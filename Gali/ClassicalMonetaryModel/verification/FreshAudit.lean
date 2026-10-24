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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
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

Restated from the `Gali/BasicNewKeynesianModel` project (each project in this
repository is self-contained).
-/

namespace Gali.ClassicalMonetaryModel

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

end Gali.ClassicalMonetaryModel

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
* `determinate_iff`: determinacy (uniqueness of bounded adapted solutions) is
  equivalent to the Schur–Cohn condition on `A` (Galí, p. 65; Blanchard and
  Kahn 1980).

Restated from the `Gali/BasicNewKeynesianModel` project (each project in this
repository is self-contained).
-/

namespace Gali.ClassicalMonetaryModel

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

end Gali.ClassicalMonetaryModel

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

Restated from the `Gali/BasicNewKeynesianModel` project (each project in this
repository is self-contained).
-/

namespace Gali.ClassicalMonetaryModel.ExpectationsFiniteTree

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

end Gali.ClassicalMonetaryModel.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The household

Galí (2015), Chapter 2, §2.1 (pp. 18–22), footnotes 3–5, and Appendix 2.1 (p. 44).

Period utility (p. 20) is `U(C, N; Z) = ((C^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)) Z` for `σ ≠ 1`
and `(log C − N^{1+φ}/(1+φ)) Z` for `σ = 1` (`periodUtility`). The book allows `σ ≥ 0`; we use
`σ > 0` wherever concavity or `σ⁻¹` is needed (correction C2-1). Several results are restated
from the Chapter 3 project (`Gali/BasicNewKeynesianModel/Household.lean`).

## Main results

* Properties assumed on p. 18: `U_c > 0`, `U_cc ≤ 0`, `U_n ≤ 0`, `U_nn ≤ 0`, `U_cz > 0`,
  separability (p. 21) and `mrs_eq` (`−U_n/U_c = C^σ N^φ`, independent of `Z`).
* Eq. (4), general utility: `static_foc_general_necessary` (variational argument) and
  `static_foc_general_sufficient` (concave `U`), via the tangent-plane inequality
  `concave_le_tangent`. For the book's utility: `static_optimum_iff` (eq. (7)) and
  `labour_supply_log_iff` (eq. (9), exact).
* Eq. (5), general utility: `euler_general_necessary` (finitely many states) and
  `euler_general_sufficient` (any expectation system), `euler_general_ratio` (the printed form).
  For the book's utility under an abstract `ExpectationSystem`: `euler_necessary`,
  `euler_sufficient`, `eulerEq_ratio_form` (eq. (8)).
* The deterministic infinite-horizon problem (`Economy`, `Plan`, `Feasible`, `Optimal`, with
  the no-Ponzi condition (3) in market prices and the overtaking criterion, which needs no
  summability): `optimal_of_foc` (**sufficiency** of budget-binding, (7), (8) and the
  transversality condition (6)); `budgetBinds_of_optimal`, `staticFOC_of_optimal`,
  `eulerDet_of_optimal` (**necessity**, the perturbation arguments of pp. 19–20);
  `tvc_liminf_of_optimal` (the book's p. 20 argument: (3) cannot hold strictly at an optimum)
  and `tvc_of_optimal_of_tendsto` (if the limit in (6) exists it is zero); `optimal_iff`;
  `tsum_le_of_optimal`; `bookTVC_iff` (the book's `Λ_{0,T} B_T/P_T` form).
* Fn. 3: `tvc_of_zero_bonds`, `tvc_of_zero_bonds_stoch` (`B_t = 0` gives (3) and (6)).
* Eq. (10): `hasFDerivAt_eulerKernel` (the Taylor step of App. 2.1 as an exact Fréchet
  derivative at the steady state `i = ρ + π̄ + σγ`), `eulerMoment_family` and
  `hasDerivAt_log_eulerMoment_family` (exact derivative of the stochastic Euler residual),
  `linearisedEuler_eq_zero_iff` (that derivative vanishes iff (10) holds),
  `pf_eulerEq_imp_eulerLogLinear` (exact under perfect foresight).
* Fn. 5: `neg_log_le_inv_sub_one`, `discount_rate_gap`, `discount_rate_gap_isBigO`.
* Eq. (11): `MoneyDemand`, `moneyDemand_iff_price`.
-/

namespace Gali.ClassicalMonetaryModel.Household

open Filter Topology

/-! ### Period utility -/

/-- Galí (2015), p. 20: utility of consumption, `(C^{1−σ} − 1)/(1 − σ)` for `σ ≠ 1` and
`log C` for `σ = 1`. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 20: disutility of labour `N^{1+φ}/(1+φ)`. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 20: period utility `U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), eq. (7), p. 21: marginal utility of consumption, `u'(C) = C^{−σ}`, in both
the `σ ≠ 1` and the log case (restated from the Chapter 3 project). -/
theorem hasDerivAt_utilC (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (utilC σ) (C ^ (-σ)) C := by
  by_cases hσ : σ = 1
  · have hfun : utilC σ = Real.log := funext fun x => by simp [utilC, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hC.ne'
  · have hfun : utilC σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [utilC, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), eq. (7), p. 21: marginal disutility of labour, `N^φ` (restated from the
Chapter 3 project). -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 18: the marginal utility `U_c = C^{−σ} Z` (derivative in `C`). -/
theorem hasDerivAt_periodUtility_C (σ φ N Z : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun C' => periodUtility σ φ C' N Z) (C ^ (-σ) * Z) C := by
  unfold periodUtility
  exact ((hasDerivAt_utilC σ hC).sub_const (disutilN φ N)).mul_const Z

/-- Galí (2015), p. 18: the marginal disutility `U_n = −N^φ Z` (derivative in `N`). -/
theorem hasDerivAt_periodUtility_N (σ C Z : ℝ) {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' => periodUtility σ φ C N' Z) (-N ^ φ * Z) N := by
  unfold periodUtility
  have := ((hasDerivAt_disutilN hφ N).const_sub (utilC σ C)).mul_const Z
  simpa using this

/-- Galí (2015), p. 18: `U_c > 0` for `C > 0`, `Z > 0`. -/
theorem margUtilC_pos (σ : ℝ) {C Z : ℝ} (hC : 0 < C) (hZ : 0 < Z) : 0 < C ^ (-σ) * Z :=
  mul_pos (Real.rpow_pos_of_pos hC _) hZ

/-- Galí (2015), p. 18: `U_n ≤ 0` for `N ≥ 0`, `Z > 0`. -/
theorem margUtilN_nonpos (φ : ℝ) {N Z : ℝ} (hN : 0 ≤ N) (hZ : 0 < Z) : -N ^ φ * Z ≤ 0 := by
  have := Real.rpow_nonneg hN φ
  nlinarith

/-- Galí (2015), p. 18: `U_cc = −σ C^{−σ−1} Z ≤ 0` (`σ > 0`, `C > 0`, `Z > 0`). -/
theorem hasDerivAt_margUtilC {σ C Z : ℝ} (hσ : 0 < σ) (hC : 0 < C) (hZ : 0 < Z) :
    HasDerivAt (fun C' => C' ^ (-σ) * Z) (-σ * C ^ (-σ - 1) * Z) C ∧
      -σ * C ^ (-σ - 1) * Z ≤ 0 := by
  refine ⟨((Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hC.ne')).mul_const Z), ?_⟩
  have := Real.rpow_pos_of_pos hC (-σ - 1)
  have : 0 < σ * C ^ (-σ - 1) * Z := by positivity
  linarith

/-- Galí (2015), p. 18: `U_nn = −φ N^{φ−1} Z ≤ 0` (`φ ≥ 0`, `N > 0`, `Z > 0`). -/
theorem hasDerivAt_margUtilN {φ N Z : ℝ} (hφ : 0 ≤ φ) (hN : 0 < N) (hZ : 0 < Z) :
    HasDerivAt (fun N' => -N' ^ φ * Z) (-(φ * N ^ (φ - 1)) * Z) N ∧
      -(φ * N ^ (φ - 1)) * Z ≤ 0 := by
  refine ⟨((Real.hasDerivAt_rpow_const (p := φ) (Or.inl hN.ne')).neg.mul_const Z), ?_⟩
  have := Real.rpow_pos_of_pos hN (φ - 1)
  have : 0 ≤ φ * N ^ (φ - 1) * Z := by positivity
  linarith

/-- Galí (2015), p. 18: `U_cz = C^{−σ} > 0`: the preference shifter raises the marginal utility
of consumption. -/
theorem hasDerivAt_margUtilC_Z (σ : ℝ) {C : ℝ} (hC : 0 < C) (Z : ℝ) :
    HasDerivAt (fun Z' => C ^ (-σ) * Z') (C ^ (-σ)) Z ∧ 0 < C ^ (-σ) := by
  refine ⟨?_, Real.rpow_pos_of_pos hC _⟩
  simpa using (hasDerivAt_id Z).const_mul (C ^ (-σ))

/-- Galí (2015), p. 21 (separability, `U_cn = 0`): the marginal utility of consumption does not
depend on hours. -/
theorem hasDerivAt_margUtilC_N (σ C Z N : ℝ) :
    HasDerivAt (fun _ : ℝ => C ^ (-σ) * Z) 0 N :=
  hasDerivAt_const N _

/-- Galí (2015), p. 21: the intratemporal marginal rate of substitution
`−U_n/U_c = C^σ N^φ` does not depend on the preference shifter `Z`. -/
theorem mrs_eq (σ φ : ℝ) {C N Z : ℝ} (hC : 0 < C) (hZ : 0 < Z) :
    -(-N ^ φ * Z) / (C ^ (-σ) * Z) = C ^ σ * N ^ φ := by
  rw [Real.rpow_neg hC.le]
  have := (Real.rpow_pos_of_pos hC σ).ne'
  field_simp

/-- Galí (2015), p. 18 (`U_cc ≤ 0`): marginal utility `C^{−σ}` is nonincreasing for `σ > 0`
(restated from the Chapter 3 project). -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (Galí (2015), p. 18, concavity of utility; restated from the Chapter 3
project). -/
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

/-- Galí (2015), p. 18: the utility of consumption is concave for `σ > 0`, in the
tangent-line form `u(y) ≤ u(x) + x^{−σ}(y − x)` for `x, y > 0`. -/
theorem utilC_le_tangent {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    utilC σ y ≤ utilC σ x + x ^ (-σ) * (y - x) := by
  refine le_tangent (f' := fun C => C ^ (-σ)) hx hy.le ?_ (fun z hz => hasDerivAt_utilC σ hz)
    (antitoneOn_margUtil hσ)
  intro z hz
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hasDerivAt_utilC σ hz0).continuousAt.continuousWithinAt

/-- Galí (2015), p. 18 (`U_c > 0`): the utility of consumption is strictly increasing,
`u(y) − u(x) ≥ y^{−σ}(y − x) > 0` for `0 < x < y`. -/
theorem utilC_strictMono {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    utilC σ x < utilC σ y := by
  have hy : 0 < y := hx.trans hxy
  have h := utilC_le_tangent hσ hy hx
  have : 0 < y ^ (-σ) * (y - x) := mul_pos (Real.rpow_pos_of_pos hy _) (sub_pos.2 hxy)
  nlinarith

/-- Galí (2015), p. 18: the disutility of labour is convex for `φ ≥ 0`, in the tangent-line
form `v(x) + x^φ (y − x) ≤ v(y)` for `x > 0`, `y ≥ 0`. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-! ### Concave functions lie below their tangent planes -/

/-- The tangent-plane inequality for a concave function with a Fréchet derivative, used for
the sufficiency of Galí's first-order conditions (2015, pp. 19–20): if `U` is concave on a
convex set `S` containing `x` and `y` and `HasFDerivAt U L x`, then `U y ≤ U x + L (y − x)`. -/
theorem concave_le_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {U : E → ℝ} {L : E →L[ℝ] ℝ} {x y : E} (hU : ConcaveOn ℝ S U) (hx : x ∈ S)
    (hy : y ∈ S) (hL : HasFDerivAt U L x) : U y ≤ U x + L (y - x) := by
  set h : ℝ → ℝ := fun s => U (x + s • (y - x)) with hh
  have hpath : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hd : HasDerivAt h (L (y - x)) 0 := by
    have hL' : HasFDerivAt U L (x + (0 : ℝ) • (y - x)) := by simpa using hL
    exact hL'.comp_hasDerivAt (0 : ℝ) hpath
  have hlim := hd.tendsto_slope_zero_right
  have hlow : ∀ᶠ s in 𝓝[>] (0 : ℝ), U y - U x ≤ s⁻¹ • (h (0 + s) - h 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have hconc := hU.2 hx hy (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hs.1.le
      (by ring : (1 - s) + s = 1)
    have heq : (1 - s) • x + s • y = x + s • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq] at hconc
    simp only [hh, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ hs.1]
    simp only [smul_eq_mul] at hconc
    nlinarith
  have := ge_of_tendsto hlim hlow
  linarith

/-- The one-dimensional tangent-line inequality for a concave differentiable function:
`u y ≤ u x + u'(x)(y − x)` (used for Galí (2015), eq. (5), p. 19). -/
theorem concave_le_tangent_real {S : Set ℝ} {u : ℝ → ℝ} {u' x y : ℝ} (hU : ConcaveOn ℝ S u)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt u u' x) : u y ≤ u x + u' * (y - x) := by
  have h := concave_le_tangent hU hx hy hd.hasFDerivAt
  simpa [mul_comm] using h

/-! ### The static (labour-supply) problem, eq. (4), general utility -/

/-- Galí (2015), eq. (4), p. 19 (**necessity**, general utility): if hours `N` are a local
optimum along the budget line `P C = W N + X` (the perturbation `P dC = W dN`) and `U` has
derivatives `U_c`, `U_n` in `C`, `N` at `(C, N)`, then `U_c (W/P) + U_n = 0`. -/
theorem static_foc_general_necessary {U : ℝ × ℝ → ℝ} {Uc Un P W X C N : ℝ} (hP : 0 < P)
    (hbud : P * C = W * N + X)
    (hU : HasFDerivAt U (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ + Un • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (C, N))
    (hloc : IsLocalMax (fun N' => U ((W * N' + X) / P, N')) N) :
    Uc * (W / P) + Un = 0 := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => ((W * N' + X) / P, N')) (W / P, 1) N := by
    have h1 : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
      simpa using (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    exact h1.prodMk (hasDerivAt_id N)
  have hU' : HasFDerivAt U (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ
      + Un • ContinuousLinearMap.snd ℝ ℝ ℝ) ((W * N + X) / P, N) := by rw [hCeq]; exact hU
  have hg := HasFDerivAt.comp_hasDerivAt (f := fun N' : ℝ => ((W * N' + X) / P, N')) N hU' hin
  have h0 := hloc.hasDerivAt_eq_zero hg
  simpa [mul_comm] using h0

/-- Galí (2015), eq. (4), p. 19: with `U_c ≠ 0` the condition of
`static_foc_general_necessary` is `−U_n/U_c = W/P`. -/
theorem static_foc_general_iff {Uc Un W P : ℝ} (hUc : Uc ≠ 0) :
    Uc * (W / P) + Un = 0 ↔ -Un / Uc = W / P := by
  constructor
  · intro h
    rw [div_eq_iff hUc]
    linarith [show Uc * (W / P) = W / P * Uc by ring]
  · intro h
    rw [div_eq_iff hUc] at h
    linarith [show Uc * (W / P) = W / P * Uc by ring]

/-- Galí (2015), eq. (4), p. 19 (**sufficiency**, general utility): if `U` is concave on a
convex set `S` of plans, differentiable at `(C, N) ∈ S`, and `U_c (W/P) + U_n = 0`, then
`(C, N)` maximises `U` over every plan `(C', N') ∈ S` on the same budget line
`P C' = W N' + X`. -/
theorem static_foc_general_sufficient {U : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {Uc Un P W X C N : ℝ}
    (hP : 0 < P) (hconc : ConcaveOn ℝ S U) (hS : (C, N) ∈ S) (hbud : P * C = W * N + X)
    (hU : HasFDerivAt U (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ + Un • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (C, N))
    (hfoc : Uc * (W / P) + Un = 0) {C' N' : ℝ} (hS' : (C', N') ∈ S)
    (hbud' : P * C' = W * N' + X) : U (C', N') ≤ U (C, N) := by
  have h := concave_le_tangent hconc hS hS' hU
  have hdC : C' - C = W / P * (N' - N) := by
    field_simp
    linarith
  have hlin : (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ + Un • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((C', N') - (C, N)) = (Uc * (W / P) + Un) * (N' - N) := by
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul]
    rw [hdC]
    ring
  rw [hlin, hfoc, zero_mul, add_zero] at h
  exact h

/-! ### The static (labour-supply) problem -/

/-- Galí (2015), eq. (4), p. 19, and eq. (7), p. 21 (**necessity**): if hours `N > 0`
are a local optimum along the budget line `P C = W N + X` (a perturbation `P dC = W dN`,
everything else unchanged) with `C > 0`, then `W/P = N^φ C^σ`. -/
theorem static_foc_necessary {σ φ P W X Z C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hZ : 0 < Z)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z) N) :
    W / P = N ^ φ * C ^ σ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hu : HasDerivAt (utilC σ) (((W * N + X) / P) ^ (-σ)) ((W * N + X) / P) :=
    hasDerivAt_utilC σ (by rw [hCeq]; exact hC)
  have hg : HasDerivAt (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z)
      ((C ^ (-σ) * (W / P) - N ^ φ) * Z) N := by
    have := (HasDerivAt.sub (hu.comp N hin) (hasDerivAt_disutilN hφ N)).mul_const Z
    rw [hCeq] at this
    exact this
  have h0 := hloc.hasDerivAt_eq_zero hg
  have h1 : C ^ (-σ) * (W / P) = N ^ φ := by
    have := (mul_eq_zero.1 h0).resolve_right hZ.ne'
    linarith
  have hCs : C ^ σ * C ^ (-σ) = 1 := by
    rw [Real.rpow_neg hC.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hC σ).ne'
  calc W / P = (C ^ σ * C ^ (-σ)) * (W / P) := by rw [hCs, one_mul]
    _ = N ^ φ * C ^ σ := by rw [mul_assoc, h1, mul_comm]

/-- Galí (2015), p. 19: a global optimum of the static problem over all feasible
plans (`N' ≥ 0`, `C' = (W N' + X)/P > 0`) with `N, C > 0` is a local optimum along the budget
line. -/
theorem static_isLocalMax_of_optimal {σ φ P W X Z C N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hopt : ∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z) :
    IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z) N := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
    (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
  filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
  rw [hCeq]
  exact hopt N' h2'.le h1'

/-- Galí (2015), eq. (7), p. 21 (**sufficiency**, by concavity): if `W/P = N^φ C^σ`
at a point `(C, N)` with `C, N > 0` on the budget line, then `(C, N)` maximises utility
among all feasible plans `N' ≥ 0`, `C' = (W N' + X)/P > 0`. -/
theorem static_foc_sufficient {σ φ P W X Z C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hZ : 0 < Z) (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X)
    (hfoc : W / P = N ^ φ * C ^ σ) {N' : ℝ} (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z := by
  have hu := utilC_le_tangent hσ hC hC'
  have hv := disutilN_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have hkey : C ^ (-σ) * (W / P) = N ^ φ := by
    rw [hfoc, Real.rpow_neg hC.le]
    field_simp [(Real.rpow_pos_of_pos hC σ).ne']
  unfold periodUtility
  apply mul_le_mul_of_nonneg_right _ hZ.le
  rw [hdiff] at hu
  nlinarith

/-- Galí (2015), eqs. (4) and (7), pp. 19–21: for `σ > 0`, `φ ≥ 0`, a point with
`C, N > 0` on the budget line solves the static problem iff `W/P = N^φ C^σ`. -/
theorem static_optimum_iff {σ φ P W X Z C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hZ : 0 < Z) (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z) ↔
      W / P = N ^ φ * C ^ σ :=
  ⟨fun h => static_foc_necessary hφ hP hZ hC hbud
      (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hσ hφ hP hZ hN hC hbud h hN' hC'⟩

/-- Galí (2015), eq. (9), p. 21, **exact**: for positive levels,
`W/P = N^φ C^σ` iff `w − p = σ c + φ n` in logs. -/
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

/-! ### The intertemporal problem: the Euler equation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eqs. (5) and (8), pp. 19–21: the consumption Euler equation
at date `t`, node by node, with the date-`t` variables taken out of `E_t` as numbers:
`Q_t = β (C_t^σ P_t / Z_t) E_t[C_{t+1}^{−σ} Z_{t+1} / P_{t+1}]`. -/
def EulerEq (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω = β * (C t ω ^ σ * P t ω / Z t ω) *
    𝔼.E t (fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') ω

/-- Galí (2015), eq. (8), p. 21: at each node the Euler equation reads
`Q_t = β E_t[(C_{t+1}/C_t)^{−σ} (Z_{t+1}/Z_t) (P_t/P_{t+1})]`, the book's printed form. -/
theorem eulerEq_ratio_form {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ}
    (hC : ∀ ω, 0 < C t ω) (hC1 : ∀ ω, 0 ≤ C (t + 1) ω) (hZ : ∀ ω, 0 < Z t ω) :
    EulerEq 𝔼 β σ Q C P Z t ↔ ∀ ω, Q t ω = β * 𝔼.E t (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω) * (P t ω / P (t + 1) ω')) ω := by
  have key : ∀ ω, (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω) * (P t ω / P (t + 1) ω'))
      = (C t ω ^ σ * P t ω / Z t ω) •
        (fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') := by
    intro ω
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.div_rpow (hC1 ω') (hC ω).le, Real.rpow_neg (hC ω).le]
    have := (Real.rpow_pos_of_pos (hC ω) σ).ne'
    have := (hZ ω).ne'
    field_simp
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [key ω, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Galí (2015), p. 20: expected utility as of date `t` (node `ω`) of the one-period
perturbation that buys `δ` more bonds at `t` (consumption falls by `Q_t δ/P_t`) and consumes
the payoff `δ` at `t + 1` (consumption rises by `δ/P_{t+1}` in every state); hours and all
other dates are unchanged, so by separability only these two terms of
`E_t ∑ β^k U_{t+k}` change. -/
noncomputable def perturbedValue (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => Z t ω * utilC σ (C t ω - Q t ω * δ / P t ω)
    + β * 𝔼.E t (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω')) ω

/-- The concavity sandwich behind Galí (2015), p. 20: for `|δ| < m ≤ P C`, the
date-`t+1` utility gain of the bond perturbation is at least
`(1 + δ/m)^{−σ} δ C^{−σ} Z / P` in every state. -/
theorem utility_gain_lower {σ m δ c p z : ℝ} (hσ : 0 < σ) (hm : 0 < m) (hc : 0 < c)
    (hp : 0 < p) (hz : 0 ≤ z) (hmpc : m ≤ p * c) (hδ : |δ| < m) :
    (1 + δ / m) ^ (-σ) * δ * (c ^ (-σ) * z / p)
      ≤ z * utilC σ (c + δ / p) - z * utilC σ (c + 0 / p) := by
  rw [zero_div, add_zero]
  have hδm := abs_lt.1 hδ
  have hk : 0 < 1 + δ / m := by
    have : -1 < δ / m := by rw [lt_div_iff₀ hm]; linarith
    linarith
  have hcp : 0 < c * (1 + δ / m) := mul_pos hc hk
  -- position of `c + δ/p` relative to `c (1 + δ/m)`
  have hrel : (0 ≤ δ → c + δ / p ≤ c * (1 + δ / m)) ∧ (δ < 0 → c * (1 + δ / m) ≤ c + δ / p) := by
    constructor
    · intro h0
      have : δ / p ≤ δ * c / m := by
        rw [div_le_div_iff₀ hp hm]; nlinarith
      have e : c * (1 + δ / m) = c + δ * c / m := by field_simp
      linarith
    · intro h0
      have : δ * c / m ≤ δ / p := by
        rw [div_le_div_iff₀ hm hp]; nlinarith
      have e : c * (1 + δ / m) = c + δ * c / m := by field_simp
      linarith
  have ha : 0 < c + δ / p := by
    rcases le_or_gt 0 δ with h0 | h0
    · have : 0 ≤ δ / p := div_nonneg h0 hp.le
      linarith
    · linarith [hrel.2 h0]
  -- tangent at `a = c + δ/p` evaluated at `c`
  have htan := utilC_le_tangent hσ ha hc
  have hsplit : (c * (1 + δ / m)) ^ (-σ) = c ^ (-σ) * (1 + δ / m) ^ (-σ) :=
    Real.mul_rpow hc.le hk.le
  have hmain : (1 + δ / m) ^ (-σ) * c ^ (-σ) * (δ / p) ≤ (c + δ / p) ^ (-σ) * (δ / p) := by
    rcases le_or_gt 0 δ with h0 | h0
    · have hle : (c * (1 + δ / m)) ^ (-σ) ≤ (c + δ / p) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos ha (hrel.1 h0) (by linarith)
      rw [hsplit] at hle
      exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg h0 hp.le)
    · have hle : (c + δ / p) ^ (-σ) ≤ (c * (1 + δ / m)) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hcp (hrel.2 h0) (by linarith)
      rw [hsplit] at hle
      exact mul_le_mul_of_nonpos_right (by linarith) (div_nonpos_of_nonpos_of_nonneg h0.le hp.le)
  have hgain : (c + δ / p) ^ (-σ) * (δ / p) ≤ utilC σ (c + δ / p) - utilC σ c := by
    have : c - (c + δ / p) = -(δ / p) := by ring
    rw [this] at htan
    linarith
  have e : (1 + δ / m) ^ (-σ) * δ * (c ^ (-σ) * z / p)
      = z * ((1 + δ / m) ^ (-σ) * c ^ (-σ) * (δ / p)) := by
    field_simp
  rw [e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (hmain.trans hgain) hz

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**necessity of the Euler equation**):
if at every date-`t` node no small bond perturbation `δ` is profitable, then the Euler
equation holds at date `t`. Hypotheses: `σ, β > 0`, positive `C_t, P_t, Z_t`, positive
`C_{t+1}, P_{t+1}`, `Z_{t+1} ≥ 0`, and a uniform lower bound `m > 0` on next period's nominal
expenditure `P_{t+1} C_{t+1}` (automatic for finitely many states). -/
theorem euler_necessary {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 < β)
    (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω) (hZ : ∀ ω, 0 < Z t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω) (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    {m : ℝ} (hm : 0 < m) (hmPC : ∀ ω, m ≤ P (t + 1) ω * C (t + 1) ω)
    (hopt : ∀ ω, ∀ᶠ δ in 𝓝 0,
      perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω) :
    EulerEq 𝔼 β σ Q C P Z t := by
  intro ω
  set G : Ω → ℝ := fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω' with hGdef
  set B := β * 𝔼.E t G ω with hB
  set A := Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω) with hA
  set f : ℝ → ℝ := fun δ => Z t ω * utilC σ (C t ω - Q t ω * δ / P t ω) with hfdef
  set g : ℝ → Ω → ℝ :=
    fun δ ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω') with hgdef
  set k : ℝ → ℝ := fun δ => (1 + δ / m) ^ (-σ) with hkdef
  -- derivative of the date-`t` term
  have hf : HasDerivAt f (-A) 0 := by
    have hin : HasDerivAt (fun δ : ℝ => C t ω - Q t ω * δ / P t ω) (-(Q t ω / P t ω)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (Q t ω)).div_const (P t ω)).const_sub
        (C t ω)
      simpa [mul_div_assoc] using this
    have hu : HasDerivAt (utilC σ) ((C t ω - Q t ω * 0 / P t ω) ^ (-σ))
        (C t ω - Q t ω * 0 / P t ω) := hasDerivAt_utilC σ (by simpa using hC ω)
    have := (hu.comp 0 hin).const_mul (Z t ω)
    refine this.congr_deriv ?_
    simp [hA]
    ring
  -- the lower bound on the change of the date-`t` value
  have hlow : ∀ δ, |δ| < m →
      perturbedValue 𝔼 β σ Q C P Z t δ ω - perturbedValue 𝔼 β σ Q C P Z t 0 ω
        ≥ f δ - f 0 + k δ * δ * B := by
    intro δ hδ
    have hpt : (k δ * δ) • G ≤ g δ - g 0 := by
      intro ω'
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hgdef, hGdef, hkdef]
      exact utility_gain_lower hσ hm (hC1 ω') (hP1 ω') (hZ1 ω') (hmPC ω') hδ
    have hE := 𝔼.mono t hpt ω
    rw [map_smul, map_sub] at hE
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hE
    have hβE := mul_le_mul_of_nonneg_left hE hβ.le
    simp only [perturbedValue, ge_iff_le]
    change f δ - f 0 + k δ * δ * B ≤ f δ + β * 𝔼.E t (g δ) ω - (f 0 + β * 𝔼.E t (g 0) ω)
    rw [hB]
    nlinarith
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), f δ - f 0 + k δ * δ * B ≤ 0 := by
    have hball : ∀ᶠ δ in 𝓝 (0 : ℝ), |δ| < m := by
      have : Tendsto (fun δ : ℝ => |δ|) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_abs.tendsto (0 : ℝ))
      exact this.eventually (gt_mem_nhds hm)
    filter_upwards [hopt ω, hball] with δ h1 h2
    have := hlow δ h2
    linarith
  have hk : Tendsto k (𝓝 0) (𝓝 1) := by
    have hca : ContinuousAt k 0 :=
      (continuousAt_const.add (continuousAt_id.div_const m)).rpow_const (Or.inl (by simp))
    simpa [hkdef] using hca.tendsto
  have hlimR : Tendsto (fun δ => δ⁻¹ * (f δ - f 0) + k δ * B) (𝓝[>] 0) (𝓝 (-A + 1 * B)) := by
    have h1 := hf.tendsto_slope_zero_right
    simp only [zero_add, smul_eq_mul] at h1
    exact h1.add ((hk.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
  have hlimL : Tendsto (fun δ => δ⁻¹ * (f δ - f 0) + k δ * B) (𝓝[<] 0) (𝓝 (-A + 1 * B)) := by
    have h1 := hf.tendsto_slope_zero_left
    simp only [zero_add, smul_eq_mul] at h1
    exact h1.add ((hk.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
  have hsplit : ∀ δ : ℝ, δ ≠ 0 →
      δ⁻¹ * (f δ - f 0) + k δ * B = δ⁻¹ * (f δ - f 0 + k δ * δ * B) := by
    intro δ hδ
    field_simp
  have hR : -A + 1 * B ≤ 0 := by
    refine le_of_tendsto hlimR ?_
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ h1 h2
    rw [hsplit δ (ne_of_gt h2)]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt h2)) h1
  have hL : 0 ≤ -A + 1 * B := by
    refine ge_of_tendsto hlimL ?_
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ h1 h2
    rw [hsplit δ (ne_of_lt h2)]
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 (le_of_lt h2)) h1
  have hAB : A = B := by linarith
  rw [hA, hB] at hAB
  have hCs : C t ω ^ σ * C t ω ^ (-σ) = 1 := by
    rw [Real.rpow_neg (hC ω).le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (hC ω) σ).ne'
  have hZ0 := (hZ ω).ne'
  have hP0 := (hP ω).ne'
  calc Q t ω = (C t ω ^ σ * C t ω ^ (-σ)) * Q t ω := by rw [hCs, one_mul]
    _ = C t ω ^ σ * P t ω / Z t ω * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)) := by
        field_simp
    _ = β * (C t ω ^ σ * P t ω / Z t ω) * 𝔼.E t G ω := by rw [hAB]; ring

/-- Galí (2015), p. 20: with finitely many states, positive `C_{t+1}` and `P_{t+1}`
have a uniform lower bound `m > 0` on next period's nominal expenditure `P_{t+1} C_{t+1}`. -/
theorem exists_expenditure_lower_bound [Finite Ω] {C P : Ω → ℝ} (hC : ∀ ω, 0 < C ω)
    (hP : ∀ ω, 0 < P ω) : ∃ m, 0 < m ∧ ∀ ω, m ≤ P ω * C ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
  · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P ω * C ω
    exact ⟨P ω₀ * C ω₀, mul_pos (hP ω₀) (hC ω₀), h₀⟩

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**necessity**, finitely many states):
no profitable small bond perturbation at any date-`t` node implies the Euler equation. -/
theorem euler_necessary_finite [Finite Ω] {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ}
    (hσ : 0 < σ) (hβ : 0 < β) (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω)
    (hZ : ∀ ω, 0 < Z t ω) (hC1 : ∀ ω, 0 < C (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    (hopt : ∀ ω, ∀ᶠ δ in 𝓝 0,
      perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω) :
    EulerEq 𝔼 β σ Q C P Z t := by
  obtain ⟨m, hm, hmPC⟩ := exists_expenditure_lower_bound hC1 hP1
  exact euler_necessary 𝔼 hσ hβ hC hP hZ hC1 hP1 hZ1 hm hmPC hopt

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**sufficiency** for one-period
perturbations, by concavity): if the Euler equation holds at date `t`, no feasible bond
perturbation `δ` (one keeping consumption positive) raises expected utility at any node. -/
theorem euler_sufficient {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω) (hZ : ∀ ω, 0 < Z t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    (heul : EulerEq 𝔼 β σ Q C P Z t) {δ : ℝ} (ω : Ω)
    (hfeas : 0 < C t ω - Q t ω * δ / P t ω) (hfeas1 : ∀ ω', 0 < C (t + 1) ω' + δ / P (t + 1) ω') :
    perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω := by
  set G : Ω → ℝ := fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω' with hGdef
  have hpt : (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω'))
      ≤ (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + 0 / P (t + 1) ω')) + δ • G := by
    intro ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_div, add_zero, hGdef]
    have h := utilC_le_tangent hσ (hC1 ω') (hfeas1 ω')
    have h2 := mul_le_mul_of_nonneg_left h (hZ1 ω')
    have e : Z (t + 1) ω' * (C (t + 1) ω' ^ (-σ) * (C (t + 1) ω' + δ / P (t + 1) ω'
        - C (t + 1) ω')) = δ * (C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') := by
      ring
    nlinarith
  have hE := 𝔼.mono t hpt ω
  rw [map_add, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  have h0 := utilC_le_tangent hσ (hC ω) hfeas
  have h0' := mul_le_mul_of_nonneg_left h0 (hZ ω).le
  have he : Q t ω = β * (C t ω ^ σ * P t ω / Z t ω) * 𝔼.E t G ω := heul ω
  have hCs : C t ω ^ σ * C t ω ^ (-σ) = 1 := by
    rw [Real.rpow_neg (hC ω).le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (hC ω) σ).ne'
  -- `Z_t C_t^{−σ} Q_t / P_t = β E_t G`
  have hAB : Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω) = β * 𝔼.E t G ω := by
    have hZ0 := (hZ ω).ne'
    have hP0 := (hP ω).ne'
    calc Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)
        = (C t ω ^ σ * C t ω ^ (-σ)) * β * 𝔼.E t G ω * (Z t ω / Z t ω) * (P t ω / P t ω) := by
          rw [he]; ring
      _ = β * 𝔼.E t G ω := by rw [hCs, div_self hZ0, div_self hP0]; ring
  have e1 : Z t ω * (C t ω ^ (-σ) * (C t ω - Q t ω * δ / P t ω - C t ω))
      = -(δ * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω))) := by ring
  rw [mul_add, e1] at h0'
  have hβE := mul_le_mul_of_nonneg_left hE hβ
  have hδ : δ * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)) = δ * (β * 𝔼.E t G ω) := by rw [hAB]
  simp only [perturbedValue, mul_zero, zero_div, sub_zero]
  simp only [zero_div] at hβE
  nlinarith

/-! ### The Euler equation (5) for a general utility function -/

/-- Galí (2015), eq. (5), pp. 19–20 (**necessity**, general utility, finitely many states):
let `u₀` be the date-`t` utility of consumption at node `ω` (hours and the shifter held fixed)
with marginal utility `U_{c,t}` at `C_t`, and `u₁ ω'` the date-`t+1` utility in state `ω'`
with marginal utility `U_{c,t+1}(ω')`. If buying `δ` more bonds at `t` (consumption falls by
`Q_t δ/P_t`, and rises by `δ/P_{t+1}` in every state at `t + 1`) is not locally profitable,
then `Q_t U_{c,t}/P_t = β E_t[U_{c,t+1}/P_{t+1}]`. With finitely many states `E_t` is a
continuous linear map, so the derivative passes under it. -/
theorem euler_general_necessary {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω)
    {β Q P₀ C₀ Uc₀ : ℝ} {u₀ : ℝ → ℝ} {u₁ : Ω → ℝ → ℝ} {C₁ P₁ Uc₁ : Ω → ℝ} (t : ℕ) (ω : Ω)
    (hu₀ : HasDerivAt u₀ Uc₀ C₀) (hu₁ : ∀ ω', HasDerivAt (u₁ ω') (Uc₁ ω') (C₁ ω'))
    (hloc : IsLocalMax (fun δ => u₀ (C₀ - Q * δ / P₀)
      + β * 𝔼.E t (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω')) ω) 0) :
    Q * Uc₀ / P₀ = β * 𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω') ω := by
  have := Fintype.ofFinite Ω
  have h0 : HasDerivAt (fun δ : ℝ => u₀ (C₀ - Q * δ / P₀)) (Uc₀ * (-(Q / P₀))) 0 := by
    have hin : HasDerivAt (fun δ : ℝ => C₀ - Q * δ / P₀) (-(Q / P₀)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul Q).div_const P₀).const_sub C₀
      simpa [mul_div_assoc] using this
    have hu : HasDerivAt u₀ Uc₀ (C₀ - Q * 0 / P₀) := by simpa using hu₀
    exact hu.comp 0 hin
  have hvec : HasDerivAt (fun δ : ℝ => fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω'))
      (fun ω' => Uc₁ ω' / P₁ ω') 0 := by
    rw [hasDerivAt_pi]
    intro ω'
    have hin : HasDerivAt (fun δ : ℝ => C₁ ω' + δ / P₁ ω') (1 / P₁ ω') 0 :=
      ((hasDerivAt_id (0 : ℝ)).div_const (P₁ ω')).const_add (C₁ ω')
    have hu : HasDerivAt (u₁ ω') (Uc₁ ω') (C₁ ω' + 0 / P₁ ω') := by simpa using hu₁ ω'
    have := hu.comp 0 hin
    rw [mul_one_div] at this
    exact this
  have hE : HasDerivAt (fun δ : ℝ => 𝔼.E t (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω')))
      (𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω')) 0 := by
    have := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hvec
    exact this
  have hEω := (hasDerivAt_pi.1 hE) ω
  have hsum := h0.add (hEω.const_mul β)
  have h := hloc.hasDerivAt_eq_zero hsum
  have e : Q * Uc₀ / P₀ = Uc₀ * (Q / P₀) := by ring
  rw [e]
  linarith

/-- Galí (2015), eq. (5), p. 19 (**sufficiency**, general concave utility, any expectation
system): if `u₀` and every `u₁ ω'` are concave and differentiable and
`Q_t U_{c,t}/P_t = β E_t[U_{c,t+1}/P_{t+1}]`, then no feasible bond perturbation `δ` raises
expected utility at the node. -/
theorem euler_general_sufficient {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    {β Q P₀ C₀ Uc₀ : ℝ} {S₀ S₁ : Set ℝ} {u₀ : ℝ → ℝ} {u₁ : Ω → ℝ → ℝ} {C₁ P₁ Uc₁ : Ω → ℝ}
    (t : ℕ) (ω : Ω) (hβ : 0 ≤ β) (hc₀ : ConcaveOn ℝ S₀ u₀) (hc₁ : ∀ ω', ConcaveOn ℝ S₁ (u₁ ω'))
    (hu₀ : HasDerivAt u₀ Uc₀ C₀) (hu₁ : ∀ ω', HasDerivAt (u₁ ω') (Uc₁ ω') (C₁ ω'))
    (hm₀ : C₀ ∈ S₀) (hm₁ : ∀ ω', C₁ ω' ∈ S₁)
    (heul : Q * Uc₀ / P₀ = β * 𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω') ω) {δ : ℝ}
    (hf₀ : C₀ - Q * δ / P₀ ∈ S₀) (hf₁ : ∀ ω', C₁ ω' + δ / P₁ ω' ∈ S₁) :
    u₀ (C₀ - Q * δ / P₀) + β * 𝔼.E t (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω')) ω
      ≤ u₀ C₀ + β * 𝔼.E t (fun ω' => u₁ ω' (C₁ ω')) ω := by
  have h0 := concave_le_tangent_real hc₀ hm₀ hf₀ hu₀
  have hpt : (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω'))
      ≤ (fun ω' => u₁ ω' (C₁ ω')) + δ • (fun ω' => Uc₁ ω' / P₁ ω') := by
    intro ω'
    have h1 := concave_le_tangent_real (hc₁ ω') (hm₁ ω') (hf₁ ω') (hu₁ ω')
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : Uc₁ ω' * (C₁ ω' + δ / P₁ ω' - C₁ ω') = δ * (Uc₁ ω' / P₁ ω') := by ring
    linarith
  have hE := 𝔼.mono t hpt ω
  rw [map_add, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  have hβE := mul_le_mul_of_nonneg_left hE hβ
  have e : Uc₀ * (C₀ - Q * δ / P₀ - C₀) = -(δ * (Q * Uc₀ / P₀)) := by ring
  rw [e, heul] at h0
  nlinarith

/-- Galí (2015), eq. (5), p. 19: with `U_{c,t} ≠ 0` and `P_t ≠ 0`, the condition
`Q_t U_{c,t}/P_t = β E_t[U_{c,t+1}/P_{t+1}]` is the book's
`Q_t = β E_t[(U_{c,t+1}/U_{c,t})(P_t/P_{t+1})]`. -/
theorem euler_general_ratio {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β Q P₀ Uc₀ : ℝ}
    {P₁ Uc₁ : Ω → ℝ} (t : ℕ) (ω : Ω) (hUc : Uc₀ ≠ 0) (hP : P₀ ≠ 0) :
    Q * Uc₀ / P₀ = β * 𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω') ω ↔
      Q = β * 𝔼.E t (fun ω' => Uc₁ ω' / Uc₀ * (P₀ / P₁ ω')) ω := by
  have hf : (fun ω' => Uc₁ ω' / Uc₀ * (P₀ / P₁ ω'))
      = (P₀ / Uc₀) • (fun ω' => Uc₁ ω' / P₁ ω') := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hf, map_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-! ### The deterministic infinite-horizon problem -/

/-- Galí (2015), eqs. (1)–(3), pp. 18–19, deterministic version: the environment of the
household. Preferences `β, σ, φ`; paths of the price level `P`, the wage `W`, dividends `Dv`,
the bond price `Q` and the preference shifter `Z`; initial bond holdings `b₀ = B_{−1}`. -/
structure Economy where
  /-- The discount factor. -/
  β : ℝ
  /-- The curvature of the utility of consumption. -/
  σ : ℝ
  /-- The inverse Frisch elasticity of labour supply. -/
  φ : ℝ
  /-- The price level. -/
  P : ℕ → ℝ
  /-- The nominal wage. -/
  W : ℕ → ℝ
  /-- Nominal dividends. -/
  Dv : ℕ → ℝ
  /-- The price of a one-period nominal bond. -/
  Q : ℕ → ℝ
  /-- The preference shifter. -/
  Z : ℕ → ℝ
  /-- Initial bond holdings `B_{−1}`. -/
  b₀ : ℝ

/-- Galí (2015), p. 18: a household plan: consumption `C_t`, hours `N_t`, and bonds `B_t`
bought at `t` (maturing at `t + 1`). -/
structure Plan where
  /-- Consumption. -/
  C : ℕ → ℝ
  /-- Hours. -/
  N : ℕ → ℝ
  /-- Bonds bought at date `t`. -/
  B : ℕ → ℝ

/-- Galí (2015), eq. (2), p. 18: bonds carried into date `t`, `B_{t−1}` (with `B_{−1} = b₀`). -/
def lagB (b₀ : ℝ) (B : ℕ → ℝ) : ℕ → ℝ
  | 0 => b₀
  | t + 1 => B t

/-- Galí (2015), pp. 18–19: the date-0 price of one unit of money paid at date `T`,
`∏_{s<T} Q_s` (the nominal discount factor implied by bond prices). -/
noncomputable def disc (Q : ℕ → ℝ) (T : ℕ) : ℝ := ∏ s ∈ Finset.range T, Q s

/-- Galí (2015), p. 19: `disc Q 0 = 1`. -/
theorem disc_zero (Q : ℕ → ℝ) : disc Q 0 = 1 := by simp [disc]

/-- Galí (2015), p. 19: `disc Q (T + 1) = disc Q T · Q_T`. -/
theorem disc_succ (Q : ℕ → ℝ) (T : ℕ) : disc Q (T + 1) = disc Q T * Q T :=
  Finset.prod_range_succ _ _

/-- Galí (2015), p. 19: positive bond prices give positive discount factors. -/
theorem disc_pos {Q : ℕ → ℝ} (hQ : ∀ t, 0 < Q t) (T : ℕ) : 0 < disc Q T :=
  Finset.prod_pos fun s _ => hQ s

/-- Galí (2015), eq. (2), p. 18: the flow budget constraint at date `t`,
`P_t C_t + Q_t B_t ≤ B_{t−1} + W_t N_t + D_t`. -/
def Budget (e : Economy) (x : Plan) (t : ℕ) : Prop :=
  e.P t * x.C t + e.Q t * x.B t ≤ lagB e.b₀ x.B t + e.W t * x.N t + e.Dv t

/-- Galí (2015), eq. (3), p. 19, deterministic form: the no-Ponzi condition
`liminf_T (∏_{s≤T} Q_s) B_T ≥ 0` on the date-0 value of the bonds bought at `T`. -/
def NoPonzi (e : Economy) (x : Plan) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ disc e.Q (T + 1) * x.B T

/-- Galí (2015), pp. 18–19: a feasible plan: positive consumption, nonnegative hours, the
budget constraint (2) at every date, and the no-Ponzi condition (3). -/
def Feasible (e : Economy) (x : Plan) : Prop :=
  (∀ t, 0 < x.C t) ∧ (∀ t, 0 ≤ x.N t) ∧ (∀ t, Budget e x t) ∧ NoPonzi e x

/-- Galí (2015), eq. (1), p. 18, deterministic: the finite-horizon sum
`∑_{t<T} β^t U(C_t, N_t; Z_t)` of lifetime utility. -/
noncomputable def partialUtility (e : Economy) (x : Plan) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t)

/-- Galí (2015), eq. (1), p. 18: a feasible plan is optimal when no feasible plan overtakes
it: for every feasible `y` and `ε > 0`, eventually `∑_{t<T} β^t U(y_t) ≤ ∑_{t<T} β^t U(x_t) + ε`.
This needs no summability; for summable utility it is `∑' β^t U(y_t) ≤ ∑' β^t U(x_t)`
(`tsum_le_of_optimal`). -/
def Optimal (e : Economy) (x : Plan) : Prop :=
  Feasible e x ∧ ∀ y, Feasible e y → ∀ ε > 0, ∀ᶠ T in atTop,
    partialUtility e y T ≤ partialUtility e x T + ε

/-- Galí (2015), eq. (7), p. 21: the static condition `W_t/P_t = N_t^φ C_t^σ` at every date. -/
def StaticFOC (e : Economy) (x : Plan) : Prop :=
  ∀ t, e.W t / e.P t = x.N t ^ e.φ * x.C t ^ e.σ

/-- Galí (2015), eq. (8), p. 21, deterministic: the Euler equation at every date,
`Q_t = β (C_t^σ P_t/Z_t)(C_{t+1}^{−σ} Z_{t+1}/P_{t+1})`. -/
def EulerDet (e : Economy) (x : Plan) : Prop :=
  ∀ t, e.Q t = e.β * (x.C t ^ e.σ * e.P t / e.Z t) *
    (x.C (t + 1) ^ (-e.σ) * e.Z (t + 1) / e.P (t + 1))

/-- Galí (2015), eq. (2), p. 18: the budget constraint holds with equality at every date. -/
def BudgetBinds (e : Economy) (x : Plan) : Prop :=
  ∀ t, e.P t * x.C t + e.Q t * x.B t = lagB e.b₀ x.B t + e.W t * x.N t + e.Dv t

/-- Galí (2015), eq. (6), p. 19, deterministic form: the transversality condition
`lim_T (∏_{s≤T} Q_s) B_T = 0`. -/
def Transversality (e : Economy) (x : Plan) : Prop :=
  Tendsto (fun T => disc e.Q (T + 1) * x.B T) atTop (𝓝 0)

/-- Galí (2015), p. 19: the discounted marginal utility of money,
`λ_t = β^t U_{c,t}/P_t = β^t Z_t C_t^{−σ}/P_t`. -/
noncomputable def lam (e : Economy) (x : Plan) (t : ℕ) : ℝ :=
  e.β ^ t * e.Z t * x.C t ^ (-e.σ) / e.P t

/-- Galí (2015), eq. (8), p. 21: the deterministic Euler equation at `t` is `λ_{t+1} = Q_t λ_t`. -/
theorem eulerDet_iff_lam (e : Economy) (x : Plan) (t : ℕ) (hβ : 0 < e.β)
    (hC : 0 < x.C t) (hZ : 0 < e.Z t) (hP : 0 < e.P t) :
    e.Q t = e.β * (x.C t ^ e.σ * e.P t / e.Z t) *
      (x.C (t + 1) ^ (-e.σ) * e.Z (t + 1) / e.P (t + 1)) ↔
      lam e x (t + 1) = e.Q t * lam e x t := by
  have hc : 0 < x.C t ^ e.σ := Real.rpow_pos_of_pos hC _
  have hl : 0 < lam e x t := by
    unfold lam
    have := Real.rpow_pos_of_pos hC (-e.σ)
    positivity
  constructor
  · intro h
    rw [h]
    unfold lam
    rw [Real.rpow_neg hC.le]
    field_simp
    ring
  · intro h
    have hq : e.Q t = lam e x (t + 1) / lam e x t := by rw [h]; field_simp
    rw [hq]
    unfold lam
    rw [Real.rpow_neg hC.le]
    field_simp
    ring

/-- Galí (2015), p. 19: along the Euler equation, `λ_T = λ_0 ∏_{s<T} Q_s`. -/
theorem lam_eq_disc (e : Economy) (x : Plan) (hlam : ∀ t, lam e x (t + 1) = e.Q t * lam e x t)
    (T : ℕ) : lam e x T = lam e x 0 * disc e.Q T := by
  induction T with
  | zero => rw [disc_zero, mul_one]
  | succ T ih => rw [hlam, ih, disc_succ]; ring

/-- Summation by parts behind Galí (2015), p. 20: if `g 0 = 0` and `g (t + 1) = f t`, then
`∑_{t ≤ T} (g t − f t) = −f T`. -/
theorem sum_telescope (f g : ℕ → ℝ) (h0 : g 0 = 0) (hs : ∀ t, g (t + 1) = f t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), (g t - f t) = -f T := by
  induction T with
  | zero => simp [h0]
  | succ T ih => rw [Finset.sum_range_succ, ih, hs]; ring

/-- Galí (2015), eqs. (6)–(8), pp. 19–21 (**sufficiency**, deterministic infinite horizon):
a feasible plan with interior hours that satisfies the budget constraint with equality, the
static condition (7), the Euler equation (8) at every date and the transversality condition
(6) is optimal. (`σ > 0` covers the log case `σ = 1`.) -/
theorem optimal_of_foc (e : Economy) (x : Plan) (hβ : 0 < e.β) (hσ : 0 < e.σ) (hφ : 0 ≤ e.φ)
    (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hx : Feasible e x) (hN : ∀ t, 0 < x.N t)
    (hbind : BudgetBinds e x) (hst : StaticFOC e x) (heu : EulerDet e x)
    (htvc : Transversality e x) : Optimal e x := by
  refine ⟨hx, fun y hy ε hε => ?_⟩
  obtain ⟨hCx, -, -, -⟩ := hx
  obtain ⟨hCy, hNy, hBy, hNPy⟩ := hy
  have hlam : ∀ t, lam e x (t + 1) = e.Q t * lam e x t := fun t =>
    (eulerDet_iff_lam e x t hβ (hCx t) (hZ t) (hP t)).1 (heu t)
  have hper : ∀ t, e.β ^ t * periodUtility e.σ e.φ (y.C t) (y.N t) (e.Z t)
      - e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t)
      ≤ lam e x t * (lagB e.b₀ y.B t - lagB e.b₀ x.B t) - lam e x (t + 1) * (y.B t - x.B t) := by
    intro t
    have hu := utilC_le_tangent hσ (hCx t) (hCy t)
    have hv := disutilN_tangent_le hφ (hN t) (hNy t)
    have hc : 0 < x.C t ^ e.σ := Real.rpow_pos_of_pos (hCx t) _
    have hm : x.C t ^ (-e.σ) = (x.C t ^ e.σ)⁻¹ := Real.rpow_neg (hCx t).le _
    have hNφ : x.N t ^ e.φ = e.W t / e.P t * x.C t ^ (-e.σ) := by
      rw [hst t, hm]
      field_simp
    have hb := hBy t
    have hbx := hbind t
    unfold Budget at hb
    rw [hlam t]
    unfold periodUtility lam
    have hk : 0 ≤ e.β ^ t * e.Z t := by have := hZ t; positivity
    have hm0 : 0 ≤ x.C t ^ (-e.σ) := (Real.rpow_pos_of_pos (hCx t) _).le
    have hPt := hP t
    have step1 : (utilC e.σ (y.C t) - disutilN e.φ (y.N t))
        - (utilC e.σ (x.C t) - disutilN e.φ (x.N t))
        ≤ x.C t ^ (-e.σ) / e.P t * (e.P t * (y.C t - x.C t) - e.W t * (y.N t - x.N t)) := by
      have e1 : x.C t ^ (-e.σ) / e.P t * (e.P t * (y.C t - x.C t) - e.W t * (y.N t - x.N t))
          = x.C t ^ (-e.σ) * (y.C t - x.C t) - x.N t ^ e.φ * (y.N t - x.N t) := by
        rw [hNφ]
        field_simp
      rw [e1]
      linarith
    have step2 : e.P t * (y.C t - x.C t) - e.W t * (y.N t - x.N t)
        ≤ (lagB e.b₀ y.B t - lagB e.b₀ x.B t) - e.Q t * (y.B t - x.B t) := by
      linarith
    have step3 := mul_le_mul_of_nonneg_left step2 (div_nonneg hm0 hPt.le)
    have step4 := mul_le_mul_of_nonneg_left (step1.trans step3) hk
    have e2 : e.β ^ t * ((utilC e.σ (y.C t) - disutilN e.φ (y.N t)) * e.Z t)
        - e.β ^ t * ((utilC e.σ (x.C t) - disutilN e.φ (x.N t)) * e.Z t)
        = e.β ^ t * e.Z t * ((utilC e.σ (y.C t) - disutilN e.φ (y.N t))
          - (utilC e.σ (x.C t) - disutilN e.φ (x.N t))) := by ring
    rw [e2]
    refine step4.trans (le_of_eq ?_)
    ring
  have hsum : ∀ T, partialUtility e y (T + 1) - partialUtility e x (T + 1)
      ≤ lam e x 0 * (disc e.Q (T + 1) * x.B T) - lam e x 0 * (disc e.Q (T + 1) * y.B T) := by
    intro T
    unfold partialUtility
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_le_sum fun t _ => hper t).trans (le_of_eq ?_)
    rw [sum_telescope (fun t => lam e x (t + 1) * (y.B t - x.B t))
      (fun t => lam e x t * (lagB e.b₀ y.B t - lagB e.b₀ x.B t)) (by simp [lagB])
      (fun t => rfl) T, lam_eq_disc e x hlam]
    ring
  have hl0 : 0 < lam e x 0 := by
    unfold lam
    have := Real.rpow_pos_of_pos (hCx 0) (-e.σ)
    have := hZ 0
    have := hP 0
    positivity
  set δ := ε / (2 * lam e x 0) with hδ
  have hδ0 : 0 < δ := by positivity
  have h1 : ∀ᶠ T in atTop, disc e.Q (T + 1) * x.B T < δ := htvc.eventually (gt_mem_nhds hδ0)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (h1.and (hNPy δ hδ0))
  refine eventually_atTop.2 ⟨T₀ + 1, fun T hT => ?_⟩
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  obtain ⟨ha, hb⟩ := hT₀ T' (by omega)
  have hs := hsum T'
  have hcalc : lam e x 0 * δ + lam e x 0 * δ = ε := by
    rw [hδ]
    field_simp
    ring
  nlinarith

/-- Galí (2015), eq. (1), p. 18: for an optimal plan and any feasible plan whose discounted
utilities are summable, `∑' β^t U(y_t) ≤ ∑' β^t U(x_t)`. -/
theorem tsum_le_of_optimal {e : Economy} {x y : Plan} (hopt : Optimal e x) (hy : Feasible e y)
    (hsx : Summable fun t => e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t))
    (hsy : Summable fun t => e.β ^ t * periodUtility e.σ e.φ (y.C t) (y.N t) (e.Z t)) :
    ∑' t, e.β ^ t * periodUtility e.σ e.φ (y.C t) (y.N t) (e.Z t)
      ≤ ∑' t, e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hx := hsx.hasSum.tendsto_sum_nat
  have hy' := hsy.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto hy' (hx.add_const ε) (hopt.2 y hy ε hε)

/-- An optimal plan is not overtaken: a feasible deviation whose finite-horizon utility gain is
eventually a constant `g` has `g ≤ 0` (used for the necessity results of Galí (2015),
pp. 19–20). -/
theorem gain_nonpos_of_optimal {e : Economy} {x y : Plan} (hopt : Optimal e x)
    (hy : Feasible e y) {g : ℝ} {T₀ : ℕ}
    (hg : ∀ T, T₀ ≤ T → partialUtility e y T - partialUtility e x T = g) : g ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨T, hT1, hT2⟩ := ((hopt.2 y hy (g / 2) (by linarith)).and
    (eventually_ge_atTop T₀)).exists
  have := hg T hT2
  linarith

/-- A sum over `range T` of a function vanishing off `t` is its value at `t` (`t < T`). -/
theorem sum_range_single {f : ℕ → ℝ} {t T : ℕ} (hf : ∀ s, s ≠ t → f s = 0) (hT : t < T) :
    ∑ s ∈ Finset.range T, f s = f t :=
  Finset.sum_eq_single_of_mem t (Finset.mem_range.2 hT) fun s _ hs => hf s hs

/-- A sum over `range T` of a function vanishing off `{t, t + 1}` is `f t + f (t + 1)`. -/
theorem sum_range_pair {f : ℕ → ℝ} {t T : ℕ} (hf : ∀ s, s ≠ t → s ≠ t + 1 → f s = 0)
    (hT : t + 1 < T) : ∑ s ∈ Finset.range T, f s = f t + f (t + 1) :=
  Finset.sum_eq_add_of_mem t (t + 1) (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 hT)
    (by omega) fun s _ hs => hf s hs.1 hs.2

/-- Galí (2015), eq. (2), p. 18 (**necessity**): an optimal plan exhausts the budget at every
date; otherwise consuming the slack at that date raises utility (`U_c > 0`). -/
theorem budgetBinds_of_optimal {e : Economy} {x : Plan} (hβ : 0 < e.β) (hσ : 0 < e.σ)
    (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) : BudgetBinds e x := by
  intro t
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  by_contra hne
  have hlt := lt_of_le_of_ne (hB t) hne
  set s := lagB e.b₀ x.B t + e.W t * x.N t + e.Dv t - (e.P t * x.C t + e.Q t * x.B t) with hs
  have hs0 : 0 < s := by linarith
  have hsp : 0 < s / e.P t := div_pos hs0 (hP t)
  set y : Plan := ⟨Function.update x.C t (x.C t + s / e.P t), x.N, x.B⟩ with hydef
  have hy : Feasible e y := by
    refine ⟨fun r => ?_, hN, fun r => ?_, hNP⟩
    · by_cases hr : r = t
      · subst hr
        simp only [hydef, Function.update_self]
        linarith [hC r]
      · simp only [hydef, Function.update_of_ne hr]
        exact hC r
    · by_cases hr : r = t
      · subst hr
        simp only [Budget, hydef, Function.update_self]
        rw [mul_add, mul_div_cancel₀ _ (hP r).ne']
        linarith
      · simp only [Budget, hydef, Function.update_of_ne hr]
        exact hB r
  have hg : ∀ T, t + 1 ≤ T → partialUtility e y T - partialUtility e x T =
      e.β ^ t * ((utilC e.σ (x.C t + s / e.P t) - utilC e.σ (x.C t)) * e.Z t) := by
    intro T hT
    unfold partialUtility
    rw [← Finset.sum_sub_distrib, sum_range_single (t := t) _ (by omega)]
    · simp only [hydef, Function.update_self, periodUtility]
      ring
    · intro r hr
      simp only [hydef, Function.update_of_ne hr]
      ring
  have hle := gain_nonpos_of_optimal hopt hy hg
  have hu := utilC_strictMono hσ (hC t) (by linarith : x.C t < x.C t + s / e.P t)
  have : 0 < e.β ^ t * ((utilC e.σ (x.C t + s / e.P t) - utilC e.σ (x.C t)) * e.Z t) :=
    mul_pos (pow_pos hβ t) (mul_pos (by linarith) (hZ t))
  linarith

/-- Galí (2015), eqs. (4) and (7), pp. 19–21 (**necessity**, deterministic infinite horizon):
at an optimal plan, every date with positive hours satisfies `W_t/P_t = N_t^φ C_t^σ`. -/
theorem staticFOC_of_optimal {e : Economy} {x : Plan} (hβ : 0 < e.β) (hσ : 0 < e.σ)
    (hφ : 0 ≤ e.φ) (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) (t : ℕ)
    (hNt : 0 < x.N t) : e.W t / e.P t = x.N t ^ e.φ * x.C t ^ e.σ := by
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  have hbind := budgetBinds_of_optimal hβ hσ hP hZ hopt t
  set X := lagB e.b₀ x.B t + e.Dv t - e.Q t * x.B t with hX
  have hbud : e.P t * x.C t = e.W t * x.N t + X := by rw [hX]; linarith
  have hCeq : (e.W t * x.N t + X) / e.P t = x.C t := by rw [← hbud]; field_simp [(hP t).ne']
  refine static_foc_necessary hφ (hP t) (hZ t) (hC t) hbud ?_
  have hcont : Continuous fun N' : ℝ => (e.W t * N' + X) / e.P t := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 (x.N t), 0 < (e.W t * N' + X) / e.P t :=
    (hcont.tendsto _).eventually_const_lt (by rw [hCeq]; exact hC t)
  filter_upwards [h1, eventually_gt_nhds hNt] with N' h1' h2'
  set y : Plan := ⟨Function.update x.C t ((e.W t * N' + X) / e.P t),
    Function.update x.N t N', x.B⟩ with hydef
  have hy : Feasible e y := by
    refine ⟨fun r => ?_, fun r => ?_, fun r => ?_, hNP⟩
    · by_cases hr : r = t
      · subst hr; simpa only [hydef, Function.update_self] using h1'
      · simp only [hydef, Function.update_of_ne hr]; exact hC r
    · by_cases hr : r = t
      · subst hr; simp only [hydef, Function.update_self]; exact h2'.le
      · simp only [hydef, Function.update_of_ne hr]; exact hN r
    · by_cases hr : r = t
      · subst hr
        simp only [Budget, hydef, Function.update_self]
        rw [mul_div_cancel₀ _ (hP r).ne', hX]
        linarith
      · simp only [Budget, hydef, Function.update_of_ne hr]
        exact hB r
  have hg : ∀ T, t + 1 ≤ T → partialUtility e y T - partialUtility e x T =
      e.β ^ t * (periodUtility e.σ e.φ ((e.W t * N' + X) / e.P t) N' (e.Z t)
        - periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t)) := by
    intro T hT
    unfold partialUtility
    rw [← Finset.sum_sub_distrib, sum_range_single (t := t) _ (by omega)]
    · simp only [hydef, Function.update_self]
      ring
    · intro r hr
      simp only [hydef, Function.update_of_ne hr]
      ring
  have hle := gain_nonpos_of_optimal hopt hy hg
  have hb := pow_pos hβ t
  rw [hCeq]
  nlinarith

/-- Galí (2015), p. 18: `B_{t−1}` after changing the bonds bought at date `t` only. -/
theorem lagB_update (b₀ : ℝ) (B : ℕ → ℝ) (t : ℕ) (v : ℝ) (r : ℕ) :
    lagB b₀ (Function.update B t v) r = if r = t + 1 then v else lagB b₀ B r := by
  cases r with
  | zero => simp [lagB]
  | succ r =>
    by_cases hr : r = t
    · subst hr; simp [lagB]
    · simp [lagB, hr]

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**necessity**, deterministic infinite horizon,
the perturbation argument of p. 20): at an optimal plan the Euler equation holds at every
date. The deviation buys `δ` more bonds at `t`, consumes `Q_t δ/P_t` less at `t` and `δ/P_{t+1}`
more at `t + 1`; it is feasible for small `δ` and changes no other date. -/
theorem eulerDet_of_optimal {e : Economy} {x : Plan} (hβ : 0 < e.β)
    (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) : EulerDet e x := by
  intro t
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  rw [eulerDet_iff_lam e x t hβ (hC t) (hZ t) (hP t)]
  set G : ℝ → ℝ := fun δ => e.β ^ t * e.Z t * utilC e.σ (x.C t - e.Q t * δ / e.P t)
    + e.β ^ (t + 1) * e.Z (t + 1) * utilC e.σ (x.C (t + 1) + δ / e.P (t + 1)) with hGdef
  have hG : HasDerivAt G (e.β ^ t * e.Z t * (x.C t ^ (-e.σ) * (-(e.Q t / e.P t)))
      + e.β ^ (t + 1) * e.Z (t + 1) * (x.C (t + 1) ^ (-e.σ) * (1 / e.P (t + 1)))) 0 := by
    have hin0 : HasDerivAt (fun δ : ℝ => x.C t - e.Q t * δ / e.P t) (-(e.Q t / e.P t)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (e.Q t)).div_const (e.P t)).const_sub (x.C t)
      simpa [mul_div_assoc] using this
    have hin1 : HasDerivAt (fun δ : ℝ => x.C (t + 1) + δ / e.P (t + 1)) (1 / e.P (t + 1)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).div_const (e.P (t + 1))).const_add (x.C (t + 1))
    have hu0 : HasDerivAt (utilC e.σ) (x.C t ^ (-e.σ)) (x.C t - e.Q t * 0 / e.P t) := by
      simpa using hasDerivAt_utilC e.σ (hC t)
    have hu1 : HasDerivAt (utilC e.σ) (x.C (t + 1) ^ (-e.σ)) (x.C (t + 1) + 0 / e.P (t + 1)) := by
      simpa using hasDerivAt_utilC e.σ (hC (t + 1))
    exact ((hu0.comp 0 hin0).const_mul _).add ((hu1.comp 0 hin1).const_mul _)
  have hloc : IsLocalMax G 0 := by
    have hc0 : Continuous fun δ : ℝ => x.C t - e.Q t * δ / e.P t := by fun_prop
    have hc1 : Continuous fun δ : ℝ => x.C (t + 1) + δ / e.P (t + 1) := by fun_prop
    have h0 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < x.C t - e.Q t * δ / e.P t :=
      (hc0.tendsto 0).eventually_const_lt (by simpa using hC t)
    have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < x.C (t + 1) + δ / e.P (t + 1) :=
      (hc1.tendsto 0).eventually_const_lt (by simpa using hC (t + 1))
    filter_upwards [h0, h1] with δ hδ0 hδ1
    set y : Plan := ⟨fun s => if s = t then x.C t - e.Q t * δ / e.P t
      else if s = t + 1 then x.C (t + 1) + δ / e.P (t + 1) else x.C s, x.N,
      Function.update x.B t (x.B t + δ)⟩ with hydef
    have hy : Feasible e y := by
      refine ⟨fun r => ?_, hN, fun r => ?_, fun ε hε => ?_⟩
      · by_cases hr : r = t
        · simp only [hydef, hr, ↓reduceIte]; exact hδ0
        · by_cases hr1 : r = t + 1
          · simp only [hydef, hr1, ↓reduceIte, show t + 1 ≠ t by omega]; exact hδ1
          · simp only [hydef, hr, hr1, ↓reduceIte]; exact hC r
      · unfold Budget
        rw [lagB_update]
        by_cases hr : r = t
        · subst hr
          simp only [hydef, ↓reduceIte, Function.update_self, show r ≠ r + 1 by omega]
          have := hB r
          unfold Budget at this
          have e1 : e.P r * (x.C r - e.Q r * δ / e.P r) = e.P r * x.C r - e.Q r * δ := by
            field_simp [(hP r).ne']
          rw [e1]
          linarith
        · by_cases hr1 : r = t + 1
          · subst hr1
            simp only [hydef, ↓reduceIte, show t + 1 ≠ t by omega,
              Function.update_of_ne (show t + 1 ≠ t by omega)]
            have := hB (t + 1)
            unfold Budget lagB at this
            have e1 : e.P (t + 1) * (x.C (t + 1) + δ / e.P (t + 1))
                = e.P (t + 1) * x.C (t + 1) + δ := by
              field_simp [(hP (t + 1)).ne']
            rw [e1]
            linarith
          · simp only [hydef, hr, hr1, ↓reduceIte, Function.update_of_ne hr]
            exact hB r
      · filter_upwards [hNP ε hε, eventually_gt_atTop t] with T hT1 hT2
        simp only [hydef, Function.update_of_ne (show T ≠ t by omega)]
        exact hT1
    have hg : ∀ T, t + 2 ≤ T → partialUtility e y T - partialUtility e x T = G δ - G 0 := by
      intro T hT
      unfold partialUtility
      rw [← Finset.sum_sub_distrib, sum_range_pair (t := t) _ (by omega)]
      · simp only [hydef, hGdef, ↓reduceIte, show t + 1 ≠ t by omega, periodUtility]
        simp only [mul_zero, zero_div, sub_zero, add_zero]
        ring
      · intro r hr hr1
        simp only [hydef, hr, hr1, ↓reduceIte]
        ring
    linarith [gain_nonpos_of_optimal hopt hy hg]
  have h := hloc.hasDerivAt_eq_zero hG
  unfold lam
  linear_combination h

/-- Galí (2015), p. 20 and eq. (6), p. 19 (**necessity of transversality**, the book's
argument): at an optimal plan the no-Ponzi condition (3) cannot hold with strict inequality.
If the date-0 value of bonds stayed above some `L > 0`, the household could consume `L/P_0`
more at date 0 and roll the debt over forever, which raises utility. Hence, for every `L > 0`,
`(∏_{s≤T} Q_s) B_T < L` for infinitely many `T`: `liminf_T (∏_{s≤T} Q_s) B_T ≤ 0`. -/
theorem tvc_liminf_of_optimal {e : Economy} {x : Plan} (hσ : 0 < e.σ) (hP : ∀ t, 0 < e.P t)
    (hQ : ∀ t, 0 < e.Q t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) {L : ℝ} (hL : 0 < L) :
    ∃ᶠ T in atTop, disc e.Q (T + 1) * x.B T < L := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  have hd := disc_pos hQ
  set y : Plan := ⟨Function.update x.C 0 (x.C 0 + L / e.P 0), x.N,
    fun s => x.B s - L / disc e.Q (s + 1)⟩ with hydef
  have hy : Feasible e y := by
    refine ⟨fun r => ?_, hN, fun r => ?_, fun ε hε => ?_⟩
    · by_cases hr : r = 0
      · subst hr
        simp only [hydef, Function.update_self]
        have := div_pos hL (hP 0)
        linarith [hC 0]
      · simp only [hydef, Function.update_of_ne hr]
        exact hC r
    · cases r with
      | zero =>
        have := hB 0
        unfold Budget lagB at this ⊢
        simp only [hydef, Function.update_self, disc_succ, disc_zero, one_mul]
        have e1 : e.P 0 * (x.C 0 + L / e.P 0) + e.Q 0 * (x.B 0 - L / e.Q 0)
            = e.P 0 * x.C 0 + e.Q 0 * x.B 0 := by
          field_simp [(hP 0).ne', (hQ 0).ne']
          ring
        rw [e1]
        exact this
      | succ r =>
        have := hB (r + 1)
        unfold Budget lagB at this ⊢
        simp only [hydef, Function.update_of_ne (show r + 1 ≠ 0 by omega)]
        have e1 : e.Q (r + 1) * (x.B (r + 1) - L / disc e.Q (r + 1 + 1))
            = e.Q (r + 1) * x.B (r + 1) - L / disc e.Q (r + 1) := by
          rw [disc_succ e.Q (r + 1)]
          field_simp [(hQ (r + 1)).ne', (hd (r + 1)).ne']
        rw [e1]
        linarith
    · filter_upwards [hcon] with T hT
      push Not at hT
      simp only [hydef]
      rw [mul_sub, mul_div_cancel₀ _ (hd (T + 1)).ne']
      linarith
  have hg : ∀ T, 0 + 1 ≤ T → partialUtility e y T - partialUtility e x T =
      e.β ^ 0 * ((utilC e.σ (x.C 0 + L / e.P 0) - utilC e.σ (x.C 0)) * e.Z 0) := by
    intro T hT
    unfold partialUtility
    rw [← Finset.sum_sub_distrib, sum_range_single (t := 0) _ (by omega)]
    · simp only [hydef, Function.update_self, periodUtility]
      ring
    · intro r hr
      simp only [hydef, Function.update_of_ne hr]
      ring
  have hle := gain_nonpos_of_optimal hopt hy hg
  have hu := utilC_strictMono hσ (hC 0) (by
    have := div_pos hL (hP 0); linarith : x.C 0 < x.C 0 + L / e.P 0)
  have : 0 < e.β ^ 0 * ((utilC e.σ (x.C 0 + L / e.P 0) - utilC e.σ (x.C 0)) * e.Z 0) := by
    rw [pow_zero, one_mul]
    exact mul_pos (by linarith) (hZ 0)
  linarith

/-- Galí (2015), eq. (6), p. 19 (**necessity of transversality**): at an optimal plan, if the
date-0 value of bond holdings `(∏_{s≤T} Q_s) B_T` converges (as the book's `lim` presupposes),
its limit is zero. The no-Ponzi condition (3) gives `≥ 0`; `tvc_liminf_of_optimal` gives `≤ 0`. -/
theorem tvc_of_optimal_of_tendsto {e : Economy} {x : Plan} (hσ : 0 < e.σ)
    (hP : ∀ t, 0 < e.P t) (hQ : ∀ t, 0 < e.Q t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x)
    {L : ℝ} (hlim : Tendsto (fun T => disc e.Q (T + 1) * x.B T) atTop (𝓝 L)) : L = 0 := by
  rcases lt_trichotomy L 0 with hL | hL | hL
  · exfalso
    have h1 := hopt.1.2.2.2 (-L / 2) (by linarith)
    have h2 : ∀ᶠ T in atTop, disc e.Q (T + 1) * x.B T < L / 2 :=
      hlim.eventually (gt_mem_nhds (by linarith))
    obtain ⟨T, hT1, hT2⟩ := (h1.and h2).exists
    linarith
  · exact hL
  · exfalso
    have h1 := tvc_liminf_of_optimal hσ hP hQ hZ hopt (half_pos hL)
    have h2 : ∀ᶠ T in atTop, L / 2 < disc e.Q (T + 1) * x.B T :=
      hlim.eventually (lt_mem_nhds (by linarith))
    obtain ⟨T, hT1, hT2⟩ := (h1.and_eventually h2).exists
    linarith

/-- Galí (2015), eqs. (2)–(8), pp. 18–21 (**characterisation**, deterministic infinite
horizon): for a feasible plan with positive hours whose discounted bond value converges, the
plan is optimal iff the budget binds, the static condition (7), the Euler equation (8) and the
transversality condition (6) hold. -/
theorem optimal_iff {e : Economy} {x : Plan} (hβ : 0 < e.β) (hσ : 0 < e.σ) (hφ : 0 ≤ e.φ)
    (hP : ∀ t, 0 < e.P t) (hQ : ∀ t, 0 < e.Q t) (hZ : ∀ t, 0 < e.Z t) (hx : Feasible e x)
    (hN : ∀ t, 0 < x.N t)
    (hlim : ∃ L, Tendsto (fun T => disc e.Q (T + 1) * x.B T) atTop (𝓝 L)) :
    Optimal e x ↔ BudgetBinds e x ∧ StaticFOC e x ∧ EulerDet e x ∧ Transversality e x := by
  constructor
  · intro hopt
    obtain ⟨L, hL⟩ := hlim
    have h0 := tvc_of_optimal_of_tendsto hσ hP hQ hZ hopt hL
    subst h0
    exact ⟨budgetBinds_of_optimal hβ hσ hP hZ hopt,
      fun t => staticFOC_of_optimal hβ hσ hφ hP hZ hopt t (hN t),
      eulerDet_of_optimal hβ hP hZ hopt, hL⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact optimal_of_foc e x hβ hσ hφ hP hZ hx hN h1 h2 h3 h4

/-- Galí (2015), eq. (6), p. 19, in the book's notation (date `t = 0`):
`Λ_{0,T} B_T/P_T` with `Λ_{0,T} = β^T U_{c,T}/U_{c,0}` and `U_{c,t} = Z_t C_t^{−σ}`. -/
noncomputable def bookTVCTerm (e : Economy) (x : Plan) (T : ℕ) : ℝ :=
  e.β ^ T * (e.Z T * x.C T ^ (-e.σ)) / (e.Z 0 * x.C 0 ^ (-e.σ)) * x.B T / e.P T

/-- Galí (2015), eq. (6), p. 19: along the Euler equation the book's term is
`Λ_{0,T} B_T/P_T = (∏_{s<T} Q_s) B_T / P_0`. -/
theorem bookTVCTerm_eq {e : Economy} {x : Plan} (hβ : 0 < e.β) (hP : ∀ t, 0 < e.P t)
    (hZ : ∀ t, 0 < e.Z t) (hC : ∀ t, 0 < x.C t) (heu : EulerDet e x) (T : ℕ) :
    bookTVCTerm e x T = disc e.Q T * x.B T / e.P 0 := by
  have hlam : ∀ t, lam e x (t + 1) = e.Q t * lam e x t := fun t =>
    (eulerDet_iff_lam e x t hβ (hC t) (hZ t) (hP t)).1 (heu t)
  have h := lam_eq_disc e x hlam T
  unfold lam at h
  simp only [pow_zero, one_mul] at h
  unfold bookTVCTerm
  have hc0 := Real.rpow_pos_of_pos (hC 0) (-e.σ)
  have hPT := (hP T).ne'
  have hP0 := (hP 0).ne'
  have hZ0 := (hZ 0).ne'
  have e1 : e.β ^ T * (e.Z T * x.C T ^ (-e.σ)) = e.β ^ T * e.Z T * x.C T ^ (-e.σ) / e.P T
      * e.P T := by field_simp
  rw [e1, h]
  field_simp

/-- Galí (2015), eq. (6), p. 19: with bond prices bounded, `0 < q ≤ Q_T ≤ Q̄`, the book's
transversality condition `Λ_{0,T} B_T/P_T → 0` is equivalent to `Transversality`
(`(∏_{s≤T} Q_s) B_T → 0`) along the Euler equation. -/
theorem bookTVC_iff {e : Economy} {x : Plan} (hβ : 0 < e.β) (hP : ∀ t, 0 < e.P t)
    (hZ : ∀ t, 0 < e.Z t) (hC : ∀ t, 0 < x.C t) (heu : EulerDet e x) {q Qb : ℝ} (hq : 0 < q)
    (hQl : ∀ t, q ≤ e.Q t) (hQu : ∀ t, e.Q t ≤ Qb) :
    Tendsto (bookTVCTerm e x) atTop (𝓝 0) ↔ Transversality e x := by
  have hb := bookTVCTerm_eq hβ hP hZ hC heu
  have hP0 := hP 0
  have hQ : ∀ t, 0 < e.Q t := fun t => lt_of_lt_of_le hq (hQl t)
  have hdB : ∀ T, disc e.Q (T + 1) * x.B T = e.Q T * (e.P 0 * bookTVCTerm e x T) := by
    intro T
    rw [hb, disc_succ]
    field_simp
  unfold Transversality
  simp_rw [hdB]
  constructor
  · intro h
    have h' : Tendsto (fun T => e.P 0 * bookTVCTerm e x T) atTop (𝓝 0) := by
      simpa using h.const_mul (e.P 0)
    refine squeeze_zero_norm (a := fun T => Qb * ‖e.P 0 * bookTVCTerm e x T‖) (fun T => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs (e.Q T), abs_of_pos (hQ T)]
      exact mul_le_mul_of_nonneg_right (hQu T) (norm_nonneg _)
    · simpa using (h'.norm).const_mul Qb
  · intro h
    have h' : Tendsto (fun T => e.P 0 * bookTVCTerm e x T) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun T => q⁻¹ * ‖e.Q T * (e.P 0 * bookTVCTerm e x T)‖)
        (fun T => ?_) ?_
      · rw [norm_mul (e.Q T), Real.norm_eq_abs (e.Q T), abs_of_pos (hQ T), ← mul_assoc]
        have : 1 ≤ q⁻¹ * e.Q T := by rw [le_inv_mul_iff₀ hq, mul_one]; exact hQl T
        nlinarith [norm_nonneg (e.P 0 * bookTVCTerm e x T)]
      · simpa using (h.norm).const_mul q⁻¹
    have := h'.const_mul (e.P 0)⁻¹
    simp only [mul_zero] at this
    refine this.congr fun T => ?_
    field_simp

/-- Galí (2015), fn. 3, p. 20 (deterministic): with zero bond holdings, `B_t = 0` for all `t`,
the no-Ponzi condition (3) and the transversality condition (6) both hold. -/
theorem tvc_of_zero_bonds (e : Economy) (x : Plan) (h0 : ∀ t, x.B t = 0) :
    NoPonzi e x ∧ Transversality e x ∧ Tendsto (bookTVCTerm e x) atTop (𝓝 0) := by
  refine ⟨fun ε hε => Eventually.of_forall fun T => ?_, ?_, ?_⟩
  · rw [h0, mul_zero]; linarith
  · simp only [Transversality, h0, mul_zero, tendsto_const_nhds]
  · have : bookTVCTerm e x = fun _ => 0 := by funext T; simp [bookTVCTerm, h0]
    rw [this]
    exact tendsto_const_nhds

/-- Galí (2015), fn. 3, p. 20 (under uncertainty): with zero net bond holdings,
`B_t = 0` in every state, `E_t[Λ_{t,T} B_T/P_T] = 0` for every `T`, so (6) holds at every `t`,
whatever the stochastic discount factor `Λ` and prices `P`. -/
theorem tvc_of_zero_bonds_stoch {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    (Λ : ℕ → ℕ → Ω → ℝ) (B P : ℕ → Ω → ℝ) (h0 : ∀ T ω, B T ω = 0) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => Λ t T ω' * B T ω' / P T ω') ω) atTop (𝓝 0) := by
  have : ∀ T, (fun ω' => Λ t T ω' * B T ω' / P T ω') = 0 := fun T => by
    funext ω'
    simp [h0]
  simp only [this, map_zero, Pi.zero_apply, tendsto_const_nhds]

/-! ### Log forms of the Euler equation -/

/-- Galí (2015), App. 2.1, eq. (51), p. 44: the Euler moment at node `ω`,
`E_t[exp(i_t − ρ − σ(c_{t+1} − c_t) − (p_{t+1} − p_t) + (z_{t+1} − z_t))]`, all variables
in logs, date-`t` values entering as numbers. -/
noncomputable def eulerMoment (σ ρ : ℝ) (i c p z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
    - (p (t + 1) ω' - p t ω) + (z (t + 1) ω' - z t ω))) ω

/-- Galí (2015), eq. (8), p. 21, and eq. (51), p. 44, **exact**: with `Q = e^{−i}`, `β = e^{−ρ}`,
`C = e^c`, `P = e^p`, `Z = e^z`, the Euler equation at date `t` is equivalent to the Euler
moment being equal to one at every node. -/
theorem eulerEq_iff_moment (σ ρ : ℝ) (i c p z : ℕ → Ω → ℝ) (t : ℕ) :
    EulerEq 𝔼 (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω)) (fun t ω => Real.exp (c t ω))
        (fun t ω => Real.exp (p t ω)) (fun t ω => Real.exp (z t ω)) t ↔
      ∀ ω, eulerMoment 𝔼 σ ρ i c p z t ω = 1 := by
  set G : Ω → ℝ := fun ω' => Real.exp (c (t + 1) ω') ^ (-σ) * Real.exp (z (t + 1) ω')
    / Real.exp (p (t + 1) ω') with hGdef
  have hmom : ∀ ω, eulerMoment 𝔼 σ ρ i c p z t ω
      = Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω) * 𝔼.E t G ω := by
    intro ω
    have hfun : (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
        - (p (t + 1) ω' - p t ω) + (z (t + 1) ω' - z t ω)))
        = Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω) • G := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hGdef]
      rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    rw [eulerMoment, hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [hmom ω]
  simp only
  rw [← hGdef]
  have e1 : Real.exp (c t ω) ^ σ * Real.exp (p t ω) / Real.exp (z t ω)
      = Real.exp (σ * c t ω + p t ω - z t ω) := by
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_sub, mul_comm (c t ω)]
  have e2 : Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω)
      = Real.exp (i t ω) * (Real.exp (-ρ) * Real.exp (σ * c t ω + p t ω - z t ω)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e1, e2]
  have hi : Real.exp (i t ω) * Real.exp (-i t ω) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  constructor
  · intro h
    rw [mul_assoc, ← h, hi]
  · intro h
    have hpos := Real.exp_pos (i t ω)
    have : Real.exp (-i t ω) = Real.exp (-i t ω) * (Real.exp (i t ω) *
        (Real.exp (-ρ) * Real.exp (σ * c t ω + p t ω - z t ω) * 𝔼.E t G ω)) := by
      rw [← mul_assoc (Real.exp (i t ω)), h, mul_one]
    rw [this, ← mul_assoc, mul_comm (Real.exp (-i t ω)), hi, one_mul]

/-- Galí (2015), eqs. (8) and (10), p. 21 (**exact, perfect foresight**): under perfect
foresight the Euler equation holds at date `t` iff, in logs,
`i_t − (p_{t+1} − p_t) − ρ = σ (c_{t+1} − c_t) − (z_{t+1} − z_t)`. -/
theorem pf_eulerEq_iff (σ ρ : ℝ) (i c p z : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
        (fun t ω => Real.exp (z t ω)) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ
        = σ * (c (t + 1) ω - c t ω) - (z (t + 1) ω - z t ω) := by
  rw [eulerEq_iff_moment]
  refine forall_congr' fun ω => ?_
  simp only [eulerMoment, perfectForesight, LinearMap.id_apply]
  rw [← Real.exp_zero, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (10), p. 21 (**exact, perfect foresight, no preference shock**): with
`Z ≡ 1` the
Euler equation is exactly `i_t − π_{t+1} − ρ = σ (c_{t+1} − c_t)` in logs. -/
theorem pf_eulerEq_iff_noshock (σ ρ : ℝ) (i c p : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω)) (fun _ _ => 1) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ = σ * (c (t + 1) ω - c t ω) := by
  have h := pf_eulerEq_iff σ ρ i c p (fun _ _ => 0) t
  simp only [Real.exp_zero, sub_self, sub_zero] at h
  exact h

/-! ### The first-order approximation under uncertainty -/

/-- Galí (2015), App. 2.1, p. 44 (the first-order step): for a bounded random variable
`Y`, `s ↦ E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. Only linearity,
monotonicity and constants of `E_t` are used: the remainder `exp(sY) − 1 − sY` is bounded by
`s² M²` uniformly, and `|E_t x| ≤ sup |x|`. -/
theorem hasDerivAt_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω) (𝔼.E t Y ω) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero]
  have hO : (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
      - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω) =O[𝓝 0]
      fun s : ℝ => s ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (M ^ 2)
    have hcont : Continuous (fun s : ℝ => |s| * M) := by fun_prop
    have hlim : Tendsto (fun s : ℝ => |s| * M) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto 0
      rwa [abs_zero, zero_mul] at this
    filter_upwards [hlim.eventually (ge_mem_nhds one_pos)] with s hs
    have key : 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
        - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω
        = 𝔼.E t (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω') ω := by
      have h1 : (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω')
          = (fun ω' => Real.exp (s * Y ω')) - (fun _ => (1 : ℝ)) - s • Y := by
        funext ω'
        simp
      have h2 : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
        funext ω'
        simp
      rw [h1, h2, map_sub, map_sub, map_smul, 𝔼.const]
      simp
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs]
    apply 𝔼.abs_E_le
    intro ω'
    have hy : |s * Y ω'| ≤ 1 := by
      rw [abs_mul]
      calc |s| * |Y ω'| ≤ |s| * M := mul_le_mul_of_nonneg_left (hY ω') (abs_nonneg s)
        _ ≤ 1 := hs
    have hsq : (s * Y ω') ^ 2 ≤ M ^ 2 * |s ^ 2| := by
      rw [abs_pow, sq_abs, mul_pow, mul_comm]
      have : Y ω' ^ 2 ≤ M ^ 2 := by
        have := hY ω'
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg s)
    exact (Real.abs_exp_sub_one_sub_id_le hy).trans hsq
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Galí (2015), App. 2.1, p. 44: for a bounded `Y`,
`s ↦ log E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. -/
theorem hasDerivAt_log_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω))
      (𝔼.E t Y ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω = 1 := by
    have : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
      funext ω'
      simp
    rw [this, 𝔼.const]
  have := (hasDerivAt_E_exp 𝔼 hY t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at this
  exact this

/-! ### The log-linear Euler equation (10) as an exact derivative -/

/-- Galí (2015), App. 2.1, p. 44: the map
`(i, Δc, π, Δz) ↦ exp(i − σ Δc − π − ρ + Δz)` whose conditional expectation is one in
eq. (51). -/
noncomputable def eulerKernel (σ ρ : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  Real.exp (v 0 - σ * v 1 - v 2 - ρ + v 3)

/-- Galí (2015), App. 2.1, p. 44: the perfect-foresight steady state with inflation `π̄` and
consumption growth `γ`, `(i, Δc, π, Δz) = (ρ + π̄ + σγ, γ, π̄, 0)`. -/
noncomputable def steadyPoint (σ ρ πbar γ : ℝ) : Fin 4 → ℝ := ![ρ + πbar + σ * γ, γ, πbar, 0]

/-- Galí (2015), App. 2.1, p. 44: the gradient `(1, −σ, −1, 1)` of `eulerKernel` at the steady
state, as a continuous linear functional. -/
noncomputable def eulerGrad (σ : ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 - σ • ContinuousLinearMap.proj 1 - ContinuousLinearMap.proj 2
    + ContinuousLinearMap.proj 3

/-- Galí (2015), App. 2.1, p. 44: `eulerGrad σ v = v₀ − σ v₁ − v₂ + v₃`. -/
theorem eulerGrad_apply (σ : ℝ) (v : Fin 4 → ℝ) : eulerGrad σ v = v 0 - σ * v 1 - v 2 + v 3 :=
  rfl

/-- Galí (2015), App. 2.1, p. 44: the steady state `i = ρ + π̄ + σγ` satisfies (51) exactly,
`exp(i − σγ − π̄ − ρ + 0) = 1`. -/
theorem eulerKernel_steady (σ ρ πbar γ : ℝ) : eulerKernel σ ρ (steadyPoint σ ρ πbar γ) = 1 := by
  have h0 : steadyPoint σ ρ πbar γ 0 = ρ + πbar + σ * γ := rfl
  have h1 : steadyPoint σ ρ πbar γ 1 = γ := rfl
  have h2 : steadyPoint σ ρ πbar γ 2 = πbar := rfl
  have h3 : steadyPoint σ ρ πbar γ 3 = 0 := rfl
  simp only [eulerKernel, h0, h1, h2, h3]
  rw [← Real.exp_zero]
  congr 1
  ring

/-- Galí (2015), App. 2.1, p. 44 (**the first-order Taylor expansion as an exact derivative**):
`eulerKernel` has Fréchet derivative `(1, −σ, −1, 1)` at the steady state, i.e. value `1` and
gradient `(1, −σ, −1, 1)` — the coefficients of the book's expansion. -/
theorem hasFDerivAt_eulerKernel (σ ρ πbar γ : ℝ) :
    HasFDerivAt (eulerKernel σ ρ) (eulerGrad σ) (steadyPoint σ ρ πbar γ) := by
  have hfun : eulerKernel σ ρ = fun v => Real.exp (eulerGrad σ v - ρ) := by
    funext v
    simp only [eulerKernel, eulerGrad_apply]
    congr 1
    ring
  have h := ((eulerGrad σ).hasFDerivAt (x := steadyPoint σ ρ πbar γ)).sub_const ρ |>.exp
  rw [hfun]
  have h1 : Real.exp (eulerGrad σ (steadyPoint σ ρ πbar γ) - ρ) = 1 := by
    have := eulerKernel_steady σ ρ πbar γ
    rw [hfun] at this
    exact this
  rw [h1, one_smul] at h
  exact h

/-- Galí (2015), App. 2.1, p. 44: the first-order approximation
`1 + (i − i*) − σ(Δc − γ) − (π − π̄) + Δz` equals `1 + i − σΔc − π − ρ + Δz` (the book's second
line), since `i* = ρ + π̄ + σγ`. -/
theorem eulerKernel_linearisation (σ ρ πbar γ : ℝ) (v : Fin 4 → ℝ) :
    eulerKernel σ ρ (steadyPoint σ ρ πbar γ) + eulerGrad σ (v - steadyPoint σ ρ πbar γ)
      = 1 + v 0 - σ * v 1 - v 2 - ρ + v 3 := by
  have h0 : steadyPoint σ ρ πbar γ 0 = ρ + πbar + σ * γ := rfl
  have h1 : steadyPoint σ ρ πbar γ 1 = γ := rfl
  have h2 : steadyPoint σ ρ πbar γ 2 = πbar := rfl
  have h3 : steadyPoint σ ρ πbar γ 3 = 0 := rfl
  rw [eulerKernel_steady, eulerGrad_apply]
  simp only [Pi.sub_apply, h0, h1, h2, h3]
  ring

/-- Galí (2015), App. 2.1, p. 44: along the family of paths `i = ρ + π̄ + σγ + s î`,
`c_t = c̄ + γ t + s ĉ_t`, `p_t = p̄ + π̄ t + s p̂_t`, `z = s ẑ` around the steady state with
inflation `π̄` and growth `γ`, the Euler moment is `E_t[exp(s Y)]` for the deviation
`Y = î_t + σ ĉ_t + p̂_t − ẑ_t − σ ĉ_{t+1} − p̂_{t+1} + ẑ_{t+1}`. -/
theorem eulerMoment_family (σ ρ πbar γ cbar pbar s : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    eulerMoment 𝔼 σ ρ (fun t ω => ρ + πbar + σ * γ + s * ih t ω)
      (fun t ω => cbar + γ * t + s * ch t ω) (fun t ω => pbar + πbar * t + s * ph t ω)
      (fun t ω => s * zh t ω) t ω
    = 𝔼.E t (fun ω' => Real.exp (s * (ih t ω + σ * ch t ω + ph t ω - zh t ω
        - σ * ch (t + 1) ω' - ph (t + 1) ω' + zh (t + 1) ω'))) ω := by
  unfold eulerMoment
  refine congrArg (fun x => 𝔼.E t x ω) (funext fun ω' => ?_)
  congr 1
  push_cast
  ring

/-- Galí (2015), App. 2.1, p. 44: the steady state with inflation `π̄`, growth `γ` and
`i = ρ + π̄ + σγ` satisfies the Euler equation (51): the Euler moment is one at `s = 0`. -/
theorem eulerMoment_family_zero (σ ρ πbar γ cbar pbar : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    eulerMoment 𝔼 σ ρ (fun t ω => ρ + πbar + σ * γ + 0 * ih t ω)
      (fun t ω => cbar + γ * t + 0 * ch t ω) (fun t ω => pbar + πbar * t + 0 * ph t ω)
      (fun t ω => 0 * zh t ω) t ω = 1 := by
  rw [eulerMoment_family]
  simp only [zero_mul, Real.exp_zero]
  exact congrFun (𝔼.const t 1) ω

/-- Galí (2015), eq. (10), p. 21: the linear expression obtained by linearising the Euler
moment, in deviations (hats): `î_t − σ (E_t ĉ_{t+1} − ĉ_t) − (E_t p̂_{t+1} − p̂_t)
+ (E_t ẑ_{t+1} − ẑ_t)` (restated from the Chapter 3 project). -/
noncomputable def linearisedEuler (σ : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
    + (𝔼.E t (zh (t + 1)) ω - zh t ω)

/-- Galí (2015), eq. (10), p. 21, and App. 2.1, p. 44 (**exact derivative under
uncertainty**): along the family of `eulerMoment_family` with bounded deviations, the log
Euler residual `s ↦ log E_t[exp(i_t − ρ − σΔc − Δp + Δz)](ω)` has derivative at `s = 0` equal
to `linearisedEuler σ î ĉ p̂ ẑ t ω`. -/
theorem hasDerivAt_log_eulerMoment_family (σ ρ πbar γ cbar pbar : ℝ)
    {ih ch ph zh : ℕ → Ω → ℝ} (hc : BoundedProc ch) (hp : BoundedProc ph)
    (hz : BoundedProc zh) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (eulerMoment 𝔼 σ ρ
        (fun t ω => ρ + πbar + σ * γ + s * ih t ω) (fun t ω => cbar + γ * t + s * ch t ω)
        (fun t ω => pbar + πbar * t + s * ph t ω) (fun t ω => s * zh t ω) t ω))
      (linearisedEuler 𝔼 σ ih ch ph zh t ω) 0 := by
  obtain ⟨Mc, hMc⟩ := hc
  obtain ⟨Mp, hMp⟩ := hp
  obtain ⟨Mz, hMz⟩ := hz
  set a : ℝ := ih t ω + σ * ch t ω + ph t ω - zh t ω with ha
  set Y : Ω → ℝ := fun ω' => ih t ω + σ * ch t ω + ph t ω - zh t ω
    - σ * ch (t + 1) ω' - ph (t + 1) ω' + zh (t + 1) ω' with hY
  have hbd : ∀ ω', |Y ω'| ≤ |a| + |σ| * Mc + Mp + Mz := by
    intro ω'
    have h1 := abs_le.1 (show |σ * ch (t + 1) ω'| ≤ |σ| * Mc by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMc _ _) (abs_nonneg σ))
    have h2 := abs_le.1 (hMp (t + 1) ω')
    have h3 := abs_le.1 (hMz (t + 1) ω')
    have h4 := abs_le.1 (le_refl |a|)
    rw [abs_le]
    simp only [hY]
    constructor <;> linarith
  simp_rw [eulerMoment_family]
  have hval : 𝔼.E t Y ω = linearisedEuler 𝔼 σ ih ch ph zh t ω := by
    have hfun : Y = (fun _ => a) + ((-σ) • ch (t + 1) - ph (t + 1) + zh (t + 1)) := by
      funext ω'
      simp only [hY, ha, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, map_add, 𝔼.const, map_add, map_sub, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, linearisedEuler, ha]
    ring
  rw [← hval]
  exact hasDerivAt_log_E_exp 𝔼 hbd t ω

/-- Galí (2015), eq. (10), p. 21: the log-linear Euler equation as a model equation,
`c_t = E_t c_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t` (restated from the
Chapter 3 project). -/
def EulerLogLinear (σ ρ ρz : ℝ) (c i infl z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), eq. (10), p. 21: for an adapted (log) price level `p̂` with inflation
`π̂_{t+1} = p̂_{t+1} − p̂_t`, the linearised Euler expression is
`î_t − σ (E_t ĉ_{t+1} − ĉ_t) − E_t π̂_{t+1} + (E_t ẑ_{t+1} − ẑ_t)`. -/
theorem linearisedEuler_eq (σ : ℝ) {ih ch ph zh infl : ℕ → Ω → ℝ} (hp : 𝔼.Adapted ph)
    (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) (t : ℕ) :
    linearisedEuler 𝔼 σ ih ch ph zh t = ih t - σ • (𝔼.E t (ch (t + 1)) - ch t)
      - 𝔼.E t (infl (t + 1)) + (𝔼.E t (zh (t + 1)) - zh t) := by
  funext ω
  rw [hinfl, map_sub, hp t]
  simp [linearisedEuler]

/-- Galí (2015), eq. (10), p. 21 (**the first-order condition is exactly (10)**): for
`σ ≠ 0`, an adapted price level and an AR(1) preference shifter (`E_t ẑ_{t+1} = ρ_z ẑ_t`,
p. 21), the derivative of `hasDerivAt_log_eulerMoment_family` vanishes at every date and node
iff (10) holds for the levels `c_t = c̄ + γ t + ĉ_t`, `i_t = ρ + π̄ + σγ + î_t`,
`π_{t+1} = π̄ + π̂_{t+1}`, `z = ẑ`. -/
theorem linearisedEuler_eq_zero_iff {σ ρ ρz πbar γ cbar : ℝ} (hσ : σ ≠ 0)
    {ih ch ph zh infl : ℕ → Ω → ℝ} (hp : 𝔼.Adapted ph)
    (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) (hzar : 𝔼.IsAR1 ρz zh) :
    (∀ t, linearisedEuler 𝔼 σ ih ch ph zh t = 0) ↔
      EulerLogLinear 𝔼 σ ρ ρz (fun t => (fun _ => cbar + γ * t) + ch t)
        (fun t => (fun _ => ρ + πbar + σ * γ) + ih t) (fun t => (fun _ => πbar) + infl t) zh := by
  unfold EulerLogLinear
  refine forall_congr' fun t => ?_
  rw [linearisedEuler_eq 𝔼 σ hp hinfl t, hzar.2 t]
  simp only [map_add, 𝔼.const]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    push_cast
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    push_cast at e
    field_simp at e
    linear_combination e

/-- Galí (2015), eq. (10), p. 21 (**exact under perfect foresight**): if the nonlinear Euler
equation holds at every date, `π_{t+1} = p_{t+1} − p_t`, and the preference shifter follows
`z_{t+1} = ρ_z z_t`, then (10) holds exactly (`σ ≠ 0`). -/
theorem pf_eulerEq_imp_eulerLogLinear {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {i c p z infl : ℕ → Unit → ℝ}
    (heul : ∀ t, EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
      (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
      (fun t ω => Real.exp (z t ω)) t)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (hz : ∀ t, z (t + 1) = ρz • z t) :
    EulerLogLinear perfectForesight σ ρ ρz c i infl z := by
  intro t
  have h := (pf_eulerEq_iff σ ρ i c p z t).1 (heul t)
  funext ω
  have e := h ω
  have ez := congrFun (hz t) ω
  have ei := congrFun (hinfl t) ω
  simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at e ez ei ⊢
  rw [ei]
  rw [ez] at e
  field_simp
  linear_combination e

/-! ### Footnote 5: the discount rate -/

/-- Galí (2015), fn. 5, p. 22: `ρ = −log β ≤ β⁻¹ − 1` for `β > 0`. -/
theorem neg_log_le_inv_sub_one {β : ℝ} (hβ : 0 < β) : -Real.log β ≤ β⁻¹ - 1 := by
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hβ)
  rwa [Real.log_inv] at this

/-- Galí (2015), fn. 5, p. 22: the gap in `ρ ≃ β⁻¹ − 1` is second order:
`0 ≤ (β⁻¹ − 1) − (−log β) ≤ (1 − β)²/β` for every `β > 0`. -/
theorem discount_rate_gap {β : ℝ} (hβ : 0 < β) :
    0 ≤ (β⁻¹ - 1) - (-Real.log β) ∧ (β⁻¹ - 1) - (-Real.log β) ≤ (1 - β) ^ 2 / β := by
  refine ⟨by linarith [neg_log_le_inv_sub_one hβ], ?_⟩
  have h := Real.log_le_sub_one_of_pos hβ
  have e : (1 - β) ^ 2 / β = β⁻¹ - 1 + (β - 1) := by field_simp; ring
  rw [e]
  linarith

/-- Galí (2015), fn. 5, p. 22: `(β⁻¹ − 1) − (−log β) = O((1 − β)²)` as `β → 1`. -/
theorem discount_rate_gap_isBigO :
    (fun β : ℝ => (β⁻¹ - 1) - (-Real.log β)) =O[𝓝 1] fun β => (1 - β) ^ 2 := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [lt_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num)] with β hβ
  have hβ0 : 0 < β := by linarith
  obtain ⟨h1, h2⟩ := discount_rate_gap hβ0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg (sq_nonneg _)]
  refine h2.trans ?_
  rw [div_le_iff₀ hβ0]
  nlinarith [sq_nonneg (1 - β)]

/-! ### Money demand (11) -/

/-- Galí (2015), eq. (11), p. 22: the log-linear money demand `m_t − p_t = c_t − η i_t`
(up to an additive constant, set to zero), with interest semielasticity `η ≥ 0`. -/
def MoneyDemand (η : ℝ) (m p c i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, m t - p t = c t - η • i t

/-- Galí (2015), eq. (11), p. 22: money demand pins down the price level given money,
consumption and the nominal rate: `p_t = m_t − c_t + η i_t`. -/
theorem moneyDemand_iff_price (η : ℝ) (m p c i : ℕ → Ω → ℝ) :
    MoneyDemand η m p c i ↔ ∀ t, p t = m t - c t + η • i t := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> funext ω <;> have e := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢ <;> linarith

/-- Galí (2015), eq. (11), p. 22: `η` is the interest semielasticity of real balances,
`∂(m − p)/∂i = −η`. -/
theorem moneyDemand_semielasticity (η c : ℝ) (i : ℝ) :
    HasDerivAt (fun i' : ℝ => c - η * i') (-η) i := by
  simpa using ((hasDerivAt_id i).const_mul η).const_sub c

end Gali.ClassicalMonetaryModel.Household

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Firms, equilibrium and monetary neutrality

Galí (2015), Chapter 2, §2.2–2.3 (pp. 22–24) and §2.4.4 (p. 30).

## Main results

* Eq. (14): `labour_demand_iff` (an interior `N` maximises profits iff `W/P = (1 − α)A N^{−α}`,
  `0 ≤ α < 1`), `labour_demand_unique` (for `0 < α < 1` the explicit `labourDemand` is the
  unique maximiser over `N ≥ 0`), `labour_demand_not_unique_alpha_zero` (at `α = 0` it is not
  unique). Eq. (15): `labour_demand_log_iff` (exact).
* Eqs. (16)–(19), (21): `staticBlock_iff` — for `D = σ(1 − α) + φ + α ≠ 0` the four static
  conditions (9), (15), (16), (17) hold iff `n = ψ_na a + ψ_n`, `y = ψ_ya a + ψ_y`, `c = y`,
  `ω = ψ_ωa a + ψ_ω`; `staticBlock_exists`, `staticBlock_unique`. `bigD_pos` (`σ > 0`) and the
  correction C2-1: `bigD_zero_counterexample`, `staticBlock_degenerate_no_solution`,
  `staticBlock_degenerate_many`. The static block is exactly log-linear:
  `levelsBlock_iff_log`, `levelsBlock_iff_explicit`.
* Comparative statics, p. 24: `psiYa_pos`, `psiWa_pos`, `psiNa_pos_iff`, `psiNa_eq_zero_iff`,
  `psiNa_neg_iff`, `sign_psiNa`; the real rate (correction C2-2): `rateCoeffA_neg_iff`,
  `rateCoeffA_rho_one`, `realRate_no_z_response`.
* Eq. (20): `realRate_of_euler`, `realRate_eq` (under any `ExpectationSystem`),
  `realRate_eq_pf` (exact, nonlinear, perfect foresight), `equilibrium_realRate`.
* Neutrality, p. 24: `Equilibrium`, `EquilibriumUnder` (any monetary policy, as a predicate on
  the nominal paths), `neutrality`, `neutrality_across_policies`, `equilibrium_of_allocation`
  (the real allocation with any nominal paths delivering the real rate is an equilibrium);
  in levels: `levels_neutrality`, `realBondPrice_neutral`.
* §2.4.4: `welfare_policy_invariant`, `welfare_limit_policy_invariant`.
-/

namespace Gali.ClassicalMonetaryModel.FirmsEquilibrium

open Filter Topology

/-! ### The firm's problem, eqs. (12)–(15) -/

/-- Galí (2015), eqs. (12)–(13), p. 22: profits `P A N^{1−α} − W N`. -/
noncomputable def profit (P W A α N : ℝ) : ℝ := P * (A * N ^ (1 - α)) - W * N

/-- Galí (2015), eq. (14), p. 23: the derivative of profits in `N > 0`,
`P (1 − α) A N^{−α} − W`. -/
theorem hasDerivAt_profit (P W A α : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (profit P W A α) (P * (A * ((1 - α) * N ^ (-α))) - W) N := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).const_mul P
  have h2 := h.sub ((hasDerivAt_id N).const_mul W)
  rw [show (1 : ℝ) - α - 1 = -α by ring, mul_one] at h2
  exact h2

/-- Galí (2015), eq. (14), p. 23 (**necessity**): an interior local profit maximum `N > 0`
satisfies `W/P = (1 − α) A N^{−α}` (`P > 0`). -/
theorem labour_demand_necessary {P W A α N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hloc : IsLocalMax (profit P W A α) N) : W / P = (1 - α) * A * N ^ (-α) := by
  have h := hloc.hasDerivAt_eq_zero (hasDerivAt_profit P W A α hN)
  field_simp
  linarith

/-- Galí (2015), eq. (14), p. 23 (**sufficiency**, by concavity for `0 ≤ α < 1`): if
`W/P = (1 − α) A N^{−α}` at `N > 0` (`P > 0`, `A ≥ 0`), then `N` maximises profits over all
`N' ≥ 0`. -/
theorem labour_demand_sufficient {P W A α N : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hP : 0 < P)
    (hA : 0 ≤ A) (hN : 0 < N) (hfoc : W / P = (1 - α) * A * N ^ (-α)) {N' : ℝ} (hN' : 0 ≤ N') :
    profit P W A α N' ≤ profit P W A α N := by
  have htan : N' ^ (1 - α) ≤ N ^ (1 - α) + (1 - α) * N ^ (-α) * (N' - N) := by
    refine Household.le_tangent (f := fun x => x ^ (1 - α))
      (f' := fun x => (1 - α) * x ^ (-α)) hN hN' ?_ (fun z hz => ?_) ?_
    · exact (Real.continuous_rpow_const (by linarith)).continuousOn
    · have := Real.hasDerivAt_rpow_const (x := z) (p := 1 - α) (Or.inl hz.ne')
      rwa [show (1 : ℝ) - α - 1 = -α by ring] at this
    · intro u hu v _ huv
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu huv (by linarith))
        (by linarith)
  have hW : W = P * ((1 - α) * A * N ^ (-α)) := by
    rw [← hfoc]
    field_simp
  unfold profit
  have := mul_le_mul_of_nonneg_left htan (mul_nonneg hP.le hA)
  rw [hW]
  nlinarith

/-- Galí (2015), eq. (14), p. 23: for `0 ≤ α < 1`, `P > 0`, `A ≥ 0` and `N > 0`, `N` maximises
profits over `N' ≥ 0` iff `W/P = (1 − α) A N^{−α}`. -/
theorem labour_demand_iff {P W A α N : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hP : 0 < P)
    (hA : 0 ≤ A) (hN : 0 < N) :
    (∀ N', 0 ≤ N' → profit P W A α N' ≤ profit P W A α N) ↔
      W / P = (1 - α) * A * N ^ (-α) := by
  constructor
  · intro h
    refine labour_demand_necessary hP hN ?_
    filter_upwards [eventually_gt_nhds hN] with N' hN'
    exact h N' hN'.le
  · intro h N' hN'
    exact labour_demand_sufficient hα0 hα1 hP hA hN h hN'

/-- Galí (2015), eq. (14), p. 23: the labour demand `N* = ((1 − α) A P/W)^{1/α}`. -/
noncomputable def labourDemand (P W A α : ℝ) : ℝ := ((1 - α) * A * P / W) ^ α⁻¹

/-- Galí (2015), eq. (14), p. 23 (**uniqueness** for `0 < α < 1`): with `P, W, A > 0`, the
labour demand `N*` is positive, maximises profits over `N ≥ 0`, and is the only maximiser. -/
theorem labour_demand_unique {P W A α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hP : 0 < P)
    (hW : 0 < W) (hA : 0 < A) :
    0 < labourDemand P W A α ∧
      ∀ N, 0 ≤ N → ((∀ N', 0 ≤ N' → profit P W A α N' ≤ profit P W A α N) ↔
        N = labourDemand P W A α) := by
  set K := (1 - α) * A * P / W with hK
  have hK0 : 0 < K := by
    have : 0 < 1 - α := by linarith
    positivity
  have hNs : 0 < labourDemand P W A α := Real.rpow_pos_of_pos hK0 _
  -- the FOC holds at `N*`
  have hpow : labourDemand P W A α ^ (-α) = K⁻¹ := by
    unfold labourDemand
    rw [← hK, ← Real.rpow_mul hK0.le, show α⁻¹ * -α = -1 by field_simp, Real.rpow_neg_one]
  have hfoc : W / P = (1 - α) * A * labourDemand P W A α ^ (-α) := by
    rw [hpow, hK]
    have : (1 - α) ≠ 0 := by linarith
    field_simp
  have hmax := fun N' (hN' : 0 ≤ N') =>
    labour_demand_sufficient hα0.le hα1 hP hA.le hNs hfoc hN'
  refine ⟨hNs, fun N hN => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases hN.lt_or_eq with hN0 | hN0
    · have hf := (labour_demand_iff hα0.le hα1 hP hA.le hN0).1 h
      -- `N^{−α}` is injective
      have h1 : N ^ (-α) = labourDemand P W A α ^ (-α) := by
        have h2 : (1 - α) * A ≠ 0 := by
          have : 0 < 1 - α := by linarith
          positivity
        have := hf.symm.trans hfoc
        rw [mul_right_inj' h2] at this
        exact this
      have hα : -α ≠ 0 := by linarith
      rw [← Real.rpow_rpow_inv hN hα, h1, Real.rpow_rpow_inv hNs.le hα]
    · -- `N = 0` earns zero profit, `N*` earns a positive profit
      exfalso
      have h0 := h _ hNs.le
      rw [← hN0] at h0
      have hp0 : profit P W A α 0 = 0 := by
        simp [profit, Real.zero_rpow (show (1 : ℝ) - α ≠ 0 by linarith)]
      rw [hp0] at h0
      have hval : profit P W A α (labourDemand P W A α)
          = labourDemand P W A α * (W * α / (1 - α)) := by
        unfold profit
        have hs : labourDemand P W A α ^ (1 - α)
            = labourDemand P W A α * labourDemand P W A α ^ (-α) := by
          rw [sub_eq_add_neg, Real.rpow_add hNs, Real.rpow_one]
        rw [hs, hpow, hK]
        have : (1 - α) ≠ 0 := by linarith
        field_simp
        ring
      have : 0 < labourDemand P W A α * (W * α / (1 - α)) := by
        have : 0 < 1 - α := by linarith
        positivity
      linarith
  · rw [h]
    exact hmax

/-- Galí (2015), p. 23 (**non-uniqueness at `α = 0`**, so the book's uniqueness needs
`α > 0`): with constant returns and `W = P A`, profits are zero for every `N`, so every
`N ≥ 0` (e.g. `1` and `2`) maximises profits. -/
theorem labour_demand_not_unique_alpha_zero {P A : ℝ} :
    ∀ N N', profit P (P * A) A 0 N' ≤ profit P (P * A) A 0 N := by
  intro N N'
  simp [profit]
  ring_nf
  rfl

/-- Galí (2015), eq. (15), p. 23 (**exact**): for positive levels and `α < 1`,
`W/P = (1 − α) A N^{−α}` iff `w − p = a − α n + log(1 − α)` in logs. -/
theorem labour_demand_log_iff {W P A α N : ℝ} (hW : 0 < W) (hP : 0 < P) (hA : 0 < A)
    (hN : 0 < N) (hα : α < 1) :
    W / P = (1 - α) * A * N ^ (-α) ↔
      Real.log W - Real.log P = Real.log A - α * Real.log N + Real.log (1 - α) := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hr : 0 < (1 - α) * A * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  rw [← Real.log_injOn_pos.eq_iff (div_pos hW hP) hr, Real.log_div hW.ne' hP.ne',
    Real.log_mul (by positivity) (Real.rpow_pos_of_pos hN _).ne',
    Real.log_mul h1.ne' hA.ne', Real.log_rpow hN]
  constructor <;> intro h <;> linarith

/-! ### The equilibrium real block, eqs. (16)–(21) -/

/-- Galí (2015), p. 23: `D = σ(1 − α) + φ + α`, the denominator of every `ψ`. -/
def bigD (σ φ α : ℝ) : ℝ := σ * (1 - α) + φ + α

/-- Galí (2015), p. 23: `ψ_na = (1 − σ)/D`. -/
noncomputable def psiNa (σ φ α : ℝ) : ℝ := (1 - σ) / bigD σ φ α

/-- Galí (2015), p. 23: `ψ_n = log(1 − α)/D`. -/
noncomputable def psiN (σ φ α : ℝ) : ℝ := Real.log (1 - α) / bigD σ φ α

/-- Galí (2015), p. 23: `ψ_ya = (1 + φ)/D`. -/
noncomputable def psiYa (σ φ α : ℝ) : ℝ := (1 + φ) / bigD σ φ α

/-- Galí (2015), p. 23: `ψ_y = (1 − α) ψ_n`. -/
noncomputable def psiY (σ φ α : ℝ) : ℝ := (1 - α) * psiN σ φ α

/-- Galí (2015), p. 24: `ψ_ωa = (σ + φ)/D`. -/
noncomputable def psiWa (σ φ α : ℝ) : ℝ := (σ + φ) / bigD σ φ α

/-- Galí (2015), p. 24: `ψ_ω = (σ(1 − α) + φ) log(1 − α)/D`. -/
noncomputable def psiW (σ φ α : ℝ) : ℝ := (σ * (1 - α) + φ) * Real.log (1 - α) / bigD σ φ α

/-- Galí (2015), p. 23 (correction C2-1): `D > 0` for `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem bigD_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < bigD σ φ α := by
  unfold bigD
  have : 0 < σ * (1 - α) := mul_pos hσ (by linarith)
  linarith

/-- Galí (2015), p. 20 (correction C2-1): with the book's `σ ≥ 0`, `D` can vanish:
`σ = φ = α = 0` gives `D = 0`. -/
theorem bigD_zero_counterexample : bigD 0 0 0 = 0 := by norm_num [bigD]

/-- Galí (2015), eqs. (9), (15), (16), (17), pp. 21–23: the static equilibrium conditions at
one date and state, in logs: labour supply `ω = σ c + φ n`, labour demand
`ω = a − α n + log(1 − α)`, goods-market clearing `y = c`, and the production function
`y = a + (1 − α) n`. -/
def StaticBlock (σ φ α a y c n ω : ℝ) : Prop :=
  ω = σ * c + φ * n ∧ ω = a - α * n + Real.log (1 - α) ∧ y = c ∧ y = a + (1 - α) * n

/-- Galí (2015), eqs. (18), (19), (21), pp. 23–24 (**the unique solution**): if `D ≠ 0`, the
static block holds iff `n = ψ_na a + ψ_n`, `y = ψ_ya a + ψ_y`, `c = y` and
`ω = ψ_ωa a + ψ_ω`. -/
theorem staticBlock_iff {σ φ α a y c n ω : ℝ} (hD : bigD σ φ α ≠ 0) :
    StaticBlock σ φ α a y c n ω ↔
      n = psiNa σ φ α * a + psiN σ φ α ∧ y = psiYa σ φ α * a + psiY σ φ α ∧ c = y ∧
        ω = psiWa σ φ α * a + psiW σ φ α := by
  unfold psiY psiNa psiN psiYa psiWa psiW
  unfold bigD at hD ⊢
  have hk : (σ * (1 - α) + φ + α) * (σ * (1 - α) + φ + α)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hc : c = a + (1 - α) * n := h3.symm.trans h4
    have hn : n * (σ * (1 - α) + φ + α) = (1 - σ) * a + Real.log (1 - α) := by
      linear_combination h2 - h1 - σ * hc
    have hn' : n = (1 - σ) * (σ * (1 - α) + φ + α)⁻¹ * a
        + Real.log (1 - α) * (σ * (1 - α) + φ + α)⁻¹ := by
      linear_combination (σ * (1 - α) + φ + α)⁻¹ * hn - n * hk
    refine ⟨hn', ?_, h3.symm, ?_⟩
    · rw [h4, hn']
      linear_combination (-a) * hk
    · rw [h2, hn']
      linear_combination (-(a + Real.log (1 - α))) * hk
  · rintro ⟨hn, hy, hc, hω⟩
    refine ⟨?_, ?_, hc.symm, ?_⟩
    · rw [hω, hc, hy, hn]
      ring
    · rw [hω, hn]
      linear_combination (a + Real.log (1 - α)) * hk
    · rw [hy, hn]
      linear_combination a * hk

/-- Galí (2015), eqs. (18)–(21), pp. 23–24: for `D ≠ 0` the static block has a solution. -/
theorem staticBlock_exists {σ φ α : ℝ} (hD : bigD σ φ α ≠ 0) (a : ℝ) :
    StaticBlock σ φ α a (psiYa σ φ α * a + psiY σ φ α) (psiYa σ φ α * a + psiY σ φ α)
      (psiNa σ φ α * a + psiN σ φ α) (psiWa σ φ α * a + psiW σ φ α) :=
  (staticBlock_iff hD).2 ⟨rfl, rfl, rfl, rfl⟩

/-- Galí (2015), eqs. (18)–(21), pp. 23–24: for `D ≠ 0` the static block has at most one
solution. -/
theorem staticBlock_unique {σ φ α a y c n ω y' c' n' ω' : ℝ} (hD : bigD σ φ α ≠ 0)
    (h : StaticBlock σ φ α a y c n ω) (h' : StaticBlock σ φ α a y' c' n' ω') :
    y = y' ∧ c = c' ∧ n = n' ∧ ω = ω' := by
  obtain ⟨hn, hy, hc, hω⟩ := (staticBlock_iff hD).1 h
  obtain ⟨hn', hy', hc', hω'⟩ := (staticBlock_iff hD).1 h'
  refine ⟨by rw [hy, hy'], by rw [hc, hc', hy, hy'], by rw [hn, hn'], by rw [hω, hω']⟩

/-- Galí (2015), p. 20 (correction C2-1, **failure at `D = 0`**): with `σ = φ = α = 0` the
static block has no solution when `a ≠ 0` ... -/
theorem staticBlock_degenerate_no_solution {a y c n ω : ℝ} (ha : a ≠ 0) :
    ¬ StaticBlock 0 0 0 a y c n ω := by
  rintro ⟨h1, h2, -, -⟩
  simp only [zero_mul, add_zero, sub_zero, Real.log_one] at h1 h2
  exact ha (h2.symm.trans h1)

/-- Galí (2015), p. 20 (correction C2-1, **failure at `D = 0`**): ... and infinitely many
solutions when `a = 0`: every `n` gives one. -/
theorem staticBlock_degenerate_many (n : ℝ) : StaticBlock 0 0 0 0 n n n 0 := by
  refine ⟨by ring, ?_, rfl, by ring⟩
  simp

/-- Galí (2015), eqs. (7), (12), (14), (16), p. 21–23, in levels: labour supply
`W/P = C^σ N^φ`, labour demand `W/P = (1 − α) A N^{−α}`, `Y = C` and `Y = A N^{1−α}`, with the
real wage `w = W/P`. -/
def LevelsBlock (σ φ α A Y C N w : ℝ) : Prop :=
  w = C ^ σ * N ^ φ ∧ w = (1 - α) * A * N ^ (-α) ∧ Y = C ∧ Y = A * N ^ (1 - α)

/-- Galí (2015), pp. 21–23 (**the static block is exactly log-linear**): for positive levels
and `α < 1`, the conditions in levels hold iff their logs satisfy `StaticBlock`; no
approximation is involved. -/
theorem levelsBlock_iff_log {σ φ α A Y C N w : ℝ} (hα : α < 1) (hA : 0 < A) (hY : 0 < Y)
    (hC : 0 < C) (hN : 0 < N) (hw : 0 < w) :
    LevelsBlock σ φ α A Y C N w ↔ StaticBlock σ φ α (Real.log A) (Real.log Y) (Real.log C)
      (Real.log N) (Real.log w) := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hs : 0 < C ^ σ * N ^ φ := mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hN _)
  have hd : 0 < (1 - α) * A * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  have hp : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  unfold LevelsBlock StaticBlock
  rw [← Real.log_injOn_pos.eq_iff hw hs, ← Real.log_injOn_pos.eq_iff hw hd,
    ← Real.log_injOn_pos.eq_iff hY hC, ← Real.log_injOn_pos.eq_iff hY hp,
    Real.log_mul (Real.rpow_pos_of_pos hC _).ne' (Real.rpow_pos_of_pos hN _).ne',
    Real.log_rpow hC, Real.log_rpow hN,
    Real.log_mul (by positivity) (Real.rpow_pos_of_pos hN _).ne', Real.log_mul h1.ne' hA.ne',
    Real.log_rpow hN, Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN]
  constructor
  · rintro ⟨e1, e2, e3, e4⟩
    exact ⟨e1, by linarith, e3, by linarith⟩
  · rintro ⟨e1, e2, e3, e4⟩
    exact ⟨e1, by linarith, e3, by linarith⟩

/-- Galí (2015), eqs. (18)–(21), pp. 23–24, in levels (**exact**): for `D ≠ 0`, `α < 1` and
`A > 0`, the levels block has the unique positive solution
`N = exp(ψ_na a + ψ_n)`, `Y = C = exp(ψ_ya a + ψ_y)`, `W/P = exp(ψ_ωa a + ψ_ω)`, `a = log A`. -/
theorem levelsBlock_iff_explicit {σ φ α A Y C N w : ℝ} (hD : bigD σ φ α ≠ 0) (hα : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hC : 0 < C) (hN : 0 < N) (hw : 0 < w) :
    LevelsBlock σ φ α A Y C N w ↔
      N = Real.exp (psiNa σ φ α * Real.log A + psiN σ φ α) ∧
      Y = Real.exp (psiYa σ φ α * Real.log A + psiY σ φ α) ∧ C = Y ∧
      w = Real.exp (psiWa σ φ α * Real.log A + psiW σ φ α) := by
  have key : ∀ {u x : ℝ}, 0 < u → (Real.log u = x ↔ u = Real.exp x) := fun hu =>
    ⟨fun h => by rw [← h, Real.exp_log hu], fun h => by rw [h, Real.log_exp]⟩
  rw [levelsBlock_iff_log hα hA hY hC hN hw, staticBlock_iff hD, key hN, key hY, key hw,
    Real.log_injOn_pos.eq_iff hC hY]

/-! ### Comparative statics, p. 24 -/

/-- Galí (2015), p. 24: output always rises with technology, `ψ_ya > 0` (`D > 0`, `φ ≥ 0`). -/
theorem psiYa_pos {σ φ α : ℝ} (hφ : 0 ≤ φ) (hD : 0 < bigD σ φ α) : 0 < psiYa σ φ α :=
  div_pos (by linarith) hD

/-- Galí (2015), p. 24: the real wage rises with technology, `ψ_ωa > 0` (`σ > 0`, `φ ≥ 0`,
`D > 0`). -/
theorem psiWa_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hD : 0 < bigD σ φ α) :
    0 < psiWa σ φ α :=
  div_pos (by linarith) hD

/-- Galí (2015), p. 24: employment rises with technology iff `σ < 1`. -/
theorem psiNa_pos_iff {σ φ α : ℝ} (hD : 0 < bigD σ φ α) : 0 < psiNa σ φ α ↔ σ < 1 := by
  unfold psiNa
  rw [div_pos_iff_of_pos_right hD]
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 24: employment is unchanged by technology iff `σ = 1` (log utility). -/
theorem psiNa_eq_zero_iff {σ φ α : ℝ} (hD : 0 < bigD σ φ α) : psiNa σ φ α = 0 ↔ σ = 1 := by
  unfold psiNa
  rw [div_eq_zero_iff, or_iff_left hD.ne', sub_eq_zero, eq_comm]

/-- Galí (2015), p. 24: employment falls with technology iff `σ > 1`. -/
theorem psiNa_neg_iff {σ φ α : ℝ} (hD : 0 < bigD σ φ α) : psiNa σ φ α < 0 ↔ 1 < σ := by
  unfold psiNa
  rw [div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h
    right
    exact ⟨by linarith, hD⟩

/-- Galí (2015), p. 24: `sign ψ_na = sign(1 − σ)`. -/
theorem sign_psiNa {σ φ α : ℝ} (hD : 0 < bigD σ φ α) :
    SignType.sign (psiNa σ φ α) = SignType.sign (1 - σ) := by
  rcases lt_trichotomy σ 1 with h | h | h
  · rw [sign_pos ((psiNa_pos_iff hD).2 h), sign_pos (by linarith)]
  · rw [(psiNa_eq_zero_iff hD).2 h, h, sub_self, sign_zero]
  · rw [sign_neg ((psiNa_neg_iff hD).2 h), sign_neg (by linarith)]

/-- Galí (2015), eq. (20), p. 23: the coefficient `−σ(1 − ρ_a)ψ_ya` of `a_t` in the real
interest rate. -/
noncomputable def rateCoeffA (σ φ α ρa : ℝ) : ℝ := -(σ * (1 - ρa) * psiYa σ φ α)

/-- Galí (2015), p. 24 (correction C2-2): with `σ > 0`, `φ ≥ 0`, `D > 0` and `ρ_a ≤ 1`, the real
rate falls after a positive technology shock iff `ρ_a < 1`. -/
theorem rateCoeffA_neg_iff {σ φ α ρa : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hD : 0 < bigD σ φ α)
    (hρ : ρa ≤ 1) : rateCoeffA σ φ α ρa < 0 ↔ ρa < 1 := by
  unfold rateCoeffA
  have hy := psiYa_pos hφ hD
  constructor
  · intro h
    by_contra h'
    have : ρa = 1 := le_antisymm hρ (not_lt.1 h')
    rw [this] at h
    simp at h
  · intro h
    have : 0 < σ * (1 - ρa) * psiYa σ φ α := mul_pos (mul_pos hσ (by linarith)) hy
    linarith

/-- Galí (2015), p. 24 (correction C2-2, **counterexample** to the unqualified claim): with a
random-walk technology, `ρ_a = 1`, the real rate does not respond to technology at all. -/
theorem rateCoeffA_rho_one (σ φ α : ℝ) : rateCoeffA σ φ α 1 = 0 := by
  simp [rateCoeffA]

/-- Galí (2015), p. 24 (correction C2-2): with `ρ_z ≤ 1`, the real rate rises with the
preference shifter, coefficient `1 − ρ_z > 0`, iff `ρ_z < 1`. -/
theorem rateCoeffZ_pos_iff {ρz : ℝ} : 0 < 1 - ρz ↔ ρz < 1 := sub_pos

/-! ### The real interest rate, eq. (20) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (20), first line, p. 23: with goods-market clearing `c = y` and `σ ≠ 0`,
the log-linear Euler equation (10) gives the real rate
`r_t ≡ i_t − E_t π_{t+1} = ρ + (1 − ρ_z) z_t + σ (E_t y_{t+1} − y_t)`. -/
theorem realRate_of_euler {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {y i infl z : ℕ → Ω → ℝ}
    (heu : Household.EulerLogLinear 𝔼 σ ρ ρz y i infl z) (t : ℕ) :
    i t - 𝔼.E t (infl (t + 1)) = (fun _ => ρ) + (1 - ρz) • z t
      + σ • (𝔼.E t (y (t + 1)) - y t) := by
  have h := heu t
  funext ω
  have e := congrFun h ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  field_simp at e
  linear_combination e

/-- Galí (2015), eq. (20), p. 23: with output `y_t = ψ_ya a_t + ψ_y` and an AR(1) technology
(`E_t a_{t+1} = ρ_a a_t`), the real rate is `r_t = ρ + (1 − ρ_z) z_t − σ(1 − ρ_a) ψ_ya a_t`. -/
theorem realRate_eq {σ φ α ρ ρz ρa : ℝ} (hσ : σ ≠ 0) {y i infl z a : ℕ → Ω → ℝ}
    (heu : Household.EulerLogLinear 𝔼 σ ρ ρz y i infl z)
    (hy : ∀ t, y t = psiYa σ φ α • a t + fun _ => psiY σ φ α) (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    i t - 𝔼.E t (infl (t + 1)) = (fun _ => ρ) + (1 - ρz) • z t
      + rateCoeffA σ φ α ρa • a t := by
  rw [realRate_of_euler 𝔼 hσ heu t, hy (t + 1), hy t, map_add, map_smul, ha.2 t, 𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rateCoeffA]
  ring

/-- Galí (2015), eq. (20), p. 23 (**exact under perfect foresight**): if the nonlinear Euler
equation (8) holds at every date (with `Q = e^{−i}`, `β = e^{−ρ}`, `C = Y = e^y`, `P = e^p`,
`Z = e^z`), output is `y_t = ψ_ya a_t + ψ_y`, and `a_{t+1} = ρ_a a_t`, `z_{t+1} = ρ_z z_t`, then
the real rate `i_t − (p_{t+1} − p_t)` equals `ρ + (1 − ρ_z) z_t − σ(1 − ρ_a)ψ_ya a_t` exactly. -/
theorem realRate_eq_pf {σ φ α ρ ρz ρa : ℝ} {i y p z a : ℕ → Unit → ℝ}
    (heul : ∀ t, Household.EulerEq perfectForesight (Real.exp (-ρ)) σ
      (fun t ω => Real.exp (-i t ω)) (fun t ω => Real.exp (y t ω))
      (fun t ω => Real.exp (p t ω)) (fun t ω => Real.exp (z t ω)) t)
    (hy : ∀ t ω, y t ω = psiYa σ φ α * a t ω + psiY σ φ α)
    (ha : ∀ t ω, a (t + 1) ω = ρa * a t ω) (hz : ∀ t ω, z (t + 1) ω = ρz * z t ω)
    (t : ℕ) (ω : Unit) :
    i t ω - (p (t + 1) ω - p t ω) = ρ + (1 - ρz) * z t ω + rateCoeffA σ φ α ρa * a t ω := by
  have h := (Household.pf_eulerEq_iff σ ρ i y p z t).1 (heul t) ω
  rw [hy (t + 1), hy t, ha, hz] at h
  unfold rateCoeffA
  linear_combination h

/-! ### Equilibrium and neutrality, p. 24 -/

/-- Galí (2015), §2.3, pp. 22–24: an equilibrium of the (log-linear) classical economy given
technology `a` and preferences `z`: the static block (9), (15)–(17) at every date and state,
the Euler equation (10), and the definition of the real rate `r_t = i_t − E_t π_{t+1}`.
Monetary policy enters only through the nominal variables `i`, `infl`. -/
def Equilibrium (σ φ α ρ ρz : ℝ) (a z y c n ω r i infl : ℕ → Ω → ℝ) : Prop :=
  (∀ t s, StaticBlock σ φ α (a t s) (y t s) (c t s) (n t s) (ω t s)) ∧
    Household.EulerLogLinear 𝔼 σ ρ ρz c i infl z ∧
    ∀ t, r t = i t - 𝔼.E t (infl (t + 1))

/-- Galí (2015), §2.3–2.4, pp. 22–30: an equilibrium under a monetary policy. A policy is any
condition on the nominal paths (interest rate `i`, inflation `infl`, money `m`, prices `p`):
an interest-rate rule, a money-supply rule, or an exogenous path. Money demand (11) and
`π_{t+1} = p_{t+1} − p_t` are imposed as well. -/
def EquilibriumUnder (σ φ α ρ ρz η : ℝ)
    (policy : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    (a z y c n ω r i infl m p : ℕ → Ω → ℝ) : Prop :=
  Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl ∧ Household.MoneyDemand η m p c i ∧
    (∀ t, infl (t + 1) = p (t + 1) - p t) ∧ policy i infl m p

/-- Galí (2015), eqs. (18)–(21), pp. 23–24: in every equilibrium (`D ≠ 0`) the real allocation
is `n = ψ_na a + ψ_n`, `y = c = ψ_ya a + ψ_y`, `ω = ψ_ωa a + ψ_ω`, whatever the nominal
variables. -/
theorem equilibrium_allocation {σ φ α ρ ρz : ℝ} (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl)
    (t : ℕ) (s : Ω) :
    n t s = psiNa σ φ α * a t s + psiN σ φ α ∧ y t s = psiYa σ φ α * a t s + psiY σ φ α ∧
      c t s = y t s ∧ ω t s = psiWa σ φ α * a t s + psiW σ φ α :=
  (staticBlock_iff hD).1 (h.1 t s)

/-- Galí (2015), p. 24 (**neutrality**): for `σ ≠ 0` and `D ≠ 0`, any two equilibria with the
same technology and preference shocks have identical output, consumption, employment, real
wage and real interest rate, whatever their nominal interest rates and inflation. -/
theorem neutrality {σ φ α ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl y' c' n' ω' r' i' infl' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl)
    (h' : Equilibrium 𝔼 σ φ α ρ ρz a z y' c' n' ω' r' i' infl') :
    y = y' ∧ c = c' ∧ n = n' ∧ ω = ω' ∧ r = r' := by
  have hst : ∀ t s, y t s = y' t s ∧ c t s = c' t s ∧ n t s = n' t s ∧ ω t s = ω' t s :=
    fun t s => staticBlock_unique hD (h.1 t s) (h'.1 t s)
  have hy : y = y' := funext fun t => funext fun s => (hst t s).1
  have hc : c = c' := funext fun t => funext fun s => (hst t s).2.1
  refine ⟨hy, hc, funext fun t => funext fun s => (hst t s).2.2.1,
    funext fun t => funext fun s => (hst t s).2.2.2, ?_⟩
  funext t
  rw [h.2.2 t, h'.2.2 t, realRate_of_euler 𝔼 hσ h.2.1 t, realRate_of_euler 𝔼 hσ h'.2.1 t, hc]

/-- Galí (2015), p. 24 (**neutrality across policies**): the real allocation and the real rate
are the same in an equilibrium under any monetary policy `policy₁` and in one under any other
policy `policy₂`. -/
theorem neutrality_across_policies {σ φ α ρ ρz η : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    (policy₁ policy₂ : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    {a z y c n ω r i infl m p y' c' n' ω' r' i' infl' m' p' : ℕ → Ω → ℝ}
    (h : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₁ a z y c n ω r i infl m p)
    (h' : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₂ a z y' c' n' ω' r' i' infl' m' p') :
    y = y' ∧ c = c' ∧ n = n' ∧ ω = ω' ∧ r = r' :=
  neutrality 𝔼 hσ hD h.1 h'.1

/-- Galí (2015), eq. (20), p. 23: in every equilibrium with an AR(1) technology the real rate
is `r_t = ρ + (1 − ρ_z) z_t − σ(1 − ρ_a)ψ_ya a_t`, independent of monetary policy. -/
theorem equilibrium_realRate {σ φ α ρ ρz ρa : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl)
    (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    r t = (fun _ => ρ) + (1 - ρz) • z t + rateCoeffA σ φ α ρa • a t := by
  have hcy : c = y := funext fun t => funext fun s => (equilibrium_allocation 𝔼 hD h t s).2.2.1
  have hy : ∀ t, y t = psiYa σ φ α • a t + fun _ => psiY σ φ α := fun t => by
    funext s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (equilibrium_allocation 𝔼 hD h t s).2.1
  have heu := h.2.1
  rw [hcy] at heu
  rw [h.2.2 t]
  exact realRate_eq 𝔼 hσ heu hy ha t

/-- Galí (2015), §2.3, in levels and under uncertainty (**exact neutrality of the static
block**): two positive allocations satisfying the levels block (7), (12), (14), (16) at a date
and state with the same technology `A` coincide (`D ≠ 0`, `α < 1`). -/
theorem levels_neutrality {σ φ α A Y C N w Y' C' N' w' : ℝ} (hD : bigD σ φ α ≠ 0) (hα : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hC : 0 < C) (hN : 0 < N) (hw : 0 < w) (hY' : 0 < Y')
    (hC' : 0 < C') (hN' : 0 < N') (hw' : 0 < w') (h : LevelsBlock σ φ α A Y C N w)
    (h' : LevelsBlock σ φ α A Y' C' N' w') : Y = Y' ∧ C = C' ∧ N = N' ∧ w = w' := by
  obtain ⟨e1, e2, e3, e4⟩ := (levelsBlock_iff_explicit hD hα hA hY hC hN hw).1 h
  obtain ⟨f1, f2, f3, f4⟩ := (levelsBlock_iff_explicit hD hα hA hY' hC' hN' hw').1 h'
  exact ⟨by rw [e2, f2], by rw [e3, f3, e2, f2], by rw [e1, f1], by rw [e4, f4]⟩

/-- Galí (2015), eq. (8), p. 21: the price of a one-period real (consumption-indexed) bond at
node `ω`, `β E_t[(C_{t+1}/C_t)^{−σ} Z_{t+1}/Z_t]`; its log is minus the real interest rate of
the nonlinear model. -/
noncomputable def realBondPrice (β σ : ℝ) (C Z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  β * 𝔼.E t (fun ω' => (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω)) ω

/-- Galí (2015), p. 24 (**exact neutrality of the real rate**, nonlinear model under
uncertainty): if two equilibria satisfy the levels block at every date and state with the same
technology, their real bond prices coincide at every node, whatever the nominal bond prices
and price levels. -/
theorem realBondPrice_neutral {σ φ α β : ℝ} (hD : bigD σ φ α ≠ 0) (hα : α < 1)
    {A Z Y C N w Y' C' N' w' : ℕ → Ω → ℝ} (hA : ∀ t s, 0 < A t s)
    (hpos : ∀ t s, 0 < Y t s ∧ 0 < C t s ∧ 0 < N t s ∧ 0 < w t s)
    (hpos' : ∀ t s, 0 < Y' t s ∧ 0 < C' t s ∧ 0 < N' t s ∧ 0 < w' t s)
    (h : ∀ t s, LevelsBlock σ φ α (A t s) (Y t s) (C t s) (N t s) (w t s))
    (h' : ∀ t s, LevelsBlock σ φ α (A t s) (Y' t s) (C' t s) (N' t s) (w' t s)) (t : ℕ) (s : Ω) :
    realBondPrice 𝔼 β σ C Z t s = realBondPrice 𝔼 β σ C' Z t s := by
  have hC : C = C' := funext fun t => funext fun s =>
    (levels_neutrality hD hα (hA t s) (hpos t s).1 (hpos t s).2.1 (hpos t s).2.2.1
      (hpos t s).2.2.2 (hpos' t s).1 (hpos' t s).2.1 (hpos' t s).2.2.1 (hpos' t s).2.2.2
      (h t s) (h' t s)).2.1
  rw [hC]

/-! ### Welfare, §2.4.4 -/

/-- Galí (2015), eq. (1), p. 18, and §2.4.4, p. 30: expected discounted utility up to date `T`
as of date 0, `E_0 ∑_{t<T} β^t U(e^{c_t}, e^{n_t}; e^{z_t})`, of a (log) allocation. -/
noncomputable def welfare (β σ φ : ℝ) (c n z : ℕ → Ω → ℝ) (T : ℕ) : Ω → ℝ :=
  𝔼.E 0 (fun s => ∑ t ∈ Finset.range T, β ^ t *
    Household.periodUtility σ φ (Real.exp (c t s)) (Real.exp (n t s)) (Real.exp (z t s)))

/-- Galí (2015), §2.4.4, p. 30 (**all policies are welfare-equivalent**): for `σ ≠ 0`, `D ≠ 0`,
two equilibria under any two monetary policies give the same expected discounted utility at
every horizon `T`. -/
theorem welfare_policy_invariant {σ φ α ρ ρz η β : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    (policy₁ policy₂ : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    {a z y c n ω r i infl m p y' c' n' ω' r' i' infl' m' p' : ℕ → Ω → ℝ}
    (h : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₁ a z y c n ω r i infl m p)
    (h' : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₂ a z y' c' n' ω' r' i' infl' m' p') (T : ℕ) :
    welfare 𝔼 β σ φ c n z T = welfare 𝔼 β σ φ c' n' z T := by
  obtain ⟨-, hc, hn, -, -⟩ := neutrality_across_policies 𝔼 hσ hD policy₁ policy₂ h h'
  rw [hc, hn]

/-- Galí (2015), §2.4.4, p. 30: no policy rule is better than any other. If expected
discounted utility converges (to `W` and `W'`) under two policies, then `W = W'`. -/
theorem welfare_limit_policy_invariant {σ φ α ρ ρz η β : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    (policy₁ policy₂ : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    {a z y c n ω r i infl m p y' c' n' ω' r' i' infl' m' p' : ℕ → Ω → ℝ}
    (h : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₁ a z y c n ω r i infl m p)
    (h' : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₂ a z y' c' n' ω' r' i' infl' m' p') {s : Ω}
    {W W' : ℝ} (hW : Tendsto (fun T => welfare 𝔼 β σ φ c n z T s) atTop (𝓝 W))
    (hW' : Tendsto (fun T => welfare 𝔼 β σ φ c' n' z T s) atTop (𝓝 W')) : W = W' := by
  have he : (fun T => welfare 𝔼 β σ φ c n z T s) = fun T => welfare 𝔼 β σ φ c' n' z T s :=
    funext fun T => by rw [welfare_policy_invariant 𝔼 hσ hD policy₁ policy₂ h h' T]
  rw [he] at hW
  exact tendsto_nhds_unique hW hW'

/-- Galí (2015), p. 24 (correction C2-2, **counterexample**): with a random-walk preference
shifter, `ρ_z = 1`, the equilibrium real rate does not respond to `z_t` at all:
`r_t = ρ − σ(1 − ρ_a)ψ_ya a_t`. -/
theorem realRate_no_z_response {σ φ α ρ ρa : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 σ φ α ρ 1 a z y c n ω r i infl)
    (ha : 𝔼.IsAR1 ρa a) (t : ℕ) : r t = (fun _ => ρ) + rateCoeffA σ φ α ρa • a t := by
  rw [equilibrium_realRate 𝔼 hσ hD h ha t, sub_self, zero_smul, add_zero]

/-- Galí (2015), pp. 23–24: conversely, the allocation of (18)–(21) together with any nominal
paths `i`, `π` that deliver the real rate `ρ + (1 − ρ_z) z_t + σ(E_t y_{t+1} − y_t)` is an
equilibrium (`σ ≠ 0`, `D ≠ 0`): monetary policy can choose nominal paths freely subject to
this one restriction. -/
theorem equilibrium_of_allocation {σ φ α ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y n ω r i infl : ℕ → Ω → ℝ}
    (hn : ∀ t s, n t s = psiNa σ φ α * a t s + psiN σ φ α)
    (hy : ∀ t s, y t s = psiYa σ φ α * a t s + psiY σ φ α)
    (hω : ∀ t s, ω t s = psiWa σ φ α * a t s + psiW σ φ α)
    (hr : ∀ t, r t = i t - 𝔼.E t (infl (t + 1)))
    (hi : ∀ t, i t - 𝔼.E t (infl (t + 1)) = (fun _ => ρ) + (1 - ρz) • z t
      + σ • (𝔼.E t (y (t + 1)) - y t)) :
    Equilibrium 𝔼 σ φ α ρ ρz a z y y n ω r i infl := by
  refine ⟨fun t s => (staticBlock_iff hD).2 ⟨hn t s, hy t s, rfl, hω t s⟩, fun t => ?_, hr⟩
  funext s
  have e := congrFun (hi t) s
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  field_simp
  linear_combination e

end Gali.ClassicalMonetaryModel.FirmsEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interest-rate rules and price-level determination in the classical model

Galí (2015), Chapter 2, §2.4.1–2.4.2, pp. 24–28. The real block of the classical
model (the natural real rate `r_t = ρ + r̂_t`, output `y_t`) is determined independently
of monetary policy (§2.3), so here it is taken as an exogenous bounded adapted process,
as the book does in §2.4. Every statement holds for an arbitrary `ExpectationSystem`, so
both under perfect foresight and under genuine uncertainty.

## Main results

* `Fisher`, `fisher_steadyState_iff`: the Fisherian equation (22), p. 24, and its
  steady state `i = ρ + π`, p. 25.
* §2.4.1, exogenous nominal rate `i_t = i + v_t`: `exo_equilibrium_iff` — an adapted
  inflation process is an equilibrium iff `π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` for a
  martingale-difference sunspot `ξ` (p. 26). `exo_two_equilibria` (any expectation
  system, in particular perfect foresight, where the free variable is initial
  inflation: `perfectForesight_exo_pinned`) and `coin_exo_sunspot` (a genuine sunspot at
  date 1 in the coin-flip tree) exhibit two distinct bounded equilibria.
* §2.4.2, the rule `i_t = ρ + π + φ_π(π_t − π) + v_t`: `rule_fisher_iff_eq24` gives (24);
  `eq25_unique_bounded`: for `φ_π > 1` the forward series (25) is the unique bounded
  equilibrium; `inflation_ar1_closed_form`, `inflation_closed_form_book`: the AR(1)
  closed form on p. 27; `hasDerivAt_inflImpact`, `hasDerivAt_rateImpact`,
  `hasDerivAt_moneyImpact`: the monetary-shock derivatives on p. 27;
  `liquidity_effect_iff`: a liquidity effect iff `η ρ_v > 1` (given `φ_π > ρ_v`).
* (26) and fn. 7, p. 28: `path26_eq24`, `path26_bounded`: for `|φ_π| < 1` every bounded
  martingale-difference `ξ` gives a bounded equilibrium; `eq24_iff_path26`: every adapted
  equilibrium is of that form; `path26_injective`: distinct sunspots give distinct
  equilibria; `isMDS_fn7`: the fn. 7 combinations are martingale differences.
* The Taylor principle, p. 28: `taylor_principle` — for `φ_π ≥ 0`, (24) is determinate
  iff `φ_π > 1`. This includes the case `φ_π = 1`, which the book omits: then the
  equilibrium is never unique (`not_unique_of_le_one`), and it may fail to exist
  (`phi_one_no_bounded_solution`).
* Correction C2-3: `c2_3_forward_converges_not_unique` — for AR(1) drivers with
  `|ρ| < φ_π < 1` the forward series (25) converges (to `(r̂_t − v_t)/(φ_π − ρ)`) and
  solves (24), but it is not the unique bounded solution; `printed_divergence_false`:
  the printed claim "(25) does not converge for `φ_π < 1`" is false for every `φ_π > 0`.
-/

namespace Gali.ClassicalMonetaryModel.InterestRules

open ExpectationsFiniteTree

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Preliminaries -/

/-- Galí (2015), §2.4, p. 24 (information): a random variable known at date `s` is known at
every later date `t ≥ s`. -/
theorem E_of_known {s t : ℕ} {x : Ω → ℝ} (h : 𝔼.E s x = x) (hst : s ≤ t) :
    𝔼.E t x = x := by
  rw [← h, 𝔼.known hst]

/-- Galí (2015), §2.4, p. 24 (information): an adapted process is known at all later dates. -/
theorem E_of_adapted_le {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E t (x s) = x s :=
  E_of_known 𝔼 (hx s) hst

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward series is adapted (it is a
date-`t` forecast). Proved here; the core module lacks it. -/
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
  rw [map_smul, 𝔼.E_E_self, Pi.smul_apply, smul_eq_mul]

/-- Galí (2015), p. 27 (impact derivatives): an affine map `e ↦ α + β e` has derivative `β`. -/
theorem hasDerivAt_affine (α β x : ℝ) : HasDerivAt (fun e => α + β * e) β x := by
  simpa using HasDerivAt.const_add α (HasDerivAt.const_mul β (hasDerivAt_id x))

/-! ### The Fisherian equation (22) -/

/-- Galí (2015), eq. (22), p. 24: the Fisherian equation `i_t = E_t{π_{t+1}} + r_t`. -/
def Fisher (i infl r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (infl (t + 1)) + r t

/-- Galí (2015), p. 25: in a steady state with `r = ρ`, constant `i` and `π` satisfy the
Fisherian equation (22) iff `i = ρ + π`. -/
theorem fisher_steadyState_iff [Nonempty Ω] (ibar πbar ρ : ℝ) :
    Fisher 𝔼 (fun _ _ => ibar) (fun _ _ => πbar) (fun _ _ => ρ) ↔ ibar = ρ + πbar := by
  constructor
  · intro h
    have := congrFun (h 0) (Classical.arbitrary Ω)
    simp only [𝔼.const, Pi.add_apply] at this
    linarith
  · intro h t
    funext ω
    simp only [𝔼.const, Pi.add_apply]
    linarith

/-- Galí (2015), p. 26: the real rate `r_t = ρ + r̂_t`, with `r̂_t` the deviation from the
steady-state value `ρ`. -/
def realRate (ρ : ℝ) (rhat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => ρ) + rhat t

/-! ### §2.4.1 An exogenous path for the nominal interest rate -/

/-- Galí (2015), p. 26: a martingale-difference (sunspot) process: adapted, with
`E_{t−1}{ξ_t} = 0` for all `t ≥ 1` (written `E_t{ξ_{t+1}} = 0`). -/
def IsMDS (ξ : ℕ → Ω → ℝ) : Prop := 𝔼.Adapted ξ ∧ ∀ t, 𝔼.E t (ξ (t + 1)) = 0

/-- Galí (2015), p. 26: the inflation path `π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` under the
exogenous rate `i_t = i + v_t`; at date 0 (no date −1) it is `π_0 = π + ξ_0`. -/
def exoPath (πbar : ℝ) (v rhat ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => (fun _ : Ω => πbar) + ξ 0
  | t + 1 => (fun _ : Ω => πbar) + v t - rhat t + ξ (t + 1)

/-- Galí (2015), p. 26: the sunspot implicit in an inflation process,
`ξ_0 = π_0 − π` and `ξ_{t+1} = π_{t+1} − E_t{π_{t+1}}`. -/
def innov (πbar : ℝ) (infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => infl 0 - fun _ : Ω => πbar
  | t + 1 => infl (t + 1) - 𝔼.E t (infl (t + 1))

/-- Galí (2015), p. 26: the sunspot implicit in an adapted inflation process is a
martingale difference. -/
theorem innov_isMDS {πbar : ℝ} {infl : ℕ → Ω → ℝ} (h : 𝔼.Adapted infl) :
    IsMDS 𝔼 (innov 𝔼 πbar infl) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => simp only [innov, map_sub, h 0, 𝔼.const]
    | succ t => simp only [innov, map_sub, h (t + 1), 𝔼.known (Nat.le_succ t)]
  · simp only [innov, map_sub, 𝔼.E_E_self, sub_self]

/-- Galí (2015), p. 26 (sufficiency): for every martingale-difference `ξ`, the path
`π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` satisfies the Fisherian equation (22) under the rule
`i_t = ρ + π + v_t`. -/
theorem exoPath_fisher {ρ πbar : ℝ} {v rhat ξ : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hr : 𝔼.Adapted rhat) (hξ : IsMDS 𝔼 ξ) :
    Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) (exoPath πbar v rhat ξ)
      (realRate ρ rhat) := by
  intro t
  simp only [exoPath, realRate, map_add, map_sub, 𝔼.const, hv t, hr t, hξ.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
  ring

/-- Galí (2015), §2.4.1, p. 26 (**indeterminacy**, necessity and sufficiency): under the
exogenous rate `i_t = i + v_t` with `i = ρ + π`, an adapted inflation process is an
equilibrium iff `π_t = π + v_{t−1} − r̂_{t−1} + ξ_t` for some martingale-difference `ξ`. -/
theorem exo_equilibrium_iff {ρ πbar : ℝ} {v rhat infl : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hr : 𝔼.Adapted rhat) (hinfl : 𝔼.Adapted infl) :
    Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) infl (realRate ρ rhat) ↔
      ∃ ξ, IsMDS 𝔼 ξ ∧ infl = exoPath πbar v rhat ξ := by
  constructor
  · intro hF
    refine ⟨innov 𝔼 πbar infl, innov_isMDS 𝔼 hinfl, ?_⟩
    funext t ω
    cases t with
    | zero => simp [exoPath, innov]
    | succ t =>
      have h := congrFun (hF t) ω
      simp only [realRate, Pi.add_apply] at h
      simp only [exoPath, innov, Pi.add_apply, Pi.sub_apply]
      linarith
  · rintro ⟨ξ, hξ, rfl⟩
    exact exoPath_fisher 𝔼 hv hr hξ

/-- Galí (2015), p. 26: the equivalent price-level form
`p_t = π + p_{t−1} + v_{t−1} − r̂_{t−1} + ξ_t`, given `p_t = p_{t−1} + π_t`. -/
theorem price_exoPath {πbar : ℝ} {v rhat ξ p : ℕ → Ω → ℝ}
    (hp : ∀ t, p (t + 1) = p t + exoPath πbar v rhat ξ (t + 1)) (t : ℕ) :
    p (t + 1) = (fun _ => πbar) + p t + v t - rhat t + ξ (t + 1) := by
  rw [hp t]
  funext ω
  simp only [exoPath, Pi.add_apply, Pi.sub_apply]
  ring

/-- Galí (2015), p. 26: the inflation path is bounded when `v`, `r̂` and `ξ` are. -/
theorem exoPath_bounded {πbar : ℝ} {v rhat ξ : ℕ → Ω → ℝ} (hv : BoundedProc v)
    (hr : BoundedProc rhat) (hξ : BoundedProc ξ) : BoundedProc (exoPath πbar v rhat ξ) := by
  obtain ⟨Mv, hMv⟩ := hv
  obtain ⟨Mr, hMr⟩ := hr
  obtain ⟨Mξ, hMξ⟩ := hξ
  refine ⟨|πbar| + Mv + Mr + Mξ, fun t ω => ?_⟩
  have hv0 : 0 ≤ Mv := (abs_nonneg _).trans (hMv 0 ω)
  have hr0 : 0 ≤ Mr := (abs_nonneg _).trans (hMr 0 ω)
  have hp1 := le_abs_self πbar
  have hp2 := neg_abs_le πbar
  cases t with
  | zero =>
    simp only [exoPath, Pi.add_apply]
    have h3 := abs_le.mp (hMξ 0 ω)
    rw [abs_le]
    constructor <;> linarith
  | succ t =>
    simp only [exoPath, Pi.add_apply, Pi.sub_apply]
    have h1 := abs_le.mp (hMv t ω)
    have h2 := abs_le.mp (hMr t ω)
    have h3 := abs_le.mp (hMξ (t + 1) ω)
    rw [abs_le]
    constructor <;> linarith

/-- Galí (2015), p. 26: the inflation path is adapted when `v`, `r̂` and `ξ` are. -/
theorem exoPath_adapted {πbar : ℝ} {v rhat ξ : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hr : 𝔼.Adapted rhat) (hξ : 𝔼.Adapted ξ) : 𝔼.Adapted (exoPath πbar v rhat ξ) := by
  intro t
  cases t with
  | zero => simp only [exoPath, map_add, 𝔼.const, hξ 0]
  | succ t =>
    simp only [exoPath, map_add, map_sub, 𝔼.const, hξ (t + 1),
      E_of_adapted_le 𝔼 hv (Nat.le_succ t), E_of_adapted_le 𝔼 hr (Nat.le_succ t)]

/-- Galí (2015), p. 26: the zero process is a martingale difference. -/
theorem zero_isMDS : IsMDS 𝔼 0 :=
  ⟨fun t => by simp, fun t => by simp⟩

/-- Galí (2015), p. 26: a deterministic sunspot that moves only date-0 inflation. -/
def dateZeroShock : ℕ → Ω → ℝ := fun t _ => if t = 0 then 1 else 0

/-- Galí (2015), p. 26: the date-0 sunspot is a martingale difference (under any
expectation system, including perfect foresight). -/
theorem dateZeroShock_isMDS : IsMDS 𝔼 dateZeroShock := by
  refine ⟨fun t => 𝔼.const t _, fun t => ?_⟩
  change 𝔼.E t (fun _ => if t + 1 = 0 then (1 : ℝ) else 0) = 0
  rw [𝔼.const]
  funext ω
  simp

/-- Galí (2015), p. 26: the date-0 sunspot is bounded. -/
theorem dateZeroShock_bounded : BoundedProc (dateZeroShock (Ω := Ω)) :=
  ⟨1, fun t ω => by unfold dateZeroShock; split_ifs <;> simp⟩

/-- Galí (2015), §2.4.1, p. 26 (**two distinct bounded equilibria**, any expectation system,
in particular perfect foresight): under an exogenous nominal rate there are two different
bounded adapted equilibrium inflation processes. -/
theorem exo_two_equilibria [Nonempty Ω] {ρ πbar : ℝ} {v rhat : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted v) (hr : 𝔼.Adapted rhat) (hvb : BoundedProc v) (hrb : BoundedProc rhat) :
    ∃ π₁ π₂ : ℕ → Ω → ℝ,
      Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) π₁ (realRate ρ rhat) ∧
      Fisher 𝔼 (fun t => (fun _ => ρ + πbar) + v t) π₂ (realRate ρ rhat) ∧
      BoundedProc π₁ ∧ BoundedProc π₂ ∧ 𝔼.Adapted π₁ ∧ 𝔼.Adapted π₂ ∧ π₁ ≠ π₂ := by
  refine ⟨exoPath πbar v rhat 0, exoPath πbar v rhat dateZeroShock,
    exoPath_fisher 𝔼 hv hr (zero_isMDS 𝔼), exoPath_fisher 𝔼 hv hr (dateZeroShock_isMDS 𝔼),
    exoPath_bounded hvb hrb ⟨0, fun t ω => by simp⟩,
    exoPath_bounded hvb hrb dateZeroShock_bounded,
    exoPath_adapted 𝔼 hv hr (zero_isMDS 𝔼).1,
    exoPath_adapted 𝔼 hv hr (dateZeroShock_isMDS 𝔼).1, fun h => ?_⟩
  have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
  simp [exoPath, dateZeroShock] at this

/-- Galí (2015), p. 26, under perfect foresight: a martingale difference vanishes from
date 1 on (there is no news to be surprised by). -/
theorem perfectForesight_isMDS {ξ : ℕ → Unit → ℝ} (h : IsMDS perfectForesight ξ) (t : ℕ) :
    ξ (t + 1) = 0 :=
  h.2 t

/-- Galí (2015), §2.4.1, p. 26, under perfect foresight: every equilibrium satisfies
`π_{t+1} = π + v_t − r̂_t`, so the only indeterminacy is initial inflation `π_0`
(equivalently the initial price level); `exo_two_equilibria` shows it is indeed free. -/
theorem perfectForesight_exo_pinned {ρ πbar : ℝ} {v rhat infl : ℕ → Unit → ℝ}
    (h : Fisher perfectForesight (fun t => (fun _ => ρ + πbar) + v t) infl (realRate ρ rhat))
    (t : ℕ) : infl (t + 1) = (fun _ => πbar) + v t - rhat t := by
  funext ω
  have := congrFun (h t) ω
  change ρ + πbar + v t ω = infl (t + 1) ω + (ρ + rhat t ω) at this
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

/-- Galí (2015), p. 26 (uncertainty example): the coin-flip innovation is a martingale
difference. -/
theorem coinShock_isMDS : IsMDS coinSystem coinShock := by
  refine ⟨fun t => ?_, coinShock_mean_zero⟩
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun _ h => coinShock_measurable t h

/-- Galí (2015), p. 26 (uncertainty example): the coin-flip innovation is bounded by 1. -/
theorem coinShock_bounded : BoundedProc coinShock :=
  ⟨1, fun t ω => by unfold coinShock; split_ifs <;> simp⟩

/-- Galí (2015), §2.4.1, p. 26 (**a genuine sunspot** in the coin-flip tree): under an
exogenous nominal rate, the fundamental path (`ξ = 0`) and the sunspot path (`ξ` = the coin
flip) are both bounded adapted equilibria; they agree at date 0 but differ at date 1 by a
coin flip unrelated to fundamentals. -/
theorem coin_exo_sunspot {ρ πbar : ℝ} {v rhat : ℕ → Bool × Bool → ℝ}
    (hv : coinSystem.Adapted v) (hr : coinSystem.Adapted rhat)
    (hvb : BoundedProc v) (hrb : BoundedProc rhat) :
    Fisher coinSystem (fun t => (fun _ => ρ + πbar) + v t) (exoPath πbar v rhat 0)
        (realRate ρ rhat) ∧
      Fisher coinSystem (fun t => (fun _ => ρ + πbar) + v t)
        (exoPath πbar v rhat coinShock) (realRate ρ rhat) ∧
      BoundedProc (exoPath πbar v rhat 0) ∧ BoundedProc (exoPath πbar v rhat coinShock) ∧
      coinSystem.Adapted (exoPath πbar v rhat 0) ∧
      coinSystem.Adapted (exoPath πbar v rhat coinShock) ∧
      exoPath πbar v rhat coinShock 0 = exoPath πbar v rhat 0 0 ∧
      exoPath πbar v rhat coinShock 1 (true, true) =
        exoPath πbar v rhat 0 1 (true, true) + 1 := by
  refine ⟨exoPath_fisher _ hv hr (zero_isMDS _), exoPath_fisher _ hv hr coinShock_isMDS,
    exoPath_bounded hvb hrb ⟨0, fun t ω => by simp⟩, exoPath_bounded hvb hrb coinShock_bounded,
    exoPath_adapted _ hv hr (zero_isMDS _).1, exoPath_adapted _ hv hr coinShock_isMDS.1,
    ?_, ?_⟩
  · funext ω
    simp [exoPath, coinShock]
  · simp [exoPath, coinShock]

/-! ### §2.4.2 A simple interest-rate rule -/

/-- Galí (2015), p. 26: the rule `i_t = ρ + π + φ_π(π_t − π) + v_t`. -/
def Rule (ρ πbar φ : ℝ) (i infl v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ + πbar) + φ • (infl t - fun _ => πbar) + v t

/-- Galí (2015), p. 27: the inflation gap `π̂_t = π_t − π`. -/
def gap (πbar : ℝ) (infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => infl t - fun _ => πbar

/-- Galí (2015), eq. (24), p. 27: `φ_π π̂_t = E_t{π̂_{t+1}} + r̂_t − v_t`. -/
def Eq24 (φ : ℝ) (z rhat v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φ • z t = 𝔼.E t (z (t + 1)) + rhat t - v t

/-- Galí (2015), eq. (24), p. 27: given the rule, the Fisherian equation (22) holds iff the
inflation gap satisfies (24). -/
theorem rule_fisher_iff_eq24 {ρ πbar φ : ℝ} {i infl v rhat : ℕ → Ω → ℝ}
    (hR : Rule ρ πbar φ i infl v) :
    Fisher 𝔼 i infl (realRate ρ rhat) ↔ Eq24 𝔼 φ (gap πbar infl) rhat v := by
  constructor
  · intro hF t
    funext ω
    have h1 := congrFun (hF t) ω
    have h2 := congrFun (hR t) ω
    simp only [gap, realRate, map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 ⊢
    linarith
  · intro hE t
    funext ω
    have h1 := congrFun (hE t) ω
    have h2 := congrFun (hR t) ω
    simp only [gap, realRate, map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 ⊢
    linarith

/-- Galí (2015), eq. (25), p. 27: the forward solution
`π̂_t = ∑_{k ≥ 0} φ_π^{−(k+1)} E_t{r̂_{t+k} − v_{t+k}}`. -/
noncomputable def fwd25 (φ : ℝ) (rhat v : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω

/-- Galí (2015), eq. (24), p. 27: the forcing `φ_π^{−1}(r̂_t − v_t)` of (24) written as
`π̂_t = φ_π^{−1} E_t{π̂_{t+1}} + φ_π^{−1}(r̂_t − v_t)`. -/
noncomputable def forcing25 (φ : ℝ) (rhat v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => φ⁻¹ • (rhat t - v t)

/-- Galí (2015), eq. (25), p. 27: (25) is the core forward series with `a = 1/φ_π`. -/
theorem fwd25_eq_forwardSeries (φ : ℝ) (rhat v : ℕ → Ω → ℝ) :
    fwd25 𝔼 φ rhat v = 𝔼.forwardSeries φ⁻¹ (forcing25 φ rhat v) := by
  funext t ω
  simp only [fwd25, ExpectationSystem.forwardSeries, forcing25, map_smul, Pi.smul_apply,
    smul_eq_mul]
  refine tsum_congr fun k => ?_
  ring

/-- Galí (2015), eq. (24), p. 27: for `φ_π ≠ 0`, (24) is the forward equation
`π̂_t = φ_π^{−1} E_t{π̂_{t+1}} + φ_π^{−1}(r̂_t − v_t)`. -/
theorem eq24_iff_forward {φ : ℝ} (hφ : φ ≠ 0) {z rhat v : ℕ → Ω → ℝ} :
    Eq24 𝔼 φ z rhat v ↔
      ∀ t, z t = φ⁻¹ • 𝔼.E t (z (t + 1)) + forcing25 φ rhat v t := by
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [forcing25, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [← mul_add, ← add_sub_assoc, ← h1, ← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [forcing25, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [h1, ← mul_add, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul, add_sub_assoc]

/-- Galí (2015), eq. (24), p. 27: the forcing is bounded when `r̂` and `v` are. -/
theorem forcing25_bound {φ M₁ M₂ : ℝ} (hφ : 0 < φ) {rhat v : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |rhat t ω| ≤ M₁) (hv : ∀ t ω, |v t ω| ≤ M₂) (t : ℕ) (ω : Ω) :
    |forcing25 φ rhat v t ω| ≤ φ⁻¹ * (M₁ + M₂) := by
  simp only [forcing25, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hφ)]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hr t ω) (hv t ω)))
    (inv_pos.mpr hφ).le

/-- Galí (2015), eq. (24), p. 27: the forcing is adapted when `r̂` and `v` are. -/
theorem forcing25_adapted {φ : ℝ} {rhat v : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) : 𝔼.Adapted (forcing25 φ rhat v) := by
  intro t
  simp only [forcing25, map_smul, map_sub, hr t, hv t]

/-- Galí (2015), eqs. (24)–(25), p. 27 (**determinacy for `φ_π > 1`**): with bounded adapted
`r̂` and `v`, the forward series (25) converges, is bounded and adapted, solves (24), and is
the unique bounded solution of (24). -/
theorem eq25_unique_bounded {φ : ℝ} (hφ : 1 < φ) {rhat v : ℕ → Ω → ℝ}
    (hrb : BoundedProc rhat) (hvb : BoundedProc v) (hra : 𝔼.Adapted rhat)
    (hva : 𝔼.Adapted v) :
    Eq24 𝔼 φ (fwd25 𝔼 φ rhat v) rhat v ∧ BoundedProc (fwd25 𝔼 φ rhat v) ∧
      𝔼.Adapted (fwd25 𝔼 φ rhat v) ∧
      ∀ z, Eq24 𝔼 φ z rhat v → BoundedProc z → z = fwd25 𝔼 φ rhat v := by
  obtain ⟨M₁, hM₁⟩ := hrb
  obtain ⟨M₂, hM₂⟩ := hvb
  have hφ0 : 0 < φ := one_pos.trans hφ
  have ha0 : 0 ≤ φ⁻¹ := (inv_pos.mpr hφ0).le
  have ha1 : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hφ
  have hu := forcing25_bound hφ0 hM₁ hM₂
  have hua := forcing25_adapted 𝔼 (φ := φ) hra hva
  rw [fwd25_eq_forwardSeries]
  refine ⟨(eq24_iff_forward 𝔼 hφ0.ne').mpr (𝔼.forwardSeries_solves ha0 ha1 hu hua),
    𝔼.forwardSeries_bounded ha0 ha1 hu, forwardSeries_adapted 𝔼 ha0 ha1 hu, fun z hz hzb => ?_⟩
  exact 𝔼.eq_forwardSeries ha0 ha1 hu hua ((eq24_iff_forward 𝔼 hφ0.ne').mp hz) hzb

/-- Galí (2015), p. 27 (AR(1) closed form): if `r̂_t = c_a a_t + c_z z_t` with `a`, `z`, `v`
bounded AR(1) processes with persistences `ρ_a, ρ_z, ρ_v ≤ 1 < φ_π`, the forward solution
(25) is `π̂_t = c_a/(φ_π − ρ_a) a_t + c_z/(φ_π − ρ_z) z_t − v_t/(φ_π − ρ_v)`. -/
theorem inflation_ar1_closed_form {φ ρa ρz ρv ca cz : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hvb : BoundedProc v) (hr : ∀ t, rhat t = ca • a t + cz • z t) :
    fwd25 𝔼 φ rhat v =
      fun t => (ca / (φ - ρa)) • a t + (cz / (φ - ρz)) • z t - (φ - ρv)⁻¹ • v t := by
  have hda : φ - ρa ≠ 0 := by linarith
  have hdz : φ - ρz ≠ 0 := by linarith
  have hdv : φ - ρv ≠ 0 := by linarith
  obtain ⟨Ma, hMa⟩ := hab
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Mv, hMv⟩ := hvb
  have hra : 𝔼.Adapted rhat := fun t => by
    rw [hr t, map_add, map_smul, map_smul, ha.1 t, hz.1 t]
  have hrb : BoundedProc rhat := by
    refine ⟨|ca| * Ma + |cz| * Mz, fun t ω => ?_⟩
    rw [hr t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMa t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  obtain ⟨-, -, -, huniq⟩ := eq25_unique_bounded 𝔼 hφ hrb ⟨Mv, hMv⟩ hra hv.1
  refine (huniq _ (fun t => ?_) ?_).symm
  · funext ω
    have h1 := congrFun (ha.2 t) ω
    have h2 := congrFun (hz.2 t) ω
    have h3 := congrFun (hv.2 t) ω
    have h4 := congrFun (hr t) ω
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4]
    field_simp
    ring
  · refine ⟨|ca / (φ - ρa)| * Ma + |cz / (φ - ρz)| * Mz + |(φ - ρv)⁻¹| * Mv,
      fun t ω => ?_⟩
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
      rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMa t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMv t ω) (abs_nonneg _)

/-- Galí (2015), (20) p. 23 and p. 27: a real rate `r̂_t = c_a a_t + c_z z_t` built from
bounded adapted drivers is bounded and adapted. -/
theorem combo_bounded_adapted {ca cz : ℝ} {a z rhat : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a)
    (hz : 𝔼.Adapted z) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hr : ∀ t, rhat t = ca • a t + cz • z t) : BoundedProc rhat ∧ 𝔼.Adapted rhat := by
  obtain ⟨Ma, hMa⟩ := hab
  obtain ⟨Mz, hMz⟩ := hzb
  refine ⟨⟨|ca| * Ma + |cz| * Mz, fun t ω => ?_⟩, fun t => ?_⟩
  · rw [hr t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMa t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  · rw [hr t, map_add, map_smul, map_smul, ha t, hz t]

/-- Galí (2015), p. 27 (closed form of every bounded equilibrium): if `r̂_t = c_a a_t + c_z z_t`
with bounded AR(1) drivers and `ρ_a, ρ_z, ρ_v ≤ 1 < φ_π`, every bounded solution of (24) has
`π_t = π + c_a/(φ_π − ρ_a) a_t + c_z/(φ_π − ρ_z) z_t − v_t/(φ_π − ρ_v)`. -/
theorem infl_closed_form {φ ρa ρz ρv ca cz πbar : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hvb : BoundedProc v) (hr : ∀ t, rhat t = ca • a t + cz • z t)
    (heq : Eq24 𝔼 φ (gap πbar infl) rhat v) (hb : BoundedProc (gap πbar infl)) (t : ℕ)
    (ω : Ω) :
    infl t ω = πbar + ca / (φ - ρa) * a t ω + cz / (φ - ρz) * z t ω - (φ - ρv)⁻¹ * v t ω := by
  have hc := inflation_ar1_closed_form 𝔼 hφ hρa hρz hρv ha hz hv hab hzb hvb hr
  obtain ⟨hrb, hra⟩ := combo_bounded_adapted 𝔼 ha.1 hz.1 hab hzb hr
  obtain ⟨-, -, -, huniq⟩ := eq25_unique_bounded 𝔼 hφ hrb hvb hra hv.1
  have h := congrFun (congrFun ((huniq _ heq hb).trans hc) t) ω
  simp only [gap, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  linarith

/-- Galí (2015), p. 27 (the printed closed form): with the real rate of (20),
`r̂_t = −σ(1 − ρ_a)ψ_ya a_t + (1 − ρ_z) z_t`, every bounded equilibrium of the rule has
`π_t = π − σ(1−ρ_a)ψ_ya/(φ_π−ρ_a) a_t + (1−ρ_z)/(φ_π−ρ_z) z_t − v_t/(φ_π−ρ_v)`. -/
theorem inflation_closed_form_book {φ ρa ρz ρv σ ψya πbar : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat infl : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hvb : BoundedProc v) (hr : ∀ t, rhat t = (-(σ * (1 - ρa) * ψya)) • a t + (1 - ρz) • z t)
    (heq : Eq24 𝔼 φ (gap πbar infl) rhat v) (hb : BoundedProc (gap πbar infl)) (t : ℕ)
    (ω : Ω) :
    infl t ω = πbar - σ * (1 - ρa) * ψya / (φ - ρa) * a t ω + (1 - ρz) / (φ - ρz) * z t ω -
      1 / (φ - ρv) * v t ω := by
  rw [infl_closed_form 𝔼 hφ hρa hρz hρv ha hz hv hab hzb hvb hr heq hb t ω]
  ring

/-! ### Responses to a monetary policy shock, p. 27 -/

/-- Galí (2015), p. 27: equilibrium inflation `π_t = A − v_t/(φ_π − ρ_v)` as a function of the
date-`t` policy innovation `ε^v_t`, with `v_t = ρ_v v_{t−1} + ε^v_t` and everything not
depending on `ε^v_t` collected in `A`. -/
noncomputable def inflImpact (φ ρv A vprev ε : ℝ) : ℝ := A - (ρv * vprev + ε) / (φ - ρv)

/-- Galí (2015), p. 27: the equilibrium nominal rate `i_t = B − ρ_v v_t/(φ_π − ρ_v)` as a
function of the innovation `ε^v_t`. -/
noncomputable def rateImpact (φ ρv B vprev ε : ℝ) : ℝ := B - ρv / (φ - ρv) * (ρv * vprev + ε)

/-- Galí (2015), p. 27 with (11): money `m_t = p_{t−1} + π_t + y_t − η i_t` as a function of
the innovation `ε^v_t` (`C = p_{t−1} + y_t` does not depend on it). -/
noncomputable def moneyImpact (η φ ρv C A B vprev ε : ℝ) : ℝ :=
  C + inflImpact φ ρv A vprev ε - η * rateImpact φ ρv B vprev ε

/-- Galí (2015), p. 27: with `φ_π > 1`, the equilibrium date-`t` inflation, nominal rate and
money supply (from (11), `m_t = p_t + y_t − η i_t`, and `p_t = p_{t−1} + π_t`) are the impact
maps evaluated at the innovation `ε^v_t = v_t − ρ_v v_{t−1}`; everything else (`a_t`, `z_t`,
`v_{t−1}`, `p_{t−1}`, `y_t`) enters only through `A`, `B`, `C`. -/
theorem impact_representation {ρ πbar η φ ρa ρz ρv ca cz : ℝ} (hφ : 1 < φ) (hρa : ρa ≤ 1)
    (hρz : ρz ≤ 1) (hρv : ρv ≤ 1) {a z v rhat infl i m p y : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hz : 𝔼.IsAR1 ρz z) (hv : 𝔼.IsAR1 ρv v) (hab : BoundedProc a)
    (hzb : BoundedProc z) (hvb : BoundedProc v) (hr : ∀ t, rhat t = ca • a t + cz • z t)
    (hR : Rule ρ πbar φ i infl v) (hF : Fisher 𝔼 i infl (realRate ρ rhat))
    (hb : BoundedProc (gap πbar infl)) (hm : ∀ t, m t = p t + y t - η • i t)
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (t : ℕ) (ω : Ω) :
    infl (t + 1) ω = inflImpact φ ρv
        (πbar + ca / (φ - ρa) * a (t + 1) ω + cz / (φ - ρz) * z (t + 1) ω) (v t ω)
        (v (t + 1) ω - ρv * v t ω) ∧
      i (t + 1) ω = rateImpact φ ρv
        (ρ + πbar + φ * (ca / (φ - ρa)) * a (t + 1) ω + φ * (cz / (φ - ρz)) * z (t + 1) ω)
        (v t ω) (v (t + 1) ω - ρv * v t ω) ∧
      m (t + 1) ω = moneyImpact η φ ρv (p t ω + y (t + 1) ω)
        (πbar + ca / (φ - ρa) * a (t + 1) ω + cz / (φ - ρz) * z (t + 1) ω)
        (ρ + πbar + φ * (ca / (φ - ρa)) * a (t + 1) ω + φ * (cz / (φ - ρz)) * z (t + 1) ω)
        (v t ω) (v (t + 1) ω - ρv * v t ω) := by
  have hdv : φ - ρv ≠ 0 := by linarith
  have heq := (rule_fisher_iff_eq24 𝔼 hR).mp hF
  have hc := infl_closed_form 𝔼 hφ hρa hρz hρv ha hz hv hab hzb hvb hr heq hb (t + 1) ω
  have hi := congrFun (hR (t + 1)) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  have hinfl : infl (t + 1) ω = inflImpact φ ρv
      (πbar + ca / (φ - ρa) * a (t + 1) ω + cz / (φ - ρz) * z (t + 1) ω) (v t ω)
      (v (t + 1) ω - ρv * v t ω) := by
    rw [hc]
    unfold inflImpact
    ring
  have hrate : i (t + 1) ω = rateImpact φ ρv
      (ρ + πbar + φ * (ca / (φ - ρa)) * a (t + 1) ω + φ * (cz / (φ - ρz)) * z (t + 1) ω)
      (v t ω) (v (t + 1) ω - ρv * v t ω) := by
    rw [hi, hc]
    unfold rateImpact
    field_simp
    ring
  refine ⟨hinfl, hrate, ?_⟩
  have hm1 := congrFun (hm (t + 1)) ω
  have hp1 := congrFun (hp t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hm1 hp1
  rw [hm1, hp1, hinfl, hrate]
  unfold moneyImpact
  ring

/-- Galí (2015), p. 27: `∂π_t/∂ε^v_t = −1/(φ_π − ρ_v)`. -/
theorem hasDerivAt_inflImpact (φ ρv A vprev ε : ℝ) :
    HasDerivAt (inflImpact φ ρv A vprev) (-1 / (φ - ρv)) ε := by
  have h : inflImpact φ ρv A vprev =
      fun e => inflImpact φ ρv A vprev 0 + -1 / (φ - ρv) * e := by
    funext e
    unfold inflImpact
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 27: `∂i_t/∂ε^v_t = −ρ_v/(φ_π − ρ_v)`. -/
theorem hasDerivAt_rateImpact (φ ρv B vprev ε : ℝ) :
    HasDerivAt (rateImpact φ ρv B vprev) (-ρv / (φ - ρv)) ε := by
  have h : rateImpact φ ρv B vprev =
      fun e => rateImpact φ ρv B vprev 0 + -ρv / (φ - ρv) * e := by
    funext e
    unfold rateImpact
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 27: `∂m_t/∂ε^v_t = (η ρ_v − 1)/(φ_π − ρ_v)`. -/
theorem hasDerivAt_moneyImpact (η φ ρv C A B vprev ε : ℝ) :
    HasDerivAt (moneyImpact η φ ρv C A B vprev) ((η * ρv - 1) / (φ - ρv)) ε := by
  have h : moneyImpact η φ ρv C A B vprev =
      fun e => moneyImpact η φ ρv C A B vprev 0 + (η * ρv - 1) / (φ - ρv) * e := by
    funext e
    unfold moneyImpact inflImpact rateImpact
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 27: a monetary tightening lowers inflation, `−1/(φ_π − ρ_v) < 0`, for
`φ_π > ρ_v`. -/
theorem inflation_falls {φ ρv : ℝ} (hφ : ρv < φ) : -1 / (φ - ρv) < 0 :=
  div_neg_of_neg_of_pos (by norm_num) (by linarith)

/-- Galí (2015), p. 27: the nominal rate falls after a tightening, `−ρ_v/(φ_π − ρ_v) < 0`,
iff the shock is persistent, `ρ_v > 0` (given `φ_π > ρ_v`). -/
theorem rate_falls_iff {φ ρv : ℝ} (hφ : ρv < φ) : -ρv / (φ - ρv) < 0 ↔ 0 < ρv := by
  have hd : 0 < φ - ρv := by linarith
  rw [div_neg_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hd⟩

/-- Galí (2015), p. 27 (**liquidity effect iff `η ρ_v > 1`**): for `η ≥ 0` and `φ_π > ρ_v`,
the nominal rate falls and the money supply rises after a policy shock
(`∂i_t/∂ε^v_t < 0 < ∂m_t/∂ε^v_t`) iff `η ρ_v > 1`. -/
theorem liquidity_effect_iff {η φ ρv : ℝ} (hη : 0 ≤ η) (hφ : ρv < φ) :
    (-ρv / (φ - ρv) < 0 ∧ 0 < (η * ρv - 1) / (φ - ρv)) ↔ 1 < η * ρv := by
  have hd : 0 < φ - ρv := by linarith
  rw [div_pos_iff_of_pos_right hd]
  constructor
  · rintro ⟨-, h⟩
    linarith
  · intro h
    refine ⟨(rate_falls_iff hφ).mpr ?_, by linarith⟩
    by_contra hρ
    push Not at hρ
    nlinarith

/-! ### (26): multiplicity for `φ_π < 1`, p. 28 -/

/-- Galí (2015), eq. (26), p. 28, in gaps: `π̂_0 = ξ_0`,
`π̂_{t+1} = φ_π π̂_t − r̂_t + v_t + ξ_{t+1}`. -/
def path26 (φ : ℝ) (rhat v ξ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => ξ 0
  | t + 1 => φ • path26 φ rhat v ξ t - rhat t + v t + ξ (t + 1)

/-- Galí (2015), p. 28: the surprise component of a process, `z_0` at date 0 and
`z_{t+1} − E_t{z_{t+1}}` afterwards. -/
def surprise (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => z 0
  | t + 1 => z (t + 1) - 𝔼.E t (z (t + 1))

/-- Galí (2015), p. 28: the surprise of an adapted process is a martingale difference. -/
theorem surprise_isMDS {z : ℕ → Ω → ℝ} (h : 𝔼.Adapted z) : IsMDS 𝔼 (surprise 𝔼 z) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => exact h 0
    | succ t => simp only [surprise, map_sub, h (t + 1), 𝔼.known (Nat.le_succ t)]
  · simp only [surprise, map_sub, 𝔼.E_E_self, sub_self]

/-- Galí (2015), eq. (26), p. 28: the path (26) is adapted. -/
theorem path26_adapted {φ : ℝ} {rhat v ξ : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hξ : 𝔼.Adapted ξ) : 𝔼.Adapted (path26 φ rhat v ξ) := by
  intro t
  induction t with
  | zero => exact hξ 0
  | succ t ih =>
    simp only [path26, map_add, map_sub, map_smul, hξ (t + 1), E_of_known 𝔼 ih (Nat.le_succ t),
      E_of_adapted_le 𝔼 hr (Nat.le_succ t), E_of_adapted_le 𝔼 hv (Nat.le_succ t)]

/-- Galí (2015), eq. (26), p. 28 (sufficiency, any `φ_π`): for every martingale-difference
`ξ`, the path (26) solves (24). -/
theorem path26_eq24 {φ : ℝ} {rhat v ξ : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat) (hv : 𝔼.Adapted v)
    (hξ : IsMDS 𝔼 ξ) : Eq24 𝔼 φ (path26 φ rhat v ξ) rhat v := by
  intro t
  have ha := path26_adapted 𝔼 (φ := φ) hr hv hξ.1 t
  simp only [path26, map_add, map_sub, map_smul, ha, hr t, hv t, hξ.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (26), p. 28 (boundedness): for `|φ_π| < 1` and bounded `r̂`, `v`, `ξ`,
the path (26) is bounded (by `max M_ξ (B/(1 − |φ_π|))`, `B = M_r + M_v + M_ξ`). -/
theorem path26_bounded {φ : ℝ} (hφ : |φ| < 1) {rhat v ξ : ℕ → Ω → ℝ}
    (hrb : BoundedProc rhat) (hvb : BoundedProc v) (hξb : BoundedProc ξ) :
    BoundedProc (path26 φ rhat v ξ) := by
  obtain ⟨Mr, hMr⟩ := hrb
  obtain ⟨Mv, hMv⟩ := hvb
  obtain ⟨Mξ, hMξ⟩ := hξb
  have hpos : 0 < 1 - |φ| := by linarith
  set K := max Mξ ((Mr + Mv + Mξ) / (1 - |φ|)) with hK
  have hBK : Mr + Mv + Mξ ≤ (1 - |φ|) * K := by
    calc Mr + Mv + Mξ = (1 - |φ|) * ((Mr + Mv + Mξ) / (1 - |φ|)) := by field_simp
      _ ≤ (1 - |φ|) * K := mul_le_mul_of_nonneg_left (le_max_right _ _) hpos.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (hMξ 0 ω).trans (le_max_left _ _)
  | succ t ih =>
    intro ω
    simp only [path26, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : |φ * path26 φ rhat v ξ t ω| ≤ |φ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have h1' := abs_le.mp h1
    have h2 := abs_le.mp (hMr t ω)
    have h3 := abs_le.mp (hMv t ω)
    have h4 := abs_le.mp (hMξ (t + 1) ω)
    rw [abs_le]
    constructor <;> nlinarith

/-- Galí (2015), p. 28: the surprise of the path (26) is the sunspot `ξ` itself. -/
theorem surprise_path26 {φ : ℝ} {rhat v ξ : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hξ : IsMDS 𝔼 ξ) : surprise 𝔼 (path26 φ rhat v ξ) = ξ := by
  funext t
  cases t with
  | zero => rfl
  | succ t =>
    have ha := path26_adapted 𝔼 (φ := φ) hr hv hξ.1 t
    simp only [surprise, path26, map_add, map_sub, map_smul, ha, hr t, hv t, hξ.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring

/-- Galí (2015), eq. (26), p. 28 (**necessity and sufficiency**, any `φ_π`): an adapted
process solves (24) iff it is the path (26) for some martingale-difference `ξ`. -/
theorem eq24_iff_path26 {φ : ℝ} {z rhat v : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hz : 𝔼.Adapted z) :
    Eq24 𝔼 φ z rhat v ↔ ∃ ξ, IsMDS 𝔼 ξ ∧ z = path26 φ rhat v ξ := by
  constructor
  · intro h
    refine ⟨surprise 𝔼 z, surprise_isMDS 𝔼 hz, ?_⟩
    funext t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext ω
      have h1 := congrFun (h t) ω
      have h2 := congrFun ih ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [path26, surprise, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← h2]
      linarith
  · rintro ⟨ξ, hξ, rfl⟩
    exact path26_eq24 𝔼 hr hv hξ

/-- Galí (2015), p. 28: distinct sunspots give distinct equilibria (26). -/
theorem path26_injective {φ : ℝ} {rhat v ξ ξ' : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rhat)
    (hv : 𝔼.Adapted v) (hξ : IsMDS 𝔼 ξ) (hξ' : IsMDS 𝔼 ξ')
    (h : path26 φ rhat v ξ = path26 φ rhat v ξ') : ξ = ξ' := by
  rw [← surprise_path26 𝔼 (φ := φ) hr hv hξ, ← surprise_path26 𝔼 (φ := φ) hr hv hξ', h]

/-- Galí (2015), eq. (26), p. 28, in levels: with `π_t = π + π̂_t`,
`π_{t+1} = (1 − φ_π)π + φ_π π_t − r̂_t + v_t + ξ_{t+1}`. -/
theorem eq26_levels {πbar φ : ℝ} {rhat v ξ infl : ℕ → Ω → ℝ}
    (h : ∀ s, infl s = (fun _ => πbar) + path26 φ rhat v ξ s) (t : ℕ) :
    infl (t + 1) = (fun _ => (1 - φ) * πbar) + φ • infl t - rhat t + v t + ξ (t + 1) := by
  rw [h (t + 1), h t]
  funext ω
  simp only [path26, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (26) and p. 28 (**multiplicity for `|φ_π| < 1`**): every bounded
martingale-difference `ξ` gives a bounded adapted solution of (24), and different sunspots
give different solutions. -/
theorem eq26_multiplicity {φ : ℝ} (hφ : |φ| < 1) {rhat v : ℕ → Ω → ℝ}
    (hr : 𝔼.Adapted rhat) (hv : 𝔼.Adapted v) (hrb : BoundedProc rhat) (hvb : BoundedProc v) :
    (∀ ξ, IsMDS 𝔼 ξ → BoundedProc ξ →
      Eq24 𝔼 φ (path26 φ rhat v ξ) rhat v ∧ BoundedProc (path26 φ rhat v ξ) ∧
        𝔼.Adapted (path26 φ rhat v ξ)) ∧
      ∀ ξ ξ', IsMDS 𝔼 ξ → IsMDS 𝔼 ξ' → ξ ≠ ξ' → path26 φ rhat v ξ ≠ path26 φ rhat v ξ' :=
  ⟨fun _ hξ hξb => ⟨path26_eq24 𝔼 hr hv hξ, path26_bounded hφ hrb hvb hξb,
      path26_adapted 𝔼 hr hv hξ.1⟩,
    fun _ _ hξ hξ' hne h => hne (path26_injective 𝔼 hr hv hξ hξ' h)⟩

/-- Galí (2015), fn. 7, p. 28: `ξ_t = τ_a ε^a_t + τ_z ε^z_t + τ_v ε^v_t + ξ*_t` is a
martingale difference for every choice of `τ_a, τ_z, τ_v` when the fundamental innovations
and the pure sunspot `ξ*` are. -/
theorem isMDS_fn7 {τa τz τv : ℝ} {εa εz εv ξs : ℕ → Ω → ℝ} (ha : IsMDS 𝔼 εa)
    (hz : IsMDS 𝔼 εz) (hv : IsMDS 𝔼 εv) (hs : IsMDS 𝔼 ξs) :
    IsMDS 𝔼 (fun t => τa • εa t + τz • εz t + τv • εv t + ξs t) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [map_add, map_smul, ha.1 t, hz.1 t, hv.1 t, hs.1 t]
  · simp only [map_add, map_smul, ha.2 t, hz.2 t, hv.2 t, hs.2 t, smul_zero, add_zero]

/-- Galí (2015), fn. 7, p. 28 (**indeterminate responses**): in the equilibrium (26) built on
the sunspot of fn. 7, the inflation surprise at `t + 1` is
`τ_a ε^a_{t+1} + τ_z ε^z_{t+1} + τ_v ε^v_{t+1} + ξ*_{t+1}`, so its response to each
fundamental shock is the arbitrary coefficient `τ`. -/
theorem fn7_surprise {φ τa τz τv : ℝ} {rhat v εa εz εv ξs : ℕ → Ω → ℝ}
    (hr : 𝔼.Adapted rhat) (hv : 𝔼.Adapted v) (ha : IsMDS 𝔼 εa)
    (hz : IsMDS 𝔼 εz) (hve : IsMDS 𝔼 εv) (hs : IsMDS 𝔼 ξs) (t : ℕ) :
    surprise 𝔼 (path26 φ rhat v (fun s => τa • εa s + τz • εz s + τv • εv s + ξs s)) (t + 1) =
      τa • εa (t + 1) + τz • εz (t + 1) + τv • εv (t + 1) + ξs (t + 1) := by
  rw [surprise_path26 𝔼 hr hv (isMDS_fn7 𝔼 ha hz hve hs)]

/-! ### The Taylor principle, p. 28, including `φ_π = 1` -/

/-- Galí (2015), p. 28: (24) is determinate when, for all bounded adapted `r̂`, `v`, it has
exactly one bounded adapted solution. -/
def Determinate24 (φ : ℝ) : Prop :=
  ∀ rhat v : ℕ → Ω → ℝ, BoundedProc rhat → BoundedProc v → 𝔼.Adapted rhat → 𝔼.Adapted v →
    ∃! z, Eq24 𝔼 φ z rhat v ∧ BoundedProc z ∧ 𝔼.Adapted z

/-- Galí (2015), p. 28: the deterministic self-fulfilling path `φ_π^t c` of the homogeneous
equation `φ_π d_t = E_t{d_{t+1}}`. -/
def homPath (φ c : ℝ) : ℕ → Ω → ℝ := fun t _ => φ ^ t * c

/-- Galí (2015), p. 28: the self-fulfilling path is deterministic, hence known at every date. -/
theorem E_homPath (φ c : ℝ) (t s : ℕ) : 𝔼.E t (homPath φ c s) = homPath φ c s :=
  𝔼.const t _

/-- Galí (2015), p. 28: adding `φ_π^t c` to a solution of (24) gives another solution. -/
theorem eq24_add_homPath {φ c : ℝ} {z rhat v : ℕ → Ω → ℝ} (hz : Eq24 𝔼 φ z rhat v) :
    Eq24 𝔼 φ (fun t => z t + homPath φ c t) rhat v := by
  intro t
  funext ω
  have h1 := congrFun (hz t) ω
  simp only [map_add, E_homPath, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at h1 ⊢
  simp only [homPath, pow_succ]
  linear_combination h1

/-- Galí (2015), p. 28 (**non-uniqueness for `0 ≤ φ_π ≤ 1`**, including `φ_π = 1`): next to
every bounded adapted solution of (24) there is a different one. -/
theorem not_unique_of_le_one [Nonempty Ω] {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1)
    {z rhat v : ℕ → Ω → ℝ} (hz : Eq24 𝔼 φ z rhat v) (hzb : BoundedProc z)
    (hza : 𝔼.Adapted z) :
    ∃ z', Eq24 𝔼 φ z' rhat v ∧ BoundedProc z' ∧ 𝔼.Adapted z' ∧ z' ≠ z := by
  obtain ⟨M, hM⟩ := hzb
  refine ⟨fun t => z t + homPath φ 1 t, eq24_add_homPath 𝔼 hz, ⟨M + 1, fun t ω => ?_⟩,
    fun t => ?_, fun h => ?_⟩
  · simp only [homPath, Pi.add_apply, mul_one]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_of_nonneg (pow_nonneg h0 t)]
    exact pow_le_one₀ h0 h1
  · simp only [map_add, hza t, E_homPath]
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp [homPath] at this

/-- Galí (2015), p. 28 (**the Taylor principle**, with the `φ_π = 1` case decided): for
`φ_π ≥ 0`, (24) is determinate iff `φ_π > 1`. -/
theorem taylor_principle [Nonempty Ω] {φ : ℝ} (hφ : 0 ≤ φ) : Determinate24 𝔼 φ ↔ 1 < φ := by
  constructor
  · intro hD
    by_contra hle
    push Not at hle
    obtain ⟨z, ⟨hz, hzb, hza⟩, huniq⟩ :=
      hD 0 0 ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩ (fun t => by simp)
        (fun t => by simp)
    obtain ⟨z', h1, h2, h3, hne⟩ := not_unique_of_le_one 𝔼 hφ hle hz hzb hza
    exact hne (huniq z' ⟨h1, h2, h3⟩)
  · intro h rhat v hrb hvb hra hva
    obtain ⟨hs, hb, ha, hu⟩ := eq25_unique_bounded 𝔼 h hrb hvb hra hva
    exact ⟨fwd25 𝔼 φ rhat v, ⟨hs, hb, ha⟩, fun z hz => hu z hz.1 hz.2.1⟩

/-- Galí (2015), p. 28, the case `φ_π = 1` omitted by the book (**existence can fail**): with
`r̂_t − v_t ≡ c ≠ 0`, (24) with `φ_π = 1` has no bounded solution at all, since
`π̂_0 = E_0{π̂_{k+1}} + (k + 1)c` for every `k`. -/
theorem phi_one_no_bounded_solution [Nonempty Ω] {c : ℝ} (hc : c ≠ 0) {z : ℕ → Ω → ℝ}
    (hz : Eq24 𝔼 1 z (fun _ _ => c) 0) : ¬ BoundedProc z := by
  rintro ⟨M, hM⟩
  have hstep : ∀ t ω, z t ω = 𝔼.E t (z (t + 1)) ω + c := fun t ω => by
    have := congrFun (hz t) ω
    simpa using this
  have hiter : ∀ k : ℕ, ∀ ω, z 0 ω = 𝔼.E 0 (z (k + 1)) ω + ((k : ℝ) + 1) * c := by
    intro k
    induction k with
    | zero => intro ω; simpa using hstep 0 ω
    | succ k ih =>
      intro ω
      have hzk : z (k + 1) = 𝔼.E (k + 1) (z (k + 1 + 1)) + fun _ => c := by
        funext ω'
        simp only [Pi.add_apply]
        exact hstep (k + 1) ω'
      rw [ih ω, hzk, map_add, 𝔼.tower (Nat.zero_le _), 𝔼.const]
      simp only [Pi.add_apply]
      push_cast
      ring
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M / |c|)
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have ω := Classical.arbitrary Ω
  have h1 := hiter k ω
  have h2 := abs_le.mp (hM 0 ω)
  have h3 := abs_le.mp (𝔼.abs_E_le (hM (k + 1)) 0 ω)
  have h4 : ((k : ℝ) + 1) * |c| ≤ 2 * M := by
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), ← abs_mul, abs_le]
    constructor <;> linarith
  have h5 : 2 * M < (k : ℝ) * |c| := by rwa [div_lt_iff₀ hcpos] at hk
  nlinarith

/-! ### Correction C2-3: the forward series can converge when `φ_π < 1` -/

/-- Galí (2015), (25) p. 27 and p. 28 (correction C2-3): for an AR(1) driver
`r̂_t − v_t` with persistence `|ρ| < φ_π`, the forward series (25) converges, with sum
`(r̂_t − v_t)/(φ_π − ρ)`, whether or not `φ_π > 1`. -/
theorem fwd25_ar1_hasSum {φ ρ : ℝ} (hφ : 0 < φ) (hρ : |ρ| < φ) {rhat v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ (fun t => rhat t - v t)) (t : ℕ) (ω : Ω) :
    HasSum (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω)
      ((rhat t ω - v t ω) / (φ - ρ)) := by
  have hq : |ρ / φ| < 1 := by
    rw [abs_div, abs_of_pos hφ, div_lt_one hφ]
    exact hρ
  have hd : φ - ρ ≠ 0 := by
    have := le_abs_self ρ
    linarith
  have hg := (hasSum_geometric_of_abs_lt_one hq).mul_left (φ⁻¹ * (rhat t ω - v t ω))
  have hf : (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω) =
      fun k => φ⁻¹ * (rhat t ω - v t ω) * (ρ / φ) ^ k := by
    funext k
    have h := congrFun (𝔼.ar1_iterate hu t k) ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
    rw [h, div_eq_mul_inv, mul_pow]
    ring
  rw [hf]
  convert hg using 1
  field_simp

/-- Galí (2015), p. 28: for an AR(1) driver, `(r̂_t − v_t)/(φ_π − ρ)` solves (24) for every
`φ_π ≠ ρ`. -/
theorem ar1_solution_eq24 {φ ρ : ℝ} (hd : φ - ρ ≠ 0) {rhat v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ (fun t => rhat t - v t)) :
    Eq24 𝔼 φ (fun t => (φ - ρ)⁻¹ • (rhat t - v t)) rhat v := by
  intro t
  have h2 : 𝔼.E t (rhat (t + 1) - v (t + 1)) = ρ • (rhat t - v t) := hu.2 t
  rw [map_smul, h2]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), p. 28 (**correction C2-3**): for `0 < φ_π ≤ 1` and a bounded AR(1) driver
`r̂_t − v_t` with `|ρ| < φ_π`, the forward series (25) converges, equals
`(r̂_t − v_t)/(φ_π − ρ)`, and is a bounded adapted solution of (24) — but it is not the
unique one: another bounded adapted solution exists. -/
theorem c2_3_forward_converges_not_unique [Nonempty Ω] {φ ρ : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hρ : |ρ| < φ) {rhat v : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ (fun t => rhat t - v t))
    (hub : BoundedProc (fun t => rhat t - v t)) :
    (∀ t ω, Summable (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω)) ∧
      fwd25 𝔼 φ rhat v = (fun t => (φ - ρ)⁻¹ • (rhat t - v t)) ∧
      Eq24 𝔼 φ (fwd25 𝔼 φ rhat v) rhat v ∧ BoundedProc (fwd25 𝔼 φ rhat v) ∧
      𝔼.Adapted (fwd25 𝔼 φ rhat v) ∧
      ∃ z, Eq24 𝔼 φ z rhat v ∧ BoundedProc z ∧ 𝔼.Adapted z ∧ z ≠ fwd25 𝔼 φ rhat v := by
  have hd0 : 0 < φ - ρ := by
    have := le_abs_self ρ
    linarith
  have hfeq : fwd25 𝔼 φ rhat v = (fun t => (φ - ρ)⁻¹ • (rhat t - v t)) := by
    funext t ω
    rw [fwd25, (fwd25_ar1_hasSum 𝔼 hφ hρ hu t ω).tsum_eq]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
  have hsol : Eq24 𝔼 φ (fwd25 𝔼 φ rhat v) rhat v := by
    rw [hfeq]
    exact ar1_solution_eq24 𝔼 hd0.ne' hu
  have hb : BoundedProc (fwd25 𝔼 φ rhat v) := by
    obtain ⟨M, hM⟩ := hub
    refine ⟨(φ - ρ)⁻¹ * M, fun t ω => ?_⟩
    rw [hfeq]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hd0)]
    exact mul_le_mul_of_nonneg_left (hM t ω) (inv_pos.mpr hd0).le
  have ha : 𝔼.Adapted (fwd25 𝔼 φ rhat v) := by
    intro t
    rw [hfeq]
    simp only [map_smul]
    rw [hu.1 t]
  obtain ⟨z, h1, h2, h3, h4⟩ := not_unique_of_le_one 𝔼 hφ.le hφ1 hsol hb ha
  exact ⟨fun t ω => (fwd25_ar1_hasSum 𝔼 hφ hρ hu t ω).summable, hfeq, hsol, hb, ha,
    z, h1, h2, h3, h4⟩

/-- Galí (2015), p. 28: the printed claim "if `φ_π < 1`, the forward solution (25) does not
converge", read as: for every bounded adapted `r̂`, `v` the series (25) diverges somewhere. -/
def PrintedDivergence (φ : ℝ) : Prop :=
  ∀ rhat v : ℕ → Ω → ℝ, BoundedProc rhat → BoundedProc v → 𝔼.Adapted rhat → 𝔼.Adapted v →
    ∃ t ω, ¬ Summable (fun k => φ⁻¹ ^ (k + 1) * 𝔼.E t (rhat (t + k) - v (t + k)) ω)

/-- Galí (2015), p. 28 (**the printed claim is false**, correction C2-3): in the coin-flip
tree, for every `φ_π > 0` (in particular every `φ_π ∈ (0, 1)`), the serially uncorrelated
real-rate shock `r̂_t = ε_t` (an AR(1) with `ρ = 0`) gives a convergent series (25). -/
theorem printed_divergence_false {φ : ℝ} (hφ : 0 < φ) :
    ¬ PrintedDivergence coinSystem φ := by
  intro h
  have hz : (fun t => coinShock t - (0 : ℕ → Bool × Bool → ℝ) t) = coinShock := by
    funext t ω
    simp
  have hu : coinSystem.IsAR1 0 (fun t => coinShock t - (0 : ℕ → Bool × Bool → ℝ) t) := by
    rw [hz]
    exact ⟨coinShock_isMDS.1, fun t => by rw [coinShock_mean_zero, zero_smul]⟩
  obtain ⟨t, ω, hns⟩ := h coinShock 0 coinShock_bounded ⟨0, fun t ω => by simp⟩
    coinShock_isMDS.1 (fun t => by simp)
  exact hns (fwd25_ar1_hasSum coinSystem hφ (by simpa using hφ) hu t ω).summable

end Gali.ClassicalMonetaryModel.InterestRules

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# An exogenous path for the money supply in the classical model

Galí (2015), Chapter 2, §2.4.3, pp. 28–30. The real block (the real rate `r_t` and output
`y_t`) is exogenous to monetary policy (§2.3) and is taken here as given bounded adapted
processes. The money supply `m_t` is set exogenously by the central bank. All statements
hold for an arbitrary `ExpectationSystem` (perfect foresight or genuine uncertainty).

## Main results

* `eq27_of_model`: money demand (11) with `c_t = y_t` (16) and the Fisherian equation (22)
  imply the price-level equation (27), `p_t = η/(1+η) E_t p_{t+1} + m_t/(1+η) + u_t`, for
  `η ≥ 0`; `fisher_of_eq27` is the converse for `η > 0`.
* `eq28_unique`: for bounded adapted `m`, `u` and `η ≥ 0`, the forward solution (28) is the
  unique bounded solution of (27): the price level is always determined.
* `eq29_unique`: with a (possibly non-stationary) money supply whose growth `Δm_t` is bounded,
  (29) `p_t = m_t + ∑_{k≥1} (η/(1+η))ᵏ E_t Δm_{t+k} + ū_t` is the unique solution of (27) with
  `p_t − m_t` bounded (fn. 8: via `p̃_t = p_t − m_t`, `eq27_iff_tilde`).
* `interest_rate_29`: the p. 29 interest-rate expression.
* AR(1) money growth, p. 30: `ar1_money_equilibrium` —
  `p_t = m_t + ηρ_m/(1+η(1−ρ_m)) Δm_t` and `i_t = ρ_m/(1+η(1−ρ_m)) Δm_t`;
  `ar1_series29` evaluates the series in (29); `hasDerivAt_priceImpactM` etc. give the
  impact responses; `price_overshoots_iff` (overshooting iff `η ρ_m > 0`) and
  `no_liquidity_effect_iff` (the nominal rate rises iff `ρ_m > 0`).
-/

namespace Gali.ClassicalMonetaryModel.MoneySupply

open InterestRules

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The price-level equation (27) -/

/-- Galí (2015), eq. (11), p. 22, with goods-market clearing `c_t = y_t` (16):
the money demand `m_t − p_t = y_t − η i_t`. -/
def MoneyDemand (η : ℝ) (m p y i : ℕ → Ω → ℝ) : Prop := ∀ t, m t - p t = y t - η • i t

/-- Galí (2015), p. 27: inflation is the change in the (log) price level,
`π_{t+1} = p_{t+1} − p_t`. -/
def InflationId (p infl : ℕ → Ω → ℝ) : Prop := ∀ t, infl (t + 1) = p (t + 1) - p t

/-- Galí (2015), p. 29: the forcing `u_t ≡ (1 + η)^{−1}(η r_t − y_t)` of (27). -/
noncomputable def uDef (η : ℝ) (r y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (1 + η)⁻¹ • (η • r t - y t)

/-- Galí (2015), eq. (27), p. 29: `p_t = η/(1+η) E_t{p_{t+1}} + (1+η)^{−1} m_t + u_t`. -/
def Eq27 (η : ℝ) (p m u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = (η / (1 + η)) • 𝔼.E t (p (t + 1)) + ((1 + η)⁻¹ • m t + u t)

/-- Galí (2015), eq. (27), p. 29 (derivation): for `η ≥ 0`, money demand (11) with (16), the
Fisherian equation (22) and `π_{t+1} = p_{t+1} − p_t` (adapted `p`) imply (27). -/
theorem eq27_of_model {η : ℝ} (hη : 0 ≤ η) {m p y i infl r : ℕ → Ω → ℝ}
    (hmd : MoneyDemand η m p y i) (hF : Fisher 𝔼 i infl r) (hid : InflationId p infl)
    (hp : 𝔼.Adapted p) : Eq27 𝔼 η p m (uDef η r y) := by
  intro t
  have hF' : i t = 𝔼.E t (p (t + 1)) - p t + r t := by rw [hF t, hid t, map_sub, hp t]
  funext ω
  have h1 := congrFun hF' ω
  have h2 := congrFun (hmd t) ω
  simp only [uDef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have hne : (1 + η) ≠ 0 := by linarith
  have key : (1 + η) * p t ω = η * 𝔼.E t (p (t + 1)) ω + m t ω + (η * r t ω - y t ω) := by
    linear_combination (-1 : ℝ) * h2 + η * h1
  have hpe : p t ω = (1 + η)⁻¹ * ((1 + η) * p t ω) := by field_simp
  rw [hpe, key]
  ring

/-- Galí (2015), eq. (27), p. 29 (converse): for `η > 0`, if the price level satisfies (27)
and the nominal rate clears the money market (11), the Fisherian equation (22) holds. -/
theorem fisher_of_eq27 {η : ℝ} (hη : 0 < η) {m p y i infl r : ℕ → Ω → ℝ}
    (h27 : Eq27 𝔼 η p m (uDef η r y)) (hmd : MoneyDemand η m p y i)
    (hid : InflationId p infl) (hp : 𝔼.Adapted p) : Fisher 𝔼 i infl r := by
  intro t
  rw [hid t, map_sub, hp t]
  funext ω
  have h1 := congrFun (h27 t) ω
  have h2 := congrFun (hmd t) ω
  simp only [uDef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have hne : (1 + η) ≠ 0 := by linarith
  have key : (1 + η) * p t ω = η * 𝔼.E t (p (t + 1)) ω + m t ω + (η * r t ω - y t ω) := by
    rw [h1]
    field_simp
    ring
  have h3 : η * i t ω = η * (𝔼.E t (p (t + 1)) ω - p t ω + r t ω) := by
    linear_combination h2 + key
  exact mul_left_cancel₀ hη.ne' h3

/-! ### The forward solution (28) -/

/-- Galí (2015), (28) p. 29: the forward series is additive, `∑ aᵏ E_t(c m_{t+k} + u_{t+k})
= c ∑ aᵏ E_t m_{t+k} + ∑ aᵏ E_t u_{t+k}`, for bounded `m`, `u` and `0 ≤ a < 1`. -/
theorem forwardSeries_smul_add {a c M₁ M₂ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {m u : ℕ → Ω → ℝ} (hm : ∀ t ω, |m t ω| ≤ M₁) (hu : ∀ t ω, |u t ω| ≤ M₂) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun s => c • m s + u s) t ω =
      c * 𝔼.forwardSeries a m t ω + 𝔼.forwardSeries a u t ω := by
  have h1 := (𝔼.forwardSeries_summable ha0 ha1 hm t ω).mul_left c
  have h2 := 𝔼.forwardSeries_summable ha0 ha1 hu t ω
  change ∑' k, a ^ k * 𝔼.E t (c • m (t + k) + u (t + k)) ω =
    c * ∑' k, a ^ k * 𝔼.E t (m (t + k)) ω + ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
  rw [← tsum_mul_left, ← h1.tsum_add h2]
  refine tsum_congr fun k => ?_
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (28), p. 29: `p_t = (1+η)^{−1} ∑_{k≥0} (η/(1+η))ᵏ E_t{m_{t+k}} + ū_t`,
`ū_t = ∑_{k≥0} (η/(1+η))ᵏ E_t{u_{t+k}}`. -/
noncomputable def fwd28 (η : ℝ) (m u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + η)⁻¹ * 𝔼.forwardSeries (η / (1 + η)) m t ω +
    𝔼.forwardSeries (η / (1 + η)) u t ω

/-- Galí (2015), eq. (27), p. 29: `0 ≤ η/(1+η) < 1` for `η ≥ 0`. -/
theorem coef_bounds {η : ℝ} (hη : 0 ≤ η) : 0 ≤ η / (1 + η) ∧ η / (1 + η) < 1 :=
  ⟨div_nonneg hη (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

/-- Galí (2015), eq. (28), p. 29 (**the price level is determined**): for `η ≥ 0` and bounded
adapted `m`, `u`, the forward solution (28) converges, is bounded and adapted, solves (27),
and is the unique bounded solution of (27). -/
theorem eq28_unique {η : ℝ} (hη : 0 ≤ η) {m u : ℕ → Ω → ℝ} (hmb : BoundedProc m)
    (hma : 𝔼.Adapted m) (hub : BoundedProc u) (hua : 𝔼.Adapted u) :
    Eq27 𝔼 η (fwd28 𝔼 η m u) m u ∧ BoundedProc (fwd28 𝔼 η m u) ∧
      𝔼.Adapted (fwd28 𝔼 η m u) ∧
      ∀ p, Eq27 𝔼 η p m u → BoundedProc p → p = fwd28 𝔼 η m u := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  obtain ⟨M₁, hM₁⟩ := hmb
  obtain ⟨M₂, hM₂⟩ := hub
  have hc : 0 < (1 + η)⁻¹ := inv_pos.mpr (by linarith)
  set w : ℕ → Ω → ℝ := fun s => (1 + η)⁻¹ • m s + u s with hw
  have hwb : ∀ t ω, |w t ω| ≤ (1 + η)⁻¹ * M₁ + M₂ := fun t ω => by
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hM₂ t ω))
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hM₁ t ω) hc.le
  have hwa : 𝔼.Adapted w := fun t => by
    simp only [hw, map_add, map_smul, hma t, hua t]
  have hfs : fwd28 𝔼 η m u = 𝔼.forwardSeries (η / (1 + η)) w := by
    funext t ω
    rw [hw, forwardSeries_smul_add 𝔼 ha0 ha1 hM₁ hM₂]
    rfl
  rw [hfs]
  exact ⟨𝔼.forwardSeries_solves ha0 ha1 hwb hwa, 𝔼.forwardSeries_bounded ha0 ha1 hwb,
    forwardSeries_adapted 𝔼 ha0 ha1 hwb,
    fun p hp hpb => 𝔼.eq_forwardSeries ha0 ha1 hwb hwa hp hpb⟩

/-! ### The money-growth representation (29) and fn. 8 -/

/-- Galí (2015), fn. 8, p. 29: the forcing `η/(1+η) E_t{Δm_{t+1}} + u_t` of the equation for
`p̃_t = p_t − m_t`. -/
noncomputable def w29 (η : ℝ) (dm u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (η / (1 + η)) • 𝔼.E t (dm (t + 1)) + u t

/-- Galí (2015), fn. 8, p. 29: with `m_{t+1} = m_t + Δm_{t+1}` (adapted `m`), (27) is
equivalent to `p̃_t = η/(1+η) E_t{p̃_{t+1}} + η/(1+η) E_t{Δm_{t+1}} + u_t`, `p̃ = p − m`. -/
theorem eq27_iff_tilde {η : ℝ} (hη : 0 ≤ η) {p m dm u : ℕ → Ω → ℝ}
    (hdm : ∀ t, m (t + 1) = m t + dm (t + 1)) (hma : 𝔼.Adapted m) :
    Eq27 𝔼 η p m u ↔
      ∀ t, p t - m t = (η / (1 + η)) • 𝔼.E t (p (t + 1) - m (t + 1)) + w29 𝔼 η dm u t := by
  have hne : (1 + η) ≠ 0 := by linarith
  have hid : (1 + η)⁻¹ = 1 - η / (1 + η) := by
    field_simp
    ring
  have hEm : ∀ t, 𝔼.E t (m (t + 1)) = m t + 𝔼.E t (dm (t + 1)) := fun t => by
    rw [hdm t, map_add, hma t]
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hEm t) ω
    simp only [w29, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [hid] at h1
    rw [h2]
    linear_combination h1
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hEm t) ω
    simp only [w29, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    rw [hid]
    linear_combination h1

/-- Galí (2015), eq. (29), p. 29:
`p_t = m_t + ∑_{k≥1} (η/(1+η))ᵏ E_t{Δm_{t+k}} + ū_t` (the sum written from `k + 1`). -/
noncomputable def fwd29 (η : ℝ) (m dm u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => m t ω + ∑' k, (η / (1 + η)) ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω +
    𝔼.forwardSeries (η / (1 + η)) u t ω

/-- Galí (2015), fn. 8, p. 29: (29) is `m_t` plus the forward solution of the `p̃` equation. -/
theorem fwd29_eq {η : ℝ} (hη : 0 ≤ η) {m dm u : ℕ → Ω → ℝ} (hdmb : BoundedProc dm)
    (hub : BoundedProc u) (t : ℕ) :
    fwd29 𝔼 η m dm u t = m t + 𝔼.forwardSeries (η / (1 + η)) (w29 𝔼 η dm u) t := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  obtain ⟨M₁, hM₁⟩ := hdmb
  obtain ⟨M₂, hM₂⟩ := hub
  funext ω
  set a := η / (1 + η) with ha
  have h1 : Summable (fun k => a ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω) := by
    refine ((𝔼.forwardSeries_summable ha0 ha1 (u := fun s => dm (s + 1))
      (fun s ω' => hM₁ (s + 1) ω') t ω).mul_left a).congr fun k => ?_
    ring
  have h2 := 𝔼.forwardSeries_summable ha0 ha1 hM₂ t ω
  simp only [fwd29, Pi.add_apply]
  rw [add_assoc]
  congr 1
  change _ = ∑' k, a ^ k * 𝔼.E t (w29 𝔼 η dm u (t + k)) ω
  change ∑' k, a ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω +
    ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
  rw [← h1.tsum_add h2]
  refine tsum_congr fun k => ?_
  simp only [w29, map_add, map_smul, 𝔼.tower (Nat.le_add_right t k), Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (29) and fn. 8, p. 29 (**existence and uniqueness with a non-stationary
money supply**): for `η ≥ 0`, adapted `m` with bounded growth `Δm` and bounded
adapted `u`, (29) solves (27), `p_t − m_t` is bounded, `p` is adapted, and (29) is the unique
solution of (27) with `p_t − m_t` bounded. -/
theorem eq29_unique {η : ℝ} (hη : 0 ≤ η) {m dm u : ℕ → Ω → ℝ}
    (hdm : ∀ t, m (t + 1) = m t + dm (t + 1)) (hma : 𝔼.Adapted m) (hdmb : BoundedProc dm)
    (hub : BoundedProc u) (hua : 𝔼.Adapted u) :
    Eq27 𝔼 η (fwd29 𝔼 η m dm u) m u ∧ BoundedProc (fun t => fwd29 𝔼 η m dm u t - m t) ∧
      𝔼.Adapted (fwd29 𝔼 η m dm u) ∧
      ∀ p, Eq27 𝔼 η p m u → BoundedProc (fun t => p t - m t) → p = fwd29 𝔼 η m dm u := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  have hfeq := fwd29_eq 𝔼 (m := m) hη hdmb hub
  obtain ⟨M₁, hM₁⟩ := hdmb
  obtain ⟨M₂, hM₂⟩ := hub
  set a := η / (1 + η) with ha
  have hwb : ∀ t ω, |w29 𝔼 η dm u t ω| ≤ M₁ + M₂ := fun t ω => by
    simp only [w29, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hM₂ t ω))
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |𝔼.E t (dm (t + 1)) ω| ≤ 1 * M₁ :=
          mul_le_mul ha1.le (𝔼.abs_E_le (hM₁ (t + 1)) t ω) (abs_nonneg _) zero_le_one
      _ = M₁ := one_mul _
  have hwa : 𝔼.Adapted (w29 𝔼 η dm u) := fun t => by
    simp only [w29, map_add, map_smul, 𝔼.E_E_self, hua t]
  have htil : (fun t => fwd29 𝔼 η m dm u t - m t) = 𝔼.forwardSeries a (w29 𝔼 η dm u) := by
    funext t
    rw [hfeq t, add_sub_cancel_left]
  refine ⟨(eq27_iff_tilde 𝔼 hη hdm hma).mpr fun t => ?_, ?_, fun t => ?_, fun p hp hpb => ?_⟩
  · have h := congrFun htil
    rw [h t, h (t + 1)]
    exact 𝔼.forwardSeries_solves ha0 ha1 hwb hwa t
  · rw [htil]
    exact 𝔼.forwardSeries_bounded ha0 ha1 hwb
  · rw [hfeq t, map_add, hma t, forwardSeries_adapted 𝔼 ha0 ha1 hwb t]
  · have hz := (eq27_iff_tilde 𝔼 hη hdm hma).mp hp
    have he := 𝔼.eq_forwardSeries (z := fun t => p t - m t) ha0 ha1 hwb hwa hz hpb
    funext t
    rw [hfeq t, ← congrFun he t, add_sub_cancel]

/-- Galí (2015), p. 29 (the nominal rate under a money rule): for `η > 0`, money demand (11)
gives `i_t = η^{−1}(y_t − (m_t − p_t))`, and with (29)
`i_t = η^{−1} ∑_{k≥1} (η/(1+η))ᵏ E_t{Δm_{t+k}} + u''_t`, `u''_t = η^{−1}(ū_t + y_t)`. -/
theorem interest_rate_29 {η : ℝ} (hη : 0 < η) {m dm u p y i : ℕ → Ω → ℝ}
    (hmd : MoneyDemand η m p y i) (hp : p = fwd29 𝔼 η m dm u) (t : ℕ) (ω : Ω) :
    i t ω = η⁻¹ * (y t ω - (m t ω - p t ω)) ∧
      i t ω = η⁻¹ * ∑' k, (η / (1 + η)) ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω +
        η⁻¹ * (𝔼.forwardSeries (η / (1 + η)) u t ω + y t ω) := by
  have h2 := congrFun (hmd t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
  have hi : i t ω = η⁻¹ * (y t ω - (m t ω - p t ω)) := by
    rw [h2]
    field_simp
    ring
  refine ⟨hi, ?_⟩
  rw [hi, hp]
  simp only [fwd29]
  ring

/-! ### AR(1) money growth, p. 30 -/

/-- Galí (2015), p. 30: for AR(1) money growth with persistence `ρ_m`, `|ρ_m| ≤ 1`, the series
in (29) sums to `ηρ_m/(1+η(1−ρ_m)) Δm_t`. -/
theorem ar1_series29 {η ρ : ℝ} (hη : 0 ≤ η) (hρ : |ρ| ≤ 1) {dm : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ dm) (t : ℕ) (ω : Ω) :
    HasSum (fun k => (η / (1 + η)) ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω)
      (η * ρ / (1 + η * (1 - ρ)) * dm t ω) := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  set a := η / (1 + η) with ha
  have hq : |a * ρ| < 1 := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |ρ| ≤ a * 1 := mul_le_mul_of_nonneg_left hρ ha0
      _ < 1 := by linarith
  have hg := (hasSum_geometric_of_abs_lt_one hq).mul_left (a * ρ * dm t ω)
  have hf : (fun k => a ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω) =
      fun k => a * ρ * dm t ω * (a * ρ) ^ k := by
    funext k
    have h := congrFun (𝔼.ar1_iterate hu t (k + 1)) ω
    rw [← add_assoc] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    ring
  rw [hf]
  have hne : (1 + η) ≠ 0 := by linarith
  have hne2 : 1 + η * (1 - ρ) ≠ 0 := by
    have := le_abs_self ρ
    nlinarith
  have hne3 : 1 + η - η * ρ ≠ 0 := fun h => hne2 (by linarith)
  convert hg using 1
  rw [ha]
  field_simp
  ring

/-- Galí (2015), p. 30 (**AR(1) money growth**): with no real shocks (`r_t = y_t = 0`),
`η ≥ 0` and money growth `Δm` a bounded AR(1) with `|ρ_m| ≤ 1`, in every equilibrium
(money demand (11), Fisher (22), adapted `p` with `p_t − m_t` bounded)
`p_t = m_t + ηρ_m/(1+η(1−ρ_m)) Δm_t` and `i_t = ρ_m/(1+η(1−ρ_m)) Δm_t`. -/
theorem ar1_money_equilibrium {η ρ : ℝ} (hη : 0 ≤ η) (hρ : |ρ| ≤ 1)
    {m dm p i infl : ℕ → Ω → ℝ} (hdm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hma : 𝔼.Adapted m) (hu : 𝔼.IsAR1 ρ dm) (hdmb : BoundedProc dm)
    (hmd : MoneyDemand η m p 0 i) (hF : Fisher 𝔼 i infl 0) (hid : InflationId p infl)
    (hp : 𝔼.Adapted p) (hpb : BoundedProc (fun t => p t - m t)) :
    (∀ t, p t = m t + (η * ρ / (1 + η * (1 - ρ))) • dm t) ∧
      ∀ t, i t = (ρ / (1 + η * (1 - ρ))) • dm t := by
  have hne : (1 + η) ≠ 0 := by linarith
  have hD : 0 < 1 + η * (1 - ρ) := by
    have := le_abs_self ρ
    nlinarith
  set c := η * ρ / (1 + η * (1 - ρ)) with hc
  have h0 : uDef η (0 : ℕ → Ω → ℝ) 0 = 0 := by
    funext t ω
    simp [uDef]
  have h27 : Eq27 𝔼 η p m 0 := by
    have := eq27_of_model 𝔼 hη hmd hF hid hp
    rwa [h0] at this
  obtain ⟨-, -, -, huniq⟩ := eq29_unique 𝔼 (u := 0) hη hdm hma hdmb ⟨0, fun t ω => by simp⟩
    (fun t => by simp)
  set q : ℕ → Ω → ℝ := fun t => m t + c • dm t with hq
  have hq27 : Eq27 𝔼 η q m 0 := by
    refine (eq27_iff_tilde 𝔼 hη hdm hma).mpr fun t => ?_
    funext ω
    have h1 := congrFun (hu.2 t) ω
    simp only [hq, w29, map_sub, map_add, map_smul, hdm t, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    rw [h1, hc]
    field_simp
    ring
  have hqb : BoundedProc (fun t => q t - m t) := by
    obtain ⟨M, hM⟩ := hdmb
    refine ⟨|c| * M, fun t ω => ?_⟩
    simp only [hq, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)
  have hpq : p = q := (huniq p h27 hpb).trans (huniq q hq27 hqb).symm
  refine ⟨fun t => by rw [hpq], fun t => ?_⟩
  rw [hF t, hid t, hpq]
  funext ω
  have h1 := congrFun (hu.2 t) ω
  have h2 := congrFun (hu.1 t) ω
  simp only [hq, hdm t, map_sub, map_add, map_smul, hma t, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
  rw [h1, h2, hc]
  field_simp
  ring

/-- Galí (2015), p. 30: the price level `p_t = m_t + ηρ_m/(1+η(1−ρ_m)) Δm_t` as a function of
the date-`t` money-growth innovation `ε^m_t`, with `Δm_t = ρ_m Δm_{t−1} + ε^m_t` and
`m_t = m_{t−1} + Δm_t`. -/
noncomputable def priceImpactM (η ρ mprev dmprev ε : ℝ) : ℝ :=
  mprev + (ρ * dmprev + ε) + η * ρ / (1 + η * (1 - ρ)) * (ρ * dmprev + ε)

/-- Galí (2015), p. 30: the money supply `m_t = m_{t−1} + Δm_t` as a function of `ε^m_t`. -/
def moneyImpactM (ρ mprev dmprev ε : ℝ) : ℝ := mprev + (ρ * dmprev + ε)

/-- Galí (2015), p. 30: the nominal rate `i_t = ρ_m/(1+η(1−ρ_m)) Δm_t` as a function of
`ε^m_t`. -/
noncomputable def rateImpactM (η ρ dmprev ε : ℝ) : ℝ :=
  ρ / (1 + η * (1 - ρ)) * (ρ * dmprev + ε)

/-- Galí (2015), p. 30: in the AR(1) equilibrium, the date-`t+1` price level, money supply and
nominal rate are the impact maps evaluated at `ε^m_{t+1} = Δm_{t+1} − ρ_m Δm_t`, everything
else (`m_t`, `Δm_t`) being predetermined. -/
theorem impact_representationM {η ρ : ℝ} {m dm p i : ℕ → Ω → ℝ}
    (hdm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hp : ∀ t, p t = m t + (η * ρ / (1 + η * (1 - ρ))) • dm t)
    (hi : ∀ t, i t = (ρ / (1 + η * (1 - ρ))) • dm t) (t : ℕ) (ω : Ω) :
    p (t + 1) ω = priceImpactM η ρ (m t ω) (dm t ω) (dm (t + 1) ω - ρ * dm t ω) ∧
      m (t + 1) ω = moneyImpactM ρ (m t ω) (dm t ω) (dm (t + 1) ω - ρ * dm t ω) ∧
      i (t + 1) ω = rateImpactM η ρ (dm t ω) (dm (t + 1) ω - ρ * dm t ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hp (t + 1), hdm t]
    simp only [priceImpactM, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hdm t]
    simp only [moneyImpactM, Pi.add_apply]
    ring
  · rw [hi (t + 1)]
    simp only [rateImpactM, Pi.smul_apply, smul_eq_mul]
    ring

/-- Galí (2015), p. 30: `∂p_t/∂ε^m_t = 1 + ηρ_m/(1+η(1−ρ_m))`. -/
theorem hasDerivAt_priceImpactM (η ρ mprev dmprev ε : ℝ) :
    HasDerivAt (priceImpactM η ρ mprev dmprev) (1 + η * ρ / (1 + η * (1 - ρ))) ε := by
  have h : priceImpactM η ρ mprev dmprev =
      fun e => priceImpactM η ρ mprev dmprev 0 + (1 + η * ρ / (1 + η * (1 - ρ))) * e := by
    funext e
    unfold priceImpactM
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 30: `∂m_t/∂ε^m_t = 1`. -/
theorem hasDerivAt_moneyImpactM (ρ mprev dmprev ε : ℝ) :
    HasDerivAt (moneyImpactM ρ mprev dmprev) 1 ε := by
  have h : moneyImpactM ρ mprev dmprev = fun e => moneyImpactM ρ mprev dmprev 0 + 1 * e := by
    funext e
    unfold moneyImpactM
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 30: `∂i_t/∂ε^m_t = ρ_m/(1+η(1−ρ_m))`. -/
theorem hasDerivAt_rateImpactM (η ρ dmprev ε : ℝ) :
    HasDerivAt (rateImpactM η ρ dmprev) (ρ / (1 + η * (1 - ρ))) ε := by
  have h : rateImpactM η ρ dmprev =
      fun e => rateImpactM η ρ dmprev 0 + ρ / (1 + η * (1 - ρ)) * e := by
    funext e
    unfold rateImpactM
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 30 (**price overshooting**): for `η ≥ 0` and `ρ_m ≤ 1`, the price level
responds more than one-for-one to a money-growth shock (`∂p_t/∂ε^m_t > 1 = ∂m_t/∂ε^m_t`)
iff `η ρ_m > 0`; in particular whenever `η > 0` and `ρ_m > 0`. -/
theorem price_overshoots_iff {η ρ : ℝ} (hη : 0 ≤ η) (hρ : ρ ≤ 1) :
    1 < 1 + η * ρ / (1 + η * (1 - ρ)) ↔ 0 < η * ρ := by
  have hD : 0 < 1 + η * (1 - ρ) := by nlinarith
  rw [lt_add_iff_pos_right, div_pos_iff_of_pos_right hD]

/-- Galí (2015), p. 30: overshooting in the empirically relevant case `η > 0`, `0 < ρ_m ≤ 1`. -/
theorem price_overshoots {η ρ : ℝ} (hη : 0 < η) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1) :
    1 < 1 + η * ρ / (1 + η * (1 - ρ)) :=
  (price_overshoots_iff hη.le hρ).mpr (mul_pos hη hρ0)

/-- Galí (2015), p. 30 (**no liquidity effect**): for `η ≥ 0` and `ρ_m ≤ 1`, the nominal rate
rises after a money-growth expansion (`∂i_t/∂ε^m_t > 0`) iff `ρ_m > 0`. -/
theorem no_liquidity_effect_iff {η ρ : ℝ} (hη : 0 ≤ η) (hρ : ρ ≤ 1) :
    0 < ρ / (1 + η * (1 - ρ)) ↔ 0 < ρ := by
  have hD : 0 < 1 + η * (1 - ρ) := by nlinarith
  exact div_pos_iff_of_pos_right hD

end Gali.ClassicalMonetaryModel.MoneySupply

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money in the utility function: the separable example

Galí (2015), Chapter 2, §2.5 and §2.5.1 (pp. 31–34).

Real balances `M_t/P_t` enter period utility (eq. (30)) and the flow budget constraint
becomes (31).

* `budget_rewrite`: eq. (32), the budget constraint in terms of total financial wealth
  `A_t = B_t + M_t`; the services of money cost `1 − Q_t = 1 − e^{−i_t}`
  (`price_of_money_services`, `one_sub_exp_neg_le`, `mul_exp_neg_le_one_sub_exp_neg`:
  `i e^{−i} ≤ 1 − e^{−i} ≤ i`, the book's `1 − e^{−i} ≃ i`).
* `miu_foc_necessary`: eq. (33) for a **general** differentiable utility of
  `(C, M/P)`: if the perturbation `P dC + (1 − Q) dM = 0` (p. 33) cannot raise utility,
  then `U_m = (1 − Q) U_c`.
* For the separable utility of p. 33 (`sepUtil`), `miu_static_optimum_iff`: the plan is
  optimal against every feasible perturbation **iff** `U_m / U_c = 1 − Q`
  (necessity by the first-order condition, sufficiency by concavity);
  `miu_static_optimum_iff_exp` is the same with `Q = e^{−i}`. Separability
  (`hasDerivAt_sepUtil_C`, `hasDerivAt_sepUtil_N`): `U_c` and `U_n` do not depend on real
  balances, so (7)–(10) are unchanged (p. 33).
* `money_demand_iff`: eq. (34), `M/P = C^{σ/ν} (1 − e^{−i})^{−1/ν}`, valid for `i > 0`;
  `no_money_demand_of_nonpos`: for `i ≤ 0` the optimality condition has no solution.
* `hasFDerivAt_logMoneyDemand`: eq. (35) as an **exact derivative**: the log money demand
  `(c, i) ↦ (σ/ν) c − ν⁻¹ log(1 − e^{−i})` has total derivative `(σ/ν, −η)` with
  `η = 1/(ν(e^i − 1))`; `eta_le`, `exp_neg_div_le_eta`: `e^{−i}/(νi) ≤ η ≤ 1/(νi)`, the
  book's `η ≃ 1/(νi)`.
* `hasFDerivAt_logMoneyDemand_unit`, `money_demand_unit_elastic`: eq. (36), the case
  `ν = σ`.

The utility functions and their concavity lemmas are restated from the Chapter 3 project
(`Household.lean`).
-/

namespace Gali.ClassicalMonetaryModel.MIUSeparable

open Filter Topology

/-! ### The budget constraint -/

/-- Galí (2015), eq. (32), p. 32 (**exact**): with total financial wealth `A_t = B_t + M_t`
and `A_{t−1} = B_{t−1} + M_{t−1}`, the flow budget constraint (31)
`P C + Q B + M ≤ B_{−1} + M_{−1} + W N + D` is equivalent to
`P C + Q A + (1 − Q) M ≤ A_{−1} + W N + D`. -/
theorem budget_rewrite (P C Q B M Bm Mm W N D : ℝ) :
    P * C + Q * B + M ≤ Bm + Mm + W * N + D ↔
      P * C + Q * (B + M) + (1 - Q) * M ≤ (Bm + Mm) + W * N + D := by
  have h : P * C + Q * (B + M) + (1 - Q) * M = P * C + Q * B + M := by ring
  rw [h]

/-- Galí (2015), p. 32: with `i = −log Q` the bond price is `Q = e^{−i}`, so the price of the
services of money is `1 − Q = 1 − e^{−i}`. -/
theorem price_of_money_services {Q : ℝ} (hQ : 0 < Q) : 1 - Q = 1 - Real.exp (-(-Real.log Q)) := by
  rw [neg_neg, Real.exp_log hQ]

/-- Galí (2015), p. 32 (`1 − e^{−i} ≃ i`, upper bound): `1 − e^{−i} ≤ i` for every `i`. -/
theorem one_sub_exp_neg_le (i : ℝ) : 1 - Real.exp (-i) ≤ i := by
  linarith [Real.add_one_le_exp (-i)]

/-- Galí (2015), p. 32 (`1 − e^{−i} ≃ i`, lower bound): `i e^{−i} ≤ 1 − e^{−i}`. -/
theorem mul_exp_neg_le_one_sub_exp_neg (i : ℝ) : i * Real.exp (-i) ≤ 1 - Real.exp (-i) := by
  have h1 := Real.add_one_le_exp i
  have h2 : Real.exp i * Real.exp (-i) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-i)]

/-! ### Eq. (33) for a general utility function -/

/-- Galí (2015), eq. (33), pp. 32–33 (**necessity, general utility**): let `U(C, M/P)` be
differentiable at the plan with derivative `L` (so `U_c = L (1, 0)`, `U_m = L (0, 1)`). If no
small perturbation `(dC, dM) = (−(1 − Q) δ / P, δ)`, which satisfies
`P dC + (1 − Q) dM = 0` and leaves all other variables unchanged, raises utility, then
`U_m = (1 − Q) U_c`. -/
theorem miu_foc_necessary {U : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {P Q C M : ℝ} (hP : P ≠ 0)
    (hU : HasFDerivAt U L (C, M / P))
    (hloc : IsLocalMax (fun δ : ℝ => U (C - (1 - Q) * δ / P, (M + δ) / P)) 0) :
    L (0, 1) = (1 - Q) * L (1, 0) := by
  have hc1 : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa using this
  have hc2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add M).div_const P
    simpa using this
  have hcomp := hU.comp_hasDerivAt_of_eq 0 (hc1.prodMk hc2) (by simp)
  have h0 := hloc.hasDerivAt_eq_zero hcomp
  have hv : ((-((1 - Q) / P), 1 / P) : ℝ × ℝ)
      = (-((1 - Q) / P)) • ((1 : ℝ), (0 : ℝ)) + (1 / P) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h0
  field_simp at h0
  linarith

/-! ### The separable utility of §2.5.1 -/

/-- Galí (2015), p. 33: the isoelastic utility `(x^{1−σ} − 1)/(1 − σ)`, with the log case
`σ = 1` (restated from the Chapter 3 project). -/
noncomputable def utilPow (σ x : ℝ) : ℝ :=
  if σ = 1 then Real.log x else (x ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 33: marginal utility `x^{−σ}` of `utilPow` (restated from the Chapter 3
project). -/
theorem hasDerivAt_utilPow (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (utilPow σ) (x ^ (-σ)) x := by
  by_cases hσ : σ = 1
  · have hfun : utilPow σ = Real.log := funext fun y => by simp [utilPow, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hx.ne'
  · have hfun : utilPow σ = fun y => (y ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun y => by simp [utilPow, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (restated from the Chapter 3 project; Galí (2015), p. 32, concavity). -/
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

/-- Galí (2015), p. 32 (utility concave in each argument): `utilPow σ` lies below its tangent
lines on `(0, ∞)` for `σ > 0` (restated from the Chapter 3 project). -/
theorem utilPow_le_tangent {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    utilPow σ y ≤ utilPow σ x + x ^ (-σ) * (y - x) := by
  refine le_tangent (f' := fun z => z ^ (-σ)) hx hy.le ?_ (fun z hz => hasDerivAt_utilPow σ hz)
    (fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith))
  intro z hz
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hasDerivAt_utilPow σ hz0).continuousAt.continuousWithinAt

/-- Galí (2015), p. 33: the separable period utility
`U(C, M/P, N; Z) = ((C^{1−σ} − 1)/(1 − σ) + ((M/P)^{1−ν} − 1)/(1 − ν) − N^{1+φ}/(1+φ)) Z`
(log branches for `σ = 1`, `ν = 1`), with `m = M/P` real balances. -/
noncomputable def sepUtil (σ ν φ Z C m N : ℝ) : ℝ :=
  (utilPow σ C + utilPow ν m - N ^ (1 + φ) / (1 + φ)) * Z

/-- Galí (2015), p. 33 (separability): `U_c = C^{−σ} Z` does not depend on real balances `m`
or on hours, so eqs. (7), (8) and their log forms (9), (10) are unchanged. -/
theorem hasDerivAt_sepUtil_C (σ ν φ Z m N : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun C' => sepUtil σ ν φ Z C' m N) (C ^ (-σ) * Z) C := by
  have := (((hasDerivAt_utilPow σ hC).add_const (utilPow ν m)).sub_const
    (N ^ (1 + φ) / (1 + φ))).mul_const Z
  exact this

/-- Galí (2015), p. 33 (separability): `U_n = −N^φ Z` does not depend on real balances. -/
theorem hasDerivAt_sepUtil_N (σ ν Z C m : ℝ) {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' => sepUtil σ ν φ Z C m N') (-(N ^ φ) * Z) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have hd : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have := (hd.const_sub (utilPow σ C + utilPow ν m)).mul_const Z
  simpa [sepUtil, sub_eq_add_neg] using this

/-- Galí (2015), p. 33: derivative at `δ = 0` of utility along the money perturbation
`(dC, dM) = (−(1 − Q) δ / P, δ)`: `(−C^{−σ}(1 − Q)/P + (M/P)^{−ν}/P) Z`. -/
theorem hasDerivAt_perturbation (σ ν φ Z N : ℝ) {P Q C M : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hM : 0 < M) :
    HasDerivAt (fun δ => sepUtil σ ν φ Z (C - (1 - Q) * δ / P) ((M + δ) / P) N)
      ((C ^ (-σ) * (-((1 - Q) / P)) + (M / P) ^ (-ν) * (1 / P)) * Z) 0 := by
  have hc1 : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa using this
  have hc2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add M).div_const P
    simpa using this
  have hu1 : HasDerivAt (utilPow σ) (C ^ (-σ)) (C - (1 - Q) * 0 / P) := by
    simpa using hasDerivAt_utilPow σ hC
  have hu2 : HasDerivAt (utilPow ν) ((M / P) ^ (-ν)) ((M + 0) / P) := by
    simpa using hasDerivAt_utilPow ν (div_pos hM hP)
  have := (((hu1.comp 0 hc1).add (hu2.comp 0 hc2)).sub_const
    (N ^ (1 + φ) / (1 + φ))).mul_const Z
  exact this

/-- Galí (2015), eq. (33), pp. 32–33, separable utility (**necessary and sufficient**): for
`σ, ν > 0`, `Z, P > 0`, `C, M > 0`, the plan `(C, M)` cannot be improved by any feasible
perturbation `(dC, dM) = (−(1 − Q) δ / P, δ)` (positive consumption and money) **iff**
`U_m = (1 − Q) U_c`, i.e. `(M/P)^{−ν} = (1 − Q) C^{−σ}`. -/
theorem miu_static_optimum_iff {σ ν φ Z P Q C M N : ℝ} (hσ : 0 < σ) (hν : 0 < ν) (hZ : 0 < Z)
    (hP : 0 < P) (hC : 0 < C) (hM : 0 < M) :
    (∀ δ, 0 < C - (1 - Q) * δ / P → 0 < (M + δ) / P →
      sepUtil σ ν φ Z (C - (1 - Q) * δ / P) ((M + δ) / P) N ≤ sepUtil σ ν φ Z C (M / P) N) ↔
      (M / P) ^ (-ν) = (1 - Q) * C ^ (-σ) := by
  constructor
  · intro hopt
    have hloc : IsLocalMax (fun δ => sepUtil σ ν φ Z (C - (1 - Q) * δ / P) ((M + δ) / P) N) 0 := by
      have hc1 : Continuous fun δ : ℝ => C - (1 - Q) * δ / P := by fun_prop
      have hc2 : Continuous fun δ : ℝ => (M + δ) / P := by fun_prop
      have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - (1 - Q) * δ / P :=
        (hc1.tendsto 0).eventually_const_lt (by simpa using hC)
      have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < (M + δ) / P :=
        (hc2.tendsto 0).eventually_const_lt (by simpa using div_pos hM hP)
      filter_upwards [e1, e2] with δ h1 h2
      simpa using hopt δ h1 h2
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_perturbation σ ν φ Z N hP hC hM)
    have h1 := (mul_eq_zero.1 h0).resolve_right hZ.ne'
    field_simp at h1
    linarith
  · intro hfoc δ h1 h2
    have t1 := utilPow_le_tangent hσ hC h1
    have t2 := utilPow_le_tangent hν (div_pos hM hP) h2
    unfold sepUtil
    apply mul_le_mul_of_nonneg_right _ hZ.le
    have e : C ^ (-σ) * (C - (1 - Q) * δ / P - C) + (M / P) ^ (-ν) * ((M + δ) / P - M / P)
        = 0 := by rw [hfoc]; ring
    linarith

/-- Galí (2015), eq. (33), p. 32, ratio form: `U_m = (1 − Q) U_c` iff `U_m / U_c = 1 − Q`
(`U_c = C^{−σ} > 0`). -/
theorem foc_iff_ratio {σ ν Q C m : ℝ} (hC : 0 < C) :
    m ^ (-ν) = (1 - Q) * C ^ (-σ) ↔ m ^ (-ν) / C ^ (-σ) = 1 - Q := by
  rw [div_eq_iff (Real.rpow_pos_of_pos hC _).ne']

/-- Galí (2015), eq. (33), pp. 32–33, with `Q = e^{−i}` (**necessary and sufficient**):
the plan is optimal against all feasible money perturbations iff
`U_m / U_c = 1 − e^{−i}`. -/
theorem miu_static_optimum_iff_exp {σ ν φ Z P i C M N : ℝ} (hσ : 0 < σ) (hν : 0 < ν)
    (hZ : 0 < Z) (hP : 0 < P) (hC : 0 < C) (hM : 0 < M) :
    (∀ δ, 0 < C - (1 - Real.exp (-i)) * δ / P → 0 < (M + δ) / P →
      sepUtil σ ν φ Z (C - (1 - Real.exp (-i)) * δ / P) ((M + δ) / P) N
        ≤ sepUtil σ ν φ Z C (M / P) N) ↔
      (M / P) ^ (-ν) / C ^ (-σ) = 1 - Real.exp (-i) := by
  rw [miu_static_optimum_iff hσ hν hZ hP hC hM, foc_iff_ratio hC]

/-! ### Eq. (34): money demand -/

/-- Galí (2015), eq. (34), p. 34 (**exact**): for `i > 0`, `ν > 0` and positive `C`, `m`, the
optimality condition `m^{−ν} = (1 − e^{−i}) C^{−σ}` is equivalent to the money demand
`m = C^{σ/ν} (1 − e^{−i})^{−1/ν}`. -/
theorem money_demand_iff {σ ν i C m : ℝ} (hν : 0 < ν) (hi : 0 < i) (hC : 0 < C) (hm : 0 < m) :
    m ^ (-ν) = (1 - Real.exp (-i)) * C ^ (-σ) ↔
      m = C ^ (σ / ν) * (1 - Real.exp (-i)) ^ (-1 / ν) := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hp1 : 0 < m ^ (-ν) := Real.rpow_pos_of_pos hm _
  have hp2 : 0 < (1 - Real.exp (-i)) * C ^ (-σ) := mul_pos hk (Real.rpow_pos_of_pos hC _)
  have hp3 : 0 < C ^ (σ / ν) * (1 - Real.exp (-i)) ^ (-1 / ν) :=
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hk _)
  rw [← Real.log_injOn_pos.eq_iff hp1 hp2, ← Real.log_injOn_pos.eq_iff hm hp3,
    Real.log_rpow hm, Real.log_mul hk.ne' (Real.rpow_pos_of_pos hC _).ne', Real.log_rpow hC,
    Real.log_mul (Real.rpow_pos_of_pos hC _).ne' (Real.rpow_pos_of_pos hk _).ne',
    Real.log_rpow hC, Real.log_rpow hk]
  have key : σ / ν * Real.log C + -1 / ν * Real.log (1 - Real.exp (-i))
      = (σ * Real.log C - Real.log (1 - Real.exp (-i))) / ν := by ring
  rw [key, eq_div_iff hν.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 34: money is held only at a positive nominal rate. For `i ≤ 0` the
optimality condition (33) `m^{−ν} = (1 − e^{−i}) C^{−σ}` has no solution with `m, C > 0`. -/
theorem no_money_demand_of_nonpos {σ ν i C m : ℝ} (hi : i ≤ 0) (hC : 0 < C) (hm : 0 < m) :
    m ^ (-ν) ≠ (1 - Real.exp (-i)) * C ^ (-σ) := by
  have hk : 1 - Real.exp (-i) ≤ 0 := by
    have : 1 ≤ Real.exp (-i) := Real.one_le_exp (by linarith)
    linarith
  have h1 : 0 < m ^ (-ν) := Real.rpow_pos_of_pos hm _
  have h2 : (1 - Real.exp (-i)) * C ^ (-σ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hk (Real.rpow_pos_of_pos hC _).le
  intro h
  linarith

/-! ### Eq. (35): the log-linear money demand -/

/-- Galí (2015), eq. (35), p. 34: the log money demand implied by (34),
`log(M/P) = (σ/ν) c − ν⁻¹ log(1 − e^{−i})` with `c = log C`. -/
noncomputable def logMoneyDemand (σ ν c i : ℝ) : ℝ :=
  σ / ν * c - 1 / ν * Real.log (1 - Real.exp (-i))

/-- Galí (2015), p. 34: the interest semi-elasticity of money demand `η = 1/(ν(e^i − 1))`. -/
noncomputable def eta (ν i : ℝ) : ℝ := 1 / (ν * (Real.exp i - 1))

/-- Galí (2015), eqs. (34)–(35), p. 34 (**exact**): the log of the money demand (34) is
`logMoneyDemand σ ν (log C) i`. -/
theorem log_money_demand {σ ν i C : ℝ} (hi : 0 < i) (hC : 0 < C) :
    Real.log (C ^ (σ / ν) * (1 - Real.exp (-i)) ^ (-1 / ν))
      = logMoneyDemand σ ν (Real.log C) i := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  rw [Real.log_mul (Real.rpow_pos_of_pos hC _).ne' (Real.rpow_pos_of_pos hk _).ne',
    Real.log_rpow hC, Real.log_rpow hk, logMoneyDemand]
  ring

/-- Galí (2015), p. 34 (the Taylor step behind (35)): for `i > 0`,
`d/di log(1 − e^{−i}) = 1/(e^i − 1)`. -/
theorem hasDerivAt_log_one_sub_exp_neg {i : ℝ} (hi : 0 < i) :
    HasDerivAt (fun j => Real.log (1 - Real.exp (-j))) (1 / (Real.exp i - 1)) i := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have h1 : HasDerivAt (fun j => 1 - Real.exp (-j)) (-(Real.exp (-i) * (-1))) i :=
    ((hasDerivAt_neg i).exp).const_sub 1
  refine (h1.log hk.ne').congr_deriv ?_
  have he : 1 < Real.exp i := Real.one_lt_exp_iff.2 hi
  have hx : Real.exp (-i) = (Real.exp i)⁻¹ := Real.exp_neg i
  rw [hx]
  have : Real.exp i - 1 ≠ 0 := by linarith
  have : Real.exp i ≠ 0 := (Real.exp_pos i).ne'
  field_simp

/-- Galí (2015), eq. (35), p. 34, as an **exact derivative**: for `i > 0`, `ν ≠ 0`, the log
money demand `(c, i) ↦ (σ/ν) c − ν⁻¹ log(1 − e^{−i})` has total derivative
`(dc, di) ↦ (σ/ν) dc − η di`, `η = 1/(ν(e^i − 1))`; to first order
`m − p = (σ/ν) c − η i` up to a constant. -/
theorem hasFDerivAt_logMoneyDemand (σ ν c : ℝ) {i : ℝ} (hi : 0 < i) :
    HasFDerivAt (fun x : ℝ × ℝ => logMoneyDemand σ ν x.1 x.2)
      ((σ / ν) • ContinuousLinearMap.fst ℝ ℝ ℝ - eta ν i • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c, i) := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((c, i) : ℝ × ℝ))).const_mul (σ / ν)
  have h2 := ((hasDerivAt_log_one_sub_exp_neg hi).comp_hasFDerivAt ((c, i) : ℝ × ℝ)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((c, i) : ℝ × ℝ)))).const_mul (1 / ν)
  refine (h1.sub h2).congr_fderiv ?_
  ext
  · simp [eta]
  · simp [eta]
    ring

/-- Galí (2015), p. 34: `η > 0` for `ν > 0`, `i > 0`. -/
theorem eta_pos {ν i : ℝ} (hν : 0 < ν) (hi : 0 < i) : 0 < eta ν i := by
  have : 0 < Real.exp i - 1 := by linarith [Real.one_lt_exp_iff.2 hi]
  unfold eta
  positivity

/-- Galí (2015), p. 34 (`η ≃ 1/(νi)`, upper bound): `η ≤ 1/(ν i)`. -/
theorem eta_le {ν i : ℝ} (hν : 0 < ν) (hi : 0 < i) : eta ν i ≤ 1 / (ν * i) := by
  unfold eta
  apply one_div_le_one_div_of_le (mul_pos hν hi)
  have := Real.add_one_le_exp i
  nlinarith

/-- Galí (2015), p. 34 (`η ≃ 1/(νi)`, lower bound): `e^{−i}/(ν i) ≤ η`. -/
theorem exp_neg_div_le_eta {ν i : ℝ} (hν : 0 < ν) (hi : 0 < i) :
    Real.exp (-i) / (ν * i) ≤ eta ν i := by
  have hpos : 0 < Real.exp i - 1 := by linarith [Real.one_lt_exp_iff.2 hi]
  have h : Real.exp (-i) * Real.exp i = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 := one_sub_exp_neg_le i
  unfold eta
  rw [div_le_div_iff₀ (mul_pos hν hi) (mul_pos hν hpos)]
  have e : Real.exp (-i) * (ν * (Real.exp i - 1)) = ν * (1 - Real.exp (-i)) := by
    linear_combination ν * h
  rw [e]
  nlinarith

/-! ### Eq. (36): the case `ν = σ` -/

/-- Galí (2015), eq. (36), p. 34 (**exact derivative**): for `ν = σ ≠ 0` the log money demand
has unit consumption elasticity: its derivative is `(dc, di) ↦ dc − η di`. -/
theorem hasFDerivAt_logMoneyDemand_unit (c : ℝ) {σ i : ℝ} (hσ : σ ≠ 0) (hi : 0 < i) :
    HasFDerivAt (fun x : ℝ × ℝ => logMoneyDemand σ σ x.1 x.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ - eta σ i • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, i) := by
  have := hasFDerivAt_logMoneyDemand σ σ c hi
  rwa [div_self hσ, one_smul] at this

/-- Galí (2015), eq. (36), p. 34 (the log-linear model): with `ν = σ` the linearised money
demand reads `m − p = c − η i`, and with all output consumed (`y = c`) it is
`m − p = y − η i`. -/
theorem money_demand_unit_elastic {σ η mp c y i : ℝ} (hσ : σ ≠ 0)
    (h35 : mp = σ / σ * c - η * i) (hyc : y = c) : mp = c - η * i ∧ mp = y - η * i := by
  rw [div_self hσ, one_mul] at h35
  exact ⟨h35, hyc ▸ h35⟩

end Gali.ClassicalMonetaryModel.MIUSeparable

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money in the utility function: the nonseparable example

Galí (2015), Chapter 2, §2.5.2 (pp. 34–40).

## The household

Period utility is `U(X, N) = (X^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)` with the CES composite
`X = ((1 − ϑ) C^{1−ν} + ϑ (M/P)^{1−ν})^{1/(1−ν)}` (`X = C^{1−ϑ} (M/P)^ϑ` for `ν = 1`),
`composite`, `nsUtil`, with `0 < ϑ < 1`, `σ, ν > 0`.

* `hasDerivAt_composite_path`, `hasDerivAt_nsUtil_C`, `hasDerivAt_nsUtil_m`: the marginal
  utilities `U_c = (1 − ϑ) X^{ν−σ} C^{−ν}`, `U_m = ϑ X^{ν−σ} (M/P)^{−ν}` (p. 35).
* `labour_foc_necessary` (eq. (37)), `money_foc_necessary` + `money_demand_39_iff`
  (eq. (39)), `uc_ratio` + `euler5_iff_miuEuler` (eq. (38) from (5)), all from the
  variational arguments of
  pp. 19–20 and 33. `labour_supply_nu_eq_sigma`, `miuEuler_nu_eq_sigma`: for `ν = σ`
  (37)–(38) reduce to the separable case. `moneyDemand39_homogeneous`,
  `hasFDerivAt_log_money_demand_40`: fn. 10 (unit consumption elasticity for all `ν, σ`)
  and eq. (40) as an exact derivative.
* `labour_supply_log`: the log form of (37), `w − p = σc + φn + (ν − σ)(c − x)`, exactly.

## Steady state and the coefficients `χ`, `k_m`, `ϖ`

* `hasFDerivAt_gap`: `c − x` as a function of `(c, m − p)` has derivative
  `χ (dc − d(m − p))` with `χ = share ϑ ν (m − p − c)`; at the zero-inflation steady state
  (`km_money_demand`: `M/P = k_m C`, `k_m = (ϑ/((1 − β)(1 − ϑ)))^{1/ν}`),
  `share_at_km`: `χ = k_m(1 − β)/(1 + k_m(1 − β))`, `chi1_eq_chi`: the printed first form
  equals it; `chi_mem`: `χ ∈ [0, 1)`.
* `eta_steady_state`, `varpi_eq`: `ϖ = η χ (ν − σ) = k_m β (1 − σ/ν)/(1 + k_m(1 − β))`;
  `eq41`: eq. (41).

## The log-linear equilibrium

* `eq43`: (42)–(43), `y = ψ_ya a + ψ_yi i + const`, `ψ_yi = −ϖ(1 − α)/D`;
  `psiYi_neg_iff`, `varpi_pos_iff`.
* `tendsto_psiYi_nu`, `psiYi_limit_calib`, `tendsto_calib_beta_one` and the numerical
  bounds `psiYi_limit_km_base`, `psiYi_limit_km_m2` (p. 38).
* `eq44_45`, `Theta_mem`: (44)–(45), `Θ ∈ [0, 1)`.
* `miuEuler_iff_moment`, `pf_miuEuler_iff` (exact), `hasDerivAt_log_miuMoment_family`
  (exact derivative under uncertainty), `linearisedMIUEuler_eq_zero_iff`,
  `eulerGap_iff_eulerLinear`: eqs. (46)–(47).
* `real_balance_eq_iff`, `price_level_48`, `price_level_48_exists`: eq. (48), the unique
  solution with bounded real balances, via `eq_forwardSeries`.
* `real_wage_countercyclical`, `real_wage_strictly_countercyclical`,
  `real_wage_acyclical_of_alpha_zero`: p. 39–40.
-/

namespace Gali.ClassicalMonetaryModel.MIUNonseparable

open Filter Topology

/-! ### The composite index `X` -/

/-- Galí (2015), p. 35: the composite of consumption and real balances,
`X = ((1 − ϑ) C^{1−ν} + ϑ m^{1−ν})^{1/(1−ν)}` for `ν ≠ 1` and `X = C^{1−ϑ} m^ϑ` for `ν = 1`. -/
noncomputable def composite (ϑ ν C m : ℝ) : ℝ :=
  if ν = 1 then C ^ (1 - ϑ) * m ^ ϑ
  else ((1 - ϑ) * C ^ (1 - ν) + ϑ * m ^ (1 - ν)) ^ (1 / (1 - ν))

/-- Galí (2015), p. 35: the composite is positive for positive `C`, `m` and `0 < ϑ < 1`. -/
theorem composite_pos {ϑ ν C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hC : 0 < C) (hm : 0 < m) :
    0 < composite ϑ ν C m := by
  unfold composite
  split_ifs
  · exact mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hm _)
  · exact Real.rpow_pos_of_pos (add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hC _))
      (mul_pos hϑ0 (Real.rpow_pos_of_pos hm _))) _

/-- Galí (2015), p. 35: the composite is homogeneous of degree one,
`X(λC, λm) = λ X(C, m)` for `λ > 0`. -/
theorem composite_homogeneous {ϑ ν C m l : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hC : 0 < C)
    (hm : 0 < m) (hl : 0 < l) : composite ϑ ν (l * C) (l * m) = l * composite ϑ ν C m := by
  unfold composite
  split_ifs with hν
  · rw [Real.mul_rpow hl.le hC.le, Real.mul_rpow hl.le hm.le]
    have : l ^ (1 - ϑ) * l ^ ϑ = l := by
      rw [← Real.rpow_add hl, sub_add_cancel, Real.rpow_one]
    calc l ^ (1 - ϑ) * C ^ (1 - ϑ) * (l ^ ϑ * m ^ ϑ)
        = (l ^ (1 - ϑ) * l ^ ϑ) * (C ^ (1 - ϑ) * m ^ ϑ) := by ring
      _ = l * (C ^ (1 - ϑ) * m ^ ϑ) := by rw [this]
  · have hs : (1 : ℝ) - ν ≠ 0 := sub_ne_zero.2 (Ne.symm hν)
    have hS : 0 < (1 - ϑ) * C ^ (1 - ν) + ϑ * m ^ (1 - ν) :=
      add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hC _))
        (mul_pos hϑ0 (Real.rpow_pos_of_pos hm _))
    rw [Real.mul_rpow hl.le hC.le, Real.mul_rpow hl.le hm.le]
    have e : (1 - ϑ) * (l ^ (1 - ν) * C ^ (1 - ν)) + ϑ * (l ^ (1 - ν) * m ^ (1 - ν))
        = l ^ (1 - ν) * ((1 - ϑ) * C ^ (1 - ν) + ϑ * m ^ (1 - ν)) := by ring
    rw [e, Real.mul_rpow (Real.rpow_pos_of_pos hl _).le hS.le, ← Real.rpow_mul hl.le,
      mul_one_div_cancel hs, Real.rpow_one]

/-- Galí (2015), p. 35: derivative of the composite along a differentiable path
`y ↦ (c y, q y)` of consumption and real balances:
`dX = X^ν ((1 − ϑ) C^{−ν} dC + ϑ m^{−ν} dm)`. -/
theorem hasDerivAt_composite_path {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) {c q : ℝ → ℝ}
    {c' q' x : ℝ} (hc : HasDerivAt c c' x) (hq : HasDerivAt q q' x) (hcx : 0 < c x)
    (hqx : 0 < q x) :
    HasDerivAt (fun y => composite ϑ ν (c y) (q y))
      (composite ϑ ν (c x) (q x) ^ ν * ((1 - ϑ) * c x ^ (-ν) * c' + ϑ * q x ^ (-ν) * q')) x := by
  by_cases hν : ν = 1
  · subst hν
    have hfun : (fun y => composite ϑ 1 (c y) (q y)) = fun y => c y ^ (1 - ϑ) * q y ^ ϑ := by
      funext y
      simp [composite]
    rw [hfun]
    have h1 := hc.rpow_const (p := 1 - ϑ) (Or.inl hcx.ne')
    have h2 := hq.rpow_const (p := ϑ) (Or.inl hqx.ne')
    refine (h1.mul h2).congr_deriv ?_
    simp only [composite, ↓reduceIte, Real.rpow_one]
    rw [show (1 : ℝ) - ϑ - 1 = (1 - ϑ) + (-1) by ring, show ϑ - 1 = ϑ + (-1) by ring,
      Real.rpow_add hcx, Real.rpow_add hqx]
    ring
  · have hs : (1 : ℝ) - ν ≠ 0 := sub_ne_zero.2 (Ne.symm hν)
    have hfun : (fun y => composite ϑ ν (c y) (q y))
        = fun y => ((1 - ϑ) * c y ^ (1 - ν) + ϑ * q y ^ (1 - ν)) ^ (1 / (1 - ν)) := by
      funext y
      simp [composite, hν]
    have hSpos : 0 < (1 - ϑ) * c x ^ (1 - ν) + ϑ * q x ^ (1 - ν) :=
      add_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hcx _))
        (mul_pos hϑ0 (Real.rpow_pos_of_pos hqx _))
    have hSd := ((hc.rpow_const (p := 1 - ν) (Or.inl hcx.ne')).const_mul (1 - ϑ)).add
      ((hq.rpow_const (p := 1 - ν) (Or.inl hqx.ne')).const_mul ϑ)
    rw [hfun]
    refine (hSd.rpow_const (p := 1 / (1 - ν)) (Or.inl hSpos.ne')).congr_deriv ?_
    have hX : composite ϑ ν (c x) (q x)
        = ((1 - ϑ) * c x ^ (1 - ν) + ϑ * q x ^ (1 - ν)) ^ (1 / (1 - ν)) := by
      simp [composite, hν]
    simp only [Pi.add_apply]
    rw [hX, ← Real.rpow_mul hSpos.le, show 1 / (1 - ν) - 1 = 1 / (1 - ν) * ν by field_simp; ring,
      show (1 : ℝ) - ν - 1 = -ν by ring]
    field_simp

/-! ### Utility and marginal utilities -/

/-- Galí (2015), p. 34: period utility `U(X, N) = (X^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)`
(log branch for `σ = 1`), as a function of consumption `C`, real balances `m` and hours. -/
noncomputable def nsUtil (σ φ ϑ ν C m N : ℝ) : ℝ :=
  MIUSeparable.utilPow σ (composite ϑ ν C m) - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 35: derivative of utility along a path of `(C, m)` with hours fixed:
`X^{ν−σ}((1 − ϑ) C^{−ν} dC + ϑ m^{−ν} dm)`. -/
theorem hasDerivAt_nsUtil_path (σ φ N : ℝ) {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    {c q : ℝ → ℝ} {c' q' x : ℝ} (hc : HasDerivAt c c' x) (hq : HasDerivAt q q' x)
    (hcx : 0 < c x) (hqx : 0 < q x) :
    HasDerivAt (fun y => nsUtil σ φ ϑ ν (c y) (q y) N)
      (composite ϑ ν (c x) (q x) ^ (ν - σ) *
        ((1 - ϑ) * c x ^ (-ν) * c' + ϑ * q x ^ (-ν) * q')) x := by
  have hX := composite_pos (ν := ν) hϑ0 hϑ1 hcx hqx
  have h := ((MIUSeparable.hasDerivAt_utilPow σ hX).comp x
    (hasDerivAt_composite_path hϑ0 hϑ1 hc hq hcx hqx)).sub_const (N ^ (1 + φ) / (1 + φ))
  refine h.congr_deriv ?_
  rw [show ν - σ = -σ + ν by ring, Real.rpow_add hX]
  ring

/-- Galí (2015), p. 35: the marginal utility of consumption `U_c = (1 − ϑ) X^{ν−σ} C^{−ν}`. -/
theorem hasDerivAt_nsUtil_C (σ φ N : ℝ) {ϑ ν C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun C' => nsUtil σ φ ϑ ν C' m N)
      ((1 - ϑ) * composite ϑ ν C m ^ (ν - σ) * C ^ (-ν)) C := by
  have := hasDerivAt_nsUtil_path σ φ N (ν := ν) hϑ0 hϑ1 (hasDerivAt_id C)
    (hasDerivAt_const C m) hC hm
  refine this.congr_deriv ?_
  simp only [id]
  ring

/-- Galí (2015), p. 35: the marginal utility of real balances `U_m = ϑ X^{ν−σ} m^{−ν}`. -/
theorem hasDerivAt_nsUtil_m (σ φ N : ℝ) {ϑ ν C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun m' => nsUtil σ φ ϑ ν C m' N)
      (ϑ * composite ϑ ν C m ^ (ν - σ) * m ^ (-ν)) m := by
  have := hasDerivAt_nsUtil_path σ φ N (ν := ν) hϑ0 hϑ1 (hasDerivAt_const m C)
    (hasDerivAt_id m) hC hm
  refine this.congr_deriv ?_
  simp only [id]
  ring

/-- Galí (2015), p. 35: the marginal rate of substitution between real balances and
consumption, `U_m / U_c = (ϑ/(1 − ϑ)) (m/C)^{−ν}`. -/
theorem um_div_uc {ϑ ν σ C m X : ℝ} (hϑ1 : ϑ < 1) (hC : 0 < C) (hm : 0 < m) (hX : 0 < X) :
    ϑ * X ^ (ν - σ) * m ^ (-ν) / ((1 - ϑ) * X ^ (ν - σ) * C ^ (-ν))
      = ϑ / (1 - ϑ) * (m / C) ^ (-ν) := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 := (Real.rpow_pos_of_pos hX (ν - σ)).ne'
  have h3 := (Real.rpow_pos_of_pos hC (-ν)).ne'
  rw [Real.div_rpow hm.le hC.le]
  field_simp

/-! ### Eq. (37): labour supply -/

/-- Galí (2015), eq. (37), p. 35: the marginal rate of substitution
`−U_n/U_c = N^φ / ((1 − ϑ) X^{ν−σ} C^{−ν}) = N^φ X^{σ−ν} C^ν (1 − ϑ)⁻¹`. -/
theorem mrs_eq {ϑ ν σ φ N C X : ℝ} (hϑ1 : ϑ < 1) (hC : 0 < C) (hX : 0 < X) :
    N ^ φ / ((1 - ϑ) * X ^ (ν - σ) * C ^ (-ν)) = N ^ φ * X ^ (σ - ν) * C ^ ν / (1 - ϑ) := by
  have h1 : (1 : ℝ) - ϑ ≠ 0 := by linarith
  rw [show σ - ν = -(ν - σ) by ring, Real.rpow_neg hX.le, Real.rpow_neg hC.le]
  have h2 := (Real.rpow_pos_of_pos hX (ν - σ)).ne'
  have h3 := (Real.rpow_pos_of_pos hC ν).ne'
  field_simp

/-- Galí (2015), eq. (37), p. 35 (**necessity**): if hours `N` are a local optimum along the
budget line `P C = W N + Y₀` (the perturbation `P dC = W dN` of p. 19, real balances `m` and
everything else unchanged), with `C, m > 0`, then `W/P = N^φ X^{σ−ν} C^ν (1 − ϑ)⁻¹`. -/
theorem labour_foc_necessary {σ φ ϑ ν P W Y₀ C m N : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1)
    (hφ : 0 ≤ φ) (hP : 0 < P) (hC : 0 < C) (hm : 0 < m) (hbud : P * C = W * N + Y₀)
    (hloc : IsLocalMax (fun N' => nsUtil σ φ ϑ ν ((W * N' + Y₀) / P) m N') N) :
    W / P = N ^ φ * composite ϑ ν C m ^ (σ - ν) * C ^ ν / (1 - ϑ) := by
  have hCeq : (W * N + Y₀) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + Y₀) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const Y₀).div_const P
    simpa using this
  have hX := composite_pos (ν := ν) hϑ0 hϑ1 hC hm
  have hd : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    have : (1 : ℝ) + φ ≠ 0 := by linarith
    field_simp
  have hp := hasDerivAt_composite_path (ν := ν) hϑ0 hϑ1 hin (hasDerivAt_const N m)
    (by rw [hCeq]; exact hC) hm
  have hu := (MIUSeparable.hasDerivAt_utilPow σ (composite_pos (ν := ν) hϑ0 hϑ1
    (by rw [hCeq]; exact hC) hm)).comp N hp
  have hg := HasDerivAt.sub hu hd
  have h0 := hloc.hasDerivAt_eq_zero hg
  simp only [hCeq, mul_zero, add_zero] at h0
  rw [← mrs_eq (φ := φ) (N := N) (σ := σ) (ν := ν) hϑ1 hC hX]
  have hUc : 0 < (1 - ϑ) * composite ϑ ν C m ^ (ν - σ) * C ^ (-ν) :=
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hX _)) (Real.rpow_pos_of_pos hC _)
  rw [eq_div_iff hUc.ne']
  have e : composite ϑ ν C m ^ (-σ) * (composite ϑ ν C m ^ ν * ((1 - ϑ) * C ^ (-ν) * (W / P)))
      = W / P * ((1 - ϑ) * composite ϑ ν C m ^ (ν - σ) * C ^ (-ν)) := by
    rw [show ν - σ = -σ + ν by ring, Real.rpow_add hX]
    ring
  linarith

/-- Galí (2015), p. 35: with `ν = σ` the labour supply (37) is
`W/P = N^φ C^σ (1 − ϑ)⁻¹`, the separable case up to the constant factor `(1 − ϑ)⁻¹`. -/
theorem labour_supply_nu_eq_sigma (ϑ σ φ N X C : ℝ) :
    N ^ φ * X ^ (σ - σ) * C ^ σ / (1 - ϑ) = N ^ φ * C ^ σ / (1 - ϑ) := by
  rw [sub_self, Real.rpow_zero, mul_one]

/-- Galí (2015), p. 36: the log form of (37), exactly,
`log(N^φ X^{σ−ν} C^ν/(1 − ϑ)) = σ c + φ n + (ν − σ)(c − x) − log(1 − ϑ)`. -/
theorem labour_supply_log {σ φ ϑ ν N X C : ℝ} (hϑ1 : ϑ < 1) (hN : 0 < N) (hX : 0 < X)
    (hC : 0 < C) :
    Real.log (N ^ φ * X ^ (σ - ν) * C ^ ν / (1 - ϑ))
      = σ * Real.log C + φ * Real.log N + (ν - σ) * (Real.log C - Real.log X)
        - Real.log (1 - ϑ) := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hX,
    Real.log_rpow hC]
  ring

/-! ### Eq. (39): money demand -/

/-- Galí (2015), eq. (39), p. 35 (**necessity**, eq. (33) for the nonseparable utility): if the
money perturbation `(dC, dM) = (−(1 − Q) δ / P, δ)` (p. 33) cannot raise utility, then
`U_m = (1 − Q) U_c`, i.e. `ϑ m^{−ν} = (1 − Q)(1 − ϑ) C^{−ν}` with `m = M/P`. -/
theorem money_foc_necessary {σ φ ϑ ν P Q C M N : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hP : 0 < P)
    (hC : 0 < C) (hM : 0 < M)
    (hloc : IsLocalMax (fun δ => nsUtil σ φ ϑ ν (C - (1 - Q) * δ / P) ((M + δ) / P) N) 0) :
    ϑ * (M / P) ^ (-ν) = (1 - Q) * ((1 - ϑ) * C ^ (-ν)) := by
  have hc1 : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa using this
  have hc2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add M).div_const P
    simpa using this
  have h := hasDerivAt_nsUtil_path σ φ N (ν := ν) hϑ0 hϑ1 hc1 hc2 (by simpa using hC)
    (by simpa using div_pos hM hP)
  have h0 := hloc.hasDerivAt_eq_zero h
  simp only [mul_zero, zero_div, sub_zero, add_zero] at h0
  have hX := composite_pos (ν := ν) hϑ0 hϑ1 hC (div_pos hM hP)
  have h1 := (mul_eq_zero.1 h0).resolve_left (Real.rpow_pos_of_pos hX _).ne'
  field_simp at h1
  linarith

/-- Galí (2015), eq. (39), p. 35: the money demand
`M/P = C (1 − e^{−i})^{−1/ν} (ϑ/(1 − ϑ))^{1/ν}`. -/
noncomputable def moneyDemand39 (ϑ ν C i : ℝ) : ℝ :=
  C * (1 - Real.exp (-i)) ^ (-1 / ν) * (ϑ / (1 - ϑ)) ^ (1 / ν)

/-- Galí (2015), eq. (39), p. 35 (**exact**): for `i > 0`, the optimality condition
`ϑ m^{−ν} = (1 − e^{−i})(1 − ϑ) C^{−ν}` is equivalent to the money demand (39). -/
theorem money_demand_39_iff {ϑ ν i C m : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hν : 0 < ν)
    (hi : 0 < i) (hC : 0 < C) (hm : 0 < m) :
    ϑ * m ^ (-ν) = (1 - Real.exp (-i)) * ((1 - ϑ) * C ^ (-ν)) ↔ m = moneyDemand39 ϑ ν C i := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have hr : 0 < ϑ / (1 - ϑ) := div_pos hϑ0 h1
  have hp1 : 0 < ϑ * m ^ (-ν) := mul_pos hϑ0 (Real.rpow_pos_of_pos hm _)
  have hp2 : 0 < (1 - Real.exp (-i)) * ((1 - ϑ) * C ^ (-ν)) :=
    mul_pos hk (mul_pos h1 (Real.rpow_pos_of_pos hC _))
  have hp3 : 0 < moneyDemand39 ϑ ν C i := by
    unfold moneyDemand39
    exact mul_pos (mul_pos hC (Real.rpow_pos_of_pos hk _)) (Real.rpow_pos_of_pos hr _)
  rw [← Real.log_injOn_pos.eq_iff hp1 hp2, ← Real.log_injOn_pos.eq_iff hm hp3]
  unfold moneyDemand39
  rw [Real.log_mul hϑ0.ne' (Real.rpow_pos_of_pos hm _).ne', Real.log_rpow hm,
    Real.log_mul hk.ne' (mul_pos h1 (Real.rpow_pos_of_pos hC _)).ne',
    Real.log_mul h1.ne' (Real.rpow_pos_of_pos hC _).ne', Real.log_rpow hC,
    Real.log_mul (mul_pos hC (Real.rpow_pos_of_pos hk _)).ne' (Real.rpow_pos_of_pos hr _).ne',
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos hk _).ne', Real.log_rpow hk, Real.log_rpow hr,
    Real.log_div hϑ0.ne' h1.ne']
  have key : Real.log C + -1 / ν * Real.log (1 - Real.exp (-i))
      + 1 / ν * (Real.log ϑ - Real.log (1 - ϑ))
      = (ν * Real.log C - Real.log (1 - Real.exp (-i)) + (Real.log ϑ - Real.log (1 - ϑ))) / ν := by
    field_simp
    ring
  rw [key, eq_div_iff hν.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), fn. 10, p. 36: the money demand (39) is homogeneous of degree one in
consumption (unit consumption elasticity), whatever `ν` and `σ`. -/
theorem moneyDemand39_homogeneous (ϑ ν C i l : ℝ) :
    moneyDemand39 ϑ ν (l * C) i = l * moneyDemand39 ϑ ν C i := by
  unfold moneyDemand39
  ring

/-- Galí (2015), eq. (40), p. 36 (**exact**): for `i > 0`,
`log(M/P) = c − ν⁻¹ log(1 − e^{−i}) + ν⁻¹ log(ϑ/(1 − ϑ))` with `c = log C`. -/
theorem log_moneyDemand39 {ϑ ν i C : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hν : ν ≠ 0)
    (hi : 0 < i) (hC : 0 < C) :
    Real.log (moneyDemand39 ϑ ν C i)
      = MIUSeparable.logMoneyDemand ν ν (Real.log C) i + 1 / ν * Real.log (ϑ / (1 - ϑ)) := by
  have hk : 0 < 1 - Real.exp (-i) := by
    have : Real.exp (-i) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hr : 0 < ϑ / (1 - ϑ) := div_pos hϑ0 (by linarith)
  unfold moneyDemand39 MIUSeparable.logMoneyDemand
  rw [Real.log_mul (mul_pos hC (Real.rpow_pos_of_pos hk _)).ne' (Real.rpow_pos_of_pos hr _).ne',
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos hk _).ne', Real.log_rpow hk, Real.log_rpow hr]
  rw [div_self hν]
  ring

/-- Galí (2015), eq. (40), p. 36 (**exact derivative**): for `ν ≠ 0`, `i > 0`, the log money
demand `(c, i) ↦ c − ν⁻¹ log(1 − e^{−i}) + const` has derivative `(dc, di) ↦ dc − η di`,
`η = 1/(ν(e^i − 1))`: to first order `m − p = c − η i` (up to a constant). -/
theorem hasFDerivAt_log_money_demand_40 (ϑ c : ℝ) {ν i : ℝ} (hν : ν ≠ 0) (hi : 0 < i) :
    HasFDerivAt
      (fun x : ℝ × ℝ => MIUSeparable.logMoneyDemand ν ν x.1 x.2 + 1 / ν * Real.log (ϑ / (1 - ϑ)))
      (ContinuousLinearMap.fst ℝ ℝ ℝ - MIUSeparable.eta ν i • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c, i) :=
  (MIUSeparable.hasFDerivAt_logMoneyDemand_unit c hν hi).add_const _

/-! ### `χ`: the log-linearised composite -/

/-- Galí (2015), p. 36: the share of real balances in the composite, as a function of
`d = log(M/P) − log C`: `ϑ e^{(1−ν)d}/((1 − ϑ) + ϑ e^{(1−ν)d})`. -/
noncomputable def share (ϑ ν d : ℝ) : ℝ :=
  ϑ * Real.exp ((1 - ν) * d) / ((1 - ϑ) + ϑ * Real.exp ((1 - ν) * d))

/-- Galí (2015), p. 36: `x = log X` as a function of `c = log C` and `q = log(M/P)`. -/
noncomputable def logX (ϑ ν c q : ℝ) : ℝ := Real.log (composite ϑ ν (Real.exp c) (Real.exp q))

/-- Galí (2015), p. 36: by homogeneity `x(c, q) = c + x(0, q − c)`. -/
theorem logX_homogeneous {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (c q : ℝ) :
    logX ϑ ν c q = c + logX ϑ ν 0 (q - c) := by
  unfold logX
  have h1 : Real.exp c = Real.exp c * Real.exp 0 := by rw [Real.exp_zero, mul_one]
  have h2 : Real.exp q = Real.exp c * Real.exp (q - c) := by
    rw [← Real.exp_add, add_sub_cancel]
  rw [h1, h2, composite_homogeneous hϑ0 hϑ1 (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _),
    Real.log_mul (Real.exp_pos _).ne' (composite_pos hϑ0 hϑ1 (Real.exp_pos _)
      (Real.exp_pos _)).ne', Real.log_exp, Real.exp_zero]

/-- Galí (2015), p. 36: `d ↦ x(0, d)` has derivative `share ϑ ν d` (both for `ν ≠ 1` and
for the Cobb–Douglas case `ν = 1`, where the share is `ϑ`). -/
theorem hasDerivAt_logX_zero {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (d : ℝ) :
    HasDerivAt (fun d' => logX ϑ ν 0 d') (share ϑ ν d) d := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  by_cases hν : ν = 1
  · subst hν
    have hfun : (fun d' => logX ϑ 1 0 d') = fun d' => ϑ * d' := by
      funext d'
      simp only [logX, composite, ↓reduceIte, Real.exp_zero, Real.one_rpow, one_mul]
      rw [Real.log_rpow (Real.exp_pos _), Real.log_exp]
    rw [hfun]
    refine ((hasDerivAt_id d).const_mul ϑ).congr_deriv ?_
    simp [share]
  · have hs : (1 : ℝ) - ν ≠ 0 := sub_ne_zero.2 (Ne.symm hν)
    have hfun : (fun d' => logX ϑ ν 0 d')
        = fun d' => 1 / (1 - ν) * Real.log ((1 - ϑ) + ϑ * Real.exp ((1 - ν) * d')) := by
      funext d'
      have hS : 0 < (1 - ϑ) + ϑ * Real.exp ((1 - ν) * d') :=
        add_pos h1 (mul_pos hϑ0 (Real.exp_pos _))
      simp only [logX, composite, hν, ↓reduceIte, Real.exp_zero, Real.one_rpow, mul_one]
      rw [← Real.exp_mul, mul_comm d', Real.log_rpow hS]
    rw [hfun]
    have hS : 0 < (1 - ϑ) + ϑ * Real.exp ((1 - ν) * d) :=
      add_pos h1 (mul_pos hϑ0 (Real.exp_pos _))
    have hin : HasDerivAt (fun d' => (1 - ϑ) + ϑ * Real.exp ((1 - ν) * d'))
        (ϑ * (Real.exp ((1 - ν) * d) * (1 - ν))) d := by
      have := (((hasDerivAt_id d).const_mul (1 - ν)).exp.const_mul ϑ).const_add (1 - ϑ)
      simpa using this
    refine ((hin.log hS.ne').const_mul (1 / (1 - ν))).congr_deriv ?_
    unfold share
    field_simp

/-- Galí (2015), p. 36 (**exact derivative**): `c − x` as a function of `(c, q)`, `q = m − p`,
has total derivative `χ (dc − dq)` at `(c, q)`, with `χ = share ϑ ν (q − c)`: to first
order `c − x = χ (c − (m − p))` (up to a constant). -/
theorem hasFDerivAt_gap {ϑ ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (c q : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => x.1 - logX ϑ ν x.1 x.2)
      (share ϑ ν (q - c) • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))
      (c, q) := by
  have hfun : (fun x : ℝ × ℝ => x.1 - logX ϑ ν x.1 x.2)
      = fun x : ℝ × ℝ => -logX ϑ ν 0 (x.2 - x.1) := by
    funext x
    rw [logX_homogeneous hϑ0 hϑ1 x.1 x.2]
    ring
  rw [hfun]
  have hl : HasFDerivAt (fun x : ℝ × ℝ => x.2 - x.1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (c, q) :=
    hasFDerivAt_snd.sub hasFDerivAt_fst
  have h := ((hasDerivAt_logX_zero (ν := ν) hϑ0 hϑ1 (q - c)).comp_hasFDerivAt (c, q) hl).neg
  refine h.congr_fderiv ?_
  ext <;> simp

/-- Galí (2015), p. 36: the steady-state inverse consumption velocity
`k_m = (ϑ/((1 − β)(1 − ϑ)))^{1/ν}`. -/
noncomputable def km (ϑ β ν : ℝ) : ℝ := (ϑ / ((1 - β) * (1 - ϑ))) ^ (1 / ν)

/-- Galí (2015), p. 37: `χ = k_m(1 − β)/(1 + k_m(1 − β))`, written as a function of `k`. -/
noncomputable def chi (k β : ℝ) : ℝ := k * (1 - β) / (1 + k * (1 - β))

/-- Galí (2015), p. 36: the first printed form
`χ = ϑ^{1/ν}(1 − β)^{1−1/ν}/((1 − ϑ)^{1/ν} + ϑ^{1/ν}(1 − β)^{1−1/ν})`. -/
noncomputable def chi1 (ϑ β ν : ℝ) : ℝ :=
  ϑ ^ (1 / ν) * (1 - β) ^ (1 - 1 / ν) /
    ((1 - ϑ) ^ (1 / ν) + ϑ ^ (1 / ν) * (1 - β) ^ (1 - 1 / ν))

/-- Galí (2015), p. 36: `k_m > 0`. -/
theorem km_pos {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1) : 0 < km ϑ β ν :=
  Real.rpow_pos_of_pos (div_pos hϑ0 (mul_pos (by linarith) (by linarith))) _

/-- Galí (2015), p. 36: `k_m` is the steady-state ratio `(M/P)/C` implied by the money demand
(39) at the zero-inflation steady state `i = ρ = −log β`. -/
theorem km_money_demand {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (C : ℝ) : moneyDemand39 ϑ ν C (-Real.log β) = C * km ϑ β ν := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 : (0 : ℝ) < 1 - β := by linarith
  unfold moneyDemand39 km
  rw [neg_neg, Real.exp_log hβ0, mul_assoc]
  congr 1
  rw [show ϑ / ((1 - β) * (1 - ϑ)) = (1 - β)⁻¹ * (ϑ / (1 - ϑ)) by field_simp,
    Real.mul_rpow (inv_nonneg.2 h2.le) (div_pos hϑ0 h1).le, Real.inv_rpow h2.le, neg_div,
    Real.rpow_neg h2.le]

/-- Galí (2015), p. 36: at the steady-state ratio `M/P = k_m C` the share equals
`χ = k_m(1 − β)/(1 + k_m(1 − β))` (p. 37). -/
theorem share_at_km {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1) (hν : 0 < ν) :
    share ϑ ν (Real.log (km ϑ β ν)) = chi (km ϑ β ν) β := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 : (0 : ℝ) < 1 - β := by linarith
  have hk := km_pos (ν := ν) hϑ0 hϑ1 hβ1
  have hb : 0 < ϑ / ((1 - β) * (1 - ϑ)) := div_pos hϑ0 (mul_pos h2 h1)
  have hexp : Real.exp ((1 - ν) * Real.log (km ϑ β ν)) = km ϑ β ν * ((1 - β) * (1 - ϑ) / ϑ) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hk, sub_eq_add_neg, Real.rpow_add hk, Real.rpow_one]
    congr 1
    unfold km
    rw [← Real.rpow_mul hb.le, show 1 / ν * -ν = -1 by field_simp, Real.rpow_neg_one, inv_div]
  unfold share chi
  rw [hexp]
  field_simp

/-- Galí (2015), pp. 36–37: the two printed forms of `χ` agree,
`ϑ^{1/ν}(1 − β)^{1−1/ν}/((1 − ϑ)^{1/ν} + ϑ^{1/ν}(1 − β)^{1−1/ν}) = k_m(1 − β)/(1 + k_m(1 − β))`. -/
theorem chi1_eq_chi {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1) :
    chi1 ϑ β ν = chi (km ϑ β ν) β := by
  have h1 : (0 : ℝ) < 1 - ϑ := by linarith
  have h2 : (0 : ℝ) < 1 - β := by linarith
  have a1 := Real.rpow_pos_of_pos h1 (1 / ν)
  have a2 := Real.rpow_pos_of_pos h2 (1 / ν)
  have a3 := Real.rpow_pos_of_pos hϑ0 (1 / ν)
  unfold chi1 chi km
  rw [Real.div_rpow hϑ0.le (mul_pos h2 h1).le, Real.mul_rpow h2.le h1.le,
    Real.rpow_sub h2, Real.rpow_one]
  field_simp

/-- Galí (2015), p. 36: `χ ∈ [0, 1)` for `k ≥ 0` and `β < 1`. -/
theorem chi_mem {k β : ℝ} (hk : 0 ≤ k) (hβ1 : β < 1) : 0 ≤ chi k β ∧ chi k β < 1 := by
  have h : 0 ≤ k * (1 - β) := mul_nonneg hk (by linarith)
  unfold chi
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

/-- Galí (2015), p. 36: `χ` is the partial derivative of `log X` with respect to `log(M/P)` at
the zero-inflation steady state `q = c + log k_m`; with the two printed forms. -/
theorem hasDerivAt_logX_steady_state {ϑ β ν : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hβ1 : β < 1)
    (hν : 0 < ν) (c : ℝ) :
    HasDerivAt (fun q => logX ϑ ν c q) (chi (km ϑ β ν) β) (c + Real.log (km ϑ β ν)) ∧
      chi1 ϑ β ν = chi (km ϑ β ν) β := by
  refine ⟨?_, chi1_eq_chi hϑ0 hϑ1 hβ1⟩
  have hfun : (fun q => logX ϑ ν c q) = fun q => c + logX ϑ ν 0 (q - c) :=
    funext fun q => logX_homogeneous hϑ0 hϑ1 c q
  rw [hfun, ← share_at_km hϑ0 hϑ1 hβ1 hν]
  have h := (hasDerivAt_logX_zero (ν := ν) hϑ0 hϑ1 (c + Real.log (km ϑ β ν) - c)).comp
    (c + Real.log (km ϑ β ν)) ((hasDerivAt_id _).sub_const c)
  have h2 := h.const_add c
  simp only [add_sub_cancel_left, mul_one] at h2
  exact h2

/-! ### `η` and `ϖ` at the steady state; eq. (41) -/

/-- Galí (2015), p. 37: at the zero-inflation steady state `i = ρ = −log β`,
`η = 1/(ν(e^ρ − 1)) = β/(ν(1 − β))`. -/
theorem eta_steady_state {ν β : ℝ} (hν : ν ≠ 0) (hβ0 : 0 < β) (hβ1 : β < 1) :
    MIUSeparable.eta ν (-Real.log β) = β / (ν * (1 - β)) := by
  unfold MIUSeparable.eta
  rw [Real.exp_neg, Real.exp_log hβ0]
  have : (1 : ℝ) - β ≠ 0 := by linarith
  field_simp

/-- Galí (2015), eq. (41), p. 37: `ϖ = k_m β (1 − σ/ν)/(1 + k_m(1 − β))`. -/
noncomputable def varpi (k β σ ν : ℝ) : ℝ := k * β * (1 - σ / ν) / (1 + k * (1 - β))

/-- Galí (2015), p. 37: `η χ (ν − σ) = ϖ` with the steady-state `η = β/(ν(1 − β))`. -/
theorem varpi_eq {k β σ ν : ℝ} (hν : ν ≠ 0) (hβ1 : β < 1) (hk : 0 ≤ k) :
    β / (ν * (1 - β)) * chi k β * (ν - σ) = varpi k β σ ν := by
  have : (1 : ℝ) - β ≠ 0 := by linarith
  have : 1 + k * (1 - β) ≠ 0 := by nlinarith
  unfold chi varpi
  field_simp

/-- Galí (2015), p. 37: for `k_m > 0`, `0 < β < 1`, `ν > 0`: `ϖ > 0 ⟺ ν > σ`. -/
theorem varpi_pos_iff {k β σ ν : ℝ} (hk : 0 < k) (hβ0 : 0 < β) (hβ1 : β < 1) (hν : 0 < ν) :
    0 < varpi k β σ ν ↔ σ < ν := by
  have hA : 0 < 1 + k * (1 - β) := by nlinarith
  have hkb : 0 < k * β := mul_pos hk hβ0
  unfold varpi
  rw [div_pos_iff_of_pos_right hA, mul_pos_iff_of_pos_left hkb, sub_pos, div_lt_one hν]

/-- Galí (2015), eq. (41), p. 37 (the log-linear model): from the log form of (37),
`c − x = χ (c − (m − p))` and (40) `m − p = c − η i`, the labour supply is
`w − p = σ c + φ n + χ (ν − σ)(c − (m − p)) = σ c + φ n + ϖ i` with `ϖ = η χ (ν − σ)`. -/
theorem eq41 {σ φ ν χ η ϖ w c n x mp i : ℝ} (hϖ : ϖ = η * χ * (ν - σ))
    (hls : w = σ * c + φ * n + (ν - σ) * (c - x)) (hx : c - x = χ * (c - mp))
    (h40 : mp = c - η * i) :
    w = σ * c + φ * n + χ * (ν - σ) * (c - mp) ∧ w = σ * c + φ * n + ϖ * i := by
  constructor
  · rw [hls, hx]
    ring
  · rw [hls, hx, h40, hϖ]
    ring

/-! ### Eqs. (42)–(43): output and the nominal rate -/

/-- Galí (2015), p. 23: `D = σ(1 − α) + φ + α`. -/
noncomputable def bigD (σ φ α : ℝ) : ℝ := σ * (1 - α) + φ + α

/-- Galí (2015), p. 37: `ψ_ya = (1 + φ)/D`. -/
noncomputable def psiYa (σ φ α : ℝ) : ℝ := (1 + φ) / bigD σ φ α

/-- Galí (2015), p. 37: `ψ_yi = −ϖ(1 − α)/D`. -/
noncomputable def psiYi (ϖ σ φ α : ℝ) : ℝ := -(ϖ * (1 - α)) / bigD σ φ α

/-- Galí (2015), eqs. (42)–(43), p. 37 (the log-linear model): labour-market clearing
`σ c + φ n + ϖ i = a − α n + log(1 − α)` with `y = c` and `y = a + (1 − α) n` give exactly
`y = ψ_ya a + ψ_yi i + (1 − α) log(1 − α)/D` (the additive constant made explicit). -/
theorem eq43 {σ φ α ϖ y a n i c : ℝ} (hD : bigD σ φ α ≠ 0)
    (h42 : σ * c + φ * n + ϖ * i = a - α * n + Real.log (1 - α)) (hyc : y = c)
    (h17 : y = a + (1 - α) * n) :
    y = psiYa σ φ α * a + psiYi ϖ σ φ α * i + (1 - α) * Real.log (1 - α) / bigD σ φ α := by
  have key : bigD σ φ α * y = (1 + φ) * a - ϖ * (1 - α) * i + (1 - α) * Real.log (1 - α) := by
    unfold bigD
    linear_combination (1 - α) * h42 + σ * (1 - α) * hyc + (φ + α) * h17
  unfold psiYa psiYi
  field_simp
  linear_combination key

/-- Galí (2015), p. 37: for `D > 0` and `α < 1`, `ψ_yi < 0 ⟺ ϖ > 0`. -/
theorem psiYi_neg_iff {ϖ σ φ α : ℝ} (hD : 0 < bigD σ φ α) (hα : α < 1) :
    psiYi ϖ σ φ α < 0 ↔ 0 < ϖ := by
  unfold psiYi
  rw [div_neg_iff]
  constructor
  · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · linarith
    · nlinarith
  · intro h
    right
    exact ⟨by nlinarith, hD⟩

/-- Galí (2015), p. 38: as `ν → ∞` with `k_m`, `β` fixed,
`ψ_yi → −k_m β (1 − α)/(D (1 + k_m (1 − β)))`. -/
theorem tendsto_psiYi_nu (k β σ φ α : ℝ) :
    Tendsto (fun ν => psiYi (varpi k β σ ν) σ φ α) atTop
      (𝓝 (-(k * β * (1 - α)) / (bigD σ φ α * (1 + k * (1 - β))))) := by
  have h1 : Tendsto (fun ν : ℝ => σ / ν) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h3 := (((((tendsto_const_nhds (x := (1 : ℝ))).sub h1).const_mul (k * β)).div_const
    (1 + k * (1 - β))).mul_const (1 - α)).neg.div_const (bigD σ φ α)
  have hfun : (fun ν => psiYi (varpi k β σ ν) σ φ α)
      = fun ν => -(k * β * (1 - σ / ν) / (1 + k * (1 - β)) * (1 - α)) / bigD σ φ α := by
    funext ν
    simp only [psiYi, varpi]
  rw [hfun]
  convert h3 using 2
  rw [sub_zero, mul_one, div_mul_eq_mul_div, neg_div, neg_div, div_div,
    mul_comm (1 + k * (1 - β))]

/-- Galí (2015), p. 38: with `σ = 1`, `φ = 5`, `α = 1/4` (`D = 6`) the `ν → ∞` limit of
`ψ_yi` is `−k_m β/(8(1 + k_m(1 − β)))`. -/
theorem psiYi_limit_calib (k β : ℝ) :
    -(k * β * (1 - 1 / 4)) / (bigD 1 5 (1 / 4) * (1 + k * (1 - β)))
      = -(k * β) / (8 * (1 + k * (1 - β))) := by
  unfold bigD
  by_cases h : 1 + k * (1 - β) = 0
  · simp [h]
  · field_simp
    ring

/-- Galí (2015), p. 38 (`ψ_yi ≃ −k_m/8`): as `β → 1` the calibrated limit
`−k_m β/(8(1 + k_m(1 − β)))` tends to `−k_m/8`. -/
theorem tendsto_calib_beta_one (k : ℝ) :
    Tendsto (fun β : ℝ => -(k * β) / (8 * (1 + k * (1 - β)))) (𝓝 1) (𝓝 (-k / 8)) := by
  have hc : ContinuousAt (fun β : ℝ => -(k * β) / (8 * (1 + k * (1 - β)))) 1 :=
    ((continuousAt_const.mul continuousAt_id).neg).div
      (continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
        (continuousAt_const.sub continuousAt_id)))) (by norm_num)
  simpa using hc.tendsto

/-- Galí (2015), p. 38: the `ν → ∞` limit of `ψ_yi` at `σ = 1`, `φ = 5`, `α = 1/4`, as a
function of `k_m` and `β` (`tendsto_psiYi_nu`). -/
noncomputable def calibLimit (k β : ℝ) : ℝ :=
  -(k * β * (1 - 1 / 4)) / (bigD 1 5 (1 / 4) * (1 + k * (1 - β)))

/-- Galí (2015), p. 38, monetary base (`k_m = 0.3`, `β = 0.99`, `σ = 1`, `φ = 5`,
`α = 1/4`): the limit multiplier lies in `(−0.04, −0.035)` (book: `≃ −0.04`), and a
one-point annual (`0.25` quarterly) rise in `i` moves quarterly output by between
`−0.01` and `−0.009` percent (book: about `0.01` percent). -/
theorem psiYi_limit_km_base :
    -(4 / 100) < calibLimit (3 / 10) (99 / 100) ∧ calibLimit (3 / 10) (99 / 100) < -(35 / 1000) ∧
      -(1 / 100) < calibLimit (3 / 10) (99 / 100) / 4 ∧
      calibLimit (3 / 10) (99 / 100) / 4 < -(9 / 1000) := by
  simp only [calibLimit, bigD]
  norm_num

/-- Galí (2015), p. 38, M2 (`k_m = 3`, `β = 0.99`, `σ = 1`, `φ = 5`, `α = 1/4`): the limit
multiplier lies in `(−0.37, −0.36)` (book: `≃ −0.4`, i.e. `−k_m/8 = −0.375` rounded), and a
one-point annual rise in `i` moves quarterly output by between `−0.1` and `−0.09` percent
(book: `0.1` percent). -/
theorem psiYi_limit_km_m2 :
    -(37 / 100) < calibLimit 3 (99 / 100) ∧ calibLimit 3 (99 / 100) < -(36 / 100) ∧
      -(1 / 10) < calibLimit 3 (99 / 100) / 4 ∧ calibLimit 3 (99 / 100) / 4 < -(9 / 100) := by
  simp only [calibLimit, bigD]
  norm_num

/-! ### Eqs. (44)–(45) -/

/-- Galí (2015), p. 38: `Θ = ϖ(1 − α)/(η D + ϖ(1 − α))`. -/
noncomputable def Theta (ϖ η σ φ α : ℝ) : ℝ := ϖ * (1 - α) / (η * bigD σ φ α + ϖ * (1 - α))

/-- Galí (2015), p. 39: `Λ = η(α + φ)/(η D + ϖ(1 − α))`. -/
noncomputable def Lambda (ϖ η σ φ α : ℝ) : ℝ := η * (α + φ) / (η * bigD σ φ α + ϖ * (1 - α))

/-- Galí (2015), eqs. (44)–(45), p. 38 (the log-linear model, `a = 0`): from (43)
`y = ψ_yi i` and (40) `m − p = y − η i`: `y = Θ (m − p)` and
`i = −η⁻¹ (1 − Θ)(m − p)`. -/
theorem eq44_45 {ϖ η σ φ α y q i : ℝ} (hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0) (hη : η ≠ 0)
    (hD : bigD σ φ α ≠ 0) (h43 : y = psiYi ϖ σ φ α * i) (h40 : q = y - η * i) :
    y = Theta ϖ η σ φ α * q ∧ i = -(1 / η) * (1 - Theta ϖ η σ φ α) * q := by
  have h43' : y * bigD σ φ α = -(ϖ * (1 - α)) * i := by
    rw [h43, psiYi]
    field_simp
  have hi : i * (η * bigD σ φ α + ϖ * (1 - α)) = -(bigD σ φ α * q) := by
    linear_combination bigD σ φ α * h40 + h43'
  have hi' : i = -(bigD σ φ α * q) / (η * bigD σ φ α + ϖ * (1 - α)) := by
    rw [eq_div_iff hK]
    exact hi
  constructor
  · rw [h43, hi', psiYi, Theta]
    field_simp
  · rw [hi', show 1 - Theta ϖ η σ φ α = η * bigD σ φ α / (η * bigD σ φ α + ϖ * (1 - α)) by
      unfold Theta; field_simp; ring]
    field_simp

/-- Galí (2015), p. 38: `Θ ∈ [0, 1)` for `η > 0`, `D > 0`, `ϖ ≥ 0`, `α < 1`. -/
theorem Theta_mem {ϖ η σ φ α : ℝ} (hη : 0 < η) (hD : 0 < bigD σ φ α) (hϖ : 0 ≤ ϖ) (hα : α < 1) :
    0 ≤ Theta ϖ η σ φ α ∧ Theta ϖ η σ φ α < 1 := by
  have h1 : 0 ≤ ϖ * (1 - α) := mul_nonneg hϖ (by linarith)
  have h2 : 0 < η * bigD σ φ α := mul_pos hη hD
  unfold Theta
  exact ⟨div_nonneg h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- Galí (2015), p. 39: `Λ ≥ 0` for `η > 0`, `D > 0`, `ϖ ≥ 0`, `α < 1`, `α + φ ≥ 0`. -/
theorem Lambda_nonneg {ϖ η σ φ α : ℝ} (hη : 0 < η) (hD : 0 < bigD σ φ α) (hϖ : 0 ≤ ϖ)
    (hα : α < 1) (hαφ : 0 ≤ α + φ) : 0 ≤ Lambda ϖ η σ φ α := by
  have h1 : 0 ≤ ϖ * (1 - α) := mul_nonneg hϖ (by linarith)
  have h2 : 0 < η * bigD σ φ α := mul_pos hη hD
  unfold Lambda
  exact div_nonneg (mul_nonneg hη.le hαφ) (by linarith)

/-- Galí (2015), p. 39 (the algebra behind (48)): `η + ϖ(1 − Θ) − σ Θ η = η + ϖ Λ`. -/
theorem coef_identity {ϖ η σ φ α : ℝ} (hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0) :
    η + ϖ * (1 - Theta ϖ η σ φ α) - σ * Theta ϖ η σ φ α * η = η + ϖ * Lambda ϖ η σ φ α := by
  unfold Theta Lambda
  field_simp
  unfold bigD
  ring

/-! ### Eqs. (38), (46)–(47): the Euler equation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (38), p. 35: the marginal-utility ratio entering (5),
`U_c(C', X')/U_c(C, X) = (C'/C)^{−ν}(X'/X)^{ν−σ}`. -/
theorem uc_ratio {ϑ ν σ C X C' X' : ℝ} (hϑ1 : ϑ < 1) (hC : 0 < C) (hX : 0 < X) (hC' : 0 ≤ C')
    (hX' : 0 ≤ X') :
    (1 - ϑ) * X' ^ (ν - σ) * C' ^ (-ν) / ((1 - ϑ) * X ^ (ν - σ) * C ^ (-ν))
      = (C' / C) ^ (-ν) * (X' / X) ^ (ν - σ) := by
  have h1 : (1 : ℝ) - ϑ ≠ 0 := by linarith
  have h2 := (Real.rpow_pos_of_pos hX (ν - σ)).ne'
  have h3 := (Real.rpow_pos_of_pos hC (-ν)).ne'
  rw [Real.div_rpow hC' hC.le, Real.div_rpow hX' hX.le]
  field_simp

/-- Galí (2015), eq. (38), p. 35: the Euler equation at date `t`, node by node,
`Q_t = β E_t[(C_{t+1}/C_t)^{−ν}(X_{t+1}/X_t)^{ν−σ} P_t/P_{t+1}]` (date-`t` values enter as
numbers at the node `ω`). -/
def MIUEuler (β σ ν : ℝ) (Q C X P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω = β * 𝔼.E t (fun ω' => (C (t + 1) ω' / C t ω) ^ (-ν) *
    (X (t + 1) ω' / X t ω) ^ (ν - σ) * (P t ω / P (t + 1) ω')) ω

/-- Galí (2015), eq. (38), p. 35, from eq. (5), p. 19: the Euler equation
`Q_t = β E_t[(U_{c,t+1}/U_{c,t})(P_t/P_{t+1})]` with the marginal utility
`U_c = (1 − ϑ) X^{ν−σ} C^{−ν}` is exactly (38) (positive `C`, `X`). -/
theorem euler5_iff_miuEuler {β σ ν ϑ : ℝ} (hϑ1 : ϑ < 1) {Q C X P : ℕ → Ω → ℝ} {t : ℕ}
    (hC : ∀ ω, 0 < C t ω) (hX : ∀ ω, 0 < X t ω) (hC1 : ∀ ω, 0 ≤ C (t + 1) ω)
    (hX1 : ∀ ω, 0 ≤ X (t + 1) ω) :
    (∀ ω, Q t ω = β * 𝔼.E t (fun ω' =>
      (1 - ϑ) * X (t + 1) ω' ^ (ν - σ) * C (t + 1) ω' ^ (-ν) /
        ((1 - ϑ) * X t ω ^ (ν - σ) * C t ω ^ (-ν)) * (P t ω / P (t + 1) ω')) ω) ↔
      MIUEuler 𝔼 β σ ν Q C X P t := by
  unfold MIUEuler
  refine forall_congr' fun ω => ?_
  have h : (fun ω' => (1 - ϑ) * X (t + 1) ω' ^ (ν - σ) * C (t + 1) ω' ^ (-ν) /
      ((1 - ϑ) * X t ω ^ (ν - σ) * C t ω ^ (-ν)) * (P t ω / P (t + 1) ω'))
      = fun ω' => (C (t + 1) ω' / C t ω) ^ (-ν) * (X (t + 1) ω' / X t ω) ^ (ν - σ) *
        (P t ω / P (t + 1) ω') := by
    funext ω'
    rw [uc_ratio hϑ1 (hC ω) (hX ω) (hC1 ω') (hX1 ω')]
  rw [h]

/-- Galí (2015), p. 35: with `ν = σ` the Euler equation (38) is the separable-case Euler
equation `Q_t = β E_t[(C_{t+1}/C_t)^{−σ} P_t/P_{t+1}]`. -/
theorem miuEuler_nu_eq_sigma (β σ : ℝ) (Q C X P : ℕ → Ω → ℝ) (t : ℕ) :
    MIUEuler 𝔼 β σ σ Q C X P t ↔ ∀ ω, Q t ω = β * 𝔼.E t (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (P t ω / P (t + 1) ω')) ω := by
  simp [MIUEuler]

/-- Galí (2015), p. 39: the Euler moment of (38) in logs,
`E_t[exp(i_t − ρ − ν Δc_{t+1} + (ν − σ) Δx_{t+1} − Δp_{t+1})]` at the node `ω`. -/
noncomputable def miuMoment (σ ν ρ : ℝ) (i c x p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - ν * (c (t + 1) ω' - c t ω)
    + (ν - σ) * (x (t + 1) ω' - x t ω) - (p (t + 1) ω' - p t ω))) ω

/-- Galí (2015), eq. (38), p. 35 (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`,
`X = e^x`, `P = e^p`, the Euler equation holds iff the Euler moment is one at every node. -/
theorem miuEuler_iff_moment (σ ν ρ : ℝ) (i c x p : ℕ → Ω → ℝ) (t : ℕ) :
    MIUEuler 𝔼 (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (x t ω))
        (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, miuMoment 𝔼 σ ν ρ i c x p t ω = 1 := by
  unfold MIUEuler
  refine forall_congr' fun ω => ?_
  set G : Ω → ℝ := fun ω' => (Real.exp (c (t + 1) ω') / Real.exp (c t ω)) ^ (-ν) *
    (Real.exp (x (t + 1) ω') / Real.exp (x t ω)) ^ (ν - σ) *
    (Real.exp (p t ω) / Real.exp (p (t + 1) ω')) with hG
  have hmom : miuMoment 𝔼 σ ν ρ i c x p t ω = Real.exp (i t ω - ρ) * 𝔼.E t G ω := by
    have hfun : (fun ω' => Real.exp (i t ω - ρ - ν * (c (t + 1) ω' - c t ω)
        + (ν - σ) * (x (t + 1) ω' - x t ω) - (p (t + 1) ω' - p t ω)))
        = Real.exp (i t ω - ρ) • G := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hG]
      rw [← Real.exp_sub, ← Real.exp_sub, ← Real.exp_sub, ← Real.exp_mul, ← Real.exp_mul,
        ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [miuMoment, hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hmom]
  have e1 : Real.exp (i t ω - ρ) = Real.exp (i t ω) * Real.exp (-ρ) := by
    rw [← Real.exp_add]
    ring_nf
  have e2 : Real.exp (i t ω) * Real.exp (-i t ω) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [e1]
  constructor
  · intro h
    rw [mul_assoc, ← h, e2]
  · intro h
    calc Real.exp (-i t ω)
        = Real.exp (-i t ω) * (Real.exp (i t ω) * Real.exp (-ρ) * 𝔼.E t G ω) := by
          rw [h, mul_one]
      _ = (Real.exp (i t ω) * Real.exp (-i t ω)) * (Real.exp (-ρ) * 𝔼.E t G ω) := by ring
      _ = Real.exp (-ρ) * 𝔼.E t G ω := by rw [e2, one_mul]

/-- Galí (2015), eq. (46), p. 39, first line (**exact under perfect foresight**): the Euler
equation (38) holds at date `t` iff
`c_t = c_{t+1} − σ⁻¹(i_t − π_{t+1} − (ν − σ)((c_{t+1} − x_{t+1}) − (c_t − x_t)) − ρ)`. -/
theorem pf_miuEuler_iff {σ : ℝ} (hσ : σ ≠ 0) (ν ρ : ℝ) (i c x p : ℕ → Unit → ℝ) (t : ℕ) :
    MIUEuler perfectForesight (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (x t ω))
        (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, c t ω = c (t + 1) ω - σ⁻¹ * (i t ω - (p (t + 1) ω - p t ω)
        - (ν - σ) * ((c (t + 1) ω - x (t + 1) ω) - (c t ω - x t ω)) - ρ) := by
  rw [miuEuler_iff_moment]
  refine forall_congr' fun ω => ?_
  simp only [miuMoment, perfectForesight, LinearMap.id_apply]
  rw [Real.exp_eq_one_iff]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- Galí (2015), ch. 2, App. 2.1, p. 44 (restated from the Chapter 3 project): for a bounded
random variable `Y`, `s ↦ E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. -/
theorem hasDerivAt_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω) (𝔼.E t Y ω) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero]
  have hO : (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
      - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω) =O[𝓝 0]
      fun s : ℝ => s ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (M ^ 2)
    have hcont : Continuous (fun s : ℝ => |s| * M) := by fun_prop
    have hlim : Tendsto (fun s : ℝ => |s| * M) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto 0
      rwa [abs_zero, zero_mul] at this
    filter_upwards [hlim.eventually (ge_mem_nhds one_pos)] with s hs
    have key : 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
        - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω
        = 𝔼.E t (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω') ω := by
      have h1 : (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω')
          = (fun ω' => Real.exp (s * Y ω')) - (fun _ => (1 : ℝ)) - s • Y := by
        funext ω'
        simp
      have h2 : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
        funext ω'
        simp
      rw [h1, h2, map_sub, map_sub, map_smul, 𝔼.const]
      simp
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs]
    apply 𝔼.abs_E_le
    intro ω'
    have hy : |s * Y ω'| ≤ 1 := by
      rw [abs_mul]
      calc |s| * |Y ω'| ≤ |s| * M := mul_le_mul_of_nonneg_left (hY ω') (abs_nonneg s)
        _ ≤ 1 := hs
    have hsq : (s * Y ω') ^ 2 ≤ M ^ 2 * |s ^ 2| := by
      rw [abs_pow, sq_abs, mul_pow, mul_comm]
      have : Y ω' ^ 2 ≤ M ^ 2 := by
        have := hY ω'
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg s)
    exact (Real.abs_exp_sub_one_sub_id_le hy).trans hsq
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Galí (2015), ch. 2, App. 2.1, p. 44 (restated from the Chapter 3 project): for bounded `Y`,
`s ↦ log E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. -/
theorem hasDerivAt_log_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω))
      (𝔼.E t Y ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω = 1 := by
    have : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
      funext ω'
      simp
    rw [this, 𝔼.const]
  have := (hasDerivAt_E_exp 𝔼 hY t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at this
  exact this

/-- Galí (2015), eq. (46), p. 39: the linear expression obtained by linearising the Euler
moment of (38), in deviations from the zero-inflation steady state:
`î_t − ν(E_t ĉ_{t+1} − ĉ_t) + (ν − σ)(E_t x̂_{t+1} − x̂_t) − (E_t p̂_{t+1} − p̂_t)`. -/
noncomputable def linearisedMIUEuler (σ ν : ℝ) (ih ch xh ph : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ih t ω - ν * (𝔼.E t (ch (t + 1)) ω - ch t ω)
    + (ν - σ) * (𝔼.E t (xh (t + 1)) ω - xh t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)

/-- Galí (2015), p. 39: at the zero-inflation steady state (`i = ρ`, constant `c̄, x̄, p̄`) the
Euler moment of (38) equals one. -/
theorem miuMoment_family_zero (σ ν ρ cbar xbar pbar : ℝ) (ih ch xh ph : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    miuMoment 𝔼 σ ν ρ (fun t ω => ρ + 0 * ih t ω) (fun t ω => cbar + 0 * ch t ω)
      (fun t ω => xbar + 0 * xh t ω) (fun t ω => pbar + 0 * ph t ω) t ω = 1 := by
  simp only [miuMoment, zero_mul, add_zero, sub_self, mul_zero, Real.exp_zero]
  rw [𝔼.const]

/-- Galí (2015), eq. (46), p. 39, as an **exact derivative**: along the family of stochastic
paths `i = ρ + s î`, `c = c̄ + s ĉ`, `x = x̄ + s x̂`, `p = p̄ + s p̂` around the zero-inflation
steady state, with bounded deviations, `s ↦ log E_t[exp(i_t − ρ − νΔc + (ν − σ)Δx − Δp)](ω)`
has derivative at `s = 0` equal to `linearisedMIUEuler σ ν î ĉ x̂ p̂ t ω`. -/
theorem hasDerivAt_log_miuMoment_family (σ ν ρ cbar xbar pbar : ℝ) {ih ch xh ph : ℕ → Ω → ℝ}
    (hc : BoundedProc ch) (hx : BoundedProc xh) (hp : BoundedProc ph) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (miuMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
        (fun t ω => cbar + s * ch t ω) (fun t ω => xbar + s * xh t ω)
        (fun t ω => pbar + s * ph t ω) t ω))
      (linearisedMIUEuler 𝔼 σ ν ih ch xh ph t ω) 0 := by
  obtain ⟨Mc, hMc⟩ := hc
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨Mp, hMp⟩ := hp
  set a : ℝ := ih t ω + ν * ch t ω - (ν - σ) * xh t ω + ph t ω with ha
  set Y : Ω → ℝ := fun ω' => a + (-ν * ch (t + 1) ω' + (ν - σ) * xh (t + 1) ω' - ph (t + 1) ω')
    with hY
  have hbd : ∀ ω', |Y ω'| ≤ |a| + |ν| * Mc + |ν - σ| * Mx + Mp := by
    intro ω'
    have h1 := abs_le.1 (show |ν * ch (t + 1) ω'| ≤ |ν| * Mc by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMc _ _) (abs_nonneg ν))
    have h2 := abs_le.1 (show |(ν - σ) * xh (t + 1) ω'| ≤ |ν - σ| * Mx by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMx _ _) (abs_nonneg _))
    have h3 := abs_le.1 (hMp (t + 1) ω')
    have h4 := abs_le.1 (le_refl |a|)
    rw [abs_le]
    simp only [hY]
    constructor <;> linarith
  have hfam : ∀ s : ℝ, miuMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
      (fun t ω => cbar + s * ch t ω) (fun t ω => xbar + s * xh t ω)
      (fun t ω => pbar + s * ph t ω) t ω = 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω := by
    intro s
    unfold miuMoment
    refine congrArg (fun z => 𝔼.E t z ω) (funext fun ω' => ?_)
    congr 1
    simp only [hY, ha]
    ring
  simp_rw [hfam]
  have hval : 𝔼.E t Y ω = linearisedMIUEuler 𝔼 σ ν ih ch xh ph t ω := by
    have hfun : Y = (fun _ => a) + ((-ν) • ch (t + 1) + (ν - σ) • xh (t + 1) - ph (t + 1)) := by
      funext ω'
      simp [hY, smul_eq_mul]
    rw [hfun, map_add, 𝔼.const, map_sub, map_add, map_smul, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, linearisedMIUEuler, ha]
    ring
  rw [← hval]
  exact hasDerivAt_log_E_exp 𝔼 hbd t ω

/-- Galí (2015), eq. (46), p. 39, first line, as a model equation:
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − (ν − σ)(E_t g_{t+1} − g_t) − ρ)` with
`g = c − x`. -/
def EulerGap (σ ν ρ : ℝ) (c g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))
    - (ν - σ) • (𝔼.E t (g (t + 1)) - g t) - fun _ => ρ)

/-- Galí (2015), eqs. (46)–(47), p. 39, last line, as a model equation:
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ϖ E_t Δi_{t+1} − ρ)`. -/
def EulerLinear (σ ϖ ρ : ℝ) (c i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))
    - ϖ • (𝔼.E t (i (t + 1)) - i t) - fun _ => ρ)

/-- Galí (2015), eq. (46), p. 39 (**the first-order condition is exactly (46), first line**):
for `σ ≠ 0`, an adapted price level `p̂` and `π_{t+1} = p̂_{t+1} − p̂_t`, the linearised Euler
expression vanishes at every date iff `EulerGap` holds for `ĉ`, `ĝ = ĉ − x̂`, `i = ρ + î`. -/
theorem linearisedMIUEuler_eq_zero_iff {σ ν ρ : ℝ} (hσ : σ ≠ 0) {ih ch xh ph infl : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted ph) (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) :
    (∀ t, linearisedMIUEuler 𝔼 σ ν ih ch xh ph t = 0) ↔
      EulerGap 𝔼 σ ν ρ ch (fun t => ch t - xh t) (fun t => (fun _ => ρ) + ih t) infl := by
  unfold EulerGap
  refine forall_congr' fun t => ?_
  rw [hinfl, map_sub, hp t, map_sub]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [linearisedMIUEuler, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at e ⊢
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [linearisedMIUEuler, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at e ⊢
    field_simp at e
    linear_combination e

/-- Galí (2015), eq. (46), p. 39 (the log-linear model): if `c − x = κ i + const` at every date
(from `c − x = χ(c − (m − p))` and (40), `κ = χ η`), then the first line of (46) is
equivalent to its last line with `ϖ = (ν − σ) κ`. -/
theorem eulerGap_iff_eulerLinear {σ ν ρ κ k : ℝ} {c g i infl : ℕ → Ω → ℝ}
    (hg : ∀ t, g t = κ • i t + fun _ => k) :
    EulerGap 𝔼 σ ν ρ c g i infl ↔ EulerLinear 𝔼 σ ((ν - σ) * κ) ρ c i infl := by
  unfold EulerGap EulerLinear
  refine forall_congr' fun t => ?_
  have h : (ν - σ) • (𝔼.E t (g (t + 1)) - g t) = ((ν - σ) * κ) • (𝔼.E t (i (t + 1)) - i t) := by
    rw [hg (t + 1), hg t, map_add, map_smul, 𝔼.const, mul_smul, smul_sub κ]
    congr 1
    abel
  rw [h]

/-- Galí (2015), eq. (47), p. 39: with goods-market clearing `y = c`, (46) in consumption is
(47) in output. -/
theorem eq47_of_clearing {σ ϖ ρ : ℝ} {c y i infl : ℕ → Ω → ℝ} (hyc : y = c) :
    EulerLinear 𝔼 σ ϖ ρ y i infl ↔ EulerLinear 𝔼 σ ϖ ρ c i infl := by
  rw [hyc]

/-! ### Eq. (48): the price level -/

/-- Galí (2015), p. 39 (the algebra behind (48)): with `y = Θ q`, `i = −η⁻¹(1 − Θ) q`
(`q = m − p`), and `Δ = E_t m_{t+1} − m_t`, `π̄ = E_t p_{t+1} − p_t = Δ − (E_t q_{t+1} − q_t)`,
the Euler equation (47) (deviations) at a node is equivalent to
`(1 − Θ + B) q_t = B E_t q_{t+1} − η Δ`, `B = η + ϖ(1 − Θ) − σ Θ η`. -/
theorem real_balance_eq_iff_real {σ η ϖ Θ qt Eq Em mt : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) :
    Θ * qt = Θ * Eq - σ⁻¹ * (-(1 / η) * (1 - Θ) * qt - ((Em - Eq) - (mt - qt))
      - ϖ * (-(1 / η) * (1 - Θ) * Eq - -(1 / η) * (1 - Θ) * qt)) ↔
    (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)) * qt
      = (η + ϖ * (1 - Θ) - σ * Θ * η) * Eq - η * (Em - mt) := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)) * qt)]
  have key : Θ * qt - (Θ * Eq - σ⁻¹ * (-(1 / η) * (1 - Θ) * qt - ((Em - Eq) - (mt - qt))
      - ϖ * (-(1 / η) * (1 - Θ) * Eq - -(1 / η) * (1 - Θ) * qt)))
      = -(σ * η)⁻¹ * ((1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)) * qt
        - ((η + ϖ * (1 - Θ) - σ * Θ * η) * Eq - η * (Em - mt))) := by
    field_simp
    ring
  rw [key, neg_mul, neg_eq_zero, mul_eq_zero, or_iff_right (inv_ne_zero (mul_ne_zero hσ hη))]

/-- Galí (2015), p. 39 (the algebra behind (48)): for `d ≠ 0`, `d q = B E − η Δ` iff
`q = (B/d) E − (η/d) Δ`. -/
theorem solve_forward {d B q E η Δ : ℝ} (hd : d ≠ 0) :
    d * q = B * E - η * Δ ↔ q = B / d * E + -(η / d) * Δ := by
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- Galí (2015), p. 39 (the algebra behind (48)): given (44), (45) with `q = m − p`,
`π_{t+1} = p_{t+1} − p_t` and an adapted `p`, the Euler equation (47) in deviations holds
iff real balances satisfy `q_t = a E_t q_{t+1} + u_t` with
`a = B/(1 − Θ + B)` and `u_t = −η/(1 − Θ + B) (E_t m_{t+1} − m_t)`. -/
theorem real_balance_eq_iff {σ η ϖ Θ : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    (hB : 1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η) ≠ 0) {m p y i infl : ℕ → Ω → ℝ}
    (hpA : 𝔼.Adapted p) (h44 : ∀ t, y t = Θ • (m t - p t))
    (h45 : ∀ t, i t = (-(1 / η) * (1 - Θ)) • (m t - p t))
    (hπ : ∀ t, infl (t + 1) = p (t + 1) - p t) :
    EulerLinear 𝔼 σ ϖ 0 y i infl ↔ ∀ t, (fun t => m t - p t) t =
      ((η + ϖ * (1 - Θ) - σ * Θ * η) / (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η))) •
        𝔼.E t ((fun t => m t - p t) (t + 1)) +
      (-(η / (1 - Θ + (η + ϖ * (1 - Θ) - σ * Θ * η)))) • (𝔼.E t (m (t + 1)) - m t) := by
  unfold EulerLinear
  refine forall_congr' fun t => ?_
  rw [h44 t, h44 (t + 1), h45 t, h45 (t + 1), hπ t]
  simp only [map_sub, map_smul, hpA t, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, sub_zero]
  have hiff := real_balance_eq_iff_real (ϖ := ϖ) (Θ := Θ) (qt := m t ω - p t ω)
    (Eq := 𝔼.E t (m (t + 1)) ω - 𝔼.E t (p (t + 1)) ω) (Em := 𝔼.E t (m (t + 1)) ω)
    (mt := m t ω) hσ hη
  have e : 𝔼.E t (p (t + 1)) ω - p t ω = (𝔼.E t (m (t + 1)) ω
      - (𝔼.E t (m (t + 1)) ω - 𝔼.E t (p (t + 1)) ω)) - (m t ω - (m t ω - p t ω)) := by ring
  rw [e, hiff]
  exact solve_forward hB

/-- Galí (2015), (48) p. 39: the forward series of real balances is adapted:
`E_t` of the date-`t` forward series is itself (uses `E_tsum`). -/
theorem forwardSeries_adapted {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  funext ω
  have hb : ∀ k ω', |a ^ k * 𝔼.E t (u (t + k)) ω'| ≤ a ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω') (pow_nonneg ha0 k)
  change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω') ω = _
  rw [𝔼.E_tsum ha0 ha1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (a ^ k • 𝔼.E t (u (t + k))) ω = _
  rw [map_smul, ExpectationSystem.E_E_self, Pi.smul_apply, smul_eq_mul]

/-- Galí (2015), (48) p. 39: the forcing term `u_t = c (E_t m_{t+1} − m_t)` of the
real-balance equation is adapted and bounded when money growth is bounded. -/
theorem forcing_bounded_adapted {M c : ℝ} {m : ℕ → Ω → ℝ} (hmA : 𝔼.Adapted m)
    (hΔ : ∀ t ω, |m (t + 1) ω - m t ω| ≤ M) :
    (∀ t ω, |(c • (𝔼.E t (m (t + 1)) - m t)) ω| ≤ |c| * M) ∧
      𝔼.Adapted (fun t => c • (𝔼.E t (m (t + 1)) - m t)) := by
  have hE : ∀ t, 𝔼.E t (m (t + 1)) - m t = 𝔼.E t (m (t + 1) - m t) := by
    intro t
    rw [map_sub, hmA t]
  constructor
  · intro t ω
    rw [hE t, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => hΔ t ω') t ω) (abs_nonneg c)
  · intro t
    simp only
    rw [hE t, map_smul, ExpectationSystem.E_E_self]

/-- Galí (2015), (48) p. 39: the forward series of the forcing term, rewritten with expected
money growth: `∑ aᵏ E_t u_{t+k} = c ∑ aᵏ E_t Δm_{t+k+1}`. -/
theorem forwardSeries_money (a c : ℝ) {m : ℕ → Ω → ℝ} (hmA : 𝔼.Adapted m) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun t => c • (𝔼.E t (m (t + 1)) - m t)) t ω
      = c * ∑' k, a ^ k * 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') ω := by
  unfold ExpectationSystem.forwardSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h : 𝔼.E t (c • (𝔼.E (t + k) (m (t + k + 1)) - m (t + k)))
      = c • 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') := by
    rw [map_smul, map_sub, 𝔼.tower (Nat.le_add_right t k), ← hmA (t + k),
      𝔼.tower (Nat.le_add_right t k), hmA (t + k), ← map_sub]
    rfl
  rw [h, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (48), p. 39 (**uniqueness**): in the log-linear model (44), (45), (47)
(deviations, `a = 0`) with `σ, η > 0`, `D > 0`, `ϖ ≥ 0`, `α < 1`, `α + φ ≥ 0`, adapted money
`m` with bounded growth, every adapted price level with bounded real balances `m − p` is
`p_t = m_t + η/(η + ϖΛ) ∑_{k≥1} ((η + ϖΛ)/(1 − Θ + η + ϖΛ))ᵏ E_t Δm_{t+k}`
(the sum written with index `k + 1`, `k ≥ 0`). -/
theorem price_level_48 {σ η ϖ φ α M : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hD : 0 < bigD σ φ α)
    (hϖ : 0 ≤ ϖ) (hα : α < 1) (hαφ : 0 ≤ α + φ) {m p y i infl : ℕ → Ω → ℝ}
    (hmA : 𝔼.Adapted m) (hpA : 𝔼.Adapted p) (hΔ : ∀ t ω, |m (t + 1) ω - m t ω| ≤ M)
    (h44 : ∀ t, y t = Theta ϖ η σ φ α • (m t - p t))
    (h45 : ∀ t, i t = (-(1 / η) * (1 - Theta ϖ η σ φ α)) • (m t - p t))
    (hπ : ∀ t, infl (t + 1) = p (t + 1) - p t) (h47 : EulerLinear 𝔼 σ ϖ 0 y i infl)
    (hqb : BoundedProc (fun t => m t - p t)) (t : ℕ) (ω : Ω) :
    p t ω = m t ω + η / (η + ϖ * Lambda ϖ η σ φ α) * ∑' k,
      ((η + ϖ * Lambda ϖ η σ φ α) / (1 - Theta ϖ η σ φ α + (η + ϖ * Lambda ϖ η σ φ α))) ^ (k + 1)
        * 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') ω := by
  set Θ := Theta ϖ η σ φ α with hΘ
  set Λ := Lambda ϖ η σ φ α with hΛ
  have hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0 := by
    have := mul_pos hη hD
    have := mul_nonneg hϖ (show (0 : ℝ) ≤ 1 - α by linarith)
    linarith
  have hTh := Theta_mem hη hD hϖ hα
  have hL : 0 ≤ Λ := Lambda_nonneg hη hD hϖ hα hαφ
  have hBid := coef_identity (σ := σ) (φ := φ) hK
  set B := η + ϖ * Λ with hBdef
  have hB0 : 0 < B := by have := mul_nonneg hϖ hL; linarith
  have hden : 0 < 1 - Θ + B := by linarith [hTh.2]
  have hr := (real_balance_eq_iff 𝔼 hσ.ne' hη.ne' (by rw [hBid]; exact hden.ne') hpA
    h44 h45 hπ).1 h47
  rw [hBid] at hr
  set a := B / (1 - Θ + B) with ha
  have ha0 : 0 ≤ a := div_nonneg hB0.le hden.le
  have ha1 : a < 1 := (div_lt_one hden).2 (by linarith [hTh.2])
  obtain ⟨hub, huA⟩ := forcing_bounded_adapted 𝔼 (c := -(η / (1 - Θ + B))) hmA hΔ
  have hq := 𝔼.eq_forwardSeries ha0 ha1 hub huA hr hqb
  have hqt := congrFun (congrFun hq t) ω
  simp only [Pi.sub_apply] at hqt
  rw [forwardSeries_money 𝔼 a _ hmA t ω] at hqt
  have hp : p t ω = m t ω + η / (1 - Θ + B) *
      ∑' k, a ^ k * 𝔼.E t (fun ω' => m (t + k + 1) ω' - m (t + k) ω') ω := by
    linarith
  rw [hp, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [pow_succ, ha]
  field_simp

/-- Galí (2015), eq. (48), p. 39 (**existence**): under the hypotheses of `price_level_48`
the price level `p_t = m_t − q_t`, with `q` the forward series of the real-balance equation,
is adapted, has bounded real balances, and with `y`, `i`, `π` from (44), (45) satisfies the
Euler equation (47); it is therefore the unique such equilibrium. -/
theorem price_level_48_exists {σ η ϖ φ α M : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (hD : 0 < bigD σ φ α) (hϖ : 0 ≤ ϖ) (hα : α < 1) (hαφ : 0 ≤ α + φ) {m : ℕ → Ω → ℝ}
    (hmA : 𝔼.Adapted m) (hΔ : ∀ t ω, |m (t + 1) ω - m t ω| ≤ M) :
    ∃ p : ℕ → Ω → ℝ, 𝔼.Adapted p ∧ BoundedProc (fun t => m t - p t) ∧
      EulerLinear 𝔼 σ ϖ 0 (fun t => Theta ϖ η σ φ α • (m t - p t))
        (fun t => (-(1 / η) * (1 - Theta ϖ η σ φ α)) • (m t - p t))
        (fun t => match t with
          | 0 => 0
          | s + 1 => p (s + 1) - p s) := by
  set Θ := Theta ϖ η σ φ α with hΘ
  set Λ := Lambda ϖ η σ φ α with hΛ
  have hK : η * bigD σ φ α + ϖ * (1 - α) ≠ 0 := by
    have := mul_pos hη hD
    have := mul_nonneg hϖ (show (0 : ℝ) ≤ 1 - α by linarith)
    linarith
  have hTh := Theta_mem hη hD hϖ hα
  have hL : 0 ≤ Λ := Lambda_nonneg hη hD hϖ hα hαφ
  have hBid := coef_identity (σ := σ) (φ := φ) hK
  have hB0 : 0 < η + ϖ * Λ := by have := mul_nonneg hϖ hL; linarith
  have hden : 0 < 1 - Θ + (η + ϖ * Λ) := by linarith [hTh.2]
  set a := (η + ϖ * Λ) / (1 - Θ + (η + ϖ * Λ)) with ha
  have ha0 : 0 ≤ a := div_nonneg hB0.le hden.le
  have ha1 : a < 1 := (div_lt_one hden).2 (by linarith [hTh.2])
  obtain ⟨hub, huA⟩ := forcing_bounded_adapted 𝔼 (c := -(η / (1 - Θ + (η + ϖ * Λ)))) hmA hΔ
  set u := fun t => (-(η / (1 - Θ + (η + ϖ * Λ)))) • (𝔼.E t (m (t + 1)) - m t) with hu
  set q := 𝔼.forwardSeries a u with hq
  have hqA : 𝔼.Adapted q := forwardSeries_adapted 𝔼 ha0 ha1 hub
  refine ⟨fun t => m t - q t, ?_, ?_, ?_⟩
  · intro t
    simp only
    rw [map_sub, hmA t, hqA t]
  · have hb := 𝔼.forwardSeries_bounded ha0 ha1 hub
    have e : (fun t => m t - (fun t => m t - q t) t) = q := by
      funext t
      simp
    rw [e]
    exact hb
  · have hpA : 𝔼.Adapted (fun t => m t - q t) := by
      intro t
      simp only
      rw [map_sub, hmA t, hqA t]
    refine (real_balance_eq_iff 𝔼 hσ.ne' hη.ne' (by rw [hBid]; exact hden.ne') hpA
      (fun t => rfl) (fun t => rfl) (fun t => rfl)).2 ?_
    rw [hBid]
    intro t
    have hs := 𝔼.forwardSeries_solves ha0 ha1 hub huA t
    have e : ∀ s, m s - (m s - q s) = q s := fun s => sub_sub_cancel _ _
    simp only [e]
    exact hs

/-! ### The real wage after a monetary shock (pp. 39–40) -/

/-- Galí (2015), pp. 39–40: with technology unchanged, two equilibria (e.g. before and after a
monetary shock) on the labour demand schedule `ω = a − α n + log(1 − α)` with
`y = a + (1 − α) n` satisfy `ω₁ − ω₂ = −(α/(1 − α))(y₁ − y₂)`, so
`(ω₁ − ω₂)(y₁ − y₂) ≤ 0`: the real wage is (weakly) countercyclical. -/
theorem real_wage_countercyclical {α a n₁ n₂ y₁ y₂ w₁ w₂ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hd₁ : w₁ = a - α * n₁ + Real.log (1 - α)) (hd₂ : w₂ = a - α * n₂ + Real.log (1 - α))
    (hy₁ : y₁ = a + (1 - α) * n₁) (hy₂ : y₂ = a + (1 - α) * n₂) :
    w₁ - w₂ = -(α / (1 - α)) * (y₁ - y₂) ∧ (w₁ - w₂) * (y₁ - y₂) ≤ 0 := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have e : w₁ - w₂ = -(α / (1 - α)) * (y₁ - y₂) := by
    rw [hd₁, hd₂, hy₁, hy₂]
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 ≤ α / (1 - α) := div_nonneg hα0 (by linarith)
  nlinarith [sq_nonneg (y₁ - y₂)]

/-- Galí (2015), pp. 39–40: for `0 < α < 1`, a monetary shock that changes output
moves the real wage in the opposite direction: `(ω₁ − ω₂)(y₁ − y₂) < 0`. -/
theorem real_wage_strictly_countercyclical {α a n₁ n₂ y₁ y₂ w₁ w₂ : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hd₁ : w₁ = a - α * n₁ + Real.log (1 - α))
    (hd₂ : w₂ = a - α * n₂ + Real.log (1 - α)) (hy₁ : y₁ = a + (1 - α) * n₁)
    (hy₂ : y₂ = a + (1 - α) * n₂) (hy : y₁ ≠ y₂) : (w₁ - w₂) * (y₁ - y₂) < 0 := by
  obtain ⟨e, -⟩ := real_wage_countercyclical hα0.le hα1 hd₁ hd₂ hy₁ hy₂
  rw [e]
  have : 0 < α / (1 - α) := div_pos hα0 (by linarith)
  have : 0 < (y₁ - y₂) ^ 2 := by
    have : y₁ - y₂ ≠ 0 := sub_ne_zero.2 hy
    positivity
  nlinarith

/-- Galí (2015), pp. 39–40 (**the claim needs `α > 0`**): with `α = 0` the labour demand
schedule is flat and the real wage does not move at all after a monetary shock. -/
theorem real_wage_acyclical_of_alpha_zero {a n₁ n₂ w₁ w₂ : ℝ}
    (hd₁ : w₁ = a - 0 * n₁ + Real.log (1 - 0)) (hd₂ : w₂ = a - 0 * n₂ + Real.log (1 - 0)) :
    w₁ = w₂ := by
  rw [hd₁, hd₂]
  ring

end Gali.ClassicalMonetaryModel.MIUNonseparable

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal monetary policy with money in the utility function: the Friedman rule

Galí (2015), Chapter 2, §2.5.3 (pp. 40–42), with fn. 13.

## The planner

The planner solves the static problem `max U(C, M/P, N)` subject to `C = A N^{1−α}` (p. 40).

* `planner_foc_necessary`: for a **general** differentiable `U` (derivative `L`, so
  `U_c = L(1,0,0)`, `U_m = L(0,1,0)`, `U_n = L(0,0,1)`), an optimum with `N, M/P > 0`
  satisfies (49) `−U_n = (1 − α) A N^{−α} U_c` and (50) `U_m = 0`; `planner_foc_ratio` is
  (49) in the printed ratio form.
* `planner_optimum_iff`: for an additively separable utility `u(C) + v(m) − h(N)` with `u, v`
  concave, `u' ≥ 0` and `h` convex, (49)–(50) are **necessary and sufficient**.
* `no_planner_optimum_isoelastic`: with the book's own isoelastic utility of real balances
  `U_m > 0` everywhere, so (50) never holds: efficiency needs a satiation level.

## Decentralisation and the Friedman rule

* `decentralised_49`: (49) holds in any decentralised equilibrium ((4) with (14)), whatever
  the policy.
* `decentralised_efficient_iff`: given (33), `U_m = 0` at every date iff `i_t = 0` at every
  date (the Friedman rule); `decentralised_optimal_iff_friedman`: with the separable utility
  the decentralised allocation solves the planner's problem iff `i = 0`.
* `friedman_steady_state_inflation`: under the Friedman rule the steady state has `π = −ρ`
  (and `Π = β`), deflation for `ρ > 0`.

## Indeterminacy under `i = 0` (p. 41)

* `friedman_euler_iff`, `friedman_equilibrium_iff`: with `i ≡ 0`, (43) and (47) hold iff
  `π_{t+1} = −ρ − σ ψ_ya E_t Δa_{t+1} + ξ_{t+1}` for a martingale-difference sequence `ξ`.
* `friedman_indeterminate`: next to every equilibrium there is a different one (initial
  inflation, hence the price level, is free); `friedman_sunspot_coin`: under genuine
  uncertainty (two coin flips) a non-degenerate sunspot `ξ` gives a different equilibrium.

## Fn. 13 (and exercise 2.6): `î_t = φ_π π̂_t` in the MIU model

* `ruleSystem_iff`: the system reduces to `(1 + φ_π s) E_t π_{t+1} = φ_π (1 + s) π_t + g_t`,
  `s = ϖ + σ ψ_yi = ϖ(φ + α)/D ≥ 0` (`s_eq`).
* `fn13_unique`, `fn13_exists` (`φ_π > 1`: exactly one bounded solution) and
  `fn13_not_unique` (`0 ≤ φ_π ≤ 1`: a second bounded solution next to any solution).

## The rule `i_t = φ (r_{t−1} + π_t)` (p. 42)

In the **log-linear** model (Fisher equation (22), survey item C2-5):
`lagged_rule_unique` (`φ > 1`: every bounded solution has `i ≡ 0`, `π_t = −r_{t−1}`),
`lagged_rule_exists`, and `inflation_rule_implies_zero_rate`.
-/

namespace Gali.ClassicalMonetaryModel.FriedmanRule

open Filter Topology

/-! ### The planner's problem -/

/-- Galí (2015), eqs. (49)–(50), p. 40 (**necessity, general utility**): if `(N, m)` with
`N, m > 0` maximises `U(A N'^{1−α}, m', N')` over `N', m' > 0` and `U` is differentiable at
the optimum with derivative `L`, then `−U_n = (1 − α) A N^{−α} U_c` and `U_m = 0`. -/
theorem planner_foc_necessary {U : ℝ × ℝ × ℝ → ℝ} {L : ℝ × ℝ × ℝ →L[ℝ] ℝ} {A α N m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hU : HasFDerivAt U L (A * N ^ (1 - α), m, N))
    (hopt : ∀ N' m', 0 < N' → 0 < m' →
      U (A * N' ^ (1 - α), m', N') ≤ U (A * N ^ (1 - α), m, N)) :
    -L (0, 0, 1) = (1 - α) * A * N ^ (-α) * L (1, 0, 0) ∧ L (0, 1, 0) = 0 := by
  constructor
  · have hc : HasDerivAt (fun N' : ℝ => (A * N' ^ (1 - α), m, N'))
        ((1 - α) * A * N ^ (-α), 0, 1) N := by
      have h1 := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A
      have h2 := (hasDerivAt_const N m).prodMk (hasDerivAt_id N)
      refine (h1.prodMk h2).congr_deriv ?_
      rw [show (1 : ℝ) - α - 1 = -α by ring]
      ext <;> simp
      ring
    have hloc : IsLocalMax (fun N' : ℝ => U (A * N' ^ (1 - α), m, N')) N := by
      filter_upwards [eventually_gt_nhds hN] with N' hN'
      exact hopt N' m hN' hm
    have h0 := hloc.hasDerivAt_eq_zero (hU.comp_hasDerivAt N hc)
    have hv : (((1 - α) * A * N ^ (-α), 0, 1) : ℝ × ℝ × ℝ)
        = ((1 - α) * A * N ^ (-α)) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hv, map_add, map_smul, smul_eq_mul] at h0
    linarith
  · have hc : HasDerivAt (fun m' : ℝ => (A * N ^ (1 - α), m', N)) (0, 1, 0) m :=
      (hasDerivAt_const m _).prodMk ((hasDerivAt_id m).prodMk (hasDerivAt_const m N))
    have hloc : IsLocalMax (fun m' : ℝ => U (A * N ^ (1 - α), m', N)) m := by
      filter_upwards [eventually_gt_nhds hm] with m' hm'
      exact hopt N m' hN hm'
    exact hloc.hasDerivAt_eq_zero (hU.comp_hasDerivAt m hc)

/-- Galí (2015), eq. (49), p. 40, ratio form: with `U_c ≠ 0`,
`−U_n/U_c = (1 − α) A N^{−α}`. -/
theorem planner_foc_ratio {Uc Un A α N : ℝ} (hUc : Uc ≠ 0)
    (h : -Un = (1 - α) * A * N ^ (-α) * Uc) : -Un / Uc = (1 - α) * A * N ^ (-α) := by
  rw [h, mul_div_assoc, div_self hUc, mul_one]

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangents at positive points (Galí (2015), p. 40: concavity of the planner's problem). -/
theorem tangent_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z) (hanti : AntitoneOn f' (Set.Ioi 0)) :
    f y ≤ f x + f' x * (y - x) := by
  refine MIUSeparable.le_tangent hx hy.le (fun z hz => ?_) hd hanti
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hd z hz0).continuousAt.continuousWithinAt

/-- Galí (2015), p. 40: the technology `A N^{1−α}` (`A > 0`, `0 ≤ α < 1`) is concave:
`A N'^{1−α} ≤ A N^{1−α} + (1 − α) A N^{−α} (N' − N)` for `N, N' > 0`. -/
theorem production_le_tangent {A α N N' : ℝ} (hA : 0 < A) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hN : 0 < N) (hN' : 0 < N') :
    A * N' ^ (1 - α) ≤ A * N ^ (1 - α) + (1 - α) * A * N ^ (-α) * (N' - N) := by
  have h := tangent_of_deriv (f := fun z => A * z ^ (1 - α))
    (f' := fun z => (1 - α) * A * z ^ (-α)) hN hN' (fun z hz => ?_) ?_
  · simpa using h
  · refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hz.ne')).const_mul A).congr_deriv ?_
    rw [show (1 : ℝ) - α - 1 = -α by ring]
    ring
  · intro a ha b _ hab
    have h1 : (0 : ℝ) ≤ (1 - α) * A := mul_nonneg (by linarith) hA.le
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hab (by linarith)) h1

/-- Galí (2015), eqs. (49)–(50), p. 40 (**necessary and sufficient**, separable utility
`u(C) + v(m) − h(N)`): with `u`, `v` differentiable and concave on `(0, ∞)`, `u'(C) ≥ 0`,
`h` differentiable and convex on `(0, ∞)`, `A > 0`, `0 ≤ α < 1`, the point `(N, m)` maximises
`u(A N'^{1−α}) + v(m') − h(N')` over `N', m' > 0` iff
`h'(N) = (1 − α) A N^{−α} u'(C)` (eq. (49)) and `v'(m) = 0` (eq. (50)). -/
theorem planner_optimum_iff {u v h u' v' h' : ℝ → ℝ} {A α N m : ℝ} (hA : 0 < A)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hN : 0 < N) (hm : 0 < m)
    (hu : ∀ z, 0 < z → HasDerivAt u (u' z) z) (hu_anti : AntitoneOn u' (Set.Ioi 0))
    (hu_pos : 0 ≤ u' (A * N ^ (1 - α)))
    (hv : ∀ z, 0 < z → HasDerivAt v (v' z) z) (hv_anti : AntitoneOn v' (Set.Ioi 0))
    (hh : ∀ z, 0 < z → HasDerivAt h (h' z) z) (hh_mono : MonotoneOn h' (Set.Ioi 0)) :
    (∀ N' m', 0 < N' → 0 < m' →
      u (A * N' ^ (1 - α)) + v m' - h N' ≤ u (A * N ^ (1 - α)) + v m - h N) ↔
      (h' N = (1 - α) * A * N ^ (-α) * u' (A * N ^ (1 - α)) ∧ v' m = 0) := by
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  constructor
  · intro hopt
    constructor
    · have hd1 : HasDerivAt (fun N' : ℝ => A * N' ^ (1 - α)) ((1 - α) * A * N ^ (-α)) N := by
        refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).congr_deriv
          ?_
        rw [show (1 : ℝ) - α - 1 = -α by ring]
        ring
      have hg : HasDerivAt (fun N' => u (A * N' ^ (1 - α)) + v m - h N')
          (u' (A * N ^ (1 - α)) * ((1 - α) * A * N ^ (-α)) - h' N) N :=
        HasDerivAt.sub (((hu _ hC).comp N hd1).add_const (v m)) (hh N hN)
      have hloc : IsLocalMax (fun N' => u (A * N' ^ (1 - α)) + v m - h N') N := by
        filter_upwards [eventually_gt_nhds hN] with N' hN'
        exact hopt N' m hN' hm
      have h0 := hloc.hasDerivAt_eq_zero hg
      linarith
    · have hg : HasDerivAt (fun m' => u (A * N ^ (1 - α)) + v m' - h N) (v' m) m := by
        have := ((hv m hm).const_add (u (A * N ^ (1 - α)))).sub_const (h N)
        exact this
      have hloc : IsLocalMax (fun m' => u (A * N ^ (1 - α)) + v m' - h N) m := by
        filter_upwards [eventually_gt_nhds hm] with m' hm'
        exact hopt N m' hN hm'
      exact hloc.hasDerivAt_eq_zero hg
  · rintro ⟨h49, h50⟩ N' m' hN' hm'
    have hC' : 0 < A * N' ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN' _)
    have t1 := tangent_of_deriv hC hC' hu hu_anti
    have t2 := tangent_of_deriv hm hm' hv hv_anti
    have t3 := tangent_of_deriv (f := fun z => -h z) (f' := fun z => -h' z) hN hN'
      (fun z hz => (hh z hz).neg) (fun a ha b hb hab => neg_le_neg (hh_mono ha hb hab))
    have tp := production_le_tangent hA hα0 hα1 hN hN'
    rw [h50, zero_mul, add_zero] at t2
    have k := mul_le_mul_of_nonneg_left (sub_le_sub_right tp (A * N ^ (1 - α))) hu_pos
    have e : u' (A * N ^ (1 - α)) * (A * N ^ (1 - α) + (1 - α) * A * N ^ (-α) * (N' - N)
        - A * N ^ (1 - α)) = h' N * (N' - N) := by
      rw [h49]
      ring
    linarith

/-- Galí (2015), p. 40 (**(50) needs satiation**): with the isoelastic utility of real
balances of §2.5.1, `v = ((M/P)^{1−ν} − 1)/(1 − ν)` (`ν > 0`), `U_m = m^{−ν} > 0` everywhere,
so (50) never holds and the planner's problem has no solution: no `(N, m)` with `N, m > 0`
maximises `u(A N'^{1−α}) + v(m') − h(N')`. -/
theorem no_planner_optimum_isoelastic {u h : ℝ → ℝ} {ν A α N m : ℝ} (hN : 0 < N) (hm : 0 < m) :
    ¬ ∀ N' m', 0 < N' → 0 < m' →
      u (A * N' ^ (1 - α)) + MIUSeparable.utilPow ν m' - h N'
        ≤ u (A * N ^ (1 - α)) + MIUSeparable.utilPow ν m - h N := by
  intro hopt
  have hg : HasDerivAt (fun m' => u (A * N ^ (1 - α)) + MIUSeparable.utilPow ν m' - h N)
      (m ^ (-ν)) m :=
    ((MIUSeparable.hasDerivAt_utilPow ν hm).const_add (u (A * N ^ (1 - α)))).sub_const (h N)
  have hloc : IsLocalMax (fun m' => u (A * N ^ (1 - α)) + MIUSeparable.utilPow ν m' - h N) m := by
    filter_upwards [eventually_gt_nhds hm] with m' hm'
    exact hopt N m' hN hm'
  exact (Real.rpow_pos_of_pos hm (-ν)).ne' (hloc.hasDerivAt_eq_zero hg)

/-! ### Decentralisation and the Friedman rule -/

/-- Galí (2015), p. 41: in a decentralised equilibrium, the household's labour supply (4)
`−U_n/U_c = W/P` and the firm's labour demand (14) `W/P = (1 − α) A N^{−α}` together give
the efficiency condition (49), whatever monetary policy is. -/
theorem decentralised_49 {Uc Un W P A α N : ℝ} (h4 : -Un / Uc = W / P)
    (h14 : W / P = (1 - α) * A * N ^ (-α)) : -Un / Uc = (1 - α) * A * N ^ (-α) := by
  rw [h4, h14]

/-- Galí (2015), p. 41: `1 − e^{−i} = 0` iff `i = 0`. -/
theorem one_sub_exp_neg_eq_zero_iff (i : ℝ) : 1 - Real.exp (-i) = 0 ↔ i = 0 := by
  rw [sub_eq_zero, eq_comm, Real.exp_eq_one_iff, neg_eq_zero]

/-- Galí (2015), p. 41 (**the Friedman rule**): if the household's money condition (33)
`U_m = (1 − e^{−i}) U_c` holds at every date with `U_c ≠ 0`, the efficiency condition (50)
`U_m = 0` holds at every date iff `i_t = 0` at every date. -/
theorem decentralised_efficient_iff {Uc Um i : ℕ → ℝ} (hUc : ∀ t, Uc t ≠ 0)
    (h33 : ∀ t, Um t = (1 - Real.exp (-i t)) * Uc t) :
    (∀ t, Um t = 0) ↔ ∀ t, i t = 0 := by
  refine forall_congr' fun t => ?_
  rw [h33 t, mul_eq_zero, or_iff_left (hUc t), one_sub_exp_neg_eq_zero_iff]

/-- Galí (2015), p. 41 (**the Friedman rule, global form**): with the separable utility of
`planner_optimum_iff` and `u'(C) > 0`, a decentralised allocation satisfying (49) (from (4)
and (14)) and the money condition (33) `v'(m) = (1 − e^{−i}) u'(C)` solves the planner's
problem iff `i = 0`. -/
theorem decentralised_optimal_iff_friedman {u v h u' v' h' : ℝ → ℝ} {A α N m i : ℝ}
    (hA : 0 < A) (hα0 : 0 ≤ α) (hα1 : α < 1) (hN : 0 < N) (hm : 0 < m)
    (hu : ∀ z, 0 < z → HasDerivAt u (u' z) z) (hu_anti : AntitoneOn u' (Set.Ioi 0))
    (hu_pos : 0 < u' (A * N ^ (1 - α)))
    (hv : ∀ z, 0 < z → HasDerivAt v (v' z) z) (hv_anti : AntitoneOn v' (Set.Ioi 0))
    (hh : ∀ z, 0 < z → HasDerivAt h (h' z) z) (hh_mono : MonotoneOn h' (Set.Ioi 0))
    (h49 : h' N = (1 - α) * A * N ^ (-α) * u' (A * N ^ (1 - α)))
    (h33 : v' m = (1 - Real.exp (-i)) * u' (A * N ^ (1 - α))) :
    (∀ N' m', 0 < N' → 0 < m' →
      u (A * N' ^ (1 - α)) + v m' - h N' ≤ u (A * N ^ (1 - α)) + v m - h N) ↔ i = 0 := by
  rw [planner_optimum_iff hA hα0 hα1 hN hm hu hu_anti hu_pos.le hv hv_anti hh hh_mono, h33,
    mul_eq_zero, or_iff_left hu_pos.ne', one_sub_exp_neg_eq_zero_iff]
  exact and_iff_right h49

/-- Galí (2015), p. 41: in a steady state with constant consumption the Euler equation reads
`e^{−i} = e^{−ρ} e^{−π}` (`Q = β/Π`); under the Friedman rule `i = 0` this gives `π = −ρ`,
i.e. `Π = e^π = β`, and deflation `π < 0` when `ρ > 0`. -/
theorem friedman_steady_state_inflation {i ρ π : ℝ}
    (hE : Real.exp (-i) = Real.exp (-ρ) * Real.exp (-π)) (hi : i = 0) :
    π = -ρ ∧ Real.exp π = Real.exp (-ρ) ∧ (0 < ρ → π < 0) := by
  rw [← Real.exp_add, Real.exp_eq_exp, hi] at hE
  have hπ : π = -ρ := by linarith
  exact ⟨hπ, by rw [hπ], fun h => by linarith⟩

/-! ### Indeterminacy under `i = 0` -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 41 (the log-linear model): with `i ≡ 0`, output from (43)
`y_t = ψ_ya a_t + ψ_y` and adapted technology, the Euler equation (47) holds iff
`E_t π_{t+1} = −ρ − σ ψ_ya (E_t a_{t+1} − a_t)` at every date. -/
theorem friedman_euler_iff {σ ϖ ρ ψya ψy : ℝ} (hσ : σ ≠ 0) {a y infl : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = ψya • a t + fun _ => ψy) :
    MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl ↔
      ∀ t, 𝔼.E t (infl (t + 1)) = (fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t) := by
  unfold MIUNonseparable.EulerLinear
  refine forall_congr' fun t => ?_
  rw [hy t, hy (t + 1), map_add, map_smul, 𝔼.const]
  simp only [funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_self, mul_zero,
    sub_zero, map_zero, Pi.zero_apply]
  constructor
  · intro h
    field_simp at h
    linear_combination -h
  · intro h
    field_simp
    linear_combination -h

/-- Galí (2015), p. 41 (**indeterminacy under `i = 0`**): with `i ≡ 0`, `y_t = ψ_ya a_t + ψ_y`
and `σ ≠ 0`, inflation is an equilibrium iff there is a martingale-difference sequence `ξ`
(`E_t ξ_{t+1} = 0`) with `π_{t+1} = −ρ − σ ψ_ya E_t Δa_{t+1} + ξ_{t+1}` at every date; any such
`ξ` gives an equilibrium. -/
theorem friedman_equilibrium_iff {σ ϖ ρ ψya ψy : ℝ} (hσ : σ ≠ 0) {a y infl : ℕ → Ω → ℝ}
    (haA : 𝔼.Adapted a) (hy : ∀ t, y t = ψya • a t + fun _ => ψy) :
    MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl ↔
      ∃ ξ : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (ξ (t + 1)) = 0) ∧ ∀ t,
        infl (t + 1) = (fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t) + ξ (t + 1) := by
  rw [friedman_euler_iff 𝔼 hσ hy]
  have hEf : ∀ t, 𝔼.E t ((fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t))
      = (fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t) := by
    intro t
    rw [map_sub, 𝔼.const, map_smul, map_sub, ExpectationSystem.E_E_self, haA t]
  constructor
  · intro h
    refine ⟨fun s => match s with
      | 0 => 0
      | t + 1 => infl (t + 1) - ((fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t)),
      fun t => ?_, fun t => ?_⟩
    · simp only
      rw [map_sub, h t, hEf t, sub_self]
    · simp only
      abel
  · rintro ⟨ξ, hξ, hπ⟩ t
    rw [hπ t, map_add, hξ t, add_zero, hEf t]

/-- Galí (2015), p. 41 (**two distinct equilibria under `i = 0`**): next to any equilibrium
inflation process there is a different one, obtained by changing date-0 inflation (hence
the initial price level) by any `c ≠ 0`; nothing in (43), (47) pins it down. -/
theorem friedman_indeterminate [Nonempty Ω] {σ ϖ ρ : ℝ} {y infl : ℕ → Ω → ℝ}
    (h : MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl) {c : ℝ} (hc : c ≠ 0) :
    ∃ infl' : ℕ → Ω → ℝ, MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl' ∧
      infl' ≠ infl := by
  refine ⟨fun s => match s with
    | 0 => infl 0 + fun (_ : Ω) => c
    | t + 1 => infl (t + 1), fun t => h t, fun he => hc ?_⟩
  have := congrFun (congrFun he 0) (Classical.arbitrary Ω)
  simpa using this

/-- Galí (2015), p. 41 (**a genuine sunspot**): under the two-coin-flip expectation system,
with constant technology and `i ≡ 0`, both the fundamental path `π_{t+1} = −ρ` and the sunspot
path `π_{t+1} = −ρ + ε_{t+1}` (`ε` the mean-zero coin-flip shock) are equilibria, and they
differ at date 1. -/
theorem friedman_sunspot_coin {σ ϖ ρ ψy : ℝ} (hσ : σ ≠ 0) :
    MIUNonseparable.EulerLinear ExpectationsFiniteTree.coinSystem σ ϖ ρ (fun _ _ => ψy)
        (fun _ => 0) (fun _ _ => -ρ) ∧
      MIUNonseparable.EulerLinear ExpectationsFiniteTree.coinSystem σ ϖ ρ (fun _ _ => ψy)
        (fun _ => 0) (fun t ω => -ρ + ExpectationsFiniteTree.coinShock t ω) ∧
      (fun t ω => -ρ + ExpectationsFiniteTree.coinShock t ω) ≠
        fun (_ : ℕ) (_ : Bool × Bool) => -ρ := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem with h𝔼c
  have hy : ∀ _ : ℕ, (fun _ : Bool × Bool => ψy) = (0 : ℝ) • (fun _ : Bool × Bool => (0 : ℝ))
      + fun _ => ψy := fun _ => by
    funext ω
    simp
  have haA : 𝔼c.Adapted (fun _ _ => 0) := fun t => by
    rw [show (fun _ : Bool × Bool => (0 : ℝ)) = fun _ => 0 from rfl, 𝔼c.const]
  refine ⟨?_, ?_, ?_⟩
  · refine (friedman_equilibrium_iff 𝔼c hσ (a := fun _ _ => 0) haA hy).2
      ⟨fun _ => 0, fun t => map_zero _, fun t => ?_⟩
    funext ω
    simp [𝔼c.const]
  · refine (friedman_equilibrium_iff 𝔼c hσ (a := fun _ _ => 0) haA hy).2
      ⟨ExpectationsFiniteTree.coinShock, fun t => ExpectationsFiniteTree.coinShock_mean_zero t,
        fun t => ?_⟩
    funext ω
    simp [𝔼c.const]
  · intro he
    have := congrFun (congrFun he 1) (true, true)
    simp [ExpectationsFiniteTree.coinShock] at this

/-! ### Fn. 13: the rule `î_t = φ_π π̂_t` in the MIU model -/

/-- Galí (2015), fn. 13, p. 41 (exercise 2.6): the composite coefficient
`s = ϖ + σ ψ_yi = ϖ(φ + α)/D`. -/
theorem s_eq {ϖ σ φ α : ℝ} (hD : MIUNonseparable.bigD σ φ α ≠ 0) :
    ϖ + σ * MIUNonseparable.psiYi ϖ σ φ α = ϖ * (φ + α) / MIUNonseparable.bigD σ φ α := by
  unfold MIUNonseparable.psiYi
  field_simp
  unfold MIUNonseparable.bigD
  ring

/-- Galí (2015), fn. 13, p. 41: `s ≥ 0` for `ϖ ≥ 0`, `φ + α ≥ 0`, `D > 0`. -/
theorem s_nonneg {ϖ σ φ α : ℝ} (hD : 0 < MIUNonseparable.bigD σ φ α) (hϖ : 0 ≤ ϖ)
    (hφα : 0 ≤ φ + α) : 0 ≤ ϖ + σ * MIUNonseparable.psiYi ϖ σ φ α := by
  rw [s_eq hD.ne']
  exact div_nonneg (mul_nonneg hϖ hφα) hD.le

/-- Galí (2015), fn. 13, p. 41 (the log-linear model, deviations): output (43)
`ŷ = ψ_ya a + ψ_yi î`, the Euler equation (47) and the rule `î_t = φ_π π̂_t`. -/
def RuleSystem (σ ϖ ψya ψyi phiPi : ℝ) (a infl : ℕ → Ω → ℝ) : Prop :=
  MIUNonseparable.EulerLinear 𝔼 σ ϖ 0 (fun t => ψya • a t + ψyi • (phiPi • infl t))
    (fun t => phiPi • infl t) infl

/-- Galí (2015), fn. 13, p. 41: the node-wise algebra behind `ruleSystem_iff`. -/
theorem rule_real {σ ϖ ψya ψyi φπ at' Ea πt Eπ : ℝ} (hσ : σ ≠ 0) :
    ψya * at' + ψyi * (φπ * πt) = ψya * Ea + ψyi * (φπ * Eπ)
      - σ⁻¹ * (φπ * πt - Eπ - ϖ * (φπ * Eπ - φπ * πt) - 0) ↔
    (1 + φπ * (ϖ + σ * ψyi)) * Eπ = φπ * (1 + (ϖ + σ * ψyi)) * πt + σ * ψya * (at' - Ea) := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := (1 + φπ * (ϖ + σ * ψyi)) * Eπ)]
  have key : ψya * at' + ψyi * (φπ * πt) - (ψya * Ea + ψyi * (φπ * Eπ)
      - σ⁻¹ * (φπ * πt - Eπ - ϖ * (φπ * Eπ - φπ * πt) - 0))
      = -σ⁻¹ * ((1 + φπ * (ϖ + σ * ψyi)) * Eπ
        - (φπ * (1 + (ϖ + σ * ψyi)) * πt + σ * ψya * (at' - Ea))) := by
    field_simp
    ring
  rw [key, neg_mul, neg_eq_zero, mul_eq_zero, or_iff_right (inv_ne_zero hσ)]

/-- Galí (2015), fn. 13, p. 41 (exercise 2.6): for `σ ≠ 0` the system holds iff
`(1 + φ_π s) E_t π_{t+1} = φ_π (1 + s) π_t + σ ψ_ya (a_t − E_t a_{t+1})`, `s = ϖ + σ ψ_yi`. -/
theorem ruleSystem_iff {σ ϖ ψya ψyi phiPi : ℝ} (hσ : σ ≠ 0) (a infl : ℕ → Ω → ℝ) :
    RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl ↔ ∀ t,
      (1 + phiPi * (ϖ + σ * ψyi)) • 𝔼.E t (infl (t + 1))
        = (phiPi * (1 + (ϖ + σ * ψyi))) • infl t + (σ * ψya) • (a t - 𝔼.E t (a (t + 1))) := by
  unfold RuleSystem MIUNonseparable.EulerLinear
  refine forall_congr' fun t => ?_
  simp only [map_add, map_smul, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact rule_real hσ

/-- Galí (2015), fn. 13, p. 41 (**uniqueness for `φ_π > 1`**): with `s ≥ 0` and `σ ≠ 0`, two
bounded solutions of the system coincide. -/
theorem fn13_unique {σ ϖ ψya ψyi phiPi : ℝ} (hσ : σ ≠ 0) (hs : 0 ≤ ϖ + σ * ψyi)
    (hφ : 1 < phiPi) {a infl₁ infl₂ : ℕ → Ω → ℝ}
    (h₁ : RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl₁) (h₂ : RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl₂)
    (hb₁ : BoundedProc infl₁) (hb₂ : BoundedProc infl₂) : infl₁ = infl₂ := by
  set s := ϖ + σ * ψyi with hsdef
  have hpos : 0 < phiPi * (1 + s) := by nlinarith
  set c := (1 + phiPi * s) / (phiPi * (1 + s)) with hc
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hpos.le
  have hc1 : c < 1 := (div_lt_one hpos).2 (by nlinarith)
  have e₁ := (ruleSystem_iff 𝔼 hσ a infl₁).1 h₁
  have e₂ := (ruleSystem_iff 𝔼 hσ a infl₂).1 h₂
  have hf : ∀ {π : ℕ → Ω → ℝ}, (∀ t, (1 + phiPi * s) • 𝔼.E t (π (t + 1))
      = (phiPi * (1 + s)) • π t + (σ * ψya) • (a t - 𝔼.E t (a (t + 1)))) →
      ∀ t, π t = c • 𝔼.E t (π (t + 1)) + (-(σ * ψya) / (phiPi * (1 + s))) •
        (a t - 𝔼.E t (a (t + 1))) := by
    intro π e t
    funext ω
    have := congrFun (e t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [hc]
    field_simp
    linear_combination -this
  have habs : |c| < 1 := by rw [abs_of_nonneg hc0]; exact hc1
  exact 𝔼.forward_unique habs (hf e₁) (hf e₂) hb₁ hb₂

/-- Galí (2015), fn. 13, p. 41 (**existence for `φ_π > 1`**): with bounded adapted technology,
the forward series is a bounded solution of the system. -/
theorem fn13_exists {σ ϖ ψya ψyi phiPi M : ℝ} (hσ : σ ≠ 0) (hs : 0 ≤ ϖ + σ * ψyi)
    (hφ : 1 < phiPi) {a : ℕ → Ω → ℝ} (haA : 𝔼.Adapted a) (hab : ∀ t ω, |a t ω| ≤ M) :
    ∃ infl : ℕ → Ω → ℝ, RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl ∧ BoundedProc infl ∧
      𝔼.Adapted infl := by
  set s := ϖ + σ * ψyi with hsdef
  have hpos : 0 < phiPi * (1 + s) := by nlinarith
  set c := (1 + phiPi * s) / (phiPi * (1 + s)) with hc
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hpos.le
  have hc1 : c < 1 := (div_lt_one hpos).2 (by nlinarith)
  set k := -(σ * ψya) / (phiPi * (1 + s)) with hk
  set u : ℕ → Ω → ℝ := fun t => k • (a t - 𝔼.E t (a (t + 1))) with hu
  have hub : ∀ t ω, |u t ω| ≤ |k| * (M + M) := by
    intro t ω
    simp only [hu, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hab t ω) ?_))
      (abs_nonneg k)
    exact 𝔼.abs_E_le (hab (t + 1)) t ω
  have huA : 𝔼.Adapted u := by
    intro t
    simp only [hu]
    rw [map_smul, map_sub, haA t, ExpectationSystem.E_E_self]
  refine ⟨𝔼.forwardSeries c u, ?_, 𝔼.forwardSeries_bounded hc0 hc1 hub,
    MIUNonseparable.forwardSeries_adapted 𝔼 hc0 hc1 hub⟩
  rw [ruleSystem_iff 𝔼 hσ]
  intro t
  have hsol := 𝔼.forwardSeries_solves hc0 hc1 hub huA t
  rw [hsol]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu, Pi.sub_apply]
  rw [hc, hk]
  field_simp
  ring

/-- Galí (2015), fn. 13, p. 41 (**multiplicity for `0 ≤ φ_π ≤ 1`**): with `s ≥ 0`,
`σ ≠ 0`, next to any bounded solution there is a different bounded solution
`π_t + c^t`, `c = φ_π(1 + s)/(1 + φ_π s) ∈ [0, 1]` (a self-fulfilling deterministic path). -/
theorem fn13_not_unique [Nonempty Ω] {σ ϖ ψya ψyi phiPi : ℝ} (hσ : σ ≠ 0)
    (hs : 0 ≤ ϖ + σ * ψyi) (hφ0 : 0 ≤ phiPi) (hφ1 : phiPi ≤ 1) {a infl : ℕ → Ω → ℝ}
    (h : RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl) (hb : BoundedProc infl) :
    ∃ infl' : ℕ → Ω → ℝ, RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl' ∧ BoundedProc infl' ∧
      infl' ≠ infl := by
  set s := ϖ + σ * ψyi with hsdef
  have hden : 0 < 1 + phiPi * s := by nlinarith
  set c := phiPi * (1 + s) / (1 + phiPi * s) with hc
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hden.le
  have hc1 : c ≤ 1 := (div_le_one hden).2 (by nlinarith)
  obtain ⟨M, hM⟩ := hb
  have e := (ruleSystem_iff 𝔼 hσ a infl).1 h
  refine ⟨fun t => infl t + fun _ => c ^ t, ?_, ⟨M + 1, fun t ω => ?_⟩, fun he => ?_⟩
  · rw [ruleSystem_iff 𝔼 hσ]
    intro t
    rw [map_add, 𝔼.const, smul_add, e t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc, pow_succ]
    field_simp
    ring
  · simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_of_nonneg (pow_nonneg hc0 t)]
    exact pow_le_one₀ hc0 hc1
  · have := congrFun (congrFun he 0) (Classical.arbitrary Ω)
    simp at this

/-! ### The rule `i_t = φ (r_{t−1} + π_t)` (p. 42), in the log-linear model -/

/-- Galí (2015), p. 42 (**uniqueness**, log-linear model): with the Fisher equation (22)
`i_t = r_t + E_t π_{t+1}`, an adapted real rate `r`, the rule `i_t = φ (r_{t−1} + π_t)`
(`r_{−1}` given) and `φ > 1`, every bounded nominal rate is `i ≡ 0`, and then
`π_0 = −r_{−1}`, `π_{t+1} = −r_t`. -/
theorem lagged_rule_unique {φ rm1 : ℝ} (hφ : 1 < φ) {r i infl : ℕ → Ω → ℝ}
    (hrA : 𝔼.Adapted r) (hF : ∀ t, i t = r t + 𝔼.E t (infl (t + 1)))
    (hR0 : i 0 = φ • ((fun _ => rm1) + infl 0)) (hR : ∀ t, i (t + 1) = φ • (r t + infl (t + 1)))
    (hib : BoundedProc i) :
    i = 0 ∧ infl 0 = (fun _ => -rm1) ∧ ∀ t, infl (t + 1) = -r t := by
  have hφ0 : φ ≠ 0 := by linarith
  have heq : ∀ t, i t = φ⁻¹ • 𝔼.E t (i (t + 1)) + 0 := by
    intro t
    rw [hR t, map_smul, map_add, hrA t, ← hF t, smul_smul, inv_mul_cancel₀ hφ0, one_smul,
      add_zero]
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = φ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have habs : |φ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < φ)]
    exact inv_lt_one_of_one_lt₀ hφ
  have hi0 : i = 0 := 𝔼.forward_unique habs heq hz hib ⟨0, fun _ _ => by simp⟩
  refine ⟨hi0, ?_, fun t => ?_⟩
  · have h := hR0
    rw [hi0] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.zero_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    have := (mul_eq_zero.1 this.symm).resolve_left hφ0
    linarith
  · have h := hR t
    rw [hi0] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.zero_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    have := (mul_eq_zero.1 this.symm).resolve_left hφ0
    simp only [Pi.neg_apply]
    linarith

/-- Galí (2015), p. 42 (**existence**, log-linear model): `i ≡ 0`, `π_0 = −r_{−1}`,
`π_{t+1} = −r_t` satisfies the Fisher equation and the rule; inflation is adapted and is
bounded when `r` is. -/
theorem lagged_rule_exists (φ rm1 : ℝ) {r : ℕ → Ω → ℝ} (hrA : 𝔼.Adapted r) :
    let infl : ℕ → Ω → ℝ := fun s => match s with
      | 0 => fun _ => -rm1
      | t + 1 => -r t
    (∀ t, (0 : ℕ → Ω → ℝ) t = r t + 𝔼.E t (infl (t + 1))) ∧
      (0 : ℕ → Ω → ℝ) 0 = φ • ((fun _ => rm1) + infl 0) ∧
      (∀ t, (0 : ℕ → Ω → ℝ) (t + 1) = φ • (r t + infl (t + 1))) ∧ 𝔼.Adapted infl ∧
      (BoundedProc r → BoundedProc infl) := by
  intro infl
  refine ⟨fun t => ?_, ?_, fun t => ?_, fun t => ?_, fun ⟨M, hM⟩ => ⟨max M |rm1|, ?_⟩⟩
  · simp only [infl, map_neg, hrA t]
    simp
  · funext ω
    simp [infl]
  · funext ω
    simp [infl]
  · rcases t with _ | t
    · simp only [infl]
      exact 𝔼.const 0 (-rm1)
    · simp only [infl]
      rw [map_neg, ← hrA t, 𝔼.known (Nat.le_succ t)]
  · intro t ω
    rcases t with _ | t
    · simp [infl]
    · simp only [infl, Pi.neg_apply, abs_neg]
      exact (hM t ω).trans (le_max_left _ _)

/-- Galí (2015), p. 42: more generally, any policy that makes inflation move one-for-one and
inversely with the lagged real rate, `π_{t+1} = −r_t`, implies a zero nominal rate through
the Fisher equation (22), for adapted `r`. -/
theorem inflation_rule_implies_zero_rate {r i infl : ℕ → Ω → ℝ} (hrA : 𝔼.Adapted r)
    (hF : ∀ t, i t = r t + 𝔼.E t (infl (t + 1))) (hπ : ∀ t, infl (t + 1) = -r t) :
    ∀ t, i t = 0 := by
  intro t
  rw [hF t, hπ t, map_neg, hrA t, add_neg_cancel]

end Gali.ClassicalMonetaryModel.FriedmanRule

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.1: optimality conditions under nonseparable leisure

Galí (2015), Chapter 2, Exercise 2.1, p. 46. The period utility is
`U(C, N) = ([C (1 − N)^ν]^{1−σ} − 1)/(1 − σ)` (`periodUtility`; its limit
`log C + ν log(1 − N)` for `σ = 1` is included), with `σ > 0`, `ν > 0`, `0 ≤ N < 1`.
The household problem is that of §2.1 (pp. 18–20): budget `P_t C_t + Q_t B_t ≤ B_{t−1} +
W_t N_t + D_t`.

## Marginal utilities (exact derivatives)

`hasDerivAt_periodUtility_C`, `hasDerivAt_periodUtility_N`: `U_C = [C(1−N)^ν]^{−σ}(1−N)^ν`
(`margUtilC`, `= C^{−σ}(1−N)^{ν(1−σ)}` by `margUtilC_eq`) and
`U_N = −[C(1−N)^ν]^{−σ} C ν (1−N)^{ν−1}` (`margUtilN`); `mrs_eq`: `−U_N/U_C = ν C/(1 − N)`.

## The static (labour-supply) condition, eq. (4), p. 19

Hours are perturbed along the budget line `P dC = W dN`.
* `static_foc_necessary`: a local optimum satisfies `U_C (W/P) + U_N = 0`, i.e. eq. (4);
  `static_wage_necessary`: hence `W/P = ν C/(1 − N)`.
* `static_foc_sufficient`: conversely `W/P = ν C/(1 − N)` gives the global optimum over all
  feasible hours (`U` is a strictly increasing function of `C(1 − N)^ν`, whose logarithm is
  concave along the budget line; this works for every `σ > 0`, although `U` itself is not
  jointly concave when `σ < 1` and `(1 − σ)(1 + ν) > 1`). `static_optimum_iff` combines both.
* `labour_supply_log_iff` (**exact**): `w − p = c + log ν − log(1 − N)`.
* `hasDerivAt_labourSupply_family` (**first order**): along `c = c̄ + s ĉ`, `n = n̄ + s n̂`
  the right-hand side has derivative `ĉ + (N/(1 − N)) n̂` at `s = 0`: the log-linear labour
  supply `ŵ − p̂ = ĉ + (N/(1−N)) n̂`, with `N = e^{n̄}`.

## The Euler equation, eq. (5), p. 19

General tools, stated for an arbitrary `ExpectationSystem`:
* `hasDerivAt_E_of_uniform`: if `F(δ)(ω') − F(0)(ω') − δ L(ω') = o(δ)` uniformly in `ω'`,
  then `δ ↦ E_t F(δ)` has derivative `E_t L` (the abstract `E_t` only needs to be linear,
  monotone and constant-preserving).
* `uniform_of_concave`: for concave utilities the uniformity follows from a uniform modulus of
  continuity of marginal utility, which always holds with finitely many states
  (`uniformCont_of_finite`).
* `euler_necessary_generic`, `euler_sufficient_generic`: first-order condition of the
  one-period bond perturbation, necessary (local optimum) and sufficient (concavity).

For Exercise 2.1: `euler_necessary` (necessity under the uniform-continuity hypothesis),
`euler_necessary_finite` (finitely many states, no extra hypothesis), `euler_sufficient`, and
`EulerEq`, the book's eq. (5) `Q_t = β E_t[(U_{C,t+1}/U_{C,t})(P_t/P_{t+1})]` written as
`Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`.

## Log-linear Euler equation

* `eulerEq_iff_moment` (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`, `P = e^p`,
  `1 − N = e^ℓ`: `E_t[exp(i_t − ρ − σΔc_{t+1} − Δp_{t+1} + ν(1−σ)Δℓ_{t+1})] = 1`.
* `pf_eulerEq_iff` (**exact**, perfect foresight):
  `i_t − π_{t+1} − ρ = σΔc_{t+1} − ν(1−σ)Δℓ_{t+1}`.
* `hasDerivAt_moment_family` (**first order**, uncertainty): along `i = ρ + s î`,
  `c = c̄ + s ĉ`, `p = p̄ + s p̂`, `n = n̄ + s n̂` (bounded deviations; `ℓ = log(1 − e^n)`), the
  Euler moment has derivative `E_t` of `linearisedEuler` at `s = 0`;
  `linearisedEuler_zero_iff`: this vanishes iff
  `ĉ_t = E_t ĉ_{t+1} − σ^{−1}(î_t − E_t π̂_{t+1}) + σ^{−1} ν (1 − σ) (N/(1 − N)) E_t Δn̂_{t+1}`,
  the log-linear Euler equation with the nonseparable-leisure term.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_1

open Filter Topology

/-! ### Utility -/

/-- Galí (2015), Exercise 2.1, p. 46: the outer transformation `g(x) = (x^{1−σ} − 1)/(1 − σ)`
of the composite `x = C(1 − N)^ν`, and its limit `log x` for `σ = 1` (restated from the
Chapter 3 project, `utilC`). -/
noncomputable def utilC (σ x : ℝ) : ℝ :=
  if σ = 1 then Real.log x else (x ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), Exercise 2.1, p. 46: `g'(x) = x^{−σ}` for `x > 0`, in both the `σ ≠ 1` and
the log case (restated from the Chapter 3 project). -/
theorem hasDerivAt_utilC (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (utilC σ) (x ^ (-σ)) x := by
  by_cases hσ : σ = 1
  · have hfun : utilC σ = Real.log := funext fun x => by simp [utilC, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hx.ne'
  · have hfun : utilC σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [utilC, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), Exercise 2.1, p. 46: `g` is strictly increasing on `(0, ∞)`. -/
theorem utilC_strictMonoOn (σ : ℝ) : StrictMonoOn (utilC σ) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) (fun x hx => ?_) (fun x hx => ?_)
  · exact (hasDerivAt_utilC σ hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hx
    rw [(hasDerivAt_utilC σ hx).deriv]
    exact Real.rpow_pos_of_pos hx _

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (Galí (2015), p. 18, concavity of utility; restated from the Chapter 3
project). -/
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

/-- Galí (2015), p. 18 (concavity): a function differentiable on `(0, ∞)` with nonincreasing
derivative satisfies the tangent inequality `f y ≤ f x + f'(x)(y − x)` for `x, y > 0`. -/
theorem tangent_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z) (hanti : AntitoneOn f' (Set.Ioi 0)) :
    f y ≤ f x + f' x * (y - x) := by
  refine le_tangent hx hy.le (fun z hz => ?_) hd hanti
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hd z hz0).continuousAt.continuousWithinAt

/-- Galí (2015), Exercise 2.1, p. 46: period utility `U(C, N) = g(C (1 − N)^ν)`. -/
noncomputable def periodUtility (σ ν C N : ℝ) : ℝ := utilC σ (C * (1 - N) ^ ν)

/-- Galí (2015), Exercise 2.1, p. 46: marginal utility of consumption
`U_C = [C(1 − N)^ν]^{−σ} (1 − N)^ν`. -/
noncomputable def margUtilC (σ ν C N : ℝ) : ℝ := (C * (1 - N) ^ ν) ^ (-σ) * (1 - N) ^ ν

/-- Galí (2015), Exercise 2.1, p. 46: marginal utility of hours
`U_N = −[C(1 − N)^ν]^{−σ} C ν (1 − N)^{ν−1}`. -/
noncomputable def margUtilN (σ ν C N : ℝ) : ℝ :=
  -((C * (1 - N) ^ ν) ^ (-σ) * (C * (ν * (1 - N) ^ (ν - 1))))

/-- Galí (2015), Exercise 2.1, p. 46 (**exact derivative**): `∂U/∂C = margUtilC`. -/
theorem hasDerivAt_periodUtility_C (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    HasDerivAt (fun C' => periodUtility σ ν C' N) (margUtilC σ ν C N) C := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  exact (hasDerivAt_utilC σ (mul_pos hC hL)).comp C (hasDerivAt_mul_const ((1 - N) ^ ν))

/-- Galí (2015), Exercise 2.1, p. 46: `d/dN (1 − N)^ν = −ν (1 − N)^{ν−1}` for `N < 1`. -/
theorem hasDerivAt_leisure_pow (ν : ℝ) {N : ℝ} (hN : N < 1) :
    HasDerivAt (fun N' => (1 - N') ^ ν) (ν * (1 - N) ^ (ν - 1) * (-1)) N :=
  (Real.hasDerivAt_rpow_const (x := 1 - N) (p := ν) (Or.inl (sub_pos.2 hN).ne')).comp N
    ((hasDerivAt_id N).const_sub 1)

/-- Galí (2015), Exercise 2.1, p. 46 (**exact derivative**): `∂U/∂N = margUtilN`. -/
theorem hasDerivAt_periodUtility_N (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    HasDerivAt (fun N' => periodUtility σ ν C N') (margUtilN σ ν C N) N := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  refine ((hasDerivAt_utilC σ (mul_pos hC hL)).comp N
    ((hasDerivAt_leisure_pow ν hN).const_mul C)).congr_deriv ?_
  unfold margUtilN
  ring

/-- Galí (2015), Exercise 2.1, p. 46: `U_C > 0`. -/
theorem margUtilC_pos (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    0 < margUtilC σ ν C N := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC hL) _) hL

/-- Galí (2015), Exercise 2.1, p. 46: `U_C = C^{−σ} (1 − N)^{ν(1−σ)}`. -/
theorem margUtilC_eq (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    margUtilC σ ν C N = C ^ (-σ) * (1 - N) ^ (ν * (1 - σ)) := by
  have h1 : 0 < 1 - N := by linarith
  unfold margUtilC
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg h1.le ν), ← Real.rpow_mul h1.le, mul_assoc,
    ← Real.rpow_add h1]
  congr 2
  ring

/-- Galí (2015), Exercise 2.1, p. 46, and eq. (4), p. 19: the marginal rate of substitution
`−U_N/U_C = ν C/(1 − N)`. -/
theorem mrs_eq (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    -margUtilN σ ν C N / margUtilC σ ν C N = ν * C / (1 - N) := by
  have h1 : 0 < 1 - N := by linarith
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos h1 ν
  have hX : 0 < (C * (1 - N) ^ ν) ^ (-σ) := Real.rpow_pos_of_pos (mul_pos hC hL) _
  unfold margUtilN margUtilC
  rw [Real.rpow_sub_one h1.ne', neg_neg]
  field_simp

/-! ### The static (labour-supply) problem -/

/-- Galí (2015), eq. (4), p. 19, for Exercise 2.1 (**necessity**): if hours `N` (with
`N < 1`, `C > 0`) are a local optimum along the budget line `P C = W N + X` (perturbation
`P dC = W dN`, everything else unchanged), then `U_C · W/P + U_N = 0`. -/
theorem static_foc_necessary {σ ν P W X C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : N < 1)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ ν ((W * N' + X) / P) N') N) :
    margUtilC σ ν C N * (W / P) + margUtilN σ ν C N = 0 := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hprod := hin.mul (hasDerivAt_leisure_pow ν hN)
  have hu : HasDerivAt (utilC σ) (((W * N + X) / P * (1 - N) ^ ν) ^ (-σ))
      ((W * N + X) / P * (1 - N) ^ ν) := hasDerivAt_utilC σ (by rw [hCeq]; exact mul_pos hC hL)
  have hg := hu.comp N hprod
  have h0 := hloc.hasDerivAt_eq_zero hg
  rw [hCeq] at h0
  unfold margUtilC margUtilN
  linear_combination h0

/-- Galí (2015), eq. (4), p. 19, for Exercise 2.1: a local optimum of hours satisfies
`W/P = ν C/(1 − N)`. -/
theorem static_wage_necessary {σ ν P W X C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : N < 1)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ ν ((W * N' + X) / P) N') N) :
    W / P = ν * C / (1 - N) := by
  have h := static_foc_necessary hP hC hN hbud hloc
  have hpos := margUtilC_pos σ ν hC hN
  rw [← mrs_eq σ ν hC hN, eq_div_iff hpos.ne']
  linear_combination h

/-- Galí (2015), Exercise 2.1, p. 46 (**sufficiency**): if `W/P = ν C/(1 − N)` at a point
`(C, N)` on the budget line (`C > 0`, `N < 1`, `ν > 0`), then `(C, N)` maximises utility over
all feasible hours `N' < 1` with `C' = (W N' + X)/P > 0`. -/
theorem static_foc_sufficient {σ ν P W X C N : ℝ} (hν : 0 < ν) (hP : 0 < P) (hC : 0 < C)
    (hN : N < 1) (hbud : P * C = W * N + X) (hfoc : W / P = ν * C / (1 - N)) {N' : ℝ}
    (hN' : N' < 1) (hC' : 0 < (W * N' + X) / P) :
    periodUtility σ ν ((W * N' + X) / P) N' ≤ periodUtility σ ν C N := by
  set C' := (W * N' + X) / P with hC'def
  have h1 : 0 < 1 - N := by linarith
  have h1' : 0 < 1 - N' := by linarith
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos h1 ν
  have hL' : 0 < (1 - N') ^ ν := Real.rpow_pos_of_pos h1' ν
  have hdiff : C' - C = ν * C / (1 - N) * (N' - N) := by
    rw [← hfoc, hC'def, show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  -- `log` of the composite is concave along the budget line
  have hlogC : Real.log C' ≤ Real.log C + (C' / C - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos hC' hC)
    rw [Real.log_div hC'.ne' hC.ne'] at this
    linarith
  have hlogN : Real.log (1 - N') ≤ Real.log (1 - N) + ((1 - N') / (1 - N) - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos h1' h1)
    rw [Real.log_div h1'.ne' h1.ne'] at this
    linarith
  have hkey : Real.log (C' * (1 - N') ^ ν) ≤ Real.log (C * (1 - N) ^ ν) := by
    rw [Real.log_mul hC'.ne' hL'.ne', Real.log_mul hC.ne' hL.ne', Real.log_rpow h1',
      Real.log_rpow h1]
    have e1 : C' / C - 1 = ν * ((N' - N) / (1 - N)) := by
      rw [div_sub_one hC.ne', hdiff]
      field_simp
    have e2 : (1 - N') / (1 - N) - 1 = -((N' - N) / (1 - N)) := by
      field_simp
      ring
    rw [e1] at hlogC
    rw [e2] at hlogN
    nlinarith
  have hle : C' * (1 - N') ^ ν ≤ C * (1 - N) ^ ν :=
    (Real.log_le_log_iff (mul_pos hC' hL') (mul_pos hC hL)).1 hkey
  exact (utilC_strictMonoOn σ).monotoneOn (mul_pos hC' hL') (mul_pos hC hL) hle

/-- Galí (2015), p. 19: a global optimum of the static problem over all feasible plans with
`0 < N < 1` and `C > 0` is a local optimum along the budget line. -/
theorem static_isLocalMax_of_optimal {σ ν P W X C N : ℝ} (hP : 0 < P) (hN : N < 1)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hopt : ∀ N', N' < 1 → 0 < (W * N' + X) / P →
      periodUtility σ ν ((W * N' + X) / P) N' ≤ periodUtility σ ν C N) :
    IsLocalMax (fun N' => periodUtility σ ν ((W * N' + X) / P) N') N := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
    (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
  filter_upwards [h1, eventually_lt_nhds hN] with N' h1' h2'
  rw [hCeq]
  exact hopt N' h2' h1'

/-- Galí (2015), eq. (4), p. 19, for Exercise 2.1: for `ν > 0`, a point with `C > 0`,
`N < 1` on the budget line solves the static problem iff `W/P = ν C/(1 − N)`. -/
theorem static_optimum_iff {σ ν P W X C N : ℝ} (hν : 0 < ν) (hP : 0 < P) (hC : 0 < C)
    (hN : N < 1) (hbud : P * C = W * N + X) :
    (∀ N', N' < 1 → 0 < (W * N' + X) / P →
      periodUtility σ ν ((W * N' + X) / P) N' ≤ periodUtility σ ν C N) ↔
      W / P = ν * C / (1 - N) :=
  ⟨fun h => static_wage_necessary hP hC hN hbud (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hν hP hC hN hbud h hN' hC'⟩

/-- Galí (2015), Exercise 2.1 (**exact log form** of the labour-supply condition):
`W/P = ν C/(1 − N)` iff `w − p = c + log ν − log(1 − N)`. -/
theorem labour_supply_log_iff {ν W P C N : ℝ} (hν : 0 < ν) (hW : 0 < W) (hP : 0 < P)
    (hC : 0 < C) (hN : N < 1) :
    W / P = ν * C / (1 - N) ↔
      Real.log W - Real.log P = Real.log C + Real.log ν - Real.log (1 - N) := by
  have h1 : 0 < 1 - N := by linarith
  rw [← Real.log_injOn_pos.eq_iff (div_pos hW hP) (div_pos (mul_pos hν hC) h1),
    Real.log_div hW.ne' hP.ne', Real.log_div (mul_pos hν hC).ne' h1.ne',
    Real.log_mul hν.ne' hC.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 2.1 (**exact derivative**): with `N = e^n < 1`,
`d/dn [−log(1 − e^n)] = N/(1 − N)`. -/
theorem hasDerivAt_neg_log_one_sub_exp {n : ℝ} (hn : Real.exp n < 1) :
    HasDerivAt (fun x => -Real.log (1 - Real.exp x)) (Real.exp n / (1 - Real.exp n)) n := by
  have h := (((Real.hasDerivAt_exp n).const_sub 1).log (sub_pos.2 hn).ne').neg
  refine h.congr_deriv ?_
  ring

/-- Galí (2015), Exercise 2.1 (**first-order log-linear labour supply**): along
`c = c̄ + s ĉ`, `n = n̄ + s n̂` the map `s ↦ c + log ν − log(1 − e^n)` (the real wage
`w − p` demanded) has derivative `ĉ + (N/(1 − N)) n̂` at `s = 0`, `N = e^{n̄}`. -/
theorem hasDerivAt_labourSupply_family (ν cbar nbar ch nh : ℝ) (hn : Real.exp nbar < 1) :
    HasDerivAt (fun s => (cbar + s * ch) + Real.log ν - Real.log (1 - Real.exp (nbar + s * nh)))
      (ch + Real.exp nbar / (1 - Real.exp nbar) * nh) 0 := by
  have hin : HasDerivAt (fun s : ℝ => nbar + s * nh) nh 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const nh).const_add nbar
  have ho : HasDerivAt (fun x => -Real.log (1 - Real.exp x))
      (Real.exp nbar / (1 - Real.exp nbar)) (nbar + 0 * nh) := by
    rw [zero_mul, add_zero]
    exact hasDerivAt_neg_log_one_sub_exp hn
  have hc : HasDerivAt (fun s : ℝ => cbar + s * ch + Real.log ν) ch 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const ch).const_add cbar).add_const (Real.log ν)
  have := hc.add (ho.comp 0 hin)
  refine this.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · ring
  · exact Eventually.of_forall fun s => by simp [Function.comp_def, sub_eq_add_neg]

/-! ### Differentiating under the abstract expectation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 19 and App. 2.1, p. 44 (differentiating expected utility): if
`F(δ) − F(0) − δ L = o(δ)` uniformly in the state, then `δ ↦ E_t F(δ)` has derivative
`E_t L` at `0`. Only linearity, monotonicity and constants of `E_t` are used. -/
theorem hasDerivAt_E_of_uniform {F : ℝ → Ω → ℝ} {L : Ω → ℝ}
    (hF : ∀ ε > 0, ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ω, |F δ ω - F 0 ω - δ * L ω| ≤ ε * |δ|)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun δ => 𝔼.E t (F δ) ω) (𝔼.E t L ω) 0 := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hF ε hε] with δ hδ
  have e : 𝔼.E t (F δ) ω - 𝔼.E t (F 0) ω - (δ - 0) • 𝔼.E t L ω
      = 𝔼.E t (F δ - F 0 - δ • L) ω := by
    simp [map_sub, map_smul]
  rw [e, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero]
  exact 𝔼.abs_E_le (fun ω' => by simpa using hδ ω') t ω

/-- Galí (2015), p. 19 (one-period bond perturbation, concave utility): if the date-`t+1`
utilities `u ω` are differentiable on `(0, ∞)` with nonincreasing marginal utility `D ω`,
`c, p > 0` with a uniform lower bound `m ≤ p c`, and marginal utility has a uniform modulus of
continuity, then `δ ↦ u(c + δ/p)` is differentiable at `0` uniformly in the state, with
derivative `D(c)/p`. -/
theorem uniform_of_concave {u D : Ω → ℝ → ℝ} {c p : Ω → ℝ} {m : ℝ} (hm : 0 < m)
    (hp : ∀ ω, 0 < p ω) (hmpc : ∀ ω, m ≤ p ω * c ω)
    (hd : ∀ ω x, 0 < x → HasDerivAt (u ω) (D ω x) x)
    (hanti : ∀ ω, AntitoneOn (D ω) (Set.Ioi 0))
    (huc : ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω, |D ω (c ω + h / p ω) - D ω (c ω)| / p ω ≤ ε) :
    ∀ ε > 0, ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ω,
      |u ω (c ω + δ / p ω) - u ω (c ω + 0 / p ω) - δ * (D ω (c ω) / p ω)| ≤ ε * |δ| := by
  intro ε hε
  have hball : ∀ᶠ δ in 𝓝 (0 : ℝ), |δ| < m := by
    simpa using eventually_abs_sub_lt (0 : ℝ) hm
  filter_upwards [huc ε hε, hball] with δ hδ hδm ω
  have hpω := hp ω
  have hc : 0 < c ω := by
    have := hmpc ω
    by_contra h
    push Not at h
    nlinarith
  have hy : 0 < c ω + δ / p ω := by
    have h1 : |δ / p ω| < c ω := by
      rw [abs_div, abs_of_pos hpω, div_lt_iff₀ hpω]
      nlinarith [hmpc ω]
    have := neg_abs_le (δ / p ω)
    linarith
  rw [zero_div, add_zero]
  have t1 := tangent_of_deriv hc hy (hd ω) (hanti ω)
  have t2 := tangent_of_deriv hy hc (hd ω) (hanti ω)
  have e1 : D ω (c ω) * (c ω + δ / p ω - c ω) = δ * (D ω (c ω) / p ω) := by
    field_simp
    ring
  have e2 : D ω (c ω + δ / p ω) * (c ω - (c ω + δ / p ω))
      = -(δ * (D ω (c ω + δ / p ω) / p ω)) := by
    field_simp
    ring
  rw [e1] at t1
  rw [e2] at t2
  have hdiff : |δ * (D ω (c ω + δ / p ω) / p ω) - δ * (D ω (c ω) / p ω)| ≤ ε * |δ| := by
    rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos hpω, mul_comm]
    exact mul_le_mul_of_nonneg_right (hδ ω) (abs_nonneg δ)
  rw [abs_le] at hdiff ⊢
  constructor <;> linarith [hdiff.1, hdiff.2]

/-- Galí (2015), p. 19: with finitely many states the uniform modulus of continuity of marginal
utility required by `uniform_of_concave` holds automatically. -/
theorem uniformCont_of_finite [Finite Ω] {D : Ω → ℝ → ℝ} {c p : Ω → ℝ}
    (hcont : ∀ ω, ContinuousAt (D ω) (c ω)) :
    ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω, |D ω (c ω + h / p ω) - D ω (c ω)| / p ω ≤ ε := by
  intro ε hε
  rw [Filter.eventually_all]
  intro ω
  have hin : Tendsto (fun h : ℝ => c ω + h / p ω) (𝓝 0) (𝓝 (c ω)) := by
    have : Continuous (fun h : ℝ => c ω + h / p ω) := by fun_prop
    simpa using this.tendsto 0
  have hlim : Tendsto (fun h : ℝ => |D ω (c ω + h / p ω) - D ω (c ω)| / p ω) (𝓝 0)
      (𝓝 (|D ω (c ω) - D ω (c ω)| / p ω)) :=
    (((hcont ω).tendsto.comp hin).sub_const _).abs.div_const _
  rw [sub_self, abs_zero, zero_div] at hlim
  exact hlim.eventually (Iic_mem_nhds hε)

/-- Galí (2015), eq. (5), p. 19 (**necessity**, generic form): if the date-`t` value
`f(δ) + β E_t G(δ)` of a perturbation `δ` has a local maximum at `δ = 0`, where `f` has
derivative `f'` and `G(δ) − G(0) − δ L = o(δ)` uniformly in the state, then
`f' + β E_t L = 0`. -/
theorem euler_necessary_generic {f : ℝ → ℝ} {f' β : ℝ} {G : ℝ → Ω → ℝ} {L : Ω → ℝ}
    (hf : HasDerivAt f f' 0)
    (hG : ∀ ε > 0, ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ ω, |G δ ω - G 0 ω - δ * L ω| ≤ ε * |δ|)
    (t : ℕ) (ω : Ω) (hloc : IsLocalMax (fun δ => f δ + β * 𝔼.E t (G δ) ω) 0) :
    f' + β * 𝔼.E t L ω = 0 :=
  hloc.hasDerivAt_eq_zero (hf.add ((hasDerivAt_E_of_uniform 𝔼 hG t ω).const_mul β))

/-- Galí (2015), eq. (5), p. 19 (**sufficiency**, generic form): if the date-`t` term lies
below its tangent `f(δ) ≤ f(0) + δ a`, each date-`t+1` term lies below its tangent
`G(δ) ≤ G(0) + δ L`, `β ≥ 0`, and the first-order condition `a + β E_t L = 0` holds, then the
perturbation `δ` does not raise the date-`t` value. -/
theorem euler_sufficient_generic {f : ℝ → ℝ} {a β δ : ℝ} {G : ℝ → Ω → ℝ} {L : Ω → ℝ}
    (hβ : 0 ≤ β) (hf : f δ ≤ f 0 + δ * a) (hG : ∀ ω', G δ ω' ≤ G 0 ω' + δ * L ω')
    (t : ℕ) (ω : Ω) (hfoc : a + β * 𝔼.E t L ω = 0) :
    f δ + β * 𝔼.E t (G δ) ω ≤ f 0 + β * 𝔼.E t (G 0) ω := by
  have hle : G δ ≤ G 0 + δ • L := fun ω' => by simpa using hG ω'
  have hE := 𝔼.mono t hle ω
  rw [map_add, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  have := mul_le_mul_of_nonneg_left hE hβ
  have e : δ * a + β * (δ * 𝔼.E t L ω) = δ * (a + β * 𝔼.E t L ω) := by ring
  rw [hfoc, mul_zero] at e
  nlinarith

/-! ### The Euler equation for Exercise 2.1 -/

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1, node by node:
`Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`, i.e.
`Q_t = β E_t[(U_{C,t+1}/U_{C,t})(P_t/P_{t+1})]`. -/
def EulerEq (β σ ν : ℝ) (Q C N P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω * margUtilC σ ν (C t ω) (N t ω) / P t ω =
    β * 𝔼.E t (fun ω' => margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') ω

/-- Galí (2015), p. 19, for Exercise 2.1: expected utility as of node `ω` at date `t` of the
perturbation that buys `δ` more bonds at `t` (consumption falls by `Q_t δ/P_t`) and consumes
the payoff at `t + 1` (consumption rises by `δ/P_{t+1}`), hours unchanged. -/
noncomputable def perturbedValue (β σ ν : ℝ) (Q C N P : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => periodUtility σ ν (C t ω - Q t ω * δ / P t ω) (N t ω)
    + β * 𝔼.E t (fun ω' => periodUtility σ ν (C (t + 1) ω' + δ / P (t + 1) ω') (N (t + 1) ω')) ω

/-- Galí (2015), Exercise 2.1: `U_C` is nonincreasing in `C` for `σ > 0`. -/
theorem margUtilC_antitoneOn {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) {N : ℝ} (hN : N < 1) :
    AntitoneOn (fun C => margUtilC σ ν C N) (Set.Ioi 0) := by
  intro a ha b _ hab
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  have ha' : (0 : ℝ) < a * (1 - N) ^ ν := mul_pos ha hL
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ha'
    (mul_le_mul_of_nonneg_right hab hL.le) (by linarith)) hL.le

/-- Galí (2015), Exercise 2.1: `U_C` is continuous in `C` at `C > 0`. -/
theorem margUtilC_continuousAt (σ ν : ℝ) {C N : ℝ} (hC : 0 < C) (hN : N < 1) :
    ContinuousAt (fun C' => margUtilC σ ν C' N) C := by
  have hL : 0 < (1 - N) ^ ν := Real.rpow_pos_of_pos (by linarith) ν
  exact ((continuousAt_id.mul continuousAt_const).rpow_const
    (Or.inl (mul_pos hC hL).ne')).mul continuousAt_const

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1 (**necessity of the Euler equation**): if at
every date-`t` node no small bond perturbation is profitable, the Euler equation holds.
Hypotheses: `σ > 0`, positive prices and consumption, `N < 1`, a uniform lower bound
`m ≤ P_{t+1} C_{t+1}`, and a uniform modulus of continuity of next period's marginal utility
(automatic with finitely many states, `euler_necessary_finite`). -/
theorem euler_necessary {β σ ν : ℝ} {Q C N P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ)
    (hC : ∀ ω, 0 < C t ω) (hN : ∀ ω, N t ω < 1) (hP : ∀ ω, 0 < P t ω)
    (hN1 : ∀ ω, N (t + 1) ω < 1) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    {m : ℝ} (hm : 0 < m) (hmPC : ∀ ω, m ≤ P (t + 1) ω * C (t + 1) ω)
    (huc : ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω,
      |margUtilC σ ν (C (t + 1) ω + h / P (t + 1) ω) (N (t + 1) ω)
        - margUtilC σ ν (C (t + 1) ω) (N (t + 1) ω)| / P (t + 1) ω ≤ ε)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ ν Q C N P t δ ω) 0) :
    EulerEq 𝔼 β σ ν Q C N P t := by
  intro ω
  have hG := uniform_of_concave (u := fun ω' c => periodUtility σ ν c (N (t + 1) ω'))
    (D := fun ω' c => margUtilC σ ν c (N (t + 1) ω')) hm hP1 hmPC
    (fun ω' x hx => hasDerivAt_periodUtility_C σ ν hx (hN1 ω'))
    (fun ω' => margUtilC_antitoneOn hσ ν (hN1 ω')) huc
  have hin : HasDerivAt (fun δ : ℝ => C t ω - Q t ω * δ / P t ω) (-(Q t ω / P t ω)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (Q t ω)).div_const (P t ω)).const_sub (C t ω)
    simpa [mul_div_assoc] using this
  have hu : HasDerivAt (fun c => periodUtility σ ν c (N t ω)) (margUtilC σ ν (C t ω) (N t ω))
      (C t ω - Q t ω * 0 / P t ω) := by
    simpa using hasDerivAt_periodUtility_C σ ν (hC ω) (hN ω)
  have h := euler_necessary_generic 𝔼 (hu.comp 0 hin) hG t ω (hopt ω)
  have hP0 := (hP ω).ne'
  have e : Q t ω * margUtilC σ ν (C t ω) (N t ω) / P t ω
      = -(margUtilC σ ν (C t ω) (N t ω) * -(Q t ω / P t ω)) := by
    field_simp
  rw [e]
  linarith

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1 (**necessity**, finitely many states): no
profitable small bond perturbation at any date-`t` node implies the Euler equation. -/
theorem euler_necessary_finite [Finite Ω] {β σ ν : ℝ} {Q C N P : ℕ → Ω → ℝ} {t : ℕ}
    (hσ : 0 < σ) (hC : ∀ ω, 0 < C t ω) (hN : ∀ ω, N t ω < 1) (hP : ∀ ω, 0 < P t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hN1 : ∀ ω, N (t + 1) ω < 1) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ ν Q C N P t δ ω) 0) :
    EulerEq 𝔼 β σ ν Q C N P t := by
  obtain ⟨m, hm, hmPC⟩ : ∃ m, 0 < m ∧ ∀ ω, m ≤ P (t + 1) ω * C (t + 1) ω := by
    rcases isEmpty_or_nonempty Ω with hΩ | hΩ
    · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
    · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P (t + 1) ω * C (t + 1) ω
      exact ⟨_, mul_pos (hP1 ω₀) (hC1 ω₀), h₀⟩
  exact euler_necessary 𝔼 hσ hC hN hP hN1 hP1 hm hmPC
    (uniformCont_of_finite (D := fun ω' c => margUtilC σ ν c (N (t + 1) ω'))
      (fun ω' => margUtilC_continuousAt σ ν (hC1 ω') (hN1 ω'))) hopt

/-- Galí (2015), eq. (5), p. 19, for Exercise 2.1 (**sufficiency**, by concavity in
consumption): if the Euler equation holds at date `t` and `β ≥ 0`, no feasible bond
perturbation `δ` (one keeping consumption positive) raises expected utility at any node. -/
theorem euler_sufficient {β σ ν : ℝ} {Q C N P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hC : ∀ ω, 0 < C t ω) (hN : ∀ ω, N t ω < 1) (hP : ∀ ω, 0 < P t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hN1 : ∀ ω, N (t + 1) ω < 1)
    (heul : EulerEq 𝔼 β σ ν Q C N P t) {δ : ℝ} (ω : Ω)
    (hfeas : 0 < C t ω - Q t ω * δ / P t ω)
    (hfeas1 : ∀ ω', 0 < C (t + 1) ω' + δ / P (t + 1) ω') :
    perturbedValue 𝔼 β σ ν Q C N P t δ ω ≤ perturbedValue 𝔼 β σ ν Q C N P t 0 ω := by
  have hP0 := (hP ω).ne'
  have hf := tangent_of_deriv (hC ω) hfeas
    (fun x hx => hasDerivAt_periodUtility_C σ ν hx (hN ω)) (margUtilC_antitoneOn hσ ν (hN ω))
  have hG : ∀ ω', periodUtility σ ν (C (t + 1) ω' + δ / P (t + 1) ω') (N (t + 1) ω')
      ≤ periodUtility σ ν (C (t + 1) ω' + 0 / P (t + 1) ω') (N (t + 1) ω')
        + δ * (margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') := by
    intro ω'
    have := tangent_of_deriv (hC1 ω') (hfeas1 ω')
      (fun x hx => hasDerivAt_periodUtility_C σ ν hx (hN1 ω'))
      (margUtilC_antitoneOn hσ ν (hN1 ω'))
    rw [zero_div, add_zero]
    have e : margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω')
        * (C (t + 1) ω' + δ / P (t + 1) ω' - C (t + 1) ω')
        = δ * (margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') := by ring
    linarith
  have hfoc : -(margUtilC σ ν (C t ω) (N t ω) * Q t ω / P t ω)
      + β * 𝔼.E t (fun ω' => margUtilC σ ν (C (t + 1) ω') (N (t + 1) ω') / P (t + 1) ω') ω
      = 0 := by
    have := heul ω
    rw [← this]
    ring
  have h := euler_sufficient_generic 𝔼
    (f := fun δ => periodUtility σ ν (C t ω - Q t ω * δ / P t ω) (N t ω))
    (G := fun δ ω' => periodUtility σ ν (C (t + 1) ω' + δ / P (t + 1) ω') (N (t + 1) ω'))
    (a := -(margUtilC σ ν (C t ω) (N t ω) * Q t ω / P t ω)) hβ ?_ hG t ω hfoc
  · exact h
  · simp only [mul_zero, zero_div, sub_zero]
    have e : margUtilC σ ν (C t ω) (N t ω) * (C t ω - Q t ω * δ / P t ω - C t ω)
        = δ * -(margUtilC σ ν (C t ω) (N t ω) * Q t ω / P t ω) := by ring
    linarith

/-! ### Log forms of the Euler equation -/

/-- Galí (2015), Exercise 2.1 and App. 2.1, p. 44: the Euler moment at node `ω` in logs,
`E_t[exp(i_t − ρ − σ(c_{t+1} − c_t) − (p_{t+1} − p_t) + ν(1−σ)(ℓ_{t+1} − ℓ_t))]` with
`ℓ = log(1 − N)`; date-`t` values enter as numbers. -/
noncomputable def eulerMoment (σ ν ρ : ℝ) (i c p ℓ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
    - (p (t + 1) ω' - p t ω) + ν * (1 - σ) * (ℓ (t + 1) ω' - ℓ t ω))) ω

/-- Galí (2015), Exercise 2.1: in logs, `U_C(e^c, 1 − e^ℓ) = exp(−σ c + ν(1 − σ) ℓ)`. -/
theorem margUtilC_exp (σ ν c ℓ : ℝ) :
    margUtilC σ ν (Real.exp c) (1 - Real.exp ℓ) = Real.exp (-σ * c + ν * (1 - σ) * ℓ) := by
  unfold margUtilC
  rw [sub_sub_cancel, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Galí (2015), Exercise 2.1 (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`,
`P = e^p`, `1 − N = e^ℓ`, the Euler equation at date `t` holds iff the Euler moment equals one
at every node. -/
theorem eulerEq_iff_moment (σ ν ρ : ℝ) (i c p ℓ : ℕ → Ω → ℝ) (t : ℕ) :
    EulerEq 𝔼 (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω)) (fun t ω => Real.exp (c t ω))
        (fun t ω => 1 - Real.exp (ℓ t ω)) (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, eulerMoment 𝔼 σ ν ρ i c p ℓ t ω = 1 := by
  set G : Ω → ℝ := fun ω' =>
    Real.exp (-σ * c (t + 1) ω' + ν * (1 - σ) * ℓ (t + 1) ω' - p (t + 1) ω') with hGdef
  have hmom : ∀ ω, eulerMoment 𝔼 σ ν ρ i c p ℓ t ω
      = Real.exp (i t ω - ρ + σ * c t ω + p t ω - ν * (1 - σ) * ℓ t ω) * 𝔼.E t G ω := by
    intro ω
    have hfun : (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
        - (p (t + 1) ω' - p t ω) + ν * (1 - σ) * (ℓ (t + 1) ω' - ℓ t ω)))
        = Real.exp (i t ω - ρ + σ * c t ω + p t ω - ν * (1 - σ) * ℓ t ω) • G := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hGdef]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [eulerMoment, hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  have hG : (fun ω' => margUtilC σ ν (Real.exp (c (t + 1) ω')) (1 - Real.exp (ℓ (t + 1) ω'))
      / Real.exp (p (t + 1) ω')) = G := by
    funext ω'
    rw [margUtilC_exp, hGdef, ← Real.exp_sub]
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [hmom ω, hG, margUtilC_exp, ← Real.exp_add, ← Real.exp_sub]
  set A := -i t ω + (-σ * c t ω + ν * (1 - σ) * ℓ t ω) - p t ω with hA
  have e : Real.exp (i t ω - ρ + σ * c t ω + p t ω - ν * (1 - σ) * ℓ t ω)
      = Real.exp (-ρ) * (Real.exp A)⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add, hA]
    congr 1
    ring
  rw [e]
  have hpos := Real.exp_pos A
  constructor
  · intro h
    rw [mul_assoc, mul_comm ((Real.exp A)⁻¹), ← mul_assoc, ← h, mul_inv_cancel₀ hpos.ne']
  · intro h
    field_simp at h
    linarith

/-- Galí (2015), Exercise 2.1 (**exact, perfect foresight**): the Euler equation holds at
date `t` iff `i_t − (p_{t+1} − p_t) − ρ = σ(c_{t+1} − c_t) − ν(1 − σ)(ℓ_{t+1} − ℓ_t)`,
`ℓ = log(1 − N)`. -/
theorem pf_eulerEq_iff (σ ν ρ : ℝ) (i c p ℓ : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ ν (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => 1 - Real.exp (ℓ t ω))
        (fun t ω => Real.exp (p t ω)) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ
        = σ * (c (t + 1) ω - c t ω) - ν * (1 - σ) * (ℓ (t + 1) ω - ℓ t ω) := by
  rw [eulerEq_iff_moment]
  refine forall_congr' fun ω => ?_
  simp only [eulerMoment, perfectForesight, LinearMap.id_apply]
  rw [← Real.exp_zero, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-! ### The first-order approximation under uncertainty -/

/-- Galí (2015), App. 2.1, p. 44 (uniform first-order expansion): if `ℓ` has derivative `ℓ'`
at `x`, then `ℓ(x + s b) − ℓ(x) − s b ℓ' = o(s)` uniformly over `|b| ≤ M`. -/
theorem uniform_comp_line {ℓ : ℝ → ℝ} {ℓ' x M : ℝ} (hℓ : HasDerivAt ℓ ℓ' x) (hM : 0 ≤ M) :
    ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ b : ℝ, |b| ≤ M →
      |ℓ (x + s * b) - ℓ x - s * b * ℓ'| ≤ ε * |s| := by
  intro ε hε
  have hM1 : 0 < M + 1 := by linarith
  have h := (Asymptotics.isLittleO_iff.1 (hasDerivAt_iff_isLittleO.1 hℓ))
    (div_pos hε hM1)
  obtain ⟨η, hη, hη'⟩ := Metric.eventually_nhds_iff.1 h
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < η / (M + 1) := by
    simpa using eventually_abs_sub_lt (0 : ℝ) (div_pos hη hM1)
  filter_upwards [hs] with s hs b hb
  have hsb : |s * b| ≤ |s| * (M + 1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
  have hd : dist (x + s * b) x < η := by
    rw [Real.dist_eq, add_sub_cancel_left]
    have := (lt_div_iff₀ hM1).1 hs
    linarith
  have h2 := hη' hd
  rw [add_sub_cancel_left, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul] at h2
  calc |ℓ (x + s * b) - ℓ x - s * b * ℓ'| ≤ ε / (M + 1) * |s * b| := h2
    _ ≤ ε / (M + 1) * (|s| * (M + 1)) := by gcongr
    _ = ε * |s| := by field_simp

/-- Galí (2015), App. 2.1, p. 44 (uniform first-order expansion of `exp`): if
`g(s) − s L = o(s)` uniformly, `g(0) = 0` and `L` is bounded, then
`exp(g(s)) − exp(g(0)) − s L = o(s)` uniformly. -/
theorem uniform_exp {g : ℝ → Ω → ℝ} {L : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hL : ∀ ω, |L ω| ≤ K)
    (hg0 : ∀ ω, g 0 ω = 0)
    (hg : ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ ω, |g s ω - s * L ω| ≤ ε * |s|) :
    ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ ω,
      |Real.exp (g s ω) - Real.exp (g 0 ω) - s * L ω| ≤ ε * |s| := by
  intro ε hε
  have hK1 : 0 < K + 1 := by linarith
  set r := min (1 / (K + 1)) (ε / (2 * (K + 1) ^ 2)) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hε1 : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
  have hs : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < r := by
    simpa using eventually_abs_sub_lt (0 : ℝ) hr0
  filter_upwards [hg _ hε1, hs] with s h1 h2 ω
  have h1 := h1 ω
  rw [hg0 ω, Real.exp_zero]
  have hm1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
  have hm2 : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  have hsL : |s * L ω| ≤ K * |s| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hL ω) (abs_nonneg s)
  have hs0 := abs_nonneg s
  have hgb : |g s ω| ≤ (K + 1) * |s| := by
    have := abs_sub_abs_le_abs_sub (g s ω) (s * L ω)
    nlinarith
  have hsr1 : |s| ≤ 1 / (K + 1) := h2.le.trans (min_le_left _ _)
  have hsr2 : |s| ≤ ε / (2 * (K + 1) ^ 2) := h2.le.trans (min_le_right _ _)
  have hg1 : |g s ω| ≤ 1 := by
    calc |g s ω| ≤ (K + 1) * |s| := hgb
      _ ≤ (K + 1) * (1 / (K + 1)) := by gcongr
      _ = 1 := by field_simp
  have hexp := Real.abs_exp_sub_one_sub_id_le hg1
  have hsq : g s ω ^ 2 ≤ ε / 2 * |s| := by
    calc g s ω ^ 2 = |g s ω| ^ 2 := (sq_abs _).symm
      _ ≤ ((K + 1) * |s|) ^ 2 := by gcongr
      _ = (K + 1) ^ 2 * |s| * |s| := by ring
      _ ≤ (K + 1) ^ 2 * (ε / (2 * (K + 1) ^ 2)) * |s| := by gcongr
      _ = ε / 2 * |s| := by field_simp
  have htri : |Real.exp (g s ω) - 1 - s * L ω|
      ≤ |Real.exp (g s ω) - 1 - g s ω| + |g s ω - s * L ω| := by
    have := abs_add_le (Real.exp (g s ω) - 1 - g s ω) (g s ω - s * L ω)
    rwa [show Real.exp (g s ω) - 1 - g s ω + (g s ω - s * L ω)
      = Real.exp (g s ω) - 1 - s * L ω by ring] at this
  nlinarith

/-- Galí (2015), Exercise 2.1 and App. 2.1, p. 44: the linearised Euler expression at node
`ω`, `î_t − σ(ĉ_{t+1} − ĉ_t) − (p̂_{t+1} − p̂_t) − ν(1 − σ)(N/(1 − N))(n̂_{t+1} − n̂_t)` as a
date-`t+1` random variable (date-`t` values enter as numbers). -/
noncomputable def linearisedEuler (σ ν Nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Ω → ℝ :=
  fun ω' => ih t ω - σ * (ch (t + 1) ω' - ch t ω) - (ph (t + 1) ω' - ph t ω)
    - ν * (1 - σ) * (Nbar / (1 - Nbar)) * (nh (t + 1) ω' - nh t ω)

/-- Galí (2015), Exercise 2.1: at `s = 0` the family of paths `i = ρ`, `c = c̄`, `p = p̄`,
`n = n̄` is a steady state: the Euler moment equals one. -/
theorem eulerMoment_family_zero (σ ν ρ cbar pbar nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    eulerMoment 𝔼 σ ν ρ (fun t ω => ρ + 0 * ih t ω) (fun t ω => cbar + 0 * ch t ω)
      (fun t ω => pbar + 0 * ph t ω)
      (fun t ω => Real.log (1 - Real.exp (nbar + 0 * nh t ω))) t ω = 1 := by
  simp [eulerMoment, 𝔼.const]

/-- Galí (2015), Exercise 2.1 and App. 2.1, p. 44 (**first-order log-linearisation of the
Euler equation under uncertainty**): along `i = ρ + s î`, `c = c̄ + s ĉ`, `p = p̄ + s p̂`,
`n = n̄ + s n̂` (bounded deviations, `N = e^{n̄} < 1`, `ℓ = log(1 − e^n)`), the Euler moment
has derivative `E_t[linearisedEuler]` at `s = 0`. -/
theorem hasDerivAt_moment_family (σ ν ρ cbar pbar nbar : ℝ) (hn : Real.exp nbar < 1)
    {ih ch ph nh : ℕ → Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t ω, |ih t ω| ≤ M ∧ |ch t ω| ≤ M ∧ |ph t ω| ≤ M ∧ |nh t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => eulerMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
        (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
        (fun t ω => Real.log (1 - Real.exp (nbar + s * nh t ω))) t ω)
      (𝔼.E t (linearisedEuler σ ν (Real.exp nbar) ih ch ph nh t ω) ω) 0 := by
  set ℓf : ℝ → ℝ := fun x => Real.log (1 - Real.exp x) with hℓf
  set ℓ' := -(Real.exp nbar / (1 - Real.exp nbar)) with hℓ'
  have hℓ : HasDerivAt ℓf ℓ' nbar := by
    have h := ((Real.hasDerivAt_exp nbar).const_sub 1).log (sub_pos.2 hn).ne'
    exact h.congr_deriv (by rw [hℓ']; ring)
  set κ := ν * (1 - σ) with hκ
  set d := nh t ω with hd
  set a : Ω → ℝ := fun ω' =>
    ih t ω - σ * (ch (t + 1) ω' - ch t ω) - (ph (t + 1) ω' - ph t ω) with ha
  set g : ℝ → Ω → ℝ := fun s ω' =>
    s * a ω' + κ * (ℓf (nbar + s * nh (t + 1) ω') - ℓf (nbar + s * d)) with hg
  set L := linearisedEuler σ ν (Real.exp nbar) ih ch ph nh t ω with hLdef
  have hL : ∀ ω', L ω' = a ω' + κ * ℓ' * (nh (t + 1) ω' - d) := fun ω' => by
    simp only [hLdef, linearisedEuler, ha, hℓ', hκ, hd]
    ring
  have hfun : ∀ s, eulerMoment 𝔼 σ ν ρ (fun t ω => ρ + s * ih t ω)
      (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
      (fun t ω => Real.log (1 - Real.exp (nbar + s * nh t ω))) t ω
      = 𝔼.E t (fun ω' => Real.exp (g s ω')) ω := by
    intro s
    unfold eulerMoment
    refine congrArg (fun F => 𝔼.E t F ω) (funext fun ω' => ?_)
    congr 1
    simp only [hg, ha, hκ, hℓf, hd]
    ring
  have hg0 : ∀ ω', g 0 ω' = 0 := by
    intro ω'
    simp [hg]
  have hgu : ∀ ε > 0, ∀ᶠ s in 𝓝 (0 : ℝ), ∀ ω', |g s ω' - s * L ω'| ≤ ε * |s| := by
    intro ε hε
    have hκ1 : 0 < 2 * |κ| + 1 := by positivity
    filter_upwards [uniform_comp_line hℓ hM (ε / (2 * |κ| + 1)) (div_pos hε hκ1)]
      with s hs ω'
    have h1 := hs (nh (t + 1) ω') (hb (t + 1) ω').2.2.2
    have h2 := hs d (hb t ω).2.2.2
    have e : g s ω' - s * L ω' = κ * ((ℓf (nbar + s * nh (t + 1) ω') - ℓf nbar
        - s * nh (t + 1) ω' * ℓ') - (ℓf (nbar + s * d) - ℓf nbar - s * d * ℓ')) := by
      rw [hL]
      simp only [hg]
      ring
    have hfrac : 2 * |κ| / (2 * |κ| + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) hκ1.le
    rw [e, abs_mul]
    calc |κ| * |ℓf (nbar + s * nh (t + 1) ω') - ℓf nbar - s * nh (t + 1) ω' * ℓ'
          - (ℓf (nbar + s * d) - ℓf nbar - s * d * ℓ')|
        ≤ |κ| * (ε / (2 * |κ| + 1) * |s| + ε / (2 * |κ| + 1) * |s|) := by
          gcongr
          exact (abs_sub _ _).trans (add_le_add h1 h2)
      _ = 2 * |κ| / (2 * |κ| + 1) * (ε * |s|) := by
          field_simp
          ring
      _ ≤ 1 * (ε * |s|) := mul_le_mul_of_nonneg_right hfrac (by positivity)
      _ = ε * |s| := one_mul _
  set K := M + |σ| * (2 * M) + 2 * M + |κ * ℓ'| * (2 * M) with hK
  have hLb : ∀ ω', |L ω'| ≤ K := by
    intro ω'
    obtain ⟨hi, hc0, hp0, hn0⟩ := hb t ω
    obtain ⟨-, hc1, hp1, hn1⟩ := hb (t + 1) ω'
    have hc : |ch (t + 1) ω' - ch t ω| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
    have hp : |ph (t + 1) ω' - ph t ω| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
    have hnn : |nh (t + 1) ω' - d| ≤ 2 * M := (abs_sub _ _).trans (by rw [hd]; linarith)
    have h3 : |σ * (ch (t + 1) ω' - ch t ω)| ≤ |σ| * (2 * M) := by
      rw [abs_mul]; gcongr
    have h4 : |κ * ℓ' * (nh (t + 1) ω' - d)| ≤ |κ * ℓ'| * (2 * M) := by
      rw [abs_mul]; gcongr
    have ha' : |a ω'| ≤ M + |σ| * (2 * M) + 2 * M := by
      have e1 := abs_sub (ih t ω - σ * (ch (t + 1) ω' - ch t ω)) (ph (t + 1) ω' - ph t ω)
      have e2 := abs_sub (ih t ω) (σ * (ch (t + 1) ω' - ch t ω))
      simp only [ha]
      linarith
    rw [hL]
    have := abs_add_le (a ω') (κ * ℓ' * (nh (t + 1) ω' - d))
    linarith
  have hK0 : 0 ≤ K := by positivity
  have hexp := uniform_exp hK0 hLb hg0 hgu
  have hder := hasDerivAt_E_of_uniform 𝔼 (F := fun s ω' => Real.exp (g s ω')) hexp t ω
  exact hder.congr_of_eventuallyEq (Eventually.of_forall fun s => hfun s)

/-- Galí (2015), Exercise 2.1: the expectation of the linearised Euler expression,
`î_t − σ(E_t ĉ_{t+1} − ĉ_t) − (E_t p̂_{t+1} − p̂_t) − ν(1 − σ)(N/(1 − N))(E_t n̂_{t+1} − n̂_t)`,
by linearity of `E_t` only. -/
theorem E_linearisedEuler (σ ν Nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    𝔼.E t (linearisedEuler σ ν Nbar ih ch ph nh t ω) ω
      = ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
        - ν * (1 - σ) * (Nbar / (1 - Nbar)) * (𝔼.E t (nh (t + 1)) ω - nh t ω) := by
  set k := ν * (1 - σ) * (Nbar / (1 - Nbar)) with hk
  have hfun : linearisedEuler σ ν Nbar ih ch ph nh t ω
      = (fun _ => ih t ω + σ * ch t ω + ph t ω + k * nh t ω) + (-σ) • ch (t + 1)
        + (-1 : ℝ) • ph (t + 1) + (-k) • nh (t + 1) := by
    funext ω'
    simp only [linearisedEuler, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk]
    ring
  rw [hfun]
  simp only [map_add, map_smul, 𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), Exercise 2.1 (**log-linear Euler equation**): for `σ ≠ 0` the derivative of
the Euler moment vanishes at node `ω` iff
`ĉ_t = E_t ĉ_{t+1} − σ^{−1}(î_t − E_t π̂_{t+1}) + σ^{−1} ν(1 − σ)(N/(1 − N))(E_t n̂_{t+1} − n̂_t)`,
`π̂_{t+1} = p̂_{t+1} − p̂_t`. -/
theorem linearisedEuler_zero_iff {σ : ℝ} (hσ : σ ≠ 0) (ν Nbar : ℝ) (ih ch ph nh : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    𝔼.E t (linearisedEuler σ ν Nbar ih ch ph nh t ω) ω = 0 ↔
      ch t ω = 𝔼.E t (ch (t + 1)) ω - σ⁻¹ * (ih t ω - (𝔼.E t (ph (t + 1)) ω - ph t ω))
        + σ⁻¹ * (ν * (1 - σ) * (Nbar / (1 - Nbar))) * (𝔼.E t (nh (t + 1)) ω - nh t ω) := by
  rw [E_linearisedEuler]
  set R := 𝔼.E t (ch (t + 1)) ω - σ⁻¹ * (ih t ω - (𝔼.E t (ph (t + 1)) ω - ph t ω))
    + σ⁻¹ * (ν * (1 - σ) * (Nbar / (1 - Nbar))) * (𝔼.E t (nh (t + 1)) ω - nh t ω) with hR
  have key : ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
      - ν * (1 - σ) * (Nbar / (1 - Nbar)) * (𝔼.E t (nh (t + 1)) ω - nh t ω)
      = -σ * (R - ch t ω) := by
    rw [hR]
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have := (mul_eq_zero.1 h).resolve_left (neg_ne_zero.2 hσ)
    linarith
  · intro h
    rw [← h, sub_self, mul_zero]

end Gali.ClassicalMonetaryModel.Ex2_1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.2: alternative interest rules for the classical economy

Galí (2015), Chapter 2, Exercise 2.2, pp. 46–47. Output `y_t` and the real rate
`r_t ≡ i_t − E_t π_{t+1} = ρ + σ E_t Δy_{t+1}` are determined independently of monetary policy
(§2.3, pp. 23–24), so they are taken as exogenous bounded adapted processes. The equilibrium
conditions used are the Fisher equation `i_t = r_t + E_t π_{t+1}` (`Fisher`, in price form
`i_t = r_t + E_t p_{t+1} − p_t`, `FisherP`) and the money demand
`m_t − p_t = y_t − η i_t + ε^m_t`.

## a. Strict inflation targeting

* (i) `strictIT_solves`: under `i_t = r_t + π* + φ_π(π_t − π*)` the path `π_t ≡ π*` is an
  equilibrium; `strictIT_unique`: for `|φ_π| > 1` it is the only bounded one, so this rule
  guarantees full stabilisation. The plain rule `i_t = r_t + π*` (`φ_π = 0`) does not:
  `strictIT_not_unique` gives a second bounded equilibrium whenever `|φ_π| ≤ 1`, and
  `strictIT_sunspot` shows that `π* + ξ` is an equilibrium for every martingale-difference `ξ`
  when `φ_π = 0`.
* (ii) `strictIT_money_growth`: the money growth this requires,
  `Δm_t = π* + Δy_t − η Δr_t + Δε^m_t`.
* (iii) `constMoneyGrowth_inflation`: under `Δm_t = π*`,
  `π_t = π* − Δy_t + η Δi_t − Δε^m_t`; `constMoneyGrowth_not_stabilising`: unless
  `y − η r + ε^m` happens to be constant over time, inflation is not stabilised.

## b. Price-level targeting

* (i) Rule `i_t = ρ + π* + φ_p (p_t − p*_t)`, `p*_t = p*_0 + π* t`, `φ_p > 0`.
  `plEquilibrium_iff`: in terms of `p̂_t = p_t − p*_t` the equilibrium is
  `p̂_t = (1 + φ_p)^{−1} E_t p̂_{t+1} + (1 + φ_p)^{−1} r̂_t`, `r̂_t = r_t − ρ`.
  `plEquilibrium_unique_iff`: among price paths with `p − p*` bounded the equilibrium is
  unique, `p̂_t = ∑_{k ≥ 0} (1 + φ_p)^{−(k+1)} E_t r̂_{t+k}`; `plEquilibrium_exists`: it exists.
  `pl_ar1`: for AR(1) `r̂`, `p̂_t = r̂_t/(1 + φ_p − ρ_r)`.
  `hint_constant_target_unbounded` (erratum C2-7): the hint's `p_t − p*` with a constant `p*`
  is unbounded when `π* ≠ 0`; the deviation must be taken from the time-varying `p*_t`.
* (ii) Money rule `Δm_t = π*`, `m_0 = p*_0`, so `m_t = p*_t` (`moneyPath_eq_pstar`).
  `moneyEquilibrium_iff`: `p̂_t = (η/(1+η)) E_t p̂_{t+1} + u_t` with
  `u_t = (η(r_t + π*) − y_t − ε^m_t)/(1 + η)`; `moneyEquilibrium_unique_iff`,
  `moneyEquilibrium_exists`: the unique equilibrium is the forward series (`η ≥ 0`).
* (iii) `moneyRule_as_interestRule`: money market clearing with `m_t = p*_t` is exactly the
  interest rule `i_t = ψ (p_t − p*_t) + u_t` with `ψ = 1/η`, `u_t = (y_t + ε^m_t)/η`;
  `moneyEquilibrium_iff_interestRule`: the two regimes have the same equilibria.
* (iv) is a verbal discussion and is not formalised.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_2

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### General lemmas -/

/-- Galí (2015), p. 25 (expectations of a known constant): `E_t (x − c) = E_t x − c`. -/
theorem E_sub_const (t : ℕ) (x : Ω → ℝ) (c : ℝ) :
    𝔼.E t (fun ω => x ω - c) = fun ω => 𝔼.E t x ω - c := by
  have h : (fun ω => x ω - c) = x - fun _ => c := rfl
  rw [h, map_sub, 𝔼.const]
  rfl

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward series of a bounded adapted forcing
process is itself adapted (it is known at the date it refers to). -/
theorem forwardSeries_adapted {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  have h := 𝔼.forwardSeries_solves ha0 ha1 hu hadapt t
  conv_lhs => rw [h]
  rw [map_add, map_smul, 𝔼.E_E_self, hadapt t, ← h]

/-- Galí (2015), (25) p. 27: the forward series of `a u` is
`∑_{k ≥ 0} a^{k+1} E_t u_{t+k}`. -/
theorem forwardSeries_smul_apply (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun t => a • u t) t ω = ∑' k, a ^ (k + 1) * 𝔼.E t (u (t + k)) ω := by
  unfold ExpectationSystem.forwardSeries
  refine tsum_congr fun k => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-! ### a. Strict inflation targeting -/

/-- Galí (2015), Exercise 2.2, p. 46: the Fisher equation `i_t = r_t + E_t π_{t+1}`
(definition of the real rate). -/
def Fisher (r i infl : ℕ → Ω → ℝ) : Prop := ∀ t, i t = r t + 𝔼.E t (infl (t + 1))

/-- Galí (2015), Exercise 2.2(a)(i), p. 46: the strict inflation-targeting rule
`i_t = r_t + π* + φ_π (π_t − π*)`. -/
def StrictITRule (φπ πstar : ℝ) (r i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i t ω = r t ω + πstar + φπ * (infl t ω - πstar)

/-- Galí (2015), Exercise 2.2(a)(i), p. 46: under the rule `i_t = r_t + π* + φ_π(π_t − π*)`
the constant path `π_t = π*`, `i_t = r_t + π*` is an equilibrium (for every `φ_π`). -/
theorem strictIT_solves (φπ πstar : ℝ) (r : ℕ → Ω → ℝ) :
    Fisher 𝔼 r (fun t ω => r t ω + πstar) (fun _ _ => πstar) ∧
      StrictITRule φπ πstar r (fun t ω => r t ω + πstar) (fun _ _ => πstar) := by
  refine ⟨fun t => ?_, fun t ω => by ring⟩
  rw [𝔼.const]
  rfl

/-- Galí (2015), Exercise 2.2(a)(i), p. 46 (**full stabilisation**): with `|φ_π| > 1` every
bounded equilibrium under the rule `i_t = r_t + π* + φ_π(π_t − π*)` has `π_t = π*`. -/
theorem strictIT_unique {φπ πstar : ℝ} (hφ : 1 < |φπ|) {r i infl : ℕ → Ω → ℝ}
    (hfis : Fisher 𝔼 r i infl) (hrule : StrictITRule φπ πstar r i infl)
    (hb : BoundedProc infl) : ∀ t ω, infl t ω = πstar := by
  have hφ0 : φπ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hφ
    linarith
  set z : ℕ → Ω → ℝ := fun t ω => infl t ω - πstar with hz
  have hzeq : ∀ t, z t = φπ⁻¹ • 𝔼.E t (z (t + 1)) + 0 := by
    intro t
    funext ω
    have h1 := congrFun (hfis t) ω
    have h2 := hrule t ω
    have hE : 𝔼.E t (z (t + 1)) ω = 𝔼.E t (infl (t + 1)) ω - πstar :=
      congrFun (E_sub_const 𝔼 t (infl (t + 1)) πstar) ω
    change infl t ω - πstar = φπ⁻¹ * 𝔼.E t (z (t + 1)) ω + 0
    rw [hE]
    simp only [Pi.add_apply] at h1
    field_simp
    linarith
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = φπ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have ha : |φπ⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hφ
  obtain ⟨M, hM⟩ := hb
  have hzb : BoundedProc z := ⟨M + |πstar|, fun t ω => (abs_sub _ _).trans (by linarith [hM t ω])⟩
  have := 𝔼.forward_unique ha hzeq h0 hzb ⟨0, fun t ω => by simp⟩
  intro t ω
  have h := congrFun (congrFun this t) ω
  simp only [hz, Pi.zero_apply] at h
  linarith

/-- Galí (2015), Exercise 2.2(a)(i), p. 46 (**the rule `i_t = r_t + π*` does not guarantee
stabilisation**): for `|φ_π| ≤ 1` the deterministic path `π_t = π* + φ_πᵗ` is a second bounded
equilibrium, different from `π_t ≡ π*`. -/
theorem strictIT_not_unique [Nonempty Ω] {φπ : ℝ} (hφ : |φπ| ≤ 1) (πstar : ℝ)
    (r : ℕ → Ω → ℝ) :
    Fisher 𝔼 r (fun t ω => r t ω + πstar + φπ * φπ ^ t) (fun t _ => πstar + φπ ^ t) ∧
      StrictITRule φπ πstar r (fun t ω => r t ω + πstar + φπ * φπ ^ t)
        (fun t _ => πstar + φπ ^ t) ∧
      BoundedProc (fun t (_ : Ω) => πstar + φπ ^ t) ∧
      𝔼.Adapted (fun t (_ : Ω) => πstar + φπ ^ t) ∧
      (fun t (_ : Ω) => πstar + φπ ^ t) ≠ fun _ _ => πstar := by
  refine ⟨fun t => ?_, fun t ω => by ring, ⟨|πstar| + 1, fun t ω => ?_⟩,
    fun t => 𝔼.const t _, fun h => ?_⟩
  · rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply]
    ring
  · refine (abs_add_le _ _).trans ?_
    rw [abs_pow]
    linarith [pow_le_one₀ (abs_nonneg φπ) hφ (n := t)]
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp at this

/-- Galí (2015), Exercise 2.2(a)(i) and §2.4.1, pp. 25–26 (**sunspots** under
`i_t = r_t + π*`): for every bounded adapted `ξ` with `E_t ξ_{t+1} = 0`, the path
`π_t = π* + ξ_t` is an equilibrium of the rule with `φ_π = 0`. -/
theorem strictIT_sunspot (πstar : ℝ) (r ξ : ℕ → Ω → ℝ) (hξ : ∀ t, 𝔼.E t (ξ (t + 1)) = 0) :
    Fisher 𝔼 r (fun t ω => r t ω + πstar) (fun t ω => πstar + ξ t ω) ∧
      StrictITRule 0 πstar r (fun t ω => r t ω + πstar) (fun t ω => πstar + ξ t ω) := by
  refine ⟨fun t => ?_, fun t ω => by ring⟩
  have h : (fun ω => πstar + ξ (t + 1) ω) = (fun _ => πstar) + ξ (t + 1) := rfl
  change (fun ω => r t ω + πstar) = r t + 𝔼.E t (fun ω => πstar + ξ (t + 1) ω)
  rw [h, map_add, 𝔼.const, hξ t]
  funext ω
  simp

/-- Galí (2015), Exercise 2.2(a)(ii), p. 46: with `π_t ≡ π*` (so `p_{t+1} = p_t + π*`) and
`i_t = r_t + π*`, money demand `m_t = p_t + y_t − η i_t + ε^m_t` implies
`Δm_{t+1} = π* + Δy_{t+1} − η Δr_{t+1} + Δε^m_{t+1}`. -/
theorem strictIT_money_growth {η πstar : ℝ} {r y ε p m i : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p (t + 1) ω = p t ω + πstar) (hi : ∀ t ω, i t ω = r t ω + πstar)
    (hmd : ∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω) (t : ℕ) (ω : Ω) :
    m (t + 1) ω - m t ω = πstar + (y (t + 1) ω - y t ω) - η * (r (t + 1) ω - r t ω)
      + (ε (t + 1) ω - ε t ω) := by
  have h1 := hmd t ω
  have h2 := hmd (t + 1) ω
  rw [hi] at h1 h2
  rw [hp] at h2
  linarith

/-- Galí (2015), Exercise 2.2(a)(iii), p. 46: under constant money growth `Δm_t = π*`, money
demand gives `π_{t+1} = π* − Δy_{t+1} + η Δi_{t+1} − Δε^m_{t+1}`, where
`π_{t+1} = p_{t+1} − p_t`. -/
theorem constMoneyGrowth_inflation {η πstar : ℝ} {y ε p m i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar)
    (hmd : ∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω) (t : ℕ) (ω : Ω) :
    p (t + 1) ω - p t ω = πstar - (y (t + 1) ω - y t ω) + η * (i (t + 1) ω - i t ω)
      - (ε (t + 1) ω - ε t ω) := by
  have h1 := hmd t ω
  have h2 := hmd (t + 1) ω
  have h3 := hm t ω
  linarith

/-- Galí (2015), Exercise 2.2(a)(iii), p. 46 (**why constant money growth fails**): if under
`Δm_t = π*` inflation were constant at `π*` (with the Fisher equation, so `i_t = r_t + π*`),
then `y_t − η r_t + ε^m_t` would be constant over time. Hence whenever
`Δy_{t+1} − η Δr_{t+1} + Δε^m_{t+1} ≠ 0` at some date and state, inflation is not stabilised. -/
theorem constMoneyGrowth_not_stabilising {η πstar : ℝ} {r y ε p m i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar)
    (hmd : ∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω)
    (hfis : ∀ t ω, i t ω = r t ω + 𝔼.E t (fun ω' => p (t + 1) ω' - p t ω') ω)
    {t : ℕ} {ω : Ω}
    (hshock : (y (t + 1) ω - y t ω) - η * (r (t + 1) ω - r t ω) + (ε (t + 1) ω - ε t ω) ≠ 0) :
    ¬ ∀ s ω', p (s + 1) ω' - p s ω' = πstar := by
  intro hπ
  have hi : ∀ s ω', i s ω' = r s ω' + πstar := by
    intro s ω'
    rw [hfis s ω']
    have : (fun ω' => p (s + 1) ω' - p s ω') = fun _ => πstar := funext fun ω' => hπ s ω'
    rw [this, 𝔼.const]
  have h := constMoneyGrowth_inflation hm hmd t ω
  rw [hπ t ω, hi, hi] at h
  apply hshock
  linarith

/-! ### b(i). Price-level targeting through an interest rule -/

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: the price-level target `p*_t = p*_0 + π* t`. -/
def pstar (p0 πstar : ℝ) (t : ℕ) : ℝ := p0 + πstar * t

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: the target grows at rate `π*`. -/
theorem pstar_succ (p0 πstar : ℝ) (t : ℕ) :
    pstar p0 πstar (t + 1) = pstar p0 πstar t + πstar := by
  simp only [pstar]
  push_cast
  ring

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: the deviation of the price level from target,
`p̂_t = p_t − p*_t`. -/
def devPL (p0 πstar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => p t ω - pstar p0 πstar t

/-- Galí (2015), Exercise 2.2, p. 46: the Fisher equation in price form,
`i_t = r_t + E_t p_{t+1} − p_t`. -/
def FisherP (r p i : ℕ → Ω → ℝ) : Prop := ∀ t, i t = r t + 𝔼.E t (p (t + 1)) - p t

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: equilibrium under the price-level rule
`i_t = ρ + π* + φ_p (p_t − p*_t)`. -/
def PLEquilibrium (φp ρ πstar p0 : ℝ) (r p i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, i t ω = ρ + πstar + φp * devPL p0 πstar p t ω) ∧ FisherP 𝔼 r p i

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: `E_t p̂_{t+1} = E_t p_{t+1} − p*_{t+1}`. -/
theorem E_devPL (p0 πstar : ℝ) (p : ℕ → Ω → ℝ) (t s : ℕ) (ω : Ω) :
    𝔼.E t (devPL p0 πstar p s) ω = 𝔼.E t (p s) ω - pstar p0 πstar s := by
  have := congrFun (E_sub_const 𝔼 t (p s) (pstar p0 πstar s)) ω
  exact this

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**reduced form**): for `φ_p > −1`, the equilibrium
conditions under the price-level rule are equivalent to the rule together with
`p̂_t = (1 + φ_p)^{−1} E_t p̂_{t+1} + (1 + φ_p)^{−1} (r_t − ρ)`. -/
theorem plEquilibrium_iff {φp ρ πstar p0 : ℝ} (hφ : 0 < 1 + φp) (r p i : ℕ → Ω → ℝ) :
    PLEquilibrium 𝔼 φp ρ πstar p0 r p i ↔
      (∀ t ω, i t ω = ρ + πstar + φp * devPL p0 πstar p t ω) ∧
      ∀ t, devPL p0 πstar p t = (1 + φp)⁻¹ • 𝔼.E t (devPL p0 πstar p (t + 1))
        + (1 + φp)⁻¹ • fun ω => r t ω - ρ := by
  unfold PLEquilibrium FisherP
  refine and_congr_right fun hrule => forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, E_devPL, pstar_succ]
  rw [hrule t ω]
  simp only [devPL]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**the unique equilibrium price level**): for
`φ_p > 0`, bounded adapted `r̂_t = r_t − ρ`, and an adapted price path with `p − p*` bounded,
the economy is in equilibrium iff `i` follows the rule and
`p_t − p*_t = ∑_{k ≥ 0} (1 + φ_p)^{−(k+1)} E_t r̂_{t+k}`. -/
theorem plEquilibrium_unique_iff {φp ρ πstar p0 M : ℝ} (hφ : 0 < φp) {r p i : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω - ρ| ≤ M) (hra : 𝔼.Adapted r) (hpb : BoundedProc (devPL p0 πstar p)) :
    PLEquilibrium 𝔼 φp ρ πstar p0 r p i ↔
      (∀ t ω, i t ω = ρ + πstar + φp * devPL p0 πstar p t ω) ∧
      ∀ t ω, devPL p0 πstar p t ω
        = ∑' k, ((1 + φp)⁻¹) ^ (k + 1) * 𝔼.E t (fun ω' => r (t + k) ω' - ρ) ω := by
  set a := (1 + φp)⁻¹ with ha
  have h1 : 0 < 1 + φp := by linarith
  have ha0 : 0 ≤ a := inv_nonneg.2 h1.le
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  set rh : ℕ → Ω → ℝ := fun t ω => r t ω - ρ with hrh
  have hrha : 𝔼.Adapted rh := fun t => by
    rw [hrh]
    simp only
    rw [E_sub_const, hra t]
  have hu : ∀ t ω, |(fun t => a • rh t) t ω| ≤ a * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hr t ω) ha0
  have hua : 𝔼.Adapted (fun t => a • rh t) := fun t => by rw [map_smul, hrha t]
  rw [plEquilibrium_iff 𝔼 h1]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h t ω
    have heq := 𝔼.eq_forwardSeries ha0 ha1 hu hua h hpb
    rw [heq, forwardSeries_smul_apply]
  · intro h t
    have heq : devPL p0 πstar p = 𝔼.forwardSeries a (fun t => a • rh t) := by
      funext s ω
      rw [h s ω, forwardSeries_smul_apply]
    rw [heq]
    exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**existence**): for `φ_p > 0` and bounded adapted
`r̂`, the price path `p_t = p*_t + ∑_{k ≥ 0} (1 + φ_p)^{−(k+1)} E_t r̂_{t+k}` with `i` given by
the rule is an equilibrium, adapted, with `p − p*` bounded. -/
theorem plEquilibrium_exists {φp ρ πstar p0 M : ℝ} (hφ : 0 < φp) {r : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω - ρ| ≤ M) (hra : 𝔼.Adapted r) :
    ∃ p i : ℕ → Ω → ℝ, PLEquilibrium 𝔼 φp ρ πstar p0 r p i ∧ 𝔼.Adapted p ∧ 𝔼.Adapted i ∧
      BoundedProc (devPL p0 πstar p) := by
  set a := (1 + φp)⁻¹ with ha
  have h1 : 0 < 1 + φp := by linarith
  have ha0 : 0 ≤ a := inv_nonneg.2 h1.le
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  set rh : ℕ → Ω → ℝ := fun t ω => r t ω - ρ with hrh
  have hrha : 𝔼.Adapted rh := fun t => by
    rw [hrh]
    simp only
    rw [E_sub_const, hra t]
  have hu : ∀ t ω, |(fun t => a • rh t) t ω| ≤ a * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hr t ω) ha0
  have hua : 𝔼.Adapted (fun t => a • rh t) := fun t => by rw [map_smul, hrha t]
  set F := 𝔼.forwardSeries a (fun t => a • rh t) with hF
  have hFa := forwardSeries_adapted 𝔼 ha0 ha1 hu hua
  set p : ℕ → Ω → ℝ := fun t ω => pstar p0 πstar t + F t ω with hp
  have hdev : devPL p0 πstar p = F := by
    funext t ω
    simp [devPL, hp]
  refine ⟨p, fun t ω => ρ + πstar + φp * devPL p0 πstar p t ω, ?_, ?_, ?_, ?_⟩
  · rw [plEquilibrium_iff 𝔼 h1]
    refine ⟨fun t ω => rfl, fun t => ?_⟩
    rw [hdev]
    exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t
  · intro t
    have : p t = (fun _ => pstar p0 πstar t) + F t := rfl
    rw [this, map_add, 𝔼.const, hFa t]
  · intro t
    have : (fun ω => ρ + πstar + φp * devPL p0 πstar p t ω)
        = (fun _ => ρ + πstar) + φp • F t := by
      funext ω
      simp [hdev]
    change 𝔼.E t (fun ω => ρ + πstar + φp * devPL p0 πstar p t ω)
      = fun ω => ρ + πstar + φp * devPL p0 πstar p t ω
    rw [this, map_add, map_smul, 𝔼.const, hFa t]
  · rw [hdev]
    exact 𝔼.forwardSeries_bounded ha0 ha1 hu

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**AR(1) real rate**): if `r̂_t = r_t − ρ` is a
bounded AR(1) process with persistence `ρ_r`, `|ρ_r| ≤ 1`, the unique bounded equilibrium
deviation from target is `p̂_t = r̂_t/(1 + φ_p − ρ_r)`. -/
theorem pl_ar1 {φp ρ πstar p0 ρr : ℝ} (hφ : 0 < φp) (hρr : |ρr| ≤ 1) {r p i : ℕ → Ω → ℝ}
    (har : 𝔼.IsAR1 ρr (fun t ω => r t ω - ρ)) (hrb : BoundedProc fun t ω => r t ω - ρ)
    (hpb : BoundedProc (devPL p0 πstar p)) (heq : PLEquilibrium 𝔼 φp ρ πstar p0 r p i)
    (t : ℕ) (ω : Ω) :
    devPL p0 πstar p t ω = (r t ω - ρ) / (1 + φp - ρr) := by
  set a := (1 + φp)⁻¹ with ha
  have h1 : 0 < 1 + φp := by linarith
  have ha0 : 0 ≤ a := inv_nonneg.2 h1.le
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hρ1 : ρr ≤ 1 := (le_abs_self ρr).trans hρr
  have hden : 0 < 1 + φp - ρr := by linarith
  set rh : ℕ → Ω → ℝ := fun t ω => r t ω - ρ with hrh
  have har' : 𝔼.IsAR1 ρr (fun t => a • rh t) :=
    ⟨fun t => by rw [map_smul, har.1 t], fun t => by rw [map_smul, har.2 t, smul_comm]⟩
  have h1a : 1 - a * ρr ≠ 0 := by
    have : 1 - a * ρr = (1 + φp - ρr) / (1 + φp) := by
      rw [ha]
      field_simp
    rw [this]
    exact (div_pos hden h1).ne'
  have hsol := 𝔼.forward_ar1_solves h1a har'
  have h2 := ((plEquilibrium_iff 𝔼 h1 r p i).1 heq).2
  obtain ⟨M, hM⟩ := hrb
  have hb2 : BoundedProc fun t => (1 - a * ρr)⁻¹ • (fun t => a • rh t) t :=
    ⟨|(1 - a * ρr)⁻¹| * (a * M), fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha0]
      gcongr
      exact hM t ω⟩
  have hu := 𝔼.forward_unique (u := fun t => a • rh t) (by rwa [abs_of_nonneg ha0]) h2
    hsol hpb hb2
  rw [hu]
  simp only [Pi.smul_apply, smul_eq_mul, hrh, ha]
  field_simp

/-- Galí (2015), Exercise 2.2(b)(i), p. 47, erratum C2-7: the hint's deviation `p_t − p*`
from a *constant* `p* = p*_0` is unbounded whenever `π* ≠ 0` and `p − p*_t` is bounded, so it
cannot serve as the stationary variable of the forward solution; the deviation must be taken
from the time-varying target `p*_t = p*_0 + π* t` (1st-edition leftover, see survey §6). -/
theorem hint_constant_target_unbounded [Nonempty Ω] {πstar p0 : ℝ} (hπ : πstar ≠ 0)
    {p : ℕ → Ω → ℝ} (hpb : BoundedProc (devPL p0 πstar p)) :
    ¬ BoundedProc (fun t ω => p t ω - p0) := by
  rintro ⟨K, hK⟩
  obtain ⟨M, hM⟩ := hpb
  obtain ⟨n, hn⟩ := exists_nat_gt ((K + M) / |πstar|)
  have hpos : 0 < |πstar| := abs_pos.2 hπ
  set ω := Classical.arbitrary Ω
  have h1 := hK n ω
  have h2 := hM n ω
  simp only [devPL, pstar] at h2
  have e : πstar * n = (p n ω - p0) - (p n ω - (p0 + πstar * n)) := by ring
  have h3 : |πstar * n| ≤ K + M := by
    rw [e]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  rw [abs_mul, Nat.abs_cast] at h3
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

/-! ### b(ii)–(iii). The money-supply rule -/

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47: `Δm_t = π*` with `m_0 = p*_0` gives `m_t = p*_t`. -/
theorem moneyPath_eq_pstar {p0 πstar : ℝ} {m : ℕ → Ω → ℝ} (h0 : ∀ ω, m 0 ω = p0)
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar) : ∀ t ω, m t ω = pstar p0 πstar t := by
  intro t ω
  induction t with
  | zero => simp [h0, pstar]
  | succ t ih =>
    rw [pstar_succ, ← ih]
    linarith [hm t ω]

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47: equilibrium under a money-supply rule: money
market clearing `m_t − p_t = y_t − η i_t + ε^m_t` and the Fisher equation. -/
def MoneyEquilibrium (η : ℝ) (y ε r m p i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω) ∧ FisherP 𝔼 r p i

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47: the forcing term
`u_t = (η (r_t + π*) − y_t − ε^m_t)/(1 + η)` of the price-level equation. -/
noncomputable def moneyForcing (η πstar : ℝ) (y ε r : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (η * (r t ω + πstar) - y t ω - ε t ω) / (1 + η)

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47 (**reduced form**): with `m_t = p*_t` and `η ≥ 0`,
the equilibrium conditions are equivalent to the Fisher equation together with
`p̂_t = (η/(1 + η)) E_t p̂_{t+1} + u_t`. -/
theorem moneyEquilibrium_iff {η p0 πstar : ℝ} (hη : 0 ≤ η) {y ε r m p i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m t ω = pstar p0 πstar t) :
    MoneyEquilibrium 𝔼 η y ε r m p i ↔ FisherP 𝔼 r p i ∧
      ∀ t, devPL p0 πstar p t = (η / (1 + η)) • 𝔼.E t (devPL p0 πstar p (t + 1))
        + moneyForcing η πstar y ε r t := by
  unfold MoneyEquilibrium
  rw [and_comm]
  refine and_congr_right fun hfis => ?_
  have h1 : 0 < 1 + η := by linarith
  constructor
  · intro hmd t
    funext ω
    have h2 := hmd t ω
    have h3 := congrFun (hfis t) ω
    simp only [Pi.add_apply, Pi.sub_apply] at h3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, E_devPL, pstar_succ, moneyForcing,
      devPL]
    rw [hm, h3] at h2
    field_simp
    linarith
  · intro hd t ω
    have h2 := congrFun (hd t) ω
    have h3 := congrFun (hfis t) ω
    simp only [Pi.add_apply, Pi.sub_apply] at h3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, E_devPL, pstar_succ, moneyForcing,
      devPL] at h2
    rw [hm, h3]
    field_simp at h2
    linarith

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47 (**the unique equilibrium price level under the
money rule**): for `η ≥ 0`, bounded adapted `y`, `ε^m`, `r`, and an adapted price path with
`p − p*` bounded, the economy is in equilibrium iff the Fisher equation holds and
`p_t − p*_t = ∑_{k ≥ 0} (η/(1+η))ᵏ E_t u_{t+k}`. -/
theorem moneyEquilibrium_unique_iff {η p0 πstar M : ℝ} (hη : 0 ≤ η)
    {y ε r m p i : ℕ → Ω → ℝ} (hm : ∀ t ω, m t ω = pstar p0 πstar t)
    (hu : ∀ t ω, |moneyForcing η πstar y ε r t ω| ≤ M)
    (hua : 𝔼.Adapted (moneyForcing η πstar y ε r)) (hpb : BoundedProc (devPL p0 πstar p)) :
    MoneyEquilibrium 𝔼 η y ε r m p i ↔ FisherP 𝔼 r p i ∧
      devPL p0 πstar p = 𝔼.forwardSeries (η / (1 + η)) (moneyForcing η πstar y ε r) := by
  have h1 : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1.le
  have ha1 : η / (1 + η) < 1 := (div_lt_one h1).2 (by linarith)
  rw [moneyEquilibrium_iff 𝔼 hη hm]
  refine and_congr_right fun _ => ⟨fun h => 𝔼.eq_forwardSeries ha0 ha1 hu hua h hpb,
    fun h t => ?_⟩
  rw [h]
  exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47 (**existence**): with `m_t = p*_t`, `η ≥ 0` and
bounded adapted forcing, `p_t = p*_t + ∑_{k ≥ 0} (η/(1+η))ᵏ E_t u_{t+k}` and `i` from the
Fisher equation form an equilibrium with `p` adapted and `p − p*` bounded. -/
theorem moneyEquilibrium_exists {η p0 πstar M : ℝ} (hη : 0 ≤ η) {y ε r m : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m t ω = pstar p0 πstar t) (hu : ∀ t ω, |moneyForcing η πstar y ε r t ω| ≤ M)
    (hua : 𝔼.Adapted (moneyForcing η πstar y ε r)) :
    ∃ p i : ℕ → Ω → ℝ, MoneyEquilibrium 𝔼 η y ε r m p i ∧ 𝔼.Adapted p ∧
      BoundedProc (devPL p0 πstar p) := by
  have h1 : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1.le
  have ha1 : η / (1 + η) < 1 := (div_lt_one h1).2 (by linarith)
  set F := 𝔼.forwardSeries (η / (1 + η)) (moneyForcing η πstar y ε r) with hF
  have hFa := forwardSeries_adapted 𝔼 ha0 ha1 hu hua
  set p : ℕ → Ω → ℝ := fun t ω => pstar p0 πstar t + F t ω with hp
  have hdev : devPL p0 πstar p = F := by
    funext t ω
    simp [devPL, hp]
  refine ⟨p, fun t => r t + 𝔼.E t (p (t + 1)) - p t, ?_, ?_, ?_⟩
  · rw [moneyEquilibrium_iff 𝔼 hη hm]
    refine ⟨fun t => rfl, fun t => ?_⟩
    rw [hdev]
    exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t
  · intro t
    have : p t = (fun _ => pstar p0 πstar t) + F t := rfl
    rw [this, map_add, 𝔼.const, hFa t]
  · rw [hdev]
    exact 𝔼.forwardSeries_bounded ha0 ha1 hu

/-- Galí (2015), Exercise 2.2(b)(iii), p. 47: with `m_t = p*_t` and `η > 0`, money market
clearing `m_t − p_t = y_t − η i_t + ε^m_t` is exactly the price-level interest rule
`i_t = ψ (p_t − p*_t) + u_t` with `ψ = 1/η` and `u_t = (y_t + ε^m_t)/η`. -/
theorem moneyRule_as_interestRule {η p0 πstar : ℝ} (hη : 0 < η) {y ε m p i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m t ω = pstar p0 πstar t) (t : ℕ) (ω : Ω) :
    m t ω - p t ω = y t ω - η * i t ω + ε t ω ↔
      i t ω = η⁻¹ * devPL p0 πstar p t ω + (y t ω + ε t ω) / η := by
  rw [hm, devPL]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Galí (2015), Exercise 2.2(b)(iii), p. 47: the money-supply regime (`Δm_t = π*`,
`m_0 = p*_0`) and the interest rule `i_t = (1/η)(p_t − p*_t) + (y_t + ε^m_t)/η` have exactly the
same equilibria. -/
theorem moneyEquilibrium_iff_interestRule {η p0 πstar : ℝ} (hη : 0 < η)
    {y ε r m p i : ℕ → Ω → ℝ} (hm0 : ∀ ω, m 0 ω = p0)
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar) :
    MoneyEquilibrium 𝔼 η y ε r m p i ↔
      (∀ t ω, i t ω = η⁻¹ * devPL p0 πstar p t ω + (y t ω + ε t ω) / η) ∧ FisherP 𝔼 r p i := by
  have hmp := moneyPath_eq_pstar hm0 hm
  unfold MoneyEquilibrium
  exact and_congr_left fun _ => forall_congr' fun t => forall_congr' fun ω =>
    moneyRule_as_interestRule hη hmp t ω

end Gali.ClassicalMonetaryModel.Ex2_2

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.3: equilibrium indeterminacy and interest rate rules

Galí (2015), Chapter 2, Exercise 2.3, pp. 47–48 (based on Woodford 2003). The real rate `r_t`
is exogenous (bounded, adapted) and the Fisher equation `i_t = r_t + E_t π_{t+1}` holds.

## Determinacy with one predetermined variable

The partial-adjustment rule makes `i_{t−1}` a predetermined state, so the core criterion for
two non-predetermined variables (`ExpectationSystem.determinate_iff`) does not apply. This
module proves the Blanchard–Kahn criterion for the system
`k_{t+1} = b₁₁ k_t + b₁₂ x_t + f¹_t`, `E_t x_{t+1} = b₂₁ k_t + b₂₂ x_t + f²_t` (`SolvesPred`),
`k` predetermined (`k_0` given), `x` a jump variable:
* `saddle_unique`, `saddle_exists`: if one root `μ` lies outside the unit circle, the other
  root `b₁₁ + b₂₂ − μ` inside, and a left eigenvector `(w₁, w₂)` of `μ` has `w₂ ≠ 0` (the rank
  condition; `leftEigen_of_b12` supplies one when `b₁₂ ≠ 0`), then for every `k_0` there is
  exactly one bounded solution.
* `stable_not_unique`: if both roots lie inside (Schur–Cohn), every bounded solution has a
  second one with the same `k_0` (multiplicity).
* `outside_nonexistence`: if both roots lie outside (`BothOutside`, see
  `bothOutside_roots`), two bounded solutions agree at date 0, so for all initial conditions but
  at most one there is no bounded solution (non-existence).
* `exists_bounded_forward`: the scalar forward equation `z_t = a E_t z_{t+1} + u_t` has a
  bounded solution for every `|a| < 1` (also `a < 0`).

## a. Partial adjustment `i_t = φ_i i_{t−1} + (1 − φ_i)(ρ + φ_π π_t)`

* `pa_iff_system`: the equilibrium is the system above with `k_t = i_{t−1} − ρ`, `x_t = π_t`,
  roots `0` and `λ = φ_i + (1 − φ_i)φ_π`.
* `pa_determinate_iff`: for `0 ≤ φ_i < 1`, the equilibrium is unique for every bounded real
  rate and initial `i_{−1}` iff `|λ| > 1`; `pa_determinate_iff_of_nonneg`: for `φ_π ≥ 0` iff
  `φ_π > 1`.
* `pa_interest_forward`: for `φ_π > 1` the equilibrium interest rate is
  `i_t − ρ = ∑_{k ≥ 0} λ^{−(k+1)} (1 − φ_i)φ_π E_t r̂_{t+k}` and inflation is
  `π_t = (î_t − φ_i î_{t−1})/((1 − φ_i)φ_π)` (`pa_inflation_eq`).
* `pa_boundary_nonexistence`: at `φ_π = 1` a constant `r̂ ≠ 0` has no bounded equilibrium,
  so both failure modes occur.
* `pa_phi_i_one_not_determinate` (**correction**): the book allows `φ_i ∈ [0, 1]`, but for
  `φ_i = 1` the equilibrium is never unique, whatever `φ_π`; the claim needs `φ_i < 1`.

## b–c. Moving-average inflation targeting `i_t = ρ + φ_π π̄_t`

* `maBar`: `π̄_t = (1 − δ)∑_{k ≥ 0} δᵏ π_{t−k}`, a genuine infinite sum over the whole past
  (pre-sample inflation `h` is part of the data); `maBar_succ`: `π̄_t = δ π̄_{t−1} + (1−δ) π_t`.
* `ma_iff_pa` (c): the moving-average rule is exactly the partial-adjustment rule with
  `φ_i = δ` and `i_{−1} = ρ + φ_π π̄_{−1}`; `ma_equilibrium_iff_pa`; `pa_as_ma`: conversely
  every partial-adjustment rule with `φ_π ≠ 0` is a moving-average rule for a suitable history.
* `ma_determinate_iff` (b): for `0 ≤ δ < 1`, determinacy iff `|δ + (1 − δ)φ_π| > 1`;
  `ma_determinate_iff_of_nonneg`: for `φ_π ≥ 0` iff `φ_π > 1`.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_3

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Scalar forward equations with a negative coefficient -/

/-- Galí (2015), (25) p. 27 (forward solutions), for any `|a| < 1`: the equation
`z_t = a E_t z_{t+1} + u_t` with bounded adapted `u` has a bounded adapted solution. For
`a < 0` it is `(−1)ᵗ` times the forward series of `|a|` applied to `(−1)ᵗ u_t`. -/
theorem exists_bounded_forward {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    ∃ z : ℕ → Ω → ℝ, (∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) ∧ 𝔼.Adapted z ∧
      BoundedProc z := by
  rcases le_or_gt 0 a with ha0 | ha0
  · have ha1 : a < 1 := (le_abs_self a).trans_lt ha
    exact ⟨𝔼.forwardSeries a u, 𝔼.forwardSeries_solves ha0 ha1 hu hua,
      Ex2_2.forwardSeries_adapted 𝔼 ha0 ha1 hu hua, 𝔼.forwardSeries_bounded ha0 ha1 hu⟩
  · set b := -a with hb
    have hb0 : 0 ≤ b := by linarith
    have hb1 : b < 1 := by rw [abs_of_neg ha0] at ha; linarith
    set v : ℕ → Ω → ℝ := fun t => ((-1 : ℝ) ^ t) • u t with hv
    have hvb : ∀ t ω, |v t ω| ≤ M := fun t ω => by
      simp only [hv, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      exact hu t ω
    have hva : 𝔼.Adapted v := fun t => by rw [hv]; simp only; rw [map_smul, hua t]
    set F := 𝔼.forwardSeries b v with hF
    have hFs := 𝔼.forwardSeries_solves hb0 hb1 hvb hva
    have hFa := Ex2_2.forwardSeries_adapted 𝔼 hb0 hb1 hvb hva
    obtain ⟨K, hK⟩ := 𝔼.forwardSeries_bounded hb0 hb1 hvb
    have hsq : ∀ t : ℕ, ((-1 : ℝ) ^ t) * (-1) ^ t = 1 := fun t => by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    refine ⟨fun t => ((-1 : ℝ) ^ t) • F t, fun t => ?_, fun t => ?_, ⟨K, fun t ω => ?_⟩⟩
    · change ((-1 : ℝ) ^ t) • F t = a • 𝔼.E t (((-1 : ℝ) ^ (t + 1)) • F (t + 1)) + u t
      rw [hF, hFs t, map_smul]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, hb, pow_succ]
      have := hsq t
      linear_combination (u t ω) * this
    · rw [map_smul, hFa t]
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      exact hK t ω

/-! ### Systems with one predetermined variable -/

/-- Galí (2015), Exercise 2.3, p. 47 (and Blanchard–Kahn 1980): `(k, x)` solves the system
with predetermined `k` and jump variable `x`:
`k_{t+1} = b₁₁ k_t + b₁₂ x_t + f¹_t` and `E_t x_{t+1} = b₂₁ k_t + b₂₂ x_t + f²_t`. -/
def SolvesPred (b11 b12 b21 b22 : ℝ) (f1 f2 k x : ℕ → Ω → ℝ) : Prop :=
  (∀ t, k (t + 1) = b11 • k t + b12 • x t + f1 t) ∧
    ∀ t, 𝔼.E t (x (t + 1)) = b21 • k t + b22 • x t + f2 t

/-- Galí (2015), p. 25 (information): what is known at `t` is known at `t + 1`. -/
theorem known_succ {t : ℕ} {y : Ω → ℝ} (h : 𝔼.E t y = y) : 𝔼.E (t + 1) y = y := by
  rw [← h, 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 2.3: in a solution with `k_0` known at `0` and adapted `x`, `f¹`,
the predetermined variable is known one period ahead: `E_t k_t = k_t` and
`E_t k_{t+1} = k_{t+1}`. -/
theorem pred_known {b11 b12 b21 b22 : ℝ} {f1 f2 k x : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x) (hk0 : 𝔼.E 0 (k 0) = k 0)
    (hx : 𝔼.Adapted x) (hf1 : 𝔼.Adapted f1) :
    ∀ t, 𝔼.E t (k t) = k t ∧ 𝔼.E t (k (t + 1)) = k (t + 1) := by
  have step : ∀ t, 𝔼.E t (k t) = k t → 𝔼.E t (k (t + 1)) = k (t + 1) := fun t h => by
    rw [hs.1 t, map_add, map_add, map_smul, map_smul, h, hx t, hf1 t]
  have hk : ∀ t, 𝔼.E t (k t) = k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => exact known_succ 𝔼 (step t ih)
  exact fun t => ⟨hk t, step t (hk t)⟩

/-- Galí (2015), Exercise 2.3 (Blanchard–Kahn): along a solution, `z_t = w₁ k_t + w₂ x_t` for
a left eigenvector `(w₁, w₂)` of the root `μ` satisfies the scalar forward equation
`z_t = μ^{−1} E_t z_{t+1} − μ^{−1}(w₁ f¹_t + w₂ f²_t)`. -/
theorem saddle_z_eq {b11 b12 b21 b22 μ w1 w2 : ℝ} (hw1 : w1 * b11 + w2 * b21 = μ * w1)
    (hw2 : w1 * b12 + w2 * b22 = μ * w2) (hμ : μ ≠ 0) {f1 f2 k x : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x) (hk : ∀ t, 𝔼.E t (k (t + 1)) = k (t + 1))
    (t : ℕ) :
    (fun t => w1 • k t + w2 • x t) t = μ⁻¹ • 𝔼.E t ((fun t => w1 • k t + w2 • x t) (t + 1))
      + (-μ⁻¹) • (w1 • f1 t + w2 • f2 t) := by
  simp only
  rw [map_add, map_smul, map_smul, hk t, hs.2 t, hs.1 t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination (-(k t ω)) * hw1 - (x t ω) * hw2

/-- Galí (2015), Exercise 2.3 (**uniqueness on the saddle path**): if `|μ| > 1` is a root with
left eigenvector `(w₁, w₂)`, `w₂ ≠ 0`, then two bounded solutions with the same initial
`k_0` (known at date 0) coincide. -/
theorem saddle_unique {b11 b12 b21 b22 μ w1 w2 : ℝ} (hw1 : w1 * b11 + w2 * b21 = μ * w1)
    (hw2 : w1 * b12 + w2 * b22 = μ * w2) (hw20 : w2 ≠ 0) (hμ : 1 < |μ|)
    {f1 f2 k x k' x' : ℕ → Ω → ℝ} (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x)
    (hs' : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k' x') (hk0 : k 0 = k' 0)
    (hk0a : 𝔼.E 0 (k 0) = k 0) (hx : 𝔼.Adapted x) (hx' : 𝔼.Adapted x') (hf1 : 𝔼.Adapted f1)
    (hkb : BoundedProc k) (hxb : BoundedProc x) (hkb' : BoundedProc k')
    (hxb' : BoundedProc x') : k = k' ∧ x = x' := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hμ
    linarith
  have hk := fun t => (pred_known 𝔼 hs hk0a hx hf1 t).2
  have hk' := fun t => (pred_known 𝔼 hs' (by rw [← hk0]; exact hk0a) hx' hf1 t).2
  have ha : |μ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ
  have hzb : ∀ {k x : ℕ → Ω → ℝ}, BoundedProc k → BoundedProc x →
      BoundedProc (fun t => w1 • k t + w2 • x t) := by
    intro k x ⟨M1, hM1⟩ ⟨M2, hM2⟩
    refine ⟨|w1| * M1 + |w2| * M2, fun t ω => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
    · exact hM1 t ω
    · exact hM2 t ω
  have hz := 𝔼.forward_unique ha (saddle_z_eq 𝔼 hw1 hw2 hμ0 hs hk)
    (saddle_z_eq 𝔼 hw1 hw2 hμ0 hs' hk') (hzb hkb hxb) (hzb hkb' hxb')
  have hxk : ∀ t, k t = k' t → x t = x' t := by
    intro t ht
    have h := congrFun hz t
    simp only [ht] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have h2 : w2 * x t ω = w2 * x' t ω := by linarith
    exact mul_left_cancel₀ hw20 h2
  have hkk : ∀ t, k t = k' t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hs.1 t, hs'.1 t, ih, hxk t ih]
  exact ⟨funext hkk, funext fun t => hxk t (hkk t)⟩

/-- Galí (2015), Exercise 2.3: the path of the predetermined variable on the saddle path,
`k_0` given and `k_{t+1} = μ₁ k_t + c z_t + f¹_t`. -/
def kPath (k0 : Ω → ℝ) (μ1 c : ℝ) (z f1 : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => k0
  | t + 1 => μ1 • kPath k0 μ1 c z f1 t + c • z t + f1 t

/-- Galí (2015), Exercise 2.3: for `|μ₁| < 1` and bounded `k_0`, `z`, `f¹`, the saddle-path
`k` is bounded by `max K₀ ((|c| |M_z| + |M_f|)/(1 − |μ₁|))`. -/
theorem kPath_bounded {k0 : Ω → ℝ} {μ1 c K0 Mz Mf : ℝ} {z f1 : ℕ → Ω → ℝ} (hμ1 : |μ1| < 1)
    (hk0 : ∀ ω, |k0 ω| ≤ K0) (hz : ∀ t ω, |z t ω| ≤ Mz) (hf : ∀ t ω, |f1 t ω| ≤ Mf) :
    ∀ t ω, |kPath k0 μ1 c z f1 t ω| ≤ max K0 ((|c| * |Mz| + |Mf|) / (1 - |μ1|)) := by
  set B := max K0 ((|c| * |Mz| + |Mf|) / (1 - |μ1|)) with hB
  have h1 : 0 < 1 - |μ1| := by linarith
  have hD : |c| * |Mz| + |Mf| ≤ (1 - |μ1|) * B := by
    have := le_max_right K0 ((|c| * |Mz| + |Mf|) / (1 - |μ1|))
    rw [← hB, div_le_iff₀ h1] at this
    linarith
  have hB0 : 0 ≤ B := le_trans (by positivity) (le_max_right _ _)
  intro t
  induction t with
  | zero => exact fun ω => (hk0 ω).trans (le_max_left _ _)
  | succ t ih =>
    intro ω
    simp only [kPath, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h3 : |μ1 * kPath k0 μ1 c z f1 t ω| ≤ |μ1| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have h4 : |c * z t ω| ≤ |c| * |Mz| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((hz t ω).trans (le_abs_self _)) (abs_nonneg _)
    have h5 : |f1 t ω| ≤ |Mf| := (hf t ω).trans (le_abs_self _)
    calc |μ1 * kPath k0 μ1 c z f1 t ω + c * z t ω + f1 t ω|
        ≤ |μ1 * kPath k0 μ1 c z f1 t ω| + |c * z t ω| + |f1 t ω| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ |μ1| * B + (|c| * |Mz| + |Mf|) := by linarith
      _ ≤ B := by nlinarith

/-- Galí (2015), Exercise 2.3 (**existence on the saddle path**): if `|μ| > 1` is a root with
left eigenvector `(w₁, w₂)`, `w₂ ≠ 0`, the other root `b₁₁ + b₂₂ − μ` has modulus below one,
and the forcing terms and `k_0` are bounded and known when dated, then there is a bounded
solution starting from `k_0`. -/
theorem saddle_exists {b11 b12 b21 b22 μ w1 w2 : ℝ} (hw1 : w1 * b11 + w2 * b21 = μ * w1)
    (hw2 : w1 * b12 + w2 * b22 = μ * w2) (hw20 : w2 ≠ 0) (hμ : 1 < |μ|)
    (hμ1 : |b11 + b22 - μ| < 1) {f1 f2 : ℕ → Ω → ℝ} {k0 : Ω → ℝ} (hf1b : BoundedProc f1)
    (hf2b : BoundedProc f2) (hf1 : 𝔼.Adapted f1) (hf2 : 𝔼.Adapted f2)
    (hk0b : ∃ M, ∀ ω, |k0 ω| ≤ M) (hk0 : 𝔼.E 0 k0 = k0) :
    ∃ k x : ℕ → Ω → ℝ, SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x ∧ k 0 = k0 ∧ 𝔼.Adapted x ∧
      BoundedProc k ∧ BoundedProc x := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hμ
    linarith
  obtain ⟨M1, hM1⟩ := hf1b
  obtain ⟨M2, hM2⟩ := hf2b
  obtain ⟨K0, hK0⟩ := hk0b
  set g : ℕ → Ω → ℝ := fun t => w1 • f1 t + w2 • f2 t with hg
  have hu : ∀ t ω, |((-μ⁻¹) • g t) ω| ≤ |μ⁻¹| * (|w1| * M1 + |w2| * M2) := fun t ω => by
    simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
    · exact hM1 t ω
    · exact hM2 t ω
  have hua : 𝔼.Adapted (fun t => (-μ⁻¹) • g t) := fun t => by
    simp only [hg]
    rw [map_smul, map_add, map_smul, map_smul, hf1 t, hf2 t]
  have ha : |μ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ
  obtain ⟨z, hz, hza, ⟨Mz, hMz⟩⟩ := exists_bounded_forward 𝔼 ha hu hua
  set μ1 := b11 + b22 - μ with hμ1def
  set c := b12 / w2 with hc
  set k := kPath k0 μ1 c z f1 with hk
  have hkb := kPath_bounded (c := c) hμ1 hK0 hMz hM1
  -- the predetermined variable is known one period ahead
  have hkk : ∀ t, 𝔼.E t (k t) = k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih =>
      refine known_succ 𝔼 ?_
      change 𝔼.E t (μ1 • k t + c • z t + f1 t) = μ1 • k t + c • z t + f1 t
      rw [map_add, map_add, map_smul, map_smul, ih, hza t, hf1 t]
  have hk1 : ∀ t, 𝔼.E t (k (t + 1)) = k (t + 1) := by
    intro t
    change 𝔼.E t (μ1 • k t + c • z t + f1 t) = μ1 • k t + c • z t + f1 t
    rw [map_add, map_add, map_smul, map_smul, hkk t, hza t, hf1 t]
  -- `E_t z_{t+1} = μ z_t + g_t`
  have hEz : ∀ t ω, 𝔼.E t (z (t + 1)) ω = μ * z t ω + g t ω := by
    intro t ω
    have := congrFun (hz t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    field_simp at this
    linarith
  refine ⟨k, fun t => w2⁻¹ • (z t - w1 • k t), ⟨fun t => ?_, fun t => ?_⟩, rfl, fun t => ?_,
    ⟨_, hkb⟩, ⟨|w2⁻¹| * (|Mz| + |w1| * max K0 ((|c| * |Mz| + |M1|) / (1 - |μ1|))),
      fun t ω => ?_⟩⟩
  · change μ1 • k t + c • z t + f1 t = b11 • k t + b12 • (w2⁻¹ • (z t - w1 • k t)) + f1 t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hμ1def, hc]
    field_simp
    linear_combination (k t ω) * hw2
  · rw [map_smul, map_sub, map_smul, hk1 t]
    funext ω
    have hkt : k (t + 1) ω = μ1 * k t ω + c * z t ω + f1 t ω := rfl
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hEz, hkt, hg, hμ1def,
      hc]
    field_simp
    linear_combination (-(w2 * k t ω)) * hw1 + (-(z t ω)) * hw2
  · rw [map_smul, map_sub, map_smul, hza t, hkk t]
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    gcongr
    refine (abs_sub _ _).trans (add_le_add ((hMz t ω).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    gcongr
    exact hkb t ω

/-- Galí (2015), Exercise 2.3 (rank condition): if `b₁₂ ≠ 0` and `μ` is a root of the
characteristic polynomial `μ² − (b₁₁ + b₂₂)μ + (b₁₁b₂₂ − b₁₂b₂₁)`, then
`(w₁, w₂) = (μ − b₂₂, b₁₂)` is a left eigenvector for `μ` with `w₂ ≠ 0`. -/
theorem leftEigen_of_b12 {b11 b12 b21 b22 μ : ℝ}
    (hroot : μ ^ 2 - (b11 + b22) * μ + (b11 * b22 - b12 * b21) = 0) :
    (μ - b22) * b11 + b12 * b21 = μ * (μ - b22) ∧ (μ - b22) * b12 + b12 * b22 = μ * b12 := by
  constructor
  · linear_combination (-1 : ℝ) * hroot
  · ring

/-- Galí (2015), Exercise 2.3 (**multiplicity when both roots are inside the unit circle**):
under the Schur–Cohn condition every bounded solution `(k, x)` has a different bounded
solution with the same `k_0`, obtained by adding the deterministic path
`(k, x)_t ↦ (k, x)_t + Bᵗ (0, 1)`. -/
theorem stable_not_unique [Nonempty Ω] {b11 b12 b21 b22 : ℝ}
    (hA : SchurStable (b11 + b22) (b11 * b22 - b12 * b21)) {f1 f2 k x : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x) (hx : 𝔼.Adapted x) (hkb : BoundedProc k)
    (hxb : BoundedProc x) :
    ∃ k' x' : ℕ → Ω → ℝ, SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k' x' ∧ k' 0 = k 0 ∧
      𝔼.Adapted x' ∧ BoundedProc k' ∧ BoundedProc x' ∧ x' ≠ x := by
  set B : Matrix (Fin 2) (Fin 2) ℝ := !![b11, b12; b21, b22] with hB
  have hS : SchurStable (tr2 B) (det2 B) := by
    simpa [tr2, det2, hB] using hA
  set d : ℕ → Fin 2 → ℝ := fun t i => (B ^ t) i 1 with hd
  have hrec : ∀ t i, d (t + 1) i = B i 0 * d t 0 + B i 1 * d t 1 := by
    intro t i
    simp only [hd, pow_succ', Matrix.mul_apply, Fin.sum_univ_two]
  have hdb : ∀ i, ∃ C, ∀ t, |d t i| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ :=
      (Metric.isBounded_range_of_tendsto _ (tendsto_pow_entry hS i 1)).exists_norm_le
    exact ⟨C, fun t => by simpa using hC _ ⟨t, rfl⟩⟩
  obtain ⟨C0, hC0⟩ := hdb 0
  obtain ⟨C1, hC1⟩ := hdb 1
  obtain ⟨Mk, hMk⟩ := hkb
  obtain ⟨Mx, hMx⟩ := hxb
  refine ⟨fun t ω => k t ω + d t 0, fun t ω => x t ω + d t 1, ⟨fun t => ?_, fun t => ?_⟩,
    ?_, fun t => ?_, ⟨Mk + C0, fun t ω => ?_⟩, ⟨Mx + C1, fun t ω => ?_⟩, fun h => ?_⟩
  · funext ω
    have := congrFun (hs.1 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this, hrec t 0]
    simp [hB]
    ring
  · have hfun : (fun ω => x (t + 1) ω + d (t + 1) 1) = x (t + 1) + fun _ => d (t + 1) 1 := rfl
    change 𝔼.E t (fun ω => x (t + 1) ω + d (t + 1) 1) = _
    rw [hfun, map_add, 𝔼.const, hs.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrec t 1]
    simp [hB]
    ring
  · funext ω
    simp [hd]
  · have hfun : (fun ω => x t ω + d t 1) = x t + fun _ => d t 1 := rfl
    change 𝔼.E t (fun ω => x t ω + d t 1) = fun ω => x t ω + d t 1
    rw [hfun, map_add, 𝔼.const, hx t]
  · exact (abs_add_le _ _).trans (add_le_add (hMk t ω) (hC0 t))
  · exact (abs_add_le _ _).trans (add_le_add (hMx t ω) (hC1 t))
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp [hd] at this

/-- Galí (2015), Exercise 2.3: both roots of `z² − T z + D` lie strictly outside the unit
circle (`bothOutside_roots`); equivalently the reversed polynomial is Schur–Cohn stable. -/
def BothOutside (T D : ℝ) : Prop := 1 < |D| ∧ |T| < |1 + D|

/-- Galí (2015), Exercise 2.3: under `BothOutside T D` the inverse matrix, with trace `T/D` and
determinant `1/D`, satisfies the Schur–Cohn condition. -/
theorem schurStable_inv_of_bothOutside {T D : ℝ} (h : BothOutside T D) :
    SchurStable (T / D) (1 / D) := by
  obtain ⟨hD, hT⟩ := h
  have hD0 : 0 < |D| := by linarith
  have h1 : |1 / D| < 1 := by
    rw [abs_div, abs_one, div_lt_one hD0]
    exact hD
  refine ⟨h1, ?_⟩
  have hpos : 0 < 1 + 1 / D := by
    have := neg_abs_le (1 / D)
    linarith
  have e : |1 + D| / |D| = 1 + 1 / D := by
    have e1 : (1 + D) / D = 1 + 1 / D := by rw [add_div, div_self (abs_pos.1 hD0), add_comm]
    rw [← abs_div, e1, abs_of_pos hpos]
  rw [abs_div, ← e]
  exact div_lt_div_of_pos_right hT hD0

/-- Galí (2015), Exercise 2.3: under `BothOutside T D` every complex root of `z² − T z + D`
has modulus greater than one. -/
theorem bothOutside_roots {T D : ℝ} (h : BothOutside T D) {z : ℂ}
    (hz : z ^ 2 - T * z + D = 0) : 1 < ‖z‖ := by
  have hD0 : D ≠ 0 := fun h0 => by
    have := h.1
    rw [h0, abs_zero] at this
    linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    have h2 : ((D : ℝ) : ℂ) = 0 := by simpa using hz
    exact hD0 (by exact_mod_cast h2)
  have hw : z⁻¹ ^ 2 - ((T / D : ℝ) : ℂ) * z⁻¹ + ((1 / D : ℝ) : ℂ) = 0 := by
    have hD0' : (D : ℂ) ≠ 0 := by exact_mod_cast hD0
    push_cast
    field_simp
    linear_combination hz
  have hroots := (schurStable_iff_roots _ _).1 (schurStable_inv_of_bothOutside h)
  have hlt : ‖z⁻¹‖ < 1 := by
    rcases eq_root_of_eq hw with h1 | h1
    · rw [h1]; exact hroots.1
    · rw [h1]; exact hroots.2
  rw [norm_inv] at hlt
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rwa [inv_lt_one₀ hpos] at hlt

/-- Galí (2015), Exercise 2.3 (**non-existence when both roots are outside the unit
circle**): two bounded solutions with the same forcing terms, both with `k_0` known at date 0
and adapted `x`, agree at date 0. So for every forcing there is at most one initial condition
`k_0` with a bounded solution. -/
theorem outside_nonexistence {b11 b12 b21 b22 : ℝ}
    (hout : BothOutside (b11 + b22) (b11 * b22 - b12 * b21)) {f1 f2 k x k' x' : ℕ → Ω → ℝ}
    (hs : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k x)
    (hs' : SolvesPred 𝔼 b11 b12 b21 b22 f1 f2 k' x') (hk0 : 𝔼.E 0 (k 0) = k 0)
    (hk0' : 𝔼.E 0 (k' 0) = k' 0) (hx : 𝔼.Adapted x) (hx' : 𝔼.Adapted x')
    (hkb : BoundedProc k) (hxb : BoundedProc x) (hkb' : BoundedProc k')
    (hxb' : BoundedProc x') : k 0 = k' 0 ∧ x 0 = x' 0 := by
  set D := b11 * b22 - b12 * b21 with hDdef
  have hD0 : D ≠ 0 := fun h0 => by
    have := hout.1
    rw [h0, abs_zero] at this
    linarith
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![b22 / D, -b12 / D; -b21 / D, b11 / D] with hA
  have hS : SchurStable (tr2 A) (det2 A) := by
    have e1 : tr2 A = (b11 + b22) / D := by simp [tr2, hA]; ring
    have e2 : det2 A = 1 / D := by
      simp only [det2, hA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      rw [hDdef]
      ring
    rw [e1, e2]
    exact schurStable_inv_of_bothOutside hout
  obtain ⟨Mk, hMk⟩ := hkb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mk', hMk'⟩ := hkb'
  obtain ⟨Mx', hMx'⟩ := hxb'
  -- the date-0 expectation of the difference follows the deterministic recursion
  have key : ∀ ω, 𝔼.E 0 (k 0 - k' 0) ω = 0 ∧ 𝔼.E 0 (x 0 - x' 0) ω = 0 := by
    intro ω
    set y : ℕ → Fin 2 → ℝ := fun t => ![𝔼.E 0 (k t - k' t) ω, 𝔼.E 0 (x t - x' t) ω] with hy
    have hrec0 : ∀ t, 𝔼.E 0 (k (t + 1) - k' (t + 1)) ω
        = b11 * 𝔼.E 0 (k t - k' t) ω + b12 * 𝔼.E 0 (x t - x' t) ω := by
      intro t
      rw [hs.1 t, hs'.1 t]
      have : b11 • k t + b12 • x t + f1 t - (b11 • k' t + b12 • x' t + f1 t)
          = b11 • (k t - k' t) + b12 • (x t - x' t) := by
        funext ω'; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this, map_add, map_smul, map_smul]
      rfl
    have hrec1 : ∀ t, 𝔼.E 0 (x (t + 1) - x' (t + 1)) ω
        = b21 * 𝔼.E 0 (k t - k' t) ω + b22 * 𝔼.E 0 (x t - x' t) ω := by
      intro t
      rw [← 𝔼.tower (Nat.zero_le t), map_sub, hs.2 t, hs'.2 t]
      have : b21 • k t + b22 • x t + f2 t - (b21 • k' t + b22 • x' t + f2 t)
          = b21 • (k t - k' t) + b22 • (x t - x' t) := by
        funext ω'; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this, map_add, map_smul, map_smul]
      rfl
    have hhom : ∀ t, y t = A.mulVec (y (t + 1)) := by
      intro t
      funext i
      fin_cases i
      · simp only [hy, hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
        rw [hrec0, hrec1]
        field_simp
        rw [hDdef]
        ring
      · simp only [hy, hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
        rw [hrec0, hrec1]
        field_simp
        rw [hDdef]
        ring
    have hyb : BoundedSeq y := by
      refine ⟨Mk + Mk' + (Mx + Mx'), fun t i => ?_⟩
      have h1 : |𝔼.E 0 (k t - k' t) ω| ≤ Mk + Mk' :=
        𝔼.abs_E_le (fun ω' => (abs_sub _ _).trans (add_le_add (hMk t ω') (hMk' t ω'))) 0 ω
      have h2 : |𝔼.E 0 (x t - x' t) ω| ≤ Mx + Mx' :=
        𝔼.abs_E_le (fun ω' => (abs_sub _ _).trans (add_le_add (hMx t ω') (hMx' t ω'))) 0 ω
      have h0 : 0 ≤ Mk + Mk' := (abs_nonneg _).trans h1
      have h0' : 0 ≤ Mx + Mx' := (abs_nonneg _).trans h2
      fin_cases i
      · simp only [hy, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
      · simp only [hy, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith
    have h0 := homogeneous_eq_zero hS hhom hyb
    have e0 := congrFun (congrFun h0 0) 0
    have e1 := congrFun (congrFun h0 0) 1
    simp only [hy, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.zero_apply] at e0 e1
    exact ⟨e0, e1⟩
  constructor
  · funext ω
    have := (key ω).1
    rw [map_sub, hk0, hk0'] at this
    simpa [sub_eq_zero] using this
  · funext ω
    have := (key ω).2
    rw [map_sub, hx 0, hx' 0] at this
    simpa [sub_eq_zero] using this

/-! ### a. The partial-adjustment rule -/

/-- Galí (2015), Exercise 2.3(a), p. 47: the lagged interest rate `i_{t−1}`, with the given
initial value `i_{−1}` at `t = 0`. -/
def lagI (im1 : Ω → ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => im1
  | t + 1 => i t

/-- Galí (2015), Exercise 2.3(a): `i_{−1}` at date 0. -/
theorem lagI_zero (im1 : Ω → ℝ) (i : ℕ → Ω → ℝ) : lagI im1 i 0 = im1 := rfl

/-- Galí (2015), Exercise 2.3(a): `i_{(t+1)−1} = i_t`. -/
theorem lagI_succ (im1 : Ω → ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) : lagI im1 i (t + 1) = i t := rfl

/-- Galí (2015), Exercise 2.3(a), p. 47: equilibrium under the partial-adjustment rule
`i_t = φ_i i_{t−1} + (1 − φ_i)(ρ + φ_π π_t)` with the Fisher equation
`i_t = r_t + E_t π_{t+1}`. -/
def PAEquilibrium (φi φπ ρ : ℝ) (r : ℕ → Ω → ℝ) (im1 : Ω → ℝ) (i infl : ℕ → Ω → ℝ) : Prop :=
  (∀ t, i t = r t + 𝔼.E t (infl (t + 1))) ∧
    ∀ t ω, i t ω = φi * lagI im1 i t ω + (1 - φi) * (ρ + φπ * infl t ω)

/-- Galí (2015), Exercise 2.3(a), p. 47: the partial-adjustment equilibrium is the system
`k_{t+1} = φ_i k_t + κ π_t`, `E_t π_{t+1} = φ_i k_t + κ π_t − r̂_t` in the predetermined
`k_t = i_{t−1} − ρ` and the jump variable `π_t`, with `κ = (1 − φ_i)φ_π`; its matrix has roots
`0` and `λ = φ_i + κ`. -/
theorem pa_iff_system (φi φπ ρ : ℝ) (r : ℕ → Ω → ℝ) (im1 : Ω → ℝ) (i infl : ℕ → Ω → ℝ) :
    PAEquilibrium 𝔼 φi φπ ρ r im1 i infl ↔
      SolvesPred 𝔼 φi ((1 - φi) * φπ) φi ((1 - φi) * φπ) (fun _ _ => 0)
        (fun t ω => ρ - r t ω) (fun t ω => lagI im1 i t ω - ρ) infl := by
  constructor
  · rintro ⟨hf, hr⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · simp only [lagI_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hr t ω]
      ring
    · have := congrFun (hf t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [hr t ω] at this
      linarith
  · rintro ⟨h1, h2⟩
    have hrule : ∀ t ω, i t ω = φi * lagI im1 i t ω + (1 - φi) * (ρ + φπ * infl t ω) := by
      intro t ω
      have := congrFun (h1 t) ω
      simp only [lagI_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    refine ⟨fun t => funext fun ω => ?_, hrule⟩
    have := congrFun (h2 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    linarith [hrule t ω]

/-- Galí (2015), Exercise 2.3: with an adapted real rate, the Fisher equation makes the nominal
rate adapted. -/
theorem pa_i_adapted {φi φπ ρ : ℝ} {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ}
    (hra : 𝔼.Adapted r) (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) : 𝔼.Adapted i := by
  intro t
  rw [heq.1 t, map_add, hra t, 𝔼.E_E_self]

/-- Galí (2015), Exercise 2.3(a): the deviation `i_{t−1} − ρ` of a bounded interest path with a
bounded initial condition is bounded. -/
theorem lag_bounded {ρ : ℝ} {im1 : Ω → ℝ} {i : ℕ → Ω → ℝ} (him1 : ∃ M, ∀ ω, |im1 ω| ≤ M)
    (hib : BoundedProc i) : BoundedProc (fun t ω => lagI im1 i t ω - ρ) := by
  obtain ⟨M1, hM1⟩ := him1
  obtain ⟨M2, hM2⟩ := hib
  refine ⟨max M1 M2 + |ρ|, fun t ω => (abs_sub _ _).trans ?_⟩
  cases t with
  | zero => simp only [lagI_zero]; linarith [hM1 ω, le_max_left M1 M2]
  | succ t => simp only [lagI_succ]; linarith [hM2 t ω, le_max_right M1 M2]

/-- Galí (2015), Exercise 2.3(a): with `i_{−1}` known at date 0, `E_0 k_0 = k_0` for
`k_0 = i_{−1} − ρ`. -/
theorem E_zero_k0 {ρ : ℝ} {im1 : Ω → ℝ} (him1a : 𝔼.E 0 im1 = im1) (i : ℕ → Ω → ℝ) :
    𝔼.E 0 ((fun t ω => lagI im1 i t ω - ρ) 0) = (fun t ω => lagI im1 i t ω - ρ) 0 := by
  change 𝔼.E 0 (fun ω => im1 ω - ρ) = fun ω => im1 ω - ρ
  rw [Ex2_2.E_sub_const, him1a]

/-- Galí (2015), Exercise 2.3(a) (**uniqueness**): for `0 ≤ φ_i < 1` and
`|φ_i + (1 − φ_i)φ_π| > 1`, two bounded partial-adjustment equilibria with the same real rate
and the same `i_{−1}` (known at date 0) coincide. -/
theorem pa_unique {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1)
    (hlam : 1 < |φi + (1 - φi) * φπ|) {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ}
    (him1 : ∃ M, ∀ ω, |im1 ω| ≤ M) (him1a : 𝔼.E 0 im1 = im1) {i infl i' infl' : ℕ → Ω → ℝ}
    (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl)
    (heq' : PAEquilibrium 𝔼 φi φπ ρ r im1 i' infl') (hx : 𝔼.Adapted infl)
    (hx' : 𝔼.Adapted infl') (hib : BoundedProc i) (hxb : BoundedProc infl)
    (hib' : BoundedProc i') (hxb' : BoundedProc infl') : i = i' ∧ infl = infl' := by
  have hκ : (1 - φi) * φπ ≠ 0 := by
    intro h0
    rw [h0, add_zero, abs_of_nonneg hφi0] at hlam
    linarith
  obtain ⟨hk, hxx⟩ := saddle_unique 𝔼 (b11 := φi) (b12 := (1 - φi) * φπ) (b21 := φi)
    (b22 := (1 - φi) * φπ) (μ := φi + (1 - φi) * φπ) (w1 := φi)
    (w2 := (1 - φi) * φπ) (by ring) (by ring) hκ hlam ((pa_iff_system 𝔼 _ _ _ _ _ _ _).1 heq)
    ((pa_iff_system 𝔼 _ _ _ _ _ _ _).1 heq') rfl (E_zero_k0 𝔼 him1a i) hx hx'
    (fun t => 𝔼.const t 0) (lag_bounded him1 hib) hxb (lag_bounded him1 hib') hxb'
  refine ⟨funext fun t => funext fun ω => ?_, hxx⟩
  have := congrFun (congrFun hk (t + 1)) ω
  simp only [lagI_succ] at this
  linarith

/-- Galí (2015), Exercise 2.3(a) (**existence**): for `0 ≤ φ_i < 1` and
`|φ_i + (1 − φ_i)φ_π| > 1`, for every bounded adapted real rate and bounded `i_{−1}` known at
date 0 there is a bounded adapted partial-adjustment equilibrium. -/
theorem pa_exists {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1)
    (hlam : 1 < |φi + (1 - φi) * φπ|) {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} (hrb : BoundedProc r)
    (hra : 𝔼.Adapted r) (him1 : ∃ M, ∀ ω, |im1 ω| ≤ M) (him1a : 𝔼.E 0 im1 = im1) :
    ∃ i infl, PAEquilibrium 𝔼 φi φπ ρ r im1 i infl ∧ 𝔼.Adapted i ∧ 𝔼.Adapted infl ∧
      BoundedProc i ∧ BoundedProc infl := by
  have hκ : (1 - φi) * φπ ≠ 0 := by
    intro h0
    rw [h0, add_zero, abs_of_nonneg hφi0] at hlam
    linarith
  obtain ⟨Mr, hMr⟩ := hrb
  obtain ⟨M1, hM1⟩ := him1
  have hf2b : BoundedProc (fun t ω => ρ - r t ω) :=
    ⟨|ρ| + Mr, fun t ω => (abs_sub _ _).trans (by linarith [hMr t ω])⟩
  have hf2a : 𝔼.Adapted (fun t ω => ρ - r t ω) := fun t => by
    change 𝔼.E t ((fun _ => ρ) - r t) = (fun _ => ρ) - r t
    rw [map_sub, 𝔼.const, hra t]
  have hk0b : ∃ M, ∀ ω, |(fun ω => im1 ω - ρ) ω| ≤ M :=
    ⟨M1 + |ρ|, fun ω => (abs_sub _ _).trans (by linarith [hM1 ω])⟩
  have hk0a : 𝔼.E 0 (fun ω => im1 ω - ρ) = fun ω => im1 ω - ρ := by
    rw [Ex2_2.E_sub_const, him1a]
  obtain ⟨k, x, hs, hk0, hxa, ⟨Mk, hMk⟩, hxb⟩ := saddle_exists 𝔼 (b11 := φi)
    (b12 := (1 - φi) * φπ) (b21 := φi) (b22 := (1 - φi) * φπ) (μ := φi + (1 - φi) * φπ)
    (w1 := φi) (w2 := (1 - φi) * φπ) (by ring) (by ring) hκ hlam
    (by rw [show φi + (1 - φi) * φπ - (φi + (1 - φi) * φπ) = 0 by ring, abs_zero]; exact one_pos)
    ⟨0, fun t ω => by simp⟩ hf2b (fun t => 𝔼.const t 0) hf2a hk0b hk0a
  have hkn := pred_known 𝔼 hs (by rw [hk0]; exact hk0a) hxa (fun t => 𝔼.const t 0)
  set i : ℕ → Ω → ℝ := fun t ω => ρ + k (t + 1) ω with hi
  have hlag : (fun t ω => lagI im1 i t ω - ρ) = k := by
    funext t ω
    cases t with
    | zero => simp only [lagI_zero]; rw [hk0]
    | succ t => simp only [lagI_succ, hi]; ring
  refine ⟨i, x, ?_, fun t => ?_, hxa, ⟨|ρ| + Mk, fun t ω => ?_⟩, hxb⟩
  · rw [pa_iff_system, hlag]
    exact hs
  · change 𝔼.E t ((fun _ => ρ) + k (t + 1)) = (fun _ => ρ) + k (t + 1)
    rw [map_add, 𝔼.const, (hkn t).2]
  · exact (abs_add_le _ _).trans (by linarith [hMk (t + 1) ω])

/-- Galí (2015), Exercise 2.3(a): in an equilibrium with an adapted real rate,
`E_t i_{t+1} − ρ = λ(i_t − ρ) − κ(r_t − ρ)` with `λ = φ_i + κ`, `κ = (1 − φ_i)φ_π`: the
interest rate obeys a scalar forward equation. -/
theorem pa_interest_eq {φi φπ ρ : ℝ} {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ}
    (hra : 𝔼.Adapted r) (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) (t : ℕ) (ω : Ω) :
    𝔼.E t (i (t + 1)) ω - ρ = (φi + (1 - φi) * φπ) * (i t ω - ρ) - (1 - φi) * φπ * (r t ω - ρ) := by
  have hia := pa_i_adapted 𝔼 hra heq
  have hfun : i (t + 1) = (fun _ => (1 - φi) * ρ) + φi • i t + ((1 - φi) * φπ) • infl (t + 1) := by
    funext ω'
    rw [heq.2 (t + 1) ω']
    simp only [lagI_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, map_add, map_add, map_smul, map_smul, 𝔼.const, hia t]
  have hf := congrFun (heq.1 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hf ⊢
  rw [show 𝔼.E t (infl (t + 1)) ω = i t ω - r t ω by linarith]
  ring

/-- Galí (2015), Exercise 2.3(a) (**solution for the interest rate**): for `0 ≤ φ_i < 1` and
`φ_π > 1`, in any bounded equilibrium with bounded adapted `r̂ = r − ρ`,
`i_t − ρ = ∑_{k ≥ 0} λ^{−k} E_t[λ^{−1} κ r̂_{t+k}]`, `λ = φ_i + κ > 1`, `κ = (1 − φ_i)φ_π`. -/
theorem pa_interest_forward {φi φπ ρ M : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1) (hφπ : 1 < φπ)
    {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ} (hr : ∀ t ω, |r t ω - ρ| ≤ M)
    (hra : 𝔼.Adapted r) (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) (hib : BoundedProc i) :
    (fun t ω => i t ω - ρ) = 𝔼.forwardSeries (φi + (1 - φi) * φπ)⁻¹
      (fun t => ((φi + (1 - φi) * φπ)⁻¹ * ((1 - φi) * φπ)) • fun ω => r t ω - ρ) := by
  set lam := φi + (1 - φi) * φπ with hlam
  set κ := (1 - φi) * φπ with hκ
  have hlam1 : 1 < lam := by
    have : 0 < (1 - φi) * (φπ - 1) := mul_pos (by linarith) (by linarith)
    rw [hlam]
    nlinarith
  have ha0 : 0 ≤ lam⁻¹ := inv_nonneg.2 (by linarith)
  have ha1 : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam1
  have hu : ∀ t ω, |((lam⁻¹ * κ) • fun ω => r t ω - ρ) ω| ≤ |lam⁻¹ * κ| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    gcongr
    exact hr t ω
  have hua : 𝔼.Adapted (fun t => (lam⁻¹ * κ) • fun ω => r t ω - ρ) := fun t => by
    rw [map_smul, Ex2_2.E_sub_const, hra t]
  obtain ⟨Mi, hMi⟩ := hib
  refine 𝔼.eq_forwardSeries ha0 ha1 hu hua (fun t => funext fun ω => ?_)
    ⟨Mi + |ρ|, fun t ω => (abs_sub _ _).trans (by linarith [hMi t ω])⟩
  have h := pa_interest_eq 𝔼 hra heq t ω
  have hE : 𝔼.E t (fun ω => i (t + 1) ω - ρ) ω = 𝔼.E t (i (t + 1)) ω - ρ :=
    congrFun (Ex2_2.E_sub_const 𝔼 t (i (t + 1)) ρ) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hE, h]
  field_simp
  ring

/-- Galí (2015), Exercise 2.3(a) (**equilibrium inflation**): the rule gives
`κ π_t = (i_t − ρ) − φ_i (i_{t−1} − ρ)`, `κ = (1 − φ_i)φ_π`, so with `i` from
`pa_interest_forward`, `π_t = (î_t − φ_i î_{t−1})/κ`. -/
theorem pa_inflation_eq {φi φπ ρ : ℝ} {r : ℕ → Ω → ℝ} {im1 : Ω → ℝ} {i infl : ℕ → Ω → ℝ}
    (heq : PAEquilibrium 𝔼 φi φπ ρ r im1 i infl) (t : ℕ) (ω : Ω) :
    (1 - φi) * φπ * infl t ω = (i t ω - ρ) - φi * (lagI im1 i t ω - ρ) := by
  rw [heq.2 t ω]
  ring

/-- Galí (2015), Exercise 2.3(a): determinacy of the partial-adjustment rule: for every bounded
adapted real rate and every bounded `i_{−1}` known at date 0 there is exactly one bounded
adapted equilibrium. -/
def PADeterminate (φi φπ ρ : ℝ) : Prop :=
  ∀ (r : ℕ → Ω → ℝ) (im1 : Ω → ℝ), BoundedProc r → 𝔼.Adapted r → (∃ M, ∀ ω, |im1 ω| ≤ M) →
    𝔼.E 0 im1 = im1 →
    (∃ i infl, PAEquilibrium 𝔼 φi φπ ρ r im1 i infl ∧ 𝔼.Adapted i ∧ 𝔼.Adapted infl ∧
      BoundedProc i ∧ BoundedProc infl) ∧
    ∀ i infl i' infl', PAEquilibrium 𝔼 φi φπ ρ r im1 i infl →
      PAEquilibrium 𝔼 φi φπ ρ r im1 i' infl' → 𝔼.Adapted infl → 𝔼.Adapted infl' →
      BoundedProc i → BoundedProc infl → BoundedProc i' → BoundedProc infl' →
      i = i' ∧ infl = infl'

/-- Galí (2015), Exercise 2.3(a) (**self-fulfilling deviation**): with `r_t = ρ` and
`i_{−1} = ρ`, besides `(i, π) = (ρ, 0)` the deterministic path `π_0 = 1`,
`π_{t+1} = κ λᵗ`, `i_t = ρ + κ λᵗ` is an equilibrium (`κ = (1 − φ_i)φ_π`, `λ = φ_i + κ`). -/
theorem pa_two_solutions (φi φπ ρ : ℝ) :
    PAEquilibrium 𝔼 φi φπ ρ (fun _ _ => ρ) (fun _ => ρ) (fun _ _ => ρ) (fun _ _ => 0) ∧
      PAEquilibrium 𝔼 φi φπ ρ (fun _ _ => ρ) (fun _ => ρ)
        (fun t _ => ρ + (1 - φi) * φπ * (φi + (1 - φi) * φπ) ^ t)
        (fun t _ => if t = 0 then 1 else (1 - φi) * φπ * (φi + (1 - φi) * φπ) ^ (t - 1)) := by
  refine ⟨⟨fun t => ?_, fun t ω => ?_⟩, ⟨fun t => ?_, fun t ω => ?_⟩⟩
  · rw [𝔼.const]
    funext ω
    simp
  · cases t <;> simp [lagI_zero, lagI_succ] <;> ring
  · rw [𝔼.const]
    funext ω
    simp
  · cases t with
    | zero => simp [lagI_zero]; ring
    | succ t => simp [lagI_succ, pow_succ]; ring

/-- Galí (2015), Exercise 2.3(a) (**indeterminacy for `|λ| ≤ 1`**): for
`|φ_i + (1 − φ_i)φ_π| ≤ 1` the partial-adjustment rule is not determinate. -/
theorem pa_not_determinate [Nonempty Ω] {φi φπ ρ : ℝ} (hlam : |φi + (1 - φi) * φπ| ≤ 1) :
    ¬ PADeterminate 𝔼 φi φπ ρ := by
  intro hdet
  obtain ⟨h0, h1⟩ := pa_two_solutions 𝔼 φi φπ ρ
  set κ := (1 - φi) * φπ
  set lam := φi + (1 - φi) * φπ
  have hpow : ∀ t : ℕ, |κ * lam ^ t| ≤ |κ| := fun t => by
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hlam)
  have hu := (hdet (fun _ _ => ρ) (fun _ => ρ) ⟨|ρ|, fun t ω => le_rfl⟩ (fun t => 𝔼.const t ρ)
    ⟨|ρ|, fun ω => le_rfl⟩ (𝔼.const 0 ρ)).2 _ _ _ _ h0 h1 (fun t => 𝔼.const t 0)
    (fun t => 𝔼.const t _) ⟨|ρ|, fun t ω => le_rfl⟩ ⟨0, fun t ω => by simp⟩
    ⟨|ρ| + |κ|, fun t ω => (abs_add_le _ _).trans (by linarith [hpow t])⟩
    ⟨1 + |κ|, fun t ω => ?_⟩
  · have := congrFun (congrFun hu.2 0) (Classical.arbitrary Ω)
    simp at this
  · cases t with
    | zero => simp
    | succ t => simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; linarith [hpow t]

/-- Galí (2015), Exercise 2.3(a) (**determinacy criterion**): for `0 ≤ φ_i < 1` the rule of
partial adjustment is determinate iff `|φ_i + (1 − φ_i)φ_π| > 1`. -/
theorem pa_determinate_iff [Nonempty Ω] {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi) (hφi1 : φi < 1) :
    PADeterminate 𝔼 φi φπ ρ ↔ 1 < |φi + (1 - φi) * φπ| := by
  constructor
  · intro hdet
    by_contra h
    exact pa_not_determinate 𝔼 (not_lt.1 h) hdet
  · intro hlam r im1 hrb hra him1 him1a
    exact ⟨pa_exists 𝔼 hφi0 hφi1 hlam hrb hra him1 him1a,
      fun i infl i' infl' heq heq' hx hx' hib hxb hib' hxb' =>
        pa_unique 𝔼 hφi0 hφi1 hlam him1 him1a heq heq' hx hx' hib hxb hib' hxb'⟩

/-- Galí (2015), Exercise 2.3(a) (**the book's answer**): for `0 ≤ φ_i < 1` and `φ_π ≥ 0` the
rule of partial adjustment is determinate iff `φ_π > 1`. -/
theorem pa_determinate_iff_of_nonneg [Nonempty Ω] {φi φπ ρ : ℝ} (hφi0 : 0 ≤ φi)
    (hφi1 : φi < 1) (hφπ : 0 ≤ φπ) : PADeterminate 𝔼 φi φπ ρ ↔ 1 < φπ := by
  rw [pa_determinate_iff 𝔼 hφi0 hφi1, abs_of_nonneg (by positivity)]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

/-- Galí (2015), Exercise 2.3(a) (**correction**: the book allows `φ_i ∈ [0, 1]`): for
`φ_i = 1` the rule is `i_t = i_{t−1}` and the equilibrium is never unique, whatever `φ_π`:
with `r_t = i_{−1} = ρ`, both `π ≡ 0` and `π_0 = 1, π_{t+1} = 0` are bounded equilibria. -/
theorem pa_phi_i_one_not_determinate [Nonempty Ω] (φπ ρ : ℝ) : ¬ PADeterminate 𝔼 1 φπ ρ := by
  intro hdet
  have h0 : PAEquilibrium 𝔼 1 φπ ρ (fun _ _ => ρ) (fun _ => ρ) (fun _ _ => ρ) (fun _ _ => 0) :=
    ⟨fun t => by rw [𝔼.const]; funext ω; simp,
      fun t ω => by cases t <;> simp [lagI_zero, lagI_succ]⟩
  have h1 : PAEquilibrium 𝔼 1 φπ ρ (fun _ _ => ρ) (fun _ => ρ) (fun _ _ => ρ)
      (fun t _ => if t = 0 then 1 else 0) :=
    ⟨fun t => by rw [𝔼.const]; funext ω; simp,
      fun t ω => by cases t <;> simp [lagI_zero, lagI_succ]⟩
  have hu := (hdet (fun _ _ => ρ) (fun _ => ρ) ⟨|ρ|, fun t ω => le_rfl⟩ (fun t => 𝔼.const t ρ)
    ⟨|ρ|, fun ω => le_rfl⟩ (𝔼.const 0 ρ)).2 _ _ _ _ h0 h1 (fun t => 𝔼.const t 0)
    (fun t => 𝔼.const t _) ⟨|ρ|, fun t ω => le_rfl⟩ ⟨0, fun t ω => by simp⟩
    ⟨|ρ|, fun t ω => le_rfl⟩ ⟨1, fun t ω => by dsimp only; split_ifs <;> simp⟩
  have := congrFun (congrFun hu.2 0) (Classical.arbitrary Ω)
  simp at this

/-- Galí (2015), Exercise 2.3(a) (**non-existence at the boundary**): for `0 ≤ φ_i < 1`,
`φ_π = 1` (so `λ = 1`) and the constant real rate `r_t = ρ + 1`, there is no bounded
equilibrium: `E_0 i_t − ρ = (i_0 − ρ) − (1 − φ_i) t` drifts. -/
theorem pa_boundary_nonexistence [Nonempty Ω] {φi ρ : ℝ} (hφi1 : φi < 1) (im1 : Ω → ℝ)
    {i infl : ℕ → Ω → ℝ} (heq : PAEquilibrium 𝔼 φi 1 ρ (fun _ _ => ρ + 1) im1 i infl) :
    ¬ BoundedProc i := by
  rintro ⟨M, hM⟩
  have hra : 𝔼.Adapted (fun _ _ => ρ + 1) := fun t => 𝔼.const t _
  have hia := pa_i_adapted 𝔼 hra heq
  have hstep : ∀ t ω, 𝔼.E t (i (t + 1)) ω = i t ω - (1 - φi) := by
    intro t ω
    have := pa_interest_eq 𝔼 hra heq t ω
    linarith
  have hdrift : ∀ t ω, 𝔼.E 0 (i t) ω = i 0 ω - (1 - φi) * t := by
    intro t
    induction t with
    | zero => intro ω; rw [hia 0]; simp
    | succ t ih =>
      intro ω
      rw [← 𝔼.tower (Nat.zero_le t)]
      have : 𝔼.E t (i (t + 1)) = i t - fun _ => 1 - φi := funext fun ω => by
        rw [hstep t ω]; rfl
      rw [this, map_sub, 𝔼.const]
      simp only [Pi.sub_apply]
      rw [ih ω]
      push_cast
      ring
  set ω := Classical.arbitrary Ω
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / (1 - φi))
  have h1 := 𝔼.abs_E_le (hM n) 0 ω
  rw [hdrift n ω] at h1
  have h2 := hM 0 ω
  rw [div_lt_iff₀ (by linarith)] at hn
  have h3 := neg_abs_le (i 0 ω - (1 - φi) * n)
  have h4 := le_abs_self (i 0 ω)
  nlinarith

/-! ### b–c. Moving-average inflation targeting -/

/-- Galí (2015), Exercise 2.3(b), p. 48: inflation over the whole past: `π_s` for dates
`s ≥ 0` and the pre-sample history `π_{−1−j} = h_j`. -/
def extInfl (infl h : ℕ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun s => if 0 ≤ s then infl s.toNat else h (-s - 1).toNat

/-- Galí (2015), Exercise 2.3(b), p. 48: the moving average
`π̄_s = (1 − δ) ∑_{k ≥ 0} δᵏ π_{s−k}` (a genuine infinite sum). -/
noncomputable def maBar (δ : ℝ) (e : ℤ → Ω → ℝ) (s : ℤ) : Ω → ℝ :=
  fun ω => (1 - δ) * ∑' k : ℕ, δ ^ k * e (s - k) ω

/-- Galí (2015), Exercise 2.3(b): the pre-sample moving average
`π̄_{−1} = (1 − δ) ∑_{j ≥ 0} δʲ h_j`. -/
noncomputable def hbar (δ : ℝ) (h : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => (1 - δ) * ∑' j : ℕ, δ ^ j * h j ω

/-- Galí (2015), Exercise 2.3(b)–(c), p. 48: for `0 ≤ δ < 1` and bounded inflation,
`π̄_s = δ π̄_{s−1} + (1 − δ) π_s`. -/
theorem maBar_succ {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {e : ℤ → Ω → ℝ}
    (he : ∀ s ω, |e s ω| ≤ M) (s : ℤ) (ω : Ω) :
    maBar δ e s ω = δ * maBar δ e (s - 1) ω + (1 - δ) * e s ω := by
  have hsum : Summable (fun k : ℕ => δ ^ k * e (s - k) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hδ0 hδ1).mul_right M) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hδ0]
      exact mul_le_mul_of_nonneg_left (he _ ω) (pow_nonneg hδ0 k))
  unfold maBar
  rw [hsum.tsum_eq_zero_add]
  have e1 : ∑' k : ℕ, δ ^ (k + 1) * e (s - ((k + 1 : ℕ) : ℤ)) ω
      = δ * ∑' k : ℕ, δ ^ k * e (s - 1 - k) ω := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show s - ((k + 1 : ℕ) : ℤ) = s - 1 - k by push_cast; ring, pow_succ]
    ring
  rw [e1]
  simp
  ring

/-- Galí (2015), Exercise 2.3(b): at the sample dates the extended path is `π`. -/
theorem extInfl_nat (infl h : ℕ → Ω → ℝ) (t : ℕ) : extInfl infl h t = infl t := by
  simp [extInfl]

/-- Galí (2015), Exercise 2.3(b): before the sample the extended path is the history `h`. -/
theorem extInfl_neg (infl h : ℕ → Ω → ℝ) (j : ℕ) : extInfl infl h (-1 - j) = h j := by
  have h1 : ¬ (0 : ℤ) ≤ -1 - j := by omega
  have h2 : (-(-1 - (j : ℤ)) - 1).toNat = j := by omega
  simp only [extInfl, h1, ↓reduceIte, h2]

/-- Galí (2015), Exercise 2.3(b): `π̄_{−1}` depends only on the pre-sample history. -/
theorem maBar_neg_one (δ : ℝ) (infl h : ℕ → Ω → ℝ) (ω : Ω) :
    maBar δ (extInfl infl h) (-1) ω = hbar δ h ω := by
  unfold maBar hbar
  congr 1
  refine tsum_congr fun k => ?_
  rw [extInfl_neg]

/-- Galí (2015), Exercise 2.3(b): a bound for the extended inflation path. -/
theorem extInfl_bounded {infl h : ℕ → Ω → ℝ} {M1 M2 : ℝ} (h1 : ∀ t ω, |infl t ω| ≤ M1)
    (h2 : ∀ j ω, |h j ω| ≤ M2) : ∀ s ω, |extInfl infl h s ω| ≤ max M1 M2 := by
  intro s ω
  unfold extInfl
  split_ifs
  · exact (h1 _ ω).trans (le_max_left _ _)
  · exact (h2 _ ω).trans (le_max_right _ _)

/-- Galí (2015), Exercise 2.3(c), p. 48 (**equivalence of the two rules**): for `0 ≤ δ < 1` and
bounded inflation and history, `i_t = ρ + φ_π π̄_t` at every date iff
`i_t = δ i_{t−1} + (1 − δ)(ρ + φ_π π_t)` at every date with `i_{−1} = ρ + φ_π π̄_{−1}`: the
moving-average rule is the partial-adjustment rule with `φ_i = δ`. -/
theorem ma_iff_pa {δ φπ ρ M1 M2 : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {infl h : ℕ → Ω → ℝ}
    (h1 : ∀ t ω, |infl t ω| ≤ M1) (h2 : ∀ j ω, |h j ω| ≤ M2) (i : ℕ → Ω → ℝ) :
    (∀ t ω, i t ω = ρ + φπ * maBar δ (extInfl infl h) t ω) ↔
      ∀ t ω, i t ω = δ * lagI (fun ω => ρ + φπ * hbar δ h ω) i t ω
        + (1 - δ) * (ρ + φπ * infl t ω) := by
  have hb := extInfl_bounded h1 h2
  have hrec : ∀ (t : ℕ) ω, maBar δ (extInfl infl h) t ω
      = δ * maBar δ (extInfl infl h) ((t : ℤ) - 1) ω + (1 - δ) * infl t ω := by
    intro t ω
    rw [maBar_succ hδ0 hδ1 hb, extInfl_nat]
  constructor
  · intro hma t ω
    rw [hma t ω, hrec t ω]
    cases t with
    | zero =>
      simp only [lagI_zero, Nat.cast_zero, zero_sub]
      rw [maBar_neg_one]
      ring
    | succ t =>
      simp only [lagI_succ]
      rw [show ((t + 1 : ℕ) : ℤ) - 1 = t by push_cast; ring, hma t ω]
      ring
  · intro hpa t
    induction t with
    | zero =>
      intro ω
      rw [hpa 0 ω, hrec 0 ω]
      simp only [lagI_zero, Nat.cast_zero, zero_sub]
      rw [maBar_neg_one]
      ring
    | succ t ih =>
      intro ω
      rw [hpa (t + 1) ω, hrec (t + 1) ω]
      simp only [lagI_succ]
      rw [show ((t + 1 : ℕ) : ℤ) - 1 = t by push_cast; ring, ih ω]
      ring

/-- Galí (2015), Exercise 2.3(b), p. 48: equilibrium under the moving-average rule
`i_t = ρ + φ_π π̄_t` with the Fisher equation, given the pre-sample history `h`. -/
def MAEquilibrium (δ φπ ρ : ℝ) (r h i infl : ℕ → Ω → ℝ) : Prop :=
  (∀ t, i t = r t + 𝔼.E t (infl (t + 1))) ∧
    ∀ t ω, i t ω = ρ + φπ * maBar δ (extInfl infl h) t ω

/-- Galí (2015), Exercise 2.3(c), p. 48: for bounded inflation and history the moving-average
equilibria are exactly the partial-adjustment equilibria with `φ_i = δ` and
`i_{−1} = ρ + φ_π π̄_{−1}`. -/
theorem ma_equilibrium_iff_pa {δ φπ ρ M1 M2 : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {r h i infl : ℕ → Ω → ℝ} (h1 : ∀ t ω, |infl t ω| ≤ M1) (h2 : ∀ j ω, |h j ω| ≤ M2) :
    MAEquilibrium 𝔼 δ φπ ρ r h i infl ↔
      PAEquilibrium 𝔼 δ φπ ρ r (fun ω => ρ + φπ * hbar δ h ω) i infl :=
  and_congr_right fun _ => ma_iff_pa hδ0 hδ1 h1 h2 i

/-- Galí (2015), Exercise 2.3(c): conversely, for `φ_π ≠ 0` every initial condition `i_{−1}` of
the partial-adjustment rule is produced by a moving-average history (the constant history
`h_j = (i_{−1} − ρ)/φ_π`). -/
theorem pa_as_ma {δ φπ ρ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hφπ : φπ ≠ 0) (im1 : Ω → ℝ) :
    (fun ω => ρ + φπ * hbar δ (fun _ ω => (im1 ω - ρ) / φπ) ω) = im1 := by
  funext ω
  unfold hbar
  rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
  have : (1 - δ) ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), Exercise 2.3(b): bounds for the pre-sample moving average. -/
theorem hbar_bounded {δ M : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : ℕ → Ω → ℝ}
    (hh : ∀ j ω, |h j ω| ≤ M) (ω : Ω) : |hbar δ h ω| ≤ M := by
  unfold hbar
  have hs : HasSum (fun k : ℕ => δ ^ k * M) ((1 - δ)⁻¹ * M) :=
    (hasSum_geometric_of_lt_one hδ0 hδ1).mul_right M
  have hb := tsum_of_norm_bounded (f := fun j => δ ^ j * h j ω) hs (fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_left (hh k ω) (pow_nonneg hδ0 k))
  rw [Real.norm_eq_abs] at hb
  have h1 : 0 < 1 - δ := by linarith
  rw [abs_mul, abs_of_pos h1]
  calc (1 - δ) * |∑' j, δ ^ j * h j ω| ≤ (1 - δ) * ((1 - δ)⁻¹ * M) := by gcongr
    _ = M := by field_simp

/-- Galí (2015), Exercise 2.3(b): a pre-sample history known at date 0 gives `π̄_{−1}` known at
date 0. -/
theorem hbar_known {δ M ρ φπ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : ℕ → Ω → ℝ}
    (hh : ∀ j ω, |h j ω| ≤ M) (hha : ∀ j, 𝔼.E 0 (h j) = h j) :
    𝔼.E 0 (fun ω => ρ + φπ * hbar δ h ω) = fun ω => ρ + φπ * hbar δ h ω := by
  have hfun : (fun ω => ρ + φπ * hbar δ h ω)
      = (fun _ => ρ) + (φπ * (1 - δ)) • fun ω => ∑' j : ℕ, δ ^ j * h j ω := by
    funext ω
    simp only [hbar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, map_add, map_smul, 𝔼.const]
  congr 2
  funext ω
  rw [𝔼.E_tsum hδ0 hδ1 (f := fun j ω => δ ^ j * h j ω) (M := M) (fun k ω => by
    rw [abs_mul, abs_pow, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_left (hh k ω) (pow_nonneg hδ0 k)) 0 ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E 0 (δ ^ k • h k) ω = _
  rw [map_smul, hha k]
  rfl

/-- Galí (2015), Exercise 2.3(b): determinacy of the moving-average rule: for every bounded
adapted real rate and every bounded pre-sample history known at date 0 there is exactly one
bounded adapted equilibrium. -/
def MADeterminate (δ φπ ρ : ℝ) : Prop :=
  ∀ (r h : ℕ → Ω → ℝ), BoundedProc r → 𝔼.Adapted r → BoundedProc h →
    (∀ j, 𝔼.E 0 (h j) = h j) →
    (∃ i infl, MAEquilibrium 𝔼 δ φπ ρ r h i infl ∧ 𝔼.Adapted i ∧ 𝔼.Adapted infl ∧
      BoundedProc i ∧ BoundedProc infl) ∧
    ∀ i infl i' infl', MAEquilibrium 𝔼 δ φπ ρ r h i infl →
      MAEquilibrium 𝔼 δ φπ ρ r h i' infl' → 𝔼.Adapted infl → 𝔼.Adapted infl' →
      BoundedProc i → BoundedProc infl → BoundedProc i' → BoundedProc infl' →
      i = i' ∧ infl = infl'

/-- Galí (2015), Exercise 2.3(b) (**determinacy criterion**): for `0 ≤ δ < 1` the
moving-average rule is determinate iff `|δ + (1 − δ)φ_π| > 1`. -/
theorem ma_determinate_iff [Nonempty Ω] {δ φπ ρ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    MADeterminate 𝔼 δ φπ ρ ↔ 1 < |δ + (1 - δ) * φπ| := by
  constructor
  · intro hdet
    by_contra hlam
    push Not at hlam
    obtain ⟨p0, p1⟩ := pa_two_solutions 𝔼 δ φπ ρ
    have hh0 : (fun (ω : Ω) => ρ + φπ * hbar δ (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) ω)
        = fun _ => ρ := by
      funext ω
      simp [hbar]
    set κ := (1 - δ) * φπ
    set lam := δ + (1 - δ) * φπ
    have hpow : ∀ t : ℕ, |κ * lam ^ t| ≤ |κ| := fun t => by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hlam)
    have hb1 : ∀ t (ω : Ω), |(if t = 0 then 1 else κ * lam ^ (t - 1))| ≤ 1 + |κ| := by
      intro t ω
      cases t with
      | zero => simp
      | succ t =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        linarith [hpow t]
    have m0 : MAEquilibrium 𝔼 δ φπ ρ (fun _ _ => ρ) (fun _ _ => 0) (fun _ _ => ρ)
        (fun _ _ => 0) := by
      rw [ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 (M1 := 0) (M2 := 0) (fun t ω => by simp)
        (fun j ω => by simp), hh0]
      exact p0
    have m1 : MAEquilibrium 𝔼 δ φπ ρ (fun _ _ => ρ) (fun _ _ => 0)
        (fun t _ => ρ + κ * lam ^ t) (fun t _ => if t = 0 then 1 else κ * lam ^ (t - 1)) := by
      rw [ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 (M1 := 1 + |κ|) (M2 := 0) (fun t ω => hb1 t ω)
        (fun j ω => by simp), hh0]
      exact p1
    have hu := (hdet (fun _ _ => ρ) (fun _ _ => 0) ⟨|ρ|, fun t ω => le_rfl⟩
      (fun t => 𝔼.const t ρ) ⟨0, fun t ω => by simp⟩ (fun j => 𝔼.const 0 0)).2 _ _ _ _ m0 m1
      (fun t => 𝔼.const t 0) (fun t => 𝔼.const t _) ⟨|ρ|, fun t ω => le_rfl⟩
      ⟨0, fun t ω => by simp⟩
      ⟨|ρ| + |κ|, fun t ω => (abs_add_le _ _).trans (by linarith [hpow t])⟩
      ⟨1 + |κ|, hb1⟩
    have := congrFun (congrFun hu.2 0) (Classical.arbitrary Ω)
    simp at this
  · intro hlam r h hrb hra ⟨Mh, hMh⟩ hha
    have him1 : ∃ M, ∀ ω, |(fun ω => ρ + φπ * hbar δ h ω) ω| ≤ M :=
      ⟨|ρ| + |φπ| * Mh, fun ω => (abs_add_le _ _).trans (by
        rw [abs_mul]
        gcongr
        exact hbar_bounded hδ0 hδ1 hMh ω)⟩
    have him1a := hbar_known 𝔼 (ρ := ρ) (φπ := φπ) hδ0 hδ1 hMh hha
    refine ⟨?_, fun i infl i' infl' heq heq' hx hx' hib hxb hib' hxb' => ?_⟩
    · obtain ⟨i, infl, heq, hia, hxa, hib, ⟨Mx, hMx⟩⟩ :=
        pa_exists 𝔼 hδ0 hδ1 hlam hrb hra him1 him1a
      exact ⟨i, infl, (ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 hMx hMh).2 heq, hia, hxa, hib,
        ⟨Mx, hMx⟩⟩
    · obtain ⟨Mx, hMx⟩ := hxb
      obtain ⟨Mx', hMx'⟩ := hxb'
      exact pa_unique 𝔼 hδ0 hδ1 hlam him1 him1a
        ((ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 hMx hMh).1 heq)
        ((ma_equilibrium_iff_pa 𝔼 hδ0 hδ1 hMx' hMh).1 heq') hx hx' hib ⟨Mx, hMx⟩ hib'
        ⟨Mx', hMx'⟩

/-- Galí (2015), Exercise 2.3(b) (**the book's answer**): for `0 ≤ δ < 1` and `φ_π ≥ 0` the
moving-average rule is determinate iff `φ_π > 1`. -/
theorem ma_determinate_iff_of_nonneg [Nonempty Ω] {δ φπ ρ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hφπ : 0 ≤ φπ) : MADeterminate 𝔼 δ φπ ρ ↔ 1 < φπ := by
  rw [ma_determinate_iff 𝔼 hδ0 hδ1, abs_of_nonneg (by positivity)]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

end Gali.ClassicalMonetaryModel.Ex2_3

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.4: the welfare costs of inflation (Lucas 2000)

Galí (2015), Chapter 2, Exercise 2.4, p. 48. Endowment economy with period utility
`U(C, M/P) = ([C ψ(M/(P C))]^{1−σ} − 1)/(1 − σ)` (log for `σ = 1`), `ψ(z) = z/(χ + z)`,
`χ > 0`, `σ > 0`, and budget `P_t C_t + Q_t B_t + M_t ≤ B_{t−1} + M_{t−1} + P_t Y_t`.
With real balances `m = M/P`, `C ψ(m/C) = C m/(χ C + m)` (`aggX_eq`), so
`1/X = 1/C + χ/m` (`inv_aggX`).

## a. Optimality conditions and money demand

* `hasDerivAt_periodUtility_C`, `hasDerivAt_periodUtility_M` (**exact derivatives**):
  `U_C = X^{−σ} m²/(χC + m)²`, `U_m = X^{−σ} χC²/(χC + m)²`; `mrs_money`: `U_m/U_C = χ (C/m)²`.
* Money versus bonds (holding `δ` more money and `δ` fewer bonds leaves `t+1` resources
  unchanged and costs `(1 − Q_t)δ/P_t` of consumption): `money_foc_necessary`,
  `money_foc_sufficient`, `money_optimum_iff`: optimal iff `U_m = (1 − Q_t) U_C`, i.e.
  `(1 − Q_t) m² = χ C²`. `money_demand_iff`: for `Q_t < 1`,
  `M_t/P_t = C_t (χ/(1 − Q_t))^{1/2}`. `no_money_foc_at_zero_rate`: at `Q_t = 1` the condition
  has no solution (no satiation). `money_demand_log`, `hasDerivAt_money_demand_log`: in logs
  `m − p − c = ½ log χ − ½ log(1 − e^{−i})`, interest semi-elasticity `1/(2(e^i − 1))`.
* Bonds (`EulerEq`, `Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`): `euler_necessary` (uniform
  continuity of marginal utility), `euler_necessary_finite`, `euler_sufficient`, using the
  generic results of `Ex2_1`.

## b. The Friedman rule

`eqWelfare σ χ Y i` is equilibrium period utility (`C = Y`, money demand at rate `i`).
`eqWelfare_eq`: it equals `u(Y/(1 + s(i)))`, `s(i) = (χ(1 − e^{−i}))^{1/2}`.
`friedman_rule`: it is strictly decreasing in `i > 0`, below the satiation level `u(Y)`, and
tends to `u(Y)` as `i → 0⁺`; `friedman_rule_inflation`: in a steady state `i = ρ + π`, welfare
strictly decreases in `π > −ρ`, so the optimum is the Friedman rule `π = −ρ`.

## c. The welfare cost of inflation (steady state, `Y = 1`, `i = ρ + π`)

With `s_π = s(ρ + π)`:
* `welfareCost_levels` (consumption raised by `λ`, real balances `M/P` at their `π` level):
  if `s_π < 1 + s_0` then `λ(π) = (s_π − s_0)/(1 + s_0 − s_π)` is the unique compensation
  (`welfareCost_levels_unique`); `welfareCost_levels_none`: otherwise no rise in consumption
  compensates.
* `welfareCost_ratio` (consumption and real balances scaled together, velocity at its `π`
  level): `λ(π) = (s_π − s_0)/(1 + s_0)`, unique (`welfareCost_ratio_unique`).
* `welfareCost_levels_pos_iff`, `welfareCost_ratio_pos_iff`: the cost is positive iff `π > 0`.

## d. Interest-rate fluctuations to second order

* `hasDerivAt_W`, `hasDerivAt_W1`: `W(i) = u(1/(1 + s(i)))` (`Wf`, equal to `eqWelfare` at
  `Y = 1` by `eqWelfare_one_eq_Wf`) has `W' = W1`, `W'' = W2` in
  closed form; `welfare_taylor`: `W(i) = W(ī) + W1(ī)(i − ī) + ½ W2(ī)(i − ī)² + O((i − ī)³)`.
* `welfare_fluctuations`: for `i_t = ī + s ε_t` with `|ε_t| ≤ M`, `E_0 ε_t = 0`,
  `∑ βᵗ E_0 W(i_t) − ∑ βᵗ W(ī) = ½ W2(ī) s² ∑ βᵗ E_0 ε_t² + O(s³)`.
* `W2_pos_of_le_two`, `fluctuations_raise_welfare` (**finding**): for `σ ≤ 2` (including log
  utility) `W'' > 0`, so mean-preserving interest-rate fluctuations *raise* welfare to second
  order: the "losses" of part (d) are negative. `W2_pos_iff` gives the exact sign condition.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_4

open Filter Topology

/-! ### Utility -/

/-- Galí (2015), Exercise 2.4, p. 48: `ψ(z) = z/(χ + z)`. -/
noncomputable def psi (χ z : ℝ) : ℝ := z / (χ + z)

/-- Galí (2015), Exercise 2.4, p. 48: the composite `X = C ψ(m/C)`, `m = M/P`. -/
noncomputable def aggX (χ C m : ℝ) : ℝ := C * psi χ (m / C)

/-- Galí (2015), Exercise 2.4, p. 48: period utility `U(C, M/P) = u(C ψ(M/(P C)))` with
`u(x) = (x^{1−σ} − 1)/(1 − σ)` (`log x` for `σ = 1`). -/
noncomputable def periodUtility (σ χ C m : ℝ) : ℝ := Ex2_1.utilC σ (aggX χ C m)

/-- Galí (2015), Exercise 2.4: `C ψ(m/C) = C m/(χ C + m)`. -/
theorem aggX_eq {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    aggX χ C m = C * m / (χ * C + m) := by
  have h : 0 < χ * C + m := by positivity
  unfold aggX psi
  field_simp

/-- Galí (2015), Exercise 2.4: `X > 0`. -/
theorem aggX_pos {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) : 0 < aggX χ C m := by
  rw [aggX_eq hχ hC hm]
  positivity

/-- Galí (2015), Exercise 2.4: `1/X = 1/C + χ/m`. -/
theorem inv_aggX {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    (aggX χ C m)⁻¹ = C⁻¹ + χ / m := by
  rw [aggX_eq hχ hC hm]
  field_simp
  ring

/-- Galí (2015), Exercise 2.4: marginal utility of consumption `U_C = X^{−σ} m²/(χ C + m)²`. -/
noncomputable def margUtilC (σ χ C m : ℝ) : ℝ :=
  (C * m / (χ * C + m)) ^ (-σ) * (m ^ 2 / (χ * C + m) ^ 2)

/-- Galí (2015), Exercise 2.4: marginal utility of real balances
`U_m = X^{−σ} χ C²/(χ C + m)²`. -/
noncomputable def margUtilM (σ χ C m : ℝ) : ℝ :=
  (C * m / (χ * C + m)) ^ (-σ) * (χ * C ^ 2 / (χ * C + m) ^ 2)

/-- Galí (2015), Exercise 2.4 (**exact derivative**): `∂X/∂C = m²/(χ C + m)²`. -/
theorem hasDerivAt_aggX_C {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun C' => aggX χ C' m) (m ^ 2 / (χ * C + m) ^ 2) C := by
  have hD : χ * C + m ≠ 0 := by positivity
  have h : HasDerivAt (fun C' => C' * m / (χ * C' + m)) (m ^ 2 / (χ * C + m) ^ 2) C := by
    have := ((hasDerivAt_id' C).mul_const m).div
      (((hasDerivAt_id' C).const_mul χ).add_const m) hD
    refine this.congr_deriv ?_
    field_simp
    ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hC] with C' hC'
  exact aggX_eq hχ hC' hm

/-- Galí (2015), Exercise 2.4 (**exact derivative**): `∂X/∂m = χ C²/(χ C + m)²`. -/
theorem hasDerivAt_aggX_M {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun m' => aggX χ C m') (χ * C ^ 2 / (χ * C + m) ^ 2) m := by
  have hD : χ * C + m ≠ 0 := by positivity
  have h : HasDerivAt (fun m' => C * m' / (χ * C + m')) (χ * C ^ 2 / (χ * C + m) ^ 2) m := by
    have := ((hasDerivAt_id' m).const_mul C).div ((hasDerivAt_id' m).const_add (χ * C)) hD
    refine this.congr_deriv ?_
    field_simp
    ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hm] with m' hm'
  exact aggX_eq hχ hC hm'

/-- Galí (2015), Exercise 2.4(a) (**exact derivative**): `∂U/∂C = margUtilC`. -/
theorem hasDerivAt_periodUtility_C (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C)
    (hm : 0 < m) : HasDerivAt (fun C' => periodUtility σ χ C' m) (margUtilC σ χ C m) C := by
  have h := (Ex2_1.hasDerivAt_utilC σ (aggX_pos hχ hC hm)).comp C (hasDerivAt_aggX_C hχ hC hm)
  rw [aggX_eq hχ hC hm] at h
  exact h

/-- Galí (2015), Exercise 2.4(a) (**exact derivative**): `∂U/∂m = margUtilM`. -/
theorem hasDerivAt_periodUtility_M (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C)
    (hm : 0 < m) : HasDerivAt (fun m' => periodUtility σ χ C m') (margUtilM σ χ C m) m := by
  have h := (Ex2_1.hasDerivAt_utilC σ (aggX_pos hχ hC hm)).comp m (hasDerivAt_aggX_M hχ hC hm)
  rw [aggX_eq hχ hC hm] at h
  exact h

/-- Galí (2015), Exercise 2.4(a): `U_m/U_C = χ (C/m)²`. -/
theorem mrs_money (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    margUtilM σ χ C m / margUtilC σ χ C m = χ * (C / m) ^ 2 := by
  have hD : 0 < χ * C + m := by positivity
  have hX : 0 < (C * m / (χ * C + m)) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  unfold margUtilM margUtilC
  field_simp

/-! ### a. Money versus bonds: the demand for real balances -/

/-- Galí (2015), Exercise 2.4(a): date-`t` utility after holding `δ` more money and `δ` fewer
bonds: consumption falls by `(1 − Q)δ/P`, real balances rise by `δ/P`, and date-`t+1`
resources are unchanged. -/
noncomputable def swapValue (σ χ Q P C m δ : ℝ) : ℝ :=
  periodUtility σ χ (C - (1 - Q) * δ / P) (m + δ / P)

/-- Galí (2015), Exercise 2.4(a): along the money-bond swap, `X` has derivative
`(χ C² − (1 − Q) m²)/(P (χ C + m)²)` at `δ = 0`. -/
theorem hasDerivAt_swap_aggX {χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) :
    HasDerivAt (fun δ => aggX χ (C - (1 - Q) * δ / P) (m + δ / P))
      ((χ * C ^ 2 - (1 - Q) * m ^ 2) / (P * (χ * C + m) ^ 2)) 0 := by
  have hD : χ * C + m ≠ 0 := by positivity
  have hc : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa [mul_div_assoc] using this
  have hmm : HasDerivAt (fun δ : ℝ => m + δ / P) (1 / P) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).div_const P).const_add m
  have hden : (fun δ : ℝ => χ * (C - (1 - Q) * δ / P) + (m + δ / P)) 0 ≠ 0 := by
    simpa using hD
  have h := HasDerivAt.div (HasDerivAt.mul hc hmm) (HasDerivAt.add (hc.const_mul χ) hmm) hden
  have h' : HasDerivAt (fun δ => (C - (1 - Q) * δ / P) * (m + δ / P)
      / (χ * (C - (1 - Q) * δ / P) + (m + δ / P)))
      ((χ * C ^ 2 - (1 - Q) * m ^ 2) / (P * (χ * C + m) ^ 2)) 0 := by
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.add_apply, mul_zero, zero_div, sub_zero, add_zero]
    field_simp
    ring
  refine h'.congr_of_eventuallyEq ?_
  have hc1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - (1 - Q) * δ / P :=
    (hc.continuousAt.tendsto).eventually_const_lt (by simpa using hC)
  have hm1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < m + δ / P :=
    (hmm.continuousAt.tendsto).eventually_const_lt (by simpa using hm)
  filter_upwards [hc1, hm1] with δ h1 h2
  exact aggX_eq hχ h1 h2

/-- Galí (2015), Exercise 2.4(a) (**necessity**): if the money-bond swap has a local maximum at
`δ = 0` (with `χ > 0`, `P, C, m > 0`), then `(1 − Q) m² = χ C²`, i.e. `U_m = (1 − Q) U_C`. -/
theorem money_foc_necessary {σ χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) (hloc : IsLocalMax (swapValue σ χ Q P C m) 0) :
    (1 - Q) * m ^ 2 = χ * C ^ 2 := by
  have hX := hasDerivAt_swap_aggX (Q := Q) hχ hP hC hm
  have hpos : 0 < aggX χ (C - (1 - Q) * 0 / P) (m + 0 / P) := by
    simpa using aggX_pos hχ hC hm
  have hu := (Ex2_1.hasDerivAt_utilC σ hpos).comp 0 hX
  have h0 := hloc.hasDerivAt_eq_zero hu
  have hr : 0 < aggX χ (C - (1 - Q) * 0 / P) (m + 0 / P) ^ (-σ) := Real.rpow_pos_of_pos hpos _
  have h1 := (mul_eq_zero.1 h0).resolve_left hr.ne'
  have hD : 0 < P * (χ * C + m) ^ 2 := by positivity
  rw [div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · linarith
  · linarith

/-- Galí (2015), Exercise 2.4(a): `1/y ≥ 1/x − (y − x)/x²` for `x, y > 0` (convexity of `1/x`). -/
theorem inv_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : x⁻¹ - (y - x) / x ^ 2 ≤ y⁻¹ := by
  have h : y⁻¹ - (x⁻¹ - (y - x) / x ^ 2) = (y - x) ^ 2 / (x ^ 2 * y) := by
    field_simp
    ring
  have : 0 ≤ (y - x) ^ 2 / (x ^ 2 * y) := by positivity
  linarith

/-- Galí (2015), Exercise 2.4(a) (**sufficiency**): if `(1 − Q) m² = χ C²`, no feasible
money-bond swap `δ` (keeping consumption and real balances positive) raises utility. -/
theorem money_foc_sufficient {σ χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) (hfoc : (1 - Q) * m ^ 2 = χ * C ^ 2) {δ : ℝ}
    (hc : 0 < C - (1 - Q) * δ / P) (hm' : 0 < m + δ / P) :
    swapValue σ χ Q P C m δ ≤ swapValue σ χ Q P C m 0 := by
  unfold swapValue periodUtility
  simp only [mul_zero, zero_div, sub_zero, add_zero]
  have h1 := inv_tangent hC hc
  have h2 := inv_tangent hm hm'
  have hinv : (aggX χ C m)⁻¹ ≤ (aggX χ (C - (1 - Q) * δ / P) (m + δ / P))⁻¹ := by
    rw [inv_aggX hχ hC hm, inv_aggX hχ hc hm']
    have e : (C - (1 - Q) * δ / P - C) / C ^ 2 + χ * ((m + δ / P - m) / m ^ 2) = 0 := by
      field_simp
      linear_combination (-δ) * hfoc
    have h3 : χ * (m⁻¹ - (m + δ / P - m) / m ^ 2) ≤ χ * (m + δ / P)⁻¹ :=
      mul_le_mul_of_nonneg_left h2 hχ
    rw [div_eq_mul_inv χ m, div_eq_mul_inv χ (m + δ / P)]
    nlinarith
  have hle := (inv_le_inv₀ (aggX_pos hχ hC hm) (aggX_pos hχ hc hm')).1 hinv
  exact (Ex2_1.utilC_strictMonoOn σ).monotoneOn (aggX_pos hχ hc hm') (aggX_pos hχ hC hm) hle

/-- Galí (2015), Exercise 2.4(a): for `χ ≥ 0` and `C, m > 0`, holding real balances `m` is
optimal against every feasible money-bond swap iff `(1 − Q) m² = χ C²`
(`U_m/U_C = 1 − Q`, cf. eq. (33), p. 33). -/
theorem money_optimum_iff {σ χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) :
    (∀ δ, 0 < C - (1 - Q) * δ / P → 0 < m + δ / P →
      swapValue σ χ Q P C m δ ≤ swapValue σ χ Q P C m 0) ↔ (1 - Q) * m ^ 2 = χ * C ^ 2 := by
  constructor
  · intro h
    refine money_foc_necessary (σ := σ) hχ hP hC hm ?_
    have hc : Continuous fun δ : ℝ => C - (1 - Q) * δ / P := by fun_prop
    have hmc : Continuous fun δ : ℝ => m + δ / P := by fun_prop
    filter_upwards [(hc.tendsto 0).eventually_const_lt (by simpa using hC),
      (hmc.tendsto 0).eventually_const_lt (by simpa using hm)] with δ h1 h2
    exact h δ h1 h2
  · intro h δ h1 h2
    exact money_foc_sufficient hχ hP hC hm h h1 h2

/-- Galí (2015), Exercise 2.4(a) (**money demand**): for `χ > 0`, `Q < 1` and `C, m > 0`,
`(1 − Q) m² = χ C²` iff `M/P = C (χ/(1 − Q))^{1/2}`. -/
theorem money_demand_iff {χ Q C m : ℝ} (hχ : 0 < χ) (hQ : Q < 1) (hC : 0 < C) (hm : 0 < m) :
    (1 - Q) * m ^ 2 = χ * C ^ 2 ↔ m = C * Real.sqrt (χ / (1 - Q)) := by
  have h1 : 0 < 1 - Q := by linarith
  have hs : Real.sqrt (χ / (1 - Q)) ^ 2 = χ / (1 - Q) := Real.sq_sqrt (by positivity)
  constructor
  · intro h
    have hpos : 0 ≤ C * Real.sqrt (χ / (1 - Q)) := by positivity
    refine (pow_left_inj₀ hm.le hpos two_ne_zero).1 ?_
    rw [mul_pow, hs]
    field_simp
    linarith
  · intro h
    rw [h, mul_pow, hs]
    field_simp

/-- Galí (2015), Exercise 2.4(a): at a zero nominal rate (`Q = 1`) the money condition
`(1 − Q) m² = χ C²` has no solution with `χ, C > 0`: real balances are never satiated. -/
theorem no_money_foc_at_zero_rate {χ C m : ℝ} (hχ : 0 < χ) (hC : 0 < C) :
    (1 - 1) * m ^ 2 ≠ χ * C ^ 2 := by
  have : 0 < χ * C ^ 2 := by positivity
  simp only [sub_self, zero_mul]
  exact this.ne

/-- Galí (2015), Exercise 2.4(a) (**money demand in logs**, exact): with `Q = e^{−i}`, `i > 0`,
`log m − log C = ½ log χ − ½ log(1 − e^{−i})`. -/
theorem money_demand_log {χ i C : ℝ} (hχ : 0 < χ) (hi : 0 < i) (hC : 0 < C) :
    Real.log (C * Real.sqrt (χ / (1 - Real.exp (-i)))) - Real.log C
      = 1 / 2 * Real.log χ - 1 / 2 * Real.log (1 - Real.exp (-i)) := by
  have he : Real.exp (-i) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h1 : 0 < 1 - Real.exp (-i) := by linarith
  rw [Real.log_mul hC.ne' (Real.sqrt_pos.2 (by positivity)).ne', Real.log_sqrt (by positivity),
    Real.log_div hχ.ne' h1.ne']
  ring

/-- Galí (2015), Exercise 2.4(a) (**exact derivative**): the log money demand
`½ log χ − ½ log(1 − e^{−i})` has derivative `−1/(2(e^i − 1))` in `i > 0`: the interest
semi-elasticity is `η(i) = 1/(2(e^i − 1))`. -/
theorem hasDerivAt_money_demand_log (χ : ℝ) {i : ℝ} (hi : 0 < i) :
    HasDerivAt (fun i => 1 / 2 * Real.log χ - 1 / 2 * Real.log (1 - Real.exp (-i)))
      (-(1 / (2 * (Real.exp i - 1)))) i := by
  have he : Real.exp (-i) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hei : 1 < Real.exp i := Real.one_lt_exp_iff.2 hi
  have hexp : HasDerivAt (fun i => Real.exp (-i)) (-Real.exp (-i)) i := by
    have := (hasDerivAt_neg i).exp
    convert this using 1
    ring
  have h := ((hexp.const_sub 1).log (by linarith)).const_mul (1 / 2) |>.const_sub
    (1 / 2 * Real.log χ)
  refine h.congr_deriv ?_
  rw [Real.exp_neg]
  have : Real.exp i - 1 ≠ 0 := by linarith
  field_simp

/-! ### a. The Euler equation for bonds -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 2.4(a) and eq. (5), p. 19, node by node:
`Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`, with `U_C` evaluated at `(C, M/P)`. -/
def EulerEq (β σ χ : ℝ) (Q C m P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω * margUtilC σ χ (C t ω) (m t ω) / P t ω =
    β * 𝔼.E t (fun ω' => margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') ω

/-- Galí (2015), Exercise 2.4(a): expected utility at node `ω` after buying `δ` more bonds at
`t` and consuming the payoff at `t + 1`, money holdings unchanged. -/
noncomputable def perturbedValue (β σ χ : ℝ) (Q C m P : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => periodUtility σ χ (C t ω - Q t ω * δ / P t ω) (m t ω)
    + β * 𝔼.E t (fun ω' => periodUtility σ χ (C (t + 1) ω' + δ / P (t + 1) ω') (m (t + 1) ω')) ω

/-- Galí (2015), Exercise 2.4(a): `U_C` is nonincreasing in `C` (`σ > 0`, `χ ≥ 0`, `m > 0`). -/
theorem margUtilC_antitoneOn {σ χ m : ℝ} (hσ : 0 < σ) (hχ : 0 ≤ χ) (hm : 0 < m) :
    AntitoneOn (fun C => margUtilC σ χ C m) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hDa : 0 < χ * a + m := by positivity
  have hDb : 0 < χ * b + m := by positivity
  have hX : a * m / (χ * a + m) ≤ b * m / (χ * b + m) := by
    rw [div_le_div_iff₀ hDa hDb]
    nlinarith [mul_pos hm hm]
  have h1 : (b * m / (χ * b + m)) ^ (-σ) ≤ (a * m / (χ * a + m)) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hX (by linarith)
  have h2 : m ^ 2 / (χ * b + m) ^ 2 ≤ m ^ 2 / (χ * a + m) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : χ * a + m ≤ χ * b + m := by nlinarith
    exact pow_le_pow_left₀ hDa.le this 2
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Galí (2015), Exercise 2.4(a): `U_C` is continuous in `C` at `C > 0`. -/
theorem margUtilC_continuousAt (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    ContinuousAt (fun C' => margUtilC σ χ C' m) C := by
  have hD : χ * C + m ≠ 0 := by positivity
  have hX : C * m / (χ * C + m) ≠ 0 := by positivity
  unfold margUtilC
  refine ContinuousAt.mul ?_ ?_
  · exact ((continuousAt_id.mul continuousAt_const).div
      (continuousAt_const.mul continuousAt_id |>.add continuousAt_const) hD).rpow_const
      (Or.inl hX)
  · exact continuousAt_const.div
      ((continuousAt_const.mul continuousAt_id |>.add continuousAt_const).pow 2) (by positivity)

/-- Galí (2015), Exercise 2.4(a) (**necessity of the Euler equation**): if no small bond
perturbation is profitable at any date-`t` node, the Euler equation holds. Hypotheses: `σ > 0`,
`χ ≥ 0`, positive consumption, real balances and prices, a uniform lower bound
`k ≤ P_{t+1} C_{t+1}` and a uniform modulus of continuity of `U_{C,t+1}` (automatic with
finitely many states, `euler_necessary_finite`). -/
theorem euler_necessary {β σ χ : ℝ} {Q C m P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hχ : 0 ≤ χ)
    (hC : ∀ ω, 0 < C t ω) (hm : ∀ ω, 0 < m t ω) (hP : ∀ ω, 0 < P t ω)
    (hm1 : ∀ ω, 0 < m (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    {k : ℝ} (hk : 0 < k) (hkPC : ∀ ω, k ≤ P (t + 1) ω * C (t + 1) ω)
    (huc : ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω,
      |margUtilC σ χ (C (t + 1) ω + h / P (t + 1) ω) (m (t + 1) ω)
        - margUtilC σ χ (C (t + 1) ω) (m (t + 1) ω)| / P (t + 1) ω ≤ ε)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ χ Q C m P t δ ω) 0) :
    EulerEq 𝔼 β σ χ Q C m P t := by
  intro ω
  have hG := Ex2_1.uniform_of_concave (u := fun ω' c => periodUtility σ χ c (m (t + 1) ω'))
    (D := fun ω' c => margUtilC σ χ c (m (t + 1) ω')) hk hP1 hkPC
    (fun ω' x hx => hasDerivAt_periodUtility_C σ hχ hx (hm1 ω'))
    (fun ω' => margUtilC_antitoneOn hσ hχ (hm1 ω')) huc
  have hin : HasDerivAt (fun δ : ℝ => C t ω - Q t ω * δ / P t ω) (-(Q t ω / P t ω)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (Q t ω)).div_const (P t ω)).const_sub (C t ω)
    simpa [mul_div_assoc] using this
  have hu : HasDerivAt (fun c => periodUtility σ χ c (m t ω)) (margUtilC σ χ (C t ω) (m t ω))
      (C t ω - Q t ω * 0 / P t ω) := by
    simpa using hasDerivAt_periodUtility_C σ hχ (hC ω) (hm ω)
  have h := Ex2_1.euler_necessary_generic 𝔼 (hu.comp 0 hin) hG t ω (hopt ω)
  have hP0 := (hP ω).ne'
  have e : Q t ω * margUtilC σ χ (C t ω) (m t ω) / P t ω
      = -(margUtilC σ χ (C t ω) (m t ω) * -(Q t ω / P t ω)) := by
    field_simp
  rw [e]
  linarith

/-- Galí (2015), Exercise 2.4(a) (**necessity**, finitely many states). -/
theorem euler_necessary_finite [Finite Ω] {β σ χ : ℝ} {Q C m P : ℕ → Ω → ℝ} {t : ℕ}
    (hσ : 0 < σ) (hχ : 0 ≤ χ) (hC : ∀ ω, 0 < C t ω) (hm : ∀ ω, 0 < m t ω)
    (hP : ∀ ω, 0 < P t ω) (hC1 : ∀ ω, 0 < C (t + 1) ω) (hm1 : ∀ ω, 0 < m (t + 1) ω)
    (hP1 : ∀ ω, 0 < P (t + 1) ω)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ χ Q C m P t δ ω) 0) :
    EulerEq 𝔼 β σ χ Q C m P t := by
  obtain ⟨k, hk, hkPC⟩ : ∃ k, 0 < k ∧ ∀ ω, k ≤ P (t + 1) ω * C (t + 1) ω := by
    rcases isEmpty_or_nonempty Ω with hΩ | hΩ
    · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
    · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P (t + 1) ω * C (t + 1) ω
      exact ⟨_, mul_pos (hP1 ω₀) (hC1 ω₀), h₀⟩
  exact euler_necessary 𝔼 hσ hχ hC hm hP hm1 hP1 hk hkPC
    (Ex2_1.uniformCont_of_finite (D := fun ω' c => margUtilC σ χ c (m (t + 1) ω'))
      (fun ω' => margUtilC_continuousAt σ hχ (hC1 ω') (hm1 ω'))) hopt

/-- Galí (2015), Exercise 2.4(a) (**sufficiency** of the Euler equation, by concavity in
consumption): no feasible bond perturbation raises expected utility. -/
theorem euler_sufficient {β σ χ : ℝ} {Q C m P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hχ : 0 ≤ χ) (hC : ∀ ω, 0 < C t ω) (hm : ∀ ω, 0 < m t ω) (hP : ∀ ω, 0 < P t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hm1 : ∀ ω, 0 < m (t + 1) ω)
    (heul : EulerEq 𝔼 β σ χ Q C m P t) {δ : ℝ} (ω : Ω)
    (hfeas : 0 < C t ω - Q t ω * δ / P t ω)
    (hfeas1 : ∀ ω', 0 < C (t + 1) ω' + δ / P (t + 1) ω') :
    perturbedValue 𝔼 β σ χ Q C m P t δ ω ≤ perturbedValue 𝔼 β σ χ Q C m P t 0 ω := by
  have hP0 := (hP ω).ne'
  have hf := Ex2_1.tangent_of_deriv (hC ω) hfeas
    (fun x hx => hasDerivAt_periodUtility_C σ hχ hx (hm ω)) (margUtilC_antitoneOn hσ hχ (hm ω))
  have hG : ∀ ω', periodUtility σ χ (C (t + 1) ω' + δ / P (t + 1) ω') (m (t + 1) ω')
      ≤ periodUtility σ χ (C (t + 1) ω' + 0 / P (t + 1) ω') (m (t + 1) ω')
        + δ * (margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') := by
    intro ω'
    have := Ex2_1.tangent_of_deriv (hC1 ω') (hfeas1 ω')
      (fun x hx => hasDerivAt_periodUtility_C σ hχ hx (hm1 ω'))
      (margUtilC_antitoneOn hσ hχ (hm1 ω'))
    rw [zero_div, add_zero]
    have e : margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω')
        * (C (t + 1) ω' + δ / P (t + 1) ω' - C (t + 1) ω')
        = δ * (margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') := by ring
    linarith
  have hfoc : -(margUtilC σ χ (C t ω) (m t ω) * Q t ω / P t ω)
      + β * 𝔼.E t (fun ω' => margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') ω
      = 0 := by
    have := heul ω
    rw [← this]
    ring
  have h := Ex2_1.euler_sufficient_generic 𝔼
    (f := fun δ => periodUtility σ χ (C t ω - Q t ω * δ / P t ω) (m t ω))
    (G := fun δ ω' => periodUtility σ χ (C (t + 1) ω' + δ / P (t + 1) ω') (m (t + 1) ω'))
    (a := -(margUtilC σ χ (C t ω) (m t ω) * Q t ω / P t ω)) hβ ?_ hG t ω hfoc
  · exact h
  · simp only [mul_zero, zero_div, sub_zero]
    have e : margUtilC σ χ (C t ω) (m t ω) * (C t ω - Q t ω * δ / P t ω - C t ω)
        = δ * -(margUtilC σ χ (C t ω) (m t ω) * Q t ω / P t ω) := by ring
    linarith

/-! ### b. The Friedman rule -/

/-- Galí (2015), Exercise 2.4(b): `s(i) = (χ(1 − e^{−i}))^{1/2}`, which equals `χ/(M/(PC))` on
the money-demand schedule. -/
noncomputable def sRate (χ i : ℝ) : ℝ := Real.sqrt (χ * (1 - Real.exp (-i)))

/-- Galí (2015), Exercise 2.4(a)–(b): the money demand `M/(PC) = (χ/(1 − e^{−i}))^{1/2}`. -/
noncomputable def zDemand (χ i : ℝ) : ℝ := Real.sqrt (χ / (1 - Real.exp (-i)))

/-- Galí (2015), Exercise 2.4(b): equilibrium period utility with `C = Y` and real balances on
the money-demand schedule at the nominal rate `i`. -/
noncomputable def eqWelfare (σ χ Y i : ℝ) : ℝ := periodUtility σ χ Y (Y * zDemand χ i)

/-- Galí (2015), Exercise 2.4: `0 < 1 − e^{−i}` for `i > 0`. -/
theorem one_sub_exp_neg_pos {i : ℝ} (hi : 0 < i) : 0 < 1 - Real.exp (-i) := by
  have : Real.exp (-i) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- Galí (2015), Exercise 2.4(b): `M/(PC) > 0` for `i > 0`. -/
theorem zDemand_pos {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) : 0 < zDemand χ i :=
  Real.sqrt_pos.2 (div_pos hχ (one_sub_exp_neg_pos hi))

/-- Galí (2015), Exercise 2.4(b): `s(i) > 0` for `i > 0`. -/
theorem sRate_pos {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) : 0 < sRate χ i :=
  Real.sqrt_pos.2 (mul_pos hχ (one_sub_exp_neg_pos hi))

/-- Galí (2015), Exercise 2.4(b): on the money-demand schedule `χ/(M/(PC)) = s(i)`. -/
theorem chi_div_zDemand {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) : χ / zDemand χ i = sRate χ i := by
  have h1 := one_sub_exp_neg_pos hi
  have hz := zDemand_pos hχ hi
  refine (pow_left_inj₀ (div_pos hχ hz).le (sRate_pos hχ hi).le two_ne_zero).1 ?_
  rw [div_pow, zDemand, sRate, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- Galí (2015), Exercise 2.4(b): equilibrium utility is `u(Y/(1 + s(i)))`. -/
theorem eqWelfare_eq (σ : ℝ) {χ Y i : ℝ} (hχ : 0 < χ) (hY : 0 < Y) (hi : 0 < i) :
    eqWelfare σ χ Y i = Ex2_1.utilC σ (Y / (1 + sRate χ i)) := by
  have hz := zDemand_pos hχ hi
  have hs := sRate_pos hχ hi
  unfold eqWelfare periodUtility
  congr 1
  have hX := inv_aggX hχ.le hY (mul_pos hY hz)
  rw [show χ / (Y * zDemand χ i) = (χ / zDemand χ i) / Y by field_simp, chi_div_zDemand hχ hi]
    at hX
  have hXpos := aggX_pos hχ.le hY (mul_pos hY hz)
  have : aggX χ Y (Y * zDemand χ i) = ((aggX χ Y (Y * zDemand χ i))⁻¹)⁻¹ := (inv_inv _).symm
  rw [this, hX]
  field_simp

/-- Galí (2015), Exercise 2.4(b): `s` is strictly increasing on `[0, ∞)`. -/
theorem sRate_strictMonoOn {χ : ℝ} (hχ : 0 < χ) : StrictMonoOn (sRate χ) (Set.Ici 0) := by
  intro a ha b _ hab
  have ha' : (0 : ℝ) ≤ a := ha
  have h1 : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.2 (by linarith)
  have h2 : 0 ≤ 1 - Real.exp (-a) := by
    have : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  exact Real.sqrt_lt_sqrt (mul_nonneg hχ.le h2) (by nlinarith)

/-- Galí (2015), Exercise 2.4(b): `s` is continuous and `s(0) = 0`. -/
theorem sRate_continuous (χ : ℝ) : Continuous (sRate χ) := by
  unfold sRate
  fun_prop

/-- Galí (2015), Exercise 2.4(b) (**the Friedman rule is optimal**): for `χ > 0` and every
endowment realisation `Y > 0`, equilibrium utility is strictly decreasing in the nominal rate
`i > 0`, lies strictly below the satiation level `u(Y)`, and tends to `u(Y)` as `i → 0⁺`;
since `i ≥ 0` (`Q ≤ 1`), welfare is maximised by driving the nominal rate to zero. -/
theorem friedman_rule (σ : ℝ) {χ Y : ℝ} (hχ : 0 < χ) (hY : 0 < Y) :
    StrictAntiOn (eqWelfare σ χ Y) (Set.Ioi 0) ∧
      (∀ i, 0 < i → eqWelfare σ χ Y i < Ex2_1.utilC σ Y) ∧
      Tendsto (eqWelfare σ χ Y) (𝓝[>] 0) (𝓝 (Ex2_1.utilC σ Y)) := by
  have hpos : ∀ i, 0 < i → 0 < Y / (1 + sRate χ i) := fun i hi => by
    have := sRate_pos hχ hi
    positivity
  refine ⟨fun a ha b hb hab => ?_, fun i hi => ?_, ?_⟩
  · rw [eqWelfare_eq σ hχ hY ha, eqWelfare_eq σ hχ hY hb]
    refine Ex2_1.utilC_strictMonoOn σ (hpos b hb) (hpos a ha) ?_
    have hs := sRate_strictMonoOn hχ (Set.mem_Ici.2 (le_of_lt ha))
      (Set.mem_Ici.2 (le_of_lt hb)) hab
    have := sRate_pos hχ ha
    exact div_lt_div_of_pos_left hY (by positivity) (by linarith)
  · rw [eqWelfare_eq σ hχ hY hi]
    refine Ex2_1.utilC_strictMonoOn σ (hpos i hi) hY ?_
    have := sRate_pos hχ hi
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · have hs0 : sRate χ 0 = 0 := by simp [sRate]
    have hlim : Tendsto (fun i => Y / (1 + sRate χ i)) (𝓝[>] 0) (𝓝 Y) := by
      have h := ((sRate_continuous χ).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rw [hs0] at h
      have h2 := (tendsto_const_nhds (x := Y)).div (h.const_add 1) (by norm_num)
      rw [add_zero, div_one] at h2
      exact h2
    have hu := ((Ex2_1.hasDerivAt_utilC σ hY).continuousAt.tendsto).comp hlim
    refine hu.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with i hi
    exact (eqWelfare_eq σ hχ hY hi).symm

/-- Galí (2015), Exercise 2.4(b): in a steady state with `i = ρ + π`, equilibrium utility is
strictly decreasing in inflation `π > −ρ`, so the optimum is the Friedman rule `π = −ρ`. -/
theorem friedman_rule_inflation (σ ρ : ℝ) {χ Y : ℝ} (hχ : 0 < χ) (hY : 0 < Y) :
    StrictAntiOn (fun π => eqWelfare σ χ Y (ρ + π)) (Set.Ioi (-ρ)) := by
  intro a ha b hb hab
  have ha' : -ρ < a := ha
  have hb' : -ρ < b := hb
  exact (friedman_rule σ hχ hY).1 (show (0 : ℝ) < ρ + a by linarith)
    (show (0 : ℝ) < ρ + b by linarith) (by linarith)

/-! ### c. The welfare cost of inflation -/

/-- Galí (2015), Exercise 2.4(c): on the money-demand schedule, `1/X(C, m) = 1/C + s(i)` when
real balances are `m = zDemand χ i` (steady state `C = 1`) held fixed while `C` varies. -/
theorem inv_aggX_demand {χ C i : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hi : 0 < i) :
    (aggX χ C (zDemand χ i))⁻¹ = C⁻¹ + sRate χ i := by
  rw [inv_aggX hχ.le hC (zDemand_pos hχ hi), chi_div_zDemand hχ hi]

/-- Galí (2015), Exercise 2.4(c): the welfare cost (consumption raised by `λ`, real balances at
their `π` level): `λ(π) = (s_π − s_0)/(1 + s_0 − s_π)`, `s_π = s(ρ + π)`. -/
noncomputable def welfareCostLevels (χ ρ π : ℝ) : ℝ :=
  (sRate χ (ρ + π) - sRate χ ρ) / (1 + sRate χ ρ - sRate χ (ρ + π))

/-- Galí (2015), Exercise 2.4(c): indifference between steady-state inflation `π` with
consumption `1 + λ` and zero inflation with consumption `1` holds iff
`1/(1 + λ) + s_π = 1 + s_0` (real balances at their own steady-state levels). -/
theorem indifference_levels_iff (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l) :
    periodUtility σ χ (1 + l) (zDemand χ (ρ + π)) = periodUtility σ χ 1 (zDemand χ ρ) ↔
      (1 + l)⁻¹ + sRate χ (ρ + π) = 1 + sRate χ ρ := by
  have hi : 0 < ρ + π := by linarith
  have hl1 : 0 < 1 + l := by linarith
  have hA := aggX_pos hχ.le hl1 (zDemand_pos hχ hi)
  have hB := aggX_pos hχ.le one_pos (zDemand_pos hχ hρ)
  unfold periodUtility
  rw [(Ex2_1.utilC_strictMonoOn σ).injOn.eq_iff hA hB, ← inv_inj, inv_aggX_demand hχ hl1 hi,
    inv_aggX_demand hχ one_pos hρ, inv_one]

/-- Galí (2015), Exercise 2.4(c) (**closed form**, levels version): if `s_π < 1 + s_0`, the
compensation `λ(π) = (s_π − s_0)/(1 + s_0 − s_π)` satisfies `1 + λ > 0` and makes the
household indifferent between inflation `π` and zero inflation. -/
theorem welfareCost_levels (σ : ℝ) {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π)
    (hex : sRate χ (ρ + π) < 1 + sRate χ ρ) :
    -1 < welfareCostLevels χ ρ π ∧
      periodUtility σ χ (1 + welfareCostLevels χ ρ π) (zDemand χ (ρ + π))
        = periodUtility σ χ 1 (zDemand χ ρ) := by
  have hd : 0 < 1 + sRate χ ρ - sRate χ (ρ + π) := by linarith
  have e : 1 + welfareCostLevels χ ρ π = 1 / (1 + sRate χ ρ - sRate χ (ρ + π)) := by
    unfold welfareCostLevels
    field_simp
    ring
  have hl : -1 < welfareCostLevels χ ρ π := by
    have : 0 < 1 + welfareCostLevels χ ρ π := by rw [e]; positivity
    linarith
  refine ⟨hl, (indifference_levels_iff σ hχ hρ hπ hl).2 ?_⟩
  rw [e, one_div, inv_inv]
  ring

/-- Galí (2015), Exercise 2.4(c) (**uniqueness**, levels version): any compensation `λ > −1`
making the household indifferent equals `λ(π)`. -/
theorem welfareCost_levels_unique (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l)
    (h : periodUtility σ χ (1 + l) (zDemand χ (ρ + π)) = periodUtility σ χ 1 (zDemand χ ρ)) :
    l = welfareCostLevels χ ρ π := by
  have h' := (indifference_levels_iff σ hχ hρ hπ hl).1 h
  have hl1 : 0 < 1 + l := by linarith
  have hd : 1 + sRate χ ρ - sRate χ (ρ + π) = (1 + l)⁻¹ := by linarith
  have hd0 : 0 < 1 + sRate χ ρ - sRate χ (ρ + π) := by rw [hd]; positivity
  have e1 : l * (1 + l)⁻¹ = 1 - (1 + l)⁻¹ := by
    field_simp
    ring
  have key : sRate χ (ρ + π) - sRate χ ρ = l * (1 + l)⁻¹ := by rw [e1]; linarith
  unfold welfareCostLevels
  rw [key, hd]
  field_simp

/-- Galí (2015), Exercise 2.4(c) (**no compensation**, levels version): if `s_π ≥ 1 + s_0`, no
increase in consumption with real balances held at their `π` level compensates for inflation
`π` (utility in `C` is bounded by the satiation level `1/s_π` of `X`). -/
theorem welfareCost_levels_none (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l) (hno : 1 + sRate χ ρ ≤ sRate χ (ρ + π)) :
    periodUtility σ χ (1 + l) (zDemand χ (ρ + π)) ≠ periodUtility σ χ 1 (zDemand χ ρ) := by
  intro h
  have h' := (indifference_levels_iff σ hχ hρ hπ hl).1 h
  have : 0 < (1 + l)⁻¹ := inv_pos.2 (by linarith)
  linarith

/-- Galí (2015), Exercise 2.4(c): the welfare cost when consumption and real balances are
scaled together (velocity held at its `π` level): `λ(π) = (s_π − s_0)/(1 + s_0)`. -/
noncomputable def welfareCostRatio (χ ρ π : ℝ) : ℝ :=
  (sRate χ (ρ + π) - sRate χ ρ) / (1 + sRate χ ρ)

/-- Galí (2015), Exercise 2.4(c) (**closed form**, ratio version):
`U((1 + λ), (1 + λ) z_π) = U(1, z_0)` with `λ = welfareCostRatio`, and `1 + λ > 0`. -/
theorem welfareCost_ratio (σ : ℝ) {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π) :
    -1 < welfareCostRatio χ ρ π ∧
      periodUtility σ χ (1 + welfareCostRatio χ ρ π)
        ((1 + welfareCostRatio χ ρ π) * zDemand χ (ρ + π))
        = periodUtility σ χ 1 (zDemand χ ρ) := by
  have hi : 0 < ρ + π := by linarith
  have hs0 := sRate_pos hχ hρ
  have hs := sRate_pos hχ hi
  have e : 1 + welfareCostRatio χ ρ π = (1 + sRate χ (ρ + π)) / (1 + sRate χ ρ) := by
    unfold welfareCostRatio
    field_simp
    ring
  have hl1 : 0 < 1 + welfareCostRatio χ ρ π := by rw [e]; positivity
  refine ⟨by linarith, ?_⟩
  unfold periodUtility
  congr 1
  have hz := zDemand_pos hχ hi
  have hA := aggX_pos hχ.le hl1 (mul_pos hl1 hz)
  have hB := aggX_pos hχ.le one_pos (zDemand_pos hχ hρ)
  rw [← inv_inj, inv_aggX hχ.le hl1 (mul_pos hl1 hz), inv_aggX_demand hχ one_pos hρ,
    show χ / ((1 + welfareCostRatio χ ρ π) * zDemand χ (ρ + π))
      = (1 + welfareCostRatio χ ρ π)⁻¹ * (χ / zDemand χ (ρ + π)) by field_simp,
    chi_div_zDemand hχ hi, e]
  field_simp

/-- Galí (2015), Exercise 2.4(c) (**uniqueness**, ratio version). -/
theorem welfareCost_ratio_unique (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l)
    (h : periodUtility σ χ (1 + l) ((1 + l) * zDemand χ (ρ + π))
      = periodUtility σ χ 1 (zDemand χ ρ)) : l = welfareCostRatio χ ρ π := by
  have hi : 0 < ρ + π := by linarith
  have hl1 : 0 < 1 + l := by linarith
  have hz := zDemand_pos hχ hi
  have hs0 := sRate_pos hχ hρ
  have hA := aggX_pos hχ.le hl1 (mul_pos hl1 hz)
  have hB := aggX_pos hχ.le one_pos (zDemand_pos hχ hρ)
  unfold periodUtility at h
  rw [(Ex2_1.utilC_strictMonoOn σ).injOn.eq_iff hA hB, ← inv_inj,
    inv_aggX hχ.le hl1 (mul_pos hl1 hz), inv_aggX_demand hχ one_pos hρ,
    show χ / ((1 + l) * zDemand χ (ρ + π)) = (1 + l)⁻¹ * (χ / zDemand χ (ρ + π)) by
      field_simp, chi_div_zDemand hχ hi] at h
  unfold welfareCostRatio
  rw [eq_div_iff (by positivity)]
  field_simp at h
  linarith

/-- Galí (2015), Exercise 2.4(c): the (ratio-version) welfare cost is positive iff `π > 0`. -/
theorem welfareCost_ratio_pos_iff {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π) :
    0 < welfareCostRatio χ ρ π ↔ 0 < π := by
  have hs0 := sRate_pos hχ hρ
  have hmono := sRate_strictMonoOn hχ
  unfold welfareCostRatio
  rw [div_pos_iff_of_pos_right (by positivity), sub_pos]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : sRate χ (ρ + π) ≤ sRate χ ρ :=
      hmono.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hρ.le) (by linarith)
    linarith
  · intro h
    exact hmono (Set.mem_Ici.2 hρ.le) (Set.mem_Ici.2 (by linarith)) (by linarith)

/-- Galí (2015), Exercise 2.4(c): when it exists, the (levels-version) welfare cost is
positive iff `π > 0`. -/
theorem welfareCost_levels_pos_iff {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π)
    (hex : sRate χ (ρ + π) < 1 + sRate χ ρ) : 0 < welfareCostLevels χ ρ π ↔ 0 < π := by
  have hmono := sRate_strictMonoOn hχ
  unfold welfareCostLevels
  rw [div_pos_iff_of_pos_right (by linarith), sub_pos]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : sRate χ (ρ + π) ≤ sRate χ ρ :=
      hmono.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hρ.le) (by linarith)
    linarith
  · intro h
    exact hmono (Set.mem_Ici.2 hρ.le) (Set.mem_Ici.2 (by linarith)) (by linarith)

/-! ### d. Interest-rate fluctuations to second order -/

/-- Galí (2015), Exercise 2.4(d): equilibrium utility as a function of the nominal rate,
`W(i) = u(1/(1 + s(i)))` (steady-state endowment `Y = 1`). -/
noncomputable def Wf (σ χ i : ℝ) : ℝ := Ex2_1.utilC σ (1 + sRate χ i)⁻¹

/-- Galí (2015), Exercise 2.4(d): `W` is equilibrium utility `eqWelfare` at `Y = 1`. -/
theorem eqWelfare_one_eq_Wf (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    eqWelfare σ χ 1 i = Wf σ χ i := by
  rw [eqWelfare_eq σ hχ one_pos hi, one_div]
  rfl

/-- Galí (2015), Exercise 2.4(d): `s'(i) = χ e^{−i}/(2 s(i))`. -/
noncomputable def sDeriv (χ i : ℝ) : ℝ := χ * Real.exp (-i) / (2 * sRate χ i)

/-- Galí (2015), Exercise 2.4(d): `s''(i) = −s'(i) − s'(i)²/s(i)`. -/
noncomputable def sDeriv2 (χ i : ℝ) : ℝ := -sDeriv χ i - sDeriv χ i ^ 2 / sRate χ i

/-- Galí (2015), Exercise 2.4(d): `W'(i) = −(1 + s)^{σ−2} s'`. -/
noncomputable def W1 (σ χ i : ℝ) : ℝ := -((1 + sRate χ i) ^ (σ - 2) * sDeriv χ i)

/-- Galí (2015), Exercise 2.4(d):
`W''(i) = (2 − σ)(1 + s)^{σ−3} s'² + (1 + s)^{σ−2}(s' + s'²/s)`. -/
noncomputable def W2 (σ χ i : ℝ) : ℝ :=
  (2 - σ) * (1 + sRate χ i) ^ (σ - 3) * sDeriv χ i ^ 2
    + (1 + sRate χ i) ^ (σ - 2) * (sDeriv χ i + sDeriv χ i ^ 2 / sRate χ i)

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `s` has derivative `s'` at `i > 0`. -/
theorem hasDerivAt_sRate {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (sRate χ) (sDeriv χ i) i := by
  have h1 := one_sub_exp_neg_pos hi
  have hexp : HasDerivAt (fun i => Real.exp (-i)) (-Real.exp (-i)) i := by
    have := (hasDerivAt_neg i).exp
    convert this using 1
    ring
  have hg := (hexp.const_sub 1).const_mul χ
  have hs := (Real.hasDerivAt_sqrt (mul_pos hχ h1).ne').comp i hg
  refine hs.congr_deriv ?_
  unfold sDeriv sRate
  have : 0 < Real.sqrt (χ * (1 - Real.exp (-i))) := Real.sqrt_pos.2 (mul_pos hχ h1)
  field_simp

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `s'` has derivative `s''` at `i > 0`. -/
theorem hasDerivAt_sDeriv {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (sDeriv χ) (sDeriv2 χ i) i := by
  have hs := sRate_pos hχ hi
  have hexp : HasDerivAt (fun i => Real.exp (-i)) (-Real.exp (-i)) i := by
    have := (hasDerivAt_neg i).exp
    convert this using 1
    ring
  have h := (hexp.const_mul χ).div ((hasDerivAt_sRate hχ hi).const_mul 2)
    (by positivity : (2 * sRate χ i) ≠ 0)
  refine h.congr_deriv ?_
  unfold sDeriv2 sDeriv
  field_simp

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `W' = W1` at `i > 0`. -/
theorem hasDerivAt_W (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (Wf σ χ) (W1 σ χ i) i := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hinv := ((hasDerivAt_sRate hχ hi).const_add 1).inv h1.ne'
  have hu := (Ex2_1.hasDerivAt_utilC σ (inv_pos.2 h1)).comp i hinv
  refine hu.congr_deriv ?_
  unfold W1
  rw [Real.inv_rpow h1.le, Real.rpow_neg h1.le, inv_inv, Real.rpow_sub h1, Real.rpow_two]
  field_simp

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `W1' = W2` at `i > 0`. -/
theorem hasDerivAt_W1 (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (W1 σ χ) (W2 σ χ i) i := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hA := (Real.hasDerivAt_rpow_const (p := σ - 2) (Or.inl h1.ne')).comp i
    ((hasDerivAt_sRate hχ hi).const_add 1)
  have h := (hA.mul (hasDerivAt_sDeriv hχ hi)).neg
  refine h.congr_deriv ?_
  unfold W2 sDeriv2
  rw [show σ - 2 - 1 = σ - 3 by ring]
  simp only [Function.comp_apply]
  ring

/-- Galí (2015), Exercise 2.4(d): `W` is three times continuously differentiable on
`(0, ∞)`. -/
theorem contDiffOn_W (σ : ℝ) {χ : ℝ} (hχ : 0 < χ) :
    ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (Wf σ χ) (Set.Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have h1 := one_sub_exp_neg_pos hx'
  have hs := sRate_pos hχ hx'
  have hin : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun i => (1 + sRate χ i)⁻¹) x := by
    have hg : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun i : ℝ => χ * (1 - Real.exp (-i))) := by
      fun_prop
    have hsq : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (sRate χ) x :=
      hg.contDiffAt.sqrt (mul_pos hχ h1).ne'
    exact (contDiffAt_const.add hsq).inv (by linarith)
  have hy : 0 < (1 + sRate χ x)⁻¹ := inv_pos.2 (by linarith)
  have hout : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (Ex2_1.utilC σ) (1 + sRate χ x)⁻¹ := by
    by_cases hσ : σ = 1
    · have hfun : Ex2_1.utilC σ = Real.log := funext fun y => by simp [Ex2_1.utilC, hσ]
      rw [hfun]
      exact Real.contDiffAt_log.2 hy.ne'
    · have hfun : Ex2_1.utilC σ = fun y => (y ^ (1 - σ) - 1) / (1 - σ) :=
        funext fun y => by simp [Ex2_1.utilC, hσ]
      rw [hfun]
      exact ((Real.contDiffAt_rpow_const_of_ne hy.ne').sub contDiffAt_const).div_const _
  exact (hout.comp x hin).contDiffWithinAt

/-- Galí (2015), Exercise 2.4(d): `W'' = W2` at `i > 0`. -/
theorem deriv_deriv_W (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    deriv (deriv (Wf σ χ)) i = W2 σ χ i := by
  have heq : deriv (Wf σ χ) =ᶠ[𝓝 i] W1 σ χ := by
    filter_upwards [Ioi_mem_nhds hi] with x hx
    exact (hasDerivAt_W σ hχ hx).deriv
  rw [heq.deriv_eq, (hasDerivAt_W1 σ hχ hi).deriv]

/-- Galí (2015), Exercise 2.4(d) (**second-order Taylor expansion**): for `ī > 0`,
`W(i) = W(ī) + W1(ī)(i − ī) + ½ W2(ī)(i − ī)² + O((i − ī)³)`. -/
theorem welfare_taylor (σ : ℝ) {χ ibar : ℝ} (hχ : 0 < χ) (hi : 0 < ibar) :
    (fun i => Wf σ χ i - Wf σ χ ibar - W1 σ χ ibar * (i - ibar)
      - 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2) =O[𝓝 ibar] fun i => (i - ibar) ^ 3 := by
  have ht := taylor_isLittleO (convex_Ioi 0) hi (contDiffOn_W σ hχ)
  rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds hi)] at ht
  set c3 := iteratedDerivWithin 3 (Wf σ χ) (Set.Ioi 0) ibar with hc3
  have d1 : iteratedDerivWithin 1 (Wf σ χ) (Set.Ioi 0) ibar = W1 σ χ ibar := by
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hi, iteratedDeriv_one,
      (hasDerivAt_W σ hχ hi).deriv]
  have d2 : iteratedDerivWithin 2 (Wf σ χ) (Set.Ioi 0) ibar = W2 σ χ ibar := by
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hi, iteratedDeriv_succ, iteratedDeriv_one,
      deriv_deriv_W σ hχ hi]
  have hT : ∀ i, taylorWithinEval (Wf σ χ) 3 (Set.Ioi 0) ibar i
      = Wf σ χ ibar + W1 σ χ ibar * (i - ibar) + 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2
        + c3 / 6 * (i - ibar) ^ 3 := by
    intro i
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, d1, d2,
      ← hc3, Nat.factorial, smul_eq_mul]
    push_cast
    ring
  have hfun : (fun i => Wf σ χ i - Wf σ χ ibar - W1 σ χ ibar * (i - ibar)
      - 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2)
      = (fun i => Wf σ χ i - taylorWithinEval (Wf σ χ) 3 (Set.Ioi 0) ibar i)
        + fun i => c3 / 6 * (i - ibar) ^ 3 := by
    funext i
    simp only [Pi.add_apply, hT]
    ring
  rw [hfun]
  exact ht.isBigO.add (Asymptotics.isBigO_const_mul_self _ _ _)

/-- Galí (2015), Exercise 2.4(d) (**second-order welfare effect of interest-rate
fluctuations**): let `i_t = ī + s ε_t` with `ī > 0`, `|ε_t| ≤ M`, `E_0 ε_t = 0`, and
`0 ≤ β < 1`. Relative to the constant policy `i_t = ī`, expected discounted utility changes by
`½ W2(ī) s² ∑ βᵗ E_0 ε_t²` up to an `O(|s|³)` remainder:
there are `K` and `r > 0` with
`|∑ βᵗ E_0 W(i_t) − ∑ βᵗ W(ī) − ½ W2(ī) s² ∑ βᵗ E_0 ε_t²| ≤ K |s|³` for `|s| < r`. -/
theorem welfare_fluctuations (σ : ℝ) {χ ibar β M : ℝ}
    (hχ : 0 < χ) (hi : 0 < ibar) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ε : ℕ → Ω → ℝ}
    (hε : ∀ t ω, |ε t ω| ≤ M) (hE : ∀ t, 𝔼.E 0 (ε t) = 0) (ω : Ω) :
    ∃ K r : ℝ, 0 < r ∧ ∀ s : ℝ, |s| < r →
      |∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
        - ∑' t : ℕ, β ^ t * Wf σ χ ibar
        - 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω|
        ≤ K * |s| ^ 3 := by
  obtain ⟨c, hc⟩ := (welfare_taylor σ hχ hi).bound
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.1 hc
  have hM : 0 ≤ M := by
    have := hε 0 ω
    exact (abs_nonneg _).trans this
  have hM1 : 0 < M + 1 := by linarith
  set R : ℝ → ℝ := fun i => Wf σ χ i - Wf σ χ ibar - W1 σ χ ibar * (i - ibar)
    - 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2 with hR
  refine ⟨|c| * M ^ 3 / (1 - β), η / (M + 1), div_pos hη hM1, fun s hs => ?_⟩
  have hsM : ∀ e : ℝ, |e| ≤ M → |s * e| < η := by
    intro e he
    rw [abs_mul]
    have : |s| * |e| ≤ |s| * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
    have := (lt_div_iff₀ hM1).1 hs
    linarith
  have hRb : ∀ t ω', |R (ibar + s * ε t ω')| ≤ |c| * M ^ 3 * |s| ^ 3 := by
    intro t ω'
    have hd : dist (ibar + s * ε t ω') ibar < η := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact hsM _ (hε t ω')
    have h0 := hηb hd
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h0
    have h : |R (ibar + s * ε t ω')| ≤ c * |(ibar + s * ε t ω' - ibar) ^ 3| := h0
    rw [add_sub_cancel_left, abs_pow, abs_mul] at h
    calc |R (ibar + s * ε t ω')| ≤ c * (|s| * |ε t ω'|) ^ 3 := h
      _ ≤ |c| * (|s| * |ε t ω'|) ^ 3 := by gcongr; exact le_abs_self c
      _ ≤ |c| * (|s| * M) ^ 3 := by gcongr; exact hε t ω'
      _ = |c| * M ^ 3 * |s| ^ 3 := by ring
  -- one period
  have hper : ∀ t, 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
      = Wf σ χ ibar + 1 / 2 * W2 σ χ ibar * s ^ 2 * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
        + 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by
    intro t
    have hfun : (fun ω' => Wf σ χ (ibar + s * ε t ω'))
        = (fun _ => Wf σ χ ibar) + (W1 σ χ ibar * s) • ε t
          + (1 / 2 * W2 σ χ ibar * s ^ 2) • (fun ω' => ε t ω' ^ 2)
          + fun ω' => R (ibar + s * ε t ω') := by
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hR]
      ring
    rw [hfun, map_add, map_add, map_add, map_smul, map_smul, 𝔼.const, hE t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
  have hgeo := summable_geometric_of_lt_one hβ0 hβ1
  have hsum2 : Summable fun t : ℕ => β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω := by
    refine Summable.of_norm_bounded (hgeo.mul_right (M ^ 2)) (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) 0 ω) (pow_nonneg hβ0 t)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hε t ω') 2
  have hsumR : Summable fun t : ℕ => β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by
    refine Summable.of_norm_bounded (hgeo.mul_right (|c| * M ^ 3 * |s| ^ 3)) (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb t) 0 ω) (pow_nonneg hβ0 t)
  have hsum0 : Summable fun t : ℕ => β ^ t * Wf σ χ ibar := hgeo.mul_right _
  have htot : ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
      = ∑' t : ℕ, β ^ t * Wf σ χ ibar
        + 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
        + ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by
    calc ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
        = ∑' t : ℕ, ((β ^ t * Wf σ χ ibar
            + 1 / 2 * W2 σ χ ibar * s ^ 2 * (β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω))
            + β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω) :=
          tsum_congr fun t => by rw [hper t]; ring
      _ = _ := by
          rw [(hsum0.add (hsum2.mul_left _)).tsum_add hsumR,
            hsum0.tsum_add (hsum2.mul_left _), tsum_mul_left]
  rw [htot]
  have hbound : |∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω|
      ≤ |c| * M ^ 3 / (1 - β) * |s| ^ 3 := by
    have hs' : HasSum (fun t : ℕ => β ^ t * (|c| * M ^ 3 * |s| ^ 3))
        ((1 - β)⁻¹ * (|c| * M ^ 3 * |s| ^ 3)) :=
      (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right _
    have := tsum_of_norm_bounded
      (f := fun t : ℕ => β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω) hs' (fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb t) 0 ω) (pow_nonneg hβ0 t))
    rw [Real.norm_eq_abs] at this
    calc _ ≤ (1 - β)⁻¹ * (|c| * M ^ 3 * |s| ^ 3) := this
      _ = |c| * M ^ 3 / (1 - β) * |s| ^ 3 := by field_simp
  have e : ∑' t : ℕ, β ^ t * Wf σ χ ibar
      + 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
      + ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω
      - ∑' t : ℕ, β ^ t * Wf σ χ ibar
      - 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
      = ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by ring
  rw [e]
  exact hbound

/-- Galí (2015), Exercise 2.4(d): the sign of `W''`: `W2(i) > 0` iff
`1 + s'/s + (2 − σ) s'/(1 + s) > 0` (all evaluated at `i > 0`). -/
theorem W2_pos_iff (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    0 < W2 σ χ i ↔
      0 < 1 + sDeriv χ i / sRate χ i + (2 - σ) * sDeriv χ i / (1 + sRate χ i) := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hd : 0 < sDeriv χ i := by unfold sDeriv; positivity
  have e : W2 σ χ i = sDeriv χ i * (1 + sRate χ i) ^ (σ - 2)
      * (1 + sDeriv χ i / sRate χ i + (2 - σ) * sDeriv χ i / (1 + sRate χ i)) := by
    unfold W2
    rw [show σ - 3 = (σ - 2) - 1 by ring, Real.rpow_sub_one h1.ne']
    field_simp
    ring
  have hp : 0 < sDeriv χ i * (1 + sRate χ i) ^ (σ - 2) :=
    mul_pos hd (Real.rpow_pos_of_pos h1 _)
  rw [e]
  exact ⟨fun h => pos_of_mul_pos_right h hp.le, fun h => mul_pos hp h⟩

/-- Galí (2015), Exercise 2.4(d) (**finding**): for `σ ≤ 2` (including log utility) `W'' > 0`
at every `i > 0`: utility is convex in the nominal rate. -/
theorem W2_pos_of_le_two {σ : ℝ} (hσ : σ ≤ 2) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    0 < W2 σ χ i := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hd : 0 < sDeriv χ i := by unfold sDeriv; positivity
  unfold W2
  have : 0 ≤ (2 - σ) * (1 + sRate χ i) ^ (σ - 3) * sDeriv χ i ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_pos_of_pos h1 _).le) (sq_nonneg _)
  have : 0 < (1 + sRate χ i) ^ (σ - 2) * (sDeriv χ i + sDeriv χ i ^ 2 / sRate χ i) :=
    mul_pos (Real.rpow_pos_of_pos h1 _) (by positivity)
  linarith

/-- Galí (2015), Exercise 2.4(d) (**finding: fluctuations raise welfare for `σ ≤ 2`**): if
`σ ≤ 2` and the fluctuations have positive discounted variance
`V = ∑ βᵗ E_0 ε_t² > 0`, then for all small `s ≠ 0` expected discounted utility under
`i_t = ī + s ε_t` strictly exceeds that of the constant policy `i_t = ī`. -/
theorem fluctuations_raise_welfare {σ : ℝ} (hσ : σ ≤ 2)
    {χ ibar β M : ℝ} (hχ : 0 < χ) (hi : 0 < ibar) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ε : ℕ → Ω → ℝ} (hε : ∀ t ω, |ε t ω| ≤ M) (hE : ∀ t, 𝔼.E 0 (ε t) = 0) (ω : Ω)
    (hV : 0 < ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, s ≠ 0 → |s| < r →
      ∑' t : ℕ, β ^ t * Wf σ χ ibar
        < ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω := by
  obtain ⟨K, r, hr, hK⟩ := welfare_fluctuations 𝔼 σ hχ hi hβ0 hβ1 hε hE ω
  set V := ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω with hVdef
  have hW := W2_pos_of_le_two hσ hχ hi
  set a := 1 / 2 * W2 σ χ ibar * V with ha
  have ha0 : 0 < a := by positivity
  refine ⟨min r (a / (|K| + 1)), lt_min hr (by positivity), fun s hs0 hs => ?_⟩
  have hsr : |s| < r := hs.trans_le (min_le_left _ _)
  have hsa : |s| < a / (|K| + 1) := hs.trans_le (min_le_right _ _)
  have h := hK s hsr
  have hspos : 0 < |s| := abs_pos.2 hs0
  have hK1 : 0 < |K| + 1 := by positivity
  have hsq : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  have hcube : K * |s| ^ 3 < a * s ^ 2 := by
    rw [hsq]
    have h1 : |s| * (|K| + 1) < a := (lt_div_iff₀ hK1).1 hsa
    have h2 : K * |s| ^ 3 ≤ |K| * |s| ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have h3 : |K| * |s| ^ 3 < a * |s| ^ 2 := by
      have : |K| * |s| < a := by nlinarith
      have hs2 : 0 < |s| ^ 2 := by positivity
      calc |K| * |s| ^ 3 = (|K| * |s|) * |s| ^ 2 := by ring
        _ < a * |s| ^ 2 := mul_lt_mul_of_pos_right this hs2
    linarith
  have e : 1 / 2 * W2 σ χ ibar * s ^ 2 * V = a * s ^ 2 := by rw [ha]; ring
  rw [e] at h
  have := (abs_le.1 h).1
  linarith

end Gali.ClassicalMonetaryModel.Ex2_4

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.5: an exact equilibrium of the classical monetary model

Galí (2015), Chapter 2, Exercise 2.5, pp. 48–49. Money in the utility function with period
utility `log C + log (M/P) − N^{1+φ}/(1+φ)` (eq. (52)), a linear technology `Y = A N` with
`A_{t+1}/A_t = (1 + γ_a) e^{ε^a_{t+1}}`, and an exogenous money supply
`M_{t+1}/M_t = (1 + γ_m) e^{ε^m_{t+1}}` (eq. (53)), with i.i.d. Gaussian innovations.

## (a) Optimality conditions

* Marginal utilities (`hasDerivAt_utility_C`, `_m`, `_N`): `U_c = 1/C`, `U_m = 1/(M/P)`,
  `U_n = −N^φ`.
* Labour supply `W/P = C N^φ` (`labour_optimum_iff`, necessity and sufficiency).
* Money demand `C = (1 − Q)(M/P)`, i.e. velocity `P C/M = 1 − Q` (`money_optimum_iff`,
  necessity and sufficiency along the budget line (32) with financial wealth held fixed).
* Firm: `W = P A` (`firm_optimum_iff`).
* Euler equation (5) with `U_c = 1/C`: `Q_t = β E_t[(C_t P_t)/(C_{t+1} P_{t+1})]`, stated with a
  genuine conditional expectation `μ[· | ℱ t]` (`IsEquilibrium.euler`).

## (b) The exact equilibrium

The shocks live on a genuine probability space with a filtration `ℱ`: the innovations are
adapted, `N(0, σ²)` at each date, and `ε_{t+1}` is independent of `ℱ_t`
(`GaussianInnovations`), hence i.i.d.

* `employment_eq_one`: in every equilibrium `N_t = 1`, so `Y_t = C_t = A_t`
  (`output_eq_technology`), state by state, with no guess needed.
* `velocity_eq`: velocity is `P_t Y_t / M_t = 1 − Q_t`.
* `condExp_money_ratio`: `E_t[M_t/M_{t+1}] = e^{σ_m²/2}/(1 + γ_m)` (Gaussian MGF,
  `mgf_gaussianReal`, plus independence, `condExp_indep_eq`).
* `velocity_of_constant`: a constant velocity must be `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`;
  `candidate_isEquilibrium`: conversely, when `β e^{σ_m²/2} < 1 + γ_m` the constant-velocity
  allocation is an exact equilibrium.
* `shockMeasure`, `shockFiltration`, `techInnovations`, `moneyInnovations`: a concrete
  probability space (`Measure.infinitePi` of `N(0, σ_a²) ⊗ N(0, σ_m²)`) with the natural
  filtration carrying i.i.d. Gaussian innovations; `exists_exact_equilibrium`: the exact
  equilibrium genuinely exists on it.
* `inflation_eq`: gross inflation `P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`;
  `nominalRate_eq`: the nominal rate is the constant `i = −log Q`.

## (c) Welfare and optimal policy

* `hasSum_expected_welfare`: expected lifetime utility `∑ βᵗ E[U_t]` equals
  `(2 log A₀ − log V − 1/(1+φ))/(1 − β) + 2 β log(1 + γ_a)/(1 − β)²`. Monetary policy enters
  only through `−log V/(1 − β)`, `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`.
* `integral_tsum_welfare`: welfare is the expectation of lifetime utility,
  `E[∑ₜ βᵗ U_t] = ∑ₜ βᵗ E[U_t]` (dominated convergence with a geometric bound on `E|βᵗ U_t|`).
* `welfare_strictAnti_gamma`, `welfare_strictMono_var`: welfare falls with money growth `γ_m`
  and rises with the variance `σ_m²` (a higher variance raises `E_t[M_t/M_{t+1}]`).
* `welfare_rate_strictAnti`, `tendsto_welfare_rate`: as a function of the constant nominal rate
  `i = −log Q ≥ 0` welfare is strictly decreasing on `i > 0` and unbounded as `i → 0⁺`.
* `not_optimal_of_equilibrium`: every policy with an equilibrium (`i > 0`) is strictly
  improved upon, so an optimal policy must have `i = 0`, i.e. `Q = 1` (the Friedman rule,
  `friedman_iff`).

**Imprecision (reported).** With `log (M/P)` there is no satiation in real balances: at
`Q = 1` velocity would be `V = 0`, the constant-velocity equilibrium does not exist
(`not_equilibrium_at_friedman`) and welfare is unbounded. The Friedman rule is the
supremum, approached as `i → 0⁺`, not an attained maximum.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-! ### (a) Optimality conditions -/

/-- Galí (2015), Ex. 2.5, eq. (52), p. 49: period utility `log C + log m − N^{1+φ}/(1+φ)`,
with real balances `m = M/P`. -/
noncomputable def utility (φ C m N : ℝ) : ℝ :=
  Real.log C + Real.log m - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), Ex. 2.5(a), p. 49: the marginal utility of consumption is `U_c = 1/C`. -/
theorem hasDerivAt_utility_C (φ m N : ℝ) {C : ℝ} (hC : C ≠ 0) :
    HasDerivAt (fun C' => utility φ C' m N) C⁻¹ C := by
  have := ((Real.hasDerivAt_log hC).add_const (Real.log m)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 2.5(a), p. 49: the marginal utility of real balances is `U_m = 1/m`. -/
theorem hasDerivAt_utility_m (φ C N : ℝ) {m : ℝ} (hm : m ≠ 0) :
    HasDerivAt (fun m' => utility φ C m' N) m⁻¹ m := by
  have := ((Real.hasDerivAt_log hm).const_add (Real.log C)).sub_const (N ^ (1 + φ) / (1 + φ))
  simpa [utility] using this

/-- Galí (2015), Ex. 2.5(a), p. 49: the marginal disutility of labour is `−U_n = N^φ`. -/
theorem hasDerivAt_utility_N {φ : ℝ} (hφ : 0 ≤ φ) (C m N : ℝ) :
    HasDerivAt (fun N' => utility φ C m N') (-N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have hd : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have := hd.const_sub (Real.log C + Real.log m)
  simpa [utility] using this

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (restated from the Chapter 3 project; used for the concavity of (52)). -/
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

/-- Galí (2015), p. 18: the disutility of labour is convex for `φ ≥ 0`, in tangent-line form
`x^{1+φ}/(1+φ) + x^φ (y − x) ≤ y^{1+φ}/(1+φ)` (restated from the Chapter 3 project). -/
theorem disutil_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    x ^ (1 + φ) / (1 + φ) + x ^ φ * (y - x) ≤ y ^ (1 + φ) / (1 + φ) := by
  have hd : ∀ z : ℝ, HasDerivAt (fun N : ℝ => N ^ (1 + φ) / (1 + φ)) (z ^ φ) z := by
    intro z
    refine ((Real.hasDerivAt_rpow_const (x := z) (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  have h := le_tangent (f := fun N => -(N ^ (1 + φ) / (1 + φ))) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hd z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), p. 21: the marginal disutility of labour, `d/dN [N^{1+φ}/(1+φ)] = N^φ`. -/
theorem hasDerivAt_disutil {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), Ex. 2.5(a) (concavity of (52)): the tangent-line inequality for `log`,
`log y ≤ log x + (y − x)/x` for `x, y > 0`. -/
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have : y / x - 1 = (y - x) / x := by field_simp
  linarith

/-- Galí (2015), Ex. 2.5(a), with eq. (4), p. 19 (**necessity**): if hours `N` are a local
optimum along the budget line `P C = W N + X` (real balances `m` fixed) with `C > 0`, then
`W/P = C N^φ`. -/
theorem labour_foc_necessary {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hC : 0 < C)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => utility φ ((W * N' + X) / P) m N') N) :
    W / P = C * N ^ φ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hg : HasDerivAt (fun N' => utility φ ((W * N' + X) / P) m N') (C⁻¹ * (W / P) - N ^ φ)
      N := by
    have h1 : HasDerivAt (fun N' => Real.log ((W * N' + X) / P)) (C⁻¹ * (W / P)) N := by
      have := (Real.hasDerivAt_log (by rw [hCeq]; exact hC.ne')).comp N hin
      rw [hCeq] at this
      exact this
    have h2 : HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N :=
      hasDerivAt_disutil hφ N
    exact HasDerivAt.sub (h1.add_const (Real.log m)) h2
  have h0 := hloc.hasDerivAt_eq_zero hg
  field_simp at h0
  field_simp
  linarith

/-- Galí (2015), Ex. 2.5(a), p. 19 (**sufficiency**, by concavity): if `W/P = C N^φ` at a
point with `C, N > 0` on the budget line `P C = W N + X`, it maximises (52) among all feasible
`N' ≥ 0` with `C' = (W N' + X)/P > 0`. -/
theorem labour_foc_sufficient {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X) (hfoc : W / P = C * N ^ φ) {N' : ℝ}
    (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    utility φ ((W * N' + X) / P) m N' ≤ utility φ C m N := by
  have hu := log_le_tangent hC hC'
  have hv := disutil_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have h3 : ((W * N' + X) / P - C) / C = N ^ φ * (N' - N) := by
    rw [hdiff, hfoc]; field_simp
  unfold utility
  linarith

/-- Galí (2015), Ex. 2.5(a), eq. (4), p. 19: a point with `C, N > 0` on the budget line solves
the labour-supply problem iff `W/P = C N^φ`. -/
theorem labour_optimum_iff {φ P W X m C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      utility φ ((W * N' + X) / P) m N' ≤ utility φ C m N) ↔ W / P = C * N ^ φ := by
  constructor
  · intro h
    refine labour_foc_necessary (m := m) hφ hP hC hbud ?_
    have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
    have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
    have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
      (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
    filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
    rw [hCeq]
    exact h N' h2'.le h1'
  · intro h N' hN' hC'
    exact labour_foc_sufficient hφ hP hN hC hbud h hN' hC'

/-- Galí (2015), Ex. 2.5(a), with eq. (33), p. 32 (**necessity**): holding total financial
wealth fixed, the budget (32) reads `P C + (1 − Q) P m = X`. If real balances `m > 0` are a
local optimum along it with `C > 0`, then `C = (1 − Q) m`: velocity `P C/M` equals `1 − Q`. -/
theorem money_foc_necessary {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X)
    (hloc : IsLocalMax (fun m' => utility φ ((X - (1 - Q) * P * m') / P) m' N) m) :
    C = (1 - Q) * m := by
  have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
  have hin : HasDerivAt (fun m' : ℝ => (X - (1 - Q) * P * m') / P) (-(1 - Q)) m := by
    have := (((hasDerivAt_id' m).const_mul ((1 - Q) * P)).const_sub X).div_const P
    convert this using 1
    field_simp
  have hg : HasDerivAt (fun m' => utility φ ((X - (1 - Q) * P * m') / P) m' N)
      (C⁻¹ * (-(1 - Q)) + m⁻¹) m := by
    have h1 : HasDerivAt (fun m' => Real.log ((X - (1 - Q) * P * m') / P)) (C⁻¹ * (-(1 - Q)))
        m := by
      have := (Real.hasDerivAt_log (by rw [hCeq]; exact hC.ne')).comp m hin
      rw [hCeq] at this
      exact this
    have := (h1.add (Real.hasDerivAt_log hm.ne')).sub_const (N ^ (1 + φ) / (1 + φ))
    simpa [utility] using this
  have h0 := hloc.hasDerivAt_eq_zero hg
  field_simp at h0
  linarith

/-- Galí (2015), Ex. 2.5(a), eq. (33), p. 32 (**sufficiency**, by concavity of `log`): if
`C = (1 − Q) m` at a point with `C, m > 0` on the budget line `P C + (1 − Q) P m = X`, it
maximises (52) among all `m' > 0` with `C' > 0`. -/
theorem money_foc_sufficient {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X) (hfoc : C = (1 - Q) * m) {m' : ℝ} (hm' : 0 < m')
    (hC' : 0 < (X - (1 - Q) * P * m') / P) :
    utility φ ((X - (1 - Q) * P * m') / P) m' N ≤ utility φ C m N := by
  have h1 := log_le_tangent hC hC'
  have h2 := log_le_tangent hm hm'
  have hdiff : (X - (1 - Q) * P * m') / P - C = -(1 - Q) * (m' - m) := by
    rw [← hbud]; field_simp; ring
  have hsum : ((X - (1 - Q) * P * m') / P - C) / C + (m' - m) / m = 0 := by
    rw [hdiff, hfoc]
    have hm0 : m ≠ 0 := hm.ne'
    by_cases hQ : 1 - Q = 0
    · rw [hQ] at hfoc; linarith
    · field_simp; ring
  unfold utility
  linarith

/-- Galí (2015), Ex. 2.5(a), eq. (33), p. 32: on the budget line, `(C, m)` with `C, m > 0`
solves the portfolio problem iff `C = (1 − Q) m`. -/
theorem money_optimum_iff {φ P Q X m C N : ℝ} (hP : 0 < P) (hC : 0 < C) (hm : 0 < m)
    (hbud : P * C + (1 - Q) * P * m = X) :
    (∀ m', 0 < m' → 0 < (X - (1 - Q) * P * m') / P →
      utility φ ((X - (1 - Q) * P * m') / P) m' N ≤ utility φ C m N) ↔ C = (1 - Q) * m := by
  constructor
  · intro h
    refine money_foc_necessary (φ := φ) (N := N) hP hC hm hbud ?_
    have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
    have hcont : Continuous fun m' : ℝ => (X - (1 - Q) * P * m') / P := by fun_prop
    have h1 : ∀ᶠ m' in 𝓝 m, 0 < (X - (1 - Q) * P * m') / P :=
      (hcont.tendsto m).eventually_const_lt (by rw [hCeq]; exact hC)
    filter_upwards [h1, eventually_gt_nhds hm] with m' h1' h2'
    rw [hCeq]
    exact h m' h2' h1'
  · intro h m' hm' hC'
    exact money_foc_sufficient hP hC hm hbud h hm' hC'

/-- Galí (2015), Ex. 2.5(a), p. 49: the competitive firm with `Y = A N` maximises
`P A N − W N` over `N ≥ 0` at some `N > 0` iff `W = P A`. -/
theorem firm_optimum_iff {P A W N : ℝ} (hN : 0 < N) :
    (∀ N', 0 ≤ N' → P * A * N' - W * N' ≤ P * A * N - W * N) ↔ W = P * A := by
  constructor
  · intro h
    have h1 := h (2 * N) (by linarith)
    have h2 := h 0 le_rfl
    have h3 : (P * A - W) * N = 0 := by nlinarith
    have := (mul_eq_zero.1 h3).resolve_right hN.ne'
    linarith
  · intro h N' _
    rw [h]; ring_nf; rfl

/-! ### The stochastic environment -/


/-! ### (b) The stochastic environment and the exact equilibrium -/

variable {Ω : Type*}

/-- Galí (2015), Ex. 2.5, p. 49, and eq. (53): the level `X_t = X₀ (1 + γ)ᵗ e^{ε_1 + ⋯ + ε_t}`
of technology (`X = A`) or of the money supply (`X = M`). -/
noncomputable def level (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  X₀ * (1 + γ) ^ t * Real.exp (∑ s ∈ Finset.range t, ε (s + 1) ω)

/-- Galí (2015), Ex. 2.5, p. 49, and eq. (53): `X_{t+1}/X_t = (1 + γ) e^{ε_{t+1}}`. -/
theorem level_succ (X₀ γ : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    level X₀ γ ε (t + 1) ω = level X₀ γ ε t ω * ((1 + γ) * Real.exp (ε (t + 1) ω)) := by
  simp only [level, Finset.sum_range_succ, Real.exp_add, pow_succ]
  ring

/-- Galí (2015), Ex. 2.5, p. 49: levels are positive when `X₀ > 0` and `1 + γ > 0`. -/
theorem level_pos {X₀ γ : ℝ} (hX : 0 < X₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : 0 < level X₀ γ ε t ω := by
  unfold level
  positivity

variable [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)

/-- Galí (2015), Ex. 2.5, p. 49: i.i.d. Gaussian innovations `ε_t ~ N(0, σ²)` on a probability
space with filtration `ℱ`: `ε_t` is `ℱ_t`-measurable, has law `N(0, σ²)`, and `ε_{t+1}` is
independent of `ℱ_t` (so the sequence is independent and identically distributed). -/
structure GaussianInnovations where
  /-- The innovation at each date. -/
  ε : ℕ → Ω → ℝ
  /-- The variance `σ²`. -/
  var : ℝ≥0
  /-- `ε_t` is known at date `t`. -/
  adapted : ∀ t, Measurable[ℱ t] (ε t)
  /-- `ε_t ~ N(0, σ²)`. -/
  hasLaw : ∀ t, HasLaw (ε t) (gaussianReal 0 var) μ
  /-- `ε_{t+1}` is independent of the date-`t` information. -/
  indep : ∀ t, Indep (MeasurableSpace.comap (ε (t + 1)) inferInstance) (ℱ t) μ

/-- Galí (2015), eq. (5), p. 20, with `U_c = 1/C` (Ex. 2.5(a)): the right side
`β E_t[(C_t P_t)/(C_{t+1} P_{t+1})]` of the Euler equation, with a genuine conditional
expectation given `ℱ_t`. -/
noncomputable def eulerRHS (β : ℝ) (C P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * μ[fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω') | ℱ t] ω

variable (β φ : ℝ) (A M C N Y P W Q : ℕ → Ω → ℝ)

/-- Galí (2015), Ex. 2.5(a)–(b), pp. 48–49: an equilibrium. The household conditions are
labour supply (4) `W/P = C N^φ`, money demand (33) `C = (1 − Q)(M/P)` and the Euler equation
(5); the firm sets `W = P A`; `Y = A N` and `C = Y`. -/
structure IsEquilibrium where
  /-- Consumption is positive. -/
  pos_C : ∀ t ω, 0 < C t ω
  /-- Hours are positive. -/
  pos_N : ∀ t ω, 0 < N t ω
  /-- The price level is positive. -/
  pos_P : ∀ t ω, 0 < P t ω
  /-- Labour supply, eq. (4): `W/P = C N^φ`. -/
  labour : ∀ t ω, W t ω / P t ω = C t ω * N t ω ^ φ
  /-- Money demand, eq. (33): `C = (1 − Q)(M/P)`. -/
  money : ∀ t ω, C t ω = (1 - Q t ω) * (M t ω / P t ω)
  /-- The Euler equation (5). -/
  euler : ∀ t, Q t =ᵐ[μ] eulerRHS μ ℱ β C P t
  /-- Labour demand of the competitive firm: `W = P A`. -/
  firm : ∀ t ω, W t ω = P t ω * A t ω
  /-- Technology: `Y = A N`. -/
  technology : ∀ t ω, Y t ω = A t ω * N t ω
  /-- Goods-market clearing: `C = Y`. -/
  clearing : ∀ t ω, C t ω = Y t ω

variable {μ ℱ β φ A M C N Y P W Q}

/-- Galí (2015), Ex. 2.5(b), p. 49: in every equilibrium employment is `N_t = 1`, state by
state (no guess is needed: with log utility the income and substitution effects cancel). -/
theorem employment_eq_one (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hφ : 0 ≤ φ)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) : N t ω = 1 := by
  have hN := h.pos_N t ω
  have hP := h.pos_P t ω
  have hl := h.labour t ω
  rw [h.firm t ω, mul_div_cancel_left₀ _ hP.ne', h.clearing t ω, h.technology t ω] at hl
  have h1 : A t ω * 1 = A t ω * N t ω ^ (1 + φ) := by
    rw [Real.rpow_add hN, Real.rpow_one]
    linarith
  have h2 : N t ω ^ (1 + φ) = 1 := (mul_left_cancel₀ (hA t ω).ne' h1).symm
  have hne : (1 + φ) ≠ 0 := by linarith
  rw [← Real.rpow_rpow_inv hN.le hne, h2, Real.one_rpow]

/-- Galí (2015), Ex. 2.5(b), p. 49: in every equilibrium `Y_t = A_t` and `C_t = A_t`. -/
theorem output_eq_technology (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hφ : 0 ≤ φ)
    (hA : ∀ t ω, 0 < A t ω) (t : ℕ) (ω : Ω) : Y t ω = A t ω ∧ C t ω = A t ω := by
  have hY : Y t ω = A t ω := by rw [h.technology t ω, employment_eq_one h hφ hA t ω, mul_one]
  exact ⟨hY, (h.clearing t ω).trans hY⟩

/-- Galí (2015), Ex. 2.5(b), p. 49: velocity is `P_t Y_t / M_t = 1 − Q_t` in every
equilibrium. -/
theorem velocity_eq (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (t : ℕ) (ω : Ω) : P t ω * Y t ω / M t ω = 1 - Q t ω := by
  have hP := (h.pos_P t ω).ne'
  have hMt := (hM t ω).ne'
  rw [← h.clearing t ω, h.money t ω]
  field_simp

/-- Galí (2015), Ex. 2.5(b), p. 49, with the Gaussian MGF: for the money supply (53),
`E_t[M_t/M_{t+1}] = e^{σ_m²/2}/(1 + γ_m)`, since `M_t/M_{t+1} = e^{−ε_{t+1}}/(1 + γ_m)` with
`ε_{t+1} ~ N(0, σ_m²)` independent of `ℱ_t`. -/
theorem condExp_money_ratio [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ : ℝ} (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (t : ℕ) :
    μ[fun ω => level M₀ γ G.ε t ω / level M₀ γ G.ε (t + 1) ω | ℱ t]
      =ᵐ[μ] fun _ => Real.exp (G.var / 2) / (1 + γ) := by
  have hfun : (fun ω => level M₀ γ G.ε t ω / level M₀ γ G.ε (t + 1) ω)
      = fun ω => (1 + γ)⁻¹ * Real.exp (-G.ε (t + 1) ω) := by
    funext ω
    have h1 : level M₀ γ G.ε t ω ≠ 0 :=
      mul_ne_zero (mul_ne_zero hM (pow_ne_zero _ hγ.ne')) (Real.exp_pos _).ne'
    rw [level_succ, Real.exp_neg]
    field_simp
  rw [hfun]
  have hmeas : Measurable (G.ε (t + 1)) := (G.adapted (t + 1)).mono (ℱ.le (t + 1)) le_rfl
  have hg : Measurable fun x : ℝ => (1 + γ)⁻¹ * Real.exp (-x) := by fun_prop
  have hsm : StronglyMeasurable[MeasurableSpace.comap (G.ε (t + 1)) inferInstance]
      (fun ω => (1 + γ)⁻¹ * Real.exp (-G.ε (t + 1) ω)) :=
    (hg.comp (comap_measurable (G.ε (t + 1)))).stronglyMeasurable
  refine (condExp_indep_eq hmeas.comap_le (ℱ.le t) hsm (G.indep t)).trans ?_
  refine Filter.Eventually.of_forall fun _ => ?_
  have hint : ∫ ω, Real.exp (-G.ε (t + 1) ω) ∂μ = Real.exp (G.var / 2) := by
    have h := mgf_gaussianReal (G.hasLaw (t + 1)) (-1)
    simp only [mgf, neg_one_mul, zero_mul, zero_add, neg_one_sq, mul_one] at h
    exact h
  simp only
  rw [integral_const_mul, hint]
  ring

/-- Galí (2015), Ex. 2.5(b): the steady value `Q* = β e^{σ_m²/2}/(1 + γ_m)` of the bond price. -/
noncomputable def Qstar (β γ v : ℝ) : ℝ := β * Real.exp (v / 2) / (1 + γ)

/-- Galí (2015), Ex. 2.5(b): the constant velocity `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
noncomputable def velocity (β γ v : ℝ) : ℝ := 1 - Qstar β γ v

/-- Galí (2015), Ex. 2.5(b), p. 49: with constant velocity, `C_t P_t = V M_t`, the Euler
equation's right side is the constant `β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem eulerRHS_of_const_velocity [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : M₀ ≠ 0) (hγ : 0 < 1 + γ) (hV : V ≠ 0) {C P : ℕ → Ω → ℝ}
    (hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ G.ε t ω) (t : ℕ) :
    eulerRHS μ ℱ β C P t =ᵐ[μ] fun _ => Qstar β γ G.var := by
  have hfun : (fun ω' => C t ω' * P t ω' / (C (t + 1) ω' * P (t + 1) ω'))
      = fun ω' => level M₀ γ G.ε t ω' / level M₀ γ G.ε (t + 1) ω' := by
    funext ω'
    rw [hCP, hCP, mul_div_mul_left _ _ hV]
  filter_upwards [condExp_money_ratio G hM hγ t] with ω hω
  simp only [eulerRHS]
  rw [hfun, hω, Qstar]
  ring

/-- Galí (2015), Ex. 2.5(b), p. 49 (the hint): if velocity is constant, `P_t Y_t/M_t = V`,
then necessarily `V = 1 − β e^{σ_m²/2}/(1 + γ_m)`. -/
theorem velocity_of_constant [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ)
    (h : IsEquilibrium μ ℱ β φ A (level M₀ γ G.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γ G.ε t ω = V) :
    V = velocity β γ G.var := by
  have hMp := level_pos hM hγ G.ε
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (hMp 0 ω₀)
  have hCP : ∀ t ω, C t ω * P t ω = V * level M₀ γ G.ε t ω := fun t ω => by
    rw [← hV t ω, ← h.clearing t ω]
    field_simp [(hMp t ω).ne']
  have hQ : ∀ ω, Q 0 ω = 1 - V := fun ω => by
    rw [← hV 0 ω, velocity_eq h hMp 0 ω]
    ring
  have hae := (h.euler 0).trans (eulerRHS_of_const_velocity G hM.ne' hγ hVpos.ne' hCP 0)
  obtain ⟨ω, hω⟩ := hae.exists
  rw [hQ ω] at hω
  simp only at hω
  rw [velocity]
  linarith

/-- Galí (2015), Ex. 2.5(b), p. 49: an equilibrium with constant velocity exists only if
`Q* = β e^{σ_m²/2}/(1 + γ_m) < 1`, i.e. only if the nominal rate is strictly positive. -/
theorem qstar_lt_one_of_equilibrium [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ)
    (h : IsEquilibrium μ ℱ β φ A (level M₀ γ G.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γ G.ε t ω = V) : Qstar β γ G.var < 1 := by
  have hVeq := velocity_of_constant G hM hγ h hV
  obtain ⟨ω₀, -⟩ := (h.euler 0).exists
  have hVpos : 0 < V := by
    rw [← hV 0 ω₀, ← h.clearing 0 ω₀]
    exact div_pos (mul_pos (h.pos_P 0 ω₀) (h.pos_C 0 ω₀)) (level_pos hM hγ G.ε 0 ω₀)
  rw [hVeq, velocity] at hVpos
  linarith

/-- Galí (2015), Ex. 2.5(b), p. 49 (**existence**): if `β e^{σ_m²/2} < 1 + γ_m`, the
allocation `N_t = 1`, `C_t = Y_t = A_t`, `P_t = V M_t/A_t`, `W_t = P_t A_t`, `Q_t = Q*`, with
`V = 1 − Q*`, is an exact equilibrium. -/
theorem candidate_isEquilibrium [IsProbabilityMeasure μ] (Ga Gm : GaussianInnovations μ ℱ)
    {A₀ γa M₀ γm : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm)
    (hQ : Qstar β γm Gm.var < 1) :
    IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) (level M₀ γm Gm.ε) (level A₀ γa Ga.ε)
      (fun _ _ => 1) (level A₀ γa Ga.ε)
      (fun t ω => velocity β γm Gm.var * level M₀ γm Gm.ε t ω / level A₀ γa Ga.ε t ω)
      (fun t ω => velocity β γm Gm.var * level M₀ γm Gm.ε t ω)
      (fun _ _ => Qstar β γm Gm.var) := by
  have hV : 0 < velocity β γm Gm.var := by rw [velocity]; linarith
  have hAp := level_pos hA hγa Ga.ε
  have hMp := level_pos hM hγm Gm.ε
  refine ⟨hAp, fun _ _ => one_pos, fun t ω => div_pos (mul_pos hV (hMp t ω)) (hAp t ω), ?_, ?_,
    ?_, ?_, fun t ω => (mul_one _).symm, fun _ _ => rfl⟩
  · intro t ω
    simp only [Real.one_rpow, mul_one]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hV.ne']
  · intro t ω
    rw [show 1 - Qstar β γm Gm.var = velocity β γm Gm.var from rfl]
    field_simp [(hAp t ω).ne', (hMp t ω).ne', hV.ne']
  · intro t
    refine (eulerRHS_of_const_velocity Gm hM.ne' hγm hV.ne' (fun t ω => ?_) t).symm
    field_simp [(hAp t ω).ne']
  · intro t ω
    field_simp [(hAp t ω).ne']

/-- Galí (2015), Ex. 2.5(b), p. 49: in an equilibrium with constant velocity, gross inflation is
`P_{t+1}/P_t = (1 + γ_m)/(1 + γ_a) e^{ε^m_{t+1} − ε^a_{t+1}}`. -/
theorem inflation_eq (Ga Gm : GaussianInnovations μ ℱ) {A₀ γa M₀ γm V : ℝ} (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hφ : 0 ≤ φ)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) (level M₀ γm Gm.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm Gm.ε t ω = V) (t : ℕ) (ω : Ω) :
    P (t + 1) ω / P t ω = (1 + γm) / (1 + γa) * Real.exp (Gm.ε (t + 1) ω - Ga.ε (t + 1) ω) := by
  have hAp := level_pos hA hγa Ga.ε
  have hMp := level_pos hM hγm Gm.ε
  have hPeq : ∀ s, P s ω = V * level M₀ γm Gm.ε s ω / level A₀ γa Ga.ε s ω := fun s => by
    have h1 := hV s ω
    rw [(output_eq_technology h hφ hAp s ω).1] at h1
    rw [← h1]
    field_simp [(hAp s ω).ne', (hMp s ω).ne']
  have hVpos : 0 < V := by
    rw [← hV 0 ω, ← h.clearing 0 ω]
    exact div_pos (mul_pos (h.pos_P 0 ω) (h.pos_C 0 ω)) (hMp 0 ω)
  rw [hPeq, hPeq, level_succ, level_succ, Real.exp_sub]
  field_simp [(hAp t ω).ne', (hMp t ω).ne', hVpos.ne', hγa.ne', (Real.exp_pos (Ga.ε (t + 1) ω)).ne']

/-- Galí (2015), Ex. 2.5(b), p. 49: net inflation `π_{t+1} = log(P_{t+1}/P_t)` equals
`log(1 + γ_m) − log(1 + γ_a) + ε^m_{t+1} − ε^a_{t+1}`. -/
theorem log_inflation_eq (Ga Gm : GaussianInnovations μ ℱ) {A₀ γa M₀ γm V : ℝ} (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hφ : 0 ≤ φ)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) (level M₀ γm Gm.ε) C N Y P W Q)
    (hV : ∀ t ω, P t ω * Y t ω / level M₀ γm Gm.ε t ω = V) (t : ℕ) (ω : Ω) :
    Real.log (P (t + 1) ω / P t ω) =
      Real.log (1 + γm) - Real.log (1 + γa) + Gm.ε (t + 1) ω - Ga.ε (t + 1) ω := by
  rw [inflation_eq Ga Gm hA hγa hM hγm hφ h hV t ω, Real.log_mul (div_pos hγm hγa).ne'
    (Real.exp_pos _).ne', Real.log_div hγm.ne' hγa.ne', Real.log_exp]
  ring

/-- Galí (2015), Ex. 2.5(b), p. 49, and p. 32 (`Q = e^{−i}`): the constant nominal rate
`i = −log Q* = log(1 + γ_m) − log β − σ_m²/2`. -/
theorem nominalRate_eq {β γ v : ℝ} (hβ : 0 < β) (hγ : 0 < 1 + γ) :
    -Real.log (Qstar β γ v) = Real.log (1 + γ) - Real.log β - v / 2 := by
  rw [Qstar, Real.log_div (mul_pos hβ (Real.exp_pos _)).ne' hγ.ne',
    Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Galí (2015), Ex. 2.5(c), p. 49: the constraint `Q_t ≤ 1` (a nonnegative nominal rate)
reads `β e^{σ_m²/2} ≤ 1 + γ_m`. -/
theorem qstar_le_one_iff {β γ v : ℝ} (hγ : 0 < 1 + γ) :
    Qstar β γ v ≤ 1 ↔ β * Real.exp (v / 2) ≤ 1 + γ := by
  rw [Qstar, div_le_one hγ]

/-- Galí (2015), Ex. 2.5(c), p. 49: the Friedman rule `i = −log Q* = 0` holds iff `Q* = 1`,
i.e. iff `1 + γ_m = β e^{σ_m²/2}`. -/
theorem friedman_iff {β γ v : ℝ} (hβ : 0 < β) (hγ : 0 < 1 + γ) :
    -Real.log (Qstar β γ v) = 0 ↔ 1 + γ = β * Real.exp (v / 2) := by
  have hQ : 0 < Qstar β γ v := div_pos (mul_pos hβ (Real.exp_pos _)) hγ
  rw [neg_eq_zero, Real.log_eq_zero]
  constructor
  · rintro (h | h | h)
    · exact absurd h hQ.ne'
    · rw [Qstar, div_eq_one_iff_eq hγ.ne'] at h; exact h.symm
    · linarith
  · intro h
    right; left
    rw [Qstar, h, div_self (mul_pos hβ (Real.exp_pos _)).ne']

/-- Galí (2015), Ex. 2.5(c), p. 49 (**imprecision**): at the Friedman rule `Q* = 1` there is no
equilibrium with constant velocity (velocity would be `0`, real balances infinite). -/
theorem not_equilibrium_at_friedman [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ)
    {M₀ γ V : ℝ} (hM : 0 < M₀) (hγ : 0 < 1 + γ) (hF : Qstar β γ G.var = 1)
    (h : IsEquilibrium μ ℱ β φ A (level M₀ γ G.ε) C N Y P W Q) :
    ¬ ∀ t ω, P t ω * Y t ω / level M₀ γ G.ε t ω = V := fun hV => by
  have := qstar_lt_one_of_equilibrium G hM hγ h hV
  linarith

/-! ### (c) Welfare -/

/-- Galí (2015), Ex. 2.5(c), p. 49: in an equilibrium with constant velocity `V`, period
utility is `2 log A_t − log V − 1/(1+φ)`. -/
theorem period_utility_eq (h : IsEquilibrium μ ℱ β φ A M C N Y P W Q) (hφ : 0 ≤ φ)
    (hA : ∀ t ω, 0 < A t ω) (hM : ∀ t ω, 0 < M t ω) {V : ℝ}
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) (t : ℕ) (ω : Ω) :
    utility φ (C t ω) (M t ω / P t ω) (N t ω) =
      2 * Real.log (A t ω) - Real.log V - 1 / (1 + φ) := by
  have hY := output_eq_technology h hφ hA t ω
  have hN := employment_eq_one h hφ hA t ω
  have hP := h.pos_P t ω
  have hVpos : 0 < V := by
    rw [← hV t ω, hY.1]; exact div_pos (mul_pos hP (hA t ω)) (hM t ω)
  have hmp : M t ω / P t ω = A t ω / V := by
    rw [← hV t ω, hY.1]
    field_simp [(hA t ω).ne', (hM t ω).ne', hP.ne']
  rw [utility, hY.2, hmp, hN, Real.one_rpow, Real.log_div (hA t ω).ne' hVpos.ne']
  ring

/-- Galí (2015), Ex. 2.5(c), p. 49: expected log technology,
`E[log A_t] = log A₀ + t log(1 + γ_a)` (the innovations have mean zero). -/
theorem integral_log_level [IsProbabilityMeasure μ] (G : GaussianInnovations μ ℱ) {A₀ γ : ℝ}
    (hA : 0 < A₀) (hγ : 0 < 1 + γ) (t : ℕ) :
    ∫ ω, Real.log (level A₀ γ G.ε t ω) ∂μ = Real.log A₀ + t * Real.log (1 + γ) := by
  have hfun : (fun ω => Real.log (level A₀ γ G.ε t ω))
      = fun ω => (Real.log A₀ + t * Real.log (1 + γ)) + ∑ s ∈ Finset.range t, G.ε (s + 1) ω := by
    funext ω
    rw [level, Real.log_mul (mul_pos hA (pow_pos hγ t)).ne' (Real.exp_pos _).ne',
      Real.log_mul hA.ne' (pow_pos hγ t).ne', Real.log_pow, Real.log_exp]
  have hint : ∀ s, Integrable (G.ε s) μ := fun s =>
    (G.hasLaw s).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))
  have hzero : ∀ s, ∫ ω, G.ε s ω ∂μ = 0 := fun s => by
    rw [(G.hasLaw s).integral_eq, integral_id_gaussianReal]
  rw [hfun, integral_add (integrable_const _) (integrable_finsetSum _ fun s _ => hint (s + 1)),
    integral_finsetSum _ fun s _ => hint (s + 1)]
  simp [hzero]

/-- Galí (2015), Ex. 2.5(c), p. 49: closed-form expected lifetime utility
`(2 log A₀ − log V − 1/(1+φ))/(1 − β) + 2 β log(1 + γ_a)/(1 − β)²`. -/
noncomputable def welfareValue (β φ A₀ γa V : ℝ) : ℝ :=
  (2 * Real.log A₀ - Real.log V - 1 / (1 + φ)) / (1 - β) + 2 * Real.log (1 + γa) * β / (1 - β) ^ 2

/-- Galí (2015), Ex. 2.5(c), p. 49 (**infinite horizon**): in an equilibrium with constant
velocity `V`, expected lifetime utility `∑ₜ βᵗ E[U_t]` converges to `welfareValue`. -/
theorem hasSum_expected_welfare [IsProbabilityMeasure μ] (Ga : GaussianInnovations μ ℱ)
    {A₀ γa V : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hφ : 0 ≤ φ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) :
    HasSum (fun t : ℕ => β ^ t * ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ)
      (welfareValue β φ A₀ γa V) := by
  have hAp := level_pos hA hγa Ga.ε
  have hE : ∀ t : ℕ, ∫ ω, utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ
      = (2 * Real.log A₀ - Real.log V - 1 / (1 + φ)) + 2 * Real.log (1 + γa) * t := by
    intro t
    have hfun : (fun ω => utility φ (C t ω) (M t ω / P t ω) (N t ω))
        = fun ω => 2 * Real.log (level A₀ γa Ga.ε t ω) - (Real.log V + 1 / (1 + φ)) := by
      funext ω
      rw [period_utility_eq h hφ hAp hM hV t ω]
      ring
    have hint : Integrable (fun ω => Real.log (level A₀ γa Ga.ε t ω)) μ := by
      have hfun' : (fun ω => Real.log (level A₀ γa Ga.ε t ω))
          = fun ω => (Real.log A₀ + t * Real.log (1 + γa)) +
            ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω := by
        funext ω
        rw [level, Real.log_mul (mul_pos hA (pow_pos hγa t)).ne' (Real.exp_pos _).ne',
          Real.log_mul hA.ne' (pow_pos hγa t).ne', Real.log_pow, Real.log_exp]
      rw [hfun']
      exact (integrable_const _).add (integrable_finsetSum _ fun s _ =>
        (Ga.hasLaw (s + 1)).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)))
    rw [hfun, integral_sub (hint.const_mul 2) (integrable_const _), integral_const_mul,
      integral_log_level Ga hA hγa t]
    simp
    ring
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left
    (2 * Real.log A₀ - Real.log V - 1 / (1 + φ))
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)).mul_left (2 * Real.log (1 + γa))
  have hsum := hg.add hn
  have hne : (1 - β) ≠ 0 := by linarith
  convert hsum using 1
  · funext t
    rw [hE t]
    ring
  · rw [welfareValue]
    field_simp

/-- Galí (2015), Ex. 2.5(c): `welfareValue = K − log V/(1 − β)` with `K` independent of
monetary policy. -/
theorem welfareValue_eq (β φ A₀ γa V : ℝ) :
    welfareValue β φ A₀ γa V = welfareValue β φ A₀ γa 1 - Real.log V / (1 - β) := by
  simp only [welfareValue, Real.log_one, sub_zero]
  ring

/-- Galí (2015), Ex. 2.5(c): welfare is strictly decreasing in velocity: for `V₁, V₂ > 0`,
`welfare(V₂) < welfare(V₁)` iff `V₁ < V₂`. -/
theorem welfareValue_lt_iff {β φ A₀ γa V₁ V₂ : ℝ} (hβ : β < 1) (h1 : 0 < V₁) (h2 : 0 < V₂) :
    welfareValue β φ A₀ γa V₂ < welfareValue β φ A₀ γa V₁ ↔ V₁ < V₂ := by
  rw [welfareValue_eq β φ A₀ γa V₂, welfareValue_eq β φ A₀ γa V₁, sub_lt_sub_iff_left,
    div_lt_div_iff_of_pos_right (by linarith), Real.log_lt_log_iff h1 h2]

/-- Galí (2015), Ex. 2.5(c), p. 49: welfare is strictly decreasing in money growth `γ_m`
(among policies with an equilibrium, `Q* < 1`). -/
theorem welfare_strictAnti_gamma {β φ A₀ γa v γ₁ γ₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ₁ : 0 < 1 + γ₁) (h12 : γ₁ < γ₂) (hQ : Qstar β γ₁ v < 1) :
    welfareValue β φ A₀ γa (velocity β γ₂ v) < welfareValue β φ A₀ γa (velocity β γ₁ v) := by
  have hγ₂ : 0 < 1 + γ₂ := by linarith
  have hlt : Qstar β γ₂ v < Qstar β γ₁ v :=
    div_lt_div_of_pos_left (mul_pos hβ0 (Real.exp_pos _)) hγ₁ (by linarith)
  have hpos : 0 < Qstar β γ₂ v := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγ₂
  rw [welfareValue_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 2.5(c), p. 49: welfare is strictly increasing in the variance `σ_m²` of
money growth (among policies with an equilibrium, `Q* < 1`): a higher variance raises
`E_t[M_t/M_{t+1}]`, the bond price and real balances. -/
theorem welfare_strictMono_var {β φ A₀ γa γ v₁ v₂ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (h12 : v₁ < v₂) (hQ : Qstar β γ v₂ < 1) :
    welfareValue β φ A₀ γa (velocity β γ v₁) < welfareValue β φ A₀ γa (velocity β γ v₂) := by
  have hlt : Qstar β γ v₁ < Qstar β γ v₂ := by
    unfold Qstar
    gcongr
  rw [welfareValue_lt_iff hβ1 (by rw [velocity]; linarith) (by rw [velocity]; linarith),
    velocity, velocity]
  linarith

/-- Galí (2015), Ex. 2.5(c), p. 49: as a function of the constant nominal rate `i > 0`
(`Q* = e^{−i}`, `V = 1 − e^{−i}`), welfare is strictly decreasing. -/
theorem welfare_rate_strictAnti {β φ A₀ γa : ℝ} (hβ : β < 1) :
    StrictAntiOn (fun i => welfareValue β φ A₀ γa (1 - Real.exp (-i))) (Set.Ioi 0) := by
  intro i hi j hj hij
  have hpos : ∀ x : ℝ, 0 < x → 0 < 1 - Real.exp (-x) := fun x hx => by
    have := Real.exp_lt_exp.2 (show -x < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  simp only
  rw [welfareValue_lt_iff hβ (hpos i hi) (hpos j hj)]
  have := Real.exp_lt_exp.2 (show -j < -i by linarith)
  linarith

/-- Galí (2015), Ex. 2.5(c), p. 49: welfare is unbounded as the nominal rate falls to zero:
`welfare(1 − e^{−i}) → ∞` as `i → 0⁺`. The Friedman rule is a supremum, not attained. -/
theorem tendsto_welfare_rate {β φ A₀ γa : ℝ} (hβ : β < 1) :
    Tendsto (fun i => welfareValue β φ A₀ γa (1 - Real.exp (-i))) (𝓝[>] 0) atTop := by
  have hV : Tendsto (fun i : ℝ => 1 - Real.exp (-i)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun i : ℝ => 1 - Real.exp (-i)) (𝓝 0) (𝓝 (1 - Real.exp (-0))) :=
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).tendsto 0
      simp only [neg_zero, Real.exp_zero, sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with i hi
      have := Real.exp_lt_exp.2 (show -i < 0 by simp only [Set.mem_Ioi] at hi; linarith)
      rw [Real.exp_zero] at this
      simp only [Set.mem_Ioi]
      linarith
  have hlog : Tendsto (fun i : ℝ => -Real.log (1 - Real.exp (-i)) * (1 - β)⁻¹) (𝓝[>] 0) atTop :=
    (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hV)).atTop_mul_const
      (inv_pos.2 (by linarith))
  refine (tendsto_atTop_add_const_left _ (welfareValue β φ A₀ γa 1) hlog).congr fun i => ?_
  rw [welfareValue_eq β φ A₀ γa (1 - Real.exp (-i))]
  ring

/-- Galí (2015), Ex. 2.5(c), p. 49 (**the optimal policy must satisfy the Friedman rule**):
every policy `(γ_m, σ_m²)` with an equilibrium (`Q* < 1`, i.e. `i > 0`) is strictly improved
upon by another admissible policy with an equilibrium; so no policy with `i > 0` is optimal. -/
theorem not_optimal_of_equilibrium {β φ A₀ γa γ v : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < 1 + γ) (hQ : Qstar β γ v < 1) :
    ∃ γ', 0 < 1 + γ' ∧ Qstar β γ' v < 1 ∧
      welfareValue β φ A₀ γa (velocity β γ v) < welfareValue β φ A₀ γa (velocity β γ' v) := by
  set q := Qstar β γ v with hq
  have hqpos : 0 < q := div_pos (mul_pos hβ0 (Real.exp_pos _)) hγ
  set q' := (q + 1) / 2 with hq'
  have hq'pos : 0 < q' := by rw [hq']; linarith
  have hb : 0 < β * Real.exp (v / 2) := mul_pos hβ0 (Real.exp_pos _)
  refine ⟨β * Real.exp (v / 2) / q' - 1, by simp only [add_sub_cancel]; positivity, ?_, ?_⟩
  · have : Qstar β (β * Real.exp (v / 2) / q' - 1) v = q' := by
      rw [Qstar, add_sub_cancel]; field_simp
    rw [this, hq']; linarith
  · have : Qstar β (β * Real.exp (v / 2) / q' - 1) v = q' := by
      rw [Qstar, add_sub_cancel]; field_simp
    rw [welfareValue_lt_iff hβ1 (by rw [velocity, this, hq']; linarith)
      (by rw [velocity, ← hq]; linarith), velocity, velocity, this, ← hq, hq']
    linarith

/-! ### (c) Welfare as the expectation of lifetime utility -/

omit mΩ in
/-- Galí (2015), Ex. 2.5, p. 49: `log A_t = log A₀ + t log(1 + γ) + ε_1 + ⋯ + ε_t`. -/
theorem log_level_eq {A₀ γ : ℝ} (hA : 0 < A₀) (hγ : 0 < 1 + γ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : Real.log (level A₀ γ ε t ω) =
      (Real.log A₀ + t * Real.log (1 + γ)) + ∑ s ∈ Finset.range t, ε (s + 1) ω := by
  rw [level, Real.log_mul (mul_pos hA (pow_pos hγ t)).ne' (Real.exp_pos _).ne',
    Real.log_mul hA.ne' (pow_pos hγ t).ne', Real.log_pow, Real.log_exp]

/-- Galí (2015), Ex. 2.5: Gaussian innovations are integrable. -/
theorem integrable_innovation (G : GaussianInnovations μ ℱ) (s : ℕ) : Integrable (G.ε s) μ :=
  (G.hasLaw s).integrable (memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1))

/-- Galí (2015), Ex. 2.5: `E|ε_s| = ∫ |x| dN(0, σ²)`, the same at every date. -/
theorem integral_abs_innovation (G : GaussianInnovations μ ℱ) (s : ℕ) :
    ∫ ω, |G.ε s ω| ∂μ = ∫ x, |x| ∂(gaussianReal 0 G.var) :=
  (G.hasLaw s).integral_comp (f := fun x : ℝ => |x|) continuous_abs.aestronglyMeasurable

/-- Galí (2015), Ex. 2.5(c), p. 49 (**expected lifetime utility**): in an equilibrium with
constant velocity `V`, `E[∑ₜ βᵗ U_t] = ∑ₜ βᵗ E[U_t] = welfareValue`. The interchange of the
expectation and the infinite sum is justified by the geometric bound
`E|βᵗ U_t| ≤ βᵗ (2(|log A₀| + t|log(1+γ_a)| + t E|ε|) + |log V + 1/(1+φ)|)`. -/
theorem integral_tsum_welfare [IsProbabilityMeasure μ] (Ga : GaussianInnovations μ ℱ)
    {A₀ γa V : ℝ} (hA : 0 < A₀) (hγa : 0 < 1 + γa) (hφ : 0 ≤ φ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h : IsEquilibrium μ ℱ β φ (level A₀ γa Ga.ε) M C N Y P W Q) (hM : ∀ t ω, 0 < M t ω)
    (hV : ∀ t ω, P t ω * Y t ω / M t ω = V) :
    ∫ ω, ∑' t : ℕ, β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω) ∂μ =
      welfareValue β φ A₀ γa V := by
  have hAp := level_pos hA hγa Ga.ε
  set K := Real.log V + 1 / (1 + φ) with hK
  set m₁ := ∫ x, |x| ∂(gaussianReal 0 Ga.var) with hm₁
  have hm₁0 : 0 ≤ m₁ := integral_nonneg fun x => abs_nonneg x
  have hF : ∀ t : ℕ, (fun ω => β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)) =
      fun ω => β ^ t * (2 * ((Real.log A₀ + t * Real.log (1 + γa)) +
        ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω) - K) := by
    intro t
    funext ω
    rw [period_utility_eq h hφ hAp hM hV t ω, log_level_eq hA hγa Ga.ε t ω, hK]
    ring
  have hsumint : ∀ t : ℕ, Integrable (fun ω => ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω) μ :=
    fun t => integrable_finsetSum _ fun s _ => integrable_innovation Ga (s + 1)
  have hint : ∀ t : ℕ, Integrable
      (fun ω => β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)) μ := by
    intro t
    rw [hF t]
    exact (((integrable_const _).add (hsumint t)).const_mul 2 |>.sub
      (integrable_const K)).const_mul (β ^ t)
  set g : ℕ → ℝ := fun t => β ^ t * ((2 * |Real.log A₀| + |K|) +
    (2 * |Real.log (1 + γa)| + 2 * m₁) * t) with hg
  have hgs : Summable g := by
    have h1 := (summable_geometric_of_lt_one hβ0 hβ1).mul_left (2 * |Real.log A₀| + |K|)
    have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)).summable.mul_left
      (2 * |Real.log (1 + γa)| + 2 * m₁)
    refine (h1.add h2).congr fun t => ?_
    simp only [hg]
    ring
  have hbound : ∀ t : ℕ,
      ∫ ω, ‖β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)‖ ∂μ ≤ g t := by
    intro t
    have hpt : ∀ ω, ‖β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)‖ ≤
        β ^ t * ((2 * |Real.log A₀| + |K|) + 2 * t * |Real.log (1 + γa)| +
          2 * ∑ s ∈ Finset.range t, |Ga.ε (s + 1) ω|) := by
      intro ω
      have e := congrFun (hF t) ω
      rw [e, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
      have h1 := Finset.abs_sum_le_sum_abs (fun s => Ga.ε (s + 1) ω) (Finset.range t)
      have h2 : |(t : ℝ) * Real.log (1 + γa)| = t * |Real.log (1 + γa)| := by
        rw [abs_mul, Nat.abs_cast]
      have h3 := abs_add_le (Real.log A₀ + t * Real.log (1 + γa))
        (∑ s ∈ Finset.range t, Ga.ε (s + 1) ω)
      have h4 := abs_add_le (Real.log A₀) (t * Real.log (1 + γa))
      have h5 := abs_sub (2 * ((Real.log A₀ + t * Real.log (1 + γa)) +
        ∑ s ∈ Finset.range t, Ga.ε (s + 1) ω)) K
      rw [abs_mul, abs_two] at h5
      linarith
    have hrint : Integrable (fun ω => β ^ t * ((2 * |Real.log A₀| + |K|) +
        2 * t * |Real.log (1 + γa)| + 2 * ∑ s ∈ Finset.range t, |Ga.ε (s + 1) ω|)) μ :=
      ((integrable_const _).add ((integrable_finsetSum _ fun s _ =>
        (integrable_innovation Ga (s + 1)).abs).const_mul 2)).const_mul (β ^ t)
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => norm_nonneg _) hrint
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (integrable_const _) ((integrable_finsetSum _ fun s _ =>
      (integrable_innovation Ga (s + 1)).abs).const_mul 2), integral_const_mul,
      integral_finsetSum _ fun s _ => (integrable_innovation Ga (s + 1)).abs]
    simp only [integral_abs_innovation, ← hm₁, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, integral_const, probReal_univ, smul_eq_mul, one_mul, hg]
    ring
  have hsum : Summable fun t : ℕ =>
      ∫ ω, ‖β ^ t * utility φ (C t ω) (M t ω / P t ω) (N t ω)‖ ∂μ :=
    hgs.of_nonneg_of_le (fun t => integral_nonneg fun ω => norm_nonneg _) hbound
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [integral_const_mul]
  exact (hasSum_expected_welfare Ga hA hγa hφ hβ0 hβ1 h hM hV).tsum_eq

/-! ### A concrete probability space carrying the shocks (non-vacuity) -/

/-- Galí (2015), Ex. 2.5, p. 49: the law of one period's innovations `(ε^a_t, ε^m_t)`,
independent `N(0, σ_a²)` and `N(0, σ_m²)`. -/
noncomputable abbrev pairLaw (va vm : ℝ≥0) : Measure (ℝ × ℝ) :=
  (gaussianReal 0 va).prod (gaussianReal 0 vm)

/-- Galí (2015), Ex. 2.5, p. 49: the sample space `ℕ → ℝ × ℝ` of innovation sequences with the
i.i.d. product law `⊗ₜ pairLaw` (`Measure.infinitePi`). -/
noncomputable abbrev shockMeasure (va vm : ℝ≥0) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => pairLaw va vm

/-- Galí (2015), Ex. 2.5, p. 49: the natural filtration `ℱ_t = σ((ε^a_s, ε^m_s), s ≤ t)` of the
coordinate process. -/
noncomputable def shockFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ × ℝ)) :=
  Filtration.natural (fun (i : ℕ) (ω : ℕ → ℝ × ℝ) => ω i)
    fun i => (measurable_pi_apply i).stronglyMeasurable

/-- Galí (2015), Ex. 2.5, p. 49: the date-`t+1` innovation pair is independent of `ℱ_t` under
the product law. -/
theorem coord_indep (va vm : ℝ≥0) (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω (t + 1)) inferInstance)
      (shockFiltration t) (shockMeasure va vm) := by
  have hI : iIndep (fun i => MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance)
      (shockMeasure va vm) :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (X := fun _ (x : ℝ × ℝ) => x)
      (P := fun _ : ℕ => pairLaw va vm) (fun _ => measurable_id))
  have h := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hI
    (S := {t + 1}) (T := Set.Iic t) (Set.disjoint_singleton_left.2 (by simp))
  simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iic] at h
  exact h

/-- Galí (2015), Ex. 2.5, p. 49: `ℱ_t` contains the date-`t` innovations. -/
theorem comap_le_shockFiltration (t : ℕ) :
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω t) inferInstance ≤ shockFiltration t :=
  le_iSup₂ (f := fun j (_ : j ≤ t) =>
    MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω j) inferInstance) t le_rfl

/-- Galí (2015), Ex. 2.5, p. 49: the technology innovations `ε^a_t = (ω t).1`, an i.i.d.
`N(0, σ_a²)` sequence adapted to the natural filtration (an instance of
`GaussianInnovations`). -/
noncomputable def techInnovations (va vm : ℝ≥0) :
    GaussianInnovations (shockMeasure va vm) shockFiltration where
  ε := fun t ω => (ω t).1
  var := va
  adapted := fun t => measurable_fst.comp ((comap_measurable _).mono
    (comap_le_shockFiltration t) le_rfl)
  hasLaw := fun t => HasLaw.comp (Y := Prod.fst)
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    (measurePreserving_eval_infinitePi (fun _ : ℕ => pairLaw va vm) t).hasLaw
  indep := fun t => indep_of_indep_of_le_left (coord_indep va vm t)
    (measurable_fst.comp (comap_measurable _)).comap_le

/-- Galí (2015), Ex. 2.5, p. 49: the money-growth innovations `ε^m_t = (ω t).2`, an i.i.d.
`N(0, σ_m²)` sequence adapted to the natural filtration. -/
noncomputable def moneyInnovations (va vm : ℝ≥0) :
    GaussianInnovations (shockMeasure va vm) shockFiltration where
  ε := fun t ω => (ω t).2
  var := vm
  adapted := fun t => measurable_snd.comp ((comap_measurable _).mono
    (comap_le_shockFiltration t) le_rfl)
  hasLaw := fun t => HasLaw.comp (Y := Prod.snd)
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
    (measurePreserving_eval_infinitePi (fun _ : ℕ => pairLaw va vm) t).hasLaw
  indep := fun t => indep_of_indep_of_le_left (coord_indep va vm t)
    (measurable_snd.comp (comap_measurable _)).comap_le

/-- Galí (2015), Ex. 2.5(b), p. 49 (**an exact equilibrium genuinely exists**): on the concrete
space `shockMeasure`, with i.i.d. Gaussian technology and money innovations, if
`β e^{σ_m²/2} < 1 + γ_m` the constant-velocity allocation is an equilibrium. -/
theorem exists_exact_equilibrium (va vm : ℝ≥0) {A₀ γa M₀ γm : ℝ} (hA : 0 < A₀)
    (hγa : 0 < 1 + γa) (hM : 0 < M₀) (hγm : 0 < 1 + γm) (hQ : Qstar β γm vm < 1) :
    IsEquilibrium (shockMeasure va vm) shockFiltration β φ
      (level A₀ γa (techInnovations va vm).ε) (level M₀ γm (moneyInnovations va vm).ε)
      (level A₀ γa (techInnovations va vm).ε) (fun _ _ => 1)
      (level A₀ γa (techInnovations va vm).ε)
      (fun t ω => velocity β γm vm * level M₀ γm (moneyInnovations va vm).ε t ω /
        level A₀ γa (techInnovations va vm).ε t ω)
      (fun t ω => velocity β γm vm * level M₀ γm (moneyInnovations va vm).ε t ω)
      (fun _ _ => Qstar β γm vm) :=
  candidate_isEquilibrium (β := β) (techInnovations va vm) (moneyInnovations va vm) hA hγa hM
    hγm hQ

end Gali.ClassicalMonetaryModel.Ex2_5

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.6: equilibrium uniqueness in the money-in-the-utility-function model

Galí (2015), Chapter 2, Exercise 2.6, p. 49, using eqs. (43) (p. 37) and (47) (p. 39) and the
rule `i_t = ρ + φ_π π_t` (fn. 13, p. 41).

The log-linear MIU equilibrium conditions, stated here for an arbitrary `ExpectationSystem`:

* (43) `y_t = ψ_y + ψ_ya a_t + ψ_yi i_t` (`ψ_y` the additive constant),
  `ψ_ya = (1+φ)/D`, `ψ_yi = −ϖ(1−α)/D`, `D = σ(1−α)+φ+α`;
* (47) `y_t = E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ϖ(E_t i_{t+1} − i_t) − ρ)`;
* the rule `i_t = ρ + φ_π π_t`.

## Main results

* `inflEq_of_isEquilibrium`, `isEquilibrium_iff`: an equilibrium is exactly (43), the rule, and
  `(1 + φ_π k) E_t π_{t+1} = φ_π(1+k) π_t − σψ_ya(E_t a_{t+1} − a_t)`, `k = ϖ + σψ_yi`; with
  no technology shocks `E_t π_{t+1} = c π_t`, `c = φ_π(1+ϖ+σψ_yi)/(1+φ_π(ϖ+σψ_yi))`
  (`expected_infl_eq_c`).
* `kappa_eq`, `kappa_nonneg`: `ϖ + σψ_yi = ϖ(φ+α)/D ≥ 0`.
* `one_lt_abs_c_iff`: for `φ_π ≥ 0`, `|c| > 1 ⟺ φ_π > 1`.
* `unique_of_one_lt_abs_c`, `exists_equilibrium`: for `φ_π > 1` there is exactly one bounded
  equilibrium (for any bounded adapted technology).
* `not_unique_of_le_one`: for `0 ≤ φ_π ≤ 1` every bounded equilibrium has a second one.
* `determinate_iff`: with `a ≡ 0` the unique bounded equilibrium is `π ≡ 0` iff `φ_π > 1`.
* `counterexample_negative_phi`: the sign restriction `φ_π ≥ 0` (implicit in the book) is
  needed: `φ_π = −2`, `ϖ = 0` gives a determinate equilibrium although `φ_π < 1`.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_6

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (18), p. 23: `D = σ(1−α) + φ + α`. -/
def bigD (σ φ α : ℝ) : ℝ := σ * (1 - α) + φ + α

/-- Galí (2015), eq. (43), p. 37: `ψ_ya = (1+φ)/D`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / bigD σ φ α

/-- Galí (2015), eq. (43), p. 37: `ψ_yi = −ϖ(1−α)/D`. -/
noncomputable def psiYI (σ φ α ϖ : ℝ) : ℝ := -(ϖ * (1 - α)) / bigD σ φ α

/-- Galí (2015), Ex. 2.6, p. 49: the coefficient `c = φ_π(1+k)/(1+φ_π k)`, `k = ϖ + σψ_yi`. -/
noncomputable def cCoef (φπ k : ℝ) : ℝ := φπ * (1 + k) / (1 + φπ * k)

/-- Galí (2015), eq. (47), p. 39: the right side
`E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ϖ(E_t i_{t+1} − i_t) − ρ)`. -/
noncomputable def rhs47 (σ ρ ϖ : ℝ) (y infl i : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (y (t + 1)) -
    σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - ϖ • (𝔼.E t (i (t + 1)) - i t) - fun _ => ρ)

/-- Galí (2015), Ex. 2.6, p. 49 (**existence**): the bounded adapted forcing
`u_t = s (E_t a_{t+1} − a_t)` of the inflation equation, `s = σψ_ya/(φ_π(1+k))`. -/
noncomputable def forcing (s : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  s • (𝔼.E t (a (t + 1)) - a t)

variable (σ ρ ϖ ψy ψya ψyi φπ : ℝ) (a y infl i : ℕ → Ω → ℝ)

/-- Galí (2015), Ex. 2.6, p. 49: an equilibrium of the MIU model under `i_t = ρ + φ_π π_t`:
conditions (43), (47) and the rule. -/
structure IsEquilibrium where
  /-- Eq. (43), p. 37. -/
  eq43 : ∀ t, y t = (fun _ => ψy) + ψya • a t + ψyi • i t
  /-- Eq. (47), p. 39. -/
  eq47 : ∀ t, y t = rhs47 𝔼 σ ρ ϖ y infl i t
  /-- The rule `i_t = ρ + φ_π π_t` (Ex. 2.6). -/
  rule : ∀ t, i t = (fun _ => ρ) + φπ • infl t

/-- Galí (2015), Ex. 2.6, p. 49: the reduced inflation equation
`(1 + φ_π k) E_t π_{t+1} = φ_π(1+k) π_t − σψ_ya(E_t a_{t+1} − a_t)`, `k = ϖ + σψ_yi`. -/
def InflEq : Prop :=
  ∀ t, (1 + φπ * (ϖ + σ * ψyi)) • 𝔼.E t (infl (t + 1)) =
    (φπ * (1 + (ϖ + σ * ψyi))) • infl t - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t)

variable {𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i}

/-- Pointwise form of eq. (43) and its date-`t` expectation (Galí (2015), p. 37). -/
theorem eq43_apply (h43 : ∀ t, y t = (fun _ => ψy) + ψya • a t + ψyi • i t) (t : ℕ) (ω : Ω) :
    y t ω = ψy + ψya * a t ω + ψyi * i t ω ∧
      𝔼.E t (y (t + 1)) ω = ψy + ψya * 𝔼.E t (a (t + 1)) ω + ψyi * 𝔼.E t (i (t + 1)) ω := by
  refine ⟨by simp [h43 t], ?_⟩
  rw [h43 (t + 1)]
  simp [map_add, map_smul, 𝔼.const]

/-- Pointwise form of the rule `i_t = ρ + φ_π π_t` and its expectation (Galí (2015), Ex. 2.6). -/
theorem rule_apply (hr : ∀ t, i t = (fun _ => ρ) + φπ • infl t) (t : ℕ) (ω : Ω) :
    i t ω = ρ + φπ * infl t ω ∧ 𝔼.E t (i (t + 1)) ω = ρ + φπ * 𝔼.E t (infl (t + 1)) ω := by
  refine ⟨by simp [hr t], ?_⟩
  rw [hr (t + 1)]
  simp [map_add, map_smul, 𝔼.const]

/-- Galí (2015), eq. (47), p. 39, pointwise and multiplied through by `σ ≠ 0`. -/
theorem eq47_apply_iff (hσ : σ ≠ 0) (t : ℕ) (ω : Ω) :
    y t ω = rhs47 𝔼 σ ρ ϖ y infl i t ω ↔
      σ * (y t ω - 𝔼.E t (y (t + 1)) ω) =
        -(i t ω - 𝔼.E t (infl (t + 1)) ω - ϖ * (𝔼.E t (i (t + 1)) ω - i t ω) - ρ) := by
  simp only [rhs47, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have : y t ω - 𝔼.E t (y (t + 1)) ω =
        -(i t ω - 𝔼.E t (infl (t + 1)) ω - ϖ * (𝔼.E t (i (t + 1)) ω - i t ω) - ρ) / σ := by
      rw [← h]; field_simp
    rw [div_eq_inv_mul] at this
    linarith

/-- Galí (2015), Ex. 2.6, p. 49: every equilibrium satisfies the reduced inflation equation. -/
theorem inflEq_of_isEquilibrium (hσ : σ ≠ 0)
    (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i) :
    InflEq 𝔼 σ ϖ ψya ψyi φπ a infl := by
  intro t
  funext ω
  obtain ⟨hy, hEy⟩ := eq43_apply h.eq43 t ω
  obtain ⟨hi, hEi⟩ := rule_apply (𝔼 := 𝔼) h.rule t ω
  have h47 := (eq47_apply_iff hσ t ω).1 (congrFun (h.eq47 t) ω)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hy, hEy, hEi, hi] at h47
  linear_combination -h47

/-- Galí (2015), Ex. 2.6, p. 49: conversely, (43), the rule and the reduced inflation equation
give (47); so an equilibrium is exactly (43) + rule + `InflEq`. -/
theorem isEquilibrium_iff (hσ : σ ≠ 0) :
    Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i) ↔
      (∀ t, y t = (fun _ => ψy) + ψya • a t + ψyi • i t) ∧
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) ∧ InflEq 𝔼 σ ϖ ψya ψyi φπ a infl := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.eq43, h.rule, inflEq_of_isEquilibrium hσ h⟩
  · rintro ⟨h43, hr, hI⟩
    refine ⟨⟨h43, fun t => ?_, hr⟩⟩
    funext ω
    obtain ⟨hy, hEy⟩ := eq43_apply h43 t ω
    obtain ⟨hi, hEi⟩ := rule_apply (𝔼 := 𝔼) hr t ω
    have hIt := congrFun (hI t) ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hIt
    refine (eq47_apply_iff hσ t ω).2 ?_
    rw [hy, hEy, hEi, hi]
    linear_combination -hIt

/-- Galí (2015), Ex. 2.6, p. 49: with no technology shocks (`a ≡ 0`) and `1 + φ_π k ≠ 0`,
every equilibrium satisfies `E_t π_{t+1} = c π_t`. -/
theorem expected_infl_eq_c (hσ : σ ≠ 0) (ha : ∀ t, a t = 0)
    (hk : 1 + φπ * (ϖ + σ * ψyi) ≠ 0) (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i)
    (t : ℕ) : 𝔼.E t (infl (t + 1)) = cCoef φπ (ϖ + σ * ψyi) • infl t := by
  have hI := inflEq_of_isEquilibrium hσ h t
  rw [ha, ha, map_zero, sub_zero, smul_zero, sub_zero] at hI
  funext ω
  have := congrFun hI ω
  simp only [Pi.smul_apply, smul_eq_mul] at this
  simp only [Pi.smul_apply, smul_eq_mul, cCoef]
  field_simp
  linarith

/-- Galí (2015), Ex. 2.6 and eq. (43), p. 37: `ϖ + σψ_yi = ϖ(φ+α)/D` (for `D ≠ 0`). -/
theorem kappa_eq {σ φ α ϖ : ℝ} (hD : bigD σ φ α ≠ 0) :
    ϖ + σ * psiYI σ φ α ϖ = ϖ * (φ + α) / bigD σ φ α := by
  rw [psiYI]
  field_simp
  rw [bigD]
  ring

/-- Galí (2015), Ex. 2.6, p. 49: `ϖ + σψ_yi ≥ 0` under `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1` and the
book's maintained `ϖ ≥ 0` (p. 38). -/
theorem kappa_nonneg {σ φ α ϖ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hϖ : 0 ≤ ϖ) : 0 ≤ ϖ + σ * psiYI σ φ α ϖ := by
  have hD : 0 < bigD σ φ α := by
    rw [bigD]; nlinarith
  rw [kappa_eq hD.ne']
  exact div_nonneg (mul_nonneg hϖ (by linarith)) hD.le

/-- Galí (2015), Ex. 2.6, p. 49: for `φ_π ≥ 0` and `k ≥ 0`, `|c| > 1 ⟺ φ_π > 1`. -/
theorem one_lt_abs_c_iff {φπ k : ℝ} (hφ : 0 ≤ φπ) (hk : 0 ≤ k) :
    1 < |cCoef φπ k| ↔ 1 < φπ := by
  have hd : 0 < 1 + φπ * k := by nlinarith
  have hc : 0 ≤ cCoef φπ k := div_nonneg (mul_nonneg hφ (by linarith)) hd.le
  rw [abs_of_nonneg hc, cCoef, one_lt_div hd]
  constructor <;> intro h <;> nlinarith

/-- Galí (2015), Ex. 2.6, p. 49 (**uniqueness**): if `1 + φ_π k ≠ 0` and `|c| > 1`, two
bounded equilibria with the same technology coincide. -/
theorem unique_of_one_lt_abs_c (hσ : σ ≠ 0) (hk : 1 + φπ * (ϖ + σ * ψyi) ≠ 0)
    (hc : 1 < |cCoef φπ (ϖ + σ * ψyi)|) {y' infl' i' : ℕ → Ω → ℝ}
    (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i)
    (h' : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y' infl' i')
    (hb : BoundedProc infl) (hb' : BoundedProc infl') :
    y = y' ∧ infl = infl' ∧ i = i' := by
  set k := ϖ + σ * ψyi with hkdef
  set c := cCoef φπ k with hcdef
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith
  have hI := inflEq_of_isEquilibrium hσ h
  have hI' := inflEq_of_isEquilibrium hσ h'
  -- the difference d solves d_t = c⁻¹ E_t d_{t+1}
  have hd : ∀ t, (infl - infl') t = c⁻¹ • 𝔼.E t ((infl - infl') (t + 1)) + 0 := by
    intro t
    funext ω
    have e1 := congrFun (hI t) ω
    have e2 := congrFun (hI' t) ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2
    rw [← hkdef] at e1 e2
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      Pi.zero_apply, add_zero]
    have key : c * (infl t ω - infl' t ω) =
        𝔼.E t (infl (t + 1)) ω - 𝔼.E t (infl' (t + 1)) ω := by
      rw [hcdef, cCoef]
      field_simp
      linear_combination e2 - e1
    rw [← key, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = c⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t; simp
  have hbd : BoundedProc (infl - infl') := by
    obtain ⟨M, hM⟩ := hb
    obtain ⟨M', hM'⟩ := hb'
    exact ⟨M + M', fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))⟩
  have hca : |c⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hc
  have hdz := 𝔼.forward_unique hca hd hz hbd ⟨0, fun _ _ => by simp⟩
  have hπ : infl = infl' := sub_eq_zero.1 hdz
  have hi : i = i' := by
    funext t; rw [h.rule t, h'.rule t, hπ]
  refine ⟨?_, hπ, hi⟩
  funext t; rw [h.eq43 t, h'.eq43 t, hi]

/-- Galí (2015), Ex. 2.6, p. 49 (**existence**): for `φ_π > 1`, `k ≥ 0`, and bounded adapted
technology, there is a bounded adapted equilibrium: `π` is the forward series
`∑ c⁻ʲ E_t u_{t+j}`, `i_t = ρ + φ_π π_t`, and `y` from (43). -/
theorem exists_equilibrium (hσ : σ ≠ 0) (hφ : 1 < φπ) (hk : 0 ≤ ϖ + σ * ψyi)
    (ha : 𝔼.Adapted a) {Ma : ℝ} (hab : ∀ t ω, |a t ω| ≤ Ma) :
    ∃ y' infl' i' : ℕ → Ω → ℝ, Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y' infl' i') ∧
      BoundedProc infl' ∧ 𝔼.Adapted infl' ∧ 𝔼.Adapted i' ∧ 𝔼.Adapted y' := by
  set k := ϖ + σ * ψyi with hkdef
  set c := cCoef φπ k with hcdef
  have hd : 0 < 1 + φπ * k := by nlinarith
  have hc1 : 1 < c := by
    have := (one_lt_abs_c_iff (by linarith) hk).2 hφ
    have hc0' : 0 ≤ cCoef φπ k := div_nonneg (mul_nonneg (by linarith) (by linarith)) hd.le
    rw [abs_of_nonneg hc0'] at this
    exact this
  have hcinv0 : 0 ≤ c⁻¹ := inv_nonneg.2 (by linarith)
  have hcinv1 : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc1
  set s := σ * ψya / (φπ * (1 + k)) with hsdef
  set u := forcing 𝔼 s a with hudef
  have hub : ∀ t ω, |u t ω| ≤ |s| * (Ma + Ma) := by
    intro t ω
    simp only [hudef, forcing, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
      (add_le_add (𝔼.abs_E_le (hab (t + 1)) t ω) (hab t ω))) (abs_nonneg s)
  have hua : 𝔼.Adapted u := by
    intro t
    simp only [hudef, forcing, map_smul, map_sub, 𝔼.E_E_self, ha t]
  set p := 𝔼.forwardSeries c⁻¹ u with hpdef
  have hp := 𝔼.forwardSeries_solves hcinv0 hcinv1 hub hua
  rw [← hpdef] at hp
  have hpa : 𝔼.Adapted p := by
    intro t
    rw [hp t, map_add, map_smul, 𝔼.E_E_self, hua t]
  refine ⟨fun t => (fun _ => ψy) + ψya • a t + ψyi • ((fun _ => ρ) + φπ • p t), p,
    fun t => (fun _ => ρ) + φπ • p t, ?_, 𝔼.forwardSeries_bounded hcinv0 hcinv1 hub, hpa, ?_, ?_⟩
  · refine (isEquilibrium_iff hσ).2 ⟨fun _ => rfl, fun _ => rfl, fun t => ?_⟩
    funext ω
    have e := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hudef, forcing, Pi.sub_apply] at e
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hφ0 : φπ * (1 + k) ≠ 0 := by positivity
    rw [e]
    simp only [hcdef, cCoef, hsdef]
    field_simp
    ring
  · intro t
    simp only [map_add, map_smul, 𝔼.const, hpa t]
  · intro t
    simp only [map_add, map_smul, 𝔼.const, hpa t, ha t]

/-- Galí (2015), Ex. 2.6, p. 49 (**multiplicity**): if `0 ≤ φ_π ≤ 1` and `k ≥ 0`, every
equilibrium `(y, π, i)` has a second, distinct one, `π_t + cᵗ` (with `i`, `y` adjusted),
which is bounded (and adapted) whenever the first is: `0 ≤ c ≤ 1`. -/
theorem not_unique_of_le_one [Nonempty Ω] (hσ : σ ≠ 0) (hφ0 : 0 ≤ φπ) (hφ1 : φπ ≤ 1)
    (hk : 0 ≤ ϖ + σ * ψyi) (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i)
    (hb : BoundedProc infl) :
    ∃ y' infl' i' : ℕ → Ω → ℝ, Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y' infl' i') ∧
      BoundedProc infl' ∧ infl' ≠ infl ∧
      (𝔼.Adapted infl → 𝔼.Adapted infl') := by
  set k := ϖ + σ * ψyi with hkdef
  set c := cCoef φπ k with hcdef
  have hd : 0 < 1 + φπ * k := by nlinarith
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg hφ0 (by linarith)) hd.le
  have hc1 : c ≤ 1 := by
    rw [hcdef, cCoef, div_le_one hd]; nlinarith
  set d : ℕ → Ω → ℝ := fun t _ => c ^ t with hddef
  have hI := inflEq_of_isEquilibrium hσ h
  refine ⟨fun t => y t + (ψyi * φπ) • d t, fun t => infl t + d t, fun t => i t + φπ • d t, ?_,
    ?_, ?_, ?_⟩
  · refine (isEquilibrium_iff hσ).2 ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
    · rw [h.eq43 t, smul_add, mul_smul]; abel
    · rw [h.rule t, smul_add]; abel
    · funext ω
      have e := congrFun (hI t) ω
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_add, hddef,
        𝔼.const]
      have hcd : (1 + φπ * k) * c = φπ * (1 + k) := by
        rw [hcdef, cCoef]; field_simp
      rw [pow_succ]
      linear_combination e + c ^ t * hcd
  · obtain ⟨M, hM⟩ := hb
    refine ⟨M + 1, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)⟩
    simp only [hddef, abs_pow, abs_of_nonneg hc0]
    exact pow_le_one₀ hc0 hc1
  · intro heq
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun heq 0) ω
    simp [hddef] at this
  · intro hpa t
    simp only [map_add, hpa t, hddef, 𝔼.const]

/-- Galí (2015), Ex. 2.6, p. 49: with no technology shocks the zero-inflation path
`π ≡ 0`, `i ≡ ρ`, `y ≡ ψ_y + ψ_yi ρ` is an equilibrium. -/
theorem zero_isEquilibrium (hσ : σ ≠ 0) :
    Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ (fun _ => 0)
      (fun _ _ => ψy + ψyi * ρ) (fun _ => 0) (fun _ _ => ρ)) := by
  refine (isEquilibrium_iff hσ).2 ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω; simp
  · funext ω; simp
  · funext ω; simp

/-- Galí (2015), Ex. 2.6, p. 49 (**the exercise**): with no technology shocks, `σ > 0` and
`k = ϖ + σψ_yi ≥ 0` (`kappa_nonneg`), the unique bounded equilibrium is `π ≡ 0` if and only if
`φ_π > 1` (for `φ_π ≥ 0`). -/
theorem determinate_iff [Nonempty Ω] (hσ : σ ≠ 0) (hφ0 : 0 ≤ φπ) (hk : 0 ≤ ϖ + σ * ψyi) :
    (∀ y' infl' i' : ℕ → Ω → ℝ,
      Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ (fun _ => 0) y' infl' i') →
        BoundedProc infl' → infl' = fun _ => 0) ↔ 1 < φπ := by
  constructor
  · intro hU
    by_contra hle
    push Not at hle
    obtain ⟨y', infl', i', ⟨h'⟩, hb', hne, -⟩ := not_unique_of_le_one hσ hφ0 hle hk
      (zero_isEquilibrium (𝔼 := 𝔼) (ψya := ψya) (φπ := φπ) hσ).some ⟨0, fun _ _ => by simp⟩
    exact hne (hU _ _ _ ⟨h'⟩ hb')
  · intro hφ y' infl' i' ⟨h'⟩ hb'
    have hd : 0 < 1 + φπ * (ϖ + σ * ψyi) := by nlinarith
    have hc := (one_lt_abs_c_iff hφ0 hk).2 hφ
    exact (unique_of_one_lt_abs_c hσ hd.ne' hc h'
      (zero_isEquilibrium (𝔼 := 𝔼) (ψya := ψya) (φπ := φπ) hσ).some hb'
      ⟨0, fun _ _ => by simp⟩).2.1

/-- Galí (2015), Ex. 2.6, p. 49 (**correction**: the restriction `φ_π ≥ 0` is needed): with
`ϖ = 0` (so `k = 0`) and `φ_π = −2 < 1` we get `|c| = 2 > 1`, so the bounded equilibrium is
still unique. -/
theorem counterexample_negative_phi :
    1 < |cCoef (-2) 0| ∧ (1 : ℝ) + (-2) * 0 ≠ 0 ∧ ¬ (1 < (-2 : ℝ)) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [cCoef]
  norm_num

/-- Galí (2015), Ex. 2.6, p. 49 (**correction**, applied): with `ϖ = 0`, `ψ_yi = 0` and
`φ_π = −2`, two bounded equilibria coincide, although `φ_π < 1`. -/
theorem unique_negative_phi (hσ : σ ≠ 0) {y' infl' i' : ℕ → Ω → ℝ}
    (h : IsEquilibrium 𝔼 σ ρ 0 ψy ψya 0 (-2) a y infl i)
    (h' : IsEquilibrium 𝔼 σ ρ 0 ψy ψya 0 (-2) a y' infl' i')
    (hb : BoundedProc infl) (hb' : BoundedProc infl') :
    y = y' ∧ infl = infl' ∧ i = i' :=
  unique_of_one_lt_abs_c hσ (by norm_num) (by simpa using counterexample_negative_phi.1) h h'
    hb hb'

end Gali.ClassicalMonetaryModel.Ex2_6

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.7: a shopping-time model

Galí (2015), Chapter 2, Exercise 2.7, p. 50. Consuming `C` takes shopping time `S(C, M/P)` with
`S_c > 0`, `S_m ≤ 0`; period utility is `V(C, L)` with leisure `L = 1 − N − S(C, M/P)`. Write
`m = M/P`.

## (a) The implied utility `U(C, m, N) = V(C, 1 − N − S(C, m))` (`shoppingU`)

* `hasDerivAt_curve`: the chain rule along a curve, for differentiable `V : ℝ × ℝ → ℝ`.
* `hasDerivAt_U_c`, `hasDerivAt_U_m`, `hasDerivAt_U_n`: `U_c = V_C − V_L S_c`,
  `U_m = −V_L S_m`, `U_n = −V_L`.
* `U_m_nonneg`, `U_n_neg`, `U_c_lt_V_C`: `U_m ≥ 0`, `U_n < 0`, and `U_c < V_C` (the sign of
  `U_c` is ambiguous, `U_c_sign_ambiguous`).
* Second derivatives along sections (`C` fixed, `v = V(C, ·)`, `s = S(C, ·)`):
  `U_mm = v'' s'² − v' s''` (`hasDerivAt_U_mm`, `U_mm_nonpos`), `U_nn = v''`
  (`hasDerivAt_U_nn`), `U_nm = v'' s'` (`hasDerivAt_U_nm`, `U_nm_nonneg`).

## (b) Optimality and `(W/P)(−S_m) ≃ i`

* `labour_foc`, `money_foc` (**necessity**, under the budget constraint (31)): along
  `P dC = W dN`, `(W/P) U_c + U_n = 0` (eq. (4)); along the portfolio line
  `P dC = −(1 − Q) P dm`, `U_m = (1 − Q) U_c` (eq. (33)).
* `shopping_rate_eq`: hence `(W/P)(−S_m) = 1 − Q = 1 − e^{−i}` **exactly**; and
  `shopping_rate_approx`: `|(W/P)(−S_m) − i| ≤ i²` for `|i| ≤ 1`, with
  `hasDerivAt_one_sub_exp_neg` (value `0` and slope `1` at `i = 0`).

## (c) Money demand with `V = log C + χ log L`, `S = A v + B/v − 2√(AB)`, `v = C/m`

* `hasDerivAt_S_m`: `S_m = −A C/m² + B/C`; `S_nonneg`, `S_eq_zero_iff` (minimum at
  `v = √(B/A)`); `S_m_nonpos_iff` (`S_m ≤ 0 ⟺ v² ≥ B/A`).
* `money_demand`: `v² = B/A + (1 − Q) C/(A w)`, i.e. `m = C/√(B/A + (1 − Q) C/(A w))`,
  `w = W/P`; `money_demand_of_hasFDerivAt` derives it from (b).
* `money_demand_strictAnti`: real balances fall as `1 − Q` (the nominal rate) rises;
  `money_demand_satiation`: at `i = 0`, `v = √(B/A)` (finite satiation).
-/

namespace Gali.ClassicalMonetaryModel.Ex2_7

open Filter Topology

/-- Galí (2015), Ex. 2.7(a), p. 50: the implied utility `U(C, m, N) = V(C, 1 − N − S(C, m))`. -/
def shoppingU (V S : ℝ × ℝ → ℝ) (C m N : ℝ) : ℝ := V (C, 1 - N - S (C, m))

/-- Galí (2015), Ex. 2.7(a), p. 50: the chain rule along a curve,
`d/dt V(f t, g t) = f' V_1 + g' V_2`, where `V_1 = V'(1,0)`, `V_2 = V'(0,1)`. -/
theorem hasDerivAt_curve {V : ℝ × ℝ → ℝ} {V' : ℝ × ℝ →L[ℝ] ℝ} {f g : ℝ → ℝ} {a b t : ℝ}
    (hV : HasFDerivAt V V' (f t, g t)) (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => V (f s, g s)) (a * V' (1, 0) + b * V' (0, 1)) t := by
  have h := hV.comp_hasDerivAt (f := fun s => (f s, g s)) t (hf.prodMk hg)
  have hv : ((a, b) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact h

/-- Galí (2015), Ex. 2.7(a): partial derivatives of a differentiable `S : ℝ × ℝ → ℝ` along the
coordinate sections. -/
theorem hasDerivAt_sections {S : ℝ × ℝ → ℝ} {S' : ℝ × ℝ →L[ℝ] ℝ} {C m : ℝ}
    (hS : HasFDerivAt S S' (C, m)) :
    HasDerivAt (fun C' => S (C', m)) (S' (1, 0)) C ∧
      HasDerivAt (fun m' => S (C, m')) (S' (0, 1)) m := by
  constructor
  · have := hasDerivAt_curve (f := fun x => x) (g := fun _ => m) hS (hasDerivAt_id' C)
      (hasDerivAt_const C m)
    simpa using this
  · have := hasDerivAt_curve (f := fun _ => C) (g := fun x => x) hS (hasDerivAt_const m C)
      (hasDerivAt_id' m)
    simpa using this

variable {V S : ℝ × ℝ → ℝ} {V' S' : ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_c = V_C − V_L S_c`. -/
theorem hasDerivAt_U_c (hV : HasFDerivAt V V' (C, 1 - N - S (C, m)))
    (hS : HasFDerivAt S S' (C, m)) :
    HasDerivAt (fun C' => shoppingU V S C' m N) (V' (1, 0) - V' (0, 1) * S' (1, 0)) C := by
  have hL : HasDerivAt (fun C' => 1 - N - S (C', m)) (-S' (1, 0)) C := by
    have := ((hasDerivAt_sections hS).1).const_sub (1 - N)
    simpa using this
  have := hasDerivAt_curve (f := fun x => x) (g := fun C' => 1 - N - S (C', m)) (t := C) hV
    (hasDerivAt_id' C) hL
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_m = −V_L S_m`. -/
theorem hasDerivAt_U_m (hV : HasFDerivAt V V' (C, 1 - N - S (C, m)))
    (hS : HasFDerivAt S S' (C, m)) :
    HasDerivAt (fun m' => shoppingU V S C m' N) (-(V' (0, 1) * S' (0, 1))) m := by
  have hL : HasDerivAt (fun m' => 1 - N - S (C, m')) (-S' (0, 1)) m := by
    have := ((hasDerivAt_sections hS).2).const_sub (1 - N)
    simpa using this
  have := hasDerivAt_curve (f := fun _ => C) (g := fun m' => 1 - N - S (C, m')) (t := m) hV
    (hasDerivAt_const m C) hL
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_n = −V_L`. -/
theorem hasDerivAt_U_n (hV : HasFDerivAt V V' (C, 1 - N - S (C, m))) :
    HasDerivAt (fun N' => shoppingU V S C m N') (-V' (0, 1)) N := by
  have hL : HasDerivAt (fun N' => 1 - N' - S (C, m)) (-1) N :=
    ((hasDerivAt_id' N).const_sub 1).sub_const (S (C, m))
  have := hasDerivAt_curve (f := fun _ => C) (g := fun N' => 1 - N' - S (C, m)) (t := N) hV
    (hasDerivAt_const N C) hL
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: with `V_L > 0` and `S_m ≤ 0`, `U_m = −V_L S_m ≥ 0`. -/
theorem U_m_nonneg {VL Sm : ℝ} (hVL : 0 < VL) (hSm : Sm ≤ 0) : 0 ≤ -(VL * Sm) := by
  nlinarith

/-- Galí (2015), Ex. 2.7(a), p. 50: with `V_L > 0`, `U_n = −V_L < 0`. -/
theorem U_n_neg {VL : ℝ} (hVL : 0 < VL) : -VL < 0 := by linarith

/-- Galí (2015), Ex. 2.7(a), p. 50: with `V_L > 0` and `S_c > 0`, `U_c = V_C − V_L S_c < V_C`:
shopping time lowers the marginal utility of consumption. -/
theorem U_c_lt_V_C {VC VL Sc : ℝ} (hVL : 0 < VL) (hSc : 0 < Sc) : VC - VL * Sc < VC := by
  nlinarith

/-- Galí (2015), Ex. 2.7(a), p. 50: the sign of `U_c = V_C − V_L S_c` is not determined by the
signs of `V_C, V_L, S_c > 0` alone. -/
theorem U_c_sign_ambiguous :
    (0 : ℝ) < 1 - 1 * (1 / 2) ∧ (1 : ℝ) - 1 * 2 < 0 := by norm_num

/-- Galí (2015), Ex. 2.7(a), p. 50: along the section `m ↦ U(C, m, N)` with `v = V(C, ·)`,
`s = S(C, ·)`: `U_m = −v'(L) s'(m)`. -/
theorem hasDerivAt_section_m {v v' s s' : ℝ → ℝ} {N m : ℝ}
    (hv : ∀ L, HasDerivAt v (v' L) L) (hs : HasDerivAt s (s' m) m) :
    HasDerivAt (fun m' => v (1 - N - s m')) (-(v' (1 - N - s m) * s' m)) m := by
  have := (hv (1 - N - s m)).comp m (hs.const_sub (1 - N))
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_mm = v''(L) s'(m)² − v'(L) s''(m)`. -/
theorem hasDerivAt_U_mm {v' v'' s s' s'' : ℝ → ℝ} {N m : ℝ}
    (hv' : ∀ L, HasDerivAt v' (v'' L) L) (hs : HasDerivAt s (s' m) m)
    (hs' : HasDerivAt s' (s'' m) m) :
    HasDerivAt (fun m' => -(v' (1 - N - s m') * s' m'))
      (v'' (1 - N - s m) * s' m ^ 2 - v' (1 - N - s m) * s'' m) m := by
  have h1 := (hv' (1 - N - s m)).comp m (hs.const_sub (1 - N))
  have := (h1.mul hs').neg
  exact this.congr_deriv (by simp only [Function.comp_def]; ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_mm ≤ 0` when `V` is concave in leisure (`v'' ≤ 0`),
`V_L ≥ 0`, and shopping time is convex in real balances (`s'' ≥ 0`). -/
theorem U_mm_nonpos {vpp vp sp spp : ℝ} (hvpp : vpp ≤ 0) (hvp : 0 ≤ vp) (hspp : 0 ≤ spp) :
    vpp * sp ^ 2 - vp * spp ≤ 0 := by
  nlinarith [sq_nonneg sp, mul_nonneg hvp hspp]

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_n = −v'(L)` along `N`, and `U_nn = v''(L) ≤ 0` when `V`
is concave in leisure. -/
theorem hasDerivAt_U_nn {v v' v'' : ℝ → ℝ} {N sm : ℝ} (hv : ∀ L, HasDerivAt v (v' L) L)
    (hv' : ∀ L, HasDerivAt v' (v'' L) L) :
    HasDerivAt (fun N' => v (1 - N' - sm)) (-v' (1 - N - sm)) N ∧
      HasDerivAt (fun N' => -v' (1 - N' - sm)) (v'' (1 - N - sm)) N := by
  have hL : HasDerivAt (fun N' : ℝ => 1 - N' - sm) (-1) N :=
    ((hasDerivAt_id' N).const_sub 1).sub_const sm
  constructor
  · have := (hv (1 - N - sm)).comp N hL
    exact this.congr_deriv (by ring)
  · have := ((hv' (1 - N - sm)).comp N hL).neg
    exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: the cross derivative `U_nm = v''(L) s'(m)`
(differentiating `U_n = −v'(1 − N − s(m))` in `m`). -/
theorem hasDerivAt_U_nm {v' v'' s s' : ℝ → ℝ} {N m : ℝ}
    (hv' : ∀ L, HasDerivAt v' (v'' L) L) (hs : HasDerivAt s (s' m) m) :
    HasDerivAt (fun m' => -v' (1 - N - s m')) (v'' (1 - N - s m) * s' m) m := by
  have := ((hv' (1 - N - s m)).comp m (hs.const_sub (1 - N))).neg
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_nm = v'' s' ≥ 0` when `v'' ≤ 0` and `S_m ≤ 0`: more real
balances save shopping time and so raise the marginal disutility-of-work term. -/
theorem U_nm_nonneg {vpp sp : ℝ} (hvpp : vpp ≤ 0) (hsp : sp ≤ 0) : 0 ≤ vpp * sp :=
  mul_nonneg_of_nonpos_of_nonpos hvpp hsp

/-! ### (b) Optimality conditions -/

/-- Galí (2015), Ex. 2.7(b), with eq. (4), p. 19 (**necessity**): if hours `N` are a local
optimum along the budget line `P C = W N + X` (from (31), everything else fixed), then
`(W/P) U_c + U_n = 0`. -/
theorem labour_foc {P W X L : ℝ} (hP : 0 < P) (hbud : P * C = W * N + X)
    (hL : L = 1 - N - S (C, m)) (hV : HasFDerivAt V V' (C, L)) (hS : HasFDerivAt S S' (C, m))
    (hloc : IsLocalMax (fun N' => shoppingU V S ((W * N' + X) / P) m N') N) :
    W / P * (V' (1, 0) - V' (0, 1) * S' (1, 0)) + -V' (0, 1) = 0 := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hc : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id' N).const_mul W).add_const X).div_const P
    simpa using this
  have hSc : HasDerivAt (fun N' => S ((W * N' + X) / P, m)) (W / P * S' (1, 0)) N := by
    have := hasDerivAt_curve (f := fun N' => (W * N' + X) / P) (g := fun _ => m)
      (by rw [hCeq]; exact hS) hc (hasDerivAt_const N m)
    simpa using this
  have hl : HasDerivAt (fun N' => 1 - N' - S ((W * N' + X) / P, m)) (-1 - W / P * S' (1, 0))
      N := by
    have := ((hasDerivAt_id' N).const_sub 1).sub hSc
    convert this using 1
  have hg := hasDerivAt_curve (f := fun N' => (W * N' + X) / P)
    (g := fun N' => 1 - N' - S ((W * N' + X) / P, m)) (by rw [hCeq, ← hL]; exact hV) hc hl
  have h0 := hloc.hasDerivAt_eq_zero hg
  linear_combination h0

/-- Galí (2015), Ex. 2.7(b), with eq. (33), p. 32 (**necessity**): along the portfolio line
`P C + (1 − Q) P m = X` (budget (32), total wealth fixed), a local optimum `m` satisfies
`U_m = (1 − Q) U_c`. -/
theorem money_foc {P Q X L : ℝ} (hP : 0 < P) (hbud : P * C + (1 - Q) * P * m = X)
    (hL : L = 1 - N - S (C, m)) (hV : HasFDerivAt V V' (C, L)) (hS : HasFDerivAt S S' (C, m))
    (hloc : IsLocalMax (fun m' => shoppingU V S ((X - (1 - Q) * P * m') / P) m' N) m) :
    -(V' (0, 1) * S' (0, 1)) = (1 - Q) * (V' (1, 0) - V' (0, 1) * S' (1, 0)) := by
  have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
  have hc : HasDerivAt (fun m' : ℝ => (X - (1 - Q) * P * m') / P) (-(1 - Q)) m := by
    have := (((hasDerivAt_id' m).const_mul ((1 - Q) * P)).const_sub X).div_const P
    convert this using 1
    field_simp
  have hSm : HasDerivAt (fun m' => S ((X - (1 - Q) * P * m') / P, m'))
      (-(1 - Q) * S' (1, 0) + 1 * S' (0, 1)) m :=
    hasDerivAt_curve (f := fun m' => (X - (1 - Q) * P * m') / P) (g := fun m' => m')
      (by rw [hCeq]; exact hS) hc (hasDerivAt_id' m)
  have hl : HasDerivAt (fun m' => 1 - N - S ((X - (1 - Q) * P * m') / P, m'))
      (-(-(1 - Q) * S' (1, 0) + 1 * S' (0, 1))) m := by
    have := hSm.const_sub (1 - N)
    convert this using 1
  have hg := hasDerivAt_curve (f := fun m' => (X - (1 - Q) * P * m') / P)
    (g := fun m' => 1 - N - S ((X - (1 - Q) * P * m') / P, m')) (by rw [hCeq, ← hL]; exact hV)
    hc hl
  have h0 := hloc.hasDerivAt_eq_zero hg
  linear_combination h0

/-- Galí (2015), Ex. 2.7(b), p. 50: combining (4) and (33) (with `V_L ≠ 0`):
`(W/P)(−S_m) = 1 − Q` **exactly**. -/
theorem shopping_rate_eq {w Q VC VL Sc Sm : ℝ} (hVL : VL ≠ 0)
    (hlab : w * (VC - VL * Sc) + -VL = 0) (hmon : -(VL * Sm) = (1 - Q) * (VC - VL * Sc)) :
    w * -Sm = 1 - Q := by
  have hUc : VC - VL * Sc ≠ 0 := by
    intro h0; rw [h0, mul_zero, zero_add, neg_eq_zero] at hlab; exact hVL hlab
  have h1 : w * (VC - VL * Sc) = VL := by linarith
  have h2 : (w * -Sm) * (VC - VL * Sc) = (1 - Q) * (VC - VL * Sc) := by
    rw [← hmon]; linear_combination (-Sm) * h1
  exact mul_right_cancel₀ hUc h2

/-- Galí (2015), p. 32: `i ↦ 1 − e^{−i}` vanishes at `0` with slope `1`, so `1 − e^{−i} ≃ i`. -/
theorem hasDerivAt_one_sub_exp_neg :
    HasDerivAt (fun i : ℝ => 1 - Real.exp (-i)) 1 0 ∧ 1 - Real.exp (-(0 : ℝ)) = 0 := by
  refine ⟨?_, by simp⟩
  have := ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)).const_sub 1
  simpa using this

/-- Galí (2015), Ex. 2.7(b), p. 50 (**precise first-order statement**): under the optimal plan
`(W/P)(−S_m) = 1 − e^{−i}`, and `|(W/P)(−S_m) − i| ≤ i²` for `|i| ≤ 1`. -/
theorem shopping_rate_approx {w Sm i : ℝ} (h : w * -Sm = 1 - Real.exp (-i)) (hi : |i| ≤ 1) :
    |w * -Sm - i| ≤ i ^ 2 := by
  have hb := Real.abs_exp_sub_one_sub_id_le (x := -i) (by rwa [abs_neg])
  rw [h, show 1 - Real.exp (-i) - i = -(Real.exp (-i) - 1 - -i) by ring, abs_neg]
  simpa using hb

/-! ### (c) Money demand -/

/-- Galí (2015), Ex. 2.7(c), p. 50 (Schmitt-Grohé and Uribe 2011): shopping time
`S(C, m) = A v + B/v − 2√(AB)` with velocity `v = C/m` (`v = P C/M`). -/
noncomputable def sguS (A B C m : ℝ) : ℝ := A * (C / m) + B / (C / m) - 2 * Real.sqrt (A * B)

/-- Galí (2015), Ex. 2.7(c): `S_m = −A C/m² + B/C`. -/
theorem hasDerivAt_S_m {A B C m : ℝ} (hC : C ≠ 0) (hm : m ≠ 0) :
    HasDerivAt (fun m' => sguS A B C m') (-(A * C / m ^ 2) + B / C) m := by
  have hfun : (fun m' => sguS A B C m') = fun m' => A * C * m'⁻¹ + B / C * m' -
      2 * Real.sqrt (A * B) := by
    funext m'
    rw [sguS]
    by_cases h0 : m' = 0
    · simp [h0]
    · field_simp
  rw [hfun]
  have := ((((hasDerivAt_inv hm).const_mul (A * C)).add
    ((hasDerivAt_id' m).const_mul (B / C))).sub_const (2 * Real.sqrt (A * B)))
  convert this using 1
  field_simp

/-- Galí (2015), Ex. 2.7(c): `S · v = (√A v − √B)²` for `A, B ≥ 0` and `v = C/m ≠ 0`. -/
theorem S_mul_v {A B C m : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hv : C / m ≠ 0) :
    sguS A B C m * (C / m) = (Real.sqrt A * (C / m) - Real.sqrt B) ^ 2 := by
  have hsq : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  have hBv : B / (C / m) * (C / m) = B := div_mul_cancel₀ B hv
  rw [sguS, hsq]
  linear_combination (-(C / m) ^ 2) * h1 + hBv - h2

/-- Galí (2015), Ex. 2.7(c): shopping time is nonnegative, `S ≥ 0` (for `A, B ≥ 0`, `v > 0`). -/
theorem S_nonneg {A B C m : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hv : 0 < C / m) :
    0 ≤ sguS A B C m := by
  have h := S_mul_v hA hB hv.ne'
  have : 0 ≤ sguS A B C m * (C / m) := by rw [h]; exact sq_nonneg _
  exact nonneg_of_mul_nonneg_left this hv

/-- Galí (2015), Ex. 2.7(c): for `A > 0`, `B ≥ 0` shopping time is zero exactly at
`v² = B/A`. -/
theorem S_eq_zero_iff {A B C m : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hv : 0 < C / m) :
    sguS A B C m = 0 ↔ (C / m) ^ 2 = B / A := by
  have h1 := Real.sq_sqrt hA.le
  have h2 := Real.sq_sqrt hB
  have hval := S_mul_v hA.le hB hv.ne'
  have hnn : 0 ≤ Real.sqrt A * (C / m) := mul_nonneg (Real.sqrt_nonneg A) hv.le
  constructor
  · intro h
    rw [h, zero_mul] at hval
    have : Real.sqrt A * (C / m) = Real.sqrt B := by
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 hval.symm
      linarith
    rw [eq_div_iff hA.ne', ← h1, ← h2, ← this]
    ring
  · intro h
    have hB' : Real.sqrt A * (C / m) = Real.sqrt B := by
      have : (Real.sqrt A * (C / m)) ^ 2 = Real.sqrt B ^ 2 := by
        rw [mul_pow, h, h1, h2]; field_simp
      exact (pow_left_inj₀ hnn (Real.sqrt_nonneg B) two_ne_zero).1 this
    rw [hB', sub_self, zero_pow two_ne_zero] at hval
    exact (mul_eq_zero.1 hval).resolve_right hv.ne'

/-- Galí (2015), Ex. 2.7(c): `S_m ≤ 0` (the book's assumption) iff `v² ≥ B/A`. -/
theorem S_m_nonpos_iff {A B C m : ℝ} (hA : 0 < A) (hC : 0 < C) (hm : 0 < m) :
    -(A * C / m ^ 2) + B / C ≤ 0 ↔ B / A ≤ (C / m) ^ 2 := by
  rw [div_le_iff₀ hA]
  constructor
  · intro h
    have : B / C ≤ A * C / m ^ 2 := by linarith
    rw [div_le_div_iff₀ hC (by positivity)] at this
    rw [div_pow]
    rw [mul_comm, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith
  · intro h
    rw [div_pow, mul_comm, ← mul_div_assoc, le_div_iff₀ (by positivity)] at h
    have : B / C ≤ A * C / m ^ 2 := by
      rw [div_le_div_iff₀ hC (by positivity)]
      nlinarith
    linarith

/-- Galí (2015), Ex. 2.7(c), p. 50 (**money demand**): if `w (−S_m) = 1 − Q` (part (b)) with
`w = W/P > 0`, `A > 0`, `C, m > 0`, then `v² = B/A + (1 − Q) C/(A w)` and
`m = C/√(B/A + (1 − Q) C/(A w))`. -/
theorem money_demand {A B C m w Q : ℝ} (hA : 0 < A) (hC : 0 < C) (hm : 0 < m) (hw : 0 < w)
    (h : w * -(-(A * C / m ^ 2) + B / C) = 1 - Q) :
    (C / m) ^ 2 = B / A + (1 - Q) * C / (A * w) ∧
      m = C / Real.sqrt (B / A + (1 - Q) * C / (A * w)) := by
  have hv : (C / m) ^ 2 = B / A + (1 - Q) * C / (A * w) := by
    rw [← h]
    field_simp
    ring
  refine ⟨hv, ?_⟩
  rw [← hv, Real.sqrt_sq (div_pos hC hm).le]
  field_simp

/-- Galí (2015), Ex. 2.7(c), p. 50: the money demand derived from part (b): if `S = sguS A B`
has derivative `S'` at `(C, m)` and `w (−S_m) = 1 − Q` with `S_m = S'(0,1)`, then
`m = C/√(B/A + (1 − Q) C/(A w))`. -/
theorem money_demand_of_hasFDerivAt {A B C m w Q : ℝ} {S' : ℝ × ℝ →L[ℝ] ℝ} (hA : 0 < A)
    (hC : 0 < C) (hm : 0 < m) (hw : 0 < w)
    (hS : HasFDerivAt (fun p : ℝ × ℝ => sguS A B p.1 p.2) S' (C, m))
    (h : w * -S' (0, 1) = 1 - Q) :
    m = C / Real.sqrt (B / A + (1 - Q) * C / (A * w)) := by
  have h1 := (hasDerivAt_sections hS).2
  have h2 := hasDerivAt_S_m (A := A) (B := B) hC.ne' hm.ne'
  rw [h1.unique h2] at h
  exact (money_demand hA hC hm hw h).2

/-- Galí (2015), Ex. 2.7(c), p. 50: money demand is strictly decreasing in the opportunity cost
`1 − Q = 1 − e^{−i}` (for `A, B, C, w > 0`, nonnegative rates). -/
theorem money_demand_strictAnti {A B C w : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hw : 0 < w) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    C / Real.sqrt (B / A + y * C / (A * w)) < C / Real.sqrt (B / A + x * C / (A * w)) := by
  have hAw : 0 < A * w := mul_pos hA hw
  have h0 : 0 < B / A + x * C / (A * w) := by positivity
  have hlt : B / A + x * C / (A * w) < B / A + y * C / (A * w) := by
    have : x * C / (A * w) < y * C / (A * w) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hxy hC) hAw
    linarith
  exact div_lt_div_of_pos_left hC (Real.sqrt_pos.2 h0) (Real.sqrt_lt_sqrt h0.le hlt)

/-- Galí (2015), Ex. 2.7(c), p. 50: at the Friedman rule (`Q = 1`, `i = 0`) velocity is
`v = √(B/A)`, the shopping-time minimum: real balances satiate at a finite level. -/
theorem money_demand_satiation {A B C m w : ℝ} (hA : 0 < A) (hC : 0 < C) (hm : 0 < m)
    (hw : 0 < w) (h : w * -(-(A * C / m ^ 2) + B / C) = 1 - 1) :
    C / m = Real.sqrt (B / A) := by
  have hv := (money_demand hA hC hm hw h).1
  rw [sub_self, zero_mul, zero_div, add_zero] at hv
  rw [← hv, Real.sqrt_sq (div_pos hC hm).le]

end Gali.ClassicalMonetaryModel.Ex2_7

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.8: a cash-in-advance economy

Galí (2015), Chapter 2, Exercise 2.8, p. 50. The household maximises
`∑ βᵗ (log C_t − N_t^{1+φ}/(1+φ))` subject to the budget constraints
`P_t C_t + Q_t B_t + M_t ≤ B_{t−1} + M_{t−1} + W_t N_t + T_t` and the cash-in-advance (CIA)
constraint `P_t C_t ≤ M_{t−1} + T_t`. Output is `Y_t = N_t`, money grows at the constant rate
`γ`, and there is no uncertainty.

**Indexing.** `M t` and `B t` denote the money and bonds carried *into* date `t` (the book's
`M_{t−1}`, `B_{t−1}`), so `Budget` reads `P_t C_t + Q_t B_{t+1} + M_{t+1} ≤ B_t + M_t + W_t N_t
+ T_t` and `CIA` reads `P_t C_t ≤ M_t + T_t`.

## (a) Optimality conditions: a KKT argument for the single inequality

`Optimal` is optimality against every feasible plan that keeps the initial holdings and agrees
with the plan from some date on (finite deviations); `optimal_of_tsum_max` shows that a plan
maximising the infinite discounted sum `∑' βᵗ U_t` is `Optimal`. Feasible perturbations give:

* `foc_labour_money` (labour today financing cash for tomorrow, two-sided):
  `N_t^φ = β W_t/(P_{t+1} C_{t+1})`;
* `foc_labour_bonds` (labour today, bonds, less labour tomorrow, two-sided):
  `Q_t N_t^φ/W_t = β N_{t+1}^φ/W_{t+1}`;
* `foc_cia_ineq` (consumption against labour today; only *decreasing* consumption is feasible
  when the CIA binds, `nonneg_of_left_max` is the one-sided Fermat rule proved by hand):
  `N_t^φ P_t/W_t ≤ 1/C_t`, with equality when the CIA is slack (`foc_cia_slack`).
* `kkt`: the multiplier form. With `λ_t = N_t^φ/W_t` and `μ_t = 1/(P_t C_t) − λ_t`:
  `1/C_t = P_t(λ_t + μ_t)`, `λ_t = β(λ_{t+1} + μ_{t+1})`, `λ_t Q_t = β λ_{t+1}`, `μ_t ≥ 0`,
  `μ_t (M_t + T_t − P_t C_t) = 0`.

**Infinite horizon, no-Ponzi and transversality.** `NoPonzi`, `OptimalNP` (overtaking
optimality against all feasible no-Ponzi plans); `optimal_of_optimalNP`;
`tvc_liminf_of_optimalNP` (necessity of transversality: rolling over debt `d` while working
`d/W_0` less); `budget_binds_of_optimal`; `overtakes_of_foc` (**sufficiency**: the conditions of
(a), a binding budget and the transversality condition imply overtaking optimality against all
no-Ponzi plans with nonnegative money).

## (b) Money growth and output

`IsEquilibrium` collects the household conditions of (a), `W = P`, `C = N` and the money
supply `M^s_t = M^s_0 (1+γ)ᵗ`; `isEquilibrium_of_optimal` shows that an optimal plan with
market clearing is one.

* `Q_le_one`: `Q_t ≤ 1` in every equilibrium; `cia_binds_of_Q_lt_one`: if `Q_t < 1` the CIA
  binds at `t+1`.
* `output_of_binding`: when the CIA binds at `t` and `t+1`, `N_t^{1+φ} = β/(1+γ)`, so
  `Y_t = (β/(1+γ))^{1/(1+φ)}` (`output_eq`), strictly decreasing in `γ`
  (`output_strictAnti`).
* `cia_binds_of_tvc`, `output_eq_of_tvc` (**every equilibrium**): with the transversality
  condition `EqTVC` (implied by household optimality, `eqTVC_of_optimalNP`), `0 < β ≤ 1` and
  `γ ≥ 0`, the CIA binds at every date and `Y_t = (β/(1+γ))^{1/(1+φ)}`.
  `slack_equilibrium_counterexample`: for `β < 1 + γ < 1` there is an equilibrium with a slack
  CIA and transversality, so `1 + γ > β` alone does not suffice.
* `stationary_isEquilibrium`: for `1 + γ ≥ β` this allocation, with `P_{t+1}/P_t = 1 + γ` and
  `Q = β/(1+γ)`, is an equilibrium.

## (c) Optimal inflation

* `stationary_utility_le`: period utility `log N − N^{1+φ}/(1+φ)` is maximised only at `N = 1`.
* `hasSum_welfare`: lifetime welfare of the stationary equilibrium is `U*/(1 − β)`.
* `optimal_inflation`: among `1 + γ ≥ β` welfare is maximised exactly at `1 + γ = β`: gross
  inflation `β`, i.e. net inflation `π = β − 1`, and `Q = 1` (`i = 0`, the Friedman rule).
-/

namespace Gali.ClassicalMonetaryModel.Ex2_8

open Filter Topology

/-- Galí (2015), Ex. 2.8, p. 50: period utility `log C − N^{1+φ}/(1+φ)`. -/
noncomputable def u (φ C N : ℝ) : ℝ := Real.log C - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 21: `d/dN [N^{1+φ}/(1+φ)] = N^φ`. -/
theorem hasDerivAt_disutil {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- **KKT for a single inequality, proved by hand** (used for Galí (2015), Ex. 2.8(a)): if
`f` has derivative `d` at `0` and `f δ ≤ f 0` for all small `δ ≤ 0` (only decreases are
feasible), then `d ≥ 0`. -/
theorem nonneg_of_left_max {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (h : ∀ᶠ δ in 𝓝 0, δ ≤ 0 → f δ ≤ f 0) : 0 ≤ d := by
  by_contra hd
  push Not at hd
  have ho := hf.isLittleO
  have hc : 0 < -d / 2 := by linarith
  have h2 := ho.def hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h.and h2)
  set δ := -(ε / 2) with hδ
  have hdist : dist δ 0 < ε := by
    rw [Real.dist_eq, hδ, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith
  obtain ⟨h1, h3⟩ := hball hdist
  have hle := h1 (by rw [hδ]; linarith)
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs] at h3
  have habs : |δ| = ε / 2 := by rw [hδ, abs_neg, abs_of_pos (by linarith)]
  rw [habs] at h3
  have := (abs_le.1 h3).1
  rw [hδ] at this
  nlinarith

/-! ### The household problem -/

/-- Galí (2015), Ex. 2.8, p. 50: the date-`t` budget constraint (with `M t`, `B t` the holdings
carried into `t`). -/
def Budget (P W Q T C N M B : ℕ → ℝ) (t : ℕ) : Prop :=
  P t * C t + Q t * B (t + 1) + M (t + 1) ≤ B t + M t + W t * N t + T t

/-- Galí (2015), Ex. 2.8, p. 50: the cash-in-advance constraint `P_t C_t ≤ M_{t−1} + T_t`. -/
def CIA (P T C M : ℕ → ℝ) (t : ℕ) : Prop := P t * C t ≤ M t + T t

/-- Galí (2015), Ex. 2.8, p. 50: a feasible plan. -/
def Feasible (P W Q T C N M B : ℕ → ℝ) : Prop :=
  ∀ t, Budget P W Q T C N M B t ∧ CIA P T C M t ∧ 0 < C t ∧ 0 ≤ N t

/-- Galí (2015), Ex. 2.8, p. 50: optimality against every feasible plan with the same initial
holdings that agrees with the plan from some date `T₀` on (finite deviations). -/
def Optimal (β φ : ℝ) (P W Q T C N M B : ℕ → ℝ) : Prop :=
  Feasible P W Q T C N M B ∧
    ∀ (C' N' M' B' : ℕ → ℝ) (T₀ : ℕ), Feasible P W Q T C' N' M' B' → M' 0 = M 0 → B' 0 = B 0 →
      (∀ s, T₀ ≤ s → C' s = C s ∧ N' s = N s ∧ M' s = M s ∧ B' s = B s) →
      ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
        ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s)

variable {β φ : ℝ} {P W Q T C N M B : ℕ → ℝ}

/-- Galí (2015), Ex. 2.8, p. 50 (**infinite horizon**): a feasible plan whose discounted
utility is summable and maximal among all feasible plans with the same initial holdings and
summable utility is `Optimal`. -/
theorem optimal_of_tsum_max (hf : Feasible P W Q T C N M B)
    (hs : Summable fun s => β ^ s * u φ (C s) (N s))
    (hmax : ∀ C' N' M' B' : ℕ → ℝ, Feasible P W Q T C' N' M' B' → M' 0 = M 0 → B' 0 = B 0 →
      Summable (fun s => β ^ s * u φ (C' s) (N' s)) →
      ∑' s, β ^ s * u φ (C' s) (N' s) ≤ ∑' s, β ^ s * u φ (C s) (N s)) :
    Optimal β φ P W Q T C N M B := by
  refine ⟨hf, fun C' N' M' B' T₀ hf' hM hB hagree => ?_⟩
  have htail : (fun s => β ^ (s + T₀) * u φ (C' (s + T₀)) (N' (s + T₀))) =
      fun s => β ^ (s + T₀) * u φ (C (s + T₀)) (N (s + T₀)) := by
    funext s
    rw [(hagree (s + T₀) (by omega)).1, (hagree (s + T₀) (by omega)).2.1]
  have hs' : Summable fun s => β ^ s * u φ (C' s) (N' s) := by
    rw [← summable_nat_add_iff T₀]
    rw [htail]
    exact (summable_nat_add_iff T₀).2 hs
  have h := hmax C' N' M' B' hf' hM hB hs'
  rw [← hs'.sum_add_tsum_nat_add T₀, ← hs.sum_add_tsum_nat_add T₀] at h
  have he : ∑' s, β ^ (s + T₀) * u φ (C' (s + T₀)) (N' (s + T₀)) =
      ∑' s, β ^ (s + T₀) * u φ (C (s + T₀)) (N (s + T₀)) := by rw [htail]
  linarith

/-- Galí (2015), Ex. 2.8(a): a feasible deviation at dates `t, t+1` (holdings changed only
for `t+1`) does not raise utility. -/
theorem gain_nonpos (hopt : Optimal β φ P W Q T C N M B) {C' N' M' B' : ℕ → ℝ} (t : ℕ)
    (hf : Feasible P W Q T C' N' M' B')
    (hCN : ∀ s, s ≠ t → s ≠ t + 1 → C' s = C s ∧ N' s = N s)
    (hMB : ∀ s, s ≠ t + 1 → M' s = M s ∧ B' s = B s) :
    β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) +
      β ^ (t + 1) * (u φ (C' (t + 1)) (N' (t + 1)) - u φ (C (t + 1)) (N (t + 1))) ≤ 0 := by
  have h := hopt.2 C' N' M' B' (t + 1 + 1) hf (hMB 0 (by omega)).1 (hMB 0 (by omega)).2
    (fun s hs => ⟨(hCN s (by omega) (by omega)).1, (hCN s (by omega) (by omega)).2,
      (hMB s (by omega)).1, (hMB s (by omega)).2⟩)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
    Finset.sum_range_succ (n := t)] at h
  have hsame : ∑ s ∈ Finset.range t, β ^ s * u φ (C' s) (N' s) =
      ∑ s ∈ Finset.range t, β ^ s * u φ (C s) (N s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    rw [(hCN s (by omega) (by omega)).1, (hCN s (by omega) (by omega)).2]
  linarith

/-- Galí (2015), Ex. 2.8(a), p. 50 (**two-sided perturbation**): working `δ` more at `t`,
holding the extra wage income as cash, and spending it at `t+1`: `N_t^φ = β W_t/(P_{t+1}
C_{t+1})`. -/
theorem foc_labour_money (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    N t ^ φ = β * W t / (P (t + 1) * C (t + 1)) := by
  have hC := fun s => (hopt.1 s).2.2.1
  set f : ℝ → ℝ := fun δ => β ^ t * (u φ (C t) (N t + δ) - u φ (C t) (N t)) +
    β ^ (t + 1) * (u φ (C (t + 1) + W t * δ / P (t + 1)) (N (t + 1)) -
      u φ (C (t + 1)) (N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc : Continuous fun δ : ℝ => C (t + 1) + W t * δ / P (t + 1) := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C (t + 1) + W t * δ / P (t + 1) :=
      (hc.tendsto 0).eventually_const_lt (by simpa using hC (t + 1))
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), -N t < δ := eventually_gt_nhds (by linarith [hN t])
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T (Function.update C (t + 1) (C (t + 1) + W t * δ / P (t + 1)))
        (Function.update N t (N t + δ)) (Function.update M (t + 1) (M (t + 1) + W t * δ)) B := by
      intro s
      obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
      have hPW : P (t + 1) * (W t * δ / P (t + 1)) = W t * δ := by
        field_simp [(hP (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;> first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas
      (fun s h1 h2 => by simp [h1, h2])
      (fun s h1 => by simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      show t + 1 ≠ t by omega, ↓reduceIte] at hg
    simp only [hfdef, add_zero, mul_zero, zero_div, sub_self, mul_zero]
    linarith
  have hd : HasDerivAt f (β ^ t * (-(N t ^ φ)) +
      β ^ (t + 1) * ((C (t + 1))⁻¹ * (W t / P (t + 1)))) 0 := by
    have hn : HasDerivAt (fun δ => u φ (C t) (N t + δ) - u φ (C t) (N t)) (-(N t ^ φ)) 0 := by
      have := ((hasDerivAt_disutil hφ (N t + 0)).comp 0 ((hasDerivAt_id' 0).const_add (N t)))
      have h2 := (this.const_sub (Real.log (C t))).sub_const (u φ (C t) (N t))
      simp only [add_zero, mul_one] at h2
      exact h2.congr_deriv (by ring)
    have hc : HasDerivAt (fun δ => u φ (C (t + 1) + W t * δ / P (t + 1)) (N (t + 1)) -
        u φ (C (t + 1)) (N (t + 1))) ((C (t + 1))⁻¹ * (W t / P (t + 1))) 0 := by
      have hin : HasDerivAt (fun δ : ℝ => C (t + 1) + W t * δ / P (t + 1)) (W t / P (t + 1)) 0 := by
        have := (((hasDerivAt_id' (0 : ℝ)).const_mul (W t)).div_const (P (t + 1))).const_add
          (C (t + 1))
        simpa using this
      have hl := (Real.hasDerivAt_log (by simpa using (hC (t + 1)).ne')).comp 0 hin
      have h2 := (hl.sub_const (N (t + 1) ^ (1 + φ) / (1 + φ))).sub_const
        (u φ (C (t + 1)) (N (t + 1)))
      simp only [mul_zero, zero_div, add_zero] at h2
      exact h2
    exact (hn.const_mul (β ^ t)).add (hc.const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * N t ^ φ = β ^ t * (β * ((C (t + 1))⁻¹ * (W t / P (t + 1)))) := by linarith
  rw [mul_left_cancel₀ hb.ne' h1]
  field_simp

/-- Galí (2015), Ex. 2.8(a), p. 50 (**two-sided perturbation**): working `δ` more at `t`,
buying bonds with the income and working less at `t+1`:
`Q_t N_t^φ/W_t = β N_{t+1}^φ/W_{t+1}` (`λ_t Q_t = β λ_{t+1}`). -/
theorem foc_labour_bonds (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hW : ∀ t, 0 < W t) (hQ : ∀ t, 0 < Q t) (t : ℕ) :
    Q t * N t ^ φ / W t = β * N (t + 1) ^ φ / W (t + 1) := by
  set k := W t / (Q t * W (t + 1)) with hk
  set f : ℝ → ℝ := fun δ => β ^ t * (u φ (C t) (N t + δ) - u φ (C t) (N t)) +
    β ^ (t + 1) * (u φ (C (t + 1)) (N (t + 1) - k * δ) - u φ (C (t + 1)) (N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc : Continuous fun δ : ℝ => N (t + 1) - k * δ := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N (t + 1) - k * δ :=
      (hc.tendsto 0).eventually_const_lt (by simpa using hN (t + 1))
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), -N t < δ := eventually_gt_nhds (by linarith [hN t])
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T C
        (Function.update (Function.update N t (N t + δ)) (t + 1) (N (t + 1) - k * δ)) M
        (Function.update B (t + 1) (B (t + 1) + W t * δ / Q t)) := by
      intro s
      obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
      have hQW1 : Q t * (W t * δ / Q t) = W t * δ := by field_simp [(hQ t).ne']
      have hQW2 : W (t + 1) * (k * δ) = W t * δ / Q t := by
        rw [hk]; field_simp [(hQ t).ne', (hW (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;> first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas
      (fun s h1 h2 => by simp [h1, h2])
      (fun s h1 => by simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      ↓reduceIte] at hg
    simp only [hfdef, add_zero, mul_zero, sub_zero, sub_self]
    linarith
  have hd : HasDerivAt f (β ^ t * (-(N t ^ φ)) + β ^ (t + 1) * (-(N (t + 1) ^ φ) * -k)) 0 := by
    have hn : HasDerivAt (fun δ => u φ (C t) (N t + δ) - u φ (C t) (N t)) (-(N t ^ φ)) 0 := by
      have := ((hasDerivAt_disutil hφ (N t + 0)).comp 0 ((hasDerivAt_id' 0).const_add (N t)))
      have h2 := (this.const_sub (Real.log (C t))).sub_const (u φ (C t) (N t))
      simp only [add_zero, mul_one] at h2
      exact h2.congr_deriv (by ring)
    have hm : HasDerivAt (fun δ => u φ (C (t + 1)) (N (t + 1) - k * δ) -
        u φ (C (t + 1)) (N (t + 1))) (-(N (t + 1) ^ φ) * -k) 0 := by
      have hin : HasDerivAt (fun δ : ℝ => N (t + 1) - k * δ) (-k) 0 := by
        have := ((hasDerivAt_id' (0 : ℝ)).const_mul k).const_sub (N (t + 1))
        simpa using this
      have := (hasDerivAt_disutil hφ (N (t + 1) - k * 0)).comp 0 hin
      have h2 := (this.const_sub (Real.log (C (t + 1)))).sub_const (u φ (C (t + 1)) (N (t + 1)))
      simp only [mul_zero, sub_zero] at h2
      exact h2.congr_deriv (by ring)
    exact (hn.const_mul (β ^ t)).add (hm.const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * N t ^ φ = β ^ t * (β * N (t + 1) ^ φ * k) := by linarith
  have h2 := mul_left_cancel₀ hb.ne' h1
  rw [hk] at h2
  rw [h2]
  field_simp [(hQ t).ne', (hW t).ne', (hW (t + 1)).ne']

/-- Galí (2015), Ex. 2.8(a): the consumption–labour perturbation at date `t`
(`C_t + δ`, `N_t + P_t δ/W_t`) is feasible whenever the CIA still holds and the levels stay
admissible. -/
theorem cia_family_feasible (hopt : Optimal β φ P W Q T C N M B) (hW : ∀ t, 0 < W t)
    {t : ℕ} {δ : ℝ} (h1 : 0 < C t + δ) (h2 : 0 ≤ N t + P t * δ / W t)
    (h3 : P t * (C t + δ) ≤ M t + T t) :
    Feasible P W Q T (Function.update C t (C t + δ)) (Function.update N t (N t + P t * δ / W t))
      M B := by
  intro s
  obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
  have hPW : W t * (P t * δ / W t) = P t * δ := by field_simp [(hW t).ne']
  simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;> first | omega | nlinarith

/-- Galí (2015), Ex. 2.8(a): the utility gain of the consumption–labour perturbation and its
derivative `β^t (1/C_t − N_t^φ P_t/W_t)` at `δ = 0`. -/
theorem hasDerivAt_cia_family {t : ℕ} (hφ : 0 ≤ φ) (hC : 0 < C t) :
    HasDerivAt (fun δ => β ^ t * (u φ (C t + δ) (N t + P t * δ / W t) - u φ (C t) (N t)))
      (β ^ t * ((C t)⁻¹ - N t ^ φ * (P t / W t))) 0 := by
  have hin : HasDerivAt (fun δ : ℝ => N t + P t * δ / W t) (P t / W t) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_mul (P t)).div_const (W t)).const_add (N t)
    simpa using this
  have hl : HasDerivAt (fun δ : ℝ => Real.log (C t + δ)) (C t + 0)⁻¹ 0 :=
    (Real.hasDerivAt_log (by simpa using hC.ne')).comp 0 ((hasDerivAt_id' 0).const_add (C t))
      |>.congr_deriv (by simp)
  have hd := (hasDerivAt_disutil hφ (N t + P t * 0 / W t)).comp 0 hin
  simp only [mul_zero, zero_div, add_zero] at hl hd
  have := ((HasDerivAt.sub hl hd).sub_const (u φ (C t) (N t))).const_mul (β ^ t)
  exact this

/-- Galí (2015), Ex. 2.8(a), p. 50 (**KKT, the inequality**): only *lower* consumption is
always feasible under the CIA, so `N_t^φ P_t/W_t ≤ 1/C_t`. -/
theorem foc_cia_ineq (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) (t : ℕ) :
    N t ^ φ * P t / W t ≤ 1 / C t := by
  have hC := (hopt.1 t).2.2.1
  have hcia := (hopt.1 t).2.1
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C t + δ :=
    (eventually_gt_nhds (show -C t < (0 : ℝ) by linarith)).mono fun δ h => by linarith
  have hc : Continuous fun δ : ℝ => N t + P t * δ / W t := by fun_prop
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N t + P t * δ / W t :=
    (hc.tendsto 0).eventually_const_lt (by simpa using hN t)
  have hleft : ∀ᶠ δ in 𝓝 (0 : ℝ), δ ≤ 0 →
      β ^ t * (u φ (C t + δ) (N t + P t * δ / W t) - u φ (C t) (N t)) ≤
        β ^ t * (u φ (C t + 0) (N t + P t * 0 / W t) - u φ (C t) (N t)) := by
    filter_upwards [e1, e2] with δ h1 h2 hδ
    have h3 : P t * (C t + δ) ≤ M t + T t := by
      simp only [CIA] at hcia; nlinarith [hP t]
    have hg := gain_nonpos hopt t (cia_family_feasible hopt hW h1 h2.le h3)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [mul_zero, zero_div, add_zero, sub_self, mul_zero]
    exact hg
  have h0 := nonneg_of_left_max (hasDerivAt_cia_family (β := β) (P := P) (W := W) hφ hC) hleft
  have h1 : 0 ≤ (C t)⁻¹ - N t ^ φ * (P t / W t) :=
    nonneg_of_mul_nonneg_right (by linarith) (pow_pos hβ t)
  rw [mul_div_assoc, one_div]
  linarith

/-- Galí (2015), Ex. 2.8(a), p. 50 (**KKT, complementary slackness**): if the CIA is slack at
`t`, the perturbation is feasible in both directions and `N_t^φ P_t/W_t = 1/C_t`. -/
theorem foc_cia_slack (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hW : ∀ t, 0 < W t) {t : ℕ} (hslack : P t * C t < M t + T t) :
    N t ^ φ * P t / W t = 1 / C t := by
  have hC := (hopt.1 t).2.2.1
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C t + δ :=
    (eventually_gt_nhds (show -C t < (0 : ℝ) by linarith)).mono fun δ h => by linarith
  have hc : Continuous fun δ : ℝ => N t + P t * δ / W t := by fun_prop
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N t + P t * δ / W t :=
    (hc.tendsto 0).eventually_const_lt (by simpa using hN t)
  have hc3 : Continuous fun δ : ℝ => P t * (C t + δ) := by fun_prop
  have e3 : ∀ᶠ δ in 𝓝 (0 : ℝ), P t * (C t + δ) < M t + T t :=
    (hc3.tendsto 0).eventually_lt_const (by simpa using hslack)
  have hloc : IsLocalMax (fun δ => β ^ t * (u φ (C t + δ) (N t + P t * δ / W t) -
      u φ (C t) (N t))) 0 := by
    filter_upwards [e1, e2, e3] with δ h1 h2 h3
    have hg := gain_nonpos hopt t (cia_family_feasible hopt hW h1 h2.le h3.le)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [mul_zero, zero_div, add_zero, sub_self, mul_zero]
    exact hg
  have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_cia_family hφ hC)
  have h1 : (C t)⁻¹ - N t ^ φ * (P t / W t) = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_pos hβ t).ne'
  rw [mul_div_assoc, one_div]
  linarith

/-- Galí (2015), Ex. 2.8(a), p. 50 (**KKT multipliers**): with `λ_t = N_t^φ/W_t` (budget) and
`μ_t = 1/(P_t C_t) − λ_t` (CIA): `1/C_t = P_t(λ_t + μ_t)`, `λ_t = β(λ_{t+1} + μ_{t+1})` (money),
`λ_t Q_t = β λ_{t+1}` (bonds), `μ_t ≥ 0`, and `μ_t (M_t + T_t − P_t C_t) = 0`. -/
theorem kkt (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) (hQ : ∀ t, 0 < Q t) :
    ∃ lam mu : ℕ → ℝ, (∀ t, lam t = N t ^ φ / W t) ∧
      (∀ t, 1 / C t = P t * (lam t + mu t)) ∧ (∀ t, lam t = β * (lam (t + 1) + mu (t + 1))) ∧
      (∀ t, lam t * Q t = β * lam (t + 1)) ∧ (∀ t, 0 ≤ mu t) ∧
      (∀ t, mu t * (M t + T t - P t * C t) = 0) := by
  have hC := fun t => (hopt.1 t).2.2.1
  refine ⟨fun t => N t ^ φ / W t, fun t => 1 / (P t * C t) - N t ^ φ / W t, fun _ => rfl,
    fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · field_simp [(hP t).ne', (hC t).ne']
    ring
  · simp only [add_sub_cancel]
    rw [foc_labour_money hopt hβ hφ hN hP t]
    field_simp [(hW t).ne']
  · rw [mul_comm, ← mul_div_assoc, foc_labour_bonds hopt hβ hφ hN hW hQ t, mul_div_assoc]
  · have := foc_cia_ineq hopt hβ hφ hN hP hW t
    have h2 : N t ^ φ / W t ≤ 1 / (P t * C t) := by
      rw [div_le_div_iff₀ (hW t) (mul_pos (hP t) (hC t))]
      rw [div_le_div_iff₀ (hW t) (hC t)] at this
      nlinarith
    linarith
  · rcases (hopt.1 t).2.1.lt_or_eq with hlt | heq
    · have := foc_cia_slack hopt hβ hφ hN hW hlt
      have h2 : 1 / (P t * C t) - N t ^ φ / W t = 0 := by
        rw [div_eq_div_iff (hW t).ne' (hC t).ne'] at this
        field_simp [(hP t).ne', (hC t).ne', (hW t).ne']
        linarith
      change (1 / (P t * C t) - N t ^ φ / W t) * (M t + T t - P t * C t) = 0
      rw [h2, zero_mul]
    · rw [heq, sub_self, mul_zero]

/-! ### No-Ponzi, overtaking optimality and transversality -/

/-- Galí (2015), p. 19 (ch. 2 notation): the date-0 price `∏_{s<T} Q_s` of one unit of money
delivered at date `T`. -/
noncomputable def disc (Q : ℕ → ℝ) (T : ℕ) : ℝ := ∏ s ∈ Finset.range T, Q s

/-- Galí (2015), p. 19: `disc Q (s+1) = disc Q s · Q_s`. -/
theorem disc_succ (Q : ℕ → ℝ) (s : ℕ) : disc Q (s + 1) = disc Q s * Q s :=
  Finset.prod_range_succ _ _

/-- Galí (2015), p. 19: discount factors are positive when bond prices are. -/
theorem disc_pos {Q : ℕ → ℝ} (hQ : ∀ t, 0 < Q t) (T : ℕ) : 0 < disc Q T :=
  Finset.prod_pos fun s _ => hQ s

/-- Galí (2015), eq. (3), p. 19, for Ex. 2.8: the no-Ponzi condition on total financial wealth
`B_T + M_T` carried into `T`, `liminf_T disc_T (B_T + M_T) ≥ 0`. -/
def NoPonzi (Q M B : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ disc Q T * (B T + M T)

/-- Galí (2015), eqs. (1)–(3), pp. 18–19, for Ex. 2.8: optimality in the overtaking sense
against every feasible plan satisfying the no-Ponzi condition (the infinite-horizon problem;
deviations need not be finite). -/
def OptimalNP (β φ : ℝ) (P W Q T C N M B : ℕ → ℝ) : Prop :=
  (Feasible P W Q T C N M B ∧ NoPonzi Q M B) ∧
    ∀ C' N' M' B' : ℕ → ℝ, Feasible P W Q T C' N' M' B' → NoPonzi Q M' B' → M' 0 = M 0 →
      B' 0 = B 0 → ∀ ε > 0, ∀ᶠ T₀ in atTop,
        ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
          ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s) + ε

/-- Galí (2015), Ex. 2.8(a): an overtaking-optimal plan is optimal against finite deviations,
so all the first-order conditions of (a) apply to it. -/
theorem optimal_of_optimalNP (hopt : OptimalNP β φ P W Q T C N M B) :
    Optimal β φ P W Q T C N M B := by
  refine ⟨hopt.1.1, fun C' N' M' B' T₀ hf hM hB hagree => ?_⟩
  have hNP : NoPonzi Q M' B' := fun ε hε => by
    filter_upwards [hopt.1.2 ε hε, eventually_ge_atTop T₀] with T h1 h2
    rw [(hagree T h2).2.2.1, (hagree T h2).2.2.2]
    exact h1
  have key : ∀ ε > 0, ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
      ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s) + ε := by
    intro ε hε
    obtain ⟨T₁, hT₁⟩ := ((hopt.2 C' N' M' B' hf hNP hM hB ε hε).and
      (eventually_ge_atTop T₀)).exists
    have htail : ∑ s ∈ Finset.Ico T₀ T₁, β ^ s * u φ (C' s) (N' s) =
        ∑ s ∈ Finset.Ico T₀ T₁, β ^ s * u φ (C s) (N s) :=
      Finset.sum_congr rfl fun s hs => by
        rw [(hagree s (Finset.mem_Ico.1 hs).1).1, (hagree s (Finset.mem_Ico.1 hs).1).2.1]
    have h1 := hT₁.1
    rw [← Finset.sum_range_add_sum_Ico _ hT₁.2, ← Finset.sum_range_add_sum_Ico _ hT₁.2,
      htail] at h1
    linarith
  by_contra hcon
  push Not at hcon
  have := key _ (half_pos (sub_pos.2 hcon))
  linarith

/-- Galí (2015), p. 20 and eq. (6), p. 19, for Ex. 2.8 (**necessity of transversality**): at an
overtaking-optimal plan the no-Ponzi condition cannot hold strictly. If the discounted wealth
stayed above `L > 0`, the household could work `d/W_0` less at date 0 and roll the debt `d`
over forever. Hence `disc_T (B_T + M_T) < L` for infinitely many `T`. -/
theorem tvc_liminf_of_optimalNP (hopt : OptimalNP β φ P W Q T C N M B) (hφ : 0 ≤ φ)
    (hQ : ∀ t, 0 < Q t) (hW : 0 < W 0) (hN : 0 < N 0) {L : ℝ} (hL : 0 < L) :
    ∃ᶠ T in atTop, disc Q T * (B T + M T) < L := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set d := min L (W 0 * N 0) with hd
  have hd0 : 0 < d := lt_min hL (mul_pos hW hN)
  have hdL : d ≤ L := min_le_left _ _
  have hdW : d ≤ W 0 * N 0 := min_le_right _ _
  have hN' : 0 ≤ N 0 - d / W 0 := by
    rw [sub_nonneg, div_le_iff₀ hW]; linarith
  have hNlt : N 0 - d / W 0 < N 0 := by
    have := div_pos hd0 hW; linarith
  set N' := Function.update N 0 (N 0 - d / W 0) with hN'def
  set B' : ℕ → ℝ := fun s => if s = 0 then B 0 else B s - d / disc Q s with hB'def
  have hdisc := disc_pos hQ
  have hfeas : Feasible P W Q T C N' M B' := by
    intro s
    obtain ⟨hb, hc, hCp, hNp⟩ := hopt.1.1 s
    refine ⟨?_, hc, hCp, ?_⟩
    · simp only [Budget] at hb ⊢
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp only [hB'def, hN'def, Function.update_self, show (0 + 1 : ℕ) ≠ 0 by omega,
          ↓reduceIte]
        have e1 : Q 0 * (B (0 + 1) - d / disc Q (0 + 1)) = Q 0 * B (0 + 1) - d := by
          rw [disc_succ, show disc Q 0 = 1 from Finset.prod_range_zero _, one_mul]
          field_simp [(hQ 0).ne']
        have e2 : W 0 * (N 0 - d / W 0) = W 0 * N 0 - d := by field_simp [hW.ne']
        rw [e1, e2]
        linarith
      · simp only [hB'def, hN'def, Function.update_of_ne (show s ≠ 0 by omega),
          show s + 1 ≠ 0 by omega, show s ≠ 0 by omega, ↓reduceIte]
        have e1 : Q s * (B (s + 1) - d / disc Q (s + 1)) = Q s * B (s + 1) - d / disc Q s := by
          rw [disc_succ]
          field_simp [(hQ s).ne', (hdisc s).ne']
        rw [e1]
        linarith
    · by_cases hs : s = 0
      · subst hs; simp only [hN'def, Function.update_self]; exact hN'
      · simp only [hN'def, Function.update_of_ne hs]; exact hNp
  have hNP : NoPonzi Q M B' := fun ε hε => by
    filter_upwards [hcon, eventually_ge_atTop 1] with T hT hT1
    push Not at hT
    simp only [hB'def, show T ≠ 0 by omega, ↓reduceIte]
    rw [show disc Q T * (B T - d / disc Q T + M T) = disc Q T * (B T + M T) - d by
      field_simp [(hdisc T).ne']; ring]
    linarith
  have hG : 0 < u φ (C 0) (N 0 - d / W 0) - u φ (C 0) (N 0) := by
    have := Real.rpow_lt_rpow hN' hNlt (by linarith : (0 : ℝ) < 1 + φ)
    have h1 : (0 : ℝ) < 1 + φ := by linarith
    simp only [u]
    have : (N 0 - d / W 0) ^ (1 + φ) / (1 + φ) < N 0 ^ (1 + φ) / (1 + φ) :=
      div_lt_div_of_pos_right this h1
    linarith
  set G := u φ (C 0) (N 0 - d / W 0) - u φ (C 0) (N 0) with hGdef
  obtain ⟨T₁, hT₁⟩ := ((hopt.2 C N' M B' hfeas hNP rfl (by simp [hB'def]) (G / 2)
    (half_pos hG)).and (eventually_ge_atTop 1)).exists
  have h1 := hT₁.1
  obtain ⟨k, hk⟩ : ∃ k, T₁ = k + 1 := ⟨T₁ - 1, by omega⟩
  rw [hk, Finset.sum_range_succ', Finset.sum_range_succ'] at h1
  have hsame : ∑ s ∈ Finset.range k, β ^ (s + 1) * u φ (C (s + 1)) (N' (s + 1)) =
      ∑ s ∈ Finset.range k, β ^ (s + 1) * u φ (C (s + 1)) (N (s + 1)) :=
    Finset.sum_congr rfl fun s _ => by
      rw [hN'def, Function.update_of_ne (show s + 1 ≠ 0 by omega)]
  rw [hsame, hN'def, Function.update_self] at h1
  simp only [pow_zero, one_mul] at h1
  linarith

/-! ### (a) Sufficiency of the first-order conditions -/

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its tangent
lines (restated from the Chapter 3 project; concavity for Galí (2015), Ex. 2.8(a)). -/
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

/-- Galí (2015), Ex. 2.8(a): concavity of `u`, in tangent form
`u(C', N') ≤ u(C, N) + (C' − C)/C − N^φ (N' − N)` for `C, C', N > 0`, `N' ≥ 0`. -/
theorem u_le_tangent (hφ : 0 ≤ φ) {C N C' N' : ℝ} (hC : 0 < C) (hN : 0 < N) (hC' : 0 < C')
    (hN' : 0 ≤ N') : u φ C' N' ≤ u φ C N + (C' - C) / C - N ^ φ * (N' - N) := by
  have hlog : Real.log C' ≤ Real.log C + (C' - C) / C := by
    have h := Real.log_le_sub_one_of_pos (div_pos hC' hC)
    rw [Real.log_div hC'.ne' hC.ne'] at h
    have : C' / C - 1 = (C' - C) / C := by field_simp
    linarith
  have hv : N ^ (1 + φ) / (1 + φ) + N ^ φ * (N' - N) ≤ N' ^ (1 + φ) / (1 + φ) := by
    have h := le_tangent (f := fun x => -(x ^ (1 + φ) / (1 + φ))) (f' := fun x => -x ^ φ) hN hN'
      (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
        (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutil hφ z).neg)
      (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
    linarith
  unfold u
  linarith

/-- Galí (2015), Ex. 2.8(a): the discounted budget multiplier `Λ_t = βᵗ N_t^φ/W_t`
(`= βᵗ λ_t`). -/
noncomputable def lamD (β φ : ℝ) (W N : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * N t ^ φ / W t

/-- Galí (2015), Ex. 2.8(a): the discounted CIA multiplier `βᵗ/(P_t C_t) − Λ_t` (`= βᵗ μ_t`). -/
noncomputable def muD (β φ : ℝ) (P W C N : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t / (P t * C t) - lamD β φ W N t

/-- Galí (2015), Ex. 2.8(a): an optimal plan exhausts its budget at every date where hours are
positive (otherwise working less would be feasible and better). -/
theorem budget_binds_of_optimal (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β)
    (hφ : 0 ≤ φ) (hW : ∀ t, 0 < W t) {t : ℕ} (hN : 0 < N t) :
    P t * C t + Q t * B (t + 1) + M (t + 1) = B t + M t + W t * N t + T t := by
  by_contra hne
  have hlt := lt_of_le_of_ne (hopt.1 t).1 hne
  set sl := B t + M t + W t * N t + T t - (P t * C t + Q t * B (t + 1) + M (t + 1)) with hsl
  have hsl0 : 0 < sl := by rw [hsl]; linarith
  set δ := min (N t / 2) (sl / (2 * W t)) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos hsl0 (by linarith [hW t]))
  have hδN : δ ≤ N t / 2 := min_le_left _ _
  have hδs : δ ≤ sl / (2 * W t) := min_le_right _ _
  have hWδ : W t * δ ≤ sl / 2 := by
    have := mul_le_mul_of_nonneg_left hδs (hW t).le
    rw [show W t * (sl / (2 * W t)) = sl / 2 by field_simp [(hW t).ne']] at this
    exact this
  have hfeas : Feasible P W Q T C (Function.update N t (N t - δ)) M B := by
    intro s
    obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
    simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
    refine ⟨?_, hc', hCp, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
      first | omega | nlinarith
  have hg := gain_nonpos hopt t hfeas (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
  simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
    ↓reduceIte, sub_self, mul_zero, add_zero] at hg
  have hlt2 : (N t - δ) ^ (1 + φ) < N t ^ (1 + φ) :=
    Real.rpow_lt_rpow (by linarith) (by linarith) (by linarith)
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have h3 : (N t - δ) ^ (1 + φ) / (1 + φ) < N t ^ (1 + φ) / (1 + φ) :=
    div_lt_div_of_pos_right hlt2 h1
  have hpos : 0 < β ^ t * (u φ (C t) (N t - δ) - u φ (C t) (N t)) := by
    refine mul_pos (pow_pos hβ t) ?_
    simp only [u]
    linarith
  linarith

/-- Galí (2015), Ex. 2.8(a) (**sufficiency of the first-order conditions**): let a feasible
plan with positive hours, prices and wages exhaust its budget and satisfy the
conditions of (a) — the labour–money condition, the bond condition, the KKT inequality with
complementary slackness — and the transversality condition
`disc_{k+1} B_{k+1} + disc_k M_{k+1} → 0`. Then it overtakes every feasible no-Ponzi plan with
the same initial holdings and nonnegative money holdings. The proof is the Lagrangian
argument: concavity gives a per-period bound, the multipliers telescope the budgets, and what
remains is the transversality term of the plan minus the no-Ponzi term of the competitor. -/
theorem overtakes_of_foc (hβ : 0 < β) (hφ : 0 ≤ φ) (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t)
    (hW : ∀ t, 0 < W t) (hfeas : Feasible P W Q T C N M B)
    (hbind : ∀ t, P t * C t + Q t * B (t + 1) + M (t + 1) = B t + M t + W t * N t + T t)
    (hI : ∀ t, N t ^ φ = β * W t / (P (t + 1) * C (t + 1)))
    (hII : ∀ t, Q t * N t ^ φ / W t = β * N (t + 1) ^ φ / W (t + 1))
    (hIII : ∀ t, N t ^ φ * P t / W t ≤ 1 / C t)
    (hsl : ∀ t, P t * C t < M t + T t → N t ^ φ * P t / W t = 1 / C t)
    (htvc : ∀ ε > 0, ∀ᶠ k in atTop, disc Q (k + 1) * B (k + 1) + disc Q k * M (k + 1) ≤ ε)
    {C' N' M' B' : ℕ → ℝ} (hf' : Feasible P W Q T C' N' M' B') (hnp' : NoPonzi Q M' B')
    (hM' : ∀ t, 0 ≤ M' t) (hM0 : M' 0 = M 0) (hB0 : B' 0 = B 0) :
    ∀ ε > 0, ∀ᶠ T₀ in atTop, ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
      ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s) + ε := by
  have hC : ∀ t, 0 < C t := fun t => (hfeas t).2.2.1
  set Λ := lamD β φ W N with hΛ
  set Mu := muD β φ P W C N with hMu
  -- multiplier identities
  have hΛQ : ∀ t, Λ t * Q t = Λ (t + 1) := by
    intro t
    calc Λ t * Q t = β ^ t * (Q t * N t ^ φ / W t) := by simp only [hΛ, lamD]; ring
      _ = β ^ t * (β * N (t + 1) ^ φ / W (t + 1)) := by rw [hII t]
      _ = Λ (t + 1) := by simp only [hΛ, lamD, pow_succ]; ring
  have hΛMu : ∀ t, Λ t = Λ (t + 1) + Mu (t + 1) := by
    intro t
    simp only [hMu, muD, hΛ, add_sub_cancel, lamD, hI t, pow_succ]
    field_simp [(hW t).ne', (hP (t + 1)).ne', (hC (t + 1)).ne']
  have hΛpos : ∀ t, 0 < Λ t := fun t =>
    div_pos (mul_pos (pow_pos hβ t) (Real.rpow_pos_of_pos (hN t) φ)) (hW t)
  have hMu0 : ∀ t, 0 ≤ Mu t := by
    intro t
    have h3 := hIII t
    have e1 : β ^ t * N t ^ φ / W t = (β ^ t / P t) * (N t ^ φ * P t / W t) := by
      field_simp [(hP t).ne', (hW t).ne']
    have e2 : β ^ t / (P t * C t) = (β ^ t / P t) * (1 / C t) := by
      field_simp [(hP t).ne', (hC t).ne']
    simp only [hMu, muD, lamD, sub_nonneg]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h3 (div_nonneg (pow_pos hβ t).le (hP t).le)
  have hΛdisc : ∀ t, Λ t = Λ 0 * disc Q t := by
    intro t
    induction t with
    | zero => simp [disc]
    | succ t ih => rw [← hΛQ t, ih, disc_succ]; ring
  -- per-period bound
  have hper : ∀ t, β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) ≤
      Λ t * ((B' t - B t) + (M' t - M t) - Q t * (B' (t + 1) - B (t + 1)) -
        (M' (t + 1) - M (t + 1))) + Mu t * (M' t - M t) := by
    intro t
    obtain ⟨hb', hc', hC't, hN't⟩ := hf' t
    have hcon := u_le_tangent hφ (hC t) (hN t) hC't hN't
    have e1 : β ^ t / C t = P t * (Λ t + Mu t) := by
      simp only [hMu, muD, hΛ, add_sub_cancel]; field_simp [(hP t).ne']
    have e2 : β ^ t * N t ^ φ = W t * Λ t := by
      simp only [hΛ, lamD]; field_simp [(hW t).ne']
    have hcon2 : β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) ≤
        P t * (Λ t + Mu t) * (C' t - C t) - W t * Λ t * (N' t - N t) := by
      have := mul_le_mul_of_nonneg_left (show u φ (C' t) (N' t) - u φ (C t) (N t) ≤
        (C' t - C t) / C t - N t ^ φ * (N' t - N t) by linarith) (pow_pos hβ t).le
      rw [← e1, ← e2]
      calc _ ≤ _ := this
        _ = _ := by ring
    have hbud : P t * (C' t - C t) - W t * (N' t - N t) ≤ (B' t - B t) + (M' t - M t) -
        Q t * (B' (t + 1) - B (t + 1)) - (M' (t + 1) - M (t + 1)) := by
      simp only [Budget] at hb'
      linarith [hbind t]
    have hcia : Mu t * (P t * (C' t - C t)) ≤ Mu t * (M' t - M t) := by
      rcases (hfeas t).2.1.lt_or_eq with hlt | heq
      · have hz : Mu t = 0 := by
          have := hsl t hlt
          have e1 : β ^ t * N t ^ φ / W t = (β ^ t / P t) * (N t ^ φ * P t / W t) := by
            field_simp [(hP t).ne', (hW t).ne']
          have e2 : β ^ t / (P t * C t) = (β ^ t / P t) * (1 / C t) := by
            field_simp [(hP t).ne', (hC t).ne']
          simp only [hMu, muD, lamD]
          rw [e1, e2, this, sub_self]
        rw [hz, zero_mul, zero_mul]
      · simp only [CIA] at hc'
        exact mul_le_mul_of_nonneg_left (by linarith) (hMu0 t)
    nlinarith [mul_le_mul_of_nonneg_left hbud (hΛpos t).le]
  -- telescoping
  have htel : ∀ T₀, ∑ t ∈ Finset.range T₀, (Λ t * ((B' t - B t) + (M' t - M t) -
      Q t * (B' (t + 1) - B (t + 1)) - (M' (t + 1) - M (t + 1))) + Mu t * (M' t - M t)) =
      -(Λ T₀ * (B' T₀ - B T₀)) - (Λ T₀ + Mu T₀) * (M' T₀ - M T₀) := by
    intro T₀
    induction T₀ with
    | zero => simp [hM0, hB0]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      linear_combination (-(B' (k + 1) - B (k + 1))) * hΛQ k +
        (-(M' (k + 1) - M (k + 1))) * hΛMu k
  intro ε hε
  have hΛ0 := hΛpos 0
  have hε2 : 0 < ε / (2 * Λ 0) := div_pos hε (by linarith)
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually (htvc _ hε2), hnp' _ hε2,
    eventually_ge_atTop 1] with T₀ h1 h2 h3
  obtain ⟨k, rfl⟩ : ∃ k, T₀ = k + 1 := ⟨T₀ - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (k + 1)) => hper t
  rw [htel] at hsum
  have hdiff : ∑ s ∈ Finset.range (k + 1), β ^ s * u φ (C' s) (N' s) -
      ∑ s ∈ Finset.range (k + 1), β ^ s * u φ (C s) (N s) =
      ∑ t ∈ Finset.range (k + 1), β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hk := hΛMu k
  have hMuM : 0 ≤ Mu (k + 1) * M' (k + 1) := mul_nonneg (hMu0 _) (hM' _)
  have ha := mul_le_mul_of_nonneg_left h1 hΛ0.le
  have hb := mul_le_mul_of_nonneg_left h2 hΛ0.le
  have hc : Λ 0 * (ε / (2 * Λ 0)) = ε / 2 := by field_simp
  rw [hc] at ha
  rw [mul_neg, hc] at hb
  have e1 := hΛdisc (k + 1)
  have e2 := hΛdisc k
  have hx : Λ (k + 1) * B (k + 1) + (Λ (k + 1) + Mu (k + 1)) * M (k + 1) =
      Λ 0 * (disc Q (k + 1) * B (k + 1) + disc Q k * M (k + 1)) := by
    rw [← hk, e1, e2]; ring
  have hy : Λ (k + 1) * (B' (k + 1) + M' (k + 1)) =
      Λ 0 * (disc Q (k + 1) * (B' (k + 1) + M' (k + 1))) := by rw [e1]; ring
  nlinarith

/-! #**Infinite horizon, no-Ponzi and transversality.** `NoPonzi`, `OptimalNP` (overtaking
optimality against all feasible no-Ponzi plans); `optimal_of_optimalNP`;
`tvc_liminf_of_optimalNP` (necessity of transversality: rolling over debt `d` while working
`d/W_0` less); `budget_binds_of_optimal`; `overtakes_of_foc` (**sufficiency**: the conditions of
(a), a binding budget and the transversality condition imply overtaking optimality against all
no-Ponzi plans with nonnegative money).

## (b) Money growth and output -/

variable (β φ γ Ms₀ : ℝ) (C N P W Q Ms : ℕ → ℝ)

/-- Galí (2015), Ex. 2.8(b), p. 50: an equilibrium. The household conditions of (a) (`kkt`),
competitive firms `W = P` (`Y = N`), goods-market clearing `C = N`, and money
`M^s_t = M^s_0 (1+γ)ᵗ` held for purchases at `t` (`M_{t−1} + T_t = M^s_t`). -/
structure IsEquilibrium where
  /-- Positive consumption. -/
  pos_C : ∀ t, 0 < C t
  /-- Positive hours. -/
  pos_N : ∀ t, 0 < N t
  /-- Positive prices. -/
  pos_P : ∀ t, 0 < P t
  /-- Labour–money condition `N_t^φ = β W_t/(P_{t+1} C_{t+1})`. -/
  focI : ∀ t, N t ^ φ = β * W t / (P (t + 1) * C (t + 1))
  /-- Bond condition `Q_t N_t^φ/W_t = β N_{t+1}^φ/W_{t+1}`. -/
  focII : ∀ t, Q t * N t ^ φ / W t = β * N (t + 1) ^ φ / W (t + 1)
  /-- KKT inequality `N_t^φ P_t/W_t ≤ 1/C_t`. -/
  focIII : ∀ t, N t ^ φ * P t / W t ≤ 1 / C t
  /-- Complementary slackness. -/
  slack : ∀ t, P t * C t < Ms t → N t ^ φ * P t / W t = 1 / C t
  /-- The CIA constraint. -/
  cia : ∀ t, P t * C t ≤ Ms t
  /-- Competitive firm with `Y = N`: `W = P`. -/
  firm : ∀ t, W t = P t
  /-- Goods-market clearing `C = Y = N`. -/
  clearing : ∀ t, C t = N t
  /-- Constant money growth. -/
  money : ∀ t, Ms t = Ms₀ * (1 + γ) ^ t

variable {β φ γ Ms₀ C N P W Q Ms}

/-- Galí (2015), Ex. 2.8(b): an optimal household plan (with positive hours, prices, wages
and bond prices) at market-clearing prices is an equilibrium. -/
theorem isEquilibrium_of_optimal {T M B : ℕ → ℝ} (hopt : Optimal β φ P W Q T C N M B)
    (hβ : 0 < β) (hφ : 0 ≤ φ) (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hMT : ∀ t, M t + T t = Ms t) (hfirm : ∀ t, W t = P t) (hclear : ∀ t, C t = N t)
    (hmoney : ∀ t, Ms t = Ms₀ * (1 + γ) ^ t) : IsEquilibrium β φ γ Ms₀ C N P W Q Ms := by
  have hW : ∀ t, 0 < W t := fun t => by rw [hfirm t]; exact hP t
  refine ⟨fun t => (hopt.1 t).2.2.1, hN, hP, foc_labour_money hopt hβ hφ hN hP,
    foc_labour_bonds hopt hβ hφ hN hW hQ, foc_cia_ineq hopt hβ hφ hN hP hW, fun t ht => ?_,
    fun t => ?_, hfirm, hclear, hmoney⟩
  · exact foc_cia_slack hopt hβ hφ hN hW (by rw [hMT t]; exact ht)
  · have := (hopt.1 t).2.1
    simp only [CIA] at this
    rw [← hMT t]; exact this

/-- Galí (2015), Ex. 2.8(b): in every equilibrium `Q_t ≤ 1` (a nonnegative nominal rate:
otherwise money would dominate bonds). -/
theorem Q_le_one (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hβ : 0 ≤ β) (t : ℕ) : Q t ≤ 1 := by
  have hW : ∀ t, 0 < W t := fun t => by rw [h.firm t]; exact h.pos_P t
  have ha : 0 < N t ^ φ / W t := div_pos (Real.rpow_pos_of_pos (h.pos_N t) φ) (hW t)
  have hPC : 0 < P (t + 1) * C (t + 1) := mul_pos (h.pos_P _) (h.pos_C _)
  have hI : N t ^ φ / W t = β / (P (t + 1) * C (t + 1)) := by
    rw [h.focI t]; field_simp [(hW t).ne']
  have hIII : N (t + 1) ^ φ / W (t + 1) ≤ 1 / (P (t + 1) * C (t + 1)) := by
    have := h.focIII (t + 1)
    rw [div_le_div_iff₀ (hW _) (h.pos_C _)] at this
    rw [div_le_div_iff₀ (hW _) hPC]
    nlinarith [h.pos_P (t + 1)]
  have hII : Q t * (N t ^ φ / W t) = β * (N (t + 1) ^ φ / W (t + 1)) := by
    rw [← mul_div_assoc, h.focII t, mul_div_assoc]
  have : Q t * (N t ^ φ / W t) ≤ 1 * (N t ^ φ / W t) := by
    rw [hII, one_mul, hI, div_eq_mul_one_div β]
    exact mul_le_mul_of_nonneg_left hIII hβ
  exact le_of_mul_le_mul_right this ha

/-- Galí (2015), Ex. 2.8(b): if `Q_t < 1` (a positive nominal rate) the CIA binds at `t+1`. -/
theorem cia_binds_of_Q_lt_one (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) {t : ℕ}
    (hQ : Q t < 1) : P (t + 1) * C (t + 1) = Ms (t + 1) := by
  by_contra hne
  have hlt := lt_of_le_of_ne (h.cia (t + 1)) hne
  have hW : ∀ t, 0 < W t := fun t => by rw [h.firm t]; exact h.pos_P t
  have ha : 0 < N t ^ φ / W t := div_pos (Real.rpow_pos_of_pos (h.pos_N t) φ) (hW t)
  have hPC : 0 < P (t + 1) * C (t + 1) := mul_pos (h.pos_P _) (h.pos_C _)
  have hI : N t ^ φ / W t = β / (P (t + 1) * C (t + 1)) := by
    rw [h.focI t]; field_simp [(hW t).ne']
  have hIII : N (t + 1) ^ φ / W (t + 1) = 1 / (P (t + 1) * C (t + 1)) := by
    have := h.slack (t + 1) hlt
    rw [div_eq_div_iff (hW _).ne' (h.pos_C _).ne'] at this
    rw [div_eq_div_iff (hW _).ne' hPC.ne']
    linarith
  have hII : Q t * (N t ^ φ / W t) = β * (N (t + 1) ^ φ / W (t + 1)) := by
    rw [← mul_div_assoc, h.focII t, mul_div_assoc]
  have : Q t * (N t ^ φ / W t) = 1 * (N t ^ φ / W t) := by
    rw [hII, one_mul, hI, hIII, div_eq_mul_one_div β]
  have := mul_right_cancel₀ ha.ne' this
  linarith

/-- Galí (2015), Ex. 2.8(b), p. 50 (**money growth and output**): if the CIA binds at `t` and
`t+1`, then `N_t^{1+φ} = β/(1+γ)`. -/
theorem output_of_binding (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hγ : 0 < 1 + γ)
    {t : ℕ} (hb : P t * C t = Ms t) (hb1 : P (t + 1) * C (t + 1) = Ms (t + 1)) :
    N t ^ (1 + φ) = β / (1 + γ) := by
  have hN := h.pos_N t
  have hI := h.focI t
  rw [hb1, h.firm t, h.money (t + 1), pow_succ] at hI
  have hMs : Ms₀ * (1 + γ) ^ t = P t * N t := by rw [← h.money t, ← hb, h.clearing t]
  rw [← mul_assoc, hMs] at hI
  rw [Real.rpow_add hN, Real.rpow_one, hI]
  field_simp [(h.pos_P t).ne', hN.ne', hγ.ne']

/-- Galí (2015), Ex. 2.8(b), p. 50: hence `Y_t = N_t = (β/(1+γ))^{1/(1+φ)}`. -/
theorem output_eq (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ) (hγ : 0 < 1 + γ)
    {t : ℕ} (hb : P t * C t = Ms t) (hb1 : P (t + 1) * C (t + 1) = Ms (t + 1)) :
    N t = (β / (1 + γ)) ^ (1 + φ)⁻¹ := by
  rw [← output_of_binding h hγ hb hb1, Real.rpow_rpow_inv (h.pos_N t).le (by linarith)]

/-- Galí (2015), Ex. 2.8(b), p. 50: equilibrium output `(β/(1+γ))^{1/(1+φ)}` is strictly
decreasing in money growth `γ` (on `γ > −1`). -/
theorem output_strictAnti (hβ : 0 < β) (hφ : 0 ≤ φ) :
    StrictAntiOn (fun γ : ℝ => (β / (1 + γ)) ^ (1 + φ)⁻¹) (Set.Ioi (-1)) := by
  intro γ₁ h1 γ₂ h2 h12
  simp only [Set.mem_Ioi] at h1 h2
  exact Real.rpow_lt_rpow (div_pos hβ (by linarith)).le
    (div_lt_div_of_pos_left hβ (by linarith) (by linarith)) (inv_pos.2 (by linarith))

/-- Galí (2015), Ex. 2.8(b), p. 50 (**existence**): for `0 < β ≤ 1 + γ` and `M^s_0 > 0`, the
allocation `C_t = N_t = N* = (β/(1+γ))^{1/(1+φ)}`, `P_t = M^s_t/N*`, `W = P`, `Q_t = β/(1+γ)`
is an equilibrium (with a binding CIA). -/
theorem stationary_isEquilibrium (hβ : 0 < β) (hγ : β ≤ 1 + γ) (hφ : 0 ≤ φ) (hM : 0 < Ms₀) :
    IsEquilibrium β φ γ Ms₀ (fun _ => (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun _ => (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun t => Ms₀ * (1 + γ) ^ t / (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun t => Ms₀ * (1 + γ) ^ t / (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun _ => β / (1 + γ)) (fun t => Ms₀ * (1 + γ) ^ t) := by
  have hγ0 : 0 < 1 + γ := by linarith
  set n := (β / (1 + γ)) ^ (1 + φ)⁻¹ with hn
  have hnpos : 0 < n := Real.rpow_pos_of_pos (div_pos hβ hγ0) _
  have hn1 : n ^ (1 + φ) = β / (1 + γ) :=
    Real.rpow_inv_rpow (div_pos hβ hγ0).le (by linarith)
  have hnφ : n ^ φ * n = β / (1 + γ) := by
    rw [← hn1, Real.rpow_add hnpos, Real.rpow_one, mul_comm]
  have hnφ' : (1 + γ) * (n ^ φ * n) = β := by rw [hnφ]; field_simp
  have hX : n ^ φ * n ≤ 1 := by rw [hnφ, div_le_one hγ0]; exact hγ
  refine ⟨fun _ => hnpos, fun _ => hnpos, fun t => by positivity, fun t => ?_, fun t => ?_,
    fun t => ?_, fun t ht => ?_, fun t => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · rw [pow_succ]
    field_simp
    linear_combination hnφ'
  · rw [pow_succ]
    field_simp
  · rw [div_le_div_iff₀ (by positivity) hnpos]
    field_simp
    linarith [hX]
  · field_simp at ht
    exact absurd ht (lt_irrefl _)
  · field_simp
    rfl

/-- Galí (2015), Ex. 2.8(b): in the stationary equilibrium gross inflation is
`P_{t+1}/P_t = 1 + γ`. -/
theorem stationary_inflation {n : ℝ} (hγ : 0 < 1 + γ) (hM : 0 < Ms₀) (hn : 0 < n) (t : ℕ) :
    (Ms₀ * (1 + γ) ^ (t + 1) / n) / (Ms₀ * (1 + γ) ^ t / n) = 1 + γ := by
  rw [pow_succ]
  field_simp

/-! ### (b) Transversality and the binding CIA in every equilibrium -/

/-- Galí (2015), eq. (6), p. 19, for Ex. 2.8 in equilibrium (`B = 0`, money held into `T+1` is
`M^s_T`): the transversality condition `liminf_T disc_{T+1} M^s_T ≤ 0`, i.e. for every `L > 0`
infinitely often `disc_{T+1} M^s_T < L`. -/
def EqTVC (Q Ms : ℕ → ℝ) : Prop :=
  ∀ L > 0, ∃ᶠ T in atTop, disc Q (T + 1) * Ms T < L

/-- Galí (2015), Ex. 2.8: an overtaking-optimal household plan with no bonds outstanding
(`B = 0`) and money market clearing (`M_{t+1} = M^s_t`) satisfies the equilibrium
transversality condition. -/
theorem eqTVC_of_optimalNP {T M B : ℕ → ℝ} (hopt : OptimalNP β φ P W Q T C N M B)
    (hφ : 0 ≤ φ) (hQ : ∀ t, 0 < Q t) (hW : 0 < W 0) (hN : 0 < N 0) (hB : ∀ t, B t = 0)
    (hM : ∀ t, M (t + 1) = Ms t) : EqTVC Q Ms := by
  intro L hL
  have h := tvc_liminf_of_optimalNP hopt hφ hQ hW hN hL
  rw [Filter.frequently_atTop] at h ⊢
  intro a
  obtain ⟨b, hb, hbL⟩ := h (a + 1)
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  refine ⟨c, by omega, ?_⟩
  rw [hB, hM, zero_add] at hbL
  exact hbL

/-- Galí (2015), Ex. 2.8(b): bond prices are positive in every equilibrium (`β > 0`). -/
theorem Q_pos (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hβ : 0 < β) (t : ℕ) : 0 < Q t := by
  have hW : ∀ t, 0 < W t := fun t => by rw [h.firm t]; exact h.pos_P t
  have h1 := h.focII t
  have hr : 0 < β * N (t + 1) ^ φ / W (t + 1) :=
    div_pos (mul_pos hβ (Real.rpow_pos_of_pos (h.pos_N _) φ)) (hW _)
  rw [← h1, mul_div_assoc] at hr
  exact pos_of_mul_pos_left hr (div_pos (Real.rpow_pos_of_pos (h.pos_N t) φ) (hW t)).le

/-- Galí (2015), Ex. 2.8(b): if the CIA is slack at `t`, then `N_t = 1` (efficient hours). -/
theorem employment_one_of_slack (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ)
    {t : ℕ} (hs : P t * C t < Ms t) : N t = 1 := by
  have e := h.slack t hs
  rw [h.firm t, h.clearing t, mul_div_assoc, div_self (h.pos_P t).ne', mul_one] at e
  have hN := h.pos_N t
  have h2 : N t ^ (1 + φ) = 1 := by
    rw [Real.rpow_add hN, Real.rpow_one, e]; field_simp
  rw [← Real.rpow_rpow_inv hN.le (by linarith : (1 + φ) ≠ 0), h2, Real.one_rpow]

/-- Galí (2015), Ex. 2.8(b): with `0 < β ≤ 1 + γ` a slack CIA stays slack (real balances grow
at the gross rate `(1+γ)/β`). -/
theorem slack_succ (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ) (hβ : 0 < β)
    (hβγ : β ≤ 1 + γ) {t : ℕ} (hs : P t * C t < Ms t) :
    P (t + 1) * C (t + 1) < Ms (t + 1) := by
  have hN := employment_one_of_slack h hφ hs
  have hI := h.focI t
  rw [hN, Real.one_rpow, h.firm t] at hI
  have hPC : 0 < P (t + 1) * C (t + 1) := mul_pos (h.pos_P _) (h.pos_C _)
  have e : P (t + 1) * C (t + 1) = β * P t := by
    rw [eq_div_iff hPC.ne'] at hI; linarith
  rw [h.clearing t, hN, mul_one] at hs
  have hMs : Ms (t + 1) = (1 + γ) * Ms t := by rw [h.money, h.money, pow_succ]; ring
  have hMs0 : 0 ≤ Ms t := (h.pos_P t).le.trans hs.le
  rw [e, hMs]
  calc β * P t < β * Ms t := mul_lt_mul_of_pos_left hs hβ
    _ ≤ (1 + γ) * Ms t := mul_le_mul_of_nonneg_right hβγ hMs0

/-- Galí (2015), Ex. 2.8(b): if the CIA is slack at `t` and `t+1`, the nominal rate is zero:
`Q_t = 1`. -/
theorem Q_eq_one_of_slack (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ) {t : ℕ}
    (hs : P t * C t < Ms t) (hs1 : P (t + 1) * C (t + 1) < Ms (t + 1)) : Q t = 1 := by
  have hN := employment_one_of_slack h hφ hs
  have hN1 := employment_one_of_slack h hφ hs1
  have hI := h.focI t
  have hII := h.focII t
  rw [hN, Real.one_rpow, h.firm t, h.clearing (t + 1), hN1, mul_one] at hI
  rw [hN, hN1, Real.one_rpow, h.firm t, h.firm (t + 1), mul_one] at hII
  have hP := h.pos_P t
  have hP1 := h.pos_P (t + 1)
  rw [eq_div_iff hP1.ne', one_mul] at hI
  rw [div_eq_div_iff hP.ne' hP1.ne'] at hII
  have : Q t * P (t + 1) = 1 * P (t + 1) := by linarith
  exact mul_right_cancel₀ hP1.ne' this

/-- Galí (2015), Ex. 2.8(b) (**the CIA binds in every equilibrium**, `γ ≥ 0`): with
`0 < β ≤ 1`, `γ ≥ 0` and the transversality condition, the CIA binds at every date. A slack
CIA would stay slack forever with `Q = 1`, and the discounted money stock
`disc_{T+1} M^s_T` would then grow at the rate `1 + γ ≥ 1`, violating transversality. -/
theorem cia_binds_of_tvc (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (htvc : EqTVC Q Ms)
    (hφ : 0 ≤ φ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hγ : 0 ≤ γ) (t : ℕ) : P t * C t = Ms t := by
  by_contra hne
  have hs : P t * C t < Ms t := lt_of_le_of_ne (h.cia t) hne
  have hβγ : β ≤ 1 + γ := by linarith
  have hall : ∀ k, P (t + k) * C (t + k) < Ms (t + k) := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k ih => exact slack_succ h hφ hβ hβγ ih
  set D : ℕ → ℝ := fun T => disc Q (T + 1) * Ms T with hD
  have hQp := Q_pos h hβ
  have hDt : 0 < D t := by
    have : 0 < Ms t := (mul_pos (h.pos_P t) (h.pos_C t)).trans hs
    exact mul_pos (disc_pos hQp _) this
  have hgrow : ∀ k, D t ≤ D (t + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hQ1 : Q (t + k + 1) = 1 := Q_eq_one_of_slack h hφ (hall (k + 1)) (by
        simpa [add_assoc] using hall (k + 2))
      have hstep : D (t + (k + 1)) = (1 + γ) * D (t + k) := by
        simp only [hD]
        rw [show t + (k + 1) = t + k + 1 by ring, disc_succ, hQ1, h.money, h.money, pow_succ]
        ring
      have hD0 : 0 ≤ D (t + k) := hDt.le.trans ih
      rw [hstep]
      nlinarith
  obtain ⟨T, hT1, hT2⟩ := ((htvc (D t) hDt).and_eventually (eventually_ge_atTop t)).exists
  obtain ⟨k, rfl⟩ : ∃ k, T = t + k := ⟨T - t, by omega⟩
  exact absurd (hgrow k) (not_le.2 hT1)

/-- Galí (2015), Ex. 2.8(b), p. 50 (**every equilibrium**): with transversality, `0 < β ≤ 1`
and `γ ≥ 0`, output is `Y_t = N_t = (β/(1+γ))^{1/(1+φ)}` at every date. -/
theorem output_eq_of_tvc (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (htvc : EqTVC Q Ms)
    (hφ : 0 ≤ φ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hγ : 0 ≤ γ) (t : ℕ) :
    N t = (β / (1 + γ)) ^ (1 + φ)⁻¹ :=
  output_eq h hφ (by linarith) (cia_binds_of_tvc h htvc hφ hβ hβ1 hγ t)
    (cia_binds_of_tvc h htvc hφ hβ hβ1 hγ (t + 1))

/-- Galí (2015), Ex. 2.8(b) (**correction**: `1 + γ > β` is not enough when `γ < 0`): for
`β < 1 + γ < 1`, `0 < P₀ < M^s_0`, the path `C = N = 1`, `P_t = W_t = P₀ βᵗ`, `Q = 1` is an
equilibrium satisfying transversality in which the CIA is slack at every date, and output
`1` differs from `(β/(1+γ))^{1/(1+φ)}`. -/
theorem slack_equilibrium_counterexample {P₀ : ℝ} (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hβγ : β < 1 + γ) (hγ1 : 1 + γ < 1) (hP₀ : 0 < P₀) (hPM : P₀ < Ms₀) :
    IsEquilibrium β φ γ Ms₀ (fun _ => 1) (fun _ => 1) (fun t => P₀ * β ^ t)
        (fun t => P₀ * β ^ t) (fun _ => 1) (fun t => Ms₀ * (1 + γ) ^ t) ∧
      EqTVC (fun _ => 1) (fun t => Ms₀ * (1 + γ) ^ t) ∧
      (∀ t, P₀ * β ^ t * 1 < Ms₀ * (1 + γ) ^ t) ∧ (β / (1 + γ)) ^ (1 + φ)⁻¹ < 1 := by
  have hγ0 : 0 < 1 + γ := by linarith
  have hslack : ∀ t : ℕ, P₀ * β ^ t * 1 < Ms₀ * (1 + γ) ^ t := by
    intro t
    rw [mul_one]
    exact mul_lt_mul hPM (pow_le_pow_left₀ hβ.le hβγ.le t) (pow_pos hβ t) (by linarith)
  refine ⟨⟨fun _ => one_pos, fun _ => one_pos, fun t => by positivity, fun t => ?_,
    fun t => ?_, fun t => ?_, fun t _ => ?_, fun t => (hslack t).le, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩, ?_, hslack, ?_⟩
  · simp only [Real.one_rpow, mul_one, pow_succ]
    field_simp
  · simp only [Real.one_rpow, pow_succ]
    field_simp
  · simp only [Real.one_rpow]
    field_simp
    rfl
  · simp only [Real.one_rpow]
    field_simp
  · intro L hL
    have hlim : Tendsto (fun T : ℕ => disc (fun _ => (1 : ℝ)) (T + 1) * (Ms₀ * (1 + γ) ^ T))
        atTop (𝓝 0) := by
      have : (fun T : ℕ => disc (fun _ => (1 : ℝ)) (T + 1) * (Ms₀ * (1 + γ) ^ T)) =
          fun T => Ms₀ * (1 + γ) ^ T := by
        funext T; simp [disc]
      rw [this]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1).const_mul Ms₀
    exact (hlim.eventually (gt_mem_nhds hL)).frequently
  · exact Real.rpow_lt_one (div_pos hβ hγ0).le ((div_lt_one hγ0).2 hβγ)
      (inv_pos.2 (by linarith))

/-! ### (c) Optimal inflation -/

/-- Galí (2015), Ex. 2.8(c), p. 50: `log N − N^{1+φ}/(1+φ) ≤ −1/(1+φ)` for `N > 0`, with
equality iff `N = 1` (the efficient allocation). -/
theorem stationary_utility_le (hφ : 0 ≤ φ) {n : ℝ} (hn : 0 < n) :
    u φ n n ≤ -1 / (1 + φ) ∧ (u φ n n = -1 / (1 + φ) ↔ n = 1) := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  set x := n ^ (1 + φ) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hn _
  have hlog : Real.log n = Real.log x / (1 + φ) := by
    rw [hx, Real.log_rpow hn]; field_simp
  have hu : u φ n n = (Real.log x - x) / (1 + φ) := by
    rw [u, hlog, ← hx]; ring
  have hx1 : x = 1 ↔ n = 1 := by
    constructor
    · intro h
      rw [← Real.rpow_rpow_inv hn.le h1.ne', ← hx, h, Real.one_rpow]
    · intro h; rw [hx, h, Real.one_rpow]
  rw [hu]
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff_of_pos_right h1]
    linarith [Real.log_le_sub_one_of_pos hxpos]
  · rw [← hx1]
    constructor
    · intro h
      by_contra hne
      have := Real.log_lt_sub_one_of_pos hxpos hne
      have h2 : Real.log x - x = -1 := by
        field_simp at h; linarith
      linarith
    · intro h; rw [h, Real.log_one]; ring

/-- Galí (2015), Ex. 2.8(c) (**infinite horizon**): lifetime welfare of a stationary allocation
is `∑ βᵗ u(N, N) = u(N, N)/(1 − β)`. -/
theorem hasSum_welfare (hβ0 : 0 ≤ β) (hβ1 : β < 1) (n : ℝ) :
    HasSum (fun t : ℕ => β ^ t * u φ n n) (u φ n n / (1 - β)) := by
  have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (u φ n n)
  rw [div_eq_mul_inv, mul_comm]
  exact this

/-- Galí (2015), Ex. 2.8(c), p. 50 (**optimal inflation**): among money growth rates with
`1 + γ ≥ β` (i.e. `Q = β/(1+γ) ≤ 1`), stationary period utility is maximal exactly when
`1 + γ = β`: gross inflation `P_{t+1}/P_t = β`, net inflation `π = β − 1`, `Q = 1` (the
Friedman rule). -/
theorem optimal_inflation (hβ : 0 < β) (hφ : 0 ≤ φ) {γ : ℝ} (hγ : β ≤ 1 + γ) :
    u φ ((β / (1 + γ)) ^ (1 + φ)⁻¹) ((β / (1 + γ)) ^ (1 + φ)⁻¹) ≤
        u φ ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ∧
      (u φ ((β / (1 + γ)) ^ (1 + φ)⁻¹) ((β / (1 + γ)) ^ (1 + φ)⁻¹) =
          u φ ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ↔
        1 + γ = β) := by
  have hγ0 : 0 < 1 + γ := by linarith
  have hstar : (β / (1 + (β - 1))) ^ (1 + φ)⁻¹ = 1 := by
    rw [show 1 + (β - 1) = β by ring, div_self hβ.ne', Real.one_rpow]
  have hpos : 0 < (β / (1 + γ)) ^ (1 + φ)⁻¹ := Real.rpow_pos_of_pos (div_pos hβ hγ0) _
  have hval : u φ 1 1 = -1 / (1 + φ) := by
    rw [u, Real.log_one, Real.one_rpow]; ring
  obtain ⟨hle, hiff⟩ := stationary_utility_le hφ hpos
  rw [hstar, hval]
  refine ⟨hle, ?_⟩
  rw [hiff]
  constructor
  · intro h
    have h2 := congrArg (fun x : ℝ => x ^ (1 + φ)) h
    simp only [Real.one_rpow] at h2
    rw [Real.rpow_inv_rpow (div_pos hβ hγ0).le (by linarith), div_eq_one_iff_eq hγ0.ne'] at h2
    exact h2.symm
  · intro h
    rw [h, div_self hβ.ne', Real.one_rpow]

/-- Galí (2015), Ex. 2.8(c), p. 50: at the optimum the bond price is `Q = β/(1+γ) = 1`, i.e.
the nominal rate is zero (Friedman rule). -/
theorem friedman_at_optimum (hβ : 0 < β) {γ : ℝ} (h : 1 + γ = β) : β / (1 + γ) = 1 := by
  rw [h, div_self hβ.ne']

end Gali.ClassicalMonetaryModel.Ex2_8

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 2.9: cash and credit goods

Galí (2015), Chapter 2, Exercise 2.9, pp. 50–51. Utility `V(C₁, C₂, N)` (eq. (54)) of a cash
good `C₁`, a credit good `C₂` and hours `N`; both goods cost `P_t`; the budget is
`P_t(C₁ₜ + C₂ₜ) + Q_t B_t + M_t ≤ B_{t−1} + M_{t−1} + W_t N_t + T_t` and the cash-in-advance
constraint `P_t C₁ₜ ≤ M_{t−1} + T_t`. No uncertainty.

**Indexing.** As in Ex. 2.8, `M t`, `B t` are the holdings carried *into* date `t`.
`V` is any function `ℝ × ℝ × ℝ → ℝ`, differentiable at the plan, with partial derivatives
`V₁ = V'(1,0,0)`, `V₂ = V'(0,1,0)`, `V₃ = V'(0,0,1)`.

## (a) First-order conditions (KKT for the single inequality, by hand)

Feasible perturbations of an `Optimal` plan (finite deviations; `optimal_of_tsum_max` links
this to the infinite discounted sum) give:

* `foc_credit_labour` (two-sided): `V₂/P_t = −V₃/W_t`;
* `foc_cash_credit_ineq` (one-sided: only shifting spending *away* from the cash good is
  always feasible; `nonneg_of_left_max`): `V₁ ≥ V₂`, with equality when the CIA is slack
  (`foc_cash_credit_slack`);
* `foc_bonds` (two-sided): `Q_t V₂ₜ/P_t = β V₂,ₜ₊₁/P_{t+1}`;
* `foc_money` (two-sided): `V₂ₜ/P_t = β V₁,ₜ₊₁/P_{t+1}`;
* `kkt`: with `λ_t = V₂ₜ/P_t` (budget) and `μ_t = (V₁ₜ − V₂ₜ)/P_t` (CIA):
  `V₁ = P(λ + μ)`, `V₂ = P λ`, `V₃ = −W λ`, `λ_t Q_t = β λ_{t+1}`,
  `λ_t = β(λ_{t+1} + μ_{t+1})`, `μ_t ≥ 0`, `μ_t (M_t + T_t − P_t C₁ₜ) = 0`.

## (b) The reduced form

With a binding CIA, `C₁ = M/P`, so `U(C, M/P, N) = V(M/P, C − M/P, N)`:
`hasDerivAt_U_m` gives `U_m = V₁ − V₂`, and `U_m_eq_mul_mu`: `U_m = P μ ≥ 0` at an optimum
(`U_m_nonneg`); `U_c = V₂`, `U_n = V₃` (`hasDerivAt_U_c`, `hasDerivAt_U_n`).
-/

namespace Gali.ClassicalMonetaryModel.Ex2_9

open Filter Topology

/-- Galí (2015), Ex. 2.9(a): the chain rule along a curve in `ℝ × ℝ × ℝ`,
`d/ds V(f s, g s, h s) = f' V₁ + g' V₂ + h' V₃`. -/
theorem hasDerivAt_curve3 {V : ℝ × ℝ × ℝ → ℝ} {V' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {f g h : ℝ → ℝ}
    {a b c s : ℝ} (hV : HasFDerivAt V V' (f s, g s, h s)) (hf : HasDerivAt f a s)
    (hg : HasDerivAt g b s) (hh : HasDerivAt h c s) :
    HasDerivAt (fun x => V (f x, g x, h x))
      (a * V' (1, 0, 0) + b * V' (0, 1, 0) + c * V' (0, 0, 1)) s := by
  have hd := hV.comp_hasDerivAt (f := fun x => (f x, g x, h x)) s (hf.prodMk (hg.prodMk hh))
  have hv : ((a, b, c) : ℝ × ℝ × ℝ) =
      a • ((1, 0, 0) : ℝ × ℝ × ℝ) + b • ((0, 1, 0) : ℝ × ℝ × ℝ) + c • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul] at hd
  exact hd

/-- **KKT for a single inequality, proved by hand** (Galí (2015), Ex. 2.9(a)): if `f` has
derivative `d` at `0` and `f δ ≤ f 0` for all small `δ ≤ 0`, then `d ≥ 0`. -/
theorem nonneg_of_left_max {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (h : ∀ᶠ δ in 𝓝 0, δ ≤ 0 → f δ ≤ f 0) : 0 ≤ d := by
  by_contra hd
  push Not at hd
  have ho := hf.isLittleO
  have hc : 0 < -d / 2 := by linarith
  have h2 := ho.def hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h.and h2)
  set δ := -(ε / 2) with hδ
  have hdist : dist δ 0 < ε := by
    rw [Real.dist_eq, hδ, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith
  obtain ⟨h1, h3⟩ := hball hdist
  have hle := h1 (by rw [hδ]; linarith)
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs] at h3
  have habs : |δ| = ε / 2 := by rw [hδ, abs_neg, abs_of_pos (by linarith)]
  rw [habs] at h3
  have := (abs_le.1 h3).1
  rw [hδ] at this
  nlinarith

/-! ### The household problem -/

/-- Galí (2015), Ex. 2.9, p. 51: the budget constraint at date `t`. -/
def Budget (P W Q T C₁ C₂ N M B : ℕ → ℝ) (t : ℕ) : Prop :=
  P t * (C₁ t + C₂ t) + Q t * B (t + 1) + M (t + 1) ≤ B t + M t + W t * N t + T t

/-- Galí (2015), Ex. 2.9, p. 51: the CIA constraint `P_t C₁ₜ ≤ M_{t−1} + T_t`. -/
def CIA (P T C₁ M : ℕ → ℝ) (t : ℕ) : Prop := P t * C₁ t ≤ M t + T t

/-- Galí (2015), Ex. 2.9, p. 51: a feasible plan. -/
def Feasible (P W Q T C₁ C₂ N M B : ℕ → ℝ) : Prop :=
  ∀ t, Budget P W Q T C₁ C₂ N M B t ∧ CIA P T C₁ M t ∧ 0 ≤ C₁ t ∧ 0 ≤ C₂ t ∧ 0 ≤ N t

/-- Galí (2015), Ex. 2.9, eq. (54), p. 50: optimality against all feasible finite deviations
with the same initial holdings. -/
def Optimal (β : ℝ) (V : ℝ × ℝ × ℝ → ℝ) (P W Q T C₁ C₂ N M B : ℕ → ℝ) : Prop :=
  Feasible P W Q T C₁ C₂ N M B ∧
    ∀ (C₁' C₂' N' M' B' : ℕ → ℝ) (T₀ : ℕ), Feasible P W Q T C₁' C₂' N' M' B' →
      M' 0 = M 0 → B' 0 = B 0 →
      (∀ s, T₀ ≤ s → C₁' s = C₁ s ∧ C₂' s = C₂ s ∧ N' s = N s ∧ M' s = M s ∧ B' s = B s) →
      ∑ s ∈ Finset.range T₀, β ^ s * V (C₁' s, C₂' s, N' s) ≤
        ∑ s ∈ Finset.range T₀, β ^ s * V (C₁ s, C₂ s, N s)

variable {β : ℝ} {V : ℝ × ℝ × ℝ → ℝ} {P W Q T C₁ C₂ N M B : ℕ → ℝ}

/-- Galí (2015), Ex. 2.9 (**infinite horizon**): a feasible plan maximising the summable
discounted sum `∑' βᵗ V_t` among feasible plans with the same initial holdings is `Optimal`. -/
theorem optimal_of_tsum_max (hf : Feasible P W Q T C₁ C₂ N M B)
    (hs : Summable fun s => β ^ s * V (C₁ s, C₂ s, N s))
    (hmax : ∀ C₁' C₂' N' M' B' : ℕ → ℝ, Feasible P W Q T C₁' C₂' N' M' B' → M' 0 = M 0 →
      B' 0 = B 0 → Summable (fun s => β ^ s * V (C₁' s, C₂' s, N' s)) →
      ∑' s, β ^ s * V (C₁' s, C₂' s, N' s) ≤ ∑' s, β ^ s * V (C₁ s, C₂ s, N s)) :
    Optimal β V P W Q T C₁ C₂ N M B := by
  refine ⟨hf, fun C₁' C₂' N' M' B' T₀ hf' hM hB hagree => ?_⟩
  have htail : (fun s => β ^ (s + T₀) * V (C₁' (s + T₀), C₂' (s + T₀), N' (s + T₀))) =
      fun s => β ^ (s + T₀) * V (C₁ (s + T₀), C₂ (s + T₀), N (s + T₀)) := by
    funext s
    obtain ⟨h1, h2, h3, -⟩ := hagree (s + T₀) (by omega)
    rw [h1, h2, h3]
  have hs' : Summable fun s => β ^ s * V (C₁' s, C₂' s, N' s) := by
    rw [← summable_nat_add_iff T₀, htail]
    exact (summable_nat_add_iff T₀).2 hs
  have h := hmax C₁' C₂' N' M' B' hf' hM hB hs'
  rw [← hs'.sum_add_tsum_nat_add T₀, ← hs.sum_add_tsum_nat_add T₀] at h
  have he : ∑' s, β ^ (s + T₀) * V (C₁' (s + T₀), C₂' (s + T₀), N' (s + T₀)) =
      ∑' s, β ^ (s + T₀) * V (C₁ (s + T₀), C₂ (s + T₀), N (s + T₀)) := by rw [htail]
  linarith

/-- Galí (2015), Ex. 2.9(a): a feasible deviation at dates `t, t+1` (holdings changed only
for `t+1`) does not raise utility. -/
theorem gain_nonpos (hopt : Optimal β V P W Q T C₁ C₂ N M B) {C₁' C₂' N' M' B' : ℕ → ℝ}
    (t : ℕ) (hf : Feasible P W Q T C₁' C₂' N' M' B')
    (hC : ∀ s, s ≠ t → s ≠ t + 1 → C₁' s = C₁ s ∧ C₂' s = C₂ s ∧ N' s = N s)
    (hMB : ∀ s, s ≠ t + 1 → M' s = M s ∧ B' s = B s) :
    β ^ t * (V (C₁' t, C₂' t, N' t) - V (C₁ t, C₂ t, N t)) +
      β ^ (t + 1) * (V (C₁' (t + 1), C₂' (t + 1), N' (t + 1)) -
        V (C₁ (t + 1), C₂ (t + 1), N (t + 1))) ≤ 0 := by
  have h := hopt.2 C₁' C₂' N' M' B' (t + 1 + 1) hf (hMB 0 (by omega)).1 (hMB 0 (by omega)).2
    (fun s hs => ⟨(hC s (by omega) (by omega)).1, (hC s (by omega) (by omega)).2.1,
      (hC s (by omega) (by omega)).2.2, (hMB s (by omega)).1, (hMB s (by omega)).2⟩)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
    Finset.sum_range_succ (n := t)] at h
  have hsame : ∑ s ∈ Finset.range t, β ^ s * V (C₁' s, C₂' s, N' s) =
      ∑ s ∈ Finset.range t, β ^ s * V (C₁ s, C₂ s, N s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    obtain ⟨h1, h2, h3⟩ := hC s (by omega) (by omega)
    rw [h1, h2, h3]
  linarith

variable {V' : ℕ → ℝ × ℝ × ℝ →L[ℝ] ℝ}

/-- Galí (2015), Ex. 2.9(a), p. 51 (**two-sided**): more credit good financed by more work,
`P dC₂ = W dN`: `V₂/P_t = −V₃/W_t`. -/
theorem foc_credit_labour (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₂ : ∀ t, 0 < C₂ t)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) (t : ℕ) :
    V' t (0, 1, 0) / P t = -V' t (0, 0, 1) / W t := by
  set f : ℝ → ℝ := fun δ => β ^ t * (V (C₁ t, C₂ t + δ, N t + P t * δ / W t) -
    V (C₁ t, C₂ t, N t)) with hfdef
  have hloc : IsLocalMax f 0 := by
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), -C₂ t < δ := eventually_gt_nhds (by linarith [hC₂ t])
    have hc : Continuous fun δ : ℝ => N t + P t * δ / W t := by fun_prop
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N t + P t * δ / W t :=
      (hc.tendsto 0).eventually_const_lt (by simpa using hN t)
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T C₁ (Function.update C₂ t (C₂ t + δ))
        (Function.update N t (N t + P t * δ / W t)) M B := by
      intro s
      obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
      have hPW : W t * (P t * δ / W t) = P t * δ := by field_simp [(hW t).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
        first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [hfdef, add_zero, mul_zero, zero_div, sub_self]
    exact hg
  have hd : HasDerivAt f (β ^ t * (0 * V' t (1, 0, 0) + 1 * V' t (0, 1, 0) +
      P t / W t * V' t (0, 0, 1))) 0 := by
    have hin : HasDerivAt (fun δ : ℝ => N t + P t * δ / W t) (P t / W t) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).const_mul (P t)).div_const (W t)).const_add (N t)
      simpa using this
    have hc2 : HasDerivAt (fun δ : ℝ => C₂ t + δ) 1 0 := (hasDerivAt_id' 0).const_add _
    have := hasDerivAt_curve3 (f := fun _ => C₁ t) (g := fun δ => C₂ t + δ)
      (h := fun δ => N t + P t * δ / W t) (s := 0) (by simpa using hV t)
      (hasDerivAt_const 0 (C₁ t)) hc2 hin
    exact (this.sub_const (V (C₁ t, C₂ t, N t))).const_mul (β ^ t)
  have h0 := (mul_eq_zero.1 (hloc.hasDerivAt_eq_zero hd)).resolve_left (pow_pos hβ t).ne'
  have h1 : V' t (0, 1, 0) = -(P t / W t * V' t (0, 0, 1)) := by linarith
  rw [div_eq_div_iff (hP t).ne' (hW t).ne', h1]
  field_simp [(hW t).ne']

/-- Galí (2015), Ex. 2.9(a): the cash–credit shift `C₁ + δ`, `C₂ − δ` is feasible whenever the
CIA still holds and both goods stay nonnegative. -/
theorem cash_credit_feasible (hopt : Optimal β V P W Q T C₁ C₂ N M B) {t : ℕ} {δ : ℝ}
    (h1 : 0 ≤ C₁ t + δ) (h2 : 0 ≤ C₂ t - δ) (h3 : P t * (C₁ t + δ) ≤ M t + T t) :
    Feasible P W Q T (Function.update C₁ t (C₁ t + δ)) (Function.update C₂ t (C₂ t - δ)) N M
      B := by
  intro s
  obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
  simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
    first | omega | nlinarith

/-- Galí (2015), Ex. 2.9(a): the gain of the cash–credit shift has derivative
`β^t (V₁ − V₂)` at `δ = 0`. -/
theorem hasDerivAt_cash_credit (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (t : ℕ) :
    HasDerivAt (fun δ => β ^ t * (V (C₁ t + δ, C₂ t - δ, N t) - V (C₁ t, C₂ t, N t)))
      (β ^ t * (1 * V' t (1, 0, 0) + -1 * V' t (0, 1, 0) + 0 * V' t (0, 0, 1))) 0 := by
  have h1 : HasDerivAt (fun δ : ℝ => C₁ t + δ) 1 0 := (hasDerivAt_id' 0).const_add _
  have h2 : HasDerivAt (fun δ : ℝ => C₂ t - δ) (-1) 0 := (hasDerivAt_id' 0).const_sub _
  have := hasDerivAt_curve3 (f := fun δ => C₁ t + δ) (g := fun δ => C₂ t - δ)
    (h := fun _ => N t) (s := 0) (by simpa using hV t) h1 h2 (hasDerivAt_const 0 (N t))
  exact (this.sub_const (V (C₁ t, C₂ t, N t))).const_mul (β ^ t)

/-- Galí (2015), Ex. 2.9(a), p. 51 (**KKT, the inequality**): shifting spending away from the
cash good is always feasible, so `V₁ ≥ V₂`. -/
theorem foc_cash_credit_ineq (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    V' t (0, 1, 0) ≤ V' t (1, 0, 0) := by
  have hcia := (hopt.1 t).2.1
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), -C₁ t < δ := eventually_gt_nhds (by linarith [hC₁ t])
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < C₂ t := eventually_lt_nhds (hC₂ t)
  have hleft : ∀ᶠ δ in 𝓝 (0 : ℝ), δ ≤ 0 →
      β ^ t * (V (C₁ t + δ, C₂ t - δ, N t) - V (C₁ t, C₂ t, N t)) ≤
        β ^ t * (V (C₁ t + 0, C₂ t - 0, N t) - V (C₁ t, C₂ t, N t)) := by
    filter_upwards [e1, e2] with δ h1 h2 hδ
    have h3 : P t * (C₁ t + δ) ≤ M t + T t := by
      simp only [CIA] at hcia; nlinarith [hP t]
    have hg := gain_nonpos hopt t (cash_credit_feasible hopt (by linarith) (by linarith) h3)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [add_zero, sub_zero, sub_self, mul_zero]
    exact hg
  have h0 := nonneg_of_left_max (hasDerivAt_cash_credit hV t) hleft
  have h1 : 0 ≤ 1 * V' t (1, 0, 0) + -1 * V' t (0, 1, 0) + 0 * V' t (0, 0, 1) :=
    nonneg_of_mul_nonneg_right h0 (pow_pos hβ t)
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**complementary slackness**): if the CIA is slack,
`V₁ = V₂`. -/
theorem foc_cash_credit_slack (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) {t : ℕ} (hslack : P t * C₁ t < M t + T t) :
    V' t (1, 0, 0) = V' t (0, 1, 0) := by
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), -C₁ t < δ := eventually_gt_nhds (by linarith [hC₁ t])
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < C₂ t := eventually_lt_nhds (hC₂ t)
  have hc3 : Continuous fun δ : ℝ => P t * (C₁ t + δ) := by fun_prop
  have e3 : ∀ᶠ δ in 𝓝 (0 : ℝ), P t * (C₁ t + δ) < M t + T t :=
    (hc3.tendsto 0).eventually_lt_const (by simpa using hslack)
  have hloc : IsLocalMax (fun δ => β ^ t * (V (C₁ t + δ, C₂ t - δ, N t) -
      V (C₁ t, C₂ t, N t))) 0 := by
    filter_upwards [e1, e2, e3] with δ h1 h2 h3
    have hg := gain_nonpos hopt t (cash_credit_feasible hopt (by linarith) (by linarith) h3.le)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [add_zero, sub_zero, sub_self, mul_zero]
    exact hg
  have h0 := (mul_eq_zero.1 (hloc.hasDerivAt_eq_zero (hasDerivAt_cash_credit hV t))).resolve_left
    (pow_pos hβ t).ne'
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**two-sided**): bonds, buying `δ` bonds with less credit
good at `t` and spending the proceeds on the credit good at `t+1`:
`Q_t V₂ₜ/P_t = β V₂,ₜ₊₁/P_{t+1}`. -/
theorem foc_bonds (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₂ : ∀ t, 0 < C₂ t)
    (hP : ∀ t, 0 < P t) (t : ℕ) :
    Q t * V' t (0, 1, 0) / P t = β * V' (t + 1) (0, 1, 0) / P (t + 1) := by
  set f : ℝ → ℝ := fun δ => β ^ t * (V (C₁ t, C₂ t - Q t * δ / P t, N t) -
    V (C₁ t, C₂ t, N t)) + β ^ (t + 1) * (V (C₁ (t + 1), C₂ (t + 1) + δ / P (t + 1), N (t + 1)) -
      V (C₁ (t + 1), C₂ (t + 1), N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc1 : Continuous fun δ : ℝ => C₂ t - Q t * δ / P t := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₂ t - Q t * δ / P t :=
      (hc1.tendsto 0).eventually_const_lt (by simpa using hC₂ t)
    have hc2 : Continuous fun δ : ℝ => C₂ (t + 1) + δ / P (t + 1) := by fun_prop
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₂ (t + 1) + δ / P (t + 1) :=
      (hc2.tendsto 0).eventually_const_lt (by simpa using hC₂ (t + 1))
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T C₁
        (Function.update (Function.update C₂ t (C₂ t - Q t * δ / P t)) (t + 1)
          (C₂ (t + 1) + δ / P (t + 1))) N M (Function.update B (t + 1) (B (t + 1) + δ)) := by
      intro s
      obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
      have hPQ : P t * (Q t * δ / P t) = Q t * δ := by field_simp [(hP t).ne']
      have hP1 : P (t + 1) * (δ / P (t + 1)) = δ := by field_simp [(hP (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
        first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas (fun s h1 h2 => by simp [h1, h2]) (fun s h1 => by
      simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      ↓reduceIte] at hg
    simp only [hfdef, add_zero, mul_zero, zero_div, sub_zero, sub_self]
    linarith
  have hd : HasDerivAt f (β ^ t * (0 * V' t (1, 0, 0) + -(Q t / P t) * V' t (0, 1, 0) +
      0 * V' t (0, 0, 1)) + β ^ (t + 1) * (0 * V' (t + 1) (1, 0, 0) +
      1 / P (t + 1) * V' (t + 1) (0, 1, 0) + 0 * V' (t + 1) (0, 0, 1))) 0 := by
    have hg1 : HasDerivAt (fun δ : ℝ => C₂ t - Q t * δ / P t) (-(Q t / P t)) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).const_mul (Q t)).div_const (P t)).const_sub (C₂ t)
      simpa using this
    have hg2 : HasDerivAt (fun δ : ℝ => C₂ (t + 1) + δ / P (t + 1)) (1 / P (t + 1)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).div_const (P (t + 1))).const_add (C₂ (t + 1))
      simpa using this
    have d1 := hasDerivAt_curve3 (f := fun _ => C₁ t) (g := fun δ => C₂ t - Q t * δ / P t)
      (h := fun _ => N t) (s := 0) (by simpa using hV t) (hasDerivAt_const 0 (C₁ t)) hg1
      (hasDerivAt_const 0 (N t))
    have d2 := hasDerivAt_curve3 (f := fun _ => C₁ (t + 1))
      (g := fun δ => C₂ (t + 1) + δ / P (t + 1)) (h := fun _ => N (t + 1)) (s := 0)
      (by simpa using hV (t + 1)) (hasDerivAt_const 0 (C₁ (t + 1))) hg2
      (hasDerivAt_const 0 (N (t + 1)))
    exact ((d1.sub_const _).const_mul (β ^ t)).add ((d2.sub_const _).const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * (Q t / P t * V' t (0, 1, 0)) =
      β ^ t * (β * (1 / P (t + 1) * V' (t + 1) (0, 1, 0))) := by linarith
  have h2 := mul_left_cancel₀ hb.ne' h1
  field_simp [(hP t).ne', (hP (t + 1)).ne'] at h2 ⊢
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**two-sided**): money, holding `δ` more cash (less credit
good at `t`) and buying the cash good at `t+1`: `V₂ₜ/P_t = β V₁,ₜ₊₁/P_{t+1}`. -/
theorem foc_money (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    V' t (0, 1, 0) / P t = β * V' (t + 1) (1, 0, 0) / P (t + 1) := by
  set f : ℝ → ℝ := fun δ => β ^ t * (V (C₁ t, C₂ t - δ / P t, N t) - V (C₁ t, C₂ t, N t)) +
    β ^ (t + 1) * (V (C₁ (t + 1) + δ / P (t + 1), C₂ (t + 1), N (t + 1)) -
      V (C₁ (t + 1), C₂ (t + 1), N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc1 : Continuous fun δ : ℝ => C₂ t - δ / P t := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₂ t - δ / P t :=
      (hc1.tendsto 0).eventually_const_lt (by simpa using hC₂ t)
    have hc2 : Continuous fun δ : ℝ => C₁ (t + 1) + δ / P (t + 1) := by fun_prop
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₁ (t + 1) + δ / P (t + 1) :=
      (hc2.tendsto 0).eventually_const_lt (by simpa using hC₁ (t + 1))
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T (Function.update C₁ (t + 1) (C₁ (t + 1) + δ / P (t + 1)))
        (Function.update C₂ t (C₂ t - δ / P t)) N (Function.update M (t + 1) (M (t + 1) + δ))
        B := by
      intro s
      obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
      have hP0 : P t * (δ / P t) = δ := by field_simp [(hP t).ne']
      have hP1 : P (t + 1) * (δ / P (t + 1)) = δ := by field_simp [(hP (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
        first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas (fun s h1 h2 => by simp [h1, h2]) (fun s h1 => by
      simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      show t + 1 ≠ t by omega, ↓reduceIte] at hg
    simp only [hfdef, add_zero, zero_div, sub_zero, sub_self, mul_zero]
    linarith
  have hd : HasDerivAt f (β ^ t * (0 * V' t (1, 0, 0) + -(1 / P t) * V' t (0, 1, 0) +
      0 * V' t (0, 0, 1)) + β ^ (t + 1) * (1 / P (t + 1) * V' (t + 1) (1, 0, 0) +
      0 * V' (t + 1) (0, 1, 0) + 0 * V' (t + 1) (0, 0, 1))) 0 := by
    have hg1 : HasDerivAt (fun δ : ℝ => C₂ t - δ / P t) (-(1 / P t)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).div_const (P t)).const_sub (C₂ t)
      simpa using this
    have hg2 : HasDerivAt (fun δ : ℝ => C₁ (t + 1) + δ / P (t + 1)) (1 / P (t + 1)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).div_const (P (t + 1))).const_add (C₁ (t + 1))
      simpa using this
    have d1 := hasDerivAt_curve3 (f := fun _ => C₁ t) (g := fun δ => C₂ t - δ / P t)
      (h := fun _ => N t) (s := 0) (by simpa using hV t) (hasDerivAt_const 0 (C₁ t)) hg1
      (hasDerivAt_const 0 (N t))
    have d2 := hasDerivAt_curve3 (f := fun δ => C₁ (t + 1) + δ / P (t + 1))
      (g := fun _ => C₂ (t + 1)) (h := fun _ => N (t + 1)) (s := 0)
      (by simpa using hV (t + 1)) hg2 (hasDerivAt_const 0 (C₂ (t + 1)))
      (hasDerivAt_const 0 (N (t + 1)))
    exact ((d1.sub_const _).const_mul (β ^ t)).add ((d2.sub_const _).const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * (1 / P t * V' t (0, 1, 0)) =
      β ^ t * (β * (1 / P (t + 1) * V' (t + 1) (1, 0, 0))) := by linarith
  have h2 := mul_left_cancel₀ hb.ne' h1
  field_simp [(hP t).ne', (hP (t + 1)).ne'] at h2 ⊢
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**KKT multipliers**): with `λ_t = V₂ₜ/P_t` and
`μ_t = (V₁ₜ − V₂ₜ)/P_t`: `V₁ = P(λ + μ)`, `V₂ = Pλ`, `V₃ = −Wλ`, `λ_t Q_t = β λ_{t+1}`,
`λ_t = β(λ_{t+1} + μ_{t+1})`, `μ_t ≥ 0` and `μ_t (M_t + T_t − P_t C₁ₜ) = 0`. -/
theorem kkt (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) :
    ∃ lam mu : ℕ → ℝ, (∀ t, V' t (1, 0, 0) = P t * (lam t + mu t)) ∧
      (∀ t, V' t (0, 1, 0) = P t * lam t) ∧ (∀ t, V' t (0, 0, 1) = -(W t * lam t)) ∧
      (∀ t, lam t * Q t = β * lam (t + 1)) ∧ (∀ t, lam t = β * (lam (t + 1) + mu (t + 1))) ∧
      (∀ t, 0 ≤ mu t) ∧ (∀ t, mu t * (M t + T t - P t * C₁ t) = 0) := by
  refine ⟨fun t => V' t (0, 1, 0) / P t, fun t => (V' t (1, 0, 0) - V' t (0, 1, 0)) / P t,
    fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · field_simp [(hP t).ne']; ring
  · field_simp [(hP t).ne']
  · have := foc_credit_labour hopt hβ hV hC₂ hN hP hW t
    dsimp only
    rw [this]; field_simp [(hW t).ne']
  · dsimp only
    rw [mul_comm, ← mul_div_assoc, foc_bonds hopt hβ hV hC₂ hP t, mul_div_assoc]
  · dsimp only
    rw [foc_money hopt hβ hV hC₁ hC₂ hP t]
    field_simp [(hP (t + 1)).ne']
    ring
  · exact div_nonneg (by linarith [foc_cash_credit_ineq hopt hβ hV hC₁ hC₂ hP t]) (hP t).le
  · rcases (hopt.1 t).2.1.lt_or_eq with hlt | heq
    · have := foc_cash_credit_slack hopt hβ hV hC₁ hC₂ hlt
      change (V' t (1, 0, 0) - V' t (0, 1, 0)) / P t * (M t + T t - P t * C₁ t) = 0
      rw [this, sub_self, zero_div, zero_mul]
    · change (V' t (1, 0, 0) - V' t (0, 1, 0)) / P t * (M t + T t - P t * C₁ t) = 0
      rw [heq, sub_self, mul_zero]

/-! ### (b) The reduced form -/

/-- Galí (2015), Ex. 2.9(b), p. 51: the reduced-form utility `U(C, m, N) = V(m, C − m, N)`
when the CIA binds (`C₁ = m = M/P`). -/
def reducedU (V : ℝ × ℝ × ℝ → ℝ) (C m N : ℝ) : ℝ := V (m, C - m, N)

/-- Galí (2015), Ex. 2.9(b), p. 51: `U_m = V₁ − V₂` (chain rule). -/
theorem hasDerivAt_U_m {V'' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}
    (hV : HasFDerivAt V V'' (m, C - m, N)) :
    HasDerivAt (fun m' => reducedU V C m' N) (V'' (1, 0, 0) - V'' (0, 1, 0)) m := by
  have := hasDerivAt_curve3 (f := fun x => x) (g := fun x => C - x) (h := fun _ => N) (s := m)
    hV (hasDerivAt_id' m) ((hasDerivAt_id' m).const_sub C) (hasDerivAt_const m N)
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.9(b), p. 51: `U_c = V₂`. -/
theorem hasDerivAt_U_c {V'' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}
    (hV : HasFDerivAt V V'' (m, C - m, N)) :
    HasDerivAt (fun C' => reducedU V C' m N) (V'' (0, 1, 0)) C := by
  have := hasDerivAt_curve3 (f := fun _ => m) (g := fun x => x - m) (h := fun _ => N) (s := C)
    hV (hasDerivAt_const C m) ((hasDerivAt_id' C).sub_const m) (hasDerivAt_const C N)
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.9(b), p. 51: `U_n = V₃`. -/
theorem hasDerivAt_U_n {V'' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}
    (hV : HasFDerivAt V V'' (m, C - m, N)) :
    HasDerivAt (fun N' => reducedU V C m N') (V'' (0, 0, 1)) N := by
  have := hasDerivAt_curve3 (f := fun _ => m) (g := fun _ => C - m) (h := fun x => x) (s := N)
    hV (hasDerivAt_const N m) (hasDerivAt_const N (C - m)) (hasDerivAt_id' N)
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.9(b), p. 51: at an optimum `U_m = V₁ − V₂ = P_t μ_t`, with `μ_t` the
CIA multiplier of `kkt`. -/
theorem U_m_eq_mul_mu (hP : ∀ t, 0 < P t) (t : ℕ) :
    V' t (1, 0, 0) - V' t (0, 1, 0) = P t * ((V' t (1, 0, 0) - V' t (0, 1, 0)) / P t) := by
  field_simp [(hP t).ne']

/-- Galí (2015), Ex. 2.9(b), p. 51 (**`U_m ≥ 0`**): at an optimal plan with a binding CIA
(`C₁ₜ = M_t/P_t = m`, `C₂ₜ = C_t − m`), the reduced-form marginal utility of real balances is
`U_m = V₁ − V₂ = P_t μ_t ≥ 0`. -/
theorem U_m_nonneg (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    ∃ Um, HasDerivAt (fun m' => reducedU V (C₁ t + C₂ t) m' (N t)) Um (C₁ t) ∧ 0 ≤ Um := by
  refine ⟨V' t (1, 0, 0) - V' t (0, 1, 0), hasDerivAt_U_m (by simpa using hV t), ?_⟩
  linarith [foc_cash_credit_ineq hopt hβ hV hC₁ hC₂ hP t]

end Gali.ClassicalMonetaryModel.Ex2_9

set_option linter.style.longLine false
#print axioms Gali.ClassicalMonetaryModel.SchurStable
#print axioms Gali.ClassicalMonetaryModel.disc
#print axioms Gali.ClassicalMonetaryModel.root₁
#print axioms Gali.ClassicalMonetaryModel.root₂
#print axioms Gali.ClassicalMonetaryModel.root_sum
#print axioms Gali.ClassicalMonetaryModel.root_prod
#print axioms Gali.ClassicalMonetaryModel.root_eq
#print axioms Gali.ClassicalMonetaryModel.normSq_root_of_neg
#print axioms Gali.ClassicalMonetaryModel.norm_root_of_nonneg
#print axioms Gali.ClassicalMonetaryModel.schurStable_iff_roots
#print axioms Gali.ClassicalMonetaryModel.chSeq
#print axioms Gali.ClassicalMonetaryModel.convSeq
#print axioms Gali.ClassicalMonetaryModel.convSeq_rec
#print axioms Gali.ClassicalMonetaryModel.chSeq_eq_convSeq
#print axioms Gali.ClassicalMonetaryModel.norm_convSeq_le
#print axioms Gali.ClassicalMonetaryModel.abs_chSeq_le
#print axioms Gali.ClassicalMonetaryModel.tendsto_chSeq
#print axioms Gali.ClassicalMonetaryModel.tr2
#print axioms Gali.ClassicalMonetaryModel.det2
#print axioms Gali.ClassicalMonetaryModel.tr2_eq_trace
#print axioms Gali.ClassicalMonetaryModel.det2_eq_det
#print axioms Gali.ClassicalMonetaryModel.sq_eq_cayleyHamilton
#print axioms Gali.ClassicalMonetaryModel.pow_succ_eq
#print axioms Gali.ClassicalMonetaryModel.abs_pow_entry_le
#print axioms Gali.ClassicalMonetaryModel.tendsto_pow_entry
#print axioms Gali.ClassicalMonetaryModel.BoundedSeq
#print axioms Gali.ClassicalMonetaryModel.homogeneous_iterate
#print axioms Gali.ClassicalMonetaryModel.abs_mulVec_le
#print axioms Gali.ClassicalMonetaryModel.homogeneous_eq_zero
#print axioms Gali.ClassicalMonetaryModel.eq_root_of_eq
#print axioms Gali.ClassicalMonetaryModel.exists_eigenvector
#print axioms Gali.ClassicalMonetaryModel.exists_bounded_homogeneous
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.mk
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.E
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.const
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.mono
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.tower
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.known
#print axioms Gali.ClassicalMonetaryModel.perfectForesight
#print axioms Gali.ClassicalMonetaryModel.BoundedProc
#print axioms Gali.ClassicalMonetaryModel.BoundedVec
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.Adapted
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.IsAR1
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.E_neg
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.E_smul
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.E_E_self
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.abs_E_le
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.bounded_E
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.ar1_iterate
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.forward_iterate
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.forward_unique
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.forward_ar1_solves
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.E_tsum
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.forwardSeries
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.forwardSeries_summable
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.forwardSeries_solves
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.forwardSeries_bounded
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.eq_forwardSeries
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.Solves
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.AdaptedVec
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.system_iterate
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.system_unique
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.system_not_unique
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.Determinate
#print axioms Gali.ClassicalMonetaryModel.ExpectationSystem.determinate_iff
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.info
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.num
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinObs
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinTree
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinSystem
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.firstHeads
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinShock
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinAR1
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinShock_measurable
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Gali.ClassicalMonetaryModel.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Gali.ClassicalMonetaryModel.Household.utilC
#print axioms Gali.ClassicalMonetaryModel.Household.disutilN
#print axioms Gali.ClassicalMonetaryModel.Household.periodUtility
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_utilC
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_disutilN
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_periodUtility_C
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_periodUtility_N
#print axioms Gali.ClassicalMonetaryModel.Household.margUtilC_pos
#print axioms Gali.ClassicalMonetaryModel.Household.margUtilN_nonpos
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_margUtilC
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_margUtilN
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_margUtilC_Z
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_margUtilC_N
#print axioms Gali.ClassicalMonetaryModel.Household.mrs_eq
#print axioms Gali.ClassicalMonetaryModel.Household.antitoneOn_margUtil
#print axioms Gali.ClassicalMonetaryModel.Household.le_tangent
#print axioms Gali.ClassicalMonetaryModel.Household.utilC_le_tangent
#print axioms Gali.ClassicalMonetaryModel.Household.utilC_strictMono
#print axioms Gali.ClassicalMonetaryModel.Household.disutilN_tangent_le
#print axioms Gali.ClassicalMonetaryModel.Household.concave_le_tangent
#print axioms Gali.ClassicalMonetaryModel.Household.concave_le_tangent_real
#print axioms Gali.ClassicalMonetaryModel.Household.static_foc_general_necessary
#print axioms Gali.ClassicalMonetaryModel.Household.static_foc_general_iff
#print axioms Gali.ClassicalMonetaryModel.Household.static_foc_general_sufficient
#print axioms Gali.ClassicalMonetaryModel.Household.static_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.Household.static_isLocalMax_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Household.static_foc_sufficient
#print axioms Gali.ClassicalMonetaryModel.Household.static_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.Household.labour_supply_log_iff
#print axioms Gali.ClassicalMonetaryModel.Household.EulerEq
#print axioms Gali.ClassicalMonetaryModel.Household.eulerEq_ratio_form
#print axioms Gali.ClassicalMonetaryModel.Household.perturbedValue
#print axioms Gali.ClassicalMonetaryModel.Household.utility_gain_lower
#print axioms Gali.ClassicalMonetaryModel.Household.euler_necessary
#print axioms Gali.ClassicalMonetaryModel.Household.exists_expenditure_lower_bound
#print axioms Gali.ClassicalMonetaryModel.Household.euler_necessary_finite
#print axioms Gali.ClassicalMonetaryModel.Household.euler_sufficient
#print axioms Gali.ClassicalMonetaryModel.Household.euler_general_necessary
#print axioms Gali.ClassicalMonetaryModel.Household.euler_general_sufficient
#print axioms Gali.ClassicalMonetaryModel.Household.euler_general_ratio
#print axioms Gali.ClassicalMonetaryModel.Household.Economy
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.mk
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.β
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.σ
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.φ
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.P
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.W
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.Dv
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.Q
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.Z
#print axioms Gali.ClassicalMonetaryModel.Household.Economy.b₀
#print axioms Gali.ClassicalMonetaryModel.Household.Plan
#print axioms Gali.ClassicalMonetaryModel.Household.Plan.mk
#print axioms Gali.ClassicalMonetaryModel.Household.Plan.C
#print axioms Gali.ClassicalMonetaryModel.Household.Plan.N
#print axioms Gali.ClassicalMonetaryModel.Household.Plan.B
#print axioms Gali.ClassicalMonetaryModel.Household.lagB
#print axioms Gali.ClassicalMonetaryModel.Household.disc
#print axioms Gali.ClassicalMonetaryModel.Household.disc_zero
#print axioms Gali.ClassicalMonetaryModel.Household.disc_succ
#print axioms Gali.ClassicalMonetaryModel.Household.disc_pos
#print axioms Gali.ClassicalMonetaryModel.Household.Budget
#print axioms Gali.ClassicalMonetaryModel.Household.NoPonzi
#print axioms Gali.ClassicalMonetaryModel.Household.Feasible
#print axioms Gali.ClassicalMonetaryModel.Household.partialUtility
#print axioms Gali.ClassicalMonetaryModel.Household.Optimal
#print axioms Gali.ClassicalMonetaryModel.Household.StaticFOC
#print axioms Gali.ClassicalMonetaryModel.Household.EulerDet
#print axioms Gali.ClassicalMonetaryModel.Household.BudgetBinds
#print axioms Gali.ClassicalMonetaryModel.Household.Transversality
#print axioms Gali.ClassicalMonetaryModel.Household.lam
#print axioms Gali.ClassicalMonetaryModel.Household.eulerDet_iff_lam
#print axioms Gali.ClassicalMonetaryModel.Household.lam_eq_disc
#print axioms Gali.ClassicalMonetaryModel.Household.sum_telescope
#print axioms Gali.ClassicalMonetaryModel.Household.optimal_of_foc
#print axioms Gali.ClassicalMonetaryModel.Household.tsum_le_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Household.gain_nonpos_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Household.sum_range_single
#print axioms Gali.ClassicalMonetaryModel.Household.sum_range_pair
#print axioms Gali.ClassicalMonetaryModel.Household.budgetBinds_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Household.staticFOC_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Household.lagB_update
#print axioms Gali.ClassicalMonetaryModel.Household.eulerDet_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Household.tvc_liminf_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Household.tvc_of_optimal_of_tendsto
#print axioms Gali.ClassicalMonetaryModel.Household.optimal_iff
#print axioms Gali.ClassicalMonetaryModel.Household.bookTVCTerm
#print axioms Gali.ClassicalMonetaryModel.Household.bookTVCTerm_eq
#print axioms Gali.ClassicalMonetaryModel.Household.bookTVC_iff
#print axioms Gali.ClassicalMonetaryModel.Household.tvc_of_zero_bonds
#print axioms Gali.ClassicalMonetaryModel.Household.tvc_of_zero_bonds_stoch
#print axioms Gali.ClassicalMonetaryModel.Household.eulerMoment
#print axioms Gali.ClassicalMonetaryModel.Household.eulerEq_iff_moment
#print axioms Gali.ClassicalMonetaryModel.Household.pf_eulerEq_iff
#print axioms Gali.ClassicalMonetaryModel.Household.pf_eulerEq_iff_noshock
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_E_exp
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_log_E_exp
#print axioms Gali.ClassicalMonetaryModel.Household.eulerKernel
#print axioms Gali.ClassicalMonetaryModel.Household.steadyPoint
#print axioms Gali.ClassicalMonetaryModel.Household.eulerGrad
#print axioms Gali.ClassicalMonetaryModel.Household.eulerGrad_apply
#print axioms Gali.ClassicalMonetaryModel.Household.eulerKernel_steady
#print axioms Gali.ClassicalMonetaryModel.Household.hasFDerivAt_eulerKernel
#print axioms Gali.ClassicalMonetaryModel.Household.eulerKernel_linearisation
#print axioms Gali.ClassicalMonetaryModel.Household.eulerMoment_family
#print axioms Gali.ClassicalMonetaryModel.Household.eulerMoment_family_zero
#print axioms Gali.ClassicalMonetaryModel.Household.linearisedEuler
#print axioms Gali.ClassicalMonetaryModel.Household.hasDerivAt_log_eulerMoment_family
#print axioms Gali.ClassicalMonetaryModel.Household.EulerLogLinear
#print axioms Gali.ClassicalMonetaryModel.Household.linearisedEuler_eq
#print axioms Gali.ClassicalMonetaryModel.Household.linearisedEuler_eq_zero_iff
#print axioms Gali.ClassicalMonetaryModel.Household.pf_eulerEq_imp_eulerLogLinear
#print axioms Gali.ClassicalMonetaryModel.Household.neg_log_le_inv_sub_one
#print axioms Gali.ClassicalMonetaryModel.Household.discount_rate_gap
#print axioms Gali.ClassicalMonetaryModel.Household.discount_rate_gap_isBigO
#print axioms Gali.ClassicalMonetaryModel.Household.MoneyDemand
#print axioms Gali.ClassicalMonetaryModel.Household.moneyDemand_iff_price
#print axioms Gali.ClassicalMonetaryModel.Household.moneyDemand_semielasticity
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.profit
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.hasDerivAt_profit
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.labour_demand_necessary
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.labour_demand_sufficient
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.labour_demand_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.labourDemand
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.labour_demand_unique
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.labour_demand_not_unique_alpha_zero
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.labour_demand_log_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.bigD
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiNa
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiN
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiYa
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiY
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiWa
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiW
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.bigD_pos
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.bigD_zero_counterexample
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.StaticBlock
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.staticBlock_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.staticBlock_exists
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.staticBlock_unique
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.staticBlock_degenerate_no_solution
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.staticBlock_degenerate_many
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.LevelsBlock
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.levelsBlock_iff_log
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.levelsBlock_iff_explicit
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiYa_pos
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiWa_pos
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiNa_pos_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiNa_eq_zero_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.psiNa_neg_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.sign_psiNa
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.rateCoeffA
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.rateCoeffA_neg_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.rateCoeffA_rho_one
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.rateCoeffZ_pos_iff
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.realRate_of_euler
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.realRate_eq
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.realRate_eq_pf
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.Equilibrium
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.EquilibriumUnder
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.equilibrium_allocation
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.neutrality
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.neutrality_across_policies
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.equilibrium_realRate
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.levels_neutrality
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.realBondPrice
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.realBondPrice_neutral
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.welfare
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.welfare_policy_invariant
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.welfare_limit_policy_invariant
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.realRate_no_z_response
#print axioms Gali.ClassicalMonetaryModel.FirmsEquilibrium.equilibrium_of_allocation
#print axioms Gali.ClassicalMonetaryModel.InterestRules.E_of_known
#print axioms Gali.ClassicalMonetaryModel.InterestRules.E_of_adapted_le
#print axioms Gali.ClassicalMonetaryModel.InterestRules.forwardSeries_adapted
#print axioms Gali.ClassicalMonetaryModel.InterestRules.hasDerivAt_affine
#print axioms Gali.ClassicalMonetaryModel.InterestRules.Fisher
#print axioms Gali.ClassicalMonetaryModel.InterestRules.fisher_steadyState_iff
#print axioms Gali.ClassicalMonetaryModel.InterestRules.realRate
#print axioms Gali.ClassicalMonetaryModel.InterestRules.IsMDS
#print axioms Gali.ClassicalMonetaryModel.InterestRules.exoPath
#print axioms Gali.ClassicalMonetaryModel.InterestRules.innov
#print axioms Gali.ClassicalMonetaryModel.InterestRules.innov_isMDS
#print axioms Gali.ClassicalMonetaryModel.InterestRules.exoPath_fisher
#print axioms Gali.ClassicalMonetaryModel.InterestRules.exo_equilibrium_iff
#print axioms Gali.ClassicalMonetaryModel.InterestRules.price_exoPath
#print axioms Gali.ClassicalMonetaryModel.InterestRules.exoPath_bounded
#print axioms Gali.ClassicalMonetaryModel.InterestRules.exoPath_adapted
#print axioms Gali.ClassicalMonetaryModel.InterestRules.zero_isMDS
#print axioms Gali.ClassicalMonetaryModel.InterestRules.dateZeroShock
#print axioms Gali.ClassicalMonetaryModel.InterestRules.dateZeroShock_isMDS
#print axioms Gali.ClassicalMonetaryModel.InterestRules.dateZeroShock_bounded
#print axioms Gali.ClassicalMonetaryModel.InterestRules.exo_two_equilibria
#print axioms Gali.ClassicalMonetaryModel.InterestRules.perfectForesight_isMDS
#print axioms Gali.ClassicalMonetaryModel.InterestRules.perfectForesight_exo_pinned
#print axioms Gali.ClassicalMonetaryModel.InterestRules.coinShock_isMDS
#print axioms Gali.ClassicalMonetaryModel.InterestRules.coinShock_bounded
#print axioms Gali.ClassicalMonetaryModel.InterestRules.coin_exo_sunspot
#print axioms Gali.ClassicalMonetaryModel.InterestRules.Rule
#print axioms Gali.ClassicalMonetaryModel.InterestRules.gap
#print axioms Gali.ClassicalMonetaryModel.InterestRules.Eq24
#print axioms Gali.ClassicalMonetaryModel.InterestRules.rule_fisher_iff_eq24
#print axioms Gali.ClassicalMonetaryModel.InterestRules.fwd25
#print axioms Gali.ClassicalMonetaryModel.InterestRules.forcing25
#print axioms Gali.ClassicalMonetaryModel.InterestRules.fwd25_eq_forwardSeries
#print axioms Gali.ClassicalMonetaryModel.InterestRules.eq24_iff_forward
#print axioms Gali.ClassicalMonetaryModel.InterestRules.forcing25_bound
#print axioms Gali.ClassicalMonetaryModel.InterestRules.forcing25_adapted
#print axioms Gali.ClassicalMonetaryModel.InterestRules.eq25_unique_bounded
#print axioms Gali.ClassicalMonetaryModel.InterestRules.inflation_ar1_closed_form
#print axioms Gali.ClassicalMonetaryModel.InterestRules.combo_bounded_adapted
#print axioms Gali.ClassicalMonetaryModel.InterestRules.infl_closed_form
#print axioms Gali.ClassicalMonetaryModel.InterestRules.inflation_closed_form_book
#print axioms Gali.ClassicalMonetaryModel.InterestRules.inflImpact
#print axioms Gali.ClassicalMonetaryModel.InterestRules.rateImpact
#print axioms Gali.ClassicalMonetaryModel.InterestRules.moneyImpact
#print axioms Gali.ClassicalMonetaryModel.InterestRules.impact_representation
#print axioms Gali.ClassicalMonetaryModel.InterestRules.hasDerivAt_inflImpact
#print axioms Gali.ClassicalMonetaryModel.InterestRules.hasDerivAt_rateImpact
#print axioms Gali.ClassicalMonetaryModel.InterestRules.hasDerivAt_moneyImpact
#print axioms Gali.ClassicalMonetaryModel.InterestRules.inflation_falls
#print axioms Gali.ClassicalMonetaryModel.InterestRules.rate_falls_iff
#print axioms Gali.ClassicalMonetaryModel.InterestRules.liquidity_effect_iff
#print axioms Gali.ClassicalMonetaryModel.InterestRules.path26
#print axioms Gali.ClassicalMonetaryModel.InterestRules.surprise
#print axioms Gali.ClassicalMonetaryModel.InterestRules.surprise_isMDS
#print axioms Gali.ClassicalMonetaryModel.InterestRules.path26_adapted
#print axioms Gali.ClassicalMonetaryModel.InterestRules.path26_eq24
#print axioms Gali.ClassicalMonetaryModel.InterestRules.path26_bounded
#print axioms Gali.ClassicalMonetaryModel.InterestRules.surprise_path26
#print axioms Gali.ClassicalMonetaryModel.InterestRules.eq24_iff_path26
#print axioms Gali.ClassicalMonetaryModel.InterestRules.path26_injective
#print axioms Gali.ClassicalMonetaryModel.InterestRules.eq26_levels
#print axioms Gali.ClassicalMonetaryModel.InterestRules.eq26_multiplicity
#print axioms Gali.ClassicalMonetaryModel.InterestRules.isMDS_fn7
#print axioms Gali.ClassicalMonetaryModel.InterestRules.fn7_surprise
#print axioms Gali.ClassicalMonetaryModel.InterestRules.Determinate24
#print axioms Gali.ClassicalMonetaryModel.InterestRules.homPath
#print axioms Gali.ClassicalMonetaryModel.InterestRules.E_homPath
#print axioms Gali.ClassicalMonetaryModel.InterestRules.eq24_add_homPath
#print axioms Gali.ClassicalMonetaryModel.InterestRules.not_unique_of_le_one
#print axioms Gali.ClassicalMonetaryModel.InterestRules.taylor_principle
#print axioms Gali.ClassicalMonetaryModel.InterestRules.phi_one_no_bounded_solution
#print axioms Gali.ClassicalMonetaryModel.InterestRules.fwd25_ar1_hasSum
#print axioms Gali.ClassicalMonetaryModel.InterestRules.ar1_solution_eq24
#print axioms Gali.ClassicalMonetaryModel.InterestRules.c2_3_forward_converges_not_unique
#print axioms Gali.ClassicalMonetaryModel.InterestRules.PrintedDivergence
#print axioms Gali.ClassicalMonetaryModel.InterestRules.printed_divergence_false
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.MoneyDemand
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.InflationId
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.uDef
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.Eq27
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.eq27_of_model
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.fisher_of_eq27
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.forwardSeries_smul_add
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.fwd28
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.coef_bounds
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.eq28_unique
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.w29
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.eq27_iff_tilde
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.fwd29
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.fwd29_eq
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.eq29_unique
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.interest_rate_29
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.ar1_series29
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.ar1_money_equilibrium
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.priceImpactM
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.moneyImpactM
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.rateImpactM
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.impact_representationM
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.hasDerivAt_priceImpactM
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.hasDerivAt_moneyImpactM
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.hasDerivAt_rateImpactM
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.price_overshoots_iff
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.price_overshoots
#print axioms Gali.ClassicalMonetaryModel.MoneySupply.no_liquidity_effect_iff
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.budget_rewrite
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.price_of_money_services
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.one_sub_exp_neg_le
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.mul_exp_neg_le_one_sub_exp_neg
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.miu_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.utilPow
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.hasDerivAt_utilPow
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.le_tangent
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.utilPow_le_tangent
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.sepUtil
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.hasDerivAt_sepUtil_C
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.hasDerivAt_sepUtil_N
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.hasDerivAt_perturbation
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.miu_static_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.foc_iff_ratio
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.miu_static_optimum_iff_exp
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.money_demand_iff
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.no_money_demand_of_nonpos
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.logMoneyDemand
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.eta
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.log_money_demand
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.hasDerivAt_log_one_sub_exp_neg
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.hasFDerivAt_logMoneyDemand
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.eta_pos
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.eta_le
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.exp_neg_div_le_eta
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.hasFDerivAt_logMoneyDemand_unit
#print axioms Gali.ClassicalMonetaryModel.MIUSeparable.money_demand_unit_elastic
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.composite
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.composite_pos
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.composite_homogeneous
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_composite_path
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.nsUtil
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_nsUtil_path
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_nsUtil_C
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_nsUtil_m
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.um_div_uc
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.mrs_eq
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.labour_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.labour_supply_nu_eq_sigma
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.labour_supply_log
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.money_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.moneyDemand39
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.money_demand_39_iff
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.moneyDemand39_homogeneous
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.log_moneyDemand39
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasFDerivAt_log_money_demand_40
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.share
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.logX
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.logX_homogeneous
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_logX_zero
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasFDerivAt_gap
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.km
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.chi
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.chi1
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.km_pos
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.km_money_demand
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.share_at_km
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.chi1_eq_chi
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.chi_mem
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_logX_steady_state
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.eta_steady_state
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.varpi
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.varpi_eq
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.varpi_pos_iff
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.eq41
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.bigD
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.psiYa
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.psiYi
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.eq43
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.psiYi_neg_iff
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.tendsto_psiYi_nu
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.psiYi_limit_calib
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.tendsto_calib_beta_one
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.calibLimit
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.psiYi_limit_km_base
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.psiYi_limit_km_m2
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.Theta
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.Lambda
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.eq44_45
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.Theta_mem
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.Lambda_nonneg
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.coef_identity
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.uc_ratio
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.MIUEuler
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.euler5_iff_miuEuler
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.miuEuler_nu_eq_sigma
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.miuMoment
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.miuEuler_iff_moment
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.pf_miuEuler_iff
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_E_exp
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_log_E_exp
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.linearisedMIUEuler
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.miuMoment_family_zero
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.hasDerivAt_log_miuMoment_family
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.EulerGap
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.EulerLinear
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.linearisedMIUEuler_eq_zero_iff
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.eulerGap_iff_eulerLinear
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.eq47_of_clearing
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.real_balance_eq_iff_real
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.solve_forward
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.real_balance_eq_iff
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.forwardSeries_adapted
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.forcing_bounded_adapted
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.forwardSeries_money
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.price_level_48
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.price_level_48_exists
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.real_wage_countercyclical
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.real_wage_strictly_countercyclical
#print axioms Gali.ClassicalMonetaryModel.MIUNonseparable.real_wage_acyclical_of_alpha_zero
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.planner_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.planner_foc_ratio
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.tangent_of_deriv
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.production_le_tangent
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.planner_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.no_planner_optimum_isoelastic
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.decentralised_49
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.one_sub_exp_neg_eq_zero_iff
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.decentralised_efficient_iff
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.decentralised_optimal_iff_friedman
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.friedman_steady_state_inflation
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.friedman_euler_iff
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.friedman_equilibrium_iff
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.friedman_indeterminate
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.friedman_sunspot_coin
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.s_eq
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.s_nonneg
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.RuleSystem
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.rule_real
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.ruleSystem_iff
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.fn13_unique
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.fn13_exists
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.fn13_not_unique
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.lagged_rule_unique
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.lagged_rule_exists
#print axioms Gali.ClassicalMonetaryModel.FriedmanRule.inflation_rule_implies_zero_rate
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.utilC
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_utilC
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.utilC_strictMonoOn
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.le_tangent
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.tangent_of_deriv
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.periodUtility
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.margUtilC
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.margUtilN
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_periodUtility_C
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_leisure_pow
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_periodUtility_N
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.margUtilC_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.margUtilC_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.mrs_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.static_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.static_wage_necessary
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.static_foc_sufficient
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.static_isLocalMax_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.static_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.labour_supply_log_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_neg_log_one_sub_exp
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_labourSupply_family
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_E_of_uniform
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.uniform_of_concave
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.uniformCont_of_finite
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.euler_necessary_generic
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.euler_sufficient_generic
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.EulerEq
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.perturbedValue
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.margUtilC_antitoneOn
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.margUtilC_continuousAt
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.euler_necessary
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.euler_necessary_finite
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.euler_sufficient
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.eulerMoment
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.margUtilC_exp
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.eulerEq_iff_moment
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.pf_eulerEq_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.uniform_comp_line
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.uniform_exp
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.linearisedEuler
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.eulerMoment_family_zero
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.hasDerivAt_moment_family
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.E_linearisedEuler
#print axioms Gali.ClassicalMonetaryModel.Ex2_1.linearisedEuler_zero_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.E_sub_const
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.forwardSeries_adapted
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.forwardSeries_smul_apply
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.Fisher
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.StrictITRule
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.strictIT_solves
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.strictIT_unique
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.strictIT_not_unique
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.strictIT_sunspot
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.strictIT_money_growth
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.constMoneyGrowth_inflation
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.constMoneyGrowth_not_stabilising
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.pstar
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.pstar_succ
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.devPL
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.FisherP
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.PLEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.E_devPL
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.plEquilibrium_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.plEquilibrium_unique_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.plEquilibrium_exists
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.pl_ar1
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.hint_constant_target_unbounded
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.moneyPath_eq_pstar
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.MoneyEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.moneyForcing
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.moneyEquilibrium_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.moneyEquilibrium_unique_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.moneyEquilibrium_exists
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.moneyRule_as_interestRule
#print axioms Gali.ClassicalMonetaryModel.Ex2_2.moneyEquilibrium_iff_interestRule
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.exists_bounded_forward
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.SolvesPred
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.known_succ
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pred_known
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.saddle_z_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.saddle_unique
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.kPath
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.kPath_bounded
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.saddle_exists
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.leftEigen_of_b12
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.stable_not_unique
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.BothOutside
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.schurStable_inv_of_bothOutside
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.bothOutside_roots
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.outside_nonexistence
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.lagI
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.lagI_zero
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.lagI_succ
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.PAEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_iff_system
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_i_adapted
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.lag_bounded
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.E_zero_k0
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_unique
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_exists
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_interest_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_interest_forward
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_inflation_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.PADeterminate
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_two_solutions
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_not_determinate
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_determinate_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_determinate_iff_of_nonneg
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_phi_i_one_not_determinate
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_boundary_nonexistence
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.extInfl
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.maBar
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.hbar
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.maBar_succ
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.extInfl_nat
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.extInfl_neg
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.maBar_neg_one
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.extInfl_bounded
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.ma_iff_pa
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.MAEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.ma_equilibrium_iff_pa
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.pa_as_ma
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.hbar_bounded
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.hbar_known
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.MADeterminate
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.ma_determinate_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_3.ma_determinate_iff_of_nonneg
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.psi
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.aggX
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.periodUtility
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.aggX_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.aggX_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.inv_aggX
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.margUtilC
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.margUtilM
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_aggX_C
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_aggX_M
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_periodUtility_C
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_periodUtility_M
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.mrs_money
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.swapValue
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_swap_aggX
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.money_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.inv_tangent
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.money_foc_sufficient
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.money_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.money_demand_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.no_money_foc_at_zero_rate
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.money_demand_log
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_money_demand_log
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.EulerEq
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.perturbedValue
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.margUtilC_antitoneOn
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.margUtilC_continuousAt
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.euler_necessary
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.euler_necessary_finite
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.euler_sufficient
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.sRate
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.zDemand
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.eqWelfare
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.one_sub_exp_neg_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.zDemand_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.sRate_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.chi_div_zDemand
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.eqWelfare_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.sRate_strictMonoOn
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.sRate_continuous
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.friedman_rule
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.friedman_rule_inflation
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.inv_aggX_demand
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCostLevels
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.indifference_levels_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCost_levels
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCost_levels_unique
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCost_levels_none
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCostRatio
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCost_ratio
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCost_ratio_unique
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCost_ratio_pos_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfareCost_levels_pos_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.Wf
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.eqWelfare_one_eq_Wf
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.sDeriv
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.sDeriv2
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.W1
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.W2
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_sRate
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_sDeriv
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_W
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.hasDerivAt_W1
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.contDiffOn_W
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.deriv_deriv_W
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfare_taylor
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.welfare_fluctuations
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.W2_pos_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.W2_pos_of_le_two
#print axioms Gali.ClassicalMonetaryModel.Ex2_4.fluctuations_raise_welfare
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.utility
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.hasDerivAt_utility_C
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.hasDerivAt_utility_m
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.hasDerivAt_utility_N
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.le_tangent
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.disutil_tangent_le
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.hasDerivAt_disutil
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.log_le_tangent
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.labour_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.labour_foc_sufficient
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.labour_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.money_foc_necessary
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.money_foc_sufficient
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.money_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.firm_optimum_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.level
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.level_succ
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.level_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.GaussianInnovations
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.GaussianInnovations.mk
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.GaussianInnovations.ε
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.GaussianInnovations.var
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.GaussianInnovations.adapted
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.GaussianInnovations.hasLaw
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.GaussianInnovations.indep
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.eulerRHS
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.mk
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.pos_C
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.pos_N
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.pos_P
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.labour
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.money
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.euler
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.firm
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.technology
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.IsEquilibrium.clearing
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.employment_eq_one
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.output_eq_technology
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.velocity_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.condExp_money_ratio
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.Qstar
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.velocity
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.eulerRHS_of_const_velocity
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.velocity_of_constant
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.qstar_lt_one_of_equilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.candidate_isEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.inflation_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.log_inflation_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.nominalRate_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.qstar_le_one_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.friedman_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.not_equilibrium_at_friedman
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.period_utility_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.integral_log_level
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.welfareValue
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.hasSum_expected_welfare
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.welfareValue_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.welfareValue_lt_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.welfare_strictAnti_gamma
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.welfare_strictMono_var
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.welfare_rate_strictAnti
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.tendsto_welfare_rate
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.not_optimal_of_equilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.log_level_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.integrable_innovation
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.integral_abs_innovation
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.integral_tsum_welfare
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.pairLaw
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.shockMeasure
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.shockFiltration
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.coord_indep
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.comap_le_shockFiltration
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.techInnovations
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.moneyInnovations
#print axioms Gali.ClassicalMonetaryModel.Ex2_5.exists_exact_equilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.bigD
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.psiYA
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.psiYI
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.cCoef
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.rhs47
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.forcing
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.IsEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.IsEquilibrium.mk
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.IsEquilibrium.eq43
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.IsEquilibrium.eq47
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.IsEquilibrium.rule
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.InflEq
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.eq43_apply
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.rule_apply
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.eq47_apply_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.inflEq_of_isEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.isEquilibrium_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.expected_infl_eq_c
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.kappa_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.kappa_nonneg
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.one_lt_abs_c_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.unique_of_one_lt_abs_c
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.exists_equilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.not_unique_of_le_one
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.zero_isEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.determinate_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.counterexample_negative_phi
#print axioms Gali.ClassicalMonetaryModel.Ex2_6.unique_negative_phi
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.shoppingU
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_curve
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_sections
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_U_c
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_U_m
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_U_n
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.U_m_nonneg
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.U_n_neg
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.U_c_lt_V_C
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.U_c_sign_ambiguous
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_section_m
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_U_mm
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.U_mm_nonpos
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_U_nn
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_U_nm
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.U_nm_nonneg
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.labour_foc
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.money_foc
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.shopping_rate_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_one_sub_exp_neg
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.shopping_rate_approx
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.sguS
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.hasDerivAt_S_m
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.S_mul_v
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.S_nonneg
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.S_eq_zero_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.S_m_nonpos_iff
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.money_demand
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.money_demand_of_hasFDerivAt
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.money_demand_strictAnti
#print axioms Gali.ClassicalMonetaryModel.Ex2_7.money_demand_satiation
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.u
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.hasDerivAt_disutil
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.nonneg_of_left_max
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.Budget
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.CIA
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.Feasible
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.Optimal
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.optimal_of_tsum_max
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.gain_nonpos
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.foc_labour_money
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.foc_labour_bonds
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.cia_family_feasible
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.hasDerivAt_cia_family
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.foc_cia_ineq
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.foc_cia_slack
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.kkt
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.disc
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.disc_succ
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.disc_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.NoPonzi
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.OptimalNP
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.optimal_of_optimalNP
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.tvc_liminf_of_optimalNP
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.le_tangent
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.u_le_tangent
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.lamD
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.muD
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.budget_binds_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.overtakes_of_foc
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.mk
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.pos_C
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.pos_N
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.pos_P
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.focI
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.focII
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.focIII
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.slack
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.cia
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.firm
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.clearing
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.IsEquilibrium.money
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.isEquilibrium_of_optimal
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.Q_le_one
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.cia_binds_of_Q_lt_one
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.output_of_binding
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.output_eq
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.output_strictAnti
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.stationary_isEquilibrium
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.stationary_inflation
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.EqTVC
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.eqTVC_of_optimalNP
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.Q_pos
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.employment_one_of_slack
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.slack_succ
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.Q_eq_one_of_slack
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.cia_binds_of_tvc
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.output_eq_of_tvc
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.slack_equilibrium_counterexample
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.stationary_utility_le
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.hasSum_welfare
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.optimal_inflation
#print axioms Gali.ClassicalMonetaryModel.Ex2_8.friedman_at_optimum
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.hasDerivAt_curve3
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.nonneg_of_left_max
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.Budget
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.CIA
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.Feasible
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.Optimal
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.optimal_of_tsum_max
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.gain_nonpos
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.foc_credit_labour
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.cash_credit_feasible
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.hasDerivAt_cash_credit
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.foc_cash_credit_ineq
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.foc_cash_credit_slack
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.foc_bonds
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.foc_money
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.kkt
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.reducedU
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.hasDerivAt_U_m
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.hasDerivAt_U_c
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.hasDerivAt_U_n
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.U_m_eq_mul_mu
#print axioms Gali.ClassicalMonetaryModel.Ex2_9.U_m_nonneg
