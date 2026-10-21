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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Basic
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

namespace Cochrane.TwoPeriodModel

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

end Cochrane.TwoPeriodModel

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

namespace Cochrane.TwoPeriodModel

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

end Cochrane.TwoPeriodModel

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

namespace Cochrane.TwoPeriodModel.ExpectationsFiniteTree

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

end Cochrane.TwoPeriodModel.ExpectationsFiniteTree

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

namespace Cochrane.TwoPeriodModel.ForwardSolution

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

end Cochrane.TwoPeriodModel.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The last day and the two-period model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.1–1.3, pp. 4–8.

## The setting

Dates `0` and `1` inside an arbitrary `ExpectationSystem Ω` (`E_0`, `E_1`), so every result holds
under perfect foresight and under genuine uncertainty (`coin_equilibrium`). Random variables are
functions `Ω → ℝ`; all equations are equalities of functions (state by state). Date-0 variables
(`B_{−1}`, `B_0`, `s_0`, `P_0`) are `Known` at date 0: `E_0 x = x`. The date-1 surplus `s_1` and
price level `P_1` are random. Results that pull date-0 quantities out of `E_0` assume the
pull-out property `PullOut` (true for perfect foresight and every finite event tree).

## The fiscal-theory equilibrium notion

`Equilibrium 𝔼 β B₋₁ B₀ s₀ s₁ P₀ P₁ Q₀`: given fiscal policy and the debt sale `(B₋₁, B₀, s₀, s₁)`,
prices `(P₀, P₁, Q₀)` with `P₀, P₁ > 0` statewise, `P₀` known at date 0, the date-0 flow
condition (1.2), the bond-pricing equation (1.3) and the date-1 valuation equation (1.1)/(1.4).
"The price level is determined" means: there is exactly one such triple
(`equilibrium_existsUnique`), namely `P₁ = B₀/s₁`, `P₀ = B₋₁/(s₀ + βE₀s₁)` (`equilibrium_iff`).

## Main results

* (1.1), p. 4: `lastDay_iff` (`B₀ = P₁s₁ ↔ B₀/P₁ = s₁`), `lastDay_existsUnique`,
  `lastDay_none` (error E3: with `s₁ ≤ 0` there is no positive price level).
* p. 5: `excess_money_iff`, `money_shortage_iff` ("too much money chasing too few goods").
* p. 4, p. 7: `propTax_real` (a proportional tax makes `s₁ = τy₁` independent of `P₁`).
* (1.2)–(1.3), p. 8: `Flow0`, `BondPrice0`, `rate`, `bondPrice_eq_inv_one_add_rate`,
  `bondPrice_R`; the unnumbered display `flow_real`.
* (1.4)–(1.5), p. 8: `revenue_eq`, `valuation0_of_flow`, `flow_iff_valuation0`.
* Existence and uniqueness: `equilibrium_iff`, `equilibrium_existsUnique`; non-existence
  (error E3): `no_equilibrium_of_s1_nonpos`, `no_equilibrium_of_pv_nonpos`.
* Box p. 7 / p. 8: `price0_strictAnti_beta` (a lower `β` raises `P₀` with unchanged
  surpluses), `price0_strictAnti_Es1` (bad fiscal news raises `P₀`), `price0_eq_of_pv_eq`
  (`P₀` depends on surpluses only through their present value), `price0_any_level`
  (any deficit or surplus `s₀` is compatible with any price level).
* Genuine uncertainty: `coin_equilibrium` (a coin-flip economy with a random `P₁`).
-/

namespace Cochrane.TwoPeriodModel.TwoPeriod

open Cochrane.TwoPeriodModel.ExpectationsFiniteTree

variable {Ω : Type*}

/-! ### Information: variables known at a date -/

/-- Cochrane (2023), §1.3, p. 8: a random variable is known at date `t` when `E_t x = x`
(date-0 quantities `B₋₁, B₀, s₀, P₀` are known at date 0). -/
def Known (𝔼 : ExpectationSystem Ω) (t : ℕ) (x : Ω → ℝ) : Prop := 𝔼.E t x = x

/-- Cochrane (2023), §1.3, p. 8: constants are known at every date. -/
theorem known_const (𝔼 : ExpectationSystem Ω) (t : ℕ) (c : ℝ) :
    Known 𝔼 t (fun _ => c) :=
  𝔼.const t c

/-- Cochrane (2023), §1.3, p. 8: a conditional expectation `E_t x` is known at date `t`. -/
theorem known_E (𝔼 : ExpectationSystem Ω) (t : ℕ) (x : Ω → ℝ) : Known 𝔼 t (𝔼.E t x) :=
  𝔼.E_E_self t x

/-- Cochrane (2023), §1.4, p. 10: what is known at date `s` is known at every later date. -/
theorem known_mono (𝔼 : ExpectationSystem Ω) {s t : ℕ} (hst : s ≤ t) {x : Ω → ℝ}
    (hx : Known 𝔼 s x) : Known 𝔼 t x := by
  unfold Known at *
  have h := 𝔼.known hst x
  rw [hx] at h
  exact h

/-- Cochrane (2023), §1.3, p. 8: sums of known variables are known. -/
theorem known_add (𝔼 : ExpectationSystem Ω) {t : ℕ} {x y : Ω → ℝ} (hx : Known 𝔼 t x)
    (hy : Known 𝔼 t y) : Known 𝔼 t (x + y) := by
  unfold Known at *
  rw [map_add, hx, hy]

/-- Cochrane (2023), §1.3, p. 8: differences of known variables are known. -/
theorem known_sub (𝔼 : ExpectationSystem Ω) {t : ℕ} {x y : Ω → ℝ} (hx : Known 𝔼 t x)
    (hy : Known 𝔼 t y) : Known 𝔼 t (x - y) := by
  unfold Known at *
  rw [map_sub, hx, hy]

/-- Cochrane (2023), §1.3, p. 8: multiples of known variables are known. -/
theorem known_smul (𝔼 : ExpectationSystem Ω) {t : ℕ} (c : ℝ) {x : Ω → ℝ}
    (hx : Known 𝔼 t x) : Known 𝔼 t (c • x) := by
  unfold Known at *
  rw [map_smul, hx]

/-- Cochrane (2023), §1.3, p. 8: under `PullOut`, products of known variables are known. -/
theorem known_mul (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {t : ℕ} {x y : Ω → ℝ}
    (hx : Known 𝔼 t x) (hy : Known 𝔼 t y) : Known 𝔼 t (x * y) := by
  unfold Known at *
  rw [hP t x y hx, hy]

/-- Cochrane (2023), §1.3, p. 8: under `PullOut`, the reciprocal of a nowhere-zero
random variable known at `t` is known at `t`. -/
theorem known_inv (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {t : ℕ} {x : Ω → ℝ}
    (hx : Known 𝔼 t x) (hx0 : ∀ ω, x ω ≠ 0) : Known 𝔼 t x⁻¹ := by
  have h1 : x * x⁻¹ = fun _ => (1 : ℝ) := by
    funext ω
    simp only [Pi.mul_apply, Pi.inv_apply]
    exact mul_inv_cancel₀ (hx0 ω)
  have h2 := hP t x x⁻¹ hx
  rw [h1, 𝔼.const] at h2
  funext ω
  have h3 := congrFun h2 ω
  simp only [Pi.mul_apply] at h3
  simp only [Pi.inv_apply]
  field_simp [hx0 ω]
  linarith

/-- Cochrane (2023), §1.3, p. 8: under `PullOut`, quotients of known variables (nowhere-zero
denominator) are known. -/
theorem known_div (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {t : ℕ} {x y : Ω → ℝ}
    (hx : Known 𝔼 t x) (hy : Known 𝔼 t y) (hy0 : ∀ ω, y ω ≠ 0) : Known 𝔼 t (x / y) := by
  rw [div_eq_mul_inv]
  exact known_mul 𝔼 hP hx (known_inv 𝔼 hP hy hy0)

/-! ### §1.1–1.2: the last day -/

/-- Cochrane (2023), §1.1, p. 4: "cash printed in the morning must be soaked up by taxes",
`B₀ = P₁s₁`, is (1.1) `B₀/P₁ = s₁` whenever `P₁ ≠ 0`. -/
theorem lastDay_iff {B0 P1 s1 : ℝ} (hP : P1 ≠ 0) : B0 = P1 * s1 ↔ B0 / P1 = s1 := by
  rw [div_eq_iff hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (1.1), p. 4: with `B₀ > 0` and a positive real surplus `s₁ > 0` there is
exactly one positive price level solving `B₀/P₁ = s₁`, namely `P₁ = B₀/s₁`. -/
theorem lastDay_existsUnique {B0 s1 : ℝ} (hB : 0 < B0) (hs : 0 < s1) :
    ∃! P1 : ℝ, 0 < P1 ∧ B0 / P1 = s1 := by
  refine ⟨B0 / s1, ⟨div_pos hB hs, by field_simp⟩, fun P1 hP1 => ?_⟩
  obtain ⟨hpos, h⟩ := hP1
  rw [div_eq_iff hpos.ne'] at h
  rw [eq_div_iff hs.ne']
  linarith

/-- Cochrane (2023), eq. (1.1), p. 4: the price level is `P₁ = B₀/s₁`. -/
theorem lastDay_eq {B0 P1 s1 : ℝ} (hP : P1 ≠ 0) (hs : s1 ≠ 0) (h : B0 / P1 = s1) :
    P1 = B0 / s1 := by
  rw [div_eq_iff hP] at h
  rw [eq_div_iff hs]
  linarith

/-- Cochrane (2023), eq. (1.1), p. 4 (error E3, missing hypothesis): if `B₀ > 0` and the real
surplus is not positive, `s₁ ≤ 0`, no positive price level satisfies (1.1). -/
theorem lastDay_none {B0 s1 : ℝ} (hB : 0 < B0) (hs : s1 ≤ 0) :
    ¬ ∃ P1 : ℝ, 0 < P1 ∧ B0 / P1 = s1 := by
  rintro ⟨P1, hP1, h⟩
  have : 0 < B0 / P1 := div_pos hB hP1
  linarith

/-- Cochrane (2023), §1.2, p. 5: money left over after taxes, `M₁ = B₀ − P₁s₁`, is positive
("too much money chasing too few goods") exactly when the price level is below its equilibrium
value `B₀/s₁` (`P₁, s₁ > 0`). -/
theorem excess_money_iff {B0 P1 s1 : ℝ} (hs : 0 < s1) :
    0 < B0 - P1 * s1 ↔ P1 < B0 / s1 := by
  rw [lt_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §1.2, p. 5: conversely, taxes exceed the cash printed, `B₀ − P₁s₁ < 0`,
exactly when the price level is above `B₀/s₁` (`s₁ > 0`). -/
theorem money_shortage_iff {B0 P1 s1 : ℝ} (hs : 0 < s1) :
    B0 - P1 * s1 < 0 ↔ B0 / s1 < P1 := by
  rw [div_lt_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §1.1, p. 4, and §1.8, pp. 17–18: with a proportional income tax,
`P₁s₁ = τP₁y₁`, the real surplus `s₁ = τy₁` does not depend on the price level (`P₁ ≠ 0`). -/
theorem propTax_real {P1 s1 τ y1 : ℝ} (hP : P1 ≠ 0) (h : P1 * s1 = τ * P1 * y1) :
    s1 = τ * y1 := by
  have h' : P1 * s1 = P1 * (τ * y1) := by rw [h]; ring
  exact mul_left_cancel₀ hP h'

/-! ### §1.3: the two-period model -/

/-- Cochrane (2023), eq. (1.1)/(1.4), pp. 4, 8: the date-1 valuation equation `B₀/P₁ = s₁`
(state by state). -/
def Valuation1 (B0 P1 s1 : Ω → ℝ) : Prop := B0 / P1 = s1

/-- Cochrane (2023), eq. (1.2), p. 8: the date-0 flow condition `B₋₁ = P₀s₀ + Q₀B₀`. -/
def Flow0 (Bm1 P0 s0 Q0 B0 : Ω → ℝ) : Prop := Bm1 = P0 * s0 + Q0 * B0

/-- Cochrane (2023), eq. (1.3), p. 8: the bond-pricing equation `Q₀ = βE₀(P₀/P₁)`. -/
def BondPrice0 (𝔼 : ExpectationSystem Ω) (β : ℝ) (P0 P1 Q0 : Ω → ℝ) : Prop :=
  Q0 = β • 𝔼.E 0 (P0 / P1)

/-- Cochrane (2023), eq. (1.3), p. 8: the nominal interest rate `i₀` defined by
`Q₀ = 1/(1 + i₀)`, i.e. `i₀ = 1/Q₀ − 1`. -/
noncomputable def rate (Q0 : Ω → ℝ) : Ω → ℝ := fun ω => 1 / Q0 ω - 1

/-- Cochrane (2023), eq. (1.3), p. 8, first equality: `Q₀ = 1/(1 + i₀)`. -/
theorem bondPrice_eq_inv_one_add_rate (Q0 : Ω → ℝ) (ω : Ω) :
    Q0 ω = 1 / (1 + rate Q0 ω) := by
  simp only [rate, add_sub_cancel, one_div, inv_inv]

/-- Cochrane (2023), eq. (1.3), p. 8, third equality: with `β = 1/R`,
`βE₀(P₀/P₁) = (1/R)E₀(P₀/P₁)`. -/
theorem bondPrice_R (𝔼 : ExpectationSystem Ω) {β R : ℝ} (hR : β = 1 / R) (P0 P1 Q0 : Ω → ℝ) :
    BondPrice0 𝔼 β P0 P1 Q0 ↔ Q0 = (1 / R) • 𝔼.E 0 (P0 / P1) := by
  rw [BondPrice0, hR]

/-- Cochrane (2023), eq. (1.5), p. 8: the government debt valuation equation
`B₋₁/P₀ = s₀ + βE₀s₁`. -/
def Valuation0 (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 P0 s0 s1 : Ω → ℝ) : Prop :=
  Bm1 / P0 = s0 + β • 𝔼.E 0 s1

/-- Cochrane (2023), eq. (1.5), p. 8: the present value of surpluses `s₀ + βE₀s₁`. -/
noncomputable def pv (𝔼 : ExpectationSystem Ω) (β : ℝ) (s0 s1 : Ω → ℝ) : Ω → ℝ :=
  s0 + β • 𝔼.E 0 s1

/-- Cochrane (2023), §1.3, p. 8: the present value is known at date 0 when `s₀` is. -/
theorem known_pv (𝔼 : ExpectationSystem Ω) (β : ℝ) {s0 : Ω → ℝ} (hs0 : Known 𝔼 0 s0)
    (s1 : Ω → ℝ) : Known 𝔼 0 (pv 𝔼 β s0 s1) :=
  known_add 𝔼 hs0 (known_smul 𝔼 β (known_E 𝔼 0 s1))

/-- Cochrane (2023), §1.3, p. 8 (unnumbered display after (1.3)): substituting the bond price
into the flow condition, `B₋₁/P₀ = s₀ + βE₀(1/P₁)B₀` (`P₀ > 0`; `P₀, B₀` known at 0;
`PullOut`). -/
theorem flow_real (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 P0 P1 Q0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0)
    (hflow : Flow0 Bm1 P0 s0 Q0 B0) (hQ : BondPrice0 𝔼 β P0 P1 Q0) :
    Bm1 / P0 = s0 + β • 𝔼.E 0 (1 / P1) * B0 := by
  have hpo : 𝔼.E 0 (P0 / P1) = P0 * 𝔼.E 0 (1 / P1) := by
    rw [← hP 0 P0 _ hkP0]
    congr 1
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]
    ring
  funext ω
  have h1 := congrFun hflow ω
  have h2 := congrFun hpo ω
  rw [hQ] at h1
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply] at h1 h2 ⊢
  rw [h2] at h1
  have := (hP0 ω).ne'
  rw [h1]
  field_simp

/-- Cochrane (2023), eq. (1.8), p. 9 / §1.3, p. 8: bond sales raise nominal revenue
`Q₀B₀ = P₀ · βE₀s₁` when `Q₀ = βE₀(P₀/P₁)` and `B₀/P₁ = s₁` (`P₀, B₀` known at 0; `PullOut`). -/
theorem revenue_eq (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {B0 s1 P0 P1 Q0 : Ω → ℝ} (hkP0 : Known 𝔼 0 P0) (hkB0 : Known 𝔼 0 B0)
    (hQ : BondPrice0 𝔼 β P0 P1 Q0) (h1 : Valuation1 B0 P1 s1) :
    Q0 * B0 = P0 * (β • 𝔼.E 0 s1) := by
  rw [hQ]
  have e1 : 𝔼.E 0 (B0 * (P0 / P1)) = B0 * 𝔼.E 0 (P0 / P1) := hP 0 B0 _ hkB0
  have e2 : 𝔼.E 0 (P0 * s1) = P0 * 𝔼.E 0 s1 := hP 0 P0 _ hkP0
  have e3 : B0 * (P0 / P1) = P0 * s1 := by
    rw [← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring
  rw [e3, e2] at e1
  funext ω
  have := congrFun e1 ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  linear_combination (-β) * this

/-- Cochrane (2023), eqs. (1.2)–(1.5), p. 8: the flow condition (1.2), the bond price (1.3)
and date-1 equilibrium (1.4) imply the government debt valuation equation (1.5)
`B₋₁/P₀ = s₀ + βE₀s₁` (`P₀ > 0`; `P₀, B₀` known at 0; `PullOut`). -/
theorem valuation0_of_flow (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0)
    (hkB0 : Known 𝔼 0 B0) (hflow : Flow0 Bm1 P0 s0 Q0 B0) (hQ : BondPrice0 𝔼 β P0 P1 Q0)
    (h1 : Valuation1 B0 P1 s1) : Valuation0 𝔼 β Bm1 P0 s0 s1 := by
  have hr := revenue_eq 𝔼 hP hkP0 hkB0 hQ h1
  funext ω
  have e1 := congrFun hflow ω
  have e2 := congrFun hr ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply] at e1 e2 ⊢
  have := (hP0 ω).ne'
  rw [e1, e2]
  field_simp

/-- Cochrane (2023), eqs. (1.2)–(1.5), p. 8: given (1.3) and (1.4), the flow condition (1.2)
and the valuation equation (1.5) are equivalent (`P₀ > 0`; `P₀, B₀` known at 0; `PullOut`). -/
theorem flow_iff_valuation0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0)
    (hkB0 : Known 𝔼 0 B0) (hQ : BondPrice0 𝔼 β P0 P1 Q0) (h1 : Valuation1 B0 P1 s1) :
    Flow0 Bm1 P0 s0 Q0 B0 ↔ Valuation0 𝔼 β Bm1 P0 s0 s1 := by
  refine ⟨fun hflow => valuation0_of_flow 𝔼 hP hP0 hkP0 hkB0 hflow hQ h1, fun hv => ?_⟩
  have hr := revenue_eq 𝔼 hP hkP0 hkB0 hQ h1
  funext ω
  have e1 := congrFun hv ω
  have e2 := congrFun hr ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply] at e1 e2 ⊢
  have := (hP0 ω).ne'
  rw [div_eq_iff this] at e1
  rw [e1, e2]
  ring

/-! ### The equilibrium: existence, uniqueness, non-existence -/

/-- Cochrane (2023), §1.3, pp. 7–8: an equilibrium of the two-period model given fiscal policy
and the debt sale `(B₋₁, B₀, s₀, s₁)`: positive price levels `P₀, P₁`, `P₀` known at date 0,
the flow condition (1.2), the bond price (1.3) and the date-1 valuation equation (1.4). -/
def Equilibrium (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ) : Prop :=
  (∀ ω, 0 < P0 ω) ∧ (∀ ω, 0 < P1 ω) ∧ Known 𝔼 0 P0 ∧ Flow0 Bm1 P0 s0 Q0 B0 ∧
    BondPrice0 𝔼 β P0 P1 Q0 ∧ Valuation1 B0 P1 s1

/-- Cochrane (2023), eqs. (1.4)–(1.5), p. 8: from `B₀/P₁ = s₁` with `P₁, s₁ ≠ 0`, `P₁ = B₀/s₁`
state by state. -/
theorem price1_eq {B0 P1 s1 : Ω → ℝ} (hP1 : ∀ ω, P1 ω ≠ 0) (hs1 : ∀ ω, s1 ω ≠ 0)
    (h : Valuation1 B0 P1 s1) : P1 = B0 / s1 := by
  funext ω
  exact lastDay_eq (hP1 ω) (hs1 ω) (congrFun h ω)

/-- Cochrane (2023), eq. (1.5), p. 8: from `B₋₁/P₀ = s₀ + βE₀s₁` with `P₀ ≠ 0` and a nonzero
present value, `P₀ = B₋₁/(s₀ + βE₀s₁)`. -/
theorem price0_eq (𝔼 : ExpectationSystem Ω) {β : ℝ} {Bm1 P0 s0 s1 : Ω → ℝ}
    (hP0 : ∀ ω, P0 ω ≠ 0) (hpv : ∀ ω, pv 𝔼 β s0 s1 ω ≠ 0) (h : Valuation0 𝔼 β Bm1 P0 s0 s1) :
    P0 = Bm1 / pv 𝔼 β s0 s1 := by
  funext ω
  exact lastDay_eq (hP0 ω) (hpv ω) (congrFun h ω)

/-- Cochrane (2023), §1.3, pp. 7–8: characterisation of the equilibrium. With `PullOut`,
`B₀` known at 0, `s₁ > 0` and a positive present value, `(P₀, P₁, Q₀)` is an equilibrium iff
`P₀ > 0`, `P₀` known at 0, `P₁ = B₀/s₁`, `P₀ = B₋₁/(s₀ + βE₀s₁)` and `Q₀ = βE₀(P₀/P₁)`, with
`P₁ > 0`. -/
theorem equilibrium_iff (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) :
    Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0 ↔
      (∀ ω, 0 < P0 ω) ∧ Known 𝔼 0 P0 ∧ P1 = B0 / s1 ∧ P0 = Bm1 / pv 𝔼 β s0 s1 ∧
        BondPrice0 𝔼 β P0 P1 Q0 := by
  constructor
  · rintro ⟨hP0, hP1, hk, hflow, hQ, h1⟩
    have hv := valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1
    exact ⟨hP0, hk, price1_eq (fun ω => (hP1 ω).ne') (fun ω => (hs1 ω).ne') h1,
      price0_eq 𝔼 (fun ω => (hP0 ω).ne') (fun ω => (hpv ω).ne') hv, hQ⟩
  · rintro ⟨hP0, hk, rfl, hP0eq, hQ⟩
    have hP1 : ∀ ω, 0 < (B0 / s1) ω := fun ω => div_pos (hB0 ω) (hs1 ω)
    have h1 : Valuation1 B0 (B0 / s1) s1 := by
      funext ω
      simp only [Pi.div_apply]
      have := (hB0 ω).ne'
      have := (hs1 ω).ne'
      field_simp
    have hv : Valuation0 𝔼 β Bm1 P0 s0 s1 := by
      funext ω
      have e := congrFun hP0eq ω
      simp only [Pi.div_apply] at e ⊢
      have := (hP0 ω).ne'
      have := (hpv ω).ne'
      rw [div_eq_iff (hP0 ω).ne', e]
      simp only [pv] at this ⊢
      field_simp
    exact ⟨hP0, hP1, hk, (flow_iff_valuation0 𝔼 hP hP0 hk hkB0 hQ h1).mpr hv, hQ, h1⟩

/-- Cochrane (2023), §1.3, pp. 7–8: **the fiscal theory determines the price level.** With
`PullOut`, `B₋₁, B₀, s₀` known at date 0, `B₋₁, B₀ > 0`, a positive surplus `s₁ > 0` and a
positive present value `s₀ + βE₀s₁ > 0` (error E3: these hypotheses are needed), there is
exactly one equilibrium `(P₀, P₁, Q₀)`. -/
theorem equilibrium_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω) (hkBm1 : Known 𝔼 0 Bm1)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hks0 : Known 𝔼 0 s0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ), Equilibrium 𝔼 β Bm1 B0 s0 s1 p.1 p.2.1 p.2.2 := by
  set P0 := Bm1 / pv 𝔼 β s0 s1 with hP0def
  have hP0 : ∀ ω, 0 < P0 ω := fun ω => div_pos (hBm1 ω) (hpv ω)
  have hk : Known 𝔼 0 P0 :=
    known_div 𝔼 hP hkBm1 (known_pv 𝔼 β hks0 s1) (fun ω => (hpv ω).ne')
  refine ⟨(P0, B0 / s1, β • 𝔼.E 0 (P0 / (B0 / s1))), ?_, ?_⟩
  · exact (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mpr ⟨hP0, hk, rfl, rfl, rfl⟩
  · rintro ⟨Q, R, S⟩ h
    obtain ⟨-, -, hR, hQ, hS⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp h
    simp only at hR hQ hS
    rw [hS, hR, hQ]

/-- Cochrane (2023), eq. (1.1), p. 4 (error E3): if in some state the date-1 surplus is not
positive (and `B₀ > 0` there), no equilibrium exists. -/
theorem no_equilibrium_of_s1_nonpos (𝔼 : ExpectationSystem Ω) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} {ω : Ω} (hB0 : 0 < B0 ω) (hs1 : s1 ω ≤ 0) :
    ¬ Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0 := by
  rintro ⟨-, hP1, -, -, -, h1⟩
  exact lastDay_none hB0 hs1 ⟨P1 ω, hP1 ω, congrFun h1 ω⟩

/-- Cochrane (2023), eq. (1.5), p. 8 (error E3): if in some state the present value of
surpluses `s₀ + βE₀s₁` is not positive while `B₋₁ > 0`, no equilibrium exists (`PullOut`,
`B₀` known at 0). -/
theorem no_equilibrium_of_pv_nonpos (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0) {ω : Ω} (hBm1 : 0 < Bm1 ω)
    (hpv : pv 𝔼 β s0 s1 ω ≤ 0) : ¬ Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0 := by
  rintro ⟨hP0, -, hk, hflow, hQ, h1⟩
  have hv := congrFun (valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1) ω
  exact lastDay_none hBm1 hpv ⟨P0 ω, hP0 ω, hv⟩

/-! ### Comparative statics of `P₀ = B₋₁/(s₀ + βE₀s₁)` (box p. 7, p. 8) -/

/-- Cochrane (2023), box p. 7 and p. 8: "a higher discount rate, lower `β`, can lead to
inflation with no change in surpluses": with `B₋₁ > 0` and `E₀s₁ > 0`, `P₀ = B₋₁/(s₀ + βE₀s₁)`
is strictly decreasing in `β` (where the present value is positive). -/
theorem price0_strictAnti_beta {Bm1 s0 Es1 β β' : ℝ} (hB : 0 < Bm1) (hE : 0 < Es1)
    (hββ' : β < β') (hpv : 0 < s0 + β * Es1) :
    Bm1 / (s0 + β' * Es1) < Bm1 / (s0 + β * Es1) := by
  have h : s0 + β * Es1 < s0 + β' * Es1 := by nlinarith
  exact div_lt_div_of_pos_left hB hpv h

/-- Cochrane (2023), p. 8: "inflation can break out today if people see intractable future
fiscal problems": with `B₋₁ > 0`, `β > 0`, `P₀` is strictly decreasing in expected future
surpluses `E₀s₁` (where the present value is positive). -/
theorem price0_strictAnti_Es1 {Bm1 s0 β e e' : ℝ} (hB : 0 < Bm1) (hβ : 0 < β) (hee' : e < e')
    (hpv : 0 < s0 + β * e) : Bm1 / (s0 + β * e') < Bm1 / (s0 + β * e) := by
  have h : s0 + β * e < s0 + β * e' := by nlinarith
  exact div_lt_div_of_pos_left hB hpv h

/-- Cochrane (2023), p. 8: the price level `P₀` depends on the surpluses `(s₀, s₁)` only through
their present value: two policies with the same `s₀ + βE₀s₁` have the same equilibrium `P₀`
(`PullOut`, `B₀` known at 0, `s₁, s₁' > 0`, positive present value). -/
theorem price0_eq_of_pv_eq (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 s0' s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hkB0 : Known 𝔼 0 B0) (hs1 : ∀ ω, 0 < s1 ω) (hs1' : ∀ ω, 0 < s1' ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hsame : pv 𝔼 β s0 s1 = pv 𝔼 β s0' s1')
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0 s0' s1' P0' P1' Q0') : P0 = P0' := by
  have hpv' : ∀ ω, 0 < pv 𝔼 β s0' s1' ω := fun ω => hsame ▸ hpv ω
  obtain ⟨-, -, -, h, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  obtain ⟨-, -, -, h', -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1' hpv').mp he'
  rw [h, h', hsame]

/-- Cochrane (2023), p. 8: "governments can run large deficits `s₀ < 0` … with no inflation",
and "inflation can break out … despite healthy debt and deficits": for any current surplus or
deficit `s₀`, any `B₋₁ > 0`, `β > 0` and any target price level `P̄ > 0`, there is an expected
future surplus `E₀s₁` with `B₋₁/(s₀ + βE₀s₁) = P̄` (and a positive present value). -/
theorem price0_any_level {Bm1 s0 β Pbar : ℝ} (hB : 0 < Bm1) (hβ : 0 < β) (hP : 0 < Pbar) :
    ∃ e : ℝ, 0 < s0 + β * e ∧ Bm1 / (s0 + β * e) = Pbar := by
  refine ⟨(Bm1 / Pbar - s0) / β, ?_, ?_⟩
  · have : s0 + β * ((Bm1 / Pbar - s0) / β) = Bm1 / Pbar := by field_simp; ring
    rw [this]; positivity
  · have : s0 + β * ((Bm1 / Pbar - s0) / β) = Bm1 / Pbar := by field_simp; ring
    rw [this]; field_simp

/-! ### Genuine uncertainty: a coin-flip economy -/

/-- Cochrane (2023), §1.3, p. 8 (the expectation `E₀` under genuine uncertainty): in the
coin-flip tree, with `B₋₁ = B₀ = 1`, `s₀ = 0`, `β = 1/2` and the random surplus
`s₁ = 1 + 𝟙(first flip heads)`, an equilibrium exists, and in every equilibrium the date-1
price level is random: `P₁ = 1/2` after heads and `P₁ = 1` after tails, while `P₀ = 4/3`. -/
theorem coin_equilibrium :
    (∃ p : (Bool × Bool → ℝ) × (Bool × Bool → ℝ) × (Bool × Bool → ℝ),
      Equilibrium coinSystem (1 / 2) 1 1 0 (1 + firstHeads) p.1 p.2.1 p.2.2) ∧
    ∀ P0 P1 Q0 : Bool × Bool → ℝ,
      Equilibrium coinSystem (1 / 2) 1 1 0 (1 + firstHeads) P0 P1 Q0 →
        P1 (true, true) = 1 / 2 ∧ P1 (false, false) = 1 ∧ ∀ ω, P0 ω = 4 / 3 := by
  have hP : coinSystem.PullOut := finiteTree_pullOut coinTree
  have hE : ∀ ω, coinSystem.E 0 (1 + firstHeads) ω = 3 / 2 := by
    intro ω
    have h1 : coinSystem.E 0 (1 : Bool × Bool → ℝ) = fun _ => 1 := coinSystem.const 0 1
    rw [map_add, Pi.add_apply, h1, coinSystem_E0_firstHeads]
    norm_num
  have hk1 : Known coinSystem 0 (1 : Bool × Bool → ℝ) := known_const coinSystem 0 1
  have hk0 : Known coinSystem 0 (0 : Bool × Bool → ℝ) := known_const coinSystem 0 0
  have hs1 : ∀ ω, 0 < (1 + firstHeads) ω := by
    intro ω
    simp only [Pi.add_apply, Pi.one_apply, firstHeads]
    split_ifs <;> norm_num
  have hpv : ∀ ω, 0 < pv coinSystem (1 / 2) 0 (1 + firstHeads) ω := by
    intro ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hE]
    norm_num
  have hpos : ∀ ω, (0 : ℝ) < (1 : Bool × Bool → ℝ) ω := fun _ => one_pos
  refine ⟨(equilibrium_existsUnique coinSystem hP hpos hk1 hpos hk1 hk0 hs1 hpv).exists, ?_⟩
  intro P0 P1 Q0 he
  obtain ⟨-, -, h1, h0, -⟩ := (equilibrium_iff coinSystem hP hpos hk1 hs1 hpv).mp he
  refine ⟨?_, ?_, fun ω => ?_⟩
  · rw [h1]; simp [firstHeads]; norm_num
  · rw [h1]; simp [firstHeads]
  · rw [h0]
    simp only [pv, Pi.div_apply, Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, hE]
    norm_num

end Cochrane.TwoPeriodModel.TwoPeriod

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary policy, fiscal policy and inflation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.4, pp. 9–10.

The two-period model of `TwoPeriod` (equilibrium `Equilibrium`, valuation equations (1.6)–(1.7)
= (1.1) and (1.5)). Everything holds for an arbitrary `ExpectationSystem` with `PullOut`.

## Main results

* (1.8), p. 9: `eq_1_8` (the chain `B₋₁/P₀ = s₀ + Q₀B₀/P₀ = s₀ + βE₀(P₀/P₁)B₀/P₀ = s₀ + βE₀s₁`);
  `revenue_invariant` ("bond sales raise no extra revenue").
* p. 9, share split: `shareSplit_equilibrium`, `shareSplit_unique` (selling `κB₀` with unchanged
  surpluses leaves `P₀`, multiplies `P₁` by `κ`, divides `Q₀` by `κ`), `doubling` (`κ = 2`),
  `rate_strictAnti` and `shareSplit_rate_rises` (the nominal rate rises).
* p. 10, interest-rate target: `TargetEquilibrium`, `target_existsUnique` (for every `i₀ > −1`
  exactly one `(P₀, B₀, P₁)`; this is also `determinate_under_peg`), `target_bond_demand`
  (the flat supply curve: `B₀ = (1 + i₀)P₀βE₀s₁`).
* (1.9), p. 10: `expected_inflation`, `E0_invP1`.
* p. 10, "Fisherian": `fisherian_two_period` (a higher `i₀` leaves `P₀` and raises `P₁` in
  every state and lowers `E₀(1/P₁)`).
* (1.10), p. 10: `innov`, `unexpected_inflation`; "(1.9)–(1.10) completely determine expected
  and unexpected inflation": `inflation_decomposition`, `no_fiscal_news`.
-/

namespace Cochrane.TwoPeriodModel.MonetaryFiscal

open Cochrane.TwoPeriodModel.TwoPeriod

variable {Ω : Type*}

/-! ### (1.8): bond sales raise no extra revenue -/

/-- Cochrane (2023), eq. (1.8), p. 9: in an equilibrium (with `PullOut`, `B₀` known at 0),
`B₋₁/P₀ = s₀ + (1/(1 + i₀))B₀/P₀`, `(1/(1 + i₀))B₀/P₀ = βE₀(P₀/P₁)B₀/P₀`, and
`βE₀(P₀/P₁)B₀/P₀ = βE₀s₁`. -/
theorem eq_1_8 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    Bm1 / P0 = s0 + (fun ω => 1 / (1 + rate Q0 ω)) * B0 / P0 ∧
      (fun ω => 1 / (1 + rate Q0 ω)) * B0 / P0 = β • 𝔼.E 0 (P0 / P1) * B0 / P0 ∧
      β • 𝔼.E 0 (P0 / P1) * B0 / P0 = β • 𝔼.E 0 s1 := by
  obtain ⟨hP0, -, hk, hflow, hQ, h1⟩ := he
  have hr := revenue_eq 𝔼 hP hk hkB0 hQ h1
  have hQ' : (fun ω => 1 / (1 + rate Q0 ω)) = Q0 := by
    funext ω; exact (bondPrice_eq_inv_one_add_rate Q0 ω).symm
  rw [hQ']
  refine ⟨?_, by rw [hQ], ?_⟩
  · funext ω
    have e := congrFun hflow ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply] at e ⊢
    have := (hP0 ω).ne'
    rw [e]
    field_simp
  · rw [← hQ, hr]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    have := (hP0 ω).ne'
    field_simp

/-- Cochrane (2023), p. 9: "bond sales `B₀` raise real revenue equal to `βE₀(s₁)`": in every
equilibrium `Q₀B₀/P₀ = βE₀s₁`, whatever the quantity `B₀` sold (`PullOut`, `B₀` known at 0). -/
theorem revenue_invariant (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) : Q0 * B0 / P0 = β • 𝔼.E 0 s1 := by
  obtain ⟨hP0, -, hk, -, hQ, h1⟩ := he
  rw [revenue_eq 𝔼 hP hk hkB0 hQ h1]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
  have := (hP0 ω).ne'
  field_simp

/-! ### The share split -/

/-- Cochrane (2023), p. 9: **share split.** If `(P₀, P₁, Q₀)` is an equilibrium and the
government sells `κB₀` (`κ > 0`) with unchanged surpluses, then `(P₀, κP₁, Q₀/κ)` is an
equilibrium: `P₀` does not change, `P₁` rises in proportion, the bond price falls. -/
theorem shareSplit_equilibrium (𝔼 : ExpectationSystem Ω) {β k : ℝ} (hk : 0 < k)
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    Equilibrium 𝔼 β Bm1 (k • B0) s0 s1 P0 (k • P1) (k⁻¹ • Q0) := by
  obtain ⟨hP0, hP1, hkP0, hflow, hQ, h1⟩ := he
  refine ⟨hP0, fun ω => ?_, hkP0, ?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos hk (hP1 ω)
  · funext ω
    have e := congrFun hflow ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e]
    field_simp
  · have e : P0 / k • P1 = k⁻¹ • (P0 / P1) := by
      funext ω
      simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    unfold BondPrice0 at hQ ⊢
    rw [e, map_smul, hQ, smul_comm]
  · funext ω
    have e := congrFun h1 ω
    simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [← e]
    have := (hP1 ω).ne'
    field_simp

/-- Cochrane (2023), p. 9: the share split's equilibrium is the only one: under the hypotheses
of `equilibrium_existsUnique`, every equilibrium of the economy with debt `κB₀` is
`(P₀, κP₁, Q₀/κ)`. -/
theorem shareSplit_unique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ} (hk : 0 < k)
    {Bm1 B0 s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hks0 : Known 𝔼 0 s0) (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) s0 s1 P0' P1' Q0') :
    P0' = P0 ∧ P1' = k • P1 ∧ Q0' = k⁻¹ • Q0 := by
  have hB0' : ∀ ω, 0 < (k • B0) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk (hB0 ω)
  have hu := equilibrium_existsUnique 𝔼 hP hBm1 hkBm1 hB0' (known_smul 𝔼 k hkB0) hks0 hs1 hpv
  have := hu.unique (y₁ := (P0', P1', Q0')) (y₂ := (P0, k • P1, k⁻¹ • Q0)) he'
    (shareSplit_equilibrium 𝔼 hk he)
  simp only [Prod.mk.injEq] at this
  exact this

/-- Cochrane (2023), p. 9: "a doubling of `B₀` with no change in surpluses halves the bond
price … doubling debt `B₀` doubles the price level `P₁`" (and leaves `P₀`). -/
theorem doubling (𝔼 : ExpectationSystem Ω) {β : ℝ} {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ}
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    Equilibrium 𝔼 β Bm1 ((2 : ℝ) • B0) s0 s1 P0 ((2 : ℝ) • P1) ((2 : ℝ)⁻¹ • Q0) :=
  shareSplit_equilibrium 𝔼 two_pos he

/-- Cochrane (2023), eq. (1.3), p. 8: the nominal rate `i₀ = 1/Q₀ − 1` is strictly decreasing
in the bond price on `Q₀ > 0`. -/
theorem rate_strictAnti {Q Q' : ℝ} (hQ : 0 < Q) (hQQ' : Q < Q') : 1 / Q' - 1 < 1 / Q - 1 := by
  have := one_div_lt_one_div_of_lt hQ hQQ'
  linarith

/-- Cochrane (2023), p. 9: selling more debt `κB₀` (`κ > 1`) with unchanged surpluses "raises
the nominal interest rate": with `Q₀ > 0`, `rate (Q₀/κ) > rate Q₀` in every state. -/
theorem shareSplit_rate_rises {k : ℝ} (hk : 1 < k) {Q0 : Ω → ℝ} (hQ : ∀ ω, 0 < Q0 ω) (ω : Ω) :
    rate Q0 ω < rate (k⁻¹ • Q0) ω := by
  simp only [rate, Pi.smul_apply, smul_eq_mul]
  have hk0 : 0 < k⁻¹ * Q0 ω := mul_pos (inv_pos.mpr (by linarith)) (hQ ω)
  refine rate_strictAnti hk0 ?_
  have : k⁻¹ < 1 := inv_lt_one_of_one_lt₀ hk
  nlinarith [hQ ω]

/-! ### The interest-rate target -/

/-- Cochrane (2023), p. 10: an equilibrium under the interest-rate target `i₀` (the government
offers any quantity of bonds at `Q₀ = 1/(1 + i₀)`): the quantity `B₀` is now endogenous,
known at date 0 and positive, and `(P₀, P₁, Q₀ = 1/(1 + i₀))` is an equilibrium given it. -/
def TargetEquilibrium (𝔼 : ExpectationSystem Ω) (β i0 : ℝ) (Bm1 s0 s1 P0 B0 P1 : Ω → ℝ) :
    Prop :=
  Known 𝔼 0 B0 ∧ (∀ ω, 0 < B0 ω) ∧
    Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 (fun _ => 1 / (1 + i0))

/-- Cochrane (2023), eq. (1.9), p. 10: in an equilibrium with `Q₀ = 1/(1 + i₀)`, the target
sets expected inflation: `E₀(P₀/P₁) = 1/(β(1 + i₀))` (`β ≠ 0`, `i₀ ≠ −1`). -/
theorem expected_inflation (𝔼 : ExpectationSystem Ω) {β i0 : ℝ} (hβ : β ≠ 0)
    (hi : 1 + i0 ≠ 0) {Bm1 B0 s0 s1 P0 P1 : Ω → ℝ}
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 (fun _ => 1 / (1 + i0))) (ω : Ω) :
    𝔼.E 0 (P0 / P1) ω = 1 / (β * (1 + i0)) := by
  obtain ⟨-, -, -, -, hQ, -⟩ := he
  have e := congrFun hQ ω
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rw [div_eq_iff hi] at e
  rw [eq_div_iff (mul_ne_zero hβ hi)]
  linear_combination -e

/-- Cochrane (2023), eq. (1.9), p. 10: "really, by lowering `E(1/P₁)`":
`E₀(1/P₁) = 1/(β(1 + i₀)P₀)` (`PullOut`, `β ≠ 0`, `i₀ ≠ −1`). -/
theorem E0_invP1 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ} (hβ : β ≠ 0)
    (hi : 1 + i0 ≠ 0) {Bm1 B0 s0 s1 P0 P1 : Ω → ℝ}
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 (fun _ => 1 / (1 + i0))) (ω : Ω) :
    𝔼.E 0 (1 / P1) ω = 1 / (β * (1 + i0) * P0 ω) := by
  have hP0 := he.1 ω
  have hk := he.2.2.1
  have h := expected_inflation 𝔼 hβ hi he ω
  have hpo : 𝔼.E 0 (P0 / P1) = P0 * 𝔼.E 0 (1 / P1) := by
    rw [← hP 0 P0 _ hk]
    congr 1
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]
    ring
  rw [hpo] at h
  simp only [Pi.mul_apply] at h
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hβ hi) hP0.ne')]
  rw [eq_div_iff (mul_ne_zero hβ hi)] at h
  linear_combination h

/-- Cochrane (2023), p. 10: under the target, the quantity of bonds people buy at the fixed
price ("a flat supply curve") is `B₀ = (1 + i₀)P₀βE₀s₁` (`PullOut`, `i₀ ≠ −1`). -/
theorem target_bond_demand (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hi : 1 + i0 ≠ 0) {Bm1 s0 s1 P0 B0 P1 : Ω → ℝ}
    (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1) :
    B0 = (fun _ => 1 + i0) * P0 * (β • 𝔼.E 0 s1) := by
  obtain ⟨hkB0, -, -, -, hk, -, hQ, h1⟩ := he
  have hr := revenue_eq 𝔼 hP hk hkB0 hQ h1
  funext ω
  have e := congrFun hr ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [div_mul_eq_mul_div, div_eq_iff hi] at e
  linear_combination e

/-- Cochrane (2023), p. 10: **inflation is stable and determinate under an interest-rate
target, even a peg.** For every `i₀ > −1`, with `PullOut`, `B₋₁ > 0` and `s₀` known at 0,
`s₁ > 0`, `E₀s₁ > 0` and a positive present value, there is exactly one equilibrium
`(P₀, B₀, P₁)`: `P₀ = B₋₁/(s₀ + βE₀s₁)`, `B₀ = (1 + i₀)P₀βE₀s₁`, `P₁ = B₀/s₁`. -/
theorem target_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) {Bm1 s0 s1 : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hks0 : Known 𝔼 0 s0) (hs1 : ∀ ω, 0 < s1 ω)
    (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ),
      TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 p.1 p.2.1 p.2.2 := by
  have hi' : 0 < 1 + i0 := by linarith
  set P0 := Bm1 / pv 𝔼 β s0 s1 with hP0def
  have hP0 : ∀ ω, 0 < P0 ω := fun ω => div_pos (hBm1 ω) (hpv ω)
  have hkP0 : Known 𝔼 0 P0 :=
    known_div 𝔼 hP hkBm1 (known_pv 𝔼 β hks0 s1) (fun ω => (hpv ω).ne')
  set B0 := (fun _ => 1 + i0) * P0 * (β • 𝔼.E 0 s1) with hB0def
  have hB0 : ∀ ω, 0 < B0 ω := fun ω => by
    simp only [hB0def, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    have := hP0 ω; have := hEs1 ω; positivity
  have hkB0 : Known 𝔼 0 B0 :=
    known_mul 𝔼 hP (known_mul 𝔼 hP (known_const 𝔼 0 _) hkP0)
      (known_smul 𝔼 β (known_E 𝔼 0 s1))
  refine ⟨(P0, B0, B0 / s1), ⟨hkB0, hB0, ?_⟩, ?_⟩
  · refine (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mpr ⟨hP0, hkP0, rfl, rfl, ?_⟩
    -- the bond price at the target
    have hkr : Known 𝔼 0 (P0 / B0) := known_div 𝔼 hP hkP0 hkB0 (fun ω => (hB0 ω).ne')
    have e1 : P0 / (B0 / s1) = (P0 / B0) * s1 := by
      funext ω
      simp only [Pi.div_apply, Pi.mul_apply]
      have := (hB0 ω).ne'; have := (hs1 ω).ne'
      field_simp
    unfold BondPrice0
    rw [e1, hP 0 _ _ hkr]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul, hB0def]
    have := (hP0 ω).ne'; have := (hEs1 ω).ne'
    field_simp
  · rintro ⟨P0', B0', P1'⟩ ⟨hkB0', hB0', he⟩
    simp only at hkB0' hB0' he
    have hdem := target_bond_demand 𝔼 hP hi'.ne' ⟨hkB0', hB0', he⟩
    obtain ⟨-, -, h1, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0' hkB0' hs1 hpv).mp he
    have hP0eq : P0' = P0 := h0
    rw [hP0eq] at hdem
    rw [hP0eq, h1, hdem]

/-- Cochrane (2023), p. 10: "inflation is stable and determinate even with an interest-rate
peg" — the peg `i₀` determines `(P₀, B₀, P₁)` uniquely (`target_existsUnique`). -/
theorem determinate_under_peg (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) {Bm1 s0 s1 : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hks0 : Known 𝔼 0 s0) (hs1 : ∀ ω, 0 < s1 ω)
    (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    {P0 B0 P1 P0' B0' P1' : Ω → ℝ} (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1)
    (he' : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0' B0' P1') :
    P0 = P0' ∧ B0 = B0' ∧ P1 = P1' := by
  have := (target_existsUnique 𝔼 hP hβ hi hBm1 hkBm1 hks0 hs1 hEs1 hpv).unique
    (y₁ := (P0, B0, P1)) (y₂ := (P0', B0', P1')) he he'
  simp only [Prod.mk.injEq] at this
  exact this

/-- Cochrane (2023), p. 10, the **Fisherian** response: a higher target `i₀ < i₀'` has no effect
on `P₀` (hence on contemporaneous inflation `P₀/P₋₁`) and raises `P₁` in every state, lowering
`E₀(1/P₁)` (`PullOut`, `E₀s₁ > 0`). -/
theorem fisherian_two_period (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 i0' : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) (hii' : i0 < i0') {Bm1 s0 s1 : Ω → ℝ}
    (hs1 : ∀ ω, 0 < s1 ω) (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    {P0 B0 P1 P0' B0' P1' : Ω → ℝ} (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1)
    (he' : TargetEquilibrium 𝔼 β i0' Bm1 s0 s1 P0' B0' P1') :
    P0' = P0 ∧ (∀ ω, P1 ω < P1' ω) ∧ ∀ ω, 𝔼.E 0 (1 / P1') ω < 𝔼.E 0 (1 / P1) ω := by
  have hd := target_bond_demand 𝔼 hP (by linarith) he
  have hd' := target_bond_demand 𝔼 hP (by linarith) he'
  obtain ⟨hkB0, hB0, hq⟩ := he
  obtain ⟨hkB0', hB0', hq'⟩ := he'
  obtain ⟨hP0, -, h1, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp hq
  obtain ⟨-, -, h1', h0', -⟩ := (equilibrium_iff 𝔼 hP hB0' hkB0' hs1 hpv).mp hq'
  have hPP : P0' = P0 := by rw [h0, h0']
  refine ⟨hPP, fun ω => ?_, fun ω => ?_⟩
  · rw [h1, h1', hd, hd', hPP]
    simp only [Pi.div_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    refine div_lt_div_of_pos_right ?_ (hs1 ω)
    have := hP0 ω; have := hEs1 ω
    have : 0 < P0 ω * (β * 𝔼.E 0 s1 ω) := by positivity
    nlinarith
  · rw [E0_invP1 𝔼 hP hβ.ne' (by linarith) hq' ω, E0_invP1 𝔼 hP hβ.ne' (by linarith) hq ω, hPP]
    have := hP0 ω
    have h1i : 0 < 1 + i0 := by linarith
    refine one_div_lt_one_div_of_lt (by positivity) ?_
    have : 0 < β * P0 ω := by positivity
    nlinarith

/-! ### (1.10): fiscal policy sets unexpected inflation -/

/-- Cochrane (2023), p. 10: the innovation `(E₁ − E₀)x`. -/
noncomputable def innov (𝔼 : ExpectationSystem Ω) (x : Ω → ℝ) : Ω → ℝ :=
  𝔼.E 1 x - 𝔼.E 0 x

/-- Cochrane (2023), eq. (1.10), p. 10: multiplying (1.6) by `P₀` and taking innovations,
`(B₀/P₀)(E₁ − E₀)(P₀/P₁) = (E₁ − E₀)s₁` (`PullOut`; `B₀, P₀` known at 0; `P₀ > 0`). -/
theorem unexpected_inflation (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {B0 s1 P0 P1 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0) (hkB0 : Known 𝔼 0 B0)
    (h1 : Valuation1 B0 P1 s1) : (B0 / P0) * innov 𝔼 (P0 / P1) = innov 𝔼 s1 := by
  have hk0 : Known 𝔼 0 (B0 / P0) := known_div 𝔼 hP hkB0 hkP0 (fun ω => (hP0 ω).ne')
  have hk1 : Known 𝔼 1 (B0 / P0) := known_mono 𝔼 zero_le_one hk0
  have e : B0 / P0 * (P0 / P1) = s1 := by
    rw [← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    have := (hP0 ω).ne'
    field_simp
  unfold innov
  rw [mul_sub, ← hP 1 _ _ hk1, ← hP 0 _ _ hk0, e]

/-- Cochrane (2023), pp. 10, "(1.9)–(1.10) completely determine expected and unexpected
inflation": under the target `i₀`, with `s₁` known at date 1 (`PullOut`, `β ≠ 0`),
`P₀/P₁ = 1/(β(1 + i₀)) + (P₀/B₀)(E₁ − E₀)s₁` in every state. -/
theorem inflation_decomposition (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : β ≠ 0) (hi : 1 + i0 ≠ 0) {Bm1 s0 s1 P0 B0 P1 : Ω → ℝ} (hks1 : Known 𝔼 1 s1)
    (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1) (ω : Ω) :
    P0 ω / P1 ω = 1 / (β * (1 + i0)) + P0 ω / B0 ω * innov 𝔼 s1 ω := by
  obtain ⟨hkB0, hB0, hq⟩ := he
  obtain ⟨hP0, hP1, hkP0, -, -, h1⟩ := id hq
  have hk0 : Known 𝔼 0 (P0 / B0) := known_div 𝔼 hP hkP0 hkB0 (fun ω => (hB0 ω).ne')
  have e : P0 / P1 = (P0 / B0) * s1 := by
    rw [← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    have := (hB0 ω).ne'; have := (hP1 ω).ne'
    field_simp
  have hkr : Known 𝔼 1 (P0 / P1) := by
    rw [e]; exact known_mul 𝔼 hP (known_mono 𝔼 zero_le_one hk0) hks1
  have hu := congrFun (unexpected_inflation 𝔼 hP hP0 hkP0 hkB0 h1) ω
  have hexp := expected_inflation 𝔼 hβ hi hq ω
  have hin : innov 𝔼 (P0 / P1) ω = (P0 / P1) ω - 𝔼.E 0 (P0 / P1) ω := by
    simp only [innov, Pi.sub_apply]
    rw [hkr]
  simp only [Pi.mul_apply] at hu
  simp only [Pi.div_apply] at hu hin
  have := (hB0 ω).ne'; have := (hP0 ω).ne'
  have hsub : innov 𝔼 (P0 / P1) ω = P0 ω / B0 ω * innov 𝔼 s1 ω := by
    rw [← hu]; field_simp
  rw [← hexp]
  linarith

/-- Cochrane (2023), p. 10: without fiscal news (`s₁` known at date 0, so `(E₁ − E₀)s₁ = 0`),
inflation under the target equals expected inflation: `P₀/P₁ = 1/(β(1 + i₀))` in every state. -/
theorem no_fiscal_news (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : β ≠ 0) (hi : 1 + i0 ≠ 0) {Bm1 s0 s1 P0 B0 P1 : Ω → ℝ} (hks1 : Known 𝔼 0 s1)
    (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1) (ω : Ω) :
    P0 ω / P1 ω = 1 / (β * (1 + i0)) := by
  rw [inflation_decomposition 𝔼 hP hβ hi (known_mono 𝔼 zero_le_one hks1) he ω]
  have : innov 𝔼 s1 ω = 0 := by
    simp only [innov, Pi.sub_apply]
    rw [known_mono 𝔼 zero_le_one hks1, hks1, sub_self]
  rw [this, mul_zero, add_zero]

end Cochrane.TwoPeriodModel.MonetaryFiscal

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiscal policy debt sales

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.5, pp. 10–13 and
Table 1.1, p. 11.

Comparative statics of the two-period equilibrium of `TwoPeriod` when debt sales come with
changes in surpluses. Every comparison is between two equilibria (old and new policy) of the
same `ExpectationSystem` with `PullOut`; the price levels are read off `equilibrium_iff`
(`P₁ = B₀/s₁`, `P₀ = B₋₁/(s₀ + βE₀s₁)`) and the end-of-period real value of debt off
`revenue_invariant` (`Q₀B₀/P₀ = βE₀s₁`).

## Main results

* Box p. 10 / p. 11, the **equity issue**: `equityIssue_price1` (raising `B₀` and `s₁` in
  proportion leaves `P₁`), `equityIssue_revenue` (revenue is multiplied by `κ`),
  `equityIssue_lowers_price0` (the revenue can lower `P₀`), `equityIssue_funds_deficit`
  (or fund a deficit `s₀ − (κ − 1)βE₀s₁` with `P₀` unchanged).
* Table 1.1, row "Borrow", pp. 11–12: `borrow_price0`, `borrow_value_rises`,
  `borrow_keeps_price1_iff`, and `borrow_implementable` (under genuine uncertainty the borrowing
  strategy is implemented by scaling `B₀` and `s₁` by the date-0 factor
  `c = 1 − Δs₀/(βE₀s₁)`; then `P₀`, `P₁` and `Q₀` are all unchanged).
  **Error E1** (p. 12): the printed condition `(B₀ + ΔB₀)/P₁ = s₁ + RΔs₀` should read
  `s₁ − RΔs₀`: `borrow_debt_corrected` and the counterexample `borrow_printed_fails`.
* Table 1.1, row "Inflate": `inflate_price0_rises`, `inflate_value_unchanged`,
  `inflate_real_debt_falls_by_deficit` (`B₋₁/P₀` falls by exactly the fall in `s₀`).
* Table 1.1, row "AR(1)": `ar1_price0_rises_more`, `ar1_value_falls`.
* p. 12, the "s-shaped" surplus: `sShape_two_period` (a deficit with a rising value of debt
  requires expected future surpluses to rise), `steady_price0_iff` (a completely steady `P₀`
  despite a deficit iff `Δs₀ + βΔE₀s₁ = 0`).
-/

namespace Cochrane.TwoPeriodModel.DebtSales

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.MonetaryFiscal

variable {Ω : Type*}

/-- Cochrane (2023), eq. (1.5), p. 8: in an equilibrium, `P₀ = B₋₁/(s₀ + βE₀s₁)` state by state
(`PullOut`, `B₀ > 0` known at 0, `s₁ > 0`, positive present value). -/
theorem price0_formula (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) (ω : Ω) :
    P0 ω = Bm1 ω / (s0 ω + β * 𝔼.E 0 s1 ω) := by
  obtain ⟨-, -, -, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  rw [h0]
  rfl

/-! ### The equity issue -/

/-- Cochrane (2023), eq. (1.11), p. 11: "if the government raises `B₀` and `s₁` proportionally,
there is no effect on the price level at time 1": with `κ > 0`, `s₁ > 0`, `P₁, P₁' > 0`,
`B₀/P₁ = s₁` and `κB₀/P₁' = κs₁` give `P₁' = P₁`. -/
theorem equityIssue_price1 {k : ℝ} (hk : 0 < k) {B0 s1 P1 P1' : Ω → ℝ}
    (hs1 : ∀ ω, 0 < s1 ω) (hP1 : ∀ ω, 0 < P1 ω) (hP1' : ∀ ω, 0 < P1' ω)
    (h1 : Valuation1 B0 P1 s1) (h1' : Valuation1 (k • B0) P1' (k • s1)) : P1' = P1 := by
  have hks : ∀ ω, (k • s1) ω ≠ 0 := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact (mul_pos hk (hs1 ω)).ne'
  rw [price1_eq (fun ω => (hP1' ω).ne') hks h1',
    price1_eq (fun ω => (hP1 ω).ne') (fun ω => (hs1 ω).ne') h1]
  funext ω
  simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
  have := hk.ne'
  field_simp

/-- Cochrane (2023), eq. (1.12), p. 11: the equity issue raises the end-of-period real value of
debt and the real revenue from selling it: with debt `κB₀`
and surplus `κs₁` (any `s₀'`), `Q₀'B₀'/P₀' = κ · Q₀B₀/P₀` (`PullOut`, `B₀` known at 0). -/
theorem equityIssue_revenue (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ}
    {Bm1 B0 s0 s0' s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) s0' (k • s1) P0' P1' Q0') :
    Q0' * (k • B0) / P0' = k • (Q0 * B0 / P0) := by
  rw [revenue_invariant 𝔼 hP (known_smul 𝔼 k hkB0) he', revenue_invariant 𝔼 hP hkB0 he,
    map_smul, smul_comm]

/-- Cochrane (2023), p. 11: "or additional revenue can be used to lower the price level `P₀`":
with `s₀` unchanged, `κ > 1`, `β > 0`, `B₋₁ > 0` and `E₀s₁ > 0`, the equity issue lowers `P₀` in
every state (`PullOut`, `B₀ > 0` known at 0, `s₁ > 0`, positive present value). -/
theorem equityIssue_lowers_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ}
    (hβ : 0 < β) (hk : 1 < k) {Bm1 B0 s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hBm1 : ∀ ω, 0 < Bm1 ω) (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) s0 (k • s1) P0' P1' Q0') (ω : Ω) :
    P0' ω < P0 ω := by
  have hk0 : 0 < k := by linarith
  have hpvω : 0 < s0 ω + β * 𝔼.E 0 s1 ω := hpv ω
  have hlt : s0 ω + β * 𝔼.E 0 s1 ω < s0 ω + β * 𝔼.E 0 (k • s1) ω := by
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    have := hEs1 ω
    nlinarith [mul_pos (mul_pos hβ this) (sub_pos.mpr hk)]
  have hpv' : ∀ ω, 0 < pv 𝔼 β s0 (k • s1) ω := fun ω => by
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_smul]
    have hp := hpv ω; have hE := hEs1 ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp
    nlinarith [mul_pos (mul_pos hβ hE) (sub_pos.mpr hk)]
  have hB0' : ∀ ω, 0 < (k • B0) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk0 (hB0 ω)
  have hs1' : ∀ ω, 0 < (k • s1) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk0 (hs1 ω)
  rw [price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω,
    price0_formula 𝔼 hP hB0' (known_smul 𝔼 k hkB0) hs1' hpv' he' ω]
  exact div_lt_div_of_pos_left (hBm1 ω) hpvω hlt

/-- Cochrane (2023), p. 11: "the additional revenue can fund a deficit, a decline in `s₀`, with
no change in `P₀` or `P₁`": with `s₀' = s₀ − (κ − 1)βE₀s₁` and `(κB₀, κs₁)`, `P₀' = P₀` (and
`P₁' = P₁` by `equityIssue_price1`). -/
theorem equityIssue_funds_deficit (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ}
    (hk : 0 < k) {Bm1 B0 s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) (s0 - ((k - 1) * β) • 𝔼.E 0 s1) (k • s1) P0' P1' Q0') :
    P0' = P0 := by
  have hsame : pv 𝔼 β (s0 - ((k - 1) * β) • 𝔼.E 0 s1) (k • s1) = pv 𝔼 β s0 s1 := by
    funext ω
    simp only [pv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_smul]
    ring
  have hpv' : ∀ ω, 0 < pv 𝔼 β (s0 - ((k - 1) * β) • 𝔼.E 0 s1) (k • s1) ω :=
    fun ω => hsame ▸ hpv ω
  have hB0' : ∀ ω, 0 < (k • B0) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk (hB0 ω)
  have hs1' : ∀ ω, 0 < (k • s1) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk (hs1 ω)
  obtain ⟨-, -, -, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  obtain ⟨-, -, -, h0', -⟩ :=
    (equilibrium_iff 𝔼 hP hB0' (known_smul 𝔼 k hkB0) hs1' hpv').mp he'
  rw [h0', h0, hsame]

/-! ### Table 1.1: financing a deficit `Δs₀ < 0` -/

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12: lowering `s₀` by `Δ` and raising expected
`s₁` by `−RΔ` (`R = 1/β`) leaves the present value, hence `P₀`, unchanged: if
`E₀s₁' = E₀s₁ − Δ/β`, the equilibrium `P₀'` of `(B₀', s₀ + Δ, s₁')` equals `P₀`. -/
theorem borrow_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hβ : β ≠ 0)
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hs1 : ∀ ω, 0 < s1 ω) (hs1' : ∀ ω, 0 < s1' ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hE : 𝔼.E 0 s1' = 𝔼.E 0 s1 - fun _ => Δ / β)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') : P0' = P0 := by
  have hsame : pv 𝔼 β (s0 + fun _ => Δ) s1' = pv 𝔼 β s0 s1 := by
    funext ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE, Pi.sub_apply]
    field_simp
    ring
  have hpv' : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1' ω := fun ω => hsame ▸ hpv ω
  obtain ⟨-, -, -, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  obtain ⟨-, -, -, h0', -⟩ := (equilibrium_iff 𝔼 hP hB0' hkB0' hs1' hpv').mp he'
  rw [h0', h0, hsame]

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12: the end-of-period real value of debt
`Q₀B₀/P₀` rises by exactly `−Δ` (by `−Δ > 0` for a deficit `Δ < 0`). -/
theorem borrow_value_rises (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hβ : β ≠ 0)
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hkB0 : Known 𝔼 0 B0) (hkB0' : Known 𝔼 0 B0')
    (hE : 𝔼.E 0 s1' = 𝔼.E 0 s1 - fun _ => Δ / β)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') :
    Q0' * B0' / P0' = Q0 * B0 / P0 - fun _ => Δ := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he, hE]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12: the new equilibrium leaves `P₁` unchanged
in every state iff the new debt is scaled like the new surplus, `B₀' s₁ = B₀ s₁'`
(`s₁, s₁', P₁, P₁' > 0`). -/
theorem borrow_keeps_price1_iff {B0 B0' s1 s1' P1 P1' : Ω → ℝ} (hs1 : ∀ ω, 0 < s1 ω)
    (hs1' : ∀ ω, 0 < s1' ω) (hP1 : ∀ ω, 0 < P1 ω) (hP1' : ∀ ω, 0 < P1' ω)
    (h1 : Valuation1 B0 P1 s1) (h1' : Valuation1 B0' P1' s1') :
    P1' = P1 ↔ B0' * s1 = B0 * s1' := by
  rw [price1_eq (fun ω => (hP1' ω).ne') (fun ω => (hs1' ω).ne') h1',
    price1_eq (fun ω => (hP1 ω).ne') (fun ω => (hs1 ω).ne') h1]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.div_apply, Pi.mul_apply] at e ⊢
    have := (hs1 ω).ne'; have := (hs1' ω).ne'
    field_simp at e
    linarith
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.div_apply, Pi.mul_apply] at e ⊢
    have := (hs1 ω).ne'; have := (hs1' ω).ne'
    field_simp
    linarith

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12, under genuine uncertainty: scaling debt and
the date-1 surplus by the date-0 factor `c = 1 − Δ/(βE₀s₁)` implements the borrowing strategy
with `P₀`, `P₁` and `Q₀` all unchanged: `(P₀, P₁, Q₀)` is an equilibrium of
`(B₋₁, cB₀, s₀ + Δ, cs₁)`, with `E₀(cs₁) = E₀s₁ − Δ/β` (`PullOut`, `B₀` known at 0, `β > 0`,
`Δ ≤ 0`, `E₀s₁ > 0`). -/
theorem borrow_implementable (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    (hβ : 0 < β) (hΔ : Δ ≤ 0) {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    let c : Ω → ℝ := fun ω => 1 - Δ / (β * 𝔼.E 0 s1 ω)
    (∀ ω, 1 ≤ c ω) ∧ 𝔼.E 0 (c * s1) = 𝔼.E 0 s1 - (fun _ => Δ / β) ∧
      Equilibrium 𝔼 β Bm1 (c * B0) (s0 + fun _ => Δ) (c * s1) P0 P1 Q0 := by
  intro c
  obtain ⟨hP0, hP1, hk, hflow, hQ, h1⟩ := he
  have hc1 : ∀ ω, 1 ≤ c ω := fun ω => by
    have : Δ / (β * 𝔼.E 0 s1 ω) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hΔ (mul_pos hβ (hEs1 ω)).le
    simp only [c]; linarith
  have hkc : Known 𝔼 0 c := by
    have e : c = (fun _ => (1 : ℝ)) - (fun _ => Δ) / (β • 𝔼.E 0 s1) := by
      funext ω; simp [c]
    rw [e]
    exact known_sub 𝔼 (known_const 𝔼 0 1) (known_div 𝔼 hP (known_const 𝔼 0 Δ)
      (known_smul 𝔼 β (known_E 𝔼 0 s1)) (fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact (mul_pos hβ (hEs1 ω)).ne'))
  have hEc : 𝔼.E 0 (c * s1) = 𝔼.E 0 s1 - (fun _ => Δ / β) := by
    rw [hP 0 c s1 hkc]
    funext ω
    simp only [Pi.mul_apply, Pi.sub_apply, c]
    have := (hEs1 ω).ne'; have := hβ.ne'
    field_simp
  refine ⟨hc1, hEc, hP0, hP1, hk, ?_, hQ, ?_⟩
  · have hv := valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1
    have h1' : Valuation1 (c * B0) P1 (c * s1) := by
      rw [Valuation1, ← h1]
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply]
      ring
    refine (flow_iff_valuation0 𝔼 hP hP0 hk (known_mul 𝔼 hP hkc hkB0) hQ h1').mpr ?_
    rw [Valuation0, hv, hEc]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · rw [Valuation1, ← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring

/-- Cochrane (2023), p. 12 (**error E1**, corrected): with `B₀/P₁ = s₁` (`P₁ ≠ 0`, `β ≠ 0`,
`R = 1/β`), the extra debt `ΔB₀` that keeps `P₁` when `s₁` is raised by `−RΔs₀` satisfies
`(B₀ + ΔB₀)/P₁ = s₁ − RΔs₀`; precisely, `P₁` is the equilibrium price for `(B₀ + ΔB₀, s₁ − RΔs₀)`
iff `ΔB₀ = −RΔs₀P₁`. -/
theorem borrow_debt_corrected {B0 P1 s1 β Δ ΔB : ℝ} (hP1 : P1 ≠ 0) (h1 : B0 / P1 = s1) :
    (B0 + ΔB) / P1 = s1 - Δ / β ↔ ΔB = -(Δ / β) * P1 := by
  rw [← h1, div_eq_iff hP1]
  constructor
  · intro h
    field_simp at h
    have : ΔB = -(P1 * Δ / β) := by linarith
    rw [this]
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), p. 12 (**error E1**): the printed condition `(B₀ + ΔB₀)/P₁ = s₁ + RΔs₀` is
wrong: with the new surplus `s₁ − RΔs₀` and that debt, the date-1 price level is not `P₁`
whenever `Δs₀ ≠ 0` (here `R = 1/β`, `P₁ ≠ 0`, `β ≠ 0`, `s₁ − RΔs₀ ≠ 0`). -/
theorem borrow_printed_fails {B0 P1 s1 β Δ ΔB : ℝ} (hP1 : P1 ≠ 0) (hβ : β ≠ 0) (hΔ : Δ ≠ 0)
    (hs : s1 - Δ / β ≠ 0) (hprinted : (B0 + ΔB) / P1 = s1 + Δ / β) :
    (B0 + ΔB) / (s1 - Δ / β) ≠ P1 := by
  intro h
  rw [div_eq_iff hs] at h
  rw [div_eq_iff hP1, h] at hprinted
  have : P1 * (2 * (Δ / β)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hP1 h0
  · have : Δ / β = 0 := by linarith
    exact hΔ ((div_eq_zero_iff.mp this).resolve_right hβ)

/-- Cochrane (2023), Table 1.1, row "Inflate", p. 12: if `s₀` falls by `Δ < 0` and `s₁` is
unchanged, `P₀` rises in every state (`B₋₁ > 0`, positive present values). -/
theorem inflate_price0_rises (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    (hΔ : Δ < 0) {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hs1 : ∀ ω, 0 < s1 ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hpv' : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1 P0' P1' Q0') (ω : Ω) :
    P0 ω < P0' ω := by
  rw [price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω,
    price0_formula 𝔼 hP hB0' hkB0' hs1 hpv' he' ω]
  have h' := hpv' ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
  simp only [Pi.add_apply]
  exact div_lt_div_of_pos_left (hBm1 ω) h' (by linarith)

/-- Cochrane (2023), Table 1.1, row "Inflate", p. 12: the end-of-period value of debt
`Q₀B₀/P₀ = βE₀s₁`, "a claim to unchanged surpluses", does not change. -/
theorem inflate_value_unchanged (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1 P0' P1' Q0') :
    Q0' * B0' / P0' = Q0 * B0 / P0 := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he]

/-- Cochrane (2023), Table 1.1, row "Inflate", p. 12: "the value of the dollars that redeem
bonds `B₋₁` falls by exactly the fall in the surplus `s₀`": `B₋₁/P₀' = B₋₁/P₀ + Δ`. -/
theorem inflate_real_debt_falls_by_deficit (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {β Δ : ℝ} {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1 P0' P1' Q0') :
    Bm1 / P0' = Bm1 / P0 + fun _ => Δ := by
  obtain ⟨hP0, -, hk, hflow, hQ, h1⟩ := he
  obtain ⟨hP0', -, hk', hflow', hQ', h1'⟩ := he'
  rw [valuation0_of_flow 𝔼 hP hP0' hk' hkB0' hflow' hQ' h1',
    valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), Table 1.1, row "AR(1)", p. 12: if `s₁` falls along with `s₀`
(`E₀s₁' = E₀s₁ + ηΔ`, `η > 0`, `Δ < 0`, `β > 0`), `P₀` rises even more than under "Inflate":
`P₀ < P₀^{inflate} < P₀^{AR(1)}` in every state. -/
theorem ar1_price0_rises_more (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ η : ℝ}
    (hβ : 0 < β) (hΔ : Δ < 0) (hη : 0 < η)
    {Bm1 B0 Bi Ba s0 s1 sa P0 P1 Q0 Pi0 Pi1 Qi Pa0 Pa1 Qa : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hBi : ∀ ω, 0 < Bi ω)
    (hkBi : Known 𝔼 0 Bi) (hBa : ∀ ω, 0 < Ba ω) (hkBa : Known 𝔼 0 Ba)
    (hs1 : ∀ ω, 0 < s1 ω) (hsa : ∀ ω, 0 < sa ω)
    (hEa : 𝔼.E 0 sa = 𝔼.E 0 s1 + fun _ => η * Δ)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hpva : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) sa ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (hei : Equilibrium 𝔼 β Bm1 Bi (s0 + fun _ => Δ) s1 Pi0 Pi1 Qi)
    (hea : Equilibrium 𝔼 β Bm1 Ba (s0 + fun _ => Δ) sa Pa0 Pa1 Qa) (ω : Ω) :
    P0 ω < Pi0 ω ∧ Pi0 ω < Pa0 ω := by
  have hpvi : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1 ω := fun ω => by
    have := hpva ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hEa] at this ⊢
    have : β * (η * Δ) < 0 := mul_neg_of_pos_of_neg hβ (mul_neg_of_pos_of_neg hη hΔ)
    linarith
  refine ⟨inflate_price0_rises 𝔼 hP hΔ hBm1 hB0 hkB0 hBi hkBi hs1 hpv hpvi he hei ω, ?_⟩
  rw [price0_formula 𝔼 hP hBi hkBi hs1 hpvi hei ω,
    price0_formula 𝔼 hP hBa hkBa hsa hpva hea ω]
  have h' := hpva ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
  simp only [Pi.add_apply, hEa] at h' ⊢
  have : β * (η * Δ) < 0 := mul_neg_of_pos_of_neg hβ (mul_neg_of_pos_of_neg hη hΔ)
  exact div_lt_div_of_pos_left (hBm1 ω) h' (by nlinarith)

/-- Cochrane (2023), Table 1.1, row "AR(1)", p. 12: "the deficit in time 0 is accompanied by a
decline in the end-of-period value of debt": `Q₀'B₀'/P₀' = Q₀B₀/P₀ + βηΔ < Q₀B₀/P₀`. -/
theorem ar1_value_falls (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ η : ℝ}
    (hβ : 0 < β) (hΔ : Δ < 0) (hη : 0 < η)
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (hE : 𝔼.E 0 s1' = 𝔼.E 0 s1 + fun _ => η * Δ)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') (ω : Ω) :
    (Q0' * B0' / P0') ω = (Q0 * B0 / P0) ω + β * η * Δ ∧
      (Q0' * B0' / P0') ω < (Q0 * B0 / P0) ω := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he, hE]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have : β * (η * Δ) < 0 := mul_neg_of_pos_of_neg hβ (mul_neg_of_pos_of_neg hη hΔ)
  constructor
  · ring
  · linarith

/-- Cochrane (2023), Table 1.1, column `B₀/P₁`, p. 11: in each strategy the real value of the
maturing debt is `B₀/P₁ = s₁`, so it rises, is unchanged or falls with expected `s₁`:
`E₀(B₀'/P₁') − E₀(B₀/P₁) = E₀s₁' − E₀s₁`. -/
theorem maturing_value_change (𝔼 : ExpectationSystem Ω) {B0 B0' s1 s1' P1 P1' : Ω → ℝ}
    (h1 : Valuation1 B0 P1 s1) (h1' : Valuation1 B0' P1' s1') :
    𝔼.E 0 (B0' / P1') - 𝔼.E 0 (B0 / P1) = 𝔼.E 0 s1' - 𝔼.E 0 s1 := by
  rw [h1, h1']

/-- Cochrane (2023), p. 12, the **"s-shaped" surplus** in two periods: if a deficit
(`Δ < 0`) is accompanied by a rise in the end-of-period value of debt `Q₀B₀/P₀`, then expected
future surpluses must rise, `E₀s₁' > E₀s₁` (`β > 0`). -/
theorem sShape_two_period (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    (hβ : 0 < β) {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') {ω : Ω}
    (hrise : (Q0 * B0 / P0) ω < (Q0' * B0' / P0') ω) : 𝔼.E 0 s1 ω < 𝔼.E 0 s1' ω := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he] at hrise
  simp only [Pi.smul_apply, smul_eq_mul] at hrise
  exact lt_of_mul_lt_mul_left hrise hβ.le

/-- Cochrane (2023), p. 11 and p. 12: "fiscal theory can produce a completely steady price level
despite wide variation in deficits and debt": the deficit `Δ` leaves `P₀` unchanged iff it is
matched by expected future surpluses, `Δ + β(E₀s₁' − E₀s₁) = 0` (in a state `ω`; `B₋₁ > 0`,
positive present values). -/
theorem steady_price0_iff (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hs1 : ∀ ω, 0 < s1 ω) (hs1' : ∀ ω, 0 < s1' ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hpv' : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1' ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') (ω : Ω) :
    P0' ω = P0 ω ↔ Δ + β * (𝔼.E 0 s1' ω - 𝔼.E 0 s1 ω) = 0 := by
  rw [price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω,
    price0_formula 𝔼 hP hB0' hkB0' hs1' hpv' he' ω]
  have h1 := hpv ω
  have h2 := hpv' ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have hB := (hBm1 ω).ne'
  rw [div_eq_div_iff h2.ne' h1.ne']
  constructor
  · intro h
    have : Bm1 ω * ((s0 ω + β * 𝔼.E 0 s1 ω) - (s0 ω + Δ + β * 𝔼.E 0 s1' ω)) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hB
    · linarith
  · intro h
    have : s0 ω + Δ + β * 𝔼.E 0 s1' ω = s0 ω + β * 𝔼.E 0 s1 ω := by linarith
    rw [this]

end Cochrane.TwoPeriodModel.DebtSales

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Debt reactions and a price-level target; fiscal policy changes monetary policy

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.6–1.7, pp. 13–15.

The date-1 surplus follows the rule (1.13) `s₁ = B₀/P₁*`, where the price-level target `P₁* > 0`
is a date-1 random variable. Write `e = E₀(1/P₁*)`; we assume `e > 0` in every state.
An equilibrium under the rule is an `Equilibrium` of `TwoPeriod` with `s₁ = B₀/P₁*`.

## Main results

* (1.13), p. 13: `rule_price1_iff`, `rule_price1` (`P₁ = P₁*` uniquely).
* p. 14: `rule_valuation` (`B₋₁/P₀ = s₀ + βE₀(B₀/P₁*) = s₀ + βB₀E₀(1/P₁*)`),
  `rule_existsUnique`, `rule_price0`.
* p. 14, financing a deficit: `rule_borrow` (issue `ΔB₀ = −Δs₀/(βe)` more debt: `P₀`, `P₁`
  unchanged), `rule_inflate` (do not sell more debt: `P₀` rises), `rule_superinflate` (sell
  less debt: `s₁` falls and `P₀` rises even more).
* Box p. 14 / p. 15, §1.7: `rule_price0_strictAnti_B0` (more debt lowers `P₀`, `P₁ = P₁*`
  unchanged), `RuleTargetEquilibrium`, `rule_target_existsUnique` (under the rule and an
  interest-rate target, `P₀ = 1/((1 + i₀)βe)`), `rule_higher_rate_lowers_price0` ("higher
  interest rates lower inflation, immediately"), `rule_higher_rate_fiscal_tightening` (the
  accompanying expected future fiscal tightening: `B₀` and `s₁` rise, `s₀` unchanged).
* p. 15, demand curves: `rule_flat_demand` (`Q₀/P₀ = βe` for every `B₀`), `rule_revenue`
  (revenue `βB₀e` strictly increasing in `B₀`); with fixed surpluses
  `unit_elastic` (`Q₀B₀` the same for every `B₀`).
-/

namespace Cochrane.TwoPeriodModel.PriceLevelTarget

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.MonetaryFiscal
  Cochrane.TwoPeriodModel.DebtSales

variable {Ω : Type*}

/-- Cochrane (2023), eq. (1.13), p. 13: under the rule `s₁ = B₀/P₁*` (`B₀ > 0`, `P₁* > 0`), a
positive `P₁` satisfies `B₀/P₁ = s₁` iff `P₁ = P₁*`. -/
theorem rule_price1_iff {B0 Pstar P1 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hPs : ∀ ω, 0 < Pstar ω) (hP1 : ∀ ω, 0 < P1 ω) :
    Valuation1 B0 P1 (B0 / Pstar) ↔ P1 = Pstar := by
  constructor
  · intro h
    rw [price1_eq (fun ω => (hP1 ω).ne') (fun ω => (div_pos (hB0 ω) (hPs ω)).ne') h]
    funext ω
    simp only [Pi.div_apply]
    have := (hB0 ω).ne'; have := (hPs ω).ne'
    field_simp
  · rintro rfl
    rfl

/-- Cochrane (2023), p. 13: "with this rule, equilibrium inflation is given uniquely from
`B₀/P₁ = s₁` by `P₁ = P₁*`": every equilibrium under the rule has `P₁ = P₁*`. -/
theorem rule_price1 (𝔼 : ExpectationSystem Ω) {β : ℝ} {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ}
    (hB0 : ∀ ω, 0 < B0 ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) : P1 = Pstar :=
  (rule_price1_iff hB0 hPs he.2.1).mp he.2.2.2.2.2

/-- Cochrane (2023), p. 14: `E₀(B₀/P₁*) = B₀E₀(1/P₁*)` (`PullOut`, `B₀` known at 0), so the
present value under the rule is `s₀ + βB₀E₀(1/P₁*)`. -/
theorem rule_pv (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) (β : ℝ) {B0 s0 Pstar : Ω → ℝ}
    (hkB0 : Known 𝔼 0 B0) : pv 𝔼 β s0 (B0 / Pstar) = s0 + β • (B0 * 𝔼.E 0 (1 / Pstar)) := by
  have e : B0 / Pstar = B0 * (1 / Pstar) := by
    funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
  rw [pv, e, hP 0 B0 _ hkB0]

/-- Cochrane (2023), p. 14: in an equilibrium under the rule,
`B₋₁/P₀ = s₀ + βE₀(B₀/P₁*) = s₀ + βB₀E₀(1/P₁*)` (`PullOut`, `B₀` known at 0). -/
theorem rule_valuation (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) :
    Bm1 / P0 = s0 + β • 𝔼.E 0 (B0 / Pstar) ∧
      s0 + β • 𝔼.E 0 (B0 / Pstar) = s0 + β • (B0 * 𝔼.E 0 (1 / Pstar)) := by
  obtain ⟨hP0, -, hk, hflow, hQ, h1⟩ := he
  exact ⟨valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1, rule_pv 𝔼 hP β hkB0⟩

/-- Cochrane (2023), pp. 13–14: under the rule there is exactly one equilibrium (`PullOut`;
`B₋₁, B₀ > 0`, `B₋₁, B₀, s₀` known at 0; `P₁* > 0`; positive present value
`s₀ + βB₀E₀(1/P₁*)`). -/
theorem rule_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω) (hkBm1 : Known 𝔼 0 Bm1)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hks0 : Known 𝔼 0 s0)
    (hPs : ∀ ω, 0 < Pstar ω) (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω)) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ),
      Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) p.1 p.2.1 p.2.2 := by
  refine equilibrium_existsUnique 𝔼 hP hBm1 hkBm1 hB0 hkB0 hks0
    (fun ω => div_pos (hB0 ω) (hPs ω)) (fun ω => ?_)
  rw [rule_pv 𝔼 hP β hkB0]
  exact hpv ω

/-- Cochrane (2023), p. 14: the equilibrium price level under the rule,
`P₀ = B₋₁/(s₀ + βB₀E₀(1/P₁*))`. -/
theorem rule_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hPs : ∀ ω, 0 < Pstar ω) (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) (ω : Ω) :
    P0 ω = Bm1 ω / (s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω)) := by
  have hpv' : ∀ ω, 0 < pv 𝔼 β s0 (B0 / Pstar) ω := fun ω => by
    rw [rule_pv 𝔼 hP β hkB0]; exact hpv ω
  rw [price0_formula 𝔼 hP (s1 := B0 / Pstar) hB0 hkB0 (fun ω => div_pos (hB0 ω) (hPs ω)) hpv'
    he ω]
  have := congrFun (rule_pv 𝔼 hP β (s0 := s0) (Pstar := Pstar) hkB0) ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at this
  rw [this]

/-! ### Financing a deficit under the rule (p. 14) -/

/-- Cochrane (2023), p. 14: "to finance a deficit `s₀` by borrowing, without affecting the price
level at either date, the government issues more nominal debt `B₀`, without changing the
price-level target": lowering `s₀` by `Δ` and raising `B₀` by `ΔB₀` with `βΔB₀E₀(1/P₁*) = −Δ`
leaves `P₀` unchanged, and `P₁ = P₁*` in both equilibria. -/
theorem rule_borrow (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    {Bm1 B0 ΔB s0 Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < (B0 + ΔB) ω) (hkΔB : Known 𝔼 0 ΔB)
    (hPs : ∀ ω, 0 < Pstar ω) (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (hΔB : ∀ ω, β * ΔB ω * 𝔼.E 0 (1 / Pstar) ω = -Δ)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (B0 + ΔB) (s0 + fun _ => Δ) ((B0 + ΔB) / Pstar) P0' P1' Q0') :
    P0' = P0 ∧ P1' = Pstar ∧ P1 = Pstar := by
  have hkB0' := known_add 𝔼 hkB0 hkΔB
  have hsame : ∀ ω, s0 ω + Δ + β * ((B0 + ΔB) ω * 𝔼.E 0 (1 / Pstar) ω) =
      s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) := fun ω => by
    simp only [Pi.add_apply]
    linear_combination hΔB ω
  have hpv' : ∀ ω, 0 < s0 ω + Δ + β * ((B0 + ΔB) ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => by rw [hsame]; exact hpv ω
  refine ⟨funext fun ω => ?_, rule_price1 𝔼 hB0' hPs he', rule_price1 𝔼 hB0 hPs he⟩
  rw [rule_price0 𝔼 hP hB0' hkB0' hPs hpv' he' ω, rule_price0 𝔼 hP hB0 hkB0 hPs hpv he ω,
    hsame]

/-- Cochrane (2023), p. 14: "to finance the deficit by inflating away outstanding debt, the
government simply does not sell more debt `B₀`": with `B₀` unchanged and `s₀` lower by `Δ < 0`,
`P₀` rises in every state (`B₋₁ > 0`) while `P₁ = P₁*`. -/
theorem rule_inflate (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hΔ : Δ < 0)
    {Bm1 B0 s0 Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hPs : ∀ ω, 0 < Pstar ω)
    (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (hpv' : ∀ ω, 0 < s0 ω + Δ + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0 (s0 + fun _ => Δ) (B0 / Pstar) P0' P1' Q0') :
    (∀ ω, P0 ω < P0' ω) ∧ P1' = Pstar := by
  refine ⟨fun ω => ?_, rule_price1 𝔼 hB0 hPs he'⟩
  rw [rule_price0 𝔼 hP hB0 hkB0 hPs hpv he ω, rule_price0 𝔼 hP hB0 hkB0 hPs hpv' he' ω]
  have h' := hpv' ω
  exact div_lt_div_of_pos_left (hBm1 ω) h' (by linarith)

/-- Cochrane (2023), p. 14: "to super-inflate … the government sells even less debt `B₀`, which
lowers surpluses `s₁`": with `B₀' < B₀`, `s₀` lower by `Δ < 0`, `β > 0`, `E₀(1/P₁*) > 0`, the
date-1 surplus falls in every state and `P₀` rises above its "inflate" level. -/
theorem rule_superinflate (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hβ : 0 < β)
    {Bm1 B0 B0' s0 Pstar Pi0 Pi1 Qi Ps0 Ps1 Qs : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hless : ∀ ω, B0' ω < B0 ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (hpvs : ∀ ω, 0 < s0 ω + Δ + β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω))
    (hei : Equilibrium 𝔼 β Bm1 B0 (s0 + fun _ => Δ) (B0 / Pstar) Pi0 Pi1 Qi)
    (hes : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) (B0' / Pstar) Ps0 Ps1 Qs) (ω : Ω) :
    (B0' / Pstar) ω < (B0 / Pstar) ω ∧ Pi0 ω < Ps0 ω := by
  have hlt : ∀ ω, β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) < β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (hless ω) (he ω)) hβ
  have hpvi : ∀ ω, 0 < s0 ω + Δ + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => by linarith [hpvs ω, hlt ω]
  refine ⟨div_lt_div_of_pos_right (hless ω) (hPs ω), ?_⟩
  rw [rule_price0 𝔼 hP hB0 hkB0 hPs hpvi hei ω, rule_price0 𝔼 hP hB0' hkB0' hPs hpvs hes ω]
  exact div_lt_div_of_pos_left (hBm1 ω) (hpvs ω) (by linarith [hlt ω])

/-! ### §1.7: fiscal policy changes monetary policy -/

/-- Cochrane (2023), box p. 14 and p. 15: "larger debt `B₀` has no effect on `P₁ = P₁*`, and it
lowers the price level `P₀` immediately": with `B₀ < B₀'`, `s₀` unchanged, `β > 0`,
`E₀(1/P₁*) > 0`, `B₋₁ > 0`, `P₀' < P₀` in every state and `P₁ = P₁' = P₁*`. -/
theorem rule_price0_strictAnti_B0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    (hβ : 0 < β) {Bm1 B0 B0' s0 Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hmore : ∀ ω, B0 ω < B0' ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (heq : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (heq' : Equilibrium 𝔼 β Bm1 B0' s0 (B0' / Pstar) P0' P1' Q0') :
    (∀ ω, P0' ω < P0 ω) ∧ P1 = Pstar ∧ P1' = Pstar := by
  have hlt : ∀ ω, β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) < β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (hmore ω) (he ω)) hβ
  have hpv' : ∀ ω, 0 < s0 ω + β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => by linarith [hpv ω, hlt ω]
  refine ⟨fun ω => ?_, rule_price1 𝔼 hB0 hPs heq, rule_price1 𝔼 hB0' hPs heq'⟩
  rw [rule_price0 𝔼 hP hB0 hkB0 hPs hpv heq ω, rule_price0 𝔼 hP hB0' hkB0' hPs hpv' heq' ω]
  exact div_lt_div_of_pos_left (hBm1 ω) (hpv ω) (by linarith [hlt ω])

/-- Cochrane (2023), §1.7, p. 15: an equilibrium under the rule `s₁ = B₀/P₁*` and the
interest-rate target `i₀`: `B₀` endogenous, known at 0 and positive, and `Q₀ = 1/(1 + i₀)`. -/
def RuleTargetEquilibrium (𝔼 : ExpectationSystem Ω) (β i0 : ℝ) (Bm1 s0 Pstar P0 B0 P1 : Ω → ℝ) :
    Prop :=
  Known 𝔼 0 B0 ∧ (∀ ω, 0 < B0 ω) ∧
    Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 (fun _ => 1 / (1 + i0))

/-- Cochrane (2023), p. 15: under the rule, the bond price is `Q₀ = βE₀(P₀/P₁*) = βP₀E₀(1/P₁*)`,
so with the target `Q₀ = 1/(1 + i₀)` the price level is `P₀ = 1/((1 + i₀)βE₀(1/P₁*))`
(`PullOut`, `B₀ > 0`, `P₁* > 0`, `i₀ ≠ −1`, `β ≠ 0`). -/
theorem rule_target_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : β ≠ 0) (hi : 1 + i0 ≠ 0) {Bm1 s0 Pstar P0 B0 P1 : Ω → ℝ} (hPs : ∀ ω, 0 < Pstar ω)
    (he : RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar P0 B0 P1) (ω : Ω) :
    P0 ω = 1 / ((1 + i0) * β * 𝔼.E 0 (1 / Pstar) ω) := by
  obtain ⟨-, hB0, hq⟩ := he
  have hP1 := rule_price1 𝔼 hB0 hPs hq
  have hinv := E0_invP1 𝔼 hP hβ hi hq ω
  rw [hP1] at hinv
  have hP0 := (hq.1 ω).ne'
  rw [hinv]
  field_simp

/-- Cochrane (2023), §1.7, p. 15: **under the rule and an interest-rate target the equilibrium is
unique**: for `i₀ > −1`, `β > 0`, `e = E₀(1/P₁*) > 0`, with `B₋₁ > 0` and `s₀` known at 0 and
`s₀ < B₋₁(1 + i₀)βe` (so that a positive debt is sold), there is exactly one `(P₀, B₀, P₁)`:
`P₀ = 1/((1 + i₀)βe)`, `B₀ = (B₋₁/P₀ − s₀)/(βe)`, `P₁ = P₁*`. -/
theorem rule_target_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) {Bm1 s0 Pstar : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hks0 : Known 𝔼 0 s0) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (hs0 : ∀ ω, s0 ω < Bm1 ω * ((1 + i0) * β * 𝔼.E 0 (1 / Pstar) ω)) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ),
      RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar p.1 p.2.1 p.2.2 := by
  have hi' : 0 < 1 + i0 := by linarith
  set e := 𝔼.E 0 (1 / Pstar) with he_def
  have hke : Known 𝔼 0 e := known_E 𝔼 0 _
  set P0 : Ω → ℝ := fun ω => 1 / ((1 + i0) * β * e ω) with hP0def
  have hP0 : ∀ ω, 0 < P0 ω := fun ω => by
    have := he ω; simp only [hP0def]; positivity
  have hkP0 : Known 𝔼 0 P0 := by
    have : P0 = (fun _ => (1 : ℝ)) / ((1 + i0) * β) • e := by
      funext ω; simp [hP0def, mul_assoc]
    rw [this]
    exact known_div 𝔼 hP (known_const 𝔼 0 1) (known_smul 𝔼 _ hke) (fun ω => by
      simp only [Pi.smul_apply, smul_eq_mul]; have := he ω; positivity)
  set B0 : Ω → ℝ := (Bm1 / P0 - s0) / (β • e) with hB0def
  have hB0 : ∀ ω, 0 < B0 ω := fun ω => by
    simp only [hB0def, Pi.div_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP0def]
    have := he ω; have := hs0 ω
    refine div_pos ?_ (by positivity)
    rw [div_div_eq_mul_div, div_one]
    linarith
  have hkB0 : Known 𝔼 0 B0 :=
    known_div 𝔼 hP (known_sub 𝔼 (known_div 𝔼 hP hkBm1 hkP0 (fun ω => (hP0 ω).ne')) hks0)
      (known_smul 𝔼 β hke) (fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul]; have := he ω; positivity)
  have hpvB : ∀ ω, s0 ω + β * (B0 ω * e ω) = Bm1 ω / P0 ω := fun ω => by
    simp only [hB0def, Pi.div_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := (he ω).ne'; have := hβ.ne'
    field_simp
    ring
  have hpv : ∀ ω, 0 < pv 𝔼 β s0 (B0 / Pstar) ω := fun ω => by
    rw [rule_pv 𝔼 hP β hkB0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [hpvB]
    exact div_pos (hBm1 ω) (hP0 ω)
  have hs1 : ∀ ω, 0 < (B0 / Pstar) ω := fun ω => div_pos (hB0 ω) (hPs ω)
  refine ⟨(P0, B0, Pstar), ⟨hkB0, hB0, ?_⟩, ?_⟩
  · refine (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mpr ⟨hP0, hkP0, ?_, ?_, ?_⟩
    · funext ω
      simp only [Pi.div_apply]
      have := (hB0 ω).ne'; have := (hPs ω).ne'
      field_simp
    · funext ω
      rw [rule_pv 𝔼 hP β hkB0]
      simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
      rw [hpvB]
      have := (hBm1 ω).ne'; have := (hP0 ω).ne'
      field_simp
    · unfold BondPrice0
      have e1 : P0 / Pstar = P0 * (1 / Pstar) := by
        funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
      rw [e1, hP 0 P0 _ hkP0]
      funext ω
      simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hP0def]
      rw [← he_def]
      have := (he ω).ne'; have := hβ.ne'; have := hi'.ne'
      field_simp
  · rintro ⟨P0', B0', P1'⟩ hrt
    have h0 := rule_target_price0 𝔼 hP hβ.ne' hi'.ne' hPs hrt
    obtain ⟨hkB0', hB0', hq⟩ := hrt
    simp only at hkB0' hB0' hq h0
    have hP0eq : P0' = P0 := funext fun ω => by rw [h0 ω]
    have hP1 := rule_price1 𝔼 hB0' hPs hq
    have hv := (rule_valuation 𝔼 hP hkB0' hq)
    have hB : B0' = B0 := by
      funext ω
      have e1 := congrFun hv.1 ω
      have e2 := congrFun hv.2 ω
      simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
        at e1 e2
      rw [e2, hP0eq] at e1
      have h3 := hpvB ω
      have : β * e ω ≠ 0 := (mul_pos hβ (he ω)).ne'
      have h4 : β * e ω * B0' ω = β * e ω * B0 ω := by
        rw [he_def] at h3 ⊢
        linarith
      exact mul_left_cancel₀ this h4
    rw [hP0eq, hB, hP1]

/-- Cochrane (2023), box p. 14 and p. 15: "higher interest rates lower inflation, immediately":
under the rule, `i₀ < i₀'` gives `P₀' < P₀` in every state (lower current inflation
`P₀/P₋₁`), with `P₁ = P₁' = P₁*` unchanged (`PullOut`, `β > 0`, `i₀ > −1`, `E₀(1/P₁*) > 0`). -/
theorem rule_higher_rate_lowers_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {β i0 i0' : ℝ} (hβ : 0 < β) (hi : -1 < i0) (hii' : i0 < i0')
    {Bm1 s0 Pstar P0 B0 P1 P0' B0' P1' : Ω → ℝ} (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (heq : RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar P0 B0 P1)
    (heq' : RuleTargetEquilibrium 𝔼 β i0' Bm1 s0 Pstar P0' B0' P1') :
    (∀ ω, P0' ω < P0 ω) ∧ P1 = Pstar ∧ P1' = Pstar := by
  refine ⟨fun ω => ?_, rule_price1 𝔼 heq.2.1 hPs heq.2.2, rule_price1 𝔼 heq'.2.1 hPs heq'.2.2⟩
  rw [rule_target_price0 𝔼 hP hβ.ne' (by linarith) hPs heq ω,
    rule_target_price0 𝔼 hP hβ.ne' (by linarith) hPs heq' ω]
  have := he ω
  have h1 : 0 < (1 + i0) * β * 𝔼.E 0 (1 / Pstar) ω := by
    have : 0 < 1 + i0 := by linarith
    positivity
  refine one_div_lt_one_div_of_lt h1 ?_
  have : 0 < β * 𝔼.E 0 (1 / Pstar) ω := by positivity
  nlinarith

/-- Cochrane (2023), p. 15: "we see a simultaneous fiscal tightening along with the
interest-rate rise … only an expected future fiscal tightening": under the rule, a higher
target `i₀ < i₀'` with unchanged `s₀` raises the debt sold and the date-1 surplus
`s₁ = B₀/P₁*` in every state. -/
theorem rule_higher_rate_fiscal_tightening (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {β i0 i0' : ℝ} (hβ : 0 < β) (hi : -1 < i0) (hii' : i0 < i0')
    {Bm1 s0 Pstar P0 B0 P1 P0' B0' P1' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hPs : ∀ ω, 0 < Pstar ω) (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (heq : RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar P0 B0 P1)
    (heq' : RuleTargetEquilibrium 𝔼 β i0' Bm1 s0 Pstar P0' B0' P1') (ω : Ω) :
    B0 ω < B0' ω ∧ (B0 / Pstar) ω < (B0' / Pstar) ω := by
  have hlow := (rule_higher_rate_lowers_price0 𝔼 hP hβ hi hii' hPs he heq heq').1 ω
  have hv := congrFun (rule_valuation 𝔼 hP heq.1 heq.2.2).1 ω
  have hv2 := congrFun (rule_valuation 𝔼 hP heq.1 heq.2.2).2 ω
  have hv' := congrFun (rule_valuation 𝔼 hP heq'.1 heq'.2.2).1 ω
  have hv2' := congrFun (rule_valuation 𝔼 hP heq'.1 heq'.2.2).2 ω
  simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    at hv hv2 hv' hv2'
  rw [hv2] at hv
  rw [hv2'] at hv'
  have hP0 := heq.2.2.1 ω
  have hP0' := heq'.2.2.1 ω
  have hdiv : Bm1 ω / P0 ω < Bm1 ω / P0' ω := div_lt_div_of_pos_left (hBm1 ω) hP0' hlow
  have hlt : β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) < β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) := by
    linarith
  have hB : B0 ω < B0' ω :=
    lt_of_mul_lt_mul_right (lt_of_mul_lt_mul_left hlt hβ.le) (he ω).le
  exact ⟨hB, div_lt_div_of_pos_right hB (hPs ω)⟩

/-! ### Demand curves for debt (p. 15) -/

/-- Cochrane (2023), p. 15: "now, the debt demand curve is flat, giving the same real price
`Q₀/P₀` for any amount sold `B₀`": under the rule, `Q₀/P₀ = βE₀(1/P₁*)` in every equilibrium
(`PullOut`, `B₀ > 0`, `P₁* > 0`). -/
theorem rule_flat_demand (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) :
    Q0 / P0 = β • 𝔼.E 0 (1 / Pstar) := by
  have hP1 := rule_price1 𝔼 hB0 hPs he
  obtain ⟨hP0, -, hk, -, hQ, -⟩ := he
  rw [hQ, hP1]
  have e1 : P0 / Pstar = P0 * (1 / Pstar) := by
    funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
  rw [e1, hP 0 P0 _ hk]
  funext ω
  simp only [Pi.div_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have := (hP0 ω).ne'
  field_simp

/-- Cochrane (2023), p. 15: "the more bonds `B₀` sold, then, the more total real revenue such
sales produce": under the rule, revenue `Q₀B₀/P₀ = βB₀E₀(1/P₁*)`, strictly increasing in `B₀`
when `β > 0` and `E₀(1/P₁*) > 0`. -/
theorem rule_revenue (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {Bm1 B0 B0' s0 s0' Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hB0' : ∀ ω, 0 < B0' ω) (hmore : ∀ ω, B0 ω < B0' ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (heq : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (heq' : Equilibrium 𝔼 β Bm1 B0' s0' (B0' / Pstar) P0' P1' Q0') (ω : Ω) :
    (Q0 * B0 / P0) ω = β * 𝔼.E 0 (1 / Pstar) ω * B0 ω ∧
      (Q0 * B0 / P0) ω < (Q0' * B0' / P0') ω := by
  have h := congrFun (rule_flat_demand 𝔼 hP hB0 hPs heq) ω
  have h' := congrFun (rule_flat_demand 𝔼 hP hB0' hPs heq') ω
  simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at h h' ⊢
  have e1 : Q0 ω * B0 ω / P0 ω = Q0 ω / P0 ω * B0 ω := by ring
  have e2 : Q0' ω * B0' ω / P0' ω = Q0' ω / P0' ω * B0' ω := by ring
  rw [e1, e2, h, h']
  exact ⟨rfl, mul_lt_mul_of_pos_left (hmore ω) (mul_pos hβ (he ω))⟩

/-- Cochrane (2023), p. 15: "fixing surpluses `{s₀, s₁}`, the demand curve for nominal debt was
unit-elastic, giving the same total real revenue `βE₀(s₁)` for any amount of bonds `B₀`": two
equilibria with the same surpluses and debt `B₀`, `B₀'` have the same `P₀` and the same nominal
revenue `Q₀B₀ = Q₀'B₀'` (so `Q₀' = Q₀B₀/B₀'`). -/
theorem unit_elastic (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω) (hkB0' : Known 𝔼 0 B0')
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' s0 s1 P0' P1' Q0') :
    P0' = P0 ∧ Q0' * B0' = Q0 * B0 := by
  have hP0 : P0' = P0 := funext fun ω => by
    rw [price0_formula 𝔼 hP hB0' hkB0' hs1 hpv he' ω, price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω]
  refine ⟨hP0, ?_⟩
  obtain ⟨-, -, hk, -, hQ, h1⟩ := he
  obtain ⟨-, -, hk', -, hQ', h1'⟩ := he'
  rw [revenue_eq 𝔼 hP hk' hkB0' hQ' h1', revenue_eq 𝔼 hP hk hkB0 hQ h1, hP0]

end Cochrane.TwoPeriodModel.PriceLevelTarget

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Budget constraints, active versus passive policy, and a debt rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.8–1.9, pp. 15–19.

A **fiscal rule** for the last day is a function `s : ℝ → ℝ`, the real surplus the government
runs at each date-1 price level `P₁`. Its equilibrium set is `eqmSet B₀ s = {P₁ > 0 | B₀/P₁ =
s(P₁)}`. Policy is **active** when the equilibrium set has exactly one element (the fiscal theory
determines `P₁`), **passive** when it is `s(P₁) = B₀/P₁`, so that every `P₁ > 0` is an
equilibrium.

## Main results

* (1.14)–(1.15), p. 16: `budget_any_price` (the budget constraint `B₀ = P₁s₁ + M₁` holds at
  every price), `valuation_of_zero_money` and `money_zero_of_valuation` ((1.14) is the budget
  constraint plus zero demand for money left over), `money_nonzero_off_equilibrium`.
* (1.16), p. 17: `passive_eqmSet` (every `P₁ > 0` is an equilibrium), `passive_indeterminate`
  (the equilibrium set is uncountable), `passive_taxRate`, `passive_taxRate_strictAnti`
  (p. 18: the tax rate must fall as the price level rises).
* p. 17, active policy: `active_unique_of_strictAnti` (a single crossing gives at most one
  equilibrium), `active_existsUnique` (a continuous surplus rule that is weakly increasing in
  `P₁` and positive somewhere gives exactly one equilibrium), `fixed_surplus_active`,
  `propTax_active` (p. 18: a proportional tax is active), `multiple_crossings` (a rule with
  two equilibria — "or multiple crossings").
* §1.9, p. 18: `value_decomp`, `value_decomp_innov` (three sources of variation in the value of
  debt).
* §1.9, pp. 18–19, the rule `s₁ = α B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)`: `gamma_eqmSet`,
  `gamma_eqmSet_passive`, `gamma_eqmSet_empty`, `gamma_rule_general_iff` (for `γ ≠ 1`, unique
  iff `(α − γ)/(1 − γ) > 0`), `gamma_rule_determinate_iff` (with `α = 1` the
  equilibrium is unique **iff `γ ≠ 1`** — error E2: "responding less than one-for-one" is
  sufficient, not necessary: `less_than_one_for_one_not_necessary`), `gamma_rule_random`
  (the same state by state with a random target), `gamma_not_identified`,
  `obs_equiv_two_period`, `rule_regression_gamma_one` (p. 18: under (1.13) the data satisfy
  `s₁ = 1 · B₀/P₁` exactly).
-/

namespace Cochrane.TwoPeriodModel.ActivePassive

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.MonetaryFiscal

variable {Ω : Type*}

/-! ### (1.14)–(1.15): budget constraint versus equilibrium condition -/

/-- Cochrane (2023), eq. (1.15), p. 16: the budget constraint `B₀ = P₁s₁ + M₁` holds at any
price level: for every `B₀, P₁, s₁` there is exactly one money overhang `M₁`. -/
theorem budget_any_price (B0 P1 s1 : ℝ) : ∃! M1 : ℝ, B0 = P1 * s1 + M1 :=
  ⟨B0 - P1 * s1, by ring, fun M1 h => by linarith⟩

/-- Cochrane (2023), eqs. (1.14)–(1.15), p. 16: the budget constraint plus zero demand for
money at the end of the day, `M₁ = 0`, gives the valuation equation `B₀/P₁ = s₁` (`P₁ ≠ 0`). -/
theorem valuation_of_zero_money {B0 P1 s1 M1 : ℝ} (hP : P1 ≠ 0) (hb : B0 = P1 * s1 + M1)
    (hM : M1 = 0) : B0 / P1 = s1 := by
  rw [← lastDay_iff hP, hb, hM, add_zero]

/-- Cochrane (2023), eqs. (1.14)–(1.15), p. 16: conversely, if `B₀/P₁ = s₁` the money left over
is zero. -/
theorem money_zero_of_valuation {B0 P1 s1 M1 : ℝ} (hP : P1 ≠ 0) (hb : B0 = P1 * s1 + M1)
    (hv : B0 / P1 = s1) : M1 = 0 := by
  have := (lastDay_iff hP).mpr hv
  linarith

/-- Cochrane (2023), p. 16: "budget constraints hold at off-equilibrium prices; equilibrium
conditions need not": at any price level `P₁ > 0` other than `B₀/s₁` (`s₁ > 0`), the budget
constraint holds with a nonzero overhang `M₁ ≠ 0`, so (1.14) fails. -/
theorem money_nonzero_off_equilibrium {B0 P1 s1 M1 : ℝ} (hs : 0 < s1)
    (hb : B0 = P1 * s1 + M1) (hne : P1 ≠ B0 / s1) : M1 ≠ 0 := by
  intro hM
  apply hne
  rw [eq_div_iff hs.ne']
  linarith

/-! ### Fiscal rules and their equilibrium sets -/

/-- Cochrane (2023), p. 17: the equilibrium set of a date-1 fiscal rule `s : ℝ → ℝ`,
`{P₁ > 0 | B₀/P₁ = s(P₁)}`. -/
def eqmSet (B0 : ℝ) (s : ℝ → ℝ) : Set ℝ := {P | 0 < P ∧ B0 / P = s P}

/-- Cochrane (2023), eq. (1.16), p. 17: under the passive rule `s₁ = B₀/P₁`, "`P₁` cancels from
left and right": every positive price level is an equilibrium. -/
theorem passive_eqmSet (B0 : ℝ) : eqmSet B0 (fun P => B0 / P) = Set.Ioi 0 := by
  ext P
  simp [eqmSet]

/-- Cochrane (2023), p. 17: under the passive rule (1.16) "(1.14) no longer determines the
price level": the set of equilibrium price levels is uncountable. -/
theorem passive_indeterminate (B0 : ℝ) : ¬ (eqmSet B0 (fun P => B0 / P)).Countable := by
  rw [passive_eqmSet]
  intro h
  have h1 : Cardinal.mk (Set.Ioi (0 : ℝ)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr h.to_subtype
  rw [Cardinal.mk_Ioi_real] at h1
  exact absurd h1 (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- Cochrane (2023), eq. (1.16) and p. 18: implementing `s₁ = τ₁y₁ = B₀/P₁` requires the tax
rate `τ₁ = B₀/(P₁y₁)` (`P₁, y₁ ≠ 0`). -/
theorem passive_taxRate {B0 P1 y1 τ1 : ℝ} (hP : P1 ≠ 0) (hy : y1 ≠ 0) :
    τ1 * y1 = B0 / P1 ↔ τ1 = B0 / (P1 * y1) := by
  rw [eq_div_iff hP, eq_div_iff (mul_ne_zero hP hy)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 18: "the government must systematically lower the tax rate … as the
price level rises": `P₁ ↦ B₀/(P₁y₁)` is strictly decreasing on `P₁ > 0` (`B₀, y₁ > 0`). -/
theorem passive_taxRate_strictAnti {B0 y1 : ℝ} (hB : 0 < B0) (hy : 0 < y1) :
    StrictAntiOn (fun P => B0 / (P * y1)) (Set.Ioi 0) := by
  intro x hx y _ hxy
  have hx' : (0 : ℝ) < x := hx
  exact div_lt_div_of_pos_left hB (mul_pos hx' hy) (mul_lt_mul_of_pos_right hxy hy)

/-- Cochrane (2023), p. 17: "we just have to exclude the one-for-one case … (or multiple
crossings) so that there is only one solution to (1.14)": if `P ↦ B₀/P − s(P)` is strictly
decreasing on `P > 0` (single crossing), there is at most one equilibrium. -/
theorem active_unique_of_strictAnti {B0 : ℝ} {s : ℝ → ℝ}
    (h : StrictAntiOn (fun P => B0 / P - s P) (Set.Ioi 0)) :
    (eqmSet B0 s).Subsingleton := by
  rintro x ⟨hx, hxe⟩ y ⟨hy, hye⟩
  refine h.injOn hx hy ?_
  simp only [hxe, hye, sub_self]

/-- Cochrane (2023), p. 17, **active fiscal policy determines the price level**: if the surplus
rule `s(P₁)` is continuous and weakly increasing in `P₁` on `P₁ > 0` (a fixed real surplus, a
proportional tax, or austerity in response to inflation) and positive at some price level, then
for `B₀ > 0` there is exactly one equilibrium price level. -/
theorem active_existsUnique {B0 : ℝ} (hB : 0 < B0) {s : ℝ → ℝ}
    (hmono : MonotoneOn s (Set.Ioi 0)) (hcont : ContinuousOn s (Set.Ioi 0))
    (hpos : ∃ p, 0 < p ∧ 0 < s p) : ∃! P : ℝ, 0 < P ∧ B0 / P = s P := by
  obtain ⟨p, hp, hsp⟩ := hpos
  set f : ℝ → ℝ := fun P => B0 / P - s P with hf
  have hanti : StrictAntiOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have h1 : B0 / y < B0 / x := div_lt_div_of_pos_left hB hx' hxy
    have h2 : s x ≤ s y := hmono hx hy hxy.le
    simp only [hf]
    linarith
  have hden : 0 < s p + B0 / p := by positivity
  set a := B0 / (s p + B0 / p) with ha_def
  set b := p + B0 / s p with hb_def
  have ha : 0 < a := div_pos hB hden
  have hpB : p * (B0 / p) = B0 := by field_simp
  have hap : a ≤ p := by
    rw [ha_def, div_le_iff₀ hden, mul_add, hpB]
    nlinarith [mul_pos hp hsp]
  have hpb : p ≤ b := by
    have : 0 < B0 / s p := div_pos hB hsp
    linarith
  have hb : 0 < b := by linarith
  have hfa : 0 < f a := by
    have h1 : B0 / a = s p + B0 / p := by
      rw [ha_def]; field_simp
    have h2 : s a ≤ s p := hmono ha hp hap
    have h3 : 0 < B0 / p := div_pos hB hp
    simp only [hf]
    linarith
  have hfb : f b < 0 := by
    have h1 : B0 / b < s p := by
      rw [div_lt_iff₀ hb, hb_def, mul_add]
      have : s p * (B0 / s p) = B0 := by field_simp
      nlinarith [mul_pos hsp hp]
    have h2 : s p ≤ s b := hmono hp hb hpb
    simp only [hf]
    linarith
  have hab : a ≤ b := hap.trans hpb
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  have hcf : ContinuousOn f (Set.Icc a b) := by
    refine ContinuousOn.sub ?_ (hcont.mono hsub)
    exact continuousOn_const.div continuousOn_id (fun x hx => (hsub hx).ne')
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hab hcf ⟨hfb.le, hfa.le⟩
  have hc0 : 0 < c := hsub hc
  refine ⟨c, ⟨hc0, by simp only [hf] at hfc; linarith⟩, fun y ⟨hy, hye⟩ => ?_⟩
  refine hanti.injOn hy hc0 ?_
  simp only [hf, hye, sub_self]
  simp only [hf] at hfc
  exact hfc.symm

/-- Cochrane (2023), §1.1 and p. 17: a fixed real surplus `s₁ > 0` is an active policy: exactly
one equilibrium price level. -/
theorem fixed_surplus_active {B0 s1 : ℝ} (hB : 0 < B0) (hs : 0 < s1) :
    ∃! P : ℝ, 0 < P ∧ B0 / P = (fun _ => s1) P :=
  active_existsUnique hB (fun _ _ _ _ _ => le_rfl) continuousOn_const ⟨1, one_pos, hs⟩

/-- Cochrane (2023), pp. 17–18: "with a proportional tax on income … the real surplus
`s₁ = τy₁ − g₁` is then independent of the price level, so fiscal policy is active": exactly one
equilibrium when `τy₁ − g₁ > 0`. -/
theorem propTax_active {B0 τ y1 g1 : ℝ} (hB : 0 < B0) (hs : 0 < τ * y1 - g1) :
    ∃! P : ℝ, 0 < P ∧ B0 / P = (fun _ => τ * y1 - g1) P :=
  fixed_surplus_active hB hs

/-- Cochrane (2023), p. 17, "(or multiple crossings)": a surplus rule can cross the valuation
curve more than once; for `B₀ > 0` the rule `s(P) = B₀(3 − P)/2` has the two equilibria
`P₁ = 1` and `P₁ = 2`, so it is not active. -/
theorem multiple_crossings {B0 : ℝ} :
    (1 : ℝ) ∈ eqmSet B0 (fun P => B0 * (3 - P) / 2) ∧
      (2 : ℝ) ∈ eqmSet B0 (fun P => B0 * (3 - P) / 2) := by
  refine ⟨⟨one_pos, by ring⟩, ⟨two_pos, by ring⟩⟩

/-! ### §1.9: three sources of variation in the value of debt -/

/-- Cochrane (2023), §1.9, p. 18: `B₀/P₁ = B₀/P₁* + B₀(1/P₁ − 1/P₁*)`: nominal debt, the
price-level target, and inflation different from the target. -/
theorem value_decomp (B0 P1 Pstar : ℝ) : B0 / P1 = B0 / Pstar + B0 * (1 / P1 - 1 / Pstar) := by
  ring

/-- Cochrane (2023), §1.9, p. 18: the unexpected value of debt splits into an innovation in
the target and in inflation relative to the target:
`(E₁ − E₀)(B₀/P₁) = B₀(E₁ − E₀)(1/P₁*) + B₀(E₁ − E₀)(1/P₁ − 1/P₁*)` (`PullOut`, `B₀` known at
date 0). -/
theorem value_decomp_innov (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {B0 P1 Pstar : Ω → ℝ}
    (hkB0 : Known 𝔼 0 B0) :
    innov 𝔼 (B0 / P1) = B0 * innov 𝔼 (1 / Pstar) + B0 * innov 𝔼 (1 / P1 - 1 / Pstar) := by
  have hk1 : Known 𝔼 1 B0 := known_mono 𝔼 zero_le_one hkB0
  have e1 : B0 / P1 = B0 * (1 / P1) := by
    funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
  rw [e1]
  unfold innov
  rw [hP 1 B0 _ hk1, hP 0 B0 _ hkB0, map_sub, map_sub]
  funext ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- Cochrane (2023), §1.9, p. 19: the surplus rule `s₁ = α B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)`. -/
noncomputable def gammaRule (α γ B0 Pstar : ℝ) (P : ℝ) : ℝ :=
  α * (B0 / Pstar) + γ * (B0 / P - B0 / Pstar)

/-- Cochrane (2023), §1.9, pp. 18–19: the equilibria of the `γ`-rule are the `P₁ > 0` with
`(1 − γ)B₀/P₁ = (α − γ)B₀/P₁*` (for `γ ≠ 1` this pins down `B₀/P₁`). -/
theorem gamma_eqmSet {α γ B0 Pstar : ℝ} :
    eqmSet B0 (gammaRule α γ B0 Pstar) =
      {P | 0 < P ∧ (1 - γ) * (B0 / P) = (α - γ) * (B0 / Pstar)} := by
  ext P
  simp only [eqmSet, gammaRule, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hP, h⟩ <;> exact ⟨hP, by linarith⟩

/-- Cochrane (2023), §1.9, p. 19: with `α = γ = 1` the `γ`-rule is the passive rule: every
`P₁ > 0` is an equilibrium. -/
theorem gamma_eqmSet_passive (B0 Pstar : ℝ) :
    eqmSet B0 (gammaRule 1 1 B0 Pstar) = Set.Ioi 0 := by
  ext P
  simp only [eqmSet, gammaRule, Set.mem_ofPred_eq, Set.mem_Ioi]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by ring⟩

/-- Cochrane (2023), §1.9, p. 19: with `γ = 1` and `α ≠ 1` there is no equilibrium
(`B₀ ≠ 0`, `P₁* ≠ 0`). -/
theorem gamma_eqmSet_empty {α B0 Pstar : ℝ} (hα : α ≠ 1) (hB : B0 ≠ 0) (hPs : Pstar ≠ 0) :
    eqmSet B0 (gammaRule α 1 B0 Pstar) = ∅ := by
  rw [gamma_eqmSet]
  ext P
  simp only [Set.mem_ofPred_eq, sub_self, zero_mul, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ h
  have : (α - 1) * (B0 / Pstar) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hα) (div_ne_zero hB hPs)
  exact this h.symm

/-- Cochrane (2023), §1.9, pp. 18–19 (**error E2**): with `α = 1`, `B₀ > 0`, `P₁* > 0`, the
`γ`-rule has a unique equilibrium **iff `γ ≠ 1`**, and then `P₁ = P₁*`. -/
theorem gamma_rule_determinate_iff {γ B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) :
    (∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P) ↔ γ ≠ 1 := by
  constructor
  · rintro ⟨P, hP, hu⟩ rfl
    have h1 := hu P hP
    have h2 := hu (P + 1) ⟨by linarith [hP.1], by simp [gammaRule]⟩
    linarith
  · intro hγ
    refine ⟨Pstar, ⟨hPs, by simp [gammaRule]⟩, fun P ⟨hP, h⟩ => ?_⟩
    simp only [gammaRule, one_mul] at h
    have h1 : (1 - γ) * (B0 / P - B0 / Pstar) = 0 := by linarith
    have h2 : B0 / P = B0 / Pstar := by
      rcases mul_eq_zero.mp h1 with h0 | h0
      · exact absurd (by linarith : γ = 1) hγ
      · linarith
    rw [div_eq_div_iff hP.ne' hPs.ne'] at h2
    exact (mul_left_cancel₀ hB.ne' (by linarith : B0 * Pstar = B0 * P)).symm

/-- Cochrane (2023), §1.9, pp. 18–19, general `α`: for `γ ≠ 1`, `B₀ > 0`, `P₁* > 0` the
`γ`-rule has a unique equilibrium iff `(α − γ)/(1 − γ) > 0`, namely
`P₁ = P₁*(1 − γ)/(α − γ)`. -/
theorem gamma_rule_general_iff {α γ B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar)
    (hγ : γ ≠ 1) :
    (∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule α γ B0 Pstar P) ↔ 0 < (α - γ) / (1 - γ) := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  set c := (α - γ) / (1 - γ) with hc
  have key : ∀ P, B0 / P = gammaRule α γ B0 Pstar P ↔ B0 / P = c * (B0 / Pstar) := by
    intro P
    simp only [gammaRule, hc]
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    constructor <;> intro h <;> linarith
  have hX : 0 < B0 / Pstar := div_pos hB hPs
  constructor
  · rintro ⟨P, ⟨hP, h⟩, -⟩
    rw [key] at h
    by_contra hneg
    have : c * (B0 / Pstar) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hX.le
    have : 0 < B0 / P := div_pos hB hP
    linarith
  · intro hcpos
    have hQ : 0 < Pstar / c := div_pos hPs hcpos
    have hsol : B0 / (Pstar / c) = c * (B0 / Pstar) := by
      field_simp
    refine ⟨Pstar / c, ⟨hQ, (key _).mpr hsol⟩, fun P ⟨hP, h⟩ => ?_⟩
    rw [key, ← hsol, div_eq_div_iff hP.ne' hQ.ne'] at h
    exact mul_left_cancel₀ hB.ne' (by linarith)

/-- Cochrane (2023), p. 18 (**error E2**): "active fiscal policy only requires that the
government respond less than one-for-one to the last component" — responding less than
one-for-one (`γ < 1`) is not necessary: the over-responding rule `γ = 2` is also determinate. -/
theorem less_than_one_for_one_not_necessary {B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) :
    ∃ γ : ℝ, 1 < γ ∧ ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P :=
  ⟨2, one_lt_two, (gamma_rule_determinate_iff hB hPs).mpr (by norm_num)⟩

/-- Cochrane (2023), §1.9, pp. 18–19, with a random target: if the surplus follows the
`γ`-rule state by state, `s₁ = B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)`, then for `γ ≠ 1` the only positive
`P₁` solving `B₀/P₁ = s₁` is `P₁ = P₁*`, while for `γ = 1` every positive `P₁` solves it. -/
theorem gamma_rule_random {γ : ℝ} {B0 Pstar : Ω → ℝ} (hB : ∀ ω, 0 < B0 ω)
    (hPs : ∀ ω, 0 < Pstar ω) :
    (γ ≠ 1 → ∀ P1 : Ω → ℝ, (∀ ω, 0 < P1 ω) →
      (Valuation1 B0 P1 (fun ω => gammaRule 1 γ (B0 ω) (Pstar ω) (P1 ω)) ↔ P1 = Pstar)) ∧
    (γ = 1 → ∀ P1 : Ω → ℝ, Valuation1 B0 P1 (fun ω => gammaRule 1 γ (B0 ω) (Pstar ω) (P1 ω))) := by
  refine ⟨fun hγ P1 hP1 => ⟨fun h => funext fun ω => ?_, ?_⟩, fun hγ P1 => ?_⟩
  · obtain ⟨P, -, hu⟩ := (gamma_rule_determinate_iff (hB ω) (hPs ω)).mpr hγ
    exact (hu (P1 ω) ⟨hP1 ω, congrFun h ω⟩).trans (hu (Pstar ω)
      ⟨hPs ω, by simp [gammaRule]⟩).symm
  · rintro rfl
    funext ω
    simp [gammaRule]
  · subst hγ
    funext ω
    simp only [Pi.div_apply, gammaRule]
    ring

/-- Cochrane (2023), p. 19: "the parameter `γ` … is not identified": for every `γ ≠ 1` (with
`α = 1`) the equilibrium is the same, `P₁ = P₁*` and `s₁ = B₀/P₁*`. -/
theorem gamma_not_identified {γ γ' B0 Pstar P P' : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar)
    (hγ : γ ≠ 1) (hγ' : γ' ≠ 1) (hP : 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P)
    (hP' : 0 < P' ∧ B0 / P' = gammaRule 1 γ' B0 Pstar P') :
    P = P' ∧ gammaRule 1 γ B0 Pstar P = gammaRule 1 γ' B0 Pstar P' ∧ P = Pstar := by
  obtain ⟨Q, -, hu⟩ := (gamma_rule_determinate_iff hB hPs).mpr hγ
  obtain ⟨Q', -, hu'⟩ := (gamma_rule_determinate_iff hB hPs).mpr hγ'
  have h1 : P = Pstar := (hu P hP).trans (hu Pstar ⟨hPs, by simp [gammaRule]⟩).symm
  have h2 : P' = Pstar := (hu' P' hP').trans (hu' Pstar ⟨hPs, by simp [gammaRule]⟩).symm
  refine ⟨h1.trans h2.symm, ?_, h1⟩
  rw [h1, h2]
  simp [gammaRule]

/-- Cochrane (2023), p. 19, **observational equivalence**: a passive regime (`α = γ = 1`) whose
price level is set elsewhere at `P₁*`, and the active regime (`α = 1`, `γ = 0`) produce the same
observables `(P₁, s₁) = (P₁*, B₀/P₁*)`: `P₁*` is an equilibrium of the passive rule, and the
active rule's unique equilibrium is `P₁*`, with the same surplus. -/
theorem obs_equiv_two_period {B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) :
    Pstar ∈ eqmSet B0 (gammaRule 1 1 B0 Pstar) ∧
      (∀ P, P ∈ eqmSet B0 (gammaRule 1 0 B0 Pstar) ↔ P = Pstar) ∧
      gammaRule 1 1 B0 Pstar Pstar = gammaRule 1 0 B0 Pstar Pstar ∧
      gammaRule 1 0 B0 Pstar Pstar = B0 / Pstar := by
  obtain ⟨Q, -, hu⟩ := (gamma_rule_determinate_iff (γ := 0) hB hPs).mpr (by norm_num)
  have hstar : Pstar ∈ eqmSet B0 (gammaRule 1 0 B0 Pstar) := ⟨hPs, by simp [gammaRule]⟩
  refine ⟨⟨hPs, by simp [gammaRule]⟩, fun P => ⟨fun h => (hu P h).trans (hu Pstar hstar).symm,
    fun h => h ▸ hstar⟩, by simp [gammaRule], by simp [gammaRule]⟩

/-- Cochrane (2023), p. 18: "one is tempted to run a regression, say `s₁ = a + γ(B₀/P₁) + u₁`
… the regression would estimate `γ = 1`": in every equilibrium of the active rule (1.13)
`s₁ = B₀/P₁*`, the data satisfy `s₁ = 0 + 1 · B₀/P₁` exactly. -/
theorem rule_regression_gamma_one {B0 Pstar P1 : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar)
    (h : 0 < P1 ∧ B0 / P1 = B0 / Pstar) : B0 / Pstar = 0 + 1 * (B0 / P1) ∧ P1 = Pstar := by
  refine ⟨by rw [h.2]; ring, ?_⟩
  have h2 := h.2
  rw [div_eq_div_iff h.1.ne' hPs.ne'] at h2
  exact (mul_left_cancel₀ hB.ne' (by linarith : B0 * P1 = B0 * Pstar))

end Cochrane.TwoPeriodModel.ActivePassive

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links: Cochrane's active/passive fiscal policy and Woodford's Ricardian rules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.8–1.9, pp. 15–19,
compared with Woodford (2003), *Interest and Prices*, Chapter 4, §4, pp. 311–314
(locally Ricardian tax rules) and Chapter 2, §4.1, p. 124 (a Ricardian fiscal rule implies the
transversality condition).

The Woodford material is **restated** from the Woodford Chapter 4 project
(`NeoWicksellianFramework/Fiscal.lean`: `Debt45`, `dRec`, `eq_dRec`, `rec_bounded`,
`rec_unbounded`, `LocallyRicardian`, `locallyRicardian_iff`; `BlanchardKahn.lean`:
`abs_rec_le`) and the Woodford Chapter 2 project (`PriceLevelDetermination/GlobalDynamics.lean`:
`discount`, `ricardian_step`, `ricardian_discounted`, `ricardian_tvc`,
`ricardian_tvc_fails_of_alpha_zero`); nothing is imported from those projects.

## Main results (the links)

* Cochrane's `γ` (the surplus response to the real value of debt, p. 18) plays the role of
  Woodford's `τ_b` in (4.4). `passive_locallyRicardian`: Cochrane's passive response `γ = 1` is
  locally Ricardian for every `β > 0`; `fixed_surplus_not_locallyRicardian`: Cochrane's active
  benchmark `γ = 0` (surpluses that ignore debt) is not, for `0 < β ≤ 1`;
  `locallyRicardian_iff_interval`: locally Ricardian iff `1 − β < τ_b < 1 + β`.
* `two_period_indeterminate_imp_locallyRicardian`: a `γ`-rule that leaves the two-period price
  level indeterminate is locally Ricardian. The converse fails:
  `locallyRicardian_two_period_determinate` (`γ = 1 − β/2` is locally Ricardian yet
  determinate in two periods) — "passive" is the single point `γ = 1` with a last day and an
  interval with an infinite horizon. `not_locallyRicardian_two_period_determinate`: every
  non-Ricardian `γ` gives a determinate two-period price level.
* `passive_is_alpha_one`: Cochrane's passive rule (1.16), `P₁s₁ = B₀`, is Woodford's (4.2)
  Ricardian rule `T = αW − ΔM` with `α = 1` and no money; `alpha_one_debt_retired`: under it
  discounted end-of-period liabilities are zero at every date, so the transversality condition
  holds for every price path, just as (1.14) holds for every `P₁` (`passive_valuation_any_price`);
  `zero_surplus_restricts_prices`: with `α = 0` the transversality condition fails unless
  liabilities are zero, so it restricts prices — the fiscal-theory reading.
-/

namespace Cochrane.TwoPeriodModel.Links

open Filter Topology
open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.ActivePassive

variable {Ω : Type*}

/-! ### Restated from the Woodford Chapter 4 project -/

/-- Woodford (2003), p. 277 and Prop. C.2, p. 672 (restated from the Woodford Chapter 4
project): a stable scalar recursion `x_{t+1} = λ x_t + u_t` with `|λ| < 1` and bounded `u` stays
bounded; used for Cochrane (2023), §1.9, p. 18. -/
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

/-- Woodford (2003), eq. (4.5), p. 313 (restated from the Woodford Chapter 4 project): the law
of motion of real debt under the tax rule (4.4),
`b̂_t = β⁻¹[(1 − τ_b) b̂_{t−1} − (b̄ + τ_π) π_t + (1 − τ_g) Ĝ_t − τ_y Ŷ_t]
+ (b̄ − β⁻¹τ_i) î_t − β⁻¹ v_t`, with `d_t = b̂_{t−1}`; compared with Cochrane (2023), §1.9,
p. 18. -/
def Debt45 (β bb τb τg τπ τy τi : ℝ) (d π G Y i v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
    (bb - β⁻¹ * τi) • i t - β⁻¹ • v t

/-- Woodford (2003), (4.5), p. 313 (restated from the Woodford Chapter 4 project): the debt
path generated from `d_0` and inputs `u_t` by `d_{t+1} = γ d_t + u_t`; used for Cochrane
(2023), §1.9, p. 18. -/
def dRec (γ : ℝ) (u : ℕ → Ω → ℝ) (d0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d0
  | t + 1 => γ • dRec γ u d0 t + u t

/-- Woodford (2003), (4.5), pp. 313–314 (restated from the Woodford Chapter 4 project): a
solution of `d_{t+1} = γ d_t + u_t` is `dRec`; used for Cochrane (2023), §1.9, p. 18. -/
theorem eq_dRec {γ : ℝ} {u d : ℕ → Ω → ℝ} (hd : ∀ t, d (t + 1) = γ • d t + u t) :
    d = dRec γ u (d 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [hd t, ih]; rfl

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project): for `|γ| < 1`
the recursion `d_{t+1} = γ d_t + u_t` is bounded-input-bounded-state; used for Cochrane (2023),
§1.9, p. 18. -/
theorem rec_bounded {γ B U : ℝ} (hγ : |γ| < 1) {u d : ℕ → Ω → ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hu : ∀ t ω, |u t ω| ≤ U) (hd : ∀ t, d (t + 1) = γ • d t + u t) (h0 : ∀ ω, |d 0 ω| ≤ B) :
    ∀ t ω, |d t ω| ≤ B + U / (1 - |γ|) := by
  intro t ω
  have hq : 0 ≤ U / (1 - |γ|) := div_nonneg hU (by linarith)
  refine (abs_rec_le hγ (u := fun t => u t ω) (x := fun t => d t ω) (fun t => hu t ω) (h0 ω)
    (fun t => by simp [hd t]) t).trans ?_
  exact max_le (by linarith) (by linarith)

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project): for `|γ| ≥ 1`
the recursion is not bounded-input-bounded-state (`|d_t| ≥ εt` for the inputs
`ε (sign γ)^{t+1}`); used for Cochrane (2023), §1.9, p. 18. -/
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

/-- Woodford (2003), p. 312 (restated from the Woodford Chapter 4 project): a tax rule is
**locally Ricardian** if, substituted into (4.5), it keeps real debt bounded for every small
initial debt and all small paths of `π, Ŷ, î, Ĝ, v`; compared with Cochrane's passive policy,
Cochrane (2023), §1.8–1.9, pp. 17–19. -/
def LocallyRicardian (Ω : Type*) (β bb τb τg τπ τy τi : ℝ) : Prop :=
  ∃ δ > 0, ∀ (b0 : ℝ) (d π Y i G v : ℕ → Ω → ℝ), |b0| ≤ δ →
    (∀ t ω, |π t ω| ≤ δ ∧ |Y t ω| ≤ δ ∧ |i t ω| ≤ δ ∧ |G t ω| ≤ δ ∧ |v t ω| ≤ δ) →
    d 0 = (fun _ => b0) → Debt45 β bb τb τg τπ τy τi d π G Y i v → BoundedProc d

/-- Woodford (2003), p. 313 (restated from the Woodford Chapter 4 project): the tax rule (4.4)
is locally Ricardian iff `|β⁻¹(1 − τ_b)| < 1`; compared with Cochrane (2023), §1.9, p. 18. -/
theorem locallyRicardian_iff [Nonempty Ω] {β bb τb τg τπ τy τi : ℝ} (hβ : 0 < β) :
    LocallyRicardian Ω β bb τb τg τπ τy τi ↔ |β⁻¹ * (1 - τb)| < 1 := by
  set γ := β⁻¹ * (1 - τb) with hγ
  constructor
  · intro hR
    by_contra hcon
    have h1 : 1 ≤ |γ| := not_lt.mp hcon
    obtain ⟨δ, hδ, hR⟩ := hR
    set ε := δ / (1 + β) with hε
    have hε0 : 0 < ε := div_pos hδ (by linarith)
    have hεβ : β * ε ≤ δ := by
      rw [hε, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    set s : ℝ := if 0 ≤ γ then 1 else -1 with hs
    have habs : ∀ n : ℕ, |s ^ n| = 1 := by
      intro n; rw [abs_pow]
      have : |s| = 1 := by rw [hs]; split_ifs <;> norm_num
      rw [this, one_pow]
    set u : ℕ → Ω → ℝ := fun t _ => ε * s ^ (t + 1) with hu
    set d := dRec γ u 0 with hd
    have hrec : ∀ t, d (t + 1) = γ • d t + u t := fun t => rfl
    have hB := hR 0 d 0 0 0 0 (fun t _ => -(β * ε * s ^ (t + 1))) (by simp [hδ.le])
      (fun t ω => by
        refine ⟨by simp [hδ.le], by simp [hδ.le], by simp [hδ.le], by simp [hδ.le], ?_⟩
        rw [abs_neg, abs_mul, habs, mul_one, abs_of_pos (mul_pos hβ hε0)]
        exact hεβ)
      (by funext ω; rfl) (fun t => by
        rw [hrec t]
        funext ω
        simp only [hu, hγ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
          smul_eq_mul]
        field_simp
        ring)
    obtain ⟨M, hM⟩ := hB
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have hgrow := rec_unbounded h1 hε0.le (d := d) (fun t => hrec t) rfl
    obtain ⟨n, hn⟩ := exists_nat_gt (M / ε)
    have := hgrow n ω
    have := hM n ω
    rw [div_lt_iff₀ hε0] at hn
    linarith
  · intro hγ1
    refine ⟨1, one_pos, fun b0 d π Y i G v hb0 hin hd0 hd => ?_⟩
    set U := β⁻¹ * (|bb + τπ| + |1 - τg| + |τy|) + |bb - β⁻¹ * τi| + β⁻¹ with hU
    have hβi : 0 < β⁻¹ := inv_pos.mpr hβ
    have hU0 : 0 ≤ U := by positivity
    set u : ℕ → Ω → ℝ := fun t => β⁻¹ • (-(bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
      (bb - β⁻¹ * τi) • i t - β⁻¹ • v t with hu
    have hrec : ∀ t, d (t + 1) = γ • d t + u t := by
      intro t
      rw [hd t]
      funext ω
      simp only [hu, hγ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hub : ∀ t ω, |u t ω| ≤ U := by
      intro t ω
      obtain ⟨a1, a2, a3, a4, a5⟩ := hin t ω
      simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have q1 : |-(bb + τπ) * π t ω + (1 - τg) * G t ω - τy * Y t ω| ≤
          |bb + τπ| + |1 - τg| + |τy| := by
        refine (abs_sub _ _).trans ?_
        refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_neg]
        nlinarith [abs_nonneg (bb + τπ), abs_nonneg (1 - τg), abs_nonneg τy,
          mul_le_mul_of_nonneg_left a1 (abs_nonneg (bb + τπ)),
          mul_le_mul_of_nonneg_left a4 (abs_nonneg (1 - τg)),
          mul_le_mul_of_nonneg_left a2 (abs_nonneg τy)]
      refine (abs_sub _ _).trans ?_
      refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβi]
      nlinarith [mul_le_mul_of_nonneg_left q1 hβi.le,
        mul_le_mul_of_nonneg_left a3 (abs_nonneg (bb - β⁻¹ * τi)),
        mul_le_mul_of_nonneg_left a5 hβi.le]
    exact ⟨1 + U / (1 - |γ|), rec_bounded hγ1 zero_le_one hU0 hub hrec
      (fun ω => by rw [hd0]; simpa using hb0)⟩

/-! ### Cochrane's `γ` versus Woodford's `τ_b` -/

/-- Cochrane (2023), (1.16), p. 17, and §1.9, p. 18, vs Woodford (2003), (4.4), p. 313:
Cochrane's passive response — surpluses rise one-for-one with the real value of debt,
`γ = τ_b = 1` — is locally Ricardian for every `β > 0` (debt is retired each period). -/
theorem passive_locallyRicardian [Nonempty Ω] {β bb τg τπ τy τi : ℝ} (hβ : 0 < β) :
    LocallyRicardian Ω β bb 1 τg τπ τy τi :=
  (locallyRicardian_iff hβ).mpr (by simp)

/-- Cochrane (2023), §1.8, pp. 17–18, vs Woodford (2003), p. 313: Cochrane's active benchmark,
surpluses that do not respond to the value of debt (`γ = τ_b = 0`), is not locally Ricardian
when `0 < β ≤ 1`. -/
theorem fixed_surplus_not_locallyRicardian [Nonempty Ω] {β bb τg τπ τy τi : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) : ¬ LocallyRicardian Ω β bb 0 τg τπ τy τi := by
  rw [locallyRicardian_iff hβ, sub_zero, mul_one, abs_of_pos (inv_pos.mpr hβ), not_lt]
  exact one_le_inv₀ hβ |>.mpr hβ1

/-- Woodford (2003), p. 313, in Cochrane's terms (§1.9, p. 18): the debt response `τ_b` is
locally Ricardian ("passive") iff `1 − β < τ_b < 1 + β` (`β > 0`). -/
theorem locallyRicardian_iff_interval [Nonempty Ω] {β bb τb τg τπ τy τi : ℝ} (hβ : 0 < β) :
    LocallyRicardian Ω β bb τb τg τπ τy τi ↔ 1 - β < τb ∧ τb < 1 + β := by
  rw [locallyRicardian_iff hβ, abs_mul, abs_of_pos (inv_pos.mpr hβ), ← div_eq_inv_mul,
    div_lt_one hβ, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Cochrane (2023), §1.9, pp. 18–19, vs Woodford (2003), p. 313: if the `γ`-rule
`s₁ = B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)` leaves the two-period price level indeterminate (no unique
equilibrium; `B₀, P₁* > 0`), the same response `τ_b = γ` is locally Ricardian. -/
theorem two_period_indeterminate_imp_locallyRicardian [Nonempty Ω]
    {β bb γ τg τπ τy τi B0 Pstar : ℝ} (hβ : 0 < β) (hB : 0 < B0) (hPs : 0 < Pstar)
    (h : ¬ ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P) :
    LocallyRicardian Ω β bb γ τg τπ τy τi := by
  have hγ : γ = 1 := by
    by_contra hne
    exact h ((gamma_rule_determinate_iff hB hPs).mpr hne)
  rw [hγ]
  exact passive_locallyRicardian hβ

/-- Cochrane (2023), §1.9, pp. 18–19, vs Woodford (2003), p. 313: the converse fails — with an
infinite horizon "passive" is an interval of responses, with a last day only `γ = 1`: the
response `γ = 1 − β/2` is locally Ricardian, yet the two-period `γ`-rule with it has a unique
equilibrium (`0 < β`, `B₀, P₁* > 0`). -/
theorem locallyRicardian_two_period_determinate [Nonempty Ω] {β bb τg τπ τy τi B0 Pstar : ℝ}
    (hβ : 0 < β) (hB : 0 < B0) (hPs : 0 < Pstar) :
    LocallyRicardian Ω β bb (1 - β / 2) τg τπ τy τi ∧
      ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 (1 - β / 2) B0 Pstar P := by
  refine ⟨(locallyRicardian_iff_interval hβ).mpr ⟨by linarith, by linarith⟩,
    (gamma_rule_determinate_iff hB hPs).mpr ?_⟩
  intro h
  linarith

/-- Cochrane (2023), §1.9, pp. 18–19, vs Woodford (2003), p. 313: every response that is not
locally Ricardian gives a determinate two-period price level (`β, B₀, P₁* > 0`). -/
theorem not_locallyRicardian_two_period_determinate [Nonempty Ω]
    {β bb γ τg τπ τy τi B0 Pstar : ℝ} (hβ : 0 < β) (hB : 0 < B0) (hPs : 0 < Pstar)
    (h : ¬ LocallyRicardian Ω β bb γ τg τπ τy τi) :
    ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P := by
  refine (gamma_rule_determinate_iff hB hPs).mpr ?_
  rintro rfl
  exact h (passive_locallyRicardian hβ)

/-! ### Restated from the Woodford Chapter 2 project: a Ricardian rule implies the TVC -/

/-- Woodford (2003), §1, p. 66 (restated from the Woodford Chapter 2 project): the
perfect-foresight discount factor `Q_{t,T} = ∏_{s=t}^{T-1} Q_{s,s+1}`; compared with Cochrane
(2023), (1.16), p. 17. -/
def discount (q : ℕ → ℝ) (t T : ℕ) : ℝ := ∏ s ∈ Finset.Ico t T, q s

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): under
`T_t = αW_t − Δ_tM_t` the government budget gives `Q_{t,t+1}W_{t+1} = (1 − α)W_t`; compared
with Cochrane (2023), (1.16), p. 17. -/
theorem ricardian_step {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (t : ℕ)
    (hgov : q t * W (t + 1) = W t - Tx t - Δ t * M t)
    (hrule : Tx t = α * W t - Δ t * M t) : q t * W (t + 1) = (1 - α) * W t := by
  rw [hgov, hrule]; ring

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): iterating,
`Q_{t,t+n}W_{t+n} = (1 − α)ⁿ W_t`; compared with Cochrane (2023), (1.16), p. 17. -/
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
`0 < α ≤ 1`, `Q_{t,T}W_T → 0` whatever the paths of the other variables; compared with
Cochrane (2023), (1.16), p. 17. -/
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

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): with
`α = 0`, `Q_{t,T}W_T = W_t` for `T ≥ t`, so the transversality condition fails whenever
`W_t ≠ 0`; compared with Cochrane (2023), §1.8, p. 17. -/
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

/-! ### Cochrane's passive rule is Woodford's Ricardian rule with `α = 1` -/

/-- Cochrane (2023), (1.16), p. 17, vs Woodford (2003), (4.2), p. 124: with no money (`M = 0`),
nominal taxes `T = P₁s₁` and maturing liabilities `W = B₀`, Woodford's rule `T = αW − ΔM` with
`α = 1` is exactly Cochrane's passive rule `s₁ = B₀/P₁` (`P₁ ≠ 0`). -/
theorem passive_is_alpha_one {B0 P1 s1 Δ : ℝ} (hP : P1 ≠ 0) :
    P1 * s1 = 1 * B0 - Δ * 0 ↔ s1 = B0 / P1 := by
  rw [one_mul, mul_zero, sub_zero, eq_div_iff hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), (1.16), p. 17: under the passive rule the valuation equation (1.14) holds
at every positive price level, the two-period counterpart of Woodford's "the transversality
condition necessarily holds" (`ricardian_tvc`). -/
theorem passive_valuation_any_price (B0 P1 : Ω → ℝ) : Valuation1 B0 P1 (B0 / P1) := rfl

/-- Woodford (2003), (4.2), p. 124 with `α = 1`, in Cochrane's terms ((1.16), p. 17): the
passive rule retires all liabilities each period, `Q_{t,t+1}W_{t+1} = 0`, so discounted
liabilities `Q_{t,T}W_T` vanish for every `T > t` and the transversality condition holds for any
price path. -/
theorem alpha_one_debt_retired {q W Tx Δ M : ℕ → ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = 1 * W s - Δ s * M s) (t n : ℕ) :
    q t * W (t + 1) = 0 ∧ discount q t (t + (n + 1)) * W (t + (n + 1)) = 0 := by
  refine ⟨by rw [ricardian_step t (hgov t) (hrule t)]; ring, ?_⟩
  rw [ricardian_discounted hgov hrule t (n + 1)]
  simp

/-- Cochrane (2023), §1.8, p. 17 ("a passive policy is a choice"), vs Woodford (2003), p. 124:
when taxes do not respond to liabilities (`α = 0`, the analogue of a fixed surplus), the
transversality condition fails at every date with nonzero liabilities: it is not automatically
satisfied but restricts the price path — the valuation equation then determines prices. -/
theorem zero_surplus_restricts_prices {q W Tx Δ M : ℕ → ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = 0 * W s - Δ s * M s) (t : ℕ) :
    Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) → W t = 0 := by
  intro h
  by_contra hW
  exact ricardian_tvc_fails_of_alpha_zero hgov hrule t hW h

end Cochrane.TwoPeriodModel.Links

set_option linter.style.longLine false
#print axioms Cochrane.TwoPeriodModel.SchurStable
#print axioms Cochrane.TwoPeriodModel.disc
#print axioms Cochrane.TwoPeriodModel.root₁
#print axioms Cochrane.TwoPeriodModel.root₂
#print axioms Cochrane.TwoPeriodModel.root_sum
#print axioms Cochrane.TwoPeriodModel.root_prod
#print axioms Cochrane.TwoPeriodModel.root_eq
#print axioms Cochrane.TwoPeriodModel.normSq_root_of_neg
#print axioms Cochrane.TwoPeriodModel.norm_root_of_nonneg
#print axioms Cochrane.TwoPeriodModel.schurStable_iff_roots
#print axioms Cochrane.TwoPeriodModel.chSeq
#print axioms Cochrane.TwoPeriodModel.convSeq
#print axioms Cochrane.TwoPeriodModel.convSeq_rec
#print axioms Cochrane.TwoPeriodModel.chSeq_eq_convSeq
#print axioms Cochrane.TwoPeriodModel.norm_convSeq_le
#print axioms Cochrane.TwoPeriodModel.abs_chSeq_le
#print axioms Cochrane.TwoPeriodModel.tendsto_chSeq
#print axioms Cochrane.TwoPeriodModel.tr2
#print axioms Cochrane.TwoPeriodModel.det2
#print axioms Cochrane.TwoPeriodModel.tr2_eq_trace
#print axioms Cochrane.TwoPeriodModel.det2_eq_det
#print axioms Cochrane.TwoPeriodModel.sq_eq_cayleyHamilton
#print axioms Cochrane.TwoPeriodModel.pow_succ_eq
#print axioms Cochrane.TwoPeriodModel.abs_pow_entry_le
#print axioms Cochrane.TwoPeriodModel.tendsto_pow_entry
#print axioms Cochrane.TwoPeriodModel.BoundedSeq
#print axioms Cochrane.TwoPeriodModel.homogeneous_iterate
#print axioms Cochrane.TwoPeriodModel.abs_mulVec_le
#print axioms Cochrane.TwoPeriodModel.homogeneous_eq_zero
#print axioms Cochrane.TwoPeriodModel.eq_root_of_eq
#print axioms Cochrane.TwoPeriodModel.exists_eigenvector
#print axioms Cochrane.TwoPeriodModel.exists_bounded_homogeneous
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.mk
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.E
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.const
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.mono
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.tower
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.known
#print axioms Cochrane.TwoPeriodModel.perfectForesight
#print axioms Cochrane.TwoPeriodModel.BoundedProc
#print axioms Cochrane.TwoPeriodModel.BoundedVec
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.Adapted
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.IsAR1
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.E_neg
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.E_smul
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.E_E_self
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.abs_E_le
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.bounded_E
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.ar1_iterate
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forward_iterate
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forward_unique
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.E_tsum
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forwardSeries
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.PullOut
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.Solves
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.AdaptedVec
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.system_iterate
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.system_unique
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.system_not_unique
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.Determinate
#print axioms Cochrane.TwoPeriodModel.ExpectationSystem.determinate_iff
#print axioms Cochrane.TwoPeriodModel.perfectForesight_pullOut
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.TwoPeriodModel.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.Solves
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.E_of_known
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.solves_adapted
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.iterate_A15
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.summable_A16
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.ScalarEq
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.scalarSol
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.scalarSol_apply
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.scalarEq_iff
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.scalar_homog
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.sunspotFamily
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.homog_solves
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.solves_add_homog
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.existsUnique_iff
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.ar1_decay
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.predetermined_restriction
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.summable_geom_mul
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.abel_tsum
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.TwoPeriodModel.ForwardSolution.E_tsum_dom
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.Known
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_const
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_E
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_mono
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_add
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_sub
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_smul
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_mul
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_inv
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_div
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.lastDay_iff
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.lastDay_existsUnique
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.lastDay_eq
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.lastDay_none
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.excess_money_iff
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.money_shortage_iff
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.propTax_real
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.Valuation1
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.Flow0
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.BondPrice0
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.rate
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.bondPrice_eq_inv_one_add_rate
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.bondPrice_R
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.Valuation0
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.pv
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.known_pv
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.flow_real
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.revenue_eq
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.valuation0_of_flow
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.flow_iff_valuation0
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.Equilibrium
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.price1_eq
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.price0_eq
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.equilibrium_iff
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.equilibrium_existsUnique
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.no_equilibrium_of_s1_nonpos
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.no_equilibrium_of_pv_nonpos
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.price0_strictAnti_beta
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.price0_strictAnti_Es1
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.price0_eq_of_pv_eq
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.price0_any_level
#print axioms Cochrane.TwoPeriodModel.TwoPeriod.coin_equilibrium
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.eq_1_8
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.revenue_invariant
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.shareSplit_equilibrium
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.shareSplit_unique
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.doubling
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.rate_strictAnti
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.shareSplit_rate_rises
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.TargetEquilibrium
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.expected_inflation
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.E0_invP1
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.target_bond_demand
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.target_existsUnique
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.determinate_under_peg
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.fisherian_two_period
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.innov
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.unexpected_inflation
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.inflation_decomposition
#print axioms Cochrane.TwoPeriodModel.MonetaryFiscal.no_fiscal_news
#print axioms Cochrane.TwoPeriodModel.DebtSales.price0_formula
#print axioms Cochrane.TwoPeriodModel.DebtSales.equityIssue_price1
#print axioms Cochrane.TwoPeriodModel.DebtSales.equityIssue_revenue
#print axioms Cochrane.TwoPeriodModel.DebtSales.equityIssue_lowers_price0
#print axioms Cochrane.TwoPeriodModel.DebtSales.equityIssue_funds_deficit
#print axioms Cochrane.TwoPeriodModel.DebtSales.borrow_price0
#print axioms Cochrane.TwoPeriodModel.DebtSales.borrow_value_rises
#print axioms Cochrane.TwoPeriodModel.DebtSales.borrow_keeps_price1_iff
#print axioms Cochrane.TwoPeriodModel.DebtSales.borrow_implementable
#print axioms Cochrane.TwoPeriodModel.DebtSales.borrow_debt_corrected
#print axioms Cochrane.TwoPeriodModel.DebtSales.borrow_printed_fails
#print axioms Cochrane.TwoPeriodModel.DebtSales.inflate_price0_rises
#print axioms Cochrane.TwoPeriodModel.DebtSales.inflate_value_unchanged
#print axioms Cochrane.TwoPeriodModel.DebtSales.inflate_real_debt_falls_by_deficit
#print axioms Cochrane.TwoPeriodModel.DebtSales.ar1_price0_rises_more
#print axioms Cochrane.TwoPeriodModel.DebtSales.ar1_value_falls
#print axioms Cochrane.TwoPeriodModel.DebtSales.maturing_value_change
#print axioms Cochrane.TwoPeriodModel.DebtSales.sShape_two_period
#print axioms Cochrane.TwoPeriodModel.DebtSales.steady_price0_iff
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_price1_iff
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_price1
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_pv
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_valuation
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_existsUnique
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_price0
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_borrow
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_inflate
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_superinflate
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_price0_strictAnti_B0
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.RuleTargetEquilibrium
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_target_price0
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_target_existsUnique
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_higher_rate_lowers_price0
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_higher_rate_fiscal_tightening
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_flat_demand
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.rule_revenue
#print axioms Cochrane.TwoPeriodModel.PriceLevelTarget.unit_elastic
#print axioms Cochrane.TwoPeriodModel.ActivePassive.budget_any_price
#print axioms Cochrane.TwoPeriodModel.ActivePassive.valuation_of_zero_money
#print axioms Cochrane.TwoPeriodModel.ActivePassive.money_zero_of_valuation
#print axioms Cochrane.TwoPeriodModel.ActivePassive.money_nonzero_off_equilibrium
#print axioms Cochrane.TwoPeriodModel.ActivePassive.eqmSet
#print axioms Cochrane.TwoPeriodModel.ActivePassive.passive_eqmSet
#print axioms Cochrane.TwoPeriodModel.ActivePassive.passive_indeterminate
#print axioms Cochrane.TwoPeriodModel.ActivePassive.passive_taxRate
#print axioms Cochrane.TwoPeriodModel.ActivePassive.passive_taxRate_strictAnti
#print axioms Cochrane.TwoPeriodModel.ActivePassive.active_unique_of_strictAnti
#print axioms Cochrane.TwoPeriodModel.ActivePassive.active_existsUnique
#print axioms Cochrane.TwoPeriodModel.ActivePassive.fixed_surplus_active
#print axioms Cochrane.TwoPeriodModel.ActivePassive.propTax_active
#print axioms Cochrane.TwoPeriodModel.ActivePassive.multiple_crossings
#print axioms Cochrane.TwoPeriodModel.ActivePassive.value_decomp
#print axioms Cochrane.TwoPeriodModel.ActivePassive.value_decomp_innov
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gammaRule
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gamma_eqmSet
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gamma_eqmSet_passive
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gamma_eqmSet_empty
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gamma_rule_determinate_iff
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gamma_rule_general_iff
#print axioms Cochrane.TwoPeriodModel.ActivePassive.less_than_one_for_one_not_necessary
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gamma_rule_random
#print axioms Cochrane.TwoPeriodModel.ActivePassive.gamma_not_identified
#print axioms Cochrane.TwoPeriodModel.ActivePassive.obs_equiv_two_period
#print axioms Cochrane.TwoPeriodModel.ActivePassive.rule_regression_gamma_one
#print axioms Cochrane.TwoPeriodModel.Links.abs_rec_le
#print axioms Cochrane.TwoPeriodModel.Links.Debt45
#print axioms Cochrane.TwoPeriodModel.Links.dRec
#print axioms Cochrane.TwoPeriodModel.Links.eq_dRec
#print axioms Cochrane.TwoPeriodModel.Links.rec_bounded
#print axioms Cochrane.TwoPeriodModel.Links.rec_unbounded
#print axioms Cochrane.TwoPeriodModel.Links.LocallyRicardian
#print axioms Cochrane.TwoPeriodModel.Links.locallyRicardian_iff
#print axioms Cochrane.TwoPeriodModel.Links.passive_locallyRicardian
#print axioms Cochrane.TwoPeriodModel.Links.fixed_surplus_not_locallyRicardian
#print axioms Cochrane.TwoPeriodModel.Links.locallyRicardian_iff_interval
#print axioms Cochrane.TwoPeriodModel.Links.two_period_indeterminate_imp_locallyRicardian
#print axioms Cochrane.TwoPeriodModel.Links.locallyRicardian_two_period_determinate
#print axioms Cochrane.TwoPeriodModel.Links.not_locallyRicardian_two_period_determinate
#print axioms Cochrane.TwoPeriodModel.Links.discount
#print axioms Cochrane.TwoPeriodModel.Links.ricardian_step
#print axioms Cochrane.TwoPeriodModel.Links.ricardian_discounted
#print axioms Cochrane.TwoPeriodModel.Links.ricardian_tvc
#print axioms Cochrane.TwoPeriodModel.Links.ricardian_tvc_fails_of_alpha_zero
#print axioms Cochrane.TwoPeriodModel.Links.passive_is_alpha_one
#print axioms Cochrane.TwoPeriodModel.Links.passive_valuation_any_price
#print axioms Cochrane.TwoPeriodModel.Links.alpha_one_debt_retired
#print axioms Cochrane.TwoPeriodModel.Links.zero_surplus_restricts_prices
