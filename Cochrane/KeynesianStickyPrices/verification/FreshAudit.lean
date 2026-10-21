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
import Mathlib.Analysis.Normed.Group.Tannery
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

namespace Cochrane.KeynesianStickyPrices

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

end Cochrane.KeynesianStickyPrices

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

namespace Cochrane.KeynesianStickyPrices

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

end Cochrane.KeynesianStickyPrices

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

namespace Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree

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

end Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree

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

namespace Cochrane.KeynesianStickyPrices.ForwardSolution

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

end Cochrane.KeynesianStickyPrices.ForwardSolution

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Shared tools for Chapter 17

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, pp. 397–421, and Online
Appendix A1, §1.7–§1.8 and §1.13.1, pp. 569–572 and 586–588: general lemmas used by both the
simple-model chain (`StaticIS` … `AdaptiveTaylor`) and the full-model chain (`FullModel` …
`History`). They were proved separately in the two chains and are collected here once.

* Stable scalar recursions: if `x_{n+1} = a x_n + f_n` with `|a| < 1` and `f_n → 0` then
  `x_n → 0` (`tendsto_zero_of_stable`), and the averaging form `tendsto_of_stable_avg`
  (long-run responses, pp. 406 and 408).
* Forward sums `∑_j qʲ g_{n+j}` of a bounded path with `|q| < 1`: recursion and bound
  (`fwd_sum_props`) and limit (`fwd_sum_tendsto`, dominated convergence) — eq. (5.5), p. 119,
  as used on p. 408.
* Infinite-past (ℤ-indexed) backward recursions `x_{s+1} = a x_s + w_{s+1}`, `|a| < 1`: the
  backward moving average (17.8), p. 400 (`backward_iterate`, `eq_backward_series`,
  `backward_series_solves`), and its homogeneous corollary `int_homog_zero` (a bounded solution
  of `x_{s+1} = a x_s` on ℤ vanishes), used for the anticipated-from-the-infinite-past path of
  Fig. 17.5, p. 409.
* The structural matrices of the three-equation model, p. 420 and A1 (1.55), p. 586:
  `Pmat`, `Qmat` and the solved transition matrix `solvedA P Q = P⁻¹Q` with its trace and
  determinant (`tr2_solvedA`, `det2_solvedA`, `det2_Pmat`).
-/

namespace Cochrane.KeynesianStickyPrices.SharedTools

open Filter Topology

/-! ### Stable recursions -/

/-- Cochrane (2023), p. 406 (supporting lemma, proved here): if `x_{n+1} = a x_n + f_n` with
`|a| < 1` and `f_n → 0`, then `x_n → 0`. -/
theorem tendsto_zero_of_stable {a : ℝ} (ha : |a| < 1) {x f : ℕ → ℝ}
    (h : ∀ n, x (n + 1) = a * x n + f n) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1a : 0 < 1 - |a| := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hf ((1 - |a|) * ε / 2) (by positivity)
  have hk : ∀ k, |x (N + k)| ≤ |a| ^ k * |x N| + ε / 2 := by
    intro k
    induction k with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ k ih =>
      have hfk := hN (N + k) (Nat.le_add_right N k)
      rw [Real.dist_eq, sub_zero] at hfk
      rw [← add_assoc, h]
      calc |a * x (N + k) + f (N + k)| ≤ |a| * |x (N + k)| + |f (N + k)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |a| * (|a| ^ k * |x N| + ε / 2) + (1 - |a|) * ε / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg a)) hfk.le
        _ = |a| ^ (k + 1) * |x N| + ε / 2 := by ring
  have hpow : Tendsto (fun k => |a| ^ k * |x N|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const (|x N|)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hpow (ε / 2) (by positivity)
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 := hk (K + k)
  have h2 := hK (K + k) (Nat.le_add_right K k)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  rw [Real.dist_eq, sub_zero, add_assoc]
  linarith

/-- Cochrane (2023), p. 406 (supporting lemma): if `x_{n+1} = a x_n + b y_n` with `a + b = 1`,
`|a| < 1` and `y_n → ȳ`, then `x_n → ȳ`. -/
theorem tendsto_of_stable_avg {a b yb : ℝ} (ha : |a| < 1) (hab : a + b = 1) {x y : ℕ → ℝ}
    (h : ∀ n, x (n + 1) = a * x n + b * y n) (hy : Tendsto y atTop (𝓝 yb)) :
    Tendsto x atTop (𝓝 yb) := by
  have hf : Tendsto (fun n => b * (y n - yb)) atTop (𝓝 0) := by
    simpa using (hy.sub_const yb).const_mul b
  have := tendsto_zero_of_stable ha (x := fun n => x n - yb) (f := fun n => b * (y n - yb))
    (fun n => by rw [h n]; linear_combination yb * hab) hf
  simpa using this.add_const yb

/-! ### Forward sums -/

/-- Cochrane (2023), p. 408: the forward sum `Y_n = ∑_j qʲ g_{n+j}` of a bounded path, `|q| < 1`,
satisfies `Y_n = g_n + q Y_{n+1}` and `|Y_n| ≤ M/(1 − |q|)`. -/
theorem fwd_sum_props {q M : ℝ} (hq : |q| < 1) {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ M) :
    (∀ n, (∑' j : ℕ, q ^ j * g (n + j)) = g n + q * ∑' j : ℕ, q ^ j * g (n + 1 + j)) ∧
      ∀ n, |∑' j : ℕ, q ^ j * g (n + j)| ≤ M / (1 - |q|) := by
  have hgeo := summable_geometric_of_lt_one (abs_nonneg q) hq
  have hb : ∀ n j, ‖q ^ j * g (n + j)‖ ≤ |q| ^ j * M := fun n j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hg _) (pow_nonneg (abs_nonneg q) j)
  have hs : ∀ n, Summable fun j => q ^ j * g (n + j) := fun n =>
    Summable.of_norm_bounded (hgeo.mul_right M) (hb n)
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [(hs n).tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    refine tsum_congr fun j => ?_
    rw [pow_succ, show n + (j + 1) = n + 1 + j by ring]
    ring
  · have := tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (abs_nonneg q) hq).mul_right M)
      (hb n)
    rw [Real.norm_eq_abs] at this
    simpa [div_eq_mul_inv, mul_comm] using this

/-- Cochrane (2023), p. 408: the forward sum converges to `ḡ/(1 − q)` when `g_n → ḡ`
(dominated convergence for series). -/
theorem fwd_sum_tendsto {q M gb : ℝ} (hq : |q| < 1) {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ M)
    (hlim : Tendsto g atTop (𝓝 gb)) :
    Tendsto (fun n => ∑' j : ℕ, q ^ j * g (n + j)) atTop (𝓝 (gb / (1 - q))) := by
  have hgeo := summable_geometric_of_lt_one (abs_nonneg q) hq
  have hq1 : 1 - q ≠ 0 := by
    intro h0; have : q = 1 := by linarith
    rw [this, abs_one] at hq; exact lt_irrefl _ hq
  have hsum : ∑' j : ℕ, q ^ j * gb = gb / (1 - q) := by
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hq]; field_simp
  rw [← hsum]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => |q| ^ j * M)
    (hgeo.mul_right M) (fun j => ?_) (Eventually.of_forall fun n j => ?_)
  · exact (hlim.comp (tendsto_add_atTop_nat j)).const_mul (q ^ j)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hg _) (pow_nonneg (abs_nonneg q) j)

/-! ### Infinite-past backward recursions (ℤ-indexed) -/

/-- Cochrane (2023), eq. (17.8), p. 400: iterating the stable backward recursion
`x_{s+1} = a x_s + w_{s+1}` on the integers `k` times,
`x_t = aᵏ x_{t−k} + ∑_{j<k} aʲ w_{t−j}`. -/
theorem backward_iterate {a : ℝ} {x w : ℤ → ℝ} (h : ∀ s, x (s + 1) = a * x s + w (s + 1))
    (t : ℤ) (k : ℕ) :
    x t = a ^ k * x (t - k) + ∑ j ∈ Finset.range k, a ^ j * w (t - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := h (t - (k + 1 : ℕ))
    have e : t - ((k + 1 : ℕ) : ℤ) + 1 = t - k := by push_cast; ring
    rw [e] at hs
    rw [ih, hs, Finset.sum_range_succ]
    ring

/-- Cochrane (2023), eq. (17.8), p. 400: with `|a| < 1`, every bounded solution on the integers
of `x_{s+1} = a x_s + w_{s+1}` (bounded `w`) is the backward moving average
`x_t = ∑_{j ≥ 0} aʲ w_{t−j}`. -/
theorem eq_backward_series {a Mx Mw : ℝ} (ha : |a| < 1) {x w : ℤ → ℝ}
    (hx : ∀ s, |x s| ≤ Mx) (hw : ∀ s, |w s| ≤ Mw) (h : ∀ s, x (s + 1) = a * x s + w (s + 1))
    (t : ℤ) : x t = ∑' j : ℕ, a ^ j * w (t - j) := by
  have hsum : Summable fun j : ℕ => a ^ j * w (t - j) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right Mw)
      fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hw _) (pow_nonneg (abs_nonneg a) j)
  have hlim : Tendsto (fun k => ∑ j ∈ Finset.range k, a ^ j * w (t - j)) atTop (𝓝 (x t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun k => |a| ^ k * Mx) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, backward_iterate h t k, abs_abs,
        show ∀ A S : ℝ, S - (A + S) = -A from fun A S => by ring, abs_neg, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hx _) (pow_nonneg (abs_nonneg a) k)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const Mx
  exact tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat

/-- Cochrane (2023), eq. (17.8), p. 400 (converse): for `|a| < 1` and bounded `w`, the backward
moving average is a bounded solution of `x_{s+1} = a x_s + w_{s+1}`. -/
theorem backward_series_solves {a Mw : ℝ} (ha : |a| < 1) {w : ℤ → ℝ} (hw : ∀ s, |w s| ≤ Mw) :
    (∀ s, (∑' j : ℕ, a ^ j * w (s + 1 - j)) = a * (∑' j : ℕ, a ^ j * w (s - j)) + w (s + 1)) ∧
      ∀ s, |∑' j : ℕ, a ^ j * w (s - j)| ≤ Mw / (1 - |a|) := by
  have hg := summable_geometric_of_lt_one (abs_nonneg a) ha
  have hsum : ∀ s, Summable fun j : ℕ => a ^ j * w (s - j) := fun s =>
    Summable.of_norm_bounded (hg.mul_right Mw) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hw _) (pow_nonneg (abs_nonneg a) j)
  refine ⟨fun s => ?_, fun s => ?_⟩
  · rw [(hsum (s + 1)).tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
    rw [add_comm]
    congr 1
    refine tsum_congr fun j => ?_
    rw [pow_succ, show s + 1 - ((j : ℤ) + 1) = s - j by ring]
    ring
  · have hb : ∀ j : ℕ, ‖a ^ j * w (s - j)‖ ≤ |a| ^ j * Mw := fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hw _) (pow_nonneg (abs_nonneg a) j)
    have := tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_right Mw) hb
    rw [Real.norm_eq_abs] at this
    simpa [div_eq_mul_inv, mul_comm] using this

/-- Cochrane (2023), eq. (17.8), p. 400 and Fig. 17.5, p. 409 (homogeneous case): with
`|a| < 1`, the only bounded solution on the integers of `x_{s+1} = a x_s` is zero (an infinite
past leaves no free initial condition). -/
theorem int_homog_zero {a M : ℝ} (ha : |a| < 1) {x : ℤ → ℝ} (hx : ∀ s, |x s| ≤ M)
    (h : ∀ s, x (s + 1) = a * x s) : x = 0 := by
  funext t
  have e := eq_backward_series ha hx (w := fun _ => 0) (Mw := 0) (fun _ => by simp)
    (fun s => by rw [h s, add_zero]) t
  simpa using e

/-! ### The structural matrices of the three-equation model -/

/-- Cochrane (2023), p. 420: the matrix `A = P⁻¹ Q` of `x_t = A E_t x_{t+1}`, written with the
adjugate of `P`. -/
noncomputable def solvedA (P Q : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(P 1 1 * Q 0 0 - P 0 1 * Q 1 0) / det2 P, (P 1 1 * Q 0 1 - P 0 1 * Q 1 1) / det2 P;
    (P 0 0 * Q 1 0 - P 1 0 * Q 0 0) / det2 P, (P 0 0 * Q 1 1 - P 1 0 * Q 0 1) / det2 P]

/-- `tr A = (P₁₁Q₀₀ − P₀₁Q₁₀ − P₁₀Q₀₁ + P₀₀Q₁₁)/det P`. -/
theorem tr2_solvedA (P Q : Matrix (Fin 2) (Fin 2) ℝ) :
    tr2 (solvedA P Q) =
      (P 1 1 * Q 0 0 - P 0 1 * Q 1 0 - P 1 0 * Q 0 1 + P 0 0 * Q 1 1) / det2 P := by
  simp only [tr2, solvedA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- `det A = det Q / det P`. -/
theorem det2_solvedA {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : det2 P ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : det2 (solvedA P Q) = det2 Q / det2 P := by
  have h : det2 (solvedA P Q) = solvedA P Q 0 0 * solvedA P Q 1 1 -
      solvedA P Q 0 1 * solvedA P Q 1 0 := rfl
  rw [h]
  simp only [solvedA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [div_mul_div_comm, div_mul_div_comm, div_sub_div_same,
    div_eq_div_iff (mul_ne_zero hP hP) hP]
  unfold det2
  ring

/-- Cochrane (2023), p. 420: the structural matrix `P = [[1 + σφ_x, σφ], [−κ, 1]]`. -/
def Pmat (σ κ φ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + σ * φx, σ * φ; -κ, 1]

/-- Cochrane (2023), p. 420: the structural matrix `Q = [[1, σ], [0, β]]`. -/
def Qmat (σ β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, σ; 0, β]

/-- `D = det P = 1 + σφ_x + σκφ`. -/
theorem det2_Pmat (σ κ φ φx : ℝ) : det2 (Pmat σ κ φ φx) = 1 + σ * φx + σ * κ * φ := by
  simp [det2, Pmat]; ring

end Cochrane.KeynesianStickyPrices.SharedTools

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# New vs. old Keynesian models: the static IS curve

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.1 "New vs. old
Keynesian models" and §17.2 "Responses to interest rate changes", pp. 397–401.

The model is the IS curve and Phillips curve (17.1)–(17.2) with a generic expected-inflation
process `πᵉ`; deleting `E_t x_{t+1}` gives the static IS model (17.3)–(17.4), whose single
equilibrium condition is (17.5) `π_t = −σκ i_t + (1 + σκ) πᵉ_t`.

* Adaptive expectations `πᵉ_t = π_{t−1}` (old Keynesian), (17.6): the solution is unique given
  `π_{−1}` (`adaptive_existsUnique`, "determinate"), but under a peg it spirals away:
  `π_t − ī = (1 + σκ)^{t+1}(π_{−1} − ī)` (`adaptive_peg`, `adaptive_peg_unbounded`).
* Rational expectations `πᵉ_t = E_t π_{t+1}` (new Keynesian), (17.7): the coefficient
  `1/(1 + σκ)` lies in `(0, 1)` ("stable"), but any expectational error is possible
  ("indeterminate"): `reFamily_solves`, `eq_reFamily`, `re_indeterminate`, `re_not_unique`.
* (17.8): the finite-start form `reFamily_closed`, and the infinite-past backward moving average
  (`eq_17_8`; converse `SharedTools.backward_series_solves`): every bounded solution has the
  form (17.8), and conversely.
* Figure 17.1 (`fig17_1_path`, `fig17_1_tendsto`, `fig17_1_less_sticky`) and Figure 17.2
  (`fig17_2_solves`, `fig17_2_strictMono`, `fig17_2_tendsto`, `fig17_2_less_sticky`,
  `fig17_2_frictionless_limit`, `fig17_2_dashed`), and the frictionless limit `κ → ∞` of (17.7)
  (`tendsto_coeff_17_7`).
* p. 401: a fully expected rate path brings no expectational errors (`no_surprise_of_known`);
  active fiscal policy, by fixing unexpected inflation, selects one equilibrium
  (`fiscal_selects`).

Everything is stated for an arbitrary `ExpectationSystem`, so it holds under perfect foresight
and under genuine uncertainty. Throughout, `σ, κ > 0` where needed.
-/

namespace Cochrane.KeynesianStickyPrices.StaticIS

open Filter Topology
open SharedTools (eq_backward_series)

variable {Ω : Type*}

/-! ### The model (17.1)–(17.5) -/

/-- Cochrane (2023), eqs. (17.1)–(17.2), pp. 397–398: the IS curve
`x_t = E_t x_{t+1} − σ(i_t − πᵉ_t)` and Phillips curve `π_t = πᵉ_t + κ x_t` with an expected
inflation process `πᵉ`. -/
def ISPhillips (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = 𝔼.E t (x (t + 1)) ω - σ * (i t ω - πe t ω) ∧ π t ω = πe t ω + κ * x t ω

/-- Cochrane (2023), eqs. (17.1)–(17.2), pp. 397–398: eliminating output,
`π_t = (1 + σκ) πᵉ_t − σκ i_t + κ E_t x_{t+1}`. -/
theorem isPhillips_infl {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} {i πe x π : ℕ → Ω → ℝ}
    (h : ISPhillips 𝔼 σ κ i πe x π) (t : ℕ) (ω : Ω) :
    π t ω = (1 + σ * κ) * πe t ω - σ * κ * i t ω + κ * 𝔼.E t (x (t + 1)) ω := by
  obtain ⟨h1, h2⟩ := h t ω
  rw [h2, h1]; ring

/-- Cochrane (2023), eqs. (17.3)–(17.4), p. 398: the static IS curve `x_t = −σ(i_t − πᵉ_t)` and
the Phillips curve `π_t = πᵉ_t + κ x_t`. -/
def StaticModel (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = -σ * (i t ω - πe t ω) ∧ π t ω = πe t ω + κ * x t ω

/-- Cochrane (2023), p. 398: (17.3)–(17.4) are (17.1)–(17.2) with the `E_t x_{t+1}` term
deleted. -/
theorem isPhillips_iff_static_of_E_zero {𝔼 : ExpectationSystem Ω} {σ κ : ℝ}
    {i πe x π : ℕ → Ω → ℝ} (h0 : ∀ t, 𝔼.E t (x (t + 1)) = 0) :
    ISPhillips 𝔼 σ κ i πe x π ↔ StaticModel σ κ i πe x π := by
  unfold ISPhillips StaticModel
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  rw [h0 t, Pi.zero_apply]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨by rw [h1]; ring, h2⟩

/-- Cochrane (2023), eq. (17.5), p. 398: eliminating `x_t` from (17.3)–(17.4), the static model
holds iff output is given by (17.3) and `π_t = −σκ i_t + (1 + σκ) πᵉ_t`. -/
theorem staticModel_iff (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) :
    StaticModel σ κ i πe x π ↔ (∀ t ω, x t ω = -σ * (i t ω - πe t ω)) ∧
      ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * πe t ω := by
  constructor
  · intro h
    refine ⟨fun t ω => (h t ω).1, fun t ω => ?_⟩
    obtain ⟨h1, h2⟩ := h t ω
    rw [h2, h1]; ring
  · rintro ⟨h1, h2⟩ t ω
    refine ⟨h1 t ω, ?_⟩
    rw [h2 t ω, h1 t ω]; ring

/-- Cochrane (2023), eq. (17.5), p. 398: an inflation process is part of an equilibrium of
(17.3)–(17.4) iff it satisfies the single equation (17.5). -/
theorem exists_static_iff_17_5 (σ κ : ℝ) (i πe π : ℕ → Ω → ℝ) :
    (∃ x, StaticModel σ κ i πe x π) ↔
      ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * πe t ω := by
  constructor
  · rintro ⟨x, hx⟩
    exact ((staticModel_iff σ κ i πe x π).mp hx).2
  · intro h
    exact ⟨fun t ω => -σ * (i t ω - πe t ω),
      (staticModel_iff σ κ i πe _ π).mpr ⟨fun _ _ => rfl, h⟩⟩

/-! ### Adaptive expectations (17.6) -/

/-- Cochrane (2023), p. 398: the lagged inflation process `π_{t−1}`, with initial value
`π_{−1}`; adaptive expectations set `πᵉ_t = π_{t−1}`. -/
def lagged (π0 : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => π t

/-- Cochrane (2023), eq. (17.6), p. 398: the adaptive-expectations equilibrium condition
`π_t = (1 + σκ) π_{t−1} − σκ i_t`, given `π_{−1}`. -/
def AdaptiveEq (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω = (1 + σ * κ) * lagged π0 π t ω - σ * κ * i t ω

/-- Cochrane (2023), eq. (17.6), p. 398: with `πᵉ_t = π_{t−1}` the static model (17.3)–(17.4)
reduces to (17.6). -/
theorem exists_static_adaptive_iff (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) :
    (∃ x, StaticModel σ κ i (lagged π0 π) x π) ↔ AdaptiveEq σ κ π0 i π := by
  rw [exists_static_iff_17_5]
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro h <;> rw [h] <;> ring

/-- Cochrane (2023), p. 398: (17.6) rearranged, `π_t − π_{t−1} = −σκ (i_t − π_{t−1})`: a higher
real rate brings inflation down. -/
theorem adaptive_change_iff (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) :
    AdaptiveEq σ κ π0 i π ↔ ∀ t ω,
      π t ω - lagged π0 π t ω = -(σ * κ) * (i t ω - lagged π0 π t ω) := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 399 (the old-Keynesian mechanism): with adaptive expectations a nominal
rate above lagged inflation (a high real rate) lowers output, and lower output lowers
inflation. -/
theorem adaptive_mechanism {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {π0 : Ω → ℝ}
    {i x π : ℕ → Ω → ℝ} (h : StaticModel σ κ i (lagged π0 π) x π) {t : ℕ} {ω : Ω}
    (hi : lagged π0 π t ω < i t ω) : x t ω < 0 ∧ π t ω < lagged π0 π t ω := by
  obtain ⟨h1, h2⟩ := h t ω
  have hx : x t ω < 0 := by rw [h1]; nlinarith
  exact ⟨hx, by rw [h2]; nlinarith⟩

/-- Cochrane (2023), eq. (17.6), p. 398: the solution of (17.6) built forward from `π_{−1}`. -/
def adaptivePath (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => (1 + σ * κ) * π0 ω - σ * κ * i 0 ω
  | t + 1 => fun ω => (1 + σ * κ) * adaptivePath σ κ π0 i t ω - σ * κ * i (t + 1) ω

/-- Cochrane (2023), eq. (17.6), p. 398: `adaptivePath` solves (17.6). -/
theorem adaptivePath_solves (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) :
    AdaptiveEq σ κ π0 i (adaptivePath σ κ π0 i) := by
  intro t ω
  cases t <;> rfl

/-- Cochrane (2023), p. 398, "There is only one equilibrium": two solutions of (17.6) with the
same `π_{−1}` coincide. -/
theorem adaptive_unique {σ κ : ℝ} {π0 : Ω → ℝ} {i π π' : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 i π) (h' : AdaptiveEq σ κ π0 i π') : π = π' := by
  funext t ω
  induction t with
  | zero => rw [h 0 ω, h' 0 ω]; rfl
  | succ t ih => rw [h (t + 1) ω, h' (t + 1) ω]; simp only [lagged]; rw [ih]

/-- Cochrane (2023), p. 398, "determinate": given `π_{−1}`, (17.6) has exactly one solution
(whatever the interest-rate path). -/
theorem adaptive_existsUnique (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) :
    ∃! π, AdaptiveEq σ κ π0 i π :=
  ⟨_, adaptivePath_solves σ κ π0 i, fun _ h => adaptive_unique h (adaptivePath_solves σ κ π0 i)⟩

/-- Cochrane (2023), eq. (17.6), p. 398: under an interest-rate peg `i_t = ī`,
`π_t − ī = (1 + σκ)^{t+1} (π_{−1} − ī)`. -/
theorem adaptive_peg {σ κ ib : ℝ} {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (t : ℕ) (ω : Ω) :
    π t ω = ib + (1 + σ * κ) ^ (t + 1) * (π0 ω - ib) := by
  induction t with
  | zero => rw [h 0 ω]; simp only [lagged]; ring
  | succ t ih => rw [h (t + 1) ω]; simp only [lagged]; rw [ih]; ring

/-- Cochrane (2023), p. 398, "unstable": under a peg, inflation spirals away from the peg,
`|π_t − ī| → ∞`, unless it starts exactly at the peg. -/
theorem adaptive_peg_unbounded {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) {ω : Ω} (hω : π0 ω ≠ ib) :
    Tendsto (fun t => |π t ω - ib|) atTop atTop := by
  have he : (fun t => |π t ω - ib|) = fun t => (1 + σ * κ) ^ (t + 1) * |π0 ω - ib| := by
    funext t
    rw [adaptive_peg h t ω, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]
  rw [he]
  have hpos : 0 < |π0 ω - ib| := abs_pos.mpr (sub_ne_zero.mpr hω)
  refine Tendsto.atTop_mul_const hpos ?_
  exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp (tendsto_add_atTop_nat 1)

/-- Cochrane (2023), p. 398: under a peg the adaptive solution is bounded iff inflation starts at
the peg, `π_{−1} = ī`. -/
theorem adaptive_peg_bounded_iff {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ}
    {π : ℕ → Ω → ℝ} (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (ω : Ω) :
    (∃ M, ∀ t, |π t ω| ≤ M) ↔ π0 ω = ib := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra hne
    obtain ⟨t, ht⟩ := ((adaptive_peg_unbounded hσκ h hne).eventually_gt_atTop
      (M + |ib|)).exists
    have := abs_sub (π t ω) ib
    linarith [hM t]
  · intro he
    exact ⟨|ib|, fun t => by rw [adaptive_peg h t ω, he, sub_self, mul_zero, add_zero]⟩

/-- Cochrane (2023), p. 398: `i = π` is a steady state of the adaptive model. -/
theorem adaptive_steady_state (σ κ c : ℝ) :
    AdaptiveEq σ κ (fun (_ : Ω) => c) (fun _ _ => c) (fun _ _ => c) := by
  intro t ω
  cases t <;> simp only [lagged] <;> ring

/-! ### Rational expectations (17.7) -/

/-- Cochrane (2023), eqs. (17.5) and (17.7), p. 398: the rational-expectations equilibrium
condition `π_t = −σκ i_t + (1 + σκ) E_t π_{t+1}`, with `π` adapted. -/
def REModel (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * 𝔼.E t (π (t + 1)) ω

/-- Cochrane (2023), p. 398: the rational-expectations model is (17.3)–(17.4) with
`πᵉ_t = E_t π_{t+1}`. -/
theorem reModel_iff_static (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i π : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ i π ↔
      𝔼.Adapted π ∧ ∃ x, StaticModel σ κ i (fun t => 𝔼.E t (π (t + 1))) x π := by
  rw [exists_static_iff_17_5]; rfl

/-- Cochrane (2023), eq. (17.7), p. 398:
`E_t π_{t+1} = π_t/(1 + σκ) + σκ/(1 + σκ) · i_t`. -/
theorem reModel_iff_17_7 (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    (i π : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ i π ↔ 𝔼.Adapted π ∧ ∀ t ω,
      𝔼.E t (π (t + 1)) ω = 1 / (1 + σ * κ) * π t ω + σ * κ / (1 + σ * κ) * i t ω := by
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun ω => ?_)
  constructor
  · intro e; rw [e]; field_simp; ring
  · intro e; rw [e]; field_simp; ring

/-- Cochrane (2023), p. 398: (17.7) rearranged, `E_t π_{t+1} − π_t = σκ (i_t − E_t π_{t+1})`:
a higher real rate raises subsequent expected inflation. -/
theorem re_change {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} {i π : ℕ → Ω → ℝ}
    (h : REModel 𝔼 σ κ i π) (t : ℕ) (ω : Ω) :
    𝔼.E t (π (t + 1)) ω - π t ω = σ * κ * (i t ω - 𝔼.E t (π (t + 1)) ω) := by
  rw [h.2 t ω]; ring

/-- Cochrane (2023), p. 398: with rational expectations a nominal rate above expected inflation
(a high real rate) raises expected inflation above current inflation. -/
theorem re_mechanism {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} (hσκ : 0 < σ * κ) {i π : ℕ → Ω → ℝ}
    (h : REModel 𝔼 σ κ i π) {t : ℕ} {ω : Ω} (hi : 𝔼.E t (π (t + 1)) ω < i t ω) :
    π t ω < 𝔼.E t (π (t + 1)) ω := by
  have := re_change h t ω
  nlinarith

/-- Cochrane (2023), p. 398, "The coefficient `1/(1 + σκ) < 1`": the coefficient of (17.7) lies
in `(0, 1)`, and the two coefficients sum to one. -/
theorem coeff_17_7 {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    0 < 1 / (1 + σ * κ) ∧ 1 / (1 + σ * κ) < 1 ∧ 0 < σ * κ / (1 + σ * κ) ∧
      1 / (1 + σ * κ) + σ * κ / (1 + σ * κ) = 1 := by
  have h1 : 0 < 1 + σ * κ := by linarith
  refine ⟨by positivity, by rw [div_lt_one h1]; linarith, by positivity, ?_⟩
  field_simp

/-- Cochrane (2023), p. 398: `i = π` is a steady state of the rational-expectations model. -/
theorem re_steady_state (𝔼 : ExpectationSystem Ω) (σ κ c : ℝ) :
    REModel 𝔼 σ κ (fun _ _ => c) (fun _ _ => c) := by
  refine ⟨fun t => 𝔼.const t c, fun t ω => ?_⟩
  rw [show (fun (_ : Ω) => c) = (fun _ => c) from rfl, 𝔼.const]; ring

/-- Cochrane (2023), eqs. (17.7)–(17.8), pp. 398–400: the backward recursion
`π_{t+1} = π_t/(1+σκ) + σκ/(1+σκ) · i_t + δ_{t+1}` from `π_0`, driven by expectational errors
`δ`. -/
noncomputable def reFamily (σ κ : ℝ) (π0 : Ω → ℝ) (i δ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => (1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t + (σ * κ / (1 + σ * κ)) • i t + δ (t + 1)

/-- Cochrane (2023), p. 400: the recursion defining `reFamily`. -/
theorem reFamily_succ (σ κ : ℝ) (π0 : Ω → ℝ) (i δ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    reFamily σ κ π0 i δ (t + 1) ω = 1 / (1 + σ * κ) * reFamily σ κ π0 i δ t ω +
      σ * κ / (1 + σ * κ) * i t ω + δ (t + 1) ω := rfl

/-- Cochrane (2023), p. 400: the family is adapted when `π_0`, `i` and `δ` are. -/
theorem reFamily_adapted (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) {π0 : Ω → ℝ} {i δ : ℕ → Ω → ℝ}
    (hπ0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i) (hδ : 𝔼.Adapted δ) :
    𝔼.Adapted (reFamily σ κ π0 i δ) := by
  intro t
  induction t with
  | zero => exact hπ0
  | succ t ih =>
    change 𝔼.E (t + 1) ((1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t +
      (σ * κ / (1 + σ * κ)) • i t + δ (t + 1)) = _
    rw [map_add, map_add, map_smul, map_smul, ← ih, ← hi t, 𝔼.known (Nat.le_succ t),
      𝔼.known (Nat.le_succ t), hδ (t + 1), ih, hi t]
    rfl

/-- Cochrane (2023), p. 398, "any value of unexpected inflation `ΔE_{t+1}π_{t+1}` is possible":
for every `π_0` known at date 0 and every adapted martingale-difference process `δ`, the
family is an equilibrium of (17.7) whose expectational errors are exactly `δ`. -/
theorem reFamily_solves (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    {π0 : Ω → ℝ} {i δ : ℕ → Ω → ℝ} (hπ0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i)
    (hδ : 𝔼.Adapted δ) (hmd : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    REModel 𝔼 σ κ i (reFamily σ κ π0 i δ) ∧ ∀ t ω,
      reFamily σ κ π0 i δ (t + 1) ω - 𝔼.E t (reFamily σ κ π0 i δ (t + 1)) ω = δ (t + 1) ω := by
  have had := reFamily_adapted 𝔼 σ κ hπ0 hi hδ
  have hE : ∀ t, 𝔼.E t (reFamily σ κ π0 i δ (t + 1)) =
      (1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t + (σ * κ / (1 + σ * κ)) • i t := by
    intro t
    change 𝔼.E t ((1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t +
      (σ * κ / (1 + σ * κ)) • i t + δ (t + 1)) = _
    rw [map_add, map_add, map_smul, map_smul, had t, hi t, hmd t, add_zero]
  refine ⟨⟨had, fun t ω => ?_⟩, fun t ω => ?_⟩
  · rw [hE t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hE t, reFamily_succ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), p. 400: the expectational errors `δ_{t+1} = π_{t+1} − E_t π_{t+1}` of a
process (set to zero at date 0). -/
def reErr (𝔼 : ExpectationSystem Ω) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => π (t + 1) - 𝔼.E t (π (t + 1))

/-- Cochrane (2023), p. 400: expectational errors of an adapted process are adapted and have
conditional mean zero. -/
theorem reErr_mds (𝔼 : ExpectationSystem Ω) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) :
    𝔼.Adapted (reErr 𝔼 π) ∧ ∀ t, 𝔼.E t (reErr 𝔼 π (t + 1)) = 0 := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => exact map_zero _
    | succ t => change 𝔼.E (t + 1) (π (t + 1) - 𝔼.E t (π (t + 1))) = _
                rw [map_sub, hπ (t + 1), 𝔼.known (Nat.le_succ t)]; rfl
  · change 𝔼.E t (π (t + 1) - 𝔼.E t (π (t + 1))) = 0
    rw [map_sub, 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), eqs. (17.7)–(17.8), p. 400: every equilibrium of (17.7) is a member of the
family, driven by its own expectational errors. -/
theorem eq_reFamily {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} (h : 1 + σ * κ ≠ 0) {i π : ℕ → Ω → ℝ}
    (hπ : REModel 𝔼 σ κ i π) : π = reFamily σ κ (π 0) i (reErr 𝔼 π) := by
  have h17 := ((reModel_iff_17_7 𝔼 h i π).mp hπ).2
  funext t ω
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [reFamily_succ, ← ih]
    change π (t + 1) ω = _ + (π (t + 1) ω - 𝔼.E t (π (t + 1)) ω)
    rw [h17 t ω]; ring

/-- Cochrane (2023), p. 400: with bounded `π_0`, `i` and `δ` and `σκ > 0`, the family is
bounded (the recursion is stable). -/
theorem reFamily_bounded {σ κ B Mi Mδ : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {i δ : ℕ → Ω → ℝ}
    (hπ0 : ∀ ω, |π0 ω| ≤ B) (hi : ∀ t ω, |i t ω| ≤ Mi) (hδ : ∀ t ω, |δ t ω| ≤ Mδ) :
    BoundedProc (reFamily σ κ π0 i δ) := by
  obtain ⟨ha0, ha1, hb0, hab⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  have hb1 : b < 1 := by linarith
  set K := |B| + (|Mi| + |Mδ|) / (1 - a) with hK
  have h1a : 0 < 1 - a := by linarith
  have hKa : (1 - a) * K = (1 - a) * |B| + (|Mi| + |Mδ|) := by
    rw [hK]; field_simp
  refine ⟨K, fun t ω => ?_⟩
  induction t generalizing ω with
  | zero => exact (hπ0 ω).trans ((le_abs_self B).trans (by
      have : 0 ≤ (|Mi| + |Mδ|) / (1 - a) := by positivity
      linarith))
  | succ t ih =>
    rw [reFamily_succ]
    have e1 : |a * reFamily σ κ π0 i δ t ω| ≤ a * K := by
      rw [abs_mul, abs_of_pos ha0]; exact mul_le_mul_of_nonneg_left (ih ω) ha0.le
    have e2 : |b * i t ω| ≤ |Mi| := by
      rw [abs_mul, abs_of_pos hb0]
      calc b * |i t ω| ≤ 1 * |i t ω| := mul_le_mul_of_nonneg_right hb1.le (abs_nonneg _)
        _ ≤ |Mi| := by rw [one_mul]; exact (hi t ω).trans (le_abs_self _)
    have e3 : |δ (t + 1) ω| ≤ |Mδ| := (hδ (t + 1) ω).trans (le_abs_self _)
    have hB : 0 ≤ (1 - a) * |B| := mul_nonneg h1a.le (abs_nonneg _)
    calc |a * reFamily σ κ π0 i δ t ω + b * i t ω + δ (t + 1) ω|
        ≤ |a * reFamily σ κ π0 i δ t ω| + |b * i t ω| + |δ (t + 1) ω| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ a * K + |Mi| + |Mδ| := by linarith
      _ ≤ K := by linarith

/-- Cochrane (2023), p. 398, "Inflation is stable but indeterminate": for every bounded adapted
interest-rate path and every initial inflation `c`, there is a bounded equilibrium of (17.7)
with `π_0 = c`. -/
theorem re_indeterminate (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (hσκ : 0 < σ * κ)
    {i : ℕ → Ω → ℝ} (hib : BoundedProc i) (hi : 𝔼.Adapted i) (c : ℝ) :
    ∃ π, REModel 𝔼 σ κ i π ∧ BoundedProc π ∧ π 0 = fun _ => c := by
  obtain ⟨Mi, hMi⟩ := hib
  refine ⟨reFamily σ κ (fun _ => c) i 0,
    (reFamily_solves 𝔼 (by linarith) (𝔼.const 0 c) hi (fun t => map_zero _)
      (fun t => map_zero _)).1,
    reFamily_bounded hσκ (B := |c|) (fun _ => le_rfl) hMi (Mδ := 0) (fun _ _ => by simp), rfl⟩

/-- Cochrane (2023), p. 398: (17.7) never has a unique bounded equilibrium. -/
theorem re_not_unique (𝔼 : ExpectationSystem Ω) [Nonempty Ω] {σ κ : ℝ} (hσκ : 0 < σ * κ)
    {i : ℕ → Ω → ℝ} (hib : BoundedProc i) (hi : 𝔼.Adapted i) :
    ¬ ∃! π, REModel 𝔼 σ κ i π ∧ BoundedProc π := by
  rintro ⟨π, -, hu⟩
  obtain ⟨p0, h0, hb0, he0⟩ := re_indeterminate 𝔼 hσκ hib hi 0
  obtain ⟨p1, h1, hb1, he1⟩ := re_indeterminate 𝔼 hσκ hib hi 1
  have e := (hu p0 ⟨h0, hb0⟩).trans (hu p1 ⟨h1, hb1⟩).symm
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun e 0) ω
  rw [he0, he1] at this
  norm_num at this

/-- Cochrane (2023), eq. (17.8), p. 400 (finite-start form): with initial value `π_0`,
`π_{t+1} = aᵗ⁺¹ π_0 + b ∑_{j ≤ t} aʲ i_{t−j} + ∑_{j ≤ t} aʲ δ_{t+1−j}`, where `a = 1/(1+σκ)`
and `b = σκ/(1+σκ)`. -/
theorem reFamily_closed (σ κ : ℝ) (π0 : Ω → ℝ) (i δ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    reFamily σ κ π0 i δ (t + 1) ω = (1 / (1 + σ * κ)) ^ (t + 1) * π0 ω +
      σ * κ / (1 + σ * κ) * ∑ j ∈ Finset.range (t + 1), (1 / (1 + σ * κ)) ^ j * i (t - j) ω +
      ∑ j ∈ Finset.range (t + 1), (1 / (1 + σ * κ)) ^ j * δ (t + 1 - j) ω := by
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  induction t with
  | zero =>
    rw [reFamily_succ]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one,
      Nat.sub_zero]
    rfl
  | succ t ih =>
    rw [reFamily_succ, ih, Finset.sum_range_succ' (fun j => a ^ j * i (t + 1 - j) ω),
      Finset.sum_range_succ' (fun j => a ^ j * δ (t + 1 + 1 - j) ω)]
    simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, one_mul, pow_succ,
      Finset.mul_sum]
    have e1 : ∀ j, a ^ j * a * i (t - j) ω = a * (a ^ j * i (t - j) ω) := fun j => by ring
    have e2 : ∀ j, a ^ j * a * δ (t + 1 - j) ω = a * (a ^ j * δ (t + 1 - j) ω) := fun j => by
      ring
    simp only [e1, e2, ← Finset.mul_sum]
    ring

/-! ### (17.8) with an infinite past -/

/-- Cochrane (2023), eq. (17.8), p. 400: with an infinite past, every bounded path satisfying
`π_{t+1} = π_t/(1+σκ) + σκ/(1+σκ) · i_t + δ_{t+1}` for bounded `i`, `δ` is
`π_{t+1} = σκ/(1+σκ) ∑ (1+σκ)^{−j} i_{t−j} + ∑ (1+σκ)^{−j} δ_{t+1−j}`. The statement is
pathwise (one history `ω` at a time); `δ` is the expectational error `π_{t+1} − E_t π_{t+1}`. -/
theorem eq_17_8 {σ κ Mπ Mi Mδ : ℝ} (hσκ : 0 < σ * κ) {π i δ : ℤ → ℝ}
    (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi) (hδ : ∀ s, |δ s| ≤ Mδ)
    (h : ∀ s, π (s + 1) = 1 / (1 + σ * κ) * π s + σ * κ / (1 + σ * κ) * i s + δ (s + 1))
    (t : ℤ) :
    π (t + 1) = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) +
      ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * δ (t + 1 - j) := by
  obtain ⟨ha0, ha1, hb0, -⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  have haa : |a| < 1 := by rw [abs_of_pos ha0]; exact ha1
  set w : ℤ → ℝ := fun s => b * i (s - 1) + δ s with hw
  have hwb : ∀ s, |w s| ≤ b * |Mi| + |Mδ| := fun s => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ((hδ s).trans (le_abs_self _)))
    rw [abs_mul, abs_of_pos hb0]
    exact mul_le_mul_of_nonneg_left ((hi _).trans (le_abs_self _)) hb0.le
  have hrec : ∀ s, π (s + 1) = a * π s + w (s + 1) := fun s => by
    rw [h s, hw]; simp only [add_sub_cancel_right]; ring
  rw [eq_backward_series haa hπ hwb hrec (t + 1)]
  have hg := summable_geometric_of_lt_one (abs_nonneg a) haa
  have hsi : Summable fun j : ℕ => a ^ j * i (t - j) :=
    Summable.of_norm_bounded (hg.mul_right Mi) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg (abs_nonneg a) j)
  have hsd : Summable fun j : ℕ => a ^ j * δ (t + 1 - j) :=
    Summable.of_norm_bounded (hg.mul_right Mδ) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hδ _) (pow_nonneg (abs_nonneg a) j)
  rw [← tsum_mul_left, ← (hsi.mul_left b).tsum_add hsd]
  refine tsum_congr fun j => ?_
  rw [hw]
  simp only [show t + 1 - (j : ℤ) - 1 = t - j by ring]
  ring

/-! ### Figures 17.1 and 17.2 -/

/-- Cochrane (2023), Figure 17.1, p. 399: in the adaptive model, a permanent rise of the rate
from 0 to 1 at date 0 (with `π_{−1} = 0`) gives `π_t = 1 − (1 + σκ)^{t+1}`. -/
theorem fig17_1_path {σ κ : ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ (fun _ => 0) (fun _ _ => 1) π) (t : ℕ) (ω : Ω) :
    π t ω = 1 - (1 + σ * κ) ^ (t + 1) := by
  rw [adaptive_peg h t ω]; ring

/-- Cochrane (2023), Figure 17.1 and p. 399, "inflation spirals downward": after the permanent
rate rise inflation tends to `−∞`. -/
theorem fig17_1_tendsto {σ κ : ℝ} (hσκ : 0 < σ * κ) {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ (fun _ => 0) (fun _ _ => 1) π) (ω : Ω) :
    Tendsto (fun t => π t ω) atTop atBot := by
  have he : (fun t => π t ω) = fun t => 1 - (1 + σ * κ) ^ (t + 1) := funext fun t =>
    fig17_1_path h t ω
  rw [he]
  have := (tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < 1 + σ * κ)).comp
    (tendsto_add_atTop_nat 1)
  exact tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp this)

/-- Cochrane (2023), Figure 17.1 ("less sticky"): with a larger `κ` inflation falls faster,
at every date. -/
theorem fig17_1_less_sticky {σ κ₁ κ₂ : ℝ} (hσ : 0 < σ) (hκ₁ : 0 < κ₁) (hκ : κ₁ < κ₂) (t : ℕ) :
    1 - (1 + σ * κ₂) ^ (t + 1) < 1 - (1 + σ * κ₁) ^ (t + 1) := by
  have : (1 + σ * κ₁) ^ (t + 1) < (1 + σ * κ₂) ^ (t + 1) :=
    pow_lt_pow_left₀ (by nlinarith) (by nlinarith) (Nat.succ_ne_zero t)
  linarith

/-- Cochrane (2023), Figure 17.2, p. 400: the `δ = 0` response to a permanent rise of the rate
from 0 to 1 at date 0, `π_t = 1 − (1 + σκ)^{−t}`, is an equilibrium of (17.7) (deterministic,
hence adapted under any expectation system), starting at `π_0 = 0`. -/
theorem fig17_2_solves (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0) :
    REModel 𝔼 σ κ (fun _ _ => 1) (fun t _ => 1 - (1 / (1 + σ * κ)) ^ t) := by
  refine ⟨fun t => 𝔼.const t _, fun t ω => ?_⟩
  rw [𝔼.const]
  simp only [pow_succ]
  field_simp
  ring

/-- Cochrane (2023), Figure 17.2, p. 400, "the interest-rate rise eventually brings inflation up
to meet it": the `δ = 0` response rises strictly. -/
theorem fig17_2_strictMono {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    StrictMono fun t : ℕ => 1 - (1 / (1 + σ * κ)) ^ t := by
  obtain ⟨ha0, ha1, -, -⟩ := coeff_17_7 hσκ
  intro m n hmn
  have := pow_lt_pow_right_of_lt_one₀ ha0 ha1 hmn
  simp only
  linarith

/-- Cochrane (2023), Figure 17.2, p. 400: the `δ = 0` response converges to the new rate 1. -/
theorem fig17_2_tendsto {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    Tendsto (fun t : ℕ => 1 - (1 / (1 + σ * κ)) ^ t) atTop (𝓝 1) := by
  obtain ⟨ha0, ha1, -, -⟩ := coeff_17_7 hσκ
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_sub (1 : ℝ)

/-- Cochrane (2023), Figure 17.2, p. 400, "less sticky": with a larger `κ` the response is
higher at every date `t ≥ 1` (the dynamics happen faster). -/
theorem fig17_2_less_sticky {σ κ₁ κ₂ : ℝ} (hσ : 0 < σ) (hκ₁ : 0 < κ₁) (hκ : κ₁ < κ₂) {t : ℕ}
    (ht : t ≠ 0) :
    1 - (1 / (1 + σ * κ₁)) ^ t < 1 - (1 / (1 + σ * κ₂)) ^ t := by
  have h1 : 0 < 1 + σ * κ₁ := by nlinarith
  have hlt : 1 / (1 + σ * κ₂) < 1 / (1 + σ * κ₁) :=
    one_div_lt_one_div_of_lt h1 (by nlinarith)
  have := pow_lt_pow_left₀ hlt (one_div_pos.mpr (by nlinarith)).le ht
  linarith

/-- Cochrane (2023), p. 400, "The model smoothly approaches the frictionless result, in which
`π_1 = 1` and stays there": as `κ → ∞` the response at every date `t ≥ 1` tends to 1. -/
theorem fig17_2_frictionless_limit {σ : ℝ} (hσ : 0 < σ) {t : ℕ} (ht : t ≠ 0) :
    Tendsto (fun κ : ℝ => 1 - (1 / (1 + σ * κ)) ^ t) atTop (𝓝 1) := by
  have h1 : Tendsto (fun κ : ℝ => 1 + σ * κ) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (Tendsto.const_mul_atTop hσ tendsto_id)
  have h2 : Tendsto (fun κ : ℝ => 1 / (1 + σ * κ)) atTop (𝓝 0) := by
    exact h1.inv_tendsto_atTop.congr fun κ => by simp [one_div]
  have h3 := (h2.pow t).const_sub (1 : ℝ)
  rwa [zero_pow ht, sub_zero] at h3

/-- Cochrane (2023), Figure 17.2, p. 400 (dashed lines): after the date-1 jump, every value
`π_1 = c` gives a path `π_{t+1} = 1 + (c − 1)(1+σκ)^{−t}` obeying the perfect-foresight
recursion of (17.7) from date 1 on, and every such path converges to 1. -/
theorem fig17_2_dashed {σ κ : ℝ} (hσκ : 0 < σ * κ) (c : ℝ) :
    (∀ t : ℕ, 1 + (c - 1) * (1 / (1 + σ * κ)) ^ (t + 1) =
      1 / (1 + σ * κ) * (1 + (c - 1) * (1 / (1 + σ * κ)) ^ t) + σ * κ / (1 + σ * κ) * 1) ∧
      Tendsto (fun t : ℕ => 1 + (c - 1) * (1 / (1 + σ * κ)) ^ t) atTop (𝓝 1) := by
  obtain ⟨ha0, ha1, -, -⟩ := coeff_17_7 hσκ
  refine ⟨fun t => ?_, ?_⟩
  · have : 1 + σ * κ ≠ 0 := by linarith
    rw [pow_succ]; field_simp; ring
  · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_mul (c - 1)).const_add
      (1 : ℝ)

/-- Cochrane (2023), p. 402 (the frictionless limit of (17.7)): as `κ → ∞` the coefficients
`1/(1+σκ)` and `σκ/(1+σκ)` of (17.7) tend to 0 and 1, giving the frictionless Fisher
relation `E_t π_{t+1} = i_t`. -/
theorem tendsto_coeff_17_7 {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ : ℝ => 1 / (1 + σ * κ)) atTop (𝓝 0) ∧
      Tendsto (fun κ : ℝ => σ * κ / (1 + σ * κ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun κ : ℝ => 1 + σ * κ) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (Tendsto.const_mul_atTop hσ tendsto_id)
  have h2 : Tendsto (fun κ : ℝ => 1 / (1 + σ * κ)) atTop (𝓝 0) := by
    exact h1.inv_tendsto_atTop.congr fun κ => by simp [one_div]
  refine ⟨h2, ?_⟩
  have h3 := h2.const_sub (1 : ℝ)
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have : 1 + σ * κ ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### Expected rises and fiscal selection (p. 401) -/

/-- Cochrane (2023), p. 401, "The response to an expected interest-rate rise is the same, only
that there can be no jump at time 1": if everything is known at the announcement date 0, all
later expectational errors are zero. -/
theorem no_surprise_of_known (𝔼 : ExpectationSystem Ω) {π : ℕ → Ω → ℝ}
    (hk : ∀ t, 𝔼.E 0 (π t) = π t) (t : ℕ) : π (t + 1) - 𝔼.E t (π (t + 1)) = 0 := by
  rw [← hk (t + 1), 𝔼.known (Nat.zero_le t), sub_self]

/-- Cochrane (2023), p. 401: in an equilibrium of (17.7) in which everything is known at the
announcement date 0, the path is pinned down by `π_0` (the only possible jump comes on the
announcement date). -/
theorem eq_reFamily_of_known {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    {i π : ℕ → Ω → ℝ} (hπ : REModel 𝔼 σ κ i π) (hk : ∀ t, 𝔼.E 0 (π t) = π t) :
    π = reFamily σ κ (π 0) i 0 := by
  have he : reErr 𝔼 π = 0 := by
    funext t ω
    cases t with
    | zero => rfl
    | succ t => exact congrFun (no_surprise_of_known 𝔼 hk t) ω
  rw [← he]
  exact eq_reFamily h hπ

/-- Cochrane (2023), p. 401, "Active fiscal policy likewise selects one equilibrium": if fiscal
policy fixes unexpected inflation `ΔE_{t+1} π_{t+1} = −ε_{t+1}` (a fiscal shock `ε`, adapted with
mean zero) and inflation at date 0, the equilibrium of (17.7) is unique. -/
theorem fiscal_selects (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    {π0 : Ω → ℝ} {i ε : ℕ → Ω → ℝ} (hπ0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i)
    (hε : 𝔼.Adapted ε) (hmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    ∃! π, REModel 𝔼 σ κ i π ∧ π 0 = π0 ∧ ∀ t, π (t + 1) - 𝔼.E t (π (t + 1)) = -ε (t + 1) := by
  have hnε : 𝔼.Adapted (-ε) := fun t => by rw [Pi.neg_apply, map_neg, hε t]
  have hmd' : ∀ t, 𝔼.E t ((-ε) (t + 1)) = 0 := fun t => by
    rw [Pi.neg_apply, map_neg, hmd t, neg_zero]
  obtain ⟨hs, herr⟩ := reFamily_solves 𝔼 h hπ0 hi hnε hmd'
  refine ⟨reFamily σ κ π0 i (-ε), ⟨hs, rfl, fun t => funext fun ω => herr t ω⟩, ?_⟩
  rintro π ⟨hπ, h0, hd⟩
  have h17 := ((reModel_iff_17_7 𝔼 h i π).mp hπ).2
  funext t ω
  induction t with
  | zero => rw [h0]; rfl
  | succ t ih =>
    rw [reFamily_succ, ← ih]
    have := congrFun (hd t) ω
    simp only [Pi.sub_apply, Pi.neg_apply] at this
    rw [h17 t ω] at this
    simp only [Pi.neg_apply]
    linarith

end Cochrane.KeynesianStickyPrices.StaticIS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Policy rules under adaptive and rational expectations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.2 (p. 401) and §17.3
"Rational expectations responses with policy rules", pp. 401–403.

Adding the rule `i_t = φ π_t + u_{i,t}` to the static model gives (17.9)
`π_t = (1+σκ)/(1+σκφ) πᵉ_t − σκ/(1+σκφ) u_{i,t}`.

* Adaptive expectations (17.10): the solution is always unique given `π_{−1}`
  (`adaptiveRule_existsUnique`); it is stable iff `|1 + σκ| < |1 + σκφ|`, i.e. iff
  `φ > 1` or `φ < −1 − 2/(σκ)` (`adaptiveStable_iff`). Survey error **E7** (confirmed): the book's
  "the Taylor rule `|φ| > 1` stabilizes" is false for `−1 − 2/(σκ) ≤ φ < −1`
  (`printed_abs_phi_gt_one_stabilizes_false`: `σκ = 1/2`, `φ = −3/2` gives coefficient 6); the
  book's "`|φ| < 1` produces unstable inflation" is true (`passive_unstable`).
* Rational expectations (17.11): the model has exactly one bounded equilibrium for every bounded
  disturbance iff `φ > 1` or `φ < −1 − 2/(σκ)` (`reDeterminate_iff`). **E7** again: "passive
  policy `φ < 1` produces … indeterminate inflation" fails for `φ < −1 − 2/(σκ)`
  (`printed_passive_indeterminate_false`, `φ = −6`, `σκ = 1/2`); the coefficient of (17.11) has
  modulus below one iff `−1 − 2/(σκ) < φ < 1` (`re_coeff_abs_lt_one_iff`).
* The forward solution of p. 403 (`forward_solution`), the frictionless limit `κ → ∞` of
  (17.11), which is (16.4) (`tendsto_coeff_17_11`).
* p. 401: with `i_t = i*_t + φ(π_t − π*_t)` and `φ > 1` the central bank selects any
  equilibrium `π*` of the peg model, i.e. any value of unexpected inflation
  (`rule_selects`, `rule_selects_any_delta`).
-/

namespace Cochrane.KeynesianStickyPrices.RulesAdaptiveRE

open Filter Topology StaticIS ForwardSolution

variable {Ω : Type*}

/-! ### The key inequality -/

/-- Cochrane (2023), p. 402 (survey error E7): for `s = σκ > 0`,
`|1 + s| < |1 + sφ|` iff `φ > 1` or `φ < −1 − 2/s`. -/
theorem abs_lt_abs_iff {s φ : ℝ} (hs : 0 < s) :
    |1 + s| < |1 + s * φ| ↔ 1 < φ ∨ φ < -1 - 2 / s := by
  rw [← sq_lt_sq, ← sub_pos]
  have e : (1 + s * φ) ^ 2 - (1 + s) ^ 2 = s * ((φ - 1) * (s * φ + s + 2)) := by ring
  rw [e, mul_pos_iff_of_pos_left hs, mul_pos_iff]
  have e2 : φ < -1 - 2 / s ↔ s * φ + s + 2 < 0 := by
    have : -1 - 2 / s = (-s - 2) / s := by field_simp
    rw [this, lt_div_iff₀ hs]
    constructor <;> intro h <;> linarith
  rw [e2]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr h2
  · rintro (h1 | h2)
    · exact Or.inl ⟨by linarith, by nlinarith⟩
    · refine Or.inr ⟨?_, h2⟩
      nlinarith

/-- Cochrane (2023), p. 402 (survey error E7): for `σκ > 0` and `1 + σκφ ≠ 0`, the coefficient
`(1+σκ)/(1+σκφ)` of (17.10) has modulus below one iff `φ > 1` or `φ < −1 − 2/(σκ)`. -/
theorem abs_coeff_lt_one_iff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (h : 1 + σ * κ * φ ≠ 0) :
    |(1 + σ * κ) / (1 + σ * κ * φ)| < 1 ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [abs_div, div_lt_one (abs_pos.mpr h)]
  exact abs_lt_abs_iff hσκ

/-! ### (17.9) and adaptive expectations (17.10) -/

/-- Cochrane (2023), eq. (17.9), p. 402: with the rule `i_t = φ π_t + u_t`, (17.5) is
`π_t = (1+σκ)/(1+σκφ) πᵉ_t − σκ/(1+σκφ) u_t`. -/
theorem eq_17_9 {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) (πe π u : ℕ → Ω → ℝ) :
    (∀ t ω, π t ω = -(σ * κ) * (φ * π t ω + u t ω) + (1 + σ * κ) * πe t ω) ↔
      ∀ t ω, π t ω = (1 + σ * κ) / (1 + σ * κ * φ) * πe t ω -
        σ * κ / (1 + σ * κ * φ) * u t ω := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor
  · intro e; field_simp; linear_combination e
  · intro e; field_simp at e; linear_combination e

/-- Cochrane (2023), eq. (17.10), p. 402: the adaptive model (17.6) with the rule
`i_t = φ π_t + u_t`. -/
def AdaptiveRule (σ κ φ : ℝ) (π0 : Ω → ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  AdaptiveEq σ κ π0 (fun t ω => φ * π t ω + u t ω) π

/-- Cochrane (2023), eq. (17.10), p. 402:
`π_t = (1+σκ)/(1+σκφ) π_{t−1} − σκ/(1+σκφ) u_t`. -/
theorem adaptiveRule_iff_17_10 {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) (π0 : Ω → ℝ)
    (u π : ℕ → Ω → ℝ) :
    AdaptiveRule σ κ φ π0 u π ↔ ∀ t ω, π t ω = (1 + σ * κ) / (1 + σ * κ * φ) *
      lagged π0 π t ω - σ * κ / (1 + σ * κ * φ) * u t ω := by
  rw [← eq_17_9 h]
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro e <;> linear_combination e

/-- Cochrane (2023), eq. (17.10), p. 402: the solution of (17.10) built from `π_{−1}`. -/
noncomputable def adaptiveRulePath (σ κ φ : ℝ) (π0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => (1 + σ * κ) / (1 + σ * κ * φ) * π0 ω - σ * κ / (1 + σ * κ * φ) * u 0 ω
  | t + 1 => fun ω => (1 + σ * κ) / (1 + σ * κ * φ) * adaptiveRulePath σ κ φ π0 u t ω -
      σ * κ / (1 + σ * κ * φ) * u (t + 1) ω

/-- Cochrane (2023), p. 402, "there is only one equilibrium": given `π_{−1}`, (17.10) has
exactly one solution for every rule with `1 + σκφ ≠ 0`. -/
theorem adaptiveRule_existsUnique {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) (π0 : Ω → ℝ)
    (u : ℕ → Ω → ℝ) : ∃! π, AdaptiveRule σ κ φ π0 u π := by
  refine ⟨adaptiveRulePath σ κ φ π0 u, (adaptiveRule_iff_17_10 h π0 u _).mpr fun t ω => ?_,
    fun π hπ => ?_⟩
  · cases t <;> rfl
  · have e := (adaptiveRule_iff_17_10 h π0 u π).mp hπ
    funext t ω
    induction t with
    | zero => rw [e 0 ω]; rfl
    | succ t ih => rw [e (t + 1) ω]; simp only [lagged]; rw [ih]; rfl

/-- Cochrane (2023), eq. (17.10), p. 402: with no disturbance, `π_t = cᵗ⁺¹ π_{−1}` with
`c = (1+σκ)/(1+σκφ)`. -/
theorem adaptiveRule_homog {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 0 π) (t : ℕ) (ω : Ω) :
    π t ω = ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1) * π0 ω := by
  have e := (adaptiveRule_iff_17_10 h π0 0 π).mp hπ
  induction t with
  | zero => rw [e 0 ω]; simp [lagged]
  | succ t ih => rw [e (t + 1) ω]; simp only [lagged]; rw [ih]; simp; ring

/-- Cochrane (2023), p. 402: stability of the adaptive model with a rule — after any initial
condition, inflation returns to zero when there are no further disturbances ("Any shocks …
eventually die out"). -/
def AdaptiveStable (Ω : Type*) (σ κ φ : ℝ) : Prop :=
  ∀ (π0 : Ω → ℝ) (π : ℕ → Ω → ℝ), AdaptiveRule σ κ φ π0 0 π →
    ∀ ω, Tendsto (fun t => π t ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 402 (survey error E7, corrected): the adaptive model with the rule
`i = φπ + u` is stable iff `φ > 1` or `φ < −1 − 2/(σκ)`. -/
theorem adaptiveStable_iff [Nonempty Ω] {σ κ φ : ℝ} (hσκ : 0 < σ * κ)
    (h : 1 + σ * κ * φ ≠ 0) :
    AdaptiveStable Ω σ κ φ ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [← abs_coeff_lt_one_iff hσκ h]
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  constructor
  · intro hs
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    obtain ⟨π, hπ, -⟩ := adaptiveRule_existsUnique h (fun _ => (1 : ℝ)) 0
    have hl := hs _ π hπ ω
    have he : (fun t => π t ω) = fun t => c ^ (t + 1) := funext fun t => by
      rw [adaptiveRule_homog h hπ t ω, mul_one]
    rw [he] at hl
    have hl' : Tendsto (fun t => c ^ t) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mp hl
    exact tendsto_pow_atTop_nhds_zero_iff.mp hl'
  · intro hc π0 π hπ ω
    have he : (fun t => π t ω) = fun t => c ^ (t + 1) * π0 ω := funext fun t =>
      adaptiveRule_homog h hπ t ω
    rw [he]
    have h0 := (tendsto_add_atTop_iff_nat 1).mpr (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc)
    simpa using h0.mul_const (π0 ω)

/-- Cochrane (2023), p. 402, "Any 'passive' monetary policy `|φ| < 1` produces unstable …
inflation. The coefficient on lagged inflation is above one" (true, in modulus). -/
theorem passive_unstable {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (h : 1 + σ * κ * φ ≠ 0)
    (hφ : |φ| < 1) : 1 < |(1 + σ * κ) / (1 + σ * κ * φ)| := by
  rw [abs_div, one_lt_div (abs_pos.mpr h)]
  rw [abs_lt] at hφ
  rw [abs_of_pos (by linarith : 0 < 1 + σ * κ), abs_lt]
  constructor <;> nlinarith

/-- Cochrane (2023), p. 402: when the coefficient exceeds one in modulus, every undisturbed path
starting away from zero diverges, `|π_t| → ∞`. -/
theorem unstable_diverges {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0)
    (hc : 1 < |(1 + σ * κ) / (1 + σ * κ * φ)|) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 0 π) {ω : Ω} (hω : π0 ω ≠ 0) :
    Tendsto (fun t => |π t ω|) atTop atTop := by
  have he : (fun t => |π t ω|) =
      fun t => |(1 + σ * κ) / (1 + σ * κ * φ)| ^ (t + 1) * |π0 ω| := funext fun t => by
    rw [adaptiveRule_homog h hπ t ω, abs_mul, abs_pow]
  rw [he]
  exact Tendsto.atTop_mul_const (abs_pos.mpr hω)
    ((tendsto_pow_atTop_atTop_of_one_lt hc).comp (tendsto_add_atTop_nat 1))

/-- Cochrane (2023), p. 402, survey error E7: the printed claim "The Taylor rule `|φ| > 1`
stabilizes" is false. With `σ = 1`, `κ = 1/2` and `φ = −3/2` (so `|φ| > 1`) the coefficient of
(17.10) is `6`, and inflation spirals away. -/
theorem printed_abs_phi_gt_one_stabilizes_false :
    1 < |(-3 / 2 : ℝ)| ∧ (1 + 1 * (1 / 2)) / (1 + 1 * (1 / 2) * (-3 / 2)) = (6 : ℝ) ∧
      ¬ (1 < (-3 / 2 : ℝ) ∨ (-3 / 2 : ℝ) < -1 - 2 / (1 * (1 / 2))) := by
  refine ⟨by norm_num [abs_of_neg], by norm_num, by norm_num⟩

/-- Cochrane (2023), p. 402 (boundary case of E7): at `φ = −1 − 2/(σκ)` the coefficient of
(17.10) is exactly `−1`: undisturbed inflation oscillates forever, neither stable nor
explosive. -/
theorem boundary_coeff {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    (1 + σ * κ) / (1 + σ * κ * (-1 - 2 / (σ * κ))) = -1 := by
  have : σ * κ ≠ 0 := hσκ.ne'
  have hσ : σ ≠ 0 := left_ne_zero_of_mul this
  have hκ : κ ≠ 0 := right_ne_zero_of_mul this
  have h2 : 1 + σ * κ * (-1 - 2 / (σ * κ)) = -(1 + σ * κ) := by field_simp; ring
  rw [h2, div_neg, div_self (by linarith)]

/-- Cochrane (2023), p. 402: in the stable case bounded disturbances produce bounded inflation,
whatever the initial condition. -/
theorem adaptiveRule_bounded {σ κ φ B M : ℝ} (h : 1 + σ * κ * φ ≠ 0)
    (hc : |(1 + σ * κ) / (1 + σ * κ * φ)| < 1) {π0 : Ω → ℝ} {u π : ℕ → Ω → ℝ}
    (hπ0 : ∀ ω, |π0 ω| ≤ B) (hu : ∀ t ω, |u t ω| ≤ M) (hπ : AdaptiveRule σ κ φ π0 u π) :
    BoundedProc π := by
  have e := (adaptiveRule_iff_17_10 h π0 u π).mp hπ
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  set k := σ * κ / (1 + σ * κ * φ)
  set K := |B| + |k| * |M| / (1 - |c|) with hK
  have h1c : 0 < 1 - |c| := by linarith
  have hKc : (1 - |c|) * K = (1 - |c|) * |B| + |k| * |M| := by rw [hK]; field_simp
  have hB : 0 ≤ (1 - |c|) * |B| := mul_nonneg h1c.le (abs_nonneg _)
  have hstep : ∀ x : ℝ, |x| ≤ K → ∀ t ω, |c * x - k * u t ω| ≤ K := fun x hx t ω => by
    calc |c * x - k * u t ω| ≤ |c| * |x| + |k| * |u t ω| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ |c| * K + |k| * |M| :=
          add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg c))
            (mul_le_mul_of_nonneg_left ((hu t ω).trans (le_abs_self M)) (abs_nonneg k))
      _ ≤ K := by nlinarith [abs_nonneg c]
  have hK0 : |B| ≤ K := by
    have : 0 ≤ |k| * |M| / (1 - |c|) := by positivity
    linarith
  refine ⟨K, fun t ω => ?_⟩
  induction t generalizing ω with
  | zero => rw [e 0 ω]; exact hstep _ (((hπ0 ω).trans (le_abs_self B)).trans hK0) 0 ω
  | succ t ih => rw [e (t + 1) ω]; exact hstep _ (ih ω) (t + 1) ω

/-! ### Rational expectations (17.11) -/

/-- Cochrane (2023), eqs. (17.9) and (17.11), p. 402: the rational-expectations model (17.5)
with `πᵉ_t = E_t π_{t+1}` and the rule `i_t = φ π_t + u_t`. -/
def RERule (𝔼 : ExpectationSystem Ω) (σ κ φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  REModel 𝔼 σ κ (fun t ω => φ * π t ω + u t ω) π

/-- Cochrane (2023), eq. (17.11), p. 402:
`E_t π_{t+1} = (1+σκφ)/(1+σκ) π_t + σκ/(1+σκ) u_t`. -/
theorem reRule_iff_17_11 (𝔼 : ExpectationSystem Ω) {σ κ φ : ℝ} (h : 1 + σ * κ ≠ 0)
    (u π : ℕ → Ω → ℝ) :
    RERule 𝔼 σ κ φ u π ↔ 𝔼.Adapted π ∧ ∀ t ω, 𝔼.E t (π (t + 1)) ω =
      (1 + σ * κ * φ) / (1 + σ * κ) * π t ω + σ * κ / (1 + σ * κ) * u t ω := by
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun ω => ?_)
  constructor
  · intro e; simp only at e; field_simp; linear_combination -e
  · intro e; field_simp at e; simp only; linear_combination -e

/-- Cochrane (2023), eq. (17.11), p. 402, in the undivided form of the core:
`(1 + σκφ) π_t = (1 + σκ) E_t π_{t+1} − σκ u_t`. -/
theorem reRule_iff_scalar (𝔼 : ExpectationSystem Ω) (σ κ φ : ℝ) (u π : ℕ → Ω → ℝ) :
    RERule 𝔼 σ κ φ u π ↔ 𝔼.Adapted π ∧
      ScalarEq 𝔼 (1 + σ * κ * φ) (1 + σ * κ) (fun t => (-(σ * κ)) • u t) π := by
  refine and_congr Iff.rfl ⟨fun e t => funext fun ω => ?_, fun e t ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination e t ω
  · have := congrFun (e t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this

/-- Cochrane (2023), p. 402: determinacy of the rational-expectations model with a rule — for
every bounded adapted disturbance there is exactly one bounded equilibrium. -/
def REDeterminate (𝔼 : ExpectationSystem Ω) (σ κ φ : ℝ) : Prop :=
  ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∃! π, BoundedProc π ∧ RERule 𝔼 σ κ φ u π

/-- Cochrane (2023), p. 402 (survey error E7, corrected): (17.11) is determinate iff `φ > 1` or
`φ < −1 − 2/(σκ)`. -/
theorem reDeterminate_iff (𝔼 : ExpectationSystem Ω) [Nonempty Ω] {σ κ φ : ℝ}
    (hσκ : 0 < σ * κ) : REDeterminate 𝔼 σ κ φ ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [← abs_lt_abs_iff hσκ]
  constructor
  · intro hd
    by_contra hc
    push Not at hc
    have hB : 1 + σ * κ ≠ 0 := by linarith
    obtain ⟨hh, hhb⟩ := scalar_homog 𝔼 hc hB
    have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
    obtain ⟨π, -, hu⟩ := hd 0 ⟨0, fun _ _ => by simp⟩ hz
    have hf : (fun t => (-(σ * κ)) • (0 : ℕ → Ω → ℝ) t) = 0 := by funext t; simp
    have s0 : RERule 𝔼 σ κ φ 0 0 :=
      (reRule_iff_scalar 𝔼 σ κ φ 0 0).mpr ⟨hz, by rw [hf]; intro t; simp⟩
    have s1 : RERule 𝔼 σ κ φ 0 (fun t _ => ((1 + σ * κ * φ) / (1 + σ * κ)) ^ t) :=
      (reRule_iff_scalar 𝔼 σ κ φ 0 _).mpr ⟨fun t => 𝔼.const t _, by rw [hf]; exact hh⟩
    have e := (hu _ ⟨hhb, s1⟩).trans (hu 0 ⟨⟨0, fun _ _ => by simp⟩, s0⟩).symm
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun e 0) ω
    simp at this
  · intro hc u ⟨M, hM⟩ hua
    have hf : ∀ t ω, |(fun t => (-(σ * κ)) • u t) t ω| ≤ σ * κ * M := fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hσκ]
      exact mul_le_mul_of_nonneg_left (hM t ω) hσκ.le
    have hfa : 𝔼.Adapted (fun t => (-(σ * κ)) • u t) := fun t => by rw [map_smul, hua t]
    obtain ⟨hs, hb, ha, hu⟩ := scalar_existsUnique 𝔼 hc hf hfa
    exact ⟨_, ⟨hb, (reRule_iff_scalar 𝔼 σ κ φ u _).mpr ⟨ha, hs⟩⟩,
      fun π hπ => hu π ((reRule_iff_scalar 𝔼 σ κ φ u π).mp hπ.2).2 hπ.1⟩

/-- Cochrane (2023), p. 402, "The coefficient on lagged inflation in (17.11) is below one": the
coefficient `(1+σκφ)/(1+σκ)` of (17.11) has modulus below one iff `−1 − 2/(σκ) < φ < 1`. -/
theorem re_coeff_abs_lt_one_iff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    |(1 + σ * κ * φ) / (1 + σ * κ)| < 1 ↔ -1 - 2 / (σ * κ) < φ ∧ φ < 1 := by
  have h1 : 0 < 1 + σ * κ := by linarith
  rw [abs_div, abs_of_pos h1, div_lt_one h1, abs_lt]
  have e2 : -1 - 2 / (σ * κ) < φ ↔ 0 < σ * κ * φ + σ * κ + 2 := by
    have : -1 - 2 / (σ * κ) = (-(σ * κ) - 2) / (σ * κ) := by
      rw [sub_div, neg_div, div_self hσκ.ne']
    rw [this, div_lt_iff₀ hσκ]
    constructor <;> intro h <;> linarith
  rw [e2]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by nlinarith⟩

/-- Cochrane (2023), p. 402, survey error E7: the printed "passive policy `φ < 1` produces
stable, indeterminate inflation" is false for very negative `φ`. With `σ = 1`, `κ = 1/2` and
`φ = −6 < 1` the model is determinate. -/
theorem printed_passive_indeterminate_false (𝔼 : ExpectationSystem Ω) [Nonempty Ω] :
    (-6 : ℝ) < 1 ∧ REDeterminate 𝔼 1 (1 / 2) (-6) := by
  refine ⟨by norm_num, (reDeterminate_iff 𝔼 (by norm_num)).mpr (Or.inr (by norm_num))⟩

/-- Cochrane (2023), p. 402: for `−1 − 2/(σκ) ≤ φ ≤ 1` (in particular passive `0 ≤ φ ≤ 1`)
the model is indeterminate. -/
theorem passive_indeterminate (𝔼 : ExpectationSystem Ω) [Nonempty Ω] {σ κ φ : ℝ}
    (hσκ : 0 < σ * κ) (h1 : φ ≤ 1) (h2 : -1 - 2 / (σ * κ) ≤ φ) : ¬ REDeterminate 𝔼 σ κ φ := by
  rw [reDeterminate_iff 𝔼 hσκ]
  push Not
  exact ⟨h1, h2⟩

/-- Cochrane (2023), p. 403: the forward solution. When (17.11) is determinate, the unique
bounded equilibrium is
`π_t = −σκ/(1+σκφ) ∑_j ((1+σκ)/(1+σκφ))ʲ E_t u_{t+j}`. -/
theorem forward_solution (𝔼 : ExpectationSystem Ω) {σ κ φ M : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) {u π : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) (hπb : BoundedProc π) (hπ : RERule 𝔼 σ κ φ u π) (t : ℕ) (ω : Ω) :
    π t ω = -(σ * κ) / (1 + σ * κ * φ) *
      ∑' j, ((1 + σ * κ) / (1 + σ * κ * φ)) ^ j * 𝔼.E t (u (t + j)) ω := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  have hf : ∀ t ω, |(fun t => (-(σ * κ)) • u t) t ω| ≤ σ * κ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hσκ]
    exact mul_le_mul_of_nonneg_left (hu t ω) hσκ.le
  have hfa : 𝔼.Adapted (fun t => (-(σ * κ)) • u t) := fun t => by rw [map_smul, hua t]
  obtain ⟨-, -, -, huniq⟩ := scalar_existsUnique 𝔼 hc hf hfa
  rw [huniq π ((reRule_iff_scalar 𝔼 σ κ φ u π).mp hπ).2 hπb, scalarSol_apply, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, div_pow, pow_succ]
  have hA : 1 + σ * κ * φ ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith [abs_nonneg (1 + σ * κ)]
  field_simp

/-- Cochrane (2023), p. 402, "The frictionless case (16.4), `E_t π_{t+1} = φ π_t + u_{i,t}`, is
the `κ → ∞` limit": the coefficients of (17.11) tend to `φ` and `1`. -/
theorem tendsto_coeff_17_11 {σ : ℝ} (hσ : 0 < σ) (φ : ℝ) :
    Tendsto (fun κ : ℝ => (1 + σ * κ * φ) / (1 + σ * κ)) atTop (𝓝 φ) ∧
      Tendsto (fun κ : ℝ => σ * κ / (1 + σ * κ)) atTop (𝓝 1) := by
  obtain ⟨h0, h1⟩ := tendsto_coeff_17_7 hσ
  refine ⟨?_, h1⟩
  have h2 := (h0.const_mul (1 - φ)).const_add φ
  rw [mul_zero, add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have : 1 + σ * κ ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### Equilibrium selection by the rule (p. 401) -/

/-- Cochrane (2023), p. 401: with `i_t = i*_t + φ (π_t − π*_t)`, the deviation `d = π − π*` of
an equilibrium from an equilibrium `π*` of the model with `i*` obeys
`(1 + σκφ) d_t = (1 + σκ) E_t d_{t+1}`, i.e. `E_t d_{t+1} = (1+σκφ)/(1+σκ) d_t`. -/
theorem deviation_eq {𝔼 : ExpectationSystem Ω} {σ κ φ : ℝ} {istar πstar π : ℕ → Ω → ℝ}
    (hstar : REModel 𝔼 σ κ istar πstar)
    (hπ : REModel 𝔼 σ κ (fun t ω => istar t ω + φ * (π t ω - πstar t ω)) π) :
    ScalarEq 𝔼 (1 + σ * κ * φ) (1 + σ * κ) 0 (π - πstar) := by
  intro t
  funext ω
  have e1 := hstar.2 t ω
  have e2 := hπ.2 t ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply, map_sub,
    add_zero]
  linear_combination e2 - e1

/-- Cochrane (2023), p. 401: "If we rule out nominal explosions and add a policy rule
`i_t = i*_t + φ(π_t − π*_t)` with `φ > 1` … the central bank can achieve any value of
unexpected inflation": for any bounded equilibrium `π*` of the model with `i*`, it is the unique
bounded equilibrium under the rule (also for `φ < −1 − 2/(σκ)`). -/
theorem rule_selects {𝔼 : ExpectationSystem Ω} {σ κ φ : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) {istar πstar : ℕ → Ω → ℝ}
    (hstar : REModel 𝔼 σ κ istar πstar) (hb : BoundedProc πstar) :
    ∃! π, BoundedProc π ∧
      REModel 𝔼 σ κ (fun t ω => istar t ω + φ * (π t ω - πstar t ω)) π := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  refine ⟨πstar, ⟨hb, ⟨hstar.1, fun t ω => ?_⟩⟩, fun π ⟨hπb, hπ⟩ => ?_⟩
  · rw [hstar.2 t ω]; ring
  · obtain ⟨-, -, -, huniq⟩ := scalar_existsUnique 𝔼 (K := 0) hc (f := 0) (fun _ _ => by simp)
      (fun t => by simp)
    obtain ⟨M₁, hM₁⟩ := hπb
    obtain ⟨M₂, hM₂⟩ := hb
    have hd : BoundedProc (π - πstar) := ⟨M₁ + M₂, fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω))⟩
    have h0 : ScalarEq 𝔼 (1 + σ * κ * φ) (1 + σ * κ) 0 0 := fun t => by simp
    have e := (huniq _ (deviation_eq hstar hπ) hd).trans
      (huniq 0 h0 ⟨0, fun _ _ => by simp⟩).symm
    exact sub_eq_zero.mp e

/-- Cochrane (2023), p. 401: any member of the family of equilibria of the peg model
(any adapted bounded martingale-difference process `δ` of unexpected inflation, any `π_0`)
can be selected by the rule `i_t = i*_t + φ(π_t − π*_t)` with `φ > 1`. -/
theorem rule_selects_any_delta (𝔼 : ExpectationSystem Ω) {σ κ φ B Mi Mδ : ℝ}
    (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π0 : Ω → ℝ} {istar δ : ℕ → Ω → ℝ}
    (hπ0 : 𝔼.E 0 π0 = π0) (hπ0b : ∀ ω, |π0 ω| ≤ B) (hi : 𝔼.Adapted istar)
    (hib : ∀ t ω, |istar t ω| ≤ Mi) (hδ : 𝔼.Adapted δ) (hδb : ∀ t ω, |δ t ω| ≤ Mδ)
    (hmd : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    ∃! π, BoundedProc π ∧ REModel 𝔼 σ κ (fun t ω => istar t ω +
      φ * (π t ω - reFamily σ κ π0 istar δ t ω)) π := by
  exact rule_selects hσκ (Or.inl hφ) (reFamily_solves 𝔼 (by linarith) hπ0 hi hδ hmd).1
    (reFamily_bounded hσκ hπ0b hib hδb)

end Cochrane.KeynesianStickyPrices.RulesAdaptiveRE

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Responses to AR(1) monetary-policy disturbances

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.3.1 "Responses with
policy rules", pp. 403–405, §17.4.3 "Responses to AR(1) monetary policy disturbances",
pp. 415–416, and Online Appendix A1, §1.8 "Three-equation model solution", pp. 571–572, and
§1.13.1 "Calculating responses of the standard new-Keynesian model", pp. 586–588.

## The simple sticky-price model (17.11)

With an AR(1) disturbance `E_t u_{t+1} = η u_t`, `|η| ≤ 1`, and a determinate rule:

* (17.12): the unique bounded equilibrium is `π_t = −u_t/(φ − η + (1−η)/(σκ))`
  (`eq_17_12`), equal to the forward-series form (`eq_17_12_series`, `coeff_17_12_forms`);
* (17.13): `i_t = −(η − (1−η)/(σκ))/(φ − η + (1−η)/(σκ)) u_t` (`eq_17_13`,
  `coeff_17_13_forms`);
* the frictionless limits `κ → ∞` are (16.9) and (16.11) (`tendsto_17_12`, `tendsto_17_13`);
* `η = 1` is super-Fisherian, `π = i = −u/(φ−1)` (`superFisher_simple`); `η = 1/(1+σκ)` is the
  open-mouth case `π = −u/φ`, `i = 0` (`openMouth_simple`); and for `φ > 1` the interest rate
  moves with the disturbance iff `η < 1/(1+σκ)` (`i_coeff_pos_iff`, Figure 17.3: `fig17_3`).

## The three-equation model (17.15)–(17.17), (17.20)–(17.21)

* A1 (1.59): undetermined coefficients (`msv_solves`, `coeffs_of_msv`); (1.60)–(1.62)
  (`eq_1_59_iff`, `msv_i_eq`); for `φ > 1` the minimal-state-variable solution is the unique
  bounded equilibrium (`msv_unique`, via `threeEq_solves` and `schurStable_of_one_lt`).
* A1 §1.8: the lag-operator form `−σκ/((1+σκφ)(1−λ₁η)(1−λ₂η))` equals (1.60) (`lag_form`,
  `lag_factor`, `partial_fractions`, `lag_sum_ar1`). Survey error **E11** (confirmed): the book
  says "both roots unstable, `λ₁ < 1` and `λ₂ < 1`", but the roots can be complex
  (`lag_roots_complex_example`, `φ = 1.5, β = 0.99, σ = 1, κ = 0.5`); the correct statement is
  that both have modulus below one (`lag_roots_norm_lt_one`).
* p. 415: `η = 1` is super-Fisherian, `π = i = −u/(φ−1)`, `x = (1−β)/κ · π`
  (`superFisher_full`).
* p. 416: the open-mouth persistence `η*` is the unique root in `(0,1)` of
  `βη² − (1+β+σκ)η + 1 = 0` (`etaStar_root`, `etaStar_mem`, `eq_etaStar`); there
  `i = 0` and `π = −u/φ` (`openMouth_full`); for Figure 17.8 (`β = .95, κ = .5, σ = 1`)
  `0.508 < η* < 0.509` (`etaStar_fig17_8`); a negative disturbance lowers `i` and raises `π` iff
  `η < η*` (`full_i_coeff_pos_of_lt`, `full_i_coeff_neg_of_gt`, `fig17_8_transitory`).
* (1.60) generalises (17.12) (`β = 0`, `msv_beta_zero`) and (16.9) (`κ → ∞`, `tendsto_1_60`).
-/

namespace Cochrane.KeynesianStickyPrices.AR1Responses

open Filter Topology StaticIS RulesAdaptiveRE ForwardSolution
open SharedTools (Pmat Qmat solvedA det2_Pmat)

variable {Ω : Type*}

/-! ### The simple model: (17.12)–(17.13) -/

/-- Cochrane (2023), eq. (17.12), p. 403: the denominator `φ − η + (1−η)/(σκ)`. -/
noncomputable def den (σ κ φ η : ℝ) : ℝ := φ - η + (1 - η) / (σ * κ)

/-- Cochrane (2023), eq. (17.12), p. 403: `σκ (φ − η + (1−η)/(σκ)) = (1 + σκφ) − η(1 + σκ)`. -/
theorem den_mul {σ κ φ η : ℝ} (hσκ : σ * κ ≠ 0) :
    σ * κ * den σ κ φ η = 1 + σ * κ * φ - η * (1 + σ * κ) := by
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  unfold den; field_simp; ring

/-- Cochrane (2023), eq. (17.12), p. 403: with a determinate rule and `|η| ≤ 1` the denominator
is nonzero. -/
theorem den_ne_zero {σ κ φ η : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ))
    (hη : |η| ≤ 1) : den σ κ φ η ≠ 0 := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  intro h0
  have e := den_mul (φ := φ) (η := η) hσκ.ne'
  rw [h0, mul_zero] at e
  have e' : 1 + σ * κ * φ = η * (1 + σ * κ) := by linarith
  rw [e', abs_mul] at hc
  have : |η| * |1 + σ * κ| ≤ |1 + σ * κ| := by
    calc |η| * |1 + σ * κ| ≤ 1 * |1 + σ * κ| := mul_le_mul_of_nonneg_right hη (abs_nonneg _)
      _ = |1 + σ * κ| := one_mul _
  linarith

/-- Cochrane (2023), eq. (17.12), p. 403: for `φ > 1`, `η ≤ 1` the denominator is positive. -/
theorem den_pos {σ κ φ η : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hη : η ≤ 1) :
    0 < den σ κ φ η := by
  have e := den_mul (φ := φ) (η := η) hσκ.ne'
  have : 0 < σ * κ * den σ κ φ η := by rw [e]; nlinarith
  exact pos_of_mul_pos_right this hσκ.le

/-- Cochrane (2023), eq. (17.12), p. 403: with an AR(1) disturbance, `π_t = −u_t/den` is an
equilibrium of (17.11). -/
theorem ar1_solves (𝔼 : ExpectationSystem Ω) {σ κ φ η : ℝ} (hσκ : σ * κ ≠ 0)
    (hD : den σ κ φ η ≠ 0) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) :
    RERule 𝔼 σ κ φ u (fun t => (-1 / den σ κ φ η) • u t) := by
  refine ⟨fun t => by rw [map_smul, hu.1 t], fun t ω => ?_⟩
  rw [map_smul, hu.2 t]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e := den_mul (φ := φ) (η := η) hσκ
  field_simp
  linear_combination u t ω * e

/-- Cochrane (2023), eq. (17.12), p. 403: with an AR(1) disturbance (`|η| ≤ 1`), bounded
adapted `u` and a determinate rule, the unique bounded equilibrium of (17.11) is
`π_t = −u_t/(φ − η + (1−η)/(σκ))`. -/
theorem eq_17_12 (𝔼 : ExpectationSystem Ω) {σ κ φ η M : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) (hη : |η| ≤ 1) {u π : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hM : ∀ t ω, |u t ω| ≤ M) (hπb : BoundedProc π)
    (hπ : RERule 𝔼 σ κ φ u π) (t : ℕ) (ω : Ω) :
    π t ω = -1 / den σ κ φ η * u t ω := by
  have hD := den_ne_zero hσκ hφ hη
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  have hf : ∀ t ω, |(fun t => (-(σ * κ)) • u t) t ω| ≤ σ * κ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hσκ]
    exact mul_le_mul_of_nonneg_left (hM t ω) hσκ.le
  have hfa : 𝔼.Adapted (fun t => (-(σ * κ)) • u t) := fun t => by rw [map_smul, hu.1 t]
  obtain ⟨-, -, -, huniq⟩ := scalar_existsUnique 𝔼 hc hf hfa
  have hs := ar1_solves 𝔼 hσκ.ne' hD hu
  have hb : BoundedProc (fun t => (-1 / den σ κ φ η) • u t) := ⟨|-1 / den σ κ φ η| * M,
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have e := (huniq π ((reRule_iff_scalar 𝔼 σ κ φ u π).mp hπ).2 hπb).trans
    (huniq _ ((reRule_iff_scalar 𝔼 σ κ φ u _).mp hs).2 hb).symm
  rw [e]; rfl

/-- Cochrane (2023), eq. (17.12), p. 403: the two printed forms agree,
`σκ/((1+σκφ)(1 − η(1+σκ)/(1+σκφ))) = 1/(φ − η + (1−η)/(σκ))`. -/
theorem coeff_17_12_forms {σ κ φ η : ℝ} (hσκ : σ * κ ≠ 0) (hM : 1 + σ * κ * φ ≠ 0)
    (hD : den σ κ φ η ≠ 0) :
    σ * κ / ((1 + σ * κ * φ) * (1 - η * ((1 + σ * κ) / (1 + σ * κ * φ)))) =
      1 / den σ κ φ η := by
  have e := den_mul (φ := φ) (η := η) hσκ
  have h2 : (1 + σ * κ * φ) * (1 - η * ((1 + σ * κ) / (1 + σ * κ * φ))) =
      σ * κ * den σ κ φ η := by rw [e]; field_simp
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  rw [h2]; field_simp

/-- Cochrane (2023), p. 403 and eq. (17.12): the forward series evaluated at an AR(1)
disturbance, `−σκ/(1+σκφ) ∑ ((1+σκ)/(1+σκφ))ʲ E_t u_{t+j} = −u_t/den`. -/
theorem eq_17_12_series (𝔼 : ExpectationSystem Ω) {σ κ φ η : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) (hη : |η| ≤ 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (t : ℕ) (ω : Ω) :
    -(σ * κ) / (1 + σ * κ * φ) *
      ∑' j, ((1 + σ * κ) / (1 + σ * κ * φ)) ^ j * 𝔼.E t (u (t + j)) ω =
      -1 / den σ κ φ η * u t ω := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  have hM : 1 + σ * κ * φ ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith [abs_nonneg (1 + σ * κ)]
  have hD := den_ne_zero hσκ hφ hη
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  have hcη : |c * η| < 1 := by
    rw [abs_mul]
    have hc1 : |c| < 1 := by
      rw [abs_div, div_lt_one (abs_pos.mpr hM)]; exact hc
    calc |c| * |η| ≤ |c| * 1 := mul_le_mul_of_nonneg_left hη (abs_nonneg c)
      _ < 1 := by rw [mul_one]; exact hc1
  have hterm : ∀ j : ℕ, c ^ j * 𝔼.E t (u (t + j)) ω = u t ω * (c * η) ^ j := fun j => by
    rw [𝔼.ar1_iterate hu t j, Pi.smul_apply, smul_eq_mul, mul_pow]; ring
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hcη]
  have h1 : 1 - c * η ≠ 0 := by
    intro h0
    have : c * η = 1 := by linarith
    rw [this, abs_one] at hcη; exact lt_irrefl _ hcη
  have hf := coeff_17_12_forms hσκ.ne' hM hD
  rw [mul_comm η c] at hf
  have e2 : -(σ * κ) / (1 + σ * κ * φ) * (u t ω * (1 - c * η)⁻¹) =
      -(σ * κ / ((1 + σ * κ * φ) * (1 - c * η))) * u t ω := by
    field_simp
  rw [e2, hf]
  ring

/-- Cochrane (2023), eq. (17.13), p. 404: the two printed forms of the interest-rate
coefficient agree, `1 − φ/den = −(η − (1−η)/(σκ))/den`. -/
theorem coeff_17_13_forms {σ κ φ η : ℝ} (hD : den σ κ φ η ≠ 0) :
    1 - φ / den σ κ φ η = -(η - (1 - η) / (σ * κ)) / den σ κ φ η := by
  rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
  unfold den; ring

/-- Cochrane (2023), eq. (17.13), p. 404: in the equilibrium of (17.12) the interest rate is
`i_t = φ π_t + u_t = −(η − (1−η)/(σκ))/den · u_t`. -/
theorem eq_17_13 {σ κ φ η : ℝ} (hD : den σ κ φ η ≠ 0) (u : ℝ) :
    φ * (-1 / den σ κ φ η * u) + u = -(η - (1 - η) / (σ * κ)) / den σ κ φ η * u := by
  rw [← coeff_17_13_forms hD]; field_simp; ring

/-- Cochrane (2023), p. 404, "The frictionless limit `κ → ∞` reduces to the frictionless AR(1)
responses": `−1/den → −1/(φ − η)`, which is (16.9). -/
theorem tendsto_17_12 {σ φ η : ℝ} (hσ : 0 < σ) (hφη : φ - η ≠ 0) :
    Tendsto (fun κ : ℝ => -1 / den σ κ φ η) atTop (𝓝 (-1 / (φ - η))) := by
  have h1 : Tendsto (fun κ : ℝ => σ * κ) atTop atTop := Tendsto.const_mul_atTop hσ tendsto_id
  have h2 : Tendsto (fun κ : ℝ => (1 - η) / (σ * κ)) atTop (𝓝 0) :=
    h1.const_div_atTop (1 - η)
  have h3 : Tendsto (fun κ : ℝ => den σ κ φ η) atTop (𝓝 (φ - η)) := by
    simpa [den] using h2.const_add (φ - η)
  exact tendsto_const_nhds.div h3 hφη

/-- Cochrane (2023), p. 404: the frictionless limit of (17.13) is (16.11),
`i_t = −η/(φ − η) u_t`. -/
theorem tendsto_17_13 {σ φ η : ℝ} (hσ : 0 < σ) (hφη : φ - η ≠ 0) :
    Tendsto (fun κ : ℝ => -(η - (1 - η) / (σ * κ)) / den σ κ φ η) atTop
      (𝓝 (-η / (φ - η))) := by
  have h1 : Tendsto (fun κ : ℝ => σ * κ) atTop atTop := Tendsto.const_mul_atTop hσ tendsto_id
  have h2 : Tendsto (fun κ : ℝ => (1 - η) / (σ * κ)) atTop (𝓝 0) :=
    h1.const_div_atTop (1 - η)
  have h3 : Tendsto (fun κ : ℝ => den σ κ φ η) atTop (𝓝 (φ - η)) := by
    simpa [den] using h2.const_add (φ - η)
  have h4 : Tendsto (fun κ : ℝ => -(η - (1 - η) / (σ * κ))) atTop (𝓝 (-η)) := by
    simpa using (h2.const_sub η).neg
  exact h4.div h3 hφη

/-- Cochrane (2023), p. 404, "a persistent shock `η = 1` produces a super-Fisherian result":
`π_t = i_t = −u_t/(φ − 1)`. -/
theorem superFisher_simple (σ κ φ : ℝ) :
    -1 / den σ κ φ 1 = -1 / (φ - 1) ∧ -(1 - (1 - 1) / (σ * κ)) / den σ κ φ 1 = -1 / (φ - 1) := by
  unfold den; constructor <;> norm_num

/-- Cochrane (2023), p. 405, the open-mouth case: for `η = 1/(1+σκ)`, (17.12)–(17.13) give
`π_t = −u_t/φ` and `i_t = 0`. -/
theorem openMouth_simple {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    -1 / den σ κ φ (1 / (1 + σ * κ)) = -1 / φ ∧
      -(1 / (1 + σ * κ) - (1 - 1 / (1 + σ * κ)) / (σ * κ)) / den σ κ φ (1 / (1 + σ * κ)) =
        0 := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have hσ := left_ne_zero_of_mul hσκ.ne'
  have hκ := right_ne_zero_of_mul hσκ.ne'
  have h2 : 1 / (1 + σ * κ) - (1 - 1 / (1 + σ * κ)) / (σ * κ) = 0 := by
    field_simp; ring
  have h3 : den σ κ φ (1 / (1 + σ * κ)) = φ := by
    unfold den; linear_combination (-1 : ℝ) * h2
  rw [h2, h3]; simp

/-- Cochrane (2023), p. 405: the sign of the interest-rate response. For `s = σκ > 0`,
`η − (1−η)/s > 0` iff `η > 1/(1+s)`. -/
theorem num_pos_iff {s η : ℝ} (hs : 0 < s) : 0 < η - (1 - η) / s ↔ 1 / (1 + s) < η := by
  rw [sub_pos, div_lt_iff₀ hs, div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 405, "the actual interest rate goes in the direction of the disturbance,
and inflation goes in the opposite direction … only … for sufficiently transitory shocks": for
`φ > 1` and `η ≤ 1`, inflation always moves opposite to `u`, and the interest rate moves with
`u` iff `η < 1/(1+σκ)`. -/
theorem i_coeff_pos_iff {σ κ φ η : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hη : η ≤ 1) :
    -1 / den σ κ φ η < 0 ∧
      (0 < -(η - (1 - η) / (σ * κ)) / den σ κ φ η ↔ η < 1 / (1 + σ * κ)) := by
  have hD := den_pos hσκ hφ hη
  refine ⟨div_neg_of_neg_of_pos (by norm_num) hD, ?_⟩
  rw [div_pos_iff_of_pos_right hD, neg_pos, sub_neg, lt_div_iff₀ hσκ,
    lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + σ * κ)]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), Figure 17.3, p. 404 (`σ = 1`, `κ = 1/2`, any `φ > 1`): `1/(1+σκ) = 2/3`;
at `η = 0.3` the rate moves with the disturbance, at `η = 0.9` against it (Fisherian), and at
`η = 2/3` not at all. -/
theorem fig17_3 {φ : ℝ} (hφ : 1 < φ) :
    (1 : ℝ) / (1 + 1 * (1 / 2)) = 2 / 3 ∧
      0 < -((0.3 : ℝ) - (1 - 0.3) / (1 * (1 / 2))) / den 1 (1 / 2) φ 0.3 ∧
      -((0.9 : ℝ) - (1 - 0.9) / (1 * (1 / 2))) / den 1 (1 / 2) φ 0.9 < 0 ∧
      -((2 / 3 : ℝ) - (1 - 2 / 3) / (1 * (1 / 2))) / den 1 (1 / 2) φ (2 / 3) = 0 := by
  refine ⟨by norm_num, ?_, ?_, by norm_num⟩
  · exact div_pos (by norm_num) (den_pos (by norm_num) hφ (by norm_num))
  · exact div_neg_of_neg_of_pos (by norm_num) (den_pos (by norm_num) hφ (by norm_num))

/-! ### The three-equation model: A1 §1.13.1, (1.59)–(1.62) -/

/-- Cochrane (2023), eqs. (17.15)–(17.17), (17.20) and A1 §1.8, p. 571: the three-equation
model with the rule substituted, `x_t = E_t x_{t+1} − σ(φπ_t + u_t − E_t π_{t+1})`,
`π_t = β E_t π_{t+1} + κ x_t` (so `i_t = φπ_t + u_t`), with `x`, `π` adapted. -/
def ThreeEq (𝔼 : ExpectationSystem Ω) (σ κ β φ : ℝ) (u x π : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted x ∧ 𝔼.Adapted π ∧ ∀ t ω,
    x t ω = 𝔼.E t (x (t + 1)) ω - σ * (φ * π t ω + u t ω - 𝔼.E t (π (t + 1)) ω) ∧
    π t ω = β * 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), A1 eq. (1.60), p. 588: the denominator
`φ − η + (1 − βη)(1 − η)/(σκ)`. -/
noncomputable def denF (σ κ β φ η : ℝ) : ℝ := φ - η + (1 - β * η) * (1 - η) / (σ * κ)

/-- Cochrane (2023), A1 eq. (1.60), p. 588:
`σκ · denF = βη² − (1 + β + σκ)η + 1 + σκφ`. -/
theorem denF_mul {σ κ β φ η : ℝ} (hσκ : σ * κ ≠ 0) :
    σ * κ * denF σ κ β φ η = β * η ^ 2 - (1 + β + σ * κ) * η + 1 + σ * κ * φ := by
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  unfold denF; field_simp; ring

/-- Cochrane (2023), A1 eq. (1.60), p. 588: for `φ > 1`, `0 ≤ β ≤ 1` and `η ≤ 1` the
denominator is positive. -/
theorem denF_pos {σ κ β φ η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hφ : 1 < φ)
    (hη : η ≤ 1) : 0 < denF σ κ β φ η := by
  have e := denF_mul (β := β) (φ := φ) (η := η) hσκ.ne'
  have key : β * η ^ 2 - (1 + β + σ * κ) * η + 1 + σ * κ * φ =
      σ * κ * (φ - 1) + (η - 1) * (β * η - 1 - σ * κ) := by ring
  have h2 : 0 ≤ (η - 1) * (β * η - 1 - σ * κ) := by
    apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
    nlinarith
  have : 0 < σ * κ * denF σ κ β φ η := by rw [e, key]; nlinarith
  exact pos_of_mul_pos_right this hσκ.le

/-- Cochrane (2023), A1 eq. (1.59), p. 588: undetermined coefficients. If `u` is AR(1) and
`(απ, αx)` solve (1.59), then `π_t = απ u_t`, `x_t = αx u_t` solve the three-equation
model. -/
theorem msv_solves (𝔼 : ExpectationSystem Ω) {σ κ β φ η aπ ax : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (h1 : (1 - η) * ax = -σ * (1 + (φ - η) * aπ))
    (h2 : (1 - β * η) * aπ = κ * ax) :
    ThreeEq 𝔼 σ κ β φ u (fun t => ax • u t) (fun t => aπ • u t) := by
  refine ⟨fun t => by rw [map_smul, hu.1 t], fun t => by rw [map_smul, hu.1 t],
    fun t ω => ⟨?_, ?_⟩⟩ <;>
  · simp only [map_smul, hu.2 t, Pi.smul_apply, smul_eq_mul]
    first
    | linear_combination u t ω * h1
    | linear_combination u t ω * h2

/-- Cochrane (2023), A1 p. 588, "Since these equations must hold for any `u_{i,t}`, conclude"
(1.59): if the guess solves the model and the disturbance is nonzero somewhere, the
coefficients satisfy (1.59). -/
theorem coeffs_of_msv (𝔼 : ExpectationSystem Ω) {σ κ β φ η aπ ax : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (h : ThreeEq 𝔼 σ κ β φ u (fun t => ax • u t) (fun t => aπ • u t))
    {t : ℕ} {ω : Ω} (hne : u t ω ≠ 0) :
    (1 - η) * ax = -σ * (1 + (φ - η) * aπ) ∧ (1 - β * η) * aπ = κ * ax := by
  obtain ⟨e1, e2⟩ := h.2.2 t ω
  simp only [map_smul, hu.2 t, Pi.smul_apply, smul_eq_mul] at e1 e2
  constructor
  · apply mul_right_cancel₀ hne; linear_combination e1
  · apply mul_right_cancel₀ hne; linear_combination e2

/-- Cochrane (2023), A1 eqs. (1.59)–(1.61), p. 588: (1.59) holds iff
`απ = −1/(φ − η + (1−βη)(1−η)/(σκ))` (1.60) and `αx = (1 − βη)/κ · απ` (1.61). -/
theorem eq_1_59_iff {σ κ β φ η aπ ax : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hD : denF σ κ β φ η ≠ 0) :
    ((1 - η) * ax = -σ * (1 + (φ - η) * aπ) ∧ (1 - β * η) * aπ = κ * ax) ↔
      (aπ = -1 / denF σ κ β φ η ∧ ax = (1 - β * η) / κ * aπ) := by
  have e := denF_mul (β := β) (φ := φ) (η := η) (mul_ne_zero hσ hκ)
  constructor
  · rintro ⟨h1, h2⟩
    have hax : ax = (1 - β * η) / κ * aπ := by field_simp; linear_combination -h2
    refine ⟨?_, hax⟩
    rw [hax] at h1
    rw [eq_div_iff hD]
    have h3 : σ * κ * (aπ * denF σ κ β φ η) = σ * κ * (-1) := by
      rw [← mul_assoc, mul_comm (σ * κ) aπ, mul_assoc, e]
      field_simp at h1
      linear_combination h1
    exact mul_left_cancel₀ (mul_ne_zero hσ hκ) h3
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by rw [h2]; field_simp⟩
    rw [h2, h1]
    field_simp
    linear_combination e

/-- Cochrane (2023), A1 eq. (1.62), p. 588: with (1.60), the interest rate
`i_t = φ π_t + u_t` equals `(η − (1−βη)(1−η)/(σκ)) π_t`. -/
theorem msv_i_eq {σ κ β φ η : ℝ} (hD : denF σ κ β φ η ≠ 0) (u : ℝ) :
    φ * (-1 / denF σ κ β φ η * u) + u =
      (η - (1 - β * η) * (1 - η) / (σ * κ)) * (-1 / denF σ κ β φ η * u) := by
  field_simp
  unfold denF
  ring

/-- Cochrane (2023), A1 eq. (1.55), p. 586, and p. 420: the transition matrix of the
forward-looking form `(x_t, π_t) = A E_t(x_{t+1}, π_{t+1}) + w_t` of the three-equation model,
`A = P⁻¹Q` with the structural matrices `P`, `Q` of (17.29)–(17.32) at `φ_x = 0` (the same
matrices as the determinacy analysis, `SharedTools.Pmat`, `SharedTools.Qmat`). -/
noncomputable def transA (σ κ β φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  solvedA (Pmat σ κ φ 0) (Qmat σ β)

/-- Cochrane (2023), A1 eq. (1.55), p. 586: the entries of the transition matrix,
`A = (1 + σκφ)⁻¹ [[1, σ(1 − φβ)], [κ, β + σκ]]`. -/
theorem transA_explicit (σ κ β φ : ℝ) :
    transA σ κ β φ = !![1 / (1 + σ * κ * φ), σ * (1 - φ * β) / (1 + σ * κ * φ);
      κ / (1 + σ * κ * φ), (β + σ * κ) / (1 + σ * κ * φ)] := by
  have hD : det2 (Pmat σ κ φ 0) = 1 + σ * κ * φ := by rw [det2_Pmat]; ring
  unfold transA solvedA
  rw [hD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pmat, Qmat] <;> ring

/-- Cochrane (2023), A1 §1.8 and (1.55), pp. 571, 586: every solution of the three-equation
model solves the vector system `X_t = A E_t X_{t+1} + w_t` with `X = (x, π)`. -/
theorem threeEq_solves (𝔼 : ExpectationSystem Ω) {σ κ β φ : ℝ} (hM : 1 + σ * κ * φ ≠ 0)
    {u x π : ℕ → Ω → ℝ} (h : ThreeEq 𝔼 σ κ β φ u x π) :
    𝔼.Solves (transA σ κ β φ)
      (fun t => ![(-σ / (1 + σ * κ * φ)) • u t, (-(σ * κ) / (1 + σ * κ * φ)) • u t])
      (fun t => ![x t, π t]) := by
  intro t j
  funext ω
  obtain ⟨e1, e2⟩ := h.2.2 t ω
  have g0 : x t ω = 1 / (1 + σ * κ * φ) * 𝔼.E t (x (t + 1)) ω +
      σ * (1 - φ * β) / (1 + σ * κ * φ) * 𝔼.E t (π (t + 1)) ω +
      -σ / (1 + σ * κ * φ) * u t ω := by
    field_simp
    linear_combination e1 - σ * φ * e2
  have g1 : π t ω = κ / (1 + σ * κ * φ) * 𝔼.E t (x (t + 1)) ω +
      (β + σ * κ) / (1 + σ * κ * φ) * 𝔼.E t (π (t + 1)) ω +
      -(σ * κ) / (1 + σ * κ * φ) * u t ω := by
    have k1 : π t ω * (1 + σ * κ * φ) = κ * 𝔼.E t (x (t + 1)) ω +
        (β + σ * κ) * 𝔼.E t (π (t + 1)) ω + -(σ * κ) * u t ω := by
      linear_combination e2 + κ * e1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      ← add_div, eq_div_iff hM]
    linear_combination k1
  fin_cases j <;> simp [transA_explicit]
  · linear_combination g0
  · linear_combination g1

/-- Cochrane (2023), A1 p. 587: for `φ > 1` (and `0 < β < 1`, `σκ > 0`) the transition matrix
satisfies the Schur–Cohn condition (both eigenvalues of `A` inside the unit circle, i.e. both
eigenvalues of the matrix of (1.55) outside it). -/
theorem schurStable_of_one_lt {σ κ β φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) : SchurStable (tr2 (transA σ κ β φ)) (det2 (transA σ κ β φ)) := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  have htr : tr2 (transA σ κ β φ) = (1 + β + σ * κ) / (1 + σ * κ * φ) := by
    simp [tr2, transA_explicit]; field_simp; ring
  have hdet : det2 (transA σ κ β φ) = β / (1 + σ * κ * φ) := by
    simp [det2, transA_explicit]; field_simp; ring
  rw [htr, hdet]
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos (by positivity), div_lt_one hM]; nlinarith
  · rw [abs_of_pos (by positivity), div_lt_iff₀ hM, add_mul, div_mul_cancel₀ _ hM.ne']
    nlinarith

/-- Cochrane (2023), A1 pp. 587–588 and p. 415: for `φ > 1` the minimal-state-variable solution
`π_t = −u_t/denF`, `x_t = (1−βη)/κ · π_t` is the unique bounded equilibrium of the
three-equation model with a bounded AR(1) disturbance (`|η| ≤ 1`). -/
theorem msv_unique (𝔼 : ExpectationSystem Ω) {σ κ β φ η M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φ) (hη : |η| ≤ 1) {u x π : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hM : ∀ t ω, |u t ω| ≤ M) (h : ThreeEq 𝔼 σ κ β φ u x π)
    (hxb : BoundedProc x) (hπb : BoundedProc π) :
    π = (fun t => (-1 / denF σ κ β φ η) • u t) ∧
      x = (fun t => ((1 - β * η) / κ * (-1 / denF σ κ β φ η)) • u t) := by
  have hσκ : 0 < σ * κ := mul_pos hσ hκ
  have hD := (denF_pos hσκ hβ0.le hβ1.le hφ (abs_le.mp hη).2).ne'
  have hMM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  obtain ⟨h1, h2⟩ := (eq_1_59_iff hσ.ne' hκ.ne' hD).mpr ⟨rfl, rfl⟩
  have hs := msv_solves 𝔼 hu h1 h2
  have hS := schurStable_of_one_lt hσκ hβ0 hβ1 hφ
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπ, hMπ⟩ := hπb
  set aπ := -1 / denF σ κ β φ η
  set ax := (1 - β * η) / κ * aπ
  have e := 𝔼.system_unique hS (threeEq_solves 𝔼 hMM h) (threeEq_solves 𝔼 hMM hs)
    (fun t j => by fin_cases j <;> simp [h.1 t, h.2.1 t])
    (fun t j => by fin_cases j <;> simp [hs.1 t, hs.2.1 t])
    ⟨max Mx Mπ, fun t j ω => by
      fin_cases j
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMπ t ω).trans (le_max_right _ _)⟩
    ⟨max (|ax| * M) (|aπ| * M), fun t j ω => by
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_left _ _)
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
          smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_right _ _)⟩
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · simpa using congrFun (congrFun e t) 1
  · simpa using congrFun (congrFun e t) 0

/-- Cochrane (2023), p. 415, the super-Fisherian full model: for `η = 1`,
`π = −u/(φ−1)`, `x = −(1−β)/κ · u/(φ−1)` and `i = −u/(φ−1)`. -/
theorem superFisher_full (σ κ β φ : ℝ) :
    -1 / denF σ κ β φ 1 = -1 / (φ - 1) ∧
      (1 - β * 1) / κ * (-1 / denF σ κ β φ 1) = -((1 - β) / κ) * (1 / (φ - 1)) ∧
      (1 - (1 - β * 1) * (1 - 1) / (σ * κ)) * (-1 / denF σ κ β φ 1) = -1 / (φ - 1) := by
  unfold denF
  refine ⟨by norm_num, by ring, by norm_num⟩

/-- Cochrane (2023), p. 415: in the super-Fisherian case a negative disturbance raises the
interest rate and (with `β < 1`) output, "because the `φπ_t` term … wins". -/
theorem superFisher_full_signs {κ β φ u : ℝ} (hκ : 0 < κ) (hβ : β < 1) (hφ : 1 < φ)
    (hu : u < 0) : 0 < -1 / (φ - 1) * u ∧ 0 < -((1 - β) / κ) * (1 / (φ - 1)) * u := by
  have h1 : 0 < φ - 1 := by linarith
  have h2 : 0 < (1 - β) / κ := div_pos (by linarith) hκ
  constructor
  · rw [neg_div]; nlinarith [div_pos one_pos h1]
  · have : 0 < (1 - β) / κ * (1 / (φ - 1)) := mul_pos h2 (div_pos one_pos h1)
    nlinarith

/-- Cochrane (2023), A1 p. 588: (1.60) generalises the simple model (17.12): at `β = 0` the
denominators coincide. -/
theorem msv_beta_zero (σ κ φ η : ℝ) : denF σ κ 0 φ η = den σ κ φ η := by
  unfold denF den; ring

/-- Cochrane (2023), A1 p. 588: (1.60) generalises the frictionless model (16.9): as `κ → ∞`,
`−1/denF → −1/(φ − η)`. -/
theorem tendsto_1_60 {σ β φ η : ℝ} (hσ : 0 < σ) (hφη : φ - η ≠ 0) :
    Tendsto (fun κ : ℝ => -1 / denF σ κ β φ η) atTop (𝓝 (-1 / (φ - η))) := by
  have h1 : Tendsto (fun κ : ℝ => σ * κ) atTop atTop := Tendsto.const_mul_atTop hσ tendsto_id
  have h2 : Tendsto (fun κ : ℝ => (1 - β * η) * (1 - η) / (σ * κ)) atTop (𝓝 0) :=
    h1.const_div_atTop _
  have h3 : Tendsto (fun κ : ℝ => denF σ κ β φ η) atTop (𝓝 (φ - η)) := by
    simpa [denF] using h2.const_add (φ - η)
  exact tendsto_const_nhds.div h3 hφη

/-! ### A1 §1.8: the lag-operator form -/

/-- Cochrane (2023), A1 §1.8, p. 572: the lag polynomial
`1 − (1+β+σκ)/(1+σκφ) z + β/(1+σκφ) z²` evaluated at `η` equals `σκ · denF/(1+σκφ)`, so the
lag-operator solution `−σκ/((1+σκφ)(1−λ₁η)(1−λ₂η)) u` is (1.60). -/
theorem lag_form {σ κ β φ η : ℝ} (hσκ : σ * κ ≠ 0) (hM : 1 + σ * κ * φ ≠ 0)
    (hD : denF σ κ β φ η ≠ 0) :
    -(σ * κ) / ((1 + σ * κ * φ) * (1 - (1 + β + σ * κ) / (1 + σ * κ * φ) * η +
      β / (1 + σ * κ * φ) * η ^ 2)) = -1 / denF σ κ β φ η := by
  have e := denF_mul (β := β) (φ := φ) (η := η) hσκ
  have h2 : (1 + σ * κ * φ) * (1 - (1 + β + σ * κ) / (1 + σ * κ * φ) * η +
      β / (1 + σ * κ * φ) * η ^ 2) = σ * κ * denF σ κ β φ η := by
    rw [e]; field_simp; ring
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  rw [h2]; field_simp

/-- Cochrane (2023), A1 §1.8, p. 572: factoring the lag polynomial with the roots of
`z² − T z + D` (`T = (1+β+σκ)/(1+σκφ)`, `D = β/(1+σκφ)`), complex in general:
`(1 − λ₁η)(1 − λ₂η) = 1 − Tη + Dη²`. -/
theorem lag_factor (T D : ℝ) (η : ℂ) :
    (1 - root₁ T D * η) * (1 - root₂ T D * η) = 1 - T * η + D * η ^ 2 := by
  rw [← root_sum T D, ← root_prod T D]; ring

/-- Cochrane (2023), A1 §1.8, p. 572: the partial-fraction step,
`(1/(λ₁−λ₂))(−λ₁/(1−λ₁η) + λ₂/(1−λ₂η)) = −1/((1−λ₁η)(1−λ₂η))`, in any field. -/
theorem partial_fractions {K : Type*} [Field K] {l1 l2 η : K} (h12 : l1 - l2 ≠ 0)
    (h1 : 1 - l1 * η ≠ 0) (h2 : 1 - l2 * η ≠ 0) :
    1 / (l1 - l2) * (-l1 / (1 - l1 * η) + l2 / (1 - l2 * η)) =
      -1 / ((1 - l1 * η) * (1 - l2 * η)) := by
  field_simp
  ring

/-- Cochrane (2023), A1 §1.8, p. 572: the forward sums at an AR(1) disturbance,
`∑ λʲ ηʲ = 1/(1 − λη)` for `‖λη‖ < 1` (complex `λ`). -/
theorem lag_sum_ar1 {l η : ℂ} (h : ‖l * η‖ < 1) :
    HasSum (fun j : ℕ => l ^ j * η ^ j) (1 - l * η)⁻¹ := by
  simpa [mul_pow] using hasSum_geometric_of_norm_lt_one h

/-- Cochrane (2023), A1 §1.8, p. 572 (survey error E11, corrected): for `φ > 1` both lag roots
`λ₁, λ₂` (roots of `z² − Tz + D`) have modulus strictly below one, so both are solved
forward. -/
theorem lag_roots_norm_lt_one {σ κ β φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) :
    ‖root₁ ((1 + β + σ * κ) / (1 + σ * κ * φ)) (β / (1 + σ * κ * φ))‖ < 1 ∧
      ‖root₂ ((1 + β + σ * κ) / (1 + σ * κ * φ)) (β / (1 + σ * κ * φ))‖ < 1 := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  rw [← schurStable_iff_roots]
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos (by positivity), div_lt_one hM]; nlinarith
  · rw [abs_of_pos (by positivity), div_lt_iff₀ hM, add_mul, div_mul_cancel₀ _ hM.ne']
    nlinarith

/-- Cochrane (2023), A1 §1.8, p. 572, survey error E11: the printed "both roots unstable,
`λ₁ < 1` and `λ₂ < 1`" treats the roots as real, but they can be complex: with `φ = 1.5`,
`β = 0.99`, `σ = 1`, `κ = 0.5` the discriminant is negative and `λ₁` has nonzero imaginary
part. -/
theorem lag_roots_complex_example :
    discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5)) (0.99 / (1 + 1 * 0.5 * 1.5)) < 0 ∧
      (root₁ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5)) (0.99 / (1 + 1 * 0.5 * 1.5))).im ≠
        0 := by
  have hd : discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5) : ℝ)
      (0.99 / (1 + 1 * 0.5 * 1.5)) < 0 := by
    unfold discQ; norm_num
  refine ⟨hd, ?_⟩
  have hn : ¬ (0 ≤ discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5) : ℝ)
      (0.99 / (1 + 1 * 0.5 * 1.5))) := not_le.mpr hd
  unfold root₁
  simp only [hn, ↓reduceIte]
  have : 0 < Real.sqrt (-discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5) : ℝ)
      (0.99 / (1 + 1 * 0.5 * 1.5))) := Real.sqrt_pos.mpr (by linarith)
  simp only [ne_eq]
  positivity

/-! ### The open-mouth persistence `η*` (p. 416) -/

/-- Cochrane (2023), p. 416: the open-mouth condition `η − (1−βη)(1−η)/(σκ) = 0` is
`βη² − (1 + β + σκ)η + 1 = 0`. -/
theorem openMouth_iff_quadratic {σ κ β η : ℝ} (hσκ : σ * κ ≠ 0) :
    η - (1 - β * η) * (1 - η) / (σ * κ) = 0 ↔ β * η ^ 2 - (1 + β + σ * κ) * η + 1 = 0 := by
  rw [sub_eq_zero, eq_div_iff hσκ]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 416: the smaller root of `βη² − (1 + β + σκ)η + 1 = 0`. -/
noncomputable def etaStar (σ κ β : ℝ) : ℝ :=
  ((1 + β + σ * κ) - Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / (2 * β)

/-- Cochrane (2023), p. 416: `η*` is a root of `βη² − (1 + β + σκ)η + 1`. -/
theorem etaStar_root {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    β * etaStar σ κ β ^ 2 - (1 + β + σ * κ) * etaStar σ κ β + 1 = 0 := by
  have hdisc : 0 ≤ (1 + β + σ * κ) ^ 2 - 4 * β := by nlinarith
  have hs := Real.sq_sqrt hdisc
  unfold etaStar
  set r := Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)
  field_simp
  linear_combination hs

/-- Cochrane (2023), p. 416: `0 < η* < 1`. -/
theorem etaStar_mem {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < etaStar σ κ β ∧ etaStar σ κ β < 1 := by
  set S := 1 + β + σ * κ
  have hdisc : 0 ≤ S ^ 2 - 4 * β := by nlinarith
  set r := Real.sqrt (S ^ 2 - 4 * β)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs : r ^ 2 = S ^ 2 - 4 * β := Real.sq_sqrt hdisc
  have hS : 0 < S := by positivity
  have hrS : r < S := by nlinarith
  have hr2 : S - 2 * β < r := by nlinarith
  unfold etaStar
  constructor
  · exact div_pos (by linarith) (by positivity)
  · rw [div_lt_one (by positivity)]; linarith

/-- Cochrane (2023), p. 416: the factorisation used for uniqueness and signs,
`f(a) − f(b) = (a − b)(β(a + b) − (1 + β + σκ))` for `f(η) = βη² − (1+β+σκ)η + 1`. -/
theorem quad_sub (σ κ β a b : ℝ) :
    (β * a ^ 2 - (1 + β + σ * κ) * a + 1) - (β * b ^ 2 - (1 + β + σ * κ) * b + 1) =
      (a - b) * (β * (a + b) - (1 + β + σ * κ)) := by ring

/-- Cochrane (2023), p. 416: `η*` is the only root of the open-mouth condition with `η ≤ 1`
(in particular the only one in `(0, 1)`). -/
theorem eq_etaStar {σ κ β η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hη : η ≤ 1)
    (h : β * η ^ 2 - (1 + β + σ * κ) * η + 1 = 0) : η = etaStar σ κ β := by
  have h0 := etaStar_root hσκ hβ0 hβ1
  obtain ⟨-, h1⟩ := etaStar_mem hσκ hβ0 hβ1
  have e := quad_sub σ κ β η (etaStar σ κ β)
  rw [h, h0, sub_zero] at e
  have hneg : β * (η + etaStar σ κ β) - (1 + β + σ * κ) < 0 := by nlinarith
  have := mul_eq_zero.mp e.symm
  rcases this with h2 | h2
  · linarith
  · linarith

/-- Cochrane (2023), p. 416, open mouth in the full model: at `η = η*` the interest rate does
not move, `i = 0`, and `π = −u/φ`. -/
theorem openMouth_full {σ κ β φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    denF σ κ β φ (etaStar σ κ β) = φ ∧
      etaStar σ κ β - (1 - β * etaStar σ κ β) * (1 - etaStar σ κ β) / (σ * κ) = 0 := by
  have h0 := (openMouth_iff_quadratic hσκ.ne').mpr (etaStar_root hσκ hβ0 hβ1)
  refine ⟨?_, h0⟩
  unfold denF
  linear_combination (-1 : ℝ) * h0

/-- Cochrane (2023), p. 416 and Figure 17.8 (`β = 0.95`, `κ = 1/2`, `σ = 1`): the open-mouth
persistence is `η* ≈ 0.51`; precisely `0.508 < η* < 0.509`. -/
theorem etaStar_fig17_8 : (0.508 : ℝ) < etaStar 1 (1 / 2) 0.95 ∧
    etaStar 1 (1 / 2) 0.95 < 0.509 := by
  have hr := etaStar_root (σ := 1) (κ := 1 / 2) (β := 0.95) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨h0, h1⟩ := etaStar_mem (σ := 1) (κ := 1 / 2) (β := 0.95) (by norm_num) (by norm_num)
    (by norm_num)
  set e := etaStar 1 (1 / 2) 0.95
  constructor
  · by_contra hc
    push Not at hc
    have := quad_sub 1 (1 / 2) 0.95 e 0.508
    nlinarith
  · by_contra hc
    push Not at hc
    have := quad_sub 1 (1 / 2) 0.95 e 0.509
    nlinarith

/-- Cochrane (2023), p. 416, "for more transitory `η`, … a negative `u_{i,t}` shock lowers
interest rates `i_t` and raises inflation": for `φ > 1` and `η < η*`, the interest-rate
coefficient `(η − (1−βη)(1−η)/(σκ))·(−1/denF)` is positive and the inflation coefficient
negative. -/
theorem full_i_coeff_pos_of_lt {σ κ β φ η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) (hη : η < etaStar σ κ β) :
    -1 / denF σ κ β φ η < 0 ∧
      0 < (η - (1 - β * η) * (1 - η) / (σ * κ)) * (-1 / denF σ κ β φ η) := by
  obtain ⟨-, h1⟩ := etaStar_mem hσκ hβ0 hβ1
  have hD := denF_pos (η := η) hσκ hβ0.le hβ1.le hφ (by linarith)
  have hneg : -1 / denF σ κ β φ η < 0 := div_neg_of_neg_of_pos (by norm_num) hD
  refine ⟨hneg, mul_pos_of_neg_of_neg ?_ hneg⟩
  have hf : 0 < β * η ^ 2 - (1 + β + σ * κ) * η + 1 := by
    have e := quad_sub σ κ β η (etaStar σ κ β)
    rw [etaStar_root hσκ hβ0 hβ1, sub_zero] at e
    rw [e]
    exact mul_pos_of_neg_of_neg (by linarith) (by nlinarith)
  have : η * (σ * κ) - (1 - β * η) * (1 - η) < 0 := by nlinarith
  rw [sub_neg, lt_div_iff₀ hσκ]
  linarith

/-- Cochrane (2023), pp. 415–416: for `φ > 1` and `η* < η ≤ 1` the interest rate moves with
inflation (opposite to the disturbance): the interest-rate coefficient is negative. -/
theorem full_i_coeff_neg_of_gt {σ κ β φ η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) (hη1 : etaStar σ κ β < η) (hη : η ≤ 1) :
    (η - (1 - β * η) * (1 - η) / (σ * κ)) * (-1 / denF σ κ β φ η) < 0 := by
  have hD := denF_pos hσκ hβ0.le hβ1.le hφ hη
  have hneg : -1 / denF σ κ β φ η < 0 := div_neg_of_neg_of_pos (by norm_num) hD
  refine mul_neg_of_pos_of_neg ?_ hneg
  have hf : β * η ^ 2 - (1 + β + σ * κ) * η + 1 < 0 := by
    have e := quad_sub σ κ β η (etaStar σ κ β)
    rw [etaStar_root hσκ hβ0 hβ1, sub_zero] at e
    rw [e]
    exact mul_neg_of_pos_of_neg (by linarith) (by nlinarith)
  rw [sub_pos, div_lt_iff₀ hσκ]
  nlinarith

/-- Cochrane (2023), Figure 17.8, p. 416 (`β = 0.95`, `κ = 1/2`, `σ = 1`, `φ = 1.5`,
`η = 0.3`): a negative disturbance lowers the interest rate and raises inflation. -/
theorem fig17_8_transitory {u : ℝ} (hu : u < 0) :
    0 < -1 / denF 1 (1 / 2) 0.95 1.5 0.3 * u ∧
      (0.3 - (1 - 0.95 * 0.3) * (1 - 0.3) / (1 * (1 / 2))) *
        (-1 / denF 1 (1 / 2) 0.95 1.5 0.3) * u < 0 := by
  have hlt : (0.3 : ℝ) < etaStar 1 (1 / 2) 0.95 := by linarith [etaStar_fig17_8.1]
  obtain ⟨h1, h2⟩ := full_i_coeff_pos_of_lt (σ := 1) (κ := 1 / 2) (β := 0.95) (φ := 1.5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlt
  exact ⟨mul_pos_of_neg_of_neg h1 hu, mul_neg_of_pos_of_neg h2 hu⟩

end Cochrane.KeynesianStickyPrices.AR1Responses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Full-model responses: inflation as a two-sided moving average of interest rates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4 "Full-model
responses" and §17.4.1 "Interest rates and inflation", eqs. (17.15)–(17.18), pp. 407–410, with
Figures 17.5–17.6; the two-sided moving average is eq. (5.5), p. 119, and Online Appendix A1,
§1.7, pp. 569–571.

## The model

`Model` is (17.15)–(17.17) with IS and Phillips-curve disturbances, for an arbitrary
`ExpectationSystem`. Eliminating output and the real rate gives (17.18) (`eq_17_18`, with
disturbances `eq_17_18_shocks`): with `κ ≠ 0` the model holds iff `r_t = i_t − E_t π_{t+1}`,
`κ x_t = π_t − β E_t π_{t+1} − u_{π,t}` and
`σκ i_t = −β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t + (u_{π,t} − E_t u_{π,t+1}) + κ u_{x,t}`.

## Perfect foresight: the two-sided solution

Under perfect foresight (sequences `ℕ → ℝ`, `pf_model_iff` links them to the
`perfectForesight` expectation system) the roots `λ₁ > 1 > λ₂ > 0` of
`λ² − (1 + β + σκ) λ + β` (restated from the Chapter 5 project `StickyPriceFiscal`) factor the
second-order equation (`second_iff_factor`): bounded inflation solves (17.18) iff
`λ₁ π_{t+1} = π_t + σκ F_t` with `F_t = ∑_{k≥0} λ₂ᵏ i_{t+k}`. Hence (`pf_existsUnique`) for
bounded `i` the bounded equilibria are exactly the paths `path p`, one for each initial inflation
`π_0 = p` — the single multiple-equilibrium jump of perfect foresight. The equilibrium with no
past surprises is the two-sided moving average (5.5),
`π_t = c [∑_{j<t} λ₁^{−j} i_{t−1−j} + λ₂ F_t]`, `c = σκ/(λ₁ − λ₂)` (`twoSided_eq`).
Long-run neutrality: if `i_t → ī` then every bounded equilibrium has `π_t → ī` and
`x_t → (1 − β) ī/κ` (`tendsto_pi`, `tendsto_x`).

## Figure 17.5 (permanent rise announced at date 0, effective from date `T`)

For the step `i_t = 1{t ≥ T}`: `F_step` (`F_t = λ₂^{T−t}/(1 − λ₂)`); the no-surprise equilibrium
`antPath` jumps at the announcement (`antPath_zero_pos`: "the δ₁ = 0 equilibrium
already had a little jump", p. 410), rises before the rate rises (`antPath_le_T`:
`π_t = c λ₂^{T−t+1}/(1 − λ₂)` for `t ≤ T`), is positive, strictly increasing, below one and
converges to one (`antPath_pos`, `antPath_strictMono`, `antPath_lt_one`,
`antPath_tendsto_one`). Output falls up to and including the date of the rise
(`antPath_x_neg`), because output is low exactly when inflation is rising faster than `1/β`
(`x_neg_iff`), and tends to `(1 − β)/κ ≥ 0` (`antPath_x_tendsto`). For **every** initial
inflation, an announced rise raises inflation at every date before (and after) the rise relative
to no rise (`rise_raises_inflation`); the response to a surprise rise joins the anticipated
response at the date of the rise (`dashed_joins_solid`). Fig. 17.6 (p. 410): every initial
jump, positive (A, B), zero (D) or negative (E), is an equilibrium and converges to one
(`fig17_6_any_jump`).

## Figure 17.5: the rise anticipated from the infinite past (ℤ-indexed paths)

On `ℤ` (`SecondZ`, `stepZ`), the permanent rise at date `T` known forever has exactly one
bounded perfect-foresight inflation path (`zPath_existsUnique`; uniqueness for every bounded rate
path, `secondZ_unique`), in closed form `zPath`: `π_t = c λ₂^{T−t+1}/(1 − λ₂)` for `t ≤ T`,
`π_t = 1 − (1 − c λ₂/(1 − λ₂)) λ₁^{−(t−T)}` for `t ≥ T`. It depends only on `t − T`
(`zPath_shift`). The no-surprise response announced at date 0 coincides with it from the
announcement on (`zPath_eq_antPath`, `antPath_eq_zPath_shift`), and as the announcement
recedes every response, whatever its initial jump, converges to it date by date
(`tendsto_zPath`).
-/

namespace Cochrane.KeynesianStickyPrices.FullModel

open Filter Topology
open SharedTools (tendsto_zero_of_stable fwd_sum_props fwd_sum_tendsto int_homog_zero)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model (17.15)–(17.17) -/

/-- Cochrane (2023), eq. (17.15), p. 407: the IS curve `x_t = E_t x_{t+1} − σ r_t + u_{x,t}`. -/
def IS (σ : ℝ) (ux r x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • r t + ux t

/-- Cochrane (2023), eq. (17.16), p. 407: the Fisher equation `i_t = r_t + E_t π_{t+1}`. -/
def Fisher (i r π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + 𝔼.E t (π (t + 1))

/-- Cochrane (2023), eq. (17.17), p. 407: the Phillips curve
`π_t = β E_t π_{t+1} + κ x_t + u_{π,t}`. -/
def PC (β κ : ℝ) (uπ x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + uπ t

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407: the full new-Keynesian model with IS and
Phillips-curve disturbances `u_x`, `u_π`. -/
def Model (σ β κ : ℝ) (ux uπ i r x π : ℕ → Ω → ℝ) : Prop :=
  IS 𝔼 σ ux r x ∧ Fisher 𝔼 i r π ∧ PC 𝔼 β κ uπ x π

/-- Cochrane (2023), eq. (17.16), p. 407: the Fisher equation defines the real rate,
`r_t = i_t − E_t π_{t+1}`. -/
theorem fisher_iff (i r π : ℕ → Ω → ℝ) :
    Fisher 𝔼 i r π ↔ r = fun t => i t - 𝔼.E t (π (t + 1)) := by
  constructor
  · intro h
    funext t
    rw [h t]
    abel
  · intro h t
    subst h
    exact (sub_add_cancel _ _).symm

/-- Cochrane (2023), eq. (17.18), p. 408, with the disturbances of (17.15)–(17.17) (the form
behind (17.27), p. 418): for `κ ≠ 0` (and any `σ`) the model holds iff the real rate is
`r_t = i_t − E_t π_{t+1}`, output is given by the Phillips curve, and
`σκ i_t = −β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t + (u_{π,t} − E_t u_{π,t+1})
  + κ u_{x,t}`. -/
theorem eq_17_18_shocks {σ β κ : ℝ} (hκ : κ ≠ 0) {ux uπ i r x π : ℕ → Ω → ℝ} :
    Model 𝔼 σ β κ ux uπ i r x π ↔
      (r = fun t => i t - 𝔼.E t (π (t + 1))) ∧
      (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)) - uπ t)) ∧
      ∀ t, (σ * κ) • i t = -β • 𝔼.E t (π (t + 2)) + (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) -
        π t + (uπ t - 𝔼.E t (uπ (t + 1))) + κ • ux t := by
  have hkk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  constructor
  · rintro ⟨his, hf, hpc⟩
    have hr := (fisher_iff 𝔼 i r π).mp hf
    refine ⟨hr, fun t => ?_, fun t => ?_⟩
    · funext ω
      have h := congrFun (hpc t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h ⊢
      have hk : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ
      linear_combination (-κ⁻¹) * h - x t ω * hk
    · funext ω
      have h1 := congrFun (his t) ω
      have h2 := congrFun (hpc t) ω
      have h3 := congrFun (congrArg (𝔼.E t) (hpc (t + 1))) ω
      rw [map_add, map_add, map_smul, map_smul, 𝔼.tower (Nat.le_succ t)] at h3
      rw [hr] at h1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
        neg_mul] at h1 h2 h3 ⊢
      linear_combination κ * h1 + h2 - h3
  · rintro ⟨hr, hx, hsec⟩
    have hf : Fisher 𝔼 i r π := (fisher_iff 𝔼 i r π).mpr hr
    have hpc : PC 𝔼 β κ uπ x π := by
      intro t
      funext ω
      have h := congrFun (hx t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h ⊢
      rw [h]
      linear_combination (-(π t ω - β * 𝔼.E t (π (t + 1)) ω - uπ t ω)) * hkk
    refine ⟨fun t => ?_, hf, hpc⟩
    funext ω
    have h1 := congrFun (hsec t) ω
    have h2 := congrFun (hpc t) ω
    have h3 := congrFun (congrArg (𝔼.E t) (hpc (t + 1))) ω
    rw [map_add, map_add, map_smul, map_smul, 𝔼.tower (Nat.le_succ t)] at h3
    rw [hr]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      neg_mul] at h1 h2 h3 ⊢
    apply mul_left_cancel₀ hκ
    linear_combination -h2 + h3 + h1

/-- Cochrane (2023), eq. (17.18), p. 408: with no disturbances, eliminating `x_t` from
(17.15)–(17.17) gives `i_t = (1/(σκ)) [−β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t]`. -/
theorem eq_17_18 {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ 0 0 i r x π) (t : ℕ) :
    i t = (σ * κ)⁻¹ • (-β • 𝔼.E t (π (t + 2)) + (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) - π t) := by
  have h3 := ((eq_17_18_shocks 𝔼 hκ).mp h).2.2 t
  simp only [Pi.zero_apply, map_zero, sub_zero, add_zero, smul_zero] at h3
  rw [← h3, smul_smul, inv_mul_cancel₀ (mul_ne_zero hσ hκ), one_smul]


/-! ### Perfect foresight -/

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, under perfect foresight and with no
disturbances (the setting of Figs. 17.5–17.7): `x_t = x_{t+1} − σ(i_t − π_{t+1})` and
`π_t = β π_{t+1} + κ x_t`, for sequences. -/
def PFEqm (σ β κ : ℝ) (i x π : ℕ → ℝ) : Prop :=
  ∀ t, x t = x (t + 1) - σ * (i t - π (t + 1)) ∧ π t = β * π (t + 1) + κ * x t

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407: `PFEqm` is the model under the
`perfectForesight` expectation system (with zero disturbances), the real rate being
`r_t = i_t − π_{t+1}`. -/
theorem pf_model_iff {σ β κ : ℝ} (i r x π : ℕ → ℝ) :
    Model perfectForesight σ β κ 0 0 (fun t _ => i t) (fun t _ => r t) (fun t _ => x t)
        (fun t _ => π t) ↔
      (∀ t, r t = i t - π (t + 1)) ∧ PFEqm σ β κ i x π := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun t => ?_, fun t => ⟨?_, ?_⟩⟩
    · have := congrFun (h2 t) ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply] at this
      linarith
    · have e1 := congrFun (h1 t) ()
      have e2 := congrFun (h2 t) ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
      rw [e1, show r t = i t - π (t + 1) by linarith]
      ring
    · have e3 := congrFun (h3 t) ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply] at e3
      linarith
  · rintro ⟨hr, h⟩
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> funext u <;>
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    · rw [hr t]
      linarith [(h t).1]
    · rw [hr t]
      ring
    · linarith [(h t).2]

/-- A real sequence is bounded. -/
def BoundedS (z : ℕ → ℝ) : Prop := ∃ M, ∀ t, |z t| ≤ M

/-- Cochrane (2023), eq. (17.18), p. 408, under perfect foresight:
`π_t − (1 + β + σκ) π_{t+1} + β π_{t+2} = −σκ i_t`. -/
def Second (σ β κ : ℝ) (i π : ℕ → ℝ) : Prop :=
  ∀ t, π t - (1 + β + σ * κ) * π (t + 1) + β * π (t + 2) = -(σ * κ) * i t

/-- Cochrane (2023), eq. (17.18), p. 408 (perfect foresight): for `κ ≠ 0`, `(x, π)` is an
equilibrium iff `x_t = (π_t − β π_{t+1})/κ` and inflation solves (17.18). -/
theorem pfEqm_iff_second {σ β κ : ℝ} (hκ : κ ≠ 0) (i x π : ℕ → ℝ) :
    PFEqm σ β κ i x π ↔ (∀ t, x t = (π t - β * π (t + 1)) / κ) ∧ Second σ β κ i π := by
  constructor
  · intro h
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [eq_div_iff hκ]
      linarith [(h t).2]
    · obtain ⟨h1, h2⟩ := h t
      have h3 := (h (t + 1)).2
      linear_combination h2 - h3 + κ * h1
  · rintro ⟨hx, hs⟩ t
    refine ⟨?_, ?_⟩
    · rw [hx t, hx (t + 1)]
      field_simp
      linear_combination hs t
    · rw [hx t]
      field_simp
      ring

/-! ### The roots (restated from the Chapter 5 project `StickyPriceFiscal`) -/

/-- Cochrane (2023), eq. (5.6), p. 119 (restated from the Chapter 5 project): the larger root
`λ₁ = [(1 + β + σκ) + √((1 + β + σκ)² − 4β)]/2` of `λ² − (1 + β + σκ) λ + β`. -/
noncomputable def lam1 (σ β κ : ℝ) : ℝ :=
  (1 + β + σ * κ + Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119 (restated from the Chapter 5 project): the smaller root
`λ₂ = [(1 + β + σκ) − √((1 + β + σκ)² − 4β)]/2`. -/
noncomputable def lam2 (σ β κ : ℝ) : ℝ :=
  (1 + β + σ * κ - Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the discriminant is positive when `σκ > 0`, `β > 0`. -/
theorem disc_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    0 < (1 + β + σ * κ) ^ 2 - 4 * β := by
  nlinarith [sq_nonneg (1 - β), sq_nonneg (σ * κ)]

/-- Cochrane (2023), A1 p. 570: `λ₁ + λ₂ = 1 + β + σκ`. -/
theorem lam_sum (σ β κ : ℝ) : lam1 σ β κ + lam2 σ β κ = 1 + β + σ * κ := by
  unfold lam1 lam2; ring

/-- Cochrane (2023), A1 p. 570: `λ₁ λ₂ = β`. -/
theorem lam_prod {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam1 σ β κ * lam2 σ β κ = β := by
  unfold lam1 lam2
  have h := Real.sq_sqrt (disc_pos ha hβ).le
  nlinarith [h]

/-- Cochrane (2023), A1 p. 570: `σκ = (λ₁ − 1)(1 − λ₂)`. -/
theorem sigma_kappa_eq {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    σ * κ = (lam1 σ β κ - 1) * (1 - lam2 σ β κ) := by
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  linear_combination -h1 + h2

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ < λ₁`. -/
theorem lam2_lt_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam2 σ β κ < lam1 σ β κ := by
  unfold lam1 lam2
  have := Real.sqrt_pos.mpr (disc_pos ha hβ)
  linarith

/-- Cochrane (2023), p. 408: `λ₁ > 1`. -/
theorem one_lt_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 1 < lam1 σ β κ := by
  by_contra hc
  push Not at hc
  have h := sigma_kappa_eq ha hβ
  have h2 := lam2_lt_lam1 ha hβ
  nlinarith

/-- Cochrane (2023), p. 408: `λ₂ < 1`. -/
theorem lam2_lt_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : lam2 σ β κ < 1 := by
  have h := sigma_kappa_eq ha hβ
  have h1 := one_lt_lam1 ha hβ
  by_contra hc
  push Not at hc
  nlinarith

/-- Cochrane (2023), p. 408: `λ₂ > 0`. -/
theorem lam2_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 0 < lam2 σ β κ := by
  have h := lam_prod ha hβ
  have h1 := one_lt_lam1 ha hβ
  by_contra hc
  push Not at hc
  nlinarith

/-! ### Forward sums of the interest rate -/

/-- Cochrane (2023), eq. (5.5), p. 119: the forward-solved factor `F_t = ∑_{k≥0} qᵏ i_{t+k}`. -/
noncomputable def F (q : ℝ) (i : ℕ → ℝ) (t : ℕ) : ℝ := ∑' k, q ^ k * i (t + k)

/-- The forward sum converges for bounded `i` and `0 ≤ q < 1`. -/
theorem F_summable {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℕ) : Summable (fun k => q ^ k * i (t + k)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
  exact mul_le_mul_of_nonneg_left (hi (t + k)) (pow_nonneg hq0 k)

/-- The forward sum satisfies `F_t = i_t + q F_{t+1}` (from `SharedTools.fwd_sum_props`). -/
theorem F_rec {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℕ) : F q i t = i t + q * F q i (t + 1) :=
  (fwd_sum_props (by rwa [abs_of_nonneg hq0]) hi).1 t

/-- The forward sum is bounded by `M/(1 − q)` (from `SharedTools.fwd_sum_props`). -/
theorem F_bound {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℕ) : |F q i t| ≤ M / (1 - q) := by
  have h := (fwd_sum_props (by rwa [abs_of_nonneg hq0]) hi).2 t
  rwa [abs_of_nonneg hq0] at h

/-- A bounded solution of `d_t = q d_{t+1}` with `|q| < 1` vanishes. -/
theorem homog_zero {q : ℝ} (hq : |q| < 1) {d : ℕ → ℝ} (hd : ∀ t, d t = q * d (t + 1))
    (hb : BoundedS d) : d = 0 := by
  obtain ⟨M, hM⟩ := hb
  have hit : ∀ t k, d t = q ^ k * d (t + k) := by
    intro t k
    induction k with
    | zero => simp
    | succ k ih => rw [ih, hd (t + k), ← add_assoc, pow_succ]; ring
  funext t
  have hle : ∀ k, |d t| ≤ |q| ^ k * M := fun k => by
    rw [hit t k, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM (t + k)) (pow_nonneg (abs_nonneg q) k)
  have hlim : Tendsto (fun k => |q| ^ k * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg q) hq).mul_const M
  have h0 : |d t| ≤ 0 := ge_of_tendsto' hlim hle
  simpa using h0

/-- The forward sum is the unique bounded solution of `G_t = i_t + q G_{t+1}`. -/
theorem F_unique {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i G : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (hG : ∀ t, G t = i t + q * G (t + 1)) (hGb : BoundedS G) : G = F q i := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  obtain ⟨MG, hMG⟩ := hGb
  have h := homog_zero hq (d := fun t => G t - F q i t)
    (fun t => by rw [hG t, F_rec hq0 hq1 hi t]; ring)
    ⟨MG + M / (1 - q), fun t => (abs_sub _ _).trans (add_le_add (hMG t) (F_bound hq0 hq1 hi t))⟩
  funext t
  have := congrFun h t
  simp only [Pi.zero_apply] at this
  linarith


/-! ### Factoring the lag polynomial and the family of bounded equilibria -/

/-- Cochrane (2023), A1 §1.7, p. 570: the factorisation
`(π_t − λ₁ π_{t+1}) − λ₂ (π_{t+1} − λ₁ π_{t+2}) = π_t − (1 + β + σκ) π_{t+1} + β π_{t+2}`. -/
theorem factor_identity {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (π : ℕ → ℝ) (t : ℕ) :
    (π t - lam1 σ β κ * π (t + 1)) - lam2 σ β κ * (π (t + 1) - lam1 σ β κ * π (t + 2)) =
      π t - (1 + β + σ * κ) * π (t + 1) + β * π (t + 2) := by
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  linear_combination (-(π (t + 1))) * h1 + π (t + 2) * h2

/-- Cochrane (2023), eq. (5.5), p. 119, and A1 §1.7, p. 570 (perfect foresight): for bounded
`i` and bounded `π`, (17.18) holds iff `λ₁ π_{t+1} = π_t + σκ F_t`,
`F_t = ∑_{k≥0} λ₂ᵏ i_{t+k}` (the unstable factor solved forward, the stable one backward). -/
theorem second_iff_factor {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hπ : BoundedS π) :
    Second σ β κ i π ↔ ∀ t, lam1 σ β κ * π (t + 1) = π t + σ * κ * F (lam2 σ β κ) i t := by
  have hl0 := (lam2_pos ha hβ).le
  have hl1 := lam2_lt_one ha hβ
  constructor
  · intro hs
    obtain ⟨Mπ, hMπ⟩ := hπ
    have hq : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg hl0]; exact hl1
    have hd := homog_zero hq
      (d := fun t => π t - lam1 σ β κ * π (t + 1) + σ * κ * F (lam2 σ β κ) i t)
      (fun t => by
        have e := hs t
        have f := F_rec hl0 hl1 hi t
        have fi := factor_identity ha hβ π t
        linear_combination fi + e + (σ * κ) * f)
      ⟨Mπ + |lam1 σ β κ| * Mπ + |σ * κ| * (M / (1 - lam2 σ β κ)), fun t => by
        have h1 := hMπ t
        have h2 := hMπ (t + 1)
        have h3 := F_bound hl0 hl1 hi t
        calc |π t - lam1 σ β κ * π (t + 1) + σ * κ * F (lam2 σ β κ) i t|
            ≤ |π t| + |lam1 σ β κ| * |π (t + 1)| + |σ * κ| * |F (lam2 σ β κ) i t| := by
              rw [← abs_mul, ← abs_mul]
              exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
          _ ≤ Mπ + |lam1 σ β κ| * Mπ + |σ * κ| * (M / (1 - lam2 σ β κ)) := by gcongr⟩
    intro t
    have := congrFun hd t
    simp only [Pi.zero_apply] at this
    linarith
  · intro hf t
    have e1 := hf t
    have e2 := hf (t + 1)
    have f := F_rec hl0 hl1 hi t
    have fi := factor_identity ha hβ π t
    linear_combination -fi - e1 + lam2 σ β κ * e2 - (σ * κ) * f

/-- Cochrane (2023), p. 408 and eq. (5.5): the perfect-foresight equilibrium path with initial
inflation `π_0 = p`, `π_{t+1} = (π_t + σκ F_t)/λ₁`. -/
noncomputable def path (σ β κ : ℝ) (i : ℕ → ℝ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | t + 1 => (path σ β κ i p t + σ * κ * F (lam2 σ β κ) i t) / lam1 σ β κ

/-- The path satisfies the factored equation `λ₁ π_{t+1} = π_t + σκ F_t`. -/
theorem path_factor {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (i : ℕ → ℝ) (p : ℝ) (t : ℕ) :
    lam1 σ β κ * path σ β κ i p (t + 1) = path σ β κ i p t + σ * κ * F (lam2 σ β κ) i t := by
  have h1 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  simp only [path]
  field_simp

/-- Cochrane (2023), pp. 137–138 (restated from the Chapter 5 project): if
`|x_{t+1}| ≤ c |x_t| + F` with `0 ≤ c < 1` and `|x_0| ≤ V`, then `|x_t| ≤ V + F/(1 − c)`. -/
theorem bounded_of_rec {c F V : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hF : 0 ≤ F) {x : ℕ → ℝ}
    (hx0 : |x 0| ≤ V) (hx : ∀ t, |x (t + 1)| ≤ c * |x t| + F) (t : ℕ) :
    |x t| ≤ V + F / (1 - c) := by
  induction t with
  | zero =>
    have : 0 ≤ F / (1 - c) := div_nonneg hF (by linarith)
    linarith
  | succ t ih =>
    have hV : 0 ≤ V := (abs_nonneg _).trans hx0
    have key : c * (V + F / (1 - c)) + F ≤ V + F / (1 - c) := by
      have h1c : 0 < 1 - c := by linarith
      have : F = (1 - c) * (F / (1 - c)) := by field_simp
      nlinarith
    calc |x (t + 1)| ≤ c * |x t| + F := hx t
      _ ≤ c * (V + F / (1 - c)) + F := by gcongr
      _ ≤ V + F / (1 - c) := key

/-- The path is bounded for bounded `i`. -/
theorem path_bounded {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (p : ℝ) : BoundedS (path σ β κ i p) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hM : 0 ≤ M := (abs_nonneg _).trans (hi 0)
  have hc1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have h2p : 0 < 1 - lam2 σ β κ := by linarith
  have hnn : 0 ≤ (lam1 σ β κ)⁻¹ * (σ * κ * (M / (1 - lam2 σ β κ))) := by positivity
  refine ⟨|p| + (lam1 σ β κ)⁻¹ * (σ * κ * (M / (1 - lam2 σ β κ))) / (1 - (lam1 σ β κ)⁻¹),
    bounded_of_rec (inv_nonneg.mpr hl0.le) hc1 hnn le_rfl (fun t => ?_)⟩
  have hF := F_bound h20 h21 hi t
  simp only [path]
  rw [div_eq_inv_mul, abs_mul, abs_of_pos (inv_pos.mpr hl0), ← mul_add]
  gcongr
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos ha]
  gcongr

/-- Cochrane (2023), p. 408 and eq. (5.5) (perfect foresight): for bounded `i` and every
initial inflation `p`, there is exactly one bounded solution of (17.18) with `π_0 = p`. Bounded
equilibria are indexed by the single initial jump. -/
theorem pf_existsUnique {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (p : ℝ) :
    ∃! π : ℕ → ℝ, BoundedS π ∧ Second σ β κ i π ∧ π 0 = p := by
  refine ⟨path σ β κ i p, ⟨path_bounded ha hβ hi p,
    (second_iff_factor ha hβ hi (path_bounded ha hβ hi p)).mpr (path_factor ha hβ i p), rfl⟩,
    fun π ⟨hb, hs, h0⟩ => ?_⟩
  have hf := (second_iff_factor ha hβ hi hb).mp hs
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    apply mul_left_cancel₀ hl0
    rw [hf t, path_factor ha hβ i p t, ih]

/-- Cochrane (2023), §17.4.1, p. 408 (perfect foresight): for `σκ > 0`, `κ ≠ 0`, `β > 0` and
bounded `i`, a bounded `(x, π)` is an equilibrium iff `x_t = (π_t − β π_{t+1})/κ` and `π` is the
path with initial value `π_0`. -/
theorem pf_eqm_iff {σ β κ M : ℝ} (ha : 0 < σ * κ) (hκ : κ ≠ 0) (hβ : 0 < β) {i x π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hb : BoundedS π) :
    PFEqm σ β κ i x π ↔
      (∀ t, x t = (π t - β * π (t + 1)) / κ) ∧ π = path σ β κ i (π 0) := by
  rw [pfEqm_iff_second hκ]
  refine and_congr_right fun _ => ⟨fun hs => ?_, fun h => ?_⟩
  · obtain ⟨_, _, huniq⟩ := pf_existsUnique ha hβ hi (π 0)
    exact huniq π ⟨hb, hs, rfl⟩ ▸ (huniq _ ⟨path_bounded ha hβ hi _,
      (second_iff_factor ha hβ hi (path_bounded ha hβ hi _)).mpr (path_factor ha hβ i _),
      rfl⟩).symm
  · rw [h]
    exact (second_iff_factor ha hβ hi (path_bounded ha hβ hi _)).mpr (path_factor ha hβ i _)

/-! ### Long-run neutrality -/

/-- A stable recursion `y_{t+1} = q y_t + b_t`, `0 ≤ q < 1`, with `b_t → B` has
`y_t → B/(1 − q)` (from `SharedTools.tendsto_zero_of_stable`). -/
theorem tendsto_of_rec {q B : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {y b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 B)) (hy : ∀ t, y (t + 1) = q * y t + b t) :
    Tendsto y atTop (𝓝 (B / (1 - q))) := by
  have h1q : 1 - q ≠ 0 := by linarith
  have hq : |q| < 1 := by rwa [abs_of_nonneg hq0]
  have he := tendsto_zero_of_stable hq (x := fun t => y t - B / (1 - q))
    (f := fun t => b t - B) (fun t => by
      rw [hy t]
      field_simp
      ring) (by simpa using hb.sub_const B)
  simpa using he.add_const (B / (1 - q))

/-- If `i_t → ī` (bounded `i`), the forward sum `F_t = ∑ qᵏ i_{t+k}` tends to `ī/(1 − q)` (from
`SharedTools.fwd_sum_tendsto`). -/
theorem tendsto_F {q M ib : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hl : Tendsto i atTop (𝓝 ib)) :
    Tendsto (F q i) atTop (𝓝 (ib / (1 - q))) :=
  fwd_sum_tendsto (by rwa [abs_of_nonneg hq0]) hi hl

/-- Cochrane (2023), §17.4.1, p. 408 ("long-run impulse response = 1"; A1 p. 570): if the
interest rate converges, `i_t → ī`, then in **every** bounded perfect-foresight equilibrium
inflation converges to the same value, `π_t → ī`. -/
theorem tendsto_pi {σ β κ M ib : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hl : Tendsto i atTop (𝓝 ib)) (hb : BoundedS π)
    (hs : Second σ β κ i π) : Tendsto π atTop (𝓝 ib) := by
  have hf := (second_iff_factor ha hβ hi hb).mp hs
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hF := tendsto_F h20 h21 hi hl
  have hrec : ∀ t, π (t + 1) =
      (lam1 σ β κ)⁻¹ * π t + (lam1 σ β κ)⁻¹ * (σ * κ) * F (lam2 σ β κ) i t := fun t => by
    rw [mul_assoc, ← mul_add, ← hf t, ← mul_assoc, inv_mul_cancel₀ hl0.ne', one_mul]
  have h := tendsto_of_rec (inv_nonneg.mpr hl0.le) (inv_lt_one_of_one_lt₀ hl1)
    (hF.const_mul ((lam1 σ β κ)⁻¹ * (σ * κ))) hrec
  convert h using 2
  have hsk := sigma_kappa_eq ha hβ
  have h2 : 1 - lam2 σ β κ ≠ 0 := by linarith
  have h3 : lam1 σ β κ - 1 ≠ 0 := by linarith
  field_simp
  rw [mul_assoc ib σ κ, hsk]
  ring

/-- Cochrane (2023), §17.4.1, p. 408: correspondingly output converges to its long-run
Phillips-curve value, `x_t → (1 − β) ī/κ`. -/
theorem tendsto_x {σ β κ M ib : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i x π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hl : Tendsto i atTop (𝓝 ib)) (hb : BoundedS π)
    (hs : Second σ β κ i π) (hx : ∀ t, x t = (π t - β * π (t + 1)) / κ) :
    Tendsto x atTop (𝓝 ((1 - β) * ib / κ)) := by
  have hp := tendsto_pi ha hβ hi hl hb hs
  have hp1 := hp.comp (tendsto_add_atTop_nat 1)
  have h := (hp.sub (hp1.const_mul β)).div_const κ
  rw [show (ib - β * ib) / κ = (1 - β) * ib / κ by ring] at h
  refine h.congr fun t => ?_
  rw [hx t]
  rfl


/-! ### The two-sided moving average (5.5) -/

/-- Cochrane (2023), eq. (5.5), p. 119: the coefficient `c = σκ/(λ₁ − λ₂)`. -/
noncomputable def coef (σ β κ : ℝ) : ℝ := σ * κ / (lam1 σ β κ - lam2 σ β κ)

/-- Cochrane (2023), eq. (5.5), p. 119: `c (λ₁ − λ₂) = σκ`. -/
theorem coef_mul {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    coef σ β κ * (lam1 σ β κ - lam2 σ β κ) = σ * κ := by
  unfold coef
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr (lam2_lt_lam1 ha hβ).ne')

/-- Cochrane (2023), eq. (5.5), p. 119: `c > 0`. -/
theorem coef_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 0 < coef σ β κ :=
  div_pos ha (sub_pos.mpr (lam2_lt_lam1 ha hβ))

/-- Cochrane (2023), eq. (5.5), p. 119 and §17.4.1, p. 408 (perfect foresight, no past
surprises): the two-sided moving average
`π_t = c [∑_{j<t} λ₁^{−j} i_{t−1−j} + λ₂ ∑_{k≥0} λ₂ᵏ i_{t+k}]`. -/
noncomputable def twoSided (σ β κ : ℝ) (i : ℕ → ℝ) (t : ℕ) : ℝ :=
  coef σ β κ * (∑ j ∈ Finset.range t, (lam1 σ β κ)⁻¹ ^ j * i (t - 1 - j) +
    lam2 σ β κ * F (lam2 σ β κ) i t)

/-- Cochrane (2023), eq. (5.5), p. 119: the two-sided moving average satisfies the factored
equation `λ₁ π_{t+1} = π_t + σκ F_t`. -/
theorem twoSided_factor {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (t : ℕ) :
    lam1 σ β κ * twoSided σ β κ i (t + 1) = twoSided σ β κ i t + σ * κ * F (lam2 σ β κ) i t := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have hll : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have f := F_rec (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hi t
  have hc := coef_mul ha hβ
  have hs : ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * i (t + 1 - 1 - j) =
      (lam1 σ β κ)⁻¹ * (∑ j ∈ Finset.range t, (lam1 σ β κ)⁻¹ ^ j * i (t - 1 - j)) + i t := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega, pow_succ]
      ring
    · simp
  unfold twoSided
  rw [hs]
  set S := ∑ j ∈ Finset.range t, (lam1 σ β κ)⁻¹ ^ j * i (t - 1 - j)
  linear_combination (coef σ β κ * S) * hll - (coef σ β κ * lam1 σ β κ) * f +
    F (lam2 σ β κ) i t * hc

/-- Cochrane (2023), eq. (5.5), p. 119 and §17.4.1, p. 408: the equilibrium path with initial
inflation `c λ₂ F_0` (no expectational error at the start) is the two-sided moving average. -/
theorem twoSided_eq {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) :
    path σ β κ i (coef σ β κ * lam2 σ β κ * F (lam2 σ β κ) i 0) = twoSided σ β κ i := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  funext t
  induction t with
  | zero => simp [path, twoSided, mul_assoc]
  | succ t ih =>
    apply mul_left_cancel₀ hl0
    rw [path_factor ha hβ i _ t, ih, twoSided_factor ha hβ hi t]

/-! ### Figure 17.5: an announced permanent rise -/

/-- Cochrane (2023), Fig. 17.5, p. 408: the permanent rise `i_t = 1` from date `T` on, `0` before
(announced at date 0). -/
noncomputable def stepI (T t : ℕ) : ℝ := if T ≤ t then 1 else 0

/-- The step is bounded by one. -/
theorem stepI_bound (T t : ℕ) : |stepI T t| ≤ 1 := by
  unfold stepI
  split_ifs <;> norm_num

/-- Cochrane (2023), Fig. 17.5: the step tends to one. -/
theorem stepI_tendsto (T : ℕ) : Tendsto (stepI T) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop T] with t ht
  simp [stepI, ht]

/-- Cochrane (2023), Fig. 17.5: for the step, `F_t = ∑ qᵏ i_{t+k} = q^{T−t}/(1 − q)` (with
truncated subtraction: `1/(1 − q)` from date `T` on). -/
theorem F_step {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (T t : ℕ) :
    F q (stepI T) t = q ^ (T - t) / (1 - q) := by
  have h1q : 1 - q ≠ 0 := by linarith
  have h := F_unique hq0 hq1 (stepI_bound T) (G := fun t => q ^ (T - t) / (1 - q))
    (fun t => by
      simp only [stepI]
      split_ifs with h
      · rw [show T - t = 0 by omega, show T - (t + 1) = 0 by omega]
        field_simp
        ring
      · rw [show T - t = T - (t + 1) + 1 by omega, pow_succ]
        field_simp
        ring)
    ⟨1 / (1 - q), fun t => by
      rw [abs_of_nonneg (div_nonneg (pow_nonneg hq0 _) (by linarith))]
      exact div_le_div_of_nonneg_right (pow_le_one₀ hq0 hq1.le) (by linarith)⟩
  exact (congrFun h t).symm

/-- Cochrane (2023), Fig. 17.5, p. 409 and p. 410: the response to the announced rise with no
expectational error, the two-sided moving average (5.5) for the step (`antPath_twoSided`). -/
noncomputable def antPath (σ β κ : ℝ) (T : ℕ) : ℕ → ℝ :=
  path σ β κ (stepI T) (coef σ β κ * lam2 σ β κ * F (lam2 σ β κ) (stepI T) 0)

/-- Cochrane (2023), eq. (5.5) and Fig. 17.5: `antPath` is the two-sided moving average. -/
theorem antPath_twoSided {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    antPath σ β κ T = twoSided σ β κ (stepI T) :=
  twoSided_eq ha hβ (stepI_bound T)

/-- Cochrane (2023), Fig. 17.5: `antPath` is a bounded perfect-foresight equilibrium path. -/
theorem antPath_second {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    BoundedS (antPath σ β κ T) ∧ Second σ β κ (stepI T) (antPath σ β κ T) :=
  ⟨path_bounded ha hβ (stepI_bound T) _, (second_iff_factor ha hβ (stepI_bound T)
    (path_bounded ha hβ (stepI_bound T) _)).mpr (path_factor ha hβ _ _)⟩

/-- Cochrane (2023), Fig. 17.5, p. 409 ("inflation now rises before the interest rates rise"):
up to the date of the rise, `π_t = c λ₂^{T−t+1}/(1 − λ₂)` — positive and growing at rate
`1/λ₂` while the interest rate is still zero. -/
theorem antPath_le_T {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {T t : ℕ} (ht : t ≤ T) :
    antPath σ β κ T t = coef σ β κ * lam2 σ β κ ^ (T - t + 1) / (1 - lam2 σ β κ) := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1q : 1 - lam2 σ β κ ≠ 0 := by linarith
  have hc := coef_mul ha hβ
  induction t with
  | zero =>
    simp only [antPath, path, F_step h20 h21, Nat.sub_zero]
    rw [pow_succ]
    field_simp
  | succ t ih =>
    have ih' := ih (by omega)
    apply mul_left_cancel₀ hl0
    rw [antPath, path_factor ha hβ _ _ t, ← antPath, ih', F_step h20 h21,
      show T - t + 1 = T - (t + 1) + 1 + 1 by omega, show T - t = T - (t + 1) + 1 by omega]
    field_simp
    linear_combination (-(lam2 σ β κ ^ (T - (t + 1)) * lam2 σ β κ)) * hc

/-- Cochrane (2023), p. 410 ("the original δ₁ = 0 equilibrium already had a little jump in
inflation"): on the announcement date inflation jumps to `π_0 = c λ₂^{T+1}/(1 − λ₂) > 0`. -/
theorem antPath_zero_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    antPath σ β κ T 0 = coef σ β κ * lam2 σ β κ ^ (T + 1) / (1 - lam2 σ β κ) ∧
      0 < antPath σ β κ T 0 := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have h := antPath_le_T ha hβ (Nat.zero_le T)
  rw [Nat.sub_zero] at h
  refine ⟨h, ?_⟩
  rw [h]
  have := coef_pos ha hβ
  have : 0 < 1 - lam2 σ β κ := by linarith
  positivity

/-- Cochrane (2023), Fig. 17.5, p. 409: the no-surprise response rises monotonically. -/
theorem antPath_strictMono {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    StrictMono (antPath σ β κ T) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hc := coef_mul ha hβ
  have hcp := coef_pos ha hβ
  have h1q : 0 < 1 - lam2 σ β κ := by linarith
  have hfac : ∀ t, lam1 σ β κ * antPath σ β κ T (t + 1) =
      antPath σ β κ T t + σ * κ * F (lam2 σ β κ) (stepI T) t := fun t => path_factor ha hβ _ _ t
  have hFm : ∀ t, F (lam2 σ β κ) (stepI T) t ≤ F (lam2 σ β κ) (stepI T) (t + 1) := fun t => by
    rw [F_step h2.le h21, F_step h2.le h21]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one h2.le h21.le (Nat.sub_le_sub_left (Nat.le_succ t) T)) (by linarith)
  have hF0 : 0 < F (lam2 σ β κ) (stepI T) 0 := by
    rw [F_step h2.le h21]
    positivity
  -- the increments are positive
  have hd : ∀ t, antPath σ β κ T t < antPath σ β κ T (t + 1) := by
    intro t
    induction t with
    | zero =>
      have e := hfac 0
      have h0 : antPath σ β κ T 0 = coef σ β κ * lam2 σ β κ * F (lam2 σ β κ) (stepI T) 0 := rfl
      -- `λ₁ (π₁ − π₀) = c λ₁ (1 − λ₂) F₀ > 0`
      have key : lam1 σ β κ * (antPath σ β κ T 1 - antPath σ β κ T 0) =
          coef σ β κ * lam1 σ β κ * (1 - lam2 σ β κ) * F (lam2 σ β κ) (stepI T) 0 := by
        rw [mul_sub, e, h0]
        linear_combination (-F (lam2 σ β κ) (stepI T) 0) * hc
      have : 0 < lam1 σ β κ * (antPath σ β κ T 1 - antPath σ β κ T 0) := by
        rw [key]; positivity
      have := (pos_iff_pos_of_mul_pos this).mp hl0
      linarith
    | succ t ih =>
      have e1 := hfac t
      have e2 := hfac (t + 1)
      have hm := hFm t
      have : 0 < lam1 σ β κ * (antPath σ β κ T (t + 2) - antPath σ β κ T (t + 1)) := by
        rw [mul_sub, e2, e1]
        nlinarith
      have := (pos_iff_pos_of_mul_pos this).mp hl0
      linarith
  exact strictMono_nat_of_lt_succ hd

/-- Cochrane (2023), Fig. 17.5, p. 408 ("long-run response 1"): the response converges to one. -/
theorem antPath_tendsto_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    Tendsto (antPath σ β κ T) atTop (𝓝 1) :=
  tendsto_pi ha hβ (stepI_bound T) (stepI_tendsto T) (antPath_second ha hβ T).1
    (antPath_second ha hβ T).2

/-- Cochrane (2023), Fig. 17.5: the response stays below the new interest rate, `π_t < 1`. -/
theorem antPath_lt_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℕ) :
    antPath σ β κ T t < 1 :=
  ((antPath_strictMono ha hβ T) (Nat.lt_succ_self t)).trans_le
    ((antPath_strictMono ha hβ T).monotone.ge_of_tendsto (antPath_tendsto_one ha hβ T) _)

/-- Cochrane (2023), Fig. 17.5, p. 409: inflation is positive at every date, in particular at
every date before the interest rate rises. -/
theorem antPath_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℕ) :
    0 < antPath σ β κ T t :=
  (antPath_zero_pos ha hβ T).2.trans_le ((antPath_strictMono ha hβ T).monotone (Nat.zero_le t))

/-- Cochrane (2023), p. 409 ("output is low if inflation is low relative to expected future
inflation, i.e. if inflation is increasing"): with `x_t = (π_t − β π_{t+1})/κ` and `κ > 0`,
`x_t < 0` iff `π_t < β π_{t+1}`. -/
theorem x_neg_iff {β κ : ℝ} (hκ : 0 < κ) (π : ℕ → ℝ) (t : ℕ) :
    (π t - β * π (t + 1)) / κ < 0 ↔ π t < β * π (t + 1) := by
  rw [div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hκ⟩

/-- Cochrane (2023), Fig. 17.5, p. 409 ("output declines"; "fully expected interest-rate rises
do lower output"): along the no-surprise response, output is negative at every date up to and
including the date of the rise. -/
theorem antPath_x_neg {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {T t : ℕ}
    (ht : t ≤ T) :
    (antPath σ β κ T t - β * antPath σ β κ T (t + 1)) / κ < 0 := by
  have ha := mul_pos hσ hκ
  rw [x_neg_iff hκ]
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hc := coef_mul ha hβ
  have hcp := coef_pos ha hβ
  have hp := lam_prod ha hβ
  have h1q : 0 < 1 - lam2 σ β κ := by linarith
  have e : lam1 σ β κ * antPath σ β κ T (t + 1) =
      antPath σ β κ T t + σ * κ * F (lam2 σ β κ) (stepI T) t := path_factor ha hβ _ _ t
  rw [antPath_le_T ha hβ ht, F_step h2.le h21] at e
  -- `β π_{t+1} − π_t = λ₂ (λ₁ π_{t+1}) − π_t = c (λ₁ − 1) λ₂^{T−t+1}/(1 − λ₂)`
  have key : β * antPath σ β κ T (t + 1) - antPath σ β κ T t =
      coef σ β κ * (lam1 σ β κ - 1) * lam2 σ β κ ^ (T - t + 1) / (1 - lam2 σ β κ) := by
    have hb : β * antPath σ β κ T (t + 1) =
        lam2 σ β κ * (lam1 σ β κ * antPath σ β κ T (t + 1)) := by
      rw [← mul_assoc, mul_comm (lam2 σ β κ), hp]
    rw [hb, e, antPath_le_T ha hβ ht]
    field_simp
    linear_combination (-(lam2 σ β κ * lam2 σ β κ ^ (T - t))) * hc
  have : 0 < coef σ β κ * (lam1 σ β κ - 1) * lam2 σ β κ ^ (T - t + 1) / (1 - lam2 σ β κ) := by
    have : 0 < lam1 σ β κ - 1 := by linarith
    positivity
  linarith

/-- Cochrane (2023), Fig. 17.5: output converges to `(1 − β)/κ`, its long-run Phillips-curve
value (nonnegative, zero only for `β = 1`). -/
theorem antPath_x_tendsto {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    Tendsto (fun t => (antPath σ β κ T t - β * antPath σ β κ T (t + 1)) / κ) atTop
      (𝓝 ((1 - β) / κ)) := by
  have h := tendsto_x ha hβ (stepI_bound T) (stepI_tendsto T) (antPath_second ha hβ T).1
    (antPath_second ha hβ T).2 (fun t => rfl)
  simpa using h

/-- Cochrane (2023), p. 409 ("expected future interest-rate rises increase inflation today"):
for **every** initial inflation `p`, the announced rise raises inflation at every date `t ≥ 1`
(before and after the rise) relative to the path with no rise and the same initial jump. -/
theorem rise_raises_inflation {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) (p : ℝ)
    (t : ℕ) : path σ β κ (fun _ => 0) p (t + 1) < path σ β κ (stepI T) p (t + 1) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans (one_lt_lam1 ha hβ)
  have hF0 : ∀ s, F (lam2 σ β κ) (fun _ => (0 : ℝ)) s = 0 := fun s => by simp [F]
  have hFp : ∀ s, 0 < F (lam2 σ β κ) (stepI T) s := fun s => by
    rw [F_step h2.le h21]
    have : 0 < 1 - lam2 σ β κ := by linarith
    positivity
  have hle : ∀ s, path σ β κ (fun _ => 0) p s ≤ path σ β κ (stepI T) p s := by
    intro s
    induction s with
    | zero => exact le_rfl
    | succ s ih =>
      simp only [path, hF0, mul_zero, add_zero]
      gcongr
      nlinarith [hFp s]
  simp only [path, hF0, mul_zero, add_zero]
  gcongr
  nlinarith [hFp t, hle t]

/-- Cochrane (2023), Fig. 17.5, p. 409 ("the dashed line … joins the solid inflation curve"):
the no-surprise response to an unexpected rise at date `T` (announced at `T`, i.e. `antPath 0`
started at `T`) coincides from date `T` on with the response to the rise announced at date 0. -/
theorem dashed_joins_solid {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T s : ℕ) :
    antPath σ β κ T (T + s) = antPath σ β κ 0 s := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  induction s with
  | zero =>
    rw [add_zero, antPath_le_T ha hβ le_rfl, antPath_le_T ha hβ le_rfl, Nat.sub_self,
      Nat.sub_self]
  | succ s ih =>
    apply mul_left_cancel₀ hl0
    have e1 : lam1 σ β κ * antPath σ β κ T (T + s + 1) =
        antPath σ β κ T (T + s) + σ * κ * F (lam2 σ β κ) (stepI T) (T + s) :=
      path_factor ha hβ _ _ _
    have e2 : lam1 σ β κ * antPath σ β κ 0 (s + 1) =
        antPath σ β κ 0 s + σ * κ * F (lam2 σ β κ) (stepI 0) s := path_factor ha hβ _ _ _
    rw [← add_assoc, e1, e2, ih, F_step h2.le h21, F_step h2.le h21,
      show T - (T + s) = 0 by omega, Nat.zero_sub]

/-- Cochrane (2023), Fig. 17.6, pp. 409–410 (equilibria A–E): for an unexpected permanent rise
(`T = 0`), **every** initial inflation `p` — a super-neutral `π₁ = 1` (B), no jump (D), or a
negative jump (E) — gives a bounded equilibrium, and every one converges to the new interest
rate. -/
theorem fig17_6_any_jump {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (p : ℝ) :
    BoundedS (path σ β κ (stepI 0) p) ∧ Second σ β κ (stepI 0) (path σ β κ (stepI 0) p) ∧
      path σ β κ (stepI 0) p 0 = p ∧ Tendsto (path σ β κ (stepI 0) p) atTop (𝓝 1) := by
  have hb := path_bounded ha hβ (stepI_bound 0) p
  have hs := (second_iff_factor ha hβ (stepI_bound 0) hb).mpr (path_factor ha hβ _ p)
  exact ⟨hb, hs, rfl, tendsto_pi ha hβ (stepI_bound 0) (stepI_tendsto 0) hb hs⟩


/-! ### Figure 17.5: the rise anticipated from the infinite past (ℤ-indexed paths) -/

/-- Cochrane (2023), eq. (17.18), p. 408, under perfect foresight on the whole line `ℤ`:
`π_t − (1 + β + σκ) π_{t+1} + β π_{t+2} = −σκ i_t` for every date `t ∈ ℤ`. -/
def SecondZ (σ β κ : ℝ) (i π : ℤ → ℝ) : Prop :=
  ∀ t : ℤ, π t - (1 + β + σ * κ) * π (t + 1) + β * π (t + 2) = -(σ * κ) * i t

/-- A real ℤ-indexed sequence is bounded. -/
def BoundedZ (z : ℤ → ℝ) : Prop := ∃ M, ∀ t, |z t| ≤ M

/-- Cochrane (2023), Fig. 17.5, p. 409: the permanent rise `i_t = 1{t ≥ T}` on `ℤ`, known at
every date (anticipated from the infinite past). -/
noncomputable def stepZ (T t : ℤ) : ℝ := if T ≤ t then 1 else 0

/-- Cochrane (2023), eq. (5.5): `F_t = ∑_{k≥0} λ₂ᵏ i_{t+k}` for the ℤ-step, in closed form
`λ₂^{max(T−t,0)}/(1 − λ₂)`. -/
noncomputable def GZ (σ β κ : ℝ) (T t : ℤ) : ℝ :=
  lam2 σ β κ ^ (T - t).toNat / (1 - lam2 σ β κ)

/-- Cochrane (2023), Fig. 17.5, p. 409 (solid line): the response anticipated from the infinite
past, `π_t = c λ₂^{T−t+1}/(1 − λ₂)` for `t ≤ T` and
`π_t = 1 − (1 − c λ₂/(1 − λ₂)) λ₁^{−(t−T)}` for `t ≥ T`. -/
noncomputable def zPath (σ β κ : ℝ) (T t : ℤ) : ℝ :=
  if t ≤ T then coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ) * lam2 σ β κ ^ (T - t).toNat
  else 1 - (1 - coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ)) * (lam1 σ β κ)⁻¹ ^ (t - T).toNat

/-- The closed-form forward sum satisfies `G_t = i_t + λ₂ G_{t+1}`. -/
theorem GZ_rec {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℤ) :
    GZ σ β κ T t = stepZ T t + lam2 σ β κ * GZ σ β κ T (t + 1) := by
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith [lam2_lt_one ha hβ]
  unfold GZ stepZ
  split_ifs with h
  · rw [show (T - t).toNat = 0 by omega, show (T - (t + 1)).toNat = 0 by omega]
    field_simp
    ring
  · rw [show (T - t).toNat = (T - (t + 1)).toNat + 1 by omega, pow_succ]
    field_simp
    ring

/-- Cochrane (2023), eq. (5.5) on `ℤ`: the anticipated response satisfies the factored equation
`λ₁ π_{t+1} = π_t + σκ F_t` at every date. -/
theorem zPath_factor {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℤ) :
    lam1 σ β κ * zPath σ β κ T (t + 1) = zPath σ β κ T t + σ * κ * GZ σ β κ T t := by
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith
  have hc := coef_mul ha hβ
  have hsk := sigma_kappa_eq ha hβ
  have hll : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hsk' : σ * κ * (1 / (1 - lam2 σ β κ)) = lam1 σ β κ - 1 := by
    rw [hsk]; field_simp
  set K := coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ) with hK
  unfold zPath GZ
  rw [← hK]
  by_cases hA : t + 1 ≤ T
  · have hA' : t ≤ T := by omega
    simp only [hA, hA', ↓reduceIte]
    rw [show (T - t).toNat = (T - (t + 1)).toNat + 1 by omega, pow_succ, hK]
    field_simp
    linear_combination (lam2 σ β κ * lam2 σ β κ ^ (T - (t + 1)).toNat) * hc
  · by_cases hB : t = T
    · subst hB
      simp only [hA, le_refl, ↓reduceIte]
      rw [show (t + 1 - t).toNat = 1 by omega, sub_self, Int.toNat_zero, pow_one, pow_zero,
        mul_one, hsk']
      linear_combination (-(1 - K)) * hll
    · have hB' : ¬ t ≤ T := by omega
      simp only [hA, hB', ↓reduceIte]
      rw [show (t + 1 - T).toNat = (t - T).toNat + 1 by omega,
        show (T - t).toNat = 0 by omega, pow_succ, pow_zero, hsk']
      linear_combination (-(1 - K) * (lam1 σ β κ)⁻¹ ^ (t - T).toNat) * hll

/-- Cochrane (2023), Fig. 17.5, p. 409: the anticipated response is bounded. -/
theorem zPath_bounded {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    BoundedZ (zPath σ β κ T) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (one_pos.trans hl1).le
  have hμ1 : (lam1 σ β κ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hl1).le
  set K := coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ)
  refine ⟨|K| + 1 + |1 - K|, fun t => ?_⟩
  unfold zPath
  split_ifs
  · rw [abs_mul, abs_pow, abs_of_pos h2]
    have : lam2 σ β κ ^ (T - t).toNat ≤ 1 := pow_le_one₀ h2.le h21.le
    have := abs_nonneg K
    have := abs_nonneg (1 - K)
    nlinarith
  · refine (abs_sub _ _).trans ?_
    rw [abs_one, abs_mul, abs_pow, abs_of_nonneg hμ0]
    have : (lam1 σ β κ)⁻¹ ^ (t - T).toNat ≤ 1 := pow_le_one₀ hμ0 hμ1
    have := abs_nonneg K
    have := abs_nonneg (1 - K)
    nlinarith

/-- Cochrane (2023), Fig. 17.5, p. 409: the anticipated response solves (17.18) at every date of
`ℤ`. -/
theorem zPath_second {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    SecondZ σ β κ (stepZ T) (zPath σ β κ T) := by
  intro t
  have e1 := zPath_factor ha hβ T t
  have e2 := zPath_factor ha hβ T (t + 1)
  have f := GZ_rec ha hβ T t
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  rw [show t + 1 + 1 = t + 2 by ring] at e2
  linear_combination zPath σ β κ T (t + 1) * h1 - zPath σ β κ T (t + 2) * h2 - e1 +
    lam2 σ β κ * e2 - (σ * κ) * f

/-- Cochrane (2023), p. 408 and eq. (5.5) on `ℤ`: for any bounded interest-rate path there is
at most one bounded perfect-foresight inflation path on the whole line — with an infinite past
there is no free initial condition. -/
theorem secondZ_unique {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π π' : ℤ → ℝ}
    (hπ : SecondZ σ β κ i π) (hπ' : SecondZ σ β κ i π') (hb : BoundedZ π)
    (hb' : BoundedZ π') : π = π' := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hb'
  set d : ℤ → ℝ := fun t => π t - π' t with hd
  have hdb : ∀ t, |d t| ≤ M + M' := fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  -- `w_t = d_t − λ₁ d_{t+1}` satisfies `w_t = λ₂ w_{t+1}`
  set w : ℤ → ℝ := fun t => d t - lam1 σ β κ * d (t + 1) with hw
  have hwrec : ∀ t, w t = lam2 σ β κ * w (t + 1) := fun t => by
    have a := hπ t
    have b := hπ' t
    simp only [hw, hd, show t + 1 + 1 = t + 2 by ring]
    linear_combination a - b - (π (t + 1) - π' (t + 1)) * h1 + (π (t + 2) - π' (t + 2)) * h2
  have hwb : ∀ t, |w t| ≤ M + M' + lam1 σ β κ * (M + M') := fun t => by
    refine (abs_sub _ _).trans (add_le_add (hdb t) ?_)
    rw [abs_mul, abs_of_pos hl0]
    exact mul_le_mul_of_nonneg_left (hdb (t + 1)) hl0.le
  -- `w` read backwards is a bounded solution of a stable recursion on `ℤ`, hence zero
  have hq2 : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg h20]; exact h21
  have hwz := int_homog_zero hq2 (x := fun s => w (-s)) (fun s => hwb (-s)) (fun s => by
    rw [hwrec (-(s + 1)), show -(s + 1) + 1 = -s by ring])
  have hw0 : ∀ t, w t = 0 := fun t => by simpa using congrFun hwz (-t)
  -- then `d_{t+1} = λ₁⁻¹ d_t`, again a bounded solution of a stable recursion on `ℤ`
  have hdrec : ∀ s, d (s + 1) = (lam1 σ β κ)⁻¹ * d s := fun s => by
    have := hw0 s
    simp only [hw] at this
    field_simp
    linarith
  have hq : |(lam1 σ β κ)⁻¹| < 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hl0.le)]; exact inv_lt_one_of_one_lt₀ hl1
  have hd0 := int_homog_zero hq hdb hdrec
  funext t
  have := congrFun hd0 t
  simp only [hd, Pi.zero_apply] at this
  linarith

/-- Cochrane (2023), Fig. 17.5, p. 409: for the permanent rise at date `T` anticipated from the
infinite past there is exactly one bounded perfect-foresight inflation path on `ℤ`, `zPath`. -/
theorem zPath_existsUnique {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    ∃! π : ℤ → ℝ, BoundedZ π ∧ SecondZ σ β κ (stepZ T) π :=
  ⟨zPath σ β κ T, ⟨zPath_bounded ha hβ T, zPath_second ha hβ T⟩,
    fun _ ⟨hb, hs⟩ => secondZ_unique ha hβ hs (zPath_second ha hβ T) hb (zPath_bounded ha hβ T)⟩

/-- The anticipated response depends only on the distance to the rise: shifting the rise date
and the date by `N` leaves it unchanged. -/
theorem zPath_shift (σ β κ : ℝ) (T t N : ℤ) :
    zPath σ β κ (T + N) (t + N) = zPath σ β κ T t := by
  unfold zPath
  rw [show T + N - (t + N) = T - t by ring, show t + N - (T + N) = t - T by ring]
  simp only [add_le_add_iff_right]

/-- Cochrane (2023), Fig. 17.5, pp. 409–410: the ℕ-indexed no-surprise response to the rise at
date `T` announced at date 0 (`antPath`, the two-sided moving average (5.5) with `δ = 0`)
coincides at every date `s ≥ 0` with the response anticipated from the infinite past. -/
theorem zPath_eq_antPath {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T s : ℕ) :
    zPath σ β κ T s = antPath σ β κ T s := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith
  induction s with
  | zero =>
    rw [(antPath_zero_pos ha hβ T).1]
    unfold zPath
    have h0 : ((0 : ℕ) : ℤ) ≤ (T : ℤ) := by omega
    simp only [h0, ↓reduceIte]
    rw [show ((T : ℤ) - ((0 : ℕ) : ℤ)).toNat = T by omega, pow_succ]
    field_simp
  | succ s ih =>
    apply mul_left_cancel₀ hl0
    have e1 := zPath_factor ha hβ (T : ℤ) (s : ℤ)
    have e2 : lam1 σ β κ * antPath σ β κ T (s + 1) =
        antPath σ β κ T s + σ * κ * F (lam2 σ β κ) (stepI T) s := path_factor ha hβ _ _ _
    rw [show ((s + 1 : ℕ) : ℤ) = (s : ℤ) + 1 by push_cast; ring, e1, e2, ih,
      F_step h2.le h21]
    unfold GZ
    rw [show ((T : ℤ) - (s : ℤ)).toNat = T - s by omega]

/-- Cochrane (2023), Fig. 17.5: with the announcement at date `−N` (rise at date `T ≥ 0`), the
no-surprise response coincides after the announcement with the response anticipated from the
infinite past: `antPath (T + N) s = zPath T (s − N)`. -/
theorem antPath_eq_zPath_shift {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T N s : ℕ) :
    antPath σ β κ (T + N) s = zPath σ β κ T ((s : ℤ) - N) := by
  rw [← zPath_eq_antPath ha hβ, ← zPath_shift σ β κ T ((s : ℤ) - N) N]
  push_cast
  ring_nf

/-- Two paths for the same rate path differ by `(p − q) λ₁^{−n}`. -/
theorem path_sub_path (σ β κ : ℝ) (i : ℕ → ℝ) (p q : ℝ)
    (n : ℕ) : path σ β κ i p n - path σ β κ i q n = (p - q) * (lam1 σ β κ)⁻¹ ^ n := by
  induction n with
  | zero => simp [path]
  | succ n ih =>
    simp only [path]
    rw [pow_succ, ← mul_assoc, ← ih]
    ring

/-- Cochrane (2023), Fig. 17.5, p. 409: as the announcement recedes into the past, **every**
perfect-foresight response converges to the response anticipated from the infinite past. With
the announcement at date `−N`, a rise at date `T` and any initial jump `p` at the announcement,
inflation at a fixed date `t ∈ ℤ` tends to `zPath T t` as `N → ∞`. -/
theorem tendsto_zPath {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) (p : ℝ) (t : ℤ) :
    Tendsto (fun N : ℕ => path σ β κ (stepI (T + N)) p (t + N).toNat) atTop
      (𝓝 (zPath σ β κ T t)) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (one_pos.trans hl1).le
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  -- the jump of the no-surprise response at the announcement vanishes
  have ha0 : Tendsto (fun N : ℕ => antPath σ β κ (T + N) 0) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => coef σ β κ * lam2 σ β κ ^ (T + N + 1) / (1 - lam2 σ β κ))
        atTop (𝓝 (coef σ β κ * 0 / (1 - lam2 σ β κ))) :=
      (((tendsto_pow_atTop_nhds_zero_of_lt_one h2.le h21).comp
        (tendsto_add_atTop_nat (T + 1))).const_mul _).div_const _ |>.congr fun N => by
          simp only [Function.comp_apply]
          ring_nf
    rw [mul_zero, zero_div] at this
    exact this.congr fun N => ((antPath_zero_pos ha hβ (T + N)).1).symm
  have hn : Tendsto (fun N : ℕ => (t + N).toNat) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + (-t).toNat, fun N hN => by omega⟩
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hn
  have hlim := ((tendsto_const_nhds (x := p)).sub ha0).mul hpow
  rw [mul_zero] at hlim
  have h := hlim.const_add (zPath σ β κ T t)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (-t).toNat] with N hN
  have hs := path_sub_path σ β κ (stepI (T + N)) p (antPath σ β κ (T + N) 0) (t + N).toNat
  have he := antPath_eq_zPath_shift ha hβ T N (t + N).toNat
  rw [show (((t + N).toNat : ℕ) : ℤ) - (N : ℤ) = t by omega] at he
  have hd : path σ β κ (stepI (T + N)) (antPath σ β κ (T + N) 0) (t + N).toNat =
      antPath σ β κ (T + N) (t + N).toNat := rfl
  rw [hd, he] at hs
  simp only [Function.comp_apply]
  linarith

end Cochrane.KeynesianStickyPrices.FullModel

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Persistence does not determine the sign of the inflation response

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.3.1, pp. 405–406
(eq. (17.14)), §17.4.1, p. 410, and §17.4.3, p. 416.

* (17.14): an inflation target and an interest-rate target are an equilibrium pair of the
  simple model iff `i*_t = (1 + 1/(σκ)) E_t π*_{t+1} − π*_t/(σκ)` (`eq_17_14`).
* The printed inverse of (17.14), `E_t π*_{t+1} = σκ/(1+σκ) ∑ (1+σκ)^{−j} i*_{t−j}`, omits past
  expectational errors (survey error **E8**, confirmed): the correct statement adds
  `∑_{j ≥ 1} (1+σκ)^{−j} δ_{t+1−j}` (`corrected_inverse`); the printed form holds iff the
  error term vanishes, e.g. with no past surprises (`printed_inverse_of_no_surprise`), and fails
  for the dashed equilibria of Figure 17.2 (`printed_inverse_false`).
* "Any value of unexpected inflation is consistent with any persistence of the interest-rate
  target": for every expectation system with a date-1 news shock `ε`, every bounded path `g` of
  the rate target and every `c`, there is a bounded equilibrium with `ΔE_1 π*_1 = c ε`
  (`any_sign`); under genuine uncertainty on the coin-flip tree (`any_sign_coin`); a permanent
  rise with a negative response (`permanent_negative`) and a one-period rise with a positive
  response (`transitory_positive`).
* "The long-run response of inflation to interest rates … is always positive": in every
  equilibrium in which the rate converges and expectational errors die out, inflation
  converges to the rate (`long_run_one`, using `SharedTools.tendsto_zero_of_stable`), in
  particular after an announcement (`any_sign_long_run`).
* The full model (17.18) under perfect foresight after the announcement (§17.4.1, p. 410;
  §17.4.3, p. 416), in the notation of `FullModel` (`FullModel.Second`, `FullModel.path`): for
  every bounded rate path and every value `c` of announcement-date inflation there is exactly
  one bounded equilibrium (`full_any_sign`), namely `FullModel.path` with `π_0 = c`, and
  inflation converges to the rate in the long run (`full_long_run`). The stable root of the
  dynamics is the open-mouth persistence: `η* = 1/λ₁` (`etaStar_eq_inv_lam1`), and the unstable
  root of `βλ² − (1+β+σκ)λ + 1` is `1/λ₂ > 1` (`etaStar_mul_inv_lam2`, `one_lt_inv_lam2`).
-/

namespace Cochrane.KeynesianStickyPrices.PersistenceFreedom

open Filter Topology StaticIS AR1Responses
open SharedTools (tendsto_zero_of_stable tendsto_of_stable_avg eq_backward_series)

variable {Ω : Type*}

/-! ### (17.14) and its inverse -/

/-- Cochrane (2023), eq. (17.14), p. 405: a target pair `(i*, π*)` is an equilibrium of the
simple model (17.7) iff `i*_t = (1 + 1/(σκ)) E_t π*_{t+1} − π*_t/(σκ)`. -/
theorem eq_17_14 (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (hσκ : σ * κ ≠ 0)
    (istar πstar : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ istar πstar ↔ 𝔼.Adapted πstar ∧ ∀ t ω,
      istar t ω = (1 + 1 / (σ * κ)) * 𝔼.E t (πstar (t + 1)) ω - πstar t ω / (σ * κ) := by
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun ω => ?_)
  constructor
  · intro e; field_simp; linear_combination e
  · intro e; field_simp at e; linear_combination e

/-- Cochrane (2023), eq. (17.14), p. 405 (survey error E8, corrected inverse): on the integers
(an infinite past), if `e_t = E_t π_{t+1}` satisfies (17.7), `e_t = π_t/(1+σκ) + σκ/(1+σκ) i_t`,
and `e`, `π`, `i` are bounded, then with the expectational errors `δ_s = π_s − e_{s−1}`,
`e_t = σκ/(1+σκ) ∑_{j≥0} (1+σκ)^{−j} i_{t−j} + ∑_{j≥0} (1+σκ)^{−(j+1)} δ_{t−j}`. The
statement is pathwise (one history at a time). -/
theorem corrected_inverse {σ κ Me Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {e π i : ℤ → ℝ}
    (he : ∀ s, |e s| ≤ Me) (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi)
    (h : ∀ s, e s = 1 / (1 + σ * κ) * π s + σ * κ / (1 + σ * κ) * i s) (t : ℤ) :
    e t = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) +
      ∑' j : ℕ, (1 / (1 + σ * κ)) ^ (j + 1) * (π (t - j) - e (t - j - 1)) := by
  obtain ⟨ha0, ha1, hb0, -⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  have haa : |a| < 1 := by rw [abs_of_pos ha0]; exact ha1
  set w : ℤ → ℝ := fun s => b * i s + a * (π s - e (s - 1)) with hw
  have hwb : ∀ s, |w s| ≤ b * |Mi| + a * (|Mπ| + |Me|) := fun s => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos hb0]
      exact mul_le_mul_of_nonneg_left ((hi _).trans (le_abs_self _)) hb0.le
    · rw [abs_mul, abs_of_pos ha0]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_)) ha0.le
      · exact (hπ _).trans (le_abs_self _)
      · exact (he _).trans (le_abs_self _)
  have hrec : ∀ s, e (s + 1) = a * e s + w (s + 1) := fun s => by
    rw [h (s + 1), hw]; simp only [add_sub_cancel_right]; ring
  rw [eq_backward_series haa he hwb hrec t]
  have hg := summable_geometric_of_lt_one (abs_nonneg a) haa
  have hsi : Summable fun j : ℕ => a ^ j * i (t - j) :=
    Summable.of_norm_bounded (hg.mul_right Mi) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg (abs_nonneg a) j)
  have hsd : Summable fun j : ℕ => a ^ (j + 1) * (π (t - j) - e (t - j - 1)) :=
    Summable.of_norm_bounded ((hg.mul_left |a|).mul_right (Mπ + Me)) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, pow_succ, mul_comm (|a| ^ j) |a|]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hπ _) (he _)))
        (by positivity)
  rw [← tsum_mul_left, ← (hsi.mul_left b).tsum_add hsd]
  refine tsum_congr fun j => ?_
  rw [hw]
  ring

/-- Cochrane (2023), eq. (17.14), p. 405: the printed inverse
`E_t π*_{t+1} = σκ/(1+σκ) ∑ (1+σκ)^{−j} i*_{t−j}` holds when there have been no expectational
errors up to date `t` (`π_s = E_{s−1} π_s` for `s ≤ t`). -/
theorem printed_inverse_of_no_surprise {σ κ Me Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {e π i : ℤ → ℝ}
    (he : ∀ s, |e s| ≤ Me) (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi)
    (h : ∀ s, e s = 1 / (1 + σ * κ) * π s + σ * κ / (1 + σ * κ) * i s) {t : ℤ}
    (hns : ∀ s ≤ t, π s = e (s - 1)) :
    e t = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) := by
  rw [corrected_inverse hσκ he hπ hi h t]
  have : ∀ j : ℕ, (1 / (1 + σ * κ)) ^ (j + 1) * (π (t - j) - e (t - j - 1)) = 0 := fun j => by
    rw [hns (t - j) (by omega), sub_self, mul_zero]
  rw [tsum_congr this, tsum_zero, add_zero]

/-- Cochrane (2023), eq. (17.14), p. 405, survey error E8: the printed inverse is false in
general. With `σκ = 1` (so the coefficient is `1/2`), `i* = 0` and a single unexpected
inflation `δ_1 = 1` (the dashed lines of Figure 17.2), `e_t = E_t π_{t+1}` and `π` satisfy
(17.7), all are bounded, yet `e_1 = 1/2` while the printed formula gives 0. -/
theorem printed_inverse_false :
    ∃ e π i : ℤ → ℝ, (∀ s, |e s| ≤ 1) ∧ (∀ s, |π s| ≤ 1) ∧ (∀ s, |i s| ≤ 1) ∧
      (∀ s, e s = 1 / (1 + 1) * π s + 1 / (1 + 1) * i s) ∧
      e 1 ≠ 1 / (1 + 1) * ∑' j : ℕ, (1 / (1 + 1 : ℝ)) ^ j * i (1 - j) := by
  refine ⟨fun s => if 0 < s then (1 / 2 : ℝ) ^ s.toNat else 0,
    fun s => if 0 < s then (1 / 2 : ℝ) ^ (s.toNat - 1) else 0, fun _ => 0,
    fun s => ?_, fun s => ?_, fun s => by simp, fun s => ?_, ?_⟩
  · dsimp only
    split_ifs
    · rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp
  · dsimp only
    split_ifs
    · rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp
  · dsimp only
    split_ifs with hs
    · have hn : s.toNat = s.toNat - 1 + 1 := by omega
      rw [hn, pow_succ, Nat.add_sub_cancel]
      ring
    · simp
  · simp

/-! ### Any persistence with any sign (§17.3.1, p. 405) -/

/-- Cochrane (2023), p. 405: the inflation response (per unit of the date-1 news shock) after an
announcement at date 1: `p_0 = 0`, announcement-date inflation `p_1 = c`, and thereafter
`p_{t+1} = p_t/(1+σκ) + σκ/(1+σκ) g_t`. -/
noncomputable def targetPath (σ κ : ℝ) (g : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => c
  | t + 2 => 1 / (1 + σ * κ) * targetPath σ κ g c (t + 1) + σ * κ / (1 + σ * κ) * g (t + 1)

/-- Cochrane (2023), p. 405: the interest-rate target `i*_t = g_t ε` for `t ≥ 1` (zero before
the news). -/
noncomputable def shockRate (g : ℕ → ℝ) (ε : Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (if t = 0 then 0 else g t) * ε ω

/-- Cochrane (2023), p. 405: the inflation target `π*_t = p_t ε`. -/
noncomputable def shockInfl (p : ℕ → ℝ) (ε : Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => p t * ε ω

/-- Cochrane (2023), p. 405: the response path is bounded when `g` is. -/
theorem targetPath_bounded {σ κ M : ℝ} (hσκ : 0 < σ * κ) {g : ℕ → ℝ} (hg : ∀ t, |g t| ≤ M)
    (c : ℝ) : ∀ t, |targetPath σ κ g c t| ≤ |c| + |M| / (1 - 1 / (1 + σ * κ)) := by
  obtain ⟨ha0, ha1, hb0, hab⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  set K := |c| + |M| / (1 - a) with hK
  have h1a : 0 < 1 - a := by linarith
  have hKa : (1 - a) * K = (1 - a) * |c| + |M| := by rw [hK]; field_simp
  have hK0 : |c| ≤ K := by have : 0 ≤ |M| / (1 - a) := by positivity
                           linarith
  have hstep : ∀ x : ℝ, |x| ≤ K → ∀ t, |a * x + b * g t| ≤ K := fun x hx t => by
    have e1 : |a * x| ≤ a * K := by
      rw [abs_mul, abs_of_pos ha0]; exact mul_le_mul_of_nonneg_left hx ha0.le
    have e2 : |b * g t| ≤ |M| := by
      rw [abs_mul, abs_of_pos hb0]
      calc b * |g t| ≤ 1 * |g t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ ≤ |M| := by rw [one_mul]; exact (hg t).trans (le_abs_self _)
    have hc : 0 ≤ (1 - a) * |c| := mul_nonneg h1a.le (abs_nonneg _)
    linarith [abs_add_le (a * x) (b * g t)]
  have key : ∀ t, |targetPath σ κ g c t| ≤ K ∧ |targetPath σ κ g c (t + 1)| ≤ K := by
    intro t
    induction t with
    | zero => exact ⟨by simp only [targetPath, abs_zero]; positivity, hK0⟩
    | succ t ih => exact ⟨ih.2, hstep _ ih.2 (t + 1)⟩
  exact fun t => (key t).1

/-- Cochrane (2023), p. 405, "Any value of unexpected inflation is consistent with any
persistence of the interest-rate target": let `ε` be news revealed at date 1 (`E_0 ε = 0`,
`E_1 ε = ε`). For every bounded target path `g` (any persistence) and every `c`, the pair
`i*_t = g_t ε` (`t ≥ 1`), `π*_t = p_t ε` is a bounded equilibrium of (17.7) — so (17.14) holds —
with unexpected inflation `ΔE_1 π*_1 = π*_1 − E_0 π*_1 = c ε`. -/
theorem any_sign (𝔼 : ExpectationSystem Ω) {σ κ Mg Mε : ℝ} (hσκ : 0 < σ * κ) {ε : Ω → ℝ}
    (hε0 : 𝔼.E 0 ε = 0) (hε1 : 𝔼.E 1 ε = ε) (hεb : ∀ ω, |ε ω| ≤ Mε) {g : ℕ → ℝ}
    (hg : ∀ t, |g t| ≤ Mg) (c : ℝ) :
    REModel 𝔼 σ κ (shockRate g ε) (shockInfl (targetPath σ κ g c) ε) ∧
      BoundedProc (shockInfl (targetPath σ κ g c) ε) ∧
      BoundedProc (shockRate g ε) ∧
      shockInfl (targetPath σ κ g c) ε 1 - 𝔼.E 0 (shockInfl (targetPath σ κ g c) ε 1) =
        c • ε := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have hεt : ∀ t, 1 ≤ t → 𝔼.E t ε = ε := fun t ht => by
    rw [← hε1, 𝔼.known ht]
  have hEs : ∀ t (q : ℝ), 𝔼.E t (fun ω => q * ε ω) = fun ω => q * 𝔼.E t ε ω := fun t q => by
    have := 𝔼.E_smul t q ε
    exact this
  set p := targetPath σ κ g c
  refine ⟨⟨fun t => ?_, fun t ω => ?_⟩,
    ⟨(|c| + |Mg| / (1 - 1 / (1 + σ * κ))) * Mε, fun t ω => ?_⟩, ⟨|Mg| * Mε, fun t ω => ?_⟩, ?_⟩
  · cases t with
    | zero =>
      change 𝔼.E 0 (fun ω => p 0 * ε ω) = fun ω => p 0 * ε ω
      rw [hEs]; simp [p, targetPath]
    | succ t =>
      change 𝔼.E (t + 1) (fun ω => p (t + 1) * ε ω) = fun ω => p (t + 1) * ε ω
      rw [hEs, hεt (t + 1) (Nat.le_add_left 1 t)]
  · change p t * ε ω = -(σ * κ) * ((if t = 0 then 0 else g t) * ε ω) +
      (1 + σ * κ) * 𝔼.E t (fun ω => p (t + 1) * ε ω) ω
    rw [hEs]
    cases t with
    | zero => simp [p, targetPath, hε0]
    | succ t =>
      rw [hεt (t + 1) (Nat.le_add_left 1 t)]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, p, targetPath]
      field_simp
      ring
  · rw [show shockInfl p ε t ω = p t * ε ω from rfl, abs_mul]
    exact mul_le_mul (targetPath_bounded hσκ hg c t) (hεb ω) (abs_nonneg _)
      ((abs_nonneg _).trans (targetPath_bounded hσκ hg c t))
  · rw [show shockRate g ε t ω = (if t = 0 then 0 else g t) * ε ω from rfl, abs_mul]
    refine mul_le_mul ?_ (hεb ω) (abs_nonneg _) (abs_nonneg Mg)
    split_ifs
    · simp
    · exact (hg t).trans (le_abs_self _)
  · funext ω
    change p 1 * ε ω - 𝔼.E 0 (fun ω => p 1 * ε ω) ω = c * ε ω
    rw [hEs, hε0]
    simp [p, targetPath]

/-- Cochrane (2023), p. 406, "The long-run response of inflation to interest rates in this model
is always positive": after the announcement, if the rate target converges, `g_t → ḡ`, the
inflation response converges to `ḡ`, whatever the announcement-date jump `c`. -/
theorem any_sign_long_run {σ κ gb : ℝ} (hσκ : 0 < σ * κ) {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 gb)) (c : ℝ) :
    Tendsto (targetPath σ κ g c) atTop (𝓝 gb) := by
  obtain ⟨ha0, ha1, -, hab⟩ := coeff_17_7 hσκ
  have haa : |1 / (1 + σ * κ)| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have := tendsto_of_stable_avg haa hab (x := fun n => targetPath σ κ g c (n + 1))
    (y := fun n => g (n + 1)) (fun n => rfl) ((tendsto_add_atTop_iff_nat 1).mpr hg)
  exact (tendsto_add_atTop_iff_nat 1).mp this

/-- Cochrane (2023), p. 405 and Figure 17.2 ("a permanent `i*_t` shock can come with a negative
`π*_t` response"): a permanent rise `g ≡ 1` with `c = −1`: inflation falls on announcement and
then rises to the new rate. -/
theorem permanent_negative {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    targetPath σ κ (fun _ => 1) (-1) 1 < 0 ∧
      Tendsto (targetPath σ κ (fun _ => 1) (-1)) atTop (𝓝 1) :=
  ⟨by simp [targetPath], any_sign_long_run hσκ tendsto_const_nhds (-1)⟩

/-- Cochrane (2023), p. 405 ("Contrary examples, with transitory interest rates … and positive
inflation responses are just as easy to construct"): a one-period rate rise (`g_1 = 1`, zero
otherwise) with `c = 1`, a positive inflation response that dies out. -/
theorem transitory_positive {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    0 < targetPath σ κ (fun t => if t = 1 then 1 else 0) 1 1 ∧
      Tendsto (targetPath σ κ (fun t => if t = 1 then 1 else 0) 1) atTop (𝓝 0) := by
  refine ⟨by simp [targetPath], any_sign_long_run hσκ ?_ 1⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  simp [ht.ne']

/-- Cochrane (2023), p. 405, under genuine uncertainty: on the coin-flip tree (news revealed by
the first flip at date 1) every bounded persistence pattern `g` of the rate target is compatible
with every value `c` of unexpected inflation on the announcement date (per unit of the shock,
which is `+1` in the heads state). -/
theorem any_sign_coin {σ κ Mg : ℝ} (hσκ : 0 < σ * κ) {g : ℕ → ℝ} (hg : ∀ t, |g t| ≤ Mg)
    (c : ℝ) :
    ∃ istar πstar : ℕ → Bool × Bool → ℝ,
      REModel ExpectationsFiniteTree.coinSystem σ κ istar πstar ∧ BoundedProc πstar ∧
      BoundedProc istar ∧
      πstar 1 (true, true) - ExpectationsFiniteTree.coinSystem.E 0 (πstar 1) (true, true) = c ∧
      ∀ t, 1 ≤ t → istar t (true, true) = g t := by
  have hε : ExpectationsFiniteTree.coinShock 1 = ExpectationsFiniteTree.coinAR1 0 1 := by
    funext ω; simp [ExpectationsFiniteTree.coinAR1]
  have hε0 : ExpectationsFiniteTree.coinSystem.E 0 (ExpectationsFiniteTree.coinShock 1) = 0 :=
    ExpectationsFiniteTree.coinShock_mean_zero 0
  have hε1 : ExpectationsFiniteTree.coinSystem.E 1 (ExpectationsFiniteTree.coinShock 1) =
      ExpectationsFiniteTree.coinShock 1 := by
    rw [hε]; exact (ExpectationsFiniteTree.coinAR1_isAR1 0).1 1
  have hεb : ∀ ω, |ExpectationsFiniteTree.coinShock 1 ω| ≤ 1 := fun ω => by
    unfold ExpectationsFiniteTree.coinShock; split_ifs <;> simp
  obtain ⟨hm, hb, hbi, hd⟩ := any_sign ExpectationsFiniteTree.coinSystem hσκ hε0 hε1 hεb hg c
  refine ⟨_, _, hm, hb, hbi, ?_, fun t ht => ?_⟩
  · have := congrFun hd (true, true)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]; simp [ExpectationsFiniteTree.coinShock]
  · simp [shockRate, ExpectationsFiniteTree.coinShock, show t ≠ 0 by omega]

/-- Cochrane (2023), p. 406, "A persistently high interest rate still drives inflation up
eventually in all equilibria of this model": in any equilibrium of (17.7), along any history in
which the rate converges to `ī` and the expectational errors die out, inflation converges to
`ī`. -/
theorem long_run_one {𝔼 : ExpectationSystem Ω} {σ κ ib : ℝ} (hσκ : 0 < σ * κ)
    {i π : ℕ → Ω → ℝ} (hπ : REModel 𝔼 σ κ i π) {ω : Ω}
    (hi : Tendsto (fun t => i t ω) atTop (𝓝 ib))
    (hδ : Tendsto (fun t => π (t + 1) ω - 𝔼.E t (π (t + 1)) ω) atTop (𝓝 0)) :
    Tendsto (fun t => π t ω) atTop (𝓝 ib) := by
  obtain ⟨ha0, ha1, -, hab⟩ := coeff_17_7 hσκ
  have haa : |1 / (1 + σ * κ)| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have h17 := ((reModel_iff_17_7 𝔼 (by linarith) i π).mp hπ).2
  have hf : Tendsto (fun t => σ * κ / (1 + σ * κ) * (i t ω - ib) +
      (π (t + 1) ω - 𝔼.E t (π (t + 1)) ω)) atTop (𝓝 0) := by
    simpa using ((hi.sub_const ib).const_mul (σ * κ / (1 + σ * κ))).add hδ
  have := tendsto_zero_of_stable haa (x := fun t => π t ω - ib) (fun t => by
    have e := h17 t ω
    linear_combination e + ib * hab) hf
  simpa using this.add_const ib

/-! ### The full model (17.18) under perfect foresight (§17.4.1, §17.4.3) -/

/-- Cochrane (2023), §17.4.3, p. 416 and eq. (5.6), p. 119: the open-mouth persistence is the
reciprocal of the larger root of `λ² − (1 + β + σκ)λ + β`, `η* = 1/λ₁`. -/
theorem etaStar_eq_inv_lam1 {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    etaStar σ κ β = (FullModel.lam1 σ β κ)⁻¹ := by
  have hs := Real.sq_sqrt (FullModel.disc_pos hσκ hβ0).le
  refine eq_inv_of_mul_eq_one_left ?_
  unfold etaStar FullModel.lam1
  set r := Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)
  field_simp
  linear_combination (-1 : ℝ) * hs

/-- Cochrane (2023), p. 408: the roots of `βλ² − (1 + β + σκ)λ + 1` are `η* = 1/λ₁` (stable)
and `1/λ₂` (unstable): `β η* λ₂⁻¹ = 1` and `β(η* + λ₂⁻¹) = 1 + β + σκ`. -/
theorem etaStar_mul_inv_lam2 {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    β * (etaStar σ κ β * (FullModel.lam2 σ β κ)⁻¹) = 1 ∧
      β * (etaStar σ κ β + (FullModel.lam2 σ β κ)⁻¹) = 1 + β + σ * κ := by
  have hp := FullModel.lam_prod hσκ hβ0
  have hs := FullModel.lam_sum σ β κ
  have h1 := (one_pos.trans (FullModel.one_lt_lam1 hσκ hβ0)).ne'
  have h2 := (FullModel.lam2_pos hσκ hβ0).ne'
  rw [etaStar_eq_inv_lam1 hσκ hβ0]
  set l1 := FullModel.lam1 σ β κ
  set l2 := FullModel.lam2 σ β κ
  constructor
  · calc β * (l1⁻¹ * l2⁻¹) = (l1 * l2) * (l1⁻¹ * l2⁻¹) := by rw [hp]
      _ = 1 := by field_simp
  · calc β * (l1⁻¹ + l2⁻¹) = (l1 * l2) * (l1⁻¹ + l2⁻¹) := by rw [hp]
      _ = l1 + l2 := by field_simp; ring
      _ = 1 + β + σ * κ := hs

/-- Cochrane (2023), p. 408: the unstable root `1/λ₂` exceeds one. -/
theorem one_lt_inv_lam2 {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    1 < (FullModel.lam2 σ β κ)⁻¹ :=
  (one_lt_inv₀ (FullModel.lam2_pos hσκ hβ0)).mpr (FullModel.lam2_lt_one hσκ hβ0)

/-- Cochrane (2023), §17.4.1, p. 410 and §17.4.3, p. 416, "there is no connection between the
persistence of the interest-rate shock and the sign of the inflation movement": in the full
model (17.18) under perfect foresight after the announcement (`FullModel.Second`), for every
bounded interest-rate path `i` (any persistence) and every announcement-date inflation `c` (any
sign) there is exactly one bounded equilibrium with `π_0 = c` — `FullModel.path σ β κ i c`
(`FullModel.pf_existsUnique`). -/
theorem full_any_sign {σ κ β M : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ n, |i n| ≤ M) (c : ℝ) :
    ∃! π : ℕ → ℝ, FullModel.Second σ β κ i π ∧ (∃ K, ∀ n, |π n| ≤ K) ∧ π 0 = c := by
  obtain ⟨π, ⟨hb, hs, h0⟩, hu⟩ := FullModel.pf_existsUnique hσκ hβ0 hi c
  exact ⟨π, ⟨hs, hb, h0⟩, fun π' ⟨hs', hb', h0'⟩ => hu π' ⟨hb', hs', h0'⟩⟩

/-- Cochrane (2023), §17.4.1, p. 408 (long-run response 1 in the full model): along the
equilibrium of `full_any_sign` (`FullModel.path`), if the rate converges, `i_n → ī`, inflation
converges to `ī`, whatever the announcement-date jump. -/
theorem full_long_run {σ κ β M ib : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ n, |i n| ≤ M) (hlim : Tendsto i atTop (𝓝 ib)) (c : ℝ) :
    Tendsto (FullModel.path σ β κ i c) atTop (𝓝 ib) :=
  FullModel.tendsto_pi hσκ hβ0 hi hlim (FullModel.path_bounded hσκ hβ0 hi c)
    ((FullModel.second_iff_factor hσκ hβ0 hi (FullModel.path_bounded hσκ hβ0 hi c)).mpr
      (FullModel.path_factor hσκ hβ0 i c))

end Cochrane.KeynesianStickyPrices.PersistenceFreedom

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Adaptive expectations with a Taylor rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.3.2 "Adaptive
expectations responses with policy rules", pp. 406–407, Figure 17.4.

With adaptive expectations, the rule `i_t = φπ_t + u_t` and an AR(1) disturbance
`u_t = η u_{t−1} + ε_t`, inflation follows the AR(2)
`(1 − (1+σκ)/(1+φσκ) L)(1 − ηL) π_t = −σκ/(1+φσκ) ε_t` (`ar2`).

Figure 17.4 (`η = 1`, a permanent disturbance from date 0, `π_{−1} = 0`):
`π_t = −(1 − cᵗ⁺¹)/(φ − 1)` with `c = (1+σκ)/(1+φσκ)` (`fig17_4_path`). For `φ > 1`
(`fig17_4_coeff`): the interest rate first rises (`fig17_4_i_zero`), inflation declines
(`fig17_4_infl_strictAnti`), the rate then falls (`fig17_4_i_strictAnti`) and reverses course
(`fig17_4_i_reverses`), and both converge to `−1/(φ − 1)` (`fig17_4_tendsto`): the disinflation is
stabilised. In general, for `φ > 1` bounded disturbances give bounded inflation and transitory
disturbances die out (`taylor_bounded`, `taylor_transitory`). If the interest rate cannot move,
inflation spirals (`peg_spiral`): a deflation spiral at the zero bound, an inflation spiral under a
too-low peg (Friedman).
-/

namespace Cochrane.KeynesianStickyPrices.AdaptiveTaylor

open Filter Topology StaticIS RulesAdaptiveRE PersistenceFreedom
open SharedTools (tendsto_zero_of_stable)

variable {Ω : Type*}

/-- Cochrane (2023), p. 406: with adaptive expectations, the rule and an AR(1) disturbance
`u_{t+1} = η u_t + ε_{t+1}`, inflation follows the AR(2)
`π_{t+2} − (c + η) π_{t+1} + cη π_t = −k ε_{t+2}`, with `c = (1+σκ)/(1+φσκ)` and
`k = σκ/(1+φσκ)`, i.e. `(1 − cL)(1 − ηL) π_t = −k ε_t`. -/
theorem ar2 {σ κ φ η : ℝ} (h : 1 + σ * κ * φ ≠ 0) {π0 : Ω → ℝ} {u ε π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 u π) (hu : ∀ t ω, u (t + 1) ω = η * u t ω + ε (t + 1) ω)
    (t : ℕ) (ω : Ω) :
    π (t + 2) ω - ((1 + σ * κ) / (1 + σ * κ * φ) + η) * π (t + 1) ω +
      (1 + σ * κ) / (1 + σ * κ * φ) * η * π t ω =
      -(σ * κ / (1 + σ * κ * φ)) * ε (t + 2) ω := by
  have e := (adaptiveRule_iff_17_10 h π0 u π).mp hπ
  have e1 := e (t + 1) ω
  have e2 := e (t + 2) ω
  simp only [lagged] at e1 e2
  have hu2 := hu (t + 1) ω
  rw [e2, e1, hu2]
  ring

/-- Cochrane (2023), p. 406: the first form of the AR(2),
`(1 − (1+σκ)/(1+φσκ) L) π_t = −σκ/(1+φσκ) u_t`, is (17.10). -/
theorem ar1_form {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) {π0 : Ω → ℝ} {u π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 u π) (t : ℕ) (ω : Ω) :
    π t ω - (1 + σ * κ) / (1 + σ * κ * φ) * lagged π0 π t ω =
      -(σ * κ / (1 + σ * κ * φ)) * u t ω := by
  rw [(adaptiveRule_iff_17_10 h π0 u π).mp hπ t ω]; ring

/-- Cochrane (2023), p. 406: for `φ > 1` (and `σκ > 0`) the coefficient on lagged inflation,
`c = (1+σκ)/(1+φσκ)`, lies in `(0, 1)`, and `σκ/(1+φσκ) = (1 − c)/(φ − 1)`. -/
theorem fig17_4_coeff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    0 < (1 + σ * κ) / (1 + σ * κ * φ) ∧ (1 + σ * κ) / (1 + σ * κ * φ) < 1 ∧
      σ * κ / (1 + σ * κ * φ) = (1 - (1 + σ * κ) / (1 + σ * κ * φ)) / (φ - 1) := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  refine ⟨by positivity, by rw [div_lt_one hM]; nlinarith, ?_⟩
  field_simp
  ring

/-- Cochrane (2023), Figure 17.4, p. 407: the response to a permanent disturbance (`η = 1`,
`u_t = 1` from date 0, `π_{−1} = 0`) is `π_t = −(1 − cᵗ⁺¹)/(φ − 1)`. -/
theorem fig17_4_path {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ (fun _ => 0) (fun _ _ => 1) π) (t : ℕ) (ω : Ω) :
    π t ω = -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1) := by
  have hM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  have e := (adaptiveRule_iff_17_10 hM _ _ π).mp hπ
  obtain ⟨-, -, hk⟩ := fig17_4_coeff hσκ hφ
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  have hφ1 : φ - 1 ≠ 0 := by linarith
  induction t with
  | zero => rw [e 0 ω]; simp only [lagged, hk]; field_simp; ring
  | succ t ih => rw [e (t + 1) ω]; simp only [lagged]; rw [ih, hk]; field_simp; ring

/-- Cochrane (2023), Figure 17.4: the interest rate along the response,
`i_t = φ π_t + 1 = 1 − φ (1 − cᵗ⁺¹)/(φ − 1)`. -/
noncomputable def fig17_4_rate (σ κ φ : ℝ) (t : ℕ) : ℝ :=
  φ * (-(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1)) + 1

/-- Cochrane (2023), p. 406, "interest rates rise": on impact `i_0 = 1/(1 + φσκ) > 0`. -/
theorem fig17_4_i_zero {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    fig17_4_rate σ κ φ 0 = 1 / (1 + σ * κ * φ) ∧ 0 < fig17_4_rate σ κ φ 0 := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  obtain ⟨-, -, hk⟩ := fig17_4_coeff hσκ hφ
  have e : fig17_4_rate σ κ φ 0 = 1 / (1 + σ * κ * φ) := by
    unfold fig17_4_rate
    rw [zero_add, pow_one, neg_div, ← hk]
    set M := 1 + σ * κ * φ with hMdef
    have hM0 : M ≠ 0 := hM.ne'
    field_simp
    rw [hMdef]
    ring
  exact ⟨e, by rw [e]; positivity⟩

/-- Cochrane (2023), p. 406, "inflation declines": the inflation response is strictly
decreasing. -/
theorem fig17_4_infl_strictAnti {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    StrictAnti fun t : ℕ => -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1) := by
  obtain ⟨h0, h1, -⟩ := fig17_4_coeff hσκ hφ
  intro m n hmn
  have := pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega : m + 1 < n + 1)
  have hφ1 : 0 < φ - 1 := by linarith
  simp only
  rw [div_lt_div_iff_of_pos_right hφ1]
  linarith

/-- Cochrane (2023), p. 406, "interest rates then decline to catch and stabilize inflation":
the interest rate is strictly decreasing after its initial rise. -/
theorem fig17_4_i_strictAnti {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    StrictAnti (fig17_4_rate σ κ φ) := by
  intro m n hmn
  have := fig17_4_infl_strictAnti hσκ hφ hmn
  unfold fig17_4_rate
  have hφ0 : 0 < φ := by linarith
  nlinarith

/-- Cochrane (2023), Figure 17.4, p. 407: inflation and the interest rate converge to the same
long-run value `π_∞ = i_∞ = −1/(φ − 1)`: the disinflation is stabilised. -/
theorem fig17_4_tendsto {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    Tendsto (fun t : ℕ => -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1)) atTop
      (𝓝 (-1 / (φ - 1))) ∧
      Tendsto (fig17_4_rate σ κ φ) atTop (𝓝 (-1 / (φ - 1))) := by
  obtain ⟨h0, h1, -⟩ := fig17_4_coeff hσκ hφ
  have hp : Tendsto (fun t : ℕ => ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1)
  have hπ : Tendsto (fun t : ℕ => -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1))
      atTop (𝓝 (-1 / (φ - 1))) := by
    simpa using ((hp.const_sub 1).neg).div_const (φ - 1)
  refine ⟨hπ, ?_⟩
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hlim : φ * (-1 / (φ - 1)) + 1 = -1 / (φ - 1) := by field_simp; ring
  rw [← hlim]
  exact (hπ.const_mul φ).add_const 1

/-- Cochrane (2023), p. 406, "the actual interest rate quickly reverses course": the interest
rate, positive on impact, eventually becomes negative. -/
theorem fig17_4_i_reverses {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    0 < fig17_4_rate σ κ φ 0 ∧ ∃ T, ∀ t ≥ T, fig17_4_rate σ κ φ t < 0 := by
  refine ⟨(fig17_4_i_zero hσκ hφ).2, ?_⟩
  have hneg : -1 / (φ - 1) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
  exact eventually_atTop.mp ((fig17_4_tendsto hσκ hφ).2.eventually (gt_mem_nhds hneg))

/-- Cochrane (2023), p. 406, "the seal (the central bank) [moves] its nose more than one for one":
for `φ > 1` every bounded disturbance produces bounded inflation, from any initial
condition. -/
theorem taylor_bounded {σ κ φ B M : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π0 : Ω → ℝ}
    {u π : ℕ → Ω → ℝ} (hπ0 : ∀ ω, |π0 ω| ≤ B) (hu : ∀ t ω, |u t ω| ≤ M)
    (hπ : AdaptiveRule σ κ φ π0 u π) : BoundedProc π := by
  have hM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  exact adaptiveRule_bounded hM ((abs_coeff_lt_one_iff hσκ hM).mpr (Or.inl hφ)) hπ0 hu hπ

/-- Cochrane (2023), p. 406: for `φ > 1` a transitory disturbance (`u_t → 0` along a history)
leaves no lasting inflation: `π_t → 0`. -/
theorem taylor_transitory {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π0 : Ω → ℝ}
    {u π : ℕ → Ω → ℝ} (hπ : AdaptiveRule σ κ φ π0 u π) {ω : Ω}
    (hu : Tendsto (fun t => u t ω) atTop (𝓝 0)) : Tendsto (fun t => π t ω) atTop (𝓝 0) := by
  have hM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  have hc := (abs_coeff_lt_one_iff hσκ hM).mpr (Or.inl hφ)
  have e := (adaptiveRule_iff_17_10 hM π0 u π).mp hπ
  have hf : Tendsto (fun t => -(σ * κ / (1 + σ * κ * φ)) * u (t + 1) ω) atTop (𝓝 0) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).mpr hu).const_mul (-(σ * κ / (1 + σ * κ * φ)))
  exact tendsto_zero_of_stable hc (fun t => by rw [e (t + 1) ω]; simp only [lagged]; ring) hf

/-- Cochrane (2023), p. 406, "If interest rates hit the zero bound or cannot move, the model
predicts a deflation spiral" (and Friedman's too-low peg, an inflation spiral): with the rate
fixed at `ī`, inflation below `ī` falls without bound and inflation above `ī` rises without
bound. -/
theorem peg_spiral {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (ω : Ω) :
    (π0 ω < ib → Tendsto (fun t => π t ω) atTop atBot) ∧
      (ib < π0 ω → Tendsto (fun t => π t ω) atTop atTop) := by
  have he : (fun t => π t ω) = fun t => ib + (1 + σ * κ) ^ (t + 1) * (π0 ω - ib) :=
    funext fun t => adaptive_peg h t ω
  have hp : Tendsto (fun t : ℕ => (1 + σ * κ) ^ (t + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp (tendsto_add_atTop_nat 1)
  rw [he]
  refine ⟨fun hlt => ?_, fun hgt => ?_⟩
  · exact tendsto_atBot_add_const_left _ ib (hp.atTop_mul_const_of_neg (by linarith))
  · exact tendsto_atTop_add_const_left _ ib (hp.atTop_mul_const (by linarith))

end Cochrane.KeynesianStickyPrices.AdaptiveTaylor

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The fiscal underpinnings of new-Keynesian models

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4.2 "The fiscal
underpinnings of new-Keynesian models", eq. (17.19), pp. 411–415, with Figure 17.7.

## The unexpected-inflation identity (17.19)

With one-period debt the linearised flow condition is
`ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (`Flow`). For an arbitrary expectation system,
`innov t y = E_{t+1} y − E_t y` is the innovation `ΔE_{t+1}`. The finite-horizon identity
`innov_finite` is exact; under the transversality condition and summability it gives
(`eq_17_19`)

  `ΔE_{t+1} π_{t+1} = −∑_{j≥0} ρʲ ΔE_{t+1} s̃_{t+1+j} + ∑_{j≥0} ρʲ ΔE_{t+1} r_{t+1+j}`,

where `r_{t+1+j} = i_{t+j} − E_{t+j} π_{t+1+j}` is the (ex-ante) real rate **earned between
`t + j` and `t + 1 + j`**. With the dating of (17.16), `r_t = i_t − E_t π_{t+1}`, the real-rate
term carries an extra factor `ρ` (`eq_17_19_own_dating`); the printed sum is then right iff
`ρ = 1` or there is no real-rate news (`printed_own_dating_iff`). With the text's ex-post
`r_{t+1} = i_t − π_{t+1}` the `j = 0` term would be `−ΔE_{t+1} π_{t+1}` itself
(`expost_first_term`), so that reading is wrong. For bounded processes and `0 ≤ ρ < 1` the
innovation passes through the sums (`eq_17_19_bounded`), which is the printed form `ΔE Σ`.

Consequences (p. 411): "for higher interest rates to lower inflation, there must be a fiscal
contraction" (`fiscal_contraction`); at a 100% debt-to-GDP ratio surpluses must rise one
percentage point of GDP per point of unexpected disinflation (`surplus_gdp`).

## Figure 17.7 and the reverse-engineered disturbances (pp. 412–414)

Under perfect foresight after the shock, an interest-rate path `i` can be produced by a whole
family of disturbances `u = i − φ π` (`reverse_engineer`): one for every initial inflation. For
the AR(1) path `i_n = ηⁿ` the equilibrium is `π_n = c ηⁿ + (π₁ − c) μⁿ` with
`c = σκ/(−βη² + (1 + β + σκ)η − 1)`, `μ = 1/λ₁` (`piAR_eq_path`), and the surpluses required by
(17.19) with `ρ = 1` are `Σs = −π₁ + ∑_n (i_n − π_{n+1})` (`sigmaS_closed`). At the book's
parameters (`η = 0.6`, `σ = 1`, `κ = 0.25`, `β = 0.95`, `φ = 1.2`) this gives exactly the printed
3.55, 2.23, 0.91, −0.41, and 2.55 from real rates (`fig17_7_values`, `fig17_7_real_rates`); the
reverse-engineered disturbances are not AR(1) (`fig17_7_u_not_ar1`). Survey error E10 (p. 414):
`5 × 2.23 = 11.15`, not 11.5 (`e10`).

## Figure 17.6: `Δs` for equilibria A–E (p. 410)

With (17.19) and `ρ < 1`, after an unexpected permanent rise the equilibrium with initial
inflation `p` needs `Δs(p) = −p + ∑ ρʲ(1 − π_{j+1}) = (1 − p)/(λ₁ − ρ) − p` (`deltaS`,
`deltaS_closed`), the percentage change in steady-state surpluses (`permanent_surplus_pct`):
B has `Δs = −1` for all parameters (`deltaS_B`), D has `Δs = 1/(λ₁ − ρ)` (`deltaS_D`), C is
`p = 1/(1 + λ₁ − ρ)` (`deltaS_zero_iff`). The book does not state the parameters of Fig. 17.6,
so the printed numbers cannot be recomputed; but the affine form alone shows that, given the
printed D and `δ = 0` values, A and E cannot be the jumps `δ₁ = ±1%` (`fig17_6_inconsistent`);
they correspond to jumps of about `+0.83` and `−0.87` (`fig17_6_implied_jumps`).
-/

namespace Cochrane.KeynesianStickyPrices.FiscalUnderpinnings

open Filter Topology FullModel

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The unexpected-inflation identity -/

/-- Cochrane (2023), eq. (17.19), p. 411: the innovation `ΔE_{t+1} y = E_{t+1} y − E_t y`. -/
def innov (t : ℕ) (y : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) y - 𝔼.E t y

/-- Cochrane (2023), p. 411 (one-period debt; eq. (5.16), p. 121): the linearised flow
condition `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`. -/
def Flow (ρ : ℝ) (i s v π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t + i t - π (t + 1) - s (t + 1)

/-- Cochrane (2023), eq. (17.16), p. 407: the ex-ante real rate `r_n = i_n − E_n π_{n+1}`
(earned between `n` and `n + 1`). -/
def rea (i π : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := i n - 𝔼.E n (π (n + 1))

/-- The innovation is linear. -/
theorem innov_sub (t : ℕ) (a b : Ω → ℝ) : innov 𝔼 t (a - b) = innov 𝔼 t a - innov 𝔼 t b := by
  unfold innov
  rw [map_sub, map_sub]
  abel

/-- The innovation of a variable known at `t` is zero. -/
theorem innov_known {t s : ℕ} (hs : s ≤ t) {y : Ω → ℝ} (hy : 𝔼.E s y = y) : innov 𝔼 t y = 0 := by
  unfold innov
  rw [ForwardSolution.E_of_known 𝔼 (by omega) hy, ForwardSolution.E_of_known 𝔼 hs hy, sub_self]

/-- Cochrane (2023), p. 411: for `n ≥ t + 1`, the date-`(t+1)` news about the ex-post real
return `i_n − π_{n+1}` equals the news about the ex-ante rate `r_n`. -/
theorem innov_expost_eq {t n : ℕ} (hn : t + 1 ≤ n) (i π : ℕ → Ω → ℝ) :
    innov 𝔼 t (i n - π (n + 1)) = innov 𝔼 t (rea 𝔼 i π n) := by
  unfold innov rea
  simp only [map_sub, 𝔼.tower hn, 𝔼.tower (show t ≤ n by omega)]

/-- Cochrane (2023), p. 411: the `j = 0` term with the ex-post rate `r_{t+1} = i_t − π_{t+1}`
is `−ΔE_{t+1} π_{t+1}` (for adapted `i`), so (17.19) cannot be read with ex-post rates. -/
theorem expost_first_term (t : ℕ) {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (π : ℕ → Ω → ℝ) :
    innov 𝔼 t (i t - π (t + 1)) = -innov 𝔼 t (π (t + 1)) := by
  rw [innov_sub, innov_known 𝔼 le_rfl (hi t), zero_sub]

/-- The date-`t` ex-ante rate is known at `t`, so its innovation vanishes. -/
theorem innov_rea_self (t : ℕ) {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (π : ℕ → Ω → ℝ) :
    innov 𝔼 t (rea 𝔼 i π t) = 0 :=
  innov_known 𝔼 le_rfl (by unfold rea; rw [map_sub, hi t, 𝔼.E_E_self])

/-- Cochrane (2023), eq. (17.19), p. 411, finite horizon (exact): for adapted `v`, `i` and the
flow condition,
`ΔE_{t+1} π_{t+1} = −∑_{j≤N} ρʲ ΔE_{t+1} s̃_{t+1+j} + ∑_{j<N} ρ^{j+1} ΔE_{t+1} r_{t+1+j}
  − ρ^{N+1} ΔE_{t+1} v_{t+N+1}`. -/
theorem innov_finite {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v) (hi : 𝔼.Adapted i)
    (hf : Flow ρ i s v π) (t N : ℕ) (ω : Ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -∑ j ∈ Finset.range (N + 1), ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω +
        ∑ j ∈ Finset.range N, ρ ^ (j + 1) * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω -
        ρ ^ (N + 1) * innov 𝔼 t (v (t + N + 1)) ω := by
  -- the innovation of the flow condition at date `n`
  have hflow : ∀ n, ρ * innov 𝔼 t (v (n + 1)) ω =
      innov 𝔼 t (v n) ω + innov 𝔼 t (i n - π (n + 1)) ω - innov 𝔼 t (s (n + 1)) ω := by
    intro n
    have h := congrArg (innov 𝔼 t) (hf n)
    unfold innov at h ⊢
    simp only [map_smul, map_sub, map_add] at h ⊢
    have h' := congrFun h ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h' ⊢
    linear_combination h'
  induction N with
  | zero =>
    have h := hflow t
    rw [innov_known 𝔼 le_rfl (hv t), expost_first_term 𝔼 t hi] at h
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, Finset.range_zero,
      Finset.sum_empty, pow_one, add_zero, Pi.zero_apply, Pi.neg_apply] at h ⊢
    linear_combination h
  | succ N ih =>
    have h := hflow (t + N + 1)
    rw [innov_expost_eq 𝔼 (by omega)] at h
    rw [ih, Finset.sum_range_succ _ (N + 1),
      Finset.sum_range_succ (fun j => ρ ^ (j + 1) * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω) N,
      show t + 1 + (N + 1) = t + N + 1 + 1 by omega, show t + 1 + N = t + N + 1 by omega,
      show t + (N + 1) + 1 = t + N + 1 + 1 by omega]
    linear_combination ρ ^ (N + 1) * h


/-- Cochrane (2023), eq. (17.19), p. 411, corrected dating (with `ρ` placed explicitly): for
adapted `v`, `i`, the flow condition, the transversality condition
`ρᴺ ΔE_{t+1} v_{t+N} → 0` and summable news series,
`ΔE_{t+1} π_{t+1} = −∑ ρʲ ΔE_{t+1} s̃_{t+1+j} + ρ ∑ ρʲ ΔE_{t+1} r_{t+1+j}` with
`r_n = i_n − E_n π_{n+1}` dated as in (17.16). -/
theorem eq_17_19_own_dating {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hi : 𝔼.Adapted i) (hf : Flow ρ i s v π) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun N => ρ ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
    (hr : Summable fun j => ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω +
        ρ * ∑' j, ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω := by
  have h1 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      atTop (𝓝 (∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)) :=
    hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N => ∑ j ∈ Finset.range N,
      ρ ^ (j + 1) * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω) atTop
      (𝓝 (ρ * ∑' j, ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω)) := by
    refine (hr.hasSum.tendsto_sum_nat.const_mul ρ).congr fun N => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : Tendsto (fun N => ρ ^ (N + 1) * innov 𝔼 t (v (t + N + 1)) ω) atTop (𝓝 0) :=
    htvc.comp (tendsto_add_atTop_nat 1)
  have hlim := (h1.neg.add h2).sub h3
  rw [sub_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr fun N => ?_) hlim
  exact innov_finite 𝔼 hv hi hf t N ω

/-- Cochrane (2023), eq. (17.19), p. 411, **as printed**, with `r_{t+1+j}` read as the ex-ante
real rate earned between `t + j` and `t + 1 + j`, `i_{t+j} − E_{t+j} π_{t+1+j}`:
`ΔE_{t+1} π_{t+1} = −∑_{j≥0} ρʲ ΔE_{t+1} s̃_{t+1+j} + ∑_{j≥0} ρʲ ΔE_{t+1} r_{t+1+j}`. The
`j = 0` real-rate term is known at `t` and has no news. -/
theorem eq_17_19 {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hi : 𝔼.Adapted i) (hf : Flow ρ i s v π) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun N => ρ ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
    (hr : Summable fun j => ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + j)) ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω +
        ∑' j, ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + j)) ω := by
  have hr' : Summable fun j => ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω := by
    by_cases hρ : ρ = 0
    · simp [hρ, zero_pow_eq]
      exact (summable_nat_add_iff 1).mp (summable_of_ne_finset_zero (s := {0})
        (fun j hj => by simp at hj; simp [hj]))
    · have := ((summable_nat_add_iff 1).mpr hr).mul_left ρ⁻¹
      refine this.congr fun j => ?_
      rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
      field_simp
  rw [eq_17_19_own_dating 𝔼 hv hi hf t ω htvc hs hr', hr.tsum_eq_zero_add]
  rw [add_zero, innov_rea_self 𝔼 t hi, Pi.zero_apply, mul_zero, zero_add, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), eq. (17.19), p. 411: with the dating of (17.16), `r_n = i_n − E_n π_{n+1}`,
the printed formula (no factor `ρ` in front of the real-rate sum) holds iff `ρ = 1` or the
real-rate news is zero (here `S`, `R` stand for the two news sums of `eq_17_19_own_dating`). -/
theorem printed_own_dating_iff {ρ S R infl1 : ℝ} (h : infl1 = -S + ρ * R) :
    infl1 = -S + R ↔ ρ = 1 ∨ R = 0 := by
  rw [h]
  constructor
  · intro h'
    have : (ρ - 1) * R = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr h1
  · rintro (h1 | h1) <;> simp [h1]

/-- `ΔE_{t+1}` passes through a series dominated by a geometric series. -/
theorem innov_tsum {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ω, |f k ω| ≤ a ^ k * M) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (fun ω' => ∑' k, f k ω') ω = ∑' k, innov 𝔼 t (f k) ω := by
  have hg : Summable fun k : ℕ => a ^ k * M :=
    (summable_geometric_of_lt_one ha0 ha1).mul_right M
  have s1 : Summable fun k => 𝔼.E (t + 1) (f k) ω := Summable.of_norm_bounded hg
    (fun k => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) (t + 1) ω)
  have s2 : Summable fun k => 𝔼.E t (f k) ω := Summable.of_norm_bounded hg
    (fun k => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)
  unfold innov
  rw [Pi.sub_apply, 𝔼.E_tsum ha0 ha1 hf, 𝔼.E_tsum ha0 ha1 hf, ← s1.tsum_sub s2]
  rfl

/-- Cochrane (2023), eq. (17.19), p. 411, for bounded processes and `0 ≤ ρ < 1`, in the printed
form `ΔE_{t+1} π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j} + ΔE_{t+1} ∑ ρʲ r_{t+1+j}` (real rates earned
between `t + j` and `t + 1 + j`): transversality and summability are automatic. -/
theorem eq_17_19_bounded {ρ M : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {i s v π : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted v) (hi : 𝔼.Adapted i) (hf : Flow ρ i s v π)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hvb : ∀ t ω, |v t ω| ≤ M) (hib : ∀ t ω, |i t ω| ≤ M)
    (hπb : ∀ t ω, |π t ω| ≤ M) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -innov 𝔼 t (fun ω' => ∑' j, ρ ^ j * s (t + 1 + j) ω') ω +
        innov 𝔼 t (fun ω' => ∑' j, ρ ^ j * rea 𝔼 i π (t + j) ω') ω := by
  have hinb : ∀ (y : Ω → ℝ) (K : ℝ), (∀ ω, |y ω| ≤ K) → ∀ ω, |innov 𝔼 t y ω| ≤ 2 * K := by
    intro y K hy ω
    unfold innov
    rw [Pi.sub_apply, two_mul]
    exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le hy _ ω) (𝔼.abs_E_le hy _ ω))
  have hreab : ∀ n ω, |rea 𝔼 i π n ω| ≤ 2 * M := by
    intro n ω
    unfold rea
    rw [Pi.sub_apply, two_mul]
    exact (abs_sub _ _).trans (add_le_add (hib n ω) (𝔼.abs_E_le (hπb (n + 1)) n ω))
  have hgeo : Summable fun k : ℕ => ρ ^ k * (2 * (2 * M)) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_right _
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0 ω)
  have hsm : ∀ (y : ℕ → Ω → ℝ), (∀ n ω, |y n ω| ≤ 2 * M) →
      Summable fun j => ρ ^ j * innov 𝔼 t (y j) ω := by
    intro y hy
    refine Summable.of_norm_bounded hgeo (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (hinb _ _ (hy j) ω) (pow_nonneg hρ0 j)
  have hs2 : ∀ n ω, |s n ω| ≤ 2 * M := fun n ω => (hsb n ω).trans (by linarith)
  have htvc : Tendsto (fun N => ρ ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N => ρ ^ N * (2 * M)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (2 * M)
    refine squeeze_zero_norm (fun N => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (hinb _ _ (hvb (t + N)) ω) (pow_nonneg hρ0 N)
  rw [eq_17_19 𝔼 hv hi hf t ω htvc (hsm (fun j => s (t + 1 + j)) (fun n ω => hs2 _ ω))
    (hsm (fun j => rea 𝔼 i π (t + j)) (fun n ω => hreab _ ω))]
  rw [innov_tsum 𝔼 hρ0 hρ1 (f := fun j ω' => ρ ^ j * s (t + 1 + j) ω') (M := M)
      (fun k ω' => by rw [abs_mul, abs_pow, abs_of_nonneg hρ0]
                      exact mul_le_mul_of_nonneg_left (hsb _ ω') (pow_nonneg hρ0 k)) t ω,
    innov_tsum 𝔼 hρ0 hρ1 (f := fun j ω' => ρ ^ j * rea 𝔼 i π (t + j) ω') (M := 2 * M)
      (fun k ω' => by rw [abs_mul, abs_pow, abs_of_nonneg hρ0]
                      exact mul_le_mul_of_nonneg_left (hreab _ ω') (pow_nonneg hρ0 k)) t ω]
  have hc : ∀ (c : ℝ) (y : Ω → ℝ), innov 𝔼 t (fun ω' => c * y ω') ω = c * innov 𝔼 t y ω := by
    intro c y
    change innov 𝔼 t (c • y) ω = _
    unfold innov
    rw [map_smul, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hc]

/-- Cochrane (2023), p. 411 ("for higher interest rates to lower inflation, there must be a
fiscal contraction"): in (17.19), if unexpected inflation is negative and real-rate news is
nonnegative, news about the present value of surpluses is positive. -/
theorem fiscal_contraction {infl1 S R : ℝ} (h : infl1 = -S + R) (hinfl : infl1 < 0) (hR : 0 ≤ R) :
    0 < S := by linarith

/-- Cochrane (2023), pp. 411–412: since `s̃` is the surplus divided by the value of debt, the
surplus as a share of GDP is `(debt/GDP) · s̃`. With no real-rate news an unexpected
disinflation of `d` points needs surplus news of `(debt/GDP) · d` points of GDP: one for one at
100% debt-to-GDP, a quarter of that at 25% (1980). -/
theorem surplus_gdp {infl1 S debtGDP : ℝ} (h : infl1 = -S + 0) :
    debtGDP * S = debtGDP * (-infl1) ∧ (1 : ℝ) * S = -infl1 ∧ (1 / 4 : ℝ) * S = -infl1 / 4 := by
  refine ⟨by rw [h]; ring, by rw [h]; ring, by rw [h]; ring⟩

/-! ### Reverse-engineered disturbances (p. 414) -/

/-- Cochrane (2023), p. 414 ("I reverse-engineer a `{u_t}` disturbance to produce the same
interest-rate path and a chosen value of initial inflation"; perfect foresight): for every
bounded rate path `i`, every initial inflation `p` and every `φ`, the disturbance
`u = i − φ π` with `π = path p` makes `(x, π)` with `x_t = (π_t − β π_{t+1})/κ` an equilibrium
of the model with the rule `i_t = φ π_t + u_t`, with initial inflation `p`. Different `p` give
different inflation and (for `φ ≠ 0`) different disturbances, but the same interest rate. -/
theorem reverse_engineer {σ β κ M φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (p : ℝ) :
    let π := path σ β κ i p
    let u := fun t => i t - φ * π t
    (∀ t, i t = φ * π t + u t) ∧ π 0 = p ∧ BoundedS π ∧
      PFEqm σ β κ i (fun t => (π t - β * π (t + 1)) / κ) π := by
  have ha := mul_pos hσ hκ
  have hb := path_bounded ha hβ hi p
  refine ⟨fun t => by ring, rfl, hb, (pfEqm_iff_second hκ.ne' _ _ _).mpr ⟨fun t => rfl, ?_⟩⟩
  exact (second_iff_factor ha hβ hi hb).mpr (path_factor ha hβ i p)

/-- Cochrane (2023), p. 414: different initial inflations give different reverse-engineered
disturbances (for `φ ≠ 0`) producing the same interest-rate path. -/
theorem reverse_engineer_distinct {σ β κ φ p p' : ℝ} (hφ : φ ≠ 0) (hp : p ≠ p') (i : ℕ → ℝ) :
    (fun t => i t - φ * path σ β κ i p t) ≠ (fun t => i t - φ * path σ β κ i p' t) := by
  intro h
  have := congrFun h 0
  simp only [path] at this
  exact hp (mul_left_cancel₀ hφ (by linarith))


/-! ### Figure 17.7: an AR(1) interest-rate rise -/

/-- Cochrane (2023), Fig. 17.7, p. 413: the particular-solution coefficient
`c = σκ/(−βη² + (1 + β + σκ)η − 1)` of the response to `i_n = ηⁿ`. -/
noncomputable def cAR (σ β κ η : ℝ) : ℝ := σ * κ / (-β * η ^ 2 + (1 + β + σ * κ) * η - 1)

/-- Cochrane (2023), Fig. 17.7, p. 413 (dates `n = 0, 1, …` stand for the book's `1, 2, …`):
inflation `π_n = c ηⁿ + (π₁ − c) μⁿ`, `μ = 1/λ₁`, for the AR(1) path `i_n = ηⁿ` with initial
inflation `π₁ = p`. -/
noncomputable def piAR (σ β κ η p : ℝ) (n : ℕ) : ℝ :=
  cAR σ β κ η * η ^ n + (p - cAR σ β κ η) * (lam1 σ β κ)⁻¹ ^ n

/-- Cochrane (2023), Fig. 17.7: `π_n = c ηⁿ + (π₁ − c) μⁿ` solves (17.18) for `i_n = ηⁿ`. -/
theorem piAR_second {σ β κ η : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) (p : ℝ) :
    Second σ β κ (fun n => η ^ n) (piAR σ β κ η p) := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have hroot : 1 - (1 + β + σ * κ) * (lam1 σ β κ)⁻¹ + β * (lam1 σ β κ)⁻¹ ^ 2 = 0 := by
    have h1 := lam_sum σ β κ
    have h2 := lam_prod ha hβ
    have hr : lam1 σ β κ ^ 2 - (1 + β + σ * κ) * lam1 σ β κ + β = 0 := by
      linear_combination lam1 σ β κ * h1 - h2
    field_simp
    linear_combination hr
  have hc : cAR σ β κ η * (-β * η ^ 2 + (1 + β + σ * κ) * η - 1) = σ * κ := by
    unfold cAR; exact div_mul_cancel₀ _ hD
  intro n
  simp only [piAR, pow_succ]
  linear_combination (-(η ^ n)) * hc +
    (p - cAR σ β κ η) * (lam1 σ β κ)⁻¹ ^ n * hroot

/-- Cochrane (2023), p. 414 ("the inflation path is then determined by the solution (5.5) up to
an initial value"): for `0 ≤ η < 1`, `piAR p` is the unique bounded equilibrium path with
initial inflation `p`. -/
theorem piAR_eq_path {σ β κ η : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) (p : ℝ) :
    piAR σ β κ η p = path σ β κ (fun n => η ^ n) p := by
  have hi : ∀ n, |η ^ n| ≤ 1 := fun n => by
    rw [abs_of_nonneg (pow_nonneg hη0 n)]; exact pow_le_one₀ hη0 hη1.le
  have hl1 := one_lt_lam1 ha hβ
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (one_pos.trans hl1).le
  have hμ1 : (lam1 σ β κ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hl1).le
  obtain ⟨_, _, huniq⟩ := pf_existsUnique ha hβ hi p
  have hb : BoundedS (piAR σ β κ η p) := ⟨|cAR σ β κ η| + |p - cAR σ β κ η|, fun n => by
    unfold piAR
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_of_le_one_right (abs_nonneg _) (hi n)
    · rw [abs_of_nonneg (pow_nonneg hμ0 n)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hμ0 hμ1)⟩
  have hp : BoundedS (path σ β κ (fun n => η ^ n) p) := path_bounded ha hβ hi p
  rw [huniq _ ⟨hb, piAR_second ha hβ hD p, by simp [piAR]⟩,
    huniq _ ⟨hp, (second_iff_factor ha hβ hi hp).mpr (path_factor ha hβ _ p), rfl⟩]

/-- Cochrane (2023), p. 412 and Fig. 17.7: the cumulative surplus required by (17.19) with
`ρ = 1` (after a shock at date 1, pre-shock expectations at the steady state, perfect foresight
afterwards): `Σs = −π₁ + ∑_n (i_n − π_{n+1})` — the windfall plus the real interest costs. -/
noncomputable def sigmaS (σ β κ η p : ℝ) : ℝ :=
  -p + ∑' n, (η ^ n - piAR σ β κ η p (n + 1))

/-- Cochrane (2023), Fig. 17.7: closed form
`Σs = −π₁ + 1/(1 − η) − c η/(1 − η) − (π₁ − c)/(λ₁ − 1)`. -/
theorem sigmaS_closed {σ β κ η : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (p : ℝ) :
    sigmaS σ β κ η p = -p + 1 / (1 - η) - cAR σ β κ η * η / (1 - η) -
      (p - cAR σ β κ η) / (lam1 σ β κ - 1) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr hl0.le
  have hμ1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have g1 := hasSum_geometric_of_lt_one hη0 hη1
  have g2 := hasSum_geometric_of_lt_one hμ0 hμ1
  have hs : HasSum (fun n => η ^ n - piAR σ β κ η p (n + 1))
      ((1 - η)⁻¹ - (cAR σ β κ η * η * (1 - η)⁻¹ +
        (p - cAR σ β κ η) * (lam1 σ β κ)⁻¹ * (1 - (lam1 σ β κ)⁻¹)⁻¹)) := by
    refine g1.sub ((g1.mul_left (cAR σ β κ η * η)).add
      (g2.mul_left ((p - cAR σ β κ η) * (lam1 σ β κ)⁻¹))) |>.congr_fun ?_
    intro n
    simp only [piAR, pow_succ]
    ring
  unfold sigmaS
  rw [hs.tsum_eq]
  have h1 : 1 - η ≠ 0 := by linarith
  have h2 : lam1 σ β κ - 1 ≠ 0 := by linarith
  have h3 : 1 - (lam1 σ β κ)⁻¹ = (lam1 σ β κ - 1) / lam1 σ β κ := by field_simp
  rw [h3]
  field_simp
  ring

/-- Cochrane (2023), Fig. 17.7 (`σ = 1`, `κ = 0.25`, `β = 0.95`, `η = 0.6`): `c = −125/11`. -/
theorem fig17_7_c : cAR 1 (19 / 20) (1 / 4) (3 / 5) = -125 / 11 := by
  unfold cAR; norm_num

/-- Cochrane (2023), Fig. 17.7: `λ₁ = (2.2 + √1.04)/2`. -/
theorem fig17_7_lam1 : lam1 1 (19 / 20) (1 / 4) = (11 / 5 + Real.sqrt (26 / 25)) / 2 := by
  unfold lam1
  rw [show ((1 : ℝ) + 19 / 20 + 1 * (1 / 4)) ^ 2 - 4 * (19 / 20) = 26 / 25 by norm_num]
  norm_num

/-- Cochrane (2023), Fig. 17.7: `1.6099 < λ₁ < 1.609905`. -/
theorem fig17_7_lam1_bounds :
    (1.6099 : ℝ) < lam1 1 (19 / 20) (1 / 4) ∧ lam1 1 (19 / 20) (1 / 4) < 1.609905 := by
  rw [fig17_7_lam1]
  have h1 : (1.0198 : ℝ) < Real.sqrt (26 / 25) :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt (26 / 25) < (1.01981 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor <;> linarith

/-- The book's parameters satisfy `σκ > 0`, `β > 0`, `0 ≤ η < 1`. -/
theorem fig17_7_params :
    (0 : ℝ) < 1 * (1 / 4) ∧ (0 : ℝ) < 19 / 20 ∧ (0 : ℝ) ≤ 3 / 5 ∧ (3 / 5 : ℝ) < 1 := by
  norm_num

/-- Cochrane (2023), Fig. 17.7: `Σs` at the book's parameters, in terms of
`L = 1/(λ₁ − 1) ∈ (1.639599, 1.639614)`: `Σs = −π₁ + 5/2 + 375/22 − (π₁ + 125/11) L`. -/
theorem fig17_7_sigmaS (p : ℝ) :
    sigmaS 1 (19 / 20) (1 / 4) (3 / 5) p =
      -p + 5 / 2 + 375 / 22 - (p + 125 / 11) * (1 / (lam1 1 (19 / 20) (1 / 4) - 1)) := by
  obtain ⟨ha, hβ, hη0, hη1⟩ := fig17_7_params
  rw [sigmaS_closed ha hβ hη0 hη1, fig17_7_c]
  ring

/-- The bounds `1.639599 < 1/(λ₁ − 1) < 1.639614` at the book's parameters. -/
theorem fig17_7_L_bounds :
    (1.639599 : ℝ) < 1 / (lam1 1 (19 / 20) (1 / 4) - 1) ∧
      1 / (lam1 1 (19 / 20) (1 / 4) - 1) < 1.639614 := by
  obtain ⟨h1, h2⟩ := fig17_7_lam1_bounds
  have hp : 0 < lam1 1 (19 / 20) (1 / 4) - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- Cochrane (2023), Fig. 17.7, p. 413 (panel titles): with the same AR(1) interest-rate path,
initial inflation `π₁ = −1, −0.5, 0, 0.5` requires cumulative surpluses that round to
`Σs = 3.55, 2.23, 0.91, −0.41` percent of GDP (`ρ = 1`, 100% debt-to-GDP). -/
theorem fig17_7_values :
    (3.545 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) < 3.555) ∧
    (2.225 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1 / 2) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1 / 2) < 2.235) ∧
    (0.905 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) 0 ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) 0 < 0.915) ∧
    (-0.415 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (1 / 2) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (1 / 2) < -0.405) := by
  obtain ⟨h1, h2⟩ := fig17_7_L_bounds
  simp only [fig17_7_sigmaS]
  generalize 1 / (lam1 1 (19 / 20) (1 / 4) - 1) = L at h1 h2 ⊢
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num <;> linarith

/-- Cochrane (2023), p. 413: in the top-left panel (`π₁ = −1`) the surpluses rise one point to
pay the deflationary windfall and "an additional 2.55 percentage points of GDP because of the
long period of high real interest rates": `∑ (i_n − π_{n+1}) = Σs + π₁ ∈ (2.545, 2.555)`. -/
theorem fig17_7_real_rates :
    2.545 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) + (-1) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) + (-1) < 2.555 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := fig17_7_values
  obtain ⟨l1, l2⟩ := fig17_7_L_bounds
  rw [fig17_7_sigmaS] at h1 h2 ⊢
  generalize 1 / (lam1 1 (19 / 20) (1 / 4) - 1) = L at h1 h2 l1 l2 ⊢
  constructor <;> norm_num <;> linarith

/-- Cochrane (2023), Fig. 17.7, p. 414 (lower-left panel, "inflation starts at zero and then
slightly rises"): with `π₁ = 0`, `π₂ = c (η − μ) ∈ (0, 0.25)`. -/
theorem fig17_7_zero_panel :
    0 < piAR 1 (19 / 20) (1 / 4) (3 / 5) 0 1 ∧ piAR 1 (19 / 20) (1 / 4) (3 / 5) 0 1 < 1 / 4 := by
  obtain ⟨h1, h2⟩ := fig17_7_lam1_bounds
  have hp : 0 < lam1 1 (19 / 20) (1 / 4) := by linarith
  have e : piAR 1 (19 / 20) (1 / 4) (3 / 5) 0 1 =
      -125 / 11 * (3 / 5) + 125 / 11 * (1 / lam1 1 (19 / 20) (1 / 4)) := by
    simp only [piAR, fig17_7_c, pow_one]
    ring
  have m1 : (1 / 1.609905 : ℝ) < 1 / lam1 1 (19 / 20) (1 / 4) :=
    one_div_lt_one_div_of_lt hp h2
  have m2 : 1 / lam1 1 (19 / 20) (1 / 4) < (1 / 1.6099 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) h1
  rw [e]
  constructor <;> norm_num at m1 m2 ⊢ <;> linarith

/-- Cochrane (2023), p. 414 ("the reverse-engineered `u_t` processes are not AR(1)"): a sum
`a ηⁿ + b μⁿ` with `a, b ≠ 0`, `η ≠ μ` is not a geometric sequence. -/
theorem not_geometric {a b η μ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hημ : η ≠ μ) :
    ¬ ∃ r : ℝ, ∀ n : ℕ, a * η ^ (n + 1) + b * μ ^ (n + 1) = r * (a * η ^ n + b * μ ^ n) := by
  rintro ⟨r, hr⟩
  have h0 := hr 0
  have h1 := hr 1
  simp only [pow_zero, pow_one, mul_one, zero_add] at h0 h1
  have key : a * b * (η - μ) ^ 2 = 0 := by
    have : (a * η + b * μ) ^ 2 = (a + b) * (a * η ^ 2 + b * μ ^ 2) := by
      rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
      have : (a * η + b * μ) ^ 2 = (a * η + b * μ) * (r * (a + b)) := by rw [← h0]; ring
      rw [this, h1]; ring
    linear_combination -this
  have : (η - μ) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hημ)
  exact (mul_ne_zero (mul_ne_zero ha hb) this) key

/-- Cochrane (2023), Fig. 17.7 and p. 414: at the book's parameters (`φ = 1.2`) the
reverse-engineered disturbance `u_n = i_n − φ π_n` is not AR(1) for any initial inflation
`π₁ ≠ c = −125/11`, in particular for all four panels. -/
theorem fig17_7_u_not_ar1 {p : ℝ} (hp : p ≠ -125 / 11) :
    ¬ ∃ r : ℝ, ∀ n : ℕ,
      ((3 / 5 : ℝ) ^ (n + 1) - 6 / 5 * piAR 1 (19 / 20) (1 / 4) (3 / 5) p (n + 1)) =
        r * ((3 / 5 : ℝ) ^ n - 6 / 5 * piAR 1 (19 / 20) (1 / 4) (3 / 5) p n) := by
  obtain ⟨h1, h2⟩ := fig17_7_lam1_bounds
  have hp0 : 0 < lam1 1 (19 / 20) (1 / 4) := by linarith
  have hμ : (3 / 5 : ℝ) ≠ (lam1 1 (19 / 20) (1 / 4))⁻¹ := by
    intro h
    have : lam1 1 (19 / 20) (1 / 4) = 5 / 3 := by
      rw [← inv_inv (lam1 1 (19 / 20) (1 / 4)), ← h]; norm_num
    linarith
  have hb : -(6 / 5) * (p + 125 / 11) ≠ 0 := by
    have : p + 125 / 11 ≠ 0 := fun h => hp (by linarith)
    exact mul_ne_zero (by norm_num) this
  have hng := not_geometric (a := 161 / 11) (by norm_num) hb hμ
  rintro ⟨r, hr⟩
  refine hng ⟨r, fun n => ?_⟩
  have := hr n
  simp only [piAR, fig17_7_c] at this
  linear_combination this

/-- Cochrane (2023), p. 413: "multiplying by 5 … requires an 18% of GDP austerity program":
`5 × 3.55 = 17.75 ≈ 18`. -/
theorem fig17_7_times_five : (5 : ℝ) * 3.55 = 17.75 := by norm_num

/-- Survey error E10, Cochrane (2023), p. 414: "5 × 2.23 = 11.5" is an arithmetic slip:
`5 × 2.23 = 11.15 ≠ 11.5`; at $200 billion per point of GDP (p. 411) this is $2.23 trillion,
matching the printed "$2.2 trillion". -/
theorem e10 : (5 : ℝ) * 2.23 = 11.15 ∧ (5 : ℝ) * 2.23 ≠ 11.5 ∧ (11.15 : ℝ) * 200 = 2230 := by
  norm_num


/-! ### Figure 17.6: the surplus change `Δs` of equilibria A–E (ρ < 1) -/

/-- Cochrane (2023), Fig. 17.6, p. 410: after an unexpected permanent rise at date 0
(`i_t = 1`, `t ≥ 0`), the perfect-foresight path with initial inflation `p` is
`π_j = 1 + (p − 1) λ₁^{−j}`. -/
theorem path_step0 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (p : ℝ) (j : ℕ) :
    path σ β κ (stepI 0) p j = 1 + (p - 1) * (lam1 σ β κ)⁻¹ ^ j := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith
  have hsk := sigma_kappa_eq ha hβ
  induction j with
  | zero => simp [path]
  | succ j ih =>
    simp only [path]
    rw [ih, F_step h2.le h21, Nat.zero_sub, pow_zero, pow_succ, hsk]
    field_simp
    ring

/-- Cochrane (2023), Fig. 17.6, p. 410, and eq. (17.19) with `0 ≤ ρ < 1` (real rates earned
between `j` and `j + 1`, `eq_17_19`): the news about the present value of surpluses needed by
the equilibrium with initial inflation `p`, with pre-shock expectations at the steady state,
`Δs = −π₀ + ∑_j ρʲ (i_j − π_{j+1})`. A permanent change `Δ` of `s̃` has present value
`Δ/(1 − ρ)` (`permanent_surplus_pct`), i.e. `Δ/s̃̄` with steady state `s̃̄ = 1 − ρ` (debt value
one), so `Δs` is the percentage change in steady-state surpluses that Fig. 17.6 reports. -/
noncomputable def deltaS (σ β κ ρ p : ℝ) : ℝ :=
  -p + ∑' j : ℕ, ρ ^ j * (1 - path σ β κ (stepI 0) p (j + 1))

/-- A permanent surplus change `Δ` has present value `∑ ρʲ Δ = Δ/(1 − ρ)`. -/
theorem permanent_surplus_pct {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (Δ : ℝ) :
    ∑' j : ℕ, ρ ^ j * Δ = Δ / (1 - ρ) := by
  rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ1, div_eq_inv_mul]

/-- Cochrane (2023), Fig. 17.6: closed form `Δs(p) = (1 − p)/(λ₁ − ρ) − p` for `0 ≤ ρ < λ₁`. -/
theorem deltaS_closed {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) (p : ℝ) :
    deltaS σ β κ ρ p = (1 - p) / (lam1 σ β κ - ρ) - p := by
  have hl0 : 0 < lam1 σ β κ := one_pos.trans (one_lt_lam1 ha hβ)
  have hq0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := mul_nonneg hρ0 (inv_nonneg.mpr hl0.le)
  have hq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hl0]; exact hρ
  have hterm : ∀ j : ℕ, ρ ^ j * (1 - path σ β κ (stepI 0) p (j + 1)) =
      (1 - p) * (lam1 σ β κ)⁻¹ * (ρ * (lam1 σ β κ)⁻¹) ^ j := fun j => by
    rw [path_step0 ha hβ, mul_pow, pow_succ]; ring
  unfold deltaS
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have h1 : lam1 σ β κ - ρ ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Fig. 17.6, equilibrium B (`π = 1` at once, the super-neutral response):
`Δs = −1`, for every parameter value — the printed "B, Δs = −1.00". -/
theorem deltaS_B {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) : deltaS σ β κ ρ 1 = -1 := by
  rw [deltaS_closed ha hβ hρ0 hρ]; simp

/-- Cochrane (2023), Fig. 17.6, equilibrium D (no unexpected inflation, `π₀ = 0`):
`Δs = 1/(λ₁ − ρ) > 0` — real rates rise, so surpluses must rise. -/
theorem deltaS_D {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) : deltaS σ β κ ρ 0 = 1 / (lam1 σ β κ - ρ) ∧ 0 < deltaS σ β κ ρ 0 := by
  rw [deltaS_closed ha hβ hρ0 hρ]
  refine ⟨by ring, ?_⟩
  have : 0 < lam1 σ β κ - ρ := by linarith
  simp only [sub_zero]
  positivity

/-- Cochrane (2023), Fig. 17.6, equilibrium C and p. 410 ("the Δs = 0 equilibrium is not the
equilibrium … with ΔE₁π₁ = 0"): `Δs = 0` exactly at initial inflation `1/(1 + λ₁ − ρ) ∈ (0, 1)`. -/
theorem deltaS_zero_iff {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) (p : ℝ) :
    deltaS σ β κ ρ p = 0 ↔ p = 1 / (1 + lam1 σ β κ - ρ) := by
  rw [deltaS_closed ha hβ hρ0 hρ]
  have h1 : lam1 σ β κ - ρ ≠ 0 := by linarith
  have h2 : 1 + lam1 σ β κ - ρ ≠ 0 := by linarith
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), Fig. 17.6, p. 410: the printed `Δs` values cannot all hold with A and E
being the jumps `δ₁ = ±1%` relative to the `δ = 0` equilibrium. Whatever the parameters, `Δs` is
affine, `Δs(p) = K (1 − p) − p` (`deltaS_closed`, with `K = 1/(λ₁ − ρ)`; with (17.16)'s dating
`K = ρ/(λ₁ − ρ)`). If D (`p = 0`) has `Δs = 1.66` and the `δ = 0` equilibrium (`p = p₀`) has
`Δs = 0.67` (up to rounding), then `δ = +1` gives `Δs < −1.9` (printed A: −1.53) and `δ = −1`
gives `Δs > 3.2` (printed E: 2.99). -/
theorem fig17_6_inconsistent {K p0 : ℝ} (f : ℝ → ℝ) (hf : ∀ p, f p = K * (1 - p) - p)
    (hD : |f 0 - 1.66| ≤ 0.005) (h0 : |f p0 - 0.67| ≤ 0.005) :
    f (p0 + 1) < -1.9 ∧ 3.2 < f (p0 - 1) := by
  rw [hf] at hD h0 ⊢
  rw [hf]
  rw [abs_le] at hD h0
  constructor <;> nlinarith [hD.1, hD.2, h0.1, h0.2]

/-- Cochrane (2023), Fig. 17.6, p. 410: with the affine `Δs` of `deltaS_closed`, the printed A
(`Δs = −1.53`) and E (`Δs = 2.99`) correspond to jumps of about `+0.83` and `−0.87` relative to
the `δ = 0` equilibrium (all printed values up to rounding), not `±1`. -/
theorem fig17_6_implied_jumps {K p0 pA pE : ℝ} (f : ℝ → ℝ) (hf : ∀ p, f p = K * (1 - p) - p)
    (hD : |f 0 - 1.66| ≤ 0.005) (h0 : |f p0 - 0.67| ≤ 0.005) (hA : |f pA + 1.53| ≤ 0.005)
    (hE : |f pE - 2.99| ≤ 0.005) :
    0.82 < pA - p0 ∧ pA - p0 < 0.84 ∧ 0.86 < p0 - pE ∧ p0 - pE < 0.88 := by
  simp only [hf, abs_le] at hD h0 hA hE
  have hK1 : 1.655 ≤ K := by linarith [hD.1]
  have hK2 : K ≤ 1.665 := by linarith [hD.2]
  have eA : (1 + K) * (pA - p0) = (K * (1 - p0) - p0) - (K * (1 - pA) - pA) := by ring
  have eE : (1 + K) * (p0 - pE) = (K * (1 - pE) - pE) - (K * (1 - p0) - p0) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hA.1, hA.2, hE.1, hE.2, h0.1, h0.2]

end Cochrane.KeynesianStickyPrices.FiscalUnderpinnings

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policy in the full new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5 "Optimal policy,
determinacy and selection" and §17.5.1 "Optimal policy", eqs. (17.22)–(17.28), pp. 417–420.

Policy is written in King's form (17.22), `i_t = i*_t + φ(π_t − π*_t)` (`KingRule`); in the
equilibrium `i = i*`, `π = π*` and `φ` drops out (`king_equilibrium`, `king_iff_standard`: the
same rule is `i_t = φ π_t + u_{i,t}` with the stochastic intercept `u_{i,t} = i*_t − φ π*_t`).
The starred model (17.23)–(17.24) (`Starred`) is the full model (`starred_iff_model`).

* (17.27): for `σ, κ ≠ 0`, `(i*, x*, π*)` solves the starred model iff
  `x* = (π* − β E π*' − u_π)/κ` and
  `i*_t = (1/σκ)[−β E_t π*_{t+2} + (1 + β + σκ) E_t π*_{t+1} − π*_t]
    + (1/σκ)[−E_t u_{π,t+1} + u_{π,t}] + u_{x,t}/σ` (`eq_17_27`). Hence **any** inflation
  path is attainable exactly, with bounded output and rate if everything is bounded
  (`any_pi_attainable`), and any output path is attainable (`any_x_attainable`).
* (17.25): zero inflation (`eq_17_25`). (17.26): zero output gap, with the unique bounded
  inflation `π* = E_t ∑ βʲ u_{π,t+j}` (`eq_17_26`, `E_forwardSeries_succ`).
* Survey error E9 (p. 418): with `x* = 0` the intercept is
  `i* − φπ* = (1 − φβ) E_t ∑ βʲ u_{π,t+1+j} − φ u_{π,t} + u_{x,t}/σ` (`e9_intercept`), not the
  printed `(1 − φ) E_t ∑ βʲ u_{π,t+1+j} + u_{x,t}/σ`; the two differ by
  `φ[(1 − β) E_t ∑ βʲ u_{π,t+1+j} − u_{π,t}]` (`e9_difference`), e.g. `−160/67` vs `−70/67` for
  an AR(1) cost-push shock with `ρ = 0.7`, `β = 0.95`, `φ = 1.5` (`e9_counterexample`).
* Woodford's loss `λ var(x) + (1 − λ) var(π)`: `x* = 0` and `π* = 0` are its corners
  (`loss_corner_x`, `loss_corner_pi`).
* (17.28): the rule with long-run target, natural rate and systematic responses is a rule with
  total inflation coefficient `θ_π + φ_π` (`rule_17_28_eq`).
* p. 419, "different values of φ without a time-varying intercept cannot fully stabilize
  inflation or output": zero inflation under `i_t = φ π_t + c` requires the IS shock to be
  `u_x = σc + (E_t u_{π,t+1} − u_{π,t})/κ`, whatever `φ` (`pi_zero_constant_intercept`), so with
  no IS shock and a non-constant geometric cost-push shock no `(φ, c)` works
  (`no_rule_stabilises_inflation`); zero output under a constant intercept forces `φ = ρ`,
  `c = 0` for an AR(1) cost-push shock (`x_zero_constant_intercept`), i.e. `φ < 1`, where
  the equilibrium is not determinate (`TaylorDeterminacy`).
-/

namespace Cochrane.KeynesianStickyPrices.OptimalPolicy

open Filter Topology FullModel

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### King's form of the rule and the starred model -/

/-- Cochrane (2023), eq. (17.22), p. 417: `i_t = i*_t + φ(π_t − π*_t)`. -/
def KingRule (φ : ℝ) (i istar π πstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = istar t + φ • (π t - πstar t)

/-- Cochrane (2023), p. 418: King's rule is `i_t = φ π_t + u_{i,t}` with the stochastic
intercept (monetary-policy disturbance) `u_{i,t} = i*_t − φ π*_t`. -/
theorem king_iff_standard (φ : ℝ) (i istar π πstar : ℕ → Ω → ℝ) :
    KingRule φ i istar π πstar ↔ ∀ t, i t = φ • π t + (istar t - φ • πstar t) := by
  refine forall_congr' fun t => ?_
  rw [smul_sub]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), p. 417 ("we only observe `i_t = i*_t` and `π_t = π*_t`, so φ disappears
from equilibrium dynamics"): the starred paths satisfy King's rule for **every** `φ`. -/
theorem king_equilibrium (φ : ℝ) (istar πstar : ℕ → Ω → ℝ) :
    KingRule φ istar istar πstar πstar := fun t => by simp

/-- Cochrane (2023), eqs. (17.23)–(17.24), p. 417: the starred model
`x*_t = E_t x*_{t+1} − σ(i*_t − E_t π*_{t+1}) + u_{x,t}`,
`π*_t = β E_t π*_{t+1} + κ x*_t + u_{π,t}`. -/
def Starred (σ β κ : ℝ) (ux uπ i x π : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1))) + ux t) ∧
    ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + uπ t

/-- Cochrane (2023), eqs. (17.23)–(17.24): the starred model is (17.15)–(17.17) with the real
rate `r_t = i_t − E_t π_{t+1}`. -/
theorem starred_iff_model (σ β κ : ℝ) (ux uπ i x π : ℕ → Ω → ℝ) :
    Starred 𝔼 σ β κ ux uπ i x π ↔
      Model 𝔼 σ β κ ux uπ i (fun t => i t - 𝔼.E t (π (t + 1))) x π := by
  unfold Starred Model IS PC
  rw [fisher_iff]
  simp

/-- Cochrane (2023), eq. (17.27), p. 418: for `σ, κ ≠ 0`, `(i*, x*, π*)` solves the starred
model iff `x*_t = κ⁻¹(π*_t − β E_t π*_{t+1} − u_{π,t})` and
`i*_t = (σκ)⁻¹[−β E_t π*_{t+2} + (1 + β + σκ) E_t π*_{t+1} − π*_t]
  + (σκ)⁻¹[−E_t u_{π,t+1} + u_{π,t}] + σ⁻¹ u_{x,t}`. -/
theorem eq_17_27 {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (ux uπ i x π : ℕ → Ω → ℝ) :
    Starred 𝔼 σ β κ ux uπ i x π ↔
      (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)) - uπ t)) ∧
      ∀ t, i t = (σ * κ)⁻¹ • (-β • 𝔼.E t (π (t + 2)) + (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) -
          π t) + (σ * κ)⁻¹ • (-𝔼.E t (uπ (t + 1)) + uπ t) + σ⁻¹ • ux t := by
  rw [starred_iff_model, eq_17_18_shocks 𝔼 hκ]
  have hσκ : σ * κ ≠ 0 := mul_ne_zero hσ hκ
  simp only [true_and]
  refine and_congr_right fun _ => forall_congr' fun t => ?_
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply,
      neg_mul] at e ⊢
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply,
      neg_mul] at e ⊢
    rw [e]
    field_simp
    ring

/-- Cochrane (2023), eq. (17.25), p. 417: zero inflation `π* = 0` is achieved iff
`x*_t = −u_{π,t}/κ` and `i*_t = (1/σκ)(−E_t u_{π,t+1} + u_{π,t}) + u_{x,t}/σ`. -/
theorem eq_17_25 {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (ux uπ i x : ℕ → Ω → ℝ) :
    Starred 𝔼 σ β κ ux uπ i x 0 ↔
      (∀ t, x t = -κ⁻¹ • uπ t) ∧
      ∀ t, i t = (σ * κ)⁻¹ • (-𝔼.E t (uπ (t + 1)) + uπ t) + σ⁻¹ • ux t := by
  rw [eq_17_27 𝔼 hσ hκ]
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_sub, add_zero, sub_zero,
    zero_add, smul_neg, neg_smul]

/-- Cochrane (2023), eq. (17.26), p. 417: `E_t π*_{t+1} = E_t ∑_{j≥0} βʲ u_{π,t+1+j}` for the
forward series `π* = ∑ βʲ E_t u_{π,t+j}` (bounded `u_π`, `0 ≤ β < 1`). -/
theorem E_forwardSeries_succ {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) :
    𝔼.E t (𝔼.forwardSeries β u (t + 1)) ω = ∑' j, β ^ j * 𝔼.E t (u (t + 1 + j)) ω := by
  have hb : ∀ k ω', |β ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + 1 + k)) (t + 1) ω') (pow_nonneg hβ0 k)
  change 𝔼.E t (fun ω' => ∑' k, β ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
  rw [𝔼.E_tsum hβ0 hβ1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (β ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
  rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (17.26), p. 417: for `σ ≠ 0`, `0 ≤ β < 1` and bounded adapted `u_π`,
a zero output gap `x* = 0` with bounded inflation is achieved iff
`π*_t = E_t ∑ βʲ u_{π,t+j}` (the forward series) and
`i*_t = E_t π*_{t+1} + u_{x,t}/σ = E_t ∑ βʲ u_{π,t+1+j} + u_{x,t}/σ` (`E_forwardSeries_succ`). -/
theorem eq_17_26 {σ β κ M : ℝ} (hσ : σ ≠ 0) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ux uπ i π : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |uπ t ω| ≤ M) (hua : 𝔼.Adapted uπ) (hπb : BoundedProc π) :
    Starred 𝔼 σ β κ ux uπ i 0 π ↔
      π = 𝔼.forwardSeries β uπ ∧
      i = fun t => 𝔼.E t (𝔼.forwardSeries β uπ (t + 1)) + σ⁻¹ • ux t := by
  constructor
  · rintro ⟨his, hpc⟩
    have hπ : π = 𝔼.forwardSeries β uπ :=
      𝔼.eq_forwardSeries hβ0 hβ1 hu hua (fun t => by simpa using hpc t) hπb
    refine ⟨hπ, funext fun t => funext fun ω => ?_⟩
    have e := congrFun (his t) ω
    rw [← hπ]
    simp only [Pi.zero_apply, map_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    field_simp
    linear_combination e
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext ω
      simp only [Pi.zero_apply, map_zero, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      field_simp
      ring
    · rw [𝔼.forwardSeries_solves hβ0 hβ1 hu hua t]
      simp

/-- Survey error E9, Cochrane (2023), p. 418 (corrected): with `x* = 0` the
intercept/disturbance is
`i*_t − φ π*_t = (1 − φβ) E_t ∑ βʲ u_{π,t+1+j} − φ u_{π,t} + u_{x,t}/σ`. -/
theorem e9_intercept {σ β κ M φ : ℝ} (hσ : σ ≠ 0) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ux uπ i π : ℕ → Ω → ℝ} (hu : ∀ t ω, |uπ t ω| ≤ M) (hua : 𝔼.Adapted uπ)
    (hπb : BoundedProc π) (h : Starred 𝔼 σ β κ ux uπ i 0 π) (t : ℕ) (ω : Ω) :
    i t ω - φ * π t ω =
      (1 - φ * β) * ∑' j, β ^ j * 𝔼.E t (uπ (t + 1 + j)) ω - φ * uπ t ω + σ⁻¹ * ux t ω := by
  obtain ⟨hπ, hi⟩ := (eq_17_26 𝔼 hσ hβ0 hβ1 hu hua hπb).mp h
  have hs := congrFun (𝔼.forwardSeries_solves hβ0 hβ1 hu hua t) ω
  rw [hi, hπ]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs ⊢
  rw [hs, E_forwardSeries_succ 𝔼 hβ0 hβ1 hu t ω]
  ring

/-- Survey error E9, Cochrane (2023), p. 418: the correct intercept minus the printed one,
`(1 − φβ) S − φ u + u_x/σ − [(1 − φ) S + u_x/σ] = φ[(1 − β) S − u]`; it vanishes (for
`φ ≠ 0`) only if `(1 − β) E_t ∑ βʲ u_{π,t+1+j} = u_{π,t}`. -/
theorem e9_difference (φ β S u uxσ : ℝ) :
    ((1 - φ * β) * S - φ * u + uxσ) - ((1 - φ) * S + uxσ) = φ * ((1 - β) * S - u) := by ring

/-- Survey error E9, Cochrane (2023), p. 418, counterexample: perfect foresight,
`u_{π,t} = 0.7ᵗ`, `u_x = 0`, `β = 0.95`, `φ = 1.5`. Then `S_0 = ∑ βʲ u_{π,1+j} = 140/67`, the
correct intercept `(1 − φβ) S_0 − φ u_{π,0} = −160/67 ≈ −2.388` (`e9_intercept`), the printed
`(1 − φ) S_0 = −70/67 ≈ −1.045`. -/
theorem e9_counterexample :
    ∑' j : ℕ, (19 / 20 : ℝ) ^ j * (7 / 10) ^ (1 + j) = 140 / 67 ∧
      (1 - 3 / 2 * (19 / 20 : ℝ)) * (140 / 67) - 3 / 2 * (7 / 10) ^ 0 = -160 / 67 ∧
      (1 - 3 / 2 : ℝ) * (140 / 67) = -70 / 67 ∧ (-160 / 67 : ℝ) ≠ -70 / 67 := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num⟩
  have h : ∀ j : ℕ, (19 / 20 : ℝ) ^ j * (7 / 10) ^ (1 + j) = 7 / 10 * (133 / 200) ^ j := by
    intro j
    rw [pow_add, pow_one, show (133 / 200 : ℝ) = 19 / 20 * (7 / 10) by norm_num, mul_pow]
    ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-! ### Any path is attainable -/

/-- A bounded process stays bounded under `E_t` applied to a shifted date. -/
theorem boundedProc_E {y : ℕ → Ω → ℝ} (hy : BoundedProc y) (k : ℕ) :
    BoundedProc fun t => 𝔼.E t (y (t + k)) := by
  obtain ⟨M, hM⟩ := hy
  exact ⟨M, fun t ω => 𝔼.abs_E_le (hM (t + k)) t ω⟩

/-- Sums and scalar multiples of bounded processes are bounded. -/
theorem boundedProc_add_smul {y z : ℕ → Ω → ℝ} (hy : BoundedProc y) (hz : BoundedProc z)
    (a b : ℝ) : BoundedProc fun t => a • y t + b • z t := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨N, hN⟩ := hz
  refine ⟨|a| * M + |b| * N, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hN t ω) (abs_nonneg b)

/-- Cochrane (2023), p. 418 ("monetary policy in this model can still attain … any given
inflation path … exactly"; "the interest-rate policy `i*_t` that generates any desired
inflation path"): for `σ, κ ≠ 0` and **any** target `π*`, the output gap and the rate given by
(17.27) solve the starred model; if `π*`, `u_π`, `u_x` are bounded so are `x*` and `i*`. -/
theorem any_pi_attainable {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (ux uπ π : ℕ → Ω → ℝ) :
    let x := fun t => κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)) - uπ t)
    let i := fun t => (σ * κ)⁻¹ • (-β • 𝔼.E t (π (t + 2)) +
      (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) - π t) + (σ * κ)⁻¹ • (-𝔼.E t (uπ (t + 1)) + uπ t) +
      σ⁻¹ • ux t
    Starred 𝔼 σ β κ ux uπ i x π ∧
      (BoundedProc π → BoundedProc uπ → BoundedProc ux → BoundedProc x ∧ BoundedProc i) := by
  intro x i
  refine ⟨(eq_17_27 𝔼 hσ hκ ux uπ i x π).mpr ⟨fun t => rfl, fun t => rfl⟩, ?_⟩
  intro hπ hu hx
  have e1 := boundedProc_E 𝔼 hπ 1
  have e2 := boundedProc_E 𝔼 hπ 2
  have e0 := boundedProc_E 𝔼 hu 1
  have hneg : ∀ {y : ℕ → Ω → ℝ}, BoundedProc y → BoundedProc fun t => -y t := by
    intro y ⟨M, hM⟩
    exact ⟨M, fun t ω => by simpa using hM t ω⟩
  refine ⟨?_, ?_⟩
  · have h := boundedProc_add_smul (boundedProc_add_smul hπ e1 1 (-β)) hu 1 (-1)
    obtain ⟨M, hM⟩ := boundedProc_add_smul h h κ⁻¹ 0
    refine ⟨M, fun t ω => ?_⟩
    have := hM t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, one_mul,
      neg_one_mul] at this
    simp only [x, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    convert this using 2
    ring
  · have a1 := boundedProc_add_smul (boundedProc_add_smul e2 e1 (-β) (1 + β + σ * κ)) hπ 1 (-1)
    have a2 := boundedProc_add_smul (hneg e0) hu 1 1
    have a3 := boundedProc_add_smul (boundedProc_add_smul a1 a2 (σ * κ)⁻¹ (σ * κ)⁻¹) hx 1 σ⁻¹
    obtain ⟨M, hM⟩ := a3
    refine ⟨M, fun t ω => ?_⟩
    have := hM t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, one_mul,
      neg_one_mul] at this
    simp only [i, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul,
      neg_mul]
    convert this using 2
    ring

/-- Cochrane (2023), p. 418 ("… or any given output path exactly"): for `0 ≤ β < 1`, `σ ≠ 0`
and bounded adapted target output `x*` and cost-push shock `u_π`, inflation
`π* = ∑ βʲ E_t(κ x*_{t+j} + u_{π,t+j})` and
`i*_t = E_t π*_{t+1} + (E_t x*_{t+1} − x*_t + u_{x,t})/σ` solve the starred model, with `π*`
bounded. -/
theorem any_x_attainable {σ β κ M : ℝ} (hσ : σ ≠ 0) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ux uπ x : ℕ → Ω → ℝ} (hb : ∀ t ω, |κ * x t ω + uπ t ω| ≤ M)
    (ha : 𝔼.Adapted fun t => κ • x t + uπ t) :
    let π := 𝔼.forwardSeries β fun t => κ • x t + uπ t
    let i := fun t => 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t + ux t)
    Starred 𝔼 σ β κ ux uπ i x π ∧ BoundedProc π := by
  intro π i
  have hb' : ∀ t ω, |(fun t => κ • x t + uπ t) t ω| ≤ M := fun t ω => by simpa using hb t ω
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, 𝔼.forwardSeries_bounded hβ0 hβ1 hb'⟩
  · funext ω
    simp only [i, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · change 𝔼.forwardSeries β (fun t => κ • x t + uπ t) t =
      β • 𝔼.E t (𝔼.forwardSeries β (fun t => κ • x t + uπ t) (t + 1)) + κ • x t + uπ t
    rw [𝔼.forwardSeries_solves hβ0 hβ1 hb' ha t]
    abel

/-! ### Woodford's loss and the rule (17.28) -/

/-- Cochrane (2023), p. 418: Woodford's loss `λ V(x) + (1 − λ) V(π)` for a variance-like
functional `V`. -/
def woodfordLoss (V : (ℕ → Ω → ℝ) → ℝ) (lam : ℝ) (x π : ℕ → Ω → ℝ) : ℝ :=
  lam * V x + (1 - lam) * V π

/-- Cochrane (2023), p. 418 ("the choices `x* = 0` and `π* = 0` are simple examples of such
policies"): for `V ≥ 0` with `V 0 = 0`, `x* = 0` minimises the loss with `λ = 1`. -/
theorem loss_corner_x (V : (ℕ → Ω → ℝ) → ℝ) (hV : ∀ y, 0 ≤ V y) (hV0 : V 0 = 0)
    (π x' π' : ℕ → Ω → ℝ) : woodfordLoss V 1 0 π ≤ woodfordLoss V 1 x' π' := by
  unfold woodfordLoss
  rw [hV0]
  linarith [hV x']

/-- Cochrane (2023), p. 418: `π* = 0` minimises the loss with `λ = 0`. -/
theorem loss_corner_pi (V : (ℕ → Ω → ℝ) → ℝ) (hV : ∀ y, 0 ≤ V y) (hV0 : V 0 = 0)
    (x x' π' : ℕ → Ω → ℝ) : woodfordLoss V 0 x 0 ≤ woodfordLoss V 0 x' π' := by
  unfold woodfordLoss
  rw [hV0]
  linarith [hV π']

/-- Cochrane (2023), eq. (17.28), p. 419:
`i_t = r*_t + π^T + θ_π π_t + θ_x x_t + φ_π (π_t − π^T) + u_{i,t}`. -/
def Rule1728 (θπ θx φπ πT : ℝ) (rstar u i x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rstar t + (fun _ => πT) + θπ • π t + θx • x t + φπ • (π t - fun _ => πT) + u t

/-- Cochrane (2023), eq. (17.28), p. 419: the rule responds to inflation with total coefficient
`θ_π + φ_π`, with intercept `r*_t + (1 − φ_π) π^T + u_{i,t}`. -/
theorem rule_17_28_eq {θπ θx φπ πT : ℝ} {rstar u i x π : ℕ → Ω → ℝ} :
    Rule1728 θπ θx φπ πT rstar u i x π ↔
      ∀ t, i t = (θπ + φπ) • π t + θx • x t + (rstar t + (fun _ => (1 - φπ) * πT) + u t) := by
  refine forall_congr' fun t => ?_
  have : ∀ a b : Ω → ℝ, a = b ↔ ∀ ω, a ω = b ω := fun a b => funext_iff
  rw [this, this]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  constructor <;> intro h <;> rw [h] <;> ring

/-! ### A constant intercept cannot fully stabilise -/

/-- Cochrane (2023), p. 419 ("different values of φ without a time-varying intercept cannot
fully stabilize inflation"): zero inflation is an equilibrium under `i_t = φ π_t + c` (constant
`c`) only if the IS disturbance is exactly `u_{x,t} = σc + (E_t u_{π,t+1} − u_{π,t})/κ` —
a condition that does not involve `φ`. -/
theorem pi_zero_constant_intercept {σ β κ φ c : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    {ux uπ i x : ℕ → Ω → ℝ} (h : Starred 𝔼 σ β κ ux uπ i x 0)
    (hrule : ∀ t, i t = φ • (0 : ℕ → Ω → ℝ) t + fun _ => c) (t : ℕ) :
    ux t = (fun _ => σ * c) + κ⁻¹ • (𝔼.E t (uπ (t + 1)) - uπ t) := by
  obtain ⟨-, hi⟩ := (eq_17_25 𝔼 hσ hκ ux uπ i x).mp h
  have e := hi t
  rw [hrule t] at e
  funext ω
  have e' := congrFun e ω
  simp only [Pi.zero_apply, smul_zero, zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.neg_apply, Pi.sub_apply] at e' ⊢
  rw [e']
  field_simp
  ring

/-- Cochrane (2023), p. 419: with no IS disturbance and a geometric cost-push shock
`u_{π,t} = ρᵗ u₀` (`ρ ≠ 1`, `u₀ ≠ 0`), no rule `i_t = φ π_t + c` with a constant intercept has
zero inflation as an equilibrium, whatever `φ` and `c` (perfect foresight). -/
theorem no_rule_stabilises_inflation {σ β κ ρ u0 : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hρ : ρ ≠ 1)
    (hu0 : u0 ≠ 0) (φ c : ℝ) (i x : ℕ → Unit → ℝ) :
    ¬ (Starred perfectForesight σ β κ 0 (fun t _ => ρ ^ t * u0) i x 0 ∧
      ∀ t, i t = φ • (0 : ℕ → Unit → ℝ) t + fun _ => c) := by
  rintro ⟨h, hrule⟩
  have e0 := congrFun (pi_zero_constant_intercept perfectForesight hσ hκ h hrule 0) ()
  have e1 := congrFun (pi_zero_constant_intercept perfectForesight hσ hκ h hrule 1) ()
  simp only [perfectForesight, LinearMap.id_apply, Pi.zero_apply, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, pow_zero, pow_one, zero_add] at e0 e1
  have key : κ⁻¹ * ((ρ - 1) ^ 2 * u0) = 0 := by linear_combination e0 - e1
  rcases mul_eq_zero.mp key with h1 | h1
  · exact hκ (inv_eq_zero.mp h1)
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hρ (by nlinarith [pow_eq_zero_iff (n := 2) (a := ρ - 1) two_ne_zero |>.mp h2])
    · exact hu0 h2

/-- Cochrane (2023), p. 419 ("… or output"; perfect foresight): with no IS disturbance and an
AR(1) cost-push shock `u_{π,t} = ρᵗ u₀` (`|ρ| < 1`, `u₀ ≠ 0`, `0 ≤ β < 1`), if a zero output
gap with bounded inflation is an equilibrium under a rule `i_t = φ π_t + c` with constant
intercept, then `φ = ρ` and `c = 0`: the coefficient is pinned to the shock persistence, below
one — where the three-equation model is indeterminate (`TaylorDeterminacy`). -/
theorem x_zero_constant_intercept {β ρ u0 φ c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    (hu0 : u0 ≠ 0) {i π : ℕ → ℝ} (hpc : ∀ t, π t = β * π (t + 1) + ρ ^ t * u0)
    (hb : BoundedS π) (his : ∀ t, i t = π (t + 1)) (hrule : ∀ t, i t = φ * π t + c) :
    φ = ρ ∧ c = 0 := by
  have hβρ : β * ρ < 1 := by
    have h1 : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left (le_abs_self ρ) hβ0
    have h2 : β * |ρ| < 1 := by nlinarith [abs_nonneg ρ]
    linarith
  have hK : 1 - β * ρ ≠ 0 := by linarith
  set K := u0 / (1 - β * ρ) with hKdef
  have hK0 : K ≠ 0 := div_ne_zero hu0 hK
  -- inflation is `K ρᵗ`
  have hd := homog_zero (q := β) (by rw [abs_of_nonneg hβ0]; exact hβ1)
    (d := fun t => π t - K * ρ ^ t) (fun t => by
      rw [hpc t, hKdef, pow_succ]
      field_simp
      ring)
    (by
      obtain ⟨M, hM⟩ := hb
      refine ⟨M + |K|, fun t => (abs_sub _ _).trans (add_le_add (hM t) ?_)⟩
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg K) (pow_le_one₀ (abs_nonneg ρ) hρ.le))
  have hπ : ∀ t, π t = K * ρ ^ t := fun t => by
    have := congrFun hd t
    simp only [Pi.zero_apply] at this
    linarith
  have e0 := hrule 0
  have e1 := hrule 1
  rw [his, hπ, hπ] at e0 e1
  simp only [pow_zero, pow_one, mul_one, zero_add] at e0 e1
  have hρ1 : ρ - 1 ≠ 0 := by
    intro h
    have : ρ = 1 := by linarith
    rw [this, abs_one] at hρ
    exact lt_irrefl _ hρ
  have key : K * (ρ - 1) * (ρ - φ) = 0 := by linear_combination e1 - e0 - ρ * e0 + ρ * e0
  have hφ : φ = ρ := by
    rcases mul_eq_zero.mp key with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hK0
      · exact absurd h' hρ1
    · linarith
  refine ⟨hφ, ?_⟩
  rw [hφ] at e0
  linarith

end Cochrane.KeynesianStickyPrices.OptimalPolicy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Determinacy in the three-equation model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5.2 "Determinacy",
eqs. (17.29)–(17.33), pp. 420–421; Online Appendix A1, §1.13.1, eqs. (1.55)–(1.58),
pp. 586–587; Chapter 16, p. 369, and Chapter 12, p. 328 ("φ > 1 is neither necessary nor
sufficient").

## Generic structural systems

A two-variable system `P x_t = Q E_t x_{t+1}` (`StructSolves`) is *determinate* when its only
bounded adapted solution is zero (`StructDeterminate`). For an arbitrary expectation system
(with `Ω` nonempty), `structDeterminate_iff`: determinate iff `det P ≠ 0` and `A = P⁻¹Q`
satisfies the Schur–Cohn condition (both eigenvalues inside the unit circle — both eigenvalues
of the transition matrix `A⁻¹` of `E_t x_{t+1} = A⁻¹ x_t` explosive). If `det P = 0` there is a
one-period self-fulfilling blip (`not_determinate_of_det_zero`). The proof uses the core
`ExpectationSystem.system_unique` / `system_not_unique` (Galí's `TaylorRuleSystem` pattern).

## The deviation system (17.29)–(17.32), with an output response

Deviations from an equilibrium follow `ĩ = r̃ + E π̃'`, `x̃ = E x̃' − σ r̃`,
`π̃ = β E π̃' + κ x̃`, `ĩ = φ π̃ + φ_x x̃` (`Deviation`; (17.32) is `φ_x = 0`). With
`D = 1 + σφ_x + σκφ` and `T = 1 + β + σκ + βσφ_x`:

* `determinate_iff` / `determinate_iff_explicit`: determinate iff `D ≠ 0` and
  `SchurStable (T/D) (β/D)`, i.e. `(D > 0 ∧ β < D ∧ |T| < D + β) ∨ (D < 0 ∧ β < −D ∧ |T| < −D − β)`.
* `determinate_iff_phi` (A1 p. 587 and (1.58)): for `φ_x = 0`, `σ, κ > 0`, `0 < β < 1`,
  determinate iff `φ > 1` or `φ < −(1 + 2(1 + β)/(σκ))`.
* `determinate_iff_BM`: for `φ, φ_x ≥ 0`, determinate iff `κ(φ − 1) + (1 − β)φ_x > 0`
  (restated from Galí's Bullard–Mitra condition; Cochrane's `σ` is Galí's `1/σ`).
* "φ > 1 is neither necessary nor sufficient" (p. 420, A1 p. 587, Ch16 p. 369, Ch12 P8):
  `not_necessary_witness`, `not_necessary_phix` (every `φ ∈ [0, 1)` is made determinate by some
  `φ_x ≥ 0`), `not_necessary_negative` (oscillating region, `φ_x = 0`), `not_sufficient_witness`
  and `not_sufficient` (every `φ > 1` is made indeterminate by some `φ_x < 0`), while for
  `φ_x ≥ 0` the condition `φ > 1` is sufficient (`sufficient_of_phix_nonneg`) and output
  responses only widen the region (`widens_with_phix`).
* (17.33) and (1.55): `deviation_iff_17_33`, `eq_1_55`; the printed `u_x` coefficient of
  (1.55) is off by a factor `β` (`printed_1_55_iff`).
* (1.57): `trM`, `detM`, `eq_1_57` (the printed eigenvalues are the roots of the characteristic
  polynomial `λ² − tr M λ + det M`), `plus_root_gt_one`, `roots_phi_lt_one` (`φ < 1`: one root
  below one; inside `(−1, 1)` iff `φ > −(1 + 2(1+β)/(σκ))`; below `−1` beyond (1.58)),
  `roots_phi_gt_one` (`φ > 1`: both roots explosive, real or complex).
* φ irrelevance (pp. 419–420): `deviation_of_eqm`, `phi_irrelevance` — for every `φ` in the
  determinacy region the bounded equilibria of the model with King's rule are exactly the
  starred one, so the equilibrium set does not depend on `φ` (`phi_irrelevance_sets`); the
  reverse-engineered disturbances of p. 414 give unique equilibria (`standard_rule_unique`,
  `reverse_engineered_unique`).
* p. 421 (real explosions): for `φ < 1/β` (in particular `1 < φ < 1/β`) a non-selected path
  has `βᵗ x̃_t → −∞` (`real_explosion`).
-/

namespace Cochrane.KeynesianStickyPrices.TaylorDeterminacy

open Filter Topology FullModel OptimalPolicy
open SharedTools (Pmat Qmat solvedA tr2_solvedA det2_solvedA det2_Pmat)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Generic structural systems `P x_t = Q E_t x_{t+1}` -/

/-- Cochrane (2023), p. 420 (the system behind (17.33)): `x` solves `P x_t = Q E_t x_{t+1}`. -/
def StructSolves (P Q : Matrix (Fin 2) (Fin 2) ℝ) (x : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, P i 0 • x t 0 + P i 1 • x t 1 =
    Q i 0 • 𝔼.E t (x (t + 1) 0) + Q i 1 • 𝔼.E t (x (t + 1) 1)

/-- Cochrane (2023), p. 420: determinacy — the only bounded adapted solution of
`P x_t = Q E_t x_{t+1}` is zero. -/
def StructDeterminate (P Q : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x, 𝔼.AdaptedVec x → BoundedVec x → StructSolves 𝔼 P Q x → x = 0

/-- Solving two linear equations by Cramer's rule. -/
theorem solve2 {P00 P01 P10 P11 q0 q1 a b : ℝ} (hD : P00 * P11 - P01 * P10 ≠ 0) :
    (P00 * a + P01 * b = q0 ∧ P10 * a + P11 * b = q1) ↔
      (a = (P11 * q0 - P01 * q1) / (P00 * P11 - P01 * P10) ∧
        b = (P00 * q1 - P10 * q0) / (P00 * P11 - P01 * P10)) := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor <;> rw [eq_div_iff hD]
    · linear_combination P11 * h0 - P01 * h1
    · linear_combination P00 * h1 - P10 * h0
  · rintro ⟨ha, hb⟩
    have ka : a * (P00 * P11 - P01 * P10) = P11 * q0 - P01 * q1 := by
      rw [ha, div_mul_cancel₀ _ hD]
    have kb : b * (P00 * P11 - P01 * P10) = P00 * q1 - P10 * q0 := by
      rw [hb, div_mul_cancel₀ _ hD]
    constructor <;> apply mul_right_cancel₀ hD
    · linear_combination P00 * ka + P01 * kb
    · linear_combination P10 * ka + P11 * kb

/-- For `det P ≠ 0`, `P x_t = Q E_t x_{t+1}` iff `x_t = A E_t x_{t+1}`, `A = P⁻¹ Q`. -/
theorem struct_iff_solves {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : det2 P ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (x : ℕ → Fin 2 → Ω → ℝ) :
    StructSolves 𝔼 P Q x ↔ 𝔼.Solves (solvedA P Q) 0 x := by
  have hP' : P 0 0 * P 1 1 - P 0 1 * P 1 0 ≠ 0 := hP
  have hd : det2 P = P 0 0 * P 1 1 - P 0 1 * P 1 0 := rfl
  constructor
  · intro h t i
    funext ω
    have e0 := congrFun (h t 0) ω
    have e1 := congrFun (h t 1) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
    obtain ⟨ha, hb⟩ := (solve2 hP').mp ⟨e0, e1⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    fin_cases i
    · simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [ha]; ring
    · simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
      rw [hb]; ring
  · intro h t i
    funext ω
    have e0 := congrFun (h t 0) ω
    have e1 := congrFun (h t 1) ω
    simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, add_zero] at e0 e1
    have hab := (solve2 hP' (a := x t 0 ω) (b := x t 1 ω)
      (q0 := Q 0 0 * 𝔼.E t (x (t + 1) 0) ω + Q 0 1 * 𝔼.E t (x (t + 1) 1) ω)
      (q1 := Q 1 0 * 𝔼.E t (x (t + 1) 0) ω + Q 1 1 * 𝔼.E t (x (t + 1) 1) ω)).mpr
      ⟨by rw [e0]; ring, by rw [e1]; ring⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · exact hab.1
    · exact hab.2

/-- Cochrane (2023), p. 420: if `det P = 0` the system is not determinate — a vector `v ≠ 0`
with `P v = 0` gives the bounded solution `x_0 = v`, `x_t = 0` for `t ≥ 1`. -/
theorem not_determinate_of_det_zero [Nonempty Ω] {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : det2 P = 0) (Q : Matrix (Fin 2) (Fin 2) ℝ) : ¬ StructDeterminate 𝔼 P Q := by
  have hP' : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 0 := hP
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, P i 0 * v 0 + P i 1 * v 1 = 0 := by
    by_cases h0 : P 0 0 = 0 ∧ P 0 1 = 0
    · by_cases h1 : P 1 0 = 0 ∧ P 1 1 = 0
      · refine ⟨![1, 0], fun h => by simpa using congrFun h 0, fun i => ?_⟩
        fin_cases i <;> simp [h0.1, h1.1]
      · refine ⟨![P 1 1, -P 1 0], fun h => h1 ⟨by simpa using congrFun h 1,
          by simpa using congrFun h 0⟩, fun i => ?_⟩
        fin_cases i
        · simp [h0.1, h0.2]
        · simp; ring
    · refine ⟨![P 0 1, -P 0 0], fun h => h0 ⟨by simpa using congrFun h 1,
        by simpa using congrFun h 0⟩, fun i => ?_⟩
      fin_cases i
      · simp; ring
      · simp; linear_combination -hP'
  intro hdet
  set x : ℕ → Fin 2 → Ω → ℝ := fun t j _ => if t = 0 then v j else 0 with hx
  have hsol : StructSolves 𝔼 P Q x := by
    intro t i
    funext ω
    simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_one_ne_zero, ↓reduceIte,
      𝔼.const, mul_zero, add_zero]
    split_ifs
    · exact hv i
    · simp
  have h := hdet x (fun t j => by simp only [hx]; exact 𝔼.const t _)
    ⟨|v 0| + |v 1|, fun t j ω => by
      simp only [hx]
      split_ifs
      · fin_cases j <;> simp
      · simp only [abs_zero]; positivity⟩ hsol
  apply hv0
  funext j
  have := congrFun (congrFun (congrFun h 0) j) (Classical.arbitrary Ω)
  simpa [hx] using this

/-- Cochrane (2023), p. 420, and A1 p. 587 (Blanchard–Kahn): `P x_t = Q E_t x_{t+1}` is
determinate iff `det P ≠ 0` and `A = P⁻¹Q` satisfies the Schur–Cohn condition. -/
theorem structDeterminate_iff [Nonempty Ω] (P Q : Matrix (Fin 2) (Fin 2) ℝ) :
    StructDeterminate 𝔼 P Q ↔
      det2 P ≠ 0 ∧ SchurStable (tr2 (solvedA P Q)) (det2 (solvedA P Q)) := by
  constructor
  · intro h
    have hP : det2 P ≠ 0 := fun h0 => not_determinate_of_det_zero 𝔼 h0 Q h
    refine ⟨hP, ?_⟩
    by_contra hA
    have hz : 𝔼.Solves (solvedA P Q) 0 0 := fun t i => by simp
    obtain ⟨y, hy, hay, hby, hne⟩ :=
      𝔼.system_not_unique hA hz (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    exact hne (h y hay hby ((struct_iff_solves 𝔼 hP Q y).mpr hy))
  · rintro ⟨hP, hA⟩ x hax hbx hx
    have hz : 𝔼.Solves (solvedA P Q) 0 0 := fun t i => by simp
    exact 𝔼.system_unique hA ((struct_iff_solves 𝔼 hP Q x).mp hx) hz hax
      (fun t i => by simp) hbx ⟨0, fun t i ω => by simp⟩

/-! ### The deviation system (17.29)–(17.32) -/

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, with an output response `φ_x` (eq. (18.1),
p. 427): `ĩ_t = r̃_t + E_t π̃_{t+1}`, `x̃_t = E_t x̃_{t+1} − σ r̃_t`,
`π̃_t = β E_t π̃_{t+1} + κ x̃_t`, `ĩ_t = φ π̃_t + φ_x x̃_t`. -/
def Deviation (σ β κ φ φx : ℝ) (i r x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + 𝔼.E t (π (t + 1)) ∧ x t = 𝔼.E t (x (t + 1)) - σ • r t ∧
    π t = β • 𝔼.E t (π (t + 1)) + κ • x t ∧ i t = φ • π t + φx • x t

/-- The stacked vector `(x̃_t, π̃_t)`. -/
def stack (x π : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, π t]

/-- Cochrane (2023), eqs. (17.29)–(17.32): eliminating `ĩ` and `r̃`, the deviation system is
`(1 + σφ_x) x̃_t + σφ π̃_t = E_t x̃_{t+1} + σ E_t π̃_{t+1}`, `−κ x̃_t + π̃_t = β E_t π̃_{t+1}`. -/
theorem deviation_iff_struct (σ β κ φ φx : ℝ) (i r x π : ℕ → Ω → ℝ) :
    Deviation 𝔼 σ β κ φ φx i r x π ↔
      (∀ t, i t = φ • π t + φx • x t) ∧ (∀ t, r t = i t - 𝔼.E t (π (t + 1))) ∧
        StructSolves 𝔼 (Pmat σ κ φ φx) (Qmat σ β) (stack x π) := by
  constructor
  · intro h
    refine ⟨fun t => (h t).2.2.2, fun t => by rw [(h t).1]; abel, fun t j => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    have e3 := congrFun h3 ω
    have e4 := congrFun h4 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
    fin_cases j
    · simp only [Pmat, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Qmat, one_smul]
      linear_combination e2 + σ * e1 - σ * e4
    · simp only [Pmat, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, stack, neg_smul,
        one_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Qmat, zero_smul,
        Pi.zero_apply, zero_add]
      linear_combination e3
  · rintro ⟨hi, hr, hs⟩ t
    have e0 := hs t 0
    have e1 := hs t 1
    simp only [Pmat, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Qmat, one_smul, neg_smul, zero_smul,
      zero_add] at e0 e1
    refine ⟨by rw [hr t]; abel, ?_, ?_, hi t⟩
    · funext ω
      have f0 := congrFun e0 ω
      have fi := congrFun (hi t) ω
      rw [hr t]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f0 fi ⊢
      rw [fi]
      linear_combination f0
    · funext ω
      have f1 := congrFun e1 ω
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at f1 ⊢
      linear_combination f1

/-- Cochrane (2023), p. 420: the deviation system is *determinate* when its only bounded
adapted solution has `x̃ = π̃ = 0` (and then `ĩ = r̃ = 0`). -/
def Determinate (σ β κ φ φx : ℝ) : Prop :=
  ∀ i r x π : ℕ → Ω → ℝ, 𝔼.Adapted x → 𝔼.Adapted π → BoundedProc x → BoundedProc π →
    Deviation 𝔼 σ β κ φ φx i r x π → x = 0 ∧ π = 0

/-- Determinacy of the deviation system is determinacy of the structural system. -/
theorem determinate_iff_struct (σ β κ φ φx : ℝ) :
    Determinate 𝔼 σ β κ φ φx ↔ StructDeterminate 𝔼 (Pmat σ κ φ φx) (Qmat σ β) := by
  constructor
  · intro h v hav hbv hv
    set x : ℕ → Ω → ℝ := fun t => v t 0
    set π : ℕ → Ω → ℝ := fun t => v t 1
    have hst : stack x π = v := by
      funext t j; fin_cases j <;> rfl
    have hd : Deviation 𝔼 σ β κ φ φx (fun t => φ • π t + φx • x t)
        (fun t => φ • π t + φx • x t - 𝔼.E t (π (t + 1))) x π :=
      (deviation_iff_struct 𝔼 σ β κ φ φx _ _ x π).mpr ⟨fun t => rfl, fun t => rfl, hst ▸ hv⟩
    obtain ⟨M, hM⟩ := hbv
    obtain ⟨h1, h2⟩ := h _ _ x π (fun t => hav t 0) (fun t => hav t 1)
      ⟨M, fun t ω => hM t 0 ω⟩ ⟨M, fun t ω => hM t 1 ω⟩ hd
    rw [← hst, h1, h2]
    funext t j
    fin_cases j <;> rfl
  · intro h i r x π hx hπ hbx hbπ hd
    have hs := ((deviation_iff_struct 𝔼 σ β κ φ φx i r x π).mp hd).2.2
    obtain ⟨M₁, h₁⟩ := hbx
    obtain ⟨M₂, h₂⟩ := hbπ
    have h0 := h (stack x π) (fun t j => by fin_cases j; exacts [hx t, hπ t])
      ⟨max M₁ M₂, fun t j ω => by
        fin_cases j
        · exact (h₁ t ω).trans (le_max_left _ _)
        · exact (h₂ t ω).trans (le_max_right _ _)⟩ hs
    exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun h0 t) 0,
      funext fun t => by simpa [stack] using congrFun (congrFun h0 t) 1⟩

/-- Cochrane (2023), p. 420 and A1 p. 587: the deviation system (with output response) is
determinate iff `D = 1 + σφ_x + σκφ ≠ 0` and `SchurStable (T/D) (β/D)`,
`T = 1 + β + σκ + βσφ_x`. -/
theorem determinate_iff [Nonempty Ω] (σ β κ φ φx : ℝ) :
    Determinate 𝔼 σ β κ φ φx ↔
      1 + σ * φx + σ * κ * φ ≠ 0 ∧
        SchurStable ((1 + β + σ * κ + β * σ * φx) / (1 + σ * φx + σ * κ * φ))
          (β / (1 + σ * φx + σ * κ * φ)) := by
  rw [determinate_iff_struct, structDeterminate_iff, det2_Pmat]
  refine and_congr_right fun hD => ?_
  have hD' : det2 (Pmat σ κ φ φx) ≠ 0 := by rwa [det2_Pmat]
  rw [tr2_solvedA, det2_solvedA hD', det2_Pmat]
  have hq : det2 (Qmat σ β) = β := by simp [det2, Qmat]
  rw [hq]
  have ht : Pmat σ κ φ φx 1 1 * Qmat σ β 0 0 - Pmat σ κ φ φx 0 1 * Qmat σ β 1 0 -
      Pmat σ κ φ φx 1 0 * Qmat σ β 0 1 + Pmat σ κ φ φx 0 0 * Qmat σ β 1 1 =
      1 + β + σ * κ + β * σ * φx := by
    simp [Pmat, Qmat]; ring
  rw [ht]

/-- Schur–Cohn for `(T/D, β/D)` with `D > 0`, `β > 0`: `β < D ∧ |T| < D + β`. -/
theorem schur_div_pos {T D β : ℝ} (hD : 0 < D) (hβ : 0 < β) :
    SchurStable (T / D) (β / D) ↔ β < D ∧ |T| < D + β := by
  unfold SchurStable
  rw [abs_div, abs_div, abs_of_pos hD, abs_of_pos hβ, div_lt_one hD, one_add_div hD.ne',
    div_lt_div_iff_of_pos_right hD]

/-- Schur–Cohn for `(T/D, β/D)` with `D < 0`, `β > 0`: `β < −D ∧ |T| < −D − β`. -/
theorem schur_div_neg {T D β : ℝ} (hD : D < 0) (hβ : 0 < β) :
    SchurStable (T / D) (β / D) ↔ β < -D ∧ |T| < -D - β := by
  unfold SchurStable
  have hD' : 0 < -D := by linarith
  have hD0 : D ≠ 0 := hD.ne
  rw [abs_div, abs_div, abs_of_neg hD, abs_of_pos hβ, div_lt_one hD',
    show 1 + β / D = (-D - β) / -D by field_simp; ring, div_lt_div_iff_of_pos_right hD']

/-- Cochrane (2023), p. 420 and A1 p. 587, explicit form: determinate iff
`(D > 0 ∧ β < D ∧ |T| < D + β) ∨ (D < 0 ∧ β < −D ∧ |T| < −D − β)`. -/
theorem determinate_iff_explicit [Nonempty Ω] {σ β κ φ φx : ℝ} (hβ : 0 < β) :
    Determinate 𝔼 σ β κ φ φx ↔
      (0 < 1 + σ * φx + σ * κ * φ ∧ β < 1 + σ * φx + σ * κ * φ ∧
          |1 + β + σ * κ + β * σ * φx| < 1 + σ * φx + σ * κ * φ + β) ∨
        (1 + σ * φx + σ * κ * φ < 0 ∧ β < -(1 + σ * φx + σ * κ * φ) ∧
          |1 + β + σ * κ + β * σ * φx| < -(1 + σ * φx + σ * κ * φ) - β) := by
  rw [determinate_iff]
  rcases lt_trichotomy (1 + σ * φx + σ * κ * φ) 0 with hD | hD | hD
  · rw [schur_div_neg hD hβ]
    constructor
    · rintro ⟨-, h⟩; exact Or.inr ⟨hD, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · linarith
      · exact ⟨hD.ne, h⟩
  · rw [hD]
    simp only [ne_eq, not_true_eq_false, false_and, lt_self_iff_false, false_or]
  · rw [schur_div_pos hD hβ]
    constructor
    · rintro ⟨-, h⟩; exact Or.inl ⟨hD, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ⟨hD.ne', h⟩
      · linarith

/-- Cochrane (2023), A1 p. 587 and eq. (1.58), with Ch17 p. 420: in the three-equation model
with `i = φπ` (`φ_x = 0`), `σ, κ > 0`, `0 < β < 1`, the equilibrium is determinate iff
`φ > 1` or `φ < −(1 + 2(1 + β)/(σκ))`. -/
theorem determinate_iff_phi [Nonempty Ω] {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) :
    Determinate 𝔼 σ β κ φ 0 ↔ 1 < φ ∨ φ < -(1 + 2 * (1 + β) / (σ * κ)) := by
  have ha := mul_pos hσ hκ
  rw [determinate_iff_explicit 𝔼 hβ]
  simp only [mul_zero, add_zero]
  have hT : 0 < 1 + β + σ * κ := by linarith
  rw [abs_of_pos hT]
  have hb : -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) = -(σ * κ) - 2 * (1 + β) := by
    field_simp
    ring
  constructor
  · rintro (⟨-, -, h⟩ | ⟨-, -, h⟩)
    · left
      nlinarith
    · right
      have : φ * (σ * κ) < -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) := by rw [hb]; nlinarith
      exact lt_of_mul_lt_mul_right this ha.le
  · rintro (h | h)
    · left
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · right
      have : φ * (σ * κ) < -(σ * κ) - 2 * (1 + β) := by
        rw [← hb]; exact mul_lt_mul_of_pos_right h ha
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Cochrane (2023), Ch16 p. 369 and A1 p. 587 (restated from Galí's Bullard–Mitra condition):
for `σ, κ > 0`, `0 < β < 1` and `φ, φ_x ≥ 0`, determinate iff `κ(φ − 1) + (1 − β)φ_x > 0`. -/
theorem determinate_iff_BM [Nonempty Ω] {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 0 ≤ φ) (hφx : 0 ≤ φx) :
    Determinate 𝔼 σ β κ φ φx ↔ 0 < κ * (φ - 1) + (1 - β) * φx := by
  rw [determinate_iff_explicit 𝔼 hβ]
  have h1 : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  have h2 : 0 ≤ σ * κ * φ := mul_nonneg (mul_pos hσ hκ).le hφ
  have hT : 0 < 1 + β + σ * κ + β * σ * φx := by
    have := mul_nonneg hβ.le h1
    nlinarith [mul_pos hσ hκ]
  rw [abs_of_pos hT]
  constructor
  · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
    · have : 0 < σ * (κ * (φ - 1) + (1 - β) * φx) := by nlinarith
      exact pos_of_mul_pos_right this hσ.le
    · linarith
  · intro h
    left
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith [mul_pos hσ h]


/-! ### φ > 1 is neither necessary nor sufficient -/

/-- Cochrane (2023), p. 420, A1 p. 587, Ch16 p. 369 and Ch12 p. 328 ("φ > 1 is neither
necessary …"): with `σ = κ = 1`, `β = 1/2`, the rule `i = 0.5 π + 2 x` (`φ < 1`) is
determinate. -/
theorem not_necessary_witness [Nonempty Ω] : Determinate 𝔼 1 (1 / 2) 1 (1 / 2) 2 :=
  (determinate_iff_BM 𝔼 one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).mpr (by norm_num)

/-- Cochrane (2023), p. 420 ("adding `φ_x x_t` responses widens the range"): for `σ, κ > 0`,
`0 < β < 1`, every `φ ∈ [0, 1)` is made determinate by a large enough output response. -/
theorem not_necessary_phix [Nonempty Ω] {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) :
    ∃ φx, 0 ≤ φx ∧ Determinate 𝔼 σ β κ φ φx := by
  have h1β : 0 < 1 - β := by linarith
  refine ⟨κ * (1 - φ) / (1 - β) + 1, by positivity, ?_⟩
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ0 (by positivity)]
  field_simp
  nlinarith

/-- Cochrane (2023), A1 p. 587, eq. (1.58): even with `φ_x = 0`, `φ > 1` is not necessary —
`σ = κ = 1`, `β = 1/2`, `φ = −5 < −(1 + 2(1 + β)/(σκ)) = −4` is determinate. -/
theorem not_necessary_negative [Nonempty Ω] : Determinate 𝔼 1 (1 / 2) 1 (-5) 0 :=
  (determinate_iff_phi 𝔼 one_pos one_pos (by norm_num) (by norm_num)).mpr (Or.inr (by norm_num))

/-- Cochrane (2023), p. 420, Ch16 p. 369, Ch12 P8 p. 328 ("… nor sufficient"; "the coefficient
can exceed 1 while the eigenvalue is stable"): with `σ = κ = 1`, `β = 1/2`, the rule
`i = 2π − 2x` (`φ = 2 > 1`) is not determinate. -/
theorem not_sufficient_witness [Nonempty Ω] : ¬ Determinate 𝔼 1 (1 / 2) 1 2 (-2) := by
  rw [determinate_iff_explicit 𝔼 (by norm_num)]
  norm_num

/-- Cochrane (2023), p. 420: for **every** `φ` (in particular every `φ > 1`) and `σ ≠ 0` there
is an output response `φ_x = −(1 + σκφ)/σ` that makes the system indeterminate. -/
theorem not_sufficient [Nonempty Ω] {σ β κ : ℝ} (hσ : σ ≠ 0) (φ : ℝ) :
    ∃ φx, ¬ Determinate 𝔼 σ β κ φ φx := by
  refine ⟨-(1 + σ * κ * φ) / σ, fun h => ((determinate_iff 𝔼 _ _ _ _ _).mp h).1 ?_⟩
  field_simp
  ring

/-- Cochrane (2023), p. 420: with a nonnegative output response, `φ > 1` is sufficient. -/
theorem sufficient_of_phix_nonneg [Nonempty Ω] {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 1 < φ) (hφx : 0 ≤ φx) : Determinate 𝔼 σ β κ φ φx :=
  (determinate_iff_BM 𝔼 hσ hκ hβ hβ1 (by linarith) hφx).mpr
    (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) hφx])

/-- Cochrane (2023), p. 420 ("adding `φ_x x_t` responses widens the range of parameters"):
for `φ ≥ 0`, raising a nonnegative output response preserves determinacy. -/
theorem widens_with_phix [Nonempty Ω] {σ β κ φ φx φx' : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 0 ≤ φ) (hφx : 0 ≤ φx) (hle : φx ≤ φx')
    (h : Determinate 𝔼 σ β κ φ φx) : Determinate 𝔼 σ β κ φ φx' := by
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ hφx] at h
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ (hφx.trans hle)]
  nlinarith

/-! ### The matrix forms (17.33) and (1.55) -/

/-- Cochrane (2023), eq. (17.33), p. 420 (with output response): for `β ≠ 0` the deviation
system is `E_t x̃_{t+1} = β⁻¹[(β + σκ + βσφ_x) x̃_t − σ(1 − βφ) π̃_t]`,
`E_t π̃_{t+1} = β⁻¹[−κ x̃_t + π̃_t]` (with `ĩ = φπ̃ + φ_x x̃`, `r̃ = ĩ − E π̃'`); (17.33) is
`φ_x = 0`. -/
theorem deviation_iff_17_33 {σ β κ φ φx : ℝ} (hβ : β ≠ 0) (i r x π : ℕ → Ω → ℝ) :
    Deviation 𝔼 σ β κ φ φx i r x π ↔
      (∀ t, i t = φ • π t + φx • x t) ∧ (∀ t, r t = i t - 𝔼.E t (π (t + 1))) ∧
        ∀ t, 𝔼.E t (x (t + 1)) =
            β⁻¹ • ((β + σ * κ + β * σ * φx) • x t - (σ * (1 - β * φ)) • π t) ∧
          𝔼.E t (π (t + 1)) = β⁻¹ • (-κ • x t + π t) := by
  rw [deviation_iff_struct]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h t
    have e0 := h t 0
    have e1 := h t 1
    simp only [Pmat, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Qmat, one_smul, neg_smul, zero_smul,
      zero_add] at e0 e1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have f0 := congrFun e0 ω
      have f1 := congrFun e1 ω
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at f0 f1 ⊢
      rw [eq_inv_mul_iff_mul_eq₀ hβ]
      linear_combination -β * f0 + σ * f1
    · have f1 := congrFun e1 ω
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at f1 ⊢
      rw [eq_inv_mul_iff_mul_eq₀ hβ]
      linear_combination -f1
  · intro h t j
    obtain ⟨h0, h1⟩ := h t
    funext ω
    have f0 := congrFun h0 ω
    have f1 := congrFun h1 ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at f0 f1
    fin_cases j
    · simp only [Pmat, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Qmat, one_smul]
      rw [f0, f1]
      field_simp
      ring
    · simp only [Pmat, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, stack, neg_smul,
        one_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Qmat, zero_smul,
        Pi.zero_apply, zero_add]
      rw [f1]
      field_simp

/-- Cochrane (2023), A1 eq. (1.55), p. 586 (corrected): in the model (17.15)–(17.17) with
`i_t = φ π_t + u_{i,t}` and `β ≠ 0`,
`E_t x_{t+1} = β⁻¹[(β + σκ) x_t − σ(1 − βφ) π_t] + β⁻¹[−β u_{x,t} + σ u_{π,t} + σβ u_{i,t}]`,
`E_t π_{t+1} = β⁻¹[−κ x_t + π_t] − β⁻¹ u_{π,t}`. The printed shock row has `−1` in place of
`−β` for `u_x` (see `printed_1_55_iff`). -/
theorem eq_1_55 {σ β κ φ : ℝ} (hβ : β ≠ 0) {ux uπ ui i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ ux uπ i r x π) (hrule : ∀ t, i t = φ • π t + ui t) (t : ℕ) :
    𝔼.E t (x (t + 1)) = β⁻¹ • ((β + σ * κ) • x t - (σ * (1 - β * φ)) • π t) +
        β⁻¹ • (-β • ux t + σ • uπ t + (σ * β) • ui t) ∧
      𝔼.E t (π (t + 1)) = β⁻¹ • (-κ • x t + π t) - β⁻¹ • uπ t := by
  obtain ⟨his, hf, hpc⟩ := h
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · have e1 := congrFun (his t) ω
    have e2 := congrFun (hf t) ω
    have e3 := congrFun (hpc t) ω
    have e4 := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
    rw [← mul_add, eq_inv_mul_iff_mul_eq₀ hβ]
    linear_combination -β * e1 - β * σ * e2 + β * σ * e4 + σ * e3
  · have e3 := congrFun (hpc t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e3 ⊢
    rw [← mul_sub, eq_inv_mul_iff_mul_eq₀ hβ]
    linear_combination -e3

/-- Cochrane (2023), A1 eq. (1.55), p. 586, as printed: its first row, with `u_x` coefficient
`−1/β`, holds at a date and state iff `β = 1` or `u_{x,t} = 0` there — the printed shock
matrix is wrong for `β ≠ 1` (new error, not in the survey). -/
theorem printed_1_55_iff {σ β κ φ : ℝ} (hβ : β ≠ 0) {ux uπ ui i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ ux uπ i r x π) (hrule : ∀ t, i t = φ • π t + ui t) (t : ℕ) (ω : Ω) :
    𝔼.E t (x (t + 1)) ω = β⁻¹ * ((β + σ * κ) * x t ω - σ * (1 - β * φ) * π t ω) +
        β⁻¹ * (-1 * ux t ω + σ * uπ t ω + σ * β * ui t ω) ↔ β = 1 ∨ ux t ω = 0 := by
  have e := congrFun (eq_1_55 𝔼 hβ h hrule t).1 ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  rw [e]
  constructor
  · intro h'
    have : (β - 1) * ux t ω = 0 := by
      field_simp at h'
      linear_combination -h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr h1
  · rintro (h1 | h1)
    · subst h1; ring
    · rw [h1]; ring

/-! ### The eigenvalues (1.57) -/

/-- Cochrane (2023), eq. (1.57), p. 587: `tr M = (1 + β + σκ)/β` for the transition matrix `M`
of (17.33). -/
noncomputable def trM (σ β κ : ℝ) : ℝ := (1 + β + σ * κ) / β

/-- Cochrane (2023), eq. (1.57), p. 587: `det M = (1 + σκφ)/β`. -/
noncomputable def detM (σ β κ φ : ℝ) : ℝ := (1 + σ * κ * φ) / β

/-- Cochrane (2023), eq. (17.33), p. 420: the transition matrix
`M = β⁻¹ [[β + σκ, −σ(1 − βφ)], [−κ, 1]]`. -/
noncomputable def Mmat (σ β κ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(β + σ * κ) / β, -(σ * (1 - β * φ)) / β; -κ / β, 1 / β]

/-- Cochrane (2023), eq. (1.57): `tr M` and `det M`. -/
theorem tr_det_Mmat {σ β κ φ : ℝ} (hβ : β ≠ 0) :
    tr2 (Mmat σ β κ φ) = trM σ β κ ∧ det2 (Mmat σ β κ φ) = detM σ β κ φ := by
  simp only [tr2, det2, Mmat, trM, detM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor <;> field_simp <;> ring

/-- Cochrane (2023), eq. (1.57), p. 587: the discriminant
`Δ = (1 − β + σκ)² − 4βσκ(φ − 1)`. -/
def discE (σ β κ φ : ℝ) : ℝ := (1 - β + σ * κ) ^ 2 - 4 * β * σ * κ * (φ - 1)

/-- `discQ (tr M) (det M) = Δ/β²`. -/
theorem discQ_eq {σ β κ φ : ℝ} (hβ : β ≠ 0) :
    discQ (trM σ β κ) (detM σ β κ φ) = discE σ β κ φ / β ^ 2 := by
  unfold discQ trM detM discE
  field_simp
  ring

/-- Cochrane (2023), eq. (1.57), p. 587: for `β > 0` and `Δ ≥ 0` the eigenvalues of `M` are
`λ = 1 + [(1 − β + σκ) ± √Δ]/(2β)`: they are the roots `root₁`, `root₂` of the characteristic
polynomial `λ² − tr M λ + det M`. -/
theorem eq_1_57 {σ β κ φ : ℝ} (hβ : 0 < β) (hΔ : 0 ≤ discE σ β κ φ) :
    root₁ (trM σ β κ) (detM σ β κ φ) =
        ((1 + ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) : ℝ) : ℂ) ∧
      root₂ (trM σ β κ) (detM σ β κ φ) =
        ((1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) : ℝ) : ℂ) := by
  have hd := discQ_eq (σ := σ) (κ := κ) (φ := φ) hβ.ne'
  have hnn : 0 ≤ discQ (trM σ β κ) (detM σ β κ φ) := by rw [hd]; positivity
  have hs : Real.sqrt (discQ (trM σ β κ) (detM σ β κ φ)) = Real.sqrt (discE σ β κ φ) / β := by
    rw [hd, Real.sqrt_div hΔ, Real.sqrt_sq hβ.le]
  unfold root₁ root₂
  simp only [hnn, ↓reduceIte, hs]
  simp only [trM]
  constructor <;> congr 1 <;> field_simp <;> ring

/-- Cochrane (2023), A1 p. 587 ("the + eigenvalue is greater than one"): for `σκ > 0`,
`0 < β < 1` and `Δ ≥ 0`, `λ₊ > 1`. -/
theorem plus_root_gt_one {σ β κ φ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hβ1 : β < 1) :
    1 < 1 + ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) := by
  have := Real.sqrt_nonneg (discE σ β κ φ)
  have : 0 < ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) := by
    apply div_pos <;> linarith
  linarith

/-- Cochrane (2023), A1 p. 587 ("if φ < 1 the − eigenvalue is less than one") and eq. (1.58):
for `σ, κ > 0`, `0 < β < 1` and `φ < 1`, the eigenvalues are real, `λ₋ < 1`, and `λ₋ > −1`
(stable) iff `φ > −(1 + 2(1 + β)/(σκ))`; below that bound `λ₋ < −1` (oscillating
explosion). -/
theorem roots_phi_lt_one {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1)
    (hφ : φ < 1) :
    0 < discE σ β κ φ ∧ 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) < 1 ∧
      (-1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) ↔
        -(1 + 2 * (1 + β) / (σ * κ)) < φ) := by
  have ha := mul_pos hσ hκ
  have hb : 0 < 1 - β + σ * κ := by linarith
  have hgt : (1 - β + σ * κ) ^ 2 < discE σ β κ φ := by
    unfold discE
    have : 0 < 4 * β * σ * κ * (1 - φ) := by
      have := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hβ) hσ) hκ
      exact mul_pos this (by linarith)
    nlinarith
  have hsq : 1 - β + σ * κ < Real.sqrt (discE σ β κ φ) := (Real.lt_sqrt hb.le).mpr hgt
  refine ⟨lt_trans (by positivity) hgt, ?_, ?_⟩
  · have : ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  · have hc : 0 < 1 + 3 * β + σ * κ := by linarith
    have key : -1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) ↔
        Real.sqrt (discE σ β κ φ) < 1 + 3 * β + σ * κ := by
      rw [← sub_pos, show 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) - -1 =
        (1 + 3 * β + σ * κ - Real.sqrt (discE σ β κ φ)) / (2 * β) by field_simp; ring,
        div_pos_iff_of_pos_right (by linarith), sub_pos]
    rw [key, Real.sqrt_lt' hc]
    have e : (1 + 3 * β + σ * κ) ^ 2 - discE σ β κ φ =
        4 * β * (2 + 2 * β + σ * κ + σ * κ * φ) := by unfold discE; ring
    have hb2 : -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) = -(σ * κ) - 2 * (1 + β) := by
      field_simp; ring
    constructor
    · intro h
      have h4 : 0 < 4 * β * (2 + 2 * β + σ * κ + σ * κ * φ) := by linarith
      have h5 : 0 < 2 + 2 * β + σ * κ + σ * κ * φ := pos_of_mul_pos_right h4 (by linarith)
      have : -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) < φ * (σ * κ) := by rw [hb2]; linarith
      exact lt_of_mul_lt_mul_right this ha.le
    · intro h
      have := mul_lt_mul_of_pos_right h ha
      rw [hb2] at this
      have h5 : 0 < 2 + 2 * β + σ * κ + σ * κ * φ := by linarith
      nlinarith

/-- Cochrane (2023), Ch17 p. 420 ("‖φ‖ < 1 leaves one stable eigenvalue"): for `|φ| < 1`,
`−1 < λ₋ < 1 < λ₊`. -/
theorem abs_phi_lt_one_one_stable {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφ : |φ| < 1) :
    -1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) ∧
      1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) < 1 ∧
      1 < 1 + ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) := by
  rw [abs_lt] at hφ
  obtain ⟨-, h2, h3⟩ := roots_phi_lt_one hσ hκ hβ hβ1 hφ.2
  refine ⟨h3.mpr ?_, h2, plus_root_gt_one (mul_pos hσ hκ) hβ hβ1⟩
  have : 0 < 2 * (1 + β) / (σ * κ) := by have := mul_pos hσ hκ; positivity
  linarith

/-- Cochrane (2023), Ch17 p. 420 and A1 p. 587 ("if φ > 1 then both eigenvalues are greater
than one"): for `φ > 1` either the roots are real and `λ₋ > 1`, or they are complex with modulus
greater than one (survey error E11: "greater than one" must be read as modulus). -/
theorem roots_phi_gt_one {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) :
    (0 ≤ discE σ β κ φ ∧ 1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β)) ∨
      (discE σ β κ φ < 0 ∧ 1 < ‖root₁ (trM σ β κ) (detM σ β κ φ)‖ ∧
        1 < ‖root₂ (trM σ β κ) (detM σ β κ φ)‖) := by
  have ha := mul_pos hσ hκ
  have hb : 0 < 1 - β + σ * κ := by linarith
  rcases le_or_gt 0 (discE σ β κ φ) with hΔ | hΔ
  · left
    refine ⟨hΔ, ?_⟩
    have hlt : discE σ β κ φ < (1 - β + σ * κ) ^ 2 := by
      unfold discE
      have := mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hβ) hσ) hκ)
        (sub_pos.mpr hφ)
      nlinarith
    have := (Real.sqrt_lt' hb).mpr hlt
    have : 0 < ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) :=
      div_pos (by linarith) (by linarith)
    linarith
  · right
    have hneg : discQ (trM σ β κ) (detM σ β κ φ) < 0 := by
      rw [discQ_eq hβ.ne']; exact div_neg_of_neg_of_pos hΔ (by positivity)
    obtain ⟨h1, h2⟩ := normSq_root_of_neg hneg
    have hdet : 1 < detM σ β κ φ := by
      unfold detM
      rw [one_lt_div hβ]
      nlinarith
    refine ⟨hΔ, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have := norm_nonneg (root₁ (trM σ β κ) (detM σ β κ φ))
      nlinarith
    · by_contra hc
      push Not at hc
      have := norm_nonneg (root₂ (trM σ β κ) (detM σ β κ φ))
      nlinarith


/-! ### φ irrelevance (pp. 419–420) -/

/-- Cochrane (2023), eqs. (17.22)–(17.24): an equilibrium of the full model (17.15)–(17.17)
(starred form) under King's rule `i_t = i*_t + φ(π_t − π*_t)`. -/
def KingEqm (σ β κ φ : ℝ) (ux uπ istar πstar i x π : ℕ → Ω → ℝ) : Prop :=
  Starred 𝔼 σ β κ ux uπ i x π ∧ KingRule φ i istar π πstar

/-- Cochrane (2023), p. 420 ("subtracting, deviations must follow the same model … but without
constants or disturbances"): if `(i*, x*, π*)` solves the starred model and `(i, x, π)` is an
equilibrium under King's rule, the deviations solve (17.29)–(17.32). -/
theorem deviation_of_eqm {σ β κ φ : ℝ} {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar)
    (he : KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π) :
    Deviation 𝔼 σ β κ φ 0 (fun t => i t - istar t)
      (fun t => i t - istar t - 𝔼.E t (π (t + 1) - πstar (t + 1)))
      (fun t => x t - xstar t) (fun t => π t - πstar t) := by
  obtain ⟨⟨h1, h2⟩, hk⟩ := he
  obtain ⟨g1, g2⟩ := hs
  intro t
  beta_reduce
  refine ⟨by abel, ?_, ?_, ?_⟩
  · rw [h1 t, g1 t]
    simp only [map_sub, smul_sub]
    abel
  · rw [h2 t, g2 t]
    simp only [map_sub, smul_sub]
    abel
  · rw [hk t]
    simp

/-- Cochrane (2023), pp. 419–420 (φ irrelevance): if the deviation system with coefficient `φ`
is determinate (e.g. `φ > 1`, `determinate_iff_phi`), the bounded adapted equilibria under
King's rule are exactly the starred paths, whatever `φ`. -/
theorem phi_irrelevance [Nonempty Ω] {σ β κ φ : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π ↔ i = istar ∧ x = xstar ∧ π = πstar := by
  constructor
  · intro he
    have hd := deviation_of_eqm 𝔼 hs he
    have hbsub : ∀ {a b : ℕ → Ω → ℝ}, BoundedProc a → BoundedProc b →
        BoundedProc fun t => a t - b t := by
      intro a b ⟨M, hM⟩ ⟨N, hN⟩
      exact ⟨M + N, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hN t ω))⟩
    obtain ⟨h1, h2⟩ := hdet _ _ _ _ (fun t => by simp only [map_sub, hx t, hxs t])
      (fun t => by simp only [map_sub, hπ t, hπs t]) (hbsub hbx hbxs) (hbsub hbπ hbπs) hd
    have ex : x = xstar := funext fun t => sub_eq_zero.mp (congrFun h1 t)
    have eπ : π = πstar := funext fun t => sub_eq_zero.mp (congrFun h2 t)
    refine ⟨funext fun t => ?_, ex, eπ⟩
    rw [he.2 t, eπ]
    simp
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨hs, king_equilibrium _ _ _⟩

/-- Cochrane (2023), pp. 419–420 ("the parameter φ does not enter equilibrium dynamics"): for
any two coefficients `φ`, `φ'` in the determinacy region, the bounded adapted equilibria under
King's rule coincide. -/
theorem phi_irrelevance_sets [Nonempty Ω] {σ β κ φ φ' : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    (hdet' : Determinate 𝔼 σ β κ φ' 0) {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π ↔ KingEqm 𝔼 σ β κ φ' ux uπ istar πstar i x π := by
  rw [phi_irrelevance 𝔼 hdet hs hxs hπs hbxs hbπs hx hπ hbx hbπ,
    phi_irrelevance 𝔼 hdet' hs hxs hπs hbxs hbπs hx hπ hbx hbπ]

/-- Cochrane (2023), p. 418 and p. 414: with the disturbance `u_{i,t} = i*_t − φ π*_t`, the
standard rule `i_t = φ π_t + u_{i,t}` has the starred paths as its unique bounded adapted
equilibrium whenever `φ` is in the determinacy region. -/
theorem standard_rule_unique [Nonempty Ω] {σ β κ φ : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    (Starred 𝔼 σ β κ ux uπ i x π ∧ ∀ t, i t = φ • π t + (istar t - φ • πstar t)) ↔
      i = istar ∧ x = xstar ∧ π = πstar := by
  rw [← king_iff_standard]
  exact phi_irrelevance 𝔼 hdet hs hxs hπs hbxs hbπs hx hπ hbx hbπ

/-- A perfect-foresight equilibrium of `FullModel.PFEqm` solves the starred model under the
`perfectForesight` expectation system (no disturbances). -/
theorem pf_starred {σ β κ : ℝ} {i x π : ℕ → ℝ} (h : PFEqm σ β κ i x π) :
    Starred perfectForesight σ β κ 0 0 (fun t _ => i t) (fun t _ => x t) (fun t _ => π t) := by
  refine ⟨fun t => funext fun _ => ?_, fun t => funext fun _ => ?_⟩ <;>
    simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, add_zero]
  · exact (h t).1
  · exact (h t).2

/-- Cochrane (2023), p. 414 ("if fed these `{u_t}` paths, the model produces the given interest
rate and inflation paths"): for `σ, κ > 0`, `0 < β < 1`, `φ > 1`, a bounded rate path `i*` and
any initial inflation `p`, the reverse-engineered disturbance `u = i* − φ π*` (with
`π* = path p`) makes `(i*, x*, π*)` the **unique** bounded equilibrium of the model with
`i_t = φ π_t + u_t` (perfect foresight). -/
theorem reverse_engineered_unique {σ β κ φ M p : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φ) {istar : ℕ → ℝ} (hi : ∀ t, |istar t| ≤ M)
    {i x π : ℕ → Unit → ℝ} (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    (Starred perfectForesight σ β κ 0 0 i x π ∧
        ∀ t, i t = φ • π t + fun _ => istar t - φ * path σ β κ istar p t) ↔
      i = (fun t _ => istar t) ∧
        x = (fun t _ => (path σ β κ istar p t - β * path σ β κ istar p (t + 1)) / κ) ∧
        π = fun t _ => path σ β κ istar p t := by
  obtain ⟨-, -, hb, heq⟩ := FiscalUnderpinnings.reverse_engineer (φ := φ) hσ hκ hβ hi p
  have hs := pf_starred heq
  have hdet := (determinate_iff_phi perfectForesight hσ hκ hβ hβ1).mpr (Or.inl hφ)
  have hbx' : BoundedProc
      (fun t (_ : Unit) => (path σ β κ istar p t - β * path σ β κ istar p (t + 1)) / κ) := by
    obtain ⟨Mp, hMp⟩ := hb
    refine ⟨(Mp + |β| * Mp) / κ, fun t _ => ?_⟩
    rw [abs_div, abs_of_pos hκ]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    · exact hMp t
    · exact hMp (t + 1)
  have hbπ' : BoundedProc (fun t (_ : Unit) => path σ β κ istar p t) := by
    obtain ⟨Mp, hMp⟩ := hb
    exact ⟨Mp, fun t _ => hMp t⟩
  have := standard_rule_unique perfectForesight hdet hs (fun _ => rfl) (fun _ => rfl) hbx'
    hbπ' (x := x) (π := π) (i := i) (fun _ => rfl) (fun _ => rfl) hbx hbπ
  rw [← this]
  refine and_congr_right fun _ => forall_congr' fun t => ?_
  constructor <;> intro h <;> rw [h] <;> funext u <;> simp [smul_eq_mul]

/-! ### Real explosions (p. 421) -/

/-- Cochrane (2023), p. 421 ("nominal explosions can also be real explosions … faster than the
interest rate so `E_t βʲ x_{t+j} → ∞`"): for `σ, κ > 0`, `β > 0` and `φ < 1/β` — in
particular for `1 < φ < 1/β`, where the deviation system is determinate and this path is one
of the explosions ruled out — the deviation system (17.29)–(17.32) has a perfect-foresight
solution with `βᵗ x̃_t → −∞`, which violates a real transversality condition. -/
theorem real_explosion {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hφβ : φ < 1 / β) :
    ∃ x π : ℕ → ℝ,
      Deviation perfectForesight σ β κ φ 0 (fun t _ => φ * π t)
        (fun t _ => φ * π t - π (t + 1)) (fun t _ => x t) (fun t _ => π t) ∧
      Tendsto (fun t => β ^ t * x t) atTop atBot := by
  have ha := mul_pos hσ hκ
  obtain ⟨μ, hμ1, hroot⟩ : ∃ μ : ℝ, 1 < μ ∧
      μ ^ 2 - (1 + β + σ * κ) * μ + β * (1 + σ * κ * φ) = 0 := by
    set A := 1 + β + σ * κ with hA
    set B := β * (1 + σ * κ * φ) with hB
    have hβφ : β * φ < 1 := by rwa [lt_div_iff₀ hβ, mul_comm] at hφβ
    have hq1 : 1 - A + B < 0 := by
      have : σ * κ * (β * φ - 1) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
      nlinarith
    have hdisc : (A - 2) ^ 2 < A ^ 2 - 4 * B := by nlinarith
    have hsq2 : Real.sqrt (A ^ 2 - 4 * B) ^ 2 = A ^ 2 - 4 * B :=
      Real.sq_sqrt (by nlinarith [sq_nonneg (A - 2)])
    have hlt : |A - 2| < Real.sqrt (A ^ 2 - 4 * B) :=
      (Real.lt_sqrt (abs_nonneg _)).mpr (by rw [sq_abs]; exact hdisc)
    refine ⟨(A + Real.sqrt (A ^ 2 - 4 * B)) / 2, ?_, ?_⟩
    · have := neg_abs_le (A - 2)
      linarith
    · nlinarith [hsq2]
  have hβ0 : β ≠ 0 := hβ.ne'
  have hβμ : β * (μ / β) = μ := mul_div_cancel₀ μ hβ0
  have hbr : (1 - μ) - (1 - μ) * (μ / β) + σ * φ * κ - σ * κ * (μ / β) = 0 := by
    field_simp
    linear_combination hroot
  refine ⟨fun t => (1 - μ) * (μ / β) ^ t, fun t => κ * (μ / β) ^ t, fun t => ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> funext u <;>
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]
    · ring
    · rw [pow_succ]
      linear_combination ((μ / β) ^ t) * hbr
    · rw [pow_succ]
      linear_combination (-(κ * (μ / β) ^ t)) * hβμ
  · have h1 : Tendsto (fun t : ℕ => μ ^ t) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hμ1
    have h2 := h1.const_mul_atTop_of_neg (by linarith : 1 - μ < 0)
    refine h2.congr fun t => ?_
    simp only [div_pow]
    field_simp

end Cochrane.KeynesianStickyPrices.TaylorDeterminacy

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# History and implications

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 18, "History and
implications", pp. 422–432: the precise claims.

* Footnote 1, p. 424 (the Lucas critique): in the permanent-income model
  `c_t = r k_t + rβ E_t ∑ βʲ y_{t+j}` with `β = 1/(1 + r)` and AR(1) income,
  `c_t = r k_t + rβ/(1 − βη) y_t = r k_t + r/(1 + r − η) y_t` (`pih_consumption`, `mpc_eq`): the
  marginal propensity to consume depends on the persistence `η` (`mpc_strictMonoOn`,
  `mpc_injective`) — it is "a mongrel, … not a structural parameter".
* (18.1), p. 427: the Taylor rule with an output response (`Rule181`); in the three-equation
  model with `φ_π, φ_x ≥ 0` its equilibrium is determinate iff `κ(φ_π − 1) + (1 − β)φ_x > 0`
  (`rule181_determinate_iff`), so `φ_π > 1` "gives the eigenvalue you need"
  (`rule181_phi_gt_one`).
* (18.2), p. 427: the inertial, forward-looking rule (`Rule182`); with `φ_i = 0` and the rest
  zero it is (18.1) (`rule182_reduces`); without inertia its deviation system is a structural
  system `P x̃_t = Q E_t x̃_{t+1}` (`rule182_deviation_iff`), determinate iff `det P ≠ 0` and
  `P⁻¹Q` is Schur stable (`rule182_determinate_iff`).
* (18.3), p. 427, "write it King's way, and the likelihood function will be flat": any function
  of the equilibrium paths takes the same value for every `φ` in the determinacy region
  (`likelihood_flat`).
* p. 428, Clarida–Galí–Gertler: `φ_π > 1` means determinacy, but `φ_π < 1` means multiple
  equilibria only if the output response is small, `(1 − β)φ_x ≤ κ(1 − φ_π)` (`cgg_reading`).
-/

namespace Cochrane.KeynesianStickyPrices.History

open Filter Topology OptimalPolicy TaylorDeterminacy
open SharedTools (Pmat solvedA det2_Pmat)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The permanent-income footnote (p. 424) -/

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424: the marginal propensity to consume out of
current income, `r/(1 + r − η)`. -/
noncomputable def mpc (r η : ℝ) : ℝ := r / (1 + r - η)

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424: with `β = 1/(1 + r)`,
`rβ/(1 − βη) = r/(1 + r − η)`. -/
theorem mpc_eq {r η : ℝ} (hr : 0 < r) (hη : η < 1 + r) :
    r * (1 / (1 + r)) / (1 - 1 / (1 + r) * η) = mpc r η := by
  unfold mpc
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : 1 + r - η ≠ 0 := by linarith
  field_simp

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424: in the rational-expectations permanent-income
model `c_t = r k_t + rβ E_t ∑_{j≥0} βʲ y_{t+j}` with `β = 1/(1 + r)`, `r > 0`, and AR(1) income
`E_t y_{t+1} = η y_t` with `|η| ≤ 1`, consumption is the Keynesian consumption function
`c_t = r k_t + r/(1 + r − η) · y_t`. -/
theorem pih_consumption {r η : ℝ} (hr : 0 < r) (hη : |η| ≤ 1) {y k : ℕ → Ω → ℝ}
    (hy : 𝔼.IsAR1 η y) (t : ℕ) (ω : Ω) :
    Summable (fun j => (1 / (1 + r)) ^ j * 𝔼.E t (y (t + j)) ω) ∧
      r * k t ω + r * (1 / (1 + r)) * ∑' j, (1 / (1 + r)) ^ j * 𝔼.E t (y (t + j)) ω =
        r * k t ω + mpc r η * y t ω := by
  have hβ0 : 0 < 1 / (1 + r) := by positivity
  have hβ1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hq : |1 / (1 + r) * η| < 1 := by
    rw [abs_mul, abs_of_pos hβ0]
    calc 1 / (1 + r) * |η| ≤ 1 / (1 + r) * 1 := by gcongr
      _ < 1 := by linarith
  have hterm : ∀ j, (1 / (1 + r)) ^ j * 𝔼.E t (y (t + j)) ω = y t ω * (1 / (1 + r) * η) ^ j := by
    intro j
    rw [𝔼.ar1_iterate hy t j, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  simp_rw [hterm]
  refine ⟨(summable_geometric_of_abs_lt_one hq).mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hq, ← mpc_eq hr (by
    have := (abs_le.mp hη).2; linarith)]
  have : 1 - 1 / (1 + r) * η ≠ 0 := by
    have := (abs_lt.mp hq).2
    linarith
  field_simp

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424 ("if policy changes the persistence of income
… the marginal propensity to consume changes"): for `r > 0` the MPC is strictly increasing in
the persistence `η` on `η < 1 + r`. -/
theorem mpc_strictMonoOn {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (mpc r) (Set.Iio (1 + r)) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  unfold mpc
  apply div_lt_div_of_pos_left hr (by linarith) (by linarith)

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424 ("the marginal propensity to consume is a
'mongrel'"): different persistences give different MPCs. -/
theorem mpc_injective {r η η' : ℝ} (hr : 0 < r) (hη : η < 1 + r) (hη' : η' < 1 + r)
    (hne : η ≠ η') : mpc r η ≠ mpc r η' :=
  ((mpc_strictMonoOn hr).injOn).ne (Set.mem_Iio.mpr hη) (Set.mem_Iio.mpr hη') hne

/-! ### The rules (18.1)–(18.3) -/

/-- Cochrane (2023), eq. (18.1), p. 427: `i_t = φ_π π_t + φ_x x_t + u_{i,t}`. -/
def Rule181 (φπ φx : ℝ) (u i x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = φπ • π t + φx • x t + u t

/-- Cochrane (2023), eq. (18.2), p. 427:
`i_t = φ_i i_{t−1} + φ_π π_t + φ_x x_t + φ_{π,1} E_t π_{t+1} + φ_{x,1} E_t x_{t+1} + u_{i,t}`
(from date 1 on). -/
def Rule182 (φi φπ φx φπ1 φx1 : ℝ) (u i x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i (t + 1) = φi • i t + φπ • π (t + 1) + φx • x (t + 1) +
    φπ1 • 𝔼.E (t + 1) (π (t + 2)) + φx1 • 𝔼.E (t + 1) (x (t + 2)) + u (t + 1)

/-- Cochrane (2023), eqs. (18.1)–(18.2): with no inertia and no forward responses, (18.2) is
(18.1) (from date 1 on). -/
theorem rule182_reduces (φπ φx : ℝ) (u i x π : ℕ → Ω → ℝ) :
    Rule182 𝔼 0 φπ φx 0 0 u i x π ↔ ∀ t, i (t + 1) = φπ • π (t + 1) + φx • x (t + 1) + u (t + 1) :=
  by simp [Rule182]

/-- Cochrane (2023), p. 427 ("you discover … that φ_π > 1 gives the eigenvalue you need for a
unique linearized solution"), restated: in the three-equation model with (18.1), `σ, κ > 0`,
`0 < β < 1`, `φ_π, φ_x ≥ 0`, the deviation system is determinate iff
`κ(φ_π − 1) + (1 − β)φ_x > 0`. -/
theorem rule181_determinate_iff [Nonempty Ω] {σ β κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Determinate 𝔼 σ β κ φπ φx ↔ 0 < κ * (φπ - 1) + (1 - β) * φx :=
  determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφπ hφx

/-- Cochrane (2023), p. 427: with `φ_x ≥ 0`, `φ_π > 1` in (18.1) delivers determinacy. -/
theorem rule181_phi_gt_one [Nonempty Ω] {σ β κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hφx : 0 ≤ φx) : Determinate 𝔼 σ β κ φπ φx :=
  sufficient_of_phix_nonneg 𝔼 hσ hκ hβ hβ1 hφπ hφx

/-- Cochrane (2023), eq. (18.2), p. 427, without inertia: the structural matrix
`P = [[1 + σφ_x, σφ_π], [−κ, 1]]` and `Q = [[1 − σφ_{x,1}, σ(1 − φ_{π,1})], [0, β]]`. -/
def Q182 (σ β φπ1 φx1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - σ * φx1, σ * (1 - φπ1); 0, β]

/-- Cochrane (2023), eq. (18.2), p. 427: deviations under the forward-looking rule without
inertia, `ĩ = φ_π π̃ + φ_x x̃ + φ_{π,1} E π̃' + φ_{x,1} E x̃'`, with `x̃ = E x̃' − σ(ĩ − E π̃')`
and `π̃ = β E π̃' + κ x̃`, form the structural system `P x̃_t = Q E_t x̃_{t+1}`. -/
theorem rule182_deviation_iff (σ β κ φπ φx φπ1 φx1 : ℝ) (x π : ℕ → Ω → ℝ) :
    (∀ t, x t = 𝔼.E t (x (t + 1)) - σ • ((φπ • π t + φx • x t + φπ1 • 𝔼.E t (π (t + 1)) +
        φx1 • 𝔼.E t (x (t + 1))) - 𝔼.E t (π (t + 1))) ∧
      π t = β • 𝔼.E t (π (t + 1)) + κ • x t) ↔
      StructSolves 𝔼 (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1) (stack x π) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp only [Pmat, Q182, stack, Fin.zero_eta, Fin.isValue, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1
    · simp only [Pmat, Q182, stack, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      linear_combination e2
  · intro h t
    have e0 := h t 0
    have e1 := h t 1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have f := congrFun e0 ω
      simp only [Pmat, Q182, stack, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] at f
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination f
    · have f := congrFun e1 ω
      simp only [Pmat, Q182, stack, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] at f
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination f

/-- Cochrane (2023), eq. (18.2), p. 427, without inertia: the deviation system is determinate iff
`det P = 1 + σφ_x + σκφ_π ≠ 0` and `P⁻¹Q` satisfies the Schur–Cohn condition. -/
theorem rule182_determinate_iff [Nonempty Ω] (σ β κ φπ φx φπ1 φx1 : ℝ) :
    StructDeterminate 𝔼 (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1) ↔
      1 + σ * φx + σ * κ * φπ ≠ 0 ∧
        SchurStable (tr2 (solvedA (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1)))
          (det2 (solvedA (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1))) := by
  rw [structDeterminate_iff, det2_Pmat]

/-- Cochrane (2023), eq. (18.3) and p. 427 ("write it King's way, and the likelihood function
will be flat"): for any statistic `L` of the equilibrium paths, and any `φ`, `φ'` in the
determinacy region, `L` takes the same value on the bounded adapted equilibria under King's
rule with `φ` and with `φ'`. -/
theorem likelihood_flat [Nonempty Ω] {σ β κ φ φ' : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    (hdet' : Determinate 𝔼 σ β κ φ' 0) {ux uπ istar xstar πstar : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    {β' : Type*} (L : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → β')
    {i x π i' x' π' : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x)
    (hbπ : BoundedProc π) (hx' : 𝔼.Adapted x') (hπ' : 𝔼.Adapted π') (hbx' : BoundedProc x')
    (hbπ' : BoundedProc π') (he : KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π)
    (he' : KingEqm 𝔼 σ β κ φ' ux uπ istar πstar i' x' π') : L i x π = L i' x' π' := by
  obtain ⟨rfl, rfl, rfl⟩ := (phi_irrelevance 𝔼 hdet hs hxs hπs hbxs hbπs hx hπ hbx hbπ).mp he
  obtain ⟨rfl, rfl, rfl⟩ :=
    (phi_irrelevance 𝔼 hdet' hs hxs hπs hbxs hbπs hx' hπ' hbx' hbπ').mp he'
  rfl

/-- Cochrane (2023), p. 428 (Clarida, Galí and Gertler: "φ_π < 1 means multiple-equilibrium
volatility, and φ_π > 1 means determinacy"): with `φ_π ∈ [0, 1)` and `φ_x ≥ 0` the equilibrium
is indeterminate iff `(1 − β)φ_x ≤ κ(1 − φ_π)`, so the reading holds for small output
responses only. -/
theorem cgg_reading [Nonempty Ω] {σ β κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    ¬ Determinate 𝔼 σ β κ φπ φx ↔ (1 - β) * φx ≤ κ * (1 - φπ) := by
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφπ hφx, not_lt]
  constructor <;> intro h <;> linarith

end Cochrane.KeynesianStickyPrices.History

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Links between the simple-model and full-model formalisations of Chapter 17

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, pp. 397–421, Chapter 18,
p. 427, and Online Appendix A1, §1.8 and §1.13.1, pp. 571–572 and 586–588. The chapter was
formalised in two chains: the simple sticky-price model (17.1)–(17.14) with A1 §1.8/§1.13.1
(`StaticIS`, `RulesAdaptiveRE`, `AR1Responses`, `PersistenceFreedom`, `AdaptiveTaylor`) and
the full model (17.15)–(17.33) with Chapter 18 (`FullModel`, `FiscalUnderpinnings`,
`OptimalPolicy`, `TaylorDeterminacy`, `History`). This module proves that they talk about the
same objects.

* Innovations (pp. 400, 405, 411): the simple model's expectational error `reErr` is the
  innovation `FiscalUnderpinnings.innov` of an adapted process (`reErr_eq_innov`); the
  announcement-date surprise of `PersistenceFreedom.any_sign` is an innovation
  (`any_sign_innov`).
* The simple model is the `β = 0` case of the full model, exactly:
  - (17.18) under perfect foresight at `β = 0` is (17.7) with no expectational errors
    (`second_beta_zero_iff`), and on `ℤ` its bounded solutions are the backward moving average
    (17.8) (`secondZ_beta_zero`) — the `β = 0` end of `FullModel.secondZ_unique`;
  - the deviation system (17.29)–(17.32) at `β = 0` is the rational-expectations model with
    the rule, (17.11) (`deviation_beta_zero`), and determinacy of the full model at `β = 0`
    (`TaylorDeterminacy.Determinate`) is exactly the corrected E7 condition
    `φ > 1 ∨ φ < −1 − 2/(σκ)` (`determinate_beta_zero_iff`), i.e. `REDeterminate`
    (`determinate_beta_zero_iff_reDeterminate`);
  - the (1.58) bound `−(1 + 2(1+β)/(σκ))` equals the E7 bound `−1 − 2/(σκ)` at `β = 0`
    (`bound_1_58_beta_zero`), lies strictly below it for `β > 0` (`bound_1_58_lt`) and tends to
    it as `β → 0` (`tendsto_bound_1_58`).
* The (1.55) matrix: `AR1Responses.transA` is by definition `solvedA (Pmat σ κ φ 0) (Qmat σ β)`
  (`transA_eq_solvedA`), the inverse of the matrix `M` of (17.33) (`Mmat_mul_transA`).
  Determinacy is Schur stability of `transA` (`determinate_iff_transA`), so the MSV
  uniqueness of A1 p. 588 holds on the whole determinacy region (1.58), not only for `φ > 1`
  (`msv_unique_of_determinate`).
* E11: the lag-operator roots of A1 §1.8 (chain A) and the eigenvalues (1.57) (chain B) are
  reciprocal (`inv_mem_roots`, `discQ_div`), so `lag_roots_norm_lt_one` gives both eigenvalues
  of modulus above one for `φ > 1` (`eigen_norm_gt_one`); the complex example of
  `lag_roots_complex_example` is in the complex branch of `roots_phi_gt_one`
  (`complex_example_discE`).
* The three-equation model of A1 §1.13.1 is the full model with the rule substituted
  (`threeEq_iff_model`). Open mouth (p. 416): `λ₂ = β η*` (`lam2_eq_beta_mul_etaStar`), and
  with `i ≡ 0` every perfect-foresight equilibrium decays at rate `η*` (`openMouth_path`);
  super-Fisherian (p. 415): a constant rate gives the constant inflation path
  (`superFisher_path`).
* Fig. 17.5 vs p. 405/410: the path anticipated from the infinite past is the member of the
  `full_any_sign` family with initial value `zPath T 0` (`zPath_eq_path`), and every other
  initial jump differs from it by `(c − zPath T 0) λ₁^{−n}` (`path_sub_zPath`).
* History (18.1)–(18.2) (p. 427): the deviation system is the model with the rule (18.1)
  (`deviation_iff_rule181`); (18.2) without forward responses has `Q = Qmat`
  (`Q182_no_forward`) and the same determinacy condition (`rule182_determinate_iff_determinate`).
-/

namespace Cochrane.KeynesianStickyPrices.Links

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Innovations -/

/-- Cochrane (2023), p. 400 and eq. (17.19), p. 411: for an adapted process the expectational
error of the simple model, `δ_{t+1} = π_{t+1} − E_t π_{t+1}` (`StaticIS.reErr`), is the
innovation `ΔE_{t+1} π_{t+1} = E_{t+1} π_{t+1} − E_t π_{t+1}` (`FiscalUnderpinnings.innov`). -/
theorem reErr_eq_innov {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (t : ℕ) :
    StaticIS.reErr 𝔼 π (t + 1) = FiscalUnderpinnings.innov 𝔼 t (π (t + 1)) := by
  change π (t + 1) - 𝔼.E t (π (t + 1)) = 𝔼.E (t + 1) (π (t + 1)) - 𝔼.E t (π (t + 1))
  rw [hπ (t + 1)]

/-- Cochrane (2023), p. 405 and p. 411: in `PersistenceFreedom.any_sign` the announcement-date
surprise is the innovation, `ΔE_1 π*_1 = c ε`. -/
theorem any_sign_innov {σ κ Mg Mε : ℝ} (hσκ : 0 < σ * κ) {ε : Ω → ℝ}
    (hε0 : 𝔼.E 0 ε = 0) (hε1 : 𝔼.E 1 ε = ε) (hεb : ∀ ω, |ε ω| ≤ Mε) {g : ℕ → ℝ}
    (hg : ∀ t, |g t| ≤ Mg) (c : ℝ) :
    FiscalUnderpinnings.innov 𝔼 0
      (PersistenceFreedom.shockInfl (PersistenceFreedom.targetPath σ κ g c) ε 1) = c • ε := by
  obtain ⟨hm, -, -, hd⟩ := PersistenceFreedom.any_sign 𝔼 hσκ hε0 hε1 hεb hg c
  rw [← reErr_eq_innov 𝔼 hm.1 0]
  exact hd

/-! ### The simple model is the `β = 0` case of the full model -/

/-- Cochrane (2023), eqs. (17.18), p. 408, and (17.7), p. 398: under perfect foresight, (17.18)
with `β = 0` is (17.7) with no expectational errors,
`π_{t+1} = π_t/(1+σκ) + σκ/(1+σκ) i_t`. -/
theorem second_beta_zero_iff {σ κ : ℝ} (hσκ : 1 + σ * κ ≠ 0) (i π : ℕ → ℝ) :
    FullModel.Second σ 0 κ i π ↔
      ∀ t, π (t + 1) = 1 / (1 + σ * κ) * π t + σ * κ / (1 + σ * κ) * i t := by
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), eq. (17.8), p. 400, and Fig. 17.5, p. 409: on `ℤ`, every bounded solution
of (17.18) with `β = 0` (bounded rate path) is the backward moving average (17.8) with no
expectational errors, `π_{t+1} = σκ/(1+σκ) ∑_j (1+σκ)^{−j} i_{t−j}` — the `β = 0` counterpart of
the infinite-past uniqueness `FullModel.secondZ_unique` (proved there for `β > 0`). -/
theorem secondZ_beta_zero {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → ℝ}
    (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi) (h : FullModel.SecondZ σ 0 κ i π) (t : ℤ) :
    π (t + 1) = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have e := StaticIS.eq_17_8 hσκ hπ hi (δ := fun _ => 0) (Mδ := 0) (fun _ => by simp)
    (fun s => by
      have hs := h s
      field_simp
      linear_combination -hs) t
  simpa using e

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, and (17.11), p. 402: at `β = 0` the
deviation system of the full model with `i = φπ` is the rational-expectations simple model with
the rule, (17.11) with no disturbance (for adapted `π`, `κ ≠ 0`). -/
theorem deviation_beta_zero {σ κ φ : ℝ} (hκ : κ ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (hπ : 𝔼.Adapted π) (h : TaylorDeterminacy.Deviation 𝔼 σ 0 κ φ 0 i r x π) :
    RulesAdaptiveRE.RERule 𝔼 σ κ φ 0 π := by
  have hx : ∀ t, x t = κ⁻¹ • π t := fun t => by
    rw [(h t).2.2.1, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  refine ⟨hπ, fun t ω => ?_⟩
  obtain ⟨h1, h2, -, h4⟩ := h t
  have e1 := congrFun h1 ω
  have e2 := congrFun h2 ω
  have e4 := congrFun h4 ω
  have ex := congrFun (hx t) ω
  have ex' : 𝔼.E t (x (t + 1)) ω = κ⁻¹ * 𝔼.E t (π (t + 1)) ω := by
    rw [hx (t + 1), map_smul]; rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_mul,
    add_zero] at e1 e2 e4 ex
  simp only [Pi.zero_apply, add_zero]
  rw [ex, ex'] at e2
  have hk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  linear_combination κ * e2 + σ * κ * e1 - σ * κ * e4 - (π t ω - 𝔼.E t (π (t + 1)) ω) * hk

/-- Cochrane (2023), p. 402 (E7) and A1 p. 587: at `β = 0` the full model's determinacy
condition (`TaylorDeterminacy.determinate_iff`) is exactly the corrected E7 condition of the
simple model, `φ > 1 ∨ φ < −1 − 2/(σκ)`. -/
theorem determinate_beta_zero_iff [Nonempty Ω] {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    TaylorDeterminacy.Determinate 𝔼 σ 0 κ φ 0 ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [TaylorDeterminacy.determinate_iff, ← RulesAdaptiveRE.abs_lt_abs_iff hσκ]
  simp only [mul_zero, add_zero, zero_div, SchurStable, abs_zero, zero_lt_one, true_and,
    zero_mul]
  constructor
  · rintro ⟨hD, h⟩
    rwa [abs_div, div_lt_one (abs_pos.mpr hD)] at h
  · intro h
    have hD : 1 + σ * κ * φ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      exact absurd h (not_lt.mpr (abs_nonneg _))
    exact ⟨hD, by rwa [abs_div, div_lt_one (abs_pos.mpr hD)]⟩

/-- Cochrane (2023), p. 402 and p. 420: at `β = 0` the full model is determinate exactly when the
simple model (17.11) is (`RulesAdaptiveRE.reDeterminate_iff`). -/
theorem determinate_beta_zero_iff_reDeterminate [Nonempty Ω] {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    TaylorDeterminacy.Determinate 𝔼 σ 0 κ φ 0 ↔ RulesAdaptiveRE.REDeterminate 𝔼 σ κ φ := by
  rw [determinate_beta_zero_iff 𝔼 hσκ, RulesAdaptiveRE.reDeterminate_iff 𝔼 hσκ]

/-- Cochrane (2023), eq. (1.58), A1 p. 587, and p. 402: at `β = 0` the lower determinacy bound
`−(1 + 2(1+β)/(σκ))` is the E7 bound `−1 − 2/(σκ)`. -/
theorem bound_1_58_beta_zero (σ κ : ℝ) :
    -(1 + 2 * (1 + 0) / (σ * κ)) = -1 - 2 / (σ * κ) := by ring

/-- Cochrane (2023), eq. (1.58), A1 p. 587: for `β > 0` the full-model bound lies strictly below
the simple-model bound, `−(1 + 2(1+β)/(σκ)) < −1 − 2/(σκ)`. -/
theorem bound_1_58_lt {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ : 0 < β) :
    -(1 + 2 * (1 + β) / (σ * κ)) < -1 - 2 / (σ * κ) := by
  have : 2 / (σ * κ) < 2 * (1 + β) / (σ * κ) :=
    div_lt_div_of_pos_right (by linarith) hσκ
  linarith

/-- Cochrane (2023), eq. (1.58), A1 p. 587: as `β → 0` the full-model bound tends to the
simple-model bound `−1 − 2/(σκ)`. -/
theorem tendsto_bound_1_58 (σ κ : ℝ) :
    Tendsto (fun β : ℝ => -(1 + 2 * (1 + β) / (σ * κ))) (𝓝 0) (𝓝 (-1 - 2 / (σ * κ))) := by
  have hc : Continuous (fun β : ℝ => -(1 + 2 * (1 + β) / (σ * κ))) := by fun_prop
  have h := hc.tendsto 0
  rwa [bound_1_58_beta_zero] at h

/-! ### The (1.55) matrix and MSV uniqueness -/

/-- Cochrane (2023), A1 eq. (1.55), p. 586, and p. 420: the transition matrix of chain A is the
solved structural matrix `P⁻¹Q` of the determinacy analysis at `φ_x = 0`. -/
theorem transA_eq_solvedA (σ κ β φ : ℝ) :
    AR1Responses.transA σ κ β φ =
      SharedTools.solvedA (SharedTools.Pmat σ κ φ 0) (SharedTools.Qmat σ β) := rfl

/-- Cochrane (2023), eq. (17.33), p. 420, and A1 eq. (1.55), p. 586: the matrix `M` of (17.33)
(`E_t x_{t+1} = M x_t`) is the inverse of the forward-looking transition matrix `A`. -/
theorem Mmat_mul_transA {σ κ β φ : ℝ} (hβ : β ≠ 0) (hD : 1 + σ * κ * φ ≠ 0) :
    TaylorDeterminacy.Mmat σ β κ φ * AR1Responses.transA σ κ β φ = 1 := by
  have hD' : 1 + κ * σ * φ ≠ 0 := by rwa [show κ * σ * φ = σ * κ * φ by ring]
  rw [AR1Responses.transA_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TaylorDeterminacy.Mmat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Cochrane (2023), p. 420 and A1 p. 587: the deviation system (17.29)–(17.32) is determinate
iff `1 + σκφ ≠ 0` and the transition matrix `A` of (1.55) (`AR1Responses.transA`) is Schur
stable. -/
theorem determinate_iff_transA [Nonempty Ω] (σ κ β φ : ℝ) :
    TaylorDeterminacy.Determinate 𝔼 σ β κ φ 0 ↔
      1 + σ * κ * φ ≠ 0 ∧
        SchurStable (tr2 (AR1Responses.transA σ κ β φ)) (det2 (AR1Responses.transA σ κ β φ)) := by
  rw [TaylorDeterminacy.determinate_iff_struct, TaylorDeterminacy.structDeterminate_iff,
    SharedTools.det2_Pmat, transA_eq_solvedA]
  simp only [mul_zero, add_zero]

/-- Cochrane (2023), A1 pp. 587–588 (MSV uniqueness) on the whole determinacy region (1.58):
whenever the deviation system is determinate (`TaylorDeterminacy.determinate_iff_phi`: `φ > 1`
or `φ < −(1 + 2(1+β)/(σκ))`) and the MSV denominator is nonzero, the minimal-state-variable
solution is the unique bounded equilibrium of the three-equation model with a bounded AR(1)
disturbance. `AR1Responses.msv_unique` is the case `φ > 1`. -/
theorem msv_unique_of_determinate [Nonempty Ω] {σ κ β φ η M : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hdet : TaylorDeterminacy.Determinate 𝔼 σ β κ φ 0)
    (hD : AR1Responses.denF σ κ β φ η ≠ 0) {u x π : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hM : ∀ t ω, |u t ω| ≤ M) (h : AR1Responses.ThreeEq 𝔼 σ κ β φ u x π)
    (hxb : BoundedProc x) (hπb : BoundedProc π) :
    π = (fun t => (-1 / AR1Responses.denF σ κ β φ η) • u t) ∧
      x = (fun t => ((1 - β * η) / κ * (-1 / AR1Responses.denF σ κ β φ η)) • u t) := by
  obtain ⟨hMM, hS⟩ := (determinate_iff_transA 𝔼 σ κ β φ).mp hdet
  obtain ⟨h1, h2⟩ := (AR1Responses.eq_1_59_iff hσ hκ hD).mpr ⟨rfl, rfl⟩
  have hs := AR1Responses.msv_solves 𝔼 hu h1 h2
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπ, hMπ⟩ := hπb
  set aπ := -1 / AR1Responses.denF σ κ β φ η
  set ax := (1 - β * η) / κ * aπ
  have e := 𝔼.system_unique hS (AR1Responses.threeEq_solves 𝔼 hMM h)
    (AR1Responses.threeEq_solves 𝔼 hMM hs)
    (fun t j => by fin_cases j <;> simp [h.1 t, h.2.1 t])
    (fun t j => by fin_cases j <;> simp [hs.1 t, hs.2.1 t])
    ⟨max Mx Mπ, fun t j ω => by
      fin_cases j
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMπ t ω).trans (le_max_right _ _)⟩
    ⟨max (|ax| * M) (|aπ| * M), fun t j ω => by
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_left _ _)
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
          smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_right _ _)⟩
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · simpa using congrFun (congrFun e t) 1
  · simpa using congrFun (congrFun e t) 0

/-! ### E11: lag roots and eigenvalues are reciprocal -/

/-- Cochrane (2023), A1 §1.8, p. 572, and eq. (1.57), p. 587: if `z` is a root of
`z² − Tz + D` with `D ≠ 0`, then `1/z` is a root of `λ² − (T/D)λ + 1/D`. -/
theorem inv_mem_roots {T D : ℝ} (hD : D ≠ 0) {z : ℂ}
    (hz : z = root₁ T D ∨ z = root₂ T D) :
    z⁻¹ = root₁ (T / D) (1 / D) ∨ z⁻¹ = root₂ (T / D) (1 / D) := by
  have hq := root_eq T D z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    have : (D : ℂ) = 0 := by simpa using hq
    exact hD (by exact_mod_cast this)
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  refine eq_root_of_eq ?_
  push_cast
  field_simp
  linear_combination hq

/-- Cochrane (2023), A1 p. 572 and p. 587: the discriminants of the two quadratics have the same
sign, `discQ (T/D) (1/D) = discQ T D / D²`. -/
theorem discQ_div {T D : ℝ} (hD : D ≠ 0) : discQ (T / D) (1 / D) = discQ T D / D ^ 2 := by
  unfold discQ
  field_simp

/-- Cochrane (2023), eq. (1.57), p. 587: `tr M = tr A/det A` and `det M = 1/det A` for the
lag-polynomial coefficients `T = (1+β+σκ)/(1+σκφ)`, `D = β/(1+σκφ)` of A1 §1.8. -/
theorem trM_detM_eq {σ β κ φ : ℝ} (hβ : β ≠ 0) (hM : 1 + σ * κ * φ ≠ 0) :
    TaylorDeterminacy.trM σ β κ =
        (1 + β + σ * κ) / (1 + σ * κ * φ) / (β / (1 + σ * κ * φ)) ∧
      TaylorDeterminacy.detM σ β κ φ = 1 / (β / (1 + σ * κ * φ)) := by
  unfold TaylorDeterminacy.trM TaylorDeterminacy.detM
  constructor <;> field_simp

/-- Cochrane (2023), Ch17 p. 420 and A1 p. 587 (survey error E11, unified): for `φ > 1` both
eigenvalues of (1.57) have modulus strictly above one, real or complex — derived from the
chain-A statement `AR1Responses.lag_roots_norm_lt_one` by reciprocity. -/
theorem eigen_norm_gt_one {σ β κ φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) :
    1 < ‖root₁ (TaylorDeterminacy.trM σ β κ) (TaylorDeterminacy.detM σ β κ φ)‖ ∧
      1 < ‖root₂ (TaylorDeterminacy.trM σ β κ) (TaylorDeterminacy.detM σ β κ φ)‖ := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  set T := (1 + β + σ * κ) / (1 + σ * κ * φ)
  set D := β / (1 + σ * κ * φ)
  have hD : D ≠ 0 := (div_pos hβ0 hM).ne'
  have hD' : 1 / D ≠ 0 := one_div_ne_zero hD
  obtain ⟨htr, hdet⟩ := trM_detM_eq (φ := φ) (κ := κ) (σ := σ) hβ0.ne' hM.ne'
  obtain ⟨hA1, hA2⟩ := AR1Responses.lag_roots_norm_lt_one hσκ hβ0 hβ1 hφ
  have back : ∀ w : ℂ, (w = root₁ (T / D) (1 / D) ∨ w = root₂ (T / D) (1 / D)) → 1 < ‖w‖ := by
    intro w hw
    have hinv := inv_mem_roots hD' hw
    rw [show T / D / (1 / D) = T by field_simp, one_div_one_div] at hinv
    have hlt : ‖w⁻¹‖ < 1 := by rcases hinv with h | h <;> rw [h] <;> assumption
    have hw0 : w ≠ 0 := by
      rintro rfl
      have := root_eq (T / D) (1 / D) 0 hw
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
        zero_add] at this
      exact hD' (by exact_mod_cast this)
    rw [norm_inv] at hlt
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rwa [inv_lt_one₀ hpos] at hlt
  rw [htr, hdet]
  exact ⟨back _ (Or.inl rfl), back _ (Or.inr rfl)⟩

/-- Cochrane (2023), A1 p. 572 (E11) and p. 587: the parameters of
`AR1Responses.lag_roots_complex_example` (`σ = 1`, `β = 0.99`, `κ = 0.5`, `φ = 1.5`) have
negative discriminant (1.57), so they fall in the complex branch of
`TaylorDeterminacy.roots_phi_gt_one`. -/
theorem complex_example_discE : TaylorDeterminacy.discE 1 0.99 0.5 1.5 < 0 := by
  unfold TaylorDeterminacy.discE
  norm_num

/-! ### The three-equation model, open mouth and super-Fisherian -/

/-- Cochrane (2023), A1 §1.13.1, p. 588, and eqs. (17.15)–(17.17), (17.20), pp. 407 and 415:
the three-equation model of chain A is the full model (17.15)–(17.17) with no IS or Phillips
disturbances, the rule `i_t = φπ_t + u_t` and the real rate `r_t = i_t − E_t π_{t+1}`. -/
theorem threeEq_iff_model (σ κ β φ : ℝ) (u x π : ℕ → Ω → ℝ) :
    AR1Responses.ThreeEq 𝔼 σ κ β φ u x π ↔ 𝔼.Adapted x ∧ 𝔼.Adapted π ∧
      FullModel.Model 𝔼 σ β κ 0 0 (fun t => φ • π t + u t)
        (fun t => φ • π t + u t - 𝔼.E t (π (t + 1))) x π := by
  unfold AR1Responses.ThreeEq FullModel.Model FullModel.IS FullModel.Fisher FullModel.PC
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      linarith [(h t ω).1]
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
      linarith [(h t ω).2]
  · rintro ⟨h1, -, h3⟩ t ω
    have e1 := congrFun (h1 t) ω
    have e3 := congrFun (h3 t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      add_zero] at e1 e3
    exact ⟨by linarith, by linarith⟩

/-- Cochrane (2023), p. 416 and eq. (5.6), p. 119: the smaller root of
`λ² − (1+β+σκ)λ + β` is `β` times the open-mouth persistence, `λ₂ = β η*`. -/
theorem lam2_eq_beta_mul_etaStar {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    FullModel.lam2 σ β κ = β * AR1Responses.etaStar σ κ β := by
  have hp := FullModel.lam_prod hσκ hβ0
  have h1 := (one_pos.trans (FullModel.one_lt_lam1 hσκ hβ0)).ne'
  rw [PersistenceFreedom.etaStar_eq_inv_lam1 hσκ hβ0, eq_mul_inv_iff_mul_eq₀ h1]
  linear_combination hp

/-- Cochrane (2023), p. 416 (open mouth) with §17.4.1, p. 408: under perfect foresight, with the
interest rate held at zero every bounded equilibrium of (17.18) decays at the open-mouth rate,
`π_t = π_0 η*ᵗ`; with an AR(1) disturbance of persistence `η*` the MSV solution
(`AR1Responses.openMouth_full`: `i = 0`, `π = −u/φ`) is the member with `π_0 = −u_0/φ`. -/
theorem openMouth_path {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (c : ℝ) :
    FullModel.path σ β κ (fun _ => 0) c = fun t => c * AR1Responses.etaStar σ κ β ^ t := by
  funext t
  induction t with
  | zero => simp [FullModel.path]
  | succ t ih =>
    have hF : FullModel.F (FullModel.lam2 σ β κ) (fun _ => (0 : ℝ)) t = 0 := by
      simp [FullModel.F]
    rw [FullModel.path, ih, hF, PersistenceFreedom.etaStar_eq_inv_lam1 hσκ hβ0, pow_succ]
    ring

/-- Cochrane (2023), p. 415 (super-Fisherian, `η = 1`) with §17.4.1, p. 408: under perfect
foresight a constant interest rate `c` and constant inflation `c` solve (17.18), and this is the
bounded equilibrium with `π_0 = c` (`FullModel.path`) — the `η = 1` MSV response
`π = i = −u/(φ−1)` of `AR1Responses.superFisher_full`. -/
theorem superFisher_path {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (c : ℝ) :
    FullModel.Second σ β κ (fun _ => c) (fun _ => c) ∧
      FullModel.path σ β κ (fun _ => c) c = fun _ => c := by
  have hs : FullModel.Second σ β κ (fun _ => c) (fun _ => c) := fun _ => by ring
  have hi : ∀ t : ℕ, |(fun _ => c) t| ≤ |c| := fun _ => le_rfl
  refine ⟨hs, ?_⟩
  have hb := FullModel.path_bounded hσκ hβ0 hi c
  exact (FullModel.pf_existsUnique hσκ hβ0 hi c).unique
    ⟨hb, (FullModel.second_iff_factor hσκ hβ0 hi hb).mpr (FullModel.path_factor hσκ hβ0 _ c),
      rfl⟩
    ⟨⟨|c|, fun _ => le_rfl⟩, hs, rfl⟩

/-! ### Fig. 17.5 and the "any sign" family -/

/-- Cochrane (2023), Fig. 17.5, p. 409, and pp. 405, 410: from the announcement on, the response
anticipated from the infinite past (`FullModel.zPath`) is the member of the
`PersistenceFreedom.full_any_sign` family (`FullModel.path`) with initial inflation
`zPath T 0`. -/
theorem zPath_eq_path {σ β κ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (T : ℕ) :
    (fun s : ℕ => FullModel.zPath σ β κ T s) =
      FullModel.path σ β κ (FullModel.stepI T) (FullModel.zPath σ β κ T 0) := by
  have h0 := FullModel.zPath_eq_antPath hσκ hβ0 T 0
  rw [Nat.cast_zero] at h0
  rw [h0]
  funext s
  rw [FullModel.zPath_eq_antPath hσκ hβ0 T s]
  rfl

/-- Cochrane (2023), pp. 405, 409–410 ("any sign"): every other member of the `full_any_sign`
family — any announcement-date inflation `c`, of either sign — differs from the anticipated
path by a decaying term, `π_n − zPath_n = (c − zPath_0) λ₁^{−n}`. -/
theorem path_sub_zPath {σ β κ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (T : ℕ) (c : ℝ) (n : ℕ) :
    FullModel.path σ β κ (FullModel.stepI T) c n - FullModel.zPath σ β κ T n =
      (c - FullModel.zPath σ β κ T 0) * (FullModel.lam1 σ β κ)⁻¹ ^ n := by
  have h := congrFun (zPath_eq_path hσκ hβ0 T) n
  rw [h]
  exact FullModel.path_sub_path σ β κ _ c _ n

/-! ### History (18.1)–(18.2) -/

/-- Cochrane (2023), eq. (18.1), p. 427, and (17.29)–(17.32), p. 420: the deviation system with
an output response is the full model in deviations with the rule (18.1) without disturbance. -/
theorem deviation_iff_rule181 (σ β κ φπ φx : ℝ) (i r x π : ℕ → Ω → ℝ) :
    TaylorDeterminacy.Deviation 𝔼 σ β κ φπ φx i r x π ↔
      (∀ t, i t = r t + 𝔼.E t (π (t + 1)) ∧ x t = 𝔼.E t (x (t + 1)) - σ • r t ∧
        π t = β • 𝔼.E t (π (t + 1)) + κ • x t) ∧ History.Rule181 φπ φx 0 i x π := by
  unfold TaylorDeterminacy.Deviation History.Rule181
  simp only [Pi.zero_apply, add_zero]
  constructor
  · intro h
    exact ⟨fun t => ⟨(h t).1, (h t).2.1, (h t).2.2.1⟩, fun t => (h t).2.2.2⟩
  · rintro ⟨h, hr⟩ t
    exact ⟨(h t).1, (h t).2.1, (h t).2.2, hr t⟩

/-- Cochrane (2023), eq. (18.2), p. 427: without forward-looking responses the matrix `Q` of
(18.2) is the matrix `Q` of (17.29)–(17.32). -/
theorem Q182_no_forward (σ β : ℝ) : History.Q182 σ β 0 0 = SharedTools.Qmat σ β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [History.Q182, SharedTools.Qmat]

/-- Cochrane (2023), eqs. (18.1)–(18.2), p. 427: without inertia and forward responses, (18.2)
has the same determinacy condition as the deviation system with (18.1). -/
theorem rule182_determinate_iff_determinate (σ β κ φπ φx : ℝ) :
    TaylorDeterminacy.StructDeterminate 𝔼 (SharedTools.Pmat σ κ φπ φx) (History.Q182 σ β 0 0) ↔
      TaylorDeterminacy.Determinate 𝔼 σ β κ φπ φx := by
  rw [Q182_no_forward, TaylorDeterminacy.determinate_iff_struct]

end Cochrane.KeynesianStickyPrices.Links

set_option linter.style.longLine false
#print axioms Cochrane.KeynesianStickyPrices.SchurStable
#print axioms Cochrane.KeynesianStickyPrices.discQ
#print axioms Cochrane.KeynesianStickyPrices.root₁
#print axioms Cochrane.KeynesianStickyPrices.root₂
#print axioms Cochrane.KeynesianStickyPrices.root_sum
#print axioms Cochrane.KeynesianStickyPrices.root_prod
#print axioms Cochrane.KeynesianStickyPrices.root_eq
#print axioms Cochrane.KeynesianStickyPrices.normSq_root_of_neg
#print axioms Cochrane.KeynesianStickyPrices.norm_root_of_nonneg
#print axioms Cochrane.KeynesianStickyPrices.schurStable_iff_roots
#print axioms Cochrane.KeynesianStickyPrices.chSeq
#print axioms Cochrane.KeynesianStickyPrices.convSeq
#print axioms Cochrane.KeynesianStickyPrices.convSeq_rec
#print axioms Cochrane.KeynesianStickyPrices.chSeq_eq_convSeq
#print axioms Cochrane.KeynesianStickyPrices.norm_convSeq_le
#print axioms Cochrane.KeynesianStickyPrices.abs_chSeq_le
#print axioms Cochrane.KeynesianStickyPrices.tendsto_chSeq
#print axioms Cochrane.KeynesianStickyPrices.tr2
#print axioms Cochrane.KeynesianStickyPrices.det2
#print axioms Cochrane.KeynesianStickyPrices.tr2_eq_trace
#print axioms Cochrane.KeynesianStickyPrices.det2_eq_det
#print axioms Cochrane.KeynesianStickyPrices.sq_eq_cayleyHamilton
#print axioms Cochrane.KeynesianStickyPrices.pow_succ_eq
#print axioms Cochrane.KeynesianStickyPrices.abs_pow_entry_le
#print axioms Cochrane.KeynesianStickyPrices.tendsto_pow_entry
#print axioms Cochrane.KeynesianStickyPrices.BoundedSeq
#print axioms Cochrane.KeynesianStickyPrices.homogeneous_iterate
#print axioms Cochrane.KeynesianStickyPrices.abs_mulVec_le
#print axioms Cochrane.KeynesianStickyPrices.homogeneous_eq_zero
#print axioms Cochrane.KeynesianStickyPrices.eq_root_of_eq
#print axioms Cochrane.KeynesianStickyPrices.exists_eigenvector
#print axioms Cochrane.KeynesianStickyPrices.exists_bounded_homogeneous
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.mk
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.E
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.const
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.mono
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.tower
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.known
#print axioms Cochrane.KeynesianStickyPrices.perfectForesight
#print axioms Cochrane.KeynesianStickyPrices.BoundedProc
#print axioms Cochrane.KeynesianStickyPrices.BoundedVec
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.Adapted
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.IsAR1
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.E_neg
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.E_smul
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.E_E_self
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.abs_E_le
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.bounded_E
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.ar1_iterate
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forward_iterate
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forward_unique
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forward_ar1_solves
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.E_tsum
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forwardSeries
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forwardSeries_summable
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forwardSeries_solves
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forwardSeries_bounded
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.eq_forwardSeries
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.forwardSeries_adapted
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.PullOut
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.Solves
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.AdaptedVec
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.system_iterate
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.system_unique
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.system_not_unique
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.Determinate
#print axioms Cochrane.KeynesianStickyPrices.ExpectationSystem.determinate_iff
#print axioms Cochrane.KeynesianStickyPrices.perfectForesight_pullOut
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.info
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.num
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinObs
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinTree
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinSystem
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.firstHeads
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinShock
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinAR1
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinShock_measurable
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Cochrane.KeynesianStickyPrices.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.Solves
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.E_of_known
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.solves_adapted
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.iterate_A15
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.tendsto_partial_A16
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.summable_A16
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.eq_forwardSeries_abs
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.forwardSeries_solves_abs
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.forwardSeries_bounded_abs
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.forwardSeries_adapted_abs
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.existsUnique_bounded
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.ScalarEq
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.scalarEq_one_iff
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.scalarSol
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.scalarSol_apply
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.scalarEq_iff
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.scalar_existsUnique
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.scalar_homog
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.scalar_determinate_iff
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.sunspotFamily
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.sunspotFamily_succ
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.sunspotFamily_adapted
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.sunspotFamily_solves
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.sunspotFamily_bounded
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.eq_sunspotFamily
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.homog_solves
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.solves_add_homog
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.bounded_solutions_not_countable
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.exists_bounded_of_one_lt
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.existsUnique_iff
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.printed_A17_one_solves
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.printed_A17_fails_neg_one
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.unit_sunspot_solves
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.unit_sunspot_bounded
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.forwardSeries_solves_of_decay
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.ar1_decay
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.no_bounded_solution_unit
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.solves_iff_forwardSeries
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.predetermined_restriction
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.hasSum_geometric_ratio
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.tsum_geometric_ratio
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.summable_geom_mul
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.abel_tsum
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.sum_weights_by_parts
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.tsum_weights_by_parts
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.abs_lt_abs_iff_of_add_pos
#print axioms Cochrane.KeynesianStickyPrices.ForwardSolution.E_tsum_dom
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.tendsto_zero_of_stable
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.tendsto_of_stable_avg
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.fwd_sum_props
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.fwd_sum_tendsto
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.backward_iterate
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.eq_backward_series
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.backward_series_solves
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.int_homog_zero
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.solvedA
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.tr2_solvedA
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.det2_solvedA
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.Pmat
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.Qmat
#print axioms Cochrane.KeynesianStickyPrices.SharedTools.det2_Pmat
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.ISPhillips
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.isPhillips_infl
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.StaticModel
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.isPhillips_iff_static_of_E_zero
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.staticModel_iff
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.exists_static_iff_17_5
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.lagged
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.AdaptiveEq
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.exists_static_adaptive_iff
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_change_iff
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_mechanism
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptivePath
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptivePath_solves
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_unique
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_existsUnique
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_peg
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_peg_unbounded
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_peg_bounded_iff
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.adaptive_steady_state
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.REModel
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reModel_iff_static
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reModel_iff_17_7
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.re_change
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.re_mechanism
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.coeff_17_7
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.re_steady_state
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reFamily
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reFamily_succ
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reFamily_adapted
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reFamily_solves
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reErr
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reErr_mds
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.eq_reFamily
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reFamily_bounded
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.re_indeterminate
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.re_not_unique
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.reFamily_closed
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.eq_17_8
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_1_path
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_1_tendsto
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_1_less_sticky
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_2_solves
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_2_strictMono
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_2_tendsto
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_2_less_sticky
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_2_frictionless_limit
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fig17_2_dashed
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.tendsto_coeff_17_7
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.no_surprise_of_known
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.eq_reFamily_of_known
#print axioms Cochrane.KeynesianStickyPrices.StaticIS.fiscal_selects
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.abs_lt_abs_iff
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.abs_coeff_lt_one_iff
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.eq_17_9
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.AdaptiveRule
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.adaptiveRule_iff_17_10
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.adaptiveRulePath
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.adaptiveRule_existsUnique
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.adaptiveRule_homog
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.AdaptiveStable
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.adaptiveStable_iff
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.passive_unstable
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.unstable_diverges
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.printed_abs_phi_gt_one_stabilizes_false
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.boundary_coeff
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.adaptiveRule_bounded
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.RERule
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.reRule_iff_17_11
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.reRule_iff_scalar
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.REDeterminate
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.reDeterminate_iff
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.re_coeff_abs_lt_one_iff
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.printed_passive_indeterminate_false
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.passive_indeterminate
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.forward_solution
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.tendsto_coeff_17_11
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.deviation_eq
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.rule_selects
#print axioms Cochrane.KeynesianStickyPrices.RulesAdaptiveRE.rule_selects_any_delta
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.den
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.den_mul
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.den_ne_zero
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.den_pos
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.ar1_solves
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.eq_17_12
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.coeff_17_12_forms
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.eq_17_12_series
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.coeff_17_13_forms
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.eq_17_13
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.tendsto_17_12
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.tendsto_17_13
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.superFisher_simple
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.openMouth_simple
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.num_pos_iff
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.i_coeff_pos_iff
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.fig17_3
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.ThreeEq
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.denF
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.denF_mul
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.denF_pos
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.msv_solves
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.coeffs_of_msv
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.eq_1_59_iff
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.msv_i_eq
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.transA
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.transA_explicit
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.threeEq_solves
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.schurStable_of_one_lt
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.msv_unique
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.superFisher_full
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.superFisher_full_signs
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.msv_beta_zero
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.tendsto_1_60
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.lag_form
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.lag_factor
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.partial_fractions
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.lag_sum_ar1
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.lag_roots_norm_lt_one
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.lag_roots_complex_example
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.openMouth_iff_quadratic
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.etaStar
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.etaStar_root
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.etaStar_mem
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.quad_sub
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.eq_etaStar
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.openMouth_full
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.etaStar_fig17_8
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.full_i_coeff_pos_of_lt
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.full_i_coeff_neg_of_gt
#print axioms Cochrane.KeynesianStickyPrices.AR1Responses.fig17_8_transitory
#print axioms Cochrane.KeynesianStickyPrices.FullModel.IS
#print axioms Cochrane.KeynesianStickyPrices.FullModel.Fisher
#print axioms Cochrane.KeynesianStickyPrices.FullModel.PC
#print axioms Cochrane.KeynesianStickyPrices.FullModel.Model
#print axioms Cochrane.KeynesianStickyPrices.FullModel.fisher_iff
#print axioms Cochrane.KeynesianStickyPrices.FullModel.eq_17_18_shocks
#print axioms Cochrane.KeynesianStickyPrices.FullModel.eq_17_18
#print axioms Cochrane.KeynesianStickyPrices.FullModel.PFEqm
#print axioms Cochrane.KeynesianStickyPrices.FullModel.pf_model_iff
#print axioms Cochrane.KeynesianStickyPrices.FullModel.BoundedS
#print axioms Cochrane.KeynesianStickyPrices.FullModel.Second
#print axioms Cochrane.KeynesianStickyPrices.FullModel.pfEqm_iff_second
#print axioms Cochrane.KeynesianStickyPrices.FullModel.lam1
#print axioms Cochrane.KeynesianStickyPrices.FullModel.lam2
#print axioms Cochrane.KeynesianStickyPrices.FullModel.disc_pos
#print axioms Cochrane.KeynesianStickyPrices.FullModel.lam_sum
#print axioms Cochrane.KeynesianStickyPrices.FullModel.lam_prod
#print axioms Cochrane.KeynesianStickyPrices.FullModel.sigma_kappa_eq
#print axioms Cochrane.KeynesianStickyPrices.FullModel.lam2_lt_lam1
#print axioms Cochrane.KeynesianStickyPrices.FullModel.one_lt_lam1
#print axioms Cochrane.KeynesianStickyPrices.FullModel.lam2_lt_one
#print axioms Cochrane.KeynesianStickyPrices.FullModel.lam2_pos
#print axioms Cochrane.KeynesianStickyPrices.FullModel.F
#print axioms Cochrane.KeynesianStickyPrices.FullModel.F_summable
#print axioms Cochrane.KeynesianStickyPrices.FullModel.F_rec
#print axioms Cochrane.KeynesianStickyPrices.FullModel.F_bound
#print axioms Cochrane.KeynesianStickyPrices.FullModel.homog_zero
#print axioms Cochrane.KeynesianStickyPrices.FullModel.F_unique
#print axioms Cochrane.KeynesianStickyPrices.FullModel.factor_identity
#print axioms Cochrane.KeynesianStickyPrices.FullModel.second_iff_factor
#print axioms Cochrane.KeynesianStickyPrices.FullModel.path
#print axioms Cochrane.KeynesianStickyPrices.FullModel.path_factor
#print axioms Cochrane.KeynesianStickyPrices.FullModel.bounded_of_rec
#print axioms Cochrane.KeynesianStickyPrices.FullModel.path_bounded
#print axioms Cochrane.KeynesianStickyPrices.FullModel.pf_existsUnique
#print axioms Cochrane.KeynesianStickyPrices.FullModel.pf_eqm_iff
#print axioms Cochrane.KeynesianStickyPrices.FullModel.tendsto_of_rec
#print axioms Cochrane.KeynesianStickyPrices.FullModel.tendsto_F
#print axioms Cochrane.KeynesianStickyPrices.FullModel.tendsto_pi
#print axioms Cochrane.KeynesianStickyPrices.FullModel.tendsto_x
#print axioms Cochrane.KeynesianStickyPrices.FullModel.coef
#print axioms Cochrane.KeynesianStickyPrices.FullModel.coef_mul
#print axioms Cochrane.KeynesianStickyPrices.FullModel.coef_pos
#print axioms Cochrane.KeynesianStickyPrices.FullModel.twoSided
#print axioms Cochrane.KeynesianStickyPrices.FullModel.twoSided_factor
#print axioms Cochrane.KeynesianStickyPrices.FullModel.twoSided_eq
#print axioms Cochrane.KeynesianStickyPrices.FullModel.stepI
#print axioms Cochrane.KeynesianStickyPrices.FullModel.stepI_bound
#print axioms Cochrane.KeynesianStickyPrices.FullModel.stepI_tendsto
#print axioms Cochrane.KeynesianStickyPrices.FullModel.F_step
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_twoSided
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_second
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_le_T
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_zero_pos
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_strictMono
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_tendsto_one
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_lt_one
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_pos
#print axioms Cochrane.KeynesianStickyPrices.FullModel.x_neg_iff
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_x_neg
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_x_tendsto
#print axioms Cochrane.KeynesianStickyPrices.FullModel.rise_raises_inflation
#print axioms Cochrane.KeynesianStickyPrices.FullModel.dashed_joins_solid
#print axioms Cochrane.KeynesianStickyPrices.FullModel.fig17_6_any_jump
#print axioms Cochrane.KeynesianStickyPrices.FullModel.SecondZ
#print axioms Cochrane.KeynesianStickyPrices.FullModel.BoundedZ
#print axioms Cochrane.KeynesianStickyPrices.FullModel.stepZ
#print axioms Cochrane.KeynesianStickyPrices.FullModel.GZ
#print axioms Cochrane.KeynesianStickyPrices.FullModel.zPath
#print axioms Cochrane.KeynesianStickyPrices.FullModel.GZ_rec
#print axioms Cochrane.KeynesianStickyPrices.FullModel.zPath_factor
#print axioms Cochrane.KeynesianStickyPrices.FullModel.zPath_bounded
#print axioms Cochrane.KeynesianStickyPrices.FullModel.zPath_second
#print axioms Cochrane.KeynesianStickyPrices.FullModel.secondZ_unique
#print axioms Cochrane.KeynesianStickyPrices.FullModel.zPath_existsUnique
#print axioms Cochrane.KeynesianStickyPrices.FullModel.zPath_shift
#print axioms Cochrane.KeynesianStickyPrices.FullModel.zPath_eq_antPath
#print axioms Cochrane.KeynesianStickyPrices.FullModel.antPath_eq_zPath_shift
#print axioms Cochrane.KeynesianStickyPrices.FullModel.path_sub_path
#print axioms Cochrane.KeynesianStickyPrices.FullModel.tendsto_zPath
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.eq_17_14
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.corrected_inverse
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.printed_inverse_of_no_surprise
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.printed_inverse_false
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.targetPath
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.shockRate
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.shockInfl
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.targetPath_bounded
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.any_sign
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.any_sign_long_run
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.permanent_negative
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.transitory_positive
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.any_sign_coin
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.long_run_one
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.etaStar_eq_inv_lam1
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.etaStar_mul_inv_lam2
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.one_lt_inv_lam2
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.full_any_sign
#print axioms Cochrane.KeynesianStickyPrices.PersistenceFreedom.full_long_run
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.ar2
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.ar1_form
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_coeff
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_path
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_rate
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_i_zero
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_infl_strictAnti
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_i_strictAnti
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_tendsto
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.fig17_4_i_reverses
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.taylor_bounded
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.taylor_transitory
#print axioms Cochrane.KeynesianStickyPrices.AdaptiveTaylor.peg_spiral
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.innov
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.Flow
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.rea
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.innov_sub
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.innov_known
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.innov_expost_eq
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.expost_first_term
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.innov_rea_self
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.innov_finite
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.eq_17_19_own_dating
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.eq_17_19
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.printed_own_dating_iff
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.innov_tsum
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.eq_17_19_bounded
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fiscal_contraction
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.surplus_gdp
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.reverse_engineer
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.reverse_engineer_distinct
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.cAR
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.piAR
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.piAR_second
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.piAR_eq_path
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.sigmaS
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.sigmaS_closed
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_c
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_lam1
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_lam1_bounds
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_params
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_sigmaS
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_L_bounds
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_values
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_real_rates
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_zero_panel
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.not_geometric
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_u_not_ar1
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_7_times_five
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.e10
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.path_step0
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.deltaS
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.permanent_surplus_pct
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.deltaS_closed
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.deltaS_B
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.deltaS_D
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.deltaS_zero_iff
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_6_inconsistent
#print axioms Cochrane.KeynesianStickyPrices.FiscalUnderpinnings.fig17_6_implied_jumps
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.KingRule
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.king_iff_standard
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.king_equilibrium
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.Starred
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.starred_iff_model
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.eq_17_27
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.eq_17_25
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.E_forwardSeries_succ
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.eq_17_26
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.e9_intercept
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.e9_difference
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.e9_counterexample
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.boundedProc_E
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.boundedProc_add_smul
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.any_pi_attainable
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.any_x_attainable
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.woodfordLoss
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.loss_corner_x
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.loss_corner_pi
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.Rule1728
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.rule_17_28_eq
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.pi_zero_constant_intercept
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.no_rule_stabilises_inflation
#print axioms Cochrane.KeynesianStickyPrices.OptimalPolicy.x_zero_constant_intercept
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.StructSolves
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.StructDeterminate
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.solve2
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.struct_iff_solves
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.not_determinate_of_det_zero
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.structDeterminate_iff
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.Deviation
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.stack
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.deviation_iff_struct
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.Determinate
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.determinate_iff_struct
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.determinate_iff
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.schur_div_pos
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.schur_div_neg
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.determinate_iff_explicit
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.determinate_iff_phi
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.determinate_iff_BM
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.not_necessary_witness
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.not_necessary_phix
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.not_necessary_negative
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.not_sufficient_witness
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.not_sufficient
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.sufficient_of_phix_nonneg
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.widens_with_phix
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.deviation_iff_17_33
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.eq_1_55
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.printed_1_55_iff
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.trM
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.detM
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.Mmat
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.tr_det_Mmat
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.discE
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.discQ_eq
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.eq_1_57
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.plus_root_gt_one
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.roots_phi_lt_one
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.abs_phi_lt_one_one_stable
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.roots_phi_gt_one
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.KingEqm
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.deviation_of_eqm
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.phi_irrelevance
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.phi_irrelevance_sets
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.standard_rule_unique
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.pf_starred
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.reverse_engineered_unique
#print axioms Cochrane.KeynesianStickyPrices.TaylorDeterminacy.real_explosion
#print axioms Cochrane.KeynesianStickyPrices.History.mpc
#print axioms Cochrane.KeynesianStickyPrices.History.mpc_eq
#print axioms Cochrane.KeynesianStickyPrices.History.pih_consumption
#print axioms Cochrane.KeynesianStickyPrices.History.mpc_strictMonoOn
#print axioms Cochrane.KeynesianStickyPrices.History.mpc_injective
#print axioms Cochrane.KeynesianStickyPrices.History.Rule181
#print axioms Cochrane.KeynesianStickyPrices.History.Rule182
#print axioms Cochrane.KeynesianStickyPrices.History.rule182_reduces
#print axioms Cochrane.KeynesianStickyPrices.History.rule181_determinate_iff
#print axioms Cochrane.KeynesianStickyPrices.History.rule181_phi_gt_one
#print axioms Cochrane.KeynesianStickyPrices.History.Q182
#print axioms Cochrane.KeynesianStickyPrices.History.rule182_deviation_iff
#print axioms Cochrane.KeynesianStickyPrices.History.rule182_determinate_iff
#print axioms Cochrane.KeynesianStickyPrices.History.likelihood_flat
#print axioms Cochrane.KeynesianStickyPrices.History.cgg_reading
#print axioms Cochrane.KeynesianStickyPrices.Links.reErr_eq_innov
#print axioms Cochrane.KeynesianStickyPrices.Links.any_sign_innov
#print axioms Cochrane.KeynesianStickyPrices.Links.second_beta_zero_iff
#print axioms Cochrane.KeynesianStickyPrices.Links.secondZ_beta_zero
#print axioms Cochrane.KeynesianStickyPrices.Links.deviation_beta_zero
#print axioms Cochrane.KeynesianStickyPrices.Links.determinate_beta_zero_iff
#print axioms Cochrane.KeynesianStickyPrices.Links.determinate_beta_zero_iff_reDeterminate
#print axioms Cochrane.KeynesianStickyPrices.Links.bound_1_58_beta_zero
#print axioms Cochrane.KeynesianStickyPrices.Links.bound_1_58_lt
#print axioms Cochrane.KeynesianStickyPrices.Links.tendsto_bound_1_58
#print axioms Cochrane.KeynesianStickyPrices.Links.transA_eq_solvedA
#print axioms Cochrane.KeynesianStickyPrices.Links.Mmat_mul_transA
#print axioms Cochrane.KeynesianStickyPrices.Links.determinate_iff_transA
#print axioms Cochrane.KeynesianStickyPrices.Links.msv_unique_of_determinate
#print axioms Cochrane.KeynesianStickyPrices.Links.inv_mem_roots
#print axioms Cochrane.KeynesianStickyPrices.Links.discQ_div
#print axioms Cochrane.KeynesianStickyPrices.Links.trM_detM_eq
#print axioms Cochrane.KeynesianStickyPrices.Links.eigen_norm_gt_one
#print axioms Cochrane.KeynesianStickyPrices.Links.complex_example_discE
#print axioms Cochrane.KeynesianStickyPrices.Links.threeEq_iff_model
#print axioms Cochrane.KeynesianStickyPrices.Links.lam2_eq_beta_mul_etaStar
#print axioms Cochrane.KeynesianStickyPrices.Links.openMouth_path
#print axioms Cochrane.KeynesianStickyPrices.Links.superFisher_path
#print axioms Cochrane.KeynesianStickyPrices.Links.zPath_eq_path
#print axioms Cochrane.KeynesianStickyPrices.Links.path_sub_zPath
#print axioms Cochrane.KeynesianStickyPrices.Links.deviation_iff_rule181
#print axioms Cochrane.KeynesianStickyPrices.Links.Q182_no_forward
#print axioms Cochrane.KeynesianStickyPrices.Links.rule182_determinate_iff_determinate
