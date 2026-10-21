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
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
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

Restated from the `Gali/OpenEconomy` project; citations to Galí (2015) mark where the
result is used in that book (each project in this
repository is self-contained).
-/

namespace Woodford.ReturnOfMonetaryRules

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

end Woodford.ReturnOfMonetaryRules

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

Restated from the `Gali/OpenEconomy` project; citations to Galí (2015) mark where the
result is used in that book (each project in this
repository is self-contained).
-/

namespace Woodford.ReturnOfMonetaryRules

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

end Woodford.ReturnOfMonetaryRules

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

Restated from the `Gali/OpenEconomy` project; citations to Galí (2015) mark where the
result is used in that book (each project in this
repository is self-contained).
-/

namespace Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree

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

end Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Overnight interest rates under a channel system

Woodford (2003), *Interest and Prices*, Chapter 1, §3.1–3.2, pp. 25–33.

Under a channel system the central bank lends overnight balances at `i^l = ī + δ` and pays
`i^d = ī − δ` on deposits. Following Woodford (2001c) the interbank market clears at
(3.1), p. 27,

  `i = i^d + F(−S/σ) (i^l − i^d)`,

where `S` is the aggregate supply of clearing balances, `σ > 0` measures payment uncertainty and
`F` is a cumulative distribution function.

**Choice of `F`.** The book describes `F` (p. 27) only as a function that "increases
monotonically from 0 to 1". We formalise exactly that as `IsCDF F` (monotone, limit `0` at `−∞`
and `1` at `+∞`) and show (`isCDF_cdf`, `exists_measure_of_isCDF`) that the right-continuous
functions with this property are precisely the Mathlib CDFs `ProbabilityTheory.cdf μ` of
probability measures `μ` on `ℝ`. The theorems use only the property each needs (often merely
monotonicity and `0 ≤ F ≤ 1`, which `IsCDF` implies: `IsCDF.nonneg`, `IsCDF.le_one`), and the
`cdf_*` corollaries specialise them to a genuine probability distribution.

The text does not derive (3.1) from a bank's reserve-management problem; it cites Woodford
(2001c) for that model, so no derivation is formalised here.

## Main results

* `rate_mem_channel`: `i^d ≤ i ≤ i^l` (p. 28).
* `rate_antitone`, `rate_strictAnti`: the rate is non-increasing in supply, strictly decreasing
  when `F` is strictly increasing (p. 28).
* `rate_eq_target_iff`: at the channel midpoint, `i = ī ↔ F(−S/σ) = 1/2`.
* `exists_eq_half`, `existsUnique_target_supply`, `target_supply_iff`: (3.2), the unique supply
  hitting the target is `S = −F⁻¹(1/2) σ` (IVT for existence).
* `target_supply_set_indep`: the target supply does not depend on `ī` (p. 28).
* `rate_shift_channel`: moving the channel moves the rate one-for-one with no change in supply.
* `rate_noClearing`: with no clearing demand (`F` the CDF of the point mass at `0`), `i = i^d`
  for every positive supply (p. 32).
-/

namespace Woodford.ReturnOfMonetaryRules.ChannelSystem

open Filter Topology MeasureTheory ProbabilityTheory

/-- Woodford (2003), eq. (3.1), p. 27: the market-clearing overnight rate
`i = i^d + F(−S/σ)(i^l − i^d)` given deposit rate `iD`, lending rate `iL`, uncertainty `σ` and
supply of clearing balances `S`. -/
noncomputable def rate (F : ℝ → ℝ) (iD iL σ S : ℝ) : ℝ := iD + F (-S / σ) * (iL - iD)

/-- Woodford (2003), p. 27: `F` is a cumulative distribution function in the book's sense, a
monotone function rising from `0` (at `−∞`) to `1` (at `+∞`). -/
def IsCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1)

/-- Woodford (2003), p. 27: a CDF in the sense of `IsCDF` is nonnegative. -/
theorem IsCDF.nonneg {F : ℝ → ℝ} (hF : IsCDF F) (x : ℝ) : 0 ≤ F x :=
  le_of_tendsto hF.2.1 (eventually_atBot.2 ⟨x, fun _ hy => hF.1 hy⟩)

/-- Woodford (2003), p. 27: a CDF in the sense of `IsCDF` is at most one. -/
theorem IsCDF.le_one {F : ℝ → ℝ} (hF : IsCDF F) (x : ℝ) : F x ≤ 1 :=
  ge_of_tendsto hF.2.2 (eventually_atTop.2 ⟨x, fun _ hy => hF.1 hy⟩)

/-- Woodford (2003), p. 27: the CDF of a measure on `ℝ` (Mathlib `ProbabilityTheory.cdf`) is a
CDF in the book's sense. -/
theorem isCDF_cdf (μ : Measure ℝ) : IsCDF (cdf μ) :=
  ⟨monotone_cdf μ, tendsto_cdf_atBot μ, tendsto_cdf_atTop μ⟩

/-- Woodford (2003), p. 27: conversely, every right-continuous `F` with `IsCDF F` is the CDF of a
probability measure on `ℝ`, so `IsCDF` plus right-continuity is exactly "the CDF of a
probability distribution of payment shocks". -/
theorem exists_measure_of_isCDF {F : ℝ → ℝ} (hF : IsCDF F)
    (hr : ∀ x, ContinuousWithinAt F (Set.Ici x) x) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ⇑(cdf μ) = F := by
  let f : StieltjesFunction ℝ := ⟨F, hF.1, hr⟩
  have h0 : Tendsto f atBot (𝓝 0) := hF.2.1
  have h1 : Tendsto f atTop (𝓝 1) := hF.2.2
  exact ⟨f.measure, f.isProbabilityMeasure h0 h1,
    congrArg (fun g : StieltjesFunction ℝ => ⇑g) (cdf_measure_stieltjesFunction f h0 h1)⟩

/-! ### The rate stays in the channel and falls with supply -/

/-- Woodford (2003), p. 28: the market overnight rate lies in the channel, `i^d ≤ i ≤ i^l`,
for any `F` with values in `[0, 1]`. -/
theorem rate_mem_channel {F : ℝ → ℝ} (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    {iD iL : ℝ} (h : iD ≤ iL) (σ S : ℝ) :
    iD ≤ rate F iD iL σ S ∧ rate F iD iL σ S ≤ iL := by
  unfold rate
  have hd : 0 ≤ iL - iD := sub_nonneg.mpr h
  constructor
  · nlinarith [hF0 (-S / σ)]
  · nlinarith [hF1 (-S / σ)]

/-- Woodford (2003), p. 28: the overnight rate is a non-increasing function of the supply of
clearing balances (`σ > 0`, `F` monotone, `i^d ≤ i^l`). -/
theorem rate_antitone {F : ℝ → ℝ} (hF : Monotone F) {iD iL σ : ℝ} (h : iD ≤ iL)
    (hσ : 0 < σ) : Antitone (fun S => rate F iD iL σ S) := by
  intro S₁ S₂ hS
  have hx : -S₂ / σ ≤ -S₁ / σ := div_le_div_of_nonneg_right (by linarith) hσ.le
  have := hF hx
  simp only [rate]
  nlinarith [sub_nonneg.mpr h]

/-- Woodford (2003), p. 28: the overnight rate is strictly decreasing in supply when `F` is
strictly increasing and the channel has positive width. -/
theorem rate_strictAnti {F : ℝ → ℝ} (hF : StrictMono F) {iD iL σ : ℝ} (h : iD < iL)
    (hσ : 0 < σ) : StrictAnti (fun S => rate F iD iL σ S) := by
  intro S₁ S₂ hS
  have hx : -S₂ / σ < -S₁ / σ := div_lt_div_of_pos_right (by linarith) hσ
  have := hF hx
  simp only [rate]
  nlinarith [sub_pos.mpr h]

/-- Woodford (2003), p. 28 (CDF form): for the CDF of any measure `μ` the rate lies in the
channel. -/
theorem cdf_rate_mem_channel (μ : Measure ℝ) {iD iL : ℝ} (h : iD ≤ iL) (σ S : ℝ) :
    iD ≤ rate (cdf μ) iD iL σ S ∧ rate (cdf μ) iD iL σ S ≤ iL :=
  rate_mem_channel (cdf_nonneg μ) (cdf_le_one μ) h σ S

/-- Woodford (2003), p. 28 (CDF form): for the CDF of any measure `μ` the rate is non-increasing
in supply. -/
theorem cdf_rate_antitone (μ : Measure ℝ) {iD iL σ : ℝ} (h : iD ≤ iL) (hσ : 0 < σ) :
    Antitone (fun S => rate (cdf μ) iD iL σ S) :=
  rate_antitone (monotone_cdf μ) h hσ

/-! ### Hitting the target: equation (3.2) -/

/-- Woodford (2003), p. 27: with `i^l = ī + δ`, `i^d = ī − δ`, the rate is
`ī − δ + 2δ F(−S/σ)`. -/
theorem rate_channel (F : ℝ → ℝ) (ibar δ σ S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar - δ + 2 * δ * F (-S / σ) := by
  unfold rate; ring

/-- Woodford (2003), p. 28: with a symmetric channel of half-width `δ > 0` around the target `ī`,
the market rate equals the target exactly when `F(−S/σ) = 1/2`. -/
theorem rate_eq_target_iff (F : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (ibar σ S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar ↔ F (-S / σ) = 1 / 2 := by
  rw [rate_channel]
  constructor
  · intro h
    have : δ * (2 * F (-S / σ) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hδ.ne'
    · linarith
  · intro h
    rw [h]; ring

/-- Woodford (2003), p. 28: a continuous CDF takes the value `1/2` (intermediate value theorem
and the limits `0`, `1`), so `F⁻¹(1/2)` in (3.2) exists. -/
theorem exists_eq_half {F : ℝ → ℝ} (hF : IsCDF F) (hc : Continuous F) : ∃ x, F x = 1 / 2 := by
  obtain ⟨a, ha⟩ := (hF.2.1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  obtain ⟨b, hb⟩ := (hF.2.2.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))).exists
  exact intermediate_value_univ₂ hc continuous_const ha.le hb.le

/-- Woodford (2003), eq. (3.2), p. 28: if `F` is strictly increasing with `F x₀ = 1/2`
(`x₀ = F⁻¹(1/2)`), the rate equals the target `ī` if and only if `S = −x₀ σ`. -/
theorem target_supply_iff {F : ℝ → ℝ} (hF : StrictMono F) {x₀ : ℝ} (hx₀ : F x₀ = 1 / 2)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (ibar S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar ↔ S = -x₀ * σ := by
  rw [rate_eq_target_iff F hδ, ← hx₀, hF.injective.eq_iff]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]; field_simp

/-- Woodford (2003), eq. (3.2), p. 28: for a continuous, strictly increasing CDF there is exactly
one supply of clearing balances at which the overnight rate equals the target. -/
theorem existsUnique_target_supply {F : ℝ → ℝ} (hF : IsCDF F) (hc : Continuous F)
    (hs : StrictMono F) {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (ibar : ℝ) :
    ∃! S, rate F (ibar - δ) (ibar + δ) σ S = ibar := by
  obtain ⟨x₀, hx₀⟩ := exists_eq_half hF hc
  refine ⟨-x₀ * σ, (target_supply_iff hs hx₀ hδ hσ ibar _).mpr rfl, fun S hS => ?_⟩
  exact (target_supply_iff hs hx₀ hδ hσ ibar S).mp hS

/-- Woodford (2003), p. 28: the supply of clearing balances needed to hit the target is
"unrelated to changes in the target level of interest rates": the set of target-hitting supplies
is the same for every target `ī` (no hypothesis on `F` is needed). -/
theorem target_supply_set_indep (F : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (σ ibar₁ ibar₂ : ℝ) :
    {S | rate F (ibar₁ - δ) (ibar₁ + δ) σ S = ibar₁} =
      {S | rate F (ibar₂ - δ) (ibar₂ + δ) σ S = ibar₂} := by
  ext S
  simp only [Set.mem_ofPred_eq, rate_eq_target_iff F hδ]

/-- Woodford (2003), p. 28: if payment shocks are symmetric, `F 0 = 1/2`, the target supply is
`S = 0` whatever the degree of uncertainty `σ > 0`. -/
theorem target_supply_symmetric {F : ℝ → ℝ} (hF : StrictMono F) (h0 : F 0 = 1 / 2)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (ibar S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar ↔ S = 0 := by
  rw [target_supply_iff hF h0 hδ hσ]
  simp

/-- Woodford (2003), p. 28: changes in the level of overnight rates are brought about by shifting
the deposit and lending rates; a shift of the channel by `Δ` moves the market rate by exactly `Δ`
at an unchanged supply of clearing balances. -/
theorem rate_shift_channel (F : ℝ → ℝ) (iD iL σ S Δ : ℝ) :
    rate F (iD + Δ) (iL + Δ) σ S = rate F iD iL σ S + Δ := by
  unfold rate; ring

/-! ### No clearing demand (p. 32) -/

/-- Woodford (2003), p. 32: with no clearing demand the payment shock is degenerate at `0`; its
CDF vanishes at every negative argument. -/
theorem cdf_dirac_zero_of_neg {x : ℝ} (hx : x < 0) : cdf (Measure.dirac (0 : ℝ)) x = 0 := by
  have hm : (0 : ℝ) ∉ Set.Iic x := by simpa using hx
  rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic,
    Set.indicator_of_notMem hm]
  simp

/-- Woodford (2003), p. 32: with no clearing demand, (3.1) "reduces to `i = i^d`" for every
positive supply of central-bank balances (and every `σ > 0`). -/
theorem rate_noClearing {S σ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (iD iL : ℝ) :
    rate (cdf (Measure.dirac (0 : ℝ))) iD iL σ S = iD := by
  have hx : -S / σ < 0 := div_neg_of_neg_of_pos (by linarith) hσ
  simp [rate, cdf_dirac_zero_of_neg hx]

/-- Woodford (2003), pp. 32–33: with no clearing demand, variations in a positive supply of
central-bank balances have no effect at all on the overnight rate. -/
theorem rate_noClearing_indep {S₁ S₂ σ : ℝ} (h₁ : 0 < S₁) (h₂ : 0 < S₂) (hσ : 0 < σ)
    (iD iL : ℝ) :
    rate (cdf (Measure.dirac (0 : ℝ))) iD iL σ S₁ =
      rate (cdf (Measure.dirac (0 : ℝ))) iD iL σ S₂ := by
  rw [rate_noClearing h₁ hσ, rate_noClearing h₂ hσ]

end Woodford.ReturnOfMonetaryRules.ChannelSystem

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interest-rate rules

Woodford (2003), *Interest and Prices*, Chapter 1, §4 and §4.1, pp. 37–44.

## Main results

* `WicksellRule` (4.1); `difference_iff_wicksell` (fn. 30, p. 38): adopting the difference
  rule `Δi_t = φ π_t` from `t₀` is equivalent to the Wicksellian rule (4.1) with intercept
  `ī = i_{t₀−1} − φ p_{t₀−1}`, and `wicksell_intercept_eq` pins the intercept down.
* `wicksell_violates_zlb` (fn. 29): (4.1) cannot hold at every price level, since it would
  require negative interest rates.
* `taylorRule` (4.3), `taylorRule_at_target`, `taylorRule_real_rate_at_target`
  (p. 39: `i = 4%` at target, an implied real rate of `2%`) and `taylorPrinciple_iff`
  (p. 40: the real rate rises with inflation iff the inflation coefficient exceeds one).
* `PartialAdjustment` (4.5), `DesiredRate` (4.6) and the long-run response
  `partialAdjustment_longRun`: under the Schur–Cohn condition the funds rate converges to
  `ī + φ_π(π − π̄) + φ_x(1 − γ)x` after a permanent change, so the long-run coefficients are
  `φ_π` and `φ_x(1 − γ)`; `judd_rudebusch_stable` checks the condition at the Table 1.1
  estimates.
* `ForecastDesiredRate` (4.7) and `TargetCriterion` (4.8), Svensson's target criterion.
-/

namespace Woodford.ReturnOfMonetaryRules.InterestRateRules

open Filter Topology

variable {Ω : Type*}

/-! ### The Wicksellian rule and footnote 30 -/

/-- Woodford (2003), eq. (4.1), p. 38: the Wicksellian rule `i_t = ī + φ p_t` holds at date `t`
(`p_t` the log price level). -/
def WicksellRule (ibar φ : ℝ) (i p : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = (fun _ => ibar) + φ • p t

/-- Woodford (2003), eq. (4.2) and fn. 30, p. 38: the difference rule `Δi_t = φ π_t`,
`π_t ≡ Δp_t`, at date `t + 1`. -/
def DifferenceRule (φ : ℝ) (i p : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i (t + 1) - i t = φ • (p (t + 1) - p t)

/-- Woodford (2003), fn. 30, p. 38: a commitment to the difference rule (4.2) from date
`t₀ = s + 1` on is equivalent to the Wicksellian rule (4.1) from date `s = t₀ − 1` on, with
intercept `i_{t₀−1} − φ p_{t₀−1}` (both directions, by telescoping). -/
theorem difference_iff_wicksell (φ : ℝ) (i p : ℕ → Ω → ℝ) (s : ℕ) :
    (∀ t, s ≤ t → DifferenceRule φ i p t) ↔
      ∀ t, s ≤ t → i t = (i s - φ • p s) + φ • p t := by
  constructor
  · intro h t hst
    induction t, hst using Nat.le_induction with
    | base => abel
    | succ t hst ih =>
      have h1 := h t hst
      unfold DifferenceRule at h1
      rw [smul_sub] at h1
      calc i (t + 1) = i t + (φ • p (t + 1) - φ • p t) := by rw [← h1]; abel
        _ = _ := by rw [ih]; abel
  · intro h t hst
    unfold DifferenceRule
    rw [h (t + 1) (Nat.le_succ_of_le hst), h t hst, smul_sub]
    abel

/-- Woodford (2003), fn. 30, p. 38: if the Wicksellian rule holds from date `s = t₀ − 1` on with
some intercept `ī`, that intercept is `i_{t₀−1} − φ p_{t₀−1}` (in every state). -/
theorem wicksell_intercept_eq {ibar φ : ℝ} {i p : ℕ → Ω → ℝ} {s : ℕ}
    (h : WicksellRule ibar φ i p s) : (fun _ => ibar) = i s - φ • p s := by
  unfold WicksellRule at h
  rw [h]; abel

/-- Woodford (2003), fn. 30, p. 38: a Wicksellian rule with any constant intercept implies the
difference rule at every date. -/
theorem wicksell_imp_difference {ibar φ : ℝ} {i p : ℕ → Ω → ℝ}
    (h : ∀ t, WicksellRule ibar φ i p t) (t : ℕ) : DifferenceRule φ i p t := by
  unfold DifferenceRule
  rw [h (t + 1), h t, smul_sub]
  abel

/-- Woodford (2003), fn. 29, p. 38: the log-linear rule (4.1) with `φ ≠ 0` cannot be maintained
at all price levels, since some price level would call for a negative nominal rate. -/
theorem wicksell_violates_zlb (ibar : ℝ) {φ : ℝ} (hφ : φ ≠ 0) : ∃ p : ℝ, ibar + φ * p < 0 :=
  ⟨-(ibar + 1) / φ, by field_simp; linarith⟩

/-! ### The Taylor rule (4.3) and reaction functions (4.4) -/

/-- Woodford (2003), eq. (4.4), p. 40: a reaction function `i = ī + φ_π(π − π̄) + φ_x x`
with inflation target `piStar` (the book's `π̄`). -/
def reactionFn (ibar φπ φx piStar infl x : ℝ) : ℝ := ibar + φπ * (infl - piStar) + φx * x

/-- Woodford (2003), eq. (4.3), p. 39: the Taylor (1993) rule
`i = 0.04 + 1.5(π̄ − 0.02) + 0.5(y − y^p)`, as a function of inflation and the output gap. -/
noncomputable def taylorRule (infl gap : ℝ) : ℝ := 0.04 + 1.5 * (infl - 0.02) + 0.5 * gap

/-- Woodford (2003), eqs. (4.3)–(4.4), pp. 39–40: the Taylor rule is the reaction function with
`ī = 4%`, `φ_π = 1.5`, `φ_x = 0.5` and inflation target `2%`. -/
theorem taylorRule_eq_reactionFn (infl gap : ℝ) :
    taylorRule infl gap = reactionFn 0.04 1.5 0.5 0.02 infl gap := rfl

/-- Woodford (2003), p. 39: with inflation at its 2% target and a zero output gap, the Taylor
rule sets the funds rate at 4%. -/
theorem taylorRule_at_target : taylorRule 0.02 0 = 0.04 := by
  norm_num [taylorRule]

/-- Woodford (2003), p. 39: the implied long-run real funds rate at target is 2%. -/
theorem taylorRule_real_rate_at_target : taylorRule 0.02 0 - 0.02 = 0.02 := by
  norm_num [taylorRule]

/-- Woodford (2003), p. 40 (the Taylor principle): the real rate `i − π` implied by a reaction
function is strictly increasing in inflation if and only if `φ_π > 1`. -/
theorem taylorPrinciple_iff (ibar φπ φx piStar x : ℝ) :
    StrictMono (fun infl => reactionFn ibar φπ φx piStar infl x - infl) ↔ 1 < φπ := by
  constructor
  · intro h
    have := h (show (0 : ℝ) < 1 by norm_num)
    simp only [reactionFn] at this
    linarith
  · intro h a b hab
    simp only [reactionFn]
    nlinarith

/-- Woodford (2003), p. 40: the Taylor rule satisfies the Taylor principle — inflation `Δ` above
target raises the real funds rate by `0.5 Δ`. -/
theorem taylorRule_real_rate_rises (infl gap Δ : ℝ) :
    taylorRule (infl + Δ) gap - (infl + Δ) = taylorRule infl gap - infl + 0.5 * Δ := by
  unfold taylorRule; ring

/-- Woodford (2003), p. 40: Goodhart's (1992) rule `i = 0.03 + 1.5 π̄` is a reaction function of
the form (4.4) with `φ_π = 1.5 > 1` and no output response, for any inflation target. -/
theorem goodhartRule_eq_reactionFn (piStar infl x : ℝ) :
    (0.03 : ℝ) + 1.5 * infl = reactionFn (0.03 + 1.5 * piStar) 1.5 0 piStar infl x := by
  unfold reactionFn; ring

/-- Woodford (2003), Table 1.1, p. 41: the Taylor (1999c) and Clarida et al. (2000) inflation
coefficients violate the Taylor principle before 1979 and satisfy it afterwards, while
Orphanides's (2003) real-time estimates exceed one in both periods. -/
theorem table11_taylor_principle :
    (0.81 : ℝ) < 1 ∧ (1 : ℝ) < 1.53 ∧ (0.83 : ℝ) < 1 ∧ (1 : ℝ) < 2.15 ∧
      (1 : ℝ) < 1.49 ∧ (1 : ℝ) < 1.89 := by
  norm_num

/-! ### Partial adjustment (4.5)–(4.6) -/

/-- Woodford (2003), eq. (4.5), p. 41: the funds rate follows the partial-adjustment dynamics
`i_t = (1 − ρ₁) ī_t + ρ₁ i_{t−1} + ρ₂(i_{t−1} − i_{t−2})` towards the desired rate `ibarT`
(stated at date `t + 2`). -/
def PartialAdjustment (ρ₁ ρ₂ : ℝ) (i ibarT : ℕ → ℝ) : Prop :=
  ∀ t, i (t + 2) = (1 - ρ₁) * ibarT (t + 2) + ρ₁ * i (t + 1) + ρ₂ * (i (t + 1) - i t)

/-- Woodford (2003), eq. (4.6), p. 41: the desired funds rate
`ī_t = ī + φ_π(π̄_t − π̄) + φ_x(x_t − γ x_{t−1})` (stated at date `t + 1`; `piStar` is the
book's `π̄`). -/
def DesiredRate (ibar φπ φx γ piStar : ℝ) (infl x ibarT : ℕ → ℝ) : Prop :=
  ∀ t, ibarT (t + 1) = ibar + φπ * (infl (t + 1) - piStar) + φx * (x (t + 1) - γ * x t)

/-- Woodford (2003), (4.5), p. 41: a solution of the homogeneous second-order recursion
`d_{k+2} = T d_{k+1} − D d_k` is `d_{k+2} = p_{k+1} d₁ − D p_k d₀`, with `p` the
Cayley–Hamilton sequence `chSeq`. -/
theorem recursion_eq_chSeq {T D : ℝ} {d : ℕ → ℝ}
    (hd : ∀ k, d (k + 2) = T * d (k + 1) - D * d k) (k : ℕ) :
    d (k + 2) = chSeq T D (k + 1) * d 1 - D * chSeq T D k * d 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => rw [hd 0]; simp [chSeq]
    | 1, _ => rw [hd 1, hd 0]; simp [chSeq]; ring
    | k + 2, ih =>
      rw [hd (k + 2), ih (k + 1) (by omega), ih k (by omega)]
      simp only [chSeq]
      ring

/-- Woodford (2003), (4.5), p. 41: if the desired rate is constant at `c` from date `T₀` on and
the partial-adjustment roots lie inside the unit circle (`SchurStable (ρ₁ + ρ₂) ρ₂`), the funds
rate converges to `c`: partial adjustment changes the dynamics but not the long-run level. -/
theorem partialAdjustment_tendsto {ρ₁ ρ₂ c : ℝ} {i ibarT : ℕ → ℝ}
    (hS : SchurStable (ρ₁ + ρ₂) ρ₂) (hpa : PartialAdjustment ρ₁ ρ₂ i ibarT) {T₀ : ℕ}
    (hc : ∀ t, T₀ ≤ t → ibarT t = c) : Tendsto i atTop (𝓝 c) := by
  set d : ℕ → ℝ := fun k => i (k + T₀) - c with hd_def
  have hd : ∀ k, d (k + 2) = (ρ₁ + ρ₂) * d (k + 1) - ρ₂ * d k := by
    intro k
    have h := hpa (k + T₀)
    rw [hc (k + T₀ + 2) (by omega)] at h
    simp only [hd_def, show k + 2 + T₀ = k + T₀ + 2 by omega,
      show k + 1 + T₀ = k + T₀ + 1 by omega, h]
    ring
  have h1 : Tendsto (fun k => chSeq (ρ₁ + ρ₂) ρ₂ (k + 1)) atTop (𝓝 0) :=
    (tendsto_chSeq hS).comp (tendsto_add_atTop_nat 1)
  have h0 := tendsto_chSeq hS
  have hlim : Tendsto (fun k => d (k + 2)) atTop (𝓝 0) := by
    have := (h1.mul_const (d 1)).sub ((h0.const_mul ρ₂).mul_const (d 0))
    simp only [zero_mul, mul_zero, sub_zero] at this
    refine this.congr fun k => ?_
    rw [recursion_eq_chSeq hd k, mul_assoc]
  have hd0 : Tendsto d atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 2).mp hlim
  have hi : Tendsto (fun k => i (k + T₀)) atTop (𝓝 c) := by
    have := hd0.add_const c
    simp only [zero_add] at this
    refine this.congr fun k => ?_
    simp [hd_def]
  exact (tendsto_add_atTop_iff_nat T₀).mp hi

/-- Woodford (2003), (4.5)–(4.6), p. 41: **long-run responses.** After a permanent change that
holds inflation at `πL` and the output gap at `xL` from date `T₀` on, the funds rate converges to
`ī + φ_π(πL − π̄) + φ_x(1 − γ) xL`. The long-run inflation coefficient is `φ_π` and the long-run
output-gap coefficient is `φ_x(1 − γ)`, whatever the adjustment speeds `ρ₁, ρ₂`. -/
theorem partialAdjustment_longRun {ρ₁ ρ₂ ibar φπ φx γ piStar πL xL : ℝ}
    {i ibarT infl x : ℕ → ℝ} (hS : SchurStable (ρ₁ + ρ₂) ρ₂)
    (hpa : PartialAdjustment ρ₁ ρ₂ i ibarT) (hdes : DesiredRate ibar φπ φx γ piStar infl x ibarT)
    {T₀ : ℕ} (hπ : ∀ t, T₀ ≤ t → infl t = πL) (hx : ∀ t, T₀ ≤ t → x t = xL) :
    Tendsto i atTop (𝓝 (ibar + φπ * (πL - piStar) + φx * (1 - γ) * xL)) := by
  refine partialAdjustment_tendsto hS hpa (T₀ := T₀ + 1) fun t ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [hdes s, hπ (s + 1) (by omega), hx (s + 1) (by omega), hx s (by omega)]
  ring

/-- Woodford (2003), (4.5), p. 41: with `ρ₁ ≠ 1`, a constant funds rate `k` is consistent
with partial adjustment towards a constant desired rate `c` iff `k = c`. -/
theorem partialAdjustment_const_iff {ρ₁ ρ₂ k c : ℝ} (hρ : ρ₁ ≠ 1) :
    PartialAdjustment ρ₁ ρ₂ (fun _ => k) (fun _ => c) ↔ k = c := by
  constructor
  · intro h
    have h0 := h 0
    have : (1 - ρ₁) * (k - c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (by linarith) hρ
    · linarith
  · rintro rfl t
    ring

/-- Woodford (2003), Table 1.1, p. 41: the Judd–Rudebusch partial-adjustment estimates
(Greenspan: `ρ₁ = 0.72`, `ρ₂ = 0.43`; Volcker: `ρ₁ = 0.56`, `ρ₂ = 0`) satisfy the Schur–Cohn
condition, so `partialAdjustment_longRun` applies to them. -/
theorem judd_rudebusch_stable :
    SchurStable (0.72 + 0.43) 0.43 ∧ SchurStable (0.56 + 0) 0 := by
  unfold SchurStable
  norm_num [abs_of_pos]

/-! ### Forecast-based rules and target criteria (4.7)–(4.8) -/

/-- Woodford (2003), eq. (4.7), p. 42: the Clarida–Galí–Gertler forecast-based desired rate
`ī_t = ī + φ_π E_t[π_{t+1} − π̄] + φ_x E_t x_t`. -/
def ForecastDesiredRate (𝔼 : ExpectationSystem Ω) (ibar φπ φx piStar : ℝ)
    (infl x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ibar) + φπ • (𝔼.E t (infl (t + 1)) - fun _ => piStar) + φx • 𝔼.E t (x t)

/-- Woodford (2003), eq. (4.8), p. 44: Svensson's flexible inflation-targeting criterion
`E_t π_{t+j} + λ E_t x_{t+k} = π̄` holds at date `t` (`lam` is the book's `λ > 0`). -/
def TargetCriterion (𝔼 : ExpectationSystem Ω) (piStar lam : ℝ) (j k : ℕ)
    (infl x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  𝔼.E t (infl (t + j)) + lam • 𝔼.E t (x (t + k)) = fun _ => piStar

/-- Woodford (2003), eq. (4.8), p. 44: under perfect foresight the target criterion says
`π_{t+j} + λ x_{t+k} = π̄`. -/
theorem targetCriterion_perfectForesight (piStar lam : ℝ) (j k : ℕ)
    (infl x : ℕ → Unit → ℝ) (t : ℕ) :
    TargetCriterion perfectForesight piStar lam j k infl x t ↔
      infl (t + j) () + lam * x (t + k) () = piStar := by
  unfold TargetCriterion
  have hE : ∀ s (y : Unit → ℝ), perfectForesight.E s y = y := fun _ _ => rfl
  constructor
  · intro h
    simpa [hE] using congrFun h ()
  · intro h
    funext u
    simpa [hE] using h

/-- Woodford (2003), eq. (4.8), p. 44: with `λ > 0` the criterion trades off the two forecasts —
a projected positive output gap requires projected inflation below target. -/
theorem targetCriterion_tradeoff {𝔼 : ExpectationSystem Ω} {piStar lam : ℝ} {j k : ℕ}
    {infl x : ℕ → Ω → ℝ} {t : ℕ} (h : TargetCriterion 𝔼 piStar lam j k infl x t)
    (hlam : 0 < lam) {ω : Ω} (hx : 0 < 𝔼.E t (x (t + k)) ω) :
    𝔼.E t (infl (t + j)) ω < piStar := by
  have := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  nlinarith

end Woodford.ReturnOfMonetaryRules.InterestRateRules

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Neo-Wicksellian price-level determination

Woodford (2003), *Interest and Prices*, Chapter 1, §4.3, pp. 49–52.

The flexible-price IS (Fisher) relation (4.9) `p_t = E_t p_{t+1} + r_t − i_t` and the
Wicksellian rule (4.10) `i_t = ī_t + φ p_t` combine into (4.11)
`p_t = α E_t p_{t+1} + α(r_t − ī_t)`, `α = 1/(1 + φ)`. For `φ > 0` and bounded exogenous
`{r_t, ī_t}` the unique bounded solution is (4.12)
`p_t = ∑_{j ≥ 0} α^{j+1} E_t(r_{t+j} − ī_{t+j})`.

All statements hold for an arbitrary `ExpectationSystem`, so under perfect foresight and under
genuine uncertainty. A bounded equilibrium need not be assumed adapted.

## Main results

* `equilibrium_iff_reduced`: (4.9) + (4.10) ⇔ (4.11) whenever `1 + φ ≠ 0`; `alpha_mem`:
  `0 < α < 1` for `φ > 0`.
* `priceLevel_equilibrium`, `eq_priceLevel`, `existsUnique_priceLevel`: (4.12) is a bounded,
  adapted equilibrium and the only bounded one (via the core `forwardSeries_solves`,
  `eq_forwardSeries`).
* `priceLevel_const`: for constant `r̄, ī` the price level is `p̄ = φ⁻¹(r̄ − ī)`;
  `abs_sub_longRun_le`: the price level stays within `K/φ` of `p̄` when `r_t − ī_t` stays within
  `K` of `r̄ − ī`; `tendsto_longRun`: it converges (uniformly) to `p̄` when `r_t − ī_t` does to
  `r̄ − ī`.
* `equilibrium_mono` (p. 51): the price level rises with `r` and falls with `ī`.
* The role of `φ > 0`: `homog_equilibrium`, `not_unique_of_mem_Icc` (for `−2 ≤ φ ≤ 0`, every
  bounded equilibrium has a continuum of bounded companions, including the exogenous-rate
  case `φ = 0` and the degenerate `φ = −1`), `peg_no_bounded` (for `φ = 0` with a constant
  nonzero `r − ī` there is no bounded equilibrium at all) and the exact characterisation
  `existsUnique_iff`: a unique bounded equilibrium exists for every bounded adapted
  `{r, ī}` if and only if `φ > 0` or `φ < −2`. The book's sufficient condition `φ > 0` is thus
  not necessary (strongly negative responses `φ < −2` also determine an oscillating price
  level); this is recorded as a precision, not an error.

Footnote 44 and (4.13) (sticky prices, the Taylor principle) are forward pointers to
Chapters 2 and 4 and are not formalised here.
-/

namespace Woodford.ReturnOfMonetaryRules.NeoWicksellian

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (4.9), p. 50: the flexible-price IS (Fisher) relation
`p_t = E_t p_{t+1} + r_t − i_t`. -/
def Fisher (r i p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = 𝔼.E t (p (t + 1)) + r t - i t

/-- Woodford (2003), eq. (4.10), p. 50: an equilibrium price path under the Wicksellian rule
`i_t = ī_t + φ p_t`, i.e. (4.9) with the rule substituted for `i_t`. -/
def Equilibrium (φ : ℝ) (r ibar p : ℕ → Ω → ℝ) : Prop :=
  Fisher 𝔼 r (fun t => ibar t + φ • p t) p

/-- Woodford (2003), eq. (4.11), p. 51: `p_t = α E_t p_{t+1} + α(r_t − ī_t)`. -/
def Reduced (α : ℝ) (r ibar p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = α • 𝔼.E t (p (t + 1)) + α • (r t - ibar t)

/-- Woodford (2003), eq. (4.12), p. 51: the forward solution
`p_t = ∑_{j ≥ 0} α^{j+1} E_t(r_{t+j} − ī_{t+j})`, `α = (1 + φ)⁻¹`. -/
noncomputable def priceLevel (φ : ℝ) (r ibar : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, (1 + φ)⁻¹ ^ (j + 1) * 𝔼.E t (r (t + j) - ibar (t + j)) ω

/-- Woodford (2003), p. 51: the coefficient `α = 1/(1 + φ)` satisfies `0 < α < 1` for `φ > 0`. -/
theorem alpha_mem {φ : ℝ} (hφ : 0 < φ) : 0 < (1 + φ)⁻¹ ∧ (1 + φ)⁻¹ < 1 :=
  ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩

/-- Woodford (2003), (4.9)–(4.11), pp. 50–51: substituting the rule (4.10) into (4.9) gives
(4.11) with `α = 1/(1 + φ)`, and conversely (both directions; needs only `1 + φ ≠ 0`). -/
theorem equilibrium_iff_reduced {φ : ℝ} (hφ : 1 + φ ≠ 0) (r ibar p : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 φ r ibar p ↔ Reduced 𝔼 (1 + φ)⁻¹ r ibar p := by
  unfold Equilibrium Fisher Reduced
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_add, eq_inv_mul_iff_mul_eq₀ hφ]
  constructor
  · intro h; linear_combination (1 + φ) * h - φ * h
  · intro h; linear_combination h

/-! ### Equation (4.12): the unique bounded solution -/

/-- Woodford (2003), eq. (4.12), p. 51: the series (4.12) is the core forward series of (4.11),
`∑ αᵏ E_t u_{t+k}` with `u = α(r − ī)`. -/
theorem priceLevel_eq_forwardSeries (φ : ℝ) (r ibar : ℕ → Ω → ℝ) :
    priceLevel 𝔼 φ r ibar = 𝔼.forwardSeries (1 + φ)⁻¹ (fun t => (1 + φ)⁻¹ • (r t - ibar t)) := by
  funext t ω
  unfold priceLevel ExpectationSystem.forwardSeries
  refine tsum_congr fun j => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Woodford (2003), p. 51: the forcing term `α(r − ī)` of (4.11) is bounded by `M_r + M_i`
when `|α| ≤ 1`. -/
theorem forcing_bounded {α Mr Mi : ℝ} (hα : |α| ≤ 1) {r ibar : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hi : ∀ t ω, |ibar t ω| ≤ Mi) (t : ℕ) (ω : Ω) :
    |((fun t => α • (r t - ibar t)) t) ω| ≤ Mr + Mi := by
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
  calc |α| * |r t ω - ibar t ω| ≤ 1 * |r t ω - ibar t ω| := by gcongr
    _ ≤ Mr + Mi := by rw [one_mul]; exact (abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω))

/-- Woodford (2003), p. 51: the forcing term `α(r − ī)` of (4.11) is adapted when `r` and `ī`
are. -/
theorem forcing_adapted (α : ℝ) {r ibar : ℕ → Ω → ℝ} (har : 𝔼.Adapted r)
    (hai : 𝔼.Adapted ibar) : 𝔼.Adapted (fun t => α • (r t - ibar t)) := by
  intro t
  simp only [map_smul, map_sub, har t, hai t]

/-- Woodford (2003), eq. (4.12), p. 51 (existence): for `φ > 0` and bounded adapted `{r, ī}`,
the price level (4.12) is an equilibrium, bounded and adapted. -/
theorem priceLevel_equilibrium {φ Mr Mi : ℝ} (hφ : 0 < φ) {r ibar : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hi : ∀ t ω, |ibar t ω| ≤ Mi) (har : 𝔼.Adapted r)
    (hai : 𝔼.Adapted ibar) :
    Equilibrium 𝔼 φ r ibar (priceLevel 𝔼 φ r ibar) ∧ BoundedProc (priceLevel 𝔼 φ r ibar) ∧
      𝔼.Adapted (priceLevel 𝔼 φ r ibar) := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  have hα : |(1 + φ)⁻¹| ≤ 1 := by rw [abs_of_pos h0]; exact h1.le
  have hu := forcing_bounded hα hr hi
  have hua := forcing_adapted 𝔼 (1 + φ)⁻¹ har hai
  rw [priceLevel_eq_forwardSeries]
  refine ⟨(equilibrium_iff_reduced 𝔼 (by linarith) r ibar _).mpr fun t => ?_,
    𝔼.forwardSeries_bounded h0.le h1 hu, 𝔼.forwardSeries_adapted h0.le h1 hu⟩
  exact 𝔼.forwardSeries_solves h0.le h1 hu hua t

/-- Woodford (2003), eq. (4.12), p. 51 (uniqueness): for `φ > 0` and bounded adapted `{r, ī}`,
every bounded equilibrium price path is (4.12). -/
theorem eq_priceLevel {φ Mr Mi : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hi : ∀ t ω, |ibar t ω| ≤ Mi) (har : 𝔼.Adapted r)
    (hai : 𝔼.Adapted ibar) (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p) :
    p = priceLevel 𝔼 φ r ibar := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  have hα : |(1 + φ)⁻¹| ≤ 1 := by rw [abs_of_pos h0]; exact h1.le
  rw [priceLevel_eq_forwardSeries]
  exact 𝔼.eq_forwardSeries h0.le h1 (forcing_bounded hα hr hi)
    (forcing_adapted 𝔼 (1 + φ)⁻¹ har hai)
    ((equilibrium_iff_reduced 𝔼 (by linarith) r ibar p).mp hp) hpb

/-- Woodford (2003), eq. (4.12), p. 51: for `φ > 0` and bounded adapted `{r, ī}` there is
exactly one bounded equilibrium price path. -/
theorem existsUnique_priceLevel {φ : ℝ} (hφ : 0 < φ) {r ibar : ℕ → Ω → ℝ}
    (hrb : BoundedProc r) (hib : BoundedProc ibar) (har : 𝔼.Adapted r) (hai : 𝔼.Adapted ibar) :
    ∃! p, BoundedProc p ∧ Equilibrium 𝔼 φ r ibar p := by
  obtain ⟨Mr, hr⟩ := hrb
  obtain ⟨Mi, hi⟩ := hib
  obtain ⟨he, hb, -⟩ := priceLevel_equilibrium 𝔼 hφ hr hi har hai
  exact ⟨_, ⟨hb, he⟩, fun p hp => eq_priceLevel 𝔼 hφ hr hi har hai hp.2 hp.1⟩

/-! ### The long-run price level `p̄ = φ⁻¹(r̄ − ī)` -/

/-- Woodford (2003), p. 51: an a-priori bound for forward equations. If `z` is bounded,
`z_t = a E_t z_{t+1} + u_t` with `|a| < 1`, and `|u_t| ≤ K` from date `N` on, then
`|z_t| ≤ K/(1 − |a|)` from date `N` on (no adaptedness needed). -/
theorem abs_le_of_forward {a M K : ℝ} (ha : |a| < 1) {z u : ℕ → Ω → ℝ} (N : ℕ)
    (hz : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) (hM : ∀ t ω, |z t ω| ≤ M)
    (hK : ∀ t, N ≤ t → ∀ ω, |u t ω| ≤ K) (t : ℕ) (ht : N ≤ t) (ω : Ω) :
    |z t ω| ≤ K / (1 - |a|) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK t ht ω)
  have h1 : 0 < 1 - |a| := by linarith
  have hKa : 0 ≤ K / (1 - |a|) := div_nonneg hK0 h1.le
  have key : ∀ n : ℕ, ∀ s, N ≤ s → ∀ ω', |z s ω'| ≤ |a| ^ n * M + K / (1 - |a|) := by
    intro n
    induction n with
    | zero =>
      intro s _ ω'
      have := hM s ω'
      rw [pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro s hs ω'
      have hE := 𝔼.abs_E_le (fun ω'' => ih (s + 1) (by omega) ω'') s ω'
      rw [hz s]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * 𝔼.E s (z (s + 1)) ω' + u s ω'|
          ≤ |a| * |𝔼.E s (z (s + 1)) ω'| + |u s ω'| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |a| * (|a| ^ n * M + K / (1 - |a|)) + K := by
            gcongr
            exact hK s hs ω'
        _ = |a| ^ (n + 1) * M + K / (1 - |a|) := by
            field_simp
            ring
  have hlim : Tendsto (fun n : ℕ => |a| ^ n * M + K / (1 - |a|)) atTop
      (𝓝 (K / (1 - |a|))) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const M).add_const
      (K / (1 - |a|))
  exact ge_of_tendsto' hlim fun n => key n t ht ω

/-- Woodford (2003), p. 51: deviations of an equilibrium price level from `c₀/φ` satisfy the
forward equation (4.11) with forcing `α(r_t − ī_t − c₀)`. -/
theorem deviation_reduced {φ : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (c₀ : ℝ) (t : ℕ) :
    p t - (fun _ => c₀ / φ) = (1 + φ)⁻¹ • 𝔼.E t (p (t + 1) - fun _ => c₀ / φ) +
      (1 + φ)⁻¹ • (r t - ibar t - fun _ => c₀) := by
  funext ω
  have h := congrFun (hp t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  have h1 : (1 + φ)⁻¹ * (1 + φ) = 1 := inv_mul_cancel₀ (by linarith)
  have h2 : c₀ / φ * φ = c₀ := div_mul_cancel₀ c₀ hφ.ne'
  rw [map_sub, 𝔼.const]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (1 + φ)⁻¹ * h + (c₀ / φ - p t ω) * h1 - (1 + φ)⁻¹ * h2

/-- Woodford (2003), p. 51: "the equilibrium price level fluctuates in a bounded interval around
the long-run average value `p̄ ≡ φ⁻¹(r̄ − ī)`". Precisely: if `|r_t − ī_t − (r̄ − ī)| ≤ K`
always, every bounded equilibrium satisfies `|p_t − p̄| ≤ K/φ`. -/
theorem abs_sub_longRun_le {φ rbar ib K : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p)
    (hK : ∀ t ω, |r t ω - ibar t ω - (rbar - ib)| ≤ K) (t : ℕ) (ω : Ω) :
    |p t ω - (rbar - ib) / φ| ≤ K / φ := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  obtain ⟨M, hM⟩ := hpb
  have hz := deviation_reduced 𝔼 hφ hp (rbar - ib)
  have hzb : ∀ t ω, |((p t - fun _ => (rbar - ib) / φ : Ω → ℝ)) ω| ≤ M + |(rbar - ib) / φ| :=
    fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)
  have hu : ∀ t, 0 ≤ t → ∀ ω,
      |(((1 + φ)⁻¹ • (r t - ibar t - fun _ => rbar - ib) : Ω → ℝ)) ω| ≤ (1 + φ)⁻¹ * K := by
    intro t _ ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_of_pos h0]
    exact mul_le_mul_of_nonneg_left (hK t ω) h0.le
  have hα : |(1 + φ)⁻¹| < 1 := by rw [abs_of_pos h0]; exact h1
  have := abs_le_of_forward 𝔼 hα 0 hz hzb hu t (Nat.zero_le t) ω
  rw [abs_of_pos h0] at this
  have hφ0 : φ ≠ 0 := hφ.ne'
  have hφ1 : 1 + φ ≠ 0 := by linarith
  have he : (1 + φ)⁻¹ * K / (1 - (1 + φ)⁻¹) = K / φ := by
    field_simp
    rw [add_sub_cancel_left, mul_div_assoc, mul_div_cancel₀ K hφ0]
  simpa [he] using this

/-- Woodford (2003), p. 51: with constant `r_t = r̄` and `ī_t = ī`, the unique bounded
equilibrium is the constant `p̄ = φ⁻¹(r̄ − ī)`. -/
theorem priceLevel_const {φ rbar ib : ℝ} (hφ : 0 < φ) {p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ (fun _ _ => rbar) (fun _ _ => ib) p) (hpb : BoundedProc p) :
    ∀ t ω, p t ω = φ⁻¹ * (rbar - ib) := by
  intro t ω
  have h := abs_sub_longRun_le 𝔼 (rbar := rbar) (ib := ib) (K := 0) hφ hp hpb
    (fun _ _ => by simp) t ω
  rw [zero_div, abs_nonpos_iff, sub_eq_zero] at h
  rw [h, div_eq_inv_mul]

/-- Woodford (2003), p. 51: the constant `p̄ = φ⁻¹(r̄ − ī)` is indeed an equilibrium for
constant `r̄, ī` (so `priceLevel_const` is not vacuous). -/
theorem longRun_equilibrium {φ : ℝ} (hφ : 0 < φ) (rbar ib : ℝ) :
    Equilibrium 𝔼 φ (fun _ _ => rbar) (fun _ _ => ib) (fun _ _ => φ⁻¹ * (rbar - ib)) := by
  intro t
  rw [𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), p. 51: if `r_t − ī_t` converges (uniformly over states) to `r̄ − ī`, every
bounded equilibrium price level converges uniformly to `p̄ = φ⁻¹(r̄ − ī)`. -/
theorem tendsto_longRun {φ rbar ib : ℝ} (hφ : 0 < φ) {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p)
    (hconv : ∀ ε > 0, ∃ N, ∀ t, N ≤ t → ∀ ω, |r t ω - ibar t ω - (rbar - ib)| ≤ ε) :
    ∀ ε > 0, ∃ N, ∀ t, N ≤ t → ∀ ω, |p t ω - (rbar - ib) / φ| ≤ ε := by
  intro ε hε
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  obtain ⟨M, hM⟩ := hpb
  obtain ⟨N, hN⟩ := hconv (φ * ε) (mul_pos hφ hε)
  refine ⟨N, fun t ht ω => ?_⟩
  have hz := deviation_reduced 𝔼 hφ hp (rbar - ib)
  have hzb : ∀ t ω, |((p t - fun _ => (rbar - ib) / φ : Ω → ℝ)) ω| ≤ M + |(rbar - ib) / φ| :=
    fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)
  have hu : ∀ t, N ≤ t → ∀ ω,
      |(((1 + φ)⁻¹ • (r t - ibar t - fun _ => rbar - ib) : Ω → ℝ)) ω| ≤ (1 + φ)⁻¹ * (φ * ε) := by
    intro t ht ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_of_pos h0]
    exact mul_le_mul_of_nonneg_left (hN t ht ω) h0.le
  have hα : |(1 + φ)⁻¹| < 1 := by rw [abs_of_pos h0]; exact h1
  have := abs_le_of_forward 𝔼 hα N hz hzb hu t ht ω
  rw [abs_of_pos h0] at this
  have hφ0 : φ ≠ 0 := hφ.ne'
  have hφ1 : 1 + φ ≠ 0 := by linarith
  have he : (1 + φ)⁻¹ * (φ * ε) / (1 - (1 + φ)⁻¹) = ε := by
    field_simp
    rw [add_sub_cancel_left, div_self hφ0]
  simpa [he] using this

/-! ### Comparative statics (p. 51) -/

/-- Woodford (2003), p. 51: a comparison principle for forward equations. If `z` is bounded,
`z_t = a E_t z_{t+1} + u_t` with `0 ≤ a < 1` and `u ≥ 0`, then `z ≥ 0`. -/
theorem nonneg_of_forward {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {z u : ℕ → Ω → ℝ}
    (hz : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) (hM : ∀ t ω, |z t ω| ≤ M)
    (hu : ∀ t ω, 0 ≤ u t ω) (t : ℕ) (ω : Ω) : 0 ≤ z t ω := by
  have key : ∀ n : ℕ, ∀ s ω', -(a ^ n * M) ≤ z s ω' := by
    intro n
    induction n with
    | zero =>
      intro s ω'
      have := neg_abs_le (z s ω')
      rw [pow_zero, one_mul]
      linarith [hM s ω']
    | succ n ih =>
      intro s ω'
      have hle : (fun _ => -(a ^ n * M)) ≤ z (s + 1) := fun ω'' => ih (s + 1) ω''
      have hE : -(a ^ n * M) ≤ 𝔼.E s (z (s + 1)) ω' := by
        have := 𝔼.mono s hle ω'
        rwa [𝔼.const] at this
      rw [hz s]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left hE ha0
      have hp : a * -(a ^ n * M) = -(a ^ (n + 1) * M) := by ring
      linarith [hu s ω']
  have hlim : Tendsto (fun n : ℕ => -(a ^ n * M)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const M).neg
  exact le_of_tendsto' hlim fun n => key n t ω

/-- Woodford (2003), p. 51: the equilibrium price level is increased by a rise in the real rate
`r` not matched by policy, and by a loosening of policy (a lower intercept `ī`): if
`r ≤ r'` and `ī' ≤ ī` in every date and state, the bounded equilibria satisfy `p ≤ p'`. -/
theorem equilibrium_mono {φ : ℝ} (hφ : 0 < φ) {r r' ibar ibar' p p' : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (hp' : Equilibrium 𝔼 φ r' ibar' p')
    (hpb : BoundedProc p) (hpb' : BoundedProc p') (hr : ∀ t ω, r t ω ≤ r' t ω)
    (hi : ∀ t ω, ibar' t ω ≤ ibar t ω) (t : ℕ) (ω : Ω) : p t ω ≤ p' t ω := by
  obtain ⟨h0, h1⟩ := alpha_mem hφ
  obtain ⟨M, hM⟩ := hpb
  obtain ⟨M', hM'⟩ := hpb'
  have e := (equilibrium_iff_reduced 𝔼 (by linarith) r ibar p).mp hp
  have e' := (equilibrium_iff_reduced 𝔼 (by linarith) r' ibar' p').mp hp'
  have hz : ∀ s, (p' s - p s) = (1 + φ)⁻¹ • 𝔼.E s (p' (s + 1) - p (s + 1)) +
      (1 + φ)⁻¹ • ((r' s - ibar' s) - (r s - ibar s)) := by
    intro s
    rw [map_sub]
    funext ω
    have h1 := congrFun (e s) ω
    have h2 := congrFun (e' s) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination h2 - h1
  have hzb : ∀ s ω, |(p' s - p s) ω| ≤ M' + M :=
    fun s ω => (abs_sub _ _).trans (add_le_add (hM' s ω) (hM s ω))
  have hu : ∀ s ω, 0 ≤ ((1 + φ)⁻¹ • ((r' s - ibar' s) - (r s - ibar s))) ω := by
    intro s ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact mul_nonneg h0.le (by linarith [hr s ω, hi s ω])
  have := nonneg_of_forward 𝔼 h0.le h1 hz hzb hu t ω
  simp only [Pi.sub_apply] at this
  linarith

/-- Woodford (2003), eq. (4.12), p. 51: every weight `α^{j+1}` in (4.12) is positive, so news of
a higher future real rate or a lower future intercept raises the price level immediately. -/
theorem weights_pos {φ : ℝ} (hφ : 0 < φ) (j : ℕ) : 0 < (1 + φ)⁻¹ ^ (j + 1) :=
  pow_pos (alpha_mem hφ).1 _

/-! ### The role of `φ > 0`: indeterminacy and the exact determinacy region -/

/-- Woodford (2003), pp. 38, 51: the homogeneous path `q_t = (1 + φ)ᵗ`. -/
def homog (φ : ℝ) : ℕ → Ω → ℝ := fun t _ => (1 + φ) ^ t

/-- Woodford (2003), (4.9)–(4.10): `q_t = (1 + φ)ᵗ` solves the equilibrium conditions with
`r = ī = 0`, for every `φ` (for `φ = −1` it is `1, 0, 0, …`). -/
theorem homog_equilibrium (φ : ℝ) :
    Equilibrium 𝔼 φ (fun _ _ => 0) (fun _ _ => 0) (homog φ) := by
  intro t
  unfold homog
  rw [𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (4.9)–(4.10): adding any multiple of the homogeneous path to an equilibrium
gives another equilibrium. -/
theorem equilibrium_add_homog {φ : ℝ} {r ibar p : ℕ → Ω → ℝ}
    (hp : Equilibrium 𝔼 φ r ibar p) (c : ℝ) :
    Equilibrium 𝔼 φ r ibar (p + c • homog φ) := by
  intro t
  have hq := homog_equilibrium 𝔼 φ t
  have hpt := hp t
  funext ω
  have h1 := congrFun hpt ω
  have h2 := congrFun hq ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add,
    map_smul] at h1 h2 ⊢
  linear_combination h1 + c * h2

/-- Woodford (2003), p. 51: the homogeneous path is bounded exactly when `−2 ≤ φ ≤ 0`
(this direction: it is bounded by `1` there). -/
theorem homog_bounded {φ : ℝ} (h1 : -2 ≤ φ) (h2 : φ ≤ 0) : BoundedProc (homog (Ω := Ω) φ) := by
  refine ⟨1, fun t _ => ?_⟩
  unfold homog
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Woodford (2003), pp. 38, 51 (the role of `φ > 0`): for `−2 ≤ φ ≤ 0` — in particular for an
exogenous interest-rate path, `φ = 0` — every bounded equilibrium `p` has the bounded
companions `p + c (1 + φ)ᵗ`, all distinct: the price level is indeterminate. -/
theorem not_unique_of_mem_Icc [Nonempty Ω] {φ : ℝ} (h1 : -2 ≤ φ) (h2 : φ ≤ 0)
    {r ibar p : ℕ → Ω → ℝ} (hp : Equilibrium 𝔼 φ r ibar p) (hpb : BoundedProc p) (c : ℝ) :
    Equilibrium 𝔼 φ r ibar (p + c • homog φ) ∧ BoundedProc (p + c • homog φ) ∧
      (c ≠ 0 → p + c • homog φ ≠ p) := by
  refine ⟨equilibrium_add_homog 𝔼 hp c, ?_, fun hc h => ?_⟩
  · obtain ⟨M, hM⟩ := hpb
    obtain ⟨Mq, hMq⟩ := homog_bounded (Ω := Ω) h1 h2
    refine ⟨M + |c| * Mq, fun t ω => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMq t ω) (abs_nonneg c)
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun h 0) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, homog, pow_zero, mul_one,
      add_eq_left] at this
    exact hc this

/-- Woodford (2003), p. 38 and §4.3: with an exogenous interest-rate path (`φ = 0`) and a
constant nonzero gap `r_t − ī_t = κ`, there is no bounded equilibrium at all (`E₀ p_t` drifts by
`−κ` each period). Together with `not_unique_of_mem_Icc` this shows that under an interest-rate
peg a bounded equilibrium either fails to exist or is not unique. -/
theorem peg_no_bounded [Nonempty Ω] {κ : ℝ} (hκ : κ ≠ 0) {r ibar p : ℕ → Ω → ℝ}
    (hgap : ∀ t, r t - ibar t = fun _ => κ) (hp : Equilibrium 𝔼 0 r ibar p) :
    ¬ BoundedProc p := by
  rintro ⟨M, hM⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hstep : ∀ t, 𝔼.E 0 (p t) = 𝔼.E 0 (p (t + 1)) + fun _ => κ := by
    intro t
    have h : p t = 𝔼.E t (p (t + 1)) + (r t - ibar t) := by
      rw [hp t]; simp only [zero_smul, add_zero]; abel
    rw [hgap t] at h
    conv_lhs => rw [h]
    rw [map_add, 𝔼.tower (Nat.zero_le t), 𝔼.const]
  have hdrift : ∀ t : ℕ, 𝔼.E 0 (p t) ω = 𝔼.E 0 (p 0) ω - t * κ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := congrFun (hstep t) ω
      simp only [Pi.add_apply] at this
      push_cast
      linarith
  have hb : ∀ t, |𝔼.E 0 (p t) ω| ≤ M := fun t => 𝔼.abs_E_le (hM t) 0 ω
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / |κ|)
  have hκ' : 0 < |κ| := abs_pos.mpr hκ
  have h1 := hb n
  have h2 := hb 0
  rw [hdrift n] at h1
  have h3 : |(n : ℝ) * κ| ≤ 2 * M := by
    calc |(n : ℝ) * κ| = |𝔼.E 0 (p 0) ω - (𝔼.E 0 (p 0) ω - n * κ)| := by ring_nf
      _ ≤ |𝔼.E 0 (p 0) ω| + |𝔼.E 0 (p 0) ω - n * κ| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  rw [abs_mul, Nat.abs_cast] at h3
  rw [div_lt_iff₀ hκ'] at hn
  linarith

/-- Woodford (2003), p. 51 (general `|a| < 1`): the forward series solves
`z_t = a E_t z_{t+1} + u_t` for bounded adapted `u` and any `|a| < 1`, including negative `a`
(the core `forwardSeries_solves` covers `0 ≤ a < 1`; this extends its proof). -/
theorem forwardSeries_solves_abs {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) (t : ℕ) :
    𝔼.forwardSeries a u t = a • 𝔼.E t (𝔼.forwardSeries a u (t + 1)) + u t := by
  have ha0 : 0 ≤ |a| := abs_nonneg a
  have hsum : ∀ s ω, Summable (fun k => a ^ k * 𝔼.E s (u (s + k)) ω) := fun s ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha).mul_right M) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (s + k)) s ω) (pow_nonneg ha0 k))
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
  rw [hE, (hsum t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero, hadapt t,
    ← tsum_mul_left, add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Woodford (2003), p. 51 (general `|a| < 1`): the forward series of a bounded process is
bounded by `M/(1 − |a|)`. -/
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

/-- Woodford (2003), §4.3, pp. 50–51 (exact determinacy region, sharpening the book's `φ > 0`):
for every bounded adapted `{r, ī}` there is exactly one bounded equilibrium price path if and
only if `φ > 0` or `φ < −2`, i.e. `|1 + φ| > 1`. -/
theorem existsUnique_iff [Nonempty Ω] (φ : ℝ) :
    (∀ r ibar : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ibar → 𝔼.Adapted r →
      𝔼.Adapted ibar → ∃! p, BoundedProc p ∧ Equilibrium 𝔼 φ r ibar p) ↔
      (0 < φ ∨ φ < -2) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hz : 𝔼.Adapted (fun _ _ => (0 : ℝ)) := fun t => 𝔼.const t 0
    have hzb : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
    obtain ⟨p, -, hu⟩ := h _ _ hzb hzb hz hz
    have h0 : Equilibrium 𝔼 φ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
      intro t
      rw [𝔼.const]
      funext ω
      simp
    have e0 := hu _ ⟨hzb, h0⟩
    have eq := hu _ ⟨homog_bounded hc2 hc1, homog_equilibrium 𝔼 φ⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (eq.trans e0.symm) 0) ω
    simp [homog] at this
  · intro hφ r ibar ⟨Mr, hr⟩ ⟨Mi, hi⟩ har hai
    have hne : 1 + φ ≠ 0 := by rcases hφ with h | h <;> intro h' <;> linarith
    have hα : |(1 + φ)⁻¹| < 1 := by
      rw [abs_inv]
      refine inv_lt_one_of_one_lt₀ ?_
      rcases hφ with h | h
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    have hu := forcing_bounded hα.le hr hi
    have hua := forcing_adapted 𝔼 (1 + φ)⁻¹ har hai
    refine ⟨𝔼.forwardSeries (1 + φ)⁻¹ (fun t => (1 + φ)⁻¹ • (r t - ibar t)),
      ⟨forwardSeries_bounded_abs 𝔼 hα hu, (equilibrium_iff_reduced 𝔼 hne r ibar _).mpr
        fun t => forwardSeries_solves_abs 𝔼 hα hu hua t⟩, fun p hp => ?_⟩
    exact 𝔼.forward_unique hα ((equilibrium_iff_reduced 𝔼 hne r ibar p).mp hp.2)
      (fun t => forwardSeries_solves_abs 𝔼 hα hu hua t) hp.1 (forwardSeries_bounded_abs 𝔼 hα hu)

end Woodford.ReturnOfMonetaryRules.NeoWicksellian

set_option linter.style.longLine false
#print axioms Woodford.ReturnOfMonetaryRules.SchurStable
#print axioms Woodford.ReturnOfMonetaryRules.disc
#print axioms Woodford.ReturnOfMonetaryRules.root₁
#print axioms Woodford.ReturnOfMonetaryRules.root₂
#print axioms Woodford.ReturnOfMonetaryRules.root_sum
#print axioms Woodford.ReturnOfMonetaryRules.root_prod
#print axioms Woodford.ReturnOfMonetaryRules.root_eq
#print axioms Woodford.ReturnOfMonetaryRules.normSq_root_of_neg
#print axioms Woodford.ReturnOfMonetaryRules.norm_root_of_nonneg
#print axioms Woodford.ReturnOfMonetaryRules.schurStable_iff_roots
#print axioms Woodford.ReturnOfMonetaryRules.chSeq
#print axioms Woodford.ReturnOfMonetaryRules.convSeq
#print axioms Woodford.ReturnOfMonetaryRules.convSeq_rec
#print axioms Woodford.ReturnOfMonetaryRules.chSeq_eq_convSeq
#print axioms Woodford.ReturnOfMonetaryRules.norm_convSeq_le
#print axioms Woodford.ReturnOfMonetaryRules.abs_chSeq_le
#print axioms Woodford.ReturnOfMonetaryRules.tendsto_chSeq
#print axioms Woodford.ReturnOfMonetaryRules.tr2
#print axioms Woodford.ReturnOfMonetaryRules.det2
#print axioms Woodford.ReturnOfMonetaryRules.tr2_eq_trace
#print axioms Woodford.ReturnOfMonetaryRules.det2_eq_det
#print axioms Woodford.ReturnOfMonetaryRules.sq_eq_cayleyHamilton
#print axioms Woodford.ReturnOfMonetaryRules.pow_succ_eq
#print axioms Woodford.ReturnOfMonetaryRules.abs_pow_entry_le
#print axioms Woodford.ReturnOfMonetaryRules.tendsto_pow_entry
#print axioms Woodford.ReturnOfMonetaryRules.BoundedSeq
#print axioms Woodford.ReturnOfMonetaryRules.homogeneous_iterate
#print axioms Woodford.ReturnOfMonetaryRules.abs_mulVec_le
#print axioms Woodford.ReturnOfMonetaryRules.homogeneous_eq_zero
#print axioms Woodford.ReturnOfMonetaryRules.eq_root_of_eq
#print axioms Woodford.ReturnOfMonetaryRules.exists_eigenvector
#print axioms Woodford.ReturnOfMonetaryRules.exists_bounded_homogeneous
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.mk
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.E
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.const
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.mono
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.tower
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.known
#print axioms Woodford.ReturnOfMonetaryRules.perfectForesight
#print axioms Woodford.ReturnOfMonetaryRules.BoundedProc
#print axioms Woodford.ReturnOfMonetaryRules.BoundedVec
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.Adapted
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.IsAR1
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.E_neg
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.E_smul
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.E_E_self
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.abs_E_le
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.bounded_E
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.ar1_iterate
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forward_iterate
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forward_unique
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forward_ar1_solves
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.E_tsum
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forwardSeries
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forwardSeries_summable
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forwardSeries_solves
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forwardSeries_bounded
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.eq_forwardSeries
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.forwardSeries_adapted
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.PullOut
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.Solves
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.AdaptedVec
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.system_iterate
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.system_unique
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.system_not_unique
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.Determinate
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationSystem.determinate_iff
#print axioms Woodford.ReturnOfMonetaryRules.perfectForesight_pullOut
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.info
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.num
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinObs
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinTree
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinSystem
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.firstHeads
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinShock
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinAR1
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinShock_measurable
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Woodford.ReturnOfMonetaryRules.ExpectationsFiniteTree.finiteTree_pullOut
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.IsCDF
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.IsCDF.nonneg
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.IsCDF.le_one
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.isCDF_cdf
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.exists_measure_of_isCDF
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_mem_channel
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_antitone
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_strictAnti
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.cdf_rate_mem_channel
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.cdf_rate_antitone
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_channel
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_eq_target_iff
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.exists_eq_half
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.target_supply_iff
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.existsUnique_target_supply
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.target_supply_set_indep
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.target_supply_symmetric
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_shift_channel
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.cdf_dirac_zero_of_neg
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_noClearing
#print axioms Woodford.ReturnOfMonetaryRules.ChannelSystem.rate_noClearing_indep
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.WicksellRule
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.DifferenceRule
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.difference_iff_wicksell
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.wicksell_intercept_eq
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.wicksell_imp_difference
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.wicksell_violates_zlb
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.reactionFn
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.taylorRule
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.taylorRule_eq_reactionFn
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.taylorRule_at_target
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.taylorRule_real_rate_at_target
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.taylorPrinciple_iff
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.taylorRule_real_rate_rises
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.goodhartRule_eq_reactionFn
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.table11_taylor_principle
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.PartialAdjustment
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.DesiredRate
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.recursion_eq_chSeq
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.partialAdjustment_tendsto
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.partialAdjustment_longRun
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.partialAdjustment_const_iff
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.judd_rudebusch_stable
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.ForecastDesiredRate
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.TargetCriterion
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.targetCriterion_perfectForesight
#print axioms Woodford.ReturnOfMonetaryRules.InterestRateRules.targetCriterion_tradeoff
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.Fisher
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.Equilibrium
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.Reduced
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.priceLevel
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.alpha_mem
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.equilibrium_iff_reduced
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.priceLevel_eq_forwardSeries
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.forcing_bounded
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.forcing_adapted
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.priceLevel_equilibrium
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.eq_priceLevel
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.existsUnique_priceLevel
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.abs_le_of_forward
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.deviation_reduced
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.abs_sub_longRun_le
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.priceLevel_const
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.longRun_equilibrium
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.tendsto_longRun
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.nonneg_of_forward
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.equilibrium_mono
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.weights_pos
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.homog
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.homog_equilibrium
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.equilibrium_add_homog
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.homog_bounded
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.not_unique_of_mem_Icc
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.peg_no_bounded
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.forwardSeries_solves_abs
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.forwardSeries_bounded_abs
#print axioms Woodford.ReturnOfMonetaryRules.NeoWicksellian.existsUnique_iff
