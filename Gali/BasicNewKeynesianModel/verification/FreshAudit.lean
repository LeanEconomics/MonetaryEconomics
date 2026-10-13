import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Fin.VecNotation
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Calvo price durations

Galí (2015), Chapter 3, §3.2 (p. 55). Each period a firm may reset its price
with probability `1 − θ`, independently of its history. A price set today is
still in force `k` periods later with probability `θᵏ`, and its duration (the
number of periods until the first reset opportunity, counting the current one)
is `k ≥ 1` with probability `(1 − θ) θ^{k−1}`. The book states that the
average duration of a price is `1/(1 − θ)`.

## Main results

* `survival_sum`: the duration probabilities sum to one.
* `mean_duration`: the expected duration is `1/(1 − θ)` (Galí, p. 55).
* `CalvoParam`: the Calvo parameter `θ ∈ [0, 1)` bundled with its range, the
  form later modules use.
-/

namespace Gali.BasicNewKeynesianModel

/-- The probability that a price lasts exactly `k + 1` periods,
`(1 − θ) θᵏ` (Galí, p. 55). Durations are indexed from `0` so that the
duration `k + 1 ≥ 1` has index `k`. -/
noncomputable def durationProb (θ : ℝ) (k : ℕ) : ℝ := (1 - θ) * θ ^ k

/-- Duration probabilities are nonnegative for `θ ∈ [0, 1]`. -/
theorem durationProb_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (k : ℕ) :
    0 ≤ durationProb θ k :=
  mul_nonneg (by linarith) (pow_nonneg h0 k)

/-- The duration probabilities form a distribution: `∑ₖ (1 − θ) θᵏ = 1`
for `θ ∈ [0, 1)`. -/
theorem survival_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' k, durationProb θ k = 1 := by
  unfold durationProb
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp [sub_ne_zero.mpr (ne_of_lt h1).symm]

/-- The probability that a price set today is still in force after `k`
periods is `θᵏ`: the tail mass of the duration distribution beyond `k`
periods, `∑_{j ≥ k} (1 − θ) θʲ = θᵏ`. -/
theorem tail_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (k : ℕ) :
    ∑' j, durationProb θ (j + k) = θ ^ k := by
  unfold durationProb
  have hs : ∀ j, (1 - θ) * θ ^ (j + k) = θ ^ k * ((1 - θ) * θ ^ j) := by
    intro j; ring
  simp_rw [hs]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp [sub_ne_zero.mpr (ne_of_lt h1).symm]

/-- **Average price duration** (Galí, p. 55): with reset probability `1 − θ`,
the expected duration of a price is `∑ₖ (k + 1)(1 − θ) θᵏ = 1/(1 − θ)`. -/
theorem mean_duration {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb θ k = 1 / (1 - θ) := by
  have hn : ‖θ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hA : Summable fun k : ℕ => (k : ℝ) * θ ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hn |>.congr fun k => by simp
  have hB : Summable fun k : ℕ => θ ^ k := summable_geometric_of_lt_one h0 h1
  have hs : ∀ k : ℕ, ((k : ℝ) + 1) * durationProb θ k
      = (1 - θ) * ((k : ℝ) * θ ^ k) + (1 - θ) * θ ^ k := by
    intro k; unfold durationProb; ring
  simp_rw [hs]
  rw [(hA.mul_left _).tsum_add (hB.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one hn, tsum_geometric_of_lt_one h0 h1]
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  field_simp
  ring

/-- A Calvo price-stickiness parameter: `θ` is the probability that a firm
cannot reset its price in a given period, with `0 ≤ θ < 1` (Galí, p. 55). -/
structure CalvoParam where
  /-- The probability of not resetting the price this period. -/
  θ : ℝ
  nonneg : 0 ≤ θ
  lt_one : θ < 1

/-- The average duration of a price under a Calvo parameter is `1/(1 − θ)`
(Galí, p. 55). -/
theorem CalvoParam.mean_duration (c : CalvoParam) :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb c.θ k = 1 / (1 - c.θ) :=
  Gali.BasicNewKeynesianModel.mean_duration c.nonneg c.lt_one

end Gali.BasicNewKeynesianModel

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
-/

namespace Gali.BasicNewKeynesianModel

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

end Gali.BasicNewKeynesianModel

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
-/

namespace Gali.BasicNewKeynesianModel

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

end Gali.BasicNewKeynesianModel

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
-/

namespace Gali.BasicNewKeynesianModel.ExpectationsFiniteTree

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

end Gali.BasicNewKeynesianModel.ExpectationsFiniteTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dixit–Stiglitz (CES) aggregation

Galí (2015), Chapter 3, §3.1 (p. 53), eq. (12) (p. 58) and Appendix 3.1 (p. 83).

Goods are indexed by a measure space `(G, μ)`: the book's continuum `[0, 1]` with Lebesgue
measure is `μ = volume.restrict (Set.Icc 0 1)`, and a finite (discretised) set of goods with
weights `w i` is `μ = weightMeasure w`. For an elasticity of substitution `ε > 1`, write
`r = (ε − 1)/ε ∈ (0, 1)`. The consumption index is `C = (∫ C(i)^r)^{1/r}` and the price index
is `P = (∫ P(i)^{1−ε})^{1/(1−ε)}`.

## Main results

* `spend_ge`: expenditure minimisation — every bundle `C(·) ≥ 0` costs at least `P · C`,
  where `C` is the bundle's own CES aggregate.
* `spend_eq_iff`: the cost is exactly `P · C` iff `C(i) = (P(i)/P)^{−ε} C` almost everywhere
  (both directions): eq. (1).
* `cesAgg_demand`, `spend_demand`: the demand schedule (1) delivers the aggregate `C` exactly
  and costs exactly `P C` (p. 53).
* `cesAgg_le_of_spend`, `cesAgg_eq_iff_of_spend`: the book's dual form (App. 3.1): for given
  expenditure `X`, the attainable index is at most `X / P`, with equality iff
  `C(i) = (P(i)/P)^{−ε} X/P` a.e.
* `market_clearing`: eq. (12), `Y = C`, and `Y(i) = (P(i)/P)^{−ε} Y`.
* `unitInterval_expenditure_minimisation` and `finite_expenditure_minimisation`: the results
  for the continuum `[0, 1]` and for finitely many goods with positive weights.

The proof replaces the Lagrangian of App. 3.1 by a pointwise weighted AM–GM (Young) inequality
which is integrated; its strict form gives the "only if" direction, which the first-order
conditions alone do not deliver.
-/

namespace Gali.BasicNewKeynesianModel.CES

open MeasureTheory

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), p. 53: the aggregate price index `P = (∫ P(i)^{1−ε} di)^{1/(1−ε)}`. -/
noncomputable def priceIndex (μ : Measure G) (ε : ℝ) (P : G → ℝ) : ℝ :=
  (∫ i, P i ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), p. 52–53: the CES consumption index
`C = (∫ C(i)^{(ε−1)/ε} di)^{ε/(ε−1)}`. -/
noncomputable def cesAgg (μ : Measure G) (ε : ℝ) (c : G → ℝ) : ℝ :=
  (∫ i, c i ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), eq. (1), p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C`. -/
noncomputable def demand (μ : Measure G) (ε : ℝ) (P : G → ℝ) (C : ℝ) (i : G) : ℝ :=
  (P i / priceIndex μ ε P) ^ (-ε) * C

/-- Galí (2015), App. 3.1, p. 83: the exponent identity `(ε−1)/ε + 1/ε = 1`. -/
theorem r_add_inv {ε : ℝ} (hε : 1 < ε) : (ε - 1) / ε + 1 / ε = 1 := by
  have : ε ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), App. 3.1, p. 83: the factorisation behind `young_le`,
`c^r = (a c C^{−1/ε})^r (a^{1−ε} C^r)^{1/ε}` with `r = (ε − 1)/ε`. -/
theorem young_key {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    (a * c * C ^ (-1 / ε)) ^ ((ε - 1) / ε) * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ^ (1 / ε)
      = c ^ ((ε - 1) / ε) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hc,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hC.le]
  have e1 : a ^ ((ε - 1) / ε) * c ^ ((ε - 1) / ε) * C ^ (-1 / ε * ((ε - 1) / ε)) *
      (a ^ ((1 - ε) * (1 / ε)) * C ^ ((ε - 1) / ε * (1 / ε)))
      = c ^ ((ε - 1) / ε) * (a ^ ((ε - 1) / ε) * a ^ ((1 - ε) * (1 / ε))) *
        (C ^ (-1 / ε * ((ε - 1) / ε)) * C ^ ((ε - 1) / ε * (1 / ε))) := by ring
  rw [e1, ← Real.rpow_add ha, ← Real.rpow_add hC]
  have z1 : (ε - 1) / ε + (1 - ε) * (1 / ε) = 0 := by field_simp; ring
  have z2 : -1 / ε * ((ε - 1) / ε) + (ε - 1) / ε * (1 / ε) = 0 := by ring
  rw [z1, z2, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]

/-- Galí (2015), App. 3.1, p. 83: the pointwise weighted AM–GM (Young) inequality behind
expenditure minimisation. For a relative price `a > 0`, a quantity `c ≥ 0` and an aggregate
`C > 0`, `c^r ≤ r (a c C^{−1/ε}) + (1/ε) a^{1−ε} C^r` with `r = (ε − 1)/ε`. -/
theorem young_le {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) ≤
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC]
  exact Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by linarith) hε0.le)
    (by positivity) (by positivity) (by positivity) (r_add_inv hε)

/-- Galí (2015), App. 3.1, p. 83: equality in `young_le` holds iff `c = a^{−ε} C`, i.e. iff
the quantity lies on the demand schedule (1). -/
theorem young_eq_iff {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) =
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ↔
      c = a ^ (-ε) * C := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (div_pos (by linarith) hε0) (by positivity) (by positivity) (by positivity) (r_add_inv hε)]
  have hk : a * C ^ (-1 / ε) ≠ 0 := by positivity
  have hv : a ^ (1 - ε) * C ^ ((ε - 1) / ε) = a * C ^ (-1 / ε) * (a ^ (-ε) * C) := by
    have h1 : a ^ (1 - ε) = a * a ^ (-ε) := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
    have h2 : C ^ ((ε - 1) / ε) = C ^ (-1 / ε) * C := by
      have : (ε - 1) / ε = -1 / ε + 1 := by field_simp; ring
      rw [this, Real.rpow_add hC, Real.rpow_one]
    rw [h1, h2]
    ring
  rw [hv, show a * c * C ^ (-1 / ε) = a * C ^ (-1 / ε) * c by ring]
  exact mul_right_inj' hk

variable {μ : Measure G} {ε : ℝ} {P : G → ℝ}

/-- Galí (2015), p. 53: the price index is positive when `∫ P(i)^{1−ε} > 0`. -/
theorem priceIndex_pos (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) : 0 < priceIndex μ ε P :=
  Real.rpow_pos_of_pos hpos _

/-- Galí (2015), p. 53: `P^{1−ε} = ∫ P(i)^{1−ε} di`, the defining property of the index. -/
theorem priceIndex_rpow (hε : 1 < ε) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    priceIndex μ ε P ^ (1 - ε) = ∫ i, P i ^ (1 - ε) ∂μ :=
  Real.rpow_inv_rpow hpos.le (by linarith)

/-- Galí (2015), p. 85 (index condition): `∫ (P(i)/P)^{1−ε} di = 1`. -/
theorem integral_relPrice_rpow (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    ∫ i, (P i / priceIndex μ ε P) ^ (1 - ε) ∂μ = 1 := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  rw [integral_div, priceIndex_rpow hε hpos, div_self hpos.ne']

/-- Galí (2015), p. 85: the relative-price integrand `(P(i)/P)^{1−ε}` is integrable. -/
theorem integrable_relPrice_rpow (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    Integrable (fun i => (P i / priceIndex μ ε P) ^ (1 - ε)) μ := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  exact hPi.div_const _

/-- Galí (2015), eq. (1) and p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C` delivers
exactly the aggregate `C`. -/
theorem cesAgg_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {C : ℝ} (hC : 0 ≤ C) : cesAgg μ ε (demand μ ε P C) = C := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  have hpt : ∀ i, demand μ ε P C i ^ ((ε - 1) / ε)
      = C ^ ((ε - 1) / ε) * (P i / priceIndex μ ε P) ^ (1 - ε) := by
    intro i
    have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
    rw [demand, Real.mul_rpow (by positivity) hC, ← Real.rpow_mul ha.le]
    have : -ε * ((ε - 1) / ε) = 1 - ε := by field_simp; ring
    rw [this, mul_comm]
  unfold cesAgg
  simp_rw [hpt]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one, Real.rpow_rpow_inv hC hr]

/-- Galí (2015), p. 53: `P(i) (P(i)/P)^{−ε} C = P C (P(i)/P)^{1−ε}` pointwise. -/
theorem price_mul_demand (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) (C : ℝ)
    (i : G) : P i * demand μ ε P C i
      = priceIndex μ ε P * C * (P i / priceIndex μ ε P) ^ (1 - ε) := by
  have hI := priceIndex_pos hpos
  have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
  have h1 : (P i / priceIndex μ ε P) ^ (1 - ε)
      = P i / priceIndex μ ε P * (P i / priceIndex μ ε P) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  rw [demand, h1]
  field_simp

/-- Galí (2015), p. 53: under the demand schedule, total expenditure is
`∫ P(i) C(i) di = P C`. -/
theorem spend_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    (C : ℝ) : ∫ i, P i * demand μ ε P C i ∂μ = priceIndex μ ε P * C := by
  simp_rw [price_mul_demand hP hpos C]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), App. 3.1, p. 83: the CES aggregate is nonnegative. -/
theorem cesAgg_nonneg {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ cesAgg μ ε c :=
  Real.rpow_nonneg (integral_nonneg fun i => Real.rpow_nonneg (hc i) _) _

/-- Galí (2015), App. 3.1, p. 83: `C^r = ∫ C(i)^r` for the CES aggregate `C`. -/
theorem cesAgg_rpow (hε : 1 < ε) {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) :
    cesAgg μ ε c ^ ((ε - 1) / ε) = ∫ i, c i ^ ((ε - 1) / ε) ∂μ :=
  Real.rpow_inv_rpow (integral_nonneg fun i => Real.rpow_nonneg (hc i) _)
    (div_ne_zero (by linarith) (by linarith))

/-- Galí (2015), App. 3.1, p. 83: the integrated Young bound. For a bundle with positive
aggregate `C`, `C^r ≤ r C^{−1/ε} (∫ P c)/P + (1/ε) C^r`. -/
theorem integrated_young (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ)
    (hC : 0 < cesAgg μ ε c) :
    Integrable (fun i => (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) μ ∧
      (∀ i, c i ^ ((ε - 1) / ε) ≤ (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∧
      ∫ i, ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∂μ
        = (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
          (∫ i, P i * c i ∂μ) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) := by
  have hI := priceIndex_pos hpos
  have hint1 := hpc.const_mul ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P))
  have hint2 := (integrable_relPrice_rpow hPi hP hpos).const_mul
    (1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε))
  refine ⟨hint1.add hint2, fun i => ?_, ?_⟩
  · have h := young_le hε (div_pos (hP i) hI) (hc i) hC
    have e : (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) * (P i * c i)
        = (ε - 1) / ε * (P i / priceIndex μ ε P * c i * cesAgg μ ε c ^ (-1 / ε)) := by ring
    rw [e]
    linarith
  · rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), p. 53 and App. 3.1, p. 83 (**expenditure minimisation**): any bundle
`C(·) ≥ 0` costs at least `P · C`, where `C` is its CES aggregate. -/
theorem spend_ge (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    priceIndex μ ε P * cesAgg μ ε c ≤ ∫ i, P i * c i ∂μ := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hS : 0 ≤ ∫ i, P i * c i ∂μ := integral_nonneg fun i => mul_nonneg (hP i).le (hc i)
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero]; exact hS
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun i => Real.rpow_nonneg (hc i) ((ε - 1) / ε)) hint
    (Filter.Eventually.of_forall hle)
  rw [hval, ← cesAgg_rpow hε hc] at hmono
  set C := cesAgg μ ε c
  set S := ∫ i, P i * c i ∂μ
  have hK : 0 < C ^ (-1 / ε) := Real.rpow_pos_of_pos hC _
  have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
    have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
    rw [this, Real.rpow_add hC, Real.rpow_one]
  rw [hCr] at hmono
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) hε0
  have h1 : (ε - 1) / ε * (C * C ^ (-1 / ε)) ≤
      (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by
    have e : 1 / ε = 1 - (ε - 1) / ε := by field_simp; ring
    rw [e] at hmono
    have e2 : (ε - 1) / ε * (C ^ (-1 / ε) / priceIndex μ ε P) * S
        = (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by ring
    rw [e2] at hmono
    linarith
  have h2 := le_of_mul_le_mul_left h1 hr
  rw [mul_comm C] at h2
  have h3 := le_of_mul_le_mul_left h2 hK
  rw [le_div_iff₀ hI] at h3
  linarith

/-- Galí (2015), eq. (1), p. 53 and App. 3.1, p. 83: a bundle costs exactly `P · C` (its
aggregate `C`) **if and only if** it is the demand schedule `C(i) = (P(i)/P)^{−ε} C`
almost everywhere. -/
theorem spend_eq_iff (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    ∫ i, P i * c i ∂μ = priceIndex μ ε P * cesAgg μ ε c ↔
      c =ᵐ[μ] demand μ ε P (cesAgg μ ε c) := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  constructor
  swap
  · intro h
    rw [← spend_demand hε hP hpos (cesAgg μ ε c)]
    refine integral_congr_ae ?_
    filter_upwards [h] with i hi
    rw [hi]
  intro heq
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero] at heq
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun i => mul_nonneg (hP i).le (hc i)) hpc).1 heq
    filter_upwards [hz] with i hi
    rw [← h0, demand, mul_zero]
    simp only [Pi.zero_apply] at hi
    rcases mul_eq_zero.1 hi with h | h
    · exact absurd h (hP i).ne'
    · exact h
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  set C := cesAgg μ ε c
  have hcr : Integrable (fun i => c i ^ ((ε - 1) / ε)) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← cesAgg_rpow hε hc]
    exact (Real.rpow_pos_of_pos hC _).ne'
  have hdiff := (integral_eq_zero_iff_of_nonneg
    (fun i => sub_nonneg.2 (hle i)) (hint.sub hcr)).1 (by
      rw [integral_sub hint hcr, hval, ← cesAgg_rpow hε hc, heq]
      have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
        have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
        rw [this, Real.rpow_add hC, Real.rpow_one]
      rw [hCr]
      field_simp
      ring)
  filter_upwards [hdiff] with i hi
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  have := (young_eq_iff hε (div_pos (hP i) hI) (hc i) hC).1 (by
    rw [← hi]
    ring)
  rw [this, demand]

/-- Galí (2015), App. 3.1, p. 83 (dual form): for a bundle with expenditure
`∫ P(i) C(i) = X`, the attainable consumption index is at most `X / P`. -/
theorem cesAgg_le_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) : cesAgg μ ε c ≤ X / priceIndex μ ε P := by
  rw [le_div_iff₀ (priceIndex_pos hpos), mul_comm, ← hX]
  exact spend_ge hε hP hPi hpos hc hpc

/-- Galí (2015), App. 3.1, p. 83 (dual form, equality): with expenditure `X`, the index
attains `X / P` iff `C(i) = (P(i)/P)^{−ε} X/P` almost everywhere. -/
theorem cesAgg_eq_iff_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) :
    cesAgg μ ε c = X / priceIndex μ ε P ↔
      c =ᵐ[μ] demand μ ε P (X / priceIndex μ ε P) := by
  have hI := priceIndex_pos hpos
  constructor
  · intro h
    rw [← h]
    refine (spend_eq_iff hε hP hPi hpos hc hpc).1 ?_
    rw [h, hX]
    field_simp
  · intro h
    have hX0 : 0 ≤ X / priceIndex μ ε P := by
      rw [← hX]
      exact div_nonneg (integral_nonneg fun i => mul_nonneg (hP i).le (hc i)) hI.le
    have hagg : cesAgg μ ε c = cesAgg μ ε (demand μ ε P (X / priceIndex μ ε P)) := by
      unfold cesAgg
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h] with i hi
      rw [hi]
    rw [hagg, cesAgg_demand hε hP hpos hX0]

/-- Galí (2015), eq. (12), p. 58: goods-market clearing `Y(i) = C(i)` for all `i`, with
households on their demand schedule, gives `Y = C` for the CES output index and
`Y(i) = (P(i)/P)^{−ε} Y`. -/
theorem market_clearing (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {C : ℝ} (hC : 0 ≤ C) {Y : G → ℝ}
    (hclear : ∀ i, Y i = demand μ ε P C i) :
    cesAgg μ ε Y = C ∧ ∀ i, Y i = demand μ ε P (cesAgg μ ε Y) i := by
  have hY : Y = demand μ ε P C := funext hclear
  have hagg : cesAgg μ ε Y = C := by rw [hY, cesAgg_demand hε hP hpos hC]
  exact ⟨hagg, fun i => by rw [hagg, hclear]⟩

/-- Galí (2015), p. 53: a positive integrable function has positive integral against a
nonzero measure (used to see that `∫ P(i)^{1−ε} > 0`). -/
theorem integral_pos_of_pos {f : G → ℝ} (hμ : μ ≠ 0) (hf : ∀ i, 0 < f i)
    (hfi : Integrable f μ) : 0 < ∫ i, f i ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun i => (hf i).le) hfi]
  have : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun i => (hf i).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 hμ

/-- Galí (2015), p. 53: Lebesgue measure on the goods continuum `[0, 1]` is nonzero. -/
theorem unitInterval_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  simp

/-- Galí (2015), §3.1, p. 53 and App. 3.1, p. 83, on the book's **continuum of goods
`[0, 1]` with Lebesgue measure**: (i) every bundle `C(·) ≥ 0` costs at least `P · C`;
(ii) it costs exactly `P · C` iff `C(i) = (P(i)/P)^{−ε} C` for a.e. `i ∈ [0, 1]`;
(iii) the demand schedule attains any aggregate `C ≥ 0`; (iv) it costs `P C`. -/
theorem unitInterval_expenditure_minimisation (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQi : IntegrableOn (fun i => Q i ^ (1 - ε)) (Set.Icc 0 1)) {c : ℝ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hQc : IntegrableOn (fun i => Q i * c i) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * cesAgg (volume.restrict (Set.Icc 0 1)) ε c
        ≤ ∫ i in Set.Icc 0 1, Q i * c i ∧
      (∫ i in Set.Icc 0 1, Q i * c i
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε c ↔
        ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          c i = demand (volume.restrict (Set.Icc 0 1)) ε Q
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε c) i) ∧
      (∀ C : ℝ, 0 ≤ C → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Q C) = C) ∧
      ∀ C : ℝ, ∫ i in Set.Icc 0 1, Q i * demand (volume.restrict (Set.Icc 0 1)) ε Q C i
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * C := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun i => Real.rpow_pos_of_pos (hQ i) _)
    hQi
  exact ⟨spend_ge hε hQ hQi hpos hc hQc, spend_eq_iff hε hQ hQi hpos hc hQc,
    fun C hC => cesAgg_demand hε hQ hpos hC, spend_demand hε hQ hpos⟩

namespace Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Galí (2015), p. 53 (finitely many goods): the measure placing weight `w i` on good `i`,
a discretisation of `[0, 1]` (e.g. `w i = 1/n`). -/
noncomputable def weightMeasure (w : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- Galí (2015), p. 53: the weighted measure gives good `x` mass `w x`. -/
theorem weightMeasure_singleton {w : ι → ℝ} (x : ι) :
    weightMeasure w {x} = ENNReal.ofReal (w x) := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [Measure.dirac_apply' _ (measurableSet_singleton x), hb]
  · simp

omit [MeasurableSingletonClass ι] in
/-- Galí (2015), p. 53: the weighted measure is finite. -/
theorem weightMeasure_univ_lt_top {w : ι → ℝ} : weightMeasure w Set.univ < ⊤ := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

/-- Galí (2015), p. 53: every function is integrable for the weighted measure. -/
theorem integrable_weightMeasure {w : ι → ℝ} (f : ι → ℝ) : Integrable f (weightMeasure w) := by
  have : IsFiniteMeasure (weightMeasure w) := ⟨weightMeasure_univ_lt_top⟩
  exact Integrable.of_finite

/-- Galí (2015), p. 53: integrals against the weighted measure are weighted sums,
`∫ f = ∑ᵢ w i f i`. -/
theorem integral_weightMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) :
    ∫ i, f i ∂(weightMeasure w) = ∑ i, w i * f i := by
  rw [integral_fintype (integrable_weightMeasure f)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.real, weightMeasure_singleton, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- Galí (2015), §3.1, p. 53 and App. 3.1, p. 83, for **finitely many goods** with weights
`w i > 0`. With `P = (∑ w P(i)^{1−ε})^{1/(1−ε)}` and `C = (∑ w C(i)^r)^{1/r}`:
(i) `∑ w P(i) C(i) ≥ P C`; (ii) equality iff `C(i) = (P(i)/P)^{−ε} C` for **every** `i`;
(iii) the demand schedule attains any `C ≥ 0`; (iv) it costs exactly `P C`. -/
theorem finite_expenditure_minimisation [Nonempty ι] (hε : 1 < ε) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {Q : ι → ℝ} (hQ : ∀ i, 0 < Q i) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ * (∑ i, w i * c i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹
        ≤ ∑ i, w i * (Q i * c i) ∧
      (∑ i, w i * (Q i * c i) = (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ *
          (∑ i, w i * c i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ ↔
        ∀ i, c i = (Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) *
          (∑ j, w j * c j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹) ∧
      (∀ C : ℝ, 0 ≤ C → (∑ i, w i *
        ((Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * C) ^ ((ε - 1) / ε)) ^
          ((ε - 1) / ε)⁻¹ = C) ∧
      ∀ C : ℝ, ∑ i, w i * (Q i * ((Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * C))
        = (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ * C := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hμ : weightMeasure w ≠ 0 := by
    intro h
    obtain ⟨x⟩ := ‹Nonempty ι›
    have := weightMeasure_singleton (w := w) x
    rw [h, Measure.coe_zero, Pi.zero_apply] at this
    exact (ENNReal.ofReal_pos.2 (hw x)).ne' this.symm
  have hpos := integral_pos_of_pos hμ (fun i => Real.rpow_pos_of_pos (hQ i) (1 - ε))
    (integrable_weightMeasure _)
  have hPI : priceIndex (weightMeasure w) ε Q = (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ := by
    rw [priceIndex, integral_weightMeasure hw0]
  have hCA : ∀ d : ι → ℝ, cesAgg (weightMeasure w) ε d
      = (∑ j, w j * d j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ := by
    intro d
    rw [cesAgg, integral_weightMeasure hw0]
  have hD : ∀ C i, demand (weightMeasure w) ε Q C i
      = (Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * C := by
    intro C i
    rw [demand, hPI]
  have h1 := spend_ge hε hQ (integrable_weightMeasure _) hpos hc (integrable_weightMeasure _)
  have h2 := spend_eq_iff hε hQ (integrable_weightMeasure _) hpos hc (integrable_weightMeasure _)
  rw [hPI, hCA, integral_weightMeasure hw0] at h1 h2
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h2
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h2]
    constructor
    · intro h i
      rw [← hD]
      exact h i (by rw [weightMeasure_singleton]; exact (ENNReal.ofReal_pos.2 (hw i)).ne')
    · intro h i _
      rw [hD]
      exact h i
  · intro C hC
    have := cesAgg_demand hε hQ hpos hC (μ := weightMeasure w)
    rw [hCA] at this
    simpa only [hD] using this
  · intro C
    have := spend_demand hε hQ hpos C (μ := weightMeasure w)
    rw [integral_weightMeasure hw0, hPI] at this
    simpa only [hD] using this

end Finite

end Gali.BasicNewKeynesianModel.CES

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Calvo aggregate price dynamics

Galí (2015), Chapter 3, §3.2.1 (p. 55), eqs. (7)–(8), and Appendix 3.2 (p. 84), eq. (36);
the probability identity of Appendix 3.3 (pp. 84–85).

## The model of the cross-section

Firms form a measure space `(F, m)` (the book's `[0, 1]`). In period `t` firms in a measurable
set `S` reset their price to the common value `P*_t`; the others keep last period's price.
Appendix 3.2 asserts that "the distribution of prices among firms not adjusting in period `t`
corresponds to the distribution of effective prices in period `t − 1`, though with total mass
reduced to `θ`". We take exactly this as the hypothesis (the non-resetters are a
representative subsample):

  `(m.restrict Sᶜ).map p_{t−1} = θ • m.map p_{t−1}`,  `m S = 1 − θ`.

`dist_law_of_motion` then derives the law of motion of the price distribution
`ν_t = θ ν_{t−1} + (1 − θ) δ_{P*_t}`, and `calvo_recursion` derives (7)/(36),
`Π_t^{1−ε} = θ + (1 − θ)(P*_t / P_{t−1})^{1−ε}`. The hypothesis is not vacuous:
`lottery_model` shows that it holds for *every* initial price distribution when the Calvo
lottery is a uniform draw `u ∈ [0, 1]` independent of the firm's price (firms
`Ω × [0, 1]` with the product measure, resetting iff `u > θ`), and `calvo_recursion_lottery`
states (7) for that explicit model. This is the cleanest rigorous reading of "a fraction
`1 − θ` resets, independently of the time elapsed and of the current price": a law of large
numbers is not needed because the continuum of firms carries the product measure.

## Main results

* `dist_law_of_motion`, `integral_calvo_mix`, `calvo_recursion_of_dist`, `calvo_recursion`,
  `lottery_model`, `calvo_recursion_lottery`: eq. (7)/(36).
* `dist_k_step`, `prob_identity`, `dist_k_step_mass`: App. 3.3's decomposition of the
  period-`t + k` distribution by date of last reset, and `θᵏ + (1−θ) ∑_{h=1}^k θ^{k−h} = 1`.
* `zero_inflation_iff`, `zero_inflation_levels`: `Π = 1 ⟺ P* = P_{t−1}` (p. 55).
* `log_infl_eq_inflFn`, `inflFn_zero`, `hasDerivAt_inflFn`, `inflFn_isLittleO`: eq. (8) as
  the exact derivative of `log Π_t` in `log(P*_t/P_{t−1})` at `0`, equal to `1 − θ`.
-/

namespace Gali.BasicNewKeynesianModel.CalvoIndex

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-- Galí (2015), App. 3.2, p. 84: integrating against the Calvo mixture
`θ ν + (1 − θ) δ_{P*}` gives `θ ∫ f dν + (1 − θ) f(P*)`. -/
theorem integral_calvo_mix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (Pstar : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar)
      = θ * ∫ x, f x ∂ν + (1 - θ) * f Pstar := by
  have hd : Integrable f (Measure.dirac Pstar) := integrable_dirac (by simp)
  rw [integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), eq. (36), p. 84, at the level of price distributions: if
`ν_t = θ ν_{t−1} + (1 − θ) δ_{P*}`, where `ν_{t−1}` has a positive, integrable
`∫ p^{1−ε}`, then with `P_s = (∫ p^{1−ε} dν_s)^{1/(1−ε)}`,
`(P_t/P_{t−1})^{1−ε} = θ + (1 − θ)(P*/P_{t−1})^{1−ε}`. -/
theorem calvo_recursion_of_dist {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1)
    {νprev : Measure ℝ} {Pstar : ℝ} (hPstar : 0 < Pstar)
    (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) νprev)
    (hpos : 0 < ∫ x, x ^ (1 - ε) ∂νprev) :
    (priceIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε
        (fun x => x) / priceIndex νprev ε (fun x => x)) ^ (1 - ε)
      = θ + (1 - θ) * (Pstar / priceIndex νprev ε (fun x => x)) ^ (1 - ε) := by
  have hmix := integral_calvo_mix h0 h1.le Pstar hint
  have hnew : 0 < θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Pstar ^ (1 - ε) := by
    have : 0 < (1 - θ) * Pstar ^ (1 - ε) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hPstar _)
    have : 0 ≤ θ * ∫ x, x ^ (1 - ε) ∂νprev := mul_nonneg h0 hpos.le
    linarith
  have hI := priceIndex_pos (P := fun x : ℝ => x) hpos
  have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
  have hPt : priceIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar)
      ε (fun x => x) ^ (1 - ε) = θ * ∫ x, x ^ (1 - ε) ∂νprev + (1 - θ) * Pstar ^ (1 - ε) := by
    unfold priceIndex
    rw [hmix, Real.rpow_inv_rpow hnew.le hsub]
  have hPt0 : 0 ≤ priceIndex (ENNReal.ofReal θ • νprev + ENNReal.ofReal (1 - θ) •
      Measure.dirac Pstar) ε (fun x => x) := by
    unfold priceIndex
    rw [hmix]
    exact Real.rpow_nonneg hnew.le _
  rw [Real.div_rpow hPt0 hI.le, Real.div_rpow hPstar.le hI.le, hPt,
    priceIndex_rpow (P := fun x : ℝ => x) hε hpos]
  field_simp

/-- Galí (2015), App. 3.2, p. 84 (**law of motion of the price distribution**). Firms
`(F, m)`; those in `S` (mass `1 − θ`) reset to `P*`, the rest keep `p_{t−1}`, and the
non-resetters are a representative subsample (their price distribution is `θ` times that of
all firms). Then `ν_t = θ ν_{t−1} + (1 − θ) δ_{P*}` where `ν_s = m.map p_s`. -/
theorem dist_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ : ℝ}
    {S : Set F} (hS : MeasurableSet S) {pprev pnow : F → ℝ} (hnow : Measurable pnow)
    {Pstar : ℝ} (hreset : ∀ i ∈ S, pnow i = Pstar) (hkeep : ∀ i ∉ S, pnow i = pprev i)
    (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev) :
    m.map pnow = ENNReal.ofReal θ • m.map pprev + ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := m) hS]
  rw [Measure.map_add _ _ hnow]
  have h1 : (m.restrict S).map pnow = ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
    rw [Measure.map_congr (g := fun _ => Pstar) ((ae_restrict_iff' hS).2
      (Filter.Eventually.of_forall hreset)), Measure.map_const, Measure.restrict_apply_univ,
      hmass]
  have h2 : (m.restrict Sᶜ).map pnow = (m.restrict Sᶜ).map pprev :=
    Measure.map_congr ((ae_restrict_iff' hS.compl).2 (Filter.Eventually.of_forall hkeep))
  rw [h1, h2, hind, add_comm]

/-- Galí (2015), eq. (7), p. 55 and eq. (36), p. 84 (**Calvo price-index recursion**),
derived from the firm-level model of `dist_law_of_motion`: with `P_s` the CES price index of
the cross-section `p_s`, `(P_t/P_{t−1})^{1−ε} = θ + (1 − θ)(P*_t/P_{t−1})^{1−ε}`. -/
theorem calvo_recursion {F : Type*} [MeasurableSpace F] (m : Measure F) {ε θ : ℝ}
    (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {S : Set F} (hS : MeasurableSet S)
    {pprev pnow : F → ℝ} (hprev : Measurable pprev) (hnow : Measurable pnow) {Pstar : ℝ}
    (hPstar : 0 < Pstar) (hreset : ∀ i ∈ S, pnow i = Pstar)
    (hkeep : ∀ i ∉ S, pnow i = pprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev)
    (hint : Integrable (fun i => pprev i ^ (1 - ε)) m)
    (hpos : 0 < ∫ i, pprev i ^ (1 - ε) ∂m) :
    (priceIndex m ε pnow / priceIndex m ε pprev) ^ (1 - ε)
      = θ + (1 - θ) * (Pstar / priceIndex m ε pprev) ^ (1 - ε) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hmap : ∀ p : F → ℝ, Measurable p →
      ∫ i, p i ^ (1 - ε) ∂m = ∫ x, x ^ (1 - ε) ∂(m.map p) := fun p hp =>
    (integral_map hp.aemeasurable hmeas.aestronglyMeasurable).symm
  have hidx : ∀ p : F → ℝ, Measurable p →
      priceIndex m ε p = priceIndex (m.map p) ε (fun x => x) := fun p hp => by
    unfold priceIndex
    rw [hmap p hp]
  have hint' : Integrable (fun x : ℝ => x ^ (1 - ε)) (m.map pprev) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hprev.aemeasurable).2 hint
  rw [hidx pnow hnow, hidx pprev hprev, dist_law_of_motion m hS hnow hreset hkeep hmass hind]
  rw [hmap pprev hprev] at hpos
  exact calvo_recursion_of_dist hε h0 h1 hPstar hint' hpos

/-- Galí (2015), §3.2, p. 55 (**the Calvo lottery is a representative subsample**): for any
probability space of firms `(Ω, μ₀)` with prices `p`, give each firm an independent uniform
draw `u ∈ [0, 1]` and let it reset iff `u > θ`. On `Ω × [0, 1]` with the product measure the
resetters have mass `1 − θ`, the non-resetters' price distribution is `θ` times the full one,
and the full distribution is that of `p` under `μ₀`. -/
theorem lottery_model {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {p : Ω → ℝ} (hp : Measurable p) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.univ ×ˢ Set.Ioi θ)
        = ENNReal.ofReal (1 - θ) ∧
      ((μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).restrict (Set.univ ×ˢ Set.Ioi θ)ᶜ).map
          (fun x => p x.1)
        = ENNReal.ofReal θ •
          (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1) ∧
      (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1) = μ₀.map p := by
  have hfst : ∀ ν : Measure ℝ, SFinite ν →
      (μ₀.prod ν).map (fun x => p x.1) = ν Set.univ • μ₀.map p := by
    intro ν _
    have : (fun x : Ω × ℝ => p x.1) = p ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map hp measurable_fst, Measure.map_fst_prod, Measure.map_smul]
    exact hp.aemeasurable
  have hall : (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).map (fun x => p x.1)
      = μ₀.map p := by
    rw [hfst _ inferInstance, Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  refine ⟨?_, ?_, hall⟩
  · rw [Measure.prod_prod, measure_univ, one_mul,
      Measure.restrict_apply measurableSet_Ioi]
    have : Set.Ioi θ ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc θ 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨h, by linarith, h'⟩
    rw [this, Real.volume_Ioc]
  · have hc : (Set.univ ×ˢ Set.Ioi θ : Set (Ω × ℝ))ᶜ = Set.univ ×ˢ Set.Iic θ := by
      ext x
      simp
    rw [hc, ← Measure.prod_restrict, Measure.restrict_univ, hfst _ inferInstance, hall,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iic]
    have : Set.Iic θ ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 θ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h, h', -⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨h', h, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]

/-- Galí (2015), eq. (7), p. 55 and eq. (36), p. 84, for the **explicit Calvo-lottery
economy** of `lottery_model`: firms `(ω, u) ∈ Ω × [0, 1]`, last period's price `p ω`, and
this period's price `P*` if `u > θ` and `p ω` otherwise. With `P_{t−1}` the index of `p`
under `μ₀`, `(P_t/P_{t−1})^{1−ε} = θ + (1 − θ)(P*/P_{t−1})^{1−ε}`. -/
theorem calvo_recursion_lottery {Ω : Type*} [MeasurableSpace Ω] (μ₀ : Measure Ω)
    [IsProbabilityMeasure μ₀] {ε θ : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 < p ω) (hint : Integrable (fun ω => p ω ^ (1 - ε)) μ₀)
    {Pstar : ℝ} (hPstar : 0 < Pstar) :
    (priceIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε
        (fun x => if θ < x.2 then Pstar else p x.1) / priceIndex μ₀ ε p) ^ (1 - ε)
      = θ + (1 - θ) * (Pstar / priceIndex μ₀ ε p) ^ (1 - ε) := by
  obtain ⟨hmass, hind, hall⟩ := lottery_model μ₀ hp h0 h1.le
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hpp : Measurable fun x : Ω × ℝ => p x.1 := hp.comp measurable_fst
  have hI : ∫ x, p x.1 ^ (1 - ε) ∂(μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ ω, p ω ^ (1 - ε) ∂μ₀ := by
    rw [← integral_map hpp.aemeasurable hmeas.aestronglyMeasurable, hall,
      integral_map hp.aemeasurable hmeas.aestronglyMeasurable]
  have hidx : priceIndex (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ε (fun x => p x.1)
      = priceIndex μ₀ ε p := by
    unfold priceIndex
    rw [hI]
  have hint' : Integrable (fun x => p x.1 ^ (1 - ε))
      (μ₀.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hp.aemeasurable).2 hint
    rw [← hall] at this
    exact (integrable_map_measure hmeas.aestronglyMeasurable hpp.aemeasurable).1 this
  have hpos : 0 < ∫ ω, p ω ^ (1 - ε) ∂μ₀ :=
    integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ₀)
      (fun ω => Real.rpow_pos_of_pos (hp0 ω) _) hint
  have hS : MeasurableSet (Set.univ ×ˢ Set.Ioi θ : Set (Ω × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hnow : Measurable fun x : Ω × ℝ => if θ < x.2 then Pstar else p x.1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const hpp
  rw [← hidx]
  refine calvo_recursion _ hε h0 h1 hS hpp hnow hPstar ?_ ?_ hmass hind hint'
    (by rw [hI]; exact hpos)
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]
  · intro x hx
    simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hx
    simp only [hx, ↓reduceIte]

/-- Galí (2015), App. 3.3, p. 84 (**decomposition by date of last reset**): if the price
distribution follows `ν_{s+1} = θ ν_s + (1 − θ) δ_{P*_{s+1}}`, then
`ν_{t+k} = θᵏ ν_t + ∑_{h=1}^{k} (1 − θ) θ^{k−h} δ_{P*_{t+h}}` (written with `h ↦ h + 1`): a
mass `θᵏ` still charges the prices of date `t`, and a mass `(1 − θ)θ^{k−h}` last reset at
`t + h`. -/
theorem dist_k_step {θ : ℝ} (h0 : 0 ≤ θ) {ν : ℕ → Measure ℝ} {Pstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Pstar (t + 1)))
    (t k : ℕ) :
    ν (t + k) = ENNReal.ofReal (θ ^ k) • ν t + ∑ h ∈ Finset.range k,
      ENNReal.ofReal ((1 - θ) * θ ^ (k - 1 - h)) • Measure.dirac (Pstar (t + h + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, hlaw, ih, smul_add, Finset.smul_sum, smul_smul, Finset.sum_range_succ]
    simp_rw [smul_smul]
    have hc : ∀ h ∈ Finset.range k, ENNReal.ofReal θ * ENNReal.ofReal ((1 - θ) * θ ^ (k - 1 - h))
        = ENNReal.ofReal ((1 - θ) * θ ^ (k + 1 - 1 - h)) := by
      intro h hh
      rw [Finset.mem_range] at hh
      rw [← ENNReal.ofReal_mul h0]
      congr 1
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl fun h hh => by rw [hc h hh], ← ENNReal.ofReal_mul h0, ← pow_succ',
      show k + 1 - 1 - k = 0 by omega, pow_zero, mul_one, add_assoc]

/-- Galí (2015), App. 3.3, p. 84: the probabilities in (37) sum to one,
`θᵏ + (1 − θ) ∑_{h=1}^{k} θ^{k−h} = 1`. -/
theorem prob_identity (θ : ℝ) (k : ℕ) :
    θ ^ k + (1 - θ) * ∑ h ∈ Finset.Icc 1 k, θ ^ (k - h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero]
    have hs : ∑ h ∈ Finset.Icc 1 k, θ ^ (k + 1 - h) = θ * ∑ h ∈ Finset.Icc 1 k, θ ^ (k - h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_Icc] at hh
      rw [show k + 1 - h = (k - h) + 1 by omega, pow_succ]
      ring
    rw [hs]
    linear_combination θ * ih

/-- Galí (2015), App. 3.3, p. 84: the identity of `prob_identity` in the indexing of
`dist_k_step`, `θᵏ + ∑_{h<k} (1 − θ) θ^{k−1−h} = 1`. -/
theorem prob_identity_range (θ : ℝ) (k : ℕ) :
    θ ^ k + ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k - 1 - h) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show k + 1 - 1 - k = 0 by omega, pow_zero]
    have hs : ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k + 1 - 1 - h)
        = θ * ∑ h ∈ Finset.range k, (1 - θ) * θ ^ (k - 1 - h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_range] at hh
      rw [show k + 1 - 1 - h = (k - 1 - h) + 1 by omega, pow_succ]
      ring
    rw [hs]
    linear_combination θ * ih

/-- Galí (2015), App. 3.3, p. 84: if `ν_t` is a probability distribution, so is `ν_{t+k}`;
the masses of `dist_k_step` add up to one. -/
theorem dist_k_step_mass {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ}
    {Pstar : ℕ → ℝ}
    (hlaw : ∀ t, ν (t + 1)
      = ENNReal.ofReal θ • ν t + ENNReal.ofReal (1 - θ) • Measure.dirac (Pstar (t + 1)))
    (t k : ℕ) (hν : ν t Set.univ = 1) : ν (t + k) Set.univ = 1 := by
  have hnn : ∀ h ∈ Finset.range k, 0 ≤ (1 - θ) * θ ^ (k - 1 - h) :=
    fun h _ => mul_nonneg (by linarith) (pow_nonneg h0 _)
  rw [dist_k_step h0 hlaw t k]
  simp only [Measure.coe_add, Measure.coe_smul, Measure.coe_finsetSum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, measure_univ, hν, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← ENNReal.ofReal_add (pow_nonneg h0 _)
    (Finset.sum_nonneg hnn), prob_identity_range, ENNReal.ofReal_one]

/-- Galí (2015), p. 55: a positive number `y` satisfies `y^{1−ε} = 1` iff `y = 1` (`ε ≠ 1`). -/
theorem rpow_eq_one_iff {ε y : ℝ} (hε : ε ≠ 1) (hy : 0 < y) : y ^ (1 - ε) = 1 ↔ y = 1 := by
  constructor
  · intro h
    have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
    rw [← Real.rpow_rpow_inv hy.le hsub, h, Real.one_rpow]
  · rintro rfl
    exact Real.one_rpow _

/-- Galí (2015), p. 55 (**zero-inflation steady state**): under (7), gross inflation is one
iff the reset price equals last period's price index, `Π = 1 ⟺ P*/P_{t−1} = 1`
(`0 ≤ θ < 1`, `ε ≠ 1`). -/
theorem zero_inflation_iff {θ ε Pi x : ℝ} (h1 : θ < 1) (hε : ε ≠ 1) (hPi : 0 < Pi)
    (hx : 0 < x) (hrec : Pi ^ (1 - ε) = θ + (1 - θ) * x ^ (1 - ε)) : Pi = 1 ↔ x = 1 := by
  rw [← rpow_eq_one_iff hε hPi, ← rpow_eq_one_iff hε hx, hrec]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  constructor
  · intro h
    have h' : (1 - θ) * x ^ (1 - ε) = (1 - θ) * 1 := by linarith
    exact mul_left_cancel₀ this h'
  · intro h
    rw [h]
    ring

/-- Galí (2015), p. 55, in levels: under (7), `P_t = P_{t−1}` iff `P*_t = P_{t−1}`, and then
`P*_t = P_{t−1} = P_t`. -/
theorem zero_inflation_levels {θ ε Pt Pprev Pstar : ℝ} (h1 : θ < 1) (hε : ε ≠ 1)
    (hPt : 0 < Pt) (hPprev : 0 < Pprev) (hPstar : 0 < Pstar)
    (hrec : (Pt / Pprev) ^ (1 - ε) = θ + (1 - θ) * (Pstar / Pprev) ^ (1 - ε)) :
    (Pt = Pprev ↔ Pstar = Pprev) ∧ (Pt = Pprev → Pstar = Pprev ∧ Pstar = Pt) := by
  have h := zero_inflation_iff h1 hε (div_pos hPt hPprev) (div_pos hPstar hPprev) hrec
  rw [div_eq_one_iff_eq hPprev.ne', div_eq_one_iff_eq hPprev.ne'] at h
  exact ⟨h, fun he => ⟨h.1 he, (h.1 he).trans he.symm⟩⟩

/-- Galí (2015), eq. (8), p. 55: log gross inflation as a function of the log relative reset
price `y = log(P*_t/P_{t−1})`, as implied by (7):
`π(y) = (1 − ε)⁻¹ log(θ + (1 − θ) e^{(1−ε) y})`. -/
noncomputable def inflFn (θ ε y : ℝ) : ℝ :=
  (1 - ε)⁻¹ * Real.log (θ + (1 - θ) * Real.exp ((1 - ε) * y))

/-- Galí (2015), eq. (8), p. 55: the exact (nonlinear) relation (7) says
`log Π_t = inflFn θ ε (log(P*_t/P_{t−1}))`. -/
theorem log_infl_eq_inflFn {θ ε Pi x : ℝ} (hε : ε ≠ 1) (hPi : 0 < Pi) (hx : 0 < x)
    (hrec : Pi ^ (1 - ε) = θ + (1 - θ) * x ^ (1 - ε)) :
    Real.log Pi = inflFn θ ε (Real.log x) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hPi, Real.rpow_def_of_pos hx, mul_comm (Real.log x)] at h
  rw [inflFn, ← h]
  field_simp

/-- Galí (2015), p. 55: at the zero-inflation steady state (`P* = P_{t−1}`, i.e. `y = 0`),
`π = 0`. -/
theorem inflFn_zero (θ ε : ℝ) : inflFn θ ε 0 = 0 := by
  simp [inflFn]

/-- Galí (2015), eq. (8), p. 55 (**exact derivative**): `d log Π_t / d log(P*_t/P_{t−1}) = 1 − θ`
at the zero-inflation steady state; i.e. `π_t = (1 − θ)(p*_t − p_{t−1})` is the first-order
approximation of (7). -/
theorem hasDerivAt_inflFn (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) : HasDerivAt (inflFn θ ε) (1 - θ) 0 := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have h1 : HasDerivAt (fun y : ℝ => (1 - ε) * y) (1 - ε) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - ε)
  have h2 := HasDerivAt.exp h1
  have h3 := HasDerivAt.const_add θ (HasDerivAt.const_mul (1 - θ) h2)
  have hne : θ + (1 - θ) * Real.exp ((1 - ε) * 0) ≠ 0 := by simp
  have h4 := HasDerivAt.const_mul (1 - ε)⁻¹ (HasDerivAt.log h3 hne)
  unfold inflFn
  convert h4 using 1
  simp only [mul_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-- Galí (2015), eq. (8), p. 55: the remainder of the log-linear approximation is
`o(y)`, `inflFn θ ε y − (1 − θ) y = o(y)` as `y → 0`. -/
theorem inflFn_isLittleO (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) :
    (fun y => inflFn θ ε y - (1 - θ) * y) =o[nhds 0] fun y => y := by
  have h := (hasDerivAt_iff_isLittleO.1 (hasDerivAt_inflFn θ hε))
  simpa [inflFn_zero, mul_comm] using h

end Gali.BasicNewKeynesianModel.CalvoIndex

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Price dispersion

Galí (2015), Chapter 3, §3.3 (pp. 58–59), eq. (14), and Appendix 3.4 (pp. 85–86).

Goods/firms form a probability space `(G, μ)` (the book's `[0, 1]` with Lebesgue measure, or
finitely many goods with weights summing to one). The dispersion term is
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`, with `P` the CES price index of `CES`.

## Main results

* `employment_level`, `employment_identity`: with `Y(i) = A N(i)^{1−α}` and the demand
  schedule, `N = (Y/A)^{1/(1−α)} ∫ (P(i)/P)^{−ε/(1−α)}` and hence exactly
  `(1 − α) log N = log Y − log A + d` (eq. (14) before approximation).
* `dispersion_nonneg`: `d ≥ 0` (Jensen, via a pointwise Bernoulli inequality).
* `dispersion_eq_zero_iff`, `dispersion_eq_zero_iff_const`: `d = 0` iff all prices equal
  (almost everywhere), i.e. iff `P(i) = P` a.e.
* `dispersion_second_order` (**App. 3.4**): along the family of price distributions
  `p(i) = p̄ + s z(i)` with `z` bounded and measurable (the index condition holding by
  construction of `P`), `d(s) = (ε/(2Θ)) var_i p(i) + O(s³)` as `s → 0`, with
  `Θ = (1 − α)/(1 − α + αε)`. This holds for an arbitrary probability space of goods, so in
  particular for the continuum `[0, 1]`.
* `dispersion_family_isBigO_sq`, `dispersion_family_first_order`: `d(s) = O(s²)`, `d(0) = 0`
  and `d'(0) = 0`: "`d_t` is equal to zero up to a first-order approximation" (p. 59).
* `relLogPrice_moments`, `relLogPrice_mean_second_order`, `relLogPrice_sq_second_order`: the
  intermediate steps of App. 3.4, `E_i p̂ = ((ε − 1)/2) E_i p̂² + O(s³)` and
  `E_i p̂² = var_i p + O(s⁴)`, with `p̂(i) = p(i) − p`.

The proof of the second-order result writes `d(s)` exactly in terms of the cumulant-generating
function `K` of `z`, `d(s) = (1 − α) K(−εs/(1−α)) + (ε/(1−ε)) K((1−ε)s)`, and applies
Taylor's theorem to the analytic function `K` (`K(0) = 0`, `K'(0) = E z`, `K''(0) = var z`).
-/

namespace Gali.BasicNewKeynesianModel.PriceDispersion

open MeasureTheory ProbabilityTheory Gali.BasicNewKeynesianModel.CES

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), p. 59 and App. 3.4, p. 86: the price-dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
noncomputable def dispersion (μ : Measure G) (α ε : ℝ) (P : G → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ)

/-- Galí (2015), p. 60 and App. 3.4, p. 86: `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), App. 3.4, p. 86: the cross-sectional variance
`var_i p(i) = ∫ (p(i) − ∫ p)² di`. -/
noncomputable def crossVar (μ : Measure G) (p : G → ℝ) : ℝ :=
  ∫ i, (p i - ∫ j, p j ∂μ) ^ 2 ∂μ

variable {μ : Measure G} {α ε : ℝ} {P : G → ℝ}

/-- Galí (2015), p. 59: with production `Y(i) = A N(i)^{1−α}` (5) and output on the demand
schedule `Y(i) = (P(i)/P)^{−ε} Y` (from (1) and goods-market clearing), aggregate employment
is `N = ∫ N(i) = (Y/A)^{1/(1−α)} ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
theorem employment_level (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α)) :
    ∫ i, N i ∂μ
      = (Y / A) ^ (1 - α)⁻¹ * ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ := by
  have hI := priceIndex_pos hpos
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  have hpt : ∀ i, N i = (Y / A) ^ (1 - α)⁻¹ * (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) := by
    intro i
    have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
    have h1 : N i ^ (1 - α) = (P i / priceIndex μ ε P) ^ (-ε) * (Y / A) := by
      have := hprod i
      rw [demand] at this
      field_simp
      linarith
    rw [← Real.rpow_rpow_inv (hN i) hsub, h1, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha.le, div_eq_mul_inv (-ε), mul_comm]
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Galí (2015), p. 59, eq. (14) before approximation (**exact**):
`(1 − α) log N = log Y − log A + d`. -/
theorem employment_identity (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α))
    (hD : 0 < ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ) :
    (1 - α) * Real.log (∫ i, N i ∂μ) = Real.log Y - Real.log A + dispersion μ α ε P := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [employment_level hα1 hP hpos hA hY.le hN hprod, Real.log_mul (by positivity) hD.ne',
    Real.log_rpow (by positivity), Real.log_div hY.ne' hA.ne', dispersion]
  field_simp

/-- Galí (2015), App. 3.4, p. 85: the exponent `q = ε/((ε − 1)(1 − α))` turning
`y(i) = (P(i)/P)^{1−ε}` into `y(i)^q = (P(i)/P)^{−ε/(1−α)}` exceeds one. -/
theorem one_lt_q (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 < ε / ((ε - 1) * (1 - α)) := by
  rw [one_lt_div (by apply mul_pos <;> linarith)]
  nlinarith

/-- Galí (2015), App. 3.4, p. 85: `(P(i)/P)^{−ε/(1−α)} = ((P(i)/P)^{1−ε})^q`. -/
theorem rpow_disp_eq (hε : 1 < ε) (hα1 : α < 1) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-ε / (1 - α)) = (x ^ (1 - ε)) ^ (ε / ((ε - 1) * (1 - α))) := by
  rw [← Real.rpow_mul hx]
  congr 1
  have : (1 : ℝ) - α ≠ 0 := by linarith
  have : ε - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), App. 3.4, p. 85: the pointwise Bernoulli bound
`(P(i)/P)^{−ε/(1−α)} ≥ 1 + q((P(i)/P)^{1−ε} − 1)`, strict unless `P(i) = P`. -/
theorem bernoulli_disp (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) {x : ℝ} (hx : 0 < x) :
    1 + ε / ((ε - 1) * (1 - α)) * (x ^ (1 - ε) - 1) ≤ x ^ (-ε / (1 - α)) ∧
      (1 + ε / ((ε - 1) * (1 - α)) * (x ^ (1 - ε) - 1) = x ^ (-ε / (1 - α)) → x = 1) := by
  have hy : 0 < x ^ (1 - ε) := Real.rpow_pos_of_pos hx _
  have hs : -1 ≤ x ^ (1 - ε) - 1 := by linarith
  rw [rpow_disp_eq hε hα1 hx.le]
  have hq := one_lt_q hε hα0 hα1
  refine ⟨by simpa using one_add_mul_self_le_rpow_one_add hs hq.le, fun heq => ?_⟩
  by_contra hne
  have hy1 : x ^ (1 - ε) - 1 ≠ 0 := by
    intro h0
    have h1 : x ^ (1 - ε) = 1 := by linarith
    have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
    apply hne
    rw [← Real.rpow_rpow_inv hx.le hsub, h1, Real.one_rpow]
  have := one_add_mul_self_lt_rpow_one_add hs hy1 hq
  simp only [add_sub_cancel] at this
  linarith

/-- Galí (2015), App. 3.4, p. 85: the Bernoulli lower bound integrates to one,
`∫ (1 + q((P(i)/P)^{1−ε} − 1)) = 1`, by the index condition (probability measure). -/
theorem integral_bernoulli_lower [IsProbabilityMeasure μ] (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (q : ℝ) :
    Integrable (fun i => 1 + q * ((P i / priceIndex μ ε P) ^ (1 - ε) - 1)) μ ∧
      ∫ i, (1 + q * ((P i / priceIndex μ ε P) ^ (1 - ε) - 1)) ∂μ = 1 := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun i => Real.rpow_pos_of_pos (hP i) (1 - ε)) hPi
  have hy := integrable_relPrice_rpow hPi hP hpos
  have he : (fun i => 1 + q * ((P i / priceIndex μ ε P) ^ (1 - ε) - 1))
      = fun i => (1 - q) + q * (P i / priceIndex μ ε P) ^ (1 - ε) := by
    funext i
    ring
  rw [he]
  refine ⟨(integrable_const _).add (hy.const_mul q), ?_⟩
  rw [integral_add (integrable_const _) (hy.const_mul q), integral_const, integral_const_mul,
    integral_relPrice_rpow hε hP hpos]
  simp

/-- Galí (2015), App. 3.4, p. 85 (Jensen): with the index condition `∫ (P(i)/P)^{1−ε} = 1`,
`∫ (P(i)/P)^{−ε/(1−α)} ≥ 1`. -/
theorem one_le_integral_disp [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    1 ≤ ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun i => Real.rpow_pos_of_pos (hP i) (1 - ε)) hPi
  have hI := priceIndex_pos hpos
  obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hP hPi (ε / ((ε - 1) * (1 - α)))
  have h := integral_mono hlow hD fun i => (bernoulli_disp hε hα0 hα1 (div_pos (hP i) hI)).1
  rwa [hval] at h

/-- Galí (2015), App. 3.4, p. 85: **price dispersion is nonnegative**, `d ≥ 0`. -/
theorem dispersion_nonneg [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    0 ≤ dispersion μ α ε P :=
  mul_nonneg (by linarith) (Real.log_nonneg (one_le_integral_disp hε hα0 hα1 hP hPi hD))

/-- Galí (2015), p. 59 and App. 3.4, p. 85: `d = 0` **iff** every price equals the index,
`P(i) = P` for almost every `i`. -/
theorem dispersion_eq_zero_iff [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dispersion μ α ε P = 0 ↔ ∀ᵐ i ∂μ, P i = priceIndex μ ε P := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun i => Real.rpow_pos_of_pos (hP i) (1 - ε)) hPi
  have hI := priceIndex_pos hpos
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  constructor
  · intro h0
    have hlog : Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ) = 0 := by
      rw [dispersion] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hsub
      · exact h
    have h1 := one_le_integral_disp hε hα0 hα1 hP hPi hD
    have hint1 : ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ = 1 := by
      rcases Real.log_eq_zero.1 hlog with h | h | h <;> [linarith; exact h; linarith]
    obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hP hPi (ε / ((ε - 1) * (1 - α)))
    have hz := (integral_eq_zero_iff_of_nonneg (fun i => sub_nonneg.2
      (bernoulli_disp hε hα0 hα1 (div_pos (hP i) hI)).1) (hD.sub hlow)).1 (by
        rw [integral_sub hD hlow, hint1, hval, sub_self])
    filter_upwards [hz] with i hi
    simp only [Pi.zero_apply, sub_eq_zero] at hi
    have := (bernoulli_disp hε hα0 hα1 (div_pos (hP i) hI)).2 hi.symm
    rwa [div_eq_one_iff_eq hI.ne'] at this
  · intro h
    have hint1 : ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ = 1 := by
      rw [integral_congr_ae (g := fun _ => (1 : ℝ)) (by
        filter_upwards [h] with i hi
        rw [hi, div_self hI.ne', Real.one_rpow])]
      simp
    rw [dispersion, hint1, Real.log_one, mul_zero]

/-- Galí (2015), p. 59: `d = 0` iff all prices are equal (to some common value `c`, which
is then the price index). -/
theorem dispersion_eq_zero_iff_const [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dispersion μ α ε P = 0 ↔ ∃ c, ∀ᵐ i ∂μ, P i = c := by
  rw [dispersion_eq_zero_iff hε hα0 hα1 hP hPi hD]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨c, hc⟩ => ?_⟩
  obtain ⟨i₀, hi₀⟩ := hc.exists
  have hc0 : 0 < c := hi₀ ▸ hP i₀
  have hidx : priceIndex μ ε P = c := by
    unfold priceIndex
    rw [integral_congr_ae (g := fun _ => c ^ (1 - ε)) (by
      filter_upwards [hc] with i hi
      rw [hi])]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact Real.rpow_rpow_inv hc0.le (by linarith)
  rw [hidx]
  exact hc

/-- Galí (2015), App. 3.4, p. 85: for a bounded measurable `z` on a probability space, every
`exp(t z)` is integrable (so the moment-generating function is finite everywhere). -/
theorem integrable_exp_mul [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (t : ℝ) : Integrable (fun i => Real.exp (t * z i)) μ := by
  refine Integrable.of_bound ((measurable_const.mul hz).exp.aestronglyMeasurable)
    (Real.exp (|t| * B)) (Filter.Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * z i ≤ |t * z i| := le_abs_self _
    _ = |t| * |z i| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB i) (abs_nonneg t)

/-- Galí (2015), App. 3.4, p. 85: for bounded `z`, the cumulant-generating function is
analytic on all of `ℝ` (the domain of finiteness of the mgf is `ℝ`). -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Galí (2015), App. 3.4, pp. 85–86: **second-order Taylor expansion of the cumulant
generating function** of a bounded `z`:
`K(u) = (E z) u + (var z/2) u² + O(u³)` as `u → 0`. -/
theorem cgf_taylor [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) :
    (fun u => cgf z μ u - (∫ i, z i ∂μ) * u - (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      =O[nhds 0] fun u => u ^ 3 := by
  have hint := interior_integrableExpSet (μ := μ) hz hB
  have hAn : AnalyticOnNhd ℝ (cgf z μ) Set.univ := by
    have := analyticOnNhd_cgf (X := z) (μ := μ)
    rwa [hint] at this
  have hCD : ContDiff ℝ 3 (cgf z μ) := hAn.contDiff
  have hT := taylor_isLittleO_univ (x₀ := 0) hCD
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hint]
    trivial
  have hd1 : deriv (cgf z μ) 0 = ∫ i, z i ∂μ := by
    rw [deriv_cgf_zero h0]
    simp
  have hd2 : iteratedDeriv 2 (cgf z μ) 0 = ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ := by
    rw [iteratedDeriv_two_cgf_eq_integral h0, hd1, mgf_zero]
    simp
  have heq : (fun u => cgf z μ u - (∫ i, z i ∂μ) * u -
      (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      = fun u => (cgf z μ u - taylorWithinEval (cgf z μ) 3 Set.univ 0 u) +
        iteratedDeriv 3 (cgf z μ) 0 / 6 * u ^ 3 := by
    funext u
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_univ,
      iteratedDeriv_zero, iteratedDeriv_one, hd1, hd2, cgf_zero, smul_eq_mul, sub_zero]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  simp only [sub_zero] at hT
  exact hT.isBigO.add ((Asymptotics.isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 3.4, pp. 85–86: the Taylor remainder of `K` along a ray,
`K(a s) − (E z)(a s) − (var z/2)(a s)² = O(s³)` as `s → 0`, for every slope `a`. -/
theorem cgf_taylor_comp [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (a : ℝ) :
    (fun s => cgf z μ (a * s) - (∫ i, z i ∂μ) * (a * s) -
      (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * (a * s) ^ 2) =O[nhds 0] fun s => s ^ 3 := by
  have hR := cgf_taylor (μ := μ) hz hB
  have ht : Filter.Tendsto (fun s : ℝ => a * s) (nhds 0) (nhds 0) := by
    have := (Filter.tendsto_id (x := nhds (0 : ℝ))).const_mul a
    simpa using this
  refine (hR.comp_tendsto ht).trans ?_
  have : ((fun u : ℝ => u ^ 3) ∘ fun s => a * s) = fun s => a ^ 3 * s ^ 3 := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [this]
  exact (Asymptotics.isBigO_refl _ _).const_mul_left _

/-- Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))` the log price
index is `p = p̄ + K((1 − ε)s)/(1 − ε)`, i.e. `P = exp(p̄ + K((1−ε)s)/(1−ε))`. -/
theorem priceIndex_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar s : ℝ) :
    priceIndex μ ε (fun i => Real.exp (pbar + s * z i))
      = Real.exp (pbar + cgf z μ ((1 - ε) * s) / (1 - ε)) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsum : ∫ i, Real.exp (pbar + s * z i) ^ (1 - ε) ∂μ
      = Real.exp ((1 - ε) * pbar) * mgf z μ ((1 - ε) * s) := by
    have : ∀ i, Real.exp (pbar + s * z i) ^ (1 - ε)
        = Real.exp ((1 - ε) * pbar) * Real.exp ((1 - ε) * s * z i) := by
      intro i
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  unfold priceIndex
  rw [hsum, Real.rpow_def_of_pos (mul_pos (Real.exp_pos _) (hM _)),
    Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf]
  congr 1
  field_simp

/-- Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))`, the dispersion
term is exactly `d(s) = (1 − α) K(−εs/(1−α)) + (ε/(1−ε)) K((1−ε)s)`, with `K` the cumulant
generating function of `z`. -/
theorem dispersion_family_eq [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (hα : α ≠ 1) (pbar s : ℝ) :
    dispersion μ α ε (fun i => Real.exp (pbar + s * z i))
      = (1 - α) * cgf z μ (-ε / (1 - α) * s) + ε / (1 - ε) * cgf z μ ((1 - ε) * s) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsubα : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hidx : priceIndex μ ε (fun i => Real.exp (pbar + s * z i))
      = Real.exp (pbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε)) :=
    priceIndex_family hz hB hε pbar s
  have hrel : ∀ i, (Real.exp (pbar + s * z i) /
      Real.exp (pbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) ^ (-ε / (1 - α))
      = Real.exp (ε / (1 - α) * (Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) *
        Real.exp (-ε / (1 - α) * s * z i) := by
    intro i
    rw [← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [dispersion, hidx]
  simp_rw [hrel]
  rw [integral_const_mul]
  have hm2 : ∫ i, Real.exp (-ε / (1 - α) * s * z i) ∂μ = mgf z μ (-ε / (1 - α) * s) := rfl
  rw [hm2, Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf, cgf]
  field_simp
  ring

/-- Galí (2015), App. 3.4, p. 86: the cross-sectional variance of `p(i) = p̄ + s z(i)` is
`s² var z`. -/
theorem crossVar_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (pbar s : ℝ) :
    crossVar μ (fun i => pbar + s * z i) = s ^ 2 * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ := by
  have hzI : Integrable z μ :=
    Integrable.of_bound hz.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hB i)
  have hmean : ∫ i, (pbar + s * z i) ∂μ = pbar + s * ∫ i, z i ∂μ := by
    rw [integral_add (integrable_const _) (hzI.const_mul s), integral_const, integral_const_mul]
    simp
  unfold crossVar
  beta_reduce
  rw [hmean]
  have hpt : ∀ i, (pbar + s * z i - (pbar + s * ∫ j, z j ∂μ)) ^ 2
      = s ^ 2 * (z i - ∫ j, z j ∂μ) ^ 2 := fun i => by ring
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Galí (2015), App. 3.4, pp. 85–86 (**second-order approximation of price dispersion**):
for any probability space of goods, any bounded measurable `z` and any level `p̄`, the family
of price distributions `p(i) = p̄ + s z(i)` (with `P` its CES index, so the index condition
holds) satisfies `d(s) = (ε/(2Θ)) var_i p(i) + O(s³)` as `s → 0`,
`Θ = (1 − α)/(1 − α + αε)`. -/
theorem dispersion_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 3 := by
  have hcomp := cgf_taylor_comp (μ := μ) hz hB
  have hsubε : (1 : ℝ) - ε ≠ 0 := by linarith
  have hsubα : (1 : ℝ) - α ≠ 0 := by linarith
  have hden : 1 - α + α * ε ≠ 0 := by nlinarith
  have heq : (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      = fun s => (1 - α) * (cgf z μ (-ε / (1 - α) * s) - (∫ i, z i ∂μ) * (-ε / (1 - α) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * (-ε / (1 - α) * s) ^ 2) +
        ε / (1 - ε) * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [dispersion_family_eq hz hB (by linarith) (by linarith), crossVar_family hz hB, bigTheta]
    field_simp
    ring
  rw [heq]
  exact ((hcomp _).const_mul_left _).add ((hcomp _).const_mul_left _)

/-- Galí (2015), p. 59 and App. 3.4: along the family `p(i) = p̄ + s z(i)`, `d(s) = O(s²)`. -/
theorem dispersion_family_isBigO_sq [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i))) =O[nhds 0]
      fun s => s ^ 2 := by
  have h3 := dispersion_second_order (μ := μ) hz hB hε hα0 hα1 pbar
  have h32 : (fun s : ℝ => s ^ 3) =O[nhds 0] fun s => s ^ 2 :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
  have hq : (fun s => ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 2 := by
    have : (fun s => ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
        = fun s => (ε / (2 * bigTheta α ε) * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hz hB]
      ring
    rw [this]
    exact (Asymptotics.isBigO_refl _ _).const_mul_left _
  have := (h3.trans h32).add hq
  simpa using this

/-- Galí (2015), p. 59 (**`d_t` vanishes to first order**): along the family
`p(i) = p̄ + s z(i)`, `d(0) = 0` and `d'(0) = 0`. -/
theorem dispersion_family_first_order [IsProbabilityMeasure μ] {z : G → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (pbar : ℝ) :
    dispersion μ α ε (fun i => Real.exp (pbar + 0 * z i)) = 0 ∧
      HasDerivAt (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i))) 0 0 := by
  have hd0 : dispersion μ α ε (fun i => Real.exp (pbar + 0 * z i)) = 0 := by
    rw [dispersion_family_eq hz hB (by linarith) (by linarith)]
    simp [cgf_zero]
  refine ⟨hd0, ?_⟩
  rw [hasDerivAt_iff_isLittleO, hd0]
  have h2 := dispersion_family_isBigO_sq (μ := μ) hz hB hε hα0 hα1 pbar
  have h21 : (fun s : ℝ => s ^ 2) =o[nhds 0] fun s => s ^ 1 :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 1 < 2)
  simpa using h2.trans_isLittleO h21

/-- Galí (2015), App. 3.4, p. 85: the log relative price `p̂(i) = p(i) − p` along the family
`p(i) = p̄ + s z(i)`, with `p` the log CES price index. -/
noncomputable def relLogPrice (μ : Measure G) (ε : ℝ) (z : G → ℝ) (pbar s : ℝ) (i : G) : ℝ :=
  pbar + s * z i - Real.log (priceIndex μ ε (fun j => Real.exp (pbar + s * z j)))

/-- Galí (2015), App. 3.4, pp. 85–86 (exact moments of `p̂`): `E_i p̂ = s E z − K((1−ε)s)/(1−ε)`
and `E_i p̂² = var_i p + (E_i p̂)²`. -/
theorem relLogPrice_moments [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar s : ℝ) :
    ∫ i, relLogPrice μ ε z pbar s i ∂μ
        = s * (∫ i, z i ∂μ) - cgf z μ ((1 - ε) * s) / (1 - ε) ∧
      ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ
        = crossVar μ (fun i => pbar + s * z i) + (∫ i, relLogPrice μ ε z pbar s i ∂μ) ^ 2 := by
  have hzI : Integrable z μ :=
    Integrable.of_bound hz.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hB i)
  set m := ∫ i, z i ∂μ
  have hz2 : Integrable (fun i => (z i - m) ^ 2) μ := by
    refine Integrable.of_bound ((hz.sub measurable_const).pow_const 2).aestronglyMeasurable
      ((B + |m|) ^ 2) (Filter.Eventually.of_forall fun i => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have h1 : |z i - m| ≤ B + |m| := (abs_sub _ _).trans (by linarith [hB i])
    calc (z i - m) ^ 2 = |z i - m| ^ 2 := (sq_abs _).symm
      _ ≤ (B + |m|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hzc : Integrable (fun i => z i - m) μ := hzI.sub (integrable_const m)
  have hzm : ∫ i, (z i - m) ∂μ = 0 := by
    rw [integral_sub hzI (integrable_const m)]
    simp [m]
  set e := s * m - cgf z μ ((1 - ε) * s) / (1 - ε)
  have hpt : ∀ i, relLogPrice μ ε z pbar s i = s * (z i - m) + e := by
    intro i
    rw [relLogPrice, priceIndex_family hz hB hε, Real.log_exp]
    ring
  have hmean : ∫ i, relLogPrice μ ε z pbar s i ∂μ = e := by
    simp_rw [hpt]
    rw [integral_add (hzc.const_mul s) (integrable_const e), integral_const_mul, hzm]
    simp
  refine ⟨hmean, ?_⟩
  rw [hmean, crossVar_family hz hB]
  have hsq : ∀ i, relLogPrice μ ε z pbar s i ^ 2
      = s ^ 2 * (z i - m) ^ 2 + (2 * s * e) * (z i - m) + e ^ 2 := by
    intro i
    rw [hpt]
    ring
  simp_rw [hsq]
  have hA : Integrable (fun i => s ^ 2 * (z i - m) ^ 2 + 2 * s * e * (z i - m)) μ :=
    (hz2.const_mul _).add (hzc.const_mul _)
  rw [integral_add hA (integrable_const _), integral_add (hz2.const_mul _) (hzc.const_mul _),
    integral_const_mul, integral_const_mul, hzm]
  simp [m]

/-- Galí (2015), App. 3.4, p. 85: `E_i p̂ = ((ε − 1)/2) E_i p̂² + O(s³)` along the family
`p(i) = p̄ + s z(i)` (the second-order consequence of the index condition). -/
theorem relLogPrice_mean_second_order [IsProbabilityMeasure μ] {z : G → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (pbar : ℝ) :
    (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ -
        (ε - 1) / 2 * ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ) =O[nhds 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := by linarith
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  set m := ∫ i, z i ∂μ
  set v := ∫ i, (z i - m) ^ 2 ∂μ
  set R : ℝ → ℝ := fun s => cgf z μ ((1 - ε) * s) - m * ((1 - ε) * s) - v / 2 * ((1 - ε) * s) ^ 2
  have hmean : ∀ s, ∫ i, relLogPrice μ ε z pbar s i ∂μ
      = -(R s / (1 - ε)) - (1 - ε) * v / 2 * s ^ 2 := by
    intro s
    rw [(relLogPrice_moments hz hB hε.ne' pbar s).1]
    simp only [R]
    field_simp
    ring
  have hE : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ) =O[nhds 0] fun s => s ^ 2 := by
    have h32 : (fun s : ℝ => s ^ 3) =O[nhds 0] fun s => s ^ 2 :=
      (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
    have : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ)
        = fun s => (-(1 - ε)⁻¹) * R s + (-((1 - ε) * v / 2)) * s ^ 2 := by
      funext s
      rw [hmean]
      field_simp
      ring
    rw [this]
    exact ((hR.trans h32).const_mul_left _).add ((Asymptotics.isBigO_refl _ _).const_mul_left _)
  have hE2 : (fun s => (∫ i, relLogPrice μ ε z pbar s i ∂μ) *
      (∫ i, relLogPrice μ ε z pbar s i ∂μ)) =O[nhds 0] fun s => s ^ 3 := by
    have h4 := hE.mul hE
    have e4 : (fun s : ℝ => s ^ 2 * s ^ 2) = fun s => s ^ 4 := by
      funext s
      ring
    rw [e4] at h4
    exact h4.trans (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 4)).isBigO
  have heq : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ -
        (ε - 1) / 2 * ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ)
      = fun s => (-(1 - ε)⁻¹) * R s + (-((ε - 1) / 2)) *
          ((∫ i, relLogPrice μ ε z pbar s i ∂μ) * (∫ i, relLogPrice μ ε z pbar s i ∂μ)) := by
    funext s
    rw [(relLogPrice_moments hz hB hε.ne' pbar s).2, crossVar_family hz hB, hmean]
    field_simp
    ring
  rw [heq]
  exact (hR.const_mul_left _).add (hE2.const_mul_left _)

/-- Galí (2015), App. 3.4, p. 86: `∫ (p(i) − p)² di ≃ var_i p(i)`; precisely, along the family
`p(i) = p̄ + s z(i)` the difference is `(E_i p̂)² = O(s⁴)`. -/
theorem relLogPrice_sq_second_order [IsProbabilityMeasure μ] {z : G → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (pbar : ℝ) :
    (fun s => ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ - crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 4 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := by linarith
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  have h32 : (fun s : ℝ => s ^ 3) =O[nhds 0] fun s => s ^ 2 :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
  have hE : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ) =O[nhds 0] fun s => s ^ 2 := by
    have : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ)
        = fun s => (-(1 - ε)⁻¹) * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
            (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) +
          (-((1 - ε) * (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2)) * s ^ 2 := by
      funext s
      rw [(relLogPrice_moments hz hB hε.ne' pbar s).1]
      field_simp
      ring
    rw [this]
    exact ((hR.trans h32).const_mul_left _).add ((Asymptotics.isBigO_refl _ _).const_mul_left _)
  have heq : (fun s => ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ -
      crossVar μ (fun i => pbar + s * z i))
      = fun s => (∫ i, relLogPrice μ ε z pbar s i ∂μ) * (∫ i, relLogPrice μ ε z pbar s i ∂μ) := by
    funext s
    rw [(relLogPrice_moments hz hB hε.ne' pbar s).2]
    ring
  rw [heq]
  have h4 := hE.mul hE
  have e4 : (fun s : ℝ => s ^ 2 * s ^ 2) = fun s => s ^ 4 := by
    funext s
    ring
  rwa [e4] at h4

end Gali.BasicNewKeynesianModel.PriceDispersion

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The reset-price problem

Galí (2015), Chapter 3, §3.2.2 (pp. 56–57) and Appendix 3.3 (pp. 84–85).

A firm that resets its price at `t` chooses `P*` to maximise the genuine infinite
discounted sum `∑ₖ θᵏ E_t[Q_{t,t+k}(P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))]` subject to
the demand schedule (9), `Y_{t+k|t} = (P*/P_{t+k})^{−ε} C_{t+k}`. Expectations are
an arbitrary `ExpectationSystem`, so every statement holds under perfect foresight
and under uncertainty.

## Main results

* `E_tsum`: `E_t` commutes with discounted sums of bounded random variables (a
  consequence of the expectation axioms alone).
* `forwardSum_rec`, `forwardSum_unique`, `normForward_rec`, `normForward_unique`:
  recursive forms of discounted forward sums and their uniqueness among bounded
  processes.
* `hasDerivAt_E`, `hasDerivAt_tsum_E`: differentiation under `E_t` and under the
  infinite sum, with explicit Lipschitz and domination hypotheses.
* `hasDerivAt_objective`: the derivative of the objective is
  `((1 − ε)/P*) ∑ₖ θᵏ E_t[Q Y (P* − M Ψ')]`; `foc_of_isLocalMax`: (10) is necessary.
* `isMaxOn_iff_foc`: with convex costs (10) characterises the optimum, and the
  optimum is unique.
* `flexible_foc_iff`, `flexible_price_optimum`: `θ = 0 ⇒ P* = M Ψ'_{t|t}`.
* `steadyState_foc_iff`: in the zero-inflation steady state `P = M Ψ`.
* `hasDerivAt_focLHS_path`, `eq11_iff`: the log-linear rule (11) is exactly the
  vanishing of the derivative of (10) at the steady state along any bounded
  perturbation.
* `resetPrice_recursive`: the recursive form of the pricing rule.
* `reset_prob_sum`, `firmValue_eq`, `isMaxOn_firmValue_iff`: Appendix 3.3, eq. (37).
-/

namespace Gali.BasicNewKeynesianModel.ResetPrice

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Conditional expectations of discounted sums -/

/-- A geometrically weighted series of uniformly bounded random variables
converges at every state (used throughout Galí (2015), ch. 3, e.g. eq. (11), p. 57). -/
theorem summable_geometric_bounded {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) : Summable fun k => a ^ k * y k ω := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)

/-- The bound of a geometrically weighted series of bounded random variables:
`|∑ aᵏ yₖ| ≤ M / (1 − |a|)` (Galí (2015), ch. 3, p. 57). -/
theorem abs_tsum_geometric_le {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) :
    |∑' k, a ^ k * y k ω| ≤ M / (1 - |a|) := by
  have hs := summable_geometric_bounded ha hy ω
  have hg : Summable fun k => |a| ^ k * M :=
    (summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M
  have h1 : |∑' k, a ^ k * y k ω| ≤ ∑' k, |a ^ k * y k ω| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k => a ^ k * y k ω)
        (by simpa only [Real.norm_eq_abs] using hs.abs)
  have h2 : ∑' k, |a ^ k * y k ω| ≤ ∑' k, |a| ^ k * M := by
    refine Summable.tsum_le_tsum (fun k => ?_) hs.abs hg
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)
  rw [tsum_mul_right, tsum_geometric_of_lt_one (abs_nonneg a) ha] at h2
  calc |∑' k, a ^ k * y k ω| ≤ (1 - |a|)⁻¹ * M := h1.trans h2
    _ = M / (1 - |a|) := by rw [div_eq_inv_mul]

/-- **Conditional expectations commute with discounted sums.** For uniformly
bounded random variables and `|a| < 1`,
`E_t[∑ₖ aᵏ yₖ] = ∑ₖ aᵏ E_t yₖ`. This is the interchange used whenever Galí (2015)
writes `E_t` inside an infinite discounted sum (eqs. (10), (11), (16), pp. 56–60).
It follows from the expectation axioms alone: `E_t` is monotone and preserves
constants, so it is continuous for the uniform norm. -/
theorem E_tsum {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (t : ℕ) :
    𝔼.E t (fun ω => ∑' k, a ^ k * y k ω) = fun ω => ∑' k, a ^ k * 𝔼.E t (y k) ω := by
  funext ω
  set F : Ω → ℝ := fun ω => ∑' k, a ^ k * y k ω with hF
  set Fn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, a ^ k • y k with hFn
  set T : ℕ → ℝ := fun n => ∑' k, |a| ^ (k + n) * M with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add fun k => |a| ^ k * M
  have htail : ∀ n ω', |F ω' - Fn n ω'| ≤ T n := by
    intro n ω'
    have hs := summable_geometric_bounded ha hy ω'
    have hsplit := hs.sum_add_tsum_nat_add n
    have hFn' : Fn n ω' = ∑ k ∈ Finset.range n, a ^ k * y k ω' := by
      simp [hFn, Finset.sum_apply]
    rw [hFn']
    change |∑' k, a ^ k * y k ω' - _| ≤ T n
    rw [← hsplit, add_sub_cancel_left]
    have hs' : Summable fun k => a ^ (k + n) * y (k + n) ω' :=
      (summable_nat_add_iff n).mpr hs
    have hg : Summable fun k => |a| ^ (k + n) * M :=
      (summable_nat_add_iff n).mpr
        ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    calc |∑' k, a ^ (k + n) * y (k + n) ω'| ≤ ∑' k, |a ^ (k + n) * y (k + n) ω'| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => a ^ (k + n) * y (k + n) ω')
              (by simpa only [Real.norm_eq_abs] using hs'.abs)
      _ ≤ T n := by
          refine Summable.tsum_le_tsum (fun k => ?_) hs'.abs hg
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (hy (k + n) ω') (pow_nonneg (abs_nonneg a) _)
  have hEFn : ∀ n, 𝔼.E t (Fn n) ω = ∑ k ∈ Finset.range n, a ^ k * 𝔼.E t (y k) ω := by
    intro n
    simp [hFn, map_sum, map_smul, Finset.sum_apply]
  have hlim1 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop (𝓝 (𝔼.E t F ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hTlim
    have h := 𝔼.abs_E_le (x := F - Fn n) (fun ω' => htail n ω') t ω
    rw [map_sub, Pi.sub_apply] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have hbE : ∀ k ω', |𝔼.E t (y k) ω'| ≤ M := fun k ω' => 𝔼.abs_E_le (hy k) t ω'
  have hlim2 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop
      (𝓝 (∑' k, a ^ k * 𝔼.E t (y k) ω)) := by
    simp_rw [hEFn]
    exact (summable_geometric_bounded ha hbE ω).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim1 hlim2

/-- The discounted forward sum `∑ₖ aᵏ E_t x_{t+k}` of a process (Galí (2015),
eqs. (11) and (16), pp. 57–60, and the forward solution of (17), p. 61). -/
noncomputable def forwardSum (a : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * 𝔼.E t (x (t + k)) ω

/-- The forward sum of a process bounded by `M` is bounded by `M / (1 − |a|)`
(Galí (2015), p. 60). -/
theorem abs_forwardSum_le {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |forwardSum 𝔼 a x t ω| ≤ M / (1 - |a|) :=
  abs_tsum_geometric_le ha (fun k ω' => 𝔼.bounded_E hx t (t + k) ω') ω

/-- The forward sum of a bounded process is a bounded process (Galí (2015), p. 60). -/
theorem forwardSum_bounded {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} (hx : BoundedProc x) :
    BoundedProc (forwardSum 𝔼 a x) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M / (1 - |a|), fun t ω => abs_forwardSum_le 𝔼 ha hM t ω⟩

/-- **Recursive form of a forward sum** (Galí (2015), the step from the series
for `p*` to eq. (16), p. 60): for a bounded adapted process `x`,
`S_t = x_t + a E_t S_{t+1}` where `S_t = ∑ₖ aᵏ E_t x_{t+k}`. -/
theorem forwardSum_rec {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) (t : ℕ) :
    forwardSum 𝔼 a x t = x t + a • 𝔼.E t (forwardSum 𝔼 a x (t + 1)) := by
  have hy : ∀ k ω, |𝔼.E (t + 1) (x (t + 1 + k)) ω| ≤ M :=
    fun k ω => 𝔼.bounded_E hx (t + 1) (t + 1 + k) ω
  have hE : 𝔼.E t (forwardSum 𝔼 a x (t + 1))
      = fun ω => ∑' k, a ^ k * 𝔼.E t (x (t + 1 + k)) ω := by
    unfold forwardSum
    rw [E_tsum 𝔼 ha hy t]
    funext ω
    congr 1
    funext k
    rw [𝔼.tower (Nat.le_succ t)]
  rw [hE]
  funext ω
  have hs := summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hx t (t + k) ω') ω
  simp only [forwardSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, hxa t, ← tsum_mul_left]
  congr 1
  congr 1
  funext k
  rw [pow_succ, show t + (k + 1) = t + 1 + k by omega]
  ring

/-- **Uniqueness of the forward sum** (Galí (2015), p. 60–61): with `|a| < 1`,
the forward sum is the only bounded process satisfying `S_t = x_t + a E_t S_{t+1}`. -/
theorem forwardSum_unique {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) {z : ℕ → Ω → ℝ} (hz : BoundedProc z)
    (hzrec : ∀ t, z t = x t + a • 𝔼.E t (z (t + 1))) : z = forwardSum 𝔼 a x := by
  refine 𝔼.forward_unique ha (u := x) (fun t => ?_) (fun t => ?_) hz
    (forwardSum_bounded 𝔼 ha ⟨M, hx⟩)
  · rw [add_comm]; exact hzrec t
  · rw [add_comm]; exact forwardSum_rec 𝔼 ha hx hxa t

/-! ### Differentiating under `E_t` -/

/-- **Differentiation under a conditional expectation.** If the second-order
remainder of `z ↦ g z` at `x` is bounded by `C h²` uniformly in the state, then
`z ↦ E_t[g z]` has derivative `E_t[g']` at `x`. Needed to differentiate the
reset-price objective of Galí (2015), p. 56, under `E_t`. -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- A Lipschitz bound on the derivative bounds the second-order remainder:
`|f(x+h) − f(x) − h f'(x)| ≤ L h²` (mean value theorem). -/
theorem remainder_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {x r L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ y ∈ Metric.ball x r, HasDerivAt f (f' y) y)
    (hL : ∀ y ∈ Metric.ball x r, |f' y - f' x| ≤ L * |y - x|) {h : ℝ} (hh : |h| < r) :
    |f (x + h) - f x - h * f' x| ≤ L * h ^ 2 := by
  have hsub : Metric.closedBall x |h| ⊆ Metric.ball x r :=
    Metric.closedBall_subset_ball hh
  have hd : ∀ y ∈ Metric.closedBall x |h|,
      HasDerivWithinAt (fun z => f z - z * f' x) (f' y - f' x) (Metric.closedBall x |h|) y := by
    intro y hy
    have h1 := hf y (hsub hy)
    have h2 : HasDerivAt (fun z : ℝ => z * f' x) (f' x) y := by
      simpa using (hasDerivAt_id y).mul_const (f' x)
    exact (HasDerivAt.sub h1 h2).hasDerivWithinAt
  have hb : ∀ y ∈ Metric.closedBall x |h|, ‖f' y - f' x‖ ≤ L * |h| := by
    intro y hy
    rw [Real.norm_eq_abs]
    refine (hL y (hsub hy)).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    simpa [Metric.mem_closedBall, Real.dist_eq] using hy
  have hx : x ∈ Metric.closedBall x |h| := Metric.mem_closedBall_self (abs_nonneg h)
  have hxh : x + h ∈ Metric.closedBall x |h| := by
    simp [Metric.mem_closedBall]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_closedBall x |h|) hx hxh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at this
  calc |f (x + h) - f x - h * f' x| = |f (x + h) - (x + h) * f' x - (f x - x * f' x)| := by
        ring_nf
    _ ≤ L * |h| * |h| := this
    _ = L * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Differentiation under `E_t`, Lipschitz form.** If `z ↦ g z ω` has derivative
`g' z ω` near `x` and the derivative is Lipschitz at `x` uniformly in the state,
then `z ↦ E_t[g z]` has derivative `E_t[g' x]` at `x` (Galí (2015), p. 56). -/
theorem hasDerivAt_E {g g' : ℝ → Ω → ℝ} {x r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hg : ∀ y ∈ Metric.ball x r, ∀ ω, HasDerivAt (fun z => g z ω) (g' y ω) y)
    (hL : ∀ y ∈ Metric.ball x r, ∀ ω, |g' y ω - g' x ω| ≤ L * |y - x|) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t (g' x) ω) x :=
  hasDerivAt_E_of_remainder 𝔼 hr (fun _ hh ω' => remainder_le_of_lipschitz_deriv hL0
    (fun y hy => hg y hy ω') (fun y hy => hL y hy ω') hh) t ω

/-- **Term-by-term differentiation of a discounted sum of conditional
expectations** (Galí (2015), eq. (10), p. 56): `z ↦ ∑ₖ θᵏ E_t[gₖ z]` has
derivative `∑ₖ θᵏ E_t[g'ₖ x]` on an open interval `U`, provided each `g'ₖ` is
locally Lipschitz uniformly in the state and dominated by `uₖ` with
`∑ |θ|ᵏ uₖ < ∞`, and the series converges at one point of `U`. -/
theorem hasDerivAt_tsum_E {θ : ℝ} {g g' : ℕ → ℝ → Ω → ℝ} {U : Set ℝ} {u : ℕ → ℝ}
    (hU : IsOpen U) (hU' : IsPreconnected U)
    (hg : ∀ k, ∀ y ∈ U, ∀ ω, HasDerivAt (fun z => g k z ω) (g' k y ω) y)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0,
      ∀ z ∈ Metric.ball y r, ∀ ω, |g' k z ω - g' k y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |g' k y ω| ≤ u k) (hu : Summable fun k => |θ| ^ k * u k)
    {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => θ ^ k * 𝔼.E t (g k y₀) ω) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => ∑' k, θ ^ k * 𝔼.E t (g k z) ω)
      (∑' k, θ ^ k * 𝔼.E t (g' k x) ω) x := by
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => |θ| ^ k * u k)
    (g := fun k z => θ ^ k * 𝔼.E t (g k z) ω) (g' := fun k z => θ ^ k * 𝔼.E t (g' k z) ω)
    hu hU hU' (fun k y hy => ?_) (fun k y hy => ?_) hy₀ hs hx
  · obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU y hy
    obtain ⟨L, hL0, r, hr, hL⟩ := hLip k y hy
    have hsub : Metric.ball y (min r r₁) ⊆ Metric.ball y r₁ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hsub' : Metric.ball y (min r r₁) ⊆ Metric.ball y r :=
      Metric.ball_subset_ball (min_le_left _ _)
    exact (hasDerivAt_E 𝔼 (lt_min hr hr₁) hL0 (fun z hz ω' => hg k z (hball (hsub hz)) ω')
      (fun z hz ω' => hL z (hsub' hz) ω') t ω).const_mul (θ ^ k)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k y hy) t ω)
      (pow_nonneg (abs_nonneg θ) k)

/-! ### The reset-price objective and the first-order condition (10) -/

/-- The desired (frictionless) gross markup `M = ε/(ε − 1)` (Galí (2015), p. 57). -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- The desired markup exceeds one: `M > 1` for `ε > 1` (Galí (2015), p. 57). -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  unfold markup
  rw [one_lt_div (by linarith)]
  linarith

/-- The desired markup is positive (Galí (2015), p. 57). -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  lt_trans one_pos (one_lt_markup hε)

/-- The demand constraint (9), Galí (2015), p. 56:
`Y_{t+k|t} = (P*_t / P_{t+k})^{−ε} C_{t+k}`, as a random variable. -/
noncomputable def demand (ε Pstar : ℝ) (P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => (Pstar / P ω) ^ (-ε) * C ω

/-- Demand factorises as `P*^{−ε} · P^ε C` (Galí (2015), eq. (9), p. 56). -/
theorem demand_eq {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    demand ε x P C ω = x ^ (-ε) * (P ω ^ ε * C ω) := by
  unfold demand
  rw [Real.div_rpow hx.le (hP ω).le, Real.rpow_neg (hP ω).le ε, div_inv_eq_mul]
  ring

/-- Demand is positive (Galí (2015), eq. (9), p. 56). -/
theorem demand_pos {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) : 0 < demand ε x P C ω :=
  mul_pos (Real.rpow_pos_of_pos (div_pos hx (hP ω)) _) (hC ω)

/-- The price elasticity of demand (9) is `−ε`: `dY/dP* = −ε Y / P*`
(Galí (2015), p. 56). -/
theorem hasDerivAt_demand {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    HasDerivAt (fun z => demand ε z P C ω) (-ε * demand ε x P C ω / x) x := by
  have hxP : x / P ω ≠ 0 := (div_pos hx (hP ω)).ne'
  have h1 : HasDerivAt (fun z => z / P ω) (1 / P ω) x := (hasDerivAt_id x).div_const (P ω)
  have h2 := (h1.rpow_const (p := -ε) (Or.inl hxP)).mul_const (C ω)
  refine h2.congr_deriv ?_
  unfold demand
  rw [Real.rpow_sub_one hxP]
  have := (hP ω).ne'
  field_simp

/-- Realised discounted nominal profits at horizon `k` of a firm that reset its
price to `P*` (Galí (2015), p. 56, and Appendix 3.3, p. 84):
`Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))`, where
`Q_{t,t+k} = Λ_{t,t+k}/P_{t+k}` converts nominal date-`t+k` profits into date-`t`
consumption and `Ψ_{t+k}` is the nominal cost function. -/
noncomputable def profit (ε : ℝ) (Q P C : Ω → ℝ) (Ψ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (Pstar * demand ε Pstar P C ω - Ψ ω (demand ε Pstar P C ω))

/-- **The reset-price objective** (Galí (2015), p. 56):
`∑ₖ θᵏ E_t[Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))]`, a genuine infinite
discounted sum, evaluated at the state `ω`. -/
noncomputable def objective (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) Pstar) ω

/-- The summand of (10), Galí (2015), p. 56:
`Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})`, with `Ψ'_{t+k|t} = Ψ'_{t+k}(Y_{t+k|t})`
the nominal marginal cost. -/
noncomputable def focTerm (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * demand ε Pstar P C ω * (Pstar - markup ε * dΨ ω (demand ε Pstar P C ω))

/-- The left-hand side of the optimality condition (10), Galí (2015), p. 56:
`∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})]`. -/
noncomputable def focSum (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (focTerm ε (Q k) (P k) (C k) (dΨ k) Pstar) ω

/-- The derivative of horizon-`k` profits in `P*`:
`((1 − ε)/P*) Q Y (P* − M Ψ')` (Galí (2015), p. 56). -/
noncomputable def profitDeriv (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - ε) / Pstar * focTerm ε Q P C dΨ Pstar ω

/-- **Marginal profit at one horizon** (Galí (2015), p. 56):
`d/dP* [Q (P* Y − Ψ(Y))] = ((1 − ε)/P*) Q Y (P* − M Ψ'(Y))`. -/
theorem hasDerivAt_profit {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : Ω → ℝ}
    {Ψ dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ ω) (dΨ ω y) y) (ω : Ω) :
    HasDerivAt (fun z => profit ε Q P C Ψ z ω) (profitDeriv ε Q P C dΨ x ω) x := by
  have hY := hasDerivAt_demand (ε := ε) (C := C) hx hP ω
  have hΨY := (hΨ ω _ (demand_pos hx hP hC ω)).comp x hY
  have h := (((hasDerivAt_id x).mul hY).sub hΨY).const_mul (Q ω)
  refine h.congr_deriv ?_
  unfold profitDeriv focTerm markup
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : x ≠ 0 := hx.ne'
  simp only [id]
  field_simp
  ring

/-- `E_t` of marginal profit: the constant `(1 − ε)/P*` comes out of `E_t`
(Galí (2015), p. 56). -/
theorem E_profitDeriv (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (x : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.E t (profitDeriv ε Q P C dΨ x) ω = (1 - ε) / x * 𝔼.E t (focTerm ε Q P C dΨ x) ω := by
  have : profitDeriv ε Q P C dΨ x = ((1 - ε) / x) • focTerm ε Q P C dΨ x := rfl
  rw [this, 𝔼.E_smul]
  rfl

/-- **The derivative of the reset-price objective** (Galí (2015), eq. (10), p. 56):
under explicit domination and local-Lipschitz hypotheses on marginal profits and
convergence of the objective at one price, the objective has derivative
`((1 − ε)/P*) ∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]` at every `P*` in
an open interval `U ⊆ (0, ∞)`. -/
theorem hasDerivAt_objective {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    {U : Set ℝ} (hU : IsOpen U) (hU' : IsPreconnected U) (hUpos : U ⊆ Set.Ioi 0)
    {u : ℕ → ℝ}
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (hu : Summable fun k => |θ| ^ k * u k) {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y₀) ω)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  have h := hasDerivAt_tsum_E 𝔼 (θ := θ)
    (g := fun k z => profit ε (Q k) (P k) (C k) (Ψ k) z)
    (g' := fun k z => profitDeriv ε (Q k) (P k) (C k) (dΨ k) z) hU hU'
    (fun k y hy ω' => hasDerivAt_profit hε (hUpos hy) (hP k) (hC k) (hΨ k) ω')
    hLip hdom hu hy₀ t ω hs hx
  refine h.congr_deriv ?_
  simp only [E_profitDeriv, focSum]
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- **The optimality condition (10) is necessary** (Galí (2015), eq. (10), p. 56):
if `P*` is a local maximum of the reset-price objective, then
`∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})] = 0`. -/
theorem foc_of_isLocalMax {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} {t : ℕ} {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hder : HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x)
    (hmax : IsLocalMax (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) x) :
    focSum 𝔼 θ ε Q P C dΨ t x ω = 0 := by
  have h := hmax.hasDerivAt_eq_zero hder
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- The objective is differentiable at every positive price when marginal profits
are dominated on every bounded interval `(a, b)` with `a > 0` (Galí (2015), p. 56). -/
theorem hasDerivAt_objective_of_pos {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  obtain ⟨u, hu, hdom⟩ := hloc (x / 2) (x + 1) (by positivity)
  have hxU : x ∈ Set.Ioo (x / 2) (x + 1) := ⟨by linarith, by linarith⟩
  have hUpos : Set.Ioo (x / 2) (x + 1) ⊆ Set.Ioi 0 := fun y hy => by
    simp only [Set.mem_Ioi]; linarith [hy.1]
  exact hasDerivAt_objective 𝔼 hε hP hC hΨ isOpen_Ioo isPreconnected_Ioo hUpos
    (fun k y hy => hLip k y (hUpos hy)) hdom hu hxU t ω (hs x hx) hxU

/-! ### The first-order condition characterises the optimum (convex costs) -/

/-- The `P*`-dependent core of the summand of (10) once the factor `P*^{−ε}` of
demand is taken out: `Q P^ε C (P* − M Ψ'(Y))` (Galí (2015), p. 56). -/
noncomputable def focCore (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (P ω ^ ε * C ω) * (Pstar - markup ε * dΨ ω (demand ε Pstar P C ω))

/-- The summand of (10) is `P*^{−ε}` times its core (Galí (2015), p. 56). -/
theorem focTerm_eq {ε x : ℝ} (hx : 0 < x) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) : focTerm ε Q P C dΨ x = x ^ (-ε) • focCore ε Q P C dΨ x := by
  funext ω
  simp only [focTerm, focCore, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hP ω]
  ring

/-- With convex costs (nondecreasing marginal cost), the core of (10) increases in
`P*` at least at rate `Q P^ε C`: a higher price lowers demand and hence marginal
cost (Galí (2015), p. 56). -/
theorem focCore_sub_ge {ε : ℝ} (hε : 1 < ε) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (ω : Ω) :
    (y - x) * (Q ω * (P ω ^ ε * C ω)) ≤ focCore ε Q P C dΨ y ω - focCore ε Q P C dΨ x ω := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hK : 0 < P ω ^ ε * C ω := mul_pos (Real.rpow_pos_of_pos (hP ω) ε) (hC ω)
  have hdem : demand ε y P C ω ≤ demand ε x P C ω := by
    rw [demand_eq hx hP ω, demand_eq hy hP ω]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
      hK.le
  have hd : dΨ ω (demand ε y P C ω) ≤ dΨ ω (demand ε x P C ω) :=
    hconv ω (demand_pos hy hP hC ω) (demand_pos hx hP hC ω) hdem
  have key : focCore ε Q P C dΨ y ω - focCore ε Q P C dΨ x ω
        - (y - x) * (Q ω * (P ω ^ ε * C ω))
      = Q ω * (P ω ^ ε * C ω) *
        (markup ε * (dΨ ω (demand ε x P C ω) - dΨ ω (demand ε y P C ω))) := by
    unfold focCore; ring
  have h0 : 0 ≤ Q ω * (P ω ^ ε * C ω) *
      (markup ε * (dΨ ω (demand ε x P C ω) - dΨ ω (demand ε y P C ω))) :=
    mul_nonneg (mul_pos (hQ ω) hK).le
      (mul_nonneg (markup_pos hε).le (sub_nonneg.mpr hd))
  linarith

/-- `E_t` version of `focCore_sub_ge` (Galí (2015), p. 56). -/
theorem E_focCore_le {ε : ℝ} (hε : 1 < ε) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (t : ℕ) (ω : Ω) :
    (y - x) * 𝔼.E t (fun ω' => Q ω' * (P ω' ^ ε * C ω')) ω + 𝔼.E t (focCore ε Q P C dΨ x) ω
      ≤ 𝔼.E t (focCore ε Q P C dΨ y) ω := by
  have hle : (y - x) • (fun ω' => Q ω' * (P ω' ^ ε * C ω')) + focCore ε Q P C dΨ x
      ≤ focCore ε Q P C dΨ y := fun ω' => by
    have := focCore_sub_ge hε hQ hP hC hconv hx hxy ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have := 𝔼.mono t hle ω
  simpa [map_add, map_smul] using this

/-- The expected-revenue weight `E_t[Q P^ε C]` is nonnegative (Galí (2015), p. 56). -/
theorem E_weight_nonneg {ε : ℝ} {Q P C : Ω → ℝ} (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (t : ℕ) (ω : Ω) :
    0 ≤ 𝔼.E t (fun ω' => Q ω' * (P ω' ^ ε * C ω')) ω := by
  have h0 : (0 : Ω → ℝ) ≤ fun ω' => Q ω' * (P ω' ^ ε * C ω') := fun ω' =>
    (mul_pos (hQ ω') (mul_pos (Real.rpow_pos_of_pos (hP ω') ε) (hC ω'))).le
  simpa using 𝔼.mono t h0 ω

/-- `E_t` of the summand of (10) in terms of marginal profit
(Galí (2015), p. 56). -/
theorem E_focCore_eq {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : Ω → ℝ}
    (dΨ : Ω → ℝ → ℝ) (hP : ∀ ω, 0 < P ω) (t : ℕ) (ω : Ω) :
    𝔼.E t (focCore ε Q P C dΨ x) ω
      = ((1 - ε) / x * x ^ (-ε))⁻¹ * 𝔼.E t (profitDeriv ε Q P C dΨ x) ω := by
  rw [E_profitDeriv, focTerm_eq hx dΨ hP, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h2 : x ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have h3 : 1 - ε ≠ 0 := by linarith
  field_simp

/-- **The optimality condition (10) characterises the optimal reset price**
(Galí (2015), eq. (10), p. 56). With convex costs (nondecreasing marginal cost),
positive discount factors, prices and demand, and a positive current-period
revenue weight, a positive price `P*` maximises the reset-price objective over
all positive prices if and only if it satisfies (10); such a maximiser is then
the strict, hence unique, maximiser. -/
theorem isMaxOn_iff_foc {θ ε : ℝ} (hε : 1 < ε) (hθ : 0 ≤ θ) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ k ω, 0 < Q k ω) (hP : ∀ k ω, 0 < P k ω)
    (hC : ∀ k ω, 0 < C k ω) (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hconv : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0))
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω)
    (hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω)
    {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 θ ε Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 θ ε Q P C Ψ t y ω < objective 𝔼 θ ε Q P C Ψ t x ω) := by
  set V := fun z => objective 𝔼 θ ε Q P C Ψ t z ω with hV
  set H : ℝ → ℝ := fun z => ∑' k, θ ^ k * 𝔼.E t (focCore ε (Q k) (P k) (C k) (dΨ k) z) ω
    with hH
  have hder : ∀ z, 0 < z → HasDerivAt V ((1 - ε) / z * focSum 𝔼 θ ε Q P C dΨ t z ω) z :=
    fun z hz => hasDerivAt_objective_of_pos 𝔼 hε hP hC hΨ hLip hloc t ω hs hz
  -- summability of the core series
  have hsum : ∀ z, 0 < z →
      Summable fun k => θ ^ k * 𝔼.E t (focCore ε (Q k) (P k) (C k) (dΨ k) z) ω := by
    intro z hz
    obtain ⟨u, hu, hdom⟩ := hloc (z / 2) (z + 1) (by positivity)
    have hzU : z ∈ Set.Ioo (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
    have hs' : Summable fun k =>
        θ ^ k * 𝔼.E t (profitDeriv ε (Q k) (P k) (C k) (dΨ k) z) ω := by
      refine Summable.of_norm_bounded hu fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k z hzU) t ω)
        (pow_nonneg (abs_nonneg θ) k)
    refine (hs'.mul_left ((1 - ε) / z * z ^ (-ε))⁻¹).congr fun k => ?_
    rw [E_focCore_eq 𝔼 hε hz _ (hP k)]
    ring
  -- (10) in terms of the core series
  have hfocH : ∀ z, 0 < z → focSum 𝔼 θ ε Q P C dΨ t z ω = z ^ (-ε) * H z := by
    intro z hz
    simp only [focSum, hH, focTerm_eq hz _ (hP _), 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  -- the core series is strictly increasing
  have hHmono : ∀ z y, 0 < z → z < y → H z < H y := by
    intro z y hz hzy
    refine Summable.tsum_lt_tsum (i := 0) (fun k => ?_) ?_ (hsum z hz)
      (hsum y (hz.trans hzy))
    · have h1 := E_focCore_le 𝔼 hε (hQ k) (hP k) (hC k) (hconv k) hz hzy.le t ω
      have h2 := E_weight_nonneg 𝔼 (ε := ε) (hQ k) (hP k) (hC k) t ω
      have h3 : 0 ≤ (y - z) * 𝔼.E t (fun ω' => Q k ω' * (P k ω' ^ ε * C k ω')) ω :=
        mul_nonneg (by linarith) h2
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hθ k)
    · have h1 := E_focCore_le 𝔼 hε (hQ 0) (hP 0) (hC 0) (hconv 0) hz hzy.le t ω
      have h3 : 0 < (y - z) * 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω :=
        mul_pos (by linarith) hpos
      simp only [pow_zero, one_mul]
      linarith
  have hcoef : ∀ z, 0 < z → (1 - ε) / z < 0 := fun z hz => div_neg_of_neg_of_pos (by linarith) hz
  -- the strict-maximum part
  have hstrict : focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x → V y < V x := by
    intro hfoc
    have hHx : H x = 0 := by
      have := hfocH x hx
      rw [hfoc] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (Real.rpow_pos_of_pos hx _).ne'
    have hcont : ∀ z, 0 < z → ContinuousAt V z := fun z hz => (hder z hz).continuousAt
    have hinc : StrictMonoOn V (Set.Ioc 0 x) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 x)
        (fun z hz => (hcont z hz.1).continuousWithinAt) fun z hz => ?_
      rw [interior_Ioc] at hz
      rw [(hder z hz.1).deriv, hfocH z hz.1]
      have hHz : H z < 0 := hHx ▸ hHmono z x hz.1 hz.2
      have := mul_neg_of_neg_of_pos hHz (Real.rpow_pos_of_pos hz.1 (-ε))
      nlinarith [hcoef z hz.1]
    have hdec : StrictAntiOn V (Set.Ici x) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici x)
        (fun z hz => (hcont z (lt_of_lt_of_le hx hz)).continuousWithinAt) fun z hz => ?_
      rw [interior_Ici] at hz
      have hz0 : 0 < z := hx.trans hz
      rw [(hder z hz0).deriv, hfocH z hz0]
      have hHz : 0 < H z := hHx ▸ hHmono x z hx hz
      have := mul_pos (Real.rpow_pos_of_pos hz0 (-ε)) hHz
      nlinarith [hcoef z hz0]
    intro y hy hyx
    rcases lt_or_gt_of_ne hyx with h | h
    · exact hinc ⟨hy, h.le⟩ ⟨hx, le_rfl⟩ h
    · exact hdec (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h
  refine ⟨⟨fun hmax => ?_, fun hfoc => ?_⟩, hstrict⟩
  · exact foc_of_isLocalMax 𝔼 hε hx (hder x hx) (hmax.isLocalMax (Ioi_mem_nhds hx))
  · intro y hy
    rcases eq_or_ne y x with h | h
    · rw [h]; exact le_refl (V x)
    · exact (hstrict hfoc y hy h).le

/-! ### Flexible prices and the zero-inflation steady state -/

/-- With flexible prices (`θ = 0`) the objective reduces to current expected
profits (Galí (2015), p. 57). -/
theorem objective_flexible (ε : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    objective 𝔼 0 ε Q P C Ψ t z ω = 𝔼.E t (profit ε (Q 0) (P 0) (C 0) (Ψ 0) z) ω := by
  unfold objective
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- With flexible prices (`θ = 0`) condition (10) involves only the current period
(Galí (2015), p. 57). -/
theorem focSum_flexible (ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    focSum 𝔼 0 ε Q P C dΨ t z ω = 𝔼.E t (focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) z) ω := by
  unfold focSum
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- **Flexible-price pricing rule** (Galí (2015), p. 57): with `θ = 0` and the
current-period variables known at `t`, condition (10) holds if and only if
`P*_t = M Ψ'_{t|t}`, the frictionless markup over marginal cost. -/
theorem flexible_foc_iff {ε x : ℝ} (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    {t : ℕ} (hknown : 𝔼.E t (focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) x)
      = focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) x) (ω : Ω) :
    focSum 𝔼 0 ε Q P C dΨ t x ω = 0 ↔ x = markup ε * dΨ 0 ω (demand ε x (P 0) (C 0) ω) := by
  rw [focSum_flexible, hknown]
  unfold focTerm
  have h := mul_pos (hQ ω) (demand_pos (ε := ε) hx hP hC ω)
  constructor
  · intro h0
    have := (mul_eq_zero.mp h0).resolve_left h.ne'
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero]

/-- **Flexible-price optimum** (Galí (2015), p. 57): with `θ = 0`, if the
current-period profit function is known at `t` and `P*` is a local maximum of
the objective, then `P* = M Ψ'_{t|t}`. -/
theorem flexible_price_optimum {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ 0 ω) (dΨ 0 ω y) y) {t : ℕ}
    (hknown : ∀ z, 𝔼.E t (profit ε (Q 0) (P 0) (C 0) (Ψ 0) z)
      = profit ε (Q 0) (P 0) (C 0) (Ψ 0) z) {ω : Ω}
    (hmax : IsLocalMax (fun z => objective 𝔼 0 ε Q P C Ψ t z ω) x) :
    x = markup ε * dΨ 0 ω (demand ε x (P 0) (C 0) ω) := by
  have hfun : (fun z => objective 𝔼 0 ε Q P C Ψ t z ω)
      = fun z => profit ε (Q 0) (P 0) (C 0) (Ψ 0) z ω := by
    funext z; rw [objective_flexible, hknown]
  rw [hfun] at hmax
  have h0 := hmax.hasDerivAt_eq_zero (hasDerivAt_profit hε hx hP hC hΨ ω)
  unfold profitDeriv focTerm at h0
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h := mul_pos (hQ ω) (demand_pos (ε := ε) hx hP hC ω)
  have h1 := (mul_eq_zero.mp h0).resolve_left hc
  have := (mul_eq_zero.mp h1).resolve_left h.ne'
  linarith

/-- **The zero-inflation steady state** (Galí (2015), p. 57): with constant price
level `P`, consumption `C`, discount factors `Λ_{t,t+k} = βᵏ` and marginal cost `Ψ`
at the steady-state output, condition (10) at `P* = P` holds if and only if
`P = M Ψ`: actual markups equal the frictionless markup. -/
theorem steadyState_foc_iff {β θ ε Pbar Cbar Ψbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hP : 0 < Pbar) (hC : 0 < Cbar) {dΨ : ℕ → Ω → ℝ → ℝ}
    (hdΨ : ∀ k ω, dΨ k ω Cbar = Ψbar) (t : ℕ) (ω : Ω) :
    focSum 𝔼 θ ε (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t Pbar ω = 0
      ↔ Pbar = markup ε * Ψbar := by
  have hY : ∀ ω' : Ω, demand ε Pbar (fun _ => Pbar) (fun _ => Cbar) ω' = Cbar := by
    intro ω'; simp [demand, div_self hP.ne']
  have hterm : ∀ k, focTerm ε (fun _ => β ^ k / Pbar) (fun _ => Pbar) (fun _ => Cbar) (dΨ k) Pbar
      = fun _ => β ^ k / Pbar * Cbar * (Pbar - markup ε * Ψbar) := by
    intro k; funext ω'
    simp only [focTerm, hY, hdΨ]
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  have hsum : focSum 𝔼 θ ε (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t
      Pbar ω = (1 - β * θ)⁻¹ * (Cbar / Pbar * (Pbar - markup ε * Ψbar)) := by
    simp only [focSum, hterm, 𝔼.const]
    rw [← tsum_geometric_of_lt_one hβθ0 hβθ1, ← tsum_mul_right]
    congr 1; funext k
    rw [mul_pow]; field_simp
  rw [hsum]
  have h1 : (1 - β * θ)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have h2 : Cbar / Pbar ≠ 0 := (div_pos hC hP).ne'
  constructor
  · intro h0
    have := (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h1)).resolve_left h2
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero, mul_zero]

/-! ### The log-linear pricing rule (11) as the exact linearisation of (10) -/

/-- The log desired markup `μ = log M` (Galí (2015), p. 57). -/
noncomputable def logMarkup (ε : ℝ) : ℝ := Real.log (markup ε)

/-- The left-hand side of (10) written in terms of the weights
`wₖ = Λ_{t,t+k} Y_{t+k|t} / P_{t+k}` and the nominal marginal costs
`Ψ_{t+k|t}` (Galí (2015), eq. (10), p. 56):
`∑ₖ θᵏ E_t[wₖ (P* − M Ψ_{t+k|t})]`. -/
noncomputable def focLHS (θ ε : ℝ) (w : ℕ → Ω → ℝ) (Pstar : ℝ) (Ψm : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (fun ω' => w k ω' * (Pstar - markup ε * Ψm k ω')) ω

/-- The reset-price condition `focSum` is (10) with weights `Q_{t,t+k} Y_{t+k|t}`
and marginal costs `Ψ'_{t+k}(Y_{t+k|t})` (Galí (2015), p. 56). -/
theorem focSum_eq_focLHS (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (x : ℝ) :
    focSum 𝔼 θ ε Q P C dΨ t x = focLHS 𝔼 θ ε (fun k ω => Q k ω * demand ε x (P k) (C k) ω) x
      (fun k ω => dΨ k ω (demand ε x (P k) (C k) ω)) t := rfl

/-- Differentiating `E_t[exp(s g)]` in `s` for a bounded random variable `g`:
the derivative is `E_t[g exp(s g)]`. -/
theorem hasDerivAt_E_exp {g : Ω → ℝ} {B : ℝ} (hg : ∀ ω, |g ω| ≤ B) (t : ℕ) (ω : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ω' => Real.exp (r * g ω')) ω)
      (𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω) s := by
  refine hasDerivAt_E_of_remainder 𝔼 (g := fun r ω' => Real.exp (r * g ω'))
    (δ := 1 / (|B| + 1)) (C := Real.exp (|s| * |B|) * B ^ 2) (by positivity)
    (fun h hh ω' => ?_) t ω
  have hgB : |g ω'| ≤ |B| := (hg ω').trans (le_abs_self B)
  have hhB : |h| * |B| ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hh
    nlinarith [abs_nonneg B, abs_nonneg h]
  have hhg : |h * g ω'| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hgB (abs_nonneg h)).trans hhB
  have hexp := Real.abs_exp_sub_one_sub_id_le hhg
  have key : Real.exp ((s + h) * g ω') - Real.exp (s * g ω') - h * (g ω' * Real.exp (s * g ω'))
      = Real.exp (s * g ω') * (Real.exp (h * g ω') - 1 - h * g ω') := by
    rw [add_mul, Real.exp_add]; ring
  rw [key, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp (s * g ω') ≤ Real.exp (|s| * |B|) := by
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hgB (abs_nonneg s)
  have e2 : (h * g ω') ^ 2 ≤ B ^ 2 * h ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr hgB) (sq_nonneg h)
  calc Real.exp (s * g ω') * |Real.exp (h * g ω') - 1 - h * g ω'|
      ≤ Real.exp (|s| * |B|) * (B ^ 2 * h ^ 2) :=
        mul_le_mul e1 (hexp.trans e2) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|s| * |B|) * B ^ 2 * h ^ 2 := by ring

/-- **Exact linearisation of (10) at the zero-inflation steady state**
(Galí (2015), p. 57). Perturb the steady state along an arbitrary bounded
direction: log weights `log wₖ = log(βᵏ w̄) + s ŵₖ` (stochastic discount factor,
demand and price level combined), log reset price `p* = p̄ + s x̂`, and log
marginal costs `ψ_{t+k|t} = ψ̄ + s ψ̂ₖ`, where the steady state satisfies
`p̄ = μ + ψ̄` (`P = M Ψ`). Then the left-hand side of (10) has derivative
`w̄ e^{p̄} ∑ₖ (βθ)ᵏ (x̂ − E_t ψ̂ₖ)` at `s = 0`. The weight deviations `ŵ` drop out:
to first order only prices and marginal costs matter. -/
theorem hasDerivAt_focLHS_path {θ β ε wbar pbar xhat B : ℝ} (hε : 1 < ε) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {what ψhat : ℕ → Ω → ℝ}
    (hw : ∀ k ω, |what k ω| ≤ B) (hψ : ∀ k ω, |ψhat k ω| ≤ B) (hxB : |xhat| ≤ B)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focLHS 𝔼 θ ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      (wbar * Real.exp pbar * ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω)) 0 := by
  set c := wbar * Real.exp pbar with hc
  set a : ℕ → Ω → ℝ := fun k ω' => what k ω' + xhat with ha
  set b : ℕ → Ω → ℝ := fun k ω' => what k ω' + ψhat k ω' with hb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hxB
  have haB : ∀ k ω', |a k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω'])
  have hbB : ∀ k ω', |b k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω', hψ k ω'])
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  -- rewrite the path of (10) through exponentials of `s a` and `s b`
  have hfun : (fun s => focLHS 𝔼 θ ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      = fun s => ∑' k, (β * θ) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)) := by
    funext s
    unfold focLHS
    congr 1; funext k
    have hint : (fun ω' => β ^ k * wbar * Real.exp (s * what k ω') *
          (Real.exp (pbar + s * xhat)
            - markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')))
        = (β ^ k * c) • ((fun ω' => Real.exp (s * a k ω'))
            - fun ω' => Real.exp (s * b k ω')) := by
      funext ω'
      have hM : markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')
          = Real.exp (pbar + s * ψhat k ω') := by
        rw [logMarkup, show pbar - Real.log (markup ε) + s * ψhat k ω'
            = (pbar + s * ψhat k ω') + -Real.log (markup ε) by ring, Real.exp_add,
          Real.exp_neg, Real.exp_log (markup_pos hε)]
        have := (markup_pos hε).ne'
        field_simp
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hM]
      simp only [ha, hb, hc, mul_add, Real.exp_add]
      ring
    rw [hint, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow]
    ring
  rw [hfun]
  -- term-by-term differentiation on `(-1, 1)`
  have hbd : ∀ (g : Ω → ℝ), (∀ ω', |g ω'| ≤ 2 * B) → ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
      |𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω| ≤ 2 * B * Real.exp (2 * B) := by
    intro g hg s hs
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hg ω') ?_ (Real.exp_pos _).le (by linarith)
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ 1 * (2 * B) := mul_le_mul hs1 (hg ω') (abs_nonneg _) zero_le_one
      _ = 2 * B := one_mul _
  have hD := hasDerivAt_tsum_of_isPreconnected
    (u := fun k => (β * θ) ^ k * (|c| * (2 * (2 * B * Real.exp (2 * B)))))
    (g := fun k s => (β * θ) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)))
    (g' := fun k s => (β * θ) ^ k * (c * (𝔼.E t (fun ω' => a k ω' * Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => b k ω' * Real.exp (s * b k ω')) ω)))
    (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    ((summable_geometric_of_lt_one hβθ0 hβθ1).mul_right _) isOpen_Ioo isPreconnected_Ioo
    (fun k s _ => (((hasDerivAt_E_exp 𝔼 (haB k) t ω s).sub
      (hasDerivAt_E_exp 𝔼 (hbB k) t ω s)).const_mul c).const_mul _)
    (fun k s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβθ0 k), abs_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg c))
        (pow_nonneg hβθ0 k)
      refine (abs_sub _ _).trans ?_
      linarith [hbd _ (haB k) s hs, hbd _ (hbB k) s hs])
    ⟨by norm_num, by norm_num⟩
    (by simp)
    ⟨by norm_num, by norm_num⟩
  refine hD.congr_deriv ?_
  rw [← tsum_mul_left]
  congr 1; funext k
  have hab : (fun ω' => a k ω' * Real.exp (0 * a k ω'))
      - (fun ω' => b k ω' * Real.exp (0 * b k ω')) = (fun _ => xhat) - ψhat k := by
    funext ω'; simp [ha, hb]
  rw [← Pi.sub_apply (𝔼.E t _), ← map_sub, hab, map_sub, 𝔼.const]
  simp only [Pi.sub_apply]
  ring

/-- **The log-linear pricing rule (11)** (Galí (2015), eq. (11), p. 57). The
first-order term of (10) at the zero-inflation steady state vanishes if and only if
`p*_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k|t}`, where `p*_t = p̄ + x̂` and
`ψ_{t+k|t} = ψ̄ + ψ̂ₖ` with `ψ̄ = p̄ − μ`. -/
theorem eq11_iff {θ β ε wbar pbar xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hwbar : 0 < wbar) {ψhat : ℕ → Ω → ℝ} (hψ : ∀ k ω, |ψhat k ω| ≤ B)
    (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup ε + (1 - β * θ) *
        ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω := by
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  have hβθ : |β * θ| < 1 := by rwa [abs_of_nonneg hβθ0]
  have hg := summable_geometric_of_lt_one hβθ0 hβθ1
  have hT := summable_geometric_bounded hβθ (fun k ω' => 𝔼.abs_E_le (hψ k) t ω') ω
  set T := ∑' k, (β * θ) ^ k * 𝔼.E t (ψhat k) ω with hTdef
  have h1 : ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = xhat * (1 - β * θ)⁻¹ - T := by
    simp_rw [mul_sub]
    rw [Summable.tsum_sub (hg.mul_right xhat) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβθ0 hβθ1]
    ring
  have h2 : ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
      = (pbar - logMarkup ε) * (1 - β * θ)⁻¹ + T := by
    have : ∀ k, 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
        = (pbar - logMarkup ε) + 𝔼.E t (ψhat k) ω := by
      intro k
      have hf : (fun ω' => (pbar - logMarkup ε) + ψhat k ω')
          = (fun _ => pbar - logMarkup ε) + ψhat k := rfl
      rw [hf, map_add, 𝔼.const]; rfl
    simp_rw [this, mul_add]
    rw [Summable.tsum_add (hg.mul_right _) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβθ0 hβθ1, mul_comm]
  rw [h1, h2]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  have hd : 1 - β * θ ≠ 0 := by linarith
  constructor
  · intro h
    have h3 := (mul_eq_zero.mp h).resolve_left hc
    field_simp at h3 ⊢
    linarith
  · intro h
    have h3 : xhat * (1 - β * θ)⁻¹ - T = 0 := by
      field_simp at h ⊢
      linarith
    rw [h3, mul_zero]

/-- (11) in terms of real marginal cost `mc_{t+k|t} = ψ_{t+k|t} − p_{t+k}`
(Galí (2015), p. 57 and fn. 4, p. 61):
`μ + (1 − βθ)∑(βθ)ᵏ E_t ψ_{t+k|t} = μ + (1 − βθ)∑(βθ)ᵏ E_t[mc_{t+k|t} + p_{t+k}]`. -/
theorem eq11_real_marginal_cost (θ β ε : ℝ) (ψ mc p : ℕ → Ω → ℝ)
    (h : ∀ k, ψ k = mc k + p k) (t : ℕ) (ω : Ω) :
    logMarkup ε + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ k) ω
      = logMarkup ε + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (mc k + p k) ω := by
  simp_rw [h]

/-! ### Recursive form of the pricing rule -/

/-- The normalised forward sum `(1 − a) ∑ₖ aᵏ E_t x_{t+k}` satisfies
`S_t = a E_t S_{t+1} + (1 − a) x_t` (Galí (2015), eq. (16), p. 60). -/
theorem normForward_rec {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) (t : ℕ) :
    (1 - a) • forwardSum 𝔼 a x t
      = a • 𝔼.E t ((1 - a) • forwardSum 𝔼 a x (t + 1)) + (1 - a) • x t := by
  rw [forwardSum_rec 𝔼 ha hx hxa t, 𝔼.E_smul, smul_add, smul_smul, smul_smul,
    mul_comm (1 - a) a, add_comm]

/-- **Uniqueness of the recursive pricing rule** (Galí (2015), eq. (16), p. 60):
the normalised forward sum is the only bounded process with
`S_t = a E_t S_{t+1} + (1 − a) x_t`. -/
theorem normForward_unique {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) {S : ℕ → Ω → ℝ} (hS : BoundedProc S)
    (hrec : ∀ t, S t = a • 𝔼.E t (S (t + 1)) + (1 - a) • x t) :
    S = fun t => (1 - a) • forwardSum 𝔼 a x t := by
  refine 𝔼.forward_unique ha (u := fun t => (1 - a) • x t) hrec (fun t => ?_) hS ?_
  · exact normForward_rec 𝔼 ha hx hxa t
  · obtain ⟨B, hB⟩ := forwardSum_bounded 𝔼 ha ⟨M, hx⟩
    refine ⟨|1 - a| * B, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)

/-- A constant passes through the normalised forward sum:
`(1 − a) ∑ₖ aᵏ E_t[c + y_{t+k}] = c + (1 − a) ∑ₖ aᵏ E_t y_{t+k}`
(Galí (2015), eq. (11), p. 57: the markup `μ` in front of the sum). -/
theorem normForward_const_add {a : ℝ} (ha : |a| < 1) (c : ℝ) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ t ω, |y t ω| ≤ M) (t : ℕ) :
    (1 - a) • forwardSum 𝔼 a (fun s => (fun _ => c) + y s) t
      = (fun _ => c) + (1 - a) • forwardSum 𝔼 a y t := by
  funext ω
  have ha1 : a < 1 := (le_abs_self a).trans_lt ha
  have hd : 1 - a ≠ 0 := by linarith
  have hg : Summable fun k => a ^ k :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])
  have hT := summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hy t (t + k) ω') ω
  simp only [forwardSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, 𝔼.const]
  simp_rw [mul_add]
  rw [Summable.tsum_add (hg.mul_right c) hT, tsum_mul_right,
    tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])]
  field_simp

/-- **Recursive form of the pricing rule under constant returns** (Galí (2015),
eqs. (11) and (16), pp. 57–60): when firm-specific marginal cost equals the
economy-wide `ψ_{t+k}` (`α = 0`), the reset price
`p*_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}` satisfies
`p*_t = βθ E_t p*_{t+1} + (1 − βθ)(μ + ψ_t)` and is its only bounded solution. -/
theorem resetPrice_recursive {a μ : ℝ} (ha : |a| < 1) {ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hψ : ∀ t ω, |ψ t ω| ≤ M) (hψa : 𝔼.Adapted ψ) :
    (∀ t, (fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ t
        = a • 𝔼.E t ((fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ (t + 1))
          + (1 - a) • ((fun _ => μ) + ψ t)) ∧
    ∀ S : ℕ → Ω → ℝ, BoundedProc S →
      (∀ t, S t = a • 𝔼.E t (S (t + 1)) + (1 - a) • ((fun _ => μ) + ψ t)) →
      S = fun t => (fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ t := by
  set x : ℕ → Ω → ℝ := fun s => (fun _ => μ) + ψ s with hx
  have hxb : ∀ t ω, |x t ω| ≤ |μ| + M := fun t ω =>
    (abs_add_le _ _).trans (by simp only [add_le_add_iff_left, hψ])
  have hxa : 𝔼.Adapted x := fun t => by
    simp only [hx, map_add, 𝔼.const, hψa t]
  have heq : ∀ t, (fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ t
      = (1 - a) • forwardSum 𝔼 a x t := fun t =>
    (normForward_const_add 𝔼 ha μ hψ t).symm
  refine ⟨fun t => ?_, fun S hS hrec => ?_⟩
  · rw [heq t, heq (t + 1)]
    exact normForward_rec 𝔼 ha hxb hxa t
  · rw [normForward_unique 𝔼 ha hxb hxa hS hrec]
    funext t
    exact (heq t).symm

/-! ### Appendix 3.3: the firm's objective function -/

/-- **Reset-history probabilities** (Galí (2015), Appendix 3.3, eq. (37), p. 84):
a price reset at `t` is still in force at `t + k` with probability `θᵏ`, and was
last reset at `t + h` (`1 ≤ h ≤ k`) with probability `(1 − θ) θ^{k−h}`; these
probabilities sum to one. -/
theorem reset_prob_sum (θ : ℝ) (k : ℕ) :
    θ ^ k + (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) = 1 := by
  have hr : ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) = ∑ h ∈ Finset.range k, θ ^ h := by
    rw [← Finset.sum_range_reflect (fun j => θ ^ j) k]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Nat.sub_sub, add_comm 1 h]
  rw [hr]
  linear_combination -(geom_sum_mul θ k)

/-- The value of a firm resetting its price at `t` (Galí (2015), Appendix 3.3,
eq. (37), pp. 84–85): at horizon `k` the expected real dividend is
`θᵏ E_t[Xₖ(P*)]` (price still `P*`) plus `(1 − θ) ∑_{h=1}^{k} θ^{k−h} E_t[Z_{k,h}]`
(price last reset at `t + h`), and the latter does not depend on `P*`. -/
noncomputable def firmValue (θ : ℝ) (X : ℕ → ℝ → Ω → ℝ) (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, (θ ^ k * 𝔼.E t (X k Pstar) ω
    + (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω)

/-- The `P*`-independent term `Υ_t` of the firm's value (Galí (2015), p. 85). -/
noncomputable def resetValueRest (θ : ℝ) (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω

/-- **Decomposition of the firm's value** (Galí (2015), p. 85):
`V_{t|t}(P*) = ∑ₖ θᵏ E_t[Xₖ(P*)] + Υ_t`, with `Υ_t` independent of `P*`. -/
theorem firmValue_eq (θ : ℝ) (X : ℕ → ℝ → Ω → ℝ) (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ) (Pstar : ℝ)
    (ω : Ω) (hX : Summable fun k => θ ^ k * 𝔼.E t (X k Pstar) ω)
    (hZ : Summable fun k =>
      (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω) :
    firmValue 𝔼 θ X Z t Pstar ω
      = ∑' k, θ ^ k * 𝔼.E t (X k Pstar) ω + resetValueRest 𝔼 θ Z t ω :=
  hX.tsum_add hZ

/-- **The text's objective is the firm's value up to a constant** (Galí (2015),
p. 56 and Appendix 3.3, p. 85): with `Xₖ` the discounted profits of a firm still
charging `P*`, a price maximises the firm's value over a set of prices if and only
if it maximises the reset-price objective. -/
theorem isMaxOn_firmValue_iff {θ ε : ℝ} {Q P C : ℕ → Ω → ℝ} {Ψ : ℕ → Ω → ℝ → ℝ}
    (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (S : Set ℝ) (x : ℝ) (hx : x ∈ S)
    (hX : ∀ z ∈ S, Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) z) ω)
    (hZ : Summable fun k =>
      (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω) :
    IsMaxOn (fun z => firmValue 𝔼 θ (fun k z => profit ε (Q k) (P k) (C k) (Ψ k) z) Z t z ω)
        S x ↔
      IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) S x := by
  simp only [isMaxOn_iff]
  refine forall₂_congr fun z hz => ?_
  rw [firmValue_eq 𝔼 θ _ Z t z ω (hX z hz) hZ, firmValue_eq 𝔼 θ _ Z t x ω (hX x hx) hZ,
    add_le_add_iff_right]
  rfl

/-! ### Regularity of the reset-price problem from model primitives -/

/-- **Primitive assumptions on the reset-price problem** (Galí (2015), p. 56): Calvo
`θ ≥ 0` and a discount bound `β ≥ 0` with `θβ < 1`; `ε > 1`; nominal discount factors
`0 < Q_{t,t+k} ≤ Q̄ βᵏ`; price levels and consumption in `[m, M̄]` with `m > 0`; a
nominal cost function `Ψ` twice differentiable at positive output, with `Ψ`, `Ψ'`,
`Ψ''` bounded, uniformly in the horizon and the state, on every compact range of
positive output. -/
def Primitives (θ β ε Qb m Mx : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ) :
    Prop :=
  0 ≤ θ ∧ 0 ≤ β ∧ θ * β < 1 ∧ 1 < ε ∧ 0 < m ∧
  (∀ k ω, 0 < Q k ω ∧ Q k ω ≤ Qb * β ^ k) ∧
  (∀ k ω, m ≤ P k ω ∧ P k ω ≤ Mx) ∧ (∀ k ω, m ≤ C k ω ∧ C k ω ≤ Mx) ∧
  (∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y) ∧
  (∀ k ω y, 0 < y → HasDerivAt (dΨ k ω) (d2Ψ k ω y) y) ∧
  (∀ y₁ y₂, 0 < y₁ → ∃ K, ∀ k ω y, y₁ ≤ y → y ≤ y₂ →
    |Ψ k ω y| ≤ K ∧ |dΨ k ω y| ≤ K ∧ |d2Ψ k ω y| ≤ K)

/-- Bounds on the demand shifter `P^ε C ∈ [m^ε m, M̄^ε M̄]` (Galí (2015), eq. (9),
p. 56). -/
theorem weight_bounds {ε m Mx : ℝ} (hε : 0 ≤ ε) (hm : 0 < m) {P C : Ω → ℝ}
    (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx) (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    m ^ ε * m ≤ P ω ^ ε * C ω ∧ P ω ^ ε * C ω ≤ Mx ^ ε * Mx := by
  have hP0 : 0 ≤ P ω := hm.le.trans (hP ω).1
  have hC0 : 0 ≤ C ω := hm.le.trans (hC ω).1
  refine ⟨mul_le_mul (Real.rpow_le_rpow hm.le (hP ω).1 hε) (hC ω).1 hm.le
    (Real.rpow_nonneg hP0 _), mul_le_mul (Real.rpow_le_rpow hP0 (hP ω).2 hε) (hC ω).2 hC0
    (Real.rpow_nonneg (hP0.trans (hP ω).2) _)⟩

/-- **Demand stays in a compact range of positive output** when the reset price
ranges over `[lo, hi] ⊂ (0, ∞)` (Galí (2015), eq. (9), p. 56). -/
theorem demand_bounds {ε m Mx lo hi z : ℝ} (hε : 0 ≤ ε) (hm : 0 < m) (hlo : 0 < lo)
    (hz1 : lo ≤ z) (hz2 : z ≤ hi) {P C : Ω → ℝ} (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx)
    (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    hi ^ (-ε) * (m ^ ε * m) ≤ demand ε z P C ω ∧
      demand ε z P C ω ≤ lo ^ (-ε) * (Mx ^ ε * Mx) := by
  have hz : 0 < z := hlo.trans_le hz1
  have hPpos : ∀ ω, 0 < P ω := fun ω => hm.trans_le (hP ω).1
  obtain ⟨hw1, hw2⟩ := weight_bounds hε hm hP hC ω
  rw [demand_eq hz hPpos ω]
  have hm0 : 0 ≤ m ^ ε * m := by positivity
  exact ⟨mul_le_mul (Real.rpow_le_rpow_of_nonpos hz hz2 (by linarith)) hw1 hm0
      (Real.rpow_nonneg hz.le _),
    mul_le_mul (Real.rpow_le_rpow_of_nonpos hlo hz1 (by linarith)) hw2 (hm0.trans hw1)
      (Real.rpow_nonneg hlo.le _)⟩

/-- Marginal profit in factored form:
`((1 − ε)/P*) Q Y (P* − M Ψ') = (1 − ε) Q P^ε C (P*^{−ε} − M P*^{−ε−1} Ψ')`
(Galí (2015), p. 56). -/
theorem profitDeriv_eq {ε z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    profitDeriv ε Q P C dΨ z ω = (1 - ε) * Q ω * (P ω ^ ε * C ω) *
      (z ^ (-ε) - markup ε * (z ^ (-ε - 1) * dΨ ω (demand ε z P C ω))) := by
  unfold profitDeriv focTerm
  rw [demand_eq hz hP ω, Real.rpow_sub_one hz.ne']
  field_simp

/-- The derivative of marginal profit in the reset price (Galí (2015), p. 56). -/
noncomputable def profitDeriv2 (ε : ℝ) (Q P C : Ω → ℝ) (dΨ d2Ψ : Ω → ℝ → ℝ) (z : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - ε) * Q ω * (P ω ^ ε * C ω) * (-ε * z ^ (-ε - 1) - markup ε *
    ((-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)
      + z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z))))

/-- Marginal profit is differentiable in the reset price, with derivative
`profitDeriv2` (Galí (2015), p. 56). -/
theorem hasDerivAt_profitDeriv {ε z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ}
    {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hdΨ : ∀ ω y, 0 < y → HasDerivAt (dΨ ω) (d2Ψ ω y) y) (ω : Ω) :
    HasDerivAt (fun x => profitDeriv ε Q P C dΨ x ω) (profitDeriv2 ε Q P C dΨ d2Ψ z ω) z := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-ε)) (-ε * z ^ (-ε - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h2 : HasDerivAt (fun x : ℝ => x ^ (-ε - 1)) ((-ε - 1) * z ^ (-ε - 1 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h3 : HasDerivAt (fun x => dΨ ω (demand ε x P C ω))
      (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z)) z :=
    (hdΨ ω _ (demand_pos hz hP hC ω)).comp z (hasDerivAt_demand hz hP ω)
  have hG := (HasDerivAt.sub h1 ((HasDerivAt.mul h2 h3).const_mul (markup ε))).const_mul
    ((1 - ε) * Q ω * (P ω ^ ε * C ω))
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hz] with x hx
  exact profitDeriv_eq hx dΨ hP ω

/-- A bound on marginal profit on prices `≥ lo > 0` (Galí (2015), p. 56). -/
theorem abs_profitDeriv_le {ε z lo Qm W K : ℝ} (hε : 1 < ε) (hlo : 0 < lo) (hz : lo ≤ z)
    {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) (hQ0 : 0 < Q ω)
    (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ ε * C ω) (hW : P ω ^ ε * C ω ≤ W)
    (hd : |dΨ ω (demand ε z P C ω)| ≤ K) :
    |profitDeriv ε Q P C dΨ z ω|
      ≤ (ε - 1) * Qm * W * (lo ^ (-ε) + markup ε * (lo ^ (-ε - 1) * K)) := by
  have hz0 : 0 < z := hlo.trans_le hz
  rw [profitDeriv_eq hz0 dΨ hP ω]
  have hM := markup_pos hε
  have a0 : 0 ≤ z ^ (-ε) := Real.rpow_nonneg hz0.le _
  have a1 : 0 ≤ z ^ (-ε - 1) := Real.rpow_nonneg hz0.le _
  have b0 : z ^ (-ε) ≤ lo ^ (-ε) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b1 : z ^ (-ε - 1) ≤ lo ^ (-ε - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have hc : |(1 - ε) * Q ω * (P ω ^ ε * C ω)| ≤ (ε - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - ε ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have hi : |z ^ (-ε) - markup ε * (z ^ (-ε - 1) * dΨ ω (demand ε z P C ω))|
      ≤ lo ^ (-ε) + markup ε * (lo ^ (-ε - 1) * K) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg a0, abs_mul, abs_of_pos hM, abs_mul, abs_of_nonneg a1]
    gcongr
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- A bound on the derivative of marginal profit on prices `≥ lo > 0`
(Galí (2015), p. 56). -/
theorem abs_profitDeriv2_le {ε z lo Qm W K Yh : ℝ} (hε : 1 < ε) (hlo : 0 < lo)
    (hz : lo ≤ z) {Q P C : Ω → ℝ} {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) (hQ0 : 0 < Q ω) (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ ε * C ω)
    (hW : P ω ^ ε * C ω ≤ W) (hd : |dΨ ω (demand ε z P C ω)| ≤ K)
    (hd2 : |d2Ψ ω (demand ε z P C ω)| ≤ K) (hY : demand ε z P C ω ≤ Yh) :
    |profitDeriv2 ε Q P C dΨ d2Ψ z ω| ≤ (ε - 1) * Qm * W * (ε * lo ^ (-ε - 1)
      + markup ε * ((ε + 1) * lo ^ (-ε - 1 - 1) * K + lo ^ (-ε - 1) * (K * (ε * (Yh / lo))))) := by
  have hz0 : 0 < z := hlo.trans_le hz
  have hM := markup_pos hε
  have hε0 : 0 < ε := by linarith
  have hY0 := demand_pos (ε := ε) hz0 hP hC ω
  have a1 : 0 ≤ z ^ (-ε - 1) := Real.rpow_nonneg hz0.le _
  have a2 : 0 ≤ z ^ (-ε - 1 - 1) := Real.rpow_nonneg hz0.le _
  have b1 : z ^ (-ε - 1) ≤ lo ^ (-ε - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b2 : z ^ (-ε - 1 - 1) ≤ lo ^ (-ε - 1 - 1) :=
    Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have bY : demand ε z P C ω / z ≤ Yh / lo := div_le_div₀ (hY0.le.trans hY) hY hlo hz
  have hK : 0 ≤ K := (abs_nonneg _).trans hd
  have hc : |(1 - ε) * Q ω * (P ω ^ ε * C ω)| ≤ (ε - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - ε ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have e1 : |-ε * z ^ (-ε - 1)| = ε * z ^ (-ε - 1) := by
    rw [abs_mul, abs_neg, abs_of_pos hε0, abs_of_nonneg a1]
  have e2 : |(-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)|
      = (ε + 1) * z ^ (-ε - 1 - 1) * |dΨ ω (demand ε z P C ω)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg a2, abs_of_nonpos (by linarith : -ε - 1 ≤ 0)]
    ring
  have e3 : |z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z))|
      = z ^ (-ε - 1) * (|d2Ψ ω (demand ε z P C ω)| * (ε * (demand ε z P C ω / z))) := by
    have hn : -ε * demand ε z P C ω / z ≤ 0 := by
      rw [neg_mul, neg_div]; exact neg_nonpos.mpr (by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonpos hn]
    ring
  have hi : |-ε * z ^ (-ε - 1) - markup ε *
      ((-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)
        + z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z)))|
      ≤ ε * lo ^ (-ε - 1)
        + markup ε * ((ε + 1) * lo ^ (-ε - 1 - 1) * K + lo ^ (-ε - 1) * (K * (ε * (Yh / lo)))) := by
    refine (abs_sub _ _).trans ?_
    rw [e1, abs_mul, abs_of_pos hM]
    refine add_le_add (by gcongr) (mul_le_mul_of_nonneg_left ?_ hM.le)
    refine (abs_add_le _ _).trans ?_
    rw [e2, e3]
    have hYz : 0 ≤ demand ε z P C ω / z := by positivity
    gcongr
  unfold profitDeriv2
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- **Local Lipschitz bounds on marginal profit from primitives** (Galí (2015),
p. 56): under `Primitives`, marginal profit is Lipschitz in the reset price near
every positive price, uniformly in the state. -/
theorem lipschitz_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y| := by
  obtain ⟨-, hβ, -, hε, hm, hQ, hP, hC, -, hdΨ, hΨb⟩ := hprim
  intro k y hy
  have hε0 : 0 ≤ ε := by linarith
  have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
  have hCpos : ∀ ω, 0 < C k ω := fun ω => hm.trans_le (hC k ω).1
  set lo := y / 2 with hlo_def
  set hi := 2 * y with hhi_def
  have hlo : 0 < lo := by positivity
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  set Yh := lo ^ (-ε) * Khi
  have hy1 : 0 < hi ^ (-ε) * Klo := by positivity
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-ε) * Klo) Yh hy1
  set L₀ := (ε - 1) * (|Qb| * β ^ k) * Khi * (ε * lo ^ (-ε - 1) + markup ε *
    ((ε + 1) * lo ^ (-ε - 1 - 1) * |K| + lo ^ (-ε - 1) * (|K| * (ε * (Yh / lo)))))
  refine ⟨max L₀ 0, le_max_right _ _, lo, hlo, fun z hz ω => ?_⟩
  have hball : ∀ x ∈ Metric.ball y lo, lo ≤ x ∧ x ≤ hi := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith
  have hd : ∀ x ∈ Metric.ball y lo, HasDerivWithinAt
      (fun x => profitDeriv ε (Q k) (P k) (C k) (dΨ k) x ω)
      (profitDeriv2 ε (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω) (Metric.ball y lo) x :=
    fun x hx => (hasDerivAt_profitDeriv (hlo.trans_le (hball x hx).1) hPpos hCpos (hdΨ k)
      ω).hasDerivWithinAt
  have hb : ∀ x ∈ Metric.ball y lo,
      ‖profitDeriv2 ε (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω‖ ≤ max L₀ 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hball x hx
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm hlo hx1 hx2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hε0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, hK2⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    rw [Real.norm_eq_abs]
    exact (abs_profitDeriv2_le hε hlo hx1 hPpos hCpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ ε * m).trans hw1) hw2 (hK1.trans (le_abs_self _))
      (hK2.trans (le_abs_self _)) hY2).trans (le_max_left _ _)
  have hyb : y ∈ Metric.ball y lo := Metric.mem_ball_self hlo
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_ball y lo) hyb hz
  simpa only [Real.norm_eq_abs] using this

/-- **Domination of marginal profit from primitives** (Galí (2015), p. 56): under
`Primitives`, on every interval `(a, b)` with `a > 0`, marginal profit at horizon `k`
is bounded by `uₖ = c βᵏ`, and `∑ θᵏ uₖ < ∞` since `θβ < 1`. -/
theorem dominated_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k := by
  obtain ⟨hθ, hβ, hθβ, hε, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro a b ha
  have hε0 : 0 ≤ ε := by linarith
  set hi := max b a
  have hhi : 0 < hi := ha.trans_le (le_max_right _ _)
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-ε) * Klo) (a ^ (-ε) * Khi) (by positivity)
  set c := (ε - 1) * |Qb| * Khi * (a ^ (-ε) + markup ε * (a ^ (-ε - 1) * |K|))
  refine ⟨fun k => (ε - 1) * (|Qb| * β ^ k) * Khi * (a ^ (-ε) + markup ε * (a ^ (-ε - 1) * |K|)),
    ?_, fun k y hy ω => ?_⟩
  · refine ((summable_geometric_of_lt_one (mul_nonneg hθ hβ) hθβ).mul_left c).congr
      fun k => ?_
    rw [abs_of_nonneg hθ, mul_pow]
    ring
  · have hy1 : a ≤ y := hy.1.le
    have hy2 : y ≤ hi := hy.2.le.trans (le_max_left _ _)
    have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm ha hy1 hy2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hε0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, -⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    exact abs_profitDeriv_le hε ha hy1 hPpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ ε * m).trans hw1) hw2 (hK1.trans (le_abs_self _))

/-- **Convergence of the objective from primitives** (Galí (2015), p. 56): under
`Primitives`, the reset-price objective converges at every positive price. -/
theorem summable_profit_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) : ∀ y, 0 < y →
      Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω := by
  obtain ⟨hθ, hβ, hθβ, hε, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro y hy
  have hε0 : 0 ≤ ε := by linarith
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  obtain ⟨K, hK⟩ := hΨb (y ^ (-ε) * Klo) (y ^ (-ε) * Khi) (by positivity)
  set c := |Qb| * (y * |y ^ (-ε) * Khi| + |K|)
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg hθ hβ) hθβ).mul_left c) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hθ]
  have hb : ∀ ω', |profit ε (Q k) (P k) (C k) (Ψ k) y ω'| ≤ |Qb| * β ^ k *
      (y * |y ^ (-ε) * Khi| + |K|) := by
    intro ω'
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm hy le_rfl le_rfl (hP k) (hC k) ω'
    obtain ⟨hK0, -, -⟩ := hK k ω' _ hY1 hY2
    have hY0 : 0 < demand ε y (P k) (C k) ω' :=
      demand_pos hy (fun ω => hm.trans_le (hP k ω).1) (fun ω => hm.trans_le (hC k ω).1) ω'
    have hQm : Q k ω' ≤ |Qb| * β ^ k :=
      (hQ k ω').2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    unfold profit
    rw [abs_mul, abs_of_pos (hQ k ω').1]
    refine mul_le_mul hQm ((abs_sub _ _).trans (add_le_add ?_
      (hK0.trans (le_abs_self _)))) (abs_nonneg _) ((hQ k ω').1.le.trans hQm)
    rw [abs_mul, abs_of_pos hy, abs_of_pos hY0]
    exact mul_le_mul_of_nonneg_left (hY2.trans (le_abs_self _)) hy.le
  calc θ ^ k * |𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω|
      ≤ θ ^ k * (|Qb| * β ^ k * (y * |y ^ (-ε) * Khi| + |K|)) :=
        mul_le_mul_of_nonneg_left (𝔼.abs_E_le hb t ω) (pow_nonneg hθ k)
    _ = c * (θ * β) ^ k := by rw [mul_pow]; ring

/-- **The derivative of the reset-price objective, from primitives only**
(Galí (2015), eq. (10), p. 56): under `Primitives`, at every positive price the
objective has derivative `((1 − ε)/P*) ∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]`. -/
theorem hasDerivAt_objective_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨-, -, -, hε, hm, -, hP, hC, hΨ, -, -⟩ := hprim
  exact hasDerivAt_objective_of_pos 𝔼 hε (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hLip hloc t ω hs hx

/-- **(10) is necessary, from primitives only** (Galí (2015), eq. (10), p. 56): under
`Primitives`, a local maximum `P* > 0` of the reset-price objective satisfies (10). -/
theorem foc_of_isLocalMax_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) {t : ℕ}
    {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hmax : IsLocalMax (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) x) :
    focSum 𝔼 θ ε Q P C dΨ t x ω = 0 :=
  foc_of_isLocalMax 𝔼 hprim.2.2.2.1 hx (hasDerivAt_objective_of_primitives 𝔼 hprim t ω hx) hmax

/-- **(10) characterises the optimal reset price, from primitives only**
(Galí (2015), eq. (10), p. 56): under `Primitives`, convex costs (`Ψ'' ≥ 0`) and the
book's normalisation `Λ_{t,t} = 1` (so `Q_{t,t} = 1/P_t`), a positive price maximises
the objective over all positive prices if and only if it satisfies (10), and it is
then the unique maximiser. -/
theorem isMaxOn_iff_foc_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ)
    (hconv : ∀ k ω y, 0 < y → 0 ≤ d2Ψ k ω y) (hQ0 : ∀ ω, Q 0 ω = (P 0 ω)⁻¹) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 θ ε Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 θ ε Q P C Ψ t y ω < objective 𝔼 θ ε Q P C Ψ t x ω) := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨hθ, -, -, hε, hm, hQ, hP, hC, hΨ, hdΨ, -⟩ := hprim
  have hε0 : 0 ≤ ε := by linarith
  have hmono : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0) := by
    intro k ω
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun y hy => (hdΨ k ω y hy).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioi]
      exact fun y hy => (hdΨ k ω y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro y hy
      rw [(hdΨ k ω y hy).deriv]
      exact hconv k ω y hy
  have hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω := by
    have hMx : 0 < Mx := hm.trans_le ((hP 0 ω).1.trans (hP 0 ω).2)
    have hc : 0 < Mx⁻¹ * (m ^ ε * m) := by positivity
    have hle : (fun _ : Ω => Mx⁻¹ * (m ^ ε * m))
        ≤ fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω') := fun ω' => by
      simp only
      rw [hQ0 ω']
      have hP0 : 0 < P 0 ω' := hm.trans_le (hP 0 ω').1
      exact mul_le_mul (inv_anti₀ hP0 (hP 0 ω').2)
        (weight_bounds hε0 hm (hP 0) (hC 0) ω').1 (by positivity) (inv_nonneg.mpr hP0.le)
    have := 𝔼.mono t hle ω
    rw [𝔼.const] at this
    exact hc.trans_le this
  exact isMaxOn_iff_foc 𝔼 hε hθ (fun k ω => (hQ k ω).1) (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hmono hLip hloc t ω hs hpos hx

end Gali.BasicNewKeynesianModel.ResetPrice

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Marginal cost and the optimal reset price

Galí (2015), Chapter 3, §3.3 (pp. 58–60).

## Main results

* `eq14_exact`: the exact aggregate employment identity
  `(1 − α) n_t = y_t − a_t + d_t`, with `d_t` the price-dispersion term; `eq14`:
  equation (14) when `d_t = 0` (the dispersion term is studied elsewhere);
  `dispersion_symmetric`: `d_t = 0` when all prices are equal.
* `log_marginal_cost`: firm marginal cost `ψ = w − (a − α n + log(1 − α))`.
* `average_marginal_cost`, `log_aggregate_first_order`: average marginal cost
  across price cohorts, `ψ_t = w_t − (a_t − α n_t + log(1 − α))`, exactly in the
  cohort average of employment and to first order in `n_t`.
* `eq15`: `ψ_{t+k|t} = ψ_{t+k} − (αε/(1 − α))(p*_t − p_{t+k})`.
* `Theta_pos`, `Theta_le_one`, `Theta_eq_one_iff`: `Θ ∈ (0, 1]`, `Θ = 1 ↔ α = 0`.
* `pstar_formula`: `p*_t = (1 − βθ) ∑ₖ (βθ)ᵏ E_t[p_{t+k} − Θ μ̂_{t+k}]`.
* `eq16`, `eq16_unique`, `eq16_of_eq11`: the recursive form (16) and the
  uniqueness of its bounded solution.
-/

namespace Gali.BasicNewKeynesianModel.MarginalCost

open Filter Topology

/-! ### Aggregate employment, eq. (14) -/

/-- Aggregate employment `N_t = ∫ (Y_t(i)/A_t)^{1/(1−α)} di` with
`Y_t(i) = (P_t(i)/P_t)^{−ε} Y_t` (Galí (2015), p. 59, using (5), (1) and goods
market clearing), for a continuum of firms `ι` with measure `ν`. -/
noncomputable def employment {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    (α ε Y A P : ℝ) (p : ι → ℝ) : ℝ :=
  ∫ i, ((p i / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)) ∂ν

/-- The price-dispersion term `d_t = (1 − α) log ∫ (P_t(i)/P_t)^{−ε/(1−α)} di`
(Galí (2015), p. 59). -/
noncomputable def dispersion {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    (α ε P : ℝ) (p : ι → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (p i / P) ^ (-ε / (1 - α)) ∂ν)

/-- **The exact employment identity** (Galí (2015), p. 59):
`(1 − α) n_t = y_t − a_t + d_t`. -/
theorem eq14_exact {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    {α ε Y A P : ℝ} (hα : α < 1) (hY : 0 < Y) (hA : 0 < A) (hP : 0 < P) {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hD : 0 < ∫ i, (p i / P) ^ (-ε / (1 - α)) ∂ν) :
    (1 - α) * Real.log (employment ν α ε Y A P p)
      = Real.log Y - Real.log A + dispersion ν α ε P p := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hint : (fun i => ((p i / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)))
      = fun i => (p i / P) ^ (-ε / (1 - α)) * (Y / A) ^ (1 / (1 - α)) := by
    funext i
    have hpi : 0 ≤ p i / P := (div_pos (hp i) hP).le
    rw [mul_div_assoc, Real.mul_rpow (Real.rpow_nonneg hpi _) (div_pos hY hA).le,
      ← Real.rpow_mul hpi]
    congr 2
    ring
  have hc : 0 < (Y / A) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos (div_pos hY hA) _
  unfold employment dispersion
  rw [hint, MeasureTheory.integral_mul_const, Real.log_mul hD.ne' hc.ne',
    Real.log_rpow (div_pos hY hA), Real.log_div hY.ne' hA.ne']
  field_simp
  ring

/-- With equal prices across firms and a probability measure of firms, there is no
dispersion: `d_t = 0` (Galí (2015), p. 59, the symmetric case). -/
theorem dispersion_symmetric {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    [MeasureTheory.IsProbabilityMeasure ν] {α ε P : ℝ} (hP : 0 < P) :
    dispersion ν α ε P (fun _ => P) = 0 := by
  simp [dispersion, div_self hP.ne']

/-- **Equation (14)** (Galí (2015), p. 59): with no price dispersion (`d_t = 0`,
true to first order around the zero-inflation steady state),
`n_t = (y_t − a_t)/(1 − α)`. -/
theorem eq14 {α n y a d : ℝ} (hα : α < 1) (h : (1 - α) * n = y - a + d) (hd : d = 0) :
    n = (y - a) / (1 - α) := by
  have h1 : 1 - α ≠ 0 := by linarith
  rw [hd, add_zero] at h
  field_simp
  linarith

/-! ### Marginal cost -/

/-- The production function (5) in logs (Galí (2015), p. 55):
`log(A N^{1−α}) = a + (1 − α) n`. -/
theorem log_production {α A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    Real.log (A * N ^ (1 - α)) = Real.log A + (1 - α) * Real.log N := by
  rw [Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN]

/-- **Firm marginal cost** (Galí (2015), p. 59 and fn. 3): nominal marginal cost
`Ψ = W / MPN` with `MPN = (1 − α) A N^{−α}`, so in logs
`ψ = w − (a − α n + log(1 − α))`. -/
theorem log_marginal_cost {α W A N : ℝ} (hα : α < 1) (hW : 0 < W) (hA : 0 < A)
    (hN : 0 < N) :
    Real.log (W / ((1 - α) * A * N ^ (-α)))
      = Real.log W - (Real.log A - α * Real.log N + Real.log (1 - α)) := by
  have h1 : 0 < 1 - α := by linarith
  rw [Real.log_div hW.ne' (by positivity), Real.log_mul (by positivity)
    (Real.rpow_pos_of_pos hN _).ne', Real.log_mul h1.ne' hA.ne', Real.log_rpow hN]
  ring

/-- The demand schedule (9) with goods-market clearing (12) in logs (Galí (2015),
p. 60): `log((P*/P)^{−ε} C) = −ε (p* − p) + c`. -/
theorem log_demand {ε Ps P C : ℝ} (hPs : 0 < Ps) (hP : 0 < P) (hC : 0 < C) :
    Real.log ((Ps / P) ^ (-ε) * C) = -ε * (Real.log Ps - Real.log P) + Real.log C := by
  rw [Real.log_mul (Real.rpow_pos_of_pos (div_pos hPs hP) _).ne' hC.ne',
    Real.log_rpow (div_pos hPs hP), Real.log_div hPs.ne' hP.ne']

/-- **Average marginal cost across price cohorts** (Galí (2015), p. 60): with
cohort weights `(1 − θ)θᵏ`, the average of `ψ_{t|t−k} = w − (a − α n_{t|t−k} +
log(1 − α))` is `w − (a − α n̄ + log(1 − α))`, where `n̄` is the cohort average of
log employment. -/
theorem average_marginal_cost {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (w a α : ℝ)
    {n : ℕ → ℝ} (hn : Summable fun k => durationProb θ k * n k) :
    ∑' k, durationProb θ k * (w - (a - α * n k + Real.log (1 - α)))
      = w - (a - α * ∑' k, durationProb θ k * n k + Real.log (1 - α)) := by
  have hd : Summable fun k => durationProb θ k :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ)
  have h : ∀ k, durationProb θ k * (w - (a - α * n k + Real.log (1 - α)))
      = durationProb θ k * (w - a - Real.log (1 - α)) + α * (durationProb θ k * n k) := by
    intro k; ring
  simp_rw [h]
  rw [Summable.tsum_add (hd.mul_right _) (hn.mul_left α), tsum_mul_right, tsum_mul_left,
    survival_sum hθ0 hθ1]
  ring

/-- **Log of aggregate employment equals average log employment to first order**
(Galí (2015), p. 60, "holds up to a first order approximation about a symmetric
equilibrium"). Perturbing cohort log employment `n_{t|t−k} = n̄ + s n̂ₖ` around a
symmetric point, `log ∑ (1 − θ)θᵏ e^{n_{t|t−k}} − ∑ (1 − θ)θᵏ n_{t|t−k}` vanishes
together with its derivative at `s = 0`. -/
theorem log_aggregate_first_order {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (nbar : ℝ)
    {nhat : ℕ → ℝ} {B : ℝ} (hB : ∀ k, |nhat k| ≤ B) :
    (Real.log (∑' k, durationProb θ k * Real.exp (nbar + 0 * nhat k))
        - ∑' k, durationProb θ k * (nbar + 0 * nhat k) = 0) ∧
    HasDerivAt (fun s => Real.log (∑' k, durationProb θ k * Real.exp (nbar + s * nhat k))
        - ∑' k, durationProb θ k * (nbar + s * nhat k)) 0 0 := by
  have hd : Summable fun k => durationProb θ k :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ)
  have hd0 : ∀ k, 0 ≤ durationProb θ k := fun k => durationProb_nonneg hθ0 hθ1.le k
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hS : Summable fun k => durationProb θ k * nhat k := by
    refine Summable.of_norm_bounded (hd.mul_right B) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd0 k)]
    exact mul_le_mul_of_nonneg_left (hB k) (hd0 k)
  have hsum1 : ∑' k, durationProb θ k = 1 := survival_sum hθ0 hθ1
  have hval : ∑' k, durationProb θ k * Real.exp (nbar + 0 * nhat k) = Real.exp nbar := by
    simp only [zero_mul, add_zero]
    rw [tsum_mul_right, hsum1, one_mul]
  have hlin : ∀ s, ∑' k, durationProb θ k * (nbar + s * nhat k)
      = nbar + s * ∑' k, durationProb θ k * nhat k := by
    intro s
    have : ∀ k, durationProb θ k * (nbar + s * nhat k)
        = durationProb θ k * nbar + s * (durationProb θ k * nhat k) := fun k => by ring
    simp_rw [this]
    rw [Summable.tsum_add (hd.mul_right _) (hS.mul_left s), tsum_mul_right, tsum_mul_left,
      hsum1, one_mul]
  refine ⟨by rw [hval, Real.log_exp, hlin, zero_mul, add_zero, sub_self], ?_⟩
  -- derivative of the aggregate
  have hD := hasDerivAt_tsum_of_isPreconnected
    (u := fun k => durationProb θ k * (B * Real.exp (|nbar| + B)))
    (g := fun k s => durationProb θ k * Real.exp (nbar + s * nhat k))
    (g' := fun k s => durationProb θ k * (nhat k * Real.exp (nbar + s * nhat k)))
    (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    (hd.mul_right _) isOpen_Ioo isPreconnected_Ioo
    (fun k s _ => by
      have h1 : HasDerivAt (fun s => nbar + s * nhat k) (nhat k) s := by
        simpa using ((hasDerivAt_id s).mul_const (nhat k)).const_add nbar
      have h2 := (Real.hasDerivAt_exp _).comp s h1
      refine (h2.const_mul (durationProb θ k)).congr_deriv ?_
      ring)
    (fun k s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd0 k), abs_mul,
        abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left (mul_le_mul (hB k) ?_ (Real.exp_pos _).le hB0)
        (hd0 k)
      rw [Real.exp_le_exp]
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      calc nbar + s * nhat k ≤ |nbar| + |s * nhat k| := add_le_add (le_abs_self _)
            (le_abs_self _)
        _ = |nbar| + |s| * |nhat k| := by rw [abs_mul]
        _ ≤ |nbar| + 1 * B := by
            have := mul_le_mul hs1 (hB k) (abs_nonneg _) zero_le_one
            linarith
        _ = |nbar| + B := by ring)
    ⟨by norm_num, by norm_num⟩
    (by
      simp only [zero_mul, add_zero]
      exact hd.mul_right _)
    ⟨by norm_num, by norm_num⟩
  have hpos : (∑' k, durationProb θ k * Real.exp (nbar + 0 * nhat k)) ≠ 0 := by
    rw [hval]; exact (Real.exp_pos _).ne'
  have hlog := hD.log hpos
  have hlinD : HasDerivAt (fun s => ∑' k, durationProb θ k * (nbar + s * nhat k))
      (∑' k, durationProb θ k * nhat k) 0 := by
    simp_rw [hlin]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (∑' k, durationProb θ k * nhat k)).const_add
      nbar
  refine (HasDerivAt.sub hlog hlinD).congr_deriv ?_
  rw [hval]
  simp only [zero_mul, add_zero]
  have : ∀ k, durationProb θ k * (nhat k * Real.exp nbar)
      = Real.exp nbar * (durationProb θ k * nhat k) := fun k => by ring
  simp_rw [this]
  rw [tsum_mul_left]
  field_simp
  ring

/-- **Equation (15)** (Galí (2015), p. 60). With firm and average marginal cost
`ψ = w − (a − α n + log(1 − α))`, the firm production function in logs
`y_{t+k|t} = a + (1 − α) n_{t+k|t}`, the aggregate relation (14)
`(1 − α) n = y − a`, demand (9) in logs and goods-market clearing (12):
`ψ_{t+k|t} = ψ_{t+k} + α(n_{t+k|t} − n_{t+k})
          = ψ_{t+k} + (α/(1 − α))(y_{t+k|t} − y_{t+k})
          = ψ_{t+k} − (αε/(1 − α))(p*_t − p_{t+k})`. -/
theorem eq15 {α ε w a ni n yi y ps p c ψi ψ : ℝ} (hα : α < 1)
    (hψi : ψi = w - (a - α * ni + Real.log (1 - α)))
    (hψ : ψ = w - (a - α * n + Real.log (1 - α)))
    (hyi : yi = a + (1 - α) * ni) (hy : (1 - α) * n = y - a)
    (hdem : yi = -ε * (ps - p) + c) (hc : c = y) :
    ψi = ψ + α * (ni - n) ∧ ψi = ψ + α / (1 - α) * (yi - y) ∧
      ψi = ψ - α * ε / (1 - α) * (ps - p) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have e1 : ψi = ψ + α * (ni - n) := by rw [hψi, hψ]; ring
  have hn : ni - n = (yi - y) / (1 - α) := by
    field_simp
    linarith
  refine ⟨e1, ?_, ?_⟩
  · rw [e1, hn]; ring
  · rw [e1, hn, hdem, hc]
    field_simp
    ring

/-- Under constant returns (`α = 0`) firm-specific and average marginal cost
coincide, `ψ_{t+k|t} = ψ_{t+k}` (Galí (2015), p. 60). -/
theorem eq15_crs {ε w a ni n yi y ps p c ψi ψ : ℝ}
    (hψi : ψi = w - (a - 0 * ni + Real.log (1 - 0)))
    (hψ : ψ = w - (a - 0 * n + Real.log (1 - 0)))
    (hyi : yi = a + (1 - 0) * ni) (hy : (1 - 0) * n = y - a)
    (hdem : yi = -ε * (ps - p) + c) (hc : c = y) : ψi = ψ := by
  have := (eq15 (α := 0) (by norm_num) hψi hψ hyi hy hdem hc).2.2
  simpa using this

/-! ### The optimal reset price -/

/-- `Θ = (1 − α)/(1 − α + αε)` (Galí (2015), p. 60). -/
noncomputable def Theta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- `Θ > 0` (Galí (2015), p. 60). -/
theorem Theta_pos {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : 0 < Theta α ε :=
  div_pos (by linarith) (by nlinarith)

/-- `Θ ≤ 1` (Galí (2015), p. 60). -/
theorem Theta_le_one {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : Theta α ε ≤ 1 := by
  unfold Theta
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- `Θ = 1` exactly under constant returns, `α = 0` (Galí (2015), p. 61). -/
theorem Theta_eq_one_iff {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    Theta α ε = 1 ↔ α = 0 := by
  unfold Theta
  rw [div_eq_one_iff_eq (by nlinarith)]
  constructor
  · intro h
    have : α * ε = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hε.ne'
  · intro h; rw [h]; ring

/-- `Θ (1 + αε/(1 − α)) = 1`: `Θ` is the inverse of one plus the strategic
complementarity coefficient of (15) (Galí (2015), p. 60). -/
theorem Theta_mul {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    Theta α ε * (1 + α * ε / (1 - α)) = 1 := by
  unfold Theta
  have h1 : 1 - α ≠ 0 := by linarith
  have h2 : 1 - α + α * ε ≠ 0 := by nlinarith
  field_simp

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- The markup gap `μ̂_t = μ_t − μ`, with average markup `μ_t = p_t − ψ_t`
(Galí (2015), p. 60). -/
def markupGap (μ : ℝ) (p ψ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - ψ t - fun _ => μ

/-- A discounted affine sum: `∑ aᵏ (c + d₁ fₖ + d₂ gₖ)` (Galí (2015), p. 60). -/
theorem tsum_geom_affine {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f g : ℕ → ℝ}
    (hf : Summable fun k => a ^ k * f k) (hg : Summable fun k => a ^ k * g k) (c d₁ d₂ : ℝ) :
    ∑' k, a ^ k * (c + d₁ * f k + d₂ * g k)
      = c * (1 - a)⁻¹ + d₁ * ∑' k, a ^ k * f k + d₂ * ∑' k, a ^ k * g k := by
  have hgeo := summable_geometric_of_lt_one ha0 ha1
  have h : ∀ k, a ^ k * (c + d₁ * f k + d₂ * g k)
      = (a ^ k * c + d₁ * (a ^ k * f k)) + d₂ * (a ^ k * g k) := fun k => by ring
  simp_rw [h]
  rw [Summable.tsum_add ((hgeo.mul_right c).add (hf.mul_left d₁)) (hg.mul_left d₂),
    Summable.tsum_add (hgeo.mul_right c) (hf.mul_left d₁), tsum_mul_right, tsum_mul_left,
    tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1]
  ring

/-- **The optimal reset price in terms of markup gaps** (Galí (2015), p. 60).
Substituting (15), `ψ_{t+k|t} = ψ_{t+k} − (αε/(1 − α))(p*_t − p_{t+k})`, into (11),
`p*_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k|t}`, gives
`p*_t = (1 − βθ) ∑ₖ (βθ)ᵏ E_t[p_{t+k} − Θ μ̂_{t+k}]`. Here `a = βθ ∈ [0, 1)`. -/
theorem pstar_formula {a α ε μ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) {pstar p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (t : ℕ)
    (hpa : 𝔼.E t (pstar t) = pstar t)
    (h11 : pstar t = (fun _ => μ) + (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => ψ s - (α * ε / (1 - α)) • (pstar t - p s)) t) :
    pstar t = (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => p s - Theta α ε • markupGap μ p ψ s) t := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  set κ := α * ε / (1 - α) with hκ
  set Θ := Theta α ε with hΘ
  have hΘκ : Θ * (1 + κ) = 1 := Theta_mul hα0 hα1 hε
  funext ω
  set X := pstar t ω with hX
  set A : ℕ → ℝ := fun k => 𝔼.E t (ψ (t + k)) ω with hA
  set B : ℕ → ℝ := fun k => 𝔼.E t (p (t + k)) ω with hB
  have hsA : Summable fun k => a ^ k * A k :=
    ResetPrice.summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hψ t (t + k) ω') ω
  have hsB : Summable fun k => a ^ k * B k :=
    ResetPrice.summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hp t (t + k) ω') ω
  have hE1 : ∀ k, 𝔼.E t (ψ (t + k) - κ • (pstar t - p (t + k))) ω
      = -κ * X + 1 * A k + κ * B k := by
    intro k
    simp only [map_sub, map_smul, hpa, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hA, hB, hX]
    ring
  have hE2 : ∀ k, 𝔼.E t (p (t + k) - Θ • markupGap μ p ψ (t + k)) ω
      = Θ * μ + Θ * A k + (1 - Θ) * B k := by
    intro k
    simp only [markupGap, map_sub, map_smul, 𝔼.const, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hA, hB]
    ring
  have h11ω := congrFun h11 ω
  simp only [ResetPrice.forwardSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE1] at h11ω
  rw [tsum_geom_affine ha0 ha1 hsA hsB] at h11ω
  simp only [ResetPrice.forwardSum, Pi.smul_apply, smul_eq_mul, hE2]
  rw [tsum_geom_affine ha0 ha1 hsA hsB]
  have hd : 1 - a ≠ 0 := by linarith
  set SA := ∑' k, a ^ k * A k
  set SB := ∑' k, a ^ k * B k
  have e1 : (1 - a) * (-κ * X * (1 - a)⁻¹ + 1 * SA + κ * SB)
      = -κ * X + (1 - a) * SA + κ * (1 - a) * SB := by
    field_simp
  have e2 : (1 - a) * (Θ * μ * (1 - a)⁻¹ + Θ * SA + (1 - Θ) * SB)
      = Θ * μ + Θ * (1 - a) * SA + (1 - Θ) * (1 - a) * SB := by
    field_simp
  rw [e2]
  have h' : X = μ + (-κ * X + (1 - a) * SA + κ * (1 - a) * SB) := by
    rw [← e1]; exact h11ω
  linear_combination Θ * h' - (X - (1 - a) * SB) * hΘκ

/-- The forcing process of (16), `x_t = p_t − Θ μ̂_t`, is bounded when `p` and `ψ` are
(Galí (2015), p. 60). -/
theorem forcing_bounded {α ε μ : ℝ} {p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |(p t - Theta α ε • markupGap μ p ψ t) ω| ≤ M + |Theta α ε| * (M + M + |μ|) := by
  simp only [markupGap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sub _ _).trans (add_le_add (hp t ω) ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hp t ω) (hψ t ω)))
    le_rfl)

/-- The forcing process of (16) is adapted when `p` and `ψ` are
(Galí (2015), p. 60). -/
theorem forcing_adapted {α ε μ : ℝ} {p ψ : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) : 𝔼.Adapted fun t => p t - Theta α ε • markupGap μ p ψ t := by
  intro t
  simp only [markupGap, map_sub, map_smul, hpa t, hψa t, 𝔼.const]

/-- **Equation (16)** (Galí (2015), p. 60): the reset price
`p*_t = (1 − βθ) ∑ₖ (βθ)ᵏ E_t[p_{t+k} − Θ μ̂_{t+k}]` satisfies
`p*_t = βθ E_t p*_{t+1} + (1 − βθ)(p_t − Θ μ̂_t)`. -/
theorem eq16 {a α ε μ : ℝ} (ha : |a| < 1) {p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) (t : ℕ) :
    (1 - a) • ResetPrice.forwardSum 𝔼 a (fun s => p s - Theta α ε • markupGap μ p ψ s) t
      = a • 𝔼.E t ((1 - a) • ResetPrice.forwardSum 𝔼 a
          (fun s => p s - Theta α ε • markupGap μ p ψ s) (t + 1))
        + (1 - a) • (p t - Theta α ε • markupGap μ p ψ t) :=
  ResetPrice.normForward_rec 𝔼 ha (forcing_bounded hp hψ) (forcing_adapted 𝔼 hpa hψa) t

/-- **Uniqueness for (16)** (Galí (2015), p. 60): the series for `p*` is the only
bounded process satisfying `p*_t = βθ E_t p*_{t+1} + (1 − βθ)(p_t − Θ μ̂_t)`. -/
theorem eq16_unique {a α ε μ : ℝ} (ha : |a| < 1) {p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) {S : ℕ → Ω → ℝ} (hS : BoundedProc S)
    (hrec : ∀ t, S t = a • 𝔼.E t (S (t + 1))
      + (1 - a) • (p t - Theta α ε • markupGap μ p ψ t)) :
    S = fun t => (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => p s - Theta α ε • markupGap μ p ψ s) t :=
  ResetPrice.normForward_unique 𝔼 ha (forcing_bounded hp hψ) (forcing_adapted 𝔼 hpa hψa) hS
    hrec

/-- **From (11) and (15) to (16)** (Galí (2015), p. 60): if the reset price obeys
the log-linear rule (11) with firm-specific marginal cost (15) at every date, then
it obeys the recursion (16) at every date. -/
theorem eq16_of_eq11 {a α ε μ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) {pstar p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) (hsa : 𝔼.Adapted pstar)
    (h11 : ∀ t, pstar t = (fun _ => μ) + (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => ψ s - (α * ε / (1 - α)) • (pstar t - p s)) t) (t : ℕ) :
    pstar t = a • 𝔼.E t (pstar (t + 1)) + (1 - a) • (p t - Theta α ε • markupGap μ p ψ t) := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  have hf : ∀ s, pstar s = (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun r => p r - Theta α ε • markupGap μ p ψ r) s := fun s =>
    pstar_formula 𝔼 ha0 ha1 hα0 hα1 hε hp hψ s (hsa s) (h11 s)
  rw [hf t, hf (t + 1)]
  exact eq16 𝔼 ha hp hψ hpa hψa t

end Gali.BasicNewKeynesianModel.MarginalCost

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian Phillips curve

Galí (2015), Chapter 3, §3.3 (pp. 60–63), including footnote 4.

## Main results

* `eq17`: combining (8) and (16) gives `π_t = β E_t π_{t+1} − λ μ̂_t` with
  `λ = (1 − θ)(1 − βθ)Θ/θ`.
* `lam_strictAntiOn_theta`, `lam_strictAntiOn_alpha`, `lam_strictAntiOn_eps`:
  `λ` is strictly decreasing in `θ`, in `α`, and in `ε` when `α > 0`;
  `lam_const_eps`, `not_lam_strictAntiOn_eps`: at `α = 0`, `λ` does not depend on
  `ε`, so the book's claim (p. 61) fails there (correction C3-2).
* `nkpc_forward`, `nkpc_forward_unique`: `π_t = −λ ∑ₖ βᵏ E_t μ̂_{t+k}` is the unique
  bounded solution of (17).
* `fn4`: the real-marginal-cost form `π_t = β E_t π_{t+1} + λ m̂c_t`.
* `eq18`, `eq19_iff_eq20`, `eq21`: the markup–output relation, natural output
  `y^n_t = ψ_ya a_t + ψ_y` and the markup gap–output gap relation.
* `psi_y_neg`, `not_psi_y_pos`: `ψ_y < 0` (the book prints `> 0`, correction C3-1).
* `psi_y_perfect_competition`, `natural_output_lower`: `μ = 0` gives the classical
  output of chapter 2; market power lowers the level of output, not its slope.
* `eq22`: the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`, `κ = λ(σ + (φ + α)/(1 − α))`.
-/

namespace Gali.BasicNewKeynesianModel.NKPC

open MarginalCost

/-- `λ = (1 − θ)(1 − βθ)Θ/θ` (Galí (2015), p. 61). -/
noncomputable def lam (θ β α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) * Theta α ε / θ

/-- `λ > 0` for `θ ∈ (0, 1)` and `β < 1` (Galí (2015), p. 61). -/
theorem lam_pos {θ β α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : 0 < lam θ β α ε := by
  unfold lam
  have : 0 < 1 - β * θ := by nlinarith
  have := Theta_pos hα0 hα1 hε
  positivity

/-! ### The inflation equation (17) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Equation (17)** (Galí (2015), p. 60), derived from (8) and (16). With
inflation `π_t = p_t − p_{t−1}`, the price-index relation (8)
`π_t = (1 − θ)(p*_t − p_{t−1})` and the reset-price recursion (16)
`p*_t = βθ E_t p*_{t+1} + (1 − βθ)(p_t − Θ μ̂_t)`, inflation satisfies
`π_t = β E_t π_{t+1} − λ μ̂_t` at every date `t ≥ 1`. -/
theorem eq17 {θ β α ε μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {p pstar π ψ : ℕ → Ω → ℝ}
    (hpa : 𝔼.Adapted p) (hπ : ∀ t, π (t + 1) = p (t + 1) - p t)
    (h8 : ∀ t, π (t + 1) = (1 - θ) • (pstar (t + 1) - p t))
    (h16 : ∀ t, pstar t = (β * θ) • 𝔼.E t (pstar (t + 1))
      + (1 - β * θ) • (p t - Theta α ε • markupGap μ p ψ t)) (t : ℕ) :
    π (t + 1) = β • 𝔼.E (t + 1) (π (t + 2)) - lam θ β α ε • markupGap μ p ψ (t + 1) := by
  have h1θ : 1 - θ ≠ 0 := by linarith
  have hnext : pstar (t + 2) = p (t + 1) + (1 - θ)⁻¹ • π (t + 2) := by
    rw [h8 (t + 1), smul_smul, inv_mul_cancel₀ h1θ, one_smul]
    abel
  have hE : 𝔼.E (t + 1) (pstar (t + 2))
      = p (t + 1) + (1 - θ)⁻¹ • 𝔼.E (t + 1) (π (t + 2)) := by
    rw [hnext, map_add, map_smul, hpa (t + 1)]
  have h16' := h16 (t + 1)
  rw [hE] at h16'
  funext ω
  have e8 := congrFun (h8 t) ω
  have eπ := congrFun (hπ t) ω
  have e16 := congrFun h16' ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e8 eπ e16 ⊢
  unfold lam
  set G := markupGap μ p ψ (t + 1) ω
  set Epi := 𝔼.E (t + 1) (π (t + 2)) ω
  set Θ := Theta α ε
  -- `p*_{t+1} − p_{t+1} = θ/(1 − θ) π_{t+1}` and (16) give the result
  have hgap : pstar (t + 1) ω - p (t + 1) ω = θ * (1 - θ)⁻¹ * π (t + 1) ω := by
    field_simp
    linear_combination -e8 + (1 - θ) * eπ
  have hgap2 : pstar (t + 1) ω - p (t + 1) ω
      = β * θ * (1 - θ)⁻¹ * Epi - (1 - β * θ) * Θ * G := by
    rw [e16]; ring
  have hθ : θ ≠ 0 := hθ0.ne'
  have key : θ * (1 - θ)⁻¹ * π (t + 1) ω = β * θ * (1 - θ)⁻¹ * Epi - (1 - β * θ) * Θ * G := by
    rw [← hgap, hgap2]
  field_simp at key ⊢
  linear_combination key

/-! ### Comparative statics of `λ` -/

/-- **`λ` is strictly decreasing in the degree of price stickiness `θ`**
(Galí (2015), p. 61). -/
theorem lam_strictAntiOn_theta {β α ε : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) :
    StrictAntiOn (fun θ => lam θ β α ε) (Set.Ioo 0 1) := by
  intro θ₁ h₁ θ₂ h₂ h12
  have hΘ := Theta_pos hα0 hα1 hε
  simp only [lam]
  rw [div_lt_div_iff₀ h₂.1 h₁.1]
  have hb : 0 ≤ β * (θ₂ - θ₁) := mul_nonneg hβ0 (by linarith)
  have hp1 : 0 < 1 - β * θ₂ := by nlinarith [h₂.2]
  have key : (1 - θ₂) * (1 - β * θ₂) * θ₁ < (1 - θ₁) * (1 - β * θ₁) * θ₂ := by
    have e1 : (1 - θ₂) * θ₁ < (1 - θ₁) * θ₂ := by nlinarith
    have e2 : 1 - β * θ₂ ≤ 1 - β * θ₁ := by nlinarith
    calc (1 - θ₂) * (1 - β * θ₂) * θ₁ = ((1 - θ₂) * θ₁) * (1 - β * θ₂) := by ring
      _ < ((1 - θ₁) * θ₂) * (1 - β * θ₂) := mul_lt_mul_of_pos_right e1 hp1
      _ ≤ ((1 - θ₁) * θ₂) * (1 - β * θ₁) :=
          mul_le_mul_of_nonneg_left e2 (mul_pos (by linarith [h₁.2]) h₂.1).le
      _ = (1 - θ₁) * (1 - β * θ₁) * θ₂ := by ring
  calc (1 - θ₂) * (1 - β * θ₂) * Theta α ε * θ₁
      = (1 - θ₂) * (1 - β * θ₂) * θ₁ * Theta α ε := by ring
    _ < (1 - θ₁) * (1 - β * θ₁) * θ₂ * Theta α ε := mul_lt_mul_of_pos_right key hΘ
    _ = (1 - θ₁) * (1 - β * θ₁) * Theta α ε * θ₂ := by ring

/-- `Θ` is strictly decreasing in `α` on `[0, 1)` when `ε > 0` (Galí (2015), p. 61). -/
theorem Theta_strictAntiOn_alpha {ε : ℝ} (hε : 0 < ε) :
    StrictAntiOn (fun α => Theta α ε) (Set.Ico 0 1) := by
  intro α₁ h₁ α₂ h₂ h12
  simp only [Theta]
  rw [div_lt_div_iff₀ (by nlinarith [h₂.1, h₂.2]) (by nlinarith [h₁.1, h₁.2])]
  nlinarith [mul_lt_mul_of_pos_right h12 hε]

/-- **`λ` is strictly decreasing in the measure of decreasing returns `α`**
(Galí (2015), p. 61). -/
theorem lam_strictAntiOn_alpha {θ β ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hε : 0 < ε) :
    StrictAntiOn (fun α => lam θ β α ε) (Set.Ico 0 1) := by
  intro α₁ h₁ α₂ h₂ h12
  have hc : 0 < (1 - θ) * (1 - β * θ) / θ := by
    have : 0 < 1 - β * θ := by nlinarith
    have : 0 < 1 - θ := by linarith
    positivity
  have := Theta_strictAntiOn_alpha hε h₁ h₂ h12
  simp only [lam, mul_div_right_comm _ (Theta _ _)] at this ⊢
  exact mul_lt_mul_of_pos_left this hc

/-- **`λ` is strictly decreasing in the demand elasticity `ε` when `α > 0`**
(Galí (2015), p. 61, corrected: see `not_lam_strictAntiOn_eps`). -/
theorem lam_strictAntiOn_eps {θ β α : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 < α) (hα1 : α < 1) :
    StrictAntiOn (fun ε => lam θ β α ε) (Set.Ioi 0) := by
  intro ε₁ h₁ ε₂ h₂ h12
  have hc : 0 < (1 - θ) * (1 - β * θ) / θ := by
    have : 0 < 1 - β * θ := by nlinarith
    have : 0 < 1 - θ := by linarith
    positivity
  have hΘ : Theta α ε₂ < Theta α ε₁ := by
    simp only [Theta]
    have h1 : 0 < 1 - α + α * ε₁ := by nlinarith [Set.mem_Ioi.mp h₁]
    exact div_lt_div_of_pos_left (by linarith) h1 (by nlinarith)
  simp only [lam, mul_div_right_comm _ (Theta _ _)]
  exact mul_lt_mul_of_pos_left hΘ hc

/-- Under constant returns (`α = 0`), `λ` does not depend on `ε` (Galí (2015),
p. 61: `Θ = 1` when `α = 0`). -/
theorem lam_const_eps (θ β ε₁ ε₂ : ℝ) : lam θ β 0 ε₁ = lam θ β 0 ε₂ := by
  simp [lam, Theta]

/-- **Correction C3-2** (Galí (2015), p. 61): the claim that `λ` is strictly
decreasing in `ε` is false at `α = 0`, where `λ` is constant in `ε`. -/
theorem not_lam_strictAntiOn_eps (θ β : ℝ) :
    ¬ StrictAntiOn (fun ε => lam θ β 0 ε) (Set.Ioi 1) := by
  intro h
  have := h (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num) (show (3 : ℝ) ∈ Set.Ioi 1 by norm_num)
    (by norm_num)
  simp only [lam_const_eps θ β 3 2, lt_self_iff_false] at this

/-! ### Forward solution of (17) -/

/-- **Forward solution of (17)** (Galí (2015), p. 61): for a bounded adapted
markup gap, `π_t = −λ ∑ₖ βᵏ E_t μ̂_{t+k}` satisfies `π_t = β E_t π_{t+1} − λ μ̂_t`
and is bounded. -/
theorem nkpc_forward {β lamv : ℝ} (hβ : |β| < 1) {μhat : ℕ → Ω → ℝ} {M : ℝ}
    (hμ : ∀ t ω, |μhat t ω| ≤ M) (hμa : 𝔼.Adapted μhat) :
    (∀ t, (-lamv) • ResetPrice.forwardSum 𝔼 β μhat t
        = β • 𝔼.E t ((-lamv) • ResetPrice.forwardSum 𝔼 β μhat (t + 1)) - lamv • μhat t) ∧
      BoundedProc fun t => (-lamv) • ResetPrice.forwardSum 𝔼 β μhat t := by
  refine ⟨fun t => ?_, ?_⟩
  · rw [ResetPrice.forwardSum_rec 𝔼 hβ hμ hμa t, 𝔼.E_smul, smul_add, smul_smul, smul_smul,
      mul_comm β (-lamv)]
    simp only [neg_smul]
    abel
  · obtain ⟨B, hB⟩ := ResetPrice.forwardSum_bounded 𝔼 hβ ⟨M, hμ⟩
    refine ⟨|lamv| * B, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)

/-- **Uniqueness of the forward solution** (Galí (2015), p. 61): every bounded
solution of (17) equals `−λ ∑ₖ βᵏ E_t μ̂_{t+k}`. -/
theorem nkpc_forward_unique {β lamv : ℝ} (hβ : |β| < 1) {μhat : ℕ → Ω → ℝ} {M : ℝ}
    (hμ : ∀ t ω, |μhat t ω| ≤ M) (hμa : 𝔼.Adapted μhat) {π : ℕ → Ω → ℝ}
    (hπ : BoundedProc π) (h17 : ∀ t, π t = β • 𝔼.E t (π (t + 1)) - lamv • μhat t) :
    π = fun t => (-lamv) • ResetPrice.forwardSum 𝔼 β μhat t := by
  obtain ⟨hsol, hb⟩ := nkpc_forward 𝔼 (lamv := lamv) hβ hμ hμa
  refine 𝔼.forward_unique hβ (u := fun t => -(lamv • μhat t)) (fun t => ?_) (fun t => ?_) hπ hb
  · rw [h17 t, sub_eq_add_neg]
  · rw [hsol t, sub_eq_add_neg]

/-- Inflation is nonnegative when markups are expected to be at or below their
desired level at every horizon (Galí (2015), p. 61). -/
theorem inflation_nonneg_of_markups_below {β lamv : ℝ} (hβ0 : 0 ≤ β)
    (hlam : 0 ≤ lamv) {μhat : ℕ → Ω → ℝ} (t : ℕ) (ω : Ω) (hneg : ∀ k, 𝔼.E t (μhat (t + k)) ω ≤ 0) :
    0 ≤ ((-lamv) • ResetPrice.forwardSum 𝔼 β μhat t) ω := by
  simp only [Pi.smul_apply, smul_eq_mul, ResetPrice.forwardSum]
  have hs : ∑' k, β ^ k * 𝔼.E t (μhat (t + k)) ω ≤ 0 :=
    tsum_nonpos fun k => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0 k) (hneg k)
  nlinarith

/-- **Footnote 4** (Galí (2015), p. 61): with real marginal cost `mc_t = ψ_t − p_t =
−μ_t` and its deviation `m̂c_t = mc_t + μ = −μ̂_t`, (17) reads
`π_t = β E_t π_{t+1} + λ m̂c_t`. -/
theorem fn4 {β lamv μ : ℝ} {p ψ π : ℕ → Ω → ℝ} (t : ℕ)
    (h17 : π t = β • 𝔼.E t (π (t + 1)) - lamv • markupGap μ p ψ t) :
    π t = β • 𝔼.E t (π (t + 1)) + lamv • ((ψ t - p t) - fun _ => -μ) := by
  rw [h17, sub_eq_add_neg, ← smul_neg]
  congr 2
  funext ω
  simp [markupGap]
  ring

/-! ### Markups and output: (18)–(21) -/

/-- **Equation (18)** (Galí (2015), p. 62): with `μ_t = p_t − ψ_t`, average marginal
cost `ψ_t = w_t − (a_t − α n_t + log(1 − α))`, labour supply (2)
`w_t − p_t = σ y_t + φ n_t` (using `c_t = y_t`) and (14) `(1 − α) n_t = y_t − a_t`,
`μ_t = −(σ + (φ + α)/(1 − α)) y_t + ((1 + φ)/(1 − α)) a_t + log(1 − α)`. -/
theorem eq18 {σ φ α w p n y a ψ μt : ℝ} (hα : α < 1) (hμ : μt = p - ψ)
    (hψ : ψ = w - (a - α * n + Real.log (1 - α))) (h2 : w - p = σ * y + φ * n)
    (h14 : (1 - α) * n = y - a) :
    μt = -(σ + (φ + α) / (1 - α)) * y + (1 + φ) / (1 - α) * a + Real.log (1 - α) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hn : n = (y - a) / (1 - α) := by field_simp; linarith
  rw [hμ, hψ, hn]
  have hw : w = p + σ * y + φ * ((y - a) / (1 - α)) := by rw [← hn]; linarith
  rw [hw]
  field_simp
  ring

/-- `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)` (Galí (2015), p. 62). -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- `ψ_y = −(1 − α)(μ − log(1 − α))/(σ(1 − α) + φ + α)` (Galí (2015), p. 62). -/
noncomputable def psiY (σ φ α μ : ℝ) : ℝ :=
  -((1 - α) * (μ - Real.log (1 - α))) / (σ * (1 - α) + φ + α)

/-- The denominator `σ(1 − α) + φ + α` is positive (Galí (2015), p. 62). -/
theorem denom_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < σ * (1 - α) + φ + α := by
  have : 0 < σ * (1 - α) := mul_pos hσ (by linarith)
  linarith

/-- **Natural output, (19) ⟺ (20)** (Galí (2015), p. 62): evaluating (18) at the
flexible-price equilibrium, where the average markup equals the desired `μ`,
`μ = −(σ + (φ + α)/(1 − α)) y^n_t + ((1 + φ)/(1 − α)) a_t + log(1 − α)` holds if and
only if `y^n_t = ψ_ya a_t + ψ_y`. -/
theorem eq19_iff_eq20 {σ φ α μ yn a : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    μ = -(σ + (φ + α) / (1 - α)) * yn + (1 + φ) / (1 - α) * a + Real.log (1 - α) ↔
      yn = psiYA σ φ α * a + psiY σ φ α μ := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hD := (denom_pos hσ hφ hα0 hα1).ne'
  unfold psiYA psiY
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- **Correction C3-1** (Galí (2015), p. 62): with a positive desired markup
`μ > 0` and `α ∈ [0, 1)`, `ψ_y < 0` (the book prints `ψ_y > 0`). -/
theorem psi_y_neg {σ φ α μ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hμ : 0 < μ) : psiY σ φ α μ < 0 := by
  unfold psiY
  have hlog : Real.log (1 - α) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have : 0 < (1 - α) * (μ - Real.log (1 - α)) := mul_pos (by linarith) (by linarith)
  exact div_neg_of_neg_of_pos (by linarith) (denom_pos hσ hφ hα0 hα1)

/-- The book's sign claim `ψ_y > 0` (Galí (2015), p. 62) is false (C3-1). -/
theorem not_psi_y_pos {σ φ α μ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hμ : 0 < μ) : ¬ 0 < psiY σ φ α μ :=
  fun h => lt_asymm h (psi_y_neg hσ hφ hα0 hα1 hμ)

/-- The log desired markup `μ = log(ε/(ε − 1))` is positive for `ε > 1`
(Galí (2015), p. 57). -/
theorem logMarkup_pos {ε : ℝ} (hε : 1 < ε) : 0 < ResetPrice.logMarkup ε :=
  Real.log_pos (ResetPrice.one_lt_markup hε)

/-- C3-1 at the book's markup: `ψ_y < 0` for `μ = log(ε/(ε − 1))`, `ε > 1`
(Galí (2015), p. 62). -/
theorem psi_y_neg_at_markup {σ φ α ε : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 1 < ε) : psiY σ φ α (ResetPrice.logMarkup ε) < 0 :=
  psi_y_neg hσ hφ hα0 hα1 (logMarkup_pos hε)

/-- **Perfect competition gives the classical output** (Galí (2015), p. 62): at
`μ = 0`, `ψ_y = (1 − α) log(1 − α)/(σ(1 − α) + φ + α)`, the constant of the
classical equilibrium output of chapter 2. -/
theorem psi_y_perfect_competition (σ φ α : ℝ) :
    psiY σ φ α 0 = (1 - α) * Real.log (1 - α) / (σ * (1 - α) + φ + α) := by
  unfold psiY
  ring

/-- **Market power lowers the level of natural output, not its slope**
(Galí (2015), p. 62): `ψ_y` is strictly decreasing in `μ`, so for `μ > 0` natural
output is below its perfect-competition level at every technology level, while
the slope `ψ_ya` does not involve `μ`. -/
theorem natural_output_lower {σ φ α μ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hμ : 0 < μ) (a : ℝ) :
    psiYA σ φ α * a + psiY σ φ α μ < psiYA σ φ α * a + psiY σ φ α 0 := by
  have hD := denom_pos hσ hφ hα0 hα1
  have : psiY σ φ α μ < psiY σ φ α 0 := by
    unfold psiY
    rw [div_lt_div_iff_of_pos_right hD]
    nlinarith
  linarith

/-- **Equation (21)** (Galí (2015), p. 62): subtracting (19) from (18),
`μ̂_t = −(σ + (φ + α)/(1 − α)) (y_t − y^n_t)`. -/
theorem eq21 {σ φ α μ μt y yn a : ℝ}
    (h18 : μt = -(σ + (φ + α) / (1 - α)) * y + (1 + φ) / (1 - α) * a + Real.log (1 - α))
    (h19 : μ = -(σ + (φ + α) / (1 - α)) * yn + (1 + φ) / (1 - α) * a + Real.log (1 - α)) :
    μt - μ = -(σ + (φ + α) / (1 - α)) * (y - yn) := by
  rw [h18, h19]; ring

/-! ### The New Keynesian Phillips curve (22) -/

/-- `κ = λ(σ + (φ + α)/(1 − α))` (Galí (2015), p. 63). -/
noncomputable def kappa (θ β α ε σ φ : ℝ) : ℝ := lam θ β α ε * (σ + (φ + α) / (1 - α))

/-- `κ > 0` (Galí (2015), p. 63). -/
theorem kappa_pos {θ β α ε σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) (hσ : 0 < σ) (hφ : 0 ≤ φ) :
    0 < kappa θ β α ε σ φ := by
  unfold kappa
  have : 0 ≤ (φ + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  exact mul_pos (lam_pos hθ0 hθ1 hβ1 hα0 hα1 hε) (by linarith)

/-- **The New Keynesian Phillips curve (22)** (Galí (2015), p. 63): combining (17)
with (21), `π_t = β E_t π_{t+1} + κ ỹ_t`, where `ỹ_t = y_t − y^n_t`. -/
theorem eq22 {θ β α ε σ φ μ : ℝ} {p ψ π ygap : ℕ → Ω → ℝ} (t : ℕ)
    (h17 : π t = β • 𝔼.E t (π (t + 1)) - lam θ β α ε • markupGap μ p ψ t)
    (h21 : markupGap μ p ψ t = (-(σ + (φ + α) / (1 - α))) • ygap t) :
    π t = β • 𝔼.E t (π (t + 1)) + kappa θ β α ε σ φ • ygap t := by
  rw [h17, h21, smul_smul, kappa, sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

/-- **The NKPC from primitives** (Galí (2015), pp. 60–63): (8), (16) and the
markup–output relations (18)–(19) at every date give
`π_t = β E_t π_{t+1} + κ ỹ_t` at every date `t ≥ 1`. -/
theorem eq22_of_primitives {θ β α ε σ φ μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {p pstar π ψ y yn a : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hπ : ∀ t, π (t + 1) = p (t + 1) - p t)
    (h8 : ∀ t, π (t + 1) = (1 - θ) • (pstar (t + 1) - p t))
    (h16 : ∀ t, pstar t = (β * θ) • 𝔼.E t (pstar (t + 1))
      + (1 - β * θ) • (p t - Theta α ε • markupGap μ p ψ t))
    (h18 : ∀ t ω, p t ω - ψ t ω = -(σ + (φ + α) / (1 - α)) * y t ω
      + (1 + φ) / (1 - α) * a t ω + Real.log (1 - α))
    (h19 : ∀ t ω, μ = -(σ + (φ + α) / (1 - α)) * yn t ω
      + (1 + φ) / (1 - α) * a t ω + Real.log (1 - α)) (t : ℕ) :
    π (t + 1) = β • 𝔼.E (t + 1) (π (t + 2))
      + kappa θ β α ε σ φ • (y (t + 1) - yn (t + 1)) := by
  have h17 := eq17 𝔼 hθ0 hθ1 hpa hπ h8 h16 t
  refine eq22 (σ := σ) (φ := φ) (ygap := fun s => y s - yn s) 𝔼 (t + 1) h17 ?_
  funext ω
  have := eq21 (h18 (t + 1) ω) (h19 (t + 1) ω)
  simp only [markupGap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

end Gali.BasicNewKeynesianModel.NKPC

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The dynamic IS equation

Galí (2015), Chapter 3, §3.3, pp. 58 and 63. Combining the consumer's Euler
equation with goods-market clearing `Y_t = C_t` gives the Euler equation in
output, eq. (13),

  `y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`.

## Main results

* `forward_sum`: iterating any forward equation `x_t = E_t x_{t+1} + f_t`
  gives the exact finite-horizon identity
  `x_t = ∑_{k<T} E_t f_{t+k} + E_t x_{t+T}`.
* `euler_forward_finite`, `euler_forward_ar1`: the forward iteration of (13)
  (p. 58); for an AR(1) preference shock the shock term is
  `σ⁻¹ (1 − ρ_zᵀ) z_t`.
* `euler_forward_tendsto`, `euler_forward_tsum`: the infinite-horizon form of
  p. 58, `y_t = σ⁻¹ z_t − σ⁻¹ ∑_k E_t (r_{t+k} − ρ) + lim_T E_t y_{t+T}`; the
  series of expected real-rate gaps converges whenever `E_t y_{t+T}` does.
* `natRate_iff`: the natural rate `r^n_t` is the only real rate at which
  output equals its natural level in (13).
* `natRate_ar1`: eq. (24), `r^n_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`.
* `euler_iff_disGap`: eq. (13) is equivalent to the DIS in gaps, eq. (23).
* `gap_forward_tendsto`, `gap_forward_tsum`: eq. (25),
  `ỹ_t = −σ⁻¹ ∑_k E_t (r_{t+k} − r^n_{t+k})` when `E_t ỹ_{t+T} → 0`.
-/

namespace Gali.BasicNewKeynesianModel.DIS

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 63: the (expected) real interest rate
`r_t ≡ i_t − E_t π_{t+1}`. -/
def realRate (i infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => i t - 𝔼.E t (infl (t + 1))

/-- Galí (2015), eq. (13), p. 58: the Euler equation in output,
`y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`. -/
def EulerOutput (σ ρ ρz : ℝ) (y i infl z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), eq. (20), p. 62: the elasticity of natural output with
respect to technology, `ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), eq. (20), p. 62: natural output `y^n_t = ψ_ya a_t + ψ_y`. -/
def natOutput (ψya ψy : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => ψya • a t + fun _ => ψy

/-- Galí (2015), p. 63: the natural rate of interest, the real rate that
supports the natural level of output in (13),
`r^n_t = ρ + σ (E_t y^n_{t+1} − y^n_t) + (1 − ρ_z) z_t`. -/
def natRate (σ ρ ρz : ℝ) (yn z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => ρ) + σ • (𝔼.E t (yn (t + 1)) - yn t) + (1 - ρz) • z t

/-- Galí (2015), eq. (23), p. 63: the dynamic IS equation in terms of the
output gap, `ỹ_t = −σ⁻¹ (i_t − E_t π_{t+1} − r^n_t) + E_t ỹ_{t+1}`. -/
def DISGap (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), p. 58 (the forward solution of (13)): an adapted solution of
`x_t = E_t x_{t+1} + f_t` satisfies, for every horizon `T`, the exact identity
`x_t = ∑_{k<T} E_t f_{t+k} + E_t x_{t+T}`. -/
theorem forward_sum {x f : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (h : ∀ t, x t = 𝔼.E t (x (t + 1)) + f t) (t T : ℕ) :
    x t = ∑ k ∈ Finset.range T, 𝔼.E t (f (t + k)) + 𝔼.E t (x (t + T)) := by
  induction T with
  | zero => simp [hx t]
  | succ T ih =>
    rw [ih, h (t + T), map_add, 𝔼.tower (Nat.le_add_right t T), Finset.sum_range_succ,
      ← add_assoc t T 1]
    abel

/-- Galí (2015), p. 58: the forward iteration of (13) over a finite horizon
`T`, an exact identity:
`y_t = ∑_{k<T} σ⁻¹ (1 − ρ_z) E_t z_{t+k} − σ⁻¹ ∑_{k<T} E_t (r_{t+k} − ρ) + E_t y_{t+T}`. -/
theorem euler_forward_finite {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hy : 𝔼.Adapted y)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t T : ℕ) :
    y t = ∑ k ∈ Finset.range T, (σ⁻¹ * (1 - ρz)) • 𝔼.E t (z (t + k))
      - σ⁻¹ • ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
      + 𝔼.E t (y (t + T)) := by
  have hf : ∀ s, y s = 𝔼.E s (y (s + 1))
      + ((σ⁻¹ * (1 - ρz)) • z s - σ⁻¹ • (realRate 𝔼 i infl s - fun _ => ρ)) := by
    intro s
    rw [h s, realRate]
    abel
  rw [forward_sum 𝔼 hy hf t T]
  simp only [map_sub, map_smul, Finset.sum_sub_distrib, smul_sub, Finset.smul_sum]

/-- Galí (2015), p. 58: for an AR(1) preference shock (`E_t z_{t+1} = ρ_z z_t`)
the forward iteration of (13) over `T` periods reads
`y_t = σ⁻¹ (1 − ρ_zᵀ) z_t − σ⁻¹ ∑_{k<T} E_t (r_{t+k} − ρ) + E_t y_{t+T}`. -/
theorem euler_forward_ar1 {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hy : 𝔼.Adapted y)
    (hz : 𝔼.IsAR1 ρz z) (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t T : ℕ) :
    y t = (σ⁻¹ * (1 - ρz ^ T)) • z t
      - σ⁻¹ • ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
      + 𝔼.E t (y (t + T)) := by
  rw [euler_forward_finite 𝔼 hy h t T]
  congr 2
  simp only [𝔼.ar1_iterate hz, smul_smul, ← Finset.sum_smul]
  have hg : (1 - ρz) * ∑ k ∈ Finset.range T, ρz ^ k = 1 - ρz ^ T := by
    linear_combination -(geom_sum_mul ρz T)
  rw [← Finset.mul_sum, mul_assoc, hg]

/-- Galí (2015), p. 58: if `E_t y_{t+T}` converges to `L` as `T → ∞` and
`|ρ_z| < 1`, the partial sums of expected real-rate gaps converge, with
`∑_{k<T} E_t (r_{t+k} − ρ) → z_t − σ (y_t − L)`. -/
theorem euler_forward_tendsto {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hρz : |ρz| < 1) (hy : 𝔼.Adapted y) (hz : 𝔼.IsAR1 ρz z)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t : ℕ) {L : Ω → ℝ}
    (hlim : Tendsto (fun T => 𝔼.E t (y (t + T))) atTop (𝓝 L)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ))
      atTop (𝓝 (z t - σ • (y t - L))) := by
  have hid : ∀ T, ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
      = (1 - ρz ^ T) • z t - σ • (y t - 𝔼.E t (y (t + T))) := by
    intro T
    have e := euler_forward_ar1 𝔼 hy hz h t T
    set S := ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp at e'
    linear_combination e'
  have hp : Tendsto (fun T : ℕ => (1 : ℝ) - ρz ^ T) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρz)
  have hlim' := (hp.smul_const (z t)).sub
    (((tendsto_const_nhds (x := y t)).sub hlim).const_smul σ)
  rw [one_smul] at hlim'
  exact hlim'.congr fun T => (hid T).symm

/-- Galí (2015), p. 58: the infinite-horizon forward solution of (13),
`y_t = σ⁻¹ z_t − σ⁻¹ ∑_{k ≥ 0} E_t (r_{t+k} − ρ) + lim_T E_t y_{t+T}`, for a
summable series of expected real-rate gaps. -/
theorem euler_forward_tsum {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hρz : |ρz| < 1) (hy : 𝔼.Adapted y) (hz : 𝔼.IsAR1 ρz z)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t : ℕ) {L : Ω → ℝ}
    (hlim : Tendsto (fun T => 𝔼.E t (y (t + T))) atTop (𝓝 L))
    (hs : Summable fun k => 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)) :
    y t = σ⁻¹ • z t - σ⁻¹ • ∑' k, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ) + L := by
  have h1 := euler_forward_tendsto 𝔼 hσ hρz hy hz h t hlim
  rw [tendsto_nhds_unique hs.hasSum.tendsto_sum_nat h1]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), p. 58: the forward solution of (13) under
`lim_T E_t y_{t+T} = 0`: `y_t = σ⁻¹ z_t − σ⁻¹ ∑_{k ≥ 0} E_t (r_{t+k} − ρ)`, and
the partial sums converge to `z_t − σ y_t`. -/
theorem euler_forward_limit_zero {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hρz : |ρz| < 1) (hy : 𝔼.Adapted y) (hz : 𝔼.IsAR1 ρz z)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t : ℕ)
    (hlim : Tendsto (fun T => 𝔼.E t (y (t + T))) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ))
        atTop (𝓝 (z t - σ • y t)) ∧
      ((Summable fun k => 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)) →
        y t = σ⁻¹ • z t - σ⁻¹ • ∑' k, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)) := by
  refine ⟨by simpa using euler_forward_tendsto 𝔼 hσ hρz hy hz h t hlim, fun hs => ?_⟩
  simpa using euler_forward_tsum 𝔼 hσ hρz hy hz h t hlim hs

/-- Galí (2015), p. 63: output equals its natural level in (13) at date `t`
if and only if the real rate equals the natural rate `r^n_t`. -/
theorem natRate_iff {σ ρ ρz : ℝ} (hσ : σ ≠ 0) (yn i infl z : ℕ → Ω → ℝ) (t : ℕ) :
    (yn t = 𝔼.E t (yn (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
        + (σ⁻¹ * (1 - ρz)) • z t) ↔ realRate 𝔼 i infl t = natRate 𝔼 σ ρ ρz yn z t := by
  unfold realRate natRate
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp
    linear_combination e

/-- Galí (2015), eq. (24), p. 63: when technology follows an AR(1) process with
persistence `ρ_a` and natural output is `y^n_t = ψ_ya a_t + ψ_y`, the natural
rate is `r^n_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`. -/
theorem natRate_ar1 {σ ρ ρz ρa ψya ψy : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (z : ℕ → Ω → ℝ) (t : ℕ) :
    natRate 𝔼 σ ρ ρz (natOutput ψya ψy a) z t
      = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t := by
  unfold natRate natOutput
  rw [map_add, map_smul, 𝔼.const, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (23), p. 63: with the output gap `ỹ_t = y_t − y^n_t` and
the natural rate `r^n`, the Euler equation (13) is equivalent to the DIS
equation in gaps. -/
theorem euler_iff_disGap {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {y yn ygap i infl z : ℕ → Ω → ℝ}
    (hgap : ∀ t, ygap t = y t - yn t) :
    EulerOutput 𝔼 σ ρ ρz y i infl z ↔ DISGap 𝔼 σ ygap i infl (natRate 𝔼 σ ρ ρz yn z) := by
  unfold EulerOutput DISGap natRate
  simp only [hgap, map_sub]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e

/-- Galí (2015), eq. (25), p. 63: if `E_t ỹ_{t+T} → 0`, the partial sums of
expected real-rate gaps `∑_{k<T} E_t (r_{t+k} − r^n_{t+k})` converge to
`−σ ỹ_t`. -/
theorem gap_forward_tendsto {σ : ℝ} {ygap i infl rn : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hy : 𝔼.Adapted ygap) (h : DISGap 𝔼 σ ygap i infl rn) (t : ℕ)
    (hlim : Tendsto (fun T => 𝔼.E t (ygap (t + T))) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k)))
      atTop (𝓝 (-σ • ygap t)) := by
  have hf : ∀ s, ygap s = 𝔼.E s (ygap (s + 1)) + (-σ⁻¹) • (realRate 𝔼 i infl s - rn s) := by
    intro s
    rw [h s, realRate, neg_smul]
    abel
  have hid : ∀ T, ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k))
      = -σ • (ygap t - 𝔼.E t (ygap (t + T))) := by
    intro T
    have e := forward_sum 𝔼 hy hf t T
    simp only [map_smul, ← Finset.smul_sum] at e
    set S := ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k))
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp at e'
    linear_combination e'
  have hlim' := ((tendsto_const_nhds (x := ygap t)).sub hlim).const_smul (-σ)
  rw [sub_zero] at hlim'
  exact hlim'.congr fun T => (hid T).symm

/-- Galí (2015), eq. (25), p. 63: under `lim_T E_t ỹ_{t+T} = 0`, and for a
summable series, `ỹ_t = −σ⁻¹ ∑_{k ≥ 0} E_t (r_{t+k} − r^n_{t+k})`. -/
theorem gap_forward_tsum {σ : ℝ} {ygap i infl rn : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hy : 𝔼.Adapted ygap) (h : DISGap 𝔼 σ ygap i infl rn) (t : ℕ)
    (hlim : Tendsto (fun T => 𝔼.E t (ygap (t + T))) atTop (𝓝 0))
    (hs : Summable fun k => 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k))) :
    ygap t = -σ⁻¹ • ∑' k, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k)) := by
  rw [tendsto_nhds_unique hs.hasSum.tendsto_sum_nat (gap_forward_tendsto 𝔼 hσ hy h t hlim)]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end Gali.BasicNewKeynesianModel.DIS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The household problem and the Euler equation

Galí (2015), Chapter 3, §3.1 (pp. 52–54), eqs. (2)–(3), reusing Chapter 2, §2.1
(pp. 18–22), eqs. (4)–(5) and (7)–(10); the goods-market link to eq. (13), p. 58; and the
production side of eq. (14), p. 59.

## The household

Period utility (p. 54) is `U(C, N; Z) = ((C^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)) Z` for
`σ ≠ 1` and `(log C − N^{1+φ}/(1+φ)) Z` for `σ = 1`, with `σ > 0`, `φ ≥ 0`, `Z > 0`
(`periodUtility`). Both optimality conditions are derived from Galí's variational argument
(pp. 19–20).

* **Static problem** (labour supply). Holding everything else fixed, a change of hours is
  financed one-for-one in consumption, `P dC = W dN`: the household chooses `N ≥ 0` on the
  budget line `P C = W N + X` (`X` collects the unchanged bond and dividend terms).
  `static_foc_necessary`: a local optimum with `C, N > 0` satisfies `W/P = N^φ C^σ` (ch. 2,
  eq. (7)); `static_foc_sufficient`: by concavity the condition implies a global optimum;
  `static_optimum_iff` combines them. `labour_supply_log_iff`: eq. (2), `w − p = σ c + φ n`,
  exactly in logs.
* **Intertemporal problem** (Euler equation). Buying `δ` more bonds at date `t` lowers
  consumption by `Q_t δ/P_t` and raises date-`t+1` consumption by `δ/P_{t+1}` in every state
  (`perturbedValue`). `euler_necessary`: if no small perturbation is profitable at any
  date-`t` node, then `Q_t = β (C_t^σ P_t/Z_t) E_t[C_{t+1}^{−σ} Z_{t+1}/P_{t+1}]` at every
  node (`EulerEq`), i.e. `Q_t = β E_t[(C_{t+1}/C_t)^{−σ}(Z_{t+1}/Z_t)(P_t/P_{t+1})]`
  (`eulerEq_ratio_form`). `euler_sufficient`: conversely no feasible perturbation is
  profitable when the Euler equation holds.

## Expectations

Everything is stated for an arbitrary `ExpectationSystem` (a linear, monotone,
constant-preserving `E_t` with the tower property), so the results hold under perfect
foresight and under uncertainty. The abstract `E_t` cannot be assumed to commute with
limits, so the Euler necessity proof never differentiates under `E_t`: it sandwiches the
date-`t+1` utility gain between tangent lines of the concave utility (only monotonicity and
linearity of `E_t` are used) under a uniform lower bound `m ≤ P_{t+1} C_{t+1}` on next
period's nominal expenditure; such a bound always exists when `Ω` is finite
(`exists_expenditure_lower_bound`, `euler_necessary_finite`). Date-`t` variables enter
`EulerEq` as numbers at the node `ω`, which is how a node-by-node optimality condition reads
and avoids any "taking out what is known" property that `ExpectationSystem` does not provide.

## Log-linear forms

* `eulerEq_iff_moment` (**exact**): with `Q = e^{−i}`, `β = e^{−ρ}`, `C = e^c`, `P = e^p`,
  `Z = e^z`, the Euler equation is `E_t[exp(i_t − ρ − σΔc_{t+1} − Δp_{t+1} + Δz_{t+1})] = 1`.
* `pf_eulerEq_iff` (**exact**, perfect foresight):
  `i_t − π_{t+1} − ρ = σ(c_{t+1} − c_t) − (z_{t+1} − z_t)`; `pf_eulerEq_iff_noshock`: with no
  preference shock, `i_t − π_{t+1} − ρ = σ(c_{t+1} − c_t)`.
* `hasDerivAt_log_E_exp`, `hasDerivAt_log_eulerMoment_family` (**first order**, uncertainty):
  along the family of paths `i = ρ + s î`, `c = c̄ + s ĉ`, `p = p̄ + s p̂`, `z = s ẑ` (bounded
  deviations, zero-inflation steady state at `s = 0`, `eulerMoment_family_zero`), the map
  `s ↦ log E_t[exp(i_t − ρ − σΔc − Δp + Δz)]` has derivative at `0` equal to
  `î_t − σ(E_t ĉ_{t+1} − ĉ_t) − E_t π̂_{t+1} + (E_t ẑ_{t+1} − ẑ_t)`
  (`linearisedEuler`, `linearisedEuler_eq`), and `linearisedEuler_eq_zero_iff`: for AR(1)
  `ẑ` this derivative vanishes at every date iff eq. (3) holds (`EulerLogLinear`).
* `pf_eulerEq_imp_eulerLogLinear`: under perfect foresight eq. (3) holds exactly.

## Goods market and production

* `eulerOutput_iff_of_clearing`: with `Y_t = C_t` (eq. (12)) eq. (3) is exactly
  `DIS.EulerOutput`, eq. (13); `pf_eulerEq_imp_eulerOutput` chains the nonlinear Euler
  equation under perfect foresight into (13).
* `employment_log_identity`: `Y(i) = A N(i)^{1−α}` on the demand schedule gives exactly
  `(1 − α) n = y − a + d`, `d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di` (p. 59).
-/

namespace Gali.BasicNewKeynesianModel.Household

open Filter Topology MeasureTheory

/-! ### Period utility -/

/-- Galí (2015), p. 54 (and ch. 2, p. 20): utility of consumption, `(C^{1−σ} − 1)/(1 − σ)`
for `σ ≠ 1` and `log C` for `σ = 1`. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 54: disutility of labour `N^{1+φ}/(1+φ)`. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 54: period utility `U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), ch. 2, eq. (7), p. 21: marginal utility of consumption, `u'(C) = C^{−σ}`,
in both the `σ ≠ 1` and the log case. -/
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

/-- Galí (2015), ch. 2, eq. (7), p. 21: marginal disutility of labour, `N^φ`. -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), ch. 2, p. 18 (`U_cc ≤ 0`): marginal utility `C^{−σ}` is nonincreasing for
`σ > 0`. -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (used for Galí (2015), ch. 2, p. 18, concavity of utility). -/
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

/-- Galí (2015), ch. 2, p. 18: the utility of consumption is concave for `σ > 0`, in the
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

/-- Galí (2015), ch. 2, p. 18: the disutility of labour is convex for `φ ≥ 0`, in the
tangent-line form `v(x) + x^φ (y − x) ≤ v(y)` for `x > 0`, `y ≥ 0`. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-! ### The static (labour-supply) problem -/

/-- Galí (2015), ch. 2, eq. (4), p. 19, and eq. (7), p. 21 (**necessity**): if hours `N > 0`
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

/-- Galí (2015), ch. 2, p. 19: a global optimum of the static problem over all feasible
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

/-- Galí (2015), ch. 2, eq. (7), p. 21 (**sufficiency**, by concavity): if `W/P = N^φ C^σ`
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

/-- Galí (2015), ch. 2, eqs. (4) and (7), pp. 19–21: for `σ > 0`, `φ ≥ 0`, a point with
`C, N > 0` on the budget line solves the static problem iff `W/P = N^φ C^σ`. -/
theorem static_optimum_iff {σ φ P W X Z C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hZ : 0 < Z) (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z) ↔
      W / P = N ^ φ * C ^ σ :=
  ⟨fun h => static_foc_necessary hφ hP hZ hC hbud
      (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hσ hφ hP hZ hN hC hbud h hN' hC'⟩

/-- Galí (2015), eq. (2), p. 54 (ch. 2, eq. (9), p. 21), **exact**: for positive levels,
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

/-- Galí (2015), p. 54 (ch. 2, eqs. (5) and (8), pp. 19–21): the consumption Euler equation
at date `t`, node by node, with the date-`t` variables taken out of `E_t` as numbers:
`Q_t = β (C_t^σ P_t / Z_t) E_t[C_{t+1}^{−σ} Z_{t+1} / P_{t+1}]`. -/
def EulerEq (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω = β * (C t ω ^ σ * P t ω / Z t ω) *
    𝔼.E t (fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') ω

/-- Galí (2015), p. 54 (ch. 2, eq. (8), p. 21): at each node the Euler equation reads
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

/-- Galí (2015), ch. 2, p. 20: expected utility as of date `t` (node `ω`) of the one-period
perturbation that buys `δ` more bonds at `t` (consumption falls by `Q_t δ/P_t`) and consumes
the payoff `δ` at `t + 1` (consumption rises by `δ/P_{t+1}` in every state); hours and all
other dates are unchanged, so by separability only these two terms of
`E_t ∑ β^k U_{t+k}` change. -/
noncomputable def perturbedValue (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => Z t ω * utilC σ (C t ω - Q t ω * δ / P t ω)
    + β * 𝔼.E t (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω')) ω

/-- The concavity sandwich behind Galí (2015), ch. 2, p. 20: for `|δ| < m ≤ P C`, the
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

/-- Galí (2015), ch. 2, eqs. (5) and (8), pp. 19–21 (**necessity of the Euler equation**):
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

/-- Galí (2015), ch. 2, p. 20: with finitely many states, positive `C_{t+1}` and `P_{t+1}`
have a uniform lower bound `m > 0` on next period's nominal expenditure `P_{t+1} C_{t+1}`. -/
theorem exists_expenditure_lower_bound [Finite Ω] {C P : Ω → ℝ} (hC : ∀ ω, 0 < C ω)
    (hP : ∀ ω, 0 < P ω) : ∃ m, 0 < m ∧ ∀ ω, m ≤ P ω * C ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
  · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P ω * C ω
    exact ⟨P ω₀ * C ω₀, mul_pos (hP ω₀) (hC ω₀), h₀⟩

/-- Galí (2015), ch. 2, eqs. (5) and (8), pp. 19–21 (**necessity**, finitely many states):
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

/-- Galí (2015), ch. 2, eqs. (5) and (8), pp. 19–21 (**sufficiency** for one-period
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

/-! ### Log forms of the Euler equation -/

/-- Galí (2015), p. 54 and ch. 2, App. 2.1, p. 44: the Euler moment at node `ω`,
`E_t[exp(i_t − ρ − σ(c_{t+1} − c_t) − (p_{t+1} − p_t) + (z_{t+1} − z_t))]`, all variables
in logs, date-`t` values entering as numbers. -/
noncomputable def eulerMoment (σ ρ : ℝ) (i c p z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
    - (p (t + 1) ω' - p t ω) + (z (t + 1) ω' - z t ω))) ω

/-- Galí (2015), p. 54 (ch. 2, eq. (8), p. 21), **exact**: with `Q = e^{−i}`, `β = e^{−ρ}`,
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

/-- Galí (2015), p. 54 and ch. 2, p. 21 (**exact, perfect foresight**): under perfect
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

/-- Galí (2015), p. 54 (**exact, perfect foresight, no preference shock**): with `Z ≡ 1` the
Euler equation is exactly `i_t − π_{t+1} − ρ = σ (c_{t+1} − c_t)` in logs. -/
theorem pf_eulerEq_iff_noshock (σ ρ : ℝ) (i c p : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω)) (fun _ _ => 1) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ = σ * (c (t + 1) ω - c t ω) := by
  have h := pf_eulerEq_iff σ ρ i c p (fun _ _ => 0) t
  simp only [Real.exp_zero, sub_self, sub_zero] at h
  exact h

/-! ### The first-order approximation under uncertainty -/

/-- Galí (2015), ch. 2, App. 2.1, p. 44 (the first-order step): for a bounded random variable
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

/-- Galí (2015), ch. 2, App. 2.1, p. 44: for a bounded `Y`,
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

/-- Galí (2015), p. 54, eq. (3): the linear expression obtained by linearising the Euler
moment around the zero-inflation steady state, in deviations (hats):
`î_t − σ (E_t ĉ_{t+1} − ĉ_t) − (E_t p̂_{t+1} − p̂_t) + (E_t ẑ_{t+1} − ẑ_t)`. -/
noncomputable def linearisedEuler (σ : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
    + (𝔼.E t (zh (t + 1)) ω - zh t ω)

/-- Galí (2015), p. 55: at the zero-inflation steady state (`i = ρ`, constant `c̄`, `p̄`,
`z = 0`), the Euler moment equals one: the steady state satisfies the Euler equation. -/
theorem eulerMoment_family_zero (σ ρ cbar pbar : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    eulerMoment 𝔼 σ ρ (fun t ω => ρ + 0 * ih t ω) (fun t ω => cbar + 0 * ch t ω)
      (fun t ω => pbar + 0 * ph t ω) (fun t ω => 0 * zh t ω) t ω = 1 := by
  simp only [eulerMoment, zero_mul, add_zero, sub_self, mul_zero, Real.exp_zero]
  rw [𝔼.const]

/-- Galí (2015), p. 54, eq. (3), as an **exact derivative** (ch. 2, App. 2.1, p. 44): along
the family of stochastic paths `i = ρ + s î`, `c = c̄ + s ĉ`, `p = p̄ + s p̂`, `z = s ẑ` around
the zero-inflation steady state, with bounded deviations, the log Euler residual
`s ↦ log E_t[exp(i_t − ρ − σΔc − Δp + Δz)](ω)` has derivative at `s = 0` equal to
`linearisedEuler σ î ĉ p̂ ẑ t ω`. -/
theorem hasDerivAt_log_eulerMoment_family (σ ρ cbar pbar : ℝ) {ih ch ph zh : ℕ → Ω → ℝ}
    (hc : BoundedProc ch) (hp : BoundedProc ph) (hz : BoundedProc zh) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (eulerMoment 𝔼 σ ρ (fun t ω => ρ + s * ih t ω)
        (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
        (fun t ω => s * zh t ω) t ω))
      (linearisedEuler 𝔼 σ ih ch ph zh t ω) 0 := by
  obtain ⟨Mc, hMc⟩ := hc
  obtain ⟨Mp, hMp⟩ := hp
  obtain ⟨Mz, hMz⟩ := hz
  set a : ℝ := ih t ω + σ * ch t ω + ph t ω - zh t ω with ha
  set Y : Ω → ℝ := fun ω' => a + (-σ * ch (t + 1) ω' - ph (t + 1) ω' + zh (t + 1) ω') with hY
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
  have hfam : ∀ s : ℝ, eulerMoment 𝔼 σ ρ (fun t ω => ρ + s * ih t ω)
      (fun t ω => cbar + s * ch t ω) (fun t ω => pbar + s * ph t ω)
      (fun t ω => s * zh t ω) t ω = 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω := by
    intro s
    unfold eulerMoment
    refine congrArg (fun x => 𝔼.E t x ω) (funext fun ω' => ?_)
    congr 1
    simp only [hY, ha]
    ring
  simp_rw [hfam]
  have hval : 𝔼.E t Y ω = linearisedEuler 𝔼 σ ih ch ph zh t ω := by
    have hfun : Y = (fun _ => a) + ((-σ) • ch (t + 1) - ph (t + 1) + zh (t + 1)) := by
      funext ω'
      simp [hY, smul_eq_mul]
    rw [hfun, map_add, 𝔼.const, map_add, map_sub, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, linearisedEuler, ha]
    ring
  rw [← hval]
  exact hasDerivAt_log_E_exp 𝔼 hbd t ω

/-- Galí (2015), p. 54, eq. (3): the log-linear Euler equation as a model equation,
`c_t = E_t c_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`. -/
def EulerLogLinear (σ ρ ρz : ℝ) (c i infl z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), p. 54: for an adapted (log) price level `p̂` with inflation
`π̂_{t+1} = p̂_{t+1} − p̂_t`, the linearised Euler expression is
`î_t − σ (E_t ĉ_{t+1} − ĉ_t) − E_t π̂_{t+1} + (E_t ẑ_{t+1} − ẑ_t)`. -/
theorem linearisedEuler_eq (σ : ℝ) {ih ch ph zh infl : ℕ → Ω → ℝ} (hp : 𝔼.Adapted ph)
    (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) (t : ℕ) :
    linearisedEuler 𝔼 σ ih ch ph zh t = ih t - σ • (𝔼.E t (ch (t + 1)) - ch t)
      - 𝔼.E t (infl (t + 1)) + (𝔼.E t (zh (t + 1)) - zh t) := by
  funext ω
  rw [hinfl, map_sub, hp t]
  simp [linearisedEuler]

/-- Galí (2015), p. 54, eq. (3) (**the first-order condition is exactly (3)**): for `σ ≠ 0`,
an adapted price level and an AR(1) preference shifter (`E_t ẑ_{t+1} = ρ_z ẑ_t`), the
linearised Euler expression vanishes at every date and node iff eq. (3) holds for the
deviations with `i_t = ρ + î_t`. -/
theorem linearisedEuler_eq_zero_iff {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {ih ch ph zh infl : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted ph) (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t)
    (hzar : 𝔼.IsAR1 ρz zh) :
    (∀ t, linearisedEuler 𝔼 σ ih ch ph zh t = 0) ↔
      EulerLogLinear 𝔼 σ ρ ρz ch (fun t => (fun _ => ρ) + ih t) infl zh := by
  unfold EulerLogLinear
  refine forall_congr' fun t => ?_
  rw [linearisedEuler_eq 𝔼 σ hp hinfl t, hzar.2 t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    field_simp at e
    linear_combination e

/-- Galí (2015), p. 54, eq. (3): (3) for log consumption `c̄ + ĉ` is equivalent to (3) for
the deviation `ĉ`, since `E_t` leaves constants unchanged. -/
theorem eulerLogLinear_add_const_iff (σ ρ ρz cbar : ℝ) (ch i infl z : ℕ → Ω → ℝ) :
    EulerLogLinear 𝔼 σ ρ ρz (fun t => (fun _ => cbar) + ch t) i infl z ↔
      EulerLogLinear 𝔼 σ ρ ρz ch i infl z := by
  unfold EulerLogLinear
  refine forall_congr' fun t => ?_
  rw [map_add, 𝔼.const]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith

/-- Galí (2015), p. 54, eq. (3) (**exact under perfect foresight**): if the nonlinear Euler
equation holds at every date, `π_{t+1} = p_{t+1} − p_t`, and the preference shifter follows
`z_{t+1} = ρ_z z_t`, then (3) holds exactly (`σ ≠ 0`). -/
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

/-! ### Goods-market clearing and the Euler equation in output -/

/-- Galí (2015), eqs. (12)–(13), p. 58 (**exact**): with goods-market clearing `Y_t = C_t`
(so `y_t = c_t` in logs), the log-linear Euler equation (3) in consumption is exactly the
Euler equation in output `DIS.EulerOutput`, eq. (13). -/
theorem eulerOutput_iff_of_clearing {σ ρ ρz : ℝ} {Y C y c i infl z : ℕ → Ω → ℝ}
    (hclear : ∀ t, Y t = C t) (hy : ∀ t ω, y t ω = Real.log (Y t ω))
    (hc : ∀ t ω, c t ω = Real.log (C t ω)) :
    DIS.EulerOutput 𝔼 σ ρ ρz y i infl z ↔ EulerLogLinear 𝔼 σ ρ ρz c i infl z := by
  have hyc : y = c := by
    funext t ω
    rw [hy, hc, hclear]
  subst hyc
  rfl

/-- Galí (2015), eqs. (3), (12) and (13), pp. 54 and 58: the log-linear Euler equation (3)
together with goods-market clearing `Y_t = C_t` implies the Euler equation in output (13). -/
theorem eulerOutput_of_eulerLogLinear {σ ρ ρz : ℝ} {Y C y c i infl z : ℕ → Ω → ℝ}
    (hclear : ∀ t, Y t = C t) (hy : ∀ t ω, y t ω = Real.log (Y t ω))
    (hc : ∀ t ω, c t ω = Real.log (C t ω)) (h3 : EulerLogLinear 𝔼 σ ρ ρz c i infl z) :
    DIS.EulerOutput 𝔼 σ ρ ρz y i infl z :=
  (eulerOutput_iff_of_clearing 𝔼 hclear hy hc).2 h3

/-- Galí (2015), eq. (13), p. 58 (**exact under perfect foresight**): the nonlinear Euler
equation at every date, `π_{t+1} = p_{t+1} − p_t` and an AR(1) preference shifter give
exactly the Euler equation in output (13) for `y = c`, i.e. under goods-market clearing
`Y_t = C_t` (see `eulerOutput_iff_of_clearing`). -/
theorem pf_eulerEq_imp_eulerOutput {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {i c p z infl : ℕ → Unit → ℝ}
    (heul : ∀ t, EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
      (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
      (fun t ω => Real.exp (z t ω)) t)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (hz : ∀ t, z (t + 1) = ρz • z t) :
    DIS.EulerOutput perfectForesight σ ρ ρz c i infl z :=
  pf_eulerEq_imp_eulerLogLinear hσ heul hinfl hz

/-! ### The production side of eq. (14) -/

/-- Galí (2015), p. 59 (**exact**): with firms forming a measure space `(F, μ)`, production
`Y(i) = A N(i)^{1−α}` (eq. (5)), output on the demand schedule `Y(i) = (P(i)/P)^{−ε} Y` and
aggregate employment `N = ∫ N(i) di`, one has exactly
`(1 − α) log N = log Y − log A + d`, with the dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. Here `P > 0` is any aggregate price level. -/
theorem employment_log_identity {F : Type*} [MeasurableSpace F] {μ : Measure F}
    {α ε A Y P : ℝ} {Pi Yi Ni : F → ℝ} (hα : α < 1) (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P)
    (hPi : ∀ i, 0 < Pi i) (hN : ∀ i, 0 ≤ Ni i)
    (hdem : ∀ i, Yi i = (Pi i / P) ^ (-ε) * Y) (hprod : ∀ i, Yi i = A * Ni i ^ (1 - α))
    (hD : 0 < ∫ i, (Pi i / P) ^ (-ε / (1 - α)) ∂μ) :
    (1 - α) * Real.log (∫ i, Ni i ∂μ)
      = Real.log Y - Real.log A + (1 - α) * Real.log (∫ i, (Pi i / P) ^ (-ε / (1 - α)) ∂μ) := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  have hpt : ∀ i, Ni i = (Y / A) ^ (1 - α)⁻¹ * (Pi i / P) ^ (-ε / (1 - α)) := by
    intro i
    have ha : 0 < Pi i / P := div_pos (hPi i) hP
    have h1 : Ni i ^ (1 - α) = (Pi i / P) ^ (-ε) * (Y / A) := by
      have := (hdem i).symm.trans (hprod i)
      field_simp
      linarith
    rw [← Real.rpow_rpow_inv (hN i) hsub, h1, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha.le, div_eq_mul_inv (-ε), mul_comm]
  simp_rw [hpt]
  rw [integral_const_mul, Real.log_mul (by positivity) hD.ne', Real.log_rpow (by positivity),
    Real.log_div hY.ne' hA.ne']
  field_simp

end Gali.BasicNewKeynesianModel.Household

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibrium under a simple interest-rate rule

Galí (2015), Chapter 3, §3.4.1, pp. 64–66. The non-policy block of the basic
New Keynesian model is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` (eq. (22), with
`κ > 0` a parameter) and the DIS equation (23). Monetary policy follows the
Taylor-type rule (26), `i_t = ρ + φ_π π_t + φ_y ŷ_t + v_t`.

## Main results

* `taylorRule_iff_gap`: the rule rewritten with the output gap (p. 65).
* `equilibrium_iff_solves`: the NKPC, the DIS and the rule hold if and only
  if `(ỹ, π)` solves the system (27), `x_t = A_T E_t x_{t+1} + B_T u_t`, with
  `A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]` and `Ω = 1/(σ + φ_y + κφ_π)`.
* `schurStable_AT_iff` (**Bullard–Mitra**): for `σ, κ > 0`, `0 < β < 1` and
  `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit circle iff
  `κ (φ_π − 1) + (1 − β) φ_y > 0`, condition (28).
* `determinate_iff_BM`, `equilibrium_unique`, `equilibrium_not_unique`: the
  equilibrium is determinate iff (28) holds; under (28) bounded equilibria
  coincide, and without it every bounded equilibrium has a second one.
* `msvLambda_pos`, `msv_structural`, `equilibrium_iff_msv`: for an AR(1)
  composite shock `u` the MSV solution (29)–(30), `ỹ_t = (1 − βρ_u) Λ_u u_t`,
  `π_t = κ Λ_u u_t`, has `Λ_u > 0` under (28) for every `ρ_u < 1` and is the unique bounded
  equilibrium.
-/

namespace Gali.BasicNewKeynesianModel.TaylorRuleSystem

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (22), p. 63: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (26), p. 64: the interest-rate rule
`i_t = ρ + φ_π π_t + φ_y ŷ_t + v_t`, with `ŷ_t` the deviation of output from
its steady-state value. -/
def TaylorRule (ρ φπ φy : ℝ) (i infl yhat v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • yhat t + v t

/-- Galí (2015), p. 65: the rule (26) in terms of the output gap,
`i_t = ρ + φ_π π_t + φ_y ỹ_t + φ_y ŷ^n_t + v_t`. -/
def TaylorRuleGap (ρ φπ φy : ℝ) (i infl ygap yhatn v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yhatn t + v t

/-- Galí (2015), p. 65: since `ŷ_t = ỹ_t + ŷ^n_t`, rule (26) is the same as
its output-gap form. -/
theorem taylorRule_iff_gap {ρ φπ φy : ℝ} {i infl yhat ygap yhatn v : ℕ → Ω → ℝ}
    (hyhat : ∀ t, yhat t = ygap t + yhatn t) :
    TaylorRule ρ φπ φy i infl yhat v ↔ TaylorRuleGap ρ φπ φy i infl ygap yhatn v := by
  simp only [TaylorRule, TaylorRuleGap, hyhat, smul_add, add_assoc]

/-- Galí (2015), p. 65: the composite shock of system (27),
`u_t = r̂^n_t − φ_y ŷ^n_t − v_t` with `r̂^n_t = r^n_t − ρ`. -/
def shockU (ρ φy : ℝ) (rn yhatn v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - (fun _ => ρ) - φy • yhatn t - v t

/-- Galí (2015), §3.4.1, pp. 63–65: an equilibrium under the interest-rate rule:
the NKPC (22), the DIS (23) and the rule (26) in gap form. -/
def Equilibrium (β σ κ ρ φπ φy : ℝ) (rn yhatn v ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS.DISGap 𝔼 σ ygap i infl rn ∧
    TaylorRuleGap ρ φπ φy i infl ygap yhatn v

/-- Galí (2015), §3.4.1, p. 65: the equilibrium conditions with the interest
rate substituted out, `(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1} + u_t`
together with the NKPC. -/
def Structural (β σ κ φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (σ + φy) • ygap t + φπ • infl t
      = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), p. 65: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (27), p. 65: the matrix
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), eq. (27), p. 65: the vector `B_T = Ω (1, κ)`. -/
noncomputable def BT (σ κ φπ φy : ℝ) : Fin 2 → ℝ := ![omega σ κ φπ φy, omega σ κ φπ φy * κ]

/-- Galí (2015), eq. (27): the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (27): the forcing term `B u_t` of the system. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), §3.4.1, p. 65: with the rule in gap form, the NKPC and the
DIS hold if and only if the structural equations hold with the composite shock
`u_t = r̂^n_t − φ_y ŷ^n_t − v_t`. -/
theorem nk_iff_structural {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0)
    {rn yhatn v ygap infl i : ℕ → Ω → ℝ} (hrule : TaylorRuleGap ρ φπ φy i infl ygap yhatn v) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS.DISGap 𝔼 σ ygap i infl rn) ↔
      Structural 𝔼 β σ κ φπ φy (shockU ρ φy rn yhatn v) ygap infl := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σ * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σ⁻¹ * e + σ⁻¹ * r
      - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), eq. (27), p. 65: the structural equations are equivalent to
`x_t = A_T E_t x_{t+1} + B_T u_t` for `x_t = (ỹ_t, π_t)`, provided
`σ + φ_y + κ φ_π ≠ 0`. -/
theorem structural_iff_solves {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0)
    (u ygap infl : ℕ → Ω → ℝ) :
    Structural 𝔼 β σ κ φπ φy u ygap infl ↔
      𝔼.Solves (AT β σ κ φπ φy) (forcing (BT σ κ φπ φy) u) (stack ygap infl) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination e1 - φπ * e2
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination κ * e1 + (σ + φy) * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, Fin.isValue, Matrix.cons_val_zero, AT, omega, one_div, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, forcing, BT] at h0 h1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination (σ + φy) * e0 + φπ * e1
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0
/-- Galí (2015), eq. (27), p. 65: with the rule (26) in gap form, `(ỹ, π)`
satisfies the NKPC and the DIS if and only if it solves
`x_t = A_T E_t x_{t+1} + B_T u_t`. -/
theorem equilibrium_iff_solves {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0)
    (hS : σ + φy + κ * φπ ≠ 0) {rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (hrule : TaylorRuleGap ρ φπ φy i infl ygap yhatn v) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i ↔
      𝔼.Solves (AT β σ κ φπ φy) (forcing (BT σ κ φπ φy) (shockU ρ φy rn yhatn v))
        (stack ygap infl) := by
  rw [← structural_iff_solves 𝔼 hS, ← nk_iff_structural 𝔼 hσ hrule]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hrule⟩⟩

/-- The trace of `A_T`: `tr A_T = (σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)`
(Galí 2015, p. 65). -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The determinant of `A_T`: `det A_T = σ β/(σ + φ_y + κ φ_π)`
(Galí 2015, p. 65). -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Bullard–Mitra** (Galí 2015, eq. (28), p. 65): for `σ, κ > 0`,
`0 < β < 1` and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit
circle (the Schur–Cohn condition) if and only if
`κ (φ_π − 1) + (1 − β) φ_y > 0`. -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + φy + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + φy + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Galí (2015), p. 65 (Blanchard–Kahn and Bullard–Mitra): the system (27) is
determinate, i.e. has at most one bounded adapted solution for every forcing
process, if and only if condition (28) holds. -/
theorem determinate_iff_BM [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- Two bounded processes stack to a bounded vector process. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- **Uniqueness under (28)** (Galí 2015, p. 65): if
`κ (φ_π − 1) + (1 − β) φ_y > 0`, two equilibria with bounded adapted output
gap and inflation, driven by the same exogenous processes, coincide (output
gap, inflation and the nominal rate). -/
theorem equilibrium_unique {β σ κ ρ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn yhatn v ygap infl i ygap' infl' i' : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (he' : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap' infl' i')
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' ∧ i = i' := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  have hy := (equilibrium_iff_solves 𝔼 hσ.ne' hS he'.2.2).mp he'
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h28) hx hy
    (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 ha' hb')
    (boundedVec_stack hba hbb) (boundedVec_stack hba' hbb')
  have h1 : ygap = ygap' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 0
  have h2 : infl = infl' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 1
  refine ⟨h1, h2, funext fun t => ?_⟩
  rw [he.2.2 t, he'.2.2 t, h1, h2]

/-- **Indeterminacy without (28)** (Galí 2015, p. 65): if
`κ (φ_π − 1) + (1 − β) φ_y ≤ 0`, then next to any equilibrium with bounded
adapted output gap and inflation there is a second one, with a different
output gap or inflation path. -/
theorem equilibrium_not_unique [Nonempty Ω] {β σ κ ρ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h28 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) {rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap' infl' i' ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hrule' : TaylorRuleGap ρ φπ φy
      (fun t => (fun _ => ρ) + φπ • infl' t + φy • ygap' t + φy • yhatn t + v t)
      infl' ygap' yhatn v := fun t => rfl
  refine ⟨ygap', infl', _, (equilibrium_iff_solves 𝔼 hσ.ne' hS hrule').mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The minimum-state-variable solution -/

/-- Galí (2015), p. 66: the denominator
`(1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u)` of `Λ_u`. -/
def msvDen (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * (σ * (1 - ρu) + φy) + κ * (φπ - ρu)

/-- Galí (2015), p. 66: `Λ_u = 1/((1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u))`. -/
noncomputable def msvLambda (β σ κ φπ φy ρu : ℝ) : ℝ := 1 / msvDen β σ κ φπ φy ρu

/-- Galí (2015), eq. (29), p. 66: `ψ_y = (1 − βρ_u) Λ_u`. -/
noncomputable def msvPsiY (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), eq. (30), p. 66: `ψ_π = κ Λ_u`. -/
noncomputable def msvPsiPi (β σ κ φπ φy ρu : ℝ) : ℝ := κ * msvLambda β σ κ φπ φy ρu

/-- The denominator of `Λ_u` decomposes as
`(1 − ρ_u)((1 − βρ_u) σ + κ + β φ_y) + [κ (φ_π − 1) + (1 − β) φ_y]`
(Galí 2015, p. 66). -/
theorem msvDen_eq (β σ κ φπ φy ρu : ℝ) :
    msvDen β σ κ φπ φy ρu
      = (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) + (κ * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen; ring

/-- Galí (2015), p. 66: under (28) and for `ρ_u < 1` (in particular
`ρ_u ∈ [0, 1)`) the denominator of `Λ_u` is positive. -/
theorem msvDen_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β σ κ φπ φy ρu := by
  rw [msvDen_eq]
  have hbr : β * ρu < 1 := by nlinarith
  have h1 : 0 ≤ (1 - β * ρu) * σ := by nlinarith
  have h2 : 0 ≤ (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Galí (2015), p. 66: `Λ_u > 0` under (28), for every `ρ_u < 1`. -/
theorem msvLambda_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvLambda β σ κ φπ φy ρu :=
  one_div_pos.mpr (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28)

/-- A scalar multiple of an AR(1) process is AR(1) with the same persistence. -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- Galí (2015), eqs. (29)–(30), p. 66: for an AR(1) composite shock with
persistence `ρ_u` (and a nonzero denominator), the MSV processes
`ỹ_t = ψ_y u_t`, `π_t = ψ_π u_t` satisfy the structural equations. -/
theorem msv_structural {β σ κ φπ φy ρu : ℝ} (hD : msvDen β σ κ φπ φy ρu ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) :
    Structural 𝔼 β σ κ φπ φy u (fun t => msvPsiY β σ κ φπ φy ρu • u t)
      (fun t => msvPsiPi β σ κ φπ φy ρu • u t) := by
  have c1 : (σ + φy) * msvPsiY β σ κ φπ φy ρu + φπ * msvPsiPi β σ κ φπ φy ρu
      = σ * (msvPsiY β σ κ φπ φy ρu * ρu) + msvPsiPi β σ κ φπ φy ρu * ρu + 1 := by
    unfold msvPsiY msvPsiPi msvLambda
    field_simp
    unfold msvDen
    ring
  have c2 : msvPsiPi β σ κ φπ φy ρu
      = β * (msvPsiPi β σ κ φπ φy ρu * ρu) + κ * msvPsiY β σ κ φπ φy ρu := by
    unfold msvPsiY msvPsiPi
    ring
  intro t
  simp only [map_smul, hu.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c2

/-- Galí (2015), p. 66: under (28), for a bounded AR(1) composite shock with
`ρ_u < 1`, every bounded adapted solution of the structural equations is
the MSV solution (29)–(30). -/
theorem msv_unique {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {u ygap infl : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hub : BoundedProc u)
    (hs : Structural 𝔼 β σ κ φπ φy u ygap infl) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ygap = (fun t => msvPsiY β σ κ φπ φy ρu • u t) ∧
      infl = (fun t => msvPsiPi β σ κ φπ φy ρu • u t) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne'
  have hbs : ∀ c : ℝ, BoundedProc (fun t => c • u t) := by
    intro c
    obtain ⟨M, hM⟩ := hub
    exact ⟨|c| * M, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h28)
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs)
    ((structural_iff_solves 𝔼 hS _ _ _).mp (msv_structural 𝔼 hD hu))
    (adaptedVec_stack 𝔼 ha hb)
    (adaptedVec_stack 𝔼 (isAR1_smul 𝔼 hu _).1 (isAR1_smul 𝔼 hu _).1)
    (boundedVec_stack hba hbb) (boundedVec_stack (hbs _) (hbs _))
  exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
    funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1⟩

/-- **The unique bounded equilibrium** (Galí 2015, eqs. (29)–(30), p. 66): under
(28), with a bounded AR(1) composite shock `u = r̂^n − φ_y ŷ^n − v` of
persistence `ρ_u < 1`, a triple `(ỹ, π, i)` with bounded adapted `ỹ`, `π`
is an equilibrium if and only if `ỹ_t = (1 − βρ_u) Λ_u u_t`,
`π_t = κ Λ_u u_t` and `i_t` is given by the rule. The MSV triple is itself
bounded and adapted, so it is the unique bounded equilibrium. -/
theorem equilibrium_iff_msv {β σ κ ρ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu (shockU ρ φy rn yhatn v)) (hub : BoundedProc (shockU ρ φy rn yhatn v))
    {ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i ↔
      ygap = (fun t => msvPsiY β σ κ φπ φy ρu • shockU ρ φy rn yhatn v t) ∧
      infl = (fun t => msvPsiPi β σ κ φπ φy ρu • shockU ρ φy rn yhatn v t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yhatn t + v t := by
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne'
  constructor
  · intro he
    obtain ⟨h1, h2⟩ := msv_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hu hub
      ((nk_iff_structural 𝔼 hσ.ne' he.2.2).mp ⟨he.1, he.2.1⟩) ha hb hba hbb
    exact ⟨h1, h2, funext he.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hrule : TaylorRuleGap ρ φπ φy i infl ygap yhatn v := fun t => by rw [h3]
    have hs := (nk_iff_structural 𝔼 (β := β) (κ := κ) (rn := rn) hσ.ne' hrule).mpr
      (h1 ▸ h2 ▸ msv_structural 𝔼 hD hu)
    exact ⟨hs.1, hs.2, hrule⟩

end Gali.BasicNewKeynesianModel.TaylorRuleSystem

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Responses to shocks under the interest-rate rule

Galí (2015), Chapter 3, §§3.4.1.1–3.4.1.3, pp. 66–72. Under condition (28)
the unique bounded equilibrium is the MSV solution (29)–(30) of
`TaylorRuleSystem`. This module specialises it to the three shocks of the
basic model.

## Main results

* `monetary_shock`, `monetary_money_supply` (pp. 66–67): output gap,
  inflation, real rate, nominal rate and money supply after a monetary policy
  shock `v`; `liquidity_effect_iff` and `money_contracts_of_nominal_rises`.
* `discount_shock`, `discount_eq_monetary` (pp. 70–71): a discount-rate shock
  `z` moves `(ỹ, π)` exactly like a monetary shock `v = −(1 − ρ_z) z`.
  `discount_natRate_falls` and `discount_natRate_book_numbers` record the
  correction C3-5: the natural rate **falls** after the book's shock.
* `technology_shock`, `technology_output`, `technology_employment`
  (pp. 71–72): responses of `ỹ`, `π`, `y`, `n` to technology, with the
  corrected employment coefficient (C3-3, a missing `1/(1 − α)`), and
  `techNCoef_sub_printed` showing that the printed formula differs.
* `techOutputCoef_mem` and `techOutputCoef_counterexample` (C3-4): the output
  coefficient `κ (φ_π − ρ_a) Λ_a` lies in `(0, 1)` when `φ_π > ρ_a`, but can
  be negative under (28) alone.
* `techNCoef_neg_of_one_le_sigma`, `techNCoef_neg_of_phiy_large` (p. 72):
  employment falls after a technology improvement if `σ ≥ 1` (given
  `φ_π ≥ ρ_a`) or if `φ_y` is large.
-/

namespace Gali.BasicNewKeynesianModel.ShockResponses

open TaylorRuleSystem

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- A scalar multiple of a bounded process is bounded. -/
theorem boundedProc_smul {s : ℕ → Ω → ℝ} (hs : BoundedProc s) (c : ℝ) :
    BoundedProc (fun t => c • s t) := by
  obtain ⟨M, hM⟩ := hs
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), p. 66: if the composite shock is `u_t = c s_t` for a bounded
AR(1) process `s` with persistence `ρ_u < 1`, then under (28) every
equilibrium with bounded adapted `ỹ`, `π` has `ỹ_t = ψ_y c s_t` and
`π_t = ψ_π c s_t`. -/
theorem eq_msv_of_shock {β σ κ ρ φπ φy ρu c : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {s rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 ρu s) (hsb : BoundedProc s) (hU : ∀ t, shockU ρ φy rn yhatn v t = c • s t)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    (∀ t, ygap t = (msvPsiY β σ κ φπ φy ρu * c) • s t) ∧
      (∀ t, infl t = (msvPsiPi β σ κ φπ φy ρu * c) • s t) := by
  have hU' : shockU ρ φy rn yhatn v = fun t => c • s t := funext hU
  have hu : 𝔼.IsAR1 ρu (shockU ρ φy rn yhatn v) := by
    rw [hU']; exact isAR1_smul 𝔼 hs c
  have hub : BoundedProc (shockU ρ φy rn yhatn v) := by
    rw [hU']; exact boundedProc_smul hsb c
  obtain ⟨h1, h2, -⟩ :=
    (equilibrium_iff_msv 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hu hub ha hb hba hbb).mp he
  exact ⟨fun t => by simp only [h1, hU, smul_smul], fun t => by simp only [h2, hU, smul_smul]⟩

/-! ### Monetary policy shock (§3.4.1.1, pp. 66–67) -/

/-- Galí (2015), p. 66: output-gap response to a monetary shock,
`−(1 − βρ_v) Λ_v`. -/
noncomputable def monYgapCoef (β σ κ φπ φy ρv : ℝ) : ℝ :=
  -((1 - β * ρv) * msvLambda β σ κ φπ φy ρv)

/-- Galí (2015), p. 66: inflation response to a monetary shock, `−κ Λ_v`. -/
noncomputable def monInflCoef (β σ κ φπ φy ρv : ℝ) : ℝ := -(κ * msvLambda β σ κ φπ φy ρv)

/-- Galí (2015), p. 66: real-rate response to a monetary shock,
`σ (1 − ρ_v)(1 − βρ_v) Λ_v`. -/
noncomputable def monRealCoef (β σ κ φπ φy ρv : ℝ) : ℝ :=
  σ * (1 - ρv) * (1 - β * ρv) * msvLambda β σ κ φπ φy ρv

/-- Galí (2015), p. 67: nominal-rate response to a monetary shock,
`[σ (1 − ρ_v)(1 − βρ_v) − ρ_v κ] Λ_v`. -/
noncomputable def monNomCoef (β σ κ φπ φy ρv : ℝ) : ℝ :=
  (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ) * msvLambda β σ κ φπ φy ρv

/-- Galí (2015), p. 67: money-supply response to a monetary shock,
`−Λ_v [(1 − βρ_v)(1 + ησ (1 − ρ_v)) + (1 − ηρ_v) κ]`. -/
noncomputable def monMoneyCoef (β σ κ φπ φy ρv η : ℝ) : ℝ :=
  -(msvLambda β σ κ φπ φy ρv * ((1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ))

/-- **Monetary policy shock** (Galí 2015, pp. 66–67): with `a = z = 0`
(so `r^n_t = ρ` and `ŷ^n_t = 0`), an AR(1) monetary shock `v` with
persistence `ρ_v < 1` and (28), every equilibrium with bounded adapted `ỹ`, `π`
has `ỹ_t = −(1 − βρ_v) Λ_v v_t`, `π_t = −κ Λ_v v_t`,
`r̂_t = σ (1 − ρ_v)(1 − βρ_v) Λ_v v_t` and
`î_t = [σ (1 − ρ_v)(1 − βρ_v) − ρ_v κ] Λ_v v_t`. -/
theorem monetary_shock {β σ κ ρ φπ φy ρv : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (hv : 𝔼.IsAR1 ρv v) (hvb : BoundedProc v) (hrn : ∀ t, rn t = fun _ => ρ)
    (hyn : ∀ t, yhatn t = 0) (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    (∀ t, ygap t = monYgapCoef β σ κ φπ φy ρv • v t) ∧
      (∀ t, infl t = monInflCoef β σ κ φπ φy ρv • v t) ∧
      (∀ t, DIS.realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β σ κ φπ φy ρv • v t) ∧
      (∀ t, i t - (fun _ => ρ) = monNomCoef β σ κ φπ φy ρv • v t) := by
  have hU : ∀ t, shockU ρ φy rn yhatn v t = (-1 : ℝ) • v t := by
    intro t
    simp [shockU, hrn, hyn]
  obtain ⟨h1, h2⟩ := eq_msv_of_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hv hvb hU he ha hb hba hbb
  have hy : ∀ t, ygap t = monYgapCoef β σ κ φπ φy ρv • v t := fun t => by
    rw [h1 t, monYgapCoef, msvPsiY, mul_neg_one]
  have hp : ∀ t, infl t = monInflCoef β σ κ φπ φy ρv • v t := fun t => by
    rw [h2 t, monInflCoef, msvPsiPi, mul_neg_one]
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have hr : ∀ t, DIS.realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β σ κ φπ φy ρv • v t := by
    intro t
    have hd := he.2.1 t
    rw [hy t, hy (t + 1), map_smul, hv.2 t, hrn t] at hd
    funext ω
    have e := congrFun hd ω
    simp only [DIS.realRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    simp only [monYgapCoef, monRealCoef] at e ⊢
    linear_combination σ * e - (i t ω - (𝔼.E t) (infl (t + 1)) ω - ρ) * hinv
  refine ⟨hy, hp, hr, fun t => ?_⟩
  have h := hr t
  rw [DIS.realRate, hp (t + 1), map_smul, hv.2 t] at h
  funext ω
  have e := congrFun h ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  simp only [monInflCoef, monRealCoef, monNomCoef] at e ⊢
  linear_combination e

/-- **Money supply after a monetary shock** (Galí 2015, p. 67): with money
demand (4) `m_t = p_t + y_t − η i_t`, the price level `p_{t+1} = p_t + π_{t+1}`
and output `y_t = ỹ_t + ȳ` (natural output is constant when `a = 0`),
`m_{t+1} = p_t + (ȳ − ηρ) − Λ_v [(1 − βρ_v)(1 + ησ (1 − ρ_v)) + (1 − ηρ_v) κ] v_{t+1}`. -/
theorem monetary_money_supply {β σ κ ρ φπ φy ρv η ybar : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v ygap infl i m p y : ℕ → Ω → ℝ}
    (hv : 𝔼.IsAR1 ρv v) (hvb : BoundedProc v) (hrn : ∀ t, rn t = fun _ => ρ)
    (hyn : ∀ t, yhatn t = 0) (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) (hm : ∀ t, m t = p t + y t - η • i t)
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hy : ∀ t, y t = ygap t + fun _ => ybar)
    (t : ℕ) :
    m (t + 1) = p t + (fun _ => ybar - η * ρ) + monMoneyCoef β σ κ φπ φy ρv η • v (t + 1) := by
  obtain ⟨h1, h2, -, h4⟩ :=
    monetary_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hv hvb hrn hyn he ha hb hba hbb
  have hi : i (t + 1) = (fun _ => ρ) + monNomCoef β σ κ φπ φy ρv • v (t + 1) := by
    rw [← h4 (t + 1)]; abel
  rw [hm, hp, hy, hi, h1, h2]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [monYgapCoef, monInflCoef, monNomCoef, monMoneyCoef]
  ring

/-- Galí (2015), p. 66: under (28) and `ρ_v < 1`, a monetary tightening lowers
the output gap and inflation and raises the real rate. -/
theorem monetary_signs {β σ κ φπ φy ρv : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1) (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) :
    monYgapCoef β σ κ φπ φy ρv < 0 ∧ monInflCoef β σ κ φπ φy ρv < 0 ∧
      0 < monRealCoef β σ κ φπ φy ρv := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h28
  have hbr : 0 < 1 - β * ρv := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold monYgapCoef; nlinarith [mul_pos hbr hL]
  · unfold monInflCoef; nlinarith [mul_pos hκ hL]
  · unfold monRealCoef
    have : 0 < σ * (1 - ρv) := mul_pos hσ (by linarith)
    positivity

/-- Galí (2015), p. 67: the nominal rate falls after a monetary tightening if
and only if `σ (1 − ρ_v)(1 − βρ_v) < ρ_v κ` (high persistence). -/
theorem monNomCoef_neg_iff {β σ κ φπ φy ρv : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρv) :
    monNomCoef β σ κ φπ φy ρv < 0 ↔ σ * (1 - ρv) * (1 - β * ρv) < ρv * κ := by
  unfold monNomCoef
  rw [mul_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h; exact Or.inr ⟨by linarith, hL⟩

/-- Galí (2015), p. 67: the money-supply bracket is
`(1 − βρ_v) + κ + η [σ (1 − ρ_v)(1 − βρ_v) − ρ_v κ]`. -/
theorem money_bracket_eq (β σ κ ρv η : ℝ) :
    (1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ
      = (1 - β * ρv) + κ + η * (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ) := by
  ring

/-- Galí (2015), p. 67: with `Λ_v > 0`, money contracts after a tightening
(`m` coefficient negative) if and only if
`(1 − βρ_v)(1 + ησ (1 − ρ_v)) + (1 − ηρ_v) κ > 0`. -/
theorem monMoneyCoef_neg_iff {β σ κ φπ φy ρv η : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρv) :
    monMoneyCoef β σ κ φπ φy ρv η < 0 ↔
      0 < (1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ := by
  unfold monMoneyCoef
  rw [neg_lt_zero]
  exact ⟨fun h => pos_of_mul_pos_right h hL.le, fun h => mul_pos hL h⟩

/-- Galí (2015), p. 67: `di_t/dv_t > 0` is sufficient for a contraction in the
money supply, for `η ≥ 0`, `κ > 0` and `βρ_v < 1`. -/
theorem money_contracts_of_nominal_rises {β σ κ φπ φy ρv η : ℝ} (hκ : 0 < κ)
    (hbr : β * ρv < 1) (hη : 0 ≤ η) (hL : 0 < msvLambda β σ κ φπ φy ρv)
    (hi : 0 < monNomCoef β σ κ φπ φy ρv) : monMoneyCoef β σ κ φπ φy ρv η < 0 := by
  rw [monMoneyCoef_neg_iff hL, money_bracket_eq]
  have hb : 0 < σ * (1 - ρv) * (1 - β * ρv) - ρv * κ := pos_of_mul_pos_left hi hL.le
  have : 0 ≤ η * (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ) := mul_nonneg hη hb.le
  linarith

/-- **Liquidity effect** (Galí 2015, p. 67): the nominal rate and the money
supply move in opposite directions after a monetary shock if and only if the
nominal-rate bracket and the money-supply bracket have the same sign. -/
theorem liquidity_effect_iff {β σ κ φπ φy ρv η : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρv) :
    monNomCoef β σ κ φπ φy ρv * monMoneyCoef β σ κ φπ φy ρv η < 0 ↔
      0 < (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ)
        * ((1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ) := by
  have e : monNomCoef β σ κ φπ φy ρv * monMoneyCoef β σ κ φπ φy ρv η
      = -(msvLambda β σ κ φπ φy ρv ^ 2 * ((σ * (1 - ρv) * (1 - β * ρv) - ρv * κ)
        * ((1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ))) := by
    unfold monNomCoef monMoneyCoef; ring
  rw [e, neg_lt_zero]
  have h2 : 0 < msvLambda β σ κ φπ φy ρv ^ 2 := by positivity
  exact ⟨fun h => pos_of_mul_pos_right h h2.le, fun h => mul_pos h2 h⟩

/-- Galí (2015), p. 67: `di_t/dv_t > 0` is sufficient for a liquidity effect. -/
theorem liquidity_effect_of_nominal_rises {β σ κ φπ φy ρv η : ℝ} (hκ : 0 < κ)
    (hbr : β * ρv < 1) (hη : 0 ≤ η) (hL : 0 < msvLambda β σ κ φπ φy ρv)
    (hi : 0 < monNomCoef β σ κ φπ φy ρv) :
    monNomCoef β σ κ φπ φy ρv * monMoneyCoef β σ κ φπ φy ρv η < 0 :=
  mul_neg_of_pos_of_neg hi (money_contracts_of_nominal_rises hκ hbr hη hL hi)

/-! ### Discount-rate shock (§3.4.1.2, pp. 70–71) -/

/-- **Discount-rate shock** (Galí 2015, pp. 70–71): with `a = v = 0` the
natural rate is `r^n_t = ρ + (1 − ρ_z) z_t` (eq. (24)) and `ŷ^n_t = 0`; for an
AR(1) preference shock with `ρ_z < 1` and (28), every equilibrium with bounded
adapted `ỹ`, `π` has `ỹ_t = (1 − βρ_z) Λ_z (1 − ρ_z) z_t`,
`π_t = κ Λ_z (1 − ρ_z) z_t`, `î_t = (φ_π κ + φ_y (1 − βρ_z)) Λ_z (1 − ρ_z) z_t`
and `r̂_t = (1 − ρ_z)(1 − σ (1 − ρ_z)(1 − βρ_z) Λ_z) z_t`. -/
theorem discount_shock {β σ κ ρ φπ φy ρz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρz < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v z ygap infl i : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ρz z) (hzb : BoundedProc z) (hrn : ∀ t, rn t = (fun _ => ρ) + (1 - ρz) • z t)
    (hyn : ∀ t, yhatn t = 0) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    (∀ t, ygap t = ((1 - β * ρz) * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t) ∧
      (∀ t, infl t = (κ * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t) ∧
      (∀ t, i t - (fun _ => ρ)
        = ((φπ * κ + φy * (1 - β * ρz)) * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t) ∧
      (∀ t, DIS.realRate 𝔼 i infl t - (fun _ => ρ)
        = ((1 - ρz) * (1 - σ * (1 - ρz) * (1 - β * ρz) * msvLambda β σ κ φπ φy ρz)) • z t) := by
  have hU : ∀ t, shockU ρ φy rn yhatn v t = (1 - ρz) • z t := by
    intro t
    simp [shockU, hrn, hyn, hv0]
  obtain ⟨h1, h2⟩ := eq_msv_of_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hz hzb hU he ha hb hba hbb
  have hy : ∀ t, ygap t = ((1 - β * ρz) * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t :=
    fun t => by rw [h1 t, msvPsiY]
  have hp : ∀ t, infl t = (κ * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t :=
    fun t => by rw [h2 t, msvPsiPi]
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  refine ⟨hy, hp, fun t => ?_, fun t => ?_⟩
  · rw [he.2.2 t, hyn t, hv0 t, hy t, hp t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  · have hd := he.2.1 t
    rw [hy t, hy (t + 1), map_smul, hz.2 t, hrn t] at hd
    funext ω
    have e := congrFun hd ω
    simp only [DIS.realRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination σ * e - (i t ω - (𝔼.E t) (infl (t + 1)) ω - (ρ + (1 - ρz) * z t ω))
      * hinv

/-- Galí (2015), p. 71: the discount-rate shock and a monetary shock enter the
system (27) symmetrically. An equilibrium under a discount-rate shock `z` and
one under the monetary shock `v_t = −(1 − ρ_z) z_t` (with constant natural
rate) have the same output gap and inflation. -/
theorem discount_eq_monetary {β σ κ ρ φπ φy ρz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρz < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn yhatn v z ygap infl i rn' yhatn' v' ygap' infl' i' : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ρz z) (hzb : BoundedProc z) (hrn : ∀ t, rn t = (fun _ => ρ) + (1 - ρz) • z t)
    (hyn : ∀ t, yhatn t = 0) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hrn' : ∀ t, rn' t = fun _ => ρ) (hyn' : ∀ t, yhatn' t = 0)
    (hv' : ∀ t, v' t = (-(1 - ρz)) • z t)
    (he' : Equilibrium 𝔼 β σ κ ρ φπ φy rn' yhatn' v' ygap' infl' i') (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' := by
  obtain ⟨h1, h2, -, -⟩ :=
    discount_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hz hzb hrn hyn hv0 he ha hb hba hbb
  have hvf : v' = fun t => (-(1 - ρz)) • z t := funext hv'
  have hvA : 𝔼.IsAR1 ρz v' := by rw [hvf]; exact isAR1_smul 𝔼 hz _
  have hvB : BoundedProc v' := by rw [hvf]; exact boundedProc_smul hzb _
  obtain ⟨g1, g2, -, -⟩ :=
    monetary_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hvA hvB hrn' hyn' he' ha' hb' hba' hbb'
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · rw [h1 t, g1 t, hv' t, smul_smul, monYgapCoef]; ring_nf
  · rw [h2 t, g2 t, hv' t, smul_smul, monInflCoef]; ring_nf

/-- Galí (2015), p. 71: the nominal-rate and real-rate coefficients of the
discount-rate shock are positive under (28) when `φ_π ≥ ρ_z`, so a fall in
`z` lowers both interest rates, as the text says. -/
theorem discount_rates_fall {β σ κ φπ φy ρz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρz < 1) (hρπ : ρz ≤ φπ)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) :
    0 < (φπ * κ + φy * (1 - β * ρz)) * msvLambda β σ κ φπ φy ρz * (1 - ρz) ∧
      0 < (1 - ρz) * (1 - σ * (1 - ρz) * (1 - β * ρz) * msvLambda β σ κ φπ φy ρz) := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h28
  have hD := msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28
  have hbr : 0 < 1 - β * ρz := by nlinarith
  have h1ρ : 0 < 1 - ρz := by linarith
  refine ⟨?_, ?_⟩
  · have : 0 < φπ * κ + φy * (1 - β * ρz) := by
      rcases hφπ.lt_or_eq with h | h
      · have := mul_pos h hκ; nlinarith
      · subst h
        have : φy ≠ 0 := by rintro rfl; nlinarith
        have := lt_of_le_of_ne hφy (Ne.symm this)
        nlinarith
    positivity
  · apply mul_pos h1ρ
    have e : 1 - σ * (1 - ρz) * (1 - β * ρz) * msvLambda β σ κ φπ φy ρz
        = ((1 - β * ρz) * φy + κ * (φπ - ρz)) * msvLambda β σ κ φπ φy ρz := by
      unfold msvLambda
      field_simp
      unfold msvDen
      ring
    rw [e]
    apply mul_pos _ hL
    have : 0 ≤ κ * (φπ - ρz) := mul_nonneg hκ.le (by linarith)
    rcases (mul_nonneg hbr.le hφy).lt_or_eq with h | h
    · linarith
    · -- `φ_y = 0`, so (28) forces `φ_π > 1 > ρ_z`
      have hφy0 : φy = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · linarith
        · exact h'
      subst hφy0
      have : 1 < φπ := by nlinarith
      nlinarith

/-- **Correction C3-5** (Galí 2015, p. 71): a fall in `z` lowers the natural
rate. If `z_t = ε` with `ε < 0` and `ρ_z < 1`, then by (24) (with `a = 0`)
`r^n_t − ρ = (1 − ρ_z) ε < 0`; the text says the natural rate increases. -/
theorem discount_natRate_falls {ρ ρz ε : ℝ} (hρ1 : ρz < 1) (hε : ε < 0)
    {rn z : ℕ → Ω → ℝ} {t : ℕ} (hrn : rn t = (fun _ => ρ) + (1 - ρz) • z t)
    (hzt : z t = fun _ => ε) :
    rn t - (fun _ => ρ) = (fun _ => (1 - ρz) * ε) ∧ (1 - ρz) * ε < 0 := by
  refine ⟨?_, mul_neg_of_pos_of_neg (by linarith) hε⟩
  rw [hrn, hzt]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Correction C3-5**, the book's numbers (Galí 2015, p. 71): with
`ρ_z = 0.5` and `ε^z = −0.5` the natural rate changes by
`(1 − ρ_z) ε^z = −0.25` per quarter, i.e. by `−1` percentage point at an
annual rate: a fall, not an increase. -/
theorem discount_natRate_book_numbers :
    (1 - (1 / 2 : ℝ)) * (-1 / 2) = -1 / 4 ∧ 4 * ((1 - (1 / 2 : ℝ)) * (-1 / 2)) = -1 := by
  norm_num

/-! ### Technology shock (§3.4.1.3, pp. 71–72) -/

/-- Galí (2015), p. 71: output-gap response to technology,
`−ψ_ya (φ_y + σ (1 − ρ_a))(1 − βρ_a) Λ_a`. -/
noncomputable def techYgapCoef (β σ κ φπ φy ρa ψya : ℝ) : ℝ :=
  -(ψya * (φy + σ * (1 - ρa)) * (1 - β * ρa) * msvLambda β σ κ φπ φy ρa)

/-- Galí (2015), p. 72: inflation response to technology,
`−ψ_ya (φ_y + σ (1 − ρ_a)) κ Λ_a`. -/
noncomputable def techInflCoef (β σ κ φπ φy ρa ψya : ℝ) : ℝ :=
  -(ψya * (φy + σ * (1 - ρa)) * κ * msvLambda β σ κ φπ φy ρa)

/-- Galí (2015), p. 72: the factor `κ (φ_π − ρ_a) Λ_a` of the output response
to technology. -/
noncomputable def techOutputCoef (β σ κ φπ φy ρa : ℝ) : ℝ :=
  κ * (φπ - ρa) * msvLambda β σ κ φπ φy ρa

/-- **Corrected** employment response to technology (Galí 2015, p. 72, with
correction C3-3):
`Λ_a [(1 − σ) κ (φ_π − ρ_a)/(σ (1 − α) + φ + α) − (φ_y + σ (1 − ρ_a))(1 − βρ_a)/(1 − α)]`. -/
noncomputable def techNCoef (β σ κ φπ φy ρa φ α : ℝ) : ℝ :=
  msvLambda β σ κ φπ φy ρa * ((1 - σ) * κ * (φπ - ρa) / (σ * (1 - α) + φ + α)
    - (φy + σ * (1 - ρa)) * (1 - β * ρa) / (1 - α))

/-- The employment coefficient **as printed** in Galí (2015), p. 72:
`Λ_a [(1 − σ) κ (φ_π − ρ_a)/(σ (1 − α) + φ + α) − (φ_y + σ (1 − ρ_a))(1 − βρ_a)]`
(missing the factor `1/(1 − α)` on the second term). -/
noncomputable def techNCoefPrinted (β σ κ φπ φy ρa φ α : ℝ) : ℝ :=
  msvLambda β σ κ φπ φy ρa * ((1 - σ) * κ * (φπ - ρa) / (σ * (1 - α) + φ + α)
    - (φy + σ * (1 - ρa)) * (1 - β * ρa))

/-- **Technology shock** (Galí 2015, pp. 71–72): with `z = v = 0`,
`r^n_t = ρ − σ (1 − ρ_a) ψ_ya a_t` (eq. (24)) and `ŷ^n_t = ψ_ya a_t`, an AR(1)
technology process with `ρ_a < 1` and (28), every equilibrium with bounded
adapted `ỹ`, `π` has `ỹ_t = −ψ_ya (φ_y + σ (1 − ρ_a))(1 − βρ_a) Λ_a a_t` and
`π_t = −ψ_ya (φ_y + σ (1 − ρ_a)) κ Λ_a a_t`. -/
theorem technology_shock {β σ κ ρ φπ φy ρa ψya : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρa < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v a ygap infl i : ℕ → Ω → ℝ}
    (hav : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hrn : ∀ t, rn t = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t)
    (hyn : ∀ t, yhatn t = ψya • a t) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    (∀ t, ygap t = techYgapCoef β σ κ φπ φy ρa ψya • a t) ∧
      (∀ t, infl t = techInflCoef β σ κ φπ φy ρa ψya • a t) := by
  have hU : ∀ t, shockU ρ φy rn yhatn v t = (-(ψya * (φy + σ * (1 - ρa)))) • a t := by
    intro t
    rw [shockU, hrn, hyn, hv0]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  obtain ⟨h1, h2⟩ := eq_msv_of_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hav hab hU he ha hb hba hbb
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [h1 t, msvPsiY, techYgapCoef]; ring_nf
  · rw [h2 t, msvPsiPi, techInflCoef]; ring_nf

/-- Galí (2015), p. 72: the output response decomposes as
`ψ_ya + (ỹ coefficient) = ψ_ya κ (φ_π − ρ_a) Λ_a`. -/
theorem techOutput_eq {β σ κ φπ φy ρa ψya : ℝ} (hD : msvDen β σ κ φπ φy ρa ≠ 0) :
    techYgapCoef β σ κ φπ φy ρa ψya + ψya = ψya * techOutputCoef β σ κ φπ φy ρa := by
  unfold techYgapCoef techOutputCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- **Output after a technology shock** (Galí 2015, p. 72): with
`y_t = ỹ_t + y^n_t` and `y^n_t = ψ_ya a_t + ψ_y`, the equilibrium output is
`y_t = ψ_y + ψ_ya κ (φ_π − ρ_a) Λ_a a_t`. -/
theorem technology_output {β σ κ ρ φπ φy ρa ψya ψy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρa < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v a ygap infl i y : ℕ → Ω → ℝ}
    (hav : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hrn : ∀ t, rn t = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t)
    (hyn : ∀ t, yhatn t = ψya • a t) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hy : ∀ t, y t = ygap t + DIS.natOutput ψya ψy a t) (t : ℕ) :
    y t = (fun _ => ψy) + (ψya * techOutputCoef β σ κ φπ φy ρa) • a t := by
  obtain ⟨h1, -⟩ := technology_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hav hab hrn hyn hv0
    he ha hb hba hbb
  rw [hy, h1, DIS.natOutput, ← techOutput_eq (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne',
    add_smul]
  abel

/-- The corrected employment coefficient: `ψ_ya κ (φ_π − ρ_a) Λ_a − 1`
divided by `1 − α` equals `techNCoef` (Galí 2015, p. 72, correction C3-3),
when `ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)`. -/
theorem techNCoef_eq {β σ κ φπ φy ρa φ α : ℝ} (hD : msvDen β σ κ φπ φy ρa ≠ 0)
    (hd : σ * (1 - α) + φ + α ≠ 0) (hα : 1 - α ≠ 0) :
    (DIS.psiYA σ φ α * techOutputCoef β σ κ φπ φy ρa - 1) / (1 - α)
      = techNCoef β σ κ φπ φy ρa φ α := by
  unfold DIS.psiYA techOutputCoef techNCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- **Employment after a technology shock, corrected** (Galí 2015, p. 72,
correction C3-3): with `y_t = ỹ_t + ψ_ya a_t + ψ_y`,
`ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)` and the first-order production relation
(14) `(1 − α) n_t = y_t − a_t`, employment is `n_t = ψ_y/(1 − α) + c_n a_t`
with
`c_n = Λ_a [(1 − σ) κ (φ_π − ρ_a)/(σ (1 − α) + φ + α) − (φ_y + σ (1 − ρ_a))(1 − βρ_a)/(1 − α)]`. -/
theorem technology_employment {β σ κ ρ φπ φy ρa ψy φ α : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρa < 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v a ygap infl i y n : ℕ → Ω → ℝ}
    (hav : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hrn : ∀ t, rn t = (fun _ => ρ) - (σ * (1 - ρa) * DIS.psiYA σ φ α) • a t)
    (hyn : ∀ t, yhatn t = DIS.psiYA σ φ α • a t) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hy : ∀ t, y t = ygap t + DIS.natOutput (DIS.psiYA σ φ α) ψy a t)
    (hn : ∀ t, n t = (1 - α)⁻¹ • (y t - a t)) (t : ℕ) :
    n t = (fun _ => ψy / (1 - α)) + techNCoef β σ κ φπ φy ρa φ α • a t := by
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne'
  have hd : σ * (1 - α) + φ + α ≠ 0 := by nlinarith
  have hα : 1 - α ≠ 0 := by linarith
  rw [hn, technology_output 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hav hab hrn hyn hv0 he ha hb hba
    hbb hy t, ← techNCoef_eq hD hd hα]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The printed employment formula is wrong** (Galí 2015, p. 72, C3-3): the
corrected coefficient minus the printed one is
`−α/(1 − α) · (φ_y + σ (1 − ρ_a))(1 − βρ_a) Λ_a`. -/
theorem techNCoef_sub_printed (β σ κ φπ φy ρa φ α : ℝ) (hα : 1 - α ≠ 0) :
    techNCoef β σ κ φπ φy ρa φ α - techNCoefPrinted β σ κ φπ φy ρa φ α
      = -(α / (1 - α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa) * msvLambda β σ κ φπ φy ρa)) := by
  unfold techNCoef techNCoefPrinted
  field_simp
  ring

/-- Galí (2015), p. 72, C3-3: the printed and corrected employment
coefficients differ whenever `α ≠ 0` (with `ρ_a < 1`, `0 < β < 1`, `σ > 0`,
`φ_y ≥ 0` and `Λ_a ≠ 0`). -/
theorem techNCoef_ne_printed {β σ κ φπ φy ρa φ α : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hα : α ≠ 0) (hα1 : α < 1)
    (hL : msvLambda β σ κ φπ φy ρa ≠ 0) :
    techNCoef β σ κ φπ φy ρa φ α ≠ techNCoefPrinted β σ κ φπ φy ρa φ α := by
  intro h
  have e := techNCoef_sub_printed β σ κ φπ φy ρa φ α (by linarith)
  rw [h, sub_self] at e
  have hX : 0 < (φy + σ * (1 - ρa)) * (1 - β * ρa) := by
    apply mul_pos
    · nlinarith
    · nlinarith
  have hne : α / (1 - α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa) * msvLambda β σ κ φπ φy ρa)
      ≠ 0 := by
    apply mul_ne_zero (div_ne_zero hα (by linarith)) (mul_ne_zero hX.ne' hL)
  exact hne (by linarith)

/-- **Correction C3-4** (Galí 2015, p. 72): if `φ_π > ρ_a` (and `ρ_a < 1`),
then `κ (φ_π − ρ_a) Λ_a ∈ (0, 1)`; so output rises after a technology
improvement, but by less than natural output. -/
theorem techOutputCoef_mem {β σ κ φπ φy ρa : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hρπ : ρa < φπ) :
    0 < techOutputCoef β σ κ φπ φy ρa ∧ techOutputCoef β σ κ φπ φy ρa < 1 := by
  have hbr : 0 < 1 - β * ρa := by nlinarith
  have hA : 0 < (1 - β * ρa) * (σ * (1 - ρa) + φy) := by
    apply mul_pos hbr; nlinarith
  have hB : 0 < κ * (φπ - ρa) := mul_pos hκ (by linarith)
  have hD : 0 < msvDen β σ κ φπ φy ρa := by unfold msvDen; linarith
  unfold techOutputCoef msvLambda
  rw [mul_one_div]
  refine ⟨div_pos hB hD, ?_⟩
  rw [div_lt_one hD]
  unfold msvDen
  linarith

/-- **Counterexample to the printed claim** (Galí 2015, p. 72, C3-4): with
`φ_π = 0`, `φ_y = 20`, `ρ_a = 0.9`, `β = 0.99`, `σ = 1`, `κ = 0.1717`,
condition (28) holds, yet `κ (φ_π − ρ_a) Λ_a < 0`: output **falls** after a
technology improvement. -/
theorem techOutputCoef_counterexample :
    0 < (0.1717 : ℝ) * (0 - 1) + (1 - 0.99) * 20 ∧
      techOutputCoef 0.99 1 0.1717 0 20 0.9 < 0 := by
  unfold techOutputCoef msvLambda msvDen
  norm_num

/-- Galí (2015), p. 72, C3-4: the claim also fails at the boundary `ρ_a = 1`,
`φ_y = 0` (allowed in the book's `ρ_a ∈ [0, 1]`): the coefficient equals 1. -/
theorem techOutputCoef_unit_root {β σ κ φπ : ℝ} (hκ : κ ≠ 0) (hφπ : φπ ≠ 1) :
    techOutputCoef β σ κ φπ 0 1 = 1 := by
  have : κ * (φπ - 1) ≠ 0 := mul_ne_zero hκ (sub_ne_zero.mpr hφπ)
  unfold techOutputCoef msvLambda msvDen
  field_simp
  ring

/-- Galí (2015), p. 72: with `Λ_a > 0`, `0 ≤ α < 1` and `σ (1 − α) + φ + α > 0`,
employment falls after a technology improvement if and only if
`(1 − σ) κ (φ_π − ρ_a)(1 − α) < (σ (1 − α) + φ + α)(φ_y + σ (1 − ρ_a))(1 − βρ_a)`. -/
theorem techNCoef_neg_iff {β σ κ φπ φy ρa φ α : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρa)
    (hα1 : α < 1) (hd : 0 < σ * (1 - α) + φ + α) :
    techNCoef β σ κ φπ φy ρa φ α < 0 ↔
      (1 - σ) * κ * (φπ - ρa) * (1 - α)
        < (σ * (1 - α) + φ + α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa)) := by
  have h1α : 0 < 1 - α := by linarith
  unfold techNCoef
  rw [mul_neg_iff]
  have key : (1 - σ) * κ * (φπ - ρa) / (σ * (1 - α) + φ + α)
      - (φy + σ * (1 - ρa)) * (1 - β * ρa) / (1 - α)
      = ((1 - σ) * κ * (φπ - ρa) * (1 - α)
        - (σ * (1 - α) + φ + α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa)))
        / ((σ * (1 - α) + φ + α) * (1 - α)) := by
    field_simp
  rw [key]
  have hp : 0 < (σ * (1 - α) + φ + α) * (1 - α) := mul_pos hd h1α
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · rw [div_neg_iff] at h
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · linarith
      · linarith
    · linarith
  · intro h
    exact Or.inl ⟨hL, div_neg_of_neg_of_pos (by linarith) hp⟩

/-- Galí (2015), p. 72: `σ ≥ 1` is sufficient for employment to fall after a
technology improvement, provided `φ_π ≥ ρ_a` (the book omits this condition;
see C3-4), with `ρ_a < 1`, `α < 1`, `φ ≥ 0`. -/
theorem techNCoef_neg_of_one_le_sigma {β σ κ φπ φy ρa φ α : ℝ} (hσ : 1 ≤ σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hρπ : ρa ≤ φπ)
    (hφ : 0 ≤ φ) (hα1 : α < 1) : techNCoef β σ κ φπ φy ρa φ α < 0 := by
  have hbr : 0 < 1 - β * ρa := by nlinarith
  have hA : 0 < (1 - β * ρa) * (σ * (1 - ρa) + φy) := by
    apply mul_pos hbr; nlinarith
  have hD : 0 < msvDen β σ κ φπ φy ρa := by
    unfold msvDen; have := mul_nonneg hκ.le (sub_nonneg.mpr hρπ); linarith
  have hL : 0 < msvLambda β σ κ φπ φy ρa := one_div_pos.mpr hD
  have hd : 0 < σ * (1 - α) + φ + α := by nlinarith
  rw [techNCoef_neg_iff hL hα1 hd]
  have h1 : (1 - σ) * κ * (φπ - ρa) * (1 - α) ≤ 0 := by
    have : 0 ≤ κ * (φπ - ρa) * (1 - α) :=
      mul_nonneg (mul_nonneg hκ.le (sub_nonneg.mpr hρπ)) (by linarith)
    nlinarith
  have h2 : 0 < (σ * (1 - α) + φ + α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa)) := by
    apply mul_pos hd; nlinarith
  linarith

/-- Galí (2015), p. 72: employment also falls when `φ_y` is large enough:
precisely, whenever `(1 − σ) κ (φ_π − ρ_a)(1 − α) ≤ (σ (1 − α) + φ + α) φ_y (1 − βρ_a)`,
which holds for all sufficiently large `φ_y` (with `φ_π ≥ ρ_a`, `ρ_a < 1`). -/
theorem techNCoef_neg_of_phiy_large {β σ κ φπ φy ρa φ α : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hρπ : ρa ≤ φπ)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlarge : (1 - σ) * κ * (φπ - ρa) * (1 - α) ≤ (σ * (1 - α) + φ + α) * φy * (1 - β * ρa)) :
    techNCoef β σ κ φπ φy ρa φ α < 0 := by
  have hbr : 0 < 1 - β * ρa := by nlinarith
  have hA : 0 < (1 - β * ρa) * (σ * (1 - ρa) + φy) := by
    apply mul_pos hbr; nlinarith
  have hD : 0 < msvDen β σ κ φπ φy ρa := by
    unfold msvDen; have := mul_nonneg hκ.le (sub_nonneg.mpr hρπ); linarith
  have hL : 0 < msvLambda β σ κ φπ φy ρa := one_div_pos.mpr hD
  have hd : 0 < σ * (1 - α) + φ + α := by nlinarith
  rw [techNCoef_neg_iff hL hα1 hd]
  have h2 : 0 < (σ * (1 - α) + φ + α) * (σ * (1 - ρa) * (1 - β * ρa)) := by
    apply mul_pos hd; apply mul_pos _ hbr; nlinarith
  nlinarith

end Gali.BasicNewKeynesianModel.ShockResponses

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The baseline calibration

Galí (2015), Chapter 3, pp. 67–68 (and fn. 12, p. 72). Quarterly baseline:
`β = 0.99`, `σ = 1`, `φ = 5`, `α = 1/4`, `ε = 9`, `η = 4`, `θ = 3/4`,
`φ_π = 1.5`, `φ_y = 0.125`, `ρ_v = 0.5`, and `ρ_a = 0.9` for the technology
shock. All facts below are exact rational computations.

## Main results

* `markup_baseline`: `M = ε/(ε − 1) = 9/8`, a 12.5 percent markup.
* `mean_duration_baseline`: the mean price duration is 4 quarters.
* `bigTheta_baseline`, `lambda_baseline`, `kappa_baseline`: `Θ = 1/4`,
  `λ = 103/4800 ≈ 0.0215`, `κ = 103/600 ≈ 0.1717`.
* `bullardMitra_baseline`: condition (28) holds.
* `psiYA_baseline`: `ψ_ya = 1` at `σ = 1` (fn. 12, where it is misprinted as
  `ϕ_ya`, C3-7).
* `monetary_signs_baseline`, `liquidity_effect_baseline`,
  `technology_baseline`, `employment_baseline`: signs and values of the
  response coefficients, including the corrected employment coefficient
  `≈ −0.2564` versus the printed formula's `≈ −0.1923` (C3-3).
-/

namespace Gali.BasicNewKeynesianModel.Calibration

open TaylorRuleSystem ShockResponses

/-- Galí (2015), p. 57: the desired gross markup `M = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 60: `Θ = (1 − α)/(1 − α + α ε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), p. 61: `λ = (1 − θ)(1 − βθ) Θ/θ`. -/
noncomputable def lambdaNK (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), p. 63: `κ = λ (σ + (φ + α)/(1 − α))`. -/
noncomputable def kappaNK (β θ σ φ α ε : ℝ) : ℝ := lambdaNK β θ α ε * (σ + (φ + α) / (1 - α))

/-- The baseline value of `κ` (Galí 2015, p. 67). -/
noncomputable def κ₀ : ℝ := kappaNK 0.99 0.75 1 5 0.25 9

/-- The baseline Calvo parameter `θ = 3/4` (Galí 2015, p. 67). -/
noncomputable def baselineCalvo : CalvoParam where
  θ := 3 / 4
  nonneg := by norm_num
  lt_one := by norm_num

/-- Galí (2015), p. 67: with `ε = 9` the desired markup is `M = 9/8 = 1.125`. -/
theorem markup_baseline : markup 9 = 9 / 8 ∧ markup 9 = 1.125 := by
  unfold markup; norm_num

/-- Galí (2015), pp. 67–68: `θ = 3/4` implies an average price duration of
four quarters. -/
theorem mean_duration_baseline :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb baselineCalvo.θ k = 4 := by
  rw [baselineCalvo.mean_duration]
  simp only [baselineCalvo]
  norm_num

/-- Galí (2015), p. 67: `β = 0.99` implies a steady-state annualised real
return `β⁻⁴ − 1` of about 4 percent. -/
theorem annual_return_baseline :
    0.041 < (1 / (0.99 : ℝ)) ^ 4 - 1 ∧ (1 / (0.99 : ℝ)) ^ 4 - 1 < 0.0411 := by
  norm_num

/-- Galí (2015), p. 67: `φ = 5` is a Frisch elasticity `1/φ = 0.2`, and the
quarterly output coefficient is `φ_y = 0.5/4 = 0.125`. -/
theorem frisch_and_phiy_baseline : (1 : ℝ) / 5 = 0.2 ∧ (0.5 : ℝ) / 4 = 0.125 := by
  norm_num

/-- Galí (2015), p. 60: at `α = 1/4`, `ε = 9`, `Θ = 1/4`. -/
theorem bigTheta_baseline : bigTheta 0.25 9 = 1 / 4 := by
  unfold bigTheta; norm_num

/-- Galí (2015), p. 61: the baseline `λ = 103/4800 ∈ (0.0214, 0.0215)`. -/
theorem lambda_baseline :
    lambdaNK 0.99 0.75 0.25 9 = 103 / 4800 ∧
      0.0214 < lambdaNK 0.99 0.75 0.25 9 ∧ lambdaNK 0.99 0.75 0.25 9 < 0.0215 := by
  unfold lambdaNK bigTheta; norm_num

/-- Galí (2015), p. 63: the baseline `κ = 103/600 ∈ (0.1716, 0.1717)`. -/
theorem kappa_baseline : κ₀ = 103 / 600 ∧ 0.1716 < κ₀ ∧ κ₀ < 0.1717 := by
  unfold κ₀ kappaNK lambdaNK bigTheta; norm_num

/-- Galí (2015), eq. (28), p. 65: the baseline satisfies the Bullard–Mitra
condition `κ (φ_π − 1) + (1 − β) φ_y > 0`, so the equilibrium is
determinate. -/
theorem bullardMitra_baseline : 0 < κ₀ * (1.5 - 1) + (1 - 0.99) * 0.125 := by
  rw [kappa_baseline.1]; norm_num

/-- Galí (2015), p. 72, fn. 12 (misprinted there as `ϕ_ya`, C3-7):
`ψ_ya = (1 + φ)/(σ (1 − α) + φ + α) = 1` at `σ = 1`, for any `φ`, `α` with
`φ + 1 ≠ 0`; in particular at the baseline. -/
theorem psiYA_one_of_sigma_one {φ α : ℝ} (h : 1 + φ ≠ 0) : DIS.psiYA 1 φ α = 1 := by
  unfold DIS.psiYA
  rw [show 1 * (1 - α) + φ + α = 1 + φ by ring]
  exact div_self h

/-- Galí (2015), p. 72, fn. 12: `ψ_ya = 1` at the baseline. -/
theorem psiYA_baseline : DIS.psiYA 1 5 0.25 = 1 := psiYA_one_of_sigma_one (by norm_num)

/-- Galí (2015), pp. 66–68 (figure 3.1): at the baseline with `ρ_v = 0.5`, a
monetary tightening lowers the output gap and inflation, raises the real rate
and also raises the nominal rate (by less than its exogenous component). -/
theorem monetary_signs_baseline :
    monYgapCoef 0.99 1 κ₀ 1.5 0.125 0.5 < 0 ∧ monInflCoef 0.99 1 κ₀ 1.5 0.125 0.5 < 0 ∧
      0 < monRealCoef 0.99 1 κ₀ 1.5 0.125 0.5 ∧ 0 < monNomCoef 0.99 1 κ₀ 1.5 0.125 0.5 ∧
      monNomCoef 0.99 1 κ₀ 1.5 0.125 0.5 < 1 := by
  rw [kappa_baseline.1]
  unfold monYgapCoef monInflCoef monRealCoef monNomCoef msvLambda msvDen
  norm_num

/-- Galí (2015), p. 68: at the baseline (`η = 4`) the money supply contracts
after a tightening and the model displays a liquidity effect. -/
theorem liquidity_effect_baseline :
    monMoneyCoef 0.99 1 κ₀ 1.5 0.125 0.5 4 < 0 ∧
      monNomCoef 0.99 1 κ₀ 1.5 0.125 0.5 * monMoneyCoef 0.99 1 κ₀ 1.5 0.125 0.5 4 < 0 := by
  rw [kappa_baseline.1]
  unfold monMoneyCoef monNomCoef msvLambda msvDen
  norm_num

/-- Galí (2015), p. 72 (figure 3.3): at the baseline with `ρ_a = 0.9` the
output coefficient `κ (φ_π − ρ_a) Λ_a ≈ 0.808` lies in `(0, 1)`, and the output
gap and inflation fall after a technology improvement. -/
theorem technology_baseline :
    0.807 < techOutputCoef 0.99 1 κ₀ 1.5 0.125 0.9 ∧
      techOutputCoef 0.99 1 κ₀ 1.5 0.125 0.9 < 0.808 ∧
      techYgapCoef 0.99 1 κ₀ 1.5 0.125 0.9 1 < 0 ∧
      techInflCoef 0.99 1 κ₀ 1.5 0.125 0.9 1 < 0 := by
  rw [kappa_baseline.1]
  unfold techOutputCoef techYgapCoef techInflCoef msvLambda msvDen
  norm_num

/-- **Correction C3-3 at the baseline** (Galí 2015, p. 72): the corrected
employment coefficient is `≈ −0.2564`, the printed formula gives `≈ −0.1923`;
both are negative but they differ. -/
theorem employment_baseline :
    -0.2565 < techNCoef 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 ∧
      techNCoef 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 < -0.2564 ∧
      -0.1924 < techNCoefPrinted 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 ∧
      techNCoefPrinted 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 < -0.1923 ∧
      techNCoef 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25
        ≠ techNCoefPrinted 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 := by
  rw [kappa_baseline.1]
  unfold techNCoef techNCoefPrinted msvLambda msvDen
  norm_num

end Gali.BasicNewKeynesianModel.Calibration

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibrium under an exogenous money supply

Galí (2015), Chapter 3, §3.4.2, pp. 73–79. With the money supply exogenous, the
money-demand equation (4) joins the NKPC (22) and the DIS (23):

* (31), p. 74: money demand in terms of the output gap, `l_t = ỹ_t − η i_t + y^n_t`;
* (32), p. 74: eliminating `i_t`,
  `(1 + ση) ỹ_t = ση E_t ỹ_{t+1} + l̂_t + η E_t π_{t+1} + η r̂^n_t − ŷ^n_t`;
* (33), p. 74: the real-balance identity `l̂_{t−1} = l̂_t + π_t − Δm_t`;
* (34), p. 75: the 3×3 system `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t`;
* (35), p. 75: AR(1) money growth;
* p. 77: the interest-rate equation and its forward solution;
* p. 79: the money rule as a price-level rule.

## Conventions

All variables are deviations from steady state (constants dropped, as the book does
from (32) on). The predetermined variable `l̂_{t−1}` is the process `L t`, so `L (t + 1)`
is `l̂_t` and `L 0` is the initial condition `l̂_{−1}`. NKPC and DIS are stated here as
model equations with parameters (Galí (22), (23), p. 63).

## Main results

* `model_iff_system34`: the model equations ⇔ the matrix form (34).
* `det_AM1_sub_smul_AM0`: `det(A_{M,1} − z A_{M,0}) = (ση − z(1+ση))(β−z)(1−z) − ηκz(1−z) + κz²`.
* `charpoly_AM_eval`: the eigenvalues of `A_M = A_{M,0}⁻¹ A_{M,1}` are exactly the roots of
  that cubic.
* `charCubic_zero`, `charCubic_one`, `charCubic_expand`: `f(0) = σηβ > 0`, `f(1) = κ > 0`,
  leading coefficient `−(1+ση) < 0`.
* `AM_has_eigenvalue_gt_one`: `A_M` has a real eigenvalue strictly greater than one (IVT).
* `det_AM`, `det_AM_pos_lt_one`: the product of the eigenvalues is `σηβ/(1+ση) ∈ (0,1)`.
* `interest_rate_equation`: `i_t = η/(1+η) E_t i_{t+1} + ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}`.
* `interest_rate_forward_unique`, `interest_rate_forward_exists`: the forward solution is
  the unique bounded solution (genuine infinite sum).
* `interest_rate_log_utility`, `interest_rate_comoves`: `σ = 1 ⇒ i_t = ρ_m Δm_t/(1+η(1−ρ_m))`.
* `price_level_rule`: the p. 79 rewrite with `v_t = −η⁻¹ Δm_t`.

## Not yet claimed

The book's statement (p. 75, fn. 14) that `A_M` ALWAYS has two eigenvalues inside and one
outside the unit circle is supported in the book only numerically. Here it is recorded as
the proposition `BookDeterminacyClaim` and NOT proved: only the existence of one real
eigenvalue `> 1` and the product of the eigenvalues are proved.
-/

namespace Gali.BasicNewKeynesianModel.MoneyRule

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Model equations -/

/-- Galí (2015), eq. (22), p. 63: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (infl ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (23), p. 63 (deviations from steady state): the dynamic IS equation
`ỹ_t = −σ⁻¹(î_t − E_t π_{t+1} − r̂^n_t) + E_t ỹ_{t+1}`. -/
def DIS (σ : ℝ) (ygap infl i rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), eq. (31), p. 74 (deviations): money demand in terms of the output gap,
`l̂_t = ỹ_t − η î_t + ŷ^n_t`, with `l̂_t = L (t + 1)`. -/
def MoneyDemandGap (η : ℝ) (ygap i yn L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L (t + 1) = ygap t - η • i t + yn t

/-- Galí (2015), eq. (32), p. 74: the DIS with the interest rate eliminated,
`(1+ση) ỹ_t = ση E_t ỹ_{t+1} + l̂_t + η E_t π_{t+1} + η r̂^n_t − ŷ^n_t`. -/
def Eq32 (σ η : ℝ) (ygap infl L rn yn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + σ * η) • ygap t = (σ * η) • 𝔼.E t (ygap (t + 1)) + L (t + 1) +
    η • 𝔼.E t (infl (t + 1)) + η • rn t - yn t

/-- Galí (2015), eq. (33), p. 74: the real-balance identity `l̂_{t−1} = l̂_t + π_t − Δm_t`. -/
def RealBalanceId (infl L dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L t = L (t + 1) + infl t - dm t

/-- Galí (2015), p. 75: real balances `l̂_{t−1}` are predetermined, so `l̂_t` is known at `t`. -/
def Predetermined (L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (L (t + 1)) = L (t + 1)

omit 𝔼 in
/-- Galí (2015), eq. (31), p. 74: money demand (4), `m_t − p_t = y_t − η i_t`, with
`y_t = ỹ_t + y^n_t`, gives (31). -/
theorem eq31_of_money_demand (η : ℝ) {m p y ygap yn i L : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t) (hy : ∀ t, y t = ygap t + yn t)
    (hL : ∀ t, L (t + 1) = m t - p t) : MoneyDemandGap η ygap i yn L := by
  intro t
  rw [hL, hMD, hy]
  abel

omit 𝔼 in
/-- Galí (2015), eq. (33), p. 74: with `l_t = m_t − p_t`, `π_t = p_t − p_{t−1}` and
`Δm_t = m_t − m_{t−1}`, the real-balance identity holds at every date `t ≥ 1`. -/
theorem eq33_of_levels {m p L infl dm : ℕ → Ω → ℝ}
    (hL : ∀ t, L (t + 1) = m t - p t) (hp : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hm : ∀ t, dm (t + 1) = m (t + 1) - m t) (t : ℕ) :
    L (t + 1) = L (t + 1 + 1) + infl (t + 1) - dm (t + 1) := by
  rw [hL, hL, hp, hm]
  abel

/-- Galí (2015), eq. (32), p. 74: given money demand (31), the DIS (23) is equivalent to
(32) (for `σ ≠ 0`, `η ≠ 0`). -/
theorem dis_iff_eq32 {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) {ygap infl i rn yn L : ℕ → Ω → ℝ}
    (hMD : MoneyDemandGap η ygap i yn L) :
    DIS 𝔼 σ ygap infl i rn ↔ Eq32 𝔼 σ η ygap infl L rn yn := by
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2]
    have h1' : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      rw [h1]; field_simp
    linear_combination η * h1'
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    have h3 : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      have h4 : η * (σ * ygap t ω - (-(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
          σ * 𝔼.E t (ygap (t + 1)) ω)) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hη
      · linarith
    field_simp
    linear_combination h3

/-! ### The matrix form (34) -/

/-- Galí (2015), eq. (34), p. 75: the matrix `A_{M,0}`. -/
def AM0 (σ η κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1 + σ * η, 0, 0; -κ, 1, 0; 0, -1, 1]

/-- Galí (2015), eq. (34), p. 75: the matrix `A_{M,1}`. -/
def AM1 (σ η β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![σ * η, η, 1; 0, β, 0; 0, 0, 1]

/-- Galí (2015), eq. (34), p. 75: the matrix `B_M`. -/
def BM (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![η, -1, 0; 0, 0, 0; 0, 0, -1]

/-- Galí (2015), eq. (34), p. 75: the state `x_t = (ỹ_t, π_t, l̂_{t−1})`. -/
def stateVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![ygap t ω, infl t ω, L t ω]

/-- Galí (2015), eq. (34), p. 75: the forecast
`E_t x_{t+1} = (E_t ỹ_{t+1}, E_t π_{t+1}, E_t l̂_t)`. -/
def expVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![𝔼.E t (ygap (t + 1)) ω, 𝔼.E t (infl (t + 1)) ω, 𝔼.E t (L (t + 1)) ω]

omit 𝔼 in
/-- Galí (2015), eq. (34), p. 75: the shocks `(r̂^n_t, ŷ^n_t, Δm_t)`. -/
def shockVec (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![rn t ω, yn t ω, dm t ω]

/-- Galí (2015), eq. (34), p. 75: `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t` in every
state. -/
def System34 (σ η β κ : ℝ) (ygap infl L rn yn dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
    (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω)

/-- Galí (2015), eq. (34), p. 75: with `l̂` predetermined, the matrix system (34) is
equivalent to (32), the NKPC (22) and the identity (33). -/
theorem system34_iff {σ η β κ : ℝ} {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ η β κ ygap infl L rn yn dm ↔
      Eq32 𝔼 σ η ygap infl L rn yn ∧ NKPC 𝔼 β κ infl ygap ∧ RealBalanceId infl L dm := by
  constructor
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · have h0 := congrFun (h t ω) 0
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 ⊢
      linarith
    · have h1 := congrFun (h t ω) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h1 ⊢
      linarith
    · have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h2 ⊢
      linarith
  · rintro ⟨h32, h22, h33⟩ t ω
    have a := congrFun (h32 t) ω
    have b := congrFun (h22 t) ω
    have c := congrFun (h33 t) ω
    have hLω := congrFun (hL t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] <;> linarith

/-- Galí (2015), eqs. (22), (23), (31), (33) and (34), pp. 63–75: given money demand (31)
and predetermined real balances, the model equations NKPC, DIS and (33) hold if and only
if the matrix system (34) holds (`σ ≠ 0`, `η ≠ 0`). -/
theorem model_iff_system34 {σ η β κ : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    {ygap infl i L rn yn dm : ℕ → Ω → ℝ} (hMD : MoneyDemandGap η ygap i yn L)
    (hL : Predetermined 𝔼 L) :
    (NKPC 𝔼 β κ infl ygap ∧ DIS 𝔼 σ ygap infl i rn ∧ RealBalanceId infl L dm) ↔
      System34 𝔼 σ η β κ ygap infl L rn yn dm := by
  rw [system34_iff 𝔼 hL, dis_iff_eq32 𝔼 hσ hη hMD]
  tauto

/-! ### Eigenvalues of `A_M` -/

/-- Galí (2015), p. 75 (survey §3.1): the characteristic cubic
`f(z) = det(A_{M,1} − z A_{M,0}) = (ση − z(1+ση))(β−z)(1−z) − ηκz(1−z) + κz²`. -/
def charCubic (σ η β κ z : ℝ) : ℝ :=
  (σ * η - z * (1 + σ * η)) * (β - z) * (1 - z) - η * κ * z * (1 - z) + κ * z ^ 2

/-- Galí (2015), p. 75: `det(A_{M,1} − z A_{M,0})` is the characteristic cubic (exact). -/
theorem det_AM1_sub_smul_AM0 (σ η β κ z : ℝ) :
    (AM1 σ η β - z • AM0 σ η κ).det = charCubic σ η β κ z := by
  simp [Matrix.det_fin_three, AM0, AM1, charCubic]
  ring

/-- Galí (2015), p. 75: `det A_{M,0} = 1 + ση`. -/
theorem det_AM0 (σ η κ : ℝ) : (AM0 σ η κ).det = 1 + σ * η := by
  simp [Matrix.det_fin_three, AM0]

/-- Galí (2015), p. 75: `det A_{M,1} = σηβ`. -/
theorem det_AM1 (σ η β : ℝ) : (AM1 σ η β).det = σ * η * β := by
  simp [Matrix.det_fin_three, AM1]

/-- Galí (2015), p. 75: the matrix `A_M ≡ A_{M,0}⁻¹ A_{M,1}`. -/
noncomputable def AM (σ η β κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (AM0 σ η κ)⁻¹ * AM1 σ η β

/-- Galí (2015), p. 75: `det(A_M − z I) = (1+ση)⁻¹ f(z)` when `1 + ση ≠ 0`. -/
theorem det_AM_sub_smul {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
      (1 + σ * η)⁻¹ * charCubic σ η β κ z := by
  have hu : IsUnit (AM0 σ η κ).det := by rw [det_AM0]; exact h.isUnit
  have hfac : AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      (AM0 σ η κ)⁻¹ * (AM1 σ η β - z • AM0 σ η κ) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hu, AM]
  rw [hfac, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv',
    det_AM1_sub_smul_AM0]

/-- Galí (2015), p. 75: the characteristic polynomial of `A_M` evaluated at `z` is
`−(1+ση)⁻¹ f(z)`, so the eigenvalues of `A_M` are exactly the roots of `f`. -/
theorem charpoly_AM_eval {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.eval z = -((1 + σ * η)⁻¹ * charCubic σ η β κ z) := by
  rw [Matrix.eval_charpoly, ← det_AM_sub_smul h]
  have : Matrix.scalar (Fin 3) z - AM σ η β κ =
      -(AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
    rw [neg_sub, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [this, Matrix.det_neg]
  simp only [Fintype.card_fin]
  ring

/-- Galí (2015), p. 75: a real `z` is an eigenvalue of `A_M` iff `f(z) = 0`. -/
theorem isRoot_charpoly_AM_iff {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.IsRoot z ↔ charCubic σ η β κ z = 0 := by
  rw [Polynomial.IsRoot.def, charpoly_AM_eval h, neg_eq_zero, mul_eq_zero]
  simp [inv_eq_zero, h]

/-- Galí (2015), p. 75: the cubic expanded; its leading coefficient is `−(1+ση)`. -/
theorem charCubic_expand (σ η β κ z : ℝ) :
    charCubic σ η β κ z = -(1 + σ * η) * z ^ 3 +
      (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * z ^ 2 +
      (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * z + σ * η * β := by
  unfold charCubic
  ring

/-- Galí (2015), p. 75: `f(0) = σηβ`. -/
theorem charCubic_zero (σ η β κ : ℝ) : charCubic σ η β κ 0 = σ * η * β := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(1) = κ`. -/
theorem charCubic_one (σ η β κ : ℝ) : charCubic σ η β κ 1 = κ := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(0) > 0` and `f(1) > 0` for `σ, η, β, κ > 0`, and the leading
coefficient `−(1+ση)` is negative. -/
theorem charCubic_signs {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β) (hκ : 0 < κ) :
    0 < charCubic σ η β κ 0 ∧ 0 < charCubic σ η β κ 1 ∧ -(1 + σ * η) < 0 := by
  rw [charCubic_zero, charCubic_one]
  refine ⟨by positivity, hκ, ?_⟩
  have : 0 < σ * η := mul_pos hσ hη
  linarith

/-- Galí (2015), p. 75: the cubic has a real root strictly greater than one (IVT between
`f(1) = κ > 0` and a point where `f < 0`). -/
theorem charCubic_root_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ charCubic σ η β κ z = 0 := by
  set b := 1 + σ * η with hb
  set c₂ := σ * η + b * (1 + β) + η * κ + κ with hc₂
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb0 : 0 < b := by linarith
  have hc₂0 : 0 < c₂ := by
    have : 0 < η * κ := mul_pos hη hκ
    nlinarith
  set R := 1 + c₂ / b with hR
  have hR1 : 1 < R := by have := div_pos hc₂0 hb0; linarith
  have hbR : b * R = b + c₂ := by rw [hR]; field_simp
  have hfR : charCubic σ η β κ R < 0 := by
    rw [charCubic_expand]
    have hηκ : 0 < η * κ := mul_pos hη hκ
    have hsηβ : 0 < σ * η * β := by positivity
    have hlead : -b * R ^ 3 + c₂ * R ^ 2 = -b * R ^ 2 := by
      have : -b * R ^ 3 + c₂ * R ^ 2 = R ^ 2 * (c₂ - b * R) := by ring
      rw [this, hbR]; ring
    have hc1 : (-(σ * η) * (1 + β) - b * β - η * κ) * R ≤
        -(σ * η) * (1 + β) - b * β - η * κ := by
      have hneg : -(σ * η) * (1 + β) - b * β - η * κ < 0 := by nlinarith
      nlinarith
    have hR2 : 1 < R ^ 2 := by nlinarith
    have hsum : -(σ * η) * (1 + β) - b * β - η * κ + σ * η * β < 0 := by nlinarith
    have hfin : -b * R ^ 2 < 0 := by nlinarith
    calc -(1 + σ * η) * R ^ 3 + (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * R ^ 2 +
          (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * R + σ * η * β
        = (-b * R ^ 3 + c₂ * R ^ 2) +
          (-(σ * η) * (1 + β) - b * β - η * κ) * R + σ * η * β := by
          rw [hb, hc₂]
      _ < 0 := by rw [hlead]; linarith
  have hcont : ContinuousOn (charCubic σ η β κ) (Set.Icc 1 R) := by
    unfold charCubic
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (charCubic σ η β κ R) (charCubic σ η β κ 1) := by
    rw [charCubic_one]
    exact ⟨hfR, hκ⟩
  obtain ⟨z, ⟨hz1, -⟩, hz⟩ := intermediate_value_Ioo' hR1.le hcont hmem
  exact ⟨z, hz1, hz⟩

/-- Galí (2015), p. 75: for `σ, η, β, κ > 0`, `A_M` has a real eigenvalue strictly
greater than one (so at least one eigenvalue lies outside the unit circle). -/
theorem AM_has_eigenvalue_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ (AM σ η β κ).charpoly.IsRoot z := by
  obtain ⟨z, hz1, hz⟩ := charCubic_root_gt_one hσ hη hβ hκ
  have h : 1 + σ * η ≠ 0 := by have := mul_pos hσ hη; linarith
  exact ⟨z, hz1, (isRoot_charpoly_AM_iff h z).mpr hz⟩

/-- Galí (2015), p. 75: `det A_M = σηβ/(1+ση)`, the product of the three eigenvalues. -/
theorem det_AM {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) :
    (AM σ η β κ).det = σ * η * β / (1 + σ * η) := by
  rw [AM, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv', det_AM1]
  field_simp

/-- Galí (2015), p. 75: for `σ, η > 0` and `0 < β < 1`, the product of the eigenvalues of
`A_M` lies in `(0, 1)`. -/
theorem det_AM_pos_lt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hβ1 : β < 1) : 0 < (AM σ η β κ).det ∧ (AM σ η β κ).det < 1 := by
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb : 0 < 1 + σ * η := by linarith
  rw [det_AM hb.ne']
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hb]
  nlinarith

/-- Galí (2015), p. 75 and fn. 14: the book's determinacy claim, NOT YET CLAIMED here:
the cubic factors as `−(1+ση)(z − r)(z² + q₁ z + q₀)` with `r > 1` and both roots of the
quadratic factor inside the unit circle (Schur–Cohn). The book supports it numerically
only; this definition records the statement without proof. -/
def BookDeterminacyClaim (σ η β κ : ℝ) : Prop :=
  ∃ r q₁ q₀ : ℝ, 1 < r ∧
    (∀ z, charCubic σ η β κ z = -(1 + σ * η) * (z - r) * (z ^ 2 + q₁ * z + q₀)) ∧
    SchurStable (-q₁) q₀

/-! ### Money growth and the interest rate (pp. 75–77) -/

/-- Galí (2015), eq. (35), p. 75: money growth `Δm_{t+1} = ρ_m Δm_t + ε^m_{t+1}` with
innovations of conditional mean zero is an AR(1) process. -/
theorem moneyGrowth_isAR1 {ρm : ℝ} {dm ε : ℕ → Ω → ℝ} (hadapt : 𝔼.Adapted dm)
    (hlaw : ∀ t, dm (t + 1) = ρm • dm t + ε (t + 1)) (hε : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    𝔼.IsAR1 ρm dm := by
  refine ⟨hadapt, fun t => ?_⟩
  rw [hlaw, map_add, map_smul, hadapt t, hε, add_zero]

/-- Galí (2015), p. 77: combining money demand (4), `m_t − p_t = y_t − η i_t`, with the DIS
(23) (natural rate and natural output constant, deviations) gives
`(1+η) i_t = η E_t i_{t+1} + E_t Δm_{t+1} + (σ−1) E_t Δy_{t+1}`. -/
theorem interest_rate_equation_raw {σ η : ℝ} (hσ : σ ≠ 0) {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (t : ℕ) :
    (1 + η) • i t = η • 𝔼.E t (i (t + 1)) + 𝔼.E t (dm (t + 1)) +
      (σ - 1) • 𝔼.E t (dy (t + 1)) := by
  have hMD1 := congrArg (𝔼.E t) (hMD (t + 1))
  rw [hm, hp, hy] at hMD1
  simp only [map_sub, map_add, map_smul, hap t, ham t, hay t] at hMD1
  have hIS' := hIS t
  rw [hy, map_add, hay t] at hIS'
  funext ω
  have a := congrFun hMD1 ω
  have b := congrFun (hMD t) ω
  have c := congrFun hIS' ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c ⊢
  have c' : 𝔼.E t (infl (t + 1)) ω = i t ω - σ * 𝔼.E t (dy (t + 1)) ω := by
    have : σ⁻¹ * (i t ω - 𝔼.E t (infl (t + 1)) ω) = 𝔼.E t (dy (t + 1)) ω := by linarith
    field_simp at this
    linarith
  linear_combination b - a - c'

/-- Galí (2015), p. 77: with AR(1) money growth (35), the interest-rate equation
`i_t = η/(1+η) E_t i_{t+1} + ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}` (for `η ≠ −1`). -/
theorem interest_rate_equation {σ η ρm : ℝ} (hσ : σ ≠ 0) (hη : 1 + η ≠ 0)
    {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (hdm : 𝔼.IsAR1 ρm dm)
    (t : ℕ) :
    i t = (η / (1 + η)) • 𝔼.E t (i (t + 1)) + (ρm / (1 + η)) • dm t +
      ((σ - 1) / (1 + η)) • 𝔼.E t (dy (t + 1)) := by
  have h := interest_rate_equation_raw 𝔼 hσ hMD hIS hp hm hy hap ham hay t
  rw [hdm.2 t] at h
  funext ω
  have a := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a ⊢
  field_simp
  linear_combination a

/-! ### Forward solutions as genuine infinite sums -/

/-- Galí (2015), p. 77 (used for the forward solution): `E_t` commutes with a series
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

/-- Galí (2015), p. 77: the forward solution `z_t = ∑_{k ≥ 0} aᵏ E_t u_{t+k}` of
`z_t = a E_t z_{t+1} + u_t`. -/
noncomputable def forwardSeries (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω

/-- Galí (2015), p. 77: the forward series is summable for bounded forcing. -/
theorem forwardSeries_summable {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable (fun k => a ^ k * 𝔼.E t (u (t + k)) ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg ha0 k)

/-- Galí (2015), p. 77: the forward series solves `z_t = a E_t z_{t+1} + u_t` for bounded
adapted forcing `u` and `0 ≤ a < 1`. -/
theorem forwardSeries_solves {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) (t : ℕ) :
    forwardSeries 𝔼 a u t = a • 𝔼.E t (forwardSeries 𝔼 a u (t + 1)) + u t := by
  funext ω
  have hE : 𝔼.E t (forwardSeries 𝔼 a u (t + 1)) ω =
      ∑' k, a ^ k * 𝔼.E t (u (t + 1 + k)) ω := by
    have hb : ∀ k ω', |a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ a ^ k * M := by
      intro k ω'
      rw [abs_mul, abs_pow, abs_of_nonneg ha0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + 1 + k)) (t + 1) ω')
        (pow_nonneg ha0 k)
    change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
    rw [E_tsum 𝔼 ha0 ha1 hb t ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
    rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
  rw [hE, (forwardSeries_summable 𝔼 ha0 ha1 hu t ω).tsum_eq_zero_add,
    pow_zero, one_mul, add_zero, hadapt t, ← tsum_mul_left, add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Galí (2015), p. 77: the forward series is bounded by `M / (1 − a)`. -/
theorem forwardSeries_bounded {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (forwardSeries 𝔼 a u) := by
  refine ⟨M / (1 - a), fun t ω => ?_⟩
  have hs := forwardSeries_summable 𝔼 ha0 ha1 hu t ω
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

/-- Galí (2015), p. 77: any bounded solution of `z_t = a E_t z_{t+1} + u_t` (bounded
adapted `u`, `0 ≤ a < 1`) is the forward series. -/
theorem eq_forwardSeries {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u z : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u)
    (hz : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) (hzb : BoundedProc z) :
    z = forwardSeries 𝔼 a u := by
  have ha : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  exact 𝔼.forward_unique ha hz (forwardSeries_solves 𝔼 ha0 ha1 hu hadapt) hzb
    (forwardSeries_bounded 𝔼 ha0 ha1 hu)

/-- Galí (2015), p. 77: the forcing term of the interest-rate equation,
`u_t = ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}`. -/
noncomputable def rateForcing (σ η ρm : ℝ) (dm dy : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (ρm / (1 + η)) • dm t + ((σ - 1) / (1 + η)) • 𝔼.E t (dy (t + 1))

/-- Galí (2015), p. 77: the printed forward solution
`i_t = ρ_m/(1+η(1−ρ_m)) Δm_t + (σ−1)/(1+η) ∑_{k≥0} (η/(1+η))ᵏ E_t Δy_{t+1+k}`. -/
noncomputable def rateForward (σ η ρm : ℝ) (dm dy : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ρm / (1 + η * (1 - ρm)) * dm t ω +
    (σ - 1) / (1 + η) * ∑' k, (η / (1 + η)) ^ k * 𝔼.E t (dy (t + 1 + k)) ω

/-- Galí (2015), p. 77: the forward series of the interest-rate equation equals the printed
closed form (`η ≥ 0`, `|ρ_m| < 1`, bounded `Δy`). -/
theorem forwardSeries_rate_eq {σ η ρm Mdy : ℝ} (hη : 0 ≤ η) (hρ : |ρm| < 1)
    {dm dy : ℕ → Ω → ℝ} (hdm : 𝔼.IsAR1 ρm dm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) :
    forwardSeries 𝔼 (η / (1 + η)) (rateForcing 𝔼 σ η ρm dm dy) =
      rateForward 𝔼 σ η ρm dm dy := by
  funext t ω
  set a := η / (1 + η) with ha
  have h1η : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ a := div_nonneg hη h1η.le
  have ha1 : a < 1 := by rw [ha, div_lt_one h1η]; linarith
  have haρ : |a * ρm| < 1 := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |ρm| ≤ 1 * |ρm| := mul_le_mul_of_nonneg_right ha1.le (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact hρ
  have hterm : ∀ k, a ^ k * 𝔼.E t (rateForcing 𝔼 σ η ρm dm dy (t + k)) ω =
      ρm / (1 + η) * dm t ω * (a * ρm) ^ k +
        (σ - 1) / (1 + η) * (a ^ k * 𝔼.E t (dy (t + 1 + k)) ω) := by
    intro k
    have hdmk := congrFun (𝔼.ar1_iterate hdm t k) ω
    have hdyk : 𝔼.E t (𝔼.E (t + k) (dy (t + k + 1))) = 𝔼.E t (dy (t + 1 + k)) := by
      rw [𝔼.tower (Nat.le_add_right t k), show t + k + 1 = t + 1 + k by omega]
    simp only [rateForcing, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hdmk, hdyk]
    ring
  have hs1 : Summable (fun k : ℕ => ρm / (1 + η) * dm t ω * (a * ρm) ^ k) :=
    (summable_geometric_of_abs_lt_one haρ).mul_left _
  have hs2 : Summable (fun k => (σ - 1) / (1 + η) * (a ^ k * 𝔼.E t (dy (t + 1 + k)) ω)) := by
    refine (Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right Mdy)
      (fun k => ?_)).mul_left ((σ - 1) / (1 + η))
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdy (t + 1 + k)) t ω) (pow_nonneg ha0 k)
  rw [forwardSeries, tsum_congr hterm, hs1.tsum_add hs2, tsum_mul_left,
    tsum_geometric_of_abs_lt_one haρ, tsum_mul_left, rateForward]
  congr 1
  have h2 : 0 < 1 + η * (1 - ρm) := by
    have : ρm < 1 := (abs_lt.mp hρ).2
    nlinarith
  have hx : 1 - η / (1 + η) * ρm = (1 + η * (1 - ρm)) / (1 + η) := by
    field_simp
    ring
  rw [ha, hx]
  field_simp

/-- Galí (2015), p. 77: the forcing term is adapted. -/
theorem rateForcing_adapted {σ η ρm : ℝ} {dm dy : ℕ → Ω → ℝ} (hdm : 𝔼.Adapted dm) :
    𝔼.Adapted (rateForcing 𝔼 σ η ρm dm dy) := by
  intro t
  simp only [rateForcing, map_add, map_smul, hdm t, 𝔼.E_E_self]

/-- Galí (2015), p. 77: the forcing term is bounded when `Δm` and `Δy` are. -/
theorem rateForcing_bounded {σ η ρm Mdm Mdy : ℝ} {dm dy : ℕ → Ω → ℝ}
    (hdmb : ∀ t ω, |dm t ω| ≤ Mdm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) (t : ℕ) (ω : Ω) :
    |rateForcing 𝔼 σ η ρm dm dy t ω| ≤ |ρm / (1 + η)| * Mdm + |(σ - 1) / (1 + η)| * Mdy := by
  simp only [rateForcing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hdmb t ω) (abs_nonneg _)
  · exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdy (t + 1)) t ω) (abs_nonneg _)

/-- Galí (2015), p. 77: the forward solution exists: the printed closed form solves
`i_t = η/(1+η) E_t i_{t+1} + ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}` and is bounded
(`η ≥ 0`, `|ρ_m| < 1`, bounded `Δm`, `Δy`). -/
theorem interest_rate_forward_exists {σ η ρm Mdm Mdy : ℝ} (hη : 0 ≤ η) (hρ : |ρm| < 1)
    {dm dy : ℕ → Ω → ℝ} (hdm : 𝔼.IsAR1 ρm dm) (hdmb : ∀ t ω, |dm t ω| ≤ Mdm)
    (hdy : ∀ t ω, |dy t ω| ≤ Mdy) :
    (∀ t, rateForward 𝔼 σ η ρm dm dy t =
      (η / (1 + η)) • 𝔼.E t (rateForward 𝔼 σ η ρm dm dy (t + 1)) + (ρm / (1 + η)) • dm t +
        ((σ - 1) / (1 + η)) • 𝔼.E t (dy (t + 1))) ∧
      BoundedProc (rateForward 𝔼 σ η ρm dm dy) := by
  have h1η : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1η.le
  have ha1 : η / (1 + η) < 1 := by rw [div_lt_one h1η]; linarith
  have hub := rateForcing_bounded 𝔼 (σ := σ) (η := η) (ρm := ρm) hdmb hdy
  rw [← forwardSeries_rate_eq 𝔼 hη hρ hdm hdy]
  refine ⟨fun t => ?_, forwardSeries_bounded 𝔼 ha0 ha1 hub⟩
  rw [forwardSeries_solves 𝔼 ha0 ha1 hub (rateForcing_adapted 𝔼 hdm.1) t, rateForcing,
    add_assoc]

/-- Galí (2015), p. 77: the forward solution is the unique bounded equilibrium interest
rate: under money demand (4), the DIS (23), AR(1) money growth (35) and bounded `Δm`, `Δy`,
every bounded `i` equals
`ρ_m/(1+η(1−ρ_m)) Δm_t + (σ−1)/(1+η) ∑_{k≥0} (η/(1+η))ᵏ E_t Δy_{t+1+k}`. -/
theorem interest_rate_forward_unique {σ η ρm Mdm Mdy : ℝ} (hσ : σ ≠ 0) (hη : 0 ≤ η)
    (hρ : |ρm| < 1) {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (hdm : 𝔼.IsAR1 ρm dm)
    (hdmb : ∀ t ω, |dm t ω| ≤ Mdm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) (hib : BoundedProc i) :
    i = rateForward 𝔼 σ η ρm dm dy := by
  have h1η : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1η.le
  have ha1 : η / (1 + η) < 1 := by rw [div_lt_one h1η]; linarith
  have hub := rateForcing_bounded 𝔼 (σ := σ) (η := η) (ρm := ρm) hdmb hdy
  have hi : ∀ t, i t = (η / (1 + η)) • 𝔼.E t (i (t + 1)) +
      rateForcing 𝔼 σ η ρm dm dy t := fun t => by
    rw [rateForcing, ← add_assoc]
    exact interest_rate_equation 𝔼 hσ h1η.ne' hMD hIS hp hm hy hap ham hay hdm t
  rw [eq_forwardSeries 𝔼 ha0 ha1 hub (rateForcing_adapted 𝔼 hdm.1) hi hib,
    forwardSeries_rate_eq 𝔼 hη hρ hdm hdy]

/-- Galí (2015), p. 77: with log utility (`σ = 1`) the bounded equilibrium interest rate is
`i_t = ρ_m Δm_t / (1 + η(1−ρ_m))`. -/
theorem interest_rate_log_utility {η ρm Mdm Mdy : ℝ} (hη : 0 ≤ η)
    (hρ : |ρm| < 1) {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - (1 : ℝ)⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (hdm : 𝔼.IsAR1 ρm dm)
    (hdmb : ∀ t ω, |dm t ω| ≤ Mdm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) (hib : BoundedProc i)
    (t : ℕ) : i t = (ρm / (1 + η * (1 - ρm))) • dm t := by
  rw [interest_rate_forward_unique 𝔼 one_ne_zero hη hρ hMD hIS hp hm hy hap ham hay hdm hdmb
    hdy hib]
  funext ω
  simp [rateForward]

/-- Galí (2015), p. 77: for `ρ_m ∈ [0, 1)` and `η ≥ 0` the coefficient
`ρ_m/(1+η(1−ρ_m))` is nonnegative (positive if `ρ_m > 0`), so with `σ = 1` the nominal
rate comoves positively with money growth: `i_t Δm_t ≥ 0` in every state. -/
theorem interest_rate_comoves {η ρm : ℝ} (hη : 0 ≤ η) (hρ0 : 0 ≤ ρm) (hρ1 : ρm < 1)
    {i dm : ℕ → Ω → ℝ} (hi : ∀ t, i t = (ρm / (1 + η * (1 - ρm))) • dm t) :
    0 ≤ ρm / (1 + η * (1 - ρm)) ∧ (0 < ρm → 0 < ρm / (1 + η * (1 - ρm))) ∧
      ∀ t ω, 0 ≤ i t ω * dm t ω := by
  have hden : 0 < 1 + η * (1 - ρm) := by nlinarith
  refine ⟨div_nonneg hρ0 hden.le, fun h => div_pos h hden, fun t ω => ?_⟩
  rw [hi t, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact mul_nonneg (div_nonneg hρ0 hden.le) (mul_self_nonneg _)

/-- Galí (2015), p. 77: a liquidity effect is possible: if `σ > 1` and the expected
discounted output growth `∑ (η/(1+η))ᵏ E_t Δy_{t+1+k}` is negative, the nominal rate lies
below the money-growth term `ρ_m Δm_t/(1+η(1−ρ_m))`. -/
theorem liquidity_effect_of_sigma_gt_one {σ η ρm : ℝ} (hσ : 1 < σ) (hη : 0 ≤ η)
    {dm dy : ℕ → Ω → ℝ} (t : ℕ) (ω : Ω)
    (hneg : ∑' k, (η / (1 + η)) ^ k * 𝔼.E t (dy (t + 1 + k)) ω < 0) :
    rateForward 𝔼 σ η ρm dm dy t ω < ρm / (1 + η * (1 - ρm)) * dm t ω := by
  have h1η : 0 < 1 + η := by linarith
  have hc : 0 < (σ - 1) / (1 + η) := div_pos (by linarith) h1η
  have := mul_neg_of_pos_of_neg hc hneg
  simp only [rateForward]
  linarith

omit 𝔼 in
/-- Galí (2015), p. 79: money demand (4), `m_t − p_t = ŷ_t − η i_t`, rewritten as an
interest-rate rule targeting the price level, with `v_t = −η⁻¹ Δm_t`:
`i_t = η⁻¹(p_t − m_{t−1}) + η⁻¹ ŷ_t + v_t = η⁻¹(p_{t−1} − m_{t−1}) + η⁻¹ π_t + η⁻¹ ŷ_t + v_t`
(stated at dates `t + 1 ≥ 1`). -/
theorem price_level_rule {η : ℝ} (hη : η ≠ 0) {m p y i infl dm v : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t) (hp : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hm : ∀ t, dm (t + 1) = m (t + 1) - m t) (hv : ∀ t, v t = -η⁻¹ • dm t) (t : ℕ) :
    i (t + 1) = η⁻¹ • (p (t + 1) - m t) + η⁻¹ • y (t + 1) + v (t + 1) ∧
      i (t + 1) = η⁻¹ • (p t - m t) + η⁻¹ • infl (t + 1) + η⁻¹ • y (t + 1) + v (t + 1) := by
  have key : i (t + 1) = η⁻¹ • (p (t + 1) - m t) + η⁻¹ • y (t + 1) + v (t + 1) := by
    funext ω
    have a := congrFun (hMD (t + 1)) ω
    have b := congrFun (hm t) ω
    have c := congrFun (hv (t + 1)) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c ⊢
    rw [c, b, show i (t + 1) ω = η⁻¹ * (η * i (t + 1) ω) by field_simp]
    linear_combination η⁻¹ * a
  refine ⟨key, ?_⟩
  rw [key, hp]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Gali.BasicNewKeynesianModel.MoneyRule

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.1: discrete records of exponential price durations

Galí (2015), Chapter 3, Exercise 3.1 (pp. 88–89). Prices change in continuous time, and the
duration `T` (in months) of a price spell has the exponential law with density
`f(t) = φ e^{−φt}`, i.e. `T ∼ expMeasure φ` (Mathlib's exponential distribution, the gamma
law with shape one). Every statement below is a statement about this probability measure.

## Main results

* (a) `hazard_eq`, `hazard_tendsto`, `cond_change_prob`: the hazard `f(t)/(1 − F(t))` equals
  `φ` at every date, and the conditional probability of a change in `(t, t + h]` divided by
  `h` tends to `φ` as `h ↓ 0`, at every `t ≥ 0`; `memoryless`.
* (b) `mean_duration` (`∫ T = 1/φ`), `median_duration` and `cdf_eq_half_iff` (the median is
  `log 2/φ` and it is the unique one), `median_div_mean` (the ratio is `log 2`) and
  `median_lt_mean`.
* (c) `monthly_change_prob`: whatever the age of a price at a monthly record date, the
  probability that the next record differs is `λ = 1 − e^{−φ}`; `lambda_eq_iff` inverts this
  as the estimator `φ = −log(1 − λ)`; `lambda_lt_phi` (the raw frequency understates `φ`,
  because a price may change more than once within a month).
* (d) `quarterly_survival`: the probability that a price is not changed over a quarter is
  `θ = e^{−3φ} = (1 − λ)³`; `quarterlyCalvo` is the implied quarterly Calvo parameter and
  `quarterlyCalvo_mean_duration` its mean duration in quarters.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_1

open MeasureTheory ProbabilityTheory Filter Topology

/-- Galí (2015), Ex. 3.1, p. 88: the distribution function of the exponential duration,
`F(t) = 1 − e^{−φt}` for `t ≥ 0`. -/
theorem cdf_eq {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    cdf (expMeasure φ) t = 1 - Real.exp (-(φ * t)) := by
  rw [cdf_expMeasure_eq hφ]
  simp only [ht, ↓reduceIte]

/-- Galí (2015), Ex. 3.1, p. 88: `P(T ≤ t) = 1 − e^{−φt}` for `t ≥ 0`. -/
theorem prob_le {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    (expMeasure φ).real (Set.Iic t) = 1 - Real.exp (-(φ * t)) := by
  have := isProbabilityMeasure_expMeasure hφ
  rw [← cdf_eq_real, cdf_eq hφ ht]

/-- Galí (2015), Ex. 3.1, p. 88: the survival function, `P(T > t) = e^{−φt}` for `t ≥ 0`. -/
theorem survival {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    (expMeasure φ).real (Set.Ioi t) = Real.exp (-(φ * t)) := by
  have := isProbabilityMeasure_expMeasure hφ
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, prob_le hφ ht]
  ring

/-- Galí (2015), Ex. 3.1, p. 88: the survival probability is positive. -/
theorem survival_pos {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    0 < (expMeasure φ).real (Set.Ioi t) := by
  rw [survival hφ ht]
  exact Real.exp_pos _

/-- Galí (2015), Ex. 3.1, p. 88: the probability of a price change in the window
`(t, t + h]`, `P(t < T ≤ t + h) = e^{−φt}(1 − e^{−φh})`. -/
theorem prob_window {φ t h : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    (expMeasure φ).real (Set.Ioc t (t + h)) = Real.exp (-(φ * t)) * (1 - Real.exp (-(φ * h))) := by
  have := isProbabilityMeasure_expMeasure hφ
  rw [← Set.Ioi_sdiff_Ioi, measureReal_sdiff (Set.Ioi_subset_Ioi (by linarith)) measurableSet_Ioi,
    survival hφ ht, survival hφ (by linarith)]
  rw [mul_sub, mul_one, ← Real.exp_add]
  ring_nf

/-- Galí (2015), Ex. 3.1(a), p. 88: **memorylessness**,
`P(T > t + s | T > t) = P(T > s)` for `t, s ≥ 0`. -/
theorem memoryless {φ t s : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (expMeasure φ).real (Set.Ioi (t + s)) / (expMeasure φ).real (Set.Ioi t)
      = (expMeasure φ).real (Set.Ioi s) := by
  rw [survival hφ (by linarith), survival hφ ht, survival hφ hs, div_eq_iff (Real.exp_pos _).ne',
    ← Real.exp_add]
  ring_nf

/-- Galí (2015), Ex. 3.1(a), p. 88: the **hazard rate** `f(t)/(1 − F(t))` equals `φ` at every
date `t ≥ 0`. -/
theorem hazard_eq {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    exponentialPDFReal φ t / (expMeasure φ).real (Set.Ioi t) = φ := by
  rw [survival hφ ht, exponentialPDFReal, gammaPDFReal]
  simp only [ht, ↓reduceIte, Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero,
    mul_one]
  rw [mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]

/-- Galí (2015), Ex. 3.1(a), p. 88: the conditional probability of a price change within
`h` months, given that the price has survived to `t`, is `1 − e^{−φh}`, independently of
`t` (the change probability is constant over time). -/
theorem cond_change_prob {φ t h : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    (expMeasure φ).real (Set.Ioc t (t + h)) / (expMeasure φ).real (Set.Ioi t)
      = 1 - Real.exp (-(φ * h)) := by
  rw [prob_window hφ ht hh, survival hφ ht, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

/-- Galí (2015), Ex. 3.1(a), p. 88: the **instantaneous probability of a price change** is
`φ` at every date: `P(t < T ≤ t + h | T > t)/h → φ` as `h ↓ 0`, for every `t ≥ 0`. -/
theorem hazard_tendsto {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    Tendsto (fun h => (expMeasure φ).real (Set.Ioc t (t + h)) /
      (h * (expMeasure φ).real (Set.Ioi t))) (𝓝[>] 0) (𝓝 φ) := by
  have hd : HasDerivAt (fun h : ℝ => -Real.exp (-(φ * h))) φ 0 := by
    have h1 : HasDerivAt (fun h : ℝ => -(φ * h)) (-φ) 0 := by
      have := (hasDerivAt_id (0 : ℝ)).const_mul (-φ)
      simp only [id, mul_one] at this
      convert this using 1
      ext h
      ring
    have h2 := HasDerivAt.neg (HasDerivAt.exp h1)
    convert h2 using 1
    simp
  refine tendsto_nhdsWithin_congr (fun h (hh : 0 < h) => ?_) hd.tendsto_slope_zero_right
  rw [div_mul_eq_div_div_swap, cond_change_prob hφ ht hh.le]
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Ex. 3.1(b), p. 89: the **mean duration** of a price is `E[T] = 1/φ`. -/
theorem mean_duration {φ : ℝ} (hφ : 0 < φ) : ∫ x, x ∂(expMeasure φ) = 1 / φ := by
  have hmeas : Measurable (gammaPDF 1 φ) := (measurable_gammaPDFReal 1 φ).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hpdf : ∀ x, (gammaPDF 1 φ x).toReal = gammaPDFReal 1 φ x := fun x =>
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hφ x)
  simp_rw [hpdf, smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi 0) (fun x hx => by
    simp only [Set.mem_Ioi, not_lt] at hx
    rcases hx.lt_or_eq with h | h
    · simp [gammaPDFReal, not_le.mpr h]
    · simp [h])]
  have hcongr : ∀ x ∈ Set.Ioi (0 : ℝ), gammaPDFReal 1 φ x * x
      = φ * (x ^ ((2 : ℝ) - 1) * Real.exp (-(φ * x))) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    simp only [gammaPDFReal, hx0, ↓reduceIte, Real.rpow_one, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one]
    norm_num
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi two_pos hφ]
  have hG : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
      mul_one]
  rw [hG, Real.rpow_two]
  field_simp

/-- Galí (2015), Ex. 3.1(b), p. 89: the **median duration** is `log 2/φ`: exactly half of
all prices last at most `log 2/φ` months and half last longer. -/
theorem median_duration {φ : ℝ} (hφ : 0 < φ) :
    (expMeasure φ).real (Set.Iic (Real.log 2 / φ)) = 1 / 2 ∧
      (expMeasure φ).real (Set.Ioi (Real.log 2 / φ)) = 1 / 2 := by
  have hm : 0 ≤ Real.log 2 / φ := div_nonneg (Real.log_nonneg (by norm_num)) hφ.le
  have he : Real.exp (-(φ * (Real.log 2 / φ))) = 1 / 2 := by
    rw [mul_div_cancel₀ _ hφ.ne', Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [prob_le hφ hm, survival hφ hm, he]
  norm_num

/-- Galí (2015), Ex. 3.1(b), p. 89: the median is unique: `F(t) = 1/2` iff `t = log 2/φ`. -/
theorem cdf_eq_half_iff {φ t : ℝ} (hφ : 0 < φ) :
    cdf (expMeasure φ) t = 1 / 2 ↔ t = Real.log 2 / φ := by
  rw [cdf_expMeasure_eq hφ]
  by_cases ht : 0 ≤ t
  · simp only [ht, ↓reduceIte]
    constructor
    · intro h
      have he : Real.exp (-(φ * t)) = 2⁻¹ := by linarith
      have hl := congrArg Real.log he
      rw [Real.log_exp, Real.log_inv] at hl
      field_simp
      linarith
    · intro h
      rw [h, mul_div_cancel₀ _ hφ.ne', Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
  · simp only [ht, ↓reduceIte]
    constructor
    · intro h; norm_num at h
    · intro h
      exact absurd (h ▸ div_nonneg (Real.log_nonneg (by norm_num)) hφ.le) ht

/-- Galí (2015), Ex. 3.1(b), p. 89: the ratio of the median to the mean duration is
`log 2 ≈ 0.69`, independently of `φ`. -/
theorem median_div_mean {φ : ℝ} (hφ : 0 < φ) :
    (Real.log 2 / φ) / ∫ x, x ∂(expMeasure φ) = Real.log 2 := by
  rw [mean_duration hφ]
  field_simp

/-- Galí (2015), Ex. 3.1(b), p. 89: the median duration is strictly below the mean. -/
theorem median_lt_mean {φ : ℝ} (hφ : 0 < φ) : Real.log 2 / φ < ∫ x, x ∂(expMeasure φ) := by
  rw [mean_duration hφ]
  have h2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  exact div_lt_div_of_pos_right h2 hφ

/-- Galí (2015), Ex. 3.1(c), p. 89: the monthly frequency of price changes implied by a
rate `φ`, `λ = 1 − e^{−φ}`. -/
noncomputable def monthlyFreq (φ : ℝ) : ℝ := 1 - Real.exp (-φ)

/-- Galí (2015), Ex. 3.1(c), p. 89: whatever the age `a ≥ 0` of a price at a monthly record
date, the probability that the next monthly record differs (at least one change within the
month, possibly several) is `λ = 1 − e^{−φ}`. Hence the fraction `λ_t` of items whose
recorded price changes estimates `λ` whatever the age distribution of prices. -/
theorem monthly_change_prob {φ a : ℝ} (hφ : 0 < φ) (ha : 0 ≤ a) :
    (expMeasure φ).real (Set.Ioc a (a + 1)) / (expMeasure φ).real (Set.Ioi a) = monthlyFreq φ := by
  rw [cond_change_prob hφ ha zero_le_one, mul_one, monthlyFreq]

/-- Galí (2015), Ex. 3.1(c), p. 89: estimating `φ`: the observed monthly frequency `λ < 1`
equals `1 − e^{−φ}` if and only if `φ = −log(1 − λ)`. -/
theorem lambda_eq_iff {φ lam : ℝ} (hl : lam < 1) :
    monthlyFreq φ = lam ↔ φ = -Real.log (1 - lam) := by
  rw [monthlyFreq]
  constructor
  · intro h
    have : Real.exp (-φ) = 1 - lam := by linarith
    rw [← this, Real.log_exp, neg_neg]
  · intro h
    rw [h, neg_neg, Real.exp_log (by linarith)]
    ring

/-- Galí (2015), Ex. 3.1(c), p. 89: the monthly frequency lies in `(0, 1)` for `φ > 0`. -/
theorem monthlyFreq_mem {φ : ℝ} (hφ : 0 < φ) : 0 < monthlyFreq φ ∧ monthlyFreq φ < 1 := by
  rw [monthlyFreq]
  constructor
  · have : Real.exp (-φ) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  · have := Real.exp_pos (-φ)
    linarith

/-- Galí (2015), Ex. 3.1(c), p. 89: the raw monthly frequency `λ` understates the rate `φ`
(`1 − e^{−φ} < φ` for `φ ≠ 0`), because a price may change more than once in a month. -/
theorem lambda_lt_phi {φ : ℝ} (hφ : φ ≠ 0) : monthlyFreq φ < φ := by
  rw [monthlyFreq]
  have := Real.add_one_lt_exp (neg_ne_zero.mpr hφ)
  linarith

/-- Galí (2015), Ex. 3.1(d), p. 89: the probability that a price survives a quarter (three
months), whatever its age `a ≥ 0`, is `θ = e^{−3φ} = (1 − λ)³`. This is the quarterly Calvo
parameter. -/
theorem quarterly_survival {φ a : ℝ} (hφ : 0 < φ) (ha : 0 ≤ a) :
    (expMeasure φ).real (Set.Ioi (a + 3)) / (expMeasure φ).real (Set.Ioi a)
      = Real.exp (-(3 * φ)) ∧ Real.exp (-(3 * φ)) = (1 - monthlyFreq φ) ^ 3 := by
  constructor
  · rw [memoryless hφ ha (by norm_num), survival hφ (by norm_num), mul_comm]
  · rw [monthlyFreq, sub_sub_cancel, ← Real.exp_nat_mul]
    norm_num

/-- Galí (2015), Ex. 3.1(d), p. 89: the quarterly Calvo parameter `θ = (1 − λ)³` calibrated
from a monthly frequency `λ ∈ (0, 1]`. -/
noncomputable def quarterlyCalvo (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) : CalvoParam where
  θ := (1 - lam) ^ 3
  nonneg := pow_nonneg (by linarith) 3
  lt_one := by
    have ha : 0 ≤ 1 - lam := by linarith
    have hb : 1 - lam < 1 := by linarith
    calc (1 - lam) ^ 3 ≤ 1 - lam := pow_le_of_le_one ha hb.le (by norm_num)
      _ < 1 := hb

/-- Galí (2015), Ex. 3.1(d), p. 89: calibrated from `λ = 1 − e^{−φ}`, the quarterly Calvo
parameter equals the quarterly survival probability `e^{−3φ}`. -/
theorem quarterlyCalvo_theta {φ : ℝ} (hφ : 0 < φ) :
    (quarterlyCalvo (monthlyFreq φ) (monthlyFreq_mem hφ).1 (monthlyFreq_mem hφ).2.le).θ
      = Real.exp (-(3 * φ)) :=
  (quarterly_survival hφ le_rfl).2.symm

/-- Galí (2015), Ex. 3.1(d), p. 89, with p. 55: the mean price duration in quarters implied
by the calibrated Calvo parameter, `1/(1 − θ) = 1/(1 − e^{−3φ})`. -/
theorem quarterlyCalvo_mean_duration {φ : ℝ} (hφ : 0 < φ) :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb
      (quarterlyCalvo (monthlyFreq φ) (monthlyFreq_mem hφ).1 (monthlyFreq_mem hφ).2.le).θ k
      = 1 / (1 - Real.exp (-(3 * φ))) := by
  rw [CalvoParam.mean_duration, quarterlyCalvo_theta hφ]

end Gali.BasicNewKeynesianModel.Ex3_1

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.2: government purchases in the basic New Keynesian model

Galí (2015), Chapter 3, Exercise 3.2 (p. 89). The government buys `G(i)` of every good and
maximises the CES index `G = (∫ G(i)^{1−1/ε} di)^{ε/(ε−1)}` for given spending
`∫ P(i) G(i) di`; purchases are financed by lump-sum taxes.

Goods are indexed by a measure space `(Gd, μ)` (the book's `[0, 1]` is
`μ = volume.restrict (Set.Icc 0 1)`). The government's problem is the same CES expenditure
problem as the household's (App. 3.1, p. 83), so the CES machinery of
`BasicNewKeynesianModel.CES` (`priceIndex`, `cesAgg`, `demand`, `cesAgg_eq_iff_of_spend`, ...)
applies verbatim to the government's purchases.

## Main results

* (a) `govt_index_le`, `govt_index_eq_iff` (from `CES.cesAgg_le_of_spend`,
  `CES.cesAgg_eq_iff_of_spend`): the government's optimal purchases are
  `G(i) = (P(i)/P)^{−ε} G` (both directions); `total_demand`: total demand for good `i` is
  `Y(i) = (P(i)/P)^{−ε}(C + G)`; `aggregate_output`: the output index is `Y = C + G`.
* (b) `hasFDerivAt_log_output`: `log Y = log(e^c + e^g)` has derivative `(1 − S_G, S_G)` at the
  steady state, i.e. `ŷ = (1 − S_G) ĉ + S_G ĝ` exactly to first order, with
  `S_G = G/Y` (`shareG_log`).
* (c) `log_realMC`, `hasFDerivAt_logMC`: average real marginal cost
  `mc = (C^σ N^φ)/((1 − α) A N^{−α})` with `N = (Y/A)^{1/(1−α)}` and `C = Y − G` has, in logs,
  derivative `m̂c = (σ/(1 − S_G) + (φ + α)/(1 − α)) ŷ − σ S_G/(1 − S_G) ĝ − (1 + φ)/(1 − α) â`;
  `mc_coeff_g_neg`: government purchases lower marginal cost at given output.
* (d) `dis_iff`: with `ŷ = (1 − S_G) ĉ + S_G ĝ`, the Euler equation is equivalent to the DIS
  `ŷ_t = E_t ŷ_{t+1} − ((1 − S_G)/σ)(i_t − E_t π_{t+1} − ρ) + S_G (ĝ_t − E_t ĝ_{t+1})`;
  `dis_ar1_term` gives the AR(1) form of the fiscal term.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_2

open MeasureTheory Gali.BasicNewKeynesianModel.CES

variable {Gd : Type*} [MeasurableSpace Gd]

variable {μ : Measure Gd} {ε : ℝ} {P : Gd → ℝ}

/-! ### (a) Total demand -/

/-- Galí (2015), Ex. 3.2(a), p. 89 (**the government's problem**, upper bound): purchases
`G(·) ≥ 0` with spending `∫ P(i) G(i) di = X` attain at most the index `X/P`. -/
theorem govt_index_le (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {g : Gd → ℝ} (hg0 : ∀ i, 0 ≤ g i) (hpg : Integrable (fun i => P i * g i) μ) {X : ℝ}
    (hX : ∫ i, P i * g i ∂μ = X) : cesAgg μ ε g ≤ X / priceIndex μ ε P :=
  cesAgg_le_of_spend hε hP hPi hpos hg0 hpg hX

/-- Galí (2015), Ex. 3.2(a), p. 89 (**the government's optimal purchases**): with spending
`X`, the government attains the maximal index `G = X/P` if and only if
`G(i) = (P(i)/P)^{−ε} G` almost everywhere. -/
theorem govt_index_eq_iff (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {g : Gd → ℝ} (hg0 : ∀ i, 0 ≤ g i) (hpg : Integrable (fun i => P i * g i) μ) {X : ℝ}
    (hX : ∫ i, P i * g i ∂μ = X) :
    cesAgg μ ε g = X / priceIndex μ ε P ↔ g =ᵐ[μ] demand μ ε P (X / priceIndex μ ε P) :=
  cesAgg_eq_iff_of_spend hε hP hPi hpos hg0 hpg hX

/-- Galí (2015), Ex. 3.2(a), p. 89: the demand schedule is linear in the aggregate,
`(P(i)/P)^{−ε} C + (P(i)/P)^{−ε} G = (P(i)/P)^{−ε} (C + G)`. -/
theorem demand_add (C Gv : ℝ) (i : Gd) :
    demand μ ε P C i + demand μ ε P Gv i = demand μ ε P (C + Gv) i := by
  unfold demand
  ring

/-- Galí (2015), Ex. 3.2(a), p. 89: **total demand facing firm `i`**. If households and the
government both buy on their optimal schedules, `C(i) = (P(i)/P)^{−ε} C` and
`G(i) = (P(i)/P)^{−ε} G` (a.e.), then `Y(i) = C(i) + G(i) = (P(i)/P)^{−ε}(C + G)` (a.e.). -/
theorem total_demand {c g : Gd → ℝ} {C Gv : ℝ} (hc : c =ᵐ[μ] demand μ ε P C)
    (hg : g =ᵐ[μ] demand μ ε P Gv) :
    (fun i => c i + g i) =ᵐ[μ] demand μ ε P (C + Gv) := by
  filter_upwards [hc, hg] with i hci hgi
  rw [hci, hgi, demand_add]

/-- Galí (2015), Ex. 3.2(a), p. 89: the government's optimal purchases. With spending
`∫ P(i) G(i) = X`, the government attains the index `X/P` exactly when its purchases are
`G(i) = (P(i)/P)^{−ε} X/P` a.e.; and then total demand for good `i` is
`(P(i)/P)^{−ε}(C + X/P)` given household demand `C(i) = (P(i)/P)^{−ε} C`. -/
theorem govt_total_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {g c : Gd → ℝ} (hg0 : ∀ i, 0 ≤ g i) (hpg : Integrable (fun i => P i * g i) μ) {X C : ℝ}
    (hX : ∫ i, P i * g i ∂μ = X) (hopt : cesAgg μ ε g = X / priceIndex μ ε P)
    (hc : c =ᵐ[μ] demand μ ε P C) :
    (fun i => c i + g i) =ᵐ[μ] demand μ ε P (C + cesAgg μ ε g) := by
  have hg := (govt_index_eq_iff hε hP hPi hpos hg0 hpg hX).1 hopt
  rw [hopt]
  exact total_demand hc hg

/-- Galí (2015), Ex. 3.2(a)–(b), p. 89: goods-market clearing. When output of every good
equals total demand, `Y(i) = (P(i)/P)^{−ε}(C + G)`, the CES output index is `Y = C + G`. -/
theorem aggregate_output (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {C Gv : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ Gv) {Y : Gd → ℝ}
    (hY : ∀ i, Y i = demand μ ε P (C + Gv) i) : cesAgg μ ε Y = C + Gv := by
  rw [show Y = demand μ ε P (C + Gv) from funext hY, cesAgg_demand hε hP hpos (by linarith)]

/-! ### (b) The log-linear goods-market condition -/

/-- Galí (2015), Ex. 3.2(b), p. 89: the government share `S_G = G/Y = e^g/(e^c + e^g)` as a
function of log consumption `c` and log purchases `g`. -/
noncomputable def shareG (c g : ℝ) : ℝ := Real.exp g / (Real.exp c + Real.exp g)

/-- Galí (2015), Ex. 3.2(b), p. 89: in levels, `S_G = G/(C + G) = G/Y`. -/
theorem shareG_log {C Gv : ℝ} (hC : 0 < C) (hG : 0 < Gv) :
    shareG (Real.log C) (Real.log Gv) = Gv / (C + Gv) := by
  rw [shareG, Real.exp_log hC, Real.exp_log hG]

/-- Galí (2015), Ex. 3.2(b), p. 89: `1 − S_G = C/Y`. -/
theorem one_sub_shareG (c g : ℝ) :
    1 - shareG c g = Real.exp c / (Real.exp c + Real.exp g) := by
  rw [shareG]
  have : Real.exp c + Real.exp g ≠ 0 := by positivity
  field_simp
  ring

/-- Galí (2015), Ex. 3.2(b), p. 89: `0 < S_G < 1`. -/
theorem shareG_mem (c g : ℝ) : 0 < shareG c g ∧ shareG c g < 1 := by
  have h1 := Real.exp_pos c
  have h2 := Real.exp_pos g
  refine ⟨by rw [shareG]; positivity, ?_⟩
  rw [shareG, div_lt_one (by positivity)]
  linarith

/-- Galí (2015), Ex. 3.2(b), p. 89: **log-linear goods-market clearing**. Log output
`y = log(e^c + e^g)` (from `Y = C + G`) has Fréchet derivative `(1 − S_G, S_G)` at any point
`(c, g)`; to first order around a steady state with share `S_G`,
`ŷ = (1 − S_G) ĉ + S_G ĝ`. -/
theorem hasFDerivAt_log_output (c g : ℝ) :
    HasFDerivAt (fun v : ℝ × ℝ => Real.log (Real.exp v.1 + Real.exp v.2))
      ((1 - shareG c g) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        shareG c g • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, g) := by
  have h1 := HasFDerivAt.exp (hasFDerivAt_fst (𝕜 := ℝ) (p := (c, g)))
  have h2 := HasFDerivAt.exp (hasFDerivAt_snd (𝕜 := ℝ) (p := (c, g)))
  have h := HasFDerivAt.log (HasFDerivAt.add h1 h2) (by simp only [Pi.add_apply]; positivity)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  rw [one_sub_shareG, shareG]
  simp only [smul_apply, add_apply, Pi.add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  have : Real.exp c + Real.exp g ≠ 0 := by positivity
  field_simp

/-! ### (c) Average real marginal cost -/

/-- Galí (2015), Ex. 3.2(c), p. 89 (with eq. (14), p. 59): aggregate employment
`N = (Y/A)^{1/(1−α)}` (price dispersion is of second order, App. 3.4). -/
noncomputable def empl (α Y A : ℝ) : ℝ := (Y / A) ^ (1 - α)⁻¹

/-- Galí (2015), Ex. 3.2(c), p. 89 (with p. 59–60): average real marginal cost, the real wage
`C^σ N^φ` (labour supply, with `C = Y − G`) over the marginal product of labour
`(1 − α) A N^{−α}`. -/
noncomputable def realMC (σ φ α Y Gv A : ℝ) : ℝ :=
  (Y - Gv) ^ σ * empl α Y A ^ φ / ((1 - α) * A * empl α Y A ^ (-α))

/-- Galí (2015), Ex. 3.2(c), p. 89: log real marginal cost in terms of log output `y`, log
purchases `g` and log technology `a`:
`σ log(e^y − e^g) + ((φ + α)/(1 − α))(y − a) − a − log(1 − α)`. -/
noncomputable def logMC (σ φ α y g a : ℝ) : ℝ :=
  σ * Real.log (Real.exp y - Real.exp g) + (φ + α) / (1 - α) * (y - a) - a - Real.log (1 - α)

/-- Galí (2015), Ex. 3.2(c), p. 89: the log of real marginal cost is `logMC` of the logs. -/
theorem log_realMC {σ φ α Y Gv A : ℝ} (hα : α < 1) (hG : 0 < Gv) (hYG : Gv < Y) (hA : 0 < A) :
    Real.log (realMC σ φ α Y Gv A) = logMC σ φ α (Real.log Y) (Real.log Gv) (Real.log A) := by
  have hY : 0 < Y := by linarith
  have hN : 0 < empl α Y A := Real.rpow_pos_of_pos (div_pos hY hA) _
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hlogN : Real.log (empl α Y A) = (Real.log Y - Real.log A) / (1 - α) := by
    rw [empl, Real.log_rpow (div_pos hY hA), Real.log_div hY.ne' hA.ne']
    field_simp
  rw [realMC, logMC, Real.exp_log hY, Real.exp_log hG,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by have : 0 < Y - Gv := by linarith
                     positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul h1α.ne' hA.ne',
    Real.log_rpow (by linarith), Real.log_rpow hN, Real.log_rpow hN, hlogN]
  field_simp
  ring

/-- Galí (2015), Ex. 3.2(c), p. 89: **log-linear average real marginal cost**. With
`S_G = e^g/e^y` (`= G/Y`), `logMC` has Fréchet derivative
`(σ/(1 − S_G) + (φ + α)/(1 − α), −σ S_G/(1 − S_G), −(1 + φ)/(1 − α))` in `(y, g, a)`, i.e.
`m̂c = (σ/(1 − S_G) + (φ + α)/(1 − α)) ŷ − (σ S_G/(1 − S_G)) ĝ − ((1 + φ)/(1 − α)) â`. -/
theorem hasFDerivAt_logMC {σ φ α y g a : ℝ} (hα : α < 1) (hgy : g < y) :
    HasFDerivAt (fun v : ℝ × ℝ × ℝ => logMC σ φ α v.1 v.2.1 v.2.2)
      ((σ / (1 - Real.exp g / Real.exp y) + (φ + α) / (1 - α)) •
          ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        (σ * (Real.exp g / Real.exp y) / (1 - Real.exp g / Real.exp y)) •
          (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
        ((1 + φ) / (1 - α)) •
          (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (y, g, a) := by
  have hey : Real.exp g < Real.exp y := Real.exp_lt_exp.mpr hgy
  have hne : Real.exp y - Real.exp g ≠ 0 := by linarith
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  have hy := hasFDerivAt_fst (𝕜 := ℝ) (p := (y, g, a))
  have hg := HasFDerivAt.fst (hasFDerivAt_snd (𝕜 := ℝ) (p := (y, g, a)))
  have ha := HasFDerivAt.snd (hasFDerivAt_snd (𝕜 := ℝ) (p := (y, g, a)))
  have hlog := HasFDerivAt.log (HasFDerivAt.sub (HasFDerivAt.exp hy) (HasFDerivAt.exp hg)) hne
  have h := HasFDerivAt.sub_const (Real.log (1 - α)) (HasFDerivAt.sub (HasFDerivAt.add
    (HasFDerivAt.const_mul hlog σ) (HasFDerivAt.const_mul (HasFDerivAt.sub hy ha)
      ((φ + α) / (1 - α)))) ha)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [sub_apply, add_apply, smul_apply, Pi.sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_comp,
    Function.comp_apply, smul_eq_mul]
  have hey0 : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  have hd : 1 - Real.exp g / Real.exp y = (Real.exp y - Real.exp g) / Real.exp y := by
    field_simp
  rw [hd]
  field_simp
  ring

/-- Galí (2015), Ex. 3.2(c), p. 89 (intuition): at given output and technology, government
purchases **lower** real marginal cost — they crowd out consumption, which raises the
marginal utility of consumption and lowers the real wage required for given hours:
the coefficient on `ĝ` is `−σ S_G/(1 − S_G) < 0`. -/
theorem mc_coeff_g_neg {σ SG : ℝ} (hσ : 0 < σ) (hS0 : 0 < SG) (hS1 : SG < 1) :
    -(σ * SG / (1 - SG)) < 0 := by
  have : 0 < σ * SG / (1 - SG) := div_pos (mul_pos hσ hS0) (by linarith)
  linarith

/-- Galí (2015), Ex. 3.2(c), p. 89: the elasticity of marginal cost with respect to output
rises with the government share: `σ/(1 − S_G) ≥ σ` for `0 ≤ S_G < 1`, `σ ≥ 0`. -/
theorem mc_coeff_y_ge {σ SG : ℝ} (hσ : 0 ≤ σ) (hS0 : 0 ≤ SG) (hS1 : SG < 1) :
    σ ≤ σ / (1 - SG) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-! ### (d) The dynamic IS equation with government purchases -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (3), p. 54: the log-linear Euler equation in deviations,
`ĉ_t = E_t ĉ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)`. -/
def Euler (σ ρ : ℝ) (c i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)

/-- Galí (2015), Ex. 3.2(d), p. 89: the dynamic IS equation with government purchases,
`ŷ_t = E_t ŷ_{t+1} − ((1 − S_G)/σ)(i_t − E_t π_{t+1} − ρ) + S_G (ĝ_t − E_t ĝ_{t+1})`. -/
def DISG (σ ρ SG : ℝ) (y g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - ((1 - SG) / σ) • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ) +
    SG • (g t - 𝔼.E t (g (t + 1)))

/-- Galí (2015), Ex. 3.2(d), p. 89: **the DIS with government purchases**. Given the
log-linear goods-market condition `ŷ = (1 − S_G) ĉ + S_G ĝ` (part (b)) and `S_G < 1`, the
Euler equation holds if and only if the modified DIS holds: the interest elasticity of output
falls to `(1 − S_G)/σ` and expected changes in purchases shift the relation. -/
theorem dis_iff {σ ρ SG : ℝ} (hS : SG ≠ 1) {y c g i infl : ℕ → Ω → ℝ}
    (hgm : ∀ t, y t = (1 - SG) • c t + SG • g t) :
    Euler 𝔼 σ ρ c i infl ↔ DISG 𝔼 σ ρ SG y g i infl := by
  have hE : ∀ t, 𝔼.E t (y (t + 1)) = (1 - SG) • 𝔼.E t (c (t + 1)) + SG • 𝔼.E t (g (t + 1)) :=
    fun t => by rw [hgm (t + 1), map_add, map_smul, map_smul]
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h3 := congrFun (hE t) ω
    have h4 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h3 h4 ⊢
    rw [div_eq_mul_inv]
    linear_combination h1 - h3 + (1 - SG) * h4
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h3 := congrFun (hE t) ω
    have h5 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h3 h5 ⊢
    rw [div_eq_mul_inv] at h5
    have hk : (1 - SG) * (c t ω - (𝔼.E t (c (t + 1)) ω -
        σ⁻¹ * (i t ω - 𝔼.E t (infl (t + 1)) ω - ρ))) = 0 := by
      linear_combination -h1 + h3 + h5
    rcases mul_eq_zero.1 hk with h0 | h0
    · exact absurd (by linarith : SG = 1) hS
    · linarith

/-- Galí (2015), Ex. 3.2(d), p. 89: with AR(1) purchases, `E_t ĝ_{t+1} = ρ_g ĝ_t`, the fiscal
term of the DIS is `S_G (1 − ρ_g) ĝ_t`: a persistent rise in purchases raises output demand
on impact relative to expected future output. -/
theorem dis_ar1_term {SG ρg : ℝ} {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (t : ℕ) :
    SG • (g t - 𝔼.E t (g (t + 1))) = (SG * (1 - ρg)) • g t := by
  rw [hg.2 t]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

end Gali.BasicNewKeynesianModel.Ex3_2

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.3: government purchases and sticky prices

Galí (2015), Chapter 3, Exercise 3.3 (pp. 89–91). The government buys a fraction `τ_t` of the
output of every good, `G_t(i) = τ_t Y_t(i)`, financed by lump-sum taxes; `g_t ≡ −log(1 − τ_t)`.
Households: Euler equation `c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)` and labour supply
`w_t − p_t = σ c_t + φ n_t`; technology `y_t = n_t`; the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`;
under flexible prices firms set a constant (log) markup `μ` over marginal cost.

## Main results

* (a) `cesAgg_smul`, `goods_market_exact`: `C(i) = (1 − τ) Y(i)` gives `C = (1 − τ) Y` for the CES
  indices, hence `y_t = c_t + g_t` **exactly**.
* (b) `natural_output`, `natural_output_iff`: `y^n = (σ g − μ)/(σ + φ)`;
  `natOutput_multiplier_mem`, `natCons_multiplier_neg`: under flexible prices a fiscal expansion
  raises output by a fraction `σ/(σ + φ) ∈ (0, 1)` of `g` and lowers consumption: the negative
  wealth effect raises labour supply at the unchanged real wage `−μ`.
* (c) `euler_iff_dis_output`, `dis_output_iff_gap`, `euler_iff_dis_gap`: the DIS
  `ỹ_t = E_t ỹ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r^n_t)` with
  `r^n_t = ρ + σφ/(σ + φ)(g_t − E_t g_{t+1})`; `natRate_eq_euler` (the rate that supports the
  natural allocation); `natRate_ar1`: `r^n_t = ρ + σφ(1 − ρ_g)/(σ + φ) g_t`.
* (d) Under `i_t = ρ + φ_π π_t`: `schurStable_iff` (determinacy iff `φ_π > 1`),
  `msv_equilibrium` (existence), `equilibrium_iff_msv` (the MSV solution
  `ỹ_t = (1 − βρ_g) Λ_g c_g g_t`, `π_t = κ Λ_g c_g g_t` is the unique bounded equilibrium),
  `equilibrium_not_unique` (indeterminacy for `φ_π ≤ 1`), and the responses
  `msv_responses_pos`, `output_multiplier_bounds`: gap, inflation and the nominal rate rise,
  and the output multiplier lies strictly between its flexible-price value `σ/(σ + φ)` and one.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_3

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-! ### (a) Goods-market clearing -/

namespace Goods

variable {Gd : Type*} [MeasurableSpace Gd] {μ : Measure Gd} {ε : ℝ}

/-- Galí (2015), Ex. 3.3(a), p. 90: the CES index is homogeneous of degree one,
`(∫ (k c(i))^r)^{1/r} = k (∫ c(i)^r)^{1/r}` for `k ≥ 0`. -/
theorem cesAgg_smul (hε : 1 < ε) {k : ℝ} (hk : 0 ≤ k) {c : Gd → ℝ} (hc : ∀ i, 0 ≤ c i) :
    cesAgg μ ε (fun i => k * c i) = k * cesAgg μ ε c := by
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  unfold cesAgg
  simp_rw [Real.mul_rpow hk (hc _)]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hk _)
    (integral_nonneg fun i => Real.rpow_nonneg (hc i) _), Real.rpow_rpow_inv hk hr]

/-- Galí (2015), Ex. 3.3(a), p. 90: **exact goods-market clearing**. If the government buys
`G(i) = τ Y(i)` of every good and households consume the rest, `C(i) = Y(i) − τ Y(i)`, then
the indices satisfy `C = (1 − τ) Y` and `G = τ Y`; so with `g ≡ −log(1 − τ)`,
`y = c + g` holds exactly (not only to first order). -/
theorem goods_market_exact (hε : 1 < ε) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {Y : Gd → ℝ}
    (hY : ∀ i, 0 ≤ Y i) (hYpos : 0 < cesAgg μ ε Y) :
    cesAgg μ ε (fun i => Y i - τ * Y i) = (1 - τ) * cesAgg μ ε Y ∧
      cesAgg μ ε (fun i => τ * Y i) = τ * cesAgg μ ε Y ∧
      Real.log (cesAgg μ ε Y) =
        Real.log (cesAgg μ ε (fun i => Y i - τ * Y i)) + -Real.log (1 - τ) := by
  have hC : cesAgg μ ε (fun i => Y i - τ * Y i) = (1 - τ) * cesAgg μ ε Y := by
    rw [← cesAgg_smul hε (by linarith) hY]
    congr 1
    funext i
    ring
  refine ⟨hC, cesAgg_smul hε hτ0 hY, ?_⟩
  rw [hC, Real.log_mul (by linarith) hYpos.ne']
  ring

end Goods

/-! ### (b) The natural level of output -/

/-- Galí (2015), Ex. 3.3(b), p. 90: **natural output**. Under flexible prices the real wage
equals the inverse markup, `w − p = −μ` (price = markup over nominal marginal cost `w`, since
`y = n`); with labour supply `w − p = σ c + φ n`, `y = n` and `y = c + g`, output is
`y^n = (σ g − μ)/(σ + φ)`. -/
theorem natural_output {σ φ μ y c n g wp : ℝ} (hσφ : σ + φ ≠ 0) (hmark : wp = -μ)
    (hls : wp = σ * c + φ * n) (htech : y = n) (hgm : y = c + g) :
    y = (σ * g - μ) / (σ + φ) := by
  rw [eq_div_iff hσφ]
  subst htech
  have hc : c = y - g := by linarith
  subst hc
  linarith

/-- Galí (2015), Ex. 3.3(b), p. 90: the flexible-price allocation is unique and given by
`y = n = (σ g − μ)/(σ + φ)`, `c = y − g` and `w − p = −μ`: the four conditions hold if and only
if the allocation is this one. -/
theorem natural_output_iff {σ φ μ y c n g wp : ℝ} (hσφ : σ + φ ≠ 0) :
    (wp = -μ ∧ wp = σ * c + φ * n ∧ y = n ∧ y = c + g) ↔
      (y = (σ * g - μ) / (σ + φ) ∧ n = y ∧ c = y - g ∧ wp = -μ) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨natural_output hσφ h1 h2 h3 h4, h3.symm, by linarith, h1⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h4, ?_, h2.symm, by linarith⟩
    rw [h4, h3, h2, h1]
    field_simp
    ring

/-- Galí (2015), Ex. 3.3(b), p. 90: natural consumption `c^n = y^n − g = −(φ g + μ)/(σ + φ)`. -/
theorem natural_consumption {σ φ μ g : ℝ} (hσφ : σ + φ ≠ 0) :
    (σ * g - μ) / (σ + φ) - g = -(φ * g + μ) / (σ + φ) := by
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(b), p. 90 (mechanism): for `σ, φ > 0` the flexible-price output
multiplier `σ/(σ + φ)` lies strictly between zero and one. -/
theorem natOutput_multiplier_mem {σ φ : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) :
    0 < σ / (σ + φ) ∧ σ / (σ + φ) < 1 := by
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- Galí (2015), Ex. 3.3(b), p. 90 (mechanism): consumption falls one-for-`φ/(σ + φ)` with
purchases. Higher purchases make households poorer, the marginal utility of consumption
rises, and labour supply shifts out at the unchanged real wage, so employment and output
rise while consumption is crowded out. -/
theorem natCons_multiplier_neg {σ φ : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) :
    σ / (σ + φ) - 1 = -(φ / (σ + φ)) ∧ -(φ / (σ + φ)) < 0 := by
  have h : σ + φ ≠ 0 := by positivity
  refine ⟨by field_simp; ring, ?_⟩
  have : 0 < φ / (σ + φ) := by positivity
  linarith

/-! ### (c) The dynamic IS equation and the natural rate -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Ex. 3.3, p. 89: the log-linear Euler equation
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)`. -/
def Euler (σ ρ : ℝ) (c i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)

/-- Galí (2015), Ex. 3.3(c), p. 90: the DIS in output,
`y_t = E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ) + (g_t − E_t g_{t+1})`. -/
def DISOutput (σ ρ : ℝ) (y g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ) +
    (g t - 𝔼.E t (g (t + 1)))

/-- Galí (2015), Ex. 3.3(b), p. 90: the natural output process `y^n_t = (σ g_t − μ)/(σ + φ)`. -/
noncomputable def natOutput (σ φ μ : ℝ) (g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σ + φ)⁻¹ • (σ • g t - fun _ => μ)

/-- Galí (2015), Ex. 3.3(c), p. 90: the natural rate
`r^n_t = ρ + (σφ/(σ + φ))(g_t − E_t g_{t+1})`. -/
noncomputable def natRate (σ φ ρ : ℝ) (g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => ρ) + (σ * φ / (σ + φ)) • (g t - 𝔼.E t (g (t + 1)))

/-- Galí (2015), Ex. 3.3(c), p. 90: the DIS in the output gap,
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r^n_t)`. -/
def DISGap (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), Ex. 3.3(c), p. 90: with `y_t = c_t + g_t`, the Euler equation holds if and
only if the output DIS holds. -/
theorem euler_iff_dis_output {σ ρ : ℝ} {y c g i infl : ℕ → Ω → ℝ}
    (hgm : ∀ t, y t = c t + g t) :
    Euler 𝔼 σ ρ c i infl ↔ DISOutput 𝔼 σ ρ y g i infl := by
  have hE : ∀ t, 𝔼.E t (y (t + 1)) = 𝔼.E t (c (t + 1)) + 𝔼.E t (g (t + 1)) :=
    fun t => by rw [hgm (t + 1), map_add]
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination h1 - h2 + h3
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination -h1 + h2 + h3

/-- Galí (2015), Ex. 3.3(c), p. 90: with `ỹ = y − y^n`, the output DIS holds if and only if
the gap DIS holds with the natural rate `r^n`. -/
theorem dis_output_iff_gap {σ φ μ ρ : ℝ} (hσ : σ ≠ 0) (hσφ : σ + φ ≠ 0)
    {y ygap g i infl : ℕ → Ω → ℝ} (hgap : ∀ t, ygap t = y t - natOutput σ φ μ g t) :
    DISOutput 𝔼 σ ρ y g i infl ↔ DISGap 𝔼 σ ygap i infl (natRate 𝔼 σ φ ρ g) := by
  have hE : ∀ t, 𝔼.E t (ygap (t + 1))
      = 𝔼.E t (y (t + 1)) - (σ + φ)⁻¹ • (σ • 𝔼.E t (g (t + 1)) - fun _ => μ) :=
    fun t => by rw [hgap (t + 1), natOutput, map_sub, map_smul, map_sub, map_smul, 𝔼.const]
  have hK : σ⁻¹ * (σ * φ / (σ + φ)) + (σ + φ)⁻¹ * σ = 1 := by
    field_simp
    ring
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (hgap t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [natOutput, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination h1 - h2 + h3 - (g t ω - 𝔼.E t (g (t + 1)) ω) * hK
  · intro h t
    funext ω
    have h1 := congrFun (hgap t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [natOutput, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination -h1 + h2 + h3 + (g t ω - 𝔼.E t (g (t + 1)) ω) * hK

/-- Galí (2015), Ex. 3.3(c), p. 90: **the DIS with government purchases**. Given `y = c + g`
and `ỹ = y − y^n`, the Euler equation holds if and only if
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r^n_t)`,
`r^n_t = ρ + σφ/(σ + φ) (g_t − E_t g_{t+1})`. -/
theorem euler_iff_dis_gap {σ φ μ ρ : ℝ} (hσ : σ ≠ 0) (hσφ : σ + φ ≠ 0)
    {y c ygap g i infl : ℕ → Ω → ℝ} (hgm : ∀ t, y t = c t + g t)
    (hgap : ∀ t, ygap t = y t - natOutput σ φ μ g t) :
    Euler 𝔼 σ ρ c i infl ↔ DISGap 𝔼 σ ygap i infl (natRate 𝔼 σ φ ρ g) :=
  (euler_iff_dis_output 𝔼 hgm).trans (dis_output_iff_gap 𝔼 hσ hσφ hgap)

/-- Galí (2015), Ex. 3.3(c), p. 90: the natural rate is the real rate that supports the
natural allocation: `r^n_t = ρ + σ (E_t c^n_{t+1} − c^n_t)` with `c^n = y^n − g`. -/
theorem natRate_eq_euler {σ φ μ ρ : ℝ} (hσφ : σ + φ ≠ 0) (g : ℕ → Ω → ℝ) (t : ℕ) :
    natRate 𝔼 σ φ ρ g t = (fun _ => ρ) + σ • (𝔼.E t (natOutput σ φ μ g (t + 1) - g (t + 1)) -
      (natOutput σ φ μ g t - g t)) := by
  funext ω
  simp only [natRate, natOutput, map_sub, map_smul, 𝔼.const, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(c), p. 90: with AR(1) purchases (`E_t g_{t+1} = ρ_g g_t`) the natural
rate is `r^n_t = ρ + σφ(1 − ρ_g)/(σ + φ) g_t`. -/
theorem natRate_ar1 {σ φ ρ ρg : ℝ} {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (t : ℕ) :
    natRate 𝔼 σ φ ρ g t = (fun _ => ρ) + (σ * φ * (1 - ρg) / (σ + φ)) • g t := by
  funext ω
  simp only [natRate, hg.2 t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### (d) Equilibrium under `i_t = ρ + φ_π π_t` -/

/-- Galí (2015), Ex. 3.3, p. 90: the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), Ex. 3.3(d), p. 91: the rule `i_t = ρ + φ_π π_t`. -/
def Rule (ρ φπ : ℝ) (i infl : ℕ → Ω → ℝ) : Prop := ∀ t, i t = (fun _ => ρ) + φπ • infl t

/-- Galí (2015), Ex. 3.3(d), p. 91: an equilibrium: NKPC, gap DIS with natural rate `rn`, rule. -/
def Equilibrium (β σ κ ρ φπ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DISGap 𝔼 σ ygap i infl rn ∧ Rule ρ φπ i infl

/-- Galí (2015), Ex. 3.3(d), p. 91: the system matrix with the rate substituted out,
`A = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [σκ, κ + βσ]]`. -/
noncomputable def A (β σ κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φπ), (1 - β * φπ) / (σ + κ * φπ);
    σ * κ / (σ + κ * φπ), (κ + β * σ) / (σ + κ * φπ)]

/-- Galí (2015), Ex. 3.3(d), p. 91: the stacked vector `(ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), Ex. 3.3(d), p. 91: the forcing term `(σ + κφ_π)⁻¹ (1, κ) u_t`. -/
noncomputable def forcing (σ κ φπ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(σ + κ * φπ)⁻¹ • u t, (κ / (σ + κ * φπ)) • u t]

/-- Galí (2015), Ex. 3.3(d), p. 91: with the rule substituted, the NKPC and the gap DIS hold
iff `(ỹ, π)` solves `x_t = A E_t x_{t+1} + B u_t` with `u_t = r^n_t − ρ`. -/
theorem equilibrium_iff_solves {β σ κ ρ φπ : ℝ} (hσ : σ ≠ 0) (hS : σ + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hrule : Rule ρ φπ i infl) :
    Equilibrium 𝔼 β σ κ ρ φπ rn ygap infl i ↔
      𝔼.Solves (A β σ κ φπ) (forcing σ κ φπ (fun t => rn t - fun _ => ρ)) (stack ygap infl) := by
  have hσσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hσσ' : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  have hSS : (σ + κ * φπ) * (σ + κ * φπ)⁻¹ = 1 := mul_inv_cancel₀ hS
  have hSS' : (σ + κ * φπ)⁻¹ * (σ + κ * φπ) = 1 := inv_mul_cancel₀ hS
  constructor
  · rintro ⟨hp, hd, -⟩ t j
    funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 r
    rw [r] at e1
    have hs : (σ + κ * φπ) * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω +
        (1 - β * φπ) * 𝔼.E t (infl (t + 1)) ω + (rn t ω - ρ) := by
      linear_combination σ * e1 - φπ * e2 -
        (ρ + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hσσ
    have hs2 : (σ + κ * φπ) * infl t ω = σ * κ * 𝔼.E t (ygap (t + 1)) ω +
        (κ + β * σ) * 𝔼.E t (infl (t + 1)) ω + κ * (rn t ω - ρ) := by
      linear_combination (σ + κ * φπ) * e2 + κ * hs
    fin_cases j
    · simp only [stack, forcing, A, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (σ + κ * φπ)⁻¹ * hs - ygap t ω * hSS'
    · simp only [stack, forcing, A, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (σ + κ * φπ)⁻¹ * hs2 - infl t ω * hSS'
  · intro h
    have hdis : ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) ∧
        infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t := by
      intro t
      have h0 := h t 0
      have h1 := h t 1
      simp only [stack, forcing, A, Fin.isValue, Matrix.cons_val_zero, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
      have key : ∀ ω, (σ + κ * φπ) * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω +
            (1 - β * φπ) * 𝔼.E t (infl (t + 1)) ω + (rn t ω - ρ) ∧
          (σ + κ * φπ) * infl t ω = σ * κ * 𝔼.E t (ygap (t + 1)) ω +
            (κ + β * σ) * 𝔼.E t (infl (t + 1)) ω + κ * (rn t ω - ρ) := by
        intro ω
        have e0 := congrFun h0 ω
        have e1 := congrFun h1 ω
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
        constructor
        · linear_combination (σ + κ * φπ) * e0 + (σ * 𝔼.E t (ygap (t + 1)) ω +
            (1 - β * φπ) * 𝔼.E t (infl (t + 1)) ω + (rn t ω - ρ)) * hSS
        · linear_combination (σ + κ * φπ) * e1 + (σ * κ * 𝔼.E t (ygap (t + 1)) ω +
            (κ + β * σ) * 𝔼.E t (infl (t + 1)) ω + κ * (rn t ω - ρ)) * hSS
      have hn : ∀ ω, infl t ω = β * 𝔼.E t (infl (t + 1)) ω + κ * ygap t ω := by
        intro ω
        apply mul_left_cancel₀ hS
        linear_combination (key ω).2 - κ * (key ω).1
      refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
      · have r := congrFun (hrule t) ω
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
        rw [r]
        have hsig : σ * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω -
            (ρ + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) := by
          linear_combination (key ω).1 + φπ * hn ω
        linear_combination σ⁻¹ * hsig - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hσσ'
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact hn ω
    exact ⟨fun t => (hdis t).2, fun t => (hdis t).1, hrule⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: `tr A = (σ(1 + β) + κ)/(σ + κφ_π)`. -/
theorem tr2_A {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    tr2 (A β σ κ φπ) = (σ * (1 + β) + κ) / (σ + κ * φπ) := by
  simp only [tr2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(d), p. 91: `det A = σβ/(σ + κφ_π)`. -/
theorem det2_A {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    det2 (A β σ κ φπ) = σ * β / (σ + κ * φπ) := by
  simp only [det2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(d), p. 91 (the Taylor principle): for `σ, κ > 0`, `0 < β < 1`,
`φ_π ≥ 0`, both eigenvalues of `A` lie inside the unit circle iff `φ_π > 1`. -/
theorem schurStable_iff {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    SchurStable (tr2 (A β σ κ φπ)) (det2 (A β σ κ φπ)) ↔ 1 < φπ := by
  have hS : 0 < σ + κ * φπ := by positivity
  rw [tr2_A hS.ne', det2_A hS.ne']
  have hD0 : 0 < σ * β / (σ + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ) / (σ + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0, one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  constructor
  · rintro ⟨-, h⟩; nlinarith
  · intro h; exact ⟨hD1, by nlinarith⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: determinacy (at most one bounded adapted solution for
every forcing) holds iff `φ_π > 1`. -/
theorem determinate_iff [Nonempty Ω] {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) : 𝔼.Determinate (A β σ κ φπ) ↔ 1 < φπ :=
  (𝔼.determinate_iff _).trans (schurStable_iff hσ hκ hβ0 hβ1 hφπ)

/-- Two bounded processes stack to a bounded vector process. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), Ex. 3.3(c)–(d), p. 90: the composite coefficient
`c_g = σφ(1 − ρ_g)/(σ + φ)` of the natural-rate deviation `r^n_t − ρ = c_g g_t`. -/
noncomputable def cg (σ φ ρg : ℝ) : ℝ := σ * φ * (1 - ρg) / (σ + φ)

/-- Galí (2015), Ex. 3.3(d), p. 91: `Λ_g = 1/((1 − βρ_g) σ (1 − ρ_g) + κ (φ_π − ρ_g))`. -/
noncomputable def lam (β σ κ φπ ρg : ℝ) : ℝ := 1 / ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg))

/-- Galí (2015), Ex. 3.3(d), p. 91: `Λ_g > 0` for `φ_π > 1`, `ρ_g < 1`. -/
theorem lam_pos {β σ κ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 1 < φπ) (hρ1 : ρg < 1) : 0 < lam β σ κ φπ ρg := by
  have h1 : 0 < 1 - β * ρg := by nlinarith
  have h2 : 0 < (1 - β * ρg) * σ * (1 - ρg) := by
    have : 0 < 1 - ρg := by linarith
    positivity
  have h3 : 0 < κ * (φπ - ρg) := mul_pos hκ (by linarith)
  exact one_div_pos.mpr (by linarith)

/-- Galí (2015), Ex. 3.3(d), p. 91: the MSV output-gap coefficient `(1 − βρ_g) Λ_g c_g`. -/
noncomputable def psiY (β σ κ φ φπ ρg : ℝ) : ℝ := (1 - β * ρg) * lam β σ κ φπ ρg * cg σ φ ρg

/-- Galí (2015), Ex. 3.3(d), p. 91: the MSV inflation coefficient `κ Λ_g c_g`. -/
noncomputable def psiPi (β σ κ φ φπ ρg : ℝ) : ℝ := κ * lam β σ κ φπ ρg * cg σ φ ρg

/-- A scalar multiple of an AR(1) process is AR(1) with the same persistence. -/
theorem isAR1_smul {ρg : ℝ} {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (c : ℝ) :
    𝔼.IsAR1 ρg (fun t => c • g t) :=
  ⟨fun t => by simp only [map_smul, hg.1 t], fun t => by
    simp only [map_smul, hg.2 t, smul_comm c ρg]⟩

/-- A scalar multiple of a bounded process is bounded. -/
theorem bounded_smul {g : ℕ → Ω → ℝ} (hg : BoundedProc g) (c : ℝ) :
    BoundedProc (fun t => c • g t) := by
  obtain ⟨M, hM⟩ := hg
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: **existence** — with AR(1) purchases, the MSV processes
`ỹ_t = (1 − βρ_g) Λ_g c_g g_t`, `π_t = κ Λ_g c_g g_t`, `i_t = ρ + φ_π π_t` form an
equilibrium (the denominator of `Λ_g` being nonzero). -/
theorem msv_equilibrium {β σ κ φ ρ φπ ρg : ℝ} (hσ : σ ≠ 0) (hσφ : σ + φ ≠ 0)
    (hden : (1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg) ≠ 0) {g : ℕ → Ω → ℝ}
    (hg : 𝔼.IsAR1 ρg g) :
    Equilibrium 𝔼 β σ κ ρ φπ (natRate 𝔼 σ φ ρ g) (fun t => psiY β σ κ φ φπ ρg • g t)
      (fun t => psiPi β σ κ φ φπ ρg • g t)
      (fun t => (fun _ => ρ) + φπ • (psiPi β σ κ φ φπ ρg • g t)) := by
  have c1 : psiPi β σ κ φ φπ ρg = β * (psiPi β σ κ φ φπ ρg * ρg) + κ * psiY β σ κ φ φπ ρg := by
    unfold psiPi psiY
    ring
  have c2 : psiY β σ κ φ φπ ρg = psiY β σ κ φ φπ ρg * ρg - σ⁻¹ *
      (φπ * psiPi β σ κ φ φπ ρg - psiPi β σ κ φ φπ ρg * ρg - σ * φ * (1 - ρg) / (σ + φ)) := by
    unfold psiY psiPi lam cg
    field_simp
    ring
  refine ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩
  · funext ω
    simp only [map_smul, hg.2 t, smul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination g t ω * c1
  · funext ω
    rw [natRate_ar1 𝔼 hg t]
    simp only [map_smul, hg.2 t, smul_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination g t ω * c2

/-- Galí (2015), Ex. 3.3(d), p. 91: **the unique bounded equilibrium**. For `σ, κ, φ > 0`,
`0 < β < 1`, `φ_π > 1` and bounded AR(1) purchases with `ρ_g < 1` (the book has
`ρ_g ∈ [0, 1)`), a triple `(ỹ, π, i)` with bounded adapted `ỹ`, `π` is an equilibrium iff
it is the MSV triple. -/
theorem equilibrium_iff_msv {β σ κ φ ρ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hρ1 : ρg < 1)
    {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (hgb : BoundedProc g) {ygap infl i : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ (natRate 𝔼 σ φ ρ g) ygap infl i ↔
      ygap = (fun t => psiY β σ κ φ φπ ρg • g t) ∧
      infl = (fun t => psiPi β σ κ φ φπ ρg • g t) ∧
      i = fun t => (fun _ => ρ) + φπ • (psiPi β σ κ φ φπ ρg • g t) := by
  have hS : σ + κ * φπ ≠ 0 := by nlinarith
  have hσφ : σ + φ ≠ 0 := by linarith
  have hden : (1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg) ≠ 0 := by
    have := lam_pos hσ hκ hβ0 hβ1 hφπ hρ1
    unfold lam at this
    exact (one_div_pos.mp this).ne'
  have hmsv := msv_equilibrium 𝔼 (ρ := ρ) hσ.ne' hσφ hden hg
  constructor
  · intro he
    have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
    have hy := (equilibrium_iff_solves 𝔼 hσ.ne' hS hmsv.2.2).mp hmsv
    have heq := 𝔼.system_unique ((schurStable_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφπ) hx hy
      (adaptedVec_stack 𝔼 ha hb)
      (adaptedVec_stack 𝔼 (isAR1_smul 𝔼 hg _).1 (isAR1_smul 𝔼 hg _).1)
      (boundedVec_stack hba hbb) (boundedVec_stack (bounded_smul hgb _) (bounded_smul hgb _))
    have h1 : ygap = fun t => psiY β σ κ φ φπ ρg • g t :=
      funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : infl = fun t => psiPi β σ κ φ φπ ρg • g t :=
      funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, funext fun t => ?_⟩
    rw [he.2.2 t, h2]
  · rintro ⟨rfl, rfl, rfl⟩
    exact hmsv

/-- Galí (2015), Ex. 3.3(d), p. 91: for `φ_π ≤ 1` the equilibrium is indeterminate: next to
any bounded adapted equilibrium there is a second one with a different gap or inflation. -/
theorem equilibrium_not_unique [Nonempty Ω] {β σ κ ρ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ0 : 0 ≤ φπ) (hφπ : φπ ≤ 1) {rn ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φπ rn ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β σ κ ρ φπ rn ygap' infl' i' ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : σ + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (A β σ κ φπ)) (det2 (A β σ κ φπ)) := by
    rw [schurStable_iff hσ hκ hβ0 hβ1 hφπ0]; linarith
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hrule' : Rule ρ φπ (fun t => (fun _ => ρ) + φπ • infl' t) infl' := fun t => rfl
  refine ⟨ygap', infl', _, (equilibrium_iff_solves 𝔼 hσ.ne' hS hrule').mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-- Galí (2015), Ex. 3.3(d), p. 91: **the response to a fiscal expansion**. For
`σ, κ, φ > 0`, `0 < β < 1`, `φ_π > 1`, `ρ_g < 1`: the output gap, inflation and the
nominal rate all rise with `g` (`ψ_y, ψ_π, φ_π ψ_π > 0`), as does the real rate
`i_t − E_t π_{t+1}`, whose coefficient is `(φ_π − ρ_g) ψ_π > 0`. -/
theorem msv_responses_pos {β σ κ φ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hρ1 : ρg < 1) :
    0 < psiY β σ κ φ φπ ρg ∧ 0 < psiPi β σ κ φ φπ ρg ∧ 0 < φπ * psiPi β σ κ φ φπ ρg ∧
      0 < (φπ - ρg) * psiPi β σ κ φ φπ ρg := by
  have hL := lam_pos hσ hκ hβ0 hβ1 hφπ hρ1
  have hc : 0 < cg σ φ ρg := by
    unfold cg
    have : 0 < 1 - ρg := by linarith
    positivity
  have h1 : 0 < 1 - β * ρg := by nlinarith
  have hP : 0 < psiPi β σ κ φ φπ ρg := by unfold psiPi; positivity
  refine ⟨by unfold psiY; positivity, hP, by positivity, mul_pos (by linarith) hP⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: **the output multiplier under sticky prices**. Output is
`y_t = y^n_t + ỹ_t`, with multiplier `σ/(σ + φ) + ψ_y`; it strictly exceeds the flexible-price
multiplier `σ/(σ + φ)` and is strictly below one, so consumption is still crowded out
(`y − g` falls), but by less than under flexible prices. -/
theorem output_multiplier_bounds {β σ κ φ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hρ1 : ρg < 1) :
    σ / (σ + φ) < σ / (σ + φ) + psiY β σ κ φ φπ ρg ∧
      σ / (σ + φ) + psiY β σ κ φ φπ ρg < 1 := by
  refine ⟨by linarith [(msv_responses_pos hσ hκ hφ hβ0 hβ1 hφπ hρ1).1], ?_⟩
  have h1 : 0 < 1 - β * ρg := by nlinarith
  have h2 : 0 < 1 - ρg := by linarith
  have hk : 0 < κ * (φπ - ρg) := mul_pos hκ (by linarith)
  have hd : 0 < (1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg) := by positivity
  have hσφ : 0 < σ + φ := by linarith
  unfold psiY lam cg
  rw [show σ / (σ + φ) + (1 - β * ρg) * (1 / ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg))) *
      (σ * φ * (1 - ρg) / (σ + φ)) = (σ * ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg)) +
        φ * ((1 - β * ρg) * σ * (1 - ρg))) / ((σ + φ) *
          ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg))) by field_simp]
  rw [div_lt_one (by positivity)]
  nlinarith

end Gali.BasicNewKeynesianModel.Ex3_3

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.4: indexation and the New Keynesian Phillips curve

Galí (2015), Chapter 3, Exercise 3.4 (pp. 91–92). Between reoptimisations a firm indexes its
price, `P_{t+k|t} = P_{t+k−1|t} Π_{t+k−1}^ω Π^{1−ω}` (`ω ∈ [0, 1]`, `Π` steady-state gross
inflation), so a price set at `t` is `P*_t X_{t,k}` at `t + k`, with
`X_{t,k} = ∏_{j<k} Π_{t+j}^ω Π^{1−ω}`. Technology is constant returns (nominal marginal cost
`Ψ_{t+k}` independent of the firm's output) and demand is `Y_{t+k|t} = (P_{t+k|t}/P_{t+k})^{−ε}
C_{t+k}`. A reoptimising firm maximises
`∑_k θᵏ E_t{Λ_{t,t+k}(1/P_{t+k})(P_{t+k|t} Y_{t+k|t} − Ψ_{t+k} Y_{t+k|t})}`.

## Main results

* (a) `dist_law_of_motion`, `integral_indexed_mix`, `indexed_recursion`: the exact law of
  motion `Π_t^{1−ε} = θ (Π_{t−1}^ω Π^{1−ω})^{1−ε} + (1 − θ)(P*_t/P_{t−1})^{1−ε}`;
  `log_infl_eq_inflFn`, `inflFn_ss`, `hasFDerivAt_inflFn`: its exact first-order form
  `π̂_t = θω π̂_{t−1} + (1 − θ)(p*_t − p_{t−1} − π)`.
* (b) `objective_eq`, `hasDerivAt_objective`: the objective is
  `x^{1−ε} A_t − x^{−ε} B_t` and its derivative is `((1 − ε)/x)` times the book-form
  first-order condition `∑ θᵏ E_t{Λ Y_{t+k|t} (P*_t X_{t,k} − M Ψ_{t+k})/P_{t+k}}`;
  `foc_iff`: the FOC holds iff `P*_t = M B_t/A_t`; `isMaxOn_iff_foc`: a price maximises the
  objective **iff** it satisfies the FOC (sufficiency via Bernoulli's inequality).
* (c) `hasDerivAt_logResetPrice`, `logResetPrice_zero`, `resetPrice_isMaxOn_iff`: along any
  perturbation of the stochastic environment around the steady state, the log of the optimal
  reset price is differentiable with derivative
  `(1 − βθ) ∑ (βθ)ᵏ E_t{ψ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}`, i.e. the log-linear rule
  `p*_t = μ + (1 − βθ) ∑ (βθ)ᵏ E_t{ψ_{t+k} − ω ∑_{j<k} π̂_{t+j}}` (up to the steady-state path).
* (d) `hybrid_nkpc`: (a) and (c) imply
  `π̂_t = γ_b π̂_{t−1} + γ_f E_t π̂_{t+1} − λ̃ μ̂_t` with `γ_b = ω/(1 + βω)`,
  `γ_f = β/(1 + βω)`, `λ̃ = λ/(1 + βω)`, `λ = (1 − θ)(1 − βθ)/θ`; `rule_of_hybrid_nkpc`: the
  converse (given (a), the hybrid NKPC implies the rule (c)), so (c) ⟺ (d) under (a).
-/

namespace Gali.BasicNewKeynesianModel.Ex3_4

open MeasureTheory Filter Topology

/-! ### (a) The price index under indexation -/

namespace PriceIndex

/-- Galí (2015), Ex. 3.4(a), p. 91: the CES price index of a price distribution `ν`,
`P = (∫ p^{1−ε} dν)^{1/(1−ε)}`. -/
noncomputable def priceIdx (ν : Measure ℝ) (ε : ℝ) : ℝ := (∫ x, x ^ (1 - ε) ∂ν) ^ (1 - ε)⁻¹

/-- Galí (2015), Ex. 3.4(a), p. 91 (**law of motion of the price distribution**). Firms
`(F, m)`; those in `S` (mass `1 − θ`) reset to `P*`, the others index their price,
`p_t(i) = I p_{t−1}(i)` with `I = Π_{t−1}^ω Π^{1−ω}`; the non-resetters are a representative
subsample (their price distribution is `θ` times the full one). Then
`ν_t = θ (I · ν_{t−1}) + (1 − θ) δ_{P*}`. -/
theorem dist_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ I : ℝ}
    {S : Set F} (hS : MeasurableSet S) {pprev pnow : F → ℝ} (hprev : Measurable pprev)
    (hnow : Measurable pnow) {Pstar : ℝ} (hreset : ∀ i ∈ S, pnow i = Pstar)
    (hkeep : ∀ i ∉ S, pnow i = I * pprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev) :
    m.map pnow = ENNReal.ofReal θ • (m.map pprev).map (fun x => I * x) +
      ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := m) hS]
  rw [Measure.map_add _ _ hnow]
  have h1 : (m.restrict S).map pnow = ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
    rw [Measure.map_congr (g := fun _ => Pstar) ((ae_restrict_iff' hS).2
      (Filter.Eventually.of_forall hreset)), Measure.map_const, Measure.restrict_apply_univ,
      hmass]
  have h2 : (m.restrict Sᶜ).map pnow = ((m.restrict Sᶜ).map pprev).map (fun x => I * x) := by
    rw [Measure.map_map (measurable_const_mul I) hprev]
    exact Measure.map_congr ((ae_restrict_iff' hS.compl).2 (Filter.Eventually.of_forall hkeep))
  rw [h1, h2, hind, Measure.map_smul, add_comm]
  exact (measurable_const_mul I).aemeasurable

/-- Galí (2015), Ex. 3.4(a), p. 91: integrating `p^{1−ε}` against the indexed Calvo mixture
gives `θ I^{1−ε} ∫ p^{1−ε} dν + (1 − θ) P*^{1−ε}`. -/
theorem integral_indexed_mix {ν : Measure ℝ} {θ I ε : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hI : 0 < I)
    (Pstar : ℝ) (hnn : ∀ᵐ x ∂ν, 0 ≤ x) (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) ν) :
    ∫ x, x ^ (1 - ε) ∂(ENNReal.ofReal θ • ν.map (fun x => I * x) +
        ENNReal.ofReal (1 - θ) • Measure.dirac Pstar)
      = θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂ν) + (1 - θ) * Pstar ^ (1 - ε) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hae : (fun x : ℝ => (I * x) ^ (1 - ε)) =ᵐ[ν] fun x => I ^ (1 - ε) * x ^ (1 - ε) := by
    filter_upwards [hnn] with x hx
    rw [Real.mul_rpow hI.le hx]
  have hcomp : Integrable ((fun x : ℝ => x ^ (1 - ε)) ∘ fun x => I * x) ν :=
    (hint.const_mul (I ^ (1 - ε))).congr hae.symm
  have hmap : Integrable (fun x : ℝ => x ^ (1 - ε)) (ν.map fun x => I * x) :=
    (integrable_map_measure hmeas.aestronglyMeasurable
      (measurable_const_mul I).aemeasurable).2 hcomp
  have hd : Integrable (fun x : ℝ => x ^ (1 - ε)) (Measure.dirac Pstar) :=
    integrable_dirac (by simp)
  rw [integral_add_measure (hmap.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul,
    integral_map (measurable_const_mul I).aemeasurable hmeas.aestronglyMeasurable,
    integral_congr_ae hae, integral_const_mul]

/-- Galí (2015), Ex. 3.4(a), p. 91 (**exact inflation dynamics under indexation**): if
`ν_t = θ (I · ν_{t−1}) + (1 − θ) δ_{P*}` with `I = Π_{t−1}^ω Π^{1−ω}`, then with
`P_s` the price index of `ν_s`,
`(P_t/P_{t−1})^{1−ε} = θ I^{1−ε} + (1 − θ)(P*/P_{t−1})^{1−ε}`. -/
theorem indexed_recursion {ε θ I : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) (hI : 0 < I)
    {νprev : Measure ℝ} {Pstar : ℝ} (hPstar : 0 < Pstar) (hnn : ∀ᵐ x ∂νprev, 0 ≤ x)
    (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) νprev)
    (hpos : 0 < ∫ x, x ^ (1 - ε) ∂νprev) :
    (priceIdx (ENNReal.ofReal θ • νprev.map (fun x => I * x) +
        ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε / priceIdx νprev ε) ^ (1 - ε)
      = θ * I ^ (1 - ε) + (1 - θ) * (Pstar / priceIdx νprev ε) ^ (1 - ε) := by
  have hmix := integral_indexed_mix h0 h1.le hI Pstar hnn hint
  have hnew : 0 < θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂νprev) + (1 - θ) * Pstar ^ (1 - ε) := by
    have : 0 < (1 - θ) * Pstar ^ (1 - ε) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hPstar _)
    have : 0 ≤ θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂νprev) :=
      mul_nonneg h0 (mul_nonneg (Real.rpow_nonneg hI.le _) hpos.le)
    linarith
  have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
  have hIp : 0 < priceIdx νprev ε := Real.rpow_pos_of_pos hpos _
  have hIp' : priceIdx νprev ε ^ (1 - ε) = ∫ x, x ^ (1 - ε) ∂νprev :=
    Real.rpow_inv_rpow hpos.le hsub
  have hPt : priceIdx (ENNReal.ofReal θ • νprev.map (fun x => I * x) +
      ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε ^ (1 - ε)
      = θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂νprev) + (1 - θ) * Pstar ^ (1 - ε) := by
    unfold priceIdx
    rw [hmix, Real.rpow_inv_rpow hnew.le hsub]
  have hPt0 : 0 ≤ priceIdx (ENNReal.ofReal θ • νprev.map (fun x => I * x) +
      ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε := by
    unfold priceIdx
    rw [hmix]
    exact Real.rpow_nonneg hnew.le _
  rw [Real.div_rpow hPt0 hIp.le, Real.div_rpow hPstar.le hIp.le, hPt, hIp']
  field_simp

/-- Galí (2015), Ex. 3.4(a), p. 91: log gross inflation as a function of last period's log
gross inflation `v.1` and the log relative reset price `v.2 = log(P*_t/P_{t−1})`:
`(1 − ε)⁻¹ log(θ e^{(1−ε)(ω v.1 + (1−ω)π)} + (1 − θ) e^{(1−ε) v.2})`, `π = log Π`. -/
noncomputable def inflFn (θ ε ω πbar : ℝ) (v : ℝ × ℝ) : ℝ :=
  (1 - ε)⁻¹ * Real.log (θ * Real.exp ((1 - ε) * (ω * v.1 + (1 - ω) * πbar)) +
    (1 - θ) * Real.exp ((1 - ε) * v.2))

/-- Galí (2015), Ex. 3.4(a), p. 91: the exact recursion says
`log Π_t = inflFn (log Π_{t−1}, log(P*_t/P_{t−1}))`. -/
theorem log_infl_eq_inflFn {θ ε ω Pi Piprev Pibar x : ℝ} (hε : ε ≠ 1) (hPi : 0 < Pi)
    (hprev : 0 < Piprev) (hbar : 0 < Pibar) (hx : 0 < x)
    (hrec : Pi ^ (1 - ε) = θ * (Piprev ^ ω * Pibar ^ (1 - ω)) ^ (1 - ε) + (1 - θ) * x ^ (1 - ε)) :
    Real.log Pi = inflFn θ ε ω (Real.log Pibar) (Real.log Piprev, Real.log x) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hI : 0 < Piprev ^ ω * Pibar ^ (1 - ω) :=
    mul_pos (Real.rpow_pos_of_pos hprev _) (Real.rpow_pos_of_pos hbar _)
  have hlogI : Real.log (Piprev ^ ω * Pibar ^ (1 - ω))
      = ω * Real.log Piprev + (1 - ω) * Real.log Pibar := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hprev _).ne' (Real.rpow_pos_of_pos hbar _).ne',
      Real.log_rpow hprev, Real.log_rpow hbar]
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hPi, Real.rpow_def_of_pos hI, Real.rpow_def_of_pos hx, hlogI,
    mul_comm (_ + _) (1 - ε), mul_comm (Real.log x)] at h
  rw [inflFn, ← h]
  field_simp

/-- Galí (2015), Ex. 3.4(a), p. 91: at the steady state (`Π_{t−1} = Π`, `P*_t/P_{t−1} = Π`)
inflation is at its steady-state value: `inflFn (π, π) = π`. -/
theorem inflFn_ss (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) (ω πbar : ℝ) :
    inflFn θ ε ω πbar (πbar, πbar) = πbar := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have e : θ * Real.exp ((1 - ε) * (ω * πbar + (1 - ω) * πbar)) +
      (1 - θ) * Real.exp ((1 - ε) * πbar) = Real.exp ((1 - ε) * πbar) := by
    rw [show ω * πbar + (1 - ω) * πbar = πbar by ring]
    ring
  rw [inflFn, e, Real.log_exp]
  field_simp

/-- Galí (2015), Ex. 3.4(a), p. 91 (**exact first-order inflation equation**): at the steady
state `(π, π)` the Fréchet derivative of `inflFn` is `(θω, 1 − θ)`, i.e.
`π̂_t = θω π̂_{t−1} + (1 − θ)(p*_t − p_{t−1} − π)` to first order. -/
theorem hasFDerivAt_inflFn (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) (ω πbar : ℝ) :
    HasFDerivAt (inflFn θ ε ω πbar)
      ((θ * ω) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - θ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (πbar, πbar) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (πbar, πbar))
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := (πbar, πbar))
  have h1 := HasFDerivAt.exp (HasFDerivAt.const_mul (HasFDerivAt.const_add
    ((1 - ω) * πbar) (HasFDerivAt.const_mul hf ω)) (1 - ε))
  have h2 := HasFDerivAt.exp (HasFDerivAt.const_mul hs (1 - ε))
  have hsum := HasFDerivAt.add (HasFDerivAt.const_mul h1 θ) (HasFDerivAt.const_mul h2 (1 - θ))
  have hne : (fun v : ℝ × ℝ => θ * Real.exp ((1 - ε) * ((1 - ω) * πbar + ω * v.1)) +
      (1 - θ) * Real.exp ((1 - ε) * v.2)) (πbar, πbar) ≠ 0 := by
    have : (1 - ω) * πbar + ω * πbar = πbar := by ring
    simp only [this]
    rw [← add_mul, add_sub_cancel, one_mul]
    exact (Real.exp_pos _).ne'
  have h := HasFDerivAt.const_mul (HasFDerivAt.log hsum hne) (1 - ε)⁻¹
  have hfun : inflFn θ ε ω πbar = fun v : ℝ × ℝ => (1 - ε)⁻¹ * Real.log
      (θ * Real.exp ((1 - ε) * ((1 - ω) * πbar + ω * v.1)) +
        (1 - θ) * Real.exp ((1 - ε) * v.2)) := by
    funext v
    rw [inflFn, add_comm (ω * v.1)]
  rw [hfun]
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have : (1 - ω) * πbar + ω * πbar = πbar := by ring
  simp only [smul_apply, add_apply, Pi.add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, this]
  have hden : θ * Real.exp ((1 - ε) * πbar) + (1 - θ) * Real.exp ((1 - ε) * πbar)
      = Real.exp ((1 - ε) * πbar) := by ring
  rw [hden]
  have hE : Real.exp ((1 - ε) * πbar) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

end PriceIndex

/-! ### (b) The reset-price problem and its first-order condition -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 57: the desired gross markup `M = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), Ex. 3.4, p. 91, with eq. (9), p. 56: the demand for a firm whose price at
`t + k` is `x X_{t,k}`, `Y_{t+k|t} = (x X/P)^{−ε} C`. -/
noncomputable def demand (ε x : ℝ) (X P C : Ω → ℝ) : Ω → ℝ := fun ζ => (x * X ζ / P ζ) ^ (-ε) * C ζ

/-- Galí (2015), Ex. 3.4, p. 91: real profit at `t + k` discounted by `Λ`, with constant
returns (`C(Y) = Ψ Y`): `Λ (x X Y − Ψ Y)/P`. -/
noncomputable def profit (ε x : ℝ) (Λ X P C Ψ : Ω → ℝ) : Ω → ℝ :=
  fun ζ => Λ ζ * (x * X ζ * demand ε x X P C ζ - Ψ ζ * demand ε x X P C ζ) / P ζ

/-- Galí (2015), Ex. 3.4, p. 91: the reoptimising firm's objective at date `t` as a function
of its reset price `x = P*_t`, `∑_k θᵏ E_t{profit_k}`. Its arguments are indexed by the
horizon `k`: `Λ k = Λ_{t,t+k}`, `X k = X_{t,k}`, `P k = P_{t+k}`, `C k = C_{t+k}`,
`Ψ k = Ψ_{t+k}`. -/
noncomputable def objective (θ ε : ℝ) (t : ℕ) (Λ X P C Ψ : ℕ → Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (profit ε x (Λ k) (X k) (P k) (C k) (Ψ k)) ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: the revenue factor `Λ X^{1−ε} P^{ε−1} C`. -/
noncomputable def revFactor (ε : ℝ) (Λ X P C : Ω → ℝ) : Ω → ℝ :=
  fun ζ => Λ ζ * X ζ ^ (1 - ε) * P ζ ^ (ε - 1) * C ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: the cost factor `Λ Ψ X^{−ε} P^{ε−1} C`. -/
noncomputable def costFactor (ε : ℝ) (Λ X P C Ψ : Ω → ℝ) : Ω → ℝ :=
  fun ζ => Λ ζ * Ψ ζ * X ζ ^ (-ε) * P ζ ^ (ε - 1) * C ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: `A_t = ∑ θᵏ E_t{Λ X^{1−ε} P^{ε−1} C}`. -/
noncomputable def sumA (θ ε : ℝ) (t : ℕ) (Λ X P C : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: `B_t = ∑ θᵏ E_t{Λ Ψ X^{−ε} P^{ε−1} C}`. -/
noncomputable def sumB (θ ε : ℝ) (t : ℕ) (Λ X P C Ψ : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: the book-form first-order condition,
`∑ θᵏ E_t{Λ_{t,t+k} Y_{t+k|t} (P*_t X_{t,k} − M Ψ_{t+k})/P_{t+k}}`. -/
noncomputable def focSum (θ ε : ℝ) (t : ℕ) (Λ X P C Ψ : ℕ → Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (fun ζ' => Λ k ζ' * demand ε x (X k) (P k) (C k) ζ' *
    (x * X k ζ' - markup ε * Ψ k ζ') / P k ζ') ζ

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: demand in factored form,
`(x X/P)^{−ε} C = x^{−ε} X^{−ε} P^ε C`. -/
theorem demand_eq {ε x : ℝ} (hx : 0 < x) {X P C : Ω → ℝ} (hX : ∀ ζ, 0 < X ζ)
    (hP : ∀ ζ, 0 < P ζ) (ζ : Ω) :
    demand ε x X P C ζ = x ^ (-ε) * X ζ ^ (-ε) * P ζ ^ ε * C ζ := by
  have hX' := hX ζ
  have hP' := hP ζ
  rw [demand, Real.div_rpow (by positivity) hP'.le, Real.mul_rpow hx.le hX'.le,
    Real.rpow_neg hP'.le ε, div_inv_eq_mul]

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: profit is `x^{1−ε}` times the revenue factor minus
`x^{−ε}` times the cost factor. -/
theorem profit_eq {ε x : ℝ} (hx : 0 < x) {Λ X P C Ψ : Ω → ℝ} (hX : ∀ ζ, 0 < X ζ)
    (hP : ∀ ζ, 0 < P ζ) :
    profit ε x Λ X P C Ψ =
      x ^ (1 - ε) • revFactor ε Λ X P C - x ^ (-ε) • costFactor ε Λ X P C Ψ := by
  funext ζ
  have hX' := hX ζ
  have hP' := hP ζ
  have e1 : x ^ (1 - ε) = x * x ^ (-ε) := by rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  have e2 : X ζ ^ (1 - ε) = X ζ * X ζ ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hX', Real.rpow_one]
  have e3 : P ζ ^ (ε - 1) = P ζ ^ ε / P ζ := Real.rpow_sub_one hP'.ne' ε
  simp only [profit, revFactor, costFactor, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hX hP, e1, e2, e3]
  field_simp

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: the FOC integrand in factored form,
`Λ Y (x X − M Ψ)/P = x^{−ε}(x · revFactor − M · costFactor)`. -/
theorem focTerm_eq {ε x : ℝ} (hx : 0 < x) {Λ X P C Ψ : Ω → ℝ} (hX : ∀ ζ, 0 < X ζ)
    (hP : ∀ ζ, 0 < P ζ) :
    (fun ζ' => Λ ζ' * demand ε x X P C ζ' * (x * X ζ' - markup ε * Ψ ζ') / P ζ')
      = x ^ (-ε) • (x • revFactor ε Λ X P C - markup ε • costFactor ε Λ X P C Ψ) := by
  funext ζ
  have hX' := hX ζ
  have hP' := hP ζ
  have e2 : X ζ ^ (1 - ε) = X ζ * X ζ ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hX', Real.rpow_one]
  have e3 : P ζ ^ (ε - 1) = P ζ ^ ε / P ζ := Real.rpow_sub_one hP'.ne' ε
  simp only [revFactor, costFactor, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hX hP, e2, e3]
  field_simp

/-- Galí (2015), Ex. 3.4(b), p. 92: the objective is `x^{1−ε} A_t − x^{−ε} B_t` (the series
`A_t`, `B_t` being summable at the state considered). -/
theorem objective_eq {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) :
    objective 𝔼 θ ε t Λ X P C Ψ x ζ
      = x ^ (1 - ε) * sumA 𝔼 θ ε t Λ X P C ζ - x ^ (-ε) * sumB 𝔼 θ ε t Λ X P C Ψ ζ := by
  unfold objective sumA sumB
  have hterm : ∀ k, θ ^ k * 𝔼.E t (profit ε x (Λ k) (X k) (P k) (C k) (Ψ k)) ζ
      = x ^ (1 - ε) * (θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ) -
        x ^ (-ε) * (θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) := by
    intro k
    rw [profit_eq hx (hX k) (hP k), map_sub, map_smul, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm]
  rw [(hsA.mul_left _).tsum_sub (hsB.mul_left _), tsum_mul_left, tsum_mul_left]

/-- Galí (2015), Ex. 3.4(b), p. 92: the FOC sum is `x^{−ε}(x A_t − M B_t)`. -/
theorem focSum_eq {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) :
    focSum 𝔼 θ ε t Λ X P C Ψ x ζ
      = x ^ (-ε) * (x * sumA 𝔼 θ ε t Λ X P C ζ - markup ε * sumB 𝔼 θ ε t Λ X P C Ψ ζ) := by
  unfold focSum sumA sumB
  have hterm : ∀ k, θ ^ k * 𝔼.E t (fun ζ' => Λ k ζ' * demand ε x (X k) (P k) (C k) ζ' *
      (x * X k ζ' - markup ε * Ψ k ζ') / P k ζ') ζ
      = x ^ (-ε) * x * (θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ) -
        x ^ (-ε) * markup ε *
          (θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) := by
    intro k
    rw [focTerm_eq hx (hX k) (hP k), map_smul, map_sub, map_smul, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm]
  rw [(hsA.mul_left _).tsum_sub (hsB.mul_left _), tsum_mul_left, tsum_mul_left]
  ring

/-- Galí (2015), Ex. 3.4(b), p. 92: **the first-order condition**. The objective has
derivative `((1 − ε)/x) · ∑ θᵏ E_t{Λ Y_{t+k|t}(P*_t X_{t,k} − M Ψ_{t+k})/P_{t+k}}` at every
`x = P*_t > 0`. -/
theorem hasDerivAt_objective {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hε : 1 < ε) (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) :
    HasDerivAt (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ)
      ((1 - ε) / x * focSum 𝔼 θ ε t Λ X P C Ψ x ζ) x := by
  set A := sumA 𝔼 θ ε t Λ X P C ζ
  set B := sumB 𝔼 θ ε t Λ X P C Ψ ζ
  have h1 : HasDerivAt (fun y : ℝ => y ^ (1 - ε)) ((1 - ε) * x ^ (1 - ε - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => y ^ (-ε)) (-ε * x ^ (-ε - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h := HasDerivAt.sub (HasDerivAt.mul_const h1 A) (HasDerivAt.mul_const h2 B)
  have heq : (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ) =ᶠ[𝓝 x]
      fun y => y ^ (1 - ε) * A - y ^ (-ε) * B := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact objective_eq 𝔼 hy hX hP hsA hsB
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [focSum_eq 𝔼 hx hX hP hsA hsB, markup]
  have e1 : x ^ (1 - ε - 1) = x ^ (-ε) := by ring_nf
  have e2 : x ^ (-ε - 1) = x ^ (-ε) / x := Real.rpow_sub_one hx.ne' (-ε)
  rw [e1, e2]
  have hε1 : ε - 1 ≠ 0 := by linarith
  field_simp
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: the FOC `x A − M B = 0` holds iff `x = M B/A`. -/
theorem foc_iff_closed {ε x A B : ℝ} (hx : 0 < x) (hA : 0 < A) :
    x ^ (-ε) * (x * A - markup ε * B) = 0 ↔ x = markup ε * B / A := by
  rw [mul_eq_zero, eq_div_iff hA.ne']
  constructor
  · rintro (h | h)
    · exact absurd h (Real.rpow_pos_of_pos hx _).ne'
    · linarith
  · intro h
    right
    linarith

/-- Galí (2015), Ex. 3.4(b), p. 92: **the FOC pins down the reset price**:
`∑ θᵏ E_t{Λ Y (P*_t X − M Ψ)/P} = 0` iff `P*_t = M B_t/A_t`. -/
theorem foc_iff {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ)
    (hA : 0 < sumA 𝔼 θ ε t Λ X P C ζ) :
    focSum 𝔼 θ ε t Λ X P C Ψ x ζ = 0 ↔
      x = markup ε * sumB 𝔼 θ ε t Λ X P C Ψ ζ / sumA 𝔼 θ ε t Λ X P C ζ := by
  rw [focSum_eq 𝔼 hx hX hP hsA hsB]
  exact foc_iff_closed hx hA

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: the profit function `y^{1−ε} A − y^{−ε} B` (`A, B > 0`,
`ε > 1`) is maximised on `(0, ∞)` at `x = M B/A`; the proof is Bernoulli's inequality
`r^ε ≥ 1 + ε (r − 1)` for `r = y/x`. -/
theorem value_le_at_closed {ε A B x y : ℝ} (hε : 1 < ε) (hA : 0 < A) (hB : 0 < B)
    (hx : x = markup ε * B / A) (hy : 0 < y) :
    y ^ (1 - ε) * A - y ^ (-ε) * B ≤ x ^ (1 - ε) * A - x ^ (-ε) * B := by
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hxpos : 0 < x := by
    rw [hx, markup]
    have : 0 < ε / (ε - 1) := div_pos (by linarith) (by linarith)
    positivity
  set r := y / x with hr_def
  have hr : 0 < r := div_pos hy hxpos
  have hy' : y = r * x := by rw [hr_def]; field_simp
  have hb := one_add_mul_self_le_rpow_one_add (s := r - 1) (by linarith) (p := ε) hε.le
  rw [add_sub_cancel] at hb
  have hrr : r ^ (-ε) * r ^ ε = 1 := by rw [← Real.rpow_add hr]; simp
  have hk : r ^ (-ε) * (1 + ε * (r - 1)) ≤ 1 := by
    calc r ^ (-ε) * (1 + ε * (r - 1)) ≤ r ^ (-ε) * r ^ ε :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hr _).le
      _ = 1 := hrr
  rw [hy', Real.mul_rpow hr.le hxpos.le, Real.mul_rpow hr.le hxpos.le]
  have e1 : r ^ (1 - ε) = r * r ^ (-ε) := by rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
  have e2 : x ^ (1 - ε) = x * x ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hxpos, Real.rpow_one]
  rw [e1, e2]
  have hxA : x * A = ε * (ε - 1)⁻¹ * B := by rw [hx, markup]; field_simp
  have hinv : (ε - 1) * (ε - 1)⁻¹ = 1 := mul_inv_cancel₀ hε1
  have hdiff : x * x ^ (-ε) * A - x ^ (-ε) * B -
      (r * r ^ (-ε) * (x * x ^ (-ε)) * A - r ^ (-ε) * x ^ (-ε) * B)
      = x ^ (-ε) * B * (ε - 1)⁻¹ * (1 - r ^ (-ε) * (1 + ε * (r - 1))) := by
    linear_combination (x ^ (-ε) * (1 - r * r ^ (-ε))) * hxA +
      x ^ (-ε) * B * (1 - r ^ (-ε)) * hinv
  have hpos : 0 ≤ x ^ (-ε) * B * (ε - 1)⁻¹ * (1 - r ^ (-ε) * (1 + ε * (r - 1))) := by
    have : 0 < (ε - 1)⁻¹ := inv_pos.mpr (by linarith)
    have : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hxpos _
    have : 0 ≤ 1 - r ^ (-ε) * (1 + ε * (r - 1)) := by linarith
    positivity
  linarith

/-- Galí (2015), Ex. 3.4(b), p. 92: **optimality ⟺ the first-order condition**. With
`A_t, B_t > 0` (summable), a reset price `x > 0` maximises the objective over all positive
prices if and only if it satisfies the FOC. -/
theorem isMaxOn_iff_foc {θ ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {t : ℕ}
    {Λ X P C Ψ : ℕ → Ω → ℝ} (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ)
    (hA : 0 < sumA 𝔼 θ ε t Λ X P C ζ) (hB : 0 < sumB 𝔼 θ ε t Λ X P C Ψ ζ) :
    IsMaxOn (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ) (Set.Ioi 0) x ↔
      focSum 𝔼 θ ε t Λ X P C Ψ x ζ = 0 := by
  constructor
  · intro hmax
    have hloc : IsLocalMax (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ) x :=
      hmax.isLocalMax (Ioi_mem_nhds hx)
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_objective 𝔼 hx hε hX hP hsA hsB)
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (div_ne_zero (by linarith) hx.ne')
    · exact h
  · intro hfoc y hy
    have hxc := (foc_iff 𝔼 hx hX hP hsA hsB hA).1 hfoc
    change objective 𝔼 θ ε t Λ X P C Ψ y ζ ≤ objective 𝔼 θ ε t Λ X P C Ψ x ζ
    rw [objective_eq 𝔼 hy hX hP hsA hsB, objective_eq 𝔼 hx hX hP hsA hsB]
    exact value_le_at_closed hε hA hB hxc hy

/-! ### (c) Log-linearising the optimal reset price -/

/-- Galí (2015), Ex. 3.4(c), p. 92 (**differentiation under `E_t`**): if `z` is a bounded
random variable, `r ↦ E_t[e^{r z}]` has derivative `E_t[z e^{r z}]` at every `s`. The proof uses
only the axioms of `ExpectationSystem` (linearity, monotonicity, constants): the second-order
remainder is bounded uniformly in the state. -/
theorem hasDerivAt_E_exp {z : Ω → ℝ} {B : ℝ} (hz : ∀ ζ, |z ζ| ≤ B) (t : ℕ) (ζ : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ζ' => Real.exp (r * z ζ')) ζ)
      (𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ) s := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (fun ζ' => Real.exp ((s + h) * z ζ')) ζ -
      𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ -
        h • 𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ) =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound (Real.exp (|s| * |B|) * |B| ^ 2) ?_
    have hev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| * |B| ≤ 1 := by
      have hc : Tendsto (fun h : ℝ => |h| * |B|) (𝓝 0) (𝓝 0) := by
        have := (continuous_abs.tendsto (0 : ℝ)).mul_const |B|
        simpa using this
      exact hc (Iic_mem_nhds one_pos)
    filter_upwards [hev] with h hh
    have hfun : (fun ζ' => Real.exp (s * z ζ') * (Real.exp (h * z ζ') - 1 - h * z ζ'))
        = (fun ζ' => Real.exp ((s + h) * z ζ')) - (fun ζ' => Real.exp (s * z ζ')) -
          h • (fun ζ' => z ζ' * Real.exp (s * z ζ')) := by
      funext ζ'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [add_mul, Real.exp_add]
      ring
    have key : 𝔼.E t (fun ζ' => Real.exp ((s + h) * z ζ')) ζ -
        𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ -
          h • 𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ
        = 𝔼.E t (fun ζ' => Real.exp (s * z ζ') * (Real.exp (h * z ζ') - 1 - h * z ζ')) ζ := by
      rw [hfun, map_sub, map_sub, map_smul]
      rfl
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    refine 𝔼.abs_E_le (fun ζ' => ?_) t ζ
    have hzB : |z ζ'| ≤ |B| := (hz ζ').trans (le_abs_self B)
    have hhz : |h * z ζ'| ≤ 1 := by
      rw [abs_mul]
      calc |h| * |z ζ'| ≤ |h| * |B| := mul_le_mul_of_nonneg_left hzB (abs_nonneg h)
        _ ≤ 1 := hh
    have e1 := Real.abs_exp_sub_one_sub_id_le hhz
    have e2 : |Real.exp (s * z ζ')| ≤ Real.exp (|s| * |B|) := by
      rw [Real.abs_exp]
      apply Real.exp_le_exp.mpr
      calc s * z ζ' ≤ |s * z ζ'| := le_abs_self _
        _ = |s| * |z ζ'| := abs_mul _ _
        _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hzB (abs_nonneg s)
    have e3 : (h * z ζ') ^ 2 ≤ |B| ^ 2 * h ^ 2 := by
      rw [mul_pow, mul_comm]
      have : z ζ' ^ 2 ≤ |B| ^ 2 := by
        rw [← sq_abs (z ζ')]
        exact pow_le_pow_left₀ (abs_nonneg _) hzB 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg h)
    rw [abs_mul]
    calc |Real.exp (s * z ζ')| * |Real.exp (h * z ζ') - 1 - h * z ζ'|
        ≤ Real.exp (|s| * |B|) * (|B| ^ 2 * h ^ 2) :=
          mul_le_mul e2 (e1.trans e3) (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|s| * |B|) * B ^ 2 * |h| ^ 2 := by rw [sq_abs B, sq_abs h]; ring
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c), p. 92: `∑ (k + 1) qᵏ < ∞` for `0 ≤ q < 1` (deviations of the
indexation factor grow linearly with the horizon). -/
theorem summable_succ_mul_geom {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable fun k : ℕ => ((k : ℝ) + 1) * q ^ k := by
  have hn : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hA := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hB := summable_geometric_of_lt_one h0 h1
  refine (hA.add hB).congr fun k => ?_
  simp only [pow_one]
  ring

/-- Galí (2015), Ex. 3.4(c), p. 92: the discounted sum `∑ aᵏ E_t[e^{s zₖ}]`. -/
noncomputable def expSum (a : ℝ) (t : ℕ) (z : ℕ → Ω → ℝ) (s : ℝ) (ζ : Ω) : ℝ :=
  ∑' k, a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ

/-- Galí (2015), Ex. 3.4(c), p. 92: a radius on which the perturbed sums converge,
`log(2/(1 + a))/(K + 1)`. -/
noncomputable def radius (a K : ℝ) : ℝ := Real.log (2 / (1 + a)) / (K + 1)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c), p. 92: the radius is positive. -/
theorem radius_pos {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K) : 0 < radius a K := by
  unfold radius
  have : 1 < 2 / (1 + a) := by rw [one_lt_div (by linarith)]; linarith
  exact div_pos (Real.log_pos this) (by linarith)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c), p. 92: inside the radius, `e^{|s| K} ≤ 2/(1 + a)`. -/
theorem exp_le_of_lt_radius {a K s : ℝ} (h0 : 0 ≤ a) (hK : 0 ≤ K) (hs : |s| < radius a K) :
    Real.exp (|s| * K) ≤ 2 / (1 + a) := by
  have hpos : 0 < 2 / (1 + a) := div_pos two_pos (by linarith)
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have hr : |s| * (K + 1) ≤ Real.log (2 / (1 + a)) := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < K + 1)).1 hs
    linarith
  nlinarith [abs_nonneg s]

/-- Galí (2015), Ex. 3.4(c), p. 92: `|E_t[z e^{s z}]| ≤ B e^{|s| B}` for `|z| ≤ B`. -/
theorem abs_E_mul_exp_le {z : Ω → ℝ} {B : ℝ} (hz : ∀ ζ, |z ζ| ≤ B) (t : ℕ) (s : ℝ) (ζ : Ω) :
    |𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ| ≤ B * Real.exp (|s| * B) := by
  refine 𝔼.abs_E_le (fun ζ' => ?_) t ζ
  rw [abs_mul, Real.abs_exp]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hz ζ')
  refine mul_le_mul (hz ζ') (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hB
  calc s * z ζ' ≤ |s * z ζ'| := le_abs_self _
    _ = |s| * |z ζ'| := abs_mul _ _
    _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hz ζ') (abs_nonneg s)

/-- Galí (2015), Ex. 3.4(c), p. 92: `e^{−|s| B} ≤ E_t[e^{s z}] ≤ e^{|s| B}` for `|z| ≤ B`. -/
theorem E_exp_bounds {z : Ω → ℝ} {B : ℝ} (hz : ∀ ζ, |z ζ| ≤ B) (t : ℕ) (s : ℝ) (ζ : Ω) :
    Real.exp (-(|s| * B)) ≤ 𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ ∧
      𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ ≤ Real.exp (|s| * B) := by
  have hb : ∀ ζ', |s * z ζ'| ≤ |s| * B := fun ζ' => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hz ζ') (abs_nonneg s)
  have hlo : (fun _ => Real.exp (-(|s| * B))) ≤ fun ζ' => Real.exp (s * z ζ') := fun ζ' =>
    Real.exp_le_exp.mpr (by linarith [neg_abs_le (s * z ζ'), hb ζ'])
  have hhi : (fun ζ' => Real.exp (s * z ζ')) ≤ fun _ => Real.exp (|s| * B) := fun ζ' =>
    Real.exp_le_exp.mpr (by linarith [le_abs_self (s * z ζ'), hb ζ'])
  have h1 := 𝔼.mono t hlo ζ
  have h2 := 𝔼.mono t hhi ζ
  rw [𝔼.const] at h1 h2
  exact ⟨h1, h2⟩

/-- Galí (2015), Ex. 3.4(c), p. 92: inside the radius, the terms of `expSum` are dominated by
`(2/(1 + a)) (2a/(1 + a))ᵏ`, so the series converges and is positive. -/
theorem expSum_summable_pos {a K s : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K)
    {z : ℕ → Ω → ℝ} (hz : ∀ k ζ, |z k ζ| ≤ K * (k + 1)) (hs : |s| < radius a K) (t : ℕ)
    (ζ : Ω) : Summable (fun k => a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ) ∧
      0 < expSum 𝔼 a t z s ζ := by
  set c := 2 / (1 + a) with hc
  have hc0 : 0 < c := div_pos two_pos (by linarith)
  have hac : a * c < 1 := by rw [hc, mul_div_assoc', div_lt_one (by linarith)]; linarith
  have hexp := exp_le_of_lt_radius h0 hK hs
  have hbd : ∀ k, |a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ| ≤ c * (a * c) ^ k := by
    intro k
    have hb := (E_exp_bounds 𝔼 (hz k) t s ζ).2
    have hpos := (E_exp_bounds 𝔼 (hz k) t s ζ).1
    have hE0 : 0 ≤ 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ := (Real.exp_pos _).le.trans hpos
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 k), abs_of_nonneg hE0]
    have hpow : Real.exp (|s| * (K * (k + 1))) ≤ c ^ (k + 1) := by
      rw [show |s| * (K * (k + 1)) = ((k + 1 : ℕ) : ℝ) * (|s| * K) by push_cast; ring,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le hexp _
    calc a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ ≤ a ^ k * c ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (hb.trans hpow) (pow_nonneg h0 k)
      _ = c * (a * c) ^ k := by ring
  have hsum : Summable (fun k => a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity) hac).mul_left c)
      fun k => by rw [Real.norm_eq_abs]; exact hbd k
  refine ⟨hsum, ?_⟩
  unfold expSum
  refine hsum.tsum_pos (fun k => ?_) 0 ?_
  · exact mul_nonneg (pow_nonneg h0 k)
      ((Real.exp_pos _).le.trans (E_exp_bounds 𝔼 (hz k) t s ζ).1)
  · simp only [pow_zero, one_mul]
    exact (Real.exp_pos _).trans_le (E_exp_bounds 𝔼 (hz 0) t s ζ).1

/-- Galí (2015), Ex. 3.4(c), p. 92: at `s = 0` the sum is `∑ aᵏ = 1/(1 − a)`. -/
theorem expSum_zero {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (t : ℕ) (z : ℕ → Ω → ℝ) (ζ : Ω) :
    expSum 𝔼 a t z 0 ζ = (1 - a)⁻¹ := by
  unfold expSum
  simp only [zero_mul, Real.exp_zero, 𝔼.const, mul_one]
  exact tsum_geometric_of_lt_one h0 h1

/-- Galí (2015), Ex. 3.4(c), p. 92 (**term-by-term differentiation**): for `|zₖ| ≤ K(k + 1)`,
`s ↦ ∑ aᵏ E_t[e^{s zₖ}]` has derivative `∑ aᵏ E_t[zₖ]` at `s = 0`. -/
theorem hasDerivAt_expSum {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K)
    {z : ℕ → Ω → ℝ} (hz : ∀ k ζ, |z k ζ| ≤ K * (k + 1)) (t : ℕ) (ζ : Ω) :
    HasDerivAt (fun s => expSum 𝔼 a t z s ζ) (∑' k, a ^ k * 𝔼.E t (z k) ζ) 0 := by
  set r := radius a K
  have hr := radius_pos h0 h1 hK
  set c := 2 / (1 + a) with hc
  have hc0 : 0 < c := div_pos two_pos (by linarith)
  have hac : a * c < 1 := by rw [hc, mul_div_assoc', div_lt_one (by linarith)]; linarith
  set u : ℕ → ℝ := fun k => K * c * (((k : ℝ) + 1) * (a * c) ^ k)
  have hu : Summable u := (summable_succ_mul_geom (by positivity) hac).mul_left (K * c)
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun k s => a ^ k *
      𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ)
    (g' := fun k s => a ^ k * 𝔼.E t (fun ζ' => z k ζ' * Real.exp (s * z k ζ')) ζ)
    (t := Set.Ioo (-r) r) (y₀ := 0) hu isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => (hasDerivAt_E_exp 𝔼 (hz k) t ζ y).const_mul (a ^ k))
    (fun k y hy => ?_) hmem0 ?_ hmem0
  · refine hd.congr_deriv (tsum_congr fun k => ?_)
    simp only [zero_mul, Real.exp_zero, mul_one]
  · have hy' : |y| < r := abs_lt.mpr ⟨hy.1, hy.2⟩
    have hexp := exp_le_of_lt_radius h0 hK hy'
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    have hb := abs_E_mul_exp_le 𝔼 (hz k) t y ζ
    have hpow : Real.exp (|y| * (K * (k + 1))) ≤ c ^ (k + 1) := by
      rw [show |y| * (K * (k + 1)) = ((k + 1 : ℕ) : ℝ) * (|y| * K) by push_cast; ring,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le hexp _
    calc a ^ k * |𝔼.E t (fun ζ' => z k ζ' * Real.exp (y * z k ζ')) ζ|
        ≤ a ^ k * (K * (k + 1) * c ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
            (pow_nonneg h0 k)
      _ = u k := by simp only [u]; ring
  · simp only [zero_mul, Real.exp_zero, 𝔼.const, mul_one]
    exact summable_geometric_of_lt_one h0 h1

/-- Galí (2015), Ex. 3.4(c), p. 92: the series `∑ aᵏ E_t zₖ` converges for `|zₖ| ≤ K(k+1)`. -/
theorem summable_E_lin {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) {z : ℕ → Ω → ℝ}
    (hz : ∀ k ζ, |z k ζ| ≤ K * (k + 1)) (t : ℕ) (ζ : Ω) :
    Summable fun k => a ^ k * 𝔼.E t (z k) ζ := by
  refine Summable.of_norm_bounded ((summable_succ_mul_geom h0 h1).mul_left K) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
  calc a ^ k * |𝔼.E t (z k) ζ| ≤ a ^ k * (K * (k + 1)) :=
        mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hz k) t ζ) (pow_nonneg h0 k)
    _ = K * (((k : ℝ) + 1) * a ^ k) := by ring

/-- Galí (2015), Ex. 3.4(c), p. 92: **the log ratio of two perturbed sums**:
`d/ds [log ∑ aᵏ E_t e^{s z^b_k} − log ∑ aᵏ E_t e^{s z^a_k}]` at `0` equals
`(1 − a) ∑ aᵏ (E_t z^b_k − E_t z^a_k)`. -/
theorem hasDerivAt_logRatio {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K)
    {za zb : ℕ → Ω → ℝ} (hza : ∀ k ζ, |za k ζ| ≤ K * (k + 1))
    (hzb : ∀ k ζ, |zb k ζ| ≤ K * (k + 1)) (t : ℕ) (ζ : Ω) :
    HasDerivAt (fun s => Real.log (expSum 𝔼 a t zb s ζ) - Real.log (expSum 𝔼 a t za s ζ))
      ((1 - a) * ∑' k, a ^ k * (𝔼.E t (zb k) ζ - 𝔼.E t (za k) ζ)) 0 := by
  have hne : (1 - a)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have hA := HasDerivAt.log (hasDerivAt_expSum 𝔼 h0 h1 hK hza t ζ)
    (by rw [expSum_zero 𝔼 h0 h1]; exact hne)
  have hB := HasDerivAt.log (hasDerivAt_expSum 𝔼 h0 h1 hK hzb t ζ)
    (by rw [expSum_zero 𝔼 h0 h1]; exact hne)
  refine (HasDerivAt.sub hB hA).congr_deriv ?_
  rw [expSum_zero 𝔼 h0 h1, expSum_zero 𝔼 h0 h1]
  have hs : ∑' k, a ^ k * (𝔼.E t (zb k) ζ - 𝔼.E t (za k) ζ)
      = ∑' k, a ^ k * 𝔼.E t (zb k) ζ - ∑' k, a ^ k * 𝔼.E t (za k) ζ := by
    rw [← (summable_E_lin 𝔼 h0 h1 hzb t ζ).tsum_sub (summable_E_lin 𝔼 h0 h1 hza t ζ)]
    exact tsum_congr fun k => by ring
  rw [hs]
  have h1a : (1 : ℝ) - a ≠ 0 := by linarith
  field_simp

/-! #### The model along a perturbation path -/

/-- Galí (2015), Ex. 3.4(c), p. 92: steady-state parameters. `β` discount factor, `θ` Calvo
parameter, `ε` elasticity, `ω` indexation, `πbar = log Π` steady-state inflation, and the
date-`t` steady-state logs `pbar` (price level), `cbar` (consumption), `ψbar` (nominal
marginal cost). Along the steady state `P_{t+k} = e^{pbar + kπ}`, `Ψ_{t+k} = e^{ψbar + kπ}`,
`C_{t+k} = e^{cbar}`, `Λ_{t,t+k} = βᵏ`. -/
structure SteadyState where
  β : ℝ
  θ : ℝ
  ε : ℝ
  ω : ℝ
  πbar : ℝ
  pbar : ℝ
  cbar : ℝ
  ψbar : ℝ

variable (Ω) in
/-- Galí (2015), Ex. 3.4(c), p. 92: the directions of perturbation (log deviations, indexed by
the horizon `k`): `lam k = λ̂_{t,t+k}`, `price k = p̂_{t+k}`, `cons k = ĉ_{t+k}`,
`mc k = ψ̂_{t+k}` (nominal marginal cost) and `infl j = π̂_{t+j}`. -/
structure Deviation where
  lam : ℕ → Ω → ℝ
  price : ℕ → Ω → ℝ
  cons : ℕ → Ω → ℝ
  mc : ℕ → Ω → ℝ
  infl : ℕ → Ω → ℝ

/-- Galí (2015), Ex. 3.4(c): the discount factor along the path, `βᵏ e^{s λ̂}`. -/
noncomputable def lamPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (k * Real.log S.β + s * D.lam k ζ)

/-- Galí (2015), Ex. 3.4(c): the price level along the path. -/
noncomputable def pPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (S.pbar + k * S.πbar + s * D.price k ζ)

/-- Galí (2015), Ex. 3.4(c): consumption along the path. -/
noncomputable def cPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (S.cbar + s * D.cons k ζ)

/-- Galí (2015), Ex. 3.4(c): nominal marginal cost along the path. -/
noncomputable def psiPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (S.ψbar + k * S.πbar + s * D.mc k ζ)

/-- Galí (2015), Ex. 3.4(c): gross inflation `Π_{t+j}` along the path. -/
noncomputable def inflPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun j ζ => Real.exp (S.πbar + s * D.infl j ζ)

/-- Galí (2015), Ex. 3.4, p. 91: the indexation factor `X_{t,k} = ∏_{j<k} Π_{t+j}^ω Π^{1−ω}`
along the path. -/
noncomputable def xPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => ∏ j ∈ Finset.range k, inflPath S D s j ζ ^ S.ω * Real.exp S.πbar ^ (1 - S.ω)

/-- Galí (2015), Ex. 3.4(c): the deviation of `log X_{t,k}`, `ω ∑_{j<k} π̂_{t+j}`. -/
def xDev (S : SteadyState) (D : Deviation Ω) : ℕ → Ω → ℝ :=
  fun k ζ => S.ω * ∑ j ∈ Finset.range k, D.infl j ζ

/-- Galí (2015), Ex. 3.4(c): the deviation of the log revenue factor,
`λ̂ + (1 − ε) x̂ + (ε − 1) p̂ + ĉ`. -/
def aDev (S : SteadyState) (D : Deviation Ω) : ℕ → Ω → ℝ :=
  fun k ζ => D.lam k ζ + (1 - S.ε) * xDev S D k ζ + (S.ε - 1) * D.price k ζ + D.cons k ζ

/-- Galí (2015), Ex. 3.4(c): the deviation of the log cost factor, `â + ψ̂ − x̂`. -/
def bDev (S : SteadyState) (D : Deviation Ω) : ℕ → Ω → ℝ :=
  fun k ζ => aDev S D k ζ + (D.mc k ζ - xDev S D k ζ)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4, p. 91: `X_{t,k} = exp(kπ + s ω ∑_{j<k} π̂_{t+j})`. -/
theorem xPath_eq (S : SteadyState) (D : Deviation Ω) (s : ℝ) (k : ℕ) (ζ : Ω) :
    xPath S D s k ζ = Real.exp (k * S.πbar + s * xDev S D k ζ) := by
  unfold xPath inflPath xDev
  have hterm : ∀ j, Real.exp (S.πbar + s * D.infl j ζ) ^ S.ω * Real.exp S.πbar ^ (1 - S.ω)
      = Real.exp (S.πbar + s * S.ω * D.infl j ζ) := by
    intro j
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hterm]
  rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): the revenue factor along the path is
`e^{(ε−1) pbar + cbar} βᵏ e^{s âₖ}`. -/
theorem revFactor_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (s : ℝ) (k : ℕ) :
    revFactor S.ε (lamPath S D s k) (xPath S D s k) (pPath S D s k) (cPath S D s k)
      = (Real.exp ((S.ε - 1) * S.pbar + S.cbar) * S.β ^ k) •
        fun ζ => Real.exp (s * aDev S D k ζ) := by
  funext ζ
  simp only [revFactor, lamPath, pPath, cPath, xPath_eq, Pi.smul_apply, smul_eq_mul]
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_log hβ, ← Real.exp_nat_mul,
    Real.exp_log hβ, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  unfold aDev
  congr 1
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): the cost factor along the path is
`e^{ψbar + (ε−1) pbar + cbar} βᵏ e^{s b̂ₖ}`. -/
theorem costFactor_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (s : ℝ) (k : ℕ) :
    costFactor S.ε (lamPath S D s k) (xPath S D s k) (pPath S D s k) (cPath S D s k)
        (psiPath S D s k)
      = (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) * S.β ^ k) •
        fun ζ => Real.exp (s * bDev S D k ζ) := by
  funext ζ
  simp only [costFactor, lamPath, pPath, cPath, psiPath, xPath_eq, Pi.smul_apply, smul_eq_mul]
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_log hβ, ← Real.exp_nat_mul,
    Real.exp_log hβ, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  unfold bDev aDev
  congr 1
  ring

/-- Galí (2015), Ex. 3.4(c): `A_t` along the path is `e^{(ε−1) pbar + cbar}` times
`∑ (βθ)ᵏ E_t e^{s âₖ}`. -/
theorem sumA_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (t : ℕ) (s : ℝ)
    (ζ : Ω) : sumA 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s) ζ
      = Real.exp ((S.ε - 1) * S.pbar + S.cbar) * expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ := by
  unfold sumA expSum
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [revFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Galí (2015), Ex. 3.4(c): `B_t` along the path is `e^{ψbar + (ε−1) pbar + cbar}` times
`∑ (βθ)ᵏ E_t e^{s b̂ₖ}`. -/
theorem sumB_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (t : ℕ) (s : ℝ)
    (ζ : Ω) : sumB 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s)
        (psiPath S D s) ζ
      = Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) *
        expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ := by
  unfold sumB expSum
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [costFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Galí (2015), Ex. 3.4(c), p. 92: the log of the optimal reset price `M B_t/A_t` along the
perturbation path. -/
noncomputable def logResetPrice (S : SteadyState) (D : Deviation Ω) (t : ℕ) (s : ℝ) (ζ : Ω) :
    ℝ :=
  Real.log (markup S.ε *
    sumB 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s)
      (psiPath S D s) ζ /
    sumA 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s) ζ)

/-- Galí (2015), Ex. 3.4(c): the bounds on the perturbation directions used below: all
deviations grow at most linearly in the horizon, inflation deviations are bounded. -/
def DevBounded (D : Deviation Ω) (K : ℝ) : Prop :=
  (∀ k ζ, |D.lam k ζ| ≤ K * (k + 1)) ∧ (∀ k ζ, |D.price k ζ| ≤ K * (k + 1)) ∧
    (∀ k ζ, |D.cons k ζ| ≤ K * (k + 1)) ∧ (∀ k ζ, |D.mc k ζ| ≤ K * (k + 1)) ∧
    ∀ j ζ, |D.infl j ζ| ≤ K

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): `|x̂ₖ| ≤ K(k + 1)` for `0 ≤ ω ≤ 1`. -/
theorem abs_xDev_le {S : SteadyState} (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1) {D : Deviation Ω}
    {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (k : ℕ) (ζ : Ω) :
    |xDev S D k ζ| ≤ K * (k + 1) := by
  unfold xDev
  rw [abs_mul, abs_of_nonneg hω0]
  have hs : |∑ j ∈ Finset.range k, D.infl j ζ| ≤ k * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range k, |D.infl j ζ| ≤ ∑ _j ∈ Finset.range k, K :=
          Finset.sum_le_sum fun j _ => hD.2.2.2.2 j ζ
      _ = k * K := by simp
  calc S.ω * |∑ j ∈ Finset.range k, D.infl j ζ| ≤ 1 * (k * K) :=
        mul_le_mul hω1 hs (abs_nonneg _) zero_le_one
    _ ≤ K * (k + 1) := by nlinarith

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): `|âₖ|, |b̂ₖ| ≤ (2ε + 2) K (k + 1)`. -/
theorem abs_dev_le {S : SteadyState} (hε : 1 < S.ε) (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1)
    {D : Deviation Ω} {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (k : ℕ) (ζ : Ω) :
    |aDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) ∧
      |bDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) := by
  have hx := abs_xDev_le hω0 hω1 hK hD k ζ
  obtain ⟨h1, h2, h3, h4, -⟩ := hD
  have hk : (0 : ℝ) ≤ K * (k + 1) := by positivity
  have ha : |aDev S D k ζ| ≤ 2 * S.ε * K * (k + 1) := by
    unfold aDev
    have e1 : |(1 - S.ε) * xDev S D k ζ| ≤ (S.ε - 1) * (K * (k + 1)) := by
      rw [abs_mul, abs_of_nonpos (by linarith : 1 - S.ε ≤ 0), neg_sub]
      exact mul_le_mul_of_nonneg_left hx (by linarith)
    have e2 : |(S.ε - 1) * D.price k ζ| ≤ (S.ε - 1) * (K * (k + 1)) := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ S.ε - 1)]
      exact mul_le_mul_of_nonneg_left (h2 k ζ) (by linarith)
    calc |D.lam k ζ + (1 - S.ε) * xDev S D k ζ + (S.ε - 1) * D.price k ζ + D.cons k ζ|
        ≤ |D.lam k ζ| + |(1 - S.ε) * xDev S D k ζ| + |(S.ε - 1) * D.price k ζ| +
            |D.cons k ζ| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ K * (k + 1) + (S.ε - 1) * (K * (k + 1)) + (S.ε - 1) * (K * (k + 1)) +
            K * (k + 1) := by
          gcongr
          · exact h1 k ζ
          · exact h3 k ζ
      _ = 2 * S.ε * K * (k + 1) := by ring
  refine ⟨ha.trans (by nlinarith : 2 * S.ε * K * (k + 1) ≤ (2 * S.ε + 2) * K * (k + 1)), ?_⟩
  unfold bDev
  calc |aDev S D k ζ + (D.mc k ζ - xDev S D k ζ)|
      ≤ |aDev S D k ζ| + (|D.mc k ζ| + |xDev S D k ζ|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ 2 * S.ε * K * (k + 1) + (K * (k + 1) + K * (k + 1)) := by
        gcongr
        exact h4 k ζ
    _ = (2 * S.ε + 2) * K * (k + 1) := by ring

/-- Galí (2015), Ex. 3.4(c), p. 92: at the steady state the reset price is
`p* = μ + ψbar` (`μ = log M`). -/
theorem logResetPrice_zero (S : SteadyState) (hβ : 0 < S.β) (hθ0 : 0 ≤ S.θ)
    (hβθ : S.β * S.θ < 1) (hε : 1 < S.ε) (D : Deviation Ω) (t : ℕ) (ζ : Ω) :
    logResetPrice 𝔼 S D t 0 ζ = Real.log (markup S.ε) + S.ψbar := by
  have ha0 : 0 ≤ S.β * S.θ := mul_nonneg hβ.le hθ0
  unfold logResetPrice
  rw [sumA_path 𝔼 S hβ D t 0 ζ, sumB_path 𝔼 S hβ D t 0 ζ, expSum_zero 𝔼 ha0 hβθ,
    expSum_zero 𝔼 ha0 hβθ]
  have hM : 0 < markup S.ε := div_pos (by linarith) (by linarith)
  have h1b : 1 - S.β * S.θ ≠ 0 := by linarith
  have e : markup S.ε * (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) * (1 - S.β * S.θ)⁻¹) /
      (Real.exp ((S.ε - 1) * S.pbar + S.cbar) * (1 - S.β * S.θ)⁻¹)
      = markup S.ε * Real.exp S.ψbar := by
    rw [show S.ψbar + (S.ε - 1) * S.pbar + S.cbar = S.ψbar + ((S.ε - 1) * S.pbar + S.cbar)
      by ring, Real.exp_add]
    have := Real.exp_pos ((S.ε - 1) * S.pbar + S.cbar)
    field_simp
  rw [e, Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- Galí (2015), Ex. 3.4(c), p. 92: **the log-linear price-setting rule as an exact
derivative**. Perturb every variable of the reset-price problem in an arbitrary direction
`D` (with linearly bounded deviations); the log of the optimal reset price `M B_t/A_t` has
derivative
`(1 − βθ) ∑ (βθ)ᵏ E_t{ψ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}` at the steady state. Deviations of the
discount factor, the price level and consumption drop out. -/
theorem hasDerivAt_logResetPrice (S : SteadyState) (hβ : 0 < S.β) (hθ0 : 0 ≤ S.θ)
    (hβθ : S.β * S.θ < 1) (hε : 1 < S.ε) (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1) (D : Deviation Ω)
    {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (t : ℕ) (ζ : Ω) :
    HasDerivAt (fun s => logResetPrice 𝔼 S D t s ζ)
      ((1 - S.β * S.θ) * ∑' k, (S.β * S.θ) ^ k *
        𝔼.E t (fun ζ' => D.mc k ζ' - S.ω * ∑ j ∈ Finset.range k, D.infl j ζ') ζ) 0 := by
  have ha0 : 0 ≤ S.β * S.θ := mul_nonneg hβ.le hθ0
  have hK' : 0 ≤ (2 * S.ε + 2) * K := by nlinarith
  have hza : ∀ k ζ, |aDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).1
  have hzb : ∀ k ζ, |bDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).2
  have hR := hasDerivAt_logRatio 𝔼 ha0 hβθ hK' hza hzb t ζ
  have hM : 0 < markup S.ε := div_pos (by linarith) (by linarith)
  have hcont : ∀ z : ℕ → Ω → ℝ, (∀ k ζ, |z k ζ| ≤ (2 * S.ε + 2) * K * (k + 1)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), expSum 𝔼 (S.β * S.θ) t z s ζ ≠ 0 := by
    intro z hz
    refine (hasDerivAt_expSum 𝔼 ha0 hβθ hK' hz t ζ).continuousAt.eventually_ne ?_
    rw [expSum_zero 𝔼 ha0 hβθ]
    exact inv_ne_zero (by linarith)
  have heq : (fun s => logResetPrice 𝔼 S D t s ζ) =ᶠ[𝓝 0] fun s =>
      (Real.log (markup S.ε) + S.ψbar) + (Real.log (expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ) -
        Real.log (expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ)) := by
    filter_upwards [hcont _ hza, hcont _ hzb] with s hsa hsb
    unfold logResetPrice
    rw [sumA_path 𝔼 S hβ D t s ζ, sumB_path 𝔼 S hβ D t s ζ]
    have e : markup S.ε * (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) *
        expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ) /
        (Real.exp ((S.ε - 1) * S.pbar + S.cbar) * expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ)
        = markup S.ε * Real.exp S.ψbar * expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ /
          expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ := by
      rw [show S.ψbar + (S.ε - 1) * S.pbar + S.cbar = S.ψbar + ((S.ε - 1) * S.pbar + S.cbar)
        by ring, Real.exp_add]
      have := Real.exp_pos ((S.ε - 1) * S.pbar + S.cbar)
      field_simp
    rw [e, Real.log_div (mul_ne_zero (mul_ne_zero hM.ne' (Real.exp_pos _).ne') hsb) hsa,
      Real.log_mul (mul_ne_zero hM.ne' (Real.exp_pos _).ne') hsb,
      Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  refine ((hR.const_add _).congr_of_eventuallyEq heq).congr_deriv ?_
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  rw [← Pi.sub_apply (𝔼.E t (bDev S D k)), ← map_sub]
  have hfun : bDev S D k - aDev S D k
      = fun ζ' => D.mc k ζ' - S.ω * ∑ j ∈ Finset.range k, D.infl j ζ' := by
    funext ζ'
    simp only [Pi.sub_apply, bDev, xDev]
    ring
  rw [hfun]

/-- Galí (2015), Ex. 3.4(b)–(c), p. 92: **the perturbed reset price is optimal**. Near the
steady state (`|s| < δ`), for every state, a positive price maximises the perturbed objective
if and only if it equals `exp (logResetPrice s)`, the price whose derivative is computed in
`hasDerivAt_logResetPrice`. -/
theorem resetPrice_isMaxOn_iff (S : SteadyState) (hβ : 0 < S.β) (hθ0 : 0 ≤ S.θ)
    (hβθ : S.β * S.θ < 1) (hε : 1 < S.ε) (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1) (D : Deviation Ω)
    {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (t : ℕ) :
    ∃ δ > 0, ∀ s, |s| < δ → ∀ ζ, ∀ x > 0,
      (IsMaxOn (fun y => objective 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s)
          (cPath S D s) (psiPath S D s) y ζ) (Set.Ioi 0) x ↔
        x = Real.exp (logResetPrice 𝔼 S D t s ζ)) := by
  have ha0 : 0 ≤ S.β * S.θ := mul_nonneg hβ.le hθ0
  have hK' : 0 ≤ (2 * S.ε + 2) * K := by nlinarith
  have hza : ∀ k ζ, |aDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).1
  have hzb : ∀ k ζ, |bDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).2
  refine ⟨radius (S.β * S.θ) ((2 * S.ε + 2) * K), radius_pos ha0 hβθ hK', fun s hs ζ x hx => ?_⟩
  obtain ⟨hsa, hpa⟩ := expSum_summable_pos 𝔼 ha0 hβθ hK' hza hs t ζ
  obtain ⟨hsb, hpb⟩ := expSum_summable_pos 𝔼 ha0 hβθ hK' hzb hs t ζ
  have hX : ∀ k ζ, 0 < xPath S D s k ζ := fun k ζ => by rw [xPath_eq]; exact Real.exp_pos _
  have hP : ∀ k ζ, 0 < pPath S D s k ζ := fun k ζ => Real.exp_pos _
  have hsA : Summable fun k => S.θ ^ k * 𝔼.E t (revFactor S.ε (lamPath S D s k)
      (xPath S D s k) (pPath S D s k) (cPath S D s k)) ζ := by
    refine (hsa.mul_left (Real.exp ((S.ε - 1) * S.pbar + S.cbar))).congr fun k => ?_
    rw [revFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  have hsB : Summable fun k => S.θ ^ k * 𝔼.E t (costFactor S.ε (lamPath S D s k)
      (xPath S D s k) (pPath S D s k) (cPath S D s k) (psiPath S D s k)) ζ := by
    refine (hsb.mul_left (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar))).congr fun k => ?_
    rw [costFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  have hA : 0 < sumA 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s) ζ := by
    rw [sumA_path 𝔼 S hβ D t s ζ]; exact mul_pos (Real.exp_pos _) hpa
  have hB : 0 < sumB 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s)
      (psiPath S D s) ζ := by
    rw [sumB_path 𝔼 S hβ D t s ζ]; exact mul_pos (Real.exp_pos _) hpb
  have hM : 0 < markup S.ε := div_pos (by linarith) (by linarith)
  rw [isMaxOn_iff_foc 𝔼 hε hx hX hP hsA hsB hA hB, foc_iff 𝔼 hx hX hP hsA hsB hA,
    logResetPrice, Real.exp_log (div_pos (mul_pos hM hB) hA)]

/-! ### (d) The hybrid New Keynesian Phillips curve -/

/-- Galí (2015), eq. (17), p. 61, with `α = 0` (constant returns, `Θ = 1`):
`λ = (1 − θ)(1 − βθ)/θ`. -/
noncomputable def lambdaNK (β θ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ

/-- Galí (2015), Ex. 3.4(d), p. 92 (used for the forward sums of (c)): `E_t` commutes with a
series whose terms are dominated, uniformly in the state, by a summable sequence. Only the
`ExpectationSystem` axioms are used (`E_t` is monotone and fixes constants, hence continuous
for the uniform norm). -/
theorem E_tsum_of_bound {y : ℕ → Ω → ℝ} {u : ℕ → ℝ} (hy : ∀ k ζ, |y k ζ| ≤ u k)
    (hu : Summable u) (t : ℕ) :
    𝔼.E t (fun ζ => ∑' k, y k ζ) = fun ζ => ∑' k, 𝔼.E t (y k) ζ := by
  funext ζ
  set F : Ω → ℝ := fun ζ => ∑' k, y k ζ with hF
  set Fn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, y k with hFn
  set T : ℕ → ℝ := fun n => ∑' k, u (k + n) with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add u
  have hsy : ∀ ζ', Summable fun k => y k ζ' := fun ζ' =>
    Summable.of_norm_bounded hu fun k => by rw [Real.norm_eq_abs]; exact hy k ζ'
  have htail : ∀ n ζ', |F ζ' - Fn n ζ'| ≤ T n := by
    intro n ζ'
    have hsplit := (hsy ζ').sum_add_tsum_nat_add n
    have hFn' : Fn n ζ' = ∑ k ∈ Finset.range n, y k ζ' := by simp [hFn, Finset.sum_apply]
    rw [hFn']
    change |∑' k, y k ζ' - _| ≤ T n
    rw [← hsplit, add_sub_cancel_left]
    have hs' : Summable fun k => y (k + n) ζ' := (summable_nat_add_iff n).mpr (hsy ζ')
    have hg : Summable fun k => u (k + n) := (summable_nat_add_iff n).mpr hu
    calc |∑' k, y (k + n) ζ'| ≤ ∑' k, |y (k + n) ζ'| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => y (k + n) ζ')
              (by simpa only [Real.norm_eq_abs] using hs'.abs)
      _ ≤ T n := Summable.tsum_le_tsum (fun k => hy (k + n) ζ') hs'.abs hg
  have hEFn : ∀ n, 𝔼.E t (Fn n) ζ = ∑ k ∈ Finset.range n, 𝔼.E t (y k) ζ := by
    intro n
    simp [hFn, map_sum, Finset.sum_apply]
  have hlim1 : Tendsto (fun n => 𝔼.E t (Fn n) ζ) atTop (𝓝 (𝔼.E t F ζ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hTlim
    have h := 𝔼.abs_E_le (x := F - Fn n) (fun ζ' => htail n ζ') t ζ
    rw [map_sub, Pi.sub_apply] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have hsE : Summable fun k => 𝔼.E t (y k) ζ :=
    Summable.of_norm_bounded hu fun k => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hy k) t ζ
  have hlim2 : Tendsto (fun n => 𝔼.E t (Fn n) ζ) atTop (𝓝 (∑' k, 𝔼.E t (y k) ζ)) := by
    simp_rw [hEFn]
    exact hsE.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim1 hlim2

/-- Galí (2015), Ex. 3.4(d): the expectation system shifted by one period, `E'_t = E_{t+1}`
(used to apply forward uniqueness to equations that hold from date `1` on). -/
def shiftE : ExpectationSystem Ω where
  E := fun t => 𝔼.E (t + 1)
  const := fun t c => 𝔼.const (t + 1) c
  mono := fun t _ _ h => 𝔼.mono (t + 1) h
  tower := fun h x => 𝔼.tower (Nat.succ_le_succ h) x
  known := fun h x => 𝔼.known (Nat.succ_le_succ h) x

/-- Galí (2015), Ex. 3.4(c)–(d): the relative term of the price-setting rule at horizon `k`,
`(p̂_{t+k} − p̂_t) − μ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}`, with `p̂_{t+k} − p̂_t = ∑_{j<k} π̂_{t+1+j}`. -/
def Zrel (ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t k : ℕ) : Ω → ℝ :=
  fun ζ => ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ - mu (t + k) ζ -
    ω * ∑ j ∈ Finset.range k, infl (t + j) ζ

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `Z_{t,0} = −μ̂_t`. -/
theorem Zrel_zero (ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t : ℕ) :
    Zrel ω infl mu t 0 = fun ζ => -mu t ζ := by
  funext ζ
  simp [Zrel]

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `Z_{t,k+1} = π̂_{t+1} − ω π̂_t + Z_{t+1,k}`. -/
theorem Zrel_succ (ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t k : ℕ) :
    Zrel ω infl mu t (k + 1) =
      fun ζ => infl (t + 1) ζ - ω * infl t ζ + Zrel ω infl mu (t + 1) k ζ := by
  funext ζ
  simp only [Zrel, Finset.sum_range_succ']
  have e1 : ∑ j ∈ Finset.range k, infl (t + 1 + (j + 1)) ζ
      = ∑ j ∈ Finset.range k, infl (t + 1 + 1 + j) ζ :=
    Finset.sum_congr rfl fun j _ => by rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
  have e2 : ∑ j ∈ Finset.range k, infl (t + (j + 1)) ζ
      = ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ :=
    Finset.sum_congr rfl fun j _ => by rw [show t + (j + 1) = t + 1 + j by omega]
  rw [e1, e2, show t + (k + 1) = t + 1 + k by omega]
  simp only [add_zero]
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `|Z_{t,k}| ≤ 2M(k + 1)` when `|π̂|, |μ̂| ≤ M`, `0 ≤ ω ≤ 1`. -/
theorem abs_Zrel_le {ω M : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hM : 0 ≤ M)
    {infl mu : ℕ → Ω → ℝ} (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (t k : ℕ) (ζ : Ω) : |Zrel ω infl mu t k ζ| ≤ 2 * M * (k + 1) := by
  have hs : ∀ m, |∑ j ∈ Finset.range k, infl (m + j) ζ| ≤ k * M := by
    intro m
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range k, |infl (m + j) ζ| ≤ ∑ _j ∈ Finset.range k, M :=
          Finset.sum_le_sum fun j _ => hib _ ζ
      _ = k * M := by simp
  unfold Zrel
  have h1 := hs (t + 1)
  have h2 := hs t
  have h3 := hmb (t + k) ζ
  have h4 : |ω * ∑ j ∈ Finset.range k, infl (t + j) ζ| ≤ k * M := by
    rw [abs_mul, abs_of_nonneg hω0]
    calc ω * |∑ j ∈ Finset.range k, infl (t + j) ζ| ≤ 1 * (k * M) :=
          mul_le_mul hω1 h2 (abs_nonneg _) zero_le_one
      _ = k * M := one_mul _
  calc |∑ j ∈ Finset.range k, infl (t + 1 + j) ζ - mu (t + k) ζ -
        ω * ∑ j ∈ Finset.range k, infl (t + j) ζ|
      ≤ |∑ j ∈ Finset.range k, infl (t + 1 + j) ζ| + |mu (t + k) ζ| +
          |ω * ∑ j ∈ Finset.range k, infl (t + j) ζ| :=
        (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ k * M + M + k * M := by gcongr
    _ ≤ 2 * M * (k + 1) := by nlinarith

/-- Galí (2015), Ex. 3.4(c)–(d): the discounted forward sum `T_t = ∑ aᵏ E_t Z_{t,k}`. -/
noncomputable def Tsum (a ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ζ => ∑' k, a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ

/-- Galí (2015), Ex. 3.4(d): the forward sum is bounded by `∑ aᵏ 2M(k + 1)`. -/
theorem abs_Tsum_le {a ω M : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hM : 0 ≤ M) {infl mu : ℕ → Ω → ℝ} (hib : ∀ t ζ, |infl t ζ| ≤ M)
    (hmb : ∀ t ζ, |mu t ζ| ≤ M) (t : ℕ) (ζ : Ω) :
    |Tsum 𝔼 a ω infl mu t ζ| ≤ ∑' k : ℕ, 2 * M * (((k : ℝ) + 1) * a ^ k) := by
  have hb : ∀ k, |a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ| ≤ 2 * M * (((k : ℝ) + 1) * a ^ k) := by
    intro k
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    calc a ^ k * |𝔼.E t (Zrel ω infl mu t k) ζ| ≤ a ^ k * (2 * M * (k + 1)) :=
          mul_le_mul_of_nonneg_left
            (𝔼.abs_E_le (abs_Zrel_le hω0 hω1 hM hib hmb t k) t ζ) (pow_nonneg h0 k)
      _ = 2 * M * (((k : ℝ) + 1) * a ^ k) := by ring
  have hg : Summable fun k : ℕ => 2 * M * (((k : ℝ) + 1) * a ^ k) :=
    (summable_succ_mul_geom h0 h1).mul_left _
  have hs : Summable fun k => |a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb hg
  calc |Tsum 𝔼 a ω infl mu t ζ| ≤ ∑' k, |a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ| := by
        simpa [Real.norm_eq_abs, Tsum] using
          norm_tsum_le_tsum_norm (f := fun k => a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ)
            (by simpa only [Real.norm_eq_abs] using hs)
    _ ≤ _ := Summable.tsum_le_tsum hb hs hg

/-- Galí (2015), Ex. 3.4(d): **the recursion of the forward sum**,
`T_t = −μ̂_t + (a/(1 − a))(E_t π̂_{t+1} − ω π̂_t) + a E_t T_{t+1}`. -/
theorem Tsum_rec {a ω M : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hM : 0 ≤ M) {infl mu : ℕ → Ω → ℝ} (hia : 𝔼.Adapted infl) (hma : 𝔼.Adapted mu)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M) (t : ℕ) :
    Tsum 𝔼 a ω infl mu t = (fun ζ => -mu t ζ) +
      (a / (1 - a)) • (𝔼.E t (infl (t + 1)) - ω • infl t) +
        a • 𝔼.E t (Tsum 𝔼 a ω infl mu (t + 1)) := by
  have hZ : ∀ s k ζ, |Zrel ω infl mu s k ζ| ≤ 2 * M * (k + 1) :=
    fun s k ζ => abs_Zrel_le hω0 hω1 hM hib hmb s k ζ
  -- `E_t` of the next forward sum
  have hET : 𝔼.E t (Tsum 𝔼 a ω infl mu (t + 1))
      = fun ζ => ∑' k, a ^ k * 𝔼.E t (Zrel ω infl mu (t + 1) k) ζ := by
    have hy : ∀ k ζ, |(a ^ k • 𝔼.E (t + 1) (Zrel ω infl mu (t + 1) k)) ζ|
        ≤ 2 * M * (((k : ℝ) + 1) * a ^ k) := by
      intro k ζ
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
      calc a ^ k * |𝔼.E (t + 1) (Zrel ω infl mu (t + 1) k) ζ| ≤ a ^ k * (2 * M * (k + 1)) :=
            mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hZ (t + 1) k) (t + 1) ζ) (pow_nonneg h0 k)
        _ = 2 * M * (((k : ℝ) + 1) * a ^ k) := by ring
    have h := E_tsum_of_bound 𝔼 hy ((summable_succ_mul_geom h0 h1).mul_left _) t
    have hl : (fun ζ => ∑' k, (a ^ k • 𝔼.E (t + 1) (Zrel ω infl mu (t + 1) k)) ζ)
        = Tsum 𝔼 a ω infl mu (t + 1) := by
      funext ζ
      simp only [Tsum, Pi.smul_apply, smul_eq_mul]
    rw [hl] at h
    rw [h]
    funext ζ
    refine tsum_congr fun k => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, 𝔼.tower (Nat.le_succ t)]
  funext ζ
  have hsum := summable_E_lin 𝔼 h0 h1 (hZ t) t ζ
  have hsum1 := summable_E_lin 𝔼 h0 h1 (hZ (t + 1)) t ζ
  have hgeo := summable_geometric_of_lt_one h0 h1
  have hterm : ∀ k, a ^ (k + 1) * 𝔼.E t (Zrel ω infl mu t (k + 1)) ζ
      = a * (𝔼.E t (infl (t + 1)) ζ - ω * infl t ζ) * a ^ k +
        a * (a ^ k * 𝔼.E t (Zrel ω infl mu (t + 1) k) ζ) := by
    intro k
    have hf : Zrel ω infl mu t (k + 1)
        = infl (t + 1) - ω • infl t + Zrel ω infl mu (t + 1) k := by
      rw [Zrel_succ]
      funext ζ'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf, map_add, map_sub, map_smul, hia t]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h0E : 𝔼.E t (Zrel ω infl mu t 0) ζ = -mu t ζ := by
    rw [Zrel_zero]
    have : (fun ζ => -mu t ζ) = -mu t := rfl
    rw [this, map_neg, hma t]
    rfl
  simp only [Tsum, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hET]
  rw [hsum.tsum_eq_zero_add, pow_zero, one_mul, h0E]
  simp_rw [hterm]
  rw [(hgeo.mul_left _).tsum_add (hsum1.mul_left a), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one h0 h1]
  have h1a : (1 : ℝ) - a ≠ 0 := by linarith
  field_simp
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `p̂_{t+k} = p̂_t + ∑_{j<k} π̂_{t+1+j}`. -/
theorem price_add {p infl : ℕ → Ω → ℝ} (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (t k : ℕ) : p (t + k) = p t + fun ζ => ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ := by
  induction k with
  | zero => funext ζ; simp
  | succ k ih =>
    funext ζ
    have h := congrFun (hinfl (t + k)) ζ
    have hi := congrFun ih ζ
    simp only [Pi.add_apply, Pi.sub_apply] at h hi ⊢
    rw [Finset.sum_range_succ, show t + 1 + k = t + k + 1 by omega, h,
      show t + (k + 1) = t + k + 1 by omega, hi]
    ring

/-- Galí (2015), Ex. 3.4(c): the price-setting rule in levels,
`(1 − βθ) ∑ (βθ)ᵏ E_t{p̂_{t+k} − μ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}`, equals `p̂_t + (1 − βθ) T_t`. -/
theorem rule_eq {a ω M : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hM : 0 ≤ M) {p infl mu : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (t : ℕ) :
    ((1 - a) • fun ζ => ∑' k, a ^ k * 𝔼.E t (fun ζ' => p (t + k) ζ' - mu (t + k) ζ' -
        ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') ζ)
      = p t + (1 - a) • Tsum 𝔼 a ω infl mu t := by
  have hZ : ∀ k ζ, |Zrel ω infl mu t k ζ| ≤ 2 * M * (k + 1) :=
    fun k ζ => abs_Zrel_le hω0 hω1 hM hib hmb t k ζ
  funext ζ
  have hterm : ∀ k, 𝔼.E t (fun ζ' => p (t + k) ζ' - mu (t + k) ζ' -
      ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') ζ = p t ζ + 𝔼.E t (Zrel ω infl mu t k) ζ := by
    intro k
    have hf : (fun ζ' => p (t + k) ζ' - mu (t + k) ζ' -
        ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') = p t + Zrel ω infl mu t k := by
      funext ζ'
      rw [price_add hinfl t k]
      simp only [Zrel, Pi.add_apply]
      ring
    rw [hf, map_add, hpa t, Pi.add_apply]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hterm, mul_add]
  rw [((summable_geometric_of_lt_one h0 h1).mul_right (p t ζ)).tsum_add
      (summable_E_lin 𝔼 h0 h1 hZ t ζ), tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  simp only [Tsum]
  have h1a : (1 : ℝ) - a ≠ 0 := by linarith
  field_simp

/-- Galí (2015), Ex. 3.4(d), p. 92: **the hybrid New Keynesian Phillips curve**. Let the
(log-deviation) price level `p̂`, inflation `π̂_{t+1} = p̂_{t+1} − p̂_t`, the average markup
`μ̂` (so `ψ̂ = p̂ − μ̂`) and the reset price `p̂*` satisfy (a)
`π̂_{t+1} = θω π̂_t + (1 − θ)(p̂*_{t+1} − p̂_t)` and the rule (c)
`p̂*_t = (1 − βθ) ∑ (βθ)ᵏ E_t{ψ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}`. Then
`π̂_{t+1} = γ_b π̂_t + γ_f E_{t+1} π̂_{t+2} − λ̃ μ̂_{t+1}` with `γ_b = ω/(1 + βω)`,
`γ_f = β/(1 + βω)`, `λ̃ = λ/(1 + βω)`. (The handwritten 1st-edition solution obtains a
different `γ_b`; it is wrong.) -/
theorem hybrid_nkpc {β θ ω M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hM : 0 ≤ M) {p infl mu pstar : ℕ → Ω → ℝ}
    (hpa : 𝔼.Adapted p) (hia : 𝔼.Adapted infl) (hma : 𝔼.Adapted mu)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (ha : ∀ t, infl (t + 1) = (θ * ω) • infl t + (1 - θ) • (pstar (t + 1) - p t))
    (hc : ∀ t, pstar t = (1 - β * θ) • fun ζ => ∑' k, (β * θ) ^ k * 𝔼.E t (fun ζ' =>
      p (t + k) ζ' - mu (t + k) ζ' - ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') ζ) (t : ℕ) :
    infl (t + 1) = (ω / (1 + β * ω)) • infl t + (β / (1 + β * ω)) • 𝔼.E (t + 1) (infl (t + 2)) -
      (lambdaNK β θ / (1 + β * ω)) • mu (t + 1) := by
  have ha0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0.le
  have ha1 : β * θ < 1 := by nlinarith
  -- `x_t = p̂*_t − p̂_t = (1 − βθ) T_t`
  have hx : ∀ s, pstar s - p s = (1 - β * θ) • Tsum 𝔼 (β * θ) ω infl mu s := by
    intro s
    rw [hc s, rule_eq 𝔼 ha0 ha1 hω0 hω1 hM hpa hib hmb hinfl s]
    abel
  have hrec := Tsum_rec 𝔼 ha0 ha1 hω0 hω1 hM hia hma hib hmb (t + 1)
  funext ζ
  -- (a) at `t + 1` and at `t + 2`, in terms of `x`
  have e5 : θ * infl (t + 1) ζ = θ * ω * infl t ζ +
      (1 - θ) * ((1 - β * θ) * Tsum 𝔼 (β * θ) ω infl mu (t + 1) ζ) := by
    have h1 := congrFun (ha t) ζ
    have h2 := congrFun (hinfl t) ζ
    have h3 := congrFun (hx (t + 1)) ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    linear_combination h1 - (1 - θ) * h2 + (1 - θ) * h3
  have e7 : θ * 𝔼.E (t + 1) (infl (t + 2)) ζ = θ * ω * infl (t + 1) ζ +
      (1 - θ) * ((1 - β * θ) * 𝔼.E (t + 1) (Tsum 𝔼 (β * θ) ω infl mu (t + 2)) ζ) := by
    have hE : 𝔼.E (t + 1) (infl (t + 2)) = (θ * ω) • infl (t + 1) +
        (1 - θ) • (𝔼.E (t + 1) (pstar (t + 2)) - p (t + 1)) := by
      rw [ha (t + 1), map_add, map_smul, map_smul, map_sub, hia (t + 1), hpa (t + 1)]
    have hE2 : 𝔼.E (t + 1) (pstar (t + 2)) = 𝔼.E (t + 1) (p (t + 2)) +
        (1 - β * θ) • 𝔼.E (t + 1) (Tsum 𝔼 (β * θ) ω infl mu (t + 2)) := by
      rw [← map_smul, ← map_add, ← hx (t + 2)]
      abel_nf
    have hEp : 𝔼.E (t + 1) (p (t + 2)) = 𝔼.E (t + 1) (infl (t + 2)) + p (t + 1) := by
      rw [show t + 2 = t + 1 + 1 by omega, hinfl (t + 1), map_sub, hpa (t + 1)]
      abel
    have h1 := congrFun hE ζ
    have h2 := congrFun hE2 ζ
    have h3 := congrFun hEp ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    linear_combination h1 + (1 - θ) * h2 + (1 - θ) * h3
  have e6 := congrFun hrec ζ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e6
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lambdaNK]
  have h1b : (1 : ℝ) - β * θ ≠ 0 := by linarith
  have hden : (1 : ℝ) + β * ω ≠ 0 := by nlinarith
  have hθ : θ ≠ 0 := hθ0.ne'
  set T1 := Tsum 𝔼 (β * θ) ω infl mu (t + 1) ζ
  set ET2 := 𝔼.E (t + 1) (Tsum 𝔼 (β * θ) ω infl mu (t + 2)) ζ
  have key : θ * (1 + β * ω) * infl (t + 1) ζ = θ * ω * infl t ζ +
      θ * β * 𝔼.E (t + 1) (infl (t + 2)) ζ - (1 - θ) * (1 - β * θ) * mu (t + 1) ζ := by
    have e6' : (1 - β * θ) * T1 = -(1 - β * θ) * mu (t + 1) ζ +
        β * θ * (𝔼.E (t + 1) (infl (t + 1 + 1)) ζ - ω * infl (t + 1) ζ) +
        β * θ * ((1 - β * θ) * ET2) := by
      rw [e6]
      field_simp
    rw [show t + 1 + 1 = t + 2 by omega] at e6'
    linear_combination e5 + (1 - θ) * e6' - β * θ * e7
  field_simp
  linear_combination key

/-- Galí (2015), Ex. 3.4(d), p. 92 (**the converse**): given the inflation equation (a), the
hybrid NKPC implies the price-setting rule (c) at every date `t ≥ 1`. Together with
`hybrid_nkpc`, under (a) the rule (c) and the hybrid NKPC are equivalent (for bounded
inflation and markups). The proof uses forward uniqueness (`forward_unique`) for
`x_t = βθ E_t x_{t+1} + f_t`, since `|βθ| < 1`. -/
theorem rule_of_hybrid_nkpc {β θ ω M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hM : 0 ≤ M) {p infl mu pstar : ℕ → Ω → ℝ}
    (hpa : 𝔼.Adapted p) (hia : 𝔼.Adapted infl) (hma : 𝔼.Adapted mu)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (ha : ∀ t, infl (t + 1) = (θ * ω) • infl t + (1 - θ) • (pstar (t + 1) - p t))
    (hnk : ∀ t, infl (t + 1) = (ω / (1 + β * ω)) • infl t +
      (β / (1 + β * ω)) • 𝔼.E (t + 1) (infl (t + 2)) - (lambdaNK β θ / (1 + β * ω)) • mu (t + 1))
    (t : ℕ) :
    pstar (t + 1) = (1 - β * θ) • fun ζ => ∑' k, (β * θ) ^ k * 𝔼.E (t + 1) (fun ζ' =>
      p (t + 1 + k) ζ' - mu (t + 1 + k) ζ' - ω * ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ') ζ := by
  set a := β * θ with ha_def
  have ha0 : 0 ≤ a := mul_nonneg hβ0 hθ0.le
  have ha1 : a < 1 := by nlinarith
  have h1θ : (1 : ℝ) - θ ≠ 0 := by linarith
  have hden : (1 : ℝ) + β * ω ≠ 0 := by nlinarith
  -- `θ π̂_{s+1} = θω π̂_s + (1 − θ) x_{s+1}` with `x_s = p̂*_s − p̂_s`
  have f5 : ∀ s ζ, θ * infl (s + 1) ζ =
      θ * ω * infl s ζ + (1 - θ) * (pstar (s + 1) ζ - p (s + 1) ζ) := by
    intro s ζ
    have h1 := congrFun (ha s) ζ
    have h2 := congrFun (hinfl s) ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    linear_combination h1 - (1 - θ) * h2
  set z₁ : ℕ → Ω → ℝ := fun s => pstar (s + 1) - p (s + 1) with hz₁
  set z₂ : ℕ → Ω → ℝ := fun s => (1 - a) • Tsum 𝔼 a ω infl mu (s + 1) with hz₂
  set u : ℕ → Ω → ℝ := fun s => (-(1 - a)) • mu (s + 1) +
    a • (𝔼.E (s + 1) (infl (s + 2)) - ω • infl (s + 1)) with hu
  have h₂ : ∀ s, z₂ s = a • (shiftE 𝔼).E s (z₂ (s + 1)) + u s := by
    intro s
    have hr := Tsum_rec 𝔼 ha0 ha1 hω0 hω1 hM hia hma hib hmb (s + 1)
    change (1 - a) • Tsum 𝔼 a ω infl mu (s + 1) =
      a • 𝔼.E (s + 1) ((1 - a) • Tsum 𝔼 a ω infl mu (s + 1 + 1)) + u s
    rw [hr, map_smul]
    funext ζ
    simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      show s + 1 + 1 = s + 2 by omega]
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    field_simp
    ring
  have h₁ : ∀ s, z₁ s = a • (shiftE 𝔼).E s (z₁ (s + 1)) + u s := by
    intro s
    change pstar (s + 1) - p (s + 1) =
      a • 𝔼.E (s + 1) (pstar (s + 1 + 1) - p (s + 1 + 1)) + u s
    have hE : θ • 𝔼.E (s + 1) (infl (s + 2)) = (θ * ω) • infl (s + 1) +
        (1 - θ) • 𝔼.E (s + 1) (pstar (s + 1 + 1) - p (s + 1 + 1)) := by
      have hf : θ • infl (s + 2) = (θ * ω) • infl (s + 1) +
          (1 - θ) • (pstar (s + 1 + 1) - p (s + 1 + 1)) := by
        funext ζ
        have := f5 (s + 1) ζ
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show s + 2 = s + 1 + 1 by omega]
        linarith
      rw [← map_smul, hf, map_add, map_smul, map_smul, hia (s + 1)]
    funext ζ
    have f7 := congrFun hE ζ
    have f5s := f5 s ζ
    have nk := congrFun (hnk s) ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f7 nk
    simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have key : θ * (1 + β * ω) * infl (s + 1) ζ = θ * ω * infl s ζ +
        θ * β * 𝔼.E (s + 1) (infl (s + 2)) ζ - (1 - θ) * (1 - β * θ) * mu (s + 1) ζ := by
      rw [nk]
      unfold lambdaNK
      field_simp
    have hT : (1 - θ) * (pstar (s + 1) ζ - p (s + 1) ζ -
        (a * 𝔼.E (s + 1) (pstar (s + 1 + 1) - p (s + 1 + 1)) ζ +
          (-(1 - a) * mu (s + 1) ζ + a * (𝔼.E (s + 1) (infl (s + 2)) ζ - ω * infl (s + 1) ζ))))
        = 0 := by
      rw [ha_def]
      linear_combination key - f5s + β * θ * f7
    rcases mul_eq_zero.1 hT with h | h
    · exact absurd h h1θ
    · linarith
  have hb₁ : BoundedProc z₁ := by
    refine ⟨θ / (1 - θ) * (2 * M), fun s ζ => ?_⟩
    have hz : z₁ s ζ = θ / (1 - θ) * (infl (s + 1) ζ - ω * infl s ζ) := by
      simp only [hz₁, Pi.sub_apply]
      field_simp
      linear_combination -(f5 s ζ)
    rw [hz, abs_mul, abs_of_nonneg (div_nonneg hθ0.le (by linarith))]
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hθ0.le (by linarith))
    calc |infl (s + 1) ζ - ω * infl s ζ| ≤ |infl (s + 1) ζ| + |ω * infl s ζ| := abs_sub _ _
      _ ≤ M + M := by
          gcongr
          · exact hib _ ζ
          · rw [abs_mul, abs_of_nonneg hω0]
            calc ω * |infl s ζ| ≤ 1 * M := mul_le_mul hω1 (hib s ζ) (abs_nonneg _) zero_le_one
              _ = M := one_mul M
      _ = 2 * M := by ring
  have hb₂ : BoundedProc z₂ := by
    refine ⟨(1 - a) * ∑' k : ℕ, 2 * M * (((k : ℝ) + 1) * a ^ k), fun s ζ => ?_⟩
    simp only [hz₂, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - a)]
    exact mul_le_mul_of_nonneg_left (abs_Tsum_le 𝔼 ha0 ha1 hω0 hω1 hM hib hmb _ ζ)
      (by linarith)
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have heq := (shiftE 𝔼).forward_unique habs h₁ h₂ hb₁ hb₂
  have hzt := congrFun heq t
  simp only [hz₁, hz₂] at hzt
  rw [rule_eq 𝔼 ha0 ha1 hω0 hω1 hM hpa hib hmb hinfl (t + 1), ← hzt]
  abel

end Gali.BasicNewKeynesianModel.Ex3_4

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.5: optimal price setting and dynamics in the Taylor model

Galí (2015), Chapter 3, Exercise 3.5, pp. 92–93. Each period a fraction `1/N`
of firms sets a price that stays fixed for `N` periods (Taylor 1980).

* (a) `hasDerivAt_objective`, `foc_of_isLocalMax`: the first-order condition of
  the price setter, derived as an exact derivative of the `N`-period objective.
  `isMaxOn_iff_foc`: the condition is also sufficient, and it has a unique
  root, the global maximiser. The condition as printed in the book omits the
  factor `1/P_{t+k}` of the objective; `printed_foc_counterexample` shows that
  the printed condition fails at the true optimum.
* (b) `hasDerivAt_focLHS_path`, `pricing_rule_iff`: the exact linearisation of
  the first-order condition at the zero-inflation steady state gives
  `p*_t = μ + ∑ₖ ωₖ E_t ψ_{t+k}`, with weights `ωₖ = βᵏ(1−β)/(1−β^N)`
  (`taylorWeight_eq`) that sum to one (`sum_taylorWeight`) and tend to `1/N`
  as `β → 1` (`tendsto_taylorWeight`).
* (c) `hasDerivAt_log_priceIndex`: `p_t = N⁻¹ ∑ₖ p*_{t−k}` to first order.
* (d) `taylor_two_period_rule`: with `N = 2` and `β = 1`,
  `p*_t = ½ p*_{t−1} + ½ E_t p*_{t+1} + δ (ỹ_t + E_t ỹ_{t+1})`, `δ = σ + φ`.
* (e) `gap_equation`, `taylor_equilibrium`: with random-walk money and
  technology, the reset price relative to `m − yⁿ` follows an AR(1) with the
  stable root `λ = (1 − √δ)/(1 + √δ)` of a quadratic; this is the unique
  bounded solution (one predetermined variable, general lemmas
  `predetermined_solves`, `predetermined_unique`). Closed forms for the output
  gap, output, employment and the price level: `taylor_gap_closed`,
  `taylor_model_closed_form`.
* (f) `taylorRoot_strictAntiOn`: persistence `λ` is strictly *decreasing* in
  `δ`; `λ → 1` as `δ → 0` and `λ < 0` (oscillation) for `δ > 1`.

Dates are natural numbers, so equations with a lag are stated at date `t + 1`.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_5

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) The first-order condition -/

/-- The desired gross markup `M = ε/(ε − 1)` (Galí (2015), Ex. 3.5(a), p. 92). -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- The log desired markup `μ = log M` (Galí (2015), Ex. 3.5(b), p. 93). -/
noncomputable def logMarkup (ε : ℝ) : ℝ := Real.log (markup ε)

/-- The desired markup is positive for `ε > 1` (Galí (2015), p. 92). -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  div_pos (by linarith) (by linarith)

/-- `(1 − ε) M = −ε` (Galí (2015), p. 92). -/
theorem one_sub_mul_markup {ε : ℝ} (hε : 1 < ε) : (1 - ε) * markup ε = -ε := by
  unfold markup
  have : ε - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Demand for a good priced at `P*`, `Y_{t+k|t} = (P*/P_{t+k})^{−ε} C_{t+k}`
(Galí (2015), Ex. 3.5, p. 92), as a random variable. -/
noncomputable def demand (ε x : ℝ) (P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => (x / P ω) ^ (-ε) * C ω

/-- With technology `Y = A N` and a competitive wage `W`, the nominal cost of
producing `Y` is `W (Y/A)` (Galí (2015), Ex. 3.5, p. 92). -/
noncomputable def cost (W A Y : ℝ) : ℝ := W * (Y / A)

/-- The nominal marginal cost is `Ψ = W/A`, independent of the firm's output
(Galí (2015), Ex. 3.5(a), p. 92), and the cost is `Ψ Y`. -/
theorem cost_eq_and_hasDerivAt (W A Y : ℝ) :
    cost W A Y = W / A * Y ∧ HasDerivAt (fun Y' => cost W A Y') (W / A) Y := by
  refine ⟨by unfold cost; ring, ?_⟩
  have h := ((hasDerivAt_id Y).div_const A).const_mul W
  refine h.congr_deriv ?_
  simp [div_eq_mul_inv]

/-- Real profits at horizon `k` of a firm that set the price `x` at date `t`,
`Λ_{t,t+k} (1/P_{t+k}) (x Y_{t+k|t} − Ψ_{t+k} Y_{t+k|t})` (Galí (2015),
Ex. 3.5, p. 92), with the linear cost of `cost_eq_and_hasDerivAt`. -/
noncomputable def profit (ε : ℝ) (Λ P C Ψ : Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ω => Λ ω / P ω * (x * demand ε x P C ω - Ψ ω * demand ε x P C ω)

/-- **The Taylor price setter's objective** (Galí (2015), Ex. 3.5, p. 92):
`∑_{k<N} E_t[Λ_{t,t+k}(1/P_{t+k})(P* Y_{t+k|t} − C_{t+k}(Y_{t+k|t}))]`. The
horizon-`k` variables `Λ k, P k, C k, Ψ k` are the date-`t+k` values. -/
noncomputable def objective (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) :
    Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N, 𝔼.E t (profit ε (Λ k) (P k) (C k) (Ψ k) x) ω

/-- The summand of the first-order condition,
`Λ_{t,t+k} (1/P_{t+k}) Y_{t+k|t} (P* − M Ψ_{t+k})` (Galí (2015), Ex. 3.5(a)). -/
noncomputable def focTerm (ε : ℝ) (Λ P C Ψ : Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ω => Λ ω / P ω * demand ε x P C ω * (x - markup ε * Ψ ω)

/-- The left-hand side of the first-order condition (Galí (2015), Ex. 3.5(a)):
`∑_{k<N} E_t[Λ_{t,t+k} (1/P_{t+k}) Y_{t+k|t} (P* − M Ψ_{t+k})]`. -/
noncomputable def focSum (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N, 𝔼.E t (focTerm ε (Λ k) (P k) (C k) (Ψ k) x) ω

/-- The demand weight `Λ P^{ε−1} C`, so that `Λ (1/P) Y = x^{−ε} · Λ P^{ε−1} C`
(Galí (2015), Ex. 3.5, p. 92). -/
noncomputable def wgt (ε : ℝ) (Λ P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => Λ ω / P ω * (P ω ^ ε * C ω)

/-- Demand factorises as `x^{−ε} P^ε C` (Galí (2015), Ex. 3.5, p. 92). -/
theorem demand_eq {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    demand ε x P C ω = x ^ (-ε) * (P ω ^ ε * C ω) := by
  unfold demand
  rw [Real.div_rpow hx.le (hP ω).le, Real.rpow_neg (hP ω).le ε, div_inv_eq_mul]
  ring

/-- Expected profits in closed form: `E_t[profit] = x^{−ε} x E_t[w] − x^{−ε} E_t[w Ψ]`
for the weight `w = Λ P^{ε−1} C` (Galí (2015), Ex. 3.5, p. 92). -/
theorem E_profit_eq {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (t : ℕ) (ω : Ω) :
    𝔼.E t (profit ε Λ P C Ψ x) ω
      = x ^ (-ε) * x * 𝔼.E t (wgt ε Λ P C) ω - x ^ (-ε) * 𝔼.E t (wgt ε Λ P C * Ψ) ω := by
  have h : profit ε Λ P C Ψ x
      = (x ^ (-ε) * x) • wgt ε Λ P C - x ^ (-ε) • (wgt ε Λ P C * Ψ) := by
    funext ω'
    simp only [profit, wgt, demand_eq hx hP, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]
    ring
  rw [h, map_sub, map_smul, map_smul]
  rfl

/-- The first-order term in closed form:
`E_t[focTerm] = x^{−ε} x E_t[w] − x^{−ε} M E_t[w Ψ]` (Galí (2015), Ex. 3.5(a)). -/
theorem E_focTerm_eq {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (t : ℕ) (ω : Ω) :
    𝔼.E t (focTerm ε Λ P C Ψ x) ω = x ^ (-ε) * x * 𝔼.E t (wgt ε Λ P C) ω
      - x ^ (-ε) * markup ε * 𝔼.E t (wgt ε Λ P C * Ψ) ω := by
  have h : focTerm ε Λ P C Ψ x
      = (x ^ (-ε) * x) • wgt ε Λ P C - (x ^ (-ε) * markup ε) • (wgt ε Λ P C * Ψ) := by
    funext ω'
    simp only [focTerm, wgt, demand_eq hx hP, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]
    ring
  rw [h, map_sub, map_smul, map_smul]
  rfl

/-- The derivative of `z ↦ z^{−ε} z a − z^{−ε} b` at `x > 0` equals
`((1 − ε)/x)(x^{−ε} x a − x^{−ε} M b)` (Galí (2015), Ex. 3.5(a)). -/
theorem hasDerivAt_closedForm {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) (a b : ℝ) :
    HasDerivAt (fun z => z ^ (-ε) * z * a - z ^ (-ε) * b)
      ((1 - ε) / x * (x ^ (-ε) * x * a - x ^ (-ε) * markup ε * b)) x := by
  have hr := Real.hasDerivAt_rpow_const (p := -ε) (Or.inl hx.ne')
  have h := HasDerivAt.sub (((hr.mul (hasDerivAt_id x)).mul_const a)) (hr.mul_const b)
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hx.ne']
  unfold markup
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : x ≠ 0 := hx.ne'
  simp only [id]
  field_simp
  ring

/-- **The derivative of the Taylor objective** (Galí (2015), Ex. 3.5(a), p. 92):
at every price `x > 0`, the objective has derivative
`((1 − ε)/x) ∑_{k<N} E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k|t}(x − M Ψ_{t+k})]`. -/
theorem hasDerivAt_objective {N : ℕ} {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x)
    {Λ P C Ψ : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => objective 𝔼 N ε Λ P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 N ε Λ P C Ψ t x ω) x := by
  unfold objective focSum
  rw [Finset.mul_sum]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := hasDerivAt_closedForm hε hx (𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
    (𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω)
  rw [E_focTerm_eq 𝔼 hx (hP k)]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with z hz
  exact E_profit_eq 𝔼 hz (hP k) t ω

/-- **The first-order condition is necessary** (Galí (2015), Ex. 3.5(a), p. 92):
a locally optimal reset price `P* > 0` satisfies
`∑_{k<N} E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k|t}(P* − M Ψ_{t+k})] = 0`. -/
theorem foc_of_isLocalMax {N : ℕ} {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x)
    {Λ P C Ψ : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω) {t : ℕ} {ω : Ω}
    (hmax : IsLocalMax (fun z => objective 𝔼 N ε Λ P C Ψ t z ω) x) :
    focSum 𝔼 N ε Λ P C Ψ t x ω = 0 := by
  have h := hmax.hasDerivAt_eq_zero (hasDerivAt_objective 𝔼 hε hx hP t ω)
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- The objective in closed form: `x^{−ε} x A − x^{−ε} B` with
`A = ∑ E_t[wₖ]`, `B = ∑ E_t[wₖ Ψₖ]` (Galí (2015), Ex. 3.5(a)). -/
theorem objective_eq {N : ℕ} {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) (t : ℕ) (ω : Ω) :
    objective 𝔼 N ε Λ P C Ψ t x ω
      = x ^ (-ε) * x * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
        - x ^ (-ε) * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω) := by
  unfold objective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => E_profit_eq 𝔼 hx (hP k) t ω

/-- The first-order sum in closed form: `x^{−ε}(x A − M B)` (Galí (2015), Ex. 3.5(a)). -/
theorem focSum_eq {N : ℕ} {ε x : ℝ} (hx : 0 < x) {Λ P C Ψ : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) (t : ℕ) (ω : Ω) :
    focSum 𝔼 N ε Λ P C Ψ t x ω
      = x ^ (-ε) * (x * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
        - markup ε * (∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω)) := by
  unfold focSum
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [E_focTerm_eq 𝔼 hx (hP k) t ω]
  ring

/-- **The first-order condition is also sufficient, and has a unique root**
(Galí (2015), Ex. 3.5(a), p. 92). If the expected demand weights and the
expected weighted marginal costs are positive, then a price `x > 0` maximises
the objective over all positive prices if and only if it satisfies the
first-order condition. The proof is Bernoulli's inequality
`u^ε ≥ 1 + ε (u − 1)`. -/
theorem isMaxOn_iff_foc {N : ℕ} {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x)
    {Λ P C Ψ : ℕ → Ω → ℝ} (hP : ∀ k ω, 0 < P k ω) {t : ℕ} {ω : Ω}
    (hA : 0 < ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω)
    (hB : 0 < ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω) :
    IsMaxOn (fun z => objective 𝔼 N ε Λ P C Ψ t z ω) (Set.Ioi 0) x ↔
      focSum 𝔼 N ε Λ P C Ψ t x ω = 0 := by
  set A := ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k)) ω with hAdef
  set B := ∑ k ∈ Finset.range N, 𝔼.E t (wgt ε (Λ k) (P k) (C k) * Ψ k) ω with hBdef
  have hM := markup_pos hε
  set xs := markup ε * B / A with hxs
  have hxs0 : 0 < xs := by positivity
  -- the objective at `xs u`, relative to its value at `xs`
  have key : ∀ u, 0 < u → objective 𝔼 N ε Λ P C Ψ t (xs * u) ω
      = xs ^ (-ε) * xs * A * (u ^ (-ε) * (u - (ε - 1) / ε)) := by
    intro u hu
    rw [objective_eq 𝔼 (by positivity) hP, Real.mul_rpow hxs0.le hu.le]
    have hB' : B = xs * A * ((ε - 1) / ε) := by
      rw [hxs]; unfold markup
      have : ε - 1 ≠ 0 := by linarith
      have : ε ≠ 0 := by linarith
      field_simp
    rw [← hAdef, ← hBdef, hB']
    ring
  have hbern : ∀ u, 0 < u → u ^ (-ε) * (u - (ε - 1) / ε) ≤ 1 / ε := by
    intro u hu
    have hb := one_add_mul_self_le_rpow_one_add (s := u - 1) (by linarith) hε.le
    rw [add_sub_cancel] at hb
    have hue : 0 < u ^ ε := Real.rpow_pos_of_pos hu ε
    rw [Real.rpow_neg hu.le, ← div_eq_inv_mul, div_le_div_iff₀ hue (by linarith)]
    have hε0 : 0 < ε := by linarith
    rw [div_eq_mul_inv]
    have : (u - (ε - 1) * ε⁻¹) * ε = ε * u - (ε - 1) := by field_simp
    nlinarith [this]
  have hbern' : ∀ u, 0 < u → u ≠ 1 → u ^ (-ε) * (u - (ε - 1) / ε) < 1 / ε := by
    intro u hu hu1
    have hb := one_add_mul_self_lt_rpow_one_add (s := u - 1) (by linarith)
      (sub_ne_zero.mpr hu1) hε
    rw [add_sub_cancel] at hb
    have hue : 0 < u ^ ε := Real.rpow_pos_of_pos hu ε
    rw [Real.rpow_neg hu.le, ← div_eq_inv_mul, div_lt_div_iff₀ hue (by linarith)]
    have : (u - (ε - 1) / ε) * ε = ε * u - (ε - 1) := by field_simp
    nlinarith [this]
  have hfoc : focSum 𝔼 N ε Λ P C Ψ t x ω = 0 ↔ x = xs := by
    rw [focSum_eq 𝔼 hx hP, ← hAdef, ← hBdef]
    have hxe : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx _
    constructor
    · intro h
      have := (mul_eq_zero.mp h).resolve_left hxe.ne'
      rw [hxs]; field_simp; linarith
    · intro h
      rw [h, hxs]; field_simp; ring
  rw [hfoc]
  have hc0 : 0 < xs ^ (-ε) * xs * A := by positivity
  have hval1 : objective 𝔼 N ε Λ P C Ψ t xs ω = xs ^ (-ε) * xs * A * (1 / ε) := by
    have := key 1 one_pos
    rw [mul_one] at this
    rw [this, Real.one_rpow, one_mul]
    have : ε ≠ 0 := by linarith
    field_simp
    ring
  constructor
  · intro hmax
    by_contra hne
    have hu : 0 < x / xs := div_pos hx hxs0
    have hu1 : x / xs ≠ 1 := fun h => hne ((div_eq_one_iff_eq hxs0.ne').mp h)
    have h1 := hmax (Set.mem_Ioi.mpr hxs0)
    have h2 := key (x / xs) hu
    rw [mul_div_cancel₀ x hxs0.ne'] at h2
    change objective 𝔼 N ε Λ P C Ψ t xs ω ≤ objective 𝔼 N ε Λ P C Ψ t x ω at h1
    rw [h2, hval1] at h1
    have := hbern' _ hu hu1
    nlinarith
  · intro h z hz
    rw [h]
    have hz0 : 0 < z := hz
    have h2 := key (z / xs) (div_pos hz0 hxs0)
    rw [mul_div_cancel₀ z hxs0.ne'] at h2
    change objective 𝔼 N ε Λ P C Ψ t z ω ≤ objective 𝔼 N ε Λ P C Ψ t xs ω
    rw [h2, hval1]
    exact mul_le_mul_of_nonneg_left (hbern _ (div_pos hz0 hxs0)) hc0.le

/-- The first-order condition **as printed** (Galí (2015), Ex. 3.5(a), p. 92):
`∑_{k<N} E_t[Λ_{t,t+k} Y_{t+k|t}(P* − M Ψ_{t+k})] = 0`, without the factor
`1/P_{t+k}` that the objective carries. -/
noncomputable def printedFocSum (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) :
    Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N,
    𝔼.E t (fun ω' => Λ k ω' * demand ε x (P k) (C k) ω' * (x - markup ε * Ψ k ω')) ω

/-- **The printed condition is not the first-order condition** (Galí (2015),
Ex. 3.5(a), p. 92). Under perfect foresight with `N = 2`, `ε = 2`, `Λ ≡ 1`,
`C ≡ 1`, `P = (1, 2)` and `Ψ = (1, 2)`, the objective is maximised at
`P* = 10/3`, where the correct condition holds but the printed one does not
(it would give `P* = 18/5`). The two conditions agree to first order around a
zero-inflation steady state (`hasDerivAt_focLHS_path` allows any weights). -/
theorem printed_foc_counterexample :
    let P : ℕ → Unit → ℝ := fun k _ => (k : ℝ) + 1
    let Ψ : ℕ → Unit → ℝ := fun k _ => (k : ℝ) + 1
    IsMaxOn (fun z => objective perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 z ())
        (Set.Ioi 0) (10 / 3) ∧
      focSum perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 (10 / 3) () = 0 ∧
      printedFocSum perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 (10 / 3) () ≠ 0 := by
  intro P Ψ
  have hP : ∀ k ω, 0 < P k ω := fun k _ => by positivity
  have hfoc : focSum perfectForesight 2 2 (fun _ _ => 1) P (fun _ _ => 1) Ψ 0 (10 / 3) () = 0 := by
    simp only [focSum, focTerm, demand, perfectForesight, LinearMap.id_apply, markup,
      Finset.sum_range_succ, Finset.sum_range_zero, P, Ψ]
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num]
    simp only [Real.rpow_intCast]
    norm_num
  refine ⟨?_, hfoc, ?_⟩
  · refine (isMaxOn_iff_foc perfectForesight (by norm_num) (by norm_num) hP ?_ ?_).mpr hfoc
    · simp only [wgt, perfectForesight, LinearMap.id_apply, Finset.sum_range_succ,
        Finset.sum_range_zero, P]
      positivity
    · simp only [wgt, perfectForesight, LinearMap.id_apply, Finset.sum_range_succ,
        Finset.sum_range_zero, P, Ψ, Pi.mul_apply]
      positivity
  · simp only [printedFocSum, demand, perfectForesight, LinearMap.id_apply, markup,
      Finset.sum_range_succ, Finset.sum_range_zero, P, Ψ]
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num]
    simp only [Real.rpow_intCast]
    norm_num

/-! ### (b) The log-linear pricing rule -/

/-- **Differentiation under `E_t`.** If the second-order remainder of `z ↦ g z`
at `x` is bounded by `C h²` uniformly in the state, then `z ↦ E_t[g z]` has
derivative `E_t[g']` at `x`. A local copy of the argument used for eq. (10) of
Galí (2015), p. 56; needed for the linearisation in Ex. 3.5(b). -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Differentiating `E_t[exp(s g)]` in `s` for a bounded random variable `g`:
the derivative is `E_t[g exp(s g)]` (Galí (2015), Ex. 3.5(b), p. 93). -/
theorem hasDerivAt_E_exp {g : Ω → ℝ} {B : ℝ} (hg : ∀ ω, |g ω| ≤ B) (t : ℕ) (ω : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ω' => Real.exp (r * g ω')) ω)
      (𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω) s := by
  refine hasDerivAt_E_of_remainder 𝔼 (g := fun r ω' => Real.exp (r * g ω'))
    (δ := 1 / (|B| + 1)) (C := Real.exp (|s| * |B|) * B ^ 2) (by positivity)
    (fun h hh ω' => ?_) t ω
  have hgB : |g ω'| ≤ |B| := (hg ω').trans (le_abs_self B)
  have hhB : |h| * |B| ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hh
    nlinarith [abs_nonneg B, abs_nonneg h]
  have hhg : |h * g ω'| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hgB (abs_nonneg h)).trans hhB
  have hexp := Real.abs_exp_sub_one_sub_id_le hhg
  have key : Real.exp ((s + h) * g ω') - Real.exp (s * g ω') - h * (g ω' * Real.exp (s * g ω'))
      = Real.exp (s * g ω') * (Real.exp (h * g ω') - 1 - h * g ω') := by
    rw [add_mul, Real.exp_add]; ring
  rw [key, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp (s * g ω') ≤ Real.exp (|s| * |B|) := by
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hgB (abs_nonneg s)
  have e2 : (h * g ω') ^ 2 ≤ B ^ 2 * h ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr (by simpa using hgB)) (sq_nonneg h)
  calc Real.exp (s * g ω') * |Real.exp (h * g ω') - 1 - h * g ω'|
      ≤ Real.exp (|s| * |B|) * (B ^ 2 * h ^ 2) :=
        mul_le_mul e1 (hexp.trans e2) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|s| * |B|) * B ^ 2 * h ^ 2 := by ring

/-- The first-order condition of Ex. 3.5(a) written with general weights
`wₖ` (Galí (2015), p. 92): `∑_{k<N} E_t[wₖ (P* − M Ψ_{t+k})]`. -/
noncomputable def focLHS (N : ℕ) (ε : ℝ) (w : ℕ → Ω → ℝ) (x : ℝ) (Ψ : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N, 𝔼.E t (fun ω' => w k ω' * (x - markup ε * Ψ k ω')) ω

/-- The first-order sum is `focLHS` with weights `Λ_{t,t+k} Y_{t+k|t}/P_{t+k}`
(Galí (2015), Ex. 3.5(a), p. 92). -/
theorem focSum_eq_focLHS (N : ℕ) (ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) :
    focSum 𝔼 N ε Λ P C Ψ t x
      = focLHS 𝔼 N ε (fun k ω => Λ k ω / P k ω * demand ε x (P k) (C k) ω) x Ψ t := rfl

/-- **Exact linearisation of the first-order condition** at the zero-inflation
steady state (Galí (2015), Ex. 3.5(b), p. 93). Perturb along an arbitrary
bounded direction: weights `wₖ = βᵏ w̄ exp(s ŵₖ)` (discount factor, demand and
`1/P` combined), reset price `P* = exp(p̄ + s x̂)` and marginal costs
`Ψ_{t+k} = exp(p̄ − μ + s ψ̂ₖ)`, where `p̄ = μ + ψ̄` is the steady state. The
derivative at `s = 0` is `w̄ e^{p̄} ∑_{k<N} βᵏ (x̂ − E_t ψ̂ₖ)`. -/
theorem hasDerivAt_focLHS_path {N : ℕ} {β ε wbar pbar xhat B : ℝ} (hε : 1 < ε)
    {what ψhat : ℕ → Ω → ℝ} (hw : ∀ k ω, |what k ω| ≤ B) (hψ : ∀ k ω, |ψhat k ω| ≤ B)
    (hxB : |xhat| ≤ B) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focLHS 𝔼 N ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      (wbar * Real.exp pbar * ∑ k ∈ Finset.range N, β ^ k * (xhat - 𝔼.E t (ψhat k) ω)) 0 := by
  set c := wbar * Real.exp pbar with hc
  set a : ℕ → Ω → ℝ := fun k ω' => what k ω' + xhat with ha
  set b : ℕ → Ω → ℝ := fun k ω' => what k ω' + ψhat k ω' with hb
  have haB : ∀ k ω', |a k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω'])
  have hbB : ∀ k ω', |b k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω', hψ k ω'])
  have hfun : (fun s => focLHS 𝔼 N ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      = fun s => ∑ k ∈ Finset.range N, β ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)) := by
    funext s
    unfold focLHS
    refine Finset.sum_congr rfl fun k _ => ?_
    have hint : (fun ω' => β ^ k * wbar * Real.exp (s * what k ω') *
          (Real.exp (pbar + s * xhat)
            - markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')))
        = (β ^ k * c) • ((fun ω' => Real.exp (s * a k ω'))
            - fun ω' => Real.exp (s * b k ω')) := by
      funext ω'
      have hM : markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')
          = Real.exp (pbar + s * ψhat k ω') := by
        rw [logMarkup, show pbar - Real.log (markup ε) + s * ψhat k ω'
            = (pbar + s * ψhat k ω') + -Real.log (markup ε) by ring, Real.exp_add,
          Real.exp_neg, Real.exp_log (markup_pos hε)]
        have := (markup_pos hε).ne'
        field_simp
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hM]
      simp only [ha, hb, hc, mul_add, Real.exp_add]
      ring
    rw [hint, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hfun, Finset.mul_sum]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := ((HasDerivAt.sub (hasDerivAt_E_exp 𝔼 (haB k) t ω 0)
    (hasDerivAt_E_exp 𝔼 (hbB k) t ω 0)).const_mul c).const_mul (β ^ k)
  refine h.congr_deriv ?_
  have hab : (fun ω' => a k ω' * Real.exp (0 * a k ω'))
      - (fun ω' => b k ω' * Real.exp (0 * b k ω')) = (fun _ => xhat) - ψhat k := by
    funext ω'; simp [ha, hb]
  rw [← Pi.sub_apply (𝔼.E t _), ← map_sub, hab, map_sub, 𝔼.const]
  simp only [Pi.sub_apply]
  ring

/-- The Taylor weights `ωₖ = βᵏ / ∑_{j<N} βʲ` (Galí (2015), Ex. 3.5(b), p. 93),
written so that they are defined at `β = 1` too. -/
noncomputable def taylorWeight (β : ℝ) (N k : ℕ) : ℝ := β ^ k / ∑ j ∈ Finset.range N, β ^ j

/-- `∑_{j<N} βʲ ≥ 1` for `β ≥ 0` and `N ≥ 1` (Galí (2015), Ex. 3.5(b)). -/
theorem one_le_geomSum {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N) :
    1 ≤ ∑ j ∈ Finset.range N, β ^ j := by
  have := Finset.single_le_sum (f := fun j => β ^ j) (fun j _ => pow_nonneg hβ j)
    (Finset.mem_range.mpr hN)
  simpa using this

/-- **The book's weights** (Galí (2015), Ex. 3.5(b), p. 93): for `β ≠ 1`,
`ωₖ = βᵏ(1 − β)/(1 − β^N)`. -/
theorem taylorWeight_eq {β : ℝ} (hβ : β ≠ 1) (N k : ℕ) :
    taylorWeight β N k = β ^ k * (1 - β) / (1 - β ^ N) := by
  unfold taylorWeight
  rw [geom_sum_eq hβ, div_div_eq_mul_div, ← neg_div_neg_eq]
  ring_nf

/-- **The weights sum to one** (Galí (2015), Ex. 3.5(b), p. 93). -/
theorem sum_taylorWeight {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range N, taylorWeight β N k = 1 := by
  unfold taylorWeight
  rw [← Finset.sum_div, div_self (by linarith [one_le_geomSum hβ hN])]

/-- The weights are positive (Galí (2015), Ex. 3.5(b)). -/
theorem taylorWeight_pos {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 < taylorWeight β N k :=
  div_pos (pow_pos hβ k) (by linarith [one_le_geomSum hβ.le hN])

/-- Without discounting the weights are `1/N` (Galí (2015), Ex. 3.5(b), p. 93). -/
theorem taylorWeight_one (N k : ℕ) : taylorWeight 1 N k = 1 / N := by
  simp [taylorWeight]

/-- **The limit `β → 1`** (Galí (2015), Ex. 3.5(b), p. 93): the book's weights
`βᵏ(1 − β)/(1 − β^N)` tend to `1/N` as `β → 1`. -/
theorem tendsto_taylorWeight {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Tendsto (fun β : ℝ => β ^ k * (1 - β) / (1 - β ^ N)) (𝓝[≠] 1) (𝓝 (1 / N)) := by
  have hS : (∑ j ∈ Finset.range N, (1 : ℝ) ^ j) ≠ 0 := by
    have := one_le_geomSum (le_refl (0 : ℝ) |>.trans zero_le_one) hN
    linarith
  have hcont : ContinuousAt (fun β : ℝ => taylorWeight β N k) 1 := by
    unfold taylorWeight
    exact ContinuousAt.div (by fun_prop) (by fun_prop) hS
  have h1 := hcont.tendsto
  rw [taylorWeight_one] at h1
  refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  exact taylorWeight_eq hβ N k

/-- **The log-linear pricing rule** (Galí (2015), Ex. 3.5(b), p. 93). The
first-order term of the first-order condition vanishes if and only if
`p*_t = μ + ∑_{k<N} ωₖ E_t ψ_{t+k}`, where `p*_t = p̄ + x̂` and
`ψ_{t+k} = (p̄ − μ) + ψ̂ₖ`. -/
theorem pricing_rule_iff {N : ℕ} (hN : 0 < N) {β ε wbar pbar xhat : ℝ} (hβ : 0 ≤ β)
    (hwbar : 0 < wbar) (ψhat : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑ k ∈ Finset.range N, β ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup ε + ∑ k ∈ Finset.range N,
        taylorWeight β N k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω := by
  set S := ∑ j ∈ Finset.range N, β ^ j with hS
  have hS1 : 1 ≤ S := one_le_geomSum hβ hN
  set T := ∑ k ∈ Finset.range N, β ^ k * 𝔼.E t (ψhat k) ω with hT
  have h1 : ∑ k ∈ Finset.range N, β ^ k * (xhat - 𝔼.E t (ψhat k) ω) = S * xhat - T := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hE : ∀ k, 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
      = (pbar - logMarkup ε) + 𝔼.E t (ψhat k) ω := by
    intro k
    have hf : (fun ω' => (pbar - logMarkup ε) + ψhat k ω')
        = (fun _ => pbar - logMarkup ε) + ψhat k := rfl
    rw [hf, map_add, 𝔼.const]; rfl
  have h2 : ∑ k ∈ Finset.range N,
      taylorWeight β N k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
      = (S * (pbar - logMarkup ε) + T) / S := by
    simp_rw [hE]
    unfold taylorWeight
    rw [← hS]
    calc ∑ k ∈ Finset.range N, β ^ k / S * (pbar - logMarkup ε + 𝔼.E t (ψhat k) ω)
        = (∑ k ∈ Finset.range N, β ^ k * (pbar - logMarkup ε + 𝔼.E t (ψhat k) ω)) / S := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = (S * (pbar - logMarkup ε) + T) / S := by
          congr 1
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [h1, h2]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  have hS0 : S ≠ 0 := by linarith
  constructor
  · intro h
    have h3 := (mul_eq_zero.mp h).resolve_left hc
    field_simp
    linarith
  · intro h
    have h3 : S * xhat - T = 0 := by
      field_simp at h
      linarith
    rw [h3, mul_zero]

/-- **The pricing rule without discounting** (Galí (2015), Ex. 3.5(b), p. 93):
with `β = 1`, `p*_t = μ + N⁻¹ ∑_{k<N} E_t ψ_{t+k}`. -/
theorem pricing_rule_iff_undiscounted {N : ℕ} (hN : 0 < N) {ε wbar pbar xhat : ℝ}
    (hwbar : 0 < wbar) (ψhat : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑ k ∈ Finset.range N, (1 : ℝ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup ε + 1 / N * ∑ k ∈ Finset.range N,
        𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω := by
  rw [pricing_rule_iff 𝔼 hN (ε := ε) zero_le_one hwbar ψhat t ω, Finset.mul_sum]
  simp only [taylorWeight_one]

/-! ### (c) The price level -/

/-- The aggregate price index of the Taylor model (Galí (2015), Ex. 3.5(c),
p. 93): a share `1/N` of firms charges each of the last `N` reset prices,
so `P_t = (N⁻¹ ∑_{k<N} (P*_{t−k})^{1−ε})^{1/(1−ε)}`; `Pstar k` is `P*_{t−k}`. -/
noncomputable def priceIndex (ε : ℝ) (N : ℕ) (Pstar : ℕ → ℝ) : ℝ :=
  ((1 / N) * ∑ k ∈ Finset.range N, Pstar k ^ (1 - ε)) ^ (1 / (1 - ε))

/-- The log price index along a path of reset prices `P*_{t−k} = exp(p̄ + s x̂ₖ)`
(Galí (2015), Ex. 3.5(c)). -/
theorem log_priceIndex_path {ε : ℝ} {N : ℕ} (hN : 0 < N) (pbar : ℝ) (xhat : ℕ → ℝ) (s : ℝ) :
    Real.log (priceIndex ε N (fun k => Real.exp (pbar + s * xhat k)))
      = 1 / (1 - ε) * Real.log ((1 / N) * ∑ k ∈ Finset.range N,
          Real.exp ((pbar + s * xhat k) * (1 - ε))) := by
  unfold priceIndex
  simp_rw [← Real.exp_mul]
  have hpos : 0 < (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, Real.exp ((pbar + s * xhat k) * (1 - ε)) :=
    mul_pos (by positivity) (Finset.sum_pos (fun k _ => Real.exp_pos _)
      (Finset.nonempty_range_iff.mpr hN.ne'))
  rw [Real.log_rpow hpos]

/-- At the zero-inflation steady state all reset prices equal `P = e^{p̄}` and
the price level is `p̄` (Galí (2015), Ex. 3.5(c)). -/
theorem log_priceIndex_steady {ε : ℝ} (hε : ε ≠ 1) {N : ℕ} (hN : 0 < N) (pbar : ℝ) :
    Real.log (priceIndex ε N (fun _ => Real.exp pbar)) = pbar := by
  have h := log_priceIndex_path (ε := ε) hN pbar (fun _ => 0) 0
  simp only [mul_zero, add_zero] at h
  rw [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    one_div_mul_cancel (by exact_mod_cast hN.ne'), one_mul, Real.log_exp]
  have : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  field_simp

/-- **The price level is the average of the last `N` reset prices**
(Galí (2015), Ex. 3.5(c), p. 93): along any path `p*_{t−k} = p̄ + s x̂ₖ`, the
derivative of the log price level at the zero-inflation steady state is
`N⁻¹ ∑_{k<N} x̂ₖ`; that is, `p_t = N⁻¹ ∑_{k<N} p*_{t−k}` to first order. -/
theorem hasDerivAt_log_priceIndex {ε : ℝ} (hε : ε ≠ 1) {N : ℕ} (hN : 0 < N) (pbar : ℝ)
    (xhat : ℕ → ℝ) :
    HasDerivAt (fun s => Real.log (priceIndex ε N (fun k => Real.exp (pbar + s * xhat k))))
      (1 / N * ∑ k ∈ Finset.range N, xhat k) 0 := by
  have hfun := funext (log_priceIndex_path (ε := ε) hN pbar xhat)
  rw [hfun]
  have hε' : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  have hk : ∀ k ∈ Finset.range N, HasDerivAt (fun s => Real.exp ((pbar + s * xhat k) * (1 - ε)))
      (Real.exp ((pbar + 0 * xhat k) * (1 - ε)) * (xhat k * (1 - ε))) 0 := by
    intro k _
    have h1 : HasDerivAt (fun s : ℝ => (pbar + s * xhat k) * (1 - ε)) (xhat k * (1 - ε)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (xhat k)).const_add pbar).mul_const
        (1 - ε)
    exact h1.exp
  have hg := (HasDerivAt.fun_sum hk).const_mul (1 / (N : ℝ))
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hval : (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, Real.exp ((pbar + 0 * xhat k) * (1 - ε))
      = Real.exp (pbar * (1 - ε)) := by
    simp only [zero_mul, add_zero]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, one_div_mul_cancel hN',
      one_mul]
  have hl := (hg.log (by rw [hval]; exact (Real.exp_pos _).ne')).const_mul (1 / (1 - ε))
  refine hl.congr_deriv ?_
  rw [hval]
  simp only [zero_mul, add_zero]
  have hsum : ∑ k ∈ Finset.range N, Real.exp (pbar * (1 - ε)) * (xhat k * (1 - ε))
      = Real.exp (pbar * (1 - ε)) * (1 - ε) * ∑ k ∈ Finset.range N, xhat k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  have := (Real.exp_pos (pbar * (1 - ε))).ne'
  field_simp

/-! ### (d) Two-period contracts without discounting -/

/-- **Natural output in levels** (Galí (2015), Ex. 3.5(d), p. 93): with flexible
prices `P = M W/A`, labour supply `W/P = C^σ N^φ`, `C = Y` and `Y = A N`,
`log Y = ((1 + φ) log A − μ)/(σ + φ)` exactly. -/
theorem natural_output_levels {σ φ ε P W A C Y Nl : ℝ} (hε : 1 < ε) (hδ : 0 < σ + φ)
    (hP : 0 < P) (hA : 0 < A) (hN : 0 < Nl) (hflex : P = markup ε * (W / A))
    (hls : W / P = C ^ σ * Nl ^ φ) (hc : C = Y) (hy : Y = A * Nl) :
    Real.log Y = ((1 + φ) * Real.log A - logMarkup ε) / (σ + φ) := by
  have hM := markup_pos hε
  have hWA : 0 < W / A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hA
    rwa [div_mul_cancel₀ W hA.ne'] at this
  have hW : W / P = A / markup ε := by
    rw [hflex]; field_simp
  rw [hW, hc, hy] at hls
  have hY : 0 < A * Nl := mul_pos hA hN
  have h1 := congrArg Real.log hls
  rw [Real.log_div hA.ne' hM.ne', Real.log_mul (Real.rpow_pos_of_pos hY σ).ne'
    (Real.rpow_pos_of_pos hN φ).ne', Real.log_rpow hY, Real.log_rpow hN,
    Real.log_mul hA.ne' hN.ne'] at h1
  rw [hy, Real.log_mul hA.ne' hN.ne', eq_div_iff hδ.ne']
  unfold logMarkup
  linear_combination (-1 : ℝ) * h1

/-- **Natural output in logs** (Galí (2015), Ex. 3.5(d), p. 93): with flexible
prices `p = μ + ψ`, `ψ = w − a`, labour supply `w − p = σ c + φ n`, `c = y` and
`n = y − a`, natural output is `yⁿ = ((1 + φ) a − μ)/(σ + φ)`. -/
theorem natural_output {σ φ μ p w a y n c : ℝ} (hδ : σ + φ ≠ 0) (hflex : p = μ + (w - a))
    (hls : w - p = σ * c + φ * n) (hc : c = y) (hn : n = y - a) :
    y = ((1 + φ) * a - μ) / (σ + φ) := by
  rw [eq_div_iff hδ]
  subst hc hn
  linear_combination (-1 : ℝ) * hls + (-1 : ℝ) * hflex

/-- Nominal marginal cost in terms of the output gap (Galí (2015), Ex. 3.5(d)):
`ψ_t = p_t + δ ỹ_t − μ` with `δ = σ + φ`. -/
theorem psi_eq_gap {σ φ μ : ℝ} (hδ : σ + φ ≠ 0) {p ψ w a c y n yn ytil : Ω → ℝ}
    (hψ : ψ = w - a) (hls : w - p = σ • c + φ • n) (hc : c = y) (hn : n = y - a)
    (hyn : yn = (σ + φ)⁻¹ • ((1 + φ) • a - fun _ => μ)) (hgap : ytil = y - yn) :
    ψ = p + (σ + φ) • ytil - fun _ => μ := by
  funext ω
  have h1 := congrFun hψ ω
  have h2 := congrFun hls ω
  have h3 := congrFun hc ω
  have h4 := congrFun hn ω
  have h5 := congrFun hyn ω
  have h6 := congrFun hgap ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5 h6 ⊢
  have h5' : (σ + φ) * yn ω = (1 + φ) * a ω - μ := by
    rw [h5]; field_simp
  linear_combination h1 + h2 + σ * h3 + φ * h4 - (σ + φ) * h6 + h5'

/-- **The two-period Taylor pricing equation** (Galí (2015), Ex. 3.5(d), p. 93).
With `N = 2` and `β = 1` the rule of (b) is `p*_t = μ + ½(E_t ψ_t + E_t ψ_{t+1})`
and the price level is `p_t = ½(p*_t + p*_{t−1})` by (c). With labour supply
`w − p = σ c + φ n`, `c = y`, `n = y − a`, `ψ = w − a`, natural output from
`natural_output`, and adapted `p*` and `ψ`:
`p*_t = ½ p*_{t−1} + ½ E_t p*_{t+1} + δ (ỹ_t + E_t ỹ_{t+1})`, `δ = σ + φ`
(stated at date `t + 1`). -/
theorem taylor_two_period_rule {σ φ μ : ℝ} (hδ : σ + φ ≠ 0)
    {pstar p ψ w a c y n yn ytil : ℕ → Ω → ℝ}
    (hrule : ∀ t, pstar t = (fun _ => μ) + (1 / 2 : ℝ) • (𝔼.E t (ψ t) + 𝔼.E t (ψ (t + 1))))
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hψ : ∀ t, ψ t = w t - a t) (hls : ∀ t, w t - p t = σ • c t + φ • n t)
    (hc : ∀ t, c t = y t) (hn : ∀ t, n t = y t - a t)
    (hyn : ∀ t, yn t = (σ + φ)⁻¹ • ((1 + φ) • a t - fun _ => μ))
    (hgap : ∀ t, ytil t = y t - yn t) (hpa : 𝔼.Adapted pstar) (hψa : 𝔼.Adapted ψ) (t : ℕ) :
    pstar (t + 1) = (1 / 2 : ℝ) • pstar t + (1 / 2 : ℝ) • 𝔼.E (t + 1) (pstar (t + 2))
      + (σ + φ) • (ytil (t + 1) + 𝔼.E (t + 1) (ytil (t + 2))) := by
  have hψ' : ∀ s, ψ s = p s + (σ + φ) • ytil s - fun _ => μ := fun s =>
    psi_eq_gap hδ (hψ s) (hls s) (hc s) (hn s) (hyn s) (hgap s)
  have hEψ2 : 𝔼.E (t + 1) (ψ (t + 2))
      = 𝔼.E (t + 1) (p (t + 2)) + (σ + φ) • 𝔼.E (t + 1) (ytil (t + 2)) - fun _ => μ := by
    rw [hψ' (t + 2), map_sub, map_add, map_smul, 𝔼.const]
  have hEp2 : 𝔼.E (t + 1) (p (t + 2))
      = (1 / 2 : ℝ) • (𝔼.E (t + 1) (pstar (t + 2)) + pstar (t + 1)) := by
    rw [hindex (t + 1), map_smul, map_add, hpa (t + 1)]
  have hR := hrule (t + 1)
  rw [hψa (t + 1)] at hR
  funext ω
  have e1 := congrFun hR ω
  have e2 := congrFun (hψ' (t + 1)) ω
  have e3 := congrFun hEψ2 ω
  have e4 := congrFun hEp2 ω
  have e5 := congrFun (hindex t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 e5 ⊢
  linear_combination 2 * e1 + e2 + e3 + e5 + e4

/-! ### One predetermined variable: existence and uniqueness -/

/-- A process `q` solves the second-order expectational difference equation
`q_{t+1} = A q_t + B E_{t+1} q_{t+2} + f_{t+1}` with one predetermined variable
(Galí (2015), Ex. 3.5(e), p. 93). -/
def SolvesPre (A B : ℝ) (f q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, q (t + 1) = A • q t + B • 𝔼.E (t + 1) (q (t + 2)) + f (t + 1)

/-- The AR(1) path `q_0 = q₀`, `q_{t+1} = λ q_t + g_{t+1}` (Galí (2015),
Ex. 3.5(e)). -/
noncomputable def ar1Path (lam : ℝ) (g : ℕ → Ω → ℝ) (q0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => q0
  | t + 1 => lam • ar1Path lam g q0 t + g (t + 1)

/-- The AR(1) path is adapted (Galí (2015), Ex. 3.5(e)). -/
theorem ar1Path_adapted {lam : ℝ} {g : ℕ → Ω → ℝ} {q0 : Ω → ℝ} (hg : 𝔼.Adapted g)
    (hq0 : 𝔼.E 0 q0 = q0) : 𝔼.Adapted (ar1Path lam g q0) := by
  intro t
  induction t with
  | zero => exact hq0
  | succ t ih =>
    have h : 𝔼.E (t + 1) (ar1Path lam g q0 t) = ar1Path lam g q0 t := by
      calc 𝔼.E (t + 1) (ar1Path lam g q0 t) = 𝔼.E (t + 1) (𝔼.E t (ar1Path lam g q0 t)) := by
            rw [ih]
        _ = 𝔼.E t (ar1Path lam g q0 t) := 𝔼.known (Nat.le_succ t) _
        _ = ar1Path lam g q0 t := ih
    change 𝔼.E (t + 1) (lam • ar1Path lam g q0 t + g (t + 1))
      = lam • ar1Path lam g q0 t + g (t + 1)
    rw [map_add, map_smul, h, hg (t + 1)]

/-- The AR(1) path is bounded when `|λ| < 1` and the innovations are bounded:
`|q_t| ≤ M₀ + K/(1 − |λ|)` (Galí (2015), Ex. 3.5(e)). -/
theorem ar1Path_bounded {lam K M0 : ℝ} (hlam : |lam| < 1) {g : ℕ → Ω → ℝ}
    (hg : ∀ t ω, |g t ω| ≤ K) {q0 : Ω → ℝ} (hq0 : ∀ ω, |q0 ω| ≤ M0) (t : ℕ) (ω : Ω) :
    |ar1Path lam g q0 t ω| ≤ M0 + K / (1 - |lam|) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hg 0 ω)
  have hM : 0 ≤ M0 := (abs_nonneg _).trans (hq0 ω)
  have hl : 0 < 1 - |lam| := by linarith
  have hR : 0 ≤ K / (1 - |lam|) := div_nonneg hK hl.le
  have hRe : |lam| * (K / (1 - |lam|)) + K = K / (1 - |lam|) := by
    field_simp; ring
  induction t with
  | zero => exact (hq0 ω).trans (by linarith)
  | succ t ih =>
    change |lam * ar1Path lam g q0 t ω + g (t + 1) ω| ≤ _
    calc |lam * ar1Path lam g q0 t ω + g (t + 1) ω|
        ≤ |lam| * |ar1Path lam g q0 t ω| + K := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]
          linarith [hg (t + 1) ω]
      _ ≤ |lam| * (M0 + K / (1 - |lam|)) + K := by
          gcongr
      _ ≤ M0 + K / (1 - |lam|) := by
          have : |lam| * M0 ≤ M0 := by
            have := abs_nonneg lam
            nlinarith
          nlinarith

/-- **Existence** (Galí (2015), Ex. 3.5(e)). Let `λ` be a root of
`B λ² − λ + A = 0`, i.e. `A = λ(1 − Bλ)`, with `1 − Bλ ≠ 0`, and let the
forcing be unpredictable, `E_t f_{t+1} = 0`. Then the AR(1) path
`q_{t+1} = λ q_t + f_{t+1}/(1 − Bλ)` solves the equation. -/
theorem predetermined_solves {A B lam : ℝ} (hA : A = lam * (1 - B * lam))
    (hd : 1 - B * lam ≠ 0) {f : ℕ → Ω → ℝ} (hfa : 𝔼.Adapted f)
    (hf0 : ∀ t, 𝔼.E t (f (t + 1)) = 0) {q0 : Ω → ℝ} (hq0 : 𝔼.E 0 q0 = q0) :
    SolvesPre 𝔼 A B f (ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0) := by
  have hga : 𝔼.Adapted (fun t => (1 - B * lam)⁻¹ • f t) := fun t => by
    simp only [map_smul, hfa t]
  have hqa := ar1Path_adapted 𝔼 (lam := lam) hga hq0
  intro t
  have hE : 𝔼.E (t + 1) (ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 (t + 2))
      = lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 (t + 1) := by
    change 𝔼.E (t + 1) (lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 (t + 1)
      + (1 - B * lam)⁻¹ • f (t + 1 + 1)) = _
    rw [map_add, map_smul, map_smul, hf0 (t + 1), hqa (t + 1), smul_zero, add_zero]
  rw [hE]
  change lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 t + (1 - B * lam)⁻¹ • f (t + 1)
    = A • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 t
      + B • (lam • (lam • ar1Path lam (fun t => (1 - B * lam)⁻¹ • f t) q0 t
        + (1 - B * lam)⁻¹ • f (t + 1))) + f (t + 1)
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hA]
  have hd' : 1 - lam * B ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- **Uniqueness** (Galí (2015), Ex. 3.5(e)). With `A = λ(1 − Bλ)`,
`1 − Bλ ≠ 0` and `|B/(1 − Bλ)| < 1` (the other root `1/γ` lies outside the
unit circle), two bounded adapted solutions with the same initial value of the
predetermined variable coincide. The proof factors the equation: the
quasi-difference `q_{t+1} − λ q_t` obeys the stable forward equation
`r_t = γ E_{t+1} r_{t+1}`, so it vanishes for bounded processes. -/
theorem predetermined_unique {A B lam : ℝ} (hA : A = lam * (1 - B * lam))
    (hd : 1 - B * lam ≠ 0) (hγ : |B / (1 - B * lam)| < 1) {f q q' : ℕ → Ω → ℝ}
    (hq : SolvesPre 𝔼 A B f q) (hq' : SolvesPre 𝔼 A B f q') (ha : 𝔼.Adapted q)
    (ha' : 𝔼.Adapted q') (hb : BoundedProc q) (hb' : BoundedProc q') (h0 : q 0 = q' 0) :
    q = q' := by
  obtain ⟨M₁, hM₁⟩ := hb
  obtain ⟨M₂, hM₂⟩ := hb'
  set d : ℕ → Ω → ℝ := fun t => q t - q' t with hd_def
  have hdeq : ∀ t, d (t + 1) = A • d t + B • 𝔼.E (t + 1) (d (t + 2)) := by
    intro t
    simp only [hd_def, map_sub, smul_sub]
    rw [hq t, hq' t]; abel
  have hda : ∀ t, 𝔼.E t (d t) = d t := by
    intro t; simp only [hd_def, map_sub, ha t, ha' t]
  have hdb : ∀ t ω, |d t ω| ≤ M₁ + M₂ := fun t ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω))
  set γ := B / (1 - B * lam) with hγdef
  set r : ℕ → Ω → ℝ := fun t => d (t + 1) - lam • d t with hr_def
  have hr : ∀ t, r t = γ • 𝔼.E (t + 1) (r (t + 1)) := by
    intro t
    have e1 : 𝔼.E (t + 1) (r (t + 1)) = 𝔼.E (t + 1) (d (t + 2)) - lam • d (t + 1) := by
      simp only [hr_def, map_sub, map_smul, hda (t + 1)]
    rw [e1]
    funext ω
    have h := congrFun (hdeq t) ω
    simp only [hr_def, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h ⊢
    rw [hA] at h
    rw [hγdef, div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination h
  have hrb : ∀ t ω, |r t ω| ≤ (1 + |lam|) * (M₁ + M₂) := fun t ω => by
    simp only [hr_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    nlinarith [hdb (t + 1) ω, hdb t ω, abs_nonneg lam]
  set z : ℕ → Ω → ℝ := fun t => 𝔼.E t (r t) with hz_def
  have hz : ∀ t, z t = γ • 𝔼.E t (z (t + 1)) + 0 := by
    intro t
    simp only [hz_def, add_zero]
    conv_lhs => rw [hr t]
    rw [map_smul, 𝔼.tower (Nat.le_succ t)]
  have hz0 : ∀ t, (0 : ℕ → Ω → ℝ) t = γ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t; simp
  have hzb : BoundedProc z := ⟨(1 + |lam|) * (M₁ + M₂), fun t ω => 𝔼.abs_E_le (hrb t) t ω⟩
  have hzz := 𝔼.forward_unique hγ hz hz0 hzb ⟨0, fun t ω => by simp⟩
  have hr0 : ∀ t, r t = 0 := by
    intro t
    rw [hr t]
    have : 𝔼.E (t + 1) (r (t + 1)) = z (t + 1) := rfl
    rw [this, hzz]
    simp
  have hd0 : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero => simp [hd_def, h0]
    | succ t ih =>
      have := hr0 t
      simp only [hr_def, ih, smul_zero, sub_zero] at this
      exact this
  funext t ω
  have := congrFun (hd0 t) ω
  simpa [hd_def, sub_eq_zero] using this

/-- The AR(1) path in closed form: `q_t = λᵗ q₀ + ∑_{j<t} λʲ g_{t−j}`
(Galí (2015), Ex. 3.5(e)). -/
theorem ar1Path_closed (lam : ℝ) (g : ℕ → Ω → ℝ) (q0 : Ω → ℝ) (t : ℕ) :
    ar1Path lam g q0 t = lam ^ t • q0 + ∑ j ∈ Finset.range t, lam ^ j • g (t - j) := by
  induction t with
  | zero => simp [ar1Path]
  | succ t ih =>
    change lam • ar1Path lam g q0 t + g (t + 1) = _
    rw [ih, Finset.sum_range_succ', smul_add, smul_smul, ← pow_succ', Finset.smul_sum]
    simp only [smul_smul, ← pow_succ', pow_zero, one_smul, Nat.sub_zero]
    have : ∀ j ∈ Finset.range t,
        lam ^ (j + 1) • g (t - j) = lam ^ (j + 1) • g (t + 1 - (j + 1)) := by
      intro j _; rw [Nat.add_sub_add_right]
    rw [Finset.sum_congr rfl this]
    abel

/-! ### (e) Random-walk money and technology -/

/-- The persistence parameter of the Taylor model, `λ = (1 − √δ)/(1 + √δ)`
(Galí (2015), Ex. 3.5(e), p. 93): the stable root of `c λ² − λ + c = 0`. -/
noncomputable def taylorRoot (δ : ℝ) : ℝ := (1 - Real.sqrt δ) / (1 + Real.sqrt δ)

/-- The coefficient `c = (1 − δ)/(2(1 + δ))` of the reset-price equation
`x_t = c x_{t−1} + c E_t x_{t+1} − c Δz_t` (Galí (2015), Ex. 3.5(e)). -/
noncomputable def taylorCoeff (δ : ℝ) : ℝ := (1 - δ) / (2 * (1 + δ))

/-- `λ` solves `c λ² − λ + c = 0`, i.e. `c = λ(1 − cλ)` (Galí (2015), Ex. 3.5(e)). -/
theorem taylorCoeff_eq {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorCoeff δ = taylorRoot δ * (1 - taylorCoeff δ * taylorRoot δ) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ δ = s ^ 2 := ⟨_, Real.sqrt_nonneg δ, (Real.sq_sqrt hδ).symm⟩
  unfold taylorCoeff taylorRoot
  rw [Real.sqrt_sq hs]
  have h1 : 1 + s ≠ 0 := by positivity
  have h2 : 1 + s ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `1 − cλ = (1 + √δ)²/(2(1 + δ)) > 0` (Galí (2015), Ex. 3.5(e)). -/
theorem one_sub_taylor_pos {δ : ℝ} (hδ : 0 ≤ δ) : 0 < 1 - taylorCoeff δ * taylorRoot δ := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ δ = s ^ 2 := ⟨_, Real.sqrt_nonneg δ, (Real.sq_sqrt hδ).symm⟩
  unfold taylorCoeff taylorRoot
  rw [Real.sqrt_sq hs]
  have h : 1 - (1 - s ^ 2) / (2 * (1 + s ^ 2)) * ((1 - s) / (1 + s))
      = (1 + s) ^ 2 / (2 * (1 + s ^ 2)) := by
    have h1 : 1 + s ≠ 0 := by positivity
    have h2 : 1 + s ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [h]
  positivity

/-- `c/(1 − cλ) = λ` (Galí (2015), Ex. 3.5(e)). -/
theorem taylor_gamma {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorCoeff δ / (1 - taylorCoeff δ * taylorRoot δ) = taylorRoot δ := by
  rw [div_eq_iff (one_sub_taylor_pos hδ).ne']
  exact taylorCoeff_eq hδ

/-- `|λ| < 1` for `δ > 0` (Galí (2015), Ex. 3.5(e)). -/
theorem abs_taylorRoot_lt_one {δ : ℝ} (hδ : 0 < δ) : |taylorRoot δ| < 1 := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  unfold taylorRoot
  have h1 : 0 < 1 + Real.sqrt δ := by linarith
  rw [abs_lt, lt_div_iff₀ h1, div_lt_iff₀ h1]
  constructor <;> linarith

/-- **The reset-price equation** (Galí (2015), Ex. 3.5(e), p. 93). With money
demand `m − p = y`, the output gap is `ỹ = z − p` for `z = m − yⁿ`. If `z` is a
random walk (`E_t z_{t+1} = z_t`; true when `m` and `a` are), then
`x = p* − z` satisfies `x_t = c x_{t−1} + c E_t x_{t+1} − c Δz_t`,
`c = (1 − δ)/(2(1 + δ))`. -/
theorem gap_equation {δ : ℝ} (hδ : 0 < δ) {pstar p z ytil : ℕ → Ω → ℝ}
    (hrule2 : ∀ t, pstar (t + 1) = (1 / 2 : ℝ) • pstar t
      + (1 / 2 : ℝ) • 𝔼.E (t + 1) (pstar (t + 2)) + δ • (ytil (t + 1) + 𝔼.E (t + 1) (ytil (t + 2))))
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hgap : ∀ t, ytil t = z t - p t) (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t)
    (hpa : 𝔼.Adapted pstar) :
    SolvesPre 𝔼 (taylorCoeff δ) (taylorCoeff δ)
      (fun t => -taylorCoeff δ • (z t - z (t - 1))) (fun t => pstar t - z t) := by
  intro t
  have hEy : 𝔼.E (t + 1) (ytil (t + 2))
      = z (t + 1) - (1 / 2 : ℝ) • (𝔼.E (t + 1) (pstar (t + 2)) + pstar (t + 1)) := by
    rw [hgap (t + 2), map_sub, hzrw (t + 1), hindex (t + 1), map_smul, map_add, hpa (t + 1)]
  have hEx : 𝔼.E (t + 1) (pstar (t + 2) - z (t + 2))
      = 𝔼.E (t + 1) (pstar (t + 2)) - z (t + 1) := by
    rw [map_sub, hzrw (t + 1)]
  have hc : taylorCoeff δ * (2 * (1 + δ)) = 1 - δ := by
    unfold taylorCoeff; field_simp
  change pstar (t + 1) - z (t + 1) = taylorCoeff δ • (pstar t - z t)
    + taylorCoeff δ • 𝔼.E (t + 1) (pstar (t + 2) - z (t + 2))
    + -taylorCoeff δ • (z (t + 1) - z (t + 1 - 1))
  rw [hEx, Nat.add_sub_cancel]
  funext ω
  have e1 := congrFun (hrule2 t) ω
  have e2 := congrFun (hgap (t + 1)) ω
  have e3 := congrFun (hindex t) ω
  have e4 := congrFun hEy ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
  have h2 : (2 * (1 + δ)) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2
  linear_combination 2 * e1 + 2 * δ * e2 - 2 * δ * e3 + 2 * δ * e4
    - (pstar t ω + 𝔼.E (t + 1) (pstar (t + 2)) ω - 2 * z (t + 1) ω) * hc

/-- The equilibrium reset-price gap path `x_t = p*_t − z_t`:
`x_{t+1} = λ x_t − λ Δz_{t+1}` from `x₀` (Galí (2015), Ex. 3.5(e)). -/
noncomputable def taylorPath (δ : ℝ) (z : ℕ → Ω → ℝ) (x0 : Ω → ℝ) : ℕ → Ω → ℝ :=
  ar1Path (taylorRoot δ) (fun t => -taylorRoot δ • (z t - z (t - 1))) x0

/-- **Existence and uniqueness of the equilibrium of the Taylor model**
(Galí (2015), Ex. 3.5(e), p. 93). With `δ > 0`, a random walk `z = m − yⁿ`
with bounded innovations, and a given initial reset-price gap `x₀`, the
reset-price equation of `gap_equation` has exactly one bounded adapted solution
with `x 0 = x₀`, namely `x_{t+1} = λ x_t − λ (z_{t+1} − z_t)`, `λ = (1 − √δ)/(1 + √δ)`. -/
theorem taylor_equilibrium {δ : ℝ} (hδ : 0 < δ) {z : ℕ → Ω → ℝ} (hza : 𝔼.Adapted z)
    (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t) {K : ℝ} (hK : ∀ t ω, |z (t + 1) ω - z t ω| ≤ K)
    {x0 : Ω → ℝ} (hx0 : 𝔼.E 0 x0 = x0) {M0 : ℝ} (hM0 : ∀ ω, |x0 ω| ≤ M0) :
    (SolvesPre 𝔼 (taylorCoeff δ) (taylorCoeff δ) (fun t => -taylorCoeff δ • (z t - z (t - 1)))
        (taylorPath δ z x0) ∧ 𝔼.Adapted (taylorPath δ z x0) ∧
        BoundedProc (taylorPath δ z x0) ∧ taylorPath δ z x0 0 = x0) ∧
      ∀ x, SolvesPre 𝔼 (taylorCoeff δ) (taylorCoeff δ)
          (fun t => -taylorCoeff δ • (z t - z (t - 1))) x →
        𝔼.Adapted x → BoundedProc x → x 0 = x0 → x = taylorPath δ z x0 := by
  set c := taylorCoeff δ with hc
  set lam := taylorRoot δ with hlam
  have hA : c = lam * (1 - c * lam) := taylorCoeff_eq hδ.le
  have hd : 1 - c * lam ≠ 0 := (one_sub_taylor_pos hδ.le).ne'
  have hγ : c / (1 - c * lam) = lam := taylor_gamma hδ.le
  have hfa : 𝔼.Adapted (fun t => -c • (z t - z (t - 1))) := by
    intro t
    have : 𝔼.E t (z (t - 1)) = z (t - 1) := by
      rw [← hza (t - 1), 𝔼.known (Nat.sub_le t 1)]
    simp only [map_smul, map_sub, hza t, this]
  have hf0 : ∀ t, 𝔼.E t ((fun t => -c • (z t - z (t - 1))) (t + 1)) = 0 := by
    intro t
    simp only [Nat.add_sub_cancel, map_smul, map_sub, hzrw t, hza t, sub_self, smul_zero]
  have hg : (fun t => (1 - c * lam)⁻¹ • (fun t => -c • (z t - z (t - 1))) t)
      = fun t => -lam • (z t - z (t - 1)) := by
    funext t
    rw [smul_smul]
    congr 1
    rw [show -lam = -(c / (1 - c * lam)) by rw [hγ]]
    ring
  have hsol := predetermined_solves 𝔼 hA hd hfa hf0 (q0 := x0) hx0
  rw [hg] at hsol
  have hga : 𝔼.Adapted (fun t => -lam • (z t - z (t - 1))) := by
    intro t
    have : 𝔼.E t (z (t - 1)) = z (t - 1) := by
      rw [← hza (t - 1), 𝔼.known (Nat.sub_le t 1)]
    simp only [map_smul, map_sub, hza t, this]
  have hgb : ∀ t ω, |(fun t => -lam • (z t - z (t - 1))) t ω| ≤ K := by
    intro t ω
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ω)
    have hl := (abs_taylorRoot_lt_one hδ).le
    cases t with
    | zero => simp [hK0]
    | succ t =>
      simp only [Nat.add_sub_cancel, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg]
      calc |lam| * |z (t + 1) ω - z t ω| ≤ 1 * K :=
            mul_le_mul hl (hK t ω) (abs_nonneg _) zero_le_one
        _ = K := one_mul K
  refine ⟨⟨hsol, ar1Path_adapted 𝔼 hga hx0,
    ⟨M0 + K / (1 - |lam|), ar1Path_bounded (abs_taylorRoot_lt_one hδ) hgb hM0⟩, rfl⟩, ?_⟩
  intro x hx hxa hxb hx0'
  refine predetermined_unique 𝔼 hA hd ?_ hx hsol hxa (ar1Path_adapted 𝔼 hga hx0) hxb
    ⟨M0 + K / (1 - |lam|), ar1Path_bounded (abs_taylorRoot_lt_one hδ) hgb hM0⟩ hx0'
  rw [hγ]
  exact abs_taylorRoot_lt_one hδ

/-- The innovation `z_{t+1} − z_t` of `z = m − yⁿ` in terms of the money and
technology innovations `εᵐ`, `εᵃ` (Galí (2015), Ex. 3.5(e), p. 93):
`Δz = εᵐ − ((1 + φ)/δ) εᵃ`. -/
theorem z_innovation {σ φ μ : ℝ} {m a yn : ℕ → Ω → ℝ}
    (hyn : ∀ t, yn t = (σ + φ)⁻¹ • ((1 + φ) • a t - fun _ => μ)) (t : ℕ) (ω : Ω) :
    (m (t + 1) - yn (t + 1)) ω - (m t - yn t) ω
      = (m (t + 1) ω - m t ω) - (1 + φ) / (σ + φ) * (a (t + 1) ω - a t ω) := by
  simp only [Pi.sub_apply, hyn, Pi.smul_apply, smul_eq_mul]
  ring

/-- With random-walk money and technology, `z = m − yⁿ` is a random walk
(Galí (2015), Ex. 3.5(e), p. 93). -/
theorem z_randomWalk {σ φ μ : ℝ} {m a yn : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 1 m) (ha : 𝔼.IsAR1 1 a)
    (hyn : ∀ t, yn t = (σ + φ)⁻¹ • ((1 + φ) • a t - fun _ => μ)) :
    𝔼.Adapted (fun t => m t - yn t) ∧ ∀ t, 𝔼.E t (m (t + 1) - yn (t + 1)) = m t - yn t := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [hyn, map_sub, map_smul, 𝔼.const, hm.1 t, ha.1 t]
  · simp only [hyn, map_sub, map_smul, 𝔼.const, hm.2 t, ha.2 t, one_smul]

/-- The quasi-difference of the equilibrium path in closed form
(Galí (2015), Ex. 3.5(e)): with `vᵢ = z_{i+1} − z_i`,
`v_t − x_t = ∑_{j≤t} λʲ v_{t−j} − λᵗ x₀`. -/
theorem taylorPath_closed (δ : ℝ) (z : ℕ → Ω → ℝ) (x0 : Ω → ℝ) (t : ℕ) (ω : Ω) :
    (z (t + 1) ω - z t ω) - taylorPath δ z x0 t ω
      = ∑ j ∈ Finset.range (t + 1), taylorRoot δ ^ j * (z (t - j + 1) ω - z (t - j) ω)
        - taylorRoot δ ^ t * x0 ω := by
  set lam := taylorRoot δ with hlam
  induction t with
  | zero => simp [taylorPath, ar1Path]
  | succ t ih =>
    have hx : taylorPath δ z x0 (t + 1) ω
        = lam * taylorPath δ z x0 t ω - lam * (z (t + 1) ω - z t ω) := by
      simp only [taylorPath, ar1Path, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
        Nat.add_sub_cancel, ← hlam]
      ring
    rw [Finset.sum_range_succ']
    have hs : ∑ j ∈ Finset.range (t + 1),
        lam ^ (j + 1) * (z (t + 1 - (j + 1) + 1) ω - z (t + 1 - (j + 1)) ω)
        = lam * ∑ j ∈ Finset.range (t + 1), lam ^ j * (z (t - j + 1) ω - z (t - j) ω) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.add_sub_add_right]
      ring
    rw [hs, hx]
    simp only [Nat.sub_zero, pow_zero, one_mul]
    linear_combination lam * ih

/-- **Closed form for the output gap** (Galí (2015), Ex. 3.5(e), p. 93). Along
the equilibrium (`p*_t − z_t = x_t`), with `p_{t+1} = ½(p*_{t+1} + p*_t)` and
`ỹ = z − p`,
`ỹ_{t+1} = ((1 + λ)/2) (∑_{j≤t} λʲ v_{t−j} − λᵗ x₀)`, `vᵢ = z_{i+1} − z_i`:
an innovation in `z` moves the gap by `(1 + λ)/2` on impact, decaying at rate `λ`. -/
theorem taylor_gap_closed {δ : ℝ} {pstar p z ytil : ℕ → Ω → ℝ} {x0 : Ω → ℝ}
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hgap : ∀ t, ytil t = z t - p t) (heq : ∀ t, pstar t - z t = taylorPath δ z x0 t)
    (t : ℕ) (ω : Ω) :
    ytil (t + 1) ω = (1 + taylorRoot δ) / 2 *
      (∑ j ∈ Finset.range (t + 1), taylorRoot δ ^ j * (z (t - j + 1) ω - z (t - j) ω)
        - taylorRoot δ ^ t * x0 ω) := by
  have hc := taylorPath_closed δ z x0 t ω
  have hx : taylorPath δ z x0 (t + 1) ω
      = taylorRoot δ * taylorPath δ z x0 t ω - taylorRoot δ * (z (t + 1) ω - z t ω) := by
    simp only [taylorPath, ar1Path, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      Nat.add_sub_cancel]
    ring
  have e1 := congrFun (hgap (t + 1)) ω
  have e2 := congrFun (hindex t) ω
  have e3 := congrFun (heq (t + 1)) ω
  have e4 := congrFun (heq t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e1 e2 e3 e4
  rw [← hc]
  linear_combination e1 - e2 - (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e4 - (1 / 2 : ℝ) * hx

/-- **The Taylor model's equilibrium in closed form** (Galí (2015), Ex. 3.5(e),
p. 93). Suppose the pricing equation of (d) holds, `p_{t+1} = ½(p*_{t+1} + p*_t)`,
money demand gives `ỹ = z − p` with `z = m − yⁿ` a random walk with bounded
innovations, `p*` is adapted and `p* − z` is bounded. Then `p* − z` is the
unique equilibrium path `taylorPath` and the output gap, output `y = yⁿ + ỹ`,
employment `n = y − a` and the price level `p = m − y` are given in closed form
by the innovations `v` and the initial gap `x₀ = p*₀ − z₀`. -/
theorem taylor_model_closed_form {δ : ℝ} (hδ : 0 < δ) {pstar p z ytil yn m a n y : ℕ → Ω → ℝ}
    (hrule2 : ∀ t, pstar (t + 1) = (1 / 2 : ℝ) • pstar t
      + (1 / 2 : ℝ) • 𝔼.E (t + 1) (pstar (t + 2)) + δ • (ytil (t + 1) + 𝔼.E (t + 1) (ytil (t + 2))))
    (hindex : ∀ t, p (t + 1) = (1 / 2 : ℝ) • (pstar (t + 1) + pstar t))
    (hgap : ∀ t, ytil t = z t - p t) (hza : 𝔼.Adapted z) (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t)
    {K : ℝ} (hK : ∀ t ω, |z (t + 1) ω - z t ω| ≤ K) (hpa : 𝔼.Adapted pstar)
    (hb : BoundedProc fun t => pstar t - z t)
    (hy : ∀ t, y t = yn t + ytil t) (hn : ∀ t, n t = y t - a t) (hp : ∀ t, p t = m t - y t)
    (t : ℕ) (ω : Ω) :
    let lam := taylorRoot δ
    let gap := (1 + lam) / 2 * (∑ j ∈ Finset.range (t + 1),
        lam ^ j * (z (t - j + 1) ω - z (t - j) ω) - lam ^ t * (pstar 0 ω - z 0 ω))
    ytil (t + 1) ω = gap ∧ y (t + 1) ω = yn (t + 1) ω + gap ∧
      n (t + 1) ω = yn (t + 1) ω + gap - a (t + 1) ω ∧
      p (t + 1) ω = m (t + 1) ω - yn (t + 1) ω - gap := by
  intro lam gap
  have hx0 : 𝔼.E 0 (pstar 0 - z 0) = pstar 0 - z 0 := by rw [map_sub, hpa 0, hza 0]
  obtain ⟨M, hM⟩ := hb
  have hsol := gap_equation 𝔼 hδ hrule2 hindex hgap hzrw hpa
  have hxa : 𝔼.Adapted fun t => pstar t - z t := fun t => by simp only [map_sub, hpa t, hza t]
  have huniq := (taylor_equilibrium 𝔼 hδ hza hzrw hK hx0 (M0 := M) (hM 0)).2
    (fun t => pstar t - z t) hsol hxa ⟨M, hM⟩ rfl
  have heq : ∀ t, pstar t - z t = taylorPath δ z (pstar 0 - z 0) t := fun t => congrFun huniq t
  have hg := taylor_gap_closed hindex hgap heq t ω
  simp only [Pi.sub_apply] at hg
  refine ⟨hg, ?_, ?_, ?_⟩
  · rw [hy, Pi.add_apply, hg]
  · rw [hn, Pi.sub_apply, hy, Pi.add_apply, hg]
  · rw [hp, Pi.sub_apply, hy, Pi.add_apply, hg]; ring

/-! ### (f) Persistence and the degree of strategic complementarity -/

/-- **Persistence falls with `δ`** (Galí (2015), Ex. 3.5(f), p. 93): the
autoregressive root `λ(δ) = (1 − √δ)/(1 + √δ)` is strictly decreasing on
`[0, ∞)`. Strong strategic complementarity (small `δ`) makes the effects of a
monetary shock long-lived. -/
theorem taylorRoot_strictAntiOn : StrictAntiOn taylorRoot (Set.Ici 0) := by
  intro a ha b hb hab
  have hs := Real.sqrt_lt_sqrt (Set.mem_Ici.mp ha) hab
  have h0 := Real.sqrt_nonneg a
  unfold taylorRoot
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `λ > 0` exactly when `δ < 1` (strategic complementarity) (Galí (2015),
Ex. 3.5(f)). -/
theorem taylorRoot_pos_iff (δ : ℝ) : 0 < taylorRoot δ ↔ δ < 1 := by
  unfold taylorRoot
  have h0 := Real.sqrt_nonneg δ
  rw [div_pos_iff_of_pos_right (by positivity), sub_pos, Real.sqrt_lt' one_pos, one_pow]

/-- `λ = 0` at `δ = 1`: the effects of a monetary shock last only as long as
the contracts (Galí (2015), Ex. 3.5(f)). -/
theorem taylorRoot_one : taylorRoot 1 = 0 := by
  simp [taylorRoot]

/-- `λ < 0` for `δ > 1`: strategic substitutability makes responses
oscillate (Galí (2015), Ex. 3.5(f)). -/
theorem taylorRoot_neg {δ : ℝ} (hδ : 1 < δ) : taylorRoot δ < 0 := by
  unfold taylorRoot
  have h1 : 1 < Real.sqrt δ := by
    rw [Real.lt_sqrt zero_le_one, one_pow]; exact hδ
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- `λ → 1` as `δ → 0`: near-complete persistence under extreme strategic
complementarity (Galí (2015), Ex. 3.5(f)). -/
theorem tendsto_taylorRoot_zero : Tendsto taylorRoot (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt taylorRoot 0 := by
    unfold taylorRoot
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  have h := hc.tendsto
  have h1 : taylorRoot 0 = 1 := by simp [taylorRoot]
  rw [h1] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The impulse response of the output gap to a unit innovation in `z` (money)
at horizon `j`: `((1 + λ)/2) λʲ` (Galí (2015), Ex. 3.5(e)–(f)). -/
noncomputable def gapIRF (δ : ℝ) (j : ℕ) : ℝ := (1 + taylorRoot δ) / 2 * taylorRoot δ ^ j

/-- **The output-gap response is uniformly more persistent for smaller `δ`**
(Galí (2015), Ex. 3.5(f), p. 93): for `0 ≤ δ₁ < δ₂ ≤ 1` the response at every
horizon `j ≥ 1` is strictly larger under `δ₁`. -/
theorem gapIRF_lt {δ₁ δ₂ : ℝ} (h1 : 0 ≤ δ₁) (h12 : δ₁ < δ₂) (h2 : δ₂ ≤ 1) {j : ℕ}
    (hj : 0 < j) : gapIRF δ₂ j < gapIRF δ₁ j := by
  have hlt := taylorRoot_strictAntiOn (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (h1.trans h12.le)) h12
  have hnn : 0 ≤ taylorRoot δ₂ := by
    rcases h2.lt_or_eq with h | h
    · exact ((taylorRoot_pos_iff δ₂).mpr h).le
    · rw [h, taylorRoot_one]
  have hp : taylorRoot δ₂ ^ j < taylorRoot δ₁ ^ j := pow_lt_pow_left₀ hlt hnn hj.ne'
  unfold gapIRF
  have : 0 ≤ taylorRoot δ₂ ^ j := pow_nonneg hnn j
  nlinarith

end Gali.BasicNewKeynesianModel.Ex3_5

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.6: the Mankiw–Reis model of sticky information

Galí (2015), Chapter 3, Exercise 3.6, pp. 94–95. Each period a fraction `1 − θ`
of firms chooses a whole path of future prices (a price plan); the others keep
their old plans.

* (a) `hasDerivAt_log_priceIndex`: eq. (38), `p_t = (1 − θ) ∑ⱼ θʲ p_{t−j,t}`, as
  the exact first-order term of the CES price index over plan vintages.
* (b) `planObjective_update`, `plan_foc_of_isLocalMax`: the plan problem
  separates across horizons; each plan price satisfies its own first-order
  condition. `plan_rule_iff`: its exact linearisation is (39),
  `p_{t,t+k} = μ + E_t ψ_{t+k}`, with `ψ = w − ½ a` (`log_marginal_cost`).
* (c) `natural_output_levels`, `natural_output`, `mc_eq_gap`: `yⁿ = a − μ` and
  `m̂c = ỹ`.
* (d) `eq40`: eq. (40),
  `π_t = ((1−θ)/θ) ỹ_t + ((1−θ)/θ) ∑_{j≥1} θʲ E_{t−j}(π_t + Δỹ_t)`.
* (e), (f) `sticky_info_closed_form`: under random-walk money and technology the
  price level is `p_t = (1 − θ) ∑ⱼ θʲ z_{t−j}` with `z = m − yⁿ`, and the output
  gap, output, employment and inflation have closed forms; the impulse
  responses to a money innovation are `θ^{j+1}` (gap and output) and
  `(1 − θ)θʲ` (inflation); to a technology innovation the gap responds by
  `−θ^{j+1}`, output by `1 − θ^{j+1}`, employment by `½ − θ^{j+1}`.
  `nkpc_comparison`: under the standard NKPC the unique bounded equilibrium has
  exactly the same form with `θ` replaced by the stable root `λ` of
  `β λ² − (1 + β + κ) λ + 1 = 0`.

Dates are natural numbers. A plan vintage `j` periods old at date `t` was chosen
with information `E_{t−j}`, where `t − j` is truncated subtraction: firms whose
plans predate date `0` all use the date-`0` information (the filtration is
constant before the start of the economy).
-/

namespace Gali.BasicNewKeynesianModel.Ex3_6

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) The price level -/

/-- The CES price index over plan vintages (Galí (2015), Ex. 3.6(a), p. 94): a
share `(1 − θ)θʲ` of firms charges `Q j = P_{t−j,t}`, the date-`t` price of the
plan chosen `j` periods earlier, so
`P_t = (∑ⱼ (1 − θ)θʲ (P_{t−j,t})^{1−ε})^{1/(1−ε)}`. -/
noncomputable def priceIndex (θ ε : ℝ) (Q : ℕ → ℝ) : ℝ :=
  (∑' j, (1 - θ) * θ ^ j * Q j ^ (1 - ε)) ^ (1 / (1 - ε))

/-- A uniform bound on `exp((p̄ + s x̂ⱼ)(1 − ε))` for `|s| ≤ 1` and `|x̂ⱼ| ≤ B`
(Galí (2015), Ex. 3.6(a)). -/
theorem exp_vintage_le {ε pbar B s : ℝ} {xhat : ℕ → ℝ} (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1)
    (j : ℕ) :
    Real.exp ((pbar + s * xhat j) * (1 - ε)) ≤ Real.exp ((|pbar| + B) * |1 - ε|) := by
  rw [Real.exp_le_exp]
  calc (pbar + s * xhat j) * (1 - ε) ≤ |(pbar + s * xhat j) * (1 - ε)| := le_abs_self _
    _ = |pbar + s * xhat j| * |1 - ε| := abs_mul _ _
    _ ≤ (|pbar| + B) * |1 - ε| := by
      gcongr
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := hx j
      nlinarith [abs_nonneg s, abs_nonneg (xhat j)]

/-- The vintage sum converges (Galí (2015), Ex. 3.6(a)). -/
theorem summable_vintage {θ ε pbar B s : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {xhat : ℕ → ℝ}
    (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1) :
    Summable fun j => (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε)) := by
  refine Summable.of_nonneg_of_le (fun j => by have := hθ1; positivity) (fun j => ?_)
    (((summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ)).mul_right
      (Real.exp ((|pbar| + B) * |1 - ε|)))
  exact mul_le_mul_of_nonneg_left (exp_vintage_le hx hs j) (by have := hθ1; positivity)

/-- The vintage sum is positive (Galí (2015), Ex. 3.6(a)). -/
theorem vintage_pos {θ ε pbar B s : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {xhat : ℕ → ℝ}
    (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1) :
    0 < ∑' j, (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε)) :=
  (summable_vintage hθ0 hθ1 hx hs).tsum_pos (fun j => by have := hθ1; positivity) 0
    (by simp only [pow_zero, mul_one]; exact mul_pos (by linarith) (Real.exp_pos _))

/-- The log price index along a path of plan prices `P_{t−j,t} = exp(p̄ + s x̂ⱼ)`
(Galí (2015), Ex. 3.6(a)). -/
theorem log_priceIndex_path {θ ε pbar B s : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {xhat : ℕ → ℝ}
    (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1) :
    Real.log (priceIndex θ ε (fun j => Real.exp (pbar + s * xhat j)))
      = 1 / (1 - ε) *
        Real.log (∑' j, (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε))) := by
  unfold priceIndex
  simp_rw [← Real.exp_mul]
  rw [Real.log_rpow (vintage_pos hθ0 hθ1 hx hs)]

/-- The shares `(1 − θ)θʲ` sum to one (Galí (2015), Ex. 3.6(a)). -/
theorem tsum_shares {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (c : ℝ) :
    ∑' j : ℕ, (1 - θ) * θ ^ j * c = c := by
  rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1]
  have : 1 - θ ≠ 0 := by linarith
  field_simp

/-- **Eq. (38)** (Galí (2015), Ex. 3.6(a), p. 94): along any bounded direction
`p_{t−j,t} = p̄ + s x̂ⱼ`, the log price level has derivative `(1 − θ) ∑ⱼ θʲ x̂ⱼ`
at the zero-inflation steady state; that is, `p_t = (1 − θ) ∑ⱼ θʲ p_{t−j,t}` to
first order. -/
theorem hasDerivAt_log_priceIndex {θ ε pbar B : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : ε ≠ 1)
    {xhat : ℕ → ℝ} (hx : ∀ j, |xhat j| ≤ B) :
    HasDerivAt (fun s => Real.log (priceIndex θ ε (fun j => Real.exp (pbar + s * xhat j))))
      ((1 - θ) * ∑' j, θ ^ j * xhat j) 0 := by
  have hε' : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hx 0)
  set C := Real.exp ((|pbar| + B) * |1 - ε|) with hC
  set g : ℕ → ℝ → ℝ := fun j s => (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε))
    with hg
  set g' : ℕ → ℝ → ℝ := fun j s =>
    (1 - θ) * θ ^ j * (Real.exp ((pbar + s * xhat j) * (1 - ε)) * (xhat j * (1 - ε))) with hg'
  have hderiv : ∀ j s, HasDerivAt (g j) (g' j s) s := by
    intro j s
    have h1 : HasDerivAt (fun s : ℝ => (pbar + s * xhat j) * (1 - ε)) (xhat j * (1 - ε)) s := by
      simpa using (((hasDerivAt_id s).mul_const (xhat j)).const_add pbar).mul_const (1 - ε)
    exact h1.exp.const_mul _
  have hIoo : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, |s| ≤ 1 := fun s hs => abs_le.mpr ⟨hs.1.le, hs.2.le⟩
  have hT := hasDerivAt_tsum_of_isPreconnected (u := fun j => (1 - θ) * θ ^ j * (C * (B * |1 - ε|)))
    (g := g) (g' := g') (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    ((summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ) |>.mul_right _) isOpen_Ioo
    isPreconnected_Ioo (fun j s _ => hderiv j s)
    (fun j s hs => by
      simp only [hg', Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ), abs_of_nonneg (pow_nonneg hθ0 j)]
      refine mul_le_mul_of_nonneg_left ?_ (by have := hθ1; positivity)
      exact mul_le_mul (exp_vintage_le hx (hIoo s hs) j)
        (mul_le_mul_of_nonneg_right (hx j) (abs_nonneg _)) (by positivity) (by positivity))
    ⟨by norm_num, by norm_num⟩ (summable_vintage hθ0 hθ1 hx (by simp)) ⟨by norm_num, by norm_num⟩
  have hval : ∑' j, g j 0 = Real.exp (pbar * (1 - ε)) := by
    simp only [hg, zero_mul, add_zero]
    exact tsum_shares hθ0 hθ1 _
  have hL := (hT.log (by rw [hval]; exact (Real.exp_pos _).ne')).const_mul (1 / (1 - ε))
  have hfun : (fun s => Real.log (priceIndex θ ε (fun j => Real.exp (pbar + s * xhat j))))
      =ᶠ[𝓝 0] fun s => 1 / (1 - ε) * Real.log (∑' j, g j s) := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
      with s hs
    exact log_priceIndex_path hθ0 hθ1 hx (hIoo s hs)
  refine (hL.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [hval]
  have hs' : ∑' j, g' j 0
      = (1 - θ) * Real.exp (pbar * (1 - ε)) * (1 - ε) * ∑' j, θ ^ j * xhat j := by
    rw [← tsum_mul_left]
    congr 1; funext j
    simp only [hg', zero_mul, add_zero]
    ring
  rw [hs']
  have := (Real.exp_pos (pbar * (1 - ε))).ne'
  field_simp

/-- The price level at the zero-inflation steady state (Galí (2015), Ex. 3.6(a)). -/
theorem log_priceIndex_steady {θ ε pbar : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : ε ≠ 1) :
    Real.log (priceIndex θ ε (fun _ => Real.exp pbar)) = pbar := by
  have h := log_priceIndex_path (ε := ε) (pbar := pbar) (B := 0) (s := 0) hθ0 hθ1
    (xhat := fun _ => 0) (fun _ => by simp) (by simp)
  simp only [mul_zero, add_zero] at h
  rw [h, tsum_shares hθ0 hθ1, Real.log_exp]
  have : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  field_simp

/-! ### (b) The price plan -/

/-- With technology `Y = √A N` and wage `W`, nominal marginal cost is `W/√A`,
so `ψ = w − ½ a` (Galí (2015), Ex. 3.6(b), p. 94). -/
theorem log_marginal_cost {W A : ℝ} (hW : 0 < W) (hA : 0 < A) :
    Real.log (W / Real.sqrt A) = Real.log W - Real.log A / 2 := by
  rw [Real.log_div hW.ne' (Real.sqrt_pos.mpr hA).ne', Real.log_sqrt hA.le]

/-- **The price-plan objective** (Galí (2015), Ex. 3.6(b), p. 94): for a plan
`x = (P_{t,t+k})ₖ`,
`∑ₖ θᵏ E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k}(i)(P_{t,t+k} − Ψ_{t+k})]`, with
`Ψ_{t+k} = W_{t+k}/√A_{t+k}` and the demand of Ex. 3.5. -/
noncomputable def planObjective (θ ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℕ → ℝ)
    (ω : Ω) : ℝ :=
  ∑' k, θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω

/-- **The plan problem separates across horizons** (Galí (2015), Ex. 3.6(b)): if
the objective converges at the plan `x`, then changing the horizon-`k` price to
`z` changes only the horizon-`k` term. -/
theorem planObjective_update {θ ε : ℝ} {Λ P C Ψ : ℕ → Ω → ℝ} {t : ℕ} {x : ℕ → ℝ} {ω : Ω}
    (hs : Summable fun k => θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω)
    (k : ℕ) (z : ℝ) :
    planObjective 𝔼 θ ε Λ P C Ψ t (Function.update x k z) ω
      = θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω
        + ∑' j, if j = k then 0
            else θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω := by
  set f : ℕ → ℝ := fun j => θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω
    with hf
  have hupd : (fun j => θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j)
      (Function.update x k z j)) ω)
      = Function.update f k (θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  unfold planObjective
  rw [hupd, (hs.update k _).tsum_eq_add_tsum_ite k]
  simp only [Function.update_self]
  congr 1
  refine tsum_congr fun j => ?_
  by_cases hj : j = k
  · simp [hj]
  · simp only [hj, ↓reduceIte]
    rw [Function.update_of_ne hj]

/-- **The first-order condition for each plan price** (Galí (2015), Ex. 3.6(b),
p. 94): if the plan `x` is locally optimal in its horizon-`k` price
`x k > 0`, and `θ > 0`, then
`E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k}(i) (P_{t,t+k} − M Ψ_{t+k})] = 0`. -/
theorem plan_foc_of_isLocalMax {θ ε : ℝ} (hθ : 0 < θ) (hε : 1 < ε) {Λ P C Ψ : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) {t : ℕ} {x : ℕ → ℝ} {ω : Ω}
    (hs : Summable fun k => θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω)
    {k : ℕ} (hxk : 0 < x k)
    (hmax : IsLocalMax (fun z => planObjective 𝔼 θ ε Λ P C Ψ t (Function.update x k z) ω) (x k)) :
    𝔼.E t (Ex3_5.focTerm ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω = 0 := by
  have hfun : (fun z => planObjective 𝔼 θ ε Λ P C Ψ t (Function.update x k z) ω)
      = fun z => θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω
        + ∑' j, if j = k then 0
            else θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω :=
    funext fun z => planObjective_update 𝔼 hs k z
  have hd := Ex3_5.hasDerivAt_closedForm hε hxk (𝔼.E t (Ex3_5.wgt ε (Λ k) (P k) (C k)) ω)
    (𝔼.E t (Ex3_5.wgt ε (Λ k) (P k) (C k) * Ψ k) ω)
  have hd' : HasDerivAt (fun z => 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω)
      ((1 - ε) / x k * 𝔼.E t (Ex3_5.focTerm ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω) (x k) := by
    rw [Ex3_5.E_focTerm_eq 𝔼 hxk (hP k)]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hxk] with z hz
    exact Ex3_5.E_profit_eq 𝔼 hz (hP k) t ω
  have hD := (hd'.const_mul (θ ^ k)).add_const
    (∑' j, if j = k then 0
      else θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω)
  rw [hfun] at hmax
  have h0 := hmax.hasDerivAt_eq_zero hD
  have hc : θ ^ k * ((1 - ε) / x k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero k hθ.ne') (div_ne_zero (by linarith) hxk.ne')
  rw [← mul_assoc] at h0
  exact (mul_eq_zero.mp h0).resolve_left hc

/-- **Exact linearisation of a plan price's first-order condition**
(Galí (2015), Ex. 3.6(b), p. 94): with weight `w = w̄ exp(s ŵ)`, plan price
`exp(p̄ + s x̂)` and marginal cost `exp(p̄ − μ + s ψ̂)`, the derivative at `s = 0`
is `w̄ e^{p̄}(x̂ − E_t ψ̂)`. -/
theorem plan_hasDerivAt_path {ε wbar pbar xhat B : ℝ} (hε : 1 < ε) {what ψhat : Ω → ℝ}
    (hw : ∀ ω, |what ω| ≤ B) (hψ : ∀ ω, |ψhat ω| ≤ B) (hxB : |xhat| ≤ B) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => 𝔼.E t (fun ω' => wbar * Real.exp (s * what ω') *
        (Real.exp (pbar + s * xhat)
          - Ex3_5.markup ε * Real.exp (pbar - Ex3_5.logMarkup ε + s * ψhat ω'))) ω)
      (wbar * Real.exp pbar * (xhat - 𝔼.E t ψhat ω)) 0 := by
  have h := Ex3_5.hasDerivAt_focLHS_path 𝔼 (N := 1) (β := 1) (wbar := wbar) (pbar := pbar)
    hε (what := fun _ => what) (ψhat := fun _ => ψhat) (fun _ => hw) (fun _ => hψ) hxB t ω
  simpa [Ex3_5.focLHS] using h

/-- **The plan rule (39)** (Galí (2015), Ex. 3.6(b), p. 94): the first-order
term vanishes if and only if `p_{t,t+k} = μ + E_t ψ_{t+k}`, where
`p_{t,t+k} = p̄ + x̂` and `ψ_{t+k} = (p̄ − μ) + ψ̂`. -/
theorem plan_rule_iff {ε wbar pbar xhat : ℝ} (hwbar : 0 < wbar) (ψhat : Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    wbar * Real.exp pbar * (xhat - 𝔼.E t ψhat ω) = 0 ↔
      pbar + xhat
        = Ex3_5.logMarkup ε + 𝔼.E t (fun ω' => (pbar - Ex3_5.logMarkup ε) + ψhat ω') ω := by
  have hf : (fun ω' => (pbar - Ex3_5.logMarkup ε) + ψhat ω')
      = (fun _ => pbar - Ex3_5.logMarkup ε) + ψhat := rfl
  rw [hf, map_add, 𝔼.const, Pi.add_apply]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_left hc
    linarith
  · intro h
    have : xhat - 𝔼.E t ψhat ω = 0 := by linarith
    rw [this, mul_zero]

/-! ### (c) Natural output and marginal cost -/

/-- **Natural output in levels** (Galí (2015), Ex. 3.6(c), p. 94): with flexible
prices `P = M W/√A`, labour supply `W/P = N` (from `U = C − N²/2`), and
`Y = √A N`, output is `Y = A/M`, i.e. `yⁿ = a − μ` exactly. -/
theorem natural_output_levels {ε P W A Y Nl : ℝ} (hε : 1 < ε) (hA : 0 < A)
    (hflex : P = Ex3_5.markup ε * (W / Real.sqrt A)) (hP : 0 < P) (hls : W / P = Nl)
    (hy : Y = Real.sqrt A * Nl) : Real.log Y = Real.log A - Ex3_5.logMarkup ε := by
  have hM := Ex3_5.markup_pos hε
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hWA : 0 < W / Real.sqrt A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hsA
    rwa [div_mul_cancel₀ W hsA.ne'] at this
  have hN : Nl = Real.sqrt A / Ex3_5.markup ε := by
    rw [← hls, hflex]; field_simp
  have hY : Y = A / Ex3_5.markup ε := by
    rw [hy, hN, ← mul_div_assoc, Real.mul_self_sqrt hA.le]
  rw [hY, Real.log_div hA.ne' hM.ne']
  rfl

/-- **Natural output in logs** (Galí (2015), Ex. 3.6(c)(i), p. 94): flexible
prices `p = μ + ψ` with `ψ = w − ½a`, labour supply `w − p = n` and
`y = ½a + n` give `yⁿ = a − μ`. -/
theorem natural_output {μ p w a y n : ℝ} (hflex : p = μ + (w - a / 2)) (hls : w - p = n)
    (hy : y = a / 2 + n) : y = a - μ := by
  rw [hy, ← hls, hflex]; ring

/-- **Real marginal cost equals the output gap** (Galí (2015), Ex. 3.6(c)(ii),
p. 94): `m̂c_t = (ψ_t − p_t) + μ = y_t − yⁿ_t`. -/
theorem mc_eq_gap {μ p w a y n : ℝ} (hls : w - p = n) (hy : y = a / 2 + n) :
    ((w - a / 2) - p) + μ = y - (a - μ) := by
  rw [hy, ← hls]; ring

/-! ### (d) The sticky-information Phillips curve (40) -/

/-- Geometrically weighted expectations of a bounded random variable converge
(Galí (2015), Ex. 3.6(d)). -/
theorem summable_geom_E {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {Y : Ω → ℝ} {M : ℝ}
    (hY : ∀ ω, |Y ω| ≤ M) (f : ℕ → ℕ) (ω : Ω) :
    Summable fun j => θ ^ j * 𝔼.E (f j) Y ω := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ0 hθ1).mul_right M)
    fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hθ0 j)]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le hY _ ω) (pow_nonneg hθ0 j)

/-- The price level as a vintage average of expectations (Galí (2015), Ex. 3.6(d)):
combining (38) and (39) with `ψ = p + ỹ − μ`,
`p_t = (1 − θ) ∑ⱼ θʲ E_{t−j}(p_t + ỹ_t)`. -/
theorem price_level_eq {θ μ : ℝ} {p ytil ψ : ℕ → Ω → ℝ} {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (t : ℕ) (ω : Ω) :
    p t ω = (1 - θ) * ∑' j, θ ^ j * 𝔼.E (t - j) (p t + ytil t) ω := by
  rw [hindex t ω]
  congr 2; funext j
  rw [hplan, hψ, map_sub, 𝔼.const]
  simp

/-- **Eq. (40)** (Galí (2015), Ex. 3.6(d), p. 95). Under (38), (39) and
`ψ = p + ỹ − μ` (part (c)), with `p` and `ỹ` adapted and bounded at each date,
inflation `π_{t+1} = p_{t+1} − p_t` satisfies
`π_{t+1} = ((1−θ)/θ) ỹ_{t+1} + ((1−θ)/θ) ∑_{j≥1} θʲ E_{t+1−j}(π_{t+1} + Δỹ_{t+1})`;
the `j`-th term below is the `(j+1)`-st of the book, with `E_{(t+1)−(j+1)} = E_{t−j}`. -/
theorem eq40 {θ μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {p ytil ψ infl : ℕ → Ω → ℝ}
    {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hpa : 𝔼.Adapted p) (hya : 𝔼.Adapted ytil)
    (hb : ∀ t, ∃ M, ∀ ω, |p t ω + ytil t ω| ≤ M) (t : ℕ) (ω : Ω) :
    infl (t + 1) ω = (1 - θ) / θ * ytil (t + 1) ω + (1 - θ) / θ *
      ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) (infl (t + 1) + (ytil (t + 1) - ytil t)) ω := by
  obtain ⟨M₁, hM₁⟩ := hb (t + 1)
  obtain ⟨M₀, hM₀⟩ := hb t
  set X1 := p (t + 1) + ytil (t + 1) with hX1
  set X0 := p t + ytil t with hX0
  have hX1b : ∀ ω, |X1 ω| ≤ M₁ := hM₁
  have hX0b : ∀ ω, |X0 ω| ≤ M₀ := hM₀
  have hX1a : 𝔼.E (t + 1) X1 = X1 := by rw [hX1, map_add, hpa, hya]
  have hp1 := price_level_eq 𝔼 hindex hplan hψ (t + 1) ω
  have hp0 := price_level_eq 𝔼 hindex hplan hψ t ω
  rw [← hX1] at hp1
  rw [← hX0] at hp0
  have hs1 := summable_geom_E 𝔼 hθ0.le hθ1 hX1b (fun j => t + 1 - j) ω
  rw [hs1.tsum_eq_zero_add] at hp1
  simp only [pow_zero, one_mul, Nat.sub_zero, hX1a, Nat.add_sub_add_right] at hp1
  have hsA : Summable fun j => θ ^ (j + 1) * 𝔼.E (t - j) X1 ω := by
    have := (summable_geom_E 𝔼 hθ0.le hθ1 hX1b (fun j => t - j) ω).mul_left θ
    refine this.congr fun j => ?_
    ring
  have hsB : Summable fun j => θ ^ (j + 1) * 𝔼.E (t - j) X0 ω := by
    have := (summable_geom_E 𝔼 hθ0.le hθ1 hX0b (fun j => t - j) ω).mul_left θ
    refine this.congr fun j => ?_
    ring
  have hB : ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) X0 ω = θ * ∑' j, θ ^ j * 𝔼.E (t - j) X0 ω := by
    rw [← tsum_mul_left]
    congr 1; funext j; ring
  have hdiff : infl (t + 1) + (ytil (t + 1) - ytil t) = X1 - X0 := by
    rw [hinfl, hX1, hX0]; abel
  have hD : ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) (infl (t + 1) + (ytil (t + 1) - ytil t)) ω
      = ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) X1 ω - ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) X0 ω := by
    rw [← hsA.tsum_sub hsB, hdiff]
    congr 1; funext j
    rw [map_sub, Pi.sub_apply]; ring
  rw [hD, hB]
  have hi := congrFun (hinfl t) ω
  simp only [Pi.sub_apply] at hi
  rw [hi, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hθ0.ne']
  have hX1ω : X1 ω = p (t + 1) ω + ytil (t + 1) ω := rfl
  linear_combination hp1 - θ * hp0 + (1 - θ) * hX1ω

/-! ### (e), (f) Random walks: closed forms -/

/-- With money demand `y = m − p`, the vintage average involves only
`z = m − yⁿ`, so with `z` a random walk
`p_t = (1 − θ) ∑ⱼ θʲ z_{t−j}` (Galí (2015), Ex. 3.6(e), p. 95). -/
theorem price_level_randomWalk {θ μ : ℝ} {p ytil ψ z : ℕ → Ω → ℝ} {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (hgap : ∀ t, ytil t = z t - p t)
    (hz : 𝔼.IsAR1 1 z) (t : ℕ) (ω : Ω) :
    p t ω = (1 - θ) * ∑' j, θ ^ j * z (t - j) ω := by
  rw [price_level_eq 𝔼 hindex hplan hψ t ω]
  congr 2; funext j
  have hX : p t + ytil t = z t := by rw [hgap]; abel
  have hk := 𝔼.ar1_iterate hz (t - j) j
  simp only [one_pow, one_smul] at hk
  rw [hX]
  rcases le_or_gt j t with h | h
  · rw [Nat.sub_add_cancel h] at hk
    rw [hk]
  · have h0 : t - j = 0 := by omega
    rw [h0]
    have := 𝔼.ar1_iterate hz 0 t
    simp only [one_pow, one_smul, zero_add] at this
    rw [this]

/-- The lagged sums `∑ⱼ θʲ z_{s−j}` converge: only `z₀, …, z_s` enter
(Galí (2015), Ex. 3.6(e)). -/
theorem summable_lagged {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (z : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    Summable fun j => θ ^ j * z (s - j) ω := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ0 hθ1).mul_right
    (∑ k ∈ Finset.range (s + 1), |z k ω|)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hθ0 j)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 j)
  exact Finset.single_le_sum (f := fun k => |z k ω|) (fun k _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

/-- **The price-level recursion** (Galí (2015), Ex. 3.6(e), p. 95): if
`p_t = (1 − θ) ∑ⱼ θʲ z_{t−j}`, then `p₀ = z₀` and
`p_{t+1} = θ p_t + (1 − θ) z_{t+1}`. -/
theorem price_level_rec {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {p z : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * z (t - j) ω) (ω : Ω) :
    p 0 ω = z 0 ω ∧ ∀ t, p (t + 1) ω = θ * p t ω + (1 - θ) * z (t + 1) ω := by
  constructor
  · rw [hp 0 ω]
    simp only [Nat.zero_sub]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hθ0 hθ1]
    have : 1 - θ ≠ 0 := by linarith
    field_simp
  · intro t
    rw [hp (t + 1) ω, hp t ω, (summable_lagged hθ0 hθ1 z (t + 1) ω).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    have : ∑' j, θ ^ (j + 1) * z (t - j) ω = θ * ∑' j, θ ^ j * z (t - j) ω := by
      rw [← tsum_mul_left]
      congr 1; funext j; ring
    rw [this]
    ring

/-- The cumulated innovations `Hₜ = ∑_{j≤t} θʲ v_{t−j}`, `vᵢ = z_{i+1} − z_i`
(Galí (2015), Ex. 3.6(e)–(f)). -/
noncomputable def cumInnov (θ : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (t + 1), θ ^ j * (z (t - j + 1) ω - z (t - j) ω)

/-- `H_{t+1} = v_{t+1} + θ H_t` (Galí (2015), Ex. 3.6(e)). -/
theorem cumInnov_succ (θ : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    cumInnov θ z (t + 1) ω = (z (t + 2) ω - z (t + 1) ω) + θ * cumInnov θ z t ω := by
  unfold cumInnov
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_sub_add_right]
  ring

/-- **The sticky-information equilibrium under random walks in closed form**
(Galí (2015), Ex. 3.6(e)–(f), p. 95). With (38), (39), `ψ = p + ỹ − μ`, money
demand `ỹ = z − p` for `z = m − yⁿ` a random walk, and `0 ≤ θ < 1`:
`ỹ_{t+1} = θ H_t`, `π_{t+1} = (1 − θ) H_t` and `p_{t+1} = z_{t+1} − θ H_t`, where
`H_t = ∑_{j≤t} θʲ v_{t−j}` and `ỹ₀ = 0`. A unit innovation `v` raises the gap by
`θ^{j+1}` after `j` periods and inflation by `(1 − θ)θʲ`. The equilibrium is
unique: the price level is pinned down without any boundedness condition. -/
theorem sticky_info_closed_form {θ μ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    {p ytil ψ z infl : ℕ → Ω → ℝ} {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (hgap : ∀ t, ytil t = z t - p t)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (hz : 𝔼.IsAR1 1 z) (ω : Ω) :
    ytil 0 ω = 0 ∧ ∀ t, ytil (t + 1) ω = θ * cumInnov θ z t ω ∧
      infl (t + 1) ω = (1 - θ) * cumInnov θ z t ω ∧
      p (t + 1) ω = z (t + 1) ω - θ * cumInnov θ z t ω := by
  have hp := price_level_randomWalk 𝔼 hindex hplan hψ hgap hz
  obtain ⟨h0, hrec⟩ := price_level_rec hθ0 hθ1 hp ω
  have hy : ∀ t, ytil t ω = z t ω - p t ω := fun t => by rw [hgap t]; rfl
  have hkey : ∀ t, ytil t ω + (z (t + 1) ω - z t ω) = cumInnov θ z t ω := by
    intro t
    induction t with
    | zero =>
      simp [cumInnov, hy, h0]
    | succ t ih =>
      rw [cumInnov_succ, ← ih, hy, hy, hrec t]
      ring
  refine ⟨by rw [hy, h0, sub_self], fun t => ?_⟩
  have h1 : ytil (t + 1) ω = θ * cumInnov θ z t ω := by
    rw [← hkey t, hy, hy, hrec t]; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [hinfl t, Pi.sub_apply, ← hkey t, hy, hrec t]; ring
  · rw [← h1, hy]; ring

/-- **Output, employment and the gap in terms of money and technology
innovations** (Galí (2015), Ex. 3.6(e)–(f), p. 95). With `yⁿ = a − μ`,
`z = m − yⁿ`, output `y = yⁿ + ỹ` and employment `n = y − ½ a`:
`vᵢ = (m_{i+1} − m_i) − (a_{i+1} − a_i)`, so after a money innovation `u` the gap
and output rise by `θ^{j+1} u` and employment too; after a technology
innovation `ε` the gap moves by `−θ^{j+1} ε`, output by `(1 − θ^{j+1}) ε`,
employment by `(½ − θ^{j+1}) ε`, inflation by `−(1 − θ)θʲ ε`. -/
theorem output_employment {μ : ℝ} {m a yn z ytil y n : ℕ → Ω → ℝ}
    (hyn : ∀ t, yn t = a t - fun _ => μ) (hz : ∀ t, z t = m t - yn t)
    (hy : ∀ t, y t = yn t + ytil t) (hn : ∀ t, n t = y t - (1 / 2 : ℝ) • a t) (t : ℕ) (ω : Ω) :
    z (t + 1) ω - z t ω = (m (t + 1) ω - m t ω) - (a (t + 1) ω - a t ω) ∧
      y t ω = a t ω - μ + ytil t ω ∧ n t ω = a t ω / 2 - μ + ytil t ω := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hz, hyn, Pi.sub_apply]; ring
  · simp only [hy, hyn, Pi.add_apply, Pi.sub_apply]
  · simp only [hn, hy, hyn, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-! ### Comparison with the standard New Keynesian Phillips curve -/

/-- The stable root `λ = ((1 + β + κ) − √((1 + β + κ)² − 4β))/(2β)` of
`β λ² − (1 + β + κ) λ + 1 = 0` (Galí (2015), Ex. 3.6(e), p. 95). -/
noncomputable def nkpcRoot (β κ : ℝ) : ℝ :=
  ((1 + β + κ) - Real.sqrt ((1 + β + κ) ^ 2 - 4 * β)) / (2 * β)

/-- `λ` solves `β λ² − (1 + β + κ) λ + 1 = 0` (Galí (2015), Ex. 3.6(e)). -/
theorem nkpcRoot_quadratic {β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) :
    β * nkpcRoot β κ ^ 2 - (1 + β + κ) * nkpcRoot β κ + 1 = 0 := by
  have hD : 0 ≤ (1 + β + κ) ^ 2 - 4 * β := by nlinarith
  have hs := Real.sq_sqrt hD
  unfold nkpcRoot
  generalize Real.sqrt ((1 + β + κ) ^ 2 - 4 * β) = r at hs ⊢
  field_simp
  linear_combination hs

/-- `0 < λ < 1` (Galí (2015), Ex. 3.6(e)). -/
theorem nkpcRoot_mem {β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) :
    0 < nkpcRoot β κ ∧ nkpcRoot β κ < 1 := by
  have hD : 0 ≤ (1 + β + κ) ^ 2 - 4 * β := by nlinarith
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg ((1 + β + κ) ^ 2 - 4 * β)
  unfold nkpcRoot
  constructor
  · apply div_pos _ (by linarith)
    nlinarith
  · rw [div_lt_one (by linarith)]
    nlinarith

/-- **The NKPC comparison** (Galí (2015), Ex. 3.6(e)–(f), p. 95). Replace (40)
by the NKPC `π_{t+1} = β E_{t+1} π_{t+2} + κ ỹ_{t+1}` with `π_{t+1} = p_{t+1} − p_t`,
`ỹ = z − p`, `z` a random walk with bounded innovations, `p` adapted and
`p − z` bounded. Then the equilibrium is unique given `p₀`, and
`ỹ_{t+1} = λ(ỹ_t + v_t)`, `π_{t+1} = (1 − λ)(ỹ_t + v_t)` with the stable root
`λ ∈ (0,1)`: the same dynamics as sticky information,
`ỹ_{t+1} = θ(ỹ_t + v_t)`, `π_{t+1} = (1 − θ)(ỹ_t + v_t)`, with `θ` replaced by `λ`. -/
theorem nkpc_comparison {β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    {p z ytil infl : ℕ → Ω → ℝ} (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hnkpc : ∀ t, infl (t + 1) = β • 𝔼.E (t + 1) (infl (t + 2)) + κ • ytil (t + 1))
    (hgap : ∀ t, ytil t = z t - p t) (hza : 𝔼.Adapted z) (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t)
    {K : ℝ} (hK : ∀ t ω, |z (t + 1) ω - z t ω| ≤ K) (hpa : 𝔼.Adapted p)
    (hb : BoundedProc fun t => p t - z t) (t : ℕ) (ω : Ω) :
    ytil (t + 1) ω = nkpcRoot β κ * (ytil t ω + (z (t + 1) ω - z t ω)) ∧
      infl (t + 1) ω = (1 - nkpcRoot β κ) * (ytil t ω + (z (t + 1) ω - z t ω)) := by
  set S := 1 + β + κ with hS
  set lam := nkpcRoot β κ with hlam
  obtain ⟨hl0, hl1⟩ := nkpcRoot_mem hβ hβ1 hκ
  have hq : β * lam ^ 2 - S * lam + 1 = 0 := nkpcRoot_quadratic hβ hβ1 hκ
  have hq' : β * lam ^ 2 - (1 + β + κ) * lam + 1 = 0 := hq
  have hS0 : 0 < S := by positivity
  have hSl : 0 < S - β * lam := by
    have h1 : lam * (S - β * lam) = 1 := by linear_combination -hq
    by_contra h
    push Not at h
    nlinarith
  have hsol : Ex3_5.SolvesPre 𝔼 (1 / S) (β / S) (fun t => -(1 / S) • (z t - z (t - 1)))
      (fun t => p t - z t) := by
    intro t
    have hEq : 𝔼.E (t + 1) (p (t + 2) - z (t + 2)) = 𝔼.E (t + 1) (p (t + 2)) - z (t + 1) := by
      rw [map_sub, hzrw]
    have hEi : 𝔼.E (t + 1) (infl (t + 2)) = 𝔼.E (t + 1) (p (t + 2)) - p (t + 1) := by
      rw [hinfl (t + 1), map_sub, hpa (t + 1)]
    change p (t + 1) - z (t + 1) = (1 / S) • (p t - z t)
      + (β / S) • 𝔼.E (t + 1) (p (t + 2) - z (t + 2)) + -(1 / S) • (z (t + 1) - z (t + 1 - 1))
    rw [hEq, Nat.add_sub_cancel]
    funext ω
    have e1 := congrFun (hnkpc t) ω
    have e2 := congrFun (hinfl t) ω
    have e3 := congrFun hEi ω
    have e4 := congrFun (hgap (t + 1)) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
    field_simp
    linear_combination e1 - e2 + β * e3 + κ * e4
  have hA : 1 / S = lam * (1 - β / S * lam) := by
    field_simp
    linear_combination hq'
  have hd : 1 - β / S * lam ≠ 0 := by
    have : 1 - β / S * lam = (S - β * lam) / S := by field_simp
    rw [this]; positivity
  have hγ : |β / S / (1 - β / S * lam)| < 1 := by
    have : β / S / (1 - β / S * lam) = β * lam := by
      rw [div_eq_iff hd]
      field_simp
      linear_combination hq'
    rw [this, abs_of_pos (by positivity)]
    nlinarith
  have hfa : 𝔼.Adapted (fun t => -(1 / S) • (z t - z (t - 1))) := by
    intro t
    have : 𝔼.E t (z (t - 1)) = z (t - 1) := by
      rw [← hza (t - 1), 𝔼.known (Nat.sub_le t 1)]
    simp only [map_smul, map_sub, hza t, this]
  have hf0 : ∀ t, 𝔼.E t ((fun t => -(1 / S) • (z t - z (t - 1))) (t + 1)) = 0 := by
    intro t
    simp only [Nat.add_sub_cancel, map_smul, map_sub, hzrw t, hza t, sub_self, smul_zero]
  have hq0 : 𝔼.E 0 (p 0 - z 0) = p 0 - z 0 := by rw [map_sub, hpa 0, hza 0]
  have hex := Ex3_5.predetermined_solves 𝔼 hA hd hfa hf0 hq0
  set g : ℕ → Ω → ℝ := fun t => (1 - β / S * lam)⁻¹ • -(1 / S) • (z t - z (t - 1)) with hg
  have hga : 𝔼.Adapted g := fun t => by simp only [hg, map_smul, hfa t]
  obtain ⟨M, hM⟩ := hb
  have hgb : ∀ t ω, |g t ω| ≤ |(1 - β / S * lam)⁻¹ * (1 / S)| * K := by
    intro t ω
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ω)
    cases t with
    | zero =>
      simp only [hg, Nat.zero_sub, sub_self, smul_zero, Pi.zero_apply, abs_zero]
      positivity
    | succ t =>
      simp only [hg, Nat.add_sub_cancel, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [show (1 - β / S * lam)⁻¹ * (-(1 / S) * (z (t + 1) ω - z t ω))
          = -((1 - β / S * lam)⁻¹ * (1 / S)) * (z (t + 1) ω - z t ω) by ring, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg _)
  have hlam1 : |lam| < 1 := by rw [abs_of_pos hl0]; exact hl1
  have huniq := Ex3_5.predetermined_unique 𝔼 hA hd hγ hsol hex
    (fun t => by simp only [map_sub, hpa t, hza t]) (Ex3_5.ar1Path_adapted 𝔼 hga hq0)
    ⟨M, hM⟩ ⟨_, Ex3_5.ar1Path_bounded hlam1 hgb (M0 := M) (hM 0)⟩ rfl
  have hstep : p (t + 1) ω - z (t + 1) ω
      = lam * (p t ω - z t ω) - lam * (z (t + 1) ω - z t ω) := by
    have h1 : p (t + 1) ω - z (t + 1) ω = Ex3_5.ar1Path lam g (p 0 - z 0) (t + 1) ω :=
      congrFun (congrFun huniq (t + 1)) ω
    have h0 : p t ω - z t ω = Ex3_5.ar1Path lam g (p 0 - z 0) t ω :=
      congrFun (congrFun huniq t) ω
    rw [h1, h0]
    have hsc : (1 - β / S * lam)⁻¹ * (1 / S) = lam := by
      field_simp
      linear_combination hq'
    simp only [Ex3_5.ar1Path, hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      Nat.add_sub_cancel]
    rw [show (1 - β / S * lam)⁻¹ * (-(1 / S) * (z (t + 1) ω - z t ω))
        = -((1 - β / S * lam)⁻¹ * (1 / S)) * (z (t + 1) ω - z t ω) by ring, hsc]
    ring
  have hy1 := congrFun (hgap (t + 1)) ω
  have hy0 := congrFun (hgap t) ω
  have hi := congrFun (hinfl t) ω
  simp only [Pi.sub_apply] at hy1 hy0 hi
  constructor
  · rw [hy1, hy0]; linear_combination -hstep
  · rw [hi, hy0]; linear_combination hstep

end Gali.BasicNewKeynesianModel.Ex3_6

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.7: technology shocks and the Taylor rule

Galí (2015), Chapter 3, Exercise 3.7, pp. 95–96. Log utility (`σ = 1`),
technology `Y = A N`, constant desired markups, Calvo pricing.

* (a) `natural_output_levels`, `natural_output`: `yⁿ_t = a_t − μ/(1 + φ)`.
* The dynamic IS equation in gaps (`gap_dis`), with the natural rate
  `rⁿ_t = ρ + E_t a_{t+1} − a_t`; under a random walk `rⁿ = ρ`
  (`naturalRate_randomWalk`), under an AR(1) `rⁿ = ρ − (1 − ρₐ) a`
  (`naturalRate_ar1`). The DIS (41) as printed (with `ρ`) is valid only in
  the random-walk case.
* `solves_of_model`, `schurStable_iff`, `determinate_iff_taylor`: with the rule
  (43), the system `x_t = A E_t x_{t+1} + w_t` is determinate iff `φ_π > 1`.
* (b) `randomWalk_equilibrium`: with a random-walk technology and `φ_π > 1`,
  `ỹ = π = 0` is the unique bounded equilibrium, so `y = yⁿ` and `i = ρ`.
* (c) `ar1_equilibrium`, `ar1_signs`: with `a` an AR(1), `ρₐ < 1`, the
  unique bounded equilibrium is the minimum-state-variable solution
  `ỹ = −(1 − ρₐ)(1 − βρₐ) Λ a`, `π = −(1 − ρₐ) κ Λ a`,
  `Λ = 1/((1 − βρₐ)(1 − ρₐ) + κ(φ_π − ρₐ)) > 0`: a positive technology shock
  opens a negative gap and lowers inflation, and output rises by less than
  natural output.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_7

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) Natural output -/

/-- **Natural output in levels** (Galí (2015), Ex. 3.7(a), p. 96): with flexible
prices `P = M W/A` (`M > 0` the desired gross markup), labour supply
`W/P = C N^φ` (log utility), `C = Y` and `Y = A N`, employment is
`N = M^{−1/(1+φ)}` and `log Y = log A − log M/(1 + φ)` exactly. -/
theorem natural_output_levels {φ M P W A C Y Nl : ℝ} (hφ : 0 ≤ φ) (hM : 0 < M) (hP : 0 < P)
    (hA : 0 < A) (hN : 0 < Nl) (hflex : P = M * (W / A)) (hls : W / P = C * Nl ^ φ)
    (hc : C = Y) (hy : Y = A * Nl) :
    Real.log Y = Real.log A - Real.log M / (1 + φ) := by
  have hWA : 0 < W / A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hA
    rwa [div_mul_cancel₀ W hA.ne'] at this
  have hW : W / P = A / M := by
    rw [hflex]; field_simp
  rw [hW, hc, hy] at hls
  have h1 := congrArg Real.log hls
  rw [Real.log_div hA.ne' hM.ne', Real.log_mul (mul_pos hA hN).ne'
    (Real.rpow_pos_of_pos hN φ).ne', Real.log_rpow hN, Real.log_mul hA.ne' hN.ne'] at h1
  rw [hy, Real.log_mul hA.ne' hN.ne', eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff
    (by linarith)]
  linear_combination -h1

/-- **Natural output in logs** (Galí (2015), Ex. 3.7(a), p. 96): flexible prices
`p = μ + w − a`, labour supply `w − p = c + φ n`, `c = y`, `n = y − a` give
`yⁿ = a − μ/(1 + φ)`: natural output moves one-for-one with technology. -/
theorem natural_output {φ μ p w a y n c : ℝ} (hφ : 0 ≤ φ) (hflex : p = μ + (w - a))
    (hls : w - p = c + φ * n) (hc : c = y) (hn : n = y - a) : y = a - μ / (1 + φ) := by
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff h1]
  subst hc hn
  linear_combination -hls - hflex

/-! ### The dynamic IS equation in gaps and the natural rate -/

/-- The natural rate of interest with log utility, `rⁿ_t = ρ + E_t a_{t+1} − a_t`
(Galí (2015), eq. (24), p. 63, with `σ = 1`, `ψ_ya = 1`). -/
noncomputable def naturalRate (ρ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + 𝔼.E t (a (t + 1)) - a t

/-- **The DIS in gaps** (Galí (2015), Ex. 3.7, eq. (41), p. 95, and eq. (23)): the
consumption Euler equation `y_t = E_t y_{t+1} − (i_t − E_t π_{t+1} − ρ)` with
`y = ỹ + yⁿ` and `yⁿ = a − const` gives
`ỹ_t = E_t ỹ_{t+1} − (i_t − E_t π_{t+1} − rⁿ_t)`. -/
theorem gap_dis {ρ c0 : ℝ} {y ytil yn a i infl : ℕ → Ω → ℝ}
    (heuler : ∀ t, y t = 𝔼.E t (y (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ))
    (hy : ∀ t, y t = ytil t + yn t) (hyn : ∀ t, yn t = a t - fun _ => c0) (t : ℕ) :
    ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - naturalRate 𝔼 ρ a t) := by
  have h := heuler t
  rw [hy, hy, hyn, hyn, map_add, map_sub, 𝔼.const] at h
  unfold naturalRate
  funext ω
  have h' := congrFun h ω
  simp only [Pi.add_apply, Pi.sub_apply] at h' ⊢
  linarith

/-- **Random-walk technology: a constant natural rate** (Galí (2015),
Ex. 3.7(b), p. 96): if `E_t a_{t+1} = a_t` then `rⁿ_t = ρ`. -/
theorem naturalRate_randomWalk {ρ : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 1 a) (t : ℕ) :
    naturalRate 𝔼 ρ a t = fun _ => ρ := by
  unfold naturalRate
  rw [ha.2 t, one_smul, add_sub_cancel_right]

/-- **AR(1) technology: a moving natural rate** (Galí (2015), Ex. 3.7(c),
p. 96): if `E_t a_{t+1} = ρₐ a_t` then `rⁿ_t = ρ − (1 − ρₐ) a_t`. -/
theorem naturalRate_ar1 {ρ ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    naturalRate 𝔼 ρ a t = (fun _ => ρ) - (1 - ρa) • a t := by
  unfold naturalRate
  rw [ha.2 t, sub_smul, one_smul]
  abel

/-! ### The system under the rule (43) -/

/-- `Ω = 1/(1 + κ φ_π)` (Galí (2015), eq. (27), p. 65, with `σ = 1`, `φ_y = 0`). -/
noncomputable def coefOmega (κ φπ : ℝ) : ℝ := 1 / (1 + κ * φπ)

/-- The matrix `A_T` of (27) with `σ = 1`, `φ_y = 0` (Galí (2015), p. 65):
`Ω [[1, 1 − βφ_π], [κ, κ + β]]`. -/
noncomputable def AT (β κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![coefOmega κ φπ, coefOmega κ φπ * (1 - β * φπ);
    coefOmega κ φπ * κ, coefOmega κ φπ * (κ + β)]

/-- The forcing term `B_T u_t = Ω [1, κ] u_t` (Galí (2015), eq. (27), p. 65). -/
noncomputable def forcing (κ φπ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![coefOmega κ φπ • u t, (coefOmega κ φπ * κ) • u t]

/-- The state vector `x_t = (ỹ_t, π_t)` (Galí (2015), eq. (27)). -/
def stack (ytil infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ytil t, infl t]

/-- **The model as a two-variable system** (Galí (2015), eq. (27), p. 65). If
`ỹ_t = E_t ỹ_{t+1} − (φ_π π_t − E_t π_{t+1}) + u_t` (the DIS with the rule (43)
substituted, `u = rⁿ − ρ`) and `π_t = β E_t π_{t+1} + κ ỹ_t` (42), then
`x_t = A_T E_t x_{t+1} + B_T u_t`. -/
theorem solves_of_model {β κ φπ : ℝ} (hΩ : 1 + κ * φπ ≠ 0) {ytil infl u : ℕ → Ω → ℝ}
    (hdis : ∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (φπ • infl t - 𝔼.E t (infl (t + 1))) + u t)
    (hpc : ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) :
    𝔼.Solves (AT β κ φπ) (forcing κ φπ u) (stack ytil infl) := by
  intro t i
  fin_cases i
  · funext ω
    have h1 := congrFun (hdis t) ω
    have h2 := congrFun (hpc t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    simp only [stack, forcing, AT, coefOmega, Fin.zero_eta, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h1 - φπ * h2
  · funext ω
    have h1 := congrFun (hdis t) ω
    have h2 := congrFun (hpc t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    simp only [stack, forcing, AT, coefOmega, Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination κ * h1 + h2

/-- The trace of `A_T`: `Ω(1 + κ + β)` (Galí (2015), p. 65). -/
theorem tr2_AT (β κ φπ : ℝ) : tr2 (AT β κ φπ) = coefOmega κ φπ * (1 + κ + β) := by
  simp [tr2, AT]
  ring

/-- The determinant of `A_T`: `β Ω` (Galí (2015), p. 65). -/
theorem det2_AT {β κ φπ : ℝ} (hΩ : 1 + κ * φπ ≠ 0) :
    det2 (AT β κ φπ) = β * coefOmega κ φπ := by
  simp [det2, AT, coefOmega]
  field_simp
  ring

/-- **Determinacy condition for the rule (43)** (Galí (2015), Ex. 3.7(b), p. 96;
eq. (28) with `φ_y = 0`): for `0 < β < 1`, `κ > 0` and `φ_π ≥ 0`, `A_T`
satisfies the Schur–Cohn condition if and only if `φ_π > 1`. -/
theorem schurStable_iff {β κ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 ≤ φπ) : SchurStable (tr2 (AT β κ φπ)) (det2 (AT β κ φπ)) ↔ 1 < φπ := by
  have hD : 0 < 1 + κ * φπ := by positivity
  rw [tr2_AT, det2_AT hD.ne']
  have hΩ : 0 < coefOmega κ φπ := by unfold coefOmega; positivity
  have hΩ1 : coefOmega κ φπ ≤ 1 := by
    unfold coefOmega; rw [div_le_one hD]; nlinarith
  have hΩe : coefOmega κ φπ * (1 + κ * φπ) = 1 := by unfold coefOmega; field_simp
  unfold SchurStable
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  constructor
  · rintro ⟨-, h⟩
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    exact ⟨by nlinarith, by nlinarith⟩

/-- **Determinacy iff `φ_π > 1`** (Galí (2015), Ex. 3.7(b), p. 96): bounded
adapted solutions of the system are unique exactly when `φ_π > 1`. -/
theorem determinate_iff_taylor [Nonempty Ω] {β κ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hφ : 0 ≤ φπ) : 𝔼.Determinate (AT β κ φπ) ↔ 1 < φπ := by
  rw [𝔼.determinate_iff, schurStable_iff hβ0 hβ1 hκ hφ]

/-- The DIS with the rule (43) substituted (Galí (2015), Ex. 3.7(b)):
`i = ρ + φ_π π` turns (41) into `ỹ_t = E_t ỹ_{t+1} − (φ_π π_t − E_t π_{t+1}) + (rⁿ_t − ρ)`. -/
theorem dis_with_rule {ρ φπ : ℝ} {ytil infl i rn : ℕ → Ω → ℝ}
    (hdis : ∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - rn t))
    (hrule : ∀ t, i t = (fun _ => ρ) + φπ • infl t) (t : ℕ) :
    ytil t = 𝔼.E t (ytil (t + 1)) - (φπ • infl t - 𝔼.E t (infl (t + 1)))
      + (rn t - fun _ => ρ) := by
  rw [hdis t, hrule t]
  abel

/-! ### (b) Random-walk technology -/

/-- **The equilibrium under a random walk** (Galí (2015), Ex. 3.7(b), p. 96).
With `rⁿ = ρ` (random-walk technology), the rule `i = ρ + φ_π π` with
`φ_π > 1`, the DIS (41) and the NKPC (42): (i) `ỹ = π = 0`, `i = ρ` is an
equilibrium; (ii) every bounded adapted equilibrium has `ỹ = π = 0`, hence
output equals natural output, `y = yⁿ = a − μ/(1 + φ)`, and `i = ρ`. -/
theorem randomWalk_equilibrium {ρ β κ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 1 < φπ) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 1 a) :
    ((∀ t, (0 : Ω → ℝ) = 𝔼.E t 0 - ((fun _ => ρ) - 𝔼.E t 0 - naturalRate 𝔼 ρ a t)) ∧
      ∀ t, (0 : Ω → ℝ) = β • 𝔼.E t 0 + κ • (0 : Ω → ℝ)) ∧
    ∀ ytil infl i : ℕ → Ω → ℝ,
      (∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - naturalRate 𝔼 ρ a t)) →
      (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) →
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) →
      𝔼.Adapted ytil → 𝔼.Adapted infl → BoundedProc ytil → BoundedProc infl →
      ∀ t, ytil t = 0 ∧ infl t = 0 ∧ i t = fun _ => ρ := by
  have hrn := naturalRate_randomWalk 𝔼 (ρ := ρ) ha
  refine ⟨⟨fun t => ?_, fun t => by simp⟩, ?_⟩
  · rw [hrn t, map_zero]; funext ω; simp
  intro ytil infl i hdis hpc hrule hya hia ⟨M₁, hM₁⟩ ⟨M₂, hM₂⟩ t
  have hD : 1 + κ * φπ ≠ 0 := by nlinarith
  have hsys := solves_of_model 𝔼 hD (u := fun t => naturalRate 𝔼 ρ a t - fun _ => ρ)
    (fun t => dis_with_rule 𝔼 hdis hrule t) hpc
  have hw : forcing κ φπ (fun t => naturalRate 𝔼 ρ a t - fun _ => ρ) = 0 := by
    funext s j
    simp only [forcing, hrn s, sub_self, smul_zero]
    fin_cases j <;> rfl
  rw [hw] at hsys
  have hz : 𝔼.Solves (AT β κ φπ) 0 (stack 0 0) := fun s j => by
    fin_cases j <;> simp [stack]
  have hS := (schurStable_iff hβ0 hβ1 hκ (by linarith)).mpr hφ
  have heq := 𝔼.system_unique hS hsys hz
    (fun s j => by fin_cases j <;> simp [stack, hya s, hia s])
    (fun s j => by fin_cases j <;> simp [stack])
    ⟨max M₁ M₂, fun s j ω => by
      fin_cases j
      · exact (hM₁ s ω).trans (le_max_left _ _)
      · exact (hM₂ s ω).trans (le_max_right _ _)⟩
    ⟨0, fun s j ω => by fin_cases j <;> simp [stack]⟩
  have hy : ytil t = 0 := congrFun (congrFun heq t) 0
  have hi : infl t = 0 := congrFun (congrFun heq t) 1
  refine ⟨hy, hi, ?_⟩
  rw [hrule t, hi, smul_zero, add_zero]

/-! ### (c) AR(1) technology -/

/-- `Λ = 1/((1 − βρₐ)(1 − ρₐ) + κ(φ_π − ρₐ))` (Galí (2015), eq. (29)–(30), p. 66,
with `σ = 1`, `φ_y = 0`). -/
noncomputable def lam (β κ φπ ρa : ℝ) : ℝ := 1 / ((1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa))

/-- `Λ > 0` when `φ_π > 1 > ρₐ` (Galí (2015), Ex. 3.7(c)). -/
theorem lam_pos {β κ φπ ρa : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 1 < φπ)
    (hρ1 : ρa < 1) : 0 < lam β κ φπ ρa := by
  unfold lam
  have : 0 < 1 - β * ρa := by nlinarith
  have : 0 < 1 - ρa := by linarith
  have : 0 < φπ - ρa := by linarith
  positivity

/-- **The equilibrium under AR(1) technology** (Galí (2015), Ex. 3.7(c), p. 96).
With `E_t a_{t+1} = ρₐ a_t`, `ρₐ < 1` (the book has `ρₐ ∈ (0,1)`), `a` bounded, and `φ_π > 1`:
(i) `ỹ = −(1 − ρₐ)(1 − βρₐ) Λ a`, `π = −(1 − ρₐ) κ Λ a`, `i = ρ + φ_π π` is an
equilibrium; (ii) it is the only bounded adapted one. -/
theorem ar1_equilibrium {ρ β κ φπ ρa : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) :
    let ys : ℕ → Ω → ℝ := fun t => (-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa) • a t
    let ps : ℕ → Ω → ℝ := fun t => (-(1 - ρa) * κ * lam β κ φπ ρa) • a t
    ((∀ t, ys t = 𝔼.E t (ys (t + 1))
        - (((fun _ => ρ) + φπ • ps t) - 𝔼.E t (ps (t + 1)) - naturalRate 𝔼 ρ a t)) ∧
      ∀ t, ps t = β • 𝔼.E t (ps (t + 1)) + κ • ys t) ∧
    ∀ ytil infl i : ℕ → Ω → ℝ,
      (∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - naturalRate 𝔼 ρ a t)) →
      (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) →
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) →
      𝔼.Adapted ytil → 𝔼.Adapted infl → BoundedProc ytil → BoundedProc infl →
      ytil = ys ∧ infl = ps := by
  intro ys ps
  have hrn := naturalRate_ar1 𝔼 (ρ := ρ) ha
  have hL := lam_pos hβ0 hβ1 hκ hφ hρ1
  have hLe : lam β κ φπ ρa * ((1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa)) = 1 := by
    have : 0 < 1 - β * ρa := by nlinarith
    have : 0 < 1 - ρa := by linarith
    have : 0 < φπ - ρa := by linarith
    have hX : 0 < (1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa) := by positivity
    unfold lam
    rw [one_div, inv_mul_cancel₀ hX.ne']
  have hEys : ∀ t, 𝔼.E t (ys (t + 1)) = ρa • ys t := fun t => by
    simp only [ys, map_smul, ha.2 t, smul_smul, mul_comm]
  have hEps : ∀ t, 𝔼.E t (ps (t + 1)) = ρa • ps t := fun t => by
    simp only [ps, map_smul, ha.2 t, smul_smul, mul_comm]
  have hmsv1 : ∀ t, ys t = 𝔼.E t (ys (t + 1))
      - (((fun _ => ρ) + φπ • ps t) - 𝔼.E t (ps (t + 1)) - naturalRate 𝔼 ρ a t) := by
    intro t
    rw [hEys, hEps, hrn]
    funext ω
    simp only [ys, ps, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(1 - ρa) * a t ω) * hLe
  have hmsv2 : ∀ t, ps t = β • 𝔼.E t (ps (t + 1)) + κ • ys t := by
    intro t
    rw [hEps]
    funext ω
    simp only [ys, ps, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨⟨hmsv1, hmsv2⟩, ?_⟩
  intro ytil infl i hdis hpc hrule hya hia ⟨M₁, hM₁⟩ ⟨M₂, hM₂⟩
  obtain ⟨Ma, hMa⟩ := hab
  have hD : 1 + κ * φπ ≠ 0 := by nlinarith
  set u : ℕ → Ω → ℝ := fun t => naturalRate 𝔼 ρ a t - fun _ => ρ with hu
  have hsys := solves_of_model 𝔼 hD (u := u) (fun t => dis_with_rule 𝔼 hdis hrule t) hpc
  have hsys' := solves_of_model 𝔼 hD (u := u) (ytil := ys) (infl := ps)
    (fun t => by
      have := hmsv1 t
      rw [this]
      funext ω
      simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring) hmsv2
  have hS := (schurStable_iff hβ0 hβ1 hκ (by linarith)).mpr hφ
  have hya' : 𝔼.Adapted ys := fun t => by simp only [ys, map_smul, ha.1 t]
  have hpa' : 𝔼.Adapted ps := fun t => by simp only [ps, map_smul, ha.1 t]
  have heq := 𝔼.system_unique hS hsys hsys'
    (fun s j => by fin_cases j <;> simp [stack, hya s, hia s])
    (fun s j => by fin_cases j <;> simp [stack, hya' s, hpa' s])
    ⟨max M₁ M₂, fun s j ω => by
      fin_cases j
      · exact (hM₁ s ω).trans (le_max_left _ _)
      · exact (hM₂ s ω).trans (le_max_right _ _)⟩
    ⟨(|-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa| + |-(1 - ρa) * κ * lam β κ φπ ρa|) * Ma,
      fun s j ω => by
        have h1 := abs_nonneg (-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa)
        have h2 := abs_nonneg (-(1 - ρa) * κ * lam β κ φπ ρa)
        have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans (hMa 0 ω)
        fin_cases j
        · change |(-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa) * a s ω| ≤ _
          rw [abs_mul]
          nlinarith [hMa s ω, abs_nonneg (a s ω)]
        · change |(-(1 - ρa) * κ * lam β κ φπ ρa) * a s ω| ≤ _
          rw [abs_mul]
          nlinarith [hMa s ω, abs_nonneg (a s ω)]⟩
  exact ⟨funext fun t => congrFun (congrFun heq t) 0, funext fun t => congrFun (congrFun heq t) 1⟩

/-- **Signs of the responses** (Galí (2015), Ex. 3.7(c), p. 96): the output-gap
and inflation coefficients on `a` are negative, and the output coefficient
`1 − (1 − ρₐ)(1 − βρₐ)Λ = κ(φ_π − ρₐ)Λ` lies in `(0, 1)`: output rises by less
than its natural level after a positive technology shock, unlike in (b). -/
theorem ar1_signs {β κ φπ ρa : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 1 < φπ)
    (hρ1 : ρa < 1) :
    -(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa < 0 ∧ -(1 - ρa) * κ * lam β κ φπ ρa < 0 ∧
      1 - (1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa = κ * (φπ - ρa) * lam β κ φπ ρa ∧
      0 < κ * (φπ - ρa) * lam β κ φπ ρa ∧ κ * (φπ - ρa) * lam β κ φπ ρa < 1 := by
  have hL := lam_pos hβ0 hβ1 hκ hφ hρ1
  have h1 : 0 < 1 - β * ρa := by nlinarith
  have h2 : 0 < 1 - ρa := by linarith
  have h3 : 0 < φπ - ρa := by linarith
  have hLe : lam β κ φπ ρa * ((1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa)) = 1 := by
    have hX : 0 < (1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa) := by positivity
    unfold lam
    rw [one_div, inv_mul_cancel₀ hX.ne']
  refine ⟨?_, ?_, ?_, by positivity, ?_⟩
  · have : 0 < (1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa := by positivity
    linarith
  · have : 0 < (1 - ρa) * κ * lam β κ φπ ρa := by positivity
    linarith
  · linear_combination -hLe
  · have : 0 < (1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa := by positivity
    nlinarith

end Gali.BasicNewKeynesianModel.Ex3_7

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.8: a New Keynesian economy with linear utility

Galí (2015), Chapter 3, Exercise 3.8, p. 96. Period utility
`U(C, N) = C − N^{1+φ}/(1 + φ)`, technology `Y = A N`, constant desired markup,
Calvo pricing, perfectly competitive labour market.

* (a) `natural_levels`, `natural_logs`: `nⁿ = (a − μ)/φ` and
  `yⁿ = ((1 + φ) a − μ)/φ`; `natural_employment_strictMono`: natural employment
  rises with technology (the claim illustrated by the diagram of (b)).
* (b) is a labour-market diagram; it is not formalised.
* (c) `euler_real_rate`: with constant marginal utility the Euler equation
  pins the expected real return at `1/β` at every date, i.e. `r = ρ`;
  `hasDerivAt_euler_path`: its exact linearisation is `i_t = ρ + E_t π_{t+1}`.
* (d) `natural_allocation_replicated`: under `i_t = ρ + φ_π π_t` with
  `φ_π > 1`, `π = ỹ = 0` (the natural allocation) with `i = ρ` is an
  equilibrium and it is the unique bounded one.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_8

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) Natural employment and output -/

/-- **Natural employment and output in levels** (Galí (2015), Ex. 3.8(a), p. 96):
with flexible prices `P = M W/A`, labour supply `W/P = N^φ` (the marginal rate of
substitution with linear utility) and `Y = A N`: `φ log N = log A − log M` and
`φ log Y = (1 + φ) log A − log M`, exactly. -/
theorem natural_levels {φ M P W A Y Nl : ℝ} (hφ : 0 < φ) (hM : 0 < M) (hP : 0 < P)
    (hA : 0 < A) (hN : 0 < Nl) (hflex : P = M * (W / A)) (hls : W / P = Nl ^ φ)
    (hy : Y = A * Nl) :
    Real.log Nl = (Real.log A - Real.log M) / φ ∧
      Real.log Y = ((1 + φ) * Real.log A - Real.log M) / φ := by
  have hWA : 0 < W / A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hA
    rwa [div_mul_cancel₀ W hA.ne'] at this
  have hW : W / P = A / M := by
    rw [hflex]; field_simp
  rw [hW] at hls
  have h1 := congrArg Real.log hls
  rw [Real.log_div hA.ne' hM.ne', Real.log_rpow hN] at h1
  have hn : Real.log Nl = (Real.log A - Real.log M) / φ := by
    rw [eq_div_iff hφ.ne']; linarith
  refine ⟨hn, ?_⟩
  rw [hy, Real.log_mul hA.ne' hN.ne', hn]
  field_simp
  ring

/-- **Natural employment and output in logs** (Galí (2015), Ex. 3.8(a), p. 96):
flexible prices `p = μ + w − a`, labour supply `w − p = φ n` and `y = a + n` give
`nⁿ = (a − μ)/φ` and `yⁿ = ((1 + φ) a − μ)/φ`. -/
theorem natural_logs {φ μ p w a y n : ℝ} (hφ : φ ≠ 0) (hflex : p = μ + (w - a))
    (hls : w - p = φ * n) (hy : y = a + n) :
    n = (a - μ) / φ ∧ y = ((1 + φ) * a - μ) / φ := by
  have hn : n = (a - μ) / φ := by
    rw [eq_div_iff hφ]; linarith
  refine ⟨hn, ?_⟩
  rw [hy, hn]
  field_simp
  ring

/-- **Natural employment always rises with technology** (Galí (2015),
Ex. 3.8(b), p. 96): `a ↦ (a − μ)/φ` is strictly increasing for `φ > 0`, because
with linear utility there is no wealth effect on labour supply. -/
theorem natural_employment_strictMono {φ : ℝ} (hφ : 0 < φ) (μ : ℝ) :
    StrictMono fun a : ℝ => (a - μ) / φ := by
  intro a b hab
  exact div_lt_div_of_pos_right (by linarith) hφ

/-! ### (c) The Euler equation and the real interest rate -/

/-- **A constant real interest rate** (Galí (2015), Ex. 3.8(c), p. 96). With
linear utility the marginal utility of consumption is `1` at every date, so the
Euler equation for a nominal bond reads
`1 = β (1 + i_t) E_t[P_t/P_{t+1}]`. Hence the expected gross real return is
`(1 + i_t) E_t[P_t/P_{t+1}] = 1/β` at every date, and its log is `ρ = −log β`,
whatever the path of consumption. -/
theorem euler_real_rate {β : ℝ} (hβ : 0 < β) {i P : ℕ → Ω → ℝ}
    (heuler : ∀ t ω, 1 = β * (1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω)
    (t : ℕ) (ω : Ω) :
    (1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω = 1 / β ∧
      Real.log ((1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) = -Real.log β := by
  have h := heuler t ω
  have hR : (1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω = 1 / β := by
    rw [eq_div_iff hβ.ne']; linarith
  refine ⟨hR, ?_⟩
  rw [hR, one_div, Real.log_inv]

/-- **Exact linearisation of the Euler equation** (Galí (2015), Ex. 3.8(c),
p. 96). Write `1 + i_t = exp(i_t)`, `P_t/P_{t+1} = exp(−π_{t+1})` and
`β = e^{−ρ}`, and perturb the steady state `i = ρ`, `π = 0` along
`i_t = ρ + s î`, `π_{t+1} = s π̂` with `π̂` bounded. The Euler residual
`β e^{i_t} E_t[e^{−π_{t+1}}]` has derivative `î − E_t π̂` at `s = 0`, so to first
order `i_t = ρ + E_t π_{t+1}`: the real rate `i_t − E_t π_{t+1}` equals `ρ`. -/
theorem hasDerivAt_euler_path {ρ B ihat : ℝ} {πhat : Ω → ℝ} (hπ : ∀ ω, |πhat ω| ≤ B)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => Real.exp (-ρ) * Real.exp (ρ + s * ihat) *
        𝔼.E t (fun ω' => Real.exp (s * -πhat ω')) ω)
      (ihat - 𝔼.E t πhat ω) 0 := by
  have hg := Ex3_5.hasDerivAt_E_exp 𝔼 (g := fun ω' => -πhat ω') (B := B)
    (fun ω' => by rw [abs_neg]; exact hπ ω') t ω 0
  have he : HasDerivAt (fun s : ℝ => Real.exp (ρ + s * ihat)) (Real.exp (ρ + 0 * ihat) * ihat) 0 :=
    by simpa using ((((hasDerivAt_id (0 : ℝ)).mul_const ihat).const_add ρ).exp)
  have h := (he.const_mul (Real.exp (-ρ))).mul hg
  refine h.congr_deriv ?_
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * -πhat ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have h2 : 𝔼.E t (fun ω' => -πhat ω' * Real.exp (0 * -πhat ω')) ω = -𝔼.E t πhat ω := by
    simp only [zero_mul, Real.exp_zero, mul_one]
    rw [show (fun ω' => -πhat ω') = -πhat from rfl, map_neg, Pi.neg_apply]
  have h3 : Real.exp (-ρ) * Real.exp ρ = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [h1, h2, zero_mul, add_zero]
  linear_combination (ihat - 𝔼.E t πhat ω) * h3

/-! ### (d) An interest-rate rule that replicates the natural allocation -/

/-- **The rule `i = ρ + φ_π π` replicates the natural allocation** (Galí (2015),
Ex. 3.8(d), p. 96). The equilibrium conditions are the linearised Euler
equation `i_t = ρ + E_t π_{t+1}` (part (c)) and the NKPC
`π_t = β E_t π_{t+1} + κ ỹ_t` with `κ > 0`. Under the rule
`i_t = ρ + φ_π π_t`, `φ_π > 1` (finite coefficients, observables only):
(i) `π = ỹ = 0`, `i = ρ` is an equilibrium; (ii) every equilibrium with bounded
adapted inflation has `π = 0` and `ỹ = 0`, so `y = yⁿ`, and `i = ρ`. The
reason: Euler and the rule give `π_t = φ_π⁻¹ E_t π_{t+1}`, whose only bounded
solution is zero. -/
theorem natural_allocation_replicated {ρ β κ φπ : ℝ} (hκ : 0 < κ) (hφ : 1 < φπ) :
    ((∀ t : ℕ, (fun _ => ρ) = ((fun _ => ρ) + 𝔼.E t (0 : Ω → ℝ) : Ω → ℝ)) ∧
      (∀ t : ℕ, (0 : Ω → ℝ) = β • 𝔼.E t 0 + κ • (0 : Ω → ℝ)) ∧
      ((fun _ => ρ) : Ω → ℝ) = (fun _ => ρ) + φπ • (0 : Ω → ℝ)) ∧
    ∀ ytil infl i : ℕ → Ω → ℝ,
      (∀ t, i t = (fun _ => ρ) + 𝔼.E t (infl (t + 1))) →
      (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) →
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) →
      BoundedProc infl → ∀ t, infl t = 0 ∧ ytil t = 0 ∧ i t = fun _ => ρ := by
  refine ⟨⟨fun t => by simp, fun t => by simp, by simp⟩, ?_⟩
  intro ytil infl i heuler hpc hrule hb
  have hφ0 : φπ ≠ 0 := by linarith
  have hfwd : ∀ t, infl t = φπ⁻¹ • 𝔼.E t (infl (t + 1)) + 0 := by
    intro t
    have h := (heuler t).symm.trans (hrule t)
    have h' : 𝔼.E t (infl (t + 1)) = φπ • infl t := add_left_cancel h
    rw [h', smul_smul, inv_mul_cancel₀ hφ0, one_smul, add_zero]
  have hzero : ∀ t, (0 : ℕ → Ω → ℝ) t = φπ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 :=
    fun t => by simp
  have ha : |φπ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]
    exact inv_lt_one_of_one_lt₀ hφ
  have h0 := 𝔼.forward_unique ha hfwd hzero hb ⟨0, fun t ω => by simp⟩
  intro t
  have hi : infl t = 0 := congrFun h0 t
  have hi1 : infl (t + 1) = 0 := congrFun h0 (t + 1)
  have hy : ytil t = 0 := by
    have h := hpc t
    rw [hi, hi1, map_zero, smul_zero, zero_add] at h
    have : κ • ytil t = 0 := h.symm
    exact (smul_eq_zero.mp this).resolve_left hκ.ne'
  refine ⟨hi, hy, ?_⟩
  rw [hrule t, hi, smul_zero, add_zero]

end Gali.BasicNewKeynesianModel.Ex3_8

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 3.9: the hybrid Phillips curve of Galí and Gertler

Galí (2015), Chapter 3, Exercise 3.9, pp. 96–97 (Galí and Gertler 1999). A
fraction `ω` of price setters follows the backward-looking rule
`p^b_t = p*_{t−1} + π_{t−1}`; the rest set `p^f_t` as in the standard model
(`α = 0`). The average new price is `p*_t = ω p^b_t + (1 − ω) p^f_t`, the price
level is `p_t = θ p_{t−1} + (1 − θ) p*_t`, and `μ̂_t = −(σ + φ) ỹ_t`.

* `forward_price_recursive`: the forward-looking price
  `p^f_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}` satisfies
  `p^f_t = (1 − βθ)(μ + ψ_t) + βθ E_t p^f_{t+1}` (for bounded marginal cost).
* (a) `hybrid_nkpc`: `π_t = γ_b π_{t−1} + γ_f E_t π_{t+1} + κ ỹ_t` with
  `γ_b = ω/φ̃`, `γ_f = βθ/φ̃`, `κ = (1 − ω)(1 − θ)(1 − βθ)(σ + φ)/φ̃`,
  `φ̃ = θ + ω(1 − θ(1 − β))`; `hybrid_nkpc_of_series` starts from the series
  form of `p^f`. `hybrid_standard`: `ω = 0` gives the standard NKPC;
  `gammas_sum`: `γ_b + γ_f = 1 − θ(1 − β)(1 − ω)/φ̃ ≤ 1`.
* (b) is a discussion of disinflation costs; it is not formalised.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_9

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Coefficients -/

/-- `φ̃ = θ + ω(1 − θ(1 − β))` (Galí (2015), Ex. 3.9(a), p. 97). -/
def phiTilde (β θ ω : ℝ) : ℝ := θ + ω * (1 - θ * (1 - β))

/-- The backward-looking coefficient `γ_b = ω/φ̃` (Galí (2015), Ex. 3.9(a)). -/
noncomputable def gammaB (β θ ω : ℝ) : ℝ := ω / phiTilde β θ ω

/-- The forward-looking coefficient `γ_f = βθ/φ̃` (Galí (2015), Ex. 3.9(a)). -/
noncomputable def gammaF (β θ ω : ℝ) : ℝ := β * θ / phiTilde β θ ω

/-- The slope `κ = (1 − ω)(1 − θ)(1 − βθ)(σ + φ)/φ̃` (Galí (2015), Ex. 3.9(a)). -/
noncomputable def kappaH (β θ ω σ φ : ℝ) : ℝ :=
  (1 - ω) * (1 - θ) * (1 - β * θ) * (σ + φ) / phiTilde β θ ω

/-- `φ̃ ≥ θ > 0` for `θ ∈ (0,1)`, `β ≥ 0`, `ω ≥ 0` (Galí (2015), Ex. 3.9(a)). -/
theorem phiTilde_pos {β θ ω : ℝ} (hβ0 : 0 ≤ β) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hω0 : 0 ≤ ω) : 0 < phiTilde β θ ω := by
  unfold phiTilde
  have : 0 < 1 - θ * (1 - β) := by nlinarith
  positivity

/-! ### The forward-looking price as a recursion -/

/-- A geometrically weighted series of uniformly bounded random variables
converges (Galí (2015), Ex. 3.9, p. 97). -/
theorem summable_geometric_bounded {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) : Summable fun k => a ^ k * y k ω := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)

/-- **`E_t` commutes with discounted sums of bounded random variables**
(Galí (2015), Ex. 3.9, p. 97; a local copy of the interchange used for eq. (11)):
`E_t[∑ₖ aᵏ yₖ] = ∑ₖ aᵏ E_t yₖ` for `|a| < 1`. `E_t` is monotone and preserves
constants, hence continuous for the uniform norm. -/
theorem E_tsum {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (t : ℕ) :
    𝔼.E t (fun ω => ∑' k, a ^ k * y k ω) = fun ω => ∑' k, a ^ k * 𝔼.E t (y k) ω := by
  funext ω
  set F : Ω → ℝ := fun ω => ∑' k, a ^ k * y k ω with hF
  set Fn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, a ^ k • y k with hFn
  set T : ℕ → ℝ := fun n => ∑' k, |a| ^ (k + n) * M with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add fun k => |a| ^ k * M
  have htail : ∀ n ω', |F ω' - Fn n ω'| ≤ T n := by
    intro n ω'
    have hs := summable_geometric_bounded ha hy ω'
    have hsplit := hs.sum_add_tsum_nat_add n
    have hFn' : Fn n ω' = ∑ k ∈ Finset.range n, a ^ k * y k ω' := by
      simp [hFn, Finset.sum_apply]
    rw [hFn']
    change |∑' k, a ^ k * y k ω' - _| ≤ T n
    rw [← hsplit, add_sub_cancel_left]
    have hs' : Summable fun k => a ^ (k + n) * y (k + n) ω' :=
      (summable_nat_add_iff n).mpr hs
    have hg : Summable fun k => |a| ^ (k + n) * M :=
      (summable_nat_add_iff n).mpr
        ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    calc |∑' k, a ^ (k + n) * y (k + n) ω'| ≤ ∑' k, |a ^ (k + n) * y (k + n) ω'| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => a ^ (k + n) * y (k + n) ω')
              (by simpa only [Real.norm_eq_abs] using hs'.abs)
      _ ≤ T n := by
          refine Summable.tsum_le_tsum (fun k => ?_) hs'.abs hg
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (hy (k + n) ω') (pow_nonneg (abs_nonneg a) _)
  have hEFn : ∀ n, 𝔼.E t (Fn n) ω = ∑ k ∈ Finset.range n, a ^ k * 𝔼.E t (y k) ω := by
    intro n
    simp [hFn, map_sum, map_smul, Finset.sum_apply]
  have hlim1 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop (𝓝 (𝔼.E t F ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hTlim
    have h := 𝔼.abs_E_le (x := F - Fn n) (fun ω' => htail n ω') t ω
    rw [map_sub, Pi.sub_apply] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have hbE : ∀ k ω', |𝔼.E t (y k) ω'| ≤ M := fun k ω' => 𝔼.abs_E_le (hy k) t ω'
  have hlim2 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop
      (𝓝 (∑' k, a ^ k * 𝔼.E t (y k) ω)) := by
    simp_rw [hEFn]
    exact (summable_geometric_bounded ha hbE ω).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The forward-looking price in recursive form** (Galí (2015), Ex. 3.9, p. 97,
and eq. (16), p. 60). If `p^f_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}` with `ψ`
adapted and uniformly bounded and `0 ≤ βθ < 1`, then
`p^f_t = (1 − βθ)(μ + ψ_t) + βθ E_t p^f_{t+1}`. -/
theorem forward_price_recursive {β θ μ : ℝ} (hb0 : 0 ≤ β * θ) (hb1 : β * θ < 1)
    {ψ pf : ℕ → Ω → ℝ} {M : ℝ} (hψ : ∀ t ω, |ψ t ω| ≤ M) (hψa : 𝔼.Adapted ψ)
    (hpf : ∀ t ω, pf t ω = μ + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + k)) ω)
    (t : ℕ) : pf t = (1 - β * θ) • ((fun _ => μ) + ψ t) + (β * θ) • 𝔼.E t (pf (t + 1)) := by
  have ha : |β * θ| < 1 := by rwa [abs_of_nonneg hb0]
  have hy : ∀ k ω, |𝔼.E (t + 1) (ψ (t + 1 + k)) ω| ≤ M :=
    fun k ω => 𝔼.bounded_E hψ (t + 1) (t + 1 + k) ω
  have hpf' : pf (t + 1) = (fun _ => μ) + (1 - β * θ) •
      fun ω => ∑' k, (β * θ) ^ k * 𝔼.E (t + 1) (ψ (t + 1 + k)) ω := by
    funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpf (t + 1) ω]
  have hE : 𝔼.E t (pf (t + 1)) = (fun _ => μ) + (1 - β * θ) •
      fun ω => ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + 1 + k)) ω := by
    rw [hpf', map_add, map_smul, 𝔼.const, E_tsum 𝔼 ha hy t]
    congr 2
    funext ω
    congr 1
    funext k
    rw [𝔼.tower (Nat.le_succ t)]
  rw [hE]
  funext ω
  have hs := summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hψ t (t + k) ω') ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpf t ω, hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, hψa t]
  have : ∑' k, (β * θ) ^ (k + 1) * 𝔼.E t (ψ (t + (k + 1))) ω
      = (β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + 1 + k)) ω := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [pow_succ, show t + (k + 1) = t + 1 + k by omega]
    ring
  rw [this]
  ring

/-! ### (a) The hybrid New Keynesian Phillips curve -/

/-- **The hybrid NKPC** (Galí (2015), Ex. 3.9(a), p. 97). Suppose, for all
dates, the backward-looking rule `p^b_{t+1} = p*_t + π_t`, the average new price
`p*_t = ω p^b_t + (1 − ω) p^f_t`, the forward-looking price in recursive form
`p^f_t = (1 − βθ)(μ + ψ_t) + βθ E_t p^f_{t+1}`, the price level
`p_{t+1} = θ p_t + (1 − θ) p*_{t+1}`, `π_{t+1} = p_{t+1} − p_t`, the markup
`μ_t = p_t − ψ_t` with `μ̂_t = μ_t − μ = −(σ + φ) ỹ_t`, and `p`, `p*` adapted.
Then from the third date on
`π_t = γ_b π_{t−1} + γ_f E_t π_{t+1} + κ ỹ_t`. -/
theorem hybrid_nkpc {β θ ω σ φ μ : ℝ} (hβ0 : 0 ≤ β) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hω0 : 0 ≤ ω) {p pstar pb pf ψ muhat ytil infl : ℕ → Ω → ℝ}
    (hpb : ∀ t, pb (t + 1) = pstar t + infl t)
    (hstar : ∀ t, pstar t = ω • pb t + (1 - ω) • pf t)
    (hpf : ∀ t, pf t = (1 - β * θ) • ((fun _ => μ) + ψ t) + (β * θ) • 𝔼.E t (pf (t + 1)))
    (hp : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hmu : ∀ t, muhat t = (p t - ψ t) - fun _ => μ)
    (hmuy : ∀ t, muhat t = -(σ + φ) • ytil t)
    (hpa : 𝔼.Adapted p) (hsa : 𝔼.Adapted pstar) (t : ℕ) :
    infl (t + 2) = gammaB β θ ω • infl (t + 1) + gammaF β θ ω • 𝔼.E (t + 2) (infl (t + 3))
      + kappaH β θ ω σ φ • ytil (t + 2) := by
  -- expectations of next-period variables
  have hEp : 𝔼.E (t + 2) (p (t + 3))
      = θ • p (t + 2) + (1 - θ) • 𝔼.E (t + 2) (pstar (t + 3)) := by
    rw [hp (t + 2), map_add, map_smul, map_smul, hpa (t + 2)]
  have hEs : 𝔼.E (t + 2) (pstar (t + 3))
      = ω • 𝔼.E (t + 2) (pb (t + 3)) + (1 - ω) • 𝔼.E (t + 2) (pf (t + 3)) := by
    rw [hstar (t + 3), map_add, map_smul, map_smul]
  have hEb : 𝔼.E (t + 2) (pb (t + 3)) = pstar (t + 2) + (p (t + 2) - p (t + 1)) := by
    have hk : 𝔼.E (t + 2) (p (t + 1)) = p (t + 1) := by
      rw [← hpa (t + 1), 𝔼.known (by omega)]
    rw [hpb (t + 2), hinfl (t + 1), map_add, map_sub, hsa (t + 2), hpa (t + 2), hk]
  have hEi : 𝔼.E (t + 2) (infl (t + 3)) = 𝔼.E (t + 2) (p (t + 3)) - p (t + 2) := by
    rw [hinfl (t + 2), map_sub, hpa (t + 2)]
  funext x
  have e1 := congrFun (hp t) x
  have e2 := congrFun (hp (t + 1)) x
  have e3 := congrFun (hpb (t + 1)) x
  have e3' := congrFun (hinfl t) x
  have e4 := congrFun (hstar (t + 2)) x
  have e5 := congrFun (hpf (t + 2)) x
  have e6 := congrFun (hmu (t + 2)) x
  have e7 := congrFun (hmuy (t + 2)) x
  have e8 := congrFun hEp x
  have e9 := congrFun hEs x
  have e10 := congrFun hEb x
  have e11 := congrFun hEi x
  have e12 := congrFun (hinfl (t + 1)) x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
    at e1 e2 e3 e3' e4 e5 e6 e7 e8 e9 e10 e11 e12 ⊢
  -- name the scalars
  set pm2 := p t x
  set pm1 := p (t + 1) x
  set p0 := p (t + 2) x
  set sm1 := pstar (t + 1) x
  set s0 := pstar (t + 2) x
  set b0 := pb (t + 2) x
  set f0 := pf (t + 2) x
  set Ef := 𝔼.E (t + 2) (pf (t + 3)) x
  set Eπ := 𝔼.E (t + 2) (infl (t + 3)) x
  set y0 := ytil (t + 2) x
  set πm1 := infl (t + 1) x
  set π0 := infl (t + 2) x
  -- the steps of the derivation
  have a1 : (1 - θ) * (sm1 - pm2) = πm1 := by linear_combination -e1 - e3'
  have a2 : (1 - θ) * (s0 - pm1) = π0 := by linear_combination -e2 - e12
  have a3 : (1 - θ) * (b0 - pm1) = πm1 := by linear_combination (1 - θ) * e3 + a1 + (1 - θ) * e3'
  have a4 : (1 - θ) * (𝔼.E (t + 2) (pb (t + 3)) x - p0) = π0 := by
    linear_combination (1 - θ) * e10 + a2
  have a5 : (1 - θ) * (𝔼.E (t + 2) (pstar (t + 3)) x - p0) = Eπ := by
    linear_combination -e8 - e11
  have hψ : ψ (t + 2) x = p0 - μ + (σ + φ) * y0 := by linear_combination e6 - e7
  have hF : f0 - pm1 = π0 + (1 - β * θ) * (σ + φ) * y0 + β * θ * (Ef - p0) := by
    linear_combination e5 + (1 - β * θ) * hψ - e12
  have g1 : π0 = ω * πm1 + (1 - ω) * (1 - θ) * (f0 - pm1) := by
    linear_combination (1 - θ) * e4 - a2 + ω * a3
  have g2 : Eπ = ω * π0 + (1 - ω) * (1 - θ) * (Ef - p0) := by
    linear_combination (1 - θ) * e9 - a5 + ω * a4
  have key : phiTilde β θ ω * π0 = ω * πm1 + β * θ * Eπ
      + (1 - ω) * (1 - θ) * (1 - β * θ) * (σ + φ) * y0 := by
    unfold phiTilde
    linear_combination g1 + (1 - ω) * (1 - θ) * hF - β * θ * g2
  have hφt := (phiTilde_pos hβ0 hθ0 hθ1 hω0).ne'
  unfold gammaB gammaF kappaH
  field_simp
  linear_combination key

/-- **The hybrid NKPC from the series form of `p^f`** (Galí (2015), Ex. 3.9(a),
p. 97): the same conclusion when `p^f_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}`
with `ψ` adapted and uniformly bounded. -/
theorem hybrid_nkpc_of_series {β θ ω σ φ μ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hω0 : 0 ≤ ω) {p pstar pb pf ψ muhat ytil infl : ℕ → Ω → ℝ} {M : ℝ}
    (hpb : ∀ t, pb (t + 1) = pstar t + infl t)
    (hstar : ∀ t, pstar t = ω • pb t + (1 - ω) • pf t)
    (hpf : ∀ t ω', pf t ω' = μ + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + k)) ω')
    (hψb : ∀ t ω', |ψ t ω'| ≤ M) (hψa : 𝔼.Adapted ψ)
    (hp : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hmu : ∀ t, muhat t = (p t - ψ t) - fun _ => μ)
    (hmuy : ∀ t, muhat t = -(σ + φ) • ytil t)
    (hpa : 𝔼.Adapted p) (hsa : 𝔼.Adapted pstar) (t : ℕ) :
    infl (t + 2) = gammaB β θ ω • infl (t + 1) + gammaF β θ ω • 𝔼.E (t + 2) (infl (t + 3))
      + kappaH β θ ω σ φ • ytil (t + 2) := by
  have hb0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0.le
  have hb1 : β * θ < 1 := by nlinarith
  exact hybrid_nkpc 𝔼 hβ0 hθ0 hθ1 hω0 hpb hstar
    (fun s => forward_price_recursive 𝔼 hb0 hb1 hψb hψa hpf s) hp hinfl hmu hmuy hpa hsa t

/-- **No backward-looking firms: the standard NKPC** (Galí (2015), Ex. 3.9(a),
and eq. (22), p. 63, with `α = 0`): at `ω = 0`, `γ_b = 0`, `γ_f = β` and
`κ = (1 − θ)(1 − βθ)(σ + φ)/θ`. -/
theorem hybrid_standard {β θ σ φ : ℝ} (hθ0 : 0 < θ) :
    gammaB β θ 0 = 0 ∧ gammaF β θ 0 = β ∧
      kappaH β θ 0 σ φ = (1 - θ) * (1 - β * θ) * (σ + φ) / θ := by
  unfold gammaB gammaF kappaH phiTilde
  refine ⟨by simp, ?_, by simp⟩
  simp only [zero_mul, add_zero]
  field_simp

/-- **`γ_b + γ_f ≤ 1`** (Galí (2015), Ex. 3.9(a)): exactly,
`γ_b + γ_f = 1 − θ(1 − β)(1 − ω)/φ̃`, since `φ̃ − ω − βθ = θ(1 − β)(1 − ω)`. -/
theorem gammas_sum {β θ ω : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    gammaB β θ ω + gammaF β θ ω = 1 - θ * (1 - β) * (1 - ω) / phiTilde β θ ω ∧
      gammaB β θ ω + gammaF β θ ω ≤ 1 := by
  have hφ := phiTilde_pos hβ0 hθ0 hθ1 hω0
  have heq : gammaB β θ ω + gammaF β θ ω = 1 - θ * (1 - β) * (1 - ω) / phiTilde β θ ω := by
    unfold gammaB gammaF
    field_simp
    unfold phiTilde
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have : 0 ≤ θ * (1 - β) * (1 - ω) / phiTilde β θ ω := by
    apply div_nonneg _ hφ.le
    apply mul_nonneg (mul_nonneg hθ0.le (by linarith)) (by linarith)
  linarith

end Gali.BasicNewKeynesianModel.Ex3_9

set_option linter.style.longLine false
#print axioms Gali.BasicNewKeynesianModel.durationProb
#print axioms Gali.BasicNewKeynesianModel.durationProb_nonneg
#print axioms Gali.BasicNewKeynesianModel.survival_sum
#print axioms Gali.BasicNewKeynesianModel.tail_sum
#print axioms Gali.BasicNewKeynesianModel.mean_duration
#print axioms Gali.BasicNewKeynesianModel.CalvoParam
#print axioms Gali.BasicNewKeynesianModel.CalvoParam.mk
#print axioms Gali.BasicNewKeynesianModel.CalvoParam.θ
#print axioms Gali.BasicNewKeynesianModel.CalvoParam.nonneg
#print axioms Gali.BasicNewKeynesianModel.CalvoParam.lt_one
#print axioms Gali.BasicNewKeynesianModel.CalvoParam.mean_duration
#print axioms Gali.BasicNewKeynesianModel.SchurStable
#print axioms Gali.BasicNewKeynesianModel.disc
#print axioms Gali.BasicNewKeynesianModel.root₁
#print axioms Gali.BasicNewKeynesianModel.root₂
#print axioms Gali.BasicNewKeynesianModel.root_sum
#print axioms Gali.BasicNewKeynesianModel.root_prod
#print axioms Gali.BasicNewKeynesianModel.root_eq
#print axioms Gali.BasicNewKeynesianModel.normSq_root_of_neg
#print axioms Gali.BasicNewKeynesianModel.norm_root_of_nonneg
#print axioms Gali.BasicNewKeynesianModel.schurStable_iff_roots
#print axioms Gali.BasicNewKeynesianModel.chSeq
#print axioms Gali.BasicNewKeynesianModel.convSeq
#print axioms Gali.BasicNewKeynesianModel.convSeq_rec
#print axioms Gali.BasicNewKeynesianModel.chSeq_eq_convSeq
#print axioms Gali.BasicNewKeynesianModel.norm_convSeq_le
#print axioms Gali.BasicNewKeynesianModel.abs_chSeq_le
#print axioms Gali.BasicNewKeynesianModel.tendsto_chSeq
#print axioms Gali.BasicNewKeynesianModel.tr2
#print axioms Gali.BasicNewKeynesianModel.det2
#print axioms Gali.BasicNewKeynesianModel.tr2_eq_trace
#print axioms Gali.BasicNewKeynesianModel.det2_eq_det
#print axioms Gali.BasicNewKeynesianModel.sq_eq_cayleyHamilton
#print axioms Gali.BasicNewKeynesianModel.pow_succ_eq
#print axioms Gali.BasicNewKeynesianModel.abs_pow_entry_le
#print axioms Gali.BasicNewKeynesianModel.tendsto_pow_entry
#print axioms Gali.BasicNewKeynesianModel.BoundedSeq
#print axioms Gali.BasicNewKeynesianModel.homogeneous_iterate
#print axioms Gali.BasicNewKeynesianModel.abs_mulVec_le
#print axioms Gali.BasicNewKeynesianModel.homogeneous_eq_zero
#print axioms Gali.BasicNewKeynesianModel.eq_root_of_eq
#print axioms Gali.BasicNewKeynesianModel.exists_eigenvector
#print axioms Gali.BasicNewKeynesianModel.exists_bounded_homogeneous
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.mk
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.E
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.const
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.mono
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.tower
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.known
#print axioms Gali.BasicNewKeynesianModel.perfectForesight
#print axioms Gali.BasicNewKeynesianModel.BoundedProc
#print axioms Gali.BasicNewKeynesianModel.BoundedVec
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.Adapted
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.IsAR1
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.E_neg
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.E_smul
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.E_E_self
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.abs_E_le
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.bounded_E
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.ar1_iterate
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.forward_iterate
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.forward_unique
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.forward_ar1_solves
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.Solves
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.AdaptedVec
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.system_iterate
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.system_unique
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.system_not_unique
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.Determinate
#print axioms Gali.BasicNewKeynesianModel.ExpectationSystem.determinate_iff
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.mk
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.prob
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.prob_pos
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.prob_sum
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.info
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.refines
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.mass
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.num
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.mass_pos
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.mass_congr
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.num_congr
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_congr
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_of_const_on_cell
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_add
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_smul
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condELin
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_const
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_mono
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_known
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_tower
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.FiniteTree.condE_of_trivial
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinObs
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinTree
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinSystem
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.firstHeads
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinSystem_E0_firstHeads
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinSystem_not_perfectForesight
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinShock
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinAR1
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinShock_measurable
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinAR1_measurable
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinShock_mean_zero
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinAR1_isAR1
#print axioms Gali.BasicNewKeynesianModel.ExpectationsFiniteTree.coinAR1_nondegenerate
#print axioms Gali.BasicNewKeynesianModel.CES.priceIndex
#print axioms Gali.BasicNewKeynesianModel.CES.cesAgg
#print axioms Gali.BasicNewKeynesianModel.CES.demand
#print axioms Gali.BasicNewKeynesianModel.CES.r_add_inv
#print axioms Gali.BasicNewKeynesianModel.CES.young_key
#print axioms Gali.BasicNewKeynesianModel.CES.young_le
#print axioms Gali.BasicNewKeynesianModel.CES.young_eq_iff
#print axioms Gali.BasicNewKeynesianModel.CES.priceIndex_pos
#print axioms Gali.BasicNewKeynesianModel.CES.priceIndex_rpow
#print axioms Gali.BasicNewKeynesianModel.CES.integral_relPrice_rpow
#print axioms Gali.BasicNewKeynesianModel.CES.integrable_relPrice_rpow
#print axioms Gali.BasicNewKeynesianModel.CES.cesAgg_demand
#print axioms Gali.BasicNewKeynesianModel.CES.price_mul_demand
#print axioms Gali.BasicNewKeynesianModel.CES.spend_demand
#print axioms Gali.BasicNewKeynesianModel.CES.cesAgg_nonneg
#print axioms Gali.BasicNewKeynesianModel.CES.cesAgg_rpow
#print axioms Gali.BasicNewKeynesianModel.CES.integrated_young
#print axioms Gali.BasicNewKeynesianModel.CES.spend_ge
#print axioms Gali.BasicNewKeynesianModel.CES.spend_eq_iff
#print axioms Gali.BasicNewKeynesianModel.CES.cesAgg_le_of_spend
#print axioms Gali.BasicNewKeynesianModel.CES.cesAgg_eq_iff_of_spend
#print axioms Gali.BasicNewKeynesianModel.CES.market_clearing
#print axioms Gali.BasicNewKeynesianModel.CES.integral_pos_of_pos
#print axioms Gali.BasicNewKeynesianModel.CES.unitInterval_ne_zero
#print axioms Gali.BasicNewKeynesianModel.CES.unitInterval_expenditure_minimisation
#print axioms Gali.BasicNewKeynesianModel.CES.Finite.weightMeasure
#print axioms Gali.BasicNewKeynesianModel.CES.Finite.weightMeasure_singleton
#print axioms Gali.BasicNewKeynesianModel.CES.Finite.weightMeasure_univ_lt_top
#print axioms Gali.BasicNewKeynesianModel.CES.Finite.integrable_weightMeasure
#print axioms Gali.BasicNewKeynesianModel.CES.Finite.integral_weightMeasure
#print axioms Gali.BasicNewKeynesianModel.CES.Finite.finite_expenditure_minimisation
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.integral_calvo_mix
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.calvo_recursion_of_dist
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.dist_law_of_motion
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.calvo_recursion
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.lottery_model
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.calvo_recursion_lottery
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.dist_k_step
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.prob_identity
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.prob_identity_range
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.dist_k_step_mass
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.rpow_eq_one_iff
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.zero_inflation_iff
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.zero_inflation_levels
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.inflFn
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.log_infl_eq_inflFn
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.inflFn_zero
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.hasDerivAt_inflFn
#print axioms Gali.BasicNewKeynesianModel.CalvoIndex.inflFn_isLittleO
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.bigTheta
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.crossVar
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.employment_level
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.employment_identity
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.one_lt_q
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.rpow_disp_eq
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.bernoulli_disp
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.integral_bernoulli_lower
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.one_le_integral_disp
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion_nonneg
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion_eq_zero_iff
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion_eq_zero_iff_const
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.integrable_exp_mul
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.interior_integrableExpSet
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.cgf_taylor
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.cgf_taylor_comp
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.priceIndex_family
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion_family_eq
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.crossVar_family
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion_second_order
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion_family_isBigO_sq
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.dispersion_family_first_order
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.relLogPrice
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.relLogPrice_moments
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.relLogPrice_mean_second_order
#print axioms Gali.BasicNewKeynesianModel.PriceDispersion.relLogPrice_sq_second_order
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.summable_geometric_bounded
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.abs_tsum_geometric_le
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.E_tsum
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.forwardSum
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.abs_forwardSum_le
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.forwardSum_bounded
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.forwardSum_rec
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.forwardSum_unique
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_E_of_remainder
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.remainder_le_of_lipschitz_deriv
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_E
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_tsum_E
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.markup
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.one_lt_markup
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.markup_pos
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.demand
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.demand_eq
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.demand_pos
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_demand
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.profit
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.objective
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focTerm
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focSum
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.profitDeriv
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_profit
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.E_profitDeriv
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_objective
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.foc_of_isLocalMax
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_objective_of_pos
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focCore
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focTerm_eq
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focCore_sub_ge
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.E_focCore_le
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.E_weight_nonneg
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.E_focCore_eq
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.isMaxOn_iff_foc
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.objective_flexible
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focSum_flexible
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.flexible_foc_iff
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.flexible_price_optimum
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.steadyState_foc_iff
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.logMarkup
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focLHS
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.focSum_eq_focLHS
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_E_exp
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_focLHS_path
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.eq11_iff
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.eq11_real_marginal_cost
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.normForward_rec
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.normForward_unique
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.normForward_const_add
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.resetPrice_recursive
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.reset_prob_sum
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.firmValue
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.resetValueRest
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.firmValue_eq
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.isMaxOn_firmValue_iff
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.Primitives
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.weight_bounds
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.demand_bounds
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.profitDeriv_eq
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.profitDeriv2
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_profitDeriv
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.abs_profitDeriv_le
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.abs_profitDeriv2_le
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.lipschitz_of_primitives
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.dominated_of_primitives
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.summable_profit_of_primitives
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.hasDerivAt_objective_of_primitives
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.foc_of_isLocalMax_of_primitives
#print axioms Gali.BasicNewKeynesianModel.ResetPrice.isMaxOn_iff_foc_of_primitives
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.employment
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.dispersion
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.eq14_exact
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.dispersion_symmetric
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.eq14
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.log_production
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.log_marginal_cost
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.log_demand
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.average_marginal_cost
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.log_aggregate_first_order
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.eq15
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.eq15_crs
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.Theta
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.Theta_pos
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.Theta_le_one
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.Theta_eq_one_iff
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.Theta_mul
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.markupGap
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.tsum_geom_affine
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.pstar_formula
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.forcing_bounded
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.forcing_adapted
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.eq16
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.eq16_unique
#print axioms Gali.BasicNewKeynesianModel.MarginalCost.eq16_of_eq11
#print axioms Gali.BasicNewKeynesianModel.NKPC.lam
#print axioms Gali.BasicNewKeynesianModel.NKPC.lam_pos
#print axioms Gali.BasicNewKeynesianModel.NKPC.eq17
#print axioms Gali.BasicNewKeynesianModel.NKPC.lam_strictAntiOn_theta
#print axioms Gali.BasicNewKeynesianModel.NKPC.Theta_strictAntiOn_alpha
#print axioms Gali.BasicNewKeynesianModel.NKPC.lam_strictAntiOn_alpha
#print axioms Gali.BasicNewKeynesianModel.NKPC.lam_strictAntiOn_eps
#print axioms Gali.BasicNewKeynesianModel.NKPC.lam_const_eps
#print axioms Gali.BasicNewKeynesianModel.NKPC.not_lam_strictAntiOn_eps
#print axioms Gali.BasicNewKeynesianModel.NKPC.nkpc_forward
#print axioms Gali.BasicNewKeynesianModel.NKPC.nkpc_forward_unique
#print axioms Gali.BasicNewKeynesianModel.NKPC.inflation_nonneg_of_markups_below
#print axioms Gali.BasicNewKeynesianModel.NKPC.fn4
#print axioms Gali.BasicNewKeynesianModel.NKPC.eq18
#print axioms Gali.BasicNewKeynesianModel.NKPC.psiYA
#print axioms Gali.BasicNewKeynesianModel.NKPC.psiY
#print axioms Gali.BasicNewKeynesianModel.NKPC.denom_pos
#print axioms Gali.BasicNewKeynesianModel.NKPC.eq19_iff_eq20
#print axioms Gali.BasicNewKeynesianModel.NKPC.psi_y_neg
#print axioms Gali.BasicNewKeynesianModel.NKPC.not_psi_y_pos
#print axioms Gali.BasicNewKeynesianModel.NKPC.logMarkup_pos
#print axioms Gali.BasicNewKeynesianModel.NKPC.psi_y_neg_at_markup
#print axioms Gali.BasicNewKeynesianModel.NKPC.psi_y_perfect_competition
#print axioms Gali.BasicNewKeynesianModel.NKPC.natural_output_lower
#print axioms Gali.BasicNewKeynesianModel.NKPC.eq21
#print axioms Gali.BasicNewKeynesianModel.NKPC.kappa
#print axioms Gali.BasicNewKeynesianModel.NKPC.kappa_pos
#print axioms Gali.BasicNewKeynesianModel.NKPC.eq22
#print axioms Gali.BasicNewKeynesianModel.NKPC.eq22_of_primitives
#print axioms Gali.BasicNewKeynesianModel.DIS.realRate
#print axioms Gali.BasicNewKeynesianModel.DIS.EulerOutput
#print axioms Gali.BasicNewKeynesianModel.DIS.psiYA
#print axioms Gali.BasicNewKeynesianModel.DIS.natOutput
#print axioms Gali.BasicNewKeynesianModel.DIS.natRate
#print axioms Gali.BasicNewKeynesianModel.DIS.DISGap
#print axioms Gali.BasicNewKeynesianModel.DIS.forward_sum
#print axioms Gali.BasicNewKeynesianModel.DIS.euler_forward_finite
#print axioms Gali.BasicNewKeynesianModel.DIS.euler_forward_ar1
#print axioms Gali.BasicNewKeynesianModel.DIS.euler_forward_tendsto
#print axioms Gali.BasicNewKeynesianModel.DIS.euler_forward_tsum
#print axioms Gali.BasicNewKeynesianModel.DIS.euler_forward_limit_zero
#print axioms Gali.BasicNewKeynesianModel.DIS.natRate_iff
#print axioms Gali.BasicNewKeynesianModel.DIS.natRate_ar1
#print axioms Gali.BasicNewKeynesianModel.DIS.euler_iff_disGap
#print axioms Gali.BasicNewKeynesianModel.DIS.gap_forward_tendsto
#print axioms Gali.BasicNewKeynesianModel.DIS.gap_forward_tsum
#print axioms Gali.BasicNewKeynesianModel.Household.utilC
#print axioms Gali.BasicNewKeynesianModel.Household.disutilN
#print axioms Gali.BasicNewKeynesianModel.Household.periodUtility
#print axioms Gali.BasicNewKeynesianModel.Household.hasDerivAt_utilC
#print axioms Gali.BasicNewKeynesianModel.Household.hasDerivAt_disutilN
#print axioms Gali.BasicNewKeynesianModel.Household.antitoneOn_margUtil
#print axioms Gali.BasicNewKeynesianModel.Household.le_tangent
#print axioms Gali.BasicNewKeynesianModel.Household.utilC_le_tangent
#print axioms Gali.BasicNewKeynesianModel.Household.disutilN_tangent_le
#print axioms Gali.BasicNewKeynesianModel.Household.static_foc_necessary
#print axioms Gali.BasicNewKeynesianModel.Household.static_isLocalMax_of_optimal
#print axioms Gali.BasicNewKeynesianModel.Household.static_foc_sufficient
#print axioms Gali.BasicNewKeynesianModel.Household.static_optimum_iff
#print axioms Gali.BasicNewKeynesianModel.Household.labour_supply_log_iff
#print axioms Gali.BasicNewKeynesianModel.Household.EulerEq
#print axioms Gali.BasicNewKeynesianModel.Household.eulerEq_ratio_form
#print axioms Gali.BasicNewKeynesianModel.Household.perturbedValue
#print axioms Gali.BasicNewKeynesianModel.Household.utility_gain_lower
#print axioms Gali.BasicNewKeynesianModel.Household.euler_necessary
#print axioms Gali.BasicNewKeynesianModel.Household.exists_expenditure_lower_bound
#print axioms Gali.BasicNewKeynesianModel.Household.euler_necessary_finite
#print axioms Gali.BasicNewKeynesianModel.Household.euler_sufficient
#print axioms Gali.BasicNewKeynesianModel.Household.eulerMoment
#print axioms Gali.BasicNewKeynesianModel.Household.eulerEq_iff_moment
#print axioms Gali.BasicNewKeynesianModel.Household.pf_eulerEq_iff
#print axioms Gali.BasicNewKeynesianModel.Household.pf_eulerEq_iff_noshock
#print axioms Gali.BasicNewKeynesianModel.Household.hasDerivAt_E_exp
#print axioms Gali.BasicNewKeynesianModel.Household.hasDerivAt_log_E_exp
#print axioms Gali.BasicNewKeynesianModel.Household.linearisedEuler
#print axioms Gali.BasicNewKeynesianModel.Household.eulerMoment_family_zero
#print axioms Gali.BasicNewKeynesianModel.Household.hasDerivAt_log_eulerMoment_family
#print axioms Gali.BasicNewKeynesianModel.Household.EulerLogLinear
#print axioms Gali.BasicNewKeynesianModel.Household.linearisedEuler_eq
#print axioms Gali.BasicNewKeynesianModel.Household.linearisedEuler_eq_zero_iff
#print axioms Gali.BasicNewKeynesianModel.Household.eulerLogLinear_add_const_iff
#print axioms Gali.BasicNewKeynesianModel.Household.pf_eulerEq_imp_eulerLogLinear
#print axioms Gali.BasicNewKeynesianModel.Household.eulerOutput_iff_of_clearing
#print axioms Gali.BasicNewKeynesianModel.Household.eulerOutput_of_eulerLogLinear
#print axioms Gali.BasicNewKeynesianModel.Household.pf_eulerEq_imp_eulerOutput
#print axioms Gali.BasicNewKeynesianModel.Household.employment_log_identity
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.NKPC
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.TaylorRule
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.TaylorRuleGap
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.taylorRule_iff_gap
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.shockU
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.Equilibrium
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.Structural
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.omega
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.AT
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.BT
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.stack
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.forcing
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.nk_iff_structural
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.structural_iff_solves
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.equilibrium_iff_solves
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.tr2_AT
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.det2_AT
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.schurStable_AT_iff
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.determinate_iff_BM
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.boundedVec_stack
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.adaptedVec_stack
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.equilibrium_unique
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.equilibrium_not_unique
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msvDen
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msvLambda
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msvPsiY
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msvPsiPi
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msvDen_eq
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msvDen_pos
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msvLambda_pos
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.isAR1_smul
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msv_structural
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.msv_unique
#print axioms Gali.BasicNewKeynesianModel.TaylorRuleSystem.equilibrium_iff_msv
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.boundedProc_smul
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.eq_msv_of_shock
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monYgapCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monInflCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monRealCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monNomCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monMoneyCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monetary_shock
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monetary_money_supply
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monetary_signs
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monNomCoef_neg_iff
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.money_bracket_eq
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.monMoneyCoef_neg_iff
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.money_contracts_of_nominal_rises
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.liquidity_effect_iff
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.liquidity_effect_of_nominal_rises
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.discount_shock
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.discount_eq_monetary
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.discount_rates_fall
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.discount_natRate_falls
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.discount_natRate_book_numbers
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techYgapCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techInflCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techOutputCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoef
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoefPrinted
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.technology_shock
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techOutput_eq
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.technology_output
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoef_eq
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.technology_employment
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoef_sub_printed
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoef_ne_printed
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techOutputCoef_mem
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techOutputCoef_counterexample
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techOutputCoef_unit_root
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoef_neg_iff
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoef_neg_of_one_le_sigma
#print axioms Gali.BasicNewKeynesianModel.ShockResponses.techNCoef_neg_of_phiy_large
#print axioms Gali.BasicNewKeynesianModel.Calibration.markup
#print axioms Gali.BasicNewKeynesianModel.Calibration.bigTheta
#print axioms Gali.BasicNewKeynesianModel.Calibration.lambdaNK
#print axioms Gali.BasicNewKeynesianModel.Calibration.kappaNK
#print axioms Gali.BasicNewKeynesianModel.Calibration.κ₀
#print axioms Gali.BasicNewKeynesianModel.Calibration.baselineCalvo
#print axioms Gali.BasicNewKeynesianModel.Calibration.markup_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.mean_duration_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.annual_return_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.frisch_and_phiy_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.bigTheta_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.lambda_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.kappa_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.bullardMitra_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.psiYA_one_of_sigma_one
#print axioms Gali.BasicNewKeynesianModel.Calibration.psiYA_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.monetary_signs_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.liquidity_effect_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.technology_baseline
#print axioms Gali.BasicNewKeynesianModel.Calibration.employment_baseline
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.NKPC
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.DIS
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.MoneyDemandGap
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.Eq32
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.RealBalanceId
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.Predetermined
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.eq31_of_money_demand
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.eq33_of_levels
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.dis_iff_eq32
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.AM0
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.AM1
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.BM
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.stateVec
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.expVec
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.shockVec
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.System34
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.system34_iff
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.model_iff_system34
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.charCubic
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.det_AM1_sub_smul_AM0
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.det_AM0
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.det_AM1
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.AM
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.det_AM_sub_smul
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.charpoly_AM_eval
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.isRoot_charpoly_AM_iff
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.charCubic_expand
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.charCubic_zero
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.charCubic_one
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.charCubic_signs
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.charCubic_root_gt_one
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.AM_has_eigenvalue_gt_one
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.det_AM
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.det_AM_pos_lt_one
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.BookDeterminacyClaim
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.moneyGrowth_isAR1
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.interest_rate_equation_raw
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.interest_rate_equation
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.E_tsum
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.forwardSeries
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.forwardSeries_summable
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.forwardSeries_solves
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.forwardSeries_bounded
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.eq_forwardSeries
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.rateForcing
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.rateForward
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.forwardSeries_rate_eq
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.rateForcing_adapted
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.rateForcing_bounded
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.interest_rate_forward_exists
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.interest_rate_forward_unique
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.interest_rate_log_utility
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.interest_rate_comoves
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.liquidity_effect_of_sigma_gt_one
#print axioms Gali.BasicNewKeynesianModel.MoneyRule.price_level_rule
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.cdf_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.prob_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.survival
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.survival_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.prob_window
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.memoryless
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.hazard_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.cond_change_prob
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.hazard_tendsto
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.mean_duration
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.median_duration
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.cdf_eq_half_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.median_div_mean
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.median_lt_mean
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.monthlyFreq
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.monthly_change_prob
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.lambda_eq_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.monthlyFreq_mem
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.lambda_lt_phi
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.quarterly_survival
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.quarterlyCalvo
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.quarterlyCalvo_theta
#print axioms Gali.BasicNewKeynesianModel.Ex3_1.quarterlyCalvo_mean_duration
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.govt_index_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.govt_index_eq_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.demand_add
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.total_demand
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.govt_total_demand
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.aggregate_output
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.shareG
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.shareG_log
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.one_sub_shareG
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.shareG_mem
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.hasFDerivAt_log_output
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.empl
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.realMC
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.logMC
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.log_realMC
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.hasFDerivAt_logMC
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.mc_coeff_g_neg
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.mc_coeff_y_ge
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.Euler
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.DISG
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.dis_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_2.dis_ar1_term
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.Goods.cesAgg_smul
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.Goods.goods_market_exact
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natural_output
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natural_output_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natural_consumption
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natOutput_multiplier_mem
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natCons_multiplier_neg
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.Euler
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.DISOutput
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natOutput
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natRate
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.DISGap
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.euler_iff_dis_output
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.dis_output_iff_gap
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.euler_iff_dis_gap
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natRate_eq_euler
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.natRate_ar1
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.NKPC
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.Rule
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.Equilibrium
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.A
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.stack
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.forcing
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.equilibrium_iff_solves
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.tr2_A
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.det2_A
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.schurStable_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.determinate_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.boundedVec_stack
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.adaptedVec_stack
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.cg
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.lam
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.lam_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.psiY
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.psiPi
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.isAR1_smul
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.bounded_smul
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.msv_equilibrium
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.equilibrium_iff_msv
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.equilibrium_not_unique
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.msv_responses_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_3.output_multiplier_bounds
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.priceIdx
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.dist_law_of_motion
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.integral_indexed_mix
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.indexed_recursion
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.inflFn
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.log_infl_eq_inflFn
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.inflFn_ss
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.PriceIndex.hasFDerivAt_inflFn
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.markup
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.demand
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.profit
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.objective
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.revFactor
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.costFactor
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.sumA
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.sumB
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.focSum
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.demand_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.profit_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.focTerm_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.objective_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.focSum_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.hasDerivAt_objective
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.foc_iff_closed
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.foc_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.value_le_at_closed
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.isMaxOn_iff_foc
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.hasDerivAt_E_exp
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.summable_succ_mul_geom
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.expSum
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.radius
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.radius_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.exp_le_of_lt_radius
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.abs_E_mul_exp_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.E_exp_bounds
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.expSum_summable_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.expSum_zero
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.hasDerivAt_expSum
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.summable_E_lin
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.hasDerivAt_logRatio
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.mk
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.β
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.θ
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.ε
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.ω
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.πbar
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.pbar
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.cbar
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.SteadyState.ψbar
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Deviation
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Deviation.mk
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Deviation.lam
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Deviation.price
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Deviation.cons
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Deviation.mc
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Deviation.infl
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.lamPath
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.pPath
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.cPath
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.psiPath
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.inflPath
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.xPath
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.xDev
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.aDev
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.bDev
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.xPath_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.revFactor_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.costFactor_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.sumA_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.sumB_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.logResetPrice
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.DevBounded
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.abs_xDev_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.abs_dev_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.logResetPrice_zero
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.hasDerivAt_logResetPrice
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.resetPrice_isMaxOn_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.lambdaNK
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.E_tsum_of_bound
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.shiftE
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Zrel
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Zrel_zero
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Zrel_succ
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.abs_Zrel_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Tsum
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.abs_Tsum_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.Tsum_rec
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.price_add
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.rule_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.hybrid_nkpc
#print axioms Gali.BasicNewKeynesianModel.Ex3_4.rule_of_hybrid_nkpc
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.markup
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.logMarkup
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.markup_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.one_sub_mul_markup
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.demand
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.cost
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.cost_eq_and_hasDerivAt
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.profit
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.objective
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.focTerm
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.focSum
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.wgt
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.demand_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.E_profit_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.E_focTerm_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.hasDerivAt_closedForm
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.hasDerivAt_objective
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.foc_of_isLocalMax
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.objective_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.focSum_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.isMaxOn_iff_foc
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.printedFocSum
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.printed_foc_counterexample
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.hasDerivAt_E_of_remainder
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.hasDerivAt_E_exp
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.focLHS
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.focSum_eq_focLHS
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.hasDerivAt_focLHS_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorWeight
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.one_le_geomSum
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorWeight_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.sum_taylorWeight
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorWeight_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorWeight_one
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.tendsto_taylorWeight
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.pricing_rule_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.pricing_rule_iff_undiscounted
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.priceIndex
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.log_priceIndex_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.log_priceIndex_steady
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.hasDerivAt_log_priceIndex
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.natural_output_levels
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.natural_output
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.psi_eq_gap
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylor_two_period_rule
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.SolvesPre
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.ar1Path
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.ar1Path_adapted
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.ar1Path_bounded
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.predetermined_solves
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.predetermined_unique
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.ar1Path_closed
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorRoot
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorCoeff
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorCoeff_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.one_sub_taylor_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylor_gamma
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.abs_taylorRoot_lt_one
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.gap_equation
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorPath
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylor_equilibrium
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.z_innovation
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.z_randomWalk
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorPath_closed
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylor_gap_closed
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylor_model_closed_form
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorRoot_strictAntiOn
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorRoot_pos_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorRoot_one
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.taylorRoot_neg
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.tendsto_taylorRoot_zero
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.gapIRF
#print axioms Gali.BasicNewKeynesianModel.Ex3_5.gapIRF_lt
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.priceIndex
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.exp_vintage_le
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.summable_vintage
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.vintage_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.log_priceIndex_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.tsum_shares
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.hasDerivAt_log_priceIndex
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.log_priceIndex_steady
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.log_marginal_cost
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.planObjective
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.planObjective_update
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.plan_foc_of_isLocalMax
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.plan_hasDerivAt_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.plan_rule_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.natural_output_levels
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.natural_output
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.mc_eq_gap
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.summable_geom_E
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.price_level_eq
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.eq40
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.price_level_randomWalk
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.summable_lagged
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.price_level_rec
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.cumInnov
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.cumInnov_succ
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.sticky_info_closed_form
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.output_employment
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.nkpcRoot
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.nkpcRoot_quadratic
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.nkpcRoot_mem
#print axioms Gali.BasicNewKeynesianModel.Ex3_6.nkpc_comparison
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.natural_output_levels
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.natural_output
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.naturalRate
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.gap_dis
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.naturalRate_randomWalk
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.naturalRate_ar1
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.coefOmega
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.AT
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.forcing
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.stack
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.solves_of_model
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.tr2_AT
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.det2_AT
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.schurStable_iff
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.determinate_iff_taylor
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.dis_with_rule
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.randomWalk_equilibrium
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.lam
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.lam_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.ar1_equilibrium
#print axioms Gali.BasicNewKeynesianModel.Ex3_7.ar1_signs
#print axioms Gali.BasicNewKeynesianModel.Ex3_8.natural_levels
#print axioms Gali.BasicNewKeynesianModel.Ex3_8.natural_logs
#print axioms Gali.BasicNewKeynesianModel.Ex3_8.natural_employment_strictMono
#print axioms Gali.BasicNewKeynesianModel.Ex3_8.euler_real_rate
#print axioms Gali.BasicNewKeynesianModel.Ex3_8.hasDerivAt_euler_path
#print axioms Gali.BasicNewKeynesianModel.Ex3_8.natural_allocation_replicated
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.phiTilde
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.gammaB
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.gammaF
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.kappaH
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.phiTilde_pos
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.summable_geometric_bounded
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.E_tsum
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.forward_price_recursive
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.hybrid_nkpc
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.hybrid_nkpc_of_series
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.hybrid_standard
#print axioms Gali.BasicNewKeynesianModel.Ex3_9.gammas_sum
