/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LinearSystems

/-!
# A root of (A.9) on the unit circle: non-existence, for any `f₃`

Woodford (2003), *Interest and Prices*, Appendix A.3, eq. (A.9), p. 632. `LinearSystems` proves
that a root of `det(f₃λ² + f₂λ + f₁)` on the unit circle destroys invertibility of (A.8), and,
for invertible `f₃`, that existence fails (`LinearSystems.not_surjective_of_unit`, through the
companion matrix). This module proves the non-existence half **for arbitrary `f₃`**, singular
or not, and even for a singular pencil, directly by resonance on the second-order system: if
`det(f₃μ² + f₂μ + f₁) = 0` with `|μ| = 1` and `q` is a left null vector, then along any solution
`y_t = a x_t + d x_{t−1}` (`a = q f₃`, `d = q(f₂ + μ f₃)`) satisfies
`y_{t+1} = μ y_t + q · w_t`; for the bounded forcing `w_t = Re(μ^{t+1} q̄)` the sequence
`μ̄ᵗ y_t` grows linearly, so no bounded solution exists. (A unit root can come with
non-uniqueness as well, but existence always fails; there is no dichotomy.)

* `resonance_scalar`: the scalar growth argument.
* `exists_null_unit`: a left null vector of `μ²f₃ + μf₂ + f₁`, real when `μ = ±1`.
* `not_surjective_of_unit_det`, `not_surjective_of_unit_root` (**the theorem**): a unit-circle
  root gives a bounded forcing (with `x_{−1} = 0`) for which (A.10) has no bounded solution.
* `failure_cases_general`: the classification of `LinearSystems.failure_cases` without the
  hypothesis `det f₃ ≠ 0`.
-/

namespace Woodford.PriceLevelDetermination.LinearSystemsUnit

open Polynomial LinearSystems
open scoped Matrix ComplexConjugate

/-- Woodford (2003), App. A.3, p. 632 (**scalar resonance**): if `‖μ‖ = 1`, `N > 0`
(`σ = N` when `μ² = 1`) and `y_{t+1} = μ y_t + (μ^{t+1} N + μ̄^{t+1} σ)/2`, then `y` is
unbounded. (The argument of `SystemsBK.GeneralBK.no_bounded_resonance`, restated for a scalar
sequence.) -/
theorem resonance_scalar {μ : ℂ} (hμ : ‖μ‖ = 1) {N : ℝ} (hN0 : 0 < N) {σ : ℂ}
    (hre : μ ^ 2 = 1 → σ = N) {m : ℕ → ℂ}
    (hm_succ : ∀ t, m (t + 1) = μ * m t + (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2)
    {Q : ℝ} (hmQ : ∀ t, ‖m t‖ ≤ Q) : False := by
  set ζ : ℂ := conj μ ^ 2 with hζ
  have hμc : μ * conj μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ]
    norm_num
  set d : ℕ → ℂ := fun t => m t * conj μ ^ t with hd
  have hd_succ : ∀ t, d (t + 1) = d t + ((N : ℂ) + σ * ζ ^ (t + 1)) / 2 := by
    intro t
    have h1 : μ ^ (t + 1) * conj μ ^ (t + 1) = 1 := by rw [← mul_pow, hμc, one_pow]
    have h2 : μ * conj μ ^ (t + 1) = conj μ ^ t := by
      rw [pow_succ]
      linear_combination (conj μ ^ t) * hμc
    have h3 : conj μ ^ (t + 1) * conj μ ^ (t + 1) = ζ ^ (t + 1) := by
      rw [hζ, ← pow_mul, ← pow_add]
      ring_nf
    simp only [hd]
    rw [hm_succ t]
    linear_combination (m t) * h2 + ((N : ℂ) / 2) * h1 + (σ / 2) * h3
  set S : ℕ → ℂ := fun T => ∑ s ∈ Finset.range T, ζ ^ (s + 1) with hS
  have hd_closed : ∀ T : ℕ, d T = d 0 + ((T * N / 2 : ℝ) : ℂ) + σ / 2 * S T := by
    intro T
    induction T with
    | zero => simp [hS]
    | succ T ih =>
      rw [hd_succ T, ih]
      simp only [hS, Finset.sum_range_succ]
      push_cast
      ring
  have hdQ : ∀ T, ‖d T‖ ≤ Q := by
    intro T
    simp only [hd, norm_mul, norm_pow, Complex.norm_conj, hμ, one_pow, mul_one]
    exact hmQ T
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ T, -K ≤ (σ / 2 * S T).re := by
    by_cases hζ1 : ζ = 1
    · have hμ2 : μ ^ 2 = 1 := by
        have := congrArg conj hζ1
        rw [hζ, map_pow, Complex.conj_conj, map_one] at this
        exact this
      have hσN := hre hμ2
      refine ⟨0, fun T => ?_⟩
      have hST : S T = (T : ℂ) := by simp [hS, hζ1]
      rw [hσN, hST]
      have : ((N : ℂ) / 2 * (T : ℂ)).re = N / 2 * T := by
        rw [show ((N : ℂ) / 2 * (T : ℂ)) = ((N / 2 * T : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
      rw [this]
      have : 0 ≤ N / 2 * T := by positivity
      linarith
    · have hζn : ‖ζ‖ = 1 := by rw [hζ, norm_pow, Complex.norm_conj, hμ, one_pow]
      refine ⟨‖σ‖ / ‖ζ - 1‖, fun T => ?_⟩
      have hSb : ‖S T‖ ≤ 2 / ‖ζ - 1‖ := by
        have e : S T = ζ * ((ζ ^ T - 1) / (ζ - 1)) := by
          rw [hS, ← geom_sum_eq hζ1 T, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        rw [e, norm_mul, hζn, one_mul, norm_div]
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖ζ ^ T - 1‖ ≤ ‖ζ ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hζn, one_pow, norm_one]; norm_num
      have hb : ‖σ / 2 * S T‖ ≤ ‖σ‖ / ‖ζ - 1‖ := by
        rw [norm_mul, norm_div, Complex.norm_two]
        calc ‖σ‖ / 2 * ‖S T‖ ≤ ‖σ‖ / 2 * (2 / ‖ζ - 1‖) :=
              mul_le_mul_of_nonneg_left hSb (by positivity)
          _ = ‖σ‖ / ‖ζ - 1‖ := by ring
      have := Complex.abs_re_le_norm (σ / 2 * S T)
      have := neg_abs_le (σ / 2 * S T).re
      linarith
  refine SystemsBK.GeneralBK.false_of_linear_growth (a := (d 0).re) (c := N / 2) (K := K)
    (Q := Q) (by positivity) fun T => ?_
  have h1 : (d T).re = (d 0).re + T * N / 2 + (σ / 2 * S T).re := by
    rw [hd_closed T, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  have h2 : (d T).re ≤ Q := (Complex.re_le_norm _).trans (hdQ T)
  have h3 := hK T
  have : (T : ℝ) * (N / 2) = T * N / 2 := by ring
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), eq. (A.9), p. 632: the complex matrix `μ²f₃ + μf₂ + f₁`. -/
noncomputable def quadMat (f₁ f₂ f₃ : Matrix ι ι ℝ) (μ : ℂ) : Matrix ι ι ℂ :=
  μ ^ 2 • f₃.map Complex.ofReal + μ • f₂.map Complex.ofReal + f₁.map Complex.ofReal

/-- Woodford (2003), eq. (A.9), p. 632: a root `μ` of the characteristic polynomial makes
`μ²f₃ + μf₂ + f₁` singular. -/
theorem det_quadMat_of_root {f₁ f₂ f₃ : Matrix ι ι ℝ} {μ : ℂ}
    (hμ : μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots) :
    (quadMat f₁ f₂ f₃ μ).det = 0 := by
  have hroot := (mem_roots'.mp hμ).2
  rw [IsRoot, eval_map, ← coe_eval₂RingHom, quadPoly, RingHom.map_det] at hroot
  rw [← hroot]
  congr 1
  rw [map_add, map_add, map_mul, map_mul]
  ext i j
  simp [quadMat, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply]

/-- Woodford (2003), eq. (A.9), p. 632 (tool): a singular `μ²f₃ + μf₂ + f₁` has a nonzero left
null vector, which can be taken real when `μ² = 1`. -/
theorem exists_null_unit {f₁ f₂ f₃ : Matrix ι ι ℝ} {μ : ℂ} (hdet : (quadMat f₁ f₂ f₃ μ).det = 0) :
    ∃ q : ι → ℂ, q ≠ 0 ∧ q ᵥ* quadMat f₁ f₂ f₃ μ = 0 ∧ (μ ^ 2 = 1 → ∀ i, (q i).im = 0) := by
  by_cases h2 : μ ^ 2 = 1
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, μ = (r : ℂ) := by
      have : (μ - 1) * (μ + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp this with e | e
      · exact ⟨1, by push_cast; linear_combination e⟩
      · exact ⟨-1, by push_cast; linear_combination e⟩
    set R : Matrix ι ι ℝ := r ^ 2 • f₃ + r • f₂ + f₁ with hR
    have hmap : quadMat f₁ f₂ f₃ μ = R.map Complex.ofReal := by
      ext i j
      simp [quadMat, hR, hr]
    have hdetR : R.det = 0 := by
      have e := RingHom.map_det Complex.ofRealHom R
      have e2 : Complex.ofRealHom.mapMatrix R = R.map Complex.ofReal := rfl
      rw [e2, ← hmap, hdet] at e
      exact Complex.ofReal_eq_zero.mp e
    obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdetR
    refine ⟨fun i => (p i : ℂ), ?_, ?_, fun _ i => by simp⟩
    · intro h
      apply hp0
      funext i
      have := congrFun h i
      simpa using this
    · rw [hmap]
      funext j
      have hj := congrFun hp j
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply] at hj ⊢
      exact_mod_cast hj
  · obtain ⟨q, hq0, hq⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    exact ⟨q, hq0, hq, fun h => absurd h h2⟩

omit [DecidableEq ι] in
/-- Woodford (2003), eq. (A.10), p. 633 (tool): the complexification of a real matrix-vector
product, dotted with `q`. -/
theorem dot_cast_mulVec (q : ι → ℂ) (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    q ⬝ᵥ (fun i => ((M *ᵥ v) i : ℂ)) = (q ᵥ* M.map Complex.ofReal) ⬝ᵥ (fun i => (v i : ℂ)) := by
  rw [← Matrix.dotProduct_mulVec, SystemsBK.GeneralBK.map_ofReal_mulVec]

omit [DecidableEq ι] in
/-- Woodford (2003), eq. (A.10), p. 633 (tool): `‖u ⬝ v‖ ≤ (∑‖uᵢ‖) B` when `|vᵢ| ≤ B`. -/
theorem norm_dot_le (u : ι → ℂ) {v : ι → ℝ} {B : ℝ} (hv : ∀ i, |v i| ≤ B) :
    ‖u ⬝ᵥ (fun i => (v i : ℂ))‖ ≤ (∑ i, ‖u i‖) * B := by
  rw [dotProduct, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)

/-- **A unit-circle root gives non-existence, for any `f₃`** (Woodford (2003), App. A.3,
eqs. (A.9)–(A.10), pp. 632–633): if `det(f₃μ² + f₂μ + f₁) = 0` with `|μ| = 1` — `f₃` arbitrary,
even with `det(f₃λ² + f₂λ + f₁) ≡ 0` — then for the bounded forcing `w_t = Re(μ^{t+1} q̄)`
(`q` a left null vector) the linearised system (A.10) with `x_{−1} = 0` has no bounded solution:
the derivative operator (A.8) is not surjective. -/
theorem not_surjective_of_unit_det {f₁ f₂ f₃ : Matrix ι ι ℝ} {μ : ℂ}
    (hdet : (quadMat f₁ f₂ f₃ μ).det = 0) (h1 : ‖μ‖ = 1) :
    ¬ Function.Surjective (sysOp f₁ f₂ f₃) := by
  intro hs
  obtain ⟨q, hq0, hq, hre⟩ := exists_null_unit hdet
  set w : ℕ → ι → ℝ := fun t i => (μ ^ (t + 1) * conj (q i)).re with hw
  have hwb : LinearSystems.BoundedSeq w := ⟨∑ i, ‖q i‖, fun t i => by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, h1, one_pow, one_mul, Complex.norm_conj]
    exact Finset.single_le_sum (f := fun i => ‖q i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)⟩
  obtain ⟨x, hx⟩ := hs (toSeqV w hwb)
  have hsol := (sysOp_eq_iff _ _ _ _ _).mp hx
  obtain ⟨B, hB⟩ := boundedSeq_coe x
  have hBl : ∀ t i, |lagV 0 (fun s => x s) t i| ≤ B := fun t i => by
    cases t with
    | zero => simpa using (abs_nonneg (x 0 i)).trans (hB 0 i)
    | succ t => exact hB t i
  set N : ℝ := ∑ i, ‖q i‖ ^ 2 with hN
  set σ : ℂ := ∑ i, q i ^ 2 with hσ
  have hN0 : 0 < N := by
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hq0 (funext hne)
    exact Finset.sum_pos' (fun i _ => by positivity)
      ⟨i, Finset.mem_univ i, by have := norm_pos_iff.mpr hi; positivity⟩
  have hNc : (N : ℂ) = ∑ i, q i * conj (q i) := by
    rw [hN]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hqw : ∀ t, q ⬝ᵥ (fun i => (w t i : ℂ)) =
      (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2 := by
    intro t
    rw [dotProduct, hNc, hσ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw, Complex.re_eq_add_conj, map_mul, map_pow, Complex.conj_conj]
    ring
  have hσN : μ ^ 2 = 1 → σ = N := fun h => by
    have hreal := hre h
    rw [hσ, hNc]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hqi : q i = ((q i).re : ℂ) := Complex.ext rfl (by simp [hreal i])
    rw [hqi, Complex.conj_ofReal]
    ring
  -- the resonant combination `y_t = a x_t + d x_{t−1}`
  set a : ι → ℂ := q ᵥ* f₃.map Complex.ofReal with ha
  set b : ι → ℂ := q ᵥ* f₂.map Complex.ofReal with hb
  set c : ι → ℂ := q ᵥ* f₁.map Complex.ofReal with hc
  set d : ι → ℂ := b + μ • a with hd
  have hnull : μ • d + c = 0 := by
    have e : q ᵥ* quadMat f₁ f₂ f₃ μ = μ ^ 2 • a + μ • b + c := by
      simp only [quadMat, Matrix.vecMul_add, Matrix.vecMul_smul, ha, hb, hc]
    rw [hq] at e
    rw [hd, smul_add, smul_smul, ← pow_two, e]
    abel
  set y : ℕ → ℂ := fun t => a ⬝ᵥ (fun i => (x t i : ℂ)) +
    d ⬝ᵥ (fun i => (lagV 0 (fun s => x s) t i : ℂ)) with hy
  refine resonance_scalar h1 hN0 hσN (m := y) (fun t => ?_) (Q := (∑ i, ‖a i‖) * B +
    (∑ i, ‖d i‖) * B) fun t => (norm_add_le _ _).trans
      (add_le_add (norm_dot_le a (hB t)) (norm_dot_le d (hBl t)))
  have heq : c ⬝ᵥ (fun i => (lagV 0 (fun s => x s) t i : ℂ)) + b ⬝ᵥ (fun i => (x t i : ℂ)) +
      a ⬝ᵥ (fun i => (x (t + 1) i : ℂ)) = q ⬝ᵥ (fun i => (w t i : ℂ)) := by
    have e := congrArg (fun v : ι → ℝ => q ⬝ᵥ (fun i => (v i : ℂ))) (hsol t)
    simp only [Pi.add_apply, Complex.ofReal_add, toSeqV_apply] at e
    rw [← dot_cast_mulVec, ← dot_cast_mulVec, ← dot_cast_mulVec, ← e]
    simp only [dotProduct, ← Finset.sum_add_distrib, mul_add]
  rw [← hqw t, ← heq]
  simp only [hy, lagV_succ, hd, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hc' : c = -(μ • d) := eq_neg_of_add_eq_zero_right hnull
  rw [hc', hd, neg_dotProduct, smul_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  ring

/-- **A unit-circle root of (A.9) gives non-existence, for any `f₃`** (Woodford (2003), App. A.3,
eq. (A.9), p. 632): if some root of `det(f₃λ² + f₂λ + f₁)` lies on the unit circle, some bounded
forcing (with `x_{−1} = 0`) admits no bounded solution of (A.10). This extends
`LinearSystems.not_surjective_of_unit` to singular `f₃`. -/
theorem not_surjective_of_unit_root {f₁ f₂ f₃ : Matrix ι ι ℝ} {μ : ℂ}
    (hμ : μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots) (h1 : ‖μ‖ = 1) :
    ¬ Function.Surjective (sysOp f₁ f₂ f₃) :=
  not_surjective_of_unit_det (det_quadMat_of_root hμ) h1

/-- **Which half fails, for any `f₃`** (Woodford (2003), App. A.3, pp. 632–633): if the
linearised system is not determinate, then a root on the unit circle (existence fails), more
than `n` roots inside (uniqueness fails), no root on the circle but fewer than `n` inside
(existence fails), or the count is right but genericity fails (uniqueness fails). -/
theorem failure_cases_general {f₁ f₂ f₃ : Matrix ι ι ℝ} (hfail : ¬ LinDeterminate f₁ f₂ f₃) :
    (∃ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ = 1) ∧
        ¬ Function.Surjective (sysOp f₁ f₂ f₃) ∨
      Fintype.card ι < Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) ∧ ¬ Function.Injective (sysOp f₁ f₂ f₃) ∨
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
        Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) < Fintype.card ι ∧ ¬ Function.Surjective (sysOp f₁ f₂ f₃) ∨
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
        Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ ¬ Function.Injective (sysOp f₁ f₂ f₃) := by
  by_cases hu : ∃ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ = 1
  · obtain ⟨μ, hμ, h1⟩ := hu
    exact Or.inl ⟨⟨μ, hμ, h1⟩, not_surjective_of_unit_root hμ h1⟩
  · have hnu : ∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1 :=
      fun μ hμ h1 => hu ⟨μ, hμ, h1⟩
    rcases lt_trichotomy (Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
      (fun μ => ‖μ‖ < 1))) (Fintype.card ι) with h | h | h
    · exact Or.inr (Or.inr (Or.inl ⟨hnu, h, not_surjective_of_count_lt hnu h⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨hnu, h, fun hinj => hfail ?_⟩))
      have hreg : quadPoly f₁ f₂ f₃ ≠ 0 := by
        intro h0
        rw [h0, Polynomial.map_zero, roots_zero, Multiset.filter_zero,
          Multiset.card_zero] at h
        have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.mp h.symm
        rw [quadPoly, Matrix.det_isEmpty] at h0
        exact one_ne_zero h0
      exact (linDeterminate_iff f₁ f₂ f₃).mpr ⟨hreg, hnu, h,
        (homInjective_iff_injective _ _ _).mpr hinj⟩
    · exact Or.inr (Or.inl ⟨h, not_injective_of_count_gt h⟩)

end Woodford.PriceLevelDetermination.LinearSystemsUnit
