/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasure
import OptimalPolicyRules.TidyR5bFOCNecessity
import OptimalPolicyRules.OptimalRulesMeasureStabilityModels

/-!
# Necessity of the first-order conditions on a probability space

Woodford (2003), *Interest and Prices*, Chapter 8, §1.1 (pp. 538–543): every plan that is optimal
subject to the initial constraint (1.6) satisfies the first-order conditions (1.9) for some
initial multipliers `M_{t₀−1}` (asserted on p. 541 without proof).

`TidyR5bFOCNecessity.foc_necessary` proves this for the exact expectation systems with
faithful expectations, and `TidyR5bFaithNeeded.foc_ae_of_version` gives an almost-sure form on
the conditional-expectation model under two extra hypotheses (the exact operators are versions
of `condExp`, and the squared residuals are integrable). Here the general LQ problem is treated
directly on the measure framework of `OptimalRulesMeasure` (Mathlib's `condExp`, essentially
bounded adapted plans, equations a.s.), with no such hypothesis: all integrability is derived
from essential boundedness, and the strict convexity step is a.s. faithfulness of `condExp`.

## The argument

* **Deterministic responses from means** (`exists_homResp_meas`): from the solutions with data
  `(0, 0, e_j)` and `(0, 0, 0)` (Assumption 8.1, existence half, in the corrected form
  `OptimalRulesMeasure.MFOCSolvableMB`) the unconditional mean path `t ↦ ∫ (y^j_t − y^0_t) dP` is a
  bounded deterministic solution of the homogeneous (1.1) + (1.9) with `M_{t₀−1} = e_j`
  (`∫ E_t x = ∫ x`, `mean_struct`, `mean_foc`).
* **The affine family** (`m_combo`): `y⁰ + H M`, `φ⁰ + Φ M` solves (1.1) + (1.9) a.s. for every
  bounded `M` known at `t₀`; `Ẽ z_{t₀} = e⁰ + L M` with the constant matrix `L = Ẽ (H_{t₀})_z`.
* **The Lagrangian identity with an initial term** (`m_lagrangian_gap_init`), the variational
  inequality on the countable set of rational scalings and a basis of `ker L'`
  (`ae_orth_kernel`), so that `ē − e⁰ ∈ range L` a.s.; `M₀ = R(ē − e⁰)`.
* Strict convexity (`m_targets_eq_init`) gives `T y = T y^{M₀}` a.s.; (1.9) involves the plan only
  through `T y`.

The initial multiplier `M₀` is known at `t₀` (it depends on the date-`t₀` constraint value);
(1.9) then holds with `M_t` known at `t` for every `t ≥ t₀` (`MFOCSystemI`). The project's
`OptimalRulesMeasure.MFOCSystem` asks in addition that `M_{t₀−1}` be known at `t₀ − 1`; this
holds exactly when `M₀` has such a version (`mFOCSystem_of_I`), in particular under `PredInfo`, or
under the book's literal Assumption 8.1, or at `t₀ = 0`, or for the `t₀`-optimal plan (`M₀ = 0`).

## Main results

* `m_foc_necessary`: every plan optimal subject to `Ẽ z_{t₀} = ē` satisfies (1.1) + (1.9) a.s.
  with bounded initial multipliers known at `t₀`.
* `m_optimalSubjectTo_iff`: **optimality subject to (1.6) ⟺ the first-order conditions**, a.s.
* `m_foc_necessary_pred`, `m_foc_necessary_book`, `m_foc_necessary_zero`: the full
  `OptimalRulesMeasure.MFOCSystem` (`M_{t₀−1}` known at `t₀ − 1`) under `PredInfo`, under the
  book's Assumption 8.1, and at `t₀ = 0`.
* `m_t0Optimal_foc_necessary`, `m_t0Optimal_iff`: the `t₀`-optimal plan satisfies (1.9) with
  `M_{t₀−1} = 0`, and conversely.
* `nk_m_optimalSubjectTo_iff`, `in_m_optimalSubjectTo_iff`: the equivalence with no hypothesis
  left, for the basic model of §3.1 and the inflation-inertia model of §3.2 (`0 < γ ≤ 1`), on
  every filtered probability space.
-/

namespace Woodford.OptimalPolicyRules.TidyR6bFOCMeasure

open MeasureTheory Filter Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure
open TidyR5bFOCNecessity (HomResp comboF comboF_of_le comboF_of_lt Lmat zrows eq110_combo
  mem_range_of_orth exists_rightInv)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Means of random vectors -/

/-- Woodford (2003), (1.10), p. 542 (tool): the unconditional mean `∫ x dP` of a random vector,
componentwise. -/
noncomputable def meanV (S : MeasExpectationSystem Ω) {ι : Type*} (x : Ω → ι → ℝ) : ι → ℝ :=
  fun i => ∫ ω, x ω i ∂S.μ

/-- Woodford (2003), (1.10) (tool): the mean of a sum. -/
theorem meanV_add (S : MeasExpectationSystem Ω) {ι : Type*} {x y : Ω → ι → ℝ}
    (hx : ∀ i, Integrable (fun ω => x ω i) S.μ) (hy : ∀ i, Integrable (fun ω => y ω i) S.μ) :
    meanV S (fun ω => x ω + y ω) = meanV S x + meanV S y := by
  funext i
  exact integral_add (hx i) (hy i)

/-- Woodford (2003), (1.10) (tool): the mean of a difference. -/
theorem meanV_sub (S : MeasExpectationSystem Ω) {ι : Type*} {x y : Ω → ι → ℝ}
    (hx : ∀ i, Integrable (fun ω => x ω i) S.μ) (hy : ∀ i, Integrable (fun ω => y ω i) S.μ) :
    meanV S (fun ω => x ω - y ω) = meanV S x - meanV S y := by
  funext i
  exact integral_sub (hx i) (hy i)

/-- Woodford (2003), (1.10) (tool): the mean commutes with a constant matrix. -/
theorem meanV_mulVec (S : MeasExpectationSystem Ω) {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℝ)
    {x : Ω → ι → ℝ} (hx : ∀ i, Integrable (fun ω => x ω i) S.μ) :
    meanV S (fun ω => A *ᵥ x ω) = A *ᵥ meanV S x := by
  funext k
  simp only [meanV, mulVec, dotProduct]
  rw [integral_finsetSum _ (fun i _ => (hx i).const_mul (A k i))]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- Woodford (2003), (1.10) (tool): the mean of a scalar random variable times a fixed vector. -/
theorem meanV_smul (S : MeasExpectationSystem Ω) {ι : Type*} (f : Ω → ℝ) (v : ι → ℝ) :
    meanV S (fun ω => f ω • v) = (∫ ω, f ω ∂S.μ) • v := by
  funext i
  simp only [meanV, Pi.smul_apply, smul_eq_mul]
  exact integral_mul_const _ _

/-- Woodford (2003), (1.10) (tool): a.s. equal random vectors have the same mean. -/
theorem meanV_congr (S : MeasExpectationSystem Ω) {ι : Type*} {x y : Ω → ι → ℝ}
    (h : ∀ᵐ ω ∂S.μ, x ω = y ω) : meanV S x = meanV S y := by
  funext i
  exact integral_congr_ae (h.mono fun ω e => congrFun e i)

/-- Woodford (2003), (1.10) (tool): the mean of a constant vector is the vector. -/
theorem meanV_const (S : MeasExpectationSystem Ω) {ι : Type*} (v : ι → ℝ) :
    meanV S (fun _ => v) = v := by
  funext i
  simp [meanV]

/-- Woodford (2003), (1.10) (law of iterated expectations): `∫ E_t x = ∫ x`. -/
theorem meanV_EVm (S : MeasExpectationSystem Ω) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) :
    meanV S (EVm S t x) = meanV S x := by
  funext i
  exact S.integral_E t _

/-- Woodford (2003), fn 6, p. 539 (tool): the components of an essentially bounded process with
a.e. strongly measurable components are integrable. -/
theorem intV {S : MeasExpectationSystem Ω} {ι : Type*} {x : ℕ → Ω → ι → ℝ} (hb : MBoundedV S x)
    (ha : MAEMeasV S x) (t : ℕ) (i : ι) : Integrable (fun ω => x t ω i) S.μ := by
  obtain ⟨K, hK⟩ := hb
  exact integrable_of_bound (ha t i) ((hK t).mono fun ω h => h i)

/-- Woodford (2003), p. 540 (tool): an adapted vector process has a.e. strongly measurable
components. -/
theorem aemeas_of_adapted {S : MeasExpectationSystem Ω} {ι : Type*} {x : ℕ → Ω → ι → ℝ}
    (ha : MAdaptedV S x) : MAEMeasV S x := fun t i =>
  ((ha t i).mono (S.𝓕.le t)).aestronglyMeasurable

/-- Woodford (2003), fn 6 (tool): the mean of an essentially bounded random vector is bounded by
the same bound. -/
theorem abs_meanV_le {S : MeasExpectationSystem Ω} {ι : Type*} {x : Ω → ι → ℝ} {K : ℝ}
    (h : ∀ᵐ ω ∂S.μ, ∀ i, |x ω i| ≤ K) (i : ι) : |meanV S x i| ≤ K := by
  have h2 := norm_integral_le_of_norm_le_const (μ := S.μ) (f := fun ω => x ω i) (C := K)
    (h.mono fun ω e => by rw [Real.norm_eq_abs]; exact e i)
  simpa [meanV] using h2

/-! ### The weak form of the first-order system -/

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), pp. 541–542: the system (1.1) + (1.9) a.s. from `t₀`, with initial
conditions `Z_{t₀} = Z₀`, `M_{t₀−1} = M₀` (a.s.), essentially bounded plan and multipliers, and
the multiplier `M_t` known at `t` for every `t ≥ t₀`. (`OptimalRulesMeasure.MFOCSystem` asks this
at every date, including `M_{t₀−1}` at `t₀ − 1`.) -/
def MFOCSystemI (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ)
    (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  MFeasible S P c t0 Z0 y ∧ MBoundedV S φ ∧ MAEMeasV S φ ∧
    (∀ t, t0 ≤ t → ∀ r, StronglyMeasurable[S.𝓕 t] (fun ω => φ (t + 1) ω (Sum.inr r))) ∧
    (∀ᵐ ω ∂S.μ, Mpart (φ t0 ω) = M0 ω) ∧ MFOC S P t0 y φ

/-- Woodford (2003), pp. 541–542: a solution of `OptimalRulesMeasure.MFOCSystem` solves the weak
form. -/
theorem mFOCSystemI_of {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 M0 y φ) : MFOCSystemI S P c t0 Z0 M0 y φ :=
  ⟨h.1, h.2.1, h.2.2.1, fun t _ r => h.2.2.2.1 t r, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ### Deterministic responses from unconditional means -/

/-- Woodford (2003), (1.10) (tool): a fixed matrix applied to a random vector with integrable
components has integrable components. -/
theorem intMulVec {S : MeasExpectationSystem Ω} {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℝ)
    {x : Ω → ι → ℝ} (hx : ∀ i, Integrable (fun ω => x ω i) S.μ) (k : κ) :
    Integrable (fun ω => (A *ᵥ x ω) k) S.μ := by
  simp only [mulVec, dotProduct]
  exact integrable_finsetSum _ (fun i _ => (hx i).const_mul (A k i))

omit [Fintype ιτ] in
/-- Woodford (2003), (1.1), p. 537 (unconditional means): the mean path of a feasible plan with no
disturbance satisfies (1.1) under perfect foresight, `Ĩ ŷ_{t+1} = Ã ŷ_t`. -/
theorem mean_struct {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (h : MFeasible S P (fun _ _ => 0) t0 Z0 y) {t : ℕ} (ht : t0 ≤ t) :
    P.sys.Itil *ᵥ meanV S (y (t + 1)) = P.sys.Atil *ᵥ meanV S (y t) := by
  have hI := intV h.2.2.1 (aemeas_of_adapted h.2.2.2)
  rw [P.sys.Itil_mulVec, P.sys.Atil_mulVec]
  obtain ⟨h1, h2⟩ := (h.1 t ht)
  have iZ : ∀ s j, Integrable (fun ω => Zpart (y s ω) j) S.μ := fun s j => hI s _
  have iz : ∀ s j, Integrable (fun ω => zpart (y s ω) j) S.μ := fun s j => hI s _
  have ii : ∀ s, Integrable (fun ω => ipart (y s ω)) S.μ := fun s => hI s _
  have m1 := meanV_congr S h1
  have m2 := meanV_congr S (h2.mono fun ω e => e.trans (add_zero _))
  rw [meanV_add S (x := fun ω => P.sys.A11 *ᵥ Zpart (y t ω))
    (y := fun ω => P.sys.A12 *ᵥ zpart (y t ω)) (intMulVec _ (iZ t)) (intMulVec _ (iz t)),
    meanV_mulVec S _ (iZ t), meanV_mulVec S _ (iz t)] at m1
  rw [meanV_mulVec S _ (x := EVm S t (fun ω' => zpart (y (t + 1) ω')))
    (fun j => S.integrable_E t _), meanV_EVm,
    meanV_add S (x := fun ω => P.sys.A21 *ᵥ Zpart (y t ω) + P.sys.A22 *ᵥ zpart (y t ω))
    (y := fun ω => ipart (y t ω) • P.sys.B2)
    (fun k => (intMulVec _ (iZ t) k).add (intMulVec _ (iz t) k))
    (fun k => (ii t).mul_const (P.sys.B2 k)),
    meanV_add S (x := fun ω => P.sys.A21 *ᵥ Zpart (y t ω))
    (y := fun ω => P.sys.A22 *ᵥ zpart (y t ω)) (intMulVec _ (iZ t)) (intMulVec _ (iz t)),
    meanV_mulVec S _ (iZ t), meanV_mulVec S _ (iz t), meanV_smul] at m2
  congr 1

/-- Woodford (2003), (1.9) (tool): the left side of (1.9) as an affine function,
`Ã'a + T'W(Tv − τ*) − β⁻¹Ĩ'f = Ã'a + (T'WT)v − (β⁻¹Ĩ')f − T'Wτ*`. -/
theorem foc_expr_eq (P : LQProblem ιZ ιz ιτ) (a f : ιZ ⊕ ιz → ℝ) (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    P.sys.Atilᵀ *ᵥ a + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ f) =
      P.sys.Atilᵀ *ᵥ a + (P.Tᵀ * (P.W * P.T)) *ᵥ v - (P.β⁻¹ • P.sys.Itilᵀ) *ᵥ f +
        -(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) := by
  rw [mulVec_sub, mulVec_sub, ← mulVec_mulVec, ← mulVec_mulVec, Matrix.smul_mulVec]
  abel

/-- Woodford (2003), (1.9) (tool): the mean of an affine function of three random vectors. -/
theorem meanV_lin3 (S : MeasExpectationSystem Ω) {ι κ1 κ2 κ3 : Type*} [Fintype κ1] [Fintype κ2]
    [Fintype κ3] (A : Matrix ι κ1 ℝ) (B : Matrix ι κ2 ℝ) (C : Matrix ι κ3 ℝ) (k : ι → ℝ)
    {a : Ω → κ1 → ℝ} {b : Ω → κ2 → ℝ} {d : Ω → κ3 → ℝ}
    (ha : ∀ i, Integrable (fun ω => a ω i) S.μ) (hb : ∀ i, Integrable (fun ω => b ω i) S.μ)
    (hd : ∀ i, Integrable (fun ω => d ω i) S.μ) :
    meanV S (fun ω => A *ᵥ a ω + B *ᵥ b ω - C *ᵥ d ω + k) =
      A *ᵥ meanV S a + B *ᵥ meanV S b - C *ᵥ meanV S d + k := by
  rw [meanV_add S (x := fun ω => A *ᵥ a ω + B *ᵥ b ω - C *ᵥ d ω) (y := fun _ => k)
    (fun i => ((intMulVec A ha i).add (intMulVec B hb i)).sub (intMulVec C hd i))
    (fun i => integrable_const _), meanV_const,
    meanV_sub S (x := fun ω => A *ᵥ a ω + B *ᵥ b ω) (y := fun ω => C *ᵥ d ω)
    (fun i => (intMulVec A ha i).add (intMulVec B hb i)) (intMulVec C hd),
    meanV_add S (x := fun ω => A *ᵥ a ω) (y := fun ω => B *ᵥ b ω) (intMulVec A ha)
    (intMulVec B hb), meanV_mulVec S A ha, meanV_mulVec S B hb, meanV_mulVec S C hd]

/-- Woodford (2003), (1.9), p. 541 (unconditional means): the mean paths of a solution of the
weak system satisfy (1.9) under perfect foresight,
`Ã'φ̂_{t+1} + T'W(Tŷ_t − τ*) − β⁻¹Ĩ'φ̂_t = 0` for `t ≥ t₀`. -/
theorem mean_foc {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {c : ℕ → Ω → ιz → ℝ}
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystemI S P c t0 Z0 M0 y φ) {t : ℕ} (ht : t0 ≤ t) :
    P.sys.Atilᵀ *ᵥ meanV S (φ (t + 1)) + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ meanV S (y t) - P.τstar)) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ meanV S (φ t)) = 0 := by
  have hy := intV h.1.2.2.1 (aemeas_of_adapted h.1.2.2.2)
  have hφ := intV h.2.1 h.2.2.1
  have m := meanV_congr S (h.2.2.2.2.2 t ht)
  rw [meanV_const] at m
  simp only [foc_expr_eq] at m
  rw [meanV_lin3 S _ _ _ _ (a := EVm S t (φ (t + 1))) (fun i => S.integrable_E t _) (hy t)
    (hφ t), meanV_EVm] at m
  rw [foc_expr_eq]
  exact m

/-- Woodford (2003), (1.10), p. 542 (tool): the columns of a product with a column-built matrix. -/
theorem mul_of_cols' {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (h : c → b → ℝ) :
    A * Matrix.of (fun v j => h j v) = Matrix.of fun i j => (A *ᵥ h j) i :=
  TidyR5bFOCNecessity.mul_of_cols A h

/-- Woodford (2003), (1.10), p. 542: **deterministic responses to the initial multipliers exist on
every filtered probability space** under Assumption 8.1 (existence half, corrected form
`OptimalRulesMeasure.MFOCSolvableMB`): the unconditional mean paths of the differences of the
solutions with data `(0, 0, e_j)` and `(0, 0, 0)` form a bounded deterministic solution of the
homogeneous (1.1) + (1.9) with `Z_{t₀} = 0` and `M_{t₀−1} = e_j` (`∫ E_t x = ∫ x`). -/
theorem exists_homResp_meas {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (hsolv : MFOCSolvableMB S P t0) :
    ∃ (H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ) (Φ : ℕ → Matrix (ιZ ⊕ ιz) ιz ℝ),
      HomResp P t0 H Φ := by
  have hc := zero_dist (S := S) (ιz := ιz)
  have hZk : MKnownV S t0 (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) := fun _ => stronglyMeasurable_const
  have hZb : MBoundedRV S (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) :=
    ⟨0, Eventually.of_forall fun _ _ => by simp⟩
  have hsol : ∀ v : ιz → ℝ, ∃ y φ, MFOCSystem S P (fun _ _ => 0) t0 (fun _ _ => 0)
      (fun _ => v) y φ := fun v =>
    hsolv _ _ _ hc.1 hc.2 hZk hZb ⟨∑ r, |v r|, Eventually.of_forall fun _ r =>
      Finset.single_le_sum (f := fun r => |v r|) (fun _ _ => abs_nonneg _) (Finset.mem_univ r)⟩
      (fun _ => stronglyMeasurable_const)
  choose Y Ph hY using hsol
  set e : ιz → ιz → ℝ := fun j r => (1 : Matrix ιz ιz ℝ) r j with he
  set hcol : ιz → ℕ → (ιZ ⊕ ιz) ⊕ Unit → ℝ := fun j t => meanV S (Y (e j) t) - meanV S (Y 0 t)
    with hhcol
  set gcol : ιz → ℕ → ιZ ⊕ ιz → ℝ := fun j t => meanV S (Ph (e j) t) - meanV S (Ph 0 t)
    with hgcol
  have key1 : ∀ j t, t0 ≤ t → P.sys.Itil *ᵥ hcol j (t + 1) = P.sys.Atil *ᵥ hcol j t := by
    intro j t ht
    simp only [hhcol, mulVec_sub]
    rw [mean_struct (hY (e j)).1 ht, mean_struct (hY 0).1 ht]
  have key2 : ∀ j t, t0 ≤ t → P.sys.Atilᵀ *ᵥ gcol j (t + 1) +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ hcol j t)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ gcol j t) = 0 := by
    intro j t ht
    have e1 := mean_foc (mFOCSystemI_of (hY (e j))) ht
    have e0 := mean_foc (mFOCSystemI_of (hY 0)) ht
    simp only [hhcol, hgcol, mulVec_sub, smul_sub] at e1 e0 ⊢
    linear_combination (norm := module) e1 - e0
  have hZ0 : ∀ v, Zpart (meanV S (Y v t0)) = 0 := by
    intro v
    have := meanV_congr S (hY v).1.2.1
    rw [meanV_const] at this
    exact this
  have hM0 : ∀ v, Mpart (meanV S (Ph v t0)) = v := by
    intro v
    have := meanV_congr S (hY v).2.2.2.2.1
    rw [meanV_const] at this
    exact this
  choose KY hKY using fun v => (hY v).1.2.2.1
  choose KP hKP using fun v => (hY v).2.1
  refine ⟨fun t => Matrix.of fun v j => hcol j t v, fun t => Matrix.of fun r j => gcol j t r,
    fun t ht => ?_, fun t ht => ?_, fun r j => ?_, fun r j => ?_, ?_, ?_⟩
  · rw [mul_of_cols', mul_of_cols']
    ext i j
    simp only [Matrix.of_apply, key1 j t ht]
  · rw [mul_of_cols', mul_of_cols', mul_of_cols', mul_of_cols', mul_of_cols']
    ext i j
    have := congrFun (key2 j t ht) i
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.zero_apply, smul_eq_mul] at this ⊢
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using this
  · have h1 := congrFun (hZ0 (e j)) r
    have h2 := congrFun (hZ0 0) r
    simp only [Matrix.of_apply, hhcol, Pi.sub_apply]
    change Zpart (meanV S (Y (e j) t0)) r - Zpart (meanV S (Y 0 t0)) r = 0
    rw [h1, h2, Pi.zero_apply, sub_zero]
  · have h1 := congrFun (hM0 (e j)) r
    have h2 := congrFun (hM0 0) r
    simp only [Matrix.of_apply, hgcol, Pi.sub_apply]
    change Mpart (meanV S (Ph (e j) t0)) r - Mpart (meanV S (Ph 0 t0)) r = _
    rw [h1, h2, Pi.zero_apply, sub_zero]
  · refine ⟨(∑ j, |KY (e j)|) + |KY 0|, fun t v j => ?_⟩
    simp only [Matrix.of_apply, hhcol, Pi.sub_apply]
    have a1 := abs_meanV_le (hKY (e j) t) v
    have a2 := abs_meanV_le (hKY 0 t) v
    have a3 : |KY (e j)| ≤ ∑ j, |KY (e j)| :=
      Finset.single_le_sum (f := fun j => |KY (e j)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    calc _ ≤ |meanV S (Y (e j) t) v| + |meanV S (Y 0 t) v| := abs_sub _ _
      _ ≤ |KY (e j)| + |KY 0| := add_le_add (a1.trans (le_abs_self _)) (a2.trans (le_abs_self _))
      _ ≤ _ := by linarith
  · refine ⟨(∑ j, |KP (e j)|) + |KP 0|, fun t v j => ?_⟩
    simp only [Matrix.of_apply, hgcol, Pi.sub_apply]
    have a1 := abs_meanV_le (hKP (e j) t) v
    have a2 := abs_meanV_le (hKP 0 t) v
    have a3 : |KP (e j)| ≤ ∑ j, |KP (e j)| :=
      Finset.single_le_sum (f := fun j => |KP (e j)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    calc _ ≤ |meanV S (Ph (e j) t) v| + |meanV S (Ph 0 t) v| := abs_sub _ _
      _ ≤ |KP (e j)| + |KP 0| := add_le_add (a1.trans (le_abs_self _)) (a2.trans (le_abs_self _))
      _ ≤ _ := by linarith

/-! ### The affine family with conditional expectations -/

/-- Woodford (2003), p. 540 (tool): `E_t(a + b) = E_t a + b` a.s. for `b` known at `t`. -/
theorem EVm_add_known {S : MeasExpectationSystem Ω} {ι : Type*} [Finite ι] {t : ℕ}
    {a b : Ω → ι → ℝ} (ha : ∀ i, Integrable (fun ω => a ω i) S.μ) (hbk : MKnownV S t b)
    (hbi : ∀ i, Integrable (fun ω => b ω i) S.μ) :
    ∀ᵐ ω ∂S.μ, EVm S t (fun ω => a ω + b ω) ω = EVm S t a ω + b ω := by
  have h : ∀ i, ∀ᵐ ω ∂S.μ, EVm S t (fun ω => a ω + b ω) ω i = EVm S t a ω i + b ω i := by
    intro i
    have e2 := S.E_of_stronglyMeasurable (hbk i) (hbi i)
    filter_upwards [S.E_add (ha i) (hbi i) t] with ω e
    change S.E t ((fun ω => a ω i) + fun ω => b ω i) ω = _
    rw [e, Pi.add_apply, e2]
    rfl
  filter_upwards [ae_all_iff.2 h] with ω h
  funext i
  exact h i

/-- Woodford (2003), (1.10), p. 542: **the affine family with conditional expectations.** If
`(y⁰, φ⁰)` solves (1.1) + (1.9) a.s. with `M_{t₀−1} = 0` and `(H, Φ)` are deterministic responses,
then for every essentially bounded `M` known at `t₀`, the plan `y⁰ + H M` with multipliers
`φ⁰ + Φ M` solves the weak system (1.1) + (1.9) a.s. with `M_{t₀−1} = M`. -/
theorem m_combo {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {c : ℕ → Ω → ιz → ℝ}
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h0 : MFOCSystem S P c t0 Z0 0 y0 φ0)
    {H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ} {Φ : ℕ → Matrix (ιZ ⊕ ιz) ιz ℝ}
    (hH : HomResp P t0 H Φ) {M : Ω → ιz → ℝ} (hMk : MKnownV S t0 M) (hMb : MBoundedRV S M) :
    MFOCSystemI S P c t0 Z0 M (comboF t0 y0 H M) (comboF t0 φ0 Φ M) := by
  obtain ⟨⟨hs0, hZ0, hb0, ha0⟩, hbφ0, hm0, hM0, hM0e, hf0⟩ := h0
  obtain ⟨hHc, hHf, hHZ, hHM, ⟨KH, hKH⟩, ⟨KΦ, hKΦ⟩⟩ := hH
  obtain ⟨KM, hKM⟩ := hMb
  have hMt : ∀ t, t0 ≤ t → MKnownV S t M := fun t ht i => (hMk i).mono (S.𝓕.mono ht)
  have hMi : ∀ i, Integrable (fun ω => M ω i) S.μ := fun i =>
    integrable_of_bound ((hMk i).mono (S.𝓕.le t0)).aestronglyMeasurable
      (hKM.mono fun ω h => h i)
  have hkn : ∀ {κ : Type _} (G : Matrix κ ιz ℝ) (t : ℕ), t0 ≤ t →
      MKnownV S t (fun ω => G *ᵥ M ω) := fun G t ht k =>
    sm_comp (hMt t ht) (g := fun v => (G *ᵥ v) k) (by fun_prop)
  have hy0i := intV hb0 (aemeas_of_adapted ha0)
  have hφ0i := intV hbφ0 hm0
  have hItH : ∀ t, t0 ≤ t → ∀ v : ιz → ℝ,
      P.sys.Itil *ᵥ (H (t + 1) *ᵥ v) = P.sys.Atil *ᵥ (H t *ᵥ v) := fun t ht v => by
    rw [mulVec_mulVec, mulVec_mulVec, hHc t ht]
  have hZH : ∀ t, t0 ≤ t → ∀ v : ιz → ℝ, Zpart (H (t + 1) *ᵥ v) =
      P.sys.A11 *ᵥ Zpart (H t *ᵥ v) + P.sys.A12 *ᵥ zpart (H t *ᵥ v) := fun t ht v =>
    funext fun r => by
      have := congrFun (hItH t ht v) (Sum.inl r)
      rw [P.sys.Itil_mulVec, P.sys.Atil_mulVec] at this
      exact this
  have hzH : ∀ t, t0 ≤ t → ∀ v : ιz → ℝ, P.sys.Et *ᵥ zpart (H (t + 1) *ᵥ v) =
      P.sys.A21 *ᵥ Zpart (H t *ᵥ v) + P.sys.A22 *ᵥ zpart (H t *ᵥ v) +
        ipart (H t *ᵥ v) • P.sys.B2 := fun t ht v =>
    funext fun r => by
      have := congrFun (hItH t ht v) (Sum.inr r)
      rw [P.sys.Itil_mulVec, P.sys.Atil_mulVec] at this
      exact this
  have hbnd : ∀ {κ : Type _} {G : ℕ → Matrix κ ιz ℝ} {KG : ℝ}, (∀ t k j, |G t k j| ≤ KG) →
      ∀ t, ∀ᵐ ω ∂S.μ, ∀ k, |(G t *ᵥ M ω) k| ≤ Fintype.card ιz * (|KG| * |KM|) :=
    fun {κ G KG} hG t => hKM.mono fun ω h k =>
      TidyR5bFOCNecessity.abs_mulVec_le (A := G t) (v := M ω)
        (fun k' i' => (hG t k' i').trans (le_abs_self KG))
        (fun i' => (h i').trans (le_abs_self KM)) k
  have hc0 : ∀ KG : ℝ, 0 ≤ (Fintype.card ιz : ℝ) * (|KG| * |KM|) := fun KG => by positivity
  refine ⟨⟨fun t ht => ⟨?_, ?_⟩, ?_, ?_, fun t i => ?_⟩, ?_, fun t i => ?_, fun t ht r => ?_, ?_,
    fun t ht => ?_⟩
  · -- predetermined rows
    filter_upwards [(hs0 t ht).1] with ω e
    rw [comboF_of_le (by omega), comboF_of_le ht]
    change Zpart (y0 (t + 1) ω) + Zpart (H (t + 1) *ᵥ M ω) =
      P.sys.A11 *ᵥ (Zpart (y0 t ω) + Zpart (H t *ᵥ M ω)) +
        P.sys.A12 *ᵥ (zpart (y0 t ω) + zpart (H t *ᵥ M ω))
    rw [e, hZH t ht, mulVec_add, mulVec_add]
    abel
  · -- expectational rows
    have hfun : (fun ω' => zpart (comboF t0 y0 H M (t + 1) ω')) =
        fun ω' => zpart (y0 (t + 1) ω') + zpart (H (t + 1) *ᵥ M ω') := by
      funext ω'
      rw [comboF_of_le (by omega)]
      rfl
    filter_upwards [(hs0 t ht).2, EVm_add_known (S := S) (t := t)
      (a := fun ω' => zpart (y0 (t + 1) ω')) (b := fun ω' => zpart (H (t + 1) *ᵥ M ω'))
      (fun j => hy0i (t + 1) _) (fun j => hkn (H (t + 1)) t ht _)
      (fun j => intMulVec (H (t + 1)) hMi _)] with ω e ek
    rw [hfun, ek, mulVec_add, e, hzH t ht, comboF_of_le ht]
    change _ = P.sys.A21 *ᵥ (Zpart (y0 t ω) + Zpart (H t *ᵥ M ω)) +
      P.sys.A22 *ᵥ (zpart (y0 t ω) + zpart (H t *ᵥ M ω)) +
      (ipart (y0 t ω) + ipart (H t *ᵥ M ω)) • P.sys.B2 + c t ω
    rw [mulVec_add, mulVec_add, add_smul]
    abel
  · -- the initial predetermined variables
    filter_upwards [hZ0] with ω e
    rw [comboF_of_le le_rfl]
    have hz : Zpart (H t0 *ᵥ M ω) = 0 := funext fun r => by
      simp [Zpart, mulVec, dotProduct, hHZ]
    change Zpart (y0 t0 ω) + Zpart (H t0 *ᵥ M ω) = Z0 ω
    rw [e, hz, add_zero]
  · -- boundedness of the plan
    obtain ⟨K0, hK0⟩ := hb0
    refine ⟨K0 + Fintype.card ιz * (|KH| * |KM|), fun t => ?_⟩
    filter_upwards [hK0 t, hbnd hKH t] with ω h1 h2 i
    by_cases ht : t0 ≤ t
    · rw [comboF_of_le ht, Pi.add_apply]
      exact (abs_add_le _ _).trans (add_le_add (h1 i) (h2 i))
    · rw [comboF_of_lt (by omega)]
      linarith [h1 i, hc0 KH]
  · -- adaptedness of the plan
    by_cases ht : t0 ≤ t
    · have e : (fun ω => comboF t0 y0 H M t ω i) = fun ω => y0 t ω i + (H t *ᵥ M ω) i := by
        funext ω
        rw [comboF_of_le ht]
        rfl
      rw [e]
      exact (ha0 t i).add (hkn (H t) t ht i)
    · have e : (fun ω => comboF t0 y0 H M t ω i) = fun ω => y0 t ω i := by
        funext ω
        rw [comboF_of_lt (by omega)]
      rw [e]
      exact ha0 t i
  · -- boundedness of the multipliers
    obtain ⟨K0, hK0⟩ := hbφ0
    refine ⟨K0 + Fintype.card ιz * (|KΦ| * |KM|), fun t => ?_⟩
    filter_upwards [hK0 t, hbnd hKΦ t] with ω h1 h2 i
    by_cases ht : t0 ≤ t
    · rw [comboF_of_le ht, Pi.add_apply]
      exact (abs_add_le _ _).trans (add_le_add (h1 i) (h2 i))
    · rw [comboF_of_lt (by omega)]
      linarith [h1 i, hc0 KΦ]
  · -- measurability of the multipliers
    by_cases ht : t0 ≤ t
    · have e : (fun ω => comboF t0 φ0 Φ M t ω i) = fun ω => φ0 t ω i + (Φ t *ᵥ M ω) i := by
        funext ω
        rw [comboF_of_le ht]
        rfl
      rw [e]
      exact (hm0 t i).add (((hkn (Φ t) t ht i).mono (S.𝓕.le t)).aestronglyMeasurable)
    · have e : (fun ω => comboF t0 φ0 Φ M t ω i) = fun ω => φ0 t ω i := by
        funext ω
        rw [comboF_of_lt (by omega)]
      rw [e]
      exact hm0 t i
  · -- `M_t` known at `t` for `t ≥ t₀`
    have e : (fun ω => comboF t0 φ0 Φ M (t + 1) ω (Sum.inr r)) =
        fun ω => φ0 (t + 1) ω (Sum.inr r) + (Φ (t + 1) *ᵥ M ω) (Sum.inr r) := by
      funext ω
      rw [comboF_of_le (by omega)]
      rfl
    rw [e]
    exact (hM0 t r).add (hkn (Φ (t + 1)) t ht (Sum.inr r))
  · -- the initial multipliers
    filter_upwards [hM0e] with ω e
    rw [comboF_of_le le_rfl]
    funext r
    have h1 := congrFun e r
    simp only [Mpart, Pi.add_apply] at h1 ⊢
    rw [h1]
    simp only [Pi.zero_apply, zero_add]
    simp only [mulVec, dotProduct, hHM]
    simp [Matrix.one_apply]
  · -- the first-order conditions
    have e : comboF t0 φ0 Φ M (t + 1) = fun ω' => φ0 (t + 1) ω' + Φ (t + 1) *ᵥ M ω' :=
      funext fun ω' => comboF_of_le (by omega) _ _ _ _
    filter_upwards [hf0 t ht, EVm_add_known (S := S) (t := t) (a := φ0 (t + 1))
      (b := fun ω' => Φ (t + 1) *ᵥ M ω') (hφ0i (t + 1)) (hkn (Φ (t + 1)) t ht)
      (intMulVec (Φ (t + 1)) hMi)] with ω hf ek
    have hhom := congrArg (· *ᵥ M ω) (hHf t ht)
    simp only [add_mulVec, sub_mulVec, smul_mulVec, zero_mulVec, ← mulVec_mulVec] at hhom
    rw [e, ek, comboF_of_le ht, comboF_of_le ht]
    simp only [mulVec_add, mulVec_sub, smul_add] at hf hhom ⊢
    linear_combination (norm := module) hf + hhom

/-! ### The Lagrangian identity with an initial multiplier term -/

/-- Woodford (2003), p. 541 and survey §4.4: **the Lagrangian identity with a nonzero initial
term, with genuine conditional expectations.** If `y*` with multipliers `φ` solves the weak system
(1.1) + (1.9) (`M_t` known at `t` only for `t ≥ t₀`) and `y` is any bounded feasible plan, then a.s.
`J(y) − J(y*) − β⁻¹ E_{t₀}[φ_{t₀}'Ĩ(y_{t₀} − y*_{t₀})] = ∑_k β^k E_{t₀} ½ (T d)'W(T d)`,
`d = y − y*`. -/
theorem m_lagrangian_gap_init {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystemI S P c t0 Z0 M0 ys φ) (hy : MFeasible S P c t0 Z0' y) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => P.β ^ k *
        S.E t0 (fun ω' => quad P.W (P.T *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω)
      (MJ S P t0 y ω - MJ S P t0 ys ω -
        P.β⁻¹ * S.E t0 (fun ω' => φ t0 ω' ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω' - ys t0 ω'))) ω) := by
  obtain ⟨hys, hbφ, hmφ, hMφ, -, hfoc⟩ := hs
  have hβ0 := P.β_pos
  have hβ1 := P.β_lt_one
  have hWt : P.Wᵀ = P.W := by
    have := P.W_posDef.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  -- the multipliers truncated before `t₀ + 1` (for the conditional-expectation step)
  set φt : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun s => if s ≤ t0 then 0 else φ s with hφt
  have hφt_eq : ∀ s, t0 < s → φt s = φ s := fun s hs => by
    simp only [hφt, show ¬ s ≤ t0 by omega, ↓reduceIte]
  obtain ⟨Kφ, hKφ⟩ := hbφ
  have hbφt : MBoundedV S φt := ⟨max Kφ 0, fun s => by
    by_cases h : s ≤ t0
    · exact Eventually.of_forall fun ω i => by simp [hφt, h]
    · filter_upwards [hKφ s] with ω e i
      simp only [hφt, h, ↓reduceIte]
      exact (e i).trans (le_max_left _ _)⟩
  have hmφt : MAEMeasV S φt := fun s i => by
    by_cases h : s ≤ t0
    · simp only [hφt, h, ↓reduceIte, Pi.zero_apply]
      exact aestronglyMeasurable_const
    · simp only [hφt, h, ↓reduceIte]
      exact hmφ s i
  have hMφt : MMultMeas S φt := fun s r => by
    by_cases h : s + 1 ≤ t0
    · simp only [hφt, h, ↓reduceIte, Pi.zero_apply]
      exact stronglyMeasurable_const
    · simp only [hφt, h, ↓reduceIte]
      exact hMφ s (by omega) r
  have hJy := hasSum_MJ S P t0 hy.2.2.1 hy.2.2.2
  have hJys := hasSum_MJ S P t0 hys.2.2.1 hys.2.2.2
  obtain ⟨Ky, hKy⟩ := hy.2.2.1
  obtain ⟨Kys, hKys⟩ := hys.2.2.1
  have hyA : ∀ s i, AEStronglyMeasurable (fun ω => y s ω i) S.μ := fun s i =>
    ((hy.2.2.2 s i).mono (S.𝓕.le s)).aestronglyMeasurable
  have hysA : ∀ s i, AEStronglyMeasurable (fun ω => ys s ω i) S.μ := fun s i =>
    ((hys.2.2.2 s i).mono (S.𝓕.le s)).aestronglyMeasurable
  have hdA : ∀ s i, AEStronglyMeasurable (fun ω => (y s ω - ys s ω) i) S.μ := fun s i =>
    (hyA s i).sub (hysA s i)
  have hdb : ∀ s, ∀ᵐ ω ∂S.μ, ∀ i, |(y s ω - ys s ω) i| ≤ Ky + Kys := fun s => by
    filter_upwards [hKy s, hKys s] with ω h1 h2 i
    exact (abs_sub _ _).trans (add_le_add (h1 i) (h2 i))
  set a : ℕ → Ω → ℝ := fun s ω => φ s ω ⬝ᵥ (P.sys.Itil *ᵥ (y s ω - ys s ω)) with ha
  set b : ℕ → Ω → ℝ := fun s ω => EVm S s (φ (s + 1)) ω ⬝ᵥ (P.sys.Atil *ᵥ (y s ω - ys s ω))
    with hb
  set Q : ℕ → Ω → ℝ := fun s ω => quad P.W (P.T *ᵥ (y s ω - ys s ω)) with hQ
  obtain ⟨KI, hKI⟩ := exists_bound_mulVec P.sys.Itil (Ky + Kys)
  obtain ⟨KA, hKA⟩ := exists_bound_mulVec P.sys.Atil (Ky + Kys)
  obtain ⟨KL, hKL⟩ := exists_bound_lossFn P.T P.W P.τstar Ky
  obtain ⟨KLs, hKLs⟩ := exists_bound_lossFn P.T P.W P.τstar Kys
  obtain ⟨KQ, hKQ⟩ := exists_bound_lossFn P.T P.W 0 (Ky + Kys)
  set Ka : ℝ := Fintype.card (ιZ ⊕ ιz) * (Kφ * KI) with hKa
  have hab : ∀ s, ∀ᵐ ω ∂S.μ, |a s ω| ≤ Ka := fun s => by
    filter_upwards [hKφ s, hdb s] with ω h1 h2
    exact abs_dotProduct_le h1 (hKI _ h2)
  have hai : ∀ s, Integrable (a s) S.μ := fun s =>
    integrable_of_bound (aesm_comp₂ (v := φ s) (w := fun ω => y s ω - ys s ω)
      (g := fun p => p.1 ⬝ᵥ (P.sys.Itil *ᵥ p.2)) (hmφ s) (hdA s) (by fun_prop)) (hab s)
  have hbi : ∀ s, Integrable (b s) S.μ := fun s => by
    have hEm : ∀ i, AEStronglyMeasurable (fun ω => EVm S s (φ (s + 1)) ω i) S.μ := fun i =>
      (S.integrable_E s _).aestronglyMeasurable
    have hEb : ∀ᵐ ω ∂S.μ, ∀ i, |EVm S s (φ (s + 1)) ω i| ≤ Kφ :=
      ae_all_iff.2 fun i => S.abs_E_le ((hKφ (s + 1)).mono fun ω h => h i) s
    refine integrable_of_bound (aesm_comp₂ (v := EVm S s (φ (s + 1)))
      (w := fun ω => y s ω - ys s ω) (g := fun p => p.1 ⬝ᵥ (P.sys.Atil *ᵥ p.2)) hEm (hdA s)
      (by fun_prop)) (K := Fintype.card (ιZ ⊕ ιz) * (Kφ * KA)) ?_
    filter_upwards [hEb, hdb s] with ω h1 h2
    exact abs_dotProduct_le h1 (hKA _ h2)
  have hLyi : ∀ s, Integrable (fun ω => P.loss (y s ω)) S.μ := fun s =>
    integrable_of_bound (aesm_comp (hyA s) (continuous_loss P)) (K := KL)
      ((hKy s).mono fun ω h => hKL _ h)
  have hLysi : ∀ s, Integrable (fun ω => P.loss (ys s ω)) S.μ := fun s =>
    integrable_of_bound (aesm_comp (hysA s) (continuous_loss P)) (K := KLs)
      ((hKys s).mono fun ω h => hKLs _ h)
  have hQi : ∀ s, Integrable (Q s) S.μ := fun s =>
    integrable_of_bound (aesm_comp (hdA s) (g := fun v => quad P.W (P.T *ᵥ v))
      (by unfold quad; fun_prop)) (K := KQ) ((hdb s).mono fun ω h => by
        have := hKQ _ h
        simpa [lossFn] using this)
  -- the pointwise identity from (1.9)
  have hpt : ∀ k, (fun ω => P.loss (y (t0 + k) ω)) =ᵐ[S.μ]
      (fun ω => P.loss (ys (t0 + k) ω)) + Q (t0 + k) + P.β⁻¹ • a (t0 + k) - b (t0 + k) := by
    intro k
    filter_upwards [hfoc (t0 + k) (Nat.le_add_right _ _)] with ω hf
    have := lossFn_sub_of_foc hWt hf (y (t0 + k) ω)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hb, hQ]
    change lossFn P.T P.W P.τstar (y (t0 + k) ω) =
      lossFn P.T P.W P.τstar (ys (t0 + k) ω) + _ + _ - _
    linarith
  -- conditional expectations
  have hEb : ∀ k, S.E t0 (b (t0 + k)) =ᵐ[S.μ] S.E t0 (a (t0 + k + 1)) := by
    intro k
    have hn := m_E_next (P := P) hy hys hbφt hmφt hMφt (t := t0 + k) (Nat.le_add_right _ _)
    rw [hφt_eq (t0 + k + 1) (by omega)] at hn
    exact (S.E_congr hn.symm t0).trans (S.E_tower (Nat.le_add_right _ _) _)
  have hkey : ∀ k, ∀ᵐ ω ∂S.μ, S.E t0 (fun ω => P.loss (y (t0 + k) ω)) ω =
      S.E t0 (fun ω => P.loss (ys (t0 + k) ω)) ω + S.E t0 (Q (t0 + k)) ω +
        P.β⁻¹ * S.E t0 (a (t0 + k)) ω - S.E t0 (a (t0 + k + 1)) ω := by
    intro k
    have i1 := (hLysi (t0 + k)).add (hQi (t0 + k))
    have i2 := i1.add ((hai (t0 + k)).smul P.β⁻¹)
    filter_upwards [S.E_congr (hpt k) t0, S.E_sub i2 (hbi (t0 + k)) t0,
      S.E_add i1 ((hai (t0 + k)).smul P.β⁻¹) t0, S.E_add (hLysi (t0 + k)) (hQi (t0 + k)) t0,
      S.E_smul P.β⁻¹ (a (t0 + k)) t0, hEb k] with ω e1 e2 e3 e4 e5 e6
    rw [e1, e2, Pi.sub_apply, e3, Pi.add_apply, e4, Pi.add_apply, e5, e6, Pi.smul_apply,
      smul_eq_mul]
  have heb : ∀ k, ∀ᵐ ω ∂S.μ, |S.E t0 (a (t0 + k)) ω| ≤ Ka := fun k =>
    S.abs_E_le (hab (t0 + k)) t0
  filter_upwards [hJy, hJys, ae_all_iff.2 hkey, ae_all_iff.2 heb] with ω h1 h2 h3 h5
  have htel := hasSum_telescope hβ0 hβ1 (e := fun k => S.E t0 (a (t0 + k)) ω) h5
  simp only [Nat.add_zero] at htel
  have hfin := (h1.sub h2).sub htel
  refine hfin.congr_fun fun k => ?_
  rw [h3 k]
  simp only [hQ]
  ring_nf

/-- Woodford (2003), p. 541 and survey §4.4: **Lagrangian sufficiency for the weak system**: if
`y*` solves (1.1) + (1.9) a.s. and the initial multiplier term vanishes a.s.,
`φ_{t₀}'Ĩ(y_{t₀} − y*_{t₀}) = 0`, then `J(y*) ≤ J(y)` a.s. -/
theorem m_J_le_init {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystemI S P c t0 Z0 M0 ys φ) (hy : MFeasible S P c t0 Z0' y)
    (hinit : ∀ᵐ ω ∂S.μ, φ t0 ω ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω - ys t0 ω)) = 0) :
    MJ S P t0 ys ≤ᵐ[S.μ] MJ S P t0 y := by
  have hnn : ∀ k, ∀ᵐ ω ∂S.μ, 0 ≤ S.E t0
      (fun ω' => quad P.W (P.T *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω := fun k =>
    condExp_nonneg (Eventually.of_forall fun ω' => quad_nonneg P.W_posDef.posSemidef _)
  have h0 : S.E t0 (fun ω' => φ t0 ω' ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω' - ys t0 ω'))) =ᵐ[S.μ] 0 :=
    (S.E_congr hinit t0).trans (by rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, S.E_zero])
  filter_upwards [m_lagrangian_gap_init hs hy, ae_all_iff.2 hnn, h0] with ω h1 h2 h3
  have := h1.nonneg fun k => mul_nonneg (pow_pos P.β_pos k).le (h2 k)
  rw [h3, Pi.zero_apply, mul_zero, sub_zero] at this
  linarith

/-- Woodford (2003), p. 541 and fn 8 (uniqueness of the optimum), for the weak system: a bounded
feasible plan with the same discounted loss as a solution of (1.1) + (1.9), with vanishing
initial multiplier term, has the same target path a.s. for all `t ≥ t₀` (`W ≻ 0`). -/
theorem m_targets_eq_init {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystemI S P c t0 Z0 M0 ys φ) (hy : MFeasible S P c t0 Z0' y)
    (hinit : ∀ᵐ ω ∂S.μ, φ t0 ω ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω - ys t0 ω)) = 0)
    (hJ : MJ S P t0 y =ᵐ[S.μ] MJ S P t0 ys) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, P.T *ᵥ y t ω = P.T *ᵥ ys t ω := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  set Q : Ω → ℝ := fun ω => quad P.W (P.T *ᵥ (y (t0 + k) ω - ys (t0 + k) ω)) with hQ
  have hQ0 : 0 ≤ Q := fun ω => quad_nonneg P.W_posDef.posSemidef _
  have hnn : ∀ j, ∀ᵐ ω ∂S.μ, 0 ≤ S.E t0
      (fun ω' => quad P.W (P.T *ᵥ (y (t0 + j) ω' - ys (t0 + j) ω'))) ω := fun j =>
    condExp_nonneg (Eventually.of_forall fun ω' => quad_nonneg P.W_posDef.posSemidef _)
  have h0 : S.E t0 (fun ω' => φ t0 ω' ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω' - ys t0 ω'))) =ᵐ[S.μ] 0 :=
    (S.E_congr hinit t0).trans (by rw [show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, S.E_zero])
  have hEQ : S.E t0 Q =ᵐ[S.μ] 0 := by
    filter_upwards [m_lagrangian_gap_init hs hy, ae_all_iff.2 hnn, hJ, h0] with ω h1 h2 h3 h4
    rw [h3, h4, Pi.zero_apply, mul_zero, sub_zero, sub_self] at h1
    have hz := congrFun ((hasSum_zero_iff_of_nonneg
      fun j => mul_nonneg (pow_pos P.β_pos j).le (h2 j)).mp h1) k
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', P.β_pos.ne', ne_eq, false_and,
      false_or] at hz
    exact hz
  obtain ⟨Ky, hKy⟩ := hy.2.2.1
  obtain ⟨Kys, hKys⟩ := hs.1.2.2.1
  obtain ⟨KQ, hKQ⟩ := exists_bound_lossFn P.T P.W 0 (Ky + Kys)
  have hQi : Integrable Q S.μ := by
    refine integrable_of_bound (aesm_comp (g := fun v => quad P.W (P.T *ᵥ v))
      (fun i => (((hy.2.2.2 (t0 + k) i).mono (S.𝓕.le _)).aestronglyMeasurable).sub
        (((hs.1.2.2.2 (t0 + k) i).mono (S.𝓕.le _)).aestronglyMeasurable))
      (by unfold quad; fun_prop)) (K := KQ) ?_
    filter_upwards [hKy (t0 + k), hKys (t0 + k)] with ω h1 h2
    have := hKQ (y (t0 + k) ω - ys (t0 + k) ω) fun i =>
      (abs_sub _ _).trans (add_le_add (h1 i) (h2 i))
    simpa [lossFn, hQ] using this
  have hint : ∫ ω, Q ω ∂S.μ = 0 := by
    rw [← S.integral_E t0 Q]
    exact integral_eq_zero_of_ae hEQ
  have hQae : Q =ᵐ[S.μ] 0 := (integral_eq_zero_iff_of_nonneg hQ0 hQi).mp hint
  filter_upwards [hQae] with ω hq
  simp only [hQ, Pi.zero_apply, quad, mul_eq_zero, one_div, inv_eq_zero,
    OfNat.ofNat_ne_zero, false_or] at hq
  by_contra hne
  have hne' : P.T *ᵥ (y (t0 + k) ω - ys (t0 + k) ω) ≠ 0 := by
    rw [mulVec_sub]
    exact sub_ne_zero.mpr hne
  have hpos := P.W_posDef.dotProduct_mulVec_pos hne'
  rw [star_trivial] at hpos
  linarith

omit [Fintype ιτ] in
/-- Woodford (2003), p. 541 (tool): the initial multiplier term vanishes when the two plans have
the same `Z_{t₀}` and the same `Ẽ z_{t₀}` a.s. -/
theorem init_zero_of {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hZ : ∀ᵐ ω ∂S.μ, Zpart (y t0 ω) = Zpart (ys t0 ω))
    (hE : ∀ᵐ ω ∂S.μ, P.sys.Et *ᵥ zpart (y t0 ω) = P.sys.Et *ᵥ zpart (ys t0 ω)) :
    ∀ᵐ ω ∂S.μ, φ t0 ω ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω - ys t0 ω)) = 0 := by
  filter_upwards [hZ, hE] with ω e1 e2
  rw [mulVec_sub, P.sys.Itil_mulVec, P.sys.Itil_mulVec, e1, e2, sub_self, dotProduct_zero]

/-- Woodford (2003), p. 541 (**sufficiency for the weak system**): a solution of the weak system
(1.1) + (1.9) is optimal a.s. subject to its own initial constraint `Ẽ z_{t₀} = ē`. -/
theorem m_optimalSubjectTo_of_I {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystemI S P c t0 Z0 M0 y φ) :
    MOptimalSubjectTo S P c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y := by
  refine ⟨h.1, Eventually.of_forall fun _ => rfl, fun y' hy' he' => ?_⟩
  refine m_J_le_init h hy' (init_zero_of ?_ he')
  filter_upwards [hy'.2.1, h.1.2.1] with ω e1 e2
  rw [e1, e2]

omit [Fintype ιτ] in
/-- Woodford (2003), p. 541 (tool): the initial multiplier term vanishes when the two plans have
the same `Z_{t₀}` a.s. and the initial multiplier `M_{t₀−1}` is zero a.s. -/
theorem init_zero_of_M {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hZ : ∀ᵐ ω ∂S.μ, Zpart (y t0 ω) = Zpart (ys t0 ω))
    (hM : ∀ᵐ ω ∂S.μ, Mpart (φ t0 ω) = 0) :
    ∀ᵐ ω ∂S.μ, φ t0 ω ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω - ys t0 ω)) = 0 := by
  filter_upwards [hZ, hM] with ω e1 e2
  rw [mulVec_sub, P.sys.Itil_mulVec, P.sys.Itil_mulVec, e1]
  simp only [dotProduct, Fintype.sum_sum_type, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, sub_self,
    mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_eq_zero fun r _ => ?_
  have := congrFun e2 r
  simp only [Mpart, Pi.zero_apply] at this
  rw [this, zero_mul]

omit [Fintype ιτ] in
/-- Woodford (2003), p. 541 (tool): with the same `Z_{t₀}`, the initial multiplier term is
`M_{t₀−1}'(Ẽ z_{t₀} − Ẽ z*_{t₀})`. -/
theorem init_term_eq (P : LQProblem ιZ ιz ιτ) {a b : (ιZ ⊕ ιz) ⊕ Unit → ℝ} {f : ιZ ⊕ ιz → ℝ}
    (hZ : Zpart a = Zpart b) :
    f ⬝ᵥ (P.sys.Itil *ᵥ (a - b)) = Mpart f ⬝ᵥ (P.sys.Et *ᵥ zpart a - P.sys.Et *ᵥ zpart b) := by
  rw [mulVec_sub, P.sys.Itil_mulVec, P.sys.Itil_mulVec, hZ]
  simp only [dotProduct, Fintype.sum_sum_type, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, sub_self,
    mul_zero, Finset.sum_const_zero, zero_add, Mpart]

/-! ### The variational inequality -/

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.10), p. 542 (**the variational step, almost surely**): if for every `w`
with `L'w = 0` and every real `s`, `s·w'd ≤ J` a.s., then `d` lies in the range of `L` a.s.
(countably many scalings `±n`, and a basis of `ker L'`). -/
theorem ae_orth_kernel {S : MeasExpectationSystem Ω} (L : Matrix ιz ιz ℝ) {d : Ω → ιz → ℝ}
    {J : Ω → ℝ} (h : ∀ w : ιz → ℝ, Lᵀ *ᵥ w = 0 → ∀ s : ℝ, ∀ᵐ ω ∂S.μ, s * (w ⬝ᵥ d ω) ≤ J ω) :
    ∀ᵐ ω ∂S.μ, d ω ∈ LinearMap.range L.mulVecLin := by
  -- each kernel vector is a.s. orthogonal to `d`
  have h1 : ∀ w : ιz → ℝ, Lᵀ *ᵥ w = 0 → ∀ᵐ ω ∂S.μ, w ⬝ᵥ d ω = 0 := by
    intro w hw
    have hn : ∀ n : ℕ, ∀ᵐ ω ∂S.μ, (n : ℝ) * (w ⬝ᵥ d ω) ≤ J ω ∧ -(n : ℝ) * (w ⬝ᵥ d ω) ≤ J ω :=
      fun n => (h w hw n).and (h w hw (-n))
    filter_upwards [ae_all_iff.2 hn] with ω hω
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨n, hn⟩ := exists_nat_gt (J ω / -(w ⬝ᵥ d ω))
      have h2 := (hω n).2
      rw [div_lt_iff₀ (by linarith)] at hn
      linarith
    · obtain ⟨n, hn⟩ := exists_nat_gt (J ω / (w ⬝ᵥ d ω))
      have h2 := (hω n).1
      rw [div_lt_iff₀ hgt] at hn
      linarith
  -- a basis of `ker L'`
  set b := Module.finBasis ℝ (LinearMap.ker (Lᵀ).mulVecLin) with hb
  have hbk : ∀ i, Lᵀ *ᵥ (b i : ιz → ℝ) = 0 := fun i => by
    have := LinearMap.mem_ker.mp (b i).2
    rwa [Matrix.mulVecLin_apply] at this
  filter_upwards [ae_all_iff.2 fun i => h1 _ (hbk i)] with ω hω
  refine mem_range_of_orth L (d ω) fun w hw => ?_
  have hwK : w ∈ LinearMap.ker (Lᵀ).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hw
  have hsum := congrArg (Subtype.val) (b.sum_repr ⟨w, hwK⟩)
  rw [Submodule.coe_sum] at hsum
  have hsum' : ∑ i, ((b.repr ⟨w, hwK⟩ i • b i : LinearMap.ker (Lᵀ).mulVecLin) : ιz → ℝ) = w :=
    hsum
  rw [← hsum']
  simp only [Submodule.coe_smul, sum_dotProduct, smul_dotProduct, hω, smul_zero,
    Finset.sum_const_zero]

/-! ### Necessity -/

omit [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), p. 539 (tool): a plan feasible with `Z_{t₀} = Z₀'` is feasible with any `Z₀`
a.s. equal to `Z₀'`. -/
theorem mFeasible_congr {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ} (hZ : ∀ᵐ ω ∂S.μ, Z0' ω = Z0 ω)
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (h : MFeasible S P c t0 Z0' y) :
    MFeasible S P c t0 Z0 y :=
  ⟨h.1, by filter_upwards [h.2.1, hZ] with ω e1 e2; rw [e1, e2], h.2.2⟩

/-- **Woodford (2003), p. 541 (necessity of the first-order conditions), on every filtered
probability space with Mathlib's conditional expectation.** Under Assumption 8.1 (existence half,
corrected form `OptimalRulesMeasure.MFOCSolvableMB`) and a bounded adapted disturbance, every
bounded plan that minimises (1.2) a.s. among bounded feasible plans subject to `Ẽ z_{t₀} = ē`
satisfies (1.1) + (1.9) a.s., with bounded multipliers (`M_t` known at `t` for `t ≥ t₀`) and an
essentially bounded initial multiplier `M_{t₀−1}` known at `t₀`. No faithfulness, version or
integrability hypothesis: integrability follows from essential boundedness. -/
theorem m_foc_necessary {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (hsolv : MFOCSolvableMB S P t0) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} {ebar : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MOptimalSubjectTo S P c t0 Z0 ebar y) :
    ∃ M0 : Ω → ιz → ℝ, MKnownV S t0 M0 ∧ MBoundedRV S M0 ∧
      ∃ φ, MFOCSystemI S P c t0 Z0 M0 y φ := by
  obtain ⟨hfe, hey, hmin⟩ := hy
  set Z0' : Ω → ιZ → ℝ := fun ω => Zpart (y t0 ω) with hZ0'
  have hZk : MKnownV S t0 Z0' := fun r => hfe.2.2.2 t0 _
  obtain ⟨Ky, hKy⟩ := hfe.2.2.1
  have hZb : MBoundedRV S Z0' := ⟨Ky, (hKy t0).mono fun ω h r => h _⟩
  obtain ⟨y0, φ0, h0⟩ := hsolv c Z0' 0 hcb hca hZk hZb
    ⟨0, Eventually.of_forall fun _ _ => by simp⟩ (fun _ => stronglyMeasurable_const)
  obtain ⟨H, Φ, hH⟩ := exists_homResp_meas hsolv
  have hfeas : ∀ y', MFeasible S P c t0 Z0' y' → MFeasible S P c t0 Z0 y' :=
    fun y' h => mFeasible_congr hfe.2.1 h
  set L := Lmat P t0 H with hL
  set d : Ω → ιz → ℝ := fun ω => P.sys.Et *ᵥ zpart (y t0 ω) - P.sys.Et *ᵥ zpart (y0 t0 ω)
    with hd
  have hdk : MKnownV S t0 d := fun i =>
    sm_comp₂ (hfe.2.2.2 t0) (h0.1.2.2.2 t0)
      (g := fun p => (P.sys.Et *ᵥ zpart p.1 - P.sys.Et *ᵥ zpart p.2) i)
      (by unfold zpart; fun_prop)
  obtain ⟨K0, hK0⟩ := h0.1.2.2.1
  obtain ⟨KE, hKE⟩ := exists_bound_mulVec P.sys.Et (max Ky K0)
  have hdb : MBoundedRV S d := ⟨KE + KE, by
    filter_upwards [hKy t0, hK0 t0] with ω e1 e2 i
    exact (abs_sub _ _).trans (add_le_add
      (hKE _ (fun j => (e1 _).trans (le_max_left _ _)) i)
      (hKE _ (fun j => (e2 _).trans (le_max_right _ _)) i))⟩
  have hdi : ∀ i, Integrable (fun ω => d ω i) S.μ := fun i => by
    obtain ⟨Kd, hKd⟩ := hdb
    exact integrable_of_bound ((hdk i).mono (S.𝓕.le t0)).aestronglyMeasurable
      (hKd.mono fun ω h => h i)
  have hZy0 : ∀ᵐ ω ∂S.μ, Zpart (y t0 ω) = Zpart (y0 t0 ω) := h0.1.2.1.mono fun ω e => e.symm
  -- the variational inequality
  have hvar : ∀ w : ιz → ℝ, Lᵀ *ᵥ w = 0 → ∀ s : ℝ, ∀ᵐ ω ∂S.μ,
      s * (w ⬝ᵥ d ω) ≤ P.β * MJ S P t0 y ω := by
    intro w hw s
    set Ms : Ω → ιz → ℝ := fun _ => s • w with hMs
    have hc := m_combo h0 hH (M := Ms) (fun _ => stronglyMeasurable_const)
      ⟨∑ r, |(s • w) r|, Eventually.of_forall fun _ r => Finset.single_le_sum
        (f := fun r => |(s • w) r|) (fun _ _ => abs_nonneg _) (Finset.mem_univ r)⟩
    have hwLw : w ⬝ᵥ (L *ᵥ w) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]
    have hinit : (fun ω' => comboF t0 φ0 Φ Ms t0 ω' ⬝ᵥ
        (P.sys.Itil *ᵥ (y t0 ω' - comboF t0 y0 H Ms t0 ω'))) =ᵐ[S.μ]
          fun ω' => s * (w ⬝ᵥ d ω') := by
      filter_upwards [hZy0, hc.2.2.2.2.1] with ω e1 e2
      have hZc : Zpart (y t0 ω) = Zpart (comboF t0 y0 H Ms t0 ω) := by
        rw [comboF_of_le le_rfl, e1]
        funext r
        simp [Zpart, mulVec, dotProduct, hH.2.2.1]
      rw [init_term_eq P hZc, e2, eq110_combo, ← hL]
      simp only [hMs, hd, mulVec_smul]
      rw [show P.sys.Et *ᵥ zpart (y t0 ω) - (P.sys.Et *ᵥ zpart (y0 t0 ω) + s • L *ᵥ w) =
        (P.sys.Et *ᵥ zpart (y t0 ω) - P.sys.Et *ᵥ zpart (y0 t0 ω)) - s • L *ᵥ w by abel,
        dotProduct_sub, smul_dotProduct, smul_dotProduct, dotProduct_smul, hwLw]
      simp [smul_eq_mul]
    have hEk : S.E t0 (fun ω' => s * (w ⬝ᵥ d ω')) = fun ω' => s * (w ⬝ᵥ d ω') := by
      refine S.E_of_stronglyMeasurable ?_ ?_
      · exact sm_comp hdk (g := fun v => s * (w ⬝ᵥ v)) (by fun_prop)
      · simp only [dotProduct, Finset.mul_sum]
        exact integrable_finsetSum _ fun i _ => ((hdi i).const_mul (w i)).const_mul s
    have hnn : ∀ k, ∀ᵐ ω ∂S.μ, 0 ≤ S.E t0 (fun ω' => quad P.W (P.T *ᵥ
        (y (t0 + k) ω' - comboF t0 y0 H Ms (t0 + k) ω'))) ω := fun k =>
      condExp_nonneg (Eventually.of_forall fun ω' => quad_nonneg P.W_posDef.posSemidef _)
    have hJ0 : ∀ᵐ ω ∂S.μ, 0 ≤ MJ S P t0 (comboF t0 y0 H Ms) ω :=
      condExp_nonneg (Eventually.of_forall fun ω' => tsum_nonneg fun k =>
        mul_nonneg (pow_nonneg P.β_pos.le k) (quad_nonneg P.W_posDef.posSemidef _))
    filter_upwards [m_lagrangian_gap_init hc hfe, S.E_congr hinit t0, ae_all_iff.2 hnn, hJ0]
      with ω g e n j0
    rw [e, hEk] at g
    have h3 := g.nonneg fun k => mul_nonneg (pow_pos P.β_pos k).le (n k)
    have hβi : P.β * P.β⁻¹ = 1 := mul_inv_cancel₀ P.β_pos.ne'
    have h4 : P.β⁻¹ * (s * (w ⬝ᵥ d ω)) ≤ MJ S P t0 y ω := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 P.β_pos.le
    rw [← mul_assoc, hβi, one_mul] at h5
    exact h5
  have hrange := ae_orth_kernel (S := S) L hvar
  obtain ⟨R, hR⟩ := exists_rightInv L
  set M0 : Ω → ιz → ℝ := fun ω => R *ᵥ d ω with hM0
  have hM0k : MKnownV S t0 M0 := fun i => sm_comp hdk (g := fun v => (R *ᵥ v) i) (by fun_prop)
  have hM0b : MBoundedRV S M0 := by
    obtain ⟨Kd, hKd⟩ := hdb
    obtain ⟨K, hK⟩ := exists_bound_mulVec R Kd
    exact ⟨K, hKd.mono fun ω h => hK _ h⟩
  have hc := m_combo h0 hH hM0k hM0b
  have hEc : ∀ᵐ ω ∂S.μ, P.sys.Et *ᵥ zpart (comboF t0 y0 H M0 t0 ω) =
      P.sys.Et *ᵥ zpart (y t0 ω) := by
    filter_upwards [hrange] with ω hω
    rw [eq110_combo, ← hL, hM0]
    beta_reduce
    rw [hR _ hω, hd]
    beta_reduce
    abel
  have hZc : ∀ᵐ ω ∂S.μ, Zpart (y t0 ω) = Zpart (comboF t0 y0 H M0 t0 ω) := by
    filter_upwards [hc.1.2.1] with ω e
    rw [e]
  have hin := init_zero_of (φ := comboF t0 φ0 Φ M0) hZc (hEc.mono fun ω e => e.symm)
  have hle := m_J_le_init hc hfe hin
  have hge := hmin _ (hfeas _ hc.1) (by filter_upwards [hEc, hey] with ω e1 e2; rw [e1, e2])
  have hJ : MJ S P t0 y =ᵐ[S.μ] MJ S P t0 (comboF t0 y0 H M0) := by
    filter_upwards [hle, hge] with ω e1 e2
    exact le_antisymm e2 e1
  have htar := m_targets_eq_init hc hfe hin hJ
  refine ⟨M0, hM0k, hM0b, comboF t0 φ0 Φ M0, hfe, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    fun t ht => ?_⟩
  filter_upwards [hc.2.2.2.2.2 t ht, htar t ht] with ω e1 e2
  rw [e2]
  exact e1

/-- **Woodford (2003), pp. 539–541: optimality subject to (1.6) ⟺ the first-order conditions, on
every filtered probability space.** Under Assumption 8.1 (existence half, corrected form) and a
bounded adapted disturbance, a bounded plan minimises (1.2) a.s. among bounded feasible plans
subject to `Ẽ z_{t₀} = ē` iff it meets the constraint a.s. and solves (1.1) + (1.9) a.s. with some
essentially bounded initial multiplier `M_{t₀−1}` known at `t₀`. -/
theorem m_optimalSubjectTo_iff {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (hsolv : MFOCSolvableMB S P t0) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} {ebar : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} :
    MOptimalSubjectTo S P c t0 Z0 ebar y ↔
      (∀ᵐ ω ∂S.μ, P.sys.Et *ᵥ zpart (y t0 ω) = ebar ω) ∧
        ∃ M0 : Ω → ιz → ℝ, MKnownV S t0 M0 ∧ MBoundedRV S M0 ∧
          ∃ φ, MFOCSystemI S P c t0 Z0 M0 y φ := by
  refine ⟨fun hy => ⟨hy.2.1, m_foc_necessary hsolv hcb hca hy⟩, ?_⟩
  rintro ⟨he, M0, -, -, φ, h⟩
  have ho := m_optimalSubjectTo_of_I h
  exact ⟨h.1, he, fun y' hy' he' => ho.2.2 y' hy' (by
    filter_upwards [he', he] with ω e1 e2
    rw [e1, e2])⟩

/-! ### The full system with `M_{t₀−1}` known at `t₀ − 1` -/

/-- Woodford (2003), p. 540: **from the weak to the full system.** If the initial multiplier of a
solution of the weak system has a version known at `t₀ − 1`, the plan solves the full
`OptimalRulesMeasure.MFOCSystem` (every `M_t` known at `t`, including `M_{t₀−1}`) with that
version. -/
theorem mFOCSystem_of_I {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystemI S P c t0 Z0 M0 y φ)
    (hM : ∀ r, AEStronglyMeasurable[S.𝓕 (t0 - 1)] (fun ω => M0 ω r) S.μ) :
    ∃ M0' : Ω → ιz → ℝ, (∀ᵐ ω ∂S.μ, M0' ω = M0 ω) ∧ MKnownV S (t0 - 1) M0' ∧
      ∃ φ', MFOCSystem S P c t0 Z0 M0' y φ' := by
  obtain ⟨hfe, ⟨Kφ, hKφ⟩, hmφ, hMφ, hM0, hfoc⟩ := h
  set g : ιz → Ω → ℝ := fun r => (hM r).mk _ with hgdef
  have hg : ∀ r, StronglyMeasurable[S.𝓕 (t0 - 1)] (g r) := fun r => (hM r).stronglyMeasurable_mk
  have hgae : ∀ r, (fun ω => M0 ω r) =ᵐ[S.μ] g r := fun r => (hM r).ae_eq_mk
  set M0' : Ω → ιz → ℝ := fun ω r => g r ω with hM0'
  set φ' : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun t ω =>
    if t < t0 then 0 else if t = t0 then Sum.elim (fun j => φ t0 ω (Sum.inl j)) (fun r => g r ω)
      else φ t ω with hφ'
  have hgt : ∀ t, t0 < t → φ' t = φ t := fun t ht => by
    funext ω
    simp only [hφ', show ¬ t < t0 by omega, show t ≠ t0 by omega, ↓reduceIte]
  have h0 : φ' t0 =ᵐ[S.μ] φ t0 := by
    filter_upwards [hM0, ae_all_iff.2 hgae] with ω e1 e2
    simp only [hφ', lt_irrefl, ↓reduceIte]
    funext ρ
    rcases ρ with j | r
    · rfl
    · simp only [Sum.elim_inr]
      rw [← e2 r, ← e1]
      rfl
  have hMM : ∀ᵐ ω ∂S.μ, M0' ω = M0 ω := by
    filter_upwards [ae_all_iff.2 hgae] with ω e
    funext r
    exact (e r).symm
  refine ⟨M0', hMM, hg, φ', hfe, ⟨max Kφ 0, fun t => ?_⟩, fun t i => ?_, fun t r => ?_, ?_,
    fun t ht => ?_⟩
  · rcases lt_trichotomy t t0 with h1 | rfl | h1
    · refine Eventually.of_forall fun ω i => ?_
      simp only [hφ', h1, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact le_max_right _ _
    · filter_upwards [h0, hKφ t] with ω e1 e2 i
      rw [e1]
      exact (e2 i).trans (le_max_left _ _)
    · filter_upwards [hKφ t] with ω e i
      rw [hgt t h1]
      exact (e i).trans (le_max_left _ _)
  · rcases lt_trichotomy t t0 with h1 | rfl | h1
    · simp only [hφ', h1, ↓reduceIte, Pi.zero_apply]
      exact aestronglyMeasurable_const
    · exact (hmφ t i).congr (h0.mono fun ω e => (congrFun e i).symm)
    · rw [hgt t h1]
      exact hmφ t i
  · rcases lt_trichotomy (t + 1) t0 with h1 | h1 | h1
    · simp only [hφ', h1, ↓reduceIte, Pi.zero_apply]
      exact stronglyMeasurable_const
    · have ht : t = t0 - 1 := by omega
      simp only [hφ', h1, lt_irrefl, ↓reduceIte, Sum.elim_inr]
      rw [ht]
      exact hg r
    · rw [hgt (t + 1) h1]
      exact hMφ t (by omega) r
  · refine Eventually.of_forall fun ω => ?_
    simp only [hφ', lt_irrefl, ↓reduceIte]
    rfl
  · filter_upwards [hfoc t ht, h0] with ω e1 e2
    rw [hgt (t + 1) (by omega)]
    rcases eq_or_lt_of_le ht with h1 | h1
    · subst h1
      rw [e2]
      exact e1
    · rw [hgt t h1]
      exact e1

/-- **Woodford (2003), p. 541, necessity of (1.9) in the full form, under `PredInfo`**: if each
random variable known at `t₀` is a.s. known at `t₀ − 1` (no news at `t₀`), every plan optimal
subject to `Ẽ z_{t₀} = ē` solves `OptimalRulesMeasure.MFOCSystem` with an essentially bounded
initial multiplier known at `t₀ − 1`. -/
theorem m_foc_necessary_pred {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (hsolv : MFOCSolvableMB S P t0) (hpred : PredInfo S t0) {c : ℕ → Ω → ιz → ℝ}
    (hcb : MBoundedV S c) (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} {ebar : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MOptimalSubjectTo S P c t0 Z0 ebar y) :
    ∃ M0 : Ω → ιz → ℝ, MKnownV S (t0 - 1) M0 ∧ MBoundedRV S M0 ∧
      ∃ φ, MFOCSystem S P c t0 Z0 M0 y φ := by
  obtain ⟨M0, hk, ⟨K, hK⟩, φ, h⟩ := m_foc_necessary hsolv hcb hca hy
  obtain ⟨M0', he, hk', φ', h'⟩ := mFOCSystem_of_I h fun r => hpred _ (hk r)
  exact ⟨M0', hk', ⟨K, by filter_upwards [he, hK] with ω e1 e2; rw [e1]; exact e2⟩, φ', h'⟩

/-- **Woodford (2003), p. 541, necessity of (1.9) in the full form at `t₀ = 0`**: every plan
optimal subject to `Ẽ z₀ = ē` solves `OptimalRulesMeasure.MFOCSystem`. -/
theorem m_foc_necessary_zero {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    (hsolv : MFOCSolvableMB S P 0) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} {ebar : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MOptimalSubjectTo S P c 0 Z0 ebar y) :
    ∃ M0 : Ω → ιz → ℝ, MKnownV S 0 M0 ∧ MBoundedRV S M0 ∧
      ∃ φ, MFOCSystem S P c 0 Z0 M0 y φ := by
  obtain ⟨M0, hk, ⟨K, hK⟩, φ, h⟩ := m_foc_necessary hsolv hcb hca hy
  obtain ⟨M0', he, hk', φ', h'⟩ := mFOCSystem_of_I h fun r => (hk r).aestronglyMeasurable
  exact ⟨M0', hk', ⟨K, by filter_upwards [he, hK] with ω e1 e2; rw [e1]; exact e2⟩, φ', h'⟩

/-- **Woodford (2003), p. 541, necessity of (1.9) under the book's literal Assumption 8.1**
(existence for every `Z_{t₀}`, `M_{t₀−1}` known at `t₀`, `OptimalRulesMeasure.MFOCSolvable`):
every plan optimal subject to `Ẽ z_{t₀} = ē` solves the full `OptimalRulesMeasure.MFOCSystem`
with an essentially bounded initial multiplier known at `t₀ − 1` (the book's assumption forces the
needed multiplier to be predictable, `OptimalRulesMeasure.necessary_of_mFOCSystem`). -/
theorem m_foc_necessary_book {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (hsolv : MFOCSolvable S P t0) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} {ebar : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MOptimalSubjectTo S P c t0 Z0 ebar y) :
    ∃ M0 : Ω → ιz → ℝ, MKnownV S (t0 - 1) M0 ∧ MBoundedRV S M0 ∧
      ∃ φ, MFOCSystem S P c t0 Z0 M0 y φ := by
  have hMB : MFOCSolvableMB S P t0 := fun c' Z0' M0' hcb' hca' hZk _ _ hMk =>
    hsolv c' Z0' M0' hcb' hca' hZk fun i => (hMk i).mono (S.𝓕.mono (Nat.sub_le t0 1))
  obtain ⟨M0, hk, ⟨K, hK⟩, φ, h⟩ := m_foc_necessary hMB hcb hca hy
  have hZk : MKnownV S t0 (fun ω => Zpart (y t0 ω)) := fun r => hy.1.2.2.2 t0 _
  obtain ⟨y1, φ1, h1⟩ := hsolv c _ M0 hcb hca hZk hk
  have hpre := (necessary_of_mFOCSystem h1).2.2
  have hM : ∀ r, AEStronglyMeasurable[S.𝓕 (t0 - 1)] (fun ω => M0 ω r) S.μ := by
    rcases Nat.eq_zero_or_pos t0 with h0 | h0
    · subst h0
      exact fun r => (hk r).aestronglyMeasurable
    · exact hpre h0
  obtain ⟨M0', he, hk', φ', h'⟩ := mFOCSystem_of_I h hM
  exact ⟨M0', hk', ⟨K, by filter_upwards [he, hK] with ω e1 e2; rw [e1]; exact e2⟩, φ', h'⟩

/-! ### The `t₀`-optimal plan -/

/-- Woodford (2003), p. 538 and (1.8): `y` is `t₀`-optimal — a bounded feasible plan that
minimises (1.2) a.s. among all bounded feasible plans from `t₀` (no initial constraint). -/
def MT0Optimal (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ)
    (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  MFeasible S P c t0 Z0 y ∧ ∀ y', MFeasible S P c t0 Z0 y' → MJ S P t0 y ≤ᵐ[S.μ] MJ S P t0 y'

/-- Woodford (2003), p. 541 and (1.8) (**sufficiency**): a solution of (1.1) + (1.9) with
`M_{t₀−1} = 0` is `t₀`-optimal, on every filtered probability space. -/
theorem m_t0Optimal_of_foc {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystem S P c t0 Z0 0 y φ) :
    MT0Optimal S P c t0 Z0 y := by
  refine ⟨h.1, fun y' hy' => m_J_le_init (mFOCSystemI_of h) hy' (init_zero_of_M ?_ ?_)⟩
  · filter_upwards [hy'.2.1, h.1.2.1] with ω e1 e2
    rw [e1, e2]
  · exact h.2.2.2.2.1

/-- **Woodford (2003), p. 541 and (1.8), on every filtered probability space (necessity for the
`t₀`-optimal plan)**: under Assumption 8.1 (existence half, corrected form), every `t₀`-optimal
plan solves (1.1) + (1.9) a.s. with `M_{t₀−1} = 0` (the full `OptimalRulesMeasure.MFOCSystem`). -/
theorem m_t0Optimal_foc_necessary {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {t0 : ℕ} (hsolv : MFOCSolvableMB S P t0) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : MT0Optimal S P c t0 Z0 y) : ∃ φ, MFOCSystem S P c t0 Z0 0 y φ := by
  obtain ⟨hfe, hmin⟩ := hy
  have hZk : MKnownV S t0 (fun ω => Zpart (y t0 ω)) := fun r => hfe.2.2.2 t0 _
  obtain ⟨Ky, hKy⟩ := hfe.2.2.1
  obtain ⟨y0, φ0, h0⟩ := hsolv c _ 0 hcb hca hZk ⟨Ky, (hKy t0).mono fun ω h r => h _⟩
    ⟨0, Eventually.of_forall fun _ _ => by simp⟩ (fun _ => stronglyMeasurable_const)
  have hin := init_zero_of_M (S := S) (P := P) (y := y) (ys := y0) (φ := φ0)
    (h0.1.2.1.mono fun ω e => e.symm) h0.2.2.2.2.1
  have hle := m_J_le_init (mFOCSystemI_of h0) hfe hin
  have hge := hmin y0 (mFeasible_congr hfe.2.1 h0.1)
  have hJ : MJ S P t0 y =ᵐ[S.μ] MJ S P t0 y0 := by
    filter_upwards [hle, hge] with ω e1 e2
    exact le_antisymm e2 e1
  have htar := m_targets_eq_init (mFOCSystemI_of h0) hfe hin hJ
  refine ⟨φ0, hfe, h0.2.1, h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2.1, fun t ht => ?_⟩
  filter_upwards [h0.2.2.2.2.2 t ht, htar t ht] with ω e1 e2
  rw [e2]
  exact e1

/-- **Woodford (2003), p. 541 and (1.8): `t₀`-optimality ⟺ (1.1) + (1.9) with `M_{t₀−1} = 0`**, on
every filtered probability space, under Assumption 8.1 (existence half, corrected form). -/
theorem m_t0Optimal_iff {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (hsolv : MFOCSolvableMB S P t0) {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} :
    MT0Optimal S P c t0 Z0 y ↔ ∃ φ, MFOCSystem S P c t0 Z0 0 y φ :=
  ⟨m_t0Optimal_foc_necessary hsolv hcb hca, fun ⟨_, h⟩ => m_t0Optimal_of_foc h⟩

/-! ### The models of §3 -/

/-- **Woodford (2003), §3.1, pp. 583–584, with p. 541: for the basic model on every filtered
probability space, optimality subject to (1.6) ⟺ the first-order conditions** (no hypothesis
beyond the admissible calibration and a bounded adapted disturbance; Assumption 8.1 from
`OptimalRulesMeasureStabilityModels.NK.nk_m_assumption81MB`). -/
theorem nk_m_optimalSubjectTo_iff (c : IRuleBasic.Calib) (hc : c.Adm)
    (S : MeasExpectationSystem Ω) (t0 : ℕ) {cd : ℕ → Ω → Fin 2 → ℝ} (hcb : MBoundedV S cd)
    (hca : MAdaptedV S cd) {Z0 : Ω → Empty → ℝ} {ebar : Ω → Fin 2 → ℝ}
    {y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ} :
    MOptimalSubjectTo S (GeneralLinks.nkProblem c hc) cd t0 Z0 ebar y ↔
      (∀ᵐ ω ∂S.μ, (GeneralLinks.nkProblem c hc).sys.Et *ᵥ zpart (y t0 ω) = ebar ω) ∧
        ∃ M0 : Ω → Fin 2 → ℝ, MKnownV S t0 M0 ∧ MBoundedRV S M0 ∧
          ∃ φ, MFOCSystemI S (GeneralLinks.nkProblem c hc) cd t0 Z0 M0 y φ :=
  m_optimalSubjectTo_iff (OptimalRulesMeasureStabilityModels.NK.nk_m_assumption81MB c hc S
    t0).solvable hcb hca

/-- **Woodford (2003), §3.2, pp. 592–593, with p. 541: for the inflation-inertia model
(`0 < γ ≤ 1`) on every filtered probability space, optimality subject to (1.6) ⟺ the first-order
conditions** (Assumption 8.1 from
`OptimalRulesMeasureStabilityModels.Inertia.in_m_assumption81MB`). -/
theorem in_m_optimalSubjectTo_iff (c : IRuleBasic.Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (S : MeasExpectationSystem Ω) (t0 : ℕ) {cd : ℕ → Ω → Fin 2 → ℝ}
    (hcb : MBoundedV S cd) (hca : MAdaptedV S cd) {Z0 : Ω → Unit → ℝ} {ebar : Ω → Fin 2 → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} :
    MOptimalSubjectTo S (GeneralLinksInertia.inProblem c γ hc hγ0.le) cd t0 Z0 ebar y ↔
      (∀ᵐ ω ∂S.μ, (GeneralLinksInertia.inProblem c γ hc hγ0.le).sys.Et *ᵥ zpart (y t0 ω) =
        ebar ω) ∧
        ∃ M0 : Ω → Fin 2 → ℝ, MKnownV S t0 M0 ∧ MBoundedRV S M0 ∧
          ∃ φ, MFOCSystemI S (GeneralLinksInertia.inProblem c γ hc hγ0.le) cd t0 Z0 M0 y φ :=
  m_optimalSubjectTo_iff (OptimalRulesMeasureStabilityModels.Inertia.in_m_assumption81MB c γ hc
    hγ0 hγ1 S t0).solvable hcb hca

end Woodford.OptimalPolicyRules.TidyR6bFOCMeasure
