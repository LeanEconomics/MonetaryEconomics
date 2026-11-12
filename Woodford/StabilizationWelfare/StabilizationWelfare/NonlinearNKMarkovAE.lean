/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovGeneral
import StabilizationWelfare.ExpectationsMeasureIID

/-!
# Sequence-space determinacy on a general probability space (almost-sure form)

Woodford (2003), *Interest and Prices*, Appendix A.3 (pp. 631–635, (A.11)–(A.13)), Chapter 4,
Proposition 4.3 (p. 254) and Chapter 6, §1.

`NonlinearNKMarkovGeneral` proved uniqueness and existence of the bounded solution of the exact
stochastic equilibrium conditions for every core `ExpectationSystem`. Mathlib's conditional
expectation is linear and contractive only almost surely and only on integrable variables, so it is
not a Markov operator on all functions; this module redoes the argument in almost-sure form, for
an ARBITRARY filtered probability space (`ExpectationsMeasure.MeasExpectationSystem`), on
processes that are a.s. strongly measurable and essentially bounded.

* The one-step forecast operator on processes `MvA` (`(MvA h)_t = μ[h_{t+1} | 𝓕_t]`), with
  a.s. linearity, congruence, contraction and its iterates (`MvA_bd`, `MvA_gd`, `MvA_add`,
  `MvA_smul`, `MvA_mulVec`, `MvA_congr`, `iterA_*`).
* `bound_improve_ae`, `twoBlock_ae`, **`apriori_ae`**: the a-priori bound `‖v‖ ≤ K‖Lv‖` a.s.,
  with the same constant `K = Kap p` as in the pointwise case.
* **`seq_uniqueness_ae`**: two essentially bounded, a.s. measurable solutions within `ρ` of the
  almost-sure exact conditions coincide almost surely at every date.
* The inverse on essentially bounded processes: `fwdSolA`, `fwdSolA_spec` (the forward series
  passes through `μ[· | 𝓕_t]` by dominated convergence, `ExpectationsMeasure.MeasExpectationSystem
  .E_hasSum`), `linSolA`, `linSolA_spec`, `bd_linSolA`, `linSolA_Lop`, `linSolA_sub`.
* **`seq_existence_ae`**: the Newton contraction `z ↦ z − L⁻¹Φ(z)` with Picard iterates converging
  almost surely: existence and a.s. uniqueness within `r` of a solution of the exact stochastic
  conditions for every a.s. measurable disturbance process with `‖e_t‖ ≤ δ` a.s.
* **`ar1_iid_equilibrium`**: the instance with an AR(1) driven by i.i.d. innovations with ANY
  bounded-support law (`ExpectationsMeasureIID.iidSystem`, `ar1`).
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovAE

open MeasureTheory Filter Topology Asymptotics
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-! ## Processes and the forecast operator -/

/-- An a.s. bound on a process: `‖h_t‖ ≤ C` a.s. at every date. -/
def Bd {α : Type*} [Norm α] (h : ℕ → Ω → α) (C : ℝ) : Prop := ∀ t, ∀ᵐ ω ∂E.μ, ‖h t ω‖ ≤ C

/-- A process that is a.s. strongly measurable at every date. -/
def Gd {α : Type*} [TopologicalSpace α] (h : ℕ → Ω → α) : Prop :=
  ∀ t, AEStronglyMeasurable (h t) E.μ

/-- Woodford (2003), (A.11): the one-step forecast of a vector process,
`(MvA h)_t = μ[h_{t+1} | 𝓕_t]` coordinatewise. -/
noncomputable def MvA {n : ℕ} (h : ℕ → Ω → Fin n → ℝ) : ℕ → Ω → Fin n → ℝ :=
  fun t ω i => E.E t (fun ω' => h (t + 1) ω' i) ω

/-- Components of an a.s. measurable vector are a.s. measurable. -/
theorem aesm_comp {n : ℕ} {f : Ω → Fin n → ℝ} (hf : AEStronglyMeasurable f E.μ) (i : Fin n) :
    AEStronglyMeasurable (fun ω => f ω i) E.μ :=
  (continuous_apply i).comp_aestronglyMeasurable hf

/-- A vector with a.s. measurable components is a.s. measurable. -/
theorem aesm_vec {n : ℕ} {f : Ω → Fin n → ℝ} (hf : ∀ i, AEStronglyMeasurable (fun ω => f ω i) E.μ) :
    AEStronglyMeasurable f E.μ :=
  (aemeasurable_pi_iff.2 fun i => (hf i).aemeasurable).aestronglyMeasurable

/-- Components of an a.s. bounded vector are a.s. bounded. -/
theorem bd_comp {n : ℕ} {f : Ω → Fin n → ℝ} {C : ℝ} (hf : ∀ᵐ ω ∂E.μ, ‖f ω‖ ≤ C) (i : Fin n) :
    ∀ᵐ ω ∂E.μ, |f ω i| ≤ C := by
  filter_upwards [hf] with ω hω
  have := norm_le_pi_norm (f ω) i
  rw [Real.norm_eq_abs] at this
  exact this.trans hω

/-- A vector with a.s. bounded components is a.s. bounded. -/
theorem bd_vec {n : ℕ} {f : Ω → Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ∀ᵐ ω ∂E.μ, |f ω i| ≤ C) : ∀ᵐ ω ∂E.μ, ‖f ω‖ ≤ C := by
  filter_upwards [ae_all_iff.2 hf] with ω hω
  exact (pi_norm_le_iff_of_nonneg hC).2 fun i => by rw [Real.norm_eq_abs]; exact hω i

/-- Bounded a.s. measurable variables are integrable. -/
theorem integrable_of {f : Ω → ℝ} (hm : AEStronglyMeasurable f E.μ) {C : ℝ}
    (hb : ∀ᵐ ω ∂E.μ, |f ω| ≤ C) : Integrable f E.μ :=
  Integrable.of_bound hm C (by filter_upwards [hb] with ω hω; rwa [Real.norm_eq_abs])

/-- Woodford (2003), (A.11): forecasts are a.s. measurable. -/
theorem MvA_gd {n : ℕ} (h : ℕ → Ω → Fin n → ℝ) : Gd E (MvA E h) := fun t =>
  aesm_vec E fun _ => ((E.stronglyMeasurable_E t _).mono (E.𝓕.le t)).aestronglyMeasurable

/-- Woodford (2003), (A.11): forecasts keep a.s. bounds. -/
theorem MvA_bd {n : ℕ} {h : ℕ → Ω → Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C) (hb : Bd E h C) :
    Bd E (MvA E h) C := fun t =>
  bd_vec E hC fun i => E.abs_E_le (bd_comp E (hb (t + 1)) i) t

/-- Woodford (2003), (A.11): forecasts of a.s. equal processes are a.s. equal. -/
theorem MvA_congr {n : ℕ} {h g : ℕ → Ω → Fin n → ℝ} (hhg : ∀ t, h t =ᵐ[E.μ] g t) (t : ℕ) :
    MvA E h t =ᵐ[E.μ] MvA E g t := by
  have : ∀ i : Fin n, E.E t (fun ω' => h (t + 1) ω' i) =ᵐ[E.μ] E.E t (fun ω' => g (t + 1) ω' i) :=
    fun i => E.E_congr (by filter_upwards [hhg (t + 1)] with ω hω; rw [hω]) t
  filter_upwards [ae_all_iff.2 this] with ω hω
  funext i; exact hω i

/-- Woodford (2003), (A.11): forecasts are a.s. additive on bounded measurable processes. -/
theorem MvA_add {n : ℕ} {h g : ℕ → Ω → Fin n → ℝ} (hh : Gd E h) (hg : Gd E g) {C D : ℝ}
    (hhb : Bd E h C) (hgb : Bd E g D) (t : ℕ) :
    MvA E (fun s ω => h s ω + g s ω) t =ᵐ[E.μ] fun ω => MvA E h t ω + MvA E g t ω := by
  have : ∀ i : Fin n, E.E t (fun ω' => h (t + 1) ω' i + g (t + 1) ω' i) =ᵐ[E.μ]
      E.E t (fun ω' => h (t + 1) ω' i) + E.E t (fun ω' => g (t + 1) ω' i) := fun i =>
    E.E_add (integrable_of E (aesm_comp E (hh (t + 1)) i) (bd_comp E (hhb (t + 1)) i))
      (integrable_of E (aesm_comp E (hg (t + 1)) i) (bd_comp E (hgb (t + 1)) i)) t
  filter_upwards [ae_all_iff.2 this] with ω hω
  funext i; exact hω i

/-- Woodford (2003), (A.11): forecasts are a.s. homogeneous. -/
theorem MvA_smul {n : ℕ} (c : ℝ) (h : ℕ → Ω → Fin n → ℝ) (t : ℕ) :
    MvA E (fun s ω => c • h s ω) t =ᵐ[E.μ] fun ω => c • MvA E h t ω := by
  have : ∀ i : Fin n, E.E t (fun ω' => c * h (t + 1) ω' i) =ᵐ[E.μ]
      c • E.E t (fun ω' => h (t + 1) ω' i) := fun i => E.E_smul c _ t
  filter_upwards [ae_all_iff.2 this] with ω hω
  funext i; simpa [MvA] using hω i

/-- Woodford (2003), (A.11): forecasts a.s. commute with a constant matrix. -/
theorem MvA_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {h : ℕ → Ω → Fin n → ℝ}
    (hh : Gd E h) {C : ℝ} (hhb : Bd E h C) (t : ℕ) :
    MvA E (fun s ω => B.mulVec (h s ω)) t =ᵐ[E.μ] fun ω => B.mulVec (MvA E h t ω) := by
  have : ∀ i : Fin n, E.E t (fun ω' => ∑ j, B i j * h (t + 1) ω' j) =ᵐ[E.μ]
      fun ω => ∑ j, B i j * E.E t (fun ω' => h (t + 1) ω' j) ω := by
    intro i
    have hint : ∀ j, Integrable (fun ω' => h (t + 1) ω' j) E.μ := fun j =>
      integrable_of E (aesm_comp E (hh (t + 1)) j) (bd_comp E (hhb (t + 1)) j)
    have e : (fun ω' => ∑ j, B i j * h (t + 1) ω' j) = ∑ j, B i j • fun ω' => h (t + 1) ω' j := by
      funext ω'; simp [Finset.sum_apply]
    rw [e]
    have h1 := condExp_finsetSum (μ := E.μ) (m := E.𝓕 t) (s := Finset.univ)
      (f := fun j => B i j • fun ω' => h (t + 1) ω' j) fun j _ => (hint j).smul (B i j)
    have h2 : ∀ j, E.E t (B i j • fun ω' => h (t + 1) ω' j) =ᵐ[E.μ]
        B i j • E.E t (fun ω' => h (t + 1) ω' j) := fun j => E.E_smul _ _ t
    filter_upwards [h1, ae_all_iff.2 h2] with ω hω1 hω2
    change E.μ[∑ j, B i j • fun ω' => h (t + 1) ω' j | E.𝓕 t] ω = _ at hω1 ⊢
    rw [hω1, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hω2 j
  filter_upwards [ae_all_iff.2 this] with ω hω
  funext i
  simp only [MvA, Matrix.mulVec, dotProduct]
  exact hω i

/-- Forecasts of constants are the constants. -/
theorem MvA_const {n : ℕ} (c : Fin n → ℝ) : MvA E (fun _ _ => c) = fun _ _ => c := by
  funext t ω i
  simp only [MvA]
  rw [E.E_const]

/-! ## Improving a.s. bounds -/

/-- If every a.s. bound `U` of `‖f‖` improves to `b + qU` (`0 ≤ q < 1`), then `‖f‖ ≤ b/(1−q)`
a.s. -/
theorem bound_improve_ae {α : Type*} [Norm α] {f : ℕ → Ω → α} {b q U0 : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hU0 : Bd E f U0) (himp : ∀ U, Bd E f U → Bd E f (b + q * U)) :
    Bd E f (b / (1 - q)) := by
  have hn : ∀ n : ℕ, Bd E f (b / (1 - q) + q ^ n * (U0 - b / (1 - q))) := by
    intro n
    induction n with
    | zero => simpa using hU0
    | succ n ih =>
      have h := himp _ ih
      have e : b + q * (b / (1 - q) + q ^ n * (U0 - b / (1 - q))) =
          b / (1 - q) + q ^ (n + 1) * (U0 - b / (1 - q)) := by
        have : 1 - q ≠ 0 := by linarith
        field_simp; ring
      rwa [e] at h
  intro t
  filter_upwards [ae_all_iff.2 fun n => hn n t] with ω hω
  have ht : Tendsto (fun n : ℕ => b / (1 - q) + q ^ n * (U0 - b / (1 - q))) atTop
      (𝓝 (b / (1 - q) + 0 * (U0 - b / (1 - q)))) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _)
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht hω

/-! ## Iterated forecasts and the IS–AS block -/

/-- Iterated forecasts `MvAᵏ h`. -/
noncomputable def iterA {n : ℕ} (k : ℕ) (h : ℕ → Ω → Fin n → ℝ) : ℕ → Ω → Fin n → ℝ :=
  (MvA E)^[k] h

/-- Woodford (2003), (A.11): one more forecast step, outermost. -/
theorem iterA_succ {n : ℕ} (k : ℕ) (h : ℕ → Ω → Fin n → ℝ) :
    iterA E (k + 1) h = MvA E (iterA E k h) := by
  simp only [iterA, Function.iterate_succ_apply']

/-- Woodford (2003), (A.11): one more forecast step, innermost. -/
theorem iterA_succ' {n : ℕ} (k : ℕ) (h : ℕ → Ω → Fin n → ℝ) :
    iterA E (k + 1) h = iterA E k (MvA E h) := by
  simp only [iterA, Function.iterate_succ_apply]

/-- Woodford (2003), (A.11): iterated forecasts of good processes are good. -/
theorem iterA_gd {n : ℕ} {h : ℕ → Ω → Fin n → ℝ} (hh : Gd E h) (k : ℕ) : Gd E (iterA E k h) := by
  cases k with
  | zero => exact hh
  | succ k => rw [iterA_succ]; exact MvA_gd E _

/-- Woodford (2003), (A.11): iterated forecasts keep a.s. bounds. -/
theorem iterA_bd {n : ℕ} {h : ℕ → Ω → Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C) (hh : Bd E h C) (k : ℕ) :
    Bd E (iterA E k h) C := by
  induction k with
  | zero => exact hh
  | succ k ih => rw [iterA_succ]; exact MvA_bd E hC ih

/-- Woodford (2003), (A.11): iterated forecasts respect a.s. equality. -/
theorem iterA_congr {n : ℕ} {h g : ℕ → Ω → Fin n → ℝ} (hhg : ∀ t, h t =ᵐ[E.μ] g t) (k : ℕ) :
    ∀ t, iterA E k h t =ᵐ[E.μ] iterA E k g t := by
  induction k with
  | zero => exact hhg
  | succ k ih => intro t; rw [iterA_succ, iterA_succ]; exact MvA_congr E ih t

/-- `B·h` of a good process is good. -/
theorem gd_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {h : ℕ → Ω → Fin n → ℝ} (hh : Gd E h) :
    Gd E (fun s ω => B.mulVec (h s ω)) := fun t =>
  (Matrix.mulVecLin B).toContinuousLinearMap.continuous.comp_aestronglyMeasurable (hh t)

/-- `B·h` of a bounded process is bounded. -/
theorem bd_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {h : ℕ → Ω → Fin n → ℝ} {C : ℝ}
    (hh : Bd E h C) : Bd E (fun s ω => B.mulVec (h s ω)) (mnorm B * C) := fun t => by
  filter_upwards [hh t] with ω hω
  exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left hω (mnorm_nonneg _))

/-- Sums of good processes are good. -/
theorem gd_add {n : ℕ} {h g : ℕ → Ω → Fin n → ℝ} (hh : Gd E h) (hg : Gd E g) :
    Gd E (fun s ω => h s ω + g s ω) := fun t => (hh t).add (hg t)

/-- Sums of bounded processes are bounded. -/
theorem bd_add {n : ℕ} {h g : ℕ → Ω → Fin n → ℝ} {C D : ℝ} (hh : Bd E h C) (hg : Bd E g D) :
    Bd E (fun s ω => h s ω + g s ω) (C + D) := fun t => by
  filter_upwards [hh t, hg t] with ω h1 h2
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- Iterated forecasts of an affine process: `Mᵏ(Bw + b) = BMᵏw + Mᵏb` a.s. -/
theorem iterA_affine {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {w b : ℕ → Ω → Fin n → ℝ}
    (hw : Gd E w) (hb : Gd E b) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hwb : Bd E w C)
    (hbb : Bd E b D) (k : ℕ) :
    ∀ t, iterA E k (fun s ω => B.mulVec (w s ω) + b s ω) t =ᵐ[E.μ]
      fun ω => B.mulVec (iterA E k w t ω) + iterA E k b t ω := by
  induction k with
  | zero => intro t; exact Eventually.of_forall fun ω => rfl
  | succ k ih =>
    intro t
    rw [iterA_succ, iterA_succ, iterA_succ]
    refine (MvA_congr E ih t).trans ?_
    have h1 := MvA_add E (gd_mulVec E B (iterA_gd E hw k)) (iterA_gd E hb k)
      (bd_mulVec E B (iterA_bd E hC hwb k)) (iterA_bd E hD hbb k) t
    have h2 := MvA_mulVec E B (iterA_gd E hw k) (iterA_bd E hC hwb k) t
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]

/-- Woodford (2003), (A.13) a.s.: iterating `u = AMu + b`,
`u_t = ∑_{k<n} Aᵏ(Mᵏb)_t + Aⁿ(Mⁿu)_t` a.s. -/
theorem iterate_eq_ae {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {u b : ℕ → Ω → Fin n → ℝ}
    (hb : Gd E b) {U B : ℝ} (hU : 0 ≤ U) (hB : 0 ≤ B) (hub : Bd E u U)
    (hbb : Bd E b B)
    (heq : ∀ t, u t =ᵐ[E.μ] fun ω => A.mulVec (MvA E u t ω) + b t ω) (m : ℕ) :
    ∀ t, u t =ᵐ[E.μ] fun ω => ∑ k ∈ Finset.range m, (A ^ k).mulVec (iterA E k b t ω) +
      (A ^ m).mulVec (iterA E m u t ω) := by
  induction m with
  | zero => intro t; exact Eventually.of_forall fun ω => by simp [iterA]
  | succ m ih =>
    intro t
    have h1 := iterA_congr E heq m t
    have h2 := iterA_affine E A (MvA_gd E u) hb hU hB (MvA_bd E hU hub) hbb m t
    filter_upwards [ih t, h1, h2] with ω e0 e1 e2
    rw [e0, e1, e2, ← iterA_succ', Finset.sum_range_succ, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, ← pow_succ]
    abel

/-- Woodford (2003), Proposition 4.3 and App. A.3, a.s. (**the IS–AS block bound**): if
`u = AMu + b` a.s. with `u, b` bounded and measurable and `‖b‖ ≤ B` a.s., then
`‖u‖ ≤ C_A B` a.s. -/
theorem twoBlock_ae {p : Par} (hp : p.Std) {u b : ℕ → Ω → Fin 2 → ℝ} (hb : Gd E b)
    {U0 Bb : ℝ} (hBb : 0 ≤ Bb) (hu0 : Bd E u U0) (hbb : Bd E b Bb)
    (heq : ∀ t, u t =ᵐ[E.μ] fun ω => (Amat p).mulVec (MvA E u t ω) + b t ω) :
    Bd E u (CA p * Bb) := by
  have himp : ∀ U, Bd E u U → Bd E u
      ((∑ k ∈ Finset.range (Nhalf p), mnorm (Amat p ^ k)) * Bb + 1 / 2 * U) := by
    intro U hU t
    have hU0' : ∀ᵐ ω ∂E.μ, 0 ≤ U := by
      filter_upwards [hU t] with ω hω; exact (norm_nonneg _).trans hω
    by_cases hUn : 0 ≤ U
    · have hit := iterate_eq_ae E (Amat p) hb hUn hBb hU hbb heq (Nhalf p) t
      have hbk : ∀ᵐ ω ∂E.μ, ∀ k, ‖iterA E k b t ω‖ ≤ Bb :=
        ae_all_iff.2 fun k => iterA_bd E hBb hbb k t
      filter_upwards [hit, hbk, iterA_bd E hUn hU (Nhalf p) t] with ω e hk hN
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans ?_
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun k _ => (norm_mulVec_le _ _).trans
          (mul_le_mul_of_nonneg_left (hk k) (mnorm_nonneg _))
      · exact (norm_mulVec_le _ _).trans (mul_le_mul (mnorm_Nhalf hp) hN (norm_nonneg _)
          (by norm_num))
    · have : ∀ᵐ ω ∂E.μ, False := by
        filter_upwards [hU0'] with ω hω; exact hUn hω
      filter_upwards [this] with ω hω; exact hω.elim
  have h := bound_improve_ae E (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hu0 himp
  intro t
  filter_upwards [h t] with ω hω
  calc _ ≤ _ := hω
    _ = CA p * Bb := by unfold CA; ring

/-! ## The linearised operator and the a-priori bound, a.s. -/

/-- Woodford (2003), (A.12) a.s.: `(L v)_t = DQ v_t + μ[DN v_{t+1} | 𝓕_t]`. -/
noncomputable def LopA (p : Par) (v : ℕ → Ω → Fin 4 → ℝ) : ℕ → Ω → Fin 4 → ℝ :=
  fun t ω => DQ0 p (v t ω) + MvA E (fun s ω' => DN0 p (v s ω')) t ω

/-- The scalar one-step forecast `μ[f_{t+1} | 𝓕_t]`. -/
noncomputable def Ms (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => E.E t (f (t + 1))

/-- Two-term a.s. linearity of `E_t`. -/
theorem E_lin2 {f g : Ω → ℝ} (hf : Integrable f E.μ) (hg : Integrable g E.μ) (a b : ℝ) (t : ℕ) :
    E.E t (fun ω => a * f ω + b * g ω) =ᵐ[E.μ] fun ω => a * E.E t f ω + b * E.E t g ω := by
  have e : (fun ω => a * f ω + b * g ω) = a • f + b • g := by funext; simp
  rw [e]
  filter_upwards [E.E_add (hf.smul a) (hg.smul b) t, E.E_smul a f t, E.E_smul b g t]
    with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]; rfl

/-- `DQ` of a good process is good. -/
theorem gd_DQ0 {p : Par} {v : ℕ → Ω → Fin 4 → ℝ} (hv : Gd E v) : Gd E (fun s ω => DQ0 p (v s ω)) :=
  fun t => by
    have hc : Continuous (DQ0 p) := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp only [DQ0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val] <;> fun_prop
    exact hc.comp_aestronglyMeasurable (hv t)

/-- The linearised operator maps good processes to good processes. -/
theorem gd_LopA {p : Par} {v : ℕ → Ω → Fin 4 → ℝ} (hv : Gd E v) : Gd E (LopA E p v) :=
  gd_add E (gd_DQ0 E hv) (MvA_gd E _)

/-- Woodford (2003), (A.12) a.s.: the four components of the linearised operator. -/
theorem LopA_apply {p : Par} {v : ℕ → Ω → Fin 4 → ℝ} (hv : Gd E v) {V : ℝ} (hvb : Bd E v V)
    (t : ℕ) : ∀ᵐ ω ∂E.μ,
    LopA E p v t ω 0 = (p.σ + p.φy) * v t ω 0 + p.φ * v t ω 1 -
        p.σ * Ms E (fun s ω => v s ω 0) t ω - Ms E (fun s ω => v s ω 1) t ω ∧
    LopA E p v t ω 1 = v t ω 2 - (1 - p.α * p.β) * (1 - p.σ) * v t ω 0 -
        p.α * p.β * (p.θ - 1) * Ms E (fun s ω => v s ω 1) t ω -
        p.α * p.β * Ms E (fun s ω => v s ω 2) t ω ∧
    LopA E p v t ω 2 = v t ω 3 - (1 - p.α * p.β) * (1 + p.ω) * v t ω 0 -
        p.α * p.β * (p.θ * (1 + p.ω)) * Ms E (fun s ω => v s ω 1) t ω -
        p.α * p.β * Ms E (fun s ω => v s ω 3) t ω ∧
    LopA E p v t ω 3 = p.α * (p.θ - 1) * v t ω 1 -
        (1 - p.α) * (p.θ - 1) * (v t ω 3 - v t ω 2) / p.c0 := by
  have hi : ∀ i, Integrable (fun ω => v (t + 1) ω i) E.μ := fun i =>
    integrable_of E (aesm_comp E (hv (t + 1)) i) (bd_comp E (hvb (t + 1)) i)
  have h0 := E_lin2 E (hi 0) (hi 1) (-p.σ) (-1) t
  have h1 := E_lin2 E (hi 1) (hi 2) (-(p.α * p.β * (p.θ - 1))) (-(p.α * p.β)) t
  have h2 := E_lin2 E (hi 1) (hi 3) (-(p.α * p.β * (p.θ * (1 + p.ω)))) (-(p.α * p.β)) t
  filter_upwards [h0, h1, h2] with ω e0 e1 e2
  have m0 : MvA E (fun s ω' => DN0 p (v s ω')) t ω 0 =
      E.E t (fun ω => -p.σ * v (t + 1) ω 0 + -1 * v (t + 1) ω 1) ω := by
    simp only [MvA, DN0, Matrix.cons_val_zero]; congr 2; funext ω'; ring
  have m1 : MvA E (fun s ω' => DN0 p (v s ω')) t ω 1 = E.E t (fun ω =>
      -(p.α * p.β * (p.θ - 1)) * v (t + 1) ω 1 + -(p.α * p.β) * v (t + 1) ω 2) ω := by
    simp only [MvA, DN0, Matrix.cons_val_one, Matrix.cons_val_zero]; congr 2; funext ω'; ring
  have m2 : MvA E (fun s ω' => DN0 p (v s ω')) t ω 2 = E.E t (fun ω =>
      -(p.α * p.β * (p.θ * (1 + p.ω))) * v (t + 1) ω 1 + -(p.α * p.β) * v (t + 1) ω 3) ω := by
    simp only [MvA, DN0, Matrix.cons_val]; congr 2; funext ω'; ring
  have m3 : MvA E (fun s ω' => DN0 p (v s ω')) t ω 3 = 0 := by
    simp only [MvA, DN0, Matrix.cons_val]
    rw [E.E_const]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [LopA, Pi.add_apply, m0, e0, DQ0, Matrix.cons_val_zero, Ms]; ring
  · simp only [LopA, Pi.add_apply, m1, e1, DQ0, Matrix.cons_val_one, Matrix.cons_val_zero, Ms]
    ring
  · simp only [LopA, Pi.add_apply, m2, e2, DQ0, Matrix.cons_val, Ms]; ring
  · simp only [LopA, Pi.add_apply, m3, DQ0, Matrix.cons_val, add_zero]

/-- The price-index component of the linearised operator holds at every state. -/
theorem LopA_three {p : Par} (v : ℕ → Ω → Fin 4 → ℝ) (t : ℕ) (ω : Ω) :
    LopA E p v t ω 3 = p.α * (p.θ - 1) * v t ω 1 -
      (1 - p.α) * (p.θ - 1) * (v t ω 3 - v t ω 2) / p.c0 := by
  have m3 : MvA E (fun s ω' => DN0 p (v s ω')) t ω 3 = 0 := by
    simp only [MvA, DN0, Matrix.cons_val]
    rw [E.E_const]
  simp only [LopA, Pi.add_apply, m3, DQ0, Matrix.cons_val, add_zero]

/-- Forecasts are a.s. measurable (scalar). -/
theorem aesm_E (t : ℕ) (f : Ω → ℝ) : AEStronglyMeasurable (E.E t f) E.μ :=
  ((E.stronglyMeasurable_E t f).mono (E.𝓕.le t)).aestronglyMeasurable

/-- Division by a constant keeps a.s. measurability. -/
theorem aesm_div {f : Ω → ℝ} (hf : AEStronglyMeasurable f E.μ) (c : ℝ) :
    AEStronglyMeasurable (fun ω => f ω / c) E.μ := by
  simpa [div_eq_mul_inv] using hf.mul_const c⁻¹

/-- Woodford (2003), App. A.3, (A.12)–(A.13) and Proposition 4.3, **almost surely**: under the
Taylor principle, every a.s. measurable, essentially bounded process `v` satisfies
`‖v_t‖ ≤ K ‖(Lv)‖` a.s. with the constant `K = Kap p` of the pointwise case. -/
theorem apriori_ae {p : Par} (hp : p.Std) {v : ℕ → Ω → Fin 4 → ℝ} (hv : Gd E v) {V0 a : ℝ}
    (hV0 : 0 ≤ V0) (hvb : Bd E v V0) (ha0 : 0 ≤ a) (ha : Bd E (LopA E p v) a) :
    Bd E v (Kap p * a) := by
  set r := LopA E p v with hrdef
  have hrG : Gd E r := gd_LopA E hv
  have hrc : ∀ i t, ∀ᵐ ω ∂E.μ, |r t ω i| ≤ a := fun i t => bd_comp E (ha t) i
  have hvc : ∀ i t, ∀ᵐ ω ∂E.μ, |v t ω i| ≤ V0 := fun i t => bd_comp E (hvb t) i
  have hint : ∀ i t, Integrable (fun ω => v t ω i) E.μ := fun i t =>
    integrable_of E (aesm_comp E (hv t) i) (hvc i t)
  have hintr : ∀ i t, Integrable (fun ω => r t ω i) E.μ := fun i t =>
    integrable_of E (aesm_comp E (hrG t) i) (hrc i t)
  have hd := hp.dd_pos
  have hcR := hp.cR_pos
  have hk3 := hp.k3_pos
  have hab0 := hp.ab_pos
  have hab1 := hp.ab_lt_one
  have hc0 := hp.c0_pos
  have h1α : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  have hθ1 : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  -- the reset gap, at every state
  have hG : ∀ t ω, v t ω 3 - v t ω 2 = p.cR * v t ω 1 - p.k3 * r t ω 3 := fun t ω => by
    have h3 := LopA_three E (p := p) v t ω
    rw [hrdef, h3]
    unfold Par.cR Par.k3
    field_simp
    ring
  have hMG : ∀ t, ∀ᵐ ω ∂E.μ, Ms E (fun s ω => v s ω 3) t ω - Ms E (fun s ω => v s ω 2) t ω =
      p.cR * Ms E (fun s ω => v s ω 1) t ω - p.k3 * Ms E (fun s ω => r s ω 3) t ω := by
    intro t
    have e1 := E.E_sub (hint 3 (t + 1)) (hint 2 (t + 1)) t
    have ef : (fun ω => v (t + 1) ω 3) - (fun ω => v (t + 1) ω 2) =
        fun ω => p.cR * v (t + 1) ω 1 + -p.k3 * r (t + 1) ω 3 := by
      funext ω; simp only [Pi.sub_apply]; rw [hG]; ring
    have e2 := E_lin2 E (hint 1 (t + 1)) (hintr 3 (t + 1)) p.cR (-p.k3) t
    rw [ef] at e1
    filter_upwards [e1, e2] with ω h1 h2
    simp only [Ms]
    rw [Pi.sub_apply] at h1
    rw [← h1, h2]; ring
  -- the NKPC residual
  set s1 : ℕ → Ω → ℝ := fun t ω => (r t ω 2 - r t ω 1 + p.k3 * r t ω 3 -
    p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω) / p.cR with hs1
  have hNK : ∀ t, ∀ᵐ ω ∂E.μ, v t ω 1 - p.β * Ms E (fun s ω => v s ω 1) t ω -
      p.κ * v t ω 0 = s1 t ω := by
    intro t
    filter_upwards [LopA_apply E hv hvb t, hMG t] with ω hc hmg
    obtain ⟨-, c1, c2, -⟩ := hc
    have hk' : p.κ * p.cR = (1 - p.α * p.β) * (p.ω + p.σ) := by
      rw [hp.κ_eq]; field_simp
    have hab := hp.ab_c
    have hGt := hG t ω
    simp only [hs1]
    rw [eq_div_iff hcR.ne']
    rw [← hrdef] at c1 c2
    rw [c1, c2]
    unfold Par.c0 at hab
    linear_combination (-1 : ℝ) * hGt + p.α * p.β * hmg - v t ω 0 * hk' +
      Ms E (fun s ω => v s ω 1) t ω * hab
  have hm3 : ∀ t, ∀ᵐ ω ∂E.μ, |Ms E (fun s ω => r s ω 3) t ω| ≤ a := fun t =>
    E.abs_E_le (hrc 3 (t + 1)) t
  have hS1 : ∀ t, ∀ᵐ ω ∂E.μ, |s1 t ω| ≤ S1c p * a := by
    intro t
    filter_upwards [hrc 1 t, hrc 2 t, hrc 3 t, hm3 t] with ω h1 h2 h3 h4
    simp only [hs1, S1c]
    rw [abs_div, abs_of_pos hcR, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcR]
    calc |r t ω 2 - r t ω 1 + p.k3 * r t ω 3 - p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω|
        ≤ |r t ω 2| + |r t ω 1| + p.k3 * |r t ω 3| +
            p.α * p.β * p.k3 * |Ms E (fun s ω => r s ω 3) t ω| := by
          have e1 := abs_sub (r t ω 2 - r t ω 1 + p.k3 * r t ω 3)
            (p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω)
          have e2 := abs_add_le (r t ω 2 - r t ω 1) (p.k3 * r t ω 3)
          have e3 := abs_sub (r t ω 2) (r t ω 1)
          rw [abs_mul (p.α * p.β * p.k3), abs_of_pos (by positivity : 0 < p.α * p.β * p.k3),
            abs_mul, abs_of_pos hk3] at *
          linarith
      _ ≤ a + a + p.k3 * a + p.α * p.β * p.k3 * a := by gcongr
      _ = (2 + p.k3 + p.α * p.β * p.k3) * a := by ring
  -- the IS–AS block
  set u : ℕ → Ω → Fin 2 → ℝ := fun t ω => ![v t ω 0, v t ω 1] with hu
  set b : ℕ → Ω → Fin 2 → ℝ := fun t ω => ![(r t ω 0 - p.φ * s1 t ω) / p.dd,
    (p.κ * r t ω 0 + (p.σ + p.φy) * s1 t ω) / p.dd] with hb
  have hs1G : Gd E s1 := fun t => by
    simp only [hs1]
    exact aesm_div E ((((aesm_comp E (hrG t) 2).sub (aesm_comp E (hrG t) 1)).add
      ((aesm_comp E (hrG t) 3).const_mul p.k3)).sub ((aesm_E E t _).const_mul
        (p.α * p.β * p.k3))) p.cR
  have hbG : Gd E b := fun t => aesm_vec E fun i => by
    fin_cases i
    · simp only [hb, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact aesm_div E ((aesm_comp E (hrG t) 0).sub ((hs1G t).const_mul p.φ)) p.dd
    · simp only [hb, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact aesm_div E (((aesm_comp E (hrG t) 0).const_mul p.κ).add
        ((hs1G t).const_mul (p.σ + p.φy))) p.dd
  have hMu : ∀ t ω, MvA E u t ω = ![Ms E (fun s ω => v s ω 0) t ω,
      Ms E (fun s ω => v s ω 1) t ω] := fun t ω => by
    funext i; fin_cases i <;> rfl
  have heq : ∀ t, u t =ᵐ[E.μ] fun ω => (Amat p).mulVec (MvA E u t ω) + b t ω := by
    intro t
    filter_upwards [LopA_apply E hv hvb t, hNK t] with ω hc hnk
    obtain ⟨c0, -, -, -⟩ := hc
    rw [← hrdef] at c0
    rw [hMu]
    funext i
    fin_cases i
    · simp only [hu, hb, Amat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [c0, ← hnk]
      field_simp
      unfold Par.dd
      ring
    · simp only [hu, hb, Amat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
      rw [c0, ← hnk]
      field_simp
      unfold Par.dd
      ring
  have hu0 : Bd E u V0 := fun t => bd_vec E hV0 fun i => by
    fin_cases i
    · simpa [hu] using hvc 0 t
    · simpa [hu] using hvc 1 t
  have hBa : 0 ≤ Bc p * a := mul_nonneg (Bc_nonneg hp) ha0
  have hbb : Bd E b (Bc p * a) := fun t => by
    filter_upwards [hrc 0 t, hS1 t] with ω h0 hs
    have hS1n := S1c_nonneg hp
    have hκ := hp.κ_pos
    have hφ := hp.φ_nonneg
    have hσφ : 0 ≤ p.σ + p.φy := by linarith [hp.σ_pos, hp.φy_nonneg]
    refine (pi_norm_le_iff_of_nonneg hBa).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have hnum : ∀ c1 c2 : ℝ, |c1| ≤ 1 + p.κ → |c2| ≤ p.φ + (p.σ + p.φy) →
        |c1 * r t ω 0 + c2 * s1 t ω| / p.dd ≤ Bc p * a := fun c1 c2 hc1 hc2 => by
      rw [div_le_iff₀ hd]
      unfold Bc
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hd.ne']
      calc |c1 * r t ω 0 + c2 * s1 t ω| ≤ |c1| * |r t ω 0| + |c2| * |s1 t ω| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ (1 + p.κ) * a + (p.φ + (p.σ + p.φy)) * (S1c p * a) := by gcongr
        _ = (1 + p.φ * S1c p + p.κ + (p.σ + p.φy) * S1c p) * a := by ring
    fin_cases i
    · have := hnum 1 (-p.φ) (by rw [abs_one]; linarith)
        (by rw [abs_neg, abs_of_nonneg hφ]; linarith)
      simp only [hb, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
      rw [abs_div, abs_of_pos hd]
      convert this using 3; ring
    · have := hnum p.κ (p.σ + p.φy) (by rw [abs_of_pos hκ]; linarith)
        (by rw [abs_of_nonneg hσφ]; linarith)
      simp only [hb, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue]
      rw [abs_div, abs_of_pos hd]
      exact this
  have hU := twoBlock_ae E hp hbG hBa hu0 hbb heq
  have hyb : ∀ t, ∀ᵐ ω ∂E.μ, |v t ω 0| ≤ Uc p * a := fun t => by
    filter_upwards [hU t] with ω hω
    have := norm_le_pi_norm (u t ω) 0
    simp only [hu, Matrix.cons_val_zero, Real.norm_eq_abs] at this
    unfold Uc; rw [mul_assoc]; exact this.trans hω
  have hpb : ∀ t, ∀ᵐ ω ∂E.μ, |v t ω 1| ≤ Uc p * a := fun t => by
    filter_upwards [hU t] with ω hω
    have := norm_le_pi_norm (u t ω) 1
    simp only [hu, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs] at this
    unfold Uc; rw [mul_assoc]; exact this.trans hω
  -- `F`
  have hFb : Bd E (fun t ω => v t ω 2) (Fc p * a) := by
    have himp : ∀ U, Bd E (fun t ω => v t ω 2) U → Bd E (fun t ω => v t ω 2)
        ((1 + ((1 - p.α * p.β) * |1 - p.σ| + p.α * p.β * (p.θ - 1)) * Uc p) * a +
          p.α * p.β * U) := by
      intro U hU t
      have hU' : ∀ t, ∀ᵐ ω ∂E.μ, |v t ω 2| ≤ U := fun t => by
        filter_upwards [hU t] with ω hω; simpa using hω
      have hmF := E.abs_E_le (hU' (t + 1)) t
      have hmp := E.abs_E_le (hpb (t + 1)) t
      filter_upwards [LopA_apply E hv hvb t, hmF, hmp, hyb t, hrc 1 t] with ω hc hF hP hY hR
      obtain ⟨-, c1, -, -⟩ := hc
      rw [← hrdef] at c1
      have hFx : v t ω 2 = r t ω 1 + (1 - p.α * p.β) * (1 - p.σ) * v t ω 0 +
          p.α * p.β * (p.θ - 1) * Ms E (fun s ω => v s ω 1) t ω +
          p.α * p.β * Ms E (fun s ω => v s ω 2) t ω := by rw [c1]; ring
      rw [Real.norm_eq_abs, hFx]
      have e1 : |(1 - p.α * p.β) * (1 - p.σ) * v t ω 0| ≤
          (1 - p.α * p.β) * |1 - p.σ| * (Uc p * a) := by
        rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 - p.α * p.β)]
        exact mul_le_mul_of_nonneg_left hY (by positivity)
      have e2 : |p.α * p.β * (p.θ - 1) * Ms E (fun s ω => v s ω 1) t ω| ≤
          p.α * p.β * (p.θ - 1) * (Uc p * a) := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < p.α * p.β * (p.θ - 1))]
        exact mul_le_mul_of_nonneg_left hP (by positivity)
      have e3 : |p.α * p.β * Ms E (fun s ω => v s ω 2) t ω| ≤ p.α * p.β * U := by
        rw [abs_mul, abs_of_pos hab0]
        exact mul_le_mul_of_nonneg_left hF hab0.le
      have t1 := abs_add_le (r t ω 1 + (1 - p.α * p.β) * (1 - p.σ) * v t ω 0 +
        p.α * p.β * (p.θ - 1) * Ms E (fun s ω => v s ω 1) t ω)
        (p.α * p.β * Ms E (fun s ω => v s ω 2) t ω)
      have t2 := abs_add_le (r t ω 1 + (1 - p.α * p.β) * (1 - p.σ) * v t ω 0)
        (p.α * p.β * (p.θ - 1) * Ms E (fun s ω => v s ω 1) t ω)
      have t3 := abs_add_le (r t ω 1) ((1 - p.α * p.β) * (1 - p.σ) * v t ω 0)
      nlinarith
    have h := bound_improve_ae E hab0.le hab1 (U0 := V0) (fun t => by
      filter_upwards [hvc 2 t] with ω hω; simpa using hω) himp
    intro t
    filter_upwards [h t] with ω hω
    refine hω.trans (le_of_eq ?_)
    unfold Fc
    have : 1 - p.α * p.β ≠ 0 := by linarith
    field_simp
  have hKb : ∀ t, ∀ᵐ ω ∂E.μ, |v t ω 3| ≤ Kc p * a := fun t => by
    filter_upwards [hFb t, hpb t, hrc 3 t] with ω hF hP hR
    have hKx : v t ω 3 = v t ω 2 + (p.cR * v t ω 1 - p.k3 * r t ω 3) := by rw [← hG t ω]; ring
    rw [hKx]
    have e1 := abs_add_le (v t ω 2) (p.cR * v t ω 1 - p.k3 * r t ω 3)
    have e2 := abs_sub (p.cR * v t ω 1) (p.k3 * r t ω 3)
    rw [abs_mul, abs_of_pos hp.cR_pos, abs_mul (p.k3), abs_of_pos hp.k3_pos] at e2
    have := mul_le_mul_of_nonneg_left hP hp.cR_pos.le
    have := mul_le_mul_of_nonneg_left hR hp.k3_pos.le
    rw [Real.norm_eq_abs] at hF
    unfold Kc
    nlinarith
  have hK0 : 0 ≤ Kap p * a := mul_nonneg (by
    unfold Kap; have := Uc_nonneg hp; have := Fc_nonneg hp; have := Kc_nonneg hp; linarith) ha0
  intro t
  filter_upwards [hyb t, hpb t, hFb t, hKb t] with ω h0 h1 h2 h3
  rw [Real.norm_eq_abs] at h2
  refine (pi_norm_le_iff_of_nonneg hK0).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hUa := mul_nonneg (Uc_nonneg hp) ha0
  have hFa := mul_nonneg (Fc_nonneg hp) ha0
  have hKa := mul_nonneg (Kc_nonneg hp) ha0
  unfold Kap
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; nlinarith
  · simp only [Fin.mk_one, Fin.isValue]; nlinarith
  · simp only [Fin.reduceFinMk, Fin.isValue]; nlinarith
  · simp only [Fin.reduceFinMk, Fin.isValue]; nlinarith

/-! ## Uniqueness among essentially bounded processes -/

/-- Woodford (2003), (A.11) on a probability space (**the exact stochastic conditions almost
surely**): `Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t] = 0` a.s. at every date. -/
def SeqEqmAE (p : Par) (e : ℕ → Ω → Fin 5 → ℝ) (z : ℕ → Ω → Fin 4 → ℝ) : Prop :=
  ∀ t, (fun ω => Qmap p (e t ω, z t ω) + MvA E (fun s ω' => Nmap p (e s ω', z s ω')) t ω)
    =ᵐ[E.μ] 0

/-- Forecasts are a.s. subtractive on bounded measurable processes. -/
theorem MvA_sub {n : ℕ} {h g : ℕ → Ω → Fin n → ℝ} (hh : Gd E h) (hg : Gd E g) {C D : ℝ}
    (hhb : Bd E h C) (hgb : Bd E g D) (t : ℕ) :
    MvA E (fun s ω => h s ω - g s ω) t =ᵐ[E.μ] fun ω => MvA E h t ω - MvA E g t ω := by
  have hng : Gd E (fun s ω => (-1 : ℝ) • g s ω) := fun t => by
    exact ((hg t).const_smul (-1 : ℝ)).congr (Eventually.of_forall fun ω => rfl)
  have hngb : Bd E (fun s ω => (-1 : ℝ) • g s ω) D := fun t => by
    filter_upwards [hgb t] with ω hω; simpa using hω
  have h1 := MvA_add E hh hng hhb hngb t
  have h2 := MvA_smul E (-1) g t
  have e : (fun s ω => h s ω - g s ω) = fun s ω => h s ω + (-1 : ℝ) • g s ω := by
    funext s ω; simp [sub_eq_add_neg]
  rw [e]
  filter_upwards [h1, h2] with ω e1 e2
  rw [e1, e2]; simp [sub_eq_add_neg]

/-- A continuous function of good processes is good. -/
theorem gd_pair {n m k : ℕ} {φ : (Fin n → ℝ) × (Fin m → ℝ) → (Fin k → ℝ)} (hφ : Continuous φ)
    {e : ℕ → Ω → Fin n → ℝ} {z : ℕ → Ω → Fin m → ℝ} (he : Gd E e) (hz : Gd E z) :
    Gd E (fun s ω => φ (e s ω, z s ω)) := fun t =>
  hφ.comp_aestronglyMeasurable ((he t).prodMk (hz t))

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**SEQUENCE-SPACE DETERMINACY ON A GENERAL
PROBABILITY SPACE**): under the Taylor principle there is `ρ > 0` such that on every filtered
probability space, for every a.s. measurable disturbance process with `‖e_t‖ ≤ ρ` a.s., two
a.s. measurable solutions of the exact conditions with Mathlib's conditional expectations and
`‖z_t‖, ‖z′_t‖ ≤ ρ` a.s. coincide almost surely at every date. -/
theorem seq_uniqueness_ae {p : Par} (hp : p.Std) :
    ∃ ρ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 5 → ℝ) (z z' : ℕ → Ω → Fin 4 → ℝ), Gd E e → Gd E z → Gd E z' →
        Bd E e ρ → Bd E z ρ → Bd E z' ρ → SeqEqmAE E p e z → SeqEqmAE E p e z' →
          ∀ t, z t =ᵐ[E.μ] z' t := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_small (contDiff_Qmap (p := p) (n := 1)) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_small (contDiff_Nmap (p := p) (n := 1)) hη0
  set ρ := min ρQ ρN with hρdef
  have hρ0 : 0 < ρ := lt_min hρQ hρN
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    ρ).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hρ0.le))
  refine ⟨ρ, hρ0, fun Ω _ E e z z' he hz hz' heb hzb hz'b hE hE' => ?_⟩
  have hNb : ∀ w : ℕ → Ω → Fin 4 → ℝ, Bd E w ρ →
      Bd E (fun s ω => Nmap p (e s ω, w s ω)) CN := fun w hw t => by
    filter_upwards [heb t, hw t] with ω h1 h2
    exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]; exact max_le h1 h2)
  have hNg : ∀ w : ℕ → Ω → Fin 4 → ℝ, Gd E w → Gd E (fun s ω => Nmap p (e s ω, w s ω)) :=
    fun w hw => gd_pair E (contDiff_Nmap (p := p) (n := 0)).continuous he hw
  set d : ℕ → Ω → Fin 4 → ℝ := fun s ω => z s ω - z' s ω with hd
  have hdG : Gd E d := fun t => (hz t).sub (hz' t)
  have hdb : Bd E d (2 * ρ) := fun t => by
    filter_upwards [hzb t, hz'b t] with ω h1 h2
    exact (norm_sub_le _ _).trans (by linarith)
  have himp : ∀ U, Bd E d U → Bd E d (0 + 1 / 2 * U) := by
    intro U hU
    by_cases hU0 : 0 ≤ U
    · -- the residual bound
      have hRN : Bd E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω) -
          DN0 p (d s ω)) (η * U) := fun t => by
        filter_upwards [heb t, hzb t, hz'b t, hU t] with ω h1 h2 h3 h4
        have := hN (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_right _ _))
          (h2.trans (min_le_right _ _)) (h3.trans (min_le_right _ _))
        rw [fderiv_Nmap_inr] at this
        exact this.trans (mul_le_mul_of_nonneg_left h4 hη0.le)
      have hDNg : Gd E (fun s ω => DN0 p (d s ω)) := fun t =>
        ((gd_pair E (φ := fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) => DN0 p q.1) (by
          refine continuous_pi fun i => ?_
          fin_cases i <;> simp only [DN0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
            Fin.isValue, Matrix.cons_val] <;> fun_prop) hdG hdG) t)
      have hDNb : Bd E (fun s ω => DN0 p (d s ω))
          (‖fderiv ℝ (Nmap p) (0, 0)‖ * (2 * ρ)) := fun t => by
        filter_upwards [hdb t] with ω hω
        rw [← fderiv_Nmap_inr]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left (by rw [norm_pair_zero]; exact hω) (norm_nonneg _))
      have hNdg : Gd E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω)) := fun t =>
        ((hNg z hz) t).sub ((hNg z' hz') t)
      have hNdb : Bd E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω)) (CN + CN) :=
        fun t => by
          filter_upwards [hNb z hzb t, hNb z' hz'b t] with ω h1 h2
          exact (norm_sub_le _ _).trans (add_le_add h1 h2)
      have hLd : Bd E (LopA E p d) (2 * η * U) := by
        intro t
        have s1 := MvA_sub E (hNg z hz) (hNg z' hz') (hNb z hzb) (hNb z' hz'b) t
        have s2 := MvA_sub E hNdg hDNg hNdb hDNb t
        have hRb := MvA_bd E (mul_nonneg hη0.le hU0) hRN t
        filter_upwards [hE t, hE' t, s1, s2, hRb, heb t, hzb t, hz'b t, hU t]
          with ω e1 e2 m1 m2 hR h1 h2 h3 h4
        simp only [Pi.zero_apply] at e1 e2
        have hQx := hQ (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_left _ _))
          (h2.trans (min_le_left _ _)) (h3.trans (min_le_left _ _))
        rw [fderiv_Qmap_inr] at hQx
        have m2' : MvA E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω) -
            DN0 p (d s ω)) t ω = MvA E (fun s ω => Nmap p (e s ω, z s ω)) t ω -
              MvA E (fun s ω => Nmap p (e s ω, z' s ω)) t ω -
              MvA E (fun s ω => DN0 p (d s ω)) t ω := by
          rw [m2, m1]
        have key : LopA E p d t ω = -(Qmap p (e t ω, z t ω) - Qmap p (e t ω, z' t ω) -
            DQ0 p (z t ω - z' t ω)) - MvA E (fun s ω => Nmap p (e s ω, z s ω) -
              Nmap p (e s ω, z' s ω) - DN0 p (d s ω)) t ω := by
          rw [m2']
          simp only [LopA, hd]
          linear_combination (norm := abel_nf) e1 - e2
        rw [key]
        calc _ ≤ _ := norm_sub_le _ _
          _ ≤ η * U + η * U := by
              rw [norm_neg]
              exact add_le_add (hQx.trans (mul_le_mul_of_nonneg_left h4 hη0.le)) hR
          _ = 2 * η * U := by ring
      have h := apriori_ae E hp hdG (by positivity) hdb (by positivity) hLd
      intro t
      filter_upwards [h t] with ω hω
      calc _ ≤ _ := hω
        _ = 0 + 1 / 2 * U := by rw [hη]; field_simp; ring
    · intro t
      have : ∀ᵐ ω ∂E.μ, False := by
        filter_upwards [hU t] with ω hω; exact hU0 ((norm_nonneg _).trans hω)
      filter_upwards [this] with ω hω; exact hω.elim
  have h0 := bound_improve_ae E (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hdb himp
  intro t
  filter_upwards [h0 t] with ω hω
  have : d t ω = 0 := norm_le_zero_iff.1 (by simpa using hω)
  exact sub_eq_zero.1 this

/-! ## The forward series, almost surely -/

/-- Woodford (2003), (A.13) a.s.: the forward series `u_t = ∑ₖ Bᵏ (Mᵏ b)_t`. -/
noncomputable def fwdSolA {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (b : ℕ → Ω → Fin n → ℝ) :
    ℕ → Ω → Fin n → ℝ :=
  fun t ω => ∑' k, (B ^ k).mulVec (iterA E k b t ω)

/-- Woodford (2003), (A.13) a.s. (**the forward solution on a general probability space**): if
`∑ mnorm(Bᵏ) < ∞` and `b` is a.s. measurable with `‖b‖ ≤ B̄` a.s., the forward series is a.s.
measurable, `‖u‖ ≤ (∑ mnorm(Bᵏ))B̄` a.s. and `u = BMu + b` a.s. -/
theorem fwdSolA_spec {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : Summable fun k => mnorm (B ^ k)) {b : ℕ → Ω → Fin n → ℝ} (hb : Gd E b) {Bb : ℝ}
    (hBb : 0 ≤ Bb) (hbb : Bd E b Bb) :
    Gd E (fwdSolA E B b) ∧ Bd E (fwdSolA E B b) ((∑' k, mnorm (B ^ k)) * Bb) ∧
      ∀ t, fwdSolA E B b t =ᵐ[E.μ] fun ω => B.mulVec (MvA E (fwdSolA E B b) t ω) + b t ω := by
  have hsB : Summable fun k => mnorm (B ^ k) * Bb := hB.mul_right Bb
  have hall : ∀ t, ∀ᵐ ω ∂E.μ, ∀ k, ‖iterA E k b t ω‖ ≤ Bb := fun t =>
    ae_all_iff.2 fun k => iterA_bd E hBb hbb k t
  have hterm : ∀ t ω, (∀ k, ‖iterA E k b t ω‖ ≤ Bb) →
      ∀ k, ‖(B ^ k).mulVec (iterA E k b t ω)‖ ≤ mnorm (B ^ k) * Bb := fun t ω h k =>
    (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (h k) (mnorm_nonneg _))
  have hsum : ∀ t ω, (∀ k, ‖iterA E k b t ω‖ ≤ Bb) →
      Summable fun k => (B ^ k).mulVec (iterA E k b t ω) := fun t ω h =>
    Summable.of_norm_bounded hsB (hterm t ω h)
  have hG : Gd E (fwdSolA E B b) := fun t => by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, (B ^ k).mulVec (iterA E k b t ω)) (fun N =>
        Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (Matrix.mulVecLin (B ^ k)).toContinuousLinearMap.continuous.comp_aestronglyMeasurable
            (iterA_gd E hb k t)) ?_
    filter_upwards [hall t] with ω h
    exact (hsum t ω h).hasSum.tendsto_sum_nat
  have hbd : Bd E (fwdSolA E B b) ((∑' k, mnorm (B ^ k)) * Bb) := fun t => by
    filter_upwards [hall t] with ω h
    rw [← tsum_mul_right]
    exact tsum_of_norm_bounded hsB.hasSum (hterm t ω h)
  refine ⟨hG, hbd, fun t => ?_⟩
  -- forecasts pass through the series
  have hcomp : ∀ i : Fin n, ∀ᵐ ω ∂E.μ, HasSum
      (fun k => ((B ^ k).mulVec (iterA E (k + 1) b t ω)) i) (MvA E (fwdSolA E B b) t ω i) := by
    intro i
    set f : ℕ → Ω → ℝ := fun k ω' => ((B ^ k).mulVec (iterA E k b (t + 1) ω')) i with hf
    have hfm : ∀ k, AEStronglyMeasurable (f k) E.μ := fun k =>
      aesm_comp E ((Matrix.mulVecLin (B ^ k)).toContinuousLinearMap.continuous
        |>.comp_aestronglyMeasurable (iterA_gd E hb k (t + 1))) i
    have hfb : ∀ k, ∀ᵐ ω ∂E.μ, |f k ω| ≤ mnorm (B ^ k) * Bb := fun k => by
      filter_upwards [iterA_bd E hBb hbb k (t + 1)] with ω h
      have := norm_le_pi_norm ((B ^ k).mulVec (iterA E k b (t + 1) ω)) i
      rw [Real.norm_eq_abs] at this
      exact this.trans ((norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left h (mnorm_nonneg _)))
    have hH := E.E_hasSum hsB hfm hfb t
    have hcongr : (fun ω' => fwdSolA E B b (t + 1) ω' i) =ᵐ[E.μ] fun ω' => ∑' k, f k ω' := by
      filter_upwards [hall (t + 1)] with ω' h
      simp only [fwdSolA, hf]
      exact Pi.tsum_apply (hsum (t + 1) ω' h) (x := i)
    have hE := E.E_congr hcongr t
    have hk : ∀ k, E.E t (f k) =ᵐ[E.μ] fun ω => ((B ^ k).mulVec (iterA E (k + 1) b t ω)) i :=
      fun k => by
        have := MvA_mulVec E (B ^ k) (iterA_gd E hb k) (iterA_bd E hBb hbb k) t
        filter_upwards [this] with ω hω
        have := congrFun hω i
        simp only [MvA] at this
        rw [iterA_succ]
        exact this
    filter_upwards [hH, hE, ae_all_iff.2 hk] with ω h1 h2 h3
    have e : (fun k => E.E t (f k) ω) = fun k => ((B ^ k).mulVec (iterA E (k + 1) b t ω)) i :=
      funext h3
    rw [e] at h1
    simp only [MvA]
    rw [h2]
    exact h1
  filter_upwards [ae_all_iff.2 hcomp, hall t, hall (t + 1),
    iterA_bd E hBb hbb 0 t] with ω hc h0 _ _
  have hs1 : Summable fun k => (B ^ k).mulVec (iterA E (k + 1) b t ω) :=
    Summable.of_norm_bounded hsB fun k => by
      have h := h0 (k + 1)
      exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left h (mnorm_nonneg _))
  have hMv : MvA E (fwdSolA E B b) t ω = ∑' k, (B ^ k).mulVec (iterA E (k + 1) b t ω) := by
    funext i
    rw [Pi.tsum_apply hs1]
    exact (hc i).tsum_eq.symm
  have hlin : B.mulVec (∑' k, (B ^ k).mulVec (iterA E (k + 1) b t ω)) =
      ∑' k, B.mulVec ((B ^ k).mulVec (iterA E (k + 1) b t ω)) := by
    have := (Matrix.mulVecLin B).toContinuousLinearMap.map_tsum hs1
    simpa using this
  rw [hMv, hlin]
  simp only [fwdSolA]
  rw [(hsum t ω h0).tsum_eq_zero_add]
  have e1 : (fun k => (B ^ (k + 1)).mulVec (iterA E (k + 1) b t ω)) =
      fun k => B.mulVec ((B ^ k).mulVec (iterA E (k + 1) b t ω)) := funext fun k => by
    rw [Matrix.mulVec_mulVec, ← pow_succ']
  rw [e1]
  simp only [pow_zero, Matrix.one_mulVec, iterA, Function.iterate_zero, id]
  abel

/-! ## The inverse of the linearised operator, almost surely -/

/-- The NKPC forcing built from `r` (a.s. version of `NonlinearNKMarkovGeneral.s1F`). -/
noncomputable def s1A (p : Par) (r : ℕ → Ω → Fin 4 → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (r t ω 2 - r t ω 1 + p.k3 * r t ω 3 -
    p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω) / p.cR

/-- The forcing of the IS–AS block. -/
noncomputable def bA (p : Par) (r : ℕ → Ω → Fin 4 → ℝ) : ℕ → Ω → Fin 2 → ℝ :=
  fun t ω => ![(r t ω 0 - p.φ * s1A E p r t ω) / p.dd,
    (p.κ * r t ω 0 + (p.σ + p.φy) * s1A E p r t ω) / p.dd]

/-- The IS–AS block solved forward. -/
noncomputable def uA (p : Par) (r : ℕ → Ω → Fin 4 → ℝ) : ℕ → Ω → Fin 2 → ℝ :=
  fwdSolA E (Amat p) (bA E p r)

/-- The forcing of the `F` recursion. -/
noncomputable def gA (p : Par) (r : ℕ → Ω → Fin 4 → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => r t ω 1 + (1 - p.α * p.β) * (1 - p.σ) * uA E p r t ω 0 +
    p.α * p.β * (p.θ - 1) * Ms E (fun s ω => uA E p r s ω 1) t ω

/-- `F̂` solved forward. -/
noncomputable def FA (p : Par) (r : ℕ → Ω → Fin 4 → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => fwdSolA E !![p.α * p.β] (fun t ω => ![gA E p r t ω]) t ω 0

/-- Woodford (2003), App. A.3, (A.13) a.s.: the inverse of the linearised operator. -/
noncomputable def linSolA (p : Par) (r : ℕ → Ω → Fin 4 → ℝ) : ℕ → Ω → Fin 4 → ℝ :=
  fun t ω => ![uA E p r t ω 0, uA E p r t ω 1, FA E p r t ω,
    FA E p r t ω + p.cR * uA E p r t ω 1 - p.k3 * r t ω 3]

/-- Woodford (2003), App. A.3, (A.12)–(A.13) a.s. (**the linearised operator is onto the
a.s. measurable, essentially bounded processes**): `linSolA r` is a.s. measurable, essentially
bounded, and `L(linSolA r) = r` a.s. -/
theorem linSolA_spec {p : Par} (hp : p.Std) {r : ℕ → Ω → Fin 4 → ℝ} (hrG : Gd E r) {a : ℝ}
    (ha0 : 0 ≤ a) (hr : Bd E r a) :
    Gd E (linSolA E p r) ∧ (∃ C, 0 ≤ C ∧ Bd E (linSolA E p r) C) ∧
      ∀ t, LopA E p (linSolA E p r) t =ᵐ[E.μ] r t := by
  have hrc : ∀ i t, ∀ᵐ ω ∂E.μ, |r t ω i| ≤ a := fun i t => bd_comp E (hr t) i
  have hd := hp.dd_pos
  have hcR := hp.cR_pos
  have hk3 := hp.k3_pos
  have hab0 := hp.ab_pos
  have hab1 := hp.ab_lt_one
  have hθ1 : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have hm3 : ∀ t, ∀ᵐ ω ∂E.μ, |Ms E (fun s ω => r s ω 3) t ω| ≤ a := fun t =>
    E.abs_E_le (hrc 3 (t + 1)) t
  -- `s₁`
  have hs1G : Gd E (s1A E p r) := fun t => by
    unfold s1A
    exact aesm_div E ((((aesm_comp E (hrG t) 2).sub (aesm_comp E (hrG t) 1)).add
      ((aesm_comp E (hrG t) 3).const_mul p.k3)).sub ((aesm_E E t _).const_mul
        (p.α * p.β * p.k3))) p.cR
  set S1 := (2 + p.k3 + p.α * p.β * p.k3) / p.cR * a with hS1
  have hS10 : 0 ≤ S1 := by positivity
  have hs1 : ∀ t, ∀ᵐ ω ∂E.μ, |s1A E p r t ω| ≤ S1 := by
    intro t
    filter_upwards [hrc 1 t, hrc 2 t, hrc 3 t, hm3 t] with ω h1 h2 h3 h4
    simp only [s1A, hS1]
    rw [abs_div, abs_of_pos hcR, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcR]
    calc |r t ω 2 - r t ω 1 + p.k3 * r t ω 3 - p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω|
        ≤ |r t ω 2| + |r t ω 1| + p.k3 * |r t ω 3| +
            p.α * p.β * p.k3 * |Ms E (fun s ω => r s ω 3) t ω| := by
          have e1 := abs_sub (r t ω 2 - r t ω 1 + p.k3 * r t ω 3)
            (p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω)
          have e2 := abs_add_le (r t ω 2 - r t ω 1) (p.k3 * r t ω 3)
          have e3 := abs_sub (r t ω 2) (r t ω 1)
          rw [abs_mul (p.α * p.β * p.k3), abs_of_pos (by positivity : 0 < p.α * p.β * p.k3),
            abs_mul, abs_of_pos hk3] at *
          linarith
      _ ≤ a + a + p.k3 * a + p.α * p.β * p.k3 * a := by gcongr
      _ = (2 + p.k3 + p.α * p.β * p.k3) * a := by ring
  -- `b`
  set Bb := (a + p.φ * S1 + p.κ * a + (p.σ + p.φy) * S1) / p.dd with hBb
  have hBb0 : 0 ≤ Bb := by
    have := hp.φ_nonneg; have := hp.κ_pos; have := hp.σ_pos; have := hp.φy_nonneg
    positivity
  have hbG : Gd E (bA E p r) := fun t => aesm_vec E fun i => by
    fin_cases i
    · simp only [bA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact aesm_div E ((aesm_comp E (hrG t) 0).sub ((hs1G t).const_mul p.φ)) p.dd
    · simp only [bA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact aesm_div E (((aesm_comp E (hrG t) 0).const_mul p.κ).add
        ((hs1G t).const_mul (p.σ + p.φy))) p.dd
  have hbb : Bd E (bA E p r) Bb := fun t => by
    filter_upwards [hrc 0 t, hs1 t] with ω h0 hs
    have hφ := hp.φ_nonneg
    have hκ := hp.κ_pos
    have hσφ : 0 ≤ p.σ + p.φy := by linarith [hp.σ_pos, hp.φy_nonneg]
    refine (pi_norm_le_iff_of_nonneg hBb0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    fin_cases i
    · simp only [bA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hd, hBb]
      refine div_le_div_of_nonneg_right ?_ hd.le
      have := abs_sub (r t ω 0) (p.φ * s1A E p r t ω)
      rw [abs_mul, abs_of_nonneg hφ] at this
      have := mul_le_mul_of_nonneg_left hs hφ
      nlinarith [mul_nonneg hκ.le ha0, mul_nonneg hσφ hS10]
    · simp only [bA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hd, hBb]
      refine div_le_div_of_nonneg_right ?_ hd.le
      have := abs_add_le (p.κ * r t ω 0) ((p.σ + p.φy) * s1A E p r t ω)
      rw [abs_mul, abs_of_pos hκ, abs_mul, abs_of_nonneg hσφ] at this
      have := mul_le_mul_of_nonneg_left hs hσφ
      have := mul_le_mul_of_nonneg_left h0 hκ.le
      nlinarith [mul_nonneg hφ hS10]
  -- `u`
  obtain ⟨huG, huB, hueq⟩ := fwdSolA_spec E (summable_mnorm_Amat hp) hbG hBb0 hbb
  set U := (∑' k, mnorm (Amat p ^ k)) * Bb with hU
  have hU0 : 0 ≤ U := mul_nonneg (tsum_nonneg fun _ => mnorm_nonneg _) hBb0
  have huc : ∀ i t, ∀ᵐ ω ∂E.μ, |uA E p r t ω i| ≤ U := fun i t => bd_comp E (huB t) i
  have hmu : ∀ i t, ∀ᵐ ω ∂E.μ, |Ms E (fun s ω => uA E p r s ω i) t ω| ≤ U := fun i t =>
    E.abs_E_le (huc i (t + 1)) t
  -- `g` and `F`
  set G := a + (1 - p.α * p.β) * |1 - p.σ| * U + p.α * p.β * (p.θ - 1) * U with hG
  have hG0 : 0 ≤ G := by
    have : 0 < 1 - p.α * p.β := by linarith
    positivity
  have hgG : Gd E (fun t ω => ![gA E p r t ω]) := fun t => aesm_vec E fun i => by
    fin_cases i
    simp only [gA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
    exact ((aesm_comp E (hrG t) 1).add ((aesm_comp E (huG t) 0).const_mul _)).add
      ((aesm_E E t _).const_mul _)
  have hgb : Bd E (fun t ω => ![gA E p r t ω]) G := fun t => by
    filter_upwards [hrc 1 t, huc 0 t, hmu 1 t] with ω hR hY hP
    refine (pi_norm_le_iff_of_nonneg hG0).2 fun i => ?_
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, Real.norm_eq_abs, gA]
    have e1 := abs_add_le (r t ω 1 + (1 - p.α * p.β) * (1 - p.σ) * uA E p r t ω 0)
      (p.α * p.β * (p.θ - 1) * Ms E (fun s ω => uA E p r s ω 1) t ω)
    have e2 := abs_add_le (r t ω 1) ((1 - p.α * p.β) * (1 - p.σ) * uA E p r t ω 0)
    have t1 : |(1 - p.α * p.β) * (1 - p.σ) * uA E p r t ω 0| ≤
        (1 - p.α * p.β) * |1 - p.σ| * U := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 - p.α * p.β)]
      exact mul_le_mul_of_nonneg_left hY (mul_nonneg
        (by linarith : (0 : ℝ) ≤ 1 - p.α * p.β) (abs_nonneg (1 - p.σ)))
    have t2 : |p.α * p.β * (p.θ - 1) * Ms E (fun s ω => uA E p r s ω 1) t ω| ≤
        p.α * p.β * (p.θ - 1) * U := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < p.α * p.β * (p.θ - 1))]
      exact mul_le_mul_of_nonneg_left hP (by positivity)
    linarith
  have habs : mnorm !![p.α * p.β] < 1 := by
    rw [mnorm_ab, abs_of_pos hab0]; exact hab1
  obtain ⟨hFG, hFB, hFeq⟩ := fwdSolA_spec E (summable_mnorm_pow_of_lt habs) hgG hG0 hgb
  set W := (∑' k, mnorm (!![p.α * p.β] ^ k)) * G with hW
  have hW0 : 0 ≤ W := mul_nonneg (tsum_nonneg fun _ => mnorm_nonneg _) hG0
  have hFc : ∀ t, ∀ᵐ ω ∂E.μ, |FA E p r t ω| ≤ W := fun t => bd_comp E (hFB t) 0
  have hFAG : Gd E (fun t ω => FA E p r t ω) := fun t => aesm_comp E (hFG t) 0
  -- measurability and bounds of `linSolA r`
  have hLG : Gd E (linSolA E p r) := fun t => aesm_vec E fun i => by
    fin_cases i
    · exact aesm_comp E (huG t) 0
    · exact aesm_comp E (huG t) 1
    · exact hFAG t
    · simp only [linSolA, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      exact ((hFAG t).add ((aesm_comp E (huG t) 1).const_mul _)).sub
        ((aesm_comp E (hrG t) 3).const_mul _)
  set Cl := U + W + (W + p.cR * U + p.k3 * a) with hCl
  have hCl0 : 0 ≤ Cl := by positivity
  have hLB : Bd E (linSolA E p r) Cl := fun t => by
    filter_upwards [huc 0 t, huc 1 t, hFc t, hrc 3 t] with ω h0 h1 hF h3
    refine (pi_norm_le_iff_of_nonneg hCl0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have hK : |FA E p r t ω + p.cR * uA E p r t ω 1 - p.k3 * r t ω 3| ≤
        W + p.cR * U + p.k3 * a := by
      have e1 := abs_sub (FA E p r t ω + p.cR * uA E p r t ω 1) (p.k3 * r t ω 3)
      have e2 := abs_add_le (FA E p r t ω) (p.cR * uA E p r t ω 1)
      rw [abs_mul, abs_of_pos hcR] at e2
      rw [abs_mul p.k3, abs_of_pos hk3] at e1
      have := mul_le_mul_of_nonneg_left h1 hcR.le
      have := mul_le_mul_of_nonneg_left h3 hk3.le
      linarith
    fin_cases i
    · simp only [linSolA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [mul_nonneg hcR.le hU0, mul_nonneg hk3.le ha0]
    · simp only [linSolA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [mul_nonneg hcR.le hU0, mul_nonneg hk3.le ha0]
    · simp only [linSolA, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      linarith [mul_nonneg hcR.le hU0, mul_nonneg hk3.le ha0]
    · simp only [linSolA, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      linarith
  refine ⟨hLG, ⟨Cl, hCl0, hLB⟩, fun t => ?_⟩
  -- the equations
  set v := linSolA E p r with hv
  have hMv0 : ∀ ω, Ms E (fun s ω => v s ω 0) t ω = Ms E (fun s ω => uA E p r s ω 0) t ω :=
    fun ω => rfl
  have hMv1 : ∀ ω, Ms E (fun s ω => v s ω 1) t ω = Ms E (fun s ω => uA E p r s ω 1) t ω :=
    fun ω => rfl
  have hMv2 : ∀ ω, Ms E (fun s ω => v s ω 2) t ω = Ms E (fun s ω => FA E p r s ω) t ω :=
    fun ω => rfl
  have hint : ∀ f : ℕ → Ω → ℝ, Gd E f → ∀ C, (∀ t, ∀ᵐ ω ∂E.μ, |f t ω| ≤ C) →
      Integrable (f (t + 1)) E.μ := fun f hf C hC => integrable_of E (hf (t + 1)) (hC (t + 1))
  have hMK : ∀ᵐ ω ∂E.μ, Ms E (fun s ω => v s ω 3) t ω = Ms E (fun s ω => FA E p r s ω) t ω +
      p.cR * Ms E (fun s ω => uA E p r s ω 1) t ω - p.k3 * Ms E (fun s ω => r s ω 3) t ω := by
    have i1 := hint _ hFAG W hFc
    have i2 := hint _ (fun t => aesm_comp E (huG t) 1) U (huc 1)
    have i3 := hint _ (fun t => aesm_comp E (hrG t) 3) a (hrc 3)
    have e1 := E_lin2 E i1 i2 1 p.cR t
    have e2 := E_lin2 E ((i1.const_mul 1).add (i2.const_mul p.cR)) i3 1 (-p.k3) t
    have ef : (fun ω => v (t + 1) ω 3) = fun ω => 1 * (1 * FA E p r (t + 1) ω +
        p.cR * uA E p r (t + 1) ω 1) + -p.k3 * r (t + 1) ω 3 := by
      funext ω; simp only [hv, linSolA, Matrix.cons_val]; ring
    filter_upwards [e1, e2] with ω h1 h2
    simp only [Ms]
    rw [ef]
    rw [show E.E t (fun ω => 1 * (1 * FA E p r (t + 1) ω + p.cR * uA E p r (t + 1) ω 1) +
      -p.k3 * r (t + 1) ω 3) ω = 1 * E.E t (fun ω => 1 * FA E p r (t + 1) ω +
        p.cR * uA E p r (t + 1) ω 1) ω + -p.k3 * E.E t (fun ω => r (t + 1) ω 3) ω from h2]
    have e3 : E.E t (fun ω => 1 * FA E p r (t + 1) ω + p.cR * uA E p r (t + 1) ω 1) ω =
        1 * E.E t (FA E p r (t + 1)) ω + p.cR * E.E t (fun ω => uA E p r (t + 1) ω 1) ω := h1
    rw [e3]; ring
  have hcomp := LopA_apply E (p := p) hLG hLB t
  filter_upwards [hcomp, hueq t, hFeq t, hMK] with ω hc hu hF hmk
  obtain ⟨c0, c1, c2, c3⟩ := hc
  rw [← show uA E p r = fwdSolA E (Amat p) (bA E p r) from rfl] at hu
  have hu0 := congrFun hu 0
  have hu1 := congrFun hu 1
  simp only [Amat, bA, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, MvA] at hu0 hu1
  have hF0 := congrFun hF 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.add_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, MvA] at hF0
  change FA E p r t ω = p.α * p.β * Ms E (fun s ω => FA E p r s ω) t ω + gA E p r t ω at hF0
  have hd' := hd.ne'
  have h0' : p.dd * uA E p r t ω 0 = p.σ * Ms E (fun s ω => uA E p r s ω 0) t ω +
      (1 - p.φ * p.β) * Ms E (fun s ω => uA E p r s ω 1) t ω + (r t ω 0 - p.φ * s1A E p r t ω) := by
    rw [hu0]; simp only [Ms]; field_simp
  have h1' : p.dd * uA E p r t ω 1 = p.κ * p.σ * Ms E (fun s ω => uA E p r s ω 0) t ω +
      (p.κ + p.β * (p.σ + p.φy)) * Ms E (fun s ω => uA E p r s ω 1) t ω +
      (p.κ * r t ω 0 + (p.σ + p.φy) * s1A E p r t ω) := by
    rw [hu1]; simp only [Ms]; field_simp
  have edd : p.dd = p.σ + p.φy + p.φ * p.κ := rfl
  have hnk : uA E p r t ω 1 - p.β * Ms E (fun s ω => uA E p r s ω 1) t ω -
      p.κ * uA E p r t ω 0 = s1A E p r t ω := by
    have : p.dd * (uA E p r t ω 1 - p.β * Ms E (fun s ω => uA E p r s ω 1) t ω -
        p.κ * uA E p r t ω 0) = p.dd * s1A E p r t ω := by
      linear_combination h1' - p.κ * h0' -
        (p.β * Ms E (fun s ω => uA E p r s ω 1) t ω + s1A E p r t ω) * edd
    exact mul_left_cancel₀ hd' this
  have hab := hp.ab_c
  have hk' : p.κ * p.cR = (1 - p.α * p.β) * (p.ω + p.σ) := by
    rw [hp.κ_eq]; field_simp
  have hcRc : (1 - p.α) * p.cR = p.α * p.c0 := by
    unfold Par.cR; have : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
    field_simp
  have hk3c : (1 - p.α) * (p.θ - 1) * p.k3 = p.c0 := by
    unfold Par.k3; have : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
    field_simp
  have hv0 : v t ω 0 = uA E p r t ω 0 := rfl
  have hv1 : v t ω 1 = uA E p r t ω 1 := rfl
  have hv2 : v t ω 2 = FA E p r t ω := rfl
  have hv3 : v t ω 3 = FA E p r t ω + p.cR * uA E p r t ω 1 - p.k3 * r t ω 3 := rfl
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [c0, hv0, hv1, hMv0, hMv1]
    rw [edd] at h0'
    linear_combination h0' + p.φ * hnk
  · simp only [Fin.mk_one, Fin.isValue]
    rw [c1, hv2, hv0, hMv1, hMv2, hF0]
    simp only [gA]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [c2, hv3, hv0, hmk, hMv1, hF0]
    have hs1' : p.cR * s1A E p r t ω = r t ω 2 - r t ω 1 + p.k3 * r t ω 3 -
        p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω := by
      unfold s1A; field_simp
    simp only [gA]
    unfold Par.c0 at hab
    linear_combination p.cR * hnk + hs1' + uA E p r t ω 0 * hk' -
      Ms E (fun s ω => uA E p r s ω 1) t ω * hab
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [c3, hv1, hv2, hv3]
    have hc0 := hp.c0_pos.ne'
    have e : (1 - p.α) * (p.θ - 1) * (FA E p r t ω + p.cR * uA E p r t ω 1 - p.k3 * r t ω 3 -
        FA E p r t ω) / p.c0 = p.α * (p.θ - 1) * uA E p r t ω 1 - r t ω 3 := by
      rw [div_eq_iff hc0]
      linear_combination (p.θ - 1) * uA E p r t ω 1 * hcRc - r t ω 3 * hk3c
    rw [e]; ring

/-! ## Linearity, bounds and the inverse, almost surely -/

/-- `DN` of a process is good. -/
theorem gd_DN0 {p : Par} {v : ℕ → Ω → Fin 4 → ℝ} (hv : Gd E v) :
    Gd E (fun s ω => DN0 p (v s ω)) := fun t => by
  have hc : Continuous (DN0 p) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [DN0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val] <;> fun_prop
  exact hc.comp_aestronglyMeasurable (hv t)

/-- `‖DQ w‖ ≤ ‖DQ(0)‖‖w‖`. -/
theorem norm_DQ0_le {p : Par} (w : Fin 4 → ℝ) : ‖DQ0 p w‖ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * ‖w‖ := by
  rw [← fderiv_Qmap_inr, ← norm_pair_zero w]; exact ContinuousLinearMap.le_opNorm _ _

/-- `‖DN w‖ ≤ ‖DN(0)‖‖w‖`. -/
theorem norm_DN0_le {p : Par} (w : Fin 4 → ℝ) : ‖DN0 p w‖ ≤ ‖fderiv ℝ (Nmap p) (0, 0)‖ * ‖w‖ := by
  rw [← fderiv_Nmap_inr, ← norm_pair_zero w]; exact ContinuousLinearMap.le_opNorm _ _

/-- `DN` of a bounded process is bounded. -/
theorem bd_DN0 {p : Par} {v : ℕ → Ω → Fin 4 → ℝ} {V : ℝ} (hv : Bd E v V) :
    Bd E (fun s ω => DN0 p (v s ω)) (‖fderiv ℝ (Nmap p) (0, 0)‖ * V) := fun t => by
  filter_upwards [hv t] with ω hω
  exact (norm_DN0_le _).trans (mul_le_mul_of_nonneg_left hω (norm_nonneg _))

/-- Woodford (2003), App. A.3 a.s.: the linearised operator maps bounded processes to bounded
processes. -/
theorem bd_LopA {p : Par} {v : ℕ → Ω → Fin 4 → ℝ} {V : ℝ} (hV : 0 ≤ V) (hv : Bd E v V) :
    Bd E (LopA E p v) ((‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖) * V) :=
  fun t => by
    filter_upwards [hv t, MvA_bd E (mul_nonneg (norm_nonneg _) hV) (bd_DN0 E hv) t] with ω h1 h2
    calc ‖LopA E p v t ω‖ ≤ ‖DQ0 p (v t ω)‖ + ‖MvA E (fun s ω' => DN0 p (v s ω')) t ω‖ :=
          norm_add_le _ _
      _ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * V + ‖fderiv ℝ (Nmap p) (0, 0)‖ * V :=
          add_le_add ((norm_DQ0_le _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))) h2
      _ = _ := by ring

/-- Woodford (2003), App. A.3 a.s.: the linearised operator is additive in differences. -/
theorem LopA_sub {p : Par} {v w : ℕ → Ω → Fin 4 → ℝ} (hv : Gd E v) (hw : Gd E w) {V W : ℝ}
    (hvb : Bd E v V) (hwb : Bd E w W) (t : ℕ) :
    LopA E p (fun s ω => v s ω - w s ω) t =ᵐ[E.μ] fun ω => LopA E p v t ω - LopA E p w t ω := by
  have h := MvA_sub E (gd_DN0 E (p := p) hv) (gd_DN0 E (p := p) hw) (bd_DN0 E hvb)
    (bd_DN0 E hwb) t
  filter_upwards [h] with ω hω
  simp only [LopA, DQ0_sub]
  have e : (fun s ω' => DN0 p (v s ω' - w s ω')) = fun s ω' => DN0 p (v s ω') - DN0 p (w s ω') :=
    by funext s ω'; rw [DN0_sub]
  rw [e, hω]; abel

/-- Woodford (2003), App. A.3 a.s.: the linearised operator respects a.s. equality. -/
theorem LopA_congr {p : Par} {v w : ℕ → Ω → Fin 4 → ℝ} (h : ∀ t, v t =ᵐ[E.μ] w t) (t : ℕ) :
    LopA E p v t =ᵐ[E.μ] LopA E p w t := by
  have h1 : ∀ t, (fun ω => DN0 p (v t ω)) =ᵐ[E.μ] fun ω => DN0 p (w t ω) := fun t => by
    filter_upwards [h t] with ω hω; rw [hω]
  filter_upwards [h t, MvA_congr E h1 t] with ω h2 h3
  simp only [LopA]; rw [h2, h3]

/-- Woodford (2003), App. A.3 a.s.: `‖linSolA r‖ ≤ K‖r‖` a.s. -/
theorem bd_linSolA {p : Par} (hp : p.Std) {r : ℕ → Ω → Fin 4 → ℝ} (hrG : Gd E r) {a : ℝ}
    (ha0 : 0 ≤ a) (hr : Bd E r a) : Bd E (linSolA E p r) (Kap p * a) := by
  obtain ⟨hG, ⟨C, hC0, hC⟩, hL⟩ := linSolA_spec E hp hrG ha0 hr
  refine apriori_ae E hp hG hC0 hC ha0 fun t => ?_
  filter_upwards [hL t, hr t] with ω h1 h2; rw [h1]; exact h2

/-- Woodford (2003), App. A.3 a.s.: `linSolA (Lv) = v` a.s. for good bounded `v`. -/
theorem linSolA_Lop {p : Par} (hp : p.Std) {v : ℕ → Ω → Fin 4 → ℝ} (hv : Gd E v) {V : ℝ}
    (hV : 0 ≤ V) (hvb : Bd E v V) : ∀ t, linSolA E p (LopA E p v) t =ᵐ[E.μ] v t := by
  have hLb := bd_LopA E (p := p) hV hvb
  obtain ⟨hG, ⟨C, hC0, hC⟩, hL⟩ := linSolA_spec E hp (gd_LopA E hv) (by positivity) hLb
  have hd : Bd E (fun s ω => linSolA E p (LopA E p v) s ω - v s ω) (Kap p * 0) := by
    refine apriori_ae E hp (v := fun s ω => linSolA E p (LopA E p v) s ω - v s ω)
      (fun t => (hG t).sub (hv t)) (add_nonneg hC0 hV)
      (fun t => by
        filter_upwards [hC t, hvb t] with ω h1 h2; exact (norm_sub_le _ _).trans (add_le_add h1 h2))
      le_rfl fun t => ?_
    filter_upwards [LopA_sub E (p := p) hG hv hC hvb t, hL t] with ω h1 h2
    rw [h1, h2]; simp
  intro t
  filter_upwards [hd t] with ω hω
  rw [mul_zero] at hω
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hω)

/-- Woodford (2003), App. A.3 a.s.: `linSolA` is additive in differences. -/
theorem linSolA_sub {p : Par} (hp : p.Std) {r r' : ℕ → Ω → Fin 4 → ℝ} (hrG : Gd E r)
    (hr'G : Gd E r') {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hr : Bd E r a) (hr' : Bd E r' a') :
    ∀ t, linSolA E p (fun s ω => r s ω - r' s ω) t =ᵐ[E.μ]
      fun ω => linSolA E p r t ω - linSolA E p r' t ω := by
  have hdG : Gd E (fun s ω => r s ω - r' s ω) := fun t => (hrG t).sub (hr'G t)
  have hdb : Bd E (fun s ω => r s ω - r' s ω) (a + a') := fun t => by
    filter_upwards [hr t, hr' t] with ω h1 h2; exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  obtain ⟨g1, ⟨C1, hC10, hC1⟩, hL1⟩ := linSolA_spec E hp hdG (add_nonneg ha ha') hdb
  obtain ⟨g2, ⟨C2, hC20, hC2⟩, hL2⟩ := linSolA_spec E hp hrG ha hr
  obtain ⟨g3, ⟨C3, hC30, hC3⟩, hL3⟩ := linSolA_spec E hp hr'G ha' hr'
  have g23 : Gd E (fun s ω => linSolA E p r s ω - linSolA E p r' s ω) := fun t =>
    (g2 t).sub (g3 t)
  have b23 : Bd E (fun s ω => linSolA E p r s ω - linSolA E p r' s ω) (C2 + C3) := fun t => by
    filter_upwards [hC2 t, hC3 t] with ω h1 h2; exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hd : Bd E (fun s ω => linSolA E p (fun s ω => r s ω - r' s ω) s ω -
      (linSolA E p r s ω - linSolA E p r' s ω)) (Kap p * 0) := by
    refine apriori_ae E hp (v := fun s ω => linSolA E p (fun s ω => r s ω - r' s ω) s ω -
      (linSolA E p r s ω - linSolA E p r' s ω)) (fun t => (g1 t).sub (g23 t))
      (add_nonneg hC10 (add_nonneg hC20 hC30))
      (fun t => by
        filter_upwards [hC1 t, b23 t] with ω h1 h2
        exact (norm_sub_le _ _).trans (add_le_add h1 h2)) le_rfl fun t => ?_
    filter_upwards [LopA_sub E (p := p) g1 g23 hC1 b23 t, hL1 t,
      LopA_sub E (p := p) g2 g3 hC2 hC3 t, hL2 t, hL3 t]
      with ω h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]; simp
  intro t
  filter_upwards [hd t] with ω hω
  rw [mul_zero] at hω
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hω)

/-! ## Existence: the Newton contraction, almost surely -/

/-- Woodford (2003), (A.11) a.s.: the residual of the exact stochastic conditions,
`Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t]`. -/
noncomputable def PhiA (p : Par) (e : ℕ → Ω → Fin 5 → ℝ) (z : ℕ → Ω → Fin 4 → ℝ) :
    ℕ → Ω → Fin 4 → ℝ :=
  fun t ω => Qmap p (e t ω, z t ω) + MvA E (fun s ω' => Nmap p (e s ω', z s ω')) t ω

/-- `LopA 0 = 0`. -/
theorem LopA_zero (p : Par) : LopA E p (fun _ _ => (0 : Fin 4 → ℝ)) = fun _ _ => 0 := by
  have h0 : DN0 p 0 = 0 := by funext i; fin_cases i <;> simp [DN0]
  have h1 : DQ0 p 0 = 0 := by funext i; fin_cases i <;> simp [DQ0]
  funext t ω
  simp only [LopA, h0, h1, MvA_const, zero_add]

/-- Woodford (2003), App. A.3 a.s. (**the residual minus its linearisation is small**). -/
theorem resid_ae {p : Par} {η ρQ ρN : ℝ} (hη0 : 0 ≤ η)
    (hQ : ∀ e w w', ‖e‖ ≤ ρQ → ‖w‖ ≤ ρQ → ‖w'‖ ≤ ρQ →
      ‖Qmap p (e, w) - Qmap p (e, w') - fderiv ℝ (Qmap p) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    (hN : ∀ e w w', ‖e‖ ≤ ρN → ‖w‖ ≤ ρN → ‖w'‖ ≤ ρN →
      ‖Nmap p (e, w) - Nmap p (e, w') - fderiv ℝ (Nmap p) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    {CN : ℝ} (hCN : ∀ q ∈ Metric.closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ)) (min ρQ ρN),
      ‖Nmap p q‖ ≤ CN)
    {e : ℕ → Ω → Fin 5 → ℝ} {z z' : ℕ → Ω → Fin 4 → ℝ} (he : Gd E e) (hz : Gd E z)
    (hz' : Gd E z') (heb : Bd E e (min ρQ ρN)) (hzb : Bd E z (min ρQ ρN))
    (hz'b : Bd E z' (min ρQ ρN)) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : Bd E (fun s ω => z s ω - z' s ω) D) :
    Bd E (fun s ω => PhiA E p e z s ω - PhiA E p e z' s ω -
      LopA E p (fun s ω => z s ω - z' s ω) s ω) (2 * η * D) := by
  set ρ := min ρQ ρN
  have hNb : ∀ w : ℕ → Ω → Fin 4 → ℝ, Bd E w ρ →
      Bd E (fun s ω => Nmap p (e s ω, w s ω)) CN := fun w hw t => by
    filter_upwards [heb t, hw t] with ω h1 h2
    exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]; exact max_le h1 h2)
  have hNg : ∀ w : ℕ → Ω → Fin 4 → ℝ, Gd E w → Gd E (fun s ω => Nmap p (e s ω, w s ω)) :=
    fun w hw => gd_pair E (contDiff_Nmap (p := p) (n := 0)).continuous he hw
  set d : ℕ → Ω → Fin 4 → ℝ := fun s ω => z s ω - z' s ω with hd
  have hdG : Gd E d := fun t => (hz t).sub (hz' t)
  have hRN : Bd E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω) -
      DN0 p (d s ω)) (η * D) := fun t => by
    filter_upwards [heb t, hzb t, hz'b t, hD t] with ω h1 h2 h3 h4
    have := hN (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_right _ _))
      (h2.trans (min_le_right _ _)) (h3.trans (min_le_right _ _))
    rw [fderiv_Nmap_inr] at this
    exact this.trans (mul_le_mul_of_nonneg_left h4 hη0)
  have hNdg : Gd E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω)) := fun t =>
    ((hNg z hz) t).sub ((hNg z' hz') t)
  have hNdb : Bd E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω)) (CN + CN) :=
    fun t => by
      filter_upwards [hNb z hzb t, hNb z' hz'b t] with ω h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  intro t
  have s1 := MvA_sub E (hNg z hz) (hNg z' hz') (hNb z hzb) (hNb z' hz'b) t
  have s2 := MvA_sub E hNdg (gd_DN0 E (p := p) hdG) hNdb (bd_DN0 E (p := p) hD) t
  have hRb := MvA_bd E (mul_nonneg hη0 hD0) hRN t
  filter_upwards [s1, s2, hRb, heb t, hzb t, hz'b t, hD t] with ω m1 m2 hR h1 h2 h3 h4
  have hQx := hQ (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_left _ _))
    (h2.trans (min_le_left _ _)) (h3.trans (min_le_left _ _))
  rw [fderiv_Qmap_inr] at hQx
  have key : PhiA E p e z t ω - PhiA E p e z' t ω - LopA E p d t ω =
      (Qmap p (e t ω, z t ω) - Qmap p (e t ω, z' t ω) - DQ0 p (z t ω - z' t ω)) +
      MvA E (fun s ω => Nmap p (e s ω, z s ω) - Nmap p (e s ω, z' s ω) - DN0 p (d s ω)) t ω := by
    rw [m2, m1]
    simp only [PhiA, LopA, hd]
    abel
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ η * D + η * D := add_le_add (hQx.trans (mul_le_mul_of_nonneg_left h4 hη0)) hR
    _ = 2 * η * D := by ring

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**EXISTENCE AND UNIQUENESS ON A GENERAL
PROBABILITY SPACE**): under the Taylor principle there are `r, δ > 0` such that on every filtered
probability space, for every a.s. measurable disturbance process with `‖e_t‖ ≤ δ` a.s., there is
an a.s. measurable process `z` with `‖z_t‖ ≤ r` a.s. solving the exact stochastic conditions with
Mathlib's conditional expectations a.s. at every date, and every other such solution within `r`
is a.s. equal to it at every date. -/
theorem seq_existence_ae {p : Par} (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 5 → ℝ), Gd E e → Bd E e δ →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, (Gd E z ∧ Bd E z r ∧ SeqEqmAE E p e z) ∧
          ∀ z' : ℕ → Ω → Fin 4 → ℝ, Gd E z' → Bd E z' r → SeqEqmAE E p e z' →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨ρu, hρu, huniq⟩ := seq_uniqueness_ae hp
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_small (contDiff_Qmap (p := p) (n := 1)) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_small (contDiff_Nmap (p := p) (n := 1)) hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Qmap (p := p) (n := 0)).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr00.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr00.le))
  set r := min r0 ρu with hr
  have hr0' : 0 < r := lt_min hr00 hρu
  have hrr0 : r ≤ r0 := min_le_left _ _
  set τ := r / (4 * Kap p) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin 5 → ℝ => Qmap p (e, 0)) 0 :=
    ((contDiff_Qmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  have hcN : ContinuousAt (fun e : Fin 5 → ℝ => Nmap p (e, 0)) 0 :=
    ((contDiff_Nmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  set δ := min r (min (δQ / 2) (δN / 2)) with hδ
  have hδ0 : 0 < δ := lt_min hr0' (lt_min (by positivity) (by positivity))
  refine ⟨r, hr0', δ, hδ0, fun Ω _ E e he heb => ?_⟩
  have heb0 : Bd E e r0 := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans ((min_le_left _ _).trans hrr0)
  -- `Φ` is good and bounded on the ball
  have hPhiG : ∀ z, Gd E z → Gd E (PhiA E p e z) := fun z hz =>
    gd_add E (gd_pair E (contDiff_Qmap (p := p) (n := 0)).continuous he hz) (MvA_gd E _)
  have hPhiB : ∀ z, Bd E z r → Bd E (PhiA E p e z) (CQ + CN) := fun z hz t => by
    have hNb : Bd E (fun s ω => Nmap p (e s ω, z s ω)) CN := fun t => by
      filter_upwards [heb0 t, hz t] with ω h1 h2
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                      exact max_le h1 (h2.trans hrr0))
    filter_upwards [heb0 t, hz t, MvA_bd E hCN0 hNb t] with ω h1 h2 h3
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le h1 (h2.trans hrr0))) h3)
  -- the Newton map
  set T : (ℕ → Ω → Fin 4 → ℝ) → (ℕ → Ω → Fin 4 → ℝ) :=
    fun z t ω => z t ω - linSolA E p (PhiA E p e z) t ω with hT
  have hTG : ∀ z, Gd E z → Bd E z r → Gd E (T z) := fun z hz hzb t =>
    (hz t).sub ((linSolA_spec E hp (hPhiG z hz) (add_nonneg hCQ0 hCN0) (hPhiB z hzb)).1 t)
  have hcontr : ∀ z z', Gd E z → Gd E z' → Bd E z r → Bd E z' r → ∀ D, 0 ≤ D →
      Bd E (fun s ω => z s ω - z' s ω) D → Bd E (fun s ω => T z s ω - T z' s ω) (D / 2) := by
    intro z z' hz hz' hzb hz'b D hD0 hD
    have hzb0 : Bd E z r0 := fun t => by
      filter_upwards [hzb t] with ω hω; exact hω.trans hrr0
    have hz'b0 : Bd E z' r0 := fun t => by
      filter_upwards [hz'b t] with ω hω; exact hω.trans hrr0
    have hR := resid_ae E (p := p) hη0.le hQ hN hCN he hz hz' heb0 hzb0 hz'b0 hD0 hD
    have hdG : Gd E (fun s ω => z s ω - z' s ω) := fun t => (hz t).sub (hz' t)
    have hLd := bd_LopA E (p := p) hD0 hD
    have hPd : Bd E (fun s ω => PhiA E p e z s ω - PhiA E p e z' s ω) (CQ + CN + (CQ + CN)) :=
      fun t => by
        filter_upwards [hPhiB z hzb t, hPhiB z' hz'b t] with ω h1 h2
        exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hPdG : Gd E (fun s ω => PhiA E p e z s ω - PhiA E p e z' s ω) := fun t =>
      ((hPhiG z hz) t).sub ((hPhiG z' hz') t)
    have e1 := linSolA_sub E hp (hPhiG z hz) (hPhiG z' hz') (add_nonneg hCQ0 hCN0)
      (add_nonneg hCQ0 hCN0) (hPhiB z hzb) (hPhiB z' hz'b)
    have e2 := linSolA_sub E hp hPdG (gd_LopA E hdG) (by positivity)
      (mul_nonneg (by positivity) hD0) hPd hLd
    have e3 := linSolA_Lop E hp hdG hD0 hD
    have hRG : Gd E (fun s ω => PhiA E p e z s ω - PhiA E p e z' s ω -
        LopA E p (fun s ω => z s ω - z' s ω) s ω) := fun t => (hPdG t).sub (gd_LopA E hdG t)
    have hb := bd_linSolA E hp hRG (by positivity) hR
    intro t
    filter_upwards [e1 t, e2 t, e3 t, hb t] with ω h1 h2 h3 h4
    have key : T z t ω - T z' t ω = -linSolA E p (fun s ω => PhiA E p e z s ω -
        PhiA E p e z' s ω - LopA E p (fun s ω => z s ω - z' s ω) s ω) t ω := by
      rw [h2]
      simp only [hT]
      rw [h1, h3]
      abel
    rw [key, norm_neg]
    calc _ ≤ _ := h4
      _ = D / 2 := by rw [hη]; field_simp; ring
  -- `T 0` is small
  have hT0 : Bd E (T fun _ _ => 0) (r / 2) := by
    have hb : Bd E (PhiA E p e fun _ _ => 0) (2 * τ) := fun t => by
      have hs : Qmap p (0, 0) + Nmap p (0, 0) = 0 := by
        funext i; fin_cases i <;> simp [Qmap, Nmap]
      have hNg : Gd E (fun s ω => Nmap p (e s ω, (0 : Fin 4 → ℝ))) :=
        gd_pair E (contDiff_Nmap (p := p) (n := 0)).continuous he
        (fun _ => aestronglyMeasurable_const)
      have hNb : Bd E (fun s ω => Nmap p (e s ω, (0 : Fin 4 → ℝ))) CN := fun t => by
        filter_upwards [heb0 t] with ω h1
        exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                        exact max_le h1 (by simp [hr00.le]))
      have m := MvA_sub E hNg (fun _ => aestronglyMeasurable_const) hNb
        (C := CN) (D := ‖Nmap p (0, 0)‖) (h := fun s ω => Nmap p (e s ω, 0))
        (g := fun _ _ => Nmap p (0, 0)) (fun _ => Eventually.of_forall fun _ => le_rfl) t
      have hbN : Bd E (fun s ω => Nmap p (e s ω, (0 : Fin 4 → ℝ)) - Nmap p (0, 0)) τ :=
        fun t => by
          filter_upwards [heb t] with ω h1
          have h := hNc (x := e t ω) (by
            rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
              ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
          rw [dist_eq_norm] at h; exact h.le
      filter_upwards [heb t, m, MvA_bd E hτ0.le hbN t] with ω h1 hm h3
      have hq : ‖Qmap p (e t ω, 0) - Qmap p (0, 0)‖ ≤ τ := by
        have h := hQc (x := e t ω) (by
          rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have key : PhiA E p e (fun _ _ => 0) t ω = (Qmap p (e t ω, 0) - Qmap p (0, 0)) +
          MvA E (fun s ω => Nmap p (e s ω, 0) - Nmap p (0, 0)) t ω := by
        rw [hm, MvA_const]
        simp only [PhiA]
        linear_combination (norm := abel_nf) hs
      rw [key]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ τ + τ := add_le_add hq h3
        _ = 2 * τ := by ring
    have hl := bd_linSolA E hp (hPhiG _ fun _ => aestronglyMeasurable_const) (by positivity) hb
    intro t
    filter_upwards [hl t] with ω hω
    simp only [hT, zero_sub, norm_neg]
    calc _ ≤ Kap p * (2 * τ) := hω
      _ = r / 2 := by rw [hτ]; field_simp; ring
  have hballB : ∀ z, Gd E z → Bd E z r → Bd E (T z) r := by
    intro z hz hzb t
    have h1 := hcontr z (fun _ _ => 0) hz (fun _ => aestronglyMeasurable_const) hzb
      (fun t => Eventually.of_forall fun _ => by simp [hr0'.le]) r hr0'.le
      (fun t => by filter_upwards [hzb t] with ω hω; simpa using hω) t
    filter_upwards [h1, hT0 t] with ω e1 e2
    calc ‖T z t ω‖ ≤ ‖T z t ω - T (fun _ _ => 0) t ω‖ + ‖T (fun _ _ => 0) t ω‖ := by
          have := norm_add_le (T z t ω - T (fun _ _ => 0) t ω) (T (fun _ _ => 0) t ω)
          simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add e1 e2
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → ℕ → Ω → Fin 4 → ℝ := fun n => T^[n] fun _ _ => 0 with hzs
  have hzsI : ∀ n, Gd E (zs n) ∧ Bd E (zs n) r := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun _ => aestronglyMeasurable_const,
        fun t => Eventually.of_forall fun _ => by simp [hzs, hr0'.le]⟩
    | succ n ih =>
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]; exact ⟨hTG _ ih.1 ih.2, hballB _ ih.1 ih.2⟩
  have hstep : ∀ n, Bd E (fun s ω => zs n s ω - zs (n + 1) s ω) (r / 2 / 2 ^ n) := by
    intro n
    induction n with
    | zero =>
      intro t
      filter_upwards [hT0 t] with ω hω
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hω
    | succ n ih =>
      have e1 : zs (n + 1 + 1) = T (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      have h := hcontr (zs (n + 1)) (zs n) (hzsI _).1 (hzsI _).1 (hzsI _).2 (hzsI _).2
        (r / 2 / 2 ^ n) (by positivity) (fun t => by
          filter_upwards [ih t] with ω hω; rwa [norm_sub_rev])
      intro t
      filter_upwards [h t] with ω hω
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) t ω = T (zs n) t ω from by rw [e2]]
      calc _ ≤ r / 2 / 2 ^ n / 2 := hω
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hall : ∀ t, ∀ᵐ ω ∂E.μ, ∀ n, ‖zs n t ω - zs (n + 1) t ω‖ ≤ r / 2 / 2 ^ n := fun t =>
    ae_all_iff.2 fun n => hstep n t
  set z : ℕ → Ω → Fin 4 → ℝ := fun t ω => limUnder atTop fun n => zs n t ω with hz
  have hconv : ∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun n => zs n t ω) atTop (𝓝 (z t ω)) := fun t => by
    filter_upwards [hall t] with ω hω
    have hc : CauchySeq fun n => zs n t ω :=
      cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hω n
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨l, hl⟩
  have hzG : Gd E z := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hzsI n).1 t) (hconv t)
  have hzdist : ∀ n, Bd E (fun s ω => zs n s ω - z s ω) (r / 2 ^ n) := fun n t => by
    filter_upwards [hall t, hconv t] with ω hω hc
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n t ω)
      (fun n => by rw [dist_eq_norm]; exact hω n) hc n
    rwa [dist_eq_norm] at this
  have hzB : Bd E z r := fun t => by
    filter_upwards [hconv t, ae_all_iff.2 fun n => (hzsI n).2 t] with ω hc hb
    exact le_of_tendsto' hc.norm hb
  -- fixed point
  have hfix : ∀ t, T z t =ᵐ[E.μ] z t := by
    intro t
    have hTn : ∀ n, Bd E (fun s ω => T z s ω - T (zs n) s ω) (r / 2 ^ n / 2) := fun n =>
      hcontr z (zs n) hzG (hzsI n).1 hzB (hzsI n).2 (r / 2 ^ n) (by positivity) (fun t => by
        filter_upwards [hzdist n t] with ω hω; rwa [norm_sub_rev])
    filter_upwards [hconv t, ae_all_iff.2 fun n => hTn n t] with ω hc hT'
    have hlim : Tendsto (fun n => zs (n + 1) t ω) atTop (𝓝 (T z t ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => r / 2 ^ n / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hT' n
    exact tendsto_nhds_unique hlim (hc.comp (tendsto_add_atTop_nat 1))
  -- the fixed point solves the conditions
  have hl0 : ∀ t, linSolA E p (PhiA E p e z) t =ᵐ[E.μ] fun _ => 0 := fun t => by
    filter_upwards [hfix t] with ω hω
    have := congrArg (fun v => z t ω - v) hω
    simp only [hT, sub_sub_cancel, sub_self] at this
    exact this
  obtain ⟨-, -, hL⟩ := linSolA_spec E hp (hPhiG z hzG) (add_nonneg hCQ0 hCN0) (hPhiB z hzB)
  have hEq : SeqEqmAE E p e z := fun t => by
    have hc := LopA_congr E (p := p) hl0 t
    rw [LopA_zero] at hc
    filter_upwards [hL t, hc] with ω h1 h2
    change PhiA E p e z t ω = 0
    rw [← h1, h2]
  refine ⟨z, ⟨hzG, hzB, hEq⟩, fun z' hz'G hz'B hz' => ?_⟩
  have hb : Bd E e ρu := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans ((min_le_left _ _).trans (min_le_right _ _))
  exact huniq Ω E e z' z he hz'G hzG hb (fun t => by
      filter_upwards [hz'B t] with ω hω; exact hω.trans (min_le_right _ _))
    (fun t => by filter_upwards [hzB t] with ω hω; exact hω.trans (min_le_right _ _)) hz' hEq

/-! ## Instance: an AR(1) with a general bounded innovation law -/

open ExpectationsMeasureIID in
/-- Woodford (2003), Ch. 6, §1 and App. A.3 (**the exact NK model driven by an AR(1) with a
GENERAL bounded innovation law**): on the i.i.d. product space `ν^ℕ` of any innovation law `ν` with
bounded support `|ε| ≤ B` (not necessarily finitely supported), with the AR(1) state
`x_t = ρx_{t−1} + ε_t` (`|ρ| < 1`) and disturbances `e_t = x_t c`, if
`B‖c‖/(1 − |ρ|) ≤ δ` there is an a.s. measurable solution within `r` of the exact stochastic
conditions with Mathlib's conditional expectations, unique a.s. among such solutions. -/
theorem ar1_iid_equilibrium {p : Par} (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (ν : ProbabilityMeasure ℝ) (B ρ : ℝ), |ρ| < 1 →
      (∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) → ∀ c : Fin 5 → ℝ, B / (1 - |ρ|) * ‖c‖ ≤ δ →
        ∃ z : ℕ → (ℕ → ℝ) → Fin 4 → ℝ, (Gd (iidSystem ν) z ∧ Bd (iidSystem ν) z r ∧
          SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) z) ∧
          ∀ z' : ℕ → (ℕ → ℝ) → Fin 4 → ℝ, Gd (iidSystem ν) z' → Bd (iidSystem ν) z' r →
            SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) z' →
              ∀ t, z' t =ᵐ[(iidSystem ν).μ] z t := by
  obtain ⟨r, hr, δ, hδ, h⟩ := seq_existence_ae hp
  refine ⟨r, hr, δ, hδ, fun ν B ρ hρ hB c hc => h (ℕ → ℝ) (iidSystem ν) _ (fun t => ?_)
    (fun t => ?_)⟩
  · exact (((ar1_adapted ν ρ t).mono ((iidSystem ν).𝓕.le t)).aestronglyMeasurable).smul_const c
  · filter_upwards [ar1_bdd (ν := ν) hρ hB t] with ω hω
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hω (norm_nonneg c)).trans hc

end Woodford.StabilizationWelfare.NonlinearNKMarkovAE
