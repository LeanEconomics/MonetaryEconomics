/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureMarkov
import OptimalPolicyRules.ExpectationsMeasureIID
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Chapter 8 on a genuine infinite-horizon probability space: i.i.d. economies

Woodford (2003), *Interest and Prices*, Chapter 8: Assumption 8.1 (p. 541), Proposition 8.2
(p. 555) and the Definition of robust optimality (pp. 549–550), on the i.i.d. infinite-product
probability space `Ω = ℕ → ℝ`, `μ = ν^ℕ`, `𝓕_t = σ(ε_0, …, ε_t)`
(`ExpectationsMeasureIID.iidSystem`), which is not finitely supported (every history is null).

## Main results

* **Proposition 8.2's linear form on an i.i.d.-driven VAR.** `iidVAR A b` is the VAR(1)
  `s_0 = ε_0 b`, `s_{t+1} = A s_t + ε_{t+1} b`; with mean-zero bounded shocks and geometrically
  stable `A` it satisfies `IsVAR` (`iid_isVAR`), so `OptimalRulesMeasureMarkov` applies:
  `iid_prop82` (existence, a.s. uniqueness, timeless optimality and the linear form (1.5)).
* **The original-sense Assumption 8.1 and robust optimality, re-examined** (via the
  characterisations `OptimalRulesMeasure.assumption81_iff`, `assumption81M_iff`,
  `robustlyOptimal_iff`):
  * the fair-coin economy carries genuine news at every date (`coin_not_predInfo`), so **the
    book's Assumption 8.1 fails for every problem at every `t₀ ≥ 1`** (`coin_not_assumption81`),
    exactly as on the finite coin tree (`NKAssumption81.not_assumption81_coin`) — the
    counterexample persists on a genuine infinite sample space;
  * yet on the same economy every variable known at a date is a.s. bounded (`coin_bddInfo`), so
    the unbounded-initial-condition forms **become equivalent to the bounded ones a.s.**:
    `coin_assumption81M_iff`, `coin_robustlyOptimal_iff`, and at `t₀ = 0` the book's form is
    equivalent to the corrected one (`coin_assumption81_zero_iff`);
  * with Gaussian shocks date-`t` information carries unbounded variables
    (`gauss_not_bddInfo`), so the book's Assumption 8.1 fails at every `t₀` for every problem
    (`gauss_not_assumption81`), and with a predetermined variable the `M`-corrected form and
    robust optimality for all initial conditions fail too (`gauss_not_assumption81M`,
    `gauss_not_robustlyOptimal`) — the measure-theoretic form of
    `InertiaAssumption81.not_in_focSolvableM` and `not_robustlyOptimal`.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureIID

open MeasureTheory ProbabilityTheory Filter Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure ExpectationsMeasureIID OptimalRulesMeasure OptimalRulesMeasureMarkov

/-! ### A VAR(1) driven by i.i.d. shocks -/

variable {ιs : Type*} [Fintype ιs] [DecidableEq ιs]

/-- Woodford (2003), p. 537 (the exogenous state): the VAR(1) `s_0 = ε_0 b`,
`s_{t+1} = A s_t + ε_{t+1} b` driven by the i.i.d. shocks. -/
def iidVAR (A : Matrix ιs ιs ℝ) (b : ιs → ℝ) : ℕ → (ℕ → ℝ) → ιs → ℝ
  | 0 => fun ω => shock 0 ω • b
  | t + 1 => fun ω => A *ᵥ iidVAR A b t ω + shock (t + 1) ω • b

omit [DecidableEq ιs] in
/-- Woodford (2003), p. 537: the i.i.d. VAR is adapted to `𝓕_t = σ(ε_0, …, ε_t)`. -/
theorem iidVAR_adapted (ν : ProbabilityMeasure ℝ) (A : Matrix ιs ιs ℝ) (b : ιs → ℝ) :
    MAdaptedV (iidSystem ν) (iidVAR A b) := by
  intro t
  induction t with
  | zero =>
    intro i
    exact ((measurable_shock ν le_rfl).mul_const (b i)).stronglyMeasurable
  | succ t ih =>
    intro i
    have h1 : StronglyMeasurable[(iidSystem ν).𝓕 (t + 1)]
        (fun ω => (A *ᵥ iidVAR A b t ω) i) :=
      (sm_comp ih (g := fun v => (A *ᵥ v) i) (by fun_prop)).mono
        ((iidSystem ν).𝓕.mono (Nat.le_succ t))
    have h2 : StronglyMeasurable[(iidSystem ν).𝓕 (t + 1)] (fun ω => shock (t + 1) ω * b i) :=
      ((measurable_shock ν le_rfl).mul_const (b i)).stronglyMeasurable
    exact h1.add h2

/-- Woodford (2003), p. 537: with shocks bounded by `B` and geometrically stable `A`, the i.i.d.
VAR is essentially bounded. -/
theorem iidVAR_bdd {ν : ProbabilityMeasure ℝ} {A : Matrix ιs ιs ℝ} (hA : PencilSplit.PowDecay A)
    (b : ιs → ℝ) {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    MBoundedV (iidSystem ν) (iidVAR A b) := by
  obtain ⟨K, hK⟩ := bounded_rec hA (|B| * ∑ j, |b j|) (|B| * ∑ j, |b j|)
  have hb : ∀ (e : ℝ) i, |e| ≤ B → |(e • b) i| ≤ |B| * ∑ j, |b j| := by
    intro e i he
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul (he.trans (le_abs_self B)) (Finset.single_le_sum
      (f := fun j => |b j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
      (abs_nonneg _)
  refine ⟨K, fun t => ?_⟩
  filter_upwards [ae_all_iff.2 (shock_ae_bdd ν hbdd)] with ω h i
  exact hK (fun k => iidVAR A b k ω) (fun k => shock (k + 1) ω • b)
    (fun i => hb _ i (h 0)) (fun k i => hb _ i (h (k + 1))) (fun _ => rfl) t i

/-- Woodford (2003), p. 537: the i.i.d. VAR has the time-invariant conditional law of motion
`E_t s_{t+1} = A s_t` a.s. (mean-zero shocks). -/
theorem iidVAR_E {ν : ProbabilityMeasure ℝ} {A : Matrix ιs ιs ℝ} (hA : PencilSplit.PowDecay A)
    (b : ιs → ℝ) {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, EVm (iidSystem ν) t (iidVAR A b (t + 1)) ω =
      A *ᵥ iidVAR A b t ω := by
  have hsi := integrable_of_adapted (iidVAR_bdd hA b hbdd) (iidVAR_adapted ν A b)
  have hAi : ∀ i, Integrable (fun ω => (A *ᵥ iidVAR A b t ω) i) (iidSystem ν).μ :=
    integrable_mulVec A (hsi t)
  have hεi : Integrable (shock (t + 1)) (iidSystem ν).μ :=
    integrable_of_bound (measurable_shock ν le_rfl |>.mono ((iidSystem ν).𝓕.le _) le_rfl
      |>.aestronglyMeasurable) (shock_ae_bdd ν hbdd (t + 1))
  have hAk : ∀ i, StronglyMeasurable[(iidSystem ν).𝓕 t] (fun ω => (A *ᵥ iidVAR A b t ω) i) :=
    fun i => sm_comp (iidVAR_adapted ν A b t) (g := fun v => (A *ᵥ v) i) (by fun_prop)
  have hc : ∀ i, (iidSystem ν).E t (fun ω => iidVAR A b (t + 1) ω i) =ᵐ[(iidSystem ν).μ]
      fun ω => (A *ᵥ iidVAR A b t ω) i := by
    intro i
    have hf : (fun ω => iidVAR A b (t + 1) ω i) =
        (fun ω => (A *ᵥ iidVAR A b t ω) i) + b i • shock (t + 1) := by
      funext ω
      simp only [iidVAR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hf]
    filter_upwards [(iidSystem ν).E_add (hAi i) (hεi.smul (b i)) t,
      (iidSystem ν).E_smul (b i) (shock (t + 1)) t, E_shock_zero hmean t] with ω e1 e2 e3
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, (iidSystem ν).E_of_stronglyMeasurable (hAk i)
      (hAi i)]
    simp
  filter_upwards [ae_all_iff.2 hc] with ω e
  funext i
  exact e i

/-- Woodford (2003), p. 537: **the i.i.d.-driven VAR(1) is a finite-dimensional exogenous Markov
state** in the sense of `OptimalRulesMeasureMarkov.IsVAR`. -/
theorem iid_isVAR {ν : ProbabilityMeasure ℝ} {A : Matrix ιs ιs ℝ} (hA : PencilSplit.PowDecay A)
    (b : ιs → ℝ) {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) : IsVAR (iidSystem ν) A (iidVAR A b) :=
  ⟨iidVAR_bdd hA b hbdd, iidVAR_adapted ν A b, iidVAR_E hA b hbdd hmean⟩

/-- Woodford (2003), p. 537: geometrically decaying powers are bounded. -/
theorem powBdd_of_powDecay {A : Matrix ιs ιs ℝ} (hA : PencilSplit.PowDecay A) :
    PowBdd A := by
  obtain ⟨C, r, hr0, hr1, hC⟩ := hA
  refine ⟨|C|, fun k i j => (hC k i j).trans ?_⟩
  calc C * r ^ k ≤ |C| * r ^ k := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hr0 k)
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) (abs_nonneg C)
    _ = |C| := mul_one _

/-- Woodford (2003), **Proposition 8.2 and Assumption 8.1 on the i.i.d. economy**, pp. 541 and
555: on `Ω = ℕ → ℝ` with i.i.d. mean-zero bounded shocks (not finitely supported) and the
exogenous VAR(1) `s_{t+1} = A s_t + ε_{t+1} b` (`A` geometrically stable), under the
perfect-foresight Assumption 8.1 and stability of `H_n`, for every `t₀`, every bounded `Z_{t₀}`
known at `t₀` and every bounded `M_{t₀−1}` known at `t₀ − 1`, (1.1) + (1.9) has a bounded
solution, unique a.s., optimal from a timeless perspective with `X̄_t = (Z_t, M_{t−1}, s_t)`,
and `z_t = f⁰ + F X̄_t` with the time-invariant `fY`, `FY`. -/
theorem iid_prop82 {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
    [DecidableEq ιz] (P : LQProblem ιZ ιz ιτ) {A : Matrix ιs ιs ℝ} (C2 : Matrix ιz ιs ℝ)
    (hA81 : Assumption81 P perfectForesight 0) (hAd : PencilSplit.PowDecay A)
    (hstab : PencilSplit.PowDecay (Hn P A C2 hA81 (powBdd_of_powDecay hAd))) (b : ιs → ℝ)
    {ν : ProbabilityMeasure ℝ} {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) {t0 : ℕ} {Z0 : (ℕ → ℝ) → ιZ → ℝ}
    {M0 : (ℕ → ℝ) → ιz → ℝ} (hZk : MKnownV (iidSystem ν) t0 Z0)
    (hZb : MBoundedRV (iidSystem ν) Z0) (hMb : MBoundedRV (iidSystem ν) M0)
    (hMk : MKnownV (iidSystem ν) (t0 - 1) M0) :
    ∃ y φ, MFOCSystem (iidSystem ν) P (fun t ω => C2 *ᵥ iidVAR A b t ω) t0 Z0 M0 y φ ∧
      (∀ y' φ', MFOCSystem (iidSystem ν) P (fun t ω => C2 *ᵥ iidVAR A b t ω) t0 Z0 M0 y' φ' →
        ∀ t, t0 ≤ t → y' t =ᵐ[(iidSystem ν).μ] y t ∧ φ' t =ᵐ[(iidSystem ν).μ] φ t) ∧
      MTimelesslyOptimalPlan (iidSystem ν) P (fun t ω => C2 *ᵥ iidVAR A b t ω) t0 Z0
        (stateX y φ (iidVAR A b)) (zpart (fY P A C2 hA81 (powBdd_of_powDecay hAd)))
        ((FY P A C2 hA81 (powBdd_of_powDecay hAd)).submatrix (Sum.inl ∘ Sum.inr) id) y :=
  m_existsUnique_var P A C2 hA81 _ hstab (iid_isVAR hAd b hbdd hmean) hZk hZb hMb hMk

/-! ### The information conditions on i.i.d. economies -/

/-- Woodford (2003), p. 540 (tool): a function measurable with respect to the σ-algebra generated
by `g` is constant on the fibres of `g`. -/
theorem eq_of_comap_measurable {α β : Type*} [mβ : MeasurableSpace β] {g : α → β} {f : α → ℝ}
    (hf : Measurable[MeasurableSpace.comap g mβ] f) {a a' : α} (h : g a = g a') :
    f a = f a' := by
  have hs : MeasurableSet[MeasurableSpace.comap g mβ] (f ⁻¹' {f a'}) :=
    hf (measurableSet_singleton _)
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have ha' : a' ∈ g ⁻¹' B := by
    rw [hB]
    rfl
  have ha : a ∈ g ⁻¹' B := by
    simp only [Set.mem_preimage] at ha' ⊢
    rw [h]
    exact ha'
  rw [hB] at ha
  exact ha

/-- Woodford (2003), p. 540 (tool): a fair coin takes the values `±1` almost surely. -/
theorem coin_values : ∀ᵐ x ∂(coin : Measure ℝ), x = 1 ∨ x = -1 := by
  change ∀ᵐ x ∂coinMeasure, x = 1 ∨ x = -1
  rw [ae_iff]
  have hset : {x : ℝ | ¬ (x = 1 ∨ x = -1)} = ({1} ∪ {-1} : Set ℝ)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
  have hs : MeasurableSet ({1} ∪ {-1} : Set ℝ)ᶜ :=
    ((measurableSet_singleton 1).union (measurableSet_singleton (-1))).compl
  rw [hset]
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs,
    Set.indicator]
  norm_num

/-- Woodford (2003), p. 541: **on the fair-coin economy every variable known at a date is
essentially bounded** (`BddInfo`): date-`t` information is generated by `t + 1` coins, which a.s.
take finitely many values — although every single history has probability zero. -/
theorem coin_bddInfo (t : ℕ) : BddInfo (iidSystem coin) t := by
  intro f hf
  have hfm : Measurable[MeasurableSpace.comap (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t)
      MeasurableSpace.pi] f := hf.measurable
  set rep : (Set.Iic t → Bool) → (ℕ → ℝ) :=
    fun b n => if h : n ≤ t then (if b ⟨n, h⟩ then 1 else -1) else 0 with hrep
  refine ⟨∑ b : Set.Iic t → Bool, |f (rep b)|, ?_⟩
  filter_upwards [ae_all_iff.2 fun i => (measurePreserving_eval_infinitePi
    (fun _ => (coin : Measure ℝ)) i).quasiMeasurePreserving.ae coin_values] with ω hω
  set b : Set.Iic t → Bool := fun i => decide (ω i.1 = 1) with hb
  have hg : Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω =
      Preorder.restrictLe (π := fun _ : ℕ => ℝ) t (rep b) := by
    funext i
    obtain ⟨n, hn⟩ := i
    simp only [Preorder.restrictLe_apply, hrep, hb]
    have hω' : ω n = 1 ∨ ω n = -1 := hω n
    split_ifs with h h'
    · exact of_decide_eq_true h'
    · rcases hω' with h1 | h1
      · exact absurd (decide_eq_true h1) h'
      · exact h1
    · exact absurd (Set.mem_Iic.mp hn) h
  rw [eq_of_comap_measurable hfm hg]
  exact Finset.single_le_sum (f := fun b => |f (rep b)|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ b)

/-- Woodford (2003), p. 540: at `t = 0` there is nothing earlier, so `PredInfo` holds trivially
(the convention `t₀ − 1 = 0` of the core statements). -/
theorem predInfo_zero {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) :
    PredInfo S 0 := fun _ hf => hf.aestronglyMeasurable

/-- Woodford (2003), p. 540: **the fair-coin economy carries genuine news at every date** — the
date-`t` coin is known at `t` and bounded but not a.s. equal to anything known at `t − 1`, so
`PredInfo` fails at every `t ≥ 1`. -/
theorem coin_not_predInfo {t : ℕ} (ht : 1 ≤ t) : ¬ PredInfo (iidSystem coin) t := by
  intro h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hm := h (shock (s + 1)) (measurable_shock coin le_rfl).stronglyMeasurable
  rw [Nat.add_sub_cancel] at hm
  have hi : Integrable (shock (s + 1)) (iidSystem coin).μ :=
    integrable_of_bound (measurable_shock coin le_rfl |>.mono ((iidSystem coin).𝓕.le _) le_rfl
      |>.aestronglyMeasurable) (shock_ae_bdd coin coin_bdd (s + 1))
  exact shock_not_ae_E coin_mean coin_var one_pos s
    ((iidSystem coin).E_of_aestronglyMeasurable hm hi).symm

/-- Woodford (2003), p. 541 (an unbounded law): standard Gaussian shocks. -/
noncomputable def gaussLaw : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

/-- Woodford (2003), p. 541: **with Gaussian shocks every date carries an unbounded known
variable** (the date-0 shock), so `BddInfo` fails at every `t`. -/
theorem gauss_not_bddInfo (t : ℕ) : ¬ BddInfo (iidSystem gaussLaw) t := by
  intro h
  obtain ⟨K, hK⟩ := h (shock 0) (measurable_shock gaussLaw (Nat.zero_le t)).stronglyMeasurable
  have hmap := (measurePreserving_eval_infinitePi (fun _ => (gaussLaw : Measure ℝ)) 0).map_eq
  have hν : ∀ᵐ x ∂(gaussLaw : Measure ℝ), |x| ≤ K := by
    rw [← hmap]
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)).mpr hK
  have h0 : (gaussLaw : Measure ℝ) (Set.Ioi K) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.mp hν)
    have : K < |x| := lt_of_lt_of_le (Set.mem_Ioi.mp hx) (le_abs_self x)
    exact not_le.mpr this
  have hv := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  rw [Real.volume_Ioi] at hv
  exact ENNReal.top_ne_zero hv

/-! ### The book's Assumption 8.1 and robust optimality on i.i.d. economies -/

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), **Assumption 8.1**, p. 541: **the book's statement fails on the fair-coin
economy at every `t₀ ≥ 1`, for every problem** — a genuine infinite sample space where the
finite-tree counterexample `NKAssumption81.not_assumption81_coin` persists. -/
theorem coin_not_assumption81 (P : LQProblem ιZ ιz ιτ) {t0 : ℕ} (ht0 : 1 ≤ t0) :
    ¬ MAssumption81 (iidSystem coin) P t0 := fun h =>
  coin_not_predInfo ht0 (assumption81_iff.mp h).2.2

/-- Woodford (2003), Assumption 8.1, p. 541, at `t₀ = 0` on the fair-coin economy: **the book's
statement is equivalent to the corrected bounded form** (both information conditions hold). -/
theorem coin_assumption81_zero_iff (P : LQProblem ιZ ιz ιτ) :
    MAssumption81 (iidSystem coin) P 0 ↔ MAssumption81MB (iidSystem coin) P 0 := by
  rw [assumption81_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, coin_bddInfo 0, predInfo_zero _⟩⟩

/-- Woodford (2003), Assumption 8.1, p. 541, on the fair-coin economy: **unbounded initial
conditions are a.s. impossible, so `Prop82General.Assumption81M`'s measure form is equivalent to
the bounded form `MAssumption81MB`** — the boundedness counterexample
(`InertiaAssumption81.not_in_focSolvableM`) does not survive here. -/
theorem coin_assumption81M_iff (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    MAssumption81M (iidSystem coin) P t0 ↔ MAssumption81MB (iidSystem coin) P t0 := by
  rw [assumption81M_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ => coin_bddInfo t0⟩⟩

omit [DecidableEq ιZ] in
/-- Woodford (2003), Definition, pp. 549–550, on the fair-coin economy: **robust optimality for
every initial condition is equivalent to robust optimality for bounded ones** (every
`Z_{t₀}` known at `t₀` is a.s. bounded). -/
theorem coin_robustlyOptimal_iff (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) {κ : Type*} [Fintype κ]
    (Rl : (ℕ → (ℕ → ℝ) → ιz → ℝ) → (ℕ → (ℕ → ℝ) → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → (ℕ → ℝ) → ιz → ℝ) → (ℕ → (ℕ → ℝ) → (ιZ ⊕ ιz) ⊕ Unit → ℝ) →
      ℕ → (ℕ → ℝ) → κ → ℝ) :
    MRobustlyOptimal (iidSystem coin) P t0 Rl Xbar ↔
      MRobustlyOptimalB (iidSystem coin) P t0 Rl Xbar := by
  rw [robustlyOptimal_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ => coin_bddInfo t0⟩⟩

/-- Woodford (2003), **Assumption 8.1**, p. 541: **the book's statement fails on the Gaussian
economy at every `t₀`, for every problem** (an unbounded initial multiplier admits no bounded
solution). -/
theorem gauss_not_assumption81 (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    ¬ MAssumption81 (iidSystem gaussLaw) P t0 := fun h =>
  gauss_not_bddInfo t0 (assumption81_iff.mp h).2.1

/-- Woodford (2003), Assumption 8.1, p. 541: on the Gaussian economy even the form with a
bounded, predetermined initial multiplier (`Prop82General.Assumption81M`) fails for every
problem with a predetermined variable — the measure-theoretic
`InertiaAssumption81.not_in_assumption81M`. -/
theorem gauss_not_assumption81M [Nonempty ιZ] (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    ¬ MAssumption81M (iidSystem gaussLaw) P t0 := fun h =>
  gauss_not_bddInfo t0 ((assumption81M_iff.mp h).2 inferInstance)

omit [DecidableEq ιZ] in
/-- Woodford (2003), Definition, pp. 549–550: **on the Gaussian economy no rule is robustly optimal
for every initial condition** when there is a predetermined variable — the measure-theoretic
`InertiaAssumption81.not_robustlyOptimal`; the bounded form `MRobustlyOptimalB` is the right
one. -/
theorem gauss_not_robustlyOptimal [Nonempty ιZ] (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) {κ : Type*}
    [Fintype κ] (Rl : (ℕ → (ℕ → ℝ) → ιz → ℝ) → (ℕ → (ℕ → ℝ) → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → (ℕ → ℝ) → ιz → ℝ) → (ℕ → (ℕ → ℝ) → (ιZ ⊕ ιz) ⊕ Unit → ℝ) →
      ℕ → (ℕ → ℝ) → κ → ℝ) :
    ¬ MRobustlyOptimal (iidSystem gaussLaw) P t0 Rl Xbar := fun h =>
  gauss_not_bddInfo t0 ((robustlyOptimal_iff Rl Xbar).mp h |>.2 inferInstance)

end Woodford.OptimalPolicyRules.OptimalRulesMeasureIID
