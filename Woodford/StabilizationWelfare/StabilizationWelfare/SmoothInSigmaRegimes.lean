/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasure

/-!
# Certainty equivalence with Markov-switching shock laws

Woodford (2003), *Interest and Prices*, Chapter 6, Appendix E.2 (p. 695), and the perturbation
method of `SmoothInSigma`/`SmoothInSigmaMeasure`, extended to SEVERAL REGIMES: the shock law
`ν_r` depends on a Markov regime `r` (`MModel` with a finite regime set and transition matrix).

Certainty equivalence survives regime switching under the natural condition that EVERY regime's
clipped shock has mean zero; no counterexample is needed. The proof integrates the shocks out
given the regimes (`avgOut`, a bounded linear projection on the adapted subspace) and shows that
it commutes with the linearised operator `L` (Fubini, using that `f` does not depend on the
regime and that shocks are independent given the regimes); injectivity of `L` then kills the
`σ`-derivative in every regime.

## Main results

* `integral_pi_cons`, `mixH`, `lawPi`, `avgOut`, `avgS`: integrating out the first `t` shocks of
  a history under `⊗_{i<t} ν_{r_i}`; `avgOut_mem`, `norm_avgOut_le`, `avgOut_zero`.
* `avgOut_linOp` (`Π(L w) = L(Π w)`), `avgOut_add`, `avgOut_Phi_sigma`.
* `certainty_equivalence_regimes`: `g_σ(ȳ, 0, 0; r) = 0` in every regime `r`.
* `sR`, `policyR`, `markovR`, `markov_derivR`: the regime-dependent policy functions and the
  Markov property of the equilibrium.
* `second_order_sigma_regimes`: the COUPLED `σ²` system across regimes,
  `∑_{r'} P(r₀, r')[A G′_{r'}(g_σσ(r₀), 0, 0) + A g_σσ(r') + B g_σσ(r₀)
    + V_{r'}(A G_ss(r') + D²f(z̄)(…))] = 0` for every current regime `r₀`.
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaRegimes

open MeasureTheory Filter Topology
open SmoothInSigmaMeasure (Hist consH tailH consH_zero consH_succ tailH_consH adSub clipB
  MModel FinMem measurable_consH measurable_tailH abs_clipB_le continuous_clipB integrable_clipB)
open SmoothInSigmaMeasure.MModel (lagF ubar)
open SmoothInSigma (Bd mkBd mkBd_apply norm_apply_le norm_le_of_forall pbar zbar evalL)

/-! ## Integrating out the newest coordinate of a product law -/

/-- Woodford (2003), App. E.2 (Fubini on the event tree): for a product law on `ℝ^{n+1}` and a
bounded measurable `g`, `∫ g d(⊗μ_i) = ∫∫ g(e :: x) dμ₀(e) d(⊗μ_{i+1})(x)`. -/
theorem integral_pi_cons {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {n : ℕ} (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (Fin (n + 1) → ℝ) → V} (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    ∫ x, g x ∂(Measure.pi μ) =
      ∫ x, ∫ e, g (Fin.cons e x) ∂(μ 0) ∂(Measure.pi fun j => μ j.succ) := by
  have h := measurePreserving_piFinSuccAbove (α := fun _ => ℝ) μ 0
  have h1 : ∫ x, g x ∂(Measure.pi μ) =
      ∫ x, g ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
        (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x)) ∂(Measure.pi μ) := by
    simp only [MeasurableEquiv.symm_apply_apply]
  rw [h1, h.integral_comp' (fun y => g ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm y))]
  have hm : StronglyMeasurable fun y : ℝ × (Fin n → ℝ) =>
      g ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm y) :=
    hg.comp_measurable (MeasurableEquiv.measurable _)
  rw [integral_prod_symm _ (Integrable.of_bound hm.aestronglyMeasurable C
    (Eventually.of_forall fun y => hC _))]
  simp only [Fin.succAbove_zero]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  refine congrArg g (funext fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]

/-! ## Integrating out the shocks given the regimes -/

variable {R : Type}

/-- Woodford (2003), App. E.2: the history `s` with its first `t` shocks replaced by `x`
(regimes, and entries from `t` on, unchanged). -/
def mixH (t : ℕ) (s : Hist R) (x : Fin t → ℝ) : Hist R := fun i =>
  ((s i).1, if h : i < t then x ⟨i, h⟩ else (s i).2)

/-- Woodford (2003), App. E.2: replacing no shocks leaves the history unchanged. -/
theorem mixH_zero (s : Hist R) (x : Fin 0 → ℝ) : mixH 0 s x = s := by
  funext i
  simp [mixH]

/-- Woodford (2003), App. E.2: replacing the shocks of a successor history. -/
theorem mixH_cons (t : ℕ) (r : R) (e0 e : ℝ) (s : Hist R) (x : Fin t → ℝ) :
    mixH (t + 1) (consH (r, e0) s) (Fin.cons e x) = consH (r, e) (mixH t s x) := by
  funext i
  cases i with
  | zero => simp [mixH]
  | succ j =>
    by_cases hj : j < t
    · have hj' : j + 1 < t + 1 := by omega
      simp only [mixH, consH_succ, hj, hj', ↓reduceDIte]
      exact congrArg (Prod.mk _) (Fin.cons_succ (α := fun _ : Fin (t + 1) => ℝ) e x ⟨j, hj⟩)
    · have hj' : ¬ j + 1 < t + 1 := by omega
      simp only [mixH, consH_succ, hj, hj', ↓reduceDIte]

/-- Woodford (2003), App. E.2: the predecessor of a history with replaced shocks. -/
theorem tailH_mixH (t : ℕ) (s : Hist R) (x : Fin (t + 1) → ℝ) :
    tailH (mixH (t + 1) s x) = mixH t (tailH s) (fun j => x j.succ) := by
  funext i
  by_cases hi : i < t
  · have hi' : i + 1 < t + 1 := by omega
    simp only [tailH, mixH, hi, hi', ↓reduceDIte]
    rfl
  · have hi' : ¬ i + 1 < t + 1 := by omega
    simp only [tailH, mixH, hi, hi', ↓reduceDIte]

variable [MeasurableSpace R]

/-- Woodford (2003), App. E.2: replacing the shocks is measurable. -/
theorem measurable_mixH (t : ℕ) (s : Hist R) : Measurable (mixH t s) := by
  refine measurable_pi_iff.mpr fun i => measurable_const.prodMk ?_
  by_cases h : i < t
  · simp only [h, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]
    exact measurable_const

variable {Y Z : Type}

/-- Woodford (2003), App. E.2: the law of the first `t` shocks given the regimes of `s`, the
product `⊗_{i < t} ν_{r_i}`. -/
noncomputable abbrev lawPi (M : MModel R Y Z) (t : ℕ) (s : Hist R) : Measure (Fin t → ℝ) :=
  Measure.pi fun i : Fin t => (M.law (s i).1 : Measure ℝ)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Woodford (2003), App. E.2 (**integrating out the shocks given the regimes**):
`(Π w)(t, s) = ∫ w(t, s with shocks x) d(⊗_{i < t} ν_{r_i})(x)`. -/
noncomputable def avgOut (M : MModel R Y Z) (w : ℕ × Hist R → V) : ℕ × Hist R → V := fun n =>
  ∫ x, w (n.1, mixH n.1 n.2 x) ∂(lawPi M n.1 n.2)

/-- Woodford (2003), App. E.2: along a family adapted in the history, the integrand of `Π` is
integrable. -/
theorem integrable_mix (M : MModel R Y Z) {w : Bd (ℕ × Hist R) V} (hw : w ∈ adSub (R := R) V)
    (t : ℕ) (s : Hist R) : Integrable (fun x => w (t, mixH t s x)) (lawPi M t s) :=
  Integrable.of_bound ((hw.1 t).comp_measurable (measurable_mixH t s)).aestronglyMeasurable
    ‖w‖ (Eventually.of_forall fun _ => norm_apply_le w _)

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `Π` does not increase the sup norm. -/
theorem norm_avgOut_le (M : MModel R Y Z) (w : Bd (ℕ × Hist R) V) (n : ℕ × Hist R) :
    ‖avgOut M (w : ℕ × Hist R → V) n‖ ≤ ‖w‖ := by
  have := norm_integral_le_of_norm_le_const (μ := lawPi M n.1 n.2)
    (f := fun x => w (n.1, mixH n.1 n.2 x)) (C := ‖w‖)
    (Eventually.of_forall fun _ => norm_apply_le w _)
  simp only [avgOut]
  simpa using this

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `Π w` at date `t` depends only on the regimes up to `t`. -/
theorem avgOut_congr (M : MModel R Y Z) {w : ℕ × Hist R → V} (hw : FinMem w) {t : ℕ}
    {s s' : Hist R} (h : ∀ i ≤ t, (s i).1 = (s' i).1) : avgOut M w (t, s) = avgOut M w (t, s') := by
  have hl : lawPi M t s = lawPi M t s' := by
    unfold lawPi
    congr 1
    funext i
    rw [h i (le_of_lt i.2)]
  simp only [avgOut]
  rw [hl]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine hw t _ _ (fun i hi => ?_) ?_
  · simp only [mixH, hi, ↓reduceDIte, h i hi.le]
  · simp only [mixH, h t le_rfl]

variable [Finite R] [MeasurableSingletonClass R]

/-- Woodford (2003), App. E.2: `Π w` is measurable in the history (it is a function of the
finitely many regimes). -/
theorem stronglyMeasurable_avgOut (M : MModel R Y Z) {w : ℕ × Hist R → V} (hw : FinMem w)
    (t : ℕ) : StronglyMeasurable fun s => avgOut M w (t, s) := by
  set reg : Hist R → (Fin (t + 1) → R) := fun s i => (s i).1 with hreg
  set canon : (Fin (t + 1) → R) → Hist R := fun ρ i =>
    (if h : i < t + 1 then ρ ⟨i, h⟩ else ρ ⟨t, Nat.lt_succ_self t⟩, 0) with hcanon
  have he : (fun s => avgOut M w (t, s)) = (fun ρ => avgOut M w (t, canon ρ)) ∘ reg := by
    funext s
    refine avgOut_congr M hw (fun i hi => ?_)
    have hi' : i < t + 1 := Nat.lt_succ_of_le hi
    simp only [hcanon, hreg, hi', ↓reduceDIte]
  rw [he]
  exact StronglyMeasurable.of_discrete.comp_measurable
    (measurable_pi_iff.mpr fun i => measurable_fst.comp (measurable_pi_apply _))

/-- Woodford (2003), App. E.2: `Π` maps bounded adapted families to bounded adapted families. -/
theorem avgOut_mem (M : MModel R Y Z) (w : adSub (R := R) V) :
    mkBd (avgOut M ((w : Bd (ℕ × Hist R) V) : ℕ × Hist R → V))
      ⟨‖(w : Bd (ℕ × Hist R) V)‖, norm_avgOut_le M _⟩ ∈ adSub (R := R) V := by
  refine ⟨fun t => ?_, fun t s s' h1 h2 => ?_⟩
  · simpa only [mkBd_apply] using stronglyMeasurable_avgOut M w.2.2 t
  · simp only [mkBd_apply]
    refine avgOut_congr M w.2.2 (fun i hi => ?_)
    rcases lt_or_eq_of_le hi with h | h
    · rw [h1 i h]
    · rw [h]; exact h2

/-- Woodford (2003), App. E.2 (**the shock-integrating projection**) as a map on the bounded
adapted families. -/
noncomputable def avgS (M : MModel R Y Z) (w : adSub (R := R) V) : adSub (R := R) V :=
  ⟨_, avgOut_mem M w⟩

/-- Woodford (2003), App. E.2: members of `avgS`. -/
theorem avgS_apply (M : MModel R Y Z) (w : adSub (R := R) V) (n : ℕ × Hist R) :
    ((avgS M w : adSub (R := R) V) : Bd (ℕ × Hist R) V) n =
      avgOut M ((w : Bd (ℕ × Hist R) V) : ℕ × Hist R → V) n :=
  rfl

omit [MeasurableSpace R] [Finite R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2: at date `0` nothing is integrated out, `(Π w)(0, s) = w(0, s)`. -/
theorem avgOut_zero (M : MModel R Y Z) [CompleteSpace V] (w : ℕ × Hist R → V) (s : Hist R) :
    avgOut M w (0, s) = w (0, s) := by
  simp only [avgOut, mixH_zero]
  simp

/-! ## `Π` commutes with the linearised operator -/

omit [MeasurableSpace R] [Finite R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2: under a probability law, `∫ (A a(e) + b + c) = A ∫ a + b + c`. -/
theorem integral_lin3 {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [CompleteSpace V] (ν : ProbabilityMeasure ℝ) (A : W →L[ℝ] V)
    {a : ℝ → W} (ha : Integrable a (ν : Measure ℝ)) (b c : V) :
    ∫ e, (A (a e) + b + c) ∂(ν : Measure ℝ) = A (∫ e, a e ∂(ν : Measure ℝ)) + b + c := by
  rw [integral_add (f := fun e => A (a e) + b) (g := fun _ => c)
    ((A.integrable_comp ha).add (integrable_const b)) (integrable_const c),
    integral_add (f := fun e => A (a e)) (g := fun _ => b) (A.integrable_comp ha)
    (integrable_const b), A.integral_comp_comm ha]
  simp

omit [Finite R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2: the branch average along replaced shocks is integrable. -/
theorem integrable_mix_branch (M : MModel R Y Z) {w : Bd (ℕ × Hist R) V}
    [CompleteSpace V] (hw : w ∈ adSub (R := R) V) (t : ℕ) (s : Hist R) (r' : R) :
    Integrable (fun x => ∫ e, w (t + 1, consH (r', e) (mixH t s x)) ∂(M.law r' : Measure ℝ))
      (lawPi M t s) := by
  have hm : StronglyMeasurable fun q : (Fin t → ℝ) × ℝ =>
      w (t + 1, consH (r', q.2) (mixH t s q.1)) :=
    (hw.1 (t + 1)).comp_measurable (measurable_consH.comp
      (((measurable_mixH t s).comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)))
  refine Integrable.of_bound hm.integral_prod_right'.aestronglyMeasurable ‖w‖
    (Eventually.of_forall fun x => ?_)
  have := norm_integral_le_of_norm_le_const (μ := (M.law r' : Measure ℝ))
    (f := fun e => w (t + 1, consH (r', e) (mixH t s x))) (C := ‖w‖)
    (Eventually.of_forall fun _ => norm_apply_le w _)
  simpa using this

omit [Finite R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2: the lagged value along replaced shocks is integrable. -/
theorem integrable_mix_lag (M : MModel R Y Z) {w : Bd (ℕ × Hist R) V}
    (hw : w ∈ adSub (R := R) V) (t : ℕ) (s : Hist R) :
    Integrable (fun x => lagF (0 : V × ℝ × ℝ) (w : ℕ × Hist R → V) (t, mixH t s x))
      (lawPi M t s) := by
  cases t with
  | zero => simp [lagF]
  | succ k =>
    refine Integrable.of_bound ((hw.1 k).comp_measurable
      (measurable_tailH.comp (measurable_mixH (k + 1) s))).aestronglyMeasurable ‖w‖
      (Eventually.of_forall fun _ => norm_apply_le w _)

omit [Finite R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2: integrating the next-period branch along replaced shocks is
`Π` at the successor, `∫∫ w(t + 1, (r', e) :: s_x) = ∫ (Π w)(t + 1, (r', e) :: s)`. -/
theorem integral_mix_branch (M : MModel R Y Z) {w : Bd (ℕ × Hist R) V} [CompleteSpace V]
    (hw : w ∈ adSub (R := R) V) (t : ℕ) (s : Hist R) (r' : R) :
    ∫ x, ∫ e, w (t + 1, consH (r', e) (mixH t s x)) ∂(M.law r' : Measure ℝ) ∂(lawPi M t s) =
      ∫ e, avgOut M (w : ℕ × Hist R → V) (t + 1, consH (r', e) s) ∂(M.law r' : Measure ℝ) := by
  have hc : ∀ e, avgOut M (w : ℕ × Hist R → V) (t + 1, consH (r', e) s) =
      avgOut M (w : ℕ × Hist R → V) (t + 1, consH (r', 0) s) := fun e =>
    avgOut_congr M hw.2 (fun i _ => by cases i <;> rfl)
  simp only [hc, integral_const, probReal_univ, one_smul]
  simp only [avgOut]
  have h := integral_pi_cons (fun i : Fin (t + 1) => (M.law (consH (r', 0) s i).1 : Measure ℝ))
    (g := fun x => (w : ℕ × Hist R → V) (t + 1, mixH (t + 1) (consH (r', 0) s) x))
    ((hw.1 (t + 1)).comp_measurable (measurable_mixH (t + 1) (consH (r', 0) s)))
    (fun _ => norm_apply_le w _)
  refine Eq.trans ?_ h.symm
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  simp only [mixH_cons]

omit [Finite R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2: integrating the lagged value along replaced shocks is the lag of
`Π`. -/
theorem integral_mix_lag (M : MModel R Y Z) {w : Bd (ℕ × Hist R) V} [CompleteSpace V]
    (hw : w ∈ adSub (R := R) V) (t : ℕ) (s : Hist R) :
    ∫ x, lagF (0 : V × ℝ × ℝ) (w : ℕ × Hist R → V) (t, mixH t s x) ∂(lawPi M t s) =
      lagF (0 : V × ℝ × ℝ) (avgOut M (w : ℕ × Hist R → V)) (t, s) := by
  cases t with
  | zero => simp [lagF]
  | succ k =>
    simp only [lagF, tailH_mixH]
    have h := integral_pi_cons (fun i : Fin (k + 1) => (M.law (s i).1 : Measure ℝ))
      (g := fun x => (w : ℕ × Hist R → V) (k, mixH k (tailH s) fun j => x j.succ))
      ((hw.1 k).comp_measurable ((measurable_mixH k (tailH s)).comp
        (measurable_pi_iff.mpr fun j => measurable_pi_apply j.succ)))
      (fun _ => norm_apply_le w _)
    refine h.trans ?_
    simp only [Fin.cons_succ, integral_const, probReal_univ, one_smul, avgOut]
    rfl

omit [Finite R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2: along a branch, an adapted family is an integrable function of the
next shock. -/
theorem integrable_branchV (ν : ProbabilityMeasure ℝ) {w : Bd (ℕ × Hist R) V}
    (hw : w ∈ adSub (R := R) V) (t : ℕ) (s : Hist R) (r' : R) :
    Integrable (fun e => w (t + 1, consH (r', e) s)) (ν : Measure ℝ) :=
  Integrable.of_bound ((hw.1 (t + 1)).comp_measurable (measurable_consH.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
    ‖w‖ (Eventually.of_forall fun _ => norm_apply_le w _)

variable [Fintype R] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Woodford (2003), App. E.2 (**`Π` commutes with the linearised operator**): integrating out
the shocks given the regimes commutes with `L`, `Π(L w) = L(Π w)`, because `f` does not depend
on the regime and the shocks are independent given the regimes (Fubini). -/
theorem avgOut_linOp (M : MModel R Y Z) (hM : M.Std) (hf : ContDiff ℝ 1 M.f) (ybar : Y)
    (w : adSub (R := R) Y) (t : ℕ) (s : Hist R) :
    avgOut M (((M.linOp hM hf.continuous ybar w : adSub (R := R) Z) : Bd (ℕ × Hist R) Z) :
        ℕ × Hist R → Z) (t, s) =
      ((M.linOp hM hf.continuous ybar (avgS M w) : adSub (R := R) Z) :
        Bd (ℕ × Hist R) Z) (t, s) := by
  rw [M.linOp_apply hM hf.continuous hf ybar (avgS M w) t s]
  simp only [avgOut]
  have hx : ∀ x, ((M.linOp hM hf.continuous ybar w : adSub (R := R) Z) : Bd (ℕ × Hist R) Z)
      (t, mixH t s x) = ∑ r', M.trans (s 0).1 r' •
        (M.dA ybar (∫ e, (w : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) (mixH t s x))
          ∂(M.law r' : Measure ℝ)) + M.dB ybar ((w : Bd (ℕ × Hist R) Y) (t, mixH t s x)) +
          M.dC ybar (lagF 0 (w : Bd (ℕ × Hist R) Y) (t, mixH t s x))) := fun x => by
    rw [M.linOp_apply hM hf.continuous hf ybar w t (mixH t s x)]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [integral_lin3 (M.law r') (M.dA ybar) (integrable_branchV (M.law r') w.2 t _ r')]
    rfl
  rw [integral_congr_ae (Eventually.of_forall hx)]
  set a : R → (Fin t → ℝ) → Y := fun r' x =>
    ∫ e, (w : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) (mixH t s x)) ∂(M.law r' : Measure ℝ)
    with ha
  set b : (Fin t → ℝ) → Y := fun x => (w : Bd (ℕ × Hist R) Y) (t, mixH t s x) with hb
  set c : (Fin t → ℝ) → Y := fun x => lagF 0 (w : Bd (ℕ × Hist R) Y) (t, mixH t s x) with hc
  have ia : ∀ r', Integrable (a r') (lawPi M t s) := fun r' => integrable_mix_branch M w.2 t s r'
  have ib : Integrable b (lawPi M t s) := integrable_mix M w.2 t s
  have ic : Integrable c (lawPi M t s) := integrable_mix_lag M w.2 t s
  have iA : ∀ r', Integrable (fun x => M.dA ybar (a r' x)) (lawPi M t s) := fun r' =>
    (M.dA ybar).integrable_comp (ia r')
  have iB : Integrable (fun x => M.dB ybar (b x)) (lawPi M t s) := (M.dB ybar).integrable_comp ib
  have iC : Integrable (fun x => M.dC ybar (c x)) (lawPi M t s) := (M.dC ybar).integrable_comp ic
  refine (integral_finsetSum (μ := lawPi M t s) Finset.univ
    (f := fun r' x => M.trans (s 0).1 r' • (M.dA ybar (a r' x) + M.dB ybar (b x) +
      M.dC ybar (c x))) (fun r' _ => (((iA r').add iB).add iC).smul _)).trans ?_
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [integral_smul, integral_add (f := fun x => M.dA ybar (a r' x) + M.dB ybar (b x))
    (g := fun x => M.dC ybar (c x)) ((iA r').add iB) iC,
    integral_add (f := fun x => M.dA ybar (a r' x)) (g := fun x => M.dB ybar (b x)) (iA r') iB,
    (M.dA ybar).integral_comp_comm (ia r'), (M.dB ybar).integral_comp_comm ib,
    (M.dC ybar).integral_comp_comm ic, ha, hc, integral_mix_branch M w.2 t s r',
    integral_mix_lag M w.2 t s,
    integral_lin3 (M.law r') (M.dA ybar) (integrable_branchV (M.law r') (avgS M w).2 t s r')]
  rfl

/-! ## Certainty equivalence with Markov-switching laws -/

omit [Finite R] [MeasurableSingletonClass R] [Fintype R] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: `Π` is additive on bounded adapted families. -/
theorem avgOut_add {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (M : MModel R Y Z) (g h : adSub (R := R) W) (t : ℕ) (s : Hist R) :
    avgOut M (((g + h : adSub (R := R) W) : Bd (ℕ × Hist R) W) : ℕ × Hist R → W) (t, s) =
      avgOut M ((g : Bd (ℕ × Hist R) W) : ℕ × Hist R → W) (t, s) +
        avgOut M ((h : Bd (ℕ × Hist R) W) : ℕ × Hist R → W) (t, s) := by
  simp only [avgOut]
  rw [← integral_add (integrable_mix M g.2 t s) (integrable_mix M h.2 t s)]
  rfl

omit [Finite R] in
/-- Woodford (2003), App. E.2 (**the direct effect of `σ` integrates out**): the derivative of
the equilibrium map in `σ` alone is `f_{e_t} σ clip(ε_t)` at every node when every regime's
clipped shock has mean zero, and `Π` of it vanishes. -/
theorem avgOut_Phi_sigma (M : MModel R Y Z) (hM : M.Std) (hf : ContDiff ℝ 1 M.f) (ybar : Y)
    (hmean : ∀ r, ∫ e, clipB M.bound e ∂(M.law r : Measure ℝ) = 0) (t : ℕ) (s : Hist R) :
    avgOut M (((fderiv ℝ (M.Phi hM hf.continuous) ((pbar ybar : Y × ℝ × ℝ),
      SmoothInSigmaMeasure.MModel.ubar ybar) (((0, 0, 1) : Y × ℝ × ℝ), (0 : adSub (R := R) Y)) :
        adSub (R := R) Z) : Bd (ℕ × Hist R) Z) : ℕ × Hist R → Z) (t, s) = 0 := by
  have hnode : ∀ s' : Hist R, ((fderiv ℝ (M.Phi hM hf.continuous) ((pbar ybar : Y × ℝ × ℝ),
      SmoothInSigmaMeasure.MModel.ubar ybar) (((0, 0, 1) : Y × ℝ × ℝ), (0 : adSub (R := R) Y)) :
        adSub (R := R) Z) : Bd (ℕ × Hist R) Z) (t, s') =
      M.dN ybar (M.enowF ((0, 0, 1) : Y × ℝ × ℝ) (t, s')) := fun s' => by
    rw [M.fderiv_Phi_apply hM hf.continuous hf ybar]
    have hl : lagF ((0, 0, 1) : Y × ℝ × ℝ)
        ((0 : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (t, s') = 0 := by
      cases t <;> rfl
    have hi : ∀ r', ∫ e, fderiv ℝ M.f (zbar ybar) (M.wfun ((0, 0, 1) : Y × ℝ × ℝ)
        ((0 : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s'))
        ∂(M.law r' : Measure ℝ) = M.dN ybar (M.enowF ((0, 0, 1) : Y × ℝ × ℝ) (t, s')) := by
      intro r'
      have he : ∀ e, fderiv ℝ M.f (zbar ybar) (M.wfun ((0, 0, 1) : Y × ℝ × ℝ)
          ((0 : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s')) =
          M.dN ybar (M.enowF ((0, 0, 1) : Y × ℝ × ℝ) (t, s')) +
            M.dE ybar (clipB M.bound e) := fun e => by
        simp only [MModel.wfun, tailH_consH, consH_zero, M.fderiv_f_apply, one_mul]
        rw [hl]
        have z : ∀ n, ((0 : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) n = 0 := fun _ => rfl
        rw [z, z]
        simp
      simp only [he]
      rw [integral_add (integrable_const _) ((M.dE ybar).integrable_comp
        (integrable_clipB M.bound (M.law r'))), (M.dE ybar).integral_comp_comm
        (integrable_clipB M.bound (M.law r')), hmean r']
      simp
    simp only [hi, ← Finset.sum_smul, hM.trans_sum, one_smul]
  simp only [avgOut, hnode]
  cases t with
  | zero => simp [MModel.enowF]
  | succ k =>
    have hx : ∀ x : Fin (k + 1) → ℝ, M.dN ybar (M.enowF ((0, 0, 1) : Y × ℝ × ℝ)
        (k + 1, mixH (k + 1) s x)) = M.dN ybar (clipB M.bound (x 0)) := fun x => by
      simp only [MModel.enowF, one_mul]
      rfl
    simp only [hx]
    have hg : StronglyMeasurable fun x : Fin (k + 1) → ℝ => clipB M.bound (x 0) :=
      ((continuous_clipB M.bound).measurable.comp (measurable_pi_apply 0)).stronglyMeasurable
    have hgi : Integrable (fun x : Fin (k + 1) → ℝ => clipB M.bound (x 0)) (lawPi M (k + 1) s) :=
      Integrable.of_bound hg.aestronglyMeasurable |M.bound| (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_clipB_le _ _)
    rw [(M.dN ybar).integral_comp_comm hgi]
    have h := integral_pi_cons (fun i : Fin (k + 1) => (M.law (s i).1 : Measure ℝ)) hg
      (C := |M.bound|) (fun x => by rw [Real.norm_eq_abs]; exact abs_clipB_le _ _)
    rw [show (∫ x, clipB M.bound (x 0) ∂(lawPi M (k + 1) s)) = 0 from by
      refine h.trans ?_
      simp only [Fin.cons_zero]
      have h0 : ∫ e, clipB M.bound e ∂(M.law (s 0).1 : Measure ℝ) = 0 := hmean _
      simp [h0]]
    simp

/-- Woodford (2003), App. E.2, and the perturbation method (**certainty equivalence with
Markov-switching shock laws**): if every regime's clipped shock has mean zero and the
linearised operator is invertible (determinacy), the derivative of the equilibrium in `σ`
vanishes at the root in EVERY regime, `g_σ(ȳ, 0, 0; r) = 0`. The proof integrates the shocks
out given the regimes (`avgS`, which commutes with `L`, `avgOut_linOp`). -/
theorem certainty_equivalence_regimes [CompleteSpace Y] (M : MModel R Y Z) (hM : M.Std)
    (hf : ContDiff ℝ 1 M.f) {ybar : Y} (hL : (M.linOp hM hf.continuous ybar).IsInvertible)
    {ψ : Y × ℝ × ℝ → adSub (R := R) Y} (hψ : M.LocalSol ybar ψ)
    {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := R) Y} (hψd : HasFDerivAt ψ ψ' (pbar ybar))
    (hmean : ∀ r, ∫ e, clipB M.bound e ∂(M.law r : Measure ℝ) = 0) (s : Hist R) :
    ((ψ' (0, 0, 1) : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (0, s) = 0 := by
  set v : adSub (R := R) Y := ψ' (0, 0, 1) with hv
  set P' := fderiv ℝ (M.Phi hM hf.continuous) ((pbar ybar : Y × ℝ × ℝ),
    SmoothInSigmaMeasure.MModel.ubar ybar) with hP'
  have hQ : P' (((0, 0, 1) : Y × ℝ × ℝ), (0 : adSub (R := R) Y)) +
      M.linOp hM hf.continuous ybar v = 0 := by
    rw [← M.ift_identity hM hf hψ hψd (0, 0, 1), SmoothInSigmaMeasure.MModel.linOp,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_add]
    simp [hv, hP']
  have hz : M.linOp hM hf.continuous ybar (avgS M v) = 0 := by
    refine Subtype.ext (lp.ext (funext fun n => ?_))
    rcases n with ⟨t, s'⟩
    rw [← avgOut_linOp M hM hf ybar v t s']
    have h0 := congrArg (fun q : adSub (R := R) Z =>
      avgOut M ((q : Bd (ℕ × Hist R) Z) : ℕ × Hist R → Z) (t, s')) hQ
    simp only at h0
    rw [avgOut_add, avgOut_Phi_sigma M hM hf ybar hmean, zero_add] at h0
    rw [h0]
    simp [avgOut]
  obtain ⟨E, hE⟩ := hL
  have hzero : avgS M v = 0 := by
    have h1 : (E : adSub (R := R) Y →L[ℝ] adSub (R := R) Z) (avgS M v) = 0 := by
      rw [hE]; exact hz
    exact E.injective (by simpa using h1)
  have := congrArg (fun q : adSub (R := R) Y => (q : Bd (ℕ × Hist R) Y) (0, s)) hzero
  simp only [avgS_apply, avgOut_zero] at this
  simpa using this

/-! ## The `σ²` system with Markov-switching laws -/

omit [Finite R] [MeasurableSingletonClass R] [Fintype R] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the root history in regime `r`. -/
def sR (r : R) : Hist R := fun _ => (r, 0)

omit [Finite R] [MeasurableSingletonClass R] [Fintype R] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695 (**the policy function in regime `r`**):
`g(y_{−1}, s₀, σ; r) = ψ(y_{−1}, s₀, σ)(0, r)`. -/
def policyR (ψ : Y × ℝ × ℝ → adSub (R := R) Y) (r : R) (p : Y × ℝ × ℝ) : Y :=
  (ψ p : Bd (ℕ × Hist R) Y) (0, sR r)

omit [Finite R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695 (**Markov, regimes**): near `p̄`, the date-1 decision after
the regime `r'` and the shock `e` is `g(y_0, σ clip(e), σ; r')`. -/
theorem markovR (M : MModel R Y Z) {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := R) Y}
    (hψ : M.LocalSol ybar ψ) :
    ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ), ∀ (r0 r' : R) (e : ℝ),
      (ψ p : Bd (ℕ × Hist R) Y) (1, consH (r', e) (sR r0)) =
        policyR ψ r' ((ψ p : Bd (ℕ × Hist R) Y) (0, sR r0), p.2.2 * clipB M.bound e, p.2.2) := by
  filter_upwards [M.markov hψ] with p hp r0 r' e
  exact hp 0 (consH (r', e) (sR r0))

omit [Finite R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2 (**differentiating the Markov property, regimes**): with
`G′_{r'} = Dg(p̄; r')`, the derivative of the solution at the date-1 node after the regime `r'`
and the shock `e` is `G′_{r'}(ψ′v(0, r₀), v_σ clip(e), v_σ)`. -/
theorem markov_derivR (M : MModel R Y Z) {ybar : Y} (r0 r' : R) {ψ : Y × ℝ × ℝ → adSub (R := R) Y}
    (hψ : M.LocalSol ybar ψ) {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := R) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {G' : Y × ℝ × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policyR ψ r') G' (pbar ybar)) (v : Y × ℝ × ℝ) (e : ℝ) :
    (ψ' v : Bd (ℕ × Hist R) Y) (1, consH (r', e) (sR r0)) =
      G' ((ψ' v : Bd (ℕ × Hist R) Y) (0, sR r0), v.2.2 * clipB M.bound e, v.2.2) := by
  set ev : ℕ × Hist R → adSub (R := R) Y →L[ℝ] Y := fun n =>
    (evalL Y n).comp (adSub (R := R) Y).subtypeL with hev
  have hin : HasFDerivAt (fun p : Y × ℝ × ℝ =>
      ((ψ p : Bd (ℕ × Hist R) Y) (0, sR r0), p.2.2 * clipB M.bound e, p.2.2))
      (((ev (0, sR r0)).comp ψ').prod
        (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ))).smulRight
          (clipB M.bound e) |>.prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ)))))
      (pbar ybar) := by
    refine ((ev (0, sR r0)).hasFDerivAt.comp _ hψd).prodMk ?_
    refine HasFDerivAt.prodMk ?_ ?_
    · have := (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ))).smulRight (clipB M.bound e)).hasFDerivAt
        (x := (pbar ybar : Y × ℝ × ℝ))
      convert this using 1
      funext p
      simp [smul_eq_mul]
    · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ))).hasFDerivAt
  have hval : ((ψ (pbar ybar) : Bd (ℕ × Hist R) Y) (0, sR r0),
      (pbar ybar : Y × ℝ × ℝ).2.2 * clipB M.bound e, (pbar ybar : Y × ℝ × ℝ).2.2) =
      (pbar ybar : Y × ℝ × ℝ) := by
    rw [hψ.base]
    simp [pbar, ubar]
  rw [← hval] at hg
  have hR := hg.comp (pbar ybar) hin
  have hL : HasFDerivAt (fun p => (ψ p : Bd (ℕ × Hist R) Y) (1, consH (r', e) (sR r0)))
      ((ev (1, consH (r', e) (sR r0))).comp ψ') (pbar ybar) :=
    (ev (1, consH (r', e) (sR r0))).hasFDerivAt.comp _ hψd
  have heq : (fun p => (ψ p : Bd (ℕ × Hist R) Y) (1, consH (r', e) (sR r0))) =ᶠ[𝓝 (pbar ybar)]
      (policyR ψ r' ∘ fun p : Y × ℝ × ℝ =>
        ((ψ p : Bd (ℕ × Hist R) Y) (0, sR r0), p.2.2 * clipB M.bound e, p.2.2)) := by
    filter_upwards [markovR M hψ] with p hp
    exact hp r0 r' e
  have hU := hL.unique (hR.congr_of_eventuallyEq heq)
  have := congrArg (fun L : Y × ℝ × ℝ →L[ℝ] Y => L v) hU
  simpa [hev, mul_comm] using this


set_option maxHeartbeats 4000000 in
-- the chain of node identities and second derivatives is long to elaborate
omit [Finite R] in
/-- Woodford (2003), App. E.2, and the second-order perturbation equation (**the coupled `σ²`
system with Markov-switching laws**): with `g(·; r)` the policy in regime `r`,
`G′_r = Dg(p̄; r)`, `g″_r = D²g(p̄; r)`, `g_σσ(r) = g″_r(e_σ, e_σ)`, `G_s(r) = G′_r(0, 1, 0)`,
`G_ss(r) = g″_r((0,1,0),(0,1,0))` and `V_r = E_r[clip(ε)²]`, for every current regime `r₀`,
`∑_{r'} P(r₀, r')[A G′_{r'}(g_σσ(r₀), 0, 0) + A g_σσ(r') + B g_σσ(r₀)
  + V_{r'}(A G_ss(r') + D²f(z̄)((G_s(r'),0,0,0,1),(G_s(r'),0,0,0,1)))] = 0`,
under mean-zero clipped shocks in every regime and determinacy (certainty equivalence in every
regime, `certainty_equivalence_regimes`, removes the first-order terms). -/
theorem second_order_sigma_regimes [CompleteSpace Y] (M : MModel R Y Z) (hM : M.Std)
    (hf : ContDiff ℝ 2 M.f) {ybar : Y}
    (hL : (M.linOp hM hf.continuous ybar).IsInvertible) {ψ : Y × ℝ × ℝ → adSub (R := R) Y}
    (hψ : M.LocalSol ybar ψ) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (hmean : ∀ r, ∫ e, clipB M.bound e ∂(M.law r : Measure ℝ) = 0) (r0 : R) :
    ∑ r', M.trans r0 r' • (M.dA ybar (fderiv ℝ (policyR ψ r') (pbar ybar)
        (fderiv ℝ (fderiv ℝ (policyR ψ r0)) (pbar ybar) (0, 0, 1) (0, 0, 1), 0, 0)) +
      M.dA ybar (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      M.dB ybar (fderiv ℝ (fderiv ℝ (policyR ψ r0)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      (∫ e, clipB M.bound e ^ 2 ∂(M.law r' : Measure ℝ)) •
        (M.dA ybar (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) (0, 1, 0) (0, 1, 0)) +
          fderiv ℝ (fderiv ℝ M.f) (zbar ybar)
            (fderiv ℝ (policyR ψ r') (pbar ybar) (0, 1, 0), 0, 0, 0, 1)
            (fderiv ℝ (policyR ψ r') (pbar ybar) (0, 1, 0), 0, 0, 0, 1))) = 0 := by
  obtain ⟨e3, he3⟩ : ∃ e3 : Y × ℝ × ℝ, e3 = (0, 0, 1) := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : Y × ℝ × ℝ, e2 = (0, 1, 0) := ⟨_, rfl⟩
  rw [← he3, ← he2]
  have hf1 : ContDiff ℝ 1 M.f := hf.of_le (by norm_num)
  set ev : ℕ × Hist R → adSub (R := R) Y →L[ℝ] Y := fun n =>
    (evalL Y n).comp (adSub (R := R) Y).subtypeL with hev
  set evZ : ℕ × Hist R → adSub (R := R) Z →L[ℝ] Z := fun n =>
    (evalL Z n).comp (adSub (R := R) Z).subtypeL with hevZ
  set evW : ℕ × Hist R → adSub (R := R) (Y × Y × Y × ℝ × ℝ) →L[ℝ] Y × Y × Y × ℝ × ℝ :=
    fun n => (evalL (Y × Y × Y × ℝ × ℝ) n).comp
      (adSub (R := R) (Y × Y × Y × ℝ × ℝ)).subtypeL with hevW
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (pbar ybar)) (pbar ybar) :=
    (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hψev : ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ), HasFDerivAt ψ (fderiv ℝ ψ p) p :=
    (hψ2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hψF1 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (pbar ybar) :=
    ((hψ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg2 : ∀ r, ContDiffAt ℝ 2 (policyR ψ r) (pbar ybar) := fun r =>
    (ev (0, sR r)).contDiff.contDiffAt.comp (pbar ybar) hψ2
  have hgd : ∀ r, HasFDerivAt (policyR ψ r) (fderiv ℝ (policyR ψ r) (pbar ybar)) (pbar ybar) :=
    fun r => ((hg2 r).differentiableAt (by norm_num)).hasFDerivAt
  have hgev : ∀ r, ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ),
      HasFDerivAt (policyR ψ r) (fderiv ℝ (policyR ψ r) p) p := fun r =>
    ((hg2 r).eventually (by simp)).mono fun p hp =>
      (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hgF1 : ∀ r, HasFDerivAt (fderiv ℝ (policyR ψ r))
      (fderiv ℝ (fderiv ℝ (policyR ψ r)) (pbar ybar)) (pbar ybar) := fun r =>
    (((hg2 r).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hfd : ∀ z, HasFDerivAt M.f (fderiv ℝ M.f z) z := fun z =>
    (hf.differentiable (by norm_num) z).hasFDerivAt
  have hfF1 : HasFDerivAt (fderiv ℝ M.f) (fderiv ℝ (fderiv ℝ M.f) (zbar ybar)) (zbar ybar) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _).hasFDerivAt
  have hg'eq : ∀ r, fderiv ℝ (policyR ψ r) (pbar ybar) =
      (ev (0, sR r)).comp (fderiv ℝ ψ (pbar ybar)) := fun r =>
    (hgd r).unique ((ev (0, sR r)).hasFDerivAt.comp (pbar ybar) hψd)
  have hce : ∀ r, fderiv ℝ (policyR ψ r) (pbar ybar) e3 = 0 := fun r => by
    rw [hg'eq r, he3]
    exact certainty_equivalence_regimes M hM hf1 hL hψ hψd hmean (sR r)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Y × ℝ × ℝ, γ = fun s => (ybar, 0, s) := ⟨_, rfl⟩
  have hγd : ∀ s, HasDerivAt γ e3 s := fun s => by
    rw [hγ, he3]
    exact (hasDerivAt_const s ybar).prodMk ((hasDerivAt_const s (0 : ℝ)).prodMk (hasDerivAt_id s))
  have hγ0 : γ 0 = pbar ybar := by rw [hγ]; rfl
  have hγt : Tendsto γ (𝓝 0) (𝓝 (pbar ybar)) := hγ0 ▸ (hγd 0).continuousAt.tendsto
  obtain ⟨u, hu⟩ : ∃ u : ℝ → adSub (R := R) Y, u = fun s => ψ (γ s) := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ → adSub (R := R) Y, u1 = fun s => fderiv ℝ ψ (γ s) e3 :=
    ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2 : adSub (R := R) Y,
      u2 = fderiv ℝ (fderiv ℝ ψ) (pbar ybar) e3 e3 := ⟨_, rfl⟩
  have hud : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt u (u1 s) s := by
    rw [hu, hu1]
    filter_upwards [hγt.eventually hψev] with s hs
    exact hs.comp_hasDerivAt s (hγd s)
  have hu1d : HasDerivAt u1 u2 0 := by
    have hF : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (γ 0) := by
      rw [hγ0]; exact hψF1
    have h0 := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Y × ℝ × ℝ)
      (E := (Y × ℝ × ℝ) →L[ℝ] adSub (R := R) Y) (f := γ) (l := fderiv ℝ ψ) (0 : ℝ) hF (hγd 0)
    have h1 := (ContinuousLinearMap.apply ℝ (adSub (R := R) Y) e3).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h0
    rw [hu1, hu2]
    exact h1
  have hun : ∀ n, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s => ev n (u s)) (ev n (u1 s)) s :=
    fun n => hud.mono fun s hs => (ev n).hasFDerivAt.comp_hasDerivAt s hs
  have hun1 : ∀ n, HasDerivAt (fun s => ev n (u1 s)) (ev n u2) 0 := fun n =>
    (ev n).hasFDerivAt.comp_hasDerivAt 0 hu1d
  have hu0 : u 0 = SmoothInSigmaMeasure.MModel.ubar ybar := by
    rw [hu]; simp only [hγ0]; exact hψ.base
  have hu10 : u1 0 = fderiv ℝ ψ (pbar ybar) e3 := by rw [hu1]; simp only [hγ0]
  have hR0 : ∀ r, ev (0, sR r) u2 = fderiv ℝ (fderiv ℝ (policyR ψ r)) (pbar ybar) e3 e3 :=
    fun r => by
    have hF : ∀ᶠ x in 𝓝 (γ 0), HasFDerivAt (policyR ψ r) (fderiv ℝ (policyR ψ r) x) x := by
      rw [hγ0]; exact hgev r
    have hF1 : HasFDerivAt (fderiv ℝ (policyR ψ r))
        (fderiv ℝ (fderiv ℝ (policyR ψ r)) (pbar ybar)) (γ 0) := by rw [hγ0]; exact hgF1 r
    have := SmoothInSigma.Model.secondDeriv_comp (F := policyR ψ r) (a := γ)
      (a1 := fun _ => e3) (a2 := 0) (y := fun s => ev (0, sR r) (u s))
      (y1 := fun s => ev (0, sR r) (u1 s)) hF hF1
      (Eventually.of_forall hγd) (hasDerivAt_const 0 e3) (hun _) (hun1 _)
      (Eventually.of_forall fun s => by rw [hu]; rfl)
    rw [this, map_zero, add_zero]
  have h1root : ∀ r, ev (0, sR r) (u1 0) = 0 := fun r => by
    rw [hu10, ← hce r, hg'eq r]
    rfl
  have h1child : ∀ (r' : R) (e : ℝ), ev (1, consH (r', e) (sR r0)) (u1 0) =
      clipB M.bound e • fderiv ℝ (policyR ψ r') (pbar ybar) e2 := fun r' e => by
    have h := markov_derivR M r0 r' hψ hψd (hgd r') e3 e
    rw [hu10]
    change ((fderiv ℝ ψ (pbar ybar) e3 : adSub (R := R) Y) : Bd (ℕ × Hist R) Y)
      (1, consH (r', e) (sR r0)) = _
    rw [h]
    have h0 : ((fderiv ℝ ψ (pbar ybar) e3 : adSub (R := R) Y) : Bd (ℕ × Hist R) Y)
        (0, sR r0) = 0 := by rw [← hu10]; exact h1root r0
    rw [h0, he3]
    simp only [one_mul]
    rw [SmoothInSigma.Model.clm_triple, ← he3, hce r', smul_zero, add_zero, Prod.mk_zero_zero,
      Prod.mk_zero_zero, map_zero, zero_add, show ((0 : Y), clipB M.bound e, (0 : ℝ)) =
        clipB M.bound e • ((0 : Y), (1 : ℝ), (0 : ℝ)) by simp, map_smul, he2]
  have hRj : ∀ (r' : R) (e : ℝ), ev (1, consH (r', e) (sR r0)) u2 =
      fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) (0, clipB M.bound e, 1)
        (0, clipB M.bound e, 1) +
        fderiv ℝ (policyR ψ r') (pbar ybar) (ev (0, sR r0) u2, 0, 0) := fun r' e => by
    obtain ⟨b, hb⟩ : ∃ b : ℝ → Y × ℝ × ℝ, b = fun s =>
        (ev (0, sR r0) (u s), s * clipB M.bound e, s) := ⟨_, rfl⟩
    have hb0 : b 0 = pbar ybar := by
      rw [hb]
      change (ev (0, sR r0) (u 0), (0 : ℝ) * clipB M.bound e, (0 : ℝ)) = pbar ybar
      rw [hu0, zero_mul]
      rfl
    have hF : ∀ᶠ x in 𝓝 (b 0), HasFDerivAt (policyR ψ r') (fderiv ℝ (policyR ψ r') x) x := by
      rw [hb0]; exact hgev r'
    have hF1 : HasFDerivAt (fderiv ℝ (policyR ψ r'))
        (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar)) (b 0) := by rw [hb0]; exact hgF1 r'
    have hmc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s * clipB M.bound e) (clipB M.bound e) s :=
      fun s => by simpa using (hasDerivAt_id s).mul_const (clipB M.bound e)
    have ha : ∀ᶠ s in 𝓝 (0 : ℝ),
        HasDerivAt b (ev (0, sR r0) (u1 s), clipB M.bound e, 1) s := by
      rw [hb]
      exact (hun (0, sR r0)).mono fun s hs => hs.prodMk ((hmc s).prodMk (hasDerivAt_id s))
    have ha1 : HasDerivAt (fun s => (ev (0, sR r0) (u1 s), clipB M.bound e, (1 : ℝ)))
        (ev (0, sR r0) u2, 0, 0) 0 :=
      (hun1 _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
    have heq : ∀ᶠ s in 𝓝 (0 : ℝ),
        ev (1, consH (r', e) (sR r0)) (u s) = policyR ψ r' (b s) := by
      filter_upwards [hγt.eventually (markovR M hψ)] with s hs
      have h := hs r0 r' e
      rw [hγ] at h
      rw [hb, hu, hγ]
      exact h
    have := SmoothInSigma.Model.secondDeriv_comp hF hF1 ha ha1 (hun _) (hun1 _) heq
    rw [this, hb0, h1root r0]
  have hγc : ContDiffAt ℝ 2 γ 0 := by rw [hγ]; fun_prop
  have huc : ContDiffAt ℝ 2 u 0 := by
    rw [hu]
    have : ContDiffAt ℝ 2 ψ (γ 0) := by rw [hγ0]; exact hψ2
    exact this.comp 0 hγc
  obtain ⟨cf, hcf⟩ : ∃ cf : ℝ → adSub (R := R) (Y × Y × Y × ℝ × ℝ),
      cf = fun s => M.WmapL (γ s, u s) := ⟨_, rfl⟩
  have hcc : ContDiffAt ℝ 2 cf 0 := by
    rw [hcf]
    exact (M.WmapL (R := R)).contDiff.contDiffAt.comp 0 (hγc.prodMk huc)
  obtain ⟨H, hH⟩ : ∃ H : ℝ → adSub (R := R) Z, H = fun s => M.NmS hf.continuous (cf s) :=
    ⟨_, rfl⟩
  have hHc : ContDiffAt ℝ 2 H 0 := by
    rw [hH]
    exact (M.contDiff_NmS hf).contDiffAt.comp 0 hcc
  have hHd : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt H (fderiv ℝ H s 1) s :=
    (hHc.eventually (by simp)).mono fun s hs =>
      (hs.differentiableAt (by norm_num)).hasFDerivAt.hasDerivAt
  have hFD : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) 0) 0 :=
    ((hHc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hH1d : HasDerivAt (fun s => fderiv ℝ H s 1) (fderiv ℝ (fderiv ℝ H) 0 1 1) 0 := by
    have h0 : HasDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) 0 1) 0 := hFD.hasDerivAt
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ →L[ℝ] adSub (R := R) Z)
      (E := adSub (R := R) Z) (f := fderiv ℝ H)
      (l := ContinuousLinearMap.apply ℝ (adSub (R := R) Z) (1 : ℝ)) (0 : ℝ)
      (ContinuousLinearMap.apply ℝ (adSub (R := R) Z) (1 : ℝ)).hasFDerivAt h0
  have hzero : ∀ᶠ s in 𝓝 (0 : ℝ), M.AvgL hM (H s) = 0 := by
    filter_upwards [hγt.eventually hψ.solves] with s hs
    have := (M.Phi_eq_zero_iff hM hf.continuous (γ s) (ψ (γ s))).2 hs
    rw [hH, hcf, hu]
    exact this
  have hAvg : M.AvgL hM (fderiv ℝ (fderiv ℝ H) 0 1 1) = 0 := by
    have := SmoothInSigma.Model.secondDeriv_comp (F := fun x => M.AvgL hM x)
      (F1 := fun _ => M.AvgL hM) (F2 := 0) (a := H) (a1 := fun s => fderiv ℝ H s 1)
      (a2 := fderiv ℝ (fderiv ℝ H) 0 1 1) (y := fun _ => (0 : adSub (R := R) Z))
      (y1 := fun _ => 0) (y2 := 0) (Eventually.of_forall fun x => (M.AvgL hM).hasFDerivAt)
      (hasFDerivAt_const _ _) hHd hH1d (Eventually.of_forall fun s => hasDerivAt_const s _)
      (hasDerivAt_const _ _) (hzero.mono fun s hs => hs.symm)
    simpa using this.symm
  set f2 := fderiv ℝ (fderiv ℝ M.f) (zbar ybar) with hf2
  have hnode : ∀ (r' : R) (e : ℝ), evZ (1, consH (r', e) (sR r0)) (fderiv ℝ (fderiv ℝ H) 0 1 1) =
      f2 (ev (1, consH (r', e) (sR r0)) (u1 0), ev (0, sR r0) (u1 0), 0, 0, clipB M.bound e)
        (ev (1, consH (r', e) (sR r0)) (u1 0), ev (0, sR r0) (u1 0), 0, 0, clipB M.bound e) +
      fderiv ℝ M.f (zbar ybar) (ev (1, consH (r', e) (sR r0)) u2, ev (0, sR r0) u2, 0, 0, 0) :=
    fun r' e => by
    have hmc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s * clipB M.bound e) (clipB M.bound e) s :=
      fun s => by simpa using (hasDerivAt_id s).mul_const (clipB M.bound e)
    have hae : (fun s => evW (1, consH (r', e) (sR r0)) (cf s)) = fun s =>
        (ev (1, consH (r', e) (sR r0)) (u s), ev (0, sR r0) (u s), ybar, (0 : ℝ),
          s * clipB M.bound e) := by
      funext s
      rw [hcf, hγ]
      rfl
    have ha0 : (fun s => (ev (1, consH (r', e) (sR r0)) (u s), ev (0, sR r0) (u s), ybar, (0 : ℝ),
        s * clipB M.bound e)) 0 = zbar ybar := by
      simp only [zero_mul]
      rw [hu0]
      rfl
    have hF1 : HasFDerivAt (fderiv ℝ M.f) f2 ((fun s => (ev (1, consH (r', e) (sR r0)) (u s),
        ev (0, sR r0) (u s), ybar, (0 : ℝ), s * clipB M.bound e)) 0) := by
      rw [ha0]; exact hfF1
    have := SmoothInSigma.Model.secondDeriv_comp (F := M.f) (F1 := fderiv ℝ M.f) (F2 := f2)
      (a := fun s => (ev (1, consH (r', e) (sR r0)) (u s), ev (0, sR r0) (u s), ybar, (0 : ℝ),
        s * clipB M.bound e))
      (a1 := fun s => (ev (1, consH (r', e) (sR r0)) (u1 s), ev (0, sR r0) (u1 s), (0 : Y),
        (0 : ℝ), clipB M.bound e))
      (a2 := (ev (1, consH (r', e) (sR r0)) u2, ev (0, sR r0) u2, (0 : Y), (0 : ℝ), (0 : ℝ)))
      (y := fun s => evZ (1, consH (r', e) (sR r0)) (H s))
      (y1 := fun s => evZ (1, consH (r', e) (sR r0)) (fderiv ℝ H s 1))
      (Eventually.of_forall fun x => hfd x) hF1
      (((hun _).and (hun _)).mono fun s hs => hs.1.prodMk (hs.2.prodMk
        ((hasDerivAt_const s ybar).prodMk ((hasDerivAt_const s (0 : ℝ)).prodMk (hmc s)))))
      ((hun1 _).prodMk ((hun1 _).prodMk ((hasDerivAt_const _ _).prodMk
        ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _)))))
      (hHd.mono fun s hs => (evZ _).hasFDerivAt.comp_hasDerivAt s hs)
      ((evZ _).hasFDerivAt.comp_hasDerivAt 0 hH1d)
      (Eventually.of_forall fun s => by
        rw [← congrFun hae s, hH]
        rfl)
    rw [this, show (ev (1, consH (r', e) (sR r0)) (u 0), ev (0, sR r0) (u 0), ybar, (0 : ℝ),
      0 * clipB M.bound e) = zbar ybar from ha0]
  have hroot := congrArg (fun w : adSub (R := R) Z => (w : Bd (ℕ × Hist R) Z) (0, sR r0)) hAvg
  simp only [SmoothInSigmaMeasure.MModel.AvgL_apply, SmoothInSigmaMeasure.MModel.avgFun] at hroot
  have hint : ∑ r', M.trans r0 r' • ∫ e, evZ (1, consH (r', e) (sR r0))
      (fderiv ℝ (fderiv ℝ H) 0 1 1) ∂(M.law r' : Measure ℝ) = 0 := by
    simp only [ZeroMemClass.coe_zero] at hroot
    exact hroot
  have hsplit : ∀ c : ℝ, ((0 : Y), c, (1 : ℝ)) = c • e2 + e3 :=
    fun c => by rw [he3, he2]; ext <;> simp
  have hz : ∀ (c : ℝ) (g : Y), ((c • g, (0 : Y), (0 : Y), (0 : ℝ), c) : Y × Y × Y × ℝ × ℝ) =
      c • ((g, (0 : Y), (0 : Y), (0 : ℝ), (1 : ℝ)) : Y × Y × Y × ℝ × ℝ) := fun c g => by
    ext <;> simp
  have hpt : ∀ (r' : R) (e : ℝ), evZ (1, consH (r', e) (sR r0)) (fderiv ℝ (fderiv ℝ H) 0 1 1) =
      (M.dA ybar (fderiv ℝ (policyR ψ r') (pbar ybar)
          (fderiv ℝ (fderiv ℝ (policyR ψ r0)) (pbar ybar) e3 e3, 0, 0)) +
        M.dA ybar (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) e3 e3) +
        M.dB ybar (fderiv ℝ (fderiv ℝ (policyR ψ r0)) (pbar ybar) e3 e3)) +
      clipB M.bound e • M.dA ybar (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) e2 e3 +
        fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) e3 e2) +
      clipB M.bound e ^ 2 • (M.dA ybar (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) e2 e2) +
        f2 (fderiv ℝ (policyR ψ r') (pbar ybar) e2, 0, 0, 0, 1)
          (fderiv ℝ (policyR ψ r') (pbar ybar) e2, 0, 0, 0, 1)) := fun r' e => by
    rw [hnode r' e, h1child r' e, h1root r0, hRj r' e, hR0 r0, hsplit (clipB M.bound e), hz]
    simp only [SmoothInSigmaMeasure.MModel.fderiv_f_apply, map_zero, add_zero, map_add,
      map_smul, add_apply, smul_apply]
    module
  have hI : ∀ r' : R, ∫ e, evZ (1, consH (r', e) (sR r0)) (fderiv ℝ (fderiv ℝ H) 0 1 1)
      ∂(M.law r' : Measure ℝ) =
      (M.dA ybar (fderiv ℝ (policyR ψ r') (pbar ybar)
          (fderiv ℝ (fderiv ℝ (policyR ψ r0)) (pbar ybar) e3 e3, 0, 0)) +
        M.dA ybar (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) e3 e3) +
        M.dB ybar (fderiv ℝ (fderiv ℝ (policyR ψ r0)) (pbar ybar) e3 e3)) +
      (∫ e, clipB M.bound e ^ 2 ∂(M.law r' : Measure ℝ)) •
        (M.dA ybar (fderiv ℝ (fderiv ℝ (policyR ψ r')) (pbar ybar) e2 e2) +
        f2 (fderiv ℝ (policyR ψ r') (pbar ybar) e2, 0, 0, 0, 1)
          (fderiv ℝ (policyR ψ r') (pbar ybar) e2, 0, 0, 0, 1)) := fun r' => by
    rw [integral_congr_ae (Eventually.of_forall (hpt r')),
      SmoothInSigmaMeasure.integral_quad_clip, hmean r', zero_smul, add_zero]
  simp only [hI] at hint
  simp only [he3] at hint ⊢
  exact hint

end Woodford.StabilizationWelfare.SmoothInSigmaRegimes
