/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasurePath

/-!
# Local uniqueness of the perturbation equilibrium on the probability space

Woodford (2003), *Interest and Prices*, Chapter 6, Appendix E.2 (p. 695), on the GENUINE i.i.d.
probability space `(ℕ → ℝ, ν^ℕ)` of `ExpectationsMeasureIID`.

`SmoothInSigmaMeasure` proves uniqueness among solutions on the history space; here uniqueness
is proved among ARBITRARY adapted, essentially bounded processes that solve the model almost
surely with Mathlib's `condExp`. The transfer runs through the freezing lemma `condExp_freeze`:

1. Doob–Dynkin puts the process on shock prefixes `Fin (t+1) → ℝ` (`exists_prefix_version`),
   whose law is `Measure.pi` (`map_pref`); the residual of the model is then a function of the
   prefix (`resid`), zero a.s. (`ae_resid_zero`).
2. Prefixes from which the conditions hold now and almost surely forever are kept (`safeD`,
   `goodS`, via the `β`-recursion `betaB` of conditional violation probabilities); they have
   full measure (`ae_goodS`).
3. Off the good prefixes the candidate is repaired by the clamped policy function (`clampY`,
   `repF`), giving a history-space solution to which the uniqueness of `ψ` applies.

## Main results

* `pref`, `vecOf`, `histV`, `integral_pi_snoc`, `measurePreserving_init`: prefix space.
* `resid`, `exists_prefix_version`, `ae_resid_zero`: the model on prefixes.
* `betaB`, `safeD`, `goodS`, `ae_goodS`: the good prefixes.
* `clampY`, `repF`, `repF_good`, `stronglyMeasurable_repF`, `finMem_repF`: the repair.
* `unique_ae`: every adapted process a.s. within `δ` of `ȳ` that solves the model a.s. equals
  the equilibrium `y_t = ψ(p)(t, h_t)` a.s. at every date.
* `yproc_solves`, `exists_unique_equilibrium_iid`: existence, uniqueness among a.s. solutions
  and `Cᵏ` dependence on the probability space.
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaUnique

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID
open SmoothInSigmaMeasure (Hist consH tailH consH_zero consH_succ tailH_consH adSub clipB
  clipB_of_abs_le abs_clipB_le continuous_clipB measurable_consH measurable_tailH MModel)
open SmoothInSigmaMeasure.MModel (lagF policyU sNil ubar)
open SmoothInSigmaMeasurePath (histOf histOf_apply yproc condExp_freeze)
open SmoothInSigma (Bd mkBd mkBd_apply norm_apply_le norm_le_of_forall pbar zbar)

/-! ## Shock prefixes -/

/-- Woodford (2003), App. E.2: the shocks `(ε_0, …, ε_t)` of a path, oldest first. -/
def pref (t : ℕ) (ω : ℕ → ℝ) : Fin (t + 1) → ℝ := fun j => ω j

/-- Woodford (2003), App. E.2: the prefix map is measurable. -/
theorem measurable_pref (t : ℕ) : Measurable (pref t) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- Woodford (2003), App. E.2: the prefix at date `t` is known at date `t`. -/
theorem measurable_pref_F (ν : ProbabilityMeasure ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (pref t) :=
  (measurable_pi_iff.mpr fun j : Fin (t + 1) =>
    measurable_pi_apply (⟨j, Nat.lt_succ_iff.mp j.2⟩ : Set.Iic t)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t))

/-- Woodford (2003), App. E.2 (**the law of the shock prefix**): under `ν^ℕ` the prefix
`(ε_0, …, ε_t)` has law `ν^{t+1}`. -/
theorem map_pref (ν : ProbabilityMeasure ℝ) (t : ℕ) :
    (iidSystem ν).μ.map (pref t) = Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_pref t) (MeasurableSet.univ_pi hs)]
  set S : ℕ → Set ℝ := fun n => if h : n < t + 1 then s ⟨n, h⟩ else Set.univ with hS
  have hset : pref t ⁻¹' Set.univ.pi s = ((Finset.range (t + 1) : Finset ℕ) : Set ℕ).pi S := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.coe_range,
      Set.mem_Iio, pref, hS]
    constructor
    · intro h n hn
      simp only [hn, ↓reduceDIte]
      exact h ⟨n, hn⟩
    · intro h j
      have := h j j.2
      simpa [j.2] using this
  rw [hset]
  change Measure.infinitePi (fun _ : ℕ => (ν : Measure ℝ)) _ = _
  refine (Measure.infinitePi_pi (μ := fun _ : ℕ => (ν : Measure ℝ)) (s := Finset.range (t + 1))
    (t := S) (fun n _ => by
      simp only [hS]; split_ifs
      · exact hs _
      · exact MeasurableSet.univ)).trans ?_
  rw [← Fin.prod_univ_eq_prod_range (fun n => (ν : Measure ℝ) (S n)) (t + 1)]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [hS, Nat.lt_succ_iff.mp j.2]

/-! ## Histories of prefixes -/

/-- Woodford (2003), App. E.2: the history of a shock prefix (entry `i` is `ε_{t−i}`). -/
def histV (t : ℕ) (v : Fin (t + 1) → ℝ) : Hist Unit := fun i =>
  ((), if h : i ≤ t then v ⟨t - i, by omega⟩ else 0)

/-- Woodford (2003), App. E.2: the realised history is the history of the realised prefix. -/
theorem histOf_eq_histV (t : ℕ) (ω : ℕ → ℝ) : histOf t ω = histV t (pref t ω) := by
  funext i
  rw [histOf_apply]
  by_cases h : i ≤ t
  · simp [histV, h, pref]
  · simp [histV, h]

/-- Woodford (2003), App. E.2: the prefix `v` read back from a history, with root shock `c`
(oldest first; `v_0 = c`, `v_j = ε_j` from the history for `j ≥ 1`). -/
def vecOf (c : ℝ) (t : ℕ) (s : Hist Unit) : Fin (t + 1) → ℝ := fun j =>
  if (j : ℕ) = 0 then c else (s (t - j)).2

/-- Woodford (2003), App. E.2: reading the realised history back gives the realised prefix. -/
theorem vecOf_histOf (t : ℕ) (ω : ℕ → ℝ) : vecOf (ω 0) t (histOf t ω) = pref t ω := by
  funext j
  by_cases h : (j : ℕ) = 0
  · simp [vecOf, h, pref]
  · simp only [vecOf, h, ↓reduceIte, histOf_apply, pref]
    have : t - (t - (j : ℕ)) = j := by omega
    simp [this]

/-- Woodford (2003), App. E.2: the prefix of a successor history appends the new shock. -/
theorem vecOf_cons (c : ℝ) (t : ℕ) (s : Hist Unit) (e : ℝ) :
    vecOf c (t + 1) (consH ((), e) s) = Fin.snoc (vecOf c t s) e := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [vecOf]
  · rw [Fin.snoc_castSucc]
    by_cases h : (i : ℕ) = 0
    · simp [vecOf, h]
    · have hi : (i : ℕ) ≤ t := by omega
      have : t + 1 - (i : ℕ) = (t - (i : ℕ)) + 1 := by omega
      simp [vecOf, h, this]

/-- Woodford (2003), App. E.2: the prefix of the predecessor history drops the newest shock. -/
theorem vecOf_tail (c : ℝ) (t : ℕ) (s : Hist Unit) :
    vecOf c t (tailH s) = Fin.init (vecOf c (t + 1) s) := by
  funext j
  by_cases h : (j : ℕ) = 0
  · simp [vecOf, Fin.init, h]
  · have : t + 1 - (j : ℕ) = (t - (j : ℕ)) + 1 := by omega
    simp [vecOf, Fin.init, h, this, tailH]

/-- Woodford (2003), App. E.2: the prefix of a history depends only on its first `t` entries. -/
theorem vecOf_congr (c : ℝ) {t : ℕ} {s s' : Hist Unit} (h : ∀ i < t, s i = s' i) :
    vecOf c t s = vecOf c t s' := by
  funext j
  by_cases hj : (j : ℕ) = 0
  · simp [vecOf, hj]
  · simp only [vecOf, hj, ↓reduceIte]
    rw [h _ (by omega)]

/-- Woodford (2003), App. E.2: reading the prefix is measurable. -/
theorem measurable_vecOf (c : ℝ) (t : ℕ) : Measurable (vecOf c t) := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases h : (j : ℕ) = 0
  · simp only [vecOf, h, ↓reduceIte]
    exact measurable_const
  · simp only [vecOf, h, ↓reduceIte]
    exact measurable_snd.comp (measurable_pi_apply _)

/-! ## Integrating out the newest shock of a prefix -/

/-- Woodford (2003), App. E.2 (Fubini on prefixes): `∫ g dν^{n+1} = ∫∫ g(v ++ e) dν(e) dν^n(v)`
for bounded measurable `g`. -/
theorem integral_pi_snoc {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (ν : ProbabilityMeasure ℝ) {n : ℕ} {g : (Fin (n + 1) → ℝ) → V} (hg : StronglyMeasurable g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    ∫ x, g x ∂(Measure.pi fun _ => (ν : Measure ℝ)) =
      ∫ x, ∫ e, g (Fin.snoc x e) ∂(ν : Measure ℝ) ∂(Measure.pi fun _ => (ν : Measure ℝ)) := by
  have h := measurePreserving_piFinSuccAbove (α := fun _ => ℝ)
    (fun _ : Fin (n + 1) => (ν : Measure ℝ)) (Fin.last n)
  have h1 : ∫ x, g x ∂(Measure.pi fun _ => (ν : Measure ℝ)) =
      ∫ x, g ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm
        (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n) x))
        ∂(Measure.pi fun _ => (ν : Measure ℝ)) := by
    simp only [MeasurableEquiv.symm_apply_apply]
  rw [h1, h.integral_comp'
    (fun y => g ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm y))]
  have hm : StronglyMeasurable fun y : ℝ × (Fin n → ℝ) =>
      g ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm y) :=
    hg.comp_measurable (MeasurableEquiv.measurable _)
  rw [integral_prod_symm _ (Integrable.of_bound hm.aestronglyMeasurable C
    (Eventually.of_forall fun y => hC _))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  refine congrArg g ?_
  simp [MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv]

/-- Woodford (2003), App. E.2: dropping the newest shock preserves the product law. -/
theorem measurePreserving_init (ν : ProbabilityMeasure ℝ) (n : ℕ) :
    MeasurePreserving (fun x : Fin (n + 1) → ℝ => Fin.init x)
      (Measure.pi fun _ => (ν : Measure ℝ)) (Measure.pi fun _ => (ν : Measure ℝ)) := by
  have h := measurePreserving_piFinSuccAbove (α := fun _ => ℝ)
    (fun _ : Fin (n + 1) => (ν : Measure ℝ)) (Fin.last n)
  have h2 := (measurePreserving_snd (μ := (ν : Measure ℝ))
    (ν := Measure.pi fun _ : Fin n => (ν : Measure ℝ))).comp h
  convert h2 using 1
  funext x
  simp [MeasurableEquiv.piFinSuccAbove]

/-- Woodford (2003), App. E.2: appending the newest shock is measurable. -/
theorem measurable_snoc (n : ℕ) :
    Measurable fun q : (Fin n → ℝ) × ℝ => (Fin.snoc q.1 q.2 : Fin (n + 1) → ℝ) := by
  have h : (fun q : (Fin n → ℝ) × ℝ => (Fin.snoc q.1 q.2 : Fin (n + 1) → ℝ)) =
      fun q => (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm (q.2, q.1) := by
    funext q
    simp [MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv]
  rw [h]
  exact (MeasurableEquiv.measurable _).comp (measurable_snd.prodMk measurable_fst)

/-- Woodford (2003), App. E.2: dropping the newest shock is measurable. -/
theorem measurable_init (n : ℕ) : Measurable fun v : Fin (n + 1) → ℝ => Fin.init v :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-! ## The equilibrium conditions on prefixes -/

variable {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

/-- Woodford (2003), App. E.2: the predecessor value on prefixes, `y_{−1}` at date `0`. -/
def lagv (p : Y × ℝ × ℝ) (φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y) :
    (t : ℕ) → (Fin (t + 1) → ℝ) → Y
  | 0, _ => p.1
  | t + 1, v => φ t (Fin.init v)

/-- Woodford (2003), App. E.2: the current scaled shock on prefixes, `s₀` at date `0`. -/
def enowv (B : ℝ) (p : Y × ℝ × ℝ) : (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ
  | 0, _ => p.2.1
  | t + 1, v => p.2.2 * clipB B (v (Fin.last (t + 1)))

/-- Woodford (2003), App. E.2, p. 695: the residual of the equilibrium condition at the prefix
`v` and the next shock `e`, for a candidate `φ` given on prefixes. -/
def resid (N : MModel Unit Y Z) (p : Y × ℝ × ℝ) (φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y)
    (t : ℕ) (v : Fin (t + 1) → ℝ) (e : ℝ) : Z :=
  N.f (φ (t + 1) (Fin.snoc v e), φ t v, lagv p φ t v, enowv N.bound p t v,
    p.2.2 * clipB N.bound e)

omit [NormedSpace ℝ Y] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the residual is jointly measurable in the prefix and the shock. -/
theorem stronglyMeasurable_resid (N : MModel Unit Y Z) (hc : Continuous N.f) (p : Y × ℝ × ℝ)
    {φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y} (hφ : ∀ t, StronglyMeasurable (φ t)) (t : ℕ) :
    StronglyMeasurable fun q : (Fin (t + 1) → ℝ) × ℝ => resid N p φ t q.1 q.2 := by
  refine hc.comp_stronglyMeasurable ?_
  refine ((hφ (t + 1)).comp_measurable (measurable_snoc (t + 1))).prodMk
    (((hφ t).comp_measurable measurable_fst).prodMk (StronglyMeasurable.prodMk ?_
      (StronglyMeasurable.prodMk ?_ ?_)))
  · cases t with
    | zero => exact stronglyMeasurable_const
    | succ k => exact (hφ k).comp_measurable ((measurable_init (k + 1)).comp measurable_fst)
  · cases t with
    | zero => exact stronglyMeasurable_const
    | succ k =>
      exact (measurable_const.mul ((continuous_clipB N.bound).measurable.comp
        ((measurable_pi_apply _).comp measurable_fst))).stronglyMeasurable
  · exact (measurable_const.mul ((continuous_clipB N.bound).measurable.comp
      measurable_snd)).stronglyMeasurable

omit [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the residual is bounded when the candidate stays in a ball
around `ȳ` (continuity of `f` on a compact set). -/
theorem resid_bdd [FiniteDimensional ℝ Y] (N : MModel Unit Y Z) (hc : Continuous N.f)
    (p : Y × ℝ × ℝ) {φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y} {ybar : Y} {δ : ℝ}
    (hφ : ∀ t v, ‖φ t v - ybar‖ ≤ δ) :
    ∃ C, ∀ t v e, ‖resid N p φ t v e‖ ≤ C := by
  set R := δ + ‖p.1 - ybar‖ + |p.2.1| + |p.2.2| * |N.bound| with hR
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hφ 0 0)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (zbar ybar : Y × Y × Y × ℝ × ℝ)
    R).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun t v e => hC _ ?_⟩
  have hcl : ∀ x : ℝ, |p.2.2 * clipB N.bound x| ≤ |p.2.2| * |N.bound| := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_clipB_le _ _) (abs_nonneg _)
  have h1 : ‖φ (t + 1) (Fin.snoc v e) - ybar‖ ≤ R := (hφ _ _).trans (by
    have := abs_nonneg p.2.1; have := norm_nonneg (p.1 - ybar)
    have := mul_nonneg (abs_nonneg p.2.2) (abs_nonneg N.bound); linarith)
  have h2 : ‖φ t v - ybar‖ ≤ R := (hφ _ _).trans (by
    have := abs_nonneg p.2.1; have := norm_nonneg (p.1 - ybar)
    have := mul_nonneg (abs_nonneg p.2.2) (abs_nonneg N.bound); linarith)
  have h3 : ‖lagv p φ t v - ybar‖ ≤ R := by
    cases t with
    | zero =>
      have := abs_nonneg p.2.1
      have := mul_nonneg (abs_nonneg p.2.2) (abs_nonneg N.bound)
      simp only [lagv]; linarith
    | succ k =>
      refine (hφ _ _).trans ?_
      have := abs_nonneg p.2.1; have := norm_nonneg (p.1 - ybar)
      have := mul_nonneg (abs_nonneg p.2.2) (abs_nonneg N.bound); linarith
  have h4 : ‖enowv N.bound p t v‖ ≤ R := by
    rw [Real.norm_eq_abs]
    cases t with
    | zero =>
      have := norm_nonneg (p.1 - ybar)
      have := mul_nonneg (abs_nonneg p.2.2) (abs_nonneg N.bound)
      simp only [enowv]; linarith
    | succ k =>
      refine (hcl _).trans ?_
      have := abs_nonneg p.2.1; have := norm_nonneg (p.1 - ybar); linarith
  have h5 : ‖p.2.2 * clipB N.bound e‖ ≤ R := by
    rw [Real.norm_eq_abs]
    refine (hcl _).trans ?_
    have := abs_nonneg p.2.1; have := norm_nonneg (p.1 - ybar); linarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [zbar, Prod.mk_sub_mk, sub_zero]
  exact norm_prod_le_iff.2 ⟨h1, norm_prod_le_iff.2 ⟨h2, norm_prod_le_iff.2 ⟨h3,
    norm_prod_le_iff.2 ⟨h4, h5⟩⟩⟩⟩

/-! ## Path processes and their prefix versions -/

/-- Woodford (2003), App. E.2: the predecessor value along a path process, `y_{−1}` at date
`0`. -/
def zlag (p : Y × ℝ × ℝ) (z : ℕ → (ℕ → ℝ) → Y) : ℕ → (ℕ → ℝ) → Y
  | 0 => fun _ => p.1
  | t + 1 => z t

/-- Woodford (2003), App. E.2: the current scaled shock along a path, `s₀` at date `0` and
`σ clip(ε_t)` later. -/
def zenow (B : ℝ) (p : Y × ℝ × ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => p.2.1
  | t + 1 => fun ω => p.2.2 * clipB B (ω (t + 1))

omit [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2 (**Doob–Dynkin with a ball**): an adapted process that stays a.s.
within `δ` of `ȳ` has a version `φ_t(ε_0, …, ε_t)`, measurable in the prefix and within `δ` of
`ȳ` everywhere. -/
theorem exists_prefix_version [CompleteSpace Y] (ν : ProbabilityMeasure ℝ)
    {z : ℕ → (ℕ → ℝ) → Y} (hz : ∀ t, StronglyMeasurable[(iidSystem ν).𝓕 t] (z t)) {ybar : Y}
    {δ : ℝ} (hδ : 0 ≤ δ) (hzb : ∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, ‖z t ω - ybar‖ ≤ δ) :
    ∃ φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y, (∀ t, StronglyMeasurable (φ t)) ∧
      (∀ t v, ‖φ t v - ybar‖ ≤ δ) ∧
      ∀ t, z t =ᵐ[(iidSystem ν).μ] fun ω => φ t (pref t ω) := by
  have key : ∀ t, ∃ φt : (Fin (t + 1) → ℝ) → Y, StronglyMeasurable φt ∧
      (∀ v, ‖φt v - ybar‖ ≤ δ) ∧ z t =ᵐ[(iidSystem ν).μ] fun ω => φt (pref t ω) := by
    intro t
    set zc : (ℕ → ℝ) → Y := fun ω => if ‖z t ω - ybar‖ ≤ δ then z t ω else ybar with hzc
    have hm : StronglyMeasurable[(iidSystem ν).𝓕 t] zc := by
      refine StronglyMeasurable.ite ?_ (hz t) stronglyMeasurable_const
      exact measurableSet_le ((hz t).sub stronglyMeasurable_const).norm.measurable
        measurable_const
    have hm' : StronglyMeasurable[MeasurableSpace.comap
        (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t) MeasurableSpace.pi] zc := hm
    obtain ⟨h, hh, hzh⟩ := hm'.exists_eq_measurable_comp
    refine ⟨fun v => h (fun j : Set.Iic t => v ⟨j, Nat.lt_succ_of_le j.2⟩), ?_, fun v => ?_, ?_⟩
    · exact hh.comp_measurable (measurable_pi_iff.mpr fun j => measurable_pi_apply _)
    · set ω : ℕ → ℝ := fun n => if hn : n < t + 1 then v ⟨n, hn⟩ else 0 with hω
      have hr : (fun j : Set.Iic t => v ⟨j, Nat.lt_succ_of_le j.2⟩) =
          Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω := by
        funext j
        have hj : ¬ t < (j : ℕ) := not_lt.2 j.2
        simp [hω, Preorder.restrictLe, hj]
      simp only [hr]
      have := congrFun hzh ω
      simp only [Function.comp_apply] at this
      rw [← this]
      simp only [hzc]
      split_ifs with hle
      · exact hle
      · simpa using hδ
    · filter_upwards [hzb t] with ω hω
      have := congrFun hzh ω
      simp only [Function.comp_apply] at this
      rw [show (fun j : Set.Iic t => pref t ω ⟨j, Nat.lt_succ_of_le j.2⟩) =
        Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω from rfl, ← this, hzc]
      simp [hω]
  choose φ hφm hφb hφe using key
  exact ⟨φ, hφm, hφb, hφe⟩

/-- Woodford (2003), App. E.2: the prefix at `t + 1` appends `ε_{t+1}` to the prefix at `t`. -/
theorem pref_succ (t : ℕ) (ω : ℕ → ℝ) : pref (t + 1) ω = Fin.snoc (pref t ω) (ω (t + 1)) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [pref]
  · rw [Fin.snoc_castSucc]
    rfl

/-- Woodford (2003), App. E.2 (**the conditions with genuine conditional expectations become
conditions on prefixes**): if the path process `z = φ(prefix)` a.s. solves
`E_t f(z_{t+1}, z_t, z_{t−1}, e_t, σ clip(ε_{t+1})) = 0` a.s., then for `ν^{t+1}`-a.e. prefix
`v`, `∫ f(φ(v ++ e), φ(v), …) dν(e) = 0` (freezing lemma and the law of the prefix). -/
theorem ae_resid_zero [FiniteDimensional ℝ Y] [CompleteSpace Z] (ν : ProbabilityMeasure ℝ)
    (N : MModel Unit Y Z) (hc : Continuous N.f) (p : Y × ℝ × ℝ) {z : ℕ → (ℕ → ℝ) → Y}
    {φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y} (hφm : ∀ t, StronglyMeasurable (φ t)) {ybar : Y}
    {δ : ℝ} (hφb : ∀ t v, ‖φ t v - ybar‖ ≤ δ)
    (hφe : ∀ t, z t =ᵐ[(iidSystem ν).μ] fun ω => φ t (pref t ω))
    (hsol : ∀ t, (iidSystem ν).μ[fun ω => N.f (z (t + 1) ω, z t ω, zlag p z t ω,
      zenow N.bound p t ω, p.2.2 * clipB N.bound (ω (t + 1))) | (iidSystem ν).𝓕 t]
        =ᵐ[(iidSystem ν).μ] 0) (t : ℕ) :
    ∀ᵐ v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)),
      ∫ e, resid N p φ t v e ∂(ν : Measure ℝ) = 0 := by
  have hl : ∀ᵐ ω ∂(iidSystem ν).μ, zlag p z t ω = lagv p φ t (pref t ω) := by
    cases t with
    | zero => exact Eventually.of_forall fun ω => rfl
    | succ k =>
      filter_upwards [hφe k] with ω h
      exact h
  have hpath : (fun ω => N.f (z (t + 1) ω, z t ω, zlag p z t ω, zenow N.bound p t ω,
      p.2.2 * clipB N.bound (ω (t + 1)))) =ᵐ[(iidSystem ν).μ]
      fun ω => resid N p φ t (pref t ω) (ω (t + 1)) := by
    filter_upwards [hφe (t + 1), hφe t, hl] with ω h1 h2 h3
    have h4 : zenow N.bound p t ω = enowv N.bound p t (pref t ω) := by
      cases t <;> rfl
    simp only [resid, h1, h2, h3, h4, pref_succ]
  obtain ⟨C, hC⟩ := resid_bdd N hc p hφb
  have hg : StronglyMeasurable fun q : (Set.Iic t → ℝ) × ℝ =>
      resid N p φ t (fun j : Fin (t + 1) => q.1 ⟨j, Nat.lt_succ_iff.mp j.2⟩) q.2 := by
    have hmq : Measurable fun q : (Set.Iic t → ℝ) × ℝ =>
        ((fun j : Fin (t + 1) => q.1 ⟨j, Nat.lt_succ_iff.mp j.2⟩), q.2) :=
      ((measurable_pi_iff.mpr fun j => measurable_pi_apply _).comp measurable_fst).prodMk
        measurable_snd
    exact (stronglyMeasurable_resid N hc p hφm t).comp_measurable hmq
  have hfr := condExp_freeze ν t hg (C := C) (fun q => hC _ _ _)
  have h0 : ∀ᵐ ω ∂(iidSystem ν).μ, ∫ e, resid N p φ t (pref t ω) e ∂(ν : Measure ℝ) = 0 := by
    filter_upwards [hsol t, condExp_congr_ae (m := (iidSystem ν).𝓕 t) hpath, hfr]
      with ω h1 h2 h3
    have h3' : (iidSystem ν).μ[fun ω => resid N p φ t (pref t ω) (ω (t + 1)) |
        (iidSystem ν).𝓕 t] ω = ∫ e, resid N p φ t (pref t ω) e ∂(ν : Measure ℝ) := h3
    rw [← h3', ← h2, h1]
    rfl
  have hmeas : MeasurableSet {v : Fin (t + 1) → ℝ |
      ∫ e, resid N p φ t v e ∂(ν : Measure ℝ) = 0} :=
    (stronglyMeasurable_resid N hc p hφm t).integral_prod_right'.measurableSet_eq_fun
      stronglyMeasurable_const
  rw [← map_pref ν t]
  exact (ae_map_iff (measurable_pref t).aemeasurable hmeas).2 h0

/-! ## Good prefixes: the conditions hold here and almost surely at every descendant -/

/-- Woodford (2003), App. E.2: the conditional probability that the descendant `k` periods
ahead of the prefix `v` lies outside `E` (`β_0 = 1_{Eᶜ}`, `β_{k+1}(v) = ∫ β_k(v ++ e) dν`). -/
noncomputable def betaB (ν : ProbabilityMeasure ℝ) (E : (t : ℕ) → Set (Fin (t + 1) → ℝ)) :
    ℕ → (t : ℕ) → (Fin (t + 1) → ℝ) → ℝ
  | 0, t, v => (E t)ᶜ.indicator 1 v
  | k + 1, t, v => ∫ e, betaB ν E k (t + 1) (Fin.snoc v e) ∂(ν : Measure ℝ)

/-- Woodford (2003), App. E.2: `β` is a probability, `0 ≤ β ≤ 1`. -/
theorem betaB_mem (ν : ProbabilityMeasure ℝ) (E : (t : ℕ) → Set (Fin (t + 1) → ℝ)) :
    ∀ k t v, 0 ≤ betaB ν E k t v ∧ betaB ν E k t v ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro t v
    simp only [betaB]
    by_cases h : v ∈ (E t)ᶜ
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  | succ k ih =>
    intro t v
    simp only [betaB]
    refine ⟨integral_nonneg fun e => (ih _ _).1, ?_⟩
    have := norm_integral_le_of_norm_le_const (μ := (ν : Measure ℝ))
      (f := fun e => betaB ν E k (t + 1) (Fin.snoc v e)) (C := 1)
      (Eventually.of_forall fun e => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ih _ _).1]; exact (ih _ _).2)
    simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this

/-- Woodford (2003), App. E.2: `β` is measurable in the prefix. -/
theorem stronglyMeasurable_betaB (ν : ProbabilityMeasure ℝ)
    {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)} (hE : ∀ t, MeasurableSet (E t)) :
    ∀ k t, StronglyMeasurable (betaB ν E k t) := by
  intro k
  induction k with
  | zero =>
    intro t
    exact (measurable_one.indicator (hE t).compl).stronglyMeasurable
  | succ k ih =>
    intro t
    exact ((ih (t + 1)).comp_measurable (measurable_snoc (t + 1))).integral_prod_right'

/-- Woodford (2003), App. E.2: if `E` holds almost surely at every date, the expected
probability of a violation `k` periods ahead is zero. -/
theorem integral_betaB (ν : ProbabilityMeasure ℝ) {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hE : ∀ t, MeasurableSet (E t))
    (hae : ∀ t, ∀ᵐ v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)), v ∈ E t) :
    ∀ k t, ∫ v, betaB ν E k t v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)) = 0 := by
  intro k
  induction k with
  | zero =>
    intro t
    have : (fun v => betaB ν E 0 t v) =ᵐ[Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)]
        0 := by
      filter_upwards [hae t] with v hv
      simp [betaB, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hv)]
    rw [integral_congr_ae this]
    simp
  | succ k ih =>
    intro t
    have h := integral_pi_snoc ν (g := betaB ν E k (t + 1)) (stronglyMeasurable_betaB ν hE k _)
      (C := 1) (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (betaB_mem ν E k _ x).1]
        exact (betaB_mem ν E k _ x).2)
    simp only [betaB]
    rw [← h, ih (t + 1)]

/-- Woodford (2003), App. E.2: the prefixes from which a violation occurs with zero conditional
probability at every horizon. -/
def safeD (ν : ProbabilityMeasure ℝ) (E : (t : ℕ) → Set (Fin (t + 1) → ℝ)) (t : ℕ) :
    Set (Fin (t + 1) → ℝ) :=
  {v | ∀ k, betaB ν E k t v = 0}

/-- Woodford (2003), App. E.2: safe prefixes satisfy the conditions. -/
theorem safeD_sub (ν : ProbabilityMeasure ℝ) (E : (t : ℕ) → Set (Fin (t + 1) → ℝ)) {t : ℕ}
    {v : Fin (t + 1) → ℝ} (hv : v ∈ safeD ν E t) : v ∈ E t := by
  have h := hv 0
  by_contra hn
  simp [betaB, Set.indicator_of_mem (Set.mem_compl hn)] at h

/-- Woodford (2003), App. E.2: from a safe prefix, almost every successor is safe. -/
theorem safeD_snoc (ν : ProbabilityMeasure ℝ) {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hE : ∀ t, MeasurableSet (E t)) {t : ℕ} {v : Fin (t + 1) → ℝ} (hv : v ∈ safeD ν E t) :
    ∀ᵐ e ∂(ν : Measure ℝ), Fin.snoc v e ∈ safeD ν E (t + 1) := by
  refine ae_all_iff.2 fun k => ?_
  have h := hv (k + 1)
  simp only [betaB] at h
  have hi : Integrable (fun e => betaB ν E k (t + 1) (Fin.snoc v e)) (ν : Measure ℝ) :=
    Integrable.of_bound (((stronglyMeasurable_betaB ν hE k (t + 1)).comp_measurable
      ((measurable_snoc (t + 1)).comp (measurable_const.prodMk
        measurable_id))).aestronglyMeasurable) 1 (Eventually.of_forall fun e => by
        rw [Real.norm_eq_abs, abs_of_nonneg (betaB_mem ν E k _ _).1]
        exact (betaB_mem ν E k _ _).2)
  have := (integral_eq_zero_iff_of_nonneg (fun e => (betaB_mem ν E k _ _).1) hi).1 h
  filter_upwards [this] with e he
  exact he

/-- Woodford (2003), App. E.2: the safe prefixes are measurable. -/
theorem measurableSet_safeD (ν : ProbabilityMeasure ℝ) {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hE : ∀ t, MeasurableSet (E t)) (t : ℕ) : MeasurableSet (safeD ν E t) := by
  have : safeD ν E t = ⋂ k, {v | betaB ν E k t v = 0} := by
    ext v
    simp [safeD]
  rw [this]
  exact MeasurableSet.iInter fun k =>
    (stronglyMeasurable_betaB ν hE k t).measurableSet_eq_fun stronglyMeasurable_const

/-- Woodford (2003), App. E.2: almost every prefix is safe. -/
theorem ae_safeD (ν : ProbabilityMeasure ℝ) {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hE : ∀ t, MeasurableSet (E t))
    (hae : ∀ t, ∀ᵐ v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)), v ∈ E t) (t : ℕ) :
    ∀ᵐ v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)), v ∈ safeD ν E t := by
  refine ae_all_iff.2 fun k => ?_
  have hi : Integrable (betaB ν E k t) (Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)) :=
    Integrable.of_bound (stronglyMeasurable_betaB ν hE k t).aestronglyMeasurable 1
      (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (betaB_mem ν E k _ _).1]
        exact (betaB_mem ν E k _ _).2)
  have := (integral_eq_zero_iff_of_nonneg (fun v => (betaB_mem ν E k _ _).1) hi).1
    (integral_betaB ν hE hae k t)
  filter_upwards [this] with v hv
  exact hv

/-- Woodford (2003), App. E.2 (**good prefixes**): the prefix and all its ancestors are safe. -/
def goodS (ν : ProbabilityMeasure ℝ) (E : (t : ℕ) → Set (Fin (t + 1) → ℝ)) :
    (t : ℕ) → Set (Fin (t + 1) → ℝ)
  | 0 => safeD ν E 0
  | t + 1 => {v | Fin.init v ∈ goodS ν E t ∧ v ∈ safeD ν E (t + 1)}

/-- Woodford (2003), App. E.2: good prefixes are safe. -/
theorem goodS_sub (ν : ProbabilityMeasure ℝ) (E : (t : ℕ) → Set (Fin (t + 1) → ℝ)) {t : ℕ}
    {v : Fin (t + 1) → ℝ} (hv : v ∈ goodS ν E t) : v ∈ safeD ν E t := by
  cases t with
  | zero => exact hv
  | succ t => exact hv.2

/-- Woodford (2003), App. E.2: from a good prefix, almost every successor is good. -/
theorem goodS_snoc (ν : ProbabilityMeasure ℝ) {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hE : ∀ t, MeasurableSet (E t)) {t : ℕ} {v : Fin (t + 1) → ℝ} (hv : v ∈ goodS ν E t) :
    ∀ᵐ e ∂(ν : Measure ℝ), Fin.snoc v e ∈ goodS ν E (t + 1) := by
  filter_upwards [safeD_snoc ν hE (goodS_sub ν E hv)] with e he
  exact ⟨by rw [Fin.init_snoc]; exact hv, he⟩

/-- Woodford (2003), App. E.2: good prefixes are measurable. -/
theorem measurableSet_goodS (ν : ProbabilityMeasure ℝ) {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hE : ∀ t, MeasurableSet (E t)) : ∀ t, MeasurableSet (goodS ν E t) := by
  intro t
  induction t with
  | zero => exact measurableSet_safeD ν hE 0
  | succ t ih => exact ((measurable_init (t + 1)) ih).inter (measurableSet_safeD ν hE (t + 1))

/-- Woodford (2003), App. E.2: almost every prefix is good. -/
theorem ae_goodS (ν : ProbabilityMeasure ℝ) {E : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hE : ∀ t, MeasurableSet (E t))
    (hae : ∀ t, ∀ᵐ v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)), v ∈ E t) :
    ∀ t, ∀ᵐ v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)), v ∈ goodS ν E t := by
  intro t
  induction t with
  | zero => exact ae_safeD ν hE hae 0
  | succ t ih =>
    filter_upwards [(measurePreserving_init ν (t + 1)).quasiMeasurePreserving.ae ih,
      ae_safeD ν hE hae (t + 1)] with v h1 h2
    exact ⟨h1, h2⟩

/-! ## The repaired candidate -/

/-- Woodford (2003), App. E.2: the radial clamp of `y` into the closed ball of radius `r` around
`ȳ`, `ȳ + (r / max(r, ‖y − ȳ‖))(y − ȳ)`. -/
noncomputable def clampY (ybar : Y) (r : ℝ) (y : Y) : Y :=
  ybar + (r / max r ‖y - ybar‖) • (y - ybar)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the clamp is continuous. -/
theorem continuous_clampY (ybar : Y) {r : ℝ} (hr : 0 < r) : Continuous (clampY ybar r) := by
  unfold clampY
  refine continuous_const.add (Continuous.smul ?_ (continuous_id.sub continuous_const))
  exact continuous_const.div (continuous_const.max (continuous_id.sub continuous_const).norm)
    fun y => (lt_of_lt_of_le hr (le_max_left _ _)).ne'

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the clamp lands in the ball. -/
theorem norm_clampY_le (ybar : Y) {r : ℝ} (hr : 0 < r) (y : Y) :
    ‖clampY ybar r y - ybar‖ ≤ r := by
  unfold clampY
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr.le (hr.le.trans (le_max_left _ _)))]
  rw [div_mul_eq_mul_div, div_le_iff₀ (lt_of_lt_of_le hr (le_max_left _ _))]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr.le

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the clamp is the identity on the ball. -/
theorem clampY_of_le (ybar : Y) {r : ℝ} (hr : 0 < r) {y : Y} (hy : ‖y - ybar‖ ≤ r) :
    clampY ybar r y = y := by
  unfold clampY
  rw [max_eq_left hy, div_self hr.ne', one_smul, add_sub_cancel]

open Classical in
/-- Woodford (2003), App. E.2 (**the repaired candidate**): on good histories (prefix with root
shock `c` good) the prefix version `φ`, elsewhere the policy `g` applied recursively from the
last value, `x_t = g(x_{t−1}, σ clip(ε_t), σ)` (at date `0`, `g(p)`). -/
noncomputable def repF (G : (t : ℕ) → Set (Fin (t + 1) → ℝ))
    (φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y) (g : Y × ℝ × ℝ → Y) (p : Y × ℝ × ℝ) (B c : ℝ) :
    ℕ → Hist Unit → Y
  | 0, s => if vecOf c 0 s ∈ G 0 then φ 0 (vecOf c 0 s) else g p
  | t + 1, s => if vecOf c (t + 1) s ∈ G (t + 1) then φ (t + 1) (vecOf c (t + 1) s)
      else g (repF G φ g p B c t (tailH s), p.2.2 * clipB B (s 0).2, p.2.2)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: on good histories the repaired candidate is the version `φ`. -/
theorem repF_good {G : (t : ℕ) → Set (Fin (t + 1) → ℝ)} {φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y}
    {g : Y × ℝ × ℝ → Y} {p : Y × ℝ × ℝ} {B c : ℝ} {t : ℕ} {s : Hist Unit}
    (h : vecOf c t s ∈ G t) : repF G φ g p B c t s = φ t (vecOf c t s) := by
  cases t <;> simp [repF, h]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: at a bad history at date `0` the candidate is `g(p)`. -/
theorem repF_bad_zero {G : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    {φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y} {g : Y × ℝ × ℝ → Y} {p : Y × ℝ × ℝ} {B c : ℝ}
    {s : Hist Unit} (h : vecOf c 0 s ∉ G 0) : repF G φ g p B c 0 s = g p := by
  simp [repF, h]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: at a bad history later the candidate follows `g`. -/
theorem repF_bad_succ {G : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    {φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y} {g : Y × ℝ × ℝ → Y} {p : Y × ℝ × ℝ} {B c : ℝ}
    {t : ℕ} {s : Hist Unit} (h : vecOf c (t + 1) s ∉ G (t + 1)) :
    repF G φ g p B c (t + 1) s =
      g (repF G φ g p B c t (tailH s), p.2.2 * clipB B (s 0).2, p.2.2) := by
  simp [repF, h]

omit [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the repaired candidate is measurable in the history. -/
theorem stronglyMeasurable_repF {G : (t : ℕ) → Set (Fin (t + 1) → ℝ)}
    (hG : ∀ t, MeasurableSet (G t)) {φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y}
    (hφ : ∀ t, StronglyMeasurable (φ t)) {g : Y × ℝ × ℝ → Y} (hg : Continuous g)
    (p : Y × ℝ × ℝ) (B c : ℝ) : ∀ t, StronglyMeasurable (repF G φ g p B c t) := by
  intro t
  induction t with
  | zero =>
    exact StronglyMeasurable.ite ((measurable_vecOf c 0) (hG 0))
      ((hφ 0).comp_measurable (measurable_vecOf c 0)) stronglyMeasurable_const
  | succ t ih =>
    refine StronglyMeasurable.ite ((measurable_vecOf c (t + 1)) (hG (t + 1)))
      ((hφ (t + 1)).comp_measurable (measurable_vecOf c (t + 1))) ?_
    refine hg.comp_stronglyMeasurable ((ih.comp_measurable measurable_tailH).prodMk
      (StronglyMeasurable.prodMk ?_ stronglyMeasurable_const))
    exact (measurable_const.mul ((continuous_clipB B).measurable.comp
      (measurable_snd.comp (measurable_pi_apply 0)))).stronglyMeasurable

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the repaired candidate has finite memory. -/
theorem finMem_repF (G : (t : ℕ) → Set (Fin (t + 1) → ℝ))
    (φ : (t : ℕ) → (Fin (t + 1) → ℝ) → Y) (g : Y × ℝ × ℝ → Y) (p : Y × ℝ × ℝ) (B c : ℝ) :
    ∀ t (s s' : Hist Unit), (∀ i < t, s i = s' i) →
      repF G φ g p B c t s = repF G φ g p B c t s' := by
  intro t
  induction t with
  | zero =>
    intro s s' _
    have hv := vecOf_congr c (t := 0) (s := s) (s' := s') (fun i hi => absurd hi
      (Nat.not_lt_zero i))
    by_cases h1 : vecOf c 0 s ∈ G 0
    · have h1' : vecOf c 0 s' ∈ G 0 := hv ▸ h1
      simp [repF, h1', hv]
    · have h1' : vecOf c 0 s' ∉ G 0 := hv ▸ h1
      simp [repF, h1, h1']
  | succ t ih =>
    intro s s' h
    have hv := vecOf_congr c (t := t + 1) h
    have ht : repF G φ g p B c t (tailH s) = repF G φ g p B c t (tailH s') :=
      ih _ _ fun i hi => h (i + 1) (by omega)
    have h0 : (s 0).2 = (s' 0).2 := by rw [h 0 (by omega)]
    by_cases h1 : vecOf c (t + 1) s ∈ G (t + 1)
    · have h1' : vecOf c (t + 1) s' ∈ G (t + 1) := hv ▸ h1
      simp [repF, h1', hv]
    · have h1' : vecOf c (t + 1) s' ∉ G (t + 1) := hv ▸ h1
      simp [repF, h1, h1', ht, h0]

/-! ## Local uniqueness among almost-sure solutions -/

omit [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: a parameter whose components are within `r` of `p̄`. -/
theorem dist_pbar_le {ybar y : Y} {e σ r : ℝ} (hy : ‖y - ybar‖ ≤ r) (he : |e| ≤ r)
    (hσ : |σ| ≤ r) : dist ((y, e, σ) : Y × ℝ × ℝ) (pbar ybar) ≤ r := by
  change dist ((y, e, σ) : Y × ℝ × ℝ) (ybar, (0 : ℝ), (0 : ℝ)) ≤ r
  rw [Prod.dist_eq, Prod.dist_eq, dist_eq_norm, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
  exact max_le hy (max_le he hσ)

omit [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the components of a parameter near `p̄`. -/
theorem le_of_dist_pbar {ybar : Y} {q : Y × ℝ × ℝ} {r : ℝ}
    (hq : dist q (pbar ybar) ≤ r) : ‖q.1 - ybar‖ ≤ r ∧ |q.2.1| ≤ r ∧ |q.2.2| ≤ r := by
  change dist q (ybar, (0 : ℝ), (0 : ℝ)) ≤ r at hq
  rw [Prod.dist_eq, Prod.dist_eq, dist_eq_norm, Real.dist_eq, Real.dist_eq, sub_zero,
    sub_zero, max_le_iff, max_le_iff] at hq
  exact hq

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: a family within `r` of `ū` in the sup norm takes values within `r`
of `ȳ`. -/
theorem norm_sub_le_of_dist {w : adSub (R := Unit) Y} {ybar : Y} (n : ℕ × Hist Unit) :
    ‖(w : Bd (ℕ × Hist Unit) Y) n - ybar‖ ≤ dist w (ubar ybar) := by
  rw [dist_eq_norm]
  exact norm_apply_le (((w - ubar ybar : adSub (R := Unit) Y)) : Bd (ℕ × Hist Unit) Y) n

/-- Woodford (2003), App. E.2, p. 695, on the genuine probability space (**local uniqueness
among almost-sure solutions**): there is `δ > 0` such that for parameters `p` within `δ` of
`p̄`, EVERY process `z` adapted to `𝓕_t = σ(ε_0, …, ε_t)`, a.s. within `δ` of `ȳ`, that solves
`E_t f(z_{t+1}, z_t, z_{t−1}, e_t, σ clip(ε_{t+1})) = 0` almost surely (Mathlib's `condExp`)
coincides a.s. at every date with the equilibrium `y_t = ψ(p)(t, h_t)`. The proof reads `z` on
shock prefixes (Doob–Dynkin), keeps the prefixes from which the conditions hold now and a.s.
forever (`goodS`, full measure), repairs the candidate elsewhere by the policy function, and
applies the history-space uniqueness of `ψ`. -/
theorem unique_ae [CompleteSpace Y] [FiniteDimensional ℝ Y] [CompleteSpace Z]
    (ν : ProbabilityMeasure ℝ) {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f)
    (hlaw : N.law () = ν) {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) (hψc : ∀ᶠ q in 𝓝 (pbar ybar : Y × ℝ × ℝ), ContinuousAt ψ q) :
    ∃ δ > 0, ∀ p : Y × ℝ × ℝ, dist p (pbar ybar) < δ → ∀ z : ℕ → (ℕ → ℝ) → Y,
      (∀ t, StronglyMeasurable[(iidSystem ν).𝓕 t] (z t)) →
      (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, ‖z t ω - ybar‖ ≤ δ) →
      (∀ t, (iidSystem ν).μ[fun ω => N.f (z (t + 1) ω, z t ω, zlag p z t ω,
        zenow N.bound p t ω, p.2.2 * clipB N.bound (ω (t + 1))) | (iidSystem ν).𝓕 t]
          =ᵐ[(iidSystem ν).μ] 0) →
      ∀ t, z t =ᵐ[(iidSystem ν).μ] yproc (ψ p : Bd (ℕ × Hist Unit) Y) t := by
  obtain ⟨δ0, hδ0, huniq⟩ := hψ.unique
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.1
    (hψ.solves.and ((N.markov hψ).and hψc))
  set ηm := min ε δ0 with hηm
  have hηm0 : 0 < ηm := lt_min hε hδ0
  have hball' : ∀ q : Y × ℝ × ℝ, dist q (pbar ybar) ≤ ηm → _ := fun q hq =>
    hball (Metric.mem_closedBall.2 (hq.trans (min_le_left _ _)))
  have hcont0 := hψ.cont
  rw [Metric.continuousAt_iff] at hcont0
  obtain ⟨ηP', hηP', hcont⟩ := hcont0 (ηm / 4) (by positivity)
  rw [hψ.base] at hcont
  set ηP := min ηP' (ηm / 2) with hηP
  have hηP0 : 0 < ηP := lt_min hηP' (by positivity)
  set B := N.bound with hB
  set δ := min (ηP / (2 * (1 + |B|))) (ηm / 4) with hδ
  have hB1 : 0 < 1 + |B| := by positivity
  have hδ0' : 0 < δ := lt_min (div_pos hηP0 (by positivity)) (by positivity)
  have hδB : δ * (1 + |B|) ≤ ηP / 2 := by
    have := min_le_left (ηP / (2 * (1 + |B|))) (ηm / 4)
    calc δ * (1 + |B|) ≤ ηP / (2 * (1 + |B|)) * (1 + |B|) :=
          mul_le_mul_of_nonneg_right this hB1.le
      _ = ηP / 2 := by field_simp
  have hδm : δ ≤ ηm / 4 := min_le_right _ _
  have hPm : ηP ≤ ηm / 2 := min_le_right _ _
  refine ⟨δ, hδ0', ?_⟩
  intro p hp z hz hzb hsol
  have hpc := le_of_dist_pbar (r := δ) hp.le
  have hδr : δ ≤ δ * (1 + |B|) := le_mul_of_one_le_right hδ0'.le (by linarith [abs_nonneg B])
  have hclip : ∀ x : ℝ, |p.2.2 * clipB B x| ≤ δ * (1 + |B|) := fun x => by
    rw [abs_mul]
    calc |p.2.2| * |clipB B x| ≤ δ * |B| :=
          mul_le_mul hpc.2.2 (abs_clipB_le _ _) (abs_nonneg _) hδ0'.le
      _ ≤ δ * (1 + |B|) := mul_le_mul_of_nonneg_left (by linarith) hδ0'.le
  -- the policy function and its clamped, globally continuous version
  set ev0 : adSub (R := Unit) Y →L[ℝ] Y :=
    (SmoothInSigma.evalL Y (0, sNil)).comp (adSub (R := Unit) Y).subtypeL with hev0
  set pol : Y × ℝ × ℝ → Y := fun q => (ψ q : Bd (ℕ × Hist Unit) Y) (0, sNil) with hpol
  set clampQ : Y × ℝ × ℝ → Y × ℝ × ℝ := fun q =>
    (clampY ybar ηm q.1, clipB ηm q.2.1, clipB ηm q.2.2) with hclampQ
  set g : Y × ℝ × ℝ → Y := fun q => pol (clampQ q) with hg
  have hclampQ_mem : ∀ q, dist (clampQ q) (pbar ybar) ≤ ηm := fun q =>
    dist_pbar_le (norm_clampY_le ybar hηm0 _)
      ((abs_clipB_le _ _).trans (abs_of_pos hηm0).le)
      ((abs_clipB_le _ _).trans (abs_of_pos hηm0).le)
  have hgc : Continuous g := by
    have hpolc : ContinuousOn pol (Metric.closedBall (pbar ybar) ηm) := fun q hq =>
      (ev0.continuous.continuousAt.comp
        (hball' q (Metric.mem_closedBall.1 hq)).2.2).continuousWithinAt
    exact hpolc.comp_continuous ((continuous_clampY ybar hηm0).comp continuous_fst |>.prodMk
      (((continuous_clipB ηm).comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_clipB ηm).comp (continuous_snd.comp continuous_snd))))
      (fun q => Metric.mem_closedBall.2 (hclampQ_mem q))
  have hg_eq : ∀ q, dist q (pbar ybar) ≤ ηm → g q = pol q := fun q hq => by
    obtain ⟨h1, h2, h3⟩ := le_of_dist_pbar hq
    simp only [hg, hclampQ, clampY_of_le ybar hηm0 h1,
      clipB_of_abs_le (abs_le.1 h2 |>.2 |> fun _ => h2), clipB_of_abs_le h3]
  -- a version on prefixes and the good prefixes
  obtain ⟨φ, hφm, hφb, hφe⟩ := exists_prefix_version ν hz hδ0'.le hzb
  set E : (t : ℕ) → Set (Fin (t + 1) → ℝ) := fun t =>
    {v | ∫ e, resid N p φ t v e ∂(ν : Measure ℝ) = 0} with hEd
  have hEm : ∀ t, MeasurableSet (E t) := fun t =>
    (stronglyMeasurable_resid N hc p hφm t).integral_prod_right'.measurableSet_eq_fun
      stronglyMeasurable_const
  have hEa : ∀ t, ∀ᵐ v ∂(Measure.pi fun _ : Fin (t + 1) => (ν : Measure ℝ)), v ∈ E t :=
    ae_resid_zero ν N hc p hφm hφb hφe hsol
  set G := goodS ν E with hGd
  have hGm := measurableSet_goodS ν hEm
  -- the repaired candidates are equilibria in the ball, hence equal `ψ p`
  have hrep : ∀ c : ℝ, ∀ t s, (ψ p : Bd (ℕ × Hist Unit) Y) (t, s) =
      repF G φ g p B c t s := by
    intro c
    set rep := repF G φ g p B c with hrepd
    have hinv : ∀ t s, vecOf c t s ∈ G t ∨ ∃ P : Y × ℝ × ℝ, dist P (pbar ybar) < ηP ∧
        P.2.2 = p.2.2 ∧ ∃ n, rep t s = (ψ P : Bd (ℕ × Hist Unit) Y) (n, s) := by
      intro t
      induction t with
      | zero =>
        intro s
        by_cases hgd : vecOf c 0 s ∈ G 0
        · exact Or.inl hgd
        · refine Or.inr ⟨p, hp.trans_le ((min_le_left _ _).trans ?_), rfl, 0, ?_⟩
          · exact div_le_self hηP0.le (by linarith [abs_nonneg B])
          · rw [hrepd, repF_bad_zero hgd, hg_eq p (hp.le.trans (hδm.trans (by linarith)))]
            exact (ψ p).2.2 0 sNil s (fun i hi => absurd hi (Nat.not_lt_zero i)) rfl
      | succ t ih =>
        intro s
        by_cases hgd : vecOf c (t + 1) s ∈ G (t + 1)
        · exact Or.inl hgd
        · right
          rw [hrepd, repF_bad_succ hgd]
          rcases ih (tailH s) with hpar | ⟨P, hP, hP2, n, hn⟩
          · have hb : ‖rep t (tailH s) - ybar‖ ≤ δ := by
              rw [hrepd, repF_good hpar]; exact hφb _ _
            set q : Y × ℝ × ℝ := (rep t (tailH s), p.2.2 * clipB B (s 0).2, p.2.2) with hq
            have hqd : dist q (pbar ybar) ≤ δ * (1 + |B|) :=
              dist_pbar_le (hb.trans hδr) (hclip _) (hpc.2.2.trans hδr)
            refine ⟨q, lt_of_le_of_lt hqd (by linarith), rfl, 0, ?_⟩
            rw [hg_eq q (hqd.trans (by linarith))]
            exact (ψ q).2.2 0 sNil s (fun i hi => absurd hi (Nat.not_lt_zero i)) rfl
          · refine ⟨P, hP, hP2, n + 1, ?_⟩
            have hPm' : dist P (pbar ybar) ≤ ηm := hP.le.trans (hPm.trans (by linarith))
            have hmk := (hball' P hPm').2.1 n s
            have hb : ‖rep t (tailH s) - ybar‖ ≤ ηm / 4 := by
              rw [hn]
              exact (norm_sub_le_of_dist _).trans (hcont (hP.trans_le (min_le_left _ _))).le
            have hqd : dist ((rep t (tailH s), p.2.2 * clipB B (s 0).2, p.2.2) : Y × ℝ × ℝ)
                (pbar ybar) ≤ ηm := dist_pbar_le (hb.trans (by linarith))
              ((hclip _).trans (by linarith)) ((hpc.2.2.trans hδr).trans (by linarith))
            rw [hg_eq _ hqd, hmk, hP2, hn]
            rfl
    have hbd : ∀ t s, ‖rep t s - ybar‖ ≤ ηm / 4 := fun t s => by
      rcases hinv t s with hgd | ⟨P, hP, _, n, hn⟩
      · rw [hrepd, repF_good hgd]; exact (hφb _ _).trans hδm
      · rw [hn]
        exact (norm_sub_le_of_dist _).trans (hcont (hP.trans_le (min_le_left _ _))).le
    -- the repaired candidate solves the model at every node
    set repU : ℕ × Hist Unit → Y := fun n => rep n.1 n.2 with hrepU
    have hsolve : ∀ t s, ∫ e, N.f (repU (t + 1, consH ((), e) s), repU (t, s),
        lagF p repU (t, s), N.enowF p (t, s), p.2.2 * clipB N.bound e) ∂(ν : Measure ℝ) = 0 := by
      intro t s
      set v := vecOf c t s with hv
      by_cases hgd : v ∈ G t
      · have hchild : ∀ᵐ e ∂(ν : Measure ℝ),
            rep (t + 1) (consH ((), e) s) = φ (t + 1) (Fin.snoc v e) := by
          filter_upwards [goodS_snoc ν hEm hgd] with e he
          rw [hrepd, repF_good (by rw [vecOf_cons]; exact he), vecOf_cons]
        have hlag : lagF p repU (t, s) = lagv p φ t v := by
          cases t with
          | zero => rfl
          | succ k =>
            have hpar : vecOf c k (tailH s) ∈ G k := by rw [vecOf_tail]; exact hgd.1
            simp only [lagF, lagv, hrepU]
            rw [hrepd, repF_good hpar, vecOf_tail]
        have hnow : N.enowF p (t, s) = enowv N.bound p t v := by
          cases t with
          | zero => rfl
          | succ k => simp [MModel.enowF, enowv, hv, vecOf]
        have hres : ∫ e, resid N p φ t v e ∂(ν : Measure ℝ) = 0 :=
          safeD_sub ν E (goodS_sub ν E hgd)
        rw [← hres]
        refine integral_congr_ae ?_
        filter_upwards [hchild] with e he
        have hs0 : rep t s = φ t v := by rw [hrepd]; exact repF_good hgd
        rw [hlag, hnow]
        simp only [hrepU]
        rw [he, hs0]
        rfl
      · have hchild : ∀ e, rep (t + 1) (consH ((), e) s) = g (rep t s, p.2.2 * clipB B e, p.2.2) :=
          fun e => by
          have hbad : vecOf c (t + 1) (consH ((), e) s) ∉ G (t + 1) := by
            rw [vecOf_cons]
            intro hm
            exact hgd (by have := hm.1; rwa [Fin.init_snoc] at this)
          rw [hrepd, repF_bad_succ hbad]
          simp
        set q : Y × ℝ × ℝ := (lagF p repU (t, s), N.enowF p (t, s), p.2.2) with hq
        have hself : rep t s = g q := by
          cases t with
          | zero => rw [hrepd, repF_bad_zero hgd]; rfl
          | succ k => rw [hrepd, repF_bad_succ hgd]; rfl
        have hqd : dist q (pbar ybar) ≤ ηm := by
          refine dist_pbar_le ?_ ?_ ((hpc.2.2.trans hδr).trans (by linarith))
          · cases t with
            | zero => exact hpc.1.trans (by linarith)
            | succ k => exact (hbd k (tailH s)).trans (by linarith)
          · cases t with
            | zero => exact hpc.2.1.trans (by linarith)
            | succ k => exact (hclip _).trans (by linarith)
        obtain ⟨hsq, hmq, _⟩ := hball' q hqd
        have hy0 : rep t s = pol q := by rw [hself, hg_eq q hqd]
        have hc' : ∀ e, rep (t + 1) (consH ((), e) s) =
            (ψ q : Bd (ℕ × Hist Unit) Y) (1, consH ((), e) sNil) := fun e => by
          rw [hchild e, hmq 0 (consH ((), e) sNil)]
          rw [hg_eq _ (dist_pbar_le ((hbd t s).trans (by linarith))
            ((hclip _).trans (by linarith)) ((hpc.2.2.trans hδr).trans (by linarith)))]
          simp only [hpol, hy0]
          rfl
        have h0 := hsq 0 sNil
        simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
          SmoothInSigmaMeasure.MModel.trans_unit hN, one_smul, hlaw] at h0
        rw [← h0]
        refine integral_congr_ae (Eventually.of_forall fun e => ?_)
        simp only [hrepU, hc', hy0]
        rfl
    set u' : adSub (R := Unit) Y := ⟨mkBd (fun n => rep n.1 n.2) ⟨‖ybar‖ + ηm / 4, fun n => by
        have := hbd n.1 n.2
        calc ‖rep n.1 n.2‖ = ‖(rep n.1 n.2 - ybar) + ybar‖ := by rw [sub_add_cancel]
          _ ≤ ‖rep n.1 n.2 - ybar‖ + ‖ybar‖ := norm_add_le _ _
          _ ≤ ‖ybar‖ + ηm / 4 := by linarith⟩,
      ⟨fun t => stronglyMeasurable_repF hGm hφm hgc p B c t,
        fun t s s' h1 _ => finMem_repF G φ g p B c t s s' h1⟩⟩ with hu'
    have hdist : dist u' (ubar ybar) < δ0 := by
      have hm0 : ηm ≤ δ0 := min_le_right _ _
      rw [dist_eq_norm]
      refine lt_of_le_of_lt (norm_le_of_forall (C := ηm / 4) (by positivity) fun n => ?_)
        (by linarith)
      change ‖rep n.1 n.2 - ybar‖ ≤ ηm / 4
      exact hbd n.1 n.2
    have hsol' : N.Solves ((u' : adSub (R := Unit) Y) : Bd (ℕ × Hist Unit) Y) p := by
      intro t s
      simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
        SmoothInSigmaMeasure.MModel.trans_unit hN, one_smul, hlaw]
      exact hsolve t s
    have hm0 : ηm ≤ δ0 := min_le_right _ _
    have := huniq p u' (hp.trans_le (hδm.trans (by linarith))) hdist hsol'
    intro t s
    rw [this]
    rfl
  -- conclusion: on good prefixes the version is the equilibrium
  intro t
  have hGae : ∀ᵐ ω ∂(iidSystem ν).μ, pref t ω ∈ G t := by
    have h := ae_goodS ν hEm hEa t
    rw [← map_pref ν t] at h
    exact ae_of_ae_map (measurable_pref t).aemeasurable h
  filter_upwards [hφe t, hGae] with ω h1 h2
  rw [h1]
  have hvs := vecOf_histOf t ω
  have := hrep (ω 0) t (histOf t ω)
  rw [repF_good (by rw [hvs]; exact h2), hvs] at this
  exact this.symm

/-- Woodford (2003), App. E.2: the equilibrium read along the path solves the model in the
form used by `unique_ae`, `E_t f(y_{t+1}, y_t, y_{t−1}, e_t, σ clip(ε_{t+1})) = 0` a.s. -/
theorem yproc_solves [FiniteDimensional ℝ Y] [CompleteSpace Z] (ν : ProbabilityMeasure ℝ)
    {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f) (hlaw : N.law () = ν)
    {p : Y × ℝ × ℝ} {u : adSub (R := Unit) Y} (hs : N.Solves (u : Bd (ℕ × Hist Unit) Y) p)
    (t : ℕ) :
    (iidSystem ν).μ[fun ω => N.f (yproc (u : Bd (ℕ × Hist Unit) Y) (t + 1) ω,
      yproc (u : Bd (ℕ × Hist Unit) Y) t ω, zlag p (yproc (u : Bd (ℕ × Hist Unit) Y)) t ω,
      zenow N.bound p t ω, p.2.2 * clipB N.bound (ω (t + 1))) | (iidSystem ν).𝓕 t]
        =ᵐ[(iidSystem ν).μ] 0 := by
  have h := SmoothInSigmaMeasurePath.solves_ae ν hN hc hlaw hs t
  have he : (fun ω => N.f (N.wfun p (u : Bd (ℕ × Hist Unit) Y) (t + 1, histOf (t + 1) ω))) =
      fun ω => N.f (yproc (u : Bd (ℕ × Hist Unit) Y) (t + 1) ω,
        yproc (u : Bd (ℕ × Hist Unit) Y) t ω, zlag p (yproc (u : Bd (ℕ × Hist Unit) Y)) t ω,
        zenow N.bound p t ω, p.2.2 * clipB N.bound (ω (t + 1))) := by
    funext ω
    rw [SmoothInSigmaMeasurePath.wfun_histOf]
    cases t with
    | zero => rfl
    | succ k =>
      rw [SmoothInSigmaMeasurePath.lagF_histOf, SmoothInSigmaMeasurePath.enowF_histOf]
      rfl
  rw [he] at h
  exact h

/-- Woodford (2003), App. E.2, p. 695, and the perturbation method on the GENUINE probability
space (**existence, uniqueness among almost-sure solutions, and `Cᵏ` dependence**): if `f` is
`Cᵏ` (`k ≥ 1`), `f(z̄) = 0`, the linearised operator is invertible, and the shock law is `ν`,
there are a local equilibrium `ψ`, `Cᵏ` at `p̄`, and `δ > 0` such that for `p` within `δ` of
`p̄` the process `y_t = ψ(p)(t, h_t)` solves the model a.s., and every adapted process a.s.
within `δ` of `ȳ` that solves the model a.s. equals it a.s. at every date. -/
theorem exists_unique_equilibrium_iid [CompleteSpace Y] [FiniteDimensional ℝ Y]
    [CompleteSpace Z] (ν : ProbabilityMeasure ℝ) {N : MModel Unit Y Z} (hN : N.Std) {k : ℕ}
    (hk : 1 ≤ k) (hf : ContDiff ℝ k N.f) {ybar : Y} (hss : N.f (zbar ybar) = 0)
    (hdet : (N.linOp hN hf.continuous ybar).IsInvertible) (hlaw : N.law () = ν) :
    ∃ ψ : Y × ℝ × ℝ → adSub (R := Unit) Y, N.LocalSol ybar ψ ∧
      ContDiffAt ℝ k ψ (pbar ybar) ∧ ∃ δ > 0, ∀ p : Y × ℝ × ℝ, dist p (pbar ybar) < δ →
        (∀ t, (iidSystem ν).μ[fun ω => N.f (yproc (ψ p : Bd (ℕ × Hist Unit) Y) (t + 1) ω,
          yproc (ψ p : Bd (ℕ × Hist Unit) Y) t ω,
          zlag p (yproc (ψ p : Bd (ℕ × Hist Unit) Y)) t ω, zenow N.bound p t ω,
          p.2.2 * clipB N.bound (ω (t + 1))) | (iidSystem ν).𝓕 t] =ᵐ[(iidSystem ν).μ] 0) ∧
        ∀ z : ℕ → (ℕ → ℝ) → Y, (∀ t, StronglyMeasurable[(iidSystem ν).𝓕 t] (z t)) →
          (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, ‖z t ω - ybar‖ ≤ δ) →
          (∀ t, (iidSystem ν).μ[fun ω => N.f (z (t + 1) ω, z t ω, zlag p z t ω,
            zenow N.bound p t ω, p.2.2 * clipB N.bound (ω (t + 1))) | (iidSystem ν).𝓕 t]
              =ᵐ[(iidSystem ν).μ] 0) →
          ∀ t, z t =ᵐ[(iidSystem ν).μ] yproc (ψ p : Bd (ℕ × Hist Unit) Y) t := by
  obtain ⟨ψ, hψ, hψk⟩ := N.exists_smooth_solution hN hk hf hss hdet
  have hψc : ∀ᶠ q in 𝓝 (pbar ybar : Y × ℝ × ℝ), ContinuousAt ψ q :=
    (hψk.eventually (by simp)).mono fun q hq => hq.continuousAt
  obtain ⟨δ, hδ, hu⟩ := unique_ae ν hN hf.continuous hlaw hψ hψc
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 hψ.solves
  refine ⟨ψ, hψ, hψk, min δ ε, lt_min hδ hε, fun p hp => ⟨fun t => ?_, fun z hz hzb hsol =>
    hu p (hp.trans_le (min_le_left _ _)) z hz (fun t => (hzb t).mono fun ω h =>
      h.trans (min_le_left _ _)) hsol⟩⟩
  exact yproc_solves ν hN hf.continuous hlaw (hεs (hp.trans_le (min_le_right _ _))) t

end Woodford.StabilizationWelfare.SmoothInSigmaUnique
