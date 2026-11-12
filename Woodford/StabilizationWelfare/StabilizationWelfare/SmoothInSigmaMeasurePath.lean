/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasure

/-!
# The perturbation equilibrium on the i.i.d. probability space

Woodford (2003), *Interest and Prices*, Appendix E.2, p. 695 (the policy function and the
event tree), on the genuine probability space of `ExpectationsMeasureIID`: `Ω = ℕ → ℝ` with the
infinite product `ν^ℕ` of an ARBITRARY law `ν` of bounded support, shocks `ε_t(ω) = ω_t`, and
the natural filtration `𝓕_t = σ(ε_0, …, ε_t)`.

The solutions of `SmoothInSigmaMeasure` are bounded adapted families on histories. Here each is
read along the realised path, `y_t(ω) = u(t, h_t(ω))` with `h_t(ω) = (ε_t, ε_{t−1}, …, ε_0)`,
and the history-space conditions become the equilibrium conditions with Mathlib's conditional
expectation `μ[· | 𝓕_t]`, almost surely.

## Main results

* `histOf`, `histOf_succ` (`h_{t+1} = (ε_{t+1}) :: h_t`), `yproc`, `yproc_adapted`
  (`y_t` is `𝓕_t`-measurable), `norm_yproc_le` (bounded).
* `condExp_freeze` (**the freezing lemma**: independence of `ε_{t+1}` from `𝓕_t` gives
  `E_t g(ε_{≤t}, ε_{t+1}) = ∫ g(ε_{≤t}, e) dν(e)` a.s., via `condDistrib`), `condExp_node`.
* `wfun_histOf`, `lagF_histOf`, `enowF_histOf`: the arguments of `f` along the path are
  `(y_{t+1}, y_t, y_{t−1}, σ clip(ε_t), σ clip(ε_{t+1}))`; `clip_ae`: clipping is the identity
  a.s. when the support of `ν` lies in `[−B, B]`.
* `solves_ae`: a history-space solution solves `E_t f(y_{t+1}, y_t, y_{t−1}, e_t, e_{t+1}) = 0`
  a.s. on the probability space; `exists_equilibrium_iid` (existence, local uniqueness, `Cᵏ`
  dependence on `(y_{−1}, s₀, σ)`, adapted bounded processes solving the model a.s., for any
  bounded-support i.i.d. law).
* Finitely many shock values: `integral_finite_law`, `solves_finite_iff` (a law
  `∑_j π_j δ_{ε_j}` gives the finite averages `∑_j π_j f(…)` of the finite-`J` tree),
  `certainty_equivalence_finite`, `second_order_sigma_finite` (the variance is `∑_j π_j ε_j²`).
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaMeasurePath

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID
open SmoothInSigmaMeasure (Hist consH tailH consH_zero consH_succ tailH_consH adSub clipB
  clipB_of_abs_le measurable_consH MModel)
open SmoothInSigmaMeasure.MModel (lagF policyU)
open SmoothInSigma (Bd norm_apply_le pbar zbar)

variable (ν : ProbabilityMeasure ℝ)

/-! ## Histories along the path -/

/-- Woodford (2003), App. E.2: the date-`t` history read from the shocks `(ε_0, …, ε_t)`
(entry `i` is `ε_{t−i}`, zero beyond the root). -/
def histX (t : ℕ) (x : Set.Iic t → ℝ) : Hist Unit := fun i =>
  ((), if i ≤ t then x ⟨t - i, Set.mem_Iic.2 (Nat.sub_le t i)⟩ else 0)

/-- Woodford (2003), App. E.2: the realised date-`t` history `h_t(ω) = (ε_t, ε_{t−1}, …, ε_0)`. -/
def histOf (t : ℕ) (ω : ℕ → ℝ) : Hist Unit :=
  histX t (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω)

/-- Woodford (2003), App. E.2: the entries of the realised history. -/
theorem histOf_apply (t : ℕ) (ω : ℕ → ℝ) (i : ℕ) :
    histOf t ω i = ((), if i ≤ t then ω (t - i) else 0) := by
  unfold histOf histX
  by_cases h : i ≤ t
  · simp only [h, ↓reduceIte]
    rfl
  · simp [h]

/-- Woodford (2003), App. E.2 (**the history grows by the new shock**):
`h_{t+1}(ω) = (ε_{t+1}) :: h_t(ω)`. -/
theorem histOf_succ (t : ℕ) (ω : ℕ → ℝ) :
    histOf (t + 1) ω = consH ((), ω (t + 1)) (histOf t ω) := by
  funext i
  cases i with
  | zero => simp [histOf_apply]
  | succ j =>
    rw [consH_succ, histOf_apply, histOf_apply]
    simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- Woodford (2003), App. E.2: the predecessor of the realised history. -/
theorem tailH_histOf (t : ℕ) (ω : ℕ → ℝ) : tailH (histOf (t + 1) ω) = histOf t ω := by
  rw [histOf_succ, tailH_consH]

/-- Woodford (2003), App. E.2: the history map is measurable. -/
theorem measurable_histX (t : ℕ) : Measurable (histX t) := by
  refine measurable_pi_iff.mpr fun i => measurable_const.prodMk ?_
  by_cases h : i ≤ t
  · simp only [h, ↓reduceIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- Woodford (2003), App. E.2: the realised history at date `t` is `𝓕_t`-measurable. -/
theorem measurable_histOf (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (histOf t) :=
  (measurable_histX t).comp (comap_measurable _)

/-! ## The processes along the path -/

variable {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

/-- Woodford (2003), App. E.2, p. 695: the process `y_t(ω) = u(t, h_t(ω))` of a family on
histories. -/
def yproc (u : Bd (ℕ × Hist Unit) Y) (t : ℕ) (ω : ℕ → ℝ) : Y := u (t, histOf t ω)

/-- Woodford (2003), App. E.2: the process of an adapted family is adapted to `𝓕`. -/
theorem yproc_adapted {u : Bd (ℕ × Hist Unit) Y} (hu : u ∈ adSub (R := Unit) Y) (t : ℕ) :
    StronglyMeasurable[(iidSystem ν).𝓕 t] (yproc u t) :=
  (hu.1 t).comp_measurable (measurable_histOf ν t)

omit [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: the process of a bounded family is bounded by its sup norm. -/
theorem norm_yproc_le (u : Bd (ℕ × Hist Unit) Y) (t : ℕ) (ω : ℕ → ℝ) :
    ‖yproc u t ω‖ ≤ ‖u‖ :=
  norm_apply_le u _

/-! ## The freezing lemma -/

/-- Woodford (2003), App. E.2 (**the freezing lemma**): since `ε_{t+1}` is independent of
`𝓕_t` with law `ν`, `E_t g(ε_{≤t}, ε_{t+1}) = ∫ g(ε_{≤t}, e) dν(e)` almost surely, for every
bounded measurable `g` (Mathlib's `condExp_prod_ae_eq_integral_condDistrib`). -/
theorem condExp_freeze [CompleteSpace Z] (t : ℕ) {g : (Set.Iic t → ℝ) × ℝ → Z}
    (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ q, ‖g q‖ ≤ C) :
    (iidSystem ν).μ[fun ω => g (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω, ω (t + 1)) |
        (iidSystem ν).𝓕 t] =ᵐ[(iidSystem ν).μ]
      fun ω => ∫ e, g (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω, e) ∂(ν : Measure ℝ) := by
  set X : (ℕ → ℝ) → (Set.Iic t → ℝ) := Preorder.restrictLe (π := fun _ : ℕ => ℝ) t with hXd
  have hXm : Measurable X := Preorder.measurable_restrictLe t
  have hYm : Measurable fun ω : ℕ → ℝ => ω (t + 1) := measurable_pi_apply _
  have hint : Integrable (fun ω => g (X ω, ω (t + 1))) (iidSystem ν).μ :=
    Integrable.of_bound (hg.comp_measurable (hXm.prodMk hYm)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => hC _)
  have h1 := condExp_prod_ae_eq_integral_condDistrib (μ := (iidSystem ν).μ) hXm
    hYm.aemeasurable hg hint
  have hind : IndepFun X (fun ω : ℕ → ℝ => ω (t + 1)) (iidSystem ν).μ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_future ν t).symm
      (le_iSup₂ (f := fun i (_ : i ∈ Set.Ioi t) => coordSigma i) (t + 1) (Nat.lt_succ_self t))
  have hmap : (iidSystem ν).μ.map (fun ω => (X ω, ω (t + 1))) =
      ((iidSystem ν).μ.map X) ⊗ₘ Kernel.const _ (ν : Measure ℝ) := by
    rw [Measure.compProd_const,
      (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).1 hind]
    congr 1
    exact Measure.infinitePi_map_eval _ (t + 1)
  have hcd := ae_of_ae_map hXm.aemeasurable
    (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hXm hYm hmap)
  have hF : (iidSystem ν).𝓕 t = MeasurableSpace.comap X inferInstance := rfl
  rw [hF]
  filter_upwards [h1, hcd] with ω h1ω hω
  rw [h1ω, hω, Kernel.const_apply]

/-- Woodford (2003), App. E.2, p. 695 (**conditional expectations on the event tree are
averages over the next shock**): for a bounded adapted family `g`,
`E_t g(t + 1, h_{t+1}) = ∫ g(t + 1, (e) :: h_t) dν(e)` almost surely. -/
theorem condExp_node [CompleteSpace Z] {g : Bd (ℕ × Hist Unit) Z}
    (hg : g ∈ adSub (R := Unit) Z) (t : ℕ) :
    (iidSystem ν).μ[fun ω => g (t + 1, histOf (t + 1) ω) | (iidSystem ν).𝓕 t]
      =ᵐ[(iidSystem ν).μ] fun ω => ∫ e, g (t + 1, consH ((), e) (histOf t ω)) ∂(ν : Measure ℝ) := by
  have hm : StronglyMeasurable fun q : (Set.Iic t → ℝ) × ℝ =>
      g (t + 1, consH ((), q.2) (histX t q.1)) :=
    (hg.1 (t + 1)).comp_measurable (measurable_consH.comp
      (((measurable_histX t).comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)))
  have h := condExp_freeze ν t hm (C := ‖g‖) (fun q => norm_apply_le g _)
  have he : (fun ω => g (t + 1, histOf (t + 1) ω)) = fun ω =>
      g (t + 1, consH ((), ω (t + 1)) (histX t (Preorder.restrictLe (π := fun _ : ℕ => ℝ) t ω))) :=
    funext fun ω => by rw [histOf_succ]; rfl
  rw [he]
  exact h

/-! ## The equilibrium conditions along the path -/

omit [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the predecessor value along the path is `y_{t−1}`. -/
theorem lagF_histOf (p : Y × ℝ × ℝ) (u : Bd (ℕ × Hist Unit) Y) (t : ℕ) (ω : ℕ → ℝ) :
    lagF p u (t + 1, histOf (t + 1) ω) = yproc u t ω := by
  simp only [lagF, tailH_histOf, yproc]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the current scaled shock along the path is `σ clip(ε_t)`. -/
theorem enowF_histOf (N : MModel Unit Y Z) (p : Y × ℝ × ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    N.enowF p (t + 1, histOf (t + 1) ω) = p.2.2 * clipB N.bound (ω (t + 1)) := by
  simp only [MModel.enowF, histOf_succ, consH_zero]

omit [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2, p. 695: the arguments of `f` along the path,
`(y_{t+1}, y_t, y_{t−1}, e_t, σ clip(ε_{t+1}))`. -/
theorem wfun_histOf (N : MModel Unit Y Z) (p : Y × ℝ × ℝ) (u : Bd (ℕ × Hist Unit) Y) (t : ℕ)
    (ω : ℕ → ℝ) :
    N.wfun p u (t + 1, histOf (t + 1) ω) = (yproc u (t + 1) ω, yproc u t ω,
      lagF p u (t, histOf t ω), N.enowF p (t, histOf t ω),
      p.2.2 * clipB N.bound (ω (t + 1))) := by
  simp only [MModel.wfun, yproc, histOf_succ, consH_zero, tailH_consH]

/-- Woodford (2003), App. E.2: when the support of `ν` lies in `[−B, B]` the clipping is the
identity almost surely, at every date. -/
theorem clip_ae {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ t, clipB B (ω t) = ω t :=
  ae_all_iff.2 fun t => (shock_ae_bdd ν hbdd t).mono fun _ h => clipB_of_abs_le h

variable [FiniteDimensional ℝ Y] [CompleteSpace Z]

/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium conditions with genuine conditional
expectations**): if `u` solves the model on histories and the model's shock law is `ν`, then
along the path, `E_t f(y_{t+1}, y_t, y_{t−1}, e_t, σ clip(ε_{t+1})) = 0` almost surely, with
`E_t = μ[· | 𝓕_t]` on `(ℕ → ℝ, ν^ℕ)`. -/
theorem solves_ae {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f)
    (hlaw : N.law () = ν) {p : Y × ℝ × ℝ} {u : adSub (R := Unit) Y}
    (hs : N.Solves (u : Bd (ℕ × Hist Unit) Y) p) (t : ℕ) :
    (iidSystem ν).μ[fun ω => N.f (N.wfun p u (t + 1, histOf (t + 1) ω)) | (iidSystem ν).𝓕 t]
      =ᵐ[(iidSystem ν).μ] 0 := by
  set G := N.NmS hc (N.WmapL (p, u)) with hG
  have hGv : ∀ n, ((G : adSub (R := Unit) Z) : Bd (ℕ × Hist Unit) Z) n =
      N.f (N.wfun p u n) := fun n => rfl
  have h := condExp_node ν G.2 t
  simp only [hGv] at h
  filter_upwards [h] with ω hω
  rw [hω, Pi.zero_apply]
  have hs' := hs t (histOf t ω)
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
    SmoothInSigmaMeasure.MModel.trans_unit hN, one_smul, hlaw] at hs'
  simpa only [MModel.wfun, tailH_consH, consH_zero] using hs'

/-- Woodford (2003), App. E.2, p. 695, and the perturbation method on a GENUINE probability
space (**existence, local uniqueness and `Cᵏ` dependence, for any bounded-support i.i.d. law**):
if `f` is `Cᵏ` (`k ≥ 1`), `f(z̄) = 0`, the linearised operator is invertible, and the model's
shock law is `ν`, there is a local equilibrium `ψ`, `Cᵏ` at `p̄`, such that for every `p` near
`p̄` the processes `y_t = ψ(p)(t, h_t)` are `𝓕_t`-adapted, bounded, and solve
`E_t f(y_{t+1}, y_t, y_{t−1}, e_t, σ clip(ε_{t+1})) = 0` almost surely. -/
theorem exists_equilibrium_iid [CompleteSpace Y] {N : MModel Unit Y Z} (hN : N.Std) {k : ℕ}
    (hk : 1 ≤ k) (hf : ContDiff ℝ k N.f) {ybar : Y} (hss : N.f (zbar ybar) = 0)
    (hdet : (N.linOp hN hf.continuous ybar).IsInvertible) (hlaw : N.law () = ν) :
    ∃ ψ : Y × ℝ × ℝ → adSub (R := Unit) Y, N.LocalSol ybar ψ ∧ ContDiffAt ℝ k ψ (pbar ybar) ∧
      ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ),
        (∀ t, StronglyMeasurable[(iidSystem ν).𝓕 t] (yproc (ψ p : Bd (ℕ × Hist Unit) Y) t)) ∧
        (∀ t ω, ‖yproc (ψ p : Bd (ℕ × Hist Unit) Y) t ω‖ ≤ ‖(ψ p : Bd (ℕ × Hist Unit) Y)‖) ∧
        ∀ t, (iidSystem ν).μ[fun ω => N.f (N.wfun p (ψ p : Bd (ℕ × Hist Unit) Y)
          (t + 1, histOf (t + 1) ω)) | (iidSystem ν).𝓕 t] =ᵐ[(iidSystem ν).μ] 0 := by
  obtain ⟨ψ, hψ, hψk⟩ := N.exists_smooth_solution hN hk hf hss hdet
  refine ⟨ψ, hψ, hψk, ?_⟩
  filter_upwards [hψ.solves] with p hp
  exact ⟨fun t => yproc_adapted ν (ψ p).2 t, fun t ω => norm_yproc_le _ t ω,
    fun t => solves_ae ν hN hf.continuous hlaw hp t⟩

/-! ## Finitely many shock values: the finite-`J` tree recovered -/

omit [FiniteDimensional ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2 (**finite shock laws**): for `ν = ∑_j π_j δ_{ε_j}` (`π_j ≥ 0`),
`∫ g dν = ∑_j π_j g(ε_j)`, for ANY `g` (no measurability is needed against Dirac masses). -/
theorem integral_finite_law {J V : Type} [Fintype J] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {π eps : J → ℝ} (hπ : ∀ j, 0 ≤ π j) {ν' : ProbabilityMeasure ℝ}
    (hν : (ν' : Measure ℝ) = ∑ j, ENNReal.ofReal (π j) • Measure.dirac (eps j)) (g : ℝ → V) :
    ∫ e, g e ∂(ν' : Measure ℝ) = ∑ j, π j • g (eps j) := by
  rw [hν, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hπ j)]
  · intro j _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    exact (integrable_const (g (eps j))).congr (ae_eq_dirac g).symm

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] in
/-- Woodford (2003), App. E.2, p. 695 (**the finite-`J` event tree as a special case**): with
the law `∑_j π_j δ_{ε_j}` the equilibrium conditions on histories are the finite averages
`∑_j π_j f(y(t + 1, (ε_j) :: s), y(t, s), y_{t−1}, e_t, σ clip(ε_j)) = 0` of the finite tree. -/
theorem solves_finite_iff {J : Type} [Fintype J] {N : MModel Unit Y Z} (hN : N.Std)
    {π eps : J → ℝ} (hπ : ∀ j, 0 ≤ π j)
    (hν : (N.law () : Measure ℝ) = ∑ j, ENNReal.ofReal (π j) • Measure.dirac (eps j))
    (u : ℕ × Hist Unit → Y) (p : Y × ℝ × ℝ) :
    N.Solves u p ↔ ∀ t s, ∑ j, π j • N.f (u (t + 1, consH ((), eps j) s), u (t, s),
      lagF p u (t, s), N.enowF p (t, s), p.2.2 * clipB N.bound (eps j)) = 0 := by
  unfold MModel.Solves
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
    SmoothInSigmaMeasure.MModel.trans_unit hN, one_smul]
  refine forall_congr' fun t => forall_congr' fun s => ?_
  rw [integral_finite_law hπ hν]

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, and the perturbation method (**certainty equivalence with
finitely many shock values**): for the law `∑_j π_j δ_{ε_j}` with support in `[−B, B]` and
mean `∑_j π_j ε_j = 0`, under determinacy, `g_σ(ȳ, 0, 0) = 0`. -/
theorem certainty_equivalence_finite [CompleteSpace Z] [CompleteSpace Y] {J : Type} [Fintype J]
    {N : MModel Unit Y Z} (hN : N.Std) (hf : ContDiff ℝ 1 N.f) {ybar : Y}
    (hL : (N.linOp hN hf.continuous ybar).IsInvertible) {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := Unit) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {G' : Y × ℝ × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policyU ψ) G' (pbar ybar)) {π eps : J → ℝ} (hπ : ∀ j, 0 ≤ π j)
    (hν : (N.law () : Measure ℝ) = ∑ j, ENNReal.ofReal (π j) • Measure.dirac (eps j))
    (hB : ∀ j, |eps j| ≤ N.bound) (hmean : ∑ j, π j * eps j = 0) : G' (0, 0, 1) = 0 := by
  refine SmoothInSigmaMeasure.MModel.certainty_equivalence_iid hN hf hL hψ hψd hg ?_
  rw [integral_finite_law hπ hν]
  simpa only [clipB_of_abs_le (hB _), smul_eq_mul] using hmean

set_option maxHeartbeats 400000 in
-- the second-order statement is large to elaborate
omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, and the second-order perturbation equation (**the `σ²`
correction with finitely many shock values**): for the law `∑_j π_j δ_{ε_j}` with support in
`[−B, B]` and mean zero, the `σ²` equation of `second_order_sigma_iid` holds with the variance
`V = ∑_j π_j ε_j²` of the finite tree. -/
theorem second_order_sigma_finite [CompleteSpace Z] [CompleteSpace Y] {J : Type} [Fintype J]
    {N : MModel Unit Y Z} (hN : N.Std) (hf : ContDiff ℝ 2 N.f) {ybar : Y}
    (hL : (N.linOp hN hf.continuous ybar).IsInvertible) {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) {π eps : J → ℝ}
    (hπ : ∀ j, 0 ≤ π j)
    (hν : (N.law () : Measure ℝ) = ∑ j, ENNReal.ofReal (π j) • Measure.dirac (eps j))
    (hB : ∀ j, |eps j| ≤ N.bound) (hmean : ∑ j, π j * eps j = 0) :
    N.dA ybar (fderiv ℝ (policyU ψ) (pbar ybar)
        (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1), 0, 0)) +
      N.dA ybar (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      N.dB ybar (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      (∑ j, π j * eps j ^ 2) •
        (N.dA ybar (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 1, 0) (0, 1, 0)) +
          fderiv ℝ (fderiv ℝ N.f) (zbar ybar)
            (fderiv ℝ (policyU ψ) (pbar ybar) (0, 1, 0), 0, 0, 0, 1)
            (fderiv ℝ (policyU ψ) (pbar ybar) (0, 1, 0), 0, 0, 0, 1)) = 0 := by
  have hm : ∫ e, clipB N.bound e ∂(N.law () : Measure ℝ) = 0 := by
    rw [integral_finite_law hπ hν]
    simpa only [clipB_of_abs_le (hB _), smul_eq_mul] using hmean
  have h := SmoothInSigmaMeasure.MModel.second_order_sigma_iid hN hf hL hψ hψ2 hm
  have hv : ∫ e, clipB N.bound e ^ 2 ∂(N.law () : Measure ℝ) = ∑ j, π j * eps j ^ 2 := by
    rw [integral_finite_law hπ hν]
    simp only [clipB_of_abs_le (hB _), smul_eq_mul]
  rwa [hv] at h

end Woodford.StabilizationWelfare.SmoothInSigmaMeasurePath
