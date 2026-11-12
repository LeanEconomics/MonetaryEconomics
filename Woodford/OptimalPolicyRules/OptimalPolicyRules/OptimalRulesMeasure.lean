/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.ExpectationsMeasure
import OptimalPolicyRules.InertiaAssumption81
import Mathlib.Topology.Instances.Matrix

/-!
# The general linear-quadratic policy problem with genuine conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 8, Sections 1.1–1.4 (pp. 536–555): the problem
(1.1)–(1.4), the first-order conditions (1.9), Assumption 8.1 (p. 541), optimality subject to
(1.6)/(1.27) and robust optimality (pp. 549–550), on a probability space with a filtration and
Mathlib's conditional expectation (`ExpectationsMeasure.MeasExpectationSystem`). Every equation
holds almost everywhere; plans are essentially bounded and adapted.

## Main results

* `MStructural`, `MFeasible`, `MFOC`, `MFOCSystem`, `MJ`, `MOptimalSubjectTo`: (1.1), (1.9),
  (1.2) and optimality subject to (1.6), in the measure setting.
* `m_lagrangian_gap`, `m_lagrangian_sufficiency`, `m_optimalSubjectTo_of_focSystem`: Lagrangian
  sufficiency (p. 541) — a bounded solution of (1.1) + (1.9) minimises (1.2) a.s. among all
  bounded feasible plans with the same initial constraint; `m_targets_eq_of_J_eq`: the optimal
  target path is unique a.s. (`W ≻ 0`).
* Assumption 8.1 in three forms: the book's literal statement `MAssumption81` (every `Z_{t₀}`,
  `M_{t₀−1}` known at `t₀`), `MAssumption81M` (`M_{t₀−1}` bounded and known at `t₀ − 1`),
  `MAssumption81MB` (also `Z_{t₀}` bounded).
* **Re-examination on a genuine probability space** (`assumption81_iff`, `assumption81M_iff`,
  `robustlyOptimal_iff`): the book's Assumption 8.1 holds **iff** the bounded, predictable form
  holds **and** the date-`t₀` information is a.s. bounded (`BddInfo`) and a.s. predictable at
  `t₀ − 1` (`PredInfo`); robust optimality for every initial condition holds iff it holds for
  bounded ones and `BddInfo` holds. So the earlier counterexamples are not artefacts of the core
  framework: they persist exactly when `BddInfo` or `PredInfo` fails (instances in
  `OptimalRulesMeasureIID`).
* Bridge (`Bridge.mFOCSystem_iff`, `mFOCUnique_iff`, `mAssumption81_iff`, `mAssumption81M_iff`,
  `mAssumption81MB_iff`, `mOptimalSubjectTo_iff`, `mTimelesslyOptimalPlan_iff`,
  `mRobustlyOptimal_iff`, `mRobustlyOptimalB_iff`): on a finite, fully supported sample space
  every notion agrees with the core one for the induced `ExpectationSystem`
  (`ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`); there `BddInfo` always holds
  and the book's Assumption 8.1 is the corrected one plus `PredInfo`
  (`Bridge.core_assumption81_iff`). The one-point probability space is perfect foresight
  (`Bridge.unitSystem_pf`, `unit_assumption81_iff`, `unit_mFOCSystem_iff`).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasure

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Random vectors and vector processes -/

/-- Woodford (2003), p. 540: `E_t` applied componentwise to a random vector, with Mathlib's
conditional expectation. -/
noncomputable def EVm (S : MeasExpectationSystem Ω) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) :
    Ω → ι → ℝ :=
  fun ω i => S.E t (fun ω' => x ω' i) ω

/-- Woodford (2003), p. 540: a random vector known at date `t` (each component is
`𝓕_t`-strongly measurable). -/
def MKnownV (S : MeasExpectationSystem Ω) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) : Prop :=
  ∀ i, StronglyMeasurable[S.𝓕 t] (fun ω => x ω i)

/-- Woodford (2003), p. 537: an adapted vector process. -/
def MAdaptedV (S : MeasExpectationSystem Ω) {ι : Type*} (x : ℕ → Ω → ι → ℝ) : Prop :=
  ∀ t, MKnownV S t (x t)

/-- Woodford (2003), fn 6, p. 539: an essentially bounded vector process (one bound for all
dates and components). -/
def MBoundedV (S : MeasExpectationSystem Ω) {ι : Type*} (x : ℕ → Ω → ι → ℝ) : Prop :=
  ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ∀ i, |x t ω i| ≤ K

/-- Woodford (2003), fn 6, p. 539: an essentially bounded random vector. -/
def MBoundedRV (S : MeasExpectationSystem Ω) {ι : Type*} (v : Ω → ι → ℝ) : Prop :=
  ∃ K, ∀ᵐ ω ∂S.μ, ∀ i, |v ω i| ≤ K

/-- Woodford (2003), p. 540: every component of every date of the process is a random variable
(a.e. strongly measurable). -/
def MAEMeasV (S : MeasExpectationSystem Ω) {ι : Type*} (x : ℕ → Ω → ι → ℝ) : Prop :=
  ∀ t i, AEStronglyMeasurable (fun ω => x t ω i) S.μ

/-! ### Measurability and integrability tools -/

/-- Woodford (2003), p. 540 (tool): a continuous function of a random vector with a.e. strongly
measurable components is a.e. strongly measurable. -/
theorem aesm_comp {μ : Measure Ω} {ι : Type*} [Finite ι] {v : Ω → ι → ℝ}
    (hv : ∀ i, AEStronglyMeasurable (fun ω => v ω i) μ) {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    AEStronglyMeasurable (fun ω => g (v ω)) μ := by
  have hvm : AEMeasurable v μ :=
    aemeasurable_pi_iff.2 fun i => (hv i).aemeasurable
  exact (hg.measurable.comp_aemeasurable hvm).aestronglyMeasurable

/-- Woodford (2003), p. 540 (tool): a continuous function of two random vectors with a.e.
strongly measurable components is a.e. strongly measurable. -/
theorem aesm_comp₂ {μ : Measure Ω} {ι κ : Type*} [Finite ι] [Finite κ] {v : Ω → ι → ℝ}
    {w : Ω → κ → ℝ} (hv : ∀ i, AEStronglyMeasurable (fun ω => v ω i) μ)
    (hw : ∀ i, AEStronglyMeasurable (fun ω => w ω i) μ) {g : (ι → ℝ) × (κ → ℝ) → ℝ}
    (hg : Continuous g) : AEStronglyMeasurable (fun ω => g (v ω, w ω)) μ := by
  have hvm : AEMeasurable v μ := aemeasurable_pi_iff.2 fun i => (hv i).aemeasurable
  have hwm : AEMeasurable w μ := aemeasurable_pi_iff.2 fun i => (hw i).aemeasurable
  exact (hg.measurable.comp_aemeasurable (hvm.prodMk hwm)).aestronglyMeasurable

omit [MeasurableSpace Ω] in
/-- Woodford (2003), p. 540 (tool): a continuous function of a random vector known at `t` is
known at `t`. -/
theorem sm_comp {m : MeasurableSpace Ω} {ι : Type*} [Finite ι] {v : Ω → ι → ℝ}
    (hv : ∀ i, StronglyMeasurable[m] (fun ω => v ω i)) {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    StronglyMeasurable[m] (fun ω => g (v ω)) := by
  have hvm : Measurable[m] v := measurable_pi_iff.2 fun i => (hv i).measurable
  exact (hg.measurable.comp hvm).stronglyMeasurable

omit [MeasurableSpace Ω] in
/-- Woodford (2003), p. 540 (tool): a continuous function of two random vectors known at `t` is
known at `t`. -/
theorem sm_comp₂ {m : MeasurableSpace Ω} {ι κ : Type*} [Finite ι] [Finite κ] {v : Ω → ι → ℝ}
    {w : Ω → κ → ℝ} (hv : ∀ i, StronglyMeasurable[m] (fun ω => v ω i))
    (hw : ∀ i, StronglyMeasurable[m] (fun ω => w ω i)) {g : (ι → ℝ) × (κ → ℝ) → ℝ}
    (hg : Continuous g) : StronglyMeasurable[m] (fun ω => g (v ω, w ω)) := by
  have hvm : Measurable[m] v := measurable_pi_iff.2 fun i => (hv i).measurable
  have hwm : Measurable[m] w := measurable_pi_iff.2 fun i => (hw i).measurable
  exact (hg.measurable.comp (hvm.prodMk hwm)).stronglyMeasurable

/-- Woodford (2003), fn 6, p. 539 (tool): an a.e. bounded, a.e. strongly measurable variable is
integrable. -/
theorem integrable_of_bound {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {K : ℝ} (hK : ∀ᵐ ω ∂μ, |f ω| ≤ K) : Integrable f μ :=
  Integrable.of_bound hf K (hK.mono fun _ h => by rwa [Real.norm_eq_abs])

/-- Woodford (2003), p. 540 (tool): `E_t` of a matrix times a bounded random vector,
`E_t (A x) = A E_t x` a.e. -/
theorem EVm_mulVec (S : MeasExpectationSystem Ω) {ι κ : Type*} [Fintype ι] [Finite κ] (t : ℕ)
    (A : Matrix κ ι ℝ) {x : Ω → ι → ℝ} (hx : ∀ i, Integrable (fun ω => x ω i) S.μ) :
    ∀ᵐ ω ∂S.μ, EVm S t (fun ω => A *ᵥ x ω) ω = A *ᵥ EVm S t x ω := by
  have hk : ∀ k, ∀ᵐ ω ∂S.μ, EVm S t (fun ω => A *ᵥ x ω) ω k = (A *ᵥ EVm S t x ω) k := by
    intro k
    have hf : (fun ω => (A *ᵥ x ω) k) = ∑ i, A k i • fun ω => x ω i := by
      funext ω
      simp [mulVec, dotProduct, Finset.sum_apply]
    have h1 : S.E t (∑ i, A k i • fun ω => x ω i) =ᵐ[S.μ]
        ∑ i, S.E t (A k i • fun ω => x ω i) :=
      condExp_finsetSum (fun i _ => (hx i).smul (A k i)) (S.𝓕 t)
    have h2 : ∀ i, S.E t (A k i • fun ω => x ω i) =ᵐ[S.μ] A k i • S.E t (fun ω => x ω i) :=
      fun i => S.E_smul (A k i) _ t
    filter_upwards [h1, ae_all_iff.2 h2] with ω e1 e2
    change S.E t (fun ω => (A *ᵥ x ω) k) ω = _
    rw [hf, e1, Finset.sum_apply]
    simp only [e2, Pi.smul_apply, smul_eq_mul]
    simp [mulVec, dotProduct, EVm]
  filter_upwards [ae_all_iff.2 hk] with ω h
  exact funext h

/-! ### The linear-quadratic problem in the measure setting -/

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), eq. (1.1), p. 537, for all `t ≥ t₀`, almost surely: the predetermined rows
`Z_{t+1} = A₁₁ Z_t + A₁₂ z_t` and the expectational rows
`Ẽ E_t z_{t+1} = A₂₁ Z_t + A₂₂ z_t + B₂ i_t + c_t` (`c_t = C₂ s_t`), with `E_t` Mathlib's
conditional expectation. -/
def MStructural (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ)
    (t0 : ℕ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t →
    (∀ᵐ ω ∂S.μ, Zpart (y (t + 1) ω) = P.sys.A11 *ᵥ Zpart (y t ω) + P.sys.A12 *ᵥ zpart (y t ω)) ∧
    ∀ᵐ ω ∂S.μ, P.sys.Et *ᵥ EVm S t (fun ω' => zpart (y (t + 1) ω')) ω =
      P.sys.A21 *ᵥ Zpart (y t ω) + P.sys.A22 *ᵥ zpart (y t ω) + ipart (y t ω) • P.sys.B2 + c t ω

/-- Woodford (2003), pp. 538–539 and fn 6: a feasible plan from `t₀` — an essentially bounded
adapted process satisfying (1.1) a.s. for all `t ≥ t₀` and `Z_{t₀} = Z₀` a.s. -/
def MFeasible (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ)
    (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  MStructural S P c t0 y ∧ (∀ᵐ ω ∂S.μ, Zpart (y t0 ω) = Z0 ω) ∧ MBoundedV S y ∧ MAdaptedV S y

/-- Woodford (2003), eq. (1.9), p. 541, a.s. for all `t ≥ t₀`:
`Ã' E_t φ_{t+1} + T' W (τ_t − τ*) − β⁻¹ Ĩ' φ_t = 0`. -/
def MFOC (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, P.sys.Atilᵀ *ᵥ EVm S t (φ (t + 1)) ω +
    P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ t ω) = 0

/-- Woodford (2003), p. 540: the multipliers `M_t` (the `z`-block of `φ_{t+1}`) are measurable
with respect to date-`t` information. -/
def MMultMeas (S : MeasExpectationSystem Ω) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t r, StronglyMeasurable[S.𝓕 t] (fun ω => φ (t + 1) ω (Sum.inr r))

/-- Woodford (2003), pp. 541–542: the system (1.1) + (1.9) with initial conditions
`Z_{t₀} = Z₀`, `M_{t₀−1} = M₀` (a.s.), in essentially bounded processes, with `M_t` known at
`t`. -/
def MFOCSystem (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ)
    (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  MFeasible S P c t0 Z0 y ∧ MBoundedV S φ ∧ MAEMeasV S φ ∧ MMultMeas S φ ∧
    (∀ᵐ ω ∂S.μ, Mpart (φ t0 ω) = M0 ω) ∧ MFOC S P t0 y φ

/-- Woodford (2003), eq. (1.2), p. 537: the discounted expected loss
`E_{t₀} ∑_k β^k L(y_{t₀+k})`, with `E_{t₀}` Mathlib's conditional expectation. -/
noncomputable def MJ (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Ω → ℝ :=
  S.E t0 (fun ω => ∑' k, P.β ^ k * P.loss (y (t0 + k) ω))

/-- Woodford (2003), p. 539 and (1.6): `y` minimises (1.2) almost surely among bounded feasible
plans subject to the additional initial constraints `Ẽ z_{t₀} = ē` (a.s.). -/
def MOptimalSubjectTo (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (ebar : Ω → ιz → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  MFeasible S P c t0 Z0 y ∧ (∀ᵐ ω ∂S.μ, P.sys.Et *ᵥ zpart (y t0 ω) = ebar ω) ∧
    ∀ y', MFeasible S P c t0 Z0 y' → (∀ᵐ ω ∂S.μ, P.sys.Et *ᵥ zpart (y' t0 ω) = ebar ω) →
      MJ S P t0 y ≤ᵐ[S.μ] MJ S P t0 y'

/-- Woodford (2003), Definition, pp. 538–539, (1.5)–(1.6), in the measure setting: (1)
`z_t = f⁰ + F X̄_t` a.s. for all `t ≥ t₀`, a time-invariant function of a state vector `X̄_t`;
(2) the plan minimises (1.2) a.s. among bounded feasible plans subject to
`Ẽ z_{t₀} = Ẽ (f⁰ + F X̄_{t₀})`. -/
def MTimelesslyOptimalPlan {κ : Type*} [Fintype κ] (S : MeasExpectationSystem Ω)
    (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ)
    (Xbar : ℕ → Ω → κ → ℝ) (f0 : ιz → ℝ) (F : Matrix ιz κ ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  (∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, zpart (y t ω) = f0 + F *ᵥ Xbar t ω) ∧
    MOptimalSubjectTo S P c t0 Z0 (fun ω => P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω)) y

/-! ### `E_t` of the multiplier term -/

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): the components of a bounded adapted plan, and fixed
matrices applied to them, are bounded random variables. -/
theorem bound_mulVec_ae {S : MeasExpectationSystem Ω} {ι κ : Type*} [Fintype ι] [Finite κ]
    (A : Matrix κ ι ℝ) {x : ℕ → Ω → ι → ℝ} (hx : MBoundedV S x) :
    ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ∀ r, |(A *ᵥ x t ω) r| ≤ K := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨K, hK⟩ := exists_bound_mulVec A M
  exact ⟨K, fun t => (hM t).mono fun ω h r => hK _ h r⟩

omit [Fintype ιτ] in
/-- Woodford (2003), p. 540: **the conditional-expectation step of the sufficiency argument**, in
the measure setting. For two feasible plans `y`, `y*` (same disturbance), `d = y − y*`, and
bounded multipliers with `M_t` known at `t`,
`E_t [φ_{t+1}' Ĩ d_{t+1}] = (E_t φ_{t+1})' Ã d_t` a.s. (pull-out and the law of iterated
expectations). -/
theorem m_E_next {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y)
    (hys : MFeasible S P c t0 Z0' ys) {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hbφ : MBoundedV S φ)
    (hmφ : MAEMeasV S φ) (hM : MMultMeas S φ) {t : ℕ} (ht : t0 ≤ t) :
    S.E t (fun ω => φ (t + 1) ω ⬝ᵥ (P.sys.Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω))) =ᵐ[S.μ]
      fun ω => EVm S t (φ (t + 1)) ω ⬝ᵥ (P.sys.Atil *ᵥ (y t ω - ys t ω)) := by
  obtain ⟨⟨hsy, -, hby, hay⟩, ⟨hsys, -, hbys, hays⟩⟩ := And.intro hy hys
  obtain ⟨Ky, hKy⟩ := hby
  obtain ⟨Kys, hKys⟩ := hbys
  obtain ⟨Kφ, hKφ⟩ := hbφ
  -- measurability of the plans
  have hym : ∀ s i, StronglyMeasurable[S.𝓕 s] (fun ω => y s ω i) := fun s i => hay s i
  have hysm : ∀ s i, StronglyMeasurable[S.𝓕 s] (fun ω => ys s ω i) := fun s i => hays s i
  -- the row functions
  set d1 : Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ := fun ω => y (t + 1) ω - ys (t + 1) ω with hd1
  set d0 : Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ := fun ω => y t ω - ys t ω with hd0
  set g : ιZ ⊕ ιz → Ω → ℝ := fun r ω => φ (t + 1) ω r * (P.sys.Itil *ᵥ d1 ω) r with hg
  set h : ιZ ⊕ ιz → Ω → ℝ := fun r ω => EVm S t (φ (t + 1)) ω r * (P.sys.Atil *ᵥ d0 ω) r
    with hh
  -- bounds for `Ĩ d₁` and `Ã d₀`
  obtain ⟨KI, hKI⟩ := exists_bound_mulVec P.sys.Itil (Ky + Kys)
  obtain ⟨KA, hKA⟩ := exists_bound_mulVec P.sys.Atil (Ky + Kys)
  have hd1b : ∀ᵐ ω ∂S.μ, ∀ r, |(P.sys.Itil *ᵥ d1 ω) r| ≤ KI := by
    filter_upwards [hKy (t + 1), hKys (t + 1)] with ω h1 h2
    exact hKI _ fun i => (abs_sub _ _).trans (add_le_add (h1 i) (h2 i))
  have hd0b : ∀ᵐ ω ∂S.μ, ∀ r, |(P.sys.Atil *ᵥ d0 ω) r| ≤ KA := by
    filter_upwards [hKy t, hKys t] with ω h1 h2
    exact hKA _ fun i => (abs_sub _ _).trans (add_le_add (h1 i) (h2 i))
  have hd1m : ∀ r, StronglyMeasurable[S.𝓕 (t + 1)] (fun ω => (P.sys.Itil *ᵥ d1 ω) r) := by
    intro r
    exact sm_comp₂ (g := fun p => (P.sys.Itil *ᵥ (p.1 - p.2)) r) (hym (t + 1)) (hysm (t + 1))
      (by fun_prop)
  have hd0m : ∀ r, StronglyMeasurable[S.𝓕 t] (fun ω => (P.sys.Atil *ᵥ d0 ω) r) := by
    intro r
    exact sm_comp₂ (g := fun p => (P.sys.Atil *ᵥ (p.1 - p.2)) r) (hym t) (hysm t)
      (by fun_prop)
  have hφi : ∀ r, Integrable (fun ω => φ (t + 1) ω r) S.μ := fun r =>
    integrable_of_bound (hmφ (t + 1) r) ((hKφ (t + 1)).mono fun ω h => h r)
  have hgi : ∀ r, Integrable (g r) S.μ := by
    intro r
    refine integrable_of_bound ((hmφ (t + 1) r).mul
      ((hd1m r).mono (S.𝓕.le _)).aestronglyMeasurable) (K := Kφ * KI) ?_
    filter_upwards [hKφ (t + 1), hd1b] with ω h1 h2
    rw [hg, abs_mul]
    exact mul_le_mul (h1 r) (h2 r) (abs_nonneg _) ((abs_nonneg _).trans (h1 r))
  -- row by row
  have hrow : ∀ r, S.E t (g r) =ᵐ[S.μ] h r := by
    intro r
    rcases r with r | r
    · -- predetermined rows: `(Ĩ d₁)_r = (Ã d₀)_r` a.s., known at `t`
      have heq : g (Sum.inl r) =ᵐ[S.μ]
          (fun ω => (P.sys.Atil *ᵥ d0 ω) (Sum.inl r)) * fun ω => φ (t + 1) ω (Sum.inl r) := by
        filter_upwards [(hsy t ht).1, (hsys t ht).1] with ω e1 e2
        simp only [hg, hd1, hd0, Pi.mul_apply, P.sys.Itil_mulVec, P.sys.Atil_mulVec]
        have hZ : Zpart (y (t + 1) ω - ys (t + 1) ω) =
            Zpart (y (t + 1) ω) - Zpart (ys (t + 1) ω) := rfl
        have hZ0 : Zpart (y t ω - ys t ω) = Zpart (y t ω) - Zpart (ys t ω) := rfl
        have hz0 : zpart (y t ω - ys t ω) = zpart (y t ω) - zpart (ys t ω) := rfl
        rw [Sum.elim_inl, Sum.elim_inl, hZ, hZ0, hz0, e1, e2, mulVec_sub, mulVec_sub]
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      filter_upwards [S.E_congr heq t,
        S.E_pullOut (hd0m (Sum.inl r)) ((hd0b).mono fun ω h => h (Sum.inl r)) (hφi _)]
        with ω e1 e2
      rw [e1, e2, hh]
      simp only [Pi.mul_apply, EVm]
      ring
    · -- expectational rows: `M_t` is known at `t`
      have hMm := hM t r
      have hMb : ∀ᵐ ω ∂S.μ, |φ (t + 1) ω (Sum.inr r)| ≤ Kφ :=
        (hKφ (t + 1)).mono fun ω h => h _
      have hIi : Integrable (fun ω => (P.sys.Itil *ᵥ d1 ω) (Sum.inr r)) S.μ :=
        integrable_of_bound ((hd1m _).mono (S.𝓕.le _)).aestronglyMeasurable
          (hd1b.mono fun ω h => h _)
      have hgeq : g (Sum.inr r) =
          (fun ω => φ (t + 1) ω (Sum.inr r)) * fun ω => (P.sys.Itil *ᵥ d1 ω) (Sum.inr r) := rfl
      -- `E_t (Ẽ d^z_{t+1}) = Ã d₀` on the expectational rows
      have hzi : ∀ (w : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ), MAdaptedV S w → MBoundedV S w →
          ∀ j, Integrable (fun ω => zpart (w (t + 1) ω) j) S.μ := by
        intro w hw hwb j
        obtain ⟨Kw, hKw⟩ := hwb
        exact integrable_of_bound (((hw (t + 1)) _).mono (S.𝓕.le _)).aestronglyMeasurable
          ((hKw (t + 1)).mono fun ω h => h _)
      have hEd : ∀ᵐ ω ∂S.μ, S.E t (fun ω => (P.sys.Itil *ᵥ d1 ω) (Sum.inr r)) ω =
          (P.sys.Atil *ᵥ d0 ω) (Sum.inr r) := by
        have hfun : (fun ω => (P.sys.Itil *ᵥ d1 ω) (Sum.inr r)) =
            fun ω => (P.sys.Et *ᵥ (zpart (y (t + 1) ω) - zpart (ys (t + 1) ω))) r := by
          funext ω
          rw [hd1, P.sys.Itil_mulVec]
          rfl
        have hsub : ∀ j, S.E t (fun ω => zpart (y (t + 1) ω) j - zpart (ys (t + 1) ω) j)
            =ᵐ[S.μ] fun ω => EVm S t (fun ω' => zpart (y (t + 1) ω')) ω j -
              EVm S t (fun ω' => zpart (ys (t + 1) ω')) ω j := fun j =>
          S.E_sub (hzi y hay ⟨Ky, hKy⟩ j) (hzi ys hays ⟨Kys, hKys⟩ j) t
        have hmv := EVm_mulVec S t P.sys.Et (x := fun ω => zpart (y (t + 1) ω) -
          zpart (ys (t + 1) ω)) (fun j => (hzi y hay ⟨Ky, hKy⟩ j).sub
            (hzi ys hays ⟨Kys, hKys⟩ j))
        filter_upwards [hmv, ae_all_iff.2 hsub, (hsy t ht).2, (hsys t ht).2] with ω e1 e2 e3 e4
        rw [hfun]
        have := congrFun e1 r
        simp only [EVm] at this
        rw [this]
        have hv : EVm S t (fun ω' => zpart (y (t + 1) ω') - zpart (ys (t + 1) ω')) ω =
            EVm S t (fun ω' => zpart (y (t + 1) ω')) ω -
              EVm S t (fun ω' => zpart (ys (t + 1) ω')) ω := by
          funext j
          exact e2 j
        rw [hv, mulVec_sub, e3, e4, hd0, P.sys.Atil_mulVec]
        simp only [Sum.elim_inr]
        have hZ0 : Zpart (y t ω - ys t ω) = Zpart (y t ω) - Zpart (ys t ω) := rfl
        have hz0 : zpart (y t ω - ys t ω) = zpart (y t ω) - zpart (ys t ω) := rfl
        have hi0 : ipart (y t ω - ys t ω) = ipart (y t ω) - ipart (ys t ω) := rfl
        rw [hZ0, hz0, hi0, mulVec_sub, mulVec_sub, sub_smul]
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      have hEM : EVm S t (φ (t + 1)) = fun ω r' => S.E t (fun ω' => φ (t + 1) ω' r') ω := rfl
      have hEMr : S.E t (fun ω' => φ (t + 1) ω' (Sum.inr r)) =
          fun ω => φ (t + 1) ω (Sum.inr r) := S.E_of_stronglyMeasurable hMm (hφi _)
      filter_upwards [S.E_pullOut hMm hMb hIi, hEd] with ω e1 e2
      rw [hgeq, e1, hh]
      simp only [Pi.mul_apply]
      rw [e2, hEM]
      simp only
      rw [hEMr]
  -- assemble
  have hsum : (fun ω => φ (t + 1) ω ⬝ᵥ (P.sys.Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω))) =
      ∑ r, g r := by
    funext ω
    simp [hg, hd1, dotProduct, Finset.sum_apply]
  have hE : S.E t (∑ r, g r) =ᵐ[S.μ] ∑ r, S.E t (g r) :=
    condExp_finsetSum (fun r _ => hgi r) (S.𝓕 t)
  rw [hsum]
  filter_upwards [hE, ae_all_iff.2 hrow] with ω e1 e2
  rw [e1, Finset.sum_apply]
  simp only [e2]
  simp [hh, hd0, dotProduct]

/-! ### Lagrangian sufficiency -/

omit [DecidableEq ιZ] in
/-- Woodford (2003), eq. (1.3) (tool): the period loss is a continuous function of `y_t`. -/
theorem continuous_loss (P : LQProblem ιZ ιz ιτ) : Continuous P.loss := by
  unfold LQProblem.loss
  fun_prop

omit [DecidableEq ιZ] in
/-- Woodford (2003), eq. (1.2), p. 537: for a bounded adapted plan, `J = E_{t₀} ∑ β^k L_{t₀+k}` is
a.s. the convergent series `∑ β^k E_{t₀} L_{t₀+k}` of conditional expectations. -/
theorem hasSum_MJ (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    {z : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hzb : MBoundedV S z) (hza : MAdaptedV S z) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => P.β ^ k * S.E t0 (fun ω' => P.loss (z (t0 + k) ω')) ω)
      (MJ S P t0 z ω) := by
  have hβ0 := P.β_pos
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨K, hK⟩ := exists_bound_lossFn P.T P.W P.τstar Mz
  have hLm : ∀ k, AEStronglyMeasurable (fun ω' => P.loss (z (t0 + k) ω')) S.μ := fun k =>
    aesm_comp (fun i => (((hza (t0 + k)) i).mono (S.𝓕.le _)).aestronglyMeasurable)
      (continuous_loss P)
  have hLb : ∀ k, ∀ᵐ ω ∂S.μ, |P.loss (z (t0 + k) ω)| ≤ K := fun k =>
    (hMz (t0 + k)).mono fun ω h => hK _ h
  have hc : Summable (fun k => P.β ^ k * K) :=
    (summable_geometric_of_lt_one hβ0.le P.β_lt_one).mul_right K
  have hsum := S.E_hasSum (f := fun k ω => P.β ^ k * P.loss (z (t0 + k) ω)) hc
    (fun k => (hLm k).const_mul _) (fun k => (hLb k).mono fun ω h => by
      rw [abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left h (pow_pos hβ0 k).le) t0
  have hsm : ∀ k, S.E t0 (fun ω => P.β ^ k * P.loss (z (t0 + k) ω)) =ᵐ[S.μ]
      fun ω => P.β ^ k * S.E t0 (fun ω' => P.loss (z (t0 + k) ω')) ω := fun k =>
    S.E_smul (P.β ^ k) (fun ω' => P.loss (z (t0 + k) ω')) t0
  filter_upwards [hsum, ae_all_iff.2 hsm] with ω h1 h2
  exact h1.congr_fun fun k => (h2 k).symm

/-- Woodford (2003), p. 541 and survey §4.4: **Lagrangian sufficiency, exact form, with genuine
conditional expectations.** If `y*` with multipliers `φ` solves (1.1) + (1.9) (bounded, `M_t`
known at `t`) and `y` is any bounded feasible plan with the same initial multiplier term
`Ĩ (y_{t₀} − y*_{t₀}) = 0` a.s., then a.s.
`J(y) − J(y*) = ∑_k β^k E_{t₀} ½ (T d_{t₀+k})' W (T d_{t₀+k})`, `d = y − y*`. -/
theorem m_lagrangian_gap {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystem S P c t0 Z0 M0 ys φ) (hy : MFeasible S P c t0 Z0' y)
    (hinit : ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ (y t0 ω - ys t0 ω) = 0) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => P.β ^ k *
        S.E t0 (fun ω' => quad P.W (P.T *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω)
      (MJ S P t0 y ω - MJ S P t0 ys ω) := by
  obtain ⟨hys, hbφ, hmφ, hMφ, -, hfoc⟩ := hs
  have hβ0 := P.β_pos
  have hβ1 := P.β_lt_one
  have hWt : P.Wᵀ = P.W := by
    have := P.W_posDef.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hJy := hasSum_MJ S P t0 hy.2.2.1 hy.2.2.2
  have hJys := hasSum_MJ S P t0 hys.2.2.1 hys.2.2.2
  obtain ⟨Ky, hKy⟩ := hy.2.2.1
  obtain ⟨Kys, hKys⟩ := hys.2.2.1
  obtain ⟨Kφ, hKφ⟩ := hbφ
  have hyA : ∀ s i, AEStronglyMeasurable (fun ω => y s ω i) S.μ := fun s i =>
    ((hy.2.2.2 s i).mono (S.𝓕.le s)).aestronglyMeasurable
  have hysA : ∀ s i, AEStronglyMeasurable (fun ω => ys s ω i) S.μ := fun s i =>
    ((hys.2.2.2 s i).mono (S.𝓕.le s)).aestronglyMeasurable
  have hdA : ∀ s i, AEStronglyMeasurable (fun ω => (y s ω - ys s ω) i) S.μ := fun s i =>
    (hyA s i).sub (hysA s i)
  have hdb : ∀ s, ∀ᵐ ω ∂S.μ, ∀ i, |(y s ω - ys s ω) i| ≤ Ky + Kys := fun s => by
    filter_upwards [hKy s, hKys s] with ω h1 h2 i
    exact (abs_sub _ _).trans (add_le_add (h1 i) (h2 i))
  -- the processes in the per-period identity
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
    have hn := m_E_next (P := P) hy hys ⟨Kφ, hKφ⟩ hmφ hMφ (t := t0 + k) (Nat.le_add_right _ _)
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
  have he0 : S.E t0 (a t0) =ᵐ[S.μ] 0 := by
    have : a t0 =ᵐ[S.μ] 0 := by
      filter_upwards [hinit] with ω h
      simp only [ha, h, dotProduct_zero, Pi.zero_apply]
    exact (S.E_congr this t0).trans (by rw [S.E_zero])
  have heb : ∀ k, ∀ᵐ ω ∂S.μ, |S.E t0 (a (t0 + k)) ω| ≤ Ka := fun k =>
    S.abs_E_le (hab (t0 + k)) t0
  filter_upwards [hJy, hJys, ae_all_iff.2 hkey, he0, ae_all_iff.2 heb] with ω h1 h2 h3 h4 h5
  have htel := hasSum_telescope hβ0 hβ1 (e := fun k => S.E t0 (a (t0 + k)) ω) h5
  simp only [Nat.add_zero, h4, Pi.zero_apply, mul_zero] at htel
  have hfin := (h1.sub h2).sub htel
  rw [sub_zero] at hfin
  refine hfin.congr_fun fun k => ?_
  rw [h3 k]
  simp only [hQ]
  ring_nf

/-- Woodford (2003), p. 541 and survey §4.4: **Lagrangian sufficiency** with genuine
conditional expectations — under the hypotheses of `m_lagrangian_gap`, `J(y*) ≤ J(y)` a.s. -/
theorem m_lagrangian_sufficiency {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystem S P c t0 Z0 M0 ys φ) (hy : MFeasible S P c t0 Z0' y)
    (hinit : ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ (y t0 ω - ys t0 ω) = 0) :
    MJ S P t0 ys ≤ᵐ[S.μ] MJ S P t0 y := by
  have hnn : ∀ k, ∀ᵐ ω ∂S.μ, 0 ≤ S.E t0
      (fun ω' => quad P.W (P.T *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω := fun k =>
    condExp_nonneg (Eventually.of_forall fun ω' => quad_nonneg P.W_posDef.posSemidef _)
  filter_upwards [m_lagrangian_gap hs hy hinit, ae_all_iff.2 hnn] with ω h1 h2
  have := h1.nonneg fun k => mul_nonneg (pow_pos P.β_pos k).le (h2 k)
  linarith

/-- Woodford (2003), p. 541: "any bounded processes consistent with the initial conditions `Z_{t₀}`
and (1.6) [that] satisfy (1.1) and (1.9) for each `t ≥ t₀` conform to the second part of the
definition of optimality from a timeless perspective" — with genuine conditional expectations:
a solution of (1.1) + (1.9) is optimal a.s. subject to its own initial constraint
`Ẽ z_{t₀} = ē`. -/
theorem m_optimalSubjectTo_of_focSystem {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 M0 y φ) :
    MOptimalSubjectTo S P c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y := by
  refine ⟨h.1, Eventually.of_forall fun _ => rfl, fun y' hy' he' => ?_⟩
  refine m_lagrangian_sufficiency h hy' ?_
  filter_upwards [hy'.2.1, h.1.2.1, he'] with ω e1 e2 e3
  rw [mulVec_sub, P.sys.Itil_mulVec, P.sys.Itil_mulVec, e1, e2, e3, sub_self]

/-- Woodford (2003), p. 541 and fn 8 (uniqueness of the optimum), with genuine conditional
expectations: a bounded feasible plan with the same discounted loss as the solution of
(1.1) + (1.9) (same initial constraint) has the same target path almost surely,
`T y_t = T y*_t` a.s. for all `t ≥ t₀` (strict convexity, `W ≻ 0`). -/
theorem m_targets_eq_of_J_eq {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 Z0' : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystem S P c t0 Z0 M0 ys φ) (hy : MFeasible S P c t0 Z0' y)
    (hinit : ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ (y t0 ω - ys t0 ω) = 0)
    (hJ : MJ S P t0 y =ᵐ[S.μ] MJ S P t0 ys) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, P.T *ᵥ y t ω = P.T *ᵥ ys t ω := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  set Q : Ω → ℝ := fun ω => quad P.W (P.T *ᵥ (y (t0 + k) ω - ys (t0 + k) ω)) with hQ
  have hQ0 : 0 ≤ Q := fun ω => quad_nonneg P.W_posDef.posSemidef _
  have hnn : ∀ j, ∀ᵐ ω ∂S.μ, 0 ≤ S.E t0
      (fun ω' => quad P.W (P.T *ᵥ (y (t0 + j) ω' - ys (t0 + j) ω'))) ω := fun j =>
    condExp_nonneg (Eventually.of_forall fun ω' => quad_nonneg P.W_posDef.posSemidef _)
  have hEQ : S.E t0 Q =ᵐ[S.μ] 0 := by
    filter_upwards [m_lagrangian_gap hs hy hinit, ae_all_iff.2 hnn, hJ] with ω h1 h2 h3
    rw [h3, sub_self] at h1
    have hz := congrFun ((hasSum_zero_iff_of_nonneg
      fun j => mul_nonneg (pow_pos P.β_pos j).le (h2 j)).mp h1) k
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', P.β_pos.ne', ne_eq, false_and,
      false_or] at hz
    exact hz
  -- `Q` is integrable
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

/-! ### Assumption 8.1 and robust optimality on a probability space -/

/-- Woodford (2003), Assumption 8.1, p. 541 (existence half), **as stated in the book**: for every
bounded adapted disturbance and all initial conditions `Z_{t₀}`, `M_{t₀−1}` known at `t₀`
(no bound), (1.1) + (1.9) has a bounded solution (the measure-theoretic version of
`GeneralFOC.LQ.FOCSolvable`). -/
def MFOCSolvable (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ), MBoundedV S c →
    MAdaptedV S c → MKnownV S t0 Z0 → MKnownV S t0 M0 → ∃ y φ, MFOCSystem S P c t0 Z0 M0 y φ

/-- Woodford (2003), Assumption 8.1, p. 541 (existence half), with the initial multiplier bounded
and known at `t₀ − 1` (the measure-theoretic `Prop82General.FOCSolvableM`). -/
def MFOCSolvableM (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ), MBoundedV S c →
    MAdaptedV S c → MKnownV S t0 Z0 → MBoundedRV S M0 → MKnownV S (t0 - 1) M0 →
      ∃ y φ, MFOCSystem S P c t0 Z0 M0 y φ

/-- Woodford (2003), Assumption 8.1, p. 541 (existence half), with bounded initial conditions and
a predetermined initial multiplier (the measure-theoretic `InertiaAssumption81.FOCSolvableMB`). -/
def MFOCSolvableMB (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ), MBoundedV S c →
    MAdaptedV S c → MKnownV S t0 Z0 → MBoundedRV S Z0 → MBoundedRV S M0 →
      MKnownV S (t0 - 1) M0 → ∃ y φ, MFOCSystem S P c t0 Z0 M0 y φ

/-- Woodford (2003), Assumption 8.1, p. 541 (uniqueness half): two bounded solutions of
(1.1) + (1.9) with the same data agree a.s. at every date `t ≥ t₀`. -/
def MFOCUnique (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ)
    (y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ φ' : ℕ → Ω → ιZ ⊕ ιz → ℝ),
    MFOCSystem S P c t0 Z0 M0 y φ → MFOCSystem S P c t0 Z0 M0 y' φ' →
      ∀ t, t0 ≤ t → y t =ᵐ[S.μ] y' t ∧ φ t =ᵐ[S.μ] φ' t

variable (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)

/-- Woodford (2003), **Assumption 8.1**, p. 541, as stated in the book, on a probability space. -/
structure MAssumption81 where
  solvable : MFOCSolvable S P t0
  unique : MFOCUnique S P t0

/-- Woodford (2003), Assumption 8.1, p. 541, with the initial multiplier bounded and known at
`t₀ − 1`. -/
structure MAssumption81M where
  solvable : MFOCSolvableM S P t0
  unique : MFOCUnique S P t0

/-- Woodford (2003), Assumption 8.1, p. 541, with bounded initial conditions and a predetermined
initial multiplier. -/
structure MAssumption81MB where
  solvable : MFOCSolvableMB S P t0
  unique : MFOCUnique S P t0

variable {S P t0}

/-- Woodford (2003), Definition, pp. 549–550, (1.16), on a probability space: the rule `Rl` is
robustly optimal if for every bounded adapted disturbance and **every** initial condition
`Z_{t₀}` known at `t₀` it determines an a.s. unique bounded equilibrium that is optimal from a
timeless perspective. -/
def MRobustlyOptimal {κ : Type*} [Fintype κ] (S : MeasExpectationSystem Ω)
    (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ), MBoundedV S c → MAdaptedV S c → MKnownV S t0 Z0 →
    ∃ y, MFeasible S P c t0 Z0 y ∧ Rl c y ∧
      (∀ y', MFeasible S P c t0 Z0 y' → Rl c y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ (f0 : ιz → ℝ) (F : Matrix ιz κ ℝ), MTimelesslyOptimalPlan S P c t0 Z0 (Xbar c y) f0 F y

/-- Woodford (2003), Definition, pp. 549–550, (1.16), on a probability space, **for bounded
initial conditions** (the measure-theoretic `InertiaAssumption81.RobustlyOptimalB`). -/
def MRobustlyOptimalB {κ : Type*} [Fintype κ] (S : MeasExpectationSystem Ω)
    (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ), MBoundedV S c → MAdaptedV S c → MKnownV S t0 Z0 →
    MBoundedRV S Z0 →
    ∃ y, MFeasible S P c t0 Z0 y ∧ Rl c y ∧
      (∀ y', MFeasible S P c t0 Z0 y' → Rl c y' → ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ (f0 : ιz → ℝ) (F : Matrix ιz κ ℝ), MTimelesslyOptimalPlan S P c t0 Z0 (Xbar c y) f0 F y

/-- Woodford (2003), p. 541 (the information condition behind Assumption 8.1): each random
quantity known at date `t` is essentially bounded. -/
def BddInfo (S : MeasExpectationSystem Ω) (t : ℕ) : Prop :=
  ∀ f : Ω → ℝ, StronglyMeasurable[S.𝓕 t] f → ∃ K, ∀ᵐ ω ∂S.μ, |f ω| ≤ K

/-- Woodford (2003), p. 540 (the information condition behind Assumption 8.1): each random
quantity known at date `t` is a.s. equal to one known at `t − 1` (no news arrives at `t`). -/
def PredInfo (S : MeasExpectationSystem Ω) (t : ℕ) : Prop :=
  ∀ f : Ω → ℝ, StronglyMeasurable[S.𝓕 t] f → AEStronglyMeasurable[S.𝓕 (t - 1)] f S.μ

/-- Woodford (2003), pp. 538–541: **what a bounded solution forces on the initial conditions.**
If (1.1) + (1.9) has a bounded solution with `Z_{t₀} = Z₀` and `M_{t₀−1} = M₀`, then `Z₀` and
`M₀` are essentially bounded, and (for `t₀ ≥ 1`) `M₀` is a.s. equal to a variable known at
`t₀ − 1`. -/
theorem necessary_of_mFOCSystem {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P c t0 Z0 M0 y φ) :
    MBoundedRV S Z0 ∧ MBoundedRV S M0 ∧
      (1 ≤ t0 → ∀ r, AEStronglyMeasurable[S.𝓕 (t0 - 1)] (fun ω => M0 ω r) S.μ) := by
  obtain ⟨⟨-, hZ, ⟨Ky, hKy⟩, -⟩, ⟨Kφ, hKφ⟩, -, hM, hM0, -⟩ := h
  refine ⟨⟨Ky, ?_⟩, ⟨Kφ, ?_⟩, fun ht0 r => ?_⟩
  · filter_upwards [hZ, hKy t0] with ω e h j
    rw [← e]
    exact h _
  · filter_upwards [hM0, hKφ t0] with ω e h r
    rw [← e]
    exact h _
  · have hm := hM (t0 - 1) r
    rw [Nat.sub_add_cancel ht0] at hm
    refine ⟨_, hm, ?_⟩
    filter_upwards [hM0] with ω e
    rw [← e]
    rfl

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), fn 4, p. 537 (tool): a nonzero `B₂` means there is a forward-looking
variable. -/
theorem exists_B2_ne (P : LQProblem ιZ ιz ιτ) : ∃ r, P.sys.B2 r ≠ 0 := by
  by_contra h
  push Not at h
  exact P.sys.B2_ne_zero (funext h)

omit [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 541 (tool): the zero disturbance is bounded and adapted. -/
theorem zero_dist : MBoundedV S (fun _ _ (_ : ιz) => (0 : ℝ)) ∧
    MAdaptedV S (fun _ _ (_ : ιz) => (0 : ℝ)) :=
  ⟨⟨0, fun _ => Eventually.of_forall fun _ _ => by simp⟩, fun _ _ => stronglyMeasurable_const⟩

/-- Woodford (2003), p. 541 (tool): componentwise essential bounds give one bound. -/
theorem boundedRV_of_comp {μ : Measure Ω} {ι : Type*} [Finite ι] {v : Ω → ι → ℝ}
    (h : ∀ i, ∃ K, ∀ᵐ ω ∂μ, |v ω i| ≤ K) : ∃ K, ∀ᵐ ω ∂μ, ∀ i, |v ω i| ≤ K := by
  have := Fintype.ofFinite ι
  choose K hK using h
  refine ⟨∑ i, |K i|, ?_⟩
  filter_upwards [ae_all_iff.2 hK] with ω h i
  exact (h i).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |K i|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))

/-- Woodford (2003), **Assumption 8.1**, p. 541, **re-examined on a probability space.** The book's
statement (every `Z_{t₀}`, `M_{t₀−1}` known at `t₀`) holds **iff** the bounded, predetermined
form `MAssumption81MB` holds **and** every variable known at `t₀` is essentially bounded
(`BddInfo`) and a.s. known at `t₀ − 1` (`PredInfo`). So the book's form fails on any
probability space whose date-`t₀` information carries an unbounded variable or genuine news,
for every problem — and holds exactly when the corrected form does, otherwise. -/
theorem assumption81_iff :
    MAssumption81 S P t0 ↔ MAssumption81MB S P t0 ∧ BddInfo S t0 ∧ PredInfo S t0 := by
  obtain ⟨r, -⟩ := exists_B2_ne P
  constructor
  · intro hA
    refine ⟨⟨fun c Z0 M0 hcb hca hZk _ _ hMk => hA.solvable c Z0 M0 hcb hca hZk
      (fun j => (hMk j).mono (S.𝓕.mono (Nat.sub_le t0 1))), hA.unique⟩, fun f hf => ?_,
      fun f hf => ?_⟩
    · obtain ⟨y, φ, h⟩ := hA.solvable _ 0 (fun ω _ => f ω) zero_dist.1 zero_dist.2
        (fun _ => stronglyMeasurable_const) (fun _ => hf)
      obtain ⟨-, ⟨K, hK⟩, -⟩ := necessary_of_mFOCSystem h
      exact ⟨K, hK.mono fun ω h => h r⟩
    · rcases Nat.eq_zero_or_pos t0 with h0 | h0
      · subst h0
        exact hf.aestronglyMeasurable
      · obtain ⟨y, φ, h⟩ := hA.solvable _ 0 (fun ω _ => f ω) zero_dist.1 zero_dist.2
          (fun _ => stronglyMeasurable_const) (fun _ => hf)
        exact (necessary_of_mFOCSystem h).2.2 h0 r
  · rintro ⟨hB, hbdd, hpred⟩
    refine ⟨fun c Z0 M0 hcb hca hZk hMk => ?_, hB.unique⟩
    have hZb : MBoundedRV S Z0 := boundedRV_of_comp fun j => hbdd _ (hZk j)
    have hMb : MBoundedRV S M0 := boundedRV_of_comp fun j => hbdd _ (hMk j)
    have hp := fun j => hpred _ (hMk j)
    set M0' : Ω → ιz → ℝ := fun ω j => (hp j).mk _ ω with hM0'
    have hae : ∀ᵐ ω ∂S.μ, M0 ω = M0' ω := by
      filter_upwards [ae_all_iff.2 fun j => (hp j).ae_eq_mk] with ω h
      exact funext h
    have hM'b : MBoundedRV S M0' := by
      obtain ⟨K, hK⟩ := hMb
      refine ⟨K, ?_⟩
      filter_upwards [hK, hae] with ω h e
      rw [← e]
      exact h
    obtain ⟨y, φ, h⟩ := hB.solvable c Z0 M0' hcb hca hZk hZb hM'b
      (fun j => (hp j).stronglyMeasurable_mk)
    refine ⟨y, φ, h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2⟩
    filter_upwards [h.2.2.2.2.1, hae] with ω e1 e2
    rw [e1, e2]

/-- Woodford (2003), Assumption 8.1, p. 541, with a predetermined bounded initial multiplier
(`Prop82General.Assumption81M`), **re-examined on a probability space**: it is equivalent to
the bounded form `MAssumption81MB` when there is no predetermined variable, and to
`MAssumption81MB` plus `BddInfo` at `t₀` when there is one. -/
theorem assumption81M_iff :
    MAssumption81M S P t0 ↔ MAssumption81MB S P t0 ∧ (Nonempty ιZ → BddInfo S t0) := by
  constructor
  · intro hA
    refine ⟨⟨fun c Z0 M0 hcb hca hZk _ hMb hMk => hA.solvable c Z0 M0 hcb hca hZk hMb hMk,
      hA.unique⟩, fun hne f hf => ?_⟩
    obtain ⟨j⟩ := hne
    obtain ⟨y, φ, h⟩ := hA.solvable _ (fun ω _ => f ω) 0 zero_dist.1 zero_dist.2
      (fun _ => hf) ⟨0, Eventually.of_forall fun _ _ => by simp⟩
      (fun _ => stronglyMeasurable_const)
    obtain ⟨⟨K, hK⟩, -⟩ := necessary_of_mFOCSystem h
    exact ⟨K, hK.mono fun ω h => h j⟩
  · rintro ⟨hB, hbdd⟩
    refine ⟨fun c Z0 M0 hcb hca hZk hMb hMk => ?_, hB.unique⟩
    have hZb : MBoundedRV S Z0 := by
      by_cases hne : Nonempty ιZ
      · exact boundedRV_of_comp fun j => hbdd hne _ (hZk j)
      · have he : IsEmpty ιZ := not_nonempty_iff.mp hne
        exact ⟨0, Eventually.of_forall fun _ j => (IsEmpty.false j).elim⟩
    exact hB.solvable c Z0 M0 hcb hca hZk hZb hMb hMk

omit [DecidableEq ιZ] in
/-- Woodford (2003), Definition, pp. 549–550, (1.16), **re-examined on a probability space**:
robust optimality for every initial condition is equivalent to robust optimality for bounded
initial conditions plus (when there is a predetermined variable) `BddInfo` at `t₀`. -/
theorem robustlyOptimal_iff {κ : Type*} [Fintype κ]
    (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) :
    MRobustlyOptimal S P t0 Rl Xbar ↔
      MRobustlyOptimalB S P t0 Rl Xbar ∧ (Nonempty ιZ → BddInfo S t0) := by
  constructor
  · intro hR
    refine ⟨fun c Z0 hcb hca hZk _ => hR c Z0 hcb hca hZk, fun hne f hf => ?_⟩
    obtain ⟨j⟩ := hne
    obtain ⟨y, ⟨-, hZ, ⟨K, hK⟩, -⟩, -⟩ := hR _ (fun ω _ => f ω) zero_dist.1 zero_dist.2
      (fun _ => hf)
    refine ⟨K, ?_⟩
    filter_upwards [hZ, hK t0] with ω e h
    have := h (Sum.inl (Sum.inl j))
    have e' := congrFun e j
    simp only [Zpart] at e'
    rwa [e'] at this
  · rintro ⟨hB, hbdd⟩ c Z0 hcb hca hZk
    have hZb : MBoundedRV S Z0 := by
      by_cases hne : Nonempty ιZ
      · exact boundedRV_of_comp fun j => hbdd hne _ (hZk j)
      · have he : IsEmpty ιZ := not_nonempty_iff.mp hne
        exact ⟨0, Eventually.of_forall fun _ j => (IsEmpty.false j).elim⟩
    exact hB c Z0 hcb hca hZk hZb

/-! ### Bridge: finite, fully supported sample spaces -/

namespace Bridge

variable [Finite Ω] [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω}

omit [Finite Ω] [DiscreteMeasurableSpace Ω] in
/-- Woodford (2003), p. 540 (tool): when every state has positive probability, "almost surely"
is "surely". -/
theorem ae_iff_forall (hfull : ∀ ω, S.μ {ω} ≠ 0) {p : Ω → Prop} :
    (∀ᵐ ω ∂S.μ, p ω) ↔ ∀ ω, p ω := by
  refine ⟨fun h ω => ?_, fun h => Eventually.of_forall h⟩
  by_contra hne
  have h0 : S.μ {ω' | ¬ p ω'} = 0 := ae_iff.mp h
  refine hfull ω (measure_mono_null (fun ω' hω' => ?_) h0)
  rw [Set.mem_singleton_iff.mp hω']
  exact hne

omit [Finite Ω] [DiscreteMeasurableSpace Ω] in
/-- Woodford (2003), fn 6, p. 539: on a fully supported space, essentially bounded is bounded. -/
theorem mBoundedV_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) {ι : Type*} (x : ℕ → Ω → ι → ℝ) :
    MBoundedV S x ↔ BoundedV x := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K, fun t ω i => (ae_iff_forall hfull).mp (hK t) ω i⟩
  · rintro ⟨K, hK⟩
    exact ⟨K, fun t => Eventually.of_forall fun ω i => hK t ω i⟩

/-- Woodford (2003), p. 540: on a finite, fully supported space, "known at `t`" in the measure
sense (`𝓕_t`-measurable) is "known at `t`" for the induced core system (`E_t x = x`). -/
theorem mKnownV_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) :
    MKnownV S t x ↔ KnownV (S.toExpectationSystem hfull) t x := by
  constructor
  · intro h i
    rw [MeasExpectationSystem.toExpectationSystem_E]
    exact S.E_of_stronglyMeasurable (h i) Integrable.of_finite
  · intro h i
    have := h i
    rw [MeasExpectationSystem.toExpectationSystem_E] at this
    rw [← this]
    exact S.stronglyMeasurable_E t _

/-- Woodford (2003), p. 537: adaptedness agrees with the core notion. -/
theorem mAdaptedV_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) {ι : Type*} (x : ℕ → Ω → ι → ℝ) :
    MAdaptedV S x ↔ AdaptedV (S.toExpectationSystem hfull) x :=
  forall_congr' fun t => mKnownV_iff hfull t (x t)

omit [Finite Ω] [DiscreteMeasurableSpace Ω] in
/-- Woodford (2003), p. 540: the componentwise conditional expectation is the core `EV`. -/
theorem EVm_eq [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0) {ι : Type*}
    (t : ℕ) (x : Ω → ι → ℝ) : EVm S t x = EV (S.toExpectationSystem hfull) t x := rfl

omit [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), eq. (1.1): the measure-theoretic structural equations are the core ones. -/
theorem mStructural_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MStructural S P c t0 y ↔ P.sys.Structural (S.toExpectationSystem hfull) c t0 y := by
  unfold MStructural LinearRESystem.Structural
  simp only [ae_iff_forall hfull, EVm_eq hfull]
  exact forall₂_congr fun _ _ => forall_and.symm

omit [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), pp. 538–539: feasibility agrees with the core notion. -/
theorem mFeasible_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MFeasible S P c t0 Z0 y ↔ P.Feasible (S.toExpectationSystem hfull) c t0 Z0 y := by
  unfold MFeasible LQProblem.Feasible
  rw [mStructural_iff hfull, ae_iff_forall hfull, mBoundedV_iff hfull, mAdaptedV_iff hfull]

/-- Woodford (2003), pp. 541–542: the system (1.1) + (1.9) agrees with the core
`GeneralFOC.LQ.FOCSystem` of the induced core expectation system. -/
theorem mFOCSystem_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) :
    MFOCSystem S P c t0 Z0 M0 y φ ↔ FOCSystem P (S.toExpectationSystem hfull) c t0 Z0 M0 y φ := by
  have hmeas : MAEMeasV S φ := fun t i => (Measurable.of_discrete).aestronglyMeasurable
  have hmm : MMultMeas S φ ↔ MultiplierMeas (S.toExpectationSystem hfull) φ := by
    refine forall_congr' fun t => forall_congr' fun r => ⟨fun h => ?_, fun h => ?_⟩
    · rw [MeasExpectationSystem.toExpectationSystem_E]
      exact S.E_of_stronglyMeasurable h Integrable.of_finite
    · rw [MeasExpectationSystem.toExpectationSystem_E] at h
      rw [← h]
      exact S.stronglyMeasurable_E t _
  unfold MFOCSystem FOCSystem MFOC PFOC FOC
  rw [mFeasible_iff hfull, mBoundedV_iff hfull, hmm, ae_iff_forall hfull]
  simp only [ae_iff_forall hfull, EVm_eq hfull]
  exact ⟨fun ⟨a, b, _, d, e, f⟩ => ⟨a, b, d, e, f⟩, fun ⟨a, b, d, e, f⟩ => ⟨a, b, hmeas, d, e, f⟩⟩

omit [Finite Ω] [DiscreteMeasurableSpace Ω] in
/-- Woodford (2003), p. 541 (tool): on a fully supported space, a.e. equality of random vectors
is equality. -/
theorem ae_eq_iff_eq (hfull : ∀ ω, S.μ {ω} ≠ 0) {ι : Type*} (f g : Ω → ι → ℝ) :
    f =ᵐ[S.μ] g ↔ f = g := by
  rw [EventuallyEq, ae_iff_forall hfull]
  exact ⟨fun h => funext h, fun h ω => by rw [h]⟩

/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541: agrees with
`GeneralFOC.LQ.FOCUnique` of the induced core system. -/
theorem mFOCUnique_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    MFOCUnique S P t0 ↔ FOCUnique P (S.toExpectationSystem hfull) t0 := by
  unfold MFOCUnique FOCUnique
  simp only [mFOCSystem_iff hfull, ae_eq_iff_eq hfull]

/-- Woodford (2003), Assumption 8.1, p. 541, as stated in the book: agrees with
`GeneralFOC.LQ.Assumption81` of the induced core system. -/
theorem mAssumption81_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    MAssumption81 S P t0 ↔ Assumption81 P (S.toExpectationSystem hfull) t0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c Z0 M0 hcb hca hZ hM => ?_, (mFOCUnique_iff hfull P t0).mp h2⟩
    obtain ⟨y, φ, h⟩ := h1 c Z0 M0 ((mBoundedV_iff hfull c).mpr hcb)
      ((mAdaptedV_iff hfull c).mpr hca) ((mKnownV_iff hfull t0 Z0).mpr hZ)
      ((mKnownV_iff hfull t0 M0).mpr hM)
    exact ⟨y, φ, (mFOCSystem_iff hfull P c t0 Z0 M0 y φ).mp h⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun c Z0 M0 hcb hca hZ hM => ?_, (mFOCUnique_iff hfull P t0).mpr h2⟩
    obtain ⟨y, φ, h⟩ := h1 c Z0 M0 ((mBoundedV_iff hfull c).mp hcb)
      ((mAdaptedV_iff hfull c).mp hca) ((mKnownV_iff hfull t0 Z0).mp hZ)
      ((mKnownV_iff hfull t0 M0).mp hM)
    exact ⟨y, φ, (mFOCSystem_iff hfull P c t0 Z0 M0 y φ).mpr h⟩

omit [Finite Ω] [DiscreteMeasurableSpace Ω] in
/-- Woodford (2003), fn 6, p. 539: on a fully supported space, an essentially bounded random
vector is bounded. -/
theorem mBoundedRV_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) {ι : Type*} (v : Ω → ι → ℝ) :
    MBoundedRV S v ↔ ∃ K, ∀ ω i, |v ω i| ≤ K := by
  unfold MBoundedRV
  simp only [ae_iff_forall hfull]

/-- Woodford (2003), Assumption 8.1, p. 541, with bounded initial conditions and a predetermined
initial multiplier: agrees with `InertiaAssumption81.Assumption81MB` of the induced core
system. -/
theorem mAssumption81MB_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    MAssumption81MB S P t0 ↔
      InertiaAssumption81.Assumption81MB P (S.toExpectationSystem hfull) t0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c Z0 M0 hcb hca hZ hZb hMb hM => ?_, (mFOCUnique_iff hfull P t0).mp h2⟩
    obtain ⟨y, φ, h⟩ := h1 c Z0 M0 ((mBoundedV_iff hfull c).mpr hcb)
      ((mAdaptedV_iff hfull c).mpr hca) ((mKnownV_iff hfull t0 Z0).mpr hZ)
      ((mBoundedRV_iff hfull Z0).mpr hZb) ((mBoundedRV_iff hfull M0).mpr hMb)
      ((mKnownV_iff hfull (t0 - 1) M0).mpr hM)
    exact ⟨y, φ, (mFOCSystem_iff hfull P c t0 Z0 M0 y φ).mp h⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun c Z0 M0 hcb hca hZ hZb hMb hM => ?_, (mFOCUnique_iff hfull P t0).mpr h2⟩
    obtain ⟨y, φ, h⟩ := h1 c Z0 M0 ((mBoundedV_iff hfull c).mp hcb)
      ((mAdaptedV_iff hfull c).mp hca) ((mKnownV_iff hfull t0 Z0).mp hZ)
      ((mBoundedRV_iff hfull Z0).mp hZb) ((mBoundedRV_iff hfull M0).mp hMb)
      ((mKnownV_iff hfull (t0 - 1) M0).mp hM)
    exact ⟨y, φ, (mFOCSystem_iff hfull P c t0 Z0 M0 y φ).mpr h⟩

/-- Woodford (2003), Assumption 8.1, p. 541, with a predetermined bounded initial multiplier:
agrees with `Prop82General.Assumption81M` of the induced core system. -/
theorem mAssumption81M_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    MAssumption81M S P t0 ↔ Prop82General.Assumption81M P (S.toExpectationSystem hfull) t0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c Z0 M0 hcb hca hZ hMb hM => ?_, (mFOCUnique_iff hfull P t0).mp h2⟩
    obtain ⟨y, φ, h⟩ := h1 c Z0 M0 ((mBoundedV_iff hfull c).mpr hcb)
      ((mAdaptedV_iff hfull c).mpr hca) ((mKnownV_iff hfull t0 Z0).mpr hZ)
      ((mBoundedRV_iff hfull M0).mpr hMb) ((mKnownV_iff hfull (t0 - 1) M0).mpr hM)
    exact ⟨y, φ, (mFOCSystem_iff hfull P c t0 Z0 M0 y φ).mp h⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun c Z0 M0 hcb hca hZ hMb hM => ?_, (mFOCUnique_iff hfull P t0).mpr h2⟩
    obtain ⟨y, φ, h⟩ := h1 c Z0 M0 ((mBoundedV_iff hfull c).mp hcb)
      ((mAdaptedV_iff hfull c).mp hca) ((mKnownV_iff hfull t0 Z0).mp hZ)
      ((mBoundedRV_iff hfull M0).mp hMb) ((mKnownV_iff hfull (t0 - 1) M0).mp hM)
    exact ⟨y, φ, (mFOCSystem_iff hfull P c t0 Z0 M0 y φ).mpr h⟩

omit [DiscreteMeasurableSpace Ω] in
/-- Woodford (2003), p. 541: on a finite sample space every random variable is bounded, so
`BddInfo` holds at every date (consistent with `InertiaAssumption81.in_assumption81M_of_finite`,
where the bounded and unbounded forms coincide). -/
theorem bddInfo_of_finite (t : ℕ) : BddInfo S t := by
  have := Fintype.ofFinite Ω
  intro f _
  exact ⟨∑ ω, |f ω|, Eventually.of_forall fun ω => Finset.single_le_sum
    (f := fun ω => |f ω|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ω)⟩

/-- Woodford (2003), Assumption 8.1, p. 541, on a finite tree: **the core statement of the book's
form is equivalent to the corrected bounded form plus `PredInfo`** — the measure-theoretic
characterisation `assumption81_iff`, transported through the bridge (this is the finite-tree
content of `NKAssumption81.not_assumption81_coin`). -/
theorem core_assumption81_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    Assumption81 P (S.toExpectationSystem hfull) t0 ↔
      InertiaAssumption81.Assumption81MB P (S.toExpectationSystem hfull) t0 ∧
        PredInfo S t0 := by
  rw [← mAssumption81_iff hfull, ← mAssumption81MB_iff hfull, assumption81_iff]
  exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, bddInfo_of_finite t0, c⟩⟩

end Bridge

namespace Bridge

variable [Finite Ω] [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω}

omit [Finite Ω] [DiscreteMeasurableSpace Ω] [DecidableEq ιZ] in
/-- Woodford (2003), eq. (1.2): the measure-theoretic discounted loss is the core one. -/
theorem mJ_eq [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MJ S P t0 y = P.J (S.toExpectationSystem hfull) t0 y := rfl

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 539 and (1.6): optimality subject to `Ẽ z_{t₀} = ē` agrees with the core
`GeneralSetup.LQProblem.OptimalSubjectTo` of the induced core system. -/
theorem mOptimalSubjectTo_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : LQProblem ιZ ιz ιτ)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (ebar : Ω → ιz → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MOptimalSubjectTo S P c t0 Z0 ebar y ↔
      P.OptimalSubjectTo (S.toExpectationSystem hfull) c t0 Z0 ebar y := by
  unfold MOptimalSubjectTo LQProblem.OptimalSubjectTo
  simp only [Filter.EventuallyLE, ae_iff_forall hfull, mFeasible_iff hfull, mJ_eq hfull]

omit [DecidableEq ιZ] in
/-- Woodford (2003), Definition, pp. 538–539: optimality from a timeless perspective agrees with
the core `GeneralSetup.LQProblem.TimelesslyOptimalPlan`. -/
theorem mTimelesslyOptimalPlan_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) {κ : Type*} [Fintype κ]
    (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ)
    (Xbar : ℕ → Ω → κ → ℝ) (f0 : ιz → ℝ) (F : Matrix ιz κ ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MTimelesslyOptimalPlan S P c t0 Z0 Xbar f0 F y ↔
      P.TimelesslyOptimalPlan (S.toExpectationSystem hfull) c t0 Z0 Xbar f0 F y := by
  unfold MTimelesslyOptimalPlan LQProblem.TimelesslyOptimalPlan
  simp only [ae_iff_forall hfull, mOptimalSubjectTo_iff hfull]

omit [DecidableEq ιZ] in
/-- Woodford (2003), Definition, pp. 549–550, (1.16): robust optimality agrees with the core
`GeneralSetup.RobustlyOptimal` of the induced core system. -/
theorem mRobustlyOptimal_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) {κ : Type*} [Fintype κ]
    (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) :
    MRobustlyOptimal S P t0 Rl Xbar ↔
      RobustlyOptimal P (S.toExpectationSystem hfull) t0 Rl Xbar := by
  unfold MRobustlyOptimal RobustlyOptimal
  simp only [mBoundedV_iff hfull, mAdaptedV_iff hfull, mKnownV_iff hfull, mFeasible_iff hfull,
    ae_eq_iff_eq hfull, mTimelesslyOptimalPlan_iff hfull]

omit [DecidableEq ιZ] in
/-- Woodford (2003), Definition, pp. 549–550, for bounded initial conditions: agrees with the
core `InertiaAssumption81.RobustlyOptimalB`. -/
theorem mRobustlyOptimalB_iff (hfull : ∀ ω, S.μ {ω} ≠ 0) {κ : Type*} [Fintype κ]
    (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) :
    MRobustlyOptimalB S P t0 Rl Xbar ↔
      InertiaAssumption81.RobustlyOptimalB P (S.toExpectationSystem hfull) t0 Rl Xbar := by
  unfold MRobustlyOptimalB InertiaAssumption81.RobustlyOptimalB
  simp only [mBoundedV_iff hfull, mAdaptedV_iff hfull, mKnownV_iff hfull, mFeasible_iff hfull,
    ae_eq_iff_eq hfull, mTimelesslyOptimalPlan_iff hfull, mBoundedRV_iff hfull]

/-! ### The one-point probability space is perfect foresight -/

/-- Woodford (2003), p. 540 (tool): two core expectation systems with the same `E` are equal. -/
theorem expectationSystem_eq {Ω' : Type*} {𝔼 𝔼' : ExpectationSystem Ω'} (h : 𝔼.E = 𝔼'.E) :
    𝔼 = 𝔼' := by
  cases 𝔼
  cases 𝔼'
  simp only at h
  subst h
  rfl

/-- Woodford (2003), p. 540: the one-point probability space (the Dirac measure on `Unit`, trivial
filtration) — the deterministic economy. -/
noncomputable def unitSystem : MeasExpectationSystem Unit :=
  ⟨⟨Measure.dirac (), inferInstance⟩, ⊥⟩

/-- Woodford (2003), p. 540: the one point has full probability. -/
theorem unitSystem_full (u : Unit) : unitSystem.μ {u} ≠ 0 := by
  change Measure.dirac () {u} ≠ 0
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton_iff.mpr rfl)]
  exact one_ne_zero

/-- Woodford (2003), p. 540: **the core perfect-foresight system is the measure-theoretic system
of the one-point probability space** (`E_t` is the identity). -/
theorem unitSystem_pf :
    unitSystem.toExpectationSystem unitSystem_full = perfectForesight := by
  refine expectationSystem_eq (funext fun t => LinearMap.ext fun x => ?_)
  rw [MeasExpectationSystem.toExpectationSystem_E]
  have hx : x = fun _ => x () := rfl
  rw [hx, unitSystem.E_const]
  rfl

/-- Woodford (2003), Assumption 8.1, p. 541: **the core perfect-foresight Assumption 8.1 is the
measure-theoretic Assumption 8.1 of the one-point probability space** (the hypothesis behind the
coefficient matrices of `OptimalRulesMeasureMarkov`). -/
theorem unit_assumption81_iff (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) :
    MAssumption81 unitSystem P t0 ↔ Assumption81 P perfectForesight t0 := by
  rw [mAssumption81_iff unitSystem_full, unitSystem_pf]

/-- Woodford (2003), pp. 541–542: on the one-point probability space the measure-theoretic system
(1.1) + (1.9) is the core perfect-foresight one. -/
theorem unit_mFOCSystem_iff (P : LQProblem ιZ ιz ιτ) (c : ℕ → Unit → ιz → ℝ) (t0 : ℕ)
    (Z0 : Unit → ιZ → ℝ) (M0 : Unit → ιz → ℝ) (y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (φ : ℕ → Unit → ιZ ⊕ ιz → ℝ) :
    MFOCSystem unitSystem P c t0 Z0 M0 y φ ↔ FOCSystem P perfectForesight c t0 Z0 M0 y φ := by
  rw [mFOCSystem_iff unitSystem_full, unitSystem_pf]

end Bridge

end Woodford.OptimalPolicyRules.OptimalRulesMeasure
