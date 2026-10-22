/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR5Meas
import IntertemporalModel.TidyR5BondPrice

/-!
# The linear model on a genuine probability space, and the links to the abstract versions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.5, pp. 34–37 (the linear
model (2.16)–(2.19) under an interest-rate peg) and §2.6, pp. 39–42 (the rule (2.20)–(2.25)),
on a probability space with Mathlib's conditional expectation (`MeasExpectationSystem`), with
equations holding almost surely; and the links of every measure-theoretic notion of this module
and of `TidyR5Meas` to its abstract `ExpectationSystem` counterpart on finite event trees.

## Main results

* `MIsShock`, `MPegModel`, `MRuleModel`: shocks, the peg model (2.16)–(2.17) and the rule model
  (2.20)–(2.22) almost surely.
* `mPegModel_iff`, `mPeg_linear_existsUnique` ((2.19): for every adapted integrable rate path
  and every shock, exactly one solution given `π_0`, up to null sets), `mRule_iff`,
  `mRule_linear_existsUnique` ((2.25): for every `θ ∈ ℝ`, no Taylor principle).
* `mFiscShock`, `mFiscShock_isShock`: the fiscal shock `ΔE_{t+1} PV_{t+1}` of the equilibria of
  `TidyR5Meas` is a shock, and it is the shock of the exact (2.17),
  `TidyR5Meas.mUnexpected_inflation`.
* Links on every finite event tree (`ExpectationsMeasure.TreeBridge.treeSystem`):
  `tree_forwardSol` (present values agree), `tree_mPegP` (the target equilibria agree),
  `tree_mEquilibrium_iff` (`MEquilibrium` is `FiscalMonetary.Equilibrium`, for `β > 0`),
  `tree_mIsEqm_iff` (`MIsEqm` is `Valuation.IsEqm`), `tree_mIsShock_iff`,
  `tree_mPegModel_iff`, `tree_mRuleModel_iff` (the linear models agree), `tree_mFiscShock`
  (the fiscal shocks agree, and are `LinearFTMP.pvNews` for bounded surpluses).
-/

namespace Cochrane.IntertemporalModel.TidyR5MeasLinear

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The linear model -/

/-- Cochrane (2023), p. 40, on a probability space: a shock is known on arrival, integrable,
and has zero forecast, `E_t ε_{t+1} = 0` a.s. -/
def MIsShock (ε : ℕ → Ω → ℝ) : Prop :=
  (∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (ε (t + 1))) ∧ (∀ t, Integrable (ε (t + 1)) S.μ) ∧
    ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35, on a probability space: `i_t = E_t π_{t+1}` and
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` almost surely at every date. -/
def MPegModel (i ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t =ᵐ[S.μ] S.E t (π (t + 1)) ∧ S.innov t (π (t + 1)) =ᵐ[S.μ] -ε (t + 1)

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40, on a probability space: `i_t = E_t π_{t+1}`,
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` and the rule `i_t = θ π_t + u_t`, almost surely at every
date. -/
def MRuleModel (θ : ℝ) (i u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t =ᵐ[S.μ] S.E t (π (t + 1)) ∧ S.innov t (π (t + 1)) =ᵐ[S.μ] -ε (t + 1) ∧
    i t =ᵐ[S.μ] θ • π t + u t

variable {i ε π u : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 35: a variable `x` known and integrable at `t` with a shock `ε_{t+1}`:
`E_t(x − ε_{t+1}) = x` and `ΔE_{t+1}(x − ε_{t+1}) = −ε_{t+1}` almost surely. -/
theorem E_innov_known_sub_shock {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    (hxi : Integrable x S.μ) (hε : MIsShock S ε) :
    S.E t (x - ε (t + 1)) =ᵐ[S.μ] x ∧ S.innov t (x - ε (t + 1)) =ᵐ[S.μ] -ε (t + 1) := by
  have hE : S.E t (x - ε (t + 1)) =ᵐ[S.μ] x := by
    filter_upwards [S.E_sub hxi (hε.2.1 t) t, hε.2.2 t] with ω h1 h2
    rw [h1, Pi.sub_apply, S.E_of_stronglyMeasurable hx hxi, h2, Pi.zero_apply, sub_zero]
  refine ⟨hE, ?_⟩
  have hm : StronglyMeasurable[S.𝓕 (t + 1)] (x - ε (t + 1)) :=
    (hx.mono (S.𝓕.mono (Nat.le_succ t))).sub (hε.1 t)
  have hk := S.E_of_stronglyMeasurable hm (hxi.sub (hε.2.1 t))
  filter_upwards [hE] with ω h
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.neg_apply]
  rw [hk, h, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (2.19), p. 36, on a probability space: for adapted inflation integrable
at every date, an adapted integrable rate and a shock, the model (2.16)–(2.17) holds iff
`π_{t+1} = i_t − ε_{Σs,t+1}` almost surely at every date. -/
theorem mPegModel_iff (hπ : StronglyAdapted S.𝓕 π) (hπi : ∀ t, Integrable (π t) S.μ)
    (hia : StronglyAdapted S.𝓕 i) (hii : ∀ t, Integrable (i t) S.μ) (hε : MIsShock S ε) :
    MPegModel S i ε π ↔ ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1) := by
  constructor
  · intro h t
    have e := S.eq_E_add_innov (hπ (t + 1)) (hπi (t + 1))
    filter_upwards [(h t).1, (h t).2] with ω h1 h2
    rw [congrFun e ω, Pi.add_apply, ← h1, h2, Pi.sub_apply, Pi.neg_apply]
    ring
  · intro h t
    obtain ⟨hE, hN⟩ := E_innov_known_sub_shock S (hia t) (hii t) hε
    have hc1 := S.E_congr (h t) t
    have hc2 := S.E_congr (h t) (t + 1)
    refine ⟨?_, ?_⟩
    · filter_upwards [hc1, hE] with ω h1 h2
      rw [h1, h2]
    · filter_upwards [hc1, hc2, hN] with ω h1 h2 h3
      simp only [MeasExpectationSystem.innov, Pi.sub_apply] at h3 ⊢
      rw [h1, h2]
      exact h3

/-- Cochrane (2023), eq. (2.19), p. 36, on a probability space, **existence and uniqueness**: for
every adapted integrable rate path and every shock, given an integrable `π_0` known at `0`, the
solution `π_{t+1} = i_t − ε_{Σs,t+1}` (`LinearFTMP.pegSol`) is adapted, integrable and solves the
model, and every adapted integrable solution with the same `π_0` equals it almost surely at
every date. No boundedness is imposed. -/
theorem mPeg_linear_existsUnique (hia : StronglyAdapted S.𝓕 i) (hii : ∀ t, Integrable (i t) S.μ)
    (hε : MIsShock S ε) {π0 : Ω → ℝ} (h0 : StronglyMeasurable[S.𝓕 0] π0)
    (h0i : Integrable π0 S.μ) :
    (StronglyAdapted S.𝓕 (LinearFTMP.pegSol i ε π0) ∧
      (∀ t, Integrable (LinearFTMP.pegSol i ε π0 t) S.μ) ∧
      MPegModel S i ε (LinearFTMP.pegSol i ε π0)) ∧
    ∀ π : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 π → (∀ t, Integrable (π t) S.μ) → π 0 =ᵐ[S.μ] π0 →
      MPegModel S i ε π → ∀ t, π t =ᵐ[S.μ] LinearFTMP.pegSol i ε π0 t := by
  have ha : StronglyAdapted S.𝓕 (LinearFTMP.pegSol i ε π0) := fun t => by
    cases t with
    | zero => exact h0
    | succ t => exact ((hia t).mono (S.𝓕.mono (Nat.le_succ t))).sub (hε.1 t)
  have hint : ∀ t, Integrable (LinearFTMP.pegSol i ε π0 t) S.μ := fun t => by
    cases t with
    | zero => exact h0i
    | succ t => exact (hii t).sub (hε.2.1 t)
  refine ⟨⟨ha, hint, (mPegModel_iff S ha hint hia hii hε).mpr fun t =>
    Eventually.of_forall fun ω => rfl⟩, fun π hπ hπi hπ0 hm t => ?_⟩
  have h := (mPegModel_iff S hπ hπi hia hii hε).mp hm
  cases t with
  | zero => exact hπ0
  | succ t => exact h t

/-- Cochrane (2023), eq. (2.25), p. 40, on a probability space: for adapted integrable inflation
and disturbance and a shock, the rule model holds iff `π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}` and
`i_t = θ π_t + u_t` almost surely at every date. -/
theorem mRule_iff {θ : ℝ} (hπ : StronglyAdapted S.𝓕 π) (hπi : ∀ t, Integrable (π t) S.μ)
    (hu : StronglyAdapted S.𝓕 u) (hui : ∀ t, Integrable (u t) S.μ) (hε : MIsShock S ε) :
    MRuleModel S θ i u ε π ↔
      ∀ t, π (t + 1) =ᵐ[S.μ] θ • π t + u t - ε (t + 1) ∧ i t =ᵐ[S.μ] θ • π t + u t := by
  have hk : ∀ t, StronglyMeasurable[S.𝓕 t] (θ • π t + u t) := fun t =>
    ((hπ t).const_smul θ).add (hu t)
  have hki : ∀ t, Integrable (θ • π t + u t) S.μ := fun t => ((hπi t).smul θ).add (hui t)
  constructor
  · intro h t
    refine ⟨?_, (h t).2.2⟩
    have e := S.eq_E_add_innov (hπ (t + 1)) (hπi (t + 1))
    filter_upwards [(h t).1, (h t).2.1, (h t).2.2] with ω h1 h2 h3
    rw [congrFun e ω, Pi.add_apply, ← h1, h2, h3, Pi.sub_apply, Pi.neg_apply]
    ring
  · intro h t
    obtain ⟨hE, hN⟩ := E_innov_known_sub_shock S (hk t) (hki t) hε
    have hc1 := S.E_congr (h t).1 t
    have hc2 := S.E_congr (h t).1 (t + 1)
    refine ⟨?_, ?_, (h t).2⟩
    · filter_upwards [hc1, hE, (h t).2] with ω h1 h2 h3
      rw [h1, h2, h3]
    · filter_upwards [hc1, hc2, hN] with ω h1 h2 h3
      simp only [MeasExpectationSystem.innov, Pi.sub_apply] at h3 ⊢
      rw [h1, h2]
      exact h3

/-- Cochrane (2023), eqs. (2.20)–(2.25), p. 40, on a probability space, the fiscal-theory point
of §2.6: for **every** `θ ∈ ℝ`, every adapted integrable disturbance and every shock, given an
integrable `π_0` known at `0`, the solution (2.25) `LinearFTMP.ruleSol` with the rate
`θ π_t + u_t` is adapted, integrable and solves the rule model, and every adapted integrable
solution with the same `π_0` equals it almost surely at every date. -/
theorem mRule_linear_existsUnique (θ : ℝ) (hu : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (hε : MIsShock S ε) {π0 : Ω → ℝ}
    (h0 : StronglyMeasurable[S.𝓕 0] π0) (h0i : Integrable π0 S.μ) :
    (StronglyAdapted S.𝓕 (LinearFTMP.ruleSol θ u ε π0) ∧
      (∀ t, Integrable (LinearFTMP.ruleSol θ u ε π0 t) S.μ) ∧
      MRuleModel S θ (fun t => θ • LinearFTMP.ruleSol θ u ε π0 t + u t) u ε
        (LinearFTMP.ruleSol θ u ε π0)) ∧
    ∀ q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), StronglyAdapted S.𝓕 q.1 →
      (∀ t, Integrable (q.1 t) S.μ) → q.1 0 =ᵐ[S.μ] π0 → MRuleModel S θ q.2 u ε q.1 →
        ∀ t, q.1 t =ᵐ[S.μ] LinearFTMP.ruleSol θ u ε π0 t ∧
          q.2 t =ᵐ[S.μ] θ • LinearFTMP.ruleSol θ u ε π0 t + u t := by
  have ha : StronglyAdapted S.𝓕 (LinearFTMP.ruleSol θ u ε π0) := fun t => by
    induction t with
    | zero => exact h0
    | succ t ih =>
      exact (((ih.const_smul θ).add (hu t)).mono (S.𝓕.mono (Nat.le_succ t))).sub (hε.1 t)
  have hint : ∀ t, Integrable (LinearFTMP.ruleSol θ u ε π0 t) S.μ := fun t => by
    induction t with
    | zero => exact h0i
    | succ t ih => exact ((ih.smul θ).add (hui t)).sub (hε.2.1 t)
  refine ⟨⟨ha, hint, (mRule_iff S ha hint hu hui hε).mpr fun t =>
    ⟨Eventually.of_forall fun ω => rfl, Eventually.of_forall fun ω => rfl⟩⟩,
    fun q hπ hπi hπ0 hm => ?_⟩
  have h := (mRule_iff S hπ hπi hu hui hε).mp hm
  have hπeq : ∀ t, q.1 t =ᵐ[S.μ] LinearFTMP.ruleSol θ u ε π0 t := by
    intro t
    induction t with
    | zero => exact hπ0
    | succ t ih =>
      filter_upwards [(h t).1, ih] with ω h1 h2
      rw [h1]
      change (θ • q.1 t + u t - ε (t + 1)) ω =
        (θ • LinearFTMP.ruleSol θ u ε π0 t + u t - ε (t + 1)) ω
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2]
  intro t
  refine ⟨hπeq t, ?_⟩
  filter_upwards [(h t).2, hπeq t] with ω h1 h2
  rw [h1]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2]

/-! ### The fiscal shock -/

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: the fiscal shock
`ε_{Σs,t+1} = ΔE_{t+1} PV_{t+1}`, zero at date `0`. -/
noncomputable def mFiscShock (β : ℝ) (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => S.innov t (S.forwardSol β s (t + 1))

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: the fiscal shock is a shock. -/
theorem mFiscShock_isShock (β : ℝ) (s : ℕ → Ω → ℝ) : MIsShock S (mFiscShock S β s) :=
  ⟨fun t => S.stronglyMeasurable_innov t _,
    fun _ => (S.integrable_E _ _).sub (S.integrable_E _ _), fun _ => S.E_innov le_rfl _⟩

/-- Cochrane (2023), eqs. (2.13) and (2.17), pp. 30, 35, on a probability space: in every
equilibrium of `TidyR5Meas`, `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ε_{Σs,t+1}` almost surely, with
the fiscal shock `mFiscShock` (the exact (2.17)). -/
theorem mEquilibrium_fiscShock {β : ℝ} {Bm1 : Ω → ℝ} {s B P : ℕ → Ω → ℝ}
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    (fun ω => B t ω / P t ω * S.innov t (fun ω => P t ω / P (t + 1) ω) ω) =ᵐ[S.μ]
      mFiscShock S β s (t + 1) :=
  mUnexpected_inflation S h t

/-! ### Links to the abstract versions on finite event trees -/

namespace Link

open ExpectationsFiniteTree TreeBridge HouseholdMeasureTVC.Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), p. 21: on a finite tree an almost-sure equality is an equality. -/
theorem eq_of_ae {f g : Ω' → ℝ} (h : f =ᵐ[(treeSystem T).μ] g) : f = g :=
  funext (forall_of_ae T h)

/-- Cochrane (2023), eq. (2.7), p. 22: on a finite tree the measure-theoretic present value
`E_t ∑ βʲ s_{t+j}` is `FiscalMonetary.pv`. -/
theorem tree_forwardSol (β : ℝ) (s : ℕ → Ω' → ℝ) (t : ℕ) :
    (treeSystem T).forwardSol β s t = FiscalMonetary.pv T.toExpectationSystem β s t := by
  change (treeSystem T).E t (MeasExpectationSystem.discSum β s t) = _
  rw [treeE]
  rfl

/-- Cochrane (2023), eq. (2.13), p. 30: on a finite tree the measure-theoretic news operator is
`ExpectationTools.innov`. -/
theorem tree_innov (t : ℕ) (x : Ω' → ℝ) :
    (treeSystem T).innov t x = ExpectationTools.innov T.toExpectationSystem t x := by
  simp only [MeasExpectationSystem.innov, ExpectationTools.innov, treeE]

/-- Cochrane (2023), p. 21: on a finite tree a process is adapted in the measure sense iff it
is adapted in the core sense. -/
theorem tree_adapted_iff (x : ℕ → Ω' → ℝ) :
    StronglyAdapted (treeSystem T).𝓕 x ↔ T.toExpectationSystem.Adapted x :=
  forall_congr' fun t => sm_iff_known T t (x t)

/-- Cochrane (2023), eq. (2.15), p. 31: on a finite tree the measure-theoretic ex-dividend
present value is `FiscalMonetary.pvEx`. -/
theorem tree_pvExM (β : ℝ) (s : ℕ → Ω' → ℝ) (t : ℕ) :
    pvExM (treeSystem T) β s t = FiscalMonetary.pvEx T.toExpectationSystem β s t := by
  rw [FiscalMonetary.pvEx_eq, pvExM, tree_forwardSol, treeE]

/-- Cochrane (2023), §2.4.3, p. 31: on a finite tree the measure-theoretic target equilibrium is
the core one, `mPegP = FiscalMonetary.pegP` and `mPegB = FiscalMonetary.pegB` (no hypotheses). -/
theorem tree_mPegP (β : ℝ) (Bm1 : Ω' → ℝ) (s i : ℕ → Ω' → ℝ) (t : ℕ) :
    mPegP (treeSystem T) β Bm1 s i t = FiscalMonetary.pegP T.toExpectationSystem β Bm1 s i t ∧
      mPegB (treeSystem T) β Bm1 s i t = FiscalMonetary.pegB T.toExpectationSystem β Bm1 s i t := by
  have hP : ∀ t, mPegP (treeSystem T) β Bm1 s i t =
      FiscalMonetary.pegP T.toExpectationSystem β Bm1 s i t := by
    intro t
    induction t with
    | zero =>
      funext ω
      change Bm1 ω / (treeSystem T).forwardSol β s 0 ω = _
      rw [tree_forwardSol]
      rfl
    | succ t ih =>
      funext ω
      change (1 + i t ω) * mPegP (treeSystem T) β Bm1 s i t ω * pvExM (treeSystem T) β s t ω /
        (treeSystem T).forwardSol β s (t + 1) ω = _
      rw [ih, tree_pvExM, tree_forwardSol]
      rfl
  refine ⟨hP t, ?_⟩
  funext ω
  change (1 + i t ω) * mPegP (treeSystem T) β Bm1 s i t ω * pvExM (treeSystem T) β s t ω = _
  rw [hP t, tree_pvExM]
  rfl

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33: on a finite tree, with `β > 0`, the measure-theoretic
equilibrium `MEquilibrium` is exactly the core `FiscalMonetary.Equilibrium` (its condition
`i > −1` is a consequence, `TidyR5BondPrice.bondPricing_rate_gt`). -/
theorem tree_mEquilibrium_iff {β : ℝ} (hβ : 0 < β) {Bm1 : Ω' → ℝ} {s B P i : ℕ → Ω' → ℝ} :
    MEquilibrium (treeSystem T) β Bm1 s B P i ↔
      FiscalMonetary.Equilibrium T.toExpectationSystem β Bm1 s B P i := by
  constructor
  · rintro ⟨hPa, hP, hBa, hia, -, ⟨hv0, hv⟩, hbp⟩
    have hP' : ∀ t ω, 0 < P t ω := fun t => forall_of_ae T (hP t)
    have hbp' : FiscalMonetary.BondPricing T.toExpectationSystem β P i := fun t => by
      have e := eq_of_ae T (hbp t)
      rw [treeE] at e
      exact e
    refine ⟨(tree_adapted_iff T P).1 hPa, hP', (tree_adapted_iff T B).1 hBa,
      (tree_adapted_iff T i).1 hia,
      TidyR5BondPrice.bondPricing_rate_gt T.toExpectationSystem hβ hP' hbp', ⟨?_, fun t => ?_⟩,
      hbp'⟩
    · have e := eq_of_ae T hv0
      rw [tree_forwardSol] at e
      exact e
    · have e := eq_of_ae T (hv t)
      rw [tree_forwardSol] at e
      exact e
  · rintro ⟨hPa, hP, hBa, hia, -, ⟨hv0, hv⟩, hbp⟩
    refine ⟨(tree_adapted_iff T P).2 hPa, fun t => Eventually.of_forall (hP t),
      (tree_adapted_iff T B).2 hBa, (tree_adapted_iff T i).2 hia,
      fun t => Integrable.of_finite, ⟨?_, fun t => ?_⟩, fun t => ?_⟩
    · rw [tree_forwardSol]
      exact Eventually.of_forall fun ω => congrFun hv0 ω
    · rw [tree_forwardSol]
      exact Eventually.of_forall fun ω => congrFun (hv t) ω
    · rw [treeE]
      exact Eventually.of_forall fun ω => congrFun (hbp t) ω

/-- Cochrane (2023), §2.1, pp. 21–22: on a finite tree the measure-theoretic derived equilibrium
`MIsEqm` is exactly the core `Valuation.IsEqm`. -/
theorem tree_mIsEqm_iff {β : ℝ} {Bm s P Q : ℕ → Ω' → ℝ} :
    MIsEqm (treeSystem T) β Bm s P Q ↔ Valuation.IsEqm T.toExpectationSystem β Bm s P Q := by
  constructor
  · rintro ⟨hP, hPa, hQ, hflow, htvc⟩
    refine ⟨fun t => forall_of_ae T (hP t), (tree_adapted_iff T P).1 hPa, fun t => ?_,
      fun t => forall_of_ae T (hflow t), fun t ω => ?_⟩
    · have e := eq_of_ae T (hQ t)
      rw [treeE] at e
      exact e
    · have e := forall_of_ae T (htvc t) ω
      simp only [treeE] at e
      exact e
  · rintro ⟨hP, hPa, hQ, hflow, htvc⟩
    refine ⟨fun t => Eventually.of_forall (hP t), (tree_adapted_iff T P).2 hPa, fun t => ?_,
      fun t => Eventually.of_forall (hflow t), fun t => Eventually.of_forall fun ω => ?_⟩
    · rw [treeE]
      exact Eventually.of_forall fun ω => congrFun (hQ t) ω
    · simp only [treeE]
      exact htvc t ω

/-- Cochrane (2023), p. 40: on a finite tree a measure-theoretic shock is a core shock
(`LinearFTMP.IsShock`). -/
theorem tree_mIsShock_iff (ε : ℕ → Ω' → ℝ) :
    MIsShock (treeSystem T) ε ↔ LinearFTMP.IsShock T.toExpectationSystem ε := by
  constructor
  · rintro ⟨hm, -, hE⟩
    refine ⟨fun t => (sm_iff_known T (t + 1) _).1 (hm t), fun t => ?_⟩
    have e := eq_of_ae T (hE t)
    rw [treeE] at e
    exact e
  · rintro ⟨hm, hE⟩
    refine ⟨fun t => (sm_iff_known T (t + 1) _).2 (hm t), fun t => Integrable.of_finite,
      fun t => ?_⟩
    rw [treeE, hE t]

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35: on a finite tree the measure-theoretic peg model
is `LinearFTMP.PegModel`. -/
theorem tree_mPegModel_iff (i ε π : ℕ → Ω' → ℝ) :
    MPegModel (treeSystem T) i ε π ↔ LinearFTMP.PegModel T.toExpectationSystem i ε π := by
  constructor
  · intro h t
    have e1 := eq_of_ae T (h t).1
    have e2 := eq_of_ae T (h t).2
    rw [treeE] at e1
    rw [tree_innov] at e2
    exact ⟨e1, e2⟩
  · intro h t
    rw [treeE, tree_innov]
    exact ⟨Eventually.of_forall fun ω => congrFun (h t).1 ω,
      Eventually.of_forall fun ω => congrFun (h t).2 ω⟩

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: on a finite tree the measure-theoretic rule model
is `LinearFTMP.RuleModel`. -/
theorem tree_mRuleModel_iff (θ : ℝ) (i u ε π : ℕ → Ω' → ℝ) :
    MRuleModel (treeSystem T) θ i u ε π ↔ LinearFTMP.RuleModel T.toExpectationSystem θ i u ε π := by
  constructor
  · intro h t
    have e1 := eq_of_ae T (h t).1
    have e2 := eq_of_ae T (h t).2.1
    rw [treeE] at e1
    rw [tree_innov] at e2
    exact ⟨e1, e2, eq_of_ae T (h t).2.2⟩
  · intro h t
    rw [treeE, tree_innov]
    exact ⟨Eventually.of_forall fun ω => congrFun (h t).1 ω,
      Eventually.of_forall fun ω => congrFun (h t).2.1 ω,
      Eventually.of_forall fun ω => congrFun (h t).2.2 ω⟩

/-- Cochrane (2023), eq. (2.17), p. 35: on a finite tree the measure-theoretic fiscal shock is
the core news about the present value, and for bounded surpluses (`0 ≤ β < 1`) it is the core
fiscal shock `LinearFTMP.pvNews`. -/
theorem tree_mFiscShock {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω' → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    mFiscShock (treeSystem T) β s (t + 1) =
        ExpectationTools.innov T.toExpectationSystem t
          (FiscalMonetary.pv T.toExpectationSystem β s (t + 1)) ∧
      mFiscShock (treeSystem T) β s (t + 1) = LinearFTMP.pvNews T.toExpectationSystem β s t := by
  have e : mFiscShock (treeSystem T) β s (t + 1) =
      ExpectationTools.innov T.toExpectationSystem t
        (FiscalMonetary.pv T.toExpectationSystem β s (t + 1)) := by
    change (treeSystem T).innov t ((treeSystem T).forwardSol β s (t + 1)) = _
    rw [tree_innov, tree_forwardSol]
  refine ⟨e, ?_⟩
  rw [e, FiscalMonetary.news_pv_succ,
    GeneralLinks.innov_epv_eq_pvNews T.toExpectationSystem hβ0 hβ1 hs t]

end Link

end Cochrane.IntertemporalModel.TidyR5MeasLinear
