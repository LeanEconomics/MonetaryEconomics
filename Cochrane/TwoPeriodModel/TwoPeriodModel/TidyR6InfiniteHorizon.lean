/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.TwoPeriod
import TwoPeriodModel.ForwardSolution

/-!
# The infinite-horizon analogue of the two-period model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.3, eqs. (1.2)–(1.5),
pp. 7–8 (flow condition, bond price, valuation equation), §1.4, p. 9 (bond sales without
surpluses), and the infinite-horizon comparison announced on p. 4 ("I add these elements
later"). The chapter's model ends on day 1; this module states and proves its main claims with
an infinite horizon in the same setting: an arbitrary `ExpectationSystem` with
`ExpectationSystem.PullOut`, so
perfect foresight and every finite event tree.

## The model

Dates `t = 0, 1, 2, …`; `Bm t = B_{t−1}` is the nominal debt coming due at `t` (`B_{−1}` known
at 0, `B_t` known at `t`), `s` the real surplus (bounded, adapted), `P` the price level
(positive, adapted) and `Q` the bond price. At every date:
* the flow condition (1.2) `B_{t−1} = P_t s_t + Q_t B_t` (`Flow`);
* the bond-pricing equation (1.3) `Q_t = βE_t(P_t/P_{t+1})` (`BondPrice`);
* the transversality condition `β^T E_t[B_{t+T−1}/P_{t+T}] → 0` (`TVC`), the explicit limit
  that replaces the last day.

`Equilibrium` collects these. The price level is *determined* when exactly one pair `(P, Q)`
is an equilibrium given `(B, s)`.

## Main results

* `realDebt_rec`, `flow_of_rec`: given (1.3), the flow condition is the real-debt recursion
  `v_t = s_t + βE_t v_{t+1}`, `v_t = B_{t−1}/P_t`.
* `tendsto_tvc_term`: `β^T E_t v_{t+T} → v_t − ∑_j β^j E_t s_{t+j}` for every solution of the
  recursion, so `tvc_iff_valuation`: **the infinite-horizon valuation equation**
  `B_{t−1}/P_t = ∑_{j≥0} β^j E_t s_{t+j}` (the analogue of (1.5)) holds at every date iff the
  transversality condition holds; necessity and sufficiency.
* `equilibrium_iff`, `equilibrium_existsUnique`: **the price level is determined by surpluses**:
  with positive debt and a positive present value at every date there is exactly one
  equilibrium, `P_t = B_{t−1}/∑_j β^j E_t s_{t+j}`; `no_equilibrium_of_pv_nonpos` otherwise.
* `price0_eq`, `price0_eq_of_pv_eq`, `price0_indep_debt`, `price1_scales_with_debt`: `P₀`
  depends on surpluses only through their present value and not at all on later debt sales;
  selling more debt `B₀` with unchanged surpluses scales `P₁` one for one (the analogues of
  (1.5)–(1.8) and of the share split of p. 9).
-/

namespace Cochrane.TwoPeriodModel.TidyR6InfiniteHorizon

open Filter Topology Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.ForwardSolution

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (1.2), p. 8, at date `t`: `B_{t−1} = P_t s_t + Q_t B_t`, with
`Bm t = B_{t−1}`. -/
def Flow (Bm s P Q : ℕ → Ω → ℝ) (t : ℕ) : Prop := Bm t = P t * s t + Q t * Bm (t + 1)

/-- Cochrane (2023), eq. (1.3), p. 8, at date `t`: `Q_t = βE_t(P_t/P_{t+1})`. -/
def BondPrice (β : ℝ) (P Q : ℕ → Ω → ℝ) (t : ℕ) : Prop := Q t = β • 𝔼.E t (P t / P (t + 1))

/-- Cochrane (2023), eq. (1.5), p. 8: the real value of the debt coming due at `t`,
`v_t = B_{t−1}/P_t`. -/
noncomputable def realDebt (Bm P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := Bm t / P t

/-- Cochrane (2023), §1.1, p. 4 (the last day, replaced by a limit): the transversality
condition `β^T E_t[B_{t+T−1}/P_{t+T}] → 0` as `T → ∞`, at every date and state. -/
def TVC (β : ℝ) (Bm P : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (realDebt Bm P (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), §1.3, pp. 7–8, with an infinite horizon: given the debt policy `Bm` and
surpluses `s`, `(P, Q)` is an equilibrium when the price level is positive and adapted, and the
flow condition, the bond price and the transversality condition hold. -/
def Equilibrium (β : ℝ) (Bm s P Q : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ 𝔼.Adapted P ∧ (∀ t, Flow Bm s P Q t) ∧ (∀ t, BondPrice 𝔼 β P Q t) ∧
    TVC 𝔼 β Bm P

/-- Cochrane (2023), eq. (1.5), p. 8, infinite horizon: the present value of surpluses
`∑_{j≥0} β^j E_t s_{t+j}`. -/
noncomputable def pvInf (β : ℝ) (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := 𝔼.forwardSeries β s

/-- Cochrane (2023), §1.3, p. 8: the debt policy is known when issued: `B_{−1}` at date 0 and
`B_t` at date `t`. -/
def DebtKnown (Bm : ℕ → Ω → ℝ) : Prop := Known 𝔼 0 (Bm 0) ∧ ∀ t, Known 𝔼 t (Bm (t + 1))

/-! ### Flow condition = real-debt recursion -/

/-- Cochrane (2023), eqs. (1.2)–(1.3), p. 8: debt coming due at `t` is known at `t`. -/
theorem debtKnown_at {Bm : ℕ → Ω → ℝ} (hB : DebtKnown 𝔼 Bm) (t : ℕ) : Known 𝔼 t (Bm t) := by
  cases t with
  | zero => exact hB.1
  | succ t => exact known_mono 𝔼 (Nat.le_succ t) (hB.2 t)

/-- Cochrane (2023), eqs. (1.2)–(1.3), p. 8: under (1.3) the revenue from bond sales is
`Q_tB_t = P_t · βE_t v_{t+1}` (`P` adapted and nonzero, `B_t` known at `t`,
`ExpectationSystem.PullOut`). -/
theorem revenue_eq (hPO : 𝔼.PullOut) {β : ℝ} {Bm P Q : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hB : DebtKnown 𝔼 Bm) (t : ℕ) (hQ : BondPrice 𝔼 β P Q t) :
    Q t * Bm (t + 1) = P t * (β • 𝔼.E t (realDebt Bm P (t + 1))) := by
  rw [hQ]
  have e1 : 𝔼.E t (Bm (t + 1) * (P t / P (t + 1))) = Bm (t + 1) * 𝔼.E t (P t / P (t + 1)) :=
    hPO t _ _ (hB.2 t)
  have e2 : 𝔼.E t (P t * realDebt Bm P (t + 1)) = P t * 𝔼.E t (realDebt Bm P (t + 1)) :=
    hPO t _ _ (hPa t)
  have e3 : Bm (t + 1) * (P t / P (t + 1)) = P t * realDebt Bm P (t + 1) := by
    funext ω
    simp only [realDebt, Pi.mul_apply, Pi.div_apply]
    ring
  rw [e3, e2] at e1
  funext ω
  have := congrFun e1 ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  linear_combination (-β) * this

/-- Cochrane (2023), eqs. (1.2)–(1.5), p. 8, at every date: the flow condition and the bond
price give the real-debt recursion `v_t = s_t + βE_t v_{t+1}` (`P > 0` adapted, debt known,
`ExpectationSystem.PullOut`). -/
theorem realDebt_rec (hPO : 𝔼.PullOut) {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P) (hB : DebtKnown 𝔼 Bm) (t : ℕ) (hF : Flow Bm s P Q t)
    (hQ : BondPrice 𝔼 β P Q t) :
    realDebt Bm P t = s t + β • 𝔼.E t (realDebt Bm P (t + 1)) := by
  have hr := revenue_eq 𝔼 hPO hPa hB t hQ
  funext ω
  have e1 := congrFun hF ω
  have e2 := congrFun hr ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  have := (hP t ω).ne'
  change Bm t ω / P t ω = _
  rw [e1, e2]
  field_simp

/-- Cochrane (2023), eqs. (1.2)–(1.5), p. 8, conversely: the bond price and the real-debt
recursion give the flow condition. -/
theorem flow_of_rec (hPO : 𝔼.PullOut) {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P) (hB : DebtKnown 𝔼 Bm) (t : ℕ) (hQ : BondPrice 𝔼 β P Q t)
    (hv : realDebt Bm P t = s t + β • 𝔼.E t (realDebt Bm P (t + 1))) : Flow Bm s P Q t := by
  have hr := revenue_eq 𝔼 hPO hPa hB t hQ
  funext ω
  have e1 := congrFun hv ω
  have e2 := congrFun hr ω
  simp only [realDebt, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    Pi.div_apply] at e1 e2 ⊢
  have := (hP t ω).ne'
  rw [div_eq_iff this] at e1
  rw [e1, e2]
  ring

/-- Cochrane (2023), eq. (1.5), p. 8: the real debt is adapted when the price level is adapted
and nonzero and the debt is known (`ExpectationSystem.PullOut`). -/
theorem realDebt_adapted (hPO : 𝔼.PullOut) {Bm P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P) (hB : DebtKnown 𝔼 Bm) : 𝔼.Adapted (realDebt Bm P) := fun t =>
  known_div 𝔼 hPO (debtKnown_at 𝔼 hB t) (hPa t) fun ω => (hP t ω).ne'

/-! ### The valuation equation and the transversality condition -/

/-- Cochrane (2023), eq. (1.5), p. 8, iterated forward: for every adapted solution of
`v_t = s_t + βE_t v_{t+1}` (adapted `s`), the discounted terminal value
`β^T E_t v_{t+T}` converges to `v_t − ∑_{j≥0} β^j E_t s_{t+j}` (`|β| < 1`, `s` bounded). -/
theorem tendsto_tvc_term {β M : ℝ} (hβ : |β| < 1) {s v : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hv : ∀ t, v t = s t + β • 𝔼.E t (v (t + 1))) (t : ℕ) (ω : Ω) :
    Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 (v t ω - pvInf 𝔼 β s t ω)) := by
  have hsol : Solves 𝔼 β s v := fun t => by rw [hv t]; abel
  have hlim := (summable_A16 𝔼 hβ hs t ω).hasSum.tendsto_sum_nat
  have heq : ∀ T : ℕ, β ^ T * 𝔼.E t (v (t + T)) ω =
      v t ω - ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (s (t + j)) ω := by
    intro T
    have h := congrFun (iterate_A15 𝔼 hsa hsol t T) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    linarith
  simp_rw [heq]
  exact (tendsto_const_nhds (x := v t ω)).sub hlim

/-- Cochrane (2023), eq. (1.5), p. 8, **infinite-horizon valuation equation, necessity and
sufficiency**: for an adapted solution of `v_t = s_t + βE_t v_{t+1}` (bounded adapted `s`,
`|β| < 1`), `v_t = ∑_{j≥0} β^j E_t s_{t+j}` at every date iff `β^T E_t v_{t+T} → 0` at every
date and state. -/
theorem tvc_iff_valuation {β M : ℝ} (hβ : |β| < 1) {s v : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hv : ∀ t, v t = s t + β • 𝔼.E t (v (t + 1))) :
    (∀ t ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) ↔
      ∀ t, v t = pvInf 𝔼 β s t := by
  constructor
  · intro h t
    funext ω
    have := tendsto_nhds_unique (tendsto_tvc_term 𝔼 hβ hs hsa hv t ω) (h t ω)
    linarith
  · intro h t ω
    have := tendsto_tvc_term 𝔼 hβ hs hsa hv t ω
    rwa [h t, sub_self] at this

/-- Cochrane (2023), eq. (1.5), p. 8: the present value satisfies
`pv_t = s_t + βE_t pv_{t+1}` (`|β| < 1`, `s` bounded adapted). -/
theorem pvInf_rec {β M : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (hsa : 𝔼.Adapted s) (t : ℕ) :
    pvInf 𝔼 β s t = s t + β • 𝔼.E t (pvInf 𝔼 β s (t + 1)) := by
  unfold pvInf
  rw [forwardSeries_solves_abs 𝔼 hβ hs hsa t]
  abel

/-- Cochrane (2023), eq. (1.5), p. 8: the present value is adapted. -/
theorem pvInf_adapted {β M : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) :
    𝔼.Adapted (pvInf 𝔼 β s) :=
  forwardSeries_adapted_abs 𝔼 hβ hs

/-! ### The price level is determined by surpluses -/

/-- Cochrane (2023), eq. (1.5), p. 8, infinite horizon: in every equilibrium the valuation
equation `B_{t−1}/P_t = ∑_j β^j E_t s_{t+j}` holds at every date (`|β| < 1`; `s` bounded
adapted; debt known; `ExpectationSystem.PullOut`). -/
theorem valuation_of_equilibrium (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1)
    {Bm s P Q : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hB : DebtKnown 𝔼 Bm) (he : Equilibrium 𝔼 β Bm s P Q) (t : ℕ) :
    realDebt Bm P t = pvInf 𝔼 β s t := by
  obtain ⟨hP, hPa, hF, hQ, hT⟩ := he
  exact (tvc_iff_valuation 𝔼 hβ hs hsa
    (fun t => realDebt_rec 𝔼 hPO hP hPa hB t (hF t) (hQ t))).mp hT t

/-- Cochrane (2023), §1.3, pp. 7–8, infinite horizon: **characterisation of the equilibrium.**
With `|β| < 1`, bounded adapted surpluses, positive known debt and `ExpectationSystem.PullOut`,
`(P, Q)` is an
equilibrium iff `P_t = B_{t−1}/∑_j β^j E_t s_{t+j}`, with a positive present value, and
`Q_t = βE_t(P_t/P_{t+1})` at every date. -/
theorem equilibrium_iff (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1) {Bm s P Q : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hBpos : ∀ t ω, 0 < Bm t ω)
    (hB : DebtKnown 𝔼 Bm) :
    Equilibrium 𝔼 β Bm s P Q ↔
      (∀ t ω, 0 < pvInf 𝔼 β s t ω) ∧ (∀ t, P t = Bm t / pvInf 𝔼 β s t) ∧
        ∀ t, BondPrice 𝔼 β P Q t := by
  constructor
  · intro he
    have hv := valuation_of_equilibrium 𝔼 hPO hβ hs hsa hB he
    obtain ⟨hP, -, -, hQ, -⟩ := he
    have hpos : ∀ t ω, 0 < pvInf 𝔼 β s t ω := fun t ω => by
      rw [← hv t]; exact div_pos (hBpos t ω) (hP t ω)
    refine ⟨hpos, fun t => ?_, hQ⟩
    funext ω
    have := congrFun (hv t) ω
    simp only [realDebt, Pi.div_apply] at this ⊢
    rw [← this]
    field_simp [(hP t ω).ne', (hBpos t ω).ne']
  · rintro ⟨hpos, hPeq, hQ⟩
    have hP : ∀ t ω, 0 < P t ω := fun t ω => by
      rw [hPeq t]; exact div_pos (hBpos t ω) (hpos t ω)
    have hPa : 𝔼.Adapted P := fun t => by
      rw [hPeq t]
      exact known_div 𝔼 hPO (debtKnown_at 𝔼 hB t) (pvInf_adapted 𝔼 hβ hs t)
        fun ω => (hpos t ω).ne'
    have hvp : ∀ t, realDebt Bm P t = pvInf 𝔼 β s t := fun t => by
      funext ω
      simp only [realDebt, Pi.div_apply, hPeq t]
      field_simp [(hpos t ω).ne', (hBpos t ω).ne']
    have hrec : ∀ t, realDebt Bm P t = s t + β • 𝔼.E t (realDebt Bm P (t + 1)) := fun t => by
      rw [hvp t, hvp (t + 1)]
      exact pvInf_rec 𝔼 hβ hs hsa t
    exact ⟨hP, hPa, fun t => flow_of_rec 𝔼 hPO hP hPa hB t (hQ t) (hrec t), hQ,
      (tvc_iff_valuation 𝔼 hβ hs hsa hrec).mpr hvp⟩

/-- Cochrane (2023), §1.3, pp. 7–8, infinite horizon: **the fiscal theory determines the price
level.** With `|β| < 1`, bounded adapted surpluses whose present value is positive at every
date and state, positive known debt and `ExpectationSystem.PullOut`, there is exactly one
equilibrium `(P, Q)`,
namely `P_t = B_{t−1}/∑_j β^j E_t s_{t+j}`. -/
theorem equilibrium_existsUnique (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1)
    {Bm s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm) (hpos : ∀ t ω, 0 < pvInf 𝔼 β s t ω) :
    ∃! x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), Equilibrium 𝔼 β Bm s x.1 x.2 := by
  set P : ℕ → Ω → ℝ := fun t => Bm t / pvInf 𝔼 β s t
  refine ⟨(P, fun t => β • 𝔼.E t (P t / P (t + 1))), ?_, ?_⟩
  · exact (equilibrium_iff 𝔼 hPO hβ hs hsa hBpos hB).mpr ⟨hpos, fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨P', Q'⟩ h
    obtain ⟨-, hP', hQ'⟩ := (equilibrium_iff 𝔼 hPO hβ hs hsa hBpos hB).mp h
    have e1 : P' = P := funext hP'
    simp only at e1 hQ'
    subst e1
    exact Prod.ext rfl (funext hQ')

/-- Cochrane (2023), eq. (1.5), p. 8 (error E3 of the chapter, infinite horizon): if the
present value of surpluses is not positive at some date and state while the debt is positive,
there is no equilibrium. -/
theorem no_equilibrium_of_pv_nonpos (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1)
    {Bm s P Q : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hB : DebtKnown 𝔼 Bm) {t : ℕ} {ω : Ω} (hBpos : 0 < Bm t ω)
    (hpv : pvInf 𝔼 β s t ω ≤ 0) : ¬ Equilibrium 𝔼 β Bm s P Q := by
  intro he
  have hv := congrFun (valuation_of_equilibrium 𝔼 hPO hβ hs hsa hB he t) ω
  have : 0 < realDebt Bm P t ω := div_pos hBpos (he.1 t ω)
  rw [hv] at this
  linarith

/-- Cochrane (2023), eq. (1.5), p. 8, infinite horizon: in every equilibrium
`P₀ = B_{−1}/∑_j β^j E_0 s_j`. -/
theorem price0_eq (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1) {Bm s P Q : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hBpos : ∀ t ω, 0 < Bm t ω)
    (hB : DebtKnown 𝔼 Bm) (he : Equilibrium 𝔼 β Bm s P Q) : P 0 = Bm 0 / pvInf 𝔼 β s 0 :=
  ((equilibrium_iff 𝔼 hPO hβ hs hsa hBpos hB).mp he).2.1 0

/-- Cochrane (2023), p. 8, infinite horizon: the price level `P₀` depends on surpluses only
through their present value: two surplus processes with the same date-0 present value give the
same equilibrium `P₀`. -/
theorem price0_eq_of_pv_eq (hPO : 𝔼.PullOut) {β M M' : ℝ} (hβ : |β| < 1)
    {Bm s s' P Q P' Q' : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hs' : ∀ t ω, |s' t ω| ≤ M') (hsa' : 𝔼.Adapted s') (hBpos : ∀ t ω, 0 < Bm t ω)
    (hB : DebtKnown 𝔼 Bm) (hsame : pvInf 𝔼 β s 0 = pvInf 𝔼 β s' 0)
    (he : Equilibrium 𝔼 β Bm s P Q) (he' : Equilibrium 𝔼 β Bm s' P' Q') : P 0 = P' 0 := by
  rw [price0_eq 𝔼 hPO hβ hs hsa hBpos hB he, price0_eq 𝔼 hPO hβ hs' hsa' hBpos hB he', hsame]

/-- Cochrane (2023), §1.4, p. 9 (selling more debt without changing surpluses does not move
`P₀`), infinite horizon: two debt policies with the same initial debt `B_{−1}` and the same
surpluses have the same equilibrium `P₀`, however different the later debt sales. -/
theorem price0_indep_debt (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1)
    {Bm Bm' s P Q P' Q' : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm) (hBpos' : ∀ t ω, 0 < Bm' t ω)
    (hB' : DebtKnown 𝔼 Bm') (h0 : Bm 0 = Bm' 0) (he : Equilibrium 𝔼 β Bm s P Q)
    (he' : Equilibrium 𝔼 β Bm' s P' Q') : P 0 = P' 0 := by
  rw [price0_eq 𝔼 hPO hβ hs hsa hBpos hB he, price0_eq 𝔼 hPO hβ hs hsa hBpos' hB' he', h0]

/-- Cochrane (2023), §1.4, p. 9 (the share split: "doubling debt `B₀` doubles the price level
`P₁`"), infinite horizon: in equilibrium `P_t/B_{t−1} = 1/∑_j β^j E_t s_{t+j}` depends only on
surpluses, so scaling the debt coming due at `t` by `λ` with unchanged surpluses scales
`P_t` by `λ`. -/
theorem price1_scales_with_debt (hPO : 𝔼.PullOut) {β M lam : ℝ} (hβ : |β| < 1)
    {Bm Bm' s P Q P' Q' : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (hsa : 𝔼.Adapted s) (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm)
    (hBpos' : ∀ t ω, 0 < Bm' t ω) (hB' : DebtKnown 𝔼 Bm') {t : ℕ}
    (hscale : Bm' t = lam • Bm t) (he : Equilibrium 𝔼 β Bm s P Q)
    (he' : Equilibrium 𝔼 β Bm' s P' Q') : P' t = lam • P t := by
  rw [((equilibrium_iff 𝔼 hPO hβ hs hsa hBpos hB).mp he).2.1 t,
    ((equilibrium_iff 𝔼 hPO hβ hs hsa hBpos' hB').mp he').2.1 t, hscale]
  funext ω
  simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Cochrane.TwoPeriodModel.TidyR6InfiniteHorizon
