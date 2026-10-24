/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.Environment
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# The government debt valuation equation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 22–23,
equations (2.5)–(2.8), and Online Appendix A1.1 "The transversality condition", pp. 554–556,
equations (1.1)–(1.3).

Real debt is `x_t = B_{t−1}/P_t` (`Bm t / P t` in the indexing of `Environment`). The flow
condition (2.5) is `x_t = s_t + β E_t x_{t+1}` (`FlowX`), the transversality condition (2.6)
is `lim_N β^N E_t x_{t+N} = 0` (`TVC`; `tvc_iff_tvcBook` relates it to the book's form
`lim_T β^T E_t x_T = 0`), and the present value of surpluses is the genuine infinite sum
`pv_t = ∑_{j ≥ 0} β^j E_t s_{t+j}` (`pv`).

## Hypotheses made explicit

Surpluses are signed, so the present value is controlled by *absolute* summability
`∑_j β^j E_t|s_{t+j}| < ∞` at every date and state (`AbsSummable`), not by nonnegativity; and
`E_t` is interchanged with infinite sums through conditional monotone convergence
(`MonotoneConvergence`, restated from the Woodford Chapter 2 project, true for perfect foresight
and every finite event tree), applied to the positive and negative parts of `s`.

## Main results

* `telescope`: `x_t = ∑_{j<N} β^j E_t s_{t+j} + β^N E_t x_{t+N}`.
* `valuation_iff` (2.5)–(2.7): the flow condition at every date plus the TVC at every date
  holds iff `x_t = ∑_j β^j E_t s_{t+j}` at every date (both directions).
* `IsEqm`: an equilibrium (positive adapted price level, bond price (2.3), flow (2.4), TVC (2.6)),
  and the fiscal-theory determination of the price level: `eqm_price_eq` (`P_t = B_{t−1}/pv_t`),
  `eqm_of_pv_pos` (existence), `existsUnique_eqm` (the price level and bond price are unique
  given debt and surpluses), `no_eqm_of_pv_nonpos` (no equilibrium if some `pv_t ≤ 0`).
* `hh_pv_iff` (2.8) and `excess_demand_of_gap` (p. 23).
* A1.1: `tvc_iff_noPonzi_and_optimal` (the box on p. 554), `noPonzi_of_nonneg_debt`,
  `hh_iterate` ((1.1)–(1.2), with exponent `T + 1`; the printed `R^{−T}` is refuted by
  `printed_A1_2_false`), `const_explodes`, `const_terminal_limit`, `const_tvc_iff`
  (the A1.1 example, p. 555, under uncertainty too), and the perfect-foresight deviation argument
  (1.3): `deviation_closed_form`, `deviation_feasible`, `deviation_improves`,
  `deviation_optimal`, `tooLow_not_equilibrium`; `bubble_deviation` (the general version: a
  pathwise bubble can be consumed).
* `tvc_of_optimal`, `valuation_of_optimal` (p. 22): under perfect foresight, household
  optimisation implies the transversality condition (2.6), and hence (2.7).
* `deviation_optimal_concave` (A1 p. 556) under the book's assumption (concave increasing `u`),
  via `concave_le_tangent` and `deriv_nonneg_of_monotone`.
* Under uncertainty (finite state space; `SFeasible`, `expUtil`, `SOptimal` state-contingent
  plans maximising `∑_t β^t E_0 u(c_t)`): `euler_of_optimal_stoch` (the conditional Euler
  equation `Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]`, by the variational argument along
  date-`t` measurable deviations), `tvc_of_optimal_stoch` (optimisation implies (2.6) at every
  date and state, given information that stops growing, `InfoStable`), and
  `valuation_of_optimal_stoch` ((2.7)). The extra hypotheses `Faithful` and `InfoStable` hold
  for every finite event tree (`finiteTree_faithful`, `finiteTree_infoStable`).
-/

namespace Cochrane.IntertemporalModel.Valuation

open Filter Topology Environment ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Flow, transversality and present value -/

/-- Cochrane (2023), eq. (2.5), p. 22: the real flow condition `x_t = s_t + β E_t x_{t+1}` at
every date, for real debt `x_t = B_{t−1}/P_t` (see `Environment.flow_iff_real_x`). -/
def FlowX (β : ℝ) (x s : ℕ → Ω → ℝ) : Prop := ∀ t, x t = s t + β • 𝔼.E t (x (t + 1))

/-- Cochrane (2023), eq. (2.6), p. 22: the transversality condition looking forward from date
`t`, `lim_{N→∞} β^N E_t x_{t+N} = 0` in every state. -/
def TVC (β : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun N : ℕ => β ^ N * 𝔼.E t (x (t + N)) ω) atTop (𝓝 0)

/-- Cochrane (2023), eq. (2.6), p. 22, exactly as printed: `lim_{T→∞} E_t β^T B_{T−1}/P_T = 0`,
i.e. `lim_T β^T E_t x_T = 0`. -/
def TVCBook (β : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (x T) ω) atTop (𝓝 0)

/-- Cochrane (2023), eq. (2.6), p. 22: for `β > 0` the printed form `lim_T β^T E_t x_T = 0` and
the form `lim_N β^N E_t x_{t+N} = 0` are equivalent (they differ by the factor `β^t`). -/
theorem tvc_iff_tvcBook {β : ℝ} (hβ : 0 < β) (x : ℕ → Ω → ℝ) (t : ℕ) :
    TVC 𝔼 β x t ↔ TVCBook 𝔼 β x t := by
  have hb : β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
  constructor
  · intro h ω
    rw [← Filter.tendsto_add_atTop_iff_nat t]
    have := (h ω).const_mul (β ^ t)
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    rw [add_comm N t, pow_add]
    ring
  · intro h ω
    have h2 := ((Filter.tendsto_add_atTop_iff_nat t).mpr (h ω)).const_mul (β ^ t)⁻¹
    rw [mul_zero] at h2
    refine h2.congr fun N => ?_
    rw [add_comm N t, pow_add]
    field_simp

/-- Cochrane (2023), eq. (2.7), p. 22 (signed surpluses): absolute summability
`∑_j β^j E_t|s_{t+j}| < ∞` at every date and in every state. -/
def AbsSummable (β : ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable fun j : ℕ => β ^ j * 𝔼.E t (fun ω' => |s (t + j) ω'|) ω

/-- Cochrane (2023), eq. (2.7), p. 22: the present value of surpluses
`E_t ∑_{j ≥ 0} β^j s_{t+j}`, written as the genuine infinite sum `∑_j β^j E_t s_{t+j}`. This is
the core forward series `𝔼.forwardSeries β s t` under its book name (the one present-value
definition of the chapter; `FiscalMonetary.pv` is the ex-post form `E_t ∑ β^j s_{t+j}`, equal to
it under the hypotheses of `GeneralLinks.fm_pv_eq_pv`). -/
noncomputable abbrev pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.forwardSeries β s t

/-- Cochrane (2023), eq. (2.7), p. 22: the present value in coordinates,
`pv_t(ω) = ∑_j β^j E_t s_{t+j}(ω)`. -/
theorem pv_apply (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    pv 𝔼 β s t ω = ∑' j : ℕ, β ^ j * 𝔼.E t (s (t + j)) ω := rfl

/-- Cochrane (2023), eq. (2.7), p. 22: under absolute summability the present-value series
converges in every state. -/
theorem summable_terms {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s)
    (t : ℕ) (ω : Ω) : Summable fun j : ℕ => β ^ j * 𝔼.E t (s (t + j)) ω :=
  Summable.of_norm_bounded (hs t ω) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (abs_E_le_E_abs 𝔼 t _ ω) (pow_nonneg hβ j)

/-- Cochrane (2023), eq. (2.5), p. 22: with adapted surpluses, real debt satisfying the flow
condition is known at each date. -/
theorem adapted_of_flow {β : ℝ} {x s : ℕ → Ω → ℝ} (hsad : 𝔼.Adapted s) (h : FlowX 𝔼 β x s) :
    𝔼.Adapted x := by
  intro t
  calc 𝔼.E t (x t) = 𝔼.E t (s t + β • 𝔼.E t (x (t + 1))) := by rw [← h t]
    _ = s t + β • 𝔼.E t (x (t + 1)) := by rw [map_add, map_smul, hsad t, 𝔼.E_E_self]
    _ = x t := (h t).symm

/-- Cochrane (2023), p. 22 ("iterate (2.5)") and Online Appendix A1.1, p. 555: the exact
finite-horizon identity `x_t = ∑_{j<N} β^j E_t s_{t+j} + β^N E_t x_{t+N}`. -/
theorem telescope {β : ℝ} {x s : ℕ → Ω → ℝ} (h : FlowX 𝔼 β x s) {t : ℕ}
    (hxt : 𝔼.E t (x t) = x t) (N : ℕ) :
    x t = (∑ j ∈ Finset.range N, β ^ j • 𝔼.E t (s (t + j))) + β ^ N • 𝔼.E t (x (t + N)) := by
  induction N with
  | zero => simp [hxt]
  | succ N ih =>
    have step : 𝔼.E t (x (t + N)) = 𝔼.E t (s (t + N)) + β • 𝔼.E t (x (t + N + 1)) := by
      have := congrArg (𝔼.E t) (h (t + N))
      rwa [map_add, map_smul, 𝔼.tower (Nat.le_add_right t N)] at this
    rw [ih, step, Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ, ← add_assoc]
    rfl

/-- Cochrane (2023), eqs. (2.5)–(2.7), p. 22 (sufficiency): the flow condition at every date
and the TVC at `t` give `x_t = ∑_j β^j E_t s_{t+j}`, as a genuine convergent series. -/
theorem hasSum_of_flow_tvc {β : ℝ} (hβ : 0 ≤ β) {x s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (h : FlowX 𝔼 β x s) {t : ℕ} (htvc : TVC 𝔼 β x t) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + j)) ω) (x t ω) := by
  have hxt := adapted_of_flow 𝔼 hsad h t
  have hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω =
      x t ω - β ^ N * 𝔼.E t (x (t + N)) ω := by
    intro N
    have := congrFun (telescope 𝔼 h hxt N) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hlim : Tendsto (fun N => ∑ j ∈ Finset.range N, β ^ j * 𝔼.E t (s (t + j)) ω) atTop
      (𝓝 (x t ω)) := by
    simp_rw [hpart]
    simpa using (tendsto_const_nhds (x := x t ω)).sub (htvc ω)
  have hS := summable_terms 𝔼 hβ hs t ω
  rw [tendsto_nhds_unique hlim hS.hasSum.tendsto_sum_nat]
  exact hS.hasSum

/-- Cochrane (2023), p. 22 (signed surpluses), the step "iterate (2.5)" in the other
direction: the expectation at `t` of the date-`(t+N)` present value is the tail
`∑_j β^j E_t s_{t+N+j}`. Proof: split `s` into positive and negative parts and apply
conditional monotone convergence to each. -/
theorem hasSum_E_pv (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (t N : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ j * 𝔼.E t (s (t + N + j)) ω) (𝔼.E t (pv 𝔼 β s (t + N)) ω) := by
  set sp : ℕ → Ω → ℝ := fun n ω => max (s n ω) 0 with hsp
  set sn : ℕ → Ω → ℝ := fun n ω => max (-s n ω) 0 with hsn
  have hsplit : ∀ n, s n = sp n - sn n := fun n => by
    funext ω
    simp [hsp, hsn, max_zero_sub_max_neg_zero_eq_self]
  -- the summands for each part, as functions of the state
  have hpart : ∀ (r : ℕ → Ω → ℝ), (∀ n ω, 0 ≤ r n ω) → (∀ n ω, r n ω ≤ |s n ω|) →
      (∀ ω', Summable fun j : ℕ => β ^ j * 𝔼.E (t + N) (r (t + N + j)) ω') ∧
      HasSum (fun j => β ^ j * 𝔼.E t (r (t + N + j)) ω)
        (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ j * 𝔼.E (t + N) (r (t + N + j)) ω') ω) := by
    intro r hr0 hrs
    set f : ℕ → Ω → ℝ := fun j ω' => β ^ j * 𝔼.E (t + N) (r (t + N + j)) ω' with hf
    have hf0 : ∀ k ω', 0 ≤ f k ω' := fun k ω' =>
      mul_nonneg (pow_nonneg hβ k) (E_nonneg 𝔼 (hr0 _) ω')
    have hfs : ∀ ω', Summable fun k => f k ω' := fun ω' => by
      refine Summable.of_nonneg_of_le (fun k => hf0 k ω') (fun k => ?_) (hs (t + N) ω')
      exact mul_le_mul_of_nonneg_left (𝔼.mono _ (fun ω'' => hrs _ ω'') ω') (pow_nonneg hβ k)
    refine ⟨hfs, ?_⟩
    have hmc := hMC t f hf0 hfs ω
    refine hmc.congr_fun fun j => ?_
    have hfj : f j = β ^ j • 𝔼.E (t + N) (r (t + N + j)) := rfl
    rw [hfj, map_smul, 𝔼.tower (Nat.le_add_right t N)]
    rfl
  have hp := hpart sp (fun n ω => le_max_right _ _)
    (fun n ω => max_le (le_abs_self _) (abs_nonneg _))
  have hn := hpart sn (fun n ω => le_max_right _ _)
    (fun n ω => max_le (neg_le_abs _) (abs_nonneg _))
  have hpv : pv 𝔼 β s (t + N) =
      (fun ω' => ∑' j : ℕ, β ^ j * 𝔼.E (t + N) (sp (t + N + j)) ω') -
        (fun ω' => ∑' j : ℕ, β ^ j * 𝔼.E (t + N) (sn (t + N + j)) ω') := by
    funext ω'
    simp only [pv_apply, Pi.sub_apply]
    rw [← (hp.1 ω').tsum_sub (hn.1 ω')]
    refine tsum_congr fun j => ?_
    rw [hsplit (t + N + j), map_sub, Pi.sub_apply]
    ring
  rw [hpv, map_sub, Pi.sub_apply]
  refine (hp.2.sub hn.2).congr_fun fun j => ?_
  rw [hsplit (t + N + j), map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (2.7), p. 22: the present value is known at the date it is computed. -/
theorem E_pv_self (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (t : ℕ) : 𝔼.E t (pv 𝔼 β s t) = pv 𝔼 β s t := by
  funext ω
  have h := hasSum_E_pv 𝔼 hMC hβ hs t 0 ω
  simp only [add_zero] at h
  exact h.tsum_eq.symm

/-- Cochrane (2023), eqs. (2.5) and (2.7), p. 22: the present value satisfies the flow
condition, `pv_t = s_t + β E_t pv_{t+1}`. -/
theorem pv_flow (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) : FlowX 𝔼 β (pv 𝔼 β s) s := by
  intro t
  funext ω
  have h1 := hasSum_E_pv 𝔼 hMC hβ hs t 1 ω
  have h0 := (summable_terms 𝔼 hβ hs t ω).tsum_eq_zero_add
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' j : ℕ, β ^ j * 𝔼.E t (s (t + j)) ω = _
  rw [h0, ← h1.tsum_eq, ← tsum_mul_left, pow_zero, one_mul, add_zero, hsad t]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t + (j + 1) = t + 1 + j by omega]
  ring

/-- Cochrane (2023), eqs. (2.6)–(2.7), p. 22: the present value satisfies the transversality
condition: `β^N E_t pv_{t+N}` is the tail `∑_{j ≥ N} β^j E_t s_{t+j}`, which tends to zero. -/
theorem pv_tvc (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (t : ℕ) : TVC 𝔼 β (pv 𝔼 β s) t := by
  intro ω
  set f : ℕ → ℝ := fun j => β ^ j * 𝔼.E t (s (t + j)) ω with hf
  have htail : (fun N : ℕ => β ^ N * 𝔼.E t (pv 𝔼 β s (t + N)) ω) =
      fun N => ∑' j, f (j + N) := by
    funext N
    rw [← (hasSum_E_pv 𝔼 hMC hβ hs t N ω).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hf]
    rw [pow_add, show t + N + j = t + (j + N) by omega]
    ring
  rw [htail]
  exact tendsto_sum_nat_add f

/-- Cochrane (2023), eqs. (2.5)–(2.7), p. 22, both directions, with signed surpluses: for
`β ≥ 0`, adapted, absolutely summable surpluses and conditional monotone convergence, real debt
satisfies the flow condition (2.5) and the transversality condition (2.6) at every date iff it
equals the present value of surpluses (2.7) at every date. -/
theorem valuation_iff (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β)
    {x s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) :
    (FlowX 𝔼 β x s ∧ ∀ t, TVC 𝔼 β x t) ↔ ∀ t, x t = pv 𝔼 β s t := by
  constructor
  · rintro ⟨h, htvc⟩ t
    funext ω
    exact (hasSum_of_flow_tvc 𝔼 hβ hs hsad h (htvc t) ω).tsum_eq.symm
  · intro h
    have hx : x = pv 𝔼 β s := funext h
    rw [hx]
    exact ⟨pv_flow 𝔼 hMC hβ hs hsad, pv_tvc 𝔼 hMC hβ hs⟩

/-! ### The equilibrium price level -/

/-- Cochrane (2023), §2.1, pp. 21–22: an equilibrium given nominal debt `{B_t}` (`Bm`) and real
surpluses `{s_t}`: a positive price level known at each date, the bond price (2.3)
`Q_t = β E_t(P_t/P_{t+1})`, the flow condition (2.4) `B_{t−1} = P_t s_t + Q_t B_t`, and the
transversality condition (2.6) on real debt `B_{t−1}/P_t`, at every date. -/
def IsEqm (β : ℝ) (Bm s P Q : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ 𝔼.Adapted P ∧
    (∀ t, Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) ∧
    (∀ t ω, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ∧
    ∀ t, TVC 𝔼 β (fun t ω => Bm t ω / P t ω) t

/-- Cochrane (2023), eq. (2.7), p. 22: in every equilibrium the real value of nominal debt equals
the present value of surpluses at every date (debt sold at `t` known at `t`). -/
theorem eqm_realDebt_eq_pv (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q) (t : ℕ) :
    (fun ω => Bm t ω / P t ω) = pv 𝔼 β s t := by
  obtain ⟨hPpos, hPad, h23, h24, htvc⟩ := h
  have hflow : FlowX 𝔼 β (fun t ω => Bm t ω / P t ω) s := fun t =>
    (flow_iff_real_x 𝔼 hPO (hPpos t) (hPad t) (hB1 t) (h23 t)).mp (h24 t)
  exact (valuation_iff 𝔼 hMC hβ hs hsad).mp ⟨hflow, htvc⟩ t

/-- Cochrane (2023), p. 22, "the price level must adjust so that (2.7) holds": in every
equilibrium `P_t = B_{t−1}/pv_t` wherever `B_{t−1} ≠ 0`. -/
theorem eqm_price_eq (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (h : IsEqm 𝔼 β Bm s P Q) {t : ℕ} {ω : Ω}
    (hB : Bm t ω ≠ 0) : P t ω = Bm t ω / pv 𝔼 β s t ω := by
  have hx := congrFun (eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h t) ω
  have hP := (h.1 t ω).ne'
  rw [← hx]
  field_simp

/-- Cochrane (2023), p. 22: with positive nominal debt, every equilibrium has a positive
present value of surpluses at every date and state. -/
theorem eqm_pv_pos (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s P Q : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω)
    (h : IsEqm 𝔼 β Bm s P Q) (t : ℕ) (ω : Ω) : 0 < pv 𝔼 β s t ω := by
  rw [← congrFun (eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h t) ω]
  exact div_pos (hBpos t ω) (h.1 t ω)

/-- Cochrane (2023), p. 22 (the implicit hypothesis that the present value is positive, survey
item E3 for the two-period analogue): with positive nominal debt, if the present value of
surpluses is nonpositive at some date and state, there is no equilibrium. -/
theorem no_eqm_of_pv_nonpos (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm s : ℕ → Ω → ℝ} (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω) {t : ℕ}
    {ω : Ω} (hpv : pv 𝔼 β s t ω ≤ 0) : ∀ P Q, ¬ IsEqm 𝔼 β Bm s P Q := fun _ _ h =>
  absurd (eqm_pv_pos 𝔼 hPO hMC hβ hs hsad hB1 hBpos h t ω) (not_lt.mpr hpv)

/-- Cochrane (2023), p. 22: the candidate equilibrium price level `P_t = B_{t−1}/pv_t`. -/
noncomputable def eqmPrice (β : ℝ) (Bm s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => Bm t ω / pv 𝔼 β s t ω

/-- Cochrane (2023), eq. (2.3), p. 22: the bond price at the candidate equilibrium price level,
`Q_t = β E_t(P_t/P_{t+1})`. -/
noncomputable def eqmBondPrice (β : ℝ) (Bm s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => β • 𝔼.E t (fun ω => eqmPrice 𝔼 β Bm s t ω / eqmPrice 𝔼 β Bm s (t + 1) ω)

/-- Cochrane (2023), p. 22, existence: with positive nominal debt known when issued, adapted
absolutely summable surpluses with positive present value at every date and state, the price
level `P_t = B_{t−1}/pv_t` with bond price `Q_t = β E_t(P_t/P_{t+1})` is an equilibrium. -/
theorem eqm_of_pv_pos (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {Bm s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) (hB0 : ∀ t, 𝔼.E t (Bm t) = Bm t)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω)
    (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω) :
    IsEqm 𝔼 β Bm s (eqmPrice 𝔼 β Bm s) (eqmBondPrice 𝔼 β Bm s) := by
  set P : ℕ → Ω → ℝ := eqmPrice 𝔼 β Bm s with hPdef
  have hPpos : ∀ t ω, 0 < P t ω := fun t ω => div_pos (hBpos t ω) (hpv t ω)
  have hPad : 𝔼.Adapted P := fun t =>
    known_div 𝔼 hPO hFK (hB0 t) (E_pv_self 𝔼 hMC hβ hs t)
  have hx : (fun t ω => Bm t ω / P t ω) = pv 𝔼 β s := by
    funext t ω
    have := (hBpos t ω).ne'
    have := (hpv t ω).ne'
    simp only [hPdef, eqmPrice]
    field_simp
  refine ⟨hPpos, hPad, fun t => rfl, fun t => ?_, fun t => ?_⟩
  · refine (flow_iff_real_x 𝔼 hPO (Q := eqmBondPrice 𝔼 β Bm s) (hPpos t) (hPad t) (hB1 t)
      rfl).mpr ?_
    have hfl := pv_flow 𝔼 hMC hβ hs hsad t
    have h1 := congrFun hx t
    have h2 := congrFun hx (t + 1)
    rw [h1, h2]
    exact hfl
  · rw [hx]
    exact pv_tvc 𝔼 hMC hβ hs t

/-- Cochrane (2023), p. 22, "the price level must adjust so that (2.7) holds", as the
fiscal-theory determination of the price level: given positive nominal debt (known when issued)
and adapted, absolutely summable surpluses with positive present value, there is exactly one
equilibrium price level and bond-price process. This is uniqueness of the price level given
surpluses, not uniqueness among bounded solutions of a difference equation. -/
theorem existsUnique_eqm (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {Bm s : ℕ → Ω → ℝ}
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s) (hB0 : ∀ t, 𝔼.E t (Bm t) = Bm t)
    (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hBpos : ∀ t ω, 0 < Bm t ω)
    (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω) :
    ∃! PQ : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), IsEqm 𝔼 β Bm s PQ.1 PQ.2 := by
  refine ⟨(eqmPrice 𝔼 β Bm s, eqmBondPrice 𝔼 β Bm s),
    eqm_of_pv_pos 𝔼 hPO hFK hMC hβ hs hsad hB0 hB1 hBpos hpv, ?_⟩
  rintro ⟨P, Q⟩ h
  have hP : P = eqmPrice 𝔼 β Bm s := by
    funext t ω
    exact eqm_price_eq 𝔼 hPO hMC hβ hs hsad hB1 h (hBpos t ω).ne'
  have hQ : Q = fun t => β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω) := funext h.2.2.1
  rw [hQ, hP]
  rfl

/-! ### The household present-value budget constraint (2.8) -/

/-- Cochrane (2023), eqs. (2.2) and (2.8), pp. 21–23: with no money held overnight, the bond
price (2.3), a positive price level known at `t` and `B_t` known at `t`, the household flow
constraint (2.2) at `t` is the real flow `x_t = (c_t − y + s_t) + β E_t x_{t+1}`. -/
theorem hh_flow_iff_real (hPO : 𝔼.PullOut) {β y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ}
    (hM : ∀ t ω, Mm t ω = 0) (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) :
    (∀ ω, Mm t ω + Bm t ω + P t ω * y =
        P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω) ↔
      (fun ω => Bm t ω / P t ω) =
        (fun ω => c t ω - y + s t ω) + β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  rw [← flow_iff_real_x 𝔼 hPO (s := fun t ω => c t ω - y + s t ω) hPpos hPad hB h23]
  refine forall_congr' fun ω => ?_
  rw [hM t ω, hM (t + 1) ω]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (2.8), p. 23 ("add the transversality condition to the household flow
budget constraint (2.2), iterate forward"): with no money held, (2.3), positive adapted prices,
debt known when sold, and adapted absolutely summable net demands `d_t = c_t − y + s_t`, the
household flow constraints plus the TVC at every date hold iff
`B_{t−1}/P_t = ∑_j β^j E_t(c_{t+j} − y + s_{t+j})` at every date. -/
theorem hh_pv_iff (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β y : ℝ} (hβ : 0 ≤ β)
    {Mm Bm P c s Q : ℕ → Ω → ℝ} (hM : ∀ t ω, Mm t ω = 0) (hPpos : ∀ t ω, 0 < P t ω)
    (hPad : 𝔼.Adapted P) (hB1 : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : ∀ t, Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (hd : AbsSummable 𝔼 β fun t ω => c t ω - y + s t ω)
    (hdad : 𝔼.Adapted fun t ω => c t ω - y + s t ω) :
    (HhFlow y Mm Bm P c s Q ∧ ∀ t, TVC 𝔼 β (fun t ω => Bm t ω / P t ω) t) ↔
      ∀ t, (fun ω => Bm t ω / P t ω) = pv 𝔼 β (fun t ω => c t ω - y + s t ω) t := by
  rw [← valuation_iff 𝔼 hMC hβ hd hdad]
  have hfl : HhFlow y Mm Bm P c s Q ↔ FlowX 𝔼 β (fun t ω => Bm t ω / P t ω)
      (fun t ω => c t ω - y + s t ω) := by
    constructor
    · intro h t
      exact (hh_flow_iff_real 𝔼 hPO hM (hPpos t) (hPad t) (hB1 t) (h23 t)).mp (h t)
    · intro h t
      exact (hh_flow_iff_real 𝔼 hPO hM (hPpos t) (hPad t) (hB1 t) (h23 t)).mpr (h t)
  rw [hfl]

/-- Cochrane (2023), p. 23, "If the value of debt is greater than present value of surpluses,
then the household has extra wealth, which they try to spend on consumption greater than
endowment": if (2.8) holds and `B_{t−1}/P_t > ∑_j β^j E_t s_{t+j}`, then the present value of
planned excess consumption `∑_j β^j (E_t c_{t+j} − y)` is positive, so `E_t c_{t+j} > y` at some
date `t + j`. -/
theorem excess_demand_of_gap {β y : ℝ} (hβ : 0 ≤ β) {c s : ℕ → Ω → ℝ} {x : ℝ} {t : ℕ}
    {ω : Ω} (hs : AbsSummable 𝔼 β s)
    (hcs : Summable fun j : ℕ => β ^ j * (𝔼.E t (c (t + j)) ω - y))
    (h28 : x = pv 𝔼 β (fun t ω => c t ω - y + s t ω) t ω) (hgap : pv 𝔼 β s t ω < x) :
    0 < ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) ∧ ∃ j, y < 𝔼.E t (c (t + j)) ω := by
  have hterm : ∀ j, β ^ j * 𝔼.E t (fun ω => c (t + j) ω - y + s (t + j) ω) ω =
      β ^ j * (𝔼.E t (c (t + j)) ω - y) + β ^ j * 𝔼.E t (s (t + j)) ω := by
    intro j
    have : (fun ω => c (t + j) ω - y + s (t + j) ω) = c (t + j) - (fun _ => y) + s (t + j) :=
      rfl
    rw [this, map_add, map_sub, 𝔼.const]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hsum : pv 𝔼 β (fun t ω => c t ω - y + s t ω) t ω =
      ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) + pv 𝔼 β s t ω := by
    simp only [pv_apply]
    rw [← hcs.tsum_add (summable_terms 𝔼 hβ hs t ω)]
    exact tsum_congr hterm
  have hpos : 0 < ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) := by linarith
  refine ⟨hpos, ?_⟩
  by_contra hne
  push Not at hne
  have : ∑' j : ℕ, β ^ j * (𝔼.E t (c (t + j)) ω - y) ≤ 0 :=
    tsum_nonpos fun j => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ j)
      (by linarith [hne j])
  linarith

/-! ### Online Appendix A1.1: the transversality condition -/

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the "no-Ponzi" condition
`lim_T E_t β^T B_{T−1}/P_T ≥ 0`, stated without presupposing that the limit exists (as
`liminf ≥ 0`: eventually above `−ε` for every `ε > 0`). -/
def NoPonzi (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ N in atTop, -ε ≤ a N

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the optimality condition
`lim_T E_t β^T B_{T−1}/P_T ≤ 0` (as `limsup ≤ 0`). -/
def NoOverAccumulation (a : ℕ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ N in atTop, a N ≤ ε

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the transversality condition (limit zero)
holds iff both the no-Ponzi condition (`≥ 0`) and the optimality condition (`≤ 0`) hold. -/
theorem tendsto_zero_iff_noPonzi_and_optimal (a : ℕ → ℝ) :
    Tendsto a atTop (𝓝 0) ↔ NoPonzi a ∧ NoOverAccumulation a := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨N, hN⟩ := h ε hε
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have := hN n hn
      rw [Real.dist_eq, sub_zero, abs_lt] at this
      linarith
    · obtain ⟨N, hN⟩ := h ε hε
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have := hN n hn
      rw [Real.dist_eq, sub_zero, abs_lt] at this
      linarith
  · rintro ⟨h1, h2⟩ ε hε
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (h1 (ε / 2) (by linarith))
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (h2 (ε / 2) (by linarith))
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have a1 := hN1 n (le_of_max_le_left hn)
    have a2 := hN2 n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith

/-- Cochrane (2023), Online Appendix A1.1, box p. 554: the TVC (2.6) at `t` holds iff in every
state both the no-Ponzi and the optimality halves hold. -/
theorem tvc_iff_noPonzi_and_optimal (β : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) :
    TVC 𝔼 β x t ↔ ∀ ω, NoPonzi (fun N => β ^ N * 𝔼.E t (x (t + N)) ω) ∧
      NoOverAccumulation (fun N => β ^ N * 𝔼.E t (x (t + N)) ω) :=
  forall_congr' fun _ => tendsto_zero_iff_noPonzi_and_optimal _

/-- Cochrane (2023), p. 22, "Non-negative debt `B_t ≥ 0` rules out a negative value", and Online
Appendix A1.1, p. 555 (the no-Ponzi half is a genuine budget constraint): with `B ≥ 0`,
`P > 0` and `β ≥ 0` every term `β^N E_t B_{t+N−1}/P_{t+N}` is nonnegative, so the no-Ponzi
condition holds automatically. -/
theorem noPonzi_of_nonneg_debt {β : ℝ} (hβ : 0 ≤ β) {Bm P : ℕ → Ω → ℝ}
    (hB : ∀ t ω, 0 ≤ Bm t ω) (hP : ∀ t ω, 0 < P t ω) (t : ℕ) (ω : Ω) :
    NoPonzi (fun N => β ^ N * 𝔼.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω) := by
  intro ε hε
  refine Filter.Eventually.of_forall fun N => ?_
  have : 0 ≤ β ^ N * 𝔼.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω :=
    mul_nonneg (pow_nonneg hβ N)
      (E_nonneg 𝔼 (fun ω => div_nonneg (hB _ ω) (hP _ ω).le) ω)
  linarith

/-- Cochrane (2023), Online Appendix A1.1, eqs. (1.1)–(1.2), p. 554, the finite-horizon identity
(iterating the household flow (1.1)): with `d_t = c_t + s_t − y`,
`B_{t−1}/P_t = ∑_{j=0}^{T} β^j E_t d_{t+j} + β^{T+1} E_t B_{t+T}/P_{t+T+1}`. The printed (1.2)
has `R^{−T}` on the terminal term; the exponent is `T + 1` (survey E4, see
`printed_A1_2_false`). -/
theorem hh_iterate {β : ℝ} {x d : ℕ → Ω → ℝ} (hd : 𝔼.Adapted d) (h : FlowX 𝔼 β x d)
    (t T : ℕ) :
    x t = (∑ j ∈ Finset.range (T + 1), β ^ j • 𝔼.E t (d (t + j))) +
      β ^ (T + 1) • 𝔼.E t (x (t + T + 1)) :=
  telescope 𝔼 h (adapted_of_flow 𝔼 hd h t) (T + 1)

/-- Cochrane (2023), Online Appendix A1.1, eq. (1.2), p. 554, and p. 28 (survey E4): the printed
terminal weight `β^T` (`R^{−T}`) is wrong. Under perfect foresight with `β = 1/2`, `d ≡ 0` and
`x_t = 2^t` the flow condition holds, but `x_0 ≠ ∑_{j ≤ 0} β^j d_j + β^0 x_1`. -/
theorem printed_A1_2_false :
    FlowX perfectForesight (1 / 2 : ℝ) (fun t _ => (2 : ℝ) ^ t) (fun _ _ => 0) ∧
      (fun _ => (2 : ℝ) ^ 0) ≠
        (∑ j ∈ Finset.range (0 + 1), (1 / 2 : ℝ) ^ j •
          perfectForesight.E 0 ((fun _ _ => (0 : ℝ)) (0 + j))) +
        (1 / 2 : ℝ) ^ 0 • perfectForesight.E 0 ((fun t (_ : Unit) => (2 : ℝ) ^ t) (0 + 0 + 1)) := by
  refine ⟨fun t => ?_, fun h => ?_⟩
  · funext ω
    change (2 : ℝ) ^ t = 0 + 1 / 2 * 2 ^ (t + 1)
    rw [pow_succ]
    ring
  · have := congrFun h ()
    change (2 : ℝ) ^ 0 = (∑ j ∈ Finset.range (0 + 1), (1 / 2 : ℝ) ^ j * 0) +
      (1 / 2) ^ 0 * 2 ^ (0 + 0 + 1) at this
    norm_num at this

/-- Cochrane (2023), Online Appendix A1.1, p. 555, the explosion with constant surpluses
(also under uncertainty): if `x_t = s + β E_t x_{t+1}` at every date with constant `s` and
`0 < β < 1`, then `E_t x_{t+n} − s/(1−β) = β^{−n} (x_t − s/(1−β))`. -/
theorem const_explodes {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) (t n : ℕ) :
    𝔼.E t (x (t + n)) - (fun _ => s / (1 - β)) =
      (β ^ n)⁻¹ • (x t - fun _ => s / (1 - β)) := by
  have hxt := adapted_of_flow 𝔼 (fun t => 𝔼.const t s) h t
  have hb : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
  have hb1 : 1 - β ≠ 0 := by linarith
  have hb2 : β - 1 ≠ 0 := by linarith
  have htel := telescope 𝔼 h hxt n
  have hsum : (∑ j ∈ Finset.range n, β ^ j • 𝔼.E t ((fun _ _ => s : ℕ → Ω → ℝ) (t + j))) =
      fun _ => s * (1 - β ^ n) / (1 - β) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, 𝔼.const, smul_eq_mul]
    rw [← Finset.sum_mul, geom_sum_eq hβ1.ne]
    field_simp
    ring
  rw [hsum] at htel
  funext ω
  have hω := congrFun htel ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hω]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix A1.1, p. 555, "The terminal or transversality term does not
go to zero": with constant surpluses, `β^n E_t x_{t+n} → x_t − s/(1−β)`. -/
theorem const_terminal_limit {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) (t : ℕ) (ω : Ω) :
    Tendsto (fun n : ℕ => β ^ n * 𝔼.E t (x (t + n)) ω) atTop (𝓝 (x t ω - s / (1 - β))) := by
  have hb : ∀ n, β ^ n * 𝔼.E t (x (t + n)) ω =
      β ^ n * (s / (1 - β)) + (x t ω - s / (1 - β)) := by
    intro n
    have := congrFun (const_explodes 𝔼 hβ0 hβ1 h t n) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
    have h2 : 𝔼.E t (x (t + n)) ω = s / (1 - β) + (β ^ n)⁻¹ * (x t ω - s / (1 - β)) := by
      linarith
    rw [h2]
    field_simp
  simp_rw [hb]
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (s / (1 - β))).add_const (x t ω - s / (1 - β))
  simpa using hlim

/-- Cochrane (2023), Online Appendix A1.1, p. 555: with constant surpluses the TVC holds at `t`
iff `x_t = s/(1−β)` in every state, i.e. iff the price level is the equilibrium one; at a too-low
price level (`x_t > s/(1−β)`) the valuation equation acquires the extra term
`x_t − s/(1−β)`. -/
theorem const_tvc_iff {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (h : FlowX 𝔼 β x fun _ _ => s) (t : ℕ) :
    TVC 𝔼 β x t ↔ ∀ ω, x t ω = s / (1 - β) := by
  constructor
  · intro htvc ω
    have := tendsto_nhds_unique (const_terminal_limit 𝔼 hβ0 hβ1 h t ω) (htvc ω)
    linarith
  · intro hx ω
    have := const_terminal_limit 𝔼 hβ0 hβ1 h t ω
    rwa [hx ω, sub_self] at this

/-- Cochrane (2023), Online Appendix A1.1, p. 555 (display after "taking the limit"): with
constant surpluses the finite-horizon valuation converges to
`x_t = ∑_j β^j s + (x_t − s/(1−β))`. -/
theorem const_valuation_limit {β s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HasSum (fun j : ℕ => β ^ j * s) (s / (1 - β)) := by
  have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right s
  simpa [div_eq_inv_mul] using this

/-! ### The deviation argument (A1.1, (1.3)), perfect foresight -/

/-- Cochrane (2023), Online Appendix A1.1, p. 556: under perfect foresight with constant
surplus `s` and consumption `y + Δc`, real debt evolves by `z_n = s + Δc + β z_{n+1}`; every such
path from `z_0 = x₀` is `z_n = K + β^{−n}(x₀ − K)` with `K = (s + Δc)/(1 − β)`. -/
theorem deviation_closed_form {β s Δc x₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {z : ℕ → ℝ}
    (hz0 : z 0 = x₀) (hz : ∀ n, z n = s + Δc + β * z (n + 1)) (n : ℕ) :
    z n = (s + Δc) / (1 - β) + (β ^ n)⁻¹ * (x₀ - (s + Δc) / (1 - β)) := by
  have hb1 : 1 - β ≠ 0 := by linarith
  induction n with
  | zero => simp [hz0]
  | succ n ih =>
    have h := hz n
    have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
    have hz1 : z (n + 1) = (z n - (s + Δc)) / β := by
      field_simp
      linarith
    rw [hz1, ih, pow_succ]
    field_simp
    ring

/-- Cochrane (2023), Online Appendix A1.1, eq. (1.3), p. 556: if the initial value of debt
satisfies (1.3) `x₀ ≥ (s + Δc)/(1 − β)` (and `x₀ ≥ 0`), the path
`z_n = K + β^{−n}(x₀ − K)` satisfies the flow constraint with consumption `y + Δc` and keeps debt
nonnegative, `z_n ≥ x₀ ≥ 0`: the deviation is feasible. -/
theorem deviation_feasible {β s Δc x₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 ≤ x₀)
    (h13 : (s + Δc) / (1 - β) ≤ x₀) :
    let z : ℕ → ℝ := fun n => (s + Δc) / (1 - β) + (β ^ n)⁻¹ * (x₀ - (s + Δc) / (1 - β))
    z 0 = x₀ ∧ (∀ n, z n = s + Δc + β * z (n + 1)) ∧ ∀ n, x₀ ≤ z n ∧ 0 ≤ z n := by
  intro z
  have hb1 : 1 - β ≠ 0 := by linarith
  refine ⟨by simp [z], fun n => ?_, fun n => ?_⟩
  · have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ0.ne'
    simp only [z, pow_succ]
    field_simp
    ring
  · have hge : 1 ≤ (β ^ n)⁻¹ := one_le_inv₀ (pow_pos hβ0 n) |>.mpr (pow_le_one₀ hβ0.le hβ1.le)
    have hk : 0 ≤ x₀ - (s + Δc) / (1 - β) := by linarith
    have : x₀ - (s + Δc) / (1 - β) ≤ (β ^ n)⁻¹ * (x₀ - (s + Δc) / (1 - β)) := by
      nlinarith
    constructor <;> simp only [z] <;> linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "improves utility": for strictly increasing
`u` and `Δc > 0`, consuming `y + Δc` forever gives strictly higher utility
`∑ β^n u(y + Δc) > ∑ β^n u(y)` (`0 ≤ β < 1`). -/
theorem deviation_improves {β y Δc : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hu : StrictMono u) (hΔ : 0 < Δc) :
    ∑' n : ℕ, β ^ n * u y < ∑' n : ℕ, β ^ n * u (y + Δc) := by
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
  have h1 : 0 < (1 - β)⁻¹ := inv_pos.mpr (by linarith)
  exact mul_lt_mul_of_pos_left (hu (by linarith)) h1

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "the increase `Δc` by which (1.3) holds with
equality is the optimal choice": let `Δc* = (1 − β)x₀ − s` and `c* = y + Δc*`. If `u` has a
supergradient `g ≥ 0` at `c*` (as for concave increasing `u`, with `g = u'(c*)`), then every
feasible plan (flow constraint `z_n = c_n − y + s + β z_{n+1}` from `z_0 = x₀` with `z ≥ 0`, and
summable discounted consumption and utility) gives no more utility than consuming `c*` forever. -/
theorem deviation_optimal {β y s x₀ g : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hg : 0 ≤ g) (hsup : ∀ c, u c ≤ u (y + ((1 - β) * x₀ - s)) +
      g * (c - (y + ((1 - β) * x₀ - s))))
    {c z : ℕ → ℝ} (hz0 : z 0 = x₀) (hz : ∀ n, z n = c n - y + s + β * z (n + 1))
    (hznn : ∀ n, 0 ≤ z n) (hcs : Summable fun n => β ^ n * c n)
    (hus : Summable fun n => β ^ n * u (c n)) :
    ∑' n : ℕ, β ^ n * u (c n) ≤ ∑' n : ℕ, β ^ n * u (y + ((1 - β) * x₀ - s)) := by
  set cs := y + ((1 - β) * x₀ - s) with hcs_def
  have hgeo : Summable fun n : ℕ => β ^ n := summable_geometric_of_lt_one hβ0 hβ1
  have hb1 : (1 - β) ≠ 0 := by linarith
  -- the budget: partial sums of discounted net demand are at most x₀
  have htel : ∀ N, x₀ = ∑ n ∈ Finset.range N, β ^ n * (c n - y + s) + β ^ N * z N := by
    intro N
    induction N with
    | zero => simp [hz0]
    | succ N ih =>
      rw [ih, Finset.sum_range_succ, hz N, pow_succ]
      ring
  have hds : Summable fun n => β ^ n * (c n - y + s) := by
    have := hcs.add (hgeo.mul_right (s - y))
    refine this.congr fun n => ?_
    ring
  have hbud : ∑' n, β ^ n * (c n - y + s) ≤ x₀ := by
    refine hds.tsum_le_of_sum_range_le fun N => ?_
    have := htel N
    have : 0 ≤ β ^ N * z N := mul_nonneg (pow_nonneg hβ0 N) (hznn N)
    linarith
  -- the same sum for the constant plan equals x₀
  have hstar : ∑' n : ℕ, β ^ n * (cs - y + s) = x₀ := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1, hcs_def]
    field_simp
    ring
  have hdiff : ∑' n : ℕ, β ^ n * (c n - cs) ≤ 0 := by
    have hcs' : Summable fun n : ℕ => β ^ n * (cs - y + s) := hgeo.mul_right _
    have : ∑' n : ℕ, β ^ n * (c n - cs) =
        ∑' n, β ^ n * (c n - y + s) - ∑' n : ℕ, β ^ n * (cs - y + s) := by
      rw [← hds.tsum_sub hcs']
      exact tsum_congr fun n => by ring
    linarith
  have hsum2 : Summable fun n : ℕ => β ^ n * (u cs + g * (c n - cs)) := by
    have := (hgeo.mul_right (u cs - g * cs)).add (hcs.mul_left g)
    refine this.congr fun n => ?_
    ring
  calc ∑' n : ℕ, β ^ n * u (c n) ≤ ∑' n : ℕ, β ^ n * (u cs + g * (c n - cs)) :=
        Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hsup (c n))
          (pow_nonneg hβ0 n)) hus hsum2
    _ = ∑' n : ℕ, β ^ n * u cs + g * ∑' n : ℕ, β ^ n * (c n - cs) := by
        have hd2 : Summable fun n : ℕ => β ^ n * (c n - cs) := by
          have := hcs.sub (hgeo.mul_right cs)
          refine this.congr fun n => ?_
          ring
        rw [← tsum_mul_left, ← (hgeo.mul_right (u cs)).tsum_add (hd2.mul_left g)]
        exact tsum_congr fun n => by ring
    _ ≤ ∑' n : ℕ, β ^ n * u cs := by
        have := mul_nonpos_of_nonneg_of_nonpos hg hdiff
        linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556 (concave utility): for `u` concave on `ℝ` with
derivative `g` at `x`, the tangent line lies above the graph, `u c ≤ u x + g (c − x)`. -/
theorem concave_le_tangent {u : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ u) {x g : ℝ}
    (hg : HasDerivAt u g x) (c : ℝ) : u c ≤ u x + g * (c - x) := by
  rcases lt_trichotomy c x with h | h | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ c) (Set.mem_univ x) h hg
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith
  · subst h
    simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ c) h hg
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556: a monotone function has a nonnegative
derivative wherever it is differentiable. -/
theorem deriv_nonneg_of_monotone {u : ℝ → ℝ} (hm : Monotone u) {x g : ℝ}
    (hg : HasDerivAt u g x) : 0 ≤ g := by
  have h := hg.tendsto_slope_zero_right
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  have : u x ≤ u (x + t) := hm (by linarith)
  have : 0 ≤ t⁻¹ * (u (x + t) - u x) :=
    mul_nonneg (inv_nonneg.mpr ht'.le) (by linarith)
  simpa [smul_eq_mul] using this

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "the increase `Δc` by which (1.3) holds with
equality is the optimal choice", under the book's assumptions on utility: `u` concave and
increasing, differentiable at `c* = y + ((1 − β)x₀ − s)`. Every feasible plan (flow constraint
from `z_0 = x₀`, nonnegative debt, summable discounted consumption and utility) gives no more
utility than consuming `c*` forever. -/
theorem deviation_optimal_concave {β y s x₀ g : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ}
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hg : HasDerivAt u g (y + ((1 - β) * x₀ - s)))
    {c z : ℕ → ℝ} (hz0 : z 0 = x₀) (hz : ∀ n, z n = c n - y + s + β * z (n + 1))
    (hznn : ∀ n, 0 ≤ z n) (hcs : Summable fun n => β ^ n * c n)
    (hus : Summable fun n => β ^ n * u (c n)) :
    ∑' n : ℕ, β ^ n * u (c n) ≤ ∑' n : ℕ, β ^ n * u (y + ((1 - β) * x₀ - s)) :=
  deviation_optimal hβ0 hβ1 (deriv_nonneg_of_monotone hmono hg) (concave_le_tangent hconc hg)
    hz0 hz hznn hcs hus

/-- Cochrane (2023), Online Appendix A1.1, p. 556, "with `Δc > 0`, i.e. `c > y`, this choice is
not an equilibrium, as the goods market does not clear": the optimal consumption
`y + ((1 − β)x₀ − s)` exceeds the endowment iff the price level is too low,
`x₀ > s/(1 − β)`; it equals `y` iff `x₀ = s/(1−β)`. -/
theorem tooLow_not_equilibrium {β y s x₀ : ℝ} (hβ1 : β < 1) :
    (y < y + ((1 - β) * x₀ - s) ↔ s / (1 - β) < x₀) ∧
      (y + ((1 - β) * x₀ - s) = y ↔ x₀ = s / (1 - β)) := by
  have hb : 0 < 1 - β := by linarith
  constructor
  · rw [div_lt_iff₀ hb]
    constructor <;> intro h <;> linarith
  · rw [eq_div_iff hb.ne']
    constructor <;> intro h <;> linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556: the optimal plan `Δc* = (1 − β)x₀ − s` keeps
real debt constant at `x₀`, so it satisfies the transversality condition. -/
theorem optimal_plan_tvc {β s x₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    let z : ℕ → ℝ := fun n => (s + ((1 - β) * x₀ - s)) / (1 - β) +
      (β ^ n)⁻¹ * (x₀ - (s + ((1 - β) * x₀ - s)) / (1 - β))
    (∀ n, z n = x₀) ∧ Tendsto (fun n => β ^ n * z n) atTop (𝓝 0) := by
  intro z
  have hb1 : 1 - β ≠ 0 := by linarith
  have hz : ∀ n, z n = x₀ := fun n => by
    simp only [z]
    field_simp
    ring
  refine ⟨hz, ?_⟩
  simp_rw [hz]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const x₀

/-! ### Optimisation implies the transversality condition (perfect foresight) -/

/-- Cochrane (2023), p. 22, "Household maximization, budget constraint, and equilibrium `c_t = y`
also imply the household transversality condition (2.6). If the term on the left is positive,
then the consumer can raise consumption at time `t`, lower this terminal value, and raise
utility", proved under perfect foresight: if `(c, b)` is an optimal household plan
(`Environment.HhOptimal`), `u` is strictly increasing, prices are positive, the bond price is
`Q_n = β P_n/P_{n+1}` (2.3), and discounted net demands `c_n − y + s_n` are summable, then
`lim_N β^N B_{N−1}/P_N = 0`. (If the limit were positive, consuming a little more at a late date
`T` and holding correspondingly less debt afterwards would be feasible and strictly better.) -/
theorem tvc_of_optimal {β y b₀ : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} (hu : StrictMono u)
    {P s Q c b : ℕ → ℝ} (hopt : HhOptimal β y u P s Q b₀ c b) (hP : ∀ n, 0 < P n)
    (hQ : ∀ n, Q n = β * (P n / P (n + 1)))
    (hd : Summable fun n => β ^ n * (c n - y + s n)) :
    Tendsto (fun N => β ^ N * (b N / P N)) atTop (𝓝 0) := by
  obtain ⟨⟨hb0, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  set x : ℕ → ℝ := fun n => b n / P n with hxdef
  set d : ℕ → ℝ := fun n => c n - y + s n with hddef
  have hx : ∀ n, x n = d n + β * x (n + 1) := by
    intro n
    have h1 := hflow n
    have hP0 := (hP n).ne'
    have hP1 := (hP (n + 1)).ne'
    have key : b n = P n * d n + β * P n * x (n + 1) := by
      rw [hQ n] at h1
      simp only [hddef, hxdef]
      field_simp at h1 ⊢
      linear_combination h1
    simp only [hxdef] at key ⊢
    rw [key]
    field_simp
  have htel : ∀ N, x 0 = ∑ n ∈ Finset.range N, β ^ n * d n + β ^ N * x N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [ih, Finset.sum_range_succ, hx N, pow_succ]
      ring
  set L := x 0 - ∑' n, β ^ n * d n with hL
  have hlim : Tendsto (fun N => β ^ N * x N) atTop (𝓝 L) := by
    have h := (tendsto_const_nhds (x := x 0)).sub hd.hasSum.tendsto_sum_nat
    refine h.congr fun N => ?_
    have := htel N
    simp only [hddef] at this ⊢
    linarith
  have hL0 : 0 ≤ L := ge_of_tendsto' hlim fun N =>
    mul_nonneg (pow_nonneg hβ.le N) (div_nonneg (hbnn N) (hP N).le)
  rcases hL0.lt_or_eq with hLpos | hLzero
  · exfalso
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
      (hlim.eventually (lt_mem_nhds (show L / 2 < L by linarith)))
    set δ : ℝ := L / 2 / β ^ T with hδ
    have hbT : 0 < β ^ T := pow_pos hβ T
    have hδpos : 0 < δ := div_pos (by linarith) hbT
    set c' : ℕ → ℝ := fun n => c n + if n = T then δ else 0 with hc'
    set b' : ℕ → ℝ := fun n => b n - if T < n then P n * δ * β ^ T / β ^ n else 0 with hb'
    have hfeas : HhFeasible y P s Q b₀ c' b' := by
      refine ⟨by simp [hb', hb0], fun n => ?_, fun n => ?_⟩
      · have h1 := hflow n
        have hP0 := (hP n).ne'
        have hP1 := (hP (n + 1)).ne'
        have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ.ne'
        rcases lt_trichotomy n T with hn | hn | hn
        · have e1 : ¬ T < n := by omega
          have e2 : ¬ T < n + 1 := by omega
          have e3 : n ≠ T := by omega
          simp only [hc', hb', e1, e2, e3, ↓reduceIte, add_zero, sub_zero]
          exact h1
        · subst hn
          have e2 : n < n + 1 := by omega
          simp only [hc', hb', lt_irrefl, e2, ↓reduceIte, sub_zero]
          rw [hQ n] at h1 ⊢
          rw [pow_succ]
          field_simp at h1 ⊢
          linear_combination h1
        · have e2 : T < n + 1 := by omega
          have e3 : n ≠ T := by omega
          simp only [hc', hb', hn, e2, e3, ↓reduceIte, add_zero]
          rw [hQ n] at h1 ⊢
          rw [pow_succ]
          field_simp at h1 ⊢
          linear_combination (β ^ n) * h1
      · simp only [hb']
        split_ifs with hn
        · have hgt := hT n hn.le
          simp only [hxdef] at hgt
          have hbn : 0 < β ^ n := pow_pos hβ n
          have hPn := hP n
          have : P n * δ * β ^ T / β ^ n ≤ b n := by
            rw [div_le_iff₀ hbn]
            have e : δ * β ^ T = L / 2 := by rw [hδ]; field_simp
            have h3 : L / 2 < β ^ n * b n / P n := by
              calc L / 2 < β ^ n * (b n / P n) := hgt
                _ = β ^ n * b n / P n := by ring
            rw [lt_div_iff₀ hPn] at h3
            nlinarith
          linarith
        · simpa using hbnn n
    have hgain : HasSum (fun n => β ^ n * u (c' n))
        (∑' n, β ^ n * u (c n) + β ^ T * (u (c T + δ) - u (c T))) := by
      have hg : HasSum (fun n => β ^ n * u (c' n) - β ^ n * u (c n))
          (β ^ T * (u (c T + δ) - u (c T))) := by
        have h := hasSum_single (f := fun n => β ^ n * u (c' n) - β ^ n * u (c n)) T
          (fun n hn => by simp [hc', hn])
        convert h using 1
        simp only [hc', ↓reduceIte]
        ring
      convert hsum.hasSum.add hg using 1
      funext n
      ring
    have h1 := hbest c' b' hfeas hgain.summable
    rw [hgain.tsum_eq] at h1
    have : 0 < β ^ T * (u (c T + δ) - u (c T)) :=
      mul_pos hbT (sub_pos.mpr (hu (by linarith)))
    linarith
  · rw [← hLzero] at hlim
    exact hlim

/-- Cochrane (2023), eq. (2.7), p. 22, "As a result, we can then iterate (2.5) to (2.7)", derived
from household optimisation under perfect foresight: in an optimal plan at the endowment
(`c = y`) with the bond price (2.3) and summable discounted surpluses,
`B_{−1}/P_0 = ∑_n β^n s_n`. -/
theorem valuation_of_optimal {β y b₀ : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} (hu : StrictMono u)
    {P s Q b : ℕ → ℝ} (hopt : HhOptimal β y u P s Q b₀ (fun _ => y) b) (hP : ∀ n, 0 < P n)
    (hQ : ∀ n, Q n = β * (P n / P (n + 1))) (hs : Summable fun n => β ^ n * s n) :
    HasSum (fun n => β ^ n * s n) (b₀ / P 0) := by
  have hd : Summable fun n => β ^ n * ((fun _ => y) n - y + s n) := by
    refine hs.congr fun n => ?_
    ring
  have htvc := tvc_of_optimal hβ hu hopt hP hQ hd
  obtain ⟨⟨hb0, hflow, -⟩, -, -⟩ := hopt
  have htel : ∀ N, b 0 / P 0 = ∑ n ∈ Finset.range N, β ^ n * s n + β ^ N * (b N / P N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [ih, Finset.sum_range_succ, pow_succ]
      have h1 := hflow N
      rw [hQ N] at h1
      have hP0 := (hP N).ne'
      have hP1 := (hP (N + 1)).ne'
      have hbN : β ^ N ≠ 0 := pow_ne_zero N hβ.ne'
      have key : b N / P N = s N + β * (b (N + 1) / P (N + 1)) := by
        field_simp at h1 ⊢
        linear_combination h1
      rw [key]
      ring
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, β ^ n * s n) atTop (𝓝 (b₀ / P 0)) := by
    have h := (tendsto_const_nhds (x := b 0 / P 0)).sub htvc
    rw [sub_zero, hb0] at h
    refine h.congr fun N => ?_
    have := htel N
    rw [hb0] at this
    linarith
  rw [tendsto_nhds_unique hlim hs.hasSum.tendsto_sum_nat]
  exact hs.hasSum

/-- Cochrane (2023), p. 22 ("If the term on the left is positive, then the consumer can raise
consumption at time `t`, lower this terminal value, and raise utility") and Online Appendix A1.1,
p. 555, for any `ExpectationSystem`: from a plan satisfying the real household flow
`x_r = d_r + β E_r x_{r+1}` at every date, consume `δ` more at date `t` and hold
`x'_{t+n} = x_{t+n} − δβ^{−n}` (`n ≥ 1`) less debt. The new plan satisfies every flow constraint
from `t` on, lowers the terminal term by exactly `δ`, and is feasible (nonnegative debt) whenever
the old plan carries a pathwise bubble `x_{t+n} ≥ δβ^{−n}`. -/
theorem bubble_deviation {β δ : ℝ} (hβ0 : 0 < β) {x d : ℕ → Ω → ℝ} (h : FlowX 𝔼 β x d)
    (t : ℕ) :
    let x' : ℕ → Ω → ℝ := fun n => x (t + n) - fun _ => δ * (β ^ n)⁻¹
    (x t = d t + (fun _ => δ) + β • 𝔼.E t (x' 1)) ∧
      (∀ n, 1 ≤ n → x' n = d (t + n) + β • 𝔼.E (t + n) (x' (n + 1))) ∧
      (∀ N ω, 1 ≤ N → β ^ N * 𝔼.E t (x' N) ω = β ^ N * 𝔼.E t (x (t + N)) ω - δ) ∧
      ((∀ n ω, 1 ≤ n → δ * (β ^ n)⁻¹ ≤ x (t + n) ω) → ∀ n ω, 1 ≤ n → 0 ≤ x' n ω) := by
  intro x'
  have hb : β ≠ 0 := hβ0.ne'
  refine ⟨?_, fun n _ => ?_, fun N ω hN => ?_, fun hbub n ω hn => ?_⟩
  · funext ω
    have := congrFun (h t) ω
    simp only [x', map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      pow_one] at this ⊢
    rw [this]
    field_simp
    ring
  · funext ω
    have := congrFun (h (t + n)) ω
    simp only [x', map_sub, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at this ⊢
    rw [show t + (n + 1) = t + n + 1 by omega, this, pow_succ]
    have hbn : β ^ n ≠ 0 := pow_ne_zero n hb
    field_simp
    ring
  · simp only [x', map_sub, 𝔼.const, Pi.sub_apply]
    have hbn : β ^ N ≠ 0 := pow_ne_zero N hb
    field_simp
  · simp only [x', Pi.sub_apply]
    linarith [hbub n ω hn]

/-! ### Household optimisation under uncertainty (finite state space) -/

/-- Cochrane (2023), p. 21 (expected utility over a finite set of states): on a finite state
space every `E_t` is a finite weighted sum of the values of its argument. -/
theorem E_eq_sum [Fintype Ω] [DecidableEq Ω] (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    𝔼.E t x ω = ∑ ω', x ω' * 𝔼.E t (Pi.single ω' 1) ω := by
  have hx : x = ∑ ω', x ω' • (Pi.single ω' (1 : ℝ) : Ω → ℝ) := by
    funext ω
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [map_smul]
  rfl

/-- Cochrane (2023), p. 22 (limits inside `E_t`, finite state space): if `f_N → g` in every
state, then `E_t f_N → E_t g`. -/
theorem E_tendsto [Finite Ω] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : ∀ ω', Tendsto (fun N => f N ω') atTop (𝓝 (g ω'))) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => 𝔼.E t (f N) ω) atTop (𝓝 (𝔼.E t g ω)) := by
  classical
  have := Fintype.ofFinite Ω
  have e : (fun N => 𝔼.E t (f N) ω) =
      fun N => ∑ ω', f N ω' * 𝔼.E t (Pi.single ω' 1) ω := funext fun N => E_eq_sum 𝔼 t (f N) ω
  rw [e, E_eq_sum 𝔼 t g ω]
  exact tendsto_finsetSum _ fun ω' _ => (h ω').mul_const _

/-- Cochrane (2023), p. 21 (differentiating expected utility, finite state space): if
`ε ↦ f ε ω'` has derivative `f' ω'` at `a` in every state, then `ε ↦ E_t (f ε)` has derivative
`E_t f'` at `a`. -/
theorem hasDerivAt_E [Finite Ω] {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {a : ℝ}
    (h : ∀ ω', HasDerivAt (fun ε => f ε ω') (f' ω') a) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (f ε) ω) (𝔼.E t f' ω) a := by
  classical
  have := Fintype.ofFinite Ω
  have e : (fun ε => 𝔼.E t (f ε) ω) =
      fun ε => ∑ ω', f ε ω' * 𝔼.E t (Pi.single ω' 1) ω := funext fun ε => E_eq_sum 𝔼 t (f ε) ω
  rw [e, E_eq_sum 𝔼 t f' ω]
  exact HasDerivAt.fun_sum fun ω' _ => (h ω').mul_const _

/-- Cochrane (2023), p. 22 (modifying a plan at finitely many dates): if `f'` agrees with the
summable `f` off a finite set `S`, then `∑ f' = ∑ f + ∑_{n ∈ S} (f' n − f n)`. -/
theorem hasSum_of_eq_off_finset {f f' : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (h : ∀ n ∉ S, f' n = f n) : HasSum f' (∑' n, f n + ∑ n ∈ S, (f' n - f n)) := by
  have h2 : HasSum (fun n => f' n - f n) (∑ n ∈ S, (f' n - f n)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [h n hn, sub_self]
  convert hf.hasSum.add h2 using 1
  funext n
  ring

/-- Cochrane (2023), p. 21 (every state has positive probability): the date-0 expectation sees
every state, i.e. a nonnegative variable with zero date-0 expectation in every state is zero.
True for perfect foresight and every finite event tree (`finiteTree_faithful`). -/
def Faithful : Prop :=
  ∀ x : Ω → ℝ, (∀ ω, 0 ≤ x ω) → (∀ ω, 𝔼.E 0 x ω = 0) → ∀ ω, x ω = 0

/-- Cochrane (2023), p. 21: perfect foresight is faithful. -/
theorem perfectForesight_faithful : Faithful perfectForesight :=
  fun _ _ h ω => h ω

/-- Cochrane (2023), p. 21: every finite event tree is faithful (strictly positive
probabilities). -/
theorem finiteTree_faithful {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    Faithful T.toExpectationSystem := by
  classical
  intro x hx h0 ω
  have h := h0 ω
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at h
  simp only [ExpectationsFiniteTree.FiniteTree.condE, div_eq_zero_iff] at h
  rcases h with h | h
  · unfold ExpectationsFiniteTree.FiniteTree.num at h
    have hnn : ∀ ω' ∈ Finset.univ,
        0 ≤ (if T.info 0 ω' ω then T.prob ω' * x ω' else 0) := fun ω' _ => by
      split_ifs
      · exact mul_nonneg (T.prob_pos ω').le (hx ω')
      · exact le_rfl
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h ω (Finset.mem_univ ω)
    simp only [(T.info 0).refl ω, ↓reduceIte] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (T.prob_pos ω).ne'
    · exact h1
  · exact absurd h (T.mass_pos 0 ω).ne'

/-- Cochrane (2023), p. 21 (a finite economy): information stops growing after date `K`,
`E_t = E_K` for all `t ≥ K`. True for every finite event tree (`finiteTree_infoStable`). -/
def InfoStable (K : ℕ) : Prop := ∀ t, K ≤ t → ∀ x, 𝔼.E t x = 𝔼.E K x

/-- Cochrane (2023), p. 21: perfect foresight is information-stable from date 0. -/
theorem perfectForesight_infoStable : InfoStable perfectForesight 0 :=
  fun _ _ _ => rfl

/-- Cochrane (2023), p. 21: on a finite event tree the refining partitions of a finite set
stabilise, so information stops growing after some date `K`. -/
theorem finiteTree_infoStable {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : ∃ K, InfoStable T.toExpectationSystem K := by
  classical
  let S : ℕ → Finset (Ω' × Ω') := fun t => Finset.univ.filter fun p => T.info t p.1 p.2
  have hsub : ∀ s t, s ≤ t → S t ⊆ S s := fun s t hst p hp => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact T.refines hst _ _ hp
  obtain ⟨K, hK⟩ : ∃ K, ∀ t, (S K).card ≤ (S t).card := by
    have hne : (Set.range fun t => (S t).card).Nonempty := ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨K, hK⟩ := Nat.sInf_mem hne
    have hK' : (S K).card = sInf (Set.range fun t => (S t).card) := hK
    exact ⟨K, fun t => by rw [hK']; exact Nat.sInf_le ⟨t, rfl⟩⟩
  refine ⟨K, fun t ht x => ?_⟩
  have heq : S t = S K := Finset.eq_of_subset_of_card_le (hsub K t ht) (hK t)
  have hinfo : T.info t = T.info K := by
    refine Setoid.ext fun a b => ?_
    have := congrArg (fun F => (a, b) ∈ F) heq
    simpa [S] using this
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  funext ω
  simp only [ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num,
    ExpectationsFiniteTree.FiniteTree.mass]
  rw [hinfo]

/-- Cochrane (2023), eq. (2.2), p. 21, under uncertainty: a state-contingent household plan
`(c, b)` (`b n = B_{n−1}`, no money held) is feasible from initial debt `b₀` if consumption is
known at each date, bonds bought at `n` are known at `n`, the flow constraint holds at every
date and state, and `B ≥ 0`. -/
def SFeasible (y : ℝ) (P s Q : ℕ → Ω → ℝ) (b₀ : Ω → ℝ) (c b : ℕ → Ω → ℝ) : Prop :=
  b 0 = b₀ ∧ 𝔼.Adapted c ∧ (∀ n, 𝔼.E n (b (n + 1)) = b (n + 1)) ∧
    (∀ n ω, b n ω + P n ω * y = P n ω * c n ω + P n ω * s n ω + Q n ω * b (n + 1) ω) ∧
    ∀ n ω, 0 ≤ b n ω

/-- Cochrane (2023), p. 21: expected utility `E_0 ∑_t β^t u(c_t)`, written as the infinite sum
over dates `∑_t β^t E_0 u(c_t)` (as a date-0 random variable). -/
noncomputable def expUtil (β : ℝ) (u : ℝ → ℝ) (c : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑' n, β ^ n * 𝔼.E 0 (fun ω' => u (c n ω')) ω

/-- Cochrane (2023), p. 21, "A representative household maximizes `E ∑ β^t u(c_t)`": a feasible
state-contingent plan with summable expected utility that no other such plan beats in any
date-0 state. -/
def SOptimal (β y : ℝ) (u : ℝ → ℝ) (P s Q : ℕ → Ω → ℝ) (b₀ : Ω → ℝ) (c b : ℕ → Ω → ℝ) :
    Prop :=
  SFeasible 𝔼 y P s Q b₀ c b ∧
    (∀ ω, Summable fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c n ω')) ω) ∧
    ∀ c' b', SFeasible 𝔼 y P s Q b₀ c' b' →
      (∀ ω, Summable fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c' n ω')) ω) →
      ∀ ω, expUtil 𝔼 β u c' ω ≤ expUtil 𝔼 β u c ω

/-- Cochrane (2023), p. 21, "The consumer's first-order conditions", under uncertainty (finite
state space, pull-out, functions of known variables known, faithful `E_0`): if `(c, b)` is
optimal, `u` is differentiable with derivative `u'`, prices and the bond price are positive and
known when set, and the household holds bonds `B_t > 0` in every state, then the nominal Euler
equation holds: `Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]`. Proof: for every
date-`t` variable `z`, shifting `εz` dollars between consumption at `t` and bonds maturing at
`t + 1` is feasible for small `|ε|` and cannot raise expected utility, so the derivative in
`ε` vanishes; taking `z` equal to the Euler residual and using faithfulness gives the
conditional equation. -/
theorem euler_of_optimal_stoch [Finite Ω] [Nonempty Ω] (hPO : 𝔼.PullOut)
    (hFK : FunctionsKnown 𝔼) (hF : Faithful 𝔼) {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ c, HasDerivAt u (u' c) c) {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : SOptimal 𝔼 β y u P s Q b₀ c b) (hPpos : ∀ n ω, 0 < P n ω) (hPad : 𝔼.Adapted P)
    {t : ℕ} (hQpos : ∀ ω, 0 < Q t ω) (hQad : 𝔼.E t (Q t) = Q t)
    (hb : ∀ ω, 0 < b (t + 1) ω) :
    Q t * (fun ω => u' (c t ω) / P t ω) =
      β • 𝔼.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) := by
  obtain ⟨⟨hb0, hcad, hbad, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  -- Step A: the first-order condition along every date-`t` deviation `z`
  have stepA : ∀ z : Ω → ℝ, 𝔼.E t z = z → ∀ ω₀,
      β ^ t * 𝔼.E 0 (fun ω => u' (c t ω) * (z ω / P t ω)) ω₀ -
        β ^ (t + 1) * 𝔼.E 0 (fun ω => u' (c (t + 1) ω) * (z ω / (Q t ω * P (t + 1) ω))) ω₀
        = 0 := by
    intro z hz ω₀
    set a₀ : Ω → ℝ := fun ω => z ω / P t ω with ha₀
    set a₁ : Ω → ℝ := fun ω => z ω / (Q t ω * P (t + 1) ω) with ha₁
    set a₂ : Ω → ℝ := fun ω => z ω / Q t ω with ha₂
    have ha₀k : 𝔼.E t a₀ = a₀ := known_div 𝔼 hPO hFK hz (hPad t)
    have hQ1 : 𝔼.E (t + 1) (Q t * P (t + 1)) = Q t * P (t + 1) := by
      rw [hPO (t + 1) _ _ (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hQad), hPad (t + 1)]
    have ha₁k : 𝔼.E (t + 1) a₁ = a₁ :=
      known_div 𝔼 hPO hFK (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hz) hQ1
    have ha₂k : 𝔼.E t a₂ = a₂ := known_div 𝔼 hPO hFK hz hQad
    obtain ⟨ωm, hωm⟩ := Finite.exists_min (fun ω => Q t ω * b (t + 1) ω / (|z ω| + 1))
    set r := Q t ωm * b (t + 1) ωm / (|z ωm| + 1) with hr
    have hrpos : 0 < r := div_pos (mul_pos (hQpos ωm) (hb ωm)) (by positivity)
    let cε : ℝ → ℕ → Ω → ℝ := fun ε n ω =>
      c n ω + (if n = t then ε * a₀ ω else if n = t + 1 then -(ε * a₁ ω) else 0)
    let bε : ℝ → ℕ → Ω → ℝ := fun ε n ω => b n ω - (if n = t + 1 then ε * a₂ ω else 0)
    have hct : ∀ ε ω, cε ε t ω = c t ω + ε * a₀ ω := fun ε ω => by simp [cε]
    have hct1 : ∀ ε ω, cε ε (t + 1) ω = c (t + 1) ω - ε * a₁ ω := fun ε ω => by
      simp [cε, sub_eq_add_neg]
    have hcn : ∀ ε n, n ≠ t → n ≠ t + 1 → cε ε n = c n := fun ε n h1 h2 => by
      funext ω
      simp [cε, h1, h2]
    have hbt1 : ∀ ε ω, bε ε (t + 1) ω = b (t + 1) ω - ε * a₂ ω := fun ε ω => by simp [bε]
    have hbn : ∀ ε n, n ≠ t + 1 → bε ε n = b n := fun ε n h => by
      funext ω
      simp [bε, h]
    have hfeas : ∀ ε, |ε| < r → SFeasible 𝔼 y P s Q b₀ (cε ε) (bε ε) := by
      intro ε hε
      refine ⟨by rw [hbn ε 0 (by omega), hb0], fun n => ?_, fun n => ?_, fun n ω => ?_,
        fun n ω => ?_⟩
      · by_cases h1 : n = t
        · subst h1
          have e : cε ε n = c n + ε • a₀ := by
            funext ω
            rw [hct]
            rfl
          rw [e, map_add, map_smul, hcad n, ha₀k]
        · by_cases h2 : n = t + 1
          · subst h2
            have e : cε ε (t + 1) = c (t + 1) - ε • a₁ := by
              funext ω
              rw [hct1]
              rfl
            rw [e, map_sub, map_smul, hcad (t + 1), ha₁k]
          · rw [hcn ε n h1 h2, hcad n]
      · by_cases h1 : n = t
        · subst h1
          have e : bε ε (n + 1) = b (n + 1) - ε • a₂ := by
            funext ω
            rw [hbt1]
            rfl
          rw [e, map_sub, map_smul, hbad n, ha₂k]
        · rw [hbn ε (n + 1) (by omega), hbad n]
      · have h0 := hflow n ω
        by_cases h1 : n = t
        · subst h1
          rw [hct, hbn ε n (by omega), hbt1]
          have e1 : P n ω * (ε * a₀ ω) = ε * z ω := by
            simp only [ha₀]
            have := (hPpos n ω).ne'
            field_simp
          have e2 : Q n ω * (ε * a₂ ω) = ε * z ω := by
            simp only [ha₂]
            have := (hQpos ω).ne'
            field_simp
          linear_combination h0 - e1 + e2
        · by_cases h2 : n = t + 1
          · subst h2
            have h0' := hflow (t + 1) ω
            rw [hct1, hbt1, hbn ε (t + 1 + 1) (by omega)]
            have e3 : P (t + 1) ω * (ε * a₁ ω) = ε * a₂ ω := by
              simp only [ha₁, ha₂]
              have := (hPpos (t + 1) ω).ne'
              have := (hQpos ω).ne'
              field_simp
            linear_combination h0' + e3
          · rw [hcn ε n h1 h2, hbn ε n h2, hbn ε (n + 1) (by omega)]
            exact h0
      · by_cases h1 : n = t + 1
        · subst h1
          rw [hbt1]
          have hm : r ≤ Q t ω * b (t + 1) ω / (|z ω| + 1) := hωm ω
          rw [le_div_iff₀ (by positivity)] at hm
          have h2 : ε * z ω ≤ |ε| * (|z ω| + 1) := by
            have := le_abs_self (ε * z ω)
            rw [abs_mul] at this
            nlinarith [abs_nonneg ε]
          have h3 : |ε| * (|z ω| + 1) ≤ r * (|z ω| + 1) :=
            mul_le_mul_of_nonneg_right hε.le (by positivity)
          have h4 : ε * a₂ ω ≤ b (t + 1) ω := by
            simp only [ha₂]
            rw [← mul_div_assoc, div_le_iff₀ (hQpos ω)]
            linarith
          linarith
        · rw [hbn ε n h1]
          exact hbnn n ω
    -- the utility gain
    let φ : ℝ → ℝ := fun ε =>
      β ^ t * (𝔼.E 0 (fun ω => u (c t ω + ε * a₀ ω)) ω₀ - 𝔼.E 0 (fun ω => u (c t ω)) ω₀) +
      β ^ (t + 1) * (𝔼.E 0 (fun ω => u (c (t + 1) ω - ε * a₁ ω)) ω₀ -
        𝔼.E 0 (fun ω => u (c (t + 1) ω)) ω₀)
    have hdiff : ∀ ε ω, HasSum (fun n => β ^ n * 𝔼.E 0 (fun ω' => u (cε ε n ω')) ω)
        (expUtil 𝔼 β u c ω + (β ^ t * (𝔼.E 0 (fun ω' => u (c t ω' + ε * a₀ ω')) ω -
          𝔼.E 0 (fun ω' => u (c t ω')) ω) +
          β ^ (t + 1) * (𝔼.E 0 (fun ω' => u (c (t + 1) ω' - ε * a₁ ω')) ω -
          𝔼.E 0 (fun ω' => u (c (t + 1) ω')) ω))) := by
      intro ε ω
      have h := hasSum_of_eq_off_finset (hsum ω) {t, t + 1}
        (f' := fun n => β ^ n * 𝔼.E 0 (fun ω' => u (cε ε n ω')) ω) (fun n hn => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          rw [hcn ε n hn.1 hn.2])
      convert h using 1
      rw [Finset.sum_pair (by omega)]
      simp only [hct, hct1, expUtil]
      ring
    have hle : ∀ ε, |ε| < r → φ ε ≤ 0 := by
      intro ε hε
      have h1 := hbest (cε ε) (bε ε) (hfeas ε hε) (fun ω => (hdiff ε ω).summable) ω₀
      have e : expUtil 𝔼 β u (cε ε) ω₀ = expUtil 𝔼 β u c ω₀ + φ ε := (hdiff ε ω₀).tsum_eq
      linarith
    have hmax : IsLocalMax φ 0 := by
      have hmem : Set.Ioo (-r) r ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hrpos
      filter_upwards [hmem] with ε hε
      have : φ 0 = 0 := by simp [φ]
      rw [this]
      exact hle ε (abs_lt.mpr hε)
    have hd0 : HasDerivAt (fun ε => 𝔼.E 0 (fun ω => u (c t ω + ε * a₀ ω)) ω₀)
        (𝔼.E 0 (fun ω => u' (c t ω) * a₀ ω) ω₀) 0 :=
      hasDerivAt_E 𝔼 (f := fun ε ω => u (c t ω + ε * a₀ ω)) (fun ω => by
        have hin : HasDerivAt (fun ε : ℝ => c t ω + ε * a₀ ω) (a₀ ω) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₀ ω)).const_add (c t ω)
        have hu' : HasDerivAt u (u' (c t ω)) ((fun ε : ℝ => c t ω + ε * a₀ ω) 0) := by
          simpa using hu (c t ω)
        exact hu'.comp 0 hin) 0 ω₀
    have hd1 : HasDerivAt (fun ε => 𝔼.E 0 (fun ω => u (c (t + 1) ω - ε * a₁ ω)) ω₀)
        (𝔼.E 0 (fun ω => u' (c (t + 1) ω) * -a₁ ω) ω₀) 0 :=
      hasDerivAt_E 𝔼 (f := fun ε ω => u (c (t + 1) ω - ε * a₁ ω)) (fun ω => by
        have hin : HasDerivAt (fun ε : ℝ => c (t + 1) ω - ε * a₁ ω) (-a₁ ω) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a₁ ω)).const_sub (c (t + 1) ω)
        have hu' : HasDerivAt u (u' (c (t + 1) ω))
            ((fun ε : ℝ => c (t + 1) ω - ε * a₁ ω) 0) := by
          simpa using hu (c (t + 1) ω)
        exact hu'.comp 0 hin) 0 ω₀
    have hφ := ((hd0.sub_const (𝔼.E 0 (fun ω => u (c t ω)) ω₀)).const_mul (β ^ t)).add
      ((hd1.sub_const (𝔼.E 0 (fun ω => u (c (t + 1) ω)) ω₀)).const_mul (β ^ (t + 1)))
    have hzero := hmax.hasDerivAt_eq_zero hφ
    have hneg : (fun ω => u' (c (t + 1) ω) * -a₁ ω) =
        -(fun ω => u' (c (t + 1) ω) * a₁ ω) := by
      funext ω
      simp
    rw [hneg, map_neg] at hzero
    simp only [Pi.neg_apply] at hzero
    linarith
  -- Step B: the conditional Euler equation
  set A : Ω → ℝ := fun ω => u' (c t ω) / P t ω with hA
  set G : Ω → ℝ := fun ω => u' (c (t + 1) ω) / P (t + 1) ω with hG
  set Qi : Ω → ℝ := fun ω => (Q t ω)⁻¹ with hQi
  have hAk : 𝔼.E t A = A := known_div 𝔼 hPO hFK (hFK t (c t) u' (hcad t)) (hPad t)
  have hQik : 𝔼.E t Qi = Qi := hFK t (Q t) (fun r => r⁻¹) hQad
  set D : Ω → ℝ := A - β • (Qi * 𝔼.E t G) with hD
  have hDk : 𝔼.E t D = D := by
    rw [hD, map_sub, map_smul, hAk, hPO t _ _ hQik, 𝔼.E_E_self]
  have key : ∀ z, 𝔼.E t z = z → ∀ ω₀, 𝔼.E 0 (z * D) ω₀ = 0 := by
    intro z hz ω₀
    have h := stepA z hz ω₀
    have e1 : (fun ω => u' (c t ω) * (z ω / P t ω)) = z * A := by
      funext ω
      simp only [hA, Pi.mul_apply]
      ring
    have e2 : (fun ω => u' (c (t + 1) ω) * (z ω / (Q t ω * P (t + 1) ω))) = (z * Qi) * G := by
      funext ω
      simp only [hQi, hG, Pi.mul_apply]
      ring
    have hzQ : 𝔼.E t (z * Qi) = z * Qi := by rw [hPO t _ _ hz, hQik]
    have e3 : 𝔼.E 0 ((z * Qi) * G) = 𝔼.E 0 ((z * Qi) * 𝔼.E t G) := by
      rw [← 𝔼.tower (Nat.zero_le t) ((z * Qi) * G), hPO t _ _ hzQ]
    have e4 : z * D = z * A - β • ((z * Qi) * 𝔼.E t G) := by
      rw [hD]
      funext ω
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2, e3] at h
    rw [e4, map_sub, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hbt : β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
    have : β ^ t * (𝔼.E 0 (z * A) ω₀ - β * 𝔼.E 0 (z * Qi * 𝔼.E t G) ω₀) = 0 := by
      rw [pow_succ] at h
      linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hbt
    · exact h'
  have hDD : ∀ ω, D ω * D ω = 0 :=
    hF (D * D) (fun ω => mul_self_nonneg (D ω)) (key D hDk)
  have hD0 : ∀ ω, D ω = 0 := fun ω => mul_self_eq_zero.mp (hDD ω)
  funext ω
  have h := hD0 ω
  simp only [hD, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hQi] at h
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hQ0 := (hQpos ω).ne'
  have hA' : A ω = β * ((Q t ω)⁻¹ * 𝔼.E t G ω) := by linarith
  rw [hA']
  field_simp

/-- Cochrane (2023), p. 22, "Household maximization, budget constraint, and equilibrium ... imply
the household transversality condition (2.6)", under uncertainty: on a finite state space with
pull-out, functions of known variables known, a faithful `E_0`, and information that stops
growing after some date `K` (every finite event tree, `finiteTree_infoStable`), if `(c, b)` is an
optimal state-contingent plan, `u` is strictly increasing, prices are positive and adapted, the
bond price is (2.3) `Q_n = β E_n(P_n/P_{n+1})`, and discounted net demands
`β^n (c_n − y + s_n)` are summable in every state, then the transversality condition
`lim_N β^N E_t B_{t+N−1}/P_{t+N} = 0` holds at every date and state. Proof: real debt converges
pathwise, `β^n x_n → L ≥ 0`; if `L > 0` somewhere, consuming `L/(2β^T)` more at a late date
`T` and holding `P_n L/(2β^n)` less debt afterwards is feasible and raises expected utility. -/
theorem tvc_of_optimal_stoch [Finite Ω] (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hF : Faithful 𝔼) {K : ℕ} (hK : InfoStable 𝔼 K) {β y : ℝ} (hβ : 0 < β) {u : ℝ → ℝ}
    (hu : StrictMono u) {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : SOptimal 𝔼 β y u P s Q b₀ c b) (hPpos : ∀ n ω, 0 < P n ω) (hPad : 𝔼.Adapted P)
    (hQ : ∀ n, Q n = β • 𝔼.E n (fun ω => P n ω / P (n + 1) ω))
    (hd : ∀ ω, Summable fun n => β ^ n * (c n ω - y + s n ω)) (t : ℕ) :
    TVC 𝔼 β (fun n ω => b n ω / P n ω) t := by
  obtain ⟨⟨hb0, hcad, hbad, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  set x : ℕ → Ω → ℝ := fun n ω => b n ω / P n ω with hxdef
  have hstab : ∀ m n v, K ≤ m → K ≤ n → 𝔼.E m v = v → 𝔼.E n v = v := by
    intro m n v hm hn hv
    rw [hK n hn, ← hK m hm, hv]
  have hxk : ∀ n, 1 ≤ n → 𝔼.E n (x n) = x n := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact known_div 𝔼 hPO hFK (ForwardSolution.E_of_known 𝔼 (Nat.le_succ k) (hbad k))
      (hPad (k + 1))
  have hQp : ∀ n, K ≤ n → ∀ ω, Q n ω = β * (P n ω / P (n + 1) ω) := by
    intro n hn ω
    have hk : 𝔼.E n (fun ω => P n ω / P (n + 1) ω) = fun ω => P n ω / P (n + 1) ω :=
      hstab (n + 1) n _ (by omega) hn
        (known_div 𝔼 hPO hFK (ForwardSolution.E_of_known 𝔼 (Nat.le_succ n) (hPad n))
          (hPad (n + 1)))
    rw [hQ n, hk]
    rfl
  have hxflow : ∀ n, K ≤ n → ∀ ω, x n ω = (c n ω - y + s n ω) + β * x (n + 1) ω := by
    intro n hn ω
    have h1 := hflow n ω
    rw [hQp n hn ω] at h1
    have hP0 := (hPpos n ω).ne'
    have e : β * (P n ω / P (n + 1) ω) * b (n + 1) ω =
        β * P n ω * (b (n + 1) ω / P (n + 1) ω) := by ring
    have key : b n ω = P n ω * (c n ω - y + s n ω) + β * P n ω * x (n + 1) ω := by
      simp only [hxdef]
      linarith
    simp only [hxdef] at key ⊢
    rw [key]
    field_simp
  -- pathwise limits of the discounted real debt
  have hlimL : ∀ ω, ∃ L, Tendsto (fun n => β ^ n * x n ω) atTop (𝓝 L) ∧ 0 ≤ L := by
    intro ω
    set d : ℕ → ℝ := fun j => β ^ j * (c (K + j) ω - y + s (K + j) ω) with hd'
    have hbK : β ^ K ≠ 0 := pow_ne_zero K hβ.ne'
    have hds : Summable d := by
      have := ((summable_nat_add_iff K).mpr (hd ω)).mul_left (β ^ K)⁻¹
      refine this.congr fun j => ?_
      simp only [hd']
      rw [add_comm j K, pow_add]
      field_simp
    have htel : ∀ N, x K ω = ∑ j ∈ Finset.range N, d j + β ^ N * x (K + N) ω := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [ih, Finset.sum_range_succ, hxflow (K + N) (by omega) ω, pow_succ,
          show K + (N + 1) = K + N + 1 by omega]
        simp only [hd']
        ring
    have hlim : Tendsto (fun N => β ^ N * x (K + N) ω) atTop (𝓝 (x K ω - ∑' j, d j)) := by
      have h := (tendsto_const_nhds (x := x K ω)).sub hds.hasSum.tendsto_sum_nat
      refine h.congr fun N => ?_
      have := htel N
      linarith
    refine ⟨β ^ K * (x K ω - ∑' j, d j), ?_, ?_⟩
    · rw [← Filter.tendsto_add_atTop_iff_nat K]
      refine (hlim.const_mul (β ^ K)).congr fun N => ?_
      rw [show N + K = K + N by omega, pow_add]
      ring
    · exact mul_nonneg (pow_nonneg hβ.le K) (ge_of_tendsto' hlim fun N =>
        mul_nonneg (pow_nonneg hβ.le N) (div_nonneg (hbnn _ ω) (hPpos _ ω).le))
  choose L hL hL0 using hlimL
  -- the limit is known at `K`
  have hLk : 𝔼.E K L = L := by
    funext ω
    have h1 := E_tendsto 𝔼 (f := fun n ω' => β ^ n * x n ω') (fun ω' => hL ω') K ω
    have h2 : Tendsto (fun n => 𝔼.E K (fun ω' => β ^ n * x n ω') ω) atTop (𝓝 (L ω)) := by
      refine (hL ω).congr' ?_
      filter_upwards [eventually_ge_atTop (K + 1)] with n hn
      have e : (fun ω' => β ^ n * x n ω') = β ^ n • x n := by
        funext ω'
        simp
      rw [e, map_smul, hstab n K (x n) (by omega) le_rfl (hxk n (by omega))]
      rfl
    exact tendsto_nhds_unique h1 h2
  have hLkn : ∀ n, K ≤ n → 𝔼.E n L = L := fun n hn => hstab K n L le_rfl hn hLk
  -- the limit vanishes in every state
  have hLz : ∀ ω, L ω = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ω0, h0⟩ := hcon
    have hpos : 0 < L ω0 := lt_of_le_of_ne (hL0 ω0) (Ne.symm h0)
    have hev : ∀ᶠ n in atTop, K + 1 ≤ n ∧ ∀ ω, L ω / 2 ≤ β ^ n * x n ω := by
      refine (eventually_ge_atTop (K + 1)).and (Filter.eventually_all.mpr fun ω => ?_)
      rcases (hL0 ω).lt_or_eq with hp | hz
      · exact ((hL ω).eventually (lt_mem_nhds (show L ω / 2 < L ω by linarith))).mono
          fun n hn => hn.le
      · refine Filter.Eventually.of_forall fun n => ?_
        rw [← hz, zero_div]
        exact mul_nonneg (pow_nonneg hβ.le n) (div_nonneg (hbnn _ ω) (hPpos _ ω).le)
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
    have hTK := (hT T le_rfl).1
    set δ : Ω → ℝ := fun ω => L ω / (2 * β ^ T) with hδ
    let c' : ℕ → Ω → ℝ := fun n ω => c n ω + (if n = T then δ ω else 0)
    let b' : ℕ → Ω → ℝ := fun n ω =>
      b n ω - (if T < n then P n ω * (L ω / (2 * β ^ n)) else 0)
    have hc'T : ∀ ω, c' T ω = c T ω + δ ω := fun ω => by simp [c']
    have hc'n : ∀ n, n ≠ T → c' n = c n := fun n h => by
      funext ω
      simp [c', h]
    have hb'n : ∀ n, ¬ T < n → b' n = b n := fun n h => by
      funext ω
      simp [b', h]
    have hb'gt : ∀ n, T < n → ∀ ω, b' n ω = b n ω - P n ω * (L ω / (2 * β ^ n)) :=
      fun n h ω => by simp [b', h]
    have hfeas : SFeasible 𝔼 y P s Q b₀ c' b' := by
      refine ⟨by rw [hb'n 0 (by omega), hb0], fun n => ?_, fun n => ?_, fun n ω => ?_,
        fun n ω => ?_⟩
      · by_cases h : n = T
        · have e : c' n = c n + (2 * β ^ T)⁻¹ • L := by
            funext ω
            rw [h, hc'T]
            simp only [hδ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [e, map_add, map_smul, hcad n, hLkn n (by omega)]
        · rw [hc'n n h, hcad n]
      · by_cases h : T < n + 1
        · have e : b' (n + 1) = b (n + 1) - P (n + 1) * ((2 * β ^ (n + 1))⁻¹ • L) := by
            funext ω
            rw [hb'gt (n + 1) h ω]
            simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [e, map_sub, hbad n,
            hPO n _ _ (hstab (n + 1) n _ (by omega) (by omega) (hPad (n + 1))), map_smul,
            hLkn n (by omega)]
        · rw [hb'n (n + 1) h, hbad n]
      · have h1 := hflow n ω
        rcases lt_trichotomy n T with h | h | h
        · rw [hc'n n (by omega), hb'n n (by omega), hb'n (n + 1) (by omega)]
          exact h1
        · subst h
          rw [hc'T, hb'n n (lt_irrefl n), hb'gt (n + 1) (by omega) ω, hQp n (by omega) ω]
          rw [hQp n (by omega) ω] at h1
          have hP0 := (hPpos n ω).ne'
          have hP1 := (hPpos (n + 1) ω).ne'
          have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ.ne'
          have e : β * (P n ω / P (n + 1) ω) * (P (n + 1) ω * (L ω / (2 * β ^ (n + 1)))) =
              P n ω * δ ω := by
            simp only [hδ]
            rw [pow_succ]
            field_simp
          linear_combination h1 + e
        · rw [hc'n n (by omega), hb'gt n h ω, hb'gt (n + 1) (by omega) ω,
            hQp n (by omega) ω]
          rw [hQp n (by omega) ω] at h1
          have hP0 := (hPpos n ω).ne'
          have hP1 := (hPpos (n + 1) ω).ne'
          have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ.ne'
          have e : β * (P n ω / P (n + 1) ω) * (P (n + 1) ω * (L ω / (2 * β ^ (n + 1)))) =
              P n ω * (L ω / (2 * β ^ n)) := by
            rw [pow_succ]
            field_simp
          linear_combination h1 + e
      · by_cases h : T < n
        · rw [hb'gt n h ω]
          have hn := (hT n h.le).2 ω
          simp only [hxdef] at hn
          have hbn : 0 < β ^ n := pow_pos hβ n
          have hPn := hPpos n ω
          have e : β ^ n * (b n ω / P n ω) * P n ω = β ^ n * b n ω := by field_simp
          have h2 : L ω / 2 * P n ω ≤ β ^ n * (b n ω / P n ω) * P n ω :=
            mul_le_mul_of_nonneg_right hn hPn.le
          rw [e] at h2
          have : P n ω * (L ω / (2 * β ^ n)) ≤ b n ω := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            linarith
          linarith
        · rw [hb'n n h]
          exact hbnn n ω
    have hdev : ∀ ω, HasSum (fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c' n ω')) ω)
        (expUtil 𝔼 β u c ω + β ^ T * (𝔼.E 0 (fun ω' => u (c T ω' + δ ω')) ω -
          𝔼.E 0 (fun ω' => u (c T ω')) ω)) := by
      intro ω
      have h := hasSum_of_eq_off_finset (hsum ω) {T}
        (f' := fun n => β ^ n * 𝔼.E 0 (fun ω' => u (c' n ω')) ω)
        (fun n hn => by rw [hc'n n (by simpa using hn)])
      convert h using 1
      simp only [Finset.sum_singleton, hc'T, expUtil]
      ring
    set g : Ω → ℝ := fun ω' => u (c T ω' + δ ω') - u (c T ω') with hg
    have hg0 : ∀ ω', 0 ≤ g ω' := fun ω' => sub_nonneg.mpr (hu.monotone
      (le_add_of_nonneg_right (div_nonneg (hL0 ω') (by positivity))))
    have hgpos : 0 < g ω0 := sub_pos.mpr (hu (lt_add_of_pos_right _ (div_pos hpos
      (by positivity))))
    obtain ⟨ω1, hω1⟩ : ∃ ω1, 𝔼.E 0 g ω1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have := hF g hg0 hcon ω0
      linarith
    have hEpos : 0 < 𝔼.E 0 g ω1 := lt_of_le_of_ne (E_nonneg 𝔼 hg0 ω1) (Ne.symm hω1)
    have hle := hbest c' b' hfeas (fun ω => (hdev ω).summable) ω1
    have e : expUtil 𝔼 β u c' ω1 = expUtil 𝔼 β u c ω1 + β ^ T *
        (𝔼.E 0 (fun ω' => u (c T ω' + δ ω')) ω1 - 𝔼.E 0 (fun ω' => u (c T ω')) ω1) :=
      (hdev ω1).tsum_eq
    have eg : 𝔼.E 0 g ω1 = 𝔼.E 0 (fun ω' => u (c T ω' + δ ω')) ω1 -
        𝔼.E 0 (fun ω' => u (c T ω')) ω1 := by
      rw [hg, show (fun ω' => u (c T ω' + δ ω') - u (c T ω')) =
        (fun ω' => u (c T ω' + δ ω')) - (fun ω' => u (c T ω')) from rfl, map_sub]
      rfl
    have : 0 < β ^ T * 𝔼.E 0 g ω1 := mul_pos (pow_pos hβ T) hEpos
    rw [eg] at this
    linarith
  -- the transversality condition at every date
  intro ω
  have hpath : ∀ ω', Tendsto (fun N => β ^ N * x (t + N) ω') atTop (𝓝 0) := by
    intro ω'
    have h := (hL ω').comp (tendsto_add_atTop_nat t)
    rw [hLz ω'] at h
    have h2 := h.const_mul (β ^ t)⁻¹
    rw [mul_zero] at h2
    refine h2.congr fun N => ?_
    simp only [Function.comp]
    rw [show N + t = t + N by omega, pow_add]
    have := pow_ne_zero t hβ.ne'
    field_simp
  have h := E_tendsto 𝔼 (f := fun N ω' => β ^ N * x (t + N) ω') (g := fun _ => 0) hpath t ω
  have h0 : 𝔼.E t (fun _ => (0 : ℝ)) ω = 0 := by rw [𝔼.const]
  rw [h0] at h
  refine h.congr fun N => ?_
  have e : (fun ω' => β ^ N * x (t + N) ω') = β ^ N • x (t + N) := by
    funext ω'
    simp
  rw [e, map_smul]
  rfl

/-- Cochrane (2023), eq. (2.7), p. 22, derived from household optimisation under uncertainty:
under the hypotheses of `tvc_of_optimal_stoch` with consumption at the endowment `c = y`,
adapted absolutely summable surpluses and conditional monotone convergence (every finite tree),
real debt equals the present value of surpluses at every date. -/
theorem valuation_of_optimal_stoch [Finite Ω] (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    (hF : Faithful 𝔼) (hMC : MonotoneConvergence 𝔼) {K : ℕ} (hK : InfoStable 𝔼 K) {β y : ℝ}
    (hβ : 0 < β) {u : ℝ → ℝ} (hu : StrictMono u) {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : SOptimal 𝔼 β y u P s Q b₀ (fun _ _ => y) b) (hPpos : ∀ n ω, 0 < P n ω)
    (hPad : 𝔼.Adapted P) (hQ : ∀ n, Q n = β • 𝔼.E n (fun ω => P n ω / P (n + 1) ω))
    (hs : AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hd : ∀ ω, Summable fun n => β ^ n * s n ω) (t : ℕ) :
    (fun ω => b t ω / P t ω) = pv 𝔼 β s t := by
  have hd' : ∀ ω, Summable fun n => β ^ n * ((fun _ _ => y : ℕ → Ω → ℝ) n ω - y + s n ω) :=
    fun ω => (hd ω).congr fun n => by ring
  have htvc := tvc_of_optimal_stoch 𝔼 hPO hFK hF hK hβ hu hopt hPpos hPad hQ hd'
  obtain ⟨⟨-, -, hbad, hflow, -⟩, -, -⟩ := hopt
  have hfl : FlowX 𝔼 β (fun n ω => b n ω / P n ω) s := fun n =>
    (flow_iff_real_x 𝔼 hPO (hPpos n) (hPad n) (hbad n) (hQ n)).mp fun ω => by
      have := hflow n ω
      linarith
  exact (valuation_iff 𝔼 hMC hβ.le hs hsad).mp ⟨hfl, htvc⟩ t

end Cochrane.IntertemporalModel.Valuation
