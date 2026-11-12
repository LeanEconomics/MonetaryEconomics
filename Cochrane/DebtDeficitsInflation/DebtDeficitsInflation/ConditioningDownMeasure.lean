/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.ExpectationsMeasureIID
import DebtDeficitsInflation.ConditioningDown
import DebtDeficitsInflation.LinearizedIdentities

/-!
# Conditioning down on a general probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, pp. 101–102, and
Online Appendix Chapter 2, §2.1.7, eqs. (2.22)–(2.23), pp. 602–603; the identities conditioned
down are (3.17)–(3.20), pp. 63–65, and (4.2), p. 87.

People condition on `𝓕_t` (`Ω_t` in the book), the econometrician on a coarser `𝓖_t ≤ 𝓕_t`
(`I_t ⊂ Ω_t`, the VAR's information). Both are filtrations on one probability space `(Ω, P)`, and
both expectation operators are Mathlib's conditional expectations `P[· | 𝓕_t]`, `P[· | 𝓖_t]`, so
nothing is finite or finitely supported. The cross-information tower property
`E(E(x|𝓕_t)|𝓖_t) = E(x|𝓖_t)` is Mathlib's `condExp_condExp_of_le`.

## Main definitions

* `coarsen S 𝓖`: the econometrician's system — same probability, filtration `𝓖`.
* `Nested S 𝓖`: `𝓖_t ≤ 𝓕_t` at every date; `MeasCoarser SI SΩ` for a pair of systems, and
  `eq_coarsen`: every nested pair is of the form `(coarsen SΩ 𝓖, SΩ)`.
* `KnownAE 𝓖 t v`: `v` is a.e. equal to a `𝓖_t`-measurable variable (`v_t ∈ I_t`).
* `lagFiltration S`: the econometrician sees the agents' information with a one-period lag.

## Main results

* `E_coarsen_tower`, `condDown_general` (`E(X|I_t) = E(v_t|I_t)` always), `condDown_iff`
  (`v_t = E(X|I_t)` iff `v_t ∈ I_t`), `known_iff_E_eq`.
* The valuation equation (2.22) ⇒ (2.23): `condDown_valuation` (the econometrician's discounted
  forecasts sum to `E(v_t|I_t)`) and `condDown_valuation_iff` (to `v_t` iff `v_t ∈ I_t`).
* The flow identity (3.17) ex post: `pv_ex_post`, `pv_E` (under ANY information, the discounted
  forecasts sum to the forecast of `v_t`), `pv_agents`, `condDown_flow_iff` (Links.condDown_flow
  on a general probability space).
* Unexpected inflation (3.20): `innov_pv`, `unexpected_inflation_any` — for ANY information set,
  `Δπ − Δrⁿ = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}ρʲΔr + Δ_{t+1}v_t`; `unexpected_inflation_agents` (the
  book's (3.20), the extra term vanishes); `innov_coarsen_of_known` (it also vanishes for the
  econometrician when `v_t ∈ I_t`); `E_coarsen_innov` (the agents' news is unforecastable with the
  coarser information).
* The simple model (4.2): `constExp_condDown`, `innov_return_condDown` (constant expected returns
  condition down), `simple_model_any` (`Δπ − Δrⁿ = −∑ρʲΔs̃ + Δ_{t+1}v_t` for any nested
  information), `simple_model_agents` (`Δπ = −∑ρʲΔs̃`), `simple_model_econ_iff` (the book's form
  holds for the econometrician iff `Δ^I_{t+1}v_t = 0`).
* Correction: `Example.econ_decomp_counterexample` — i.i.d. shocks, MA(1) surplus, lagged
  econometrician: the agents' decomposition holds, the econometrician's book-form decomposition
  fails.
* Links: `coarsen_toExpectationSystem_E` (the finite full-support case is the
  `ConditioningDown.CondExp.condExpSystem` of Mathlib), `coarser_core` (the abstract `Coarser`),
  `condDown_iff_core` (the general `condDown_iff` IS the abstract `ConditioningDown.condDown_iff`
  there), `unexpected_inflation_core` (the core (3.20) for the bridged system).
-/

namespace Cochrane.DebtDeficitsInflation.ConditioningDownMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.DebtDeficitsInflation.ExpectationsMeasure
open Cochrane.DebtDeficitsInflation.LinearizedIdentities (Recursion Flow rec_finite tvc_of_bound
  flow_iff_recursion)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ### Two nested information sets -/

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): the econometrician's expectation system — the same
probability as the agents' system `S`, with the coarser filtration `𝓖`. -/
def coarsen (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) : MeasExpectationSystem Ω :=
  ⟨S.P, 𝓖⟩

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): the econometrician's information is contained in the
agents' at every date. -/
def Nested (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) : Prop := ∀ t, 𝓖 t ≤ S.𝓕 t

/-- Cochrane (2023), Online Appendix p. 602 ("two nested expectation systems"): `SI` and `SΩ`
share the probability and `SI`'s information is contained in `SΩ`'s. -/
def MeasCoarser (SI SΩ : MeasExpectationSystem Ω) : Prop := SI.P = SΩ.P ∧ ∀ t, SI.𝓕 t ≤ SΩ.𝓕 t

/-- Cochrane (2023), Online Appendix p. 602: every nested pair of systems is the agents' system
together with its coarsening by the econometrician's filtration. -/
theorem eq_coarsen {SI SΩ : MeasExpectationSystem Ω} (h : MeasCoarser SI SΩ) :
    SI = coarsen SΩ SI.𝓕 ∧ Nested SΩ SI.𝓕 := by
  obtain ⟨hP, hle⟩ := h
  refine ⟨?_, hle⟩
  cases SI
  cases SΩ
  simp only at hP
  subst hP
  rfl

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): `v` is (a.e. equal to) a `𝓖_t`-measurable random
variable. -/
def KnownAE (μ : Measure Ω) (𝓖 : Filtration ℕ mΩ) (t : ℕ) (v : Ω → ℝ) : Prop :=
  ∃ w : Ω → ℝ, StronglyMeasurable[𝓖 t] w ∧ v =ᵐ[μ] w

/-- Cochrane (2023), p. 101: the econometrician's probability is the agents'. -/
theorem coarsen_μ (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) :
    (coarsen S 𝓖).μ = S.μ := rfl

/-- Cochrane (2023), p. 101: the econometrician's forecast is the Mathlib conditional expectation
given `𝓖_t`. -/
theorem coarsen_E (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) (t : ℕ) (x : Ω → ℝ) :
    (coarsen S 𝓖).E t x = S.μ[x | 𝓖 t] := rfl

/-- Cochrane (2023), p. 101 (`E(E(x|Ω_t)|I_s) = E(x|I_s)`, `s ≤ t`): the tower property across
information sets (Mathlib's `condExp_condExp_of_le`). -/
theorem E_coarsen_tower {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) :
    (coarsen S 𝓖).E s (S.E t x) =ᵐ[S.μ] (coarsen S 𝓖).E s x :=
  condExp_condExp_of_le ((𝓖.mono hst).trans (h t)) (S.𝓕.le t)

/-- Cochrane (2023), p. 101 ("if not, the left-hand side should be `E(v_t|I_t)`"): if
`v_t = E(X|Ω_t)` a.e., then `E(X|I_t) = E(v_t|I_t)` a.e., for every random variable `X`. -/
theorem condDown_general {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {t : ℕ} {v X : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t X) :
    (coarsen S 𝓖).E t X =ᵐ[S.μ] (coarsen S 𝓖).E t v :=
  ((E_coarsen_tower h le_rfl X).symm.trans ((coarsen S 𝓖).E_congr hv t).symm)

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): an integrable `v` is a.e. its own `I_t`-forecast iff it
is a.e. `𝓖_t`-measurable. -/
theorem known_iff_E_eq (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) {t : ℕ}
    {v : Ω → ℝ} (hi : Integrable v S.μ) :
    v =ᵐ[S.μ] (coarsen S 𝓖).E t v ↔ KnownAE S.μ 𝓖 t v := by
  constructor
  · intro h
    exact ⟨_, (coarsen S 𝓖).stronglyMeasurable_E t v, h⟩
  · rintro ⟨w, hw, hvw⟩
    have hwi : Integrable w S.μ := hi.congr hvw
    have hE : (coarsen S 𝓖).E t w = w := (coarsen S 𝓖).E_of_stronglyMeasurable hw hwi
    exact hvw.trans (hE ▸ ((coarsen S 𝓖).E_congr hvw t).symm)

/-- Cochrane (2023), p. 101 ("this conditioning down is valid, so long as `v_t ∈ I_t`") and Online
Appendix eqs. (2.22)–(2.23), p. 602 ("only if we include the value of debt in the VAR"): on any
probability space, if `v_t = E(X|Ω_t)` a.e., then `v_t = E(X|I_t)` a.e. **if and only if** `v_t` is
(a.e.) `I_t`-measurable. No integrability of `X` is needed. -/
theorem condDown_iff {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {t : ℕ} {v X : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t X) :
    v =ᵐ[S.μ] (coarsen S 𝓖).E t X ↔ KnownAE S.μ 𝓖 t v := by
  have hi : Integrable v S.μ := (S.integrable_E t X).congr hv.symm
  rw [← known_iff_E_eq S 𝓖 hi]
  have hg := condDown_general h hv
  constructor
  · intro h1
    exact h1.trans hg
  · intro h1
    exact h1.trans hg.symm

/-- Cochrane (2023), p. 102 ("the only way to rescue such a calculation is to assume … `I_t = Ω_t`
… `v_t` would be an exact function of the observed information"): with no coarsening, `v_t` is
always known. -/
theorem known_of_same (S : MeasExpectationSystem Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v =ᵐ[S.μ] S.E t X) : KnownAE S.μ S.𝓕 t v :=
  ⟨_, S.stronglyMeasurable_E t X, hv⟩

/-- Cochrane (2023), eq. (2.13), p. 30, across information sets: the agents' news
`Δ^Ω_{t+1}x = E(x|Ω_{t+1}) − E(x|Ω_t)` cannot be forecast with the coarser information,
`E(Δ^Ω_{t+1}x | I_s) = 0` for `s ≤ t`. -/
theorem E_coarsen_innov {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) :
    (coarsen S 𝓖).E s (S.innov t x) =ᵐ[S.μ] 0 := by
  filter_upwards [(coarsen S 𝓖).E_sub (S.integrable_E (t + 1) x) (S.integrable_E t x) s,
    E_coarsen_tower h (hst.trans (Nat.le_succ t)) x, E_coarsen_tower h hst x] with ω h1 h2 h3
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, h1, Pi.sub_apply, h2, h3, sub_self,
    Pi.zero_apply]

/-! ### Present values: the valuation equation and the flow identity -/

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101: if the valuation equation holds with
the agents' information, `v_t = E(∑ρʲs_{t+1+j}|Ω_t)` a.e. (bounded measurable surpluses,
`|ρ| < 1`), then with the econometrician's information the discounted forecasts sum to
`E(v_t|I_t)`: a.e. `∑ρʲE(s_{t+1+j}|I_t) = E(v_t|I_t)`, a genuine `HasSum`. -/
theorem condDown_valuation {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ}
    (hsm : ∀ j, AEStronglyMeasurable (s j) S.μ) {K : ℝ} (hs : ∀ j, ∀ᵐ ω ∂S.μ, |s j ω| ≤ K)
    {t : ℕ} {v : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω)) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω)
      ((coarsen S 𝓖).E t v ω) := by
  set G := coarsen S 𝓖
  have hc : Summable fun j => |ρ| ^ j * K :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K
  have hb : ∀ j, ∀ᵐ ω ∂S.μ, |ρ ^ j * s (t + 1 + j) ω| ≤ |ρ| ^ j * K := fun j => by
    filter_upwards [hs (t + 1 + j)] with ω hω
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left hω (pow_nonneg (abs_nonneg _) _)
  have hE := G.E_hasSum (f := fun j ω => ρ ^ j * s (t + 1 + j) ω) hc
    (fun j => (hsm (t + 1 + j)).const_mul _) hb t
  have hsmul : ∀ j, G.E t (fun ω => ρ ^ j * s (t + 1 + j) ω) =ᵐ[S.μ]
      fun ω => ρ ^ j * G.E t (s (t + 1 + j)) ω := fun j => G.E_smul (ρ ^ j) (s (t + 1 + j)) t
  filter_upwards [hE, ae_all_iff.2 hsmul, condDown_general h hv] with ω h1 h2 h3
  rw [← h3]
  exact h1.congr_fun fun j => (h2 j).symm

/-- Cochrane (2023), eqs. (2.22)–(2.23), p. 602, and p. 101 ("this conditioning down is valid, so
long as `v_t ∈ I_t`"): under the valuation equation with the agents' information, the
econometrician's discounted forecasts sum to `v_t` a.e. **iff** `v_t` is in the VAR information. -/
theorem condDown_valuation_iff {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} (hρ : |ρ| < 1) {s : ℕ → Ω → ℝ}
    (hsm : ∀ j, AEStronglyMeasurable (s j) S.μ) {K : ℝ} (hs : ∀ j, ∀ᵐ ω ∂S.μ, |s j ω| ≤ K)
    {t : ℕ} {v : Ω → ℝ} (hv : v =ᵐ[S.μ] S.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω)) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t (s (t + 1 + j)) ω) (v ω)) ↔
      KnownAE S.μ 𝓖 t v := by
  have hi : Integrable v S.μ := (S.integrable_E t _).congr hv.symm
  rw [← known_iff_E_eq S 𝓖 hi]
  have hH := condDown_valuation h hρ hsm hs hv
  constructor
  · intro h1
    filter_upwards [h1, hH] with ω a b
    exact a.unique b
  · intro h1
    filter_upwards [h1, hH] with ω a b
    rw [a]
    exact b

/-- Cochrane (2023), eq. (3.18), p. 63, ex post on a probability space: if
`x_t = ρx_{t+1} + f_{t+1}` holds state by state, `|ρ| < 1` and `x`, `f` are (essentially) bounded,
then a.e. `x_t = ∑_{j≥0} ρʲ f_{t+1+j}` (a genuine `HasSum`). -/
theorem pv_ex_post {μ : Measure Ω} {ρ : ℝ} (hρ : |ρ| < 1) {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) {M K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂μ, |x t ω| ≤ M)
    (hf : ∀ t, ∀ᵐ ω ∂μ, |f t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂μ, HasSum (fun j => ρ ^ j * f (t + 1 + j) ω) (x t ω) := by
  filter_upwards [ae_all_iff.2 hx, ae_all_iff.2 hf] with ω hMω hKω
  have hs : Summable fun j => ‖ρ ^ j * f (t + 1 + j) ω‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hKω _) (pow_nonneg (abs_nonneg _) _)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs]
  have hfin : (fun T => ∑ j ∈ Finset.range T, ρ ^ j * f (t + 1 + j) ω) =
      fun T => x t ω - ρ ^ T * x (t + T) ω := by
    funext T
    have := congrFun (rec_finite hrec t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  rw [hfin]
  simpa using tendsto_const_nhds.sub (tvc_of_bound hρ (fun T => hMω (t + T)))

/-- Cochrane (2023), eq. (3.19), p. 64, under ANY information: with the recursion holding ex post
and bounded measurable `x`, `f`, `|ρ| < 1`, for every date `m`, a.e.
`∑_{j≥0} ρʲ E_m f_{t+1+j} = E_m x_t`. -/
theorem pv_E (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) {M K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ M)
    (hfm : ∀ t, AEStronglyMeasurable (f t) T.μ) (hf : ∀ t, ∀ᵐ ω ∂T.μ, |f t ω| ≤ K)
    (t m : ℕ) :
    ∀ᵐ ω ∂T.μ, HasSum (fun j => ρ ^ j * T.E m (f (t + 1 + j)) ω) (T.E m (x t) ω) := by
  have hc : Summable fun j => |ρ| ^ j * K :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K
  have hb : ∀ j, ∀ᵐ ω ∂T.μ, |ρ ^ j * f (t + 1 + j) ω| ≤ |ρ| ^ j * K := fun j => by
    filter_upwards [hf (t + 1 + j)] with ω hω
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left hω (pow_nonneg (abs_nonneg _) _)
  have hE := T.E_hasSum (f := fun j ω => ρ ^ j * f (t + 1 + j) ω) hc
    (fun j => (hfm (t + 1 + j)).const_mul _) hb m
  have hsmul : ∀ j, T.E m (fun ω => ρ ^ j * f (t + 1 + j) ω) =ᵐ[T.μ]
      fun ω => ρ ^ j * T.E m (f (t + 1 + j)) ω := fun j => T.E_smul (ρ ^ j) (f (t + 1 + j)) m
  have hX : (fun ω => ∑' j, ρ ^ j * f (t + 1 + j) ω) =ᵐ[T.μ] x t := by
    filter_upwards [pv_ex_post hρ hrec hx hf t] with ω hω
    exact hω.tsum_eq
  filter_upwards [hE, ae_all_iff.2 hsmul, T.E_congr hX m] with ω h1 h2 h3
  rw [← h3]
  exact h1.congr_fun fun j => (h2 j).symm

/-- Cochrane (2023), eq. (3.19), p. 64: under the agents' information (`v_t` known at `t`) the
discounted forecasts of `s̃ + g − r` sum to `v_t` itself. -/
theorem pv_agents (S : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {v f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ v f) (hvm : StronglyAdapted S.𝓕 v) {M K : ℝ}
    (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M) (hfm : ∀ t, AEStronglyMeasurable (f t) S.μ)
    (hf : ∀ t, ∀ᵐ ω ∂S.μ, |f t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (f (t + 1 + j)) ω) (v t ω) := by
  have hE : S.E t (v t) = v t :=
    S.E_of_stronglyMeasurable (hvm t) (MeasExpectationSystem.BddRV.integrable (S := S)
      ⟨((hvm t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hv t⟩)
  filter_upwards [pv_E S hρ hrec hv hfm hf t t] with ω hω
  rwa [hE] at hω

/-- Cochrane (2023), p. 101, and Online Appendix p. 602, with the flow identity (3.17) holding ex
post (the measure-theoretic `Links.condDown_flow`): for any coarser information the discounted
forecasts of `s̃ + g − r` sum to `E(v_t|I_t)`, hence to `v_t` iff `v_t ∈ I_t`. -/
theorem condDown_flow_iff {S : MeasExpectationSystem Ω} (𝓖 : Filtration ℕ mΩ) {ρ : ℝ}
    (hρ : |ρ| < 1) {v r g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) {M K : ℝ}
    (hvm : ∀ t, AEStronglyMeasurable (v t) S.μ) (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hfm : ∀ t, AEStronglyMeasurable (s t + g t - r t) S.μ)
    (hf : ∀ t, ∀ᵐ ω ∂S.μ, |(s t + g t - r t) ω| ≤ K) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) ((coarsen S 𝓖).E t (v t) ω)) ∧
    ((∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).E t
      (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω) (v t ω)) ↔ KnownAE S.μ 𝓖 t (v t)) := by
  have hrec := (flow_iff_recursion ρ v r g s).1 hflow
  have hH := pv_E (coarsen S 𝓖) hρ hrec hv hfm hf t t
  have hi : Integrable (v t) S.μ := MeasExpectationSystem.BddRV.integrable (S := S) ⟨hvm t, M, hv t⟩
  refine ⟨hH, ?_⟩
  rw [← known_iff_E_eq S 𝓖 hi]
  constructor
  · intro h1
    filter_upwards [h1, hH] with ω a b
    exact a.unique b
  · intro h1
    filter_upwards [h1, hH] with ω a b
    rw [a]
    exact b

/-! ### Unexpected inflation under any information set -/

/-- Cochrane (2023), eq. (2.13), p. 30 (tool): the news about an essentially bounded variable is
bounded by twice the bound. -/
theorem abs_innov_le (T : MeasExpectationSystem Ω) {x : Ω → ℝ} {K : ℝ}
    (hx : ∀ᵐ ω ∂T.μ, |x ω| ≤ K) (t : ℕ) : ∀ᵐ ω ∂T.μ, |T.innov t x ω| ≤ 2 * K := by
  filter_upwards [T.abs_E_le hx (t + 1), T.abs_E_le hx t] with ω h1 h2
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
  calc |T.E (t + 1) x ω - T.E t x ω| ≤ |T.E (t + 1) x ω| + |T.E t x ω| := abs_sub _ _
    _ ≤ 2 * K := by linarith

/-- Cochrane (2023), eq. (3.20), p. 65 (tool): discounted news about a bounded process is
summable a.e. -/
theorem summable_innov (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → Ω → ℝ}
    {K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ K) (t k : ℕ) :
    ∀ᵐ ω ∂T.μ, Summable fun j => ρ ^ j * T.innov t (x (k + j)) ω := by
  filter_upwards [ae_all_iff.2 fun j => abs_innov_le T (hx (k + j)) t] with ω hω
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (2 * K)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hω j) (pow_nonneg (abs_nonneg _) _)

/-- Cochrane (2023), eq. (3.20), p. 65, under ANY information: with the recursion
`x_t = ρx_{t+1} + f_{t+1}` ex post (bounded measurable `x`, `f`, `|ρ| < 1`), a.e.
`∑_{j≥0} ρʲ Δ_{t+1} f_{t+1+j} = Δ_{t+1} x_t`, where `Δ_{t+1} = E_{t+1} − E_t` is the news of the
information set at hand. -/
theorem innov_pv (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1) {x f : ℕ → Ω → ℝ}
    (hrec : Recursion ρ x f) {M K : ℝ} (hx : ∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ M)
    (hfm : ∀ t, AEStronglyMeasurable (f t) T.μ) (hf : ∀ t, ∀ᵐ ω ∂T.μ, |f t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂T.μ, HasSum (fun j => ρ ^ j * T.innov t (f (t + 1 + j)) ω) (T.innov t (x t) ω) := by
  filter_upwards [pv_E T hρ hrec hx hfm hf t (t + 1), pv_E T hρ hrec hx hfm hf t t] with ω h1 h2
  refine (h1.sub h2).congr_fun fun j => ?_
  simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (3.20), p. 65, under ANY information set on a general probability space:
if the flow identity (3.17) `ρv_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` holds ex post with
`r = rⁿ − π` (bounded measurable `v`, `s̃`, `g`, `r`, integrable `rⁿ`, `|ρ| < 1`), then a.e.
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j} + Δ_{t+1}v_t`.
The last term — news about the date-`t` value of debt — vanishes for the agents (`v_t` known at
`t`) but not in general for a coarser information set. -/
theorem unexpected_inflation_any (T : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    {M Ks Kg Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂T.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) T.μ) (hs : ∀ t, ∀ᵐ ω ∂T.μ, |s t ω| ≤ Ks)
    (hgm : ∀ t, AEStronglyMeasurable (g t) T.μ) (hg : ∀ t, ∀ᵐ ω ∂T.μ, |g t ω| ≤ Kg)
    (hrm : ∀ t, AEStronglyMeasurable (r t) T.μ) (hrb : ∀ t, ∀ᵐ ω ∂T.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) T.μ) (t : ℕ) :
    ∀ᵐ ω ∂T.μ, T.innov t (infl (t + 1)) ω - T.innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * T.innov t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * T.innov t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 2 + j)) ω + T.innov t (v t) ω := by
  have hint : ∀ {x : ℕ → Ω → ℝ} {K : ℝ}, (∀ t, AEStronglyMeasurable (x t) T.μ) →
      (∀ t, ∀ᵐ ω ∂T.μ, |x t ω| ≤ K) → ∀ t, Integrable (x t) T.μ :=
    fun hm hb t => MeasExpectationSystem.BddRV.integrable (S := T) ⟨hm t, _, hb t⟩
  have hsi := hint hsm hs
  have hgi := hint hgm hg
  have hri := hint hrm hrb
  have hfm : ∀ t, AEStronglyMeasurable (s t + g t - r t) T.μ :=
    fun t => ((hsm t).add (hgm t)).sub (hrm t)
  have hfb : ∀ t, ∀ᵐ ω ∂T.μ, |(s t + g t - r t) ω| ≤ Ks + Kg + Kr := fun t => by
    filter_upwards [hs t, hg t, hrb t] with ω h1 h2 h3
    simp only [Pi.add_apply, Pi.sub_apply]
    calc |s t ω + g t ω - r t ω| ≤ |s t ω + g t ω| + |r t ω| := abs_sub _ _
      _ ≤ |s t ω| + |g t ω| + |r t ω| := by linarith [abs_add_le (s t ω) (g t ω)]
      _ ≤ Ks + Kg + Kr := by linarith
  have hH := innov_pv T hρ ((flow_iff_recursion ρ v r g s).1 hflow) hv hfm hfb t
  -- the news is linear (a.e.)
  have hlin : ∀ j, ∀ᵐ ω ∂T.μ, T.innov t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω =
      T.innov t (s (t + 1 + j)) ω + T.innov t (g (t + 1 + j)) ω -
        T.innov t (r (t + 1 + j)) ω := fun j => by
    have hsg := (hsi (t + 1 + j)).add (hgi (t + 1 + j))
    filter_upwards [T.E_sub hsg (hri (t + 1 + j)) (t + 1), T.E_sub hsg (hri (t + 1 + j)) t,
      T.E_add (hsi (t + 1 + j)) (hgi (t + 1 + j)) (t + 1),
      T.E_add (hsi (t + 1 + j)) (hgi (t + 1 + j)) t] with ω h1 h2 h3 h4
    simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, Pi.add_apply] at *
    rw [h1, h2, h3, h4]
    ring
  have hinfl : ∀ᵐ ω ∂T.μ, T.innov t (r (t + 1)) ω =
      T.innov t (rn (t + 1)) ω - T.innov t (infl (t + 1)) ω := by
    have hii : Integrable (infl (t + 1)) T.μ := by
      have : infl (t + 1) = rn (t + 1) - r (t + 1) := by rw [hr (t + 1)]; abel
      rw [this]
      exact (hrn (t + 1)).sub (hri (t + 1))
    filter_upwards [T.E_sub (hrn (t + 1)) hii (t + 1), T.E_sub (hrn (t + 1)) hii t] with ω h1 h2
    simp only [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply]
    rw [hr (t + 1), h1, h2, Pi.sub_apply, Pi.sub_apply]
    ring
  filter_upwards [hH, ae_all_iff.2 hlin, hinfl, summable_innov T hρ hs t (t + 1),
    summable_innov T hρ hg t (t + 1), summable_innov T hρ hrb t (t + 1)] with ω h1 h2 h3 h4 h5 h6
  have hsum : HasSum (fun j => ρ ^ j * T.innov t (s (t + 1 + j)) ω +
      ρ ^ j * T.innov t (g (t + 1 + j)) ω - ρ ^ j * T.innov t (r (t + 1 + j)) ω)
      (T.innov t (v t) ω) := h1.congr_fun fun j => by rw [h2 j]; ring
  have hsplit := (h4.hasSum.add h5.hasSum).sub h6.hasSum
  have heq := hsum.unique hsplit
  have hr0 := h6.tsum_eq_zero_add
  simp only [pow_zero, one_mul, add_zero] at hr0
  have hr1 : ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 1 + (j + 1))) ω =
      ∑' j, ρ ^ (j + 1) * T.innov t (r (t + 2 + j)) ω :=
    tsum_congr fun j => by rw [show t + 1 + (j + 1) = t + 2 + j by omega]
  rw [hr1, h3] at hr0
  linarith

/-- Cochrane (2023), eq. (3.20), p. 65 (the book's form, for the agents): when `v_t` is known at
`t` the extra term vanishes, `Δπ − Δrⁿ = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}ρʲΔr`. -/
theorem unexpected_inflation_agents (S : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hvm : StronglyAdapted S.𝓕 v)
    {M Ks Kg Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hgm : ∀ t, AEStronglyMeasurable (g t) S.μ) (hg : ∀ t, ∀ᵐ ω ∂S.μ, |g t ω| ≤ Kg)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov t (infl (t + 1)) ω - S.innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * S.innov t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * S.innov t (r (t + 2 + j)) ω := by
  have hvi : Integrable (v t) S.μ := MeasExpectationSystem.BddRV.integrable (S := S)
    ⟨((hvm t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hv t⟩
  have h0 : S.innov t (v t) = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov,
      S.E_of_stronglyMeasurable ((hvm t).mono (S.𝓕.mono (Nat.le_succ t))) hvi,
      S.E_of_stronglyMeasurable (hvm t) hvi, sub_self]
  filter_upwards [unexpected_inflation_any S hρ hflow hr hv hsm hs hgm hg hrm hrb hrn t]
    with ω hω
  rw [hω, h0, Pi.zero_apply, add_zero]

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): if the value of debt is in the econometrician's
information, its news vanishes for the econometrician, `Δ^I_{t+1} v_t = 0` a.e. -/
theorem innov_coarsen_of_known (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) {t : ℕ}
    {v : Ω → ℝ} (hi : Integrable v S.μ) (hk : KnownAE S.μ 𝓖 t v) :
    (coarsen S 𝓖).innov t v =ᵐ[S.μ] 0 := by
  obtain ⟨w, hw, hvw⟩ := hk
  have hwi : Integrable w S.μ := hi.congr hvw
  have h1 : (coarsen S 𝓖).E (t + 1) w = w :=
    (coarsen S 𝓖).E_of_stronglyMeasurable (hw.mono (𝓖.mono (Nat.le_succ t))) hwi
  have h2 : (coarsen S 𝓖).E t w = w := (coarsen S 𝓖).E_of_stronglyMeasurable hw hwi
  filter_upwards [(coarsen S 𝓖).E_congr hvw (t + 1), (coarsen S 𝓖).E_congr hvw t] with ω a b
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, a, b, h1, h2, sub_self,
    Pi.zero_apply]

/-- Cochrane (2023), §4.2, p. 87 (constant expected returns) conditioned down: if the agents expect
a constant real return, `E(r_{t+1}|Ω_t) = c`, so does the econometrician at every earlier date,
`E(r_{t+1}|I_m) = c` for `m ≤ t`. -/
theorem constExp_condDown {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {r : ℕ → Ω → ℝ} {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c) {m t : ℕ}
    (hmt : m ≤ t) : (coarsen S 𝓖).E m (r (t + 1)) =ᵐ[S.μ] fun _ => c := by
  filter_upwards [(E_coarsen_tower h hmt (r (t + 1))).symm, (coarsen S 𝓖).E_congr (hc t) m]
    with ω a b
  rw [a, b, (coarsen S 𝓖).E_const]

/-- Cochrane (2023), §4.2, p. 87: under constant expected returns the news about future returns
vanishes for the econometrician (and for the agents, `𝓖 = 𝓕`), `Δ^I_{t+1} r_{t+2+j} = 0`. -/
theorem innov_return_condDown {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {r : ℕ → Ω → ℝ} {c : ℝ}
    (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c) (t j : ℕ) :
    (coarsen S 𝓖).innov t (r (t + 2 + j)) =ᵐ[S.μ] 0 := by
  have e : t + 2 + j = (t + 1 + j) + 1 := by omega
  rw [e]
  filter_upwards [constExp_condDown h hc (show t + 1 ≤ t + 1 + j by omega),
    constExp_condDown h hc (show t ≤ t + 1 + j by omega)] with ω a b
  rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, a, b, sub_self,
    Pi.zero_apply]

/-- Cochrane (2023), eq. (4.2), p. 87, and (3.24), p. 66 (the simple model: no growth, constant
expected return), under ANY information nested in the agents': a.e.
`Δ^Iπ_{t+1} − Δ^Irⁿ_{t+1} = −∑ρʲΔ^I s̃_{t+1+j} + Δ^I_{t+1} v_t`. -/
theorem simple_model_any {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖)
    {ρ : ℝ} (hρ : |ρ| < 1) {v r rn infl s : ℕ → Ω → ℝ} (hflow : Flow ρ v r (fun _ => 0) s)
    (hr : ∀ t, r t = rn t - infl t) {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    {M Ks Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (coarsen S 𝓖).innov t (infl (t + 1)) ω - (coarsen S 𝓖).innov t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * (coarsen S 𝓖).innov t (s (t + 1 + j)) ω +
        (coarsen S 𝓖).innov t (v t) ω := by
  have hg0 : (coarsen S 𝓖).innov t 0 = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov, (coarsen S 𝓖).E_zero,
      (coarsen S 𝓖).E_zero, sub_self]
  filter_upwards [unexpected_inflation_any (coarsen S 𝓖) hρ hflow hr (Kg := 0) hv hsm hs
    (fun _ => aestronglyMeasurable_const) (fun _ => Eventually.of_forall fun _ => by simp)
    hrm hrb hrn t, ae_all_iff.2 (innov_return_condDown h hc t)] with ω h1 h2
  rw [h1]
  have e1 : ∑' j, ρ ^ j * (coarsen S 𝓖).innov t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω = 0 := by
    simp [hg0]
  have e2 : ∑' j, ρ ^ (j + 1) * (coarsen S 𝓖).innov t (r (t + 2 + j)) ω = 0 := by
    simp only [h2, Pi.zero_apply, mul_zero, tsum_zero]
  rw [e1, e2]
  ring

/-- Cochrane (2023), eq. (4.2), p. 87 (`Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j}`), for the agents: in the
simple model with one-period debt (`rⁿ_{t+1}` known at `t`) and `v_t` known at `t`, a.e. the
discounted surplus news sums to minus unexpected inflation. -/
theorem simple_model_agents (S : MeasExpectationSystem Ω) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl s : ℕ → Ω → ℝ} (hflow : Flow ρ v r (fun _ => 0) s)
    (hr : ∀ t, r t = rn t - infl t) {c : ℝ} (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    (hvm : StronglyAdapted S.𝓕 v) (hrnm : ∀ t, StronglyMeasurable[S.𝓕 t] (rn (t + 1)))
    {M Ks Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.innov t (s (t + 1 + j)) ω)
      (-S.innov t (infl (t + 1)) ω) := by
  have hN : Nested S S.𝓕 := fun _ => le_rfl
  have hvi : Integrable (v t) S.μ := MeasExpectationSystem.BddRV.integrable (S := S)
    ⟨((hvm t).mono (S.𝓕.le t)).aestronglyMeasurable, M, hv t⟩
  have hk : S.innov t (v t) =ᵐ[S.μ] 0 :=
    innov_coarsen_of_known S S.𝓕 hvi ⟨v t, hvm t, ae_eq_refl _⟩
  have hkr : S.innov t (rn (t + 1)) =ᵐ[S.μ] 0 :=
    innov_coarsen_of_known S S.𝓕 (hrn (t + 1)) ⟨rn (t + 1), hrnm t, ae_eq_refl _⟩
  filter_upwards [simple_model_any hN hρ hflow hr hc hv hsm hs hrm hrb hrn t, hk, hkr,
    summable_innov S hρ hs t (t + 1)] with ω h1 h2 h3 h4
  change S.innov t (infl (t + 1)) ω - S.innov t (rn (t + 1)) ω =
    -∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω + S.innov t (v t) ω at h1
  rw [h2, h3, Pi.zero_apply] at h1
  have : -S.innov t (infl (t + 1)) ω = ∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω := by linarith
  rw [this]
  exact h4.hasSum

/-- Cochrane (2023), eq. (4.2), p. 87, p. 101 and Online Appendix p. 602, for the econometrician:
in the simple model, the book's decomposition with the econometrician's news,
`Δ^I π_{t+1} − Δ^I rⁿ_{t+1} = −∑ρʲΔ^I s̃_{t+1+j}`, holds a.e. **iff** `Δ^I_{t+1} v_t = 0` a.e.;
in particular it holds when `v_t ∈ I_t` (`innov_coarsen_of_known`). -/
theorem simple_model_econ_iff {S : MeasExpectationSystem Ω} {𝓖 : Filtration ℕ mΩ}
    (h : Nested S 𝓖) {ρ : ℝ} (hρ : |ρ| < 1) {v r rn infl s : ℕ → Ω → ℝ}
    (hflow : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t) {c : ℝ}
    (hc : ∀ t, S.E t (r (t + 1)) =ᵐ[S.μ] fun _ => c)
    {M Ks Kr : ℝ} (hv : ∀ t, ∀ᵐ ω ∂S.μ, |v t ω| ≤ M)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Ks)
    (hrm : ∀ t, AEStronglyMeasurable (r t) S.μ) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr)
    (hrn : ∀ t, Integrable (rn t) S.μ) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (coarsen S 𝓖).innov t (s (t + 1 + j)) ω)
      (-((coarsen S 𝓖).innov t (infl (t + 1)) ω - (coarsen S 𝓖).innov t (rn (t + 1)) ω))) ↔
      (coarsen S 𝓖).innov t (v t) =ᵐ[S.μ] 0 := by
  have hid := simple_model_any h hρ hflow hr hc hv hsm hs hrm hrb hrn t
  have hsum := summable_innov (coarsen S 𝓖) hρ hs t (t + 1)
  constructor
  · intro h1
    filter_upwards [h1, hid, hsum] with ω a b c
    rw [a.tsum_eq] at b
    rw [Pi.zero_apply]
    linarith
  · intro h1
    filter_upwards [h1, hid, hsum] with ω a b c
    rw [Pi.zero_apply] at a
    rw [b, a]
    simpa using c.hasSum

/-! ### Correction: the econometrician's decomposition fails when `v_t ∉ I_t` -/

/-- Cochrane (2023), p. 102 and Online Appendix p. 602 ("people have more information than we
do"): the econometrician sees the agents' information with a one-period lag, `𝓖_t = 𝓕_{t−1}`
(`𝓖_0 = 𝓕_0`). -/
def lagFiltration (S : MeasExpectationSystem Ω) : Filtration ℕ mΩ where
  seq t := S.𝓕 (t - 1)
  mono' _ _ h := S.𝓕.mono (Nat.sub_le_sub_right h 1)
  le' t := S.𝓕.le (t - 1)

/-- Cochrane (2023), p. 101: the lagged information is nested in the agents'. -/
theorem nested_lag (S : MeasExpectationSystem Ω) : Nested S (lagFiltration S) :=
  fun t => S.𝓕.mono (Nat.sub_le t 1)

namespace Example

open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID

/-- Cochrane (2023), p. 88 (the MA(1) surplus): `s̃_t = ε_t + θε_{t−1}`. -/
def exS (θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => ω t + θ * ω (t - 1)

/-- Cochrane (2023), p. 102 (`v_t = θε_t` for the MA(1)): the value of debt. -/
def exV (θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => θ * ω t

/-- Cochrane (2023), eq. (4.2), p. 87: the real return `r_t = a(ρ)ε_t`, `a(ρ) = 1 + ρθ`. -/
def exR (ρ θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => (1 + ρ * θ) * ω t

/-- Cochrane (2023), eq. (4.2), p. 87: inflation `π_t = −a(ρ)ε_t` (zero nominal rate). -/
def exInfl (ρ θ : ℝ) : ℕ → (ℕ → ℝ) → ℝ := fun t ω => -((1 + ρ * θ) * ω t)

/-- Cochrane (2023), §4.2, p. 87: the nominal return (one-period debt, `i = 0`). -/
def exRn : ℕ → (ℕ → ℝ) → ℝ := fun _ _ => 0

/-- Cochrane (2023), eq. (3.17), p. 63: the MA(1) example satisfies the flow identity ex post. -/
theorem ex_flow (ρ θ : ℝ) : Flow ρ (exV θ) (exR ρ θ) (fun _ => 0) (exS θ) := by
  intro t
  funext ω
  simp only [exV, exR, exS, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
    smul_eq_mul, Nat.add_sub_cancel]
  ring

/-- Cochrane (2023), §4.2, p. 87: `r = rⁿ − π` in the example. -/
theorem ex_fisher (ρ θ : ℝ) (t : ℕ) : exR ρ θ t = exRn t - exInfl ρ θ t := by
  funext ω
  simp only [exR, exRn, exInfl, Pi.sub_apply]
  ring

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), p. 102, and Online Appendix p. 602 (correction): with i.i.d. shocks (law `ν`,
mean `0`, variance `σ² > 0`, bounded), the MA(1) surplus `s̃_t = ε_t + θε_{t−1}` (`θ ≠ 0`) and a
lagged econometrician, the agents' decomposition `Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j}` holds at every date,
but the econometrician's version with his own news fails at `t = 1`: his news about `v_1 = θε_1`
is `θε_1 ≠ 0`. So the unexpected-inflation decomposition does NOT condition down in general; the
corrected statement is `simple_model_any` / `simple_model_econ_iff`. -/
theorem econ_decomp_counterexample {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {ρ θ : ℝ} (hρ : |ρ| < 1) (hθ : θ ≠ 0) :
    Flow ρ (exV θ) (exR ρ θ) (fun _ => 0) (exS θ) ∧
    Nested (iidSystem ν) (lagFiltration (iidSystem ν)) ∧
    (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, HasSum
      (fun j => ρ ^ j * (iidSystem ν).innov t (exS θ (t + 1 + j)) ω)
      (-(iidSystem ν).innov t (exInfl ρ θ (t + 1)) ω)) ∧
    ¬ (∀ᵐ ω ∂(iidSystem ν).μ, HasSum
      (fun j => ρ ^ j * (coarsen (iidSystem ν) (lagFiltration (iidSystem ν))).innov 1
        (exS θ (1 + 1 + j)) ω)
      (-((coarsen (iidSystem ν) (lagFiltration (iidSystem ν))).innov 1 (exInfl ρ θ (1 + 1)) ω -
        (coarsen (iidSystem ν) (lagFiltration (iidSystem ν))).innov 1 (exRn (1 + 1)) ω))) := by
  set S := iidSystem ν
  have hB := shock_ae_bdd ν hbdd
  have hc : ∀ t, S.E t (exR ρ θ (t + 1)) =ᵐ[S.μ] fun _ => (0 : ℝ) := fun t => by
    have e : exR ρ θ (t + 1) = (1 + ρ * θ) • shock (t + 1) := rfl
    filter_upwards [e ▸ S.E_smul (1 + ρ * θ) (shock (t + 1)) t, E_shock_zero hmean t]
      with ω a b
    rw [a, Pi.smul_apply, b, Pi.zero_apply, smul_zero]
  have hvm : StronglyAdapted S.𝓕 (exV θ) := fun t =>
    ((measurable_shock ν le_rfl).const_mul θ).stronglyMeasurable
  have hv : ∀ t, ∀ᵐ ω ∂S.μ, |exV θ t ω| ≤ |θ| * B := fun t => by
    filter_upwards [hB t] with ω h
    simp only [exV, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg θ)
  have hsm : ∀ t, AEStronglyMeasurable (exS θ t) S.μ := fun t =>
    Measurable.aestronglyMeasurable (by unfold exS; fun_prop)
  have hs : ∀ t, ∀ᵐ ω ∂S.μ, |exS θ t ω| ≤ B + |θ| * B := fun t => by
    filter_upwards [hB t, hB (t - 1)] with ω h1 h2
    simp only [exS]
    calc |ω t + θ * ω (t - 1)| ≤ |ω t| + |θ * ω (t - 1)| := abs_add_le _ _
      _ ≤ B + |θ| * B := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg θ))
  have hrm : ∀ t, AEStronglyMeasurable (exR ρ θ t) S.μ := fun t =>
    ((measurable_pi_apply t).const_mul _).aestronglyMeasurable
  have hrb : ∀ t, ∀ᵐ ω ∂S.μ, |exR ρ θ t ω| ≤ |1 + ρ * θ| * B := fun t => by
    filter_upwards [hB t] with ω h
    simp only [exR, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hrn : ∀ t, Integrable (exRn t) S.μ := fun _ => integrable_const 0
  refine ⟨ex_flow ρ θ, nested_lag S, fun t => ?_, ?_⟩
  · exact simple_model_agents S hρ (ex_flow ρ θ) (ex_fisher ρ θ) hc hvm
      (fun _ => stronglyMeasurable_const) hv hsm hs hrm hrb hrn t
  · rw [simple_model_econ_iff (nested_lag S) hρ (ex_flow ρ θ) (ex_fisher ρ θ) hc hv hsm hs
      hrm hrb hrn 1]
    intro h0
    have hvi : Integrable (exV θ 1) S.μ := MeasExpectationSystem.BddRV.integrable (S := S)
      ⟨(hvm 1).mono (S.𝓕.le 1) |>.aestronglyMeasurable, _, hv 1⟩
    have h2 : (coarsen S (lagFiltration S)).E (1 + 1) (exV θ 1) = exV θ 1 :=
      S.E_of_stronglyMeasurable (hvm 1) hvi
    have h1 : (coarsen S (lagFiltration S)).E 1 (exV θ 1) =ᵐ[S.μ] 0 := by
      have e : exV θ 1 = θ • shock (0 + 1) := rfl
      change S.E 0 (exV θ 1) =ᵐ[S.μ] 0
      filter_upwards [e ▸ S.E_smul θ (shock (0 + 1)) 0, E_shock_zero hmean 0] with ω a b
      rw [a, Pi.smul_apply, b, Pi.zero_apply, smul_zero]
    have hz : ∀ᵐ ω ∂S.μ, ω 1 ^ 2 = 0 := by
      filter_upwards [h0, h1] with ω a b
      rw [ExpectationsMeasure.MeasExpectationSystem.innov, Pi.sub_apply, h2, b] at a
      simp only [exV, Pi.zero_apply, sub_zero, mul_eq_zero] at a
      rcases a with a | a
      · exact absurd a hθ
      · rw [a]; ring
    have hint := integral_shock_fun ν 1 (f := fun x => x ^ 2) (measurable_id.pow_const 2)
    rw [integral_congr_ae hz, integral_zero, hvar] at hint
    linarith

end Example

/-! ### Links: the finite Mathlib instance and the abstract nested systems -/

/-- Cochrane (2023), p. 101: on a finite state space with full support, the econometrician's
system (bridged to the core) is exactly `ConditioningDown.CondExp.condExpSystem` for `𝓖`. -/
theorem coarsen_toExpectationSystem_E [Finite Ω] [DiscreteMeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) (𝓖 : Filtration ℕ mΩ) (hfull : ∀ ω, S.μ {ω} ≠ 0) (t : ℕ)
    (x : Ω → ℝ) :
    ((coarsen S 𝓖).toExpectationSystem hfull).E t x =
      (ConditioningDown.CondExp.condExpSystem S.μ hfull 𝓖 𝓖.le (fun _ _ h => 𝓖.mono h)).E t x :=
  rfl

/-- Cochrane (2023), p. 101: on a finite state space with full support, a nested pair of
measure-theoretic systems is a coarser pair of core systems in the abstract sense of
`ConditioningDown.Coarser`. -/
theorem coarser_core [Finite Ω] [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω}
    {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖) (hfull : ∀ ω, S.μ {ω} ≠ 0) :
    ConditioningDown.Coarser ((coarsen S 𝓖).toExpectationSystem hfull)
      (S.toExpectationSystem hfull) :=
  fun _ x => S.eq_of_ae_eq hfull (E_coarsen_tower h le_rfl x)

/-- Cochrane (2023), p. 101, and Online Appendix (2.22)–(2.23), p. 602: on a finite state space
with full support, the general measure-theoretic `condDown_iff` and the abstract
`ConditioningDown.condDown_iff` for nested systems are the same statement: each side of the
general one is the corresponding side of the abstract one. -/
theorem condDown_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω}
    {𝓖 : Filtration ℕ mΩ} (h : Nested S 𝓖) (hfull : ∀ ω, S.μ {ω} ≠ 0) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = S.E t X) :
    (v =ᵐ[S.μ] (coarsen S 𝓖).E t X ↔ v = ((coarsen S 𝓖).toExpectationSystem hfull).E t X) ∧
    (KnownAE S.μ 𝓖 t v ↔ ((coarsen S 𝓖).toExpectationSystem hfull).E t v = v) ∧
    (v = ((coarsen S 𝓖).toExpectationSystem hfull).E t X ↔
      ((coarsen S 𝓖).toExpectationSystem hfull).E t v = v) := by
  refine ⟨⟨fun h1 => S.eq_of_ae_eq hfull h1, fun h1 => h1 ▸ ae_eq_refl _⟩, ?_,
    ConditioningDown.condDown_iff (coarser_core h hfull) hv⟩
  rw [← known_iff_E_eq S 𝓖 Integrable.of_finite]
  exact ⟨fun h1 => (S.eq_of_ae_eq hfull h1).symm,
    fun h1 => Eventually.of_forall fun ω => (congrFun h1 ω).symm⟩

/-- Cochrane (2023), Ch. 2, p. 29 (tool): when every state has positive probability, an a.e.
statement holds at every state. -/
theorem forall_of_ae [Finite Ω] {S : MeasExpectationSystem Ω} (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {p : Ω → Prop} (h : ∀ᵐ ω ∂S.μ, p ω) (ω : Ω) : p ω := by
  by_contra hω
  exact hfull ω (measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hω)
    (ae_iff.mp h))

/-- Cochrane (2023), eq. (3.20), p. 65: on a finite state space with full support, the core
innovation operator of the bridged system is the measure-theoretic news `E_{t+1} − E_t`. -/
theorem core_innov_eq [Finite Ω] [DiscreteMeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    (hfull : ∀ ω, S.μ {ω} ≠ 0) (t : ℕ) (x : Ω → ℝ) :
    Innovations.innov (S.toExpectationSystem hfull) t x = S.innov t x := rfl

/-- Cochrane (2023), eq. (3.20), p. 65, link to the core: on a finite state space with full
support, `unexpected_inflation_agents` specialises to the core statement
(`LinearizedIdentities.unexpected_inflation_identity_tsum`'s conclusion) for the bridged
`ExpectationSystem`, at every state. -/
theorem unexpected_inflation_core [Finite Ω] [DiscreteMeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) (hfull : ∀ ω, S.μ {ω} ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1)
    {v r rn infl g s : ℕ → Ω → ℝ} (hflow : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hvm : StronglyAdapted S.𝓕 v) {M Ks Kg Kr : ℝ} (hv : ∀ t ω, |v t ω| ≤ M)
    (hs : ∀ t ω, |s t ω| ≤ Ks) (hg : ∀ t ω, |g t ω| ≤ Kg) (hrb : ∀ t ω, |r t ω| ≤ Kr) (t : ℕ)
    (ω : Ω) :
    Innovations.innov (S.toExpectationSystem hfull) t (infl (t + 1)) ω -
      Innovations.innov (S.toExpectationSystem hfull) t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * Innovations.innov (S.toExpectationSystem hfull) t (s (t + 1 + j)) ω -
        ∑' j, ρ ^ j * Innovations.innov (S.toExpectationSystem hfull) t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * Innovations.innov (S.toExpectationSystem hfull) t
          (r (t + 2 + j)) ω := by
  have hm : ∀ x : Ω → ℝ, AEStronglyMeasurable x S.μ := fun x =>
    (Measurable.of_discrete (f := x)).aestronglyMeasurable
  have hA := unexpected_inflation_any S hρ hflow hr (M := M)
    (fun t => Eventually.of_forall (hv t)) (fun t => hm _) (fun t => Eventually.of_forall (hs t))
    (fun t => hm _) (fun t => Eventually.of_forall (hg t)) (fun t => hm _)
    (fun t => Eventually.of_forall (hrb t)) (fun _ => Integrable.of_finite) t
  have hvi : Integrable (v t) S.μ := Integrable.of_finite
  have h0 : S.innov t (v t) = 0 := by
    rw [ExpectationsMeasure.MeasExpectationSystem.innov,
      S.E_of_stronglyMeasurable ((hvm t).mono (S.𝓕.mono (Nat.le_succ t))) hvi,
      S.E_of_stronglyMeasurable (hvm t) hvi, sub_self]
  have hB := forall_of_ae hfull hA ω
  rw [h0, Pi.zero_apply, add_zero] at hB
  exact hB

end Cochrane.DebtDeficitsInflation.ConditioningDownMeasure
