/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.VARIdentities
import DebtDeficitsInflation.ExpectationsFiniteTree
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditioning down: people have more information than the VAR

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, pp. 101–102 and p. 108,
and Online Appendix Chapter 2, §2.1.7, eqs. (2.22)–(2.23), pp. 602–603.

The valuation equation holds with people's information `Ω_t`,
`v_t = E(∑ ρʲ s̃_{t+1+j} | Ω_t)`. Taking expectations conditional on a smaller information set
`I_t ⊂ Ω_t` (the VAR's) gives `v_t = E(∑ ρʲ s̃_{t+1+j} | I_t)` *if and only if* `v_t ∈ I_t`;
otherwise the left-hand side is `E(v_t | I_t)`.

Two information sets cannot be expressed by a single `ExpectationSystem`; the minimal structure is
a pair of systems with the *coarser* property `E^I_t E^Ω_t = E^I_t` (the tower property across
information sets).

## Main definitions

* `Coarser 𝔼I 𝔼Ω`: `𝔼I` conditions on less information than `𝔼Ω`.
* `fullInfo Ω`: the system in which every random variable is known (`E_t = id`).
* `condExpSystem μ ℱ`: the Mathlib conditional expectation `μ[· | ℱ t]` on a finite probability
  space with full support, as an `ExpectationSystem`.

## Main results

* `condDown_general`: `E^I_t(PV) = E^I_t v_t` always; `condDown`: `v_t = E^I_t(PV)` when
  `v_t ∈ I_t`; `condDown_iff`: and only then.
* `condDown_series`, `condDown_pathwise`: the same for the genuine present-value series of a
  bounded surplus, `0 ≤ ρ < 1`.
* `r_squared_one`: if people use only the VAR information (`I = Ω`), `v_t` is an exact function of
  the VAR information (100% R², p. 102); `info_larger_of_not_known`: so a `v_t` that is not
  known given the VAR information refutes `I = Ω`.
* `condDown_fails_example`: with `v_t ∉ I_t` conditioning down genuinely fails (coin-flip tree).
* `condExpSystem`, `condExpSystem_coarser`, `condExpSystem_known_iff`, `condDown_condExp_iff`:
  the measure-theoretic instance — for nested filtrations `ℱI ≤ ℱΩ`, `μ[X|ℱI_t] = v_t` for
  `v_t = μ[X|ℱΩ_t]` iff `v_t` is `ℱI_t`-measurable.
-/

namespace Cochrane.DebtDeficitsInflation.ConditioningDown

open MeasureTheory Filter Topology

variable {Ω : Type*}

/-! ### Coarser expectation systems -/

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): the system `𝔼I` conditions on less information than
`𝔼Ω` — the tower property across information sets, `E(E(x|Ω_t)|I_t) = E(x|I_t)`. -/
def Coarser (𝔼I 𝔼Ω : ExpectationSystem Ω) : Prop := ∀ t x, 𝔼I.E t (𝔼Ω.E t x) = 𝔼I.E t x

/-- Cochrane (2023), p. 101: every system is coarser than itself. -/
theorem coarser_refl (𝔼 : ExpectationSystem Ω) : Coarser 𝔼 𝔼 := fun t x => 𝔼.E_E_self t x

/-- Cochrane (2023), p. 101: coarsening is transitive. -/
theorem coarser_trans {𝔼1 𝔼2 𝔼3 : ExpectationSystem Ω} (h12 : Coarser 𝔼1 𝔼2)
    (h23 : Coarser 𝔼2 𝔼3) : Coarser 𝔼1 𝔼3 := by
  intro t x
  rw [← h12 t (𝔼3.E t x), h23 t x, h12 t x]

/-- Cochrane (2023), Online Appendix p. 602 ("people have more information than we do"): the
full-information system, in which every random variable is known at every date (`E_t = id`). -/
def fullInfo (Ω : Type*) : ExpectationSystem Ω where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- Cochrane (2023), Online Appendix p. 602: every system is coarser than full information. -/
theorem coarser_fullInfo (𝔼 : ExpectationSystem Ω) : Coarser 𝔼 (fullInfo Ω) :=
  fun _ _ => rfl

/-! ### Conditioning down -/

/-- Cochrane (2023), p. 101 ("if not, the left-hand side should be `E(v_t|I_t)`"): if
`v_t = E(X | Ω_t)` and `I_t ⊂ Ω_t`, then `E(X | I_t) = E(v_t | I_t)` always. -/
theorem condDown_general {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {t : ℕ}
    {v X : Ω → ℝ} (hv : v = 𝔼Ω.E t X) : 𝔼I.E t X = 𝔼I.E t v := by
  rw [hv, hc t X]

/-- Cochrane (2023), p. 101, and Online Appendix eqs. (2.22)–(2.23), p. 602: conditioning down is
valid when `v_t ∈ I_t` (`E(v_t|I_t) = v_t`): then `v_t = E(X | I_t)`. -/
theorem condDown {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) (hvI : 𝔼I.E t v = v) : v = 𝔼I.E t X := by
  rw [condDown_general hc hv, hvI]

/-- Cochrane (2023), p. 101 ("this conditioning down is valid, so long as `v_t ∈ I_t`") and
Online Appendix p. 602 ("only if we include the value of debt in the VAR"): given
`v_t = E(X | Ω_t)`, the conditioned-down relation `v_t = E(X | I_t)` holds if and only if
`v_t` is known given `I_t`. -/
theorem condDown_iff {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) : v = 𝔼I.E t X ↔ 𝔼I.E t v = v := by
  constructor
  · intro h
    rw [h, 𝔼I.E_E_self]
  · exact condDown hc hv

/-- Cochrane (2023), p. 101, with the present value as a sum of forecasts: if `s̃` is bounded,
`0 ≤ ρ < 1`, `v_t = ∑ ρʲ E(s̃_{t+1+j} | Ω_t)` and `v_t ∈ I_t`, then
`v_t = ∑ ρʲ E(s̃_{t+1+j} | I_t)` — the VAR forecasts discount to the value of debt. -/
theorem condDown_series {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {ρ M : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) {t : ℕ}
    {v : Ω → ℝ} (hv : v = fun ω => ∑' j, ρ ^ j * 𝔼Ω.E t (s (t + 1 + j)) ω)
    (hvI : 𝔼I.E t v = v) : v = fun ω => ∑' j, ρ ^ j * 𝔼I.E t (s (t + 1 + j)) ω := by
  have hf : ∀ k ω, |(ρ ^ k • 𝔼Ω.E t (s (t + 1 + k))) ω| ≤ ρ ^ k * M := by
    intro k ω
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼Ω.abs_E_le (hs (t + 1 + k)) t ω) (pow_nonneg hρ0 k)
  funext ω
  have h := 𝔼I.E_tsum hρ0 hρ1 hf t ω
  have hv' : v = fun ω' => ∑' k, (ρ ^ k • 𝔼Ω.E t (s (t + 1 + k))) ω' := by
    rw [hv]; rfl
  rw [← hvI, hv', h]
  refine tsum_congr fun k => ?_
  rw [map_smul, hc t, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), p. 101, with the ex-post present value `X = ∑ ρʲ s̃_{t+1+j}` (pathwise, for
bounded `s̃` and `0 ≤ ρ < 1`): if `v_t = E(X|Ω_t)` and `v_t ∈ I_t`, then
`v_t = E(X|I_t) = ∑ ρʲ E(s̃_{t+1+j}|I_t)`. -/
theorem condDown_pathwise {𝔼I 𝔼Ω : ExpectationSystem Ω} (hc : Coarser 𝔼I 𝔼Ω) {ρ M : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) {t : ℕ}
    {v : Ω → ℝ} (hv : v = 𝔼Ω.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω))
    (hvI : 𝔼I.E t v = v) :
    v = 𝔼I.E t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω) ∧
    v = fun ω => ∑' j, ρ ^ j * 𝔼I.E t (s (t + 1 + j)) ω := by
  refine ⟨condDown hc hv hvI, ?_⟩
  have hf : ∀ k ω, |(ρ ^ k • s (t + 1 + k)) ω| ≤ ρ ^ k * M := by
    intro k ω
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
    exact mul_le_mul_of_nonneg_left (hs (t + 1 + k) ω) (pow_nonneg hρ0 k)
  funext ω
  have h := 𝔼I.E_tsum hρ0 hρ1 hf t ω
  rw [condDown hc hv hvI]
  change 𝔼I.E t (fun ω' => ∑' k, (ρ ^ k • s (t + 1 + k)) ω') ω = _
  rw [h]
  refine tsum_congr fun k => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), p. 102 ("the only way to rescue such a calculation is to assume that people
use exactly the same information … `I_t = Ω_t`. … But in that case, `v_t` would be an exact
function of the observed information, with 100% R²"): if `𝔼I = 𝔼Ω` and `v_t = E(X | Ω_t)`, then
`v_t` is known given the VAR information and the forecast residual `v_t − E(v_t|I_t)` is zero. -/
theorem r_squared_one {𝔼I 𝔼Ω : ExpectationSystem Ω} (hsame : 𝔼I = 𝔼Ω) {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) : 𝔼I.E t v = v ∧ v - 𝔼I.E t v = 0 := by
  subst hsame
  have h : 𝔼I.E t v = v := by rw [hv, 𝔼I.E_E_self]
  exact ⟨h, by rw [h, sub_self]⟩

/-- Cochrane (2023), p. 102 ("it is a testable implicit assumption, and it fails"): if the value
of debt is not an exact function of the VAR information, people's information is strictly
larger, `𝔼I ≠ 𝔼Ω`. -/
theorem info_larger_of_not_known {𝔼I 𝔼Ω : ExpectationSystem Ω} {t : ℕ} {v X : Ω → ℝ}
    (hv : v = 𝔼Ω.E t X) (hnot : 𝔼I.E t v ≠ v) : 𝔼I ≠ 𝔼Ω :=
  fun h => hnot (r_squared_one h hv).1

/-- Cochrane (2023), p. 101 and Online Appendix p. 602 ("leaving `v_t` out of the VAR, the
present value relation … does not imply the relation one tests with the VAR"): an explicit
failure. In the two-coin-flip tree, people see everything (`fullInfo`), the econometrician only
the date-0 information (the coin-flip system); with `v_0 = X =` heads on the first flip,
`v_0 = E(X|Ω_0)` but `E(X|I_0) = 1/2 ≠ v_0`. -/
theorem condDown_fails_example :
    Coarser ExpectationsFiniteTree.coinSystem (fullInfo (Bool × Bool)) ∧
    ExpectationsFiniteTree.firstHeads =
      (fullInfo (Bool × Bool)).E 0 ExpectationsFiniteTree.firstHeads ∧
    ExpectationsFiniteTree.firstHeads ≠
      ExpectationsFiniteTree.coinSystem.E 0 ExpectationsFiniteTree.firstHeads := by
  refine ⟨coarser_fullInfo _, rfl, fun h => ?_⟩
  have := congrFun h (true, true)
  rw [ExpectationsFiniteTree.coinSystem_E0_firstHeads] at this
  norm_num [ExpectationsFiniteTree.firstHeads] at this

/-! ### The measure-theoretic instance (Mathlib `condExp`) -/

namespace CondExp

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]

omit [MeasurableSingletonClass Ω] [Finite Ω] in
/-- Cochrane (2023), p. 101 (tool): on a space where every point has positive mass, almost-sure
equality is equality. -/
theorem eq_of_ae_eq {μ : Measure Ω} (hμ : ∀ ω, μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    f = g := by
  funext ω
  by_contra hne
  have h0 : μ {x | ¬ f x = g x} = 0 := ae_iff.mp h
  exact hμ ω (measure_mono_null (Set.singleton_subset_iff.mpr hne) h0)

omit [MeasurableSingletonClass Ω] [Finite Ω] in
/-- Cochrane (2023), p. 101 (tool): on a space where every point has positive mass, an almost-sure
inequality holds everywhere. -/
theorem le_of_ae_le {μ : Measure Ω} (hμ : ∀ ω, μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f ≤ᵐ[μ] g) :
    f ≤ g := by
  intro ω
  by_contra hne
  have h0 : μ {x | ¬ f x ≤ g x} = 0 := ae_iff.mp h
  exact hμ ω (measure_mono_null (Set.singleton_subset_iff.mpr hne) h0)

/-- Cochrane (2023), p. 101 (`E(·|Ω_t)` and `E(·|I_t)`): the Mathlib conditional expectation
`μ[· | ℱ t]` with respect to a filtration `ℱ` on a finite probability space whose points all have
positive mass, as an `ExpectationSystem`. -/
noncomputable def condExpSystem (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱ : ℕ → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ ‹MeasurableSpace Ω›) (hmono : Monotone ℱ) :
    ExpectationSystem Ω where
  E t :=
    { toFun := fun x => μ[x | ℱ t]
      map_add' := fun _ _ => eq_of_ae_eq hμ (condExp_add Integrable.of_finite
        Integrable.of_finite _)
      map_smul' := fun c x => eq_of_ae_eq hμ (condExp_smul c x _) }
  const t c := condExp_const (hℱ t) c
  mono _ {_ _} h := le_of_ae_le hμ (condExp_mono Integrable.of_finite Integrable.of_finite
    (ae_of_all _ h))
  tower {_ t} hst _ := eq_of_ae_eq hμ (condExp_condExp_of_le (hmono hst) (hℱ t))
  known {_ t} hst _ := condExp_of_stronglyMeasurable (hℱ t)
    (stronglyMeasurable_condExp.mono (hmono hst)) Integrable.of_finite

/-- Cochrane (2023), p. 101: the operators of `condExpSystem` are the Mathlib conditional
expectations. -/
theorem condExpSystem_E (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱ : ℕ → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ ‹MeasurableSpace Ω›) (hmono : Monotone ℱ)
    (t : ℕ) (x : Ω → ℝ) : (condExpSystem μ hμ ℱ hℱ hmono).E t x = μ[x | ℱ t] := rfl

/-- Cochrane (2023), p. 101 (`I_t ⊂ Ω_t`): for nested filtrations `ℱI_t ≤ ℱΩ_t`, the
conditional-expectation system of `ℱI` is coarser than that of `ℱΩ` (the tower property). -/
theorem condExpSystem_coarser (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱI ℱΩ : ℕ → MeasurableSpace Ω) (hI : ∀ t, ℱI t ≤ ‹MeasurableSpace Ω›)
    (hΩ : ∀ t, ℱΩ t ≤ ‹MeasurableSpace Ω›) (hmI : Monotone ℱI) (hmΩ : Monotone ℱΩ)
    (hle : ∀ t, ℱI t ≤ ℱΩ t) :
    Coarser (condExpSystem μ hμ ℱI hI hmI) (condExpSystem μ hμ ℱΩ hΩ hmΩ) := by
  intro t x
  exact eq_of_ae_eq hμ (condExp_condExp_of_le (hle t) (hΩ t))

/-- Cochrane (2023), p. 101 ("`v_t ∈ I_t`"): in the conditional-expectation system, `E_t v = v`
exactly when `v` is `ℱ_t`-measurable. -/
theorem condExpSystem_known_iff (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱ : ℕ → MeasurableSpace Ω) (hℱ : ∀ t, ℱ t ≤ ‹MeasurableSpace Ω›) (hmono : Monotone ℱ)
    (t : ℕ) (v : Ω → ℝ) :
    (condExpSystem μ hμ ℱ hℱ hmono).E t v = v ↔ StronglyMeasurable[ℱ t] v := by
  rw [condExpSystem_E]
  constructor
  · intro h
    rw [← h]
    exact stronglyMeasurable_condExp
  · intro h
    exact condExp_of_stronglyMeasurable (hℱ t) h Integrable.of_finite

/-- Cochrane (2023), p. 101, and Online Appendix eqs. (2.22)–(2.23), p. 602, in measure-theoretic
form: for nested filtrations `ℱI ≤ ℱΩ` (VAR information inside people's information) and
`v_t = E(X | ℱΩ_t)`, the conditioned-down relation `v_t = E(X | ℱI_t)` holds if and only if `v_t`
is `ℱI_t`-measurable — "so long as we include `v_t` in the VAR". -/
theorem condDown_condExp_iff (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : ∀ ω, μ {ω} ≠ 0)
    (ℱI ℱΩ : ℕ → MeasurableSpace Ω) (hI : ∀ t, ℱI t ≤ ‹MeasurableSpace Ω›)
    (hΩ : ∀ t, ℱΩ t ≤ ‹MeasurableSpace Ω›) (hmI : Monotone ℱI) (hmΩ : Monotone ℱΩ)
    (hle : ∀ t, ℱI t ≤ ℱΩ t) (t : ℕ) {v X : Ω → ℝ} (hv : v = μ[X | ℱΩ t]) :
    v = μ[X | ℱI t] ↔ StronglyMeasurable[ℱI t] v := by
  have h := condDown_iff (condExpSystem_coarser μ hμ ℱI ℱΩ hI hΩ hmI hmΩ hle) (t := t) (X := X)
    (v := v) hv
  rw [← condExpSystem_known_iff μ hμ ℱI hI hmI]
  exact h

end CondExp

end Cochrane.DebtDeficitsInflation.ConditioningDown
