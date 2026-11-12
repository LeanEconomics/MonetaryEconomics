/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR5UnitRootMeasure
import ObservationalEquivalence.TidyR5UnitRootCompact

/-!
# The Leeper model on a probability space: region (d) and the boundary `|φ| = 1`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, eqs. (22.3)–(22.6),
p. 500, and §22.7, pp. 508–509; Chapter 23, eqs. (23.1)–(23.4), p. 512.

The unstarred Leeper model `i_t = E_t π_{t+1}`, `i_t = φπ_t + u_{i,t}`,
`s̃_{t+1} = γ v_t + u_{s,t+1}` (`s̃_0 = u_{s,0}`), `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` and
`ρ v_0 + π_0 = K`, stated on any probability space with any filtration (`MeasExpectationSystem`,
Mathlib's `condExp`), every equation almost surely (`LeeperEqmM`). An equilibrium is admissible
(`AdmissibleM`) when inflation and debt are adapted, debt is integrable, inflation is essentially
bounded, and the transversality condition `ρᵀ E_t v_{t+T} → 0` holds a.s. at every date.
Disturbances are adapted and essentially bounded; the inherited debt `K` is known at date 0 and
integrable; `0 < ρ < 1` and `0 < γ < 2`.

## Main results

* `sol_of_eqmM`: every admissible equilibrium gives a bounded adapted solution of
  `E_t π_{t+1} = φπ_t + u_{i,t}` (any `φ`).
* `eqmM_of_sol`, `admissibleM_of_sol`: conversely, every bounded adapted solution, with debt from
  the flow condition (`debtM`), is an admissible equilibrium (any `φ`; the transversality condition
  holds because `|1 − γ| < 1`).
* `leeperM_exists_iff`: an admissible equilibrium exists iff the monetary equation has a bounded
  adapted solution.
* `leeperM_uncountable`: for `|φ| ≤ 1`, one bounded solution gives uncountably many admissible
  equilibria (`π_t = π̄_t + cφᵗ`).
* `leeperM_unit_iff`, `leeperM_unit_dichotomy` (**the full characterisation on every probability
  space**, `φ² = 1`): the admissible equilibria are empty or uncountable, and nonempty iff the
  conditional sums `∑_{j<T} φʲ E_t u_{i,t+j}` are essentially bounded;
  `leeperM_phi_one_iff` (`|E_t ∑_{j<T} u_{i,t+j}| ≤ C`) and `leeperM_phi_neg_one_iff`
  (`|E_t ∑_{j<T} (−1)ʲ u_{i,t+j}| ≤ C`).
* `leeperM_region_d`: region (d), `|φ| < 1`: always uncountably many admissible equilibria.

## The foundational limit of the core version

The core (abstract `ExpectationSystem`) characterisation of `TidyR5UnitRoot` and
`TidyR5UnitRootCompact` covers expectation systems in which information stops arriving
(`TidyR5UnitRoot.exists_iff_of_eventually`), disturbances known at date 0
(`TidyR5UnitRoot.exists_iff_known`), and every system with finitely supported forecasts
(`TidyR5UnitRootCompact.exists_iff_of_finSupp`), which includes every system on a countable state
space (`TidyR5UnitRootCompact.finSupp_of_countable`). In every core system the necessity half
(`TidyR5UnitRoot.condBdd_of_sol`) and the realised-sum sufficiency half
(`TidyR5UnitRoot.sol_of_pathBdd`) hold. What is not covered is a core system on an uncountable
state space whose forecasts `E_t(·)(ω)` are not finitely supported and in which information keeps
arriving. A forecast is a positive normalised linear functional on all of `ℝ^Ω`. If `Ω` carries a
countably complete nonprincipal ultrafilter `U`, which happens exactly when `|Ω|` is at least a
measurable cardinal, then `y ↦ U-lim y` is such a functional (every real function is constant on a
`U`-large set) and it is not finitely supported. Whether measurable cardinals exist is not decided
by ZFC, nor by Lean's type theory (which is equiconsistent with ZFC plus countably many
inaccessibles); their existence cannot be refuted there if they are consistent, and it cannot be
proved there if ZFC is consistent. So finite support cannot be proved for all core systems, and
the compactness argument of `TidyR5UnitRootCompact` needs it: an ultrafilter-limit forecast is not
continuous in the product topology. Every genuine probability space is covered by the theorems
of this module and `TidyR5UnitRootMeasure.exists_iff_condBddM`.
-/

namespace Cochrane.ObservationalEquivalence.TidyR5LeeperMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.LeeperRegions (mkPath)
open Cochrane.ObservationalEquivalence.TidyR5UnitRootMeasure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (22.3)–(22.6), p. 500, and (23.1)–(23.4), p. 512, on a probability space:
`x` is an equilibrium of the Leeper model when, a.s. at every date, `i_t = E_t π_{t+1}`,
`i_t = φπ_t + u_{i,t}`, `s̃_0 = u_{s,0}`, `s̃_{t+1} = γ v_t + u_{s,t+1}`,
`ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` and `ρ v_0 + π_0 = K`. -/
def LeeperEqmM (ρ φ γ : ℝ) (ui us : ℕ → Ω → ℝ) (K : Ω → ℝ) (x : Outcome Ω) : Prop :=
  (∀ t, x.i t =ᵐ[S.μ] S.E t (x.pi (t + 1))) ∧ (∀ t, x.i t =ᵐ[S.μ] φ • x.pi t + ui t) ∧
    x.s 0 =ᵐ[S.μ] us 0 ∧ (∀ t, x.s (t + 1) =ᵐ[S.μ] γ • x.v t + us (t + 1)) ∧
    (∀ t, ρ • x.v (t + 1) =ᵐ[S.μ] x.v t + x.i t - x.pi (t + 1) - x.s (t + 1)) ∧
    ρ • x.v 0 + x.pi 0 =ᵐ[S.μ] K

/-- Cochrane (2023), §22.1, p. 495, and §22.7, p. 508, on a probability space: an admissible
path — inflation and debt adapted, debt integrable, inflation essentially bounded, and the
transversality condition `ρᵀ E_t v_{t+T} → 0` a.s. at every date. -/
def AdmissibleM (ρ : ℝ) (x : Outcome Ω) : Prop :=
  StronglyAdapted S.𝓕 x.pi ∧ StronglyAdapted S.𝓕 x.v ∧ (∀ t, Integrable (x.v t) S.μ) ∧
    S.BddProc x.pi ∧
    ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => ρ ^ T * S.E t (x.v (t + T)) ω) atTop (𝓝 0)

variable {S}

/-- Cochrane (2023), (23.1)–(23.2), p. 512 (necessity, any `φ`): the inflation path of an
admissible equilibrium is a bounded adapted solution of `E_t π_{t+1} = φπ_t + u_{i,t}`. -/
theorem sol_of_eqmM {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (h : LeeperEqmM S ρ φ γ ui us K x) (ha : AdmissibleM S ρ x) : HasBddSolM S φ ui :=
  ⟨x.pi, ha.1, ha.2.2.2.1, fun t => (h.1 t).symm.trans (h.2.1 t)⟩

/-- Cochrane (2023), (23.4), p. 512: debt from the flow condition and the inherited debt,
`v_0 = (K − π_0)/ρ`, `v_{t+1} = ρ⁻¹((1 − γ)v_t + φπ_t + u_{i,t} − π_{t+1} − u_{s,t+1})`. -/
noncomputable def debtM (ρ φ γ : ℝ) (ui us : ℕ → Ω → ℝ) (K : Ω → ℝ) (π : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => ρ⁻¹ • (K - π 0)
  | t + 1 => ρ⁻¹ • ((1 - γ) • debtM ρ φ γ ui us K π t + (φ • π t + ui t - π (t + 1)) -
      us (t + 1))

/-- Cochrane (2023), (22.3)–(22.6), p. 500 (sufficiency, any `φ`): a solution of the monetary
equation, with debt from the flow condition, is an equilibrium of the Leeper model. -/
theorem eqmM_of_sol {ρ φ γ : ℝ} (hρ : ρ ≠ 0) {ui us π : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hπ : MonEqM S φ ui π) :
    LeeperEqmM S ρ φ γ ui us K (mkPath φ γ ui us π (debtM ρ φ γ ui us K π)) := by
  refine ⟨fun t => (hπ t).symm, fun t => EventuallyEq.rfl, ?_, fun t => EventuallyEq.rfl,
    fun t => EventuallyEq.of_eq ?_, EventuallyEq.of_eq ?_⟩
  · refine EventuallyEq.of_eq ?_
    change γ • (0 : Ω → ℝ) + us 0 = us 0
    rw [smul_zero, zero_add]
  · change ρ • (ρ⁻¹ • ((1 - γ) • debtM ρ φ γ ui us K π t + (φ • π t + ui t - π (t + 1)) -
      us (t + 1))) = debtM ρ φ γ ui us K π t + (φ • π t + ui t) - π (t + 1) -
        (γ • debtM ρ φ γ ui us K π t + us (t + 1))
    rw [smul_smul, mul_inv_cancel₀ hρ, one_smul, sub_smul, one_smul]
    abel
  · change ρ • (ρ⁻¹ • (K - π 0)) + π 0 = K
    rw [smul_smul, mul_inv_cancel₀ hρ, one_smul, sub_add_cancel]

/-- Cochrane (2023), (23.4), p. 512: the debt path is adapted (integrability is
`debtM_integrable`). -/
theorem debtM_meas {ρ φ γ : ℝ} {ui us π : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hπa : StronglyAdapted S.𝓕 π) (huia : StronglyAdapted S.𝓕 ui)
    (husa : StronglyAdapted S.𝓕 us) (hK : StronglyMeasurable[S.𝓕 0] K) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (debtM ρ φ γ ui us K π t) := by
  induction t with
  | zero => exact (hK.sub (hπa 0)).const_smul _
  | succ t ih =>
    have hle := S.𝓕.mono (Nat.le_succ t)
    exact ((((ih.mono hle).const_smul _).add ((((hπa t).const_smul φ).add (huia t)).mono hle
      |>.sub (hπa (t + 1)))).sub (husa (t + 1))).const_smul _

/-- Cochrane (2023), (23.4), p. 512: the debt path is integrable when inflation and the
disturbances are integrable and `K` is integrable. -/
theorem debtM_integrable {ρ φ γ : ℝ} {ui us π : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hπi : ∀ t, Integrable (π t) S.μ) (huii : ∀ t, Integrable (ui t) S.μ)
    (husi : ∀ t, Integrable (us t) S.μ) (hKi : Integrable K S.μ) (t : ℕ) :
    Integrable (debtM ρ φ γ ui us K π t) S.μ := by
  induction t with
  | zero => exact (hKi.sub (hπi 0)).smul _
  | succ t ih =>
    exact (((ih.smul _).add (((hπi t).smul φ).add (huii t) |>.sub (hπi (t + 1)))).sub
      (husi (t + 1))).smul _

/-- Cochrane (2023), p. 513 (passive fiscal policy, on a probability space): with `0 < ρ < 1`,
`|1 − γ| < 1` and essentially bounded `u_s`, debt from the flow condition satisfies the
transversality condition a.s., whatever the (bounded adapted) solution of the monetary equation. -/
theorem debtM_tvc {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : |1 - γ| < 1)
    {ui us π : ℕ → Ω → ℝ} {K : Ω → ℝ} (hπ : MonEqM S φ ui π)
    (hπi : ∀ t, Integrable (π t) S.μ) (huii : ∀ t, Integrable (ui t) S.μ)
    (husi : ∀ t, Integrable (us t) S.μ) (hKi : Integrable K S.μ)
    (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Tendsto (fun T => ρ ^ T * S.E t (debtM ρ φ γ ui us K π (t + T)) ω) atTop
      (𝓝 0) := by
  set v := debtM ρ φ γ ui us K π with hv
  have hvi : ∀ s, Integrable (v s) S.μ := debtM_integrable hπi huii husi hKi
  -- one step of the expected debt dynamics
  have hstep : ∀ T, ∀ᵐ ω ∂S.μ, ρ * S.E t (v (t + T + 1)) ω =
      (1 - γ) * S.E t (v (t + T)) ω - S.E t (us (t + T + 1)) ω := by
    intro T
    set s := t + T with hs
    have hA : Integrable (φ • π s + ui s) S.μ := ((hπi s).smul φ).add (huii s)
    have hZ : Integrable (φ • π s + ui s - π (s + 1)) S.μ := hA.sub (hπi (s + 1))
    have hB : Integrable ((1 - γ) • v s + (φ • π s + ui s - π (s + 1))) S.μ :=
      ((hvi s).smul _).add hZ
    have hC : Integrable ((1 - γ) • v s + (φ • π s + ui s - π (s + 1)) - us (s + 1)) S.μ :=
      hB.sub (husi (s + 1))
    filter_upwards [S.E_smul ρ⁻¹ ((1 - γ) • v s + (φ • π s + ui s - π (s + 1)) - us (s + 1)) t,
      S.E_sub hB (husi (s + 1)) t, S.E_add ((hvi s).smul (1 - γ)) hZ t,
      S.E_smul (1 - γ) (v s) t, S.E_sub hA (hπi (s + 1)) t,
      (S.E_tower (Nat.le_add_right t T) (π (s + 1))).symm, S.E_congr (hπ s) t] with ω
      e1 e2 e3 e4 e5 e6 e7
    have hvs : v (s + 1) = ρ⁻¹ • ((1 - γ) • v s + (φ • π s + ui s - π (s + 1)) - us (s + 1)) :=
      rfl
    rw [hvs, e1]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at e2 e3 e4 e5 ⊢
    rw [e2, e3, e4, e5, e6, e7]
    field_simp
    ring
  filter_upwards [ae_all_iff.2 hstep, ae_all_iff.2 fun T => S.abs_E_le (hus (t + T + 1)) t]
    with ω h1 h2
  refine FiscalRec.tendsto_zero_of_stable_rec (q := 1 - γ) (r := ρ) (C := |Ms|)
    (w := fun T => -(ρ ^ T * S.E t (us (t + T + 1)) ω)) hγ hρ0.le hρ1 (fun T => ?_) (fun T => ?_)
  · rw [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hρ0.le T), mul_comm]
    exact mul_le_mul_of_nonneg_right ((h2 T).trans (le_abs_self Ms)) (pow_nonneg hρ0.le T)
  · change ρ ^ (T + 1) * S.E t (v (t + T + 1)) ω = _
    rw [pow_succ, mul_assoc, h1 T]
    ring

/-- Cochrane (2023), §22.7, pp. 508–509 (sufficiency, any `φ`, on a probability space): a bounded
adapted solution of the monetary equation, with debt from the flow condition, is an admissible
equilibrium (`0 < ρ < 1`, `0 < γ < 2`, bounded adapted disturbances, `K` known at date 0 and
integrable). -/
theorem admissibleM_of_sol {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 0 < γ ∧ γ < 2)
    {ui us π : ℕ → Ω → ℝ} {K : Ω → ℝ} (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui)
    (husa : StronglyAdapted S.𝓕 us) (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms)
    (hK : StronglyMeasurable[S.𝓕 0] K) (hKi : Integrable K S.μ)
    (hπa : StronglyAdapted S.𝓕 π) (hπb : S.BddProc π) (hπ : MonEqM S φ ui π) :
    LeeperEqmM S ρ φ γ ui us K (mkPath φ γ ui us π (debtM ρ φ γ ui us K π)) ∧
      AdmissibleM S ρ (mkPath φ γ ui us π (debtM ρ φ γ ui us K π)) := by
  have hγ' : |1 - γ| < 1 := (FiscalRec.abs_one_sub_lt_one_iff γ).mpr hγ
  have hint : ∀ x : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 x → S.BddProc x →
      ∀ t, Integrable (x t) S.μ := fun x ha ⟨M, hM⟩ t =>
    MeasExpectationSystem.BddRV.integrable ⟨((ha t).mono (S.𝓕.le t)).aestronglyMeasurable,
      M, hM t⟩
  have husi : ∀ t, Integrable (us t) S.μ := hint us husa ⟨Ms, hus⟩
  refine ⟨eqmM_of_sol hρ0.ne' hπ, hπa, debtM_meas hπa huia husa hK,
    debtM_integrable (hint π hπa hπb) (hint ui huia huib) husi hKi, hπb,
    debtM_tvc hρ0 hρ1 hγ' hπ (hint π hπa hπb) (hint ui huia huib) husi hKi hus⟩

/-- Cochrane (2023), §22.7, pp. 508–509 (**existence**, on a probability space, any `φ`): the
Leeper model with `0 < γ < 2` has an admissible equilibrium iff the monetary equation
`E_t π_{t+1} = φπ_t + u_{i,t}` has a bounded adapted solution. -/
theorem leeperM_exists_iff {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 0 < γ ∧ γ < 2)
    {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui)
    (husa : StronglyAdapted S.𝓕 us) (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms)
    (hK : StronglyMeasurable[S.𝓕 0] K) (hKi : Integrable K S.μ) :
    (∃ x, LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x) ↔ HasBddSolM S φ ui :=
  ⟨fun ⟨_, hx, ha⟩ => sol_of_eqmM hx ha, fun ⟨_, hπa, hπb, hπ⟩ =>
    ⟨_, admissibleM_of_sol hρ0 hρ1 hγ huia huib husa hus hK hKi hπa hπb hπ⟩⟩

/-- Cochrane (2023), §22.7, pp. 508–509 (region (d) and the boundary `|φ| = 1`, on a probability
space): for `|φ| ≤ 1`, one bounded adapted solution `π̄` gives uncountably many admissible
equilibria, indexed by the date-0 jump `c` (`π_t = π̄_t + cφᵗ`). -/
theorem leeperM_uncountable [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : |φ| ≤ 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui) (husa : StronglyAdapted S.𝓕 us)
    (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms) (hK : StronglyMeasurable[S.𝓕 0] K)
    (hKi : Integrable K S.μ) (hsol : HasBddSolM S φ ui) :
    ¬ {x | LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x}.Countable := by
  obtain ⟨pb, hpa, ⟨M, hM⟩, hpE⟩ := hsol
  let g : ℝ → ℕ → Ω → ℝ := fun c t => pb t + fun _ => c * φ ^ t
  have hpi : ∀ t, Integrable (pb t) S.μ := fun t =>
    MeasExpectationSystem.BddRV.integrable ⟨((hpa t).mono (S.𝓕.le t)).aestronglyMeasurable,
      M, hM t⟩
  have hg : ∀ c, StronglyAdapted S.𝓕 (g c) ∧ S.BddProc (g c) ∧ MonEqM S φ ui (g c) := by
    intro c
    refine ⟨fun t => (hpa t).add stronglyMeasurable_const, ⟨M + |c|, fun t => ?_⟩, fun t => ?_⟩
    · filter_upwards [hM t] with ω h
      change |pb t ω + c * φ ^ t| ≤ M + |c|
      refine (abs_add_le _ _).trans (add_le_add h ?_)
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg c) (pow_le_one₀ (abs_nonneg φ) hφ)
    · filter_upwards [S.E_add (hpi (t + 1)) (integrable_const (c * φ ^ (t + 1))) t, hpE t]
        with ω e1 e2
      change S.E t (pb (t + 1) + fun _ => c * φ ^ (t + 1)) ω = _
      rw [e1, Pi.add_apply, e2, S.E_const]
      simp only [g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  let f : ℝ → Outcome Ω := fun c => mkPath φ γ ui us (g c) (debtM ρ φ γ ui us K (g c))
  have hmaps : Set.MapsTo f Set.univ
      {x | LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x} := fun c _ =>
    admissibleM_of_sol hρ0 hρ1 hγ huia huib husa hus hK hKi (hg c).1 (hg c).2.1 (hg c).2.2
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrArg Outcome.pi h) 0) ω
    simpa [f, g, mkPath] using this
  intro hcount
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Cochrane (2023), §22.7, pp. 508–509 (**the full characterisation at `φ² = 1` on every
probability space**): with `0 < γ < 2`, the Leeper model has an admissible equilibrium iff the
conditional sums `∑_{j<T} φʲ E_t u_{i,t+j}` are essentially bounded; and then it has uncountably
many. -/
theorem leeperM_unit_iff [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : φ ^ 2 = 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui) (husa : StronglyAdapted S.𝓕 us)
    (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms) (hK : StronglyMeasurable[S.𝓕 0] K)
    (hKi : Integrable K S.μ) :
    ((∃ x, LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x) ↔ CondBddM S φ ui) ∧
      (CondBddM S φ ui →
        ¬ {x | LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x}.Countable) := by
  have e1 := leeperM_exists_iff (φ := φ) hρ0 hρ1 hγ huia huib husa hus hK hKi
  have e2 := exists_iff_condBddM hφ huia huib
  exact ⟨e1.trans e2, fun hc => leeperM_uncountable hρ0 hρ1
    (TidyR5UnitRoot.abs_eq_one hφ).le hγ huia huib husa hus hK hKi (e2.2 hc)⟩

/-- Cochrane (2023), §22.7, pp. 508–509 (**the dichotomy at `φ² = 1`** on every probability
space): the set of admissible equilibria is empty or uncountable. -/
theorem leeperM_unit_dichotomy [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : φ ^ 2 = 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui) (husa : StronglyAdapted S.𝓕 us)
    (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms) (hK : StronglyMeasurable[S.𝓕 0] K)
    (hKi : Integrable K S.μ) :
    {x | LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x} = ∅ ∨
      ¬ {x | LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x}.Countable := by
  obtain ⟨e, hu⟩ := leeperM_unit_iff hρ0 hρ1 hφ hγ huia huib husa hus hK hKi
  by_cases hc : CondBddM S φ ui
  · exact Or.inr (hu hc)
  · refine Or.inl (Set.eq_empty_iff_forall_notMem.2 fun x hx => hc (e.1 ⟨x, hx⟩))

/-- Cochrane (2023), §22.7, pp. 508–509, at `φ = 1` on every probability space: the Leeper model
has an admissible equilibrium (then uncountably many) iff `|E_t ∑_{j<T} u_{i,t+j}| ≤ C` a.s. for
all `t`, `T`. -/
theorem leeperM_phi_one_iff [Nonempty Ω] {ρ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui) (husa : StronglyAdapted S.𝓕 us)
    (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms) (hK : StronglyMeasurable[S.𝓕 0] K)
    (hKi : Integrable K S.μ) :
    (∃ x, LeeperEqmM S ρ 1 γ ui us K x ∧ AdmissibleM S ρ x) ↔
      ∃ C, ∀ t T, ∀ᵐ ω ∂S.μ, |S.E t (∑ j ∈ Finset.range T, ui (t + j)) ω| ≤ C :=
  (leeperM_exists_iff hρ0 hρ1 hγ huia huib husa hus hK hKi).trans
    (exists_iff_phi_one_M huia huib)

/-- Cochrane (2023), §22.7, pp. 508–509, at `φ = −1` on every probability space: the Leeper model
has an admissible equilibrium (then uncountably many) iff
`|E_t ∑_{j<T} (−1)ʲ u_{i,t+j}| ≤ C` a.s. for all `t`, `T`. -/
theorem leeperM_phi_neg_one_iff [Nonempty Ω] {ρ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui) (husa : StronglyAdapted S.𝓕 us)
    (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms) (hK : StronglyMeasurable[S.𝓕 0] K)
    (hKi : Integrable K S.μ) :
    (∃ x, LeeperEqmM S ρ (-1) γ ui us K x ∧ AdmissibleM S ρ x) ↔
      ∃ C, ∀ t T, ∀ᵐ ω ∂S.μ,
        |S.E t (∑ j ∈ Finset.range T, (-1 : ℝ) ^ j • ui (t + j)) ω| ≤ C :=
  (leeperM_exists_iff hρ0 hρ1 hγ huia huib husa hus hK hKi).trans
    (exists_iff_phi_neg_one_M huia huib)

/-- Cochrane (2023), §22.7, pp. 508–509 (**region (d)** on every probability space, `|φ| < 1`,
`0 < γ < 2`, "we are back to indeterminacy"): there are uncountably many admissible equilibria
(the accumulated disturbance `D_{t+1} = φD_t + u_{i,t}` is a bounded solution). -/
theorem leeperM_region_d [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : |φ| < 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : StronglyAdapted S.𝓕 ui) (huib : S.BddProc ui) (husa : StronglyAdapted S.𝓕 us)
    (hus : ∀ t, ∀ᵐ ω ∂S.μ, |us t ω| ≤ Ms) (hK : StronglyMeasurable[S.𝓕 0] K)
    (hKi : Integrable K S.μ) :
    ¬ {x | LeeperEqmM S ρ φ γ ui us K x ∧ AdmissibleM S ρ x}.Countable := by
  obtain ⟨Mi, hMi⟩ := huib
  have hui : ∀ t, Integrable (ui t) S.μ := fun t =>
    MeasExpectationSystem.BddRV.integrable ⟨((huia t).mono (S.𝓕.le t)).aestronglyMeasurable,
      Mi, hMi t⟩
  set B := |Mi| / (1 - |φ|) with hB
  have h1 : 0 < 1 - |φ| := by linarith
  have hbound : ∀ᵐ ω ∂S.μ, ∀ t, |accumM φ ui t ω| ≤ B := by
    filter_upwards [ae_all_iff.2 hMi] with ω hω t
    induction t with
    | zero =>
      change |(0 : Ω → ℝ) ω| ≤ B
      simp only [Pi.zero_apply, abs_zero, hB]
      positivity
    | succ t ih =>
      change |(φ • accumM φ ui t + ui t) ω| ≤ B
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : |φ| * B + |Mi| = B := by
        simp only [hB]; field_simp; ring
      calc |φ * accumM φ ui t ω + ui t ω| ≤ |φ| * |accumM φ ui t ω| + |Mi| := by
            refine (abs_add_le _ _).trans (add_le_add (abs_mul _ _).le ?_)
            exact (hω t).trans (le_abs_self Mi)
        _ ≤ |φ| * B + |Mi| := by gcongr
        _ = B := e
  exact leeperM_uncountable hρ0 hρ1 hφ.le hγ huia ⟨Mi, hMi⟩ husa hus hK hKi
    ⟨accumM φ ui, fun t => (accumM_meas huia t).1, ⟨B, fun t => hbound.mono fun ω h => h t⟩,
      accumM_solves huia hui⟩

end Cochrane.ObservationalEquivalence.TidyR5LeeperMeasure
