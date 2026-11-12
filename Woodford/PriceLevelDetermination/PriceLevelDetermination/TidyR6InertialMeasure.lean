/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.InertialBoundaryExistCube
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration

/-!
# The boundary of Proposition 2.8 on a probability space

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 633–634, with the
expectations of a genuine probability space: `(Ω, μ)` a probability space, `𝓕` a filtration and
`E_t = μ[· | 𝓕 t]` Mathlib's conditional expectation, every equation holding almost surely. The
core `ExpectationSystem` cannot host such a model (on a countable state space its forecasts are
finitely supported, `SGUStochasticMeasure.expectationSystem_finite_support`), so this module
restates the exact inertial model there (`MeasEq`: adapted, essentially bounded processes, the
Fisher equation and the rule as a.s. conditional equations) and proves the uniqueness results of
`InertialBoundary` for it.

## Main results

* `ae_push`: the supremum argument almost surely (on the essential supremum of a process).
* `unique_affine_measure`: the rule `φ_π π + h(î_{−1})` (`φ_π ≠ 0`, `h` continuous, expanding
  diagonal): any two equilibria with the same initial rate and disturbances agree a.s. at every
  date.
* `unique_cube_measure`: the same for `ρ î_{−1} + σπ³` with `σ² = 1`, `σρ ≥ 1`.

On a probability space a variable known at `t` (`𝓕 t`-measurable) is a.s. its own conditional
expectation, and so is every measurable function of it: informational closure holds
automatically, almost surely, and no extra hypothesis on the expectations is needed.
-/

namespace Woodford.PriceLevelDetermination.TidyR6InertialMeasure

open MeasureTheory Filter
open scoped Topology
open LocalIFTSystems (cbrt cbrt_pow)
open InertialBoundary (sub_le_cbrt pow_le_of_le_cbrt cbrt_nonneg)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### The supremum argument almost surely -/

omit [IsProbabilityMeasure μ] in
/-- Woodford (2003), App. A.3, p. 634 (tool): **the push argument almost surely.** If a process
is essentially bounded and every essential bound `B` of it satisfies
`|a_t| + κ|a_t|³ ≤ B` a.s. at every date, the process is a.s. zero at every date. -/
theorem ae_push {a : ℕ → Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) (hb : ∃ M, ∀ t, ∀ᵐ ω ∂μ, |a t ω| ≤ M)
    (hstep : ∀ B, (∀ t, ∀ᵐ ω ∂μ, |a t ω| ≤ B) →
      ∀ t, ∀ᵐ ω ∂μ, |a t ω| + κ * |a t ω| ^ 3 ≤ B) :
    ∀ t, a t =ᵐ[μ] 0 := by
  set S : Set ℝ := {B | 0 ≤ B ∧ ∀ t, ∀ᵐ ω ∂μ, |a t ω| ≤ B} with hS
  obtain ⟨M, hM⟩ := hb
  have hne : S.Nonempty := ⟨max M 0, le_max_right _ _, fun t => (hM t).mono fun ω h =>
    h.trans (le_max_left _ _)⟩
  have hbdd : BddBelow S := ⟨0, fun B hB => hB.1⟩
  set b := sInf S with hb
  have hb0 : 0 ≤ b := le_csInf hne fun B hB => hB.1
  have hbz : b = 0 := by
    by_contra hne0
    have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hne0)
    set η := min (b / 2) (κ * (b / 2) ^ 3 / 2) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by positivity)
    obtain ⟨B, hBS, hBlt⟩ := exists_lt_of_csInf_lt hne (show sInf S < b + η by linarith)
    have hstepB := hstep B hBS.2
    set B' := max (b / 2) (b - κ * (b / 2) ^ 3 / 2) with hB'
    have hB'S : B' ∈ S := by
      refine ⟨(by positivity : (0 : ℝ) ≤ b / 2).trans (le_max_left _ _), fun t => ?_⟩
      filter_upwards [hstepB t] with ω hω
      by_cases hsm : |a t ω| < b / 2
      · exact hsm.le.trans (le_max_left _ _)
      · push Not at hsm
        have h3 : (b / 2) ^ 3 ≤ |a t ω| ^ 3 := pow_le_pow_left₀ (by positivity) hsm 3
        have h4 : η ≤ κ * (b / 2) ^ 3 / 2 := min_le_right _ _
        refine le_trans ?_ (le_max_right _ _)
        nlinarith
    have hle := csInf_le hbdd hB'S
    have h1 : B' < b := max_lt (by linarith) (by
      have : 0 < κ * (b / 2) ^ 3 / 2 := by positivity
      linarith)
    linarith
  intro t
  have hall : ∀ n : ℕ, ∀ᵐ ω ∂μ, |a t ω| ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨B, hBS, hBlt⟩ := exists_lt_of_csInf_lt hne
      (show sInf S < 1 / ((n : ℝ) + 1) by rw [← hb, hbz]; positivity)
    exact (hBS.2 t).mono fun ω h => h.trans hBlt.le
  filter_upwards [ae_all_iff.mpr hall] with ω hω
  have h0 : |a t ω| ≤ 0 := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    linarith [hω n]
  simpa using abs_nonpos_iff.mp h0

/-! ### The exact inertial model on a filtered probability space -/

/-- Woodford (2003), eq. (2.12), p. 96 (tool): the lagged interest rate `î_{t−1}`, with
`î_{−1}` given. -/
def lagI (im1 : ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => im1
  | t + 1 => i t

variable (μ) in
/-- Woodford (2003), eqs. (1.32) and (2.12), pp. 79, 96, on a probability space: `(π, î)` is an
equilibrium of the exact model with rule `Ψ`, initial rate `î_{−1}` and disturbances `(r̂, ν)`:
both processes are adapted to `𝓕` and essentially bounded, and a.s. at every date
`E_t[î_t − π_{t+1} − r̂_t] = 0` and `E_t[î_t − Ψ(π_t, î_{t−1}) − ν_t] = 0`, with
`E_t = μ[· | 𝓕 t]`. -/
def MeasEq (𝓕 : Filtration ℕ mΩ) (Ψ : ℝ × ℝ → ℝ) (im1 : ℝ) (r ν : ℕ → Ω → ℝ)
    (π i : ℕ → Ω → ℝ) : Prop :=
  (∀ t, StronglyMeasurable[𝓕 t] (π t) ∧ StronglyMeasurable[𝓕 t] (i t)) ∧
  (∃ M, ∀ t, ∀ᵐ ω ∂μ, |π t ω| ≤ M ∧ |i t ω| ≤ M) ∧
  (∀ t, μ[i t - π (t + 1) - r t | 𝓕 t] =ᵐ[μ] 0) ∧
  (∀ t, μ[i t - (fun ω => Ψ (π t ω, lagI im1 i t ω)) - ν t | 𝓕 t] =ᵐ[μ] 0)

/-- Woodford (2003), App. A.3, p. 634 (tool): an essentially bounded variable measurable for a
sub-σ-algebra of the filtration is integrable. -/
theorem integrable_of_known {𝓕 : Filtration ℕ mΩ} {t : ℕ} {f : Ω → ℝ}
    (hf : StronglyMeasurable[𝓕 t] f) {C : ℝ} (hC : ∀ᵐ ω ∂μ, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound ((hf.mono (𝓕.le t)).aestronglyMeasurable) C
    (hC.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Woodford (2003), App. A.3, p. 634 (tool): **a.s. closure**: if `f` is known at `t` and
essentially bounded, then `E_t[f − g] = f − E_t g` a.s. -/
theorem condExp_known_sub {𝓕 : Filtration ℕ mΩ} {t : ℕ} {f g : Ω → ℝ}
    (hf : StronglyMeasurable[𝓕 t] f) {C : ℝ} (hC : ∀ᵐ ω ∂μ, |f ω| ≤ C) (hg : Integrable g μ) :
    μ[f - g | 𝓕 t] =ᵐ[μ] f - μ[g | 𝓕 t] := by
  have hfi := integrable_of_known hf hC
  filter_upwards [condExp_sub hfi hg (𝓕 t)] with ω hω
  rw [hω, Pi.sub_apply, Pi.sub_apply, condExp_of_stronglyMeasurable (𝓕.le t) hf hfi]

/-- Woodford (2003), (2.12), p. 96 (tool): the lagged rate is known at `t`. -/
theorem lagI_known {𝓕 : Filtration ℕ mΩ} {im1 : ℝ} {i : ℕ → Ω → ℝ}
    (hi : ∀ t, StronglyMeasurable[𝓕 t] (i t)) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (lagI im1 i t) := by
  cases t with
  | zero => exact stronglyMeasurable_const
  | succ s => exact (hi s).mono (𝓕.mono (Nat.le_succ s))

omit [IsProbabilityMeasure μ] in
/-- Woodford (2003), (2.12), p. 96 (tool): the lagged rate is essentially bounded. -/
theorem lagI_bound {im1 M : ℝ} {i : ℕ → Ω → ℝ} (hi : ∀ t, ∀ᵐ ω ∂μ, |i t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂μ, |lagI im1 i t ω| ≤ max M |im1| := by
  cases t with
  | zero => exact Eventually.of_forall fun _ => le_max_right _ _
  | succ s => exact (hi s).mono fun _ h => h.trans (le_max_left _ _)

/-- Woodford (2003), eq. (1.32), p. 79, a.s. (tool): in an equilibrium
`E_t π_{t+1} = î_t − E_t r̂_t` a.s. -/
theorem fisher_ae {𝓕 : Filtration ℕ mΩ} {Ψ : ℝ × ℝ → ℝ} {im1 : ℝ} {r ν π i : ℕ → Ω → ℝ}
    (hr : ∀ t, Integrable (r t) μ) (he : MeasEq μ 𝓕 Ψ im1 r ν π i) (t : ℕ) :
    μ[π (t + 1) | 𝓕 t] =ᵐ[μ] i t - μ[r t | 𝓕 t] := by
  obtain ⟨had, ⟨M, hM⟩, hF, -⟩ := he
  have hiI : Integrable (i t) μ :=
    integrable_of_known (had t).2 ((hM t).mono fun _ h => h.2)
  have hπI : Integrable (π (t + 1)) μ :=
    integrable_of_known ((had (t + 1)).1) ((hM (t + 1)).mono fun _ h => h.1)
  have h1 := condExp_sub (hiI.sub hπI) (hr t) (𝓕 t)
  have h2 := condExp_sub hiI hπI (𝓕 t)
  rw [condExp_of_stronglyMeasurable (𝓕.le t) (had t).2 hiI] at h2
  filter_upwards [hF t, h1, h2] with ω h0 h1' h2'
  rw [h1', Pi.sub_apply, h2'] at h0
  simp only [Pi.sub_apply, Pi.zero_apply] at h0 ⊢
  linarith

/-! ### The affine rule -/

/-- Woodford (2003), eq. (2.12), p. 96, a.s. (tool): for the rule `φ_π π + h(î_{−1})` with `h`
continuous, in an equilibrium `î_t = φ_π π_t + h(î_{t−1}) + E_t ν_t` a.s. (a.s. closure). -/
theorem rule_ae_affine {𝓕 : Filtration ℕ mΩ} {Ψ : ℝ × ℝ → ℝ} {φ : ℝ} {h : ℝ → ℝ}
    (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) (hh : Continuous h) {im1 : ℝ}
    {r ν π i : ℕ → Ω → ℝ} (hν : ∀ t, Integrable (ν t) μ) (he : MeasEq μ 𝓕 Ψ im1 r ν π i)
    (t : ℕ) : i t =ᵐ[μ] fun ω => φ * π t ω + h (lagI im1 i t ω) + μ[ν t | 𝓕 t] ω := by
  obtain ⟨had, ⟨M, hM⟩, -, hR⟩ := he
  set L := max M |im1| with hL
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -L) (b := L)).exists_bound_of_continuousOn
    hh.continuousOn
  have hfe : (i t - fun ω => Ψ (π t ω, lagI im1 i t ω)) =
      i t - fun ω => φ * π t ω + h (lagI im1 i t ω) := by
    funext ω
    simp only [Pi.sub_apply, hΨ]
  have hfm : StronglyMeasurable[𝓕 t] (i t - fun ω => Ψ (π t ω, lagI im1 i t ω)) := by
    rw [hfe]
    exact (had t).2.sub ((stronglyMeasurable_const.mul (had t).1).add
      (hh.comp_stronglyMeasurable (lagI_known (fun s => (had s).2) t)))
  have hfb : ∀ᵐ ω ∂μ, |(i t - fun ω => Ψ (π t ω, lagI im1 i t ω)) ω| ≤ M + |φ| * M + C := by
    filter_upwards [hM t, lagI_bound (fun s => (hM s).mono fun _ h => h.2) t] with ω h1 h2
    have h3 := hC _ ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩
    rw [Real.norm_eq_abs] at h3
    rw [hfe]
    simp only [Pi.sub_apply]
    calc |i t ω - (φ * π t ω + h (lagI im1 i t ω))|
        ≤ |i t ω| + (|φ| * |π t ω| + |h (lagI im1 i t ω)|) := by
          refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
          exact (abs_add_le _ _).trans (by rw [abs_mul])
      _ ≤ M + |φ| * M + C := by
          have := mul_le_mul_of_nonneg_left h1.1 (abs_nonneg φ)
          linarith [h1.2]
  have hk := condExp_known_sub hfm hfb (hν t)
  filter_upwards [hR t, hk] with ω h0 h1
  rw [h1] at h0
  simp only [Pi.sub_apply, Pi.zero_apply, hΨ] at h0
  linarith

/-- **Uniqueness on the boundary `φ_π ≠ 0` on a probability space** (Woodford (2003), Prop. 2.8,
p. 96; App. A.3, p. 634): for the rule `Ψ(π, i) = φ_π π + h(i)` with `φ_π ≠ 0`, `h` continuous
and the expanding diagonal `|g(i) − g(i')| ≥ |i − i'| + κ|i − i'|³` (`g(i) = φ_π i + h(i)`),
any two equilibria with conditional expectations `μ[· | 𝓕 t]`, the same initial rate and the
same integrable disturbances agree almost surely at every date. -/
theorem unique_affine_measure {𝓕 : Filtration ℕ mΩ} {Ψ : ℝ × ℝ → ℝ} {φ κ : ℝ} {h : ℝ → ℝ}
    (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) (hφ : φ ≠ 0) (hκ : 0 < κ) (hh : Continuous h)
    (hexp : ∀ i i', |i - i'| + κ * |i - i'| ^ 3 ≤ |(φ * i + h i) - (φ * i' + h i')|)
    {im1 : ℝ} {r ν : ℕ → Ω → ℝ} (hr : ∀ t, Integrable (r t) μ) (hν : ∀ t, Integrable (ν t) μ)
    {π i π' i' : ℕ → Ω → ℝ} (he : MeasEq μ 𝓕 Ψ im1 r ν π i)
    (he' : MeasEq μ 𝓕 Ψ im1 r ν π' i') :
    ∀ t, π t =ᵐ[μ] π' t ∧ i t =ᵐ[μ] i' t := by
  have hA := rule_ae_affine hΨ hh hν he
  have hA' := rule_ae_affine hΨ hh hν he'
  have hF := fisher_ae hr he
  have hF' := fisher_ae hr he'
  obtain ⟨had, ⟨M, hM⟩, -, -⟩ := he
  obtain ⟨had', ⟨M', hM'⟩, -, -⟩ := he'
  set L := max M M' with hL
  have hiL : ∀ t, ∀ᵐ ω ∂μ, |i t ω| ≤ L := fun t =>
    (hM t).mono fun _ h => h.2.trans (le_max_left _ _)
  have hiL' : ∀ t, ∀ᵐ ω ∂μ, |i' t ω| ≤ L := fun t =>
    (hM' t).mono fun _ h => h.2.trans (le_max_right _ _)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -L) (b := L)).exists_bound_of_continuousOn
    hh.continuousOn
  have hπI : ∀ t, Integrable (π t) μ := fun t =>
    integrable_of_known (had t).1 ((hM t).mono fun _ h => h.1)
  have hπI' : ∀ t, Integrable (π' t) μ := fun t =>
    integrable_of_known (had' t).1 ((hM' t).mono fun _ h => h.1)
  have hHm : ∀ t, StronglyMeasurable[𝓕 t] (fun ω => h (i t ω) - h (i' t ω)) := fun t =>
    (hh.comp_stronglyMeasurable (had t).2).sub (hh.comp_stronglyMeasurable (had' t).2)
  have hHb : ∀ t, ∀ᵐ ω ∂μ, |h (i t ω) - h (i' t ω)| ≤ C + C := by
    intro t
    filter_upwards [hiL t, hiL' t] with ω h1 h2
    have e1 := hC _ ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩
    have e2 := hC _ ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩
    rw [Real.norm_eq_abs] at e1 e2
    exact (abs_sub _ _).trans (add_le_add e1 e2)
  have hHI : ∀ t, Integrable (fun ω => h (i t ω) - h (i' t ω)) μ := fun t =>
    integrable_of_known (hHm t) (hHb t)
  set D : ℕ → Ω → ℝ := fun t => i t - i' t with hD
  -- the forecast of next period's gap
  have hCt : ∀ t, μ[D (t + 1) | 𝓕 t] =ᵐ[μ]
      fun ω => (φ * i t ω + h (i t ω)) - (φ * i' t ω + h (i' t ω)) := by
    intro t
    have hDe : D (t + 1) =ᵐ[μ]
        φ • (π (t + 1) - π' (t + 1)) + fun ω => h (i t ω) - h (i' t ω) := by
      filter_upwards [hA (t + 1), hA' (t + 1)] with ω h1 h2
      simp only [hD, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [h1, h2]
      simp only [lagI]
      ring
    have hsI : Integrable (φ • (π (t + 1) - π' (t + 1))) μ :=
      ((hπI (t + 1)).sub (hπI' (t + 1))).smul φ
    filter_upwards [condExp_congr_ae (m := 𝓕 t) hDe, condExp_add hsI (hHI t) (𝓕 t),
      condExp_smul (m := 𝓕 t) φ (π (t + 1) - π' (t + 1)),
      condExp_sub (hπI (t + 1)) (hπI' (t + 1)) (𝓕 t), hF t, hF' t] with ω e1 e2 e3 e4 e5 e6
    rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, e4, Pi.sub_apply, e5, e6,
      condExp_of_stronglyMeasurable (𝓕.le t) (hHm t) (hHI t)]
    simp only [Pi.sub_apply, smul_eq_mul]
    ring
  -- the gap of interest rates vanishes
  have hD0 : ∀ t, D t =ᵐ[μ] 0 := by
    refine ae_push hκ ⟨L + L, fun t => ?_⟩ (fun B hB t => ?_)
    · filter_upwards [hiL t, hiL' t] with ω h1 h2
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    · have hb := ae_bdd_abs_condExp_of_ae_bdd_abs (m := 𝓕 t) (hB (t + 1))
      filter_upwards [hb, hCt t] with ω h1 h2
      rw [h2] at h1
      have := hexp (i t ω) (i' t ω)
      change |i t ω - i' t ω| + κ * |i t ω - i' t ω| ^ 3 ≤ B
      linarith
  have hI : ∀ t, i t =ᵐ[μ] i' t := fun t => by
    filter_upwards [hD0 t] with ω h
    simpa [hD, sub_eq_zero] using h
  have hlag : ∀ t, ∀ᵐ ω ∂μ, lagI im1 i t ω = lagI im1 i' t ω := by
    intro t
    cases t with
    | zero => exact Eventually.of_forall fun _ => rfl
    | succ s => exact hI s
  refine fun t => ⟨?_, hI t⟩
  filter_upwards [hA t, hA' t, hI t, hlag t] with ω h1 h2 h3 h4
  rw [h3, h4] at h1
  have h5 : φ * π t ω = φ * π' t ω := by linarith
  exact mul_left_cancel₀ hφ h5

/-! ### The cubic rule -/

/-- Woodford (2003), eq. (2.12), p. 96, a.s. (tool): for the rule `ρ î_{−1} + σπ³`, in an
equilibrium `î_t = ρ î_{t−1} + σ π_t³ + E_t ν_t` a.s. -/
theorem rule_ae_cube {𝓕 : Filtration ℕ mΩ} {Ψ : ℝ × ℝ → ℝ} {ρ σ : ℝ}
    (hΨ : ∀ π i, Ψ (π, i) = ρ * i + σ * π ^ 3) {im1 : ℝ} {r ν π i : ℕ → Ω → ℝ}
    (hν : ∀ t, Integrable (ν t) μ) (he : MeasEq μ 𝓕 Ψ im1 r ν π i) (t : ℕ) :
    i t =ᵐ[μ] fun ω => ρ * lagI im1 i t ω + σ * π t ω ^ 3 + μ[ν t | 𝓕 t] ω := by
  obtain ⟨had, ⟨M, hM⟩, -, hR⟩ := he
  have hfe : (i t - fun ω => Ψ (π t ω, lagI im1 i t ω)) =
      i t - fun ω => ρ * lagI im1 i t ω + σ * π t ω ^ 3 := by
    funext ω
    simp only [Pi.sub_apply, hΨ]
  have hfm : StronglyMeasurable[𝓕 t] (i t - fun ω => Ψ (π t ω, lagI im1 i t ω)) := by
    rw [hfe]
    exact (had t).2.sub ((stronglyMeasurable_const.mul (lagI_known (fun s => (had s).2) t)).add
      (stronglyMeasurable_const.mul ((continuous_pow 3).comp_stronglyMeasurable (had t).1)))
  have hfb : ∀ᵐ ω ∂μ, |(i t - fun ω => Ψ (π t ω, lagI im1 i t ω)) ω| ≤
      M + |ρ| * max M |im1| + |σ| * M ^ 3 := by
    filter_upwards [hM t, lagI_bound (fun s => (hM s).mono fun _ h => h.2) t] with ω h1 h2
    rw [hfe]
    simp only [Pi.sub_apply]
    have h3 : |π t ω| ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h1.1 3
    calc |i t ω - (ρ * lagI im1 i t ω + σ * π t ω ^ 3)|
        ≤ |i t ω| + (|ρ| * |lagI im1 i t ω| + |σ| * |π t ω| ^ 3) := by
          refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
          exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul, abs_pow])
      _ ≤ M + |ρ| * max M |im1| + |σ| * M ^ 3 := by
          have := mul_le_mul_of_nonneg_left h2 (abs_nonneg ρ)
          have := mul_le_mul_of_nonneg_left h3 (abs_nonneg σ)
          linarith [h1.2]
  have hk := condExp_known_sub hfm hfb (hν t)
  filter_upwards [hR t, hk] with ω h0 h1
  rw [h1] at h0
  simp only [Pi.sub_apply, Pi.zero_apply, hΨ] at h0
  linarith

/-- Woodford (2003), App. A.3, p. 634 (tool): the bound `w ↦ ∛(4 max(B − τw, 0))` is antitone
for `τ ≥ 0`. -/
theorem antitone_cbrt_bound (B τ : ℝ) (hτ : 0 ≤ τ) :
    Antitone fun w : ℝ => cbrt (4 * max (B - τ * w) 0) := fun a b hab =>
  InertialBoundaryExistCube.cbrt_strictMono.monotone (by
    have : B - τ * b ≤ B - τ * a := by nlinarith
    have := max_le_max this (le_refl (0 : ℝ))
    linarith)

/-- **Uniqueness on the boundary `φ_π = 0` on a probability space** (Woodford (2003), Prop. 2.8,
p. 96; App. A.3, p. 634): for the rule `Ψ(π, i) = ρ i + σπ³` with `σ² = 1`, `σρ ≥ 1`, any two
equilibria with conditional expectations `μ[· | 𝓕 t]`, the same initial rate and the same
integrable disturbances agree almost surely at every date. -/
theorem unique_cube_measure {𝓕 : Filtration ℕ mΩ} {Ψ : ℝ × ℝ → ℝ} {ρ σ : ℝ}
    (hΨ : ∀ π i, Ψ (π, i) = ρ * i + σ * π ^ 3) (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ)
    {im1 : ℝ} {r ν : ℕ → Ω → ℝ} (hr : ∀ t, Integrable (r t) μ) (hν : ∀ t, Integrable (ν t) μ)
    {π i π' i' : ℕ → Ω → ℝ} (he : MeasEq μ 𝓕 Ψ im1 r ν π i)
    (he' : MeasEq μ 𝓕 Ψ im1 r ν π' i') :
    ∀ t, π t =ᵐ[μ] π' t ∧ i t =ᵐ[μ] i' t := by
  have hA := rule_ae_cube hΨ hν he
  have hA' := rule_ae_cube hΨ hν he'
  have hF := fisher_ae hr he
  have hF' := fisher_ae hr he'
  obtain ⟨had, ⟨M, hM⟩, -, -⟩ := he
  obtain ⟨had', ⟨M', hM'⟩, -, -⟩ := he'
  set τ := σ * ρ with hτdef
  have hτ0 : 0 ≤ τ := by linarith
  have hsa : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  set L := max M M' with hL
  have hπI : ∀ t, Integrable (π t) μ := fun t =>
    integrable_of_known (had t).1 ((hM t).mono fun _ h => h.1)
  have hπI' : ∀ t, Integrable (π' t) μ := fun t =>
    integrable_of_known (had' t).1 ((hM' t).mono fun _ h => h.1)
  set D : ℕ → Ω → ℝ := fun t => i t - i' t with hD
  have hDm : ∀ t, StronglyMeasurable[𝓕 t] (D t) := fun t => (had t).2.sub (had' t).2
  -- the cubic gap of inflation, a.s.
  have hgap : ∀ t, ∀ᵐ ω ∂μ, π (t + 1) ω ^ 3 - π' (t + 1) ω ^ 3 = σ * D (t + 1) ω - τ * D t ω := by
    intro t
    filter_upwards [hA (t + 1), hA' (t + 1)] with ω h1 h2
    simp only [lagI] at h1 h2
    change _ = σ * (i (t + 1) ω - i' (t + 1) ω) - σ * ρ * (i t ω - i' t ω)
    rw [h1, h2]
    linear_combination (π' (t + 1) ω ^ 3 - π (t + 1) ω ^ 3) * hσ
  -- the forecast of the inflation gap is the interest-rate gap
  have hEP : ∀ t, μ[π (t + 1) - π' (t + 1) | 𝓕 t] =ᵐ[μ] D t := by
    intro t
    filter_upwards [condExp_sub (hπI (t + 1)) (hπI' (t + 1)) (𝓕 t), hF t, hF' t] with ω e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3]
    simp only [hD, Pi.sub_apply]
    ring
  have hD0 : ∀ t, D t =ᵐ[μ] 0 := by
    refine ae_push (κ := 1 / 4) (by norm_num) ⟨L + L, fun t => ?_⟩ (fun B hB t => ?_)
    · filter_upwards [hM t, hM' t] with ω h1 h2
      exact (abs_sub _ _).trans (add_le_add (h1.2.trans (le_max_left _ _))
        (h2.2.trans (le_max_right _ _)))
    · set fp : ℝ → ℝ := fun w => cbrt (4 * max (B - τ * w) 0) with hfp
      set fm : ℝ → ℝ := fun w => cbrt (4 * max (B - τ * (-w)) 0) with hfm
      have hfpA : Antitone fp := antitone_cbrt_bound B τ hτ0
      have hfmM : Monotone fm := fun a b hab => hfpA (neg_le_neg hab)
      have hfpm : StronglyMeasurable[𝓕 t] (fun ω => fp (D t ω)) :=
        (hfpA.measurable.comp (hDm t).measurable).stronglyMeasurable
      have hfmm : StronglyMeasurable[𝓕 t] (fun ω => fm (D t ω)) :=
        (hfmM.measurable.comp (hDm t).measurable).stronglyMeasurable
      have hDB : ∀ᵐ ω ∂μ, |D t ω| ≤ B := hB t
      have hfpb : ∀ᵐ ω ∂μ, |fp (D t ω)| ≤ fp (-B) := by
        filter_upwards [hDB] with ω h
        rw [abs_of_nonneg (cbrt_nonneg (by positivity))]
        exact hfpA (abs_le.mp h).1
      have hfmb : ∀ᵐ ω ∂μ, |fm (D t ω)| ≤ fm B := by
        filter_upwards [hDB] with ω h
        rw [abs_of_nonneg (cbrt_nonneg (by positivity))]
        exact hfmM (abs_le.mp h).2
      have hfpI := integrable_of_known hfpm hfpb
      have hfmI := integrable_of_known hfmm hfmb
      have hup : (π (t + 1) - π' (t + 1)) ≤ᵐ[μ] fun ω => fp (D t ω) := by
        filter_upwards [hgap t, hB (t + 1)] with ω h1 h2
        refine sub_le_cbrt ?_
        rw [h1]
        have : |σ * D (t + 1) ω| ≤ B := by rw [abs_mul, hsa, one_mul]; exact h2
        linarith [(abs_le.mp this).2]
      have hlo : (π' (t + 1) - π (t + 1)) ≤ᵐ[μ] fun ω => fm (D t ω) := by
        filter_upwards [hgap t, hB (t + 1)] with ω h1 h2
        refine sub_le_cbrt ?_
        have : |σ * D (t + 1) ω| ≤ B := by rw [abs_mul, hsa, one_mul]; exact h2
        have h3 := (abs_le.mp this).1
        nlinarith
      have hU := condExp_mono (m := 𝓕 t) ((hπI (t + 1)).sub (hπI' (t + 1))) hfpI hup
      have hLo := condExp_mono (m := 𝓕 t) ((hπI' (t + 1)).sub (hπI (t + 1))) hfmI hlo
      rw [condExp_of_stronglyMeasurable (𝓕.le t) hfpm hfpI] at hU
      rw [condExp_of_stronglyMeasurable (𝓕.le t) hfmm hfmI] at hLo
      have hEPn : μ[π' (t + 1) - π (t + 1) | 𝓕 t] =ᵐ[μ] -D t := by
        have e : π' (t + 1) - π (t + 1) = -(π (t + 1) - π' (t + 1)) := by abel
        rw [e]
        filter_upwards [condExp_neg (m := 𝓕 t) (μ := μ) (π (t + 1) - π' (t + 1)), hEP t]
          with ω e1 e2
        rw [e1, Pi.neg_apply, e2, Pi.neg_apply]
      filter_upwards [hU, hLo, hEP t, hEPn, hDB] with ω h1 h2 h3 h4 h5
      rw [h3] at h1
      rw [h4] at h2
      simp only [Pi.neg_apply] at h2
      set d := D t ω with hd
      change |d| + 1 / 4 * |d| ^ 3 ≤ B
      rcases le_or_gt 0 d with h0 | h0
      · have h6 := pow_le_of_le_cbrt h0 h1
        have hm : max (B - τ * d) 0 ≤ B - |d| := by
          rw [abs_of_nonneg h0]
          refine max_le (by nlinarith) (by linarith [le_abs_self d])
        rw [abs_of_nonneg h0] at hm ⊢
        linarith
      · have h6 := pow_le_of_le_cbrt (by linarith) h2
        have hm : max (B - τ * -d) 0 ≤ B - |d| := by
          rw [abs_of_neg h0]
          refine max_le (by nlinarith) (by linarith [neg_abs_le d, abs_of_neg h0])
        rw [abs_of_neg h0] at hm ⊢
        nlinarith
  have hI : ∀ t, i t =ᵐ[μ] i' t := fun t => by
    filter_upwards [hD0 t] with ω h
    simpa [hD, sub_eq_zero] using h
  have hlag : ∀ t, ∀ᵐ ω ∂μ, lagI im1 i t ω = lagI im1 i' t ω := by
    intro t
    cases t with
    | zero => exact Eventually.of_forall fun _ => rfl
    | succ s => exact hI s
  refine fun t => ⟨?_, hI t⟩
  filter_upwards [hA t, hA' t, hI t, hlag t] with ω h1 h2 h3 h4
  rw [h3, h4] at h1
  have h5 : σ * π t ω ^ 3 = σ * π' t ω ^ 3 := by linarith
  have h6 : π t ω ^ 3 = π' t ω ^ 3 := by
    have := congrArg (fun w => σ * w) h5
    rw [← mul_assoc, ← mul_assoc, hσ, one_mul, one_mul] at this
    exact this
  exact (Odd.pow_injective (by decide : Odd 3)) h6

end Woodford.PriceLevelDetermination.TidyR6InertialMeasure
