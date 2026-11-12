/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR8StochWerningMartingale
import ZeroBound.TidyR8StochWerningActiveTrap

/-!
# Natural-rate shocks when the interest rate tracks the natural rate after the trap

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, p. 474 ("The
equilibrium nominal interest rate is zero up to period `T`, and then rises back to the natural
rate `i_t = u_{r,t}`, for `t ≥ T`"), equations (20.5)–(20.10), with a random natural rate
`u_{r,t} = trapStep u T t + ν_t`, `E_t dν = −ην dt`. The book's rate rule after the trap is
`i = u_r`; with a random natural rate the interest rate is random after `T` (`trackRate`,
`IsStochEqmTrack`). (TidyR7StochWerningNatural keeps `i = 0` throughout.)

Now the natural-rate shock matters only during the trap, and the response of the unstable
combination is time varying:

* **`unstable_track`**: in every regular `L¹`-bounded equilibrium, almost surely at every date,
  `λ^f π_s − κx_s = (λ^f wPi(0)_s − κ wX(0)_s) + c(s) ν_s`, with
  `c(s) = d(1 − e^{−(λ^f+η)(T−s)})` before `T` and `0` after (`trackD`, `d = −κσ/(λ^f + η)`): news
  about the natural rate moves the unstable combination by the deterministic forward solution
  `−κσ∫_s^T e^{−(λ^f+η)(r−s)}dr`, and not at all after the trap;
* **`condExp_pi_track`**: `E_sπ_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s) + K(s,t)ν_s` with
  `K(s,t) = ∫_s^t e^{−λ^b(t−r)}c(r)e^{−η(r−s)}dr` (`trackK`);
* **existence** (`isStochEqmTrack_trackPi`, `regular_bddL2_track`): on a Brownian
  filtration, for every regular `L²`-bounded shock with `E_t dν = −ην dt` (e.g. the OU shock),
  `π = wPi(π_T) + χ`, `κx = κ wX(π_T) + λ^f χ − cν` with `χ' = −λ^bχ + cν` is an equilibrium,
  bounded in mean square. The key tool is `expDrift_mul_det`: `E_t d(c_tν_t) = (c' − ηc)ν dt`
  for a piecewise-`C¹` deterministic `c` (no Itô calculus: conditional Fubini and
  `E_sν_r = e^{−η(r−s)}ν_s`);
* non-vacuity on bmPath at the book's calibration: `bmPath_track`.
-/

namespace Cochrane.ZeroBound.TidyR8StochWerningNaturalTrack

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningExist Cochrane.ZeroBound.TidyR7StochWerningNatural
open Cochrane.ZeroBound.TidyR7StochWerningNaturalExist
open Cochrane.ZeroBound.TidyR8StochWerningNaturalMean
open Cochrane.ZeroBound.TidyR8StochWerningMartingale
open Cochrane.ZeroBound.TidyR8StochWerningActiveTrap
open Cochrane.ZeroBound.TidyR7OUPath Cochrane.ZeroBound.TidyR7OrnsteinUhlenbeck
open Cochrane.ZeroBound.TidyR7BrownianTools
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The model -/

/-- Cochrane (2023), §20.2.2, p. 474: the interest rate `0` during the trap and the natural rate
`u_{r,t}` from `T` on. -/
noncomputable def trackRate (T : ℝ) (ur : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if t < T then 0 else ur t ω

/-- Cochrane (2023), (20.5)–(20.6), p. 474, under uncertainty: **an equilibrium when the rate
tracks the random natural rate after the trap**: natural rate `u_r = trapStep u T + ν`, interest
rate `trackRate T u_r`, disturbance `trapStep g T`. -/
def IsStochEqmTrack (σ ρ κ : ℝ) (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (T u g : ℝ)
    (ν x π : ℝ → Ω → ℝ) : Prop :=
  ExpDrift P 𝓕 x (fun r ω => σ * (trackRate T (fun t ω => trapStep u T t + ν t ω) r ω -
      π r ω - (trapStep u T r + ν r ω))) ∧
    ExpDrift P 𝓕 π (fun r ω => ρ * π r ω - κ * (x r ω + trapStep g T r))

/-- Cochrane (2023), §20.2.2, p. 474: the real-rate gap under the tracking rule,
`i − u_r = −(u + ν)` during the trap and `0` after. -/
theorem trackRate_sub (T u : ℝ) (ν : ℝ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    trackRate T (fun t ω => trapStep u T t + ν t ω) r ω - (trapStep u T r + ν r ω) =
      -(trapStep u T r + trapStep 1 T r * ν r ω) := by
  by_cases h : r < T
  · simp only [trackRate, trapStep, h, ↓reduceIte]
    ring
  · simp only [trackRate, trapStep, h, ↓reduceIte]
    ring

/-- Cochrane (2023), (20.8)–(20.10), p. 475, under the tracking rule: the response of the
unstable combination to the natural-rate shock, `c(t) = d(1 − e^{−(λ^f+η)(T−t)⁺})` with
`d = −κσ/(λ^f + η)`: `−κσ∫_t^T e^{−(λ^f+η)(r−t)}dr` during the trap, `0` after. -/
noncomputable def trackD (σ κ ρ η T t : ℝ) : ℝ :=
  natD σ κ ρ η * (1 - Real.exp (-((lamf ρ κ σ + η) * max (T - t) 0)))

/-- Cochrane (2023), (20.8), p. 474: the response kernel of expected inflation,
`K(s,t) = e^{−λt}∫_s^t e^{λr}c(r)e^{−η(r−s)}dr = ∫_s^t e^{−λ(t−r)}c(r)e^{−η(r−s)}dr`.
Generalises `TidyR8StochWerningNaturalMean.natK` (the case `c ≡ 1`). -/
noncomputable def trackK (lam η : ℝ) (c : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (-(lam * t)) * ∫ r in s..t, Real.exp (lam * r) * (c r * Real.exp (-(η * (r - s))))

/-- Cochrane (2023), (20.8), p. 474: `K(s, s) = 0`. -/
theorem trackK_self (lam η : ℝ) (c : ℝ → ℝ) (s : ℝ) : trackK lam η c s s = 0 := by
  simp [trackK]

/-- Cochrane (2023), (20.8), p. 474: `∂_t K(s,t) = −λK(s,t) + c(t)e^{−η(t−s)}` for continuous
`c`.
Generalises `TidyR8StochWerningNaturalMean.hasDerivAt_natK`. -/
theorem hasDerivAt_trackK (lam η : ℝ) {c : ℝ → ℝ} (hc : Continuous c) (s t : ℝ) :
    HasDerivAt (trackK lam η c s) (-lam * trackK lam η c s t +
      c t * Real.exp (-(η * (t - s)))) t := by
  have h1 : HasDerivAt (fun τ => Real.exp (-(lam * τ))) (Real.exp (-(lam * t)) * -lam) t := by
    simpa using ((hasDerivAt_id' t).const_mul lam).neg.exp
  have h2 := ((by fun_prop : Continuous fun r => Real.exp (lam * r) *
    (c r * Real.exp (-(η * (r - s))))).integral_hasStrictDerivAt s t).hasDerivAt
  refine (h1.mul h2).congr_deriv ?_
  have he : Real.exp (-(lam * t)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [trackK]
  linear_combination (c t * Real.exp (-(η * (t - s)))) * he

/-- Cochrane (2023), (20.8), p. 474: `K(s, ·)` is continuous. -/
theorem continuous_trackK (lam η : ℝ) {c : ℝ → ℝ} (hc : Continuous c) (s : ℝ) :
    Continuous (trackK lam η c s) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_trackK lam η hc s t).continuousAt

/-- Cochrane (2023), (20.8), p. 475: `c` is continuous (it vanishes at `T` from both sides). -/
theorem continuous_trackD (σ κ ρ η T : ℝ) : Continuous (trackD σ κ ρ η T) := by
  unfold trackD
  fun_prop

/-- Cochrane (2023), (20.8), p. 475: `c = 0` after the trap. -/
theorem trackD_of_le {σ κ ρ η T t : ℝ} (ht : T ≤ t) : trackD σ κ ρ η T t = 0 := by
  simp [trackD, max_eq_right (by linarith : T - t ≤ 0)]

/-- Cochrane (2023), (20.8), p. 475: `|c| ≤ |d|` (for `λ^f + η ≥ 0`). -/
theorem abs_trackD_le {σ κ ρ η T : ℝ} (hl : 0 ≤ lamf ρ κ σ + η) (t : ℝ) :
    |trackD σ κ ρ η T t| ≤ |natD σ κ ρ η| := by
  unfold trackD
  rw [abs_mul]
  have h1 : 0 < Real.exp (-((lamf ρ κ σ + η) * max (T - t) 0)) := Real.exp_pos _
  have h2 : Real.exp (-((lamf ρ κ σ + η) * max (T - t) 0)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [le_max_right (T - t) 0])
  have : |1 - Real.exp (-((lamf ρ κ σ + η) * max (T - t) 0))| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  exact mul_le_of_le_one_right (abs_nonneg _) this

/-- Cochrane (2023), (20.8)–(20.10), p. 475: **`c' = (λ^f + η)c + κσ·1{t < T}`** off `T`. -/
theorem hasDerivAt_trackD {σ κ ρ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 ≤ η) {T t : ℝ}
    (ht : t ≠ T) :
    HasDerivAt (trackD σ κ ρ η T)
      ((lamf ρ κ σ + η) * trackD σ κ ρ η T t + κ * σ * trapStep 1 T t) t := by
  have hd := natD_eq (ρ := ρ) hσ hκ hη
  rcases lt_or_gt_of_ne ht with h | h
  · have hev : (fun τ => natD σ κ ρ η * (1 - Real.exp (-((lamf ρ κ σ + η) * (T - τ))))) =ᶠ[𝓝 t]
        trackD σ κ ρ η T := by
      filter_upwards [Iio_mem_nhds h] with τ hτ
      simp only [trackD, max_eq_left (by linarith [show τ < T from hτ] : 0 ≤ T - τ)]
    have hD : HasDerivAt (fun τ => natD σ κ ρ η * (1 - Real.exp (-((lamf ρ κ σ + η) * (T - τ)))))
        (natD σ κ ρ η * -(Real.exp (-((lamf ρ κ σ + η) * (T - t))) * (lamf ρ κ σ + η))) t := by
      have h0 : HasDerivAt (fun τ => -((lamf ρ κ σ + η) * (T - τ))) (lamf ρ κ σ + η) t := by
        have e : (fun τ => -((lamf ρ κ σ + η) * (T - τ))) =
            fun τ => (lamf ρ κ σ + η) * τ - (lamf ρ κ σ + η) * T := by
          funext τ; ring
        rw [e]
        simpa using ((hasDerivAt_id t).const_mul (lamf ρ κ σ + η)).sub_const
          ((lamf ρ κ σ + η) * T)
      exact ((hasDerivAt_const t (1 : ℝ)).sub h0.exp).const_mul _ |>.congr_deriv (by ring)
    refine (hD.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp only [trackD, max_eq_left (by linarith : 0 ≤ T - t), trapStep, h, ↓reduceIte]
    linear_combination -hd
  · have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 t] trackD σ κ ρ η T := by
      filter_upwards [Ioi_mem_nhds h] with τ hτ
      exact (trackD_of_le (le_of_lt hτ)).symm
    refine ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev.symm).congr_deriv ?_
    simp [trackD_of_le h.le, trapStep, not_lt.2 h.le]

/-! ## `E_t d(c_tν_t)` for a deterministic `c` -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): Fubini with a bounded measurable weight,
`∫_A ∫_s^t w(r)Z_r dr = ∫_s^t w(r)∫_A Z_r dr`, for a process with continuous paths, measurable
time sections and bounded first moments.
Generalises `TidyR8StochWerningMartingale.setIntegral_intervalIntegral_swap` (the case `w ≡ 1`). -/
theorem setIntegral_swap_weight [IsFiniteMeasure P] {Z : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Z t ω) (hm : ∀ t, Measurable (Z t)) {K : ℝ}
    (hK : ∀ t, 0 ≤ t → Integrable (Z t) P ∧ ∫ ω, |Z t ω| ∂P ≤ K) {w : ℝ → ℝ}
    (hw : Measurable w) {C : ℝ} (hwC : ∀ r, |w r| ≤ C) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) :
    Integrable (fun ω => ∫ r in s..t, w r * Z r ω) P ∧
    ∫ ω in A, (∫ r in s..t, w r * Z r ω) ∂P = ∫ r in s..t, w r * ∫ ω in A, Z r ω ∂P := by
  have hZp := integrable_prod_proc (P := P) hc hm hK hs (b := t)
  have hD : Integrable (Function.uncurry fun r ω => w r * Z r ω)
      ((volume.restrict (Set.Ioc s t)).prod P) :=
    hZp.bdd_mul (hw.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hwC p.1)
  refine ⟨?_, ?_⟩
  · refine hD.integral_prod_right.congr (Eventually.of_forall fun ω => ?_)
    simp only [Function.uncurry_apply_pair, intervalIntegral.integral_of_le hst]
  simp only [intervalIntegral.integral_of_le hst]
  have hDA : Integrable (Function.uncurry fun r ω => w r * Z r ω)
      ((volume.restrict (Set.Ioc s t)).prod (P.restrict A)) := by
    have he : (volume.restrict (Set.Ioc s t)).prod (P.restrict A)
        = ((volume.restrict (Set.Ioc s t)).prod P).restrict (Set.univ ×ˢ A) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [he]
    exact hD.restrict
  have := (integral_integral_swap hDA).symm
  rw [this]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [integral_const_mul]

/-- **Cochrane (2023), §20.2.2, p. 474 (tool): `E_t d(c_tν_t) = (c'_t − ηc_t)ν_t dt`** for
`η ≥ 0`, a continuous, bounded deterministic `c`, differentiable off a countable set with
bounded measurable derivative `c'`, and a regular `L¹`-bounded `ν` with `E_t dν = −ην dt`,
on any filtration. -/
theorem expDrift_mul_det [IsProbabilityMeasure P] {η : ℝ} (hη : 0 ≤ η)
    {𝓕 : Filtration ℝ mΩ}
    {ν : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν) (hνb : BddL1 P ν)
    (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) {c c' : ℝ → ℝ} (hcc : Continuous c)
    {S : Set ℝ} (hS : S.Countable) (hcd : ∀ r, r ∉ S → HasDerivAt c (c' r) r)
    (hc'm : Measurable c') {C : ℝ} (hcC : ∀ r, |c r| ≤ C) (hc'C : ∀ r, |c' r| ≤ C) :
    ExpDrift P 𝓕 (fun t ω => c t * ν t ω) (fun r ω => (c' r - η * c r) * ν r ω) := by
  obtain ⟨Kν, hKν⟩ := hνb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  have hwm : Measurable fun r => c' r - η * c r := hc'm.sub (hcc.measurable.const_mul η)
  have hwC : ∀ r, |c' r - η * c r| ≤ C + |η| * C := fun r => by
    calc |c' r - η * c r| ≤ |c' r| + |η * c r| := abs_sub _ _
      _ ≤ C + |η| * C := by
          rw [abs_mul]
          exact add_le_add (hc'C r) (mul_le_mul_of_nonneg_left (hcC r) (abs_nonneg η))
  intro s t hs hst
  obtain ⟨hI, -⟩ := setIntegral_swap_weight hν.1 hmν hKν hwm hwC hs hst Set.univ
  have hB : Integrable (fun ω => c t * ν t ω - c s * ν s ω -
      ∫ r in s..t, (c' r - η * c r) * ν r ω) P :=
    (((hKν t (hs.trans hst)).1.const_mul _).sub ((hKν s hs).1.const_mul _)).sub hI
  refine ⟨hB, ?_⟩
  have h0 : (fun _ => (0 : ℝ)) =ᵐ[P] P[fun ω => c t * ν t ω - c s * ν s ω -
      ∫ r in s..t, (c' r - η * c r) * ν r ω | 𝓕 s] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hB (fun _ _ _ => integrableOn_const
      (by simp)) (fun A hA _ => ?_) stronglyMeasurable_const.aestronglyMeasurable
    obtain ⟨-, hsw⟩ := setIntegral_swap_weight hν.1 hmν hKν hwm hwC hs hst A
    have hnu : ∀ r, s ≤ r → ∫ ω in A, ν r ω ∂P = Real.exp (-η * (r - s)) * ∫ ω in A, ν s ω ∂P :=
      fun r hr => setIntegral_nu hν ⟨Kν, hKν⟩ hνd hs hA hr
    have hint : ∫ r in s..t, (c' r - η * c r) * ∫ ω in A, ν r ω ∂P =
        (∫ r in s..t, (c' r - η * c r) * Real.exp (-η * (r - s))) * ∫ ω in A, ν s ω ∂P := by
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hst] at hr
      rw [hnu r hr.1]
      ring
    -- the FTC for `φ(r) = c(r)e^{−η(r−s)}`
    have hφ : ∫ r in s..t, (c' r - η * c r) * Real.exp (-η * (r - s)) =
        c t * Real.exp (-η * (t - s)) - c s * Real.exp (-η * (s - s)) := by
      refine integral_eq_of_hasDerivAt_off_countable_of_le
        (fun r => c r * Real.exp (-η * (r - s))) _ hst hS
        ((hcc.mul (by fun_prop : Continuous fun r => Real.exp (-η * (r - s)))).continuousOn)
        (fun r hr => ?_) ?_
      · have he : HasDerivAt (fun r => Real.exp (-η * (r - s)))
            (Real.exp (-η * (r - s)) * -η) r := by
          simpa using (((hasDerivAt_id' r).sub_const s).const_mul (-η)).exp
        exact ((hcd r hr.2).mul he).congr_deriv (by ring)
      · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
          (Measure.integrableOn_of_bounded (M := (C + |η| * C) * 1) measure_Ioc_lt_top.ne
          (hwm.mul (by fun_prop : Continuous fun r => Real.exp (-η * (r - s))).measurable
            ).aestronglyMeasurable ?_)
        refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
        change ‖(c' r - η * c r) * Real.exp (-η * (r - s))‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul (hwC r) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hwC r))
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        have := mul_nonneg hη (sub_nonneg.2 hr.1.le)
        linarith
    have i1 : Integrable (fun ω => c t * ν t ω - c s * ν s ω) (P.restrict A) :=
      (((hKν t (hs.trans hst)).1.const_mul _).sub ((hKν s hs).1.const_mul _)).integrableOn
    have i2 : Integrable (fun ω => ∫ r in s..t, (c' r - η * c r) * ν r ω) (P.restrict A) :=
      hI.integrableOn
    have i3 : Integrable (fun ω => c t * ν t ω) (P.restrict A) :=
      ((hKν t (hs.trans hst)).1.const_mul _).integrableOn
    have i4 : Integrable (fun ω => c s * ν s ω) (P.restrict A) :=
      ((hKν s hs).1.const_mul _).integrableOn
    rw [integral_sub i1 i2, integral_sub i3 i4, integral_const_mul, integral_const_mul, hsw,
      hint, hφ, hnu t hst]
    simp only [integral_zero, sub_self, mul_zero, Real.exp_zero, mul_one]
    ring
  exact h0.symm

/-! ## The unstable combination and expected inflation -/

/-- Cochrane (2023), (20.5), p. 474 (tool): under the tracking rule the IS curve has the drift
`σ(0 − π − (u + 1{t<T}ν))`. -/
theorem expDrift_x_track {σ ρ κ : ℝ} {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ}
    (h : IsStochEqmTrack σ ρ κ P 𝓕 T u g ν x π) :
    ExpDrift P 𝓕 x (fun r ω => σ * (0 - π r ω - (trapStep u T r + trapStep 1 T r * ν r ω))) :=
  expDrift_of_ae_eq h.1 (Eventually.of_forall fun ω r _ => by
    have := trackRate_sub T u ν r ω
    linear_combination σ * this)

/-- Cochrane (2023), (20.5)–(20.6), p. 474, under the tracking rule: **the conditional means
solve the deterministic model** with the natural-rate forcing `1{t<T}∫_A ν_t`: for `A ∈ 𝓕_s`,
`t ≥ s ≥ 0`, the integral forms of `∫_A x`, `∫_A π` and `∫_A ν`.
The analogue of `TidyR7StochWerning.condMean_integral_eq`. -/
theorem track_mean_forms [IsProbabilityMeasure P] {σ ρ κ η : ℝ} {𝓕 : Filtration ℝ mΩ}
    {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν) (hνb : BddL1 P ν)
    (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π) (h : IsStochEqmTrack σ ρ κ P 𝓕 T u g ν x π) {s : ℝ}
    (hs : 0 ≤ s) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) (t : ℝ) (hst : s ≤ t) :
    ∫ ω in A, x t ω ∂P - ∫ ω in A, x s ω ∂P = ∫ r in s..t, σ * (P.real A * 0 -
        ∫ ω in A, π r ω ∂P - (P.real A * trapStep u T r + trapStep 1 T r * ∫ ω in A, ν r ω ∂P)) ∧
      ∫ ω in A, π t ω ∂P - ∫ ω in A, π s ω ∂P = ∫ r in s..t, (ρ * ∫ ω in A, π r ω ∂P -
        κ * (∫ ω in A, x r ω ∂P + P.real A * trapStep g T r)) ∧
      ∫ ω in A, ν t ω ∂P - ∫ ω in A, ν s ω ∂P = ∫ r in s..t, -(η * ∫ ω in A, ν r ω ∂P) := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have pν := integrable_prod_proc (P := P) hν.1 hmν hKν hs (b := t)
  have px := integrable_prod_proc (P := P) hx.1 hmx hKx hs (b := t)
  have pπ := integrable_prod_proc (P := P) hπ.1 hmπ hKπ hs (b := t)
  have p0 := integrable_prod_det (P := P) (integrableOn_zero (s := Set.Ioc s t))
  have pu := integrable_prod_det (P := P) (trapStep_integrableOn u T (S := Set.Ioc s t)
    measure_Ioc_lt_top.ne)
  have pg := integrable_prod_det (P := P) (trapStep_integrableOn g T (S := Set.Ioc s t)
    measure_Ioc_lt_top.ne)
  have phν : Integrable (fun p : ℝ × Ω => trapStep 1 T p.1 * Function.uncurry ν p)
      ((volume.restrict (Set.Ioc s t)).prod P) :=
    pν.bdd_mul ((trapStep_measurable 1 T).comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; simpa using trapStep_abs_le 1 T p.1)
  refine ⟨?_, ?_, ?_⟩
  · rw [setIntegral_expDrift (expDrift_x_track h) hs hst hA (hKx s hs).1
      (hKx t (hs.trans hst)).1 (((p0.sub pπ).sub (pu.add phν)).const_mul σ)]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 ≤ r := hs.trans (by rw [Set.uIcc_of_le hst] at hr; exact hr.1)
    calc ∫ ω in A, σ * (0 - π r ω - (trapStep u T r + trapStep 1 T r * ν r ω)) ∂P
        = ∫ ω in A, (σ * (0 - trapStep u T r) + (-σ) * π r ω +
            (-(σ * trapStep 1 T r)) * ν r ω) ∂P := by
          congr 1; funext ω; ring
      _ = _ := setIntegral_affine (hKπ r hr0).1 (hKν r hr0).1 _ _ _ A
      _ = _ := by ring
  · rw [setIntegral_expDrift h.2 hs hst hA (hKπ s hs).1 (hKπ t (hs.trans hst)).1
      ((pπ.const_mul ρ).sub ((px.add pg).const_mul κ))]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 ≤ r := hs.trans (by rw [Set.uIcc_of_le hst] at hr; exact hr.1)
    calc ∫ ω in A, (ρ * π r ω - κ * (x r ω + trapStep g T r)) ∂P
        = ∫ ω in A, (-(κ * trapStep g T r) + ρ * π r ω + (-κ) * x r ω) ∂P := by
          congr 1; funext ω; ring
      _ = _ := setIntegral_affine (hKπ r hr0).1 (hKx r hr0).1 _ _ _ A
      _ = _ := by ring
  · rw [setIntegral_expDrift hνd hs hst hA (hKν s hs).1 (hKν t (hs.trans hst)).1
      (pν.const_mul η).neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [integral_neg, integral_const_mul]

/-- **Cochrane (2023), (20.8)–(20.10), p. 475, with the rate tracking the natural rate after the
trap: the unstable combination is pinned state by state.** Let `ν` be a regular `L¹`-bounded
shock with `E_t dν = −ην dt` (`η ≥ 0`) and `(x, π)` a regular `L¹`-bounded equilibrium of
`IsStochEqmTrack`. Then for every `s ≥ 0`, almost surely,
`λ^f π_s − κ x_s = (λ^f wPi(0)_s − κ wX(0)_s) + c(s) ν_s` with `c = trackD`
(`c(s) = 0` for `s ≥ T`).
The analogue, under the tracking rule, of `TidyR7StochWerningNatural.unstable_natural`. -/
theorem unstable_track [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν)
    (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqmTrack σ ρ κ P 𝓕 T u g ν x π) {s : ℝ} (hs : 0 ≤ s) :
    (fun ω => lamf ρ κ σ * π s ω - κ * x s ω) =ᵐ[P] fun ω =>
      (lamf ρ κ σ * wPi σ κ ρ T u g 0 s - κ * wX σ κ ρ T u g 0 s) +
        trackD σ κ ρ η T s * ν s ω := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hroot := lamf_root (ρ := ρ) hκ hσ
  set lf := lamf ρ κ σ
  set c := trackD σ κ ρ η T
  set d := natD σ κ ρ η
  have hcd : ∀ t, |c t| ≤ |d| := abs_trackD_le (by linarith)
  have key : ∀ A, MeasurableSet[𝓕 s] A →
      ∫ ω in A, (lf * π s ω - κ * x s ω) ∂P =
        ∫ ω in A, ((lf * (wPi σ κ ρ T u g 0) s - κ * (wX σ κ ρ T u g 0) s) + c s * ν s ω) ∂P := by
    intro A hA
    set p := P.real A
    set mx : ℝ → ℝ := fun r => ∫ ω in A, x r ω ∂P
    set mπ : ℝ → ℝ := fun r => ∫ ω in A, π r ω ∂P
    set mν : ℝ → ℝ := fun r => ∫ ω in A, ν r ω ∂P
    have hbν : ∀ r, 0 ≤ r → |mν r| ≤ Kν := fun r hr => abs_setIntegral_le hKν A hr
    have hix := integrableOn_setIntegral hx.1 hmx hKx A hs
    have hiπ := integrableOn_setIntegral hπ.1 hmπ hKπ A hs
    have hiν := integrableOn_setIntegral hν.1 hmν hKν A hs
    have itr : ∀ a b, IntegrableOn (trapStep a T) (Set.Icc s b) := fun a b =>
      trapStep_integrableOn a T measure_Icc_lt_top.ne
    have hcm := fun t (ht : s ≤ t) => track_mean_forms (P := P) hν ⟨Kν, hKν⟩ hνd hx ⟨Kx, hKx⟩
      hπ ⟨Kπ, hKπ⟩ h hs hA t ht
    have hGx : ∀ b, IntegrableOn (fun r => σ * (p * 0 - mπ r - (p * trapStep u T r +
        trapStep 1 T r * mν r))) (Set.Icc s b) := fun b =>
      (((integrableOn_const (by simp)).sub (hiπ b)).sub (((itr u b).const_mul p).add
        ((hiν b).bdd_mul (trapStep_measurable 1 T).aestronglyMeasurable
          (Eventually.of_forall fun r => by
            rw [Real.norm_eq_abs]; simpa using trapStep_abs_le 1 T r)))).const_mul σ
    have hGπ : ∀ b, IntegrableOn (fun r => ρ * mπ r - κ * (mx r + p * trapStep g T r))
        (Set.Icc s b) := fun b =>
      ((hiπ b).const_mul ρ).sub (((hix b).add ((itr g b).const_mul p)).const_mul κ)
    have hcx : ContinuousOn mx (Set.Ici s) :=
      continuousOn_of_intForm hGx fun t ht => (hcm t ht).1
    have hcπ : ContinuousOn mπ (Set.Ici s) :=
      continuousOn_of_intForm hGπ fun t ht => (hcm t ht).2.1
    have hcν : ContinuousOn mν (Set.Ici s) :=
      continuousOn_of_intForm (fun b => ((hiν b).const_mul η).neg) fun t ht => (hcm t ht).2.2
    have hW0c := wPi_continuous σ κ ρ T u g 0 hκ hσ
    have hX0c := wX_continuous σ κ ρ T u g 0 hκ hσ
    obtain ⟨⟨KX, hKX⟩, ⟨KW, hKW⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g 0
    have hp := wPath_isPath (ρ := ρ) hκ hσ T u g 0
    set F : ℝ → ℝ := fun r => lf * mπ r - κ * mx r -
      p * (lf * (wPi σ κ ρ T u g 0) r - κ * (wX σ κ ρ T u g 0) r) - c r * mν r with hFdef
    have hFc : ContinuousOn F (Set.Ici s) :=
      (((continuousOn_const.mul hcπ).sub (continuousOn_const.mul hcx)).sub
        (continuousOn_const.mul ((continuousOn_const.mul hW0c.continuousOn).sub
          (continuousOn_const.mul hX0c.continuousOn)))).sub
        ((continuous_trackD σ κ ρ η T).continuousOn.mul hcν)
    have hFd : ∀ t, s < t → t ∉ ({T} : Set ℝ) → HasDerivAt F (lf * F t) t := by
      intro t ht htT
      have htT' : t ≠ T := htT
      have ca : ∀ {m : ℝ → ℝ}, ContinuousOn m (Set.Ici s) → ContinuousAt m t := fun hm =>
        hm.continuousAt (Ici_mem_nhds ht)
      have dx := TidyR7StochWerningNatural.hasDerivAt_of_intForm_at hGx
        (fun t ht => (hcm t ht).1) ht
        (((continuousAt_const.sub (ca hcπ)).sub (((trapStep_continuousAt u htT').const_mul
          p).add ((trapStep_continuousAt 1 htT').mul (ca hcν)))).const_mul σ)
      have dπ := TidyR7StochWerningNatural.hasDerivAt_of_intForm_at hGπ
        (fun t ht => (hcm t ht).2.1) ht
        (((ca hcπ).const_mul ρ).sub (((ca hcx).add ((trapStep_continuousAt g htT').const_mul
          p)).const_mul κ))
      have dν : HasDerivAt mν (-(η * mν t)) t :=
        TidyR7StochWerningNatural.hasDerivAt_of_intForm_at
          (fun b => ((hiν b).const_mul η).neg) (fun t ht => (hcm t ht).2.2) ht
          ((ca hcν).const_mul η).neg
      have dc := hasDerivAt_trackD (ρ := ρ) hσ hκ hη htT'
      obtain ⟨dX, dW⟩ := hp.2.2 t (hs.trans_lt ht) htT
      refine (((((dπ.const_mul lf).sub (dx.const_mul κ)).sub
        (((dW.const_mul lf).sub (dX.const_mul κ)).const_mul p)).sub
          (dc.mul dν))).congr_deriv ?_
      simp only [F]
      linear_combination (-(mπ t - p * (wPi σ κ ρ T u g 0) t)) * hroot
    have hzero := unstable_bdd_zero (f := F) (a := lf) (p := s) (S := {T})
      (K := lf * Kπ + κ * Kx + |p| * (lf * KW + κ * KX) + |d| * Kν)
      hf (Set.countable_singleton T) hFc hFd
      (fun t ht => by
        have h1 := hKW t (hs.trans ht)
        have h2 := hKX t (hs.trans ht)
        have b1 := abs_setIntegral_le hKπ A (hs.trans ht)
        have b2 := abs_setIntegral_le hKx A (hs.trans ht)
        have b3 := hbν t (hs.trans ht)
        have b4 := hcd t
        have habs : ∀ a b e f k : ℝ, |lf * a - κ * b - p * (lf * e - κ * f) - c t * k| ≤
            lf * |a| + κ * |b| + |p| * (lf * |e| + κ * |f|) + |c t| * |k| := by
          intro a b e f k
          have e1 := abs_sub (lf * a - κ * b - p * (lf * e - κ * f)) (c t * k)
          have e2 := abs_sub (lf * a - κ * b) (p * (lf * e - κ * f))
          have e3 := abs_sub (lf * a) (κ * b)
          have e4 := abs_sub (lf * e) (κ * f)
          rw [abs_mul p, abs_mul (c t)] at *
          rw [abs_mul lf, abs_mul κ, abs_of_pos hf, abs_of_pos hκ] at e3
          rw [abs_mul lf, abs_mul κ, abs_of_pos hf, abs_of_pos hκ] at e4
          have e5 := mul_le_mul_of_nonneg_left e4 (abs_nonneg p)
          linarith
        refine (habs _ _ _ _ _).trans ?_
        have : |c t| * |mν t| ≤ |d| * Kν :=
          mul_le_mul b4 b3 (abs_nonneg _) (abs_nonneg _)
        gcongr)
      s le_rfl
    have e2 : F s = 0 := hzero
    simp only [F] at e2
    rw [integral_sub ((hKπ s hs).1.integrableOn.const_mul lf)
        ((hKx s hs).1.integrableOn.const_mul κ),
      integral_add (integrable_const _) ((hKν s hs).1.integrableOn.const_mul (c s)),
      integral_const_mul, integral_const_mul, integral_const_mul, setIntegral_const, smul_eq_mul]
    linarith
  have hYm : StronglyMeasurable[𝓕 s] fun ω => lf * π s ω - κ * x s ω :=
    (stronglyMeasurable_const.mul (hπ.2 s)).sub (stronglyMeasurable_const.mul (hx.2 s))
  have hYi : Integrable (fun ω => lf * π s ω - κ * x s ω) P :=
    ((hKπ s hs).1.const_mul lf).sub ((hKx s hs).1.const_mul κ)
  have hZi : Integrable
      (fun ω => (lf * (wPi σ κ ρ T u g 0) s - κ * (wX σ κ ρ T u g 0) s) + c s * ν s ω) P :=
    (integrable_const _).add ((hKν s hs).1.const_mul (c s))
  have h1 : (fun ω => (lf * (wPi σ κ ρ T u g 0) s - κ * (wX σ κ ρ T u g 0) s) + c s * ν s ω)
      =ᵐ[P] P[fun ω => lf * π s ω - κ * x s ω | 𝓕 s] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hYi (fun _ _ _ => hZi.integrableOn)
      (fun A hA _ => (key A hA).symm)
      (stronglyMeasurable_const.add (stronglyMeasurable_const.mul (hν.2 s))).aestronglyMeasurable
  rw [condExp_of_stronglyMeasurable (𝓕.le s) hYm hYi] at h1
  exact h1.symm

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475, under the tracking rule: **conditional means
of inflation.** For `A ∈ 𝓕_s` and `t ≥ s ≥ 0`, `∫_A π_t = P(A)wPi(0)_t +
e^{−λ^b(t−s)}(∫_A π_s − P(A)wPi(0)_s) + K(s,t)∫_A ν_s` with `K = trackK λ^b η c`. -/
theorem setIntegral_pi_track [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν)
    (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqmTrack σ ρ κ P 𝓕 T u g ν x π) {s : ℝ} (hs : 0 ≤ s) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) {t : ℝ} (hst : s ≤ t) :
    ∫ ω in A, π t ω ∂P = P.real A * wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (∫ ω in A, π s ω ∂P - P.real A * wPi σ κ ρ T u g 0 s) +
      trackK (lamb ρ κ σ) η (trackD σ κ ρ η T) s t * ∫ ω in A, ν s ω ∂P := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have hsub := lamf_sub_lamb ρ κ σ
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  set c := trackD σ κ ρ η T
  set p := P.real A
  set mx : ℝ → ℝ := fun r => ∫ ω in A, x r ω ∂P
  set mπ : ℝ → ℝ := fun r => ∫ ω in A, π r ω ∂P
  set mν : ℝ → ℝ := fun r => ∫ ω in A, ν r ω ∂P
  set W0 := wPi σ κ ρ T u g 0
  set X0 := wX σ κ ρ T u g 0
  have hix := integrableOn_setIntegral hx.1 hmx hKx A hs
  have hiπ := integrableOn_setIntegral hπ.1 hmπ hKπ A hs
  have itr : ∀ a b, IntegrableOn (trapStep a T) (Set.Icc s b) := fun a b =>
    trapStep_integrableOn a T measure_Icc_lt_top.ne
  have hcm := fun t (ht : s ≤ t) => track_mean_forms (P := P) hν ⟨Kν, hKν⟩ hνd hx ⟨Kx, hKx⟩
    hπ ⟨Kπ, hKπ⟩ h hs hA t ht
  have hGπ : ∀ b, IntegrableOn (fun r => ρ * mπ r - κ * (mx r + p * trapStep g T r))
      (Set.Icc s b) := fun b =>
    ((hiπ b).const_mul ρ).sub (((hix b).add ((itr g b).const_mul p)).const_mul κ)
  have hiν := integrableOn_setIntegral hν.1 hmν hKν A hs
  have hGx : ∀ b, IntegrableOn (fun r => σ * (p * 0 - mπ r - (p * trapStep u T r +
      trapStep 1 T r * mν r))) (Set.Icc s b) := fun b =>
    (((integrableOn_const (by simp)).sub (hiπ b)).sub (((itr u b).const_mul p).add
      ((hiν b).bdd_mul (trapStep_measurable 1 T).aestronglyMeasurable
        (Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs]; simpa using trapStep_abs_le 1 T r)))).const_mul σ
  have hcx : ContinuousOn mx (Set.Ici s) := continuousOn_of_intForm hGx fun t ht => (hcm t ht).1
  have hcπ : ContinuousOn mπ (Set.Ici s) :=
    continuousOn_of_intForm hGπ fun t ht => (hcm t ht).2.1
  have hun : ∀ r, s ≤ r → lf * mπ r - κ * mx r = p * (lf * W0 r - κ * X0 r) + c r * mν r := by
    intro r hr
    have hr0 := hs.trans hr
    have e := integral_congr_ae (μ := P.restrict A) (ae_restrict_of_ae
      (unstable_track hσ hκ hη hν ⟨Kν, hKν⟩ hνd hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hr0))
    rw [integral_sub ((hKπ r hr0).1.integrableOn.const_mul lf)
        ((hKx r hr0).1.integrableOn.const_mul κ),
      integral_add (integrable_const _) ((hKν r hr0).1.integrableOn.const_mul (c r)),
      integral_const_mul, integral_const_mul, integral_const_mul, setIntegral_const,
      smul_eq_mul] at e
    simp only [mx, mπ, mν, W0, X0, p, lf, c]
    linarith
  have hnu : ∀ r, s ≤ r → mν r = Real.exp (-η * (r - s)) * mν s := fun r hr =>
    setIntegral_nu hν ⟨Kν, hKν⟩ hνd hs hA hr
  have hp := wPath_isPath (ρ := ρ) hκ hσ T u g 0
  have hcc := continuous_trackD σ κ ρ η T
  set G : ℝ → ℝ := fun r => mπ r - p * W0 r - mν s * trackK lb η c s r with hGdef
  have hGc : ContinuousOn G (Set.Ici s) :=
    (hcπ.sub (continuousOn_const.mul (wPi_continuous σ κ ρ T u g 0 hκ hσ).continuousOn)).sub
      (continuousOn_const.mul (continuous_trackK lb η hcc s).continuousOn)
  have hGd : ∀ r, s < r → r ∉ ({T} : Set ℝ) → HasDerivAt G (-lb * G r) r := by
    intro r hr hrT
    have hrT' : r ≠ T := hrT
    have ca : ∀ {m : ℝ → ℝ}, ContinuousOn m (Set.Ici s) → ContinuousAt m r := fun hm =>
      hm.continuousAt (Ici_mem_nhds hr)
    have dπ := TidyR7StochWerningNatural.hasDerivAt_of_intForm_at hGπ
      (fun t ht => (hcm t ht).2.1) hr (((ca hcπ).const_mul ρ).sub (((ca hcx).add
        ((trapStep_continuousAt g hrT').const_mul p)).const_mul κ))
    have dW := (hp.2.2 r (hs.trans_lt hr) hrT).2
    have dk := hasDerivAt_trackK lb η hcc s r
    refine ((dπ.sub (dW.const_mul p)).sub (dk.const_mul (mν s))).congr_deriv ?_
    have h1 := hun r hr.le
    have h2 := hnu r hr.le
    have he : Real.exp (-η * (r - s)) = Real.exp (-(η * (r - s))) := by ring_nf
    rw [he] at h2
    simp only [G]
    linear_combination h1 - (mπ r - p * W0 r) * hsub + c r * h2
  have hsol := linear_ode_Ici (Set.countable_singleton T) hGc hGd t hst
  simp only [G, trackK_self, mul_zero, sub_zero] at hsol
  have he : Real.exp (-lb * (t - s)) = Real.exp (-(lb * (t - s))) := by ring_nf
  rw [he] at hsol
  change mπ t = _
  linarith

/-- **Cochrane (2023), (20.8)–(20.10), pp. 474–475, §20.2.4, p. 479, under the tracking rule:
expected inflation.** In every regular `L¹`-bounded equilibrium of `IsStochEqmTrack`,
`E_s π_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s) + K(s,t) ν_s` almost surely for
`t ≥ s ≥ 0`, with `K(s,t) = ∫_s^t e^{−λ^b(t−r)}c(r)e^{−η(r−s)}dr` (`trackK`, `c = trackD`); news
about the natural rate matters only through its expected path during the remaining trap. -/
theorem condExp_pi_track [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν)
    (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqmTrack σ ρ κ P 𝓕 T u g ν x π) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[π t | 𝓕 s] =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
      trackK (lamb ρ κ σ) η (trackD σ κ ρ η T) s t * ν s ω := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hπs := (hKπ s hs).1
  have hνs := (hKν s hs).1
  have hint : Integrable (fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
      trackK (lamb ρ κ σ) η (trackD σ κ ρ η T) s t * ν s ω) P :=
    ((integrable_const _).add ((hπs.sub (integrable_const _)).const_mul _)).add
      (hνs.const_mul _)
  have h1 : (fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
      trackK (lamb ρ κ σ) η (trackD σ κ ρ η T) s t * ν s ω) =ᵐ[P] P[π t | 𝓕 s] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hKπ t (hs.trans hst)).1
      (fun _ _ _ => hint.integrableOn)
      (fun A hA _ => by
        calc ∫ ω in A, (wPi σ κ ρ T u g 0 t +
              Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
              trackK (lamb ρ κ σ) η (trackD σ κ ρ η T) s t * ν s ω) ∂P
            = ∫ ω in A, ((wPi σ κ ρ T u g 0 t - Real.exp (-(lamb ρ κ σ * (t - s))) *
                wPi σ κ ρ T u g 0 s) + Real.exp (-(lamb ρ κ σ * (t - s))) * π s ω +
              trackK (lamb ρ κ σ) η (trackD σ κ ρ η T) s t * ν s ω) ∂P := by
                congr 1; funext ω; ring
          _ = _ := setIntegral_affine hπs hνs _ _ _ A
          _ = ∫ ω in A, π t ω ∂P := by
                rw [setIntegral_pi_track hσ hκ hη hν ⟨Kν, hKν⟩ hνd hx hxb hπ ⟨Kπ, hKπ⟩ h hs
                  hA hst]
                ring)
      ((stronglyMeasurable_const.add (stronglyMeasurable_const.mul ((hπ.2 s).sub
        stronglyMeasurable_const))).add
          (stronglyMeasurable_const.mul (hν.2 s))).aestronglyMeasurable
  exact h1.symm

/-! ## Existence -/

/-- Cochrane (2023), (20.8), p. 474, under the tracking rule: the stable-direction response
`χ' = −λ^bχ + c ν`, `χ_0 = 0` (`chiProc`). -/
noncomputable def trackChi (σ κ ρ η T : ℝ) (ν : ℝ → Ω → ℝ) : ℝ → Ω → ℝ :=
  chiProc (lamb ρ κ σ) (fun t ω => trackD σ κ ρ η T t * ν t ω)

/-- Cochrane (2023), (20.8), p. 474, under the tracking rule: inflation `wPi(π_T) + χ`. -/
noncomputable def trackPi (σ κ ρ η T u g πT : ℝ) (ν : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wPi σ κ ρ T u g πT t + trackChi σ κ ρ η T ν t ω

/-- Cochrane (2023), (20.10), p. 475, under the tracking rule: output
`wX(π_T) + (λ^f/κ)χ − cν/κ`, so that `λ^f π − κx = λ^f wPi − κ wX + cν`. -/
noncomputable def trackX (σ κ ρ η T u g πT : ℝ) (ν : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wX σ κ ρ T u g πT t + lamf ρ κ σ / κ * trackChi σ κ ρ η T ν t ω -
    trackD σ κ ρ η T t * ν t ω / κ

/-- **Cochrane (2023), (20.5)–(20.6), p. 474, under the tracking rule: existence.** On any
filtration, for a regular `L¹`-bounded shock with `E_t dν = −ην dt` (`η ≥ 0`), the processes
`(trackX, trackPi)` are a stochastic equilibrium of `IsStochEqmTrack` for every `π_T`. -/
theorem isStochEqmTrack_trackPi [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} (T u g πT : ℝ) {ν : ℝ → Ω → ℝ}
    (hν : Regular 𝓕 ν) (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) :
    IsStochEqmTrack σ ρ κ P 𝓕 T u g ν (trackX σ κ ρ η T u g πT ν)
      (trackPi σ κ ρ η T u g πT ν) := by
  have hsub := lamf_sub_lamb ρ κ σ
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hκ0 := hκ.ne'
  have hc : lamf ρ κ σ / κ * lamb ρ κ σ = σ := by
    have := lamf_mul_lamb (ρ := ρ) hκ hσ
    field_simp
    linarith
  have hlη : 0 ≤ lamf ρ κ σ + η := by linarith
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  have hWc := wPi_continuous σ κ ρ T u g πT hκ hσ
  have hXc := wX_continuous σ κ ρ T u g πT hκ hσ
  have key : ∀ (c : ℝ → ℝ), Continuous c → (∀ r, r ≠ T → HasDerivAt c
      ((lamf ρ κ σ + η) * c r + κ * σ * trapStep 1 T r) r) → (∀ r, |c r| ≤ |natD σ κ ρ η|) →
      IsStochEqmTrack σ ρ κ P 𝓕 T u g ν
        (fun t ω => wX σ κ ρ T u g πT t + lamf ρ κ σ / κ *
          chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) t ω - c t * ν t ω / κ)
        (fun t ω => wPi σ κ ρ T u g πT t + chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) t ω) := by
    intro c hcc hcd hcb
    have hZc : ∀ ω, Continuous fun t => c t * ν t ω := fun ω => hcc.mul (hν.1 ω)
    have hχc : ∀ ω, Continuous fun r => chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω :=
      fun ω => continuous_iff_continuousAt.2 fun r =>
        (hasDerivAt_chiProc hZc (lamb ρ κ σ) ω r).continuousAt
    set C := |natD σ κ ρ η| * (1 + (lamf ρ κ σ + η)) + κ * σ
    have hcC : ∀ r, |c r| ≤ C := fun r => by
      have := hcb r
      have : 0 ≤ |natD σ κ ρ η| * (lamf ρ κ σ + η) := mul_nonneg (abs_nonneg _) hlη
      nlinarith
    have hc'C : ∀ r, |(lamf ρ κ σ + η) * c r + κ * σ * trapStep 1 T r| ≤ C := fun r => by
      calc |(lamf ρ κ σ + η) * c r + κ * σ * trapStep 1 T r|
          ≤ |(lamf ρ κ σ + η) * c r| + |κ * σ * trapStep 1 T r| := abs_add_le _ _
        _ ≤ (lamf ρ κ σ + η) * |natD σ κ ρ η| + κ * σ * 1 := by
            rw [abs_mul, abs_mul, abs_of_nonneg hlη, abs_of_pos hκσ]
            exact add_le_add (mul_le_mul_of_nonneg_left (hcb r) hlη)
              (mul_le_mul_of_nonneg_left (by simpa using trapStep_abs_le 1 T r) hκσ.le)
        _ ≤ C := by nlinarith [abs_nonneg (natD σ κ ρ η)]
    have hcν := expDrift_mul_det (c' := fun r => (lamf ρ κ σ + η) * c r +
        κ * σ * trapStep 1 T r) hη hν hνb hνd hcc (Set.countable_singleton T)
      (fun r hr => hcd r hr)
      ((hcc.measurable.const_mul _).add ((trapStep_measurable 1 T).const_mul _)) hcC hc'C
    refine ⟨expDrift_of_bracket_eq hcν (-1 / κ) fun s t hs hst ω => ?_,
      expDrift_of_bracket_eq hcν 0 fun s t hs hst ω => ?_⟩
    · beta_reduce
      obtain ⟨d1, -⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
      have hχ := chiProc_sub hZc (lamb ρ κ σ) ω s t
      have iW : IntervalIntegrable (fun r => σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r))
          volume s t := ((intervalIntegrable_const.sub (hWc.intervalIntegrable s t)).sub
            (trapStep_intervalIntegrable u T s t)).const_mul σ
      have iχ : IntervalIntegrable (fun r => chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω)
          volume s t := (hχc ω).intervalIntegrable s t
      have icν : IntervalIntegrable (fun r => c r * ν r ω) volume s t :=
        (hZc ω).intervalIntegrable s t
      have ihν : IntervalIntegrable (fun r => trapStep 1 T r * ν r ω) volume s t :=
        (trapStep_intervalIntegrable 1 T s t).mul_continuousOn (hν.1 ω).continuousOn
      have e1 : (∫ r in s..t, σ * (trackRate T (fun t ω => trapStep u T t + ν t ω) r ω -
          (wPi σ κ ρ T u g πT r + chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) -
            (trapStep u T r + ν r ω))) =
          (∫ r in s..t, σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r)) -
            σ * (∫ r in s..t, chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) -
              σ * ∫ r in s..t, trapStep 1 T r * ν r ω := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_sub iW (iχ.const_mul σ),
          ← intervalIntegral.integral_sub (iW.sub (iχ.const_mul σ)) (ihν.const_mul σ)]
        refine intervalIntegral.integral_congr fun r _ => ?_
        have := trackRate_sub T u ν r ω
        linear_combination σ * this
      have e2 : (∫ r in s..t, ((lamf ρ κ σ + η) * c r + κ * σ * trapStep 1 T r - η * c r) *
          ν r ω) = lamf ρ κ σ * (∫ r in s..t, c r * ν r ω) +
            κ * σ * ∫ r in s..t, trapStep 1 T r * ν r ω := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add (icν.const_mul _) (ihν.const_mul (κ * σ))]
        refine intervalIntegral.integral_congr fun r _ => ?_
        ring
      have e3 : (∫ r in s..t, (-lamb ρ κ σ * chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω +
          c r * ν r ω)) = -lamb ρ κ σ * (∫ r in s..t,
            chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) + ∫ r in s..t, c r * ν r ω := by
        rw [intervalIntegral.integral_add (iχ.const_mul _) icν,
          intervalIntegral.integral_const_mul]
      rw [e3] at hχ
      rw [e1, e2, ← d1]
      have hk : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ0
      linear_combination (lamf ρ κ σ / κ) * hχ - (∫ r in s..t,
        chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) * hc -
        σ * (∫ r in s..t, trapStep 1 T r * ν r ω) * hk
    · beta_reduce
      obtain ⟨-, d2⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
      have hχ := chiProc_sub hZc (lamb ρ κ σ) ω s t
      have iD : IntervalIntegrable (fun r => ρ * wPi σ κ ρ T u g πT r -
          κ * (wX σ κ ρ T u g πT r + trapStep g T r)) volume s t :=
        ((hWc.intervalIntegrable s t).const_mul ρ).sub (((hXc.intervalIntegrable s t).add
          (trapStep_intervalIntegrable g T s t)).const_mul κ)
      have iχ : IntervalIntegrable (fun r => chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω)
          volume s t := (hχc ω).intervalIntegrable s t
      have icν : IntervalIntegrable (fun r => c r * ν r ω) volume s t :=
        (hZc ω).intervalIntegrable s t
      have e1 : (∫ r in s..t, (ρ * (wPi σ κ ρ T u g πT r +
          chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) -
          κ * ((wX σ κ ρ T u g πT r + lamf ρ κ σ / κ *
            chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω - c r * ν r ω / κ) +
              trapStep g T r))) =
          (∫ r in s..t, (ρ * wPi σ κ ρ T u g πT r - κ * (wX σ κ ρ T u g πT r +
            trapStep g T r))) + (ρ - lamf ρ κ σ) * (∫ r in s..t,
              chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) + ∫ r in s..t, c r * ν r ω := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add iD
          (iχ.const_mul _), ← intervalIntegral.integral_add (iD.add (iχ.const_mul _)) icν]
        refine intervalIntegral.integral_congr fun r _ => ?_
        field_simp
        ring
      have e3 : (∫ r in s..t, (-lamb ρ κ σ * chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω +
          c r * ν r ω)) = -lamb ρ κ σ * (∫ r in s..t,
            chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) + ∫ r in s..t, c r * ν r ω := by
        rw [intervalIntegral.integral_add (iχ.const_mul _) icν,
          intervalIntegral.integral_const_mul]
      rw [e3] at hχ
      rw [e1, ← d2]
      linear_combination hχ + (∫ r in s..t,
        chiProc (lamb ρ κ σ) (fun t ω => c t * ν t ω) r ω) * hsub
  exact key _ (continuous_trackD σ κ ρ η T) (fun r hr => hasDerivAt_trackD hσ hκ hη hr)
    (abs_trackD_le hlη)

variable {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a bounded deterministic multiple of an `L²`-bounded
process is `L²`-bounded.
Generalises `TidyR8StochWerningNaturalMean.BddL2.const_mul`. -/
theorem bddL2_mul_det {Z : ℝ → Ω → ℝ} (hZ : BddL2 P Z) {c : ℝ → ℝ} {C : ℝ}
    (hc : ∀ t, |c t| ≤ C) : BddL2 P (fun t ω => c t * Z t ω) := by
  obtain ⟨K, hK⟩ := hZ
  have hK0 : 0 ≤ K := (integral_nonneg fun _ => sq_nonneg _).trans (hK 0 le_rfl).2
  refine ⟨C ^ 2 * K, fun t ht => ⟨(hK t ht).1.const_mul _, ?_⟩⟩
  have hc2 : c t ^ 2 ≤ C ^ 2 := by
    have := hc t
    nlinarith [abs_nonneg (c t), sq_abs (c t)]
  calc ∫ ω, (c t * Z t ω) ^ 2 ∂P = c t ^ 2 * ∫ ω, Z t ω ^ 2 ∂P := by
        rw [← integral_const_mul]; congr 1; funext ω; ring
    _ ≤ C ^ 2 * K := mul_le_mul hc2 (hK t ht).2 (integral_nonneg fun _ => sq_nonneg _)
        (by nlinarith [abs_nonneg (c t), hc t])

/-- Cochrane (2023), §20.2.2, p. 474, under the tracking rule: on the Brownian filtration the
explicit processes are regular and bounded in mean square when the shock is (`η ≥ 0`). -/
theorem regular_bddL2_track [IsProbabilityMeasure P] (hW : ∀ t, Measurable (W t)) {σ ρ κ η : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 ≤ η) (T u g πT : ℝ) {ν : ℝ → Ω → ℝ}
    (hν : Regular (bmFiltrationReal W hW) ν) (hνb : BddL2 P ν) :
    Regular (bmFiltrationReal W hW) (trackPi σ κ ρ η T u g πT ν) ∧
      Regular (bmFiltrationReal W hW) (trackX σ κ ρ η T u g πT ν) ∧
      BddL2 P (trackPi σ κ ρ η T u g πT ν) ∧ BddL2 P (trackX σ κ ρ η T u g πT ν) := by
  have hlb := lamb_pos (ρ := ρ) hκ hσ
  have hcd : ∀ r, |trackD σ κ ρ η T r| ≤ |natD σ κ ρ η| :=
    abs_trackD_le (by linarith [lamf_pos (ρ := ρ) hκ hσ])
  have hZ : Regular (bmFiltrationReal W hW) (fun t ω => trackD σ κ ρ η T t * ν t ω) :=
    ⟨fun ω => (continuous_trackD σ κ ρ η T).mul (hν.1 ω), fun t =>
      stronglyMeasurable_const.mul (hν.2 t)⟩
  have hZb := bddL2_mul_det hνb hcd
  have hχ := regular_chiProc hW hZ (lamb ρ κ σ)
  have hχb := bddL2_chiProc hW hZ hZb hlb
  have eX : trackX σ κ ρ η T u g πT ν = fun t ω => (wX σ κ ρ T u g πT t +
      lamf ρ κ σ / κ * trackChi σ κ ρ η T ν t ω) +
        (-1 / κ) * (trackD σ κ ρ η T t * ν t ω) := by
    funext t ω
    simp only [trackX]
    ring
  refine ⟨Regular.add (regular_det _ (wPi_continuous σ κ ρ T u g πT hκ hσ)) hχ, ?_,
    BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).2) hχb, ?_⟩
  · rw [eX]
    exact Regular.add (Regular.add (regular_det _ (wX_continuous σ κ ρ T u g πT hκ hσ))
      (Regular.const_mul hχ _)) (Regular.const_mul hZ _)
  · rw [eX]
    exact BddL2.add (BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).1)
      (BddL2.const_mul hχb _)) (BddL2.const_mul hZb _)

/-! ## Non-vacuity on the constructed Brownian motion -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder

/-- Cochrane (2023), §20.2.2, pp. 474–475 (non-vacuity): on bmPath at the book's calibration
(`ρ = 0.05`, `σ = κ = 1`, `T = 5`, `u = −2%`, `g = 0`) with the OU natural-rate shock
`η = 1/2`, `s_ν = 1/100` and the rate tracking the natural rate after the trap: the response
`c(0)` is non-zero, the explicit processes with `π_T = 0` are a regular, mean-square-bounded
equilibrium, and they satisfy `unstable_track` and `condExp_pi_track`. -/
theorem bmPath_track :
    trackD 1 1 (1 / 20) (1 / 2) 5 0 ≠ 0 ∧
    IsStochEqmTrack 1 (1 / 20) 1 gaussSeq (bmFiltrationReal bmPath measurable_bmPath) 5
        (-2 / 100) 0 (ouProc (1 / 2) 0 0 (1 / 100) bmPath)
        (trackX 1 1 (1 / 20) (1 / 2) 5 (-2 / 100) 0 0 (ouProc (1 / 2) 0 0 (1 / 100) bmPath))
        (trackPi 1 1 (1 / 20) (1 / 2) 5 (-2 / 100) 0 0 (ouProc (1 / 2) 0 0 (1 / 100) bmPath)) ∧
      BddL2 gaussSeq
        (trackPi 1 1 (1 / 20) (1 / 2) 5 (-2 / 100) 0 0 (ouProc (1 / 2) 0 0 (1 / 100) bmPath)) ∧
      BddL2 gaussSeq
        (trackX 1 1 (1 / 20) (1 / 2) 5 (-2 / 100) 0 0 (ouProc (1 / 2) 0 0 (1 / 100) bmPath)) ∧
      ∀ s t, 0 ≤ s → s ≤ t →
        gaussSeq[trackPi 1 1 (1 / 20) (1 / 2) 5 (-2 / 100) 0 0
          (ouProc (1 / 2) 0 0 (1 / 100) bmPath) t |
          bmFiltrationReal bmPath measurable_bmPath s] =ᵐ[gaussSeq] fun ω =>
          wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 t + Real.exp (-(lamb (1 / 20) 1 1 * (t - s))) *
            (trackPi 1 1 (1 / 20) (1 / 2) 5 (-2 / 100) 0 0
              (ouProc (1 / 2) 0 0 (1 / 100) bmPath) s ω - wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 s) +
          trackK (lamb (1 / 20) 1 1) (1 / 2) (trackD 1 1 (1 / 20) (1 / 2) 5) s t *
            ouProc (1 / 2) 0 0 (1 / 100) bmPath s ω := by
  have := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have hη : (0 : ℝ) < 1 / 2 := by norm_num
  have hν := regular_ouProc measurable_bmPath continuous_bmPath (1 / 2) 0 0 (1 / 100)
  have hν2 := bddL2_ou hB measurable_bmPath continuous_bmPath bmPath_zero hη (1 / 100)
  have hνd := expDrift_ou hB measurable_bmPath continuous_bmPath (1 / 2) (1 / 100)
  have heq := isStochEqmTrack_trackPi (P := gaussSeq) one_pos one_pos hη.le (ρ := 1 / 20) 5
    (-2 / 100) 0 0 hν hν2.bddL1 hνd
  obtain ⟨rπ, rx, bπ, bx⟩ := regular_bddL2_track (P := gaussSeq) measurable_bmPath one_pos
    one_pos hη.le (ρ := 1 / 20) 5 (-2 / 100) 0 0 hν hν2
  refine ⟨?_, heq, bπ, bx, fun s t hs hst =>
    condExp_pi_track one_pos one_pos hη.le hν hν2.bddL1 hνd rx bx.bddL1 rπ bπ.bddL1 heq hs hst⟩
  have hf := lamf_pos (ρ := 1 / 20) (one_pos : (0 : ℝ) < 1) one_pos
  have hd : natD 1 1 (1 / 20) (1 / 2) ≠ 0 := by
    unfold natD
    exact div_ne_zero (by norm_num) (by linarith)
  unfold trackD
  refine mul_ne_zero hd (sub_ne_zero.2 (Ne.symm ?_))
  rw [Ne, Real.exp_eq_one_iff]
  have : (0 : ℝ) < (lamf (1 / 20) 1 1 + 1 / 2) * max (5 - 0) 0 := by
    rw [max_eq_left (by norm_num)]
    nlinarith
  linarith

end Cochrane.ZeroBound.TidyR8StochWerningNaturalTrack
