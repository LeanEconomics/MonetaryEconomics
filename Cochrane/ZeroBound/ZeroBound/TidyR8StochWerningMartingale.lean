/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR8StochWerningNaturalMean

/-!
# Which innovation processes occur: the equilibria are the martingales

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476
(Figure 20.4: "multiple forward-stable equilibrium inflation paths, indexed by the free
constant `C`", and the fiscal innovation of p. 476), under uncertainty.

TidyR7StochWerningTrap shows that every regular `L¹`-bounded equilibrium of the trap experiment
has `E_sπ_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s)`; TidyR7StochWerningExist builds
equilibria with constant innovation loadings `b`. Here we describe **all** of them: with
`M_t = e^{λ^b t}(π_t − wPi(0)_t)`,

* **`martingale_of_isStochEqm`**: in every regular `L¹`-bounded equilibrium `M` is a continuous
  adapted martingale (`E_s M_t = M_s`), `e^{−λ^b t}M_t` is `L¹`-bounded,
  `π_t = wPi(0)_t + e^{−λ^b t}M_t` and `x_t = wX(0)_t + (λ^f/κ)e^{−λ^b t}M_t` almost surely;
* **`isStochEqm_of_martingale`**: conversely every continuous adapted martingale `M` with
  `e^{−λ^b t}M_t` bounded in `L¹` gives an equilibrium (`zPi`, `zX`), on any filtration.

So the free constant `C` (equivalently `π_T`) of Figure 20.4 becomes a free martingale; the
"innovation processes that occur" are exactly the increments of such martingales. Which
martingales exist on the natural filtration of a Brownian motion is the content of the
martingale representation theorem (`M_t = M_0 + ∫_0^t H dW` with `H` adapted), which is not
available here; we do not need it for the description above, only to express `M` as a
stochastic integral.

Existence with **deterministic time-varying loadings** `b(u)` (`C¹`, bounded with its
derivative continuous) through Wiener integrals: `M_t = ∫_0^t e^{λ^b u} b(u) dW_u`, in the
pathwise by-parts form `wienerBP` (`wienerM`), is a continuous adapted martingale
(`condExp_wienerBP`, `martingale_wienerM`), and `ζ_t = e^{−λ^b t}M_t` is bounded in mean square
(`integral_zetaB_sq_le`); hence **`isStochEqm_loading`**: the equilibrium with
innovations `dπ_t = b(t) dW_t`, `dx_t = (λ^f/κ)b(t) dW_t` exists and is `L²`-bounded. Continuous
loadings that are not `C¹` would need the Itô integral as a continuous adapted process (its
continuous modification is not shown adapted here). Non-vacuity on bmPath with `b = cos`:
`bmPath_loading_cos`.
-/

namespace Cochrane.ZeroBound.TidyR8StochWerningMartingale

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningExist Cochrane.ZeroBound.TidyR7StochWerningNaturalExist
open Cochrane.ZeroBound.TidyR8StochWerningNaturalMean
open Cochrane.ZeroBound.TidyR7BrownianTools Cochrane.ZeroBound.TidyR7WienerGaussian
open Cochrane.ZeroBound.TidyR7ItoIntegral
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## Brackets -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474 (tool): if the bracket of `Z'` is `c` times the
bracket of `Z` and `E_t dZ = D dt`, then `E_t dZ' = D' dt`. -/
theorem expDrift_of_bracket_eq {𝓕 : Filtration ℝ mΩ} {Z D Z' D' : ℝ → Ω → ℝ}
    (h : ExpDrift P 𝓕 Z D) (c : ℝ)
    (he : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω, Z' t ω - Z' s ω - ∫ r in s..t, D' r ω =
      c * (Z t ω - Z s ω - ∫ r in s..t, D r ω)) : ExpDrift P 𝓕 Z' D' := by
  intro s t hs hst
  obtain ⟨h1, h2⟩ := h s t hs hst
  have e : (fun ω => Z' t ω - Z' s ω - ∫ r in s..t, D' r ω) =
      c • fun ω => Z t ω - Z s ω - ∫ r in s..t, D r ω := by
    funext ω
    simp [he s t hs hst ω]
  rw [e]
  refine ⟨h1.const_mul c, ?_⟩
  filter_upwards [condExp_smul (μ := P) c (fun ω => Z t ω - Z s ω - ∫ r in s..t, D r ω)
    (𝓕 s), h2] with ω e1 e2
  rw [e1, Pi.smul_apply, e2]
  simp

/-- Cochrane (2023), §20.2.2, p. 475: the inflation process `π = wPi(π_T) + ζ` driven by a
stable-direction innovation process `ζ`. -/
noncomputable def zPi (σ κ ρ T u g πT : ℝ) (ζ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wPi σ κ ρ T u g πT t + ζ t ω

/-- Cochrane (2023), (20.10), p. 475: the output process `x = wX(π_T) + (λ^f/κ)ζ`. -/
noncomputable def zX (σ κ ρ T u g πT : ℝ) (ζ : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wX σ κ ρ T u g πT t + lamf ρ κ σ / κ * ζ t ω

/-- **Cochrane (2023), (20.5)–(20.6), p. 474: any stable-direction innovation gives an
equilibrium.** If `ζ` has continuous paths and `E_t dζ = −λ^b ζ dt`, then
`(wX(π_T) + (λ^f/κ)ζ, wPi(π_T) + ζ)` is a stochastic equilibrium of the trap experiment.
Generalises `TidyR7StochWerningExist.isStochEqm_eq`. -/
theorem isStochEqm_of_zeta {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {𝓕 : Filtration ℝ mΩ}
    (T u g πT : ℝ) {ζ : ℝ → Ω → ℝ} (hζc : ∀ ω, Continuous fun t => ζ t ω)
    (hζ : ExpDrift P 𝓕 ζ (fun r ω => -(lamb ρ κ σ * ζ r ω))) :
    IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0)
      (zX σ κ ρ T u g πT ζ) (zPi σ κ ρ T u g πT ζ) := by
  have hsub := lamf_sub_lamb ρ κ σ
  have hc : lamf ρ κ σ / κ * lamb ρ κ σ = σ := by
    have := lamf_mul_lamb (ρ := ρ) hκ hσ
    field_simp
    linarith
  have hWc := wPi_continuous σ κ ρ T u g πT hκ hσ
  have hXc := wX_continuous σ κ ρ T u g πT hκ hσ
  refine ⟨expDrift_of_bracket_eq hζ (lamf ρ κ σ / κ) fun s t hs hst ω => ?_,
    expDrift_of_bracket_eq hζ 1 fun s t hs hst ω => ?_⟩
  · obtain ⟨d1, -⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
    have i1 : IntervalIntegrable (fun r => σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r))
        volume s t := ((intervalIntegrable_const.sub (hWc.intervalIntegrable s t)).sub
          (trapStep_intervalIntegrable u T s t)).const_mul σ
    have i2 : IntervalIntegrable (fun r => σ * ζ r ω) volume s t :=
      ((hζc ω).intervalIntegrable s t).const_mul σ
    have e : (∫ r in s..t, σ * (0 - zPi σ κ ρ T u g πT ζ r ω - (trapStep u T r + 0))) =
        (∫ r in s..t, σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r)) -
          σ * ∫ r in s..t, ζ r ω := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub i1 i2]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [zPi]
      ring
    have e2 : (∫ r in s..t, -(lamb ρ κ σ * ζ r ω)) = -(lamb ρ κ σ * ∫ r in s..t, ζ r ω) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    simp only [zX]
    rw [e, e2, ← d1]
    linear_combination (-(∫ r in s..t, ζ r ω)) * hc
  · obtain ⟨-, d2⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
    have i1 : IntervalIntegrable (fun r => ρ * wPi σ κ ρ T u g πT r -
        κ * (wX σ κ ρ T u g πT r + trapStep g T r)) volume s t :=
      ((hWc.intervalIntegrable s t).const_mul ρ).sub (((hXc.intervalIntegrable s t).add
        (trapStep_intervalIntegrable g T s t)).const_mul κ)
    have i2 : IntervalIntegrable (fun r => (ρ - lamf ρ κ σ) * ζ r ω) volume s t :=
      ((hζc ω).intervalIntegrable s t).const_mul _
    have e : (∫ r in s..t, (ρ * zPi σ κ ρ T u g πT ζ r ω -
        κ * (zX σ κ ρ T u g πT ζ r ω + trapStep g T r))) =
        (∫ r in s..t, (ρ * wPi σ κ ρ T u g πT r - κ * (wX σ κ ρ T u g πT r + trapStep g T r))) +
          (ρ - lamf ρ κ σ) * ∫ r in s..t, ζ r ω := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 i2]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [zPi, zX]
      field_simp
      ring
    have e2 : (∫ r in s..t, -(lamb ρ κ σ * ζ r ω)) = -(lamb ρ κ σ * ∫ r in s..t, ζ r ω) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    rw [e, e2]
    simp only [zPi]
    rw [← d2]
    linear_combination (∫ u in s..t, ζ u ω) * hsub

/-! ## From martingales to equilibria -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): for a process with continuous paths, measurable
time sections and bounded first moments, `∫_A ∫_s^t Z_r dr = ∫_s^t ∫_A Z_r dr` (Fubini). -/
theorem setIntegral_intervalIntegral_swap [IsFiniteMeasure P] {Z : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Z t ω) (hm : ∀ t, Measurable (Z t)) {K : ℝ}
    (hK : ∀ t, 0 ≤ t → Integrable (Z t) P ∧ ∫ ω, |Z t ω| ∂P ≤ K) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (A : Set Ω) :
    ∫ ω in A, (∫ r in s..t, Z r ω) ∂P = ∫ r in s..t, ∫ ω in A, Z r ω ∂P := by
  have hD := integrable_prod_proc (P := P) hc hm hK hs (b := t)
  simp only [intervalIntegral.integral_of_le hst]
  have hDA : Integrable (Function.uncurry Z)
      ((volume.restrict (Set.Ioc s t)).prod (P.restrict A)) := by
    have he : (volume.restrict (Set.Ioc s t)).prod (P.restrict A)
        = ((volume.restrict (Set.Ioc s t)).prod P).restrict (Set.univ ×ˢ A) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [he]
    exact hD.restrict
  exact (integral_integral_swap hDA).symm

/-- Cochrane (2023), §20.2.2, p. 475: `∫_s^t e^{−λr} dr = (e^{−λs} − e^{−λt})/λ`.
`WerningModel.integral_exp_fwd` at `c = 1`, `t = 0`. -/
theorem integral_exp_neg (lam : ℝ) (hlam : lam ≠ 0) (s t : ℝ) :
    ∫ r in s..t, Real.exp (-(lam * r)) = (Real.exp (-(lam * s)) - Real.exp (-(lam * t))) / lam := by
  have hd : ∀ x ∈ Set.uIcc s t, HasDerivAt (fun r => -Real.exp (-(lam * r)) / lam)
      (Real.exp (-(lam * x))) x := fun x _ => by
    have h1 : HasDerivAt (fun r => Real.exp (-(lam * r))) (Real.exp (-(lam * x)) * -lam) x := by
      simpa using ((hasDerivAt_id' x).const_mul lam).neg.exp
    refine (h1.neg.div_const lam).congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun r => Real.exp (-(lam * r))).intervalIntegrable s t)]
  ring

/-- **Cochrane (2023), §20.2.2, p. 475: a martingale gives a stable-direction innovation.** If
`M` has continuous paths and measurable sections, is a martingale on `[0, ∞)`
(`E_s M_t = M_s`) and `ζ_t = e^{−λt}M_t` is `L¹`-bounded, then `E_t dζ = −λζ dt`. -/
theorem expDrift_zeta_of_martingale [IsProbabilityMeasure P] {𝓕 : Filtration ℝ mΩ}
    {lam : ℝ} (hlam : 0 < lam) {M : ℝ → Ω → ℝ} (hMc : ∀ ω, Continuous fun t => M t ω)
    (hMm : ∀ t, StronglyMeasurable[𝓕 t] (M t))
    (hmart : ∀ s t, 0 ≤ s → s ≤ t → P[M t | 𝓕 s] =ᵐ[P] M s)
    (hζb : BddL1 P (fun t ω => Real.exp (-(lam * t)) * M t ω)) :
    ExpDrift P 𝓕 (fun t ω => Real.exp (-(lam * t)) * M t ω)
      (fun r ω => -(lam * (Real.exp (-(lam * r)) * M r ω))) := by
  obtain ⟨K, hK⟩ := hζb
  set ζ : ℝ → Ω → ℝ := fun t ω => Real.exp (-(lam * t)) * M t ω with hζdef
  have hζc : ∀ ω, Continuous fun t => ζ t ω := fun ω => (by fun_prop : Continuous fun t : ℝ =>
    Real.exp (-(lam * t))).mul (hMc ω)
  have hζm : ∀ t, Measurable (ζ t) := fun t =>
    (stronglyMeasurable_const.mul ((hMm t).mono (𝓕.le t))).measurable
  have hMi : ∀ t, 0 ≤ t → Integrable (M t) P := fun t ht => by
    have := (hK t ht).1.const_mul (Real.exp (lam * t))
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hζdef, ← mul_assoc, ← Real.exp_add]
    simp
  intro s t hs hst
  have hI : Integrable (fun ω => ∫ r in s..t, ζ r ω) P := by
    have := (integrable_prod_proc (P := P) hζc hζm hK hs (b := t)).integral_prod_right
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Function.uncurry_apply_pair, intervalIntegral.integral_of_le hst]
  have hB : Integrable (fun ω => ζ t ω - ζ s ω - ∫ r in s..t, -(lam * ζ r ω)) P := by
    have : (fun ω => ζ t ω - ζ s ω - ∫ r in s..t, -(lam * ζ r ω)) =
        fun ω => ζ t ω - ζ s ω + lam * ∫ r in s..t, ζ r ω := by
      funext ω
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      ring
    rw [this]
    exact (((hK t (hs.trans hst)).1.sub (hK s hs).1)).add (hI.const_mul lam)
  refine ⟨hB, ?_⟩
  have h0 : (fun _ => (0 : ℝ)) =ᵐ[P]
      P[fun ω => ζ t ω - ζ s ω - ∫ r in s..t, -(lam * ζ r ω) | 𝓕 s] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hB (fun _ _ _ => integrableOn_const
      (by simp)) (fun A hA _ => ?_) stronglyMeasurable_const.aestronglyMeasurable
    have hA' : MeasurableSet A := 𝓕.le s A hA
    have hmA : ∀ r, s ≤ r → ∫ ω in A, M r ω ∂P = ∫ ω in A, M s ω ∂P := fun r hr => by
      rw [← setIntegral_condExp (𝓕.le s) (hMi r (hs.trans hr)) hA]
      exact setIntegral_congr_ae hA' ((hmart s r hs hr).mono fun ω hω _ => hω)
    have hζA : ∀ r, s ≤ r → ∫ ω in A, ζ r ω ∂P =
        Real.exp (-(lam * r)) * ∫ ω in A, M s ω ∂P := fun r hr => by
      rw [integral_const_mul, hmA r hr]
    have hswap := setIntegral_intervalIntegral_swap (P := P) hζc hζm hK hs hst A
    have hint : ∫ r in s..t, ∫ ω in A, ζ r ω ∂P =
        ∫ r in s..t, Real.exp (-(lam * r)) * ∫ ω in A, M s ω ∂P := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hst] at hr
      exact hζA r hr.1
    rw [intervalIntegral.integral_mul_const, integral_exp_neg lam hlam.ne' s t] at hint
    have e : (fun ω => ζ t ω - ζ s ω - ∫ r in s..t, -(lam * ζ r ω)) =
        fun ω => ζ t ω - ζ s ω + lam * ∫ r in s..t, ζ r ω := by
      funext ω
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      ring
    have i1 : Integrable (fun ω => ζ t ω - ζ s ω) (P.restrict A) :=
      ((hK t (hs.trans hst)).1.sub (hK s hs).1).integrableOn
    have i2 : Integrable (fun ω => lam * ∫ r in s..t, ζ r ω) (P.restrict A) :=
      (hI.const_mul lam).integrableOn
    have i3 : Integrable (fun ω => ζ t ω) (P.restrict A) := (hK t (hs.trans hst)).1.integrableOn
    have i4 : Integrable (fun ω => ζ s ω) (P.restrict A) := (hK s hs).1.integrableOn
    rw [e, integral_add i1 i2, integral_sub i3 i4, hζA t hst, hζA s le_rfl,
      integral_const_mul lam (fun ω => ∫ r in s..t, ζ r ω), hswap, hint]
    simp only [integral_zero]
    field_simp
    ring
  exact h0.symm

/-- **Cochrane (2023), §20.2.2, pp. 474–476: every martingale gives an equilibrium.** On any
filtration, if `M` is a continuous adapted martingale on `[0, ∞)` with `e^{−λ^b t}M_t` bounded in
`L¹`, then with `ζ_t = e^{−λ^b t}M_t` the processes `zX(0) ζ`, `zPi(0) ζ` are a regular
`L¹`-bounded stochastic equilibrium of the trap experiment. -/
theorem isStochEqm_of_martingale [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) {𝓕 : Filtration ℝ mΩ} (T u g : ℝ) {M : ℝ → Ω → ℝ}
    (hMc : ∀ ω, Continuous fun t => M t ω) (hMm : ∀ t, StronglyMeasurable[𝓕 t] (M t))
    (hmart : ∀ s t, 0 ≤ s → s ≤ t → P[M t | 𝓕 s] =ᵐ[P] M s)
    (hζb : BddL1 P (fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω)) :
    IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0)
        (zX σ κ ρ T u g 0 fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω)
        (zPi σ κ ρ T u g 0 fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) ∧
      Regular 𝓕 (zX σ κ ρ T u g 0 fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) ∧
      Regular 𝓕 (zPi σ κ ρ T u g 0 fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) ∧
      BddL1 P (zX σ κ ρ T u g 0 fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) ∧
      BddL1 P (zPi σ κ ρ T u g 0 fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) := by
  have hreg : Regular 𝓕 (fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) :=
    ⟨fun ω => (by fun_prop : Continuous fun t : ℝ => Real.exp (-(lamb ρ κ σ * t))).mul (hMc ω),
      fun t => stronglyMeasurable_const.mul (hMm t)⟩
  refine ⟨isStochEqm_of_zeta hσ hκ T u g 0 hreg.1
      (expDrift_zeta_of_martingale (lamb_pos hκ hσ) hMc hMm hmart hζb), ?_, ?_, ?_, ?_⟩
  · exact Regular.add (regular_det 𝓕 (wX_continuous σ κ ρ T u g 0 hκ hσ))
      (Regular.const_mul hreg _)
  · exact Regular.add (regular_det 𝓕 (wPi_continuous σ κ ρ T u g 0 hκ hσ)) hreg
  · exact BddL1.add (bddL1_det (wPath_bdd (ρ := ρ) hκ hσ T u g 0).1) (BddL1.const_mul hζb _)
  · exact BddL1.add (bddL1_det (wPath_bdd (ρ := ρ) hκ hσ T u g 0).2) hζb

/-! ## From equilibria to martingales -/

/-- **Cochrane (2023), §20.2.2, pp. 474–476: every equilibrium is given by a martingale.** In
every regular `L¹`-bounded stochastic equilibrium of the trap experiment, on any filtration,
`M_t = e^{λ^b t}(π_t − wPi(0)_t)` is a continuous adapted martingale on `[0, ∞)`,
`e^{−λ^b t}M_t` is `L¹`-bounded, `π = wPi(0) + e^{−λ^b t}M` on every path, and
`x_t = wX(0)_t + (λ^f/κ)e^{−λ^b t}M_t` almost surely at every date. With
`isStochEqm_of_martingale` this describes all equilibria.
Refines `TidyR7StochWerningTrap.condExp_pi_eq`. -/
theorem martingale_of_isStochEqm [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π) :
    let M : ℝ → Ω → ℝ := fun t ω => Real.exp (lamb ρ κ σ * t) * (π t ω - wPi σ κ ρ T u g 0 t)
    (∀ ω, Continuous fun t => M t ω) ∧ (∀ t, StronglyMeasurable[𝓕 t] (M t)) ∧
      (∀ s t, 0 ≤ s → s ≤ t → P[M t | 𝓕 s] =ᵐ[P] M s) ∧
      BddL1 P (fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) ∧
      (∀ t ω, π t ω = wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * t)) * M t ω) ∧
      ∀ t, 0 ≤ t → x t =ᵐ[P] fun ω =>
        wX σ κ ρ T u g 0 t + lamf ρ κ σ / κ * (Real.exp (-(lamb ρ κ σ * t)) * M t ω) := by
  intro M
  have hWc := wPi_continuous σ κ ρ T u g 0 hκ hσ
  have hinv : ∀ t, Real.exp (-(lamb ρ κ σ * t)) * Real.exp (lamb ρ κ σ * t) = 1 := fun t => by
    rw [← Real.exp_add]; simp
  have hrep : ∀ t ω, π t ω = wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * t)) * M t ω :=
    fun t ω => by
      simp only [M]
      linear_combination (wPi σ κ ρ T u g 0 t - π t ω) * hinv t
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hζ : BddL1 P (fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) := by
    obtain ⟨KW, hKW⟩ := (wPath_bdd (ρ := ρ) hκ hσ T u g 0).2
    have := BddL1.add (P := P) ⟨Kπ, hKπ⟩ (BddL1.const_mul (bddL1_det (P := P) ⟨KW, hKW⟩) (-1))
    refine (show (fun t ω => π t ω + -1 * wPi σ κ ρ T u g 0 t) =
      (fun t ω => Real.exp (-(lamb ρ κ σ * t)) * M t ω) from ?_) ▸ this
    funext t ω
    rw [hrep t ω]
    ring
  refine ⟨fun ω => (by fun_prop : Continuous fun t : ℝ => Real.exp (lamb ρ κ σ * t)).mul
      ((hπ.1 ω).sub hWc), fun t => stronglyMeasurable_const.mul ((hπ.2 t).sub
      stronglyMeasurable_const), fun s t hs hst => ?_, hζ, hrep, fun t ht => ?_⟩
  · have hMi : ∀ t, 0 ≤ t → Integrable (M t) P := fun t ht =>
      (((hKπ t ht).1.sub (integrable_const _)).const_mul _)
    have h1 : M s =ᵐ[P] P[M t | 𝓕 s] := by
      refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hMi t (hs.trans hst))
        (fun _ _ _ => (hMi s hs).integrableOn) (fun A hA _ => ?_)
        (stronglyMeasurable_const.mul ((hπ.2 s).sub
          stronglyMeasurable_const)).aestronglyMeasurable
      obtain ⟨a1, -⟩ := setIntegral_trap hσ hκ hx hxb hπ ⟨Kπ, hKπ⟩ h hs hA t hst
      simp only [M]
      rw [integral_const_mul, integral_const_mul,
        integral_sub (hKπ s hs).1.integrableOn (integrable_const _),
        integral_sub (hKπ t (hs.trans hst)).1.integrableOn (integrable_const _),
        setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, a1]
      have e : Real.exp (lamb ρ κ σ * t) * Real.exp (-(lamb ρ κ σ * (t - s))) =
          Real.exp (lamb ρ κ σ * s) := by rw [← Real.exp_add]; ring_nf
      linear_combination (-(∫ ω in A, π s ω ∂P - P.real A * wPi σ κ ρ T u g 0 s)) * e
    exact h1.symm
  · filter_upwards [x_eq_of_pi hσ hκ hx hxb hπ ⟨Kπ, hKπ⟩ h ht] with ω hω
    rw [hω]
    simp only [M]
    linear_combination (lamf ρ κ σ / κ * (wPi σ κ ρ T u g 0 t - π t ω)) * hinv t

/-! ## Time-varying deterministic loadings through Wiener integrals -/

variable {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), §20.2.2, p. 475 (tool): **Wiener integrals have zero conditional mean**:
for a `C¹` integrand `h` (derivative `h'` continuous) and `0 ≤ s ≤ t`,
`E_s[∫_s^t h dW] = 0`, in the by-parts form `wienerBP W h h' s t`. From
`TidyR7WienerGaussian.itoInt_ae_eq_wienerBP` and `TidyR7ItoIntegral.condExp_itoInt`. -/
theorem condExp_wienerBP (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {h h' : ℝ → ℝ} (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh' : Continuous h') {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (wienerBP W h h' s t) P ∧
      P[wienerBP W h h' s t | bmFiltrationReal W hW s] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rcases hst.eq_or_lt with heq | hlt
  · subst heq
    have e : wienerBP W h h' s s = 0 := by funext ω; simp [wienerBP]
    rw [e]
    exact ⟨integrable_zero _ _ _, by simp⟩
  have h𝓕 := TidyR7BrownianQV.bmFiltrationReal_isBM hB hW
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc s t) hhc.continuousOn
  have hI : ItoIntegrand P (bmFiltrationReal W hW) (fun u _ => h u) s t C :=
    TidyR7ItoBridge.itoIntegrand_deterministic hhc.continuousOn fun u hu => by
      simpa [Real.norm_eq_abs] using hC u hu
  have hae := itoInt_ae_eq_wienerBP hB hW h𝓕 hcont hh hh' hs hlt
  refine ⟨(memLp_wienerBP hB hW hcont hh hh' hs hlt).integrable one_le_two, ?_⟩
  have h1 := condExp_itoInt hB hW h𝓕 hs le_rfl hst hI
  rw [itoInt_of_le le_rfl] at h1
  exact (condExp_congr_ae hae.symm).trans h1

/-- Cochrane (2023), §20.2.2, p. 475: the integrand `h(u) = e^{λu} b(u)` of the Wiener
integral `∫ e^{λu} b(u) dW_u`. -/
noncomputable def loadH (lam : ℝ) (b : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (lam * u) * b u

/-- Cochrane (2023), §20.2.2, p. 475: its derivative `h'(u) = e^{λu}(λb(u) + b'(u))`. -/
noncomputable def loadH' (lam : ℝ) (b b' : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (lam * u) * (lam * b u + b' u)

/-- Cochrane (2023), §20.2.2, p. 475: `h' ` is the derivative of `h`. -/
theorem hasDerivAt_loadH {lam : ℝ} {b b' : ℝ → ℝ} (hb : ∀ x, HasDerivAt b (b' x) x) (x : ℝ) :
    HasDerivAt (loadH lam b) (loadH' lam b b' x) x := by
  have h1 : HasDerivAt (fun u => Real.exp (lam * u)) (Real.exp (lam * x) * lam) x := by
    simpa using ((hasDerivAt_id' x).const_mul lam).exp
  refine (h1.mul (hb x)).congr_deriv ?_
  simp only [loadH']
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `h'` is continuous when `b, b'` are. -/
theorem continuous_loadH' {lam : ℝ} {b b' : ℝ → ℝ} (hbc : Continuous b) (hb'c : Continuous b') :
    Continuous (loadH' lam b b') := by
  unfold loadH'
  fun_prop

/-- Cochrane (2023), §20.2.2, p. 475: the martingale `M_t = ∫_0^t e^{λu} b(u) dW_u`, in the
pathwise by-parts form. -/
noncomputable def wienerM (lam : ℝ) (b b' : ℝ → ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wienerBP W (loadH lam b) (loadH' lam b b') 0 t ω

/-- Cochrane (2023), §20.2.2, p. 475: the by-parts integrals add over adjacent intervals:
`M_t − M_s = ∫_s^t h dW`. -/
theorem wienerM_sub (hcont : ∀ ω, Continuous fun t => W t ω) (lam : ℝ) {b b' : ℝ → ℝ}
    (hbc : Continuous b) (hb'c : Continuous b') (s t : ℝ) (ω : Ω) :
    wienerM lam b b' W t ω - wienerM lam b b' W s ω =
      wienerBP W (loadH lam b) (loadH' lam b b') s t ω := by
  have hc : Continuous fun u => bmReal W u ω * loadH' lam b b' u :=
    (continuous_bmReal (hcont ω)).mul (continuous_loadH' hbc hb'c)
  simp only [wienerM, wienerBP]
  rw [← intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 t)
    (hc.intervalIntegrable 0 s)]
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `M` is regular (continuous adapted paths). -/
theorem regular_wienerM (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (lam : ℝ) {b b' : ℝ → ℝ} (hbc : Continuous b) (hb'c : Continuous b') :
    Regular (bmFiltrationReal W hW) (wienerM lam b b' W) := by
  have hbm : Regular (bmFiltrationReal W hW) (bmReal W) :=
    ⟨fun ω => continuous_bmReal (hcont ω), fun t => stronglyMeasurable_bmReal_le hW le_rfl⟩
  have hhc : Continuous (loadH lam b) := by unfold loadH; fun_prop
  refine ⟨fun ω => ?_, fun t => ?_⟩
  · have hc : Continuous fun u => bmReal W u ω * loadH' lam b b' u :=
      (continuous_bmReal (hcont ω)).mul (continuous_loadH' hbc hb'c)
    simp only [wienerM, wienerBP]
    exact ((hhc.mul (continuous_bmReal (hcont ω))).sub continuous_const).sub
      (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0)
  · have e : wienerM lam b b' W t = fun ω => loadH lam b t * bmReal W t ω -
        loadH lam b 0 * bmReal W 0 ω - ∫ u in (0 : ℝ)..t, loadH' lam b b' u * bmReal W u ω := by
      funext ω
      simp only [wienerM, wienerBP]
      congr 1
      refine intervalIntegral.integral_congr fun u _ => ?_
      ring
    rw [e]
    have h0 : StronglyMeasurable[bmFiltrationReal W hW t] (bmReal W 0) := by
      by_cases ht : 0 ≤ t
      · exact stronglyMeasurable_bmReal_le hW (Real.toNNReal_le_toNNReal ht)
      · exact stronglyMeasurable_bmReal_le hW (by
          rw [Real.toNNReal_zero]; exact bot_le)
    exact ((stronglyMeasurable_const.mul (hbm.2 t)).sub (stronglyMeasurable_const.mul h0)).sub
      (stronglyMeasurable_integral_adapted hW hbm (continuous_loadH' hbc hb'c) t)

/-- **Cochrane (2023), §20.2.2, p. 475: `M` is a martingale** on `[0, ∞)`:
`E_s M_t = M_s` for `0 ≤ s ≤ t`, and `M_t` is integrable. -/
theorem martingale_wienerM (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (lam : ℝ) {b b' : ℝ → ℝ}
    (hb : ∀ x, HasDerivAt b (b' x) x) (hb'c : Continuous b') {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    Integrable (wienerM lam b b' W t) P ∧
      P[wienerM lam b b' W t | bmFiltrationReal W hW s] =ᵐ[P] wienerM lam b b' W s := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun x => (hb x).continuousAt
  have hh := hasDerivAt_loadH (lam := lam) hb
  have hh' := continuous_loadH' (lam := lam) hbc hb'c
  have i0t : Integrable (wienerM lam b b' W t) P :=
    (condExp_wienerBP hB hW hcont hh hh' le_rfl (hs.trans hst)).1
  have i0s : Integrable (wienerM lam b b' W s) P :=
    (condExp_wienerBP hB hW hcont hh hh' le_rfl hs).1
  obtain ⟨ist, cst⟩ := condExp_wienerBP hB hW hcont hh hh' hs hst
  refine ⟨i0t, ?_⟩
  have e : wienerM lam b b' W t = wienerM lam b b' W s + wienerBP W (loadH lam b)
      (loadH' lam b b') s t := by
    funext ω
    rw [Pi.add_apply, ← wienerM_sub hcont lam hbc hb'c s t ω]
    ring
  rw [e]
  filter_upwards [condExp_add (m := bmFiltrationReal W hW s) i0s ist, cst] with ω h1 h2
  rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable ((bmFiltrationReal W hW).le s)
    ((regular_wienerM hW hcont lam hbc hb'c).2 s) i0s]
  simp

/-- Cochrane (2023), §20.2.2, p. 475: the stable-direction innovation with loading `b`,
`ζ^b_t = e^{−λt}∫_0^t e^{λu}b(u)dW_u = ∫_0^t e^{−λ(t−u)}b(u)dW_u`. -/
noncomputable def zetaB (lam : ℝ) (b b' : ℝ → ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(lam * t)) * wienerM lam b b' W t ω

/-- Cochrane (2023), §20.2.2, p. 475: **`ζ^b` is bounded in mean square**: for `λ > 0`,
`|b| ≤ B` on `[0, ∞)` and `t ≥ 0`, `E(ζ^b_t)² ≤ B²/(2λ)` (Wiener isometry).
Generalises `TidyR7StochWerningExist.ouProc_sq_le` (constant loading). -/
theorem integral_zetaB_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {lam : ℝ} (hlam : 0 < lam) {b b' : ℝ → ℝ}
    (hb : ∀ x, HasDerivAt b (b' x) x) (hb'c : Continuous b') {B : ℝ}
    (hbB : ∀ u, 0 ≤ u → |b u| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (zetaB lam b b' W t) 2 P ∧ ∫ ω, zetaB lam b b' W t ω ^ 2 ∂P ≤ B ^ 2 / (2 * lam) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun x => (hb x).continuousAt
  have hh := hasDerivAt_loadH (lam := lam) hb
  have hh' := continuous_loadH' (lam := lam) hbc hb'c
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have e : zetaB lam b b' W 0 = fun _ => 0 := by funext ω; simp [zetaB, wienerM, wienerBP]
    rw [e]
    exact ⟨memLp_const 0, by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
      positivity⟩
  have hmem := memLp_wienerBP (P := P) hB hW hcont hh hh' le_rfl hpos
  have hsq := integral_wienerBP_sq (P := P) hB hW hcont hh hh' le_rfl hpos
  refine ⟨hmem.const_mul _, ?_⟩
  have e1 : ∫ ω, zetaB lam b b' W t ω ^ 2 ∂P =
      Real.exp (-(lam * t)) ^ 2 * ∫ u in (0 : ℝ)..t, loadH lam b u ^ 2 := by
    rw [← hsq, ← integral_const_mul]
    congr 1
    funext ω
    simp only [zetaB, wienerM]
    ring
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hbB 0 le_rfl)
  have e2 : ∫ u in (0 : ℝ)..t, loadH lam b u ^ 2 ≤
      ∫ u in (0 : ℝ)..t, B ^ 2 * Real.exp (lam * u) ^ 2 := by
    refine intervalIntegral.integral_mono_on hpos.le
      ((by unfold loadH; fun_prop : Continuous fun u => loadH lam b u ^ 2).intervalIntegrable
        0 t) ((by fun_prop : Continuous fun u => B ^ 2 * Real.exp (lam * u) ^ 2).intervalIntegrable
        0 t) fun u hu => ?_
    simp only [loadH, mul_pow]
    rw [mul_comm]
    have : b u ^ 2 ≤ B ^ 2 := by
      have := hbB u hu.1
      nlinarith [abs_nonneg (b u), sq_abs (b u)]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  rw [intervalIntegral.integral_const_mul, TidyR7OrnsteinUhlenbeck.integral_exp_sq hlam.ne'] at e2
  rw [e1]
  have hexp : Real.exp (-(lam * t)) ^ 2 * Real.exp (2 * lam * t) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; exact Real.exp_zero
  have hpos2 : 0 < Real.exp (-(lam * t)) ^ 2 := by positivity
  calc Real.exp (-(lam * t)) ^ 2 * ∫ u in (0 : ℝ)..t, loadH lam b u ^ 2
      ≤ Real.exp (-(lam * t)) ^ 2 * (B ^ 2 * ((Real.exp (2 * lam * t) -
          Real.exp (2 * lam * 0)) / (2 * lam))) := mul_le_mul_of_nonneg_left e2 hpos2.le
    _ = B ^ 2 * (1 - Real.exp (-(lam * t)) ^ 2) / (2 * lam) := by
        rw [mul_zero, Real.exp_zero]
        have e3 : Real.exp (-(lam * t)) ^ 2 * (B ^ 2 * ((Real.exp (2 * lam * t) - 1) /
            (2 * lam))) = B ^ 2 * (Real.exp (-(lam * t)) ^ 2 * Real.exp (2 * lam * t) -
              Real.exp (-(lam * t)) ^ 2) / (2 * lam) := by ring
        rw [e3, hexp]
    _ ≤ B ^ 2 / (2 * lam) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg B]

/-- **Cochrane (2023), (20.5)–(20.6), p. 474: equilibria with time-varying innovation
loadings.** For a `C¹` loading `b` (derivative continuous, `|b| ≤ B` on `[0, ∞)`), the processes
`π = wPi(π_T) + ζ^b`, `x = wX(π_T) + (λ^f/κ)ζ^b` (innovations `dπ_t = b(t)dW_t`,
`dx_t = (λ^f/κ)b(t)dW_t`) are a regular stochastic equilibrium of the trap experiment, bounded
in mean square.
Generalises `TidyR7StochWerningExist.isStochEqm_eq` and `TidyR7StochWerningExist.bddL2_eqPi`. -/
theorem isStochEqm_loading (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (T u g πT : ℝ) {b b' : ℝ → ℝ} (hb : ∀ x, HasDerivAt b (b' x) x) (hb'c : Continuous b')
    {B : ℝ} (hbB : ∀ u, 0 ≤ u → |b u| ≤ B) :
    IsStochEqm σ ρ κ P (bmFiltrationReal W hW) (fun _ => 0) (trapStep u T) (trapStep g T)
        (fun _ _ => 0) (zX σ κ ρ T u g πT (zetaB (lamb ρ κ σ) b b' W))
        (zPi σ κ ρ T u g πT (zetaB (lamb ρ κ σ) b b' W)) ∧
      Regular (bmFiltrationReal W hW) (zPi σ κ ρ T u g πT (zetaB (lamb ρ κ σ) b b' W)) ∧
      Regular (bmFiltrationReal W hW) (zX σ κ ρ T u g πT (zetaB (lamb ρ κ σ) b b' W)) ∧
      BddL2 P (zPi σ κ ρ T u g πT (zetaB (lamb ρ κ σ) b b' W)) ∧
      BddL2 P (zX σ κ ρ T u g πT (zetaB (lamb ρ κ σ) b b' W)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun x => (hb x).continuousAt
  have hlb := lamb_pos (ρ := ρ) hκ hσ
  have hM := regular_wienerM hW hcont (lamb ρ κ σ) hbc hb'c
  have hζ2 : BddL2 P (zetaB (lamb ρ κ σ) b b' W) :=
    ⟨B ^ 2 / (2 * lamb ρ κ σ), fun t ht => integral_zetaB_sq_le hB hW hcont hlb hb hb'c hbB ht⟩
  have hreg : Regular (bmFiltrationReal W hW) (zetaB (lamb ρ κ σ) b b' W) :=
    ⟨fun ω => (by fun_prop : Continuous fun t : ℝ => Real.exp (-(lamb ρ κ σ * t))).mul (hM.1 ω),
      fun t => stronglyMeasurable_const.mul (hM.2 t)⟩
  refine ⟨isStochEqm_of_zeta hσ hκ T u g πT hreg.1
      (expDrift_zeta_of_martingale hlb hM.1 hM.2
        (fun s t hs hst => (martingale_wienerM hB hW hcont _ hb hb'c hs hst).2)
        hζ2.bddL1), ?_, ?_, ?_, ?_⟩
  · exact Regular.add (regular_det _ (wPi_continuous σ κ ρ T u g πT hκ hσ)) hreg
  · exact Regular.add (regular_det _ (wX_continuous σ κ ρ T u g πT hκ hσ))
      (Regular.const_mul hreg _)
  · exact BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).2) hζ2
  · exact BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).1) (BddL2.const_mul hζ2 _)

/-! ## Non-vacuity on the constructed Brownian motion -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder

/-- Cochrane (2023), §20.2.2, p. 475 (non-vacuity): on bmPath at the book's calibration
(`ρ = 0.05`, `σ = κ = 1`, `T = 5`, `u_r = −2%`, `g = 0`, `π_T = 0`), the loading `b = cos`
(innovation `dπ_t = cos(t) dW_t`) gives a regular, mean-square-bounded equilibrium. -/
theorem bmPath_loading_cos :
    IsStochEqm 1 (1 / 20) 1 gaussSeq (bmFiltrationReal bmPath measurable_bmPath) (fun _ => 0)
        (trapStep (-2 / 100) 5) (trapStep 0 5) (fun _ _ => 0)
        (zX 1 1 (1 / 20) 5 (-2 / 100) 0 0 (zetaB (lamb (1 / 20) 1 1) Real.cos
          (fun u => -Real.sin u) bmPath))
        (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (zetaB (lamb (1 / 20) 1 1) Real.cos
          (fun u => -Real.sin u) bmPath)) ∧
      BddL2 gaussSeq (zPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 (zetaB (lamb (1 / 20) 1 1) Real.cos
          (fun u => -Real.sin u) bmPath)) := by
  have h := isStochEqm_loading (P := gaussSeq) isPreBrownianReal_bmPath measurable_bmPath
    continuous_bmPath one_pos one_pos (ρ := 1 / 20) 5 (-2 / 100) 0 0 Real.hasDerivAt_cos
    (by fun_prop) (B := 1) fun u _ => Real.abs_cos_le_one u
  exact ⟨h.1, h.2.2.2.1⟩

end Cochrane.ZeroBound.TidyR8StochWerningMartingale
