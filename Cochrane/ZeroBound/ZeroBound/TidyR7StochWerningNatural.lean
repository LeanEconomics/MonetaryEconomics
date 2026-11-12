/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningSelect

/-!
# Natural-rate shocks during the zero-rate episode

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–475
(equations (20.5)–(20.10)), with the natural rate `u_r` now random: the step of the trap plus a
mean-reverting shock `ν`, `E_t dν = −ην dt` (`η > 0`; e.g. the Ornstein–Uhlenbeck shock
`dν = −ην dt + s dW`). The interest rate stays at zero.

The book's (20.8)–(20.10) solve the unstable combination `y = λ^f π − κx` forward against the
forcing `z = κσ(i − u_r)`. Under uncertainty the forward solution is taken in expectation, and
since `E_t ν_{t+τ} = e^{−ητ}ν_t` the response of `y` to the shock is
`−κσ∫_0^∞ e^{−(λ^f+η)τ}dτ = −κσ/(λ^f + η)`, exactly the deterministic response to news of a
natural-rate path `e^{−ητ}`.

## Main results

* `natD`: the response coefficient `d = −κσ/(λ^f + η)`, with `d(λ^f + η) = −κσ` (`natD_eq`).
* **`unstable_natural`**: in every regular `L¹`-bounded stochastic equilibrium with zero
  interest rate and natural rate `trapStep u T + ν`, at every date `s ≥ 0`, almost surely
  `λ^f π_s − κ x_s = (λ^f wPi(0)_s − κ wX(0)_s) + d ν_s`: the unstable combination is pinned
  state by state, and its response to the natural-rate shock is the deterministic response.
  With `ν = 0` this is TidyR7StochWerningTrap.x_eq_of_pi.
* The existence of such equilibria on a Brownian motion is TidyR7StochWerningNaturalExist.
-/

namespace Cochrane.ZeroBound.TidyR7StochWerningNatural

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningSelect

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Cochrane (2023), (20.8)–(20.10), p. 475, with a mean-reverting natural-rate shock: the
response of the unstable combination `λ^f π − κx` to the shock, `d = −κσ/(λ^f + η)`. -/
noncomputable def natD (σ κ ρ η : ℝ) : ℝ := -(κ * σ) / (lamf ρ κ σ + η)

/-- Cochrane (2023), (20.8)–(20.10), p. 475: `d(λ^f + η) = −κσ` for `η ≥ 0`. -/
theorem natD_eq {σ κ ρ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 ≤ η) :
    natD σ κ ρ η * (lamf ρ κ σ + η) = -(κ * σ) := by
  have := lamf_pos (ρ := ρ) hκ hσ
  unfold natD
  field_simp

/-- Cochrane (2023), §20.2.2, p. 475 (tool): if `f_t − f_s = ∫_s^t G` on `[s, ∞)` with `G`
integrable on every `[s, b]` and continuous at `t > s`, then `f'(t) = G(t)`.
Generalises `TidyR7StochWerning.hasDerivAt_of_intForm`. -/
theorem hasDerivAt_of_intForm_at {f G : ℝ → ℝ} {s t : ℝ}
    (hG : ∀ b, IntegrableOn G (Set.Icc s b)) (hf : ∀ t, s ≤ t → f t - f s = ∫ r in s..t, G r)
    (ht : s < t) (hGc : ContinuousAt G t) : HasDerivAt f (G t) t := by
  have hev : (fun u => f s + ∫ r in s..u, G r) =ᶠ[𝓝 t] f := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    linarith [hf u (le_of_lt hu)]
  have hint : IntervalIntegrable G volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).2
      ((hG t).mono_set Set.Ioc_subset_Icc_self)
  have hmeas : StronglyMeasurableAtFilter G (𝓝 t) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem (hG (t + 1)).aestronglyMeasurable
      (Icc_mem_nhds ht (lt_add_one t))
  exact ((intervalIntegral.integral_hasDerivAt_right hint hmeas hGc).const_add
    (f s)).congr_of_eventuallyEq hev.symm

/-- **Cochrane (2023), (20.8)–(20.10), p. 475, under natural-rate shocks: the unstable
combination is pinned state by state.** Let `ν` be a regular `L¹`-bounded shock with
`E_t dν = −ην dt` (`η ≥ 0`) and `(x, π)` a regular `L¹`-bounded stochastic equilibrium with
`i = 0`, natural rate `trapStep u T + ν` and disturbance `trapStep g T`. Then for every `s ≥ 0`,
almost surely, `λ^f π_s − κ x_s = (λ^f wPi(0)_s − κ wX(0)_s) + d ν_s` with
`d = −κσ/(λ^f + η)`.
Generalises `TidyR7StochWerningTrap.x_eq_of_pi` (the case `ν = 0`). -/
theorem unstable_natural [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν)
    (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) ν x π) {s : ℝ}
    (hs : 0 ≤ s) :
    (fun ω => lamf ρ κ σ * π s ω - κ * x s ω) =ᵐ[P] fun ω =>
      (lamf ρ κ σ * wPi σ κ ρ T u g 0 s - κ * wX σ κ ρ T u g 0 s) + natD σ κ ρ η * ν s ω := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hroot := lamf_root (ρ := ρ) hκ hσ
  have hd := natD_eq (ρ := ρ) hσ hκ hη
  set lf := lamf ρ κ σ
  set d := natD σ κ ρ η
  have key : ∀ A, MeasurableSet[𝓕 s] A →
      ∫ ω in A, (lf * π s ω - κ * x s ω) ∂P =
        ∫ ω in A, ((lf * (wPi σ κ ρ T u g 0) s - κ * (wX σ κ ρ T u g 0) s) + d * ν s ω) ∂P := by
    intro A hA
    set p := P.real A
    set mx : ℝ → ℝ := fun r => ∫ ω in A, x r ω ∂P
    set mπ : ℝ → ℝ := fun r => ∫ ω in A, π r ω ∂P
    set mν : ℝ → ℝ := fun r => ∫ ω in A, ν r ω ∂P
    have hbx : ∀ r, 0 ≤ r → |mx r| ≤ Kx := fun r hr => abs_setIntegral_le hKx A hr
    have hbπ : ∀ r, 0 ≤ r → |mπ r| ≤ Kπ := fun r hr => abs_setIntegral_le hKπ A hr
    have hbν : ∀ r, 0 ≤ r → |mν r| ≤ Kν := fun r hr => abs_setIntegral_le hKν A hr
    have hint : ∀ {Z : ℝ → Ω → ℝ} {K : ℝ}, (∀ ω, Continuous fun t => Z t ω) →
        (∀ t, Measurable (Z t)) → (∀ r, 0 ≤ r → |∫ ω in A, Z r ω ∂P| ≤ K) → ∀ b,
        IntegrableOn (fun r => ∫ ω in A, Z r ω ∂P) (Set.Icc s b) := fun hc hm hb b =>
      Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
        (stronglyMeasurable_setIntegral hc hm A).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => by
          rw [Real.norm_eq_abs]; exact hb r (hs.trans hr.1))
    have hix := hint hx.1 hmx hbx
    have hiπ := hint hπ.1 hmπ hbπ
    have hiν := hint hν.1 hmν hbν
    have itr : ∀ c b, IntegrableOn (trapStep c T) (Set.Icc s b) := fun c b =>
      trapStep_integrableOn c T measure_Icc_lt_top.ne
    -- integral forms
    have hcm := fun t (ht : s ≤ t) => condMean_integral_eq (P := P)
      (fun a b => integrableOn_zero) (fun a b => trapStep_integrableOn u T measure_Ioc_lt_top.ne)
      (fun a b => trapStep_integrableOn g T measure_Ioc_lt_top.ne) hν ⟨Kν, hKν⟩
      hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hs hA t ht
    simp only [mul_zero] at hcm
    have hfν : ∀ t, s ≤ t → mν t - mν s = ∫ r in s..t, -(η * mν r) := fun t ht => by
      have pν := integrable_prod_proc (P := P) hν.1 hmν hKν hs (b := t)
      rw [setIntegral_expDrift hνd hs ht hA (hKν s hs).1 (hKν t (hs.trans ht)).1
        (pν.const_mul η).neg]
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [integral_neg, integral_const_mul]
    have hGx : ∀ b, IntegrableOn (fun r => σ * (0 - mπ r - (p * trapStep u T r + mν r)))
        (Set.Icc s b) := fun b =>
      (((integrableOn_zero.sub (hiπ b)).sub (((itr u b).const_mul p).add (hiν b))).const_mul σ)
    have hGπ : ∀ b, IntegrableOn (fun r => ρ * mπ r - κ * (mx r + p * trapStep g T r))
        (Set.Icc s b) := fun b =>
      ((hiπ b).const_mul ρ).sub (((hix b).add ((itr g b).const_mul p)).const_mul κ)
    have hcx : ContinuousOn mx (Set.Ici s) := continuousOn_of_intForm hGx fun t ht => (hcm t ht).1
    have hcπ : ContinuousOn mπ (Set.Ici s) :=
      continuousOn_of_intForm hGπ fun t ht => (hcm t ht).2
    have hcν : ContinuousOn mν (Set.Ici s) :=
      continuousOn_of_intForm (fun b => ((hiν b).const_mul η).neg) hfν
    have hW0c := wPi_continuous σ κ ρ T u g 0 hκ hσ
    have hX0c := wX_continuous σ κ ρ T u g 0 hκ hσ
    -- the deviation of the unstable combination
    obtain ⟨⟨KX, hKX⟩, ⟨KW, hKW⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g 0
    have hp := wPath_isPath (ρ := ρ) hκ hσ T u g 0
    set F : ℝ → ℝ := fun r => lf * mπ r - κ * mx r -
      p * (lf * (wPi σ κ ρ T u g 0) r - κ * (wX σ κ ρ T u g 0) r) - d * mν r with hFdef
    have hFc : ContinuousOn F (Set.Ici s) :=
      (((continuousOn_const.mul hcπ).sub (continuousOn_const.mul hcx)).sub
        (continuousOn_const.mul ((continuousOn_const.mul hW0c.continuousOn).sub
          (continuousOn_const.mul hX0c.continuousOn)))).sub (continuousOn_const.mul hcν)
    have hFd : ∀ t, s < t → t ∉ ({T} : Set ℝ) → HasDerivAt F (lf * F t) t := by
      intro t ht htT
      have htT' : t ≠ T := htT
      have ca : ∀ {m : ℝ → ℝ}, ContinuousOn m (Set.Ici s) → ContinuousAt m t := fun hm =>
        hm.continuousAt (Ici_mem_nhds ht)
      have dx := hasDerivAt_of_intForm_at hGx (fun t ht => (hcm t ht).1) ht
        (((continuousAt_const.sub (ca hcπ)).sub (((trapStep_continuousAt u htT').const_mul
          p).add (ca hcν))).const_mul σ)
      have dπ := hasDerivAt_of_intForm_at hGπ (fun t ht => (hcm t ht).2) ht
        (((ca hcπ).const_mul ρ).sub (((ca hcx).add ((trapStep_continuousAt g htT').const_mul
          p)).const_mul κ))
      have dν := hasDerivAt_of_intForm_at (fun b => ((hiν b).const_mul η).neg) hfν ht
        ((ca hcν).const_mul η).neg
      obtain ⟨dX, dW⟩ := hp.2.2 t (hs.trans_lt ht) htT
      refine (((((dπ.const_mul lf).sub (dx.const_mul κ)).sub
        (((dW.const_mul lf).sub (dX.const_mul κ)).const_mul p)).sub
          (dν.const_mul d))).congr_deriv ?_
      simp only [F, Pi.neg_apply]
      linear_combination (-(mπ t - p * (wPi σ κ ρ T u g 0) t)) * hroot + mν t * hd
    have hzero := unstable_bdd_zero (f := F) (a := lf) (p := s) (S := {T})
      (K := lf * Kπ + κ * Kx + |p| * (lf * KW + κ * KX) + |d| * Kν)
      hf (Set.countable_singleton T) hFc hFd
      (fun t ht => by
        have h1 := hKW t (hs.trans ht)
        have h2 := hKX t (hs.trans ht)
        have b1 := hbπ t (hs.trans ht)
        have b2 := hbx t (hs.trans ht)
        have b3 := hbν t (hs.trans ht)
        have habs : ∀ a b c e f : ℝ, |lf * a - κ * b - p * (lf * c - κ * e) - d * f| ≤
            lf * |a| + κ * |b| + |p| * (lf * |c| + κ * |e|) + |d| * |f| := by
          intro a b c e f
          have e1 := abs_sub (lf * a - κ * b - p * (lf * c - κ * e)) (d * f)
          have e2 := abs_sub (lf * a - κ * b) (p * (lf * c - κ * e))
          have e3 := abs_sub (lf * a) (κ * b)
          have e4 := abs_sub (lf * c) (κ * e)
          rw [abs_mul p, abs_mul d] at *
          rw [abs_mul lf, abs_mul κ, abs_of_pos hf, abs_of_pos hκ] at e3
          rw [abs_mul lf, abs_mul κ, abs_of_pos hf, abs_of_pos hκ] at e4
          have e5 := mul_le_mul_of_nonneg_left e4 (abs_nonneg p)
          linarith
        refine (habs _ _ _ _ _).trans ?_
        gcongr)
      s le_rfl
    have e2 : F s = 0 := hzero
    simp only [F] at e2
    rw [integral_sub ((hKπ s hs).1.integrableOn.const_mul lf)
        ((hKx s hs).1.integrableOn.const_mul κ),
      integral_add (integrable_const _) ((hKν s hs).1.integrableOn.const_mul d),
      integral_const_mul, integral_const_mul, integral_const_mul, setIntegral_const, smul_eq_mul]
    linarith
  have hYm : StronglyMeasurable[𝓕 s] fun ω => lf * π s ω - κ * x s ω :=
    (stronglyMeasurable_const.mul (hπ.2 s)).sub (stronglyMeasurable_const.mul (hx.2 s))
  have hYi : Integrable (fun ω => lf * π s ω - κ * x s ω) P :=
    ((hKπ s hs).1.const_mul lf).sub ((hKx s hs).1.const_mul κ)
  have hZi : Integrable
      (fun ω => (lf * (wPi σ κ ρ T u g 0) s - κ * (wX σ κ ρ T u g 0) s) + d * ν s ω) P :=
    (integrable_const _).add ((hKν s hs).1.const_mul d)
  have h1 : (fun ω => (lf * (wPi σ κ ρ T u g 0) s - κ * (wX σ κ ρ T u g 0) s) + d * ν s ω) =ᵐ[P]
      P[fun ω => lf * π s ω - κ * x s ω | 𝓕 s] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hYi (fun _ _ _ => hZi.integrableOn)
      (fun A hA _ => (key A hA).symm)
      (stronglyMeasurable_const.add (stronglyMeasurable_const.mul (hν.2 s))).aestronglyMeasurable
  rw [condExp_of_stronglyMeasurable (𝓕.le s) hYm hYi] at h1
  exact h1.symm

end Cochrane.ZeroBound.TidyR7StochWerningNatural
