/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdTVC

/-!
# The transversality condition for utilities on a convex domain

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, p. 439 ("their optimal
choices include transversality conditions") and (19.28), p. 449. `TidyR6HouseholdTVC.tvc_general`
assumed the utility concave and increasing along the bundle direction on whole lines of `ℝ²`, which
excludes `log c` and `c^{1−σ}/(1−σ)` with `σ > 1` (defined only for `c > 0`). This module shows
that concavity and monotonicity are used only on two kinds of segments — from the plan to the
reference plan, and from the plan to the Kamihigashi step — and restates the theorem accordingly.

## Main results

* `concave_chord_seg`, `concave_slope_anti_seg`, `tangent_seg`, `abs_comb_seg`: chords, slopes,
  tangent bound and an absolute bound for a function concave (or monotone) on a segment
  `[0, X]`; the tangent bound uses only the derivative at the end point `0`.
* **`tvc_seg`**: the transversality condition with concavity and monotonicity along the bundle
  required only on the segments from the plan to the reference plan and to the step, and with the
  integrable Kamihigashi step replaced by "integrable step **or** nonnegative freed wealth
  `k_T/w_T ≥ 0`" (when the household carries no net debt out of `T`, the step's utility lies
  between `u(c_T, m_T)` and its tangent bound, so it is automatically integrable).
* `line_fst`, `mem_line_fst`, `line_cons`, `mem_shift`: concavity and monotonicity of a utility
  concave on a convex domain (in `ℝ²` for money in utility, in `ℝ` for cash in advance) restricted
  to a segment of the bundle line whose end points are in the domain.
* **`miu_tvc_dom`**: the money-in-utility transversality condition for a utility `C¹` and concave
  on an open **convex** domain `U` and increasing in consumption there: no extension to `ℝ²` is
  needed; the reference plan and the step must lie in `U`.
* **`cia_tvc_dom`**: the cash-in-advance version for `u` `C¹`, concave and increasing on an open
  interval `I`; `log_hypotheses` checks that `u = log` on `(0, ∞)` satisfies all utility
  hypotheses.
* `mRef_nonneg`, `step_money_nonneg`: primitive sufficient conditions for the reference money and
  the step money to be nonnegative (velocity `V ≤ 1`, nonnegative endowment, reference
  consumption and freed wealth).

## What remains assumed, and why

* Concavity along the bundle on the plan–reference and plan–step segments. Without it the
  Kamihigashi bound `(u(c + θd) − u(c))/θ ≥ u(c + d) − u(c)` on the tail fails, and only the
  liminf form of the transversality condition (`TidyR6HouseholdFOC.miu_liminf_tvc`,
  `TidyR6HouseholdCIAKKT.cia_liminf_tvc`) survives. A counterexample to the limit form would need an
  optimum at which the first-order condition holds with `λ > 0` while wealth oscillates; with an
  admissible reference plan this forces consumption to oscillate unboundedly with summable utility,
  and certifying optimality of such a plan requires a global supergradient at the plan, which
  makes utility grow linearly and destroys summability. Every candidate constructed so far
  (utilities flat below a threshold, bounded utilities, convex–concave kinks) admitted a profitable
  deviation that sacrifices consumption at one late date, so it was not an optimum. Neither a
  proof nor a counterexample is known.
* Admissibility of the reference plan: necessary (`TidyR6HouseholdTVCCx.tvc_needs_reference`).
* The step in the domain, the reference and step money nonnegative (cash-in-advance): these say
  that the Kamihigashi deviation is in the choice set; `mRef_nonneg` and `step_money_nonneg` give
  primitive sufficient conditions. Their necessity is not shown.
-/

namespace Cochrane.Monetarism.TidyR6HouseholdTVCDom

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  HouseholdMeasureTVC TidyR6HouseholdRoll TidyR6HouseholdSuff TidyR6HouseholdTVC

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Concave and monotone functions on a segment -/

/-- Cochrane (2023), p. 439 (concavity along the bundle, on a segment): for `g` concave on
`[0, tX]` (unordered interval) and `0 ≤ θ ≤ t`, `t > 0`,
`(1 − θ/t)g(0) + (θ/t)g(tX) ≤ g(θX)`. -/
theorem concave_chord_seg {g : ℝ → ℝ} {θ t X : ℝ} (hc : ConcaveOn ℝ (Set.uIcc 0 (t * X)) g)
    (h0 : 0 ≤ θ) (hθt : θ ≤ t) (ht : 0 < t) :
    (1 - θ / t) * g 0 + θ / t * g (t * X) ≤ g (θ * X) := by
  have ha : 0 ≤ 1 - θ / t := by rw [sub_nonneg, div_le_one ht]; exact hθt
  have hb : 0 ≤ θ / t := div_nonneg h0 ht.le
  have := hc.2 Set.left_mem_uIcc Set.right_mem_uIcc ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at this
  convert this using 2
  field_simp

/-- Cochrane (2023), p. 439: `sX` lies between `0` and `tX` when `0 ≤ s ≤ t`. -/
theorem mem_uIcc_mul {s t X : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : s * X ∈ Set.uIcc 0 (t * X) := by
  rw [Set.mem_uIcc]
  rcases le_total 0 X with hX | hX
  · left
    exact ⟨mul_nonneg hs hX, mul_le_mul_of_nonneg_right hst hX⟩
  · right
    exact ⟨mul_le_mul_of_nonpos_right hst hX, mul_nonpos_of_nonneg_of_nonpos hs hX⟩

/-- Cochrane (2023), p. 439: for `g` concave on `[0, t₀X]` the slope `(g(sX) − g(0))/s` decreases
in `s ∈ (0, t₀]`. -/
theorem concave_slope_anti_seg {g : ℝ → ℝ} {s t t₀ X : ℝ}
    (hc : ConcaveOn ℝ (Set.uIcc 0 (t₀ * X)) g) (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ t₀) :
    (g (t * X) - g 0) / t ≤ (g (s * X) - g 0) / s := by
  have htpos : 0 < t := lt_of_lt_of_le hs hst
  have hsub : Set.uIcc 0 (t * X) ⊆ Set.uIcc 0 (t₀ * X) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (mem_uIcc_mul htpos.le ht)
  have h := concave_chord_seg (hc.subset hsub (Set.ordConnected_uIcc.convex)) hs.le hst htpos
  rw [div_le_div_iff₀ htpos hs]
  have e : (1 - s / t) * g 0 + s / t * g (t * X) = g 0 + s / t * (g (t * X) - g 0) := by ring
  rw [e] at h
  have h2 : s / t * (g (t * X) - g 0) * t = s * (g (t * X) - g 0) := by field_simp
  nlinarith

/-- Cochrane (2023), (19.13), p. 440 (tangent bound on a segment): for `g` concave on
`[0, t₀X]` and differentiable at `0` with derivative `V`, `g(θX) ≤ g(0) + θVX` for
`0 ≤ θ ≤ t₀`. -/
theorem tangent_seg {g : ℝ → ℝ} {V θ t₀ X : ℝ} (hc : ConcaveOn ℝ (Set.uIcc 0 (t₀ * X)) g)
    (hg : HasDerivAt g V 0) (h0 : 0 ≤ θ) (h1 : θ ≤ t₀) :
    g (θ * X) ≤ g 0 + θ * (V * X) := by
  rcases h0.lt_or_eq with hθ | hθ
  · have hlim := slope_tendsto hg hθ X
    have hge : ∀ k : ℕ, (g (θ * X) - g 0) / θ ≤
        (g (θ / ((k : ℝ) + 1) * X) - g 0) / (θ / ((k : ℝ) + 1)) := fun k =>
      concave_slope_anti_seg hc (by positivity)
        (div_le_self hθ.le (by linarith [k.cast_nonneg (α := ℝ)])) h1
    have := ge_of_tendsto' hlim hge
    rw [div_le_iff₀ hθ] at this
    linarith
  · subst hθ
    simp

/-- Cochrane (2023), p. 439: for `g` monotone on `[0, d]` and `0 ≤ θ ≤ 1`,
`|g(θd)| ≤ |g(0)| + |g(d)|` (the value lies between the end values). -/
theorem abs_comb_seg {g : ℝ → ℝ} {d θ : ℝ} (hm : MonotoneOn g (Set.uIcc 0 d)) (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) : |g (θ * d)| ≤ |g 0| + |g d| := by
  have hmem : θ * d ∈ Set.uIcc 0 d := by
    have := mem_uIcc_mul (X := d) h0 h1
    rwa [one_mul] at this
  rcases le_total 0 d with hd | hd
  · have l : g 0 ≤ g (θ * d) := hm Set.left_mem_uIcc hmem (mul_nonneg h0 hd)
    have r : g (θ * d) ≤ g d := hm hmem Set.right_mem_uIcc (by nlinarith)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (g 0), le_abs_self (g d), abs_nonneg (g 0),
      abs_nonneg (g d)]
  · have l : g d ≤ g (θ * d) := hm Set.right_mem_uIcc hmem (by nlinarith)
    have r : g (θ * d) ≤ g 0 := hm hmem Set.left_mem_uIcc (mul_nonpos_of_nonneg_of_nonpos h0 hd)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (g d), le_abs_self (g 0), abs_nonneg (g 0),
      abs_nonneg (g d)]

/-! ### The transversality condition with concavity on segments -/

/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions") and
(19.28), p. 449, **the transversality condition with concavity only on segments.** As
`TidyR6HouseholdTVC.tvc_general`, but the utility `e ↦ u(c_n + e, m_n + ϑe)` need only be concave
and increasing on the segment from `0` to the reference change `cRef_n − c_n` (every date) and
on the segment from `0` to the Kamihigashi step `θ₀x_T` (every date), almost surely; and the step
need only have integrable utility **or** the freed wealth `x_T = k_T/w_T` be nonnegative. -/
theorem tvc_seg {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {ϑ : ℝ}
    (hum : Measurable fun p : ℝ × ℝ => u p.1 p.2)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ ≤ 1)
    {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hopt : Optimal S β u Con Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s)
    (hw : ∀ n, ∀ᵐ ω ∂S.μ, wedge S ϑ Λ P n ω ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hder : ∀ T, ∀ᵐ ω ∂S.μ, HasDerivAt (fun e => u (c T ω + e) (m T ω + ϑ * e))
      (uc (c T ω) (m T ω) + ϑ * um (c T ω) (m T ω)) 0)
    (hfoc : ∀ T, ∀ᵐ ω ∂S.μ, β ^ T * (uc (c T ω) (m T ω) + ϑ * um (c T ω) (m T ω)) =
      lam * (Λ T ω * wedge S ϑ Λ P T ω))
    (href : UAdmissible S β
      (fun n ω => u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω)))
    (hRc : ∀ n, Integrable (fun ω => Λ n ω * (cRef S ϑ Λ P y s c m n ω - c n ω)) S.μ)
    (hRm : ∀ n, Integrable (fun ω => pk Λ P (n + 1) ω *
      (P n ω * (ϑ * (cRef S ϑ Λ P y s c m n ω - c n ω)))) S.μ)
    (hXc : ∀ T, Integrable (fun ω => Λ T ω * kx S ϑ Λ P a m T ω) S.μ)
    (hXm : ∀ T, Integrable (fun ω => pk Λ P (T + 1) ω * (P T ω * (ϑ * kx S ϑ Λ P a m T ω))) S.μ)
    (hsegT : ∀ T, ∀ᵐ ω ∂S.μ,
      ConcaveOn ℝ (Set.uIcc 0 (θ₀ * kx S ϑ Λ P a m T ω)) (fun e => u (c T ω + e) (m T ω + ϑ * e))
      ∧ MonotoneOn (fun e => u (c T ω + e) (m T ω + ϑ * e))
        (Set.uIcc 0 (θ₀ * kx S ϑ Λ P a m T ω)))
    (hsegR : ∀ n, ∀ᵐ ω ∂S.μ, ConcaveOn ℝ (Set.uIcc 0 (cRef S ϑ Λ P y s c m n ω - c n ω))
      (fun e => u (c n ω + e) (m n ω + ϑ * e)) ∧ MonotoneOn (fun e => u (c n ω + e)
        (m n ω + ϑ * e)) (Set.uIcc 0 (cRef S ϑ Λ P y s c m n ω - c n ω)))
    (hstep : ∀ T, Integrable (fun ω => u (c T ω + θ₀ * kx S ϑ Λ P a m T ω)
      (m T ω + ϑ * (θ₀ * kx S ϑ Λ P a m T ω))) S.μ ∨ ∀ᵐ ω ∂S.μ, 0 ≤ kx S ϑ Λ P a m T ω)
    (hcon : ∀ T θ, 0 < θ → θ < θ₀ → Con (fun n ω => c n ω + θ * kdc S ϑ Λ P y s a c m T n ω)
      (fun n ω => m n ω + θ * (ϑ * kdc S ϑ Λ P y s a c m T n ω))) :
    Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  obtain ⟨hfeas, -, hadm, hmax⟩ := hopt
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  have mz : ∀ {n : ℕ} {h : Ω → ℝ}, StronglyMeasurable[S.𝓕 n] h → Measurable h :=
    fun {n} _ h => (h.mono (S.𝓕.le n)).measurable
  set d : ℕ → ℝ := fun n => β ^ n * (∫ ω, u (c n ω) (m n ω) ∂S.μ -
    ∫ ω, u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω) ∂S.μ) with hd
  have hds : Summable d :=
    ((hadm.hasSum hβ).sub (href.hasSum hβ)).summable.congr fun n => by simp only [hd]; ring
  set R : ℕ → ℝ := fun T => ∑' n, if T < n then d n else 0 with hR
  have hRT : ∀ T, HasSum (fun n => if T < n then d n else 0) (R T) := fun T =>
    (hasSum_ite_lt hds T).summable.hasSum
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have e : ∀ T, R T = ∑' n, d n - ∑ n ∈ Finset.range (T + 1), d n := fun T =>
      (hasSum_ite_lt hds T).tsum_eq
    have := (tendsto_const_nhds (x := ∑' n, d n)).sub
      (hds.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
    rw [sub_self] at this
    exact this.congr fun T => (e T).symm
  -- the key bound at each date
  have key : ∀ T, lam * wealthPV S Λ P N0 m a (T + 1) ≤ R T := by
    intro T
    set x := kx S ϑ Λ P a m T with hx
    have hxm : Measurable x := mz (sm_kx hp hma T)
    set g : Ω → ℝ → ℝ := fun ω e => u (c T ω + e) (m T ω + ϑ * e) with hg
    set V : Ω → ℝ := fun ω => uc (c T ω) (m T ω) + ϑ * um (c T ω) (m T ω) with hV
    have hg0 : ∀ ω, g ω 0 = u (c T ω) (m T ω) := fun ω => by simp [hg]
    -- the value of the freed wealth
    obtain ⟨hkI, hkE⟩ := lam_kOut hp hfeas T
    have hVx : (fun ω => β ^ T * (V ω * x ω)) =ᵐ[S.μ] fun ω => lam * (Λ T ω * kOut S Λ P a m T ω)
        := by
      filter_upwards [hfoc T, hw T] with ω h1 h2
      simp only [hV, hx, kx]
      rw [← mul_assoc, h1]
      field_simp
    have hVxi : Integrable (fun ω => V ω * x ω) S.μ := by
      have := (hkI.const_mul lam).congr hVx.symm
      refine (this.const_mul (β ^ T)⁻¹).congr (Eventually.of_forall fun ω => ?_)
      have := pow_pos hβ T
      field_simp
    -- the integrands along the step
    have hgm : ∀ θ : ℝ, Measurable fun ω => g ω (θ * x ω) := fun θ =>
      hum.comp (((mz (hca T)).add (hxm.const_mul θ)).prodMk
        ((mz (hma T)).add ((hxm.const_mul θ).const_mul ϑ)))
    have hstepI : Integrable (fun ω => g ω (θ₀ * x ω)) S.μ := by
      rcases hstep T with h | h
      · exact h
      · have hU : Integrable (fun ω => g ω 0 + θ₀ * (V ω * x ω)) S.μ :=
          ((hadm.integrable hβ T).add (hVxi.const_mul θ₀)).congr
            (Eventually.of_forall fun ω => by simp only [Pi.add_apply, hg0])
        have hL : Integrable (fun ω => g ω 0) S.μ := (hadm.integrable hβ T).congr
          (Eventually.of_forall fun ω => (hg0 ω).symm)
        refine Integrable.mono' (hL.abs.add hU.abs) (hgm θ₀).aestronglyMeasurable ?_
        filter_upwards [hder T, hsegT T, h] with ω hdω hseg hx0
        have up := tangent_seg hseg.1 hdω hθ₀.le le_rfl
        have lo : g ω 0 ≤ g ω (θ₀ * x ω) := hseg.2 Set.left_mem_uIcc Set.right_mem_uIcc
          (mul_nonneg hθ₀.le hx0)
        simp only [Pi.add_apply]
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · linarith [neg_abs_le (g ω 0), abs_nonneg (g ω 0 + θ₀ * (V ω * x ω))]
        · linarith [le_abs_self (g ω 0 + θ₀ * (V ω * x ω)), abs_nonneg (g ω 0)]
    have hgint : ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ₀ → Integrable (fun ω => g ω (θ * x ω)) S.μ := by
      intro θ h0 h1
      have hL : Integrable (fun ω => (1 - θ / θ₀) * g ω 0 + θ / θ₀ * g ω (θ₀ * x ω)) S.μ := by
        refine (((hadm.integrable hβ T).const_mul (1 - θ / θ₀)).add
          (hstepI.const_mul (θ / θ₀))).congr (Eventually.of_forall fun ω => ?_)
        simp only [Pi.add_apply, hg, add_zero, mul_zero]
      have hU : Integrable (fun ω => g ω 0 + θ * (V ω * x ω)) S.μ :=
        ((hadm.integrable hβ T).add (hVxi.const_mul θ)).congr
          (Eventually.of_forall fun ω => by simp only [Pi.add_apply, hg0])
      refine Integrable.mono' (hL.abs.add hU.abs) (hgm θ).aestronglyMeasurable ?_
      filter_upwards [hder T, hsegT T] with ω hdω hseg
      simp only [Pi.add_apply]
      have lo := concave_chord_seg hseg.1 h0 h1 hθ₀
      have up := tangent_seg hseg.1 hdω h0 h1
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le ((1 - θ / θ₀) * g ω 0 + θ / θ₀ * g ω (θ₀ * x ω)),
          abs_nonneg (g ω 0 + θ * (V ω * x ω))]
      · have : g ω (θ * x ω) ≤ g ω 0 + θ * (V ω * x ω) := up
        linarith [le_abs_self (g ω 0 + θ * (V ω * x ω)),
          abs_nonneg ((1 - θ / θ₀) * g ω 0 + θ / θ₀ * g ω (θ₀ * x ω))]
    -- the optimality inequality for a step `θ`
    have hstepIneq : ∀ θ : ℝ, 0 < θ → θ < θ₀ →
        β ^ T * (∫ ω, g ω (θ * x ω) ∂S.μ - ∫ ω, u (c T ω) (m T ω) ∂S.μ) ≤ θ * R T := by
      intro θ h0 h1
      have hθ1 : θ ≤ 1 := (h1.le.trans hθ₀1)
      have hIC : ∀ n, Integrable (fun ω => Λ n ω * kdc S ϑ Λ P y s a c m T n ω) S.μ := by
        intro n
        by_cases h1 : n < T
        · simp [kdc, h1]
        · by_cases h2 : n = T
          · subst h2
            simpa [kdc] using hXc n
          · simpa [kdc, h1, h2] using hRc n
      have hIM : ∀ n, Integrable (fun ω => pk Λ P (n + 1) ω *
          (P n ω * (ϑ * kdc S ϑ Λ P y s a c m T n ω))) S.μ := by
        intro n
        by_cases h1 : n < T
        · simp [kdc, h1]
        · by_cases h2 : n = T
          · subst h2
            simpa [kdc] using hXm n
          · simpa [kdc, h1, h2] using hRm n
      have hF := kam_feasible_w hp hfeas hya hsa hw T hIC hIM h0.le hθ1
      set f' : ℕ → Ω → ℝ := fun n ω => u (c n ω + θ * kdc S ϑ Λ P y s a c m T n ω)
        (m n ω + θ * (ϑ * kdc S ϑ Λ P y s a c m T n ω)) with hf'
      have hf'lt : ∀ n, n < T → ∀ ω, f' n ω = u (c n ω) (m n ω) := fun n hn ω => by
        simp [hf', kdc, hn]
      have hf'T : ∀ ω, f' T ω = g ω (θ * x ω) := fun ω => by
        simp only [hf', hg, kdc, lt_irrefl, ↓reduceIte, hx]
        ring_nf
      have hcR : ∀ n ω, cRef S ϑ Λ P y s c m n ω =
          c n ω + (cRef S ϑ Λ P y s c m n ω - c n ω) := fun n ω => by ring
      have hmR : ∀ n ω, mRef S ϑ Λ P y s c m n ω =
          m n ω + ϑ * (cRef S ϑ Λ P y s c m n ω - c n ω) := fun n ω => rfl
      have hf'gt : ∀ n, T < n → ∀ ω, f' n ω = u (c n ω + θ * (cRef S ϑ Λ P y s c m n ω - c n ω))
          (m n ω + ϑ * (θ * (cRef S ϑ Λ P y s c m n ω - c n ω))) := fun n hn ω => by
        simp only [hf', kdc, show ¬ n < T by omega, show n ≠ T by omega, ↓reduceIte]
        ring_nf
      -- admissibility of the deviation
      have hadm' : UAdmissible S β f' := by
        refine uadm_of_le hβ hadm href (hgint θ h0.le h1.le) (T := T) (fun n => ?_) (fun n => ?_)
        · exact (hum.comp (((mz (hca n)).add
            ((mz (sm_kdc hp hya hsa hca hma T n)).const_mul θ)).prodMk ((mz (hma n)).add
            (((mz (sm_kdc hp hya hsa hca hma T n)).const_mul ϑ).const_mul θ)))).aestronglyMeasurable
        · filter_upwards [hsegR n] with ω hseg
          rcases lt_trichotomy n T with hn | hn | hn
          · rw [hf'lt n hn ω]
            simp only [show n ≠ T by omega, ↓reduceIte, add_zero]
            linarith [abs_nonneg (u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω))]
          · subst hn
            rw [hf'T ω]
            simp only [↓reduceIte]
            linarith [abs_nonneg (u (c n ω) (m n ω)),
              abs_nonneg (u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω))]
          · rw [hf'gt n hn ω]
            simp only [show n ≠ T by omega, ↓reduceIte, add_zero]
            have := abs_comb_seg hseg.2 h0.le hθ1
            simp only [mul_zero, add_zero] at this
            rw [show c n ω + (cRef S ϑ Λ P y s c m n ω - c n ω) = cRef S ϑ Λ P y s c m n ω by
              ring] at this
            rw [hmR n ω]
            exact this
      have hle := hmax _ _ _ hF (hcon T θ h0 h1) hadm'
      -- compare the two series of expected utilities
      set D : ℕ → ℝ := fun n => β ^ n * ∫ ω, f' n ω ∂S.μ - β ^ n * ∫ ω, u (c n ω) (m n ω) ∂S.μ
        with hD
      have hDs : HasSum D (expU S β f' - expU S β (fun n ω => u (c n ω) (m n ω))) :=
        (hadm'.hasSum hβ).sub (hadm.hasSum hβ)
      set E : ℕ → ℝ := fun n => (if n = T then β ^ T * (∫ ω, g ω (θ * x ω) ∂S.μ -
        ∫ ω, u (c T ω) (m T ω) ∂S.μ) else 0) - θ * (if T < n then d n else 0) with hE
      have hEs : HasSum E (β ^ T * (∫ ω, g ω (θ * x ω) ∂S.μ - ∫ ω, u (c T ω) (m T ω) ∂S.μ) -
          θ * R T) := (hasSum_ite_eq T _).sub ((hRT T).mul_left θ)
      have hED : ∀ n, E n ≤ D n := by
        intro n
        rcases lt_trichotomy n T with hn | hn | hn
        · simp only [hE, hD, show n ≠ T by omega, show ¬ T < n by omega, ↓reduceIte,
            mul_zero, sub_zero]
          rw [integral_congr_ae (Eventually.of_forall (hf'lt n hn)), sub_self]
        · subst hn
          simp only [hE, hD, ↓reduceIte, lt_irrefl, mul_zero, sub_zero]
          rw [integral_congr_ae (Eventually.of_forall hf'T), mul_sub]
        · simp only [hE, hD, show n ≠ T by omega, hn, ↓reduceIte, zero_sub, hd]
          have hi' := hadm'.integrable hβ n
          have hi := hadm.integrable hβ n
          have hir := href.integrable hβ n
          have hpt : ∀ᵐ ω ∂S.μ, (1 - θ) * u (c n ω) (m n ω) + θ *
              u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω) ≤ f' n ω := by
            filter_upwards [hsegR n] with ω hseg
            have := hseg.1.2 Set.left_mem_uIcc Set.right_mem_uIcc (sub_nonneg.2 hθ1) h0.le
              (by ring)
            simp only [smul_eq_mul, mul_zero, zero_add, add_zero] at this
            rw [show c n ω + (cRef S ϑ Λ P y s c m n ω - c n ω) = cRef S ϑ Λ P y s c m n ω by
              ring] at this
            rw [hf'gt n hn ω, hmR n ω]
            exact this
          have hint2 : Integrable (fun ω => (1 - θ) * u (c n ω) (m n ω) + θ *
              u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω)) S.μ :=
            (hi.const_mul (1 - θ)).add (hir.const_mul θ)
          have hmono' := integral_mono_ae hint2 hi' hpt
          rw [integral_add (hi.const_mul _) (hir.const_mul _), integral_const_mul,
            integral_const_mul] at hmono'
          have hb := pow_pos hβ n
          nlinarith
      have := hasSum_le hED hEs hDs
      linarith
    -- the monotone limit of the difference quotients
    set θk : ℕ → ℝ := fun k => θ₀ / 2 / ((k : ℝ) + 1) with hθk
    have hθk0 : ∀ k, 0 < θk k := fun k => by positivity
    have hθk1 : ∀ k, θk k < θ₀ := fun k => by
      have : θ₀ / 2 / ((k : ℝ) + 1) ≤ θ₀ / 2 :=
        div_le_self (by positivity) (by linarith [k.cast_nonneg (α := ℝ)])
      linarith
    set q : ℕ → Ω → ℝ := fun k ω => (g ω (θk k * x ω) - g ω 0) / θk k with hq
    have hqi : ∀ k, Integrable (q k) S.μ := fun k =>
      ((hgint (θk k) (hθk0 k).le (hθk1 k).le).sub ((hadm.integrable hβ T).congr
        (Eventually.of_forall fun ω => (hg0 ω).symm))).div_const _
    have hqle : ∀ k, β ^ T * ∫ ω, q k ω ∂S.μ ≤ R T := by
      intro k
      have h := hstepIneq (θk k) (hθk0 k) (hθk1 k)
      have e : ∫ ω, q k ω ∂S.μ = (∫ ω, g ω (θk k * x ω) ∂S.μ - ∫ ω, u (c T ω) (m T ω) ∂S.μ) /
          θk k := by
        simp only [hq]
        rw [integral_div, integral_sub (hgint _ (hθk0 k).le (hθk1 k).le)
          ((hadm.integrable hβ T).congr (Eventually.of_forall fun ω => (hg0 ω).symm))]
        simp only [hg0]
      rw [e, mul_div_assoc', div_le_iff₀ (hθk0 k)]
      linarith
    have hmonoq : ∀ᵐ ω ∂S.μ, Monotone fun k => q k ω := by
      filter_upwards [hsegT T] with ω hseg
      refine monotone_nat_of_le_succ fun k => ?_
      simp only [hq]
      refine concave_slope_anti_seg hseg.1 (hθk0 (k + 1)) ?_ (hθk1 k).le
      simp only [hθk]
      push_cast
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hlimq : ∀ᵐ ω ∂S.μ, Tendsto (fun k => q k ω) atTop (𝓝 (V ω * x ω)) := by
      filter_upwards [hder T] with ω hdω
      exact slope_tendsto hdω (by positivity : (0 : ℝ) < θ₀ / 2) (x ω)
    have hint := integral_tendsto_of_tendsto_of_monotone hqi hVxi hmonoq hlimq
    have hle : β ^ T * ∫ ω, V ω * x ω ∂S.μ ≤ R T :=
      le_of_tendsto' (hint.const_mul (β ^ T)) hqle
    have e2 : β ^ T * ∫ ω, V ω * x ω ∂S.μ = lam * wealthPV S Λ P N0 m a (T + 1) := by
      rw [← integral_const_mul, integral_congr_ae hVx, integral_const_mul, hkE]
    linarith
  -- conclusion
  have h1 : Tendsto (fun T => wealthPV S Λ P N0 m a (T + 1)) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have := hnp (-b / 2) (by linarith)
      filter_upwards [(tendsto_add_atTop_nat 1).eventually this] with T hT
      linarith
    · filter_upwards [(tendsto_order.1 hRlim).2 (lam * b) (by positivity)] with T hT
      have := key T
      by_contra hcon'
      rw [not_lt] at hcon'
      nlinarith
  exact (tendsto_add_atTop_iff_nat 1).1 h1


/-! ### Utilities on a convex domain -/

/-- Cochrane (2023), (19.9), p. 439: on a convex set `I ⊆ ℝ` containing `c` and `c + X`, the
whole segment `c + [0, X]` lies in `I`. -/
theorem mem_shift {I : Set ℝ} (hI : Convex ℝ I) {c X e : ℝ} (h0 : c ∈ I) (h1 : c + X ∈ I)
    (he : e ∈ Set.uIcc 0 X) : c + e ∈ I := by
  refine hI.segment_subset h0 h1 ?_
  rw [segment_eq_uIcc, Set.mem_uIcc]
  rcases Set.mem_uIcc.1 he with ⟨a, b⟩ | ⟨a, b⟩
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

/-- Cochrane (2023), (19.9), p. 439: on a convex set `U ⊆ ℝ²` containing `(x, z)` and
`(x + X, z)`, the whole segment `(x + [0, X], z)` lies in `U`. -/
theorem mem_line_fst {U : Set (ℝ × ℝ)} (hU : Convex ℝ U) {x z X e : ℝ} (h0 : (x, z) ∈ U)
    (h1 : (x + X, z) ∈ U) (he : e ∈ Set.uIcc 0 X) : (x + e, z) ∈ U := by
  by_cases hX : X = 0
  · subst hX
    have : e = 0 := by
      rcases Set.mem_uIcc.1 he with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
    subst this
    simpa using h0
  · have hl : 0 ≤ e / X ∧ e / X ≤ 1 := by
      rcases lt_or_gt_of_ne hX with hneg | hpos
      · rcases Set.mem_uIcc.1 he with ⟨a, b⟩ | ⟨a, b⟩
        · exact absurd (lt_of_le_of_lt (a.trans b) hneg) (lt_irrefl 0)
        · exact ⟨div_nonneg_of_nonpos b hneg.le, (div_le_one_of_neg hneg).2 a⟩
      · rcases Set.mem_uIcc.1 he with ⟨a, b⟩ | ⟨a, b⟩
        · exact ⟨div_nonneg a hpos.le, (div_le_one hpos).2 b⟩
        · exact absurd (lt_of_lt_of_le hpos (a.trans b)) (lt_irrefl 0)
    have := hU h0 h1 (sub_nonneg.2 hl.2) hl.1 (by ring)
    have heq : ((1 - e / X) • (x, z) + (e / X) • (x + X, z) : ℝ × ℝ) = (x + e, z) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
        ring
    rwa [heq] at this

/-- Cochrane (2023), (19.9), p. 439 (money in utility, bundle `ϑ = 0`): for `u` concave on the
convex set `U` and increasing in consumption within `U`, and `(x, z)`, `(x + X, z)` in `U`, the
function `e ↦ u(x + e, z + 0·e)` is concave and increasing on `[0, X]`. -/
theorem line_fst {u : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : Convex ℝ U)
    (hconc : ConcaveOn ℝ U (fun p : ℝ × ℝ => u p.1 p.2))
    (hmono : ∀ x x' z, (x, z) ∈ U → (x', z) ∈ U → x ≤ x' → u x z ≤ u x' z) {x z X : ℝ}
    (h0 : (x, z) ∈ U) (h1 : (x + X, z) ∈ U) :
    ConcaveOn ℝ (Set.uIcc 0 X) (fun e => u (x + e) (z + 0 * e)) ∧
      MonotoneOn (fun e => u (x + e) (z + 0 * e)) (Set.uIcc 0 X) := by
  refine ⟨⟨convex_uIcc 0 X, fun e₁ he₁ e₂ he₂ a b ha hb hab => ?_⟩, fun e₁ he₁ e₂ he₂ h => ?_⟩
  · have := hconc.2 (mem_line_fst hU h0 h1 he₁) (mem_line_fst hU h0 h1 he₂) ha hb hab
    have hpt : a • ((x + e₁, z) : ℝ × ℝ) + b • (x + e₂, z) = (x + (a * e₁ + b * e₂), z) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
        linear_combination x * hab
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
        linear_combination z * hab
    rw [hpt] at this
    simpa [smul_eq_mul] using this
  · simp only [zero_mul, add_zero]
    exact hmono _ _ _ (mem_line_fst hU h0 h1 he₁) (mem_line_fst hU h0 h1 he₂) (by linarith)

/-- Cochrane (2023), §19.5.1, p. 448: for `u` concave and increasing on the convex set `I ⊆ ℝ`
and `c`, `c + X` in `I`, the function `e ↦ u(c + e)` (any bundle money change) is concave and
increasing on `[0, X]`. -/
theorem line_cons {u : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I) (hconc : ConcaveOn ℝ I u)
    (hmono : MonotoneOn u I) {c X : ℝ} (h0 : c ∈ I) (h1 : c + X ∈ I) (z ϑ : ℝ) :
    ConcaveOn ℝ (Set.uIcc 0 X) (fun e => (fun x _ => u x : ℝ → ℝ → ℝ) (c + e) (z + ϑ * e)) ∧
      MonotoneOn (fun e => (fun x _ => u x : ℝ → ℝ → ℝ) (c + e) (z + ϑ * e))
        (Set.uIcc 0 X) := by
  refine ⟨⟨convex_uIcc 0 X, fun e₁ he₁ e₂ he₂ a b ha hb hab => ?_⟩, fun e₁ he₁ e₂ he₂ h => ?_⟩
  · have := hconc.2 (mem_shift hI h0 h1 he₁) (mem_shift hI h0 h1 he₂) ha hb hab
    simp only [smul_eq_mul] at this ⊢
    convert this using 2
    linear_combination (-c) * hab
  · exact hmono (mem_shift hI h0 h1 he₁) (mem_shift hI h0 h1 he₂) (by linarith)

/-- Cochrane (2023), §19.5.1, p. 448: `u = log` on `(0, ∞)` satisfies the utility hypotheses of
`cia_tvc_dom`: differentiable with continuous positive derivative `1/c`, concave, increasing,
measurable, on an open convex set. -/
theorem log_hypotheses :
    IsOpen (Set.Ioi (0 : ℝ)) ∧ Convex ℝ (Set.Ioi (0 : ℝ)) ∧
      (∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt Real.log x⁻¹ x) ∧
      ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi 0) ∧ Measurable Real.log ∧
      ConcaveOn ℝ (Set.Ioi 0) Real.log ∧ MonotoneOn Real.log (Set.Ioi 0) ∧
      ∀ x ∈ Set.Ioi (0 : ℝ), 0 < x⁻¹ :=
  ⟨isOpen_Ioi, convex_Ioi 0, fun _ hx => Real.hasDerivAt_log (ne_of_gt hx),
    continuousOn_inv₀.mono fun _ hx => ne_of_gt hx, Real.measurable_log,
    strictConcaveOn_log_Ioi.concaveOn, Real.strictMonoOn_log.monotoneOn,
    fun _ hx => inv_pos.2 hx⟩

/-- Cochrane (2023), (19.24)–(19.26), p. 449 (a primitive condition for nonnegative reference
money): if the cash constraint `(1/V − 1)c + y ≤ m` holds, `1/V − 1 ≥ 0` (`V ≤ 1`), `y ≥ 0` and
the reference consumption is nonnegative, then the reference money `mRef` is nonnegative. -/
theorem mRef_nonneg {θ cn mn yn cr : ℝ} (hcia : θ * cn + yn ≤ mn) (hθ : 0 ≤ θ) (hy : 0 ≤ yn)
    (hcr : 0 ≤ cr) : 0 ≤ mn + θ * (cr - cn) := by
  nlinarith

/-- Cochrane (2023), (19.26), p. 449 (a primitive condition for nonnegative step money): if
`1/V − 1 ≥ 0`, the freed wealth is nonnegative and overnight money is nonnegative, then the
money of a Kamihigashi step is nonnegative. -/
theorem step_money_nonneg {θ θ₀ mn x : ℝ} (hθ : 0 ≤ θ) (hθ₀ : 0 ≤ θ₀) (hx : 0 ≤ x)
    (hm : 0 ≤ mn) : 0 ≤ mn + θ * (θ₀ * x) := by
  positivity

open TidyR6HouseholdLocal TidyR6HouseholdFOC in
/-- Cochrane (2023), p. 439 and (19.11)–(19.12), p. 439, **the money-in-utility transversality
condition for a utility on a convex domain.** Let `u` be `C¹` on the open **convex** domain `U`
(e.g. `(0, ∞)²`), concave on `U`, increasing in consumption within `U`, and measurable; prices
`PriceWeak`, endowment and taxes adapted with integrable values, `u_c > 0` at date `0`. If the
reference plan (`cRef`, `m`) lies in `U` and is admissible, and the step
`(c_T + θ₀x_T, m_T)` lies in `U` and has integrable utility or nonnegative freed wealth, then
`E[pk_T(a_T + M_{T−1})] → 0`. No extension of `u` beyond `U` is used. -/
theorem miu_tvc_dom {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hu : C1On u uc um U) (hUc : Convex ℝ U) (hum : Measurable fun p : ℝ × ℝ => u p.1 p.2)
    (hconcU : ConcaveOn ℝ U (fun p : ℝ × ℝ => u p.1 p.2))
    (hmonoU : ∀ x x' z, (x, z) ∈ U → (x', z) ∈ U → x ≤ x' → u x z ≤ u x' z)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β u (DomainCon S U) Λ P y s N0 a0 c m a) (hp : PriceWeak S Λ P)
    (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hpos : ∀ᵐ ω ∂S.μ, 0 < uc (c 0 ω) (m 0 ω))
    (href : UAdmissible S β
      (fun n ω => u (cRef S 0 Λ P y s c m n ω) (mRef S 0 Λ P y s c m n ω)))
    (hrefU : ∀ n, ∀ᵐ ω ∂S.μ, (cRef S 0 Λ P y s c m n ω, m n ω) ∈ U)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hstep : ∀ T, Integrable (fun ω => u (c T ω + θ₀ * kx S 0 Λ P a m T ω)
      (m T ω + 0 * (θ₀ * kx S 0 Λ P a m T ω))) S.μ ∨ ∀ᵐ ω ∂S.μ, 0 ≤ kx S 0 Λ P a m T ω)
    (hstepU : ∀ T, ∀ᵐ ω ∂S.μ, (c T ω + θ₀ * kx S 0 Λ P a m T ω, m T ω) ∈ U) :
    Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  have hfeas := hopt.1
  have hdom := hopt.2.1
  obtain ⟨lam, hlam⟩ := miu_multiplier hβ hu hopt hp
  have hlam0 : 0 < lam := by
    obtain ⟨ω, h1, h2⟩ := ((hlam 0).1.and hpos).exists
    rw [pow_zero, one_mul] at h1
    rw [h1] at h2
    exact pos_of_mul_pos_left h2 (hp.2.2.1 0 ω).le
  have hw1 : ∀ n ω, wedge S 0 Λ P n ω = 1 := fun n ω => by simp [wedge]
  have hcR : ∀ n ω, c n ω + (cRef S 0 Λ P y s c m n ω - c n ω) = cRef S 0 Λ P y s c m n ω :=
    fun n ω => by ring
  refine tvc_seg (ϑ := 0) (uc := uc) (um := um) hβ hum hθ₀ hθ₀1 hopt hp hya hsa
    (fun n => Eventually.of_forall fun ω => by rw [hw1]; exact one_ne_zero) hlam0
    (fun T => ?_) (fun T => ?_) href (fun n => ?_) (fun n => ?_) (fun T => ?_) (fun T => ?_)
    (fun T => ?_) (fun n => ?_) hstep (fun T θ h0 h1 n => ?_)
  · filter_upwards [hdom T] with ω hω
    have := hu.hasDerivAt_line (x := c T ω) (y := m T ω) (g := 1) (k := 0) (ε := 0)
      (by simpa using hω)
    simpa using this
  · filter_upwards [(hlam T).1] with ω h
    rw [hw1, zero_mul, add_zero, mul_one]
    exact h
  · refine ((wealth_step_w hp hy hs hfeas n).1.neg).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.neg_apply, outlay, cRef, hw1, div_one]
    ring
  · simp
  · refine (lam_kOut hp hfeas T).1.congr (Eventually.of_forall fun ω => ?_)
    simp [kx, hw1]
  · simp
  · filter_upwards [hdom T, hstepU T] with ω h0 h1
    exact line_fst hUc hconcU hmonoU h0 h1
  · filter_upwards [hdom n, hrefU n] with ω h0 h1
    exact line_fst hUc hconcU hmonoU h0 (by rw [hcR]; exact h1)
  · filter_upwards [hdom n, hrefU n, hstepU T] with ω hd0 hr hst
    simp only [zero_mul, mul_zero, add_zero]
    rcases lt_trichotomy n T with hn | hn | hn
    · simpa [kdc, hn] using hd0
    · subst hn
      have he : θ * kx S 0 Λ P a m n ω ∈ Set.uIcc 0 (θ₀ * kx S 0 Λ P a m n ω) :=
        mem_uIcc_mul h0.le h1.le
      simpa [kdc] using mem_line_fst hUc hd0 hst he
    · have he : θ * (cRef S 0 Λ P y s c m n ω - c n ω) ∈
          Set.uIcc 0 (1 * (cRef S 0 Λ P y s c m n ω - c n ω)) :=
        mem_uIcc_mul h0.le (h1.trans_le hθ₀1).le
      rw [one_mul] at he
      have := mem_line_fst hUc hd0 (by rw [hcR]; exact hr) he
      simpa [kdc, show ¬ n < T by omega, show n ≠ T by omega] using this

open TidyR6HouseholdCIA in
/-- Cochrane (2023), (19.28), p. 449, **the cash-in-advance transversality condition for a
utility on an open interval.** As `TidyR6HouseholdTVC.cia_tvc`, but `u` need only be `C¹`,
concave and increasing on the open convex set `I` (e.g. `log` on `(0, ∞)`, `log_hypotheses`),
with consumption, the reference consumption and the step in `I`; the step may have integrable
utility or nonnegative freed wealth. -/
theorem cia_tvc_dom {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hIc : Convex ℝ I) (hu : ∀ x ∈ I, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' I)
    (hum : Measurable u) (hconc : ConcaveOn ℝ I u) (hmono : MonotoneOn u I)
    (hpos : ∀ x ∈ I, 0 < u' x) {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β (fun x _ => u x) (CIAConD S V I y) Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) (hm : ∀ t, ∀ᵐ ω ∂S.μ, 0 < m t ω)
    (href : UAdmissible S β (fun n ω => u (cRef S (1 / V - 1) Λ P y s c m n ω)))
    (hrefI : ∀ n, ∀ᵐ ω ∂S.μ, cRef S (1 / V - 1) Λ P y s c m n ω ∈ I)
    (hmr : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ mRef S (1 / V - 1) Λ P y s c m n ω)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hstep : ∀ T, Integrable (fun ω => u (c T ω + θ₀ * kx S (1 / V - 1) Λ P a m T ω)) S.μ ∨
      ∀ᵐ ω ∂S.μ, 0 ≤ kx S (1 / V - 1) Λ P a m T ω)
    (hstepI : ∀ T, ∀ᵐ ω ∂S.μ, c T ω + θ₀ * kx S (1 / V - 1) Λ P a m T ω ∈ I)
    (hstepm : ∀ T, ∀ᵐ ω ∂S.μ, 0 ≤ m T ω + (1 / V - 1) * (θ₀ * kx S (1 / V - 1) Λ P a m T ω)) :
    Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  set θV : ℝ := 1 / V - 1 with hθV
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hcia := hopt.2.1.1
  have hdom := hopt.2.1.2
  have hpos0 : ∀ t, ∀ᵐ ω ∂S.μ, 0 < u' (c t ω) := fun t => by
    filter_upwards [hdom t] with ω hω
    exact hpos _ hω.1
  have hι : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P t ω := fun t =>
    cia_iota_nonneg hβ hI hu hu' hopt hp t (hpos0 t)
  have hwl : ∀ t, ∀ᵐ ω ∂S.μ, min 1 (1 / V) ≤ wedge S θV Λ P t ω := fun t =>
    cia_wedge_pos hp hV (hι t)
  have hmin : 0 < min 1 (1 / V) := lt_min one_pos (one_div_pos.2 hV)
  have hw : ∀ t, ∀ᵐ ω ∂S.μ, wedge S θV Λ P t ω ≠ 0 := fun t =>
    (hwl t).mono fun ω h => (lt_of_lt_of_le hmin h).ne'
  obtain ⟨lam, hlam⟩ := cia_multiplier hβ hI hu hu' hopt hp
  have hfoc : ∀ t, ∀ᵐ ω ∂S.μ, β ^ t * u' (c t ω) = lam * (Λ t ω * wedge S θV Λ P t ω) :=
    fun t => (hlam t).and (hm t) |>.mono fun ω h => h.1 h.2
  have hlam0 : 0 < lam := by
    obtain ⟨ω, h1, h2, h3⟩ := ((hfoc 0).and ((hwl 0).and (hpos0 0))).exists
    rw [pow_zero, one_mul] at h1
    have hw0 := lt_of_lt_of_le hmin h2
    rw [h1] at h3
    exact pos_of_mul_pos_left h3 (mul_pos (hp.2.2.1 0 ω) hw0).le
  have hwinv : ∀ t, ∀ᵐ ω ∂S.μ, ‖(wedge S θV Λ P t ω)⁻¹‖ ≤ (min 1 (1 / V))⁻¹ := fun t => by
    filter_upwards [hwl t] with ω h
    have hpos' := lt_of_lt_of_le hmin h
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos')]
    exact inv_anti₀ hmin h
  have hwm : ∀ t, StronglyMeasurable[S.𝓕 t] (wedge S θV Λ P t) := fun t =>
    stronglyMeasurable_const.add ((hp.sm_iota t).const_mul θV)
  have hRc : ∀ n, Integrable (fun ω => Λ n ω * (cRef S θV Λ P y s c m n ω - c n ω)) S.μ := by
    intro n
    have := ((wealth_step_w hp hy hs hfeas n).1.neg).mul_bdd
      ((hwm n).measurable.inv.mono (S.𝓕.le n) le_rfl).aestronglyMeasurable (hwinv n)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.neg_apply, Pi.inv_apply, outlay, cRef]
    ring
  have hXc : ∀ T, Integrable (fun ω => Λ T ω * kx S θV Λ P a m T ω) S.μ := by
    intro T
    have := (lam_kOut hp hfeas T).1.mul_bdd
      ((hwm T).measurable.inv.mono (S.𝓕.le T) le_rfl).aestronglyMeasurable (hwinv T)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.inv_apply, kx]
    ring
  have hQ : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1 := fun t =>
    (hι t).mono fun ω h => by simp only [iota] at h; linarith
  have hRm : ∀ n, Integrable (fun ω => pk Λ P (n + 1) ω *
      (P n ω * (θV * (cRef S θV Λ P y s c m n ω - c n ω)))) S.μ := fun n =>
    integrable_pk_succ_mul hp (((sm_cRef hp hya hsa hca hma n).sub (hca n)).const_mul θV)
      (((hRc n).const_mul θV).congr (Eventually.of_forall fun ω => by ring)) (hQ n)
  have hXm : ∀ T, Integrable (fun ω => pk Λ P (T + 1) ω *
      (P T ω * (θV * kx S θV Λ P a m T ω))) S.μ := fun T =>
    integrable_pk_succ_mul hp ((sm_kx hp hma T).const_mul θV)
      (((hXc T).const_mul θV).congr (Eventually.of_forall fun ω => by ring)) (hQ T)
  have hcR : ∀ n ω, c n ω + (cRef S θV Λ P y s c m n ω - c n ω) = cRef S θV Λ P y s c m n ω :=
    fun n ω => by ring
  refine tvc_seg (ϑ := θV) (uc := fun x _ => u' x) (um := fun _ _ => 0) hβ
    (hum.comp measurable_fst) hθ₀ hθ₀1 hopt hp hya hsa hw hlam0
    (fun T => ?_) (fun T => (hfoc T).mono fun ω h => by simpa using h) href hRc hRm hXc hXm
    (fun T => ?_) (fun n => ?_) hstep
    (fun T θ h0 h1 => ⟨fun n => ?_, fun n => ?_⟩)
  · filter_upwards [hdom T] with ω hω
    have h1 : HasDerivAt (fun e : ℝ => c T ω + e) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (c T ω)
    have h2 := (hu (c T ω + 0) (by simpa using hω.1)).comp (0 : ℝ) h1
    simpa [Function.comp_def] using h2
  · filter_upwards [hdom T, hstepI T] with ω h0 h1
    exact line_cons hIc hconc hmono h0.1 h1 (m T ω) θV
  · filter_upwards [hdom n, hrefI n] with ω h0 h1
    exact line_cons hIc hconc hmono h0.1 (by rw [hcR]; exact h1) (m n ω) θV
  · filter_upwards [hcia n, hmr n, hstepm T] with ω ⟨hc1, hc2⟩ hr hst
    refine ⟨by nlinarith, ?_⟩
    rcases lt_trichotomy n T with hn | hn | hn
    · simp only [kdc, hn, ↓reduceIte, mul_zero, add_zero]
      exact hc2
    · subst hn
      simp only [kdc, lt_irrefl, ↓reduceIte]
      have e : m n ω + θ * (θV * kx S θV Λ P a m n ω) = (1 - θ / θ₀) * m n ω +
          θ / θ₀ * (m n ω + θV * (θ₀ * kx S θV Λ P a m n ω)) := by
        field_simp
        ring
      rw [e]
      have hθθ : θ / θ₀ ≤ 1 := by rw [div_le_one hθ₀]; exact h1.le
      exact add_nonneg (mul_nonneg (by linarith) hc2) (mul_nonneg (by positivity) hst)
    · simp only [kdc, show ¬ n < T by omega, show n ≠ T by omega, ↓reduceIte]
      have e : m n ω + θ * (θV * (cRef S θV Λ P y s c m n ω - c n ω)) =
          (1 - θ) * m n ω + θ * mRef S θV Λ P y s c m n ω := by
        simp only [mRef]
        ring
      rw [e]
      have hθ1 : θ ≤ 1 := (h1.trans_le hθ₀1).le
      exact add_nonneg (mul_nonneg (by linarith) hc2) (mul_nonneg h0.le hr)
  · filter_upwards [hdom n, hrefI n, hstepI T] with ω hd0 hr hst
    refine ⟨?_, Set.mem_univ _⟩
    rcases lt_trichotomy n T with hn | hn | hn
    · simpa [kdc, hn] using hd0.1
    · subst hn
      have he : θ * kx S θV Λ P a m n ω ∈ Set.uIcc 0 (θ₀ * kx S θV Λ P a m n ω) :=
        mem_uIcc_mul h0.le h1.le
      simpa [kdc] using mem_shift hIc hd0.1 hst he
    · have he : θ * (cRef S θV Λ P y s c m n ω - c n ω) ∈
          Set.uIcc 0 (1 * (cRef S θV Λ P y s c m n ω - c n ω)) :=
        mem_uIcc_mul h0.le (h1.trans_le hθ₀1).le
      rw [one_mul] at he
      have := mem_shift hIc hd0.1 (by rw [hcR]; exact hr) he
      simpa [kdc, show ¬ n < T by omega, show n ≠ T by omega] using this
end Cochrane.Monetarism.TidyR6HouseholdTVCDom
