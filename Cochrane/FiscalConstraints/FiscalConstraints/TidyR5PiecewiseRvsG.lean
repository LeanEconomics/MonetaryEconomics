/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.RvsG
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Temporary `r < g` with finitely many regimes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 196 ("if the
`r < g` opportunity fades away, fiscal theory reemerges").

`RvsG` proves the corrected 20-year formula for two regimes (`RvsG.step_existsUnique`). Here
`r − g` is piecewise constant with any finite number of regimes: `a₀` on `[T₀, T₁)`, `a₁` on
`[T₁, T₂)`, …, `a_{n−1}` on `[T_{n−1}, T_n)` and `a_n` on `[T_n, ∞)`, with `0 = T₀ ≤ T₁ ≤ ⋯ ≤ T_n`.
The rates before the last switch have any signs; the last one is positive (`r > g` after).

The proof first treats a general time-varying `r − g` with a continuous cumulative rate
`A(t) = ∫₀^t (r − g)` that is differentiable off a countable set and eventually linear with
positive slope (`SolvesGen`). Every solution is `x_t = e^{A(t)}(x₀ − ∫₀^t e^{−A(v)} σ_v dv)`
(`eq_vocA`, by the fundamental theorem of calculus off a countable set), and the sustainable debt is
`x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`.

## Main results

* General rate: `gen_solves`, `gen_bddOn`, `gen_bddOn_iff`, `gen_tendsto_abs_of_ne`,
  `gen_existsUnique`, `gen_tvc_iff`, `gSol_eq_integral`
  (`x̂_t = ∫_t^∞ exp(−∫_t^v (r − g)) σ_v dv`).
* Finitely many regimes: the cumulative rate `cum` and its regime formulas (`cum_eq_regime`,
  `cum_eq_last`, `cum_hasDerivAt_regime`, `cum_hasDerivAt_last`); the solution concept
  `SolvesPW`; `pw_existsUnique` (exactly one bounded solution), `pw_bddOn_iff` (bounded iff
  `x₀ = x̂₀`), `pw_tendsto_abs_of_ne` (every other solution explodes), `pw_tvc_iff` (the
  transversality condition iff `x₀ = x̂₀`), `pw_nominal_determinacy` (exactly one `P₀`).
* `pwPV0_eq_sum`: the general 20-year formula,
  `x̂₀ = ∑_{k<n} e^{−A(T_k)} ∫_{T_k}^{T_{k+1}} e^{−a_k(v−T_k)} σ_v dv + e^{−A(T_n)} x̂^{(n)}_{T_n}`,
  with `A(T_k) = ∑_{j<k} a_j (T_{j+1} − T_j)` and `x̂^{(n)}` the present value at the last rate.
* `pw_unique_iff_last_pos`: a bounded solution is unique for every bounded surplus iff `r > g` in
  the last regime, whatever the signs before.
* `solvesStep_iff`, `pwPV0_two_regime`: the two-regime case is `RvsG.SolvesStep` and
  `RvsG.stepPV0`.
-/

namespace Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals Cochrane.FiscalConstraints.RvsG

/-! ### A general time-varying `r − g` -/

/-- Cochrane (2023), eq. (6.4), p. 196, with time-varying `r − g = ρ(t)`: `x` is continuous on
`[0, ∞)` and solves `x' = ρ(t) x − σ` at every `t > 0` outside the exceptional set `S` (the switch
dates). -/
def SolvesGen (ρ : ℝ → ℝ) (S : Set ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ∀ t, 0 < t → t ∉ S → HasDerivAt x (ρ t * x t - σ t) t

/-- Cochrane (2023), eq. (6.5), p. 196, with time-varying `r − g`: the backward solution from
`x₀` with cumulative rate `A`, `x_t = e^{A(t)}(x₀ − ∫₀^t e^{−A(v)} σ_v dv)`. -/
noncomputable def vocA (A σ : ℝ → ℝ) (x0 t : ℝ) : ℝ :=
  exp (A t) * (x0 - ∫ v in (0 : ℝ)..t, exp (-A v) * σ v)

/-- Cochrane (2023), §6.4.1, p. 196: the sustainable initial debt-to-GDP ratio with time-varying
`r − g`, `x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`. -/
noncomputable def pvA (A σ : ℝ → ℝ) : ℝ := ∫ v in Set.Ioi (0 : ℝ), exp (-A v) * σ v

/-- Cochrane (2023), §6.4.1, p. 196: the forward-looking solution, the backward solution started
at `x̂₀`. -/
noncomputable def gSol (A σ : ℝ → ℝ) (t : ℝ) : ℝ := vocA A σ (pvA A σ) t

variable {A ρ σ x : ℝ → ℝ} {S : Set ℝ} {Tn ab M : ℝ}

/-- Cochrane (2023), eq. (6.4), p. 196: the backward solution solves `x' = r x − σ` at every
date where the cumulative rate has derivative `r`. -/
theorem vocA_hasDerivAt (hσ : Continuous σ) (hAc : Continuous A) (x0 : ℝ) {t r : ℝ}
    (hA : HasDerivAt A r t) : HasDerivAt (vocA A σ x0) (r * vocA A σ x0 t - σ t) t := by
  have hf : Continuous (fun v => exp (-A v) * σ v) := by fun_prop
  have hI := (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h := hA.exp.mul (hI.const_sub x0)
  unfold vocA
  refine h.congr_deriv ?_
  have : exp (A t) * exp (-A t) = 1 := by rw [← exp_add]; simp
  linear_combination (-(σ t)) * this

/-- Cochrane (2023), eq. (6.5), p. 196: the backward solution is continuous. -/
theorem vocA_continuous (hσ : Continuous σ) (hAc : Continuous A) (x0 : ℝ) :
    Continuous (vocA A σ x0) := by
  have hf : Continuous (fun v => exp (-A v) * σ v) := by fun_prop
  have hI : Continuous fun t => ∫ v in (0 : ℝ)..t, exp (-A v) * σ v :=
    continuous_iff_continuousAt.2 fun t =>
      (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  unfold vocA
  fun_prop

/-- Cochrane (2023), eq. (6.5), p. 196: the backward solution starts at `x₀`. -/
theorem vocA_zero (hA0 : A 0 = 0) (x0 : ℝ) : vocA A σ x0 0 = x0 := by
  unfold vocA
  rw [hA0, exp_zero, intervalIntegral.integral_same, sub_zero, one_mul]

/-- Cochrane (2023), eq. (6.5), p. 196: two backward solutions differ by `e^{A(t)}(x₀ − z₀)`. -/
theorem vocA_sub (x0 z0 t : ℝ) : vocA A σ x0 t - vocA A σ z0 t = exp (A t) * (x0 - z0) := by
  unfold vocA
  ring

/-- Cochrane (2023), eq. (6.5), p. 196 (**uniqueness with time-varying `r − g`**): every solution
on `[0, ∞)` is the backward solution from its initial value, when the cumulative rate is
continuous with derivative `ρ` off a countable set `S`. -/
theorem eq_vocA (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hx : SolvesGen ρ S σ x) {t : ℝ} (ht : 0 ≤ t) : x t = vocA A σ (x 0) t := by
  have hf : Continuous (fun v => exp (-A v) * σ v) := by fun_prop
  have hI : Continuous fun t => ∫ v in (0 : ℝ)..t, exp (-A v) * σ v :=
    continuous_iff_continuousAt.2 fun t =>
      (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  set g : ℝ → ℝ := fun u => exp (-A u) * x u + ∫ v in (0 : ℝ)..u, exp (-A v) * σ v with hg
  have hgc : ContinuousOn g (Set.Icc 0 t) :=
    ((by fun_prop : Continuous fun u => exp (-A u)).continuousOn.mul
      (hx.1.mono Set.Icc_subset_Ici_self)).add hI.continuousOn
  have hgd : ∀ u ∈ Set.Ioo 0 t \ S, HasDerivAt g 0 u := by
    rintro u ⟨hu, huS⟩
    have h1 := (hAd u hu.1 huS).neg.exp
    have h2 := hx.2 u hu.1 huS
    have h3 := (hf.integral_hasStrictDerivAt 0 u).hasDerivAt
    refine ((h1.mul h2).add h3).congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le g (fun _ => (0 : ℝ)) ht hS hgc hgd
    intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at hftc
  have h' : exp (-A t) * x t + (∫ v in (0 : ℝ)..t, exp (-A v) * σ v) - x 0 = 0 := by
    have hg0 : g 0 = x 0 := by
      simp only [hg, hA0, neg_zero, exp_zero, one_mul, intervalIntegral.integral_same, add_zero]
    have : g t - g 0 = 0 := hftc.symm
    rw [hg0] at this
    exact this
  have hE : exp (A t) * exp (-A t) = 1 := by rw [← exp_add]; simp
  unfold vocA
  linear_combination (exp (A t)) * h' + (-(x t)) * hE

/-- Cochrane (2023), §6.4.1, p. 196: if `r − g` is eventually constant at `ā > 0` (after `T_n`)
and surpluses are continuous and bounded, the discounted surpluses `e^{−A(v)} σ_v` are integrable
on every `(c, ∞)`. -/
theorem integrableOn_expA (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) (c : ℝ) :
    IntegrableOn (fun v => exp (-A v) * σ v) (Set.Ioi c) := by
  have h1 : IntegrableOn (fun v => exp (-A v) * σ v) (Set.Ioi (max c Tn)) := by
    have := (integrableOn_exp_mul_bdd ha hσ hM (max c Tn)).const_mul (exp (-A Tn + ab * Tn))
    refine IntegrableOn.congr_fun this (fun v hv => ?_) measurableSet_Ioi
    have hv' : Tn ≤ v := le_trans (le_max_right _ _) (le_of_lt hv)
    rw [hAT v hv', ← mul_assoc, ← exp_add]
    congr 2
    ring
  have h2 : IntegrableOn (fun v => exp (-A v) * σ v) (Set.Icc c (max c Tn)) :=
    (by fun_prop : Continuous fun v => exp (-A v) * σ v).integrableOn_Icc
  refine (h2.union h1).mono_set fun v hv => ?_
  rcases le_or_gt v (max c Tn) with h | h
  · exact Or.inl ⟨le_of_lt hv, h⟩
  · exact Or.inr h

/-- Cochrane (2023), §6.4.1, p. 196 (the forward formula at every date): the forward-looking
solution is `x̂_t = ∫_t^∞ exp(−(A(v) − A(t))) σ_v dv`, i.e. surpluses discounted at the cumulated
`r − g` between `t` and `v`. -/
theorem gSol_eq_integral (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) (t : ℝ) :
    gSol A σ t = ∫ v in Set.Ioi t, exp (-(A v - A t)) * σ v := by
  unfold gSol vocA pvA
  rw [integral_Ioi_sub_interval (integrableOn_expA hAc hσ hM hAT ha) t, ← integral_const_mul]
  congr 1
  funext v
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch the forward-looking solution is the
constant-rate present value `RvsG.pv ā σ t`. -/
theorem gSol_eq_pv (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) {t : ℝ} (ht : Tn ≤ t) :
    gSol A σ t = pv ab σ t := by
  rw [gSol_eq_integral hAc hσ hM hAT ha t, pv]
  rw [← integral_Ioi_comp_add (fun v => exp (-(A v - A t)) * σ v) t]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : (0 : ℝ) < u := hu
  rw [hAT (t + u) (by linarith), hAT t ht]
  congr 2
  ring

/-- Cochrane (2023), §6.4.1, p. 196: the forward-looking solution is continuous. -/
theorem gSol_continuous (hσ : Continuous σ) (hAc : Continuous A) : Continuous (gSol A σ) :=
  vocA_continuous hσ hAc _

/-- Cochrane (2023), §6.4.1, p. 196 (existence): the forward-looking solution is bounded on
`[0, ∞)`. -/
theorem gen_bddOn (hAc : Continuous A) (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M)
    (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) : BddOn (gSol A σ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Tn)).exists_bound_of_continuousOn
    (gSol_continuous hσ hAc).continuousOn
  refine ⟨max C (M / ab), fun t ht => ?_⟩
  rcases le_total t Tn with h | h
  · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
  · rw [gSol_eq_pv hAc hσ hM hAT ha h]
    exact (abs_pv_le ha hM t).trans (le_max_right _ _)

/-- Cochrane (2023), §6.4.1, p. 196 (existence): the forward-looking solution solves the
equation with time-varying `r − g`. -/
theorem gen_solves (hAc : Continuous A) (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t)
    (hσ : Continuous σ) : SolvesGen ρ S σ (gSol A σ) :=
  ⟨(gSol_continuous hσ hAc).continuousOn, fun t ht htS => vocA_hasDerivAt hσ hAc _ (hAd t ht htS)⟩

/-- Cochrane (2023), §6.4.1, p. 196: every solution differs from the forward-looking one by
`e^{A(t)}(x₀ − x̂₀)`. -/
theorem gen_sub (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hx : SolvesGen ρ S σ x) {t : ℝ} (ht : 0 ≤ t) :
    x t - gSol A σ t = exp (A t) * (x 0 - pvA A σ) := by
  rw [eq_vocA hS hAc hA0 hAd hσ hx ht, gSol, vocA_sub]

/-- Cochrane (2023), §6.4.1, p. 196 ("values of debt different from this forward-looking integral
lead to explosions"), time-varying `r − g`: a solution not starting at `x̂₀` explodes. -/
theorem gen_tendsto_abs_of_ne (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab)
    (hx : SolvesGen ρ S σ x) (hne : x 0 ≠ pvA A σ) :
    Tendsto (fun t => |x t|) atTop atTop := by
  set d := |x 0 - pvA A σ| with hd_def
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hlow : ∀ t, max 0 Tn ≤ t →
      exp (A Tn + ab * (t - Tn)) * d + -(M / ab) ≤ |x t| := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_max_left _ _) ht
    have htn : Tn ≤ t := le_trans (le_max_right _ _) ht
    have h1 := gen_sub hS hAc hA0 hAd hσ hx ht0
    have h2 := abs_pv_le ha hM t
    rw [← gSol_eq_pv hAc hσ hM hAT ha htn] at h2
    have h3 : exp (A Tn + ab * (t - Tn)) * d = |x t - gSol A σ t| := by
      rw [h1, abs_mul, abs_of_pos (exp_pos _), hAT t htn]
    have h4 := abs_sub (x t) (gSol A σ t)
    linarith
  have hlim : Tendsto (fun t => exp (A Tn + ab * (t - Tn)) * d + -(M / ab)) atTop atTop := by
    have h1 : Tendsto (fun t => A Tn + ab * (t - Tn)) atTop atTop :=
      tendsto_atTop_add_const_left _ _
        ((tendsto_atTop_add_const_right _ (-Tn) tendsto_id).const_mul_atTop ha)
    exact tendsto_atTop_add_const_right _ _ ((tendsto_exp_atTop.comp h1).atTop_mul_const hd)
  exact tendsto_atTop_mono' atTop ((eventually_ge_atTop (max 0 Tn)).mono hlow) hlim

/-- Cochrane (2023), §6.4.1, p. 196, time-varying `r − g`: a solution is bounded iff it starts at
the sustainable value `x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`. -/
theorem gen_bddOn_iff (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab)
    (hx : SolvesGen ρ S σ x) : BddOn x ↔ x 0 = pvA A σ := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hne
    have h1 := (gen_tendsto_abs_of_ne hS hAc hA0 hAd hσ hM hAT ha hx hne).eventually_gt_atTop K
    obtain ⟨t, ht1, ht2⟩ := (h1.and (eventually_ge_atTop 0)).exists
    linarith [hK t ht2]
  · intro h
    obtain ⟨K, hK⟩ := gen_bddOn hAc hσ hM hAT ha
    refine ⟨K, fun t ht => ?_⟩
    have := gen_sub hS hAc hA0 hAd hσ hx ht
    rw [h, sub_self, mul_zero, sub_eq_zero] at this
    rw [this]
    exact hK t ht

/-- Cochrane (2023), §6.4.1, p. 196 (**existence and uniqueness**, time-varying `r − g`): there is
a bounded solution, and every bounded solution is the forward-looking one at every date
`t ≥ 0`. -/
theorem gen_existsUnique (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab) :
    SolvesGen ρ S σ (gSol A σ) ∧ BddOn (gSol A σ) ∧
      ∀ x, SolvesGen ρ S σ x → BddOn x → ∀ t, 0 ≤ t → x t = gSol A σ t := by
  refine ⟨gen_solves hAc hAd hσ, gen_bddOn hAc hσ hM hAT ha, fun x hx hb t ht => ?_⟩
  have := gen_sub hS hAc hA0 hAd hσ hx ht
  rw [(gen_bddOn_iff hS hAc hA0 hAd hσ hM hAT ha hx).1 hb, sub_self, mul_zero, sub_eq_zero]
    at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (**transversality**, time-varying `r − g`): the discounted
debt-to-GDP ratio `e^{−A(t)} x_t` (debt discounted at the cumulated real rate, relative to
GDP) tends to `0` iff `x₀ = x̂₀`. -/
theorem gen_tvc_iff (hS : S.Countable) (hAc : Continuous A) (hA0 : A 0 = 0)
    (hAd : ∀ t, 0 < t → t ∉ S → HasDerivAt A (ρ t) t) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hAT : ∀ t, Tn ≤ t → A t = A Tn + ab * (t - Tn)) (ha : 0 < ab)
    (hx : SolvesGen ρ S σ x) :
    Tendsto (fun t => exp (-A t) * x t) atTop (𝓝 0) ↔ x 0 = pvA A σ := by
  have hlimI := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_expA hAc hσ hM hAT ha 0) tendsto_id
  have hev : ∀ᶠ t in atTop,
      x 0 - (∫ v in (0 : ℝ)..t, exp (-A v) * σ v) = exp (-A t) * x t := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [eq_vocA hS hAc hA0 hAd hσ hx ht, vocA, ← mul_assoc, ← exp_add]
    simp
  have hlim : Tendsto (fun t => exp (-A t) * x t) atTop (𝓝 (x 0 - pvA A σ)) :=
    (hlimI.const_sub (x 0)).congr' hev
  constructor
  · intro h
    have := tendsto_nhds_unique hlim h
    linarith
  · intro h
    rwa [h, sub_self] at hlim

/-! ### Finitely many regimes -/

/-- Cochrane (2023), §6.4.1, p. 196: `t` clamped to `[lo, hi]`, `max lo (min t hi)`. -/
noncomputable def clampI (lo hi t : ℝ) : ℝ := max lo (min t hi)

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated `r − g` with `n` switches, rates `a k` on
`[T k, T (k+1))` for `k < n` and `a n` after `T n`: `A(t) = ∫₀^t (r − g)` written out. -/
noncomputable def cum (n : ℕ) (a T : ℕ → ℝ) (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range n, a k * (clampI (T k) (T (k + 1)) t - T k)) + a n * (max t (T n) - T n)

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated `r − g` at the switch date `T j`,
`A(T_j) = ∑_{k<j} a_k (T_{k+1} − T_k)`. -/
noncomputable def cumAt (a T : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, a k * (T (k + 1) - T k)

/-- Cochrane (2023), eq. (6.4), p. 196, with finitely many regimes: `x` is continuous on
`[0, ∞)`, solves `x' = a_j x − σ` on each `(T_j, T_{j+1})`, `j < n`, and `x' = a_n x − σ` after
`T_n`. -/
def SolvesPW (n : ℕ) (a T : ℕ → ℝ) (σ x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧
    (∀ j < n, ∀ t ∈ Set.Ioo (T j) (T (j + 1)), HasDerivAt x (a j * x t - σ t) t) ∧
    ∀ t, T n < t → HasDerivAt x (a n * x t - σ t) t

/-- Cochrane (2023), §6.4.1, p. 196: the sustainable initial debt-to-GDP ratio with finitely
many regimes, `x̂₀ = ∫₀^∞ e^{−A(v)} σ_v dv`. -/
noncomputable def pwPV0 (n : ℕ) (a T : ℕ → ℝ) (σ : ℝ → ℝ) : ℝ := pvA (cum n a T) σ

/-- Cochrane (2023), §6.4.1, p. 196: the forward-looking solution with finitely many regimes. -/
noncomputable def pwSol (n : ℕ) (a T : ℕ → ℝ) (σ : ℝ → ℝ) : ℝ → ℝ := gSol (cum n a T) σ

variable {n : ℕ} {a T : ℕ → ℝ}

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated rate is continuous. -/
theorem cum_continuous (n : ℕ) (a T : ℕ → ℝ) : Continuous (cum n a T) := by
  unfold cum clampI
  fun_prop

/-- Cochrane (2023), §6.4.1, p. 196: on the closed regime `[T_j, T_{j+1}]`, `j < n`, the cumulated
rate is `A(T_j) + a_j (t − T_j)`. -/
theorem cum_eq_regime (hT : Monotone T) {j : ℕ} (hj : j < n) {t : ℝ}
    (ht : t ∈ Set.Icc (T j) (T (j + 1))) : cum n a T t = cumAt a T j + a j * (t - T j) := by
  unfold cum cumAt
  rw [← Finset.sum_range_add_sum_Ico _ (show j + 1 ≤ n by omega), Finset.sum_range_succ]
  have h1 : ∑ k ∈ Finset.range j, a k * (clampI (T k) (T (k + 1)) t - T k) =
      ∑ k ∈ Finset.range j, a k * (T (k + 1) - T k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ≤ j := Finset.mem_range.1 hk
    have e1 : T (k + 1) ≤ t := (hT hk').trans ht.1
    have e2 : T k ≤ T (k + 1) := hT (Nat.le_succ k)
    unfold clampI
    rw [min_eq_right e1, max_eq_right e2]
  have h2 : ∑ k ∈ Finset.Ico (j + 1) n, a k * (clampI (T k) (T (k + 1)) t - T k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : j + 1 ≤ k := (Finset.mem_Ico.1 hk).1
    have e1 : t ≤ T k := ht.2.trans (hT hk')
    have e2 : t ≤ T (k + 1) := e1.trans (hT (Nat.le_succ k))
    unfold clampI
    rw [min_eq_left e2, max_eq_left e1, sub_self, mul_zero]
  have h3 : clampI (T j) (T (j + 1)) t = t := by
    unfold clampI
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have h4 : max t (T n) = T n := max_eq_right (ht.2.trans (hT (show j + 1 ≤ n by omega)))
  rw [h1, h2, h3, h4]
  ring

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch the cumulated rate is
`A(T_n) + a_n (t − T_n)`. -/
theorem cum_eq_last (hT : Monotone T) {t : ℝ} (ht : T n ≤ t) :
    cum n a T t = cumAt a T n + a n * (t - T n) := by
  unfold cum cumAt
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
    have e1 : T (k + 1) ≤ t := (hT hk').trans ht
    unfold clampI
    rw [min_eq_right e1, max_eq_right (hT (Nat.le_succ k))]
  · rw [max_eq_left ht]

/-- Cochrane (2023), §6.4.1, p. 196: the cumulated rate starts at `A(0) = 0` when `T₀ = 0`. -/
theorem cum_zero (hT : Monotone T) (hT0 : T 0 = 0) : cum n a T 0 = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [cum_eq_last hT (le_of_eq hT0), hT0]
    simp [cumAt]
  · rw [cum_eq_regime hT hn ⟨le_of_eq hT0, hT0 ▸ hT (Nat.zero_le 1)⟩, hT0]
    simp [cumAt]

/-- Cochrane (2023), §6.4.1, p. 196: inside the regime `(T_j, T_{j+1})`, `j < n`, the cumulated
rate has derivative `a_j`. -/
theorem cum_hasDerivAt_regime (hT : Monotone T) {j : ℕ} (hj : j < n) {t : ℝ}
    (ht : t ∈ Set.Ioo (T j) (T (j + 1))) : HasDerivAt (cum n a T) (a j) t := by
  have hlin : HasDerivAt (fun s => cumAt a T j + a j * (s - T j)) (a j) t := by
    simpa using (((hasDerivAt_id t).sub_const (T j)).const_mul (a j)).const_add (cumAt a T j)
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact cum_eq_regime hT hj ⟨hs.1.le, hs.2.le⟩

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch the cumulated rate has derivative
`a_n`. -/
theorem cum_hasDerivAt_last (hT : Monotone T) {t : ℝ} (ht : T n < t) :
    HasDerivAt (cum n a T) (a n) t := by
  have hlin : HasDerivAt (fun s => cumAt a T n + a n * (s - T n)) (a n) t := by
    simpa using (((hasDerivAt_id t).sub_const (T n)).const_mul (a n)).const_add (cumAt a T n)
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact cum_eq_last hT (le_of_lt hs)

/-- Cochrane (2023), §6.4.1, p. 196: a date `t > 0` that is not a switch date lies inside one
regime `(T_j, T_{j+1})`, `j < n`, or after the last switch. -/
theorem regime_cases (hT0 : T 0 = 0) {t : ℝ} (ht : 0 < t)
    (htS : t ∉ Set.range T) :
    (∃ j < n, t ∈ Set.Ioo (T j) (T (j + 1))) ∨ T n < t := by
  classical
  have hne : ∀ k, T k ≠ t := fun k h => htS ⟨k, h⟩
  by_cases h : ∃ j, j < n ∧ t < T (j + 1)
  · left
    refine ⟨Nat.find h, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2⟩
    have hle : T (Nat.find h) ≤ t := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
      · rw [h0, hT0]; exact ht.le
      · obtain ⟨j', hj'⟩ : ∃ j', Nat.find h = j' + 1 := ⟨Nat.find h - 1, by omega⟩
        have hmin := Nat.find_min h (show j' < Nat.find h by omega)
        have hj'n : j' < n := by have := (Nat.find_spec h).1; omega
        rw [hj']
        push Not at hmin
        exact hmin hj'n
    exact lt_of_le_of_ne hle (hne _)
  · right
    push Not at h
    have hle : T n ≤ t := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, hT0]; exact ht.le
      · have := h (n - 1) (by omega)
        rwa [show n - 1 + 1 = n by omega] at this
    exact lt_of_le_of_ne hle (hne _)

/-- Cochrane (2023), §6.4.1, p. 196: off the switch dates, for `t > 0`, the cumulated rate has
derivative `deriv A t` (it is differentiable there). -/
theorem cum_hasDerivAt_off (hT : Monotone T) (hT0 : T 0 = 0) {t : ℝ} (ht : 0 < t)
    (htS : t ∉ Set.range T) : HasDerivAt (cum n a T) (deriv (cum n a T) t) t := by
  rcases regime_cases (n := n) hT0 ht htS with ⟨j, hj, hjt⟩ | h
  · exact (cum_hasDerivAt_regime hT hj hjt).differentiableAt.hasDerivAt
  · exact (cum_hasDerivAt_last hT h).differentiableAt.hasDerivAt

/-- Cochrane (2023), §6.4.1, p. 196: after the last switch, `A(t) = A(T_n) + a_n (t − T_n)`. -/
theorem cum_after (hT : Monotone T) (t : ℝ) (ht : T n ≤ t) :
    cum n a T t = cum n a T (T n) + a n * (t - T n) := by
  rw [cum_eq_last hT ht, cum_eq_last hT le_rfl, sub_self, mul_zero, add_zero]

/-- Cochrane (2023), §6.4.1, p. 196: a regime-by-regime solution is a solution with time-varying
`r − g` (off the switch dates). -/
theorem solvesPW_toGen (hT : Monotone T) (hT0 : T 0 = 0) (hx : SolvesPW n a T σ x) :
    SolvesGen (deriv (cum n a T)) (Set.range T) σ x := by
  refine ⟨hx.1, fun t ht htS => ?_⟩
  rcases regime_cases (n := n) hT0 ht htS with ⟨j, hj, hjt⟩ | h
  · rw [(cum_hasDerivAt_regime hT hj hjt).deriv]
    exact hx.2.1 j hj t hjt
  · rw [(cum_hasDerivAt_last hT h).deriv]
    exact hx.2.2 t h

/-- Cochrane (2023), §6.4.1, p. 196 (**existence**): the forward-looking solution solves the
regime-by-regime equation. -/
theorem pwSol_solvesPW (hT : Monotone T) (hσ : Continuous σ) :
    SolvesPW n a T σ (pwSol n a T σ) :=
  ⟨(gSol_continuous hσ (cum_continuous n a T)).continuousOn,
    fun _ hj _ ht => vocA_hasDerivAt hσ (cum_continuous n a T) _ (cum_hasDerivAt_regime hT hj ht),
    fun _ ht => vocA_hasDerivAt hσ (cum_continuous n a T) _ (cum_hasDerivAt_last hT ht)⟩

/-- Cochrane (2023), §6.4.1, p. 196 (**bounded iff sustainable**): with any rates before the last
switch and `r > g` after it, a solution is bounded iff it starts at `x̂₀`. -/
theorem pw_bddOn_iff (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hx : SolvesPW n a T σ x) : BddOn x ↔ x 0 = pwPV0 n a T σ :=
  gen_bddOn_iff (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
    (solvesPW_toGen hT hT0 hx)

/-- Cochrane (2023), §6.4.1, p. 196 ("values of debt different from this forward-looking integral
lead to explosions"), finitely many regimes: a solution not starting at `x̂₀` explodes. -/
theorem pw_tendsto_abs_of_ne (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n)
    (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) (hx : SolvesPW n a T σ x)
    (hne : x 0 ≠ pwPV0 n a T σ) : Tendsto (fun t => |x t|) atTop atTop :=
  gen_tendsto_abs_of_ne (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
    (solvesPW_toGen hT hT0 hx) hne

/-- Cochrane (2023), §6.4.1, p. 196 (**existence and uniqueness of the sustainable debt**): with
finitely many regimes of any signs and `r > g` after the last switch, the forward-looking solution
is a bounded solution, and every bounded solution equals it at every date `t ≥ 0`. -/
theorem pw_existsUnique (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) :
    SolvesPW n a T σ (pwSol n a T σ) ∧ BddOn (pwSol n a T σ) ∧
      ∀ x, SolvesPW n a T σ x → BddOn x → ∀ t, 0 ≤ t → x t = pwSol n a T σ t := by
  have h := gen_existsUnique (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
  exact ⟨pwSol_solvesPW hT hσ, h.2.1, fun x hx hb t ht =>
    h.2.2 x (solvesPW_toGen hT hT0 hx) hb t ht⟩

/-- Cochrane (2023), §6.4.1, p. 196 (**transversality**, finitely many regimes): the debt-to-GDP
ratio discounted at the cumulated `r − g`, `e^{−A(t)} x_t`, tends to `0` iff `x₀ = x̂₀`. -/
theorem pw_tvc_iff (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (hx : SolvesPW n a T σ x) :
    Tendsto (fun t => exp (-cum n a T t) * x t) atTop (𝓝 0) ↔ x 0 = pwPV0 n a T σ :=
  gen_tvc_iff (Set.countable_range T) (cum_continuous n a T) (cum_zero hT hT0)
    (fun _ ht htS => cum_hasDerivAt_off hT hT0 ht htS) hσ hM (cum_after hT) ha
    (solvesPW_toGen hT hT0 hx)

/-- Cochrane (2023), §6.4.1, p. 196: the sustainable debt at every date is the forward integral
`x̂_t = ∫_t^∞ exp(−(A(v) − A(t))) σ_v dv`. -/
theorem pwSol_eq_integral (hT : Monotone T) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (t : ℝ) :
    pwSol n a T σ t = ∫ v in Set.Ioi t, exp (-(cum n a T v - cum n a T t)) * σ v :=
  gSol_eq_integral (cum_continuous n a T) hσ hM (cum_after hT) ha t

/-- Cochrane (2023), §6.4.1, p. 196 (**the general 20-year formula**): with finitely many regimes,
`x̂₀ = ∑_{k<n} e^{−A(T_k)} ∫_{T_k}^{T_{k+1}} e^{−a_k(v−T_k)} σ_v dv + e^{−A(T_n)} x̂^{(n)}_{T_n}`,
with `A(T_k) = ∑_{j<k} a_j (T_{j+1} − T_j)` and `x̂^{(n)}_{T_n} = ∫₀^∞ e^{−a_n u} σ_{T_n+u} du`. -/
theorem pwPV0_eq_sum (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) :
    pwPV0 n a T σ = (∑ k ∈ Finset.range n, exp (-cumAt a T k) *
        ∫ v in T k..T (k + 1), exp (-a k * (v - T k)) * σ v) +
      exp (-cumAt a T n) * pv (a n) σ (T n) := by
  have hint := integrableOn_expA (cum_continuous n a T) hσ hM (cum_after hT) ha
  have hsplit : pwPV0 n a T σ = (∫ v in (0 : ℝ)..T n, exp (-cum n a T v) * σ v) +
      ∫ v in Set.Ioi (T n), exp (-cum n a T v) * σ v := by
    rw [← integral_Ioi_sub_interval hint (T n)]
    unfold pwPV0 pvA
    ring
  have hc : Continuous fun v => exp (-cum n a T v) * σ v := by
    have := cum_continuous n a T
    fun_prop
  have hfin : (∫ v in (0 : ℝ)..T n, exp (-cum n a T v) * σ v) =
      ∑ k ∈ Finset.range n, exp (-cumAt a T k) *
        ∫ v in T k..T (k + 1), exp (-a k * (v - T k)) * σ v := by
    rw [← hT0, ← intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hc.intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (hT (Nat.le_succ k))] at hv
    rw [cum_eq_regime hT (Finset.mem_range.1 hk) hv, ← mul_assoc, ← exp_add]
    congr 2
    ring
  have htail : (∫ v in Set.Ioi (T n), exp (-cum n a T v) * σ v) =
      exp (-cumAt a T n) * pv (a n) σ (T n) := by
    have hpv : pv (a n) σ (T n) = ∫ v in Set.Ioi (T n), exp (-a n * (v - T n)) * σ v := by
      rw [pv, ← integral_Ioi_comp_add (fun v => exp (-a n * (v - T n)) * σ v) (T n)]
      congr 1
      funext u
      simp only [add_sub_cancel_left]
    rw [hpv, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [cum_eq_last hT (le_of_lt hv), ← mul_assoc, ← exp_add]
    congr 2
    ring
  rw [hsplit, hfin, htail]

/-- Cochrane (2023), §6.4.1, p. 196 (`r > g` in the last regime is necessary): if the last rate is
`a_n ≤ 0`, then with zero surpluses both `0` and `e^{A(t)}` are bounded solutions, and they
differ at date `0`. -/
theorem pw_not_unique_of_last_nonpos (hT : Monotone T) (ha : a n ≤ 0) :
    SolvesPW n a T (fun _ => 0) (fun t => exp (cum n a T t)) ∧
      BddOn (fun t => exp (cum n a T t)) ∧ SolvesPW n a T (fun _ => 0) (fun _ => 0) ∧
      BddOn (fun _ => (0 : ℝ)) ∧ exp (cum n a T 0) ≠ 0 := by
  have hc := cum_continuous n a T
  refine ⟨⟨(by fun_prop : Continuous fun t => exp (cum n a T t)).continuousOn,
    fun j hj t ht => ?_, fun t ht => ?_⟩, ?_, ⟨continuousOn_const, fun j _ t _ => ?_,
    fun t _ => ?_⟩, ⟨0, fun _ _ => by simp⟩, exp_ne_zero _⟩
  · refine (cum_hasDerivAt_regime hT hj ht).exp.congr_deriv ?_
    ring
  · refine (cum_hasDerivAt_last hT ht).exp.congr_deriv ?_
    ring
  · obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T n)).exists_bound_of_continuousOn
      (by fun_prop : Continuous fun t => exp (cum n a T t)).continuousOn
    refine ⟨max C (exp (cumAt a T n)), fun t ht => ?_⟩
    rcases le_total t (T n) with h | h
    · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
    · rw [abs_of_pos (exp_pos _), cum_eq_last hT h]
      refine le_trans ?_ (le_max_right _ _)
      exact exp_le_exp.2 (by nlinarith)
  · simpa using hasDerivAt_const t (0 : ℝ)
  · simpa using hasDerivAt_const t (0 : ℝ)

/-- Cochrane (2023), §6.4.1, p. 196 (**determinacy iff `r > g` in the last regime**): whatever
the signs of `r − g` before the last switch, bounded solutions are unique for every continuous
bounded surplus path iff the last rate is positive. -/
theorem pw_unique_iff_last_pos (hT : Monotone T) (hT0 : T 0 = 0) :
    (∀ σ : ℝ → ℝ, Continuous σ → (∃ M, ∀ u, |σ u| ≤ M) → ∀ x z, SolvesPW n a T σ x →
      SolvesPW n a T σ z → BddOn x → BddOn z → ∀ t, 0 ≤ t → x t = z t) ↔ 0 < a n := by
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    obtain ⟨h1, h2, h3, h4, h5⟩ := pw_not_unique_of_last_nonpos (a := a) hT hneg
    exact h5 (h _ continuous_const ⟨0, fun _ => by simp⟩ _ _ h1 h3 h2 h4 0 le_rfl)
  · rintro ha σ hσ ⟨M, hM⟩ x z hx hz hbx hbz t ht
    have h := (pw_existsUnique hT hT0 ha hσ hM).2.2
    rw [h x hx hbx t ht, h z hz hbz t ht]

/-- Cochrane (2023), §6.4.1, p. 196 (nominal determinacy with finitely many regimes): with nominal
debt `B₀ > 0`, `y₀ > 0`, `P₀ > 0` and `x₀ = B₀/(P₀ y₀)`, there is a bounded solution iff
`P₀ = B₀/(y₀ x̂₀)`. -/
theorem pw_nominal_determinacy (hT : Monotone T) (hT0 : T 0 = 0) (ha : 0 < a n)
    (hσ : Continuous σ) (hM : ∀ u, |σ u| ≤ M) {B0 y0 P0 : ℝ} (hB0 : 0 < B0) (hy0 : 0 < y0)
    (hP0 : 0 < P0) :
    (∃ x, SolvesPW n a T σ x ∧ x 0 = B0 / (P0 * y0) ∧ BddOn x) ↔
      P0 = B0 / (y0 * pwPV0 n a T σ) := by
  constructor
  · rintro ⟨x, hx, hx0, hb⟩
    have h := (pw_bddOn_iff hT hT0 ha hσ hM hx).1 hb
    rw [hx0] at h
    have hpv : 0 < pwPV0 n a T σ := by rw [← h]; positivity
    rw [← h]
    field_simp
  · intro hP
    have hpos : 0 < y0 * pwPV0 n a T σ := by
      have : 0 < B0 / (y0 * pwPV0 n a T σ) := hP ▸ hP0
      rcases div_pos_iff.1 this with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact h2
      · linarith
    have hpv : 0 < pwPV0 n a T σ := pos_of_mul_pos_right hpos hy0.le
    obtain ⟨h1, h2, -⟩ := pw_existsUnique hT hT0 ha hσ hM
    refine ⟨pwSol n a T σ, h1, ?_, h2⟩
    have h0 : pwSol n a T σ 0 = pwPV0 n a T σ := vocA_zero (cum_zero hT hT0) _
    rw [h0, hP]
    field_simp

/-! ### The two-regime case of `RvsG` -/

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime rates, `a₁` then `a₂`. -/
noncomputable def twoA (a₁ a₂ : ℝ) (k : ℕ) : ℝ := if k = 0 then a₁ else a₂

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime switch dates, `0` then `T₀`. -/
noncomputable def twoT (T0 : ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else T0

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime dates are monotone when `T₀ ≥ 0`. -/
theorem twoT_monotone {T0 : ℝ} (hT0 : 0 ≤ T0) : Monotone (twoT T0) := by
  intro i j hij
  unfold twoT
  split_ifs <;> first | exact le_rfl | exact hT0 | omega

/-- Cochrane (2023), §6.4.1, p. 196: the two-regime solution concept of `RvsG` is the case `n = 1`
of `SolvesPW`. -/
theorem solvesStep_iff (a₁ a₂ T0 : ℝ) (σ x : ℝ → ℝ) :
    SolvesStep a₁ a₂ T0 σ x ↔ SolvesPW 1 (twoA a₁ a₂) (twoT T0) σ x := by
  unfold SolvesStep SolvesPW twoA twoT
  simp only [Nat.lt_one_iff, forall_eq, ↓reduceIte, zero_add, one_ne_zero]

/-- Cochrane (2023), §6.4.1, p. 196 (the corrected 20-year formula is the case `n = 1`): the
general regime sum reduces to `RvsG.stepPV0`. -/
theorem pwPV0_two_regime {a₁ a₂ T0 : ℝ} (hT0 : 0 ≤ T0) (ha₂ : 0 < a₂) (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) : pwPV0 1 (twoA a₁ a₂) (twoT T0) σ = stepPV0 a₁ a₂ T0 σ := by
  rw [pwPV0_eq_sum (twoT_monotone hT0) (by simp [twoT]) (by simpa [twoA] using ha₂) hσ hM]
  simp [cumAt, twoA, twoT, stepPV0]

end Cochrane.FiscalConstraints.TidyR5PiecewiseRvsG
