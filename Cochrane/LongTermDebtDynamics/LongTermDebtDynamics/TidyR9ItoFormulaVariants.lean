/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR9ItoFormula

/-!
# Variants of Itô's formula: time dependence and discounting, `1/X`, `exp X`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Track 3, chunk B1. The valuation formulas
(1.33)–(1.34) discount with `Λ/P`; positive diffusive versions are built from Itô processes by
discounting `e^{−ru}`, reciprocals (`P = 1/(P⁻¹)`, `Λ/P = Λ·P⁻¹`) and exponentials (a stochastic
discount factor `exp(−∫ i du + …)`). Each needs Itô's formula for a function whose derivatives
are bounded only on the range of the process.

## Main results

* Localisation tools: `itoInt_congr_Icc`, `itoIntegrand_congr_Icc`, `itoProcess_congr_Icc`
  (only values on `[s, t]` matter), `hasDerivAt_ite_le` (gluing two `C¹` pieces at a point).
* `itoProcess_comp_range` (**`f(X)` is an Itô process when `f''` is bounded and `f'` is bounded
  on the range of `X`**).
* (a) `ito_formula_time_pathwise`, `itoProcess_comp_time` (**`f(u, X_u)` is an Itô process**,
  drift `f_t + f_x a + ½f_xx H²`, diffusion `f_x H`, for `C^{1,2}` `f` with bounded derivatives);
  `itoProcess_discount` (**discounting**: `e^{−ru}g(X_u)`, drift
  `e^{−ru}(−r g(X) + g'(X)a + ½g''(X)H²)`, diffusion `e^{−ru}g'(X)H`).
* (b) `itoProcess_inv` (**`1/X` for `X ≥ c > 0` on `[s, t]`**): drift `−a/X² + H²/X³`, diffusion
  `−H/X²`; via `invExt`, a `C²` function with bounded second derivative equal to `1/x` on
  `[c, ∞)`.
* (c) `itoProcess_exp` (**`exp X` for `|X| ≤ M` on `[s, t]`**): drift `e^X(a + ½H²)`, diffusion
  `e^X H`; via `expExt`, equal to `exp` on `[−M, M]` and quadratic outside.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR9ItoFormulaVariants

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7StieltjesSums
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools Cochrane.LongTermDebtDynamics.TidyR7BrownianQV
  Cochrane.LongTermDebtDynamics.TidyR7ItoL2 Cochrane.LongTermDebtDynamics.TidyR7ItoSums
  Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral Cochrane.LongTermDebtDynamics.TidyR7ItoUnbounded
  Cochrane.LongTermDebtDynamics.TidyR7ItoProducts Cochrane.LongTermDebtDynamics.TidyR7ItoProcess
  Cochrane.LongTermDebtDynamics.TidyR7ItoProductRule Cochrane.LongTermDebtDynamics.TidyR9ItoTaylor
  Cochrane.LongTermDebtDynamics.TidyR9ItoFormula
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-! ## Localisation to `[s, t]` -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the Itô integral depends only on the integrand on
`[s, t]`**: if `H = H'` there, `∫_s^t H dW = ∫_s^t H' dW` (the dyadic sums agree).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoInt_congr_Icc). -/
theorem itoInt_congr_Icc {H H' : ℝ → Ω → ℝ} (h : ∀ u ∈ Set.Icc s t, ∀ ω, H u ω = H' u ω) :
    itoInt P 𝓕 W H s t = itoInt P 𝓕 W H' s t := by
  classical
  unfold itoInt
  by_cases hst : s < t
  · have e : (fun k => itoSum W H (dyadic hst k)) = fun k => itoSum W H' (dyadic hst k) :=
      funext fun k => funext fun ω => Finset.sum_congr rfl fun i hi => by
        rw [h _ (t_mem _ (Finset.mem_range.1 hi).le)]
    have key : ∀ F G : ℕ → Ω → ℝ, F = G →
        (if h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P F Y then h.choose else 0)
          = (if h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P G Y then h.choose else 0) := by
      rintro F G rfl
      rfl
    simp only [hst, ↓reduceDIte]
    exact key _ _ e
  · simp only [hst, ↓reduceDIte]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an admissible integrand may be changed off `[s, t]`
(only its values on `[s, t]` are constrained).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoIntegrand_congr_Icc). -/
theorem itoIntegrand_congr_Icc {H H' : ℝ → Ω → ℝ} {C : ℝ} (hH : ItoIntegrand P 𝓕 H s t C)
    (h : ∀ u ∈ Set.Icc s t, ∀ ω, H u ω = H' u ω) : ItoIntegrand P 𝓕 H' s t C where
  adapted u hu := by
    have e : H' u = H u := funext fun ω => (h u hu ω).symm
    rw [e]
    exact hH.adapted u hu
  bound u hu ω := by
    rw [← h u hu ω]
    exact hH.bound u hu ω
  cont := by
    filter_upwards [hH.cont] with ω hω
    exact hω.congr fun u hu => (h u hu ω).symm

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **an Itô process is determined by its values and
coefficients on `[s, t]`**: changing `X`, `a`, `H` off `[s, t]` keeps it an Itô process.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoProcess_congr_Icc). -/
theorem itoProcess_congr_Icc {X a H Y a' H' : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hst : s ≤ t)
    (hXY : ∀ u ∈ Set.Icc s t, ∀ ω, X u ω = Y u ω) (ha : ∀ u ∈ Set.Icc s t, ∀ ω, a u ω = a' u ω)
    (hH : ∀ u ∈ Set.Icc s t, ∀ ω, H u ω = H' u ω) : ItoProcess P 𝓕 W Y a' H' s t Ca CH where
  adapted u hu := by
    have e : Y u = X u := funext fun ω => (hXY u hu ω).symm
    rw [e]
    exact hX.adapted u hu
  init := by
    have e : Y s = X s := funext fun ω => (hXY s ⟨le_rfl, hst⟩ ω).symm
    rw [e]
    exact hX.init
  drift := itoIntegrand_congr_Icc hX.drift ha
  diff := itoIntegrand_congr_Icc hX.diff hH
  eq u hu := by
    have e1 : itoInt P 𝓕 W H s u = itoInt P 𝓕 W H' s u :=
      itoInt_congr_Icc fun r hr => hH r ⟨hr.1, hr.2.trans hu.2⟩
    filter_upwards [hX.eq u hu] with ω hω
    rw [← hXY u hu ω, ← hXY s ⟨le_rfl, hst⟩ ω, hω, e1]
    congr 2
    refine intervalIntegral.integral_congr fun r hr => ha r ?_ ω
    rw [Set.uIcc_of_le hu.1] at hr
    exact ⟨hr.1, hr.2.trans hu.2⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (building `C²` functions for Itô's formula): **gluing
two differentiable pieces at `c`** with equal values and derivatives there gives a function
differentiable everywhere, with the glued derivative.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.hasDerivAt_ite_le). -/
theorem hasDerivAt_ite_le {q r q' r' : ℝ → ℝ} {c : ℝ} (hq : ∀ x ≤ c, HasDerivAt q (q' x) x)
    (hr : ∀ x, c ≤ x → HasDerivAt r (r' x) x) (h0 : q c = r c) (h1 : q' c = r' c) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ c then q y else r y) (if x ≤ c then q' x else r' x) x := by
  rcases lt_trichotomy x c with hx | hx | hx
  · simp only [hx.le, ↓reduceIte]
    refine (hq x hx.le).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [(le_of_lt (Set.mem_Iio.1 hy)), ↓reduceIte]
  · subst hx
    simp only [le_refl, ↓reduceIte]
    have hl : HasDerivWithinAt (fun y => if y ≤ x then q y else r y) (q' x) (Set.Iic x) x :=
      (hq x le_rfl).hasDerivWithinAt.congr (fun y hy => by
        simp only [Set.mem_Iic.1 hy, ↓reduceIte]) (by simp only [le_refl, ↓reduceIte])
    have hr' : HasDerivWithinAt (fun y => if y ≤ x then q y else r y) (q' x) (Set.Ici x) x := by
      rw [h1]
      refine (hr x le_rfl).hasDerivWithinAt.congr (fun y hy => ?_)
        (by simp only [le_refl, ↓reduceIte, h0])
      rcases (Set.mem_Ici.1 hy).eq_or_lt with hxy | hxy
      · simp only [← hxy, le_refl, ↓reduceIte, h0]
      · simp only [not_le.2 hxy, ↓reduceIte]
    have h := hl.union hr'
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h
  · simp only [not_le.2 hx, ↓reduceIte]
    refine (hr x hx.le).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [not_le.2 (Set.mem_Ioi.1 hy), ↓reduceIte]

/-! ## `f(X)` with derivatives bounded on the range -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `f(X)` is an Itô process when `f''` is bounded and
continuous and `f'` is bounded on the range of `X`** (`|f'(X_u)| ≤ L₁` on `[s, t]`), `f(X_s)`
square integrable, `X` an Itô process with a.s. continuous paths, `0 ≤ s`: drift
`f'(X)a + ½f''(X)H²`, diffusion `f'(X)H`.
Generalises `TidyR9ItoFormula.itoProcess_comp` (global bound on `f'`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoProcess_comp_range). -/
theorem itoProcess_comp_range (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (cf'' : Continuous f'') {L1 L2 : ℝ} (hf''b : ∀ x, |f'' x| ≤ L2)
    (hf'X : ∀ u ∈ Set.Icc s t, ∀ ω, |f' (X u ω)| ≤ L1)
    (hinit : MemLp (fun ω => f (X s ω)) 2 P) :
    ItoProcess P 𝓕 W (fun u ω => f (X u ω))
      (fun u ω => f' (X u ω) * a u ω + f'' (X u ω) / 2 * (H u ω * H u ω))
      (fun u ω => f' (X u ω) * H u ω) s t (L1 * Ca + L2 / 2 * (CH * CH)) (L1 * CH) := by
  have cf : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have cf' : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
  have h1 : ItoIntegrand P 𝓕 (fun u ω => f' (X u ω)) s t L1 :=
    { adapted := fun u hu => cf'.comp_stronglyMeasurable (hX.adapted u hu)
      bound := hf'X
      cont := by
        filter_upwards [hXc] with ω hω
        exact cf'.comp_continuousOn hω }
  have h2 : ItoIntegrand P 𝓕 (fun u ω => f'' (X u ω) / 2) s t (L2 / 2) :=
    itoIntegrand_comp (g := fun _ x => f'' x / 2) hX.adapted hXc
      ((cf''.comp continuous_snd).div_const 2) fun _ _ x => by
        rw [abs_div, abs_two]
        linarith [hf''b x]
  exact
    { adapted := fun u hu => cf.comp_stronglyMeasurable (hX.adapted u hu)
      init := hinit
      drift := (itoIntegrand_mul h1 hX.drift).add (itoIntegrand_mul h2
        (itoIntegrand_mul hX.diff hX.diff))
      diff := itoIntegrand_mul h1 hX.diff
      eq := fun u hu => by
        rcases hu.1.lt_or_eq with hsu | hsu
        · have h := ito_formula_pathwise hB hW h𝓕 hs hsu (itoProcess_restrict hX hu.2)
            (by filter_upwards [hXc] with ω hω; exact hω.mono (Set.Icc_subset_Icc le_rfl hu.2))
            hf hf' cf'' hf''b
          filter_upwards [h] with ω hω
          linarith
        · subst hsu
          refine ae_of_all _ fun ω => ?_
          simp [itoInt_of_le le_rfl] }

/-! ## (a) Time dependence and discounting -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Itô's formula with time dependence, pathwise.** For
`f(u, x)` with jointly continuous partials `f_t`, `f_x`, `f_xx` bounded on `[s, t] × ℝ` and an Itô
process with a.s. continuous paths, `0 ≤ s < t`, a.s.
`f(t, X_t) − f(s, X_s) = ∫_s^t (f_t + f_x a + ½f_xx H²)(u, X_u) du + ∫_s^t f_x(u, X)H dW`.
The pathwise form of `TidyR9ItoFormula.ito_formula_time`; generalises
`TidyR9ItoFormula.ito_formula_pathwise`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.ito_formula_time_pathwise). -/
theorem ito_formula_time_pathwise (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f ft fx fxx : ℝ → ℝ → ℝ} (hft : ∀ u x, HasDerivAt (fun r => f r x) (ft u x) u)
    (hfx : ∀ u x, HasDerivAt (f u) (fx u x) x) (hfxx : ∀ u x, HasDerivAt (fx u) (fxx u x) x)
    (cf : Continuous (Function.uncurry f)) (cft : Continuous (Function.uncurry ft))
    (cfx : Continuous (Function.uncurry fx)) (cfxx : Continuous (Function.uncurry fxx))
    {Lt L1 L2 : ℝ} (hftb : ∀ u ∈ Set.Icc s t, ∀ x, |ft u x| ≤ Lt)
    (hfxb : ∀ u ∈ Set.Icc s t, ∀ x, |fx u x| ≤ L1)
    (hfxxb : ∀ u ∈ Set.Icc s t, ∀ x, |fxx u x| ≤ L2) :
    (fun ω => f t (X t ω) - f s (X s ω)) =ᵐ[P] fun ω =>
      (∫ u in s..t, (ft u (X u ω) + fx u (X u ω) * a u ω
        + fxx u (X u ω) / 2 * (H u ω * H u ω)))
      + itoInt P 𝓕 W (fun u ω => fx u (X u ω) * H u ω) s t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hG1 := msIntegrand_comp_of_bound (P := P) hX.adapted hXc cfx hfxb
  have e1 := dtInt_ae_eq_integral hst.le (MSIntegrand.mul_itoIntegrand hG1 hX.drift) (by
    filter_upwards [hXc, hX.drift.cont] with ω h1 h2
    exact (cfx.comp_continuousOn (continuousOn_id.prodMk h1)).mul h2)
  filter_upwards [ito_formula_time hB hW h𝓕 hs hst hX hXc hft hfx hfxx cf cft cfxx hftb hfxxb hG1,
    e1, hXc, hX.drift.cont, hX.diff.cont] with ω h0 h1 hc ha hH
  rw [h0, h1]
  have c0 : ContinuousOn (fun u => (u, X u ω)) (Set.Icc s t) := continuousOn_id.prodMk hc
  have i0 : IntervalIntegrable (fun u => ft u (X u ω)) MeasureTheory.volume s t :=
    (cft.comp_continuousOn c0).intervalIntegrable_of_Icc hst.le
  have i1 : IntervalIntegrable (fun u => fx u (X u ω) * a u ω) MeasureTheory.volume s t :=
    ((cfx.comp_continuousOn c0).mul ha).intervalIntegrable_of_Icc hst.le
  have i2 : IntervalIntegrable (fun u => fxx u (X u ω) / 2 * (H u ω * H u ω))
      MeasureTheory.volume s t :=
    (((cfxx.comp_continuousOn c0).div_const 2).mul (hH.mul hH)).intervalIntegrable_of_Icc hst.le
  rw [intervalIntegral.integral_add (i0.add i1) i2, intervalIntegral.integral_add i0 i1]
  have e2 : (∫ u in s..t, fxx u (X u ω) / 2 * (H u ω * H u ω))
      = (∫ u in s..t, fxx u (X u ω) * (H u ω * H u ω)) / 2 := by
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun u _ => by ring
  rw [e2]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `f(u, X_u)` is an Itô process** (`C^{1,2}` `f` with
jointly continuous partials bounded on `[s, t] × ℝ`, `X` an Itô process with a.s. continuous
paths, `0 ≤ s ≤ t`): drift `f_t + f_x a + ½f_xx H²`, diffusion `f_x H`.
Generalises `TidyR9ItoFormula.itoProcess_comp`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoProcess_comp_time). -/
theorem itoProcess_comp_time (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f ft fx fxx : ℝ → ℝ → ℝ} (hft : ∀ u x, HasDerivAt (fun r => f r x) (ft u x) u)
    (hfx : ∀ u x, HasDerivAt (f u) (fx u x) x) (hfxx : ∀ u x, HasDerivAt (fx u) (fxx u x) x)
    (cf : Continuous (Function.uncurry f)) (cft : Continuous (Function.uncurry ft))
    (cfx : Continuous (Function.uncurry fx)) (cfxx : Continuous (Function.uncurry fxx))
    {Lt L1 L2 : ℝ} (hftb : ∀ u ∈ Set.Icc s t, ∀ x, |ft u x| ≤ Lt)
    (hfxb : ∀ u ∈ Set.Icc s t, ∀ x, |fx u x| ≤ L1)
    (hfxxb : ∀ u ∈ Set.Icc s t, ∀ x, |fxx u x| ≤ L2) :
    ItoProcess P 𝓕 W (fun u ω => f u (X u ω))
      (fun u ω => ft u (X u ω) + fx u (X u ω) * a u ω + fxx u (X u ω) / 2 * (H u ω * H u ω))
      (fun u ω => fx u (X u ω) * H u ω) s t (Lt + L1 * Ca + L2 / 2 * (CH * CH)) (L1 * CH) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hs_mem : s ∈ Set.Icc s t := ⟨le_rfl, hst⟩
  have h1 : ItoIntegrand P 𝓕 (fun u ω => fx u (X u ω)) s t L1 :=
    itoIntegrand_comp hX.adapted hXc cfx hfxb
  have h2 : ItoIntegrand P 𝓕 (fun u ω => fxx u (X u ω) / 2) s t (L2 / 2) :=
    itoIntegrand_comp (g := fun u x => fxx u x / 2) hX.adapted hXc (cfxx.div_const 2)
      fun u hu x => by
        rw [abs_div, abs_two]
        linarith [hfxxb u hu x]
  exact
    { adapted := fun u hu => stronglyMeasurable_comp cf (hX.adapted u hu)
      init := memLp_comp_lipschitz hX.init (cf.comp (continuous_const.prodMk continuous_id))
        ((abs_nonneg _).trans (hfxb s hs_mem 0))
        (abs_sub_le_of_deriv_bound (hfx s) (hfxb s hs_mem))
      drift := ((itoIntegrand_comp hX.adapted hXc cft hftb).add
        (itoIntegrand_mul h1 hX.drift)).add (itoIntegrand_mul h2
          (itoIntegrand_mul hX.diff hX.diff))
      diff := itoIntegrand_mul h1 hX.diff
      eq := fun u hu => by
        rcases hu.1.lt_or_eq with hsu | hsu
        · have hsub : ∀ r ∈ Set.Icc s u, r ∈ Set.Icc s t := fun r hr => ⟨hr.1, hr.2.trans hu.2⟩
          have h := ito_formula_time_pathwise hB hW h𝓕 hs hsu (itoProcess_restrict hX hu.2)
            (by filter_upwards [hXc] with ω hω; exact hω.mono (Set.Icc_subset_Icc le_rfl hu.2))
            hft hfx hfxx cf cft cfx cfxx (fun r hr => hftb r (hsub r hr))
            (fun r hr => hfxb r (hsub r hr)) (fun r hr => hfxxb r (hsub r hr))
          filter_upwards [h] with ω hω
          linarith
        · subst hsu
          refine ae_of_all _ fun ω => ?_
          simp [itoInt_of_le le_rfl] }

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (discounting, `e^{−rt}`-type factors of (1.33)):
`e^{−ru}g(X_u)` is an Itô process** for `r ≥ 0`, `0 ≤ s ≤ t`, `g ∈ C²` with `|g| ≤ L₀`,
`|g'| ≤ L₁`, `|g''| ≤ L₂`, `g''` continuous, `X` an Itô process with a.s. continuous paths:
drift `e^{−ru}(−r g(X) + g'(X)a + ½g''(X)H²)`, diffusion `e^{−ru}g'(X)H`.
An instance of `itoProcess_comp_time`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoProcess_discount). -/
theorem itoProcess_discount (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t)) {r : ℝ} (hr : 0 ≤ r)
    {g g' g'' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    (cg'' : Continuous g'') {L0 L1 L2 : ℝ} (hgb : ∀ x, |g x| ≤ L0) (hg'b : ∀ x, |g' x| ≤ L1)
    (hg''b : ∀ x, |g'' x| ≤ L2) :
    ItoProcess P 𝓕 W (fun u ω => Real.exp (-r * u) * g (X u ω))
      (fun u ω => Real.exp (-r * u) * (-r * g (X u ω) + g' (X u ω) * a u ω
        + g'' (X u ω) / 2 * (H u ω * H u ω)))
      (fun u ω => Real.exp (-r * u) * g' (X u ω) * H u ω) s t
      (r * L0 + L1 * Ca + L2 / 2 * (CH * CH)) (L1 * CH) := by
  have cg : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have cg' : Continuous g' := continuous_iff_continuousAt.2 fun x => (hg' x).continuousAt
  have ce : Continuous fun q : ℝ × ℝ => Real.exp (-r * q.1) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_fst)
  have hexp : ∀ u ∈ Set.Icc s t, Real.exp (-r * u) ≤ 1 := fun u hu =>
    Real.exp_le_one_iff.2 (by nlinarith [hs.trans hu.1])
  have hexp0 : ∀ u, 0 ≤ Real.exp (-r * u) := fun u => (Real.exp_pos _).le
  have h := itoProcess_comp_time (f := fun u x => Real.exp (-r * u) * g x)
    (ft := fun u x => -r * Real.exp (-r * u) * g x) (fx := fun u x => Real.exp (-r * u) * g' x)
    (fxx := fun u x => Real.exp (-r * u) * g'' x) (Lt := r * L0) (L1 := L1) (L2 := L2)
    hB hW h𝓕 hs hst hX hXc
    (fun u x => by
      have h1 := HasDerivAt.mul_const (HasDerivAt.exp
        (HasDerivAt.const_mul (-r) (hasDerivAt_id' u))) (g x)
      convert h1 using 1
      ring)
    (fun u x => (hg x).const_mul _) (fun u x => (hg' x).const_mul _)
    (ce.mul (cg.comp continuous_snd))
    ((continuous_const.mul ce).mul (cg.comp continuous_snd))
    (ce.mul (cg'.comp continuous_snd)) (ce.mul (cg''.comp continuous_snd))
    (fun u hu x => by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hr, abs_of_nonneg (hexp0 u)]
      have := mul_le_mul (hexp u hu) (hgb x) (abs_nonneg _) zero_le_one
      nlinarith [abs_nonneg (g x)])
    (fun u hu x => by
      rw [abs_mul, abs_of_nonneg (hexp0 u)]
      have := mul_le_mul (hexp u hu) (hg'b x) (abs_nonneg _) zero_le_one
      linarith)
    (fun u hu x => by
      rw [abs_mul, abs_of_nonneg (hexp0 u)]
      have := mul_le_mul (hexp u hu) (hg''b x) (abs_nonneg _) zero_le_one
      linarith)
  exact itoProcess_of_coeff_eq h (fun u ω => by ring) (fun u ω => by ring)

/-! ## (b) The reciprocal `1/X` -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **a `C²` extension of `1/x` from `[c, ∞)`**: the
quadratic Taylor polynomial of `1/x` at `c` for `x ≤ c`, and `1/x` for `x > c`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.invExt). -/
noncomputable def invExt (c x : ℝ) : ℝ :=
  if x ≤ c then c⁻¹ - (x - c) * (c ^ 2)⁻¹ + (x - c) ^ 2 * (c ^ 3)⁻¹ else x⁻¹

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the derivative of `invExt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.invExt'). -/
noncomputable def invExt' (c x : ℝ) : ℝ :=
  if x ≤ c then -(c ^ 2)⁻¹ + 2 * (x - c) * (c ^ 3)⁻¹ else -(x ^ 2)⁻¹

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the second derivative of `invExt`,
`2/max(x, c)³` (continuous, bounded by `2/c³`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.invExt''). -/
noncomputable def invExt'' (c x : ℝ) : ℝ := 2 * (max x c ^ 3)⁻¹

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `invExt' = d invExt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.hasDerivAt_invExt). -/
theorem hasDerivAt_invExt {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (invExt c) (invExt' c x) x := by
  have h := hasDerivAt_ite_le (c := c)
    (q := fun x => c⁻¹ - (x - c) * (c ^ 2)⁻¹ + (x - c) ^ 2 * (c ^ 3)⁻¹)
    (r := fun x => x⁻¹) (q' := fun x => -(c ^ 2)⁻¹ + 2 * (x - c) * (c ^ 3)⁻¹)
    (r' := fun x => -(x ^ 2)⁻¹)
    (fun x _ => by
      have h1 := HasDerivAt.add (HasDerivAt.sub (hasDerivAt_const x c⁻¹)
        (HasDerivAt.mul_const (HasDerivAt.sub_const c (hasDerivAt_id' x)) ((c ^ 2)⁻¹)))
        (HasDerivAt.mul_const (HasDerivAt.pow (HasDerivAt.sub_const c (hasDerivAt_id' x)) 2)
          ((c ^ 3)⁻¹))
      convert h1 using 1
      push_cast
      ring)
    (fun x hx => hasDerivAt_inv (hc.trans_le hx).ne') (by simp) (by simp) x
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `invExt'' = d invExt'`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.hasDerivAt_invExt'). -/
theorem hasDerivAt_invExt' {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (invExt' c) (invExt'' c x) x := by
  have h := hasDerivAt_ite_le (c := c)
    (q := fun x => -(c ^ 2)⁻¹ + 2 * (x - c) * (c ^ 3)⁻¹)
    (r := fun x => -(x ^ 2)⁻¹) (q' := fun _ => 2 * (c ^ 3)⁻¹)
    (r' := fun x => 2 * (x ^ 3)⁻¹)
    (fun x _ => by
      have h1 := HasDerivAt.const_add (-(c ^ 2)⁻¹) (HasDerivAt.mul_const (HasDerivAt.const_mul 2
        (HasDerivAt.sub_const c (hasDerivAt_id' x))) ((c ^ 3)⁻¹))
      convert h1 using 1
      ring)
    (fun x hx => by
      have hx0 : x ≠ 0 := (hc.trans_le hx).ne'
      have h1 := HasDerivAt.neg (HasDerivAt.inv (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0))
      convert h1 using 1
      field_simp
      ring)
    (by simp) (by simp) x
  have e : (if x ≤ c then 2 * (c ^ 3)⁻¹ else 2 * (x ^ 3)⁻¹) = invExt'' c x := by
    unfold invExt''
    split_ifs with hx
    · rw [max_eq_right hx]
    · rw [max_eq_left (not_le.1 hx).le]
  rw [e] at h
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `invExt''` is continuous and bounded by `2/c³`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.invExt''_props). -/
theorem invExt''_props {c : ℝ} (hc : 0 < c) :
    Continuous (invExt'' c) ∧ ∀ x, |invExt'' c x| ≤ 2 * (c ^ 3)⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · refine continuous_const.mul (Continuous.inv₀ ((continuous_id.max continuous_const).pow 3)
      fun x => pow_ne_zero 3 (hc.trans_le (le_max_right x c)).ne')
  · have hm : c ≤ max x c := le_max_right x c
    have hm0 : 0 < max x c := hc.trans_le hm
    rw [invExt'', abs_of_nonneg (by positivity)]
    have : (max x c ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hm 3)
    linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: on `[c, ∞)`, `invExt = 1/x`, `invExt' = −1/x²`,
`invExt'' = 2/x³`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.invExt_of_le). -/
theorem invExt_of_le {c x : ℝ} (hcx : c ≤ x) :
    invExt c x = x⁻¹ ∧ invExt' c x = -(x ^ 2)⁻¹ ∧ invExt'' c x = 2 * (x ^ 3)⁻¹ := by
  refine ⟨?_, ?_, by rw [invExt'', max_eq_left hcx]⟩
  · unfold invExt
    split_ifs with h
    · have : x = c := le_antisymm h hcx
      subst this
      ring
    · rfl
  · unfold invExt'
    split_ifs with h
    · have : x = c := le_antisymm h hcx
      subst this
      ring
    · rfl

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the reciprocal, e.g. `1/P` or `Λ/P`): if `X` is an
Itô process with a.s. continuous paths and `X ≥ c > 0` on `[s, t]`, `0 ≤ s ≤ t`, then `1/X` is an
Itô process** with drift `−a/X² + H²/X³` and diffusion `−H/X²`.
An instance of `itoProcess_comp_range`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoProcess_inv). -/
theorem itoProcess_inv (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t)) {c : ℝ} (hc : 0 < c)
    (hXlow : ∀ u ∈ Set.Icc s t, ∀ ω, c ≤ X u ω) :
    ItoProcess P 𝓕 W (fun u ω => (X u ω)⁻¹)
      (fun u ω => -(a u ω / X u ω ^ 2) + H u ω ^ 2 / X u ω ^ 3)
      (fun u ω => -(H u ω / X u ω ^ 2)) s t
      ((c ^ 2)⁻¹ * Ca + 2 * (c ^ 3)⁻¹ / 2 * (CH * CH)) ((c ^ 2)⁻¹ * CH) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨cE, bE⟩ := invExt''_props hc
  have hpos : ∀ u ∈ Set.Icc s t, ∀ ω, 0 < X u ω := fun u hu ω => hc.trans_le (hXlow u hu ω)
  have hinit : MemLp (fun ω => invExt c (X s ω)) 2 P := by
    refine memLp_of_bound (C := c⁻¹) ((continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_invExt hc x).continuousAt).measurable.comp
        ((hX.adapted s ⟨le_rfl, hst⟩).mono (𝓕.le s)).measurable) fun ω => ?_
    have h1 := hXlow s ⟨le_rfl, hst⟩ ω
    rw [(invExt_of_le h1).1, abs_of_pos (inv_pos.2 (hc.trans_le h1))]
    exact inv_anti₀ hc h1
  have h := itoProcess_comp_range hB hW h𝓕 hs hX hXc (hasDerivAt_invExt hc)
    (hasDerivAt_invExt' hc) cE bE (L1 := (c ^ 2)⁻¹) (fun u hu ω => by
      have h1 := hXlow u hu ω
      have h0 : 0 < X u ω := hc.trans_le h1
      rw [(invExt_of_le h1).2.1, abs_neg, abs_of_pos (by positivity)]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le h1 2)) hinit
  refine itoProcess_congr_Icc h hst (fun u hu ω => (invExt_of_le (hXlow u hu ω)).1)
    (fun u hu ω => ?_) (fun u hu ω => ?_)
  · obtain ⟨-, h2, h3⟩ := invExt_of_le (hXlow u hu ω)
    rw [h2, h3]
    have := (hpos u hu ω).ne'
    field_simp
  · obtain ⟨-, h2, -⟩ := invExt_of_le (hXlow u hu ω)
    rw [h2]
    have := (hpos u hu ω).ne'
    field_simp

/-! ## (c) The exponential of a bounded Itô process -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **a `C²` extension of `exp` from `[−M, M]`**,
quadratic Taylor polynomials outside.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.expExt). -/
noncomputable def expExt (M x : ℝ) : ℝ :=
  if x ≤ -M then Real.exp (-M) * (1 + (x + M) + (x + M) ^ 2 / 2)
  else if x ≤ M then Real.exp x else Real.exp M * (1 + (x - M) + (x - M) ^ 2 / 2)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the derivative of `expExt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.expExt'). -/
noncomputable def expExt' (M x : ℝ) : ℝ :=
  if x ≤ -M then Real.exp (-M) * (1 + (x + M))
  else if x ≤ M then Real.exp x else Real.exp M * (1 + (x - M))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the second derivative of `expExt`,
`exp(max(−M, min(x, M)))`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.expExt''). -/
noncomputable def expExt'' (M x : ℝ) : ℝ := Real.exp (max (-M) (min x M))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `expExt' = d expExt`, `0 ≤ M`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.hasDerivAt_expExt). -/
theorem hasDerivAt_expExt {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    HasDerivAt (expExt M) (expExt' M x) x := by
  have hin : ∀ x, HasDerivAt (fun y => if y ≤ M then Real.exp y
      else Real.exp M * (1 + (y - M) + (y - M) ^ 2 / 2))
      (if x ≤ M then Real.exp x else Real.exp M * (1 + (x - M))) x := fun x =>
    hasDerivAt_ite_le (c := M) (q := Real.exp)
      (r := fun y => Real.exp M * (1 + (y - M) + (y - M) ^ 2 / 2)) (q' := Real.exp)
      (r' := fun y => Real.exp M * (1 + (y - M)))
      (fun x _ => Real.hasDerivAt_exp x)
      (fun x _ => by
        have h1 := HasDerivAt.const_mul (Real.exp M) (HasDerivAt.add (HasDerivAt.const_add 1
          (HasDerivAt.sub_const M (hasDerivAt_id' x))) (HasDerivAt.div_const
            (HasDerivAt.pow (HasDerivAt.sub_const M (hasDerivAt_id' x)) 2) 2))
        convert h1 using 1
        push_cast
        ring)
      (by simp) (by simp) x
  have h := hasDerivAt_ite_le (c := -M)
    (q := fun y => Real.exp (-M) * (1 + (y + M) + (y + M) ^ 2 / 2))
    (q' := fun y => Real.exp (-M) * (1 + (y + M)))
    (r' := fun x => if x ≤ M then Real.exp x else Real.exp M * (1 + (x - M)))
    (fun x _ => by
      have h1 := HasDerivAt.const_mul (Real.exp (-M)) (HasDerivAt.add (HasDerivAt.const_add 1
        (HasDerivAt.add_const M (hasDerivAt_id' x))) (HasDerivAt.div_const
          (HasDerivAt.pow (HasDerivAt.add_const M (hasDerivAt_id' x)) 2) 2))
      convert h1 using 1
      push_cast
      ring)
    (fun x _ => hin x)
    (by simp [show -M ≤ M by linarith]) (by simp [show -M ≤ M by linarith]) x
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `expExt'' = d expExt'`, `0 ≤ M`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.hasDerivAt_expExt'). -/
theorem hasDerivAt_expExt' {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    HasDerivAt (expExt' M) (expExt'' M x) x := by
  have hin : ∀ x, HasDerivAt (fun y => if y ≤ M then Real.exp y
      else Real.exp M * (1 + (y - M)))
      (if x ≤ M then Real.exp x else Real.exp M) x := fun x =>
    hasDerivAt_ite_le (c := M) (q := Real.exp) (r := fun y => Real.exp M * (1 + (y - M)))
      (q' := Real.exp) (r' := fun _ => Real.exp M)
      (fun x _ => Real.hasDerivAt_exp x)
      (fun x _ => by
        have h1 := HasDerivAt.const_mul (Real.exp M) (HasDerivAt.const_add 1
          (HasDerivAt.sub_const M (hasDerivAt_id' x)))
        convert h1 using 1
        ring)
      (by simp) rfl x
  have h := hasDerivAt_ite_le (c := -M)
    (q := fun y => Real.exp (-M) * (1 + (y + M))) (q' := fun _ => Real.exp (-M))
    (r' := fun x => if x ≤ M then Real.exp x else Real.exp M)
    (fun x _ => by
      have h1 := HasDerivAt.const_mul (Real.exp (-M)) (HasDerivAt.const_add 1
        (HasDerivAt.add_const M (hasDerivAt_id' x)))
      convert h1 using 1
      ring)
    (fun x _ => hin x)
    (by simp [show -M ≤ M by linarith]) (by simp [show -M ≤ M by linarith]) x
  have e : (if x ≤ -M then Real.exp (-M) else if x ≤ M then Real.exp x else Real.exp M)
      = expExt'' M x := by
    unfold expExt''
    split_ifs with h1 h2
    · rw [min_eq_left (h1.trans (by linarith)), max_eq_left h1]
    · rw [min_eq_left h2, max_eq_right (not_le.1 h1).le]
    · rw [min_eq_right (not_le.1 h2).le, max_eq_right (by linarith)]
  rw [e] at h
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: on `[−M, M]`, `expExt = expExt' = expExt'' = exp`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.expExt_of_abs_le). -/
theorem expExt_of_abs_le {M x : ℝ} (hx : |x| ≤ M) :
    expExt M x = Real.exp x ∧ expExt' M x = Real.exp x ∧ expExt'' M x = Real.exp x := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  refine ⟨?_, ?_, ?_⟩
  · unfold expExt
    split_ifs with h3
    · have : x = -M := le_antisymm h3 h1
      subst this
      simp
    · rfl
  · unfold expExt'
    split_ifs with h3
    · have : x = -M := le_antisymm h3 h1
      subst this
      simp
    · rfl
  · unfold expExt''
    rw [min_eq_left h2, max_eq_right h1]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (a positive stochastic discount factor
`exp(X)`): if `X` is an Itô process with a.s. continuous paths and `|X| ≤ M` on `[s, t]`,
`0 ≤ s ≤ t`, then `exp X` is an Itô process** with drift `e^X(a + ½H²)` and diffusion `e^X H`.
Applies e.g. to `X = −∫_s^· i du` with a bounded continuous rate `i` (`H = 0`).
An instance of `itoProcess_comp_range`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormulaVariants.itoProcess_exp). -/
theorem itoProcess_exp (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t)) {M : ℝ} (hM : 0 ≤ M)
    (hXb : ∀ u ∈ Set.Icc s t, ∀ ω, |X u ω| ≤ M) :
    ItoProcess P 𝓕 W (fun u ω => Real.exp (X u ω))
      (fun u ω => Real.exp (X u ω) * (a u ω + H u ω ^ 2 / 2))
      (fun u ω => Real.exp (X u ω) * H u ω) s t
      (Real.exp M * Ca + Real.exp M / 2 * (CH * CH)) (Real.exp M * CH) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have cE : Continuous (expExt'' M) :=
    Real.continuous_exp.comp (continuous_const.max (continuous_id.min continuous_const))
  have bE : ∀ x, |expExt'' M x| ≤ Real.exp M := fun x => by
    rw [expExt'', abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (max_le (by linarith) (min_le_right _ _))
  have hinit : MemLp (fun ω => expExt M (X s ω)) 2 P := by
    refine memLp_of_bound (C := Real.exp M) ((continuous_iff_continuousAt.2 fun x =>
      (hasDerivAt_expExt hM x).continuousAt).measurable.comp
        ((hX.adapted s ⟨le_rfl, hst⟩).mono (𝓕.le s)).measurable) fun ω => ?_
    have h1 := hXb s ⟨le_rfl, hst⟩ ω
    rw [(expExt_of_abs_le h1).1, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans h1)
  have h := itoProcess_comp_range hB hW h𝓕 hs hX hXc (hasDerivAt_expExt hM)
    (hasDerivAt_expExt' hM) cE bE (L1 := Real.exp M) (fun u hu ω => by
      have h1 := hXb u hu ω
      rw [(expExt_of_abs_le h1).2.1, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans h1)) hinit
  refine itoProcess_congr_Icc h hst (fun u hu ω => (expExt_of_abs_le (hXb u hu ω)).1)
    (fun u hu ω => ?_) (fun u hu ω => ?_)
  · obtain ⟨-, h2, h3⟩ := expExt_of_abs_le (hXb u hu ω)
    rw [h2, h3]
    ring
  · rw [(expExt_of_abs_le (hXb u hu ω)).2.1]

end Cochrane.LongTermDebtDynamics.TidyR9ItoFormulaVariants
