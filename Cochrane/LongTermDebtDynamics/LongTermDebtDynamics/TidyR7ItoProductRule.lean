/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7ItoCovariation
import LongTermDebtDynamics.TidyR7ItoBridge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Itô product rule `d(XY) = X dY + Y dX + d[X, Y]`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5d of the Itô track). The book's step (1.32) writes
`E_t d(ΛB/P) = Λ/P·dB + B·E_t d(Λ/P)` with no covariation term; that is the product rule of the
finite-variation calculus (`TidyR7ProductStep.ProductStepData.product_step`). When both
factors diffuse the product rule acquires the bracket `d[X, Y] = HK dt`. This module proves it.

## Setting

`X`, `Y` Itô processes on `[s, t]`, `0 ≤ s < t` (`TidyR7ItoProcess.ItoProcess`):
`X_u = X_s + ∫_s^u a dr + ∫_s^u H dW`, `Y_u = Y_s + ∫_s^u b dr + ∫_s^u K dW`, with `a, b, H, K`
bounded adapted a.s.-continuous and `X_s, Y_s` square integrable. The statements are at the two
fixed times `s < t`, through `itoInt` at partition points (no continuous version needed).

`∫ X dY := ∫_s^t X_ub_u du + ∫_s^t X K dW`; the time integral is the mean-square one
(`TidyR7ItoProducts.dtInt`, equal to the pathwise integral when the paths of `X` are a.s.
continuous, `product_rule_pathwise`), and the stochastic integral is the Itô integral of the
unbounded integrand `XK` (`TidyR7ItoUnbounded`).

## Main results

* `product_rule` (**Itô's product rule**): a.s.
  `X_tY_t − X_sY_s = ∫_s^t X dY + ∫_s^t Y dX + ∫_s^t H_uK_u du`, from the exact partition identity
  (`TidyR7StieltjesCalculus.prod_partition_identity`), the `L²` limits
  `TidyR7ItoCovariation.L2Tendsto_sumRS` and the `L¹` bracket limit
  `TidyR7ItoCovariation.tendsto_integral_abs_sumCross`.
* `product_rule_pathwise` (pathwise drift integrals), `product_rule_noDrift` (`a = b = 0`:
  `X_tY_t − X_sY_s = ∫X K dW + ∫Y H dW + ∫HK du`), `ito_formula_sq` (`Y = X`:
  `X_t² − X_s² = 2∫X dX + ∫H² du`).
* `condExp_product_rule` (the form used by (1.32)):
  `E_s[X_tY_t − X_sY_s] = E_s[∫_s^t (X b + Y a + H K) du]`, the `dW` integrals having
  conditional mean `0` (`TidyR7ItoUnbounded.condExp_itoInt_ms`).
* `tendsto_condExp_sumRS`, `tendsto_condExp_sumCross`, `expected_increment_product_rule` (the
  "expected increment" reading of Track 1): along any partitions with mesh `→ 0`, in `L¹`,
  `E_s[Σ X_iΔY_i] → E_s[∫X b du]`, `E_s[Σ Y_iΔX_i] → E_s[∫Y a du]`,
  `E_s[Σ ΔX_iΔY_i] → E_s[∫HK du]`: `E_s d(XY) = X E_s dY + Y E_s dX + E_s d[X, Y]` with
  `d[X, Y] = HK dt`.
* `condExp_product_rule_bookForm_iff`: the book-form identity (no bracket)
  `E_s[X_tY_t − X_sY_s] = E_s[∫X b du] + E_s[∫Y a du]` holds iff `E_s[∫_s^t HK du] = 0`.
* Links: `condExp_product_rule_bv` (`H = 0`: the bracket vanishes and the rule is
  `TidyR7ProductStep.ProductStepData.product_step`'s
  `E_s[B_tX_t − B_sX_s] = E_s[∫X dB] + E_s[∫B dA]` with
  `B = X`, `A = ∫b du`, `M = ∫K dW`); `itoProcess_bm` (`W` is an Itô process),
  `ito_formula_bm` (`W_t² − W_s² = 2∫_s^t W dW + (t − s)`, consistent with
  `TidyR7ItoBridge.itoInt_bm`: `itoInt_bm_of_product_rule` re-derives it),
  `product_rule_bm_id` (`tW_t − sW_s = ∫_s^t W du + ∫_s^t u dW`).
* Non-vacuity on the constructed motion `TidyR7BrownianExist.bmPath`: `ito_formula_bmPath`
  (`W_1² = 2∫_0^1 W dW + 1`), `integral_ito_formula_bmPath` (`E[W_1²] = 1`, `E[2∫W dW] = 0`,
  `E[∫_0^1 1 du] = 1`), `not_bookForm_bmPath` (the book-form identity fails for `X = Y = W`).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7ItoProductRule

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7StieltjesSums
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoL2
  Cochrane.LongTermDebtDynamics.TidyR7ItoSums Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoUnbounded Cochrane.LongTermDebtDynamics.TidyR7ItoProducts
  Cochrane.LongTermDebtDynamics.TidyR7ItoProcess Cochrane.LongTermDebtDynamics.TidyR7ItoCovariation
  Cochrane.LongTermDebtDynamics.TidyR7StieltjesCalculus
  Cochrane.LongTermDebtDynamics.TidyR7BrownianSchauder
  Cochrane.LongTermDebtDynamics.TidyR7BrownianExist
open Cochrane.LongTermDebtDynamics.TidyR7ProductStep (sumRS sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} {X Y a b H K : ℝ → Ω → ℝ} {Ca CH Cb CK : ℝ}

/-! ## Tools -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the product of two bounded admissible integrands is
one (the bracket density `HK`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.itoIntegrand_mul). -/
theorem itoIntegrand_mul {C C' : ℝ} (hH : ItoIntegrand P 𝓕 H s t C)
    (hK : ItoIntegrand P 𝓕 K s t C') : ItoIntegrand P 𝓕 (fun u ω => H u ω * K u ω) s t (C * C')
    where
  adapted u hu := (hH.adapted u hu).mul (hK.adapted u hu)
  bound u hu ω := by
    rw [abs_mul]
    exact mul_le_mul (hH.bound u hu ω) (hK.bound u hu ω) (abs_nonneg _)
      ((abs_nonneg _).trans (hH.bound u hu ω))
  cont := by
    filter_upwards [hH.cont, hK.cont] with ω h1 h2
    exact h1.mul h2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the cross sum of two Itô processes is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.integrable_sumCross). -/
theorem integrable_sumCross (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (p : Partition s t) :
    Integrable (sumCross p X Y) P :=
  (integrable_finsetSum (Finset.range p.n) fun _ hi =>
    ((hX.memLp hB hW h𝓕 hs (t_mem p (Finset.mem_range.1 hi))).sub
      (hX.memLp hB hW h𝓕 hs (t_mem p (Finset.mem_range.1 hi).le))).integrable_mul
    ((hY.memLp hB hW h𝓕 hs (t_mem p (Finset.mem_range.1 hi))).sub
      (hY.memLp hB hW h𝓕 hs (t_mem p (Finset.mem_range.1 hi).le)))).congr
    (ae_of_all _ fun _ => rfl)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `L²` convergence gives `L¹` convergence,
`E|X_k − Y| → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.tendsto_integral_abs_of_L2Tendsto). -/
theorem tendsto_integral_abs_of_L2Tendsto [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ}
    {L : Ω → ℝ} (h : L2Tendsto P Z L) :
    Tendsto (fun k => ∫ ω, |Z k ω - L ω| ∂P) atTop (𝓝 0) :=
  tendsto_zero_of_sq_le (c := 1) (fun k => by
    rw [one_mul]
    exact sq_integral_abs_le ((h.1 k).sub h.2.1)) h.2.2

/-! ## The product rule -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (infrastructure for (1.32) with diffusive bonds):
Itô's product rule.** For Itô processes `X` (drift `a`, diffusion `H`) and `Y` (drift `b`,
diffusion `K`) on `[s, t]`, `0 ≤ s < t`, almost surely
`X_tY_t − X_sY_s = (∫X b du + ∫X K dW) + (∫Y a du + ∫Y H dW) + ∫_s^t H_uK_u du`,
i.e. `X_tY_t − X_sY_s = ∫X dY + ∫Y dX + [X, Y]_s^t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.product_rule). -/
theorem product_rule (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) :
    (fun ω => X t ω * Y t ω - X s ω * Y s ω) =ᵐ[P] fun ω =>
      (dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + itoInt P 𝓕 W (fun u ω => X u ω * K u ω) s t ω)
      + (dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω
        + itoInt P 𝓕 W (fun u ω => Y u ω * H u ω) s t ω)
      + ∫ u in s..t, H u ω * K u ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set ps : ℕ → Partition s t := fun k => dyadic hst k with hps_def
  have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := tendsto_mesh_dyadic hst
  set L1 : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
    + itoInt P 𝓕 W (fun u ω => X u ω * K u ω) s t ω with hL1
  set L2 : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω
    + itoInt P 𝓕 W (fun u ω => Y u ω * H u ω) s t ω with hL2
  set L3 : Ω → ℝ := fun ω => ∫ u in s..t, H u ω * K u ω with hL3
  have h1 : L2Tendsto P (fun k => sumRS (ps k) X Y) L1 :=
    L2Tendsto_sumRS hB hW h𝓕 hs hst (hX.toMS hB hW h𝓕 hs) hY ps hps
  have h2 : L2Tendsto P (fun k => sumRS (ps k) Y X) L2 :=
    L2Tendsto_sumRS hB hW h𝓕 hs hst (hY.toMS hB hW h𝓕 hs) hX ps hps
  have h3 := tendsto_integral_abs_sumCross hB hW h𝓕 hs hst hX hY ps hps
  have mL3 : MemLp L3 2 P :=
    memLp_integral_drift (itoIntegrand_mul hX.diff hY.diff) le_rfl hst.le le_rfl
  have t1 := tendsto_integral_abs_of_L2Tendsto h1
  have t2 := tendsto_integral_abs_of_L2Tendsto h2
  have i1 : ∀ k, Integrable (fun ω => |sumRS (ps k) X Y ω - L1 ω|) P := fun k =>
    (((h1.1 k).sub h1.2.1).integrable one_le_two).abs
  have i2 : ∀ k, Integrable (fun ω => |sumRS (ps k) Y X ω - L2 ω|) P := fun k =>
    (((h2.1 k).sub h2.2.1).integrable one_le_two).abs
  have i3 : ∀ k, Integrable (fun ω => |sumCross (ps k) X Y ω - L3 ω|) P := fun k =>
    ((integrable_sumCross hB hW h𝓕 hs hX hY (ps k)).sub (mL3.integrable one_le_two)).abs
  set D : Ω → ℝ := fun ω => X t ω * Y t ω - X s ω * Y s ω with hD
  have hbound : ∀ k, ∫ ω, |D ω - (L1 ω + L2 ω + L3 ω)| ∂P
      ≤ ∫ ω, |sumRS (ps k) X Y ω - L1 ω| ∂P + ∫ ω, |sumRS (ps k) Y X ω - L2 ω| ∂P
        + ∫ ω, |sumCross (ps k) X Y ω - L3 ω| ∂P := by
    intro k
    have j2 : Integrable (fun ω => |sumRS (ps k) X Y ω - L1 ω|
        + |sumRS (ps k) Y X ω - L2 ω|) P := (i1 k).add (i2 k)
    have j3 : Integrable (fun ω => |sumRS (ps k) X Y ω - L1 ω|
        + |sumRS (ps k) Y X ω - L2 ω| + |sumCross (ps k) X Y ω - L3 ω|) P := j2.add (i3 k)
    rw [← integral_add (i1 k) (i2 k), ← integral_add j2 (i3 k)]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) j3
      (ae_of_all _ fun ω => ?_)
    have hid := prod_partition_identity (ps k) (fun u => X u ω) (fun u => Y u ω)
    have e : D ω - (L1 ω + L2 ω + L3 ω) = (sumRS (ps k) X Y ω - L1 ω)
        + (sumRS (ps k) Y X ω - L2 ω) + (sumCross (ps k) X Y ω - L3 ω) := by
      simp only [hD, sumRS, sumCross]
      rw [hid]
      ring
    change |D ω - (L1 ω + L2 ω + L3 ω)| ≤ _
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hlim := (t1.add t2).add h3
  rw [add_zero, add_zero] at hlim
  have h0 : ∫ ω, |D ω - (L1 ω + L2 ω + L3 ω)| ∂P ≤ 0 := ge_of_tendsto' hlim hbound
  have mD : MemLp (fun ω => D ω - (L1 ω + L2 ω + L3 ω)) 1 P := by
    have mX := fun u (hu : u ∈ Set.Icc s t) => hX.memLp hB hW h𝓕 hs hu
    have mY := fun u (hu : u ∈ Set.Icc s t) => hY.memLp hB hW h𝓕 hs hu
    have hDi : Integrable D P :=
      ((mX t ⟨hst.le, le_rfl⟩).integrable_mul (mY t ⟨hst.le, le_rfl⟩)).sub
        ((mX s ⟨le_rfl, hst.le⟩).integrable_mul (mY s ⟨le_rfl, hst.le⟩))
    have hL1i : Integrable L1 P := (h1.2.1).integrable one_le_two
    have hL2i : Integrable L2 P := (h2.2.1).integrable one_le_two
    exact memLp_one_iff_integrable.2 (hDi.sub ((hL1i.add hL2i).add (mL3.integrable one_le_two)))
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _)
    (memLp_one_iff_integrable.1 mD).abs).1 (le_antisymm h0 (integral_nonneg fun _ => abs_nonneg _))
  filter_upwards [hz] with ω hω
  simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hω
  exact hω

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the product rule with pathwise drift integrals.**
If the paths of `X` and `Y` are a.s. continuous on `[s, t]`, the mean-square time integrals are
the pathwise ones: a.s.
`X_tY_t − X_sY_s = ∫_s^t (X_ub_u + Y_ua_u + H_uK_u) du + ∫X K dW + ∫Y H dW`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.product_rule_pathwise). -/
theorem product_rule_pathwise (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    (hYc : ∀ᵐ ω ∂P, ContinuousOn (fun u => Y u ω) (Set.Icc s t)) :
    (fun ω => X t ω * Y t ω - X s ω * Y s ω) =ᵐ[P] fun ω =>
      (∫ u in s..t, X u ω * b u ω) + itoInt P 𝓕 W (fun u ω => X u ω * K u ω) s t ω
      + ((∫ u in s..t, Y u ω * a u ω) + itoInt P 𝓕 W (fun u ω => Y u ω * H u ω) s t ω)
      + ∫ u in s..t, H u ω * K u ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have e1 := dtInt_ae_eq_integral hst.le (MSIntegrand.mul_itoIntegrand
    (hX.toMS hB hW h𝓕 hs) hY.drift) (by
      filter_upwards [hXc, hY.drift.cont] with ω h1 h2
      exact h1.mul h2)
  have e2 := dtInt_ae_eq_integral hst.le (MSIntegrand.mul_itoIntegrand
    (hY.toMS hB hW h𝓕 hs) hX.drift) (by
      filter_upwards [hYc, hX.drift.cont] with ω h1 h2
      exact h1.mul h2)
  filter_upwards [product_rule hB hW h𝓕 hs hst hX hY, e1, e2] with ω h0 h1 h2
  rw [h0, h1, h2]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the product rule without drifts.** If `a = b = 0`
(`X`, `Y` martingale-type Itô processes), a.s.
`X_tY_t − X_sY_s = ∫X K dW + ∫Y H dW + ∫_s^t H_uK_u du`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.product_rule_noDrift). -/
theorem product_rule_noDrift (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (ha : ∀ u ω, a u ω = 0) (hb : ∀ u ω, b u ω = 0) :
    (fun ω => X t ω * Y t ω - X s ω * Y s ω) =ᵐ[P] fun ω =>
      itoInt P 𝓕 W (fun u ω => X u ω * K u ω) s t ω
      + itoInt P 𝓕 W (fun u ω => Y u ω * H u ω) s t ω + ∫ u in s..t, H u ω * K u ω := by
  have e1 : dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t =ᵐ[P] 0 :=
    dtInt_of_eq_zero fun u _ ω => by simp [hb]
  have e2 : dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t =ᵐ[P] 0 :=
    dtInt_of_eq_zero fun u _ ω => by simp [ha]
  filter_upwards [product_rule hB hW h𝓕 hs hst hX hY, e1, e2] with ω h0 h1 h2
  rw [h0, h1, h2]
  simp only [Pi.zero_apply]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Itô's formula for `x²`.** For an Itô process `X`
(drift `a`, diffusion `H`) on `[s, t]`, a.s.
`X_t² − X_s² = 2(∫X a du + ∫X H dW) + ∫_s^t H_u² du`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.ito_formula_sq). -/
theorem ito_formula_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) :
    (fun ω => X t ω ^ 2 - X s ω ^ 2) =ᵐ[P] fun ω =>
      2 * (dtInt P 𝓕 (fun u ω => X u ω * a u ω) s t ω
        + itoInt P 𝓕 W (fun u ω => X u ω * H u ω) s t ω) + ∫ u in s..t, H u ω ^ 2 := by
  filter_upwards [product_rule hB hW h𝓕 hs hst hX hX] with ω h
  simp only [sq]
  rw [h]
  ring

/-! ## Conditional form -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the form of (1.32) with diffusive bonds):
`E_s[X_tY_t − X_sY_s] = E_s[∫_s^t X b du + ∫_s^t Y a du + ∫_s^t HK du]`** a.s., the
`dW`-integrals having conditional mean `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.condExp_product_rule). -/
theorem condExp_product_rule (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) :
    P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω + ∫ u in s..t, H u ω * K u ω | 𝓕 s] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set F : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
    + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω + ∫ u in s..t, H u ω * K u ω with hF
  set I1 := itoInt P 𝓕 W (fun u ω => X u ω * K u ω) s t with hI1
  set I2 := itoInt P 𝓕 W (fun u ω => Y u ω * H u ω) s t with hI2
  have hG1 := MSIntegrand.mul_itoIntegrand (hX.toMS hB hW h𝓕 hs) hY.diff
  have hG2 := MSIntegrand.mul_itoIntegrand (hY.toMS hB hW h𝓕 hs) hX.diff
  have iI1 : Integrable I1 P := (memLp_itoInt_ms hB hW h𝓕 hs hG1).integrable one_le_two
  have iI2 : Integrable I2 P := (memLp_itoInt_ms hB hW h𝓕 hs hG2).integrable one_le_two
  have iF : Integrable F P :=
    (((memLp_dtInt (MSIntegrand.mul_itoIntegrand (hX.toMS hB hW h𝓕 hs)
      hY.drift)).integrable one_le_two).add ((memLp_dtInt (MSIntegrand.mul_itoIntegrand
        (hY.toMS hB hW h𝓕 hs) hX.drift)).integrable one_le_two)).add
      ((memLp_integral_drift (itoIntegrand_mul hX.diff hY.diff) le_rfl hst.le
        le_rfl).integrable one_le_two)
  have e1 : (fun ω => X t ω * Y t ω - X s ω * Y s ω) =ᵐ[P] F + I1 + I2 := by
    filter_upwards [product_rule hB hW h𝓕 hs hst hX hY] with ω h
    rw [h]
    simp only [hF, hI1, hI2, Pi.add_apply]
    ring
  filter_upwards [condExp_congr_ae (m := 𝓕 s) e1, condExp_add (iF.add iI1) iI2 (𝓕 s),
    condExp_add iF iI1 (𝓕 s), condExp_itoInt_ms hB hW h𝓕 hs hG1,
    condExp_itoInt_ms hB hW h𝓕 hs hG2] with ω h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, Pi.add_apply]
  simp only [hI1, hI2] at h4 h5 ⊢
  rw [h4, h5]
  simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `Z_k → Z` in `L¹` and `E_s[V] = 0`, then
`E_s[Z_k] → E_s[Z − V]` in `L¹` (`|E_s f| ≤ E_s|f|`, Mathlib `integral_abs_condExp_le`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.tendsto_integral_abs_condExp). -/
theorem tendsto_integral_abs_condExp [IsProbabilityMeasure P] {m : MeasurableSpace Ω}
    {Z : ℕ → Ω → ℝ} {L V : Ω → ℝ} (hZ : ∀ k, Integrable (Z k) P) (hL : Integrable L P)
    (hV : Integrable V P) (hV0 : P[V | m] =ᵐ[P] 0)
    (h : Tendsto (fun k => ∫ ω, |Z k ω - (L ω + V ω)| ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |P[Z k | m] ω - P[L | m] ω| ∂P) atTop (𝓝 0) := by
  refine squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) h
  have e : (fun ω => |P[Z k | m] ω - P[L | m] ω|) =ᵐ[P]
      fun ω => |P[fun ω => Z k ω - (L ω + V ω) | m] ω| := by
    have hsub := condExp_sub (m := m) (hZ k) (hL.add hV)
    have hadd := condExp_add (m := m) hL hV
    filter_upwards [hsub, hadd, hV0] with ω h1 h2 h3
    change |P[Z k | m] ω - P[L | m] ω| = |P[Z k - (L + V) | m] ω|
    rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3]
    simp
  rw [integral_congr_ae e]
  exact integral_abs_condExp_le _

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E_s[Σ X_iΔY_i] → E_s[∫_s^t X b du]` in `L¹`**
along any partitions with mesh `→ 0` (the `X dY` term in the expected-increment reading; the
`dW` part has conditional mean `0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.tendsto_condExp_sumRS). -/
theorem tendsto_condExp_sumRS (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hX : MSIntegrand P 𝓕 X s t)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |P[sumRS (ps k) X Y | 𝓕 s] ω
      - P[dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t | 𝓕 s] ω| ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := L2Tendsto_sumRS hB hW h𝓕 hs hst hX hY ps hps
  have hG := MSIntegrand.mul_itoIntegrand hX hY.diff
  exact tendsto_integral_abs_condExp (fun k => (h.1 k).integrable one_le_two)
    ((memLp_dtInt (MSIntegrand.mul_itoIntegrand hX hY.drift)).integrable one_le_two)
    ((memLp_itoInt_ms hB hW h𝓕 hs hG).integrable one_le_two)
    (condExp_itoInt_ms hB hW h𝓕 hs hG) (tendsto_integral_abs_of_L2Tendsto h)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E_s[Σ ΔX_iΔY_i] → E_s[∫_s^t H_uK_u du]` in
`L¹`** along any partitions with mesh `→ 0` (`E_s d[X, Y] = E_s[HK] dt`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.tendsto_condExp_sumCross). -/
theorem tendsto_condExp_sumCross (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |P[sumCross (ps k) X Y | 𝓕 s] ω
      - P[fun ω => ∫ u in s..t, H u ω * K u ω | 𝓕 s] ω| ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := tendsto_integral_abs_sumCross hB hW h𝓕 hs hst hX hY ps hps
  refine tendsto_integral_abs_condExp (V := 0) (fun k => integrable_sumCross hB hW h𝓕 hs hX hY
    (ps k)) ((memLp_integral_drift (itoIntegrand_mul hX.diff hY.diff) le_rfl hst.le
      le_rfl).integrable one_le_two) (integrable_zero _ _ _) (by rw [condExp_zero]) ?_
  simpa using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the expected-increment product rule**
`E_s d(XY) = X E_s dY + Y E_s dX + E_s d[X, Y]`, integrated over `[s, t]`: a.s.
`E_s[X_tY_t − X_sY_s] = E_s[∫X b du + ∫Y a du + ∫HK du]`, and along any partitions with mesh
`→ 0`, in `L¹`, `E_s[Σ X_iΔY_i] → E_s[∫X b du]`, `E_s[Σ Y_iΔX_i] → E_s[∫Y a du]`,
`E_s[Σ ΔX_iΔY_i] → E_s[∫HK du]` (`d[X, Y] = HK dt`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.expected_increment_product_rule). -/
theorem expected_increment_product_rule (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    (P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω + ∫ u in s..t, H u ω * K u ω | 𝓕 s]) ∧
    Tendsto (fun k => ∫ ω, |P[sumRS (ps k) X Y | 𝓕 s] ω
      - P[dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t | 𝓕 s] ω| ∂P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, |P[sumRS (ps k) Y X | 𝓕 s] ω
      - P[dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t | 𝓕 s] ω| ∂P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, |P[sumCross (ps k) X Y | 𝓕 s] ω
      - P[fun ω => ∫ u in s..t, H u ω * K u ω | 𝓕 s] ω| ∂P) atTop (𝓝 0) :=
  ⟨condExp_product_rule hB hW h𝓕 hs hst hX hY,
    tendsto_condExp_sumRS hB hW h𝓕 hs hst (hX.toMS hB hW h𝓕 hs) hY ps hps,
    tendsto_condExp_sumRS hB hW h𝓕 hs hst (hY.toMS hB hW h𝓕 hs) hX ps hps,
    tendsto_condExp_sumCross hB hW h𝓕 hs hst hX hY ps hps⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (when the book's form of (1.32) is right):** the
product rule without a bracket, `E_s[X_tY_t − X_sY_s] = E_s[∫X b du + ∫Y a du]` a.s., holds
**if and only if** `E_s[∫_s^t H_uK_u du] = 0` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.condExp_product_rule_bookForm_iff). -/
theorem condExp_product_rule_bookForm_iff (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) :
    (P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω | 𝓕 s]) ↔
      P[fun ω => ∫ u in s..t, H u ω * K u ω | 𝓕 s] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set F : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
    + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω with hF
  set Q : Ω → ℝ := fun ω => ∫ u in s..t, H u ω * K u ω with hQ
  have iF : Integrable F P :=
    ((memLp_dtInt (MSIntegrand.mul_itoIntegrand (hX.toMS hB hW h𝓕 hs)
      hY.drift)).integrable one_le_two).add ((memLp_dtInt (MSIntegrand.mul_itoIntegrand
        (hY.toMS hB hW h𝓕 hs) hX.drift)).integrable one_le_two)
  have iQ : Integrable Q P := (memLp_integral_drift (itoIntegrand_mul hX.diff hY.diff) le_rfl
    hst.le le_rfl).integrable one_le_two
  have hmain : P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P] P[F | 𝓕 s] + P[Q | 𝓕 s] :=
    (condExp_product_rule hB hW h𝓕 hs hst hX hY).trans (condExp_add iF iQ (𝓕 s))
  constructor
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    rw [h1, Pi.add_apply] at h2
    simp only [Pi.zero_apply]
    linarith
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    rw [h1, Pi.add_apply, h2]
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (link to Track 1's (1.32) step): no bracket when one
factor has bounded variation.** If `H = 0` (`X_u = X_s + ∫_s^u a dr`, continuous of bounded
variation), then `E_s[X_tY_t − X_sY_s] = E_s[∫_s^t X b du] + E_s[∫_s^t Y a du]` a.s. This is the
identity of `TidyR7ProductStep.ProductStepData.product_step`,
`E_s[B_tX_t − B_sX_s] = E_s[∫X dB] + E_s[∫B dA]`,
with `B := X` (so `∫Y dB = ∫Y a du`), its `X := Y`, `A := ∫b du` (so `∫B dA = ∫X b du`) and the
martingale `M := ∫K dW` (TidyR7ItoIntegral) in the martingale slot.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.condExp_product_rule_bv). -/
theorem condExp_product_rule_bv (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (hH0 : ∀ u ω, H u ω = 0) :
    P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t | 𝓕 s]
        + P[dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t | 𝓕 s] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := condExp_product_rule hB hW h𝓕 hs hst hX hY
  simp only [hH0, zero_mul, intervalIntegral.integral_zero, add_zero] at h
  refine h.trans ?_
  exact condExp_add ((memLp_dtInt (MSIntegrand.mul_itoIntegrand (hX.toMS hB hW h𝓕 hs)
      hY.drift)).integrable one_le_two) ((memLp_dtInt (MSIntegrand.mul_itoIntegrand
        (hY.toMS hB hW h𝓕 hs) hX.drift)).integrable one_le_two) (𝓕 s)

/-! ## Brownian motion -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Brownian motion is an Itô process**, drift `0`,
diffusion `1`: `W_u = W_s + ∫_s^u 0 dr + ∫_s^u 1 dW` a.s., `0 ≤ s`.
From `TidyR7ItoIntegral.itoInt_one`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.itoProcess_bm). -/
theorem itoProcess_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) :
    ItoProcess P 𝓕 W (bmReal W) (fun _ _ => 0) (fun _ _ => 1) s t 0 1 where
  adapted u _ := h𝓕.adapted u
  init := (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
  drift := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  diff := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  eq u hu := by
    filter_upwards [itoInt_one hB hW h𝓕 hs hu.1] with ω hω
    rw [hω]
    simp [incr]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Itô's formula for `W²`**,
`W_t² − W_s² = 2∫_s^t W dW + (t − s)` a.s., `0 ≤ s < t`, as the case `X = W` of
`ito_formula_sq`.
Restates `TidyR7ItoBridge.itoInt_bm`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.ito_formula_bm). -/
theorem ito_formula_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    (fun ω => bmReal W t ω ^ 2 - bmReal W s ω ^ 2) =ᵐ[P]
      fun ω => 2 * itoInt P 𝓕 W (bmReal W) s t ω + (t - s) := by
  have h := ito_formula_sq hB hW h𝓕 hs hst (itoProcess_bm (t := t) hB hW h𝓕 hs)
  have e0 : dtInt P 𝓕 (fun u ω => bmReal W u ω * (fun _ _ => (0 : ℝ)) u ω) s t =ᵐ[P] 0 :=
    dtInt_of_eq_zero fun u _ ω => by simp
  have e1 : (fun u ω => bmReal W u ω * (fun _ _ => (1 : ℝ)) u ω) = bmReal W := by
    funext u ω
    simp
  rw [e1] at h
  filter_upwards [h, e0] with ω h1 h2
  rw [h1, h2]
  simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: consistency with `TidyR7ItoBridge.itoInt_bm`.**
The product rule re-derives `∫_s^t W dW = (W_t² − W_s² − (t − s))/2` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.itoInt_bm_of_product_rule). -/
theorem itoInt_bm_of_product_rule (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    itoInt P 𝓕 W (bmReal W) s t =ᵐ[P]
      fun ω => (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - (t - s)) / 2 := by
  filter_upwards [ito_formula_bm hB hW h𝓕 hs hst] with ω h
  rw [h]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the deterministic clock `Y_u = u` is an Itô process
(drift `1`, diffusion `0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.itoProcess_id). -/
theorem itoProcess_id (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) :
    ItoProcess P 𝓕 W (fun u _ => u) (fun _ _ => 1) (fun _ _ => 0) s t 1 0 where
  adapted _ _ := stronglyMeasurable_const
  init := by
    have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    exact memLp_const s
  drift := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  diff := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  eq u hu := by
    filter_upwards [itoInt_const hB hW h𝓕 hs hu.1 (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω hω
    rw [hω]
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the product rule for `u·W_u`** (no bracket, the
clock has bounded variation): `tW_t − sW_s = ∫_s^t W_u du + ∫_s^t u dW_u` a.s., the time integral
in mean square (`TidyR7ItoProducts.dtInt`; pathwise when `W` has a.s. continuous paths), the
Wiener integral `∫u dW` of TidyR7ItoBridge.
Restates `TidyR7ItoBridge.itoInt_deterministic` with `h = id`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.product_rule_bm_id). -/
theorem product_rule_bm_id (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    (fun ω => bmReal W t ω * t - bmReal W s ω * s) =ᵐ[P]
      fun ω => dtInt P 𝓕 (bmReal W) s t ω + itoInt P 𝓕 W (fun u _ => u) s t ω := by
  have h := product_rule hB hW h𝓕 hs hst (itoProcess_bm (t := t) hB hW h𝓕 hs)
    (itoProcess_id (t := t) hB hW h𝓕 hs)
  have e1 : (fun u ω => bmReal W u ω * (fun _ _ => (1 : ℝ)) u ω) = bmReal W := by
    funext u ω
    simp
  have e2 : (fun u ω => (fun u (_ : Ω) => u) u ω * (fun _ _ => (1 : ℝ)) u ω)
      = fun u (_ : Ω) => u := by
    funext u ω
    simp
  have z1 : itoInt P 𝓕 W (fun u ω => bmReal W u ω * (fun _ _ => (0 : ℝ)) u ω) s t =ᵐ[P] 0 := by
    have e3 : (fun u ω => bmReal W u ω * (fun _ _ => (0 : ℝ)) u ω) = fun _ _ => (0 : ℝ) := by
      funext u ω
      simp
    rw [e3]
    filter_upwards [itoInt_const hB hW h𝓕 hs hst.le (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω hω
    rw [hω]
    simp
  have z2 : dtInt P 𝓕 (fun u ω => (fun u (_ : Ω) => u) u ω * (fun _ _ => (0 : ℝ)) u ω) s t
      =ᵐ[P] 0 := dtInt_of_eq_zero fun u _ ω => by simp
  rw [e1, e2] at h
  filter_upwards [h, z1, z2] with ω h0 h1 h2
  rw [h0, h1, h2]
  simp

/-! ## Non-vacuity on the constructed Brownian motion -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): `W_1² = 2∫_0^1 W dW + 1`** a.s. for
the constructed motion `TidyR7BrownianExist.bmPath` and its natural filtration.
Restates `TidyR7ItoBridge.itoInt_bmPath`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.ito_formula_bmPath). -/
theorem ito_formula_bmPath :
    (fun ω => bmPath 1 ω ^ 2) =ᵐ[gaussSeq]
      fun ω => 2 * itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath
        (bmReal bmPath) 0 1 ω + 1 := by
  have h := ito_formula_bm isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl zero_lt_one
  filter_upwards [h] with ω hω
  simp only [bmReal, Real.toNNReal_one, Real.toNNReal_zero, bmPath_zero] at hω
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity, both sides computed):** for the
constructed motion, `E[W_1² − W_0²] = 1`, `E[2∫_0^1 W dW] = 0` and `E[∫_0^1 1·1 du] = 1`: the
expected increment of `W²` is entirely the bracket `[W, W]_0^1 = 1`.
Its `E[2∫W dW] = 0` is `TidyR7ItoUnbounded.integral_mul_itoInt_ms`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.integral_ito_formula_bmPath). -/
theorem integral_ito_formula_bmPath :
    ∫ ω, (bmPath 1 ω ^ 2 - bmPath 0 ω ^ 2) ∂gaussSeq = 1 ∧
      ∫ ω, 2 * itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath
        (bmReal bmPath) 0 1 ω ∂gaussSeq = 0 ∧
      ∫ _ω, (∫ _u in (0 : ℝ)..1, (1 : ℝ) * 1) ∂gaussSeq = 1 := by
  have : IsProbabilityMeasure gaussSeq :=
    isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  refine ⟨?_, ?_, by simp⟩
  · have h := integral_incr_sq (W := bmPath) isPreBrownianReal_bmPath le_rfl zero_le_one
    simpa [incr, bmReal, bmPath_zero] using h
  · rw [integral_const_mul]
    have h0 : ∫ ω, itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath
        (bmReal bmPath) 0 1 ω ∂gaussSeq = 0 := by
      rw [integral_congr_ae (TidyR7ItoBridge.itoInt_bmPath)]
      have h := integral_incr_sq (W := bmPath) isPreBrownianReal_bmPath le_rfl zero_le_one
      simp only [incr, bmReal, Real.toNNReal_one, Real.toNNReal_zero, bmPath_zero,
        sub_zero] at h
      have i2 : Integrable (fun ω => bmPath 1 ω ^ 2) gaussSeq :=
        (integrable_incr_sq (W := bmPath) isPreBrownianReal_bmPath 0 1).congr
          (ae_of_all _ fun ω => by simp [incr, bmReal, bmPath_zero])
      rw [integral_div, integral_sub i2 (integrable_const _), h]
      simp
    rw [h0, mul_zero]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the book's form of (1.32) fails for diffusive
factors): for `X = Y = W` on the constructed motion**, `E_0[W_1² − W_0²]` is NOT a.s. equal to
`E_0[∫_0^1 W·0 du + ∫_0^1 W·0 du]` (both drifts vanish): the bracket `E_0[∫_0^1 1 du] = 1 ≠ 0`
(`condExp_product_rule_bookForm_iff`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProductRule.not_bookForm_bmPath). -/
theorem not_bookForm_bmPath :
    ¬ (gaussSeq[fun ω => bmReal bmPath 1 ω * bmReal bmPath 1 ω
        - bmReal bmPath 0 ω * bmReal bmPath 0 ω | bmFiltrationReal bmPath measurable_bmPath 0]
      =ᵐ[gaussSeq] gaussSeq[fun ω => dtInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
          (fun u ω => bmReal bmPath u ω * (fun _ _ => (0 : ℝ)) u ω) 0 1 ω
        + dtInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
          (fun u ω => bmReal bmPath u ω * (fun _ _ => (0 : ℝ)) u ω) 0 1 ω
          | bmFiltrationReal bmPath measurable_bmPath 0]) := by
  have : IsProbabilityMeasure gaussSeq :=
    isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  intro h
  have hW := itoProcess_bm (t := 1) isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
  have hiff := (condExp_product_rule_bookForm_iff isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl zero_lt_one hW
    hW).1 h
  have e : (fun _ : ℕ → ℝ => ∫ _u in (0 : ℝ)..1, (1 : ℝ) * 1) = fun _ => (1 : ℝ) := by
    funext ω
    simp
  beta_reduce at hiff
  rw [e, condExp_const ((bmFiltrationReal bmPath measurable_bmPath).le 0)] at hiff
  obtain ⟨ω, hω⟩ := hiff.exists
  simp at hω

end Cochrane.LongTermDebtDynamics.TidyR7ItoProductRule
