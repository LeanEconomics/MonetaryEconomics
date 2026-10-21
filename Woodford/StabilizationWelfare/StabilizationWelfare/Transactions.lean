/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Moments
import StabilizationWelfare.Expectations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Transactions frictions and the welfare loss (Woodford 2003, §6.4.1, App. E.4)

Woodford (2003), *Interest and Prices*, Chapter 6, §4.1 "Transactions Frictions",
pp. 420–426, with the proof of Proposition 6.7 in Appendix E.4, pp. 698–700.

## Main results

* `Assumption61`: satiation in real balances at a finite level `m̄` with one-sided limits of
  the second derivatives and `u_mm(m̄−) < 0` (Assumption 6.1, p. 422);
  `Assumption61.um_left_taylor` (one-sided Taylor expansion of `u_m` at `m̄`),
  `Assumption61.not_differentiableAt` (`u_m` has a kink at `m̄`, so `u_mm` is discontinuous),
  `Assumption61.semiElasticity_tendsto` (the money-demand semi-elasticity tends to
  `η_i = −u_c/(m̄ u_mm(m̄−))` as the interest differential tends to zero);
  `Assumption61.moneyDemand_local` (existence and local uniqueness of money demand for small
  `Δ > 0`, by a one-sided IVT and the mean value theorem), `Assumption61.semiElasticity_of_foc`
  (the family exists and has the limiting semi-elasticity), `cexA_two_solutions` (uniqueness is
  only local under the printed assumption).
* `smSig_eq`, `chi_etaI_vbar_eq`: the exact preference-ratio identities behind (E.16) and the
  substitutions of p. 700.
* `sm_consistent`, `sm_p421`, `sm_p421_ne`: the normalisation of `s_m` (survey error 20): the
  appendix needs `s_m = m̄u_m/(Ȳu_c) = Δ̄/v̄`; the p. 421 / p. 423 normalisation
  `m̄u_m/(c̄u_c) = Δ̄/(s_C v̄)` agrees only when `s_C = 1`.
* `E15_to_E17`, `E17_to_E18`, `E3_to_E4`, `E18_minus_E4`, `prop_6_7_layerA`: Proposition 6.7
  (4.9) as an exact identity (E.15)–(E.18); `remainder_scale`, `remainder_isBigO`: the
  remainder has weighted degree `≥ 3`; `alt_sm_discrepancy`, `alt_sm_not_isBigO`: with the
  p. 421 normalisation the error is a policy-dependent second-order term.
* `eq_4_2`, `calvo_AS_4_8`, `newClassical_AS_4_7`: real marginal cost and the AS relations.
* `prop_6_8`: Proposition 6.8, (4.10)–(4.11), as an identity between discounted sums;
  `lambdaI_eq_4_12` and `lambdaI_4_12_chi_zero` for (4.12) (`χ ≠ 0` is needed).
* `i* = log(1 − Δ̄) = −Δ̄ + O(Δ̄²)` is `ExpLogCES.istar_ratio`, `ExpLogCES.istar_expansion`,
  `ExpLogCES.abs_log_one_sub_add_le`.
* `loss_4_13_identity`, `eq_4_16`, `xStar_eq_4_15`, `AS_4_15`: (4.13)–(4.16).
* `loss_4_17_period`, `loss_4_17`: the corrected (4.17) as a discounted-sum identity;
  `printed_4_17_ne` (survey error 21: the term `−κ_i î₀` is spurious);
  `bracket_4_17_nonneg`, `bracket_4_17_eq_zero`.
* Table 6.1/6.2 arithmetic: `vi_sq`, `vi_rounding`, `table62_rows`, `table62_row5_printed`.
-/

namespace Woodford.StabilizationWelfare.Transactions

open Filter Topology Asymptotics
open ExpLogCES (abs_log_one_sub_add_le)
open Moments (calvoK)

/-! ### Assumption 6.1: satiation in real money balances -/

/-- Woodford (2003), Assumption 6.1, p. 422: satiation in real balances at the finite level
`m̄ > 0` (for output `Ȳ`); the second partial derivatives have finite limits as `m → m̄` from
below, and the limit of `u_mm` from below is negative. `um m` is `u_m(Ȳ, m)`. -/
structure Assumption61 where
  /-- The satiation level of real balances `m̄`. -/
  mbar : ℝ
  /-- `u_m(Ȳ, m)` as a function of `m`. -/
  um : ℝ → ℝ
  /-- `u_mm(Ȳ, m)` for `m < m̄`. -/
  umm : ℝ → ℝ
  /-- The left limit `u_mm(m̄−)`. -/
  ummL : ℝ
  /-- `u_cm(Ȳ, m)` for `m < m̄`. -/
  ucm : ℝ → ℝ
  /-- The left limit `u_cm(m̄−)`. -/
  ucmL : ℝ
  /-- The marginal utility of expenditure at satiation. -/
  uc : ℝ
  /-- `m̄ > 0`. -/
  mbar_pos : 0 < mbar
  /-- `u_c > 0`. -/
  uc_pos : 0 < uc
  /-- Below satiation, money has positive marginal utility. -/
  um_pos : ∀ m, m < mbar → 0 < um m
  /-- At and above satiation, `u_m = 0`. -/
  um_sat : ∀ m, mbar ≤ m → um m = 0
  /-- `u_m` is continuous at `m̄` from below. -/
  um_cont : ContinuousWithinAt um (Set.Iic mbar) mbar
  /-- `u_mm` is the derivative of `u_m` below satiation. -/
  hasDerivAt_um : ∀ m, m < mbar → HasDerivAt um (umm m) m
  /-- The finite left limit of `u_mm`. -/
  umm_tendsto : Tendsto umm (𝓝[<] mbar) (𝓝 ummL)
  /-- The finite left limit of `u_cm`. -/
  ucm_tendsto : Tendsto ucm (𝓝[<] mbar) (𝓝 ucmL)
  /-- `u_mm(m̄−) < 0`. -/
  ummL_neg : ummL < 0

namespace Assumption61

variable (A : Assumption61)

/-- Woodford (2003), Assumption 6.1, p. 422: `u_m(m̄) = 0` at the satiation level. -/
theorem um_mbar : A.um A.mbar = 0 := A.um_sat _ le_rfl

/-- Woodford (2003), Assumption 6.1 and (E.15), p. 699: the one-sided Taylor expansion
`u_m(m) = u_mm(m̄−)(m − m̄) + o(m − m̄)` as `m → m̄` from below. -/
theorem um_left_taylor :
    (fun m => A.um m - A.ummL * (m - A.mbar)) =o[𝓝[<] A.mbar] (fun m => m - A.mbar) := by
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhdsWithin_nhds.mp A.umm_tendsto c hc
  filter_upwards [Ioo_mem_nhdsLT (show A.mbar - δ < A.mbar by linarith)] with m hm
  obtain ⟨hm1, hm2⟩ := hm
  have hcont : ContinuousOn A.um (Set.Icc m A.mbar) := by
    intro y hy
    rcases eq_or_lt_of_le hy.2 with h | h
    · rw [h]
      exact A.um_cont.mono (fun z hz => hz.2)
    · exact (A.hasDerivAt_um y h).continuousAt.continuousWithinAt
  obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope A.um A.umm hm2 hcont
    (fun y hy => A.hasDerivAt_um y hy.2)
  rw [A.um_mbar] at hζeq
  have hne : A.mbar - m ≠ 0 := by linarith
  have hum : A.um m = A.umm ζ * (m - A.mbar) := by
    rw [hζeq]; field_simp; ring
  have hdist : dist (A.umm ζ) A.ummL < c := hball hζ.2 (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hζ.1, hζ.2])
  rw [Real.dist_eq] at hdist
  rw [hum, Real.norm_eq_abs, Real.norm_eq_abs, ← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right hdist.le (abs_nonneg _)

/-- Woodford (2003), Assumption 6.1, p. 422: the left derivative of `u_m` at `m̄` is
`u_mm(m̄−)`. -/
theorem hasDerivWithinAt_left : HasDerivWithinAt A.um A.ummL (Set.Iic A.mbar) A.mbar := by
  rw [← hasDerivWithinAt_Iio_iff_Iic, hasDerivWithinAt_iff_isLittleO]
  refine A.um_left_taylor.congr_left (fun m => ?_)
  rw [A.um_mbar, smul_eq_mul]; ring

/-- Woodford (2003), p. 422: above satiation `u_m` is locally constant, so its derivative is
zero there. -/
theorem hasDerivAt_right {m : ℝ} (hm : A.mbar < m) : HasDerivAt A.um 0 m := by
  refine (hasDerivAt_const m (0 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hm] with y hy
  exact A.um_sat y (le_of_lt hy)

/-- Woodford (2003), p. 422: the right derivative of `u_m` at `m̄` is zero. -/
theorem hasDerivWithinAt_right : HasDerivWithinAt A.um 0 (Set.Ici A.mbar) A.mbar :=
  (hasDerivWithinAt_const A.mbar (Set.Ici A.mbar) (0 : ℝ)).congr
    (fun y hy => A.um_sat y hy) A.um_mbar

/-- Woodford (2003), p. 422: "`u_mm` must be discontinuous at the satiation point": `u_m` is
not differentiable at `m̄` (left derivative `u_mm(m̄−) < 0`, right derivative `0`). -/
theorem not_differentiableAt : ¬ DifferentiableAt ℝ A.um A.mbar := by
  intro h
  have h1 := (uniqueDiffWithinAt_Iic A.mbar).eq_deriv _
    h.hasDerivAt.hasDerivWithinAt A.hasDerivWithinAt_left
  have h2 := (uniqueDiffWithinAt_Ici A.mbar).eq_deriv _
    h.hasDerivAt.hasDerivWithinAt A.hasDerivWithinAt_right
  have := A.ummL_neg
  linarith

/-- Woodford (2003), p. 422: the limiting interest semi-elasticity of money demand,
`η_i = −u_c/(m̄ u_mm)`. -/
noncomputable def etaI : ℝ := -A.uc / (A.mbar * A.ummL)

/-- Woodford (2003), p. 422: `η_i > 0`. -/
theorem etaI_pos : 0 < A.etaI := by
  unfold etaI
  have h : A.mbar * A.ummL < 0 := mul_neg_of_pos_of_neg A.mbar_pos A.ummL_neg
  exact div_pos_of_neg_of_neg (by linarith [A.uc_pos]) h

/-- Woodford (2003), p. 422 ("a well-defined (finite) interest-rate semielasticity of money
demand ... as one approaches satiation"): if real balances `m(Δ) < m̄` solve the first-order
condition `u_m(m) = Δ · w(Δ)` for small `Δ > 0` (interest differential `Δ`, marginal utility of
expenditure `w(Δ) → u_c`) and `m(Δ) → m̄` from below as `Δ → 0⁺`, then
`(m(Δ) − m̄)/(m̄ Δ) → −η_i`. The family itself is constructed in `moneyDemand_local` and
`semiElasticity_of_foc`. -/
theorem semiElasticity_tendsto {mΔ w : ℝ → ℝ}
    (hm : Tendsto mΔ (𝓝[>] 0) (𝓝[<] A.mbar))
    (hw : Tendsto w (𝓝[>] 0) (𝓝 A.uc))
    (hfoc : ∀ᶠ Δ in 𝓝[>] 0, A.um (mΔ Δ) = Δ * w Δ) :
    Tendsto (fun Δ => (mΔ Δ - A.mbar) / (A.mbar * Δ)) (𝓝[>] 0) (𝓝 (-A.etaI)) := by
  -- the error ratio `ε(m) = (u_m(m) − u_mm⁻ (m − m̄))/(m − m̄)` tends to zero
  have hε : Tendsto (fun m => (A.um m - A.ummL * (m - A.mbar)) / (m - A.mbar))
      (𝓝[<] A.mbar) (𝓝 0) := A.um_left_taylor.tendsto_div_nhds_zero
  have hε' := hε.comp hm
  have hlt : ∀ᶠ Δ in 𝓝[>] 0, mΔ Δ < A.mbar := hm self_mem_nhdsWithin
  have hpos : ∀ᶠ Δ in 𝓝[>] (0 : ℝ), 0 < Δ := self_mem_nhdsWithin
  -- denominator `u_mm⁻ + ε` tends to `u_mm⁻ ≠ 0`
  have hden : Tendsto (fun Δ => A.ummL + (A.um (mΔ Δ) - A.ummL * (mΔ Δ - A.mbar)) /
      (mΔ Δ - A.mbar)) (𝓝[>] 0) (𝓝 (A.ummL + 0)) := tendsto_const_nhds.add hε'
  rw [add_zero] at hden
  have hlim : Tendsto (fun Δ => w Δ / (A.ummL + (A.um (mΔ Δ) - A.ummL * (mΔ Δ - A.mbar)) /
      (mΔ Δ - A.mbar)) / A.mbar) (𝓝[>] 0) (𝓝 (A.uc / A.ummL / A.mbar)) :=
    (hw.div hden A.ummL_neg.ne).div_const _
  have hval : A.uc / A.ummL / A.mbar = -A.etaI := by
    unfold etaI
    have := A.mbar_pos.ne'
    have := A.ummL_neg.ne
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hlt, hpos, hfoc] with Δ h1 h2 hfo
  have hne : mΔ Δ - A.mbar ≠ 0 := by linarith
  have hden_eq : A.ummL + (A.um (mΔ Δ) - A.ummL * (mΔ Δ - A.mbar)) / (mΔ Δ - A.mbar) =
      Δ * w Δ / (mΔ Δ - A.mbar) := by
    rw [hfo]; field_simp; ring
  rw [hden_eq]
  have := A.mbar_pos.ne'
  have hΔ := h2.ne'
  by_cases hw0 : w Δ = 0
  · -- then `u_m(m(Δ)) = 0` contradicts `m(Δ) < m̄`
    have := A.um_pos _ h1
    rw [hfo, hw0, mul_zero] at this
    exact absurd this (lt_irrefl 0)
  · field_simp

/-- Woodford (2003), Assumption 6.1, p. 422: existence and LOCAL uniqueness of money demand near
satiation. Let `ucf m = u_c(Ȳ, m)`, differentiable below `m̄` with derivative `ucfm` (`= u_cm`)
having a finite left limit, and continuous at `m̄` from the left with `ucf m̄ = u_c`: this is the
regularity Assumption 6.1 presumes ("all first and second partial derivatives ... have finite
limiting values"), stated explicitly because the structure `Assumption61` does not tie `u_cm` to
a function `u_c`. Then there are `l < m̄` and `δ > 0` such that for every `Δ ∈ (0, δ)` the
first-order condition `u_m(m) = Δ u_c(m)` has exactly one solution in `(l, m̄)`, and every such
solution satisfies `m̄ − m ≤ 3u_c/(−u_mm(m̄−)) · Δ`. (Uniqueness is only local:
`cexA_two_solutions`.) -/
theorem moneyDemand_local {ucf ucfm : ℝ → ℝ} {L : ℝ}
    (hucf : ∀ m, m < A.mbar → HasDerivAt ucf (ucfm m) m)
    (hcont : ContinuousWithinAt ucf (Set.Iic A.mbar) A.mbar) (hval : ucf A.mbar = A.uc)
    (hlim : Tendsto ucfm (𝓝[<] A.mbar) (𝓝 L)) :
    ∃ l < A.mbar, ∃ δ > 0, ∀ Δ ∈ Set.Ioo 0 δ,
      (∃! m, m ∈ Set.Ioo l A.mbar ∧ A.um m = Δ * ucf m) ∧
      ∀ m ∈ Set.Ioo l A.mbar, A.um m = Δ * ucf m →
        A.mbar - m ≤ 3 * A.uc / (-A.ummL) * Δ := by
  have hL := A.ummL_neg
  have huc := A.uc_pos
  set B := |L| + 1 with hB
  have hBpos : 0 < B := by positivity
  have e1 : ∀ᶠ m in 𝓝[<] A.mbar, A.umm m < A.ummL / 2 :=
    A.umm_tendsto (Iio_mem_nhds (by linarith))
  have e2 : ∀ᶠ m in 𝓝[<] A.mbar, |ucfm m| < B := by
    have : ∀ᶠ m in 𝓝[<] A.mbar, ucfm m ∈ Set.Ioo (L - 1) (L + 1) :=
      hlim (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [this] with m hm
    rw [abs_lt]
    constructor <;> linarith [hm.1, hm.2, le_abs_self L, neg_abs_le L]
  have e3 : ∀ᶠ m in 𝓝[<] A.mbar, ucf m ∈ Set.Ioo (A.uc / 2) (3 * A.uc / 2) := by
    have ht := hcont.tendsto
    rw [hval] at ht
    exact (ht.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self))
      (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (e1.and (e2.and e3))
  have hl' : l < A.mbar := hl
  have hwin : ∀ m ∈ Set.Ioo l A.mbar, A.umm m < A.ummL / 2 ∧ |ucfm m| < B ∧
      ucf m ∈ Set.Ioo (A.uc / 2) (3 * A.uc / 2) := fun m hm => hsub hm
  set m0 := (l + A.mbar) / 2 with hm0def
  have hm0 : m0 ∈ Set.Ioo l A.mbar := ⟨by linarith, by linarith⟩
  have hum0 : 0 < A.um m0 := A.um_pos m0 hm0.2
  set δ := min ((-A.ummL) / (4 * B)) (A.um m0 / (2 * A.uc)) with hδdef
  have hδ : 0 < δ := lt_min (div_pos (by linarith) (by positivity)) (by positivity)
  -- continuity and derivatives
  have humc : ∀ a, ContinuousOn A.um (Set.Icc a A.mbar) := by
    intro a y hy
    rcases eq_or_lt_of_le hy.2 with h | h
    · rw [h]; exact A.um_cont.mono (fun z hz => hz.2)
    · exact (A.hasDerivAt_um y h).continuousAt.continuousWithinAt
  have hgc : ∀ a Δ, ContinuousOn (fun m => A.um m - Δ * ucf m) (Set.Icc a A.mbar) := by
    intro a Δ y hy
    rcases eq_or_lt_of_le hy.2 with h | h
    · rw [h]
      exact (A.um_cont.mono (fun z hz => hz.2)).sub
        (continuousWithinAt_const.mul (hcont.mono (fun z hz => hz.2)))
    · exact ((A.hasDerivAt_um y h).continuousAt.sub
        (continuousAt_const.mul (hucf y h).continuousAt)).continuousWithinAt
  have hgd : ∀ Δ m, m < A.mbar → HasDerivAt (fun m => A.um m - Δ * ucf m)
      (A.umm m - Δ * ucfm m) m := fun Δ m h =>
    HasDerivAt.sub (A.hasDerivAt_um m h) (HasDerivAt.const_mul Δ (hucf m h))
  refine ⟨l, hl', δ, hδ, ?_⟩
  intro Δ hΔ
  have hΔ0 : 0 < Δ := hΔ.1
  have hΔB : Δ * (4 * B) < -A.ummL :=
    (lt_div_iff₀ (by positivity)).mp (lt_of_lt_of_le hΔ.2 (min_le_left _ _))
  have hΔu : Δ * (2 * A.uc) < A.um m0 :=
    (lt_div_iff₀ (by positivity)).mp (lt_of_lt_of_le hΔ.2 (min_le_right _ _))
  -- the derivative of `g = u_m − Δ u_c` is negative on the window
  have hneg : ∀ m ∈ Set.Ioo l A.mbar, A.umm m - Δ * ucfm m < 0 := by
    intro m hm
    obtain ⟨h1, h2, -⟩ := hwin m hm
    have : -(Δ * ucfm m) ≤ Δ * B := by
      have := mul_le_mul_of_nonneg_left (le_trans (neg_abs_le (ucfm m)) le_rfl) hΔ0.le
      nlinarith [neg_abs_le (ucfm m), abs_nonneg (ucfm m)]
    nlinarith
  -- `u_m(m) ≥ (−u_mm⁻/2)(m̄ − m)` on the window
  have hlow : ∀ m ∈ Set.Ioo l A.mbar, -A.ummL / 2 * (A.mbar - m) < A.um m := by
    intro m hm
    obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope A.um A.umm hm.2 (humc m)
      (fun y hy => A.hasDerivAt_um y hy.2)
    rw [A.um_mbar] at hζeq
    have hζw : ζ ∈ Set.Ioo l A.mbar := ⟨by linarith [hm.1, hζ.1], hζ.2⟩
    have h1 := (hwin ζ hζw).1
    have hpos : 0 < A.mbar - m := by linarith [hm.2]
    have : A.um m = -A.umm ζ * (A.mbar - m) := by
      rw [hζeq]; field_simp; ring
    rw [this]
    nlinarith
  refine ⟨?_, fun m hm hfoc => ?_⟩
  · -- existence by the intermediate value theorem on `[m₀, m̄]`
    have hgm0 : 0 < A.um m0 - Δ * ucf m0 := by
      have hu := (hwin m0 hm0).2.2.2
      have : Δ * ucf m0 < Δ * (3 * A.uc / 2) := mul_lt_mul_of_pos_left hu hΔ0
      nlinarith
    have hgb : A.um A.mbar - Δ * ucf A.mbar < 0 := by
      rw [A.um_mbar, hval]; nlinarith
    obtain ⟨m, hm, hgm⟩ := intermediate_value_Ioo' hm0.2.le (hgc m0 Δ) ⟨hgb, hgm0⟩
    have hmw : m ∈ Set.Ioo l A.mbar := ⟨by linarith [hm.1, hm0.1], hm.2⟩
    refine ⟨m, ⟨hmw, by simp only at hgm; linarith⟩, ?_⟩
    -- uniqueness by the mean value theorem
    rintro m' ⟨hm', hfoc'⟩
    have hz : ∀ x ∈ Set.Ioo l A.mbar, ∀ y ∈ Set.Ioo l A.mbar, x < y →
        A.um x = Δ * ucf x → A.um y = Δ * ucf y → False := by
      intro x hx y hy hxy hfx hfy
      obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope (fun m => A.um m - Δ * ucf m)
        (fun m => A.umm m - Δ * ucfm m) hxy
        ((hgc x Δ).mono (Set.Icc_subset_Icc_right hy.2.le))
        (fun z hz => hgd Δ z (by linarith [hz.2, hy.2]))
      have hzero : A.umm ζ - Δ * ucfm ζ = 0 := by
        rw [hζeq]; simp only [hfx, hfy, sub_self, zero_div]
      have := hneg ζ ⟨by linarith [hx.1, hζ.1], by linarith [hζ.2, hy.2]⟩
      linarith
    have hfm : A.um m = Δ * ucf m := by simp only at hgm; linarith
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hz m' hm' m hmw h hfoc' hfm
    · exact hz m hmw m' hm' h hfm hfoc'
  · -- the bound `m̄ − m ≤ 3u_c Δ/(−u_mm⁻)`
    have h1 := hlow m hm
    have hu := (hwin m hm).2.2.2
    have : Δ * ucf m < Δ * (3 * A.uc / 2) := mul_lt_mul_of_pos_left hu hΔ0
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

/-- Woodford (2003), p. 422: the money-demand family near satiation EXISTS (so
`semiElasticity_tendsto` needs no assumed family): under the hypotheses of `moneyDemand_local`
there is `m(Δ)` with `m(Δ) < m̄` and `u_m(m(Δ)) = Δ u_c(m(Δ))` for all small `Δ > 0`,
`m(Δ) → m̄⁻`, and `(m(Δ) − m̄)/(m̄Δ) → −η_i`. -/
theorem semiElasticity_of_foc {ucf ucfm : ℝ → ℝ} {L : ℝ}
    (hucf : ∀ m, m < A.mbar → HasDerivAt ucf (ucfm m) m)
    (hcont : ContinuousWithinAt ucf (Set.Iic A.mbar) A.mbar) (hval : ucf A.mbar = A.uc)
    (hlim : Tendsto ucfm (𝓝[<] A.mbar) (𝓝 L)) :
    ∃ mΔ : ℝ → ℝ, (∀ᶠ Δ in 𝓝[>] 0, mΔ Δ < A.mbar ∧ A.um (mΔ Δ) = Δ * ucf (mΔ Δ)) ∧
      Tendsto mΔ (𝓝[>] 0) (𝓝[<] A.mbar) ∧
      Tendsto (fun Δ => (mΔ Δ - A.mbar) / (A.mbar * Δ)) (𝓝[>] 0) (𝓝 (-A.etaI)) := by
  obtain ⟨l, -, δ, hδ, h⟩ := A.moneyDemand_local hucf hcont hval hlim
  have hch : ∀ Δ : ℝ, ∃ m : ℝ, Δ ∈ Set.Ioo 0 δ →
      (m ∈ Set.Ioo l A.mbar ∧ A.um m = Δ * ucf m) := by
    intro Δ
    by_cases hΔ : Δ ∈ Set.Ioo 0 δ
    · obtain ⟨m, hm, -⟩ := (h Δ hΔ).1
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h' => absurd h' hΔ⟩
  choose mΔ hmΔ using hch
  have hev : ∀ᶠ Δ in 𝓝[>] (0 : ℝ), Δ ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδ
  have hfam : ∀ᶠ Δ in 𝓝[>] 0, mΔ Δ < A.mbar ∧ A.um (mΔ Δ) = Δ * ucf (mΔ Δ) := by
    filter_upwards [hev] with Δ hΔ
    exact ⟨(hmΔ Δ hΔ).1.2, (hmΔ Δ hΔ).2⟩
  have hm : Tendsto mΔ (𝓝[>] 0) (𝓝[<] A.mbar) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hfam.mono fun Δ hΔ => hΔ.1⟩
    rw [← tendsto_sub_nhds_zero_iff]
    have hC : Tendsto (fun Δ : ℝ => 3 * A.uc / (-A.ummL) * Δ) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun Δ : ℝ => 3 * A.uc / (-A.ummL) * Δ) (𝓝 0)
          (𝓝 (3 * A.uc / (-A.ummL) * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [hev] with Δ hΔ
    have hb := (h Δ hΔ).2 (mΔ Δ) (hmΔ Δ hΔ).1 (hmΔ Δ hΔ).2
    rw [Real.norm_eq_abs, abs_of_neg (by linarith [(hmΔ Δ hΔ).1.2])]
    linarith
  refine ⟨mΔ, hfam, hm, ?_⟩
  have hw : Tendsto (fun Δ => ucf (mΔ Δ)) (𝓝[>] 0) (𝓝 A.uc) := by
    have ht := hcont.tendsto
    rw [hval] at ht
    exact ht.comp (hm.mono_right (nhdsWithin_mono _ Set.Iio_subset_Iic_self))
  exact A.semiElasticity_tendsto hm hw (hfam.mono fun Δ hΔ => hΔ.2)

end Assumption61

/-- Woodford (2003), Assumption 6.1 (counterexample to GLOBAL uniqueness of money demand):
`m̄ = 2`, `u_m(m) = max((2 − m)/(1 + m²), 0)`, `u_c ≡ 1`. Every clause of Assumption 6.1 holds
(`u_mm(2−) = −1/5 < 0`), yet `u_m → 0` as `m → −∞`. -/
noncomputable def cexA : Assumption61 where
  mbar := 2
  um := fun m => max ((2 - m) / (1 + m ^ 2)) 0
  umm := fun m => (-(1 + m ^ 2) - (2 - m) * (2 * m)) / (1 + m ^ 2) ^ 2
  ummL := -1 / 5
  ucm := fun _ => 0
  ucmL := 0
  uc := 1
  mbar_pos := by norm_num
  uc_pos := by norm_num
  um_pos := fun m hm => lt_max_of_lt_left (div_pos (by linarith) (by positivity))
  um_sat := fun m hm => max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  um_cont := (Continuous.max (Continuous.div (by fun_prop) (by fun_prop)
    (fun x => by positivity)) continuous_const).continuousWithinAt
  hasDerivAt_um := fun m hm => by
    have h1 : HasDerivAt (fun m : ℝ => 2 - m) (-1) m := by
      simpa using HasDerivAt.const_sub 2 (hasDerivAt_id m)
    have h2 : HasDerivAt (fun m : ℝ => 1 + m ^ 2) (2 * m) m := by
      simpa using HasDerivAt.const_add 1 (hasDerivAt_pow 2 m)
    have hd : HasDerivAt (fun m : ℝ => (2 - m) / (1 + m ^ 2))
        ((-(1 + m ^ 2) - (2 - m) * (2 * m)) / (1 + m ^ 2) ^ 2) m := by
      convert HasDerivAt.div h1 h2 (by positivity) using 1
      ring
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hm] with y hy
    exact max_eq_left (div_pos (by linarith [Set.mem_Iio.mp hy]) (by positivity)).le
  umm_tendsto := by
    have hc : Continuous (fun m : ℝ => (-(1 + m ^ 2) - (2 - m) * (2 * m)) / (1 + m ^ 2) ^ 2) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
    have := (hc.tendsto 2).mono_left (nhdsWithin_le_nhds (s := Set.Iio 2))
    convert this using 2
    norm_num
  ucm_tendsto := tendsto_const_nhds
  ummL_neg := by norm_num

/-- Woodford (2003), Assumption 6.1 (correction): the printed assumption gives only LOCAL
uniqueness of money demand near satiation (`Assumption61.moneyDemand_local`). In `cexA`, for
every `Δ ∈ (0, 1)` the condition `u_m(m) = Δ u_c` has two solutions below `m̄`, one of them
negative (far from satiation). Global uniqueness needs `u_m` strictly decreasing on all of
`(−∞, m̄)` (e.g. `u_mm < 0` throughout). -/
theorem cexA_two_solutions {Δ : ℝ} (hΔ : Δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ m1 m2 : ℝ, m1 < 0 ∧ m1 < m2 ∧ m2 < cexA.mbar ∧ cexA.um m1 = Δ * cexA.uc ∧
      cexA.um m2 = Δ * cexA.uc := by
  obtain ⟨h0, h1⟩ := hΔ
  have hD : 0 < 1 + 8 * Δ - 4 * Δ ^ 2 := by nlinarith
  set s := Real.sqrt (1 + 8 * Δ - 4 * Δ ^ 2) with hs
  have hs2 : s ^ 2 = 1 + 8 * Δ - 4 * Δ ^ 2 := Real.sq_sqrt hD.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 1 < s := by nlinarith
  have key : ∀ m : ℝ, Δ * m ^ 2 + m + Δ - 2 = 0 → cexA.um m = Δ * cexA.uc := by
    intro m hm
    change max ((2 - m) / (1 + m ^ 2)) 0 = Δ * 1
    rw [show (2 - m) / (1 + m ^ 2) = Δ by
      rw [div_eq_iff (by positivity)]; linarith]
    simp [h0.le]
  have hroot : ∀ σ : ℝ, σ ^ 2 = s ^ 2 →
      Δ * ((-1 + σ) / (2 * Δ)) ^ 2 + (-1 + σ) / (2 * Δ) + Δ - 2 = 0 := by
    intro σ hσ
    have : Δ * ((-1 + σ) / (2 * Δ)) ^ 2 + (-1 + σ) / (2 * Δ) + Δ - 2 =
        (σ ^ 2 - (1 + 8 * Δ - 4 * Δ ^ 2)) / (4 * Δ) := by
      field_simp; ring
    rw [this, hσ, hs2, sub_self, zero_div]
  refine ⟨(-1 + -s) / (2 * Δ), (-1 + s) / (2 * Δ), ?_, ?_, ?_, ?_, ?_⟩
  · exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  · exact div_lt_div_of_pos_right (by linarith) (by positivity)
  · change (-1 + s) / (2 * Δ) < 2
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · exact key _ (hroot (-s) (by ring))
  · exact key _ (hroot s rfl)

/-! ### Exact preference-ratio identities (E.16) and p. 700 -/

/-- Woodford (2003), App. E.4, p. 699–700: with `s_m = m̄u_m/(Ȳu_c)`, `σ_m = −u_m/(m̄u_mm)`,
`η_i = −u_c/(m̄u_mm)` and `v̄ = Ȳ/m̄`, the product `s_m σ_m⁻¹` equals `(η_i v̄)⁻¹` EXACTLY (the
book's "+ O(Δ̄)" only concerns the gap between `η_i` and the money-demand semi-elasticity). -/
theorem smSig_eq {Ybar mbar um umm uc : ℝ} (hY : Ybar ≠ 0) (hm : mbar ≠ 0) (hum : um ≠ 0)
    (humm : umm ≠ 0) (huc : uc ≠ 0) :
    mbar * um / (Ybar * uc) * (-(mbar * umm) / um) =
      1 / ((-uc / (mbar * umm)) * (Ybar / mbar)) := by
  field_simp

/-- Woodford (2003), (E.16) p. 699 and p. 700: `χ η_i v̄ = −Ȳu_cm/(m̄u_mm)`, the leading term
of `η_y` (with `χ = m̄u_cm/u_c`). -/
theorem chi_etaI_vbar_eq {Ybar mbar ucm umm uc : ℝ} (hm : mbar ≠ 0) (humm : umm ≠ 0)
    (huc : uc ≠ 0) :
    mbar * ucm / uc * (-uc / (mbar * umm)) * (Ybar / mbar) = -(Ybar * ucm) / (mbar * umm) := by
  field_simp

/-- Woodford (2003), footnote 44, p. 423: if `χ = 0` the limiting `η_y = χ η_i v̄` is zero. -/
theorem etaY_limit_chi_zero (etaI vbar : ℝ) : (0 : ℝ) * etaI * vbar = 0 := by ring

/-- Woodford (2003), (E.15) p. 699 (survey error 20, the consistent normalisation): with the
money-demand first-order condition `u_m = Δ̄ u_c`, `s_m = m̄u_m/(Ȳu_c) = Δ̄/v̄`. -/
theorem sm_consistent {Ybar mbar um uc Δ : ℝ} (hY : Ybar ≠ 0) (hm : mbar ≠ 0) (huc : uc ≠ 0)
    (hfoc : um = Δ * uc) : mbar * um / (Ybar * uc) = Δ / (Ybar / mbar) := by
  subst hfoc; field_simp

/-- Woodford (2003), pp. 421 and 423 (survey error 20): the printed normalisation
`s_m = m̄u_m/(c̄u_c)` equals `Δ̄/(s_C v̄)` with `s_C = c̄/Ȳ`. -/
theorem sm_p421 {Ybar mbar cbar um uc Δ : ℝ} (hY : Ybar ≠ 0) (hm : mbar ≠ 0) (hc : cbar ≠ 0)
    (huc : uc ≠ 0) (hfoc : um = Δ * uc) :
    mbar * um / (cbar * uc) = Δ / (cbar / Ybar * (Ybar / mbar)) := by
  subst hfoc; field_simp

/-- Woodford (2003), pp. 421, 423 vs (E.15) (survey error 20, CONFIRMED): the two
normalisations of `s_m` differ whenever `s_C ≠ 1` and `Δ̄ ≠ 0`. -/
theorem sm_p421_ne {sC vbar Δ : ℝ} (hsC : sC ≠ 1) (hv : vbar ≠ 0) (hΔ : Δ ≠ 0) :
    Δ / (sC * vbar) ≠ Δ / vbar := by
  intro h
  by_cases hs : sC = 0
  · rw [hs, zero_mul, div_zero] at h
    exact div_ne_zero hΔ hv h.symm
  · field_simp at h
    exact hsC h.symm

/-! ### Proposition 6.7 as an exact identity (Layer A), (E.15)–(E.18)

All utility expansions are divided by the common factor `Ȳ u_c`. -/

/-- Woodford (2003), §4.1 and App. E.4: the structural coefficients entering (4.1)–(4.9):
`σ⁻¹`, `ω`, `θ⁻¹`, `χ = m̄u_cm/u_c`, `η_i`, `v̄ = Ȳ/m̄` and the money-demand income elasticity
`η_y`. -/
structure TxParams where
  /-- `σ⁻¹`. -/
  sigInv : ℝ
  /-- `ω`, the elasticity of real marginal cost with respect to own output. -/
  omega : ℝ
  /-- `θ⁻¹`, the inverse elasticity of substitution between goods. -/
  thetaInv : ℝ
  /-- `χ = m̄ u_cm / u_c`. -/
  chi : ℝ
  /-- `η_i`, the interest semi-elasticity of money demand. -/
  etaI : ℝ
  /-- `v̄ = Ȳ/m̄`, steady-state velocity. -/
  vbar : ℝ
  /-- `η_y`, the income elasticity of money demand. -/
  etaY : ℝ

/-- Woodford (2003), App. E.4: a point of the expansion: the endogenous variables `Ŷ`,
`d = î − îᵐ`, `V = var_i ŷ(i)`, the money-demand residual `r` of (4.1) (footnote 4, p. 700: of
second order), the exogenous `g`, `q`, `ε^m`, the distortions `Φ_y`, `Δ̄`, and the coefficient
gaps `e₂ = s_mσ_m⁻¹ − (η_i v̄)⁻¹`, `e₃ = η_y − χη_i v̄` (both `O(Δ̄)` by (E.16)). -/
structure TxPoint where
  /-- `Ŷ_t`. -/
  Y : ℝ
  /-- `î_t − î_tᵐ`. -/
  d : ℝ
  /-- `g_t`. -/
  g : ℝ
  /-- `q_t`. -/
  q : ℝ
  /-- `ε_tᵐ`. -/
  eps : ℝ
  /-- `Φ_y`. -/
  Phi : ℝ
  /-- `Δ̄`. -/
  Delta : ℝ
  /-- `var_i ŷ_t(i)`. -/
  V : ℝ
  /-- The residual of the log-linear money demand (4.1). -/
  r : ℝ
  /-- `e₂ = s_m σ_m⁻¹ − (η_i v̄)⁻¹`. -/
  e2 : ℝ
  /-- `e₃ = η_y − χ η_i v̄`. -/
  e3 : ℝ

/-- The weighted scaling of a point: every variable of weight one is multiplied by `s`, the
second-order quantities `V` and `r` by `s²` (survey §4, Layer A). -/
def TxPoint.scale (s : ℝ) (x : TxPoint) : TxPoint :=
  ⟨s * x.Y, s * x.d, s * x.g, s * x.q, s * x.eps, s * x.Phi, s * x.Delta, s ^ 2 * x.V,
    s ^ 2 * x.r, s * x.e2, s * x.e3⟩

variable (P : TxParams)

/-- Woodford (2003), eq. (4.3), p. 420: `Ω_mc = σ⁻¹ + ω − χ η_y`. -/
def omegaMC : ℝ := P.sigInv + P.omega - P.chi * P.etaY

/-- Woodford (2003), eq. (4.4), p. 420: `ϕ = η_i χ / Ω_mc`. -/
noncomputable def varphi : ℝ := P.etaI * P.chi / omegaMC P

/-- Woodford (2003), eq. (4.5), p. 420: `Ŷⁿ = (σ⁻¹g + ωq + χ εᵐ)/Ω_mc`. -/
noncomputable def natRate (g q eps : ℝ) : ℝ :=
  (P.sigInv * g + P.omega * q + P.chi * eps) / omegaMC P

/-- Woodford (2003), (E.15) p. 699 with the consistent normalisation (survey error 20):
`s_m = Δ̄/v̄`. -/
noncomputable def sM (Δ : ℝ) : ℝ := Δ / P.vbar

/-- Woodford (2003), eq. (4.6), p. 421: `x* = (Φ_y + s_m η_y)/Ω_mc`. -/
noncomputable def xStar (Φ Δ : ℝ) : ℝ := (Φ + sM P Δ * P.etaY) / omegaMC P

/-- Woodford (2003), eq. (4.1), p. 420: `m̂ = η_y Ŷ − η_i(î − îᵐ) + εᵐ` plus the residual `r`. -/
def mHat (x : TxPoint) : ℝ := P.etaY * x.Y - P.etaI * x.d + x.eps + x.r

/-- Woodford (2003), (E.5) p. 694: `E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ`. -/
noncomputable def mOne (x : TxPoint) : ℝ := x.Y - (1 - P.thetaInv) / 2 * x.V

/-- Woodford (2003), p. 700: `s_m σ_m⁻¹ = (η_i v̄)⁻¹ + e₂`. -/
noncomputable def smSig (x : TxPoint) : ℝ := 1 / (P.etaI * P.vbar) + x.e2

/-- Woodford (2003), eq. (E.15), p. 699: the second-order expansion of `u(Y, m; ξ)` (divided
by `Ȳu_c`, policy-independent terms omitted). -/
noncomputable def uTaylor (x : TxPoint) : ℝ :=
  x.Y + (1 - P.sigInv) / 2 * x.Y ^ 2 + P.sigInv * x.g * x.Y + sM P x.Delta * mHat P x +
    (sM P x.Delta - smSig P x) / 2 * mHat P x ^ 2 + P.chi * mHat P x * x.Y +
    sM P x.Delta * P.sigInv * x.g * mHat P x +
    (sM P x.Delta * P.chi + smSig P x) * x.eps * mHat P x

/-- Woodford (2003), eq. (E.17), p. 700. -/
noncomputable def uE17 (x : TxPoint) : ℝ :=
  x.Y + (1 - P.sigInv) / 2 * x.Y ^ 2 + P.sigInv * x.g * x.Y + sM P x.Delta * mHat P x +
    P.chi * mHat P x * x.Y - 1 / (P.etaI * P.vbar) / 2 * (mHat P x - x.eps) ^ 2

/-- Woodford (2003), eq. (E.18), p. 700. -/
noncomputable def uE18 (x : TxPoint) : ℝ :=
  x.Y + (1 - P.sigInv) / 2 * x.Y ^ 2 + P.sigInv * x.g * x.Y + sM P x.Delta * P.etaY * x.Y -
    sM P x.Delta * P.etaI * x.d + P.chi * P.etaY / 2 * x.Y ^ 2 + P.chi * x.eps * x.Y -
    P.etaI / P.vbar / 2 * x.d ^ 2

/-- Woodford (2003), eqs. (E.3) integrated over goods, p. 694: the disutility of supply in
terms of `E_i ŷ` and `E_i ŷ² = (E_i ŷ)² + var_i ŷ`. -/
noncomputable def vTaylor (x : TxPoint) : ℝ :=
  (1 - x.Phi) * mOne P x + (1 + P.omega) / 2 * (mOne P x ^ 2 + x.V) - P.omega * x.q * mOne P x

/-- Woodford (2003), eq. (E.4), p. 694. -/
noncomputable def vE4 (x : TxPoint) : ℝ :=
  (1 - x.Phi) * x.Y + (1 + P.omega) / 2 * x.Y ^ 2 - P.omega * x.q * x.Y +
    (P.thetaInv + P.omega) / 2 * x.V

/-- Woodford (2003), eq. (4.9), p. 422 / (E.14): the quadratic form
`Ω_mc (x − x*)² + v̄⁻¹η_i(î − îᵐ + Δ̄)² + (θ⁻¹ + ω) var_i ŷ` with `x = Ŷ − Ŷⁿ`. -/
noncomputable def loss49 (x : TxPoint) : ℝ :=
  omegaMC P * (x.Y - natRate P x.g x.q x.eps - xStar P x.Phi x.Delta) ^ 2 +
    P.etaI / P.vbar * (x.d + x.Delta) ^ 2 + (P.thetaInv + P.omega) * x.V

/-- Woodford (2003), (4.9): the terms independent of policy, an explicit function of the
exogenous disturbances `g, q, εᵐ` and the distortions `Φ_y, Δ̄` only. -/
noncomputable def tip (g q eps Φ Δ : ℝ) : ℝ :=
  omegaMC P / 2 * (natRate P g q eps + xStar P Φ Δ) ^ 2 + P.etaI / P.vbar / 2 * Δ ^ 2 +
    Δ / P.vbar * eps + eps ^ 2 / (2 * (P.etaI * P.vbar))

/-- The `s_m`-terms dropped between (E.15) and (E.17), with the money residual scaled by `s`. -/
noncomputable def remA (s : ℝ) (x : TxPoint) : ℝ :=
  x.Delta / P.vbar * ((P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) ^ 2 / 2 +
    P.sigInv * x.g * (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) +
    P.chi * x.eps * (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r))

/-- The `e₂`-terms dropped between (E.15) and (E.17). -/
noncomputable def remB (s : ℝ) (x : TxPoint) : ℝ :=
  x.e2 * (x.eps * (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) -
    (P.etaY * x.Y - P.etaI * x.d + x.eps + s * x.r) ^ 2 / 2)

/-- The money-demand-residual terms produced in (E.18). -/
noncomputable def remC (s : ℝ) (x : TxPoint) : ℝ :=
  x.Delta / P.vbar * x.r + P.chi * x.r * x.Y -
    1 / (P.etaI * P.vbar) * (P.etaY * x.Y - P.etaI * x.d) * x.r -
    1 / (P.etaI * P.vbar) / 2 * s * x.r ^ 2

/-- The `e₃`-terms produced by writing `χη_iv̄` for `η_y` in quadratic coefficients (p. 700). -/
noncomputable def remD (x : TxPoint) : ℝ :=
  x.e3 * (1 / (P.etaI * P.vbar) * P.etaI * x.d * x.Y -
    1 / (P.etaI * P.vbar) / 2 * P.etaY * x.Y ^ 2)

/-- The terms dropped between (E.3) and (E.4) (using (E.5)). -/
noncomputable def remE (s : ℝ) (x : TxPoint) : ℝ :=
  x.Phi * ((1 - P.thetaInv) / 2) * x.V - (1 + P.omega) * ((1 - P.thetaInv) / 2) * x.Y * x.V +
    (1 + P.omega) / 2 * ((1 - P.thetaInv) / 2) ^ 2 * s * x.V ^ 2 +
    P.omega * x.q * ((1 - P.thetaInv) / 2) * x.V

/-- Woodford (2003), (4.9): the explicit remainder `O(‖Φ, ŷ, Δ̂, ξ̃‖³)`, written along the ray
of scale `s` (`remainder P 1` is the remainder itself; see `remainder_scale`). -/
noncomputable def remainder (s : ℝ) (x : TxPoint) : ℝ :=
  remA P s x + remB P s x + remC P s x + remD P x - remE P s x

/-- Woodford (2003), (E.15) ⟶ (E.17), pp. 699–700: dropping the `O(Δ̄)` quadratic coefficients
leaves the explicit cubic terms `remA + remB` and the policy-independent `(εᵐ)²/(2η_iv̄)`. -/
theorem E15_to_E17 (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0) (x : TxPoint) :
    uTaylor P x = uE17 P x + x.eps ^ 2 / (2 * (P.etaI * P.vbar)) + remA P 1 x + remB P 1 x := by
  simp only [uTaylor, uE17, remA, remB, smSig, sM, mHat]
  field_simp
  ring

/-- Woodford (2003), (E.17) ⟶ (E.18), p. 700: substituting the money demand (4.1); the
`χ m̂ Ŷ` cross terms cancel exactly against those of `−½(η_iv̄)⁻¹(m̂ − εᵐ)²` once
`η_y = χη_i v̄ + e₃`. -/
theorem E17_to_E18 (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0) (x : TxPoint)
    (he3 : P.etaY = P.chi * P.etaI * P.vbar + x.e3) :
    uE17 P x = uE18 P x + x.Delta / P.vbar * x.eps + remC P 1 x + remD P x := by
  simp only [uE17, uE18, remC, remD, sM, mHat]
  rw [he3]
  field_simp
  ring

/-- Woodford (2003), (E.3) ⟶ (E.4), p. 694: integrating over goods and using (E.5). -/
theorem E3_to_E4 (x : TxPoint) : vTaylor P x = vE4 P x + remE P 1 x := by
  simp only [vTaylor, vE4, remE, mOne]
  ring

/-- Woodford (2003), App. E.4, last display p. 700: (E.18) minus (E.4) is EXACTLY
`−½[Ω_mc(x − x*)² + v̄⁻¹η_i(î − îᵐ + Δ̄)² + (θ⁻¹+ω)var_i ŷ]` plus policy-independent terms,
given the consistent normalisation `s_m = Δ̄/v̄`. -/
theorem E18_minus_E4 (hΩ : omegaMC P ≠ 0) (hv : P.vbar ≠ 0) (x : TxPoint) :
    uE18 P x - vE4 P x = -loss49 P x / 2 +
      (omegaMC P / 2 * (natRate P x.g x.q x.eps + xStar P x.Phi x.Delta) ^ 2 +
        P.etaI / P.vbar / 2 * x.Delta ^ 2) := by
  have hs : P.sigInv = omegaMC P - P.omega + P.chi * P.etaY := by unfold omegaMC; ring
  simp only [uE18, vE4, loss49, natRate, xStar, sM]
  rw [hs]
  field_simp
  ring

/-- Woodford (2003), Proposition 6.7, eq. (4.9), p. 422 (proof (E.15)–(E.18), pp. 698–700),
Layer A: the period utility expansion (E.15) minus the disutility expansion (E.3) equals
`−½ × (4.9)` plus terms independent of policy (`tip`, a function of `g, q, εᵐ, Φ_y, Δ̄` only)
plus the explicit remainder `remainder P 1 x`, of weighted degree `≥ 3` (`remainder_scale`). -/
theorem prop_6_7_layerA (hΩ : omegaMC P ≠ 0) (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0)
    (x : TxPoint) (he3 : P.etaY = P.chi * P.etaI * P.vbar + x.e3) :
    uTaylor P x - vTaylor P x =
      -loss49 P x / 2 + tip P x.g x.q x.eps x.Phi x.Delta + remainder P 1 x := by
  rw [E15_to_E17 P hi hv, E17_to_E18 P hi hv x he3, E3_to_E4]
  have h := E18_minus_E4 P hΩ hv x
  simp only [tip, remainder]
  linear_combination h

/-- Woodford (2003), (4.9): the remainder has weighted degree at least three — along the
weighted ray `x ↦ x.scale s` it is `s³` times a polynomial in `s`. -/
theorem remainder_scale (s : ℝ) (x : TxPoint) :
    remainder P 1 (x.scale s) = s ^ 3 * remainder P s x := by
  simp only [remainder, remA, remB, remC, remD, remE, TxPoint.scale]
  ring

/-- Woodford (2003), (4.9): the remainder is `O(s³)` along every weighted ray, i.e. it is the
"`O(‖Φ, ŷ, Δ̂, ξ̃‖³)`" term. -/
theorem remainder_isBigO (x : TxPoint) :
    (fun s => remainder P 1 (x.scale s)) =O[𝓝 0] (fun s => s ^ 3) := by
  refine OneParamTaylor.isBigO_cube_of_scaling (fun s => remainder_scale P s x) ?_
  apply Continuous.continuousAt
  simp only [remainder, remA, remB, remC, remD, remE]
  fun_prop

/-- Woodford (2003), p. 423 (survey error 20): the expansion (E.15) written with the printed
normalisation `s_m = Δ̄/(s_C v̄)` instead of `Δ̄/v̄`. -/
noncomputable def uTaylorAlt (sC : ℝ) (x : TxPoint) : ℝ :=
  x.Y + (1 - P.sigInv) / 2 * x.Y ^ 2 + P.sigInv * x.g * x.Y + x.Delta / (sC * P.vbar) * mHat P x +
    (x.Delta / (sC * P.vbar) - smSig P x) / 2 * mHat P x ^ 2 + P.chi * mHat P x * x.Y +
    x.Delta / (sC * P.vbar) * P.sigInv * x.g * mHat P x +
    (x.Delta / (sC * P.vbar) * P.chi + smSig P x) * x.eps * mHat P x

/-- The discrepancy between the two normalisations. -/
noncomputable def altDiscrepancy (sC : ℝ) (x : TxPoint) : ℝ :=
  (x.Delta / (sC * P.vbar) - x.Delta / P.vbar) *
    (mHat P x + mHat P x ^ 2 / 2 + P.sigInv * x.g * mHat P x + P.chi * x.eps * mHat P x)

/-- Woodford (2003), (4.9) with the p. 421/423 normalisation (survey error 20): the identity
of `prop_6_7_layerA` acquires the extra term `altDiscrepancy`. -/
theorem alt_sm_discrepancy (hΩ : omegaMC P ≠ 0) (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0)
    (sC : ℝ) (x : TxPoint) (he3 : P.etaY = P.chi * P.etaI * P.vbar + x.e3) :
    uTaylorAlt P sC x - vTaylor P x = -loss49 P x / 2 + tip P x.g x.q x.eps x.Phi x.Delta +
      remainder P 1 x + altDiscrepancy P sC x := by
  have h := prop_6_7_layerA P hΩ hi hv x he3
  have h2 : uTaylorAlt P sC x = uTaylor P x + altDiscrepancy P sC x := by
    simp only [uTaylorAlt, uTaylor, altDiscrepancy, sM]
    ring
  rw [h2]
  linear_combination h

/-- Woodford (2003), pp. 421, 423 vs (E.15), (4.16) (survey error 20, CONFIRMED by
counterexample): with `s_C ≠ 1` the discrepancy is a POLICY-DEPENDENT SECOND-ORDER term. Take
the policy point with only `î − îᵐ = d` and `Δ̄` non-zero and compare with the same exogenous
state at `d = 0` (so any policy-independent term cancels): the difference is not `O(s³)`
along the weighted ray. -/
theorem alt_sm_not_isBigO {sC Δ d : ℝ} (hsC : sC ≠ 1) (hv : P.vbar ≠ 0) (hi : P.etaI ≠ 0)
    (hΔ : Δ ≠ 0) (hd : d ≠ 0) :
    ¬ (fun s => altDiscrepancy P sC ((⟨0, d, 0, 0, 0, 0, Δ, 0, 0, 0, 0⟩ : TxPoint).scale s) -
        altDiscrepancy P sC ((⟨0, 0, 0, 0, 0, 0, Δ, 0, 0, 0, 0⟩ : TxPoint).scale s))
        =O[𝓝 0] (fun s => s ^ 3) := by
  intro hO
  set c := Δ / (sC * P.vbar) - Δ / P.vbar with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr (sm_p421_ne hsC hv hΔ)
  set a := -(c * P.etaI * d) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hc0 hi) hd)
  set b := c * P.etaI ^ 2 * d ^ 2 / 2 with hb
  have hf : ∀ s, altDiscrepancy P sC ((⟨0, d, 0, 0, 0, 0, Δ, 0, 0, 0, 0⟩ : TxPoint).scale s) -
      altDiscrepancy P sC ((⟨0, 0, 0, 0, 0, 0, Δ, 0, 0, 0, 0⟩ : TxPoint).scale s) =
      s ^ 2 * (a + b * s) := by
    intro s
    simp only [altDiscrepancy, mHat, TxPoint.scale, ha, hb, hc]
    field_simp
    ring
  obtain ⟨C, hC⟩ := hO.bound
  -- `a + b s → 0` along `s → 0, s ≠ 0`, but also `→ a ≠ 0`
  have h1 : Tendsto (fun s : ℝ => a + b * s) (𝓝[≠] 0) (𝓝 0) := by
    have hbound : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ‖a + b * s‖ ≤ C * ‖s‖ := by
      filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with s hs hs0
      rw [hf s, norm_mul, norm_pow, norm_pow] at hs
      have hpos : 0 < ‖s‖ ^ 2 := by
        have : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs0
        positivity
      have : ‖s‖ ^ 2 * ‖a + b * s‖ ≤ ‖s‖ ^ 2 * (C * ‖s‖) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
    have hz : Tendsto (fun s : ℝ => C * ‖s‖) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => C * ‖s‖) (𝓝 0) (𝓝 (C * ‖(0 : ℝ)‖)) :=
        tendsto_const_nhds.mul (continuous_norm.tendsto 0)
      rw [norm_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm' hbound hz
  have h2 : Tendsto (fun s : ℝ => a + b * s) (𝓝[≠] 0) (𝓝 a) := by
    have : Tendsto (fun s : ℝ => a + b * s) (𝓝 0) (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ha0 (tendsto_nhds_unique h2 h1)

/-! ### Real marginal cost and the aggregate-supply relations (4.2), (4.7), (4.8) -/

/-- Woodford (2003), eq. (4.2), p. 420: substituting money demand (4.1) into the log-linear
real marginal cost `ŝ = (ω + σ⁻¹)Ŷ − (σ⁻¹g + ωq) − χ m̂` (Chapter 4) gives
`ŝ = Ω_mc [x + ϕ(î − îᵐ)]` with `x = Ŷ − Ŷⁿ` and `Ŷⁿ` from (4.5). -/
theorem eq_4_2 (hΩ : omegaMC P ≠ 0) {Y d g q eps s : ℝ}
    (hs : s = (P.omega + P.sigInv) * Y - (P.sigInv * g + P.omega * q) -
      P.chi * (P.etaY * Y - P.etaI * d + eps)) :
    s = omegaMC P * ((Y - natRate P g q eps) + varphi P * d) := by
  have hs' : P.sigInv = omegaMC P - P.omega + P.chi * P.etaY := by unfold omegaMC; ring
  rw [hs]
  simp only [natRate, varphi]
  rw [hs']
  field_simp
  ring

/-- Woodford (2003), eq. (4.8), p. 421: the Calvo aggregate-supply relation with the
interest-rate differential. From the Chapter 3 relation `π_t = ξ/(1+ωθ) ŝ_t + βE_tπ_{t+1}`
(`ξ = (1−α)(1−αβ)/α`, restated as a hypothesis) and (4.2):
`π_t = κ[x_t + ϕ(î_t − îᵐ_t)] + βE_tπ_{t+1}` with `κ = ξ Ω_mc/(1+ωθ)`. -/
theorem calvo_AS_4_8 {S : Type*} (𝔼 : ExpectationSystem S) {α β θ : ℝ}
    (π s x d : ℕ → S → ℝ)
    (hcalvo : ∀ t, π t = ((1 - α) * (1 - α * β) / α / (1 + P.omega * θ)) • s t +
      β • 𝔼.E t (π (t + 1)))
    (hs : ∀ t, s t = omegaMC P • (x t + varphi P • d t)) (t : ℕ) :
    π t = ((1 - α) * (1 - α * β) / α * omegaMC P / (1 + P.omega * θ)) •
      (x t + varphi P • d t) + β • 𝔼.E t (π (t + 1)) := by
  rw [hcalvo t, hs t, smul_smul]
  congr 2
  ring

/-- Woodford (2003), eq. (4.7), p. 421: the New Classical aggregate-supply relation
`π_t = κ[x_t + ϕ(î_t − îᵐ_t)] + E_{t−1}π_t` with `κ = (ι/(1−ι)) Ω_mc/(1+ωθ)`, from the
Chapter 3 relation `π_t = (ι/(1−ι))/(1+ωθ) ŝ_t + E_{t−1}π_t` (a hypothesis; `pe t` is
`E_{t−1}π_t`) and (4.2). -/
theorem newClassical_AS_4_7 {S : Type*} {ι θ : ℝ} (π pe s x d : ℕ → S → ℝ)
    (hnc : ∀ t, π t = (ι / (1 - ι) / (1 + P.omega * θ)) • s t + pe t)
    (hs : ∀ t, s t = omegaMC P • (x t + varphi P • d t)) (t : ℕ) :
    π t = (ι / (1 - ι) * omegaMC P / (1 + P.omega * θ)) • (x t + varphi P • d t) + pe t := by
  rw [hnc t, hs t, smul_smul]
  congr 2
  ring

/-! ### Proposition 6.8: the normalised loss (4.10)–(4.12) -/

/-- Woodford (2003), eq. (4.8), p. 421: `κ = (1−α)(1−αβ)/α · Ω_mc/(1+ωθ)`. -/
noncomputable def kappaCalvo (α β θ : ℝ) : ℝ :=
  (1 - α) * (1 - α * β) / α * omegaMC P / (1 + P.omega * θ)

/-- Woodford (2003), eq. (4.11), p. 423: `λ_x = κ/θ`. -/
noncomputable def lambdaX (α β θ : ℝ) : ℝ := kappaCalvo P α β θ / θ

/-- Woodford (2003), eq. (4.11), p. 423: `λ_i = η_i λ_x/(v̄ Ω_mc)`. -/
noncomputable def lambdaI (lx : ℝ) : ℝ := P.etaI * lx / (P.vbar * omegaMC P)

/-- Woodford (2003), eq. (4.10), p. 423: `L_t = π_t² + λ_x(x_t − x*)² + λ_i(î_t − îᵐ_t + Δ̄)²`;
here `xg = x_t − x*` and `dd = î_t − îᵐ_t + Δ̄`. -/
noncomputable def loss410 (α β θ infl xg dd : ℝ) : ℝ :=
  infl ^ 2 + lambdaX P α β θ * xg ^ 2 + lambdaI P (lambdaX P α β θ) * dd ^ 2

/-- Woodford (2003), (4.11), p. 423: `λ_x > 0`. -/
theorem lambdaX_pos {α β θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hθ : 0 < θ) (hω : 0 ≤ P.omega) (hΩ : 0 < omegaMC P) : 0 < lambdaX P α β θ := by
  unfold lambdaX kappaCalvo
  have h1 : 0 < 1 - α * β := by nlinarith
  have h2 : 0 < 1 + P.omega * θ := by nlinarith
  have h3 : 0 < 1 - α := by linarith
  positivity

/-- Woodford (2003), (4.11), p. 423: `λ_i > 0`. -/
theorem lambdaI_pos {lx : ℝ} (hlx : 0 < lx) (hi : 0 < P.etaI) (hv : 0 < P.vbar)
    (hΩ : 0 < omegaMC P) : 0 < lambdaI P lx := by
  unfold lambdaI; positivity

/-- Woodford (2003), Proposition 6.8, (4.10)–(4.11), p. 423, with genuine discounted sums.
Given the discounted sums of the (expected) per-period terms `X2 t = (x_t − x*)²`,
`I2 t = (î_t − îᵐ_t + Δ̄)²`, `P2 t = π_t²`, and the Calvo dispersion relation of Props. 6.3/6.4
(restated as the hypothesis `hV`: `Σβᵗ var_i ŷ_t = θ²(ψ Σβᵗ π_t² + T₀)`, `T₀` independent of
policy), the discounted sum of the bracket of (4.9) equals `Λ Σβᵗ L_t + t.i.p.` with
`Λ = θ(1+ωθ)ψ > 0` and `L_t` the loss (4.10) with the weights (4.11). -/
theorem prop_6_8 {α β θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1) (hθ : 0 < θ)
    (hθi : P.thetaInv = 1 / θ) (hω : 0 ≤ P.omega) (hΩ : 0 < omegaMC P) (hv : P.vbar ≠ 0)
    {X2 I2 P2 V : ℕ → ℝ} {A B Sπ T0 : ℝ} (hX : HasSum (fun t => β ^ t * X2 t) A)
    (hI : HasSum (fun t => β ^ t * I2 t) B) (hP : HasSum (fun t => β ^ t * P2 t) Sπ)
    (hV : HasSum (fun t => β ^ t * V t) (θ ^ 2 * (calvoK α β * Sπ + T0))) :
    HasSum (fun t => β ^ t * (omegaMC P * X2 t + P.etaI / P.vbar * I2 t +
        (P.thetaInv + P.omega) * V t))
      (θ * (1 + P.omega * θ) * calvoK α β *
          (Sπ + lambdaX P α β θ * A + lambdaI P (lambdaX P α β θ) * B) +
        (P.thetaInv + P.omega) * θ ^ 2 * T0) ∧
    HasSum (fun t => β ^ t * (P2 t + lambdaX P α β θ * X2 t +
        lambdaI P (lambdaX P α β θ) * I2 t))
      (Sπ + lambdaX P α β θ * A + lambdaI P (lambdaX P α β θ) * B) := by
  have hαβ : α * β < 1 := by nlinarith
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h2 : (1 + P.omega * θ) ≠ 0 := by nlinarith
  have h3 : (1 - α) ≠ 0 := by linarith
  have hΩ' := hΩ.ne'
  have hθ' := hθ.ne'
  have hα' := hα0.ne'
  have hsum := ((hX.mul_left (omegaMC P)).add (hI.mul_left (P.etaI / P.vbar))).add
    (hV.mul_left (P.thetaInv + P.omega))
  have hsum2 := (hP.add (hX.mul_left (lambdaX P α β θ))).add
    (hI.mul_left (lambdaI P (lambdaX P α β θ)))
  refine ⟨?_, ?_⟩
  · convert hsum using 1
    · funext t; ring
    · simp only [lambdaI, lambdaX, kappaCalvo, calvoK]
      rw [hθi]
      field_simp
      ring
  · convert hsum2 using 1
    funext t; ring

/-- Woodford (2003), eq. (4.12), p. 424: with `η_y = χη_i v̄` (the small-`Δ̄` limit, (E.16)) and
`χ ≠ 0`, `λ_i = (η_i/η_y) ϕ λ_x`. -/
theorem lambdaI_eq_4_12 (hχ : P.chi ≠ 0) (hi : P.etaI ≠ 0) (hv : P.vbar ≠ 0)
    (hΩ : omegaMC P ≠ 0) (hey : P.etaY = P.chi * P.etaI * P.vbar) (lx : ℝ) :
    lambdaI P lx = P.etaI / P.etaY * varphi P * lx := by
  unfold lambdaI varphi
  rw [hey]
  field_simp

/-- Woodford (2003), (4.12) and footnote 44, pp. 423–424: the hypothesis `χ ≠ 0` is needed.
At `χ = 0` the limiting `η_y = χη_i v̄` is `0`, the right side of (4.12) is not meaningful
(it evaluates to `0` in Lean's division convention) while `λ_i > 0` by (4.11). -/
theorem lambdaI_4_12_chi_zero (hχ : P.chi = 0) (hey : P.etaY = P.chi * P.etaI * P.vbar)
    {lx : ℝ} (hlx : 0 < lx) (hi : 0 < P.etaI) (hv : 0 < P.vbar) (hΩ : 0 < omegaMC P) :
    P.etaI / P.etaY * varphi P * lx = 0 ∧ 0 < lambdaI P lx := by
  refine ⟨?_, lambdaI_pos P hlx hi hv hΩ⟩
  rw [hey, hχ]; simp

/-! ### The target interest rate `i*` and (4.13)–(4.16) -/

/-- Woodford (2003), eq. (4.13), p. 424: with interest on money fixed at `īᵐ` (so `îᵐ = 0`) the
interest term of (4.10) is `(î + Δ̄)² = (î − i*)² + (Δ̄² − i*²) + 2(Δ̄ + i*) î`: the middle term
is policy-independent and the last is `O(Δ̄² î)`, third order (`abs_log_one_sub_add_le`). -/
theorem loss_4_13_identity (ih Δ : ℝ) :
    (ih + Δ) ^ 2 = (ih - Real.log (1 - Δ)) ^ 2 + (Δ ^ 2 - Real.log (1 - Δ) ^ 2) +
      2 * (Δ + Real.log (1 - Δ)) * ih := by ring

/-- Woodford (2003), (4.13), p. 424: the bound on the policy-dependent discrepancy. -/
theorem loss_4_13_bound {ih Δ : ℝ} (h : |Δ| < 1) :
    |2 * (Δ + Real.log (1 - Δ)) * ih| ≤ 2 * (Δ ^ 2 / (1 - |Δ|)) * |ih| := by
  rw [abs_mul, abs_mul, abs_two, add_comm Δ]
  gcongr
  exact abs_log_one_sub_add_le h

/-- Woodford (2003), eq. (4.16), p. 426, with the consistent `s_m = Δ̄/v̄`:
`x* + ϕ i* = Φ_y/Ω_mc + s_m e₃/Ω_mc + ϕ(Δ̄ + i*)`, where `e₃ = η_y − χη_iv̄ = O(Δ̄)` and
`Δ̄ + i* = O(Δ̄²)`: so `x* + ϕ i* = Φ_y/Ω_mc + O(‖Φ‖²)`. -/
theorem eq_4_16 (hΩ : omegaMC P ≠ 0) (hv : P.vbar ≠ 0) {Φ Δ iS e3 : ℝ}
    (hey : P.etaY = P.chi * P.etaI * P.vbar + e3) :
    xStar P Φ Δ + varphi P * iS =
      Φ / omegaMC P + Δ / P.vbar * e3 / omegaMC P + varphi P * (Δ + iS) := by
  have hs' : P.etaY = P.chi * P.etaI * P.vbar + e3 := hey
  simp only [xStar, varphi, sM]
  rw [hs']
  field_simp
  ring

/-- Woodford (2003), (4.16), p. 426, with `η_y = χη_i v̄` and `i* = log(1 − Δ̄)`: the explicit
bound `|x* + ϕ i* − Φ_y/Ω_mc| ≤ |ϕ| Δ̄²/(1 − |Δ̄|)`. -/
theorem eq_4_16_bound (hΩ : omegaMC P ≠ 0) (hv : P.vbar ≠ 0) {Φ Δ : ℝ} (hΔ : |Δ| < 1)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) :
    |xStar P Φ Δ + varphi P * Real.log (1 - Δ) - Φ / omegaMC P| ≤
      |varphi P| * (Δ ^ 2 / (1 - |Δ|)) := by
  have hey' : P.etaY = P.chi * P.etaI * P.vbar + 0 := by rw [hey, add_zero]
  rw [eq_4_16 P hΩ hv hey']
  simp only [mul_zero, zero_div, add_zero, add_sub_cancel_left, abs_mul]
  gcongr
  rw [add_comm]
  exact abs_log_one_sub_add_le hΔ

/-- Woodford (2003), p. 425: with `Φ_y = 0` and `η_y = χη_i v̄`, `x* = ϕΔ̄ = −ϕ i* + ϕ(Δ̄ + i*)`,
so `x* = −ϕ i* + O(Δ̄²)`, and `x* > 0` when `ϕ > 0` and `Δ̄ > 0`. -/
theorem xStar_eq_4_15 (hΩ : omegaMC P ≠ 0) (hv : P.vbar ≠ 0) {Δ iS : ℝ}
    (hey : P.etaY = P.chi * P.etaI * P.vbar) :
    xStar P 0 Δ = varphi P * Δ ∧ xStar P 0 Δ = -(varphi P * iS) + varphi P * (Δ + iS) := by
  have h1 : xStar P 0 Δ = varphi P * Δ := by
    simp only [xStar, varphi, sM]
    rw [hey]
    field_simp
    ring
  exact ⟨h1, by rw [h1]; ring⟩

/-- Woodford (2003), eq. (4.15), p. 425: if `x* + ϕ i* = 0` then the New Classical AS (4.7)
with `îᵐ = 0`, `π_t = κ[x_t + ϕ î_t] + E_{t−1}π_t`, can be written
`π_t = κ[(x_t − x*) + ϕ(î_t − i*)] + E_{t−1}π_t`. -/
theorem AS_4_15 {κ φ xs iS infl pe x ih : ℝ} (hx : xs + φ * iS = 0)
    (hAS : infl = κ * (x + φ * ih) + pe) :
    infl = κ * ((x - xs) + φ * (ih - iS)) + pe := by
  rw [hAS]; linear_combination κ * hx

/-! ### The discounted loss (4.17) -/

/-- Woodford (2003), eq. (4.14), p. 425: `L_t = (π_t − E_{t−1}π_t)² + λ_x(x_t − x*)² +
λ_i(î_t − i*)²`. -/
def loss414 (lx li xs iS infl pe x ih : ℝ) : ℝ :=
  (infl - pe) ^ 2 + lx * (x - xs) ^ 2 + li * (ih - iS) ^ 2

/-- Woodford (2003), eq. (4.17), p. 426: the bracket inside the discounted sum,
`(π − E_{t−1}π)² + λ_x(x + ϕi*)² + 2(λ_xϕΦ_y/Ω_mc)(î − i*) + λ_i(î − i*)²`. -/
noncomputable def bracket417 (lx li φ Φ Ω iS infl pe x ih : ℝ) : ℝ :=
  (infl - pe) ^ 2 + lx * (x + φ * iS) ^ 2 + 2 * (lx * φ * Φ / Ω) * (ih - iS) +
    li * (ih - iS) ^ 2

/-- Woodford (2003), (4.17), p. 426, period by period: with the AS (4.7) (`îᵐ = 0`),
`λ_x = κ/θ` and `x* = Φ_y/Ω_mc − ϕ i*` (4.16),
`L_t = −2Φ_y/(θΩ_mc)(π_t − E_{t−1}π_t) + bracket_t + λ_x(Φ_y/Ω_mc)²`. -/
theorem loss_4_17_period {κ θ lx li φ Φ Ω iS xs infl pe x ih : ℝ} (hθ : θ ≠ 0)
    (hΩ : Ω ≠ 0) (hlx : lx = κ / θ) (hxs : xs = Φ / Ω - φ * iS)
    (hAS : infl - pe = κ * (x + φ * ih)) :
    loss414 lx li xs iS infl pe x ih =
      -2 * (Φ / (θ * Ω)) * (infl - pe) + bracket417 lx li φ Φ Ω iS infl pe x ih +
        lx * (Φ / Ω) ^ 2 := by
  simp only [loss414, bracket417]
  rw [hAS, hxs, hlx]
  field_simp
  ring

/-- Woodford (2003), eq. (4.17), p. 426 (CORRECTED, survey error 21), as a genuine discounted
sum under an arbitrary expectation system: with `pe (t+1) = E_t π_{t+1}` (so `pe t` is
`E_{t−1}π_t`, `pe 0` an initial condition),
`Σ βᵗ E₀L_t = −2Φ_y/(θΩ_mc) E₀(π₀ − E_{−1}π₀) + Σ βᵗ E₀[bracket_t] + λ_x(Φ_y/Ω_mc)²/(1−β)`.
There is no `−κ_i î₀` term (see `printed_4_17_ne`). -/
theorem loss_4_17 {S : Type*} (𝔼 : ExpectationSystem S) {β κ θ lx li φ Φ Ω iS xs : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hΩ : Ω ≠ 0) (hlx : lx = κ / θ)
    (hxs : xs = Φ / Ω - φ * iS) (infl pe x ih : ℕ → S → ℝ)
    (hAS : ∀ t ω, infl t ω - pe t ω = κ * (x t ω + φ * ih t ω))
    (hpe : ∀ t, pe (t + 1) = 𝔼.E t (infl (t + 1))) (ω0 : S)
    (hB : Summable (fun t => β ^ t *
      𝔼.E 0 (fun ω => bracket417 lx li φ Φ Ω iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) ω0)) :
    ∑' t, β ^ t * 𝔼.E 0 (fun ω => loss414 lx li xs iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) ω0 =
      -2 * (Φ / (θ * Ω)) * 𝔼.E 0 (fun ω => infl 0 ω - pe 0 ω) ω0 +
        ∑' t, β ^ t * 𝔼.E 0
          (fun ω => bracket417 lx li φ Φ Ω iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) ω0 +
        lx * (Φ / Ω) ^ 2 / (1 - β) := by
  set c := -2 * (Φ / (θ * Ω))
  set K0 := lx * (Φ / Ω) ^ 2
  -- the surprise terms have zero date-0 expectation from date 1 on
  have hsurp : ∀ t, t ≠ 0 → 𝔼.E 0 (fun ω => infl t ω - pe t ω) = 0 := by
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
    have hfun : (fun ω => infl (s + 1) ω - pe (s + 1) ω) = infl (s + 1) - 𝔼.E s (infl (s + 1)) := by
      funext ω; rw [hpe s]; rfl
    rw [hfun, map_sub, 𝔼.tower (Nat.zero_le s), sub_self]
  -- the period identity at the level of random variables
  have hper : ∀ t, 𝔼.E 0 (fun ω => loss414 lx li xs iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) ω0 =
      c * 𝔼.E 0 (fun ω => infl t ω - pe t ω) ω0 +
      𝔼.E 0 (fun ω => bracket417 lx li φ Φ Ω iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) ω0 + K0 := by
    intro t
    have hfun : (fun ω => loss414 lx li xs iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) =
        c • (fun ω => infl t ω - pe t ω) +
        (fun ω => bracket417 lx li φ Φ Ω iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) +
        (fun _ => K0) := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact loss_4_17_period hθ hΩ hlx hxs (hAS t ω)
    rw [hfun, map_add, map_add, map_smul, 𝔼.const]
    rfl
  have h1 : HasSum (fun t => β ^ t * (c * 𝔼.E 0 (fun ω => infl t ω - pe t ω) ω0))
      (c * 𝔼.E 0 (fun ω => infl 0 ω - pe 0 ω) ω0) := by
    have := hasSum_single (f := fun t => β ^ t * (c * 𝔼.E 0 (fun ω => infl t ω - pe t ω) ω0))
      0 (fun t ht => by rw [hsurp t ht]; simp)
    simpa using this
  have h3 : HasSum (fun t => β ^ t * K0) (K0 / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right K0
    rwa [div_eq_inv_mul]
  have htot := (h1.add hB.hasSum).add h3
  rw [show (fun t => β ^ t * 𝔼.E 0
      (fun ω => loss414 lx li xs iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) ω0) =
      fun t => β ^ t * (c * 𝔼.E 0 (fun ω => infl t ω - pe t ω) ω0) +
        β ^ t * 𝔼.E 0
          (fun ω => bracket417 lx li φ Φ Ω iS (infl t ω) (pe t ω) (x t ω) (ih t ω)) ω0 +
        β ^ t * K0 from funext fun t => by rw [hper t]; ring]
  rw [htot.tsum_eq]

/-- Woodford (2003), (4.17): if `π₀` is known at date 0 and `E_{−1}π₀` is an initial
condition known at date 0, the first term is `−2Φ_y/(θΩ_mc)(π₀ − E_{−1}π₀)`, i.e.
`−2Φ_y/(θΩ_mc) π₀ + t.i.p.` -/
theorem loss_4_17_first_term {S : Type*} (𝔼 : ExpectationSystem S) (infl pe : ℕ → S → ℝ)
    (h0 : 𝔼.E 0 (infl 0) = infl 0) (hpe0 : 𝔼.E 0 (pe 0) = pe 0) (ω0 : S) :
    𝔼.E 0 (fun ω => infl 0 ω - pe 0 ω) ω0 = infl 0 ω0 - pe 0 ω0 := by
  have : (fun ω => infl 0 ω - pe 0 ω) = infl 0 - pe 0 := rfl
  rw [this, map_sub, h0, hpe0]
  rfl

/-- Woodford (2003), eq. (4.17), p. 426 (survey error 21, CONFIRMED): the printed first term
`−2Φ_y/(θΩ_mc)[π₀ − κ_i î₀]` (with `κ_i` never defined) differs from the correct
`−2Φ_y/(θΩ_mc)π₀` whenever `Φ_y, κ_i, î₀ ≠ 0`. -/
theorem printed_4_17_ne {θ Ω Φ κi i0 π0 : ℝ} (hθ : θ ≠ 0) (hΩ : Ω ≠ 0) (hΦ : Φ ≠ 0)
    (hκi : κi ≠ 0) (hi0 : i0 ≠ 0) :
    -2 * (Φ / (θ * Ω)) * (π0 - κi * i0) ≠ -2 * (Φ / (θ * Ω)) * π0 := by
  intro h
  have : 2 * (Φ / (θ * Ω)) * κi * i0 = 0 := by linear_combination h
  have hc : Φ / (θ * Ω) ≠ 0 := div_ne_zero hΦ (mul_ne_zero hθ hΩ)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hκi) hi0) this

/-- Woodford (2003), (4.17) and p. 425 (survey error 21): reading `κ_i = κϕ` (the coefficient
on `î` in (4.7)), the printed extra term `2Φ_y/(θΩ_mc) κ_i î₀` equals exactly the date-0 term
`2(λ_xϕΦ_y/Ω_mc) î₀` of the in-sum interest term: the printed formula counts it twice. -/
theorem printed_4_17_double_count {κ θ lx φ Φ Ω i0 : ℝ} (hθ : θ ≠ 0) (hlx : lx = κ / θ) :
    2 * (Φ / (θ * Ω)) * (κ * φ * i0) = 2 * (lx * φ * Φ / Ω) * i0 := by
  rw [hlx]
  by_cases hΩ : Ω = 0
  · simp [hΩ]
  · field_simp

/-- Woodford (2003), p. 426: the bracket of (4.17) is non-negative whenever `î ≥ i*`
(the equilibrium requirement `i_t ≥ īᵐ`), `ϕ, Φ_y, λ_x, λ_i ≥ 0` and `Ω_mc > 0`. -/
theorem bracket_4_17_nonneg {lx li φ Φ Ω iS infl pe x ih : ℝ} (hlx : 0 ≤ lx) (hli : 0 ≤ li)
    (hφ : 0 ≤ φ) (hΦ : 0 ≤ Φ) (hΩ : 0 < Ω) (hih : iS ≤ ih) :
    0 ≤ bracket417 lx li φ Φ Ω iS infl pe x ih := by
  unfold bracket417
  have : 0 ≤ ih - iS := by linarith
  positivity

/-- Woodford (2003), pp. 425–426: setting `î_t = i*` and `π_t = E_{t−1}π_t` makes the bracket of
(4.17) zero (then (4.7) forces `x_t = −ϕ i*`), so these policies minimise every term but the
first. -/
theorem bracket_4_17_eq_zero {κ lx li φ Φ Ω iS infl pe x ih : ℝ} (hκ : κ ≠ 0)
    (hAS : infl - pe = κ * (x + φ * ih)) (hih : ih = iS) (hπ : infl = pe) :
    bracket417 lx li φ Φ Ω iS infl pe x ih = 0 := by
  have hx : x + φ * iS = 0 := by
    rw [hπ, sub_self, hih] at hAS
    rcases mul_eq_zero.mp hAS.symm with h | h
    · exact absurd h hκ
    · exact h
  simp only [bracket417, hπ, hih, sub_self, hx]
  ring

/-! ### Table 6.1 / Table 6.2 arithmetic -/

/-- Woodford (2003), Table 6.1 and p. 432: `3.72² = 13.8384`. -/
theorem vi_sq : (3.72 : ℝ) ^ 2 = 13.8384 := by norm_num

/-- Woodford (2003), p. 432 and Table 6.2: the printed `V[i] = 13.83` is consistent with the
printed standard deviation `3.72` (rounded): `√13.83 ∈ [3.715, 3.725)`. (`3.72²` itself rounds
to `13.84`.) -/
theorem vi_rounding : (3.715 : ℝ) ^ 2 ≤ 13.83 ∧ (13.83 : ℝ) < 3.725 ^ 2 ∧
    |(3.72 : ℝ) ^ 2 - 13.84| < 0.005 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [abs_lt]; constructor <;> norm_num

/-- Woodford (2003), Table 6.2, p. 433 and p. 432 (`Ê[L⁰] = V[π] + λ_x V[x]`): with
`λ_x = 0.04835` every row reproduces the printed `Ê[L⁰]` to the printed rounding. -/
theorem table62_rows :
    |(0.037 : ℝ) + 0.04835 * 4.015 - 0.231| ≤ 0.0005 ∧
    |(0.130 : ℝ) + 0.04835 * 10.60 - 0.643| ≤ 0.0005 ∧
    |(0.151 : ℝ) + 0.04835 * 11.75 - 0.719| ≤ 0.0005 ∧
    |(0.677 : ℝ) + 0.04835 * 29.35 - 2.096| ≤ 0.0005 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> norm_num

/-- Woodford (2003), Tables 6.1–6.2: the value `λ_x = 0.04835` is of the form `16κ/θ` (footnote
52) with `θ = 7.88` and `κ` within the rounding interval of the printed `κ = 0.024`. -/
theorem table62_lambda_form :
    (0.0235 : ℝ) ≤ 0.04835 * 7.88 / 16 ∧ 0.04835 * 7.88 / 16 < (0.0245 : ℝ) ∧
    16 * (0.04835 * 7.88 / 16) / 7.88 = (0.04835 : ℝ) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Woodford (2003), Table 6.2, last row: for ANY `V[π], V[x]` within the printed rounding,
`V[π] + λ_x V[x]` rounds to the printed `2.096` only if `0.0483 ≤ λ_x ≤ 0.0484`. -/
theorem table62_lambda_range {lam vp vx : ℝ} (hvp : |vp - 0.677| ≤ 0.0005)
    (hvx : |vx - 29.35| ≤ 0.005) (hrow : |vp + lam * vx - 2.096| ≤ 0.0005) :
    0.0483 ≤ lam ∧ lam ≤ 0.0484 := by
  rw [abs_le] at hvp hvx hrow
  obtain ⟨h1, h2⟩ := hvp
  obtain ⟨h3, h4⟩ := hvx
  obtain ⟨h5, h6⟩ := hrow
  constructor <;> nlinarith

/-- Woodford (2003), Tables 6.1–6.2: computed with the PRINTED `κ = 0.024`, `θ = 7.88`,
`λ_x = 16κ/θ = 0.04873…` does not reproduce the last row of Table 6.2 (nor does the printed
rounded `λ_x = 0.048`): the table was computed with an unrounded `κ ≈ 0.0238`. -/
theorem table62_row5_printed {vp vx : ℝ} (hvp : |vp - 0.677| ≤ 0.0005)
    (hvx : |vx - 29.35| ≤ 0.005) :
    0.0005 < |vp + 16 * 0.024 / 7.88 * vx - 2.096| ∧ 0.0005 < |vp + 0.048 * vx - 2.096| := by
  rw [abs_le] at hvp hvx
  obtain ⟨h1, h2⟩ := hvp
  obtain ⟨h3, h4⟩ := hvx
  constructor
  · rw [lt_abs]; left; nlinarith
  · rw [lt_abs]; right; nlinarith

/-- Woodford (2003), p. 433: with Table 6.1's `η_i = 28`, `χ = 0.02`, `Ω_mc = 0.63`, (4.4) gives
`ϕ = 0.888…` quarters `= 0.222…` years ("approximately 0.22 years"). -/
theorem varphi_years : |28 * 0.02 / 0.63 / 4 - (0.22 : ℝ)| < 0.005 := by
  rw [abs_lt]; constructor <;> norm_num

/-! ### Supplementary claims of pp. 421–423 -/

/-- Woodford (2003), p. 421: "if `Φ_y ≥ 0`, `x* > 0`" holds once `Ω_mc > 0` and
`Φ_y + s_m η_y > 0` (e.g. `Φ_y ≥ 0`, `s_m η_y ≥ 0`, one of them strictly positive). -/
theorem xStar_pos (hΩ : 0 < omegaMC P) {Φ Δ : ℝ} (hpos : 0 < Φ + sM P Δ * P.etaY) :
    0 < xStar P Φ Δ := by
  unfold xStar; exact div_pos hpos hΩ

/-- Woodford (2003), p. 421 (imprecision): with `Φ_y = 0` and `Δ̄ = 0` one gets `x* = 0`, so
`Φ_y ≥ 0` alone does not give `x* > 0`. -/
theorem xStar_zero : xStar P 0 0 = 0 := by simp [xStar, sM]

/-- Woodford (2003), p. 423: the Friedman condition `i_t = iᵐ_t` corresponds to
`î_t = îᵐ_t + log((1 + īᵐ)/(1 + ī))`, i.e. `î_t = îᵐ_t − Δ̄ + O(Δ̄²)` by `abs_log_one_sub_add_le`
(with `î = log((1+i)/(1+ī))`, `îᵐ = log((1+iᵐ)/(1+īᵐ))`). -/
theorem friedman_condition {i ib ibm : ℝ} (hi : 0 < 1 + i) (hib : 0 < 1 + ib)
    (hibm : 0 < 1 + ibm) :
    Real.log ((1 + i) / (1 + ib)) =
      Real.log ((1 + i) / (1 + ibm)) + Real.log ((1 + ibm) / (1 + ib)) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp

end Woodford.StabilizationWelfare.Transactions
