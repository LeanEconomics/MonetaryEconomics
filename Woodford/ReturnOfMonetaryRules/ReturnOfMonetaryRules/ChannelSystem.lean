/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.CDF
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Overnight interest rates under a channel system

Woodford (2003), *Interest and Prices*, Chapter 1, §3.1–3.2, pp. 25–33.

Under a channel system the central bank lends overnight balances at `i^l = ī + δ` and pays
`i^d = ī − δ` on deposits. Following Woodford (2001c) the interbank market clears at
(3.1), p. 27,

  `i = i^d + F(−S/σ) (i^l − i^d)`,

where `S` is the aggregate supply of clearing balances, `σ > 0` measures payment uncertainty and
`F` is a cumulative distribution function.

**Choice of `F`.** The book describes `F` (p. 27) only as a function that "increases
monotonically from 0 to 1". We formalise exactly that as `IsCDF F` (monotone, limit `0` at `−∞`
and `1` at `+∞`) and show (`isCDF_cdf`, `exists_measure_of_isCDF`) that the right-continuous
functions with this property are precisely the Mathlib CDFs `ProbabilityTheory.cdf μ` of
probability measures `μ` on `ℝ`. The theorems use only the property each needs (often merely
monotonicity and `0 ≤ F ≤ 1`, which `IsCDF` implies: `IsCDF.nonneg`, `IsCDF.le_one`), and the
`cdf_*` corollaries specialise them to a genuine probability distribution.

The text does not derive (3.1) from a bank's reserve-management problem; it cites Woodford
(2001c) for that model, so no derivation is formalised here.

## Main results

* `rate_mem_channel`: `i^d ≤ i ≤ i^l` (p. 28).
* `rate_antitone`, `rate_strictAnti`: the rate is non-increasing in supply, strictly decreasing
  when `F` is strictly increasing (p. 28).
* `rate_eq_target_iff`: at the channel midpoint, `i = ī ↔ F(−S/σ) = 1/2`.
* `exists_eq_half`, `existsUnique_target_supply`, `target_supply_iff`: (3.2), the unique supply
  hitting the target is `S = −F⁻¹(1/2) σ` (IVT for existence).
* `target_supply_set_indep`: the target supply does not depend on `ī` (p. 28).
* `rate_shift_channel`: moving the channel moves the rate one-for-one with no change in supply.
* `rate_noClearing`: with no clearing demand (`F` the CDF of the point mass at `0`), `i = i^d`
  for every positive supply (p. 32).
-/

namespace Woodford.ReturnOfMonetaryRules.ChannelSystem

open Filter Topology MeasureTheory ProbabilityTheory

/-- Woodford (2003), eq. (3.1), p. 27: the market-clearing overnight rate
`i = i^d + F(−S/σ)(i^l − i^d)` given deposit rate `iD`, lending rate `iL`, uncertainty `σ` and
supply of clearing balances `S`. -/
noncomputable def rate (F : ℝ → ℝ) (iD iL σ S : ℝ) : ℝ := iD + F (-S / σ) * (iL - iD)

/-- Woodford (2003), p. 27: `F` is a cumulative distribution function in the book's sense, a
monotone function rising from `0` (at `−∞`) to `1` (at `+∞`). -/
def IsCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1)

/-- Woodford (2003), p. 27: a CDF in the sense of `IsCDF` is nonnegative. -/
theorem IsCDF.nonneg {F : ℝ → ℝ} (hF : IsCDF F) (x : ℝ) : 0 ≤ F x :=
  le_of_tendsto hF.2.1 (eventually_atBot.2 ⟨x, fun _ hy => hF.1 hy⟩)

/-- Woodford (2003), p. 27: a CDF in the sense of `IsCDF` is at most one. -/
theorem IsCDF.le_one {F : ℝ → ℝ} (hF : IsCDF F) (x : ℝ) : F x ≤ 1 :=
  ge_of_tendsto hF.2.2 (eventually_atTop.2 ⟨x, fun _ hy => hF.1 hy⟩)

/-- Woodford (2003), p. 27: the CDF of a measure on `ℝ` (Mathlib `ProbabilityTheory.cdf`) is a
CDF in the book's sense. -/
theorem isCDF_cdf (μ : Measure ℝ) : IsCDF (cdf μ) :=
  ⟨monotone_cdf μ, tendsto_cdf_atBot μ, tendsto_cdf_atTop μ⟩

/-- Woodford (2003), p. 27: conversely, every right-continuous `F` with `IsCDF F` is the CDF of a
probability measure on `ℝ`, so `IsCDF` plus right-continuity is exactly "the CDF of a
probability distribution of payment shocks". -/
theorem exists_measure_of_isCDF {F : ℝ → ℝ} (hF : IsCDF F)
    (hr : ∀ x, ContinuousWithinAt F (Set.Ici x) x) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ⇑(cdf μ) = F := by
  let f : StieltjesFunction ℝ := ⟨F, hF.1, hr⟩
  have h0 : Tendsto f atBot (𝓝 0) := hF.2.1
  have h1 : Tendsto f atTop (𝓝 1) := hF.2.2
  exact ⟨f.measure, f.isProbabilityMeasure h0 h1,
    congrArg (fun g : StieltjesFunction ℝ => ⇑g) (cdf_measure_stieltjesFunction f h0 h1)⟩

/-! ### The rate stays in the channel and falls with supply -/

/-- Woodford (2003), p. 28: the market overnight rate lies in the channel, `i^d ≤ i ≤ i^l`,
for any `F` with values in `[0, 1]`. -/
theorem rate_mem_channel {F : ℝ → ℝ} (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    {iD iL : ℝ} (h : iD ≤ iL) (σ S : ℝ) :
    iD ≤ rate F iD iL σ S ∧ rate F iD iL σ S ≤ iL := by
  unfold rate
  have hd : 0 ≤ iL - iD := sub_nonneg.mpr h
  constructor
  · nlinarith [hF0 (-S / σ)]
  · nlinarith [hF1 (-S / σ)]

/-- Woodford (2003), p. 28: the overnight rate is a non-increasing function of the supply of
clearing balances (`σ > 0`, `F` monotone, `i^d ≤ i^l`). -/
theorem rate_antitone {F : ℝ → ℝ} (hF : Monotone F) {iD iL σ : ℝ} (h : iD ≤ iL)
    (hσ : 0 < σ) : Antitone (fun S => rate F iD iL σ S) := by
  intro S₁ S₂ hS
  have hx : -S₂ / σ ≤ -S₁ / σ := div_le_div_of_nonneg_right (by linarith) hσ.le
  have := hF hx
  simp only [rate]
  nlinarith [sub_nonneg.mpr h]

/-- Woodford (2003), p. 28: the overnight rate is strictly decreasing in supply when `F` is
strictly increasing and the channel has positive width. -/
theorem rate_strictAnti {F : ℝ → ℝ} (hF : StrictMono F) {iD iL σ : ℝ} (h : iD < iL)
    (hσ : 0 < σ) : StrictAnti (fun S => rate F iD iL σ S) := by
  intro S₁ S₂ hS
  have hx : -S₂ / σ < -S₁ / σ := div_lt_div_of_pos_right (by linarith) hσ
  have := hF hx
  simp only [rate]
  nlinarith [sub_pos.mpr h]

/-- Woodford (2003), p. 28 (CDF form): for the CDF of any measure `μ` the rate lies in the
channel. -/
theorem cdf_rate_mem_channel (μ : Measure ℝ) {iD iL : ℝ} (h : iD ≤ iL) (σ S : ℝ) :
    iD ≤ rate (cdf μ) iD iL σ S ∧ rate (cdf μ) iD iL σ S ≤ iL :=
  rate_mem_channel (cdf_nonneg μ) (cdf_le_one μ) h σ S

/-- Woodford (2003), p. 28 (CDF form): for the CDF of any measure `μ` the rate is non-increasing
in supply. -/
theorem cdf_rate_antitone (μ : Measure ℝ) {iD iL σ : ℝ} (h : iD ≤ iL) (hσ : 0 < σ) :
    Antitone (fun S => rate (cdf μ) iD iL σ S) :=
  rate_antitone (monotone_cdf μ) h hσ

/-! ### Hitting the target: equation (3.2) -/

/-- Woodford (2003), p. 27: with `i^l = ī + δ`, `i^d = ī − δ`, the rate is
`ī − δ + 2δ F(−S/σ)`. -/
theorem rate_channel (F : ℝ → ℝ) (ibar δ σ S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar - δ + 2 * δ * F (-S / σ) := by
  unfold rate; ring

/-- Woodford (2003), p. 28: with a symmetric channel of half-width `δ > 0` around the target `ī`,
the market rate equals the target exactly when `F(−S/σ) = 1/2`. -/
theorem rate_eq_target_iff (F : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (ibar σ S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar ↔ F (-S / σ) = 1 / 2 := by
  rw [rate_channel]
  constructor
  · intro h
    have : δ * (2 * F (-S / σ) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hδ.ne'
    · linarith
  · intro h
    rw [h]; ring

/-- Woodford (2003), p. 28: a continuous CDF takes the value `1/2` (intermediate value theorem
and the limits `0`, `1`), so `F⁻¹(1/2)` in (3.2) exists. -/
theorem exists_eq_half {F : ℝ → ℝ} (hF : IsCDF F) (hc : Continuous F) : ∃ x, F x = 1 / 2 := by
  obtain ⟨a, ha⟩ := (hF.2.1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  obtain ⟨b, hb⟩ := (hF.2.2.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))).exists
  exact intermediate_value_univ₂ hc continuous_const ha.le hb.le

/-- Woodford (2003), eq. (3.2), p. 28: if `F` is strictly increasing with `F x₀ = 1/2`
(`x₀ = F⁻¹(1/2)`), the rate equals the target `ī` if and only if `S = −x₀ σ`. -/
theorem target_supply_iff {F : ℝ → ℝ} (hF : StrictMono F) {x₀ : ℝ} (hx₀ : F x₀ = 1 / 2)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (ibar S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar ↔ S = -x₀ * σ := by
  rw [rate_eq_target_iff F hδ, ← hx₀, hF.injective.eq_iff]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]; field_simp

/-- Woodford (2003), eq. (3.2), p. 28: for a continuous, strictly increasing CDF there is exactly
one supply of clearing balances at which the overnight rate equals the target. -/
theorem existsUnique_target_supply {F : ℝ → ℝ} (hF : IsCDF F) (hc : Continuous F)
    (hs : StrictMono F) {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (ibar : ℝ) :
    ∃! S, rate F (ibar - δ) (ibar + δ) σ S = ibar := by
  obtain ⟨x₀, hx₀⟩ := exists_eq_half hF hc
  refine ⟨-x₀ * σ, (target_supply_iff hs hx₀ hδ hσ ibar _).mpr rfl, fun S hS => ?_⟩
  exact (target_supply_iff hs hx₀ hδ hσ ibar S).mp hS

/-- Woodford (2003), p. 28: the supply of clearing balances needed to hit the target is
"unrelated to changes in the target level of interest rates": the set of target-hitting supplies
is the same for every target `ī` (no hypothesis on `F` is needed). -/
theorem target_supply_set_indep (F : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (σ ibar₁ ibar₂ : ℝ) :
    {S | rate F (ibar₁ - δ) (ibar₁ + δ) σ S = ibar₁} =
      {S | rate F (ibar₂ - δ) (ibar₂ + δ) σ S = ibar₂} := by
  ext S
  simp only [Set.mem_ofPred_eq, rate_eq_target_iff F hδ]

/-- Woodford (2003), p. 28: if payment shocks are symmetric, `F 0 = 1/2`, the target supply is
`S = 0` whatever the degree of uncertainty `σ > 0`. -/
theorem target_supply_symmetric {F : ℝ → ℝ} (hF : StrictMono F) (h0 : F 0 = 1 / 2)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (ibar S : ℝ) :
    rate F (ibar - δ) (ibar + δ) σ S = ibar ↔ S = 0 := by
  rw [target_supply_iff hF h0 hδ hσ]
  simp

/-- Woodford (2003), p. 28: changes in the level of overnight rates are brought about by shifting
the deposit and lending rates; a shift of the channel by `Δ` moves the market rate by exactly `Δ`
at an unchanged supply of clearing balances. -/
theorem rate_shift_channel (F : ℝ → ℝ) (iD iL σ S Δ : ℝ) :
    rate F (iD + Δ) (iL + Δ) σ S = rate F iD iL σ S + Δ := by
  unfold rate; ring

/-! ### No clearing demand (p. 32) -/

/-- Woodford (2003), p. 32: with no clearing demand the payment shock is degenerate at `0`; its
CDF vanishes at every negative argument. -/
theorem cdf_dirac_zero_of_neg {x : ℝ} (hx : x < 0) : cdf (Measure.dirac (0 : ℝ)) x = 0 := by
  have hm : (0 : ℝ) ∉ Set.Iic x := by simpa using hx
  rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic,
    Set.indicator_of_notMem hm]
  simp

/-- Woodford (2003), p. 32: with no clearing demand, (3.1) "reduces to `i = i^d`" for every
positive supply of central-bank balances (and every `σ > 0`). -/
theorem rate_noClearing {S σ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (iD iL : ℝ) :
    rate (cdf (Measure.dirac (0 : ℝ))) iD iL σ S = iD := by
  have hx : -S / σ < 0 := div_neg_of_neg_of_pos (by linarith) hσ
  simp [rate, cdf_dirac_zero_of_neg hx]

/-- Woodford (2003), pp. 32–33: with no clearing demand, variations in a positive supply of
central-bank balances have no effect at all on the overnight rate. -/
theorem rate_noClearing_indep {S₁ S₂ σ : ℝ} (h₁ : 0 < S₁) (h₂ : 0 < S₂) (hσ : 0 < σ)
    (iD iL : ℝ) :
    rate (cdf (Measure.dirac (0 : ℝ))) iD iL σ S₁ =
      rate (cdf (Measure.dirac (0 : ℝ))) iD iL σ S₂ := by
  rw [rate_noClearing h₁ hσ, rate_noClearing h₂ hσ]

end Woodford.ReturnOfMonetaryRules.ChannelSystem
