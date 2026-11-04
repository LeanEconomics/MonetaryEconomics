/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasLinks
import IntertemporalModel.TidyR6MeasLinearIRF

/-!
# Passive fiscal policy, stimulus neutrality, credible reforms and Woodford's sunspots on a
probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, p. 39 (passive fiscal
policy), p. 42 (a credible reform with deficits), p. 50 (stimulus under perfect foresight) and
p. 33 against Woodford (2003), Proposition 2.5 (the general sunspot family), on a probability
space (`MeasExpectationSystem`): the restatements of `LinearFTMP.passive_valuation_holds`,
`LinearFTMP.passive_any_innovation`, `FiscalMonetary.pf_stimulus_neutral`,
`FiscalMonetary.reform_with_deficits` and `Links.sunspot_fisher`, `Links.sunspotPrice_injective`.

## Main results

* `mPassiveShock`, `mPassive_valuation_holds`, `mPassive_any_innovation`: under passive fiscal
  policy every shock is an equilibrium inflation innovation, almost surely.
* `mStimulus_neutral_no_news`: with no fiscal news at any date, a rearrangement of surpluses with
  the same initial present value and target leaves the whole price path unchanged almost surely;
  `mPf_stimulus_neutral`: in particular with full information at every date (perfect foresight).
* `mReform_with_deficits`, `mReform_exists`: in the `±1` coin economy, a surplus revision that is a
  deficit at the first two dates but has positive present value produces unexpected disinflation
  in every equilibrium, on an event of positive probability.
* Woodford's general sunspot family: `mKexp`, `mGrossInfl`, `mSunspotPrice`, `MFisherW`,
  `mSunspotPrice_pos`, `mSunspot_fisher` (every `ν < 1` with `u_c(1 − ν) ≥ m > 0` gives a solution
  of the exact Fisher equation (1.21) almost surely), `mSunspot_injective` (distinct
  martingale-difference sunspots give price paths that differ with positive probability),
  `mFisherW_one_iff` (with `u_c ≡ 1` it is the bond-pricing condition (2.3)).
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasRestate

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR5MeasLinear ExpectationsMeasureIID

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Passive fiscal policy (p. 39) -/

/-- Cochrane (2023), p. 39, on a probability space: the passive fiscal shock
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` "in response to whatever inflation happens".
Restates `LinearFTMP.passiveShock` on a genuine probability space. -/
noncomputable def mPassiveShock (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => -S.innov t (π (t + 1))

/-- Cochrane (2023), p. 39, on a probability space: under passive fiscal policy the valuation
equation holds for every inflation path satisfying the Fisher equation almost surely.
Restates `LinearFTMP.passive_valuation_holds` on a genuine probability space. -/
theorem mPassive_valuation_holds {i π : ℕ → Ω → ℝ} (hfis : ∀ t, i t =ᵐ[S.μ] S.E t (π (t + 1))) :
    MPegModel S i (mPassiveShock S π) π := fun t =>
  ⟨hfis t, Eventually.of_forall fun ω => by
    change S.innov t (π (t + 1)) ω = (-(-S.innov t (π (t + 1)))) ω
    rw [neg_neg]⟩

/-- Cochrane (2023), p. 39 ("The bank threatens hyperinflation for any but one value of
unexpected inflation"), on a probability space: with passive fiscal policy, for every adapted
integrable rate path, every shock `ν` and every integrable `π_0` known at `0`, the path
`π_{t+1} = i_t + ν_{t+1}` is adapted and integrable, satisfies the model with the passive fiscal
response, and has `ΔE_{t+1} π_{t+1} = ν_{t+1}` almost surely.
Restates `LinearFTMP.passive_any_innovation` on a genuine probability space. -/
theorem mPassive_any_innovation {i ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hii : ∀ t, Integrable (i t) S.μ) (hν : MIsShock S ν)
    (h0 : StronglyMeasurable[S.𝓕 0] π0) (h0i : Integrable π0 S.μ) :
    StronglyAdapted S.𝓕 (LinearFTMP.pegSol i (fun t => -ν t) π0) ∧
      (∀ t, Integrable (LinearFTMP.pegSol i (fun t => -ν t) π0 t) S.μ) ∧
      MPegModel S i (mPassiveShock S (LinearFTMP.pegSol i (fun t => -ν t) π0))
        (LinearFTMP.pegSol i (fun t => -ν t) π0) ∧
      ∀ t, S.innov t (LinearFTMP.pegSol i (fun t => -ν t) π0 (t + 1)) =ᵐ[S.μ] ν (t + 1) := by
  have hs : MIsShock S (fun t => -ν t) := ⟨fun t => (hν.1 t).neg, fun t => (hν.2.1 t).neg,
    fun t => by
      filter_upwards [condExp_neg (μ := S.μ) (ν (t + 1)) (S.𝓕 t), hν.2.2 t] with ω h1 h2
      have h1' : S.E t (-ν (t + 1)) ω = -S.E t (ν (t + 1)) ω := h1
      change S.E t (-ν (t + 1)) ω = 0
      rw [h1', h2, Pi.zero_apply, neg_zero]⟩
  obtain ⟨⟨ha, hint, hm⟩, -⟩ := mPeg_linear_existsUnique S hia hii hs h0 h0i
  refine ⟨ha, hint, mPassive_valuation_holds S fun t => (hm t).1, fun t => ?_⟩
  filter_upwards [(hm t).2] with ω h
  rw [h]
  simp

/-! ### Stimulus with no fiscal news (p. 50) -/

variable {β : ℝ} {Bm1 : Ω → ℝ} {s s' B P B' P' i : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 50, on a probability space: in every equilibrium with `β > 0`, positive
present values and **no present-value news** at `t + 1`, `P_{t+1} = β(1 + i_t)P_t` almost
surely. -/
theorem mPrice_succ_no_news (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) (t : ℕ)
    (hn : S.innov t (S.forwardSol β s (t + 1)) =ᵐ[S.μ] 0) :
    P (t + 1) =ᵐ[S.μ] fun ω => β * (1 + i t ω) * P t ω := by
  have hk : S.E (t + 1) (S.forwardSol β s (t + 1)) = S.forwardSol β s (t + 1) :=
    S.E_E_self (t + 1) _
  filter_upwards [mPrice_succ S h t (hpv (t + 1)), mDebt_eq S hβ0 h t (hpv (t + 1)), hn,
    hpv (t + 1)] with ω h1 h2 h3 h4
  have h2' : B t ω = (1 + i t ω) * P t ω * (β * S.E t (S.forwardSol β s (t + 1)) ω) := h2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk, Pi.zero_apply] at h3
  have e : S.E t (S.forwardSol β s (t + 1)) ω = S.forwardSol β s (t + 1) ω := by linarith
  rw [h1, h2', e]
  have := h4.ne'
  field_simp

/-- Cochrane (2023), p. 50 ("borrow money, ... spend the money, repay the debt has no effect at
all"), on a probability space, the case in which it is true: two equilibria with the same
initial debt, the same target, the same initial present value almost surely, positive present
values and **no present-value news at any date** have the same price level almost surely at
every date (`β > 0`).
Generalises `FiscalMonetary.pf_stimulus_neutral`. -/
theorem mStimulus_neutral_no_news (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1 s' B' P' i)
    (hpv0 : S.forwardSol β s' 0 =ᵐ[S.μ] S.forwardSol β s 0)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (hpv' : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s' t ω)
    (hn : ∀ t, S.innov t (S.forwardSol β s (t + 1)) =ᵐ[S.μ] 0)
    (hn' : ∀ t, S.innov t (S.forwardSol β s' (t + 1)) =ᵐ[S.μ] 0) (t : ℕ) :
    P' t =ᵐ[S.μ] P t := by
  induction t with
  | zero =>
    filter_upwards [mPrice_zero S h' (hpv' 0), mPrice_zero S h (hpv 0), hpv0] with ω h1 h2 h3
    rw [h1, h2, h3]
  | succ t ih =>
    filter_upwards [mPrice_succ_no_news S hβ0 h' hpv' t (hn' t),
      mPrice_succ_no_news S hβ0 h hpv t (hn t), ih] with ω h1 h2 h3
    rw [h1, h2, h3]

/-- Cochrane (2023), p. 50, **perfect foresight on a probability space** (the restatement of
`FiscalMonetary.pf_stimulus_neutral`): when everything is known from date `0` on (the
filtration is the full σ-algebra at every date) there is no news, so two equilibria with the
same initial debt, target and initial present value, and positive present values, have the
same price path almost surely. -/
theorem mPf_stimulus_neutral (hfull : ∀ t, S.𝓕 t = (inferInstance : MeasurableSpace Ω))
    (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) (h' : MEquilibrium S β Bm1 s' B' P' i)
    (hpv0 : S.forwardSol β s' 0 =ᵐ[S.μ] S.forwardSol β s 0)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (hpv' : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s' t ω) (t : ℕ) : P' t =ᵐ[S.μ] P t := by
  have hnews : ∀ (x : ℕ → Ω → ℝ) (t : ℕ), S.innov t (S.forwardSol β x (t + 1)) =ᵐ[S.μ] 0 :=
    fun x t => by
      have hle : S.𝓕 (t + 1) ≤ S.𝓕 t := by rw [hfull, hfull]
      have hm : StronglyMeasurable[S.𝓕 t] (S.forwardSol β x (t + 1)) :=
        (S.stronglyMeasurable_E (t + 1) _).mono hle
      rw [TidyR6MeasLinearIRF.innov_known S hm (S.integrable_E _ _)]
  exact mStimulus_neutral_no_news S hβ0 h h' hpv0 hpv hpv' (hnews s) (hnews s') t

/-! ### A credible reform with deficits (p. 42), in the `±1` coin economy -/

/-- Cochrane (2023), Ch. 2, p. 29: the fair coin lands on `1` or `−1`. -/
theorem coin_pm_one : ∀ᵐ x ∂(coin : Measure ℝ), x = 1 ∨ x = -1 := by
  change ∀ᵐ x ∂coinMeasure, x = 1 ∨ x = -1
  rw [ae_iff]
  have e : {x : ℝ | ¬ (x = 1 ∨ x = -1)} = ({1, -1} : Set ℝ)ᶜ := by
    ext x
    simp
  rw [e]
  simp [coinMeasure]

/-- Cochrane (2023), p. 42: the event "the date-`1` coin is heads" has positive probability. -/
theorem heads_pos : ¬ ∀ᵐ ω ∂(iidSystem coin).μ, TidyR6MeasLinks.cc (ω 1) ≠ 1 := by
  intro h
  have hpm : ∀ᵐ ω ∂(iidSystem coin).μ, ω 1 = 1 ∨ ω 1 = -1 :=
    (measurePreserving_eval_infinitePi (fun _ => (coin : Measure ℝ)) 1
      ).quasiMeasurePreserving.ae coin_pm_one
  have hneg : (fun ω : ℕ → ℝ => TidyR6MeasLinks.cc (ω 1)) =ᵐ[(iidSystem coin).μ]
      fun _ => -1 := by
    filter_upwards [h, hpm] with ω h1 h2
    rcases h2 with h2 | h2
    · exact absurd (by rw [h2]; exact TidyR6MeasLinks.cc_one_neg.1) h1
    · rw [h2]
      exact TidyR6MeasLinks.cc_one_neg.2
  have h1 : ∫ ω, TidyR6MeasLinks.cc (ω 1) ∂(iidSystem coin).μ = 0 := by
    rw [integral_shock_fun coin 1 TidyR6MeasLinks.measurable_cc, integral_coin,
      TidyR6MeasLinks.cc_one_neg.1, TidyR6MeasLinks.cc_one_neg.2]
    norm_num
  rw [integral_congr_ae hneg] at h1
  simp at h1

/-- Cochrane (2023), p. 42: the surplus revision `D_0 = 0`, `D_{k+1} = d_k`. -/
def dShift (d : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else d (k - 1)

/-- Cochrane (2023), p. 42: surpluses `s_k = 1 + D_k c(ε_1)`, revised by the date-`1` coin. -/
noncomputable def sReform (d : ℕ → ℝ) : ℕ → (ℕ → ℝ) → ℝ :=
  fun k ω => 1 + dShift d k * TidyR6MeasLinks.cc (ω 1)

/-- Cochrane (2023), p. 42, "a credible fiscal reform can coexist with ongoing or even larger
short-term deficits, yet produce a disinflation", **on a genuine probability space** (the
i.i.d. `±1` coin, `0 ≤ β < 1`): for a bounded revision `d` with `d_0 < 0`, `d_1 < 0` and
`∑ βʲ d_j > 0`, the surpluses `sReform d` have surplus news `d_0 c(ε_1)`, `d_1 c(ε_1)` at dates
`1`, `2` (deficits where the coin is heads, an event of positive probability) and present-value
news `(∑ βʲ d_j) c(ε_1)` (positive there), and in every equilibrium the unexpected inflation
satisfies `(B_0/P_0) ΔE_1(P_0/P_1) = (∑ βʲ d_j) c(ε_1)` almost surely: unexpected disinflation
where the deficits occur.
Restates `FiscalMonetary.reform_with_deficits` on a genuine probability space. -/
theorem mReform_with_deficits {β Dm : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {d : ℕ → ℝ}
    (hdb : ∀ k, |d k| ≤ Dm) :
    (iidSystem coin).innov 0 (sReform d 1) =ᵐ[(iidSystem coin).μ]
        d 0 • (fun ω => TidyR6MeasLinks.cc (ω 1)) ∧
      (iidSystem coin).innov 0 (sReform d 2) =ᵐ[(iidSystem coin).μ]
        d 1 • (fun ω => TidyR6MeasLinks.cc (ω 1)) ∧
      mFiscShock (iidSystem coin) β (sReform d) 1 =ᵐ[(iidSystem coin).μ]
        (∑' j, β ^ j * d j) • (fun ω => TidyR6MeasLinks.cc (ω 1)) ∧
      (∀ {Bm1 : (ℕ → ℝ) → ℝ} {B P i : ℕ → (ℕ → ℝ) → ℝ},
        MEquilibrium (iidSystem coin) β Bm1 (sReform d) B P i →
        (fun ω => B 0 ω / P 0 ω * (iidSystem coin).innov 0 (fun ω => P 0 ω / P 1 ω) ω)
          =ᵐ[(iidSystem coin).μ] (∑' j, β ^ j * d j) • (fun ω => TidyR6MeasLinks.cc (ω 1))) ∧
      ¬ ∀ᵐ ω ∂(iidSystem coin).μ, TidyR6MeasLinks.cc (ω 1) ≠ 1 := by
  set CS := iidSystem coin
  set x : (ℕ → ℝ) → ℝ := fun ω => TidyR6MeasLinks.cc (ω 1) with hx
  have hxm : StronglyMeasurable[CS.𝓕 (0 + 1)] x :=
    (TidyR6MeasLinks.measurable_cc_shock (s := 1) (t := 0 + 1) le_rfl).stronglyMeasurable
  have hxi : Integrable x CS.μ :=
    Integrable.of_bound ((hxm.mono (CS.𝓕.le _)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact TidyR6MeasLinks.abs_cc_le _)
  have hx0 : CS.E 0 x =ᵐ[CS.μ] 0 := by
    have h := TidyR6MeasLinks.E_cc 0 0 1
    have e : (fun ω : ℕ → ℝ => (0 : ℝ) + 1 * TidyR6MeasLinks.cc (ω (0 + 1))) = x := by
      funext ω
      simp [hx]
    rw [e] at h
    exact h
  have hnews := TidyR6MeasLinearIRF.mInnov_of_news CS hxm hxi hx0 0
  simp only [↓reduceIte] at hnews
  have hDb : ∀ k, |dShift d k| ≤ |Dm| := fun k => by
    unfold dShift
    split_ifs
    · simp
    · exact (hdb _).trans (le_abs_self _)
  have hsk : ∀ k, CS.innov 0 (sReform d k) =ᵐ[CS.μ] dShift d k • x := fun k => by
    have e : sReform d k = (fun _ => (1 : ℝ)) + dShift d k • x := by
      funext ω
      simp [sReform, hx]
    rw [e]
    filter_upwards [TidyR6MeasLinearIRF.innov_add' CS (integrable_const (1 : ℝ))
      (hxi.smul (dShift d k)) 0,
      TidyR6MeasLinearIRF.innov_smul' CS (dShift d k) x 0, hnews] with ω h1 h2 h3
    rw [h1, Pi.add_apply, TidyR6MeasLinearIRF.innov_known CS stronglyMeasurable_const
      (integrable_const 1), h2, Pi.smul_apply, h3, Pi.zero_apply, zero_add]
    rfl
  have hfs := TidyR6MeasLinearIRF.mPvNews_of_news CS hβ0 hβ1 (c := fun _ => 1) (C := 1)
    (D := dShift d) (Dm := |Dm|) (fun _ => by simp) hDb hxm hxi hx0 0
  simp only [↓reduceIte] at hfs
  have hsum : (∑' k, β ^ k * dShift d (0 + 1 + k)) = ∑' j, β ^ j * d j := by
    refine tsum_congr fun k => ?_
    simp [dShift]
  rw [hsum] at hfs
  have hfs' : mFiscShock CS β (sReform d) 1 =ᵐ[CS.μ] (∑' j, β ^ j * d j) • x := by
    have e : sReform d = fun k ω => (fun _ => (1 : ℝ)) k + dShift d k * x ω := rfl
    rw [e]
    exact hfs
  refine ⟨(hsk 1).trans (Eventually.of_forall fun ω => by simp [dShift]),
    (hsk 2).trans (Eventually.of_forall fun ω => by simp [dShift]), hfs',
    fun h => (mUnexpected_inflation CS h 0).trans hfs', heads_pos⟩

/-- Cochrane (2023), p. 42: such a revision exists for every `0 < β < 1`
(`FiscalMonetary.reform_with_deficits`, with an explicit bound). -/
theorem mReform_exists {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ d : ℕ → ℝ, (∀ k, |d k| ≤ 1 + 3 / β ^ 2) ∧ d 0 < 0 ∧ d 1 < 0 ∧
      0 < ∑' j, β ^ j * d j := by
  set d : ℕ → ℝ := fun j => if j = 2 then 3 / β ^ 2 else if j < 2 then -1 else 0 with hd
  have hz : ∀ j ∉ Finset.range 3, β ^ j * d j = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [hd, show j ≠ 2 by omega, show ¬ j < 2 by omega, ↓reduceIte, mul_zero]
  have h3 : 0 ≤ 3 / β ^ 2 := by positivity
  refine ⟨d, fun k => ?_, by simp [hd], by simp [hd], ?_⟩
  · simp only [hd]
    split_ifs
    · rw [abs_of_nonneg h3]
      linarith
    · norm_num
      linarith
    · simp
      linarith
  · rw [tsum_eq_sum hz]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hd]
    norm_num
    field_simp
    linarith

/-! ### Woodford's general sunspot family (Proposition 2.5) -/

/-- Woodford (2003), §A.6, p. 639 (restated from `Links.Kexp`) on a probability space, used for
Cochrane (2023), p. 33: `K_t = E_t[u_{c,t+1}(1 − ν_{t+1})]`. -/
noncomputable def mKexp (uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  S.E t (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639 (restated from `Links.grossInfl`), used for Cochrane (2023),
p. 33: gross inflation `Π_{t+1} = β(1 + i_t)K_t/(u_{c,t}(1 − ν_{t+1}))`. -/
noncomputable def mGrossInfl (β : ℝ) (i uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * (1 + i t ω) * mKexp S uc ν t ω / (uc t ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639 (restated from `Links.sunspotPrice`), used for Cochrane (2023),
p. 33: the sunspot price path `P_{t+1} = P_t Π_{t+1}`. -/
noncomputable def mSunspotPrice (β : ℝ) (P0 : Ω → ℝ) (i uc ν : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => P0
  | t + 1 => fun ω => mSunspotPrice β P0 i uc ν t ω * mGrossInfl S β i uc ν t ω

/-- Woodford (2003), eq. (1.21), p. 71 (restated from `Links.FisherExactW`) on a probability
space, used for Cochrane (2023), eq. (2.3): the exact Fisher equation
`1 + i_t = β⁻¹ {E_t[u_{c,t+1} P_t/(u_{c,t} P_{t+1})]}⁻¹` almost surely. -/
def MFisherW (β : ℝ) (i uc P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, 1 + i t ω =
    β⁻¹ * (S.E t (fun ω => uc (t + 1) ω * P t ω / (uc t ω * P (t + 1) ω)) ω)⁻¹

variable {m : ℝ} {P0 : Ω → ℝ} {uc ν ν' : ℕ → Ω → ℝ}

/-- Woodford (2003), §A.6, p. 639 (restated): `u_c(1 − ν) ≥ m` gives `K_t ≥ m` almost surely
(integrable `u_{c,t+1}(1 − ν_{t+1})`).
Restates `Links.Kexp_ge` on a genuine probability space. -/
theorem mKexp_ge (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω))
    (hint : ∀ t, Integrable (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω)) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, m ≤ mKexp S uc ν t ω := by
  have h := S.E_mono (integrable_const m) (hint t) (Eventually.of_forall fun ω => hm (t + 1) ω) t
  rw [S.E_const] at h
  exact h

/-- Woodford (2003), §A.6, p. 639 (restated): the sunspot price path is positive almost surely
(`β > 0`, `m > 0`, `P_0 > 0`, `1 + i > 0`, `u_c > 0`, `ν < 1`).
Restates `Links.sunspotPrice_pos` on a genuine probability space. -/
theorem mSunspotPrice_pos (hβ : 0 < β) (hm0 : 0 < m) (hP0 : ∀ ω, 0 < P0 ω)
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω))
    (hint : ∀ t, Integrable (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω)) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < mSunspotPrice S β P0 i uc ν t ω := by
  induction t with
  | zero => exact Eventually.of_forall hP0
  | succ t ih =>
    filter_upwards [ih, mKexp_ge S hm hint t] with ω h1 h2
    change 0 < mSunspotPrice S β P0 i uc ν t ω *
      (β * (1 + i t ω) * mKexp S uc ν t ω / (uc t ω * (1 - ν (t + 1) ω)))
    have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
    have := hi t ω
    have := huc t ω
    have h4 : 0 < mKexp S uc ν t ω := lt_of_lt_of_le hm0 h2
    positivity

/-- Woodford (2003), Proposition 2.5 and §A.6, pp. 87, 639 (restated from
`Links.sunspot_fisher`) **on a probability space**, used for Cochrane (2023), p. 33: for an
adapted rate target with `1 + i > 0` and integrable bond price, `u_c > 0` and any `ν < 1` with
`u_c(1 − ν) ≥ m > 0` and `u_{c,t+1}(1 − ν_{t+1})` integrable, the sunspot path
satisfies the exact Fisher equation (1.21) almost surely at every date. -/
theorem mSunspot_fisher (hβ : 0 < β) (hm0 : 0 < m) (hP0 : ∀ ω, 0 < P0 ω)
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t ω, 0 < 1 + i t ω)
    (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ) (huc : ∀ t ω, 0 < uc t ω)
    (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω))
    (hint : ∀ t, Integrable (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω)) S.μ) (t : ℕ) :
    MFisherW S β i uc (mSunspotPrice S β P0 i uc ν) t := by
  set Z : Ω → ℝ := fun ω => (β * (1 + i t ω) * mKexp S uc ν t ω)⁻¹ with hZ
  set X : Ω → ℝ := fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω) with hX
  have hKm : StronglyMeasurable[S.𝓕 t] (mKexp S uc ν t) := S.stronglyMeasurable_E t _
  have hZm : StronglyMeasurable[S.𝓕 t] Z :=
    (((measurable_const.mul ((hia t).measurable.const_add 1)).mul hKm.measurable).inv
      ).stronglyMeasurable
  have hKpos : ∀ᵐ ω ∂S.μ, 0 < mKexp S uc ν t ω :=
    (mKexp_ge S hm hint t).mono fun ω h => lt_of_lt_of_le hm0 h
  have hZ0 : ∀ᵐ ω ∂S.μ, 0 ≤ Z ω := hKpos.mono fun ω h => by
    simp only [hZ]
    have := hi t ω
    positivity
  have hX0 : ∀ᵐ ω ∂S.μ, 0 ≤ X ω :=
    Eventually.of_forall fun ω => hm0.le.trans (hm (t + 1) ω)
  have hZE : Integrable (fun ω => Z ω * S.E t X ω) S.μ := by
    refine ((hQi t).const_mul β⁻¹).congr ?_
    filter_upwards [hKpos] with ω h
    change β⁻¹ * (1 + i t ω)⁻¹ = (β * (1 + i t ω) * mKexp S uc ν t ω)⁻¹ * mKexp S uc ν t ω
    have := (hi t ω).ne'
    have := hβ.ne'
    have := h.ne'
    field_simp
  have hZX := (HouseholdMeasureTVC.integrable_mul_of_E hZm hZ0 (hint t) hX0 hZE).1
  have hpo := condExp_mul_of_stronglyMeasurable_left hZm hZX (hint t)
  have hratio : (fun ω => uc (t + 1) ω * mSunspotPrice S β P0 i uc ν t ω /
      (uc t ω * mSunspotPrice S β P0 i uc ν (t + 1) ω)) =ᵐ[S.μ] Z * X := by
    filter_upwards [mSunspotPrice_pos S hβ hm0 hP0 hi huc hν hm hint t, hKpos] with ω h1 h2
    change uc (t + 1) ω * mSunspotPrice S β P0 i uc ν t ω / (uc t ω *
      (mSunspotPrice S β P0 i uc ν t ω * (β * (1 + i t ω) * mKexp S uc ν t ω /
        (uc t ω * (1 - ν (t + 1) ω))))) = (β * (1 + i t ω) * mKexp S uc ν t ω)⁻¹ *
          (uc (t + 1) ω * (1 - ν (t + 1) ω))
    have h3 : 1 - ν (t + 1) ω ≠ 0 := by linarith [hν (t + 1) ω]
    have := (hi t ω).ne'
    have := (huc t ω).ne'
    have := h1.ne'
    have := h2.ne'
    have := hβ.ne'
    field_simp
  filter_upwards [S.E_congr hratio t, hpo, hKpos] with ω h1 h2 h3
  rw [h1]
  have h2' : S.E t (Z * X) ω = Z ω * S.E t X ω := h2
  rw [h2']
  change 1 + i t ω = β⁻¹ * ((β * (1 + i t ω) * mKexp S uc ν t ω)⁻¹ * mKexp S uc ν t ω)⁻¹
  have := (hi t ω).ne'
  have := hβ.ne'
  have := h3.ne'
  field_simp

/-- Woodford (2003), §A.6, p. 639 (restated from `Links.sunspotPrice_injective`) **on a
probability space**: under the hypotheses of `mSunspot_fisher` for two martingale-difference
sunspots `ν`, `ν'` (integrable, `E_t ν_{t+1} = 0` a.s.), if their price paths are equal almost
surely at every date then `ν_{t+1} = ν'_{t+1}` almost surely: distinct sunspots give price paths
that differ with positive probability. -/
theorem mSunspot_injective (hβ : 0 < β) (hm0 : 0 < m) (hP0 : ∀ ω, 0 < P0 ω)
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hν' : ∀ t ω, ν' t ω < 1) (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω))
    (hm' : ∀ t ω, m ≤ uc t ω * (1 - ν' t ω))
    (hint : ∀ t, Integrable (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω)) S.μ)
    (hint' : ∀ t, Integrable (fun ω => uc (t + 1) ω * (1 - ν' (t + 1) ω)) S.μ)
    (hνi : ∀ t, Integrable (ν (t + 1)) S.μ) (hνi' : ∀ t, Integrable (ν' (t + 1)) S.μ)
    (hmd : ∀ t, S.E t (ν (t + 1)) =ᵐ[S.μ] 0) (hmd' : ∀ t, S.E t (ν' (t + 1)) =ᵐ[S.μ] 0)
    (heq : ∀ t, mSunspotPrice S β P0 i uc ν t =ᵐ[S.μ] mSunspotPrice S β P0 i uc ν' t)
    (t : ℕ) : ν (t + 1) =ᵐ[S.μ] ν' (t + 1) := by
  set c : Ω → ℝ := fun ω => mKexp S uc ν' t ω / mKexp S uc ν t ω with hc
  have hcm : StronglyMeasurable[S.𝓕 t] c :=
    ((S.stronglyMeasurable_E t _).measurable.div
      (S.stronglyMeasurable_E t _).measurable).stronglyMeasurable
  have hrel : (fun ω => 1 - ν' (t + 1) ω) =ᵐ[S.μ] c * fun ω => 1 - ν (t + 1) ω := by
    filter_upwards [heq t, heq (t + 1), mSunspotPrice_pos S hβ hm0 hP0 hi huc hν hm hint t,
      mKexp_ge S hm hint t, mKexp_ge S hm' hint' t] with ω h0 h1 hP hK hK'
    change mSunspotPrice S β P0 i uc ν t ω * mGrossInfl S β i uc ν t ω =
      mSunspotPrice S β P0 i uc ν' t ω * mGrossInfl S β i uc ν' t ω at h1
    rw [← h0] at h1
    have hG := mul_left_cancel₀ hP.ne' h1
    simp only [mGrossInfl] at hG
    have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
    have h3' : 0 < 1 - ν' (t + 1) ω := by linarith [hν' (t + 1) ω]
    have := (hi t ω).ne'
    have := (huc t ω).ne'
    have := hβ.ne'
    have hKp := (lt_of_lt_of_le hm0 hK).ne'
    have hKp' := (lt_of_lt_of_le hm0 hK').ne'
    simp only [hc, Pi.mul_apply]
    field_simp at hG ⊢
    linear_combination hG
  have hone : ∀ μ' : ℕ → Ω → ℝ, Integrable (μ' (t + 1)) S.μ →
      S.E t (μ' (t + 1)) =ᵐ[S.μ] 0 →
      S.E t (fun ω => 1 - μ' (t + 1) ω) =ᵐ[S.μ] fun _ => 1 := fun μ' hi0 hμ => by
    have e : (fun ω => 1 - μ' (t + 1) ω) = (fun _ => (1 : ℝ)) - μ' (t + 1) := rfl
    rw [e]
    filter_upwards [S.E_sub (integrable_const 1) hi0 t, hμ] with ω h1 h2
    rw [h1, Pi.sub_apply, S.E_const, h2, Pi.zero_apply, sub_zero]
  have h1ν : Integrable (fun ω => 1 - ν (t + 1) ω) S.μ := (integrable_const 1).sub (hνi t)
  have h1ν' : Integrable (fun ω => 1 - ν' (t + 1) ω) S.μ := (integrable_const 1).sub (hνi' t)
  have hpo := condExp_mul_of_stronglyMeasurable_left hcm (h1ν'.congr hrel) h1ν
  have hc1 : c =ᵐ[S.μ] fun _ => 1 := by
    filter_upwards [S.E_congr hrel t, hpo, hone ν' (hνi' t) (hmd' t), hone ν (hνi t) (hmd t)]
      with ω h1 h2 h3 h4
    have h2' : S.E t (c * fun ω => 1 - ν (t + 1) ω) ω =
        c ω * S.E t (fun ω => 1 - ν (t + 1) ω) ω := h2
    rw [h3, h2', h4] at h1
    simp only [mul_one] at h1
    exact h1.symm
  filter_upwards [hrel, hc1] with ω h1 h2
  simp only [Pi.mul_apply, h2, one_mul] at h1
  linarith

/-- Woodford (2003), eq. (1.21), p. 71, with `u_c ≡ 1` (restated from `Links.fisher_iff_W`) on a
probability space: the exact Fisher equation is Cochrane's (2023) bond-pricing condition (2.3),
`1/(1 + i_t) = β E_t(P_t/P_{t+1})`, almost surely. -/
theorem mFisherW_one_iff {i P : ℕ → Ω → ℝ} (t : ℕ) :
    MFisherW S β i (fun _ _ => 1) P t ↔
      (fun ω => (1 + i t ω)⁻¹) =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω) := by
  have e : (fun ω => (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) (t + 1) ω * P t ω /
      ((fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t ω * P (t + 1) ω)) = fun ω => P t ω / P (t + 1) ω := by
    funext ω
    simp
  unfold MFisherW
  rw [e]
  refine ⟨fun h => h.mono fun ω hω => ?_, fun h => h.mono fun ω hω => ?_⟩
  · change (1 + i t ω)⁻¹ = β * S.E t (fun ω => P t ω / P (t + 1) ω) ω
    rw [hω, mul_inv, inv_inv, inv_inv]
  · have hω' : (1 + i t ω)⁻¹ = β * S.E t (fun ω => P t ω / P (t + 1) ω) ω := hω
    rw [← inv_inv (1 + i t ω), hω', mul_inv]

end Cochrane.IntertemporalModel.TidyR6MeasRestate
