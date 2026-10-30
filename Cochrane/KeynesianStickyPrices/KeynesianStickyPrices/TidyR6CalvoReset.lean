/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6HouseholdMeasure
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Calvo price setter: the reset-price problem and the cohort price index

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118 ("The Phillips
curve (5.2) comes from the first-order condition for monopolistically-competitive price setters,
facing ... a random probability of being allowed to change price"), and Chapter 17, p. 421 ("The
Calvo fairy").

A Calvo price setter allowed to reset at `t` chooses its log relative price `r` (known at `t`)
knowing that the price survives each further period with probability `α`, independently of
everything else. With the payoff weights `a_k`, `b_k ≥ 0` of date `t + k` (revenue valued at
marginal utility and disutility of production, both expressed relative to date-`t` prices), its
objective is `resetObj`, `E ∑_k (αβ)ᵏ(e^{(1−ε)r}a_k − e^{−ηr}b_k)` (elasticity `ε > 1`,
`η > ε − 1`).

## Main results

* `gRes_lt`: for `A, B > 0` the function `Ae^{(1−ε)r} − Be^{−ηr}` has the **unique global
  maximiser** `r* = log(ηB/((ε − 1)A))/(1 − ε + η)` (`rStar`): it is strictly increasing below
  and strictly decreasing above `r*`.
* `resetObj_eq`: the objective is `E[e^{(1−ε)r}E_tW_A − e^{−ηr}E_tW_B]` with
  `W_A = ∑_k (αβ)ᵏa_k`, `W_B = ∑_k (αβ)ᵏb_k`.
* `resetOpt_iff` (**necessity and sufficiency, among all bounded reset prices known at `t`**):
  `r` is optimal iff `r = r*(E_tW_A, E_tW_B)` almost surely, i.e. the first-order condition
  `(1 − ε + η)r = log(ηE_tW_B/((ε − 1)E_tW_A))`.
* `cohort_succ`, `cohort_one`, `index_eq_of_cohort`: the Calvo price index. With mass
  `(1 − α)α^{t−s}` of firms last resetting at `s ≤ t` (and `α^{t+1}` never resetting), the CES
  index `P_t^{1−ε}` of the cohorts satisfies `P_t^{1−ε} = αP_{t−1}^{1−ε} + (1 − α)P*_t^{1−ε}`, the
  masses sum to one, and in logs `1 = αe^{(ε−1)π_t} + (1 − α)e^{(1−ε)r_t}`.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6CalvoReset

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure

/-! ### The static reset problem -/

/-- Cochrane (2023), p. 118: the reset payoff `Ae^{(1−ε)r} − Be^{−ηr}`. -/
noncomputable def gRes (ε η A B r : ℝ) : ℝ := A * Real.exp ((1 - ε) * r) - B * Real.exp (-(η * r))

/-- Cochrane (2023), p. 118: the optimal reset price `r* = log(ηB/((ε − 1)A))/(1 − ε + η)`. -/
noncomputable def rStar (ε η A B : ℝ) : ℝ := Real.log (η * B / ((ε - 1) * A)) / (1 - ε + η)

/-- Cochrane (2023), p. 118: the derivative of the reset payoff. -/
theorem hasDerivAt_gRes (ε η A B r : ℝ) :
    HasDerivAt (gRes ε η A B)
      (A * (1 - ε) * Real.exp ((1 - ε) * r) + B * η * Real.exp (-(η * r))) r := by
  have h1 : HasDerivAt (fun r => Real.exp ((1 - ε) * r)) (Real.exp ((1 - ε) * r) * (1 - ε)) r :=
    ((hasDerivAt_id r).const_mul (1 - ε)).exp.congr_deriv (by simp)
  have h2 : HasDerivAt (fun r => Real.exp (-(η * r))) (Real.exp (-(η * r)) * (-η)) r :=
    (((hasDerivAt_id r).const_mul η).neg).exp.congr_deriv (by simp)
  exact ((h1.const_mul A).sub (h2.const_mul B)).congr_deriv (by ring)

/-- Cochrane (2023), p. 118: the sign of the derivative:
`g′(r) = e^{−ηr}(ηB − (ε − 1)Ae^{(1−ε+η)r})`. -/
theorem deriv_gRes_eq (ε η A B r : ℝ) :
    A * (1 - ε) * Real.exp ((1 - ε) * r) + B * η * Real.exp (-(η * r)) =
      Real.exp (-(η * r)) * (η * B - (ε - 1) * A * Real.exp ((1 - ε + η) * r)) := by
  have : Real.exp ((1 - ε) * r) = Real.exp (-(η * r)) * Real.exp ((1 - ε + η) * r) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  ring

/-- Cochrane (2023), p. 118: at the optimal reset price, `e^{(1−ε+η)r*} = ηB/((ε − 1)A)`. -/
theorem exp_rStar {ε η A B : ℝ} (hε : 1 < ε) (hη : ε - 1 < η) (hA : 0 < A) (hB : 0 < B) :
    Real.exp ((1 - ε + η) * rStar ε η A B) = η * B / ((ε - 1) * A) := by
  have hc : (1 - ε + η) ≠ 0 := by linarith
  have hpos : 0 < η * B / ((ε - 1) * A) :=
    div_pos (mul_pos (by linarith) hB) (mul_pos (by linarith) hA)
  rw [rStar, mul_div_cancel₀ _ hc, Real.exp_log hpos]

/-- Cochrane (2023), p. 118: **the optimal reset price is the unique global maximiser** of the
reset payoff (`ε > 1`, `η > ε − 1`, `A, B > 0`): `g(r) < g(r*)` for every `r ≠ r*`. -/
theorem gRes_lt {ε η A B : ℝ} (hε : 1 < ε) (hη : ε - 1 < η) (hA : 0 < A) (hB : 0 < B)
    {r : ℝ} (hr : r ≠ rStar ε η A B) : gRes ε η A B r < gRes ε η A B (rStar ε η A B) := by
  set rs := rStar ε η A B
  have hc : 0 < 1 - ε + η := by linarith
  have hk : 0 < (ε - 1) * A := mul_pos (by linarith) hA
  have hcont : Continuous (gRes ε η A B) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_gRes ε η A B x).continuousAt
  have hd : ∀ x, deriv (gRes ε η A B) x =
      Real.exp (-(η * x)) * (η * B - (ε - 1) * A * Real.exp ((1 - ε + η) * x)) := fun x => by
    rw [(hasDerivAt_gRes ε η A B x).deriv, deriv_gRes_eq]
  have hes := exp_rStar hε hη hA hB
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · have hmono : StrictMonoOn (gRes ε η A B) (Set.Iic rs) := by
      refine strictMonoOn_of_deriv_pos (convex_Iic rs) hcont.continuousOn fun x hx => ?_
      rw [interior_Iic, Set.mem_Iio] at hx
      rw [hd]
      refine mul_pos (Real.exp_pos _) ?_
      have h1 : Real.exp ((1 - ε + η) * x) < Real.exp ((1 - ε + η) * rs) :=
        Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hx hc)
      rw [hes] at h1
      have := mul_lt_mul_of_pos_left h1 hk
      rw [mul_div_cancel₀ _ hk.ne'] at this
      linarith
    exact hmono (Set.mem_Iic.2 hlt.le) (Set.mem_Iic.2 le_rfl) hlt
  · have hanti : StrictAntiOn (gRes ε η A B) (Set.Ici rs) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici rs) hcont.continuousOn fun x hx => ?_
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [hd]
      refine mul_neg_of_pos_of_neg (Real.exp_pos _) ?_
      have h1 : Real.exp ((1 - ε + η) * rs) < Real.exp ((1 - ε + η) * x) :=
        Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hx hc)
      rw [hes] at h1
      have := mul_lt_mul_of_pos_left h1 hk
      rw [mul_div_cancel₀ _ hk.ne'] at this
      linarith
    exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hgt.le) hgt

/-- Cochrane (2023), p. 118: `g(r) ≤ g(r*)` for every `r`. -/
theorem gRes_le {ε η A B : ℝ} (hε : 1 < ε) (hη : ε - 1 < η) (hA : 0 < A) (hB : 0 < B)
    (r : ℝ) : gRes ε η A B r ≤ gRes ε η A B (rStar ε η A B) := by
  by_cases h : r = rStar ε η A B
  · rw [h]
  · exact (gRes_lt hε hη hA hB h).le

/-! ### The reset problem on a probability space -/

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

variable (S) in
/-- Cochrane (2023), p. 118: the Calvo reset objective
`E ∑_k δᵏ(e^{(1−ε)r}a_k − e^{−ηr}b_k)` (`δ = αβ`: discounting times survival). -/
noncomputable def resetObj (δ ε η : ℝ) (a b : ℕ → Ω → ℝ) (r : Ω → ℝ) : ℝ :=
  ∫ ω, ∑' k, δ ^ k * (Real.exp ((1 - ε) * r ω) * a k ω - Real.exp (-(η * r ω)) * b k ω) ∂S.μ

variable (S) in
/-- Cochrane (2023), p. 118: `r` is an optimal reset price at `t`: known at `t`, essentially
bounded, and no such price does better. -/
def ResetOpt (t : ℕ) (δ ε η : ℝ) (a b : ℕ → Ω → ℝ) (r : Ω → ℝ) : Prop :=
  StronglyMeasurable[S.𝓕 t] r ∧ BddAt S r ∧
    ∀ r', StronglyMeasurable[S.𝓕 t] r' → BddAt S r' →
      resetObj S δ ε η a b r' ≤ resetObj S δ ε η a b r

/-- Cochrane (2023), p. 118: the reset objective is `E[e^{(1−ε)r}E_tW_A − e^{−ηr}E_tW_B]` for a
bounded reset price known at `t`, where `W_A = ∑_k δᵏa_k`, `W_B = ∑_k δᵏb_k` converge pathwise
and are integrable. -/
theorem resetObj_eq {δ ε η : ℝ} {a b : ℕ → Ω → ℝ} {t : ℕ}
    (hsa : ∀ ω, Summable fun k => δ ^ k * a k ω) (hsb : ∀ ω, Summable fun k => δ ^ k * b k ω)
    (hWA : Integrable (fun ω => ∑' k, δ ^ k * a k ω) S.μ)
    (hWB : Integrable (fun ω => ∑' k, δ ^ k * b k ω) S.μ) {r : Ω → ℝ}
    (hr : StronglyMeasurable[S.𝓕 t] r) (hrb : BddAt S r) :
    resetObj S δ ε η a b r = ∫ ω, gRes ε η (S.E t (fun ω => ∑' k, δ ^ k * a k ω) ω)
      (S.E t (fun ω => ∑' k, δ ^ k * b k ω) ω) (r ω) ∂S.μ := by
  set WA : Ω → ℝ := fun ω => ∑' k, δ ^ k * a k ω
  set WB : Ω → ℝ := fun ω => ∑' k, δ ^ k * b k ω
  have hpt : ∀ ω, ∑' k, δ ^ k * (Real.exp ((1 - ε) * r ω) * a k ω -
      Real.exp (-(η * r ω)) * b k ω) =
      Real.exp ((1 - ε) * r ω) * WA ω - Real.exp (-(η * r ω)) * WB ω := fun ω => by
    have h1 := (hsa ω).mul_left (Real.exp ((1 - ε) * r ω))
    have h2 := (hsb ω).mul_left (Real.exp (-(η * r ω)))
    rw [← (hsa ω).tsum_mul_left, ← (hsb ω).tsum_mul_left, ← h1.tsum_sub h2]
    exact tsum_congr fun k => by ring
  have m1 : StronglyMeasurable[S.𝓕 t] fun ω => Real.exp ((1 - ε) * r ω) :=
    (Real.continuous_exp.measurable.comp (hr.measurable.const_mul _)).stronglyMeasurable
  have m2 : StronglyMeasurable[S.𝓕 t] fun ω => Real.exp (-(η * r ω)) :=
    (Real.continuous_exp.measurable.comp (hr.measurable.const_mul _).neg).stronglyMeasurable
  obtain ⟨K1, hK1⟩ := BddAt.comp (v := fun z => Real.exp ((1 - ε) * z)) (by fun_prop) hrb
  obtain ⟨K2, hK2⟩ := BddAt.comp (v := fun z => Real.exp (-(η * z))) (by fun_prop) hrb
  have i1 : Integrable (fun ω => Real.exp ((1 - ε) * r ω) * WA ω) S.μ :=
    hWA.bdd_mul (m1.mono (S.𝓕.le t)).aestronglyMeasurable
      (hK1.mono fun ω h => by rwa [Real.norm_eq_abs])
  have i2 : Integrable (fun ω => Real.exp (-(η * r ω)) * WB ω) S.μ :=
    hWB.bdd_mul (m2.mono (S.𝓕.le t)).aestronglyMeasurable
      (hK2.mono fun ω h => by rwa [Real.norm_eq_abs])
  have j1 : Integrable (fun ω => Real.exp ((1 - ε) * r ω) * S.E t WA ω) S.μ :=
    (S.integrable_E t WA).bdd_mul (m1.mono (S.𝓕.le t)).aestronglyMeasurable
      (hK1.mono fun ω h => by rwa [Real.norm_eq_abs])
  have j2 : Integrable (fun ω => Real.exp (-(η * r ω)) * S.E t WB ω) S.μ :=
    (S.integrable_E t WB).bdd_mul (m2.mono (S.𝓕.le t)).aestronglyMeasurable
      (hK2.mono fun ω h => by rwa [Real.norm_eq_abs])
  unfold resetObj
  simp_rw [hpt]
  rw [integral_sub i1 i2, integral_mul_E m1 hK1 hWA, integral_mul_E m2 hK2 hWB,
    ← integral_sub j1 j2]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [gRes]
  ring

/-- Cochrane (2023), p. 118, **the Calvo reset price: necessity and sufficiency**. Let `ε > 1`,
`η > ε − 1`, the discounted weight sums converge pathwise with integrable sums, and their
forecasts `E_tW_A`, `E_tW_B` lie almost surely in `[lo, hi]` with `lo > 0`. Then `r` is an
optimal reset price at `t` iff it is known at `t`, essentially bounded, and almost surely equal
to `r*(E_tW_A, E_tW_B)`: `(1 − ε + η)r = log(ηE_tW_B/((ε − 1)E_tW_A))`. -/
theorem resetOpt_iff {δ ε η lo hi : ℝ} (hε : 1 < ε) (hη : ε - 1 < η) (hlo : 0 < lo)
    {a b : ℕ → Ω → ℝ} {t : ℕ}
    (hsa : ∀ ω, Summable fun k => δ ^ k * a k ω) (hsb : ∀ ω, Summable fun k => δ ^ k * b k ω)
    (hWA : Integrable (fun ω => ∑' k, δ ^ k * a k ω) S.μ)
    (hWB : Integrable (fun ω => ∑' k, δ ^ k * b k ω) S.μ)
    (hA : ∀ᵐ ω ∂S.μ, lo ≤ S.E t (fun ω => ∑' k, δ ^ k * a k ω) ω ∧
      S.E t (fun ω => ∑' k, δ ^ k * a k ω) ω ≤ hi)
    (hB : ∀ᵐ ω ∂S.μ, lo ≤ S.E t (fun ω => ∑' k, δ ^ k * b k ω) ω ∧
      S.E t (fun ω => ∑' k, δ ^ k * b k ω) ω ≤ hi) {r : Ω → ℝ} :
    ResetOpt S t δ ε η a b r ↔ StronglyMeasurable[S.𝓕 t] r ∧ BddAt S r ∧
      r =ᵐ[S.μ] fun ω => rStar ε η (S.E t (fun ω => ∑' k, δ ^ k * a k ω) ω)
        (S.E t (fun ω => ∑' k, δ ^ k * b k ω) ω) := by
  set A : Ω → ℝ := S.E t (fun ω => ∑' k, δ ^ k * a k ω) with hAdef
  set B : Ω → ℝ := S.E t (fun ω => ∑' k, δ ^ k * b k ω) with hBdef
  have hAm : StronglyMeasurable[S.𝓕 t] A := S.stronglyMeasurable_E t _
  have hBm : StronglyMeasurable[S.𝓕 t] B := S.stronglyMeasurable_E t _
  have hc : 0 < 1 - ε + η := by linarith
  -- the optimal reset price is known at `t` and bounded
  set rs : Ω → ℝ := fun ω => rStar ε η (A ω) (B ω) with hrsdef
  have hrsm : StronglyMeasurable[S.𝓕 t] rs :=
    ((((hBm.measurable.const_mul η).div (hAm.measurable.const_mul (ε - 1))).log).div_const
      _).stronglyMeasurable
  have hrsb : BddAt S rs := by
    obtain ⟨M, hM⟩ := ((isCompact_Icc (a := lo) (b := hi)).prod
      (isCompact_Icc (a := lo) (b := hi))).exists_bound_of_continuousOn
      (f := fun p : ℝ × ℝ => rStar ε η p.1 p.2) (by
        refine ContinuousOn.div_const (ContinuousOn.log ?_ fun p hp => ?_) _
        · exact ((continuousOn_const.mul continuous_snd.continuousOn).div
            (continuousOn_const.mul continuous_fst.continuousOn) fun p hp =>
              (mul_pos (by linarith) (hlo.trans_le hp.1.1)).ne')
        · exact (div_pos (mul_pos (by linarith) (hlo.trans_le hp.2.1))
            (mul_pos (by linarith) (hlo.trans_le hp.1.1))).ne')
    refine ⟨M, ?_⟩
    filter_upwards [hA, hB] with ω h1 h2
    have := hM (A ω, B ω) ⟨Set.mem_Icc.2 h1, Set.mem_Icc.2 h2⟩
    rwa [Real.norm_eq_abs] at this
  -- integrability of the payoffs
  have hgi : ∀ r', StronglyMeasurable[S.𝓕 t] r' → BddAt S r' →
      Integrable (fun ω => gRes ε η (A ω) (B ω) (r' ω)) S.μ := fun r' hr' hrb' => by
    have hAb : BddAt S A := ⟨max |lo| |hi|, hA.mono fun ω h => abs_le_max_abs_abs h.1 h.2⟩
    have hBb : BddAt S B := ⟨max |lo| |hi|, hB.mono fun ω h => abs_le_max_abs_abs h.1 h.2⟩
    have hb := (hAb.mul (BddAt.comp (v := fun z => Real.exp ((1 - ε) * z)) (by fun_prop) hrb')).add
      (hBb.mul (BddAt.comp (v := fun z => Real.exp (-(η * z))) (by fun_prop) hrb')).neg
    refine (show BddAt S fun ω => gRes ε η (A ω) (B ω) (r' ω) by
      simpa [gRes, sub_eq_add_neg] using hb).integrable ?_
    have hm : Measurable[S.𝓕 t] fun ω => gRes ε η (A ω) (B ω) (r' ω) :=
      (hAm.measurable.mul (Real.continuous_exp.measurable.comp
        (hr'.measurable.const_mul _))).sub (hBm.measurable.mul (Real.continuous_exp.measurable.comp
          (hr'.measurable.const_mul _).neg))
    exact (hm.stronglyMeasurable.mono (S.𝓕.le t)).aestronglyMeasurable
  have hle : ∀ r' : Ω → ℝ, ∀ᵐ ω ∂S.μ,
      gRes ε η (A ω) (B ω) (r' ω) ≤ gRes ε η (A ω) (B ω) (rs ω) :=
    fun r' => by
      filter_upwards [hA, hB] with ω h1 h2
      exact gRes_le hε hη (hlo.trans_le h1.1) (hlo.trans_le h2.1) _
  constructor
  · rintro ⟨hr, hrb, hopt⟩
    refine ⟨hr, hrb, ?_⟩
    have h1 := hopt rs hrsm hrsb
    rw [resetObj_eq hsa hsb hWA hWB hrsm hrsb, resetObj_eq hsa hsb hWA hWB hr hrb] at h1
    have hnn : 0 ≤ᵐ[S.μ] fun ω => gRes ε η (A ω) (B ω) (rs ω) - gRes ε η (A ω) (B ω) (r ω) :=
      (hle r).mono fun ω h => by simp only [Pi.zero_apply]; linarith
    have hint := (hgi rs hrsm hrsb).sub (hgi r hr hrb)
    have h0 : ∫ ω, (gRes ε η (A ω) (B ω) (rs ω) - gRes ε η (A ω) (B ω) (r ω)) ∂S.μ = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae hnn)
      rw [integral_sub (hgi rs hrsm hrsb) (hgi r hr hrb)]
      linarith
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0, hA, hB] with ω hω h1 h2
    by_contra hne
    have := gRes_lt hε hη (hlo.trans_le h1.1) (hlo.trans_le h2.1) hne
    simp only [Pi.zero_apply] at hω
    linarith
  · rintro ⟨hr, hrb, heq⟩
    refine ⟨hr, hrb, fun r' hr' hrb' => ?_⟩
    rw [resetObj_eq hsa hsb hWA hWB hr' hrb', resetObj_eq hsa hsb hWA hWB hr hrb]
    refine integral_mono_ae (hgi r' hr' hrb') (hgi r hr hrb) ?_
    filter_upwards [hle r', heq] with ω h1 h2
    rw [h2]
    exact h1

/-! ### The Calvo price index -/

/-- Cochrane (2023), p. 421 (the Calvo fairy): the CES price index `P_t^{1−ε}` of the cohorts:
mass `α^{t+1}` of firms that never reset (index `X₀ = P_{−1}^{1−ε}`) and mass `(1 − α)α^{t−s}`
that last reset at `s ≤ t` (at `X_s = P*_s^{1−ε}`). -/
noncomputable def cohort (α X0 : ℝ) (X : ℕ → ℝ) (t : ℕ) : ℝ :=
  α ^ (t + 1) * X0 + ∑ s ∈ Finset.range (t + 1), (1 - α) * α ^ (t - s) * X s

/-- Cochrane (2023), p. 421: the Calvo law of motion of the price index,
`P_{t+1}^{1−ε} = αP_t^{1−ε} + (1 − α)P*_{t+1}^{1−ε}`. -/
theorem cohort_succ (α X0 : ℝ) (X : ℕ → ℝ) (t : ℕ) :
    cohort α X0 X (t + 1) = α * cohort α X0 X t + (1 - α) * X (t + 1) := by
  simp only [cohort]
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add, Finset.mul_sum, pow_succ]
  have : ∀ s ∈ Finset.range (t + 1), (1 - α) * α ^ (t + 1 - s) * X s =
      α * ((1 - α) * α ^ (t - s) * X s) := fun s hs => by
    rw [Finset.mem_range] at hs
    rw [show t + 1 - s = (t - s) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl this]
  ring

/-- Cochrane (2023), p. 421: the cohort masses sum to one. -/
theorem cohort_one (α : ℝ) (t : ℕ) : cohort α 1 (fun _ => 1) t = 1 := by
  induction t with
  | zero => simp [cohort]
  | succ n ih => rw [cohort_succ, ih]; ring

/-- Cochrane (2023), p. 421: in logs, with `P_t^{1−ε} = e^{(1−ε)p_t}` and reset prices
`P*_t = e^{p_t + r_t}`, the law of motion is `1 = αe^{(ε−1)π_t} + (1 − α)e^{(1−ε)r_t}`, with
`π_{t+1} = p_{t+1} − p_t`. -/
theorem index_eq_of_cohort {α ε : ℝ} {p r : ℕ → ℝ} {X0 : ℝ}
    (h : ∀ t, Real.exp ((1 - ε) * p t) =
      cohort α X0 (fun s => Real.exp ((1 - ε) * (p s + r s))) t) (t : ℕ) :
    1 = α * Real.exp ((ε - 1) * (p (t + 1) - p t)) + (1 - α) * Real.exp ((1 - ε) * r (t + 1)) := by
  have h1 := h (t + 1)
  rw [cohort_succ, ← h t] at h1
  have hp := Real.exp_pos ((1 - ε) * p (t + 1))
  have e1 : Real.exp ((ε - 1) * (p (t + 1) - p t)) * Real.exp ((1 - ε) * p (t + 1)) =
      Real.exp ((1 - ε) * p t) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((1 - ε) * (p (t + 1) + r (t + 1))) =
      Real.exp ((1 - ε) * r (t + 1)) * Real.exp ((1 - ε) * p (t + 1)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e2, ← e1] at h1
  apply mul_right_cancel₀ hp.ne'
  linear_combination h1

end Cochrane.KeynesianStickyPrices.TidyR6CalvoReset
