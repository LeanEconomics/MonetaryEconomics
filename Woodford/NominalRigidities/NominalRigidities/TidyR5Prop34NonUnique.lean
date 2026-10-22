/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.TidyR5Prop34Measure
import NominalRigidities.TidyR5ExpectationsMeasureIID

/-!
# Proposition 3.4 with `ω̃θ < 0`: uniqueness fails on an i.i.d. economy without `L¹` sums

Woodford (2003), *Interest and Prices*, Chapter 3, §2.1, Proposition 3.4 (p. 182) and
Appendix B.3 (pp. 659–661).

`TidyR5Prop34Uncertainty.prop34_unique_of_w_neg` proves uniqueness among all predetermined
solutions for every core `ExpectationSystem`, and `TidyR5Prop34Measure.prop34_unique_of_w_neg_L1`
proves it on any probability space when the forward sums of (2.8) converge in `L¹`. This module
shows the `L¹` condition cannot be dropped: on the i.i.d. economy with uniform shocks
(`TidyR5ExpectationsMeasureIID.iidSystem unif`), with `log µ = 0`, `log S ≡ 0` and
`log P_{−1} = 0` (so (2.9) is the zero path), there is a second solution of (2.5) and (2.8) —
integrable, predetermined, with the forward sums of (2.8) converging absolutely at every state —
whose price level jumps to `1` at date `0`. This holds for every `ω̃θ ≠ 0`, in particular for
`−1 < ω̃θ < 0`.

## Where uniqueness breaks

The uniqueness proof passes from (2.8) at `t + 1` to its forecast at `t` by
`E_t ∑_j (αβ)ʲ E_{t+1} c_{t+1+j} = ∑_j (αβ)ʲ E_t c_{t+1+j}`. On a probability space this needs
more than a.e. convergence. The construction exploits exactly this: each period the forecast
curve `g_t(k) = E_t log P_{t+k}` is revised by news `ν_{t+1}(k)` that has conditional mean zero
**term by term** (`E_news`), while the discounted sum of the revisions is a nonzero constant at
every state (a doubling bet: `hasSum_bet`, `integral_bet`), so `E_t` and the infinite sum do not
commute. The revision is chosen to cancel the explosive `λ₂` dynamics that rule out such paths
under perfect foresight.

## Results

* `bet`, `hasSum_bet` (`∑_k bet_k(x) = 1` for every `x`), `integral_bet` (`∫ bet_k = 0`).
* `curve`, `sig`, `resid`, `news`: the forecast curve, its discounted sum, the required
  correction and the news; `curve_condition` ((2.5)+(2.8) at each date), `hasSum_curve`,
  `E_curve_iter` (`E_t g_{t+j}(k) = g_t(k+j)`).
* `prop34_not_unique_iid`: the second solution, `cexP`, and the zero solution; they differ.
* `cex_not_L1Fwd`: for `ω̃θ < 0` the second solution violates `L1Fwd` (so the correction is
  sharp), via `TidyR5Prop34Measure.prop34_unique_of_w_neg_L1`.
-/

namespace Woodford.NominalRigidities.TidyR5Prop34NonUnique

open MeasureTheory Filter Topology Calvo
open TidyR5ExpectationsMeasure TidyR5ExpectationsMeasureIID TidyR5Prop34Measure

/-- Woodford (2003), App. B.3: the i.i.d. economy with uniform shocks on `[0, 1]`. -/
noncomputable abbrev SU : MeasExpectationSystem (ℕ → ℝ) := iidSystem unif

/-! ### A doubling bet -/

/-- Woodford (2003), App. B.3 (an auxiliary random variable): the stake
`ψ_k(x) = 2^{k+1} 1[0 < x ≤ 2^{−(k+1)}]`. -/
noncomputable def stake (k : ℕ) (x : ℝ) : ℝ :=
  2 ^ (k + 1) * (Set.Ioc (0 : ℝ) ((2 : ℝ) ^ (k + 1))⁻¹).indicator 1 x

/-- Woodford (2003), App. B.3 (an auxiliary random variable): the doubling bet,
`bet_0 = 1 − ψ_0`, `bet_{k+1} = ψ_k − ψ_{k+1}`. -/
noncomputable def bet : ℕ → ℝ → ℝ
  | 0 => fun x => 1 - stake 0 x
  | k + 1 => fun x => stake k x - stake (k + 1) x

/-- Woodford (2003), App. B.3: the stake is measurable. -/
theorem measurable_stake (k : ℕ) : Measurable (stake k) :=
  measurable_const.mul (measurable_one.indicator measurableSet_Ioc)

/-- Woodford (2003), App. B.3: the bet is measurable. -/
theorem measurable_bet (k : ℕ) : Measurable (bet k) := by
  cases k with
  | zero => exact measurable_const.sub (measurable_stake 0)
  | succ k => exact (measurable_stake k).sub (measurable_stake (k + 1))

/-- Woodford (2003), App. B.3: `0 ≤ ψ_k ≤ 2^{k+1}`. -/
theorem stake_bounds (k : ℕ) (x : ℝ) : 0 ≤ stake k x ∧ stake k x ≤ 2 ^ (k + 1) := by
  unfold stake
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) ((2 : ℝ) ^ (k + 1))⁻¹
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- Woodford (2003), App. B.3: `|bet_k| ≤ 2^{k+3}`. -/
theorem abs_bet_le (k : ℕ) (x : ℝ) : |bet k x| ≤ 2 ^ (k + 3) := by
  cases k with
  | zero =>
    obtain ⟨h0, h1⟩ := stake_bounds 0 x
    simp only [bet]
    rw [abs_le]
    norm_num at h1 ⊢
    constructor <;> linarith
  | succ k =>
    obtain ⟨h0, h1⟩ := stake_bounds k x
    obtain ⟨h2, h3⟩ := stake_bounds (k + 1) x
    simp only [bet]
    have e1 : (2 : ℝ) ^ (k + 1 + 3) = 8 * 2 ^ (k + 1) := by ring
    have e2 : (2 : ℝ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
    rw [abs_le, e1]
    rw [e2] at h3
    have : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    constructor <;> linarith

/-- Woodford (2003), App. B.3: under the uniform law `∫ ψ_k = 1`. -/
theorem integral_stake (k : ℕ) : ∫ x, stake k x ∂(unif : Measure ℝ) = 1 := by
  unfold stake
  rw [integral_const_mul, integral_indicator_one measurableSet_Ioc,
    unif_real_Ioc (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))]
  exact mul_inv_cancel₀ (by positivity)

/-- Woodford (2003), App. B.3: the stake is integrable under the uniform law. -/
theorem integrable_stake (k : ℕ) : Integrable (stake k) (unif : Measure ℝ) :=
  Integrable.of_bound (measurable_stake k).aestronglyMeasurable (2 ^ (k + 1))
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (stake_bounds k x).1]
      exact (stake_bounds k x).2)

/-- Woodford (2003), App. B.3: **every bet is fair**, `∫ bet_k = 0` under the uniform law. -/
theorem integral_bet (k : ℕ) : ∫ x, bet k x ∂(unif : Measure ℝ) = 0 := by
  cases k with
  | zero =>
    simp only [bet]
    rw [integral_sub (integrable_const 1) (integrable_stake 0), integral_stake]
    simp
  | succ k =>
    simp only [bet]
    rw [integral_sub (integrable_stake k) (integrable_stake (k + 1)), integral_stake,
      integral_stake, sub_self]

/-- Woodford (2003), App. B.3: the stakes vanish eventually at every point. -/
theorem stake_eventually_zero (x : ℝ) : ∃ N, ∀ n, N ≤ n → stake n x = 0 := by
  by_cases hx : 0 < x
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N, fun n hn => ?_⟩
    unfold stake
    have hnot : x ∉ Set.Ioc (0 : ℝ) ((2 : ℝ) ^ (n + 1))⁻¹ := by
      intro hm
      have h1 : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ (1 / 2) ^ N := by
        rw [one_div, inv_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      linarith [hm.2]
    simp [Set.indicator_of_notMem hnot]
  · refine ⟨0, fun n _ => ?_⟩
    unfold stake
    have hnot : x ∉ Set.Ioc (0 : ℝ) ((2 : ℝ) ^ (n + 1))⁻¹ := fun hm => hx hm.1
    simp [Set.indicator_of_notMem hnot]

/-- Woodford (2003), App. B.3: the partial sums of the bets, `∑_{k ≤ n} bet_k = 1 − ψ_n`. -/
theorem sum_bet (x : ℝ) (n : ℕ) : ∑ k ∈ Finset.range (n + 1), bet k x = 1 - stake n x := by
  induction n with
  | zero => simp [bet]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [bet]
    ring

/-- Woodford (2003), App. B.3 (**the doubling bet pays one at every point**):
`∑_k bet_k(x) = 1` for every `x` (finitely many nonzero terms), although every bet is fair. -/
theorem hasSum_bet (x : ℝ) : HasSum (fun k => bet k x) 1 := by
  obtain ⟨N, hN⟩ := stake_eventually_zero x
  have hsum : ∑ k ∈ Finset.range (N + 1), bet k x = 1 := by rw [sum_bet, hN N le_rfl, sub_zero]
  rw [← hsum]
  refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [bet]
  rw [hN j (by omega), hN (j + 1) (by omega), sub_zero]

/-! ### The forecast curve -/

/-- Woodford (2003), App. B.3: the initial forecast curve `g_0(1) = 1`,
`g_0(2) = (c⁻¹ − 1)/q`, all other entries `0`. -/
noncomputable def init (q c : ℝ) (k : ℕ) : ℝ :=
  if k = 1 then 1 else if k = 2 then (c⁻¹ - 1) / q else 0

/-- Woodford (2003), App. B.3: the correction `R_t` that the date-`t+1` news must deliver,
from the curve and its discounted sum at `t`. -/
noncomputable def resid (α q c : ℝ) (g : ℕ → (ℕ → ℝ) → ℝ) (σ : (ℕ → ℝ) → ℝ) :
    (ℕ → ℝ) → ℝ :=
  fun ω => g 2 ω - α * g 1 ω - c / q * (σ ω - g 1 ω)

/-- Woodford (2003), App. B.3: the news `ν_{t+1}(k)` revising the forecast of horizon `k`:
zero for `k ≤ 1`, and `q^{−(k+1)} (R_t/c) bet_k(ε_{t+1})` at horizon `k + 2`. -/
noncomputable def news (q c : ℝ) (R : (ℕ → ℝ) → ℝ) (t : ℕ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | 1 => fun _ => 0
  | k + 2 => fun ω => (q ^ (k + 1))⁻¹ * (R ω / c) * bet k (ω (t + 1))

/-- Woodford (2003), App. B.3: the forecast curve `g_t(k)` and its discounted sum `Σ_t`, built
recursively: `g_{t+1}(k) = g_t(k+1) + ν_{t+1}(k)`, `Σ_{t+1} = (Σ_t − g_t(1))/q + R_t/c`. -/
noncomputable def state (α q c : ℝ) : ℕ → (ℕ → (ℕ → ℝ) → ℝ) × ((ℕ → ℝ) → ℝ)
  | 0 => (fun k _ => init q c k, fun _ => c⁻¹)
  | t + 1 =>
    (fun k ω => (state α q c t).1 (k + 1) ω
        + news q c (resid α q c (state α q c t).1 (state α q c t).2) t k ω,
      fun ω => ((state α q c t).2 ω - (state α q c t).1 1 ω) / q
        + resid α q c (state α q c t).1 (state α q c t).2 ω / c)

/-- Woodford (2003), App. B.3: the forecast curve `g_t(k) = E_t log P_{t+k}`. -/
noncomputable def curve (α q c : ℝ) (t : ℕ) : ℕ → (ℕ → ℝ) → ℝ := (state α q c t).1

/-- Woodford (2003), App. B.3: the discounted sum `Σ_t = ∑_k qᵏ g_t(k+1)`. -/
noncomputable def sig (α q c : ℝ) (t : ℕ) : (ℕ → ℝ) → ℝ := (state α q c t).2

/-- Woodford (2003), App. B.3: the correction at date `t`. -/
noncomputable def R (α q c : ℝ) (t : ℕ) : (ℕ → ℝ) → ℝ := resid α q c (curve α q c t) (sig α q c t)

/-- Woodford (2003), App. B.3: the recursion of the forecast curve. -/
theorem curve_succ (α q c : ℝ) (t k : ℕ) :
    curve α q c (t + 1) k = curve α q c t (k + 1) + news q c (R α q c t) t k := rfl

/-- Woodford (2003), App. B.3: the recursion of the discounted sum. -/
theorem sig_succ (α q c : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    sig α q c (t + 1) ω = (sig α q c t ω - curve α q c t 1 ω) / q + R α q c t ω / c := rfl

/-- Woodford (2003), App. B.3: news never revises the current value (the next value: `news_one`). -/
theorem news_zero (q c : ℝ) (Rf : (ℕ → ℝ) → ℝ) (t : ℕ) : news q c Rf t 0 = 0 := rfl

/-- Woodford (2003), App. B.3: news never revises the next value. -/
theorem news_one (q c : ℝ) (Rf : (ℕ → ℝ) → ℝ) (t : ℕ) : news q c Rf t 1 = 0 := rfl

/-- Woodford (2003), eqs. (2.5) and (2.8) at each date, for the curve: `g_t(1) − α g_t(0) = c Σ_t`
(in the model `c = (1 − α)(1 − αβ)ω̃θ/(1 + ω̃θ)`). -/
theorem curve_condition {α q c : ℝ} (hq : q ≠ 0) (hc : c ≠ 0) (t : ℕ) (ω : ℕ → ℝ) :
    curve α q c t 1 ω - α * curve α q c t 0 ω = c * sig α q c t ω := by
  cases t with
  | zero =>
    simp only [curve, sig, state, init]
    norm_num
    field_simp
  | succ t =>
    rw [curve_succ, curve_succ, sig_succ, news_one, news_zero]
    simp only [Pi.add_apply, Pi.zero_apply, add_zero, R, resid]
    field_simp
    ring

/-- Woodford (2003), App. B.3: `Σ_t` is the genuine discounted sum, `∑_k qᵏ g_t(k+1) = Σ_t`, at
every state (finitely many nonzero terms). -/
theorem hasSum_curve {α q c : ℝ} (hq : q ≠ 0) (t : ℕ) (ω : ℕ → ℝ) :
    HasSum (fun k => q ^ k * curve α q c t (k + 1) ω) (sig α q c t ω) := by
  induction t with
  | zero =>
    have hval : sig α q c 0 ω = ∑ k ∈ Finset.range 2, q ^ k * curve α q c 0 (k + 1) ω := by
      simp only [sig, curve, state, init, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
      field_simp
      ring
    rw [hval]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    rw [Finset.mem_range, not_lt] at hk
    simp only [curve, state, init]
    have h1 : k + 1 ≠ 1 := by omega
    have h2 : k + 1 ≠ 2 := by omega
    simp only [h1, h2, ↓reduceIte, mul_zero]
  | succ t ih =>
    -- the shifted curve
    have hA : HasSum (fun k => q ^ k * curve α q c t (k + 2) ω)
        ((sig α q c t ω - curve α q c t 1 ω) / q) := by
      have h := ((hasSum_nat_add_iff' 1).mpr ih).mul_left q⁻¹
      simp only [Finset.sum_range_one, pow_zero, one_mul, zero_add] at h
      refine (h.congr_fun fun k => ?_).trans_eq ?_
      · rw [pow_succ]; field_simp
      · field_simp
    -- the news
    have hB : HasSum (fun k => q ^ k * news q c (R α q c t) t (k + 1) ω) (R α q c t ω / c) := by
      refine (hasSum_nat_add_iff' 1).mp ?_
      simp only [Finset.sum_range_one, pow_zero, one_mul, zero_add, news_one, Pi.zero_apply,
        sub_zero]
      have h := (hasSum_bet (ω (t + 1))).mul_left (R α q c t ω / c)
      rw [mul_one] at h
      refine h.congr_fun fun k => ?_
      change q ^ (k + 1) * ((q ^ (k + 1))⁻¹ * (R α q c t ω / c) * bet k (ω (t + 1))) = _
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul]
    rw [sig_succ]
    refine (hA.add hB).congr_fun fun k => ?_
    rw [curve_succ, Pi.add_apply, mul_add]

/-! ### Measurability, integrability and forecasts -/

/-- Woodford (2003), App. B.3: the curve and its sum at date `t` are known at `t`. -/
theorem measurable_curve (α q c : ℝ) (t : ℕ) :
    (∀ k, Measurable[SU.𝓕 t] (curve α q c t k)) ∧ Measurable[SU.𝓕 t] (sig α q c t) := by
  induction t with
  | zero => exact ⟨fun k => measurable_const, measurable_const⟩
  | succ t ih =>
    obtain ⟨hg, hs⟩ := ih
    have hle : SU.𝓕 t ≤ SU.𝓕 (t + 1) := SU.𝓕.mono (Nat.le_succ t)
    have hR : Measurable[SU.𝓕 t] (R α q c t) :=
      ((hg 2).sub (measurable_const.mul (hg 1))).sub (measurable_const.mul (hs.sub (hg 1)))
    have hb : ∀ k, Measurable[SU.𝓕 (t + 1)] (fun ω : ℕ → ℝ => bet k (ω (t + 1))) :=
      fun k => (measurable_bet k).comp (measurable_shock unif le_rfl)
    have hn : ∀ k, Measurable[SU.𝓕 (t + 1)] (news q c (R α q c t) t k) := by
      intro k
      match k with
      | 0 => exact measurable_const
      | 1 => exact measurable_const
      | k + 2 =>
        exact (measurable_const.mul ((hR.mono hle le_rfl).div_const c)).mul (hb k)
    refine ⟨fun k => ?_, ?_⟩
    · rw [curve_succ]
      exact ((hg (k + 1)).mono hle le_rfl).add (hn k)
    · have : sig α q c (t + 1) = fun ω => (sig α q c t ω - curve α q c t 1 ω) / q
          + R α q c t ω / c := rfl
      rw [this]
      exact (((hs.sub (hg 1)).div_const q).add (hR.div_const c)).mono hle le_rfl

/-- Woodford (2003), App. B.3: the curve and its sum are integrable. -/
theorem integrable_curve (α q c : ℝ) (t : ℕ) :
    (∀ k, Integrable (curve α q c t k) SU.μ) ∧ Integrable (sig α q c t) SU.μ := by
  induction t with
  | zero => exact ⟨fun k => integrable_const _, integrable_const _⟩
  | succ t ih =>
    obtain ⟨hg, hs⟩ := ih
    have hR : Integrable (R α q c t) SU.μ :=
      ((hg 2).sub ((hg 1).const_mul α)).sub ((hs.sub (hg 1)).const_mul (c / q))
    have hn : ∀ k, Integrable (news q c (R α q c t) t k) SU.μ := by
      intro k
      match k with
      | 0 => exact integrable_const _
      | 1 => exact integrable_const _
      | k + 2 =>
        have hb : AEStronglyMeasurable (fun ω : ℕ → ℝ => bet k (ω (t + 1))) SU.μ :=
          ((measurable_bet k).comp (measurable_pi_apply (t + 1))).aestronglyMeasurable
        exact ((hR.div_const c).const_mul _).mul_bdd hb
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_bet_le k _)
    refine ⟨fun k => (hg (k + 1)).add (hn k), ?_⟩
    exact ((hs.sub (hg 1)).div_const q).add (hR.div_const c)

/-- Woodford (2003), App. B.3 (**news is unforecastable term by term**): `E_t ν_{t+1}(k) = 0`
a.e. for every horizon `k`. -/
theorem E_news (α q c : ℝ) (t k : ℕ) :
    SU.E t (news q c (R α q c t) t k) =ᵐ[SU.μ] 0 := by
  match k with
  | 0 =>
    change SU.E t (fun _ => (0 : ℝ)) =ᵐ[SU.μ] 0
    rw [SU.E_const]
    exact EventuallyEq.rfl
  | 1 =>
    change SU.E t (fun _ => (0 : ℝ)) =ᵐ[SU.μ] 0
    rw [SU.E_const]
    exact EventuallyEq.rfl
  | k + 2 =>
    obtain ⟨hgm, hsm⟩ := measurable_curve α q c t
    obtain ⟨hgi, hsi⟩ := integrable_curve α q c t
    have hR : Measurable[SU.𝓕 t] (R α q c t) :=
      ((hgm 2).sub (measurable_const.mul (hgm 1))).sub (measurable_const.mul (hsm.sub (hgm 1)))
    have hRi : Integrable (R α q c t) SU.μ :=
      ((hgi 2).sub ((hgi 1).const_mul α)).sub ((hsi.sub (hgi 1)).const_mul (c / q))
    set f : (ℕ → ℝ) → ℝ := fun ω => (q ^ (k + 1))⁻¹ * (R α q c t ω / c) with hf
    set g : (ℕ → ℝ) → ℝ := fun ω => bet k (ω (t + 1)) with hg
    have hfm : StronglyMeasurable[SU.𝓕 t] f :=
      (measurable_const.mul (hR.div_const c)).stronglyMeasurable
    have hgi' : Integrable g SU.μ :=
      Integrable.of_bound
        ((measurable_bet k).comp (measurable_pi_apply (t + 1))).aestronglyMeasurable
        (2 ^ (k + 3)) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact abs_bet_le k _)
    have hfgi : Integrable (f * g) SU.μ :=
      ((hRi.div_const c).const_mul _).mul_bdd hgi'.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_bet_le k _)
    have heq : news q c (R α q c t) t (k + 2) = f * g := rfl
    rw [heq]
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hfm hfgi hgi',
      E_shock_fun unif t (measurable_bet k)] with ω h1 h2
    rw [show SU.E t (f * g) ω = (f * SU.E t g) ω from h1, Pi.mul_apply,
      show SU.E t g ω = ∫ x, bet k x ∂(unif : Measure ℝ) from h2, integral_bet, mul_zero,
      Pi.zero_apply]

/-- Woodford (2003), App. B.3: one step of the forecast recursion, `E_t g_{t+1}(k) = g_t(k+1)`. -/
theorem E_curve_succ (α q c : ℝ) (t k : ℕ) :
    SU.E t (curve α q c (t + 1) k) =ᵐ[SU.μ] curve α q c t (k + 1) := by
  obtain ⟨hgm, -⟩ := measurable_curve α q c t
  obtain ⟨hgi, -⟩ := integrable_curve α q c t
  obtain ⟨hgi1, -⟩ := integrable_curve α q c (t + 1)
  have hni : Integrable (news q c (R α q c t) t k) SU.μ := by
    have h := (hgi1 k).sub (hgi (k + 1))
    rw [curve_succ] at h
    simpa using h
  rw [curve_succ]
  filter_upwards [SU.E_add (hgi (k + 1)) hni t, E_news α q c t k] with ω h1 h2
  rw [h1, Pi.add_apply, h2, SU.E_of_stronglyMeasurable (hgm (k + 1)).stronglyMeasurable (hgi _)]
  simp

/-- Woodford (2003), App. B.3 (**the curve is the forecast curve**): `E_t g_{t+j}(k) = g_t(k+j)`
a.e. -/
theorem E_curve_iter (α q c : ℝ) (t j : ℕ) :
    ∀ k, SU.E t (curve α q c (t + j) k) =ᵐ[SU.μ] curve α q c t (k + j) := by
  induction j with
  | zero =>
    intro k
    obtain ⟨hgm, -⟩ := measurable_curve α q c t
    obtain ⟨hgi, -⟩ := integrable_curve α q c t
    rw [add_zero, add_zero, SU.E_of_stronglyMeasurable (hgm k).stronglyMeasurable (hgi k)]
  | succ j ih =>
    intro k
    rw [show t + (j + 1) = t + j + 1 by omega]
    refine (SU.E_tower (Nat.le_add_right t j) _).symm.trans ?_
    refine (SU.E_congr (E_curve_succ α q c (t + j) k) t).trans ?_
    rw [show k + (j + 1) = k + 1 + j by omega]
    exact ih (k + 1)

/-! ### The second solution -/

/-- Woodford (2003), App. B.3: the second price path, `log P_{t−1} = g_t(0)` (in the project's
indexing `P t = log P_{t−1}`), with `q = αβ` and `c = (1 − α)(1 − αβ)ω̃θ/(1 + ω̃θ)`. -/
noncomputable def cexP (α β w : ℝ) (t : ℕ) : (ℕ → ℝ) → ℝ :=
  curve α (α * β) ((1 - α) * ((1 - α * β) / (1 + w)) * w) t 0

/-- Woodford (2003), eq. (2.5): the reset price of the second path. -/
noncomputable def cexPstar (α β w : ℝ) (t : ℕ) : (ℕ → ℝ) → ℝ :=
  fun ω => (cexP α β w (t + 1) ω - α * cexP α β w t ω) / (1 - α)

/-- Woodford (2003), **Proposition 3.4 with `ω̃θ ≠ 0` fails on a probability space without `L¹`
convergence of (2.8)** (p. 182; App. B.3, pp. 659–661). On the i.i.d. economy with uniform shocks
let `0 < α < 1`, `0 < β < 1`, `ω̃θ ≠ 0`, `1 + ω̃θ > 0`, `log µ = 0`, `log S ≡ 0`,
`log P_{−1} = 0`. Then the zero path and `cexP` both satisfy (2.5) and the a.e. form of (2.8),
both are integrable and predetermined with the same initial price level, the forward sums of
(2.8) along `cexP` converge absolutely at every state and date (a.e.), the zero path has
`L¹`-convergent sums — and `log P_0` is `0` on one path and `1` on the other. -/
theorem prop34_not_unique_iid {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hw0 : w ≠ 0) (hw : 0 < 1 + w) :
    let P := cexP α β w
    let pstar := cexPstar α β w
    (P 0 = 0 ∧ (∀ t, Integrable (P t) SU.μ) ∧ (∀ t, StronglyMeasurable[SU.𝓕 t] (P (t + 1))) ∧
      Eq25 α P pstar ∧ MEq28 SU α β w 0 0 P pstar) ∧
    ((0 : ℕ → (ℕ → ℝ) → ℝ) 0 = 0 ∧ (∀ t, Integrable ((0 : ℕ → (ℕ → ℝ) → ℝ) t) SU.μ) ∧
      (∀ t, StronglyMeasurable[SU.𝓕 t] ((0 : ℕ → (ℕ → ℝ) → ℝ) (t + 1))) ∧
      Eq25 α (0 : ℕ → (ℕ → ℝ) → ℝ) 0 ∧ MEq28 SU α β w 0 0 0 0 ∧ L1Fwd SU α β (costTerm 0 w 0 0)) ∧
    P 1 = (fun _ => 1) ∧ ¬ P 1 =ᵐ[SU.μ] (0 : ℕ → (ℕ → ℝ) → ℝ) 1 := by
  intro P pstar
  set q := α * β with hq_def
  set c := (1 - α) * ((1 - α * β) / (1 + w)) * w with hc_def
  have hq : q ≠ 0 := (mul_pos hα0 hβ0).ne'
  have h1a : (1 : ℝ) - α ≠ 0 := by linarith
  have h1q : (1 : ℝ) - α * β ≠ 0 := by nlinarith
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero h1a (div_ne_zero h1q hw.ne')) hw0
  have hP : ∀ t, P t = curve α q c t 0 := fun t => rfl
  have hPs : ∀ t, P (t + 1) = curve α q c t 1 := by
    intro t
    rw [hP, curve_succ, news_zero]
    funext ω
    simp
  have hP1 : P 1 = fun _ => 1 := by
    rw [hPs 0]
    funext ω
    simp [curve, state, init]
  -- forecasts of the price path
  have hfc : ∀ t j, SU.E t (P (t + 1 + j)) =ᵐ[SU.μ] curve α q c t (j + 1) := by
    intro t j
    have h := E_curve_iter α q c t (1 + j) 0
    rw [zero_add, show t + (1 + j) = t + 1 + j by omega, add_comm 1 j] at h
    exact h
  have hcost : ∀ t j, SU.E t (costTerm 0 w 0 P (t + j))
      =ᵐ[SU.μ] fun ω => w * curve α q c t (j + 1) ω := by
    intro t j
    have e : costTerm 0 w 0 P (t + j) = w • P (t + 1 + j) := by
      funext ω
      simp only [costTerm, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_add]
      rw [show t + j + 1 = t + 1 + j by omega]
    rw [e]
    filter_upwards [SU.E_smul w (P (t + 1 + j)) t, hfc t j] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  refine ⟨⟨?_, fun t => ?_, fun t => ?_, ?_, ?_⟩, ⟨rfl, fun t => integrable_zero _ _ _,
    fun t => stronglyMeasurable_zero, ?_, ?_, ?_⟩, hP1, ?_⟩
  · funext ω
    simp [P, cexP, curve, state, init]
  · exact (integrable_curve α q c t).1 0
  · rw [hPs t]
    exact ((measurable_curve α q c t).1 1).stronglyMeasurable
  · intro t ω
    change P (t + 1) ω = α * P t ω + (1 - α) * ((P (t + 1) ω - α * P t ω) / (1 - α))
    field_simp
    ring
  · have hall : ∀ᵐ ω ∂SU.μ, ∀ t j, SU.E t (costTerm 0 w 0 P (t + j)) ω
        = w * curve α q c t (j + 1) ω := by
      rw [ae_all_iff]; intro t; rw [ae_all_iff]; intro j
      exact hcost t j
    filter_upwards [hall] with ω h t
    have hs : HasSum (fun j => (α * β) ^ j * SU.E t (costTerm 0 w 0 P (t + j)) ω)
        (w * sig α q c t ω) := by
      refine ((hasSum_curve (c := c) hq t ω).mul_left w).congr_fun fun j => ?_
      rw [h t j]
      ring
    refine ⟨hs.summable, ?_⟩
    rw [hs.tsum_eq]
    change (P (t + 1) ω - α * P t ω) / (1 - α) = _
    rw [hPs t, hP t, curve_condition hq hc t ω, hc_def]
    field_simp
  · intro t ω
    simp
  · filter_upwards with ω t
    have h0 : ∀ j, SU.E t (costTerm 0 w 0 (0 : ℕ → (ℕ → ℝ) → ℝ) (t + j)) = 0 := by
      intro j
      have e : costTerm 0 w 0 (0 : ℕ → (ℕ → ℝ) → ℝ) (t + j) = 0 := by
        funext ω'
        simp [costTerm]
      rw [e]
      exact condExp_zero
    simp [h0]
  · intro t
    have h0 : ∀ j, SU.E t (costTerm 0 w 0 (0 : ℕ → (ℕ → ℝ) → ℝ) (t + j)) = 0 := by
      intro j
      have e : costTerm 0 w 0 (0 : ℕ → (ℕ → ℝ) → ℝ) (t + j) = 0 := by
        funext ω'
        simp [costTerm]
      rw [e]
      exact condExp_zero
    simp only [h0, Pi.zero_apply, abs_zero, integral_zero, mul_zero]
    exact summable_zero
  · rw [hP1]
    intro h
    have hnull : SU.μ {ω | (1 : ℝ) ≠ (0 : ℕ → (ℕ → ℝ) → ℝ) 1 ω} = 0 := ae_iff.mp h
    simp at hnull

/-- Woodford (2003), Prop. 3.4 with `ω̃θ < 0` (**the `L¹` condition is sharp**): the second
solution `cexP` of `prop34_not_unique_iid` has forward sums of (2.8) that do **not** converge in
`L¹` — otherwise `TidyR5Prop34Measure.prop34_unique_of_w_neg_L1` would make it equal to the zero
path. -/
theorem cex_not_L1Fwd {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hwneg : w < 0) (hw : 0 < 1 + w) :
    ¬ L1Fwd SU α β (costTerm 0 w 0 (cexP α β w)) := by
  intro hL
  obtain ⟨⟨h0, hPi, hpre, h25, h28⟩, ⟨-, hZi, hZpre, hZ25, hZ28, hZL⟩, -, hne⟩ :=
    prop34_not_unique_iid hα0 hα1 hβ0 hβ1 hwneg.ne hw
  have h := prop34_unique_of_w_neg_L1 SU hα0 hα1 hβ0 hβ1 hwneg hw
    (fun _ => integrable_zero _ _ _) hPi hZi hpre hZpre (by rw [h0]; exact EventuallyEq.rfl)
    h25 hZ25 h28 hZ28 hL hZL
  exact hne (h 1).1

end Woodford.NominalRigidities.TidyR5Prop34NonUnique
