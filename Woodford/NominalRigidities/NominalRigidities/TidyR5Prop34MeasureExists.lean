/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.TidyR5Prop34Measure

/-!
# Proposition 3.4 on a genuine probability space: existence, and `∃!` in the `L¹` class

Woodford (2003), *Interest and Prices*, Chapter 3, §2.1, Proposition 3.4 (p. 182) and
Appendix B.3 (pp. 659–661), with `E_t` Mathlib's conditional expectation
(`TidyR5ExpectationsMeasure.MeasExpectationSystem`).

Hypotheses (the measure-theoretic form of "`log S` difference-stationary"): `log S_t` is known at
`t`, `log S_0` is integrable, and the increments are a.s. bounded, `|log S_{t+1} − log S_t| ≤ K`;
the initial price level `log P_{−1}` is integrable and known at date `0`.

## The solution (2.9)

`z_T = (1 − λ₁)(log µ + log S_T) + (1 − λ₁)(1 − λ₂⁻¹) E_T ∑_k λ₂⁻ᵏ (log S_{T+k} − log S_T)`
(`zM`; the realised sum `remD` is a.s. bounded, `remD_props`), and
`log P_t = λ₁ log P_{t−1} + z_{t−1}` (`PM`), which is (2.9) written with the forward sum split
into its level and its expected changes.

* The key step (inside `prop34_exists_measure`): at almost every state and every date `t`,
  the forecasts `E_t log P_{t+n}` are exactly the perfect-foresight solution `Calvo.Psol`
  driven by the forecast path `n ↦ E_t log S_{t+n}` from `log P_{t−1}`; so (2.8) at `(t, ω)`
  is (2.8) of that deterministic economy at date `0`, which `Calvo.psol_eq28` provides.
* `prop34_exists_measure`: for every `ω̃θ > −1`, `PM` with its reset price solves (2.5) and the a.e.
  form of (2.8), is integrable and predetermined, and its forward sums converge in `L¹`.
* `prop34_existsUnique_measure`: for `−1 < ω̃θ < 0` it is, up to null sets, the only solution
  in that class (with `TidyR5Prop34Measure.prop34_unique_of_w_neg_L1`).
-/

namespace Woodford.NominalRigidities.TidyR5Prop34MeasureExists

open MeasureTheory Filter Topology Calvo QuadraticRoots
open TidyR5ExpectationsMeasure TidyR5Prop34Measure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Woodford (2003), App. B.3, p. 660 (`E_t` through a dominated series; adapted from the Cochrane
ObservationalEquivalence project's E_hasSum lemma): if `|f_k| ≤ c_k` a.e. with `∑ c_k < ∞`, the sum
`∑ f_k` is integrable, bounded by `∑ c_k`, and `E_t ∑ f_k = ∑ E_t f_k` a.e. at every date. -/
theorem tsum_dom {f : ℕ → Ω → ℝ} {c : ℕ → ℝ} (hc : Summable c)
    (hm : ∀ k, AEStronglyMeasurable (f k) S.μ) (hf : ∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ c k) :
    Integrable (fun ω => ∑' k, f k ω) S.μ ∧ (∀ᵐ ω ∂S.μ, |∑' k, f k ω| ≤ ∑' k, c k) ∧
      ∀ t, ∀ᵐ ω ∂S.μ, HasSum (fun k => S.E t (f k) ω) (S.E t (fun ω' => ∑' k, f k ω') ω) := by
  set F : Ω → ℝ := fun ω' => ∑' k, f k ω' with hF
  have hall : ∀ᵐ ω ∂S.μ, ∀ k, |f k ω| ≤ c k := ae_all_iff.2 hf
  have hsum : ∀ᵐ ω ∂S.μ, Summable (fun k => f k ω) := hall.mono fun ω h =>
    Summable.of_norm_bounded hc (fun k => by rw [Real.norm_eq_abs]; exact h k)
  have hFm : AEStronglyMeasurable F S.μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, f k ω)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hm k) ?_
    filter_upwards [hsum] with ω h
    exact h.hasSum.tendsto_sum_nat
  have htail : ∀ N, ∀ᵐ ω ∂S.μ,
      |F ω - ∑ k ∈ Finset.range N, f k ω| ≤ ∑' k, c (k + N) := by
    intro N
    filter_upwards [hall, hsum] with ω h hs
    change |∑' k, f k ω - ∑ k ∈ Finset.range N, f k ω| ≤ _
    rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left, ← Real.norm_eq_abs]
    exact tsum_of_norm_bounded ((summable_nat_add_iff N).2 hc).hasSum
      (fun k => by rw [Real.norm_eq_abs]; exact h (k + N))
  have hbF : ∀ᵐ ω ∂S.μ, |F ω| ≤ ∑' k, c k := by
    filter_upwards [htail 0] with ω h
    simpa using h
  have hint : ∀ k, Integrable (f k) S.μ := fun k =>
    Integrable.of_bound (hm k) (c k) ((hf k).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hFi : Integrable F S.μ :=
    Integrable.of_bound hFm _ (hbF.mono fun ω h => by rwa [Real.norm_eq_abs])
  refine ⟨hFi, hbF, fun t => ?_⟩
  have hdiff : ∀ N, ∀ᵐ ω ∂S.μ,
      |S.E t F ω - ∑ k ∈ Finset.range N, S.E t (f k) ω| ≤ ∑' k, c (k + N) := by
    intro N
    have hpi : Integrable (∑ k ∈ Finset.range N, f k) S.μ :=
      integrable_finsetSum' _ fun k _ => hint k
    have hEs : S.E t (∑ k ∈ Finset.range N, f k) =ᵐ[S.μ] ∑ k ∈ Finset.range N, S.E t (f k) :=
      condExp_finsetSum (fun k _ => hint k) (S.𝓕 t)
    filter_upwards [S.E_sub hFi hpi t, hEs,
      ae_bdd_abs_condExp_of_ae_bdd_abs (m := S.𝓕 t) (μ := S.μ)
        (f := F - ∑ k ∈ Finset.range N, f k) (by
        filter_upwards [htail N] with ω h
        simpa [Finset.sum_apply] using h)] with ω h1 h2 h3
    change |S.E t (F - ∑ k ∈ Finset.range N, f k) ω| ≤ _ at h3
    rw [h1, Pi.sub_apply, h2, Finset.sum_apply] at h3
    exact h3
  have hEb : ∀ᵐ ω ∂S.μ, ∀ k, |S.E t (f k) ω| ≤ c k :=
    ae_all_iff.2 fun k => ae_bdd_abs_condExp_of_ae_bdd_abs (hf k)
  filter_upwards [ae_all_iff.2 hdiff, hEb] with ω hd hb
  have hs : Summable fun k => ‖S.E t (f k) ω‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact hb k) hc
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun N => ?_) (tendsto_sum_nat_add c)
  rw [norm_norm, Real.norm_eq_abs, abs_sub_comm]
  exact hd N

/-! ### The solution -/

/-- Woodford (2003), App. B.3, p. 660: the realised discounted sum of changes in marginal cost,
`∑_k aᵏ (log S_{T+k} − log S_T)`. -/
noncomputable def remD (a : ℝ) (s : ℕ → Ω → ℝ) (T : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * (s (T + k) ω - s T ω)

/-- Woodford (2003), (2.9), p. 182: the target `z_T` of the partial adjustment, with
`a = λ₂⁻¹`: `(1 − λ₁)(log µ + log S_T) + (1 − λ₁)(1 − a) E_T ∑_k aᵏ (log S_{T+k} − log S_T)`. -/
noncomputable def zM (α β w m : ℝ) (s : ℕ → Ω → ℝ) (T : ℕ) : Ω → ℝ :=
  fun ω => (1 - lam1 β (calvoXi α β w)) * (m + s T ω)
    + (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹) *
      S.E T (remD (lam2 β (calvoXi α β w))⁻¹ s T) ω

/-- Woodford (2003), (2.9), p. 182 (**the solution on a probability space**): `PM 0 = log P_{−1}`
and `log P_t = λ₁ log P_{t−1} + z_t` (in the project's indexing `PM (t + 1) = log P_t`). -/
noncomputable def PM (α β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => P0
  | t + 1 => fun ω => lam1 β (calvoXi α β w) * PM α β w m s P0 t ω + zM S α β w m s t ω

/-- Woodford (2003), eq. (2.5), p. 180: the reset price of the solution. -/
noncomputable def pstarM (α β w m : ℝ) (s : ℕ → Ω → ℝ) (P0 : Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (PM S α β w m s P0 (t + 1) ω - α * PM S α β w m s P0 t ω) / (1 - α)

/-- Woodford (2003), App. B.3: bounded increments give `|log S_{T+k} − log S_T| ≤ K k` a.s. -/
theorem incr_bound {s : ℕ → Ω → ℝ} {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    (T k : ℕ) : ∀ᵐ ω ∂S.μ, |s (T + k) ω - s T ω| ≤ K * k := by
  induction k with
  | zero => exact Eventually.of_forall fun ω => by simp
  | succ k ih =>
    filter_upwards [ih, hsb (T + k)] with ω h1 h2
    rw [show T + (k + 1) = T + k + 1 by omega]
    have := abs_add_le (s (T + k + 1) ω - s (T + k) ω) (s (T + k) ω - s T ω)
    rw [show s (T + k + 1) ω - s (T + k) ω + (s (T + k) ω - s T ω)
      = s (T + k + 1) ω - s T ω by ring] at this
    push_cast
    linarith

/-- Woodford (2003), App. B.3: marginal cost is integrable at every date. -/
theorem integrable_s {s : ℕ → Ω → ℝ} (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t))
    (hs0 : Integrable (s 0) S.μ) {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    (T : ℕ) : Integrable (s T) S.μ := by
  have hd : Integrable (s T - s 0) S.μ := by
    refine Integrable.of_bound ((((hsm T).mono (S.𝓕.le T)).sub
      ((hsm 0).mono (S.𝓕.le 0))).aestronglyMeasurable) (K * T) ?_
    filter_upwards [incr_bound S hsb 0 T] with ω h
    rw [Real.norm_eq_abs, Pi.sub_apply]
    simpa using h
  have := hs0.add hd
  rwa [add_sub_cancel] at this

/-- Woodford (2003), App. B.3, p. 660: the realised sum `remD T` is integrable, a.s. bounded by
`K ∑ k aᵏ`, and its forecast is the sum of the forecasts. -/
theorem remD_props {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {s : ℕ → Ω → ℝ}
    (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t)) {K : ℝ}
    (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K) (T : ℕ) :
    Integrable (remD a s T) S.μ ∧
      (∀ᵐ ω ∂S.μ, |remD a s T ω| ≤ ∑' k : ℕ, a ^ k * (K * k)) ∧
      ∀ t, ∀ᵐ ω ∂S.μ, HasSum (fun k => S.E t (fun ω' => a ^ k * (s (T + k) ω' - s T ω')) ω)
        (S.E t (remD a s T) ω) := by
  have hc : Summable (fun k : ℕ => a ^ k * (K * k)) :=
    ((summable_nat_mul_geom ha0 ha1).mul_left K).congr fun k => by ring
  have hm : ∀ k, AEStronglyMeasurable (fun ω => a ^ k * (s (T + k) ω - s T ω)) S.μ := fun k =>
    ((((hsm (T + k)).mono (S.𝓕.le _)).sub ((hsm T).mono (S.𝓕.le _))).const_mul
      (a ^ k)).aestronglyMeasurable
  have hf : ∀ k, ∀ᵐ ω ∂S.μ, |a ^ k * (s (T + k) ω - s T ω)| ≤ a ^ k * (K * k) := by
    intro k
    filter_upwards [incr_bound S hsb T k] with ω h
    rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 k)]
    exact mul_le_mul_of_nonneg_left h (pow_nonneg ha0 k)
  exact tsum_dom S hc hm hf

/-- Woodford (2003), (2.9): `z_T` is known at `T` and integrable. -/
theorem zM_props {α β w m : ℝ} {s : ℕ → Ω → ℝ} (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t))
    (hs0 : Integrable (s 0) S.μ) {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    (T : ℕ) : Measurable[S.𝓕 T] (zM S α β w m s T) ∧ Integrable (zM S α β w m s T) S.μ := by
  constructor
  · exact ((measurable_const.add (hsm T).measurable).const_mul _).add
      ((S.stronglyMeasurable_E T _).measurable.const_mul _)
  · exact (((integrable_const m).add (integrable_s S hsm hs0 hsb T)).const_mul _).add
      ((S.integrable_E T _).const_mul _)

/-- Woodford (2003), (2.9): the price index of the solution is integrable, `log P_{t−1}` is known
at `t`, and `log P_t` is known at `t` (predetermined). -/
theorem PM_props {α β w m : ℝ} {s : ℕ → Ω → ℝ} (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t))
    (hs0 : Integrable (s 0) S.μ) {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    {P0 : Ω → ℝ} (hP0m : StronglyMeasurable[S.𝓕 0] P0) (hP0i : Integrable P0 S.μ) (t : ℕ) :
    Measurable[S.𝓕 t] (PM S α β w m s P0 t) ∧ Measurable[S.𝓕 t] (PM S α β w m s P0 (t + 1)) ∧
      Integrable (PM S α β w m s P0 t) S.μ := by
  induction t with
  | zero =>
    refine ⟨hP0m.measurable, ?_, hP0i⟩
    exact (hP0m.measurable.const_mul _).add (zM_props S hsm hs0 hsb 0).1
  | succ t ih =>
    obtain ⟨-, h2, h3⟩ := ih
    refine ⟨h2.mono (S.𝓕.mono (Nat.le_succ t)) le_rfl, ?_, ?_⟩
    · exact ((h2.mono (S.𝓕.mono (Nat.le_succ t)) le_rfl).const_mul _).add
        (zM_props S hsm hs0 hsb (t + 1)).1
    · exact (h3.const_mul _).add (zM_props S hsm hs0 hsb t).2

/-- Woodford (2003), (2.9), p. 182 (**the forecast of the target**): a.s.,
`E_t z_{t+i} = (1 − λ₁)(log µ + E_t log S_{t+i}) + (1 − λ₁)(1 − a) ∑_k aᵏ E_t(log S_{t+i+k} −
log S_{t+i})`. -/
theorem E_zM {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t))
    (hs0 : Integrable (s 0) S.μ) {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    (t i : ℕ) : S.E t (zM S α β w m s (t + i)) =ᵐ[S.μ] fun ω =>
      (1 - lam1 β (calvoXi α β w)) * (m + S.E t (s (t + i)) ω)
      + (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹) *
        ∑' k, (lam2 β (calvoXi α β w))⁻¹ ^ k *
          (S.E t (s (t + i + k)) ω - S.E t (s (t + i)) ω) := by
  obtain ⟨-, -, -, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  set l1 := lam1 β (calvoXi α β w)
  set a := (lam2 β (calvoXi α β w))⁻¹
  have hsi := integrable_s S hsm hs0 hsb
  obtain ⟨-, -, hHas⟩ := remD_props S ha0.le ha1 hsm hsb (t + i)
  have hfun : zM S α β w m s (t + i) = (fun _ => (1 - l1) * m) + (1 - l1) • s (t + i)
      + ((1 - l1) * (1 - a)) • S.E (t + i) (remD a s (t + i)) := by
    funext ω
    simp only [zM, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hterm : ∀ k, S.E t (fun ω' => a ^ k * (s (t + i + k) ω' - s (t + i) ω'))
      =ᵐ[S.μ] fun ω => a ^ k * (S.E t (s (t + i + k)) ω - S.E t (s (t + i)) ω) := by
    intro k
    have e : (fun ω' => a ^ k * (s (t + i + k) ω' - s (t + i) ω'))
        = a ^ k • (s (t + i + k) - s (t + i)) := rfl
    rw [e]
    filter_upwards [S.E_smul (a ^ k) (s (t + i + k) - s (t + i)) t,
      S.E_sub (hsi (t + i + k)) (hsi (t + i)) t] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, smul_eq_mul]
  rw [hfun]
  filter_upwards [S.E_add ((integrable_const _).add ((hsi _).smul (1 - l1)))
      ((S.integrable_E _ _).smul ((1 - l1) * (1 - a))) t,
    S.E_add (integrable_const ((1 - l1) * m)) ((hsi _).smul (1 - l1)) t,
    S.E_smul (1 - l1) (s (t + i)) t,
    S.E_smul ((1 - l1) * (1 - a)) (S.E (t + i) (remD a s (t + i))) t,
    S.E_tower (Nat.le_add_right t i) (remD a s (t + i)), hHas t, ae_all_iff.mpr hterm]
    with ω h1 h2 h3 h4 h5 h6 h7
  rw [h1, Pi.add_apply, h2, Pi.add_apply, S.E_const, h3, h4, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, h5, ← h6.tsum_eq]
  simp_rw [h7]
  ring

/-- Woodford (2003), App. B.3: the forecast path of marginal cost has bounded increments,
`|E_t log S_{t+n+1} − E_t log S_{t+n}| ≤ K` a.s. -/
theorem E_s_incr {s : ℕ → Ω → ℝ} (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t))
    (hs0 : Integrable (s 0) S.μ) {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    (t n : ℕ) : ∀ᵐ ω ∂S.μ, |S.E t (s (t + n + 1)) ω - S.E t (s (t + n)) ω| ≤ K := by
  have hsi := integrable_s S hsm hs0 hsb
  filter_upwards [S.E_sub (hsi (t + n + 1)) (hsi (t + n)) t,
    ae_bdd_abs_condExp_of_ae_bdd_abs (m := S.𝓕 t) (μ := S.μ)
      (f := s (t + n + 1) - s (t + n)) (hsb (t + n))] with ω h1 h2
  change |S.E t (s (t + n + 1) - s (t + n)) ω| ≤ K at h2
  rw [h1, Pi.sub_apply] at h2
  exact h2

/-- Woodford (2003), (2.9): one step of the forecast of the price index,
`E_t log P_{t+n} = λ₁ E_t log P_{t+n−1} + E_t z_{t+n}` a.s. -/
theorem E_PM_succ {α β w m : ℝ} {s : ℕ → Ω → ℝ} (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t))
    (hs0 : Integrable (s 0) S.μ) {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    {P0 : Ω → ℝ} (hP0m : StronglyMeasurable[S.𝓕 0] P0) (hP0i : Integrable P0 S.μ) (t n : ℕ) :
    S.E t (PM S α β w m s P0 (t + n + 1)) =ᵐ[S.μ] fun ω =>
      lam1 β (calvoXi α β w) * S.E t (PM S α β w m s P0 (t + n)) ω
        + S.E t (zM S α β w m s (t + n)) ω := by
  have e : PM S α β w m s P0 (t + n + 1)
      = lam1 β (calvoXi α β w) • PM S α β w m s P0 (t + n) + zM S α β w m s (t + n) := rfl
  rw [e]
  filter_upwards [S.E_add ((PM_props S (α := α) (β := β) (w := w) (m := m) hsm hs0 hsb hP0m
      hP0i (t + n)).2.2.smul (lam1 β (calvoXi α β w)))
      (zM_props S hsm hs0 hsb (t + n)).2 t, S.E_smul (lam1 β (calvoXi α β w))
      (PM S α β w m s P0 (t + n)) t] with ω h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), eq. (2.8): the forecast of the cost term,
`E_t[log µ + log S_T + ω̃θ log P_T] = log µ + E_t log S_T + ω̃θ E_t log P_T` a.s. -/
theorem E_costTerm {α β w m : ℝ} {s : ℕ → Ω → ℝ} (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t))
    (hs0 : Integrable (s 0) S.μ) {K : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K)
    {P0 : Ω → ℝ} (hP0m : StronglyMeasurable[S.𝓕 0] P0) (hP0i : Integrable P0 S.μ) (t j : ℕ) :
    S.E t (costTerm m w s (PM S α β w m s P0) (t + j)) =ᵐ[S.μ] fun ω =>
      m + S.E t (s (t + j)) ω + w * S.E t (PM S α β w m s P0 (t + j + 1)) ω := by
  have hsi := integrable_s S hsm hs0 hsb
  have hPi := fun T => (PM_props S hsm hs0 hsb hP0m hP0i (α := α) (β := β) (w := w) (m := m)
    T).2.2
  have e : costTerm m w s (PM S α β w m s P0) (t + j)
      = (fun _ => m) + s (t + j) + w • PM S α β w m s P0 (t + j + 1) := by
    funext ω
    simp [costTerm]
  rw [e]
  filter_upwards [S.E_add ((integrable_const m).add (hsi _)) ((hPi _).smul w) t,
    S.E_add (integrable_const m) (hsi (t + j)) t, S.E_smul w (PM S α β w m s P0 (t + j + 1)) t]
    with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, Pi.add_apply, S.E_const, h3, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), **Proposition 3.4: existence on a probability space** (p. 182; App. B.3,
pp. 659–661). Let `0 < α < 1`, `0 < β < 1`, `1 + ω̃θ > 0`, `log S_t` known at `t` with `log S_0`
integrable and a.s. increments bounded by `K`, and `log P_{−1}` integrable and known at `0`. Then
the solution (2.9) (`PM`, reset price `pstarM`) satisfies (2.5) and the a.e. form of (2.8), is
integrable and predetermined, and its forward sums converge in `L¹` (`L1Fwd`). -/
theorem prop34_exists_measure {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ}
    (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t)) (hs0 : Integrable (s 0) S.μ) {K : ℝ}
    (hK0 : 0 ≤ K) (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K) {P0 : Ω → ℝ}
    (hP0m : StronglyMeasurable[S.𝓕 0] P0) (hP0i : Integrable P0 S.μ) :
    PM S α β w m s P0 0 = P0 ∧ (∀ t, Integrable (PM S α β w m s P0 t) S.μ) ∧
      (∀ t, StronglyMeasurable[S.𝓕 t] (PM S α β w m s P0 (t + 1))) ∧
      Eq25 α (PM S α β w m s P0) (pstarM S α β w m s P0) ∧
      MEq28 S α β w m s (PM S α β w m s P0) (pstarM S α β w m s P0) ∧
      L1Fwd S α β (costTerm m w s (PM S α β w m s P0)) := by
  obtain ⟨hξ, hl0, hl1, ha0, ha1⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  set l1 := lam1 β (calvoXi α β w) with hl1def
  set a := (lam2 β (calvoXi α β w))⁻¹ with hadef
  set P := PM S α β w m s P0 with hPdef
  have hsi := integrable_s S hsm hs0 hsb
  have hPp := PM_props S hsm hs0 hsb (α := α) (β := β) (w := w) (m := m) hP0m hP0i
  have hPE : ∀ T, S.E T (P T) = P T := fun T =>
    S.E_of_stronglyMeasurable (hPp T).1.stronglyMeasurable (hPp T).2.2
  have hPE1 : ∀ T, S.E T (P (T + 1)) = P (T + 1) := fun T =>
    S.E_of_stronglyMeasurable (hPp T).2.1.stronglyMeasurable (hPp (T + 1)).2.2
  refine ⟨rfl, fun t => (hPp t).2.2, fun t => (hPp t).2.1.stronglyMeasurable, ?_, ?_, ?_⟩
  · intro t ω
    change P (t + 1) ω = α * P t ω + (1 - α) * ((P (t + 1) ω - α * P t ω) / (1 - α))
    have : (1 : ℝ) - α ≠ 0 := by linarith
    field_simp
    ring
  · -- (2.8): reduce to the perfect-foresight economy driven by the forecast path
    have hA1 : ∀ᵐ ω ∂S.μ, ∀ t i, S.E t (zM S α β w m s (t + i)) ω =
          (1 - l1) * (m + S.E t (s (t + i)) ω) + (1 - l1) * (1 - a) *
            ∑' k, a ^ k * (S.E t (s (t + i + k)) ω - S.E t (s (t + i)) ω) := by
      rw [ae_all_iff]; intro t; rw [ae_all_iff]; intro i
      exact E_zM S hα0 hα1 hβ0 hβ1 hw hsm hs0 hsb t i
    have hA2 : ∀ᵐ ω ∂S.μ, ∀ t n, |S.E t (s (t + n + 1)) ω - S.E t (s (t + n)) ω| ≤ K := by
      rw [ae_all_iff]; intro t; rw [ae_all_iff]; intro n
      exact E_s_incr S hsm hs0 hsb t n
    have hA3 : ∀ᵐ ω ∂S.μ, ∀ t n, S.E t (P (t + n + 1)) ω = l1 * S.E t (P (t + n)) ω
          + S.E t (zM S α β w m s (t + n)) ω := by
      rw [ae_all_iff]; intro t; rw [ae_all_iff]; intro n
      exact E_PM_succ S hsm hs0 hsb hP0m hP0i t n
    have hA4 : ∀ᵐ ω ∂S.μ, ∀ t j, S.E t (costTerm m w s P (t + j)) ω
          = m + S.E t (s (t + j)) ω + w * S.E t (P (t + j + 1)) ω := by
      rw [ae_all_iff]; intro t; rw [ae_all_iff]; intro j
      exact E_costTerm S hsm hs0 hsb hP0m hP0i t j
    filter_upwards [hA1, hA2, hA3, hA4] with ω hz hinc hP1 hc t
    set sPF : ℕ → Unit → ℝ := fun n _ => S.E t (s (t + n)) ω with hsPF
    have hsbPF : BoundedIncr sPF := ⟨K, fun n _ => hinc t n⟩
    obtain ⟨K', hK'⟩ := mcost_diffStationary perfectForesight (m := m)
      (diffStationary_of_boundedIncr perfectForesight (fun _ => rfl) hsbPF)
    have hzm : ∀ n, S.E t (zM S α β w m s (t + n)) ω = zbar perfectForesight α β w m sPF n () := by
      intro n
      have hd := fwd_decomp perfectForesight ha0.le ha1 hK' n ()
      change S.E t (zM S α β w m s (t + n)) ω
        = (1 - l1) * (1 - a) * perfectForesight.forwardSeries a (mcost m sPF) n ()
      rw [hd, hz t n]
      have h1a : (1 : ℝ) - a ≠ 0 := by linarith
      have hrem : fwdRem perfectForesight a (mcost m sPF) n ()
          = ∑' k, a ^ k * (S.E t (s (t + n + k)) ω - S.E t (s (t + n)) ω) := by
        simp only [fwdRem]
        refine tsum_congr fun k => ?_
        change a ^ k * ((m + S.E t (s (t + (n + k))) ω) - (m + S.E t (s (t + n)) ω)) = _
        rw [show t + (n + k) = t + n + k by omega]
        ring
      rw [hrem]
      change (1 - l1) * (m + S.E t (s (t + n)) ω) + _ = (1 - l1) * (1 - a) *
        ((1 - a)⁻¹ * (m + S.E t (s (t + n)) ω) + _)
      field_simp
    have hPm : ∀ n, S.E t (P (t + n)) ω
        = Psol perfectForesight α β w m sPF (fun _ => P t ω) n () := by
      intro n
      induction n with
      | zero => simp only [add_zero, hPE t]; rfl
      | succ n ih =>
        rw [show t + (n + 1) = t + n + 1 by omega, hP1 t n, ih, hzm n]
        rfl
    have hcm : ∀ j, S.E t (costTerm m w s P (t + j)) ω
        = costTerm m w sPF (Psol perfectForesight α β w m sPF (fun _ => P t ω)) j () := by
      intro j
      rw [hc t j, show t + j + 1 = t + (j + 1) by omega, hPm (j + 1)]
      rfl
    have h28 := psol_eq28 perfectForesight hα0 hα1 hβ0 hβ1 hw (s := sPF) (m := m)
      (fun _ => rfl) hsbPF (P0 := fun _ => P t ω) rfl
      ⟨|P t ω - sPF 0 ()|, fun u => le_rfl⟩ 0 ()
    obtain ⟨hs, hv⟩ := h28
    have hseq : (fun j => (α * β) ^ j * S.E t (costTerm m w s P (t + j)) ω)
        = fun j => (α * β) ^ j * perfectForesight.E 0
          (costTerm m w sPF (Psol perfectForesight α β w m sPF (fun _ => P t ω)) (0 + j)) () := by
      funext j
      rw [hcm j, zero_add]
      rfl
    refine ⟨hseq ▸ hs, ?_⟩
    rw [hseq, ← hv]
    have h1 := hPm 1
    rw [hPE1 t] at h1
    change (P (t + 1) ω - α * P t ω) / (1 - α) = (Psol perfectForesight α β w m sPF
      (fun _ => P t ω) 1 () - α * Psol perfectForesight α β w m sPF (fun _ => P t ω) 0 ()) /
      (1 - α)
    rw [← h1]
    rfl
  · -- `L¹` convergence of the forward sums
    set Ms := ∑' k : ℕ, a ^ k * (K * k)
    have hMs0 : 0 ≤ Ms := tsum_nonneg fun k => mul_nonneg (pow_nonneg ha0.le k)
      (mul_nonneg hK0 (Nat.cast_nonneg k))
    set κ' := (1 - l1) * (1 - a)
    have hκ' : 0 ≤ κ' := mul_nonneg (by linarith) (by linarith)
    set N0 := ∫ ω, |s 0 ω| ∂S.μ
    have hsN : ∀ T, ∫ ω, |s T ω| ∂S.μ ≤ N0 + K * T := by
      intro T
      have hb : ∀ᵐ ω ∂S.μ, |s T ω| ≤ |s 0 ω| + K * T := by
        filter_upwards [incr_bound S hsb 0 T] with ω h
        rw [zero_add] at h
        have := abs_sub_abs_le_abs_sub (s T ω) (s 0 ω)
        linarith
      refine (integral_mono_ae (hsi T).abs (show Integrable (fun ω => |s 0 ω| + K * T) S.μ from
        hs0.abs.add (integrable_const _)) hb).trans ?_
      rw [integral_add hs0.abs (integrable_const _), integral_const]
      simp [N0]
    have hzN : ∀ T, ∫ ω, |zM S α β w m s T ω| ∂S.μ
        ≤ (1 - l1) * (|m| + ∫ ω, |s T ω| ∂S.μ) + κ' * Ms := by
      intro T
      obtain ⟨-, hbd, -⟩ := remD_props S ha0.le ha1 hsm hsb T
      have hE := ae_bdd_abs_condExp_of_ae_bdd_abs (m := S.𝓕 T) (μ := S.μ) hbd
      have hb : ∀ᵐ ω ∂S.μ, |zM S α β w m s T ω| ≤ (1 - l1) * (|m| + |s T ω|) + κ' * Ms := by
        filter_upwards [hE] with ω h
        change |(1 - l1) * (m + s T ω) + κ' * S.E T (remD a s T) ω| ≤ _
        have k1 := abs_add_le ((1 - l1) * (m + s T ω)) (κ' * S.E T (remD a s T) ω)
        have k2 : |(1 - l1) * (m + s T ω)| ≤ (1 - l1) * (|m| + |s T ω|) := by
          rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - l1)]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by linarith)
        have k3 : |κ' * S.E T (remD a s T) ω| ≤ κ' * Ms := by
          rw [abs_mul, abs_of_nonneg hκ']
          exact mul_le_mul_of_nonneg_left h hκ'
        linarith
      have i1 : Integrable (fun ω => (1 - l1) * (|m| + |s T ω|)) S.μ :=
        ((integrable_const |m|).add (hsi T).abs).const_mul _
      refine (integral_mono_ae (zM_props S hsm hs0 hsb T).2.abs
        (show Integrable (fun ω => (1 - l1) * (|m| + |s T ω|) + κ' * Ms) S.μ from
          i1.add (integrable_const _)) hb).trans (le_of_eq ?_)
      rw [integral_add i1 (integrable_const _), integral_const_mul,
        integral_add (integrable_const _) (hsi T).abs, integral_const, integral_const]
      simp
    set D0 := (1 - l1) * (|m| + N0) + κ' * Ms
    set A := ∫ ω, |P0 ω| ∂S.μ + D0 / (1 - l1)
    have hPN : ∀ T, ∫ ω, |P T ω| ∂S.μ ≤ A + K * T := by
      intro T
      induction T with
      | zero =>
        have : 0 ≤ D0 / (1 - l1) := div_nonneg (by positivity) (by linarith)
        simp only [CharP.cast_eq_zero, mul_zero, add_zero]
        change ∫ ω, |P0 ω| ∂S.μ ≤ A
        linarith
      | succ T ih =>
        have hb : ∀ ω, |P (T + 1) ω| ≤ l1 * |P T ω| + |zM S α β w m s T ω| := by
          intro ω
          change |l1 * P T ω + zM S α β w m s T ω| ≤ _
          have := abs_add_le (l1 * P T ω) (zM S α β w m s T ω)
          rw [abs_mul, abs_of_pos hl0] at this
          exact this
        have i1 : Integrable (fun ω => l1 * |P T ω|) S.μ := (hPp T).2.2.abs.const_mul l1
        have i2 : Integrable (fun ω => |zM S α β w m s T ω|) S.μ :=
          (zM_props S hsm hs0 hsb T).2.abs
        have hI := integral_mono (hPp (T + 1)).2.2.abs
          (show Integrable (fun ω => l1 * |P T ω| + |zM S α β w m s T ω|) S.μ from i1.add i2) hb
        rw [integral_add i1 i2, integral_const_mul] at hI
        have hz := hzN T
        have hs := hsN T
        have hA : (1 - l1) * A = (1 - l1) * ∫ ω, |P0 ω| ∂S.μ + D0 := by
          have h1l : (1 : ℝ) - l1 ≠ 0 := by linarith
          simp only [A]
          rw [mul_add, mul_div_cancel₀ _ h1l]
        have hP0n : 0 ≤ ∫ ω, |P0 ω| ∂S.μ := integral_nonneg fun ω => abs_nonneg _
        have e1 : A + K * ((T + 1 : ℕ) : ℝ) - (l1 * (A + K * T) + ((1 - l1) * (|m| + (N0 + K * T))
            + κ' * Ms)) = ((1 - l1) * A - D0) + K := by
          push_cast; simp only [D0]; ring
        have i1 : l1 * ∫ ω, |P T ω| ∂S.μ ≤ l1 * (A + K * T) := mul_le_mul_of_nonneg_left ih hl0.le
        have i2 : (1 - l1) * (|m| + ∫ ω, |s T ω| ∂S.μ) ≤ (1 - l1) * (|m| + (N0 + K * T)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have : (1 - l1) * ∫ ω, |P0 ω| ∂S.μ ≥ 0 := mul_nonneg (by linarith) hP0n
        linarith
    intro t
    have hbound : ∀ j : ℕ, (α * β) ^ j * ∫ ω, |S.E t (costTerm m w s P (t + j)) ω| ∂S.μ
        ≤ (α * β) ^ j * ((|m| + N0 + K * t + |w| * (A + K * (t + 1))) + (K + |w| * K) * j) := by
      intro j
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (mul_pos hα0 hβ0).le j)
      refine (integral_abs_condExp_le _).trans ?_
      have hb : ∀ ω, |costTerm m w s P (t + j) ω|
          ≤ |m| + |s (t + j) ω| + |w| * |P (t + j + 1) ω| := by
        intro ω
        change |m + s (t + j) ω + w * P (t + j + 1) ω| ≤ _
        have k1 := abs_add_le (m + s (t + j) ω) (w * P (t + j + 1) ω)
        have k2 := abs_add_le m (s (t + j) ω)
        rw [abs_mul] at k1
        linarith
      have ic : Integrable (costTerm m w s P (t + j)) S.μ :=
        ((integrable_const m).add (hsi (t + j))).add ((hPp (t + j + 1)).2.2.const_mul w)
      have i1 : Integrable (fun ω => |m| + |s (t + j) ω|) S.μ :=
        (integrable_const |m|).add (hsi (t + j)).abs
      have i2 : Integrable (fun ω => |w| * |P (t + j + 1) ω|) S.μ :=
        (hPp (t + j + 1)).2.2.abs.const_mul |w|
      have hI := integral_mono (show Integrable (fun ω => |costTerm m w s P (t + j) ω|) S.μ from
        ic.abs) (show Integrable (fun ω => |m| + |s (t + j) ω| + |w| * |P (t + j + 1) ω|) S.μ
        from i1.add i2) hb
      rw [integral_add i1 i2, integral_add (integrable_const _) (hsi (t + j)).abs,
        integral_const, integral_const_mul] at hI
      simp only [probReal_univ, smul_eq_mul, one_mul] at hI
      have h1 := hsN (t + j)
      have h2 := hPN (t + j + 1)
      have h3 : |w| * ∫ ω, |P (t + j + 1) ω| ∂S.μ ≤ |w| * (A + K * ((t + j + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg w)
      push_cast at h1 h3 ⊢
      nlinarith [abs_nonneg w, hK0]
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg (mul_pos hα0 hβ0).le j)
      (integral_nonneg fun ω => abs_nonneg _)) hbound ?_
    have hq0 : 0 ≤ α * β := (mul_pos hα0 hβ0).le
    have hq1 : α * β < 1 := by nlinarith
    refine (((summable_geometric_of_lt_one hq0 hq1).mul_right
      (|m| + N0 + K * t + |w| * (A + K * (t + 1)))).add
      ((summable_nat_mul_geom hq0 hq1).mul_left (K + |w| * K))).congr fun j => ?_
    ring

/-- Woodford (2003), **Proposition 3.4 with `−1 < ω̃θ < 0` on a probability space: existence and
uniqueness in the `L¹` class** (p. 182; App. B.3). Under the hypotheses of
`prop34_exists_measure`, (2.9) is a solution with the listed properties, and every other
integrable predetermined solution of (2.5) and the a.e. form of (2.8) with the same initial price
level and `L¹`-convergent forward sums coincides with it almost surely at every date. -/
theorem prop34_existsUnique_measure {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ}
    (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t)) (hs0 : Integrable (s 0) S.μ) {K : ℝ}
    (hK0 : 0 ≤ K) (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s (t + 1) ω - s t ω| ≤ K) {P0 : Ω → ℝ}
    (hP0m : StronglyMeasurable[S.𝓕 0] P0) (hP0i : Integrable P0 S.μ) :
    (PM S α β w m s P0 0 = P0 ∧ (∀ t, Integrable (PM S α β w m s P0 t) S.μ) ∧
      (∀ t, StronglyMeasurable[S.𝓕 t] (PM S α β w m s P0 (t + 1))) ∧
      Eq25 α (PM S α β w m s P0) (pstarM S α β w m s P0) ∧
      MEq28 S α β w m s (PM S α β w m s P0) (pstarM S α β w m s P0) ∧
      L1Fwd S α β (costTerm m w s (PM S α β w m s P0))) ∧
    ∀ P pstar : ℕ → Ω → ℝ, P 0 =ᵐ[S.μ] P0 → (∀ t, Integrable (P t) S.μ) →
      (∀ t, StronglyMeasurable[S.𝓕 t] (P (t + 1))) → Eq25 α P pstar →
      MEq28 S α β w m s P pstar → L1Fwd S α β (costTerm m w s P) →
      ∀ t, P t =ᵐ[S.μ] PM S α β w m s P0 t ∧ pstar t =ᵐ[S.μ] pstarM S α β w m s P0 t := by
  have hex := prop34_exists_measure S (m := m) hα0 hα1 hβ0 hβ1 hw hsm hs0 hK0 hsb hP0m hP0i
  refine ⟨hex, fun P pstar h0 hPi hpre h25 h28 hL => ?_⟩
  obtain ⟨e0, hPi', hpre', h25', h28', hL'⟩ := hex
  exact prop34_unique_of_w_neg_L1 S hα0 hα1 hβ0 hβ1 hwneg hw (integrable_s S hsm hs0 hsb) hPi
    hPi' hpre hpre' (by rw [e0]; exact h0) h25 h25' h28 h28' hL hL'

end Woodford.NominalRigidities.TidyR5Prop34MeasureExists
