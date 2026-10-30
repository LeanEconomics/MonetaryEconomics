/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdCIA
import Monetarism.HouseholdMeasureTVC

/-!
# Necessity of the transversality condition without boundedness

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, p. 439 ("their optimal
choices include transversality conditions") and (19.28), p. 449, on a probability space. The
earlier theorem `HouseholdMeasureTVC.tvc_of_optimal` assumed regular prices, consumption, real
balances, claims, endowment and taxes bounded at each date, and the normalised first-order
condition `βᵀ(u_c + ϑu_m) = Λ_Tw_T`. Here none of the bounds is needed.

## The Kamihigashi deviation as an increment

`kdc`, `kda`: from date `T` on, the household consumes the freed wealth `x_T = k_T/w_T` at `T`
(`kx`; `k_T` is `HouseholdMeasureTVC.kOut`) along the bundle `(1, ϑ)` and moves `(c, m)` to the
reference plan `(cRef, mRef)` after `T`, financing it by bringing only part of its wealth into each
later date; scaled by `θ`, the deviated plan keeps the fraction `1 − θ` of wealth
(`flow_kd`, `kam_feasible_w`, `wealthPV_kd`). Its feasibility uses only integrability.

## Main results

* `concave_chord`, `concave_slope_anti`: chords and slopes of a concave function.
* `lam_kOut`: `E[Λ_Tk_T] = E[pk_{T+1}(a_{T+1} + M_T)]` under `PriceWeak`, with `Λ_Tk_T`
  integrable.
* **`tvc_general`**: at an optimum, if utility is concave and increasing along the bundle,
  differentiable along it at the plan, the first-order condition `βᵀ(u_c + ϑu_m) = λΛ_Tw_T` holds
  with a constant `λ > 0`, the reference plan is admissible and has finite cost, and a Kamihigashi
  step of size `θ₀` has integrable utility at each date, then `E[pk_T(a_T + M_{T−1})] → 0`. No
  bound on prices, consumption, real balances, claims, endowment or taxes. The proof bounds the
  utility gain of the date-`T` step by monotone convergence of concave difference quotients, so
  no differentiation under the integral sign is needed.
* `integrable_pk_succ_mul`: with `Q_n ≤ 1`, `Λ_ng` integrable implies `pk_{n+1}P_ng` integrable
  (truncation, pull-out and Fatou).
* `miu_tvc`: for the money-in-utility household (`ϑ = 0`) with a utility `C¹` on an open domain,
  concave and increasing in consumption along every whole line `e ↦ u(x + e, z)` in `ℝ²` (so `u`
  must be concave outside the domain too; `TidyR6HouseholdTVCDom.miu_tvc_dom` removes this), and
  `u_c > 0` at date `0`, the multiplier and all the integrability conditions are derived; what
  remains is the admissible reference plan (which
  `TidyR6HouseholdTVCCx.tvc_needs_reference` shows cannot be dropped), the integrability of a
  Kamihigashi step and the domain allowing the deviations.
* `cia_tvc`: for the cash-in-advance household, the multiplier, `λ > 0`, `Q_t ≤ 1`, the bound
  `w_t ≥ min(1, 1/V)` and all the integrability conditions are derived; no bounds, no `Q ≤ 1`,
  overnight money only positive (not bounded away from zero), no normalisation.
-/

namespace Cochrane.Monetarism.TidyR6HouseholdTVC

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  HouseholdMeasureTVC TidyR6HouseholdRoll TidyR6HouseholdSuff

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### The Kamihigashi increment -/

variable (S) in
/-- Cochrane (2023), (19.28), p. 449: the freed wealth per unit of bundle cost, `x_T = k_T/w_T`. -/
noncomputable def kx (ϑ : ℝ) (Λ P a m : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  kOut S Λ P a m T ω / wedge S ϑ Λ P T ω

variable (S) in
/-- Cochrane (2023), p. 439 (the Kamihigashi deviation, per unit of `θ`): the change in
consumption: nothing before `T`, `x_T` at `T`, `cRef − c` after `T`. Real balances change by `ϑ`
times it. -/
noncomputable def kdc (ϑ : ℝ) (Λ P y s a c m : ℕ → Ω → ℝ) (T : ℕ) : ℕ → Ω → ℝ :=
  fun n ω => if n < T then 0 else if n = T then kx S ϑ Λ P a m T ω
    else cRef S ϑ Λ P y s c m n ω - c n ω

variable (S) in
/-- Cochrane (2023), p. 439 (the Kamihigashi deviation, per unit of `θ`): the change in claims:
nothing up to `T`, then minus the wealth `a_n + M_{n−1}` and minus the extra money carried in. -/
noncomputable def kda (ϑ : ℝ) (Λ P y s a c m : ℕ → Ω → ℝ) (N0 : Ω → ℝ) (T : ℕ) :
    ℕ → Ω → ℝ :=
  fun n ω => if n ≤ T then 0 else -(a n ω + moneyIn N0 P m n ω) -
    moneyIn 0 P (fun k ω => ϑ * kdc S ϑ Λ P y s a c m T k ω) n ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 439: the extra money brought into `n` by the increment. -/
theorem moneyIn_kd (ϑ : ℝ) (P : ℕ → Ω → ℝ) (d : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    moneyIn 0 P (fun k ω => ϑ * d k ω) n ω =
      if n = 0 then 0 else P (n - 1) ω * (ϑ * d (n - 1) ω) := by
  cases n with
  | zero => simp [moneyIn]
  | succ k => simp [moneyIn]

/-- Cochrane (2023), p. 439: the freed wealth per unit of bundle cost is known at `T`. -/
theorem sm_kx {ϑ : ℝ} {Λ P a m : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    (hma : StronglyAdapted S.𝓕 m) (T : ℕ) : StronglyMeasurable[S.𝓕 T] (kx S ϑ Λ P a m T) := by
  have hcc : StronglyMeasurable[S.𝓕 T] (claimCost S Λ P a T) :=
    ((S.stronglyMeasurable_E T _).measurable.div (hp.sm_pk T).measurable).stronglyMeasurable
  have hw : StronglyMeasurable[S.𝓕 T] (wedge S ϑ Λ P T) :=
    stronglyMeasurable_const.add ((hp.sm_iota T).const_mul ϑ)
  exact ((((hcc.add ((hp.sm_bondPrice T).mul ((hp.2.1 T).mul (hma T)))).measurable.div
    (hp.2.1 T).measurable)).div hw.measurable).stronglyMeasurable

/-- Cochrane (2023), p. 439: the reference consumption is known at each date. -/
theorem sm_cRef {ϑ : ℝ} {Λ P y s c m : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s) (hca : StronglyAdapted S.𝓕 c)
    (hma : StronglyAdapted S.𝓕 m) (n : ℕ) :
    StronglyMeasurable[S.𝓕 n] (cRef S ϑ Λ P y s c m n) := by
  have hw : StronglyMeasurable[S.𝓕 n] (wedge S ϑ Λ P n) :=
    stronglyMeasurable_const.add ((hp.sm_iota n).const_mul ϑ)
  exact ((hca n).add (((((hya n).sub (hsa n)).sub (hca n)).sub
    ((hp.sm_iota n).mul (hma n))).measurable.div hw.measurable).stronglyMeasurable)

/-- Cochrane (2023), p. 439: the consumption increment is adapted. -/
theorem sm_kdc {ϑ : ℝ} {Λ P y s a c m : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s) (hca : StronglyAdapted S.𝓕 c)
    (hma : StronglyAdapted S.𝓕 m) (T n : ℕ) :
    StronglyMeasurable[S.𝓕 n] (kdc S ϑ Λ P y s a c m T n) := by
  by_cases h1 : n < T
  · have e : kdc S ϑ Λ P y s a c m T n = fun _ => 0 := by funext ω; simp [kdc, h1]
    rw [e]
    exact stronglyMeasurable_const
  · by_cases h2 : n = T
    · subst h2
      have e : kdc S ϑ Λ P y s a c m n n = kx S ϑ Λ P a m n := by funext ω; simp [kdc]
      rw [e]
      exact sm_kx hp hma n
    · have e : kdc S ϑ Λ P y s a c m T n = fun ω => cRef S ϑ Λ P y s c m n ω - c n ω := by
        funext ω
        simp [kdc, h1, h2]
      rw [e]
      exact (sm_cRef hp hya hsa hca hma n).sub (hca n)

/-- Cochrane (2023), (19.12), p. 439 and (19.28), p. 449 (`HouseholdMeasureTVC.pv_wealth_next`
under `PriceWeak`): for a feasible plan `Λ_Tk_T` is integrable and
`E[Λ_Tk_T] = E[pk_{T+1}(a_{T+1} + M_T)]`. -/
theorem lam_kOut {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a) (T : ℕ) :
    Integrable (fun ω => Λ T ω * kOut S Λ P a m T ω) S.μ ∧
      ∫ ω, Λ T ω * kOut S Λ P a m T ω ∂S.μ = wealthPV S Λ P N0 m a (T + 1) := by
  have hia := hf.2.2.2.2.2.1
  have hiN := hf.2.2.2.2.2.2.1
  have hzm : StronglyMeasurable[S.𝓕 T] (fun ω => P T ω * m T ω) := (hp.2.1 T).mul (hf.2.2.1 T)
  have hNi : Integrable ((fun ω => P T ω * m T ω) * pk Λ P (T + 1)) S.μ :=
    (hiN (T + 1)).congr (Eventually.of_forall fun ω => by simp only [moneyIn, Pi.mul_apply]; ring)
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := S.μ) (m := S.𝓕 T) hzm hNi
    (hp.2.2.2.2 (T + 1))
  have e : (fun ω => Λ T ω * kOut S Λ P a m T ω) = fun ω =>
      S.E T (fun ω => pk Λ P (T + 1) ω * a (T + 1) ω) ω +
        (P T ω * m T ω) * S.E T (pk Λ P (T + 1)) ω := by
    funext ω
    have h1 := (hp.pk_pos T ω).ne'
    have h2 := (hp.2.2.2.1 T ω).ne'
    rw [hp.E_pk_eq T ω, ← hp.pk_mul_P T ω]
    simp only [kOut, claimCost]
    field_simp
  have i2 : Integrable (fun ω => (P T ω * m T ω) * S.E T (pk Λ P (T + 1)) ω) S.μ :=
    integrable_condExp.congr hpull
  refine ⟨by rw [e]; exact (S.integrable_E T _).add i2, ?_⟩
  rw [e, integral_add (S.integrable_E T _) i2, S.integral_E]
  have h3 : ∫ ω, (P T ω * m T ω) * S.E T (pk Λ P (T + 1)) ω ∂S.μ =
      ∫ ω, (P T ω * m T ω) * pk Λ P (T + 1) ω ∂S.μ := by
    have := integral_congr_ae hpull
    rw [integral_condExp (S.𝓕.le T)] at this
    exact this.symm
  have hNi' : Integrable (fun ω => (P T ω * m T ω) * pk Λ P (T + 1) ω) S.μ := hNi
  rw [h3, ← integral_add (hia (T + 1)) hNi']
  exact integral_congr_ae (Eventually.of_forall fun ω => by
    simp only [moneyIn]
    ring)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), (19.10), p. 439: dividing the value of the claims by `pk_t`,
`(−A − X(Qk))/k = −A/k − XQ` for `k ≠ 0`. -/
theorem div_split {A X Q k : ℝ} (hk : k ≠ 0) : (-A - X * (Q * k)) / k = -(A / k) - X * Q := by
  field_simp

/-- Cochrane (2023), (19.10), p. 439: the date-`n` value of the claims of the increment maturing
at `n + 1`, for `n ≥ T`:
`E_n[pk_{n+1}da_{n+1}] = −E_n[pk_{n+1}a_{n+1}] − (P_nm_n + P_nϑdc_n)E_n[pk_{n+1}]`
almost surely (pull-out with integrability only). -/
theorem E_pk_kda {ϑ : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s) {T n : ℕ} (hn : T ≤ n)
    (hIM : Integrable (fun ω => pk Λ P (n + 1) ω *
      (P n ω * (ϑ * kdc S ϑ Λ P y s a c m T n ω))) S.μ) :
    ∀ᵐ ω ∂S.μ, S.E n (fun ω => pk Λ P (n + 1) ω * kda S ϑ Λ P y s a c m N0 T (n + 1) ω) ω =
      -(S.E n (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) ω) -
        (P n ω * m n ω + P n ω * (ϑ * kdc S ϑ Λ P y s a c m T n ω)) *
          S.E n (pk Λ P (n + 1)) ω := by
  have hia := hf.2.2.2.2.2.1
  have hiN := hf.2.2.2.2.2.2.1
  set f : Ω → ℝ := fun ω => P n ω * m n ω + P n ω * (ϑ * kdc S ϑ Λ P y s a c m T n ω) with hfdef
  have hfm : StronglyMeasurable[S.𝓕 n] f := ((hp.2.1 n).mul (hf.2.2.1 n)).add
    ((hp.2.1 n).mul ((sm_kdc hp hya hsa hf.2.1 hf.2.2.1 T n).const_mul ϑ))
  have hfi : Integrable (f * pk Λ P (n + 1)) S.μ := by
    have h1 : Integrable (fun ω => pk Λ P (n + 1) ω * moneyIn N0 P m (n + 1) ω) S.μ := hiN (n + 1)
    refine (h1.add hIM).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, Pi.mul_apply, moneyIn, hfdef]
    ring
  have e : (fun ω => pk Λ P (n + 1) ω * kda S ϑ Λ P y s a c m N0 T (n + 1) ω) =
      -(fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) - f * pk Λ P (n + 1) := by
    funext ω
    simp only [kda, show ¬ n + 1 ≤ T by omega, ↓reduceIte, moneyIn, Pi.sub_apply, Pi.neg_apply,
      Pi.mul_apply, hfdef]
    ring
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := S.μ) (m := S.𝓕 n) hfm hfi
    (hp.2.2.2.2 (n + 1))
  rw [e]
  filter_upwards [S.E_sub (hia (n + 1)).neg hfi n, hpull,
    condExp_neg (μ := S.μ) (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) (S.𝓕 n)] with ω h1 h2 h3
  rw [h1, Pi.sub_apply]
  change S.μ[-(fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) | S.𝓕 n] ω -
    S.μ[f * pk Λ P (n + 1) | S.𝓕 n] ω = _
  rw [h3, h2, Pi.neg_apply, Pi.mul_apply]

/-- Cochrane (2023), (19.10), p. 439 and p. 439 ("their optimal choices include transversality
conditions"), **the Kamihigashi increment satisfies the homogeneous flow constraint**, almost
surely at every date, for a feasible plan, `PriceWeak` prices, adapted endowment and taxes,
nonzero bundle costs, and integrable money values of the increment. No bounds. -/
theorem flow_kd {ϑ : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s) (hw : ∀ n, ∀ᵐ ω ∂S.μ, wedge S ϑ Λ P n ω ≠ 0) (T : ℕ)
    (hIM : ∀ n, Integrable (fun ω => pk Λ P (n + 1) ω *
      (P n ω * (ϑ * kdc S ϑ Λ P y s a c m T n ω))) S.μ) :
    Flow S Λ P 0 0 0 (kdc S ϑ Λ P y s a c m T) (fun n ω => ϑ * kdc S ϑ Λ P y s a c m T n ω)
      (kda S ϑ Λ P y s a c m N0 T) := by
  have hflow := hf.2.2.2.2.1
  intro n
  rcases lt_trichotomy n T with h | h | h
  · -- before `T` nothing changes
    have e1 : (fun ω => pk Λ P (n + 1) ω * kda S ϑ Λ P y s a c m N0 T (n + 1) ω) = 0 := by
      funext ω
      simp [kda, show n + 1 ≤ T by omega]
    refine Eventually.of_forall fun ω => ?_
    rw [show claimCost S Λ P (kda S ϑ Λ P y s a c m N0 T) n ω = S.E n (fun ω => pk Λ P (n + 1) ω *
      kda S ϑ Λ P y s a c m N0 T (n + 1) ω) ω / pk Λ P n ω from rfl, e1, S.E_zero, moneyIn_kd]
    have hk : ∀ k, k < T → kdc S ϑ Λ P y s a c m T k ω = 0 := fun k hk => by simp [kdc, hk]
    simp only [kda, show n ≤ T by omega, ↓reduceIte, hk n h, Pi.zero_apply]
    split_ifs with h0
    · simp
    · rw [hk (n - 1) (by omega)]
      simp
  · -- the date of the deviation
    subst h
    filter_upwards [E_pk_kda (N0 := N0) hp hf hya hsa le_rfl (hIM n), hw n] with ω h1 hwn
    rw [show claimCost S Λ P (kda S ϑ Λ P y s a c m N0 n) n ω = S.E n (fun ω => pk Λ P (n + 1) ω *
      kda S ϑ Λ P y s a c m N0 n (n + 1) ω) ω / pk Λ P n ω from rfl, h1, moneyIn_kd,
      hp.E_pk_eq n ω]
    have hk : ∀ k, k < n → kdc S ϑ Λ P y s a c m n k ω = 0 := fun k hk => by simp [kdc, hk]
    have hkn : kdc S ϑ Λ P y s a c m n n ω = kx S ϑ Λ P a m n ω := by simp [kdc]
    have hkx : kx S ϑ Λ P a m n ω * wedge S ϑ Λ P n ω = kOut S Λ P a m n ω :=
      div_mul_cancel₀ _ hwn
    have hpk := (hp.pk_pos n ω).ne'
    have hP := (hp.2.2.2.1 n ω).ne'
    have hkO : kOut S Λ P a m n ω * P n ω = S.E n (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) ω /
        pk Λ P n ω + bondPrice S Λ P n ω * (P n ω * m n ω) := by
      simp only [kOut, claimCost]
      field_simp
    have hw' : wedge S ϑ Λ P n ω = 1 + ϑ * (1 - bondPrice S Λ P n ω) := rfl
    rw [div_split hpk]
    rw [← hkx, hw'] at hkO
    simp only [kda, le_refl, ↓reduceIte, hkn, Pi.zero_apply]
    split_ifs with h0
    · linear_combination (-1 : ℝ) * hkO
    · rw [hk (n - 1) (by omega)]
      linear_combination (-1 : ℝ) * hkO
  · -- after the deviation
    filter_upwards [E_pk_kda (N0 := N0) hp hf hya hsa h.le (hIM n), hw n, hflow n] with
      ω h1 hwn hfl
    rw [show claimCost S Λ P (kda S ϑ Λ P y s a c m N0 T) n ω = S.E n (fun ω => pk Λ P (n + 1) ω *
      kda S ϑ Λ P y s a c m N0 T (n + 1) ω) ω / pk Λ P n ω from rfl, h1, moneyIn_kd,
      hp.E_pk_eq n ω]
    have hkn : kdc S ϑ Λ P y s a c m T n ω = cRef S ϑ Λ P y s c m n ω - c n ω := by
      simp [kdc, show ¬ n < T by omega, show n ≠ T by omega]
    have hd : (cRef S ϑ Λ P y s c m n ω - c n ω) * wedge S ϑ Λ P n ω =
        y n ω - s n ω - c n ω - iota S Λ P n ω * m n ω := by
      simp only [cRef, add_sub_cancel_left]
      exact div_mul_cancel₀ _ hwn
    have hpk := (hp.pk_pos n ω).ne'
    have hw' : wedge S ϑ Λ P n ω = 1 + ϑ * (1 - bondPrice S Λ P n ω) := rfl
    have hι : iota S Λ P n ω = 1 - bondPrice S Λ P n ω := rfl
    simp only [claimCost] at hfl
    rw [div_split hpk]
    simp only [kda, show ¬ n ≤ T by omega, ↓reduceIte, hkn, Pi.zero_apply,
      show n ≠ 0 by omega, moneyIn_kd]
    rw [hw', hι] at hd
    linear_combination (-1 : ℝ) * hfl + (-P n ω) * hd

/-- Cochrane (2023), (19.28), p. 449: after `T` the increment removes the whole wealth:
`E[pk_n(da_n + dM_{n−1})] = −E[pk_n(a_n + M_{n−1})]` for `n > T`. -/
theorem wealthPV_kd {ϑ : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} {T n : ℕ}
    (hn : T < n) :
    wealthPV S Λ P 0 (fun k ω => ϑ * kdc S ϑ Λ P y s a c m T k ω) (kda S ϑ Λ P y s a c m N0 T) n =
      -wealthPV S Λ P N0 m a n := by
  simp only [wealthPV]
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [kda, show ¬ n ≤ T by omega, ↓reduceIte]
  ring

/-- Cochrane (2023), (19.10), p. 439 and p. 439 ("their optimal choices include transversality
conditions"), **the Kamihigashi deviation is feasible without bounds**: for a feasible plan,
`PriceWeak` prices, adapted endowment and taxes, nonzero bundle costs, and integrable values
`Λ_n dc_n` and `pk_{n+1}P_nϑdc_n` of the increment, the plan `(c + θdc, m + θϑdc, a + θda)` is
feasible for every `0 ≤ θ ≤ 1`; it keeps the fraction `1 − θ` of the date-0 value of wealth after
`T`. -/
theorem kam_feasible_w {ϑ : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s) (hw : ∀ n, ∀ᵐ ω ∂S.μ, wedge S ϑ Λ P n ω ≠ 0) (T : ℕ)
    (hIC : ∀ n, Integrable (fun ω => Λ n ω * kdc S ϑ Λ P y s a c m T n ω) S.μ)
    (hIM : ∀ n, Integrable (fun ω => pk Λ P (n + 1) ω *
      (P n ω * (ϑ * kdc S ϑ Λ P y s a c m T n ω))) S.μ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Feasible S Λ P y s N0 a0 (fun n ω => c n ω + θ * kdc S ϑ Λ P y s a c m T n ω)
      (fun n ω => m n ω + θ * (ϑ * kdc S ϑ Λ P y s a c m T n ω))
      (fun n ω => a n ω + θ * kda S ϑ Λ P y s a c m N0 T n ω) := by
  obtain ⟨ha0, hca, hma, haa, hflow, hia, hiN, him, hic, hnp⟩ := hf
  have hf : Feasible S Λ P y s N0 a0 c m a := ⟨ha0, hca, hma, haa, hflow, hia, hiN, him, hic, hnp⟩
  have hdc := sm_kdc (ϑ := ϑ) (a := a) (T := T) hp hya hsa hca hma
  -- the claims of the increment
  have hdaN : ∀ n, Integrable (fun ω => pk Λ P n ω *
      moneyIn 0 P (fun k ω => ϑ * kdc S ϑ Λ P y s a c m T k ω) n ω) S.μ := by
    intro n
    cases n with
    | zero => simp [moneyIn]
    | succ k => simpa [moneyIn] using hIM k
  have hdia : ∀ n, Integrable (fun ω => pk Λ P n ω * kda S ϑ Λ P y s a c m N0 T n ω) S.μ := by
    intro n
    by_cases hn : n ≤ T
    · simp [kda, hn]
    · refine ((((hia n).add (hiN n)).neg).sub (hdaN n)).congr (Eventually.of_forall fun ω => ?_)
      simp only [kda, hn, ↓reduceIte, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
      ring
  have hdam : StronglyAdapted S.𝓕 (kda S ϑ Λ P y s a c m N0 T) := by
    intro n
    by_cases hn : n ≤ T
    · have e : kda S ϑ Λ P y s a c m N0 T n = fun _ => 0 := by funext ω; simp [kda, hn]
      rw [e]
      exact stronglyMeasurable_const
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have e : kda S ϑ Λ P y s a c m N0 T (k + 1) = fun ω => -(a (k + 1) ω + P k ω * m k ω) -
          P k ω * (ϑ * kdc S ϑ Λ P y s a c m T k ω) := by
        funext ω
        simp [kda, hn, moneyIn]
      rw [e]
      have hle : S.𝓕 k ≤ S.𝓕 (k + 1) := S.𝓕.mono (Nat.le_succ k)
      exact ((haa (k + 1)).add (((hp.2.1 k).mul (hma k)).mono hle)).neg.sub
        (((hp.2.1 k).mul ((hdc k).const_mul ϑ)).mono hle)
  refine ⟨?_, fun n => (hca n).add ((hdc n).const_mul θ),
    fun n => (hma n).add (((hdc n).const_mul ϑ).const_mul θ),
    fun n => (haa n).add ((hdam n).const_mul θ),
    flow_add hp hflow (flow_kd hp hf hya hsa hw T hIM) hia hdia θ, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n => ?_, fun δ hδ => ?_⟩
  · funext ω
    simp [kda, ← ha0]
  · refine ((hia n).add ((hdia n).const_mul θ)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · refine ((hiN n).add ((hdaN n).const_mul θ)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, moneyIn_add]
    ring
  · refine ((him n).add (((hIC n).const_mul ϑ).const_mul θ)).congr
      (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · refine ((hic n).add ((hIC n).const_mul θ)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · filter_upwards [hnp δ hδ, eventually_gt_atTop T] with n h1' hn
    rw [wealthPV_add (hia n) (hiN n) (hdia n) (hdaN n) θ, wealthPV_kd hn]
    nlinarith

/-- Cochrane (2023), (19.15), p. 441 (`Q_t ≤ 1`: a dollar tomorrow is worth at most a dollar
today): if `g` is known at `n`, `Λ_ng` is integrable and `Q_n ≤ 1`, then the date-0 value of the
money `P_ng` carried into `n + 1`, `pk_{n+1}P_ng`, is integrable. Truncation, the pull-out
property and Fatou's lemma: `E|pk_{n+1}P_ng| = E[Q_nΛ_n|g|] ≤ E|Λ_ng|`. -/
theorem integrable_pk_succ_mul {Λ P : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P) {n : ℕ} {g : Ω → ℝ}
    (hg : StronglyMeasurable[S.𝓕 n] g) (hgi : Integrable (fun ω => Λ n ω * g ω) S.μ)
    (hQ : ∀ᵐ ω ∂S.μ, bondPrice S Λ P n ω ≤ 1) :
    Integrable (fun ω => pk Λ P (n + 1) ω * (P n ω * g ω)) S.μ := by
  set h : Ω → ℝ := fun ω => P n ω * g ω with hhdef
  have hhm : StronglyMeasurable[S.𝓕 n] h := (hp.2.1 n).mul hg
  set cl : ℕ → Ω → ℝ := fun k ω => max (min (h ω) k) (-k) with hcl
  have hclm : ∀ k : ℕ, StronglyMeasurable[S.𝓕 n] (cl k) := fun k =>
    ((hhm.measurable.min measurable_const).max measurable_const).stronglyMeasurable
  have hclb : ∀ (k : ℕ) ω, |cl k ω| ≤ k := fun k ω => by
    simp only [hcl]
    rw [abs_le]
    constructor
    · exact le_max_right _ _
    · exact max_le (min_le_right _ _) (by linarith [k.cast_nonneg (α := ℝ)])
  have hcl_le : ∀ (k : ℕ) ω, |cl k ω| ≤ |h ω| := fun k ω => by
    simp only [hcl]
    rw [abs_le]
    constructor
    · have := neg_abs_le (h ω)
      have h1 : -|h ω| ≤ min (h ω) k := le_min this (by
        linarith [abs_nonneg (h ω), k.cast_nonneg (α := ℝ)])
      exact h1.trans (le_max_left _ _)
    · exact max_le ((min_le_left _ _).trans (le_abs_self _)) (by
        linarith [abs_nonneg (h ω), k.cast_nonneg (α := ℝ)])
  have hcl_ev : ∀ ω, ∀ᶠ k : ℕ in atTop, cl k ω = h ω := fun ω => by
    filter_upwards [eventually_ge_atTop ⌈|h ω|⌉₊] with k hk
    have hk' : |h ω| ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rw [abs_le] at hk'
    simp only [hcl, min_eq_left hk'.2, max_eq_left hk'.1]
  have hpk1 := hp.2.2.2.2 (n + 1)
  have hGi : ∀ k : ℕ, Integrable (fun ω => pk Λ P (n + 1) ω * cl k ω) S.μ := fun k =>
    hpk1.mul_bdd ((hclm k).mono (S.𝓕.le n)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hclb k ω)
  -- `Q` lies in `[0, 1]`
  have hQ0 : ∀ᵐ ω ∂S.μ, 0 ≤ S.E n (pk Λ P (n + 1)) ω :=
    condExp_nonneg (Eventually.of_forall fun ω => (hp.pk_pos (n + 1) ω).le)
  have hbound : ∀ k : ℕ, ∫ ω, ‖pk Λ P (n + 1) ω * cl k ω‖ ∂S.μ ≤
      ∫ ω, ‖Λ n ω * g ω‖ ∂S.μ := by
    intro k
    have e1 : ∫ ω, ‖pk Λ P (n + 1) ω * cl k ω‖ ∂S.μ =
        ∫ ω, |cl k ω| * pk Λ P (n + 1) ω ∂S.μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hp.pk_pos (n + 1) ω), mul_comm]
    have hz : StronglyMeasurable[S.𝓕 n] (fun ω => |cl k ω|) :=
      (continuous_abs.measurable.comp (hclm k).measurable).stronglyMeasurable
    rw [e1, integral_mul_E hz (K := k) (Eventually.of_forall fun ω => by
      rw [abs_abs]; exact hclb k ω) hpk1]
    refine integral_mono_ae ?_ hgi.norm ?_
    · exact (S.integrable_E n (pk Λ P (n + 1))).bdd_mul (c := k)
        ((hz.mono (S.𝓕.le n)).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_abs]; exact hclb k ω)
    · filter_upwards [hQ, hQ0] with ω h1 h2
      have hk := (hp.pk_pos n ω)
      have hEq := hp.E_pk_eq n ω
      have hΛ : Λ n ω * g ω = pk Λ P n ω * h ω := by
        rw [← hp.pk_mul_P n ω]
        simp only [hhdef]
        ring
      rw [Real.norm_eq_abs, hΛ, abs_mul, abs_of_pos hk, hEq]
      have hQ0' : 0 ≤ bondPrice S Λ P n ω := by
        rw [hEq] at h2
        exact nonneg_of_mul_nonneg_left h2 hk
      calc |cl k ω| * (bondPrice S Λ P n ω * pk Λ P n ω)
          ≤ |h ω| * (1 * pk Λ P n ω) := mul_le_mul (hcl_le k ω)
            (mul_le_mul_of_nonneg_right h1 hk.le) (by positivity) (abs_nonneg _)
        _ = pk Λ P n ω * |h ω| := by ring
  refine ⟨(hpk1.aestronglyMeasurable.mul ((hhm.mono (S.𝓕.le n)).aestronglyMeasurable)), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hfatou := lintegral_liminf_le' (μ := S.μ) (u := atTop)
    (f := fun (k : ℕ) ω => ‖pk Λ P (n + 1) ω * cl k ω‖ₑ)
    (fun k => (hGi k).aestronglyMeasurable.enorm)
  have hlim : ∀ ω, liminf (fun k : ℕ => ‖pk Λ P (n + 1) ω * cl k ω‖ₑ) atTop =
      ‖pk Λ P (n + 1) ω * h ω‖ₑ := fun ω => by
    rw [Filter.liminf_congr ((hcl_ev ω).mono fun k hk => by rw [hk]), liminf_const]
  simp only [hlim] at hfatou
  refine lt_of_le_of_lt hfatou (lt_of_le_of_lt (Filter.liminf_le_of_le (by isBoundedDefault)
    fun b hb => ?_) (ENNReal.ofReal_lt_top (r := ∫ ω, ‖Λ n ω * g ω‖ ∂S.μ)))
  obtain ⟨k, hk⟩ := hb.exists
  refine hk.trans ?_
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hGi k)]
  exact ENNReal.ofReal_le_ofReal (hbound k)

/-! ### Concave functions along a ray -/

/-- Cochrane (2023), p. 439 (concavity along the bundle): for `g` concave and `0 ≤ θ ≤ t`,
`t > 0`, the chord bound `(1 − θ/t)g(0) + (θ/t)g(tX) ≤ g(θX)`. -/
theorem concave_chord {g : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ g) {θ t X : ℝ} (h0 : 0 ≤ θ)
    (hθt : θ ≤ t) (ht : 0 < t) : (1 - θ / t) * g 0 + θ / t * g (t * X) ≤ g (θ * X) := by
  have ha : 0 ≤ 1 - θ / t := by rw [sub_nonneg, div_le_one ht]; exact hθt
  have hb : 0 ≤ θ / t := div_nonneg h0 ht.le
  have := hc.2 (Set.mem_univ 0) (Set.mem_univ (t * X)) ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at this
  convert this using 2
  field_simp

/-- Cochrane (2023), p. 439: for `g` concave the slope `(g(sX) − g(0))/s` decreases in `s > 0`. -/
theorem concave_slope_anti {g : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ g) {s t X : ℝ} (hs : 0 < s)
    (hst : s ≤ t) : (g (t * X) - g 0) / t ≤ (g (s * X) - g 0) / s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h := concave_chord hc hs.le hst ht (X := X)
  rw [div_le_div_iff₀ ht hs]
  have e : (1 - s / t) * g 0 + s / t * g (t * X) = g 0 + s / t * (g (t * X) - g 0) := by ring
  rw [e] at h
  have h2 : s / t * (g (t * X) - g 0) * t = s * (g (t * X) - g 0) := by field_simp
  nlinarith

/-- Cochrane (2023), (19.13), p. 440: for `g` differentiable at `0` with derivative `V`, the
slopes `(g(θ_kX) − g(0))/θ_k` along `θ_k = t/(k + 1) → 0⁺` converge to `VX`. -/
theorem slope_tendsto {g : ℝ → ℝ} {V : ℝ} (hg : HasDerivAt g V 0) {t : ℝ} (ht : 0 < t) (X : ℝ) :
    Tendsto (fun k : ℕ => (g (t / ((k : ℝ) + 1) * X) - g 0) / (t / ((k : ℝ) + 1))) atTop
      (𝓝 (V * X)) := by
  have hg' : HasDerivAt g V (0 * X) := by simpa using hg
  have hh : HasDerivAt (fun θ : ℝ => g (θ * X)) (V * (1 * X)) 0 :=
    hg'.comp 0 ((hasDerivAt_id 0).mul_const X)
  rw [one_mul] at hh
  have hsl := hh.tendsto_slope_zero_right
  have hθ : Tendsto (fun k : ℕ => t / ((k : ℝ) + 1)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k =>
      Set.mem_Ioi.2 (by positivity)⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul t
    simpa [div_eq_mul_inv] using this
  refine (hsl.comp hθ).congr fun k => ?_
  simp only [Function.comp_apply, zero_add, zero_mul, smul_eq_mul]
  ring

/-- Cochrane (2023), (19.9), p. 439: a utility process dominated by `|f| + |r| + |h|·1_{n = T}`
with `f`, `r` admissible and `h` integrable is admissible. -/
theorem uadm_of_le {β : ℝ} (hβ : 0 < β) {f r f' : ℕ → Ω → ℝ} {h : Ω → ℝ} {T : ℕ}
    (hf : UAdmissible S β f) (hr : UAdmissible S β r) (hh : Integrable h S.μ)
    (hm : ∀ n, AEStronglyMeasurable (f' n) S.μ)
    (hle : ∀ n, ∀ᵐ ω ∂S.μ, |f' n ω| ≤ |f n ω| + |r n ω| + if n = T then |h ω| else 0) :
    UAdmissible S β f' := by
  have hsT : ∀ ω, HasSum (fun n => β ^ n * (if n = T then |h ω| else 0)) (β ^ T * |h ω|) :=
    fun ω => by
      convert hasSum_ite_eq T (β ^ T * |h ω|) using 1
      funext n
      split_ifs with hn
      · rw [hn]
      · ring
  have hsum : ∀ᵐ ω ∂S.μ, HasSum (fun n => β ^ n * (|f n ω| + |r n ω| +
      if n = T then |h ω| else 0))
      (∑' n, β ^ n * |f n ω| + ∑' n, β ^ n * |r n ω| + β ^ T * |h ω|) := by
    filter_upwards [hf.2.1, hr.2.1] with ω h1 h2
    have := (h1.hasSum.add h2.hasSum).add (hsT ω)
    refine this.congr_fun fun n => ?_
    ring
  have hle' : ∀ᵐ ω ∂S.μ, ∀ n, β ^ n * |f' n ω| ≤ β ^ n * (|f n ω| + |r n ω| +
      if n = T then |h ω| else 0) := by
    filter_upwards [ae_all_iff.2 hle] with ω hω n
    exact mul_le_mul_of_nonneg_left (hω n) (pow_nonneg hβ.le n)
  have hs' : ∀ᵐ ω ∂S.μ, Summable fun n => β ^ n * |f' n ω| := by
    filter_upwards [hsum, hle'] with ω h1 h2
    exact Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _)) h2
      h1.summable
  refine ⟨hm, hs', ?_⟩
  refine Integrable.mono' ((hf.2.2.add hr.2.2).add (hh.abs.const_mul (β ^ T)))
    (aestronglyMeasurable_tsum (fun n => ((hm n).norm.const_mul _)) (hs'.mono fun _ h => h)) ?_
  filter_upwards [hsum, hle', hs'] with ω h1 h2 h3
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun n => mul_nonneg (pow_nonneg hβ.le n)
    (abs_nonneg _))]
  simp only [Pi.add_apply]
  rw [← h1.tsum_eq]
  exact h3.tsum_le_tsum h2 h1.summable

/-! ### The transversality condition without bounds -/

/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions") and
(19.28), p. 449, **the transversality condition is necessary, without boundedness.** Let
`(c, m, a)` be optimal (extra constraint `Con`), with prices satisfying only `PriceWeak`, the
endowment and taxes adapted and the bundle cost `w = 1 + ϑι` nonzero. Suppose the period utility
is measurable, concave and increasing along the bundle direction `(1, ϑ)`, differentiable along it
at the plan with derivative `u_c + ϑu_m`, and that the first-order condition
`βᵀ(u_c + ϑu_m) = λΛ_Tw_T` holds with a constant `λ > 0`. Suppose the reference plan (consume the
bundle financed by `y − s`) is admissible and its cost has integrable value, the freed wealth has
integrable value, a Kamihigashi step of size `θ₀ ∈ (0, 1]` has integrable utility at each date,
and `Con` allows the Kamihigashi deviations. Then `E[pk_T(a_T + M_{T−1})] → 0`. No bound on
prices, consumption, real balances, claims, endowment or taxes is used. -/
theorem tvc_general {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {ϑ : ℝ}
    (hum : Measurable fun p : ℝ × ℝ => u p.1 p.2)
    (hconc : ∀ x z, ConcaveOn ℝ Set.univ (fun e => u (x + e) (z + ϑ * e)))
    (hmono : ∀ x z, Monotone (fun e => u (x + e) (z + ϑ * e)))
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
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hstep : ∀ T, Integrable (fun ω => u (c T ω + θ₀ * kx S ϑ Λ P a m T ω)
      (m T ω + ϑ * (θ₀ * kx S ϑ Λ P a m T ω))) S.μ)
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
    have hgint : ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ₀ → Integrable (fun ω => g ω (θ * x ω)) S.μ := by
      intro θ h0 h1
      have hL : Integrable (fun ω => (1 - θ / θ₀) * g ω 0 + θ / θ₀ * g ω (θ₀ * x ω)) S.μ := by
        refine (((hadm.integrable hβ T).const_mul (1 - θ / θ₀)).add
          ((hstep T).const_mul (θ / θ₀))).congr (Eventually.of_forall fun ω => ?_)
        simp only [Pi.add_apply, hg, add_zero, mul_zero, hx]
      have hU : Integrable (fun ω => g ω 0 + θ * (V ω * x ω)) S.μ :=
        ((hadm.integrable hβ T).add (hVxi.const_mul θ)).congr
          (Eventually.of_forall fun ω => by simp only [Pi.add_apply, hg0])
      refine Integrable.mono' (hL.abs.add hU.abs) (hgm θ).aestronglyMeasurable ?_
      filter_upwards [hder T] with ω hdω
      simp only [Pi.add_apply]
      have lo := concave_chord (hconc (c T ω) (m T ω)) h0 h1 hθ₀ (X := x ω)
      have up := MoneyInUtility.concave_le_tangent (hconc (c T ω) (m T ω)) hdω (θ * x ω)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le ((1 - θ / θ₀) * g ω 0 + θ / θ₀ * g ω (θ₀ * x ω)),
          abs_nonneg (g ω 0 + θ * (V ω * x ω))]
      · have : g ω (θ * x ω) ≤ g ω 0 + θ * (V ω * x ω) := by
          simp only [hg] at up ⊢
          simp only [hV]
          nlinarith [up]
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
        · refine Eventually.of_forall fun ω => ?_
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
            have := abs_comb_le (hmono (c n ω) (m n ω)) (a := 0)
              (e := cRef S ϑ Λ P y s c m n ω - c n ω) h0.le hθ1
            simp only [mul_zero, zero_add, add_zero] at this
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
          have hpt : ∀ ω, (1 - θ) * u (c n ω) (m n ω) + θ *
              u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω) ≤ f' n ω := by
            intro ω
            have := (hconc (c n ω) (m n ω)).2 (Set.mem_univ 0)
              (Set.mem_univ (cRef S ϑ Λ P y s c m n ω - c n ω)) (sub_nonneg.2 hθ1) h0.le
              (by ring)
            simp only [smul_eq_mul, mul_zero, zero_add, add_zero] at this
            rw [show c n ω + (cRef S ϑ Λ P y s c m n ω - c n ω) = cRef S ϑ Λ P y s c m n ω by
              ring] at this
            rw [hf'gt n hn ω, hmR n ω]
            exact this
          have hint2 : Integrable (fun ω => (1 - θ) * u (c n ω) (m n ω) + θ *
              u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω)) S.μ :=
            (hi.const_mul (1 - θ)).add (hir.const_mul θ)
          have hmono' := integral_mono hint2 hi' hpt
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
      refine Eventually.of_forall fun ω => monotone_nat_of_le_succ fun k => ?_
      simp only [hq]
      refine concave_slope_anti (hconc (c T ω) (m T ω)) (hθk0 (k + 1)) ?_
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

/-! ### The money-in-utility and cash-in-advance households -/

open TidyR6HouseholdLocal TidyR6HouseholdFOC in
/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions") and
(19.11)–(19.12), p. 439, **the money-in-utility transversality condition without bounds or
normalisation.** For an optimum of the money-in-utility household (utility `C¹` on an open
domain `U`, measurable, concave and increasing along every whole line `e ↦ u(x + e, z)` in `ℝ²`,
so concave outside `U` too; `TidyR6HouseholdTVCDom.miu_tvc_dom` removes this), with `PriceWeak`
prices, adapted endowment and taxes with integrable values, and `u_c > 0` at date `0`: the
multiplier is derived (`TidyR6HouseholdFOC.miu_multiplier`) and positive, and if the reference
plan (consume `y − s − ιm`) is admissible, a Kamihigashi step of size `θ₀` has integrable utility
and the domain allows the deviations, then `E[pk_T(a_T + M_{T−1})] → 0`. -/
theorem miu_tvc {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hu : C1On u uc um U) (hum : Measurable fun p : ℝ × ℝ => u p.1 p.2)
    (hconc : ∀ x z, ConcaveOn ℝ Set.univ (fun e => u (x + e) (z + 0 * e)))
    (hmono : ∀ x z, Monotone (fun e => u (x + e) (z + 0 * e)))
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β u (DomainCon S U) Λ P y s N0 a0 c m a) (hp : PriceWeak S Λ P)
    (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hpos : ∀ᵐ ω ∂S.μ, 0 < uc (c 0 ω) (m 0 ω))
    (href : UAdmissible S β
      (fun n ω => u (cRef S 0 Λ P y s c m n ω) (mRef S 0 Λ P y s c m n ω)))
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hstep : ∀ T, Integrable (fun ω => u (c T ω + θ₀ * kx S 0 Λ P a m T ω)
      (m T ω + 0 * (θ₀ * kx S 0 Λ P a m T ω))) S.μ)
    (hcon : ∀ T θ, 0 < θ → θ < θ₀ → DomainCon S U
      (fun n ω => c n ω + θ * kdc S 0 Λ P y s a c m T n ω)
      (fun n ω => m n ω + θ * (0 * kdc S 0 Λ P y s a c m T n ω))) :
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
  refine tvc_general (ϑ := 0) (uc := uc) (um := um) hβ hum hconc hmono hopt hp hya hsa
    (fun n => Eventually.of_forall fun ω => by rw [hw1]; exact one_ne_zero) hlam0
    (fun T => ?_) (fun T => ?_) href (fun n => ?_) (fun n => ?_) (fun T => ?_) (fun T => ?_)
    hθ₀ hθ₀1 hstep hcon
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

open TidyR6HouseholdCIA in
/-- Cochrane (2023), (19.28), p. 449 ("The household's money and debt demands must also obey the
transversality condition"), **the cash-in-advance transversality condition without bounds.** At an
optimum of the cash-in-advance household (utility `u(c)` on `ℝ`, continuously differentiable,
concave, `u' > 0`; velocity `V > 0`), with only `PriceWeak` prices, adapted endowment and taxes
with integrable values and overnight money positive almost surely: the multiplier, `λ > 0`,
`Q_t ≤ 1` and the bound `w_t ≥ min(1, 1/V)` are derived (`cia_multiplier`, `cia_iota_nonneg`,
`cia_wedge_pos`); if moreover the reference plan has integrable utility and nonnegative money,
and a Kamihigashi step of size `θ₀` has integrable utility and nonnegative money at each date,
then `E[Λ_T(a_T + M_{T−1})/P_T] → 0`. Compared with `CashInAdvanceMeasureTVC.tvc_necessary`, no
bounds, no `Q ≤ 1`, no overnight money bounded away from zero and no normalisation. -/
theorem cia_tvc {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hpos : ∀ x, 0 < u' x) {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ}
    (hopt : Optimal S β (fun x _ => u x) (CIAConD S V Set.univ y) Λ P y s N0 a0 c m a)
    (hp : PriceWeak S Λ P) (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) (hm : ∀ t, ∀ᵐ ω ∂S.μ, 0 < m t ω)
    (href : UAdmissible S β (fun n ω => u (cRef S (1 / V - 1) Λ P y s c m n ω)))
    (hmr : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ mRef S (1 / V - 1) Λ P y s c m n ω)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hstep : ∀ T, Integrable (fun ω => u (c T ω + θ₀ * kx S (1 / V - 1) Λ P a m T ω)) S.μ)
    (hstepm : ∀ T, ∀ᵐ ω ∂S.μ, 0 ≤ m T ω + (1 / V - 1) * (θ₀ * kx S (1 / V - 1) Λ P a m T ω)) :
    Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  set θV : ℝ := 1 / V - 1 with hθV
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hcia := hopt.2.1.1
  have hucont : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have huI : ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt u (u' x) x := fun x _ => hu x
  -- derived: `ι ≥ 0`, the wedge, the multiplier
  have hι : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P t ω := fun t =>
    cia_iota_nonneg hβ isOpen_univ huI hu'.continuousOn hopt hp t
      (Eventually.of_forall fun ω => hpos _)
  have hwl : ∀ t, ∀ᵐ ω ∂S.μ, min 1 (1 / V) ≤ wedge S θV Λ P t ω := fun t =>
    cia_wedge_pos hp hV (hι t)
  have hmin : 0 < min 1 (1 / V) := lt_min one_pos (one_div_pos.2 hV)
  have hw : ∀ t, ∀ᵐ ω ∂S.μ, wedge S θV Λ P t ω ≠ 0 := fun t =>
    (hwl t).mono fun ω h => (lt_of_lt_of_le hmin h).ne'
  obtain ⟨lam, hlam⟩ := cia_multiplier hβ isOpen_univ huI hu'.continuousOn hopt hp
  have hfoc : ∀ t, ∀ᵐ ω ∂S.μ, β ^ t * u' (c t ω) = lam * (Λ t ω * wedge S θV Λ P t ω) :=
    fun t => (hlam t).and (hm t) |>.mono fun ω h => h.1 h.2
  have hlam0 : 0 < lam := by
    obtain ⟨ω, h1, h2⟩ := ((hfoc 0).and (hwl 0)).exists
    rw [pow_zero, one_mul] at h1
    have hw0 := lt_of_lt_of_le hmin h2
    have := hpos (c 0 ω)
    rw [h1] at this
    exact pos_of_mul_pos_left this (mul_pos (hp.2.2.1 0 ω) hw0).le
  -- the inverse wedge is bounded
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
  refine tvc_general (ϑ := θV) (uc := fun x _ => u' x) (um := fun _ _ => 0) hβ
    (hucont.measurable.comp measurable_fst) (fun x _ => ?_)
    (fun x _ a b hab => hmono (by linarith)) hopt hp hya hsa hw hlam0
    (fun T => Eventually.of_forall fun ω => ?_)
    (fun T => (hfoc T).mono fun ω h => by simpa using h) href hRc hRm hXc hXm hθ₀ hθ₀1 hstep
    (fun T θ h0 h1 => ⟨fun n => ?_, fun n => Eventually.of_forall fun ω =>
      ⟨Set.mem_univ _, Set.mem_univ _⟩⟩)
  · refine ⟨convex_univ, fun a _ b _ p q hp' hq' hpq => ?_⟩
    have := hconc.2 (Set.mem_univ (x + a)) (Set.mem_univ (x + b)) hp' hq' hpq
    simp only [smul_eq_mul] at this ⊢
    convert this using 2
    linear_combination (-x) * hpq
  · have h1 : HasDerivAt (fun e : ℝ => c T ω + e) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (c T ω)
    have h2 := (hu (c T ω + 0)).comp (0 : ℝ) h1
    simpa [Function.comp_def] using h2
  · filter_upwards [hcia n, hmr n, hstepm T, hm T] with ω ⟨hc1, hc2⟩ hr hst hmT
    refine ⟨by nlinarith, ?_⟩
    rcases lt_trichotomy n T with hn | hn | hn
    · simp only [kdc, hn, ↓reduceIte, mul_zero, add_zero]
      exact hc2
    · subst hn
      simp only [kdc, lt_irrefl, ↓reduceIte]
      have hθθ : θ / θ₀ ≤ 1 := by rw [div_le_one hθ₀]; exact h1.le
      have e : m n ω + θ * (θV * kx S θV Λ P a m n ω) = (1 - θ / θ₀) * m n ω +
          θ / θ₀ * (m n ω + θV * (θ₀ * kx S θV Λ P a m n ω)) := by
        field_simp
        ring
      rw [e]
      exact add_nonneg (mul_nonneg (by linarith) hc2) (mul_nonneg (by positivity) hst)
    · simp only [kdc, show ¬ n < T by omega, show n ≠ T by omega, ↓reduceIte]
      have e : m n ω + θ * (θV * (cRef S θV Λ P y s c m n ω - c n ω)) =
          (1 - θ) * m n ω + θ * mRef S θV Λ P y s c m n ω := by
        simp only [mRef]
        ring
      rw [e]
      have hθ1 : θ ≤ 1 := (h1.trans_le hθ₀1).le
      exact add_nonneg (mul_nonneg (by linarith) hc2) (mul_nonneg h0.le hr)

end Cochrane.Monetarism.TidyR6HouseholdTVC
