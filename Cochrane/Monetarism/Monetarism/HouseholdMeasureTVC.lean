/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.HouseholdMeasure

/-!
# Conditional present values and the necessity of the transversality condition

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, p. 439,
eqs. (19.11)–(19.12), and §19.5.1, p. 449, eqs. (19.28)–(19.30) ("their optimal choices include
transversality conditions"), for the household problem of `HouseholdMeasure` on a probability
space whose information may grow forever.

## Main results

* `iterate_ae`, `pv_iff_tvc_ae`: if `Z_t = E_tZ_{t+1} + G_t` almost surely with `G_t` known at
  `t`, then `Z_t = ∑_{j<J} E_tG_{t+j} + E_tZ_{t+J}` almost surely, and almost surely
  `∑_{j<J} E_tG_{t+j} → Z_t` iff `E_tZ_{t+J} → 0` (forward iteration with conditional
  expectations, at every date `t`).
* `pv_1911_iff`: the date-`t` present-value budget (19.11) in the money-creation form,
  `Λ_ta_t/P_t = lim E_t∑_j Λ_{t+j}((M_{t+j} − M_{t+j−1})/P_{t+j} + s + c − y)`, holds almost
  surely iff the conditional transversality condition on claims `E_t[Λ_{t+J}a_{t+J}/P_{t+J}] → 0`
  does; `pv_1912_iff`: the interest-cost form (19.12) with `a_t + M_{t−1}` iff the transversality
  condition on claims and money (19.28) does.
* The Kamihigashi scaling deviation (restated and adapted from the Cochrane IntertemporalModel
  project, `HouseholdMeasureTVC.kamC`/`kamB`): from date `T` on, keep the fraction `1 − θ` of
  wealth, consume (in the bundle direction `(1, ϑ)`) the freed wealth `θk_T/w_T` at `T`, and from
  `T + 1` on move `(c, m)` the fraction `θ` of the way to the reference plan `(cRef, mRef)`
  financed by the endowment net of taxes (`kam_feasible`).
* `tvc_key`, `tail_tendsto`: at an optimum (bundle-concave, bundle-monotone utility, regular
  prices, everything bounded at each date, reference plan admissible),
  `βᵀE[(u_c + ϑu_m)(c_T, m_T)k_T/w_T] ≤ E[tail_T] → 0`.
* `pv_wealth_next`: `E[Λ_Tk_T] = E[pk_{T+1}(a_{T+1} + M_T)]`.
* `tvc_of_optimal`: hence, with the first-order condition `βᵀ(u_c + ϑu_m) = Λ_Tw_T`, **the
  transversality condition is necessary**: `E[pk_T(a_T + M_{T−1})] → 0`.
-/

namespace Cochrane.Monetarism.HouseholdMeasureTVC

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Forward iteration with conditional expectations -/

/-- Cochrane (2023), (19.11)–(19.12), p. 439 (iterating the budget forward under uncertainty):
if `Z_t = E_tZ_{t+1} + G_t` almost surely with `Z`, `G` integrable and `G_t` known at `t`, then
`Z_t = ∑_{j<J} E_tG_{t+j} + E_tZ_{t+J}` almost surely, for every horizon `J`. -/
theorem iterate_ae {Z G : ℕ → Ω → ℝ} (hZi : ∀ t, Integrable (Z t) S.μ)
    (hGi : ∀ t, Integrable (G t) S.μ) (hGm : ∀ t, StronglyMeasurable[S.𝓕 t] (G t))
    (hrec : ∀ t, Z t =ᵐ[S.μ] S.E t (Z (t + 1)) + G t) (t J : ℕ) :
    Z t =ᵐ[S.μ] (fun ω => ∑ j ∈ Finset.range J, S.E t (G (t + j)) ω) + S.E t (Z (t + J)) := by
  induction J with
  | zero =>
    have hm : AEStronglyMeasurable[S.𝓕 t] (Z t) S.μ :=
      ((S.stronglyMeasurable_E t _).add (hGm t)).aestronglyMeasurable.congr (hrec t).symm
    filter_upwards [S.E_of_aestronglyMeasurable hm (hZi t)] with ω h
    simp [h]
  | succ J ih =>
    have h1 := S.E_congr (hrec (t + J)) t
    have h2 := S.E_add (S.integrable_E (t + J) (Z (t + J + 1))) (hGi (t + J)) t
    have h3 := S.E_tower (Nat.le_add_right t J) (Z (t + J + 1))
    filter_upwards [ih, h1, h2, h3] with ω e0 e1 e2 e3
    rw [e0, Pi.add_apply, e1, e2, Pi.add_apply, e3]
    simp only [Pi.add_apply, Finset.sum_range_succ, show t + (J + 1) = t + J + 1 by ring]
    ring

/-- Cochrane (2023), (19.11)–(19.12), p. 439 and (19.28), p. 449 (valuation iff transversality,
under uncertainty): under the hypotheses of `iterate_ae`, almost surely the partial sums
`∑_{j<J} E_tG_{t+j}` converge to `Z_t` if and only if `E_tZ_{t+J} → 0`. -/
theorem pv_iff_tvc_ae {Z G : ℕ → Ω → ℝ} (hZi : ∀ t, Integrable (Z t) S.μ)
    (hGi : ∀ t, Integrable (G t) S.μ) (hGm : ∀ t, StronglyMeasurable[S.𝓕 t] (G t))
    (hrec : ∀ t, Z t =ᵐ[S.μ] S.E t (Z (t + 1)) + G t) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (Tendsto (fun J => ∑ j ∈ Finset.range J, S.E t (G (t + j)) ω) atTop
        (𝓝 (Z t ω)) ↔ Tendsto (fun J => S.E t (Z (t + J)) ω) atTop (𝓝 0)) := by
  filter_upwards [ae_all_iff.2 fun J => iterate_ae hZi hGi hGm hrec t J] with ω h
  have e : ∀ J, ∑ j ∈ Finset.range J, S.E t (G (t + j)) ω = Z t ω - S.E t (Z (t + J)) ω :=
    fun J => by
      have := h J
      simp only [Pi.add_apply] at this
      linarith
  simp_rw [e]
  constructor
  · intro hl
    have := (tendsto_const_nhds (x := Z t ω)).sub hl
    simpa using this
  · intro hl
    have := (tendsto_const_nhds (x := Z t ω)).sub hl
    simpa using this

/-! ### The date-`t` present-value budget constraints (19.11)–(19.12) -/

/-- Cochrane (2023), eq. (19.11), p. 439 and (19.29), p. 449: the date-`t` term of the
money-creation form, `Λ_t((M_t − M_{t−1})/P_t + s_t + c_t − y_t)`. -/
noncomputable def flowB (Λ P y s : ℕ → Ω → ℝ) (N0 : Ω → ℝ) (c m : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  Λ t ω * (m t ω - moneyIn N0 P m t ω / P t ω + s t ω + c t ω - y t ω)

/-- Cochrane (2023), (19.10), p. 439: multiplying the flow constraint by `pk_t`,
`pk_ta_t + pk_tM_{t−1} + Λ_t(y_t − c_t) = E_t[pk_{t+1}a_{t+1}] + Λ_tm_t + Λ_ts_t` almost
surely. -/
theorem flow_pk {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, pk Λ P t ω * a t ω + pk Λ P t ω * moneyIn N0 P m t ω +
      Λ t ω * y t ω - Λ t ω * c t ω = S.E t (fun ω => pk Λ P (t + 1) ω * a (t + 1) ω) ω +
        Λ t ω * m t ω + Λ t ω * s t ω := by
  filter_upwards [hf.2.2.2.2.1 t] with ω h
  have hk := (hp.pk_pos t ω).ne'
  have hΛ := (hp.pk_mul_P t ω).symm
  simp only [claimCost] at h
  rw [hΛ]
  have := congrArg (fun x => pk Λ P t ω * x) h
  field_simp at this
  linear_combination this

/-- Cochrane (2023), eq. (19.11), p. 439 and (19.29), p. 449, **the date-`t` present-value budget
in the money-creation form, on a probability space**: for a feasible plan (endowment and taxes
adapted, `Λy`, `Λs` integrable), almost surely
`Λ_ta_t/P_t = lim_J ∑_{j<J} E_t[Λ_{t+j}((M_{t+j} − M_{t+j−1})/P_{t+j} + s + c − y)]` iff the
conditional transversality condition on claims `E_t[Λ_{t+J}a_{t+J}/P_{t+J}] → 0` holds (dividing
by `Λ_t > 0` gives the book's form). -/
theorem pv_1911_iff {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s) (hN0 : StronglyMeasurable[S.𝓕 0] N0)
    (hf : Feasible S Λ P y s N0 a0 c m a) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (Tendsto (fun J => ∑ j ∈ Finset.range J,
        S.E t (flowB Λ P y s N0 c m (t + j)) ω) atTop (𝓝 (pk Λ P t ω * a t ω)) ↔
      Tendsto (fun J => S.E t (fun ω => pk Λ P (t + J) ω * a (t + J) ω) ω) atTop (𝓝 0)) := by
  obtain ⟨-, hca, hma, -, -, hia, hiN, him, hic, -⟩ := id hf
  have hmIn : ∀ n, StronglyMeasurable[S.𝓕 n] (moneyIn N0 P m n) := by
    intro n
    cases n with
    | zero => exact hN0
    | succ k => exact ((hp.2.1 k).mul (hma k)).mono (S.𝓕.mono (Nat.le_succ k))
  have hG : ∀ n, flowB Λ P y s N0 c m n = fun ω => Λ n ω * m n ω -
      pk Λ P n ω * moneyIn N0 P m n ω + Λ n ω * s n ω + Λ n ω * c n ω - Λ n ω * y n ω := by
    intro n
    funext ω
    have := (hp.2.2.2.1 n ω).ne'
    simp only [flowB, pk]
    field_simp
  refine pv_iff_tvc_ae (Z := fun n ω => pk Λ P n ω * a n ω) hia (fun n => ?_) (fun n => ?_)
    (fun n => ?_) t
  · rw [hG]
    exact (((((him n).sub (hiN n)).add (hs n)).add (hic n)).sub (hy n))
  · rw [hG]
    exact (((((hp.1 n).mul (hma n)).sub ((hp.stronglyMeasurable_pk n).mul (hmIn n))).add
      ((hp.1 n).mul (hsa n))).add ((hp.1 n).mul (hca n))).sub ((hp.1 n).mul (hya n))
  · filter_upwards [flow_pk hp hf n] with ω h
    rw [hG]
    simp only [Pi.add_apply]
    linarith

/-- Cochrane (2023), eq. (19.12), p. 439 and (19.30), p. 449, **the date-`t` present-value budget
in the interest-cost form, on a probability space**: for a feasible plan (endowment and taxes
adapted, `Λy`, `Λs` integrable), almost surely
`Λ_t(a_t + M_{t−1})/P_t = lim_J ∑_{j<J} E_t[Λ_{t+j}(c + i/(1 + i)·m + s − y)_{t+j}]` iff the
conditional transversality condition (19.28) on claims and money
`E_t[Λ_{t+J}(a_{t+J} + M_{t+J−1})/P_{t+J}] → 0` holds. -/
theorem pv_1912_iff {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s) (hf : Feasible S Λ P y s N0 a0 c m a) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (Tendsto (fun J => ∑ j ∈ Finset.range J,
        S.E t (outlay S Λ P y s c m (t + j)) ω) atTop
          (𝓝 (pk Λ P t ω * (a t ω + moneyIn N0 P m t ω))) ↔
      Tendsto (fun J => S.E t (fun ω => pk Λ P (t + J) ω *
        (a (t + J) ω + moneyIn N0 P m (t + J) ω)) ω) atTop (𝓝 0)) := by
  obtain ⟨-, hca, hma, -, -, hia, hiN, -, -, -⟩ := id hf
  refine pv_iff_tvc_ae (Z := fun n ω => pk Λ P n ω * (a n ω + moneyIn N0 P m n ω))
    (fun n => ((hia n).add (hiN n)).congr (Eventually.of_forall fun ω => by
      simp only [Pi.add_apply]; ring))
    (fun n => (wealth_step hp hy hs hf n).1) (fun n => ?_) (fun n => ?_) t
  · exact ((hp.1 n).mul ((((hca n).add ((hp.stronglyMeasurable_iota n).mul (hma n))).add
      (hsa n)).sub (hya n)))
  · have hNm : StronglyMeasurable[S.𝓕 n] (fun ω => P n ω * m n ω) := (hp.2.1 n).mul (hma n)
    have hNi : Integrable ((fun ω => P n ω * m n ω) * pk Λ P (n + 1)) S.μ :=
      (hiN (n + 1)).congr (Eventually.of_forall fun ω => by
        simp only [moneyIn, Pi.mul_apply]
        ring)
    have hpull : S.E n ((fun ω => P n ω * m n ω) * pk Λ P (n + 1)) =ᵐ[S.μ]
        (fun ω => P n ω * m n ω) * S.E n (pk Λ P (n + 1)) :=
      condExp_mul_of_stronglyMeasurable_left hNm hNi (hp.integrable_pk (n + 1))
    have e : (fun ω => pk Λ P (n + 1) ω * (a (n + 1) ω + moneyIn N0 P m (n + 1) ω)) =
        (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) +
          (fun ω => P n ω * m n ω) * pk Λ P (n + 1) := by
      funext ω
      simp only [moneyIn, Pi.add_apply, Pi.mul_apply]
      ring
    have hadd := S.E_add (hia (n + 1)) hNi n
    filter_upwards [flow_pk hp hf n, hadd, hpull] with ω h h1 h2
    rw [e, Pi.add_apply, h1, Pi.add_apply, h2, Pi.mul_apply, hp.E_pk_eq n ω]
    simp only [outlay, iota]
    rw [← hp.pk_mul_P n ω] at h ⊢
    linear_combination h

/-! ### The Kamihigashi scaling deviation -/

variable (S) in
/-- Cochrane (2023), (19.12), p. 439 and (19.28), p. 449: the real value of the wealth carried out
of date `T`, `k_T = (Q_T^{claims} + Q_TM_T)/P_T` (the claims bought at `T` and the overnight money,
valued at date-`T` prices). -/
noncomputable def kOut (Λ P a m : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  (claimCost S Λ P a T ω + bondPrice S Λ P T ω * (P T ω * m T ω)) / P T ω

variable (S) in
/-- Cochrane (2023), (19.12), p. 439 (the household that holds no wealth): the reference
consumption `c + (y − s − c − ιm)/w`, the consumption bundle (direction `(1, ϑ)`) financed by the
endowment net of taxes, with no claims and no wealth carried forward. -/
noncomputable def cRef (ϑ : ℝ) (Λ P y s c m : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  c n ω + (y n ω - s n ω - c n ω - iota S Λ P n ω * m n ω) / wedge S ϑ Λ P n ω

variable (S) in
/-- Cochrane (2023), (19.12), p. 439: the reference real balances `m + ϑ(cRef − c)`. -/
noncomputable def mRef (ϑ : ℝ) (Λ P y s c m : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  m n ω + ϑ * (cRef S ϑ Λ P y s c m n ω - c n ω)

variable (S) in
/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions"; the
Kamihigashi deviation, adapted from the Cochrane IntertemporalModel project): consumption is
unchanged before `T`, raised by `θk_T/w_T` at `T`, and `(1 − θ)c + θ cRef` after `T`. -/
noncomputable def kamC (ϑ : ℝ) (Λ P y s a c m : ℕ → Ω → ℝ) (T : ℕ) (θ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if n < T then c n ω else if n = T then
    c T ω + θ * (kOut S Λ P a m T ω / wedge S ϑ Λ P T ω)
    else (1 - θ) * c n ω + θ * cRef S ϑ Λ P y s c m n ω

variable (S) in
/-- Cochrane (2023), p. 439: real balances of the Kamihigashi deviation, moving `ϑ` per unit of
the consumption change. -/
noncomputable def kamM (ϑ : ℝ) (Λ P y s a c m : ℕ → Ω → ℝ) (T : ℕ) (θ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if n < T then m n ω else if n = T then
    m T ω + ϑ * (θ * (kOut S Λ P a m T ω / wedge S ϑ Λ P T ω))
    else (1 - θ) * m n ω + θ * mRef S ϑ Λ P y s c m n ω

variable (S) in
/-- Cochrane (2023), p. 439: claims of the Kamihigashi deviation: after `T` the household brings
the fraction `1 − θ` of its wealth `a_n + M_{n−1}` into each date. -/
noncomputable def kamA (ϑ : ℝ) (Λ P y s a c m : ℕ → Ω → ℝ) (N0 : Ω → ℝ) (T : ℕ) (θ : ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => if n ≤ T then a n ω else (1 - θ) * (a n ω + moneyIn N0 P m n ω) -
    moneyIn N0 P (kamM S ϑ Λ P y s a c m T θ) n ω

/-- Cochrane (2023), (19.12), p. 439: the reference bundle is financed by the endowment net of
taxes, `cRef + ι mRef = y − s` (where `w ≠ 0`). -/
theorem cRef_budget {ϑ : ℝ} {Λ P y s c m : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (hw : wedge S ϑ Λ P n ω ≠ 0) :
    cRef S ϑ Λ P y s c m n ω + iota S Λ P n ω * mRef S ϑ Λ P y s c m n ω =
      y n ω - s n ω := by
  have e : wedge S ϑ Λ P n ω = 1 + ϑ * iota S Λ P n ω := rfl
  have hd := div_mul_cancel₀ (y n ω - s n ω - c n ω - iota S Λ P n ω * m n ω) hw
  simp only [mRef, cRef]
  linear_combination hd - (y n ω - s n ω - c n ω - iota S Λ P n ω * m n ω) /
    wedge S ϑ Λ P n ω * e

namespace Kam

variable {ϑ : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} {T n : ℕ} {θ : ℝ}

/-- Cochrane (2023), p. 439: the deviation's consumption before `T`. -/
theorem kamC_lt (h : n < T) : kamC S ϑ Λ P y s a c m T θ n = c n :=
  funext fun ω => by simp [kamC, h]

/-- Cochrane (2023), p. 439: the deviation's consumption at `T`. -/
theorem kamC_eq : kamC S ϑ Λ P y s a c m T θ T =
    fun ω => c T ω + θ * (kOut S Λ P a m T ω / wedge S ϑ Λ P T ω) :=
  funext fun ω => by simp [kamC]

/-- Cochrane (2023), p. 439: the deviation's consumption after `T`. -/
theorem kamC_gt (h : T < n) : kamC S ϑ Λ P y s a c m T θ n =
    fun ω => (1 - θ) * c n ω + θ * cRef S ϑ Λ P y s c m n ω :=
  funext fun ω => by simp [kamC, not_lt.2 h.le, h.ne']

/-- Cochrane (2023), p. 439: the deviation's real balances before `T`. -/
theorem kamM_lt (h : n < T) : kamM S ϑ Λ P y s a c m T θ n = m n :=
  funext fun ω => by simp [kamM, h]

/-- Cochrane (2023), p. 439: the deviation's real balances at `T`. -/
theorem kamM_eq : kamM S ϑ Λ P y s a c m T θ T =
    fun ω => m T ω + ϑ * (θ * (kOut S Λ P a m T ω / wedge S ϑ Λ P T ω)) :=
  funext fun ω => by simp [kamM]

/-- Cochrane (2023), p. 439: the deviation's real balances after `T`. -/
theorem kamM_gt (h : T < n) : kamM S ϑ Λ P y s a c m T θ n =
    fun ω => (1 - θ) * m n ω + θ * mRef S ϑ Λ P y s c m n ω :=
  funext fun ω => by simp [kamM, not_lt.2 h.le, h.ne']

/-- Cochrane (2023), p. 439: the deviation's claims up to `T`. -/
theorem kamA_le (h : n ≤ T) : kamA S ϑ Λ P y s a c m N0 T θ n = a n :=
  funext fun ω => by simp [kamA, h]

/-- Cochrane (2023), p. 439: the deviation's claims after `T`. -/
theorem kamA_gt (h : T < n) : kamA S ϑ Λ P y s a c m N0 T θ n =
    fun ω => (1 - θ) * (a n ω + moneyIn N0 P m n ω) -
      moneyIn N0 P (kamM S ϑ Λ P y s a c m T θ) n ω :=
  funext fun ω => by simp [kamA, not_le.2 h]

/-- Cochrane (2023), p. 439: money brought into dates up to `T` is unchanged. -/
theorem moneyIn_kamM_le (h : n ≤ T) :
    moneyIn N0 P (kamM S ϑ Λ P y s a c m T θ) n = moneyIn N0 P m n := by
  cases n with
  | zero => rfl
  | succ k =>
    funext ω
    simp only [moneyIn]
    rw [kamM_lt (by omega)]

end Kam

open Kam in
/-- Cochrane (2023), (19.10), p. 439 and p. 449 ("their optimal choices include transversality
conditions"), **the Kamihigashi deviation is feasible**: for a feasible plan whose consumption,
real balances and claims, and the endowment and taxes, are bounded at each date (endowment and
taxes adapted), with the bundle cost `w = 1 + ϑι` nonzero and `1/w` bounded, and `0 ≤ θ ≤ 1`,
the plan `(kamC, kamM, kamA)` satisfies every flow constraint almost surely, adaptedness,
integrability and the no-Ponzi condition. -/
theorem kam_feasible {ϑ : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (hab : ∀ n, BddAt S (a n))
    (hyb : ∀ n, BddAt S (y n)) (hsb : ∀ n, BddAt S (s n)) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s) (hw : ∀ n, ∀ᵐ ω ∂S.μ, wedge S ϑ Λ P n ω ≠ 0)
    (hwb : ∀ n, BddAt S fun ω => (wedge S ϑ Λ P n ω)⁻¹) (T : ℕ) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    Feasible S Λ P y s N0 a0 (kamC S ϑ Λ P y s a c m T θ) (kamM S ϑ Λ P y s a c m T θ)
      (kamA S ϑ Λ P y s a c m N0 T θ) := by
  obtain ⟨ha0, hca, hma, haa, hflow, hia, hiN, him, hic, hnp⟩ := hf
  have ae : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → AEStronglyMeasurable f S.μ :=
    fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hint : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → BddAt S f →
      Integrable f S.μ := fun h hb => hb.integrable (ae h)
  have hPb := fun k => (hp.2.2.2.2 k).2.2.1
  have hΛb := fun k => (hp.2.2.2.2 k).1
  have hwm : ∀ k, StronglyMeasurable[S.𝓕 k] (wedge S ϑ Λ P k) := fun k =>
    stronglyMeasurable_const.add ((hp.stronglyMeasurable_iota k).const_mul ϑ)
  have hKm : ∀ k, StronglyMeasurable[S.𝓕 k] (claimCost S Λ P a k) := fun k =>
    ((S.stronglyMeasurable_E k _).measurable.div
      (hp.stronglyMeasurable_pk k).measurable).stronglyMeasurable
  have hKb : ∀ k, BddAt S (claimCost S Λ P a k) := fun k =>
    ((((hp.pk_bdd (k + 1)).mul (hab (k + 1))).E k).mul (hp.pk_inv_bdd k)).congr
      (Eventually.of_forall fun ω => by simp [claimCost, div_eq_mul_inv])
  have hkm : StronglyMeasurable[S.𝓕 T]
      (fun ω => kOut S Λ P a m T ω / wedge S ϑ Λ P T ω) :=
    ((((hKm T).add ((hp.stronglyMeasurable_bondPrice T).mul ((hp.2.1 T).mul
      (hma T)))).measurable.div (hp.2.1 T).measurable).div (hwm T).measurable).stronglyMeasurable
  have hkb : BddAt S (fun ω => kOut S Λ P a m T ω / wedge S ϑ Λ P T ω) :=
    ((((hKb T).add ((hp.bondPrice_bdd T).mul ((hPb T).mul (hmb T)))).mul
      (hp.2.2.2.2 T).2.2.2).mul (hwb T)).congr
      (Eventually.of_forall fun ω => by simp [kOut, div_eq_mul_inv])
  have hcrm : ∀ k, StronglyMeasurable[S.𝓕 k] (cRef S ϑ Λ P y s c m k) := fun k =>
    ((hca k).measurable.add (((((hya k).sub (hsa k)).sub (hca k)).sub
      ((hp.stronglyMeasurable_iota k).mul (hma k))).measurable.div
      (hwm k).measurable)).stronglyMeasurable
  have hcrb : ∀ k, BddAt S (cRef S ϑ Λ P y s c m k) := fun k =>
    ((hcb k).add (((((hyb k).sub (hsb k)).sub (hcb k)).sub
      ((hp.iota_bdd k).mul (hmb k))).mul (hwb k))).congr
      (Eventually.of_forall fun ω => by simp [cRef, div_eq_mul_inv])
  have hmrm : ∀ k, StronglyMeasurable[S.𝓕 k] (mRef S ϑ Λ P y s c m k) := fun k =>
    (hma k).add (((hcrm k).sub (hca k)).const_mul ϑ)
  have hmrb : ∀ k, BddAt S (mRef S ϑ Λ P y s c m k) := fun k =>
    (hmb k).add ((BddAt.const ϑ).mul ((hcrb k).sub (hcb k)))
  -- the deviation is adapted and bounded from `T` on
  have hCm : ∀ k, StronglyMeasurable[S.𝓕 k] (kamC S ϑ Λ P y s a c m T θ k) := by
    intro k
    rcases lt_trichotomy k T with h | h | h
    · rw [kamC_lt h]; exact hca k
    · subst h; rw [kamC_eq]; exact (hca k).add (hkm.const_mul θ)
    · rw [kamC_gt h]; exact ((hca k).const_mul _).add ((hcrm k).const_mul θ)
  have hMm : ∀ k, StronglyMeasurable[S.𝓕 k] (kamM S ϑ Λ P y s a c m T θ k) := by
    intro k
    rcases lt_trichotomy k T with h | h | h
    · rw [kamM_lt h]; exact hma k
    · subst h; rw [kamM_eq]; exact (hma k).add ((hkm.const_mul θ).const_mul ϑ)
    · rw [kamM_gt h]; exact ((hma k).const_mul _).add ((hmrm k).const_mul θ)
  have hCb : ∀ k, T ≤ k → BddAt S (kamC S ϑ Λ P y s a c m T θ k) := by
    intro k hk
    rcases hk.lt_or_eq with h | h
    · rw [kamC_gt h]; exact ((BddAt.const _).mul (hcb k)).add ((BddAt.const θ).mul (hcrb k))
    · subst h; rw [kamC_eq]; exact (hcb T).add ((BddAt.const θ).mul hkb)
  have hMb : ∀ k, T ≤ k → BddAt S (kamM S ϑ Λ P y s a c m T θ k) := by
    intro k hk
    rcases hk.lt_or_eq with h | h
    · rw [kamM_gt h]; exact ((BddAt.const _).mul (hmb k)).add ((BddAt.const θ).mul (hmrb k))
    · subst h; rw [kamM_eq]
      exact (hmb T).add ((BddAt.const ϑ).mul ((BddAt.const θ).mul hkb))
  have hNm : ∀ k, StronglyMeasurable[S.𝓕 (k + 1)] (moneyIn N0 P m (k + 1)) := fun k =>
    ((hp.2.1 k).mul (hma k)).mono (S.𝓕.mono (Nat.le_succ k))
  have hNm' : ∀ k, StronglyMeasurable[S.𝓕 (k + 1)]
      (moneyIn N0 P (kamM S ϑ Λ P y s a c m T θ) (k + 1)) := fun k =>
    ((hp.2.1 k).mul (hMm k)).mono (S.𝓕.mono (Nat.le_succ k))
  refine ⟨?_, hCm, hMm, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_,
    fun k => ?_, fun δ hδ => ?_⟩
  · rw [kamA_le (Nat.zero_le T)]; exact ha0
  · -- claims adapted
    rcases le_or_gt k T with h | h
    · rw [kamA_le h]; exact haa k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [kamA_gt h]
      exact (((haa (j + 1)).add (hNm j)).const_mul _).sub (hNm' j)
  · -- the flow constraints
    rcases lt_trichotomy k T with h | h | h
    · have e1 := kamA_le (S := S) (ϑ := ϑ) (Λ := Λ) (y := y) (s := s) (c := c) (N0 := N0)
        (θ := θ) (a := a) (P := P) (m := m) h.le
      have e2 := kamA_le (S := S) (ϑ := ϑ) (Λ := Λ) (y := y) (s := s) (c := c) (N0 := N0)
        (θ := θ) (a := a) (P := P) (m := m) (show k + 1 ≤ T by omega)
      filter_upwards [hflow k] with ω hfl
      simp only [claimCost, e1, e2, kamC_lt h, kamM_lt h, moneyIn_kamM_le h.le] at hfl ⊢
      exact hfl
    · subst h
      have eA1 : kamA S ϑ Λ P y s a c m N0 k θ (k + 1) = fun ω => (1 - θ) *
          (a (k + 1) ω + P k ω * m k ω) - P k ω * kamM S ϑ Λ P y s a c m k θ k ω := by
        rw [kamA_gt (Nat.lt_succ_self k)]
        rfl
      set f : Ω → ℝ := fun ω => (1 - θ) * (P k ω * m k ω) -
        P k ω * kamM S ϑ Λ P y s a c m k θ k ω with hf
      have hfm : StronglyMeasurable[S.𝓕 k] f :=
        (((hp.2.1 k).mul (hma k)).const_mul _).sub ((hp.2.1 k).mul (hMm k))
      have hfb : BddAt S f :=
        ((BddAt.const _).mul ((hPb k).mul (hmb k))).sub ((hPb k).mul (hMb k le_rfl))
      obtain ⟨Kf, hKf⟩ := id hfb
      have hfi : Integrable (f * pk Λ P (k + 1)) S.μ :=
        hfb.integrable_mul (ae hfm) (hp.integrable_pk (k + 1))
      have e : (fun ω => pk Λ P (k + 1) ω * kamA S ϑ Λ P y s a c m N0 k θ (k + 1) ω) =
          (1 - θ) • (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) + f * pk Λ P (k + 1) := by
        rw [eA1]
        funext ω
        simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hf]
        ring
      have he : ∀ᵐ ω ∂S.μ,
          S.E k (fun ω => pk Λ P (k + 1) ω * kamA S ϑ Λ P y s a c m N0 k θ (k + 1) ω) ω =
            (1 - θ) * S.E k (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) ω +
              f ω * S.E k (pk Λ P (k + 1)) ω := by
        rw [e]
        filter_upwards [S.E_add ((hia (k + 1)).smul (1 - θ)) hfi k,
          S.E_smul (1 - θ) (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) k,
          S.E_pullOut hfm hKf (hp.integrable_pk (k + 1))] with ω h1 h2 h3
        rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      filter_upwards [hflow k, he, hw k] with ω hfl hE hwω
      simp only [claimCost] at hfl ⊢
      rw [hE, hp.E_pk_eq k ω, kamA_le le_rfl, moneyIn_kamM_le le_rfl, kamC_eq]
      simp only [hf, kamM_eq]
      set K := S.E k (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) ω / pk Λ P k ω with hK
      set W := wedge S ϑ Λ P k ω with hW
      set k_ := kOut S Λ P a m k ω with hk_
      set Q := bondPrice S Λ P k ω with hQ
      have hpk := (hp.pk_pos k ω).ne'
      have hP0 := (hp.2.2.2.1 k ω).ne'
      have hdiv : ((1 - θ) * S.E k (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) ω +
          ((1 - θ) * (P k ω * m k ω) - P k ω * (m k ω + ϑ * (θ * (k_ / W)))) *
            (Q * pk Λ P k ω)) / pk Λ P k ω = (1 - θ) * K +
          ((1 - θ) * (P k ω * m k ω) - P k ω * (m k ω + ϑ * (θ * (k_ / W)))) * Q := by
        rw [hK]
        field_simp
      rw [hdiv]
      have hD : k_ / W * W = k_ := div_mul_cancel₀ _ hwω
      have hk : k_ * P k ω = K + Q * (P k ω * m k ω) := by
        rw [hk_, kOut, div_mul_cancel₀ _ hP0]
        simp only [claimCost, hK, hQ]
      have hwdef : W = 1 + ϑ * (1 - Q) := rfl
      linear_combination hfl + θ * P k ω * (k_ / W) * hwdef - θ * P k ω * hD - θ * hk
    · have eA : kamA S ϑ Λ P y s a c m N0 T θ k = fun ω => (1 - θ) *
          (a k ω + moneyIn N0 P m k ω) - moneyIn N0 P (kamM S ϑ Λ P y s a c m T θ) k ω :=
        kamA_gt h
      have eA1 : kamA S ϑ Λ P y s a c m N0 T θ (k + 1) = fun ω => (1 - θ) *
          (a (k + 1) ω + P k ω * m k ω) - P k ω * kamM S ϑ Λ P y s a c m T θ k ω := by
        rw [kamA_gt (by omega)]
        rfl
      set f : Ω → ℝ := fun ω => (1 - θ) * (P k ω * m k ω) -
        P k ω * kamM S ϑ Λ P y s a c m T θ k ω with hf
      have hfm : StronglyMeasurable[S.𝓕 k] f :=
        (((hp.2.1 k).mul (hma k)).const_mul _).sub ((hp.2.1 k).mul (hMm k))
      have hfb : BddAt S f :=
        ((BddAt.const _).mul ((hPb k).mul (hmb k))).sub ((hPb k).mul (hMb k h.le))
      obtain ⟨Kf, hKf⟩ := id hfb
      have hfi : Integrable (f * pk Λ P (k + 1)) S.μ :=
        hfb.integrable_mul (ae hfm) (hp.integrable_pk (k + 1))
      have e : (fun ω => pk Λ P (k + 1) ω * kamA S ϑ Λ P y s a c m N0 T θ (k + 1) ω) =
          (1 - θ) • (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) + f * pk Λ P (k + 1) := by
        rw [eA1]
        funext ω
        simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hf]
        ring
      have he : ∀ᵐ ω ∂S.μ,
          S.E k (fun ω => pk Λ P (k + 1) ω * kamA S ϑ Λ P y s a c m N0 T θ (k + 1) ω) ω =
            (1 - θ) * S.E k (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) ω +
              f ω * S.E k (pk Λ P (k + 1)) ω := by
        rw [e]
        filter_upwards [S.E_add ((hia (k + 1)).smul (1 - θ)) hfi k,
          S.E_smul (1 - θ) (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) k,
          S.E_pullOut hfm hKf (hp.integrable_pk (k + 1))] with ω h1 h2 h3
        rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      filter_upwards [hflow k, he, hw k] with ω hfl hE hwω
      simp only [claimCost] at hfl ⊢
      rw [hE, hp.E_pk_eq k ω, eA, kamC_gt h]
      simp only [hf, kamM_gt h]
      set K := S.E k (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) ω / pk Λ P k ω with hK
      set Q := bondPrice S Λ P k ω with hQ
      have hpk := (hp.pk_pos k ω).ne'
      have hdiv : ((1 - θ) * S.E k (fun ω => pk Λ P (k + 1) ω * a (k + 1) ω) ω +
          ((1 - θ) * (P k ω * m k ω) - P k ω * ((1 - θ) * m k ω +
            θ * mRef S ϑ Λ P y s c m k ω)) * (Q * pk Λ P k ω)) / pk Λ P k ω = (1 - θ) * K +
          ((1 - θ) * (P k ω * m k ω) - P k ω * ((1 - θ) * m k ω +
            θ * mRef S ϑ Λ P y s c m k ω)) * Q := by
        rw [hK]
        field_simp
      rw [hdiv]
      have hbud := cRef_budget (S := S) (y := y) (s := s) (c := c) (m := m) hwω
      have hι : iota S Λ P k ω = 1 - Q := rfl
      rw [hι] at hbud
      linear_combination (1 - θ) * hfl - θ * P k ω * hbud
  · rcases le_or_gt k T with h | h
    · rw [kamA_le h]; exact hia k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : T ≤ j := by omega
      have hi2 : Integrable (fun ω => pk Λ P (j + 1) ω *
          moneyIn N0 P (kamM S ϑ Λ P y s a c m T θ) (j + 1) ω) S.μ :=
        hint ((hp.stronglyMeasurable_pk (j + 1)).mul (hNm' j))
          ((hp.pk_bdd (j + 1)).mul ((hPb j).mul (hMb j hj)))
      rw [kamA_gt h]
      exact ((((hia (j + 1)).add (hiN (j + 1))).const_mul (1 - θ)).sub hi2).congr
        (Eventually.of_forall fun ω => by simp only [Pi.sub_apply, Pi.add_apply]; ring)
  · rcases le_or_gt k T with h | h
    · rw [moneyIn_kamM_le h]; exact hiN k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact hint ((hp.stronglyMeasurable_pk (j + 1)).mul (hNm' j))
        ((hp.pk_bdd (j + 1)).mul ((hPb j).mul (hMb j (by omega))))
  · rcases lt_or_ge k T with h | h
    · rw [kamM_lt h]; exact him k
    · exact hint ((hp.1 k).mul (hMm k)) ((hΛb k).mul (hMb k h))
  · rcases lt_or_ge k T with h | h
    · rw [kamC_lt h]; exact hic k
    · exact hint ((hp.1 k).mul (hCm k)) ((hΛb k).mul (hCb k h))
  · filter_upwards [hnp δ hδ, eventually_gt_atTop T] with T' hT' hgt
    have e : wealthPV S Λ P N0 (kamM S ϑ Λ P y s a c m T θ)
        (kamA S ϑ Λ P y s a c m N0 T θ) T' = (1 - θ) * wealthPV S Λ P N0 m a T' := by
      simp only [wealthPV]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      rw [kamA_gt hgt]
      simp only
      ring
    rw [e]
    rcases le_total 0 (wealthPV S Λ P N0 m a T') with h | h
    · nlinarith
    · nlinarith

/-! ### The transversality condition is necessary -/

/-- Cochrane (2023), Online Appendix A1.1, p. 556 (restated from the Cochrane IntertemporalModel
project): for increasing `g`, a value at a convex combination is bounded by `|g a| + |g e|`. -/
theorem abs_comb_le {g : ℝ → ℝ} (hmono : Monotone g) {a e θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |g ((1 - θ) * a + θ * e)| ≤ |g a| + |g e| := by
  rcases le_total a e with hae | hae
  · have l : a ≤ (1 - θ) * a + θ * e := by nlinarith
    have r : (1 - θ) * a + θ * e ≤ e := by nlinarith
    have := hmono l
    have := hmono r
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (g a), le_abs_self (g e), abs_nonneg (g a),
      abs_nonneg (g e), neg_abs_le (g e), le_abs_self (g a)]
  · have l : e ≤ (1 - θ) * a + θ * e := by nlinarith
    have r : (1 - θ) * a + θ * e ≤ a := by nlinarith
    have := hmono l
    have := hmono r
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (g a), le_abs_self (g e), abs_nonneg (g a),
      abs_nonneg (g e), neg_abs_le (g e), le_abs_self (g a)]

/-- Cochrane (2023), p. 439 (restated from the Cochrane IntertemporalModel project): the tail
`∑_{n > T} f_n` of a convergent series is `∑ f − ∑_{n ≤ T} f_n`. -/
theorem hasSum_ite_lt {f : ℕ → ℝ} (hf : Summable f) (T : ℕ) :
    HasSum (fun n => if T < n then f n else 0) (∑' n, f n - ∑ n ∈ Finset.range (T + 1), f n) := by
  have hfin : HasSum (fun n => if T < n then 0 else f n) (∑ n ∈ Finset.range (T + 1), f n) := by
    have h : HasSum (fun n => if T < n then 0 else f n)
        (∑ n ∈ Finset.range (T + 1), if T < n then 0 else f n) :=
      hasSum_sum_of_ne_finset_zero fun n hn => by
        simp only [Finset.mem_range, not_lt] at hn
        simp only [(show T < n by omega), ↓reduceIte]
    convert h using 1
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_range] at hn
    simp only [(show ¬ T < n by omega), ↓reduceIte]
  convert hf.hasSum.sub hfin using 1
  funext n
  split_ifs <;> ring

/-- Cochrane (2023), p. 439: the tail `∑_{n > T} βⁿ(F_n − G_n)` of the utility gain of a plan
(period utilities `F`) over a reference plan (period utilities `G`). -/
noncomputable def tail (β : ℝ) (F G : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑' n, if T < n then β ^ n * (F n ω - G n ω) else 0

/-- Cochrane (2023), p. 439: for two admissible utility processes the expected tail vanishes,
`E[∑_{n > T} βⁿ(F_n − G_n)] → 0` (dominated convergence), and each tail is integrable. -/
theorem tail_tendsto {β : ℝ} (hβ : 0 < β) {F G : ℕ → Ω → ℝ} (hF : UAdmissible S β F)
    (hG : UAdmissible S β G) :
    (∀ T, Integrable (tail β F G T) S.μ) ∧
      Tendsto (fun T => ∫ ω, tail β F G T ω ∂S.μ) atTop (𝓝 0) := by
  set B : Ω → ℝ := fun ω => ∑' n, β ^ n * |F n ω| + ∑' n, β ^ n * |G n ω| with hB
  have hBi : Integrable B S.μ := hF.2.2.add hG.2.2
  have hsF' := hF.summable hβ.le
  have hsG' := hG.summable hβ.le
  have hbd : ∀ T, ∀ᵐ ω ∂S.μ, ‖tail β F G T ω‖ ≤ B ω := fun T => by
    filter_upwards [hF.2.1, hG.2.1] with ω h1 h2
    refine tsum_of_norm_bounded (h1.hasSum.add h2.hasSum) fun n => ?_
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.le, ← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (pow_nonneg hβ.le n)
    · rw [norm_zero]
      exact add_nonneg (mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _))
        (mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _))
  have hm : ∀ T, AEStronglyMeasurable (tail β F G T) S.μ := fun T => by
    refine aestronglyMeasurable_tsum (fun n => ?_) ?_
    · split_ifs
      · exact ((hF.1 n).sub (hG.1 n)).const_mul _
      · exact aestronglyMeasurable_const
    · filter_upwards [hsF', hsG'] with ω h1 h2
      have hf : Summable fun n => β ^ n * (F n ω - G n ω) :=
        (h1.sub h2).congr fun n => by ring
      exact (hasSum_ite_lt hf T).summable
  refine ⟨fun T => Integrable.mono' hBi (hm T) (hbd T), ?_⟩
  have h := tendsto_integral_of_dominated_convergence B hm hBi hbd (f := fun _ => 0) ?_
  · simpa using h
  · filter_upwards [hsF', hsG'] with ω h1 h2
    have hf : Summable fun n => β ^ n * (F n ω - G n ω) :=
      (h1.sub h2).congr fun n => by ring
    have e : ∀ T, tail β F G T ω = ∑' n, β ^ n * (F n ω - G n ω) -
        ∑ n ∈ Finset.range (T + 1), β ^ n * (F n ω - G n ω) :=
      fun T => (hasSum_ite_lt hf T).tsum_eq
    simp_rw [e]
    have := (tendsto_const_nhds (x := ∑' n, β ^ n * (F n ω - G n ω))).sub
      (hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
    simpa using this

open Kam in
/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions"),
**the Kamihigashi inequality**: at an optimal plan, with utility concave and increasing along the
bundle direction `(1, ϑ)`, regular prices, consumption, real balances, claims, endowment and taxes
bounded at each date (endowment and taxes adapted), bundle costs `w` nonzero with `1/w` bounded,
`Con` allowing the deviation for small `θ > 0`, and the reference plan admissible,
`βᵀE[(u_c + ϑu_m)(c_T, m_T) k_T/w_T] ≤ E[∑_{n > T} βⁿ(u(c_n, m_n) − u(cRef_n, mRef_n))]`. -/
theorem tvc_key {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um) {ϑ : ℝ}
    (hconc : ∀ x z, ConcaveOn ℝ Set.univ (fun e => u (x + e) (z + ϑ * e)))
    (hmono : ∀ x z, Monotone (fun e => u (x + e) (z + ϑ * e)))
    {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hopt : Optimal S β u Con Λ P y s N0 a0 c m a)
    (hp : PriceRegular S Λ P) (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hab : ∀ n, BddAt S (a n)) (hyb : ∀ n, BddAt S (y n)) (hsb : ∀ n, BddAt S (s n))
    (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s)
    (hw : ∀ n, ∀ᵐ ω ∂S.μ, wedge S ϑ Λ P n ω ≠ 0)
    (hwb : ∀ n, BddAt S fun ω => (wedge S ϑ Λ P n ω)⁻¹)
    (href : UAdmissible S β
      (fun n ω => u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω))) (T : ℕ)
    (hcon : ∃ θ₀, 0 < θ₀ ∧ θ₀ ≤ 1 ∧ ∀ θ, 0 < θ → θ < θ₀ →
      Con (kamC S ϑ Λ P y s a c m T θ) (kamM S ϑ Λ P y s a c m T θ)) :
    β ^ T * ∫ ω, (uc (c T ω) (m T ω) + ϑ * um (c T ω) (m T ω)) *
        (kOut S Λ P a m T ω / wedge S ϑ Λ P T ω) ∂S.μ ≤
      ∫ ω, tail β (fun n ω => u (c n ω) (m n ω))
        (fun n ω => u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω)) T ω ∂S.μ := by
  obtain ⟨hfeas, -, hadm, hbest⟩ := hopt
  obtain ⟨θ₀, hθ₀, hθ₀1, hcθ⟩ := hcon
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have ae : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → AEStronglyMeasurable f S.μ :=
    fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hPb := fun k => (hp.2.2.2.2 k).2.2.1
  have hwm : ∀ k, StronglyMeasurable[S.𝓕 k] (wedge S ϑ Λ P k) := fun k =>
    stronglyMeasurable_const.add ((hp.stronglyMeasurable_iota k).const_mul ϑ)
  have hKm : ∀ k, StronglyMeasurable[S.𝓕 k] (claimCost S Λ P a k) := fun k =>
    ((S.stronglyMeasurable_E k _).measurable.div
      (hp.stronglyMeasurable_pk k).measurable).stronglyMeasurable
  have hKb : ∀ k, BddAt S (claimCost S Λ P a k) := fun k =>
    ((((hp.pk_bdd (k + 1)).mul (hab (k + 1))).E k).mul (hp.pk_inv_bdd k)).congr
      (Eventually.of_forall fun ω => by simp [claimCost, div_eq_mul_inv])
  set kw : Ω → ℝ := fun ω => kOut S Λ P a m T ω / wedge S ϑ Λ P T ω with hkw
  have hkm : StronglyMeasurable[S.𝓕 T] kw :=
    ((((hKm T).add ((hp.stronglyMeasurable_bondPrice T).mul ((hp.2.1 T).mul
      (hma T)))).measurable.div (hp.2.1 T).measurable).div (hwm T).measurable).stronglyMeasurable
  have hkb : BddAt S kw :=
    ((((hKb T).add ((hp.bondPrice_bdd T).mul ((hPb T).mul (hmb T)))).mul
      (hp.2.2.2.2 T).2.2.2).mul (hwb T)).congr
      (Eventually.of_forall fun ω => by simp [hkw, kOut, div_eq_mul_inv])
  set F : ℕ → Ω → ℝ := fun n ω => u (c n ω) (m n ω) with hF
  set G : ℕ → Ω → ℝ := fun n ω => u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω)
    with hG
  set g : ℕ → Ω → ℝ → ℝ := fun n ω e => u (c n ω + e) (m n ω + ϑ * e) with hg
  set d : ℕ → Ω → ℝ := fun n ω => cRef S ϑ Λ P y s c m n ω - c n ω with hd
  have hg0 : ∀ n ω, g n ω 0 = F n ω := fun n ω => by simp [hg, hF]
  have hgd : ∀ n ω, g n ω (d n ω) = G n ω := fun n ω => by
    simp only [hg, hd, hG, mRef, add_sub_cancel]
  have huc := hu.continuous
  have hFi := hadm.integrable hβ T
  -- the key inequality for each small `θ > 0`
  have key : ∀ θ, 0 < θ → θ < θ₀ →
      β ^ T * (∫ ω, g T ω (θ * kw ω) ∂S.μ - ∫ ω, F T ω ∂S.μ) ≤
        θ * ∫ ω, tail β F G T ω ∂S.μ := by
    intro θ hθ0 hθ
    have hθ1 : θ ≤ 1 := by linarith
    have hfθ := kam_feasible hp hfeas hcb hmb hab hyb hsb hya hsa hw hwb T hθ0.le hθ1
    set c' := kamC S ϑ Λ P y s a c m T θ with hc'
    set m' := kamM S ϑ Λ P y s a c m T θ with hm'
    have hval : ∀ n ω, u (c' n ω) (m' n ω) = if n < T then F n ω else if n = T then
        g T ω (θ * kw ω) else g n ω (θ * d n ω) := by
      intro n ω
      rcases lt_trichotomy n T with h | h | h
      · simp only [hc', hm', kamC_lt h, kamM_lt h, h, ↓reduceIte, hF]
      · subst h
        simp only [hc', hm', kamC_eq, kamM_eq, lt_irrefl, ↓reduceIte, hg, hkw]
      · simp only [hc', hm', kamC_gt h, kamM_gt h, (show ¬ n < T by omega),
          (show n ≠ T by omega), ↓reduceIte, hg, hd, mRef]
        congr 1 <;> ring
    have hc'm : ∀ n, AEStronglyMeasurable (fun ω => u (c' n ω) (m' n ω)) S.μ := fun n =>
      huc.comp_aestronglyMeasurable ((ae (hfθ.2.1 n)).prodMk (ae (hfθ.2.2.1 n)))
    obtain ⟨M, hM⟩ : BddAt S (fun ω => g T ω (θ * kw ω)) :=
      BddAt.comp₂ (v := fun x z => u x z) huc ((hcb T).add ((BddAt.const θ).mul hkb))
        ((hmb T).add ((BddAt.const ϑ).mul ((BddAt.const θ).mul hkb)))
    have hbd : ∀ᵐ ω ∂S.μ, ∀ n, β ^ n * |u (c' n ω) (m' n ω)| ≤
        β ^ n * |F n ω| + β ^ n * |G n ω| + (if n = T then β ^ T * M else 0) := by
      filter_upwards [hM] with ω hMω n
      have hbn := pow_nonneg hβ.le n
      have hA := mul_nonneg hbn (abs_nonneg (G n ω))
      rw [hval]
      rcases lt_trichotomy n T with h | h | h
      · simp only [h, ↓reduceIte, h.ne, add_zero]
        linarith
      · subst h
        simp only [lt_irrefl, ↓reduceIte]
        have := mul_le_mul_of_nonneg_left hMω hbn
        nlinarith [mul_nonneg hbn (abs_nonneg (F n ω))]
      · simp only [(show ¬ n < T by omega), (show n ≠ T by omega), ↓reduceIte, add_zero]
        have h2 : |g n ω ((1 - θ) * 0 + θ * d n ω)| ≤ |g n ω 0| + |g n ω (d n ω)| :=
          abs_comb_le (hmono (c n ω) (m n ω)) hθ0.le hθ1
        rw [hg0, hgd, mul_zero, zero_add] at h2
        have := mul_le_mul_of_nonneg_left h2 hbn
        linarith
    set B : Ω → ℝ := fun ω => ∑' n, β ^ n * |F n ω| + ∑' n, β ^ n * |G n ω| with hB
    have hBi : Integrable B S.μ := hadm.2.2.add href.2.2
    have hg_sum : ∀ᵐ ω ∂S.μ, HasSum (fun n => β ^ n * |F n ω| + β ^ n * |G n ω| +
        (if n = T then β ^ T * M else 0)) (B ω + β ^ T * M) := by
      filter_upwards [hadm.2.1, href.2.1] with ω h1 h2
      exact (h1.hasSum.add h2.hasSum).add (hasSum_ite_eq T _)
    have hnn : ∀ ω n, 0 ≤ β ^ n * |u (c' n ω) (m' n ω)| := fun ω n =>
      mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _)
    have hadm' : UAdmissible S β (fun n ω => u (c' n ω) (m' n ω)) := by
      refine ⟨hc'm, ?_, ?_⟩
      · filter_upwards [hbd, hg_sum] with ω h hs
        exact Summable.of_nonneg_of_le (hnn ω) h hs.summable
      · refine Integrable.mono' (hBi.add (integrable_const (β ^ T * M)))
          (aestronglyMeasurable_tsum (fun n => (hc'm n).norm.const_mul _) ?_) ?_
        · filter_upwards [hbd, hg_sum] with ω h hs
          exact Summable.of_nonneg_of_le (hnn ω) h hs.summable
        · filter_upwards [hbd, hg_sum] with ω h hs
          rw [Real.norm_of_nonneg (tsum_nonneg (hnn ω))]
          exact hasSum_le h (Summable.of_nonneg_of_le (hnn ω) h hs.summable).hasSum hs
    have hopt' := hbest c' m' _ hfθ (hcθ θ hθ0 hθ) hadm'
    -- integrability at `T`
    have hgT : Integrable (fun ω => g T ω (θ * kw ω)) S.μ :=
      (BddAt.integrable ⟨M, hM⟩ (huc.comp_aestronglyMeasurable
        (((ae (hca T)).add ((ae hkm).const_mul θ)).prodMk
          ((ae (hma T)).add (((ae hkm).const_mul θ).const_mul ϑ)))))
    -- the pointwise lower bound
    have htl := (tail_tendsto hβ hadm href).1 T
    have hlow : ∀ᵐ ω ∂S.μ, ∑' n, β ^ n * F n ω + β ^ T * (g T ω (θ * kw ω) - F T ω) -
        θ * tail β F G T ω ≤ ∑' n, β ^ n * u (c' n ω) (m' n ω) := by
      filter_upwards [hadm.summable hβ.le, href.summable hβ.le, hadm'.summable hβ.le]
        with ω h1 h2 h3
      have hf : Summable fun n => β ^ n * (F n ω - G n ω) :=
        (h1.sub h2).congr fun n => by ring
      have htl' : HasSum (fun n => if T < n then β ^ n * (F n ω - G n ω) else 0)
          (tail β F G T ω) := (hasSum_ite_lt hf T).summable.hasSum
      have hh := (h1.hasSum.add (hasSum_ite_eq T (β ^ T * (g T ω (θ * kw ω) - F T ω)))).sub
        (htl'.mul_left θ)
      refine hasSum_le (fun n => ?_) hh h3.hasSum
      have hbn := pow_nonneg hβ.le n
      rw [hval]
      rcases lt_trichotomy n T with h | h | h
      · simp only [h, ↓reduceIte, h.ne, (show ¬ T < n by omega)]
        linarith
      · subst h
        simp only [lt_irrefl, ↓reduceIte]
        linarith
      · simp only [(show ¬ n < T by omega), (show n ≠ T by omega), h, ↓reduceIte]
        have hcv : (1 - θ) * g n ω 0 + θ * g n ω (d n ω) ≤
            g n ω ((1 - θ) * 0 + θ * d n ω) :=
          (hconc (c n ω) (m n ω)).2 (Set.mem_univ 0) (Set.mem_univ (d n ω))
            (show 0 ≤ 1 - θ by linarith) hθ0.le (by ring)
        rw [hg0, hgd, mul_zero, zero_add] at hcv
        nlinarith [mul_le_mul_of_nonneg_left hcv hbn]
    have i3 : Integrable (fun ω => β ^ T * (g T ω (θ * kw ω) - F T ω)) S.μ :=
      (hgT.sub hFi).const_mul _
    have i1 : Integrable (fun ω => ∑' n, β ^ n * F n ω +
        β ^ T * (g T ω (θ * kw ω) - F T ω)) S.μ := (hadm.integrable_sum hβ.le).add i3
    have i2 : Integrable (fun ω => θ * tail β F G T ω) S.μ := htl.const_mul θ
    have i12 : Integrable (fun ω => ∑' n, β ^ n * F n ω +
        β ^ T * (g T ω (θ * kw ω) - F T ω) - θ * tail β F G T ω) S.μ := i1.sub i2
    have hmono_int := integral_mono_ae i12 (hadm'.integrable_sum hβ.le) hlow
    rw [integral_sub i1 i2, integral_add (hadm.integrable_sum hβ.le) i3, integral_const_mul,
      integral_const_mul, integral_sub hgT hFi] at hmono_int
    unfold expU at hopt'
    linarith
  -- differentiate at `θ = 0`
  obtain ⟨R, hR1, hR2, hR3, hR4⟩ : ∃ R, (∀ᵐ ω ∂S.μ, |c T ω| ≤ R) ∧
      (∀ᵐ ω ∂S.μ, |kw ω| ≤ R) ∧ (∀ᵐ ω ∂S.μ, |m T ω| ≤ R) ∧
        ∀ᵐ ω ∂S.μ, |ϑ * kw ω| ≤ R := by
    obtain ⟨M1, h1⟩ := hcb T
    obtain ⟨M4, h4⟩ := (BddAt.const ϑ).mul hkb
    obtain ⟨M2, h2⟩ := hkb
    obtain ⟨M3, h3⟩ := hmb T
    refine ⟨max (max M1 M2) (max M3 M4), ?_, ?_, ?_, ?_⟩
    · exact h1.mono fun ω h => h.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h2.mono fun ω h => h.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact h3.mono fun ω h => h.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact h4.mono fun ω h => h.trans ((le_max_right _ _).trans (le_max_right _ _))
  have hD := hasDerivAt_integral_comp₂ hu (ae (hca T)) (ae hkm) (ae (hma T))
    ((ae hkm).const_mul ϑ) hR1 hR2 hR3 hR4
  have hφ : ∀ θ, ∫ ω, u (c T ω + θ * kw ω) (m T ω + θ * (ϑ * kw ω)) ∂S.μ =
      ∫ ω, g T ω (θ * kw ω) ∂S.μ := fun θ =>
    integral_congr_ae (Eventually.of_forall fun ω => by
      simp only [hg]
      congr 2
      ring)
  have hslope := hD.tendsto_slope_zero_right
  have hb := pow_pos hβ T
  have hle : ∫ ω, (uc (c T ω) (m T ω) * kw ω + um (c T ω) (m T ω) * (ϑ * kw ω)) ∂S.μ ≤
      (∫ ω, tail β F G T ω ∂S.μ) / β ^ T := by
    refine le_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT hθ₀] with θ hθ
    simp only [zero_add, smul_eq_mul, zero_mul, add_zero, hφ]
    rw [le_div_iff₀ hb]
    have := key θ hθ.1 hθ.2
    have hF0 : ∫ ω, F T ω ∂S.μ = ∫ ω, u (c T ω) (m T ω) ∂S.μ := rfl
    rw [hF0] at this
    have h5 := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hθ.1.le)
    rw [← mul_assoc θ⁻¹ θ, inv_mul_cancel₀ hθ.1.ne', one_mul] at h5
    calc θ⁻¹ * (∫ ω, g T ω (θ * kw ω) ∂S.μ - ∫ ω, u (c T ω) (m T ω) ∂S.μ) * β ^ T
        = θ⁻¹ * (β ^ T * (∫ ω, g T ω (θ * kw ω) ∂S.μ - ∫ ω, u (c T ω) (m T ω) ∂S.μ)) := by
          ring
      _ ≤ _ := h5
  have e : ∫ ω, (uc (c T ω) (m T ω) + ϑ * um (c T ω) (m T ω)) * kw ω ∂S.μ =
      ∫ ω, (uc (c T ω) (m T ω) * kw ω + um (c T ω) (m T ω) * (ϑ * kw ω)) ∂S.μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by ring)
  rw [e]
  rw [le_div_iff₀ hb] at hle
  linarith

/-- Cochrane (2023), (19.12), p. 439 and (19.28), p. 449: the date-0 value of the wealth carried
out of `T` is the date-0 value of the wealth brought into `T + 1`,
`E[Λ_Tk_T] = E[pk_{T+1}(a_{T+1} + M_T)]`, for a feasible plan with bounded real balances. -/
theorem pv_wealth_next {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a)
    (hmb : ∀ n, BddAt S (m n)) (T : ℕ) :
    ∫ ω, Λ T ω * kOut S Λ P a m T ω ∂S.μ = wealthPV S Λ P N0 m a (T + 1) := by
  have hia := hf.2.2.2.2.2.1
  have hzm : StronglyMeasurable[S.𝓕 T] (fun ω => P T ω * m T ω) :=
    (hp.2.1 T).mul (hf.2.2.1 T)
  obtain ⟨K, hK⟩ := ((hp.2.2.2.2 T).2.2.1.mul (hmb T))
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
    (BddAt.integrable_mul ⟨K, hK⟩ ((hzm.mono (S.𝓕.le T)).aestronglyMeasurable)
      (S.integrable_E T _))
  have i3 : Integrable (fun ω => (P T ω * m T ω) * pk Λ P (T + 1) ω) S.μ :=
    (BddAt.integrable_mul ⟨K, hK⟩ ((hzm.mono (S.𝓕.le T)).aestronglyMeasurable)
      (hp.integrable_pk (T + 1)))
  rw [e, integral_add (S.integrable_E T _) i2, S.integral_E, ← integral_mul_E hzm hK
    (hp.integrable_pk (T + 1)), ← integral_add (hia (T + 1)) i3]
  exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [moneyIn]; ring)

/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions") and
(19.28), p. 449, **the transversality condition is necessary, on a probability space**: under the
hypotheses of `tvc_key` at every date, if the first-order condition holds in the normalised form
`βᵀ(u_c + ϑu_m)(c_T, m_T) = Λ_Tw_T` almost surely, then the date-0 value of wealth vanishes in
the limit, `E[pk_T(a_T + M_{T−1})] → 0`. -/
theorem tvc_of_optimal {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {ϑ : ℝ} (hconc : ∀ x z, ConcaveOn ℝ Set.univ (fun e => u (x + e) (z + ϑ * e)))
    (hmono : ∀ x z, Monotone (fun e => u (x + e) (z + ϑ * e)))
    {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hopt : Optimal S β u Con Λ P y s N0 a0 c m a)
    (hp : PriceRegular S Λ P) (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hab : ∀ n, BddAt S (a n)) (hyb : ∀ n, BddAt S (y n)) (hsb : ∀ n, BddAt S (s n))
    (hya : StronglyAdapted S.𝓕 y) (hsa : StronglyAdapted S.𝓕 s)
    (hw : ∀ n, ∀ᵐ ω ∂S.μ, wedge S ϑ Λ P n ω ≠ 0)
    (hwb : ∀ n, BddAt S fun ω => (wedge S ϑ Λ P n ω)⁻¹)
    (href : UAdmissible S β
      (fun n ω => u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω)))
    (hcon : ∀ T, ∃ θ₀, 0 < θ₀ ∧ θ₀ ≤ 1 ∧ ∀ θ, 0 < θ → θ < θ₀ →
      Con (kamC S ϑ Λ P y s a c m T θ) (kamM S ϑ Λ P y s a c m T θ))
    (hfoc : ∀ T, ∀ᵐ ω ∂S.μ, β ^ T * (uc (c T ω) (m T ω) + ϑ * um (c T ω) (m T ω)) =
      Λ T ω * wedge S ϑ Λ P T ω) :
    Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  have hfeas := hopt.1
  have hnp := hfeas.2.2.2.2.2.2.2.2.2
  have htl := tail_tendsto hβ hopt.2.2.1 href
  have hup : ∀ T, wealthPV S Λ P N0 m a (T + 1) ≤
      ∫ ω, tail β (fun n ω => u (c n ω) (m n ω))
        (fun n ω => u (cRef S ϑ Λ P y s c m n ω) (mRef S ϑ Λ P y s c m n ω)) T ω ∂S.μ := by
    intro T
    have hk := tvc_key hβ hu hconc hmono hopt hp hcb hmb hab hyb hsb hya hsa hw hwb href T
      (hcon T)
    rw [← pv_wealth_next hp hfeas hmb T]
    refine le_of_eq_of_le ?_ hk
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hfoc T, hw T] with ω h1 h2
    rw [← mul_assoc, h1]
    field_simp
  have h1 : Tendsto (fun T => wealthPV S Λ P N0 m a (T + 1)) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have := hnp (-b / 2) (by linarith)
      filter_upwards [(tendsto_add_atTop_nat 1).eventually this] with T hT
      linarith
    · filter_upwards [(tendsto_order.1 htl.2).2 b hb] with T hT
      exact lt_of_le_of_lt (hup T) hT
  exact (tendsto_add_atTop_iff_nat 1).1 h1

/-- Cochrane (2023), (19.28), p. 449: the freed wealth per unit of bundle cost, `k_T/w_T`, is known
at `T` and bounded, when real balances and claims are bounded and `1/w` is bounded. -/
theorem kw_regular {ϑ : ℝ} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a)
    (hmb : ∀ n, BddAt S (m n)) (hab : ∀ n, BddAt S (a n))
    (hwb : ∀ n, BddAt S fun ω => (wedge S ϑ Λ P n ω)⁻¹) (T : ℕ) :
    StronglyMeasurable[S.𝓕 T] (fun ω => kOut S Λ P a m T ω / wedge S ϑ Λ P T ω) ∧
      BddAt S (fun ω => kOut S Λ P a m T ω / wedge S ϑ Λ P T ω) := by
  have hwm : StronglyMeasurable[S.𝓕 T] (wedge S ϑ Λ P T) :=
    stronglyMeasurable_const.add ((hp.stronglyMeasurable_iota T).const_mul ϑ)
  have hKm : StronglyMeasurable[S.𝓕 T] (claimCost S Λ P a T) :=
    ((S.stronglyMeasurable_E T _).measurable.div
      (hp.stronglyMeasurable_pk T).measurable).stronglyMeasurable
  have hKb : BddAt S (claimCost S Λ P a T) :=
    ((((hp.pk_bdd (T + 1)).mul (hab (T + 1))).E T).mul (hp.pk_inv_bdd T)).congr
      (Eventually.of_forall fun ω => by simp [claimCost, div_eq_mul_inv])
  exact ⟨((((hKm).add ((hp.stronglyMeasurable_bondPrice T).mul ((hp.2.1 T).mul
      (hf.2.2.1 T)))).measurable.div (hp.2.1 T).measurable).div hwm.measurable).stronglyMeasurable,
    (((hKb.add ((hp.bondPrice_bdd T).mul ((hp.2.2.2.2 T).2.2.1.mul (hmb T)))).mul
      (hp.2.2.2.2 T).2.2.2).mul (hwb T)).congr
      (Eventually.of_forall fun ω => by simp [kOut, div_eq_mul_inv])⟩

end Cochrane.Monetarism.HouseholdMeasureTVC
