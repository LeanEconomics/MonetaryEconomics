/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.HouseholdMeasure

/-!
# Perpetual rollover deviations under weak price regularity

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 439–441
(eqs. (19.10)–(19.12) and footnote 1) and §19.5.1, pp. 448–449 (eqs. (19.27)–(19.30)), for the
household problem of `HouseholdMeasure` on a probability space. This module builds the deviations
used to derive the first-order conditions and the transversality condition without the regularity
hypotheses of `HouseholdMeasure.PriceRegular`.

## Weak price regularity

`PriceWeak`: the state prices `Λ` and the price level `P` are adapted and positive, and the
nominal state-price density `pk_t = Λ_t/P_t` is integrable at every date (the date-0 price of one
dollar at `t` is finite, so the bond price `Q_t = E_t[pk_{t+1}]/pk_t` is a genuine conditional
expectation). No bound on `Λ`, `P`, `1/Λ` or `1/P` is assumed. `PriceRegular` implies it
(`priceWeak_of_priceRegular`).

## Homogeneous deviations

`HomDev`: an increment `(dc, dm, da)` to consumption, real balances and claims that satisfies the
flow constraint with zero endowment, taxes and initial money, is adapted, has the integrability
that `HouseholdMeasure.Feasible` requires, and whose date-0 value of wealth is eventually a
constant `D`. Adding `ε` times such an increment to a feasible plan keeps every requirement of
`Feasible` except possibly the no-Ponzi condition, which then holds as soon as the wealth value
shifted by `εD` satisfies it (`feasible_add`); with `D = 0` the no-Ponzi condition is untouched.
Increments add (`HomDev.add`).

## The perpetual rollover

`rollC`, `rollA`, `rollX`: consume `z` and hold `ζ` more real balances at date `t` (both known
at `t`), and finance the cost by issuing at `t` the state-contingent claim
`−P_tζ + X/pk_{t+1}` maturing at `t + 1` and rolling over `X/pk_n` forever after, with
`X = −Λ_t(z + ι_tζ)`. The date-0 value of the debt stays `E[X]` for ever (`roll_homDev`): the
household never repays, and the no-Ponzi condition only sees the constant `E[X]`. Two such
deviations at different dates whose values `E[X]` cancel are budget-neutral.
-/

namespace Cochrane.Monetarism.TidyR6HouseholdRoll

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Weak price regularity -/

variable (S) in
/-- Cochrane (2023), p. 439 ("complete contingent claim markets with state price `Λ_t`") and
(19.15), p. 441: the weak regularity of the state prices and the price level: both adapted and
positive, and the nominal state-price density `pk_t = Λ_t/P_t` integrable at every date, so that
the bond price `Q_t = E_t[pk_{t+1}]/pk_t` is a genuine conditional expectation. -/
def PriceWeak (Λ P : ℕ → Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 Λ ∧ StronglyAdapted S.𝓕 P ∧ (∀ t ω, 0 < Λ t ω) ∧ (∀ t ω, 0 < P t ω) ∧
    ∀ t, Integrable (pk Λ P t) S.μ

/-- Cochrane (2023), p. 439: the regularity hypothesis `HouseholdMeasure.PriceRegular` (bounds on
`Λ`, `P` and their reciprocals) implies the weak regularity `PriceWeak`. -/
theorem priceWeak_of_priceRegular {Λ P : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P) :
    PriceWeak S Λ P :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.integrable_pk⟩

namespace PriceWeak

variable {Λ P : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 439: the nominal state-price density is positive. -/
theorem pk_pos (hp : PriceWeak S Λ P) (t : ℕ) (ω : Ω) : 0 < pk Λ P t ω :=
  div_pos (hp.2.2.1 t ω) (hp.2.2.2.1 t ω)

/-- Cochrane (2023), p. 439: `pk_t P_t = Λ_t`. -/
theorem pk_mul_P (hp : PriceWeak S Λ P) (t : ℕ) (ω : Ω) : pk Λ P t ω * P t ω = Λ t ω := by
  have := (hp.2.2.2.1 t ω).ne'
  simp only [pk]
  field_simp

/-- Cochrane (2023), p. 439: the nominal state-price density is known at `t`. -/
theorem sm_pk (hp : PriceWeak S Λ P) (t : ℕ) : StronglyMeasurable[S.𝓕 t] (pk Λ P t) :=
  ((hp.1 t).measurable.div (hp.2.1 t).measurable).stronglyMeasurable

/-- Cochrane (2023), (19.15), p. 441: the bond price is known at `t`. -/
theorem sm_bondPrice (hp : PriceWeak S Λ P) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (bondPrice S Λ P t) :=
  ((S.stronglyMeasurable_E t _).measurable.div (hp.sm_pk t).measurable).stronglyMeasurable

/-- Cochrane (2023), (19.12), p. 439: the interest cost `ι_t` is known at `t`. -/
theorem sm_iota (hp : PriceWeak S Λ P) (t : ℕ) : StronglyMeasurable[S.𝓕 t] (iota S Λ P t) :=
  stronglyMeasurable_const.sub (hp.sm_bondPrice t)

/-- Cochrane (2023), (19.15), p. 441: `E_t[pk_{t+1}] = Q_t pk_t`. -/
theorem E_pk_eq (hp : PriceWeak S Λ P) (t : ℕ) (ω : Ω) :
    S.E t (pk Λ P (t + 1)) ω = bondPrice S Λ P t ω * pk Λ P t ω := by
  have := (hp.pk_pos t ω).ne'
  simp only [bondPrice]
  field_simp

/-- Cochrane (2023), (19.12), p. 439: `Λ_tι_t = Λ_t − P_tE_t[pk_{t+1}]`. -/
theorem lam_iota (hp : PriceWeak S Λ P) (t : ℕ) (ω : Ω) :
    Λ t ω * iota S Λ P t ω = Λ t ω - P t ω * S.E t (pk Λ P (t + 1)) ω := by
  rw [hp.E_pk_eq t ω, ← hp.pk_mul_P t ω]
  simp only [iota]
  ring

end PriceWeak

/-! ### Linearity of the flow constraint -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), (19.10), p. 439: the money brought into a date is linear in real balances,
`M'_{t−1} = M_{t−1} + εdM_{t−1}` when `m' = m + εdm` (the increment brings no initial money). -/
theorem moneyIn_add (N0 : Ω → ℝ) (P m dm : ℕ → Ω → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) :
    moneyIn N0 P (fun k ω => m k ω + ε * dm k ω) n ω =
      moneyIn N0 P m n ω + ε * moneyIn 0 P dm n ω := by
  cases n with
  | zero => simp [moneyIn]
  | succ k =>
    simp only [moneyIn]
    ring

/-- Cochrane (2023), p. 439: the cost of claims is linear in the claims (almost surely), when the
claims are integrable against the state prices. -/
theorem claimCost_add {Λ P a da : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P) {n : ℕ}
    (ha : Integrable (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) S.μ)
    (hda : Integrable (fun ω => pk Λ P (n + 1) ω * da (n + 1) ω) S.μ) (ε : ℝ) :
    ∀ᵐ ω ∂S.μ, claimCost S Λ P (fun k ω => a k ω + ε * da k ω) n ω =
      claimCost S Λ P a n ω + ε * claimCost S Λ P da n ω := by
  have e : (fun ω => pk Λ P (n + 1) ω * (a (n + 1) ω + ε * da (n + 1) ω)) =
      (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) +
        ε • (fun ω => pk Λ P (n + 1) ω * da (n + 1) ω) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  filter_upwards [S.E_add ha (hda.smul ε) n, S.E_smul ε (fun ω => pk Λ P (n + 1) ω *
    da (n + 1) ω) n] with ω h1 h2
  have hk := (hp.pk_pos n ω).ne'
  simp only [claimCost]
  rw [e, h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Cochrane (2023), (19.10), p. 439 (the flow constraint is linear): if `(c, m, a)` satisfies the
flow constraint and `(dc, dm, da)` satisfies it with zero endowment, taxes and initial money, then
`(c + εdc, m + εdm, a + εda)` satisfies the flow constraint. -/
theorem flow_add {Λ P y s : ℕ → Ω → ℝ} {N0 : Ω → ℝ} {c m a dc dm da : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hf : Flow S Λ P y s N0 c m a) (hd : Flow S Λ P 0 0 0 dc dm da)
    (ha : ∀ n, Integrable (fun ω => pk Λ P n ω * a n ω) S.μ)
    (hda : ∀ n, Integrable (fun ω => pk Λ P n ω * da n ω) S.μ) (ε : ℝ) :
    Flow S Λ P y s N0 (fun n ω => c n ω + ε * dc n ω) (fun n ω => m n ω + ε * dm n ω)
      (fun n ω => a n ω + ε * da n ω) := by
  intro n
  filter_upwards [hf n, hd n, claimCost_add hp (ha (n + 1)) (hda (n + 1)) ε] with ω h1 h2 h3
  rw [moneyIn_add, h3]
  simp only [Pi.zero_apply] at h2
  linear_combination h1 + ε * h2

/-- Cochrane (2023), (19.11)–(19.12), p. 439: the date-0 value of wealth is linear in the plan:
for `m' = m + εdm`, `a' = a + εda`, `E[pk_T(a'_T + M'_{T−1})] = E[pk_T(a_T + M_{T−1})] +
εE[pk_T(da_T + dM_{T−1})]`. -/
theorem wealthPV_add {Λ P : ℕ → Ω → ℝ} {N0 : Ω → ℝ} {m a dm da : ℕ → Ω → ℝ} {T : ℕ}
    (ha : Integrable (fun ω => pk Λ P T ω * a T ω) S.μ)
    (hN : Integrable (fun ω => pk Λ P T ω * moneyIn N0 P m T ω) S.μ)
    (hda : Integrable (fun ω => pk Λ P T ω * da T ω) S.μ)
    (hdN : Integrable (fun ω => pk Λ P T ω * moneyIn 0 P dm T ω) S.μ) (ε : ℝ) :
    wealthPV S Λ P N0 (fun n ω => m n ω + ε * dm n ω) (fun n ω => a n ω + ε * da n ω) T =
      wealthPV S Λ P N0 m a T + ε * wealthPV S Λ P 0 dm da T := by
  have h1 : Integrable (fun ω => pk Λ P T ω * (a T ω + moneyIn N0 P m T ω)) S.μ :=
    (ha.add hN).congr (Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring)
  have h2 : Integrable (fun ω => ε * (pk Λ P T ω * (da T ω + moneyIn 0 P dm T ω))) S.μ :=
    ((hda.add hdN).const_mul ε).congr
      (Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring)
  simp only [wealthPV]
  rw [← integral_const_mul, ← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [moneyIn_add]
  ring

/-! ### Homogeneous deviations -/

variable (S) in
/-- Cochrane (2023), footnote 1, p. 440 (perturbing a plan): an increment `(dc, dm, da)` to
consumption, real balances and claims that changes no initial claim, is adapted, satisfies the
flow constraint (19.10) with zero endowment, taxes and initial money, has the integrability of
`HouseholdMeasure.Feasible`, and whose date-0 value of wealth `E[pk_T(da_T + dM_{T−1})]` is
eventually the constant `D`. -/
def HomDev (Λ P : ℕ → Ω → ℝ) (dc dm da : ℕ → Ω → ℝ) (D : ℝ) : Prop :=
  da 0 = 0 ∧ StronglyAdapted S.𝓕 dc ∧ StronglyAdapted S.𝓕 dm ∧ StronglyAdapted S.𝓕 da ∧
    Flow S Λ P 0 0 0 dc dm da ∧ (∀ t, Integrable (fun ω => pk Λ P t ω * da t ω) S.μ) ∧
    (∀ t, Integrable (fun ω => pk Λ P t ω * moneyIn 0 P dm t ω) S.μ) ∧
    (∀ t, Integrable (fun ω => Λ t ω * dm t ω) S.μ) ∧
    (∀ t, Integrable (fun ω => Λ t ω * dc t ω) S.μ) ∧
    ∀ᶠ T in atTop, wealthPV S Λ P 0 dm da T = D

/-- Cochrane (2023), footnote 1, p. 440 and (19.10)–(19.12), p. 439: **adding a homogeneous
deviation to a feasible plan.** If `(c, m, a)` is feasible and `(dc, dm, da)` is a homogeneous
deviation with eventual wealth value `D`, then `(c + εdc, m + εdm, a + εda)` is feasible as soon
as the shifted wealth value `E[pk_T(a_T + M_{T−1})] + εD` satisfies the no-Ponzi condition. -/
theorem feasible_add {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a dc dm da : ℕ → Ω → ℝ}
    {D ε : ℝ} (hp : PriceWeak S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a)
    (hd : HomDev S Λ P dc dm da D)
    (hnp : ∀ δ, 0 < δ → ∀ᶠ T in atTop, -δ ≤ wealthPV S Λ P N0 m a T + ε * D) :
    Feasible S Λ P y s N0 a0 (fun n ω => c n ω + ε * dc n ω) (fun n ω => m n ω + ε * dm n ω)
      (fun n ω => a n ω + ε * da n ω) := by
  obtain ⟨ha0, hca, hma, haa, hflow, hia, hiN, him, hic, -⟩ := hf
  obtain ⟨hd0, hdc, hdm, hda, hdflow, hdia, hdiN, hdim, hdic, hdD⟩ := hd
  refine ⟨?_, fun n => (hca n).add ((hdc n).const_mul ε),
    fun n => (hma n).add ((hdm n).const_mul ε), fun n => (haa n).add ((hda n).const_mul ε),
    flow_add hp hflow hdflow hia hdia ε, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · funext ω
    simp [hd0, ← ha0]
  · refine ((hia n).add ((hdia n).const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · refine ((hiN n).add ((hdiN n).const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, moneyIn_add]
    ring
  · refine ((him n).add ((hdim n).const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · refine ((hic n).add ((hdic n).const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · intro δ hδ
    filter_upwards [hnp δ hδ, hdD] with T h1 h2
    rw [wealthPV_add (hia T) (hiN T) (hdia T) (hdiN T) ε, h2]
    exact h1

/-- Cochrane (2023), footnote 1, p. 440: **homogeneous deviations add**: the sum of two
homogeneous deviations is homogeneous, and its eventual wealth value is the sum. -/
theorem HomDev.add {Λ P : ℕ → Ω → ℝ} {dc dm da dc' dm' da' : ℕ → Ω → ℝ} {D D' : ℝ}
    (hp : PriceWeak S Λ P) (h : HomDev S Λ P dc dm da D) (h' : HomDev S Λ P dc' dm' da' D') :
    HomDev S Λ P (fun n ω => dc n ω + dc' n ω) (fun n ω => dm n ω + dm' n ω)
      (fun n ω => da n ω + da' n ω) (D + D') := by
  obtain ⟨hd0, hdc, hdm, hda, hdflow, hdia, hdiN, hdim, hdic, hdD⟩ := h
  obtain ⟨hd0', hdc', hdm', hda', hdflow', hdia', hdiN', hdim', hdic', hdD'⟩ := h'
  have hfl := flow_add hp hdflow hdflow' hdia hdia' 1
  simp only [one_mul] at hfl
  refine ⟨?_, fun n => (hdc n).add (hdc' n), fun n => (hdm n).add (hdm' n),
    fun n => (hda n).add (hda' n), hfl, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · funext ω
    simp [hd0, hd0']
  · refine ((hdia n).add (hdia' n)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · refine ((hdiN n).add (hdiN' n)).congr (Eventually.of_forall fun ω => ?_)
    have := moneyIn_add 0 P dm dm' 1 n ω
    simp only [one_mul] at this
    simp only [Pi.add_apply, this]
    ring
  · refine ((hdim n).add (hdim' n)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · refine ((hdic n).add (hdic' n)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · filter_upwards [hdD, hdD'] with T h1 h2
    have := wealthPV_add (N0 := 0) (hdia T) (hdiN T) (hdia' T) (hdiN' T) 1
    simp only [one_mul] at this
    rw [this, h1, h2]

/-! ### The perpetual rollover -/

variable (S) in
/-- Cochrane (2023), (19.12), p. 439 and footnote 1, p. 440: the date-0 value of the debt issued
to finance consuming `z` and holding `ζ` more real balances at `t`,
`X = −Λ_t(z + ι_tζ)` (the bundle costs `z + ι_tζ` date-`t` goods). -/
noncomputable def rollX (Λ P : ℕ → Ω → ℝ) (t : ℕ) (z ζ : Ω → ℝ) (ω : Ω) : ℝ :=
  -(Λ t ω * (z ω + iota S Λ P t ω * ζ ω))

/-- Cochrane (2023), footnote 1, p. 440: a change `z` at date `t` only. -/
def rollC (t : ℕ) (z : Ω → ℝ) : ℕ → Ω → ℝ := fun n ω => if n = t then z ω else 0

variable (S) in
/-- Cochrane (2023), footnote 1, p. 440 and (19.10), p. 439: the claims of the perpetual
rollover: nothing up to `t`, then `−P_tζ + X/pk_{t+1}` at `t + 1` (the money `P_tζ` carried into
`t + 1` replaces part of the claims) and `X/pk_n` at every later date (the debt is rolled over
for ever at constant date-0 value `X`). -/
noncomputable def rollA (Λ P : ℕ → Ω → ℝ) (t : ℕ) (z ζ : Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if n ≤ t then 0 else
    (if n = t + 1 then -(P t ω * ζ ω) else 0) + rollX S Λ P t z ζ ω / pk Λ P n ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), footnote 1, p. 440: money brought into a date by the rollover: `P_tζ` into
`t + 1`, nothing otherwise. -/
theorem moneyIn_rollC (P : ℕ → Ω → ℝ) (t : ℕ) (ζ : Ω → ℝ) (n : ℕ) (ω : Ω) :
    moneyIn 0 P (rollC t ζ) n ω = if n = t + 1 then P t ω * ζ ω else 0 := by
  cases n with
  | zero => simp [moneyIn]
  | succ k =>
    simp only [moneyIn, rollC, add_left_inj]
    by_cases h : k = t <;> simp [h]

/-- Cochrane (2023), (19.10), p. 439 and footnote 1, p. 440: **the perpetual rollover is a
homogeneous deviation.** For `z`, `ζ` known at `t` with `Λ_tz`, `Λ_tζ`, `pk_{t+1}P_tζ` and
`X = −Λ_t(z + ι_tζ)` integrable, consuming `z` and holding `ζ` more at `t`, financed by the claims
`rollA`, satisfies the flow constraint with zero endowment at every date, and its date-0 wealth
value is `E[X]` at every date after `t`. -/
theorem roll_homDev {Λ P : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P) {t : ℕ} {z ζ : Ω → ℝ}
    (hz : StronglyMeasurable[S.𝓕 t] z) (hζ : StronglyMeasurable[S.𝓕 t] ζ)
    (hiz : Integrable (fun ω => Λ t ω * z ω) S.μ) (hiζ : Integrable (fun ω => Λ t ω * ζ ω) S.μ)
    (hiM : Integrable (fun ω => pk Λ P (t + 1) ω * (P t ω * ζ ω)) S.μ)
    (hiX : Integrable (rollX S Λ P t z ζ) S.μ) :
    HomDev S Λ P (rollC t z) (rollC t ζ) (rollA S Λ P t z ζ) (∫ ω, rollX S Λ P t z ζ ω ∂S.μ) := by
  set X := rollX S Λ P t z ζ with hXdef
  have hXm : StronglyMeasurable[S.𝓕 t] X :=
    (((hp.1 t).mul (hz.add ((hp.sm_iota t).mul hζ))).neg)
  have hle : ∀ {n}, t ≤ n → S.𝓕 t ≤ S.𝓕 n := fun h => S.𝓕.mono h
  have hpkX : ∀ n ω, pk Λ P n ω * (X ω / pk Λ P n ω) = X ω := fun n ω => by
    have := (hp.pk_pos n ω).ne'
    field_simp
  have hEX : ∀ n, t ≤ n → S.E n X =ᵐ[S.μ] X := fun n h =>
    Eventually.of_forall fun ω => by
      rw [S.E_of_stronglyMeasurable (hXm.mono (hle h)) hiX]
  -- the claims times the state price
  have hpa : ∀ n, (fun ω => pk Λ P n ω * rollA S Λ P t z ζ n ω) = fun ω =>
      if n ≤ t then 0 else (if n = t + 1 then -(pk Λ P n ω * (P t ω * ζ ω)) else 0) + X ω := by
    intro n
    funext ω
    simp only [rollA]
    split_ifs <;> simp [mul_add, ← hXdef, hpkX]
  have hia : ∀ n, Integrable (fun ω => pk Λ P n ω * rollA S Λ P t z ζ n ω) S.μ := by
    intro n
    rw [hpa n]
    by_cases h1 : n ≤ t
    · simp only [h1, ↓reduceIte]
      exact integrable_zero _ _ _
    · simp only [h1, ↓reduceIte]
      by_cases h2 : n = t + 1
      · subst h2
        simp only [↓reduceIte]
        exact hiM.neg.add hiX
      · simp only [h2, ↓reduceIte, zero_add]
        exact hiX
  refine ⟨by funext ω; simp [rollA], ?_, ?_, ?_, ?_, hia, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases h : n = t
    · subst h
      have e : rollC n z n = z := by funext ω; simp [rollC]
      rw [e]
      exact hz
    · have e : rollC t z n = fun _ => 0 := by funext ω; simp [rollC, h]
      rw [e]
      exact stronglyMeasurable_const
  · intro n
    by_cases h : n = t
    · subst h
      have e : rollC n ζ n = ζ := by funext ω; simp [rollC]
      rw [e]
      exact hζ
    · have e : rollC t ζ n = fun _ => 0 := by funext ω; simp [rollC, h]
      rw [e]
      exact stronglyMeasurable_const
  · intro n
    by_cases h1 : n ≤ t
    · have e : rollA S Λ P t z ζ n = fun _ => 0 := by funext ω; simp [rollA, h1]
      rw [e]
      exact stronglyMeasurable_const
    · have e : rollA S Λ P t z ζ n = fun ω => (if n = t + 1 then -(P t ω * ζ ω) else 0) +
          X ω / pk Λ P n ω := by funext ω; simp [rollA, h1, hXdef]
      rw [e]
      have hn : t ≤ n := by omega
      refine StronglyMeasurable.add ?_ ((hXm.mono (hle hn)).measurable.div
        (hp.sm_pk n).measurable).stronglyMeasurable
      by_cases h2 : n = t + 1
      · simp only [h2, ↓reduceIte]
        exact (((hp.2.1 t).mul hζ).neg).mono (hle hn)
      · simp only [h2, ↓reduceIte]
        exact stronglyMeasurable_const
  · -- the flow constraint
    intro n
    rcases lt_trichotomy n t with h | h | h
    · -- before the deviation nothing changes
      have e1 : (fun ω => pk Λ P (n + 1) ω * rollA S Λ P t z ζ (n + 1) ω) = 0 := by
        rw [hpa]
        funext ω
        simp [show n + 1 ≤ t by omega]
      refine Eventually.of_forall fun ω => ?_
      rw [show claimCost S Λ P (rollA S Λ P t z ζ) n ω = S.E n (fun ω => pk Λ P (n + 1) ω *
        rollA S Λ P t z ζ (n + 1) ω) ω / pk Λ P n ω from rfl, e1, S.E_zero]
      simp [rollA, rollC, moneyIn_rollC, show n ≤ t by omega, show n ≠ t by omega,
        show n ≠ t + 1 by omega]
    · -- the deviation date
      subst h
      have e1 : (fun ω => pk Λ P (n + 1) ω * rollA S Λ P n z ζ (n + 1) ω) =
          (fun ω => -(P n ω * ζ ω)) * pk Λ P (n + 1) + X := by
        rw [hpa]
        funext ω
        simp only [show ¬ n + 1 ≤ n by omega, ↓reduceIte, ↓reduceIte, Pi.add_apply, Pi.mul_apply]
        ring
      have hfi : Integrable ((fun ω => -(P n ω * ζ ω)) * pk Λ P (n + 1)) S.μ :=
        hiM.neg.congr (Eventually.of_forall fun ω => by
          simp only [Pi.neg_apply, Pi.mul_apply]; ring)
      have hpull := condExp_mul_of_stronglyMeasurable_left (μ := S.μ) (m := S.𝓕 n)
        (f := fun ω => -(P n ω * ζ ω)) (((hp.2.1 n).mul hζ).neg) hfi (hp.2.2.2.2 (n + 1))
      filter_upwards [S.E_add hfi hiX n, hpull, hEX n le_rfl] with ω h1 h2 h3
      rw [show claimCost S Λ P (rollA S Λ P n z ζ) n ω = S.E n (fun ω => pk Λ P (n + 1) ω *
        rollA S Λ P n z ζ (n + 1) ω) ω / pk Λ P n ω from rfl, e1, h1, Pi.add_apply,
        show S.E n ((fun ω => -(P n ω * ζ ω)) * pk Λ P (n + 1)) ω =
          -(P n ω * ζ ω) * S.E n (pk Λ P (n + 1)) ω from h2, h3]
      have ra : rollA S Λ P n z ζ n ω = 0 := by simp [rollA]
      simp only [ra, moneyIn_rollC, rollC, ↓reduceIte, show n ≠ n + 1 by omega, Pi.zero_apply]
      have hk := (hp.pk_pos n ω).ne'
      have hl' : Λ n ω * (z ω + iota S Λ P n ω * ζ ω) = Λ n ω * z ω +
          (Λ n ω - P n ω * S.E n (pk Λ P (n + 1)) ω) * ζ ω := by
        rw [← hp.lam_iota n ω]
        ring
      rw [hXdef]
      simp only [rollX]
      rw [hl', ← hp.pk_mul_P n ω]
      field_simp
      ring
    · -- after the deviation the debt is rolled over
      have e1 : (fun ω => pk Λ P (n + 1) ω * rollA S Λ P t z ζ (n + 1) ω) = X := by
        rw [hpa]
        funext ω
        simp [show ¬ n + 1 ≤ t by omega, show n ≠ t by omega]
      filter_upwards [hEX n h.le] with ω h3
      rw [show claimCost S Λ P (rollA S Λ P t z ζ) n ω = S.E n (fun ω => pk Λ P (n + 1) ω *
        rollA S Λ P t z ζ (n + 1) ω) ω / pk Λ P n ω from rfl, e1, h3]
      have hk := (hp.pk_pos n ω).ne'
      simp only [rollA, moneyIn_rollC, rollC, Pi.zero_apply, show ¬ n ≤ t by omega,
        show n ≠ t by omega, ↓reduceIte, ← hXdef]
      by_cases h2 : n = t + 1
      · simp only [h2, ↓reduceIte]
        ring
      · simp only [h2, ↓reduceIte]
        ring
  · intro n
    simp only [moneyIn_rollC]
    by_cases h : n = t + 1
    · subst h
      simpa using hiM
    · simp only [h, ↓reduceIte, mul_zero]
      exact integrable_zero _ _ _
  · intro n
    by_cases h : n = t
    · subst h
      simpa [rollC] using hiζ
    · simp only [rollC, h, ↓reduceIte, mul_zero]
      exact integrable_zero _ _ _
  · intro n
    by_cases h : n = t
    · subst h
      simpa [rollC] using hiz
    · simp only [rollC, h, ↓reduceIte, mul_zero]
      exact integrable_zero _ _ _
  · filter_upwards [eventually_gt_atTop t] with T hT
    simp only [wealthPV]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have := congrFun (hpa T) ω
    simp only [moneyIn_rollC, mul_add]
    rw [this]
    simp only [show ¬ T ≤ t by omega, ↓reduceIte]
    by_cases h2 : T = t + 1
    · simp only [h2, ↓reduceIte]
      ring
    · simp [h2]

end Cochrane.Monetarism.TidyR6HouseholdRoll
