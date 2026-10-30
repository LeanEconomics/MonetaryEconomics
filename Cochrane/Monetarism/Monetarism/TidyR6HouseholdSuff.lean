/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdFOC

/-!
# Sufficiency with the liminf transversality condition, under weak price regularity

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 439–441 and p. 453
("first order conditions and transversality conditions are necessary and sufficient"), on a
probability space (`HouseholdMeasure`), with the prices satisfying only
`TidyR6HouseholdRoll.PriceWeak`.

## Main results

* `wealth_step_w`, `wealth_telescope_w`: the one-period and iterated forms of the present-value
  budget (19.12)/(19.30), restated from `HouseholdMeasure.wealth_step` and
  `HouseholdMeasure.wealth_telescope` with `PriceWeak` in place of `PriceRegular` (their proofs
  never used the bounds).
* `optimal_of_supergradient_liminf`: the sufficiency theorem
  `HouseholdMeasure.optimal_of_supergradient` with `PriceWeak` prices and the transversality
  condition weakened to its liminf form: `E[pk_T(a_T + M_{T−1})] < L` infinitely often for every
  `L > 0`.
* **`miu_optimal_iff`**: for a money-in-utility household whose utility is `C¹` on an open domain,
  has a supergradient there and `u_c > 0`, a feasible admissible plan in the domain is optimal if
  and only if there is a constant `λ > 0` with `βᵗu_c = λΛ_t`, `βᵗu_m = λΛ_tι_t` almost surely at
  every date and the liminf transversality condition holds. This characterises the household
  optimum without regularity hypotheses; the full limit `E[pk_T(a_T + M_{T−1})] → 0` is not part
  of it (`TidyR6HouseholdTVCCx.tvc_needs_reference` shows it can fail at an optimum).
-/

namespace Cochrane.Monetarism.TidyR6HouseholdSuff

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  TidyR6HouseholdRoll TidyR6HouseholdLocal TidyR6HouseholdFOC

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), (19.12), p. 439 and (19.30), p. 449 (iterating the flow constraint one
period), restated from `HouseholdMeasure.wealth_step` under `PriceWeak`: for a feasible plan the
date-`t` outlay is integrable and
`E[pk_t(a_t + M_{t−1})] = E[pk_{t+1}(a_{t+1} + M_t)] + E[Λ_t(c_t + ι_tm_t + s_t − y_t)]`. -/
theorem wealth_step_w {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a) (t : ℕ) :
    Integrable (outlay S Λ P y s c m t) S.μ ∧
      wealthPV S Λ P N0 m a t = wealthPV S Λ P N0 m a (t + 1) +
        ∫ ω, outlay S Λ P y s c m t ω ∂S.μ := by
  obtain ⟨-, -, hma, -, hflow, hia, hiN, him, hic, -⟩ := hf
  -- the money carried into `t + 1`
  have hNm : StronglyMeasurable[S.𝓕 t] (fun ω => P t ω * m t ω) := (hp.2.1 t).mul (hma t)
  have hNi : Integrable ((fun ω => P t ω * m t ω) * pk Λ P (t + 1)) S.μ :=
    (hiN (t + 1)).congr (Eventually.of_forall fun ω => by
      simp only [moneyIn, Pi.mul_apply]
      ring)
  have hpull := condExp_mul_of_stronglyMeasurable_left hNm hNi (hp.2.2.2.2 (t + 1))
  have hQm : (fun ω => P t ω * m t ω) * S.E t (pk Λ P (t + 1)) =
      fun ω => bondPrice S Λ P t ω * (Λ t ω * m t ω) := by
    funext ω
    simp only [Pi.mul_apply]
    rw [hp.E_pk_eq t ω, ← hp.pk_mul_P t ω]
    ring
  rw [hQm] at hpull
  have hQi : Integrable (fun ω => bondPrice S Λ P t ω * (Λ t ω * m t ω)) S.μ :=
    integrable_condExp.congr hpull
  have hQint : ∫ ω, P t ω * m t ω * pk Λ P (t + 1) ω ∂S.μ =
      ∫ ω, bondPrice S Λ P t ω * (Λ t ω * m t ω) ∂S.μ := by
    rw [← integral_congr_ae hpull]
    exact (integral_condExp (S.𝓕.le t)).symm
  have hout : outlay S Λ P y s c m t = fun ω => Λ t ω * c t ω + (Λ t ω * m t ω -
      bondPrice S Λ P t ω * (Λ t ω * m t ω)) + Λ t ω * s t ω - Λ t ω * y t ω := by
    funext ω
    simp only [outlay, iota]
    ring
  have hoi : Integrable (outlay S Λ P y s c m t) S.μ := by
    rw [hout]
    exact (((hic t).add ((him t).sub hQi)).add (hs t)).sub (hy t)
  refine ⟨hoi, ?_⟩
  -- integrate the flow constraint multiplied by `pk_t`
  have hfl : ∀ᵐ ω ∂S.μ, pk Λ P t ω * a t ω + pk Λ P t ω * moneyIn N0 P m t ω +
      Λ t ω * y t ω - Λ t ω * c t ω = S.E t (fun ω => pk Λ P (t + 1) ω * a (t + 1) ω) ω +
        Λ t ω * m t ω + Λ t ω * s t ω := by
    filter_upwards [hflow t] with ω h
    have hk := (hp.pk_pos t ω).ne'
    have hΛ := (hp.pk_mul_P t ω).symm
    simp only [claimCost] at h
    rw [hΛ]
    have := congrArg (fun x => pk Λ P t ω * x) h
    field_simp at this
    linear_combination this
  have hI := integral_congr_ae hfl
  have i1 : Integrable (fun ω => pk Λ P t ω * a t ω + pk Λ P t ω * moneyIn N0 P m t ω) S.μ :=
    (hia t).add (hiN t)
  have i2 : Integrable (fun ω => pk Λ P t ω * a t ω + pk Λ P t ω * moneyIn N0 P m t ω +
      Λ t ω * y t ω) S.μ := i1.add (hy t)
  have j1 : Integrable (fun ω => S.E t (fun ω => pk Λ P (t + 1) ω * a (t + 1) ω) ω +
      Λ t ω * m t ω) S.μ := (S.integrable_E t _).add (him t)
  rw [integral_sub i2 (hic t), integral_add i1 (hy t), integral_add (hia t) (hiN t),
    integral_add j1 (hs t), integral_add (S.integrable_E t _) (him t), S.integral_E] at hI
  have hw1 : wealthPV S Λ P N0 m a t = ∫ ω, pk Λ P t ω * a t ω ∂S.μ +
      ∫ ω, pk Λ P t ω * moneyIn N0 P m t ω ∂S.μ := by
    rw [← integral_add (hia t) (hiN t)]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have hw2 : wealthPV S Λ P N0 m a (t + 1) = ∫ ω, pk Λ P (t + 1) ω * a (t + 1) ω ∂S.μ +
      ∫ ω, P t ω * m t ω * pk Λ P (t + 1) ω ∂S.μ := by
    have hNi' : Integrable (fun ω => P t ω * m t ω * pk Λ P (t + 1) ω) S.μ := hNi
    rw [← integral_add (hia (t + 1)) hNi']
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [moneyIn]; ring)
  have ho : ∫ ω, outlay S Λ P y s c m t ω ∂S.μ = ∫ ω, Λ t ω * c t ω ∂S.μ +
      (∫ ω, Λ t ω * m t ω ∂S.μ - ∫ ω, bondPrice S Λ P t ω * (Λ t ω * m t ω) ∂S.μ) +
      ∫ ω, Λ t ω * s t ω ∂S.μ - ∫ ω, Λ t ω * y t ω ∂S.μ := by
    have k1 : Integrable (fun ω => Λ t ω * m t ω -
        bondPrice S Λ P t ω * (Λ t ω * m t ω)) S.μ := (him t).sub hQi
    have k2 : Integrable (fun ω => Λ t ω * c t ω + (Λ t ω * m t ω -
        bondPrice S Λ P t ω * (Λ t ω * m t ω))) S.μ := (hic t).add k1
    have k3 : Integrable (fun ω => Λ t ω * c t ω + (Λ t ω * m t ω -
        bondPrice S Λ P t ω * (Λ t ω * m t ω)) + Λ t ω * s t ω) S.μ := k2.add (hs t)
    rw [hout, integral_sub k3 (hy t), integral_add k2 (hs t), integral_add (hic t) k1,
      integral_sub (him t) hQi]
  rw [hw1, hw2, ho, hQint]
  linarith

/-- Cochrane (2023), (19.12), p. 439 and (19.30), p. 449 (iterating the flow constraint
forward): `E[pk_0(a_0 + M_{−1})] = ∑_{t<T} E[Λ_t(c_t + ι_tm_t + s_t − y_t)] + E[pk_T(a_T +
M_{T−1})]`. Restated from `HouseholdMeasure.wealth_telescope` under `PriceWeak` in place of
`PriceRegular`. -/
theorem wealth_telescope_w {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceWeak S Λ P) (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a) (T : ℕ) :
    wealthPV S Λ P N0 m a 0 = ∑ t ∈ Finset.range T, ∫ ω, outlay S Λ P y s c m t ω ∂S.μ +
      wealthPV S Λ P N0 m a T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, (wealth_step_w hp hy hs hf T).2]
    ring

/-- Cochrane (2023), (19.28), p. 449: a sequence converging to `d` that is at most `b`
infinitely often has `d ≤ b`. -/
theorem le_of_tendsto_frequently {f : ℕ → ℝ} {d b : ℝ} (hf : Tendsto f atTop (𝓝 d))
    (hb : ∃ᶠ T in atTop, f T ≤ b) : d ≤ b := by
  by_contra h
  rw [not_le] at h
  obtain ⟨T, hT1, hT2⟩ := (hb.and_eventually ((tendsto_order.1 hf).1 b h)).exists
  linarith

/-- Cochrane (2023), footnote 1, p. 440 and p. 453 ("first order conditions and transversality
conditions are necessary and sufficient"), **sufficiency under weak regularity with the liminf
transversality condition**: a feasible, admissible plan satisfying `Con` is optimal if prices
satisfy `PriceWeak`, the endowment and taxes have integrable values, the supergradient form of
the first-order conditions holds against every feasible competitor satisfying `Con`
(`βᵗ(u(c'_t, m'_t) − u(c_t, m_t)) ≤ λΛ_t((c'_t − c_t) + ι_t(m'_t − m_t))`, `λ ≥ 0`), and the
date-0 value of wealth is below every `L > 0` infinitely often. Generalises
`HouseholdMeasure.optimal_of_supergradient` (`PriceWeak`, liminf transversality condition). -/
theorem optimal_of_supergradient_liminf {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ → ℝ}
    {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : Feasible S Λ P y s N0 a0 c m a) (hcon : Con c m)
    (hadm : UAdmissible S β (fun n ω => u (c n ω) (m n ω)))
    (hlim : ∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S Λ P N0 m a T < L)
    (hsup : ∀ c' m' a', Feasible S Λ P y s N0 a0 c' m' a' → Con c' m' → ∀ t, ∀ᵐ ω ∂S.μ,
      β ^ t * (u (c' t ω) (m' t ω) - u (c t ω) (m t ω)) ≤
        lam * (Λ t ω * ((c' t ω - c t ω) + iota S Λ P t ω * (m' t ω - m t ω)))) :
    Optimal S β u Con Λ P y s N0 a0 c m a := by
  refine ⟨hf, hcon, hadm, fun c' m' a' hf' hc' hu' => ?_⟩
  set U := expU S β (fun n ω => u (c n ω) (m n ω)) with hU
  set U' := expU S β (fun n ω => u (c' n ω) (m' n ω)) with hU'
  set D : ℕ → ℝ := fun t => β ^ t * ∫ ω, u (c' t ω) (m' t ω) ∂S.μ -
    β ^ t * ∫ ω, u (c t ω) (m t ω) ∂S.μ with hD
  have hDs : HasSum D (U' - U) := (hu'.hasSum hβ).sub (hadm.hasSum hβ)
  have hle : ∀ t, D t ≤ lam * (∫ ω, outlay S Λ P y s c' m' t ω ∂S.μ -
      ∫ ω, outlay S Λ P y s c m t ω ∂S.μ) := by
    intro t
    have hi' := hu'.integrable hβ t
    have hi := hadm.integrable hβ t
    have ho' := (wealth_step_w hp hy hs hf' t).1
    have ho := (wealth_step_w hp hy hs hf t).1
    have hL : Integrable (fun ω => β ^ t * (u (c' t ω) (m' t ω) - u (c t ω) (m t ω))) S.μ :=
      (hi'.sub hi).const_mul _
    have hR : Integrable (fun ω => lam * (outlay S Λ P y s c' m' t ω -
        outlay S Λ P y s c m t ω)) S.μ := (ho'.sub ho).const_mul _
    have hmono := integral_mono_ae hL hR (by
      filter_upwards [hsup c' m' a' hf' hc' t] with ω h
      refine h.trans_eq ?_
      simp only [outlay]
      ring)
    rw [integral_const_mul, integral_const_mul, integral_sub hi' hi, integral_sub ho' ho]
      at hmono
    simp only [hD]
    linarith
  have hpart : ∀ T, ∑ t ∈ Finset.range T, D t ≤
      lam * (wealthPV S Λ P N0 m a T - wealthPV S Λ P N0 m' a' T) := by
    intro T
    have h1 := wealth_telescope_w hp hy hs hf T
    have h2 := wealth_telescope_w hp hy hs hf' T
    have hW0 : wealthPV S Λ P N0 m' a' 0 = wealthPV S Λ P N0 m a 0 := by
      simp only [wealthPV, moneyIn, hf.1, hf'.1]
    calc ∑ t ∈ Finset.range T, D t
        ≤ ∑ t ∈ Finset.range T, lam * (∫ ω, outlay S Λ P y s c' m' t ω ∂S.μ -
          ∫ ω, outlay S Λ P y s c m t ω ∂S.μ) := Finset.sum_le_sum fun t _ => hle t
      _ = lam * (wealthPV S Λ P N0 m a T - wealthPV S Λ P N0 m' a' T) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
          congr 1
          linarith
  by_contra hcon'
  push Not at hcon'
  set d := U' - U with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set δ := d / (4 * (lam + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hfr : ∃ᶠ T in atTop, ∑ t ∈ Finset.range T, D t ≤ lam * (2 * δ) := by
    refine ((hlim δ hδ0).and_eventually (hf'.2.2.2.2.2.2.2.2.2 δ hδ0)).mono fun T hT => ?_
    refine (hpart T).trans (mul_le_mul_of_nonneg_left ?_ hlam)
    linarith [hT.1, hT.2]
  have := le_of_tendsto_frequently hDs.tendsto_sum_nat hfr
  have hlt : lam * (2 * δ) < d := by
    rw [hδ]
    have e : lam * (2 * (d / (4 * (lam + 1)))) = d * (lam / (2 * (lam + 1))) := by
      field_simp
      ring
    rw [e]
    have h1 : lam / (2 * (lam + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith
  linarith

/-- Cochrane (2023), (19.13)–(19.14), p. 440 and p. 453 ("first order conditions and
transversality conditions are necessary and sufficient"), **the money-in-utility household
optimum characterised without regularity hypotheses.** Let the utility be `C¹` on the open domain
`U`, with the supergradient inequality `u(q) ≤ u(p) + u_c(p)(q₁ − p₁) + u_m(p)(q₂ − p₂)` on `U`
(concavity) and `u_c > 0` on `U`; let prices satisfy `PriceWeak` and the endowment and taxes have
integrable values. A feasible, admissible plan lying in `U` is optimal among such plans if and only
if there is a constant `λ > 0` with `βᵗu_c(c_t, m_t) = λΛ_t` and `βᵗu_m(c_t, m_t) = λΛ_tι_t` almost
surely at every date, and the date-0 value of wealth has liminf zero (it is below every `L > 0`
infinitely often). -/
theorem miu_optimal_iff {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hu : C1On u uc um U)
    (hsg : ∀ p ∈ U, ∀ q ∈ U, u q.1 q.2 ≤ u p.1 p.2 + uc p.1 p.2 * (q.1 - p.1) +
      um p.1 p.2 * (q.2 - p.2))
    (hucpos : ∀ p ∈ U, 0 < uc p.1 p.2) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hp : PriceWeak S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a) (hdom : DomainCon S U c m)
    (hadm : UAdmissible S β (fun n ω => u (c n ω) (m n ω))) :
    Optimal S β u (DomainCon S U) Λ P y s N0 a0 c m a ↔
      ∃ lam : ℝ, 0 < lam ∧ (∀ t, (∀ᵐ ω ∂S.μ, β ^ t * uc (c t ω) (m t ω) = lam * Λ t ω) ∧
        ∀ᵐ ω ∂S.μ, β ^ t * um (c t ω) (m t ω) = lam * (Λ t ω * iota S Λ P t ω)) ∧
        ∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S Λ P N0 m a T < L := by
  constructor
  · intro hopt
    obtain ⟨lam, hlam⟩ := miu_multiplier hβ hu hopt hp
    have hpos0 : ∀ᵐ ω ∂S.μ, 0 < uc (c 0 ω) (m 0 ω) := by
      filter_upwards [hdom 0] with ω hω
      exact hucpos _ hω
    obtain ⟨ω, h1, h2⟩ := ((hlam 0).1.and hpos0).exists
    have hlampos : 0 < lam := by
      rw [pow_zero, one_mul] at h1
      rw [h1] at h2
      exact pos_of_mul_pos_left h2 (hp.2.2.1 0 ω).le
    exact ⟨lam, hlampos, hlam, (miu_liminf_tvc hβ hu hopt hp hpos0).2⟩
  · rintro ⟨lam, hlam0, hfoc, hlim⟩
    refine optimal_of_supergradient_liminf hβ hp hy hs hlam0.le hf hdom hadm hlim
      fun c' m' a' _ hdom' t => ?_
    filter_upwards [hdom t, hdom' t, (hfoc t).1, (hfoc t).2] with ω h1 h2 h3 h4
    have := hsg _ h1 _ h2
    have hb := mul_le_mul_of_nonneg_left (show u (c' t ω) (m' t ω) - u (c t ω) (m t ω) ≤
      uc (c t ω) (m t ω) * (c' t ω - c t ω) + um (c t ω) (m t ω) * (m' t ω - m t ω) by
        simp only at this
        linarith) (pow_nonneg hβ.le t)
    calc β ^ t * (u (c' t ω) (m' t ω) - u (c t ω) (m t ω))
        ≤ β ^ t * (uc (c t ω) (m t ω) * (c' t ω - c t ω) +
          um (c t ω) (m t ω) * (m' t ω - m t ω)) := hb
      _ = (β ^ t * uc (c t ω) (m t ω)) * (c' t ω - c t ω) +
          (β ^ t * um (c t ω) (m t ω)) * (m' t ω - m t ω) := by ring
      _ = lam * (Λ t ω * ((c' t ω - c t ω) + iota S Λ P t ω * (m' t ω - m t ω))) := by
          rw [h3, h4]
          ring

end Cochrane.Monetarism.TidyR6HouseholdSuff
