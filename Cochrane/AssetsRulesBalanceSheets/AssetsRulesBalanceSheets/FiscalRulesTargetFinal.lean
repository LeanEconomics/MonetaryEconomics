/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRulesTargetClose

/-!
# Theorem FR (d): exact existence, uniqueness without bounds above, and finite news

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR, error E9.9; the stochastic `P*_t` target, p. 267).

This module settles the three cases left open by `FiscalRulesTargetClose`, on genuine
measure-theoretic expectation systems (news may arrive at every date).

## The comparison identity

For two equilibria with price paths `P, P'`, the deflator `N_t⁻¹ = ∏_{i<t} γ_i⁻¹`
(`γ_t = E_t(P*_t/P*_{t+1})`, `defl`) and the scaled debt difference `Δ = (b − b')/θ`, the process
`K_t = βᵗ N_t⁻¹ (1/P_t − 1/P'_t) Δ_t` is a submartingale with drift
`βᵗ N_t⁻¹ (P'_t − P_t)²/(P_t P'_t) ≥ 0` (`drift_hasSum`). Whenever `E_0 K_T → 0`,
`∑_t E_0[βᵗ N_t⁻¹ (P'_t − P_t)²/(P_t P'_t)] = Δ_0 (1/P'_0 − 1/P_0)`, and `Δ_0 = 0` forces
`P = P'` (`drift_unique`).

## (2) Two equilibria bounded away from zero, unbounded above, any `b₀`

* `fr_unique_below_pair` (general `s₀`), `fr_unique_below_rule` (the book's rule): **uniqueness
  holds.** Two equilibria with prices bounded away from zero (neither need be bounded above) and the
  same initial debt — `b̄` or not — coincide, given only the date-`0` deflator bound
  `∏_{i<k} γ_i⁻¹ ≤ L`. Here `E_0 K_T → 0` because `|Δ_T| ≤ D_T + D'_T + const` (each debt
  deviation is bounded below, `value_lower`) and the transversality condition (`below_limit`).
* `compare_identity_below`: the identity itself, for any two initial debts.
* `fr_d_news_below_of_pair` (**link**): re-derives `FiscalRulesTargetClose.fr_d_news_below`.

## (1) Existence with `b₀ = b̄ + θ d₀ ≠ b̄`: the exact condition

* `exists_iff_pathwise`: a bounded-above equilibrium exists **iff** some positive adapted
  bounded `P` with integrable `1/P` meets the interest-rate target (9.12) and
  `∑ₛ βˢ (P_s − P*_s) = d₀` on almost every path (news in the target's present value is matched
  path by path; valuation and transversality are then automatic: `eqm_of_bdd`).
* `exists_iff_forward`: equivalently, the forward valuation `D = forwardSol β (P − P*)` — the
  unique bounded solution of the contraction `D_t = (P_t − P*_t) + β E_t D_{t+1}` — is
  predictable (`D_{t+1} = E_t D_{t+1}`) and starts at `d₀` (`forward_iff_pathwise`).
* `oneShot_exists_iff` (**special case**): on the one-shot system this is the scalar condition of
  `FiscalRulesTargetClose` (with positivity only a.e.).
* `exists_imp_pos` (necessary): `d₀ + ∑ₛ βˢ P*_s > 0` a.e.; `predetermined_exists_iff`: it is
  also sufficient when the target's present value is predetermined (news at any number of dates);
  `FiscalRulesTargetClose.NoExist.oneShot_no_eqm`: not sufficient when that value carries news.
* `compare_identity_above`, `price_monotone`: for bounded-above equilibria the identity needs
  no bound on the deflator, and the date-0 price level is nondecreasing in `d₀`.

## (3) Finite-horizon information: infinite news is needed

* `EventuallyResolved`, `resolved_hL`: if no news arrives after `T`, the deflator is bounded,
  `∏ γ⁻¹ ≤ (M*/m)^{2T+1}`; hence `fr_d_resolved` (`b₀ = b̄` gives `P = P*` for prices bounded
  away from zero) and `fr_unique_resolved`.
* `iid_not_resolved`: the system of `FiscalRulesBelowCounter.fr_below_counterexample` is never
  resolved; `finite_resolved`, `finite_hL`, `tree_fr_d` (**link**): every finite system — every
  bridged core finite tree — is resolved, so the counterexample cannot occur there.
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetFinal

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure FiscalRulesTargetMeasure FiscalRulesTargetOpen
open FiscalRulesTargetClose

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The target real rate and its deflator -/

/-- Cochrane (2023), eq. (9.12), p. 267: the target's gross real-rate factor
`γ_t = P*_t E_t(1/P*_{t+1}) = E_t(P*_t/P*_{t+1})`; the interest-rate target is
`1/(1 + i_t) = β γ_t`. -/
noncomputable def gam (Pstar : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Pstar t ω * S.E t (fun ω => 1 / Pstar (t + 1) ω) ω

/-- Cochrane (2023), eq. (9.12), p. 267: the cumulative target real-rate factor (the deflator)
`N_t⁻¹ = ∏_{i<t} γ_i⁻¹`; the bounded-deflator hypothesis of Theorem FR (d) is `N_t⁻¹ ≤ L`. -/
noncomputable def defl (Pstar : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range t, (gam S Pstar i ω)⁻¹

/-- Cochrane (2023), eq. (9.12), p. 267: `γ_t` is known at `t`. -/
theorem gam_meas {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (gam S Pstar t) :=
  (hPsa t).mul (S.stronglyMeasurable_E t _)

/-- Cochrane (2023), eq. (9.12), p. 267: for a target `0 < m ≤ P* ≤ M*`,
`m/M* ≤ γ_t ≤ M*/m` a.e. -/
theorem gam_bounds {m Ms : ℝ} {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hm : 0 < m) (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, m / Ms ≤ gam S Pstar t ω ∧ gam S Pstar t ω ≤ Ms / m := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hqsi : Integrable (fun ω => 1 / Pstar (t + 1) ω) S.μ :=
    Integrable.of_bound (((hPsm (t + 1)).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le (t + 1))).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 (t + 1) ω))]
        exact one_div_le_one_div_of_le hm (hPs (t + 1) ω).1)
  have h1 := S.E_mono (integrable_const (1 / Ms)) hqsi
    (Eventually.of_forall fun ω => one_div_le_one_div_of_le (hPs0 (t + 1) ω)
      (hPs (t + 1) ω).2) t
  have h2 := S.E_mono hqsi (integrable_const (1 / m))
    (Eventually.of_forall fun ω => one_div_le_one_div_of_le hm (hPs (t + 1) ω).1) t
  rw [S.E_const] at h1 h2
  filter_upwards [h1, h2] with ω e1 e2
  have hMs : 0 < Ms := (hPs0 t ω).trans_le (hPs t ω).2
  constructor
  · calc m / Ms = m * (1 / Ms) := by ring
      _ ≤ Pstar t ω * S.E t (fun ω => 1 / Pstar (t + 1) ω) ω :=
        mul_le_mul (hPs t ω).1 e1 (by positivity) (hPs0 t ω).le
  · calc Pstar t ω * S.E t (fun ω => 1 / Pstar (t + 1) ω) ω ≤ Ms * (1 / m) :=
        mul_le_mul (hPs t ω).2 e2 ((one_div_pos.2 hMs).le.trans e1) hMs.le
      _ = Ms / m := by ring

/-- Cochrane (2023), eq. (9.12), p. 267: `N_s⁻¹` is known at `t` whenever `s ≤ t + 1` (it is
predictable). -/
theorem defl_meas {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) {s t : ℕ}
    (hst : s ≤ t + 1) : StronglyMeasurable[S.𝓕 t] (defl S Pstar s) := by
  have : Measurable[S.𝓕 t] (defl S Pstar s) := Finset.measurable_prod _ fun i hi =>
    ((gam_meas S hPsa i).mono (S.𝓕.mono (by have := Finset.mem_range.1 hi; omega))).measurable.inv
  exact this.stronglyMeasurable

/-- Cochrane (2023), eq. (9.12), p. 267: `0 < N_t⁻¹ ≤ (M*/m)ᵗ` a.e. -/
theorem defl_bounds {m Ms : ℝ} {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hm : 0 < m) (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < defl S Pstar t ω ∧ defl S Pstar t ω ≤ (Ms / m) ^ t := by
  filter_upwards [ae_all_iff.2 (gam_bounds S hPsa hm hPs)] with ω h
  have hMs : 0 < Ms := (hm.trans_le (hPs 0 ω).1).trans_le (hPs 0 ω).2
  have hpos : ∀ i, 0 < gam S Pstar i ω := fun i => (div_pos hm hMs).trans_le (h i).1
  refine ⟨Finset.prod_pos fun i _ => inv_pos.2 (hpos i), ?_⟩
  calc defl S Pstar t ω ≤ ∏ _i ∈ Finset.range t, Ms / m :=
        Finset.prod_le_prod₀ (fun i _ => (inv_pos.2 (hpos i)).le) fun i _ => by
          rw [← inv_div]
          exact inv_anti₀ (div_pos hm hMs) (h i).1
    _ = (Ms / m) ^ t := by rw [Finset.prod_const, Finset.card_range]

/-- Cochrane (2023), eq. (9.12), p. 267: `N_{t+1}⁻¹ γ_t = N_t⁻¹` a.e. -/
theorem defl_succ {m Ms : ℝ} {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hm : 0 < m) (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, defl S Pstar (t + 1) ω * gam S Pstar t ω = defl S Pstar t ω := by
  filter_upwards [gam_bounds S hPsa hm hPs t] with ω h
  have hMs : 0 < Ms := (hm.trans_le (hPs 0 ω).1).trans_le (hPs 0 ω).2
  have hpos : 0 < gam S Pstar t ω := (div_pos hm hMs).trans_le h.1
  simp only [defl, Finset.prod_range_succ]
  field_simp

/-- Cochrane (2023), eq. (9.12), p. 267: the interest-rate target in the form
`E_t(1/P_{t+1}) = γ_t / P_t` (a.e.), given that `P_t/P_{t+1}` is integrable. -/
theorem rate_q {m Ms : ℝ} {Pstar P : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) (hP : ∀ t ω, 0 < P t ω)
    (hPa : StronglyAdapted S.𝓕 P) {t : ℕ}
    (hint : Integrable (fun ω => P t ω * (1 / P (t + 1) ω)) S.μ)
    (hqi : Integrable (fun ω => 1 / P (t + 1) ω) S.μ)
    (hrate : S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) :
    S.E t (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ] fun ω => gam S Pstar t ω * (1 / P t ω) := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hqsi : Integrable (fun ω => 1 / Pstar (t + 1) ω) S.μ :=
    Integrable.of_bound (((hPsm (t + 1)).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le (t + 1))).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 (t + 1) ω))]
        exact one_div_le_one_div_of_le hm (hPs (t + 1) ω).1)
  have e1 : P t / P (t + 1) = P t * fun ω => 1 / P (t + 1) ω := by
    funext ω
    simp [div_eq_mul_inv]
  have e2 : Pstar t / Pstar (t + 1) = Pstar t * fun ω => 1 / Pstar (t + 1) ω := by
    funext ω
    simp [div_eq_mul_inv]
  have h1 : S.E t (P t * fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ]
      P t * S.E t (fun ω => 1 / P (t + 1) ω) :=
    condExp_mul_of_stronglyMeasurable_left (hPa t) hint hqi
  have h2 := S.E_pullOut (hPsa t) (C := Ms) (Eventually.of_forall fun ω => by
    rw [abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2) hqsi
  rw [e1, e2] at hrate
  filter_upwards [h1, h2, hrate] with ω f1 f2 f3
  rw [f1, f2] at f3
  simp only [Pi.mul_apply] at f3
  have hp := (hP t ω).ne'
  change S.E t (fun ω => 1 / P (t + 1) ω) ω = gam S Pstar t ω * (1 / P t ω)
  simp only [gam]
  rw [← f3]
  field_simp

/-! ### The comparison identity -/

/-- Cochrane (2023), eqs. (9.8), (9.12), pp. 266–267 (**the comparison identity**, abstract form):
let `P, P'` be positive adapted price paths whose reciprocals `q = 1/P`, `q' = 1/P'` obey the
interest-rate target `E_t q_{t+1} = γ_t q_t`, let the deflator `N ≥ 0` be predictable with
`N_{t+1} γ_t = N_t`, and let the predictable `Δ` obey `Δ_t = P_t − P'_t + β Δ_{t+1}` (the scaled
debt difference). Then `K_t = βᵗ N_t (q_t − q'_t) Δ_t` is a submartingale whose drift is
`βᵗ N_t (P'_t − P_t)(q_t − q'_t) = βᵗ N_t (P'_t − P_t)²/(P_t P'_t) ≥ 0`, so if `E_0 K_T → 0`, the
forecast drifts sum to `−K_0`. -/
theorem drift_hasSum {β : ℝ} (hβ0 : 0 < β) {P P' Δ N g : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hP' : ∀ t ω, 0 < P' t ω)
    (hPa : StronglyAdapted S.𝓕 P) (hP'a : StronglyAdapted S.𝓕 P')
    (hqi : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hqi' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hr : ∀ t, S.E t (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ] fun ω => g t ω * (1 / P t ω))
    (hr' : ∀ t, S.E t (fun ω => 1 / P' (t + 1) ω) =ᵐ[S.μ] fun ω => g t ω * (1 / P' t ω))
    (hNm : ∀ t, StronglyMeasurable[S.𝓕 t] (N (t + 1))) (hN0 : StronglyMeasurable[S.𝓕 0] (N 0))
    (hNg : ∀ t, ∀ᵐ ω ∂S.μ, N (t + 1) ω * g t ω = N t ω) (hNnn : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ N t ω)
    (hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω)
    (hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1)))
    (hKi : ∀ t, Integrable (fun ω => β ^ t * N t ω * (1 / P t ω - 1 / P' t ω) * Δ t ω) S.μ)
    (hlim : ∀ᵐ ω ∂S.μ, Tendsto (fun T => S.E 0 (fun ω => β ^ T * N T ω *
      (1 / P T ω - 1 / P' T ω) * Δ T ω) ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂S.μ, HasSum (fun t => S.E 0 (fun ω => β ^ t * N t ω *
      ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω))) ω)
      (-(N 0 ω * (1 / P 0 ω - 1 / P' 0 ω) * Δ 0 ω)) := by
  set K : ℕ → Ω → ℝ := fun t ω => β ^ t * N t ω * (1 / P t ω - 1 / P' t ω) * Δ t ω with hK
  set dr : ℕ → Ω → ℝ := fun t ω => β ^ t * N t ω *
    ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω)) with hdr
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hP'm : ∀ t, StronglyMeasurable[S.𝓕 t] (P' t) := fun t => hP'a t
  -- one step: `E_t K_{t+1} = K_t + dr_t`
  have hstep : ∀ t, S.E t (K (t + 1)) =ᵐ[S.μ] K t + dr t := by
    intro t
    set f : Ω → ℝ := fun ω => β ^ (t + 1) * N (t + 1) ω * Δ (t + 1) ω with hf
    set h : Ω → ℝ := fun ω => 1 / P (t + 1) ω - 1 / P' (t + 1) ω with hh
    have hfm : StronglyMeasurable[S.𝓕 t] f := ((hNm t).const_mul _).mul (hΔm t)
    have e : K (t + 1) = f * h := by
      funext ω
      simp only [hK, hf, hh, Pi.mul_apply]
      ring
    have hhi : Integrable h S.μ := (hqi (t + 1)).sub (hqi' (t + 1))
    have hfhi : Integrable (f * h) S.μ := by rw [← e]; exact hKi (t + 1)
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := S.𝓕 t) (μ := S.μ) hfm hfhi hhi
    have h2 := S.E_sub (hqi (t + 1)) (hqi' (t + 1)) t
    filter_upwards [h1, h2, hr t, hr' t, hNg t] with ω e1 e2 e3 e4 e5
    have e1' : S.E t (f * h) ω = f ω * S.E t h ω := e1
    rw [e, e1']
    have e2' : S.E t h ω = S.E t (fun ω => 1 / P (t + 1) ω) ω -
        S.E t (fun ω => 1 / P' (t + 1) ω) ω := e2
    simp only [Pi.add_apply]
    rw [e2', e3, e4]
    simp only [hf, hK, hdr]
    have hd := hΔ t ω
    linear_combination (β ^ (t + 1) * Δ (t + 1) ω * (1 / P t ω - 1 / P' t ω)) * e5 -
      (β ^ t * N t ω * (1 / P t ω - 1 / P' t ω)) * hd
  have hKm : ∀ t, StronglyMeasurable[S.𝓕 t] (K t) := fun t => by
    have hNt : StronglyMeasurable[S.𝓕 t] (N t) := by
      cases t with
      | zero => exact hN0
      | succ t => exact (hNm t).mono (S.𝓕.mono (Nat.le_succ t))
    have hΔt : StronglyMeasurable[S.𝓕 t] (Δ t) := by
      have e : Δ t = fun ω => P t ω - P' t ω + β * Δ (t + 1) ω := funext (hΔ t)
      rw [e]
      exact ((hPm t).sub (hP'm t)).add ((hΔm t).const_mul β)
    exact ((hNt.const_mul _).mul (((hPm t).measurable.const_div 1).stronglyMeasurable.sub
      ((hP'm t).measurable.const_div 1).stronglyMeasurable)).mul hΔt
  have hdri : ∀ t, Integrable (dr t) S.μ := fun t =>
    ((S.integrable_E t (K (t + 1))).sub (hKi t)).congr ((hstep t).mono fun ω h => by
      rw [Pi.sub_apply, h, Pi.add_apply]; ring)
  -- iterating: `E_0 K_T = K_0 + ∑_{t<T} E_0 dr_t`
  have hiter : ∀ T, ∀ᵐ ω ∂S.μ, S.E 0 (K T) ω =
      K 0 ω + ∑ t ∈ Finset.range T, S.E 0 (dr t) ω := by
    intro T
    induction T with
    | zero =>
      refine Eventually.of_forall fun ω => ?_
      simp [S.E_of_stronglyMeasurable (hKm 0) (hKi 0)]
    | succ T ih =>
      have h1 := S.E_tower (Nat.zero_le T) (K (T + 1))
      have h2 := S.E_congr (hstep T) 0
      have h3 := S.E_add (hKi T) (hdri T) 0
      filter_upwards [ih, h1, h2, h3] with ω e0 e1 e2 e3
      rw [← e1, e2, e3, Pi.add_apply, e0, Finset.sum_range_succ]
      ring
  -- the drift is nonnegative
  have hnn : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ S.E 0 (dr t) ω := fun t => by
    have h := S.E_mono (integrable_const 0) (hdri t) (by
      filter_upwards [hNnn t] with ω hN
      have e : (P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω) =
          (P' t ω - P t ω) ^ 2 / (P t ω * P' t ω) := by
        field_simp [(hP t ω).ne', (hP' t ω).ne']
      change (0 : ℝ) ≤ β ^ t * N t ω * ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω))
      rw [e]
      exact mul_nonneg (mul_nonneg (pow_pos hβ0 t).le hN)
        (div_nonneg (sq_nonneg _) (mul_pos (hP t ω) (hP' t ω)).le)) 0
    rw [S.E_const] at h
    exact h
  filter_upwards [ae_all_iff.2 hiter, ae_all_iff.2 hnn, hlim] with ω e1 e2 e3
  refine (hasSum_iff_tendsto_nat_of_nonneg e2 _).2 ?_
  have : Tendsto (fun T => S.E 0 (K T) ω - K 0 ω) atTop (𝓝 (0 - K 0 ω)) :=
    e3.sub tendsto_const_nhds
  rw [zero_sub] at this
  have eK : K 0 ω = N 0 ω * (1 / P 0 ω - 1 / P' 0 ω) * Δ 0 ω := by simp [hK]
  rw [← eK]
  exact this.congr fun T => by rw [e1 T]; ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the comparison identity gives uniqueness**): under the
hypotheses of `drift_hasSum`, if the initial debt difference vanishes (`Δ_0 = 0` a.e.) and
the deflator is positive, the two price paths coincide and `Δ ≡ 0` a.e. -/
theorem drift_unique {β : ℝ} (hβ0 : 0 < β) {P P' Δ N g : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hP' : ∀ t ω, 0 < P' t ω)
    (hPa : StronglyAdapted S.𝓕 P) (hP'a : StronglyAdapted S.𝓕 P')
    (hqi : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hqi' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hr : ∀ t, S.E t (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ] fun ω => g t ω * (1 / P t ω))
    (hr' : ∀ t, S.E t (fun ω => 1 / P' (t + 1) ω) =ᵐ[S.μ] fun ω => g t ω * (1 / P' t ω))
    (hNm : ∀ t, StronglyMeasurable[S.𝓕 t] (N (t + 1))) (hN0 : StronglyMeasurable[S.𝓕 0] (N 0))
    (hNg : ∀ t, ∀ᵐ ω ∂S.μ, N (t + 1) ω * g t ω = N t ω) (hNpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < N t ω)
    (hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω)
    (hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1)))
    (hKi : ∀ t, Integrable (fun ω => β ^ t * N t ω * (1 / P t ω - 1 / P' t ω) * Δ t ω) S.μ)
    (hlim : ∀ᵐ ω ∂S.μ, Tendsto (fun T => S.E 0 (fun ω => β ^ T * N T ω *
      (1 / P T ω - 1 / P' T ω) * Δ T ω) ω) atTop (𝓝 0))
    (hΔ0 : ∀ᵐ ω ∂S.μ, Δ 0 ω = 0) (t : ℕ) :
    P t =ᵐ[S.μ] P' t ∧ ∀ᵐ ω ∂S.μ, Δ t ω = 0 := by
  have hsum := drift_hasSum S hβ0 hP hP' hPa hP'a hqi hqi' hr hr' hNm hN0 hNg
    (fun t => (hNpos t).mono fun ω h => h.le) hΔ hΔm hKi hlim
  set dr : ℕ → Ω → ℝ := fun t ω => β ^ t * N t ω *
    ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω)) with hdr
  have hsq : ∀ t ω, (P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω) =
      (P' t ω - P t ω) ^ 2 / (P t ω * P' t ω) := fun t ω => by
    field_simp [(hP t ω).ne', (hP' t ω).ne']
  have hdrnn : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ dr t ω := fun t => by
    filter_upwards [hNpos t] with ω hN
    simp only [hdr]
    rw [hsq]
    exact mul_nonneg (mul_nonneg (pow_pos hβ0 t).le hN.le)
      (div_nonneg (sq_nonneg _) (mul_pos (hP t ω) (hP' t ω)).le)
  -- integrability of the drift, as in `drift_hasSum`
  have hdri : ∀ t, Integrable (dr t) S.μ := by
    intro t
    set f : Ω → ℝ := fun ω => β ^ (t + 1) * N (t + 1) ω * Δ (t + 1) ω with hf
    set h : Ω → ℝ := fun ω => 1 / P (t + 1) ω - 1 / P' (t + 1) ω with hh
    have hfm : StronglyMeasurable[S.𝓕 t] f := ((hNm t).const_mul _).mul (hΔm t)
    have e : (fun ω => β ^ (t + 1) * N (t + 1) ω * (1 / P (t + 1) ω - 1 / P' (t + 1) ω) *
        Δ (t + 1) ω) = f * h := by
      funext ω
      simp only [hf, hh, Pi.mul_apply]
      ring
    have hhi : Integrable h S.μ := (hqi (t + 1)).sub (hqi' (t + 1))
    have hfhi : Integrable (f * h) S.μ := by rw [← e]; exact hKi (t + 1)
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := S.𝓕 t) (μ := S.μ) hfm hfhi hhi
    have h2 := S.E_sub (hqi (t + 1)) (hqi' (t + 1)) t
    refine ((S.integrable_E t (f * h)).sub (hKi t)).congr ?_
    filter_upwards [h1, h2, hr t, hr' t, hNg t] with ω e1 e2 e3 e4 e5
    have e1' : S.E t (f * h) ω = f ω * S.E t h ω := e1
    rw [Pi.sub_apply, e1']
    have e2' : S.E t h ω = S.E t (fun ω => 1 / P (t + 1) ω) ω -
        S.E t (fun ω => 1 / P' (t + 1) ω) ω := e2
    rw [e2', e3, e4]
    simp only [hf, hdr]
    have hd := hΔ t ω
    linear_combination (β ^ (t + 1) * Δ (t + 1) ω * (1 / P t ω - 1 / P' t ω)) * e5 -
      (β ^ t * N t ω * (1 / P t ω - 1 / P' t ω)) * hd
  -- every forecast drift vanishes
  have hE0 : ∀ s, ∀ᵐ ω ∂S.μ, S.E 0 (dr s) ω = 0 := by
    intro s
    filter_upwards [hsum, hΔ0, ae_all_iff.2 fun s => S.E_mono (integrable_const 0) (hdri s)
      (hdrnn s) 0] with ω e1 e2 e3
    rw [e2, mul_zero, neg_zero] at e1
    have hnn : ∀ i, 0 ≤ S.E 0 (dr i) ω := fun i => by
      have := e3 i
      rw [S.E_const] at this
      exact this
    exact congrFun ((hasSum_zero_iff_of_nonneg hnn).1 e1) s
  have hdr0 : ∀ s, dr s =ᵐ[S.μ] 0 := fun s => by
    have hint : ∫ ω, dr s ω ∂S.μ = 0 := by
      rw [← S.integral_E 0 (dr s)]
      exact integral_eq_zero_of_ae (hE0 s)
    exact (integral_eq_zero_iff_of_nonneg_ae (hdrnn s) (hdri s)).1 hint
  have hPP : ∀ s, P s =ᵐ[S.μ] P' s := fun s => by
    filter_upwards [hdr0 s, hNpos s] with ω e hN
    simp only [hdr, Pi.zero_apply] at e
    rw [hsq] at e
    have hpos : 0 < β ^ s * N s ω := mul_pos (pow_pos hβ0 s) hN
    have h2 : (P' s ω - P s ω) ^ 2 / (P s ω * P' s ω) = 0 := by
      rcases mul_eq_zero.1 e with h | h
      · exact absurd h hpos.ne'
      · exact h
    rcases div_eq_zero_iff.1 h2 with h | h
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      linarith
    · exact absurd h (mul_pos (hP s ω) (hP' s ω)).ne'
  refine ⟨hPP t, ?_⟩
  induction t with
  | zero => exact hΔ0
  | succ t ih =>
    filter_upwards [ih, hPP t] with ω e1 e2
    have := hΔ t ω
    rw [e1, e2, sub_self, zero_add] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hβ0.ne'
    · exact h

/-! ### (2) Two equilibria bounded away from zero, unbounded above -/

/-- Cochrane (2023), §9.3.2, pp. 266–267 (supporting the uniqueness of equilibria bounded away from
zero): for two equilibria of the rule (`RuleEqmGen`, same `s₀` with bounded predetermined present
value `B`, same target `0 < m ≤ P* ≤ M*`) with prices bounded away from zero and the deflator
bounded from date `0` (`N_k⁻¹ ≤ L`), the process `K_t = βᵗ N_t⁻¹ (1/P_t − 1/P'_t) Δ_t`,
`Δ = (b − b')/θ`, is integrable and its date-`0` forecast vanishes in the limit. The proof: `|Δ_T|
≤ D_T + D'_T + 4 M*/(1 − β)` because each debt deviation `D = (b − B)/θ` is bounded below
(`value_lower`), and the transversality condition drives `βᵀ E_0 D_T` to zero. -/
theorem below_limit {β θ K mP mP' m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 B Pstar P P' b b' : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL0 : ∀ k, ∀ᵐ ω ∂S.μ, defl S Pstar k ω ≤ L)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hE' : RuleEqmGen S β θ s0 Pstar P' b') (hmP' : 0 < mP') (hP'mP : ∀ t ω, mP' ≤ P' t ω) :
    (∀ t, Integrable (fun ω => β ^ t * defl S Pstar t ω * (1 / P t ω - 1 / P' t ω) *
      (θ⁻¹ * (b t ω - b' t ω))) S.μ) ∧
    ∀ᵐ ω ∂S.μ, Tendsto (fun T => S.E 0 (fun ω => β ^ T * defl S Pstar T ω *
      (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω))) ω) atTop (𝓝 0) := by
  obtain ⟨hP, hPa, hPi, hbi, -, hflow, hpre, -, htvc⟩ := hE
  obtain ⟨hP', hP'a, hP'i, hbi', -, hflow', hpre', -, htvc'⟩ := hE'
  have h1β : 0 < 1 - β := by linarith
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hP'm : ∀ t, StronglyMeasurable[S.𝓕 t] (P' t) := fun t => hP'a t
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  -- the two debt deviations and their lower bound
  have hdev : ∀ {Q c : ℕ → Ω → ℝ}, (∀ t ω, 0 < Q t ω) → StronglyAdapted S.𝓕 Q →
      (∀ t, Integrable (Q t) S.μ) → (∀ t, Integrable (c t) S.μ) →
      (∀ t ω, c t ω = s0 t ω + θ * (Q t ω - Pstar t ω) + β * c (t + 1) ω) →
      (∀ t, StronglyMeasurable[S.𝓕 t] (c (t + 1))) →
      (∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (c (t + T)) ω) atTop (𝓝 0)) →
      (∀ t, Integrable (fun ω => θ⁻¹ * (c t ω - B t ω)) S.μ) ∧
      (∀ t, ∀ᵐ ω ∂S.μ, -(Ms / (1 - β)) ≤ θ⁻¹ * (c t ω - B t ω)) ∧
      ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E 0 (fun ω => θ⁻¹ * (c T ω - B T ω)) ω) atTop
        (𝓝 0) := by
    intro Q c hQ hQa hQi hci hcflow hcpre hctvc
    set D : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (c t ω - B t ω) with hD_def
    have hD : ∀ t ω, D t ω = Q t ω - Pstar t ω + β * D (t + 1) ω := fun t ω => by
      simp only [hD_def]
      rw [hcflow t ω, hB t ω]
      field_simp
      ring
    have hDpre : ∀ t, StronglyMeasurable[S.𝓕 t] (D (t + 1)) := fun t =>
      ((hcpre t).sub (hBpre t)).const_mul θ⁻¹
    have hDi : ∀ t, Integrable (D t) S.μ := fun t => ((hci t).sub (hBi t)).const_mul θ⁻¹
    have hDtvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (D (t + T)) ω) atTop
        (𝓝 0) := by
      intro t
      filter_upwards [tvc_sub_bdd S hβ0 hβ1 hci hBi hBK hctvc t,
        ae_all_iff.2 fun T => S.E_smul θ⁻¹ (fun ω => c (t + T) ω - B (t + T) ω) t]
        with ω e1 e2
      have := e1.const_mul θ⁻¹
      rw [mul_zero] at this
      refine this.congr fun T => ?_
      have e : D (t + T) = θ⁻¹ • fun ω => c (t + T) ω - B (t + T) ω := by
        funext ω
        simp [hD_def, smul_eq_mul]
      rw [e, e2 T, Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨hDi, value_lower S hβ0 hβ1 (Ms := Ms) hQ hQa hQi hPsa hPs0
      (fun t ω => (hPs t ω).2) hD hDpre hDi hDtvc, ?_⟩
    filter_upwards [hDtvc 0] with ω h
    simpa only [zero_add] using h
  obtain ⟨hDi, hDlow, hDtvc⟩ := hdev hP hPa hPi hbi hflow hpre htvc
  obtain ⟨hDi', hDlow', hDtvc'⟩ := hdev hP' hP'a hP'i hbi' hflow' hpre' htvc'
  set c : ℝ := Ms / (1 - β) with hc
  set Q : ℝ := 1 / mP + 1 / mP' with hQ
  -- the bounded factor
  have hfac : ∀ t, ∀ᵐ ω ∂S.μ, |β ^ t * defl S Pstar t ω * (1 / P t ω - 1 / P' t ω)| ≤
      β ^ t * L * Q := fun t => by
    filter_upwards [hL0 t, defl_bounds S hPsa hm hPs t] with ω e1 e2
    have hq : |1 / P t ω - 1 / P' t ω| ≤ Q := by
      have a1 := one_div_pos.2 (hP t ω)
      have a2 := one_div_pos.2 (hP' t ω)
      have a3 := one_div_le_one_div_of_le hmP (hPmP t ω)
      have a4 := one_div_le_one_div_of_le hmP' (hP'mP t ω)
      rw [abs_le, hQ]
      constructor <;> linarith
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hβ0 t), abs_of_pos e2.1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (pow_pos hβ0 t).le) hq (abs_nonneg _)
      (mul_nonneg (pow_pos hβ0 t).le (e2.1.le.trans e1))
  have hfacm : ∀ t, StronglyMeasurable[S.𝓕 t]
      (fun ω => β ^ t * defl S Pstar t ω * (1 / P t ω - 1 / P' t ω)) := fun t =>
    ((defl_meas S hPsa (Nat.le_succ t)).const_mul _).mul
      (((hPm t).measurable.const_div 1).stronglyMeasurable.sub
        ((hP'm t).measurable.const_div 1).stronglyMeasurable)
  have hΔi : ∀ t, Integrable (fun ω => θ⁻¹ * (b t ω - b' t ω)) S.μ := fun t =>
    ((hbi t).sub (hbi' t)).const_mul θ⁻¹
  have hKi : ∀ t, Integrable (fun ω => β ^ t * defl S Pstar t ω * (1 / P t ω - 1 / P' t ω) *
      (θ⁻¹ * (b t ω - b' t ω))) S.μ := fun t =>
    (hΔi t).bdd_mul ((hfacm t).mono (S.𝓕.le t)).aestronglyMeasurable
      ((hfac t).mono fun ω h => by rwa [Real.norm_eq_abs])
  refine ⟨hKi, ?_⟩
  have hk : ∀ T, ∀ᵐ ω ∂S.μ, |S.E 0 (fun ω => β ^ T * defl S Pstar T ω *
      (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω))) ω| ≤
      L * Q * (β ^ T * S.E 0 (fun ω => θ⁻¹ * (b T ω - B T ω)) ω +
        β ^ T * S.E 0 (fun ω => θ⁻¹ * (b' T ω - B T ω)) ω + 4 * c * β ^ T) := by
    intro T
    set Y : Ω → ℝ := fun ω => θ⁻¹ * (b T ω - B T ω) + θ⁻¹ * (b' T ω - B T ω) + 4 * c
      with hY
    set H : Ω → ℝ := (L * Q * β ^ T) • Y with hH
    have hYi : Integrable Y S.μ := ((hDi T).add (hDi' T)).add (integrable_const _)
    have hHi : Integrable H S.μ := hYi.smul _
    have hKH : ∀ᵐ ω ∂S.μ, |β ^ T * defl S Pstar T ω * (1 / P T ω - 1 / P' T ω) *
        (θ⁻¹ * (b T ω - b' T ω))| ≤ H ω := by
      filter_upwards [hfac T, hDlow T, hDlow' T] with ω e1 e2 e3
      have hc0 : 0 ≤ c := div_nonneg ((hPs0 0 ω).le.trans (hPs 0 ω).2) h1β.le
      have hΔe : θ⁻¹ * (b T ω - b' T ω) =
          θ⁻¹ * (b T ω - B T ω) - θ⁻¹ * (b' T ω - B T ω) := by ring
      have hΔb : |θ⁻¹ * (b T ω - b' T ω)| ≤ Y ω := by
        rw [hΔe]
        simp only [hY]
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      calc |β ^ T * defl S Pstar T ω * (1 / P T ω - 1 / P' T ω)| *
            |θ⁻¹ * (b T ω - b' T ω)| ≤ β ^ T * L * Q * Y ω :=
            mul_le_mul e1 hΔb (abs_nonneg _) ((abs_nonneg _).trans e1)
        _ = H ω := by simp only [hH, Pi.smul_apply, smul_eq_mul]; ring
    have hup := S.E_mono (hKi T) hHi (hKH.mono fun ω h => (le_abs_self _).trans h) 0
    have hlo := S.E_mono (hKi T).neg hHi (hKH.mono fun ω h => (neg_le_abs _).trans h) 0
    have hneg := condExp_neg (m := S.𝓕 0) (μ := S.μ) (fun ω => β ^ T * defl S Pstar T ω *
      (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω)))
    have hsm := S.E_smul (L * Q * β ^ T) Y 0
    have hadd1 := S.E_add ((hDi T).add (hDi' T)) (integrable_const (4 * c)) 0
    have hadd2 := S.E_add (hDi T) (hDi' T) 0
    filter_upwards [hup, hlo, hneg, hsm, hadd1, hadd2] with ω e1 e2 e3 e4 e5 e6
    have eH : S.E 0 H ω = L * Q * (β ^ T * S.E 0 (fun ω => θ⁻¹ * (b T ω - B T ω)) ω +
        β ^ T * S.E 0 (fun ω => θ⁻¹ * (b' T ω - B T ω)) ω + 4 * c * β ^ T) := by
      have e4' : S.E 0 H ω = L * Q * β ^ T * S.E 0 Y ω := by
        rw [hH, e4, Pi.smul_apply, smul_eq_mul]
      have e5' : S.E 0 Y ω = S.E 0 ((fun ω => θ⁻¹ * (b T ω - B T ω)) +
          fun ω => θ⁻¹ * (b' T ω - B T ω)) ω + 4 * c := by
        change S.E 0 (((fun ω => θ⁻¹ * (b T ω - B T ω)) + fun ω => θ⁻¹ * (b' T ω - B T ω)) +
          fun _ => 4 * c) ω = _
        rw [e5, Pi.add_apply, S.E_const]
      have e6' : S.E 0 ((fun ω => θ⁻¹ * (b T ω - B T ω)) +
          fun ω => θ⁻¹ * (b' T ω - B T ω)) ω =
          S.E 0 (fun ω => θ⁻¹ * (b T ω - B T ω)) ω +
            S.E 0 (fun ω => θ⁻¹ * (b' T ω - B T ω)) ω := by rw [e6, Pi.add_apply]
      rw [e4', e5', e6']
      ring
    have e3' : S.E 0 (-fun ω => β ^ T * defl S Pstar T ω * (1 / P T ω - 1 / P' T ω) *
        (θ⁻¹ * (b T ω - b' T ω))) ω = -S.E 0 (fun ω => β ^ T * defl S Pstar T ω *
        (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω))) ω := e3
    rw [e3'] at e2
    rw [eH] at e1 e2
    rw [abs_le]
    constructor <;> linarith
  filter_upwards [ae_all_iff.2 hk, hDtvc, hDtvc'] with ω e1 e2 e3
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have h3 : Tendsto (fun T => L * Q * (β ^ T * S.E 0 (fun ω => θ⁻¹ * (b T ω - B T ω)) ω +
      β ^ T * S.E 0 (fun ω => θ⁻¹ * (b' T ω - B T ω)) ω + 4 * c * β ^ T)) atTop (𝓝 0) := by
    have := ((e2.add e3).add (hg.const_mul (4 * c))).const_mul (L * Q)
    simpa using this
  exact squeeze_zero_norm (fun T => by rw [Real.norm_eq_abs]; exact e1 T) h3

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the comparison identity for equilibria bounded away
from zero**): for two equilibria as in `below_limit`, with any initial debts,
`∑_t E_0[βᵗ N_t⁻¹ (P'_t − P_t)²/(P_t P'_t)] = ((b_0 − b'_0)/θ)(1/P'_0 − 1/P_0)` a.e. (a genuine
`HasSum` of nonnegative terms; the summand is written `(P' − P)(1/P − 1/P')`). Prices may be
unbounded above. -/
theorem compare_identity_below {β θ K mP mP' m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B Pstar P P' b b' : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL0 : ∀ k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar i ω * S.E i (fun ω => 1 / Pstar (i + 1) ω) ω)⁻¹ ≤ L)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hE' : RuleEqmGen S β θ s0 Pstar P' b') (hmP' : 0 < mP') (hP'mP : ∀ t ω, mP' ≤ P' t ω) :
    ∀ᵐ ω ∂S.μ, HasSum (fun t => S.E 0 (fun ω => β ^ t * defl S Pstar t ω *
      ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω))) ω)
      (θ⁻¹ * (b 0 ω - b' 0 ω) * (1 / P' 0 ω - 1 / P 0 ω)) := by
  obtain ⟨hKi, hlim⟩ := below_limit S hβ0 hβ1 hθ hs0m hB hBpre hBK hPsa hm hPs hL0 hE hmP hPmP
    hE' hmP' hP'mP
  obtain ⟨hP, hPa, hPi, -, hrate, hflow, hpre, -, -⟩ := hE
  obtain ⟨hP', hP'a, hP'i, -, hrate', hflow', hpre', -, -⟩ := hE'
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hP'm : ∀ t, StronglyMeasurable[S.𝓕 t] (P' t) := fun t => hP'a t
  have hqi : ∀ {Q : ℕ → Ω → ℝ} {mQ : ℝ}, (∀ t, StronglyMeasurable[S.𝓕 t] (Q t)) → 0 < mQ →
      (∀ t ω, mQ ≤ Q t ω) → ∀ t, Integrable (fun ω => 1 / Q t ω) S.μ := by
    intro Q mQ hQm hmQ hQ t
    exact Integrable.of_bound (((hQm t).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le t)).aestronglyMeasurable (1 / mQ) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hmQ.trans_le (hQ t ω)))]
        exact one_div_le_one_div_of_le hmQ (hQ t ω))
  have hr : ∀ {Q : ℕ → Ω → ℝ} {mQ : ℝ}, (∀ t ω, 0 < Q t ω) → StronglyAdapted S.𝓕 Q →
      (∀ t, StronglyMeasurable[S.𝓕 t] (Q t)) → 0 < mQ → (∀ t ω, mQ ≤ Q t ω) →
      (∀ t, Integrable (Q t) S.μ) →
      (∀ t, S.E t (Q t / Q (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) → ∀ t,
      S.E t (fun ω => 1 / Q (t + 1) ω) =ᵐ[S.μ] fun ω => gam S Pstar t ω * (1 / Q t ω) := by
    intro Q mQ hQ hQa hQm hmQ hQb hQi hQr t
    refine rate_q S hPsa hm hPs hQ hQa ?_ (hqi hQm hmQ hQb (t + 1)) (hQr t)
    exact (hQi t).mul_bdd (((hQm (t + 1)).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le _)).aestronglyMeasurable (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hQ (t + 1) ω))]
        exact one_div_le_one_div_of_le hmQ (hQb (t + 1) ω))
  have hΔ : ∀ t ω, θ⁻¹ * (b t ω - b' t ω) =
      P t ω - P' t ω + β * (θ⁻¹ * (b (t + 1) ω - b' (t + 1) ω)) := fun t ω => by
    rw [hflow t ω, hflow' t ω]
    field_simp
    ring
  have h := drift_hasSum S hβ0 (Δ := fun t ω => θ⁻¹ * (b t ω - b' t ω)) hP hP' hPa hP'a
    (hqi hPm hmP hPmP) (hqi hP'm hmP' hP'mP) (hr hP hPa hPm hmP hPmP hPi hrate)
    (hr hP' hP'a hP'm hmP' hP'mP hP'i hrate') (fun t => defl_meas S hPsa le_rfl)
    (defl_meas S hPsa (Nat.zero_le 1)) (defl_succ S hPsa hm hPs)
    (fun t => (defl_bounds S hPsa hm hPs t).mono fun ω h => h.1.le) hΔ
    (fun t => ((hpre t).sub (hpre' t)).const_mul θ⁻¹) hKi hlim
  filter_upwards [h] with ω e
  have e0 : defl S Pstar 0 ω = 1 := by simp [defl]
  convert e using 1
  rw [e0]
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), two equilibria bounded away from zero
and unbounded above, `b₀ ≠ b̄` allowed — uniqueness holds**): on any measure-theoretic system, two
equilibria of the rule (`RuleEqmGen`, same `s₀` with bounded predetermined present value `B`, same
adapted target `0 < m ≤ P* ≤ M*` whose present value may carry news) with prices bounded away from
zero — but possibly unbounded above — and the same initial debt coincide, provided the deflator is
bounded from date `0`: `∏_{i<k} E_i(P*_i/P*_{i+1})⁻¹ ≤ L`. No equilibrium needs to be bounded above
and initial debt is arbitrary. Proof: the comparison identity (`compare_identity_below`) with
`Δ_0 = 0` makes a sum of nonnegative forecast drifts vanish. -/
theorem fr_unique_below_pair {β θ K mP mP' m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B Pstar P P' b b' : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL0 : ∀ k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar i ω * S.E i (fun ω => 1 / Pstar (i + 1) ω) ω)⁻¹ ≤ L)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hE' : RuleEqmGen S β θ s0 Pstar P' b') (hmP' : 0 < mP') (hP'mP : ∀ t ω, mP' ≤ P' t ω)
    (hb0 : b 0 =ᵐ[S.μ] b' 0) (t : ℕ) : P t =ᵐ[S.μ] P' t ∧ b t =ᵐ[S.μ] b' t := by
  obtain ⟨hKi, hlim⟩ := below_limit S hβ0 hβ1 hθ hs0m hB hBpre hBK hPsa hm hPs hL0 hE hmP hPmP
    hE' hmP' hP'mP
  obtain ⟨hP, hPa, hPi, -, hrate, hflow, hpre, -, -⟩ := hE
  obtain ⟨hP', hP'a, hP'i, -, hrate', hflow', hpre', -, -⟩ := hE'
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hP'm : ∀ t, StronglyMeasurable[S.𝓕 t] (P' t) := fun t => hP'a t
  have hqi : ∀ {Q : ℕ → Ω → ℝ} {mQ : ℝ}, (∀ t, StronglyMeasurable[S.𝓕 t] (Q t)) → 0 < mQ →
      (∀ t ω, mQ ≤ Q t ω) → ∀ t, Integrable (fun ω => 1 / Q t ω) S.μ := by
    intro Q mQ hQm hmQ hQ t
    exact Integrable.of_bound (((hQm t).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le t)).aestronglyMeasurable (1 / mQ) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hmQ.trans_le (hQ t ω)))]
        exact one_div_le_one_div_of_le hmQ (hQ t ω))
  have hr : ∀ {Q : ℕ → Ω → ℝ} {mQ : ℝ}, (∀ t ω, 0 < Q t ω) → StronglyAdapted S.𝓕 Q →
      (∀ t, StronglyMeasurable[S.𝓕 t] (Q t)) → 0 < mQ → (∀ t ω, mQ ≤ Q t ω) →
      (∀ t, Integrable (Q t) S.μ) →
      (∀ t, S.E t (Q t / Q (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) → ∀ t,
      S.E t (fun ω => 1 / Q (t + 1) ω) =ᵐ[S.μ] fun ω => gam S Pstar t ω * (1 / Q t ω) := by
    intro Q mQ hQ hQa hQm hmQ hQb hQi hQr t
    refine rate_q S hPsa hm hPs hQ hQa ?_ (hqi hQm hmQ hQb (t + 1)) (hQr t)
    exact (hQi t).mul_bdd (((hQm (t + 1)).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le _)).aestronglyMeasurable (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hQ (t + 1) ω))]
        exact one_div_le_one_div_of_le hmQ (hQb (t + 1) ω))
  have hΔ : ∀ t ω, θ⁻¹ * (b t ω - b' t ω) =
      P t ω - P' t ω + β * (θ⁻¹ * (b (t + 1) ω - b' (t + 1) ω)) := fun t ω => by
    rw [hflow t ω, hflow' t ω]
    field_simp
    ring
  obtain ⟨h1, h2⟩ := drift_unique S hβ0 (Δ := fun t ω => θ⁻¹ * (b t ω - b' t ω)) hP hP' hPa
    hP'a (hqi hPm hmP hPmP) (hqi hP'm hmP' hP'mP) (hr hP hPa hPm hmP hPmP hPi hrate)
    (hr hP' hP'a hP'm hmP' hP'mP hP'i hrate') (fun t => defl_meas S hPsa le_rfl)
    (defl_meas S hPsa (Nat.zero_le 1)) (defl_succ S hPsa hm hPs)
    (fun t => (defl_bounds S hPsa hm hPs t).mono fun ω h => h.1) hΔ
    (fun t => ((hpre t).sub (hpre' t)).const_mul θ⁻¹) hKi hlim
    (hb0.mono fun ω h => by simp [h]) t
  refine ⟨h1, ?_⟩
  filter_upwards [h2] with ω e
  have := (mul_eq_zero.1 e).resolve_left (inv_ne_zero hθ)
  linarith

/-- Cochrane (2023), eq. (9.12), p. 267: the bounded-deflator hypothesis of
`FiscalRulesTargetClose` (`∏_{i<k} γ_{t+i}⁻¹ ≤ L` from every date `t`) implies its date-`0` case,
which is all `fr_unique_below_pair` needs. -/
theorem hL0_of_hL {L : ℝ} {Pstar : ℕ → Ω → ℝ}
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L) (k : ℕ) :
    ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar i ω * S.E i (fun ω => 1 / Pstar (i + 1) ω) ω)⁻¹ ≤ L := by
  simpa only [zero_add] using hL 0 k

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), the book's rule, `b₀ ≠ b̄` allowed**):
two equilibria of the rule (`RuleEqm`) with the same target `0 < m ≤ P* ≤ M*` (news allowed), prices
bounded away from zero (not necessarily above) and the same initial debt `b₀` — equal to `b̄` or
not — coincide, under the bounded deflator from date `0`. -/
theorem fr_unique_below_rule {β θ bbar mP mP' m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar P P' b b' : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL0 : ∀ k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar i ω * S.E i (fun ω => 1 / Pstar (i + 1) ω) ω)⁻¹ ≤ L)
    (hE : RuleEqm S β θ bbar Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hE' : RuleEqm S β θ bbar Pstar P' b') (hmP' : 0 < mP') (hP'mP : ∀ t ω, mP' ≤ P' t ω)
    (hb0 : b 0 =ᵐ[S.μ] b' 0) (t : ℕ) : P t =ᵐ[S.μ] P' t ∧ b t =ᵐ[S.μ] b' t :=
  fr_unique_below_pair S hβ0 hβ1 hθ (K := |bbar|) (B := fun _ _ => bbar)
    (fun _ => stronglyMeasurable_const) (fun _ _ => by ring) (fun _ => stronglyMeasurable_const)
    (fun _ _ => le_rfl) hPsa hm hPs hL0 ((ruleEqm_iff_gen S).1 hE) hmP hPmP
    ((ruleEqm_iff_gen S).1 hE') hmP' hP'mP hb0 t

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**link**: agreement with `FiscalRulesTargetClose`): with
`b₀ = b̄` the pair theorem, applied to the equilibrium and to the target path `P = P*`, `b ≡ b̄`
(itself bounded away from zero), gives `fr_d_news_below`'s conclusion `P = P*` — from the
date-`0` deflator bound alone. -/
theorem fr_d_news_below_of_pair {β θ bbar mP m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar P b : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (hE : RuleEqm S β θ bbar Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hb0 : ∀ ω, b 0 ω = bbar) (t : ℕ) : P t =ᵐ[S.μ] Pstar t := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsi : ∀ t, Integrable (Pstar t) S.μ := fun t =>
    Integrable.of_bound ((hPsa t).mono (S.𝓕.le t)).aestronglyMeasurable Ms
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2)
  have hT : RuleEqm S β θ bbar Pstar Pstar (fun _ _ => bbar) :=
    (ruleEqm_iff_gen S).2 (target_ruleEqmGen S hβ0 hβ1 (θ := θ) (C := |(1 - β) * bbar|)
      (K := |bbar|) (B := fun _ _ => bbar) (fun _ => stronglyMeasurable_const)
      (fun _ _ => le_rfl) (fun _ _ => by ring) (fun _ => stronglyMeasurable_const)
      (fun _ _ => le_rfl) hPs0 hPsa hPsi)
  exact (fr_unique_below_rule S hβ0 hβ1 hθ hPsa hm hPs (hL0_of_hL S hL) hE hmP hPmP hT hm
    (fun t ω => (hPs t ω).1) (Eventually.of_forall hb0) t).1

/-! ### (1) Existence: the exact condition -/

/-- Cochrane (2023), eqs. (9.8), (9.9), p. 266: the scaled debt deviation `D = (b − b̄)/θ`
generated forward from `D_0 = d₀` by the flow `D_{t+1} = (D_t − (P_t − P*_t))/β`, path by path. -/
noncomputable def fwdDebt (β d0 : ℝ) (Pstar P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => d0
  | t + 1 => fun ω => (fwdDebt β d0 Pstar P t ω - (P t ω - Pstar t ω)) / β

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (9.8), p. 266: the forward debt obeys the flow
`D_t = P_t − P*_t + β D_{t+1}` on every path. -/
theorem fwdDebt_flow {β : ℝ} (hβ0 : 0 < β) (d0 : ℝ) (Pstar P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    fwdDebt β d0 Pstar P t ω = P t ω - Pstar t ω + β * fwdDebt β d0 Pstar P (t + 1) ω := by
  simp only [fwdDebt]
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (9.9), p. 266: telescoping the flow,
`βᵀ D_T = d₀ − ∑_{s<T} βˢ (P_s − P*_s)` on every path. -/
theorem fwdDebt_tele {β : ℝ} (hβ0 : 0 < β) (d0 : ℝ) (Pstar P : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) :
    β ^ T * fwdDebt β d0 Pstar P T ω =
      d0 - ∑ s ∈ Finset.range T, β ^ s * (P s ω - Pstar s ω) := by
  induction T with
  | zero => simp [fwdDebt]
  | succ T ih =>
    rw [Finset.sum_range_succ, pow_succ, ← sub_sub, ← ih]
    simp only [fwdDebt]
    field_simp

/-- Cochrane (2023), eq. (9.8), p. 266: the forward debt is adapted and predetermined
(`D_{t+1}` is known at `t`). -/
theorem fwdDebt_meas {β d0 : ℝ} {Pstar P : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hPa : StronglyAdapted S.𝓕 P) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (fwdDebt β d0 Pstar P t) ∧
      StronglyMeasurable[S.𝓕 t] (fwdDebt β d0 Pstar P (t + 1)) := by
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hstep : ∀ t, StronglyMeasurable[S.𝓕 t] (fwdDebt β d0 Pstar P t) →
      StronglyMeasurable[S.𝓕 t] (fwdDebt β d0 Pstar P (t + 1)) := fun t h =>
    ((h.sub ((hPm t).sub (hPsm t))).measurable.div_const β).stronglyMeasurable
  have hall : ∀ t, StronglyMeasurable[S.𝓕 t] (fwdDebt β d0 Pstar P t) := by
    intro t
    induction t with
    | zero => exact stronglyMeasurable_const
    | succ t ih => exact (hstep t ih).mono (S.𝓕.mono (Nat.le_succ t))
  exact ⟨hall t, hstep t (hall t)⟩

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (9.9), p. 266: if the realised discounted price deviations sum to `d₀`
on a path and `|P − P*| ≤ C` there, the forward debt is bounded by `C/(1 − β)` on that path. -/
theorem fwdDebt_bdd_of_hasSum {β C d0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar P : ℕ → Ω → ℝ}
    {ω : Ω} (hC : ∀ s, |P s ω - Pstar s ω| ≤ C)
    (hs : HasSum (fun s => β ^ s * (P s ω - Pstar s ω)) d0) (T : ℕ) :
    |fwdDebt β d0 Pstar P T ω| ≤ C / (1 - β) := by
  have hβT : 0 < β ^ T := pow_pos hβ0 T
  have e : d0 = ∑ s ∈ Finset.range T, β ^ s * (P s ω - Pstar s ω) +
      ∑' s, β ^ (s + T) * (P (s + T) ω - Pstar (s + T) ω) := by
    rw [← hs.tsum_eq]
    exact (hs.summable.sum_add_tsum_nat_add T).symm
  have h1 : β ^ T * fwdDebt β d0 Pstar P T ω =
      ∑' s, β ^ (s + T) * (P (s + T) ω - Pstar (s + T) ω) := by
    rw [fwdDebt_tele hβ0 d0 Pstar P T ω]
    linarith
  have hb : ∀ s, ‖β ^ (s + T) * (P (s + T) ω - Pstar (s + T) ω)‖ ≤ β ^ T * (C * β ^ s) :=
      fun s => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 _), pow_add]
    calc β ^ s * β ^ T * |P (s + T) ω - Pstar (s + T) ω| ≤ β ^ s * β ^ T * C :=
          mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ = β ^ T * (C * β ^ s) := by ring
  have hsum := ((hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left C).mul_left (β ^ T)
  have h2 := tsum_of_norm_bounded hsum hb
  rw [← h1, Real.norm_eq_abs, abs_mul, abs_of_pos hβT] at h2
  have e : β ^ T * (C * (1 - β)⁻¹) = β ^ T * (C / (1 - β)) := by rw [div_eq_mul_inv]
  rw [e] at h2
  exact le_of_mul_le_mul_left h2 hβT

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (9.9), p. 266: conversely, if the forward debt is bounded on a path and
`|P − P*| ≤ C` there, the realised discounted price deviations sum to `d₀` on that path. -/
theorem hasSum_of_fwdDebt_bdd {β C K d0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar P : ℕ → Ω → ℝ}
    {ω : Ω} (hC : ∀ s, |P s ω - Pstar s ω| ≤ C) (hK : ∀ T, |fwdDebt β d0 Pstar P T ω| ≤ K) :
    HasSum (fun s => β ^ s * (P s ω - Pstar s ω)) d0 := by
  have hsum : Summable (fun s => β ^ s * (P s ω - Pstar s ω)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C)
      fun s => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 s)]
        exact mul_le_mul_of_nonneg_left (hC s) (pow_pos hβ0 s).le
  have hrem : Tendsto (fun T => β ^ T * fwdDebt β d0 Pstar P T ω) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun T => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const K)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (hK T) (pow_pos hβ0 T).le
  have hpart : Tendsto (fun T => ∑ s ∈ Finset.range T, β ^ s * (P s ω - Pstar s ω)) atTop
      (𝓝 d0) := by
    have := (tendsto_const_nhds (x := d0)).sub hrem
    rw [sub_zero] at this
    exact this.congr fun T => by rw [fwdDebt_tele hβ0]; ring
  have he := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpart
  rw [← he]
  exact hsum.hasSum

/-- Cochrane (2023), eq. (9.9), p. 266: `hasSum_E_value` with the present value bounded only a.e.
— if `B_t = s_t + β B_{t+1}` on every path, `B` predetermined and a.e. bounded, `s` adapted and
bounded, then `∑ⱼ βʲ E_t s_{t+j} = B_t` a.e. -/
theorem hasSum_E_value_ae {β C K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s B : ℕ → Ω → ℝ}
    (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t)) (hsC : ∀ t ω, |s t ω| ≤ C)
    (hB : ∀ t ω, B t ω = s t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t, ∀ᵐ ω ∂S.μ, |B t ω| ≤ K)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t (s (t + j)) ω) (B t ω) := by
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hsm t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      ((hBK t).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hsi : ∀ t, Integrable (s t) S.μ := fun t =>
    Integrable.of_bound ((hsm t).mono (S.𝓕.le t)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hsC t ω)
  have hE : ∀ j, ∀ᵐ ω ∂S.μ, |S.E t (s (t + j)) ω| ≤ C := fun j =>
    S.abs_E_le (Eventually.of_forall fun ω => hsC (t + j) ω) t
  have hEK : ∀ k, ∀ᵐ ω ∂S.μ, |S.E t (B (t + k)) ω| ≤ K := fun k => S.abs_E_le (hBK (t + k)) t
  filter_upwards [ae_all_iff.2 (value_partial S hB hBm hBi hsi t), ae_all_iff.2 hE,
    ae_all_iff.2 hEK] with ω h1 h2 h3
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have hrem : Tendsto (fun k => β ^ k * S.E t (B (t + k)) ω) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const K)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
    exact mul_le_mul_of_nonneg_left (h3 k) (pow_pos hβ0 k).le
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k, β ^ j * S.E t (s (t + j)) ω) atTop
      (𝓝 (B t ω)) := by
    have := (tendsto_const_nhds (x := B t ω)).sub hrem
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]
  have hsum : Summable (fun j => β ^ j * S.E t (s (t + j)) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 j)]
      exact mul_le_mul_of_nonneg_left (h2 j) (pow_pos hβ0 j).le
  have he := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpart
  rw [← he]
  exact hsum.hasSum

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**existence, the construction**): let `P` be positive,
adapted, bounded above by `M`, satisfy the interest-rate target (9.12) for a target
`0 < m ≤ P* ≤ M*`, and let the forward debt generated from `d₀` (`fwdDebt`) be a.e. bounded. Then
`P` with real debt `b = b̄ + θ D` is an equilibrium of the rule (`RuleEqm`) with `b₀ = b̄ + θ d₀`:
the valuation (9.9) and the transversality condition follow from boundedness. -/
theorem eqm_of_bdd {β θ bbar d0 m Ms M K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Pstar P : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P) (hPM : ∀ t ω, P t ω ≤ M)
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1)))
    (hDK : ∀ t, ∀ᵐ ω ∂S.μ, |fwdDebt β d0 Pstar P t ω| ≤ K) :
    RuleEqm S β θ bbar Pstar P (fun t ω => bbar + θ * fwdDebt β d0 Pstar P t ω) := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hDm := fwdDebt_meas S (β := β) (d0 := d0) hPsa hPa
  set b : ℕ → Ω → ℝ := fun t ω => bbar + θ * fwdDebt β d0 Pstar P t ω with hb
  have hbm : ∀ t, StronglyMeasurable[S.𝓕 t] (b t) := fun t =>
    stronglyMeasurable_const.add ((hDm t).1.const_mul θ)
  have hbpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1)) := fun t =>
    stronglyMeasurable_const.add ((hDm t).2.const_mul θ)
  have hbK : ∀ t, ∀ᵐ ω ∂S.μ, |b t ω| ≤ |bbar| + |θ| * K := fun t => by
    filter_upwards [hDK t] with ω h
    simp only [hb]
    calc |bbar + θ * fwdDebt β d0 Pstar P t ω| ≤ |bbar| + |θ * fwdDebt β d0 Pstar P t ω| :=
          abs_add_le _ _
      _ ≤ |bbar| + |θ| * K := by
          rw [abs_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h (abs_nonneg θ))
  have hbi : ∀ t, Integrable (b t) S.μ := fun t =>
    Integrable.of_bound ((hbm t).mono (S.𝓕.le t)).aestronglyMeasurable _
      ((hbK t).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω :=
    fun t ω => by
      simp only [hb]
      rw [fwdDebt_flow hβ0 d0 Pstar P t ω]
      ring
  have hsm : ∀ t, StronglyMeasurable[S.𝓕 t]
      (fun ω => (1 - β) * bbar + θ * (P t ω - Pstar t ω)) := fun t =>
    stronglyMeasurable_const.add (((hPm t).sub (hPsm t)).const_mul θ)
  have hsC : ∀ t ω, |(1 - β) * bbar + θ * (P t ω - Pstar t ω)| ≤
      |(1 - β) * bbar| + |θ| * (M + Ms) := fun t ω => by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
    rw [abs_le]
    have := hP t ω
    have := hPM t ω
    have := (hPs t ω).2
    have := hPs0 t ω
    constructor <;> linarith
  refine ⟨hP, hPa, fun t => Integrable.of_bound ((hPm t).mono (S.𝓕.le t)).aestronglyMeasurable M
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_pos (hP t ω)]; exact hPM t ω),
    hbi, hrate, hflow, hbpre, fun t => hasSum_E_value_ae S hβ0 hβ1
      (s := fun t ω => (1 - β) * bbar + θ * (P t ω - Pstar t ω)) hsm hsC hflow hbpre hbK t,
    fun t => ?_⟩
  filter_upwards [ae_all_iff.2 fun k => S.abs_E_le (hbK (t + k)) t] with ω h
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (|bbar| + |θ| * K)
  rw [zero_mul] at hg
  refine squeeze_zero_norm (fun k => ?_) hg
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
  exact mul_le_mul_of_nonneg_left (h k) (pow_pos hβ0 k).le

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) with `b₀ ≠ b̄`: the exact existence
condition, pathwise form**): on any measure-theoretic system — news may arrive at every date — and
for any adapted target `0 < m ≤ P* ≤ M*`, an equilibrium of the rule (`RuleEqm`) with prices
bounded above and initial debt `b₀ = b̄ + θ d₀` exists **iff** there is a positive adapted price
path `P ≤ M` with integrable `1/P` that meets the interest-rate target (9.12) and whose realised
discounted deviations from the target sum to `d₀` on almost every path:
`∑ₛ βˢ (P_s − P*_s) = d₀` a.e. The news in the target's present value must be matched path by
path; the valuation (9.9) in expectation and the transversality condition are then automatic. -/
theorem exists_iff_pathwise {β θ bbar d0 m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) :
    (∃ (P b : ℕ → Ω → ℝ) (M : ℝ), RuleEqm S β θ bbar Pstar P b ∧ (∀ t ω, P t ω ≤ M) ∧
      (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∧ ∀ ω, b 0 ω = bbar + θ * d0) ↔
    ∃ (P : ℕ → Ω → ℝ) (M : ℝ), (∀ t ω, 0 < P t ω) ∧ StronglyAdapted S.𝓕 P ∧
      (∀ t ω, P t ω ≤ M) ∧ (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∧
      (∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) ∧
      ∀ᵐ ω ∂S.μ, HasSum (fun s => β ^ s * (P s ω - Pstar s ω)) d0 := by
  have h1β : 0 < 1 - β := by linarith
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hC : ∀ {P : ℕ → Ω → ℝ} {M : ℝ}, (∀ t ω, 0 < P t ω) → (∀ t ω, P t ω ≤ M) →
      ∀ t ω, |P t ω - Pstar t ω| ≤ M + Ms := fun hP hPM t ω => by
    rw [abs_le]
    have := hP t ω
    have := hPM t ω
    have := (hPs t ω).2
    have := hPs0 t ω
    constructor <;> linarith
  constructor
  · rintro ⟨P, b, M, hE, hPM, hq, hb0⟩
    obtain ⟨hP, hPa, -, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
    have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
    -- the scaled debt deviation is the forward debt, path by path
    have hDe : ∀ t ω, θ⁻¹ * (b t ω - bbar) = fwdDebt β d0 Pstar P t ω := by
      intro t
      induction t with
      | zero => intro ω; simp [fwdDebt, hb0 ω, hθ]
      | succ t ih =>
        intro ω
        simp only [fwdDebt]
        rw [← ih ω, hflow t ω]
        field_simp
        ring
    -- it is bounded
    have hDi : ∀ t, Integrable (fun ω => θ⁻¹ * (b t ω - bbar)) S.μ := fun t =>
      ((hbi t).sub (integrable_const bbar)).const_mul θ⁻¹
    have hDtvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t
        (fun ω => θ⁻¹ * (b (t + T) ω - bbar)) ω) atTop (𝓝 0) := by
      intro t
      filter_upwards [tvc_sub_bdd S hβ0 hβ1 (K := |bbar|) (g := fun _ _ => bbar) hbi
        (fun _ => integrable_const bbar) (fun _ _ => le_rfl) htvc t,
        ae_all_iff.2 fun T => S.E_smul θ⁻¹ (fun ω => b (t + T) ω - bbar) t] with ω e1 e2
      have := e1.const_mul θ⁻¹
      rw [mul_zero] at this
      refine this.congr fun T => ?_
      have e : (fun ω => θ⁻¹ * (b (t + T) ω - bbar)) = θ⁻¹ • fun ω => b (t + T) ω - bbar := by
        funext ω
        simp [smul_eq_mul]
      rw [e, e2 T, Pi.smul_apply, smul_eq_mul]
      ring
    have hDflow : ∀ t ω, θ⁻¹ * (b t ω - bbar) =
        (P t ω - Pstar t ω) + β * (θ⁻¹ * (b (t + 1) ω - bbar)) := fun t ω => by
      rw [hflow t ω]
      field_simp
      ring
    have hDB := debt_bdd S hβ0 hβ1 (C := M + Ms) (s := fun t ω => P t ω - Pstar t ω)
      (b := fun t ω => θ⁻¹ * (b t ω - bbar)) (fun t => (hPm t).sub (hPsm t))
      (hC hP hPM) hDflow (fun t => ((hpre t).sub stronglyMeasurable_const).const_mul θ⁻¹)
      hDi hDtvc
    refine ⟨P, M, hP, hPa, hPM, hq, hrate, ?_⟩
    filter_upwards [ae_all_iff.2 hDB] with ω h
    exact hasSum_of_fwdDebt_bdd hβ0 hβ1 (hC hP hPM · ω) fun T => by rw [← hDe]; exact h T
  · rintro ⟨P, M, hP, hPa, hPM, hq, hrate, hsum⟩
    have hDK : ∀ t, ∀ᵐ ω ∂S.μ, |fwdDebt β d0 Pstar P t ω| ≤ (M + Ms) / (1 - β) := fun t => by
      filter_upwards [hsum] with ω h
      exact fwdDebt_bdd_of_hasSum hβ0 hβ1 (hC hP hPM · ω) h t
    exact ⟨P, fun t ω => bbar + θ * fwdDebt β d0 Pstar P t ω, M,
      eqm_of_bdd S hβ0 hβ1 hPsa hm hPs hP hPa hPM hrate hDK, hPM, hq,
      fun ω => by simp [fwdDebt]⟩

/-- Cochrane (2023), eq. (9.9), p. 266 (**the forward valuation recursion**): for a positive
adapted `P ≤ M` and target `0 < m ≤ P* ≤ M*`, the realised discounted deviations sum to `d₀` on
almost every path iff the forward solution `D = forwardSol β (P − P*)` — the unique bounded
solution of the contraction `D_t = (P_t − P*_t) + β E_t D_{t+1}` — is predictable
(`D_{t+1} = E_t D_{t+1}` a.e.) and starts at `D_0 = d₀`. -/
theorem forward_iff_pathwise {β d0 m Ms M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Pstar P : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P) (hPM : ∀ t ω, P t ω ≤ M) :
    (∀ᵐ ω ∂S.μ, HasSum (fun s => β ^ s * (P s ω - Pstar s ω)) d0) ↔
      (∀ t, S.forwardSol β (fun t ω => P t ω - Pstar t ω) (t + 1) =ᵐ[S.μ]
        S.E t (S.forwardSol β (fun t ω => P t ω - Pstar t ω) (t + 1))) ∧
      S.forwardSol β (fun t ω => P t ω - Pstar t ω) 0 =ᵐ[S.μ] fun _ => d0 := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hβa : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  set u : ℕ → Ω → ℝ := fun t ω => P t ω - Pstar t ω with hu
  have hC : ∀ t ω, |u t ω| ≤ M + Ms := fun t ω => by
    rw [abs_le]
    have := hP t ω
    have := hPM t ω
    have := (hPs t ω).2
    have := hPs0 t ω
    constructor <;> linarith
  have hua : StronglyAdapted S.𝓕 u := fun t => (hPm t).sub (hPsm t)
  have hub : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M + Ms := fun t => Eventually.of_forall (hC t)
  have hFsol := S.forwardSol_solves hβa hua hub
  have hFbdd := S.forwardSol_bdd hβa hub
  have hFm : ∀ t, AEStronglyMeasurable (S.forwardSol β u t) S.μ := fun t =>
    ((S.forwardSol_adapted β u t).mono (S.𝓕.le t)).aestronglyMeasurable
  set D : ℕ → Ω → ℝ := fwdDebt β d0 Pstar P with hD
  have hDm := fwdDebt_meas S (β := β) (d0 := d0) hPsa hPa
  constructor
  · intro hsum
    have hDK : ∀ t, ∀ᵐ ω ∂S.μ, |D t ω| ≤ (M + Ms) / (1 - β) := fun t => by
      filter_upwards [hsum] with ω h
      exact fwdDebt_bdd_of_hasSum hβ0 hβ1 (hC · ω) h t
    have hDi : ∀ t, Integrable (D t) S.μ := fun t =>
      Integrable.of_bound (((hDm t).1).mono (S.𝓕.le t)).aestronglyMeasurable _
        ((hDK t).mono fun ω h => by rwa [Real.norm_eq_abs])
    have hDE : ∀ t, S.E t (D (t + 1)) = D (t + 1) := fun t =>
      S.E_of_stronglyMeasurable (hDm t).2 (hDi (t + 1))
    have hDsol : S.Solves β u D := fun t => Eventually.of_forall fun ω => by
      rw [hDE t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD, fwdDebt_flow hβ0 d0 Pstar P t ω]
      ring
    have heq := S.forward_unique hβa hDsol hFsol
      (fun t => ((hDm t).1.mono (S.𝓕.le t)).aestronglyMeasurable) hFm
      ⟨_, hDK⟩ hFbdd
    refine ⟨fun t => ?_, ?_⟩
    · have h1 := S.E_congr (heq (t + 1)) t
      rw [hDE t] at h1
      exact (heq (t + 1)).symm.trans h1
    · filter_upwards [heq 0] with ω h
      rw [← h]
      simp [hD, fwdDebt]
  · rintro ⟨hpred, h0⟩
    obtain ⟨MF, hMF⟩ := hFbdd
    have heq : ∀ t, D t =ᵐ[S.μ] S.forwardSol β u t := by
      intro t
      induction t with
      | zero =>
        filter_upwards [h0] with ω h
        rw [h]
        simp [hD, fwdDebt]
      | succ t ih =>
        filter_upwards [ih, hFsol t, hpred t] with ω e1 e2 e3
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e2
        rw [← e3] at e2
        change (D t ω - (P t ω - Pstar t ω)) / β = _
        rw [e1, e2]
        field_simp
        simp [hu]
    filter_upwards [ae_all_iff.2 heq, ae_all_iff.2 hMF] with ω e1 e2
    exact hasSum_of_fwdDebt_bdd hβ0 hβ1 (hC · ω) fun T => by
      change |D T ω| ≤ MF
      rw [e1 T]
      exact e2 T

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) with `b₀ ≠ b̄`: the exact existence
condition, as solvability of the forward valuation recursion**): an equilibrium of the rule with
prices bounded above and `b₀ = b̄ + θ d₀` exists iff some positive adapted `P ≤ M` with integrable
`1/P` meets the interest-rate target (9.12) and its forward valuation — the unique bounded
solution `D = forwardSol β (P − P*)` of the contraction `D_t = (P_t − P*_t) + β E_t D_{t+1}` — is a
fixed point of predictability (`D_{t+1} = E_t D_{t+1}` a.e.) with `D_0 = d₀`. -/
theorem exists_iff_forward {β θ bbar d0 m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) :
    (∃ (P b : ℕ → Ω → ℝ) (M : ℝ), RuleEqm S β θ bbar Pstar P b ∧ (∀ t ω, P t ω ≤ M) ∧
      (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∧ ∀ ω, b 0 ω = bbar + θ * d0) ↔
    ∃ (P : ℕ → Ω → ℝ) (M : ℝ), (∀ t ω, 0 < P t ω) ∧ StronglyAdapted S.𝓕 P ∧
      (∀ t ω, P t ω ≤ M) ∧ (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∧
      (∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) ∧
      (∀ t, S.forwardSol β (fun t ω => P t ω - Pstar t ω) (t + 1) =ᵐ[S.μ]
        S.E t (S.forwardSol β (fun t ω => P t ω - Pstar t ω) (t + 1))) ∧
      S.forwardSol β (fun t ω => P t ω - Pstar t ω) 0 =ᵐ[S.μ] fun _ => d0 := by
  rw [exists_iff_pathwise S hβ0 hβ1 hθ hPsa hm hPs]
  constructor
  · rintro ⟨P, M, hP, hPa, hPM, hq, hr, h⟩
    exact ⟨P, M, hP, hPa, hPM, hq, hr,
      (forward_iff_pathwise S hβ0 hβ1 hPsa hm hPs hP hPa hPM).1 h⟩
  · rintro ⟨P, M, hP, hPa, hPM, hq, hr, h1, h2⟩
    exact ⟨P, M, hP, hPa, hPM, hq, hr,
      (forward_iff_pathwise S hβ0 hβ1 hPsa hm hPs hP hPa hPM).2 ⟨h1, h2⟩⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**a necessary condition for existence**): if an
equilibrium with prices bounded above and `b₀ = b̄ + θ d₀` exists, then on almost every path the
realised present value of the target plus `d₀` is positive:
`d₀ + ∑ₛ βˢ P*_s(ω) ≥ P_0(ω) > 0`. (`FiscalRulesTargetClose.NoExist.oneShot_no_eqm`: not
sufficient, even when bounded away from zero.) -/
theorem exists_imp_pos {β θ bbar d0 m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hex : ∃ (P b : ℕ → Ω → ℝ) (M : ℝ), RuleEqm S β θ bbar Pstar P b ∧ (∀ t ω, P t ω ≤ M) ∧
      (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∧ ∀ ω, b 0 ω = bbar + θ * d0) :
    ∀ᵐ ω ∂S.μ, 0 < d0 + ∑' s, β ^ s * Pstar s ω := by
  obtain ⟨P, M, hP, -, -, -, -, hsum⟩ := (exists_iff_pathwise S hβ0 hβ1 hθ hPsa hm hPs).1 hex
  filter_upwards [hsum] with ω h
  have hA : HasSum (fun s => β ^ s * Pstar s ω) (∑' s, β ^ s * Pstar s ω) := by
    refine (Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right Ms)
      fun s => ?_).hasSum
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 s),
      abs_of_pos (hm.trans_le (hPs s ω).1)]
    exact mul_le_mul_of_nonneg_left (hPs s ω).2 (pow_pos hβ0 s).le
  have hV : HasSum (fun s => β ^ s * P s ω) (d0 + ∑' s, β ^ s * Pstar s ω) :=
    (h.add hA).congr_fun fun s => by ring
  have h1 := sum_le_hasSum (Finset.range 1) (fun s _ => (mul_pos (pow_pos hβ0 s) (hP s ω)).le) hV
  simp only [Finset.sum_range_one, pow_zero, one_mul] at h1
  exact (hP 0 ω).trans_le h1

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the one-shot condition recovered from the general
one**): on the one-shot system (`oneShot`: no information at date `0`, everything known from date
`1`) with target `P*_0 = p₀`, `P*_t = x` for `t ≥ 1` (`0 < m ≤ x ≤ M*`), an equilibrium with prices
bounded above and `b₀ = b̄ + θ d₀` exists iff some number `d` (scaled date-1 debt) has
`x + (1 − β) d > 0` a.e., `p₀ + d₀ − β d > 0`, `1/(x + (1 − β) d)` integrable and
`(p₀ + d₀ − β d) E[1/(x + (1 − β) d)] = p₀ E[1/x]`. Sufficiency is proved through
`exists_iff_pathwise` (the price path `p₀ + d₀ − β d`, then `x + (1 − β) d`, has realised
discounted deviations `d₀ − β d + β d = d₀`); necessity is `oneShot_eqm_form`. Positivity is only
needed a.e., sharpening `oneShot_eqm_exists`. -/
theorem oneShot_exists_iff (Pm : ProbabilityMeasure Ω) {β θ bbar d0 p0 m Ms : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) {x : Ω → ℝ} (hx : Measurable x) (hm : 0 < m)
    (hxb : ∀ ω, m ≤ x ω ∧ x ω ≤ Ms) (hp0 : 0 < p0) :
    (∃ (P b : ℕ → Ω → ℝ) (M : ℝ), RuleEqm (oneShot Pm) β θ bbar (osTarget p0 x) P b ∧
      (∀ t ω, P t ω ≤ M) ∧ (∀ t, Integrable (fun ω => 1 / P t ω) (oneShot Pm).μ) ∧
      ∀ ω, b 0 ω = bbar + θ * d0) ↔
    ∃ d : ℝ, (∀ᵐ ω ∂(oneShot Pm).μ, 0 < x ω + (1 - β) * d) ∧ 0 < p0 + d0 - β * d ∧
      Integrable (fun ω => 1 / (x ω + (1 - β) * d)) (oneShot Pm).μ ∧
      (p0 + d0 - β * d) * ∫ ω, 1 / (x ω + (1 - β) * d) ∂(oneShot Pm).μ =
        p0 * ∫ ω, 1 / x ω ∂(oneShot Pm).μ := by
  set S := oneShot Pm with hS
  have h1β : 0 < 1 - β := by linarith
  have hx0 : ∀ ω, 0 < x ω := fun ω => hm.trans_le (hxb ω).1
  have hF : ∀ t, S.𝓕 (t + 1) = ‹MeasurableSpace Ω› := fun t => by
    simp [hS, oneShot, oneShotFiltration]
  constructor
  · rintro ⟨P, b, M, hE, hPM, hq, hb0⟩
    obtain ⟨d, hpos, hP0, hPt, heq⟩ := oneShot_eqm_form Pm hβ0 hβ1 hθ hx hm hxb hp0 hE hPM hq hb0
    obtain ⟨ω, -⟩ := hpos.exists
    refine ⟨d, hpos, (hP0 ω) ▸ hE.1 0 ω, (hq 1).congr ?_, heq⟩
    filter_upwards [hPt 0] with ω h
    rw [h]
  · rintro ⟨d, hpos, hP0, hint, heq⟩
    set y : Ω → ℝ := fun ω => if 0 < x ω + (1 - β) * d then x ω + (1 - β) * d else 1 with hy
    have hym : Measurable y :=
      Measurable.ite (measurableSet_lt measurable_const (hx.add_const _)) (hx.add_const _)
        measurable_const
    have hy0 : ∀ ω, 0 < y ω := fun ω => by
      simp only [hy]
      split_ifs with h
      · exact h
      · exact one_pos
    have hyae : y =ᵐ[S.μ] fun ω => x ω + (1 - β) * d := by
      filter_upwards [hpos] with ω h
      simp [hy, h]
    set P : ℕ → Ω → ℝ := fun t ω => if t = 0 then p0 + d0 - β * d else y ω with hPdef
    have hPsa : StronglyAdapted S.𝓕 (osTarget p0 x) := fun t => by
      cases t with
      | zero => exact stronglyMeasurable_const
      | succ t =>
        change StronglyMeasurable[S.𝓕 (t + 1)] x
        rw [hF t]
        exact hx.stronglyMeasurable
    have hPsb : ∀ t ω, min p0 m ≤ osTarget p0 x t ω ∧ osTarget p0 x t ω ≤ max p0 Ms :=
      fun t ω => by
        cases t with
        | zero => exact ⟨min_le_left _ _, le_max_left _ _⟩
        | succ t => exact ⟨(min_le_right _ _).trans (hxb ω).1, (hxb ω).2.trans (le_max_right _ _)⟩
    refine (exists_iff_pathwise S hβ0 hβ1 hθ (d0 := d0) (bbar := bbar) hPsa
      (lt_min hp0 hm) hPsb).2 ⟨P, max (p0 + d0 - β * d) (max (Ms + |(1 - β) * d|) 1),
      fun t ω => ?_, fun t => ?_, fun t ω => ?_, fun t => ?_, fun t => ?_, ?_⟩
    · simp only [hPdef]
      split_ifs
      · exact hP0
      · exact hy0 ω
    · cases t with
      | zero =>
        have e : P 0 = fun _ => p0 + d0 - β * d := by funext ω; simp [hPdef]
        rw [e]
        exact stronglyMeasurable_const
      | succ t =>
        have e : P (t + 1) = y := by funext ω; simp [hPdef]
        rw [e, hF t]
        exact hym.stronglyMeasurable
    · cases t with
      | zero => simp [hPdef]
      | succ t =>
        simp only [hPdef, Nat.add_one_ne_zero, ↓reduceIte, hy]
        refine le_trans ?_ (le_max_right _ _)
        split_ifs
        · refine le_trans ?_ (le_max_left _ _)
          have := (hxb ω).2
          have := le_abs_self ((1 - β) * d)
          linarith
        · exact le_max_right _ _
    · cases t with
      | zero =>
        have e : (fun ω => 1 / P 0 ω) = fun _ => 1 / (p0 + d0 - β * d) := by
          funext ω; simp [hPdef]
        rw [e]
        exact integrable_const _
      | succ t =>
        refine hint.congr ?_
        filter_upwards [hyae] with ω h
        simp [hPdef, h]
    · cases t with
      | zero =>
        refine EventuallyEq.of_eq ?_
        rw [oneShot_E_zero, oneShot_E_zero]
        funext ω
        have e1 : ∫ ω, (P 0 / P 1) ω ∂S.μ =
            (p0 + d0 - β * d) * ∫ ω, 1 / (x ω + (1 - β) * d) ∂S.μ := by
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards [hyae] with ω h
          simp [hPdef, h, div_eq_mul_inv]
        have e2 : ∫ ω, (osTarget p0 x 0 / osTarget p0 x (0 + 1)) ω ∂S.μ =
            p0 * ∫ ω, 1 / x ω ∂S.μ := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp [osTarget, div_eq_mul_inv]
        change ∫ ω, (P 0 / P 1) ω ∂S.μ = ∫ ω, (osTarget p0 x 0 / osTarget p0 x (0 + 1)) ω ∂S.μ
        rw [e1, e2, heq]
      | succ t =>
        refine EventuallyEq.of_eq ?_
        have e1 : P (t + 1) / P (t + 1 + 1) = fun _ => 1 := by
          funext ω
          simp [hPdef, (hy0 ω).ne']
        have e2 : osTarget p0 x (t + 1) / osTarget p0 x (t + 1 + 1) = fun _ => 1 := by
          funext ω
          simp [osTarget, (hx0 ω).ne']
        rw [e1, e2]
    · filter_upwards [hpos] with ω h
      have hyω : y ω = x ω + (1 - β) * d := by simp [hy, h]
      have hg : HasSum (fun s => (if s = 0 then d0 - d else 0) + (1 - β) * d * β ^ s)
          (d0 - d + (1 - β) * d * (1 - β)⁻¹) :=
        (hasSum_ite_eq 0 (d0 - d)).add
          ((hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left ((1 - β) * d))
      have e : d0 - d + (1 - β) * d * (1 - β)⁻¹ = d0 := by
        field_simp
        ring
      rw [e] at hg
      refine hg.congr_fun fun s => ?_
      cases s with
      | zero => simp [hPdef, osTarget]; ring
      | succ s =>
        simp only [hPdef, Nat.add_one_ne_zero, ↓reduceIte, osTarget, hyω]
        ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (supporting the comparative statics of existence): for two
equilibria of the rule (`RuleEqmGen`, same `s₀` and target `0 < m ≤ P* ≤ M*`) with prices bounded
above and integrable `1/P`, `K_t = βᵗ N_t⁻¹ (1/P_t − 1/P'_t) Δ_t`, `Δ = (b − b')/θ`, is integrable
and `E_0 K_T → 0`: `Δ` is bounded, and `N⁻¹/P` is a martingale (`deflated_martingale`), so
`E_0 |K_T| ≤ βᵀ |Δ|_∞ (1/P_0 + 1/P'_0)`. No bounded-deflator hypothesis is needed. -/
theorem above_limit {β θ m Ms M M' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 Pstar P P' b b' : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hE' : RuleEqmGen S β θ s0 Pstar P' b')
    (hPM : ∀ t ω, P t ω ≤ M) (hP'M : ∀ t ω, P' t ω ≤ M')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ) :
    (∀ t, Integrable (fun ω => β ^ t * defl S Pstar t ω * (1 / P t ω - 1 / P' t ω) *
      (θ⁻¹ * (b t ω - b' t ω))) S.μ) ∧
    ∀ᵐ ω ∂S.μ, Tendsto (fun T => S.E 0 (fun ω => β ^ T * defl S Pstar T ω *
      (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω))) ω) atTop (𝓝 0) := by
  obtain ⟨hP, hPa, -, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  obtain ⟨hP', hP'a, -, hbi', hrate', hflow', hpre', -, htvc'⟩ := hE'
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hP'm : ∀ t, StronglyMeasurable[S.𝓕 t] (P' t) := fun t => hP'a t
  -- the rate target for both paths
  have hr : ∀ {Q : ℕ → Ω → ℝ} {MQ : ℝ}, (∀ t ω, 0 < Q t ω) → StronglyAdapted S.𝓕 Q →
      (∀ t, StronglyMeasurable[S.𝓕 t] (Q t)) → (∀ t ω, Q t ω ≤ MQ) →
      (∀ t, Integrable (fun ω => 1 / Q t ω) S.μ) →
      (∀ t, S.E t (Q t / Q (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) → ∀ t,
      S.E t (fun ω => 1 / Q (t + 1) ω) =ᵐ[S.μ] fun ω => gam S Pstar t ω * (1 / Q t ω) := by
    intro Q MQ hQ hQa hQm hQM hQq hQr t
    refine rate_q S hPsa hm hPs hQ hQa ?_ (hQq (t + 1)) (hQr t)
    exact (hQq (t + 1)).bdd_mul ((hQm t).mono (S.𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hQ t ω)]; exact hQM t ω)
  have hrP := hr hP hPa hPm hPM hq hrate
  have hrP' := hr hP' hP'a hP'm hP'M hq' hrate'
  -- the debt difference is bounded
  set d : ℕ → Ω → ℝ := fun t ω => b t ω - b' t ω with hd_def
  have hdflow : ∀ t ω, d t ω = θ * (P t ω - P' t ω) + β * d (t + 1) ω := fun t ω => by
    simp only [hd_def]
    rw [hflow t ω, hflow' t ω]
    ring
  have hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => θ * (P t ω - P' t ω)) := fun t =>
    ((hPm t).sub (hP'm t)).const_mul θ
  have hsC : ∀ t ω, |θ * (P t ω - P' t ω)| ≤ |θ| * (|M| + |M'|) := fun t ω => by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
    rw [abs_le]
    have := hP t ω
    have := hP' t ω
    have := hPM t ω
    have := hP'M t ω
    have := le_abs_self M
    have := le_abs_self M'
    constructor <;> linarith
  have hdpre : ∀ t, StronglyMeasurable[S.𝓕 t] (d (t + 1)) := fun t => (hpre t).sub (hpre' t)
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => (hbi t).sub (hbi' t)
  have hdtvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (d (t + T)) ω) atTop (𝓝 0) := by
    intro t
    filter_upwards [htvc t, htvc' t,
      ae_all_iff.2 fun T => S.E_sub (hbi (t + T)) (hbi' (t + T)) t] with ω e1 e2 e3
    have := e1.sub e2
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    change _ = β ^ T * S.E t (b (t + T) - b' (t + T)) ω
    rw [e3 T, Pi.sub_apply]
    ring
  have hdB := debt_bdd S hβ0 hβ1 (s := fun t ω => θ * (P t ω - P' t ω)) hsm hsC hdflow hdpre
    hdi hdtvc
  set KΔ : ℝ := |θ|⁻¹ * (|θ| * (|M| + |M'|) / (1 - β)) with hKΔ
  have hΔB : ∀ t, ∀ᵐ ω ∂S.μ, |θ⁻¹ * (b t ω - b' t ω)| ≤ KΔ := fun t => by
    filter_upwards [hdB t] with ω h
    rw [abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 (abs_nonneg θ))
  have hKΔ0 : 0 ≤ KΔ := by
    have h1β : 0 < 1 - β := by linarith
    positivity
  -- the deflated martingales `N⁻¹/P` and `N⁻¹/P'`
  have hmart : ∀ {Q : ℕ → Ω → ℝ}, (∀ t, StronglyMeasurable[S.𝓕 t] (Q t)) →
      (∀ t, Integrable (fun ω => 1 / Q t ω) S.μ) →
      (∀ t, S.E t (fun ω => 1 / Q (t + 1) ω) =ᵐ[S.μ]
        fun ω => gam S Pstar t ω * (1 / Q t ω)) → ∀ T,
      S.E 0 (fun ω => defl S Pstar T ω * (1 / Q T ω)) =ᵐ[S.μ] fun ω => 1 / Q 0 ω := by
    intro Q hQm hQq hQr T
    have h := deflated_martingale S (γ := gam S Pstar) (ρ := fun t ω => 1 / Q t ω)
      (Ninv := defl S Pstar) (fun t => ((hQm t).measurable.const_div 1).stronglyMeasurable)
      hQq (fun t => defl_meas S hPsa (Nat.le_succ t)) (fun t => defl_meas S hPsa le_rfl)
      (fun t => ⟨(Ms / m) ^ t, (defl_bounds S hPsa hm hPs t).mono fun ω h => by
        rw [abs_of_pos h.1]; exact h.2⟩) (defl_succ S hPsa hm hPs) hQr 0 T
    simp only [zero_add] at h
    refine h.trans (Eventually.of_forall fun ω => ?_)
    simp [defl]
  have hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => θ⁻¹ * (b t ω - b' t ω)) := fun t => by
    have e : (fun ω => θ⁻¹ * (b t ω - b' t ω)) =
        fun ω => P t ω - P' t ω + β * (θ⁻¹ * (b (t + 1) ω - b' (t + 1) ω)) := by
      funext ω
      rw [hflow t ω, hflow' t ω]
      field_simp
      ring
    rw [e]
    exact ((hPm t).sub (hP'm t)).add ((((hpre t).sub (hpre' t)).const_mul θ⁻¹).const_mul β)
  have hfacm : ∀ t, StronglyMeasurable[S.𝓕 t]
      (fun ω => β ^ t * defl S Pstar t ω * (θ⁻¹ * (b t ω - b' t ω))) := fun t =>
    ((defl_meas S hPsa (Nat.le_succ t)).const_mul _).mul (hΔm t)
  have hfacb : ∀ t, ∀ᵐ ω ∂S.μ, ‖β ^ t * defl S Pstar t ω * (θ⁻¹ * (b t ω - b' t ω))‖ ≤
      β ^ t * (Ms / m) ^ t * KΔ := fun t => by
    filter_upwards [defl_bounds S hPsa hm hPs t, hΔB t] with ω e1 e2
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (pow_pos hβ0 t), abs_of_pos e1.1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left e1.2 (pow_pos hβ0 t).le) e2 (abs_nonneg _)
      ((mul_pos (pow_pos hβ0 t) e1.1).le.trans (mul_le_mul_of_nonneg_left e1.2 (pow_pos hβ0 t).le))
  have hKi : ∀ t, Integrable (fun ω => β ^ t * defl S Pstar t ω * (1 / P t ω - 1 / P' t ω) *
      (θ⁻¹ * (b t ω - b' t ω))) S.μ := fun t =>
    (((hq t).sub (hq' t)).bdd_mul ((hfacm t).mono (S.𝓕.le t)).aestronglyMeasurable
      (hfacb t)).congr (Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring)
  refine ⟨hKi, ?_⟩
  have hNq : ∀ {Q : ℕ → Ω → ℝ}, (∀ t, Integrable (fun ω => 1 / Q t ω) S.μ) → ∀ T,
      Integrable (fun ω => defl S Pstar T ω * (1 / Q T ω)) S.μ := fun hQq T =>
    (hQq T).bdd_mul ((defl_meas S hPsa (Nat.le_succ T)).mono (S.𝓕.le T)).aestronglyMeasurable
      ((defl_bounds S hPsa hm hPs T).mono fun ω h => by
        rw [Real.norm_eq_abs, abs_of_pos h.1]; exact h.2)
  have hk : ∀ T, ∀ᵐ ω ∂S.μ, |S.E 0 (fun ω => β ^ T * defl S Pstar T ω *
      (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω))) ω| ≤
      β ^ T * KΔ * (1 / P 0 ω + 1 / P' 0 ω) := by
    intro T
    set Y : Ω → ℝ := fun ω => (defl S Pstar T ω * (1 / P T ω)) + (defl S Pstar T ω *
      (1 / P' T ω)) with hY
    set H : Ω → ℝ := (β ^ T * KΔ) • Y with hH
    have hYi : Integrable Y S.μ := (hNq hq T).add (hNq hq' T)
    have hHi : Integrable H S.μ := hYi.smul _
    have hKH : ∀ᵐ ω ∂S.μ, |β ^ T * defl S Pstar T ω * (1 / P T ω - 1 / P' T ω) *
        (θ⁻¹ * (b T ω - b' T ω))| ≤ H ω := by
      filter_upwards [defl_bounds S hPsa hm hPs T, hΔB T] with ω e1 e2
      have a1 := one_div_pos.2 (hP T ω)
      have a2 := one_div_pos.2 (hP' T ω)
      have hqq : |1 / P T ω - 1 / P' T ω| ≤ 1 / P T ω + 1 / P' T ω := by
        rw [abs_le]; constructor <;> linarith
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hβ0 T), abs_of_pos e1.1]
      calc β ^ T * defl S Pstar T ω * |1 / P T ω - 1 / P' T ω| * |θ⁻¹ * (b T ω - b' T ω)|
          ≤ β ^ T * defl S Pstar T ω * (1 / P T ω + 1 / P' T ω) * KΔ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqq (by have := e1.1; positivity)) e2
              (abs_nonneg _) (by have := e1.1; positivity)
        _ = H ω := by simp only [hH, hY, Pi.smul_apply, smul_eq_mul]; ring
    have hup := S.E_mono (hKi T) hHi (hKH.mono fun ω h => (le_abs_self _).trans h) 0
    have hlo := S.E_mono (hKi T).neg hHi (hKH.mono fun ω h => (neg_le_abs _).trans h) 0
    have hneg := condExp_neg (m := S.𝓕 0) (μ := S.μ) (fun ω => β ^ T * defl S Pstar T ω *
      (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω)))
    have hsm' := S.E_smul (β ^ T * KΔ) Y 0
    have hadd := S.E_add (hNq hq T) (hNq hq' T) 0
    filter_upwards [hup, hlo, hneg, hsm', hadd, hmart hPm hq hrP T, hmart hP'm hq' hrP' T]
      with ω e1 e2 e3 e4 e5 e6 e7
    have eH : S.E 0 H ω = β ^ T * KΔ * (1 / P 0 ω + 1 / P' 0 ω) := by
      have e4' : S.E 0 H ω = β ^ T * KΔ * S.E 0 Y ω := by
        rw [hH, e4, Pi.smul_apply, smul_eq_mul]
      have e5' : S.E 0 Y ω = S.E 0 (fun ω => defl S Pstar T ω * (1 / P T ω)) ω +
          S.E 0 (fun ω => defl S Pstar T ω * (1 / P' T ω)) ω := by
        change S.E 0 ((fun ω => defl S Pstar T ω * (1 / P T ω)) +
          fun ω => defl S Pstar T ω * (1 / P' T ω)) ω = _
        rw [e5, Pi.add_apply]
      rw [e4', e5', e6, e7]
    have e3' : S.E 0 (-fun ω => β ^ T * defl S Pstar T ω * (1 / P T ω - 1 / P' T ω) *
        (θ⁻¹ * (b T ω - b' T ω))) ω = -S.E 0 (fun ω => β ^ T * defl S Pstar T ω *
        (1 / P T ω - 1 / P' T ω) * (θ⁻¹ * (b T ω - b' T ω))) ω := e3
    rw [e3'] at e2
    rw [eH] at e1 e2
    rw [abs_le]
    constructor <;> linarith
  filter_upwards [ae_all_iff.2 hk] with ω e1
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (KΔ * (1 / P 0 ω + 1 / P' 0 ω))
  rw [zero_mul] at hg
  exact squeeze_zero_norm (fun T => by
    rw [Real.norm_eq_abs, ← mul_assoc]; exact e1 T) hg

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the comparison identity for equilibria bounded above**):
for two equilibria of the rule (`RuleEqmGen`, same `s₀` and target `0 < m ≤ P* ≤ M*`, news allowed)
with prices bounded above and any initial debts,
`∑_t E_0[βᵗ N_t⁻¹ (P'_t − P_t)²/(P_t P'_t)] = ((b_0 − b'_0)/θ)(1/P'_0 − 1/P_0)` a.e. — no
bounded-deflator hypothesis. With equal initial debts it re-proves `fr_compare`. -/
theorem compare_identity_above {β θ m Ms M M' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 Pstar P P' b b' : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hE' : RuleEqmGen S β θ s0 Pstar P' b')
    (hPM : ∀ t ω, P t ω ≤ M) (hP'M : ∀ t ω, P' t ω ≤ M')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun t => S.E 0 (fun ω => β ^ t * defl S Pstar t ω *
      ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω))) ω)
      (θ⁻¹ * (b 0 ω - b' 0 ω) * (1 / P' 0 ω - 1 / P 0 ω)) := by
  obtain ⟨hKi, hlim⟩ := above_limit S hβ0 hβ1 hθ hPsa hm hPs hE hE' hPM hP'M hq hq'
  obtain ⟨hP, hPa, -, -, hrate, hflow, hpre, -, -⟩ := hE
  obtain ⟨hP', hP'a, -, -, hrate', hflow', hpre', -, -⟩ := hE'
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hP'm : ∀ t, StronglyMeasurable[S.𝓕 t] (P' t) := fun t => hP'a t
  have hr : ∀ {Q : ℕ → Ω → ℝ} {MQ : ℝ}, (∀ t ω, 0 < Q t ω) → StronglyAdapted S.𝓕 Q →
      (∀ t, StronglyMeasurable[S.𝓕 t] (Q t)) → (∀ t ω, Q t ω ≤ MQ) →
      (∀ t, Integrable (fun ω => 1 / Q t ω) S.μ) →
      (∀ t, S.E t (Q t / Q (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) → ∀ t,
      S.E t (fun ω => 1 / Q (t + 1) ω) =ᵐ[S.μ] fun ω => gam S Pstar t ω * (1 / Q t ω) := by
    intro Q MQ hQ hQa hQm hQM hQq hQr t
    refine rate_q S hPsa hm hPs hQ hQa ?_ (hQq (t + 1)) (hQr t)
    exact (hQq (t + 1)).bdd_mul ((hQm t).mono (S.𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hQ t ω)]; exact hQM t ω)
  have hΔ : ∀ t ω, θ⁻¹ * (b t ω - b' t ω) =
      P t ω - P' t ω + β * (θ⁻¹ * (b (t + 1) ω - b' (t + 1) ω)) := fun t ω => by
    rw [hflow t ω, hflow' t ω]
    field_simp
    ring
  have h := drift_hasSum S hβ0 (Δ := fun t ω => θ⁻¹ * (b t ω - b' t ω)) hP hP' hPa hP'a
    hq hq' (hr hP hPa hPm hPM hq hrate) (hr hP' hP'a hP'm hP'M hq' hrate')
    (fun t => defl_meas S hPsa le_rfl) (defl_meas S hPsa (Nat.zero_le 1))
    (defl_succ S hPsa hm hPs) (fun t => (defl_bounds S hPsa hm hPs t).mono fun ω h => h.1.le)
    hΔ (fun t => ((hpre t).sub (hpre' t)).const_mul θ⁻¹) hKi hlim
  filter_upwards [h] with ω e
  have e0 : defl S Pstar 0 ω = 1 := by simp [defl]
  convert e using 1
  rw [e0]
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**comparative statics of existence**): if equilibria of
the rule with prices bounded above exist for initial debts `b̄ + θ d₀` and `b̄ + θ d₀'` with
`d₀ ≤ d₀'` (same target, news allowed), then `P_0 ≤ P'_0` a.e.: more initial debt (in units of
`θ`) means a higher date-0 price level. With `d₀ = d₀'` the equilibria coincide (`fr_compare`). -/
theorem price_monotone {β θ bbar d0 d0' m Ms M M' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar P P' b b' : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqm S β θ bbar Pstar P b) (hE' : RuleEqm S β θ bbar Pstar P' b')
    (hPM : ∀ t ω, P t ω ≤ M) (hP'M : ∀ t ω, P' t ω ≤ M')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) (hb0' : ∀ ω, b' 0 ω = bbar + θ * d0') (hd : d0 ≤ d0') :
    ∀ᵐ ω ∂S.μ, P 0 ω ≤ P' 0 ω := by
  rcases hd.lt_or_eq with hlt | heq
  · have h := compare_identity_above S hβ0 hβ1 hθ hPsa hm hPs ((ruleEqm_iff_gen S).1 hE)
      ((ruleEqm_iff_gen S).1 hE') hPM hP'M hq hq'
    have hnn : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ S.E 0 (fun ω => β ^ t * defl S Pstar t ω *
        ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω))) ω := fun t => by
      have hE0 := hE.1
      have hE0' := hE'.1
      have h0 : ∀ᵐ ω ∂S.μ, (0 : ℝ) ≤ β ^ t * defl S Pstar t ω *
          ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω)) := by
        filter_upwards [defl_bounds S hPsa hm hPs t] with ω hN
        have e : (P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω) =
            (P' t ω - P t ω) ^ 2 / (P t ω * P' t ω) := by
          field_simp [(hE0 t ω).ne', (hE0' t ω).ne']
        rw [e]
        exact mul_nonneg (mul_nonneg (pow_pos hβ0 t).le hN.1.le)
          (div_nonneg (sq_nonneg _) (mul_pos (hE0 t ω) (hE0' t ω)).le)
      by_cases hint : Integrable (fun ω => β ^ t * defl S Pstar t ω *
          ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω))) S.μ
      · have := S.E_mono (integrable_const 0) hint h0 0
        rw [S.E_const] at this
        exact this
      · exact Eventually.of_forall fun ω => by
          change (0 : ℝ) ≤ S.μ[fun ω => β ^ t * defl S Pstar t ω *
            ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω)) | S.𝓕 0] ω
          rw [condExp_of_not_integrable hint]
          simp
    filter_upwards [h, ae_all_iff.2 hnn] with ω e1 e2
    have hs := e1.nonneg e2
    rw [hb0 ω, hb0' ω] at hs
    have e : θ⁻¹ * (bbar + θ * d0 - (bbar + θ * d0')) = d0 - d0' := by field_simp; ring
    rw [e] at hs
    have h1 : 1 / P' 0 ω - 1 / P 0 ω ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_neg_of_neg_of_pos (sub_neg.2 hlt) hc
      linarith
    have a1 := hE.1 0 ω
    have a2 := hE'.1 0 ω
    rw [sub_nonpos, div_le_div_iff₀ a2 a1] at h1
    linarith
  · subst heq
    filter_upwards [(fr_compare S hβ0 hβ1 hθ ((ruleEqm_iff_gen S).1 hE)
      ((ruleEqm_iff_gen S).1 hE') hPM hP'M hq hq'
      (Eventually.of_forall fun ω => by rw [hb0 ω, hb0' ω]) 0).1] with ω h
    exact h.le

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**where the necessary condition is also sufficient**):
let the target `0 < m ≤ P* ≤ M*` (news at any number of dates) have a predetermined bounded present
value `a` (`a_t = P*_t + β a_{t+1}`, `a_{t+1}` known at `t`) with a known initial value `a₀`. Then
an equilibrium with prices bounded above and `b₀ = b̄ + θ d₀` exists **iff** `d₀ + a₀ > 0` — the
necessary condition of `exists_imp_pos` (here the realised present value of the target is `a₀` on
every path) is sufficient. With news in the target's present value it is not
(`FiscalRulesTargetClose.NoExist.oneShot_no_eqm`). -/
theorem predetermined_exists_iff {β θ bbar d0 m Ms K a0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar a : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K)
    (ha0 : ∀ ω, a 0 ω = a0) :
    (∃ (P b : ℕ → Ω → ℝ) (M : ℝ), RuleEqm S β θ bbar Pstar P b ∧ (∀ t ω, P t ω ≤ M) ∧
      (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∧ ∀ ω, b 0 ω = bbar + θ * d0) ↔
    0 < d0 + a0 := by
  have h1β : 0 < 1 - β := by linarith
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hapos : ∀ t ω, m / (1 - β) ≤ a t ω := fun t ω =>
    targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω
  have ha0pos : 0 < a0 := by
    obtain ⟨ω⟩ : Nonempty Ω := by
      by_contra hΩ
      rw [not_nonempty_iff] at hΩ
      have h1 : S.μ Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.2 hΩ, measure_empty] at h1
      exact zero_ne_one h1
    rw [← ha0 ω]
    exact (div_pos hm h1β).trans_le (hapos 0 ω)
  constructor
  · intro hex
    have hpos := exists_imp_pos S hβ0 hβ1 hθ hPsa hm hPs hex
    obtain ⟨ω, hω⟩ := hpos.exists
    -- the realised present value of the target is `a₀`
    have htel : ∀ T, a 0 ω = ∑ s ∈ Finset.range T, β ^ s * Pstar s ω + β ^ T * a T ω := by
      intro T
      induction T with
      | zero => simp
      | succ T ih =>
        rw [ih, Finset.sum_range_succ, ha T ω, pow_succ]
        ring
    have hsum : Summable (fun s => β ^ s * Pstar s ω) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right Ms)
        fun s => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 s), abs_of_pos (hPs0 s ω)]
          exact mul_le_mul_of_nonneg_left (hPs s ω).2 (pow_pos hβ0 s).le
    have hrem : Tendsto (fun T => β ^ T * a T ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun T => ?_)
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const K)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 T)]
      exact mul_le_mul_of_nonneg_left (haK T ω) (pow_pos hβ0 T).le
    have hpart : Tendsto (fun T => ∑ s ∈ Finset.range T, β ^ s * Pstar s ω) atTop
        (𝓝 (a 0 ω)) := by
      have := (tendsto_const_nhds (x := a 0 ω)).sub hrem
      rw [sub_zero] at this
      exact this.congr fun T => by rw [htel T]; ring
    have he := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpart
    rw [he, ha0 ω] at hω
    exact hω
  · intro hd
    have hc : ∀ ω, 0 < 1 + (bbar + θ * d0 - bbar) / (θ * a 0 ω) := fun ω => by
      rw [ha0 ω, show bbar + θ * d0 - bbar = θ * d0 by ring, mul_div_mul_left _ _ hθ]
      rw [show (1 : ℝ) + d0 / a0 = (d0 + a0) / a0 by field_simp; ring]
      exact div_pos hd ha0pos
    obtain ⟨hE, hb0⟩ := exists_proportional S hβ0 hβ1 hθ (b0 := bbar + θ * d0) hPsa hm hPs ha
      hapre haK hc
    set c : ℝ := 1 + (bbar + θ * d0 - bbar) / (θ * a0) with hcdef
    have hc' : ∀ ω, 1 + (bbar + θ * d0 - bbar) / (θ * a 0 ω) = c := fun ω => by rw [ha0 ω]
    have hc0 : 0 < c := by
      have e : c = (d0 + a0) / a0 := by
        rw [hcdef, show bbar + θ * d0 - bbar = θ * d0 by ring, mul_div_mul_left _ _ hθ]
        field_simp
        ring
      rw [e]
      exact div_pos hd ha0pos
    refine ⟨_, _, c * Ms, hE, fun t ω => ?_, fun t => ?_, fun ω => ?_⟩
    · rw [hc' ω]
      exact mul_le_mul_of_nonneg_left (hPs t ω).2 hc0.le
    · have e : (fun ω => 1 / ((1 + (bbar + θ * d0 - bbar) / (θ * a 0 ω)) * Pstar t ω)) =
          fun ω => 1 / (c * Pstar t ω) := funext fun ω => by rw [hc' ω]
      change Integrable (fun ω => 1 / ((1 + (bbar + θ * d0 - bbar) / (θ * a 0 ω)) * Pstar t ω))
        S.μ
      rw [e]
      refine Integrable.of_bound ((((hPsm t).measurable.const_mul c).const_div 1).mono
        (S.𝓕.le t) le_rfl).aestronglyMeasurable (1 / (c * m)) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (mul_pos hc0 (hPs0 t ω)))]
      exact one_div_le_one_div_of_le (mul_pos hc0 hm)
        (mul_le_mul_of_nonneg_left (hPs t ω).1 hc0.le)
    · exact hb0 ω

/-! ### (3) Finite-horizon information: the counterexample needs infinite news -/

/-- Cochrane (2023), §9.3.2, p. 267 (finite-horizon information): the system is **eventually
resolved** at `T` if no news arrives after date `T` — `𝓕_t ≤ 𝓕_T` for `t ≥ T` (so `𝓕_t = 𝓕_T`). -/
def EventuallyResolved (T : ℕ) : Prop := ∀ t, T ≤ t → S.𝓕 t ≤ S.𝓕 T

/-- Cochrane (2023), eq. (9.12), p. 267: once the system is resolved the target is known one date
ahead, so its real-rate factor is realised: `γ_i = P*_i/P*_{i+1}` for `i ≥ T`. -/
theorem resolved_gam {m Ms : ℝ} {T : ℕ} (hres : EventuallyResolved S T)
    {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) {i : ℕ} (hi : T ≤ i) (ω : Ω) :
    gam S Pstar i ω = Pstar i ω / Pstar (i + 1) ω := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hle : S.𝓕 (i + 1) ≤ S.𝓕 i := (hres (i + 1) (by omega)).trans (S.𝓕.mono hi)
  have hqm : StronglyMeasurable[S.𝓕 i] (fun ω => 1 / Pstar (i + 1) ω) :=
    (((hPsm (i + 1)).measurable.const_div 1).stronglyMeasurable).mono hle
  have hqi : Integrable (fun ω => 1 / Pstar (i + 1) ω) S.μ :=
    Integrable.of_bound (((hPsm (i + 1)).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le (i + 1))).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 (i + 1) ω))]
        exact one_div_le_one_div_of_le hm (hPs (i + 1) ω).1)
  simp only [gam, S.E_of_stronglyMeasurable hqm hqi]
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (**finite-horizon information bounds the deflator**): on a
system resolved at `T`, every adapted target `0 < m ≤ P* ≤ M*` has a bounded cumulative real-rate
factor: `∏_{i<k} E_{t+i}(P*_{t+i}/P*_{t+i+1})⁻¹ ≤ (M*/m)^{2T+1}` a.e. for all `t, k` (at most `T`
factors precede the resolution date; after it the product telescopes to `P*_{t+k}/P*_{max(t,T)}`).
-/
theorem resolved_hL {m Ms : ℝ} {T : ℕ} (hres : EventuallyResolved S T)
    {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) (t k : ℕ) :
    ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤
        (Ms / m) ^ (2 * T + 1) := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  filter_upwards [ae_all_iff.2 (gam_bounds S hPsa hm hPs)] with ω hγ
  have hMs : 0 < Ms := (hPs0 0 ω).trans_le (hPs 0 ω).2
  set c : ℝ := Ms / m with hc
  have hc1 : 1 ≤ c := by
    rw [hc, le_div_iff₀ hm, one_mul]
    exact (hPs 0 ω).1.trans (hPs 0 ω).2
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hpos : ∀ i, 0 < gam S Pstar i ω := fun i => (div_pos hm hMs).trans_le (hγ i).1
  have hinv : ∀ i, (gam S Pstar i ω)⁻¹ ≤ c := fun i => by
    rw [hc, ← inv_div]
    exact inv_anti₀ (div_pos hm hMs) (hγ i).1
  have hrat : ∀ i, 1 ≤ Pstar i ω / m ∧ Pstar i ω / m ≤ c := fun i =>
    ⟨by rw [le_div_iff₀ hm, one_mul]; exact (hPs i ω).1,
      div_le_div_of_nonneg_right (hPs i ω).2 hm.le⟩
  have key : ∀ k, ∏ i ∈ Finset.range k, (gam S Pstar (t + i) ω)⁻¹ ≤
      c ^ (2 * min k T) * (Pstar (t + k) ω / m) := by
    intro k
    induction k with
    | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, Nat.zero_min, mul_zero, pow_zero,
        one_mul, add_zero]
      exact (hrat t).1
    | succ k ih =>
      rw [Finset.prod_range_succ]
      have hG0 : 0 ≤ ∏ i ∈ Finset.range k, (gam S Pstar (t + i) ω)⁻¹ :=
        Finset.prod_nonneg fun i _ => (inv_pos.2 (hpos _)).le
      by_cases h : T ≤ t + k
      · have e : (gam S Pstar (t + k) ω)⁻¹ = Pstar (t + k + 1) ω / Pstar (t + k) ω := by
          rw [resolved_gam S hres hPsa hm hPs h ω, inv_div]
        rw [e]
        have hmono : c ^ (2 * min k T) ≤ c ^ (2 * min (k + 1) T) :=
          pow_le_pow_right₀ hc1 (by omega)
        calc (∏ i ∈ Finset.range k, (gam S Pstar (t + i) ω)⁻¹) *
              (Pstar (t + k + 1) ω / Pstar (t + k) ω)
            ≤ c ^ (2 * min k T) * (Pstar (t + k) ω / m) *
                (Pstar (t + k + 1) ω / Pstar (t + k) ω) :=
              mul_le_mul_of_nonneg_right ih (div_pos (hPs0 _ ω) (hPs0 _ ω)).le
          _ = c ^ (2 * min k T) * (Pstar (t + (k + 1)) ω / m) := by
              rw [show t + (k + 1) = t + k + 1 by ring]
              field_simp [(hPs0 (t + k) ω).ne']
          _ ≤ c ^ (2 * min (k + 1) T) * (Pstar (t + (k + 1)) ω / m) :=
              mul_le_mul_of_nonneg_right hmono (zero_le_one.trans (hrat _).1)
      · push Not at h
        have hk1 : min (k + 1) T = min k T + 1 := by omega
        rw [hk1, show 2 * (min k T + 1) = 2 * min k T + 1 + 1 by ring, pow_succ, pow_succ]
        have hcp : 0 ≤ c ^ (2 * min k T) := pow_nonneg hc0 _
        calc (∏ i ∈ Finset.range k, (gam S Pstar (t + i) ω)⁻¹) * (gam S Pstar (t + k) ω)⁻¹
            ≤ c ^ (2 * min k T) * (Pstar (t + k) ω / m) * c :=
              mul_le_mul ih (hinv _) (inv_pos.2 (hpos _)).le
                (mul_nonneg hcp (zero_le_one.trans (hrat _).1))
          _ ≤ c ^ (2 * min k T) * c * c * 1 := by
              have := mul_le_mul_of_nonneg_left (hrat (t + k)).2 hcp
              nlinarith
          _ ≤ c ^ (2 * min k T) * c * c * (Pstar (t + (k + 1)) ω / m) :=
              mul_le_mul_of_nonneg_left (hrat _).1 (mul_nonneg (mul_nonneg hcp hc0) hc0)
  calc ∏ i ∈ Finset.range k,
        (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹
      = ∏ i ∈ Finset.range k, (gam S Pstar (t + i) ω)⁻¹ := rfl
    _ ≤ c ^ (2 * min k T) * (Pstar (t + k) ω / m) := key k
    _ ≤ c ^ (2 * T) * c :=
        mul_le_mul (pow_le_pow_right₀ hc1 (by omega)) (hrat _).2
          (zero_le_one.trans (hrat _).1) (pow_nonneg hc0 _)
    _ = c ^ (2 * T + 1) := by rw [pow_succ]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), finite-horizon information, prices
bounded away from zero**): on a system resolved at some date `T`, for every adapted target
`0 < m ≤ P* ≤ M*` (news before `T` allowed), every equilibrium of the rule with prices bounded away
from zero and `b₀ = b̄` is `P = P*` — no bounded-deflator hypothesis is needed. So the
counterexample `FiscalRulesBelowCounter.fr_below_counterexample` needs news at infinitely many
dates. -/
theorem fr_d_resolved {β θ bbar mP m Ms : ℝ} {T : ℕ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    (hres : EventuallyResolved S T) {Pstar P b : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hm : 0 < m) (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqm S β θ bbar Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hb0 : ∀ ω, b 0 ω = bbar) (t : ℕ) : P t =ᵐ[S.μ] Pstar t :=
  fr_d_news_below S hβ0 hβ1 hθ hPsa hm hPs (resolved_hL S hres hPsa hm hPs) hE hmP hPmP hb0 t

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**finite-horizon information, any initial debt**): on a
system resolved at some date, two equilibria of the rule with prices bounded away from zero
(possibly unbounded above) and the same initial debt coincide. -/
theorem fr_unique_resolved {β θ bbar mP mP' m Ms : ℝ} {T : ℕ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) (hres : EventuallyResolved S T) {Pstar P P' b b' : ℕ → Ω → ℝ}
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqm S β θ bbar Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hE' : RuleEqm S β θ bbar Pstar P' b') (hmP' : 0 < mP') (hP'mP : ∀ t ω, mP' ≤ P' t ω)
    (hb0 : b 0 =ᵐ[S.μ] b' 0) (t : ℕ) : P t =ᵐ[S.μ] P' t ∧ b t =ᵐ[S.μ] b' t :=
  fr_unique_below_rule S hβ0 hβ1 hθ hPsa hm hPs
    (hL0_of_hL S (resolved_hL S hres hPsa hm hPs)) hE hmP hPmP hE' hmP' hP'mP hb0 t

/-- Cochrane (2023), §9.3.2, p. 267 (**the counterexample's information never resolves**): the
i.i.d. coin system of `FiscalRulesBelowCounter.fr_below_counterexample` is not resolved at any
date — otherwise `resolved_hL` would bound its deflator, which the counterexample shows is
unbounded. -/
theorem iid_not_resolved {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) :
    ¬ EventuallyResolved (FiscalRulesBelowCounter.Sys hβ0 hβ1) T := by
  intro hres
  obtain ⟨-, -, -, -, -, hPsa, hPs, -, -, -, -, -, -, hnoL⟩ :=
    FiscalRulesBelowCounter.fr_below_counterexample hβ0 hβ1 one_ne_zero 0
  have hm : 0 < (2 - β) * (1 - β) / 2 := by
    have : 0 < (2 - β) * (1 - β) := mul_pos (by linarith) (by linarith)
    linarith
  exact hnoL ⟨_, resolved_hL _ hres hPsa hm hPs⟩

/-- Cochrane (2023), §9.3.2, p. 267 (**every finite system is eventually resolved**): on a finite
state space the filtration stabilises — the number of date-`t` events is nondecreasing and bounded
by `2^{2^{|Ω|}}`, so it is eventually constant, and then the σ-algebras coincide. -/
theorem finite_resolved [Finite Ω] : ∃ T, EventuallyResolved S T := by
  set c : ℕ → ℕ := fun t => Set.ncard {s : Set Ω | MeasurableSet[S.𝓕 t] s} with hc
  have hbdd : BddAbove (Set.range c) :=
    ⟨Nat.card (Set Ω), by rintro _ ⟨t, rfl⟩; exact Set.ncard_le_card _⟩
  obtain ⟨T, hT⟩ := Nat.sSup_mem (Set.range_nonempty c) hbdd
  refine ⟨T, fun t ht s hs => ?_⟩
  have hsub : {s : Set Ω | MeasurableSet[S.𝓕 T] s} ⊆ {s : Set Ω | MeasurableSet[S.𝓕 t] s} :=
    fun s hs => S.𝓕.mono ht s hs
  have hle : c t ≤ c T := by
    rw [hT]
    exact le_csSup hbdd ⟨t, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub hle
  have : s ∈ {s : Set Ω | MeasurableSet[S.𝓕 t] s} := hs
  rw [← heq] at this
  exact this

/-- Cochrane (2023), §9.3.2, p. 267 (**link**: core finite trees): on every finite system — in
particular every bridged core `FiniteTree` (`TreeBridge.treeSystem`) — each adapted target
`0 < m ≤ P* ≤ M*` has a bounded deflator, so prices bounded away from zero already give uniqueness
(`fr_unique_resolved`): "on a finite tree the deflator is automatically bounded". -/
theorem finite_hL [Finite Ω] {m Ms : ℝ} {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hm : 0 < m) (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) :
    ∃ L, ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L := by
  obtain ⟨T, hres⟩ := finite_resolved S
  exact ⟨_, resolved_hL S hres hPsa hm hPs⟩

/-- Cochrane (2023), §9.3.2, p. 267 (**link** to the core `ExpectationsFiniteTree`): for every core
finite tree, the bridged measure system has a bounded deflator for every bounded adapted target,
and Theorem FR (d) for prices bounded away from zero (`b₀ = b̄`, `P = P*`) holds on it without
further hypotheses. -/
theorem tree_fr_d [Fintype Ω] [DiscreteMeasurableSpace Ω] (Tr : ExpectationsFiniteTree.FiniteTree Ω)
    {β θ bbar mP m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) {Pstar P b : ℕ → Ω → ℝ}
    (hPsa : StronglyAdapted (TreeBridge.treeSystem Tr).𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqm (TreeBridge.treeSystem Tr) β θ bbar Pstar P b) (hmP : 0 < mP)
    (hPmP : ∀ t ω, mP ≤ P t ω) (hb0 : ∀ ω, b 0 ω = bbar) (t : ℕ) :
    P t =ᵐ[(TreeBridge.treeSystem Tr).μ] Pstar t := by
  obtain ⟨T, hres⟩ := finite_resolved (TreeBridge.treeSystem Tr)
  exact fr_d_resolved _ hβ0 hβ1 hθ hres hPsa hm hPs hE hmP hPmP hb0 t

end Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetFinal
