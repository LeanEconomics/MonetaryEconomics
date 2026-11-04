/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasFiscal
import IntertemporalModel.TidyR5MeasLinear

/-!
# Impulse responses and price-level targets on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.5, pp. 34–38 (Figure 2.1:
responses to interest-rate and fiscal shocks under a peg, announcements, the expected fiscal
shock; §2.5.1, the fiscal price-level target) and §2.6, pp. 39–42 (Figure 2.2: responses under
the rule `i_t = θπ_t + u_t`), on a probability space with a filtration (`MeasExpectationSystem`),
with Mathlib's conditional expectation and equations holding almost surely. Impulse responses
are innovations `ΔE_{t+1}` at a general shock date, as in `LinearFTMP`.

## Main results

* Innovation algebra almost surely: `innov_add'`, `innov_sub'`, `innov_smul'`, `innov_lin3`,
  `innov_known`, `innov_shock`, `innov_shock_later`, `mInnov_of_news`.
* Figure 2.1 (peg, `π_{t+1} = i_t − ε_{Σs,t+1}` a.s.): `mIrf_peg_impact`, `mIrf_peg_later`,
  `mFig21_rate`, `mFig21_fiscal`, `mExpected_inflation_ahead`, `mAnnouncement_invariant`,
  `mNo_announcement_effect`, `mLong_run_fisher`; the expected fiscal shock:
  `mPvNews_of_news`, `mFig21_expected_fiscal` (inflation when the news arrives, however late the
  surpluses move).
* §2.5.1: `mPTarget_price`, `mPTarget_rate_lowers_price`, `mPTarget_fiscal_contraction`,
  `mLoggerhead`, `mInnov_pi_eq_innov_p`.
* Figure 2.2 (rule): `mIrf_disturbance`, `mIrf_rule`, `mIrf_rule_rate`, `mFig22_monetary`,
  `mFig22_fiscal`, `mFiscal_sets_impact`, `mOne_time_price_jump`, `mPrice_level_returns`. The hump
  (`LinearFTMP.hump_exists`, `LinearFTMP.fig22_peak`) is a statement about the deterministic
  coefficients `LinearFTMP.conv` and needs no restatement.
* Links back to the core on finite trees: `Link.tree_irf_peg_impact`, `Link.tree_irf_rule`,
  `Link.tree_pTarget_price`.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasLinearIRF

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR5MeasLinear TidyR6MeasFiscal

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Innovation algebra almost surely -/

/-- Cochrane (2023), eq. (2.13), p. 30, on a probability space: news is additive (integrable
variables), almost surely.
Restates `ExpectationTools.innov_add` on a genuine probability space. -/
theorem innov_add' {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.innov t (x + y) =ᵐ[S.μ] S.innov t x + S.innov t y := by
  filter_upwards [S.E_add hx hy (t + 1), S.E_add hx hy t] with ω h1 h2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.add_apply, h1, h2]
  ring

/-- Cochrane (2023), eq. (2.13), p. 30, on a probability space: news commutes with differences
(integrable variables), almost surely.
Restates `ExpectationTools.innov_sub` on a genuine probability space. -/
theorem innov_sub' {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.innov t (x - y) =ᵐ[S.μ] S.innov t x - S.innov t y := by
  filter_upwards [S.E_sub hx hy (t + 1), S.E_sub hx hy t] with ω h1 h2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, h1, h2]
  ring

/-- Cochrane (2023), eq. (2.13), p. 30, on a probability space: news is homogeneous, almost
surely.
Restates `ExpectationTools.innov_smul` on a genuine probability space. -/
theorem innov_smul' (c : ℝ) (x : Ω → ℝ) (t : ℕ) :
    S.innov t (c • x) =ᵐ[S.μ] c • S.innov t x := by
  filter_upwards [S.E_smul c x (t + 1), S.E_smul c x t] with ω h1 h2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- Cochrane (2023), eq. (2.13), p. 30, on a probability space: the news of `a x + y − z` for
integrable `x`, `y`, `z`, almost surely. -/
theorem innov_lin3 (a : ℝ) {x y z : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ)
    (hz : Integrable z S.μ) (t : ℕ) :
    S.innov t (a • x + y - z) =ᵐ[S.μ] a • S.innov t x + S.innov t y - S.innov t z := by
  filter_upwards [innov_sub' S ((hx.smul a).add hy) hz t, innov_add' S (hx.smul a) hy t,
    innov_smul' S a x t] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.sub_apply, Pi.add_apply]

/-- Cochrane (2023), p. 35: a variable known and integrable at `t` has no news at `t + 1`. -/
theorem innov_known {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    (hi : Integrable x S.μ) : S.innov t x = 0 := by
  simp only [MeasExpectationSystem.innov]
  rw [S.E_of_stronglyMeasurable (hx.mono (S.𝓕.mono (Nat.le_succ t))) hi,
    S.E_of_stronglyMeasurable hx hi, sub_self]

/-- Cochrane (2023), p. 40, on a probability space: a shock's news on arrival is the shock,
`ΔE_{t+1} ε_{t+1} = ε_{t+1}` almost surely.
Restates `LinearFTMP.innov_shock` on a genuine probability space. -/
theorem innov_shock {ε : ℕ → Ω → ℝ} (hε : MIsShock S ε) (t : ℕ) :
    S.innov t (ε (t + 1)) =ᵐ[S.μ] ε (t + 1) := by
  filter_upwards [hε.2.2 t] with ω h
  simp only [MeasExpectationSystem.innov, Pi.sub_apply,
    S.E_of_stronglyMeasurable (hε.1 t) (hε.2.1 t), h, Pi.zero_apply, sub_zero]

/-- Cochrane (2023), p. 40 (a shock "only moves unexpectedly"), on a probability space: a later
shock has no news at an earlier date, `ΔE_{t+1} ε_{t+2+j} = 0` almost surely.
Restates `LinearFTMP.innov_shock_later` on a genuine probability space. -/
theorem innov_shock_later {ε : ℕ → Ω → ℝ} (hε : MIsShock S ε) (t j : ℕ) :
    S.innov t (ε (t + 2 + j)) =ᵐ[S.μ] 0 := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e]
  filter_upwards [(S.E_tower (show t + 1 ≤ t + 1 + j by omega) (ε (t + 1 + j + 1))).symm,
    S.E_congr (hε.2.2 (t + 1 + j)) (t + 1),
    (S.E_tower (show t ≤ t + 1 + j by omega) (ε (t + 1 + j + 1))).symm,
    S.E_congr (hε.2.2 (t + 1 + j)) t] with ω h1 h2 h3 h4
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.zero_apply]
  rw [h1, h2, h3, h4, S.E_zero]
  simp

/-- Cochrane (2023), Figure 2.1 and pp. 36–37, on a probability space: a random variable revealed
at `a + 1` (known at `a + 1`, integrable, `E_a x = 0` a.s.) has news `x` at `a + 1` and none at
any other date, almost surely.
Restates `LinearFTMP.innov_of_news` on a genuine probability space. -/
theorem mInnov_of_news {a : ℕ} {x : Ω → ℝ} (hxa : StronglyMeasurable[S.𝓕 (a + 1)] x)
    (hxi : Integrable x S.μ) (hx0 : S.E a x =ᵐ[S.μ] 0) (t : ℕ) :
    S.innov t x =ᵐ[S.μ] if t = a then x else 0 := by
  rcases lt_trichotomy t a with hlt | heq | hgt
  · simp only [hlt.ne, ↓reduceIte]
    filter_upwards [(S.E_tower (show t + 1 ≤ a by omega) x).symm, S.E_congr hx0 (t + 1),
      (S.E_tower hlt.le x).symm, S.E_congr hx0 t] with ω h1 h2 h3 h4
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.zero_apply]
    rw [h1, h2, h3, h4, S.E_zero]
    simp
  · subst heq
    simp only [↓reduceIte]
    filter_upwards [hx0] with ω h
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, S.E_of_stronglyMeasurable hxa hxi, h,
      Pi.zero_apply, sub_zero]
  · simp only [hgt.ne', ↓reduceIte]
    rw [innov_known S (hxa.mono (S.𝓕.mono (show a + 1 ≤ t by omega))) hxi]

/-! ### Figure 2.1: the peg -/

variable {i ε π u εi p p' pstar : ℕ → Ω → ℝ}

/-- Cochrane (2023), Figure 2.1 and p. 36 ("there is no unexpected time-`t` inflation without a
fiscal shock"), on a probability space: under the peg solution `π_{t+1} = i_t − ε_{Σs,t+1}`
a.s. (adapted integrable rate, shock `ε`), `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` almost surely.
Restates `LinearFTMP.irf_peg_impact` on a genuine probability space. -/
theorem mIrf_peg_impact (hia : StronglyAdapted S.𝓕 i) (hii : ∀ t, Integrable (i t) S.μ)
    (hε : MIsShock S ε) (h : ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1)) (t : ℕ) :
    S.innov t (π (t + 1)) =ᵐ[S.μ] -ε (t + 1) := by
  filter_upwards [innov_congr S (h t) t, innov_sub' S (hii t) (hε.2.1 t) t, innov_shock S hε t]
    with ω e1 e2 e3
  rw [e1, e2, Pi.sub_apply, innov_known S (hia t) (hii t), e3]
  simp

/-- Cochrane (2023), Figure 2.1 and p. 36 ("inflation moves up one period later"), on a
probability space: `ΔE_{t+1} π_{t+2+j} = ΔE_{t+1} i_{t+1+j}` almost surely.
Restates `LinearFTMP.irf_peg_later` on a genuine probability space. -/
theorem mIrf_peg_later (hii : ∀ t, Integrable (i t) S.μ) (hε : MIsShock S ε)
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1)) (t j : ℕ) :
    S.innov t (π (t + 2 + j)) =ᵐ[S.μ] S.innov t (i (t + 1 + j)) := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  have hl := innov_shock_later S hε t j
  rw [e] at hl ⊢
  filter_upwards [innov_congr S (h (t + 1 + j)) t, innov_sub' S (hii _) (hε.2.1 _) t, hl]
    with ω e1 e2 e3
  rw [e1, e2, Pi.sub_apply, e3, Pi.zero_apply, sub_zero]

/-- Cochrane (2023), Figure 2.1, top panel, on a probability space: almost surely, where there is
no fiscal shock and the rate news is a permanent `1`, inflation does not move on impact and is
`1` from `t + 2` on.
Restates `LinearFTMP.fig21_rate` on a genuine probability space. -/
theorem mFig21_rate (hia : StronglyAdapted S.𝓕 i) (hii : ∀ t, Integrable (i t) S.μ)
    (hε : MIsShock S ε) (h : ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ε (t + 1) ω = 0 → (∀ j, S.innov t (i (t + 1 + j)) ω = 1) →
      S.innov t (π (t + 1)) ω = 0 ∧ ∀ j, S.innov t (π (t + 2 + j)) ω = 1 := by
  filter_upwards [mIrf_peg_impact S hia hii hε h t,
    ae_all_iff.2 fun j => mIrf_peg_later S hii hε h t j] with ω h1 h2 hε0 hn
  refine ⟨?_, fun j => ?_⟩
  · rw [h1, Pi.neg_apply, hε0, neg_zero]
  · rw [h2 j, hn j]

/-- Cochrane (2023), Figure 2.1, bottom panel, on a probability space: almost surely, where the
fiscal shock is `−1` and there is no rate news, inflation is `1` on impact and `0` afterwards.
Restates `LinearFTMP.fig21_fiscal` on a genuine probability space. -/
theorem mFig21_fiscal (hia : StronglyAdapted S.𝓕 i) (hii : ∀ t, Integrable (i t) S.μ)
    (hε : MIsShock S ε) (h : ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ε (t + 1) ω = -1 → (∀ j, S.innov t (i (t + 1 + j)) ω = 0) →
      S.innov t (π (t + 1)) ω = 1 ∧ ∀ j, S.innov t (π (t + 2 + j)) ω = 0 := by
  filter_upwards [mIrf_peg_impact S hia hii hε h t,
    ae_all_iff.2 fun j => mIrf_peg_later S hii hε h t j] with ω h1 h2 hε1 hn
  refine ⟨?_, fun j => ?_⟩
  · rw [h1, Pi.neg_apply, hε1, neg_neg]
  · rw [h2 j, hn j]

/-- Cochrane (2023), p. 36 ("If `E_{t−k} i_t` rises, then `E_{t−k} π_{t+1}` rises"), on a
probability space: `E_s π_{t+1} = E_s i_t` almost surely for every `s ≤ t`.
Restates `LinearFTMP.expected_inflation_ahead` on a genuine probability space. -/
theorem mExpected_inflation_ahead (hii : ∀ t, Integrable (i t) S.μ) (hε : MIsShock S ε)
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1)) {s t : ℕ} (hst : s ≤ t) :
    S.E s (π (t + 1)) =ᵐ[S.μ] S.E s (i t) := by
  filter_upwards [S.E_congr (h t) s, S.E_sub (hii t) (hε.2.1 t) s,
    (S.E_tower hst (ε (t + 1))).symm, S.E_congr (hε.2.2 t) s] with ω h1 h2 h3 h4
  rw [h1, h2, Pi.sub_apply, h3, h4, S.E_zero, Pi.zero_apply, sub_zero]

/-- Cochrane (2023), p. 36 ("The response is the same if the interest-rate movement is announced
ahead of time"), on a probability space: two filtrations on the same probability measure (e.g.
the rate path announced early or revealed date by date), the same rate path, no fiscal shocks
and the same `π_0` give the same inflation path almost surely.
Restates `LinearFTMP.announcement_invariant` on a genuine probability space. -/
theorem mAnnouncement_invariant (S₁ S₂ : MeasExpectationSystem Ω) (hμ : S₁.μ = S₂.μ)
    {π₁ π₂ : ℕ → Ω → ℝ} (h₁ : ∀ t, π₁ (t + 1) =ᵐ[S₁.μ] i t)
    (h₂ : ∀ t, π₂ (t + 1) =ᵐ[S₂.μ] i t) (h0 : π₁ 0 =ᵐ[S₁.μ] π₂ 0) (t : ℕ) :
    π₁ t =ᵐ[S₁.μ] π₂ t := by
  cases t with
  | zero => exact h0
  | succ t =>
    have h₂' : π₂ (t + 1) =ᵐ[S₁.μ] i t := by rw [hμ]; exact h₂ t
    exact (h₁ t).trans h₂'.symm

/-- Cochrane (2023), p. 36 ("announcements of future policy ... Not in this case"), on a
probability space: two rate paths that agree almost surely before `T` give the same inflation
almost surely up to and including `T`.
Restates `LinearFTMP.no_announcement_effect` on a genuine probability space. -/
theorem mNo_announcement_effect {i' π' : ℕ → Ω → ℝ}
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1)) (h' : ∀ t, π' (t + 1) =ᵐ[S.μ] i' t - ε (t + 1))
    (h0 : π 0 =ᵐ[S.μ] π' 0) {T : ℕ} (hii : ∀ s < T, i s =ᵐ[S.μ] i' s) :
    ∀ s ≤ T, π s =ᵐ[S.μ] π' s := by
  intro s hs
  cases s with
  | zero => exact h0
  | succ s =>
    filter_upwards [h s, h' s, hii s (by omega)] with ω e1 e2 e3
    rw [e1, e2, Pi.sub_apply, Pi.sub_apply, e3]

/-- Cochrane (2023), p. 37 ("in the long run higher nominal interest rates must come with higher
inflation"), on a probability space: a constant rate `c` and no fiscal shocks give
`π_{t+1} = c` almost surely.
Restates `LinearFTMP.long_run_fisher` on a genuine probability space. -/
theorem mLong_run_fisher {c : ℝ} (h : ∀ t, π (t + 1) =ᵐ[S.μ] i t - ε (t + 1))
    (hc : ∀ t, i t = fun _ => c) (hε : ε = 0) (t : ℕ) : π (t + 1) =ᵐ[S.μ] fun _ => c := by
  filter_upwards [h t] with ω e
  rw [e, hc t, hε]
  simp

/-! ### Figure 2.1: the expected fiscal shock -/

/-- Cochrane (2023), Figure 2.1 and pp. 36–37 ("The fiscal shock is a shock to the present value
of surpluses, so when surpluses actually change does not matter"), on a probability space: with
surpluses `s_k = c_k + D_k x` (bounded `c`, `D`; `x` revealed at `a + 1`, integrable,
`E_a x = 0` a.s.) and `0 ≤ β < 1`, the fiscal shock `ΔE_{t+1} PV_{t+1}` is almost surely
`(∑ₖ βᵏ D_{a+1+k}) x` at `t = a` and `0` at every other date.
Restates `LinearFTMP.pvNews_of_news` on a genuine probability space. -/
theorem mPvNews_of_news {β C Dm : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c D : ℕ → ℝ}
    (hc : ∀ k, |c k| ≤ C) (hD : ∀ k, |D k| ≤ Dm) {a : ℕ} {x : Ω → ℝ}
    (hxa : StronglyMeasurable[S.𝓕 (a + 1)] x) (hxi : Integrable x S.μ)
    (hx0 : S.E a x =ᵐ[S.μ] 0) (t : ℕ) :
    mFiscShock S β (fun k ω => c k + D k * x ω) (t + 1) =ᵐ[S.μ]
      if t = a then (∑' k, β ^ k * D (a + 1 + k)) • x else 0 := by
  have ha : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  set K : ℕ → ℝ := fun n => ∑' k, β ^ k * D (n + k) with hK
  set Cn : ℕ → ℝ := fun n => ∑' k, β ^ k * c (n + k) with hCn
  have hds : ∀ n, MeasExpectationSystem.discSum β (fun k ω => c k + D k * x ω) n =
      fun ω => Cn n + K n * x ω := fun n => by
    funext ω
    simp only [MeasExpectationSystem.discSum, hK, hCn]
    have h1 : Summable (fun k => β ^ k * c (n + k)) :=
      MeasExpectationSystem.summable_geom_mul ha fun k => hc (n + k)
    have h2 : Summable (fun k => β ^ k * D (n + k)) :=
      MeasExpectationSystem.summable_geom_mul ha fun k => hD (n + k)
    rw [← tsum_mul_right, ← h1.tsum_add (h2.mul_right (x ω))]
    exact tsum_congr fun k => by ring
  have hE : ∀ m n, S.E m (fun ω => Cn n + K n * x ω) =ᵐ[S.μ]
      fun ω => Cn n + K n * S.E m x ω := fun m n => by
    have e : (fun ω => Cn n + K n * x ω) = (fun _ => Cn n) + K n • x := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    filter_upwards [S.E_add (integrable_const (Cn n)) (hxi.smul (K n)) m,
      S.E_smul (K n) x m] with ω h1 h2
    rw [h1, Pi.add_apply, S.E_const, h2, Pi.smul_apply, smul_eq_mul]
  have hk : S.E (t + 1) (S.forwardSol β (fun k ω => c k + D k * x ω) (t + 1)) =
      S.forwardSol β (fun k ω => c k + D k * x ω) (t + 1) := S.E_E_self (t + 1) _
  have hfs : S.forwardSol β (fun k ω => c k + D k * x ω) (t + 1) =
      S.E (t + 1) (fun ω => Cn (t + 1) + K (t + 1) * x ω) := by
    change S.E (t + 1) (MeasExpectationSystem.discSum β _ (t + 1)) = _
    rw [hds]
  have htow : S.E t (S.forwardSol β (fun k ω => c k + D k * x ω) (t + 1)) =ᵐ[S.μ]
      S.E t (fun ω => Cn (t + 1) + K (t + 1) * x ω) := by
    rw [hfs]
    exact S.E_tower (Nat.le_succ t) _
  filter_upwards [hE (t + 1) (t + 1), htow, hE t (t + 1), mInnov_of_news S hxa hxi hx0 t]
    with ω e1 e2 e3 e4
  change S.innov t (S.forwardSol β (fun k ω => c k + D k * x ω) (t + 1)) ω = _
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk] at e4 ⊢
  rw [hfs, e1, ← hfs, e2, e3]
  have e5 : K (t + 1) * (S.E (t + 1) x ω - S.E t x ω) =
      K (t + 1) * (if t = a then x else 0) ω := by rw [e4]
  by_cases hta : t = a
  · subst hta
    simp only [↓reduceIte, Pi.smul_apply, smul_eq_mul] at e5 ⊢
    rw [← e5]
    ring
  · simp only [hta, ↓reduceIte, Pi.zero_apply, mul_zero] at e5 ⊢
    linear_combination e5

/-- Cochrane (2023), Figure 2.1, "expected fiscal shock" (pp. 36–37: "Inflation happens when the
shock is announced, not when surpluses appear"), on a probability space: with no rate response
and fiscal shocks equal to the PV news of surpluses `c_k + D_k x` announced at `a + 1`,
inflation is almost surely `−(∑ₖ βᵏ D_{a+1+k}) x` at `a + 1` and `0` at every other date.
Restates `LinearFTMP.fig21_expected_fiscal` on a genuine probability space. -/
theorem mFig21_expected_fiscal {β C Dm : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c D : ℕ → ℝ}
    (hc : ∀ k, |c k| ≤ C) (hD : ∀ k, |D k| ≤ Dm) {a : ℕ} {x : Ω → ℝ}
    (hxa : StronglyMeasurable[S.𝓕 (a + 1)] x) (hxi : Integrable x S.μ)
    (hx0 : S.E a x =ᵐ[S.μ] 0)
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] 0 - mFiscShock S β (fun k ω => c k + D k * x ω) (t + 1))
    (t : ℕ) :
    π (t + 1) =ᵐ[S.μ] if t = a then -((∑' k, β ^ k * D (a + 1 + k)) • x) else 0 := by
  filter_upwards [h t, mPvNews_of_news S hβ0 hβ1 hc hD hxa hxi hx0 t] with ω e1 e2
  rw [e1, Pi.sub_apply, e2]
  by_cases hta : t = a
  · simp [hta]
  · simp [hta]

/-! ### §2.5.1: a fiscal price-level target -/

/-- Cochrane (2023), §2.5.1, p. 38, on a probability space: if fiscal policy attains the target
`p_{t+1} = p*_{t+1}` and the Fisher equation `i_t = E_t(p_{t+1} − p_t)` holds (log price level
known at `t`, integrable), then `p_t = E_t p*_{t+1} − i_t` almost surely.
Restates `LinearFTMP.pTarget_price` on a genuine probability space. -/
theorem mPTarget_price {t : ℕ} (hp : StronglyMeasurable[S.𝓕 t] (p t))
    (hpi : Integrable (p t) S.μ) (hp1 : Integrable (p (t + 1)) S.μ)
    (hfis : i t =ᵐ[S.μ] S.E t (p (t + 1) - p t)) (htarget : p (t + 1) =ᵐ[S.μ] pstar (t + 1)) :
    p t =ᵐ[S.μ] S.E t (pstar (t + 1)) - i t := by
  filter_upwards [hfis, S.E_sub hp1 hpi t, S.E_congr htarget t] with ω h1 h2 h3
  rw [Pi.sub_apply, h1, h2, Pi.sub_apply, S.E_of_stronglyMeasurable hp hpi, h3]
  ring

/-- Cochrane (2023), §2.5.1, p. 38 ("A higher interest rate now immediately lowers inflation"),
on a probability space: with the same targets, almost surely a higher rate gives a lower price
level.
Restates `LinearFTMP.pTarget_rate_lowers_price` on a genuine probability space. -/
theorem mPTarget_rate_lowers_price {i' : ℕ → Ω → ℝ} {t : ℕ}
    (hp : StronglyMeasurable[S.𝓕 t] (p t)) (hpi : Integrable (p t) S.μ)
    (hp1 : Integrable (p (t + 1)) S.μ) (hp' : StronglyMeasurable[S.𝓕 t] (p' t))
    (hpi' : Integrable (p' t) S.μ) (hp1' : Integrable (p' (t + 1)) S.μ)
    (hfis : i t =ᵐ[S.μ] S.E t (p (t + 1) - p t))
    (hfis' : i' t =ᵐ[S.μ] S.E t (p' (t + 1) - p' t))
    (htarget : p (t + 1) =ᵐ[S.μ] pstar (t + 1)) (htarget' : p' (t + 1) =ᵐ[S.μ] pstar (t + 1)) :
    ∀ᵐ ω ∂S.μ, i t ω < i' t ω → p' t ω < p t ω := by
  filter_upwards [mPTarget_price S hp hpi hp1 hfis htarget,
    mPTarget_price S hp' hpi' hp1' hfis' htarget'] with ω h1 h2 hlt
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply]
  linarith

/-- Cochrane (2023), §2.5.1, p. 38 ("the fiscal authority will be induced to raise future
surpluses"), on a probability space: with targets `p*_{t+2}` known at `t`, the linear valuation
equation `ΔE_{t+1}(p_{t+1} − p_t) = −ε_{Σs,t+1}` forces `ε_{Σs,t+1} = ΔE_{t+1} i_{t+1}`
almost surely.
Restates `LinearFTMP.pTarget_fiscal_contraction` on a genuine probability space. -/
theorem mPTarget_fiscal_contraction (hp : StronglyAdapted S.𝓕 p)
    (hpi : ∀ t, Integrable (p t) S.μ) (hii : ∀ t, Integrable (i t) S.μ)
    (hfis : ∀ t, i t =ᵐ[S.μ] S.E t (p (t + 1) - p t))
    (htarget : ∀ t, p (t + 1) =ᵐ[S.μ] pstar (t + 1)) {t : ℕ}
    (hstar : StronglyMeasurable[S.𝓕 t] (pstar (t + 2))) (hstari : Integrable (pstar (t + 2)) S.μ)
    (h221 : S.innov t (p (t + 1) - p t) =ᵐ[S.μ] -ε (t + 1)) :
    ε (t + 1) =ᵐ[S.μ] S.innov t (i (t + 1)) := by
  have hp1 := mPTarget_price S (hp (t + 1)) (hpi (t + 1)) (hpi (t + 2)) (hfis (t + 1))
    (htarget (t + 1))
  have hk : S.E (t + 1) (pstar (t + 1 + 1)) = pstar (t + 2) :=
    S.E_of_stronglyMeasurable (hstar.mono (S.𝓕.mono (Nat.le_succ t))) hstari
  rw [hk] at hp1
  filter_upwards [h221, innov_sub' S (hpi (t + 1)) (hpi t) t, innov_congr S hp1 t,
    innov_sub' S hstari (hii (t + 1)) t] with ω h1 h2 h3 h4
  rw [h2, Pi.sub_apply, innov_known S (hp t) (hpi t), Pi.zero_apply, sub_zero, h3, h4,
    Pi.sub_apply, innov_known S hstar hstari, Pi.zero_apply, zero_sub, Pi.neg_apply] at h1
  linarith

/-- Cochrane (2023), §2.5.1, p. 38 ("then we are at a loggerhead"), on a probability space: if
fiscal policy also sets `p_t = p*_t` (targets known at `t`, integrable), the Fisher equation
leaves monetary policy no freedom, `i_t = p*_{t+1} − p*_t` almost surely. -/
theorem mLoggerhead {t : ℕ} (hstar : StronglyMeasurable[S.𝓕 t] (pstar (t + 1)))
    (hstari : Integrable (pstar (t + 1)) S.μ) (hp : StronglyMeasurable[S.𝓕 t] (p t))
    (hpi : Integrable (p t) S.μ) (hp1 : Integrable (p (t + 1)) S.μ)
    (hfis : i t =ᵐ[S.μ] S.E t (p (t + 1) - p t)) (h1 : p t =ᵐ[S.μ] pstar t)
    (h2 : p (t + 1) =ᵐ[S.μ] pstar (t + 1)) : i t =ᵐ[S.μ] pstar (t + 1) - pstar t := by
  filter_upwards [mPTarget_price S hp hpi hp1 hfis h2, h1] with ω e1 e2
  rw [Pi.sub_apply, S.E_of_stronglyMeasurable hstar hstari] at e1
  rw [Pi.sub_apply, ← e2]
  linarith

/-- Cochrane (2023), p. 38 (survey error E6, corrected), on a probability space:
`ΔE_{t+1}(p_{t+1} − p_t) = ΔE_{t+1} p_{t+1}` almost surely (`p_t` known at `t`).
Restates `LinearFTMP.innov_pi_eq_innov_p` on a genuine probability space. -/
theorem mInnov_pi_eq_innov_p {t : ℕ} (hp : StronglyMeasurable[S.𝓕 t] (p t))
    (hpi : Integrable (p t) S.μ) (hp1 : Integrable (p (t + 1)) S.μ) :
    S.innov t (p (t + 1) - p t) =ᵐ[S.μ] S.innov t (p (t + 1)) := by
  filter_upwards [innov_sub' S hp1 hpi t] with ω h
  rw [h, Pi.sub_apply, innov_known S hp hpi, Pi.zero_apply, sub_zero]

/-! ### Figure 2.2: the rule `i_t = θπ_t + u_t` -/

variable {θ η : ℝ}

/-- Cochrane (2023), eq. (2.23), p. 40, on a probability space: the response of the disturbance
`u_{t+1} = η u_t + ε_{i,t+1}` (a.s.) to a monetary shock, `ΔE_{t+1} u_{t+1+j} = ηʲ ε_{i,t+1}`
almost surely.
Restates `LinearFTMP.irf_disturbance` on a genuine probability space. -/
theorem mIrf_disturbance (hu : StronglyAdapted S.𝓕 u) (hui : ∀ t, Integrable (u t) S.μ)
    (hεi : MIsShock S εi) (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1)) (t j : ℕ) :
    S.innov t (u (t + 1 + j)) =ᵐ[S.μ] η ^ j • εi (t + 1) := by
  induction j with
  | zero =>
    filter_upwards [innov_congr S (hd t) t, innov_add' S ((hui t).smul η) (hεi.2.1 t) t,
      innov_smul' S η (u t) t, innov_shock S hεi t] with ω e1 e2 e3 e4
    rw [add_zero, e1, e2, Pi.add_apply, e3, Pi.smul_apply, innov_known S (hu t) (hui t), e4]
    simp
  | succ j ih =>
    have e : t + 1 + (j + 1) = t + 1 + j + 1 := by omega
    have hl := innov_shock_later S hεi t j
    rw [show t + 2 + j = t + 1 + j + 1 by omega] at hl
    rw [e]
    filter_upwards [innov_congr S (hd (t + 1 + j)) t,
      innov_add' S ((hui _).smul η) (hεi.2.1 _) t, innov_smul' S η (u (t + 1 + j)) t, ih, hl]
      with ω e1 e2 e3 e4 e5
    rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, e4, e5]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, pow_succ]
    ring

/-- Cochrane (2023), Figure 2.2 and eq. (2.25), pp. 40–41, on a probability space: impulse
responses of inflation in the rule model, `ΔE_{t+1} π_{t+1+j} = −θʲ ε_{Σs,t+1} + c_j ε_{i,t+1}`
almost surely, `c_j = LinearFTMP.conv θ η j`, for the a.s. solution
`π_{t+1} = θπ_t + u_t − ε_{Σs,t+1}`.
Restates `LinearFTMP.irf_rule` on a genuine probability space. -/
theorem mIrf_rule (hu : StronglyAdapted S.𝓕 u) (hui : ∀ t, Integrable (u t) S.μ)
    (hεi : MIsShock S εi) (hε : MIsShock S ε) (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1))
    (hπ : StronglyAdapted S.𝓕 π) (hπi : ∀ t, Integrable (π t) S.μ)
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] θ • π t + u t - ε (t + 1)) (t j : ℕ) :
    S.innov t (π (t + 1 + j)) =ᵐ[S.μ]
      (-θ ^ j) • ε (t + 1) + LinearFTMP.conv θ η j • εi (t + 1) := by
  induction j with
  | zero =>
    filter_upwards [innov_congr S (h t) t, innov_lin3 S θ (hπi t) (hui t) (hε.2.1 t) t,
      innov_shock S hε t] with ω e1 e2 e3
    rw [add_zero, e1, e2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      innov_known S (hπ t) (hπi t), innov_known S (hu t) (hui t), e3]
    simp [LinearFTMP.conv]
  | succ j ih =>
    have e : t + 1 + (j + 1) = t + 1 + j + 1 := by omega
    have hl := innov_shock_later S hε t j
    rw [show t + 2 + j = t + 1 + j + 1 by omega] at hl
    rw [e]
    filter_upwards [innov_congr S (h (t + 1 + j)) t,
      innov_lin3 S θ (hπi _) (hui _) (hε.2.1 _) t, ih,
      mIrf_disturbance S hu hui hεi hd t j, hl] with ω e1 e2 e3 e4 e5
    rw [e1, e2, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, e3, e4, e5]
    simp only [LinearFTMP.conv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      sub_zero, pow_succ]
    ring

/-- Cochrane (2023), Figure 2.2, p. 41, on a probability space: with the rule `i_t = θπ_t + u_t`
a.s., the rate responses are `ΔE_{t+1} i_{t+1+j} = −θ^{j+1} ε_{Σs,t+1} + c_{j+1} ε_{i,t+1}`
almost surely (inflation follows the rate with a one-period lag).
Restates `LinearFTMP.irf_rule_rate` on a genuine probability space. -/
theorem mIrf_rule_rate (hu : StronglyAdapted S.𝓕 u) (hui : ∀ t, Integrable (u t) S.μ)
    (hεi : MIsShock S εi) (hε : MIsShock S ε) (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1))
    (hπ : StronglyAdapted S.𝓕 π) (hπi : ∀ t, Integrable (π t) S.μ)
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] θ • π t + u t - ε (t + 1))
    (hi : ∀ t, i t =ᵐ[S.μ] θ • π t + u t) (t j : ℕ) :
    S.innov t (i (t + 1 + j)) =ᵐ[S.μ]
      (-θ ^ (j + 1)) • ε (t + 1) + LinearFTMP.conv θ η (j + 1) • εi (t + 1) := by
  filter_upwards [innov_congr S (hi (t + 1 + j)) t,
    innov_add' S ((hπi _).smul θ) (hui _) t, innov_smul' S θ (π (t + 1 + j)) t,
    mIrf_rule S hu hui hεi hε hd hπ hπi h t j, mIrf_disturbance S hu hui hεi hd t j]
    with ω e1 e2 e3 e4 e5
  rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, e4, e5]
  simp only [LinearFTMP.conv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Cochrane (2023), Figure 2.2, top panel, on a probability space: almost surely, where the
monetary shock is `1` and there is no fiscal shock, inflation responds `(θʲ − ηʲ)/(θ − η)` and
the rate `(θ^{j+1} − η^{j+1})/(θ − η)`, at every horizon.
Restates `LinearFTMP.fig22_monetary` on a genuine probability space. -/
theorem mFig22_monetary (hθη : θ ≠ η) (hu : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (hεi : MIsShock S εi) (hε : MIsShock S ε)
    (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1)) (hπ : StronglyAdapted S.𝓕 π)
    (hπi : ∀ t, Integrable (π t) S.μ) (h : ∀ t, π (t + 1) =ᵐ[S.μ] θ • π t + u t - ε (t + 1))
    (hi : ∀ t, i t =ᵐ[S.μ] θ • π t + u t) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, εi (t + 1) ω = 1 → ε (t + 1) ω = 0 → ∀ j,
      S.innov t (π (t + 1 + j)) ω = (θ ^ j - η ^ j) / (θ - η) ∧
      S.innov t (i (t + 1 + j)) ω = (θ ^ (j + 1) - η ^ (j + 1)) / (θ - η) := by
  filter_upwards [ae_all_iff.2 fun j => mIrf_rule S hu hui hεi hε hd hπ hπi h t j,
    ae_all_iff.2 fun j => mIrf_rule_rate S hu hui hεi hε hd hπ hπi h hi t j]
    with ω h1 h2 he1 he0 j
  rw [h1 j, h2 j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he1, he0, LinearFTMP.conv_eq hθη]
  constructor <;> ring

/-- Cochrane (2023), Figure 2.2, bottom panel, on a probability space: almost surely, where the
fiscal shock is `−1` and there is no monetary shock, inflation responds `θʲ` and the rate
`θ^{j+1}`.
Restates `LinearFTMP.fig22_fiscal` on a genuine probability space. -/
theorem mFig22_fiscal (hu : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (hεi : MIsShock S εi) (hε : MIsShock S ε)
    (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1)) (hπ : StronglyAdapted S.𝓕 π)
    (hπi : ∀ t, Integrable (π t) S.μ) (h : ∀ t, π (t + 1) =ᵐ[S.μ] θ • π t + u t - ε (t + 1))
    (hi : ∀ t, i t =ᵐ[S.μ] θ • π t + u t) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, εi (t + 1) ω = 0 → ε (t + 1) ω = -1 → ∀ j,
      S.innov t (π (t + 1 + j)) ω = θ ^ j ∧ S.innov t (i (t + 1 + j)) ω = θ ^ (j + 1) := by
  filter_upwards [ae_all_iff.2 fun j => mIrf_rule S hu hui hεi hε hd hπ hπi h t j,
    ae_all_iff.2 fun j => mIrf_rule_rate S hu hui hεi hε hd hπ hπi h hi t j]
    with ω h1 h2 he0 he1 j
  rw [h1 j, h2 j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he1, he0]
  constructor <;> ring

/-- Cochrane (2023), p. 41 ("fiscal policy alone sets the initial unexpected inflation"), on a
probability space: `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` almost surely, whatever `θ`, `η` and the
monetary shock.
Restates `LinearFTMP.fiscal_sets_impact` on a genuine probability space. -/
theorem mFiscal_sets_impact (hu : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (hεi : MIsShock S εi) (hε : MIsShock S ε)
    (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1)) (hπ : StronglyAdapted S.𝓕 π)
    (hπi : ∀ t, Integrable (π t) S.μ) (h : ∀ t, π (t + 1) =ᵐ[S.μ] θ • π t + u t - ε (t + 1))
    (t : ℕ) : S.innov t (π (t + 1)) =ᵐ[S.μ] -ε (t + 1) := by
  filter_upwards [mIrf_rule S hu hui hεi hε hd hπ hπi h t 0] with ω e
  rw [add_zero] at e
  rw [e]
  simp [LinearFTMP.conv]

/-- Cochrane (2023), p. 41 ("a one-time price level shock, with no further inflation"), on a
probability space: with `θ = 0`, almost surely where there is no monetary shock and the fiscal
shock is `−1`, inflation is `1` on impact and `0` afterwards.
Restates `LinearFTMP.one_time_price_jump` on a genuine probability space. -/
theorem mOne_time_price_jump (hu : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (hεi : MIsShock S εi) (hε : MIsShock S ε)
    (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1)) (hπ : StronglyAdapted S.𝓕 π)
    (hπi : ∀ t, Integrable (π t) S.μ)
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] (0 : ℝ) • π t + u t - ε (t + 1)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, εi (t + 1) ω = 0 → ε (t + 1) ω = -1 → ∀ j,
      S.innov t (π (t + 1 + j)) ω = if j = 0 then 1 else 0 := by
  filter_upwards [ae_all_iff.2 fun j => mIrf_rule S hu hui hεi hε hd hπ hπi h t j]
    with ω h1 he0 he1 j
  rw [h1 j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he1, he0]
  cases j with
  | zero => simp
  | succ j => simp

/-- Cochrane (2023), p. 41 ("Monetary policy could return the price level to its previous
value"), on a probability space: with `θ = 0` and `|η| < 1`, almost surely where the fiscal
shock is `−1` and the monetary shock `−(1 − η)`, the inflation responses sum to zero.
Restates `LinearFTMP.price_level_returns` on a genuine probability space. -/
theorem mPrice_level_returns (hη : |η| < 1) (hu : StronglyAdapted S.𝓕 u)
    (hui : ∀ t, Integrable (u t) S.μ) (hεi : MIsShock S εi) (hε : MIsShock S ε)
    (hd : ∀ t, u (t + 1) =ᵐ[S.μ] η • u t + εi (t + 1)) (hπ : StronglyAdapted S.𝓕 π)
    (hπi : ∀ t, Integrable (π t) S.μ)
    (h : ∀ t, π (t + 1) =ᵐ[S.μ] (0 : ℝ) • π t + u t - ε (t + 1)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, εi (t + 1) ω = -(1 - η) → ε (t + 1) ω = -1 →
      HasSum (fun j => S.innov t (π (t + 1 + j)) ω) 0 := by
  filter_upwards [ae_all_iff.2 fun j => mIrf_rule S hu hui hεi hε hd hπ hπi h t j]
    with ω h1 he0 he1
  have hx : ∀ j, S.innov t (π (t + 1 + j)) ω =
      -(0 : ℝ) ^ j * -1 + LinearFTMP.conv 0 η j * -(1 - η) := by
    intro j
    rw [h1 j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he1, he0]
  have hc : ∀ j, LinearFTMP.conv 0 η (j + 1) = η ^ j := fun j => by simp [LinearFTMP.conv]
  have htail : HasSum (fun j => S.innov t (π (t + 1 + (j + 1))) ω) (-1) := by
    have hg := (hasSum_geometric_of_abs_lt_one hη).mul_left (-(1 - η))
    have h1η : 1 - η ≠ 0 := by
      have := (abs_lt.mp hη).2
      linarith
    have hv : -(1 - η) * (1 - η)⁻¹ = -1 := by
      rw [neg_mul, mul_inv_cancel₀ h1η]
    rw [hv] at hg
    convert hg using 1
    funext j
    rw [hx (j + 1), hc j]
    simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow]
    ring
  have hf0 : S.innov t (π (t + 1 + 0)) ω = 1 := by
    rw [hx 0]
    simp [LinearFTMP.conv]
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [Finset.sum_range_one, hf0, zero_sub]
  exact htail

/-! ### Links to the core versions on finite trees -/

namespace Link

open ExpectationsFiniteTree TreeBridge HouseholdMeasureTVC.Link TidyR5MeasLinear.Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), Figure 2.1, p. 36: on a finite tree the measure-theoretic impact response
gives the core one (`LinearFTMP.irf_peg_impact`) in every state. -/
theorem tree_irf_peg_impact {i ε π : ℕ → Ω' → ℝ} (hi : T.toExpectationSystem.Adapted i)
    (hε : LinearFTMP.IsShock T.toExpectationSystem ε) (h : ∀ t, π (t + 1) = i t - ε (t + 1))
    (t : ℕ) : ExpectationTools.innov T.toExpectationSystem t (π (t + 1)) = -ε (t + 1) := by
  have e := eq_of_ae T (mIrf_peg_impact (treeSystem T) ((tree_adapted_iff T i).mpr hi)
    (fun _ => Integrable.of_finite) ((tree_mIsShock_iff T ε).mpr hε)
    (fun t => Eventually.of_forall fun ω => congrFun (h t) ω) t)
  rwa [tree_innov] at e

/-- Cochrane (2023), Figure 2.2 and eq. (2.25), pp. 40–41: on a finite tree the
measure-theoretic rule responses give the core ones (`LinearFTMP.irf_rule`) in every state. -/
theorem tree_irf_rule {θ η : ℝ} {u εi ε π : ℕ → Ω' → ℝ} (hπ : T.toExpectationSystem.Adapted π)
    (hu : T.toExpectationSystem.Adapted u) (hεi : LinearFTMP.IsShock T.toExpectationSystem εi)
    (hε : LinearFTMP.IsShock T.toExpectationSystem ε) (hd : LinearFTMP.Disturbance η u εi)
    (h : ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1)) (t j : ℕ) :
    ExpectationTools.innov T.toExpectationSystem t (π (t + 1 + j)) =
      (-θ ^ j) • ε (t + 1) + LinearFTMP.conv θ η j • εi (t + 1) := by
  have e := eq_of_ae T (mIrf_rule (treeSystem T) ((tree_adapted_iff T u).mpr hu)
    (fun _ => Integrable.of_finite) ((tree_mIsShock_iff T εi).mpr hεi)
    ((tree_mIsShock_iff T ε).mpr hε) (fun t => Eventually.of_forall fun ω => congrFun (hd t) ω)
    ((tree_adapted_iff T π).mpr hπ) (fun _ => Integrable.of_finite)
    (fun t => Eventually.of_forall fun ω => congrFun (h t) ω) t j)
  rwa [tree_innov] at e

/-- Cochrane (2023), §2.5.1, p. 38: on a finite tree the measure-theoretic price-level-target
formula gives the core one (`LinearFTMP.pTarget_price`) in every state. -/
theorem tree_pTarget_price {i p pstar : ℕ → Ω' → ℝ} {t : ℕ}
    (hp : T.toExpectationSystem.E t (p t) = p t)
    (hfis : i t = T.toExpectationSystem.E t (p (t + 1) - p t))
    (htarget : p (t + 1) = pstar (t + 1)) :
    p t = T.toExpectationSystem.E t (pstar (t + 1)) - i t := by
  have e := eq_of_ae T (mPTarget_price (treeSystem T) (i := i) (pstar := pstar)
    ((sm_iff_known T t (p t)).mpr hp) Integrable.of_finite Integrable.of_finite
    (Eventually.of_forall fun ω => by rw [treeE, ← hfis])
    (Eventually.of_forall fun ω => congrFun htarget ω))
  rwa [treeE] at e

end Link

end Cochrane.IntertemporalModel.TidyR6MeasLinearIRF
