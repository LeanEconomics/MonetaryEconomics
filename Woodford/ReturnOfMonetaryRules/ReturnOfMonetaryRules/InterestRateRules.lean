/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ReturnOfMonetaryRules.Expectations

/-!
# Interest-rate rules

Woodford (2003), *Interest and Prices*, Chapter 1, §4 and §4.1, pp. 37–44.

## Main results

* `WicksellRule` (4.1); `difference_iff_wicksell` (fn. 30, p. 38): adopting the difference
  rule `Δi_t = φ π_t` from `t₀` is equivalent to the Wicksellian rule (4.1) with intercept
  `ī = i_{t₀−1} − φ p_{t₀−1}`, and `wicksell_intercept_eq` pins the intercept down.
* `wicksell_violates_zlb` (fn. 29): (4.1) cannot hold at every price level, since it would
  require negative interest rates.
* `taylorRule` (4.3), `taylorRule_at_target`, `taylorRule_real_rate_at_target`
  (p. 39: `i = 4%` at target, an implied real rate of `2%`) and `taylorPrinciple_iff`
  (p. 40: the real rate rises with inflation iff the inflation coefficient exceeds one).
* `PartialAdjustment` (4.5), `DesiredRate` (4.6) and the long-run response
  `partialAdjustment_longRun`: under the Schur–Cohn condition the funds rate converges to
  `ī + φ_π(π − π̄) + φ_x(1 − γ)x` after a permanent change, so the long-run coefficients are
  `φ_π` and `φ_x(1 − γ)`; `judd_rudebusch_stable` checks the condition at the Table 1.1
  estimates.
* `ForecastDesiredRate` (4.7) and `TargetCriterion` (4.8), Svensson's target criterion.
-/

namespace Woodford.ReturnOfMonetaryRules.InterestRateRules

open Filter Topology

variable {Ω : Type*}

/-! ### The Wicksellian rule and footnote 30 -/

/-- Woodford (2003), eq. (4.1), p. 38: the Wicksellian rule `i_t = ī + φ p_t` holds at date `t`
(`p_t` the log price level). -/
def WicksellRule (ibar φ : ℝ) (i p : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = (fun _ => ibar) + φ • p t

/-- Woodford (2003), eq. (4.2) and fn. 30, p. 38: the difference rule `Δi_t = φ π_t`,
`π_t ≡ Δp_t`, at date `t + 1`. -/
def DifferenceRule (φ : ℝ) (i p : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i (t + 1) - i t = φ • (p (t + 1) - p t)

/-- Woodford (2003), fn. 30, p. 38: a commitment to the difference rule (4.2) from date
`t₀ = s + 1` on is equivalent to the Wicksellian rule (4.1) from date `s = t₀ − 1` on, with
intercept `i_{t₀−1} − φ p_{t₀−1}` (both directions, by telescoping). -/
theorem difference_iff_wicksell (φ : ℝ) (i p : ℕ → Ω → ℝ) (s : ℕ) :
    (∀ t, s ≤ t → DifferenceRule φ i p t) ↔
      ∀ t, s ≤ t → i t = (i s - φ • p s) + φ • p t := by
  constructor
  · intro h t hst
    induction t, hst using Nat.le_induction with
    | base => abel
    | succ t hst ih =>
      have h1 := h t hst
      unfold DifferenceRule at h1
      rw [smul_sub] at h1
      calc i (t + 1) = i t + (φ • p (t + 1) - φ • p t) := by rw [← h1]; abel
        _ = _ := by rw [ih]; abel
  · intro h t hst
    unfold DifferenceRule
    rw [h (t + 1) (Nat.le_succ_of_le hst), h t hst, smul_sub]
    abel

/-- Woodford (2003), fn. 30, p. 38: if the Wicksellian rule holds from date `s = t₀ − 1` on with
some intercept `ī`, that intercept is `i_{t₀−1} − φ p_{t₀−1}` (in every state). -/
theorem wicksell_intercept_eq {ibar φ : ℝ} {i p : ℕ → Ω → ℝ} {s : ℕ}
    (h : WicksellRule ibar φ i p s) : (fun _ => ibar) = i s - φ • p s := by
  unfold WicksellRule at h
  rw [h]; abel

/-- Woodford (2003), fn. 30, p. 38: a Wicksellian rule with any constant intercept implies the
difference rule at every date. -/
theorem wicksell_imp_difference {ibar φ : ℝ} {i p : ℕ → Ω → ℝ}
    (h : ∀ t, WicksellRule ibar φ i p t) (t : ℕ) : DifferenceRule φ i p t := by
  unfold DifferenceRule
  rw [h (t + 1), h t, smul_sub]
  abel

/-- Woodford (2003), fn. 29, p. 38: the log-linear rule (4.1) with `φ ≠ 0` cannot be maintained
at all price levels, since some price level would call for a negative nominal rate. -/
theorem wicksell_violates_zlb (ibar : ℝ) {φ : ℝ} (hφ : φ ≠ 0) : ∃ p : ℝ, ibar + φ * p < 0 :=
  ⟨-(ibar + 1) / φ, by field_simp; linarith⟩

/-! ### The Taylor rule (4.3) and reaction functions (4.4) -/

/-- Woodford (2003), eq. (4.4), p. 40: a reaction function `i = ī + φ_π(π − π̄) + φ_x x`
with inflation target `piStar` (the book's `π̄`). -/
def reactionFn (ibar φπ φx piStar infl x : ℝ) : ℝ := ibar + φπ * (infl - piStar) + φx * x

/-- Woodford (2003), eq. (4.3), p. 39: the Taylor (1993) rule
`i = 0.04 + 1.5(π̄ − 0.02) + 0.5(y − y^p)`, as a function of inflation and the output gap. -/
noncomputable def taylorRule (infl gap : ℝ) : ℝ := 0.04 + 1.5 * (infl - 0.02) + 0.5 * gap

/-- Woodford (2003), eqs. (4.3)–(4.4), pp. 39–40: the Taylor rule is the reaction function with
`ī = 4%`, `φ_π = 1.5`, `φ_x = 0.5` and inflation target `2%`. -/
theorem taylorRule_eq_reactionFn (infl gap : ℝ) :
    taylorRule infl gap = reactionFn 0.04 1.5 0.5 0.02 infl gap := rfl

/-- Woodford (2003), p. 39: with inflation at its 2% target and a zero output gap, the Taylor
rule sets the funds rate at 4%. -/
theorem taylorRule_at_target : taylorRule 0.02 0 = 0.04 := by
  norm_num [taylorRule]

/-- Woodford (2003), p. 39: the implied long-run real funds rate at target is 2%. -/
theorem taylorRule_real_rate_at_target : taylorRule 0.02 0 - 0.02 = 0.02 := by
  norm_num [taylorRule]

/-- Woodford (2003), p. 40 (the Taylor principle): the real rate `i − π` implied by a reaction
function is strictly increasing in inflation if and only if `φ_π > 1`. -/
theorem taylorPrinciple_iff (ibar φπ φx piStar x : ℝ) :
    StrictMono (fun infl => reactionFn ibar φπ φx piStar infl x - infl) ↔ 1 < φπ := by
  constructor
  · intro h
    have := h (show (0 : ℝ) < 1 by norm_num)
    simp only [reactionFn] at this
    linarith
  · intro h a b hab
    simp only [reactionFn]
    nlinarith

/-- Woodford (2003), p. 40: the Taylor rule satisfies the Taylor principle — inflation `Δ` above
target raises the real funds rate by `0.5 Δ`. -/
theorem taylorRule_real_rate_rises (infl gap Δ : ℝ) :
    taylorRule (infl + Δ) gap - (infl + Δ) = taylorRule infl gap - infl + 0.5 * Δ := by
  unfold taylorRule; ring

/-- Woodford (2003), p. 40: Goodhart's (1992) rule `i = 0.03 + 1.5 π̄` is a reaction function of
the form (4.4) with `φ_π = 1.5 > 1` and no output response, for any inflation target. -/
theorem goodhartRule_eq_reactionFn (piStar infl x : ℝ) :
    (0.03 : ℝ) + 1.5 * infl = reactionFn (0.03 + 1.5 * piStar) 1.5 0 piStar infl x := by
  unfold reactionFn; ring

/-- Woodford (2003), Table 1.1, p. 41: the Taylor (1999c) and Clarida et al. (2000) inflation
coefficients violate the Taylor principle before 1979 and satisfy it afterwards, while
Orphanides's (2003) real-time estimates exceed one in both periods. -/
theorem table11_taylor_principle :
    (0.81 : ℝ) < 1 ∧ (1 : ℝ) < 1.53 ∧ (0.83 : ℝ) < 1 ∧ (1 : ℝ) < 2.15 ∧
      (1 : ℝ) < 1.49 ∧ (1 : ℝ) < 1.89 := by
  norm_num

/-! ### Partial adjustment (4.5)–(4.6) -/

/-- Woodford (2003), eq. (4.5), p. 41: the funds rate follows the partial-adjustment dynamics
`i_t = (1 − ρ₁) ī_t + ρ₁ i_{t−1} + ρ₂(i_{t−1} − i_{t−2})` towards the desired rate `ibarT`
(stated at date `t + 2`). -/
def PartialAdjustment (ρ₁ ρ₂ : ℝ) (i ibarT : ℕ → ℝ) : Prop :=
  ∀ t, i (t + 2) = (1 - ρ₁) * ibarT (t + 2) + ρ₁ * i (t + 1) + ρ₂ * (i (t + 1) - i t)

/-- Woodford (2003), eq. (4.6), p. 41: the desired funds rate
`ī_t = ī + φ_π(π̄_t − π̄) + φ_x(x_t − γ x_{t−1})` (stated at date `t + 1`; `piStar` is the
book's `π̄`). -/
def DesiredRate (ibar φπ φx γ piStar : ℝ) (infl x ibarT : ℕ → ℝ) : Prop :=
  ∀ t, ibarT (t + 1) = ibar + φπ * (infl (t + 1) - piStar) + φx * (x (t + 1) - γ * x t)

/-- Woodford (2003), (4.5), p. 41: a solution of the homogeneous second-order recursion
`d_{k+2} = T d_{k+1} − D d_k` is `d_{k+2} = p_{k+1} d₁ − D p_k d₀`, with `p` the
Cayley–Hamilton sequence `chSeq`. -/
theorem recursion_eq_chSeq {T D : ℝ} {d : ℕ → ℝ}
    (hd : ∀ k, d (k + 2) = T * d (k + 1) - D * d k) (k : ℕ) :
    d (k + 2) = chSeq T D (k + 1) * d 1 - D * chSeq T D k * d 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => rw [hd 0]; simp [chSeq]
    | 1, _ => rw [hd 1, hd 0]; simp [chSeq]; ring
    | k + 2, ih =>
      rw [hd (k + 2), ih (k + 1) (by omega), ih k (by omega)]
      simp only [chSeq]
      ring

/-- Woodford (2003), (4.5), p. 41: if the desired rate is constant at `c` from date `T₀` on and
the partial-adjustment roots lie inside the unit circle (`SchurStable (ρ₁ + ρ₂) ρ₂`), the funds
rate converges to `c`: partial adjustment changes the dynamics but not the long-run level. -/
theorem partialAdjustment_tendsto {ρ₁ ρ₂ c : ℝ} {i ibarT : ℕ → ℝ}
    (hS : SchurStable (ρ₁ + ρ₂) ρ₂) (hpa : PartialAdjustment ρ₁ ρ₂ i ibarT) {T₀ : ℕ}
    (hc : ∀ t, T₀ ≤ t → ibarT t = c) : Tendsto i atTop (𝓝 c) := by
  set d : ℕ → ℝ := fun k => i (k + T₀) - c with hd_def
  have hd : ∀ k, d (k + 2) = (ρ₁ + ρ₂) * d (k + 1) - ρ₂ * d k := by
    intro k
    have h := hpa (k + T₀)
    rw [hc (k + T₀ + 2) (by omega)] at h
    simp only [hd_def, show k + 2 + T₀ = k + T₀ + 2 by omega,
      show k + 1 + T₀ = k + T₀ + 1 by omega, h]
    ring
  have h1 : Tendsto (fun k => chSeq (ρ₁ + ρ₂) ρ₂ (k + 1)) atTop (𝓝 0) :=
    (tendsto_chSeq hS).comp (tendsto_add_atTop_nat 1)
  have h0 := tendsto_chSeq hS
  have hlim : Tendsto (fun k => d (k + 2)) atTop (𝓝 0) := by
    have := (h1.mul_const (d 1)).sub ((h0.const_mul ρ₂).mul_const (d 0))
    simp only [zero_mul, mul_zero, sub_zero] at this
    refine this.congr fun k => ?_
    rw [recursion_eq_chSeq hd k, mul_assoc]
  have hd0 : Tendsto d atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 2).mp hlim
  have hi : Tendsto (fun k => i (k + T₀)) atTop (𝓝 c) := by
    have := hd0.add_const c
    simp only [zero_add] at this
    refine this.congr fun k => ?_
    simp [hd_def]
  exact (tendsto_add_atTop_iff_nat T₀).mp hi

/-- Woodford (2003), (4.5)–(4.6), p. 41: **long-run responses.** After a permanent change that
holds inflation at `πL` and the output gap at `xL` from date `T₀` on, the funds rate converges to
`ī + φ_π(πL − π̄) + φ_x(1 − γ) xL`. The long-run inflation coefficient is `φ_π` and the long-run
output-gap coefficient is `φ_x(1 − γ)`, whatever the adjustment speeds `ρ₁, ρ₂`. -/
theorem partialAdjustment_longRun {ρ₁ ρ₂ ibar φπ φx γ piStar πL xL : ℝ}
    {i ibarT infl x : ℕ → ℝ} (hS : SchurStable (ρ₁ + ρ₂) ρ₂)
    (hpa : PartialAdjustment ρ₁ ρ₂ i ibarT) (hdes : DesiredRate ibar φπ φx γ piStar infl x ibarT)
    {T₀ : ℕ} (hπ : ∀ t, T₀ ≤ t → infl t = πL) (hx : ∀ t, T₀ ≤ t → x t = xL) :
    Tendsto i atTop (𝓝 (ibar + φπ * (πL - piStar) + φx * (1 - γ) * xL)) := by
  refine partialAdjustment_tendsto hS hpa (T₀ := T₀ + 1) fun t ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [hdes s, hπ (s + 1) (by omega), hx (s + 1) (by omega), hx s (by omega)]
  ring

/-- Woodford (2003), (4.5), p. 41: with `ρ₁ ≠ 1`, a constant funds rate `k` is consistent
with partial adjustment towards a constant desired rate `c` iff `k = c`. -/
theorem partialAdjustment_const_iff {ρ₁ ρ₂ k c : ℝ} (hρ : ρ₁ ≠ 1) :
    PartialAdjustment ρ₁ ρ₂ (fun _ => k) (fun _ => c) ↔ k = c := by
  constructor
  · intro h
    have h0 := h 0
    have : (1 - ρ₁) * (k - c) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (by linarith) hρ
    · linarith
  · rintro rfl t
    ring

/-- Woodford (2003), Table 1.1, p. 41: the Judd–Rudebusch partial-adjustment estimates
(Greenspan: `ρ₁ = 0.72`, `ρ₂ = 0.43`; Volcker: `ρ₁ = 0.56`, `ρ₂ = 0`) satisfy the Schur–Cohn
condition, so `partialAdjustment_longRun` applies to them. -/
theorem judd_rudebusch_stable :
    SchurStable (0.72 + 0.43) 0.43 ∧ SchurStable (0.56 + 0) 0 := by
  unfold SchurStable
  norm_num [abs_of_pos]

/-! ### Forecast-based rules and target criteria (4.7)–(4.8) -/

/-- Woodford (2003), eq. (4.7), p. 42: the Clarida–Galí–Gertler forecast-based desired rate
`ī_t = ī + φ_π E_t[π_{t+1} − π̄] + φ_x E_t x_t`. -/
def ForecastDesiredRate (𝔼 : ExpectationSystem Ω) (ibar φπ φx piStar : ℝ)
    (infl x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ibar) + φπ • (𝔼.E t (infl (t + 1)) - fun _ => piStar) + φx • 𝔼.E t (x t)

/-- Woodford (2003), eq. (4.8), p. 44: Svensson's flexible inflation-targeting criterion
`E_t π_{t+j} + λ E_t x_{t+k} = π̄` holds at date `t` (`lam` is the book's `λ > 0`). -/
def TargetCriterion (𝔼 : ExpectationSystem Ω) (piStar lam : ℝ) (j k : ℕ)
    (infl x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  𝔼.E t (infl (t + j)) + lam • 𝔼.E t (x (t + k)) = fun _ => piStar

/-- Woodford (2003), eq. (4.8), p. 44: under perfect foresight the target criterion says
`π_{t+j} + λ x_{t+k} = π̄`. -/
theorem targetCriterion_perfectForesight (piStar lam : ℝ) (j k : ℕ)
    (infl x : ℕ → Unit → ℝ) (t : ℕ) :
    TargetCriterion perfectForesight piStar lam j k infl x t ↔
      infl (t + j) () + lam * x (t + k) () = piStar := by
  unfold TargetCriterion
  have hE : ∀ s (y : Unit → ℝ), perfectForesight.E s y = y := fun _ _ => rfl
  constructor
  · intro h
    simpa [hE] using congrFun h ()
  · intro h
    funext u
    simpa [hE] using h

/-- Woodford (2003), eq. (4.8), p. 44: with `λ > 0` the criterion trades off the two forecasts —
a projected positive output gap requires projected inflation below target. -/
theorem targetCriterion_tradeoff {𝔼 : ExpectationSystem Ω} {piStar lam : ℝ} {j k : ℕ}
    {infl x : ℕ → Ω → ℝ} {t : ℕ} (h : TargetCriterion 𝔼 piStar lam j k infl x t)
    (hlam : 0 < lam) {ω : Ω} (hx : 0 < 𝔼.E t (x (t + k)) ω) :
    𝔼.E t (infl (t + j)) ω < piStar := by
  have := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  nlinarith

end Woodford.ReturnOfMonetaryRules.InterestRateRules
