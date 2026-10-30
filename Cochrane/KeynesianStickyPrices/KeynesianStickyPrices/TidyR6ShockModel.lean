/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6HouseholdPref
import KeynesianStickyPrices.TidyR6ShockPC
import KeynesianStickyPrices.TidyR6DerivedModel

/-!
# (17.15)–(17.17) with genuine preference and markup shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4, p. 407 ("We can
write `u_{x,t} = −σu_{r,t}` to interpret the IS disturbance in units of an interest rate
distortion"), and Chapter 5, §5.1, p. 119 ("IS shocks to (5.1) can be formalized as discount
rate shocks"; "Phillips curve shocks, often called 'marginal cost' shocks").

The economy of TidyR6DerivedModel with two exogenous shocks, adapted and bounded:
* a **preference shock** `ξ_t = e^{ζ_t}` multiplying the utility of consumption (household of
  TidyR6HouseholdPref); `u_{r,t} = E_tζ_{t+1} − ζ_t` is the implied discount-rate shock;
* a **markup shock** `μ_t`: a stochastic sales tax `1 − e^{−μ_t}` (rebated lump sum through
  the household's taxes), raising the desired markup to `e^{μ_t}ε/(ε − 1)`.
The price setter values its after-tax revenue at the household's marginal utility of income
`ξ_tu′(C_t)`, so its data are `TidyR6ShockPC.yeoDataM` with `ν = μ − ζ` (`yeoDataM_fst_eq`).

## Main results

* `ISM_piZ_iff`, `IS_of_optimalZ`, `optimal_of_ISZ`, `optimal_iff_ISZ`: the household with the
  preference shock is optimal iff (17.15) holds with `u_{x,t} = −σu_{r,t} + σ·(second order)`
  (`uxZ`): the discount-rate shock in units of an interest-rate distortion, exactly as the book
  writes it, plus the explicit remainder. The proof reduces the weighted Euler equation to the
  unweighted one at the shadow price level `P_te^{−ζ_t}` (`price_piZ`).
* `model_of_eqmZ` (necessity, the price setter optimal among all plans), `eqm_iff_modelZ`
  (necessity and sufficiency, the price setter optimal in its concavity region): equilibria are
  exactly the solutions of (17.15)–(17.17) with
  `u_x = −σ(E_tζ_{t+1} − ζ_t) + rem_x` and `u_π = κ̃(μ_t − ζ_t) + rem_π`.
* `Tree.eqm_iff_modelZ`: on a finite tree, the project's `FullModel.Model` with these
  disturbances.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6ShockModel

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6HouseholdMeasureTVC TidyR6EulerIS TidyR6PriceSetting
open TidyR6Rotemberg TidyR6RotembergPC TidyR6ShockPC TidyR6HouseholdPref TidyR6DerivedModel

variable {Ω : Type*}

/-- Cochrane (2023), p. 407: inflation net of the preference-shock growth,
`π̃_{t+1} = π_{t+1} − (ζ_{t+1} − ζ_t)` (`π̃_0 = π_0`), the inflation of the shadow price level
`P_te^{−ζ_t}`. -/
def piZ (π ζ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π 0
  | t + 1 => fun ω => π (t + 1) ω - ζ (t + 1) ω + ζ t ω

/-- Cochrane (2023), p. 407: the shadow log price level is `p_t − ζ_t`. -/
theorem logPrice_piZ (pm : Ω → ℝ) (π ζ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    logPrice (fun ω => pm ω - ζ 0 ω) (piZ π ζ) t ω = logPrice pm π t ω - ζ t ω := by
  induction t with
  | zero => simp [logPrice, piZ]; ring
  | succ n ih =>
    rw [logPrice_succ, logPrice_succ, ih]
    simp only [piZ]
    ring

/-- Cochrane (2023), p. 407: the shadow price level `P_te^{−ζ_t}`. -/
theorem price_piZ (pm : Ω → ℝ) (π ζ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    price (fun ω => pm ω - ζ 0 ω) (piZ π ζ) t ω = price pm π t ω * Real.exp (-ζ t ω) := by
  simp only [price]
  rw [logPrice_piZ, sub_eq_add_neg, Real.exp_add]

/-- Cochrane (2023), p. 119: the weighted marginal utility of a dollar is the unweighted one at
the shadow price, `e^{ζ_t}u′(C_t)/P_t = u′(C_t)/(P_te^{−ζ_t})`. -/
theorem weighted_eq (pm : Ω → ℝ) (π ζ : ℕ → Ω → ℝ) (u' : ℝ → ℝ) (C : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : Real.exp (ζ t ω) * u' (C t ω) / price pm π t ω =
      u' (C t ω) / price (fun ω => pm ω - ζ 0 ω) (piZ π ζ) t ω := by
  rw [price_piZ, Real.exp_neg]
  have := Real.exp_pos (ζ t ω)
  have : 0 < price pm π t ω := Real.exp_pos _
  field_simp

variable [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 407: regularity carries over to the shadow price level. -/
theorem logRegular_piZ {x i π ζ : ℕ → Ω → ℝ} {pm : Ω → ℝ} (h : LogRegular S x i π pm)
    (hζ : StronglyAdapted S.𝓕 ζ) (hζb : ∀ t, BddAt S (ζ t)) :
    LogRegular S x i (piZ π ζ) (fun ω => pm ω - ζ 0 ω) := by
  obtain ⟨hx, hi, hπ, hpm, hxb, hib, hπb, hpmb⟩ := h
  refine ⟨hx, hi, fun t => ?_, hpm.sub (hζ 0), hxb, hib, fun t => ?_, ?_⟩
  · cases t with
    | zero => exact hπ 0
    | succ n =>
      exact ((hπ (n + 1)).sub (hζ (n + 1))).add ((hζ n).mono (S.𝓕.mono (Nat.le_succ n)))
  · cases t with
    | zero => exact hπb 0
    | succ n =>
      have := ((hπb (n + 1)).add (hζb (n + 1)).neg).add (hζb n)
      simpa [piZ, sub_eq_add_neg] using this
  · have := hpmb.add (hζb 0).neg
    simpa [sub_eq_add_neg] using this

variable (S) in
/-- Cochrane (2023), eq. (17.15), p. 407: the IS disturbance with a preference shock,
`u_{x,t} = −σ(E_tζ_{t+1} − ζ_t) − σE_t[expRem z̃_{t+1}]` with `z̃` the log return including the
preference-shock growth. -/
noncomputable def uxZ (γ : ℝ) (ζ i x π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => -γ⁻¹ * (S.E t (ζ (t + 1)) ω - ζ t ω) + isRem S γ i x (piZ π ζ) t ω

/-- Cochrane (2023), eq. (17.15), p. 407: the IS curve at the shadow price level (real rate
`i_t − E_tπ̃_{t+1}`) is the IS curve at the actual price level with the preference-shock
disturbance `uxZ`. -/
theorem ISM_piZ_iff {γ : ℝ} {ζ i x π : ℕ → Ω → ℝ} {t : ℕ} (hζt : StronglyMeasurable[S.𝓕 t] (ζ t))
    (hζi : Integrable (ζ t) S.μ) (hζ1 : Integrable (ζ (t + 1)) S.μ)
    (hπ1 : Integrable (π (t + 1)) S.μ) :
    ISM S γ⁻¹ (isRem S γ i x (piZ π ζ)) (realRate S i (piZ π ζ)) x t ↔
      ISM S γ⁻¹ (uxZ S γ ζ i x π) (realRate S i π) x t := by
  have e : piZ π ζ (t + 1) = π (t + 1) - ζ (t + 1) + ζ t := by
    funext ω
    simp [piZ]
  have hk : S.E t (ζ t) = ζ t := S.E_of_stronglyMeasurable hζt hζi
  have hE : S.E t (piZ π ζ (t + 1)) =ᵐ[S.μ]
      fun ω => S.E t (π (t + 1)) ω - S.E t (ζ (t + 1)) ω + ζ t ω := by
    rw [e]
    filter_upwards [S.E_add (hπ1.sub hζ1) hζi t, S.E_sub hπ1 hζ1 t] with ω h1 h2
    rw [h1, Pi.add_apply, h2, Pi.sub_apply, hk]
  unfold ISM
  constructor
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, realRate, uxZ] at h1 ⊢
    rw [h2] at h1
    linear_combination h1
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, realRate, uxZ] at h1 ⊢
    rw [h2]
    linear_combination h1

/-! ### The household with the preference shock -/

/-- Cochrane (2023), p. 119: the preference weights `e^{ζ_t}` are adapted. -/
theorem expZ_adapted {ζ : ℕ → Ω → ℝ} (hζ : StronglyAdapted S.𝓕 ζ) :
    StronglyAdapted S.𝓕 (fun t ω => Real.exp (ζ t ω)) := fun t =>
  (Real.continuous_exp.measurable.comp (hζ t).measurable).stronglyMeasurable

/-- Cochrane (2023), p. 119: the weighted Euler equation of the household with the preference
shock is the unweighted Euler equation at the shadow price level. -/
theorem weighted_euler_iff {β : ℝ} {u' : ℝ → ℝ} {ζ i π C : ℕ → Ω → ℝ} {pm : Ω → ℝ} (t : ℕ) :
    ((fun ω => bondPrice β i t ω * (Real.exp (ζ t ω) * u' (C t ω) / price pm π t ω)) =ᵐ[S.μ]
        β • S.E t (fun ω => Real.exp (ζ (t + 1) ω) * u' (C (t + 1) ω) /
          price pm π (t + 1) ω)) ↔
      ((fun ω => bondPrice β i t ω * (u' (C t ω) /
          price (fun ω => pm ω - ζ 0 ω) (piZ π ζ) t ω)) =ᵐ[S.μ]
        β • S.E t (fun ω => u' (C (t + 1) ω) /
          price (fun ω => pm ω - ζ 0 ω) (piZ π ζ) (t + 1) ω)) := by
  simp only [weighted_eq]

/-- Cochrane (2023), eq. (17.15), p. 407 and p. 119, **necessity with a preference shock**: if
consuming output is optimal for the household with preference weights `e^{ζ_t}` (`ζ` adapted and
essentially bounded at every date) and it holds bonds at `t`, the IS curve holds at `t` with the
disturbance `uxZ = −σ(E_tζ_{t+1} − ζ_t) + remainder`. -/
theorem IS_of_optimalZ {β γ a Ybar y : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b ζ : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hζ : StronglyAdapted S.𝓕 ζ) (hζb : ∀ t, BddAt S (ζ t))
    (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hopt : OptimalP S β y u (fun t ω => Real.exp (ζ t ω)) (price pm π) s (bondPrice β i) b₀
      (outp Ybar x) b) {t : ℕ} (hb : ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) :
    ISM S γ⁻¹ (uxZ S γ ζ i x π) (realRate S i π) x t := by
  have hw := euler_of_pos_w hβ hu hu'c hopt (expZ_adapted hζ) (price_adapted h)
    (fun _ => Eventually.of_forall fun _ => Real.exp_pos _) (bondPrice_sm h β t)
    (eulerRegular_of h β Ybar t) (BddAt.comp Real.continuous_exp (hζb t))
    (BddAt.comp Real.continuous_exp (hζb (t + 1))) hb
  have h2 := (euler_iff_IS hβ hγ hY hu'c hu' (logRegular_piZ h hζ hζb) hfl t).1
    ((weighted_euler_iff t).1 hw)
  exact (ISM_piZ_iff (hζ t) (integrable_of_reg hζ hζb t) (integrable_of_reg hζ hζb (t + 1))
    (integrable_of_reg h.2.2.1 h.2.2.2.2.2.2.1 (t + 1))).1 h2

/-- Cochrane (2023), eq. (17.15), p. 407 and p. 119, **sufficiency with a preference shock**: a
feasible plan consuming output, with admissible felicity, concave increasing CRRA utility, the
IS curve with the disturbance `uxZ` at every date, integrable weighted bond positions and the
transversality condition `β^N E[e^{ζ_N}u′(Y_N)B_{N−1}/P_N] → 0`, is optimal. -/
theorem optimal_of_ISZ {β γ a Ybar y : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b ζ : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hζ : StronglyAdapted S.𝓕 ζ) (hζb : ∀ t, BddAt S (ζ t))
    (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hfeas : Feasible S y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible S β (fun z => z) (felic (fun t ω => Real.exp (ζ t ω)) u (outp Ybar x)))
    (hWb : ∀ n, Integrable (fun ω => Real.exp (ζ n ω) * u' (outp Ybar x n ω) * b n ω /
      price pm π n ω) S.μ)
    (hIS : ∀ t, ISM S γ⁻¹ (uxZ S γ ζ i x π) (realRate S i π) x t)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, Real.exp (ζ N ω) * u' (outp Ybar x N ω) * b N ω /
      price pm π N ω ∂S.μ) atTop (𝓝 0)) :
    OptimalP S β y u (fun t ω => Real.exp (ζ t ω)) (price pm π) s (bondPrice β i) b₀
      (outp Ybar x) b := by
  have hreg := logRegular_piZ h hζ hζb
  refine optimal_of_euler_tvc_w hβ hu hconc hmono
    (fun _ => Eventually.of_forall fun _ => (Real.exp_pos _).le) hfeas hadm
    (fun _ => Eventually.of_forall fun _ => Real.exp_pos _) (fun n => ?_) hWb (fun n => ?_) htvc
  · have e : (fun ω => Real.exp (ζ n ω) * u' (outp Ybar x n ω) / price pm π n ω) =
        fun ω => u' (outp Ybar x n ω) / price (fun ω => pm ω - ζ 0 ω) (piZ π ζ) n ω :=
      funext fun ω => weighted_eq pm π ζ u' (outp Ybar x) n ω
    rw [e]
    exact margUtil_integrable_at hreg hu'c β Ybar n
  · have h1 := (ISM_piZ_iff (hζ n) (integrable_of_reg hζ hζb n)
      (integrable_of_reg hζ hζb (n + 1)) (integrable_of_reg h.2.2.1 h.2.2.2.2.2.2.1 (n + 1))).2
      (hIS n)
    have h2 := (weighted_euler_iff n).2 ((euler_iff_IS hβ hγ hY hu'c hu' hreg hfl n).2 h1)
    filter_upwards [h2] with ω hω
    simpa using hω

/-- Cochrane (2023), eq. (17.15), p. 407 and p. 119: under the hypotheses of both directions
(bonds held at every date), consuming output is optimal for the household with the preference
shock iff the IS curve holds at every date with `u_x = uxZ`. -/
theorem optimal_iff_ISZ {β γ a Ybar y : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b ζ : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hζ : StronglyAdapted S.𝓕 ζ) (hζb : ∀ t, BddAt S (ζ t))
    (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hfeas : Feasible S y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible S β (fun z => z) (felic (fun t ω => Real.exp (ζ t ω)) u (outp Ybar x)))
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω)
    (hWb : ∀ n, Integrable (fun ω => Real.exp (ζ n ω) * u' (outp Ybar x n ω) * b n ω /
      price pm π n ω) S.μ)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, Real.exp (ζ N ω) * u' (outp Ybar x N ω) * b N ω /
      price pm π N ω ∂S.μ) atTop (𝓝 0)) :
    OptimalP S β y u (fun t ω => Real.exp (ζ t ω)) (price pm π) s (bondPrice β i) b₀
        (outp Ybar x) b ↔ ∀ t, ISM S γ⁻¹ (uxZ S γ ζ i x π) (realRate S i π) x t :=
  ⟨fun hopt t => IS_of_optimalZ hβ hγ hY hu hu'c hu' h hζ hζb hfl hopt (hb t),
    fun hIS => optimal_of_ISZ hβ hγ hY hu hu'c hconc hmono hu' h hζ hζb hfl hfeas hadm hWb hIS
      htvc⟩

/-! ### The model with shocks -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 119: the price setter values its after-tax revenue at the household's
marginal utility of income: `A_t = e^{ζ_t}u′(Y_t)Y_te^{−μ_t}`, so its data are `yeoDataM` with
`ν = μ − ζ`. -/
theorem yeoDataM_fst_eq {γ a ϕ Ybar : ℝ} (hY : 0 < Ybar) {u' : ℝ → ℝ}
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {μ ζ x π : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : a ≤ outp Ybar x t ω) :
    (yeoDataM γ ϕ Ybar (fun t ω => μ t ω - ζ t ω) x π t ω).1 =
      Real.exp (ζ t ω) * u' (outp Ybar x t ω) * outp Ybar x t ω * Real.exp (-μ t ω) := by
  have h0 := yeoData_fst_eq (ϕ := ϕ) (π := π) hY hu' h
  simp only [yeoData] at h0
  simp only [yeoDataM]
  rw [mul_assoc (Real.exp (ζ t ω)), ← h0, show (1 - γ) * x t ω - (μ t ω - ζ t ω) =
    (1 - γ) * x t ω + (ζ t ω + -μ t ω) by ring, Real.exp_add, Real.exp_add]
  ring

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, with preference and markup shocks,
**necessity**: if the household (preference weights `e^{ζ}`) and the price setter (sales tax
`1 − e^{−μ}`, among all plans) are optimal and bonds are held, then (17.15)–(17.17) hold at every
date with `u_x = uxZ = −σ(E_tζ_{t+1} − ζ_t) + rem` and `u_π = uPiM = κ̃(μ_t − ζ_t) + rem`. -/
theorem model_of_eqmZ {β γ a Ybar y ε φ ϕ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    (hφ : φ ≠ 0) (hϕ : 1 + ϕ ≠ 0) (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b ζ μ : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hζ : StronglyAdapted S.𝓕 ζ) (hζb : ∀ t, BddAt S (ζ t))
    (hμ : StronglyAdapted S.𝓕 μ) (hμb : ∀ t, BddAt S (μ t))
    (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hhh : OptimalP S β y u (fun t ω => Real.exp (ζ t ω)) (price pm π) s (bondPrice β i) b₀
      (outp Ybar x) b)
    (hfirm : OptimalIn S (Plan S) β (rotPay ε (ε * (1 + ϕ)) φ)
      (yeoDataM γ ϕ Ybar (fun t ω => μ t ω - ζ t ω) x π) (fun _ => 0) zeroPlan)
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) :
    ModelM S γ⁻¹ β (kappaT ε φ γ Ybar * (γ + ϕ)) (uxZ S γ ζ i x π)
      (uPiM S β (kappaT ε φ γ Ybar) γ ϕ (fun t ω => μ t ω - ζ t ω) x π) i (realRate S i π)
      x π := fun t =>
  ⟨IS_of_optimalZ hβ hγ hY hu hu'c hu' h hζ hζb hfl hhh (hb t), fisherM_realRate S i π t,
    PC_of_optimalM hβ hφ hϕ hss (fun t => (hμ t).sub (hζ t)) h.1 h.2.2.1
      (fun t => (hμb t).add (hζb t).neg) h.2.2.2.2.1 h.2.2.2.2.2.2.1 hfirm t⟩

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, with preference and markup shocks,
**necessity and sufficiency**: under the regularity of `TidyR6DerivedModel.eqm_iff_model` (with
`ζ`, `μ` adapted and uniformly bounded, the margin conditions stated with `ν = μ − ζ`, and the
household's weighted admissibility, integrability and transversality conditions), the household
and the price setter (within its concavity region) are optimal iff (17.15)–(17.17) hold at every
date with `u_x = uxZ` and `u_π = uPiM` with `ν = μ − ζ`. -/
theorem eqm_iff_modelZ {β γ a Ybar y ε φ ϕ m : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hε : 1 < ε) (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (hY : 0 < Ybar) (hm : 0 < m)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b ζ μ : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hζ : StronglyAdapted S.𝓕 ζ) (hμ : StronglyAdapted S.𝓕 μ)
    (hL : ∃ L, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L ∧ |ζ t ω| ≤ L ∧ |μ t ω| ≤ L)
    (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hmx : ∀ t, ∀ᵐ ω ∂S.μ, (ε - 1) * Real.exp m ≤
      ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω + (μ t ω - ζ t ω)))
    (hmπ : ∀ t, ∀ᵐ ω ∂S.μ, Real.exp m / 2 ≤ Real.exp (π t ω))
    (hfeas : Feasible S y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible S β (fun z => z) (felic (fun t ω => Real.exp (ζ t ω)) u (outp Ybar x)))
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω)
    (hWb : ∀ n, Integrable (fun ω => Real.exp (ζ n ω) * u' (outp Ybar x n ω) * b n ω /
      price pm π n ω) S.μ)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, Real.exp (ζ N ω) * u' (outp Ybar x N ω) * b N ω /
      price pm π N ω ∂S.μ) atTop (𝓝 0)) :
    (OptimalP S β y u (fun t ω => Real.exp (ζ t ω)) (price pm π) s (bondPrice β i) b₀
        (outp Ybar x) b ∧
      OptimalIn S (RPlan S ε (ε * (1 + ϕ)) (yeoDataM γ ϕ Ybar (fun t ω => μ t ω - ζ t ω) x π)
        (fun _ => 0)) β (rotPay ε (ε * (1 + ϕ)) φ)
        (yeoDataM γ ϕ Ybar (fun t ω => μ t ω - ζ t ω) x π) (fun _ => 0) zeroPlan) ↔
      ModelM S γ⁻¹ β (kappaT ε φ γ Ybar * (γ + ϕ)) (uxZ S γ ζ i x π)
        (uPiM S β (kappaT ε φ γ Ybar) γ ϕ (fun t ω => μ t ω - ζ t ω) x π) i (realRate S i π)
        x π := by
  obtain ⟨L, hLb⟩ := hL
  have hζb : ∀ t, BddAt S (ζ t) := fun t => ⟨L, (hLb t).mono fun _ h => h.2.2.1⟩
  have hL' : ∃ L, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L ∧ |μ t ω - ζ t ω| ≤ L :=
    ⟨L + L, fun t => (hLb t).mono fun ω h => by
      have h0 : 0 ≤ L := (abs_nonneg _).trans h.1
      refine ⟨by linarith [h.1], by linarith [h.2.1], ?_⟩
      calc |μ t ω - ζ t ω| ≤ |μ t ω| + |ζ t ω| := abs_sub _ _
        _ ≤ L + L := add_le_add h.2.2.2 h.2.2.1⟩
  rw [optimal_iff_ISZ hβ hγ hY hu hu'c hconc hmono hu' h hζ hζb hfl hfeas hadm hb hWb htvc,
    optimal_iff_PCM (ν := fun t ω => μ t ω - ζ t ω) hβ hβ1 hε hϕ hφ hY hm hss
      (fun t => (hμ t).sub (hζ t)) h.1 h.2.2.1 hL' hmx
      hmπ]
  exact ⟨fun hh t => ⟨hh.1 t, fisherM_realRate S i π t, hh.2 t⟩,
    fun hh => ⟨fun t => (hh t).1, fun t => (hh t).2.2⟩⟩

/-! ### Finite event trees -/

namespace Tree

open ExpectationsFiniteTree TreeBridge TidyR6HouseholdMeasureTVC.Link TidyR6EulerIS.Tree
open TidyR6ShockPC.Tree

variable {Ω' : Type*}

/-- Cochrane (2023), eq. (17.15), p. 407, for a core expectation system: the IS disturbance with
a preference shock, `−σ(E_tζ_{t+1} − ζ_t)` plus the remainder. -/
noncomputable def coreUxZ (𝔼 : ExpectationSystem Ω') (γ : ℝ) (ζ i x π : ℕ → Ω' → ℝ) :
    ℕ → Ω' → ℝ :=
  fun t => (-γ⁻¹) • (𝔼.E t (ζ (t + 1)) - ζ t) + coreIsRem 𝔼 γ i x (piZ π ζ) t

variable [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω'] (T : FiniteTree Ω')

/-- Cochrane (2023), eq. (17.15), p. 407: on a finite tree, the almost-sure IS curve with the
preference-shock disturbance is the project's `FullModel.IS`, in every state. -/
theorem ISMZ_iff_IS (γ : ℝ) (ζ i x π : ℕ → Ω' → ℝ) :
    (∀ t, ISM (treeSystem T) γ⁻¹ (uxZ (treeSystem T) γ ζ i x π) (realRate (treeSystem T) i π)
      x t) ↔
      FullModel.IS T.toExpectationSystem γ⁻¹ (coreUxZ T.toExpectationSystem γ ζ i x π)
        (coreRealRate T.toExpectationSystem i π) x := by
  constructor
  · intro h t
    rw [(treeSystem T).eq_of_ae_eq (treeSystem_fullSupport T) (h t)]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, uxZ, coreUxZ, isRem,
      coreIsRem, realRate, coreRealRate, treeE]
  · intro h t
    refine Eventually.of_forall fun ω => ?_
    rw [h t]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, uxZ, coreUxZ, isRem,
      coreIsRem, realRate, coreRealRate, treeE]

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, with preference and markup shocks, **on a
finite event tree**: under the hypotheses of `eqm_iff_modelZ` posed on the tree, the household
and the price setter are optimal iff the project's `FullModel.Model` holds in every state with
`u_x = coreUxZ` (the discount-rate shock in rate units plus the remainder) and
`u_π = TidyR6ShockPC.Tree.coreUPiM` (`κ̃(μ − ζ)` plus the remainder). -/
theorem eqm_iff_modelZ {β γ a Ybar y ε φ ϕ m : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hε : 1 < ε) (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (hY : 0 < Ybar) (hm : 0 < m)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b ζ μ : ℕ → Ω' → ℝ} {pm b₀ : Ω' → ℝ}
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hi : StronglyAdapted (treeSystem T).𝓕 i)
    (hπ : StronglyAdapted (treeSystem T).𝓕 π) (hpm : StronglyMeasurable[(treeSystem T).𝓕 0] pm)
    (hζ : StronglyAdapted (treeSystem T).𝓕 ζ) (hμ : StronglyAdapted (treeSystem T).𝓕 μ)
    (hL : ∃ L, ∀ t ω, |x t ω| ≤ L ∧ |π t ω| ≤ L ∧ |ζ t ω| ≤ L ∧ |μ t ω| ≤ L)
    (hfl : ∀ t ω, a ≤ outp Ybar x t ω)
    (hmx : ∀ t ω, (ε - 1) * Real.exp m ≤
      ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω + (μ t ω - ζ t ω)))
    (hmπ : ∀ t ω, Real.exp m / 2 ≤ Real.exp (π t ω))
    (hfeas : Feasible (treeSystem T) y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible (treeSystem T) β (fun z => z)
      (felic (fun t ω => Real.exp (ζ t ω)) u (outp Ybar x)))
    (hb : ∀ t ω, 0 < b (t + 1) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, Real.exp (ζ N ω) * u' (outp Ybar x N ω) * b N ω /
      price pm π N ω ∂(treeSystem T).μ) atTop (𝓝 0)) :
    (OptimalP (treeSystem T) β y u (fun t ω => Real.exp (ζ t ω)) (price pm π) s
        (bondPrice β i) b₀ (outp Ybar x) b ∧
      OptimalIn (treeSystem T) (RPlan (treeSystem T) ε (ε * (1 + ϕ))
        (yeoDataM γ ϕ Ybar (fun t ω => μ t ω - ζ t ω) x π) (fun _ => 0)) β
        (rotPay ε (ε * (1 + ϕ)) φ) (yeoDataM γ ϕ Ybar (fun t ω => μ t ω - ζ t ω) x π)
        (fun _ => 0) zeroPlan) ↔
      FullModel.Model T.toExpectationSystem γ⁻¹ β (kappaT ε φ γ Ybar * (γ + ϕ))
        (coreUxZ T.toExpectationSystem γ ζ i x π)
        (coreUPiM T.toExpectationSystem β (kappaT ε φ γ Ybar) γ ϕ
          (fun t ω => μ t ω - ζ t ω) x π) i (coreRealRate T.toExpectationSystem i π) x π := by
  obtain ⟨L, hL⟩ := hL
  rw [TidyR6ShockModel.eqm_iff_modelZ hβ hβ1 hγ hε hϕ hφ hY hm hss hu hu'c hconc hmono hu'
    (logRegular_tree T hx hi hπ hpm) hζ hμ ⟨L, fun t => Eventually.of_forall (hL t)⟩
    (fun t => Eventually.of_forall (hfl t)) (fun t => Eventually.of_forall (hmx t))
    (fun t => Eventually.of_forall (hmπ t)) hfeas hadm (fun t => Eventually.of_forall (hb t))
    (fun _ => Integrable.of_finite) htvc]
  have h1 := ISMZ_iff_IS T γ ζ i x π
  have h2 := PCM_iff_PC_M T β (kappaT ε φ γ Ybar) γ ϕ (fun t ω => μ t ω - ζ t ω) x π
  constructor
  · intro h
    exact ⟨h1.1 fun t => (h t).1, fisher_coreRealRate _ i π, h2.1 fun t => (h t).2.2⟩
  · intro h t
    exact ⟨h1.2 h.1 t, fisherM_realRate _ i π t, h2.2 h.2.2 t⟩

end Tree

end Cochrane.KeynesianStickyPrices.TidyR6ShockModel
