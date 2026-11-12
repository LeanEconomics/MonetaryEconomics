/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6RotembergPC

/-!
# The derived model: equilibria of the household and price-setting problems are (17.15)–(17.17)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4, p. 407: "The economic
model, which we first met in Section 5.1 is (17.15) `x_t = E_tx_{t+1} − σr_t + u_{x,t}`, (17.16)
`i_t = r_t + E_tπ_{t+1}`, (17.17) `π_t = βE_tπ_{t+1} + κx_t + u_{π,t}`", and Chapter 5, §5.1,
p. 118 ("I jump to these linearized equilibrium conditions, but a big point of the new-Keynesian
enterprise is that this structure has detailed micro-foundations").

The project's FullModel imposes (17.15)–(17.17). Here they are derived. The economy: a
representative household with CRRA utility (`u′(C) = C^{−γ}`)
chooses consumption and one-period nominal bonds (TidyR6EulerIS), every price setter faces CES
demand and quadratic costs of changing its price (TidyR6Rotemberg), and in a symmetric equilibrium
consumption equals output `Y_t = Ȳe^{x_t}` and every price setter charges the aggregate price.
The price setter values its revenue at the household's marginal utility (`yeoData_fst_eq`);
the disutility of production and the cost of changing prices are additively separable from
consumption, so the household's consumption and bond choice, given its income, is the problem of
TidyR6EulerIS.

## Main results (on a genuine probability space, information possibly growing forever)

* `model_of_eqm` (**necessity**): if the household plan and pricing at the aggregate price are
  optimal (the price setter among **all** plans), then (17.15)–(17.17) hold at every date
  (`ModelM`) with `σ = 1/γ`, `κ = κ̃(γ + ϕ)` and the explicit remainders
  `u_{x,t} = −σE_t[expRem z_{t+1}]`, `u_{π,t} = βE_tR_G(π_{t+1}) − R_G(π_t) + κ̃R_M(x_t)`.
* `eqm_iff_model` (**necessity and sufficiency**): under the stated regularity (uniformly bounded
  output gap and inflation inside the margin conditions, positive government debt, the household's
  transversality condition), the processes form an equilibrium (household optimal, the price
  setter optimal within its concavity region) **iff** (17.15)–(17.17) hold with those
  remainders. The remainders are second order (`remainders_second_order`, `pcRem_bound`;
  `TidyR6EulerIS.isRem_bounds`): so the equilibria of the derived model are exactly the
  imposed-equation equilibria to first order.
* `steady_state_eqm`: on every probability space the zero-inflation steady state, with
  positive government debt and the concrete utility `TidyR6EulerIS.crraU`, is an equilibrium:
  the hypotheses of `eqm_iff_model` are satisfiable.
* `hasDerivAt_euler_line`, `hasDerivAt_pc_line`: along every direction, the derivatives at the
  steady state of the nonlinear Euler and Phillips-curve residuals are the linear (17.15) and
  (17.17) residuals: the log-linear model is the exact first-order part.
* Finite trees: `Tree.eqm_iff_model` (equilibria are exactly the project's `FullModel.Model` with
  the remainders as disturbances, in every state), `Tree.model_of_eqm`, and
  `Tree.eqm_17_18`: every derived equilibrium satisfies the project's (17.18) with the
  remainder disturbances (`FullModel.eq_17_18_shocks`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6DerivedModel

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6HouseholdMeasureTVC TidyR6EulerIS TidyR6PriceSetting
open TidyR6Rotemberg TidyR6RotembergPC

/-! ### First order: the remainders -/

/-- Cochrane (2023), p. 118 ("Linearize and approximate"): all three remainder functions vanish
at the steady state with zero derivative there: `expRem`, `R_G` and `R_M`. -/
theorem remainders_second_order (γ ϕ : ℝ) :
    (expRem 0 = 0 ∧ HasDerivAt expRem 0 0) ∧ (rG 0 = 0 ∧ HasDerivAt rG 0 0) ∧
      (rM γ ϕ 0 = 0 ∧ HasDerivAt (rM γ ϕ) 0 0) :=
  ⟨⟨expRem_zero, hasDerivAt_expRem_zero⟩, ⟨rG_zero, hasDerivAt_rG_zero⟩,
    ⟨rM_zero γ ϕ, hasDerivAt_rM_zero γ ϕ⟩⟩

/-- Cochrane (2023), eq. (17.15), p. 407 and p. 118: the exact derivative of the nonlinear Euler
residual `exp(h z) − 1` at the steady state `h = 0`, along the direction
`z = i − γ(x′ − x) − π′`, is the linear residual `z`, which vanishes iff
`x = x′ − σ(i − π′)` (`σ = 1/γ`). -/
theorem hasDerivAt_euler_line {γ : ℝ} (hγ : γ ≠ 0) (i x x' p' : ℝ) :
    HasDerivAt (fun h => Real.exp (h * (i - γ * (x' - x) - p')) - 1)
        (i - γ * (x' - x) - p') 0 ∧
      (i - γ * (x' - x) - p' = 0 ↔ x = x' - γ⁻¹ * (i - p')) := by
  refine ⟨?_, ?_⟩
  · have h := ((hasDerivAt_id (0 : ℝ)).mul_const (i - γ * (x' - x) - p')).exp.sub_const 1
    simpa using h
  · constructor
    · intro h
      field_simp
      linarith
    · intro h
      rw [h]
      field_simp
      ring

/-- Cochrane (2023), eq. (17.17), p. 407 and p. 118: the exact derivative of the nonlinear
Phillips-curve residual `G(hπ) − βG(hπ′) − κ̃(e^{(1+ϕ)hx} − e^{(1−γ)hx})` at the steady state
`h = 0`, along the direction `(π, π′, x)`, is the linear residual `π − βπ′ − κ̃(γ + ϕ)x`. -/
theorem hasDerivAt_pc_line (β κt γ ϕ p p' x : ℝ) :
    HasDerivAt (fun h => gInfl (h * p) - β * gInfl (h * p') - κt * mcGap γ ϕ (h * x))
      (p - β * p' - κt * (γ + ϕ) * x) 0 := by
  have hl : ∀ c : ℝ, HasDerivAt (fun h : ℝ => h * c) c 0 := fun c => by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
  have hg : ∀ c : ℝ, HasDerivAt (fun h => gInfl (h * c)) c 0 := fun c => by
    have h1 : HasDerivAt (fun h => (Real.exp (h * c) - 1) * Real.exp (h * c))
        (Real.exp (0 * c) * c * Real.exp (0 * c) + (Real.exp (0 * c) - 1) *
          (Real.exp (0 * c) * c)) 0 := ((hl c).exp.sub_const 1).mul (hl c).exp
    exact h1.congr_deriv (by simp)
  have hm : HasDerivAt (fun h => mcGap γ ϕ (h * x)) ((γ + ϕ) * x) 0 := by
    have h1 : HasDerivAt (fun h => Real.exp ((1 + ϕ) * (h * x)) - Real.exp ((1 - γ) * (h * x)))
        (Real.exp ((1 + ϕ) * (0 * x)) * ((1 + ϕ) * x) -
          Real.exp ((1 - γ) * (0 * x)) * ((1 - γ) * x)) 0 :=
      ((hl x).const_mul (1 + ϕ)).exp.sub ((hl x).const_mul (1 - γ)).exp
    exact h1.congr_deriv (by simp; ring)
  have h := ((hg p).sub ((hg p').const_mul β)).sub (hm.const_mul κt)
  exact h.congr_deriv (by ring)

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), eq. (17.17), p. 407: the Phillips-curve remainder is second order: almost
surely `|u_{π,t}| ≤ 5βE_tπ²_{t+1} + 5π_t² + |κ̃|((1 + ϕ)² + (1 − γ)²)x_t²` when
`|π_t|, |π_{t+1}| ≤ 1/2` and `|(1 + ϕ)x_t|, |(1 − γ)x_t| ≤ 1` (`β ≥ 0`). -/
theorem pcRem_bound {β κt γ ϕ : ℝ} (hβ : 0 ≤ β) {x π : ℕ → Ω → ℝ} {t : ℕ}
    (hm : AEStronglyMeasurable (π (t + 1)) S.μ)
    (hπ1 : ∀ᵐ ω ∂S.μ, |π (t + 1) ω| ≤ 1 / 2) (hπ0 : ∀ᵐ ω ∂S.μ, |π t ω| ≤ 1 / 2)
    (hx1 : ∀ᵐ ω ∂S.μ, |(1 + ϕ) * x t ω| ≤ 1) (hx2 : ∀ᵐ ω ∂S.μ, |(1 - γ) * x t ω| ≤ 1) :
    ∀ᵐ ω ∂S.μ, |pcRem S β κt γ ϕ x π t ω| ≤
      5 * β * S.E t (fun ω => π (t + 1) ω ^ 2) ω + 5 * π t ω ^ 2 +
        |κt| * (((1 + ϕ) ^ 2 + (1 - γ) ^ 2) * x t ω ^ 2) := by
  have hrc : Continuous rG := by unfold rG gInfl; fun_prop
  have hRi : Integrable (fun ω => rG (π (t + 1) ω)) S.μ := by
    refine Integrable.of_bound (hrc.comp_aestronglyMeasurable hm) (5 * (1 / 2) ^ 2) ?_
    filter_upwards [hπ1] with ω h
    rw [Real.norm_eq_abs]
    refine (rG_le h).trans ?_
    have := sq_abs (π (t + 1) ω)
    nlinarith [abs_nonneg (π (t + 1) ω)]
  have hQi : Integrable (fun ω => 5 * π (t + 1) ω ^ 2) S.μ := by
    refine Integrable.of_bound ((hm.pow 2).const_mul 5) (5 * (1 / 2) ^ 2) ?_
    filter_upwards [hπ1] with ω h
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have := abs_nonneg (π (t + 1) ω)
    have := sq_abs (π (t + 1) ω)
    norm_num
    nlinarith
  have hup := S.E_mono hRi hQi (hπ1.mono fun ω h => (le_abs_self _).trans (rG_le h)) t
  have hlo := S.E_mono hRi.neg hQi (hπ1.mono fun ω h => (neg_le_abs _).trans (rG_le h)) t
  have hneg := S.E_smul (-1) (fun ω => rG (π (t + 1) ω)) t
  have h5 := S.E_smul 5 (fun ω => π (t + 1) ω ^ 2) t
  filter_upwards [hup, hlo, hneg, h5, hπ0, hx1, hx2] with ω a1 a2 a3 a4 b0 b1 b2
  have e1 : (fun ω => 5 * π (t + 1) ω ^ 2) = (5 : ℝ) • fun ω => π (t + 1) ω ^ 2 := by
    funext ω; simp
  have e2 : (-fun ω => rG (π (t + 1) ω)) = (-1 : ℝ) • fun ω => rG (π (t + 1) ω) := by
    funext ω; simp
  rw [e1, a4, Pi.smul_apply, smul_eq_mul] at a1 a2
  rw [e2, a3, Pi.smul_apply, smul_eq_mul] at a2
  have hG := rG_le b0
  have hM := rM_le b1 b2
  have hk := abs_nonneg κt
  simp only [pcRem]
  have hK : |κt * rM γ ϕ (x t ω)| ≤ |κt| * (((1 + ϕ) ^ 2 + (1 - γ) ^ 2) * x t ω ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hM hk
  rw [abs_le] at hG hK ⊢
  constructor <;> nlinarith

/-! ### The economy and its equilibria -/

variable (S) in
/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, on a probability space: at every date, almost
surely, `x_t = E_tx_{t+1} − σr_t + u_{x,t}`, `i_t = r_t + E_tπ_{t+1}` and
`π_t = βE_tπ_{t+1} + κx_t + u_{π,t}`. -/
def ModelM (σ β κ : ℝ) (ux uπ i r x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ISM S σ ux r x t ∧ FisherM S i r π t ∧ PCM S β κ uπ x π t

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the price setter values revenue at the household's marginal utility:
`A_t = u′(Y_t)Y_t` (CRRA above the floor). -/
theorem yeoData_fst_eq {γ a ϕ Ybar : ℝ} (hY : 0 < Ybar) {u' : ℝ → ℝ}
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x π : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : a ≤ outp Ybar x t ω) :
    (yeoData γ ϕ Ybar x π t ω).1 = u' (outp Ybar x t ω) * outp Ybar x t ω := by
  rw [hu' _ h]
  simp only [yeoData, outp]
  rw [Real.mul_rpow hY.le (Real.exp_pos _).le, ← Real.exp_mul]
  have e1 : Ybar ^ (1 - γ) = Ybar ^ (-γ) * Ybar := by
    rw [show 1 - γ = -γ + 1 by ring, Real.rpow_add hY, Real.rpow_one]
  have e2 : Real.exp ((1 - γ) * x t ω) = Real.exp (x t ω * -γ) * Real.exp (x t ω) := by
    rw [← Real.exp_add]
    ring_nf
  rw [e1, e2]
  ring

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, **derived (necessity)**: if consuming output
is optimal for the household (which holds bonds at every date) and charging the aggregate price is
optimal for the Rotemberg price setter among all plans, then (17.15)–(17.17) hold at every date
with `σ = 1/γ`, `κ = κ̃(γ + ϕ)`, the real rate (17.16) and the explicit remainders `isRem` and
`pcRem`. -/
theorem model_of_eqm {β γ a Ybar y ε φ ϕ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    (hφ : φ ≠ 0) (hϕ : 1 + ϕ ≠ 0) (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hhh : Optimal S β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hfirm : OptimalIn S (Plan S) β (rotPay ε (ε * (1 + ϕ)) φ) (yeoData γ ϕ Ybar x π)
      (fun _ => 0) zeroPlan)
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) :
    ModelM S γ⁻¹ β (kappaT ε φ γ Ybar * (γ + ϕ)) (isRem S γ i x π)
      (pcRem S β (kappaT ε φ γ Ybar) γ ϕ x π) i (realRate S i π) x π := fun t =>
  ⟨IS_of_optimal hβ hγ hY hu hu'c hu' h hfl hhh (hb t), fisherM_realRate S i π t,
    PC_of_optimal hβ hφ hϕ hss h.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1 hfirm t⟩

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, **derived (necessity and sufficiency)**: let
`0 < β < 1`, `γ > 0`, `ε > 1`, `ϕ ≥ 0`, `φ > 0`, `Ȳ > 0` the steady state, `u` concave, increasing,
differentiable with continuous derivative, CRRA above the floor `a` (output above it), the
variables `LogRegular` with output gap and inflation uniformly bounded and inside the margin
conditions (`m > 0`), the household plan feasible and admissible with positive bond holdings,
integrable marginal-utility-weighted bonds and its transversality condition. Then the household
plan and the symmetric pricing are optimal (the price setter within its concavity region) **iff**
(17.15)–(17.17) hold at every date with `σ = 1/γ`, `κ = κ̃(γ + ϕ)` and the explicit second-order
remainders `isRem`, `pcRem`. -/
theorem eqm_iff_model {β γ a Ybar y ε φ ϕ m : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hε : 1 < ε) (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (hY : 0 < Ybar) (hm : 0 < m)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    (h : LogRegular S x i π pm) (hL : ∃ L, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L)
    (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp Ybar x t ω)
    (hmx : ∀ t, ∀ᵐ ω ∂S.μ, (ε - 1) * Real.exp m ≤ ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω))
    (hmπ : ∀ t, ∀ᵐ ω ∂S.μ, Real.exp m / 2 ≤ Real.exp (π t ω))
    (hfeas : Feasible S y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible S β u (outp Ybar x)) (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω)
    (hWb : ∀ n, Integrable (fun ω => u' (outp Ybar x n ω) * b n ω / price pm π n ω) S.μ)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (outp Ybar x N ω) * b N ω / price pm π N ω ∂S.μ)
      atTop (𝓝 0)) :
    (Optimal S β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b ∧
      OptimalIn S (RPlan S ε (ε * (1 + ϕ)) (yeoData γ ϕ Ybar x π) (fun _ => 0)) β
        (rotPay ε (ε * (1 + ϕ)) φ) (yeoData γ ϕ Ybar x π) (fun _ => 0) zeroPlan) ↔
      ModelM S γ⁻¹ β (kappaT ε φ γ Ybar * (γ + ϕ)) (isRem S γ i x π)
        (pcRem S β (kappaT ε φ γ Ybar) γ ϕ x π) i (realRate S i π) x π := by
  rw [optimal_iff_IS hβ hγ hY hu hu'c hconc hmono hu' h hfl hfeas hadm hb hWb htvc,
    optimal_iff_PC hβ hβ1 hε hϕ hφ hY hm hss h.1 h.2.2.1 hL hmx hmπ]
  exact ⟨fun hh t => ⟨(hh.1 t).1, (hh.1 t).2, hh.2 t⟩,
    fun hh => ⟨fun t => ⟨(hh t).1, (hh t).2.1⟩, fun t => (hh t).2.2⟩⟩

/-! ### The steady state is an equilibrium (the hypotheses are satisfiable) -/

/-- Cochrane (2023), p. 118: the steady-state output `Ȳ = ((ε − 1)/ε)^{1/(γ+ϕ)}`. -/
noncomputable def ssY (ε γ ϕ : ℝ) : ℝ := ((ε - 1) / ε) ^ (1 / (γ + ϕ))

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407: on every probability space the zero-inflation
steady state (`x = i = π = 0`, constant positive government debt `B̄` held by the household, the
taxes that satisfy its budget) is an equilibrium of the derived model, for the concrete CRRA
utility `crraU` (`0 < β < 1`, `γ > 0`, `ε > 1`, `ϕ ≥ 0`, `φ > 0`): all the hypotheses of
`eqm_iff_model` hold there, and the remainders vanish. -/
theorem steady_state_eqm {β γ ε φ ϕ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hε : 1 < ε)
    (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (y Bbar : ℝ) (hB : 0 < Bbar) :
    Optimal S β y (crraU γ (ssY ε γ ϕ)) (price (fun _ => 0) (fun _ _ => 0))
        (fun _ _ => y - ssY ε γ ϕ + (1 - β) * Bbar) (bondPrice β (fun _ _ => 0)) (fun _ => Bbar)
        (outp (ssY ε γ ϕ) (fun _ _ => 0)) (fun _ _ => Bbar) ∧
      OptimalIn S (RPlan S ε (ε * (1 + ϕ))
          (yeoData γ ϕ (ssY ε γ ϕ) (fun _ _ => 0) (fun _ _ => 0)) (fun _ => 0)) β
        (rotPay ε (ε * (1 + ϕ)) φ) (yeoData γ ϕ (ssY ε γ ϕ) (fun _ _ => 0) (fun _ _ => 0))
        (fun _ => 0) zeroPlan := by
  set Y := ssY ε γ ϕ with hYdef
  have hγϕ : 0 < γ + ϕ := by linarith
  have hYpos : 0 < Y := Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _
  have hss : ε * Y ^ (1 + ϕ) = (ε - 1) * Y ^ (1 - γ) := ybar_ss hε hγϕ.ne'
  obtain ⟨hu, hu'c, -, hconc, hmono, hu'⟩ := crraU_regular hγ.le hYpos
  have hout : ∀ t (ω : Ω), outp Y (fun _ _ => (0 : ℝ)) t ω = Y := fun _ _ => by simp [outp]
  have hpr : ∀ t (ω : Ω), price (fun _ : Ω => (0 : ℝ)) (fun _ _ => 0) t ω = 1 := fun _ _ => by
    simp [price, logPrice]
  have hbp : ∀ t (ω : Ω), bondPrice β (fun _ _ => (0 : ℝ)) t ω = β := fun _ _ => by
    simp [bondPrice]
  -- the margin
  have hq : 1 < ε * (1 + ϕ) / (ε - 1) := by
    rw [one_lt_div (by linarith)]
    nlinarith
  set m := min (Real.log 2) (Real.log (ε * (1 + ϕ) / (ε - 1))) with hmdef
  have hm : 0 < m := lt_min (Real.log_pos one_lt_two) (Real.log_pos hq)
  have hm2 : Real.exp m ≤ 2 := by
    calc Real.exp m ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (min_le_left _ _)
      _ = 2 := Real.exp_log two_pos
  have hmq : Real.exp m ≤ ε * (1 + ϕ) / (ε - 1) := by
    calc Real.exp m ≤ Real.exp (Real.log (ε * (1 + ϕ) / (ε - 1))) :=
          Real.exp_le_exp.2 (min_le_right _ _)
      _ = ε * (1 + ϕ) / (ε - 1) := Real.exp_log (by linarith)
  have hreg : LogRegular S (fun _ _ => (0 : ℝ)) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) :=
    ⟨fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
      fun _ => stronglyMeasurable_const, stronglyMeasurable_const, fun _ => BddAt.const 0,
      fun _ => BddAt.const 0, fun _ => BddAt.const 0, BddAt.const 0⟩
  have hfeas : Feasible S y (price (fun _ => 0) (fun _ _ => 0))
      (fun _ _ => y - Y + (1 - β) * Bbar) (bondPrice β (fun _ _ => 0)) (fun _ => Bbar)
      (outp Y (fun _ _ => 0)) (fun _ _ => Bbar) := by
    refine ⟨rfl, fun t => ?_, fun _ => stronglyMeasurable_const, fun n => ?_,
      fun _ => Eventually.of_forall fun _ => hB.le⟩
    · have e : outp Y (fun _ _ => (0 : ℝ)) t = fun _ => Y := funext fun ω => hout t ω
      rw [e]
      exact stronglyMeasurable_const
    · refine Eventually.of_forall fun ω => ?_
      rw [hpr, hbp, hout]
      ring
  have hadm : Admissible S β (crraU γ Y) (outp Y (fun _ _ => 0)) :=
    admissible_of_bdd hβ.le hβ1
      (continuous_iff_continuousAt.2 fun c => (hu c).continuousAt)
      (fun n => by
        have e : outp Y (fun _ _ => (0 : ℝ)) n = fun _ => Y := funext fun ω => hout n ω
        rw [e]
        exact aestronglyMeasurable_const) (M := Y)
      fun n => Eventually.of_forall fun ω => by rw [hout, abs_of_pos hYpos]
  have htvc : Tendsto (fun N => β ^ N * ∫ ω, crraMU γ Y (outp Y (fun _ _ => 0) N ω) *
      (fun _ _ => Bbar : ℕ → Ω → ℝ) N ω / price (fun _ => 0) (fun _ _ => 0) N ω ∂S.μ)
      atTop (𝓝 0) := by
    have e : (fun N => β ^ N * ∫ ω, crraMU γ Y (outp Y (fun _ _ => 0) N ω) *
        (fun _ _ => Bbar : ℕ → Ω → ℝ) N ω / price (fun _ => 0) (fun _ _ => 0) N ω ∂S.μ) =
        fun N => β ^ N * (crraMU γ Y Y * Bbar) := by
      funext N
      simp only [hout, hpr, div_one, integral_const, probReal_univ, one_smul]
    rw [e]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const
      (crraMU γ Y Y * Bbar)
  refine (eqm_iff_model hβ hβ1 hγ hε hϕ hφ hYpos hm hss hu hu'c hconc hmono hu' hreg
    ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩
    (fun t => Eventually.of_forall fun ω => by rw [hout]) (fun t => Eventually.of_forall
      fun _ => by
        simp only [mul_zero, Real.exp_zero, mul_one]
        rw [le_div_iff₀ (by linarith)] at hmq
        linarith)
    (fun t => Eventually.of_forall fun _ => by simp only [Real.exp_zero]; linarith)
    hfeas hadm (fun _ => Eventually.of_forall fun _ => hB)
    (fun n => (integrable_const (crraMU γ Y Y * Bbar)).congr
      (Eventually.of_forall fun ω => by simp only [hout, hpr, div_one]))
    htvc).2 fun t => ⟨?_, fisherM_realRate S _ _ t, ?_⟩
  · refine Eventually.of_forall fun ω => ?_
    simp [isRem, realRate, sdfGap, expRem_zero, S.E_const]
  · refine Eventually.of_forall fun ω => ?_
    simp [pcRem, rG_zero, rM_zero, S.E_const]

/-! ### Finite event trees: the project's `FullModel.Model` -/

namespace Tree

open ExpectationsFiniteTree TreeBridge TidyR6EulerIS.Tree TidyR6RotembergPC.Tree

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407: on a finite tree, `ModelM` with the
remainders is exactly the project's `FullModel.Model` for the tree's core expectation system,
with the core remainders as the disturbances `u_x`, `u_π`. -/
theorem modelM_iff (β γ κt ϕ : ℝ) (i x π : ℕ → Ω' → ℝ) :
    ModelM (treeSystem T) γ⁻¹ β (κt * (γ + ϕ)) (isRem (treeSystem T) γ i x π)
        (pcRem (treeSystem T) β κt γ ϕ x π) i (realRate (treeSystem T) i π) x π ↔
      FullModel.Model T.toExpectationSystem γ⁻¹ β (κt * (γ + ϕ))
        (coreIsRem T.toExpectationSystem γ i x π) (corePcRem T.toExpectationSystem β κt γ ϕ x π)
        i (coreRealRate T.toExpectationSystem i π) x π := by
  have h1 := ISM_iff_IS T γ i x π
  have h2 := PCM_iff_PC T β κt γ ϕ x π
  constructor
  · intro h
    exact ⟨h1.1 fun t => (h t).1, fisher_coreRealRate _ i π, h2.1 fun t => (h t).2.2⟩
  · intro h t
    exact ⟨h1.2 h.1 t, fisherM_realRate _ i π t, h2.2 h.2.2 t⟩

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, **on a finite event tree (necessity)**: if
the household plan and the symmetric pricing are optimal (the price setter among all plans), the
household holds bonds in every state and the variables are adapted, then the project's
`FullModel.Model` holds exactly, in every state, with the remainders as disturbances. -/
theorem model_of_eqm {β γ a Ybar y ε φ ϕ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    (hφ : φ ≠ 0) (hϕ : 1 + ϕ ≠ 0) (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω' → ℝ} {pm b₀ : Ω' → ℝ}
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hi : StronglyAdapted (treeSystem T).𝓕 i)
    (hπ : StronglyAdapted (treeSystem T).𝓕 π) (hpm : StronglyMeasurable[(treeSystem T).𝓕 0] pm)
    (hfl : ∀ t ω, a ≤ outp Ybar x t ω)
    (hhh : Optimal (treeSystem T) β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hfirm : OptimalIn (treeSystem T) (Plan (treeSystem T)) β (rotPay ε (ε * (1 + ϕ)) φ)
      (yeoData γ ϕ Ybar x π) (fun _ => 0) zeroPlan)
    (hb : ∀ t ω, 0 < b (t + 1) ω) :
    FullModel.Model T.toExpectationSystem γ⁻¹ β (kappaT ε φ γ Ybar * (γ + ϕ))
      (coreIsRem T.toExpectationSystem γ i x π)
      (corePcRem T.toExpectationSystem β (kappaT ε φ γ Ybar) γ ϕ x π) i
      (coreRealRate T.toExpectationSystem i π) x π :=
  (modelM_iff T β γ (kappaT ε φ γ Ybar) ϕ i x π).1
    (TidyR6DerivedModel.model_of_eqm hβ hγ hY hφ hϕ hss hu hu'c hu'
      (logRegular_tree T hx hi hπ hpm) (fun t => Eventually.of_forall (hfl t)) hhh hfirm
      fun t => Eventually.of_forall (hb t))

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, **on a finite event tree (necessity and
sufficiency)**: under the hypotheses of `TidyR6DerivedModel.eqm_iff_model` posed on the tree
(every state has positive probability, so "almost surely" is "in every state"), the household
plan and the symmetric pricing form an equilibrium iff the project's `FullModel.Model` holds with
the remainders as the disturbances `u_x`, `u_π`. -/
theorem eqm_iff_model {β γ a Ybar y ε φ ϕ m : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hε : 1 < ε) (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (hY : 0 < Ybar) (hm : 0 < m)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω' → ℝ} {pm b₀ : Ω' → ℝ}
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hi : StronglyAdapted (treeSystem T).𝓕 i)
    (hπ : StronglyAdapted (treeSystem T).𝓕 π) (hpm : StronglyMeasurable[(treeSystem T).𝓕 0] pm)
    (hL : ∃ L, ∀ t ω, |x t ω| ≤ L ∧ |π t ω| ≤ L) (hfl : ∀ t ω, a ≤ outp Ybar x t ω)
    (hmx : ∀ t ω, (ε - 1) * Real.exp m ≤ ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω))
    (hmπ : ∀ t ω, Real.exp m / 2 ≤ Real.exp (π t ω))
    (hfeas : Feasible (treeSystem T) y (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hadm : Admissible (treeSystem T) β u (outp Ybar x)) (hb : ∀ t ω, 0 < b (t + 1) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (outp Ybar x N ω) * b N ω / price pm π N ω
      ∂(treeSystem T).μ) atTop (𝓝 0)) :
    (Optimal (treeSystem T) β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b ∧
      OptimalIn (treeSystem T) (RPlan (treeSystem T) ε (ε * (1 + ϕ)) (yeoData γ ϕ Ybar x π)
        (fun _ => 0)) β (rotPay ε (ε * (1 + ϕ)) φ) (yeoData γ ϕ Ybar x π) (fun _ => 0)
        zeroPlan) ↔
      FullModel.Model T.toExpectationSystem γ⁻¹ β (kappaT ε φ γ Ybar * (γ + ϕ))
        (coreIsRem T.toExpectationSystem γ i x π)
        (corePcRem T.toExpectationSystem β (kappaT ε φ γ Ybar) γ ϕ x π) i
        (coreRealRate T.toExpectationSystem i π) x π := by
  obtain ⟨L, hL⟩ := hL
  rw [TidyR6DerivedModel.eqm_iff_model hβ hβ1 hγ hε hϕ hφ hY hm hss hu hu'c hconc hmono hu'
    (logRegular_tree T hx hi hπ hpm) ⟨L, fun t => Eventually.of_forall (hL t)⟩
    (fun t => Eventually.of_forall (hfl t)) (fun t => Eventually.of_forall (hmx t))
    (fun t => Eventually.of_forall (hmπ t)) hfeas hadm (fun t => Eventually.of_forall (hb t))
    (fun _ => Integrable.of_finite) htvc]
  exact modelM_iff T β γ (kappaT ε φ γ Ybar) ϕ i x π

/-- Cochrane (2023), eq. (17.18), p. 408, derived: in every equilibrium of the derived model on
a finite tree (necessity part of `Tree.model_of_eqm`), the interest rate and inflation satisfy the
project's (17.18) with the remainders as the disturbances,
`σκ i_t = −βE_tπ_{t+2} + (1 + β + σκ)E_tπ_{t+1} − π_t + (u_{π,t} − E_tu_{π,t+1}) + κu_{x,t}`
(`γ > 0`, `ϕ ≥ 0`, `ε > 1`, `φ > 0`, `Ȳ > 0`). -/
theorem eqm_17_18 {β γ a Ybar y ε φ ϕ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hY : 0 < Ybar)
    (hε : 1 < ε) (hφ : 0 < φ) (hϕ : 0 ≤ ϕ) (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ))
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-γ)) {x i π s b : ℕ → Ω' → ℝ} {pm b₀ : Ω' → ℝ}
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hi : StronglyAdapted (treeSystem T).𝓕 i)
    (hπ : StronglyAdapted (treeSystem T).𝓕 π) (hpm : StronglyMeasurable[(treeSystem T).𝓕 0] pm)
    (hfl : ∀ t ω, a ≤ outp Ybar x t ω)
    (hhh : Optimal (treeSystem T) β y u (price pm π) s (bondPrice β i) b₀ (outp Ybar x) b)
    (hfirm : OptimalIn (treeSystem T) (Plan (treeSystem T)) β (rotPay ε (ε * (1 + ϕ)) φ)
      (yeoData γ ϕ Ybar x π) (fun _ => 0) zeroPlan)
    (hb : ∀ t ω, 0 < b (t + 1) ω) (t : ℕ) :
    (γ⁻¹ * (kappaT ε φ γ Ybar * (γ + ϕ))) • i t =
      -β • T.toExpectationSystem.E t (π (t + 2)) +
        (1 + β + γ⁻¹ * (kappaT ε φ γ Ybar * (γ + ϕ))) • T.toExpectationSystem.E t (π (t + 1)) -
        π t + (corePcRem T.toExpectationSystem β (kappaT ε φ γ Ybar) γ ϕ x π t -
          T.toExpectationSystem.E t (corePcRem T.toExpectationSystem β (kappaT ε φ γ Ybar) γ ϕ
            x π (t + 1))) +
        (kappaT ε φ γ Ybar * (γ + ϕ)) • coreIsRem T.toExpectationSystem γ i x π t := by
  have hκ : kappaT ε φ γ Ybar * (γ + ϕ) ≠ 0 := by
    refine mul_ne_zero ?_ (by linarith)
    simp only [kappaT]
    exact div_ne_zero (mul_ne_zero (by linarith) (Real.rpow_pos_of_pos hY _).ne') hφ.ne'
  have hmod := model_of_eqm T hβ hγ hY hφ.ne' (by linarith) hss hu hu'c hu' hx hi hπ hpm hfl hhh
    hfirm hb
  exact ((FullModel.eq_17_18_shocks T.toExpectationSystem hκ).1 hmod).2.2 t

end Tree

end Cochrane.KeynesianStickyPrices.TidyR6DerivedModel
