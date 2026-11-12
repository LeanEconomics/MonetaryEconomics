/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6RotembergPC

/-!
# The Phillips curve (17.17) with a genuine cost-push disturbance

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, eq. (17.17), p. 407
(`π_t = βE_tπ_{t+1} + κx_t + u_{π,t}`), and Chapter 5, §5.1, p. 119 ("Phillips curve shocks, often
called 'marginal cost' shocks").

The Rotemberg price setter of TidyR6RotembergPC whose revenue, valued at the household's marginal
utility, is scaled by `e^{−ν_t}`: `A_t = Ȳ^{1−γ}e^{(1−γ)x_t − ν_t}` (`yeoDataM`). Two genuine
sources of `ν` are used in TidyR6ShockModel: a **markup shock** `μ_t`, a stochastic sales tax
`1 − e^{−μ_t}` that raises the desired markup to `e^{μ_t}ε/(ε − 1)`, and a **preference shock**
`ξ_t = e^{ζ_t}` on the utility of consumption, which scales the marginal utility of income by
`ξ_t`; together `ν_t = μ_t − ζ_t`.

## Main results

* `symFOC_iff_nonlinPCM`: the first-order condition at `q ≡ 0` is the exact nonlinear curve
  `G(π_t) = βE_tG(π_{t+1}) + κ̃(e^{(1+ϕ)x_t} − e^{(1−γ)x_t − ν_t})`.
* `nonlinPCM_iff_PCM`: exactly, (17.17) with `κ = κ̃(γ + ϕ)` and
  `u_{π,t} = κ̃ν_t + βE_tR_G(π_{t+1}) − R_G(π_t) + κ̃R_ν(x_t, ν_t)` (`uPiM`), the remainder
  `R_ν = expRem((1 + ϕ)x) − expRem((1 − γ)x − ν)` second order in `(x, ν)` (`rMM_eq`,
  `rMM_le`, `hasDerivAt_rMM_zero`).
* `PC_of_optimalM` (necessity over all plans) and `optimal_iff_PCM` (equivalence among the plans
  of the concavity region, under margin conditions), and on finite trees `Tree.PCM_iff_PC_M`
  (`FullModel.PC`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6ShockPC

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6PriceSetting TidyR6Rotemberg TidyR6RotembergPC TidyR6EulerIS

/-- Cochrane (2023), p. 119: the marginal-cost gap with a cost-push shift `ν`,
`e^{(1+ϕ)x} − e^{(1−γ)x − ν}`. -/
noncomputable def mcGapM (γ ϕ ν x : ℝ) : ℝ :=
  Real.exp ((1 + ϕ) * x) - Real.exp ((1 - γ) * x - ν)

/-- Cochrane (2023), p. 119: its remainder `R_ν(x) = mcGap − (γ + ϕ)x − ν`. -/
noncomputable def rMM (γ ϕ ν x : ℝ) : ℝ := mcGapM γ ϕ ν x - (γ + ϕ) * x - ν

/-- Cochrane (2023), p. 119: `R_ν = expRem((1 + ϕ)x) − expRem((1 − γ)x − ν)`. -/
theorem rMM_eq (γ ϕ ν x : ℝ) :
    rMM γ ϕ ν x = expRem ((1 + ϕ) * x) - expRem ((1 - γ) * x - ν) := by
  simp only [rMM, mcGapM, expRem]
  ring

/-- Cochrane (2023), p. 119: `R_ν` is second order,
`|R_ν| ≤ ((1 + ϕ)x)² + ((1 − γ)x − ν)²` when both arguments are at most one in absolute value. -/
theorem rMM_le {γ ϕ ν x : ℝ} (h1 : |(1 + ϕ) * x| ≤ 1) (h2 : |(1 - γ) * x - ν| ≤ 1) :
    |rMM γ ϕ ν x| ≤ ((1 + ϕ) * x) ^ 2 + ((1 - γ) * x - ν) ^ 2 := by
  have a1 := expRem_le_sq h1
  have a2 := expRem_le_sq h2
  have b1 := expRem_nonneg ((1 + ϕ) * x)
  have b2 := expRem_nonneg ((1 - γ) * x - ν)
  rw [rMM_eq, abs_le]
  constructor <;> nlinarith

/-- Cochrane (2023), p. 119: along every direction `(x, ν)`, `R_ν` has zero derivative at the
steady state. -/
theorem hasDerivAt_rMM_zero (γ ϕ ν x : ℝ) :
    HasDerivAt (fun h => rMM γ ϕ (h * ν) (h * x)) 0 0 := by
  have hc : ∀ c : ℝ, HasDerivAt (fun h : ℝ => expRem (h * c)) 0 0 := fun c => by
    have h0 : HasDerivAt expRem 0 (0 * c) := by rw [zero_mul]; exact hasDerivAt_expRem_zero
    have hl : HasDerivAt (fun h : ℝ => h * c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
    have h := h0.comp (0 : ℝ) hl
    rw [zero_mul] at h
    exact h
  have h := (hc ((1 + ϕ) * x)).sub (hc ((1 - γ) * x - ν))
  simp only [sub_self] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun h => ?_)
  simp only [rMM_eq, Pi.sub_apply]
  congr 1 <;> congr 1 <;> ring

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 119: the price setter's data with the cost-push shift `ν`. -/
noncomputable def yeoDataM (γ ϕ Ybar : ℝ) (ν x π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ × ℝ × ℝ :=
  fun t ω => (Ybar ^ (1 - γ) * Real.exp ((1 - γ) * x t ω - ν t ω),
    Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x t ω) / (1 + ϕ), π t ω)

variable (S) in
/-- Cochrane (2023), p. 119: the exact nonlinear Phillips curve with the cost-push shift. -/
def NonlinPCM (β κt γ ϕ : ℝ) (ν x π : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, gInfl (π t ω) =
    β * S.E t (fun ω => gInfl (π (t + 1) ω)) ω + κt * mcGapM γ ϕ (ν t ω) (x t ω)

variable (S) in
/-- Cochrane (2023), eq. (17.17), p. 407: the Phillips-curve disturbance with the cost-push
shock, `u_{π,t} = κ̃ν_t + βE_tR_G(π_{t+1}) − R_G(π_t) + κ̃R_ν(x_t, ν_t)`. -/
noncomputable def uPiM (β κt γ ϕ : ℝ) (ν x π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => κt * ν t ω + (β * S.E t (fun ω => rG (π (t + 1) ω)) ω - rG (π t ω) +
    κt * rMM γ ϕ (ν t ω) (x t ω))

/-- Cochrane (2023), p. 119: marginal revenue less marginal cost at the aggregate price,
`(1 − ε)A + ηB = (ε − 1)Ȳ^{1−γ}(e^{(1+ϕ)x} − e^{(1−γ)x − ν})`. -/
theorem margin_eqM {ε γ ϕ Ybar : ℝ} (hϕ : 1 + ϕ ≠ 0)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) (ν x : ℝ) :
    Ybar ^ (1 - γ) * Real.exp ((1 - γ) * x - ν) * (1 - ε) +
        Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x) / (1 + ϕ) * (ε * (1 + ϕ)) =
      (ε - 1) * Ybar ^ (1 - γ) * mcGapM γ ϕ ν x := by
  have h1 : Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x) / (1 + ϕ) * (ε * (1 + ϕ)) =
      ε * Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x) := by
    field_simp
  rw [h1]
  simp only [mcGapM]
  linear_combination Real.exp ((1 + ϕ) * x) * hss

/-- Cochrane (2023), p. 119: the first-order condition at `q ≡ 0` is the exact nonlinear Phillips
curve with the cost-push shift. -/
theorem symFOC_iff_nonlinPCM {β ε φ γ ϕ Ybar : ℝ} (hφ : φ ≠ 0) (hϕ : 1 + ϕ ≠ 0)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {ν x π : ℕ → Ω → ℝ} {t : ℕ} :
    FOC S β (rotD1 ε (ε * (1 + ϕ)) φ) (rotD2 φ) (yeoDataM γ ϕ Ybar ν x π) (fun _ => 0)
        zeroPlan t ↔
      NonlinPCM S β (kappaT ε φ γ Ybar) γ ϕ ν x π t := by
  have e2 : (fun ω => rotD2 φ (zeroPlan (t + 1) ω) (zeroPlan t ω)
      (yeoDataM γ ϕ Ybar ν x π (t + 1) ω)) = φ • fun ω => gInfl (π (t + 1) ω) := by
    funext ω
    simp [rotD2, zeroPlan, yeoDataM, gInfl, mul_assoc]
  have hE := S.E_smul φ (fun ω => gInfl (π (t + 1) ω)) t
  have hk := kappaT_mul (ε := ε) (γ := γ) (Ybar := Ybar) hφ
  unfold FOC NonlinPCM
  rw [e2, lag_zeroPlan]
  constructor
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2] at h1
    simp only [rotD1, zeroPlan, yeoDataM, mul_zero, sub_zero, Real.exp_zero,
      mul_one, neg_zero, zero_add, Pi.smul_apply, smul_eq_mul] at h1
    rw [show φ * (Real.exp (π t ω) - 1) * Real.exp (π t ω) = φ * gInfl (π t ω) by
      simp only [gInfl]; ring] at h1
    have hm := margin_eqM hϕ hss (ν t ω) (x t ω)
    apply mul_left_cancel₀ hφ
    linear_combination -h1 + hm - mcGapM γ ϕ (ν t ω) (x t ω) * hk
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2]
    simp only [rotD1, zeroPlan, yeoDataM, mul_zero, sub_zero, Real.exp_zero,
      mul_one, neg_zero, zero_add, Pi.smul_apply, smul_eq_mul]
    rw [show φ * (Real.exp (π t ω) - 1) * Real.exp (π t ω) = φ * gInfl (π t ω) by
      simp only [gInfl]; ring]
    have hm := margin_eqM hϕ hss (ν t ω) (x t ω)
    linear_combination hm - φ * h1 - mcGapM γ ϕ (ν t ω) (x t ω) * hk

/-- Cochrane (2023), eq. (17.17), p. 407, **exactly**: the nonlinear curve with the cost-push
shift is (17.17) with slope `κ̃(γ + ϕ)` and disturbance `uPiM`. -/
theorem nonlinPCM_iff_PCM {β κt γ ϕ : ℝ} {ν x π : ℕ → Ω → ℝ} {t : ℕ}
    (hπ1 : Integrable (π (t + 1)) S.μ) (hR : Integrable (fun ω => rG (π (t + 1) ω)) S.μ) :
    NonlinPCM S β κt γ ϕ ν x π t ↔ PCM S β (κt * (γ + ϕ)) (uPiM S β κt γ ϕ ν x π) x π t := by
  have e : (fun ω => gInfl (π (t + 1) ω)) = π (t + 1) + fun ω => rG (π (t + 1) ω) := by
    funext ω
    simp [rG]
  have hE := S.E_add hπ1 hR t
  unfold NonlinPCM PCM
  rw [e]
  constructor
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2, Pi.add_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uPiM, rMM, rG] at h1 ⊢
    linear_combination h1
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2, Pi.add_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uPiM, rMM, rG] at h1 ⊢
    linear_combination h1

/-! ### Regularity and optimality -/

/-- Cochrane (2023), p. 119: the data with the cost-push shift are known at `t` and essentially
bounded at every date when `x`, `π`, `ν` are. -/
theorem yeoDataM_reg {γ ϕ Ybar : ℝ} {ν x π : ℕ → Ω → ℝ} (hν : StronglyAdapted S.𝓕 ν)
    (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (hνb : ∀ t, BddAt S (ν t))
    (hxb : ∀ t, BddAt S (x t)) (hπb : ∀ t, BddAt S (π t)) :
    DataReg S (yeoDataM γ ϕ Ybar ν x π) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have mx : Measurable[S.𝓕 t] (x t) := (hx t).measurable
    have mν : Measurable[S.𝓕 t] (ν t) := (hν t).measurable
    have mπ : Measurable[S.𝓕 t] (π t) := (hπ t).measurable
    exact ((((Real.continuous_exp.measurable.comp ((mx.const_mul (1 - γ)).sub mν)).const_mul
      (Ybar ^ (1 - γ)))).prodMk ((((Real.continuous_exp.measurable.comp
      (mx.const_mul (1 + ϕ))).const_mul (Ybar ^ (1 + ϕ))).div_const (1 + ϕ)).prodMk
      mπ)).stronglyMeasurable
  · have hA : BddAt S (fun ω => Ybar ^ (1 - γ) * Real.exp ((1 - γ) * x t ω - ν t ω)) := by
      have := BddAt.comp (v := Real.exp) Real.continuous_exp
        (((BddAt.const (S := S) (1 - γ)).mul (hxb t)).add (hνb t).neg)
      have := (BddAt.const (S := S) (Ybar ^ (1 - γ))).mul this
      simpa [sub_eq_add_neg] using this
    obtain ⟨K1, hK1⟩ := hA
    obtain ⟨K2, hK2⟩ := BddAt.comp
      (v := fun y => Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * y) / (1 + ϕ)) (by fun_prop) (hxb t)
    obtain ⟨K3, hK3⟩ := hπb t
    refine ⟨max K1 (max K2 K3), ?_⟩
    filter_upwards [hK1, hK2, hK3] with ω h1 h2 h3
    exact norm3_le (h1.trans (le_max_left _ _))
      (h2.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (h3.trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Cochrane (2023), p. 119: with uniformly bounded `x`, `π`, `ν` the data are uniformly
bounded. -/
theorem yeoDataM_ubdd {γ ϕ Ybar : ℝ} {ν x π : ℕ → Ω → ℝ}
    (hL : ∃ L, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L ∧ |ν t ω| ≤ L) :
    ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖yeoDataM γ ϕ Ybar ν x π t ω‖ ≤ K := by
  obtain ⟨L, hL⟩ := hL
  obtain ⟨K1, hK1⟩ := ((isCompact_Icc (a := -L) (b := L)).prod
    (isCompact_Icc (a := -L) (b := L))).exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => Ybar ^ (1 - γ) * Real.exp ((1 - γ) * p.1 - p.2))
    (by fun_prop)
  obtain ⟨K2, -, hK2⟩ := exists_abs_le_of_continuous
    (v := fun y => Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * y) / (1 + ϕ)) (by fun_prop) L
  refine ⟨max K1 (max K2 L), fun t => ?_⟩
  filter_upwards [hL t] with ω h
  have h1 := hK1 (x t ω, ν t ω) ⟨Set.mem_Icc.2 (abs_le.1 h.1), Set.mem_Icc.2 (abs_le.1 h.2.2)⟩
  rw [Real.norm_eq_abs] at h1
  exact norm3_le (h1.trans (le_max_left _ _))
    ((hK2 _ h.1).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (h.2.1.trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Cochrane (2023), p. 119: pricing at the aggregate price lies in the concavity region with
margin `m` when `(ε − 1)e^m ≤ ε(1 + ϕ)e^{(γ+ϕ)x_t + ν_t}` and `e^m/2 ≤ e^{π_t}`. -/
theorem margin_zeroM {ε γ ϕ Ybar m : ℝ} (hε : 1 < ε) (hϕ : 0 ≤ ϕ) (hY : 0 < Ybar)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {ν x π : ℕ → Ω → ℝ}
    (hmx : ∀ t, ∀ᵐ ω ∂S.μ,
      (ε - 1) * Real.exp m ≤ ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω + ν t ω))
    (hmπ : ∀ t, ∀ᵐ ω ∂S.μ, Real.exp m / 2 ≤ Real.exp (π t ω)) :
    Margin S ε (ε * (1 + ϕ)) (yeoDataM γ ϕ Ybar ν x π) (fun _ => 0) zeroPlan m := by
  intro t
  filter_upwards [hmx t, hmπ t] with ω h1 h2
  refine ⟨?_, by simpa [zeroPlan, lag_zeroPlan, yeoDataM] using h2⟩
  simp only [yeoDataM, zeroPlan, mul_zero, Real.exp_zero, mul_one]
  set Y1 := Ybar ^ (1 - γ)
  set X := x t ω
  set V := ν t ω
  have hY1 : 0 < Y1 := Real.rpow_pos_of_pos hY _
  have h1ϕ : (0 : ℝ) < 1 + ϕ := by linarith
  have hB : (ε * (1 + ϕ)) ^ 2 * (Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * X) / (1 + ϕ)) =
      ε * (1 + ϕ) * ((ε - 1) * Y1) * Real.exp ((1 + ϕ) * X) := by
    have e0 : (ε * (1 + ϕ)) ^ 2 * (Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * X) / (1 + ϕ)) =
        ε * (1 + ϕ) * Real.exp ((1 + ϕ) * X) * (ε * Ybar ^ (1 + ϕ)) := by
      field_simp
    rw [e0, hss]
    ring
  rw [hB]
  have hsplit : Real.exp ((1 + ϕ) * X) =
      Real.exp ((γ + ϕ) * X + V) * Real.exp ((1 - γ) * X - V) := by
    rw [← Real.exp_add]
    ring_nf
  have hmm : Real.exp (-m) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
  have hc : 0 ≤ Real.exp (-m) * (ε - 1) * Y1 * Real.exp ((1 - γ) * X - V) := by
    have := Real.exp_pos (-m)
    have := Real.exp_pos ((1 - γ) * X - V)
    have : 0 ≤ ε - 1 := by linarith
    positivity
  have h3 := mul_le_mul_of_nonneg_left h1 hc
  rw [hsplit]
  have e1 : Real.exp (-m) * (ε - 1) * Y1 * Real.exp ((1 - γ) * X - V) *
      ((ε - 1) * Real.exp m) = (ε - 1) ^ 2 * (Y1 * Real.exp ((1 - γ) * X - V)) := by
    linear_combination ((ε - 1) ^ 2 * Y1 * Real.exp ((1 - γ) * X - V)) * hmm
  have e2 : Real.exp (-m) * (ε - 1) * Y1 * Real.exp ((1 - γ) * X - V) *
      (ε * (1 + ϕ) * Real.exp ((γ + ϕ) * X + V)) =
        Real.exp (-m) * (ε * (1 + ϕ) * ((ε - 1) * Y1) *
          (Real.exp ((γ + ϕ) * X + V) * Real.exp ((1 - γ) * X - V))) := by ring
  linarith

/-- Cochrane (2023), eq. (17.17), p. 407, with a cost-push shift, **necessity over all plans**:
if pricing at the aggregate price is optimal among all plans, (17.17) holds at every date with
the disturbance `uPiM`. -/
theorem PC_of_optimalM {β ε φ γ ϕ Ybar : ℝ} (hβ : 0 < β) (hφ : φ ≠ 0) (hϕ : 1 + ϕ ≠ 0)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {ν x π : ℕ → Ω → ℝ}
    (hν : StronglyAdapted S.𝓕 ν) (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π)
    (hνb : ∀ t, BddAt S (ν t)) (hxb : ∀ t, BddAt S (x t)) (hπb : ∀ t, BddAt S (π t))
    (hopt : OptimalIn S (Plan S) β (rotPay ε (ε * (1 + ϕ)) φ) (yeoDataM γ ϕ Ybar ν x π)
      (fun _ => 0) zeroPlan) (t : ℕ) :
    PCM S β (kappaT ε φ γ Ybar * (γ + ϕ)) (uPiM S β (kappaT ε φ γ Ybar) γ ϕ ν x π) x π t := by
  have hfoc := foc_of_optimal hβ (rot_smooth ε (ε * (1 + ϕ)) φ)
    (yeoDataM_reg hν hx hπ hνb hxb hπb) stronglyMeasurable_const (BddAt.const 0) hopt t
  have hπi : Integrable (π (t + 1)) S.μ :=
    (hπb (t + 1)).integrable ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable
  have hRi : Integrable (fun ω => rG (π (t + 1) ω)) S.μ :=
    (BddAt.comp (v := rG) (by unfold rG gInfl; fun_prop) (hπb (t + 1))).integrable
      ((by unfold rG gInfl; fun_prop : Continuous rG).comp_aestronglyMeasurable
        ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable)
  exact (nonlinPCM_iff_PCM hπi hRi).1 ((symFOC_iff_nonlinPCM hφ hϕ hss).1 hfoc)

/-- Cochrane (2023), eq. (17.17), p. 407, with a cost-push shift, **necessity and
sufficiency**: under the hypotheses of `TidyR6RotembergPC.optimal_iff_PC` (with `ν` adapted, all
of `x`, `π`, `ν` uniformly bounded, and the margin conditions of `margin_zeroM`), pricing at the
aggregate price is optimal among the plans of the concavity region iff (17.17) holds at every
date with the disturbance `uPiM`. -/
theorem optimal_iff_PCM {β ε φ γ ϕ Ybar m : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hε : 1 < ε)
    (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (hY : 0 < Ybar) (hm : 0 < m)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {ν x π : ℕ → Ω → ℝ}
    (hν : StronglyAdapted S.𝓕 ν) (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π)
    (hL : ∃ L, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L ∧ |ν t ω| ≤ L)
    (hmx : ∀ t, ∀ᵐ ω ∂S.μ,
      (ε - 1) * Real.exp m ≤ ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω + ν t ω))
    (hmπ : ∀ t, ∀ᵐ ω ∂S.μ, Real.exp m / 2 ≤ Real.exp (π t ω)) :
    OptimalIn S (RPlan S ε (ε * (1 + ϕ)) (yeoDataM γ ϕ Ybar ν x π) (fun _ => 0)) β
        (rotPay ε (ε * (1 + ϕ)) φ) (yeoDataM γ ϕ Ybar ν x π) (fun _ => 0) zeroPlan ↔
      ∀ t, PCM S β (kappaT ε φ γ Ybar * (γ + ϕ)) (uPiM S β (kappaT ε φ γ Ybar) γ ϕ ν x π)
        x π t := by
  obtain ⟨L, hLb⟩ := hL
  have hxb : ∀ t, BddAt S (x t) := fun t => ⟨L, (hLb t).mono fun _ h => h.1⟩
  have hπb : ∀ t, BddAt S (π t) := fun t => ⟨L, (hLb t).mono fun _ h => h.2.1⟩
  have hνb : ∀ t, BddAt S (ν t) := fun t => ⟨L, (hLb t).mono fun _ h => h.2.2⟩
  have hθ := yeoDataM_reg (γ := γ) (ϕ := ϕ) (Ybar := Ybar) hν hx hπ hνb hxb hπb
  have hθu := yeoDataM_ubdd (γ := γ) (ϕ := ϕ) (Ybar := Ybar) ⟨L, hLb⟩
  have hA : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ (yeoDataM γ ϕ Ybar ν x π t ω).1 := fun t =>
    Eventually.of_forall fun ω => by
      simp only [yeoDataM]
      exact mul_nonneg (Real.rpow_pos_of_pos hY _).le (Real.exp_pos _).le
  have hη : 0 ≤ 1 - ε + ε * (1 + ϕ) := by nlinarith
  rw [optimal_iff_foc_region hβ hβ1 hη hφ.le hm hθ hθu hA stronglyMeasurable_const
    (BddAt.const 0) uplan_zero (margin_zeroM hε hϕ hY hss hmx hmπ)
    (admissible_zero hβ.le hβ1 hθ hθu)]
  refine forall_congr' fun t => ?_
  have hπi : Integrable (π (t + 1)) S.μ :=
    (hπb (t + 1)).integrable ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable
  have hRi : Integrable (fun ω => rG (π (t + 1) ω)) S.μ :=
    (BddAt.comp (v := rG) (by unfold rG gInfl; fun_prop) (hπb (t + 1))).integrable
      ((by unfold rG gInfl; fun_prop : Continuous rG).comp_aestronglyMeasurable
        ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable)
  rw [symFOC_iff_nonlinPCM hφ.ne' (by linarith) hss, nonlinPCM_iff_PCM hπi hRi]

/-! ### Finite event trees -/

namespace Tree

open ExpectationsFiniteTree TreeBridge TidyR6HouseholdMeasureTVC.Link

variable {Ω' : Type*}

/-- Cochrane (2023), eq. (17.17), p. 407, for a core expectation system: the disturbance
`u_{π,t} = κ̃ν_t + βE_tR_G(π_{t+1}) − R_G(π_t) + κ̃R_ν(x_t, ν_t)`. -/
noncomputable def coreUPiM (𝔼 : ExpectationSystem Ω') (β κt γ ϕ : ℝ) (ν x π : ℕ → Ω' → ℝ) :
    ℕ → Ω' → ℝ :=
  fun t ω => κt * ν t ω + (β * 𝔼.E t (fun ω => rG (π (t + 1) ω)) ω - rG (π t ω) +
    κt * rMM γ ϕ (ν t ω) (x t ω))

variable [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω'] (T : FiniteTree Ω')

/-- Cochrane (2023), eq. (17.17), p. 407: on a finite tree, the almost-sure Phillips curve with
the cost-push disturbance is the project's `FullModel.PC`, in every state. -/
theorem PCM_iff_PC_M (β κt γ ϕ : ℝ) (ν x π : ℕ → Ω' → ℝ) :
    (∀ t, PCM (treeSystem T) β (κt * (γ + ϕ)) (uPiM (treeSystem T) β κt γ ϕ ν x π) x π t) ↔
      FullModel.PC T.toExpectationSystem β (κt * (γ + ϕ))
        (coreUPiM T.toExpectationSystem β κt γ ϕ ν x π) x π := by
  constructor
  · intro h t
    rw [(treeSystem T).eq_of_ae_eq (treeSystem_fullSupport T) (h t)]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uPiM, coreUPiM, treeE]
  · intro h t
    refine Eventually.of_forall fun ω => ?_
    rw [h t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uPiM, coreUPiM, treeE]

end Tree

end Cochrane.KeynesianStickyPrices.TidyR6ShockPC
