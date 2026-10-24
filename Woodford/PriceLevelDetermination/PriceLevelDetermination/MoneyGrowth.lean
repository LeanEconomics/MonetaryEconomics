/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.ForwardSolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue

/-!
# Money-growth targeting in the Sidrauski–Brock model

Woodford (2003), *Interest and Prices*, Chapter 2, §3.1–3.3, pp. 101–111, and Appendix A,
§A.11, pp. 644–645.

## The nonlinear model

* (3.2), p. 103: `foc_money_eq` (with positive money balances the complementary-slackness
  condition gives `u_m/u_c = Δ`).
* (3.5), p. 104 and fn 38: with `u_m/u_c` strictly increasing in consumption and strictly
  decreasing in real balances (the normal-goods hypothesis, stated as this monotonicity), the
  money-demand equation `u_m/u_c (Y, m) = Δ` has at most one positive solution (`lm_unique`),
  has one under the boundary conditions of fn 38 (`lm_exists`), and the solution
  `m = L(Y, Δ)` is increasing in `Y` (`lm_mono_income`) and decreasing in `Δ`
  (`lm_anti_spread`). (3.8), p. 109: the implied interest rate is increasing in `P/M`
  (`liquidity_preference_mono`).
* (3.6), p. 107: the log-linear money demand is the exact derivative of the nonlinear relation
  at the steady state (`hasFDerivAt_moneyDemand`), with the factor `1 − Δ̄` coming from
  `Δ = 1 − β(1 + iᵐ)/(1 + i)`; the signs `η_y > 0`, `η_i > 0` follow from the strict
  monotonicity of `u_m/u_c` by differentiating the identity `u_m/u_c(Y, L(Y, Δ)) = Δ`
  (`lm_partials`, `eta_pos`).

## The linear model and Proposition 2.11

* `MGEquilibrium`: (1.32) and (3.6). `lm_iff_cagan` is (A.28), `cagan_iff_scalar` is (A.29).
* `prop_2_11`: for bounded adapted exogenous processes and bounded money growth, there is
  exactly one equilibrium with bounded real balances and interest rate (A.30).
* `prop_2_11_priceLevel`: the price level is (3.7), a genuine infinite sum
  `log P_t = ∑ ϕ_j E_t[log M_{t+j} − η_i log(1 + iᵐ_{t+j}) − u_{t+j}] − log m̄`, although
  `log M` itself need not be bounded (summation by parts, `abel_tsum`);
  `phi_pos`, `hasSum_phi` give `ϕ_j > 0`, `∑ ϕ_j = 1`.
* (3.8), p. 109: `lm_iff_wicksell` — the money-demand relation is exactly a Wicksellian rule
  with `φ_p = 1/η_i`, `P* = M/m̄`, `ν = îᵐ + η_i⁻¹(η_y Ŷ + εᵐ)`; `phi_eq_wicksell_weight` and
  `priceLevel_eq_wicksell` show (3.7) is (1.39) for that rule.
* (3.9), p. 110: `wicksell_iff_moneyFeedback`. p. 110: `mgEquilibrium_composite` (only
  `log M − η_i log(1 + iᵐ)` matters). p. 106: `exists_unique_money` (with separable utility
  the money-demand relation only pins down the instruments).

## General tools (from `ForwardSolution`)

* `ForwardSolution.ScalarEq`, `ForwardSolution.scalarSol`,
  `ForwardSolution.scalar_existsUnique`: the equation `A z_t = B E_t z_{t+1} + f_t` (the form
  (A.14), p. 636) has, for every bounded adapted `f`, exactly one bounded solution iff
  `|B| < |A|` (Lemma A.14 / survey L1, L4).
* `ForwardSolution.abel_tsum`: summation by parts for geometric weights and sequences with
  bounded increments (survey L2).

The nonlinear local-determinacy claim (A.3, the implicit function theorem on `ℓ∞`) is not
formalised: as in the rest of the project the linear model is studied exactly.
-/

namespace Woodford.PriceLevelDetermination.MoneyGrowth

open Filter Topology
open Woodford.PriceLevelDetermination.ForwardSolution (ScalarEq scalarSol scalarSol_apply
  scalar_existsUnique abel_tsum summable_geom_mul)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The nonlinear money-demand relation (3.2)–(3.5), (3.8) -/

/-- Woodford (2003), (3.2), p. 103: when money balances are positive, the complementary-slackness
condition `(Δ − u_m/u_c) M = 0` of the household's first-order conditions gives `u_m/u_c = Δ`. -/
theorem foc_money_eq {ratio Δ M : ℝ} (hslack : (Δ - ratio) * M = 0) (hM : 0 < M) :
    ratio = Δ := by
  rcases mul_eq_zero.mp hslack with h | h
  · linarith
  · linarith

/-- Woodford (2003), (3.5), p. 104: if `u_m/u_c` is strictly decreasing in real balances (normal
goods), the money-demand equation `u_m/u_c(Y, m) = Δ` has at most one positive solution `m`. -/
theorem lm_unique {R : ℝ → ℝ} (hanti : StrictAntiOn R (Set.Ioi 0)) {Δ m₁ m₂ : ℝ}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (e₁ : R m₁ = Δ) (e₂ : R m₂ = Δ) : m₁ = m₂ :=
  hanti.injOn h₁ h₂ (e₁.trans e₂.symm)

/-- Woodford (2003), (3.5), p. 104 and fn 38: under the boundary conditions of fn 38 (`u_m/u_c`
unboundedly large as real balances vanish and arbitrarily small for large balances) and
continuity, the money-demand equation `u_m/u_c(Y, m) = Δ` has a positive solution for every
`Δ > 0`. -/
theorem lm_exists {R : ℝ → ℝ} (hcont : ContinuousOn R (Set.Ioi 0))
    (h0 : Tendsto R (𝓝[>] 0) atTop) (hinf : Tendsto R atTop (𝓝 0)) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ m, 0 < m ∧ R m = Δ := by
  have e₁ : ∀ᶠ m in 𝓝[>] (0 : ℝ), Δ < R m ∧ m ∈ Set.Ioi 0 :=
    (h0.eventually (eventually_gt_atTop Δ)).and self_mem_nhdsWithin
  have e₂ : ∀ᶠ m in atTop, R m < Δ ∧ 0 < m :=
    (hinf.eventually (gt_mem_nhds hΔ)).and (eventually_gt_atTop 0)
  obtain ⟨m₁, hR₁, hm₁⟩ := e₁.exists
  obtain ⟨m₂, hR₂, hm₂⟩ := e₂.exists
  have hsub : Set.uIcc m₁ m₂ ⊆ Set.Ioi 0 := fun x hx => by
    rcases Set.mem_uIcc.mp hx with h | h
    · exact lt_of_lt_of_le (Set.mem_Ioi.mp hm₁) h.1
    · exact lt_of_lt_of_le hm₂ h.1
  have hmem : Δ ∈ Set.uIcc (R m₁) (R m₂) := Set.mem_uIcc.mpr (Or.inr ⟨hR₂.le, hR₁.le⟩)
  obtain ⟨m, hm, hRm⟩ := intermediate_value_uIcc (hcont.mono hsub) hmem
  exact ⟨m, hsub hm, hRm⟩

/-- Woodford (2003), (3.5), p. 104: with `u_m/u_c` strictly increasing in consumption and strictly
decreasing in real balances (normal goods), equilibrium real balances `L(Y, Δ)` are strictly
increasing in income `Y`. -/
theorem lm_mono_income {R : ℝ → ℝ → ℝ}
    (hc : ∀ m, 0 < m → StrictMonoOn (fun c => R c m) (Set.Ioi 0))
    (hm : ∀ c, 0 < c → StrictAntiOn (R c) (Set.Ioi 0)) {c c' m m' Δ : ℝ} (hc0 : 0 < c)
    (hcc : c < c') (hm0 : 0 < m) (hm0' : 0 < m') (e : R c m = Δ) (e' : R c' m' = Δ) :
    m < m' := by
  by_contra h
  push Not at h
  have h1 : R c m < R c' m := hc m hm0 hc0 (lt_trans hc0 hcc) hcc
  have h2 : R c' m ≤ R c' m' := (hm c' (lt_trans hc0 hcc)).antitoneOn hm0' hm0 h
  linarith

/-- Woodford (2003), (3.5), p. 104: equilibrium real balances `L(Y, Δ)` are strictly decreasing in
the interest differential `Δ`. -/
theorem lm_anti_spread {R : ℝ → ℝ} (hm : StrictAntiOn R (Set.Ioi 0)) {m m' Δ Δ' : ℝ}
    (hm0 : 0 < m) (hm0' : 0 < m') (hΔ : Δ < Δ') (e : R m = Δ) (e' : R m' = Δ') : m' < m := by
  by_contra h
  push Not at h
  have := hm.antitoneOn hm0 hm0' h
  linarith

/-- Woodford (2003), (3.8), p. 109 (Keynes's liquidity-preference theory): if money demand
`ℓ(Δ) = L(Y, Δ; ξ)` is strictly decreasing in the differential `Δ = (i − iᵐ)/(1 + i)`, then the
interest rate `i = ι(P/M; iᵐ, Y, ξ)` that clears the money market is strictly increasing in the
price level. -/
theorem liquidity_preference_mono {ℓ : ℝ → ℝ} (hℓ : StrictAntiOn ℓ (Set.Ioi 0))
    {im i i' M P P' : ℝ} (him : -1 < im) (hi : im < i) (hi' : im < i') (hM : 0 < M)
    (hP : 0 < P) (hPP : P < P') (e : ℓ ((i - im) / (1 + i)) = M / P)
    (e' : ℓ ((i' - im) / (1 + i')) = M / P') : i < i' := by
  have hs : 0 < (i - im) / (1 + i) := div_pos (by linarith) (by linarith)
  have hs' : 0 < (i' - im) / (1 + i') := div_pos (by linarith) (by linarith)
  have hm : M / P' < M / P := div_lt_div_of_pos_left hM hP hPP
  have hlt : (i - im) / (1 + i) < (i' - im) / (1 + i') := by
    by_contra h
    push Not at h
    have := hℓ.antitoneOn hs' hs h
    linarith
  by_contra h
  push Not at h
  rw [div_lt_div_iff₀ (by linarith) (by linarith)] at hlt
  nlinarith

/-- Woodford (2003), (3.6), p. 107: the interest differential `Δ = 1 − (1 + iᵐ)/(1 + i)` in terms
of the log deviations `î = log((1 + i)/(1 + ī))`, `îᵐ = log((1 + iᵐ)/(1 + īᵐ))`, where
`1 + ī = β⁻¹` and `Δ̄ = 1 − β(1 + īᵐ)`. -/
noncomputable def spread (Δbar ihat imhat : ℝ) : ℝ := 1 - (1 - Δbar) * Real.exp (imhat - ihat)

/-- Woodford (2003), p. 106–107: with `1 + i = β⁻¹ e^{î}` and `1 + iᵐ = (1 + īᵐ) e^{îᵐ}`,
`(i − iᵐ)/(1 + i) = spread Δ̄ î îᵐ` for `Δ̄ = 1 − β(1 + īᵐ)`. -/
theorem spread_eq {β ibm ih imh : ℝ} (hβ : 0 < β) :
    ((β⁻¹ * Real.exp ih - 1) - ((1 + ibm) * Real.exp imh - 1)) / (1 + (β⁻¹ * Real.exp ih - 1)) =
      spread (1 - β * (1 + ibm)) ih imh := by
  unfold spread
  rw [Real.exp_sub]
  have := Real.exp_pos ih
  field_simp
  ring

/-- Woodford (2003), (3.6), p. 107: a linear functional on `ℝ³` is determined by its values on
the coordinate vectors (used to read off the partial derivatives of `L`). -/
theorem clm3_apply (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (a b c : ℝ) :
    L' (a, b, c) = a * L' (1, 0, 0) + b * L' (0, 1, 0) + c * L' (0, 0, 1) := by
  have h : ((a, b, c) : ℝ × ℝ × ℝ) = a • (1, 0, 0) + b • (0, 1, 0) + c • (0, 0, 1) := by
    ext <;> simp
  rw [h, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- Woodford (2003), (3.6), p. 107: a linear functional on `ℝ²` is determined by its values on
the coordinate vectors. -/
theorem clm2_apply (R' : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    R' (a, b) = a * R' (1, 0) + b * R' (0, 1) := by
  have h : ((a, b) : ℝ × ℝ) = a • (1, 0) + b • (0, 1) := by ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Woodford (2003), (3.6), p. 107: log real money demand `log(L(Ȳ e^{ŷ}, Δ(î, îᵐ), ξ)/m̄)` as a
function of the log deviations `(ŷ, î, îᵐ, ξ)`. -/
noncomputable def moneyDemandLog (L : ℝ × ℝ × ℝ → ℝ) (Ybar mbar Δbar : ℝ)
    (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  Real.log (L (Ybar * Real.exp x.1, spread Δbar x.2.1 x.2.2.1, x.2.2.2)) - Real.log mbar

/-- Woodford (2003), (3.6), p. 107: the income elasticity `η_y = (Ȳ/m̄) ∂L/∂Y`. -/
noncomputable def etaY (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (Ybar mbar : ℝ) : ℝ := Ybar / mbar * L' (1, 0, 0)

/-- Woodford (2003), (3.6), p. 107: the interest semielasticity `η_i = −((1 − Δ̄)/m̄) ∂L/∂Δ`. -/
noncomputable def etaI (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (mbar Δbar : ℝ) : ℝ :=
  -((1 - Δbar) / mbar * L' (0, 1, 0))

/-- Woodford (2003), (3.6), p. 107: the coefficient `(1/m̄) ∂L/∂ξ` of the money-demand
disturbance `εᵐ`. -/
noncomputable def epsCoef (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (mbar : ℝ) : ℝ := L' (0, 0, 1) / mbar

/-- Woodford (2003), (3.6), p. 107 (exact derivative): if `L` is differentiable at the steady
state `(Ȳ, Δ̄, 0)` with `L(Ȳ, Δ̄, 0) = m̄ > 0`, then the derivative of log real money demand in the
log deviations `(ŷ, î, îᵐ, ξ)` at zero is `η_y ŷ − η_i(î − îᵐ) + (1/m̄) L_ξ ξ`. -/
theorem hasFDerivAt_moneyDemand {L : ℝ × ℝ × ℝ → ℝ} {L' : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    {Ybar mbar Δbar : ℝ} (hL : HasFDerivAt L L' (Ybar, Δbar, 0))
    (hss : L (Ybar, Δbar, 0) = mbar) (hm : 0 < mbar) :
    ∃ G' : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (moneyDemandLog L Ybar mbar Δbar) G' 0 ∧
      ∀ v, G' v = etaY L' Ybar mbar * v.1 - etaI L' mbar Δbar * (v.2.1 - v.2.2.1) +
        epsCoef L' mbar * v.2.2.2 := by
  let P1 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)
  let P2 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))
  let P3 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
  let P4 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
  have hY := (P1.hasFDerivAt (x := 0)).exp.const_mul Ybar
  have hS := (((P3.hasFDerivAt (x := 0)).sub (P2.hasFDerivAt (x := 0))).exp.const_mul
    (1 - Δbar)).const_sub 1
  have hg := hY.prodMk (hS.prodMk (P4.hasFDerivAt (x := 0)))
  have hg0 : ((Ybar * Real.exp (P1 0), 1 - (1 - Δbar) * Real.exp (P3 0 - P2 0), P4 0) :
      ℝ × ℝ × ℝ) = (Ybar, Δbar, 0) := by simp
  rw [← hg0] at hL
  have hc := hL.comp (0 : ℝ × ℝ × ℝ × ℝ) hg
  have hne : (L ∘ fun x => (Ybar * Real.exp (P1 x), 1 - (1 - Δbar) * Real.exp (P3 x - P2 x),
      P4 x)) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    rw [hg0, hss]
    exact hm.ne'
  have hlog := (hc.log hne).sub_const (Real.log mbar)
  refine ⟨_, hlog, fun v => ?_⟩
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_eq_mul]
  rw [clm3_apply]
  simp [P1, P2, P3, P4, etaY, etaI, epsCoef, hss]
  field_simp
  ring

/-- Woodford (2003), (3.5)–(3.6), pp. 104–107 (signs by implicit differentiation): if
`R = u_m/u_c` is differentiable at `(Ȳ, m̄)` and the money-demand function solves
`R(Y, L(Y, Δ, 0)) = Δ` near `(Ȳ, Δ̄)`, then `R_c + R_m L_Y = 0` and `R_m L_Δ = 1`. -/
theorem lm_partials {R : ℝ × ℝ → ℝ} {R' : ℝ × ℝ →L[ℝ] ℝ} {L : ℝ × ℝ × ℝ → ℝ}
    {L' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {Ybar Δbar : ℝ} (hR : HasFDerivAt R R' (Ybar, L (Ybar, Δbar, 0)))
    (hL : HasFDerivAt L L' (Ybar, Δbar, 0))
    (hid : ∀ᶠ y in 𝓝 ((Ybar, Δbar) : ℝ × ℝ), R (y.1, L (y.1, y.2, 0)) = y.2) :
    R' (1, 0) + R' (0, 1) * L' (1, 0, 0) = 0 ∧ R' (0, 1) * L' (0, 1, 0) = 1 := by
  let Q : ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0)
  have hq : HasFDerivAt (fun y : ℝ × ℝ => ((y.1, y.2, 0) : ℝ × ℝ × ℝ)) Q (Ybar, Δbar) :=
    Q.hasFDerivAt
  have hLq := hL.comp ((Ybar, Δbar) : ℝ × ℝ) hq
  have hh := (hasFDerivAt_fst (p := ((Ybar, Δbar) : ℝ × ℝ))).prodMk hLq
  have hk := hR.comp ((Ybar, Δbar) : ℝ × ℝ) hh
  have hk2 : HasFDerivAt (fun y : ℝ × ℝ => R (y.1, L (y.1, y.2, 0)))
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar, Δbar) :=
    (hasFDerivAt_snd (p := ((Ybar, Δbar) : ℝ × ℝ))).congr_of_eventuallyEq hid
  have heq := hk.unique hk2
  have e1 := congrArg (fun F : ℝ × ℝ →L[ℝ] ℝ => F (1, 0)) heq
  have e2 := congrArg (fun F : ℝ × ℝ →L[ℝ] ℝ => F (0, 1)) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Q] at e1 e2
  simp only [zero_apply] at e1 e2
  rw [clm2_apply] at e1 e2
  simp only [zero_mul, one_mul, zero_add] at e1 e2
  constructor
  · linarith
  · linarith

/-- Woodford (2003), (3.6), p. 107: the signs `η_y > 0`, `η_i > 0`. They follow from the
normal-goods hypothesis in derivative form — `u_m/u_c` strictly increasing in consumption
(`R_c > 0`) and strictly decreasing in real balances (`R_m < 0`) at the steady state — through
`lm_partials`, given `Ȳ, m̄ > 0` and `Δ̄ < 1`. -/
theorem eta_pos {R' : ℝ × ℝ →L[ℝ] ℝ} {L' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {Ybar mbar Δbar : ℝ}
    (h1 : R' (1, 0) + R' (0, 1) * L' (1, 0, 0) = 0) (h2 : R' (0, 1) * L' (0, 1, 0) = 1)
    (hRc : 0 < R' (1, 0)) (hRm : R' (0, 1) < 0) (hY : 0 < Ybar) (hm : 0 < mbar)
    (hΔ : Δbar < 1) : 0 < etaY L' Ybar mbar ∧ 0 < etaI L' mbar Δbar := by
  have hLY : 0 < L' (1, 0, 0) := by
    by_contra h
    push Not at h
    nlinarith
  have hLD : L' (0, 1, 0) < 0 := by
    by_contra h
    push Not at h
    nlinarith
  unfold etaY etaI
  constructor
  · positivity
  · have : 0 < (1 - Δbar) / mbar := div_pos (by linarith) hm
    nlinarith

/-! ### The log-linear model (1.32), (3.6) and Proposition 2.11 -/

/-- Woodford (2003), eq. (1.32), p. 79: `î_t = r̂_t + E_t π_{t+1}`, with `π_{t+1} = log P_{t+1} −
log P_t` and `p = log P` (the date-`t` price level is known at `t`). -/
def Fisher (r p i : ℕ → Ω → ℝ) : Prop := ∀ t, i t = r t + 𝔼.E t (p (t + 1)) - p t

/-- Woodford (2003), eq. (3.6), p. 107: `m̂_t = η_y Ŷ_t − η_i(î_t − îᵐ_t) + εᵐ_t`, with
`m̂_t = log M_t − log P_t − log m̄` and `îᵐ_t = log(1 + iᵐ_t) − log(1 + īᵐ)`; `M = log Mˢ`,
`l = log(1 + iᵐ)`, `lmbar = log m̄`, `lbar = log(1 + īᵐ)`. -/
def LM (ηy ηi lmbar lbar : ℝ) (M l Y e p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, M t - p t - (fun _ => lmbar) = ηy • Y t - ηi • (i t - (l t - fun _ => lbar)) + e t

/-- Woodford (2003), §3.3, p. 107: an equilibrium of the log-linear model under exogenous
`{Mˢ, iᵐ}`: (1.32) and (3.6). -/
def MGEquilibrium (ηy ηi lmbar lbar : ℝ) (M l Y r e p i : ℕ → Ω → ℝ) : Prop :=
  Fisher 𝔼 r p i ∧ LM ηy ηi lmbar lbar M l Y e p i

/-- Woodford (2003), Prop. 2.11, p. 108: the composite disturbance
`u_t = η_y Ŷ_t − η_i r̂_t + εᵐ_t − η_i log(1 + īᵐ)`. -/
def uComp (ηy ηi lbar : ℝ) (Y r e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ηy • Y t - ηi • r t + e t - fun _ => ηi * lbar

/-- Woodford (2003), eq. (A.28), p. 644 (the Cagan form):
`m̂_t = −η_i E_t π_{t+1} + u_t + η_i log(1 + iᵐ_t)`. -/
def Cagan (ηy ηi lmbar lbar : ℝ) (M l Y r e p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, M t - p t - (fun _ => lmbar) =
    -ηi • (𝔼.E t (p (t + 1)) - p t) + uComp ηy ηi lbar Y r e t + ηi • l t

/-- Woodford (2003), (A.28), p. 644 and fn 42, p. 108: given the Fisher equation (1.32), the
money-demand relation (3.6) is equivalent to the Cagan relation (A.28). -/
theorem lm_iff_cagan {ηy ηi lmbar lbar : ℝ} {M l Y r e p i : ℕ → Ω → ℝ}
    (hF : Fisher 𝔼 r p i) :
    LM ηy ηi lmbar lbar M l Y e p i ↔ Cagan 𝔼 ηy ηi lmbar lbar M l Y r e p := by
  have key : ∀ t, ηy • Y t - ηi • (i t - (l t - fun _ => lbar)) + e t =
      -ηi • (𝔼.E t (p (t + 1)) - p t) + uComp ηy ηi lbar Y r e t + ηi • l t := by
    intro t
    rw [hF t]
    funext ω
    simp only [uComp, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold LM Cagan
  simp only [key]

/-- Woodford (2003), (A.29), p. 645: the forcing term
`u_t + η_i log(1 + iᵐ_t) − η_i E_t μ_{t+1}`, `μ_{t+1} = log M_{t+1} − log M_t`. -/
def fMG (ηy ηi lbar : ℝ) (M l Y r e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => uComp ηy ηi lbar Y r e t + ηi • l t - ηi • (𝔼.E t (M (t + 1)) - M t)

/-- Woodford (2003), (A.27)–(A.29), pp. 644–645: the Cagan relation is the scalar equation
`(1 + η_i) m̂_t = η_i E_t m̂_{t+1} + f_t` for real balances `m̂ = log M − log P − log m̄`,
i.e. (A.29) with `α = η_i/(1 + η_i)`. -/
theorem cagan_iff_scalar {ηy ηi lmbar lbar : ℝ} {M l Y r e p : ℕ → Ω → ℝ} :
    Cagan 𝔼 ηy ηi lmbar lbar M l Y r e p ↔
      ScalarEq 𝔼 (1 + ηi) ηi (fMG 𝔼 ηy ηi lbar M l Y r e)
        (fun t => M t - p t - fun _ => lmbar) := by
  unfold Cagan ScalarEq fMG
  refine forall_congr' fun t => ?_
  have hE : 𝔼.E t (M (t + 1) - p (t + 1) - fun _ => lmbar) =
      𝔼.E t (M (t + 1)) - 𝔼.E t (p (t + 1)) - fun _ => lmbar := by
    rw [map_sub, map_sub, 𝔼.const]
  rw [hE, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    linear_combination (1 + ηi) * h - ηi * h
  · intro h
    linear_combination h

/-- Woodford (2003), (A.30), p. 645: the equilibrium price level `log P = log M − m̂ − log m̄`,
with `m̂` the forward solution of (A.29). -/
noncomputable def mgPrice (ηy ηi lmbar lbar : ℝ) (M l Y r e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => M t - scalarSol 𝔼 (1 + ηi) ηi (fMG 𝔼 ηy ηi lbar M l Y r e) t - fun _ => lmbar

/-- Woodford (2003), (3.6), p. 107: the equilibrium interest rate, from (1.32). -/
noncomputable def mgRate (ηy ηi lmbar lbar : ℝ) (M l Y r e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => r t + 𝔼.E t (mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e (t + 1)) -
    mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e t

/-- Woodford (2003), Prop. 2.11, pp. 644–645: the forcing term of (A.29) is bounded and adapted
when `Ŷ, r̂, εᵐ, iᵐ` are bounded and adapted and money growth is bounded. -/
theorem fMG_bounded_adapted {ηy ηi lbar KY Kr Ke Kl KM : ℝ} {M l Y r e : ℕ → Ω → ℝ}
    (hY : ∀ t ω, |Y t ω| ≤ KY) (hr : ∀ t ω, |r t ω| ≤ Kr) (he : ∀ t ω, |e t ω| ≤ Ke)
    (hl : ∀ t ω, |l t ω| ≤ Kl) (hM : ∀ t ω, |M (t + 1) ω - M t ω| ≤ KM)
    (haY : 𝔼.Adapted Y) (har : 𝔼.Adapted r) (hae : 𝔼.Adapted e) (hal : 𝔼.Adapted l)
    (haM : 𝔼.Adapted M) :
    (∀ t ω, |fMG 𝔼 ηy ηi lbar M l Y r e t ω| ≤
      |ηy| * KY + |ηi| * Kr + Ke + |ηi * lbar| + |ηi| * Kl + |ηi| * KM) ∧
      𝔼.Adapted (fMG 𝔼 ηy ηi lbar M l Y r e) := by
  have hEM : ∀ t, 𝔼.E t (M (t + 1)) - M t = 𝔼.E t (M (t + 1) - M t) := fun t => by
    rw [map_sub, haM t]
  constructor
  · intro t ω
    have h1 : |(𝔼.E t (M (t + 1)) - M t) ω| ≤ KM := by
      rw [hEM t]
      exact 𝔼.abs_E_le (fun ω' => hM t ω') t ω
    simp only [fMG, uComp, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    have := hY t ω; have := hr t ω; have := he t ω; have := hl t ω
    calc |ηy * Y t ω - ηi * r t ω + e t ω - ηi * lbar + ηi * l t ω -
          ηi * (𝔼.E t (M (t + 1)) ω - M t ω)|
        ≤ |ηy * Y t ω| + |ηi * r t ω| + |e t ω| + |ηi * lbar| + |ηi * l t ω| +
          |ηi * (𝔼.E t (M (t + 1)) ω - M t ω)| := by
          have a2 := abs_add_le (ηy * Y t ω - ηi * r t ω) (e t ω)
          have a3 := abs_sub (ηy * Y t ω - ηi * r t ω + e t ω) (ηi * lbar)
          have a4 := abs_add_le (ηy * Y t ω - ηi * r t ω + e t ω - ηi * lbar) (ηi * l t ω)
          have a5 := abs_sub (ηy * Y t ω - ηi * r t ω + e t ω - ηi * lbar + ηi * l t ω)
            (ηi * (𝔼.E t (M (t + 1)) ω - M t ω))
          have a6 := abs_sub (ηy * Y t ω) (ηi * r t ω)
          linarith
      _ ≤ _ := by
          have c1 : |ηy * Y t ω| ≤ |ηy| * KY := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hY t ω) (abs_nonneg _)
          have c2 : |ηi * r t ω| ≤ |ηi| * Kr := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr t ω) (abs_nonneg _)
          have c3 : |ηi * l t ω| ≤ |ηi| * Kl := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hl t ω) (abs_nonneg _)
          have c4 : |ηi * (𝔼.E t (M (t + 1)) ω - M t ω)| ≤ |ηi| * KM := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          linarith [he t ω]
  · intro t
    simp only [fMG, uComp, map_add, map_sub, map_smul, 𝔼.const, haY t, har t, hae t, hal t,
      haM t, 𝔼.E_E_self]

/-- Woodford (2003), **Proposition 2.11**, pp. 107–108 and A.11, pp. 644–645 (log-linear
model): with `η_i > 0`, bounded adapted `Ŷ, r̂, εᵐ, log(1 + iᵐ)` and adapted `log Mˢ` with bounded
growth, there is exactly one equilibrium `(log P, î)` of (1.32) and (3.6) in which real balances
`m̂` and the interest rate `î` are bounded; it is `(mgPrice, mgRate)`. The price level itself may
be unbounded (money may grow). -/
theorem prop_2_11 {ηy ηi lmbar lbar KY Kr Ke Kl KM : ℝ} (hηi : 0 < ηi)
    {M l Y r e : ℕ → Ω → ℝ}
    (hY : ∀ t ω, |Y t ω| ≤ KY) (hr : ∀ t ω, |r t ω| ≤ Kr) (he : ∀ t ω, |e t ω| ≤ Ke)
    (hl : ∀ t ω, |l t ω| ≤ Kl) (hM : ∀ t ω, |M (t + 1) ω - M t ω| ≤ KM)
    (haY : 𝔼.Adapted Y) (har : 𝔼.Adapted r) (hae : 𝔼.Adapted e) (hal : 𝔼.Adapted l)
    (haM : 𝔼.Adapted M) :
    ∃! pi : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      BoundedProc (fun t => M t - pi.1 t - fun _ => lmbar) ∧ BoundedProc pi.2 ∧
        MGEquilibrium 𝔼 ηy ηi lmbar lbar M l Y r e pi.1 pi.2 := by
  obtain ⟨hfb, hfa⟩ := fMG_bounded_adapted 𝔼 (ηy := ηy) (ηi := ηi) (lbar := lbar)
    hY hr he hl hM haY har hae hal haM
  have hAB : |ηi| < |1 + ηi| := by
    rw [abs_of_pos hηi, abs_of_pos (by linarith)]; linarith
  obtain ⟨hs, ⟨Km, hKm⟩, -, huniq⟩ := scalar_existsUnique 𝔼 hAB hfb hfa
  set f := fMG 𝔼 ηy ηi lbar M l Y r e with hf
  set m := scalarSol 𝔼 (1 + ηi) ηi f with hm
  have hmhat : (fun t => M t - mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e t - fun _ => lmbar) = m := by
    funext t ω
    simp only [mgPrice, Pi.sub_apply, ← hf, ← hm]
    ring
  have hF : Fisher 𝔼 r (mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e)
      (mgRate 𝔼 ηy ηi lmbar lbar M l Y r e) := fun t => rfl
  refine ⟨(mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e, mgRate 𝔼 ηy ηi lmbar lbar M l Y r e),
    ⟨?_, ?_, hF, ?_⟩, ?_⟩
  · rw [hmhat]; exact ⟨Km, hKm⟩
  · refine ⟨Kr + KM + Km + Km, fun t ω => ?_⟩
    change |mgRate 𝔼 ηy ηi lmbar lbar M l Y r e t ω| ≤ _
    have hrate : mgRate 𝔼 ηy ηi lmbar lbar M l Y r e t =
        r t + 𝔼.E t (M (t + 1) - M t) - 𝔼.E t (m (t + 1)) + m t := by
      have h1 : ∀ s, mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e s = M s - m s - fun _ => lmbar :=
        fun s => by funext ω; simp only [mgPrice, Pi.sub_apply, ← hf, ← hm]
      simp only [mgRate, h1, map_sub, 𝔼.const, haM t]
      abel
    rw [hrate]
    simp only [Pi.add_apply, Pi.sub_apply]
    have a1 := hr t ω
    have a2 : |𝔼.E t (M (t + 1) - M t) ω| ≤ KM := 𝔼.abs_E_le (fun ω' => hM t ω') t ω
    have a3 : |𝔼.E t (m (t + 1)) ω| ≤ Km := 𝔼.abs_E_le (fun ω' => hKm (t + 1) ω') t ω
    have a4 := hKm t ω
    calc |r t ω + 𝔼.E t (M (t + 1) - M t) ω - 𝔼.E t (m (t + 1)) ω + m t ω|
        ≤ |r t ω| + |𝔼.E t (M (t + 1) - M t) ω| + |𝔼.E t (m (t + 1)) ω| + |m t ω| := by
          have b1 := abs_add_le (r t ω) (𝔼.E t (M (t + 1) - M t) ω)
          have b2 := abs_sub (r t ω + 𝔼.E t (M (t + 1) - M t) ω) (𝔼.E t (m (t + 1)) ω)
          have b3 := abs_add_le (r t ω + 𝔼.E t (M (t + 1) - M t) ω - 𝔼.E t (m (t + 1)) ω)
            (m t ω)
          linarith
      _ ≤ Kr + KM + Km + Km := by linarith
  · rw [lm_iff_cagan 𝔼 hF, cagan_iff_scalar, hmhat]
    exact hs
  · rintro ⟨p, i⟩ ⟨hpb, -, hFp, hLM⟩
    have hsc := (cagan_iff_scalar 𝔼).mp ((lm_iff_cagan 𝔼 hFp).mp hLM)
    have hmeq := huniq _ hsc hpb
    have hp : p = mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e := by
      funext t ω
      have := congrFun (congrFun hmeq t) ω
      simp only [Pi.sub_apply] at this
      simp only [mgPrice, Pi.sub_apply, ← hf, ← hm]
      linarith
    subst hp
    refine Prod.ext rfl ?_
    funext t
    exact hFp t

/-- Woodford (2003), (3.7), p. 108: the weights `ϕ_j = η_iʲ/(1 + η_i)^{j+1}`. -/
noncomputable def phi (ηi : ℝ) (j : ℕ) : ℝ := ηi ^ j / (1 + ηi) ^ (j + 1)

/-- Woodford (2003), (3.7), p. 108: `ϕ_j = (1 − α) αʲ` with `α = η_i/(1 + η_i)`. -/
theorem phi_eq (ηi : ℝ) (hηi : 0 < ηi) (j : ℕ) :
    phi ηi j = (1 - ηi / (1 + ηi)) * (ηi / (1 + ηi)) ^ j := by
  unfold phi
  have : (1 + ηi) ≠ 0 := by linarith
  rw [div_pow]
  field_simp
  ring

/-- Woodford (2003), (3.7), p. 108: the weights `ϕ_j` are positive. -/
theorem phi_pos {ηi : ℝ} (hηi : 0 < ηi) (j : ℕ) : 0 < phi ηi j := by
  unfold phi; positivity

/-- Woodford (2003), (3.7), p. 108: the weights `ϕ_j` sum to one. -/
theorem hasSum_phi {ηi : ℝ} (hηi : 0 < ηi) : HasSum (phi ηi) 1 := by
  have hq0 : 0 ≤ ηi / (1 + ηi) := by positivity
  have hq1 : ηi / (1 + ηi) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 - ηi / (1 + ηi))
  have hne : 1 - ηi / (1 + ηi) ≠ 0 := by linarith
  rw [mul_inv_cancel₀ hne] at h
  exact h.congr_fun fun j => phi_eq ηi hηi j

/-- Woodford (2003), **(3.7)**, p. 108 (from (A.30) by summation by parts, A.11, p. 645): the
equilibrium log price level is
`log P_t = ∑_j ϕ_j E_t[log M_{t+j} − η_i log(1 + iᵐ_{t+j}) − u_{t+j}] − log m̄`, the series
converging although `log M` need not be bounded. -/
theorem prop_2_11_priceLevel {ηy ηi lmbar lbar KY Kr Ke Kl KM : ℝ} (hηi : 0 < ηi)
    {M l Y r e : ℕ → Ω → ℝ}
    (hY : ∀ t ω, |Y t ω| ≤ KY) (hr : ∀ t ω, |r t ω| ≤ Kr) (he : ∀ t ω, |e t ω| ≤ Ke)
    (hl : ∀ t ω, |l t ω| ≤ Kl) (hM : ∀ t ω, |M (t + 1) ω - M t ω| ≤ KM)
    (haM : 𝔼.Adapted M) (t : ℕ) (ω : Ω) :
    Summable (fun j => phi ηi j *
        𝔼.E t (M (t + j) - ηi • l (t + j) - uComp ηy ηi lbar Y r e (t + j)) ω) ∧
      mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e t ω =
        ∑' j, phi ηi j *
          𝔼.E t (M (t + j) - ηi • l (t + j) - uComp ηy ηi lbar Y r e (t + j)) ω - lmbar := by
  set q := ηi / (1 + ηi) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  have hqa : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  clear_value q
  set x : ℕ → ℝ := fun j => 𝔼.E t (M (t + j)) ω with hx
  have hxinc : ∀ j, |x (j + 1) - x j| ≤ KM := fun j => by
    simp only [hx]
    rw [← Pi.sub_apply, ← map_sub]
    exact 𝔼.abs_E_le (fun ω' => hM (t + j) ω') t ω
  set a : ℕ → ℝ := fun j => 𝔼.E t (uComp ηy ηi lbar Y r e (t + j) + ηi • l (t + j)) ω with ha
  set Ka := |ηy| * KY + |ηi| * Kr + Ke + |ηi * lbar| + |ηi| * Kl with hKa
  have hab : ∀ j, |a j| ≤ Ka := fun j => by
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    simp only [uComp, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := hY (t + j) ω'; have := hr (t + j) ω'; have := he (t + j) ω'
    have := hl (t + j) ω'
    have b1 := abs_sub (ηy * Y (t + j) ω') (ηi * r (t + j) ω')
    have b2 := abs_add_le (ηy * Y (t + j) ω' - ηi * r (t + j) ω') (e (t + j) ω')
    have b3 := abs_sub (ηy * Y (t + j) ω' - ηi * r (t + j) ω' + e (t + j) ω') (ηi * lbar)
    have b4 := abs_add_le (ηy * Y (t + j) ω' - ηi * r (t + j) ω' + e (t + j) ω' - ηi * lbar)
      (ηi * l (t + j) ω')
    have c1 : |ηy * Y (t + j) ω'| ≤ |ηy| * KY := by rw [abs_mul]; gcongr
    have c2 : |ηi * r (t + j) ω'| ≤ |ηi| * Kr := by rw [abs_mul]; gcongr
    have c3 : |ηi * l (t + j) ω'| ≤ |ηi| * Kl := by rw [abs_mul]; gcongr
    simp only [hKa]
    linarith
  -- summability
  have hphi : ∀ j, phi ηi j = (1 - q) * q ^ j := fun j => by rw [hq]; exact phi_eq ηi hηi j
  have hsa : Summable (fun j => phi ηi j * a j) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hq0 hq1).mul_left ((1 - q) * Ka)) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, hphi, abs_of_nonneg (by have := pow_nonneg hq0 j; nlinarith)]
    calc (1 - q) * q ^ j * |a j| ≤ (1 - q) * q ^ j * Ka :=
          mul_le_mul_of_nonneg_left (hab j) (by have := pow_nonneg hq0 j; nlinarith)
      _ = (1 - q) * Ka * q ^ j := by ring
  have hsx : Summable (fun j => q ^ j * x j) := summable_geom_mul hqa hxinc
  have hsx' : Summable (fun j => phi ηi j * x j) := by
    refine (hsx.mul_left (1 - q)).congr fun j => ?_
    rw [hphi]; ring
  have hsd : Summable (fun j => q ^ (j + 1) * (x (j + 1) - x j)) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hq0 hq1).mul_left (q * KM)) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq0 _), pow_succ]
    calc q ^ j * q * |x (j + 1) - x j| ≤ q ^ j * q * KM :=
          mul_le_mul_of_nonneg_left (hxinc j) (by positivity)
      _ = q * KM * q ^ j := by ring
  -- the forcing term in expectation
  have hEf : ∀ j, 𝔼.E t (fMG 𝔼 ηy ηi lbar M l Y r e (t + j)) ω =
      a j - ηi * (x (j + 1) - x j) := fun j => by
    simp only [fMG, ha, hx, map_sub, map_add, map_smul, 𝔼.tower (Nat.le_add_right t j),
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show t + (j + 1) = t + j + 1 by omega]
  have hmstar : scalarSol 𝔼 (1 + ηi) ηi (fMG 𝔼 ηy ηi lbar M l Y r e) t ω =
      ∑' j, phi ηi j * a j - ∑' j, q ^ (j + 1) * (x (j + 1) - x j) := by
    rw [scalarSol_apply, ← hsa.tsum_sub hsd]
    refine tsum_congr fun j => ?_
    change phi ηi j * _ = _
    rw [hEf j]
    have : phi ηi j * ηi = q ^ (j + 1) := by
      rw [hphi, pow_succ, hq]
      field_simp
      ring
    linear_combination -(x (j + 1) - x j) * this
  have habel := abel_tsum hqa hxinc
  have hx0 : x 0 = M t ω := by simp only [hx, add_zero, haM t]
  have hterm : ∀ j, phi ηi j *
      𝔼.E t (M (t + j) - ηi • l (t + j) - uComp ηy ηi lbar Y r e (t + j)) ω =
      phi ηi j * x j - phi ηi j * a j := fun j => by
    simp only [ha, hx, map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hsum : Summable (fun j => phi ηi j *
      𝔼.E t (M (t + j) - ηi • l (t + j) - uComp ηy ηi lbar Y r e (t + j)) ω) :=
    (hsx'.sub hsa).congr fun j => (hterm j).symm
  refine ⟨hsum, ?_⟩
  rw [tsum_congr hterm, hsx'.tsum_sub hsa]
  have hS : ∑' j, phi ηi j * x j = (1 - q) * ∑' j, q ^ j * x j := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [hphi]; ring
  simp only [mgPrice, Pi.sub_apply]
  rw [hmstar, hS, habel, hx0]
  ring

/-! ### Money-growth targeting as a Wicksellian rule (3.8)–(3.9) -/

/-- Woodford (2003), eq. (1.34), p. 81: the log-linear Wicksellian rule
`î_t = φ_p (log P_t − log P*_t) + ν_t`. -/
def Wicksell (φp : ℝ) (pstar ν p i : ℕ → Ω → ℝ) : Prop := ∀ t, i t = φp • (p t - pstar t) + ν t

/-- Woodford (2003), p. 109: the intercept `ν_t = îᵐ_t + η_i⁻¹(η_y Ŷ_t + εᵐ_t)` of the
Wicksellian rule implied by money-growth targeting. -/
noncomputable def nuMG (ηy ηi lbar : ℝ) (l Y e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (l t - fun _ => lbar) + ηi⁻¹ • (ηy • Y t + e t)

/-- Woodford (2003), **(3.8)**, p. 109: the money-demand relation (3.6) holds if and only if the
interest rate follows the Wicksellian rule (1.34) with `φ_p = η_i⁻¹`, price-level target
`log P* = log Mˢ − log m̄` and intercept `ν = îᵐ + η_i⁻¹(η_y Ŷ + εᵐ)`. -/
theorem lm_iff_wicksell {ηy ηi lmbar lbar : ℝ} (hηi : ηi ≠ 0) {M l Y e p i : ℕ → Ω → ℝ} :
    LM ηy ηi lmbar lbar M l Y e p i ↔
      Wicksell ηi⁻¹ (fun t => M t - fun _ => lmbar) (nuMG ηy ηi lbar l Y e) p i := by
  unfold LM Wicksell nuMG
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), eq. (1.39), p. 83: the price level under a Wicksellian rule,
`log P_t = ∑_j φ_p(1 + φ_p)^{−(j+1)} E_t[log P*_{t+j} + φ_p⁻¹(r̂_{t+j} − ν_{t+j})]`. -/
noncomputable def wicksellPrice (φp : ℝ) (pstar r ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, φp * (1 + φp)⁻¹ ^ (j + 1) *
    𝔼.E t (pstar (t + j) + φp⁻¹ • (r (t + j) - ν (t + j))) ω

/-- Woodford (2003), p. 110: with `φ_p = η_i⁻¹` the weights of (1.39) are those of (3.7). -/
theorem phi_eq_wicksell_weight {ηi : ℝ} (hηi : 0 < ηi) (j : ℕ) :
    ηi⁻¹ * (1 + ηi⁻¹)⁻¹ ^ (j + 1) = phi ηi j := by
  unfold phi
  have h1 : (1 + ηi⁻¹)⁻¹ = ηi / (1 + ηi) := by field_simp; ring
  rw [h1, div_pow, pow_succ ηi j]
  field_simp

/-- Woodford (2003), p. 110: **(3.7) is (1.39)** for the Wicksellian rule (3.8) implied by
money-growth targeting (`φ_p = η_i⁻¹`, `log P* = log Mˢ − log m̄`, `ν` as in `nuMG`). -/
theorem priceLevel_eq_wicksell {ηy ηi lmbar lbar KY Kr Ke Kl KM : ℝ} (hηi : 0 < ηi)
    {M l Y r e : ℕ → Ω → ℝ}
    (hY : ∀ t ω, |Y t ω| ≤ KY) (hr : ∀ t ω, |r t ω| ≤ Kr) (he : ∀ t ω, |e t ω| ≤ Ke)
    (hl : ∀ t ω, |l t ω| ≤ Kl) (hM : ∀ t ω, |M (t + 1) ω - M t ω| ≤ KM)
    (haM : 𝔼.Adapted M) (t : ℕ) (ω : Ω) :
    mgPrice 𝔼 ηy ηi lmbar lbar M l Y r e t ω =
      wicksellPrice 𝔼 ηi⁻¹ (fun t => M t - fun _ => lmbar) r (nuMG ηy ηi lbar l Y e) t ω := by
  obtain ⟨hs, heq⟩ := prop_2_11_priceLevel 𝔼 (ηy := ηy) (lmbar := lmbar) (lbar := lbar) hηi
    hY hr he hl hM haM t ω
  have hterm : ∀ j, ηi⁻¹ * (1 + ηi⁻¹)⁻¹ ^ (j + 1) * 𝔼.E t ((M (t + j) - fun _ => lmbar) +
      ηi⁻¹⁻¹ • (r (t + j) - nuMG ηy ηi lbar l Y e (t + j))) ω =
      phi ηi j * 𝔼.E t (M (t + j) - ηi • l (t + j) - uComp ηy ηi lbar Y r e (t + j)) ω -
        lmbar * phi ηi j := fun j => by
    rw [phi_eq_wicksell_weight hηi j]
    have hE : 𝔼.E t ((M (t + j) - fun _ => lmbar) +
        ηi⁻¹⁻¹ • (r (t + j) - nuMG ηy ηi lbar l Y e (t + j))) =
        𝔼.E t (M (t + j) - ηi • l (t + j) - uComp ηy ηi lbar Y r e (t + j)) -
          fun _ => lmbar := by
      have hfun : (M (t + j) - fun _ => lmbar) +
          ηi⁻¹⁻¹ • (r (t + j) - nuMG ηy ηi lbar l Y e (t + j)) =
          (M (t + j) - ηi • l (t + j) - uComp ηy ηi lbar Y r e (t + j)) - fun _ => lmbar := by
        funext ω'
        simp only [nuMG, uComp, inv_inv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      rw [hfun, map_sub, 𝔼.const]
    rw [hE, Pi.sub_apply]
    ring
  unfold wicksellPrice
  rw [tsum_congr hterm, hs.tsum_sub ((hasSum_phi hηi).summable.mul_left lmbar),
    tsum_mul_left, (hasSum_phi hηi).tsum_eq, heq]
  ring

/-- Woodford (2003), eq. (3.9), p. 110: a money-supply feedback rule
`log Mˢ_t = log P_t + log m̄ + η_y Ŷ_t − η_i(φ_p(log P_t − log P*_t) + ν_t − îᵐ_t) + εᵐ_t`,
obtained by substituting the Wicksellian rule into (3.6). -/
def MoneyFeedback (ηy ηi lmbar lbar φp : ℝ) (pstar ν l Y e p M : ℕ → Ω → ℝ) : Prop :=
  ∀ t, M t = p t + (fun _ => lmbar) + ηy • Y t -
    ηi • (φp • (p t - pstar t) + ν t - (l t - fun _ => lbar)) + e t

/-- Woodford (2003), **(3.9)**, p. 110: given the money-demand relation (3.6), a Wicksellian rule
(1.30)/(1.34) is equivalent to the money-supply feedback rule (3.9) (for `η_i ≠ 0`). -/
theorem wicksell_iff_moneyFeedback {ηy ηi lmbar lbar φp : ℝ} (hηi : ηi ≠ 0)
    {pstar ν M l Y e p i : ℕ → Ω → ℝ} (hLM : LM ηy ηi lmbar lbar M l Y e p i) :
    Wicksell φp pstar ν p i ↔ MoneyFeedback ηy ηi lmbar lbar φp pstar ν l Y e p M := by
  unfold Wicksell MoneyFeedback
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  have h := congrFun (hLM t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  constructor
  · intro hw
    rw [hw] at h
    linarith
  · intro hm
    have : ηi * i t ω = ηi * (φp * (p t ω - pstar t ω) + ν t ω) := by linarith
    exact mul_left_cancel₀ hηi this

/-- Woodford (2003), p. 110: only the composite `log Mˢ − η_i log(1 + iᵐ)` matters — two
policies with the same composite have the same equilibria. -/
theorem mgEquilibrium_composite {ηy ηi lmbar lbar : ℝ} {M M' l l' Y r e p i : ℕ → Ω → ℝ}
    (hcomp : ∀ t, M t - ηi • l t = M' t - ηi • l' t) :
    MGEquilibrium 𝔼 ηy ηi lmbar lbar M l Y r e p i ↔
      MGEquilibrium 𝔼 ηy ηi lmbar lbar M' l' Y r e p i := by
  unfold MGEquilibrium LM
  refine and_congr Iff.rfl (forall_congr' fun t => ?_)
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  have h := congrFun (hcomp t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  constructor <;> intro h' <;> linarith

/-- Woodford (2003), p. 106 (separable utility): the money-demand relation (3.6) plays no role in
price determination under an interest-rate rule — for any paths of prices, interest rates and
interest on money it determines exactly one path of the monetary base. -/
theorem exists_unique_money (ηy ηi lmbar lbar : ℝ) (l Y e p i : ℕ → Ω → ℝ) :
    ∃! M : ℕ → Ω → ℝ, LM ηy ηi lmbar lbar M l Y e p i := by
  refine ⟨fun t => p t + (fun _ => lmbar) + (ηy • Y t - ηi • (i t - (l t - fun _ => lbar)) +
    e t), fun t => ?_, fun M hM => ?_⟩
  · funext ω; simp only [Pi.add_apply, Pi.sub_apply]; ring
  · funext t ω
    have := congrFun (hM t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
end Woodford.PriceLevelDetermination.MoneyGrowth
