/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6Rotemberg
import KeynesianStickyPrices.TidyR6EulerIS

/-!
# The Phillips curve (17.17) from the Rotemberg price setter

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, eq. (17.17), p. 407
(`π_t = βE_tπ_{t+1} + κx_t + u_{π,t}`), and Chapter 5, §5.1, p. 118 ("The Phillips curve (5.2)
comes from the first-order condition for monopolistically-competitive price setters, facing costs
of changing prices ... Both equations are deviations from steady states, so x represents the
output gap").

The price setter of TidyR6Rotemberg prices a good whose producer has CRRA utility of consumption
(`u′(C) = C^{−γ}`) and disutility of production `y^{1+ϕ}/(1 + ϕ)`; in a symmetric equilibrium
consumption equals output `Y_t = Ȳe^{x_t}`, so its data are (`yeoData`)
`A_t = u′(Y_t)Y_t = Ȳ^{1−γ}e^{(1−γ)x_t}`, `B_t = Ȳ^{1+ϕ}e^{(1+ϕ)x_t}/(1 + ϕ)`, `π_t`, with
`η = ε(1 + ϕ)`. The steady state `Ȳ` solves `εȲ^{1+ϕ} = (ε − 1)Ȳ^{1−γ}` (marginal cost equals
`(ε − 1)/ε`; `ybar_ss`). In the symmetric equilibrium every price setter sets the aggregate
price, `q ≡ 0` (`zeroPlan`).

## Main results

* `symFOC_iff_nonlinPC`: the first-order condition at `q ≡ 0` is the **exact nonlinear Phillips
  curve** `G(π_t) = βE_tG(π_{t+1}) + κ̃(e^{(1+ϕ)x_t} − e^{(1−γ)x_t})` with
  `G(π) = (e^π − 1)e^π` and `κ̃ = (ε − 1)Ȳ^{1−γ}/φ`.
* `nonlinPC_iff_PCM`: **exactly**, the nonlinear curve is (17.17)
  `π_t = βE_tπ_{t+1} + κx_t + u_{π,t}` with `κ = κ̃(γ + ϕ)` and the explicit remainder
  `u_{π,t} = βE_tR_G(π_{t+1}) − R_G(π_t) + κ̃R_M(x_t)` (`pcRem`). The remainders are second
  order: `R_G(0) = R_M(0) = 0`, zero derivatives at the steady state (`hasDerivAt_rG_zero`,
  `hasDerivAt_rM_zero`), `|R_G(π)| ≤ 5π²` for `|π| ≤ 1/2` (`rG_le`) and
  `|R_M(x)| ≤ ((1 + ϕ)² + (1 − γ)²)x²` for small `x` (`rM_le`).
* `PC_of_optimal` (**necessity** over all plans): if pricing at the aggregate price level is
  optimal for the price setter among all plans, (17.17) with `pcRem` holds at every date.
* `optimal_iff_PC` (**necessity and sufficiency**): with uniformly bounded output gap and
  inflation inside the margin conditions (output not too far below steady state, no inflation
  rate below `log(1/2)`), pricing at the aggregate price level is optimal among the plans in the
  concavity region iff (17.17) with `pcRem` holds at every date.
* Finite trees: `Tree.PCM_iff_PC` turns the almost-sure Phillips curve into the project's
  `FullModel.PC` for the tree's core expectation system.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6RotembergPC

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6PriceSetting TidyR6Rotemberg TidyR6EulerIS

/-! ### The nonlinear terms and their remainders -/

/-- Cochrane (2023), p. 118: the Rotemberg inflation term `G(π) = (e^π − 1)e^π`. -/
noncomputable def gInfl (p : ℝ) : ℝ := (Real.exp p - 1) * Real.exp p

/-- Cochrane (2023), p. 118: the marginal-cost gap `e^{(1+ϕ)x} − e^{(1−γ)x}`. -/
noncomputable def mcGap (γ ϕ x : ℝ) : ℝ := Real.exp ((1 + ϕ) * x) - Real.exp ((1 - γ) * x)

/-- Cochrane (2023), p. 118: the remainder `R_G(π) = G(π) − π`. -/
noncomputable def rG (p : ℝ) : ℝ := gInfl p - p

/-- Cochrane (2023), p. 118: the remainder `R_M(x) = e^{(1+ϕ)x} − e^{(1−γ)x} − (γ + ϕ)x`. -/
noncomputable def rM (γ ϕ x : ℝ) : ℝ := mcGap γ ϕ x - (γ + ϕ) * x

/-- Cochrane (2023), p. 118: `R_G(π) = expRem(2π) − expRem(π)`. -/
theorem rG_eq (p : ℝ) : rG p = expRem (2 * p) - expRem p := by
  simp only [rG, gInfl, expRem]
  rw [show 2 * p = p + p by ring, Real.exp_add]
  ring

/-- Cochrane (2023), p. 118: `R_M(x) = expRem((1 + ϕ)x) − expRem((1 − γ)x)`. -/
theorem rM_eq (γ ϕ x : ℝ) : rM γ ϕ x = expRem ((1 + ϕ) * x) - expRem ((1 - γ) * x) := by
  simp only [rM, mcGap, expRem]
  ring

/-- Cochrane (2023), p. 118: `R_G` vanishes at the steady state. -/
theorem rG_zero : rG 0 = 0 := by simp [rG, gInfl]

/-- Cochrane (2023), p. 118: `R_M` vanishes at the steady state. -/
theorem rM_zero (γ ϕ : ℝ) : rM γ ϕ 0 = 0 := by simp [rM, mcGap]

/-- Cochrane (2023), p. 118: the linearisation of `G` is its exact derivative at `0`:
`R_G′(0) = 0`. -/
theorem hasDerivAt_rG_zero : HasDerivAt rG 0 0 := by
  have h1 : HasDerivAt (fun p => expRem (2 * p)) (0 * 2) 0 := by
    have h0 : HasDerivAt expRem 0 (2 * (0 : ℝ)) := by
      rw [mul_zero]; exact hasDerivAt_expRem_zero
    have hl : HasDerivAt (fun p : ℝ => 2 * p) 2 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
    exact h0.comp (0 : ℝ) hl
  have h := h1.sub hasDerivAt_expRem_zero
  simp only [zero_mul, sub_self] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun p => rG_eq p)

/-- Cochrane (2023), p. 118: the linearisation of the marginal-cost gap is its exact
derivative at `0`: `R_M′(0) = 0`. -/
theorem hasDerivAt_rM_zero (γ ϕ : ℝ) : HasDerivAt (rM γ ϕ) 0 0 := by
  have hc : ∀ c : ℝ, HasDerivAt (fun x => expRem (c * x)) 0 0 := fun c => by
    have h0 : HasDerivAt expRem 0 (c * (0 : ℝ)) := by
      rw [mul_zero]; exact hasDerivAt_expRem_zero
    have hl : HasDerivAt (fun x : ℝ => c * x) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
    have h := h0.comp (0 : ℝ) hl
    rw [zero_mul] at h
    exact h
  have h := (hc (1 + ϕ)).sub (hc (1 - γ))
  simp only [sub_self] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun x => rM_eq γ ϕ x)

/-- Cochrane (2023), p. 118: `R_G` is second order, `|R_G(π)| ≤ 5π²` for `|π| ≤ 1/2`. -/
theorem rG_le {p : ℝ} (hp : |p| ≤ 1 / 2) : |rG p| ≤ 5 * p ^ 2 := by
  have h2 : |2 * p| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have h1 : |p| ≤ 1 := by linarith
  have a1 := expRem_le_sq h2
  have a2 := expRem_le_sq h1
  have b1 := expRem_nonneg (2 * p)
  have b2 := expRem_nonneg p
  rw [rG_eq, abs_le]
  constructor <;> nlinarith

/-- Cochrane (2023), p. 118: `R_M` is second order,
`|R_M(x)| ≤ ((1 + ϕ)² + (1 − γ)²)x²` when `|(1 + ϕ)x| ≤ 1` and `|(1 − γ)x| ≤ 1`. -/
theorem rM_le {γ ϕ x : ℝ} (h1 : |(1 + ϕ) * x| ≤ 1) (h2 : |(1 - γ) * x| ≤ 1) :
    |rM γ ϕ x| ≤ ((1 + ϕ) ^ 2 + (1 - γ) ^ 2) * x ^ 2 := by
  have a1 := expRem_le_sq h1
  have a2 := expRem_le_sq h2
  have b1 := expRem_nonneg ((1 + ϕ) * x)
  have b2 := expRem_nonneg ((1 - γ) * x)
  rw [rM_eq, abs_le]
  constructor <;> nlinarith

/-! ### The symmetric equilibrium -/

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 118: the price setter's data in a symmetric equilibrium with output
`Ȳe^{x_t}` and inflation `π_t`: `(Ȳ^{1−γ}e^{(1−γ)x_t}, Ȳ^{1+ϕ}e^{(1+ϕ)x_t}/(1 + ϕ), π_t)`. -/
noncomputable def yeoData (γ ϕ Ybar : ℝ) (x π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ × ℝ × ℝ :=
  fun t ω => (Ybar ^ (1 - γ) * Real.exp ((1 - γ) * x t ω),
    Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x t ω) / (1 + ϕ), π t ω)

/-- Cochrane (2023), p. 118: in a symmetric equilibrium every price setter charges the
aggregate price, `q ≡ 0`. -/
def zeroPlan : ℕ → Ω → ℝ := fun _ _ => 0

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: last period's relative price is zero too. -/
theorem lag_zeroPlan (t : ℕ) : lag (fun _ : Ω => (0 : ℝ)) zeroPlan t = fun _ => 0 := by
  cases t <;> rfl

/-- Cochrane (2023), p. 118: the slope `κ̃ = (ε − 1)Ȳ^{1−γ}/φ` of the nonlinear curve. -/
noncomputable def kappaT (ε φ γ Ybar : ℝ) : ℝ := (ε - 1) * Ybar ^ (1 - γ) / φ

variable (S) in
/-- Cochrane (2023), p. 118: the exact nonlinear Rotemberg Phillips curve at `t`, almost surely
`G(π_t) = βE_tG(π_{t+1}) + κ̃(e^{(1+ϕ)x_t} − e^{(1−γ)x_t})`. -/
def NonlinPC (β κt γ ϕ : ℝ) (x π : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, gInfl (π t ω) =
    β * S.E t (fun ω => gInfl (π (t + 1) ω)) ω + κt * mcGap γ ϕ (x t ω)

/-- Cochrane (2023), p. 118: the steady state `Ȳ = ((ε − 1)/ε)^{1/(γ+ϕ)}` solves
`εȲ^{1+ϕ} = (ε − 1)Ȳ^{1−γ}` (`ε > 1`, `γ + ϕ ≠ 0`). -/
theorem ybar_ss {ε γ ϕ : ℝ} (hε : 1 < ε) (hγϕ : γ + ϕ ≠ 0) :
    ε * (((ε - 1) / ε) ^ (1 / (γ + ϕ))) ^ (1 + ϕ) =
      (ε - 1) * (((ε - 1) / ε) ^ (1 / (γ + ϕ))) ^ (1 - γ) := by
  have hpos : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  set Y := ((ε - 1) / ε) ^ (1 / (γ + ϕ)) with hY
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hpos _
  have hsplit : Y ^ (1 + ϕ) = Y ^ (1 - γ) * Y ^ (γ + ϕ) := by
    rw [← Real.rpow_add hYpos]
    ring_nf
  have hpow : Y ^ (γ + ϕ) = (ε - 1) / ε := by
    rw [hY, ← Real.rpow_mul hpos.le, one_div, inv_mul_cancel₀ hγϕ, Real.rpow_one]
  rw [hsplit, hpow]
  field_simp

/-- Cochrane (2023), p. 118: at the steady state, the price setter's marginal revenue less
marginal cost is `(1 − ε)A + ηB = (ε − 1)Ȳ^{1−γ}(e^{(1+ϕ)x} − e^{(1−γ)x})`. -/
theorem margin_eq {ε γ ϕ Ybar : ℝ} (hϕ : 1 + ϕ ≠ 0)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) (x : ℝ) :
    Ybar ^ (1 - γ) * Real.exp ((1 - γ) * x) * (1 - ε) +
        Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x) / (1 + ϕ) * (ε * (1 + ϕ)) =
      (ε - 1) * Ybar ^ (1 - γ) * mcGap γ ϕ x := by
  have h1 : Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x) / (1 + ϕ) * (ε * (1 + ϕ)) =
      ε * Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * x) := by
    field_simp
  rw [h1]
  simp only [mcGap]
  linear_combination Real.exp ((1 + ϕ) * x) * hss

/-- Cochrane (2023), p. 118: `κ̃φ = (ε − 1)Ȳ^{1−γ}`. -/
theorem kappaT_mul {ε φ γ Ybar : ℝ} (hφ : φ ≠ 0) :
    kappaT ε φ γ Ybar * φ = (ε - 1) * Ybar ^ (1 - γ) := by
  simp only [kappaT]
  field_simp

/-- Cochrane (2023), p. 118: **the first-order condition of the symmetric equilibrium is the
exact nonlinear Phillips curve**: at `q ≡ 0` the price setter's FOC at `t` holds iff
`G(π_t) = βE_tG(π_{t+1}) + κ̃(e^{(1+ϕ)x_t} − e^{(1−γ)x_t})` almost surely (`φ ≠ 0`,
`1 + ϕ ≠ 0`, `Ȳ` the steady state). -/
theorem symFOC_iff_nonlinPC {β ε φ γ ϕ Ybar : ℝ} (hφ : φ ≠ 0) (hϕ : 1 + ϕ ≠ 0)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {x π : ℕ → Ω → ℝ} {t : ℕ} :
    FOC S β (rotD1 ε (ε * (1 + ϕ)) φ) (rotD2 φ) (yeoData γ ϕ Ybar x π) (fun _ => 0) zeroPlan t ↔
      NonlinPC S β (kappaT ε φ γ Ybar) γ ϕ x π t := by
  have e2 : (fun ω => rotD2 φ (zeroPlan (t + 1) ω) (zeroPlan t ω)
      (yeoData γ ϕ Ybar x π (t + 1) ω)) = φ • fun ω => gInfl (π (t + 1) ω) := by
    funext ω
    simp [rotD2, zeroPlan, yeoData, gInfl, mul_assoc]
  have hE := S.E_smul φ (fun ω => gInfl (π (t + 1) ω)) t
  have hk := kappaT_mul (ε := ε) (γ := γ) (Ybar := Ybar) hφ
  unfold FOC NonlinPC
  rw [e2, lag_zeroPlan]
  constructor
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2] at h1
    simp only [rotD1, zeroPlan, yeoData, mul_zero, sub_zero, Real.exp_zero,
      mul_one, neg_zero, zero_add, Pi.smul_apply, smul_eq_mul] at h1
    rw [show φ * (Real.exp (π t ω) - 1) * Real.exp (π t ω) = φ * gInfl (π t ω) by
      simp only [gInfl]; ring] at h1
    have hm := margin_eq hϕ hss (x t ω)
    apply mul_left_cancel₀ hφ
    linear_combination -h1 + hm - mcGap γ ϕ (x t ω) * hk
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2]
    simp only [rotD1, zeroPlan, yeoData, mul_zero, sub_zero, Real.exp_zero,
      mul_one, neg_zero, zero_add, Pi.smul_apply, smul_eq_mul]
    rw [show φ * (Real.exp (π t ω) - 1) * Real.exp (π t ω) = φ * gInfl (π t ω) by
      simp only [gInfl]; ring]
    have hm := margin_eq hϕ hss (x t ω)
    linear_combination hm - φ * h1 - mcGap γ ϕ (x t ω) * hk

/-! ### The log-linear Phillips curve (17.17) with explicit remainder -/

variable (S) in
/-- Cochrane (2023), eq. (17.17), p. 407, on a probability space, at date `t`: almost surely
`π_t = βE_tπ_{t+1} + κx_t + u_{π,t}`. -/
def PCM (β κ : ℝ) (uπ x π : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  π t =ᵐ[S.μ] β • S.E t (π (t + 1)) + κ • x t + uπ t

variable (S) in
/-- Cochrane (2023), eq. (17.17), p. 407: the explicit remainder of the log-linear Phillips curve,
`u_{π,t} = βE_tR_G(π_{t+1}) − R_G(π_t) + κ̃R_M(x_t)`. -/
noncomputable def pcRem (β κt γ ϕ : ℝ) (x π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => β * S.E t (fun ω => rG (π (t + 1) ω)) ω - rG (π t ω) + κt * rM γ ϕ (x t ω)

/-- Cochrane (2023), eq. (17.17), p. 407 and p. 118, **exactly**: the nonlinear Phillips curve
holds at `t` iff (17.17) holds with slope `κ = κ̃(γ + ϕ)` and the remainder `pcRem`
(`π_{t+1}` and `R_G(π_{t+1})` integrable). -/
theorem nonlinPC_iff_PCM {β κt γ ϕ : ℝ} {x π : ℕ → Ω → ℝ} {t : ℕ}
    (hπ1 : Integrable (π (t + 1)) S.μ) (hR : Integrable (fun ω => rG (π (t + 1) ω)) S.μ) :
    NonlinPC S β κt γ ϕ x π t ↔ PCM S β (κt * (γ + ϕ)) (pcRem S β κt γ ϕ x π) x π t := by
  have e : (fun ω => gInfl (π (t + 1) ω)) = π (t + 1) + fun ω => rG (π (t + 1) ω) := by
    funext ω
    simp [rG]
  have hE := S.E_add hπ1 hR t
  unfold NonlinPC PCM
  rw [e]
  constructor
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2, Pi.add_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pcRem, rM, rG] at h1 ⊢
    linear_combination h1
  · intro h
    filter_upwards [h, hE] with ω h1 h2
    rw [h2, Pi.add_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pcRem, rM, rG] at h1 ⊢
    linear_combination h1

/-! ### Regularity of the symmetric equilibrium -/

/-- Cochrane (2023), p. 118: a vector of three bounded numbers is bounded in norm. -/
theorem norm3_le {a b c K : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K) (hc : |c| ≤ K) :
    ‖((a, b, c) : ℝ × ℝ × ℝ)‖ ≤ K := by
  simp only [Prod.norm_mk, Real.norm_eq_abs]
  exact max_le ha (max_le hb hc)

/-- Cochrane (2023), p. 118: the data of the symmetric equilibrium are known at `t` and
essentially bounded at every date when output gap and inflation are. -/
theorem yeoData_reg {γ ϕ Ybar : ℝ} {x π : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (hxb : ∀ t, BddAt S (x t)) (hπb : ∀ t, BddAt S (π t)) :
    DataReg S (yeoData γ ϕ Ybar x π) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have mx : Measurable[S.𝓕 t] (x t) := (hx t).measurable
    have mπ : Measurable[S.𝓕 t] (π t) := (hπ t).measurable
    exact ((((Real.continuous_exp.measurable.comp (mx.const_mul (1 - γ))).const_mul
      (Ybar ^ (1 - γ)))).prodMk ((((Real.continuous_exp.measurable.comp
      (mx.const_mul (1 + ϕ))).const_mul (Ybar ^ (1 + ϕ))).div_const (1 + ϕ)).prodMk
      mπ)).stronglyMeasurable
  · obtain ⟨K1, hK1⟩ := BddAt.comp (v := fun y => Ybar ^ (1 - γ) * Real.exp ((1 - γ) * y))
      (by fun_prop) (hxb t)
    obtain ⟨K2, hK2⟩ := BddAt.comp
      (v := fun y => Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * y) / (1 + ϕ)) (by fun_prop) (hxb t)
    obtain ⟨K3, hK3⟩ := hπb t
    refine ⟨max K1 (max K2 K3), ?_⟩
    filter_upwards [hK1, hK2, hK3] with ω h1 h2 h3
    exact norm3_le (h1.trans (le_max_left _ _))
      (h2.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (h3.trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Cochrane (2023), p. 118: with uniformly bounded output gap and inflation, the data are
uniformly bounded. -/
theorem yeoData_ubdd {γ ϕ Ybar : ℝ} {x π : ℕ → Ω → ℝ}
    (hL : ∃ L, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L) :
    ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖yeoData γ ϕ Ybar x π t ω‖ ≤ K := by
  obtain ⟨L, hL⟩ := hL
  obtain ⟨K1, -, hK1⟩ := exists_abs_le_of_continuous
    (v := fun y => Ybar ^ (1 - γ) * Real.exp ((1 - γ) * y)) (by fun_prop) L
  obtain ⟨K2, -, hK2⟩ := exists_abs_le_of_continuous
    (v := fun y => Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * y) / (1 + ϕ)) (by fun_prop) L
  refine ⟨max K1 (max K2 L), fun t => ?_⟩
  filter_upwards [hL t] with ω h
  exact norm3_le ((hK1 _ h.1).trans (le_max_left _ _))
    ((hK2 _ h.1).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (h.2.trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Cochrane (2023), p. 118: pricing at the aggregate price is a uniformly bounded plan. -/
theorem uplan_zero : UPlan S (zeroPlan : ℕ → Ω → ℝ) :=
  ⟨⟨fun _ => stronglyMeasurable_const, fun _ => BddAt.const 0⟩, 0,
    fun _ => Eventually.of_forall fun _ => by simp [zeroPlan]⟩

/-- Cochrane (2023), p. 118: with uniformly bounded data and `0 ≤ β < 1`, pricing at the
aggregate price is admissible. -/
theorem admissible_zero {β ε η φ : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) {θ : ℕ → Ω → ℝ × ℝ × ℝ}
    (hθ : DataReg S θ) (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K) :
    Admissible S β (rotPay ε η φ) θ (fun _ => 0) zeroPlan := by
  obtain ⟨K, hK⟩ := hθu
  obtain ⟨M, hM0, hM⟩ := exists_box_bound (rot_smooth ε η φ).2.2.1 0 K
  have hb : ∀ t, ∀ᵐ ω ∂S.μ, |pay (rotPay ε η φ) θ (fun _ => 0) zeroPlan t ω| ≤ M := fun t => by
    filter_upwards [hK t] with ω h
    have := hM 0 0 (θ t ω) (by simp) (by simp) h
    simpa [pay, lag_zeroPlan, zeroPlan] using this
  have hint : ∀ t, Integrable (pay (rotPay ε η φ) θ (fun _ => 0) zeroPlan t) S.μ := fun t =>
    pay_integrable (rot_smooth ε η φ).2.2.1 hθ stronglyMeasurable_const (BddAt.const 0)
      uplan_zero.1 t
  refine ⟨hint, Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ t)
    (integral_nonneg fun _ => abs_nonneg _)) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ hβ1).mul_right M)⟩
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ t)
  have := integral_mono_ae (hint t).abs (integrable_const M) (hb t)
  simpa using this

/-- Cochrane (2023), p. 118: pricing at the aggregate price lies in the concavity region with
margin `m` when output is not too far below steady state,
`(ε − 1)e^m ≤ ε(1 + ϕ)e^{(γ+ϕ)x_t}`, and no inflation rate is below `log(e^m/2)`,
`e^m/2 ≤ e^{π_t}` (both hold at the steady state for small `m`, since `ε − 1 < ε(1 + ϕ)`). -/
theorem margin_zero {ε γ ϕ Ybar m : ℝ} (hε : 1 < ε) (hϕ : 0 ≤ ϕ) (hY : 0 < Ybar)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {x π : ℕ → Ω → ℝ}
    (hmx : ∀ t, ∀ᵐ ω ∂S.μ, (ε - 1) * Real.exp m ≤ ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω))
    (hmπ : ∀ t, ∀ᵐ ω ∂S.μ, Real.exp m / 2 ≤ Real.exp (π t ω)) :
    Margin S ε (ε * (1 + ϕ)) (yeoData γ ϕ Ybar x π) (fun _ => 0) zeroPlan m := by
  intro t
  filter_upwards [hmx t, hmπ t] with ω h1 h2
  refine ⟨?_, by simpa [zeroPlan, lag_zeroPlan, yeoData] using h2⟩
  simp only [yeoData, zeroPlan, mul_zero, Real.exp_zero, mul_one]
  set Y1 := Ybar ^ (1 - γ)
  set X := x t ω
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
  have hsplit : Real.exp ((1 + ϕ) * X) = Real.exp ((γ + ϕ) * X) * Real.exp ((1 - γ) * X) := by
    rw [← Real.exp_add]
    ring_nf
  have hmm : Real.exp (-m) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
  have hc : 0 ≤ Real.exp (-m) * (ε - 1) * Y1 * Real.exp ((1 - γ) * X) := by
    have := Real.exp_pos (-m)
    have := Real.exp_pos ((1 - γ) * X)
    have : 0 ≤ ε - 1 := by linarith
    positivity
  have h3 := mul_le_mul_of_nonneg_left h1 hc
  rw [hsplit]
  have e1 : Real.exp (-m) * (ε - 1) * Y1 * Real.exp ((1 - γ) * X) * ((ε - 1) * Real.exp m) =
      (ε - 1) ^ 2 * (Y1 * Real.exp ((1 - γ) * X)) := by
    linear_combination ((ε - 1) ^ 2 * Y1 * Real.exp ((1 - γ) * X)) * hmm
  have e2 : Real.exp (-m) * (ε - 1) * Y1 * Real.exp ((1 - γ) * X) *
      (ε * (1 + ϕ) * Real.exp ((γ + ϕ) * X)) = Real.exp (-m) * (ε * (1 + ϕ) * ((ε - 1) * Y1) *
        (Real.exp ((γ + ϕ) * X) * Real.exp ((1 - γ) * X))) := by ring
  linarith

/-- Cochrane (2023), eq. (17.17), p. 407, **necessity over all plans**: if pricing at the
aggregate price is optimal for the Rotemberg price setter among all plans (output gap and
inflation adapted and essentially bounded, `φ ≠ 0`, `1 + ϕ ≠ 0`, `Ȳ` the steady state), then
(17.17) holds at every date with `κ = κ̃(γ + ϕ)` and the remainder `pcRem`. -/
theorem PC_of_optimal {β ε φ γ ϕ Ybar : ℝ} (hβ : 0 < β) (hφ : φ ≠ 0) (hϕ : 1 + ϕ ≠ 0)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {x π : ℕ → Ω → ℝ}
    (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (hxb : ∀ t, BddAt S (x t))
    (hπb : ∀ t, BddAt S (π t))
    (hopt : OptimalIn S (Plan S) β (rotPay ε (ε * (1 + ϕ)) φ) (yeoData γ ϕ Ybar x π)
      (fun _ => 0) zeroPlan) (t : ℕ) :
    PCM S β (kappaT ε φ γ Ybar * (γ + ϕ)) (pcRem S β (kappaT ε φ γ Ybar) γ ϕ x π) x π t := by
  have hfoc := foc_of_optimal hβ (rot_smooth ε (ε * (1 + ϕ)) φ) (yeoData_reg hx hπ hxb hπb)
    stronglyMeasurable_const (BddAt.const 0) hopt t
  have hπi : Integrable (π (t + 1)) S.μ :=
    (hπb (t + 1)).integrable ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable
  have hRi : Integrable (fun ω => rG (π (t + 1) ω)) S.μ :=
    (BddAt.comp (v := rG) (by unfold rG gInfl; fun_prop) (hπb (t + 1))).integrable
      ((by unfold rG gInfl; fun_prop : Continuous rG).comp_aestronglyMeasurable
        ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable)
  exact (nonlinPC_iff_PCM hπi hRi).1 ((symFOC_iff_nonlinPC hφ hϕ hss).1 hfoc)

/-- Cochrane (2023), eq. (17.17), p. 407, **necessity and sufficiency**: let `0 < β < 1`,
`ε > 1`, `ϕ ≥ 0`, `φ > 0`, `Ȳ > 0` the steady state, output gap and inflation adapted and
uniformly bounded and inside the margin conditions of `margin_zero` (`m > 0`). Then pricing at
the aggregate price is optimal for the Rotemberg price setter among the plans in its concavity
region iff (17.17) holds at every date with `κ = κ̃(γ + ϕ)` and the remainder `pcRem`. -/
theorem optimal_iff_PC {β ε φ γ ϕ Ybar m : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hε : 1 < ε)
    (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (hY : 0 < Ybar) (hm : 0 < m)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) {x π : ℕ → Ω → ℝ}
    (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π)
    (hL : ∃ L, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L)
    (hmx : ∀ t, ∀ᵐ ω ∂S.μ, (ε - 1) * Real.exp m ≤ ε * (1 + ϕ) * Real.exp ((γ + ϕ) * x t ω))
    (hmπ : ∀ t, ∀ᵐ ω ∂S.μ, Real.exp m / 2 ≤ Real.exp (π t ω)) :
    OptimalIn S (RPlan S ε (ε * (1 + ϕ)) (yeoData γ ϕ Ybar x π) (fun _ => 0)) β
        (rotPay ε (ε * (1 + ϕ)) φ) (yeoData γ ϕ Ybar x π) (fun _ => 0) zeroPlan ↔
      ∀ t, PCM S β (kappaT ε φ γ Ybar * (γ + ϕ)) (pcRem S β (kappaT ε φ γ Ybar) γ ϕ x π) x π t := by
  obtain ⟨L, hLb⟩ := hL
  have hxb : ∀ t, BddAt S (x t) := fun t => ⟨L, (hLb t).mono fun _ h => h.1⟩
  have hπb : ∀ t, BddAt S (π t) := fun t => ⟨L, (hLb t).mono fun _ h => h.2⟩
  have hθ := yeoData_reg (γ := γ) (ϕ := ϕ) (Ybar := Ybar) hx hπ hxb hπb
  have hθu := yeoData_ubdd (γ := γ) (ϕ := ϕ) (Ybar := Ybar) ⟨L, hLb⟩
  have hA : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ (yeoData γ ϕ Ybar x π t ω).1 := fun t =>
    Eventually.of_forall fun ω => by
      simp only [yeoData]
      exact mul_nonneg (Real.rpow_pos_of_pos hY _).le (Real.exp_pos _).le
  have hη : 0 ≤ 1 - ε + ε * (1 + ϕ) := by nlinarith
  rw [optimal_iff_foc_region hβ hβ1 hη hφ.le hm hθ hθu hA stronglyMeasurable_const
    (BddAt.const 0) uplan_zero (margin_zero hε hϕ hY hss hmx hmπ)
    (admissible_zero hβ.le hβ1 hθ hθu)]
  refine forall_congr' fun t => ?_
  have hπi : Integrable (π (t + 1)) S.μ :=
    (hπb (t + 1)).integrable ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable
  have hRi : Integrable (fun ω => rG (π (t + 1) ω)) S.μ :=
    (BddAt.comp (v := rG) (by unfold rG gInfl; fun_prop) (hπb (t + 1))).integrable
      ((by unfold rG gInfl; fun_prop : Continuous rG).comp_aestronglyMeasurable
        ((hπ (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable)
  rw [symFOC_iff_nonlinPC hφ.ne' (by linarith) hss, nonlinPC_iff_PCM hπi hRi]

/-! ### Finite event trees -/

namespace Tree

open ExpectationsFiniteTree TreeBridge TidyR6HouseholdMeasureTVC.Link

variable {Ω' : Type*}

/-- Cochrane (2023), eq. (17.17), p. 407, for a core expectation system: the Phillips-curve
remainder `u_{π,t} = βE_tR_G(π_{t+1}) − R_G(π_t) + κ̃R_M(x_t)`. -/
noncomputable def corePcRem (𝔼 : ExpectationSystem Ω') (β κt γ ϕ : ℝ) (x π : ℕ → Ω' → ℝ) :
    ℕ → Ω' → ℝ :=
  fun t ω => β * 𝔼.E t (fun ω => rG (π (t + 1) ω)) ω - rG (π t ω) + κt * rM γ ϕ (x t ω)

variable [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω'] (T : FiniteTree Ω')

/-- Cochrane (2023), eq. (17.17), p. 407: on a finite tree, the almost-sure Phillips curve with
the remainder at every date is exactly the project's `FullModel.PC` for the tree's core
expectation system, with `u_π = corePcRem`, in every state. -/
theorem PCM_iff_PC (β κt γ ϕ : ℝ) (x π : ℕ → Ω' → ℝ) :
    (∀ t, PCM (treeSystem T) β (κt * (γ + ϕ)) (pcRem (treeSystem T) β κt γ ϕ x π) x π t) ↔
      FullModel.PC T.toExpectationSystem β (κt * (γ + ϕ))
        (corePcRem T.toExpectationSystem β κt γ ϕ x π) x π := by
  constructor
  · intro h t
    rw [(treeSystem T).eq_of_ae_eq (treeSystem_fullSupport T) (h t)]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pcRem, corePcRem, treeE]
  · intro h t
    refine Eventually.of_forall fun ω => ?_
    rw [h t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pcRem, corePcRem, treeE]

end Tree

end Cochrane.KeynesianStickyPrices.TidyR6RotembergPC
