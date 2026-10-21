/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations
import BasicNewKeynesianModel.CES
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Exercise 3.2: government purchases in the basic New Keynesian model

Galí (2015), Chapter 3, Exercise 3.2 (p. 89). The government buys `G(i)` of every good and
maximises the CES index `G = (∫ G(i)^{1−1/ε} di)^{ε/(ε−1)}` for given spending
`∫ P(i) G(i) di`; purchases are financed by lump-sum taxes.

Goods are indexed by a measure space `(Gd, μ)` (the book's `[0, 1]` is
`μ = volume.restrict (Set.Icc 0 1)`). The government's problem is the same CES expenditure
problem as the household's (App. 3.1, p. 83), so the CES machinery of
`BasicNewKeynesianModel.CES` (`priceIndex`, `cesAgg`, `demand`, `cesAgg_eq_iff_of_spend`, ...)
applies verbatim to the government's purchases.

## Main results

* (a) `govt_index_le`, `govt_index_eq_iff` (from `CES.cesAgg_le_of_spend`,
  `CES.cesAgg_eq_iff_of_spend`): the government's optimal purchases are
  `G(i) = (P(i)/P)^{−ε} G` (both directions); `total_demand`: total demand for good `i` is
  `Y(i) = (P(i)/P)^{−ε}(C + G)`; `aggregate_output`: the output index is `Y = C + G`.
* (b) `hasFDerivAt_log_output`: `log Y = log(e^c + e^g)` has derivative `(1 − S_G, S_G)` at the
  steady state, i.e. `ŷ = (1 − S_G) ĉ + S_G ĝ` exactly to first order, with
  `S_G = G/Y` (`shareG_log`).
* (c) `log_realMC`, `hasFDerivAt_logMC`: average real marginal cost
  `mc = (C^σ N^φ)/((1 − α) A N^{−α})` with `N = (Y/A)^{1/(1−α)}` and `C = Y − G` has, in logs,
  derivative `m̂c = (σ/(1 − S_G) + (φ + α)/(1 − α)) ŷ − σ S_G/(1 − S_G) ĝ − (1 + φ)/(1 − α) â`;
  `mc_coeff_g_neg`: government purchases lower marginal cost at given output.
* (d) `dis_iff`: with `ŷ = (1 − S_G) ĉ + S_G ĝ`, the Euler equation is equivalent to the DIS
  `ŷ_t = E_t ŷ_{t+1} − ((1 − S_G)/σ)(i_t − E_t π_{t+1} − ρ) + S_G (ĝ_t − E_t ĝ_{t+1})`;
  `dis_ar1_term` gives the AR(1) form of the fiscal term.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_2

open MeasureTheory Gali.BasicNewKeynesianModel.CES

variable {Gd : Type*} [MeasurableSpace Gd]

variable {μ : Measure Gd} {ε : ℝ} {P : Gd → ℝ}

/-! ### (a) Total demand -/

/-- Galí (2015), Ex. 3.2(a), p. 89 (**the government's problem**, upper bound): purchases
`G(·) ≥ 0` with spending `∫ P(i) G(i) di = X` attain at most the index `X/P`. -/
theorem govt_index_le (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {g : Gd → ℝ} (hg0 : ∀ i, 0 ≤ g i) (hpg : Integrable (fun i => P i * g i) μ) {X : ℝ}
    (hX : ∫ i, P i * g i ∂μ = X) : cesAgg μ ε g ≤ X / priceIndex μ ε P :=
  cesAgg_le_of_spend hε hP hPi hpos hg0 hpg hX

/-- Galí (2015), Ex. 3.2(a), p. 89 (**the government's optimal purchases**): with spending
`X`, the government attains the maximal index `G = X/P` if and only if
`G(i) = (P(i)/P)^{−ε} G` almost everywhere. -/
theorem govt_index_eq_iff (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {g : Gd → ℝ} (hg0 : ∀ i, 0 ≤ g i) (hpg : Integrable (fun i => P i * g i) μ) {X : ℝ}
    (hX : ∫ i, P i * g i ∂μ = X) :
    cesAgg μ ε g = X / priceIndex μ ε P ↔ g =ᵐ[μ] demand μ ε P (X / priceIndex μ ε P) :=
  cesAgg_eq_iff_of_spend hε hP hPi hpos hg0 hpg hX

/-- Galí (2015), Ex. 3.2(a), p. 89: the demand schedule is linear in the aggregate,
`(P(i)/P)^{−ε} C + (P(i)/P)^{−ε} G = (P(i)/P)^{−ε} (C + G)`. -/
theorem demand_add (C Gv : ℝ) (i : Gd) :
    demand μ ε P C i + demand μ ε P Gv i = demand μ ε P (C + Gv) i := by
  unfold demand
  ring

/-- Galí (2015), Ex. 3.2(a), p. 89: **total demand facing firm `i`**. If households and the
government both buy on their optimal schedules, `C(i) = (P(i)/P)^{−ε} C` and
`G(i) = (P(i)/P)^{−ε} G` (a.e.), then `Y(i) = C(i) + G(i) = (P(i)/P)^{−ε}(C + G)` (a.e.). -/
theorem total_demand {c g : Gd → ℝ} {C Gv : ℝ} (hc : c =ᵐ[μ] demand μ ε P C)
    (hg : g =ᵐ[μ] demand μ ε P Gv) :
    (fun i => c i + g i) =ᵐ[μ] demand μ ε P (C + Gv) := by
  filter_upwards [hc, hg] with i hci hgi
  rw [hci, hgi, demand_add]

/-- Galí (2015), Ex. 3.2(a), p. 89: the government's optimal purchases. With spending
`∫ P(i) G(i) = X`, the government attains the index `X/P` exactly when its purchases are
`G(i) = (P(i)/P)^{−ε} X/P` a.e.; and then total demand for good `i` is
`(P(i)/P)^{−ε}(C + X/P)` given household demand `C(i) = (P(i)/P)^{−ε} C`. -/
theorem govt_total_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {g c : Gd → ℝ} (hg0 : ∀ i, 0 ≤ g i) (hpg : Integrable (fun i => P i * g i) μ) {X C : ℝ}
    (hX : ∫ i, P i * g i ∂μ = X) (hopt : cesAgg μ ε g = X / priceIndex μ ε P)
    (hc : c =ᵐ[μ] demand μ ε P C) :
    (fun i => c i + g i) =ᵐ[μ] demand μ ε P (C + cesAgg μ ε g) := by
  have hg := (govt_index_eq_iff hε hP hPi hpos hg0 hpg hX).1 hopt
  rw [hopt]
  exact total_demand hc hg

/-- Galí (2015), Ex. 3.2(a)–(b), p. 89: goods-market clearing. When output of every good
equals total demand, `Y(i) = (P(i)/P)^{−ε}(C + G)`, the CES output index is `Y = C + G`. -/
theorem aggregate_output (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {C Gv : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ Gv) {Y : Gd → ℝ}
    (hY : ∀ i, Y i = demand μ ε P (C + Gv) i) : cesAgg μ ε Y = C + Gv := by
  rw [show Y = demand μ ε P (C + Gv) from funext hY, cesAgg_demand hε hP hpos (by linarith)]

/-! ### (b) The log-linear goods-market condition -/

/-- Galí (2015), Ex. 3.2(b), p. 89: the government share `S_G = G/Y = e^g/(e^c + e^g)` as a
function of log consumption `c` and log purchases `g`. -/
noncomputable def shareG (c g : ℝ) : ℝ := Real.exp g / (Real.exp c + Real.exp g)

/-- Galí (2015), Ex. 3.2(b), p. 89: in levels, `S_G = G/(C + G) = G/Y`. -/
theorem shareG_log {C Gv : ℝ} (hC : 0 < C) (hG : 0 < Gv) :
    shareG (Real.log C) (Real.log Gv) = Gv / (C + Gv) := by
  rw [shareG, Real.exp_log hC, Real.exp_log hG]

/-- Galí (2015), Ex. 3.2(b), p. 89: `1 − S_G = C/Y`. -/
theorem one_sub_shareG (c g : ℝ) :
    1 - shareG c g = Real.exp c / (Real.exp c + Real.exp g) := by
  rw [shareG]
  have : Real.exp c + Real.exp g ≠ 0 := by positivity
  field_simp
  ring

/-- Galí (2015), Ex. 3.2(b), p. 89: `0 < S_G < 1`. -/
theorem shareG_mem (c g : ℝ) : 0 < shareG c g ∧ shareG c g < 1 := by
  have h1 := Real.exp_pos c
  have h2 := Real.exp_pos g
  refine ⟨by rw [shareG]; positivity, ?_⟩
  rw [shareG, div_lt_one (by positivity)]
  linarith

/-- Galí (2015), Ex. 3.2(b), p. 89: **log-linear goods-market clearing**. Log output
`y = log(e^c + e^g)` (from `Y = C + G`) has Fréchet derivative `(1 − S_G, S_G)` at any point
`(c, g)`; to first order around a steady state with share `S_G`,
`ŷ = (1 − S_G) ĉ + S_G ĝ`. -/
theorem hasFDerivAt_log_output (c g : ℝ) :
    HasFDerivAt (fun v : ℝ × ℝ => Real.log (Real.exp v.1 + Real.exp v.2))
      ((1 - shareG c g) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        shareG c g • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, g) := by
  have h1 := HasFDerivAt.exp (hasFDerivAt_fst (𝕜 := ℝ) (p := (c, g)))
  have h2 := HasFDerivAt.exp (hasFDerivAt_snd (𝕜 := ℝ) (p := (c, g)))
  have h := HasFDerivAt.log (HasFDerivAt.add h1 h2) (by simp only [Pi.add_apply]; positivity)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  rw [one_sub_shareG, shareG]
  simp only [smul_apply, add_apply, Pi.add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  have : Real.exp c + Real.exp g ≠ 0 := by positivity
  field_simp

/-! ### (c) Average real marginal cost -/

/-- Galí (2015), Ex. 3.2(c), p. 89 (with eq. (14), p. 59): aggregate employment
`N = (Y/A)^{1/(1−α)}` (price dispersion is of second order, App. 3.4). -/
noncomputable def empl (α Y A : ℝ) : ℝ := (Y / A) ^ (1 - α)⁻¹

/-- Galí (2015), Ex. 3.2(c), p. 89 (with p. 59–60): average real marginal cost, the real wage
`C^σ N^φ` (labour supply, with `C = Y − G`) over the marginal product of labour
`(1 − α) A N^{−α}`. -/
noncomputable def realMC (σ φ α Y Gv A : ℝ) : ℝ :=
  (Y - Gv) ^ σ * empl α Y A ^ φ / ((1 - α) * A * empl α Y A ^ (-α))

/-- Galí (2015), Ex. 3.2(c), p. 89: log real marginal cost in terms of log output `y`, log
purchases `g` and log technology `a`:
`σ log(e^y − e^g) + ((φ + α)/(1 − α))(y − a) − a − log(1 − α)`. -/
noncomputable def logMC (σ φ α y g a : ℝ) : ℝ :=
  σ * Real.log (Real.exp y - Real.exp g) + (φ + α) / (1 - α) * (y - a) - a - Real.log (1 - α)

/-- Galí (2015), Ex. 3.2(c), p. 89: the log of real marginal cost is `logMC` of the logs. -/
theorem log_realMC {σ φ α Y Gv A : ℝ} (hα : α < 1) (hG : 0 < Gv) (hYG : Gv < Y) (hA : 0 < A) :
    Real.log (realMC σ φ α Y Gv A) = logMC σ φ α (Real.log Y) (Real.log Gv) (Real.log A) := by
  have hY : 0 < Y := by linarith
  have hN : 0 < empl α Y A := Real.rpow_pos_of_pos (div_pos hY hA) _
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hlogN : Real.log (empl α Y A) = (Real.log Y - Real.log A) / (1 - α) := by
    rw [empl, Real.log_rpow (div_pos hY hA), Real.log_div hY.ne' hA.ne']
    field_simp
  rw [realMC, logMC, Real.exp_log hY, Real.exp_log hG,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by have : 0 < Y - Gv := by linarith
                     positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul h1α.ne' hA.ne',
    Real.log_rpow (by linarith), Real.log_rpow hN, Real.log_rpow hN, hlogN]
  field_simp
  ring

/-- Galí (2015), Ex. 3.2(c), p. 89: **log-linear average real marginal cost**. With
`S_G = e^g/e^y` (`= G/Y`), `logMC` has Fréchet derivative
`(σ/(1 − S_G) + (φ + α)/(1 − α), −σ S_G/(1 − S_G), −(1 + φ)/(1 − α))` in `(y, g, a)`, i.e.
`m̂c = (σ/(1 − S_G) + (φ + α)/(1 − α)) ŷ − (σ S_G/(1 − S_G)) ĝ − ((1 + φ)/(1 − α)) â`. -/
theorem hasFDerivAt_logMC {σ φ α y g a : ℝ} (hα : α < 1) (hgy : g < y) :
    HasFDerivAt (fun v : ℝ × ℝ × ℝ => logMC σ φ α v.1 v.2.1 v.2.2)
      ((σ / (1 - Real.exp g / Real.exp y) + (φ + α) / (1 - α)) •
          ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        (σ * (Real.exp g / Real.exp y) / (1 - Real.exp g / Real.exp y)) •
          (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
        ((1 + φ) / (1 - α)) •
          (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (y, g, a) := by
  have hey : Real.exp g < Real.exp y := Real.exp_lt_exp.mpr hgy
  have hne : Real.exp y - Real.exp g ≠ 0 := by linarith
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  have hy := hasFDerivAt_fst (𝕜 := ℝ) (p := (y, g, a))
  have hg := HasFDerivAt.fst (hasFDerivAt_snd (𝕜 := ℝ) (p := (y, g, a)))
  have ha := HasFDerivAt.snd (hasFDerivAt_snd (𝕜 := ℝ) (p := (y, g, a)))
  have hlog := HasFDerivAt.log (HasFDerivAt.sub (HasFDerivAt.exp hy) (HasFDerivAt.exp hg)) hne
  have h := HasFDerivAt.sub_const (Real.log (1 - α)) (HasFDerivAt.sub (HasFDerivAt.add
    (HasFDerivAt.const_mul hlog σ) (HasFDerivAt.const_mul (HasFDerivAt.sub hy ha)
      ((φ + α) / (1 - α)))) ha)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [sub_apply, add_apply, smul_apply, Pi.sub_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_comp,
    Function.comp_apply, smul_eq_mul]
  have hey0 : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  have hd : 1 - Real.exp g / Real.exp y = (Real.exp y - Real.exp g) / Real.exp y := by
    field_simp
  rw [hd]
  field_simp
  ring

/-- Galí (2015), Ex. 3.2(c), p. 89 (intuition): at given output and technology, government
purchases **lower** real marginal cost — they crowd out consumption, which raises the
marginal utility of consumption and lowers the real wage required for given hours:
the coefficient on `ĝ` is `−σ S_G/(1 − S_G) < 0`. -/
theorem mc_coeff_g_neg {σ SG : ℝ} (hσ : 0 < σ) (hS0 : 0 < SG) (hS1 : SG < 1) :
    -(σ * SG / (1 - SG)) < 0 := by
  have : 0 < σ * SG / (1 - SG) := div_pos (mul_pos hσ hS0) (by linarith)
  linarith

/-- Galí (2015), Ex. 3.2(c), p. 89: the elasticity of marginal cost with respect to output
rises with the government share: `σ/(1 − S_G) ≥ σ` for `0 ≤ S_G < 1`, `σ ≥ 0`. -/
theorem mc_coeff_y_ge {σ SG : ℝ} (hσ : 0 ≤ σ) (hS0 : 0 ≤ SG) (hS1 : SG < 1) :
    σ ≤ σ / (1 - SG) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-! ### (d) The dynamic IS equation with government purchases -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (3), p. 54: the log-linear Euler equation in deviations,
`ĉ_t = E_t ĉ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)`. -/
def Euler (σ ρ : ℝ) (c i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)

/-- Galí (2015), Ex. 3.2(d), p. 89: the dynamic IS equation with government purchases,
`ŷ_t = E_t ŷ_{t+1} − ((1 − S_G)/σ)(i_t − E_t π_{t+1} − ρ) + S_G (ĝ_t − E_t ĝ_{t+1})`. -/
def DISG (σ ρ SG : ℝ) (y g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - ((1 - SG) / σ) • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ) +
    SG • (g t - 𝔼.E t (g (t + 1)))

/-- Galí (2015), Ex. 3.2(d), p. 89: **the DIS with government purchases**. Given the
log-linear goods-market condition `ŷ = (1 − S_G) ĉ + S_G ĝ` (part (b)) and `S_G < 1`, the
Euler equation holds if and only if the modified DIS holds: the interest elasticity of output
falls to `(1 − S_G)/σ` and expected changes in purchases shift the relation. -/
theorem dis_iff {σ ρ SG : ℝ} (hS : SG ≠ 1) {y c g i infl : ℕ → Ω → ℝ}
    (hgm : ∀ t, y t = (1 - SG) • c t + SG • g t) :
    Euler 𝔼 σ ρ c i infl ↔ DISG 𝔼 σ ρ SG y g i infl := by
  have hE : ∀ t, 𝔼.E t (y (t + 1)) = (1 - SG) • 𝔼.E t (c (t + 1)) + SG • 𝔼.E t (g (t + 1)) :=
    fun t => by rw [hgm (t + 1), map_add, map_smul, map_smul]
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h3 := congrFun (hE t) ω
    have h4 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h3 h4 ⊢
    rw [div_eq_mul_inv]
    linear_combination h1 - h3 + (1 - SG) * h4
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h3 := congrFun (hE t) ω
    have h5 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h3 h5 ⊢
    rw [div_eq_mul_inv] at h5
    have hk : (1 - SG) * (c t ω - (𝔼.E t (c (t + 1)) ω -
        σ⁻¹ * (i t ω - 𝔼.E t (infl (t + 1)) ω - ρ))) = 0 := by
      linear_combination -h1 + h3 + h5
    rcases mul_eq_zero.1 hk with h0 | h0
    · exact absurd (by linarith : SG = 1) hS
    · linarith

/-- Galí (2015), Ex. 3.2(d), p. 89: with AR(1) purchases, `E_t ĝ_{t+1} = ρ_g ĝ_t`, the fiscal
term of the DIS is `S_G (1 − ρ_g) ĝ_t`: a persistent rise in purchases raises output demand
on impact relative to expected future output. -/
theorem dis_ar1_term {SG ρg : ℝ} {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (t : ℕ) :
    SG • (g t - 𝔼.E t (g (t + 1))) = (SG * (1 - ρg)) • g t := by
  rw [hg.2 t]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

end Gali.BasicNewKeynesianModel.Ex3_2
