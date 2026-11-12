/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5aLambdaILimit
import OptimalPolicyRules.TidyR5aLambdaXZeroMeasure

/-!
# The equilibrium paths converge as `λ_i → 0`, with conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, p. 591: as the weight `λ_i` on interest
rate variability goes to zero, equilibria under the optimal rule (3.7) approach the Chapter 7
optimal paths (the criterion (2.5)). This is the measure-theoretic version of
`TidyR5aLambdaILimit`, on every filtered probability space with Mathlib's conditional expectation,
for essentially bounded adapted equilibria (`RuleEqmM`) and every essentially bounded adapted
solution of (2.1) and (2.5).

* `g_bound`: along a solution of the rule, the (2.5) residual is bounded a.s. by the right-hand
  side of (3.13); proved by applying Proposition 8.6 (`IRuleForwardIntegrated.rule_iff_crit313`)
  and `TidyR5aLambdaILimit.abs_g_le` to the conditional forecast paths (`fc_rule`).
* `d_step`, `d_bound`: the Lipschitz step for the difference of two solutions of (2.1) with
  forced (2.5) residual, again through the forecast paths (minus the homogeneous solution).
* `paths_convergeM`: for every `ε > 0`, eventually in `n`, at **every** date,
  `|πⁿ_t − π⁰_t|, |xⁿ_t − x⁰_t|, |iⁿ_t − i⁰_t| ≤ ε` a.s., with `i⁰` read off (3.1) (`i0M`).

Not covered: the existence of the equilibria `(πⁿ, xⁿ, iⁿ)` and `(π⁰, x⁰)` with conditional
expectations (they are hypotheses here, as is the existence in the perfect-foresight version).
-/

namespace Woodford.OptimalPolicyRules.TidyR5aLambdaILimitMeasure

open MeasureTheory Filter Topology
open ExpectationsMeasure
open IRuleBasic (Calib lag rho1 rho2 phiPi phiX)
open TidyR5aLambdaXZeroMeasure (BndM AdaptedM E_lin4 integrable_of_sm)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The model with conditional expectations -/

/-- Woodford (2003), (2.1), p. 560, a.s. at date `t`: `π_t = κx_t + βE_tπ_{t+1} + u_t`. -/
def ASb (S : MeasExpectationSystem Ω) (c : Calib) (u π x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, π t ω = c.κ * x t ω + c.β * S.E t (π (t + 1)) ω + u t ω

/-- Woodford (2003), (3.1), p. 583, a.s. at date `t`:
`x_t = E_tx_{t+1} − σ(i_t − E_tπ_{t+1} − rⁿ_t)`. -/
def ISb (S : MeasExpectationSystem Ω) (c : Calib) (rn π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, x t ω = S.E t (x (t + 1)) ω - c.σ * (i t ω - S.E t (π (t + 1)) ω - rn t ω)

/-- Woodford (2003), (3.7), p. 584, a.s. at date `t`: the optimal implicit instrument rule
`i_t = (1 − ρ₁)i* + ρ₁i_{t−1} + ρ₂Δi_{t−1} + φ_ππ_t + φ_xΔx_t/4` (history `x_{−1}, i_{−1},
i_{−2}`). -/
def RuleM (S : MeasExpectationSystem Ω) (c : Calib) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ)
    (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, i t ω = (1 - rho1 c.β c.σ c.κ) * c.istar + rho1 c.β c.σ c.κ * lag im1 i t ω +
    rho2 c.β * (lag im1 i t ω - lag im2 (lag im1 i) t ω) + phiPi c.σ c.κ c.li * π t ω +
    phiX c.σ c.lx c.li / 4 * (x t ω - lag xm1 x t ω)

/-- Woodford (2003), (2.1), (3.1), (3.7), p. 584, on a filtered probability space: an
equilibrium under the rule. -/
def RuleEqmM (S : MeasExpectationSystem Ω) (c : Calib) (rn u : ℕ → Ω → ℝ) (xm1 im1 im2 : ℝ)
    (π x i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ASb S c u π x t ∧ ISb S c rn π x i t ∧ RuleM S c xm1 im1 im2 π x i t

/-- Woodford (2003), (2.5), p. 561, a.s. at every date: `π_t + (λ_x/κ)(x_t − x_{t−1}) = 0`. -/
def Crit25M (S : MeasExpectationSystem Ω) (c : Calib) (xm1 : ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, π t ω + c.lx / c.κ * (x t ω - lag xm1 x t ω) = 0

/-! ### Conditional forecasts -/

/-- Woodford (2003), p. 540 (tool): the forecast of a lagged process is the lag of the forecast
path, with the date-`t` lag as initial value. -/
theorem fc_lag (S : MeasExpectationSystem Ω) {f : ℕ → Ω → ℝ} (hfa : AdaptedM S f)
    (hfi : ∀ k, Integrable (f k) S.μ) (z0 : ℝ) (t k : ℕ) (ω : Ω) :
    S.E t (lag z0 f (t + k)) ω = lag (lag z0 f t ω) (fun j (_ : Unit) => S.E t (f (t + j)) ω) k ()
        := by
  cases k with
  | zero =>
    have hk : StronglyMeasurable[S.𝓕 t] (lag z0 f t) ∧ Integrable (lag z0 f t) S.μ := by
      cases t with
      | zero => exact ⟨stronglyMeasurable_const, integrable_const _⟩
      | succ s => exact ⟨(hfa s).mono (S.𝓕.mono (Nat.le_succ s)), hfi s⟩
    rw [add_zero, S.E_of_stronglyMeasurable hk.1 hk.2]
    rfl
  | succ j => rfl

/-- Woodford (2003), p. 540 (tool): `E_t` of an affine combination of five integrable random
variables, a.s. -/
theorem E_lin5 (S : MeasExpectationSystem Ω) (t : ℕ) (a1 a2 a3 a4 a5 b : ℝ)
    {f1 f2 f3 f4 f5 : Ω → ℝ} (h1 : Integrable f1 S.μ) (h2 : Integrable f2 S.μ)
    (h3 : Integrable f3 S.μ) (h4 : Integrable f4 S.μ) (h5 : Integrable f5 S.μ) :
    ∀ᵐ ω ∂S.μ, S.E t (fun ω => b + a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω + a5 * f5 ω) ω =
      b + a1 * S.E t f1 ω + a2 * S.E t f2 ω + a3 * S.E t f3 ω + a4 * S.E t f4 ω +
        a5 * S.E t f5 ω := by
  have e : (fun ω => b + a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω + a5 * f5 ω) =
      (fun ω => a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω) + (a5 • f5 + fun _ => b) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have i4 : Integrable (fun ω => a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω) S.μ :=
    (((h1.const_mul a1).add (h2.const_mul a2)).add (h3.const_mul a3)).add (h4.const_mul a4)
  have i5 : Integrable (a5 • f5 + fun _ => b) S.μ := (h5.smul a5).add (integrable_const b)
  rw [e]
  filter_upwards [S.E_add i4 i5 t, E_lin4 S t a1 a2 a3 a4 h1 h2 h3 h4,
    S.E_add (h5.smul a5) (integrable_const b) t, S.E_smul a5 f5 t] with ω e1 e2 e3 e4
  rw [e1, Pi.add_apply, e2, e3, Pi.add_apply, e4, S.E_const]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 584 (tool): a lagged adapted process is adapted. -/
theorem lag_adaptedM (S : MeasExpectationSystem Ω) {f : ℕ → Ω → ℝ} (hfa : AdaptedM S f)
    (z0 : ℝ) : AdaptedM S (lag z0 f) := by
  intro k
  cases k with
  | zero => exact stronglyMeasurable_const
  | succ s => exact (hfa s).mono (S.𝓕.mono (Nat.le_succ s))

/-- Woodford (2003), p. 584 (tool): a lagged integrable process is integrable. -/
theorem lag_integrable {S : MeasExpectationSystem Ω} {f : ℕ → Ω → ℝ}
    (hfi : ∀ k, Integrable (f k) S.μ) (z0 : ℝ) (k : ℕ) : Integrable (lag z0 f k) S.μ := by
  cases k with
  | zero => exact integrable_const _
  | succ s => exact hfi s

/-- **Woodford (2003), (3.7), with conditional expectations: the forecasts follow the rule.** At
almost every outcome the conditional forecasts `k ↦ E_t(π, x, i)_{t+k}` satisfy the rule (3.7) at
every date under perfect foresight, with the date-`t` lags as history. -/
theorem fc_rule (S : MeasExpectationSystem Ω) (c : Calib) {xm1 im1 im2 : ℝ} {π x i : ℕ → Ω → ℝ}
    (hR : ∀ t, RuleM S c xm1 im1 im2 π x i t) (hxa : AdaptedM S x)
    (hia : AdaptedM S i) (hπi : ∀ k, Integrable (π k) S.μ) (hxi : ∀ k, Integrable (x k) S.μ)
    (hii : ∀ k, Integrable (i k) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ k, IRuleBasic.Rule c (lag xm1 x t ω) (lag im1 i t ω) (lag im2 (lag im1 i) t ω)
      (fun j (_ : Unit) => S.E t (π (t + j)) ω) (fun j (_ : Unit) => S.E t (x (t + j)) ω)
      (fun j (_ : Unit) => S.E t (i (t + j)) ω) k := by
  have hLa := lag_adaptedM S hia im1
  have hLi := lag_integrable hii im1
  refine ae_all_iff.2 fun k => ?_
  have e : (fun ω => (1 - rho1 c.β c.σ c.κ) * c.istar + rho1 c.β c.σ c.κ * lag im1 i (t + k) ω +
      rho2 c.β * (lag im1 i (t + k) ω - lag im2 (lag im1 i) (t + k) ω) +
      phiPi c.σ c.κ c.li * π (t + k) ω + phiX c.σ c.lx c.li / 4 * (x (t + k) ω -
        lag xm1 x (t + k) ω)) = fun ω => (1 - rho1 c.β c.σ c.κ) * c.istar +
      (rho1 c.β c.σ c.κ + rho2 c.β) * lag im1 i (t + k) ω +
      (-rho2 c.β) * lag im2 (lag im1 i) (t + k) ω + phiPi c.σ c.κ c.li * π (t + k) ω +
      (phiX c.σ c.lx c.li / 4) * x (t + k) ω + (-(phiX c.σ c.lx c.li / 4)) *
        lag xm1 x (t + k) ω := by
    funext ω
    ring
  filter_upwards [S.E_congr (hR (t + k)) t, E_lin5 S t (rho1 c.β c.σ c.κ + rho2 c.β)
    (-rho2 c.β) (phiPi c.σ c.κ c.li) (phiX c.σ c.lx c.li / 4) (-(phiX c.σ c.lx c.li / 4))
    ((1 - rho1 c.β c.σ c.κ) * c.istar) (hLi (t + k)) (lag_integrable hLi im2 (t + k))
    (hπi (t + k)) (hxi (t + k)) (lag_integrable hxi xm1 (t + k))] with ω e1 e2
  rw [e] at e1
  rw [e2] at e1
  have l1 := fc_lag S hia hii im1 t k ω
  have l2 := fc_lag S hLa hLi im2 t k ω
  have l3 := fc_lag S hxa hxi xm1 t k ω
  have hpath : (fun j (_ : Unit) => S.E t (lag im1 i (t + j)) ω) =
      lag (lag im1 i t ω) (fun j (_ : Unit) => S.E t (i (t + j)) ω) := by
    funext j u
    exact fc_lag S hia hii im1 t j ω
  rw [hpath] at l2
  funext u
  cases u
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [← l1, ← l2, ← l3]
  rw [e1]
  ring

/-- **Woodford (2003), (3.13) and (2.5), with conditional expectations: the (2.5) residual is
bounded by the right-hand side of (3.13).** Along a solution of the rule (3.7) with `|i| ≤ I`
a.s. (and `|i_{−1}|, |i_{−2}| ≤ I`), a.s. at every date
`|π_t + (λ_x/κ)(x_t − x_{t−1})| ≤ (1 + λ₂⁻¹)/(1 − λ₂⁻¹)·(θ_i + 2θ_Δ)(3I + |i*|)`. The proof
applies Proposition 8.6 (`IRuleForwardIntegrated.rule_iff_crit313`) and
`TidyR5aLambdaILimit.abs_g_le` to the perfect-foresight forecast paths (`fc_rule`). -/
theorem g_bound (c : Calib) (hc : c.Adm) {S : MeasExpectationSystem Ω} {xm1 im1 im2 : ℝ}
    {π x i : ℕ → Ω → ℝ} (hR : ∀ t, RuleM S c xm1 im1 im2 π x i t) (hπa : AdaptedM S π)
    (hxa : AdaptedM S x) (hia : AdaptedM S i) {Mπ Mx I : ℝ}
    (hπb : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (hxb : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ Mx)
    (hib : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ I) (hI0 : 0 ≤ I) (h1 : |im1| ≤ I) (h2 : |im2| ≤ I) :
    ∀ t, ∀ᵐ ω ∂S.μ, |π t ω + c.lx / c.κ * (x t ω - lag xm1 x t ω)| ≤
      (1 + (IRuleForwardIntegrated.L2c c)⁻¹) / (1 - (IRuleForwardIntegrated.L2c c)⁻¹) *
        ((IRuleForwardIntegrated.thetaI c + 2 * IRuleForwardIntegrated.thetaD c) *
          (I + (I + I + |c.istar|))) := by
  intro t
  have hπi : ∀ k, Integrable (π k) S.μ := fun k => integrable_of_sm S (hπa k) (hπb k)
  have hxi : ∀ k, Integrable (x k) S.μ := fun k => integrable_of_sm S (hxa k) (hxb k)
  have hii : ∀ k, Integrable (i k) S.μ := fun k => integrable_of_sm S (hia k) (hib k)
  have hEb : ∀ (f : ℕ → Ω → ℝ) (M : ℝ), (∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ M) →
      ∀ᵐ ω ∂S.μ, ∀ j, |S.E t (f (t + j)) ω| ≤ M := fun f M hf =>
    ae_all_iff.2 fun j => S.abs_E_le (hf (t + j)) t
  have hl1 : ∀ᵐ ω ∂S.μ, |lag im1 i t ω| ≤ I := by
    cases t with
    | zero => exact ae_of_all _ fun ω => h1
    | succ s => exact hib s
  have hl2 : ∀ᵐ ω ∂S.μ, |lag im2 (lag im1 i) t ω| ≤ I := by
    cases t with
    | zero => exact ae_of_all _ fun ω => h2
    | succ s =>
      cases s with
      | zero => exact ae_of_all _ fun ω => h1
      | succ r => exact hib r
  filter_upwards [fc_rule S c hR hxa hia hπi hxi hii t, hEb π Mπ hπb, hEb x Mx hxb,
    hEb i I hib, hl1, hl2] with ω hfc bπ bx bi e1 e2
  set Pπ : ℕ → Unit → ℝ := fun j _ => S.E t (π (t + j)) ω with hPπ
  set Px : ℕ → Unit → ℝ := fun j _ => S.E t (x (t + j)) ω with hPx
  set Pk : ℕ → Unit → ℝ := fun j _ => S.E t (i (t + j)) ω with hPk
  have hcrit := (IRuleForwardIntegrated.rule_iff_crit313 perfectForesight c hc (lag xm1 x t ω)
    (lag im1 i t ω) (lag im2 (lag im1 i) t ω) (π := Pπ) (x := Px) (i := Pk) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ⟨Mπ, fun k _ => bπ k⟩ ⟨Mx, fun k _ => bx k⟩
    ⟨I, fun k _ => bi k⟩).mp hfc
  have hres := fun k u => TidyR5aLambdaILimit.abs_resid_le c hc (im1 := lag im1 i t ω)
    (im2 := lag im2 (lag im1 i) t ω) (i := Pk) (fun k _ => bi k) hI0 k u
  have hg := TidyR5aLambdaILimit.abs_g_le perfectForesight c hc (fun _ => rfl) (fun _ => rfl)
    ⟨Mπ, fun k _ => bπ k⟩ ⟨Mx, fun k _ => bx k⟩ hcrit hres 0 ()
  have hπt : S.E t (π t) ω = π t ω :=
    congrFun (S.E_of_stronglyMeasurable (hπa t) (hπi t)) ω
  have hxt : S.E t (x t) ω = x t ω :=
    congrFun (S.E_of_stronglyMeasurable (hxa t) (hxi t)) ω
  have eg : TidyR5aLambdaILimit.gres c (lag xm1 x t ω) Pπ Px 0 () =
      π t ω + c.lx / c.κ * (x t ω - lag xm1 x t ω) := by
    simp only [TidyR5aLambdaILimit.gres, one_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hPπ, hPx, add_zero, hπt, hxt]
    rfl
  rw [eg] at hg
  refine hg.trans ?_
  obtain ⟨-, -, hL2, -, -⟩ := IRuleForwardIntegrated.L_props c hc
  obtain ⟨-, -, hθI, hθD⟩ := IRuleForwardIntegrated.coef313_pos c hc
  have hK1 : 0 ≤ (1 + (IRuleForwardIntegrated.L2c c)⁻¹) / (1 - (IRuleForwardIntegrated.L2c c)⁻¹)
      := by
    have : (IRuleForwardIntegrated.L2c c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL2
    have : 0 ≤ (IRuleForwardIntegrated.L2c c)⁻¹ := inv_nonneg.mpr (by linarith)
    exact div_nonneg (by linarith) (by linarith)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hK1
  linarith

/-- **Woodford (2003), (2.1) and (2.5), with conditional expectations: one step of the Lipschitz
bound.** If `d, e` are essentially bounded adapted with `e_t = κd_t + βE_te_{t+1}` and
`e_t + φ(d_t − d_{t−1}) = h_t` a.s. (`d_{−1} = 0`), `|h| ≤ G` a.s., then a.s.
`|d_t − μ₁d_{t−1}| ≤ C2·G`. The forecast paths from date `t`, minus the homogeneous solution
`μ₁ᵏ⁺¹d_{t−1}`, satisfy the hypotheses of `TidyR5aLambdaILimit.diff_bound` under perfect
foresight. -/
theorem d_step {S : MeasExpectationSystem Ω} {β κ φ G : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hφ : 0 < φ) (hG : 0 ≤ G) {d e h : ℕ → Ω → ℝ} (hda : AdaptedM S d)
    (hea : AdaptedM S e) (hha : AdaptedM S h) {Md Me : ℝ}
    (hdb : ∀ t, ∀ᵐ ω ∂S.μ, |d t ω| ≤ Md) (heb : ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ Me)
    (hhb : ∀ t, ∀ᵐ ω ∂S.μ, |h t ω| ≤ G)
    (hAS : ∀ t, ∀ᵐ ω ∂S.μ, e t ω = κ * d t ω + β * S.E t (e (t + 1)) ω)
    (hcr : ∀ t, ∀ᵐ ω ∂S.μ, e t ω + φ * (d t ω - lag 0 d t ω) = h t ω) :
    ∀ t, ∀ᵐ ω ∂S.μ, |d t ω - QuadraticRoots.lam1 β (κ / φ) * lag 0 d t ω| ≤
      TidyR5aLambdaILimit.C2 β κ φ * G := by
  intro t
  have hc : 0 < κ / φ := div_pos hκ hφ
  set μ := QuadraticRoots.lam1 β (κ / φ) with hμ
  have hμ0 : 0 < μ := QuadraticRoots.lam1_pos hβ0 hc
  have hμ1 : μ < 1 := QuadraticRoots.lam1_lt_one hβ0 hc
  have hroot : β * μ ^ 2 - (1 + β + κ / φ) * μ + 1 = 0 := QuadraticRoots.lam1_root hβ0 hc
  have hdi : ∀ k, Integrable (d k) S.μ := fun k => integrable_of_sm S (hda k) (hdb k)
  have hei : ∀ k, Integrable (e k) S.μ := fun k => integrable_of_sm S (hea k) (heb k)
  have hhi : ∀ k, Integrable (h k) S.μ := fun k => integrable_of_sm S (hha k) (hhb k)
  have hEb : ∀ (f : ℕ → Ω → ℝ) (M : ℝ), (∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ M) →
      ∀ᵐ ω ∂S.μ, ∀ j, |S.E t (f (t + j)) ω| ≤ M := fun f M hf =>
    ae_all_iff.2 fun j => S.abs_E_le (hf (t + j)) t
  -- (2.1) along the forecasts
  have hASf : ∀ᵐ ω ∂S.μ, ∀ j, S.E t (e (t + j)) ω =
      κ * S.E t (d (t + j)) ω + β * S.E t (e (t + j + 1)) ω := by
    refine ae_all_iff.2 fun j => ?_
    filter_upwards [S.E_congr (hAS (t + j)) t, E_lin4 S t κ β 0 0 (hdi (t + j))
      (S.integrable_E (t + j) (e (t + j + 1))) (hdi 0) (hdi 0),
      S.E_tower (Nat.le_add_right t j) (e (t + j + 1))] with ω e1 e2 e3
    have ee : (fun ω => κ * d (t + j) ω + β * S.E (t + j) (e (t + j + 1)) ω) =
        fun ω => κ * d (t + j) ω + β * S.E (t + j) (e (t + j + 1)) ω + 0 * d 0 ω + 0 * d 0 ω := by
      funext ω
      ring
    rw [e1, ee, e2]
    have : S.E t (S.E (t + j) (e (t + j + 1))) ω = S.E t (e (t + j + 1)) ω := e3
    rw [this]
    ring
  -- (2.5) along the forecasts
  have hcrf : ∀ᵐ ω ∂S.μ, ∀ j, S.E t (e (t + j)) ω + φ * (S.E t (d (t + j)) ω -
      lag (lag 0 d t ω) (fun k (_ : Unit) => S.E t (d (t + k)) ω) j ()) = S.E t (h (t + j)) ω := by
    refine ae_all_iff.2 fun j => ?_
    filter_upwards [S.E_congr (hcr (t + j)) t, E_lin4 S t 1 φ (-φ) 0 (hei (t + j)) (hdi (t + j))
      (lag_integrable hdi 0 (t + j)) (hdi 0)] with ω e1 e2
    have ee : (fun ω => e (t + j) ω + φ * (d (t + j) ω - lag 0 d (t + j) ω)) =
        fun ω => 1 * e (t + j) ω + φ * d (t + j) ω + (-φ) * lag 0 d (t + j) ω + 0 * d 0 ω := by
      funext ω
      ring
    rw [ee, e2] at e1
    rw [← fc_lag S hda hdi 0 t j ω, ← e1]
    ring
  filter_upwards [hASf, hcrf, hEb d Md hdb, hEb h G hhb] with ω eAS ecr bd bh
  set y0 := lag 0 d t ω with hy0
  set pd : ℕ → ℝ := fun j => S.E t (d (t + j)) ω with hpd
  set pe : ℕ → ℝ := fun j => S.E t (e (t + j)) ω with hpe
  set d' : ℕ → Unit → ℝ := fun j _ => pd j - μ ^ (j + 1) * y0 with hd'
  set e' : ℕ → Unit → ℝ := fun j _ => pe j - φ * μ ^ j * (1 - μ) * y0 with he'
  have hd'b : BoundedProc d' := ⟨Md + |y0|, fun j _ => by
    simp only [hd']
    have h1 : |μ ^ (j + 1) * y0| ≤ |y0| := by
      rw [abs_mul, abs_pow, abs_of_pos hμ0]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hμ0.le hμ1.le)
    exact (abs_sub _ _).trans (add_le_add (bd j) h1)⟩
  have hAS' : ∀ j u, e' j u = κ * d' j u + β * perfectForesight.E j (e' (j + 1)) u := by
    intro j u
    change pe j - φ * μ ^ j * (1 - μ) * y0 = κ * (pd j - μ ^ (j + 1) * y0) +
      β * (pe (j + 1) - φ * μ ^ (j + 1) * (1 - μ) * y0)
    have h1 := eAS j
    simp only [hpe, hpd] at h1 ⊢
    rw [show t + (j + 1) = t + j + 1 by omega]
    have h2 : β * φ * μ ^ 2 - (φ + β * φ + κ) * μ + φ = 0 := by
      have e : φ * (β * μ ^ 2 - (1 + β + κ / φ) * μ + 1) =
          β * φ * μ ^ 2 - (φ + β * φ + κ) * μ + φ := by
        field_simp
      rw [← e, hroot, mul_zero]
    have hr : φ * μ ^ j * (1 - μ) = κ * μ ^ (j + 1) + β * (φ * μ ^ (j + 1) * (1 - μ)) := by
      linear_combination μ ^ j * h2
    linear_combination h1 - y0 * hr
  have hcr' : ∀ j u, e' j u + φ * (d' j u - InflTargetInertia.lagW (fun _ => 0) d' j u) =
      S.E t (h (t + j)) ω := by
    intro j u
    have h1 := ecr j
    cases j with
    | zero =>
      change pe 0 - φ * μ ^ 0 * (1 - μ) * y0 + φ * (pd 0 - μ ^ (0 + 1) * y0 - 0) = _
      rw [← h1]
      simp only [hpe, hpd]
      change _ = S.E t (e (t + 0)) ω + φ * (S.E t (d (t + 0)) ω - y0)
      ring
    | succ k =>
      change pe (k + 1) - φ * μ ^ (k + 1) * (1 - μ) * y0 +
        φ * (pd (k + 1) - μ ^ (k + 1 + 1) * y0 - (pd k - μ ^ (k + 1) * y0)) = _
      rw [← h1]
      simp only [hpe, hpd]
      change _ = S.E t (e (t + (k + 1))) ω + φ * (S.E t (d (t + (k + 1))) ω - S.E t (d (t + k)) ω)
      ring
  have key := TidyR5aLambdaILimit.diff_bound perfectForesight hβ0 hβ1 hκ hφ hG (d := d')
    (e := e') (h := fun j _ => S.E t (h (t + j)) ω) (fun _ => rfl) hd'b (fun _ => rfl)
    (fun j _ => bh j) hAS' hcr' 0 ()
  have hdt : pd 0 = d t ω := by
    simp only [hpd, add_zero]
    exact congrFun (S.E_of_stronglyMeasurable (hda t) (hdi t)) ω
  simp only [hd', hdt, zero_add, pow_one] at key
  exact key

/-- **Woodford (2003), (2.1) and (2.5), with conditional expectations: the Lipschitz bound.**
Under the hypotheses of `d_step`, `|d| ≤ C2·G/(1 − μ₁)` a.s. at every date (by induction from
`d_{−1} = 0`). -/
theorem d_bound {S : MeasExpectationSystem Ω} {β κ φ G : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hφ : 0 < φ) (hG : 0 ≤ G) {d e h : ℕ → Ω → ℝ} (hda : AdaptedM S d)
    (hea : AdaptedM S e) (hha : AdaptedM S h) {Md Me : ℝ}
    (hdb : ∀ t, ∀ᵐ ω ∂S.μ, |d t ω| ≤ Md) (heb : ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ Me)
    (hhb : ∀ t, ∀ᵐ ω ∂S.μ, |h t ω| ≤ G)
    (hAS : ∀ t, ∀ᵐ ω ∂S.μ, e t ω = κ * d t ω + β * S.E t (e (t + 1)) ω)
    (hcr : ∀ t, ∀ᵐ ω ∂S.μ, e t ω + φ * (d t ω - lag 0 d t ω) = h t ω) :
    ∀ t, ∀ᵐ ω ∂S.μ, |d t ω| ≤
      TidyR5aLambdaILimit.C2 β κ φ * G / (1 - QuadraticRoots.lam1 β (κ / φ)) := by
  have hc : 0 < κ / φ := div_pos hκ hφ
  set μ := QuadraticRoots.lam1 β (κ / φ) with hμ
  have hμ0 : 0 < μ := QuadraticRoots.lam1_pos hβ0 hc
  have hμ1 : μ < 1 := QuadraticRoots.lam1_lt_one hβ0 hc
  have h1μ : 0 < 1 - μ := by linarith
  have hst := d_step hβ0 hβ1 hκ hφ hG hda hea hha hdb heb hhb hAS hcr
  have hC : 0 ≤ TidyR5aLambdaILimit.C2 β κ φ * G :=
    mul_nonneg (TidyR5aLambdaILimit.C2_nonneg hβ0 hβ1 hκ hφ) hG
  set B := TidyR5aLambdaILimit.C2 β κ φ * G / (1 - μ) with hB
  have hBeq : TidyR5aLambdaILimit.C2 β κ φ * G + μ * B = B := by
    rw [hB]
    field_simp
    ring
  have hB0 : 0 ≤ B := div_nonneg hC h1μ.le
  intro t
  induction t with
  | zero =>
    filter_upwards [hst 0] with ω e
    have : lag 0 d 0 ω = 0 := rfl
    rw [this, mul_zero, sub_zero] at e
    refine e.trans ?_
    have : μ * B ≥ 0 := mul_nonneg hμ0.le hB0
    linarith
  | succ t ih =>
    filter_upwards [hst (t + 1), ih] with ω e1 e2
    have : lag 0 d (t + 1) ω = d t ω := rfl
    rw [this] at e1
    have h3 : |μ * d t ω| ≤ μ * B := by
      rw [abs_mul, abs_of_pos hμ0]
      exact mul_le_mul_of_nonneg_left e2 hμ0.le
    calc |d (t + 1) ω| = |(d (t + 1) ω - μ * d t ω) + μ * d t ω| := by ring_nf
      _ ≤ |d (t + 1) ω - μ * d t ω| + |μ * d t ω| := abs_add_le _ _
      _ ≤ TidyR5aLambdaILimit.C2 β κ φ * G + μ * B := add_le_add e1 h3
      _ = B := hBeq

/-- Woodford (2003), (3.1), p. 583: the limit interest rate read off the IS relation,
`i⁰_t = E_tπ⁰_{t+1} + rⁿ_t + σ⁻¹(E_tx⁰_{t+1} − x⁰_t)`, with conditional expectations. -/
noncomputable def i0M (S : MeasExpectationSystem Ω) (c : Calib) (rn π0 x0 : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => S.E t (π0 (t + 1)) ω + rn t ω + c.σ⁻¹ * (S.E t (x0 (t + 1)) ω - x0 t ω)

/-- **Woodford (2003), (2.1), (2.5) and (3.1), with conditional expectations: the distance to the
(2.5) equilibrium is controlled by the (2.5) residual.** If a bounded adapted plan satisfies
(2.1) and (3.1) a.s. and `|π_t + (λ_x/κ)(x_t − x_{t−1})| ≤ G` a.s., then a.s.
`|x − x⁰| ≤ K'G`, `|π − π⁰| ≤ (1 + 2φK')G`, `|i − i⁰| ≤ (1 + 2φK' + 2σ⁻¹K')G`, with
`K' = C2/(1 − μ₁)`, `φ = λ_x/κ`, for every bounded adapted solution `(π⁰, x⁰)` of (2.1), (2.5). -/
theorem step_boundM (c : Calib) (hc : c.Adm) {S : MeasExpectationSystem Ω} {rn u : ℕ → Ω → ℝ}
    {xm1 : ℝ} {π x i π0 x0 : ℕ → Ω → ℝ}
    (hπa : AdaptedM S π) (hxa : AdaptedM S x) (hπb : BndM S π) (hxb : BndM S x)
    (hAS : ∀ t, ASb S c u π x t) (hIS : ∀ t, ISb S c rn π x i t) (hπ0a : AdaptedM S π0)
    (hx0a : AdaptedM S x0) (hπ0b : BndM S π0) (hx0b : BndM S x0)
    (hAS0 : ∀ t, ASb S c u π0 x0 t) (hcr0 : Crit25M S c xm1 π0 x0) {G : ℝ} (hG : 0 ≤ G)
    (hg : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω + c.lx / c.κ * (x t ω - lag xm1 x t ω)| ≤ G) :
    ∀ t, ∀ᵐ ω ∂S.μ,
      |x t ω - x0 t ω| ≤ TidyR5aLambdaILimit.C2 c.β c.κ (c.lx / c.κ) /
        (1 - QuadraticRoots.lam1 c.β (c.κ / (c.lx / c.κ))) * G ∧
      |π t ω - π0 t ω| ≤ (1 + 2 * (c.lx / c.κ) * (TidyR5aLambdaILimit.C2 c.β c.κ (c.lx / c.κ) /
        (1 - QuadraticRoots.lam1 c.β (c.κ / (c.lx / c.κ))))) * G ∧
      |i t ω - i0M S c rn π0 x0 t ω| ≤ (1 + 2 * (c.lx / c.κ) *
        (TidyR5aLambdaILimit.C2 c.β c.κ (c.lx / c.κ) /
          (1 - QuadraticRoots.lam1 c.β (c.κ / (c.lx / c.κ)))) +
        2 * c.σ⁻¹ * (TidyR5aLambdaILimit.C2 c.β c.κ (c.lx / c.κ) /
          (1 - QuadraticRoots.lam1 c.β (c.κ / (c.lx / c.κ))))) * G := by
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, -⟩ := hc
  set φ := c.lx / c.κ with hφdef
  have hφ : 0 < φ := div_pos hlx hκ
  set K := TidyR5aLambdaILimit.C2 c.β c.κ φ / (1 - QuadraticRoots.lam1 c.β (c.κ / φ)) with hK
  have hcφ : 0 < c.κ / φ := div_pos hκ hφ
  have hK0 : 0 ≤ K := div_nonneg (TidyR5aLambdaILimit.C2_nonneg hβ0 hβ1 hκ hφ)
    (by linarith [QuadraticRoots.lam1_lt_one hβ0 hcφ])
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπ0, hMπ0⟩ := hπ0b
  obtain ⟨Mx0, hMx0⟩ := hx0b
  have hπi : ∀ k, Integrable (π k) S.μ := fun k => integrable_of_sm S (hπa k) (hMπ k)
  have hxi : ∀ k, Integrable (x k) S.μ := fun k => integrable_of_sm S (hxa k) (hMx k)
  have hπ0i : ∀ k, Integrable (π0 k) S.μ := fun k => integrable_of_sm S (hπ0a k) (hMπ0 k)
  have hx0i : ∀ k, Integrable (x0 k) S.μ := fun k => integrable_of_sm S (hx0a k) (hMx0 k)
  set d : ℕ → Ω → ℝ := fun t ω => x t ω - x0 t ω with hd
  set e : ℕ → Ω → ℝ := fun t ω => π t ω - π0 t ω with he
  set h : ℕ → Ω → ℝ := fun t ω => π t ω + φ * (x t ω - lag xm1 x t ω) with hh
  have hda : AdaptedM S d := fun t => (hxa t).sub (hx0a t)
  have hea : AdaptedM S e := fun t => (hπa t).sub (hπ0a t)
  have hha : AdaptedM S h := fun t =>
    (hπa t).add (((hxa t).sub (lag_adaptedM S hxa xm1 t)).const_mul φ)
  have hdb : ∀ t, ∀ᵐ ω ∂S.μ, |d t ω| ≤ Mx + Mx0 := fun t => by
    filter_upwards [hMx t, hMx0 t] with ω a b
    exact (abs_sub _ _).trans (add_le_add a b)
  have heb : ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ Mπ + Mπ0 := fun t => by
    filter_upwards [hMπ t, hMπ0 t] with ω a b
    exact (abs_sub _ _).trans (add_le_add a b)
  have hASd : ∀ t, ∀ᵐ ω ∂S.μ, e t ω = c.κ * d t ω + c.β * S.E t (e (t + 1)) ω := by
    intro t
    filter_upwards [hAS t, hAS0 t, S.E_sub (hπi (t + 1)) (hπ0i (t + 1)) t] with ω a b c'
    have : S.E t (e (t + 1)) ω = S.E t (π (t + 1)) ω - S.E t (π0 (t + 1)) ω := c'
    rw [this]
    simp only [he, hd]
    linear_combination a - b
  have hlagd : ∀ t ω, lag 0 d t ω = lag xm1 x t ω - lag xm1 x0 t ω := by
    intro t ω
    cases t with
    | zero => simp [lag]
    | succ t => rfl
  have hcrd : ∀ t, ∀ᵐ ω ∂S.μ, e t ω + φ * (d t ω - lag 0 d t ω) = h t ω := by
    intro t
    filter_upwards [hcr0 t] with ω a
    rw [hlagd]
    simp only [he, hd, hh]
    linear_combination -a
  have hdB := d_bound hβ0 hβ1 hκ hφ hG hda hea hha hdb heb hg hASd hcrd
  have hlB : ∀ t, ∀ᵐ ω ∂S.μ, |lag 0 d t ω| ≤ K * G := by
    intro t
    cases t with
    | zero => exact ae_of_all _ fun ω => by simpa [lag] using mul_nonneg hK0 hG
    | succ t =>
      filter_upwards [hdB t] with ω a
      exact a.trans (le_of_eq (by rw [hK]; ring))
  have heB : ∀ t, ∀ᵐ ω ∂S.μ, |e t ω| ≤ (1 + 2 * φ * K) * G := by
    intro t
    filter_upwards [hcrd t, hg t, hdB t, hlB t] with ω a b c' d'
    have hd' : |d t ω| ≤ K * G := c'.trans (le_of_eq (by rw [hK]; ring))
    have : e t ω = h t ω - φ * (d t ω - lag 0 d t ω) := by linarith
    rw [this]
    calc |h t ω - φ * (d t ω - lag 0 d t ω)|
        ≤ |h t ω| + φ * (|d t ω| + |lag 0 d t ω|) := by
          refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_pos hφ]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hφ.le
      _ ≤ G + φ * (K * G + K * G) := by
          gcongr
      _ = (1 + 2 * φ * K) * G := by ring
  intro t
  filter_upwards [hdB t, heB t, S.abs_E_le (heB (t + 1)) t, S.abs_E_le (hdB (t + 1)) t,
    hIS t, S.E_sub (hπi (t + 1)) (hπ0i (t + 1)) t, S.E_sub (hxi (t + 1)) (hx0i (t + 1)) t]
    with ω a b c' d' e' f' g'
  have ha' : |d t ω| ≤ K * G := a.trans (le_of_eq (by rw [hK]; ring))
  refine ⟨ha', b, ?_⟩
  have hEe : S.E t (e (t + 1)) ω = S.E t (π (t + 1)) ω - S.E t (π0 (t + 1)) ω := f'
  have hEd : S.E t (d (t + 1)) ω = S.E t (x (t + 1)) ω - S.E t (x0 (t + 1)) ω := g'
  have hσ0 : c.σ ≠ 0 := hσ.ne'
  have hi : i t ω = S.E t (π (t + 1)) ω + rn t ω + c.σ⁻¹ * (S.E t (x (t + 1)) ω - x t ω) := by
    field_simp
    linarith
  have hdiff : i t ω - i0M S c rn π0 x0 t ω =
      S.E t (e (t + 1)) ω + c.σ⁻¹ * (S.E t (d (t + 1)) ω - d t ω) := by
    rw [hi, hEe, hEd]
    simp only [i0M, hd]
    ring
  rw [hdiff]
  have hs : 0 ≤ c.σ⁻¹ := inv_nonneg.mpr hσ.le
  have c'' : |S.E t (d (t + 1)) ω| ≤ K * G := d'.trans (le_of_eq (by rw [hK]; ring))
  calc |S.E t (e (t + 1)) ω + c.σ⁻¹ * (S.E t (d (t + 1)) ω - d t ω)|
      ≤ |S.E t (e (t + 1)) ω| + c.σ⁻¹ * (|S.E t (d (t + 1)) ω| + |d t ω|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg hs]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) hs
    _ ≤ (1 + 2 * φ * K) * G + c.σ⁻¹ * (K * G + K * G) := by gcongr
    _ = (1 + 2 * φ * K + 2 * c.σ⁻¹ * K) * G := by ring

/-- Woodford (2003), p. 591 (tool), with a.s. bounds: **a self-improving bound closes.** If
`|f| ≤ G₀` a.s. and every a.s. bound `G ≥ 0` gives the a.s. bound `A + qG` (`0 ≤ q < 1`,
`A ≥ 0`), then `|f| ≤ A/(1 − q)` a.s. at every date. -/
theorem affine_boundM {S : MeasExpectationSystem Ω} {f : ℕ → Ω → ℝ} {A q G0 : ℝ} (hA : 0 ≤ A)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (h0 : ∀ t, ∀ᵐ ω ∂S.μ, |f t ω| ≤ G0)
    (hstep : ∀ G, 0 ≤ G → (∀ t, ∀ᵐ ω ∂S.μ, |f t ω| ≤ G) → ∀ t, ∀ᵐ ω ∂S.μ, |f t ω| ≤ A + q * G) :
    ∀ t, ∀ᵐ ω ∂S.μ, |f t ω| ≤ A / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  set B := A / (1 - q) with hB
  have hB0 : 0 ≤ B := div_nonneg hA h1q.le
  have hAB : A + q * B = B := by
    rw [hB]
    field_simp
    ring
  have hk : ∀ k : ℕ, ∀ t, ∀ᵐ ω ∂S.μ, |f t ω| ≤ B + q ^ k * max G0 0 := by
    intro k
    induction k with
    | zero =>
      intro t
      filter_upwards [h0 t] with ω h
      have : G0 ≤ max G0 0 := le_max_left _ _
      simp only [pow_zero, one_mul]
      linarith
    | succ k ih =>
      have hG : 0 ≤ B + q ^ k * max G0 0 :=
        add_nonneg hB0 (mul_nonneg (pow_nonneg hq0 k) (le_max_right _ _))
      intro t
      filter_upwards [hstep _ hG ih t] with ω h
      calc |f t ω| ≤ A + q * (B + q ^ k * max G0 0) := h
        _ = (A + q * B) + q ^ (k + 1) * max G0 0 := by ring
        _ = B + q ^ (k + 1) * max G0 0 := by rw [hAB]
  intro t
  filter_upwards [ae_all_iff.2 fun k => hk k t] with ω h
  have hlim : Tendsto (fun k : ℕ => B + q ^ k * max G0 0) atTop (𝓝 (B + 0 * max G0 0)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim h

/-- **Woodford (2003), p. 591, on a filtered probability space with Mathlib's conditional
expectation: the equilibrium paths converge as `λ_i → 0`.** Let `l_n > 0`, `l_n → 0`, and let
`(πⁿ, xⁿ, iⁿ)` be essentially bounded adapted equilibria of (2.1), (3.1) and the optimal rule
(3.7) with `λ_i = l_n` (same disturbances, same history `x_{−1}, i_{−1}, i_{−2}`). Let `(π⁰, x⁰)`
be any essentially bounded adapted solution of (2.1) and the Chapter 7 criterion (2.5), and `i⁰`
read off (3.1) (`i0M`). Then for every `ε > 0`, eventually, at **every** date,
`|πⁿ_t − π⁰_t|, |xⁿ_t − x⁰_t|, |iⁿ_t − i⁰_t| ≤ ε` almost surely. -/
theorem paths_convergeM (c : Calib) (hc : c.Adm) {l : ℕ → ℝ} (hlpos : ∀ n, 0 < l n)
    (hl : Tendsto l atTop (𝓝 0)) {S : MeasExpectationSystem Ω} {rn u : ℕ → Ω → ℝ}
    (hrb : BndM S rn) (xm1 im1 im2 : ℝ) {π x i : ℕ → ℕ → Ω → ℝ}
    (heq : ∀ n, RuleEqmM S { c with li := l n } rn u xm1 im1 im2 (π n) (x n) (i n))
    (ha : ∀ n, AdaptedM S (π n) ∧ AdaptedM S (x n) ∧ AdaptedM S (i n))
    (hb : ∀ n, BndM S (π n) ∧ BndM S (x n) ∧ BndM S (i n)) {π0 x0 : ℕ → Ω → ℝ}
    (hπ0a : AdaptedM S π0) (hx0a : AdaptedM S x0) (hπ0b : BndM S π0) (hx0b : BndM S x0)
    (hAS0 : ∀ t, ASb S c u π0 x0 t) (hcr0 : Crit25M S c xm1 π0 x0) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t, ∀ᵐ ω ∂S.μ, |π n t ω - π0 t ω| ≤ ε ∧
      |x n t ω - x0 t ω| ≤ ε ∧ |i n t ω - i0M S c rn π0 x0 t ω| ≤ ε := by
  intro ε hε
  have hcn : ∀ n, ({ c with li := l n } : Calib).Adm := fun n =>
    ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hlpos n⟩
  obtain ⟨-, -, hL2, -, -⟩ := IRuleForwardIntegrated.L_props c hc
  set a := (IRuleForwardIntegrated.L2c c)⁻¹ with ha'
  have ha0 : 0 ≤ a := inv_nonneg.mpr (by linarith)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hL2
  set K1 := (1 + a) / (1 - a) with hK1
  have hK10 : 0 ≤ K1 := div_nonneg (by linarith) (by linarith)
  set φ := c.lx / c.κ with hφdef
  have hφ : 0 < φ := div_pos hc.2.2.2.2.1 hc.2.2.2.1
  have hcφ : 0 < c.κ / φ := div_pos hc.2.2.2.1 hφ
  set K := TidyR5aLambdaILimit.C2 c.β c.κ φ / (1 - QuadraticRoots.lam1 c.β (c.κ / φ)) with hK
  have hK0 : 0 ≤ K := div_nonneg (TidyR5aLambdaILimit.C2_nonneg hc.1 hc.2.1 hc.2.2.2.1 hφ)
    (by linarith [QuadraticRoots.lam1_lt_one hc.1 hcφ])
  set C3 := 1 + 2 * φ * K with hC3
  set C4 := 1 + 2 * φ * K + 2 * c.σ⁻¹ * K with hC4
  have hC30 : 0 ≤ C3 := by positivity
  have hC40 : 0 ≤ C4 := by
    have : 0 ≤ c.σ⁻¹ := inv_nonneg.mpr hc.2.2.1.le
    positivity
  obtain ⟨Mπ0, hMπ0⟩ := hπ0b
  obtain ⟨Mx0, hMx0⟩ := hx0b
  obtain ⟨Mr, hMr⟩ := hrb
  set Ii0 := Mπ0 + Mr + c.σ⁻¹ * (Mx0 + Mx0) with hIi0
  have hi0b : ∀ t, ∀ᵐ ω ∂S.μ, |i0M S c rn π0 x0 t ω| ≤ Ii0 := by
    intro t
    filter_upwards [S.abs_E_le (hMπ0 (t + 1)) t, S.abs_E_le (hMx0 (t + 1)) t, hMx0 t, hMr t]
      with ω h1 h2 h3 h4
    have hs : 0 ≤ c.σ⁻¹ := inv_nonneg.mpr hc.2.2.1.le
    simp only [i0M]
    calc |S.E t (π0 (t + 1)) ω + rn t ω + c.σ⁻¹ * (S.E t (x0 (t + 1)) ω - x0 t ω)|
        ≤ |S.E t (π0 (t + 1)) ω| + |rn t ω| +
          c.σ⁻¹ * (|S.E t (x0 (t + 1)) ω| + |x0 t ω|) := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _)) ?_)
          rw [abs_mul, abs_of_nonneg hs]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hs
      _ ≤ Ii0 := add_le_add (add_le_add h1 h4) (mul_le_mul_of_nonneg_left (add_le_add h2 h3) hs)
  set I0' := max (max Ii0 (|im1| + |im2|)) 0 with hI0'
  have hI0'0 : 0 ≤ I0' := le_max_right _ _
  have hIi0 : Ii0 ≤ I0' := (le_max_left _ _).trans (le_max_left _ _)
  have him : |im1| + |im2| ≤ I0' := (le_max_right _ _).trans (le_max_left _ _)
  set θ : ℕ → ℝ := fun n => IRuleForwardIntegrated.thetaI { c with li := l n } +
    2 * IRuleForwardIntegrated.thetaD { c with li := l n } with hθ
  have hθ0 : ∀ n, 0 ≤ θ n := fun n => by
    obtain ⟨-, -, h1, h2⟩ := IRuleForwardIntegrated.coef313_pos _ (hcn n)
    simp only [hθ]
    positivity
  have hθlim : Tendsto θ atTop (𝓝 0) := by
    have h1 := (IRuleForwardIntegrated.tendsto_thetaI c).comp hl
    have h2 := (IRuleForwardIntegrated.tendsto_thetaD c).comp hl
    have := h1.add (h2.const_mul 2)
    simpa [hθ, Function.comp_def] using this
  set Mbig := max (max K C3) C4 with hMbig
  have hMbig0 : 0 ≤ Mbig := le_max_of_le_right hC40
  have hlim : Tendsto (fun n => 3 * (K1 * θ n * C4)) atTop (𝓝 0) := by
    simpa using ((hθlim.const_mul K1).mul_const C4).const_mul 3
  have hlim2 : Tendsto (fun n => 2 * (K1 * θ n * (3 * I0' + |c.istar|)) * Mbig) atTop (𝓝 0) := by
    simpa using (((hθlim.const_mul K1).mul_const (3 * I0' + |c.istar|)).const_mul 2).mul_const
      Mbig
  have hev1 := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hev2 := hlim2.eventually (gt_mem_nhds hε)
  filter_upwards [hev1, hev2] with n hq hA
  set q := 3 * (K1 * θ n * C4) with hq'
  set A := K1 * θ n * (3 * I0' + |c.istar|) with hA'
  have hq0 : 0 ≤ q := mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hK10 (hθ0 n)) hC40)
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg hK10 (hθ0 n))
    (add_nonneg (mul_nonneg (by norm_num) hI0'0) (abs_nonneg _))
  obtain ⟨hπa, hxa, hia⟩ := ha n
  obtain ⟨⟨Mπ, hMπ⟩, ⟨Mx, hMx⟩, ⟨Mi, hMi⟩⟩ := hb n
  have hAS : ∀ t, ASb S c u (π n) (x n) t := fun t => (heq n t).1
  have hIS : ∀ t, ISb S c rn (π n) (x n) (i n) t := fun t => (heq n t).2.1
  have hR : ∀ t, RuleM S { c with li := l n } xm1 im1 im2 (π n) (x n) (i n) t :=
    fun t => (heq n t).2.2
  -- the self-improving bound on the (2.5) residual
  have hstep : ∀ G, 0 ≤ G → (∀ t, ∀ᵐ ω ∂S.μ,
      |π n t ω + c.lx / c.κ * (x n t ω - lag xm1 (x n) t ω)| ≤ G) →
      ∀ t, ∀ᵐ ω ∂S.μ, |π n t ω + c.lx / c.κ * (x n t ω - lag xm1 (x n) t ω)| ≤ A + q * G := by
    intro G hG hg
    have hsb := step_boundM c hc hπa hxa ⟨Mπ, hMπ⟩ ⟨Mx, hMx⟩ hAS hIS hπ0a hx0a ⟨Mπ0, hMπ0⟩
      ⟨Mx0, hMx0⟩ hAS0 hcr0 hG hg
    have hI : ∀ t, ∀ᵐ ω ∂S.μ, |i n t ω| ≤ I0' + C4 * G := by
      intro t
      filter_upwards [hsb t, hi0b t] with ω h1 h2
      have h1' : |i n t ω - i0M S c rn π0 x0 t ω| ≤ C4 * G := h1.2.2
      have := abs_sub_abs_le_abs_sub (i n t ω) (i0M S c rn π0 x0 t ω)
      linarith
    have hgb := g_bound { c with li := l n } (hcn n) hR hπa hxa hia hMπ hMx hI
      (by positivity) (by linarith [abs_nonneg im2, mul_nonneg hC40 hG])
      (by linarith [abs_nonneg im1, mul_nonneg hC40 hG])
    intro t
    filter_upwards [hgb t] with ω h
    have e : (1 + (IRuleForwardIntegrated.L2c { c with li := l n })⁻¹) /
        (1 - (IRuleForwardIntegrated.L2c { c with li := l n })⁻¹) *
        ((IRuleForwardIntegrated.thetaI { c with li := l n } +
          2 * IRuleForwardIntegrated.thetaD { c with li := l n }) *
          (I0' + C4 * G + (I0' + C4 * G + (I0' + C4 * G) + |({ c with li := l n } :
              Calib).istar|))) =
        A + q * G := by
      have hL : IRuleForwardIntegrated.L2c { c with li := l n } = IRuleForwardIntegrated.L2c c :=
        rfl
      have hs : ({ c with li := l n } : Calib).istar = c.istar := rfl
      rw [hL, hs]
      simp only [hA', hq', hK1, ha', hθ]
      ring
    rw [e] at h
    exact h
  -- an initial bound
  have hG0 : ∀ t, ∀ᵐ ω ∂S.μ, |π n t ω + c.lx / c.κ * (x n t ω - lag xm1 (x n) t ω)| ≤
      Mπ + |φ| * (Mx + max Mx |xm1|) := by
    intro t
    have hl : ∀ᵐ ω ∂S.μ, |lag xm1 (x n) t ω| ≤ max Mx |xm1| := by
      cases t with
      | zero => exact ae_of_all _ fun ω => le_max_right _ _
      | succ t => exact (hMx t).mono fun ω h => h.trans (le_max_left _ _)
    filter_upwards [hMπ t, hMx t, hl] with ω h1 h2 h3
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h2 h3)) (abs_nonneg _)
  have hq1 : q < 1 := by linarith
  have hgfin := affine_boundM hA0 hq0 hq1 hG0 hstep
  have hGn : 0 ≤ A / (1 - q) := div_nonneg hA0 (by linarith)
  have hle : A / (1 - q) ≤ 2 * A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hsb := step_boundM c hc hπa hxa ⟨Mπ, hMπ⟩ ⟨Mx, hMx⟩ hAS hIS hπ0a hx0a ⟨Mπ0, hMπ0⟩
    ⟨Mx0, hMx0⟩ hAS0 hcr0 hGn hgfin
  have hfin : ∀ C, 0 ≤ C → C ≤ Mbig → C * (A / (1 - q)) ≤ ε := by
    intro C hC hCM
    calc C * (A / (1 - q)) ≤ Mbig * (2 * A) := mul_le_mul hCM hle hGn hMbig0
      _ = 2 * A * Mbig := by ring
      _ ≤ ε := hA.le
  intro t
  filter_upwards [hsb t] with ω h
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : |x n t ω - x0 t ω| ≤ K * (A / (1 - q)) := h1
  have h2 : |π n t ω - π0 t ω| ≤ C3 * (A / (1 - q)) := h2
  have h3 : |i n t ω - i0M S c rn π0 x0 t ω| ≤ C4 * (A / (1 - q)) := h3
  refine ⟨h2.trans (hfin _ hC30 ?_), h1.trans (hfin _ hK0 ?_), h3.trans (hfin _ hC40 ?_)⟩
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

end Woodford.OptimalPolicyRules.TidyR5aLambdaILimitMeasure
