/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.IRuleForwardIntegrated
import OptimalPolicyRules.InflTargetInertia

/-!
# The equilibrium paths converge as `λ_i → 0`

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, p. 591: "in the limit as `λ_i`
approaches zero, the optimal target criterion (2.5) derived in Chapter 7 is recovered".
`IRuleForwardIntegrated` proves the coefficient limits (`tendsto_thetaI`, `tendsto_thetaD`), the
limiting criterion (`IRuleForwardIntegrated.crit_limit_iff_25`) and that a fixed plan satisfying
(3.13) along `λ_i → 0` satisfies (2.5). Here the **equilibrium paths themselves** converge,
uniformly over dates and states.

## The argument

Let `(π^n, x^n, i^n)` be the bounded equilibrium of (2.1), (3.1) and the optimal rule (3.7) for
`λ_i = l_n → 0` (`IRuleBasic.rule_determinate`), all with the same disturbances and history, and
let `(π⁰, x⁰)` be the equilibrium of (2.1) and (2.5) (`InflTargetInertia.ruleEq_existsUnique`),
with `i⁰` read off the IS relation (3.1).

* `crit_residual`: by Proposition 8.6 (`IRuleForwardIntegrated.rule_iff_crit313`) the criterion
  (3.13) holds, and it says that the (2.5) residual `g_t = π_t + (λ_x/κ)(x_t − x_{t−1})` has
  `(1 − λ₂⁻¹)∑λ₂^{−j}E_tg_{t+j} = −r_t`, `r_t = θ_i(i_{t−1} − i*) + θ_Δ(i_{t−1} − i_{t−2})`;
  hence `|g| ≤ (1 + λ₂⁻¹)/(1 − λ₂⁻¹)·sup|r|` (`abs_g_le`).
* `diff_bound`: (2.1) with (2.5)-residual `g` is the workhorse with forcing
  `φ⁻¹(βE_tg_{t+1} − g_t)`, so the distance to the (2.5) equilibrium is at most a constant
  times `sup|g|` (`InflTargetInertia.secondOrder_existsUnique`).
* `affine_bound`: since `|i^n|` is bounded by `sup|i⁰|` plus a constant times `sup|g^n|`, the bound
  is self-improving, and for small `θ_i + 2θ_Δ` it closes: `sup|g^n| ≤ 2K_n(…)`, `K_n → 0`.

## Main results

* **`paths_converge`**: for every `ε > 0`, eventually `|π^n_t − π⁰_t|, |x^n_t − x⁰_t|,
  |i^n_t − i⁰_t| ≤ ε` at **every** date and state.
* `limit_eqm`: `(π⁰, x⁰, i⁰)` is a bounded adapted solution of (2.1), (3.1) and (2.5), and every
  bounded adapted solution of (2.1) and (2.5) has these `π, x`.
* `paths_converge_exists`: the equilibria exist (and are unique) for every `l_n > 0`, so the
  convergence statement is not vacuous.
-/

namespace Woodford.OptimalPolicyRules.TidyR5aLambdaILimit

open Filter Topology
open IRuleBasic (Calib RuleEqm lag lag_known)
open IRuleForwardIntegrated (L1c L2c thetaI thetaD thetaX phiX313 Crit313 Fz Fz_eq L_props
  coef313_pos thetaI_eq forwardSeries_lin forwardSeries_diff rule_iff_crit313 tendsto_thetaI
  tendsto_thetaD)
open InflTargetInertia (lagW lagW_succ lagW_zero SecondOrder ysol wsol backRec
  secondOrder_existsUnique backRec_bounded)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Tools -/

/-- Woodford (2003), survey §4.3 (tool): the explicit bound `|∑ aᵏ E_t u_{t+k}| ≤ M/(1 − a)`
(restated from the proof of `ExpectationSystem.forwardSeries_bounded`). -/
theorem abs_forwardSeries_le {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |𝔼.forwardSeries a u t ω| ≤ M / (1 - a) := by
  have hs := 𝔼.forwardSeries_summable ha0 ha1 hu t ω
  have hg : Summable (fun k : ℕ => M * a ^ k) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_left M
  have hval : ∑' k : ℕ, M * a ^ k = M / (1 - a) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, div_eq_mul_inv]
  have hb : ∀ k, |a ^ k * 𝔼.E t (u (t + k)) ω| ≤ M * a ^ k := fun k => by
    rw [abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg ha0 k)
  have hlo : ∀ k, -(M * a ^ k) ≤ a ^ k * 𝔼.E t (u (t + k)) ω := fun k => by
    have := neg_abs_le (a ^ k * 𝔼.E t (u (t + k)) ω)
    linarith [hb k]
  change |∑' k, a ^ k * 𝔼.E t (u (t + k)) ω| ≤ _
  rw [abs_le, ← hval]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum hlo hg.neg hs
  · exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hb k)) hs hg

omit 𝔼 in
/-- Woodford (2003), p. 591 (tool): **a self-improving bound closes.** If `|f| ≤ G₀` and every
bound `G ≥ 0` on `|f|` gives the bound `A + qG` (`0 ≤ q < 1`, `A ≥ 0`), then `|f| ≤ A/(1 − q)`. -/
theorem affine_bound {f : ℕ → Ω → ℝ} {A q G0 : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h0 : ∀ t ω, |f t ω| ≤ G0)
    (hstep : ∀ G, 0 ≤ G → (∀ t ω, |f t ω| ≤ G) → ∀ t ω, |f t ω| ≤ A + q * G) :
    ∀ t ω, |f t ω| ≤ A / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  set B := A / (1 - q) with hB
  have hB0 : 0 ≤ B := div_nonneg hA h1q.le
  have hAB : A + q * B = B := by
    rw [hB]
    field_simp
    ring
  have hk : ∀ k : ℕ, ∀ t ω, |f t ω| ≤ B + q ^ k * max G0 0 := by
    intro k
    induction k with
    | zero =>
      intro t ω
      have := h0 t ω
      have : G0 ≤ max G0 0 := le_max_left _ _
      simp only [pow_zero, one_mul]
      linarith
    | succ k ih =>
      have hG : 0 ≤ B + q ^ k * max G0 0 :=
        add_nonneg hB0 (mul_nonneg (pow_nonneg hq0 k) (le_max_right _ _))
      intro t ω
      have := hstep _ hG ih t ω
      calc |f t ω| ≤ A + q * (B + q ^ k * max G0 0) := this
        _ = (A + q * B) + q ^ (k + 1) * max G0 0 := by ring
        _ = B + q ^ (k + 1) * max G0 0 := by rw [hAB]
  intro t ω
  have hlim : Tendsto (fun k : ℕ => B + q ^ k * max G0 0) atTop (𝓝 (B + 0 * max G0 0)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim fun k => hk k t ω

/-! ### The distance to the (2.5) equilibrium -/

/-- Woodford (2003), (2.1) and (2.5): the constant of `diff_bound`,
`μ₁(1 + β)/(φ(1 − βμ₁)(1 − μ₁))`, `μ₁` the stable root of the workhorse with `c = κ/φ`. -/
noncomputable def C2 (β κ φ : ℝ) : ℝ :=
  QuadraticRoots.lam1 β (κ / φ) * (φ⁻¹ * (β + 1)) /
    ((1 - β * QuadraticRoots.lam1 β (κ / φ)) * (1 - QuadraticRoots.lam1 β (κ / φ)))

/-- Woodford (2003), (2.1) and (2.5): `C2 ≥ 0`. -/
theorem C2_nonneg {β κ φ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ) :
    0 ≤ C2 β κ φ := by
  have hc : 0 < κ / φ := div_pos hκ hφ
  have hμ0 := QuadraticRoots.lam1_pos hβ0 hc
  have hμ1 := QuadraticRoots.lam1_lt_one hβ0 hc
  obtain ⟨-, hb1⟩ := QuadraticRoots.beta_lam1_mem hβ0 hβ1 hc
  unfold C2
  have : 0 < 1 - β * QuadraticRoots.lam1 β (κ / φ) := by linarith
  have : 0 < 1 - QuadraticRoots.lam1 β (κ / φ) := by linarith
  positivity

/-- **Woodford (2003), (2.1) and (2.5), the Lipschitz bound.** If `d, e` solve the homogeneous
(2.1) `e_t = κd_t + βE_te_{t+1}` with the (2.5) residual `e_t + φ(d_t − d_{t−1}) = h_t`
(`d_{−1} = 0`), `d` bounded adapted and `|h| ≤ G`, then `|d| ≤ C2·G`. -/
theorem diff_bound {β κ φ G : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    (hG : 0 ≤ G) {d e h : ℕ → Ω → ℝ} (hda : 𝔼.Adapted d) (hdb : BoundedProc d)
    (hha : 𝔼.Adapted h) (hh : ∀ t ω, |h t ω| ≤ G)
    (hAS : ∀ t ω, e t ω = κ * d t ω + β * 𝔼.E t (e (t + 1)) ω)
    (hcr : ∀ t ω, e t ω + φ * (d t ω - lagW (fun _ => 0) d t ω) = h t ω) :
    ∀ t ω, |d t ω| ≤ C2 β κ φ * G := by
  have hc : 0 < κ / φ := div_pos hκ hφ
  set μ := QuadraticRoots.lam1 β (κ / φ) with hμ
  have hμ0 : 0 < μ := QuadraticRoots.lam1_pos hβ0 hc
  have hμ1 : μ < 1 := QuadraticRoots.lam1_lt_one hβ0 hc
  obtain ⟨ha0, ha1⟩ := QuadraticRoots.beta_lam1_mem hβ0 hβ1 hc
  rw [← hμ] at ha0 ha1
  set f : ℕ → Ω → ℝ := fun t ω => φ⁻¹ * (β * 𝔼.E t (h (t + 1)) ω - h t ω) with hf
  have hfb : ∀ t ω, |f t ω| ≤ φ⁻¹ * (β + 1) * G := by
    intro t ω
    simp only [hf]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hφ), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hφ).le
    have h1 := 𝔼.abs_E_le (hh (t + 1)) t ω
    calc |β * 𝔼.E t (h (t + 1)) ω - h t ω| ≤ |β * 𝔼.E t (h (t + 1)) ω| + |h t ω| :=
          abs_sub _ _
      _ ≤ β * G + G := by
          rw [abs_mul, abs_of_pos hβ0]
          exact add_le_add (mul_le_mul_of_nonneg_left h1 hβ0.le) (hh t ω)
      _ = (β + 1) * G := by ring
  have hfa : 𝔼.Adapted f := by
    intro t
    have e1 : f t = φ⁻¹ • (β • 𝔼.E t (h (t + 1)) - h t) := by
      funext ω
      simp [hf]
    rw [e1, map_smul, map_sub, map_smul, 𝔼.tower le_rfl, hha t]
  -- the workhorse for `d`
  have hEe : ∀ t ω, 𝔼.E t (e (t + 1)) ω =
      𝔼.E t (h (t + 1)) ω - φ * (𝔼.E t (d (t + 1)) ω - d t ω) := by
    intro t ω
    have he : e (t + 1) = h (t + 1) - φ • (d (t + 1) - d t) := by
      funext ω'
      have := hcr (t + 1) ω'
      simp only [lagW_succ] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    rw [he, map_sub, map_smul, map_sub, hda t]
    rfl
  have hSO : SecondOrder 𝔼 β (κ / φ) (fun _ => 0) f d := by
    intro t ω
    have h1 := hAS t ω
    have h2 := hcr t ω
    rw [hEe t ω] at h1
    have key : β * φ * 𝔼.E t (d (t + 1)) ω - (φ + β * φ + κ) * d t ω +
        φ * lagW (fun _ => 0) d t ω = β * 𝔼.E t (h (t + 1)) ω - h t ω := by
      linear_combination h1 - h2
    simp only [hf]
    rw [← key]
    field_simp
  obtain ⟨-, huniq⟩ := secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hfb hfa (y₀ := fun _ => 0)
    (Y := 0) (fun _ => by simp) (𝔼.const 0 0)
  have hd := huniq d hSO hda hdb
  have hW : ∀ t ω, |wsol 𝔼 β (κ / φ) f t ω| ≤ μ * (φ⁻¹ * (β + 1) * G) / (1 - β * μ) := by
    intro t ω
    refine abs_forwardSeries_le 𝔼 ha0 ha1 (fun t ω => ?_) t ω
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg,
      abs_of_pos (show (0 : ℝ) < QuadraticRoots.lam1 β (κ / φ) from hμ0)]
    exact mul_le_mul_of_nonneg_left (hfb t ω) hμ0.le
  have hbr := backRec_bounded hμ0.le hμ1 (y₀ := fun _ => 0) (Y := 0) (fun _ => by simp) hW
  intro t ω
  rw [hd]
  refine (hbr t ω).trans (le_of_eq ?_)
  have hnn : 0 ≤ μ * (φ⁻¹ * (β + 1) * G) / (1 - β * μ) / (1 - μ) := by
    have : 0 < 1 - β * μ := by linarith
    have : 0 < 1 - μ := by linarith
    positivity
  rw [max_eq_right hnn, C2, ← hμ]
  field_simp

/-! ### The residual of (2.5) under the criterion (3.13) -/

/-- Woodford (2003), (3.13), p. 589: the right-hand side terms
`r_t = θ_i(i_{t−1} − i*) + θ_Δ(i_{t−1} − i_{t−2})`. -/
noncomputable def resid (c : Calib) (im1 im2 : ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  thetaI c * (lag im1 i t ω - c.istar) + thetaD c * (lag im1 i t ω - lag im2 (lag im1 i) t ω)

/-- Woodford (2003), (2.5), p. 561: the residual `π_t + (λ_x/κ)(x_t − x_{t−1})` of the Chapter 7
criterion. -/
noncomputable def gres (c : Calib) (xm1 : ℝ) (π x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (1 : ℝ) • π t + (c.lx / c.κ) • (fun s => x s - lag xm1 x s) t

/-- **Woodford (2003), (3.13), p. 589, as a statement about the (2.5) residual.** For bounded
adapted `π, x`, the criterion (3.13) at date `t` says
`(1 − λ₂⁻¹) ∑ λ₂^{−j} E_t g_{t+j} = −r_t` for the residual `g` of (2.5). -/
theorem crit_residual (c : Calib) (hc : c.Adm) {π x i : ℕ → Ω → ℝ} {xm1 im1 im2 : ℝ}
    (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x) {t : ℕ}
    (h : Crit313 𝔼 c xm1 im1 im2 π x i t) (ω : Ω) :
    (1 - (L2c c)⁻¹) * 𝔼.forwardSeries (L2c c)⁻¹ (gres c xm1 π x) t ω = -resid c im1 im2 i t ω := by
  obtain ⟨-, -, hL2, -, -⟩ := L_props c hc
  have hκ := hc.2.2.2.1
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  have ha0 : 0 ≤ (L2c c)⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : (L2c c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hL2
  have hlb : ∀ t ω, |lag xm1 x t ω| ≤ max Mx |xm1| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hMx t ω).trans (le_max_left _ _)
  have hdx : ∀ t ω, |x t ω - lag xm1 x t ω| ≤ Mx + max Mx |xm1| := fun t ω =>
    (abs_sub _ _).trans (add_le_add (hMx t ω) (hlb t ω))
  have e1 : 𝔼.forwardSeries (L2c c)⁻¹ (gres c xm1 π x) t ω =
      1 * 𝔼.forwardSeries (L2c c)⁻¹ π t ω +
        c.lx / c.κ * 𝔼.forwardSeries (L2c c)⁻¹ (fun s => x s - lag xm1 x s) t ω :=
    forwardSeries_lin 𝔼 (g := fun s => x s - lag xm1 x s) ha0 ha1 hMπ hdx _ _ t ω
  rw [forwardSeries_diff 𝔼 ha0 ha1 hMx hxa] at e1
  have hc1 := congrFun h ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hc1
  rw [Fz_eq, Fz_eq] at hc1
  have e2 : phiX313 c / 4 = (1 - (L2c c)⁻¹) * (c.lx / c.κ) := by
    unfold phiX313; field_simp
  have e3 : thetaX c / 4 = (1 - (L2c c)⁻¹) * (c.lx / c.κ) := by
    unfold thetaX; field_simp
  rw [e2, e3] at hc1
  rw [e1, resid]
  linear_combination hc1

/-- Woodford (2003), (3.13) and (2.5): **the (2.5) residual is bounded by the right-hand side of
(3.13)**: `|g_t| ≤ (1 + λ₂⁻¹)/(1 − λ₂⁻¹)·R` when `|r| ≤ R`. -/
theorem abs_g_le (c : Calib) (hc : c.Adm) {π x i : ℕ → Ω → ℝ} {xm1 im1 im2 R : ℝ}
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (h : ∀ t, Crit313 𝔼 c xm1 im1 im2 π x i t) (hR : ∀ t ω, |resid c im1 im2 i t ω| ≤ R) :
    ∀ t ω, |gres c xm1 π x t ω| ≤ (1 + (L2c c)⁻¹) / (1 - (L2c c)⁻¹) * R := by
  obtain ⟨-, -, hL2, -, -⟩ := L_props c hc
  set a := (L2c c)⁻¹ with ha
  have ha0 : 0 ≤ a := inv_nonneg.mpr (by linarith)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hL2
  have h1a : 0 < 1 - a := by linarith
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  have hgb : ∀ t ω, |gres c xm1 π x t ω| ≤ Mπ + |c.lx / c.κ| * (Mx + max Mx |xm1|) := by
    intro t ω
    have hlb : |lag xm1 x t ω| ≤ max Mx |xm1| := by
      cases t with
      | zero => exact le_max_right _ _
      | succ t => exact (hMx t ω).trans (le_max_left _ _)
    simp only [gres, one_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hMπ t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMx t ω) hlb))
      (abs_nonneg _)
  have hga : 𝔼.Adapted (gres c xm1 π x) := by
    intro t
    simp only [gres, one_smul, map_add, map_smul, map_sub, hπa t, hxa t, lag_known 𝔼 xm1 hxa t]
  have hS : ∀ t ω, 𝔼.forwardSeries a (gres c xm1 π x) t ω = -resid c im1 im2 i t ω / (1 - a) := by
    intro t ω
    have := crit_residual 𝔼 c hc hxa ⟨Mπ, hMπ⟩ ⟨Mx, hMx⟩ (h t) ω
    rw [← ha] at this
    field_simp
    linarith
  have hsol := 𝔼.forwardSeries_solves ha0 ha1 hgb hga
  intro t ω
  have e := congrFun (hsol t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
  have hEt : 𝔼.E t (𝔼.forwardSeries a (gres c xm1 π x) (t + 1)) =
      𝔼.E t (fun ω' => -resid c im1 im2 i (t + 1) ω' / (1 - a)) := by
    congr 1
    funext ω'
    exact hS (t + 1) ω'
  have hEb : |𝔼.E t (fun ω' => -resid c im1 im2 i (t + 1) ω' / (1 - a)) ω| ≤ R / (1 - a) :=
    𝔼.abs_E_le (fun ω' => by rw [abs_div, abs_neg, abs_of_pos h1a]; exact
      div_le_div_of_nonneg_right (hR (t + 1) ω') h1a.le) t ω
  have hg : gres c xm1 π x t ω = -resid c im1 im2 i t ω / (1 - a) -
      a * 𝔼.E t (fun ω' => -resid c im1 im2 i (t + 1) ω' / (1 - a)) ω := by
    rw [← hEt, ← hS t ω]
    linarith
  rw [hg]
  have hr : |-resid c im1 im2 i t ω / (1 - a)| ≤ R / (1 - a) := by
    rw [abs_div, abs_neg, abs_of_pos h1a]
    exact div_le_div_of_nonneg_right (hR t ω) h1a.le
  calc |-resid c im1 im2 i t ω / (1 - a) -
        a * 𝔼.E t (fun ω' => -resid c im1 im2 i (t + 1) ω' / (1 - a)) ω|
      ≤ |-resid c im1 im2 i t ω / (1 - a)| +
          |a * 𝔼.E t (fun ω' => -resid c im1 im2 i (t + 1) ω' / (1 - a)) ω| := abs_sub _ _
    _ ≤ R / (1 - a) + a * (R / (1 - a)) := by
        rw [abs_mul, abs_of_nonneg ha0]
        exact add_le_add hr (mul_le_mul_of_nonneg_left hEb ha0)
    _ = (1 + a) / (1 - a) * R := by field_simp

/-- Woodford (2003), (3.13) (tool): `|r_t| ≤ (θ_i + 2θ_Δ)(I + H)` when `|i| ≤ I`,
`H = |i_{−1}| + |i_{−2}| + |i*|`. -/
theorem abs_resid_le (c : Calib) (hc : c.Adm) {im1 im2 I : ℝ} {i : ℕ → Ω → ℝ}
    (hI : ∀ t ω, |i t ω| ≤ I) (hI0 : 0 ≤ I) (t : ℕ) (ω : Ω) :
    |resid c im1 im2 i t ω| ≤ (thetaI c + 2 * thetaD c) * (I + (|im1| + |im2| + |c.istar|)) := by
  obtain ⟨-, -, hθI, hθD⟩ := coef313_pos c hc
  have hl1 : |lag im1 i t ω| ≤ I + (|im1| + |im2| + |c.istar|) := by
    cases t with
    | zero =>
      change |im1| ≤ _
      linarith [abs_nonneg im2, abs_nonneg c.istar]
    | succ t =>
      have := hI t ω
      change |i t ω| ≤ _
      linarith [abs_nonneg im1, abs_nonneg im2, abs_nonneg c.istar]
  have hl2 : |lag im2 (lag im1 i) t ω| ≤ I + (|im1| + |im2| + |c.istar|) := by
    cases t with
    | zero =>
      change |im2| ≤ _
      linarith [abs_nonneg im1, abs_nonneg c.istar]
    | succ t =>
      change |lag im1 i t ω| ≤ _
      cases t with
      | zero =>
        change |im1| ≤ _
        linarith [abs_nonneg im2, abs_nonneg c.istar]
      | succ t =>
        have := hI t ω
        change |i t ω| ≤ _
        linarith [abs_nonneg im1, abs_nonneg im2, abs_nonneg c.istar]
  set H := |im1| + |im2| + |c.istar|
  have h1 : |lag im1 i t ω - c.istar| ≤ I + H := by
    have := abs_sub (lag im1 i t ω) c.istar
    have : |lag im1 i t ω| ≤ I + H - |c.istar| := by
      cases t with
      | zero =>
        change |im1| ≤ _
        simp only [H]
        linarith [abs_nonneg im2]
      | succ t =>
        have := hI t ω
        change |i t ω| ≤ _
        simp only [H]
        linarith [abs_nonneg im1, abs_nonneg im2]
    linarith
  have h2 : |lag im1 i t ω - lag im2 (lag im1 i) t ω| ≤ 2 * (I + H) := by
    have := abs_sub (lag im1 i t ω) (lag im2 (lag im1 i) t ω)
    linarith
  unfold resid
  calc |thetaI c * (lag im1 i t ω - c.istar) +
        thetaD c * (lag im1 i t ω - lag im2 (lag im1 i) t ω)|
      ≤ |thetaI c * (lag im1 i t ω - c.istar)| +
          |thetaD c * (lag im1 i t ω - lag im2 (lag im1 i) t ω)| := abs_add_le _ _
    _ ≤ thetaI c * (I + H) + thetaD c * (2 * (I + H)) := by
        rw [abs_mul, abs_mul, abs_of_pos hθI, abs_of_pos hθD]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 hθI.le)
          (mul_le_mul_of_nonneg_left h2 hθD.le)
    _ = (thetaI c + 2 * thetaD c) * (I + H) := by ring

/-! ### The limit equilibrium `λ_i = 0` -/

omit 𝔼 in
/-- Woodford (2003), p. 561 (tool): the lag with a constant initial value is `IRuleBasic.lag`. -/
theorem lagW_const (z0 : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : lagW (fun _ => z0) x t = lag z0 x t := by
  cases t <;> rfl

/-- Woodford (2003), (2.5), p. 561: the limit equilibrium inflation, the equilibrium of (2.1)
under the Chapter 7 criterion with `φ = λ_x/κ` and `x_{−1} = x_{−1}`. -/
noncomputable def pi0 (c : Calib) (xm1 : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  InflTargetInertia.inflR 𝔼 c.β c.κ (c.lx / c.κ) (fun _ => xm1) u

/-- Woodford (2003), (2.5), p. 561: the limit equilibrium output gap. -/
noncomputable def x0 (c : Calib) (xm1 : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  InflTargetInertia.gapR 𝔼 c.β c.κ (c.lx / c.κ) (fun _ => xm1) u

/-- Woodford (2003), (3.1), p. 583: the limit interest rate read off the IS relation,
`i_t = E_tπ_{t+1} + rⁿ_t + σ⁻¹(E_tx_{t+1} − x_t)`. -/
noncomputable def i0 (c : Calib) (xm1 : ℝ) (rn u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => 𝔼.E t (pi0 𝔼 c xm1 u (t + 1)) ω + rn t ω +
    c.σ⁻¹ * (𝔼.E t (x0 𝔼 c xm1 u (t + 1)) ω - x0 𝔼 c xm1 u t ω)

/-- Woodford (2003), (3.1) (tool): the IS relation solved for the interest rate. -/
theorem i_of_IS (c : Calib) (hσ : c.σ ≠ 0) {rn π x i : ℕ → Ω → ℝ} {t : ℕ}
    (h : IRuleBasic.IS 𝔼 c rn π x i t) (ω : Ω) :
    i t ω = 𝔼.E t (π (t + 1)) ω + rn t ω + c.σ⁻¹ * (𝔼.E t (x (t + 1)) ω - x t ω) := by
  have := congrFun h ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  field_simp
  linarith

/-- **Woodford (2003), (2.1), (2.5) and (3.1): the limit equilibrium.** `(π⁰, x⁰, i⁰)` is bounded
and adapted and satisfies (2.1), (3.1) and the Chapter 7 criterion (2.5) at every date; every
bounded adapted solution of (2.1) and (2.5) has inflation `π⁰` and output gap `x⁰`. -/
theorem limit_eqm (c : Calib) (hc : c.Adm) {rn u : ℕ → Ω → ℝ} (hrb : BoundedProc rn)
    (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u) (xm1 : ℝ) :
    ((∀ t, IRuleBasic.AS 𝔼 c u (pi0 𝔼 c xm1 u) (x0 𝔼 c xm1 u) t ∧
        IRuleBasic.IS 𝔼 c rn (pi0 𝔼 c xm1 u) (x0 𝔼 c xm1 u) (i0 𝔼 c xm1 rn u) t ∧
        pi0 𝔼 c xm1 u t + (c.lx / c.κ) • (x0 𝔼 c xm1 u t - lag xm1 (x0 𝔼 c xm1 u) t) = 0) ∧
      (𝔼.Adapted (pi0 𝔼 c xm1 u) ∧ 𝔼.Adapted (x0 𝔼 c xm1 u) ∧ 𝔼.Adapted (i0 𝔼 c xm1 rn u)) ∧
      (BoundedProc (pi0 𝔼 c xm1 u) ∧ BoundedProc (x0 𝔼 c xm1 u) ∧
        BoundedProc (i0 𝔼 c xm1 rn u))) ∧
    ∀ π x, 𝔼.Adapted π → 𝔼.Adapted x → BoundedProc π → BoundedProc x →
      (∀ t, IRuleBasic.AS 𝔼 c u π x t) →
      (∀ t, π t + (c.lx / c.κ) • (x t - lag xm1 x t) = 0) →
        π = pi0 𝔼 c xm1 u ∧ x = x0 𝔼 c xm1 u := by
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, -⟩ := hc
  have hφ : 0 < c.lx / c.κ := div_pos hlx hκ
  obtain ⟨Mu, hMu⟩ := hub
  obtain ⟨Mr, hMr⟩ := hrb
  obtain ⟨⟨⟨hAS, hπa, hxa, hπb, hxb⟩, hcr⟩, huniq⟩ := InflTargetInertia.ruleEq_existsUnique 𝔼
    hβ0 hβ1 hκ hφ hMu hua (x₀ := fun _ => xm1) (B := |xm1|) (fun _ => le_rfl) (𝔼.const 0 xm1)
  have hASf : ∀ t, IRuleBasic.AS 𝔼 c u (pi0 𝔼 c xm1 u) (x0 𝔼 c xm1 u) t := by
    intro t
    funext ω
    have := hAS t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact this
  obtain ⟨Bπ, hBπ⟩ := hπb
  obtain ⟨Bx, hBx⟩ := hxb
  have hBπ' : ∀ t ω, |pi0 𝔼 c xm1 u t ω| ≤ Bπ := hBπ
  have hBx' : ∀ t ω, |x0 𝔼 c xm1 u t ω| ≤ Bx := hBx
  have hxa' : ∀ t, 𝔼.E t (x0 𝔼 c xm1 u t) = x0 𝔼 c xm1 u t := hxa
  refine ⟨⟨fun t => ⟨hASf t, ?_, ?_⟩, ⟨hπa, hxa, fun t => ?_⟩,
    ⟨⟨Bπ, hBπ⟩, ⟨Bx, hBx⟩, ⟨Bπ + Mr + c.σ⁻¹ * (Bx + Bx), fun t ω => ?_⟩⟩⟩,
    fun π x hπa' hxa' hπb' hxb' hAS' hcr' => ?_⟩
  · funext ω
    simp only [i0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    have := hcr t ω
    rw [lagW_const] at this
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    exact this
  · have e : i0 𝔼 c xm1 rn u t = 𝔼.E t (pi0 𝔼 c xm1 u (t + 1)) + rn t +
        c.σ⁻¹ • (𝔼.E t (x0 𝔼 c xm1 u (t + 1)) - x0 𝔼 c xm1 u t) := by
      funext ω
      simp [i0]
    rw [e, map_add, map_add, map_smul, map_sub, 𝔼.tower le_rfl, 𝔼.tower le_rfl, hra t, hxa' t]
  · simp only [i0]
    have h1 := 𝔼.abs_E_le (hBπ' (t + 1)) t ω
    have h2 := 𝔼.abs_E_le (hBx' (t + 1)) t ω
    have h3 := hBx' t ω
    have h4 := hMr t ω
    have hs : 0 ≤ c.σ⁻¹ := inv_nonneg.mpr hσ.le
    calc |𝔼.E t (pi0 𝔼 c xm1 u (t + 1)) ω + rn t ω +
          c.σ⁻¹ * (𝔼.E t (x0 𝔼 c xm1 u (t + 1)) ω - x0 𝔼 c xm1 u t ω)|
        ≤ |𝔼.E t (pi0 𝔼 c xm1 u (t + 1)) ω| + |rn t ω| +
          c.σ⁻¹ * (|𝔼.E t (x0 𝔼 c xm1 u (t + 1)) ω| + |x0 𝔼 c xm1 u t ω|) := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _)) ?_)
          rw [abs_mul, abs_of_nonneg hs]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hs
      _ ≤ Bπ + Mr + c.σ⁻¹ * (Bx + Bx) :=
          add_le_add (add_le_add h1 h4) (mul_le_mul_of_nonneg_left (add_le_add h2 h3) hs)
  · have hcr'' : InflTargetInertia.Criterion (c.lx / c.κ) (fun _ => xm1) π x := by
      intro t ω
      have := congrFun (hcr' t) ω
      rw [lagW_const]
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
        using this
    have hplan : InflTargetInertia.Plan 𝔼 c.β c.κ u π x := by
      refine ⟨fun t ω => ?_, hπa', hxa', hπb', hxb'⟩
      have := congrFun (hAS' t) ω
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    exact huniq π x hplan hcr''

/-! ### Convergence of the equilibrium paths -/

/-- Woodford (2003), (2.1), (2.5) and (3.1): **the distance of any bounded plan satisfying (2.1)
and (3.1) to the limit equilibrium is controlled by its (2.5) residual**: if `|g| ≤ G`, then
`|x − x⁰| ≤ C2·G`, `|π − π⁰| ≤ (1 + 2φC2)G` and `|i − i⁰| ≤ (1 + 2φC2 + 2σ⁻¹C2)G`
(`φ = λ_x/κ`). -/
theorem step_bound (c : Calib) (hc : c.Adm) {rn u : ℕ → Ω → ℝ} (hrb : BoundedProc rn)
    (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : ℝ}
    {π x i : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hxb : BoundedProc x) (hAS : ∀ t, IRuleBasic.AS 𝔼 c u π x t)
    (hIS : ∀ t, IRuleBasic.IS 𝔼 c rn π x i t) {G : ℝ} (hG : 0 ≤ G)
    (hg : ∀ t ω, |gres c xm1 π x t ω| ≤ G) :
    ∀ t ω, |x t ω - x0 𝔼 c xm1 u t ω| ≤ C2 c.β c.κ (c.lx / c.κ) * G ∧
      |π t ω - pi0 𝔼 c xm1 u t ω| ≤ (1 + 2 * (c.lx / c.κ) * C2 c.β c.κ (c.lx / c.κ)) * G ∧
      |i t ω - i0 𝔼 c xm1 rn u t ω| ≤
        (1 + 2 * (c.lx / c.κ) * C2 c.β c.κ (c.lx / c.κ) +
          2 * c.σ⁻¹ * C2 c.β c.κ (c.lx / c.κ)) * G := by
  obtain ⟨⟨h0, ⟨hπ0a, hx0a, -⟩, ⟨hπ0b, hx0b, -⟩⟩, -⟩ := limit_eqm 𝔼 c hc hrb hra hub hua xm1
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, -⟩ := hc
  set φ := c.lx / c.κ with hφdef
  have hφ : 0 < φ := div_pos hlx hκ
  set K := C2 c.β c.κ φ with hK
  have hK0 : 0 ≤ K := C2_nonneg hβ0 hβ1 hκ hφ
  set d : ℕ → Ω → ℝ := fun t ω => x t ω - x0 𝔼 c xm1 u t ω with hd
  set e : ℕ → Ω → ℝ := fun t ω => π t ω - pi0 𝔼 c xm1 u t ω with he
  have hda : 𝔼.Adapted d := by
    intro t
    change 𝔼.E t (x t - x0 𝔼 c xm1 u t) = x t - x0 𝔼 c xm1 u t
    rw [map_sub, hxa t, hx0a t]
  have hdb : BoundedProc d := by
    obtain ⟨M1, hM1⟩ := hxb
    obtain ⟨M2, hM2⟩ := hx0b
    exact ⟨M1 + M2, fun t ω => (abs_sub _ _).trans (add_le_add (hM1 t ω) (hM2 t ω))⟩
  have hga : 𝔼.Adapted (gres c xm1 π x) := by
    intro t
    simp only [gres, one_smul, map_add, map_smul, map_sub, hπa t, hxa t, lag_known 𝔼 xm1 hxa t]
  have hASd : ∀ t ω, e t ω = c.κ * d t ω + c.β * 𝔼.E t (e (t + 1)) ω := by
    intro t ω
    have h1 := congrFun (hAS t) ω
    have h2 := congrFun (h0 t).1 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    have hE : 𝔼.E t (e (t + 1)) ω = 𝔼.E t (π (t + 1)) ω - 𝔼.E t (pi0 𝔼 c xm1 u (t + 1)) ω := by
      change 𝔼.E t (π (t + 1) - pi0 𝔼 c xm1 u (t + 1)) ω = _
      rw [map_sub]
      rfl
    rw [hE]
    simp only [he, hd]
    linarith
  have hcrd : ∀ t ω, e t ω + φ * (d t ω - lagW (fun _ => 0) d t ω) = gres c xm1 π x t ω := by
    intro t ω
    have h2 := congrFun (h0 t).2.2 ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2
    have hl : lagW (fun _ => 0) d t ω = lag xm1 x t ω - lag xm1 (x0 𝔼 c xm1 u) t ω := by
      cases t with
      | zero => simp [lag]
      | succ t => rfl
    rw [hl]
    simp only [gres, one_smul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, he, hd,
      ← hφdef]
    linarith
  have hdB := diff_bound 𝔼 hβ0 hβ1 hκ hφ hG hda hdb hga hg hASd hcrd
  have heB : ∀ t ω, |e t ω| ≤ (1 + 2 * φ * K) * G := by
    intro t ω
    have h1 := hcrd t ω
    have hl : |lagW (fun _ => 0) d t ω| ≤ K * G := by
      cases t with
      | zero =>
        simp only [lagW_zero, abs_zero]
        exact mul_nonneg hK0 hG
      | succ t => exact hdB t ω
    have : e t ω = gres c xm1 π x t ω - φ * (d t ω - lagW (fun _ => 0) d t ω) := by linarith
    rw [this]
    calc |gres c xm1 π x t ω - φ * (d t ω - lagW (fun _ => 0) d t ω)|
        ≤ |gres c xm1 π x t ω| + φ * (|d t ω| + |lagW (fun _ => 0) d t ω|) := by
          refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul, abs_of_pos hφ]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hφ.le
      _ ≤ G + φ * (K * G + K * G) := by
          gcongr
          · exact hg t ω
          · exact hdB t ω
      _ = (1 + 2 * φ * K) * G := by ring
  intro t ω
  refine ⟨hdB t ω, heB t ω, ?_⟩
  have hi := i_of_IS 𝔼 c hσ.ne' (hIS t) ω
  have hi0 := i_of_IS 𝔼 c hσ.ne' (h0 t).2.1 ω
  have hEe : 𝔼.E t (π (t + 1)) ω - 𝔼.E t (pi0 𝔼 c xm1 u (t + 1)) ω = 𝔼.E t (e (t + 1)) ω := by
    change _ = 𝔼.E t (π (t + 1) - pi0 𝔼 c xm1 u (t + 1)) ω
    rw [map_sub]
    rfl
  have hEd : 𝔼.E t (x (t + 1)) ω - 𝔼.E t (x0 𝔼 c xm1 u (t + 1)) ω = 𝔼.E t (d (t + 1)) ω := by
    change _ = 𝔼.E t (x (t + 1) - x0 𝔼 c xm1 u (t + 1)) ω
    rw [map_sub]
    rfl
  have hdiff : i t ω - i0 𝔼 c xm1 rn u t ω =
      𝔼.E t (e (t + 1)) ω + c.σ⁻¹ * (𝔼.E t (d (t + 1)) ω - d t ω) := by
    rw [hi, hi0, ← hEe, ← hEd]
    simp only [hd]
    ring
  rw [hdiff]
  have hs : 0 ≤ c.σ⁻¹ := inv_nonneg.mpr hσ.le
  have h1 := 𝔼.abs_E_le (heB (t + 1)) t ω
  have h2 := 𝔼.abs_E_le (hdB (t + 1)) t ω
  have h3 := hdB t ω
  calc |𝔼.E t (e (t + 1)) ω + c.σ⁻¹ * (𝔼.E t (d (t + 1)) ω - d t ω)|
      ≤ |𝔼.E t (e (t + 1)) ω| + c.σ⁻¹ * (|𝔼.E t (d (t + 1)) ω| + |d t ω|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg hs]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) hs
    _ ≤ (1 + 2 * φ * K) * G + c.σ⁻¹ * (K * G + K * G) := by gcongr
    _ = (1 + 2 * φ * K + 2 * c.σ⁻¹ * K) * G := by ring

/-- **Woodford (2003), p. 591: the equilibrium paths converge as `λ_i → 0`.** Let `l_n > 0`,
`l_n → 0`, and let `(πⁿ, xⁿ, iⁿ)` be bounded adapted equilibria of (2.1), (3.1) and the optimal
rule (3.7) with `λ_i = l_n` (same disturbances, same history `x_{−1}, i_{−1}, i_{−2}`). Then for
every `ε > 0`, eventually `|πⁿ_t − π⁰_t| ≤ ε`, `|xⁿ_t − x⁰_t| ≤ ε` and `|iⁿ_t − i⁰_t| ≤ ε` at
**every** date and state, where `(π⁰, x⁰)` is the equilibrium under the Chapter 7 criterion (2.5)
and `i⁰` is read off (3.1) (`limit_eqm`). -/
theorem paths_converge (c : Calib) (hc : c.Adm) {l : ℕ → ℝ} (hlpos : ∀ n, 0 < l n)
    (hl : Tendsto l atTop (𝓝 0)) {rn u : ℕ → Ω → ℝ} (hrb : BoundedProc rn)
    (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u) (xm1 im1 im2 : ℝ)
    {π x i : ℕ → ℕ → Ω → ℝ}
    (heq : ∀ n, RuleEqm 𝔼 { c with li := l n } rn u xm1 im1 im2 (π n) (x n) (i n))
    (ha : ∀ n, 𝔼.Adapted (π n) ∧ 𝔼.Adapted (x n) ∧ 𝔼.Adapted (i n))
    (hb : ∀ n, BoundedProc (π n) ∧ BoundedProc (x n) ∧ BoundedProc (i n)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ω, |π n t ω - pi0 𝔼 c xm1 u t ω| ≤ ε ∧
      |x n t ω - x0 𝔼 c xm1 u t ω| ≤ ε ∧ |i n t ω - i0 𝔼 c xm1 rn u t ω| ≤ ε := by
  intro ε hε
  have hcn : ∀ n, ({ c with li := l n } : Calib).Adm := fun n =>
    ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hlpos n⟩
  obtain ⟨-, -, hL2, -, -⟩ := L_props c hc
  set a := (L2c c)⁻¹ with ha'
  have ha0 : 0 ≤ a := inv_nonneg.mpr (by linarith)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hL2
  set K1 := (1 + a) / (1 - a) with hK1
  have hK10 : 0 ≤ K1 := div_nonneg (by linarith) (by linarith)
  set φ := c.lx / c.κ with hφdef
  have hφ : 0 < φ := div_pos hc.2.2.2.2.1 hc.2.2.2.1
  set K := C2 c.β c.κ φ with hK
  have hK0 : 0 ≤ K := C2_nonneg hc.1 hc.2.1 hc.2.2.2.1 hφ
  set C3 := 1 + 2 * φ * K with hC3
  set C4 := 1 + 2 * φ * K + 2 * c.σ⁻¹ * K with hC4
  have hC30 : 0 ≤ C3 := by positivity
  have hC40 : 0 ≤ C4 := by
    have : 0 ≤ c.σ⁻¹ := inv_nonneg.mpr hc.2.2.1.le
    positivity
  obtain ⟨-, -, ⟨-, -, ⟨I0, hI0⟩⟩⟩ := (limit_eqm 𝔼 c hc hrb hra hub hua xm1).1
  set I0' := max I0 0 with hI0'
  set H := |im1| + |im2| + |c.istar| with hH
  have hH0 : 0 ≤ H := by positivity
  -- the coefficient `θ_i + 2θ_Δ` for `λ_i = l_n`
  set θ : ℕ → ℝ := fun n => thetaI { c with li := l n } + 2 * thetaD { c with li := l n } with hθ
  have hθ0 : ∀ n, 0 ≤ θ n := fun n => by
    obtain ⟨-, -, h1, h2⟩ := coef313_pos _ (hcn n)
    simp only [hθ]
    positivity
  have hθlim : Tendsto θ atTop (𝓝 0) := by
    have h1 := (tendsto_thetaI c).comp hl
    have h2 := (tendsto_thetaD c).comp hl
    have := h1.add (h2.const_mul 2)
    simpa [hθ, Function.comp_def] using this
  set Mbig := max (max K C3) C4 with hMbig
  have hMbig0 : 0 ≤ Mbig := le_max_of_le_right hC40
  have hlim : Tendsto (fun n => K1 * θ n * C4) atTop (𝓝 0) := by
    simpa using (hθlim.const_mul K1).mul_const C4
  have hlim2 : Tendsto (fun n => 2 * (K1 * θ n * (I0' + H)) * Mbig) atTop (𝓝 0) := by
    simpa using (((hθlim.const_mul K1).mul_const (I0' + H)).const_mul 2).mul_const Mbig
  have hev1 := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hev2 := hlim2.eventually (gt_mem_nhds hε)
  filter_upwards [hev1, hev2] with n hq hA
  set q := K1 * θ n * C4 with hq'
  set A := K1 * θ n * (I0' + H) with hA'
  have hq0 : 0 ≤ q := mul_nonneg (mul_nonneg hK10 (hθ0 n)) hC40
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg hK10 (hθ0 n)) (add_nonneg (le_max_right _ _) hH0)
  obtain ⟨hπa, hxa, hia⟩ := ha n
  obtain ⟨hπb, hxb, hib⟩ := hb n
  have hcrit : ∀ t, Crit313 𝔼 { c with li := l n } xm1 im1 im2 (π n) (x n) (i n) t :=
    (rule_iff_crit313 𝔼 _ (hcn n) xm1 im1 im2 hπa hxa hia hπb hxb hib).mp
      fun t => (heq n t).2.2
  have hAS : ∀ t, IRuleBasic.AS 𝔼 c u (π n) (x n) t := fun t => (heq n t).1
  have hIS : ∀ t, IRuleBasic.IS 𝔼 c rn (π n) (x n) (i n) t := fun t => (heq n t).2.1
  -- the self-improving bound on the (2.5) residual
  have hstep : ∀ G, 0 ≤ G → (∀ t ω, |gres c xm1 (π n) (x n) t ω| ≤ G) →
      ∀ t ω, |gres c xm1 (π n) (x n) t ω| ≤ A + q * G := by
    intro G hG hg
    have hsb := step_bound 𝔼 c hc hrb hra hub hua hπa hxa hxb hAS hIS hG hg
    have hI : ∀ t ω, |i n t ω| ≤ I0' + C4 * G := by
      intro t ω
      have h1 := (hsb t ω).2.2
      have h2 := (hI0 t ω).trans (le_max_left I0 0)
      have := abs_sub_abs_le_abs_sub (i n t ω) (i0 𝔼 c xm1 rn u t ω)
      linarith
    have hR := abs_resid_le (c := { c with li := l n }) (im1 := im1) (im2 := im2) (hcn n) hI
      (by positivity)
    have hg' := abs_g_le 𝔼 _ (hcn n) hπa hxa hπb hxb hcrit hR
    intro t ω
    have := hg' t ω
    change |gres c xm1 (π n) (x n) t ω| ≤ _ at this
    have e : (1 + (L2c { c with li := l n })⁻¹) / (1 - (L2c { c with li := l n })⁻¹) *
        ((thetaI { c with li := l n } + 2 * thetaD { c with li := l n }) *
          (I0' + C4 * G + (|im1| + |im2| + |({ c with li := l n } : Calib).istar|))) =
        A + q * G := by
      have hL : L2c { c with li := l n } = L2c c := rfl
      have hs : ({ c with li := l n } : Calib).istar = c.istar := rfl
      rw [hL, hs]
      simp only [hA', hq', hK1, ha', hθ, hH]
      ring
    rw [e] at this
    exact this
  -- an initial bound
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  have hG0 : ∀ t ω, |gres c xm1 (π n) (x n) t ω| ≤ Mπ + |φ| * (Mx + max Mx |xm1|) := by
    intro t ω
    have hlb : |lag xm1 (x n) t ω| ≤ max Mx |xm1| := by
      cases t with
      | zero => exact le_max_right _ _
      | succ t => exact (hMx t ω).trans (le_max_left _ _)
    simp only [gres, one_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hMπ t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMx t ω) hlb))
      (abs_nonneg _)
  have hq1 : q < 1 := by linarith
  have hgfin := affine_bound hA0 hq0 hq1 hG0 hstep
  have hGn : 0 ≤ A / (1 - q) := div_nonneg hA0 (by linarith)
  have hle : A / (1 - q) ≤ 2 * A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hsb := step_bound 𝔼 c hc hrb hra hub hua hπa hxa ⟨Mx, hMx⟩ hAS hIS hGn hgfin
  have hfin : ∀ C, 0 ≤ C → C ≤ Mbig → C * (A / (1 - q)) ≤ ε := by
    intro C hC hCM
    calc C * (A / (1 - q)) ≤ Mbig * (2 * A) := mul_le_mul hCM hle hGn hMbig0
      _ = 2 * A * Mbig := by ring
      _ ≤ ε := hA.le
  intro t ω
  obtain ⟨h1, h2, h3⟩ := hsb t ω
  refine ⟨h2.trans (hfin _ hC30 ?_), h1.trans (hfin _ hK0 ?_), h3.trans (hfin _ hC40 ?_)⟩
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- **Woodford (2003), p. 591, with existence**: for every `l_n > 0`, `l_n → 0`, the equilibria
under the optimal rule exist and are unique (`IRuleBasic.rule_determinate`), and they converge
uniformly to the `λ_i = 0` equilibrium (`paths_converge`). -/
theorem paths_converge_exists (c : Calib) (hc : c.Adm) {l : ℕ → ℝ} (hlpos : ∀ n, 0 < l n)
    (hl : Tendsto l atTop (𝓝 0)) {rn u : ℕ → Ω → ℝ} (hrb : BoundedProc rn)
    (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u) (xm1 im1 im2 : ℝ) :
    ∃ e : ℕ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      (∀ n, RuleEqm 𝔼 { c with li := l n } rn u xm1 im1 im2 (e n).1 (e n).2.1 (e n).2.2 ∧
        (𝔼.Adapted (e n).1 ∧ 𝔼.Adapted (e n).2.1 ∧ 𝔼.Adapted (e n).2.2) ∧
        (BoundedProc (e n).1 ∧ BoundedProc (e n).2.1 ∧ BoundedProc (e n).2.2)) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ω, |(e n).1 t ω - pi0 𝔼 c xm1 u t ω| ≤ ε ∧
        |(e n).2.1 t ω - x0 𝔼 c xm1 u t ω| ≤ ε ∧
        |(e n).2.2 t ω - i0 𝔼 c xm1 rn u t ω| ≤ ε := by
  have hcn : ∀ n, ({ c with li := l n } : Calib).Adm := fun n =>
    ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hlpos n⟩
  have hex := fun n => (IRuleBasic.rule_determinate 𝔼 _ (hcn n) hrb hra hub hua xm1 im1 im2).exists
  choose e he using hex
  exact ⟨e, he, paths_converge 𝔼 c hc hlpos hl hrb hra hub hua xm1 im1 im2
    (fun n => (he n).1) (fun n => (he n).2.1) (fun n => (he n).2.2)⟩

end Woodford.OptimalPolicyRules.TidyR5aLambdaILimit
