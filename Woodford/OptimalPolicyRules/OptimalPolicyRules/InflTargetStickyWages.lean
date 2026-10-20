/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflTargetInertia
import OptimalPolicyRules.ExpectationTools
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Optimal inflation targeting with sticky wages and prices

Woodford (2003), *Interest and Prices*, Chapter 8, §2.2, pp. 565–567.

The supply side is (2.11)–(2.13): price inflation
`π_t = κ_p (x_t + u_t) + ξ_p (w_t − w^n_t) + β E_t π_{t+1}`, wage inflation
`π^w_t = κ_w (x_t + u_t) + ξ_w (w^n_t − w_t) + β E_t π^w_{t+1}` and the real-wage identity
`w_t = w_{t−1} + π^w_t − π_t`; the loss is (2.15)
`λ_p π_t² + λ_w (π^w_t)² + λ_x (x_t − x*)²`.

## Main results

* (2.14), the flexible-wage limit as a genuine limit `ξ_w → ∞`: `wage_gap_bound`,
  `wage_gap_tendsto`, `tendsto_E_of_tendstoUniformly`, `flexible_wage_limit` (the limit of a
  family of bounded solutions satisfies `w − w^n = (ω_w + σ⁻¹)(x + u)` and (2.1) with
  `κ = ξ_p (ω_p + ω_w + σ⁻¹)` and the rescaled cost-push shock `κ u`).
* (2.16)–(2.19): `lagrangian_derivs` (the first-order conditions are the derivatives of the
  Lagrangian), `focSW_excess`, `focSW_sufficient`, `focSW_unique` (Lagrangian sufficiency and
  uniqueness: FOC + feasibility ⇒ minimum of the expected loss among bounded plans with the same
  `π_{t₀}, π^w_{t₀}`).
* Elimination of the multipliers: `foc_q_eq` (`q_t = (κ_w − κ_p) υ_t`), `foc_asym_eq`
  (`π^asym_t + (ξ_p + ξ_w) υ_t + Δ(υ_t − β E_t υ_{t+1}) = 0`), `foc_imp_criterion` (the
  CORRECTED (2.20) `(κ_w − κ_p) π^asym_t + (ξ_p + ξ_w) q_t
  − {E_t[β q_{t+1} − q_t] − E_{t−1}[β q_t − q_{t−1}]} = 0`, survey E14), `q_eq_sym` ((2.21)).
* `printed_criterion_counterexample` (E14): a concrete model instance whose optimal plan
  (feasible, satisfying the first-order conditions, hence optimal by sufficiency) satisfies the
  corrected criterion and violates the printed (2.20).
* `criterionC_timeless` (κ_w ≠ κ_p): every bounded feasible plan satisfying the corrected
  criterion at every date `t > t₀` is optimal from a timeless perspective (the multipliers are
  reconstructed from the criterion, `elim_alg`).
* (2.22) `κ_w = κ_p`: `foc_q_zero` (the optimum has `q_t = 0`), `criterion222_iff_q`,
  `phi_normalized` (fn. 20: `φ = λ_x/κ`), `sym_timeless`, `sym_existsUnique`,
  `sym_robustlyOptimal` (the criterion `π^sym_t + φ (x_t − x_{t−1}) = 0`,
  `φ = λ_x/((λ_p + λ_w) κ)`, is robustly optimal: the real wage is exogenous
  (`wageEq_secondOrder`, `wage_unique`), and with `s = (λ_p π + λ_w π^w)/(λ_p + λ_w)` the
  problem reduces to the baseline one, `sAvg_AS`, `lossSW_split`),
  and `corrected_criterion_kappa_eq` (with `κ_w = κ_p` the corrected (2.20) alone does not force
  `q = 0`: the book's "reduces simply to `q_t = 0`" holds for the printed form, and for the
  optimal plan via `q_t = (κ_w − κ_p) υ_t`).
* `κ_w ≠ κ_p`, DETERMINACY. The first-order conditions reduce to a cubic equation in the operator
  `𝒵 = (1 − βF)(1 − L)` applied to the real wage, `λ_x 𝒵³w + p₂ 𝒵²w + p₁ 𝒵w + p₀ w = F`
  (`foc_imp_cubic`, `cubic_imp_foc`), with characteristic polynomial
  `P(Z) = λ_x Z(Z + ξ)² + λ_w(κ_w Z + Δ)² + λ_p(κ_p Z + Δ)²` (`charP`); complex expectations
  (`EC`, `fwdC`, `stage_existsUnique`) solve it factor by factor (`cubicC_existsUnique`,
  `cubicR_existsUnique`). Root location: `charP_ne_zero_of_nonneg` (no root `Z ≥ 0`),
  `stable_iff_ellForm` (a factor has a stable root iff `Z` lies outside the ellipse
  `ellForm β Z ≤ 1`), `stableRoots_of_real`, `stableRoots_of_re_neg`. Results:
  `foc_existsUnique` (under `StableRoots`, exactly one bounded optimal plan for all bounded data),
  `optimal_plan_exists`, `criterion_existsUnique` (commitment to the corrected criterion from `t₀`
  determines a unique bounded equilibrium), and the EXACT region (perfect foresight)
  `determinacy_iff_stableRoots`, `criterion_determinacy_iff_stableRoots`: strictly inside the
  ellipse existence fails for some initial conditions (`foc_not_determinate`, any expectation
  system), on the ellipse for a resonant cost-push path (`foc_not_exists_boundary`); the explicit
  parametrisation `P1` violates the root condition (`P1_not_stableRoots`,
  `P1_not_determinate`, `P1_criterion_not_determinate`).
* (2.14) unconditionally: `flexible_wage_family` — the explicit equilibria under `x_t = x̄_t` as
  `ξ_w` varies (`wFam`, `piFam`, `piwFam`) satisfy every hypothesis of `flexible_wage_limit` and
  converge uniformly to the flexible-wage equilibrium of (2.1) with `κ = ξ_p(ω_p + ω_w + σ⁻¹)`.
-/

namespace Woodford.OptimalPolicyRules.InflTargetStickyWages

open Filter Topology InflTargetInertia
open ForwardSolution (E_of_known)
open QuadraticRoots (lam1 lam1_root lam1_pos lam1_lt_one beta_lam1_mem lam1_le)
open ExpectationTools (EC EC_re EC_im EC_add EC_smul EC_sub EC_zero EC_ofReal EC_conj EC_tower
  EC_of_known norm_EC_le AdaptedC BoundedC EC_tsum_geom forwardC_iterate forwardC_unique fwdC
  fwdC_term_le fwdC_solves fwdC_bounded fwdC_adapted)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (2.11)–(2.15), pp. 565–566: the parameters of the sticky-wage model and its
loss function. -/
structure SW where
  /-- The discount factor `β`. -/
  beta : ℝ
  /-- `κ_p`. -/
  kp : ℝ
  /-- `κ_w`. -/
  kw : ℝ
  /-- `ξ_p`. -/
  xip : ℝ
  /-- `ξ_w`. -/
  xiw : ℝ
  /-- The weight `λ_p`. -/
  lp : ℝ
  /-- The weight `λ_w`. -/
  lw : ℝ
  /-- The weight `λ_x`. -/
  lx : ℝ
  /-- The optimal output gap `x*`. -/
  xstar : ℝ

/-! ### The model (2.11)–(2.13) -/

/-- Woodford (2003), (2.11), p. 565: `π_t = κ_p (x_t + u_t) + ξ_p (w_t − w^n_t) + β E_t π_{t+1}`. -/
def PriceEq (P : SW) (u wn π x w : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω = P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω) +
    P.beta * 𝔼.E t (π (t + 1)) ω

/-- Woodford (2003), (2.12), p. 565:
`π^w_t = κ_w (x_t + u_t) + ξ_w (w^n_t − w_t) + β E_t π^w_{t+1}`. -/
def WageEq (P : SW) (u wn πw x w : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, πw t ω = P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω) +
    P.beta * 𝔼.E t (πw (t + 1)) ω

/-- Woodford (2003), (2.13), p. 565: `w_t = w_{t−1} + π^w_t − π_t` (with `w_{t₀−1} = w₀`). -/
def WageId (w₀ : Ω → ℝ) (π πw w : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, w t ω = lagW w₀ w t ω + πw t ω - π t ω

/-- Woodford (2003), (2.11)–(2.13): an admissible plan — bounded adapted `π, π^w, x, w`
satisfying the three structural equations. -/
def PlanSW (P : SW) (w₀ : Ω → ℝ) (u wn π πw x w : ℕ → Ω → ℝ) : Prop :=
  PriceEq 𝔼 P u wn π x w ∧ WageEq 𝔼 P u wn πw x w ∧ WageId w₀ π πw w ∧
    𝔼.Adapted π ∧ 𝔼.Adapted πw ∧ 𝔼.Adapted x ∧ 𝔼.Adapted w ∧
    BoundedProc π ∧ BoundedProc πw ∧ BoundedProc x ∧ BoundedProc w

/-- Woodford (2003), (2.15), p. 566: `L_t = λ_p π_t² + λ_w (π^w_t)² + λ_x (x_t − x*)²`. -/
def lossSW (P : SW) (π πw x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => P.lp * π t ω ^ 2 + P.lw * πw t ω ^ 2 + P.lx * (x t ω - P.xstar) ^ 2

/-- Woodford (2003), Ch. 8 §1.1 Definition, for (2.11)–(2.15): timeless optimality — the plan is
admissible and minimises the expected loss among admissible plans with the same initial
values of the two forward-looking variables `π_{t₀}`, `π^w_{t₀}` (constraint (1.6)). -/
def TimelessOptimalSW (P : SW) (w₀ : Ω → ℝ) (u wn π πw x w : ℕ → Ω → ℝ) : Prop :=
  PlanSW 𝔼 P w₀ u wn π πw x w ∧ ∀ π' πw' x' w', PlanSW 𝔼 P w₀ u wn π' πw' x' w' →
    π' 0 = π 0 → πw' 0 = πw 0 →
    ∀ ω, expLossOf 𝔼 P.beta (lossSW P π πw x) ω ≤ expLossOf 𝔼 P.beta (lossSW P π' πw' x') ω

/-! ### (2.14): the flexible-wage limit `ξ_w → ∞` -/

/-- **Woodford (2003), (2.12) and p. 565–566**: with `κ_w = ξ_w (ω_w + σ⁻¹)` and wage inflation
bounded by `M`, the gap in the contemporaneous wage relation is at most `(1 + β) M / ξ_w`. -/
theorem wage_gap_bound {β M ξw ωw sinv : ℝ} (hβ0 : 0 ≤ β) (hξ : 0 < ξw)
    {u wn πw x w : ℕ → Ω → ℝ}
    (hw : ∀ t ω, πw t ω = ξw * (ωw + sinv) * (x t ω + u t ω) + ξw * (wn t ω - w t ω) +
      β * 𝔼.E t (πw (t + 1)) ω)
    (hM : ∀ t ω, |πw t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |(ωw + sinv) * (x t ω + u t ω) - (w t ω - wn t ω)| ≤ (1 + β) * M / ξw := by
  have h1 : ξw * ((ωw + sinv) * (x t ω + u t ω) - (w t ω - wn t ω)) =
      πw t ω - β * 𝔼.E t (πw (t + 1)) ω := by rw [hw t ω]; ring
  have h2 : |πw t ω - β * 𝔼.E t (πw (t + 1)) ω| ≤ (1 + β) * M := by
    have := 𝔼.abs_E_le (hM (t + 1)) t ω
    calc |πw t ω - β * 𝔼.E t (πw (t + 1)) ω| ≤ |πw t ω| + |β * 𝔼.E t (πw (t + 1)) ω| :=
          abs_sub _ _
      _ = |πw t ω| + β * |𝔼.E t (πw (t + 1)) ω| := by rw [abs_mul, abs_of_nonneg hβ0]
      _ ≤ M + β * M := add_le_add (hM t ω) (mul_le_mul_of_nonneg_left this hβ0)
      _ = (1 + β) * M := by ring
  rw [le_div_iff₀ hξ]
  have h3 : |(ωw + sinv) * (x t ω + u t ω) - (w t ω - wn t ω)| * ξw =
      |ξw * ((ωw + sinv) * (x t ω + u t ω) - (w t ω - wn t ω))| := by
    rw [abs_mul, abs_of_pos hξ, mul_comm]
  rw [h3, h1]
  exact h2

/-- **Woodford (2003), pp. 565–566 (the flexible-wage limit, genuine limit)**: for a family of
solutions of (2.12) indexed by `ξ_w` with `κ_w = ξ_w (ω_w + σ⁻¹)` and wage inflation bounded
uniformly in `ξ_w`, the gap `(ω_w + σ⁻¹)(x_t + u_t) − (w_t − w^n_t)` tends to `0` as
`ξ_w → ∞`. -/
theorem wage_gap_tendsto {β M ωw sinv : ℝ} (hβ0 : 0 ≤ β) {u wn : ℕ → Ω → ℝ}
    {πw x w : ℝ → ℕ → Ω → ℝ}
    (hw : ∀ ξ, 0 < ξ → ∀ t ω, πw ξ t ω = ξ * (ωw + sinv) * (x ξ t ω + u t ω) +
      ξ * (wn t ω - w ξ t ω) + β * 𝔼.E t (πw ξ (t + 1)) ω)
    (hM : ∀ ξ, 0 < ξ → ∀ t ω, |πw ξ t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Tendsto (fun ξ => (ωw + sinv) * (x ξ t ω + u t ω) - (w ξ t ω - wn t ω)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun ξ : ℝ => (1 + β) * M / ξ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with ξ hξ
  rw [Real.norm_eq_abs]
  exact wage_gap_bound 𝔼 hβ0 hξ (hw ξ hξ) (hM ξ hξ) t ω

/-- Woodford (2003), p. 566 (passing (2.11) to the limit): `E_t` is continuous along uniformly
convergent families. -/
theorem tendsto_E_of_tendstoUniformly {f : ℝ → Ω → ℝ} {g : Ω → ℝ}
    (h : TendstoUniformly f g atTop) (t : ℕ) (ω : Ω) :
    Tendsto (fun ξ => 𝔼.E t (f ξ) ω) atTop (𝓝 (𝔼.E t g ω)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have := (Metric.tendstoUniformly_iff.1 h) (ε / 2) (by positivity)
  filter_upwards [this] with ξ hξ
  rw [Real.dist_eq, ← Pi.sub_apply, ← map_sub]
  refine lt_of_le_of_lt (𝔼.abs_E_le (M := ε / 2) (fun ω' => ?_) t ω) (by linarith)
  have := hξ ω'
  rw [Real.dist_eq] at this
  rw [Pi.sub_apply, abs_sub_comm]
  exact this.le

/-- **Woodford (2003), (2.14), p. 566 (THE FLEXIBLE-WAGE LIMIT)**: let a family of solutions of
(2.11)–(2.12), indexed by `ξ_w → ∞`, with `κ_p = ξ_p ω_p`, `κ_w = ξ_w (ω_w + σ⁻¹)` and wage
inflation bounded uniformly, converge pointwise (`x`, `w`, `π`), with `π_{t+1}` converging
uniformly in the state. Then the limit satisfies `w_t − w^n_t = (ω_w + σ⁻¹)(x_t + u_t)` and the
aggregate-supply relation (2.1) `π_t = κ x_t + β E_t π_{t+1} + κ u_t` with
`κ = ξ_p (ω_p + ω_w + σ⁻¹)` (the cost-push shock rescaled to `κ u_t`). -/
theorem flexible_wage_limit {β M ξp ωp ωw sinv : ℝ} (hβ0 : 0 ≤ β) {u wn : ℕ → Ω → ℝ}
    {π πw x w : ℝ → ℕ → Ω → ℝ} {πL xL wL : ℕ → Ω → ℝ}
    (hp : ∀ ξ, 0 < ξ → ∀ t ω, π ξ t ω = ξp * ωp * (x ξ t ω + u t ω) +
      ξp * (w ξ t ω - wn t ω) + β * 𝔼.E t (π ξ (t + 1)) ω)
    (hw : ∀ ξ, 0 < ξ → ∀ t ω, πw ξ t ω = ξ * (ωw + sinv) * (x ξ t ω + u t ω) +
      ξ * (wn t ω - w ξ t ω) + β * 𝔼.E t (πw ξ (t + 1)) ω)
    (hM : ∀ ξ, 0 < ξ → ∀ t ω, |πw ξ t ω| ≤ M)
    (hx : ∀ t ω, Tendsto (fun ξ => x ξ t ω) atTop (𝓝 (xL t ω)))
    (hwl : ∀ t ω, Tendsto (fun ξ => w ξ t ω) atTop (𝓝 (wL t ω)))
    (hπ : ∀ t ω, Tendsto (fun ξ => π ξ t ω) atTop (𝓝 (πL t ω)))
    (hπu : ∀ t, TendstoUniformly (fun ξ => π ξ (t + 1)) (πL (t + 1)) atTop) :
    ∀ t ω, wL t ω - wn t ω = (ωw + sinv) * (xL t ω + u t ω) ∧
      πL t ω = ξp * (ωp + ωw + sinv) * xL t ω + β * 𝔼.E t (πL (t + 1)) ω +
        ξp * (ωp + ωw + sinv) * u t ω := by
  intro t ω
  have hgap := wage_gap_tendsto 𝔼 hβ0 hw hM t ω
  have hgap' : Tendsto (fun ξ => (ωw + sinv) * (x ξ t ω + u t ω) - (w ξ t ω - wn t ω)) atTop
      (𝓝 ((ωw + sinv) * (xL t ω + u t ω) - (wL t ω - wn t ω))) :=
    (((hx t ω).add tendsto_const_nhds).const_mul _).sub ((hwl t ω).sub tendsto_const_nhds)
  have h1 : wL t ω - wn t ω = (ωw + sinv) * (xL t ω + u t ω) := by
    have := tendsto_nhds_unique hgap' hgap
    linarith
  refine ⟨h1, ?_⟩
  have hR : Tendsto (fun ξ => ξp * ωp * (x ξ t ω + u t ω) + ξp * (w ξ t ω - wn t ω) +
      β * 𝔼.E t (π ξ (t + 1)) ω) atTop (𝓝 (ξp * ωp * (xL t ω + u t ω) +
        ξp * (wL t ω - wn t ω) + β * 𝔼.E t (πL (t + 1)) ω)) :=
    ((((hx t ω).add tendsto_const_nhds).const_mul _).add
      (((hwl t ω).sub tendsto_const_nhds).const_mul _)).add
      ((tendsto_E_of_tendstoUniformly 𝔼 (hπu t) t ω).const_mul _)
  have hL : Tendsto (fun ξ => π ξ t ω) atTop (𝓝 (ξp * ωp * (xL t ω + u t ω) +
      ξp * (wL t ω - wn t ω) + β * 𝔼.E t (πL (t + 1)) ω)) := by
    refine hR.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ξ hξ
    exact (hp ξ hξ t ω).symm
  have := tendsto_nhds_unique (hπ t ω) hL
  rw [this, h1]
  ring

/-! ### The Lagrangian and its first-order conditions (2.16)–(2.19) -/

/-- Woodford (2003), (2.16)–(2.19), p. 566: the first-order conditions, with multipliers
`φ_p, φ_w, υ` for (2.11), (2.12), (2.13) and initial multipliers `φ_{p,t₀−1} = mp₀`,
`φ_{w,t₀−1} = mw₀`. -/
def FOCsw (P : SW) (mp₀ mw₀ : Ω → ℝ) (π πw x mp mw ups : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, P.lp * π t ω + mp t ω - lagW mp₀ mp t ω + ups t ω = 0 ∧
    P.lw * πw t ω + mw t ω - lagW mw₀ mw t ω - ups t ω = 0 ∧
    P.lx * (x t ω - P.xstar) - P.kp * mp t ω - P.kw * mw t ω = 0 ∧
    ups t ω = P.xip * mp t ω - P.xiw * mw t ω + P.beta * 𝔼.E t (ups (t + 1)) ω

/-- **Woodford (2003), (2.16)–(2.19), p. 566 (the FOCs are the derivatives of the Lagrangian)**:
in the Lagrangian `∑ βᵗ {½ L_t + φ_{pt}[π_t − κ_p(x_t + u_t) − ξ_p(w_t − w^n_t) − β π_{t+1}]
+ φ_{wt}[π^w_t − κ_w(x_t + u_t) − ξ_w(w^n_t − w_t) − β π^w_{t+1}] + υ_t[w_t − w_{t−1} − π^w_t
+ π_t]}` (perfect foresight, divided by `βᵗ`), the terms containing `π_t`, `π^w_t`, `x_t`, `w_t`
have derivatives equal to the left sides of (2.16), (2.17), (2.18) and `−((2.19))`
(`−ξ_p φ_{pt} + ξ_w φ_{wt} + υ_t − β υ_{t+1}`). -/
theorem lagrangian_derivs (P : SW) (mp mp' mw mw' ups ups' v : ℝ) :
    HasDerivAt (fun v => P.lp / 2 * v ^ 2 + mp * v - mp' * v + ups * v)
        (P.lp * v + mp - mp' + ups) v ∧
      HasDerivAt (fun v => P.lw / 2 * v ^ 2 + mw * v - mw' * v - ups * v)
        (P.lw * v + mw - mw' - ups) v ∧
      HasDerivAt (fun v => P.lx / 2 * (v - P.xstar) ^ 2 - mp * P.kp * v - mw * P.kw * v)
        (P.lx * (v - P.xstar) - P.kp * mp - P.kw * mw) v ∧
      HasDerivAt (fun v => -(mp * P.xip * v) + mw * P.xiw * v + ups * v - P.beta * ups' * v)
        (-(P.xip * mp - P.xiw * mw + P.beta * ups' - ups)) v := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hasDerivAt_quad (P.lp / 2) (mp - mp' + ups) 0 v
    convert h using 1
    · funext v; ring
    · ring
  · have h := hasDerivAt_quad (P.lw / 2) (mw - mw' - ups) 0 v
    convert h using 1
    · funext v; ring
    · ring
  · have h := hasDerivAt_quad (P.lx / 2) (-(P.lx * P.xstar) - mp * P.kp - mw * P.kw)
      (P.lx / 2 * P.xstar ^ 2) v
    convert h using 1
    · funext v; ring
    · ring
  · have h := hasDerivAt_quad 0 (-(mp * P.xip) + mw * P.xiw + ups - P.beta * ups') 0 v
    convert h using 1
    · funext v; ring
    · ring

/-! ### Lagrangian sufficiency for the sticky-wage problem -/

/-- Woodford (2003), (2.15): the loss of a bounded plan is bounded. -/
theorem lossSW_bounded (P : SW) {π πw x : ℕ → Ω → ℝ} (hπ : BoundedProc π)
    (hπw : BoundedProc πw) (hx : BoundedProc x) : ∃ L, ∀ t ω, |lossSW P π πw x t ω| ≤ L := by
  obtain ⟨A, hA⟩ := hπ
  obtain ⟨B, hB⟩ := hπw
  obtain ⟨C, hC⟩ := hx
  refine ⟨|P.lp| * A ^ 2 + |P.lw| * B ^ 2 + |P.lx| * (C + |P.xstar|) ^ 2, fun t ω => ?_⟩
  have h1 := sq_bound (hA t ω)
  have h2 := sq_bound (hB t ω)
  have h3 := sq_bound ((abs_sub _ _).trans (add_le_add (hC t ω) le_rfl) :
    |x t ω - P.xstar| ≤ C + |P.xstar|)
  unfold lossSW
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  all_goals rw [abs_mul]; gcongr

/-- **Woodford (2003), (2.15)–(2.19) (the Lagrangian identity and sufficiency)**: if
`(π*, π^w*, x*, w*)` is admissible and satisfies the first-order conditions with bounded adapted
multipliers and bounded initial multipliers, and `(π, π^w, x, w)` is any admissible plan (same
disturbances, same `w_{t₀−1}`) with `mp₀ (π_0 − π*_0) = 0` and `mw₀ (π^w_0 − π^w*_0) = 0`
(the timeless initial constraints, or zero initial multipliers), then the excess expected loss
is `∑ βᵗ E_0(λ_p (Δπ_t)² + λ_w (Δπ^w_t)² + λ_x (Δx_t)²)`. -/
theorem focSW_excess (hpo : 𝔼.PullOut) (P : SW) (hβ0 : 0 ≤ P.beta) (hβ1 : P.beta < 1)
    (hlp : 0 ≤ P.lp) (hlw : 0 ≤ P.lw) (hlx : 0 ≤ P.lx) {w₀ : Ω → ℝ}
    {u wn π πw x w πs πws xs ws mp mw ups : ℕ → Ω → ℝ} {mp₀ mw₀ : Ω → ℝ}
    (hp : PlanSW 𝔼 P w₀ u wn π πw x w) (hps : PlanSW 𝔼 P w₀ u wn πs πws xs ws)
    (hmpa : 𝔼.Adapted mp) (hmwa : 𝔼.Adapted mw)
    (hmpb : BoundedProc mp) (hmwb : BoundedProc mw) (hupsb : BoundedProc ups)
    (hmp₀ : ∃ B, ∀ ω, |mp₀ ω| ≤ B) (hmw₀ : ∃ B, ∀ ω, |mw₀ ω| ≤ B)
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ πs πws xs mp mw ups)
    (hinit1 : ∀ ω, mp₀ ω * (π 0 ω - πs 0 ω) = 0) (hinit2 : ∀ ω, mw₀ ω * (πw 0 ω - πws 0 ω) = 0)
    (ω : Ω) :
    HasSum (fun t => P.beta ^ t * 𝔼.E 0 (fun ω => P.lp * (π t ω - πs t ω) ^ 2 +
        P.lw * (πw t ω - πws t ω) ^ 2 + P.lx * (x t ω - xs t ω) ^ 2) ω)
      (expLossOf 𝔼 P.beta (lossSW P π πw x) ω - expLossOf 𝔼 P.beta (lossSW P πs πws xs) ω) := by
  obtain ⟨hpe, hwe, hwi, -, -, -, hwa, hπb, hπwb, hxb, hwb⟩ := hp
  obtain ⟨hpes, hwes, hwis, -, -, -, hwsa, hπsb, hπwsb, hxsb, hwsb⟩ := hps
  obtain ⟨L, hL⟩ := lossSW_bounded P hπb hπwb hxb
  obtain ⟨Ls, hLs⟩ := lossSW_bounded P hπsb hπwsb hxsb
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨As, hAs⟩ := hπsb
  obtain ⟨Bw, hBw⟩ := hπwb
  obtain ⟨Bws, hBws⟩ := hπwsb
  obtain ⟨W, hW⟩ := hwb
  obtain ⟨Ws, hWs⟩ := hwsb
  obtain ⟨Zp, hZp⟩ := hmpb
  obtain ⟨Zw, hZw⟩ := hmwb
  obtain ⟨Zu, hZu⟩ := hupsb
  obtain ⟨Bp₀, hBp₀⟩ := hmp₀
  obtain ⟨Bw₀, hBw₀⟩ := hmw₀
  have hlp' := lagW_bounded hBp₀ hZp
  have hlw' := lagW_bounded hBw₀ hZw
  have hW0 : 0 ≤ W + Ws := add_nonneg ((abs_nonneg _).trans (hW 0 ω))
    ((abs_nonneg _).trans (hWs 0 ω))
  have hdw : ∀ t ω', |lagW w₀ w t ω' - lagW w₀ ws t ω'| ≤ W + Ws := fun t ω' => by
    cases t with
    | zero => simpa using hW0
    | succ t => exact (abs_sub _ _).trans (add_le_add (hW t ω') (hWs t ω'))
  have hHb : ∀ t ω', |(lagW mp₀ mp t * (π t - πs t) + lagW mw₀ mw t * (πw t - πws t) -
      ups t * (lagW w₀ w t - lagW w₀ ws t)) ω'| ≤
      max Bp₀ Zp * (A + As) + max Bw₀ Zw * (Bw + Bws) + Zu * (W + Ws) := by
    intro t ω'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]
      exact mul_le_mul (hlp' t ω') ((abs_sub _ _).trans (add_le_add (hA t ω') (hAs t ω')))
        (abs_nonneg _) ((abs_nonneg _).trans (hlp' t ω'))
    · rw [abs_mul]
      exact mul_le_mul (hlw' t ω') ((abs_sub _ _).trans (add_le_add (hBw t ω') (hBws t ω')))
        (abs_nonneg _) ((abs_nonneg _).trans (hlw' t ω'))
    · rw [abs_mul]
      exact mul_le_mul (hZu t ω') (hdw t ω') (abs_nonneg _) ((abs_nonneg _).trans (hZu t ω'))
  refine excess_hasSum 𝔼 hβ0 hβ1 hL hLs (fun t ω => by positivity) hHb
    (G := fun t => mp t * 𝔼.E t (π (t + 1) - πs (t + 1)) +
      mw t * 𝔼.E t (πw (t + 1) - πws (t + 1)) - (w t - ws t) * 𝔼.E t (ups (t + 1)))
    (fun t ω => ?_) (fun t => ?_) ?_ ω
  · obtain ⟨f1, f2, f3, f4⟩ := hfoc t ω
    have pe := hpe t ω
    have pes := hpes t ω
    have we := hwe t ω
    have wes := hwes t ω
    have wi := hwi t ω
    have wis := hwis t ω
    simp only [lossSW, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, map_sub]
    linear_combination 2 * (π t ω - πs t ω) * f1 + 2 * (πw t ω - πws t ω) * f2 +
      2 * (x t ω - xs t ω) * f3 - 2 * mp t ω * (pe - pes) - 2 * mw t ω * (we - wes) -
      2 * ups t ω * (wi - wis) + 2 * (w t ω - ws t ω) * f4
  · have hw' : 𝔼.E t (w t - ws t) = w t - ws t := by rw [map_sub, hwa t, hwsa t]
    rw [map_sub, map_add, E0_pull 𝔼 hpo (hmpa t), E0_pull 𝔼 hpo (hmwa t), E0_pull 𝔼 hpo hw']
    change _ = 𝔼.E 0 (mp t * (π (t + 1) - πs (t + 1)) + mw t * (πw (t + 1) - πws (t + 1)) -
      ups (t + 1) * (w t - ws t))
    rw [map_sub, map_add, mul_comm (ups (t + 1))]
  · have : lagW mp₀ mp 0 * (π 0 - πs 0) + lagW mw₀ mw 0 * (πw 0 - πws 0) -
        ups 0 * (lagW w₀ w 0 - lagW w₀ ws 0) = 0 := by
      funext ω'
      simp only [lagW_zero, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, sub_self, mul_zero,
        Pi.zero_apply]
      rw [hinit1 ω', hinit2 ω']
      ring
    rw [this, map_zero]

/-- **Woodford (2003), (2.15)–(2.19) (sufficiency)**: a plan satisfying the first-order
conditions (bounded adapted multipliers) has the smallest expected loss, state by state, among
admissible plans satisfying the initial constraints. -/
theorem focSW_sufficient (hpo : 𝔼.PullOut) (P : SW) (hβ0 : 0 ≤ P.beta) (hβ1 : P.beta < 1)
    (hlp : 0 ≤ P.lp) (hlw : 0 ≤ P.lw) (hlx : 0 ≤ P.lx) {w₀ : Ω → ℝ}
    {u wn π πw x w πs πws xs ws mp mw ups : ℕ → Ω → ℝ} {mp₀ mw₀ : Ω → ℝ}
    (hp : PlanSW 𝔼 P w₀ u wn π πw x w) (hps : PlanSW 𝔼 P w₀ u wn πs πws xs ws)
    (hmpa : 𝔼.Adapted mp) (hmwa : 𝔼.Adapted mw)
    (hmpb : BoundedProc mp) (hmwb : BoundedProc mw) (hupsb : BoundedProc ups)
    (hmp₀ : ∃ B, ∀ ω, |mp₀ ω| ≤ B) (hmw₀ : ∃ B, ∀ ω, |mw₀ ω| ≤ B)
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ πs πws xs mp mw ups)
    (hinit1 : ∀ ω, mp₀ ω * (π 0 ω - πs 0 ω) = 0) (hinit2 : ∀ ω, mw₀ ω * (πw 0 ω - πws 0 ω) = 0)
    (ω : Ω) :
    expLossOf 𝔼 P.beta (lossSW P πs πws xs) ω ≤ expLossOf 𝔼 P.beta (lossSW P π πw x) ω :=
  expLossOf_le_of_excess 𝔼 hβ0 (fun t ω => by positivity)
    (focSW_excess 𝔼 hpo P hβ0 hβ1 hlp hlw hlx hp hps hmpa hmwa hmpb hmwb hupsb hmp₀ hmw₀
      hfoc hinit1 hinit2 ω)

/-- **Woodford (2003), (2.15)–(2.19) (uniqueness of the optimum)**: an admissible plan with the
same expected loss at `ω` as a plan satisfying the first-order conditions coincides with it in
conditional mean square (`π`, `π^w` and `x`). -/
theorem focSW_unique (hpo : 𝔼.PullOut) (P : SW) (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hlx : 0 < P.lx) {w₀ : Ω → ℝ}
    {u wn π πw x w πs πws xs ws mp mw ups : ℕ → Ω → ℝ} {mp₀ mw₀ : Ω → ℝ}
    (hp : PlanSW 𝔼 P w₀ u wn π πw x w) (hps : PlanSW 𝔼 P w₀ u wn πs πws xs ws)
    (hmpa : 𝔼.Adapted mp) (hmwa : 𝔼.Adapted mw)
    (hmpb : BoundedProc mp) (hmwb : BoundedProc mw) (hupsb : BoundedProc ups)
    (hmp₀ : ∃ B, ∀ ω, |mp₀ ω| ≤ B) (hmw₀ : ∃ B, ∀ ω, |mw₀ ω| ≤ B)
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ πs πws xs mp mw ups)
    (hinit1 : ∀ ω, mp₀ ω * (π 0 ω - πs 0 ω) = 0) (hinit2 : ∀ ω, mw₀ ω * (πw 0 ω - πws 0 ω) = 0)
    (ω : Ω) (heq : expLossOf 𝔼 P.beta (lossSW P π πw x) ω =
      expLossOf 𝔼 P.beta (lossSW P πs πws xs) ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (πw t ω - πws t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 := by
  have h0 := E0_eq_zero_of_excess 𝔼 hβ0 (fun t ω => by positivity)
    (focSW_excess 𝔼 hpo P hβ0.le hβ1 hlp.le hlw.le hlx.le hp hps hmpa hmwa hmpb hmwb
      hupsb hmp₀ hmw₀ hfoc hinit1 hinit2 ω) heq t
  have hsplit : (fun ω => P.lp * (π t ω - πs t ω) ^ 2 + P.lw * (πw t ω - πws t ω) ^ 2 +
      P.lx * (x t ω - xs t ω) ^ 2) = P.lp • (fun ω => (π t ω - πs t ω) ^ 2) +
      P.lw • (fun ω => (πw t ω - πws t ω) ^ 2) + P.lx • (fun ω => (x t ω - xs t ω) ^ 2) := by
    funext ω'; simp [smul_eq_mul]
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul] at h0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
  have e1 := E_nonneg 𝔼 (f := fun ω => (π t ω - πs t ω) ^ 2) (fun ω => sq_nonneg _) 0 ω
  have e2 := E_nonneg 𝔼 (f := fun ω => (πw t ω - πws t ω) ^ 2) (fun ω => sq_nonneg _) 0 ω
  have e3 := E_nonneg 𝔼 (f := fun ω => (x t ω - xs t ω) ^ 2) (fun ω => sq_nonneg _) 0 ω
  have a1 := mul_nonneg hlp.le e1
  have a2 := mul_nonneg hlw.le e2
  have a3 := mul_nonneg hlx.le e3
  refine ⟨?_, ?_, ?_⟩
  · have : P.lp * 𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hlp.ne'
  · have : P.lw * 𝔼.E 0 (fun ω => (πw t ω - πws t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hlw.ne'
  · have : P.lx * 𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hlx.ne'

/-! ### Eliminating the multipliers: the target criterion (2.20)–(2.21) -/

/-- Woodford (2003), (2.21), p. 567 (multiplied out):
`q_t = λ_p κ_p π_t + λ_w κ_w π^w_t + λ_x (x_t − x_{t−1})`. -/
def qSW (P : SW) (x₀ : Ω → ℝ) (π πw x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => P.lp * P.kp * π t ω + P.lw * P.kw * πw t ω + P.lx * (x t ω - lagW x₀ x t ω)

/-- Woodford (2003), p. 566: `π^asym_t = λ_p ξ_p π_t − λ_w ξ_w π^w_t`. -/
def piAsym (P : SW) (π πw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => P.lp * P.xip * π t ω - P.lw * P.xiw * πw t ω

/-- Woodford (2003), p. 566: `π^sym_t = (λ_p κ_p π_t + λ_w κ_w π^w_t)/(λ_p κ_p + λ_w κ_w)`. -/
noncomputable def piSym (P : SW) (π πw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (P.lp * P.kp * π t ω + P.lw * P.kw * πw t ω) / (P.lp * P.kp + P.lw * P.kw)

/-- **Woodford (2003), (2.21), p. 567**: `q_t = (λ_p κ_p + λ_w κ_w)[π^sym_t +
λ_x/(λ_p κ_p + λ_w κ_w) (x_t − x_{t−1})]`. -/
theorem q_eq_sym (P : SW) (h : P.lp * P.kp + P.lw * P.kw ≠ 0) (x₀ : Ω → ℝ)
    (π πw x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    qSW P x₀ π πw x t ω = (P.lp * P.kp + P.lw * P.kw) * (piSym P π πw t ω +
      P.lx / (P.lp * P.kp + P.lw * P.kw) * (x t ω - lagW x₀ x t ω)) := by
  simp only [qSW, piSym]
  field_simp

/-- Woodford (2003), (2.20) CORRECTED (survey E14), at date `t + 1`, the left side of
`(κ_w − κ_p) π^asym_t + (ξ_p + ξ_w) q_t − {E_t[β q_{t+1} − q_t] − E_{t−1}[β q_t − q_{t−1}]}`. -/
noncomputable def critC (P : SW) (x₀ : Ω → ℝ) (π πw x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (P.kw - P.kp) * piAsym P π πw (t + 1) ω + (P.xip + P.xiw) * qSW P x₀ π πw x (t + 1) ω -
    (𝔼.E (t + 1) (fun ω => P.beta * qSW P x₀ π πw x (t + 2) ω - qSW P x₀ π πw x (t + 1) ω) ω -
      𝔼.E t (fun ω => P.beta * qSW P x₀ π πw x (t + 1) ω - qSW P x₀ π πw x t ω) ω)

/-- Woodford (2003), (2.20) AS PRINTED, at date `t + 1`: `(κ_w − κ_p) π^asym_t + (ξ_p + ξ_w) q_t
+ (κ_w − κ_p){E_t[β q_{t+1} − q_t] − E_{t−1}[β q_t − q_{t−1}]}`. -/
noncomputable def critPrinted (P : SW) (x₀ : Ω → ℝ) (π πw x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (P.kw - P.kp) * piAsym P π πw (t + 1) ω + (P.xip + P.xiw) * qSW P x₀ π πw x (t + 1) ω +
    (P.kw - P.kp) *
      (𝔼.E (t + 1) (fun ω => P.beta * qSW P x₀ π πw x (t + 2) ω - qSW P x₀ π πw x (t + 1) ω) ω -
        𝔼.E t (fun ω => P.beta * qSW P x₀ π πw x (t + 1) ω - qSW P x₀ π πw x t ω) ω)

/-- Woodford (2003), (2.20) corrected: the criterion holds at every date `t > t₀`. -/
def CriterionC (P : SW) (x₀ : Ω → ℝ) (π πw x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, critC 𝔼 P x₀ π πw x t ω = 0

/-- **Woodford (2003), (2.16)–(2.18) (first elimination step)**: the first-order conditions imply
`q_t = (κ_w − κ_p) υ_t` at every date `t > t₀`; at `t₀` as well when the initial multipliers are
self-consistent, `λ_x (x_{t₀−1} − x*) = κ_p φ_{p,t₀−1} + κ_w φ_{w,t₀−1}` ((2.18) at `t₀ − 1`). -/
theorem foc_q_eq {P : SW} {mp₀ mw₀ x₀ : Ω → ℝ} {π πw x mp mw ups : ℕ → Ω → ℝ}
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups) :
    (∀ t ω, qSW P x₀ π πw x (t + 1) ω = (P.kw - P.kp) * ups (t + 1) ω) ∧
    ((∀ ω, P.lx * (x₀ ω - P.xstar) - P.kp * mp₀ ω - P.kw * mw₀ ω = 0) →
      ∀ t ω, qSW P x₀ π πw x t ω = (P.kw - P.kp) * ups t ω) := by
  have hsucc : ∀ t ω, qSW P x₀ π πw x (t + 1) ω = (P.kw - P.kp) * ups (t + 1) ω := by
    intro t ω
    obtain ⟨f1, f2, f3, -⟩ := hfoc (t + 1) ω
    obtain ⟨-, -, g3, -⟩ := hfoc t ω
    simp only [lagW_succ] at f1 f2
    simp only [qSW, lagW_succ]
    linear_combination P.kp * f1 + P.kw * f2 + f3 - g3
  refine ⟨hsucc, fun hsc t ω => ?_⟩
  cases t with
  | zero =>
    obtain ⟨f1, f2, f3, -⟩ := hfoc 0 ω
    simp only [lagW_zero] at f1 f2
    simp only [qSW, lagW_zero]
    linear_combination P.kp * f1 + P.kw * f2 + f3 - hsc ω
  | succ t => exact hsucc t ω

/-- **Woodford (2003), (2.16), (2.17), (2.19) (second elimination step)**: the first-order
conditions imply `π^asym_t + (ξ_p + ξ_w) υ_t + (υ_t − β E_t υ_{t+1}) − (υ_{t−1} − β E_{t−1} υ_t)
= 0` at every date `t > t₀`. -/
theorem foc_asym_eq {P : SW} {mp₀ mw₀ : Ω → ℝ} {π πw x mp mw ups : ℕ → Ω → ℝ}
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups) (t : ℕ) (ω : Ω) :
    piAsym P π πw (t + 1) ω + (P.xip + P.xiw) * ups (t + 1) ω +
      ((ups (t + 1) ω - P.beta * 𝔼.E (t + 1) (ups (t + 2)) ω) -
        (ups t ω - P.beta * 𝔼.E t (ups (t + 1)) ω)) = 0 := by
  obtain ⟨f1, f2, -, f4⟩ := hfoc (t + 1) ω
  obtain ⟨-, -, -, g4⟩ := hfoc t ω
  simp only [lagW_succ] at f1 f2
  simp only [piAsym]
  linear_combination P.xip * f1 - P.xiw * f2 + f4 - g4

/-- Woodford (2003), (2.20): if `q_s = (κ_w − κ_p) υ_s` at dates `t, t+1, t+2` (with `υ`
adapted) and the second elimination identity holds at `t + 1`, the corrected criterion holds at
`t + 1`. -/
theorem crit_of_q_ups {P : SW} {x₀ : Ω → ℝ} {π πw x ups : ℕ → Ω → ℝ} (hua : 𝔼.Adapted ups)
    {t : ℕ} (hq : ∀ s, t ≤ s → s ≤ t + 2 → qSW P x₀ π πw x s = (P.kw - P.kp) • ups s)
    (hA : ∀ ω, piAsym P π πw (t + 1) ω + (P.xip + P.xiw) * ups (t + 1) ω +
      ((ups (t + 1) ω - P.beta * 𝔼.E (t + 1) (ups (t + 2)) ω) -
        (ups t ω - P.beta * 𝔼.E t (ups (t + 1)) ω)) = 0) (ω : Ω) :
    critC 𝔼 P x₀ π πw x t ω = 0 := by
  have e1 : (fun ω => P.beta * qSW P x₀ π πw x (t + 2) ω - qSW P x₀ π πw x (t + 1) ω) =
      (P.kw - P.kp) • (P.beta • ups (t + 2) - ups (t + 1)) := by
    rw [hq (t + 2) (by omega) le_rfl, hq (t + 1) (by omega) (by omega)]
    funext ω'; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have e2 : (fun ω => P.beta * qSW P x₀ π πw x (t + 1) ω - qSW P x₀ π πw x t ω) =
      (P.kw - P.kp) • (P.beta • ups (t + 1) - ups t) := by
    rw [hq (t + 1) (by omega) (by omega), hq t le_rfl (by omega)]
    funext ω'; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hq1 := congrFun (hq (t + 1) (by omega) (by omega)) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hq1
  simp only [critC]
  rw [e1, e2]
  simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hua (t + 1), hua t,
    hq1]
  linear_combination (P.kw - P.kp) * hA ω

/-- **Woodford (2003), (2.16)–(2.20) (THE CORRECTED TARGET CRITERION, survey E14)**: eliminating
the multipliers from the first-order conditions (adapted `υ`) gives
`(κ_w − κ_p) π^asym_t + (ξ_p + ξ_w) q_t − {E_t[β q_{t+1} − q_t] − E_{t−1}[β q_t − q_{t−1}]} = 0`
at every date `t ≥ t₀ + 2`, and at every date `t > t₀` when the initial multipliers are
self-consistent. -/
theorem foc_imp_criterion {P : SW} {mp₀ mw₀ x₀ : Ω → ℝ} {π πw x mp mw ups : ℕ → Ω → ℝ}
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups) (hua : 𝔼.Adapted ups) :
    (∀ t ω, critC 𝔼 P x₀ π πw x (t + 1) ω = 0) ∧
    ((∀ ω, P.lx * (x₀ ω - P.xstar) - P.kp * mp₀ ω - P.kw * mw₀ ω = 0) →
      CriterionC 𝔼 P x₀ π πw x) := by
  obtain ⟨hs, hsc⟩ := foc_q_eq 𝔼 (x₀ := x₀) hfoc
  refine ⟨fun t ω => crit_of_q_ups 𝔼 hua (fun s h1 _ => ?_) (foc_asym_eq 𝔼 hfoc (t + 1)) ω,
    fun h t ω => crit_of_q_ups 𝔼 hua (fun s _ _ => ?_) (foc_asym_eq 𝔼 hfoc t) ω⟩
  · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hs s' ω'
  · funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hsc h s ω'

/-! ### The printed (2.20) is wrong: a concrete optimal plan violating it -/

/-- Woodford (2003), (2.11)–(2.15): the parameters of the counterexample: `β = 1/2`, `κ_p = 1`,
`κ_w = 2`, `ξ_p = ξ_w = 1`, `λ_p = λ_w = λ_x = 1`, `x* = 0`. -/
noncomputable def P0 : SW := ⟨1 / 2, 1, 2, 1, 1, 1, 1, 1, 0⟩

/-- Woodford (2003), (2.11)–(2.12) (perfect foresight): given paths for `π, π^w, x, w`, the
disturbance `x_t + u_t = (ξ_w A_t + ξ_p B_t)/(κ_p ξ_w + κ_w ξ_p)` (with `A_t = π_t − β π_{t+1}`,
`B_t = π^w_t − β π^w_{t+1}`) makes (2.11)–(2.12) hold. -/
noncomputable def uFit (P : SW) (π πw x : ℕ → Unit → ℝ) (t : ℕ) : Unit → ℝ :=
  fun ω => (P.xiw * (π t ω - P.beta * π (t + 1) ω) + P.xip * (πw t ω - P.beta * πw (t + 1) ω)) /
    (P.kp * P.xiw + P.kw * P.xip) - x t ω

/-- Woodford (2003), (2.11)–(2.12) (perfect foresight): the natural real wage
`w^n_t = w_t − (κ_w A_t − κ_p B_t)/(κ_p ξ_w + κ_w ξ_p)` that fits given paths. -/
noncomputable def wnFit (P : SW) (π πw w : ℕ → Unit → ℝ) (t : ℕ) : Unit → ℝ :=
  fun ω => w t ω - (P.kw * (π t ω - P.beta * π (t + 1) ω) -
    P.kp * (πw t ω - P.beta * πw (t + 1) ω)) / (P.kp * P.xiw + P.kw * P.xip)

/-- **Woodford (2003), (2.11)–(2.12)**: under perfect foresight, ANY paths of `π, π^w, x, w` are
consistent with (2.11)–(2.12) for suitable disturbances `u`, `w^n` (when
`κ_p ξ_w + κ_w ξ_p ≠ 0`). -/
theorem fit_disturbances (P : SW) (hD : P.kp * P.xiw + P.kw * P.xip ≠ 0)
    (π πw x w : ℕ → Unit → ℝ) :
    PriceEq perfectForesight P (uFit P π πw x) (wnFit P π πw w) π x w ∧
      WageEq perfectForesight P (uFit P π πw x) (wnFit P π πw w) πw x w := by
  refine ⟨fun t ω => ?_, fun t ω => ?_⟩
  · change π t ω = P.kp * (x t ω + uFit P π πw x t ω) +
      P.xip * (w t ω - wnFit P π πw w t ω) + P.beta * π (t + 1) ω
    simp only [uFit, wnFit]
    set D := P.kp * P.xiw + P.kw * P.xip with hDdef
    field_simp
    rw [hDdef]
    ring
  · change πw t ω = P.kw * (x t ω + uFit P π πw x t ω) +
      P.xiw * (wnFit P π πw w t ω - w t ω) + P.beta * πw (t + 1) ω
    simp only [uFit, wnFit]
    set D := P.kp * P.xiw + P.kw * P.xip with hDdef
    field_simp
    rw [hDdef]
    ring

/-- Woodford (2003), (2.20) (E14 counterexample): the inflation path `π = (−1/2, −2, 1, 0, 0, …)`.
-/
noncomputable def piC (t : ℕ) (_ : Unit) : ℝ :=
  if t = 0 then -1 / 2 else if t = 1 then -2 else if t = 2 then 1 else 0

/-- Woodford (2003), (2.20) (E14 counterexample): the wage-inflation path (equal to `υ`): `π^w =
(1/2, 1, 0, …)`. -/
noncomputable def upsC (t : ℕ) (_ : Unit) : ℝ :=
  if t = 0 then 1 / 2 else if t = 1 then 1 else 0

/-- Woodford (2003), (2.20) (E14 counterexample): the output gap (equal to `φ_p`): `x = (0, 1, 0,
…)`. -/
noncomputable def mpC (t : ℕ) (_ : Unit) : ℝ := if t = 1 then 1 else 0

/-- Woodford (2003), (2.20) (E14 counterexample): the real wage `w = (1, 4, 3, 3, …)` from `w_{−1} =
0` and (2.13). -/
noncomputable def wC (t : ℕ) (_ : Unit) : ℝ := if t = 0 then 1 else if t = 1 then 4 else 3

/-- Woodford (2003), (2.20) (E14 counterexample): under perfect foresight `E_t` is the
identity. -/
theorem pf_E (t : ℕ) (f : Unit → ℝ) : perfectForesight.E t f = f := rfl

/-- Woodford (2003), (2.11)–(2.13) (E14 counterexample): the plan is admissible (bounded; adapted
trivially). -/
theorem planC : PlanSW perfectForesight P0 (fun _ => 0) (uFit P0 piC upsC mpC)
    (wnFit P0 piC upsC wC) piC upsC mpC wC := by
  obtain ⟨h1, h2⟩ := fit_disturbances P0 (by norm_num [P0]) piC upsC mpC wC
  refine ⟨h1, h2, fun t ω => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    ⟨2, fun t ω => ?_⟩, ⟨1, fun t ω => ?_⟩, ⟨1, fun t ω => ?_⟩, ⟨4, fun t ω => ?_⟩⟩
  · rcases t with _ | _ | _ | t <;> norm_num [lagW, wC, upsC, piC]
  · simp only [piC]; split_ifs <;> norm_num
  · simp only [upsC]; split_ifs <;> norm_num
  · simp only [mpC]; split_ifs <;> norm_num
  · simp only [wC]; split_ifs <;> norm_num

/-- Woodford (2003), (2.16)–(2.19) (E14 counterexample): the plan satisfies the FOCs (2.16)–(2.19),
with multipliers
`φ_p = (0, 1, 0, …)`, `φ_w = 0`, `υ = (1/2, 1, 0, …)` and zero initial multipliers. -/
theorem focC : FOCsw perfectForesight P0 0 0 piC upsC mpC mpC 0 upsC := by
  intro t ω
  rcases t with _ | _ | _ | t <;> norm_num [P0, lagW, pf_E, piC, upsC, mpC]

/-- **Woodford (2003), (2.20) (survey E14, counterexample to the printed criterion)**: in the
model with `β = 1/2`, `κ_p = 1`, `κ_w = 2`, `ξ_p = ξ_w = 1`, `λ_p = λ_w = λ_x = 1`, `x* = 0` and
the disturbances `uFit`, `wnFit`, the plan `(piC, upsC, mpC, wC)` is admissible, satisfies the
first-order conditions, and is therefore optimal (it minimises the loss among ALL admissible
plans, not only those with the same initial values); it satisfies the corrected criterion at
date 1, but the printed (2.20) fails there (its left side is `−2`). -/
theorem printed_criterion_counterexample :
    PlanSW perfectForesight P0 (fun _ => 0) (uFit P0 piC upsC mpC) (wnFit P0 piC upsC wC)
        piC upsC mpC wC ∧
      (∀ π' πw' x' w', PlanSW perfectForesight P0 (fun _ => 0) (uFit P0 piC upsC mpC)
          (wnFit P0 piC upsC wC) π' πw' x' w' →
        ∀ ω, expLossOf perfectForesight P0.beta (lossSW P0 piC upsC mpC) ω ≤
          expLossOf perfectForesight P0.beta (lossSW P0 π' πw' x') ω) ∧
      critC perfectForesight P0 (fun _ => 0) piC upsC mpC 0 () = 0 ∧
      critPrinted perfectForesight P0 (fun _ => 0) piC upsC mpC 0 () = -2 := by
  refine ⟨planC, fun π' πw' x' w' hp' ω => ?_, ?_, ?_⟩
  · refine focSW_sufficient perfectForesight perfectForesight_pullOut P0 (by norm_num [P0])
      (by norm_num [P0]) (by norm_num [P0]) (by norm_num [P0]) (by norm_num [P0]) hp' planC
      (fun _ => rfl) (fun _ => rfl) ⟨1, fun t ω => ?_⟩ ⟨0, fun t ω => by simp⟩
      ⟨1, fun t ω => ?_⟩ ⟨0, fun ω => by simp⟩ ⟨0, fun ω => by simp⟩ focC
      (fun ω => by simp) (fun ω => by simp) ω
    · simp only [mpC]; split_ifs <;> norm_num
    · simp only [upsC]; split_ifs <;> norm_num
  · norm_num [critC, qSW, piAsym, P0, lagW, pf_E, piC, upsC, mpC]
  · norm_num [critPrinted, qSW, piAsym, P0, lagW, pf_E, piC, upsC, mpC]

/-! ### Sufficiency of the corrected criterion (`κ_w ≠ κ_p`) -/

/-- Woodford (2003), (2.16)–(2.20) (the algebraic core of reconstructing the multipliers): if
`φ_p, φ_w` solve (2.18)–(2.19) in levels at `t` and `t + 1` (with `g = υ − β E υ'`), and
`q_{t+1} = (κ_w − κ_p) υ_{t+1}` and the corrected criterion hold at `t + 1`, then (2.16) and
(2.17) hold at `t + 1`. -/
theorem elim_alg {kp kw xip xiw lp lw X X' g g' p pw mp mp' mw mw' up : ℝ}
    (hD0 : kp * xiw + kw * xip ≠ 0) (hc0 : kw - kp ≠ 0)
    (hmp : (kp * xiw + kw * xip) * mp = xiw * X + kw * g)
    (hmp' : (kp * xiw + kw * xip) * mp' = xiw * X' + kw * g')
    (hmw : (kp * xiw + kw * xip) * mw = xip * X - kp * g)
    (hmw' : (kp * xiw + kw * xip) * mw' = xip * X' - kp * g')
    (hq : (kw - kp) * up = lp * kp * p + lw * kw * pw + (X' - X))
    (hcrit : (kw - kp) * (lp * xip * p - lw * xiw * pw) + (xip + xiw) * ((kw - kp) * up) +
      (kw - kp) * (g' - g) = 0) :
    lp * p + mp' - mp + up = 0 ∧ lw * pw + mw' - mw - up = 0 := by
  have hDc : (kp * xiw + kw * xip) * (kw - kp) ≠ 0 := mul_ne_zero hD0 hc0
  have k1 : (kp * xiw + kw * xip) * (kw - kp) * (lp * p + mp' - mp + up) = 0 := by
    linear_combination (kw - kp) * hmp' - (kw - kp) * hmp + kw * hcrit +
      ((kp * xiw + kw * xip) - kw * (xip + xiw)) * hq
  have k2 : (kp * xiw + kw * xip) * (kw - kp) * (lw * pw + mw' - mw - up) = 0 := by
    linear_combination (kw - kp) * hmw' - (kw - kp) * hmw - kp * hcrit +
      (kp * (xip + xiw) - (kp * xiw + kw * xip)) * hq
  exact ⟨(mul_eq_zero.1 k1).resolve_left hDc, (mul_eq_zero.1 k2).resolve_left hDc⟩

/-- Woodford (2003), (2.20): if `q_s = c υ_s` for all `s` and `υ` is adapted, then
`E_s[β q_{s+1} − q_s] = −c (υ_s − β E_s υ_{s+1})`. -/
theorem E_bracket {c β : ℝ} {q ups : ℕ → Ω → ℝ} (hua : 𝔼.Adapted ups)
    (hq : ∀ s, q s = c • ups s) (s : ℕ) (ω : Ω) :
    𝔼.E s (fun ω => β * q (s + 1) ω - q s ω) ω =
      -c * (ups s ω - β * 𝔼.E s (ups (s + 1)) ω) := by
  have : (fun ω => β * q (s + 1) ω - q s ω) = c • (β • ups (s + 1) - ups s) := by
    rw [hq (s + 1), hq s]
    funext ω'; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [this, map_smul, map_sub, map_smul, hua s]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (2.21): `q` of an adapted plan with a date-0 `x_{t₀−1}` is adapted. -/
theorem qSW_adapted (P : SW) {x₀ : Ω → ℝ} (hx₀a : 𝔼.E 0 x₀ = x₀) {π πw x : ℕ → Ω → ℝ}
    (hπ : 𝔼.Adapted π) (hπw : 𝔼.Adapted πw) (hx : 𝔼.Adapted x) :
    𝔼.Adapted (qSW P x₀ π πw x) := by
  intro t
  have : qSW P x₀ π πw x t = (P.lp * P.kp) • π t + (P.lw * P.kw) • πw t +
      P.lx • (x t - lagW x₀ x t) := rfl
  rw [this, map_add, map_add, map_smul, map_smul, map_smul, map_sub, hπ t, hπw t, hx t,
    lagW_adapted 𝔼 hx₀a hx t]

/-- Woodford (2003), (2.21): `q` of a bounded plan with bounded `x_{t₀−1}` is bounded. -/
theorem qSW_bounded (P : SW) {x₀ : Ω → ℝ} {B : ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B)
    {π πw x : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hπw : BoundedProc πw) (hx : BoundedProc x) :
    BoundedProc (qSW P x₀ π πw x) := by
  obtain ⟨A, hA⟩ := hπ
  obtain ⟨C, hC⟩ := hπw
  obtain ⟨X, hX⟩ := hx
  refine ⟨|P.lp * P.kp| * A + |P.lw * P.kw| * C + |P.lx| * (X + max B X), fun t ω => ?_⟩
  simp only [qSW]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA t ω) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC t ω) (abs_nonneg _)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
      (add_le_add (hX t ω) (lagW_bounded hx₀ hX t ω))) (abs_nonneg _)

/-- Woodford (2003), (2.20): a scalar multiple of a bounded adapted process is bounded and
adapted. -/
theorem smul_proc {c : ℝ} {y : ℕ → Ω → ℝ} (ha : 𝔼.Adapted y) (hb : BoundedProc y) :
    𝔼.Adapted (fun t => c • y t) ∧ BoundedProc (fun t => c • y t) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨fun t => by simp only [map_smul, ha t], ⟨|c| * M, fun t ω => ?_⟩⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)

/-- **Woodford (2003), (2.20) corrected (SUFFICIENCY, `κ_w ≠ κ_p`)**: with all of
`κ_p, κ_w, ξ_p, ξ_w` positive and `κ_w ≠ κ_p`, every admissible plan satisfying the corrected
criterion at every date `t > t₀` is optimal from a timeless perspective. The multipliers are
reconstructed from the plan: `υ_t = q_t/(κ_w − κ_p)`, `(φ_{pt}, φ_{wt})` from (2.18)–(2.19) in
levels, and the initial multipliers from (2.16)–(2.17) at `t₀`. -/
theorem criterionC_timeless (hpo : 𝔼.PullOut) (P : SW) (hβ0 : 0 ≤ P.beta) (hβ1 : P.beta < 1)
    (hlp : 0 ≤ P.lp) (hlw : 0 ≤ P.lw) (hlx : 0 ≤ P.lx) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) {B : ℝ} {w₀ x₀ : Ω → ℝ}
    (hx₀a : 𝔼.E 0 x₀ = x₀) (hx₀ : ∀ ω, |x₀ ω| ≤ B) {u wn π πw x w : ℕ → Ω → ℝ}
    (hp : PlanSW 𝔼 P w₀ u wn π πw x w) (hc : CriterionC 𝔼 P x₀ π πw x) :
    TimelessOptimalSW 𝔼 P w₀ u wn π πw x w := by
  have hc0 : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD0 : P.kp * P.xiw + P.kw * P.xip ≠ 0 := by positivity
  have hci : (P.kw - P.kp) * (P.kw - P.kp)⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hDi : (P.kp * P.xiw + P.kw * P.xip) * (P.kp * P.xiw + P.kw * P.xip)⁻¹ = 1 :=
    mul_inv_cancel₀ hD0
  obtain ⟨-, -, -, hπa, hπwa, hxa, -, hπb, hπwb, hxb, -⟩ := id hp
  have hqa := qSW_adapted 𝔼 P hx₀a hπa hπwa hxa
  have hqb := qSW_bounded P hx₀ hπb hπwb hxb
  set q := qSW P x₀ π πw x with hqdef
  set ups : ℕ → Ω → ℝ := fun t => (P.kw - P.kp)⁻¹ • q t with hups
  obtain ⟨hua0, ⟨U, hU0⟩⟩ := smul_proc 𝔼 (c := (P.kw - P.kp)⁻¹) hqa hqb
  have hua : 𝔼.Adapted ups := hua0
  have hU : ∀ t ω, |ups t ω| ≤ U := hU0
  have hq : ∀ s, q s = (P.kw - P.kp) • ups s := fun s => by
    funext ω; simp only [hups, Pi.smul_apply, smul_eq_mul]; rw [← mul_assoc, hci, one_mul]
  set g : ℕ → Ω → ℝ := fun t => ups t - P.beta • 𝔼.E t (ups (t + 1)) with hg
  have hga : 𝔼.Adapted g := fun t => by
    simp only [hg, map_sub, map_smul, 𝔼.E_E_self, hua t]
  have hgb : ∀ t ω, |g t ω| ≤ U + |P.beta| * U := fun t ω => by
    simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hU t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hU (t + 1)) t ω) (abs_nonneg _)
  set X : ℕ → Ω → ℝ := fun t ω => P.lx * (x t ω - P.xstar) with hX
  have hXa : 𝔼.Adapted X := affine_adapted 𝔼 _ _ hxa
  obtain ⟨XB, hXB⟩ := affine_bounded P.lx P.xstar hxb
  set D := P.kp * P.xiw + P.kw * P.xip with hDdef
  set mp : ℕ → Ω → ℝ := fun t => D⁻¹ • (P.xiw • X t + P.kw • g t) with hmp
  set mw : ℕ → Ω → ℝ := fun t => D⁻¹ • (P.xip • X t - P.kp • g t) with hmw
  have hmpa : 𝔼.Adapted mp := fun t => by
    simp only [hmp, map_smul, map_add, hXa t, hga t]
  have hmwa : 𝔼.Adapted mw := fun t => by
    simp only [hmw, map_smul, map_sub, hXa t, hga t]
  have hmpb : BoundedProc mp := ⟨|D⁻¹| * (|P.xiw| * XB + |P.kw| * (U + |P.beta| * U)),
    fun t ω => by
      simp only [hmp, Pi.smul_apply, Pi.add_apply, smul_eq_mul, abs_mul]
      gcongr
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
      · exact hXB t ω
      · exact hgb t ω⟩
  have hmwb : BoundedProc mw := ⟨|D⁻¹| * (|P.xip| * XB + |P.kp| * (U + |P.beta| * U)),
    fun t ω => by
      simp only [hmw, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      gcongr
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
      · exact hXB t ω
      · exact hgb t ω⟩
  obtain ⟨Zp, hZp⟩ := hmpb
  obtain ⟨Zw, hZw⟩ := hmwb
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨C, hC⟩ := hπwb
  have hDmp : ∀ t ω, D * mp t ω = P.xiw * X t ω + P.kw * g t ω := fun t ω => by
    simp only [hmp, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← mul_assoc, hDi, one_mul]
  have hDmw : ∀ t ω, D * mw t ω = P.xip * X t ω - P.kp * g t ω := fun t ω => by
    simp only [hmw, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, hDi, one_mul]
  have hfoc : FOCsw 𝔼 P (fun ω => mp 0 ω + P.lp * π 0 ω + ups 0 ω)
      (fun ω => mw 0 ω + P.lw * πw 0 ω - ups 0 ω) π πw x mp mw ups := by
    intro t ω
    have hD' : D ≠ 0 := hD0
    have e3 : P.lx * (x t ω - P.xstar) - P.kp * mp t ω - P.kw * mw t ω = 0 := by
      have h1 := hDmp t ω
      have h2 := hDmw t ω
      have : D * (P.lx * (x t ω - P.xstar) - P.kp * mp t ω - P.kw * mw t ω) = 0 := by
        simp only [hX] at h1 h2
        rw [hDdef] at h1 h2 ⊢
        linear_combination (-P.kp) * h1 - P.kw * h2
      exact (mul_eq_zero.1 this).resolve_left hD'
    have e4 : ups t ω = P.xip * mp t ω - P.xiw * mw t ω + P.beta * 𝔼.E t (ups (t + 1)) ω := by
      have h1 := hDmp t ω
      have h2 := hDmw t ω
      have : D * (ups t ω - (P.xip * mp t ω - P.xiw * mw t ω +
          P.beta * 𝔼.E t (ups (t + 1)) ω)) = 0 := by
        simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
        rw [hDdef] at h1 h2 ⊢
        linear_combination (-P.xip) * h1 + P.xiw * h2
      linarith [(mul_eq_zero.1 this).resolve_left hD']
    cases t with
    | zero =>
      simp only [lagW_zero]
      exact ⟨by ring, by ring, e3, e4⟩
    | succ t =>
      simp only [lagW_succ]
      have hcr := hc t ω
      simp only [critC] at hcr
      have eb1 := E_bracket 𝔼 (β := P.beta) hua hq (t + 1) ω
      have eb0 := E_bracket 𝔼 (β := P.beta) hua hq t ω
      rw [show t + 1 + 1 = t + 2 from rfl] at eb1
      rw [eb1, eb0] at hcr
      have hq1 := congrFun (hq (t + 1)) ω
      simp only [Pi.smul_apply, smul_eq_mul] at hq1
      have hq1' : qSW P x₀ π πw x (t + 1) ω = (P.kw - P.kp) * ups (t + 1) ω := hq1
      rw [hq1'] at hcr
      have hqq : (P.kw - P.kp) * ups (t + 1) ω = P.lp * P.kp * π (t + 1) ω +
          P.lw * P.kw * πw (t + 1) ω + (X (t + 1) ω - X t ω) := by
        rw [← hq1]; simp only [hqdef, qSW, hX, lagW_succ]; ring
      have hcrit : (P.kw - P.kp) * (P.lp * P.xip * π (t + 1) ω - P.lw * P.xiw * πw (t + 1) ω) +
          (P.xip + P.xiw) * ((P.kw - P.kp) * ups (t + 1) ω) +
          (P.kw - P.kp) * (g (t + 1) ω - g t ω) = 0 := by
        simp only [piAsym] at hcr
        simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          show t + 1 + 1 = t + 2 from rfl]
        linear_combination hcr
      obtain ⟨r1, r2⟩ := elim_alg hD0 hc0 (hDmp t ω) (hDmp (t + 1) ω) (hDmw t ω)
        (hDmw (t + 1) ω) hqq hcrit
      exact ⟨r1, r2, e3, e4⟩
  refine ⟨hp, fun π' πw' x' w' hp' h0 h0w ω => ?_⟩
  refine focSW_sufficient 𝔼 hpo P hβ0 hβ1 hlp hlw hlx hp' hp hmpa hmwa
    ⟨Zp, hZp⟩ ⟨Zw, hZw⟩ ⟨U, hU⟩ ⟨Zp + |P.lp| * A + U, fun ω => ?_⟩
    ⟨Zw + |P.lw| * C + U, fun ω => ?_⟩ hfoc (fun ω => by rw [h0, sub_self, mul_zero])
    (fun ω => by rw [h0w, sub_self, mul_zero]) ω
  · refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hZp 0 ω)
      ?_)) (hU 0 ω))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA 0 ω) (abs_nonneg _)
  · refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hZw 0 ω)
      ?_)) (hU 0 ω))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC 0 ω) (abs_nonneg _)

/-- **Woodford (2003), (2.20) corrected (the multipliers behind the criterion)**: an admissible
plan satisfying the corrected criterion at every date `t > t₀` satisfies the first-order
conditions with bounded adapted multipliers `υ = q/(κ_w − κ_p)`, `φ_p`, `φ_w` (from (2.18)–(2.19)
in levels) and the initial multipliers `φ_{p,t₀−1} = φ_{p,t₀} + λ_p π_{t₀} + υ_{t₀}`,
`φ_{w,t₀−1} = φ_{w,t₀} + λ_w π^w_{t₀} − υ_{t₀}`. -/
theorem criterionC_foc (P : SW) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) {B : ℝ} {w₀ x₀ : Ω → ℝ}
    (hx₀a : 𝔼.E 0 x₀ = x₀) (hx₀ : ∀ ω, |x₀ ω| ≤ B) {u wn π πw x w : ℕ → Ω → ℝ}
    (hp : PlanSW 𝔼 P w₀ u wn π πw x w) (hc : CriterionC 𝔼 P x₀ π πw x) :
    ∃ mp mw ups : ℕ → Ω → ℝ, FOCsw 𝔼 P (fun ω => mp 0 ω + P.lp * π 0 ω + ups 0 ω)
      (fun ω => mw 0 ω + P.lw * πw 0 ω - ups 0 ω) π πw x mp mw ups ∧ 𝔼.Adapted mp ∧
      𝔼.Adapted mw ∧ 𝔼.Adapted ups ∧ BoundedProc ups ∧
      ∀ t ω, (P.kw - P.kp) * ups t ω = qSW P x₀ π πw x t ω := by
  have hc0 : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD0 : P.kp * P.xiw + P.kw * P.xip ≠ 0 := by positivity
  have hci : (P.kw - P.kp) * (P.kw - P.kp)⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hDi : (P.kp * P.xiw + P.kw * P.xip) * (P.kp * P.xiw + P.kw * P.xip)⁻¹ = 1 :=
    mul_inv_cancel₀ hD0
  obtain ⟨-, -, -, hπa, hπwa, hxa, -, hπb, hπwb, hxb, -⟩ := id hp
  have hqa := qSW_adapted 𝔼 P hx₀a hπa hπwa hxa
  have hqb := qSW_bounded P hx₀ hπb hπwb hxb
  set q := qSW P x₀ π πw x with hqdef
  set ups : ℕ → Ω → ℝ := fun t => (P.kw - P.kp)⁻¹ • q t with hups
  obtain ⟨hua0, ⟨U, hU0⟩⟩ := smul_proc 𝔼 (c := (P.kw - P.kp)⁻¹) hqa hqb
  have hua : 𝔼.Adapted ups := hua0
  have hU : ∀ t ω, |ups t ω| ≤ U := hU0
  have hq : ∀ s, q s = (P.kw - P.kp) • ups s := fun s => by
    funext ω; simp only [hups, Pi.smul_apply, smul_eq_mul]; rw [← mul_assoc, hci, one_mul]
  set g : ℕ → Ω → ℝ := fun t => ups t - P.beta • 𝔼.E t (ups (t + 1)) with hg
  have hga : 𝔼.Adapted g := fun t => by
    simp only [hg, map_sub, map_smul, 𝔼.E_E_self, hua t]
  have hgb : ∀ t ω, |g t ω| ≤ U + |P.beta| * U := fun t ω => by
    simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hU t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hU (t + 1)) t ω) (abs_nonneg _)
  set X : ℕ → Ω → ℝ := fun t ω => P.lx * (x t ω - P.xstar) with hX
  have hXa : 𝔼.Adapted X := affine_adapted 𝔼 _ _ hxa
  obtain ⟨XB, hXB⟩ := affine_bounded P.lx P.xstar hxb
  set D := P.kp * P.xiw + P.kw * P.xip with hDdef
  set mp : ℕ → Ω → ℝ := fun t => D⁻¹ • (P.xiw • X t + P.kw • g t) with hmp
  set mw : ℕ → Ω → ℝ := fun t => D⁻¹ • (P.xip • X t - P.kp • g t) with hmw
  have hmpa : 𝔼.Adapted mp := fun t => by
    simp only [hmp, map_smul, map_add, hXa t, hga t]
  have hmwa : 𝔼.Adapted mw := fun t => by
    simp only [hmw, map_smul, map_sub, hXa t, hga t]
  have hmpb : BoundedProc mp := ⟨|D⁻¹| * (|P.xiw| * XB + |P.kw| * (U + |P.beta| * U)),
    fun t ω => by
      simp only [hmp, Pi.smul_apply, Pi.add_apply, smul_eq_mul, abs_mul]
      gcongr
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
      · exact hXB t ω
      · exact hgb t ω⟩
  have hmwb : BoundedProc mw := ⟨|D⁻¹| * (|P.xip| * XB + |P.kp| * (U + |P.beta| * U)),
    fun t ω => by
      simp only [hmw, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      gcongr
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
      · exact hXB t ω
      · exact hgb t ω⟩
  obtain ⟨Zp, hZp⟩ := hmpb
  obtain ⟨Zw, hZw⟩ := hmwb
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨C, hC⟩ := hπwb
  have hDmp : ∀ t ω, D * mp t ω = P.xiw * X t ω + P.kw * g t ω := fun t ω => by
    simp only [hmp, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← mul_assoc, hDi, one_mul]
  have hDmw : ∀ t ω, D * mw t ω = P.xip * X t ω - P.kp * g t ω := fun t ω => by
    simp only [hmw, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← mul_assoc, hDi, one_mul]
  have hfoc : FOCsw 𝔼 P (fun ω => mp 0 ω + P.lp * π 0 ω + ups 0 ω)
      (fun ω => mw 0 ω + P.lw * πw 0 ω - ups 0 ω) π πw x mp mw ups := by
    intro t ω
    have hD' : D ≠ 0 := hD0
    have e3 : P.lx * (x t ω - P.xstar) - P.kp * mp t ω - P.kw * mw t ω = 0 := by
      have h1 := hDmp t ω
      have h2 := hDmw t ω
      have : D * (P.lx * (x t ω - P.xstar) - P.kp * mp t ω - P.kw * mw t ω) = 0 := by
        simp only [hX] at h1 h2
        rw [hDdef] at h1 h2 ⊢
        linear_combination (-P.kp) * h1 - P.kw * h2
      exact (mul_eq_zero.1 this).resolve_left hD'
    have e4 : ups t ω = P.xip * mp t ω - P.xiw * mw t ω + P.beta * 𝔼.E t (ups (t + 1)) ω := by
      have h1 := hDmp t ω
      have h2 := hDmw t ω
      have : D * (ups t ω - (P.xip * mp t ω - P.xiw * mw t ω +
          P.beta * 𝔼.E t (ups (t + 1)) ω)) = 0 := by
        simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
        rw [hDdef] at h1 h2 ⊢
        linear_combination (-P.xip) * h1 + P.xiw * h2
      linarith [(mul_eq_zero.1 this).resolve_left hD']
    cases t with
    | zero =>
      simp only [lagW_zero]
      exact ⟨by ring, by ring, e3, e4⟩
    | succ t =>
      simp only [lagW_succ]
      have hcr := hc t ω
      simp only [critC] at hcr
      have eb1 := E_bracket 𝔼 (β := P.beta) hua hq (t + 1) ω
      have eb0 := E_bracket 𝔼 (β := P.beta) hua hq t ω
      rw [show t + 1 + 1 = t + 2 from rfl] at eb1
      rw [eb1, eb0] at hcr
      have hq1 := congrFun (hq (t + 1)) ω
      simp only [Pi.smul_apply, smul_eq_mul] at hq1
      have hq1' : qSW P x₀ π πw x (t + 1) ω = (P.kw - P.kp) * ups (t + 1) ω := hq1
      rw [hq1'] at hcr
      have hqq : (P.kw - P.kp) * ups (t + 1) ω = P.lp * P.kp * π (t + 1) ω +
          P.lw * P.kw * πw (t + 1) ω + (X (t + 1) ω - X t ω) := by
        rw [← hq1]; simp only [hqdef, qSW, hX, lagW_succ]; ring
      have hcrit : (P.kw - P.kp) * (P.lp * P.xip * π (t + 1) ω - P.lw * P.xiw * πw (t + 1) ω) +
          (P.xip + P.xiw) * ((P.kw - P.kp) * ups (t + 1) ω) +
          (P.kw - P.kp) * (g (t + 1) ω - g t ω) = 0 := by
        simp only [piAsym] at hcr
        simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          show t + 1 + 1 = t + 2 from rfl]
        linear_combination hcr
      obtain ⟨r1, r2⟩ := elim_alg hD0 hc0 (hDmp t ω) (hDmp (t + 1) ω) (hDmw t ω)
        (hDmw (t + 1) ω) hqq hcrit
      exact ⟨r1, r2, e3, e4⟩
  refine ⟨mp, mw, ups, hfoc, hmpa, hmwa, hua, ⟨U, hU⟩, fun t ω => ?_⟩
  have := congrFun (hq t) ω
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

/-! ### The case `κ_w = κ_p`: the criterion (2.22) -/

/-- Woodford (2003), (2.22), p. 567: `π^sym_t + λ_x/(λ_p κ_p + λ_w κ_w) (x_t − x_{t−1}) = 0` at
every date `t ≥ t₀` (i.e. `q_t = 0`; with fn. 20's `λ_p + λ_w = 1` and `κ_p = κ_w = κ` the
coefficient is `φ = λ_x/κ`, `phi_normalized`). -/
def Criterion222 (P : SW) (x₀ : Ω → ℝ) (π πw x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, piSym P π πw t ω + P.lx / (P.lp * P.kp + P.lw * P.kw) * (x t ω - lagW x₀ x t ω) = 0

/-- Woodford (2003), (2.21)–(2.22): the criterion (2.22) is `q_t = 0`. -/
theorem criterion222_iff_q (P : SW) (h : P.lp * P.kp + P.lw * P.kw ≠ 0) (x₀ : Ω → ℝ)
    (π πw x : ℕ → Ω → ℝ) : Criterion222 P x₀ π πw x ↔ ∀ t ω, qSW P x₀ π πw x t ω = 0 := by
  constructor
  · intro hc t ω
    rw [q_eq_sym P h, hc t ω, mul_zero]
  · intro hq t ω
    have := hq t ω
    rw [q_eq_sym P h] at this
    exact (mul_eq_zero.1 this).resolve_left h

/-- **Woodford (2003), (2.22) and fn. 20, p. 567**: with `κ_p = κ_w = κ` and the normalisation
`λ_p + λ_w = 1`, the coefficient in (2.22) is `φ = λ_x/κ`, as in the sticky-price case. -/
theorem phi_normalized (P : SW) (hk : P.kw = P.kp) (hl : P.lp + P.lw = 1) :
    P.lx / (P.lp * P.kp + P.lw * P.kw) = P.lx / P.kp := by
  rw [hk, ← add_mul, hl, one_mul]

/-- **Woodford (2003), p. 567 ("in the special case `κ_w = κ_p` … (2.20) reduces simply to
`q_t = 0`")**: with `κ_w = κ_p` the first-order conditions give `q_t = 0` at every date
`t > t₀` (and at `t₀` for self-consistent initial multipliers): the optimal plan satisfies
(2.22). -/
theorem foc_q_zero {P : SW} (hk : P.kw = P.kp) {mp₀ mw₀ x₀ : Ω → ℝ}
    {π πw x mp mw ups : ℕ → Ω → ℝ} (hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups) :
    (∀ t ω, qSW P x₀ π πw x (t + 1) ω = 0) ∧
    ((∀ ω, P.lx * (x₀ ω - P.xstar) - P.kp * mp₀ ω - P.kw * mw₀ ω = 0) →
      ∀ t ω, qSW P x₀ π πw x t ω = 0) := by
  obtain ⟨h1, h2⟩ := foc_q_eq 𝔼 (x₀ := x₀) hfoc
  refine ⟨fun t ω => by rw [h1 t ω, hk, sub_self, zero_mul], fun hsc t ω => ?_⟩
  rw [h2 hsc t ω, hk, sub_self, zero_mul]

/-- **Woodford (2003), (2.20) with `κ_w = κ_p` (imprecision)**: with `κ_w = κ_p` the CORRECTED
criterion does not reduce to `q_t = 0` by itself: under perfect foresight the plan `π = π^w = 0`,
`x_t = (1 − μ^{t+1})/((1 − μ) λ_x)` (`x_{t₀−1} = 0`, `μ = μ₁` the stable root for
`c = ξ_p + ξ_w`) is bounded, satisfies the corrected (2.20) at every date and has `q_t = μᵗ ≠ 0`.
(The printed (2.20) does reduce to `(ξ_p + ξ_w) q_t = 0`; for the optimal plan `q = 0` follows
from `q_t = (κ_w − κ_p) υ_t`, `foc_q_zero`.) -/
theorem corrected_criterion_kappa_eq (P : SW) (hk : P.kw = P.kp) (hβ0 : 0 < P.beta)
    (hc : 0 < P.xip + P.xiw) (hlx : P.lx ≠ 0) :
    let μ := lam1 P.beta (P.xip + P.xiw)
    let x : ℕ → Unit → ℝ := fun t _ => (1 - μ ^ (t + 1)) / ((1 - μ) * P.lx)
    BoundedProc x ∧ CriterionC perfectForesight P (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) x ∧
      ∀ t, qSW P (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) x t () = μ ^ t := by
  intro μ x
  have hμ0 : 0 < μ := lam1_pos hβ0 hc
  have hμ1 : μ < 1 := lam1_lt_one hβ0 hc
  have hroot : P.beta * μ ^ 2 - (1 + P.beta + (P.xip + P.xiw)) * μ + 1 = 0 := lam1_root hβ0 hc
  have h1μ : 1 - μ ≠ 0 := (sub_pos.2 hμ1).ne'
  have hq : ∀ t, qSW P (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) x t () = μ ^ t := by
    intro t
    cases t with
    | zero =>
      simp only [qSW, lagW_zero, x]
      field_simp
      ring
    | succ t =>
      simp only [qSW, lagW_succ, x]
      field_simp
      ring
  refine ⟨⟨2 / ((1 - μ) * |P.lx|), fun t ω => ?_⟩, fun t ω => ?_, hq⟩
  · simp only [x]
    rw [abs_div, abs_mul, abs_of_pos (sub_pos.2 hμ1)]
    gcongr
    have h1 : 0 < μ ^ (t + 1) := pow_pos hμ0 _
    have h2 : μ ^ (t + 1) ≤ 1 := pow_le_one₀ hμ0.le hμ1.le
    rw [abs_le]
    constructor <;> linarith
  · cases ω
    have e1 : ∀ s, (fun ω => P.beta * qSW P (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) x
        (s + 1) ω - qSW P (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) x s ω) =
        fun _ => P.beta * μ ^ (s + 1) - μ ^ s := fun s => by
      funext ω; cases ω; rw [hq, hq]
    simp only [critC, piAsym, hk, sub_self, mul_zero, zero_add]
    rw [show t + 2 = t + 1 + 1 from rfl, e1 (t + 1), e1 t, hq (t + 1)]
    change (P.xip + P.xiw) * μ ^ (t + 1) - ((P.beta * μ ^ (t + 1 + 1) - μ ^ (t + 1)) -
      (P.beta * μ ^ (t + 1) - μ ^ t)) = 0
    linear_combination (-(μ ^ t)) * hroot

/-- **Woodford (2003), fn. 19, p. 567 (with `κ_w = κ_p` the real wage is exogenous)**: in any
admissible plan, `w` solves `β E_t w_{t+1} − (1 + β + ξ_p + ξ_w) w_t + w_{t−1} =
−(ξ_p + ξ_w) w^n_t`, which does not involve policy. -/
theorem wageEq_secondOrder {P : SW} (hk : P.kw = P.kp) {w₀ : Ω → ℝ}
    {u wn π πw x w : ℕ → Ω → ℝ} (hpe : PriceEq 𝔼 P u wn π x w) (hwe : WageEq 𝔼 P u wn πw x w)
    (hwi : WageId w₀ π πw w) (hwa : 𝔼.Adapted w) :
    SecondOrder 𝔼 P.beta (P.xip + P.xiw) w₀ (fun t => (-(P.xip + P.xiw)) • wn t) w := by
  intro t ω
  have hE : 𝔼.E t (π (t + 1)) ω - 𝔼.E t (πw (t + 1)) ω = w t ω - 𝔼.E t (w (t + 1)) ω := by
    have : π (t + 1) - πw (t + 1) = w t - w (t + 1) := by
      funext ω'
      have := hwi (t + 1) ω'
      simp only [lagW_succ] at this
      simp only [Pi.sub_apply]
      linarith
    rw [← Pi.sub_apply, ← map_sub, this, map_sub, hwa t]
    rfl
  have h1 := hpe t ω
  have h2 := hwe t ω
  have h3 := hwi t ω
  rw [hk] at h2
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination h1 - h2 - h3 + P.beta * hE

/-- Woodford (2003), (2.22): the weighted average `s_t = (λ_p π_t + λ_w π^w_t)/(λ_p + λ_w)`
(equal to `π^sym_t` when `κ_p = κ_w`). -/
noncomputable def sAvg (P : SW) (π πw : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (P.lp * π t ω + P.lw * πw t ω) / (P.lp + P.lw)

/-- Woodford (2003), p. 566: with `κ_p = κ_w ≠ 0`, `π^sym_t = s_t`. -/
theorem piSym_eq_sAvg {P : SW} (hk : P.kw = P.kp) (hkp : P.kp ≠ 0)
    (π πw : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : piSym P π πw t ω = sAvg P π πw t ω := by
  simp only [piSym, sAvg, hk]
  rw [show P.lp * P.kp * π t ω + P.lw * P.kp * πw t ω = P.kp * (P.lp * π t ω + P.lw * πw t ω)
    by ring, show P.lp * P.kp + P.lw * P.kp = P.kp * (P.lp + P.lw) by ring,
    mul_div_mul_left _ _ hkp]

/-- **Woodford (2003), (2.11)–(2.12) with `κ_p = κ_w = κ`**: the weighted average `s` obeys the
aggregate-supply relation (2.1) with the cost-push term
`κ u_t + ((λ_p ξ_p − λ_w ξ_w)/(λ_p + λ_w)) (w_t − w^n_t)`. -/
theorem sAvg_AS {P : SW} (hk : P.kw = P.kp) (hS : P.lp + P.lw ≠ 0)
    {u wn π πw x w : ℕ → Ω → ℝ} (hpe : PriceEq 𝔼 P u wn π x w) (hwe : WageEq 𝔼 P u wn πw x w) :
    AS 𝔼 P.beta P.kp (fun t ω => P.kp * u t ω +
      (P.lp * P.xip - P.lw * P.xiw) / (P.lp + P.lw) * (w t ω - wn t ω)) (sAvg P π πw) x := by
  intro t ω
  have hE : 𝔼.E t (sAvg P π πw (t + 1)) ω =
      (P.lp * 𝔼.E t (π (t + 1)) ω + P.lw * 𝔼.E t (πw (t + 1)) ω) / (P.lp + P.lw) := by
    have : sAvg P π πw (t + 1) = (P.lp + P.lw)⁻¹ • (P.lp • π (t + 1) + P.lw • πw (t + 1)) := by
      funext ω'; simp only [sAvg, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    rw [this, map_smul, map_add, map_smul, map_smul]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have h1 := hpe t ω
  have h2 := hwe t ω
  rw [hk] at h2
  rw [hE]
  simp only [sAvg]
  field_simp
  linear_combination P.lp * h1 + P.lw * h2

/-- **Woodford (2003), (2.15) with `κ_p = κ_w`**: the period loss splits as
`(λ_p + λ_w)[s_t² + (λ_x/(λ_p + λ_w))(x_t − x*)²] + (λ_p λ_w/(λ_p + λ_w))(π_t − π^w_t)²`. -/
theorem lossSW_split (P : SW) (hS : P.lp + P.lw ≠ 0) (π πw x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lossSW P π πw x t ω = (P.lp + P.lw) *
        periodLoss (P.lx / (P.lp + P.lw)) P.xstar (sAvg P π πw) x t ω +
      P.lp * P.lw / (P.lp + P.lw) * (π t ω - πw t ω) ^ 2 := by
  simp only [lossSW, periodLoss, sAvg]
  field_simp
  ring

/-- Woodford (2003), (2.2): the expected loss is linear, `E_0 ∑ βᵗ (a ℓ¹_t + ℓ²_t) =
a E_0 ∑ βᵗ ℓ¹_t + E_0 ∑ βᵗ ℓ²_t`, for bounded period losses. -/
theorem expLossOf_add {β a L₁ L₂ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ₁ ℓ₂ : ℕ → Ω → ℝ}
    (h₁ : ∀ t ω, |ℓ₁ t ω| ≤ L₁) (h₂ : ∀ t ω, |ℓ₂ t ω| ≤ L₂) (ω : Ω) :
    expLossOf 𝔼 β (fun t ω => a * ℓ₁ t ω + ℓ₂ t ω) ω =
      a * expLossOf 𝔼 β ℓ₁ ω + expLossOf 𝔼 β ℓ₂ ω := by
  have h : ∀ t ω, |a * ℓ₁ t ω + ℓ₂ t ω| ≤ |a| * L₁ + L₂ := fun t ω => by
    refine (abs_add_le _ _).trans (add_le_add ?_ (h₂ t ω))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₁ t ω) (abs_nonneg a)
  have hs := expLossOf_hasSum 𝔼 hβ0 hβ1 h ω
  have hs' := ((expLossOf_hasSum 𝔼 hβ0 hβ1 h₁ ω).mul_left a).add
    (expLossOf_hasSum 𝔼 hβ0 hβ1 h₂ ω)
  refine hs.unique (hs'.congr_fun fun t => ?_)
  have : (fun ω => a * ℓ₁ t ω + ℓ₂ t ω) = a • ℓ₁ t + ℓ₂ t := rfl
  rw [this, map_add, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (2.13): `π_t − π^w_t = w_{t−1} − w_t`. -/
theorem infl_diff_of_wageId {w₀ : Ω → ℝ} {π πw w : ℕ → Ω → ℝ} (h : WageId w₀ π πw w)
    (t : ℕ) (ω : Ω) : π t ω - πw t ω = lagW w₀ w t ω - w t ω := by
  have := h t ω; linarith

/-- **Woodford (2003), fn. 19, p. 567**: with `κ_w = κ_p` (and `ξ_p + ξ_w > 0`, bounded adapted
`w^n`, a bounded date-0 `w_{t₀−1}`), every admissible plan has the same real wage — monetary
policy cannot affect it. -/
theorem wage_unique {P : SW} (hk : P.kw = P.kp) (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hc : 0 < P.xip + P.xiw) {N B : ℝ} {wn : ℕ → Ω → ℝ} (hwn : ∀ t ω, |wn t ω| ≤ N)
    (hwna : 𝔼.Adapted wn) {w₀ : Ω → ℝ} (hw₀ : ∀ ω, |w₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀)
    {u π πw x w : ℕ → Ω → ℝ} (hp : PlanSW 𝔼 P w₀ u wn π πw x w) :
    w = ysol 𝔼 P.beta (P.xip + P.xiw) w₀ (fun t => (-(P.xip + P.xiw)) • wn t) := by
  have hf : ∀ t ω, |(fun t => (-(P.xip + P.xiw)) • wn t) t ω| ≤ (P.xip + P.xiw) * N :=
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (hwn t ω) hc.le
  have hfa : 𝔼.Adapted (fun t => (-(P.xip + P.xiw)) • wn t) := fun t => by
    simp only [map_smul, hwna t]
  exact (secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hf hfa hw₀ hw₀a).2 w
    (wageEq_secondOrder 𝔼 hk hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.2.1) hp.2.2.2.2.2.2.1
    hp.2.2.2.2.2.2.2.2.2.2

/-- Woodford (2003), (2.22): `s` of an admissible plan is adapted and bounded. -/
theorem sAvg_adapted_bounded (P : SW) {π πw : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π)
    (hπwa : 𝔼.Adapted πw) (hπb : BoundedProc π) (hπwb : BoundedProc πw) :
    𝔼.Adapted (sAvg P π πw) ∧ BoundedProc (sAvg P π πw) := by
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨C, hC⟩ := hπwb
  refine ⟨fun t => ?_, ⟨|(P.lp + P.lw)⁻¹| * (|P.lp| * A + |P.lw| * C), fun t ω => ?_⟩⟩
  · have : sAvg P π πw t = (P.lp + P.lw)⁻¹ • (P.lp • π t + P.lw • πw t) := by
      funext ω; simp only [sAvg, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    rw [this, map_smul, map_add, map_smul, map_smul, hπa t, hπwa t]
  · have : sAvg P π πw t ω = (P.lp + P.lw)⁻¹ * (P.lp * π t ω + P.lw * πw t ω) := by
      simp only [sAvg]; ring
    rw [this, abs_mul]
    gcongr
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
    · exact hA t ω
    · exact hC t ω

/-- Woodford (2003), (2.22): the cost-push term of the reduced problem,
`κ u_t + ((λ_p ξ_p − λ_w ξ_w)/(λ_p + λ_w))(w_t − w^n_t)`. -/
noncomputable def usSym (P : SW) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => P.kp * u t ω + (P.lp * P.xip - P.lw * P.xiw) / (P.lp + P.lw) * (w t ω - wn t ω)

/-- Woodford (2003), (2.22): with `κ_p = κ_w = κ`, (2.22) is the baseline criterion (2.5) for `s`
with `φ = (λ_x/(λ_p + λ_w))/κ`. -/
theorem criterion222_iff_base {P : SW} (hk : P.kw = P.kp) (hkp : P.kp ≠ 0) (x₀ : Ω → ℝ)
    (π πw x : ℕ → Ω → ℝ) :
    Criterion222 P x₀ π πw x ↔
      Criterion (P.lx / (P.lp + P.lw) / P.kp) x₀ (sAvg P π πw) x := by
  have hco : P.lx / (P.lp * P.kp + P.lw * P.kw) = P.lx / (P.lp + P.lw) / P.kp := by
    rw [hk, div_div, show P.lp * P.kp + P.lw * P.kp = (P.lp + P.lw) * P.kp by ring]
  simp only [Criterion222, Criterion, hco, piSym_eq_sAvg hk hkp]

/-- **Woodford (2003), (2.22), pp. 566–567 (optimality, `κ_w = κ_p`)**: every admissible plan
satisfying (2.22) is optimal from a timeless perspective. The real wage, hence `π_t − π^w_t`, is
the same in every admissible plan; the loss is `(λ_p + λ_w)` times the baseline loss in
`(s, x)` plus a policy-independent term; and (2.22) is the baseline criterion for `s`. -/
theorem sym_timeless (hpo : 𝔼.PullOut) {P : SW} (hk : P.kw = P.kp) (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hlx : 0 ≤ P.lx) (hkp : 0 < P.kp)
    (hc : 0 < P.xip + P.xiw) {N B Bx : ℝ} {wn : ℕ → Ω → ℝ} (hwn : ∀ t ω, |wn t ω| ≤ N)
    (hwna : 𝔼.Adapted wn) {w₀ x₀ : Ω → ℝ} (hw₀ : ∀ ω, |w₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀)
    (hx₀ : ∀ ω, |x₀ ω| ≤ Bx) {u π πw x w : ℕ → Ω → ℝ} (hp : PlanSW 𝔼 P w₀ u wn π πw x w)
    (hcr : Criterion222 P x₀ π πw x) : TimelessOptimalSW 𝔼 P w₀ u wn π πw x w := by
  have hS : 0 < P.lp + P.lw := by linarith
  refine ⟨hp, fun π' πw' x' w' hp' h0 h0w ω => ?_⟩
  have hw := wage_unique 𝔼 hk hβ0 hβ1 hc hwn hwna hw₀ hw₀a hp
  have hw' := wage_unique 𝔼 hk hβ0 hβ1 hc hwn hwna hw₀ hw₀a hp'
  rw [← hw] at hw'
  obtain ⟨hpe, hwe, hwi, hπa, hπwa, hxa, -, hπb, hπwb, hxb, -⟩ := hp
  obtain ⟨hpe', hwe', hwi', hπa', hπwa', hxa', -, hπb', hπwb', hxb', -⟩ := hp'
  obtain ⟨hsa, hsb⟩ := sAvg_adapted_bounded 𝔼 P hπa hπwa hπb hπwb
  obtain ⟨hsa', hsb'⟩ := sAvg_adapted_bounded 𝔼 P hπa' hπwa' hπb' hπwb'
  have hAS := sAvg_AS 𝔼 hk hS.ne' hpe hwe
  have hAS' := sAvg_AS 𝔼 hk hS.ne' hpe' hwe'
  rw [hw'] at hAS'
  have hbase : Plan 𝔼 P.beta P.kp (usSym P u wn w) (sAvg P π πw) x :=
    ⟨hAS, hsa, hxa, hsb, hxb⟩
  have hbase' : Plan 𝔼 P.beta P.kp (usSym P u wn w) (sAvg P π' πw') x' :=
    ⟨hAS', hsa', hxa', hsb', hxb'⟩
  have hcrit := (criterion222_iff_base hk hkp.ne' x₀ π πw x).1 hcr
  have hT := criterion_timeless 𝔼 hpo (xstar := P.xstar) hβ0.le hβ1
    (div_nonneg hlx hS.le) hkp.ne' ⟨Bx, hx₀⟩ hbase hcrit
  have h00 : sAvg P π' πw' 0 = sAvg P π πw 0 := by
    funext ω'; simp only [sAvg, h0, h0w]
  have hle := hT.2 _ _ hbase' h00 ω
  -- the loss decomposition
  obtain ⟨L1, hL1⟩ := periodLoss_bounded (xstar := P.xstar) (div_nonneg hlx hS.le) hsb hxb
  obtain ⟨L1', hL1'⟩ := periodLoss_bounded (xstar := P.xstar) (div_nonneg hlx hS.le) hsb' hxb'
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨C, hC⟩ := hπwb
  have hK : ∀ t ω, |P.lp * P.lw / (P.lp + P.lw) * (π t ω - πw t ω) ^ 2| ≤
      |P.lp * P.lw / (P.lp + P.lw)| * (A + C) ^ 2 := fun t ω => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (sq_bound ((abs_sub _ _).trans
      (add_le_add (hA t ω) (hC t ω)))) (abs_nonneg _)
  have hD : ∀ t ω, π' t ω - πw' t ω = π t ω - πw t ω := fun t ω => by
    rw [infl_diff_of_wageId hwi' t ω, infl_diff_of_wageId hwi t ω, hw']
  have e1 : lossSW P π πw x = fun t ω => (P.lp + P.lw) *
      periodLoss (P.lx / (P.lp + P.lw)) P.xstar (sAvg P π πw) x t ω +
      P.lp * P.lw / (P.lp + P.lw) * (π t ω - πw t ω) ^ 2 := by
    funext t ω; exact lossSW_split P hS.ne' π πw x t ω
  have e2 : lossSW P π' πw' x' = fun t ω => (P.lp + P.lw) *
      periodLoss (P.lx / (P.lp + P.lw)) P.xstar (sAvg P π' πw') x' t ω +
      P.lp * P.lw / (P.lp + P.lw) * (π t ω - πw t ω) ^ 2 := by
    funext t ω; rw [lossSW_split P hS.ne' π' πw' x' t ω, hD]
  rw [e1, e2, expLossOf_add 𝔼 hβ0.le hβ1 hL1 hK, expLossOf_add 𝔼 hβ0.le hβ1 hL1' hK]
  gcongr

/-- Woodford (2003), (2.22): the equilibrium real wage, `w = ysol` of the wage equation. -/
noncomputable def wSym (P : SW) (w₀ : Ω → ℝ) (wn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ysol 𝔼 P.beta (P.xip + P.xiw) w₀ (fun t => (-(P.xip + P.xiw)) • wn t)

/-- Woodford (2003), (2.22): the equilibrium output gap under (2.22). -/
noncomputable def gapSym (P : SW) (w₀ x₀ : Ω → ℝ) (u wn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  gapR 𝔼 P.beta P.kp (P.lx / (P.lp + P.lw) / P.kp) x₀ (usSym P u wn (wSym 𝔼 P w₀ wn))

/-- Woodford (2003), (2.22): the equilibrium weighted inflation `s` under (2.22). -/
noncomputable def sSym (P : SW) (w₀ x₀ : Ω → ℝ) (u wn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  inflR 𝔼 P.beta P.kp (P.lx / (P.lp + P.lw) / P.kp) x₀ (usSym P u wn (wSym 𝔼 P w₀ wn))

/-- Woodford (2003), (2.22): equilibrium price inflation,
`π_t = s_t + (λ_w/(λ_p + λ_w))(w_{t−1} − w_t)`. -/
noncomputable def inflSym (P : SW) (w₀ x₀ : Ω → ℝ) (u wn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => sSym 𝔼 P w₀ x₀ u wn t ω + P.lw / (P.lp + P.lw) *
    (lagW w₀ (wSym 𝔼 P w₀ wn) t ω - wSym 𝔼 P w₀ wn t ω)

/-- Woodford (2003), (2.22): equilibrium wage inflation,
`π^w_t = s_t − (λ_p/(λ_p + λ_w))(w_{t−1} − w_t)`. -/
noncomputable def wageInflSym (P : SW) (w₀ x₀ : Ω → ℝ) (u wn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => sSym 𝔼 P w₀ x₀ u wn t ω - P.lp / (P.lp + P.lw) *
    (lagW w₀ (wSym 𝔼 P w₀ wn) t ω - wSym 𝔼 P w₀ wn t ω)

/-- **Woodford (2003), (2.22) (determinacy, `κ_w = κ_p`)**: for bounded adapted disturbances
`u, w^n` and bounded date-0 `w_{t₀−1}, x_{t₀−1}`, (2.11)–(2.13) and (2.22) have exactly one
bounded adapted solution, `(inflSym, wageInflSym, gapSym, wSym)`. -/
theorem sym_existsUnique {P : SW} (hk : P.kw = P.kp) (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hlx : 0 < P.lx) (hkp : 0 < P.kp)
    (hc : 0 < P.xip + P.xiw) {M N B Bx : ℝ} {u wn : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) (hwn : ∀ t ω, |wn t ω| ≤ N) (hwna : 𝔼.Adapted wn) {w₀ x₀ : Ω → ℝ}
    (hw₀ : ∀ ω, |w₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀) (hx₀ : ∀ ω, |x₀ ω| ≤ Bx)
    (hx₀a : 𝔼.E 0 x₀ = x₀) :
    (PlanSW 𝔼 P w₀ u wn (inflSym 𝔼 P w₀ x₀ u wn) (wageInflSym 𝔼 P w₀ x₀ u wn)
        (gapSym 𝔼 P w₀ x₀ u wn) (wSym 𝔼 P w₀ wn) ∧
      Criterion222 P x₀ (inflSym 𝔼 P w₀ x₀ u wn) (wageInflSym 𝔼 P w₀ x₀ u wn)
        (gapSym 𝔼 P w₀ x₀ u wn)) ∧
    ∀ π πw x w, PlanSW 𝔼 P w₀ u wn π πw x w → Criterion222 P x₀ π πw x →
      π = inflSym 𝔼 P w₀ x₀ u wn ∧ πw = wageInflSym 𝔼 P w₀ x₀ u wn ∧
        x = gapSym 𝔼 P w₀ x₀ u wn ∧ w = wSym 𝔼 P w₀ wn := by
  have hS : 0 < P.lp + P.lw := by linarith
  have hSi : (P.lp + P.lw) * (P.lp + P.lw)⁻¹ = 1 := mul_inv_cancel₀ hS.ne'
  set c := P.xip + P.xiw with hcdef
  -- the real wage
  have hf : ∀ t ω, |(fun t => (-c) • wn t) t ω| ≤ c * N := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hwn t ω) hc.le
  have hfa : 𝔼.Adapted (fun t => (-c) • wn t) := fun t => by simp only [map_smul, hwna t]
  obtain ⟨⟨hSO, hwa0, ⟨W, hW0⟩⟩, -⟩ := secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hf hfa hw₀ hw₀a
  set wS := wSym 𝔼 P w₀ wn with hwS
  have hwa : 𝔼.Adapted wS := hwa0
  have hW : ∀ t ω, |wS t ω| ≤ W := hW0
  have hSO' : SecondOrder 𝔼 P.beta c w₀ (fun t => (-c) • wn t) wS := hSO
  -- the reduced disturbance
  set us := usSym P u wn wS with hus
  have husb : ∀ t ω, |us t ω| ≤ |P.kp| * M +
      |(P.lp * P.xip - P.lw * P.xiw) / (P.lp + P.lw)| * (W + N) := fun t ω => by
    simp only [hus, usSym]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
    · exact hu t ω
    · exact (abs_sub _ _).trans (add_le_add (hW t ω) (hwn t ω))
  have husa : 𝔼.Adapted us := fun t => by
    have : us t = P.kp • u t + ((P.lp * P.xip - P.lw * P.xiw) / (P.lp + P.lw)) •
        (wS t - wn t) := rfl
    rw [this, map_add, map_smul, map_smul, map_sub, hua t, hwa t, hwna t]
  have hφ : 0 < P.lx / (P.lp + P.lw) / P.kp := by positivity
  obtain ⟨⟨hR, hRc⟩, hRu⟩ := ruleEq_existsUnique 𝔼 hβ0 hβ1 hkp hφ husb husa hx₀ hx₀a
  obtain ⟨hRAS, hsa, hxa, ⟨Sb, hSb⟩, hxb⟩ := hR
  have hla := lagW_adapted 𝔼 hw₀a hwa
  have hsS : 𝔼.Adapted (sSym 𝔼 P w₀ x₀ u wn) := hsa
  -- E of the wage difference
  have hED : ∀ t ω, 𝔼.E t (fun ω => lagW w₀ wS (t + 1) ω - wS (t + 1) ω) ω =
      wS t ω - 𝔼.E t (wS (t + 1)) ω := fun t ω => by
    have : (fun ω => lagW w₀ wS (t + 1) ω - wS (t + 1) ω) = wS t - wS (t + 1) := rfl
    rw [this, map_sub, hwa t]
    rfl
  have hEinfl : ∀ (a : ℝ) t ω, 𝔼.E t (fun ω => sSym 𝔼 P w₀ x₀ u wn (t + 1) ω +
      a * (lagW w₀ wS (t + 1) ω - wS (t + 1) ω)) ω =
      𝔼.E t (sSym 𝔼 P w₀ x₀ u wn (t + 1)) ω + a * (wS t ω - 𝔼.E t (wS (t + 1)) ω) := by
    intro a t ω
    have : (fun ω => sSym 𝔼 P w₀ x₀ u wn (t + 1) ω + a * (lagW w₀ wS (t + 1) ω -
        wS (t + 1) ω)) = sSym 𝔼 P w₀ x₀ u wn (t + 1) + a • (wS t - wS (t + 1)) := rfl
    rw [this, map_add, map_smul, map_sub, hwa t]
    rfl
  have hEinflm : ∀ (a : ℝ) t ω, 𝔼.E t (fun ω => sSym 𝔼 P w₀ x₀ u wn (t + 1) ω -
      a * (lagW w₀ wS (t + 1) ω - wS (t + 1) ω)) ω =
      𝔼.E t (sSym 𝔼 P w₀ x₀ u wn (t + 1)) ω - a * (wS t ω - 𝔼.E t (wS (t + 1)) ω) := by
    intro a t ω
    have : (fun ω => sSym 𝔼 P w₀ x₀ u wn (t + 1) ω - a * (lagW w₀ wS (t + 1) ω -
        wS (t + 1) ω)) = sSym 𝔼 P w₀ x₀ u wn (t + 1) - a • (wS t - wS (t + 1)) := rfl
    rw [this, map_sub, map_smul, map_sub, hwa t]
    rfl
  have hDb : ∀ t ω, |lagW w₀ wS t ω - wS t ω| ≤ max B W + W := fun t ω =>
    (abs_sub _ _).trans (add_le_add (lagW_bounded hw₀ hW t ω) (hW t ω))
  refine ⟨⟨⟨fun t ω => ?_, fun t ω => ?_, fun t ω => ?_, fun t => ?_, fun t => ?_, hxa, hwa,
    ⟨Sb + |P.lw / (P.lp + P.lw)| * (max B W + W), fun t ω => ?_⟩,
    ⟨Sb + |P.lp / (P.lp + P.lw)| * (max B W + W), fun t ω => ?_⟩, hxb, ⟨W, hW⟩⟩, ?_⟩,
    fun π πw x w hp hcr => ?_⟩
  · -- (2.11)
    have h1 := hRAS t ω
    have h2 := hSO' t ω
    have h3 := hEinfl (P.lw / (P.lp + P.lw)) t ω
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    change inflSym 𝔼 P w₀ x₀ u wn t ω = P.kp * (gapSym 𝔼 P w₀ x₀ u wn t ω + u t ω) +
      P.xip * (wS t ω - wn t ω) + P.beta * 𝔼.E t (fun ω => sSym 𝔼 P w₀ x₀ u wn (t + 1) ω +
        P.lw / (P.lp + P.lw) * (lagW w₀ wS (t + 1) ω - wS (t + 1) ω)) ω
    rw [h3]
    simp only [inflSym, hus, usSym] at h1 ⊢
    change sSym 𝔼 P w₀ x₀ u wn t ω = P.kp * gapSym 𝔼 P w₀ x₀ u wn t ω +
      P.beta * 𝔼.E t (sSym 𝔼 P w₀ x₀ u wn (t + 1)) ω + _ at h1
    linear_combination h1 + P.lw * (P.lp + P.lw)⁻¹ * h2 + P.xip * (wS t ω - wn t ω) * hSi
  · -- (2.12)
    have h1 := hRAS t ω
    have h2 := hSO' t ω
    have h3 := hEinflm (P.lp / (P.lp + P.lw)) t ω
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    change wageInflSym 𝔼 P w₀ x₀ u wn t ω = P.kw * (gapSym 𝔼 P w₀ x₀ u wn t ω + u t ω) +
      P.xiw * (wn t ω - wS t ω) + P.beta * 𝔼.E t (fun ω => sSym 𝔼 P w₀ x₀ u wn (t + 1) ω -
        P.lp / (P.lp + P.lw) * (lagW w₀ wS (t + 1) ω - wS (t + 1) ω)) ω
    rw [h3, hk]
    simp only [wageInflSym, hus, usSym] at h1 ⊢
    change sSym 𝔼 P w₀ x₀ u wn t ω = P.kp * gapSym 𝔼 P w₀ x₀ u wn t ω +
      P.beta * 𝔼.E t (sSym 𝔼 P w₀ x₀ u wn (t + 1)) ω + _ at h1
    linear_combination h1 - P.lp * (P.lp + P.lw)⁻¹ * h2 - P.xiw * (wS t ω - wn t ω) * hSi
  · -- (2.13)
    simp only [inflSym, wageInflSym]
    linear_combination (lagW w₀ wS t ω - wS t ω) * hSi
  · have : inflSym 𝔼 P w₀ x₀ u wn t = sSym 𝔼 P w₀ x₀ u wn t +
        (P.lw / (P.lp + P.lw)) • (lagW w₀ wS t - wS t) := rfl
    rw [this, map_add, map_smul, map_sub, hsS t, hla t, hwa t]
  · have : wageInflSym 𝔼 P w₀ x₀ u wn t = sSym 𝔼 P w₀ x₀ u wn t -
        (P.lp / (P.lp + P.lw)) • (lagW w₀ wS t - wS t) := rfl
    rw [this, map_sub, map_smul, map_sub, hsS t, hla t, hwa t]
  · simp only [inflSym]
    refine (abs_add_le _ _).trans (add_le_add (hSb t ω) ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hDb t ω) (abs_nonneg _)
  · simp only [wageInflSym]
    refine (abs_sub _ _).trans (add_le_add (hSb t ω) ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hDb t ω) (abs_nonneg _)
  · rw [criterion222_iff_base hk hkp.ne']
    have hs : sAvg P (inflSym 𝔼 P w₀ x₀ u wn) (wageInflSym 𝔼 P w₀ x₀ u wn) =
        sSym 𝔼 P w₀ x₀ u wn := by
      funext t ω
      simp only [sAvg, inflSym, wageInflSym]
      field_simp
      ring
    rw [hs]
    exact hRc
  · have hw : w = wS := wage_unique 𝔼 hk hβ0 hβ1 hc hwn hwna hw₀ hw₀a hp
    obtain ⟨hpe, hwe, hwi, hπa, hπwa, hxa', -, hπb, hπwb, hxb', -⟩ := hp
    obtain ⟨hsa', hsb'⟩ := sAvg_adapted_bounded 𝔼 P hπa hπwa hπb hπwb
    have hAS := sAvg_AS 𝔼 hk hS.ne' hpe hwe
    rw [hw] at hAS
    obtain ⟨h1, h2⟩ := hRu _ _ ⟨hAS, hsa', hxa', hsb', hxb'⟩
      ((criterion222_iff_base hk hkp.ne' x₀ π πw x).1 hcr)
    have hd : ∀ t ω, π t ω - πw t ω = lagW w₀ wS t ω - wS t ω := fun t ω => by
      rw [infl_diff_of_wageId hwi t ω, hw]
    have hsv : ∀ t ω, (P.lp * π t ω + P.lw * πw t ω) / (P.lp + P.lw) =
        sSym 𝔼 P w₀ x₀ u wn t ω := fun t ω => congrFun (congrFun h1 t) ω
    refine ⟨?_, ?_, h2, hw⟩
    · funext t ω
      have e1 := hsv t ω
      have e2 := hd t ω
      simp only [inflSym]
      rw [← e1, ← e2]
      field_simp
      ring
    · funext t ω
      have e1 := hsv t ω
      have e2 := hd t ω
      simp only [wageInflSym]
      rw [← e1, ← e2]
      field_simp
      ring

/-- **Woodford (2003), Ch. 8 §1.3 Definition, for (2.11)–(2.15)**: a rule (a relation between
`x_{t₀−1}`, `π`, `π^w`, `x`) is robustly optimal if for all bounded adapted disturbances `u, w^n`
and bounded date-0 initial conditions it determines a unique bounded adapted equilibrium, and
every equilibrium under the rule is optimal from a timeless perspective. -/
def RobustlyOptimalSW (P : SW)
    (Rule : (Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop) : Prop :=
  ∀ u wn : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → BoundedProc wn → 𝔼.Adapted wn →
    ∀ w₀ x₀ : Ω → ℝ, (∃ B, ∀ ω, |w₀ ω| ≤ B) → 𝔼.E 0 w₀ = w₀ → (∃ B, ∀ ω, |x₀ ω| ≤ B) →
    𝔼.E 0 x₀ = x₀ →
    (∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      PlanSW 𝔼 P w₀ u wn p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ Rule x₀ p.1 p.2.1 p.2.2.1) ∧
    ∀ π πw x w, PlanSW 𝔼 P w₀ u wn π πw x w → Rule x₀ π πw x →
      TimelessOptimalSW 𝔼 P w₀ u wn π πw x w

/-- **Woodford (2003), (2.22), p. 567 (THE ROBUSTLY OPTIMAL CRITERION WITH `κ_w = κ_p`)**: with
`κ_p = κ_w = κ > 0`, `λ_p, λ_w, λ_x > 0`, `ξ_p + ξ_w > 0`, `0 < β < 1`, the criterion
`π^sym_t + (λ_x/(λ_p κ_p + λ_w κ_w))(x_t − x_{t−1}) = 0` is robustly optimal. -/
theorem sym_robustlyOptimal (hpo : 𝔼.PullOut) {P : SW} (hk : P.kw = P.kp) (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hlx : 0 < P.lx) (hkp : 0 < P.kp)
    (hc : 0 < P.xip + P.xiw) :
    RobustlyOptimalSW 𝔼 P (fun x₀ π πw x => Criterion222 P x₀ π πw x) := by
  intro u wn ⟨M, hM⟩ hua ⟨N, hN⟩ hwna w₀ x₀ ⟨B, hB⟩ hw₀a ⟨Bx, hBx⟩ hx₀a
  obtain ⟨hex, huniq⟩ := sym_existsUnique 𝔼 hk hβ0 hβ1 hlp hlw hlx hkp hc hM hua hN hwna hB
    hw₀a hBx hx₀a
  refine ⟨⟨(inflSym 𝔼 P w₀ x₀ u wn, wageInflSym 𝔼 P w₀ x₀ u wn, gapSym 𝔼 P w₀ x₀ u wn,
    wSym 𝔼 P w₀ wn), hex, ?_⟩, fun π πw x w hp hcr =>
      sym_timeless 𝔼 hpo hk hβ0 hβ1 hlp hlw hlx.le hkp hc hN hwna hB hw₀a hBx hp hcr⟩
  rintro ⟨π, πw, x, w⟩ ⟨hp, hcr⟩
  obtain ⟨h1, h2, h3, h4⟩ := huniq π πw x w hp hcr
  simp [h1, h2, h3, h4]

/-- Woodford (2003), (2.22): the robust optimality holds on every finite event tree (genuine
uncertainty). -/
theorem sym_robustlyOptimal_finiteTree {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {P : SW} (hk : P.kw = P.kp) (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hlx : 0 < P.lx) (hkp : 0 < P.kp)
    (hc : 0 < P.xip + P.xiw) :
    RobustlyOptimalSW T.toExpectationSystem P (fun x₀ π πw x => Criterion222 P x₀ π πw x) :=
  sym_robustlyOptimal _ (ExpectationsFiniteTree.finiteTree_pullOut T) hk hβ0 hβ1 hlp hlw hlx
    hkp hc

/-! ## Determinacy with `κ_w ≠ κ_p` (the corrected criterion (2.20))

The equilibrium conditions reduce to a sixth-order equation in the real wage whose characteristic
polynomial is `P(𝒵)`, `𝒵 = (1 − βF)(1 − L)`. Complex roots are possible, so the analysis uses
complex-valued processes with the expectation applied to real and imaginary parts
(`ExpectationTools.EC`, with the complex forward-inverse lemma `ExpectationTools.fwdC_solves`,
`ExpectationTools.forwardC_unique`). -/

/-- Woodford (2003), (2.20): the lag of a complex process with initial value `y₀`. -/
def lagC (y₀ : Ω → ℂ) (y : ℕ → Ω → ℂ) : ℕ → Ω → ℂ
  | 0 => y₀
  | t + 1 => y t

/-- Woodford (2003), (2.20): `(lagC y₀ y)_0 = y₀`. -/
@[simp] theorem lagC_zero (y₀ : Ω → ℂ) (y : ℕ → Ω → ℂ) : lagC y₀ y 0 = y₀ := rfl

/-- Woodford (2003), (2.20): `(lagC y₀ y)_{t+1} = y_t`. -/
@[simp] theorem lagC_succ (y₀ : Ω → ℂ) (y : ℕ → Ω → ℂ) (t : ℕ) : lagC y₀ y (t + 1) = y t :=
  rfl

/-- Woodford (2003), (2.20): the complex backward recursion `y_t = μ y_{t−1} + v_t`. -/
def backRecC (μ : ℂ) (y₀ : Ω → ℂ) (v : ℕ → Ω → ℂ) : ℕ → Ω → ℂ
  | 0 => μ • y₀ + v 0
  | t + 1 => μ • backRecC μ y₀ v t + v (t + 1)

/-- Woodford (2003), (2.20): `backRecC` solves `y_t = μ y_{t−1} + v_t`. -/
theorem backRecC_eq (μ : ℂ) (y₀ : Ω → ℂ) (v : ℕ → Ω → ℂ) (t : ℕ) :
    backRecC μ y₀ v t = μ • lagC y₀ (backRecC μ y₀ v) t + v t := by
  cases t <;> rfl

/-- Woodford (2003), (2.20): `backRecC` is the only solution. -/
theorem eq_backRecC {μ : ℂ} {y₀ : Ω → ℂ} {v y : ℕ → Ω → ℂ}
    (hy : ∀ t, y t = μ • lagC y₀ y t + v t) : y = backRecC μ y₀ v := by
  funext t
  induction t with
  | zero => rw [hy 0]; rfl
  | succ t ih => rw [hy (t + 1)]; simp only [lagC_succ, ih]; rfl

/-- Woodford (2003), (2.20): for `‖μ‖ < 1` the complex backward recursion is bounded. -/
theorem backRecC_bounded {μ : ℂ} {Y W : ℝ} (hμ : ‖μ‖ < 1) {y₀ : Ω → ℂ} {v : ℕ → Ω → ℂ}
    (hy₀ : ∀ ω, ‖y₀ ω‖ ≤ Y) (hv : ∀ t ω, ‖v t ω‖ ≤ W) :
    ∀ t ω, ‖backRecC μ y₀ v t ω‖ ≤ max Y (W / (1 - ‖μ‖)) := by
  set B := max Y (W / (1 - ‖μ‖))
  have h1a : 0 < 1 - ‖μ‖ := by linarith
  have hWB : W ≤ (1 - ‖μ‖) * B := by
    have : W / (1 - ‖μ‖) ≤ B := le_max_right _ _
    rwa [div_le_iff₀ h1a, mul_comm] at this
  have step : ∀ (y : Ω → ℂ) (t : ℕ) (ω : Ω), ‖y ω‖ ≤ B → ‖μ * y ω + v t ω‖ ≤ B := by
    intro y t ω hv'
    calc ‖μ * y ω + v t ω‖ ≤ ‖μ‖ * ‖y ω‖ + ‖v t ω‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ ‖μ‖ * B + W := add_le_add (mul_le_mul_of_nonneg_left hv' (norm_nonneg _)) (hv t ω)
      _ ≤ B := by linarith
  intro t
  induction t with
  | zero => intro ω; exact step y₀ 0 ω ((hy₀ ω).trans (le_max_left _ _))
  | succ t ih => intro ω; exact step (backRecC μ y₀ v t) (t + 1) ω (ih ω)

/-- Woodford (2003), (2.20): `backRecC` of adapted data with a date-0 initial value is
adapted. -/
theorem backRecC_adapted {μ : ℂ} {y₀ : Ω → ℂ} {v : ℕ → Ω → ℂ} (h0 : EC 𝔼 0 y₀ = y₀)
    (hv : AdaptedC 𝔼 v) : AdaptedC 𝔼 (backRecC μ y₀ v) := by
  intro t
  induction t with
  | zero => change EC 𝔼 0 (μ • y₀ + v 0) = _; rw [EC_add, EC_smul, h0, hv 0]; rfl
  | succ t ih =>
    change EC 𝔼 (t + 1) (μ • backRecC μ y₀ v t + v (t + 1)) = _
    rw [EC_add, EC_smul, EC_of_known 𝔼 (Nat.le_succ t) ih, hv (t + 1)]
    rfl

/-- Woodford (2003), (2.20): the lag of an adapted complex process with date-0 initial value is
adapted. -/
theorem lagC_adapted {y₀ : Ω → ℂ} {y : ℕ → Ω → ℂ} (h0 : EC 𝔼 0 y₀ = y₀)
    (hy : AdaptedC 𝔼 y) : AdaptedC 𝔼 (lagC y₀ y) := by
  intro t
  cases t with
  | zero => exact h0
  | succ t => exact EC_of_known 𝔼 (Nat.le_succ t) (hy t)

/-- Woodford (2003), (2.20): the operator `𝒵 = (1 − βF)(1 − L)` on complex processes,
`(𝒵y)_t = (1 + β) y_t − β E_t y_{t+1} − y_{t−1}` (with `y_{−1} = y₀`). -/
noncomputable def ZopC (β : ℝ) (y₀ : Ω → ℂ) (y : ℕ → Ω → ℂ) (t : ℕ) : Ω → ℂ :=
  fun ω => (1 + β : ℂ) * y t ω - β * EC 𝔼 t (y (t + 1)) ω - lagC y₀ y t ω

/-- Woodford (2003), (2.20): `𝒵` is linear (with linearly combined initial values). -/
theorem ZopC_lin (β : ℝ) (a b : ℂ) (y₀ z₀ : Ω → ℂ) (y z : ℕ → Ω → ℂ) (t : ℕ) (ω : Ω) :
    ZopC 𝔼 β (fun ω => a * y₀ ω + b * z₀ ω) (fun s ω => a * y s ω + b * z s ω) t ω =
      a * ZopC 𝔼 β y₀ y t ω + b * ZopC 𝔼 β z₀ z t ω := by
  have hE : EC 𝔼 t (fun ω => a * y (t + 1) ω + b * z (t + 1) ω) ω =
      a * EC 𝔼 t (y (t + 1)) ω + b * EC 𝔼 t (z (t + 1)) ω := by
    rw [show (fun ω => a * y (t + 1) ω + b * z (t + 1) ω) = a • y (t + 1) + b • z (t + 1)
      from rfl, EC_add, EC_smul, EC_smul]
    rfl
  have hL : lagC (fun ω => a * y₀ ω + b * z₀ ω) (fun s ω => a * y s ω + b * z s ω) t ω =
      a * lagC y₀ y t ω + b * lagC z₀ z t ω := by cases t <;> rfl
  simp only [ZopC]
  rw [hE, hL]
  ring

/-- Woodford (2003), (2.20): `𝒵` annihilates constants. -/
theorem ZopC_const (β : ℝ) (k : Ω → ℂ) (hk : ∀ t, EC 𝔼 t k = k) (t : ℕ) (ω : Ω) :
    ZopC 𝔼 β k (fun _ => k) t ω = 0 := by
  have hl : lagC k (fun _ => k) t ω = k ω := by cases t <;> rfl
  simp only [ZopC, hk, hl]
  ring

/-- Woodford (2003), (2.20): `𝒵` of an adapted process with date-0 initial value is adapted. -/
theorem ZopC_adapted (β : ℝ) {y₀ : Ω → ℂ} {y : ℕ → Ω → ℂ} (h0 : EC 𝔼 0 y₀ = y₀)
    (hy : AdaptedC 𝔼 y) : AdaptedC 𝔼 (ZopC 𝔼 β y₀ y) := by
  intro t
  have : ZopC 𝔼 β y₀ y t = ((1 + β : ℂ) • y t - (β : ℂ) • EC 𝔼 t (y (t + 1))) -
      lagC y₀ y t := rfl
  rw [this, EC_sub, EC_sub, EC_smul, EC_smul, hy t, EC_tower 𝔼 le_rfl, lagC_adapted 𝔼 h0 hy t]

/-- Woodford (2003), (2.20): `𝒵` of a bounded process with bounded initial value is bounded. -/
theorem ZopC_bounded (β : ℝ) (hβ : 0 ≤ β) {y₀ : Ω → ℂ} {y : ℕ → Ω → ℂ} {B M : ℝ}
    (h0 : ∀ ω, ‖y₀ ω‖ ≤ B) (hy : ∀ t ω, ‖y t ω‖ ≤ M) :
    ∀ t ω, ‖ZopC 𝔼 β y₀ y t ω‖ ≤ (1 + β) * M + β * (2 * M) + max B M := by
  intro t ω
  have hl : ‖lagC y₀ y t ω‖ ≤ max B M := by
    cases t with
    | zero => exact (h0 ω).trans (le_max_left _ _)
    | succ t => exact (hy t ω).trans (le_max_right _ _)
  have h1 : ‖((1 + β : ℝ) : ℂ)‖ = 1 + β := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h2 : ‖(β : ℂ)‖ = β := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
  simp only [ZopC]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) hl)
  · rw [show (1 + (β : ℂ)) = ((1 + β : ℝ) : ℂ) by push_cast; ring, norm_mul, h1]
    exact mul_le_mul_of_nonneg_left (hy t ω) (by linarith)
  · rw [norm_mul, h2]
    exact mul_le_mul_of_nonneg_left (norm_EC_le 𝔼 (hy (t + 1)) t ω) hβ

/-- Woodford (2003), (2.20) (one factor of `P(𝒵)`): if `βμ² − (1 + β − Z)μ + 1 = 0`, then
`(𝒵 − Z) y = h` is equivalent to the forward equation `v_t = βμ E_t v_{t+1} + μ h_t` in
`v_t = y_t − μ y_{t−1}` (the factorisation `μ(𝒵 − Z) = (1 − βμF)(1 − μL)`). -/
theorem stage_iff {β : ℝ} {Z μ : ℂ} (hroot : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0)
    {y₀ : Ω → ℂ} {y h : ℕ → Ω → ℂ} (hya : AdaptedC 𝔼 y) (hμ : μ ≠ 0) :
    (∀ t ω, ZopC 𝔼 β y₀ y t ω - Z * y t ω = h t ω) ↔
      ∀ t, (fun ω => y t ω - μ * lagC y₀ y t ω) =
        ((β : ℂ) * μ) • EC 𝔼 t (fun ω => y (t + 1) ω - μ * y t ω) + μ • h t := by
  have hE : ∀ t ω, EC 𝔼 t (fun ω => y (t + 1) ω - μ * y t ω) ω =
      EC 𝔼 t (y (t + 1)) ω - μ * y t ω := fun t ω => by
    rw [show (fun ω => y (t + 1) ω - μ * y t ω) = y (t + 1) - μ • y t from rfl, EC_sub,
      EC_smul, hya t]
    rfl
  constructor
  · intro hyp t
    funext ω
    have h1 := hyp t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE]
    simp only [ZopC] at h1
    linear_combination μ * h1 + (y t ω) * hroot
  · intro hyp t ω
    have h1 := congrFun (hyp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE] at h1
    have h2 : μ * (ZopC 𝔼 β y₀ y t ω - Z * y t ω - h t ω) = 0 := by
      simp only [ZopC]
      linear_combination h1 - (y t ω) * hroot
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hμ
    · linear_combination h3

/-- Woodford (2003), (2.20): the solution of `(𝒵 − Z) y = h` with `y_{−1} = y₀`,
`y = (1 − μL)⁻¹ μ (1 − βμF)⁻¹ h`. -/
noncomputable def stageSol (β : ℝ) (μ : ℂ) (y₀ : Ω → ℂ) (h : ℕ → Ω → ℂ) : ℕ → Ω → ℂ :=
  backRecC μ y₀ (fwdC 𝔼 ((β : ℂ) * μ) (fun s => μ • h s))

/-- **Woodford (2003), (2.20) (one factor of `P(𝒵)`, existence and uniqueness)**: if
`βμ² − (1 + β − Z)μ + 1 = 0` with `‖μ‖ < 1`, then for bounded adapted `h` and a bounded date-0
initial value, `(𝒵 − Z) y = h` has exactly one bounded adapted (complex) solution. -/
theorem stage_existsUnique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Z μ : ℂ}
    (hroot : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0) (hμ : ‖μ‖ < 1) {H Y : ℝ}
    {h : ℕ → Ω → ℂ} (hh : ∀ t ω, ‖h t ω‖ ≤ H) (hha : AdaptedC 𝔼 h) {y₀ : Ω → ℂ}
    (hy₀ : ∀ ω, ‖y₀ ω‖ ≤ Y) (hy₀a : EC 𝔼 0 y₀ = y₀) :
    ((∀ t ω, ZopC 𝔼 β y₀ (stageSol 𝔼 β μ y₀ h) t ω - Z * stageSol 𝔼 β μ y₀ h t ω = h t ω) ∧
      AdaptedC 𝔼 (stageSol 𝔼 β μ y₀ h) ∧ BoundedC (stageSol 𝔼 β μ y₀ h)) ∧
    ∀ y, (∀ t ω, ZopC 𝔼 β y₀ y t ω - Z * y t ω = h t ω) → AdaptedC 𝔼 y → BoundedC y →
      y = stageSol 𝔼 β μ y₀ h := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl; simp at hroot
  have hβμ : ‖(β : ℂ) * μ‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
    nlinarith [norm_nonneg μ]
  have hgb : ∀ t ω, ‖(fun s => μ • h s) t ω‖ ≤ ‖μ‖ * H := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hh t ω) (norm_nonneg _)
  have hga : AdaptedC 𝔼 (fun s => μ • h s) := fun t => by simp only [EC_smul, hha t]
  have hws := fwdC_solves 𝔼 hβμ hgb hga
  have hwa := fwdC_adapted 𝔼 hβμ hgb
  have hwb := fwdC_bounded 𝔼 hβμ hgb
  set v := fwdC 𝔼 ((β : ℂ) * μ) (fun s => μ • h s)
  have hya : AdaptedC 𝔼 (stageSol 𝔼 β μ y₀ h) := backRecC_adapted 𝔼 hy₀a hwa
  have hqd : ∀ t, (fun ω => stageSol 𝔼 β μ y₀ h t ω - μ * lagC y₀ (stageSol 𝔼 β μ y₀ h) t ω) =
      v t := by
    intro t
    funext ω
    have := congrFun (backRecC_eq μ y₀ v t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    change backRecC μ y₀ v t ω - μ * lagC y₀ (backRecC μ y₀ v) t ω = v t ω
    rw [this]; ring
  have hqd' : ∀ t, (fun ω => stageSol 𝔼 β μ y₀ h (t + 1) ω - μ * stageSol 𝔼 β μ y₀ h t ω) =
      v (t + 1) := fun t => hqd (t + 1)
  refine ⟨⟨(stage_iff 𝔼 hroot hya hμ0).2 fun t => ?_, hya,
    ⟨_, backRecC_bounded hμ hy₀ hwb⟩⟩, fun y hy hyA hyB => ?_⟩
  · rw [hqd t, hqd' t]
    exact hws t
  · have hw := (stage_iff 𝔼 hroot hyA hμ0).1 hy
    obtain ⟨B, hB⟩ := hyB
    have hqb : BoundedC (fun t ω => y t ω - μ * lagC y₀ y t ω) := by
      refine ⟨B + ‖μ‖ * max Y B, fun t ω => ?_⟩
      refine (norm_sub_le _ _).trans (add_le_add (hB t ω) ?_)
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      cases t with
      | zero => exact (hy₀ ω).trans (le_max_left _ _)
      | succ t => exact (hB t ω).trans (le_max_right _ _)
    have heq := forwardC_unique 𝔼 hβμ (u := fun s => μ • h s)
      (z₁ := fun t ω => y t ω - μ * lagC y₀ y t ω) (fun t => hw t) hws hqb
      ⟨_, hwb⟩
    apply eq_backRecC
    intro t
    funext ω
    have := congrFun (congrFun heq t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change y t ω = μ * lagC y₀ y t ω + v t ω
    rw [← this]
    ring

/-- **Woodford (2003), (2.20) (one factor with no stable root)**: if `βμ² − (1 + β − Z)μ + 1 = 0`
with `‖μ‖ > 1` and `‖βμ‖ < 1` (i.e. both roots outside the closed unit disc), then a bounded
adapted solution of `(𝒵 − Z) y = 0` must have initial value `y_{−1} = 0`. -/
theorem stage_homog_init_zero {β : ℝ} {Z μ : ℂ}
    (hroot : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0) (hμ1 : 1 < ‖μ‖)
    (hβμ : ‖(β : ℂ) * μ‖ < 1) {Y : ℝ} {y₀ : Ω → ℂ} (hy₀ : ∀ ω, ‖y₀ ω‖ ≤ Y)
    {y : ℕ → Ω → ℂ} (hy : ∀ t ω, ZopC 𝔼 β y₀ y t ω - Z * y t ω = 0) (hya : AdaptedC 𝔼 y)
    (hyb : BoundedC y) : y₀ = 0 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl; norm_num at hμ1
  have hw := (stage_iff 𝔼 (h := fun _ _ => 0) hroot hya hμ0).1 hy
  obtain ⟨B, hB⟩ := hyb
  have hqb : BoundedC (fun t ω => y t ω - μ * lagC y₀ y t ω) := by
    refine ⟨B + ‖μ‖ * max Y B, fun t ω => ?_⟩
    refine (norm_sub_le _ _).trans (add_le_add (hB t ω) ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    cases t with
    | zero => exact (hy₀ ω).trans (le_max_left _ _)
    | succ t => exact (hB t ω).trans (le_max_right _ _)
  have hz : ∀ t, (fun _ : Ω => (0 : ℂ)) = ((β : ℂ) * μ) • EC 𝔼 t (fun _ => (0 : ℂ)) +
      (fun _ _ => (0 : ℂ)) t := fun t => by
    rw [show (fun _ : Ω => (0 : ℂ)) = 0 from rfl, EC_zero]; simp
  have heq := forwardC_unique 𝔼 hβμ (u := fun _ _ => 0)
    (z₁ := fun t ω => y t ω - μ * lagC y₀ y t ω) (z₂ := fun _ _ => 0)
    (fun t => by rw [hw t]; funext ω; simp) hz hqb ⟨0, fun _ _ => by simp⟩
  have hrec : ∀ t ω, y t ω = μ ^ (t + 1) * y₀ ω := by
    intro t ω
    induction t with
    | zero =>
      have := congrFun (congrFun heq 0) ω
      simp only [lagC_zero] at this
      linear_combination this
    | succ t ih =>
      have := congrFun (congrFun heq (t + 1)) ω
      simp only [lagC_succ] at this
      rw [pow_succ]
      linear_combination this + μ * ih
  funext ω
  by_contra hne
  have hpos : 0 < ‖y₀ ω‖ := norm_pos_iff.2 hne
  have hgrow : Tendsto (fun t : ℕ => ‖μ‖ ^ (t + 1) * ‖y₀ ω‖) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt hμ1).comp (tendsto_add_atTop_nat 1)).atTop_mul_const
      hpos
  obtain ⟨t, ht⟩ := (hgrow.eventually_gt_atTop B).exists
  have := hB t ω
  rw [hrec t ω, norm_mul, norm_pow] at this
  linarith

/-! ### The cubic operator equation `(𝒵 − Z₁)(𝒵 − Z₂)(𝒵 − Z₃) w = H` -/

/-- Woodford (2003), (2.20): the third-order operator equation in `𝒵`,
`𝒵³w − e₁𝒵²w + e₂𝒵w − e₃w = H`, with initial values `w_{−1} = w₀`, `(𝒵w)_{−1} = s₁`,
`(𝒵²w)_{−1} = s₂`. -/
def CubicC (β : ℝ) (e1 e2 e3 : ℂ) (w₀ s₁ s₂ : Ω → ℂ) (H w : ℕ → Ω → ℂ) : Prop :=
  ∀ t ω, ZopC 𝔼 β s₂ (ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w)) t ω - e1 * ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w) t ω +
    e2 * ZopC 𝔼 β w₀ w t ω - e3 * w t ω = H t ω

/-- Woodford (2003), (2.20): `ZopC` evaluated at a process given by a pointwise formula. -/
theorem ZopC_congr (β : ℝ) {y₀ z₀ : Ω → ℂ} {y z : ℕ → Ω → ℂ} (h0 : y₀ = z₀) (h : y = z)
    (t : ℕ) (ω : Ω) : ZopC 𝔼 β y₀ y t ω = ZopC 𝔼 β z₀ z t ω := by
  subst h0; subst h; rfl

/-- Woodford (2003), (2.20): bounded adapted complex processes are closed under `𝒵`. -/
theorem ZopC_bdd_adapted (β : ℝ) (hβ : 0 ≤ β) {y₀ : Ω → ℂ} {y : ℕ → Ω → ℂ}
    (h0 : EC 𝔼 0 y₀ = y₀) (hb0 : ∃ B, ∀ ω, ‖y₀ ω‖ ≤ B) (hy : AdaptedC 𝔼 y)
    (hyb : BoundedC y) : AdaptedC 𝔼 (ZopC 𝔼 β y₀ y) ∧ BoundedC (ZopC 𝔼 β y₀ y) := by
  obtain ⟨B, hB⟩ := hb0
  obtain ⟨M, hM⟩ := hyb
  exact ⟨ZopC_adapted 𝔼 β h0 hy, ⟨_, ZopC_bounded 𝔼 β hβ hB hM⟩⟩

/-- Woodford (2003), (2.20): linear combinations of bounded adapted complex processes. -/
theorem lin_bdd_adapted (a b : ℂ) {y z : ℕ → Ω → ℂ} (hy : AdaptedC 𝔼 y) (hz : AdaptedC 𝔼 z)
    (hyb : BoundedC y) (hzb : BoundedC z) :
    AdaptedC 𝔼 (fun t ω => a * y t ω + b * z t ω) ∧
      BoundedC (fun t ω => a * y t ω + b * z t ω) := by
  obtain ⟨M, hM⟩ := hyb
  obtain ⟨N, hN⟩ := hzb
  refine ⟨fun t => ?_, ⟨‖a‖ * M + ‖b‖ * N, fun t ω => ?_⟩⟩
  · change EC 𝔼 t (a • y t + b • z t) = _
    rw [EC_add, EC_smul, EC_smul, hy t, hz t]
    rfl
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
    · exact mul_le_mul_of_nonneg_left (hM t ω) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hN t ω) (norm_nonneg _)

/-- Woodford (2003), (2.20): linear combinations of bounded date-0 complex initial values. -/
theorem lin_init (a b : ℂ) {y₀ z₀ : Ω → ℂ} (hy : EC 𝔼 0 y₀ = y₀) (hz : EC 𝔼 0 z₀ = z₀)
    (hyb : ∃ B, ∀ ω, ‖y₀ ω‖ ≤ B) (hzb : ∃ B, ∀ ω, ‖z₀ ω‖ ≤ B) :
    EC 𝔼 0 (fun ω => a * y₀ ω + b * z₀ ω) = (fun ω => a * y₀ ω + b * z₀ ω) ∧
      ∃ B, ∀ ω, ‖a * y₀ ω + b * z₀ ω‖ ≤ B := by
  obtain ⟨M, hM⟩ := hyb
  obtain ⟨N, hN⟩ := hzb
  refine ⟨?_, ⟨‖a‖ * M + ‖b‖ * N, fun ω => ?_⟩⟩
  · change EC 𝔼 0 (a • y₀ + b • z₀) = _
    rw [EC_add, EC_smul, EC_smul, hy, hz]
    rfl
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
    · exact mul_le_mul_of_nonneg_left (hM ω) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hN ω) (norm_nonneg _)

/-- **Woodford (2003), (2.20) (the cubic operator equation, existence and uniqueness)**: if
`e₁, e₂, e₃` are the elementary symmetric functions of `Z₁, Z₂, Z₃` and each `Zᵢ` has a root
`μᵢ`, `‖μᵢ‖ < 1`, of `βμ² − (1 + β − Zᵢ)μ + 1 = 0`, then for every bounded adapted `H` and
bounded date-0 initial values there is exactly one bounded adapted solution. -/
theorem cubicC_existsUnique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Z1 Z2 Z3 μ1 μ2 μ3 : ℂ}
    (r1 : (β : ℂ) * μ1 ^ 2 - (1 + β - Z1) * μ1 + 1 = 0) (n1 : ‖μ1‖ < 1)
    (r2 : (β : ℂ) * μ2 ^ 2 - (1 + β - Z2) * μ2 + 1 = 0) (n2 : ‖μ2‖ < 1)
    (r3 : (β : ℂ) * μ3 ^ 2 - (1 + β - Z3) * μ3 + 1 = 0) (n3 : ‖μ3‖ < 1)
    {H : ℕ → Ω → ℂ} (hH : BoundedC H) (hHa : AdaptedC 𝔼 H) {w₀ s₁ s₂ : Ω → ℂ}
    (hw₀ : ∃ B, ∀ ω, ‖w₀ ω‖ ≤ B) (hs₁ : ∃ B, ∀ ω, ‖s₁ ω‖ ≤ B) (hs₂ : ∃ B, ∀ ω, ‖s₂ ω‖ ≤ B)
    (hw₀a : EC 𝔼 0 w₀ = w₀) (hs₁a : EC 𝔼 0 s₁ = s₁) (hs₂a : EC 𝔼 0 s₂ = s₂) :
    ∃! w, CubicC 𝔼 β (Z1 + Z2 + Z3) (Z1 * Z2 + Z1 * Z3 + Z2 * Z3) (Z1 * Z2 * Z3) w₀ s₁ s₂ H w ∧
      AdaptedC 𝔼 w ∧ BoundedC w := by
  -- initial values of the intermediate processes
  obtain ⟨hu1a, hu1b⟩ := lin_init 𝔼 1 (-Z3) hs₁a hw₀a hs₁ hw₀
  obtain ⟨hv1a, hv1b⟩ := lin_init 𝔼 1 (-(Z2 + Z3)) hs₂a hs₁a hs₂ hs₁
  obtain ⟨hu2a, hu2b⟩ := lin_init 𝔼 1 (Z2 * Z3) hv1a hw₀a hv1b hw₀
  set u1₀ : Ω → ℂ := fun ω => 1 * s₁ ω + -Z3 * w₀ ω with hu1
  set u2₀ : Ω → ℂ := fun ω => 1 * (1 * s₂ ω + -(Z2 + Z3) * s₁ ω) + Z2 * Z3 * w₀ ω with hu2
  obtain ⟨B0, hB0⟩ := hw₀
  obtain ⟨Bu1, hBu1⟩ := hu1b
  obtain ⟨Bu2, hBu2⟩ := hu2b
  obtain ⟨HB, hHB⟩ := hH
  -- the three stages
  obtain ⟨⟨e1, a1, ⟨K1, b1⟩⟩, q1⟩ := stage_existsUnique 𝔼 hβ0 hβ1 r1 n1 hHB hHa hBu2 hu2a
  obtain ⟨⟨e2, a2, ⟨K2, b2⟩⟩, q2⟩ := stage_existsUnique 𝔼 hβ0 hβ1 r2 n2 b1 a1 hBu1 hu1a
  obtain ⟨⟨e3, a3, b3⟩, q3⟩ := stage_existsUnique 𝔼 hβ0 hβ1 r3 n3 b2 a2 hB0 hw₀a
  set U2 := stageSol 𝔼 β μ1 u2₀ H with hU2
  set U1 := stageSol 𝔼 β μ2 u1₀ U2 with hU1
  set w := stageSol 𝔼 β μ3 w₀ U1 with hw
  refine ⟨w, ⟨fun t ω => ?_, a3, b3⟩, fun y ⟨hy, hya, hyb⟩ => ?_⟩
  · -- existence: the chain algebra
    have hW1 : ZopC 𝔼 β w₀ w = fun t ω => 1 * U1 t ω + Z3 * w t ω := by
      funext t ω; have := e3 t ω; linear_combination this
    have hW2 : ∀ t ω, ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w) t ω =
        1 * (1 * U2 t ω + Z2 * U1 t ω) + Z3 * ZopC 𝔼 β w₀ w t ω := by
      intro t ω
      rw [ZopC_congr 𝔼 β (z₀ := fun ω => 1 * u1₀ ω + Z3 * w₀ ω)
        (z := fun t ω => 1 * U1 t ω + Z3 * w t ω) (by funext ω; simp only [hu1]; ring) hW1,
        ZopC_lin]
      have := e2 t ω
      linear_combination this
    have hW2f : ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w) =
        fun t ω => 1 * (1 * U2 t ω + Z2 * U1 t ω) + Z3 * ZopC 𝔼 β w₀ w t ω :=
      funext fun t => funext fun ω => hW2 t ω
    have hV : ∀ t ω, ZopC 𝔼 β (fun ω => 1 * u2₀ ω + Z2 * u1₀ ω)
        (fun t ω => 1 * U2 t ω + Z2 * U1 t ω) t ω = 1 * (H t ω + Z1 * U2 t ω) +
          Z2 * (U2 t ω + Z2 * U1 t ω) := by
      intro t ω
      rw [ZopC_lin]
      have h1 := e1 t ω
      have h2 := e2 t ω
      linear_combination h1 + Z2 * h2
    have hW3 : ZopC 𝔼 β s₂ (ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w)) t ω =
        1 * (1 * (H t ω + Z1 * U2 t ω) + Z2 * (U2 t ω + Z2 * U1 t ω)) +
          Z3 * ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w) t ω := by
      rw [ZopC_congr 𝔼 β (z₀ := fun ω => 1 * (fun ω => 1 * u2₀ ω + Z2 * u1₀ ω) ω + Z3 * s₁ ω)
        (z := fun t ω => 1 * (fun t ω => 1 * U2 t ω + Z2 * U1 t ω) t ω +
          Z3 * ZopC 𝔼 β w₀ w t ω) (by funext ω; simp only [hu1, hu2]; ring) hW2f, ZopC_lin,
        hV]
    rw [hW3, hW2]
    have h3 := congrFun (congrFun hW1 t) ω
    rw [h3]
    ring
  · -- uniqueness
    set W1 := ZopC 𝔼 β w₀ y with hW1
    set W2 := ZopC 𝔼 β s₁ W1 with hW2
    obtain ⟨aW1, bW1⟩ := ZopC_bdd_adapted 𝔼 β hβ0 hw₀a ⟨B0, hB0⟩ hya hyb
    obtain ⟨aW2, bW2⟩ := ZopC_bdd_adapted 𝔼 β hβ0 hs₁a hs₁ aW1 bW1
    obtain ⟨aU1, bU1⟩ := lin_bdd_adapted 𝔼 1 (-Z3) aW1 hya bW1 hyb
    obtain ⟨aV, bV⟩ := lin_bdd_adapted 𝔼 1 (-(Z2 + Z3)) aW2 aW1 bW2 bW1
    obtain ⟨aU2, bU2⟩ := lin_bdd_adapted 𝔼 1 (Z2 * Z3) aV hya bV hyb
    have s1 : ∀ t ω, ZopC 𝔼 β u1₀ (fun t ω => 1 * W1 t ω + -Z3 * y t ω) t ω -
        Z2 * (1 * W1 t ω + -Z3 * y t ω) = (fun t ω => 1 * (fun t ω => 1 * W2 t ω +
          -(Z2 + Z3) * W1 t ω) t ω + Z2 * Z3 * y t ω) t ω := by
      intro t ω
      rw [ZopC_lin]
      simp only
      ring
    have s2 : ∀ t ω, ZopC 𝔼 β u2₀ (fun t ω => 1 * (fun t ω => 1 * W2 t ω +
        -(Z2 + Z3) * W1 t ω) t ω + Z2 * Z3 * y t ω) t ω - Z1 * (1 * (1 * W2 t ω +
          -(Z2 + Z3) * W1 t ω) + Z2 * Z3 * y t ω) = H t ω := by
      intro t ω
      rw [ZopC_lin, ZopC_lin]
      have := hy t ω
      simp only [← hW1, ← hW2] at this ⊢
      linear_combination this
    have hU2' := q1 _ s2 aU2 bU2
    have s1' : ∀ t ω, ZopC 𝔼 β u1₀ (fun t ω => 1 * W1 t ω + -Z3 * y t ω) t ω -
        Z2 * (1 * W1 t ω + -Z3 * y t ω) = U2 t ω := by
      intro t ω; rw [s1, ← hU2']
    have hU1' := q2 _ s1' aU1 bU1
    have s0 : ∀ t ω, ZopC 𝔼 β w₀ y t ω - Z3 * y t ω = U1 t ω := by
      intro t ω
      rw [← hU1']
      simp only [← hW1]
      ring
    exact q3 y s0 hya hyb

/-- Woodford (2003), (2.20): the operator `𝒵 = (1 − βF)(1 − L)` on real processes,
`(𝒵y)_t = (1 + β) y_t − β E_t y_{t+1} − y_{t−1}`. -/
def Zop (β : ℝ) (y₀ : Ω → ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + β) * y t ω - β * 𝔼.E t (y (t + 1)) ω - lagW y₀ y t ω

/-- Woodford (2003), (2.20): `𝒵` commutes with the embedding of real processes. -/
theorem ZopC_ofReal (β : ℝ) (y₀ : Ω → ℝ) (y : ℕ → Ω → ℝ) :
    ZopC 𝔼 β (fun ω => (y₀ ω : ℂ)) (fun t ω => (y t ω : ℂ)) =
      fun t ω => (Zop 𝔼 β y₀ y t ω : ℂ) := by
  funext t ω
  have hl : lagC (fun ω => (y₀ ω : ℂ)) (fun t ω => (y t ω : ℂ)) t ω = (lagW y₀ y t ω : ℂ) := by
    cases t <;> rfl
  simp only [ZopC, Zop, hl, EC_ofReal]
  push_cast
  ring

/-- Woodford (2003), (2.20): `𝒵` commutes with complex conjugation. -/
theorem ZopC_conj (β : ℝ) (y₀ : Ω → ℂ) (y : ℕ → Ω → ℂ) :
    ZopC 𝔼 β (fun ω => (starRingEnd ℂ) (y₀ ω)) (fun t ω => (starRingEnd ℂ) (y t ω)) =
      fun t ω => (starRingEnd ℂ) (ZopC 𝔼 β y₀ y t ω) := by
  funext t ω
  have hl : lagC (fun ω => (starRingEnd ℂ) (y₀ ω)) (fun t ω => (starRingEnd ℂ) (y t ω)) t ω =
      (starRingEnd ℂ) (lagC y₀ y t ω) := by cases t <;> rfl
  have hE := congrFun (EC_conj 𝔼 t (y (t + 1))) ω
  simp only [ZopC, hl, map_sub, map_mul, Complex.conj_ofReal, map_add, map_one]
  rw [← hE]

/-- Woodford (2003), (2.20): the real third-order equation
`p₃ 𝒵³w + p₂ 𝒵²w + p₁ 𝒵w + p₀ w = F`. -/
def CubicR (β p3 p2 p1 p0 : ℝ) (w₀ s₁ s₂ : Ω → ℝ) (F w : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, p3 * Zop 𝔼 β s₂ (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w)) t ω +
    p2 * Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w) t ω + p1 * Zop 𝔼 β w₀ w t ω + p0 * w t ω = F t ω

/-- Woodford (2003), (2.20): a real process is adapted iff its complexification is. -/
theorem adaptedC_ofReal {y : ℕ → Ω → ℝ} :
    AdaptedC 𝔼 (fun t ω => (y t ω : ℂ)) ↔ 𝔼.Adapted y := by
  constructor
  · intro h t
    funext ω
    have := congrFun (h t) ω
    rw [EC_ofReal] at this
    simp only at this
    exact_mod_cast this
  · intro h t
    rw [EC_ofReal]
    funext ω
    rw [h t]

/-- Woodford (2003), (2.20): `CubicR` for a real process is `CubicC` for its complexification
(with `eᵢ` the normalised coefficients). -/
theorem cubicR_iff {β p3 p2 p1 p0 : ℝ} (hp3 : p3 ≠ 0) {w₀ s₁ s₂ : Ω → ℝ}
    {F w : ℕ → Ω → ℝ} :
    CubicR 𝔼 β p3 p2 p1 p0 w₀ s₁ s₂ F w ↔
      CubicC 𝔼 β (-(p2 / p3) : ℝ) (p1 / p3 : ℝ) (-(p0 / p3) : ℝ) (fun ω => (w₀ ω : ℂ))
        (fun ω => (s₁ ω : ℂ)) (fun ω => (s₂ ω : ℂ)) (fun t ω => ((F t ω / p3 : ℝ) : ℂ))
        (fun t ω => (w t ω : ℂ)) := by
  have e1 : ZopC 𝔼 β (fun ω => (w₀ ω : ℂ)) (fun t ω => (w t ω : ℂ)) =
      fun t ω => (Zop 𝔼 β w₀ w t ω : ℂ) := ZopC_ofReal 𝔼 β w₀ w
  have e2 : ZopC 𝔼 β (fun ω => (s₁ ω : ℂ)) (fun t ω => (Zop 𝔼 β w₀ w t ω : ℂ)) =
      fun t ω => (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w) t ω : ℂ) := ZopC_ofReal 𝔼 β s₁ _
  have e3 : ZopC 𝔼 β (fun ω => (s₂ ω : ℂ))
      (fun t ω => (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w) t ω : ℂ)) =
      fun t ω => (Zop 𝔼 β s₂ (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w)) t ω : ℂ) := ZopC_ofReal 𝔼 β s₂ _
  simp only [CubicC, CubicR, e1, e2, e3]
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  rw [show (Zop 𝔼 β s₂ (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w)) t ω : ℂ) - ((-(p2 / p3) : ℝ) : ℂ) *
      (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w) t ω : ℂ) + ((p1 / p3 : ℝ) : ℂ) * (Zop 𝔼 β w₀ w t ω : ℂ) -
      ((-(p0 / p3) : ℝ) : ℂ) * (w t ω : ℂ) =
      ((Zop 𝔼 β s₂ (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w)) t ω + p2 / p3 * Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w) t ω +
        p1 / p3 * Zop 𝔼 β w₀ w t ω + p0 / p3 * w t ω : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_inj]
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    field_simp at h
    linear_combination h

/-- Woodford (2003), (2.20): `𝒵` with a real initial value commutes with conjugation. -/
theorem ZopC_conj_real (β : ℝ) {y₀ : Ω → ℂ} (hy₀ : ∀ ω, (starRingEnd ℂ) (y₀ ω) = y₀ ω)
    (y : ℕ → Ω → ℂ) :
    ZopC 𝔼 β y₀ (fun t ω => (starRingEnd ℂ) (y t ω)) =
      fun t ω => (starRingEnd ℂ) (ZopC 𝔼 β y₀ y t ω) := by
  rw [← ZopC_conj]
  congr 1
  funext ω
  rw [hy₀]

/-- **Woodford (2003), (2.20) (the real third-order equation, existence and uniqueness)**: if
`p₃ ≠ 0`, `p₃Z³ + p₂Z² + p₁Z + p₀ = p₃(Z − Z₁)(Z − Z₂)(Z − Z₃)` (Vieta) and each root `Zᵢ` has
a stable root `μᵢ` (`‖μᵢ‖ < 1`) of `βμ² − (1 + β − Zᵢ)μ + 1 = 0`, then for every bounded adapted
`F` and bounded date-0 initial values the real equation `CubicR` has exactly one bounded adapted
solution. -/
theorem cubicR_existsUnique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p3 p2 p1 p0 : ℝ}
    (hp3 : p3 ≠ 0) {Z1 Z2 Z3 μ1 μ2 μ3 : ℂ} (hv1 : Z1 + Z2 + Z3 = ((-(p2 / p3) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((p1 / p3 : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(p0 / p3) : ℝ) : ℂ))
    (r1 : (β : ℂ) * μ1 ^ 2 - (1 + β - Z1) * μ1 + 1 = 0) (n1 : ‖μ1‖ < 1)
    (r2 : (β : ℂ) * μ2 ^ 2 - (1 + β - Z2) * μ2 + 1 = 0) (n2 : ‖μ2‖ < 1)
    (r3 : (β : ℂ) * μ3 ^ 2 - (1 + β - Z3) * μ3 + 1 = 0) (n3 : ‖μ3‖ < 1)
    {F : ℕ → Ω → ℝ} (hF : BoundedProc F) (hFa : 𝔼.Adapted F) {w₀ s₁ s₂ : Ω → ℝ}
    (hw₀ : ∃ B, ∀ ω, |w₀ ω| ≤ B) (hs₁ : ∃ B, ∀ ω, |s₁ ω| ≤ B) (hs₂ : ∃ B, ∀ ω, |s₂ ω| ≤ B)
    (hw₀a : 𝔼.E 0 w₀ = w₀) (hs₁a : 𝔼.E 0 s₁ = s₁) (hs₂a : 𝔼.E 0 s₂ = s₂) :
    ∃! w, CubicR 𝔼 β p3 p2 p1 p0 w₀ s₁ s₂ F w ∧ 𝔼.Adapted w ∧ BoundedProc w := by
  have cinit : ∀ y : Ω → ℝ, 𝔼.E 0 y = y → EC 𝔼 0 (fun ω => (y ω : ℂ)) = fun ω => (y ω : ℂ) :=
    fun y hy => by rw [EC_ofReal, hy]
  have cbd : ∀ y : Ω → ℝ, (∃ B, ∀ ω, |y ω| ≤ B) → ∃ B, ∀ ω, ‖(y ω : ℂ)‖ ≤ B :=
    fun y ⟨B, hB⟩ => ⟨B, fun ω => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB ω⟩
  obtain ⟨M, hM⟩ := hF
  have hH : BoundedC (fun t ω => ((F t ω / p3 : ℝ) : ℂ)) :=
    ⟨M / |p3|, fun t ω => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
      exact div_le_div_of_nonneg_right (hM t ω) (abs_nonneg _)⟩
  have hHa : AdaptedC 𝔼 (fun t ω => ((F t ω / p3 : ℝ) : ℂ)) := by
    rw [adaptedC_ofReal]
    intro t
    change 𝔼.E t (fun ω => F t ω / p3) = fun ω => F t ω / p3
    rw [show (fun ω => F t ω / p3) = p3⁻¹ • F t by funext ω; simp [div_eq_inv_mul],
      map_smul, hFa t]
  obtain ⟨wc, ⟨hc, ha, hb⟩, huniq⟩ := cubicC_existsUnique 𝔼 hβ0 hβ1 r1 n1 r2 n2 r3 n3 hH hHa
    (cbd w₀ hw₀) (cbd s₁ hs₁) (cbd s₂ hs₂) (cinit w₀ hw₀a) (cinit s₁ hs₁a) (cinit s₂ hs₂a)
  rw [hv1, hv2, hv3] at hc huniq
  -- the conjugate solves the same equation
  have hreal : ∀ y : Ω → ℝ, ∀ ω, (starRingEnd ℂ) ((y ω : ℂ)) = (y ω : ℂ) :=
    fun y ω => Complex.conj_ofReal _
  have hconj : CubicC 𝔼 β ((-(p2 / p3) : ℝ) : ℂ) ((p1 / p3 : ℝ) : ℂ) ((-(p0 / p3) : ℝ) : ℂ)
      (fun ω => (w₀ ω : ℂ)) (fun ω => (s₁ ω : ℂ)) (fun ω => (s₂ ω : ℂ))
      (fun t ω => ((F t ω / p3 : ℝ) : ℂ)) (fun t ω => (starRingEnd ℂ) (wc t ω)) := by
    intro t ω
    rw [ZopC_conj_real 𝔼 β (hreal w₀), ZopC_conj_real 𝔼 β (hreal s₁),
      ZopC_conj_real 𝔼 β (hreal s₂)]
    have := congrArg (starRingEnd ℂ) (hc t ω)
    simp only [map_sub, map_add, map_mul, Complex.conj_ofReal] at this
    exact this
  have hca : AdaptedC 𝔼 (fun t ω => (starRingEnd ℂ) (wc t ω)) := fun t => by
    rw [EC_conj, ha t]
  have hcb : BoundedC (fun t ω => (starRingEnd ℂ) (wc t ω)) := by
    obtain ⟨B, hB⟩ := hb
    exact ⟨B, fun t ω => by rw [Complex.norm_conj]; exact hB t ω⟩
  have heq := huniq _ ⟨hconj, hca, hcb⟩
  have him : ∀ t ω, wc t ω = (((wc t ω).re : ℝ) : ℂ) := fun t ω => by
    have := congrFun (congrFun heq t) ω
    exact (Complex.conj_eq_iff_re.1 this).symm
  have hwc : wc = fun t ω => (((wc t ω).re : ℝ) : ℂ) := funext fun t => funext fun ω => him t ω
  refine ⟨fun t ω => (wc t ω).re, ⟨(cubicR_iff 𝔼 hp3).2 (hwc ▸ hc), ?_, ?_⟩, ?_⟩
  · rw [← adaptedC_ofReal, ← hwc]; exact ha
  · obtain ⟨B, hB⟩ := hb
    exact ⟨B, fun t ω => (Complex.abs_re_le_norm _).trans (hB t ω)⟩
  · intro y ⟨hy, hya, hyb⟩
    have hyc := (cubicR_iff 𝔼 hp3).1 hy
    obtain ⟨B, hB⟩ := hyb
    have := huniq _ ⟨hyc, (adaptedC_ofReal 𝔼).2 hya,
      ⟨B, fun t ω => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB t ω⟩⟩
    funext t ω
    have h1 := congrFun (congrFun this t) ω
    change (y t ω : ℂ) = wc t ω at h1
    rw [← h1, Complex.ofReal_re]

/-! ### The characteristic polynomial and the location of its roots -/

/-- Woodford (2003), (2.20)–(2.21): `Δ = κ_p ξ_w + κ_w ξ_p`. -/
def Dst (P : SW) : ℝ := P.kp * P.xiw + P.kw * P.xip

/-- **Woodford (2003), (2.16)–(2.20) (the characteristic polynomial)**: in the variable
`Z = (1 − βμ)(1 − μ⁻¹)`, `P(Z) = λ_x Z (Z + ξ_p + ξ_w)² + λ_w (κ_w Z + Δ)² + λ_p (κ_p Z + Δ)²`. -/
noncomputable def charP (P : SW) (Z : ℂ) : ℂ :=
  P.lx * Z * (Z + (P.xip + P.xiw)) ^ 2 + P.lw * (P.kw * Z + Dst P) ^ 2 +
    P.lp * (P.kp * Z + Dst P) ^ 2

/-- Woodford (2003), (2.20): the coefficient of `Z²` in `P`. -/
def cp2 (P : SW) : ℝ := 2 * P.lx * (P.xip + P.xiw) + P.lw * P.kw ^ 2 + P.lp * P.kp ^ 2

/-- Woodford (2003), (2.20): the coefficient of `Z` in `P`. -/
def cp1 (P : SW) : ℝ := P.lx * (P.xip + P.xiw) ^ 2 + 2 * Dst P * (P.lw * P.kw + P.lp * P.kp)

/-- Woodford (2003), (2.20): the constant term of `P`. -/
def cp0 (P : SW) : ℝ := Dst P ^ 2 * (P.lw + P.lp)

/-- Woodford (2003), (2.20): `P(Z) = λ_x Z³ + p₂ Z² + p₁ Z + p₀`. -/
theorem charP_expand (P : SW) (Z : ℂ) :
    charP P Z = P.lx * Z ^ 3 + cp2 P * Z ^ 2 + cp1 P * Z + cp0 P := by
  simp only [charP, cp2, cp1, cp0]
  push_cast
  ring

/-- **Woodford (2003), (2.20) (the root condition)**: every root `Z` of `P` has a root `μ`,
`‖μ‖ < 1`, of `βμ² − (1 + β − Z)μ + 1 = 0` (one stable root per factor). -/
def StableRoots (P : SW) : Prop :=
  ∀ Z : ℂ, charP P Z = 0 →
    ∃ μ : ℂ, (P.beta : ℂ) * μ ^ 2 - (1 + P.beta - Z) * μ + 1 = 0 ∧ ‖μ‖ < 1

/-- Woodford (2003), (2.20): the quadratic form of the ellipse
`{(1 + β)(1 − cos θ) + i(1 − β) sin θ}` (the image of the unit circle under `μ ↦ Z(μ)`). -/
noncomputable def ellForm (β : ℝ) (Z : ℂ) : ℝ :=
  ((Z.re - (1 + β)) / (1 + β)) ^ 2 + (Z.im / (1 - β)) ^ 2

/-- Woodford (2003), (2.20): for a root `μ ≠ 0` of `βμ² − (1 + β − Z)μ + 1 = 0`, with
`q = |μ|²`, `ellForm β Z − 1 = (1 − q)(1 − β²q)(m₁²/(1+β)² + m₂²/(1−β)²)/q²`. -/
theorem ellForm_sub_one {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Z μ : ℂ}
    (hr : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0) (hμ : μ ≠ 0) :
    ellForm β Z - 1 = (1 - Complex.normSq μ) * (1 - β ^ 2 * Complex.normSq μ) *
      (μ.re ^ 2 / (1 + β) ^ 2 + μ.im ^ 2 / (1 - β) ^ 2) / Complex.normSq μ ^ 2 := by
  have hq : 0 < Complex.normSq μ := Complex.normSq_pos.2 hμ
  have hZ : Z = 1 + β - β * μ - μ⁻¹ := by
    field_simp
    linear_combination hr
  have hre : Z.re = 1 + β - β * μ.re - μ.re / Complex.normSq μ := by
    rw [hZ]; simp [Complex.inv_re]
  have him : Z.im = -(β * μ.im) + μ.im / Complex.normSq μ := by
    rw [hZ]; simp [Complex.inv_im]; ring
  have hn : Complex.normSq μ = μ.re ^ 2 + μ.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have h1 : (1 + β) ≠ 0 := by linarith
  have h2 : (1 - β) ≠ 0 := by linarith
  simp only [ellForm, hre, him]
  rw [hn] at hq ⊢
  field_simp
  ring

/-- Woodford (2003), (2.20): a root of `βμ² − (1 + β − Z)μ + 1 = 0` exists. -/
theorem exists_mu_root (β : ℝ) (hβ : β ≠ 0) (Z : ℂ) :
    ∃ μ : ℂ, (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (discrim (β : ℂ) (-(1 + β - Z)) 1)
  have hb : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  refine ⟨(-(-(1 + β - Z)) + s) / (2 * β), ?_⟩
  have := (quadratic_eq_zero_iff hb hs ((-(-(1 + β - Z)) + s) / (2 * β))).2 (Or.inl rfl)
  linear_combination this

/-- **Woodford (2003), (2.20) (the root condition as an ellipse)**: for `0 < β < 1`, the
quadratic `βμ² − (1 + β − Z)μ + 1 = 0` has a root with `‖μ‖ < 1` iff `Z` lies strictly
outside the ellipse `ellForm β Z ≤ 1` (centre `1 + β`, semi-axes `1 + β` and `1 − β`). -/
theorem stable_iff_ellForm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (Z : ℂ) :
    (∃ μ : ℂ, (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0 ∧ ‖μ‖ < 1) ↔ 1 < ellForm β Z := by
  have hbet : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  have key : ∀ μ : ℂ, (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0 → μ ≠ 0 := by
    rintro μ hr rfl; simp at hr
  constructor
  · rintro ⟨μ, hr, hμ⟩
    have hμ0 := key μ hr
    have hq : 0 < Complex.normSq μ := Complex.normSq_pos.2 hμ0
    have hq1 : Complex.normSq μ < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg μ]
    have h := ellForm_sub_one hβ0 hβ1 hr hμ0
    have hpos : 0 < μ.re ^ 2 / (1 + β) ^ 2 + μ.im ^ 2 / (1 - β) ^ 2 := by
      have hm : 0 < μ.re ^ 2 + μ.im ^ 2 := by rw [Complex.normSq_apply] at hq; nlinarith
      have hd : μ.im ^ 2 / (1 + β) ^ 2 ≤ μ.im ^ 2 / (1 - β) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by nlinarith) (by nlinarith)
      have : 0 < (μ.re ^ 2 + μ.im ^ 2) / (1 + β) ^ 2 := by positivity
      rw [add_div] at this
      linarith
    have hb2 : 0 < 1 - β ^ 2 * Complex.normSq μ := by nlinarith
    have : 0 < ellForm β Z - 1 := by
      rw [h]; apply div_pos _ (by positivity)
      exact mul_pos (mul_pos (by linarith) hb2) hpos
    linarith
  · intro hE
    obtain ⟨μ, hr⟩ := exists_mu_root β hβ0.ne' Z
    have hμ0 := key μ hr
    by_cases h1 : ‖μ‖ < 1
    · exact ⟨μ, hr, h1⟩
    set ν := ((β : ℂ) * μ)⁻¹
    have hν : (β : ℂ) * ν ^ 2 - (1 + β - Z) * ν + 1 = 0 := by
      have hbm : (β : ℂ) * μ ≠ 0 := mul_ne_zero hbet hμ0
      simp only [ν]
      field_simp
      linear_combination hr
    by_cases h2 : ‖ν‖ < 1
    · exact ⟨ν, hν, h2⟩
    exfalso
    push Not at h1 h2
    have hνn : ‖ν‖ = 1 / (β * ‖μ‖) := by
      simp only [ν, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hβ0, one_div]
    have hμup : ‖μ‖ ≤ 1 / β := by
      rw [hνn, le_div_iff₀ (by positivity)] at h2
      rw [le_div_iff₀ hβ0]; linarith
    have hq1 : 1 ≤ Complex.normSq μ := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith
    have hq2 : β ^ 2 * Complex.normSq μ ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have : β * ‖μ‖ ≤ 1 := by rwa [le_div_iff₀ hβ0, mul_comm] at hμup
      have h0 : 0 ≤ β * ‖μ‖ := by positivity
      have := pow_le_one₀ h0 this (n := 2)
      rw [mul_pow] at this
      exact this
    have h := ellForm_sub_one hβ0 hβ1 hr hμ0
    have hq : 0 < Complex.normSq μ := by linarith
    have hnum : (1 - Complex.normSq μ) * (1 - β ^ 2 * Complex.normSq μ) *
        (μ.re ^ 2 / (1 + β) ^ 2 + μ.im ^ 2 / (1 - β) ^ 2) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      · positivity
    have : ellForm β Z - 1 ≤ 0 := by
      rw [h]; exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
    linarith

/-- Woodford (2003), (2.20): every `Z` with negative real part lies outside the ellipse. -/
theorem ellForm_gt_of_re_neg {β : ℝ} (hβ0 : 0 < β) {Z : ℂ} (h : Z.re < 0) :
    1 < ellForm β Z := by
  have h1 : 1 < ((Z.re - (1 + β)) / (1 + β)) ^ 2 := by
    rw [div_pow, one_lt_div (by positivity)]
    nlinarith
  have : 0 ≤ (Z.im / (1 - β)) ^ 2 := sq_nonneg _
  simp only [ellForm]
  linarith

/-- **Woodford (2003), (2.20)**: with all parameters positive, `P` has no root with nonnegative
real `Z` (so every REAL root is negative). -/
theorem charP_ne_zero_of_nonneg (P : SW) (hlx : 0 < P.lx) (hlw : 0 < P.lw) (hlp : 0 < P.lp)
    (hkp : 0 < P.kp) (hkw : 0 < P.kw) (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) {x : ℝ}
    (hx : 0 ≤ x) : charP P x ≠ 0 := by
  have hD : 0 < Dst P := by unfold Dst; positivity
  have hr : charP P x = ((P.lx * x * (x + (P.xip + P.xiw)) ^ 2 + P.lw * (P.kw * x + Dst P) ^ 2 +
      P.lp * (P.kp * x + Dst P) ^ 2 : ℝ) : ℂ) := by simp only [charP]; push_cast; ring
  rw [hr, Complex.ofReal_ne_zero]
  have : 0 < P.lp * (P.kp * x + Dst P) ^ 2 := by positivity
  positivity

/-- **Woodford (2003), (2.20) (a sufficient condition)**: if every root of `P` has negative real
part — in particular if all three roots are real — the root condition holds. -/
theorem stableRoots_of_re_neg (P : SW) (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (h : ∀ Z, charP P Z = 0 → Z.re < 0) : StableRoots P := fun Z hZ =>
  (stable_iff_ellForm hβ0 hβ1 Z).2 (ellForm_gt_of_re_neg hβ0 (h Z hZ))

/-- **Woodford (2003), (2.20)**: the root condition holds whenever all roots of `P` are real
(real roots are negative by `charP_ne_zero_of_nonneg`). -/
theorem stableRoots_of_real (P : SW) (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1) (hlx : 0 < P.lx)
    (hlw : 0 < P.lw) (hlp : 0 < P.lp) (hkp : 0 < P.kp) (hkw : 0 < P.kw) (hxip : 0 < P.xip)
    (hxiw : 0 < P.xiw) (h : ∀ Z, charP P Z = 0 → Z.im = 0) : StableRoots P := by
  refine stableRoots_of_re_neg P hβ0 hβ1 fun Z hZ => ?_
  by_contra hc
  push Not at hc
  have hZ' : Z = (Z.re : ℂ) := Complex.ext (by simp) (by simp [h Z hZ])
  rw [hZ'] at hZ
  exact charP_ne_zero_of_nonneg P hlx hlw hlp hkp hkw hxip hxiw hc hZ

/-- Woodford (2003), (2.20): a cubic `p₃Z³ + p₂Z² + p₁Z + p₀` (`p₃ ≠ 0`) has complex roots
`Z₁, Z₂, Z₃` with the Vieta relations. -/
theorem cubic_vieta_exists {p3 p2 p1 p0 : ℝ} (hp3 : p3 ≠ 0) :
    ∃ Z1 Z2 Z3 : ℂ, Z1 + Z2 + Z3 = ((-(p2 / p3) : ℝ) : ℂ) ∧
      Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((p1 / p3 : ℝ) : ℂ) ∧
      Z1 * Z2 * Z3 = ((-(p0 / p3) : ℝ) : ℂ) := by
  have hp3c : (p3 : ℂ) ≠ 0 := by exact_mod_cast hp3
  obtain ⟨Z1, hZ1⟩ := Complex.exists_root (f := Polynomial.C (p3 : ℂ) * Polynomial.X ^ 3 +
    Polynomial.C (p2 : ℂ) * Polynomial.X ^ 2 + Polynomial.C (p1 : ℂ) * Polynomial.X +
    Polynomial.C (p0 : ℂ)) (by rw [Polynomial.degree_cubic hp3c]; norm_num)
  have h1 : (p3 : ℂ) * Z1 ^ 3 + p2 * Z1 ^ 2 + p1 * Z1 + p0 = 0 := by
    simpa [Polynomial.IsRoot] using hZ1
  -- the quadratic factor `p₃Z² + bZ + c`
  set b : ℂ := p2 + p3 * Z1
  set c : ℂ := p1 + p2 * Z1 + p3 * Z1 ^ 2
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (discrim (p3 : ℂ) b c)
  have hd : discrim (p3 : ℂ) b c = b ^ 2 - 4 * p3 * c := by simp [discrim]
  rw [hd] at hs
  have hsum : (-b + s) / (2 * p3) + (-b - s) / (2 * p3) = -b / p3 := by
    field_simp; ring
  have hpr : (-b + s) * (-b - s) = 4 * p3 * c := by linear_combination hs
  have hprod : (-b + s) / (2 * p3) * ((-b - s) / (2 * p3)) = c / p3 := by
    rw [div_mul_div_comm, hpr]; field_simp; ring
  refine ⟨Z1, (-b + s) / (2 * p3), (-b - s) / (2 * p3), ?_, ?_, ?_⟩
  · rw [add_assoc, hsum]
    simp only [b]
    push_cast
    field_simp
    ring
  · rw [show Z1 * ((-b + s) / (2 * p3)) + Z1 * ((-b - s) / (2 * p3)) +
        (-b + s) / (2 * p3) * ((-b - s) / (2 * p3)) =
        Z1 * ((-b + s) / (2 * p3) + (-b - s) / (2 * p3)) +
        (-b + s) / (2 * p3) * ((-b - s) / (2 * p3)) by ring, hsum, hprod]
    simp only [b, c]
    push_cast
    field_simp
    ring
  · rw [mul_assoc, hprod]
    simp only [c]
    push_cast
    field_simp
    linear_combination h1

/-! ### From the first-order conditions to the cubic equation in the real wage -/

/-- Woodford (2003), (2.20): `𝒵` applied to a linear combination of six processes plus a
constant, with the correspondingly combined initial value. -/
theorem Zop_comb6 (β : ℝ) (a1 a2 a3 a4 a5 a6 k : ℝ) {y1 y2 y3 y4 y5 y6 z : ℕ → Ω → ℝ}
    {i1 i2 i3 i4 i5 i6 z₀ : Ω → ℝ}
    (hz : ∀ t ω, z t ω = a1 * y1 t ω + a2 * y2 t ω + a3 * y3 t ω + a4 * y4 t ω +
      a5 * y5 t ω + a6 * y6 t ω + k)
    (hz₀ : ∀ ω, z₀ ω = a1 * i1 ω + a2 * i2 ω + a3 * i3 ω + a4 * i4 ω + a5 * i5 ω +
      a6 * i6 ω + k) (t : ℕ) (ω : Ω) :
    Zop 𝔼 β z₀ z t ω = a1 * Zop 𝔼 β i1 y1 t ω + a2 * Zop 𝔼 β i2 y2 t ω +
      a3 * Zop 𝔼 β i3 y3 t ω + a4 * Zop 𝔼 β i4 y4 t ω + a5 * Zop 𝔼 β i5 y5 t ω +
      a6 * Zop 𝔼 β i6 y6 t ω := by
  have hf : z (t + 1) = a1 • y1 (t + 1) + a2 • y2 (t + 1) + a3 • y3 (t + 1) + a4 • y4 (t + 1) +
      a5 • y5 (t + 1) + a6 • y6 (t + 1) + (fun _ => k) := by
    funext ω'; rw [hz]; rfl
  have hE : 𝔼.E t (z (t + 1)) ω = a1 * 𝔼.E t (y1 (t + 1)) ω + a2 * 𝔼.E t (y2 (t + 1)) ω +
      a3 * 𝔼.E t (y3 (t + 1)) ω + a4 * 𝔼.E t (y4 (t + 1)) ω + a5 * 𝔼.E t (y5 (t + 1)) ω +
      a6 * 𝔼.E t (y6 (t + 1)) ω + k := by
    rw [hf]
    simp only [map_add, map_smul, 𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hl : lagW z₀ z t ω = a1 * lagW i1 y1 t ω + a2 * lagW i2 y2 t ω + a3 * lagW i3 y3 t ω +
      a4 * lagW i4 y4 t ω + a5 * lagW i5 y5 t ω + a6 * lagW i6 y6 t ω + k := by
    cases t with
    | zero => exact hz₀ ω
    | succ t => exact hz t ω
  simp only [Zop]
  rw [hE, hl, hz t ω]
  ring

/-- Woodford (2003), (2.20): `𝒵` of an adapted process with date-0 initial value is adapted. -/
theorem Zop_adapted (β : ℝ) {y₀ : Ω → ℝ} {y : ℕ → Ω → ℝ} (h0 : 𝔼.E 0 y₀ = y₀)
    (hy : 𝔼.Adapted y) : 𝔼.Adapted (Zop 𝔼 β y₀ y) := by
  intro t
  have : Zop 𝔼 β y₀ y t = ((1 + β) • y t - β • 𝔼.E t (y (t + 1))) - lagW y₀ y t := rfl
  rw [this, map_sub, map_sub, map_smul, map_smul, hy t, 𝔼.E_E_self, lagW_adapted 𝔼 h0 hy t]

/-- Woodford (2003), (2.20): `𝒵` of a bounded process with bounded initial value is bounded. -/
theorem Zop_bounded (β : ℝ) (hβ : 0 ≤ β) {y₀ : Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h0 : ∃ B, ∀ ω, |y₀ ω| ≤ B) (hy : BoundedProc y) : BoundedProc (Zop 𝔼 β y₀ y) := by
  obtain ⟨B, hB⟩ := h0
  obtain ⟨M, hM⟩ := hy
  refine ⟨(1 + β) * M + β * M + max B M, fun t ω => ?_⟩
  simp only [Zop]
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_))
    (lagW_bounded hB hM t ω))
  · rw [abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left (hM t ω) (by linarith)
  · rw [abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + 1)) t ω) hβ

/-- **Woodford (2003), (2.11)–(2.13) (the real-wage equation, general `κ`)**: in any plan,
`𝒵w + ξ w = (κ_w − κ_p)(x + u) + ξ w^n`, `ξ = ξ_p + ξ_w`, i.e.
`β E_t w_{t+1} − (1 + β + ξ) w_t + w_{t−1} = (κ_p − κ_w)(x_t + u_t) − ξ w^n_t`. -/
theorem wage_eq_general {P : SW} {w₀ : Ω → ℝ} {u wn π πw x w : ℕ → Ω → ℝ}
    (hpe : PriceEq 𝔼 P u wn π x w) (hwe : WageEq 𝔼 P u wn πw x w) (hwi : WageId w₀ π πw w)
    (hwa : 𝔼.Adapted w) (t : ℕ) (ω : Ω) :
    Zop 𝔼 P.beta w₀ w t ω + (P.xip + P.xiw) * w t ω =
      (P.kw - P.kp) * (x t ω + u t ω) + (P.xip + P.xiw) * wn t ω := by
  have hE : 𝔼.E t (π (t + 1)) ω - 𝔼.E t (πw (t + 1)) ω = w t ω - 𝔼.E t (w (t + 1)) ω := by
    have : π (t + 1) - πw (t + 1) = w t - w (t + 1) := by
      funext ω'
      have := hwi (t + 1) ω'
      simp only [lagW_succ] at this
      simp only [Pi.sub_apply]
      linarith
    rw [← Pi.sub_apply, ← map_sub, this, map_sub, hwa t]
    rfl
  have h1 := hpe t ω
  have h2 := hwe t ω
  have h3 := hwi t ω
  simp only [Zop]
  linear_combination h2 - h1 + h3 - P.beta * hE

/-- Woodford (2003), (2.20): the coefficient `a₁ = λ_x ξ + λ_p κ_p² + λ_w κ_w²`. -/
def ca1 (P : SW) : ℝ := P.lx * (P.xip + P.xiw) + P.lp * P.kp ^ 2 + P.lw * P.kw ^ 2

/-- Woodford (2003), (2.20): the coefficient `a₀ = Δ(λ_p κ_p + λ_w κ_w)`. -/
def ca0 (P : SW) : ℝ := Dst P * (P.lp * P.kp + P.lw * P.kw)

/-- Woodford (2003), (2.20): the coefficient `b₀ = Δ(λ_w ξ_w − λ_p ξ_p)`. -/
def cb0 (P : SW) : ℝ := Dst P * (P.lw * P.xiw - P.lp * P.xip)

/-- Woodford (2003), (2.20): the initial value `(𝒵w)_{t₀−1}` implied by the predetermined
`w_{t₀−1}`, `φ_{p,t₀−1}`, `φ_{w,t₀−1}`. -/
noncomputable def initS1 (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) : Ω → ℝ :=
  fun ω => (P.kw - P.kp) / P.lx * (P.kp * mp₀ ω + P.kw * mw₀ ω + P.lx * P.xstar) -
    (P.xip + P.xiw) * w₀ ω

/-- Woodford (2003), (2.20): the initial value `(𝒵²w)_{t₀−1}` implied by the predetermined
`w_{t₀−1}`, `φ_{p,t₀−1}`, `φ_{w,t₀−1}`. -/
noncomputable def initS2 (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) : Ω → ℝ :=
  fun ω => ((P.kw - P.kp) ^ 2 * (P.xip * mp₀ ω - P.xiw * mw₀ ω) -
    ca1 P * initS1 P w₀ mp₀ mw₀ ω - ca0 P * w₀ ω) / P.lx

/-- Woodford (2003), (2.20): the forcing of the cubic equation in the real wage, a combination of
`w^n`, `u` and their transforms `𝒵w^n`, `𝒵u`, `𝒵²w^n`, `𝒵²u` (zero initial values). -/
noncomputable def forcingF (P : SW) (u wn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => ca0 P * Zop 𝔼 P.beta (fun _ => 0) wn t ω +
    P.lx * (P.xip + P.xiw) * Zop 𝔼 P.beta (fun _ => 0) (Zop 𝔼 P.beta (fun _ => 0) wn) t ω +
    (P.kw - P.kp) * P.lx * Zop 𝔼 P.beta (fun _ => 0) (Zop 𝔼 P.beta (fun _ => 0) u) t ω +
    (P.xip + P.xiw) * ca0 P * wn t ω +
    P.lx * (P.xip + P.xiw) ^ 2 * Zop 𝔼 P.beta (fun _ => 0) wn t ω +
    (P.xip + P.xiw) * (P.kw - P.kp) * P.lx * Zop 𝔼 P.beta (fun _ => 0) u t ω -
    (P.kw - P.kp) * cb0 P * wn t ω

/-- **Woodford (2003), (2.11)–(2.19) ⇒ the cubic equation**: in any admissible plan satisfying the
first-order conditions (adapted multipliers, initial multipliers `mp₀, mw₀`), with `κ_w ≠ κ_p`,
the real wage solves `λ_x 𝒵³w + p₂ 𝒵²w + p₁ 𝒵w + p₀ w = F` — the characteristic polynomial is
`P(Z)` — with initial values `(w_{t₀−1}, initS1, initS2)`. -/
theorem foc_imp_cubic {P : SW} (hlx : P.lx ≠ 0) (hc : P.kw - P.kp ≠ 0) {w₀ mp₀ mw₀ : Ω → ℝ}
    {u wn π πw x w mp mw ups : ℕ → Ω → ℝ}
    (hp : PlanSW 𝔼 P w₀ u wn π πw x w) (hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups)
    (hmpa : 𝔼.Adapted mp) (hmwa : 𝔼.Adapted mw) :
    CubicR 𝔼 P.beta P.lx (cp2 P) (cp1 P) (cp0 P) w₀ (initS1 P w₀ mp₀ mw₀)
      (initS2 P w₀ mp₀ mw₀) (forcingF 𝔼 P u wn) w ∧
    ∀ t ω, (P.kw - P.kp) ^ 2 * (P.xip * mp t ω - P.xiw * mw t ω) =
      P.lx * Zop 𝔼 P.beta (initS1 P w₀ mp₀ mw₀) (Zop 𝔼 P.beta w₀ w) t ω +
      ca1 P * Zop 𝔼 P.beta w₀ w t ω + ca0 P * w t ω - ca0 P * wn t ω -
      P.lx * (P.xip + P.xiw) * Zop 𝔼 P.beta (fun _ => 0) wn t ω -
      (P.kw - P.kp) * P.lx * Zop 𝔼 P.beta (fun _ => 0) u t ω := by
  obtain ⟨hpe, hwe, hwi, -, -, -, hwa, -⟩ := hp
  set c := P.kw - P.kp with hcdef
  set ξ := P.xip + P.xiw with hξ
  set s1 := initS1 P w₀ mp₀ mw₀ with hs1
  set s2 := initS2 P w₀ mp₀ mw₀ with hs2
  -- E_t of the first-order conditions at t+1
  have hEf : ∀ t ω, P.lp * 𝔼.E t (π (t + 1)) ω + 𝔼.E t (mp (t + 1)) ω - mp t ω +
      𝔼.E t (ups (t + 1)) ω = 0 := by
    intro t ω
    have : P.lp • π (t + 1) + mp (t + 1) - mp t + ups (t + 1) = 0 := by
      funext ω'; have := (hfoc (t + 1) ω').1; simpa using this
    have h := congrFun (congrArg (𝔼.E t) this) ω
    simp only [map_add, map_sub, map_smul, hmpa t, map_zero] at h
    simpa using h
  have hEg : ∀ t ω, P.lw * 𝔼.E t (πw (t + 1)) ω + 𝔼.E t (mw (t + 1)) ω - mw t ω -
      𝔼.E t (ups (t + 1)) ω = 0 := by
    intro t ω
    have : P.lw • πw (t + 1) + mw (t + 1) - mw t - ups (t + 1) = 0 := by
      funext ω'; have := (hfoc (t + 1) ω').2.1; simpa using this
    have h := congrFun (congrArg (𝔼.E t) this) ω
    simp only [map_add, map_sub, map_smul, hmwa t, map_zero] at h
    simpa using h
  -- (E1), (E2)
  have E1 : ∀ t ω, Zop 𝔼 P.beta mp₀ mp t ω + (P.xip * mp t ω - P.xiw * mw t ω) =
      -(P.lp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) := by
    intro t ω
    obtain ⟨f1, -, -, f4⟩ := hfoc t ω
    have pe := hpe t ω
    have he := hEf t ω
    simp only [Zop]
    linear_combination f1 - P.beta * he - P.lp * pe - f4
  have E2 : ∀ t ω, Zop 𝔼 P.beta mw₀ mw t ω - (P.xip * mp t ω - P.xiw * mw t ω) =
      -(P.lw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω))) := by
    intro t ω
    obtain ⟨-, f2, -, f4⟩ := hfoc t ω
    have we := hwe t ω
    have he := hEg t ω
    simp only [Zop]
    linear_combination f2 - P.beta * he - P.lw * we + f4
  set z0 : ℕ → Ω → ℝ := fun _ _ => 0
  set i0 : Ω → ℝ := fun _ => 0
  set W1 := Zop 𝔼 P.beta w₀ w with hW1
  set W2 := Zop 𝔼 P.beta s1 W1 with hW2
  set Zn := Zop 𝔼 P.beta i0 wn with hZn
  set Zu := Zop 𝔼 P.beta i0 u with hZu
  have hx : ∀ t ω, c * (x t ω + u t ω) = W1 t ω + ξ * (w t ω - wn t ω) := fun t ω => by
    have := wage_eq_general 𝔼 hpe hwe hwi hwa t ω
    linear_combination -this
  -- (G) and (H)
  have hZX : ∀ t ω, Zop 𝔼 P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.kp * mp t ω + P.kw * mw t ω) t ω =
      P.kp * Zop 𝔼 P.beta mp₀ mp t ω + P.kw * Zop 𝔼 P.beta mw₀ mw t ω := fun t ω => by
    have := Zop_comb6 𝔼 P.beta P.kp P.kw 0 0 0 0 0 (y1 := mp) (y2 := mw) (i1 := mp₀)
      (i2 := mw₀) (y3 := z0) (y4 := z0) (y5 := z0)
      (y6 := z0) (i3 := i0) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := fun t ω => P.kp * mp t ω + P.kw * mw t ω)
      (z₀ := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => by ring) (fun ω => by ring) t ω
    rw [this]; ring
  have hZg : ∀ t ω, Zop 𝔼 P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω)
      (fun t ω => P.xip * mp t ω - P.xiw * mw t ω) t ω =
      P.xip * Zop 𝔼 P.beta mp₀ mp t ω - P.xiw * Zop 𝔼 P.beta mw₀ mw t ω := fun t ω => by
    have := Zop_comb6 𝔼 P.beta P.xip (-P.xiw) 0 0 0 0 0 (y1 := mp) (y2 := mw) (i1 := mp₀)
      (i2 := mw₀) (y3 := z0) (y4 := z0) (y5 := z0)
      (y6 := z0) (i3 := i0) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := fun t ω => P.xip * mp t ω - P.xiw * mw t ω)
      (z₀ := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (fun t ω => by ring) (fun ω => by ring) t ω
    rw [this]; ring
  -- `X = λ_x (x − x*)` as a combination of `W1, w, w^n, u`
  have hX : ∀ t ω, Zop 𝔼 P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.kp * mp t ω + P.kw * mw t ω) t ω * c =
      P.lx * W2 t ω + P.lx * ξ * W1 t ω - P.lx * ξ * Zn t ω - c * P.lx * Zu t ω := by
    intro t ω
    have := Zop_comb6 𝔼 P.beta (P.lx / c) (P.lx * ξ / c) (-(P.lx * ξ / c)) (-P.lx) 0 0
      (-(P.lx * P.xstar)) (y1 := W1) (y2 := w) (y3 := wn) (y4 := u) (y5 := z0) (y6 := z0)
      (i1 := s1) (i2 := w₀) (i3 := i0) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := fun t ω => P.kp * mp t ω + P.kw * mw t ω)
      (z₀ := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => ?_) (fun ω => ?_) t ω
    · rw [this]; field_simp; ring
    · have f3 := (hfoc t ω).2.2.1
      have h := hx t ω
      field_simp
      linear_combination (-c) * f3 + P.lx * h
    · simp only [hs1, initS1, i0]
      field_simp
      ring
  have gform : ∀ t ω, c ^ 2 * (P.xip * mp t ω - P.xiw * mw t ω) =
      P.lx * W2 t ω + ca1 P * W1 t ω + ca0 P * w t ω - ca0 P * wn t ω - P.lx * ξ * Zn t ω -
        c * P.lx * Zu t ω := by
    intro t ω
    have e1 := E1 t ω
    have e2 := E2 t ω
    have hz := hZX t ω
    have hXt := hX t ω
    have h := hx t ω
    simp only [ca1, ca0, Dst]
    linear_combination (-c) * (P.kp * e1 + P.kw * e2) - c * hz + hXt +
      (P.lp * P.kp ^ 2 + P.lw * P.kw ^ 2) * h
  set W3 := Zop 𝔼 P.beta s2 W2 with hW3
  set ZZn := Zop 𝔼 P.beta i0 Zn with hZZn
  set ZZu := Zop 𝔼 P.beta i0 Zu with hZZu
  have hZG : ∀ t ω, c ^ 2 * Zop 𝔼 P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω)
      (fun t ω => P.xip * mp t ω - P.xiw * mw t ω) t ω =
      P.lx * W3 t ω + ca1 P * W2 t ω + ca0 P * W1 t ω - ca0 P * Zn t ω - P.lx * ξ * ZZn t ω -
        c * P.lx * ZZu t ω := by
    intro t ω
    have := Zop_comb6 𝔼 P.beta (P.lx / c ^ 2) (ca1 P / c ^ 2) (ca0 P / c ^ 2)
      (-(ca0 P / c ^ 2)) (-(P.lx * ξ / c ^ 2)) (-(c * P.lx / c ^ 2)) 0
      (y1 := W2) (y2 := W1) (y3 := w) (y4 := wn) (y5 := Zn) (y6 := Zu)
      (i1 := s2) (i2 := s1) (i3 := w₀) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := fun t ω => P.xip * mp t ω - P.xiw * mw t ω)
      (z₀ := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (fun t ω => ?_) (fun ω => ?_) t ω
    · rw [this]; field_simp; ring
    · have := gform t ω
      field_simp
      linear_combination this
    · simp only [hs2, initS2, i0]
      field_simp
      ring
  refine ⟨fun t ω => ?_, fun t ω => gform t ω⟩
  have e1 := E1 t ω
  have e2 := E2 t ω
  have hg := hZg t ω
  have hG := hZG t ω
  have gf := gform t ω
  have h := hx t ω
  simp only [forcingF, cp2, cp1, cp0, ca1, ca0, cb0, Dst] at hG gf ⊢
  linear_combination c ^ 2 * (P.xip * e1 - P.xiw * e2) + c ^ 2 * hg - hG - ξ * gf +
    c * (P.lw * P.xiw * P.kw - P.lp * P.xip * P.kp) * h

/-! ### From a solution of the cubic equation back to the optimal plan -/

/-- Woodford (2003), (2.13) and (2.20): the output gap implied by the real wage,
`x = (𝒵w + ξ(w − w^n))/(κ_w − κ_p) − u`. -/
noncomputable def xOf (P : SW) (w₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (Zop 𝔼 P.beta w₀ w t ω + (P.xip + P.xiw) * (w t ω - wn t ω)) / (P.kw - P.kp) -
    u t ω

/-- Woodford (2003), (2.18)–(2.20): the combination `g = ξ_p φ_p − ξ_w φ_w` implied by the real
wage. -/
noncomputable def gOf (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (P.lx * Zop 𝔼 P.beta (initS1 P w₀ mp₀ mw₀) (Zop 𝔼 P.beta w₀ w) t ω +
    ca1 P * Zop 𝔼 P.beta w₀ w t ω + ca0 P * w t ω - ca0 P * wn t ω -
    P.lx * (P.xip + P.xiw) * Zop 𝔼 P.beta (fun _ => 0) wn t ω -
    (P.kw - P.kp) * P.lx * Zop 𝔼 P.beta (fun _ => 0) u t ω) / (P.kw - P.kp) ^ 2

/-- Woodford (2003), (2.18)–(2.19): the multiplier `φ_p = (ξ_w λ_x(x − x*) + κ_w g)/Δ`. -/
noncomputable def mpOf (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (P.xiw * (P.lx * (xOf 𝔼 P w₀ u wn w t ω - P.xstar)) +
    P.kw * gOf 𝔼 P w₀ mp₀ mw₀ u wn w t ω) / Dst P

/-- Woodford (2003), (2.18)–(2.19): the multiplier `φ_w = (ξ_p λ_x(x − x*) − κ_p g)/Δ`. -/
noncomputable def mwOf (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (P.xip * (P.lx * (xOf 𝔼 P w₀ u wn w t ω - P.xstar)) -
    P.kp * gOf 𝔼 P w₀ mp₀ mw₀ u wn w t ω) / Dst P

/-- Woodford (2003), (2.19): the multiplier `υ = ∑ βʲ E_t g_{t+j}`. -/
noncomputable def upsOf (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries P.beta (gOf 𝔼 P w₀ mp₀ mw₀ u wn w)

/-- Woodford (2003), (2.16): price inflation `π = −(Δφ_p + υ)/λ_p`. -/
noncomputable def piOf (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => -(mpOf 𝔼 P w₀ mp₀ mw₀ u wn w t ω - lagW mp₀ (mpOf 𝔼 P w₀ mp₀ mw₀ u wn w) t ω +
    upsOf 𝔼 P w₀ mp₀ mw₀ u wn w t ω) / P.lp

/-- Woodford (2003), (2.17): wage inflation `π^w = −(Δφ_w − υ)/λ_w`. -/
noncomputable def piwOf (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => -(mwOf 𝔼 P w₀ mp₀ mw₀ u wn w t ω - lagW mw₀ (mwOf 𝔼 P w₀ mp₀ mw₀ u wn w) t ω -
    upsOf 𝔼 P w₀ mp₀ mw₀ u wn w t ω) / P.lw

/-- Woodford (2003), (2.20): a linear combination of six bounded adapted processes plus a constant
is bounded and adapted. -/
theorem comb6_bdd_adapted (a1 a2 a3 a4 a5 a6 k : ℝ) {y1 y2 y3 y4 y5 y6 z : ℕ → Ω → ℝ}
    (h1 : 𝔼.Adapted y1) (h2 : 𝔼.Adapted y2) (h3 : 𝔼.Adapted y3) (h4 : 𝔼.Adapted y4)
    (h5 : 𝔼.Adapted y5) (h6 : 𝔼.Adapted y6) (b1 : BoundedProc y1) (b2 : BoundedProc y2)
    (b3 : BoundedProc y3) (b4 : BoundedProc y4) (b5 : BoundedProc y5) (b6 : BoundedProc y6)
    (hz : ∀ t ω, z t ω = a1 * y1 t ω + a2 * y2 t ω + a3 * y3 t ω + a4 * y4 t ω +
      a5 * y5 t ω + a6 * y6 t ω + k) : 𝔼.Adapted z ∧ BoundedProc z := by
  obtain ⟨M1, hM1⟩ := b1
  obtain ⟨M2, hM2⟩ := b2
  obtain ⟨M3, hM3⟩ := b3
  obtain ⟨M4, hM4⟩ := b4
  obtain ⟨M5, hM5⟩ := b5
  obtain ⟨M6, hM6⟩ := b6
  have hzf : ∀ t, z t = a1 • y1 t + a2 • y2 t + a3 • y3 t + a4 • y4 t + a5 • y5 t + a6 • y6 t +
      (fun _ => k) := fun t => by funext ω; rw [hz]; rfl
  refine ⟨fun t => ?_, ⟨|a1| * M1 + |a2| * M2 + |a3| * M3 + |a4| * M4 + |a5| * M5 +
    |a6| * M6 + |k|, fun t ω => ?_⟩⟩
  · rw [hzf t]
    simp only [map_add, map_smul, 𝔼.const, h1 t, h2 t, h3 t, h4 t, h5 t, h6 t]
  · rw [hz]
    have e : ∀ (a : ℝ) (v : ℝ) (M : ℝ), |v| ≤ M → |a * v| ≤ |a| * M := fun a v M h => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg a)
    have := e a1 _ _ (hM1 t ω)
    have := e a2 _ _ (hM2 t ω)
    have := e a3 _ _ (hM3 t ω)
    have := e a4 _ _ (hM4 t ω)
    have := e a5 _ _ (hM5 t ω)
    have := e a6 _ _ (hM6 t ω)
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ le_rfl
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    exact (abs_add_le _ _).trans (add_le_add (by assumption) (by assumption))

/-- Woodford (2003), (2.20): a linear combination of three bounded date-0 random variables plus a
constant is bounded and known at date 0. -/
theorem comb3_init (a1 a2 a3 k : ℝ) {y1 y2 y3 z : Ω → ℝ} (h1 : 𝔼.E 0 y1 = y1)
    (h2 : 𝔼.E 0 y2 = y2) (h3 : 𝔼.E 0 y3 = y3) (b1 : ∃ B, ∀ ω, |y1 ω| ≤ B)
    (b2 : ∃ B, ∀ ω, |y2 ω| ≤ B) (b3 : ∃ B, ∀ ω, |y3 ω| ≤ B)
    (hz : ∀ ω, z ω = a1 * y1 ω + a2 * y2 ω + a3 * y3 ω + k) :
    𝔼.E 0 z = z ∧ ∃ B, ∀ ω, |z ω| ≤ B := by
  have hc : 𝔼.Adapted (fun _ => z) ∧ BoundedProc (fun _ => z) := by
    obtain ⟨B1, hB1⟩ := b1
    obtain ⟨B2, hB2⟩ := b2
    obtain ⟨B3, hB3⟩ := b3
    refine comb6_bdd_adapted 𝔼 a1 a2 a3 0 0 0 k (y1 := fun _ => y1) (y2 := fun _ => y2)
      (y3 := fun _ => y3) (y4 := fun _ _ => 0) (y5 := fun _ _ => 0) (y6 := fun _ _ => 0)
      (fun t => E_of_known 𝔼 (Nat.zero_le t) h1) (fun t => E_of_known 𝔼 (Nat.zero_le t) h2)
      (fun t => E_of_known 𝔼 (Nat.zero_le t) h3) (fun t => 𝔼.const t 0) (fun t => 𝔼.const t 0)
      (fun t => 𝔼.const t 0) ⟨B1, fun _ ω => hB1 ω⟩ ⟨B2, fun _ ω => hB2 ω⟩ ⟨B3, fun _ ω => hB3 ω⟩
      ⟨0, by simp⟩ ⟨0, by simp⟩ ⟨0, by simp⟩ (fun t ω => ?_)
    rw [hz]; ring
  obtain ⟨ha, B, hB⟩ := hc
  exact ⟨ha 0, B, fun ω => hB 0 ω⟩

/-- **Woodford (2003), (2.11)–(2.19) ⇐ the cubic equation (construction of the optimal plan)**:
if the real wage `w` is a bounded adapted solution of the cubic equation with the initial values
implied by `(w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1})`, then `(piOf, piwOf, xOf, w)` is an admissible plan
satisfying the first-order conditions with the bounded adapted multipliers
`(mpOf, mwOf, upsOf)`. -/
theorem cubic_imp_foc {P : SW} (hβ0 : 0 ≤ P.beta) (hβ1 : P.beta < 1) (hlx : P.lx ≠ 0)
    (hlp : P.lp ≠ 0) (hlw : P.lw ≠ 0) (hc : P.kw - P.kp ≠ 0) (hD : Dst P ≠ 0)
    {w₀ mp₀ mw₀ : Ω → ℝ} (hw₀ : ∃ B, ∀ ω, |w₀ ω| ≤ B) (hmp₀ : ∃ B, ∀ ω, |mp₀ ω| ≤ B)
    (hmw₀ : ∃ B, ∀ ω, |mw₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀) (hmp₀a : 𝔼.E 0 mp₀ = mp₀)
    (hmw₀a : 𝔼.E 0 mw₀ = mw₀) {u wn w : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u)
    (hwn : BoundedProc wn) (hwna : 𝔼.Adapted wn)
    (hcub : CubicR 𝔼 P.beta P.lx (cp2 P) (cp1 P) (cp0 P) w₀ (initS1 P w₀ mp₀ mw₀)
      (initS2 P w₀ mp₀ mw₀) (forcingF 𝔼 P u wn) w) (hwa : 𝔼.Adapted w) (hwb : BoundedProc w) :
    PlanSW 𝔼 P w₀ u wn (piOf 𝔼 P w₀ mp₀ mw₀ u wn w) (piwOf 𝔼 P w₀ mp₀ mw₀ u wn w)
        (xOf 𝔼 P w₀ u wn w) w ∧
      FOCsw 𝔼 P mp₀ mw₀ (piOf 𝔼 P w₀ mp₀ mw₀ u wn w) (piwOf 𝔼 P w₀ mp₀ mw₀ u wn w)
        (xOf 𝔼 P w₀ u wn w) (mpOf 𝔼 P w₀ mp₀ mw₀ u wn w) (mwOf 𝔼 P w₀ mp₀ mw₀ u wn w)
        (upsOf 𝔼 P w₀ mp₀ mw₀ u wn w) ∧
      𝔼.Adapted (mpOf 𝔼 P w₀ mp₀ mw₀ u wn w) ∧ 𝔼.Adapted (mwOf 𝔼 P w₀ mp₀ mw₀ u wn w) ∧
      BoundedProc (mpOf 𝔼 P w₀ mp₀ mw₀ u wn w) ∧ BoundedProc (mwOf 𝔼 P w₀ mp₀ mw₀ u wn w) ∧
      BoundedProc (upsOf 𝔼 P w₀ mp₀ mw₀ u wn w) := by
  set c := P.kw - P.kp with hcdef
  set ξ := P.xip + P.xiw with hξ
  set s1 := initS1 P w₀ mp₀ mw₀ with hs1
  set s2 := initS2 P w₀ mp₀ mw₀ with hs2
  set i0 : Ω → ℝ := fun _ => 0 with hi0
  have i0a : 𝔼.E 0 i0 = i0 := 𝔼.const 0 0
  have i0b : ∃ B, ∀ ω, |i0 ω| ≤ B := ⟨0, fun ω => by simp [i0]⟩
  -- initial values
  obtain ⟨s1a, s1b⟩ := comb3_init 𝔼 (c / P.lx * P.kp) (c / P.lx * P.kw) (-ξ) (c * P.xstar)
    hmp₀a hmw₀a hw₀a hmp₀ hmw₀ hw₀ (z := s1) (fun ω => by
      simp only [hs1, initS1]; field_simp; ring)
  obtain ⟨s2a, s2b⟩ := comb3_init 𝔼 (c ^ 2 * P.xip / P.lx) (-(c ^ 2 * P.xiw / P.lx))
    (-(ca0 P / P.lx)) 0 hmp₀a hmw₀a hw₀a hmp₀ hmw₀ hw₀ (z := fun ω => s2 ω + ca1 P / P.lx * s1 ω)
    (fun ω => by simp only [hs2, initS2]; field_simp; ring)
  obtain ⟨s2a', s2b'⟩ := comb3_init 𝔼 1 (-(ca1 P / P.lx)) 0 0 s2a s1a i0a s2b s1b i0b
    (z := s2) (fun ω => by ring)
  -- the processes
  set W1 := Zop 𝔼 P.beta w₀ w with hW1
  set W2 := Zop 𝔼 P.beta s1 W1 with hW2
  set W3 := Zop 𝔼 P.beta s2 W2 with hW3
  set Zn := Zop 𝔼 P.beta i0 wn with hZn
  set Zu := Zop 𝔼 P.beta i0 u with hZu
  set ZZn := Zop 𝔼 P.beta i0 Zn with hZZn
  set ZZu := Zop 𝔼 P.beta i0 Zu with hZZu
  have aW1 := Zop_adapted 𝔼 P.beta hw₀a hwa
  have bW1 := Zop_bounded 𝔼 P.beta hβ0 hw₀ hwb
  have aW2 := Zop_adapted 𝔼 P.beta s1a aW1
  have bW2 := Zop_bounded 𝔼 P.beta hβ0 s1b bW1
  have aZn := Zop_adapted 𝔼 P.beta i0a hwna
  have bZn := Zop_bounded 𝔼 P.beta hβ0 i0b hwn
  have aZu := Zop_adapted 𝔼 P.beta i0a hua
  have bZu := Zop_bounded 𝔼 P.beta hβ0 i0b hu
  set x := xOf 𝔼 P w₀ u wn w with hx
  set g := gOf 𝔼 P w₀ mp₀ mw₀ u wn w with hg
  set mp := mpOf 𝔼 P w₀ mp₀ mw₀ u wn w with hmp
  set mw := mwOf 𝔼 P w₀ mp₀ mw₀ u wn w with hmw
  set ups := upsOf 𝔼 P w₀ mp₀ mw₀ u wn w with hups
  set π := piOf 𝔼 P w₀ mp₀ mw₀ u wn w with hπ
  set πw := piwOf 𝔼 P w₀ mp₀ mw₀ u wn w with hπw
  obtain ⟨xa, xb⟩ := comb6_bdd_adapted 𝔼 (1 / c) (ξ / c) (-(ξ / c)) (-1) 0 0 0 aW1 hwa hwna hua
    hua hua bW1 hwb hwn hu hu hu (z := x) (fun t ω => by
      simp only [hx, xOf, ← hcdef, ← hξ]; field_simp; ring)
  obtain ⟨ga, gb⟩ := comb6_bdd_adapted 𝔼 (P.lx / c ^ 2) (ca1 P / c ^ 2) (ca0 P / c ^ 2)
    (-(ca0 P / c ^ 2)) (-(P.lx * ξ / c ^ 2)) (-(c * P.lx / c ^ 2)) 0 aW2 aW1 hwa hwna aZn aZu
    bW2 bW1 hwb hwn bZn bZu (z := g) (fun t ω => by
      simp only [hg, gOf, ← hcdef, ← hξ, ← hs1]; field_simp; ring)
  obtain ⟨mpa, mpb⟩ := comb6_bdd_adapted 𝔼 (P.xiw * P.lx / Dst P) (P.kw / Dst P) 0 0 0 0
    (-(P.xiw * P.lx * P.xstar / Dst P)) xa ga xa xa xa xa xb gb xb xb xb xb (z := mp)
    (fun t ω => by simp only [hmp, mpOf]; field_simp; ring)
  obtain ⟨mwa, mwb⟩ := comb6_bdd_adapted 𝔼 (P.xip * P.lx / Dst P) (-(P.kp / Dst P)) 0 0 0 0
    (-(P.xip * P.lx * P.xstar / Dst P)) xa ga xa xa xa xa xb gb xb xb xb xb (z := mw)
    (fun t ω => by simp only [hmw, mwOf]; field_simp; ring)
  obtain ⟨G, hG⟩ := gb
  have upsa : 𝔼.Adapted ups := 𝔼.forwardSeries_adapted hβ0 hβ1 hG
  have upsb : BoundedProc ups := 𝔼.forwardSeries_bounded hβ0 hβ1 hG
  have upss := 𝔼.forwardSeries_solves hβ0 hβ1 hG ga
  have lmpa := lagW_adapted 𝔼 hmp₀a mpa
  have lmwa := lagW_adapted 𝔼 hmw₀a mwa
  obtain ⟨Bp, hBp⟩ := hmp₀
  obtain ⟨Bw, hBw⟩ := hmw₀
  obtain ⟨Mp, hMp⟩ := mpb
  obtain ⟨Mw, hMw⟩ := mwb
  have lmpb : BoundedProc (lagW mp₀ mp) := ⟨_, lagW_bounded hBp hMp⟩
  have lmwb : BoundedProc (lagW mw₀ mw) := ⟨_, lagW_bounded hBw hMw⟩
  obtain ⟨πa, πb⟩ := comb6_bdd_adapted 𝔼 (-1 / P.lp) (1 / P.lp) (-1 / P.lp) 0 0 0 0 mpa lmpa
    upsa upsa upsa upsa ⟨Mp, hMp⟩ lmpb upsb upsb upsb upsb (z := π)
    (fun t ω => by simp only [hπ, piOf]; field_simp; ring)
  obtain ⟨πwa, πwb⟩ := comb6_bdd_adapted 𝔼 (-1 / P.lw) (1 / P.lw) (1 / P.lw) 0 0 0 0 mwa lmwa
    upsa upsa upsa upsa ⟨Mw, hMw⟩ lmwb upsb upsb upsb upsb (z := πw)
    (fun t ω => by simp only [hπw, piwOf]; field_simp; ring)
  have hD' : P.kp * P.xiw + P.kw * P.xip ≠ 0 := hD
  have hD2 : P.xiw * P.kp + P.kw * P.xip ≠ 0 := by intro h; apply hD'; linarith
  have hD3 : P.xip * P.kw + P.xiw * P.kp ≠ 0 := by intro h; apply hD'; linarith
  have hD4 : P.kw * P.xip + P.kp * P.xiw ≠ 0 := by intro h; apply hD'; linarith
  have hDi : (P.kp * P.xiw + P.kw * P.xip) * (P.kp * P.xiw + P.kw * P.xip)⁻¹ = 1 :=
    mul_inv_cancel₀ hD'
  set z0 : ℕ → Ω → ℝ := fun _ _ => 0
  -- basic identities
  have hS : ∀ t ω, c * (x t ω + u t ω) = W1 t ω + ξ * (w t ω - wn t ω) := fun t ω => by
    simp only [hx, xOf, ← hcdef, ← hξ]; field_simp; ring
  have hcg : ∀ t ω, c ^ 2 * g t ω = P.lx * W2 t ω + ca1 P * W1 t ω + ca0 P * w t ω -
      ca0 P * wn t ω - P.lx * ξ * Zn t ω - c * P.lx * Zu t ω := fun t ω => by
    simp only [hg, gOf, ← hcdef, ← hξ, ← hs1]; field_simp; rfl
  have hgmp : ∀ t ω, P.xip * mp t ω - P.xiw * mw t ω = g t ω := fun t ω => by
    simp only [hmp, mpOf, hmw, mwOf, Dst, ← hg]
    linear_combination (g t ω) * hDi
  have ZX : ∀ t ω, c * Zop 𝔼 P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.lx * (x t ω - P.xstar)) t ω =
      P.lx * W2 t ω + P.lx * ξ * W1 t ω - P.lx * ξ * Zn t ω - c * P.lx * Zu t ω := by
    intro t ω
    have := Zop_comb6 𝔼 P.beta (P.lx / c) (P.lx * ξ / c) (-(P.lx * ξ / c)) (-P.lx) 0 0
      (-(P.lx * P.xstar)) (y1 := W1) (y2 := w) (y3 := wn) (y4 := u) (y5 := z0) (y6 := z0)
      (i1 := s1) (i2 := w₀) (i3 := i0) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := fun t ω => P.lx * (x t ω - P.xstar))
      (z₀ := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => ?_) (fun ω => ?_) t ω
    · rw [this]; field_simp; ring
    · have h := hS t ω
      field_simp
      linear_combination P.lx * h
    · simp only [hs1, initS1, i0, ← hcdef, ← hξ]
      field_simp
      ring
  have ZG : ∀ t ω, c ^ 2 * Zop 𝔼 P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω =
      P.lx * W3 t ω + ca1 P * W2 t ω + ca0 P * W1 t ω - ca0 P * Zn t ω - P.lx * ξ * ZZn t ω -
        c * P.lx * ZZu t ω := by
    intro t ω
    have := Zop_comb6 𝔼 P.beta (P.lx / c ^ 2) (ca1 P / c ^ 2) (ca0 P / c ^ 2)
      (-(ca0 P / c ^ 2)) (-(P.lx * ξ / c ^ 2)) (-(c * P.lx / c ^ 2)) 0
      (y1 := W2) (y2 := W1) (y3 := w) (y4 := wn) (y5 := Zn) (y6 := Zu)
      (i1 := s2) (i2 := s1) (i3 := w₀) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := g) (z₀ := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (fun t ω => ?_) (fun ω => ?_) t ω
    · rw [this]; field_simp; ring
    · have := hcg t ω
      field_simp
      linear_combination this
    · simp only [hs2, initS2, i0, ← hcdef, ← hs1]
      field_simp
      ring
  have Zmp : ∀ t ω, Dst P * Zop 𝔼 P.beta mp₀ mp t ω = P.xiw * Zop 𝔼 P.beta
      (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => P.lx * (x t ω - P.xstar)) t ω +
      P.kw * Zop 𝔼 P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω := by
    intro t ω
    have := Zop_comb6 𝔼 P.beta (P.xiw / Dst P) (P.kw / Dst P) 0 0 0 0 0
      (y1 := fun t ω => P.lx * (x t ω - P.xstar)) (y2 := g) (y3 := z0) (y4 := z0) (y5 := z0)
      (y6 := z0) (i1 := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (i2 := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (i3 := i0) (i4 := i0) (i5 := i0)
      (i6 := i0) (z := mp) (z₀ := mp₀) (fun t ω => ?_) (fun ω => ?_) t ω
    · rw [this]; field_simp; ring
    · simp only [hmp, mpOf, ← hx, ← hg]; field_simp; ring
    · simp only [Dst]; linear_combination (-mp₀ ω) * hDi
  have Zmw : ∀ t ω, Dst P * Zop 𝔼 P.beta mw₀ mw t ω = P.xip * Zop 𝔼 P.beta
      (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => P.lx * (x t ω - P.xstar)) t ω -
      P.kp * Zop 𝔼 P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω := by
    intro t ω
    have := Zop_comb6 𝔼 P.beta (P.xip / Dst P) (-(P.kp / Dst P)) 0 0 0 0 0
      (y1 := fun t ω => P.lx * (x t ω - P.xstar)) (y2 := g) (y3 := z0) (y4 := z0) (y5 := z0)
      (y6 := z0) (i1 := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (i2 := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (i3 := i0) (i4 := i0) (i5 := i0)
      (i6 := i0) (z := mw) (z₀ := mw₀) (fun t ω => ?_) (fun ω => ?_) t ω
    · rw [this]; field_simp; ring
    · simp only [hmw, mwOf, ← hx, ← hg]; field_simp; ring
    · simp only [Dst]; linear_combination (-mw₀ ω) * hDi
  -- (G) and (H)
  have G : ∀ t ω, Zop 𝔼 P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.lx * (x t ω - P.xstar)) t ω = c * g t ω -
      P.lp * P.kp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω)) -
      P.lw * P.kw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)) := by
    intro t ω
    have h1 := ZX t ω
    have h2 := hcg t ω
    have h3 := hS t ω
    have : c * (Zop 𝔼 P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.lx * (x t ω - P.xstar)) t ω - (c * g t ω -
      P.lp * P.kp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω)) -
      P.lw * P.kw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)))) = 0 := by
      simp only [ca1, ca0, Dst] at h2
      rw [hcdef, hξ] at *
      linear_combination h1 - h2 + (P.lp * P.kp ^ 2 + P.lw * P.kw ^ 2) * h3
    have := (mul_eq_zero.1 this).resolve_left hc
    linarith
  have H : ∀ t ω, Zop 𝔼 P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω =
      -(P.lp * P.xip * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) +
      P.lw * P.xiw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)) - ξ * g t ω := by
    intro t ω
    have h1 := ZG t ω
    have h2 := hcg t ω
    have h3 := hS t ω
    have h4 : P.lx * W3 t ω + cp2 P * W2 t ω + cp1 P * W1 t ω + cp0 P * w t ω =
        ca0 P * Zn t ω + P.lx * ξ * ZZn t ω + c * P.lx * ZZu t ω + ξ * ca0 P * wn t ω +
        P.lx * ξ ^ 2 * Zn t ω + ξ * c * P.lx * Zu t ω - c * cb0 P * wn t ω := hcub t ω
    have : c ^ 2 * (Zop 𝔼 P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω -
      (-(P.lp * P.xip * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) +
      P.lw * P.xiw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)) - ξ * g t ω)) =
        0 := by
      simp only [cp2, cp1, cp0, ca1, ca0, cb0, Dst] at h1 h2 h4
      rw [hcdef, hξ] at *
      linear_combination h1 + (P.xip + P.xiw) * h2 + h4 -
        (P.kw - P.kp) * (P.lw * P.xiw * P.kw - P.lp * P.xip * P.kp) * h3
    have := (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hc)
    linarith
  have E1 : ∀ t ω, Zop 𝔼 P.beta mp₀ mp t ω + g t ω =
      -(P.lp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) := by
    intro t ω
    have h1 := Zmp t ω
    have h2 := G t ω
    have h3 := H t ω
    have : Dst P * (Zop 𝔼 P.beta mp₀ mp t ω + g t ω +
        P.lp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) = 0 := by
      simp only [Dst] at *
      rw [hcdef, hξ] at *
      linear_combination h1 + P.xiw * h2 + P.kw * h3
    have := (mul_eq_zero.1 this).resolve_left hD
    linarith
  have E2 : ∀ t ω, Zop 𝔼 P.beta mw₀ mw t ω - g t ω =
      -(P.lw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω))) := by
    intro t ω
    have h1 := Zmw t ω
    have h2 := G t ω
    have h3 := H t ω
    have : Dst P * (Zop 𝔼 P.beta mw₀ mw t ω - g t ω +
        P.lw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω))) = 0 := by
      simp only [Dst] at *
      rw [hcdef, hξ] at *
      linear_combination h1 + P.xip * h2 - P.kp * h3
    have := (mul_eq_zero.1 this).resolve_left hD
    linarith
  -- the first-order conditions
  have f1 : ∀ t ω, P.lp * π t ω + mp t ω - lagW mp₀ mp t ω + ups t ω = 0 := by
    intro t ω
    simp only [hπ, piOf, ← hmp, ← hups]
    field_simp
    ring
  have f2 : ∀ t ω, P.lw * πw t ω + mw t ω - lagW mw₀ mw t ω - ups t ω = 0 := by
    intro t ω
    simp only [hπw, piwOf, ← hmw, ← hups]
    field_simp
    ring
  have f4 : ∀ t ω, ups t ω = P.xip * mp t ω - P.xiw * mw t ω +
      P.beta * 𝔼.E t (ups (t + 1)) ω := by
    intro t ω
    have h : ups t ω = P.beta * 𝔼.E t (ups (t + 1)) ω + g t ω := congrFun (upss t) ω
    rw [hgmp t ω]
    linarith
  have hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups := by
    intro t ω
    refine ⟨f1 t ω, f2 t ω, ?_, f4 t ω⟩
    simp only [hmp, mpOf, hmw, mwOf, Dst, ← hx, ← hg]
    linear_combination (-(P.lx * (x t ω - P.xstar))) * hDi
  -- E_t of next-period inflation
  have hEπ : ∀ t ω, P.lp * 𝔼.E t (π (t + 1)) ω =
      -(𝔼.E t (mp (t + 1)) ω - mp t ω + 𝔼.E t (ups (t + 1)) ω) := by
    intro t ω
    have hf : P.lp • π (t + 1) = -(mp (t + 1) - mp t + ups (t + 1)) := by
      funext ω'
      have := f1 (t + 1) ω'
      simp only [lagW_succ] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
      linarith
    have := congrFun (congrArg (𝔼.E t) hf) ω
    simp only [map_smul, map_neg, map_add, map_sub, mpa t, Pi.smul_apply, smul_eq_mul,
      Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this
    linarith
  have hEπw : ∀ t ω, P.lw * 𝔼.E t (πw (t + 1)) ω =
      -(𝔼.E t (mw (t + 1)) ω - mw t ω - 𝔼.E t (ups (t + 1)) ω) := by
    intro t ω
    have hf : P.lw • πw (t + 1) = -(mw (t + 1) - mw t - ups (t + 1)) := by
      funext ω'
      have := f2 (t + 1) ω'
      simp only [lagW_succ] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.sub_apply]
      linarith
    have := congrFun (congrArg (𝔼.E t) hf) ω
    simp only [map_smul, map_neg, map_sub, mwa t, Pi.smul_apply, smul_eq_mul,
      Pi.neg_apply, Pi.sub_apply] at this
    linarith
  have hpe : PriceEq 𝔼 P u wn π x w := by
    intro t ω
    have h1 := E1 t ω
    have h2 := hEπ t ω
    have h3 := f1 t ω
    have h4 := f4 t ω
    have h5 := hgmp t ω
    have : P.lp * (π t ω - (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω) +
        P.beta * 𝔼.E t (π (t + 1)) ω)) = 0 := by
      simp only [Zop] at h1
      linear_combination h3 - h1 - P.beta * h2 - h4 - h5
    have := (mul_eq_zero.1 this).resolve_left hlp
    linarith
  have hwe : WageEq 𝔼 P u wn πw x w := by
    intro t ω
    have h1 := E2 t ω
    have h2 := hEπw t ω
    have h3 := f2 t ω
    have h4 := f4 t ω
    have h5 := hgmp t ω
    have : P.lw * (πw t ω - (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω) +
        P.beta * 𝔼.E t (πw (t + 1)) ω)) = 0 := by
      simp only [Zop] at h1
      linear_combination h3 - h1 - P.beta * h2 + h4 + h5
    have := (mul_eq_zero.1 this).resolve_left hlw
    linarith
  -- the real-wage identity, by forward uniqueness
  have hwi : WageId w₀ π πw w := by
    set d : ℕ → Ω → ℝ := fun t ω => w t ω - lagW w₀ w t ω - πw t ω + π t ω with hd
    have hdE : ∀ t, d t = P.beta • 𝔼.E t (d (t + 1)) + (fun _ _ => (0 : ℝ)) t := by
      intro t
      funext ω
      have hE : 𝔼.E t (d (t + 1)) ω = 𝔼.E t (w (t + 1)) ω - w t ω - 𝔼.E t (πw (t + 1)) ω +
          𝔼.E t (π (t + 1)) ω := by
        have : d (t + 1) = w (t + 1) - w t - πw (t + 1) + π (t + 1) := rfl
        rw [this]
        simp only [map_add, map_sub, hwa t, Pi.add_apply, Pi.sub_apply]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE]
      have h1 := hpe t ω
      have h2 := hwe t ω
      have h3 := hS t ω
      simp only [hd]
      have hW : W1 t ω = (1 + P.beta) * w t ω - P.beta * 𝔼.E t (w (t + 1)) ω -
          lagW w₀ w t ω := rfl
      rw [hcdef, hξ] at *
      linear_combination h1 - h2 - hW - h3
    have lwb : BoundedProc (lagW w₀ w) := by
      obtain ⟨B, hB⟩ := hw₀
      obtain ⟨M, hM⟩ := hwb
      exact ⟨_, lagW_bounded hB hM⟩
    obtain ⟨db0, db⟩ := comb6_bdd_adapted 𝔼 1 (-1) (-1) 1 0 0 0 hwa (lagW_adapted 𝔼 hw₀a hwa)
      πwa πa πa πa hwb lwb πwb πb πb πb (z := d)
      (fun t ω => by simp only [hd]; ring)
    have hz := 𝔼.forward_unique (u := fun _ _ => 0) (by rw [abs_of_nonneg hβ0]; exact hβ1)
      hdE (z₂ := fun _ _ => 0) (fun t => by funext ω; simp [𝔼.const t 0]) db
      ⟨0, fun _ _ => by simp⟩
    intro t ω
    have := congrFun (congrFun hz t) ω
    simp only [hd] at this
    linarith
  exact ⟨⟨hpe, hwe, hwi, πa, πwa, xa, hwa, πb, πwb, xb, hwb⟩, hfoc, mpa, mwa, ⟨Mp, hMp⟩,
    ⟨Mw, hMw⟩, upsb⟩

/-! ### Determinacy of the optimal plan (`κ_w ≠ κ_p`) -/

/-- Woodford (2003), (2.20): the initial values `initS1`, `initS2` are bounded and known at date 0
when the predetermined data are. -/
theorem initS_bdd_known {P : SW} (hlx : P.lx ≠ 0) {w₀ mp₀ mw₀ : Ω → ℝ}
    (hw₀ : ∃ B, ∀ ω, |w₀ ω| ≤ B) (hmp₀ : ∃ B, ∀ ω, |mp₀ ω| ≤ B)
    (hmw₀ : ∃ B, ∀ ω, |mw₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀) (hmp₀a : 𝔼.E 0 mp₀ = mp₀)
    (hmw₀a : 𝔼.E 0 mw₀ = mw₀) :
    (𝔼.E 0 (initS1 P w₀ mp₀ mw₀) = initS1 P w₀ mp₀ mw₀ ∧
      ∃ B, ∀ ω, |initS1 P w₀ mp₀ mw₀ ω| ≤ B) ∧
    (𝔼.E 0 (initS2 P w₀ mp₀ mw₀) = initS2 P w₀ mp₀ mw₀ ∧
      ∃ B, ∀ ω, |initS2 P w₀ mp₀ mw₀ ω| ≤ B) := by
  set c := P.kw - P.kp with hcdef
  set ξ := P.xip + P.xiw with hξ
  have i0a : 𝔼.E 0 (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := 𝔼.const 0 0
  have i0b : ∃ B, ∀ ω : Ω, |(fun _ : Ω => (0 : ℝ)) ω| ≤ B := ⟨0, fun ω => by simp⟩
  obtain ⟨s1a, s1b⟩ := comb3_init 𝔼 (c / P.lx * P.kp) (c / P.lx * P.kw) (-ξ) (c * P.xstar)
    hmp₀a hmw₀a hw₀a hmp₀ hmw₀ hw₀ (z := initS1 P w₀ mp₀ mw₀) (fun ω => by
      simp only [initS1, ← hcdef, ← hξ]; field_simp; ring)
  obtain ⟨s2a, s2b⟩ := comb3_init 𝔼 (c ^ 2 * P.xip / P.lx) (-(c ^ 2 * P.xiw / P.lx))
    (-(ca0 P / P.lx)) 0 hmp₀a hmw₀a hw₀a hmp₀ hmw₀ hw₀
    (z := fun ω => initS2 P w₀ mp₀ mw₀ ω + ca1 P / P.lx * initS1 P w₀ mp₀ mw₀ ω)
    (fun ω => by simp only [initS2, ← hcdef]; field_simp; ring)
  obtain ⟨s2a', s2b'⟩ := comb3_init 𝔼 1 (-(ca1 P / P.lx)) 0 0 s2a s1a i0a s2b s1b i0b
    (z := initS2 P w₀ mp₀ mw₀) (fun ω => by ring)
  exact ⟨⟨s1a, s1b⟩, ⟨s2a', s2b'⟩⟩

/-- Woodford (2003), (2.20): the forcing `F` is bounded and adapted. -/
theorem forcingF_bdd_adapted {P : SW} (hβ0 : 0 ≤ P.beta) {u wn : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) (hwn : BoundedProc wn) (hwna : 𝔼.Adapted wn) :
    𝔼.Adapted (forcingF 𝔼 P u wn) ∧ BoundedProc (forcingF 𝔼 P u wn) := by
  have i0a : 𝔼.E 0 (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := 𝔼.const 0 0
  have i0b : ∃ B, ∀ ω : Ω, |(fun _ : Ω => (0 : ℝ)) ω| ≤ B := ⟨0, fun ω => by simp⟩
  have aZn := Zop_adapted 𝔼 P.beta i0a hwna
  have bZn := Zop_bounded 𝔼 P.beta hβ0 i0b hwn
  have aZu := Zop_adapted 𝔼 P.beta i0a hua
  have bZu := Zop_bounded 𝔼 P.beta hβ0 i0b hu
  have aZZn := Zop_adapted 𝔼 P.beta i0a aZn
  have bZZn := Zop_bounded 𝔼 P.beta hβ0 i0b bZn
  have aZZu := Zop_adapted 𝔼 P.beta i0a aZu
  have bZZu := Zop_bounded 𝔼 P.beta hβ0 i0b bZu
  exact comb6_bdd_adapted 𝔼 (ca0 P + P.lx * (P.xip + P.xiw) ^ 2) (P.lx * (P.xip + P.xiw))
    ((P.kw - P.kp) * P.lx) ((P.xip + P.xiw) * ca0 P - (P.kw - P.kp) * cb0 P)
    ((P.xip + P.xiw) * (P.kw - P.kp) * P.lx) 0 0 aZn aZZn aZZu hwna aZu aZu bZn bZZn bZZu hwn
    bZu bZu (fun t ω => by simp only [forcingF]; ring)

/-- Woodford (2003), (2.20): with Vieta's relations, `P(Z) = λ_x (Z − Z₁)(Z − Z₂)(Z − Z₃)`. -/
theorem charP_factor {P : SW} (hlx : P.lx ≠ 0) {Z1 Z2 Z3 : ℂ}
    (hv1 : Z1 + Z2 + Z3 = ((-(cp2 P / P.lx) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((cp1 P / P.lx : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(cp0 P / P.lx) : ℝ) : ℂ)) (Z : ℂ) :
    charP P Z = P.lx * (Z - Z1) * (Z - Z2) * (Z - Z3) := by
  have hl : (P.lx : ℂ) ≠ 0 := by exact_mod_cast hlx
  rw [charP_expand]
  push_cast at hv1 hv2 hv3
  have e1 : (P.lx : ℂ) * (Z1 + Z2 + Z3) = -cp2 P := by rw [hv1]; field_simp
  have e2 : (P.lx : ℂ) * (Z1 * Z2 + Z1 * Z3 + Z2 * Z3) = cp1 P := by rw [hv2]; field_simp
  have e3 : (P.lx : ℂ) * (Z1 * Z2 * Z3) = -cp0 P := by rw [hv3]; field_simp
  linear_combination Z ^ 2 * e1 - Z * e2 + e3

/-- **Woodford (2003), (2.11)–(2.19), `κ_w ≠ κ_p` (DETERMINACY OF THE OPTIMAL PLAN)**: under the
root condition `StableRoots P` (every root of `P(Z)` has a stable `μ`; equivalently every root
lies outside the ellipse, `stable_iff_ellForm`), for all bounded adapted disturbances and bounded
date-0 predetermined values `w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1}`, the first-order conditions and
(2.11)–(2.13) have exactly one bounded adapted solution (plan and multipliers). -/
theorem foc_existsUnique {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1) (hlx : 0 < P.lx)
    (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw) (hxip : 0 < P.xip)
    (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P) {u wn : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) (hwn : BoundedProc wn) (hwna : 𝔼.Adapted wn)
    {w₀ mp₀ mw₀ : Ω → ℝ} (hw₀ : ∃ B, ∀ ω, |w₀ ω| ≤ B) (hmp₀ : ∃ B, ∀ ω, |mp₀ ω| ≤ B)
    (hmw₀ : ∃ B, ∀ ω, |mw₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀) (hmp₀a : 𝔼.E 0 mp₀ = mp₀)
    (hmw₀a : 𝔼.E 0 mw₀ = mw₀) :
    ∃ π πw x w mp mw ups, (PlanSW 𝔼 P w₀ u wn π πw x w ∧ FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups ∧
      𝔼.Adapted mp ∧ 𝔼.Adapted mw ∧ BoundedProc mp ∧ BoundedProc mw ∧ BoundedProc ups) ∧
    ∀ π' πw' x' w' mp' mw' ups', PlanSW 𝔼 P w₀ u wn π' πw' x' w' →
      FOCsw 𝔼 P mp₀ mw₀ π' πw' x' mp' mw' ups' → 𝔼.Adapted mp' → 𝔼.Adapted mw' →
      BoundedProc ups' →
      π' = π ∧ πw' = πw ∧ x' = x ∧ w' = w ∧ mp' = mp ∧ mw' = mw ∧ ups' = ups := by
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD : Dst P ≠ 0 := by unfold Dst; positivity
  obtain ⟨Z1, Z2, Z3, hv1, hv2, hv3⟩ := cubic_vieta_exists (p2 := cp2 P) (p1 := cp1 P)
    (p0 := cp0 P) hlx.ne'
  have hfac := charP_factor hlx.ne' hv1 hv2 hv3
  obtain ⟨μ1, r1, n1⟩ := hR Z1 (by rw [hfac]; ring)
  obtain ⟨μ2, r2, n2⟩ := hR Z2 (by rw [hfac]; ring)
  obtain ⟨μ3, r3, n3⟩ := hR Z3 (by rw [hfac]; ring)
  obtain ⟨⟨s1a, s1b⟩, ⟨s2a, s2b⟩⟩ := initS_bdd_known 𝔼 (P := P) hlx.ne' hw₀ hmp₀ hmw₀ hw₀a
    hmp₀a hmw₀a
  obtain ⟨Fa, Fb⟩ := forcingF_bdd_adapted 𝔼 (P := P) hβ0.le hu hua hwn hwna
  obtain ⟨w, ⟨hcub, hwa, hwb⟩, hwu⟩ := cubicR_existsUnique 𝔼 hβ0.le hβ1 hlx.ne' hv1 hv2 hv3
    r1 n1 r2 n2 r3 n3 Fb Fa hw₀ s1b s2b hw₀a s1a s2a
  obtain ⟨hplan, hfoc, mpa, mwa, mpb, mwb, upsb⟩ := cubic_imp_foc 𝔼 hβ0.le hβ1 hlx.ne'
    hlp.ne' hlw.ne' hc hD hw₀ hmp₀ hmw₀ hw₀a hmp₀a hmw₀a hu hua hwn hwna hcub hwa hwb
  refine ⟨_, _, _, w, _, _, _, ⟨hplan, hfoc, mpa, mwa, mpb, mwb, upsb⟩,
    fun π' πw' x' w' mp' mw' ups' hp' hfoc' hmpa' hmwa' hupsb' => ?_⟩
  obtain ⟨hcub', hgf'⟩ := foc_imp_cubic 𝔼 hlx.ne' hc hp' hfoc' hmpa' hmwa'
  have hw' : w' = w := hwu w' ⟨hcub', hp'.2.2.2.2.2.2.1, hp'.2.2.2.2.2.2.2.2.2.2⟩
  subst hw'
  have hx' : x' = xOf 𝔼 P w₀ u wn w' := by
    funext t ω
    have := wage_eq_general 𝔼 hp'.1 hp'.2.1 hp'.2.2.1 hp'.2.2.2.2.2.2.1 t ω
    simp only [xOf]
    field_simp
    linarith
  have hg' : ∀ t ω, P.xip * mp' t ω - P.xiw * mw' t ω = gOf 𝔼 P w₀ mp₀ mw₀ u wn w' t ω := by
    intro t ω
    have := hgf' t ω
    simp only [gOf]
    field_simp
    linarith
  have hD' : P.kp * P.xiw + P.kw * P.xip ≠ 0 := hD
  have hmp' : mp' = mpOf 𝔼 P w₀ mp₀ mw₀ u wn w' := by
    funext t ω
    have h1 := (hfoc' t ω).2.2.1
    have h2 := hg' t ω
    simp only [mpOf, Dst, ← hx']
    field_simp
    have h3 := congrFun (congrFun hx' t) ω
    rw [hx'] at h1
    linear_combination (-P.xiw) * h1 + P.kw * h2 - P.xiw * P.lx * h3
  have hmw' : mw' = mwOf 𝔼 P w₀ mp₀ mw₀ u wn w' := by
    funext t ω
    have h1 := (hfoc' t ω).2.2.1
    have h2 := hg' t ω
    simp only [mwOf, Dst, ← hx']
    field_simp
    have h3 := congrFun (congrFun hx' t) ω
    rw [hx'] at h1
    linear_combination (-P.xip) * h1 - P.kp * h2 - P.xip * P.lx * h3
  -- the forward multiplier
  obtain ⟨Mp, hMp⟩ := mpb
  obtain ⟨Mw, hMw⟩ := mwb
  have hgb : ∀ t ω, |gOf 𝔼 P w₀ mp₀ mw₀ u wn w' t ω| ≤ |P.xip| * Mp + |P.xiw| * Mw := by
    intro t ω
    rw [← hg' t ω, hmp', hmw']
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMp t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMw t ω) (abs_nonneg _)
  have hga : 𝔼.Adapted (gOf 𝔼 P w₀ mp₀ mw₀ u wn w') := by
    intro t
    have : gOf 𝔼 P w₀ mp₀ mw₀ u wn w' t = P.xip • mp' t - P.xiw • mw' t := by
      funext ω; rw [← hg' t ω]; rfl
    rw [this, map_sub, map_smul, map_smul, hmpa' t, hmwa' t]
  have hups' : ups' = upsOf 𝔼 P w₀ mp₀ mw₀ u wn w' := by
    refine 𝔼.eq_forwardSeries hβ0.le hβ1 hgb hga (fun t => ?_) hupsb'
    funext ω
    have h := (hfoc' t ω).2.2.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hg' t ω]
    linarith
  have hπ' : π' = piOf 𝔼 P w₀ mp₀ mw₀ u wn w' := by
    funext t ω
    have h := (hfoc' t ω).1
    simp only [piOf, ← hmp', ← hups']
    field_simp
    linarith
  have hπw' : πw' = piwOf 𝔼 P w₀ mp₀ mw₀ u wn w' := by
    funext t ω
    have h := (hfoc' t ω).2.1
    simp only [piwOf, ← hmw', ← hups']
    field_simp
    linarith
  exact ⟨hπ', hπw', hx', rfl, hmp', hmw', hups'⟩

/-- Woodford (2003), (2.20) at the initial date `t₀` (a commitment to the criterion from `t₀`):
`(κ_w − κ_p) π^asym_{t₀} + (ξ_p + ξ_w) q_{t₀} − {E_{t₀}[β q_{t₀+1} − q_{t₀}] − e₀}`, where
`e₀ = E_{t₀−1}[β q_{t₀} − q_{t₀−1}]` is predetermined. -/
noncomputable def critC0 (P : SW) (x₀ e₀ : Ω → ℝ) (π πw x : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => (P.kw - P.kp) * piAsym P π πw 0 ω + (P.xip + P.xiw) * qSW P x₀ π πw x 0 ω -
    (𝔼.E 0 (fun ω => P.beta * qSW P x₀ π πw x 1 ω - qSW P x₀ π πw x 0 ω) ω - e₀ ω)

/-- Woodford (2003), (2.20) at `t₀`: a plan satisfying the first-order conditions (adapted `υ`)
with self-consistent initial multipliers satisfies the date-`t₀` criterion with
`e₀ = −(κ_w − κ_p)(ξ_p φ_{p,t₀−1} − ξ_w φ_{w,t₀−1})`. -/
theorem foc_crit0 {P : SW} {mp₀ mw₀ x₀ : Ω → ℝ} {π πw x mp mw ups : ℕ → Ω → ℝ}
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups) (hua : 𝔼.Adapted ups)
    (hsc : ∀ ω, P.lx * (x₀ ω - P.xstar) - P.kp * mp₀ ω - P.kw * mw₀ ω = 0) (ω : Ω) :
    critC0 𝔼 P x₀ (fun ω => -((P.kw - P.kp) * (P.xip * mp₀ ω - P.xiw * mw₀ ω))) π πw x ω = 0 := by
  have hq := (foc_q_eq 𝔼 (x₀ := x₀) hfoc).2 hsc
  have hqf : ∀ s, qSW P x₀ π πw x s = (P.kw - P.kp) • ups s := fun s => by
    funext ω'; simp only [Pi.smul_apply, smul_eq_mul]; exact hq s ω'
  have hE := E_bracket 𝔼 (β := P.beta) hua hqf 0 ω
  obtain ⟨f1, f2, -, f4⟩ := hfoc 0 ω
  simp only [lagW_zero] at f1 f2
  simp only [critC0, piAsym]
  rw [show (0 : ℕ) + 1 = 1 from rfl] at hE
  rw [hE, hq 0 ω]
  linear_combination (P.kw - P.kp) * (P.xip * f1 - P.xiw * f2 + f4)

/-- Woodford (2003), (2.19): in a plan satisfying the first-order conditions with adapted
`φ_p, φ_w`, the multiplier `υ` is adapted. -/
theorem foc_ups_adapted {P : SW} {mp₀ mw₀ : Ω → ℝ} {π πw x mp mw ups : ℕ → Ω → ℝ}
    (hfoc : FOCsw 𝔼 P mp₀ mw₀ π πw x mp mw ups) (hmpa : 𝔼.Adapted mp)
    (hmwa : 𝔼.Adapted mw) : 𝔼.Adapted ups := by
  intro t
  have h : ups t = P.xip • mp t - P.xiw • mw t + P.beta • 𝔼.E t (ups (t + 1)) := by
    funext ω; exact (hfoc t ω).2.2.2
  rw [h, map_add, map_sub, map_smul, map_smul, map_smul, hmpa t, hmwa t, 𝔼.E_E_self]

/-- **Woodford (2003), §2.2, `κ_w ≠ κ_p` (EXISTENCE OF A BOUNDED OPTIMAL PLAN)**: under the root
condition, for all bounded adapted disturbances and bounded date-0 `w_{t₀−1}` there is an
admissible plan that minimises the expected loss among ALL admissible plans (the `t₀`-optimal
plan: zero initial multipliers), and for any bounded date-0 initial multipliers an admissible plan
that is optimal from a timeless perspective. -/
theorem optimal_plan_exists (hpo : 𝔼.PullOut) {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P)
    {u wn : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) (hwn : BoundedProc wn)
    (hwna : 𝔼.Adapted wn) {w₀ mp₀ mw₀ : Ω → ℝ} (hw₀ : ∃ B, ∀ ω, |w₀ ω| ≤ B)
    (hmp₀ : ∃ B, ∀ ω, |mp₀ ω| ≤ B) (hmw₀ : ∃ B, ∀ ω, |mw₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀)
    (hmp₀a : 𝔼.E 0 mp₀ = mp₀) (hmw₀a : 𝔼.E 0 mw₀ = mw₀) :
    (∃ π πw x w, TimelessOptimalSW 𝔼 P w₀ u wn π πw x w) ∧
    ∃ π πw x w, PlanSW 𝔼 P w₀ u wn π πw x w ∧ ∀ π' πw' x' w',
      PlanSW 𝔼 P w₀ u wn π' πw' x' w' →
      ∀ ω, expLossOf 𝔼 P.beta (lossSW P π πw x) ω ≤ expLossOf 𝔼 P.beta (lossSW P π' πw' x') ω := by
  have i0a : 𝔼.E 0 (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := 𝔼.const 0 0
  have i0b : ∃ B, ∀ ω : Ω, |(fun _ : Ω => (0 : ℝ)) ω| ≤ B := ⟨0, fun ω => by simp⟩
  constructor
  · obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hfoc, mpa, mwa, mpb, mwb, upsb⟩, -⟩ :=
      foc_existsUnique 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR hu hua hwn hwna hw₀
        hmp₀ hmw₀ hw₀a hmp₀a hmw₀a
    refine ⟨π, πw, x, w, hp, fun π' πw' x' w' hp' h0 h0w ω => ?_⟩
    exact focSW_sufficient 𝔼 hpo P hβ0.le hβ1 hlp.le hlw.le hlx.le hp' hp mpa mwa mpb mwb upsb
      hmp₀ hmw₀ hfoc (fun ω => by rw [h0, sub_self, mul_zero])
      (fun ω => by rw [h0w, sub_self, mul_zero]) ω
  · obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hfoc, mpa, mwa, mpb, mwb, upsb⟩, -⟩ :=
      foc_existsUnique 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR hu hua hwn hwna hw₀
        i0b i0b hw₀a i0a i0a
    refine ⟨π, πw, x, w, hp, fun π' πw' x' w' hp' ω => ?_⟩
    exact focSW_sufficient 𝔼 hpo P hβ0.le hβ1 hlp.le hlw.le hlx.le hp' hp mpa mwa mpb mwb upsb
      i0b i0b hfoc (fun ω => by simp) (fun ω => by simp) ω

/-- **Woodford (2003), (2.20) corrected, from `t₀` (the multipliers of a criterion
equilibrium)**: an admissible plan satisfying the corrected criterion at every date `t > t₀` and
the date-`t₀` condition with predetermined `x_{t₀−1}, e₀` satisfies the first-order conditions
with the initial multipliers determined by `κ_pφ_p + κ_wφ_w = λ_x(x_{t₀−1} − x*)` and
`ξ_pφ_p − ξ_wφ_w = −e₀/(κ_w − κ_p)`. -/
theorem criterion_imp_foc {P : SW} (hkp : 0 < P.kp) (hkw : 0 < P.kw) (hxip : 0 < P.xip)
    (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) {w₀ x₀ e₀ : Ω → ℝ} {B : ℝ}
    (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hx₀a : 𝔼.E 0 x₀ = x₀) {u wn π' πw' x' w' : ℕ → Ω → ℝ}
    (hp' : PlanSW 𝔼 P w₀ u wn π' πw' x' w') (hc' : CriterionC 𝔼 P x₀ π' πw' x')
    (h0' : ∀ ω, critC0 𝔼 P x₀ e₀ π' πw' x' ω = 0) :
    ∃ mp' mw' ups' : ℕ → Ω → ℝ, FOCsw 𝔼 P
      (fun ω => (P.xiw * (P.lx * (x₀ ω - P.xstar)) + P.kw * (-e₀ ω / (P.kw - P.kp))) /
        (P.kp * P.xiw + P.kw * P.xip))
      (fun ω => (P.xip * (P.lx * (x₀ ω - P.xstar)) - P.kp * (-e₀ ω / (P.kw - P.kp))) /
        (P.kp * P.xiw + P.kw * P.xip)) π' πw' x' mp' mw' ups' ∧
      𝔼.Adapted mp' ∧ 𝔼.Adapted mw' ∧ BoundedProc ups' := by
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD : P.kp * P.xiw + P.kw * P.xip ≠ 0 := by positivity
  set c := P.kw - P.kp with hcdef
  set D := P.kp * P.xiw + P.kw * P.xip with hDdef
  set mp₀ : Ω → ℝ := fun ω => (P.xiw * (P.lx * (x₀ ω - P.xstar)) + P.kw * (-e₀ ω / c)) / D
    with hmp₀
  set mw₀ : Ω → ℝ := fun ω => (P.xip * (P.lx * (x₀ ω - P.xstar)) - P.kp * (-e₀ ω / c)) / D
    with hmw₀
  obtain ⟨mp', mw', ups', hfoc', mpa', mwa', upsa', upsb', hq'⟩ :=
    criterionC_foc 𝔼 P hkp hkw hxip hxiw hne hx₀a hx₀ hp' hc'
  have hqf : ∀ s, qSW P x₀ π' πw' x' s = c • ups' s := fun s => by
    funext ω'; simp only [Pi.smul_apply, smul_eq_mul]; exact (hq' s ω').symm
  have hsc' : ∀ ω, P.kp * (mp' 0 ω + P.lp * π' 0 ω + ups' 0 ω) +
      P.kw * (mw' 0 ω + P.lw * πw' 0 ω - ups' 0 ω) = P.lx * (x₀ ω - P.xstar) := by
    intro ω
    have f3 := (hfoc' 0 ω).2.2.1
    have hq0 := hq' 0 ω
    simp only [qSW, lagW_zero] at hq0
    linear_combination -f3 - hq0
  have hg' : ∀ ω, c * (P.xip * (mp' 0 ω + P.lp * π' 0 ω + ups' 0 ω) -
      P.xiw * (mw' 0 ω + P.lw * πw' 0 ω - ups' 0 ω)) = -e₀ ω := by
    intro ω
    have f4 := (hfoc' 0 ω).2.2.2
    have hcr := h0' ω
    have hE := E_bracket 𝔼 (β := P.beta) upsa' hqf 0 ω
    rw [show (0 : ℕ) + 1 = 1 from rfl] at hE
    simp only [critC0, piAsym] at hcr
    rw [hE, ← hq' 0 ω] at hcr
    linear_combination hcr - c * f4
  have hk : ∀ ω, P.xip * (mp' 0 ω + P.lp * π' 0 ω + ups' 0 ω) -
      P.xiw * (mw' 0 ω + P.lw * πw' 0 ω - ups' 0 ω) = -e₀ ω / c := fun ω => by
    rw [eq_div_iff hc, mul_comm]; exact hg' ω
  have hm1 : (fun ω => mp' 0 ω + P.lp * π' 0 ω + ups' 0 ω) = mp₀ := by
    funext ω
    have h1 := hsc' ω
    have h2 := hk ω
    simp only [hmp₀]
    rw [eq_div_iff hD]
    linear_combination P.xiw * h1 + P.kw * h2
  have hm2 : (fun ω => mw' 0 ω + P.lw * πw' 0 ω - ups' 0 ω) = mw₀ := by
    funext ω
    have h1 := hsc' ω
    have h2 := hk ω
    simp only [hmw₀]
    rw [eq_div_iff hD]
    linear_combination P.xip * h1 - P.kp * h2
  rw [hm1, hm2] at hfoc'
  exact ⟨mp', mw', ups', hfoc', mpa', mwa', upsb'⟩

/-- **Woodford (2003), (2.20) corrected, `κ_w ≠ κ_p` (DETERMINACY UNDER THE TARGET CRITERION)**:
under the root condition, for all bounded adapted disturbances and bounded date-0 predetermined
values `w_{t₀−1}`, `x_{t₀−1}` and `e₀ = E_{t₀−1}[β q_{t₀} − q_{t₀−1}]`, a commitment to the
corrected criterion from `t₀` (dates `t > t₀` and the date-`t₀` condition `critC0`) together with
(2.11)–(2.13) determines exactly one bounded adapted equilibrium. -/
theorem criterion_existsUnique {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P)
    {u wn : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) (hwn : BoundedProc wn)
    (hwna : 𝔼.Adapted wn) {w₀ x₀ e₀ : Ω → ℝ} (hw₀ : ∃ B, ∀ ω, |w₀ ω| ≤ B)
    (hx₀ : ∃ B, ∀ ω, |x₀ ω| ≤ B) (he₀ : ∃ B, ∀ ω, |e₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀)
    (hx₀a : 𝔼.E 0 x₀ = x₀) (he₀a : 𝔼.E 0 e₀ = e₀) :
    ∃ π πw x w, (PlanSW 𝔼 P w₀ u wn π πw x w ∧ CriterionC 𝔼 P x₀ π πw x ∧
      ∀ ω, critC0 𝔼 P x₀ e₀ π πw x ω = 0) ∧
    ∀ π' πw' x' w', PlanSW 𝔼 P w₀ u wn π' πw' x' w' → CriterionC 𝔼 P x₀ π' πw' x' →
      (∀ ω, critC0 𝔼 P x₀ e₀ π' πw' x' ω = 0) → π' = π ∧ πw' = πw ∧ x' = x ∧ w' = w := by
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD : P.kp * P.xiw + P.kw * P.xip ≠ 0 := by positivity
  set c := P.kw - P.kp with hcdef
  set D := P.kp * P.xiw + P.kw * P.xip with hDdef
  -- the initial multipliers determined by `x_{t₀−1}` and `e₀`
  set mp₀ : Ω → ℝ := fun ω => (P.xiw * (P.lx * (x₀ ω - P.xstar)) + P.kw * (-e₀ ω / c)) / D
    with hmp₀
  set mw₀ : Ω → ℝ := fun ω => (P.xip * (P.lx * (x₀ ω - P.xstar)) - P.kp * (-e₀ ω / c)) / D
    with hmw₀
  have i0a : 𝔼.E 0 (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := 𝔼.const 0 0
  have i0b : ∃ B, ∀ ω : Ω, |(fun _ : Ω => (0 : ℝ)) ω| ≤ B := ⟨0, fun ω => by simp⟩
  obtain ⟨mp₀a, mp₀b⟩ := comb3_init 𝔼 (P.xiw * P.lx / D) (-(P.kw / (c * D))) 0
    (-(P.xiw * P.lx * P.xstar / D)) hx₀a he₀a i0a hx₀ he₀ i0b (z := mp₀)
    (fun ω => by simp only [hmp₀]; field_simp; ring)
  obtain ⟨mw₀a, mw₀b⟩ := comb3_init 𝔼 (P.xip * P.lx / D) (P.kp / (c * D)) 0
    (-(P.xip * P.lx * P.xstar / D)) hx₀a he₀a i0a hx₀ he₀ i0b (z := mw₀)
    (fun ω => by simp only [hmw₀]; field_simp; ring)
  have hsc : ∀ ω, P.lx * (x₀ ω - P.xstar) - P.kp * mp₀ ω - P.kw * mw₀ ω = 0 := fun ω => by
    simp only [hmp₀, hmw₀, hDdef]; field_simp; ring
  have he : ∀ ω, -(c * (P.xip * mp₀ ω - P.xiw * mw₀ ω)) = e₀ ω := fun ω => by
    simp only [hmp₀, hmw₀, hDdef]; field_simp; ring
  obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hfoc, mpa, mwa, mpb, mwb, upsb⟩, huniq⟩ :=
    foc_existsUnique 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR hu hua hwn hwna hw₀
      mp₀b mw₀b hw₀a mp₀a mw₀a
  have upsa := foc_ups_adapted 𝔼 hfoc mpa mwa
  refine ⟨π, πw, x, w, ⟨hp, (foc_imp_criterion 𝔼 (x₀ := x₀) hfoc upsa).2 hsc, fun ω => ?_⟩, ?_⟩
  · have := foc_crit0 𝔼 hfoc upsa hsc ω
    rwa [show (fun ω => -((P.kw - P.kp) * (P.xip * mp₀ ω - P.xiw * mw₀ ω))) = e₀ from
      funext he] at this
  · intro π' πw' x' w' hp' hc' h0'
    obtain ⟨mp', mw', ups', hfoc', mpa', mwa', upsb'⟩ :=
      criterion_imp_foc 𝔼 hkp hkw hxip hxiw hne (hx₀.choose_spec) hx₀a hp' hc' h0'
    obtain ⟨h1, h2, h3, h4, -⟩ := huniq π' πw' x' w' mp' mw' ups' hp' hfoc' mpa' mwa' upsb'
    exact ⟨h1, h2, h3, h4⟩

/-! ### Failure outside the root condition -/

/-- Woodford (2003), (2.20): for a solution of the cubic equation, the outermost factor of the
chain, `U₂ = 𝒵²w − (Z₂ + Z₃)𝒵w + Z₂Z₃ w`, solves `(𝒵 − Z₁) U₂ = H` with initial value
`s₂ − (Z₂ + Z₃)s₁ + Z₂Z₃ w₀`. -/
theorem cubicC_outer {β : ℝ} {Z1 Z2 Z3 : ℂ} {w₀ s₁ s₂ : Ω → ℂ} {H w : ℕ → Ω → ℂ}
    (hw : CubicC 𝔼 β (Z1 + Z2 + Z3) (Z1 * Z2 + Z1 * Z3 + Z2 * Z3) (Z1 * Z2 * Z3) w₀ s₁ s₂ H w)
    (t : ℕ) (ω : Ω) :
    ZopC 𝔼 β (fun ω => 1 * (1 * s₂ ω + -(Z2 + Z3) * s₁ ω) + Z2 * Z3 * w₀ ω)
      (fun t ω => 1 * (1 * ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w) t ω +
        -(Z2 + Z3) * ZopC 𝔼 β w₀ w t ω) + Z2 * Z3 * w t ω) t ω -
      Z1 * (1 * (1 * ZopC 𝔼 β s₁ (ZopC 𝔼 β w₀ w) t ω + -(Z2 + Z3) * ZopC 𝔼 β w₀ w t ω) +
        Z2 * Z3 * w t ω) = H t ω := by
  rw [ZopC_lin, ZopC_lin]
  have := hw t ω
  linear_combination this

/-- Woodford (2003), (2.20): `𝒵` of a difference (with the difference of initial values). -/
theorem Zop_sub (β : ℝ) (y₀ z₀ : Ω → ℝ) (y z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Zop 𝔼 β (fun ω => y₀ ω - z₀ ω) (fun t ω => y t ω - z t ω) t ω =
      Zop 𝔼 β y₀ y t ω - Zop 𝔼 β z₀ z t ω := by
  have := Zop_comb6 𝔼 β 1 (-1) 0 0 0 0 0 (y1 := y) (y2 := z) (y3 := y) (y4 := y) (y5 := y)
    (y6 := y) (i1 := y₀) (i2 := z₀) (i3 := y₀) (i4 := y₀) (i5 := y₀) (i6 := y₀)
    (z := fun t ω => y t ω - z t ω) (z₀ := fun ω => y₀ ω - z₀ ω) (fun t ω => by ring)
    (fun ω => by ring) t ω
  rw [this]; ring

/-- Woodford (2003), (2.20): the difference of two solutions of the cubic equation with the same
forcing and the same `w₀` solves the homogeneous equation with the differences of the initial
values. -/
theorem cubicR_sub {β p3 p2 p1 p0 : ℝ} {w₀ s₁ s₂ s₁' s₂' : Ω → ℝ} {F w w' : ℕ → Ω → ℝ}
    (h : CubicR 𝔼 β p3 p2 p1 p0 w₀ s₁ s₂ F w) (h' : CubicR 𝔼 β p3 p2 p1 p0 w₀ s₁' s₂' F w') :
    CubicR 𝔼 β p3 p2 p1 p0 (fun _ => 0) (fun ω => s₁ ω - s₁' ω) (fun ω => s₂ ω - s₂' ω)
      (fun _ _ => 0) (fun t ω => w t ω - w' t ω) := by
  intro t ω
  have e1 : Zop 𝔼 β (fun _ => 0) (fun t ω => w t ω - w' t ω) =
      fun t ω => Zop 𝔼 β w₀ w t ω - Zop 𝔼 β w₀ w' t ω := by
    funext t ω
    rw [← Zop_sub]
    congr 1
    funext ω; ring
  have e2 : Zop 𝔼 β (fun ω => s₁ ω - s₁' ω)
      (fun t ω => Zop 𝔼 β w₀ w t ω - Zop 𝔼 β w₀ w' t ω) = fun t ω =>
      Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w) t ω - Zop 𝔼 β s₁' (Zop 𝔼 β w₀ w') t ω := by
    funext t ω; rw [Zop_sub]
  have e3 : Zop 𝔼 β (fun ω => s₂ ω - s₂' ω) (fun t ω => Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w) t ω -
      Zop 𝔼 β s₁' (Zop 𝔼 β w₀ w') t ω) = fun t ω =>
      Zop 𝔼 β s₂ (Zop 𝔼 β s₁ (Zop 𝔼 β w₀ w)) t ω -
        Zop 𝔼 β s₂' (Zop 𝔼 β s₁' (Zop 𝔼 β w₀ w')) t ω := by
    funext t ω; rw [Zop_sub]
  rw [e1, e2, e3]
  have a := h t ω
  have b := h' t ω
  linear_combination a - b

/-- **Woodford (2003), (2.20) (a factor with no stable root)**: if `Z` lies strictly inside the
ellipse (`ellForm β Z < 1`), every root of `βμ² − (1 + β − Z)μ + 1 = 0` satisfies
`1 < ‖μ‖` and `‖βμ‖ < 1`. -/
theorem roots_outside_of_ellForm_lt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Z μ : ℂ}
    (hin : ellForm β Z < 1) (hr : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0) :
    1 < ‖μ‖ ∧ ‖(β : ℂ) * μ‖ < 1 := by
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hr
  have hq : 0 < Complex.normSq μ := Complex.normSq_pos.2 hμ0
  have h := ellForm_sub_one hβ0 hβ1 hr hμ0
  have hpos : 0 < μ.re ^ 2 / (1 + β) ^ 2 + μ.im ^ 2 / (1 - β) ^ 2 := by
    have hm : 0 < μ.re ^ 2 + μ.im ^ 2 := by rw [Complex.normSq_apply] at hq; nlinarith
    have hd : μ.im ^ 2 / (1 + β) ^ 2 ≤ μ.im ^ 2 / (1 - β) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by nlinarith) (by nlinarith)
    have : 0 < (μ.re ^ 2 + μ.im ^ 2) / (1 + β) ^ 2 := by positivity
    rw [add_div] at this
    linarith
  have hneg : (1 - Complex.normSq μ) * (1 - β ^ 2 * Complex.normSq μ) < 0 := by
    have h2 : (1 - Complex.normSq μ) * (1 - β ^ 2 * Complex.normSq μ) *
        (μ.re ^ 2 / (1 + β) ^ 2 + μ.im ^ 2 / (1 - β) ^ 2) / Complex.normSq μ ^ 2 < 0 := by
      rw [← h]; linarith
    by_contra hc
    push Not at hc
    have : 0 ≤ (1 - Complex.normSq μ) * (1 - β ^ 2 * Complex.normSq μ) *
        (μ.re ^ 2 / (1 + β) ^ 2 + μ.im ^ 2 / (1 - β) ^ 2) / Complex.normSq μ ^ 2 := by
      positivity
    linarith
  have hq1 : 1 < Complex.normSq μ := by
    by_contra hc
    push Not at hc
    have : 0 ≤ 1 - β ^ 2 * Complex.normSq μ := by nlinarith
    nlinarith
  have hq2 : β ^ 2 * Complex.normSq μ < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hq1 hq2
  refine ⟨?_, ?_⟩
  · nlinarith [norm_nonneg μ]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0]
    nlinarith [norm_nonneg μ]

/-- **Woodford (2003), (2.16)–(2.19), `κ_w ≠ κ_p` (FAILURE OUTSIDE THE ROOT CONDITION)**: if a
root `Z₁` of `P` lies strictly inside the ellipse (`ellForm β Z₁ < 1`, so that both `μ`-roots of
its factor lie outside the unit circle), then for any disturbances there are constant initial
multipliers (with `w_{t₀−1} = 0`) for which NO admissible plan satisfies the first-order
conditions: the bounded optimal plan of `foc_existsUnique` does not exist for all initial
conditions. -/
theorem foc_not_determinate [Nonempty Ω] {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : P.lx ≠ 0) (hne : P.kw ≠ P.kp) (hD : Dst P ≠ 0) {Z1 Z2 Z3 : ℂ}
    (hv1 : Z1 + Z2 + Z3 = ((-(cp2 P / P.lx) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((cp1 P / P.lx : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(cp0 P / P.lx) : ℝ) : ℂ)) (hin : ellForm P.beta Z1 < 1)
    (u wn : ℕ → Ω → ℝ) :
    ¬ ∀ a b : ℝ, ∃ π πw x w mp mw ups, PlanSW 𝔼 P (fun _ => 0) u wn π πw x w ∧
      FOCsw 𝔼 P (fun _ => a) (fun _ => b) π πw x mp mw ups ∧ 𝔼.Adapted mp ∧ 𝔼.Adapted mw := by
  intro h
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  set c := P.kw - P.kp with hcdef
  set D := Dst P with hDdef
  set X0 := -(P.lx * P.xstar)
  set g1 := P.lx / c ^ 2
  obtain ⟨π0, πw0, x0, w0, mp0, mw0, ups0, hp0, hf0, ma0, mwa0⟩ :=
    h ((P.xiw * X0) / D) ((P.xip * X0) / D)
  obtain ⟨π1, πw1, x1, w1, mp1, mw1, ups1, hp1, hf1, ma1, mwa1⟩ :=
    h ((P.xiw * X0 + P.kw * g1) / D) ((P.xip * X0 - P.kp * g1) / D)
  have c0 := (foc_imp_cubic 𝔼 hlx hc hp0 hf0 ma0 mwa0).1
  have c1 := (foc_imp_cubic 𝔼 hlx hc hp1 hf1 ma1 mwa1).1
  have hd := cubicR_sub 𝔼 c1 c0
  have hs1 : (fun ω : Ω => initS1 P (fun _ : Ω => 0) (fun _ => (P.xiw * X0 + P.kw * g1) / D)
      (fun _ => (P.xip * X0 - P.kp * g1) / D) ω - initS1 P (fun _ => 0)
      (fun _ => (P.xiw * X0) / D) (fun _ => (P.xip * X0) / D) ω) = fun _ => 0 := by
    funext ω
    simp only [initS1, hDdef, Dst] at *
    field_simp
    ring
  have hs2 : (fun ω : Ω => initS2 P (fun _ : Ω => 0) (fun _ => (P.xiw * X0 + P.kw * g1) / D)
      (fun _ => (P.xip * X0 - P.kp * g1) / D) ω - initS2 P (fun _ => 0)
      (fun _ => (P.xiw * X0) / D) (fun _ => (P.xip * X0) / D) ω) = fun _ => 1 := by
    funext ω
    have hD' : P.kp * P.xiw + P.kw * P.xip ≠ 0 := hD
    simp only [initS2, initS1, hDdef, Dst, g1, X0] at *
    field_simp
    ring
  rw [hs1, hs2] at hd
  have hdc := (cubicR_iff 𝔼 hlx).1 hd
  rw [← hv1, ← hv2, ← hv3] at hdc
  have outer := cubicC_outer 𝔼 hdc
  -- the difference is bounded and adapted
  set dc : ℕ → Ω → ℂ := fun t ω => ((w1 t ω - w0 t ω : ℝ) : ℂ) with hdcdef
  have hda : AdaptedC 𝔼 dc := by
    rw [adaptedC_ofReal]
    intro t
    change 𝔼.E t (w1 t - w0 t) = w1 t - w0 t
    rw [map_sub, hp1.2.2.2.2.2.2.1 t, hp0.2.2.2.2.2.2.1 t]
  have hdb : BoundedC dc := by
    obtain ⟨M1, hM1⟩ := hp1.2.2.2.2.2.2.2.2.2.2
    obtain ⟨M0, hM0⟩ := hp0.2.2.2.2.2.2.2.2.2.2
    refine ⟨M1 + M0, fun t ω => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hM1 t ω) (hM0 t ω))
  have z0a : EC 𝔼 0 (fun ω => (((fun _ : Ω => (0 : ℝ)) ω : ℝ) : ℂ)) =
      fun ω => (((fun _ : Ω => (0 : ℝ)) ω : ℝ) : ℂ) := by rw [EC_ofReal, 𝔼.const]
  have z0b : ∃ B, ∀ ω : Ω, ‖(((fun _ : Ω => (0 : ℝ)) ω : ℝ) : ℂ)‖ ≤ B := ⟨0, fun ω => by simp⟩
  obtain ⟨aW1, bW1⟩ := ZopC_bdd_adapted 𝔼 P.beta hβ0.le z0a z0b hda hdb
  obtain ⟨aW2, bW2⟩ := ZopC_bdd_adapted 𝔼 P.beta hβ0.le z0a z0b aW1 bW1
  obtain ⟨aV, bV⟩ := lin_bdd_adapted 𝔼 1 (-(Z2 + Z3)) aW2 aW1 bW2 bW1
  obtain ⟨aU, bU⟩ := lin_bdd_adapted 𝔼 1 (Z2 * Z3) aV hda bV hdb
  obtain ⟨μ, hμ⟩ := exists_mu_root P.beta hβ0.ne' Z1
  obtain ⟨hμ1, hβμ⟩ := roots_outside_of_ellForm_lt hβ0 hβ1 hin hμ
  have hy := fun t ω => (outer t ω).trans (by simp : ((((fun _ _ => (0 : ℝ)) t ω /
    P.lx : ℝ) : ℂ)) = 0)
  have hz := stage_homog_init_zero 𝔼 hμ hμ1 hβμ (Y := 1) (fun ω => by simp) hy aU bU
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun hz ω
  simp at this

/-- Woodford (2003), (2.11)–(2.15): a parametrisation (all parameters positive, `κ_w ≠ κ_p`)
violating the root condition: `β = 1/2`, `κ_p = 1/20`, `κ_w = 2`, `ξ_p = ξ_w = 1/100`,
`λ_p = 1410070/3519399`, `λ_w = 3446/3519399`, `λ_x = 1`, `x* = 0`. -/
noncomputable def P1 : SW := ⟨1 / 2, 1 / 20, 2, 1 / 100, 1 / 100, 1410070 / 3519399,
  3446 / 3519399, 1, 0⟩

/-- Woodford (2003), (2.20): for `P1`, `P(Z) = (Z + 28577/440200)(Z² − Z/50 + 13/5000)`, with
roots `1/100 ± i/20` and `−28577/440200` (Vieta). -/
theorem P1_vieta :
    (⟨1 / 100, 1 / 20⟩ : ℂ) + ⟨1 / 100, -(1 / 20)⟩ + ((-(28577 / 440200) : ℝ) : ℂ) =
        ((-(cp2 P1 / P1.lx) : ℝ) : ℂ) ∧
      (⟨1 / 100, 1 / 20⟩ : ℂ) * ⟨1 / 100, -(1 / 20)⟩ +
        (⟨1 / 100, 1 / 20⟩ : ℂ) * ((-(28577 / 440200) : ℝ) : ℂ) +
        (⟨1 / 100, -(1 / 20)⟩ : ℂ) * ((-(28577 / 440200) : ℝ) : ℂ) =
        ((cp1 P1 / P1.lx : ℝ) : ℂ) ∧
      (⟨1 / 100, 1 / 20⟩ : ℂ) * ⟨1 / 100, -(1 / 20)⟩ * ((-(28577 / 440200) : ℝ) : ℂ) =
        ((-(cp0 P1 / P1.lx) : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply Complex.ext <;> simp [cp2, cp1, cp0, Dst, P1] <;> norm_num

/-- Woodford (2003), (2.20): for `P1` the root `1/100 + i/20` lies strictly inside the ellipse. -/
theorem P1_inside : ellForm P1.beta ⟨1 / 100, 1 / 20⟩ < 1 := by
  simp only [ellForm, P1]
  norm_num

/-- **Woodford (2003), (2.20) (the root condition can fail)**: `P1` violates `StableRoots`. -/
theorem P1_not_stableRoots : ¬ StableRoots P1 := by
  intro h
  obtain ⟨v1, v2, v3⟩ := P1_vieta
  have hlx : P1.lx ≠ 0 := by norm_num [P1]
  obtain ⟨μ, hr, hμ⟩ := h ⟨1 / 100, 1 / 20⟩ (by rw [charP_factor hlx v1 v2 v3]; ring)
  have := (stable_iff_ellForm (β := P1.beta) (by norm_num [P1]) (by norm_num [P1]) _).1
    ⟨μ, hr, hμ⟩
  linarith [P1_inside]

/-- **Woodford (2003), (2.16)–(2.19) (counterexample to unconditional determinacy)**: with the
parameters `P1` (all positive, `κ_w ≠ κ_p`), under any expectation system with at least one
state and any disturbances, there are constant initial multipliers for which no admissible plan
satisfies the first-order conditions. -/
theorem P1_not_determinate [Nonempty Ω] (u wn : ℕ → Ω → ℝ) :
    ¬ ∀ a b : ℝ, ∃ π πw x w mp mw ups, PlanSW 𝔼 P1 (fun _ => 0) u wn π πw x w ∧
      FOCsw 𝔼 P1 (fun _ => a) (fun _ => b) π πw x mp mw ups ∧ 𝔼.Adapted mp ∧
      𝔼.Adapted mw := by
  obtain ⟨v1, v2, v3⟩ := P1_vieta
  exact foc_not_determinate 𝔼 (by norm_num [P1]) (by norm_num [P1]) (by norm_num [P1])
    (by norm_num [P1]) (by norm_num [Dst, P1]) v1 v2 v3 P1_inside u wn

/-- **Woodford (2003), (2.20) corrected (commitment to the criterion need not determine a bounded
equilibrium)**: with the parameters `P1`, for any disturbances there are constant predetermined
values `x_{t₀−1}`, `e₀` (and `w_{t₀−1} = 0`) for which no bounded adapted equilibrium satisfies
(2.11)–(2.13), the corrected criterion at `t > t₀` and the date-`t₀` condition. -/
theorem P1_criterion_not_determinate [Nonempty Ω] (u wn : ℕ → Ω → ℝ) :
    ¬ ∀ x₀ e₀ : ℝ, ∃ π πw x w, PlanSW 𝔼 P1 (fun _ => 0) u wn π πw x w ∧
      CriterionC 𝔼 P1 (fun _ => x₀) π πw x ∧
      ∀ ω, critC0 𝔼 P1 (fun _ => x₀) (fun _ => e₀) π πw x ω = 0 := by
  intro h
  apply P1_not_determinate 𝔼 u wn
  intro a b
  obtain ⟨π, πw, x, w, hp, hc, h0⟩ := h ((P1.kp * a + P1.kw * b) / P1.lx + P1.xstar)
    (-((P1.kw - P1.kp) * (P1.xip * a - P1.xiw * b)))
  obtain ⟨mp, mw, ups, hfoc, mpa, mwa, -⟩ := criterion_imp_foc 𝔼 (P := P1) (by norm_num [P1])
    (by norm_num [P1]) (by norm_num [P1]) (by norm_num [P1]) (by norm_num [P1])
    (B := |(P1.kp * a + P1.kw * b) / P1.lx + P1.xstar|) (fun _ => le_rfl) (𝔼.const 0 _) hp hc h0
  have e1 : (fun ω : Ω => (P1.xiw * (P1.lx * ((fun _ => (P1.kp * a + P1.kw * b) / P1.lx +
      P1.xstar) ω - P1.xstar)) + P1.kw * (-(fun _ => -((P1.kw - P1.kp) * (P1.xip * a -
      P1.xiw * b))) ω / (P1.kw - P1.kp))) / (P1.kp * P1.xiw + P1.kw * P1.xip)) = fun _ => a := by
    funext ω; simp only [P1]; field_simp; ring
  have e2 : (fun ω : Ω => (P1.xip * (P1.lx * ((fun _ => (P1.kp * a + P1.kw * b) / P1.lx +
      P1.xstar) ω - P1.xstar)) - P1.kp * (-(fun _ => -((P1.kw - P1.kp) * (P1.xip * a -
      P1.xiw * b))) ω / (P1.kw - P1.kp))) / (P1.kp * P1.xiw + P1.kw * P1.xip)) = fun _ => b := by
    funext ω; simp only [P1]; field_simp; ring
  rw [e1, e2] at hfoc
  exact ⟨π, πw, x, w, mp, mw, ups, hp, hfoc, mpa, mwa⟩

/-! ### (2.14): the convergent family of equilibria as `ξ_w → ∞` -/

/-- Woodford (2003), survey §4.3: with zero initial value the workhorse solution is bounded by
`μ₁ H / ((1 − βμ₁)(1 − μ₁))` (`H` a bound of the forcing). -/
theorem ysol_bound {β c H : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) {h : ℕ → Ω → ℝ}
    (hh : ∀ t ω, |h t ω| ≤ H) (t : ℕ) (ω : Ω) :
    |ysol 𝔼 β c (fun _ => 0) h t ω| ≤
      lam1 β c * H / (1 - β * lam1 β c) / (1 - lam1 β c) := by
  have hμ0 := lam1_pos hβ0 hc
  have hμ1 := lam1_lt_one hβ0 hc
  obtain ⟨ha0, ha1⟩ := beta_lam1_mem hβ0 hβ1 hc
  have hgb := neg_mu_f_bounded hμ0 hh
  have hW := 𝔼.forwardSeries_bounded ha0 ha1 hgb
  obtain ⟨-, -⟩ := hW
  have hW' : ∀ t ω, |wsol 𝔼 β c h t ω| ≤ lam1 β c * H / (1 - β * lam1 β c) := by
    intro t ω
    have hs := 𝔼.forwardSeries_summable ha0 ha1 hgb t ω
    have hg : Summable (fun k : ℕ => lam1 β c * H * (β * lam1 β c) ^ k) :=
      (summable_geometric_of_lt_one ha0 ha1).mul_left _
    have hval : ∑' k : ℕ, lam1 β c * H * (β * lam1 β c) ^ k =
        lam1 β c * H / (1 - β * lam1 β c) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, div_eq_mul_inv]
    have hb : ∀ k, |(β * lam1 β c) ^ k * 𝔼.E t ((fun s => (-lam1 β c) • h s) (t + k)) ω| ≤
        lam1 β c * H * (β * lam1 β c) ^ k := fun k => by
      rw [abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm (lam1 β c * H)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hgb (t + k)) t ω) (pow_nonneg ha0 k)
    change |∑' k, (β * lam1 β c) ^ k * 𝔼.E t ((fun s => (-lam1 β c) • h s) (t + k)) ω| ≤ _
    have hlo : ∀ k, -(lam1 β c * H * (β * lam1 β c) ^ k) ≤
        (β * lam1 β c) ^ k * 𝔼.E t ((fun s => (-lam1 β c) • h s) (t + k)) ω := fun k => by
      have := neg_abs_le ((β * lam1 β c) ^ k * 𝔼.E t ((fun s => (-lam1 β c) • h s) (t + k)) ω)
      linarith [hb k]
    rw [← hval, abs_le]
    constructor
    · rw [← tsum_neg]
      exact Summable.tsum_le_tsum hlo hg.neg hs
    · exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hb k)) hs hg
  have := backRec_bounded hμ0.le hμ1 (Y := 0) (y₀ := fun _ => 0) (fun ω => by simp) hW' t ω
  refine this.trans (max_le ?_ le_rfl)
  have : 0 ≤ lam1 β c * H / (1 - β * lam1 β c) := (abs_nonneg _).trans (hW' 0 ω)
  exact div_nonneg this (by linarith)

/-- Woodford (2003), (2.14): the flexible-wage real wage `w^L = w^n + (ω_w + σ⁻¹)(x̄ + u)`. -/
def wLim (om : ℝ) (u wn xb : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => wn t ω + om * (xb t ω + u t ω)

/-- Woodford (2003), (2.12)–(2.13): the (`ξ_w`-independent) forcing of the real-wage gap,
`h = ξ_p(ω_p + ω̄)(x̄ + u) + 𝒵 w^L`. -/
def hGap (β ξp ωp om : ℝ) (w₀ : Ω → ℝ) (u wn xb : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => ξp * (ωp + om) * (xb t ω + u t ω) + Zop 𝔼 β w₀ (wLim om u wn xb) t ω

/-- **Woodford (2003), (2.11)–(2.13) (the equilibrium real wage for given `ξ_w`)**:
`w^ξ = w^L + g^ξ` where `g^ξ` is the bounded solution of
`β E_t g_{t+1} − (1 + β + ξ_p + ξ_w) g_t + g_{t−1} = h_t` (`g_{−1} = 0`). -/
noncomputable def wFam (β ξp ωp om : ℝ) (w₀ : Ω → ℝ) (u wn xb : ℕ → Ω → ℝ) (ξ : ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => wLim om u wn xb t ω +
    ysol 𝔼 β (ξp + ξ) (fun _ => 0) (hGap 𝔼 β ξp ωp om w₀ u wn xb) t ω

/-- Woodford (2003), (2.11): the equilibrium price inflation for given `ξ_w`,
`π^ξ = ∑ βʲ E_t[ξ_p(ω_p + ω̄)(x̄ + u)_{t+j}] + ξ_p ∑ βʲ E_t g^ξ_{t+j}`. -/
noncomputable def piFam (β ξp ωp om : ℝ) (w₀ : Ω → ℝ) (u wn xb : ℕ → Ω → ℝ) (ξ : ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => 𝔼.forwardSeries β (fun s ω => ξp * (ωp + om) * (xb s ω + u s ω)) t ω +
    ξp * 𝔼.forwardSeries β (ysol 𝔼 β (ξp + ξ) (fun _ => 0) (hGap 𝔼 β ξp ωp om w₀ u wn xb)) t ω

/-- Woodford (2003), (2.13): the equilibrium wage inflation `π^w = π + w − w_{−1}`. -/
noncomputable def piwFam (β ξp ωp om : ℝ) (w₀ : Ω → ℝ) (u wn xb : ℕ → Ω → ℝ) (ξ : ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => piFam 𝔼 β ξp ωp om w₀ u wn xb ξ t ω + wFam 𝔼 β ξp ωp om w₀ u wn xb ξ t ω -
    lagW w₀ (wFam 𝔼 β ξp ωp om w₀ u wn xb ξ) t ω

/-- Woodford (2003), (2.11): the forward series is bounded by `M/(1 − a)`. -/
theorem forwardSeries_abs_le {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (t : ℕ) (ω : Ω) : |𝔼.forwardSeries a f t ω| ≤ M / (1 - a) := by
  have hs := 𝔼.forwardSeries_summable ha0 ha1 hf t ω
  have hg : Summable (fun k : ℕ => M * a ^ k) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_left M
  have hval : ∑' k : ℕ, M * a ^ k = M / (1 - a) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, div_eq_mul_inv]
  have hb : ∀ k, |a ^ k * 𝔼.E t (f (t + k)) ω| ≤ M * a ^ k := fun k => by
    rw [abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hf (t + k)) t ω) (pow_nonneg ha0 k)
  have hlo : ∀ k, -(M * a ^ k) ≤ a ^ k * 𝔼.E t (f (t + k)) ω := fun k => by
    have := neg_abs_le (a ^ k * 𝔼.E t (f (t + k)) ω)
    linarith [hb k]
  change |∑' k, a ^ k * 𝔼.E t (f (t + k)) ω| ≤ _
  rw [abs_le, ← hval]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum hlo hg.neg hs
  · exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hb k)) hs hg

/-- Woodford (2003), (2.11): the forward series of a sum is the sum of the forward series. -/
theorem forwardSeries_E_add {a M N : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f g : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hg : ∀ t ω, |g t ω| ≤ N) (hfa : 𝔼.Adapted f)
    (hga : 𝔼.Adapted g) (k : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a f t ω + k * 𝔼.forwardSeries a g t ω =
      a * 𝔼.E t (fun ω => 𝔼.forwardSeries a f (t + 1) ω + k * 𝔼.forwardSeries a g (t + 1) ω) ω +
        (f t ω + k * g t ω) := by
  have h1 := congrFun (𝔼.forwardSeries_solves ha0 ha1 hf hfa t) ω
  have h2 := congrFun (𝔼.forwardSeries_solves ha0 ha1 hg hga t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have hE : 𝔼.E t (fun ω => 𝔼.forwardSeries a f (t + 1) ω + k * 𝔼.forwardSeries a g (t + 1) ω)
      ω = 𝔼.E t (𝔼.forwardSeries a f (t + 1)) ω + k * 𝔼.E t (𝔼.forwardSeries a g (t + 1)) ω := by
    rw [show (fun ω => 𝔼.forwardSeries a f (t + 1) ω + k * 𝔼.forwardSeries a g (t + 1) ω) =
      𝔼.forwardSeries a f (t + 1) + k • 𝔼.forwardSeries a g (t + 1) from rfl, map_add, map_smul]
    rfl
  rw [hE, h1, h2]
  ring

/-- **Woodford (2003), (2.11)–(2.14) (THE FLEXIBLE-WAGE LIMIT, unconditional)**: fix
`0 < β < 1`, `ξ_p > 0`, `ω̄ = ω_w + σ⁻¹`, bounded adapted `u`, `w^n` and a bounded adapted
output-gap path `x̄` (the policy `x_t = x̄_t`), and a bounded date-0 `w_{t₀−1}`. For every
`ξ_w > 0` the processes `(piFam, piwFam, x̄, wFam)` solve (2.11)–(2.13) with `κ_p = ξ_p ω_p`,
`κ_w = ξ_w ω̄`; wage inflation is bounded uniformly in `ξ_w`; as `ξ_w → ∞` the real wage converges
uniformly to `w^n + ω̄(x̄ + u)` and price inflation converges uniformly to the forward solution of
`π_t = κ x̄_t + β E_t π_{t+1} + κ u_t` with `κ = ξ_p(ω_p + ω_w + σ⁻¹)` — (2.14), the limit of
`flexible_wage_limit` with all its hypotheses verified. -/
theorem flexible_wage_family {β ξp ωp ωw sinv : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hξp : 0 < ξp) {u wn xb : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hua : 𝔼.Adapted u) (hwn : BoundedProc wn) (hwna : 𝔼.Adapted wn) (hxb : BoundedProc xb)
    (hxba : 𝔼.Adapted xb) {w₀ : Ω → ℝ} (hw₀ : ∃ B, ∀ ω, |w₀ ω| ≤ B) (hw₀a : 𝔼.E 0 w₀ = w₀) :
    let om := ωw + sinv
    let w := wFam 𝔼 β ξp ωp om w₀ u wn xb
    let π := piFam 𝔼 β ξp ωp om w₀ u wn xb
    let πw := piwFam 𝔼 β ξp ωp om w₀ u wn xb
    let πL := 𝔼.forwardSeries β (fun s ω => ξp * (ωp + om) * (xb s ω + u s ω))
    (∀ ξ, 0 < ξ → ∀ t ω,
      π ξ t ω = ξp * ωp * (xb t ω + u t ω) + ξp * (w ξ t ω - wn t ω) +
        β * 𝔼.E t (π ξ (t + 1)) ω ∧
      πw ξ t ω = ξ * (ωw + sinv) * (xb t ω + u t ω) + ξ * (wn t ω - w ξ t ω) +
        β * 𝔼.E t (πw ξ (t + 1)) ω ∧
      w ξ t ω = lagW w₀ (w ξ) t ω + πw ξ t ω - π ξ t ω) ∧
    (∃ M, ∀ ξ, 0 < ξ → ∀ t ω, |πw ξ t ω| ≤ M) ∧
    (∀ t, TendstoUniformly (fun ξ => w ξ t) (wLim om u wn xb t) atTop) ∧
    (∀ t, TendstoUniformly (fun ξ => π ξ t) (πL t) atTop) ∧
    ∀ t ω, wLim om u wn xb t ω - wn t ω = (ωw + sinv) * (xb t ω + u t ω) ∧
      πL t ω = ξp * (ωp + ωw + sinv) * xb t ω + β * 𝔼.E t (πL (t + 1)) ω +
        ξp * (ωp + ωw + sinv) * u t ω := by
  intro om w π πw πL
  -- the ξ_w-independent objects
  set wL := wLim om u wn xb with hwL
  set h := hGap 𝔼 β ξp ωp om w₀ u wn xb with hh
  set f1 : ℕ → Ω → ℝ := fun s ω => ξp * (ωp + om) * (xb s ω + u s ω) with hf1
  have z0 : ∀ t, 𝔼.E t (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := fun t => 𝔼.const t 0
  have zb : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  obtain ⟨wLa, wLb⟩ := comb6_bdd_adapted 𝔼 1 om om 0 0 0 0 hwna hxba hua z0 z0 z0 hwn hxb hu
    zb zb zb (z := wL) (fun t ω => by simp only [hwL, wLim]; ring)
  obtain ⟨f1a, f1b⟩ := comb6_bdd_adapted 𝔼 (ξp * (ωp + om)) (ξp * (ωp + om)) 0 0 0 0 0 hxba
    hua z0 z0 z0 z0 hxb hu zb zb zb zb (z := f1) (fun t ω => by simp only [hf1]; ring)
  have ZwLa := Zop_adapted 𝔼 β hw₀a wLa
  have ZwLb := Zop_bounded 𝔼 β hβ0.le hw₀ wLb
  obtain ⟨ha, ⟨H0, hH0'⟩⟩ := comb6_bdd_adapted 𝔼 1 1 0 0 0 0 0 f1a ZwLa z0 z0 z0 z0 f1b ZwLb
    zb zb zb zb (z := h) (fun t ω => by simp only [hh, hGap, hf1]; ring)
  set H := |H0|
  have hH : ∀ t ω, |h t ω| ≤ H := fun t ω => (hH0' t ω).trans (le_abs_self _)
  have hH0 : 0 ≤ H := abs_nonneg _
  obtain ⟨F1, hF1⟩ := f1b
  -- the uniform bound on the real-wage gap
  set mb := (1 + β) / (1 + β + ξp) with hmb
  have hmb1 : mb < 1 := by rw [hmb, div_lt_one (by linarith)]; linarith
  have hmb0 : 0 < mb := by positivity
  set C := H / ((1 - β) * (1 - mb)) with hC
  have hC0 : 0 ≤ C := div_nonneg hH0 (mul_nonneg (by linarith) (by linarith))
  set kb : ℝ → ℝ := fun ξ => C * ((1 + β) / (1 + β + ξp + ξ)) with hkb
  have hgk : ∀ ξ, 0 < ξ → ∀ t ω,
      |ysol 𝔼 β (ξp + ξ) (fun _ => 0) h t ω| ≤ kb ξ := by
    intro ξ hξ t ω
    have hc : 0 < ξp + ξ := by linarith
    have h1 := ysol_bound 𝔼 hβ0 hβ1 hc hH t ω
    have hμ0 := lam1_pos hβ0 hc
    have hμ1 := lam1_lt_one hβ0 hc
    have hμle := lam1_le hβ0 hc
    have hμmb : lam1 β (ξp + ξ) ≤ mb := hμle.trans (by
      rw [hmb]; apply div_le_div_of_nonneg_left (by linarith) (by linarith); linarith)
    refine h1.trans ?_
    have e1 : 0 < 1 - β * lam1 β (ξp + ξ) := by nlinarith
    have e2 : 0 < 1 - lam1 β (ξp + ξ) := by linarith
    rw [div_div, hkb]
    simp only
    rw [hC, div_le_iff₀ (mul_pos e1 e2)]
    have e3 : (1 - β) * (1 - mb) ≤ (1 - β * lam1 β (ξp + ξ)) * (1 - lam1 β (ξp + ξ)) := by
      apply mul_le_mul (by nlinarith) (by linarith) (by linarith) (by linarith)
    have e4 : 0 < (1 - β) * (1 - mb) := mul_pos (by linarith) (by linarith)
    have hQ : 1 ≤ ((1 - β * lam1 β (ξp + ξ)) * (1 - lam1 β (ξp + ξ))) / ((1 - β) * (1 - mb)) := by
      rw [le_div_iff₀ e4]; linarith
    have hr0 : 0 ≤ (1 + β) / (1 + β + ξp + ξ) := by positivity
    calc lam1 β (ξp + ξ) * H ≤ (1 + β) / (1 + β + ξp + ξ) * H :=
          mul_le_mul_of_nonneg_right (by rw [← add_assoc] at hμle; exact hμle) hH0
      _ ≤ (1 + β) / (1 + β + ξp + ξ) * H *
          (((1 - β * lam1 β (ξp + ξ)) * (1 - lam1 β (ξp + ξ))) / ((1 - β) * (1 - mb))) :=
          le_mul_of_one_le_right (by positivity) hQ
      _ = _ := by field_simp
  -- the equations for each ξ_w
  have hgs : ∀ ξ, 0 < ξ → SecondOrder 𝔼 β (ξp + ξ) (fun _ => 0) h
      (ysol 𝔼 β (ξp + ξ) (fun _ => 0) h) ∧ 𝔼.Adapted (ysol 𝔼 β (ξp + ξ) (fun _ => 0) h) := by
    intro ξ hξ
    obtain ⟨⟨hso, gA, -⟩, -⟩ := secondOrder_existsUnique 𝔼 hβ0 hβ1 (by linarith : 0 < ξp + ξ)
      hH ha (Y := 0) (y₀ := fun _ => 0) (fun ω => by simp) (z0 0)
    exact ⟨hso, gA⟩
  have heqs : ∀ ξ, 0 < ξ → ∀ t ω,
      π ξ t ω = ξp * ωp * (xb t ω + u t ω) + ξp * (w ξ t ω - wn t ω) +
        β * 𝔼.E t (π ξ (t + 1)) ω ∧
      πw ξ t ω = ξ * (ωw + sinv) * (xb t ω + u t ω) + ξ * (wn t ω - w ξ t ω) +
        β * 𝔼.E t (πw ξ (t + 1)) ω ∧
      w ξ t ω = lagW w₀ (w ξ) t ω + πw ξ t ω - π ξ t ω := by
    intro ξ hξ t ω
    obtain ⟨hso, gA⟩ := hgs ξ hξ
    set g := ysol 𝔼 β (ξp + ξ) (fun _ => 0) h with hg
    obtain ⟨Gb, hGb⟩ : ∃ G, ∀ t ω, |g t ω| ≤ G := ⟨kb ξ, hgk ξ hξ⟩
    have hwg : ∀ t ω, w ξ t ω = wL t ω + g t ω := fun t ω => rfl
    have hπg : ∀ t ω, π ξ t ω = 𝔼.forwardSeries β f1 t ω + ξp * 𝔼.forwardSeries β g t ω :=
      fun t ω => rfl
    have e1 := forwardSeries_E_add 𝔼 hβ0.le hβ1 hF1 hGb f1a gA ξp t ω
    have hEπ : 𝔼.E t (π ξ (t + 1)) ω = 𝔼.E t (fun ω => 𝔼.forwardSeries β f1 (t + 1) ω +
        ξp * 𝔼.forwardSeries β g (t + 1) ω) ω := rfl
    have hwa : 𝔼.Adapted (w ξ) := fun t => by
      change 𝔼.E t (wL t + g t) = wL t + g t
      rw [map_add, wLa t, gA t]
    have hEw : 𝔼.E t (πw ξ (t + 1)) ω = 𝔼.E t (π ξ (t + 1)) ω + 𝔼.E t (w ξ (t + 1)) ω -
        w ξ t ω := by
      have : πw ξ (t + 1) = π ξ (t + 1) + w ξ (t + 1) - w ξ t := rfl
      rw [this, map_sub, map_add, hwa t]
      rfl
    have hZ := Zop_comb6 𝔼 β 1 1 0 0 0 0 0 (y1 := wL) (y2 := g) (y3 := g) (y4 := g) (y5 := g)
      (y6 := g) (i1 := w₀) (i2 := fun _ => 0) (i3 := w₀) (i4 := w₀) (i5 := w₀) (i6 := w₀)
      (z := w ξ) (z₀ := w₀) (fun t ω => by rw [hwg]; ring) (fun ω => by ring) t ω
    have hs := hso t ω
    have hhd : h t ω = f1 t ω + Zop 𝔼 β w₀ wL t ω := rfl
    have hp1 : π ξ t ω = ξp * ωp * (xb t ω + u t ω) + ξp * (w ξ t ω - wn t ω) +
        β * 𝔼.E t (π ξ (t + 1)) ω := by
      rw [hπg, hEπ, e1, hwg]
      simp only [hf1, hwL, wLim]
      ring
    refine ⟨hp1, ?_, ?_⟩
    · have hπw : πw ξ t ω = π ξ t ω + w ξ t ω - lagW w₀ (w ξ) t ω := rfl
      have hWt := hwg t ω
      have hWL : wL t ω = wn t ω + om * (xb t ω + u t ω) := rfl
      have hf : f1 t ω = ξp * (ωp + om) * (xb t ω + u t ω) := rfl
      simp only [Zop] at hZ hhd
      have zg : (1 + β) * g t ω - β * 𝔼.E t (g (t + 1)) ω - lagW (fun _ => 0) g t ω =
          -h t ω - (ξp + ξ) * g t ω := by linarith [hs]
      have zwl : (1 + β) * wL t ω - β * 𝔼.E t (wL (t + 1)) ω - lagW w₀ wL t ω =
          h t ω - f1 t ω := by linarith [hhd]
      linear_combination hπw - β * hEw + hp1 + hZ + zwl + zg - hf + (ξp + ξ) * (hWt + hWL)
    · have hπw : πw ξ t ω = π ξ t ω + w ξ t ω - lagW w₀ (w ξ) t ω := rfl
      rw [hπw]; ring
  -- the bound tends to zero, and is uniform
  have hkb0 : Tendsto kb atTop (𝓝 0) := by
    have h1 : Tendsto (fun ξ : ℝ => 1 + β + ξp + ξ) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_id
    simpa [hkb] using ((tendsto_const_nhds (x := 1 + β)).div_atTop h1).const_mul C
  set kmax := C * ((1 + β) / (1 + β + ξp))
  have hkmax : ∀ ξ, 0 < ξ → kb ξ ≤ kmax := fun ξ hξ => by
    simp only [hkb, kmax]
    apply mul_le_mul_of_nonneg_left _ hC0
    apply div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  have hgmax : ∀ ξ, 0 < ξ → ∀ t ω, |ysol 𝔼 β (ξp + ξ) (fun _ => 0) h t ω| ≤ kmax :=
    fun ξ hξ t ω => (hgk ξ hξ t ω).trans (hkmax ξ hξ)
  obtain ⟨WLb, hWLb⟩ := wLb
  obtain ⟨B0, hB0⟩ := hw₀
  have hwb : ∀ ξ, 0 < ξ → ∀ t ω, |w ξ t ω| ≤ WLb + kmax := fun ξ hξ t ω =>
    (abs_add_le _ _).trans (add_le_add (hWLb t ω) (hgmax ξ hξ t ω))
  have hπb : ∀ ξ, 0 < ξ → ∀ t ω, |π ξ t ω| ≤ F1 / (1 - β) + ξp * (kmax / (1 - β)) := by
    intro ξ hξ t ω
    refine (abs_add_le _ _).trans (add_le_add (forwardSeries_abs_le 𝔼 hβ0.le hβ1 hF1 t ω) ?_)
    rw [abs_mul, abs_of_pos hξp]
    exact mul_le_mul_of_nonneg_left (forwardSeries_abs_le 𝔼 hβ0.le hβ1 (hgmax ξ hξ) t ω)
      hξp.le
  have hM : ∀ ξ, 0 < ξ → ∀ t ω, |πw ξ t ω| ≤
      F1 / (1 - β) + ξp * (kmax / (1 - β)) + (WLb + kmax) + max B0 (WLb + kmax) := by
    intro ξ hξ t ω
    have : πw ξ t ω = π ξ t ω + w ξ t ω - lagW w₀ (w ξ) t ω := rfl
    rw [this]
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hπb ξ hξ t ω)
      (hwb ξ hξ t ω))) (lagW_bounded hB0 (hwb ξ hξ) t ω))
  -- uniform convergence
  have hwU : ∀ t, TendstoUniformly (fun ξ => w ξ t) (wL t) atTop := by
    intro t
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hkb0.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with ξ h1 h2 ω
    rw [Real.dist_eq]
    have : wL t ω - w ξ t ω = -ysol 𝔼 β (ξp + ξ) (fun _ => 0) h t ω := by
      change wL t ω - (wL t ω + _) = _; ring
    rw [this, abs_neg]
    exact lt_of_le_of_lt (hgk ξ h2 t ω) h1
  have hπU : ∀ t, TendstoUniformly (fun ξ => π ξ t) (πL t) atTop := by
    intro t
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hk2 : Tendsto (fun ξ => ξp * (kb ξ / (1 - β))) atTop (𝓝 0) := by
      simpa using (hkb0.div_const (1 - β)).const_mul ξp
    filter_upwards [hk2.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with ξ h1 h2 ω
    rw [Real.dist_eq]
    have : πL t ω - π ξ t ω =
        -(ξp * 𝔼.forwardSeries β (ysol 𝔼 β (ξp + ξ) (fun _ => 0) h) t ω) := by
      change πL t ω - (πL t ω + _) = _; ring
    rw [this, abs_neg, abs_mul, abs_of_pos hξp]
    refine lt_of_le_of_lt ?_ h1
    exact mul_le_mul_of_nonneg_left (forwardSeries_abs_le 𝔼 hβ0.le hβ1 (hgk ξ h2) t ω) hξp.le
  refine ⟨heqs, ⟨_, hM⟩, hwU, hπU, ?_⟩
  have hlim := flexible_wage_limit 𝔼 hβ0.le (ωw := ωw) (sinv := sinv) (x := fun _ => xb)
    (π := π) (πw := πw) (w := w)
    (u := u) (wn := wn) (πL := πL) (xL := xb) (wL := wL)
    (fun ξ hξ t ω => (heqs ξ hξ t ω).1) (fun ξ hξ t ω => ?_) hM
    (fun t ω => tendsto_const_nhds) (fun t ω => (hwU t).tendsto_at ω)
    (fun t ω => (hπU t).tendsto_at ω) (fun t => hπU (t + 1))
  · exact hlim
  · have := (heqs ξ hξ t ω).2.1
    linear_combination this

/-! ### The boundary of the root condition: resonance -/

/-- Woodford (2003), (2.20) (resonance on the unit circle): if `‖μ‖ = 1`, `μ` is not real,
`A ≠ 0`, `c₀ ≠ 0`, then no bounded sequence satisfies
`v_{t+1} = μ v_t − c₀ (A μᵗ + Ā μ̄ᵗ)/2` (the forcing contains the unit root's own frequency). -/
theorem no_bounded_resonant {μ A c0 : ℂ} (hμ : ‖μ‖ = 1) (hreal : (starRingEnd ℂ) μ ≠ μ)
    (hA : A ≠ 0) (hc0 : c0 ≠ 0) {v : ℕ → ℂ}
    (hv : ∀ t, v (t + 1) = μ * v t -
      c0 * ((A * μ ^ t + (starRingEnd ℂ) A * (starRingEnd ℂ) μ ^ t) / 2))
    (hb : ∃ M, ∀ t, ‖v t‖ ≤ M) : False := by
  obtain ⟨M, hM⟩ := hb
  set μc := (starRingEnd ℂ) μ with hμc
  have hmm : μ * μc = 1 := by
    rw [hμc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ]; simp
  have hμc1 : ‖μc‖ = 1 := by rw [hμc, Complex.norm_conj, hμ]
  set r := μc ^ 2 with hr
  have hr1 : r ≠ 1 := by
    intro h
    apply hreal
    have h2 : μc ^ 2 * μ ^ 2 = μ ^ 2 := by rw [show μc ^ 2 = 1 from h, one_mul]
    have h3 : μc ^ 2 * μ ^ 2 = 1 := by rw [← mul_pow, mul_comm, hmm, one_pow]
    have hsq : μ ^ 2 = 1 := by rw [← h3, h2]
    have hμc' : μc = μ := by
      have : μc = μc * (μ * μ) := by rw [← sq, hsq, mul_one]
      rw [this, ← mul_assoc, mul_comm μc μ, hmm, one_mul]
    exact hμc'
  -- `S_t = v_t μ̄ᵗ` evolves by adding a linear trend
  set S : ℕ → ℂ := fun t => v t * μc ^ t with hS
  have hSrec : ∀ t, S (t + 1) = S t - c0 * (A * μc + (starRingEnd ℂ) A * μc * r ^ t) / 2 := by
    intro t
    simp only [hS, hv t, hr]
    have hp : μ ^ t * μc ^ t = 1 := by rw [← mul_pow, hmm, one_pow]
    have e : μc ^ (t + 1) = μc * μc ^ t := by ring
    rw [e]
    linear_combination (v t * μc ^ t) * hmm - (c0 * A * μc / 2) * hp
  have hclosed : ∀ t, S t = S 0 - (t : ℂ) * (c0 * A * μc / 2) -
      c0 * (starRingEnd ℂ) A * μc / 2 * ∑ s ∈ Finset.range t, r ^ s := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hSrec t, ih, Finset.sum_range_succ]
      push_cast
      ring
  have hr1' : ‖r‖ = 1 := by rw [hr, norm_pow, hμc1, one_pow]
  have hgeom : ∀ t, ‖∑ s ∈ Finset.range t, r ^ s‖ ≤ 2 / ‖r - 1‖ := by
    intro t
    have hne : r - 1 ≠ 0 := sub_ne_zero.2 hr1
    have hg := geom_sum_mul r t
    have hpos : 0 < ‖r - 1‖ := norm_pos_iff.2 hne
    rw [le_div_iff₀ hpos, ← norm_mul, hg]
    calc ‖r ^ t - 1‖ ≤ ‖r ^ t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hr1', one_pow, norm_one]; norm_num
  have hSb : ∀ t, ‖S t‖ ≤ M := fun t => by
    simp only [hS, norm_mul, norm_pow, hμc1, one_pow, mul_one]; exact hM t
  set K := ‖c0 * (starRingEnd ℂ) A * μc / 2‖ * (2 / ‖r - 1‖)
  have hk : 0 < ‖c0 * A * μc / 2‖ := by
    have : μc ≠ 0 := by intro h; rw [h] at hμc1; simp at hμc1
    have : c0 * A * μc / 2 ≠ 0 := by
      apply div_ne_zero (mul_ne_zero (mul_ne_zero hc0 hA) this) two_ne_zero
    exact norm_pos_iff.2 this
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + M + K) / ‖c0 * A * μc / 2‖)
  have h1 : (n : ℂ) * (c0 * A * μc / 2) =
      S 0 - S n - c0 * (starRingEnd ℂ) A * μc / 2 * ∑ s ∈ Finset.range n, r ^ s := by
    rw [hclosed n]; ring
  have h2 : (n : ℝ) * ‖c0 * A * μc / 2‖ ≤ M + M + K := by
    have := congrArg norm h1
    rw [norm_mul, Complex.norm_natCast] at this
    rw [this]
    calc ‖S 0 - S n - c0 * (starRingEnd ℂ) A * μc / 2 * ∑ s ∈ Finset.range n, r ^ s‖
        ≤ ‖S 0‖ + ‖S n‖ + ‖c0 * (starRingEnd ℂ) A * μc / 2‖ *
            ‖∑ s ∈ Finset.range n, r ^ s‖ := by
          refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
          rw [norm_mul]
      _ ≤ M + M + K := by
          have := mul_le_mul_of_nonneg_left (hgeom n)
            (norm_nonneg (c0 * (starRingEnd ℂ) A * μc / 2))
          linarith [hSb 0, hSb n]
  rw [div_lt_iff₀ hk] at hn
  linarith

/-- Woodford (2003), (2.20): under perfect foresight `E^ℂ_t` is the identity. -/
theorem EC_pf (t : ℕ) (z : Unit → ℂ) : EC perfectForesight t z = z := by
  funext ω
  apply Complex.ext
  · simp only [EC_re]; rfl
  · simp only [EC_im]; rfl

/-- Woodford (2003), (2.20): for a root `μ` of `βμ² − (1 + β − Z)μ + 1 = 0` and `y_t = Re μᵗ`
(zero initial value), `(𝒵 y)_{s+1} = Re(Z μ^{s+1})`. -/
theorem Zop_re_pow {β : ℝ} {Z μ : ℂ} (hr : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0)
    (s : ℕ) :
    Zop perfectForesight β (fun _ => 0) (fun t _ => (μ ^ t).re) (s + 1) () =
      (Z * μ ^ (s + 1)).re := by
  have key : (((1 + β : ℝ)) : ℂ) * μ ^ (s + 1) - (β : ℂ) * μ ^ (s + 2) - μ ^ s =
      Z * μ ^ (s + 1) := by
    push_cast
    linear_combination (-μ ^ s) * hr
  have := congrArg Complex.re key
  simp only [Complex.sub_re, Complex.re_ofReal_mul] at this
  simp only [Zop, lagW_succ]
  change (1 + β) * (μ ^ (s + 1)).re - β * (μ ^ (s + 2)).re - (μ ^ s).re = _
  exact this

/-- Woodford (2003), (2.20): `(𝒵² y)_{s+2} = Re(Z² μ^{s+2})` for `y_t = Re μᵗ`. -/
theorem ZZop_re_pow {β : ℝ} {Z μ : ℂ} (hr : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0)
    (s : ℕ) :
    Zop perfectForesight β (fun _ => 0)
      (Zop perfectForesight β (fun _ => 0) (fun t _ => (μ ^ t).re)) (s + 2) () =
      (Z ^ 2 * μ ^ (s + 2)).re := by
  have key : (((1 + β : ℝ)) : ℂ) * (Z * μ ^ (s + 2)) - (β : ℂ) * (Z * μ ^ (s + 3)) -
      Z * μ ^ (s + 1) = Z ^ 2 * μ ^ (s + 2) := by
    push_cast
    linear_combination (-(Z * μ ^ (s + 1))) * hr
  have := congrArg Complex.re key
  simp only [Complex.sub_re, Complex.re_ofReal_mul] at this
  simp only [Zop, lagW_succ]
  change (1 + β) * Zop perfectForesight β (fun _ => 0) (fun t _ => (μ ^ t).re) (s + 1 + 1) () -
    β * Zop perfectForesight β (fun _ => 0) (fun t _ => (μ ^ t).re) (s + 2 + 1) () -
    Zop perfectForesight β (fun _ => 0) (fun t _ => (μ ^ t).re) (s + 1) () = _
  rw [Zop_re_pow hr (s + 1), Zop_re_pow hr (s + 2), Zop_re_pow hr s]
  exact this

/-- Woodford (2003), (2.20): `𝒵` of the zero process (zero initial value) is zero. -/
theorem Zop_zero {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β : ℝ) (t : ℕ) (ω : Ω) :
    Zop 𝔼 β (fun _ => 0) (fun _ _ => 0) t ω = 0 := by
  have h : 𝔼.E t (fun _ : Ω => (0 : ℝ)) = fun _ => 0 := 𝔼.const t 0
  have hl : lagW (fun _ : Ω => (0 : ℝ)) (fun _ _ => (0 : ℝ)) t ω = 0 := by cases t <;> rfl
  simp only [Zop, hl]
  rw [show (fun _ : Ω => (0 : ℝ)) = (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) (t + 1) from rfl] at h
  rw [h]
  ring

/-- **Woodford (2003), (2.16)–(2.19), `κ_w ≠ κ_p` (FAILURE ON THE BOUNDARY OF THE ROOT
CONDITION)**: if a root `Z₁` of `P` has a factor root `μ` on the unit circle, then under perfect
foresight the bounded cost-push path `u_t = Re μᵗ` (and `w^n = 0`) admits NO bounded plan
satisfying the first-order conditions (zero predetermined values): the forcing resonates with the
unit root. -/
theorem foc_not_exists_boundary {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) {Z1 Z2 Z3 : ℂ}
    (hv1 : Z1 + Z2 + Z3 = ((-(cp2 P / P.lx) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((cp1 P / P.lx : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(cp0 P / P.lx) : ℝ) : ℂ)) {μ : ℂ}
    (hr : (P.beta : ℂ) * μ ^ 2 - (1 + P.beta - Z1) * μ + 1 = 0) (hμ1 : ‖μ‖ = 1) :
    ¬ ∃ π πw x w mp mw ups, PlanSW perfectForesight P (fun _ => 0)
      (fun t _ => (μ ^ t).re) (fun _ _ => 0) π πw x w ∧
      FOCsw perfectForesight P (fun _ => 0) (fun _ => 0) π πw x mp mw ups := by
  rintro ⟨π, πw, x, w, mp, mw, ups, hp, hfoc⟩
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  set β := P.beta with hβ
  set c := P.kw - P.kp with hcdef
  set ξ := P.xip + P.xiw with hξ
  have hpa : ∀ z : ℕ → Unit → ℝ, perfectForesight.Adapted z := fun _ _ => rfl
  -- μ is not real, hence neither is Z₁
  have hμ0 : μ ≠ 0 := by intro h; rw [h] at hμ1; simp at hμ1
  have hfac := charP_factor hlx.ne' hv1 hv2 hv3
  have hroot : charP P Z1 = 0 := by rw [hfac]; ring
  have hmm : μ * (starRingEnd ℂ) μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ1]; simp
  have hinv : μ⁻¹ = (starRingEnd ℂ) μ := (eq_inv_of_mul_eq_one_right hmm).symm
  have hZ : Z1 = 1 + β - β * μ - (starRingEnd ℂ) μ := by
    rw [← hinv]; field_simp; linear_combination hr
  have hZim : Z1.im = (1 - β) * μ.im := by rw [hZ]; simp; ring
  have hreal : (starRingEnd ℂ) μ ≠ μ := by
    intro h
    have him : μ.im = 0 := by
      have := congrArg Complex.im h; simp at this; linarith
    have hZr : Z1 = (Z1.re : ℂ) := Complex.ext (by simp) (by simp [hZim, him])
    have hZre : 0 ≤ Z1.re := by
      rw [hZ]
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
        Complex.re_ofReal_mul, Complex.conj_re]
      have hab : |μ.re| = 1 := by
        rw [← hμ1, Complex.norm_eq_sqrt_sq_add_sq, him]; simp [Real.sqrt_sq_eq_abs]
      have : μ.re = 1 ∨ μ.re = -1 := (abs_eq zero_le_one).1 hab
      rcases this with h1 | h1 <;> rw [h1] <;> nlinarith
    rw [hZr] at hroot
    exact charP_ne_zero_of_nonneg P hlx hlw hlp hkp hkw hxip hxiw hZre hroot
  have hμim : μ.im ≠ 0 := by
    intro h; apply hreal; apply Complex.ext <;> simp [h]
  have hne1 : (1 - β) * μ.im ≠ 0 := mul_ne_zero (by linarith) hμim
  have hZ1ne : Z1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hZim, Complex.zero_im] at this
    exact hne1 this
  have hZ1ξ : Z1 + ξ ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.add_im, Complex.ofReal_im, add_zero, hZim, Complex.zero_im] at this
    exact hne1 this
  -- the cubic equation and its outermost factor
  have hcub := (foc_imp_cubic perfectForesight hlx.ne' hc hp hfoc (hpa mp) (hpa mw)).1
  have hdc := (cubicR_iff perfectForesight hlx.ne').1 hcub
  rw [← hv1, ← hv2, ← hv3] at hdc
  have outer := cubicC_outer perfectForesight hdc
  set wc : ℕ → Unit → ℂ := fun t ω => (w t ω : ℂ) with hwc
  have hwca : AdaptedC perfectForesight wc := fun t => EC_pf t _
  have hwcb : BoundedC wc := by
    obtain ⟨M, hM⟩ := hp.2.2.2.2.2.2.2.2.2.2
    exact ⟨M, fun t ω => by rw [hwc, Complex.norm_real, Real.norm_eq_abs]; exact hM t ω⟩
  have iA : ∀ y : Unit → ℂ, EC perfectForesight 0 y = y := fun y => EC_pf 0 y
  have iB : ∀ y : Unit → ℂ, ∃ B, ∀ ω, ‖y ω‖ ≤ B := fun y => ⟨‖y ()‖, fun ω => by cases ω; rfl⟩
  set i0c : Unit → ℂ := fun ω => (((fun _ : Unit => (0 : ℝ)) ω : ℝ) : ℂ)
  set s1c : Unit → ℂ := fun ω => ((initS1 P (fun _ => 0) (fun _ => 0) (fun _ => 0) ω : ℝ) : ℂ)
  obtain ⟨aW1, bW1⟩ := ZopC_bdd_adapted perfectForesight β hβ0.le (y₀ := i0c) (iA _) (iB _)
    hwca hwcb
  obtain ⟨aW2, bW2⟩ := ZopC_bdd_adapted perfectForesight β hβ0.le (y₀ := s1c) (iA _) (iB _)
    aW1 bW1
  obtain ⟨aV, bV⟩ := lin_bdd_adapted perfectForesight 1 (-(Z2 + Z3)) aW2 aW1 bW2 bW1
  obtain ⟨-, ⟨Y, hY⟩⟩ := lin_bdd_adapted perfectForesight 1 (Z2 * Z3) aV hwca bV hwcb
  obtain ⟨U2, u2₀, hY', hrec⟩ : ∃ (U2 : ℕ → Unit → ℂ) (u2₀ : Unit → ℂ), (∀ t ω, ‖U2 t ω‖ ≤ Y) ∧
      ∀ t ω, ZopC perfectForesight β u2₀ U2 t ω - Z1 * U2 t ω =
        (((forcingF perfectForesight P (fun t _ => (μ ^ t).re) (fun _ _ => 0) t ω) / P.lx :
          ℝ) : ℂ) := ⟨_, _, hY, outer⟩
  -- the forcing at dates t ≥ 2
  set A : ℂ := (c : ℂ) * (Z1 ^ 2 + ξ * Z1) * μ ^ 2 with hA
  have hF : ∀ t, (((forcingF perfectForesight P (fun t _ => (μ ^ t).re) (fun _ _ => 0) (t + 2)
      ()) / P.lx : ℝ) : ℂ) = (A * μ ^ t + (starRingEnd ℂ) A * (starRingEnd ℂ) μ ^ t) / 2 := by
    intro t
    have z1 : ∀ t, Zop perfectForesight P.beta (fun _ => 0) (fun _ _ => 0) t () = 0 :=
      fun t => Zop_zero perfectForesight P.beta t ()
    have z2 : ∀ t, Zop perfectForesight P.beta (fun _ => 0)
        (Zop perfectForesight P.beta (fun _ => 0) (fun _ _ => 0)) t () = 0 := by
      intro t
      rw [show Zop perfectForesight P.beta (fun _ => 0) (fun _ _ => (0 : ℝ)) =
        (fun _ _ => (0 : ℝ)) from funext fun t => funext fun ω => by
          cases ω; exact z1 t]
      exact z1 t
    have h1 := Zop_re_pow hr (t + 1)
    have h2 := ZZop_re_pow hr t
    simp only [forcingF, z1, z2]
    rw [show t + 2 = t + 1 + 1 from rfl, h1, show t + 1 + 1 = t + 2 from rfl, h2]
    have hre : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (z + (starRingEnd ℂ) z) / 2 := fun z =>
      Complex.re_eq_add_conj z
    have e : (((P.kw - P.kp) * P.lx * (Z1 ^ 2 * μ ^ (t + 2)).re +
        (P.xip + P.xiw) * (P.kw - P.kp) * P.lx * (Z1 * μ ^ (t + 2)).re) / P.lx : ℝ) =
        (((c : ℂ) * (Z1 ^ 2 + ξ * Z1) * μ ^ (t + 2)).re : ℝ) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.mul_im, hcdef, hξ]
      field_simp
      ring
    simp only [mul_zero, add_zero, zero_add, sub_zero]
    rw [show ((P.kw - P.kp) * P.lx * (Z1 ^ 2 * μ ^ (t + 2)).re +
        (P.xip + P.xiw) * (P.kw - P.kp) * P.lx * (Z1 * μ ^ (t + 2)).re) / P.lx =
        (((c : ℂ) * (Z1 ^ 2 + ξ * Z1) * μ ^ (t + 2)).re : ℝ) from e, hre]
    simp only [map_mul, map_pow, map_add, Complex.conj_ofReal, hA]
    ring
  -- the recursion for `v_t = y_t − μ_b y_{t−1}`, `μ_b = 1/(βμ)`
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
  set μb : ℂ := ((β : ℂ) * μ)⁻¹ with hμbdef
  have hμb : μb * ((β : ℂ) * μ) = 1 := inv_mul_cancel₀ (mul_ne_zero hβc hμ0)
  set H : ℕ → ℂ := fun t => (((forcingF perfectForesight P (fun t _ => (μ ^ t).re)
    (fun _ _ => 0) t ()) / P.lx : ℝ) : ℂ) with hH
  set v : ℕ → ℂ := fun t => U2 t () - μb * lagC u2₀ U2 t () with hv
  have hrec' : ∀ t, v (t + 1) = μ * v t - (1 / (β : ℂ)) * H t := by
    intro t
    have h1 := hrec t ()
    simp only [ZopC, EC_pf] at h1
    have hb1 : (β : ℂ) * (1 / (β : ℂ)) = 1 := by field_simp
    have key : (β : ℂ) * μ * (v (t + 1) - (μ * v t - (1 / (β : ℂ)) * H t)) = 0 := by
      simp only [hv, lagC_succ]
      linear_combination (-μ) * h1 - (U2 t ()) * hr - (U2 t ()) * hμb +
        μ * lagC u2₀ U2 t () * hμb + μ * H t * hb1
    have := (mul_eq_zero.1 key).resolve_left (mul_ne_zero hβc hμ0)
    linear_combination this
  have hA0 : A ≠ 0 := by
    have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have : Z1 ^ 2 + ξ * Z1 = Z1 * (Z1 + ξ) := by ring
    rw [hA, this]
    exact mul_ne_zero (mul_ne_zero hcc (mul_ne_zero hZ1ne (by exact_mod_cast hZ1ξ)))
      (pow_ne_zero 2 hμ0)
  have hc0 : (1 / (β : ℂ)) ≠ 0 := one_div_ne_zero hβc
  refine no_bounded_resonant hμ1 hreal hA0 hc0 (v := fun t => v (t + 2)) (fun t => ?_)
    ⟨Y + ‖μb‖ * max ‖u2₀ ()‖ Y, fun t => ?_⟩
  · rw [show t + 1 + 2 = (t + 2) + 1 from rfl, hrec' (t + 2), ← hF t]
  · simp only [hv]
    refine (norm_sub_le _ _).trans (add_le_add (hY' _ _) ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [show t + 2 = (t + 1) + 1 from rfl, lagC_succ]
    exact (hY' _ _).trans (le_max_right _ _)

/-! ### The exact region -/

/-- Woodford (2003), (2.20): any root of `P` can be listed first in a Vieta triple. -/
theorem vieta_root_first {P : SW} (hlx : P.lx ≠ 0) {Z : ℂ} (hZ : charP P Z = 0) :
    ∃ Z2 Z3 : ℂ, Z + Z2 + Z3 = ((-(cp2 P / P.lx) : ℝ) : ℂ) ∧
      Z * Z2 + Z * Z3 + Z2 * Z3 = ((cp1 P / P.lx : ℝ) : ℂ) ∧
      Z * Z2 * Z3 = ((-(cp0 P / P.lx) : ℝ) : ℂ) := by
  obtain ⟨Z1, Z2, Z3, h1, h2, h3⟩ := cubic_vieta_exists (p2 := cp2 P) (p1 := cp1 P)
    (p0 := cp0 P) hlx
  rw [charP_factor hlx h1 h2 h3] at hZ
  have hl : (P.lx : ℂ) ≠ 0 := by exact_mod_cast hlx
  rcases mul_eq_zero.1 hZ with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hl
      · rw [sub_eq_zero] at h; subst h; exact ⟨Z2, Z3, h1, h2, h3⟩
    · rw [sub_eq_zero] at h; subst h
      exact ⟨Z1, Z3, by rw [← h1]; ring, by rw [← h2]; ring, by rw [← h3]; ring⟩
  · rw [sub_eq_zero] at h; subst h
    exact ⟨Z1, Z2, by rw [← h1]; ring, by rw [← h2]; ring, by rw [← h3]; ring⟩

/-- **Woodford (2003), §2.2, `κ_w ≠ κ_p` (THE EXACT REGION, perfect foresight)**: with all
parameters positive and `κ_w ≠ κ_p`, a bounded plan satisfying the first-order conditions exists
for EVERY bounded disturbance path and every pair of initial multipliers (`w_{t₀−1} = 0`) if and
only if the root condition `StableRoots P` holds, i.e. iff every root of
`P(Z) = λ_x Z(Z + ξ)² + λ_w(κ_w Z + Δ)² + λ_p(κ_p Z + Δ)²` lies strictly outside the ellipse
`ellForm β Z ≤ 1` (`stable_iff_ellForm`). Inside the ellipse existence fails for some initial
multipliers (`foc_not_determinate`), on it for a resonant cost-push path
(`foc_not_exists_boundary`); in the region the solution is moreover unique
(`foc_existsUnique`). -/
theorem determinacy_iff_stableRoots {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) :
    (∀ u wn : ℕ → Unit → ℝ, BoundedProc u → BoundedProc wn → ∀ a b : ℝ,
      ∃ π πw x w mp mw ups, PlanSW perfectForesight P (fun _ => 0) u wn π πw x w ∧
        FOCsw perfectForesight P (fun _ => a) (fun _ => b) π πw x mp mw ups) ↔
      StableRoots P := by
  have hpa : ∀ z : ℕ → Unit → ℝ, perfectForesight.Adapted z := fun _ _ => rfl
  have i0 : ∀ k : ℝ, perfectForesight.E 0 (fun _ : Unit => k) = fun _ => k := fun _ => rfl
  have ib : ∀ k : ℝ, ∃ B, ∀ ω : Unit, |(fun _ : Unit => k) ω| ≤ B := fun k => ⟨|k|, fun _ => le_rfl⟩
  constructor
  · intro h
    by_contra hR
    simp only [StableRoots, not_forall, not_exists, not_and] at hR
    obtain ⟨Z, hZ, hno⟩ := hR
    have hnot : ¬ 1 < ellForm P.beta Z := fun hE => by
      obtain ⟨μ, hr, hμ⟩ := (stable_iff_ellForm hβ0 hβ1 Z).2 hE
      exact absurd hμ (not_lt.2 (le_of_not_gt fun hlt => (hno μ hr) |> fun h' => h' hlt))
    obtain ⟨Z2, Z3, hv1, hv2, hv3⟩ := vieta_root_first hlx.ne' hZ
    rcases lt_or_eq_of_le (not_lt.1 hnot) with hin | hon
    · -- strictly inside
      have hD : Dst P ≠ 0 := by unfold Dst; positivity
      exact foc_not_determinate perfectForesight hβ0 hβ1 hlx.ne' hne hD hv1 hv2 hv3 hin
        (fun _ _ => 0) (fun _ _ => 0) (fun a b => by
          obtain ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩ := h (fun _ _ => 0) (fun _ _ => 0)
            ⟨0, fun _ _ => by simp⟩ ⟨0, fun _ _ => by simp⟩ a b
          exact ⟨π, πw, x, w, mp, mw, ups, hp, hf, hpa mp, hpa mw⟩)
    · -- on the ellipse: a unit root
      obtain ⟨μ0, hr0⟩ := exists_mu_root P.beta hβ0.ne' Z
      have hμ0 : μ0 ≠ 0 := by rintro rfl; simp at hr0
      have hid := ellForm_sub_one hβ0 hβ1 hr0 hμ0
      rw [hon, sub_self] at hid
      have hq : 0 < Complex.normSq μ0 := Complex.normSq_pos.2 hμ0
      have hpos : 0 < μ0.re ^ 2 / (1 + P.beta) ^ 2 + μ0.im ^ 2 / (1 - P.beta) ^ 2 := by
        have hm : 0 < μ0.re ^ 2 + μ0.im ^ 2 := by rw [Complex.normSq_apply] at hq; nlinarith
        have hd : μ0.im ^ 2 / (1 + P.beta) ^ 2 ≤ μ0.im ^ 2 / (1 - P.beta) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by nlinarith) (by nlinarith)
        have : 0 < (μ0.re ^ 2 + μ0.im ^ 2) / (1 + P.beta) ^ 2 := by positivity
        rw [add_div] at this
        linarith
      have h0 : (1 - Complex.normSq μ0) * (1 - P.beta ^ 2 * Complex.normSq μ0) = 0 := by
        have := hid.symm
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact (mul_eq_zero.1 h).resolve_right hpos.ne'
        · exact absurd h (pow_ne_zero 2 hq.ne')
      -- a root of modulus one
      obtain ⟨μ, hr, hμ1⟩ : ∃ μ : ℂ, (P.beta : ℂ) * μ ^ 2 - (1 + P.beta - Z) * μ + 1 = 0 ∧
          ‖μ‖ = 1 := by
        rcases mul_eq_zero.1 h0 with h | h
        · refine ⟨μ0, hr0, ?_⟩
          have : Complex.normSq μ0 = 1 := by linarith
          rw [Complex.normSq_eq_norm_sq] at this
          nlinarith [norm_nonneg μ0]
        · have hbc : (P.beta : ℂ) ≠ 0 := by exact_mod_cast hβ0.ne'
          refine ⟨((P.beta : ℂ) * μ0)⁻¹, ?_, ?_⟩
          · field_simp
            linear_combination hr0
          · have h2 : P.beta ^ 2 * ‖μ0‖ ^ 2 = 1 := by
              rw [Complex.normSq_eq_norm_sq] at h; linarith
            have h3 : P.beta * ‖μ0‖ = 1 := by
              have hp : 0 ≤ P.beta * ‖μ0‖ := by positivity
              nlinarith [sq_nonneg (P.beta * ‖μ0‖ - 1)]
            rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0, h3,
              inv_one]
      apply foc_not_exists_boundary hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hv1 hv2 hv3 hr hμ1
      exact h _ _ ⟨1, fun t _ => (Complex.abs_re_le_norm _).trans (by
        rw [norm_pow, hμ1, one_pow])⟩ ⟨0, fun _ _ => by simp⟩ 0 0
  · intro hR u wn hu hwn a b
    obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hf, -⟩, -⟩ := foc_existsUnique perfectForesight hβ0
      hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR hu (hpa u) hwn (hpa wn) (ib 0) (ib a) (ib b)
      (i0 0) (i0 a) (i0 b)
    exact ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩

/-- **Woodford (2003), (2.20) corrected, `κ_w ≠ κ_p` (THE EXACT REGION FOR THE TARGET CRITERION,
perfect foresight)**: commitment from `t₀` to the corrected criterion determines a bounded
equilibrium for every bounded disturbance path and all predetermined `x_{t₀−1}`, `e₀`
(`w_{t₀−1} = 0`) iff the root condition holds; in the region the equilibrium is unique
(`criterion_existsUnique`) and optimal from a timeless perspective (`criterionC_timeless`). -/
theorem criterion_determinacy_iff_stableRoots {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) :
    (∀ u wn : ℕ → Unit → ℝ, BoundedProc u → BoundedProc wn → ∀ x₀ e₀ : ℝ,
      ∃ π πw x w, PlanSW perfectForesight P (fun _ => 0) u wn π πw x w ∧
        CriterionC perfectForesight P (fun _ => x₀) π πw x ∧
        ∀ ω, critC0 perfectForesight P (fun _ => x₀) (fun _ => e₀) π πw x ω = 0) ↔
      StableRoots P := by
  have hpa : ∀ z : ℕ → Unit → ℝ, perfectForesight.Adapted z := fun _ _ => rfl
  have ib : ∀ k : ℝ, ∃ B, ∀ ω : Unit, |(fun _ : Unit => k) ω| ≤ B := fun k => ⟨|k|, fun _ => le_rfl⟩
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD : P.kp * P.xiw + P.kw * P.xip ≠ 0 := by positivity
  constructor
  · intro h
    refine (determinacy_iff_stableRoots hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne).1 ?_
    intro u wn hu hwn a b
    obtain ⟨π, πw, x, w, hp, hcr, h0⟩ := h u wn hu hwn ((P.kp * a + P.kw * b) / P.lx + P.xstar)
      (-((P.kw - P.kp) * (P.xip * a - P.xiw * b)))
    obtain ⟨mp, mw, ups, hfoc, -, -, -⟩ := criterion_imp_foc perfectForesight hkp hkw hxip hxiw
      hne (B := |(P.kp * a + P.kw * b) / P.lx + P.xstar|) (fun _ => le_rfl) rfl hp hcr h0
    have e1 : (fun ω : Unit => (P.xiw * (P.lx * ((fun _ => (P.kp * a + P.kw * b) / P.lx +
        P.xstar) ω - P.xstar)) + P.kw * (-(fun _ => -((P.kw - P.kp) * (P.xip * a -
        P.xiw * b))) ω / (P.kw - P.kp))) / (P.kp * P.xiw + P.kw * P.xip)) = fun _ => a := by
      funext ω; field_simp; ring
    have e2 : (fun ω : Unit => (P.xip * (P.lx * ((fun _ => (P.kp * a + P.kw * b) / P.lx +
        P.xstar) ω - P.xstar)) - P.kp * (-(fun _ => -((P.kw - P.kp) * (P.xip * a -
        P.xiw * b))) ω / (P.kw - P.kp))) / (P.kp * P.xiw + P.kw * P.xip)) = fun _ => b := by
      funext ω; field_simp; ring
    rw [e1, e2] at hfoc
    exact ⟨π, πw, x, w, mp, mw, ups, hp, hfoc⟩
  · intro hR u wn hu hwn x₀ e₀
    obtain ⟨π, πw, x, w, h, -⟩ := criterion_existsUnique perfectForesight hβ0 hβ1 hlx hlp hlw
      hkp hkw hxip hxiw hne hR hu (hpa u) hwn (hpa wn) (ib 0) (ib x₀) (ib e₀) rfl rfl rfl
    exact ⟨π, πw, x, w, h⟩

end Woodford.OptimalPolicyRules.InflTargetStickyWages
