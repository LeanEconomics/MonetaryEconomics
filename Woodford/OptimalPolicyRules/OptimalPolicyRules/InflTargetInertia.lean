/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.ForwardSolution
import OptimalPolicyRules.QuadraticRoots
import OptimalPolicyRules.ExpectationsFiniteTree
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Optimal inflation targeting with inflation inertia

Woodford (2003), *Interest and Prices*, Chapter 8, §2.1, pp. 560–565 (with the Chapter 7, §5
result it restates).

The model is the aggregate-supply relation (2.1) `π_t = κ x_t + β E_t π_{t+1} + u_t` and the
loss (2.2)–(2.3) `E_0 ∑ βᵗ (π_t² + λ (x_t − x*)²)`; with indexation it is (2.6)–(2.8) with
`π_t` replaced by `π_t − γ π_{t−1}`.  Dates are `t = 0, 1, …` with `t₀ = 0`; the predetermined
values at date `t₀ − 1 = −1` enter through `lagW x₀ x` (`lagW x₀ x 0 = x₀`,
`lagW x₀ x (t+1) = x t`).

## Main results

* The workhorse second-order equation `β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t`
  (`SecondOrder`, proved locally; the stable root `μ₁` is `QuadraticRoots.lam1`), the
  factorisation `secondOrder_iff_w`, and `secondOrder_existsUnique`: for
  `c > 0`, bounded adapted `f` and a bounded date-0 initial condition there is exactly one
  bounded adapted solution, `y_t = μ₁ y_{t−1} − μ₁ ∑ (βμ₁)ʲ E_t f_{t+j}` (`ysol`).
* Lagrangian sufficiency (proved locally): `excess_hasSum` (the excess expected loss of any plan
  over a plan satisfying the first-order conditions is a genuine infinite sum of nonnegative
  terms), `E0_pull` (pull-out + tower), `expLossOf_hasSum`.
* (2.1)–(2.5) (Chapter 7, Prop. 7.15): `foc_sufficient` (FOC + feasibility ⇒ minimum among all
  bounded plans with the same `π_{t₀}`, and among all plans when the initial multiplier is
  `0`), `foc_unique` (strict convexity), `as_iff_secondOrder`, `ruleEq_existsUnique`,
  `criterion_timeless`, the time-invariant representation `ruleEq_representation` (1.5), and
  `baseline_robustlyOptimal`: the criterion `π_t + φ (x_t − x_{t−1}) = 0`, `φ = λ/κ`, is robustly
  optimal (`RobustlyOptimal`) — for every bounded adapted disturbance process it determines a
  unique bounded equilibrium, and that equilibrium is optimal from a timeless perspective
  (`TimelessOptimal`).  `timeless_criterion_pf`: under perfect foresight every timelessly
  optimal plan satisfies the criterion (necessity).
* (2.6)–(2.9): `asInd_iff_as_qd` (the reduction to `π^{qd}`), `printed_asInd_counterexample`
  (the printed (2.6) has `E_t[π_{t+1} − π_t]`, which is wrong unless `γ = 1`),
  `indexation_robustlyOptimal` (the criterion (2.9) is robustly optimal for `0 ≤ γ ≤ 1`).
* (2.10): `criterion29_iff_criterion210` (with `γ = 1`, commitment to (2.9) from `t₀` is
  commitment to (2.10) with `π̄ = π_{t₀−1} + φ x_{t₀−1}`), `diff_criterion210` and
  `criterion210_not_imp_criterion25` (survey E15: the first difference of (2.10) is (2.9) with
  `γ = 1`, not (2.5)), `rule210_existsUnique`, `rule210_timeless` (every (2.10) rule is
  optimal from a timeless perspective), `rule210_robustlyOptimal` (for every constant `π̄`),
  and `rule210_diff` (p. 564: the choice of `π̄` changes the equilibrium only by a
  deterministic component, transitory in `x_t` and in `Δπ_t`, which moves long-run inflation
  by `π̄ − π̄'`; `rule210_diff_tendsto`).
* `baseline_robustlyOptimal_finiteTree`, `indexation_robustlyOptimal_finiteTree`: the pull-out
  hypothesis holds on every finite event tree, so the results apply under genuine uncertainty.
-/

namespace Woodford.OptimalPolicyRules.InflTargetInertia

open Filter Topology
open ForwardSolution (E_of_known)
open QuadraticRoots (lam1 lam1_root lam1_pos lam1_lt_one beta_lam1_mem)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Lags with a predetermined initial value -/

/-- Woodford (2003), §2.1, p. 561: the lag of a process with a given date-`t₀ − 1` value,
`(lagW x₀ x)_0 = x₀` and `(lagW x₀ x)_{t+1} = x_t`. -/
def lagW (x₀ : Ω → ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => x₀
  | t + 1 => x t

/-- Woodford (2003), p. 561: `(lagW x₀ x)_0 = x₀`. -/
@[simp] theorem lagW_zero (x₀ : Ω → ℝ) (x : ℕ → Ω → ℝ) : lagW x₀ x 0 = x₀ := rfl

/-- Woodford (2003), p. 561: `(lagW x₀ x)_{t+1} = x_t`. -/
@[simp] theorem lagW_succ (x₀ : Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : lagW x₀ x (t + 1) = x t :=
  rfl

/-- Woodford (2003), p. 561: a lagged adapted process with a date-0 initial value is adapted. -/
theorem lagW_adapted {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} (h0 : 𝔼.E 0 x₀ = x₀) (hx : 𝔼.Adapted x) :
    𝔼.Adapted (lagW x₀ x) := by
  intro t
  cases t with
  | zero => exact h0
  | succ t =>
    change 𝔼.E (t + 1) (x t) = x t
    conv_lhs => rw [← hx t]
    rw [𝔼.known (Nat.le_succ t), hx t]

/-- Woodford (2003), p. 561: a lagged bounded process with a bounded initial value is
bounded. -/
theorem lagW_bounded {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} {B M : ℝ} (h0 : ∀ ω, |x₀ ω| ≤ B)
    (hx : ∀ t ω, |x t ω| ≤ M) : ∀ t ω, |lagW x₀ x t ω| ≤ max B M := by
  intro t ω
  cases t with
  | zero => exact (h0 ω).trans (le_max_left _ _)
  | succ t => exact (hx t ω).trans (le_max_right _ _)

/-! ### Backward recursions `y_t = a y_{t−1} + w_t` -/

/-- Woodford (2003), §2.1 (the backward part of the workhorse, survey §4.3): the solution of
`y_t = a y_{t−1} + w_t` with `y_{−1} = y₀`. -/
def backRec (a : ℝ) (y₀ : Ω → ℝ) (w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => a • y₀ + w 0
  | t + 1 => a • backRec a y₀ w t + w (t + 1)

/-- Woodford (2003), survey §4.3: `backRec` solves `y_t = a y_{t−1} + w_t`. -/
theorem backRec_eq (a : ℝ) (y₀ : Ω → ℝ) (w : ℕ → Ω → ℝ) (t : ℕ) :
    backRec a y₀ w t = a • lagW y₀ (backRec a y₀ w) t + w t := by
  cases t <;> rfl

/-- Woodford (2003), survey §4.3: `backRec` is the only solution of `y_t = a y_{t−1} + w_t`
with `y_{−1} = y₀`. -/
theorem eq_backRec {a : ℝ} {y₀ : Ω → ℝ} {w y : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = a • lagW y₀ y t + w t) : y = backRec a y₀ w := by
  funext t
  induction t with
  | zero => rw [hy 0]; rfl
  | succ t ih => rw [hy (t + 1)]; simp only [lagW_succ, ih]; rfl

/-- Woodford (2003), survey §4.3: for `0 ≤ a < 1` the backward recursion keeps a bounded
forcing bounded. -/
theorem backRec_bounded {a Y W : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {y₀ : Ω → ℝ}
    {w : ℕ → Ω → ℝ} (hy₀ : ∀ ω, |y₀ ω| ≤ Y) (hw : ∀ t ω, |w t ω| ≤ W) :
    ∀ t ω, |backRec a y₀ w t ω| ≤ max Y (W / (1 - a)) := by
  set B := max Y (W / (1 - a))
  have h1a : 0 < 1 - a := by linarith
  have hWB : W ≤ (1 - a) * B := by
    have : W / (1 - a) ≤ B := le_max_right _ _
    rwa [div_le_iff₀ h1a, mul_comm] at this
  have step : ∀ (v : Ω → ℝ) (t : ℕ) (ω : Ω), |v ω| ≤ B → |a * v ω + w t ω| ≤ B := by
    intro v t ω hv
    calc |a * v ω + w t ω| ≤ |a * v ω| + |w t ω| := abs_add_le _ _
      _ = a * |v ω| + |w t ω| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ a * B + W := add_le_add (mul_le_mul_of_nonneg_left hv ha0) (hw t ω)
      _ ≤ B := by linarith
  intro t
  induction t with
  | zero => intro ω; exact step y₀ 0 ω ((hy₀ ω).trans (le_max_left _ _))
  | succ t ih => intro ω; exact step (backRec a y₀ w t) (t + 1) ω (ih ω)

/-- Woodford (2003), survey §4.3: `backRec` of adapted data with a date-0 initial value is
adapted. -/
theorem backRec_adapted {a : ℝ} {y₀ : Ω → ℝ} {w : ℕ → Ω → ℝ} (h0 : 𝔼.E 0 y₀ = y₀)
    (hw : 𝔼.Adapted w) : 𝔼.Adapted (backRec a y₀ w) := by
  intro t
  induction t with
  | zero => change 𝔼.E 0 (a • y₀ + w 0) = _; rw [map_add, map_smul, h0, hw 0]; rfl
  | succ t ih =>
    change 𝔼.E (t + 1) (a • backRec a y₀ w t + w (t + 1)) = _
    rw [map_add, map_smul, E_of_known 𝔼 (Nat.le_succ t) ih, hw (t + 1)]
    rfl

/-! ### The workhorse second-order expectational difference equation -/

/-- Woodford (2003), survey §4.3 (the workhorse of Ch. 7–8): `y` solves
`β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t` for every `t ≥ t₀ = 0`, `y_{−1} = y₀`. -/
def SecondOrder (β c : ℝ) (y₀ : Ω → ℝ) (f y : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, β * 𝔼.E t (y (t + 1)) ω - (1 + β + c) * y t ω + lagW y₀ y t ω = f t ω

/-- Woodford (2003), survey §4.3: the quasi-difference `w_t = y_t − μ y_{t−1}`. -/
def quasiDiff (μ : ℝ) (y₀ : Ω → ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => y t ω - μ * lagW y₀ y t ω

/-- Woodford (2003), survey §4.3 (the factorisation `(1 − μ₂L)(L⁻¹ − μ₁)y = f/β`): for an
adapted `y` and a nonzero root `μ`, the second-order equation is equivalent to the forward
equation `w_t = βμ E_t w_{t+1} − μ f_t` in the quasi-difference `w_t = y_t − μ y_{t−1}`. -/
theorem secondOrder_iff_w {β c μ : ℝ} (hμ : μ ≠ 0) (hroot : β * μ ^ 2 - (1 + β + c) * μ + 1 = 0)
    {y₀ : Ω → ℝ} {f y : ℕ → Ω → ℝ} (hya : 𝔼.Adapted y) :
    SecondOrder 𝔼 β c y₀ f y ↔
      ∀ t, quasiDiff μ y₀ y t =
        (β * μ) • 𝔼.E t (quasiDiff μ y₀ y (t + 1)) + (fun s => (-μ) • f s) t := by
  have hE : ∀ t ω, 𝔼.E t (quasiDiff μ y₀ y (t + 1)) ω = 𝔼.E t (y (t + 1)) ω - μ * y t ω := by
    intro t ω
    have : quasiDiff μ y₀ y (t + 1) = y (t + 1) - μ • y t := by
      funext ω'; simp [quasiDiff]
    rw [this, map_sub, map_smul, hya t]
    simp
  constructor
  · intro h t
    funext ω
    have h1 := h t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE]
    simp only [quasiDiff]
    linear_combination (-μ) * h1 + (y t ω) * hroot
  · intro h t ω
    have h1 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE, quasiDiff] at h1
    have h2 : μ * (β * 𝔼.E t (y (t + 1)) ω - (1 + β + c) * y t ω + lagW y₀ y t ω - f t ω) = 0 := by
      linear_combination (-1 : ℝ) * h1 + (y t ω) * hroot
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hμ
    · linarith

/-- Woodford (2003), survey §4.3: the forward part of the solution,
`w_t = −μ₁ ∑ⱼ (βμ₁)ʲ E_t f_{t+j}`. -/
noncomputable def wsol (β c : ℝ) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (β * lam1 β c) (fun s => (-lam1 β c) • f s)

/-- Woodford (2003), survey §4.3: the solution
`y_t = μ₁ y_{t−1} − μ₁ ∑ⱼ (βμ₁)ʲ E_t f_{t+j}` (equivalently `− β⁻¹ ∑ⱼ μ₂^{−j−1} E_t f_{t+j}`). -/
noncomputable def ysol (β c : ℝ) (y₀ : Ω → ℝ) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  backRec (lam1 β c) y₀ (wsol 𝔼 β c f)

/-- Woodford (2003), survey §4.3: the scaled forcing `−μ₁ f` is bounded. -/
theorem neg_mu_f_bounded {μ M : ℝ} (hμ : 0 < μ) {f : ℕ → Ω → ℝ} (hf : ∀ t ω, |f t ω| ≤ M) :
    ∀ t ω, |((fun s => (-μ) • f s) t) ω| ≤ μ * M := by
  intro t ω
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hμ]
  exact mul_le_mul_of_nonneg_left (hf t ω) hμ.le

/-- Woodford (2003), survey §4.3: the scaled forcing `−μ₁ f` is adapted. -/
theorem neg_mu_f_adapted {μ : ℝ} {f : ℕ → Ω → ℝ} (hfa : 𝔼.Adapted f) :
    𝔼.Adapted (fun s => (-μ) • f s) := fun t => by
  simp only [map_smul, hfa t]

/-- **Woodford (2003), survey §4.3 (the workhorse, existence and uniqueness)**: for
`0 < β < 1`, `c > 0`, a bounded adapted forcing `f` and a bounded initial condition `y₀`
known at date 0, `ysol` is a bounded adapted solution of
`β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t`, and it is the only one. -/
theorem secondOrder_existsUnique {β c M Y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c)
    {f : ℕ → Ω → ℝ} (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {y₀ : Ω → ℝ}
    (hy₀ : ∀ ω, |y₀ ω| ≤ Y) (hy₀a : 𝔼.E 0 y₀ = y₀) :
    (SecondOrder 𝔼 β c y₀ f (ysol 𝔼 β c y₀ f) ∧ 𝔼.Adapted (ysol 𝔼 β c y₀ f) ∧
      BoundedProc (ysol 𝔼 β c y₀ f)) ∧
    ∀ y, SecondOrder 𝔼 β c y₀ f y → 𝔼.Adapted y → BoundedProc y → y = ysol 𝔼 β c y₀ f := by
  have hμ0 := lam1_pos hβ0 hc
  have hμ1 := lam1_lt_one hβ0 hc
  obtain ⟨ha0, ha1⟩ := beta_lam1_mem hβ0 hβ1 hc
  set μ := lam1 β c with hμdef
  have hroot := lam1_root hβ0 hc
  rw [← hμdef] at hroot
  have hgb := neg_mu_f_bounded hμ0 hf
  have hga := neg_mu_f_adapted 𝔼 (μ := μ) hfa
  have hws := 𝔼.forwardSeries_solves ha0 ha1 hgb hga
  have hwa := 𝔼.forwardSeries_adapted ha0 ha1 hgb
  obtain ⟨W, hW⟩ := 𝔼.forwardSeries_bounded ha0 ha1 hgb
  have hya : 𝔼.Adapted (ysol 𝔼 β c y₀ f) := backRec_adapted 𝔼 hy₀a hwa
  have hqd : ∀ t, quasiDiff μ y₀ (ysol 𝔼 β c y₀ f) t = wsol 𝔼 β c f t := by
    intro t
    funext ω
    have := congrFun (backRec_eq μ y₀ (wsol 𝔼 β c f) t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [quasiDiff, ysol]
    rw [← hμdef]
    linarith
  refine ⟨⟨?_, hya, ⟨_, backRec_bounded hμ0.le hμ1 hy₀ hW⟩⟩, ?_⟩
  · rw [secondOrder_iff_w 𝔼 hμ0.ne' hroot hya]
    intro t
    rw [hqd, hqd]
    exact hws t
  · intro y hy hyA hyB
    obtain ⟨B, hB⟩ := hyB
    have hw := (secondOrder_iff_w 𝔼 hμ0.ne' hroot hyA).1 hy
    have hqb : BoundedProc (quasiDiff μ y₀ y) := by
      refine ⟨B + μ * max Y B, fun t ω => ?_⟩
      simp only [quasiDiff]
      refine (abs_sub _ _).trans (add_le_add (hB t ω) ?_)
      rw [abs_mul, abs_of_pos hμ0]
      exact mul_le_mul_of_nonneg_left (lagW_bounded hy₀ hB t ω) hμ0.le
    have heq := 𝔼.eq_forwardSeries ha0 ha1 hgb hga hw hqb
    apply eq_backRec
    intro t
    funext ω
    have := congrFun (congrFun heq t) ω
    simp only [quasiDiff] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wsol]
    rw [← hμdef, ← this]
    ring

/-! ### Expected discounted loss and Lagrangian sufficiency (survey §4.4, proved locally) -/

/-- Woodford (2003), (2.2), p. 560: the expected discounted loss `E_0 ∑_{t ≥ 0} βᵗ ℓ_t` of a
period-loss process `ℓ` (a date-0 random variable). -/
noncomputable def expLossOf (β : ℝ) (ℓ : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E 0 (fun ω => ∑' t, β ^ t * ℓ t ω)

/-- Woodford (2003), (2.2), p. 560: for a bounded period loss the expected loss is the genuine
infinite sum `∑ βᵗ E_0 ℓ_t` (`E_0` commutes with the geometrically dominated series). -/
theorem expLossOf_hasSum {β L : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ → Ω → ℝ}
    (hℓ : ∀ t ω, |ℓ t ω| ≤ L) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (ℓ t) ω) (expLossOf 𝔼 β ℓ ω) := by
  have hf : ∀ k ω, |β ^ k * ℓ k ω| ≤ β ^ k * L := fun k ω => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (hℓ k ω) (pow_nonneg hβ0 k)
  have hE := 𝔼.E_tsum hβ0 hβ1 hf 0 ω
  have heq : ∀ k, 𝔼.E 0 (fun ω' => β ^ k * ℓ k ω') ω = β ^ k * 𝔼.E 0 (ℓ k) ω := fun k => by
    have : (fun ω' => β ^ k * ℓ k ω') = β ^ k • ℓ k := rfl
    rw [this, map_smul]; rfl
  have hs : Summable (fun t => β ^ t * 𝔼.E 0 (ℓ t) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right L) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hℓ k) 0 ω) (pow_nonneg hβ0 k))
  convert hs.hasSum using 1
  change 𝔼.E 0 (fun ω' => ∑' k, β ^ k * ℓ k ω') ω = _
  rw [hE]
  exact tsum_congr heq

/-- Woodford (2003), §2, p. 560 (the Lagrangian argument): conditional expectations of a
nonnegative random variable are nonnegative. -/
theorem E_nonneg {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have := 𝔼.mono t (show (0 : Ω → ℝ) ≤ f from hf) ω
  rwa [map_zero] at this

/-- Woodford (2003), §2, p. 560 (the Lagrangian argument; the pull-out property and the law of
iterated expectations): for `a` known at `t`, `E_0 (a · E_t z) = E_0 (a z)`. -/
theorem E0_pull (hpo : 𝔼.PullOut) {t : ℕ} {a z : Ω → ℝ} (ha : 𝔼.E t a = a) :
    𝔼.E 0 (a * 𝔼.E t z) = 𝔼.E 0 (a * z) := by
  rw [← hpo t a z ha, 𝔼.tower (Nat.zero_le t)]

/-- Woodford (2003), §2, p. 560 (the Lagrangian argument, telescoping with a transversality
term; restated from the Galí Chapter 5 project): if `g_t = D_t + 2 (h_t − h_{t+1})`, `D_t ≥ 0`,
`h_0 = 0`, `h_t → 0` and `∑ g_t = G`, then `∑ D_t = G`. -/
theorem hasSum_of_telescope {g D h : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) (hD : ∀ t, 0 ≤ D t)
    (hgt : ∀ t, g t = D t + 2 * (h t - h (t + 1))) (h0 : h 0 = 0)
    (hh : Tendsto h atTop (𝓝 0)) : HasSum D G := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hD]
  have hpart : (fun n => ∑ t ∈ Finset.range n, D t) =
      fun n => ∑ t ∈ Finset.range n, g t + 2 * h n := by
    funext n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hgt n]; ring
  rw [hpart]
  simpa using hg.tendsto_sum_nat.add (hh.const_mul 2)

/-- **Woodford (2003), §2, p. 560 and Ch. 8 §1.1 (Lagrangian sufficiency, abstract form)**: if
the period losses of two plans satisfy `ℓ_t − ℓ*_t = D_t + 2 (H_t − β G_t)` pathwise with
`D_t ≥ 0`, `E_0 G_t = E_0 H_{t+1}` (the law of iterated expectations applied to the constraint
terms), `E_0 H_0 = 0` (the initial constraint) and `H` bounded (transversality), then the
excess expected loss is the genuine infinite sum `∑ βᵗ E_0 D_t`. -/
theorem excess_hasSum {β L Ls K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ ℓs D H G : ℕ → Ω → ℝ}
    (hℓ : ∀ t ω, |ℓ t ω| ≤ L) (hℓs : ∀ t ω, |ℓs t ω| ≤ Ls) (hD : ∀ t ω, 0 ≤ D t ω)
    (hH : ∀ t ω, |H t ω| ≤ K)
    (hid : ∀ t ω, ℓ t ω - ℓs t ω = D t ω + 2 * (H t ω - β * G t ω))
    (hG : ∀ t, 𝔼.E 0 (G t) = 𝔼.E 0 (H (t + 1))) (hH0 : 𝔼.E 0 (H 0) = 0) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (D t) ω) (expLossOf 𝔼 β ℓ ω - expLossOf 𝔼 β ℓs ω) := by
  refine hasSum_of_telescope
    ((expLossOf_hasSum 𝔼 hβ0 hβ1 hℓ ω).sub (expLossOf_hasSum 𝔼 hβ0 hβ1 hℓs ω))
    (fun t => mul_nonneg (pow_nonneg hβ0 t) (E_nonneg 𝔼 (hD t) 0 ω))
    (h := fun t => β ^ t * 𝔼.E 0 (H t) ω) (fun t => ?_) ?_ ?_
  · have hfun : ℓ t - ℓs t = D t + (2 : ℝ) • H t - (2 * β) • G t := by
      funext ω'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hid t ω']
      ring
    have := congrFun (congrArg (𝔼.E 0) hfun) ω
    rw [map_sub, map_sub, map_add, map_smul, map_smul, hG t] at this
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← mul_sub, this, pow_succ]
    ring
  · simp [hH0]
  · refine squeeze_zero_norm (a := fun t => β ^ t * K) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hH t) 0 ω) (pow_nonneg hβ0 t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K

/-- Woodford (2003), §2, p. 560: under the hypotheses of `excess_hasSum` the second plan has the
smaller expected loss, state by state. -/
theorem expLossOf_le_of_excess {β : ℝ} (hβ0 : 0 ≤ β) {ℓ ℓs D : ℕ → Ω → ℝ}
    (hD : ∀ t ω, 0 ≤ D t ω) {ω : Ω}
    (hs : HasSum (fun t => β ^ t * 𝔼.E 0 (D t) ω) (expLossOf 𝔼 β ℓ ω - expLossOf 𝔼 β ℓs ω)) :
    expLossOf 𝔼 β ℓs ω ≤ expLossOf 𝔼 β ℓ ω :=
  sub_nonneg.1 (hs.nonneg fun t => mul_nonneg (pow_nonneg hβ0 t) (E_nonneg 𝔼 (hD t) 0 ω))

/-- Woodford (2003), §2, p. 560 (uniqueness by strict convexity): if the excess loss is the sum
`∑ βᵗ E_0 D_t` and the two losses are equal at `ω`, then `E_0 D_t = 0` at `ω` for every `t`. -/
theorem E0_eq_zero_of_excess {β : ℝ} (hβ0 : 0 < β) {ℓ ℓs D : ℕ → Ω → ℝ}
    (hD : ∀ t ω, 0 ≤ D t ω) {ω : Ω}
    (hs : HasSum (fun t => β ^ t * 𝔼.E 0 (D t) ω) (expLossOf 𝔼 β ℓ ω - expLossOf 𝔼 β ℓs ω))
    (heq : expLossOf 𝔼 β ℓ ω = expLossOf 𝔼 β ℓs ω) (t : ℕ) : 𝔼.E 0 (D t) ω = 0 := by
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ0.le t)
    (E_nonneg 𝔼 (hD t) 0 ω))).1 hs
  have ht := congrFun hz t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at ht
  exact ht

/-- Woodford (2003), §2, p. 560: if `E_0 (a + c b) = 0` with `a, b ≥ 0` and `c > 0`, then
`E_0 a = 0` and `E_0 b = 0`. -/
theorem E0_split_zero {c : ℝ} (hc : 0 < c) {a b : Ω → ℝ} (ha : ∀ ω, 0 ≤ a ω)
    (hb : ∀ ω, 0 ≤ b ω) {ω : Ω} (h : 𝔼.E 0 (fun ω => a ω + c * b ω) ω = 0) :
    𝔼.E 0 a ω = 0 ∧ 𝔼.E 0 b ω = 0 := by
  have hsplit : (fun ω => a ω + c * b ω) = a + c • b := rfl
  rw [hsplit, map_add, map_smul] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  have h1 := E_nonneg 𝔼 ha 0 ω
  have h2 := E_nonneg 𝔼 hb 0 ω
  have h3 := mul_nonneg hc.le h2
  refine ⟨by linarith, ?_⟩
  have : c * 𝔼.E 0 b ω = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hc.ne'
  · exact h

/-- Woodford (2003), (2.3): a quadratic loss term in bounded variables is bounded. -/
theorem sq_bound {a A : ℝ} (h : |a| ≤ A) : |a ^ 2| ≤ A ^ 2 := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-! ### The baseline model (2.1)–(2.5) (Chapter 7, Proposition 7.15) -/

/-- Woodford (2003), (2.1), p. 560: the aggregate-supply relation
`π_t = κ x_t + β E_t π_{t+1} + u_t` at every date `t ≥ t₀` and state. -/
def AS (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω = κ * x t ω + β * 𝔼.E t (π (t + 1)) ω + u t ω

/-- Woodford (2003), (2.3), p. 561: the period loss `π_t² + λ (x_t − x*)²`. -/
def periodLoss (lam xstar : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => π t ω ^ 2 + lam * (x t ω - xstar) ^ 2

/-- Woodford (2003), §2.1 and fn. 6, p. 539: an admissible plan — bounded adapted inflation and
output gap satisfying (2.1) at every date and state. -/
def Plan (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 β κ u π x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x

/-- Woodford (2003), Ch. 7 (2.4)–(2.5) and Ch. 8 (1.9): the first-order conditions
`π_t + φ_t − φ_{t−1} = 0`, `λ (x_t − x*) − κ φ_t = 0` with multiplier `φ_t` and initial
multiplier `φ_{t₀−1} = m₀`. -/
def FOC (κ lam xstar : ℝ) (m₀ : Ω → ℝ) (π x m : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω + m t ω - lagW m₀ m t ω = 0 ∧ lam * (x t ω - xstar) - κ * m t ω = 0

/-- Woodford (2003), (2.3): the period loss of a bounded plan is bounded. -/
theorem periodLoss_bounded {lam xstar : ℝ} (hlam : 0 ≤ lam) {π x : ℕ → Ω → ℝ}
    (hπ : BoundedProc π) (hx : BoundedProc x) :
    ∃ L, ∀ t ω, |periodLoss lam xstar π x t ω| ≤ L := by
  obtain ⟨A, hA⟩ := hπ
  obtain ⟨B, hB⟩ := hx
  refine ⟨A ^ 2 + lam * (B + |xstar|) ^ 2, fun t ω => ?_⟩
  have h1 := sq_bound (hA t ω)
  have h2 := sq_bound ((abs_sub _ _).trans (add_le_add (hB t ω) le_rfl) :
    |x t ω - xstar| ≤ B + |xstar|)
  unfold periodLoss
  refine (abs_add_le _ _).trans (add_le_add h1 ?_)
  rw [abs_mul, abs_of_nonneg hlam]
  exact mul_le_mul_of_nonneg_left h2 hlam

/-- **Woodford (2003), Ch. 7 §5 and Ch. 8 (2.1)–(2.5) (the Lagrangian identity)**: if `(π*, x*)`
satisfies the first-order conditions with a bounded adapted multiplier and a bounded initial
multiplier `m₀`, and `(π, x)` is any other plan with `m₀ (π_0 − π*_0) = 0` (the timeless initial
constraint `π_0 = π*_0`, or `m₀ = 0` for the `t₀`-optimal plan), then the excess expected loss
is `∑ βᵗ E_0((π_t − π*_t)² + λ (x_t − x*_t)²)`. -/
theorem foc_excess (hpo : 𝔼.PullOut) {β κ lam xstar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hlam : 0 ≤ lam) {u π x πs xs m : ℕ → Ω → ℝ} {m₀ : Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hma : 𝔼.Adapted m) (hmb : BoundedProc m)
    (hm₀ : ∃ B, ∀ ω, |m₀ ω| ≤ B) (hfoc : FOC κ lam xstar m₀ πs xs m)
    (hinit : ∀ ω, m₀ ω * (π 0 ω - πs 0 ω) = 0) (ω : Ω) :
    HasSum (fun t => β ^ t *
        𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2 + lam * (x t ω - xs t ω) ^ 2) ω)
      (expLossOf 𝔼 β (periodLoss lam xstar π x) ω -
        expLossOf 𝔼 β (periodLoss lam xstar πs xs) ω) := by
  obtain ⟨hn, -, -, hπb, hxb⟩ := hp
  obtain ⟨hns, -, -, hπsb, hxsb⟩ := hps
  obtain ⟨L, hL⟩ := periodLoss_bounded (xstar := xstar) hlam hπb hxb
  obtain ⟨Ls, hLs⟩ := periodLoss_bounded (xstar := xstar) hlam hπsb hxsb
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨As, hAs⟩ := hπsb
  obtain ⟨Z, hZ⟩ := hmb
  obtain ⟨B, hB⟩ := hm₀
  have hlag := lagW_bounded hB hZ
  have hK : ∀ t ω, |(lagW m₀ m t * (π t - πs t)) ω| ≤ max B Z * (A + As) := fun t ω => by
    simp only [Pi.mul_apply, Pi.sub_apply, abs_mul]
    exact mul_le_mul (hlag t ω) ((abs_sub _ _).trans (add_le_add (hA t ω) (hAs t ω)))
      (abs_nonneg _) ((abs_nonneg _).trans (hlag t ω))
  refine excess_hasSum 𝔼 hβ0 hβ1 hL hLs (fun t ω => by positivity) hK
    (G := fun t => m t * 𝔼.E t (π (t + 1) - πs (t + 1))) (fun t ω => ?_) (fun t => ?_) ?_ ω
  · have n1 := hn t ω
    have n2 := hns t ω
    have f1 := (hfoc t ω).1
    have f2 := (hfoc t ω).2
    simp only [periodLoss, Pi.mul_apply, Pi.sub_apply, map_sub]
    linear_combination 2 * (π t ω - πs t ω) * f1 + 2 * (x t ω - xs t ω) * f2 -
      2 * m t ω * (n1 - n2)
  · exact E0_pull 𝔼 hpo (hma t)
  · have : lagW m₀ m 0 * (π 0 - πs 0) = 0 := by
      funext ω'; simpa using hinit ω'
    rw [this, map_zero]

/-- **Woodford (2003), Ch. 7 §5, Ch. 8 (2.1)–(2.5) (sufficiency of the first-order
conditions)**: a plan satisfying the first-order conditions (bounded adapted multiplier, bounded
initial multiplier `m₀`) has the smallest expected loss, state by state, among all plans with
`m₀ (π_0 − π*_0) = 0`. -/
theorem foc_sufficient (hpo : 𝔼.PullOut) {β κ lam xstar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hlam : 0 ≤ lam) {u π x πs xs m : ℕ → Ω → ℝ} {m₀ : Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hma : 𝔼.Adapted m) (hmb : BoundedProc m)
    (hm₀ : ∃ B, ∀ ω, |m₀ ω| ≤ B) (hfoc : FOC κ lam xstar m₀ πs xs m)
    (hinit : ∀ ω, m₀ ω * (π 0 ω - πs 0 ω) = 0) (ω : Ω) :
    expLossOf 𝔼 β (periodLoss lam xstar πs xs) ω ≤ expLossOf 𝔼 β (periodLoss lam xstar π x) ω :=
  expLossOf_le_of_excess 𝔼 hβ0 (fun t ω => by positivity)
    (foc_excess 𝔼 hpo hβ0 hβ1 hlam hp hps hma hmb hm₀ hfoc hinit ω)

/-- **Woodford (2003), Ch. 7 §5 (uniqueness of the optimum)**: a plan with the same expected
loss at `ω` as a plan satisfying the first-order conditions coincides with it in conditional
mean square, `E_0 (π_t − π*_t)² = E_0 (x_t − x*_t)² = 0`, for every `t`. -/
theorem foc_unique (hpo : 𝔼.PullOut) {β κ lam xstar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) {u π x πs xs m : ℕ → Ω → ℝ} {m₀ : Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hma : 𝔼.Adapted m) (hmb : BoundedProc m)
    (hm₀ : ∃ B, ∀ ω, |m₀ ω| ≤ B) (hfoc : FOC κ lam xstar m₀ πs xs m)
    (hinit : ∀ ω, m₀ ω * (π 0 ω - πs 0 ω) = 0) (ω : Ω)
    (heq : expLossOf 𝔼 β (periodLoss lam xstar π x) ω =
      expLossOf 𝔼 β (periodLoss lam xstar πs xs) ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 :=
  E0_split_zero 𝔼 hlam (fun ω => sq_nonneg _) (fun ω => sq_nonneg _)
    (E0_eq_zero_of_excess 𝔼 hβ0 (fun t ω => by positivity)
      (foc_excess 𝔼 hpo hβ0.le hβ1 hlam.le hp hps hma hmb hm₀ hfoc hinit ω) heq t)

/-! ### The target criterion (2.5) and its equilibrium -/

/-- Woodford (2003), (2.5), p. 561: the target criterion `π_t + φ (x_t − x_{t−1}) = 0` at every
date `t ≥ t₀` (with `x_{t₀−1} = x₀`). -/
def Criterion (φ : ℝ) (x₀ : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω + φ * (x t ω - lagW x₀ x t ω) = 0

/-- **Woodford (2003), Ch. 8 §1.1, Definition, pp. 538–539 (optimality from a timeless
perspective, for (2.1)–(2.3))**: a plan is timelessly optimal if it is admissible and minimises
the expected loss (2.2), state by state, among all admissible plans satisfying the additional
initial constraint (1.6) `π_{t₀} = π̄_{t₀}` with `π̄_{t₀}` its own initial inflation (the only
forward-looking variable of (2.1) is `π`).  The time-invariance requirement (1.5) of the
definition is `ruleEq_representation`. -/
def TimelessOptimal (β κ lam xstar : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  Plan 𝔼 β κ u π x ∧ ∀ π' x', Plan 𝔼 β κ u π' x' → π' 0 = π 0 →
    ∀ ω, expLossOf 𝔼 β (periodLoss lam xstar π x) ω ≤
      expLossOf 𝔼 β (periodLoss lam xstar π' x') ω

/-- **Woodford (2003), Ch. 8 §1.3, Definition, pp. 549–550 (robust optimality, for
(2.1)–(2.3))**: a time-invariant rule (a relation between `x_{t₀−1}`, `π` and `x`) is robustly
optimal if for EVERY bounded adapted disturbance process `u` and every bounded date-`t₀` initial
condition it determines a unique bounded adapted equilibrium, and every equilibrium under the rule
is optimal from a timeless perspective. -/
def RobustlyOptimal (β κ lam xstar : ℝ)
    (Rule : (Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop) : Prop :=
  ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∀ x₀ : Ω → ℝ, (∃ B, ∀ ω, |x₀ ω| ≤ B) →
    𝔼.E 0 x₀ = x₀ →
    (∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), Plan 𝔼 β κ u p.1 p.2 ∧ Rule x₀ p.1 p.2) ∧
    ∀ π x, Plan 𝔼 β κ u π x → Rule x₀ π x → TimelessOptimal 𝔼 β κ lam xstar u π x

/-- Woodford (2003), p. 569: the lag of an affine transformation is the affine transformation of
the lag. -/
theorem lagW_affine (a b : ℝ) (x₀ : Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lagW (fun ω => a * (x₀ ω - b)) (fun s ω => a * (x s ω - b)) t ω =
      a * (lagW x₀ x t ω - b) := by
  cases t <;> rfl

/-- Woodford (2003), p. 561: an affine transformation `a (x_t − b)` of an adapted process is
adapted. -/
theorem affine_adapted (a b : ℝ) {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    𝔼.Adapted (fun s ω => a * (x s ω - b)) := by
  intro t
  have : (fun ω => a * (x t ω - b)) = a • (x t - fun _ => b) := rfl
  change 𝔼.E t (fun ω => a * (x t ω - b)) = _
  rw [this, map_smul, map_sub, hx t, 𝔼.const]
  rfl

/-- Woodford (2003), p. 561: an affine transformation of a bounded process is bounded. -/
theorem affine_bounded (a b : ℝ) {x : ℕ → Ω → ℝ} (hx : BoundedProc x) :
    BoundedProc (fun s ω => a * (x s ω - b)) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨|a| * (M + |b|), fun t ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM t ω) le_rfl))
    (abs_nonneg a)

/-- **Woodford (2003), (2.5) and Ch. 7 (2.4)**: a plan satisfying the target criterion with
`φ = λ/κ` satisfies the first-order conditions with the multiplier `φ_t = (λ/κ)(x_t − x*)` and the
self-consistent initial multiplier `φ_{t₀−1} = (λ/κ)(x_{t₀−1} − x*)`. -/
theorem criterion_foc {κ lam xstar : ℝ} (hκ : κ ≠ 0) {x₀ : Ω → ℝ} {π x : ℕ → Ω → ℝ}
    (h : Criterion (lam / κ) x₀ π x) :
    FOC κ lam xstar (fun ω => lam / κ * (x₀ ω - xstar)) π x
      (fun s ω => lam / κ * (x s ω - xstar)) := by
  intro t ω
  rw [lagW_affine]
  have h1 := h t ω
  have h2 : κ * (lam / κ * (x t ω - xstar)) = lam * (x t ω - xstar) := by field_simp
  constructor
  · linear_combination h1
  · linarith

/-- **Woodford (2003), Ch. 7 Prop. 7.15 / Ch. 8 (2.5), p. 561 (optimality of the criterion)**:
every admissible plan satisfying `π_t + (λ/κ)(x_t − x_{t−1}) = 0` (bounded date-0 `x_{t₀−1}`) is
optimal from a timeless perspective. -/
theorem criterion_timeless (hpo : 𝔼.PullOut) {β κ lam xstar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hlam : 0 ≤ lam) (hκ : κ ≠ 0) {u π x : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hx₀ : ∃ B, ∀ ω, |x₀ ω| ≤ B) (hp : Plan 𝔼 β κ u π x) (hc : Criterion (lam / κ) x₀ π x) :
    TimelessOptimal 𝔼 β κ lam xstar u π x := by
  refine ⟨hp, fun π' x' hp' h0 ω => ?_⟩
  have hxa := hp.2.2.1
  have hxb := hp.2.2.2.2
  obtain ⟨B, hB⟩ := hx₀
  refine foc_sufficient 𝔼 hpo hβ0 hβ1 hlam hp' hp (affine_adapted 𝔼 _ _ hxa)
    (affine_bounded _ _ hxb) ⟨|lam / κ| * (B + |xstar|), fun ω => ?_⟩ (criterion_foc hκ hc)
    (fun ω => by rw [h0, sub_self, mul_zero]) ω
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hB ω) le_rfl))
    (abs_nonneg _)

/-- **Woodford (2003), (2.5) (uniqueness of the timeless optimum)**: a plan with the same initial
inflation and the same expected loss as a plan satisfying the criterion coincides with it in
conditional mean square. -/
theorem criterion_timeless_unique (hpo : 𝔼.PullOut) {β κ lam xstar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hlam : 0 < lam) (hκ : κ ≠ 0) {u π x π' x' : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hx₀ : ∃ B, ∀ ω, |x₀ ω| ≤ B) (hp : Plan 𝔼 β κ u π x) (hc : Criterion (lam / κ) x₀ π x)
    (hp' : Plan 𝔼 β κ u π' x') (h0 : π' 0 = π 0) (ω : Ω)
    (heq : expLossOf 𝔼 β (periodLoss lam xstar π' x') ω =
      expLossOf 𝔼 β (periodLoss lam xstar π x) ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (π' t ω - π t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (x' t ω - x t ω) ^ 2) ω = 0 := by
  obtain ⟨B, hB⟩ := hx₀
  refine foc_unique 𝔼 hpo hβ0 hβ1 hlam hp' hp (affine_adapted 𝔼 _ _ hp.2.2.1)
    (affine_bounded _ _ hp.2.2.2.2) ⟨|lam / κ| * (B + |xstar|), fun ω => ?_⟩
    (criterion_foc hκ hc) (fun ω => by rw [h0, sub_self, mul_zero]) ω heq t
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hB ω) le_rfl))
    (abs_nonneg _)

/-- Woodford (2003), (2.5): under the criterion, `E_t π_{t+1} = −φ (E_t x_{t+1} − x_t)`. -/
theorem E_infl_of_criterion {φ : ℝ} {x₀ : Ω → ℝ} {π x : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x)
    (hc : Criterion φ x₀ π x) (t : ℕ) (ω : Ω) :
    𝔼.E t (π (t + 1)) ω = -φ * (𝔼.E t (x (t + 1)) ω - x t ω) := by
  have : π (t + 1) = (-φ) • (x (t + 1) - x t) := by
    funext ω'
    have := hc (t + 1) ω'
    simp only [lagW_succ] at this
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  rw [this, map_smul, map_sub, hxa t]
  rfl

/-- **Woodford (2003), (2.1) + (2.5)**: for an adapted output gap, under the criterion with
`φ ≠ 0` the aggregate-supply relation is equivalent to the workhorse equation
`β E_t x_{t+1} − (1 + β + κ/φ) x_t + x_{t−1} = u_t/φ`. -/
theorem as_iff_secondOrder {β κ φ : ℝ} (hφ : φ ≠ 0) {u π x : ℕ → Ω → ℝ} {x₀ : Ω → ℝ}
    (hxa : 𝔼.Adapted x) (hc : Criterion φ x₀ π x) :
    AS 𝔼 β κ u π x ↔ SecondOrder 𝔼 β (κ / φ) x₀ (fun t => φ⁻¹ • u t) x := by
  constructor
  · intro h t ω
    have h1 := h t ω
    have h2 := hc t ω
    rw [E_infl_of_criterion 𝔼 hxa hc] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    have hinv : φ * φ⁻¹ = 1 := mul_inv_cancel₀ hφ
    linear_combination φ⁻¹ * h1 - φ⁻¹ * h2 -
      (β * 𝔼.E t (x (t + 1)) ω - β * x t ω - x t ω + lagW x₀ x t ω) * hinv
  · intro h t ω
    have h1 := h t ω
    have h2 := hc t ω
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [E_infl_of_criterion 𝔼 hxa hc]
    have hinv : φ * φ⁻¹ = 1 := mul_inv_cancel₀ hφ
    linear_combination h2 + φ * h1 + (κ * x t ω + u t ω) * hinv

/-- Woodford (2003), (2.5): the equilibrium output gap under the criterion,
`x_t = μ₁ x_{t−1} − μ₁ ∑ⱼ (βμ₁)ʲ E_t u_{t+j}/φ` with `μ₁` the stable root for `c = κ/φ`. -/
noncomputable def gapR (β κ φ : ℝ) (x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ysol 𝔼 β (κ / φ) x₀ (fun t => φ⁻¹ • u t)

/-- Woodford (2003), (2.5): the equilibrium inflation under the criterion,
`π_t = −φ (x_t − x_{t−1})`. -/
noncomputable def inflR (β κ φ : ℝ) (x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => -φ * (gapR 𝔼 β κ φ x₀ u t ω - lagW x₀ (gapR 𝔼 β κ φ x₀ u) t ω)

/-- **Woodford (2003), (2.5), and Ch. 7 §5 (determinacy under the criterion)**: for `κ, φ > 0`,
every bounded adapted cost-push process and every bounded date-0 `x_{t₀−1}`, the criterion and
(2.1) have exactly one bounded adapted solution, `(inflR, gapR)`. -/
theorem ruleEq_existsUnique {β κ φ M B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    {x₀ : Ω → ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hx₀a : 𝔼.E 0 x₀ = x₀) :
    (Plan 𝔼 β κ u (inflR 𝔼 β κ φ x₀ u) (gapR 𝔼 β κ φ x₀ u) ∧
      Criterion φ x₀ (inflR 𝔼 β κ φ x₀ u) (gapR 𝔼 β κ φ x₀ u)) ∧
    ∀ π x, Plan 𝔼 β κ u π x → Criterion φ x₀ π x →
      π = inflR 𝔼 β κ φ x₀ u ∧ x = gapR 𝔼 β κ φ x₀ u := by
  have hc : 0 < κ / φ := div_pos hκ hφ
  have hfb : ∀ t ω, |(fun t => φ⁻¹ • u t) t ω| ≤ φ⁻¹ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_left (hu t ω) (inv_nonneg.2 hφ.le)
  have hfa : 𝔼.Adapted (fun t => φ⁻¹ • u t) := fun t => by simp only [map_smul, hua t]
  obtain ⟨⟨hso, hya, hyb⟩, huniq⟩ := secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hfb hfa hx₀ hx₀a
  have hya' : 𝔼.Adapted (gapR 𝔼 β κ φ x₀ u) := hya
  have hcrit : Criterion φ x₀ (inflR 𝔼 β κ φ x₀ u) (gapR 𝔼 β κ φ x₀ u) := fun t ω => by
    simp only [inflR]
    ring
  have hla := lagW_adapted 𝔼 hx₀a hya
  obtain ⟨Y, hY⟩ := hyb
  refine ⟨⟨⟨(as_iff_secondOrder 𝔼 hφ.ne' hya hcrit).2 hso, fun t => ?_, hya,
    ⟨φ * (Y + max B Y), fun t ω => ?_⟩, ⟨Y, hY⟩⟩, hcrit⟩, fun π x hp hcr => ?_⟩
  · have : inflR 𝔼 β κ φ x₀ u t =
        (-φ) • (gapR 𝔼 β κ φ x₀ u t - lagW x₀ (gapR 𝔼 β κ φ x₀ u) t) := rfl
    rw [this, map_smul, map_sub, hya' t, lagW_adapted 𝔼 hx₀a hya' t]
  · simp only [inflR, abs_mul, abs_neg, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
      (add_le_add (hY t ω) (lagW_bounded hx₀ hY t ω))) hφ.le
  · have hx : x = gapR 𝔼 β κ φ x₀ u :=
      huniq x ((as_iff_secondOrder 𝔼 hφ.ne' hp.2.2.1 hcr).1 hp.1) hp.2.2.1 hp.2.2.2.2
    refine ⟨?_, hx⟩
    funext t ω
    have := hcr t ω
    simp only [inflR, ← hx]
    linarith

/-- **Woodford (2003), Ch. 8 (1.5), p. 538 (the time-invariant representation)**: in the
equilibrium under (2.5), `x_t = μ₁ x_{t−1} + w_t` and `π_t = φ(1 − μ₁) x_{t−1} − φ w_t`, where
`w_t = −μ₁ ∑ⱼ (βμ₁)ʲ E_t u_{t+j}/φ` depends only on date-`t` forecasts of the disturbances: the
nonpredetermined variables are a time-invariant function of the predetermined state and the
exogenous state. -/
theorem ruleEq_representation (β κ φ : ℝ) (x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    gapR 𝔼 β κ φ x₀ u t ω = lam1 β (κ / φ) * lagW x₀ (gapR 𝔼 β κ φ x₀ u) t ω +
        wsol 𝔼 β (κ / φ) (fun t => φ⁻¹ • u t) t ω ∧
      inflR 𝔼 β κ φ x₀ u t ω = φ * (1 - lam1 β (κ / φ)) * lagW x₀ (gapR 𝔼 β κ φ x₀ u) t ω -
        φ * wsol 𝔼 β (κ / φ) (fun t => φ⁻¹ • u t) t ω := by
  have h0 := congrFun (backRec_eq (lam1 β (κ / φ)) x₀ (wsol 𝔼 β (κ / φ) (fun t => φ⁻¹ • u t)) t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
  have h : gapR 𝔼 β κ φ x₀ u t ω = lam1 β (κ / φ) * lagW x₀ (gapR 𝔼 β κ φ x₀ u) t ω +
      wsol 𝔼 β (κ / φ) (fun t => φ⁻¹ • u t) t ω := h0
  refine ⟨h, ?_⟩
  simp only [inflR]
  rw [h]
  ring

/-- **Woodford (2003), Ch. 7 Prop. 7.15, Ch. 8 (2.1)–(2.5), pp. 560–561 (THE BASELINE ROBUSTLY
OPTIMAL CRITERION)**: for `0 < β < 1`, `κ, λ > 0`, the target criterion
`π_t + φ (x_t − x_{t−1}) = 0` with `φ = λ/κ` is robustly optimal: for every bounded adapted
cost-push process and initial `x_{t₀−1}` it determines a unique bounded equilibrium, which is
optimal from a timeless perspective. -/
theorem baseline_robustlyOptimal (hpo : 𝔼.PullOut) {β κ lam xstar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    RobustlyOptimal 𝔼 β κ lam xstar (fun x₀ π x => Criterion (lam / κ) x₀ π x) := by
  intro u ⟨M, hM⟩ hua x₀ ⟨B, hB⟩ hx₀a
  obtain ⟨hex, huniq⟩ := ruleEq_existsUnique 𝔼 hβ0 hβ1 hκ (div_pos hlam hκ) hM hua hB hx₀a
  refine ⟨⟨(inflR 𝔼 β κ (lam / κ) x₀ u, gapR 𝔼 β κ (lam / κ) x₀ u), hex, ?_⟩, ?_⟩
  · rintro ⟨π, x⟩ ⟨hp, hc⟩
    obtain ⟨h1, h2⟩ := huniq π x hp hc
    simp [h1, h2]
  · intro π x hp hc
    exact criterion_timeless 𝔼 hpo hβ0.le hβ1 hlam.le hκ.ne' ⟨B, hB⟩ hp hc

/-- **Woodford (2003), Ch. 7 §5 / Ch. 8 (2.5) (necessity, perfect foresight)**: every plan that
is optimal from a timeless perspective satisfies the target criterion
`π_t + (λ/κ)(x_t − x_{t−1}) = 0` at every date `t > t₀` (at `t₀` the criterion holds for the
self-consistent initial value of `x_{t₀−1}` implied by the constraint `π_{t₀} = π̄_{t₀}`). -/
theorem timeless_criterion_pf {β κ lam xstar M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Unit → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    {π x : ℕ → Unit → ℝ} (h : TimelessOptimal perfectForesight β κ lam xstar u π x) (t : ℕ)
    (ω : Unit) : π (t + 1) ω + lam / κ * (x (t + 1) ω - x t ω) = 0 := by
  set φ := lam / κ with hφdef
  have hφ : 0 < φ := div_pos hlam hκ
  have hc : 0 < κ / φ := div_pos hκ hφ
  set μ := lam1 β (κ / φ)
  have hμ1 := lam1_lt_one hβ0 hc
  have hpa : ∀ z : ℕ → Unit → ℝ, perfectForesight.Adapted z := fun _ _ => rfl
  set w0 := wsol perfectForesight β (κ / φ) (fun t => φ⁻¹ • u t) 0 ()
  set c := (π 0 () + φ * w0) / (φ * (1 - μ))
  have h1μ : 0 < φ * (1 - μ) := mul_pos hφ (by linarith)
  obtain ⟨⟨hpR, hcR⟩, -⟩ := ruleEq_existsUnique perfectForesight hβ0 hβ1 hκ hφ hu (hpa u)
    (x₀ := fun _ => c) (B := |c|) (fun _ => le_rfl) rfl
  have h0 : inflR perfectForesight β κ φ (fun _ => c) u 0 = π 0 := by
    funext ω'
    obtain ⟨-, hr⟩ := ruleEq_representation perfectForesight β κ φ (fun _ => c) u 0 ()
    cases ω'
    rw [hr]
    simp only [lagW_zero]
    change φ * (1 - μ) * c - φ * w0 = π 0 ()
    have hc' : φ * (1 - μ) * c = π 0 () + φ * w0 := by
      have h1m : (1 : ℝ) - μ ≠ 0 := (sub_pos.2 hμ1).ne'
      simp only [c]
      field_simp
    linear_combination hc'
  have hle1 := h.2 _ _ hpR h0 ()
  have hle2 := (criterion_timeless perfectForesight perfectForesight_pullOut (xstar := xstar)
    hβ0.le hβ1
    hlam.le hκ.ne' ⟨|c|, fun _ => le_rfl⟩ hpR hcR).2 π x h.1 h0.symm ()
  have heq := le_antisymm hle1 hle2
  have hU := fun s => criterion_timeless_unique perfectForesight perfectForesight_pullOut hβ0
    hβ1 hlam hκ.ne' ⟨|c|, fun _ => le_rfl⟩ hpR hcR h.1 h0.symm () heq s
  have hπ : ∀ s, π s () = inflR perfectForesight β κ φ (fun _ => c) u s () := fun s => by
    have := (hU s).1
    change (π s () - _) ^ 2 = 0 at this
    linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this]
  have hx : ∀ s, x s () = gapR perfectForesight β κ φ (fun _ => c) u s () := fun s => by
    have := (hU s).2
    change (x s () - _) ^ 2 = 0 at this
    linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this]
  cases ω
  rw [hπ, hx, hx]
  have := hcR (t + 1) ()
  simpa using this

/-! ### Inflation inertia: (2.6)–(2.9) -/

/-- Woodford (2003), (2.8), p. 562: quasi-differenced inflation `π^{qd}_t = π_t − γ π_{t−1}`
(with `π_{t₀−1} = π₀`). -/
def qd (γ : ℝ) (π₀ : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => π t ω - γ * lagW π₀ π t ω

/-- Woodford (2003), (2.6), p. 562 (corrected): the aggregate-supply relation with indexation,
`π_t − γ π_{t−1} = κ x_t + β E_t[π_{t+1} − γ π_t] + u_t`. -/
def ASind (β κ γ : ℝ) (π₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω - γ * lagW π₀ π t ω =
    κ * x t ω + β * 𝔼.E t (fun ω => π (t + 1) ω - γ * π t ω) ω + u t ω

/-- Woodford (2003), (2.6), p. 562, AS PRINTED: `π_t − γ π_{t−1} = κ x_t + β E_t[π_{t+1} − π_t]
+ u_t` (the `γ` inside the expectation is missing). -/
def ASindPrinted (β κ γ : ℝ) (π₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω - γ * lagW π₀ π t ω =
    κ * x t ω + β * 𝔼.E t (fun ω => π (t + 1) ω - π t ω) ω + u t ω

/-- **Woodford (2003), (2.6)–(2.8), p. 562 (the reduction)**: the indexation relation (2.6) for
`(π, x)` is exactly (2.1) for `(π^{qd}, x)`. -/
theorem asInd_iff_as_qd (β κ γ : ℝ) (π₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) :
    ASind 𝔼 β κ γ π₀ u π x ↔ AS 𝔼 β κ u (qd γ π₀ π) x :=
  Iff.rfl

/-- Woodford (2003), (2.7), p. 562: the period loss `(π_t − γ π_{t−1})² + λ (x_t − x*)²` is the
loss (2.3) in `π^{qd}`. -/
theorem periodLoss_qd (lam xstar γ : ℝ) (π₀ : Ω → ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    periodLoss lam xstar (qd γ π₀ π) x t ω =
      (π t ω - γ * lagW π₀ π t ω) ^ 2 + lam * (x t ω - xstar) ^ 2 :=
  rfl

/-- **Woodford (2003), (2.6), p. 562 (misprint)**: for `γ = 1` the printed relation is the correct
one. -/
theorem asIndPrinted_iff_of_gamma_one (β κ : ℝ) (π₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) :
    ASindPrinted 𝔼 β κ 1 π₀ u π x ↔ ASind 𝔼 β κ 1 π₀ u π x := by
  simp only [ASindPrinted, ASind, one_mul]

/-- **Woodford (2003), (2.6), p. 562 (misprint, counterexample)**: for `β ≠ 0` and `γ ≠ 1` the
printed relation is not the indexation relation: the constant path `π_t = π_{−1} = 1`, `x_t = 0`
with `u_t = (1 − γ)(1 − β)` satisfies the correct (2.6) but violates the printed one. -/
theorem printed_asInd_counterexample {β κ γ : ℝ} (hβ : β ≠ 0) (hγ : γ ≠ 1) :
    ASind perfectForesight β κ γ (fun _ => 1) (fun _ _ => (1 - γ) * (1 - β)) (fun _ _ => 1)
        (fun _ _ => 0) ∧
      ¬ ASindPrinted perfectForesight β κ γ (fun _ => 1) (fun _ _ => (1 - γ) * (1 - β))
        (fun _ _ => 1) (fun _ _ => 0) := by
  refine ⟨fun t ω => ?_, fun h => ?_⟩
  · cases t <;>
    · change 1 - γ * 1 = κ * 0 + β * (1 - γ * 1) + (1 - γ) * (1 - β)
      ring
  · have h0 := h 0 ()
    change 1 - γ * 1 = κ * 0 + β * (1 - 1) + (1 - γ) * (1 - β) at h0
    have : β * (1 - γ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hβ h1
    · exact hγ (by linarith)

/-- Woodford (2003), (2.6)–(2.7): an admissible plan with indexation (bounded adapted `π, x`
satisfying the corrected (2.6), given `π_{t₀−1} = π₀`). -/
def PlanInd (β κ γ : ℝ) (π₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ASind 𝔼 β κ γ π₀ u π x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x

/-- Woodford (2003), Ch. 8 §1.1 Definition and §2.1 (timeless optimality with indexation): the
plan is admissible and minimises the expected loss (2.2)+(2.7) among admissible plans with the
same initial inflation `π_{t₀}` (the initial constraint (1.6)). -/
def TimelessOptimalInd (β κ γ lam xstar : ℝ) (π₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  PlanInd 𝔼 β κ γ π₀ u π x ∧ ∀ π' x', PlanInd 𝔼 β κ γ π₀ u π' x' → π' 0 = π 0 →
    ∀ ω, expLossOf 𝔼 β (periodLoss lam xstar (qd γ π₀ π) x) ω ≤
      expLossOf 𝔼 β (periodLoss lam xstar (qd γ π₀ π') x') ω

/-- Woodford (2003), (2.9), p. 563: the target criterion
`π_t − γ π_{t−1} + φ (x_t − x_{t−1}) = 0` for all `t ≥ t₀`. -/
def Criterion29 (γ φ : ℝ) (π₀ x₀ : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω - γ * lagW π₀ π t ω + φ * (x t ω - lagW x₀ x t ω) = 0

/-- Woodford (2003), (2.9), p. 563: (2.9) is (2.5) with `π_t` replaced by `π^{qd}_t`. -/
theorem criterion29_iff (γ φ : ℝ) (π₀ x₀ : Ω → ℝ) (π x : ℕ → Ω → ℝ) :
    Criterion29 γ φ π₀ x₀ π x ↔ Criterion φ x₀ (qd γ π₀ π) x :=
  Iff.rfl

/-- Woodford (2003), (2.8): `π^{qd}` of an adapted process with a date-0 initial value is
adapted. -/
theorem qd_adapted {γ : ℝ} {π₀ : Ω → ℝ} {π : ℕ → Ω → ℝ} (h0 : 𝔼.E 0 π₀ = π₀)
    (hπ : 𝔼.Adapted π) : 𝔼.Adapted (qd γ π₀ π) := by
  intro t
  have : qd γ π₀ π t = π t - γ • lagW π₀ π t := rfl
  rw [this, map_sub, map_smul, hπ t, lagW_adapted 𝔼 h0 hπ t]

/-- Woodford (2003), (2.8): `π^{qd}` of a bounded process with a bounded initial value is
bounded. -/
theorem qd_bounded {γ B : ℝ} {π₀ : Ω → ℝ} {π : ℕ → Ω → ℝ} (h0 : ∀ ω, |π₀ ω| ≤ B)
    (hπ : BoundedProc π) : BoundedProc (qd γ π₀ π) := by
  obtain ⟨M, hM⟩ := hπ
  refine ⟨M + |γ| * max B M, fun t ω => ?_⟩
  refine (abs_sub _ _).trans (add_le_add (hM t ω) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (lagW_bounded h0 hM t ω) (abs_nonneg γ)

/-- Woodford (2003), (2.6)–(2.8): an admissible plan with indexation gives an admissible plan of
the baseline problem in `(π^{qd}, x)`. -/
theorem planInd_qd {β κ γ B : ℝ} {π₀ : Ω → ℝ} (h0 : 𝔼.E 0 π₀ = π₀) (hB : ∀ ω, |π₀ ω| ≤ B)
    {u π x : ℕ → Ω → ℝ} (hp : PlanInd 𝔼 β κ γ π₀ u π x) : Plan 𝔼 β κ u (qd γ π₀ π) x :=
  ⟨hp.1, qd_adapted 𝔼 h0 hp.2.1, hp.2.2.1, qd_bounded hB hp.2.2.2.1, hp.2.2.2.2⟩

/-- **Woodford (2003), (2.9), p. 563 (optimality)**: every admissible plan with indexation
satisfying (2.9) with `φ = λ/κ` is optimal from a timeless perspective. -/
theorem criterion29_timeless (hpo : 𝔼.PullOut) {β κ γ lam xstar B : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hlam : 0 ≤ lam) (hκ : κ ≠ 0) {u π x : ℕ → Ω → ℝ} {π₀ x₀ : Ω → ℝ}
    (hπ₀a : 𝔼.E 0 π₀ = π₀) (hπ₀ : ∀ ω, |π₀ ω| ≤ B) (hx₀ : ∃ B, ∀ ω, |x₀ ω| ≤ B)
    (hp : PlanInd 𝔼 β κ γ π₀ u π x) (hc : Criterion29 γ (lam / κ) π₀ x₀ π x) :
    TimelessOptimalInd 𝔼 β κ γ lam xstar π₀ u π x := by
  refine ⟨hp, fun π' x' hp' h0 ω => ?_⟩
  have hT := criterion_timeless 𝔼 hpo (xstar := xstar) hβ0 hβ1 hlam hκ hx₀
    (planInd_qd 𝔼 hπ₀a hπ₀ hp) hc
  refine hT.2 _ _ (planInd_qd 𝔼 hπ₀a hπ₀ hp') ?_ ω
  funext ω'
  simp only [qd, lagW_zero, h0]

/-- Woodford (2003), (2.9) with `γ = 1`: `π_t = γ π_{t−1} + π^{qd}_t` recovers inflation; with
`γ = 1` and `π^{qd}_t = −φ(x_t − x_{t−1})`, `π_t + φ x_t = π_{t₀−1} + φ x_{t₀−1}`. -/
theorem backRec_one_sum {φ : ℝ} {π₀ x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} (t : ℕ) (ω : Ω) :
    backRec 1 π₀ (fun s ω => -φ * (x s ω - lagW x₀ x s ω)) t ω + φ * x t ω =
      π₀ ω + φ * x₀ ω := by
  induction t with
  | zero =>
    change 1 * π₀ ω + -φ * (x 0 ω - x₀ ω) + φ * x 0 ω = _
    ring
  | succ t ih =>
    change 1 * backRec 1 π₀ (fun s ω => -φ * (x s ω - lagW x₀ x s ω)) t ω +
      -φ * (x (t + 1) ω - x t ω) + φ * x (t + 1) ω = _
    linarith

/-- Woodford (2003), (2.9), p. 563: equilibrium inflation under (2.9),
`π_t = γ π_{t−1} − φ (x_t − x_{t−1})`. -/
noncomputable def inflInd (β κ γ φ : ℝ) (π₀ x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  backRec γ π₀ (inflR 𝔼 β κ φ x₀ u)

/-- Woodford (2003), (2.9): `π^{qd}` of `inflInd` is the baseline equilibrium inflation. -/
theorem qd_inflInd (β κ γ φ : ℝ) (π₀ x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) :
    qd γ π₀ (inflInd 𝔼 β κ γ φ π₀ x₀ u) = inflR 𝔼 β κ φ x₀ u := by
  funext t ω
  have := congrFun (backRec_eq γ π₀ (inflR 𝔼 β κ φ x₀ u) t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [qd, inflInd]
  linarith

/-- **Woodford (2003), (2.9), p. 563 (determinacy)**: for `0 ≤ γ ≤ 1`, `κ, φ > 0`, every bounded
adapted `u` and bounded date-0 `π_{t₀−1}, x_{t₀−1}`, the corrected (2.6) and (2.9) have exactly
one bounded adapted solution, `(inflInd, gapR)`. -/
theorem ruleInd_existsUnique {β κ γ φ M B B' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 < φ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) {π₀ x₀ : Ω → ℝ} (hπ₀ : ∀ ω, |π₀ ω| ≤ B') (hπ₀a : 𝔼.E 0 π₀ = π₀)
    (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hx₀a : 𝔼.E 0 x₀ = x₀) :
    (PlanInd 𝔼 β κ γ π₀ u (inflInd 𝔼 β κ γ φ π₀ x₀ u) (gapR 𝔼 β κ φ x₀ u) ∧
      Criterion29 γ φ π₀ x₀ (inflInd 𝔼 β κ γ φ π₀ x₀ u) (gapR 𝔼 β κ φ x₀ u)) ∧
    ∀ π x, PlanInd 𝔼 β κ γ π₀ u π x → Criterion29 γ φ π₀ x₀ π x →
      π = inflInd 𝔼 β κ γ φ π₀ x₀ u ∧ x = gapR 𝔼 β κ φ x₀ u := by
  obtain ⟨⟨hp, hc⟩, huniq⟩ := ruleEq_existsUnique 𝔼 hβ0 hβ1 hκ hφ hu hua hx₀ hx₀a
  have hq := qd_inflInd 𝔼 β κ γ φ π₀ x₀ u
  obtain ⟨-, hia, hxa, ⟨P, hP⟩, ⟨X, hX⟩⟩ := hp
  have hbd : BoundedProc (inflInd 𝔼 β κ γ φ π₀ x₀ u) := by
    rcases lt_or_eq_of_le hγ1 with h | h
    · exact ⟨_, backRec_bounded hγ0 h hπ₀ hP⟩
    · subst h
      refine ⟨B' + φ * B + φ * X, fun t ω => ?_⟩
      have := backRec_one_sum (φ := φ) (π₀ := π₀) (x₀ := x₀) (x := gapR 𝔼 β κ φ x₀ u) t ω
      have he : inflInd 𝔼 β κ 1 φ π₀ x₀ u t ω =
          π₀ ω + φ * x₀ ω - φ * gapR 𝔼 β κ φ x₀ u t ω := by
        simp only [inflInd]
        change backRec 1 π₀ (fun s ω => -φ * (gapR 𝔼 β κ φ x₀ u s ω -
          lagW x₀ (gapR 𝔼 β κ φ x₀ u) s ω)) t ω = _
        linarith
      rw [he]
      have h1 := hπ₀ ω
      have h2 : |φ * x₀ ω| ≤ φ * B := by
        rw [abs_mul, abs_of_pos hφ]; exact mul_le_mul_of_nonneg_left (hx₀ ω) hφ.le
      have h3 : |φ * gapR 𝔼 β κ φ x₀ u t ω| ≤ φ * X := by
        rw [abs_mul, abs_of_pos hφ]; exact mul_le_mul_of_nonneg_left (hX t ω) hφ.le
      calc |π₀ ω + φ * x₀ ω - φ * gapR 𝔼 β κ φ x₀ u t ω|
          ≤ |π₀ ω + φ * x₀ ω| + |φ * gapR 𝔼 β κ φ x₀ u t ω| := abs_sub _ _
        _ ≤ |π₀ ω| + |φ * x₀ ω| + |φ * gapR 𝔼 β κ φ x₀ u t ω| := by
          gcongr; exact abs_add_le _ _
        _ ≤ B' + φ * B + φ * X := by linarith
  refine ⟨⟨⟨?_, backRec_adapted 𝔼 hπ₀a hia, hxa, hbd, ⟨X, hX⟩⟩, ?_⟩, fun π x hpi hci => ?_⟩
  · rw [asInd_iff_as_qd, hq]
    exact (ruleEq_existsUnique 𝔼 hβ0 hβ1 hκ hφ hu hua hx₀ hx₀a).1.1.1
  · rw [criterion29_iff, hq]
    exact hc
  · obtain ⟨h1, h2⟩ := huniq _ _ (planInd_qd 𝔼 hπ₀a hπ₀ hpi) hci
    refine ⟨?_, h2⟩
    apply eq_backRec
    intro t
    funext ω
    have := congrFun (congrFun h1 t) ω
    simp only [qd] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith

/-- **Woodford (2003), Ch. 8 §1.3 Definition, for (2.6)–(2.7)**: a rule (a relation between
`π_{t₀−1}, x_{t₀−1}`, `π`, `x`) is robustly optimal if for every bounded adapted `u` and bounded
date-0 initial conditions it determines a unique bounded adapted equilibrium and every such
equilibrium is optimal from a timeless perspective. -/
def RobustlyOptimalInd (β κ γ lam xstar : ℝ)
    (Rule : (Ω → ℝ) → (Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop) : Prop :=
  ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∀ π₀ x₀ : Ω → ℝ, (∃ B, ∀ ω, |π₀ ω| ≤ B) →
    𝔼.E 0 π₀ = π₀ → (∃ B, ∀ ω, |x₀ ω| ≤ B) → 𝔼.E 0 x₀ = x₀ →
    (∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), PlanInd 𝔼 β κ γ π₀ u p.1 p.2 ∧ Rule π₀ x₀ p.1 p.2) ∧
    ∀ π x, PlanInd 𝔼 β κ γ π₀ u π x → Rule π₀ x₀ π x →
      TimelessOptimalInd 𝔼 β κ γ lam xstar π₀ u π x

/-- **Woodford (2003), (2.9), p. 563 (THE ROBUSTLY OPTIMAL CRITERION WITH INFLATION INERTIA)**:
for `0 ≤ γ ≤ 1`, `0 < β < 1`, `κ, λ > 0`, the criterion
`π_t − γ π_{t−1} + (λ/κ)(x_t − x_{t−1}) = 0` is robustly optimal for (2.6)–(2.7). -/
theorem indexation_robustlyOptimal (hpo : 𝔼.PullOut) {β κ γ lam xstar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    RobustlyOptimalInd 𝔼 β κ γ lam xstar
      (fun π₀ x₀ π x => Criterion29 γ (lam / κ) π₀ x₀ π x) := by
  intro u ⟨M, hM⟩ hua π₀ x₀ ⟨B', hB'⟩ hπ₀a ⟨B, hB⟩ hx₀a
  obtain ⟨hex, huniq⟩ := ruleInd_existsUnique 𝔼 hβ0 hβ1 hκ (div_pos hlam hκ) hγ0 hγ1 hM hua
    hB' hπ₀a hB hx₀a
  refine ⟨⟨(inflInd 𝔼 β κ γ (lam / κ) π₀ x₀ u, gapR 𝔼 β κ (lam / κ) x₀ u), hex, ?_⟩, ?_⟩
  · rintro ⟨π, x⟩ ⟨hp, hc⟩
    obtain ⟨h1, h2⟩ := huniq π x hp hc
    simp [h1, h2]
  · intro π x hp hc
    exact criterion29_timeless 𝔼 hpo hβ0.le hβ1 hlam.le hκ.ne' hπ₀a hB' ⟨B, hB⟩ hp hc

/-! ### Full indexation `γ = 1`: the criterion (2.10) -/

/-- Woodford (2003), (2.10), p. 563: the criterion `π_t + φ x_t = π̄` for all `t ≥ t₀`, with a
long-run target `π̄` fixed at date `t₀` (a date-0 random variable; a constant in the book). -/
def Criterion210 (φ : ℝ) (pbar : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω + φ * x t ω = pbar ω

/-- **Woodford (2003), p. 563**: with `γ = 1`, a commitment to (2.9) from `t₀` on is equivalent
to a commitment to (2.10) with `π̄ = π_{t₀−1} + φ x_{t₀−1}`. -/
theorem criterion29_iff_criterion210 (φ : ℝ) (π₀ x₀ : Ω → ℝ) (π x : ℕ → Ω → ℝ) :
    Criterion29 1 φ π₀ x₀ π x ↔ Criterion210 φ (fun ω => π₀ ω + φ * x₀ ω) π x := by
  constructor
  · intro h t ω
    induction t with
    | zero => have := h 0 ω; simp only [lagW_zero] at this; linarith
    | succ t ih => have := h (t + 1) ω; simp only [lagW_succ] at this; linarith
  · intro h t ω
    cases t with
    | zero => have := h 0 ω; simp only [lagW_zero]; linarith
    | succ t =>
      have h1 := h t ω
      have h2 := h (t + 1) ω
      simp only [lagW_succ]
      linarith

/-- **Woodford (2003), p. 563 (survey E15, the correct statement)**: the first difference of
(2.10) is (2.9) with `γ = 1`: if (2.10) holds at all dates then
`π_{t+1} − π_t + φ (x_{t+1} − x_t) = 0`. -/
theorem diff_criterion210 {φ : ℝ} {pbar : Ω → ℝ} {π x : ℕ → Ω → ℝ}
    (h : Criterion210 φ pbar π x) (t : ℕ) (ω : Ω) :
    π (t + 1) ω - 1 * π t ω + φ * (x (t + 1) ω - x t ω) = 0 := by
  have h1 := h t ω
  have h2 := h (t + 1) ω
  linarith

/-- **Woodford (2003), p. 563 (survey E15, the printed cross-reference is wrong)**: the text says
"(2.5) is just a first-differenced form of (2.10)"; but (2.10) does not imply (2.5)
`π_t + φ (x_t − x_{t−1}) = 0` at any date: the path `π_t = 1`, `x_t = 0` satisfies (2.10) with
`π̄ = 1` and violates (2.5) at every `t > t₀`. -/
theorem criterion210_not_imp_criterion25 (φ : ℝ) :
    Criterion210 φ (fun _ => 1) (fun _ (_ : Unit) => (1 : ℝ)) (fun _ _ => 0) ∧
      ∀ t, (fun _ (_ : Unit) => (1 : ℝ)) (t + 1) () +
        φ * ((fun _ (_ : Unit) => (0 : ℝ)) (t + 1) () - (fun _ _ => (0 : ℝ)) t ()) ≠ 0 := by
  refine ⟨fun t ω => by simp, fun t => by simp⟩

/-- Woodford (2003), (2.10): the date-`t₀` impulse `ε 1[t = 0]` (the discrepancy between `π̄` and
the self-consistent value `π_{t₀−1} + φ x_{t₀−1}`). -/
def impulse (e₀ : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => e₀
  | _ + 1 => 0

/-- Woodford (2003), (2.10): the impulse of a date-0 random variable is adapted. -/
theorem impulse_adapted {e₀ : Ω → ℝ} (h : 𝔼.E 0 e₀ = e₀) : 𝔼.Adapted (impulse e₀) := by
  intro t
  cases t with
  | zero => exact h
  | succ t => exact map_zero _

/-- Woodford (2003), (2.10): under (2.10) with `γ = 1`,
`π^{qd}_t = −φ (x_t − x_{t−1}) + (π̄ − π_{t₀−1} − φ x_{t₀−1}) 1[t = t₀]`. -/
theorem qd_of_criterion210 {φ : ℝ} {pbar π₀ x₀ : Ω → ℝ} {π x : ℕ → Ω → ℝ}
    (h : Criterion210 φ pbar π x) (t : ℕ) (ω : Ω) :
    qd 1 π₀ π t ω = -φ * (x t ω - lagW x₀ x t ω) +
      impulse (fun ω => pbar ω - π₀ ω - φ * x₀ ω) t ω := by
  cases t with
  | zero =>
    have := h 0 ω
    simp only [qd, lagW_zero, impulse]
    linarith
  | succ t =>
    have h1 := h t ω
    have h2 := h (t + 1) ω
    simp only [qd, lagW_succ, impulse, Pi.zero_apply]
    linarith

/-- Woodford (2003), (2.10): the equilibrium output gap under (2.10), the baseline equilibrium
for the disturbance `u_t − (π̄ − π_{t₀−1} − φ x_{t₀−1}) 1[t = t₀]`. -/
noncomputable def gap210 (β κ φ : ℝ) (pbar π₀ x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  gapR 𝔼 β κ φ x₀ (fun t => u t - impulse (fun ω => pbar ω - π₀ ω - φ * x₀ ω) t)

/-- Woodford (2003), (2.10): the equilibrium inflation under (2.10), `π_t = π̄ − φ x_t`. -/
noncomputable def infl210 (β κ φ : ℝ) (pbar π₀ x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => pbar ω - φ * gap210 𝔼 β κ φ pbar π₀ x₀ u t ω

/-- Woodford (2003), (2.10) with `γ = 1`: a plan satisfying (2.10) solves the indexation relation
iff `(π^{qd} − impulse, x)` solves (2.1) for the disturbance `u − impulse` and the criterion
(2.5) holds for it. -/
theorem asInd_iff_of_criterion210 {β κ φ : ℝ} {pbar π₀ x₀ : Ω → ℝ} {u π x : ℕ → Ω → ℝ}
    (h : Criterion210 φ pbar π x) :
    (ASind 𝔼 β κ 1 π₀ u π x ↔
      AS 𝔼 β κ (fun t => u t - impulse (fun ω => pbar ω - π₀ ω - φ * x₀ ω) t)
        (fun t ω => -φ * (x t ω - lagW x₀ x t ω)) x) ∧
      Criterion φ x₀ (fun t ω => -φ * (x t ω - lagW x₀ x t ω)) x := by
  have hE : ∀ t, (fun ω => π (t + 1) ω - 1 * π t ω) =
      (fun t ω => -φ * (x t ω - lagW x₀ x t ω)) (t + 1) := fun t => by
    funext ω
    have := diff_criterion210 h t ω
    simp only [lagW_succ]
    linarith
  refine ⟨⟨fun hA t ω => ?_, fun hA t ω => ?_⟩, fun t ω => by ring⟩
  · have h1 := hA t ω
    have h2 := qd_of_criterion210 (π₀ := π₀) (x₀ := x₀) h t ω
    rw [hE t] at h1
    simp only [qd] at h2
    simp only [Pi.sub_apply]
    linarith
  · have h1 := hA t ω
    have h2 := qd_of_criterion210 (π₀ := π₀) (x₀ := x₀) h t ω
    simp only [qd] at h2
    simp only [Pi.sub_apply] at h1
    rw [hE t]
    linarith

/-- Woodford (2003), (2.5): `a (x_t − x_{t−1})` is adapted for adapted `x` and a date-0
`x_{t₀−1}`. -/
theorem diff_adapted {a : ℝ} {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} (h0 : 𝔼.E 0 x₀ = x₀)
    (hx : 𝔼.Adapted x) : 𝔼.Adapted (fun t ω => a * (x t ω - lagW x₀ x t ω)) := by
  intro t
  have : (fun ω => a * (x t ω - lagW x₀ x t ω)) = a • (x t - lagW x₀ x t) := rfl
  change 𝔼.E t (fun ω => a * (x t ω - lagW x₀ x t ω)) = _
  rw [this, map_smul, map_sub, hx t, lagW_adapted 𝔼 h0 hx t]
  rfl

/-- Woodford (2003), (2.5): `a (x_t − x_{t−1})` is bounded for bounded `x` and `x_{t₀−1}`. -/
theorem diff_bounded {a B M : ℝ} {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} (h0 : ∀ ω, |x₀ ω| ≤ B)
    (hx : ∀ t ω, |x t ω| ≤ M) : BoundedProc (fun t ω => a * (x t ω - lagW x₀ x t ω)) := by
  refine ⟨|a| * (M + max B M), fun t ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
    (add_le_add (hx t ω) (lagW_bounded h0 hx t ω))) (abs_nonneg a)

/-- **Woodford (2003), (2.10), p. 563 (determinacy for every `π̄`)**: with `γ = 1`, for every
bounded date-0 `π̄`, the corrected (2.6) and (2.10) have exactly one bounded adapted solution,
`(infl210, gap210)` — the choice of `π̄` does not affect determinacy. -/
theorem rule210_existsUnique {β κ φ M B B' P : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    {pbar π₀ x₀ : Ω → ℝ} (hπ₀ : ∀ ω, |π₀ ω| ≤ B') (hπ₀a : 𝔼.E 0 π₀ = π₀)
    (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hx₀a : 𝔼.E 0 x₀ = x₀) (hp : ∀ ω, |pbar ω| ≤ P)
    (hpa : 𝔼.E 0 pbar = pbar) :
    (PlanInd 𝔼 β κ 1 π₀ u (infl210 𝔼 β κ φ pbar π₀ x₀ u) (gap210 𝔼 β κ φ pbar π₀ x₀ u) ∧
      Criterion210 φ pbar (infl210 𝔼 β κ φ pbar π₀ x₀ u) (gap210 𝔼 β κ φ pbar π₀ x₀ u)) ∧
    ∀ π x, PlanInd 𝔼 β κ 1 π₀ u π x → Criterion210 φ pbar π x →
      π = infl210 𝔼 β κ φ pbar π₀ x₀ u ∧ x = gap210 𝔼 β κ φ pbar π₀ x₀ u := by
  set e₀ : Ω → ℝ := fun ω => pbar ω - π₀ ω - φ * x₀ ω with he₀
  have he₀a : 𝔼.E 0 e₀ = e₀ := by
    have : e₀ = pbar - π₀ - φ • x₀ := rfl
    rw [this, map_sub, map_sub, map_smul, hpa, hπ₀a, hx₀a]
  have hia := impulse_adapted 𝔼 he₀a
  have hub : ∀ t ω, |(fun t => u t - impulse e₀ t) t ω| ≤ M + (P + B' + φ * B) := by
    intro t ω
    refine (abs_sub _ _).trans (add_le_add (hu t ω) ?_)
    cases t with
    | zero =>
      simp only [impulse, he₀]
      have h2 : |φ * x₀ ω| ≤ φ * B := by
        rw [abs_mul, abs_of_pos hφ]; exact mul_le_mul_of_nonneg_left (hx₀ ω) hφ.le
      calc |pbar ω - π₀ ω - φ * x₀ ω| ≤ |pbar ω - π₀ ω| + |φ * x₀ ω| := abs_sub _ _
        _ ≤ |pbar ω| + |π₀ ω| + |φ * x₀ ω| := by gcongr; exact abs_sub _ _
        _ ≤ P + B' + φ * B := by linarith [hp ω, hπ₀ ω]
    | succ t =>
      simp only [impulse, Pi.zero_apply, abs_zero]
      have := (abs_nonneg _).trans (hp ω)
      have := (abs_nonneg _).trans (hπ₀ ω)
      have := (abs_nonneg _).trans (hx₀ ω)
      positivity
  have hua' : 𝔼.Adapted (fun t => u t - impulse e₀ t) := fun t => by
    simp only [map_sub, hua t, hia t]
  obtain ⟨⟨hpR, hcR⟩, huniq⟩ := ruleEq_existsUnique 𝔼 hβ0 hβ1 hκ hφ hub hua' hx₀ hx₀a
  obtain ⟨hAS, -, hxa, -, ⟨X, hX⟩⟩ := hpR
  have hc210 : Criterion210 φ pbar (infl210 𝔼 β κ φ pbar π₀ x₀ u)
      (gap210 𝔼 β κ φ pbar π₀ x₀ u) := fun t ω => by simp only [infl210]; ring
  have hxa' : 𝔼.Adapted (gap210 𝔼 β κ φ pbar π₀ x₀ u) := hxa
  refine ⟨⟨⟨?_, fun t => ?_, hxa, ⟨P + φ * X, fun t ω => ?_⟩, ⟨X, hX⟩⟩, hc210⟩,
    fun π x hpl hcl => ?_⟩
  · rw [(asInd_iff_of_criterion210 𝔼 (π₀ := π₀) (x₀ := x₀) (u := u) hc210).1]
    exact hAS
  · have : infl210 𝔼 β κ φ pbar π₀ x₀ u t = pbar - φ • gap210 𝔼 β κ φ pbar π₀ x₀ u t := rfl
    rw [this, map_sub, map_smul, E_of_known 𝔼 (Nat.zero_le t) hpa, hxa' t]
  · simp only [infl210]
    refine (abs_sub _ _).trans (add_le_add (hp ω) ?_)
    rw [abs_mul, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_left (hX t ω) hφ.le
  · obtain ⟨hA, hC⟩ := asInd_iff_of_criterion210 𝔼 (π₀ := π₀) (x₀ := x₀) (u := u) hcl
    obtain ⟨⟨B₁, hB₁⟩, hxa₁⟩ := (⟨hpl.2.2.2.2, hpl.2.2.1⟩ : BoundedProc x ∧ 𝔼.Adapted x)
    have hpl' : Plan 𝔼 β κ (fun t => u t - impulse e₀ t)
        (fun t ω => -φ * (x t ω - lagW x₀ x t ω)) x :=
      ⟨hA.1 hpl.1, diff_adapted 𝔼 hx₀a hxa₁, hxa₁, diff_bounded hx₀ hB₁, ⟨B₁, hB₁⟩⟩
    obtain ⟨-, hx⟩ := huniq _ _ hpl' hC
    refine ⟨?_, hx⟩
    funext t ω
    have := hcl t ω
    have hx' : x t ω = gap210 𝔼 β κ φ pbar π₀ x₀ u t ω := congrFun (congrFun hx t) ω
    simp only [infl210]
    rw [← hx']
    linarith

/-- **Woodford (2003), p. 564 ("any rule of the form (2.10) is also optimal from a timeless
perspective")**: with `γ = 1`, every admissible plan satisfying (2.10) with `φ = λ/κ` — for ANY
long-run target `π̄` — is optimal from a timeless perspective: it satisfies the first-order
conditions with the multiplier `φ_t = (λ/κ)(x_t − x*)` and the initial multiplier
`φ_{t₀−1} = φ_{t₀} + π^{qd}_{t₀}`. -/
theorem rule210_timeless (hpo : 𝔼.PullOut) {β κ lam xstar B : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hlam : 0 ≤ lam) (hκ : κ ≠ 0) {u π x : ℕ → Ω → ℝ} {pbar π₀ : Ω → ℝ}
    (hπ₀a : 𝔼.E 0 π₀ = π₀) (hπ₀ : ∀ ω, |π₀ ω| ≤ B) (hp : PlanInd 𝔼 β κ 1 π₀ u π x)
    (hc : Criterion210 (lam / κ) pbar π x) :
    TimelessOptimalInd 𝔼 β κ 1 lam xstar π₀ u π x := by
  refine ⟨hp, fun π' x' hp' h0 ω => ?_⟩
  have hP := planInd_qd 𝔼 hπ₀a hπ₀ hp
  have hP' := planInd_qd 𝔼 hπ₀a hπ₀ hp'
  set m : ℕ → Ω → ℝ := fun s ω => lam / κ * (x s ω - xstar) with hm
  have hma : 𝔼.Adapted m := affine_adapted 𝔼 _ _ hp.2.2.1
  have hmb : BoundedProc m := affine_bounded _ _ hp.2.2.2.2
  obtain ⟨Z, hZ⟩ := hmb
  obtain ⟨Q, hQ⟩ := hP.2.2.2.1
  have hfoc : FOC κ lam xstar (fun ω => m 0 ω + qd 1 π₀ π 0 ω) (qd 1 π₀ π) x m := by
    intro t ω
    have h2 : κ * (lam / κ * (x t ω - xstar)) = lam * (x t ω - xstar) := by field_simp
    refine ⟨?_, by simp only [hm]; linarith⟩
    cases t with
    | zero => simp only [lagW_zero]; ring
    | succ t =>
      have := diff_criterion210 hc t ω
      simp only [lagW_succ, qd, hm]
      linarith
  refine foc_sufficient 𝔼 hpo hβ0 hβ1 hlam hP' hP hma ⟨Z, hZ⟩
    ⟨Z + Q, fun ω => (abs_add_le _ _).trans (add_le_add (hZ 0 ω) (hQ 0 ω))⟩ hfoc
    (fun ω => ?_) ω
  have : qd 1 π₀ π' 0 ω = qd 1 π₀ π 0 ω := by simp only [qd, lagW_zero, h0]
  rw [this, sub_self, mul_zero]

/-- Woodford (2003), (2.10): the forcing `u_t − e₀ 1[t = t₀]` is bounded. -/
theorem forcing210_bounded {M E : ℝ} {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    {e₀ : Ω → ℝ} (he : ∀ ω, |e₀ ω| ≤ E) :
    ∀ t ω, |(fun t => u t - impulse e₀ t) t ω| ≤ M + E := by
  intro t ω
  refine (abs_sub _ _).trans (add_le_add (hu t ω) ?_)
  cases t with
  | zero => exact he ω
  | succ t =>
    simp only [impulse, Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans (he ω)

/-- **Woodford (2003), p. 564 (the choice of `π̄` affects only a deterministic component)**:
with `γ = 1`, the equilibria under (2.10) with targets `π̄` and `π̄'` (same disturbances and
initial conditions) differ by `x_t − x'_t = (π̄ − π̄') μ₁^{t+1}/φ` and
`π_t − π'_t = (π̄ − π̄')(1 − μ₁^{t+1})`: the difference involves no disturbance at all (it is
deterministic given the date-`t₀` choice of target), it is transitory in the output gap and in
inflation acceleration, and it shifts long-run inflation by exactly `π̄ − π̄'` — the responses to
disturbances are identical. -/
theorem rule210_diff {β κ φ M B B' P P' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    {pbar pbar' π₀ x₀ : Ω → ℝ} (hπ₀ : ∀ ω, |π₀ ω| ≤ B') (hπ₀a : 𝔼.E 0 π₀ = π₀)
    (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hx₀a : 𝔼.E 0 x₀ = x₀) (hp : ∀ ω, |pbar ω| ≤ P)
    (hpa : 𝔼.E 0 pbar = pbar) (hp' : ∀ ω, |pbar' ω| ≤ P') (hpa' : 𝔼.E 0 pbar' = pbar') :
    ∀ t ω, gap210 𝔼 β κ φ pbar π₀ x₀ u t ω - gap210 𝔼 β κ φ pbar' π₀ x₀ u t ω =
        (pbar ω - pbar' ω) * (lam1 β (κ / φ) ^ (t + 1) / φ) ∧
      infl210 𝔼 β κ φ pbar π₀ x₀ u t ω - infl210 𝔼 β κ φ pbar' π₀ x₀ u t ω =
        (pbar ω - pbar' ω) * (1 - lam1 β (κ / φ) ^ (t + 1)) := by
  have hc : 0 < κ / φ := div_pos hκ hφ
  set μ := lam1 β (κ / φ) with hμdef
  have hμ0 := lam1_pos hβ0 hc
  have hμ1 := lam1_lt_one hβ0 hc
  have hroot := lam1_root hβ0 hc
  rw [← hμdef] at hroot hμ0 hμ1
  -- the two forcing processes
  have hE : ∀ (q : Ω → ℝ) (Q : ℝ), (∀ ω, |q ω| ≤ Q) → 𝔼.E 0 q = q →
      (∀ t ω, |(fun t => φ⁻¹ • (fun t => u t -
        impulse (fun ω => q ω - π₀ ω - φ * x₀ ω) t) t) t ω| ≤ φ⁻¹ * (M + (Q + B' + φ * B))) ∧
      𝔼.Adapted (fun t => φ⁻¹ • (fun t => u t -
        impulse (fun ω => q ω - π₀ ω - φ * x₀ ω) t) t) := by
    intro q Q hq hqa
    have he : ∀ ω, |(fun ω => q ω - π₀ ω - φ * x₀ ω) ω| ≤ Q + B' + φ * B := fun ω => by
      have h2 : |φ * x₀ ω| ≤ φ * B := by
        rw [abs_mul, abs_of_pos hφ]; exact mul_le_mul_of_nonneg_left (hx₀ ω) hφ.le
      calc |q ω - π₀ ω - φ * x₀ ω| ≤ |q ω - π₀ ω| + |φ * x₀ ω| := abs_sub _ _
        _ ≤ |q ω| + |π₀ ω| + |φ * x₀ ω| := by gcongr; exact abs_sub _ _
        _ ≤ Q + B' + φ * B := by linarith [hq ω, hπ₀ ω]
    have hea : 𝔼.E 0 (fun ω => q ω - π₀ ω - φ * x₀ ω) = fun ω => q ω - π₀ ω - φ * x₀ ω := by
      have : (fun ω => q ω - π₀ ω - φ * x₀ ω) = q - π₀ - φ • x₀ := rfl
      rw [this, map_sub, map_sub, map_smul, hqa, hπ₀a, hx₀a]
    refine ⟨fun t ω => ?_, fun t => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hφ]
      exact mul_le_mul_of_nonneg_left (forcing210_bounded hu he t ω) (inv_nonneg.2 hφ.le)
    · simp only [map_smul, map_sub, hua t, impulse_adapted 𝔼 hea t]
  obtain ⟨hf, hfa⟩ := hE pbar P hp hpa
  obtain ⟨hf', hfa'⟩ := hE pbar' P' hp' hpa'
  obtain ⟨-, huniq⟩ := secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hf hfa hx₀ hx₀a
  obtain ⟨⟨hso', hya', ⟨Y', hY'⟩⟩, -⟩ := secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hf' hfa' hx₀ hx₀a
  set x' := ysol 𝔼 β (κ / φ) x₀ (fun t => φ⁻¹ • (fun t => u t -
    impulse (fun ω => pbar' ω - π₀ ω - φ * x₀ ω) t) t) with hx'
  set d : ℕ → Ω → ℝ := fun t ω => (pbar ω - pbar' ω) * (μ ^ (t + 1) / φ) with hd
  have hd0 : ∀ s, 𝔼.E 0 (d s) = d s := fun s => by
    have : d s = (μ ^ (s + 1) / φ) • (pbar - pbar') := by
      funext w; simp only [hd, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [this, map_smul, map_sub, hpa, hpa']
  have hda : 𝔼.Adapted d := fun s => E_of_known 𝔼 (Nat.zero_le s) (hd0 s)
  have hdb : ∀ s w, |d s w| ≤ (P + P') * (1 / φ) := fun s w => by
    have h1 : |pbar w - pbar' w| ≤ P + P' := (abs_sub _ _).trans (add_le_add (hp w) (hp' w))
    have h2 : |μ ^ (s + 1) / φ| ≤ 1 / φ := by
      rw [abs_div, abs_of_pos hφ, abs_pow, abs_of_pos hμ0]
      gcongr
      exact pow_le_one₀ hμ0.le hμ1.le
    simp only [hd, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hsum : SecondOrder 𝔼 β (κ / φ) x₀ (fun t => φ⁻¹ • (fun t => u t -
      impulse (fun ω => pbar ω - π₀ ω - φ * x₀ ω) t) t) (fun t ω => x' t ω + d t ω) := by
    intro t ω
    have h1 := hso' t ω
    have hEd : 𝔼.E t (fun ω => x' (t + 1) ω + d (t + 1) ω) ω =
        𝔼.E t (x' (t + 1)) ω + d (t + 1) ω := by
      have : (fun ω => x' (t + 1) ω + d (t + 1) ω) = x' (t + 1) + d (t + 1) := rfl
      rw [this, map_add, E_of_known 𝔼 (Nat.zero_le t) (hd0 (t + 1))]
      rfl
    rw [hEd]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1 ⊢
    cases t with
    | zero =>
      simp only [lagW_zero, impulse, hd] at h1 ⊢
      linear_combination h1 + (pbar ω - pbar' ω) / φ * hroot
    | succ t =>
      simp only [lagW_succ, impulse, Pi.zero_apply, hd] at h1 ⊢
      linear_combination h1 + (pbar ω - pbar' ω) * μ ^ (t + 1) / φ * hroot
  have hsa : 𝔼.Adapted (fun t ω => x' t ω + d t ω) := fun t => by
    have : (fun ω => x' t ω + d t ω) = x' t + d t := rfl
    change 𝔼.E t (fun ω => x' t ω + d t ω) = _
    rw [this, map_add, hya' t, hda t]
    rfl
  have heq := huniq _ hsum hsa ⟨Y' + (P + P') * (1 / φ), fun t ω =>
    (abs_add_le _ _).trans (add_le_add (hY' t ω) (hdb t ω))⟩
  intro t ω
  have hx : gap210 𝔼 β κ φ pbar π₀ x₀ u t ω = x' t ω + d t ω :=
    (congrFun (congrFun heq t) ω).symm
  have hx'' : gap210 𝔼 β κ φ pbar' π₀ x₀ u t ω = x' t ω := rfl
  refine ⟨?_, ?_⟩
  · rw [hx, hx'']; simp only [hd]; ring
  · simp only [infl210]
    rw [hx, hx'']
    simp only [hd]
    field_simp
    ring

/-- **Woodford (2003), p. 564 (transitory, deterministic difference; long-run inflation)**: as
`t → ∞` the output-gap difference between the (2.10) equilibria with targets `π̄, π̄'` vanishes
and the inflation difference tends to `π̄ − π̄'`. -/
theorem rule210_diff_tendsto {β κ φ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hφ : 0 < φ) (D : ℝ) :
    Tendsto (fun t : ℕ => D * (lam1 β (κ / φ) ^ (t + 1) / φ)) atTop (𝓝 0) ∧
      Tendsto (fun t : ℕ => D * (1 - lam1 β (κ / φ) ^ (t + 1))) atTop (𝓝 D) := by
  have hc : 0 < κ / φ := div_pos hκ hφ
  have hp : Tendsto (fun t : ℕ => lam1 β (κ / φ) ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (lam1_pos hβ0 hc).le (lam1_lt_one hβ0 hc)).comp
      (tendsto_add_atTop_nat 1)
  constructor
  · simpa using (hp.div_const φ).const_mul D
  · simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul D

/-- **Woodford (2003), pp. 563–564 ("any target criterion of the form (2.10) implements the
optimal responses to disturbances")**: with full indexation `γ = 1`, for EVERY constant
long-run target `π̄`, the criterion `π_t + (λ/κ) x_t = π̄` is robustly optimal for (2.6)–(2.7). -/
theorem rule210_robustlyOptimal (hpo : 𝔼.PullOut) {β κ lam xstar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (pbar : ℝ) :
    RobustlyOptimalInd 𝔼 β κ 1 lam xstar
      (fun _ _ π x => Criterion210 (lam / κ) (fun _ => pbar) π x) := by
  intro u ⟨M, hM⟩ hua π₀ x₀ ⟨B', hB'⟩ hπ₀a ⟨B, hB⟩ hx₀a
  obtain ⟨hex, huniq⟩ := rule210_existsUnique 𝔼 hβ0 hβ1 hκ (div_pos hlam hκ) hM hua hB' hπ₀a
    hB hx₀a (P := |pbar|) (fun _ => le_rfl) (𝔼.const 0 pbar)
  refine ⟨⟨(infl210 𝔼 β κ (lam / κ) (fun _ => pbar) π₀ x₀ u,
    gap210 𝔼 β κ (lam / κ) (fun _ => pbar) π₀ x₀ u), hex, ?_⟩, ?_⟩
  · rintro ⟨π, x⟩ ⟨hp, hc⟩
    obtain ⟨h1, h2⟩ := huniq π x hp hc
    simp [h1, h2]
  · intro π x hp hc
    exact rule210_timeless 𝔼 hpo hβ0.le hβ1 hlam.le hκ.ne' hπ₀a hB' hp hc

/-! ### The hypotheses are satisfiable under genuine uncertainty -/

/-- Woodford (2003), (2.5), p. 561: the baseline criterion is robustly optimal on every finite
event tree (genuine uncertainty; the pull-out property holds there). -/
theorem baseline_robustlyOptimal_finiteTree {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {β κ lam xstar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    RobustlyOptimal T.toExpectationSystem β κ lam xstar
      (fun x₀ π x => Criterion (lam / κ) x₀ π x) :=
  baseline_robustlyOptimal _ (ExpectationsFiniteTree.finiteTree_pullOut T) hβ0 hβ1 hκ hlam

/-- Woodford (2003), (2.9), p. 563: the indexation criterion is robustly optimal on every finite
event tree. -/
theorem indexation_robustlyOptimal_finiteTree {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {β κ γ lam xstar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    RobustlyOptimalInd T.toExpectationSystem β κ γ lam xstar
      (fun π₀ x₀ π x => Criterion29 γ (lam / κ) π₀ x₀ π x) :=
  indexation_robustlyOptimal _ (ExpectationsFiniteTree.finiteTree_pullOut T) hβ0 hβ1 hκ hlam
    hγ0 hγ1

/-- Woodford (2003), pp. 566 and 569: the derivative of a quadratic `a v² + b v + c` (used to
check that the first-order conditions of §§2.2–2.3 are the derivatives of the Lagrangians). -/
theorem hasDerivAt_quad (a b c v : ℝ) :
    HasDerivAt (fun v => a * v ^ 2 + b * v + c) (2 * a * v + b) v := by
  have h1 := ((hasDerivAt_id' v).mul (hasDerivAt_id' v)).const_mul a
  have h2 := (hasDerivAt_id' v).const_mul b
  have h := (h1.add h2).add_const c
  convert h using 1
  · funext y; simp only [Pi.mul_apply, Pi.add_apply]; ring
  · ring

end Woodford.OptimalPolicyRules.InflTargetInertia
