/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.TidyR6CriticalCriterion
import PriceLevelDetermination.InertialBoundaryExistCube

/-!
# The boundary of Proposition 2.8 for every rule with the boundary slopes

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 632–634. The exact
inertial model is the Fisher equation `E_t[î_t − π_{t+1}] = 0` and a nonlinear rule
`E_t[î_t − Ψ(π_t, î_{t−1})] = 0` (`LocalIFTSystemsApps.Finert`, no fundamental shocks,
`î_{−1} = 0`). `InertialBoundary` settled the boundary `|φ_π + ρ| = 1` only for specific rules
(`InertialBoundary.unique_affine`, `InertialBoundary.ruleCubI`). This module treats **every**
rule `Ψ` that is strictly
differentiable at the steady state with slopes `φ_π ≠ 0`, `ρ`, `|φ_π + ρ| = 1` (in particular
every `C¹` rule), and decides the sunspot question by the higher-order terms of the **diagonal**
`D(y) = Ψ(y, y)`, in both directions.

## Main results

* `inertial_unique_of_repel`: if `D` is repelling on annuli (`|D y| ≥ |y| + δ(B)` on
  `B/2 ≤ |y| ≤ B`), the steady state is the only nearby bounded equilibrium under **every**
  informationally closed expectation system. The rule may be nonlinear in inflation: inflation
  surprises cannot keep the interest rate small, because `Ψ` is monotone in `π` near `0` and the
  forecast of `π_{t+1}` is pinned by the Fisher equation (the argument uses only the information
  cell of the state, `InertialBoundaryExistCube.E_eq_of_eqOn_cell`).
* `inertial_no_coin_sunspot`: on the coin tree it suffices that `D ∘ D` repels.
* `inertial_coin_sunspot_of_side`: random sunspots on the coin tree when `D ∘ D` pulls one side
  towards the steady state.
* `inertial_coin_iff` (**the criterion**): with `D(D(y)) = y + c yᵐ + o(yᵐ)`, `c ≠ 0`, random
  sunspots exist at every scale on the coin tree **iff `c < 0` or `m` is even**.
* `inertial_diag_criterion`: in terms of `D(y) = σy + c yᵏ + o(yᵏ)` itself (`σ = φ_π + ρ`):
  sunspots iff `σc < 0` or (`σ = 1` and `k` even), for `σ = 1` or `k` odd; uniqueness under every
  informationally closed system when `σc > 0`, `k` odd.
* `ruleCubI_criterion`: the rules `φ_π π + ρ î + κ î³` of `InertialBoundary`: sunspots iff
  `σκ < 0`.
-/

namespace Woodford.PriceLevelDetermination.TidyR6InertialEveryRule

open scoped Topology
open Asymptotics Filter
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic
open TidyR6ForwardSunspots (eq_zero_of_annulus coin_E_late)
open TidyR6CriticalCriterion (bound_of_isLittleO lower_of_expansion hasDerivAt_of_expansion
  comp_expansion near_lip side_estimate)
open LocalIFTSystemsApps (Finert ruleD)
open InertialBoundary (eq0_of_solves eq1_of_solves lag_known)
open ExpectationsFiniteTree (coinSystem)

/-! ### Local estimates for a rule with slopes `φ_π`, `ρ` -/

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): strict differentiability of the rule at the steady
state as an explicit estimate on a ball. -/
theorem strict_bound {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ a b : ℝ × ℝ, ‖a‖ < δ → ‖b‖ < δ →
      |Ψ a - Ψ b - (φ * (a.1 - b.1) + ρ * (a.2 - b.2))| ≤ η * ‖a - b‖ := by
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.mp (hΨ.isLittleO.def hη)
  refine ⟨δ, hδ, fun a b ha hb => ?_⟩
  have hab : dist (a, b) ((0 : ℝ × ℝ), (0 : ℝ × ℝ)) < δ := by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt ha hb
  have h := hP hab
  have e : ruleD φ ρ (a - b) = φ * (a.1 - b.1) + ρ * (a.2 - b.2) := by
    simp [ruleD]
  simp only [Real.norm_eq_abs] at h
  rw [e] at h
  exact h

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): **the rule is monotone in inflation near the
steady state**: `|Ψ(p, y) − Ψ(q, y) − φ_π(p − q)| ≤ (|φ_π|/2)|p − q|` for small `p, q, y`. -/
theorem pi_gap {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0)
    (hφ : φ ≠ 0) :
    ∃ δ > 0, ∀ p q y : ℝ, |p| < δ → |q| < δ → |y| < δ →
      |Ψ (p, y) - Ψ (q, y) - φ * (p - q)| ≤ |φ| / 2 * |p - q| := by
  obtain ⟨δ, hδ, h⟩ := strict_bound hΨ (half_pos (abs_pos.mpr hφ))
  refine ⟨δ, hδ, fun p q y hp hq hy => ?_⟩
  have ha : ‖((p, y) : ℝ × ℝ)‖ < δ := by
    rw [Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt hp hy
  have hb : ‖((q, y) : ℝ × ℝ)‖ < δ := by
    rw [Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt hq hy
  have h1 := h (p, y) (q, y) ha hb
  have hn : ‖((p, y) : ℝ × ℝ) - (q, y)‖ = |p - q| := by
    rw [Prod.mk_sub_mk, sub_self, Prod.norm_mk, norm_zero, Real.norm_eq_abs,
      max_eq_left (abs_nonneg _)]
  simp only [sub_self, mul_zero, add_zero] at h1
  rwa [hn] at h1

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): consequences of `pi_gap`: the rule is one-to-one in
inflation and `(|φ_π|/2)|p − q| ≤ |Ψ(p, y) − Ψ(q, y)| ≤ (3|φ_π|/2)|p − q|`. -/
theorem pi_bounds {Ψ : ℝ × ℝ → ℝ} {φ δ : ℝ}
    (hg : ∀ p q y : ℝ, |p| < δ → |q| < δ → |y| < δ →
      |Ψ (p, y) - Ψ (q, y) - φ * (p - q)| ≤ |φ| / 2 * |p - q|)
    {p q y : ℝ} (hp : |p| < δ) (hq : |q| < δ) (hy : |y| < δ) :
    |φ| / 2 * |p - q| ≤ |Ψ (p, y) - Ψ (q, y)| ∧ |Ψ (p, y) - Ψ (q, y)| ≤ 3 * |φ| / 2 * |p - q| := by
  have h := hg p q y hp hq hy
  have h1 := abs_sub_abs_le_abs_sub (Ψ (p, y) - Ψ (q, y)) (φ * (p - q))
  have h2 := abs_sub_abs_le_abs_sub (φ * (p - q)) (Ψ (p, y) - Ψ (q, y))
  rw [abs_sub_comm (φ * (p - q))] at h2
  rw [abs_mul] at h1 h2
  constructor <;> nlinarith [abs_nonneg φ, abs_nonneg (p - q)]

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the diagonal `D(y) = Ψ(y, y)` has slope
`φ_π + ρ` at the steady state. -/
theorem hasDerivAt_diag {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    HasDerivAt (fun y : ℝ => Ψ (y, y)) (φ + ρ) 0 := by
  have hd : HasFDerivAt (fun i : ℝ => ((i, i) : ℝ × ℝ))
      ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) 0 :=
    (hasFDerivAt_id 0).prodMk (hasFDerivAt_id 0)
  have hΨ' : HasFDerivAt Ψ (ruleD φ ρ) ((fun i : ℝ => ((i, i) : ℝ × ℝ)) 0) := hΨ
  have h := (HasFDerivAt.comp (f := fun i : ℝ => ((i, i) : ℝ × ℝ)) (0 : ℝ) hΨ' hd).hasDerivAt
  have e : ((ruleD φ ρ).comp ((ContinuousLinearMap.id ℝ ℝ).prod
      (ContinuousLinearMap.id ℝ ℝ))) 1 = φ + ρ := by
    simp [ruleD]
  rw [e] at h
  exact h

/-! ### The two conditions state by state -/

variable {Ω : Type*} {𝔼 : ExpectationSystem Ω}

/-- Woodford (2003), eq. (2.12), p. 96 (tool): under informational closure, with no shocks, the
rule holds state by state: `î_t = Ψ(π_t, î_{t−1})`. -/
theorem rule_pathwise (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {Ψ : ℝ × ℝ → ℝ}
    {x : SProcV (Fin 2) Ω} (hx : SolvesSV 𝔼 (Finert Ψ) 0 x) (t : ℕ) (ω : Ω) :
    x (t, ω) 1 = Ψ (x (t, ω) 0, lagV (0 : Fin 2 → ℝ) (fun s => x (s, ω)) t 1) := by
  have h := congrFun (eq1_of_solves hx t) ω
  have hk : 𝔼.E t (fun ω => Ψ (x (t, ω) 0,
      lagV (0 : ParS (Fin 2) (Fin 2 → ℝ) Ω).1 (fun s => x (s, ω)) t 1)) =
      fun ω => Ψ (x (t, ω) 0, lagV (0 : ParS (Fin 2) (Fin 2 → ℝ) Ω).1
        (fun s => x (s, ω)) t 1) := by
    refine hcl t _ fun ω₁ ω₂ h12 => ?_
    have e1 := LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (hx.1 t 0) ω₁ ω₂ h12
    have e2 := LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (lag_known hx t) ω₁ ω₂ h12
    change x (t, ω₁) 0 = x (t, ω₂) 0 at e1
    simp only at e2 ⊢
    rw [e1, e2]
  have hz : 𝔼.E t (fun ω => (0 : ParS (Fin 2) (Fin 2 → ℝ) Ω).2 (t, ω) 1) = 0 := by
    change 𝔼.E t (fun _ => 0) = 0
    exact 𝔼.const t 0
  rw [hk, hz] at h
  simp only [Pi.add_apply, Pi.zero_apply, add_zero] at h
  exact h

/-- Woodford (2003), eq. (1.32), p. 79 (tool): with no shocks, `E_t π_{t+1} = î_t`. -/
theorem fisher_E {Ψ : ℝ × ℝ → ℝ} {x : SProcV (Fin 2) Ω} (hx : SolvesSV 𝔼 (Finert Ψ) 0 x)
    (t : ℕ) : 𝔼.E t (toP x (t + 1) 0) = toP x t 1 := by
  rw [eq0_of_solves hx t]
  have hz : 𝔼.E t (fun ω => (0 : ParS (Fin 2) (Fin 2 → ℝ) Ω).2 (t, ω) 0) = 0 := by
    change 𝔼.E t (fun _ => 0) = 0
    exact 𝔼.const t 0
  rw [hz, sub_zero]

/-! ### Uniqueness when the diagonal repels -/

set_option maxHeartbeats 800000 in
-- the push argument works on the information cell with explicit sign bookkeeping
/-- **No sunspots for every rule whose diagonal repels** (Woodford (2003), Prop. 2.8, p. 96;
App. A.3, pp. 632–634): let `Ψ` be strictly differentiable at the steady state with slopes
`φ_π ≠ 0`, `ρ`, `Ψ(0) = 0`, and let the diagonal `D(y) = Ψ(y, y)` be repelling on annuli up to
`r > 0`. Then there is `r' > 0` such that under **every** informationally closed expectation
system the steady state is the only bounded adapted equilibrium within `r'` of it (no shocks,
`î_{−1} = 0`). -/
theorem inertial_unique_of_repel {Ψ : ℝ × ℝ → ℝ} {φ ρ r : ℝ}
    (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0) (hΨ0 : Ψ 0 = 0) (hφ : φ ≠ 0) (hr : 0 < r)
    (hrep : ∀ B, 0 < B → B ≤ r → ∃ δ > 0, ∀ y : ℝ, B / 2 ≤ |y| → |y| ≤ B →
      |y| + δ ≤ |Ψ (y, y)|) :
    ∃ r' > 0, ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω), LocalIFTStochastic.Ops.InfoClosed 𝔼 →
      ∀ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) 0 x → ‖x‖ ≤ r' → x = 0 := by
  obtain ⟨δ0, hδ0, hgap⟩ := pi_gap hΨ hφ
  have hφa : 0 < |φ| := abs_pos.mpr hφ
  refine ⟨min r (δ0 / 2), lt_min hr (by positivity), fun {Ω} 𝔼 hcl x hx hxr => ?_⟩
  have hxr1 : ‖x‖ ≤ r := hxr.trans (min_le_left _ _)
  have hxr2 : ‖x‖ < δ0 := by have := min_le_right r (δ0 / 2); linarith
  have hb : ∀ t ω j, |x (t, ω) j| < δ0 := fun t ω j => (abs_apply_le x t ω j).trans_lt hxr2
  have h00 : Ψ ((0 : ℝ), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero]; exact hΨ0
  -- interest rates vanish
  have hI : ∀ p : ℕ × Ω, x p 1 = 0 := by
    refine eq_zero_of_annulus (fun p : ℕ × Ω => x p 1)
      (fun p => (abs_apply_le x p.1 p.2 1).trans hxr1) (fun B hB hBr hall => ?_)
    obtain ⟨δ, hδ, hδP⟩ := hrep B hB hBr
    refine ⟨δ, hδ, fun q hq => ?_⟩
    obtain ⟨t, ω⟩ := q
    by_contra hcon
    push Not at hcon
    set d := x (t, ω) 1 with hd
    have hDd : B < |Ψ (d, d)| := by have := hδP d hq (hall (t, ω)); linarith
    set S : ℝ := if 0 ≤ Ψ (d, d) then 1 else -1 with hS
    have hSD : S * Ψ (d, d) = |Ψ (d, d)| := by
      by_cases h : 0 ≤ Ψ (d, d)
      · simp only [hS, h, ↓reduceIte, one_mul, abs_of_nonneg h]
      · push Not at h
        simp only [hS, not_le.mpr h, ↓reduceIte, neg_one_mul, abs_of_neg h]
    have hS1 : |S| = 1 := by
      by_cases h : 0 ≤ Ψ (d, d) <;> simp [hS, h]
    set κ := 2 / 3 * (|Ψ (d, d)| - B) with hκ
    have hκ0 : 0 < κ := by rw [hκ]; linarith
    set q : Ω → ℝ := fun w => S * φ * (x (t + 1, w) 0 - d) with hq
    have hcell : ∀ w, LocalIFTStochastic.Ops.Indist 𝔼 t ω w → q w ≤ -κ := by
      intro w hw
      have hdw : x (t, w) 1 = d :=
        (LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (hx.1 t 1) ω w hw).symm
      have hr1 := rule_pathwise hcl hx (t + 1) w
      change x (t + 1, w) 1 = Ψ (x (t + 1, w) 0, x (t, w) 1) at hr1
      rw [hdw] at hr1
      have hg := hgap (x (t + 1, w) 0) d d (hb _ _ 0) (hb t ω 1) (hb t ω 1)
      have hbd : |x (t + 1, w) 1| ≤ B := hall (t + 1, w)
      have h1 : S * x (t + 1, w) 1 ≤ B :=
        (le_abs_self _).trans (by rw [abs_mul, hS1, one_mul]; exact hbd)
      have herr : |S * (Ψ (x (t + 1, w) 0, d) - Ψ (d, d) - φ * (x (t + 1, w) 0 - d))| ≤
          |φ| / 2 * |x (t + 1, w) 0 - d| := by
        rw [abs_mul, hS1, one_mul]
        exact hg
      have hqa : |q w| = |φ| * |x (t + 1, w) 0 - d| := by
        simp only [hq, abs_mul, hS1, one_mul]
      have hsplit : S * x (t + 1, w) 1 = |Ψ (d, d)| + q w +
          S * (Ψ (x (t + 1, w) 0, d) - Ψ (d, d) - φ * (x (t + 1, w) 0 - d)) := by
        rw [hr1, ← hSD, hq]
        ring
      have he := (abs_le.mp herr).1
      rcases le_or_gt 0 (q w) with hq0 | hq0
      · rw [abs_of_nonneg hq0] at hqa
        nlinarith
      · rw [abs_of_neg hq0] at hqa
        nlinarith
    -- the forecast of `q` is zero
    have hEq : 𝔼.E t q ω = 0 := by
      have e : q = (S * φ) • (toP x (t + 1) 0 - fun _ => d) := by
        funext w
        simp only [hq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rfl
      rw [e, map_smul, map_sub, fisher_E hx t, 𝔼.const]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      change S * φ * (d - d) = 0
      ring
    have hM : ∀ w, |q w - min (q w) (-κ)| ≤ |φ| * (4 * δ0) + κ := by
      intro w
      have h1 : |q w| ≤ |φ| * (2 * δ0) := by
        simp only [hq, abs_mul, hS1, one_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg φ)
        have h3 := abs_sub (x (t + 1, w) 0) d
        have h4 := hb (t + 1) w 0
        have h5 : |d| < δ0 := hb t ω 1
        linarith
      have h2 : |min (q w) (-κ)| ≤ |q w| + κ := by
        rcases le_total (q w) (-κ) with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h, abs_neg, abs_of_pos hκ0]; linarith [abs_nonneg (q w)]
      calc |q w - min (q w) (-κ)| ≤ |q w| + |min (q w) (-κ)| := abs_sub _ _
        _ ≤ |φ| * (4 * δ0) + κ := by linarith
    have hloc := InertialBoundaryExistCube.E_eq_of_eqOn_cell 𝔼 hcl hM
      (fun w hw => (min_eq_left (hcell w hw)).symm)
    have hle : 𝔼.E t (fun w => min (q w) (-κ)) ω ≤ -κ := by
      have := 𝔼.mono t (show (fun w => min (q w) (-κ)) ≤ fun _ => -κ from
        fun w => min_le_right _ _) ω
      rw [𝔼.const] at this
      exact this
    have : (0 : ℝ) ≤ -κ := by rw [← hEq, hloc]; exact hle
    linarith
  -- inflation vanishes
  have hP : ∀ t ω, x (t, ω) 0 = 0 := by
    intro t ω
    have hr1 := rule_pathwise hcl hx t ω
    have hlag : lagV (0 : Fin 2 → ℝ) (fun s => x (s, ω)) t 1 = 0 := by
      cases t with
      | zero => rfl
      | succ s => exact hI (s, ω)
    rw [hlag, hI (t, ω)] at hr1
    have hbd := (pi_bounds hgap (hb t ω 0) (show |(0 : ℝ)| < δ0 by rwa [abs_zero])
      (show |(0 : ℝ)| < δ0 by rwa [abs_zero])).1
    rw [← hr1, h00] at hbd
    simp only [sub_self, abs_zero, sub_zero] at hbd
    have : |x (t, ω) 0| ≤ 0 := by nlinarith [abs_nonneg (x (t, ω) 0)]
    exact abs_nonpos_iff.mp this
  ext ⟨t, ω⟩ j
  fin_cases j
  · exact hP t ω
  · exact hI (t, ω)

/-! ### The coin tree -/

/-- Woodford (2003), Prop. 2.8, p. 96: **random sunspots at every scale on the coin tree** for
the exact inertial model with rule `Ψ` (no shocks, `î_{−1} = 0`): for every `ε > 0` a bounded
adapted equilibrium within `ε` of the steady state whose date-1 value differs across the first
flip. -/
def InertialCoinSunspots (Ψ : ℝ × ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ x : SProcV (Fin 2) (Bool × Bool), SolvesSV coinSystem (Finert Ψ) 0 x ∧ ‖x‖ ≤ ε ∧
    x (1, (true, true)) ≠ x (1, (false, true))

set_option maxHeartbeats 800000 in
-- the proof follows the coin-tree equilibrium date by date
/-- **No random sunspots on the coin tree when the two-step diagonal repels** (Woodford (2003),
Prop. 2.8, p. 96; App. A.3, pp. 632–634): for a rule strictly differentiable at the steady state
with `φ_π ≠ 0`, if `D ∘ D` (`D(y) = Ψ(y, y)`) is repelling on annuli up to `r > 0` and `D`
vanishes only at `0` within `r`, the exact model has no random sunspots near the steady state on
the coin tree. From date 2 the path is deterministic, `î_{t+1} = D(î_t)`, so `î_t = 0` for
`t ≥ 2`; then `π_2` solves `Ψ(π_2, î_1) = 0`, hence is known at date 1 and equals `î_1`, so
`D(î_1) = 0`; finally `Ψ(π_1, î_0) = 0` pins `π_1`. -/
theorem inertial_no_coin_sunspot {Ψ : ℝ × ℝ → ℝ} {φ ρ r : ℝ}
    (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0) (hφ : φ ≠ 0) (hr : 0 < r)
    (hG : ∀ B, 0 < B → B ≤ r → ∃ δ > 0, ∀ y : ℝ, B / 2 ≤ |y| → |y| ≤ B →
      |y| + δ ≤ |Ψ (Ψ (y, y), Ψ (y, y))|)
    (hz : ∀ y : ℝ, |y| ≤ r → Ψ (y, y) = 0 → y = 0) : ¬ InertialCoinSunspots Ψ := by
  intro hsun
  obtain ⟨δ0, hδ0, hgap⟩ := pi_gap hΨ hφ
  have hφa : 0 < |φ| := abs_pos.mpr hφ
  obtain ⟨x, hx, hxn, hne⟩ := hsun (min r (δ0 / 2)) (lt_min hr (by positivity))
  have hxr1 : ‖x‖ ≤ r := hxn.trans (min_le_left _ _)
  have hxr2 : ‖x‖ < δ0 := by have := min_le_right r (δ0 / 2); linarith
  have hb : ∀ t ω j, |x (t, ω) j| < δ0 := fun t ω j => (abs_apply_le x t ω j).trans_lt hxr2
  have hcl : LocalIFTStochastic.Ops.InfoClosed coinSystem :=
    LocalIFTStochastic.finiteTree_infoClosed _
  have hR := rule_pathwise hcl hx
  have hF : ∀ s ω, x (s + 3, ω) 0 = x (s + 2, ω) 1 := by
    intro s ω
    have h := fisher_E hx (s + 2)
    rw [coin_E_late] at h
    exact congrFun h ω
  have hstep : ∀ s ω, x (s + 3, ω) 1 = Ψ (x (s + 2, ω) 1, x (s + 2, ω) 1) := by
    intro s ω
    have h := hR (s + 3) ω
    rw [hF s ω] at h
    exact h
  -- from date 2 on the interest rate is zero
  have hlate : ∀ s ω, x (s + 2, ω) 1 = 0 := by
    intro s ω
    refine eq_zero_of_annulus (fun p : ℕ × (Bool × Bool) => x (p.1 + 2, p.2) 1)
      (fun p => (abs_apply_le x _ _ 1).trans hxr1) (fun B hB hBr hall => ?_) (s, ω)
    obtain ⟨δ, hδ, hδP⟩ := hG B hB hBr
    refine ⟨δ, hδ, fun q hq => ?_⟩
    obtain ⟨t, ω₁⟩ := q
    have hq' : B / 2 ≤ |x (t + 2, ω₁) 1| := hq
    have e : x (t + 2 + 2, ω₁) 1 = Ψ (Ψ (x (t + 2, ω₁) 1, x (t + 2, ω₁) 1),
        Ψ (x (t + 2, ω₁) 1, x (t + 2, ω₁) 1)) := by
      rw [show t + 2 + 2 = (t + 1) + 3 by ring, hstep (t + 1) ω₁,
        show t + 1 + 2 = t + 3 by ring, hstep t ω₁]
    have hb2 : |x (t + 2 + 2, ω₁) 1| ≤ B := hall (t + 2, ω₁)
    have hb0 : |x (t + 2, ω₁) 1| ≤ B := hall (t, ω₁)
    rw [e] at hb2
    have := hδP _ hq' hb0
    change |x (t + 2, ω₁) 1| ≤ B - δ
    linarith
  -- date 2
  have h2 : ∀ ω, Ψ (x (2, ω) 0, x (1, ω) 1) = 0 := by
    intro ω
    have h0 : x (2, ω) 1 = 0 := hlate 0 ω
    have h := hR 2 ω
    rw [h0] at h
    exact h.symm
  have hk2 : coinSystem.E 1 (toP x 2 0) = toP x 2 0 := by
    refine hcl 1 _ fun ω ω' h => ?_
    have e1 : x (1, ω) 1 = x (1, ω') 1 :=
      LocalIFTStochastic.Ops.cellConst_of_known coinSystem (hx.1 1 1) ω ω' h
    have hpq := (pi_bounds hgap (hb 2 ω 0) (hb 2 ω' 0) (hb 1 ω 1)).1
    have e2 : Ψ (x (2, ω') 0, x (1, ω) 1) = 0 := by rw [e1]; exact h2 ω'
    rw [h2 ω, e2, sub_zero, abs_zero] at hpq
    have h3 : |x (2, ω) 0 - x (2, ω') 0| ≤ 0 := by
      nlinarith [abs_nonneg (x (2, ω) 0 - x (2, ω') 0)]
    have h4 := abs_nonpos_iff.mp h3
    change x (2, ω) 0 = x (2, ω') 0
    linarith
  have hπ2 : ∀ ω, x (2, ω) 0 = x (1, ω) 1 := by
    intro ω
    have h := fisher_E hx 1
    rw [hk2] at h
    exact congrFun h ω
  have hi1 : ∀ ω, x (1, ω) 1 = 0 := by
    intro ω
    refine hz _ ((abs_apply_le x 1 ω 1).trans hxr1) ?_
    have := h2 ω
    rwa [hπ2 ω] at this
  -- date 1
  have hi0 : x (0, (true, true)) 1 = x (0, (false, true)) 1 :=
    LocalIFTStochastic.Ops.cellConst_of_known coinSystem (hx.1 0 1) _ _
      (fun z => by rw [LocalIFTStochasticModels.coin_E0, LocalIFTStochasticModels.coin_E0])
  have hr1 : ∀ ω, Ψ (x (1, ω) 0, x (0, ω) 1) = 0 := by
    intro ω
    have h := hR 1 ω
    rw [hi1 ω] at h
    exact h.symm
  have hp1 : x (1, (true, true)) 0 = x (1, (false, true)) 0 := by
    have hpq := (pi_bounds hgap (hb 1 (true, true) 0) (hb 1 (false, true) 0)
      (hb 0 (true, true) 1)).1
    have e2 : Ψ (x (1, (false, true)) 0, x (0, (true, true)) 1) = 0 := by
      rw [hi0]; exact hr1 _
    rw [hr1, e2, sub_zero, abs_zero] at hpq
    have h3 : |x (1, (true, true)) 0 - x (1, (false, true)) 0| ≤ 0 := by
      nlinarith [abs_nonneg (x (1, (true, true)) 0 - x (1, (false, true)) 0)]
    have h4 := abs_nonpos_iff.mp h3
    linarith
  apply hne
  funext j
  fin_cases j
  · exact hp1
  · change x (1, (true, true)) 1 = x (1, (false, true)) 1
    rw [hi1, hi1]

/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction): the orbit of the diagonal,
`y, D(y), D(D(y)), …` with `D(y) = Ψ(y, y)`. -/
noncomputable def dorb (Ψ : ℝ × ℝ → ℝ) (y : ℝ) : ℕ → ℝ
  | 0 => y
  | t + 1 => Ψ (dorb Ψ y t, dorb Ψ y t)

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): **diagonal orbits from a two-step invariant set
stay small**: if `D ∘ D` maps `A` into itself without increasing `|y|` and `|D y| ≤ L|y|` on `A`
(`L ≥ 1`), the orbit from `y ∈ A` stays within `L|y|`. -/
theorem abs_dorb_le {Ψ : ℝ × ℝ → ℝ} {A : Set ℝ} {L : ℝ} (hL : 1 ≤ L)
    (hA : ∀ y ∈ A, Ψ (Ψ (y, y), Ψ (y, y)) ∈ A ∧ |Ψ (Ψ (y, y), Ψ (y, y))| ≤ |y|)
    (hDL : ∀ y ∈ A, |Ψ (y, y)| ≤ L * |y|) {y : ℝ} (hy : y ∈ A) (t : ℕ) :
    |dorb Ψ y t| ≤ L * |y| := by
  have heven : ∀ s, dorb Ψ y (2 * s) ∈ A ∧ |dorb Ψ y (2 * s)| ≤ |y| := by
    intro s
    induction s with
    | zero => exact ⟨hy, le_rfl⟩
    | succ s ih =>
      have e : dorb Ψ y (2 * (s + 1)) = Ψ (Ψ (dorb Ψ y (2 * s), dorb Ψ y (2 * s)),
          Ψ (dorb Ψ y (2 * s), dorb Ψ y (2 * s))) := by
        rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring]
        rfl
      rw [e]
      exact ⟨(hA _ ih.1).1, (hA _ ih.1).2.trans ih.2⟩
  have hy0 : 0 ≤ |y| := abs_nonneg y
  obtain ⟨s, hs | hs⟩ := Nat.even_or_odd' t
  · rw [hs]
    calc |dorb Ψ y (2 * s)| ≤ |y| := (heven s).2
      _ ≤ L * |y| := le_mul_of_one_le_left hy0 hL
  · rw [hs]
    change |Ψ (dorb Ψ y (2 * s), dorb Ψ y (2 * s))| ≤ L * |y|
    exact (hDL _ (heven s).1).trans (mul_le_mul_of_nonneg_left (heven s).2 (by linarith))

/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction): the coin-tree path with
`(π_0, î_0)`, the date-1 inflation `π_1 = p(b)` after first flip `b`, `î_1 = Ψ(p(b), î_0)`, and
from then on the perfect-foresight path `π_{t+1} = î_t`, `î_{t+1} = Ψ(î_t, î_t)`. -/
noncomputable def inertProc (Ψ : ℝ × ℝ → ℝ) (π0 i0 : ℝ) (p : Bool → ℝ) :
    ℕ → Bool × Bool → Fin 2 → ℝ
  | 0, _ => ![π0, i0]
  | t + 1, ω => ![lagV (p ω.1) (dorb Ψ (Ψ (p ω.1, i0))) t, dorb Ψ (Ψ (p ω.1, i0)) t]

set_option maxHeartbeats 800000 in
-- the verification unfolds the coin-tree process date by date
/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction): **the path is an equilibrium** of
the exact model on the coin tree when `î_0 = Ψ(π_0, 0)` and the two date-1 inflation rates
average to `î_0` (the Fisher equation at date 0). -/
theorem solvesSV_inertProc {Ψ : ℝ × ℝ → ℝ} {π0 i0 M : ℝ} {p : Bool → ℝ}
    (hM : ∀ t ω, ‖inertProc Ψ π0 i0 p t ω‖ ≤ M) (h0 : i0 = Ψ (π0, 0))
    (h1 : p true + p false = 2 * i0) :
    SolvesSV coinSystem (Finert Ψ) 0
      (LocalIFTStochastic.mkB (fun q => inertProc Ψ π0 i0 p q.1 q.2) ⟨M, fun q => hM q.1 q.2⟩) := by
  set x : SProcV (Fin 2) (Bool × Bool) :=
    LocalIFTStochastic.mkB (fun q => inertProc Ψ π0 i0 p q.1 q.2) ⟨M, fun q => hM q.1 q.2⟩ with hx
  have hxv : ∀ t ω, x (t, ω) = inertProc Ψ π0 i0 p t ω := fun _ _ => rfl
  refine ⟨fun t i => ?_, fun t i => ?_⟩
  · rcases t with _ | t
    · have h0' : toP x 0 i = fun _ => (![π0, i0] : Fin 2 → ℝ) i := by
        funext ω
        rfl
      rw [h0']
      exact coinSystem.const 0 _
    · have h1' : toP x (t + 1) i =
          fun ω => (fun b : Bool => inertProc Ψ π0 i0 p (t + 1) (b, b) i) ω.1 := by
        funext ω
        rfl
      rw [h1']
      exact LocalIFTStochasticModels.coin_known_fst t
        (fun b : Bool => inertProc Ψ π0 i0 p (t + 1) (b, b) i)
  · have hfis0 : ∀ t, coinSystem.E t (fun ω => Finert Ψ
        (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x) (t, ω)) 0) = 0 := by
      intro t
      rcases t with _ | t
      · have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
            (0, ω)) 0) = fun ω => i0 - p ω.1 := by
          funext ω
          simp [Finert, ptS, hxv, inertProc]
        rw [hf]
        funext ω
        rw [LocalIFTStochasticModels.coin_E0]
        simp only [Pi.zero_apply]
        linarith
      · have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
            (t + 1, ω)) 0) = 0 := by
          funext ω
          simp [Finert, ptS, hxv, inertProc]
        rw [hf]
        exact map_zero _
    have hfis1 : ∀ t, coinSystem.E t (fun ω => Finert Ψ
        (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x) (t, ω)) 1) = 0 := by
      intro t
      have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
          (t, ω)) 1) = 0 := by
        funext ω
        rcases t with _ | _ | t
        · simp [Finert, ptS, hxv, inertProc, h0]
        · simp [Finert, ptS, hxv, inertProc, dorb]
        · simp [Finert, ptS, hxv, inertProc, dorb]
      rw [hf]
      exact map_zero _
    fin_cases i
    · exact hfis0 t
    · exact hfis1 t

set_option maxHeartbeats 1600000 in
-- the proof chooses `π_0` by the intermediate value theorem and checks every bound explicitly
/-- **Random sunspots for every rule whose two-step diagonal attracts one side** (Woodford
(2003), Prop. 2.8, p. 96; App. A.3, pp. 632–634): let `Ψ` be strictly differentiable at the
steady state with slopes `φ_π ≠ 0`, `ρ`, `(φ_π + ρ)² = 1`, `Ψ(0) = 0`, and let `D ∘ D`
(`D(y) = Ψ(y, y)`) map the side `0 < s·z ≤ ρ₁` into itself without increasing `|z|`. Then the
exact model has random sunspots at every scale on the coin tree: `î_0 = D(y)` for a small `y`
on that side (reached by `π_0` through the intermediate value theorem), `π_1 = î_0 ± e`, and from
date 1 the perfect-foresight path `î_{t+1} = D(î_t)`. -/
theorem inertial_coin_sunspot_of_side {Ψ : ℝ × ℝ → ℝ} {φ ρ s ρ1 : ℝ}
    (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0) (hΨ0 : Ψ 0 = 0) (hφ : φ ≠ 0)
    (hσ : (φ + ρ) * (φ + ρ) = 1) (hs : s * s = 1) (hρ1 : 0 < ρ1)
    (hside : ∀ z, 0 < s * z → s * z ≤ ρ1 →
      0 < s * Ψ (Ψ (z, z), Ψ (z, z)) ∧ s * Ψ (Ψ (z, z), Ψ (z, z)) ≤ s * z) :
    InertialCoinSunspots Ψ := by
  intro ε hε
  have h00 : Ψ ((0 : ℝ), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero]; exact hΨ0
  have hφa : 0 < |φ| := abs_pos.mpr hφ
  have hsa : |s| = 1 := by nlinarith [abs_mul_abs_self s, abs_nonneg s]
  obtain ⟨δ1, hδ1, hL⟩ := near_lip (g := fun y => Ψ (y, y)) hσ h00
    (hasDerivAt_diag hΨ.hasFDerivAt)
  obtain ⟨δ0, hδ0, hgap⟩ := pi_gap hΨ hφ
  set ρ := min δ1 ρ1 / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρδ : ρ < δ1 := by have := min_le_left δ1 ρ1; linarith
  have hρρ : ρ ≤ ρ1 := by have := min_le_right δ1 ρ1; linarith
  set A : Set ℝ := {z | 0 < s * z ∧ s * z ≤ ρ} with hA
  have habsA : ∀ z ∈ A, |z| = s * z := fun z hz => by
    have : |s * z| = |z| := by rw [abs_mul, hsa, one_mul]
    rw [← this, abs_of_pos hz.1]
  have hAinv : ∀ z ∈ A, Ψ (Ψ (z, z), Ψ (z, z)) ∈ A ∧ |Ψ (Ψ (z, z), Ψ (z, z))| ≤ |z| := by
    intro z hz
    obtain ⟨h1, h2⟩ := hside z hz.1 (hz.2.trans hρρ)
    have hm : Ψ (Ψ (z, z), Ψ (z, z)) ∈ A := ⟨h1, h2.trans hz.2⟩
    exact ⟨hm, by rw [habsA _ hm, habsA _ hz]; exact h2⟩
  have hAL : ∀ z ∈ A, |Ψ (z, z)| ≤ 2 * |z| := by
    intro z hz
    refine (hL z ?_).2
    rw [habsA _ hz]
    linarith [hz.2]
  -- the scale
  set K := 4 + 4 / |φ| with hK
  have hK4 : 4 ≤ K := by
    have : 0 < 4 / |φ| := by positivity
    linarith
  set m := min (2 * ρ / 3) (min δ0 ε) with hm
  have hm0 : 0 < m := by positivity
  set w := m / K with hw
  have hw0 : 0 < w := by positivity
  have hKw : K * w = m := by rw [hw]; field_simp
  have hmρ : m ≤ 2 * ρ / 3 := min_le_left _ _
  have hmδ : m ≤ δ0 := (min_le_right _ _).trans (min_le_left _ _)
  have hmε : m ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have hwm : w ≤ m := by nlinarith
  have hwρ : w ≤ 2 * ρ / 3 := hwm.trans hmρ
  -- the point `y` on the attracting side and `î_0 = D(y)`
  set y := s * w with hy
  have hsy : s * y = w := by rw [hy, ← mul_assoc, hs, one_mul]
  have hyA : y ∈ A := ⟨by rw [hsy]; exact hw0, by rw [hsy]; linarith⟩
  have hyabs : |y| = w := by rw [habsA _ hyA, hsy]
  obtain ⟨hG1, hG2⟩ := hside y hyA.1 (hyA.2.trans hρρ)
  rw [hsy] at hG2
  have hi0b : |Ψ (y, y)| ≤ 2 * w := by rw [← hyabs]; exact hAL y hyA
  set i0 := Ψ (y, y) with hi0
  set Gy := Ψ (i0, i0) with hGy
  -- `π_0` by the intermediate value theorem
  set a := 4 / |φ| * w with ha
  have ha0 : 0 < a := by positivity
  have haφ : a * |φ| = 4 * w := by rw [ha]; field_simp
  have haδ : a < δ0 := by
    have h1 : 4 / |φ| * w < K * w := by
      refine mul_lt_mul_of_pos_right ?_ hw0
      rw [hK]
      linarith
    rw [ha]
    linarith
  have h0δ : |(0 : ℝ)| < δ0 := by rw [abs_zero]; exact hδ0
  have hcont : ContinuousOn (fun q => Ψ (q, 0)) (Set.uIcc (-a) a) := by
    rw [Metric.continuousOn_iff]
    intro b hb e he
    refine ⟨e / (3 * |φ|), by positivity, fun c hc hcb => ?_⟩
    rw [Set.uIcc_of_le (by linarith)] at hb hc
    have hbI : |b| < δ0 := (abs_le.mpr ⟨hb.1, hb.2⟩).trans_lt haδ
    have hcI : |c| < δ0 := (abs_le.mpr ⟨hc.1, hc.2⟩).trans_lt haδ
    have h3 := (pi_bounds hgap hcI hbI h0δ).2
    rw [Real.dist_eq] at hcb ⊢
    have h4 : 3 * |φ| / 2 * |c - b| < e := by
      have := mul_lt_mul_of_pos_left hcb (show 0 < 3 * |φ| / 2 by positivity)
      have e2 : 3 * |φ| / 2 * (e / (3 * |φ|)) = e / 2 := by field_simp
      linarith
    linarith
  have hpa := hgap a 0 0 (by rw [abs_of_pos ha0]; exact haδ) h0δ h0δ
  have hpna := hgap (-a) 0 0 (by rw [abs_neg, abs_of_pos ha0]; exact haδ) h0δ h0δ
  rw [h00, sub_zero, sub_zero, abs_of_pos ha0] at hpa
  rw [h00, sub_zero, sub_zero, abs_neg, abs_of_pos ha0] at hpna
  have hmem : i0 ∈ Set.uIcc (Ψ (-a, 0)) (Ψ (a, 0)) := by
    rw [Set.mem_uIcc]
    have hi := abs_le.mp hi0b
    have hpa' := abs_le.mp hpa
    have hpna' := abs_le.mp hpna
    rcases lt_or_gt_of_ne hφ with hneg | hpos
    · rw [abs_of_neg hneg] at haφ hpa' hpna'
      right
      constructor <;> nlinarith
    · rw [abs_of_pos hpos] at haφ hpa' hpna'
      left
      constructor <;> nlinarith
  obtain ⟨π0, hπ0mem, hπ0⟩ := intermediate_value_uIcc hcont hmem
  rw [Set.uIcc_of_le (by linarith)] at hπ0mem
  have hπ0b : |π0| ≤ a := abs_le.mpr ⟨hπ0mem.1, hπ0mem.2⟩
  -- the two date-1 inflation rates
  set e := s * Gy / (3 * |φ|) with he
  have he0 : 0 < e := by positivity
  have hew : e ≤ w / (3 * |φ|) := div_le_div_of_nonneg_right hG2 (by positivity)
  set p : Bool → ℝ := fun b => if b then i0 + e else i0 - e with hp
  have hpsum : p true + p false = 2 * i0 := by
    simp only [hp, Bool.false_eq_true, ↓reduceIte]
    ring
  have hpe : ∀ b, |p b - i0| = e := by
    intro b
    cases b
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, sub_sub_cancel_left, abs_neg,
        abs_of_pos he0]
    · simp only [hp, ↓reduceIte, add_sub_cancel_left, abs_of_pos he0]
  have hKe : 2 * w + e < K * w := by
    have h1 : e ≤ 1 / (3 * |φ|) * w := by rw [one_div_mul_eq_div]; exact hew
    have h2 : 1 / (3 * |φ|) < 4 / |φ| := by
      rw [div_lt_div_iff₀ (by positivity) hφa]
      nlinarith
    have h3 : 1 / (3 * |φ|) * w < 4 / |φ| * w := mul_lt_mul_of_pos_right h2 hw0
    rw [hK]
    nlinarith
  have hpb : ∀ b, |p b| ≤ 2 * w + e := by
    intro b
    have := abs_sub_abs_le_abs_sub (p b) i0
    rw [hpe b] at this
    linarith
  have hpδ : ∀ b, |p b| < δ0 := fun b => by linarith [hpb b]
  have hi0δ : |i0| < δ0 := by linarith
  have hI1 : ∀ b, Ψ (p b, i0) ∈ A ∧ |Ψ (p b, i0)| ≤ 3 / 2 * w := by
    intro b
    have hgb := (pi_bounds hgap (hpδ b) hi0δ hi0δ).2
    rw [hpe b] at hgb
    have he3 : 3 * |φ| / 2 * e = s * Gy / 2 := by rw [he]; field_simp
    rw [he3] at hgb
    have hsd : |s * (Ψ (p b, i0) - Gy)| ≤ s * Gy / 2 := by
      rw [abs_mul, hsa, one_mul]
      exact hgb
    have hsd' := abs_le.mp hsd
    have hsplit : s * Ψ (p b, i0) = s * Gy + s * (Ψ (p b, i0) - Gy) := by ring
    have hmemA : Ψ (p b, i0) ∈ A := ⟨by linarith [hsd'.1], by linarith [hsd'.2]⟩
    refine ⟨hmemA, ?_⟩
    rw [habsA _ hmemA]
    linarith [hsd'.2]
  have hdorb : ∀ b t, |dorb Ψ (Ψ (p b, i0)) t| ≤ 3 * w := by
    intro b t
    have h := abs_dorb_le (L := 2) one_le_two hAinv hAL (hI1 b).1 t
    have := (hI1 b).2
    linarith
  have hKwε : K * w ≤ ε := by rw [hKw]; exact hmε
  have hbound : ∀ t ω, ‖inertProc Ψ π0 i0 p t ω‖ ≤ ε := by
    intro t ω
    refine (pi_norm_le_iff_of_nonneg hε.le).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    rcases t with _ | t
    · fin_cases j
      · change |π0| ≤ ε
        have : a ≤ K * w := by
          rw [ha]
          refine mul_le_mul_of_nonneg_right ?_ hw0.le
          rw [hK]
          linarith
        linarith
      · change |i0| ≤ ε
        nlinarith
    · fin_cases j
      · change |lagV (p ω.1) (dorb Ψ (Ψ (p ω.1, i0))) t| ≤ ε
        rcases t with _ | t
        · change |p ω.1| ≤ ε
          linarith [hpb ω.1]
        · change |dorb Ψ (Ψ (p ω.1, i0)) t| ≤ ε
          nlinarith [hdorb ω.1 t]
      · change |dorb Ψ (Ψ (p ω.1, i0)) t| ≤ ε
        nlinarith [hdorb ω.1 t]
  refine ⟨_, solvesSV_inertProc hbound hπ0.symm hpsum,
    LocalIFTStochastic.norm_le_of_forall hε.le fun q => hbound q.1 q.2, fun h => ?_⟩
  have h1 := congrFun h 0
  change p true = p false at h1
  simp only [hp, Bool.false_eq_true, ↓reduceIte] at h1
  linarith

/-! ### The criterion -/

/-- **The boundary of Proposition 2.8 for every rule: the criterion in the two-step diagonal**
(Woodford (2003), Prop. 2.8, p. 96; App. A.3, pp. 632–634; both directions): let `Ψ` be strictly
differentiable at the steady state with slopes `φ_π ≠ 0`, `ρ`, `|φ_π + ρ| = 1`, `Ψ(0) = 0`, and
`D(D(y)) = y + c yᵐ + o(yᵐ)` (`D(y) = Ψ(y, y)`) with `c ≠ 0`, `m ≥ 2`. The exact model has random
sunspot equilibria at every scale on the coin tree **iff `c < 0` or `m` is even**. -/
theorem inertial_coin_iff {Ψ : ℝ × ℝ → ℝ} {φ ρ c : ℝ} {m : ℕ}
    (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0) (hΨ0 : Ψ 0 = 0) (hφ : φ ≠ 0)
    (hσ : (φ + ρ) * (φ + ρ) = 1) (hm : 2 ≤ m) (hc : c ≠ 0)
    (hG : (fun y => Ψ (Ψ (y, y), Ψ (y, y)) - y - c * y ^ m) =o[𝓝 0] fun y => y ^ m) :
    InertialCoinSunspots Ψ ↔ (c < 0 ∨ Even m) := by
  have h00 : Ψ ((0 : ℝ), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero]; exact hΨ0
  constructor
  · intro hsun
    by_contra hno
    push Not at hno
    obtain ⟨hc0, hev⟩ := hno
    have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    have hodd := Nat.not_even_iff_odd.mp hev
    obtain ⟨δ1, hδ1, hL⟩ := near_lip (g := fun y => Ψ (y, y)) hσ h00
      (hasDerivAt_diag hΨ.hasFDerivAt)
    obtain ⟨δ2, hδ2, hP⟩ := lower_of_expansion hcpos hodd hG
    have hr0 : 0 < min δ1 δ2 / 2 := by positivity
    have hr1 : min δ1 δ2 / 2 < δ1 := by have := min_le_left δ1 δ2; linarith
    have hr2 : min δ1 δ2 / 2 < δ2 := by have := min_le_right δ1 δ2; linarith
    refine inertial_no_coin_sunspot hΨ hφ hr0 (fun B hB hBr => ⟨c / 2 * (B / 2) ^ m,
      by positivity, fun y hy1 hy2 => ?_⟩) (fun y hy h0 => ?_) hsun
    · have h1 := hP y (by linarith)
      have h2 : (B / 2) ^ m ≤ |y| ^ m := pow_le_pow_left₀ (by positivity) hy1 m
      nlinarith
    · have h1 := (hL y (by linarith)).1
      rw [h0, abs_zero] at h1
      have : |y| ≤ 0 := by linarith
      exact abs_nonpos_iff.mp this
  · intro h
    have hneg_case : c < 0 → InertialCoinSunspots Ψ := fun hneg => by
      obtain ⟨ρ1, hρ1, hside⟩ := side_estimate (G := fun y => Ψ (Ψ (y, y), Ψ (y, y))) (s := 1)
        (by norm_num) hm (by rw [one_pow, mul_one]; exact hneg) hG
      exact inertial_coin_sunspot_of_side hΨ hΨ0 hφ hσ (by norm_num) hρ1 hside
    rcases h with hneg | hev
    · exact hneg_case hneg
    · rcases lt_or_gt_of_ne hc with hneg | hpos
      · exact hneg_case hneg
      · obtain ⟨ρ1, hρ1, hside⟩ := side_estimate (G := fun y => Ψ (Ψ (y, y), Ψ (y, y)))
          (s := -1) (by norm_num) hm (by rw [hev.add_one.neg_one_pow]; linarith) hG
        exact inertial_coin_sunspot_of_side hΨ hΨ0 hφ hσ (by norm_num) hρ1 hside

/-- **The criterion in the leading coefficient of the diagonal** (Woodford (2003), Prop. 2.8,
p. 96; App. A.3, pp. 632–634; both directions): for a rule as in `inertial_coin_iff` whose
diagonal is `D(y) = σy + c yᵏ + o(yᵏ)` (`σ = φ_π + ρ = ±1`, `c ≠ 0`, `k ≥ 2`), with `σ = 1` or
`k` odd: random sunspots exist at every scale on the coin tree **iff `σc < 0` or (`σ = 1` and `k`
even)**; and when `σc > 0` with `k` odd, the steady state is the only nearby bounded equilibrium
under **every** informationally closed expectation system. (For `σ = −1` and `k` even the order-`k`
term cancels in `D ∘ D`, and `inertial_coin_iff` applies to the leading term of `D ∘ D`;
`TidyR6CriticalCriterion.flip_even_undecided` shows the leading term of `D` cannot decide.) -/
theorem inertial_diag_criterion {Ψ : ℝ × ℝ → ℝ} {φ ρ c : ℝ} {k : ℕ}
    (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0) (hΨ0 : Ψ 0 = 0) (hφ : φ ≠ 0)
    (hσ : (φ + ρ) * (φ + ρ) = 1) (hk : 2 ≤ k) (hc : c ≠ 0) (hcase : φ + ρ = 1 ∨ Odd k)
    (hD : (fun y => Ψ (y, y) - (φ + ρ) * y - c * y ^ k) =o[𝓝 0] fun y => y ^ k) :
    (InertialCoinSunspots Ψ ↔ ((φ + ρ) * c < 0 ∨ (φ + ρ = 1 ∧ Even k))) ∧
    (0 < (φ + ρ) * c → Odd k → ∃ r > 0, ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω),
      LocalIFTStochastic.Ops.InfoClosed 𝔼 → ∀ x : SProcV (Fin 2) Ω,
        SolvesSV 𝔼 (Finert Ψ) 0 x → ‖x‖ ≤ r → x = 0) := by
  set σ := φ + ρ with hσdef
  have hG := comp_expansion (g := fun y => Ψ (y, y)) hσ hk hD
  constructor
  · rcases mul_self_eq_one_iff.mp hσ with h1 | h1
    · rw [h1, one_pow] at hG
      rw [inertial_coin_iff hΨ hΨ0 hφ hσ hk (by rw [h1] at *; intro h; apply hc; linarith) hG,
        h1]
      constructor
      · rintro (h | h)
        · left; linarith
        · right; exact ⟨rfl, h⟩
      · rintro (h | h)
        · left; linarith
        · right; exact h.2
    · have hodd : Odd k := by
        rcases hcase with h | h
        · rw [h1] at h; norm_num at h
        · exact h
      rw [h1, hodd.neg_one_pow] at hG
      rw [inertial_coin_iff hΨ hΨ0 hφ hσ hk (by intro h; apply hc; linarith) hG, h1]
      have hne : ¬ Even k := Nat.not_even_iff_odd.mpr hodd
      constructor
      · rintro (h | h)
        · left; linarith
        · exact absurd h hne
      · rintro (h | h)
        · left; linarith
        · norm_num at h
  · intro hsc hodd
    have hF : (fun y => σ * Ψ (y, y) - y - (σ * c) * y ^ k) =o[𝓝 0] fun y => y ^ k := by
      refine (hD.const_mul_left σ).congr_left fun y => ?_
      linear_combination (-y) * hσ
    obtain ⟨δ, hδ, hP⟩ := lower_of_expansion hsc hodd hF
    have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
    refine inertial_unique_of_repel hΨ hΨ0 hφ (r := δ / 2) (half_pos hδ)
      (fun B hB hBr => ⟨σ * c / 2 * (B / 2) ^ k, by positivity, fun y hy1 hy2 => ?_⟩)
    have h1 := hP y (by linarith)
    rw [abs_mul, hs, one_mul] at h1
    have h2 : (B / 2) ^ k ≤ |y| ^ k := pow_le_pow_left₀ (by positivity) hy1 k
    nlinarith

/-- **The cubic rules of `InertialBoundary`, all signs** (Woodford (2003), Prop. 2.8, p. 96):
for `Ψ(π, î) = φ_π π + ρ î + κ î³` (`InertialBoundary.ruleCubI`) with `φ_π ≠ 0`,
`|φ_π + ρ| = 1`, `κ ≠ 0`: random sunspots at every scale on the coin tree **iff
`(φ_π + ρ)κ < 0`**, and for `(φ_π + ρ)κ > 0` the steady state is the only nearby bounded
equilibrium under every informationally closed expectation system. -/
theorem ruleCubI_criterion {φ ρ κ : ℝ} (hφ : φ ≠ 0) (hσ : (φ + ρ) * (φ + ρ) = 1) (hκ : κ ≠ 0) :
    (InertialCoinSunspots (InertialBoundary.ruleCubI φ ρ κ) ↔ (φ + ρ) * κ < 0) ∧
    (0 < (φ + ρ) * κ → ∃ r > 0, ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω),
      LocalIFTStochastic.Ops.InfoClosed 𝔼 → ∀ x : SProcV (Fin 2) Ω,
        SolvesSV 𝔼 (Finert (InertialBoundary.ruleCubI φ ρ κ)) 0 x → ‖x‖ ≤ r → x = 0) := by
  obtain ⟨-, hfd, -, hcd, -, h0, -⟩ := InertialBoundary.rules_slopes φ ρ κ 0
  have hstrict : HasStrictFDerivAt (InertialBoundary.ruleCubI φ ρ κ) (ruleD φ ρ) 0 :=
    ((hcd 1).2.1.contDiffAt).hasStrictFDerivAt' hfd one_ne_zero
  have hD : (fun y => InertialBoundary.ruleCubI φ ρ κ (y, y) - (φ + ρ) * y - κ * y ^ 3) =o[𝓝 0]
      fun y => y ^ 3 :=
    (isLittleO_zero (fun y : ℝ => y ^ 3) (𝓝 0)).congr_left fun y => by
      simp only [InertialBoundary.ruleCubI]
      ring
  obtain ⟨h1, h2⟩ := inertial_diag_criterion hstrict h0 hφ hσ (by norm_num) hκ (Or.inr (by decide))
    hD
  refine ⟨?_, fun h => h2 h (by decide)⟩
  rw [h1]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact h
    · exact absurd h (by decide)
  · exact Or.inl

end Woodford.PriceLevelDetermination.TidyR6InertialEveryRule
