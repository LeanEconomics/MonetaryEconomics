/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaAssumption81
import OptimalPolicyRules.NKAssumption81

/-!
# Existence and uniqueness for the rule system of p. 593

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, p. 593: the inflation-inertia model
(2.6) (corrected, Chapter 3 (3.6)), (3.1) under commitment to the implicit instrument rule
(3.16), for every degree of indexation `0 ≤ γ ≤ 1`.

`InflationInertiaRules.rule_system_determinate` proves that a bounded solution of the
optimal-plan first-order system solves the rule system (2.6), (3.1), (3.16) and is its only
bounded solution with its history; `InflationInertiaRules.rule_system_unique` proves uniqueness
for all parameters. The bounded optimal plan that p. 593 assumes is supplied for `0 < γ ≤ 1` by
`InertiaAssumption81.in_focSolvableMB` (the general problem `GeneralLinksInertia.inProblem`)
and for `γ = 0` by `NKAssumption81.NK.nk_focSolvableM` (the basic problem
`GeneralLinks.nkProblem`). This module links those solutions to the `InflationInertiaRules`
formulation.

## Main results

* `RuleSol`: a bounded adapted solution of (2.6), (3.1) (dates `≥ 2`) and (3.16) (every date
  `n = t + 2 ≥ 2`) with the history `(π₁, x₁, i₁, i₀)`; `History`: the history is bounded,
  `π₁, x₁, i₁` are known at date 1 and `i₀` at date 0.
* `euler_of_focs`: (3.15), (3.4), (3.5) give (3.16) at every date (no pull-out property needed).
* `exists_pos` (`0 < γ ≤ 1`) and `exists_zero` (`γ = 0`): **for every bounded adapted
  disturbance and every history the rule system has a bounded solution**: the optimal plan from
  `t₀ = 2` with `Z₂ = π₁` and the pre-sample multipliers inferred from `(x₁, i₁, i₀)` through
  (3.4)–(3.5), with the history glued in at dates 0 and 1.
* `rule_system_exists` (any `γ ∈ [0, 1]`), `rule_system_exists_iff` (a solution exists iff the
  history is bounded and known), and **`rule_system_existsUnique`**: for every `γ ∈ [0, 1]`,
  faithful expectations with the pull-out property, the rule system has exactly one bounded
  adapted solution with each history (unique at every date `≥ 1`; `π₀, x₀` do not enter).
-/

namespace Woodford.OptimalPolicyRules.TidyRuleSystem

open GeneralSetup GeneralFOC GeneralFOC.LQ
open IRuleBasic (Calib)
open GeneralLinks (piOf xOf iOf cNK nkProblem nkPhi1 nkPhi2)
open GeneralLinksInertia (inProblem Zof Xi1 Xi2)
open InflationInertiaRules (AS IS Euler fbig FOC315 FOC34 FOC35 Bnd)

variable {Ω : Type*}

/-! ### The objects -/

/-- Woodford (2003), p. 593: the history `(π₁, x₁, i₁, i₀)` of the rule system is bounded, with
`π₁, x₁, i₁` known at date 1 and `i₀` known at date 0. -/
def History (𝔼 : ExpectationSystem Ω) (p1 x1 i1 i0 : Ω → ℝ) : Prop :=
  𝔼.E 1 p1 = p1 ∧ 𝔼.E 1 x1 = x1 ∧ 𝔼.E 1 i1 = i1 ∧ 𝔼.E 0 i0 = i0 ∧
    ∃ K, ∀ ω, |p1 ω| ≤ K ∧ |x1 ω| ≤ K ∧ |i1 ω| ≤ K ∧ |i0 ω| ≤ K

/-- Woodford (2003), p. 593: `(π, x, i)` is a bounded adapted solution of the rule system — the
aggregate-supply relation (2.6) (corrected) and the IS relation (3.1) at dates `≥ 2` and the
rule (3.16) at every date `n = t + 2` — with history `π₁ = p₁`, `x₁ = x₁`, `i₁ = i₁`,
`i₀ = i₀`. -/
def RuleSol (𝔼 : ExpectationSystem Ω) (c : Calib) (γ : ℝ) (u rn : ℕ → Ω → ℝ)
    (p1 x1 i1 i0 : Ω → ℝ) (π x i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ 𝔼.Adapted x ∧ 𝔼.Adapted i ∧ Bnd π ∧ Bnd x ∧ Bnd i ∧
    (∀ k, 2 ≤ k → AS 𝔼 c.β γ c.κ u π x k) ∧ (∀ k, 2 ≤ k → IS 𝔼 c.σ rn π x i k) ∧
    (∀ t, Euler 𝔼 c.β γ c.κ c.σ (fun k ω => i k ω - c.istar)
      (fbig 𝔼 c.β γ c.κ c.σ c.lx c.li π x) t) ∧
    π 1 = p1 ∧ x 1 = x1 ∧ i 1 = i1 ∧ i 0 = i0

/-! ### Tools -/

/-- Woodford (2003), p. 593 (tool): `E_t` of an affine combination of three variables known at
`t` is itself. -/
theorem known_lin3 (𝔼 : ExpectationSystem Ω) {t : ℕ} {f g h : Ω → ℝ} (hf : 𝔼.E t f = f)
    (hg : 𝔼.E t g = g) (hh : 𝔼.E t h = h) (a b d e : ℝ) :
    𝔼.E t (fun ω => a * f ω + b * g ω + d * h ω + e) =
      fun ω => a * f ω + b * g ω + d * h ω + e := by
  change 𝔼.E t (a • f + b • g + d • h + fun _ => e) = a • f + b • g + d • h + fun _ => e
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, 𝔼.const, hf, hg, hh]

/-- Woodford (2003), p. 593 (tool): an affine combination of three bounded random variables is
bounded. -/
theorem bdd_lin3 {f g h : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |f ω| ≤ K ∧ |g ω| ≤ K ∧ |h ω| ≤ K)
    (a b d e : ℝ) : ∃ B, ∀ ω, |a * f ω + b * g ω + d * h ω + e| ≤ B := by
  refine ⟨|a| * K + |b| * K + |d| * K + |e|, fun ω => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hK ω
  have e1 := abs_add_le (a * f ω + b * g ω + d * h ω) e
  have e2 := abs_add_le (a * f ω + b * g ω) (d * h ω)
  have e3 := abs_add_le (a * f ω) (b * g ω)
  rw [abs_mul] at e2 e3
  rw [abs_mul] at e3
  have m1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have m2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
  have m3 := mul_le_mul_of_nonneg_left h3 (abs_nonneg d)
  linarith

/-- Woodford (2003), (3.5) (tool): the multiplier `Ξ₁ = −(λᵢ/σ)(i − i*)` read off (3.5) is
adapted when `i` is. -/
theorem xi1_adapted (𝔼 : ExpectationSystem Ω) {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i)
    (a istar : ℝ) : 𝔼.Adapted (fun k ω => a * (i k ω - istar)) := by
  intro k
  rw [ExpectationTools.E_fun_mul, ExpectationTools.E_fun_sub, hi k, 𝔼.const]

/-- Woodford (2003), (2.6) (tool): `E_k[π_{k+1} − γπ_k] = E_kπ_{k+1} − γπ_k` for adapted `π`. -/
theorem E_qd (𝔼 : ExpectationSystem Ω) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (γ : ℝ) (k : ℕ)
    (ω : Ω) : 𝔼.E k (fun ω' => π (k + 1) ω' - γ * π k ω') ω = 𝔼.E k (π (k + 1)) ω - γ * π k ω := by
  rw [ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul, hπ k]

/-- **Woodford (2003), (3.15), (3.4), (3.5) ⇒ (3.16), pp. 592–593**: if (3.5) holds at every
date, (3.4) at every date `≥ 1` and (3.15) at every date `≥ 2`, then the Euler equation (3.16)
holds at every date `n = t + 2` (any expectation system; no pull-out property needed). -/
theorem euler_of_focs (𝔼 : ExpectationSystem Ω) {β γ κ σ lamx lami xstar istar : ℝ}
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : lami ≠ 0) {π x i Ξ1 Ξ2 : ℕ → Ω → ℝ}
    (hπ : 𝔼.Adapted π) (hx : 𝔼.Adapted x) (hi : 𝔼.Adapted i) (hΞ1 : 𝔼.Adapted Ξ1)
    (h5 : ∀ k, FOC35 σ lami istar i Ξ1 k) (h4 : ∀ k, 1 ≤ k → FOC34 β κ lamx xstar x Ξ1 Ξ2 k)
    (h15 : ∀ k, 2 ≤ k → FOC315 𝔼 β γ σ π Ξ1 Ξ2 k) (t : ℕ) :
    Euler 𝔼 β γ κ σ (fun k ω => i k ω - istar) (fbig 𝔼 β γ κ σ lamx lami π x) t :=
  (InflationInertiaRules.foc315_iff_euler 𝔼 hβ hκ hσ hli hπ hx hi hΞ1 t (fun k _ _ => h5 k)
    (fun k hk _ => h4 k (by omega))).mp (h15 (t + 2) (by omega))

/-- Woodford (2003), (2.1)/(2.6), (3.1) as (1.1) (tool): the disturbance vector `cNK` of
bounded disturbances is bounded. -/
theorem cNK_bounded (c : Calib) {u rn : ℕ → Ω → ℝ} (hub : Bnd u) (hrb : Bnd rn) :
    BoundedV (cNK c u rn) := by
  obtain ⟨Cu, -, hCu⟩ := hub
  obtain ⟨Cr, -, hCr⟩ := hrb
  refine ⟨Cu + |c.σ| * Cr, fun t ω j => ?_⟩
  have h1 := hCu t ω
  have h2 := mul_le_mul_of_nonneg_left (hCr t ω) (abs_nonneg c.σ)
  have h3 : 0 ≤ |c.σ| * |rn t ω| := by positivity
  have h4 : 0 ≤ |u t ω| := abs_nonneg _
  fin_cases j
  · change |-u t ω| ≤ _
    rw [abs_neg]
    linarith
  · change |-(c.σ * rn t ω)| ≤ _
    rw [abs_neg, abs_mul]
    linarith

/-- Woodford (2003), (2.1)/(2.6), (3.1) as (1.1) (tool): the disturbance vector `cNK` of
adapted disturbances is adapted. -/
theorem cNK_adapted (𝔼 : ExpectationSystem Ω) (c : Calib) {u rn : ℕ → Ω → ℝ}
    (hua : 𝔼.Adapted u) (hra : 𝔼.Adapted rn) : AdaptedV 𝔼 (cNK c u rn) := by
  intro t j
  fin_cases j
  · change 𝔼.E t (-(u t)) = -(u t)
    rw [map_neg, hua t]
  · change 𝔼.E t (-(c.σ • rn t)) = -(c.σ • rn t)
    rw [map_neg, map_smul, hra t]

/-- Woodford (2003), p. 593 (tool): a bound for the glued processes. -/
theorem bnd_glue {g : ℕ → Ω → ℝ} {M K : ℝ} (h : ∀ k ω, |g k ω| ≤ M ∨ |g k ω| ≤ K) :
    Bnd g := by
  refine ⟨max (max M K) 0, le_max_right _ _, fun k ω => ?_⟩
  rcases h k ω with h1 | h1
  · exact h1.trans ((le_max_left M K).trans (le_max_left _ _))
  · exact h1.trans ((le_max_right M K).trans (le_max_left _ _))

/-! ### Existence for `0 < γ ≤ 1` -/

/-- **Woodford (2003), p. 593: existence for `0 < γ ≤ 1`.** For every bounded adapted
disturbance `(u, rⁿ)` and every bounded history `(π₁, x₁, i₁, i₀)` (`π₁, x₁, i₁` known at 1,
`i₀` at 0), the rule system (2.6), (3.1), (3.16) has a bounded adapted solution with that
history, under any expectation system. It is the bounded optimal plan from `t₀ = 2`
(`InertiaAssumption81.in_focSolvableMB`) with `Z₂ = π₁` and `M₁ = (Ξ₂₁, Ξ₁₁)` inferred from
`(x₁, i₁, i₀)` through (3.4)–(3.5), with the history glued in at dates 0 and 1. -/
theorem exists_pos (c : Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hub : Bnd u) (hua : 𝔼.Adapted u)
    (hrb : Bnd rn) (hra : 𝔼.Adapted rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : History 𝔼 p1 x1 i1 i0) : ∃ π x i, RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i := by
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  obtain ⟨hβ0, hβ1, hσ0, hκ0, hlx0, hli0⟩ := hc
  have hβ : c.β ≠ 0 := hβ0.ne'
  have hσ : c.σ ≠ 0 := hσ0.ne'
  have hκ : c.κ ≠ 0 := hκ0.ne'
  have hli : c.li ≠ 0 := hli0.ne'
  have hi01 : 𝔼.E 1 i0 = i0 := ForwardSolution.E_of_known 𝔼 (by norm_num) hi0
  -- the pre-sample multipliers inferred from the history
  set X1 : Ω → ℝ := fun ω => -(c.li / c.σ) * (i1 ω - c.istar) with hX1d
  set X0 : Ω → ℝ := fun ω => -(c.li / c.σ) * (i0 ω - c.istar) with hX0d
  set X2 : Ω → ℝ := fun ω => (c.lx * (x1 ω - c.xstar) + X1 ω - c.β⁻¹ * X0 ω) / c.κ with hX2d
  have eX1 : X1 = fun ω => -(c.li / c.σ) * i1 ω + 0 * x1 ω + 0 * i0 ω + c.li / c.σ * c.istar := by
    funext ω
    simp only [hX1d]
    ring
  have eX2 : X2 = fun ω => c.lx / c.κ * x1 ω + (-(c.li / c.σ) / c.κ) * i1 ω +
      (c.β⁻¹ * (c.li / c.σ) / c.κ) * i0 ω +
        (-(c.lx * c.xstar) + c.li / c.σ * c.istar - c.β⁻¹ * (c.li / c.σ) * c.istar) / c.κ := by
    funext ω
    simp only [hX2d, hX1d, hX0d]
    field_simp
    ring
  set Z0 : Ω → Unit → ℝ := fun ω _ => p1 ω with hZ0d
  set M0 : Ω → Fin 2 → ℝ := fun ω => ![X2 ω, X1 ω] with hM0d
  have hZk : KnownV 𝔼 2 Z0 := fun _ => ForwardSolution.E_of_known 𝔼 (by norm_num) hp1
  have hMk : KnownV 𝔼 (2 - 1) M0 := by
    intro j
    fin_cases j
    · change 𝔼.E 1 X2 = X2
      rw [eX2]
      exact known_lin3 𝔼 hx1 hi1 hi01 _ _ _ _
    · change 𝔼.E 1 X1 = X1
      rw [eX1]
      exact known_lin3 𝔼 hi1 hx1 hi01 _ _ _ _
  have hK' : ∀ ω, |x1 ω| ≤ K ∧ |i1 ω| ≤ K ∧ |i0 ω| ≤ K := fun ω =>
    ⟨(hK ω).2.1, (hK ω).2.2.1, (hK ω).2.2.2⟩
  have hK'' : ∀ ω, |i1 ω| ≤ K ∧ |x1 ω| ≤ K ∧ |i0 ω| ≤ K := fun ω =>
    ⟨(hK ω).2.2.1, (hK ω).2.1, (hK ω).2.2.2⟩
  have hMb : ∃ B, ∀ ω r, |M0 ω r| ≤ B := by
    obtain ⟨B2, hB2⟩ := bdd_lin3 hK' (c.lx / c.κ) (-(c.li / c.σ) / c.κ)
      (c.β⁻¹ * (c.li / c.σ) / c.κ)
      ((-(c.lx * c.xstar) + c.li / c.σ * c.istar - c.β⁻¹ * (c.li / c.σ) * c.istar) / c.κ)
    obtain ⟨B1, hB1⟩ := bdd_lin3 hK'' (-(c.li / c.σ)) 0 0 (c.li / c.σ * c.istar)
    refine ⟨max B1 B2, fun ω r => ?_⟩
    fin_cases r
    · change |X2 ω| ≤ _
      rw [eX2]
      exact (hB2 ω).trans (le_max_right _ _)
    · change |X1 ω| ≤ _
      rw [eX1]
      exact (hB1 ω).trans (le_max_left _ _)
  obtain ⟨y, φ, hs⟩ := InertiaAssumption81.in_focSolvableMB c γ ⟨hβ0, hβ1, hσ0, hκ0,
    hlx0, hli0⟩ hγ0 hγ1 𝔼 2 (cNK c u rn) Z0 M0 (cNK_bounded c hub hrb)
    (cNK_adapted 𝔼 c hua hra) hZk ⟨K, fun ω _ => (hK ω).1⟩ hMb hMk
  have hc' : c.Adm := ⟨hβ0, hβ1, hσ0, hκ0, hlx0, hli0⟩
  obtain ⟨⟨hst, hZ0, ⟨My, hMy⟩, hya⟩, -, hmφ, hM, hfoc⟩ := hs
  -- the rows of (1.1) and (1.9) at dates `≥ 2`
  have hS : ∀ k, 2 ≤ k → ∀ ω, Zof y (k + 1) ω = piOf y k ω ∧
      c.β * 𝔼.E k (piOf y (k + 1)) ω =
        -γ * Zof y k ω + (1 + c.β * γ) * piOf y k ω - c.κ * xOf y k ω + cNK c u rn k ω 0 ∧
      c.σ * 𝔼.E k (piOf y (k + 1)) ω + 𝔼.E k (xOf y (k + 1)) ω =
        xOf y k ω + c.σ * iOf y k ω + cNK c u rn k ω 1 := fun k hk ω =>
    (InertiaFOCSystem.in_struct_at c γ hc' hγ0.le 𝔼 (cNK c u rn) y k ω).mp (hst k hk ω)
  have hF := fun k (hk : 2 ≤ k) ω =>
    (GeneralLinksInertia.in_foc_at_iff c γ hc' hγ0.le 𝔼 y hmφ k ω).mp (hfoc k hk ω)
  -- the glued processes
  set π : ℕ → Ω → ℝ := fun k => if k = 1 then p1 else piOf y k with hπd
  set x : ℕ → Ω → ℝ := fun k => if k = 1 then x1 else xOf y k with hxd
  set i : ℕ → Ω → ℝ := fun k => if k = 0 then i0 else if k = 1 then i1 else iOf y k with hid
  set Ξ1 : ℕ → Ω → ℝ := fun k ω => -(c.li / c.σ) * (i k ω - c.istar) with hΞ1d
  set Ξ2 : ℕ → Ω → ℝ := Xi2 φ with hΞ2d
  have hπk : ∀ k, 2 ≤ k → π k = piOf y k := fun k hk => by
    simp only [hπd, show k ≠ 1 by omega, ↓reduceIte]
  have hxk : ∀ k, 2 ≤ k → x k = xOf y k := fun k hk => by
    simp only [hxd, show k ≠ 1 by omega, ↓reduceIte]
  have hik : ∀ k, 2 ≤ k → i k = iOf y k := fun k hk => by
    simp only [hid, show k ≠ 0 by omega, show k ≠ 1 by omega, ↓reduceIte]
  have hπ1 : π 1 = p1 := by simp only [hπd, ↓reduceIte]
  have hx1' : x 1 = x1 := by simp only [hxd, ↓reduceIte]
  have hi1' : i 1 = i1 := by simp only [hid, one_ne_zero, ↓reduceIte]
  have hi0' : i 0 = i0 := by simp only [hid, ↓reduceIte]
  have hπa : 𝔼.Adapted π := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hπd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 0))
      · rw [hπ1]; exact hp1
    · rw [hπk k hk]; exact hya k (Sum.inl (Sum.inr 0))
  have hxa : 𝔼.Adapted x := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hxd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 1))
      · rw [hx1']; exact hx1
    · rw [hxk k hk]; exact hya k (Sum.inl (Sum.inr 1))
  have hia : 𝔼.Adapted i := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [hi0']; exact hi0
      · rw [hi1']; exact hi1
    · rw [hik k hk]; exact hya k (Sum.inr ())
  have hΞ1a : 𝔼.Adapted Ξ1 := xi1_adapted 𝔼 hia _ _
  -- `Z_k = π_{k−1}` for `k ≥ 2`
  have hZ : ∀ k, 2 ≤ k → ∀ ω, Zof y k ω = π (k - 1) ω := by
    intro k hk ω
    rcases Nat.lt_or_ge k 3 with h3 | h3
    · obtain rfl : k = 2 := by omega
      rw [show 2 - 1 = 1 by rfl, hπ1]
      exact congrFun (hZ0 ω) ()
    · have := (hS (k - 1) (by omega) ω).1
      rw [show k - 1 + 1 = k by omega] at this
      rw [this, hπk (k - 1) (by omega)]
  -- the multipliers
  have hXi1 : ∀ k, 1 ≤ k → ∀ ω, Xi1 φ k ω = Ξ1 k ω := by
    intro k hk ω
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      have := congrFun (hM ω) 1
      simp only [Mpart, hM0d, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [Xi1, hΞ1d, hi1']
      rw [this]
    · have h3 := (hF k h2 ω).2.2.2
      simp only [hΞ1d, hik k h2]
      field_simp
      linarith
  have hXi21 : ∀ ω, Ξ2 1 ω = X2 ω := by
    intro ω
    have := congrFun (hM ω) 0
    simp only [Mpart, hM0d, Matrix.cons_val_zero] at this
    exact this
  have hφ1 : ∀ k, 2 ≤ k → ∀ ω, φ k ω (Sum.inr 1) = Ξ1 (k - 1) ω := by
    intro k hk ω
    rw [← hXi1 (k - 1) (by omega) ω]
    simp only [Xi1, show k - 1 + 1 = k by omega]
  have hφ0 : ∀ k, 2 ≤ k → ∀ ω, φ k ω (Sum.inr 0) = Ξ2 (k - 1) ω := by
    intro k hk ω
    simp only [hΞ2d, Xi2, show k - 1 + 1 = k by omega]
  have hξ : ∀ s, 2 ≤ s → ∀ ω, φ s ω (Sum.inl ()) =
      -(c.β * γ) * (Ξ2 s ω + (π s ω - γ * π (s - 1) ω)) := by
    intro s hs ω
    have h0 := (hF s hs ω).1
    rw [hZ s hs ω, ← hπk s hs] at h0
    simp only [hΞ2d]
    field_simp at h0
    linear_combination -h0
  -- the first-order conditions in the `InflationInertiaRules` form
  have h5 : ∀ k, FOC35 c.σ c.li c.istar i Ξ1 k := by
    intro k ω
    simp only [hΞ1d]
    field_simp
    ring
  have h4 : ∀ k, 1 ≤ k → FOC34 c.β c.κ c.lx c.xstar x Ξ1 Ξ2 k := by
    intro k hk ω
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      rw [hXi21 ω, hx1']
      simp only [hΞ1d, hX2d, hX1d, hX0d, hi1', hi0', show 1 - 1 = 0 by rfl]
      field_simp
      ring
    · have h3 := (hF k h2 ω).2.2.1
      rw [hXi1 k (by omega) ω, hφ1 k h2 ω, ← hxk k h2] at h3
      simp only [hΞ2d]
      linarith
  have h15 : ∀ k, 2 ≤ k → FOC315 𝔼 c.β γ c.σ π Ξ1 Ξ2 k := by
    intro k hk ω
    have h1 := (hF k hk ω).2.1
    have hE : (fun ω' => φ (k + 1) ω' (Sum.inl ())) =
        fun ω' => -(c.β * γ) * (Ξ2 (k + 1) ω' + (π (k + 1) ω' - γ * π k ω')) := by
      funext ω'
      rw [hξ (k + 1) (by omega) ω', show k + 1 - 1 = k by omega]
    rw [hE, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add, hZ k hk ω, ← hπk k hk,
      hφ0 k hk ω, hφ1 k hk ω] at h1
    have hb : c.β⁻¹ * (c.β * Ξ2 (k - 1) ω + c.σ * Ξ1 (k - 1) ω) =
        Ξ2 (k - 1) ω + c.β⁻¹ * c.σ * Ξ1 (k - 1) ω := by
      field_simp
    rw [hb] at h1
    simp only [hΞ2d] at h1 ⊢
    linear_combination h1
  have hAS : ∀ k, 2 ≤ k → AS 𝔼 c.β γ c.κ u π x k := by
    intro k hk ω
    have h1 := (hS k hk ω).2.1
    rw [hZ k hk ω, ← hπk k hk, ← hπk (k + 1) (by omega), ← hxk k hk] at h1
    rw [E_qd 𝔼 hπa γ k ω]
    simp only [cNK, Matrix.cons_val_zero] at h1
    linarith
  have hIS : ∀ k, 2 ≤ k → IS 𝔼 c.σ rn π x i k := by
    intro k hk ω
    have h1 := (hS k hk ω).2.2
    rw [← hπk (k + 1) (by omega), ← hxk k hk, ← hxk (k + 1) (by omega), ← hik k hk] at h1
    simp only [cNK, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    linarith
  have hbπ : Bnd π := bnd_glue (M := My) (K := K) fun k ω => by
    rcases eq_or_ne k 1 with rfl | hk
    · right; rw [hπ1]; exact (hK ω).1
    · left; simp only [hπd, hk, ↓reduceIte]; exact hMy k ω _
  have hbx : Bnd x := bnd_glue (M := My) (K := K) fun k ω => by
    rcases eq_or_ne k 1 with rfl | hk
    · right; rw [hx1']; exact (hK ω).2.1
    · left; simp only [hxd, hk, ↓reduceIte]; exact hMy k ω _
  have hbi : Bnd i := bnd_glue (M := My) (K := K) fun k ω => by
    rcases eq_or_ne k 0 with rfl | hk0
    · right; rw [hi0']; exact (hK ω).2.2.2
    rcases eq_or_ne k 1 with rfl | hk
    · right; rw [hi1']; exact (hK ω).2.2.1
    · left; simp only [hid, hk0, hk, ↓reduceIte]; exact hMy k ω _
  exact ⟨π, x, i, hπa, hxa, hia, hbπ, hbx, hbi, hAS, hIS,
    euler_of_focs 𝔼 hβ hκ hσ hli hπa hxa hia hΞ1a h5 h4 h15, hπ1, hx1', hi1', hi0'⟩

/-! ### Existence for `γ = 0` -/

/-- **Woodford (2003), p. 593: existence for `γ = 0`.** For every bounded adapted disturbance
and every bounded history `(π₁, x₁, i₁, i₀)` the rule system (2.6), (3.1), (3.16) at `γ = 0` has
a bounded adapted solution with that history, under any expectation system: the bounded optimal
plan of the basic problem from `t₀ = 2` (`NKAssumption81.NK.nk_focSolvableM`) with the
pre-sample multipliers inferred from `(x₁, i₁, i₀)`, with the history glued in. (Unlike
`Links.inertia_system_gamma_zero`, the history here is an arbitrary bounded random vector.) -/
theorem exists_zero (c : Calib) (hc : c.Adm) (𝔼 : ExpectationSystem Ω) {u rn : ℕ → Ω → ℝ}
    (hub : Bnd u) (hua : 𝔼.Adapted u) (hrb : Bnd rn) (hra : 𝔼.Adapted rn)
    {p1 x1 i1 i0 : Ω → ℝ} (hh : History 𝔼 p1 x1 i1 i0) :
    ∃ π x i, RuleSol 𝔼 c 0 u rn p1 x1 i1 i0 π x i := by
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  obtain ⟨hβ0, hβ1, hσ0, hκ0, hlx0, hli0⟩ := hc
  have hc' : c.Adm := ⟨hβ0, hβ1, hσ0, hκ0, hlx0, hli0⟩
  have hβ : c.β ≠ 0 := hβ0.ne'
  have hσ : c.σ ≠ 0 := hσ0.ne'
  have hκ : c.κ ≠ 0 := hκ0.ne'
  have hli : c.li ≠ 0 := hli0.ne'
  have hi01 : 𝔼.E 1 i0 = i0 := ForwardSolution.E_of_known 𝔼 (by norm_num) hi0
  set X1 : Ω → ℝ := fun ω => -(c.li / c.σ) * (i1 ω - c.istar) with hX1d
  set X0 : Ω → ℝ := fun ω => -(c.li / c.σ) * (i0 ω - c.istar) with hX0d
  set X2 : Ω → ℝ := fun ω => (c.lx * (x1 ω - c.xstar) + X1 ω - c.β⁻¹ * X0 ω) / c.κ with hX2d
  have eX1 : X1 = fun ω => -(c.li / c.σ) * i1 ω + 0 * x1 ω + 0 * i0 ω + c.li / c.σ * c.istar := by
    funext ω
    simp only [hX1d]
    ring
  have eX2 : X2 = fun ω => c.lx / c.κ * x1 ω + (-(c.li / c.σ) / c.κ) * i1 ω +
      (c.β⁻¹ * (c.li / c.σ) / c.κ) * i0 ω +
        (-(c.lx * c.xstar) + c.li / c.σ * c.istar - c.β⁻¹ * (c.li / c.σ) * c.istar) / c.κ := by
    funext ω
    simp only [hX2d, hX1d, hX0d]
    field_simp
    ring
  set Z0 : Ω → Empty → ℝ := fun _ e => e.elim with hZ0d
  set M0 : Ω → Fin 2 → ℝ := fun ω => ![X2 ω, X1 ω] with hM0d
  have hZk : KnownV 𝔼 2 Z0 := fun e => e.elim
  have hMk : KnownV 𝔼 (2 - 1) M0 := by
    intro j
    fin_cases j
    · change 𝔼.E 1 X2 = X2
      rw [eX2]
      exact known_lin3 𝔼 hx1 hi1 hi01 _ _ _ _
    · change 𝔼.E 1 X1 = X1
      rw [eX1]
      exact known_lin3 𝔼 hi1 hx1 hi01 _ _ _ _
  have hK' : ∀ ω, |x1 ω| ≤ K ∧ |i1 ω| ≤ K ∧ |i0 ω| ≤ K := fun ω =>
    ⟨(hK ω).2.1, (hK ω).2.2.1, (hK ω).2.2.2⟩
  have hK'' : ∀ ω, |i1 ω| ≤ K ∧ |x1 ω| ≤ K ∧ |i0 ω| ≤ K := fun ω =>
    ⟨(hK ω).2.2.1, (hK ω).2.1, (hK ω).2.2.2⟩
  have hMb : ∃ B, ∀ ω r, |M0 ω r| ≤ B := by
    obtain ⟨B2, hB2⟩ := bdd_lin3 hK' (c.lx / c.κ) (-(c.li / c.σ) / c.κ)
      (c.β⁻¹ * (c.li / c.σ) / c.κ)
      ((-(c.lx * c.xstar) + c.li / c.σ * c.istar - c.β⁻¹ * (c.li / c.σ) * c.istar) / c.κ)
    obtain ⟨B1, hB1⟩ := bdd_lin3 hK'' (-(c.li / c.σ)) 0 0 (c.li / c.σ * c.istar)
    refine ⟨max B1 B2, fun ω r => ?_⟩
    fin_cases r
    · change |X2 ω| ≤ _
      rw [eX2]
      exact (hB2 ω).trans (le_max_right _ _)
    · change |X1 ω| ≤ _
      rw [eX1]
      exact (hB1 ω).trans (le_max_left _ _)
  obtain ⟨y, φ, hs⟩ := NKAssumption81.NK.nk_focSolvableM c hc' 𝔼 2 (cNK c u rn) Z0 M0
    (cNK_bounded c hub hrb) (cNK_adapted 𝔼 c hua hra) hZk hMb hMk
  obtain ⟨⟨hst, -, ⟨My, hMy⟩, hya⟩, -, hmφ, hM, hfoc⟩ := hs
  have hS : ∀ k, 2 ≤ k → ∀ ω, c.β * 𝔼.E k (piOf y (k + 1)) ω =
        piOf y k ω - c.κ * xOf y k ω + cNK c u rn k ω 0 ∧
      c.σ * 𝔼.E k (piOf y (k + 1)) ω + 𝔼.E k (xOf y (k + 1)) ω =
        xOf y k ω + c.σ * iOf y k ω + cNK c u rn k ω 1 := fun k hk ω =>
    (NKAssumption81.NK.nk_struct_at c hσ 𝔼 (cNK c u rn) y k ω).mp (hst k hk ω).2
  have hF := fun k (hk : 2 ≤ k) ω =>
    (GeneralLinks.nk_foc_at_iff c hc' 𝔼 y hmφ k ω).mp (hfoc k hk ω)
  set π : ℕ → Ω → ℝ := fun k => if k = 1 then p1 else piOf y k with hπd
  set x : ℕ → Ω → ℝ := fun k => if k = 1 then x1 else xOf y k with hxd
  set i : ℕ → Ω → ℝ := fun k => if k = 0 then i0 else if k = 1 then i1 else iOf y k with hid
  set Ξ1 : ℕ → Ω → ℝ := fun k ω => -(c.li / c.σ) * (i k ω - c.istar) with hΞ1d
  set Ξ2 : ℕ → Ω → ℝ := nkPhi2 φ with hΞ2d
  have hπk : ∀ k, 2 ≤ k → π k = piOf y k := fun k hk => by
    simp only [hπd, show k ≠ 1 by omega, ↓reduceIte]
  have hxk : ∀ k, 2 ≤ k → x k = xOf y k := fun k hk => by
    simp only [hxd, show k ≠ 1 by omega, ↓reduceIte]
  have hik : ∀ k, 2 ≤ k → i k = iOf y k := fun k hk => by
    simp only [hid, show k ≠ 0 by omega, show k ≠ 1 by omega, ↓reduceIte]
  have hπ1 : π 1 = p1 := by simp only [hπd, ↓reduceIte]
  have hx1' : x 1 = x1 := by simp only [hxd, ↓reduceIte]
  have hi1' : i 1 = i1 := by simp only [hid, one_ne_zero, ↓reduceIte]
  have hi0' : i 0 = i0 := by simp only [hid, ↓reduceIte]
  have hπa : 𝔼.Adapted π := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hπd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 0))
      · rw [hπ1]; exact hp1
    · rw [hπk k hk]; exact hya k (Sum.inl (Sum.inr 0))
  have hxa : 𝔼.Adapted x := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hxd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 1))
      · rw [hx1']; exact hx1
    · rw [hxk k hk]; exact hya k (Sum.inl (Sum.inr 1))
  have hia : 𝔼.Adapted i := by
    intro k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [hi0']; exact hi0
      · rw [hi1']; exact hi1
    · rw [hik k hk]; exact hya k (Sum.inr ())
  have hΞ1a : 𝔼.Adapted Ξ1 := xi1_adapted 𝔼 hia _ _
  have hXi1 : ∀ k, 1 ≤ k → ∀ ω, nkPhi1 φ k ω = Ξ1 k ω := by
    intro k hk ω
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      have := congrFun (hM ω) 1
      simp only [Mpart, hM0d, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [nkPhi1, hΞ1d, hi1']
      rw [this]
    · have h3 := (hF k h2 ω).2.2
      simp only [hΞ1d, hik k h2]
      field_simp
      linarith
  have hXi21 : ∀ ω, Ξ2 1 ω = X2 ω := by
    intro ω
    have := congrFun (hM ω) 0
    simp only [Mpart, hM0d, Matrix.cons_val_zero] at this
    exact this
  have hφ1 : ∀ k, 2 ≤ k → ∀ ω, φ k ω (Sum.inr 1) = Ξ1 (k - 1) ω := by
    intro k hk ω
    rw [← hXi1 (k - 1) (by omega) ω]
    simp only [nkPhi1, show k - 1 + 1 = k by omega]
  have hφ0 : ∀ k, 2 ≤ k → ∀ ω, φ k ω (Sum.inr 0) = Ξ2 (k - 1) ω := by
    intro k hk ω
    simp only [hΞ2d, nkPhi2, show k - 1 + 1 = k by omega]
  have h5 : ∀ k, FOC35 c.σ c.li c.istar i Ξ1 k := by
    intro k ω
    simp only [hΞ1d]
    field_simp
    ring
  have h4 : ∀ k, 1 ≤ k → FOC34 c.β c.κ c.lx c.xstar x Ξ1 Ξ2 k := by
    intro k hk ω
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      rw [hXi21 ω, hx1']
      simp only [hΞ1d, hX2d, hX1d, hX0d, hi1', hi0', show 1 - 1 = 0 by rfl]
      field_simp
      ring
    · have h3 := (hF k h2 ω).2.1
      rw [hXi1 k (by omega) ω, hφ1 k h2 ω, ← hxk k h2] at h3
      simp only [hΞ2d]
      linarith
  have h15 : ∀ k, 2 ≤ k → FOC315 𝔼 c.β 0 c.σ π Ξ1 Ξ2 k := by
    intro k hk ω
    have h1 := (hF k hk ω).1
    rw [← hπk k hk, hφ0 k hk ω, hφ1 k hk ω] at h1
    have hb : c.σ / c.β = c.β⁻¹ * c.σ := by field_simp
    rw [hb] at h1
    simp only [hΞ2d] at h1 ⊢
    linear_combination h1
  have hAS : ∀ k, 2 ≤ k → AS 𝔼 c.β 0 c.κ u π x k := by
    intro k hk ω
    have h1 := (hS k hk ω).1
    rw [← hπk k hk, ← hπk (k + 1) (by omega), ← hxk k hk] at h1
    rw [E_qd 𝔼 hπa 0 k ω]
    simp only [cNK, Matrix.cons_val_zero] at h1
    linarith
  have hIS : ∀ k, 2 ≤ k → IS 𝔼 c.σ rn π x i k := by
    intro k hk ω
    have h1 := (hS k hk ω).2
    rw [← hπk (k + 1) (by omega), ← hxk k hk, ← hxk (k + 1) (by omega), ← hik k hk] at h1
    simp only [cNK, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    linarith
  have hbπ : Bnd π := bnd_glue (M := My) (K := K) fun k ω => by
    rcases eq_or_ne k 1 with rfl | hk
    · right; rw [hπ1]; exact (hK ω).1
    · left; simp only [hπd, hk, ↓reduceIte]; exact hMy k ω _
  have hbx : Bnd x := bnd_glue (M := My) (K := K) fun k ω => by
    rcases eq_or_ne k 1 with rfl | hk
    · right; rw [hx1']; exact (hK ω).2.1
    · left; simp only [hxd, hk, ↓reduceIte]; exact hMy k ω _
  have hbi : Bnd i := bnd_glue (M := My) (K := K) fun k ω => by
    rcases eq_or_ne k 0 with rfl | hk0
    · right; rw [hi0']; exact (hK ω).2.2.2
    rcases eq_or_ne k 1 with rfl | hk
    · right; rw [hi1']; exact (hK ω).2.2.1
    · left; simp only [hid, hk0, hk, ↓reduceIte]; exact hMy k ω _
  exact ⟨π, x, i, hπa, hxa, hia, hbπ, hbx, hbi, hAS, hIS,
    euler_of_focs 𝔼 hβ hκ hσ hli hπa hxa hia hΞ1a h5 h4 h15, hπ1, hx1', hi1', hi0'⟩

/-! ### Existence and uniqueness for every `γ ∈ [0, 1]` -/

/-- **Woodford (2003), p. 593: existence for every `0 ≤ γ ≤ 1`.** For every bounded adapted
disturbance and every bounded history known at the right dates, the rule system (2.6), (3.1),
(3.16) has a bounded adapted solution with that history (any expectation system). -/
theorem rule_system_exists (c : Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hub : Bnd u) (hua : 𝔼.Adapted u)
    (hrb : Bnd rn) (hra : 𝔼.Adapted rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : History 𝔼 p1 x1 i1 i0) : ∃ π x i, RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i := by
  rcases hγ0.lt_or_eq with hγ | rfl
  · exact exists_pos c hc hγ hγ1 𝔼 hub hua hrb hra hh
  · exact exists_zero c hc 𝔼 hub hua hrb hra hh

/-- Woodford (2003), p. 593: a solution of the rule system has a bounded history, known at the
right dates (the converse of `rule_system_exists`). -/
theorem history_of_sol {𝔼 : ExpectationSystem Ω} {c : Calib} {γ : ℝ} {u rn : ℕ → Ω → ℝ}
    {p1 x1 i1 i0 : Ω → ℝ} {π x i : ℕ → Ω → ℝ} (h : RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i) :
    History 𝔼 p1 x1 i1 i0 := by
  obtain ⟨hπa, hxa, hia, ⟨Cπ, -, hCπ⟩, ⟨Cx, -, hCx⟩, ⟨Ci, -, hCi⟩, -, -, -, h1, h2, h3, h4⟩ := h
  subst h1 h2 h3 h4
  refine ⟨hπa 1, hxa 1, hia 1, hia 0, max (max Cπ Cx) Ci, fun ω => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (hCπ 1 ω).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hCx 1 ω).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (hCi 1 ω).trans (le_max_right _ _)
  · exact (hCi 0 ω).trans (le_max_right _ _)

/-- **Woodford (2003), p. 593, existence exactly characterised**: for `0 ≤ γ ≤ 1` the rule
system has a bounded adapted solution with history `(π₁, x₁, i₁, i₀)` **iff** that history is
bounded with `π₁, x₁, i₁` known at 1 and `i₀` known at 0. -/
theorem rule_system_exists_iff (c : Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hub : Bnd u) (hua : 𝔼.Adapted u)
    (hrb : Bnd rn) (hra : 𝔼.Adapted rn) (p1 x1 i1 i0 : Ω → ℝ) :
    (∃ π x i, RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i) ↔ History 𝔼 p1 x1 i1 i0 :=
  ⟨fun ⟨_, _, _, h⟩ => history_of_sol h,
    fun hh => rule_system_exists c hc hγ0 hγ1 𝔼 hub hua hrb hra hh⟩

/-- **Woodford (2003), p. 593: the rule system (3.16) is determinate for every `γ ∈ [0, 1]`.**
Under the standing assumptions (`0 < β < 1`, `σ, κ, λₓ, λᵢ > 0`) and faithful expectations with
the pull-out property, for every bounded adapted disturbance `(u, rⁿ)` and every bounded history
`(π₁, x₁, i₁, i₀)` known at the right dates, the system (2.6), (3.1), (3.16) has a bounded
adapted solution with that history, and every bounded adapted solution with that history
coincides with it at every date `≥ 1` (the values `π₀, x₀` do not enter the system). -/
theorem rule_system_existsUnique (c : Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (hpull : 𝔼.PullOut) (hfaith : ExpectationTools.Faithful 𝔼)
    {u rn : ℕ → Ω → ℝ} (hub : Bnd u) (hua : 𝔼.Adapted u) (hrb : Bnd rn) (hra : 𝔼.Adapted rn)
    {p1 x1 i1 i0 : Ω → ℝ} (hh : History 𝔼 p1 x1 i1 i0) :
    ∃ π x i, RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i ∧
      ∀ π' x' i', RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π' x' i' →
        ∀ k, 1 ≤ k → π' k = π k ∧ x' k = x k ∧ i' k = i k := by
  obtain ⟨π, x, i, hsol⟩ := rule_system_exists c hc hγ0 hγ1 𝔼 hub hua hrb hra hh
  refine ⟨π, x, i, hsol, fun π' x' i' hsol' k hk => ?_⟩
  obtain ⟨ha, hb, hc3, b1, b2, b3, hAS, hIS, hE, e1, e2, e3, e4⟩ := hsol
  obtain ⟨ha', hb', hc3', b1', b2', b3', hAS', hIS', hE', e1', e2', e3', e4'⟩ := hsol'
  obtain ⟨hβ0, hβ1, hσ0, hκ0, hlx0, hli0⟩ := hc
  have key := InflationInertiaRules.rule_system_unique 𝔼 hpull hfaith hβ0 hβ1 hκ0.ne' hσ0.ne'
    hli0 hlx0.le ha' hb' hc3' ha hb hc3 b1' b2' b3' b1 b2 b3 hAS' hAS hIS' hIS hE' hE
    (fun ω => by rw [e1, e1']) (fun ω => by rw [e2, e2']) (fun ω => by rw [e3, e3'])
    (fun ω => by rw [e4, e4']) k hk
  exact ⟨funext fun ω => (key ω).1, funext fun ω => (key ω).2.1, funext fun ω => (key ω).2.2⟩

end Woodford.OptimalPolicyRules.TidyRuleSystem
