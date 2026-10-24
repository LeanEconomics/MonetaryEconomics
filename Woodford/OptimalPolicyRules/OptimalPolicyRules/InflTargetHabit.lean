/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflTargetInertia
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Optimal inflation targeting with habit persistence

Woodford (2003), *Interest and Prices*, Chapter 8, §2.3, pp. 568–569.

The aggregate-supply relation is (2.23)
`π_t = κ[(x_t − δ x_{t−1}) − βδ E_t(x_{t+1} − δ x_t)] + β E_t π_{t+1} + u_t` and the loss is
(2.24) `π_t² + λ (x_t − δ x_{t−1} − x̂*)²`, both functions of the quasi-differenced gap
`z_t = x_t − δ x_{t−1}` (`quasiDiff δ x₀ x`).

## Main results

* `lagrangian_derivs`: the first-order conditions are the derivatives of the Lagrangian; the
  derivative with respect to `x_t` is `g_t − βδ g_{t+1}` with
  `g_t = λ(x_t − δ x_{t−1} − x̂*) − κ φ_t + δκ φ_{t−1}` (survey E17: this RAW condition is not
  (2.26)).
* `raw_iff_g_zero`: for bounded multipliers and plans (`βδ < 1`) the raw condition
  `g_t − βδ E_t g_{t+1} = 0` is equivalent to (2.26) `g_t = 0`; `raw_not_imp_g_zero`: without
  boundedness it is not (the unbounded path `g_t = (βδ)^{−t}`).
* `habit_excess`, `habit_sufficient`, `habit_unique`: Lagrangian sufficiency — a plan satisfying
  (2.25)–(2.26) with bounded adapted multipliers minimises the expected loss among bounded plans
  with the same `π_{t₀} − δκ z_{t₀}` (timeless constraint), uniquely (`π`, `z` and `x` in
  conditional mean square).
* p. 569: `g_eq` (`g_t = −κ(d_t − δ d_{t−1})`, `d_t = φ_t − (λ/κ)(x_t − x*)`,
  `x* = x̂*/(1 − δ)`), `foc226_iff` (the general solution of (2.26)), `phi_timeInvariant` (the
  time-invariant multiplier `φ_t = (λ/κ)(x_t − x*)`).
* (2.27): `criterion_foc_habit` and `habit_robustlyOptimal`: the criterion
  `π_t + (λ/κ)(x_t − x_{t−1}) = 0` — the SAME criterion as in the baseline model, independent of
  `δ` (hence of `η`; the book writes `λ_x` for `λ`) — is robustly optimal for every
  `0 ≤ δ < 1`; `as_iff_secondOrder_habit` reduces the equilibrium to the workhorse with
  `c = κ(1 − δ)(1 − βδ)/(κδ + φ) > 0`.
-/

namespace Woodford.OptimalPolicyRules.InflTargetHabit

open Filter Topology InflTargetInertia

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model (2.23)–(2.24) -/

/-- Woodford (2003), (2.23), p. 568:
`π_t = κ[(x_t − δ x_{t−1}) − βδ E_t(x_{t+1} − δ x_t)] + β E_t π_{t+1} + u_t`. -/
def ASh (β κ δ : ℝ) (x₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω = κ * (quasiDiff δ x₀ x t ω - β * δ * 𝔼.E t (quasiDiff δ x₀ x (t + 1)) ω) +
    β * 𝔼.E t (π (t + 1)) ω + u t ω

/-- Woodford (2003), (2.24), p. 568: the period loss `π_t² + λ (x_t − δ x_{t−1} − x̂*)²`. -/
def lossH (lam xhat δ : ℝ) (x₀ : Ω → ℝ) (π x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  periodLoss lam xhat π (quasiDiff δ x₀ x)

/-- Woodford (2003), (2.23)–(2.24): an admissible plan (bounded adapted `π, x` satisfying
(2.23), given `x_{t₀−1} = x₀`). -/
def PlanH (β κ δ : ℝ) (x₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ASh 𝔼 β κ δ x₀ u π x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x

/-- Woodford (2003), Ch. 8 §1.1 Definition, for (2.23)–(2.24): timeless optimality. The
forward-looking combination of (2.23) is `π − δκ z` (it appears in the constraint of date
`t₀ − 1` as `E_{t₀−1}[β π_{t₀} − βδκ z_{t₀}]`), so the initial constraint (1.6) fixes
`π_{t₀} − δκ z_{t₀}` at its value under the plan. -/
def TimelessOptimalH (β κ δ lam xhat : ℝ) (x₀ : Ω → ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  PlanH 𝔼 β κ δ x₀ u π x ∧ ∀ π' x', PlanH 𝔼 β κ δ x₀ u π' x' →
    (∀ ω, π' 0 ω - δ * κ * quasiDiff δ x₀ x' 0 ω = π 0 ω - δ * κ * quasiDiff δ x₀ x 0 ω) →
    ∀ ω, expLossOf 𝔼 β (lossH lam xhat δ x₀ π x) ω ≤ expLossOf 𝔼 β (lossH lam xhat δ x₀ π' x') ω

/-- Woodford (2003), (2.26), p. 569: `g_t = λ(x_t − δ x_{t−1} − x̂*) − κ φ_t + δκ φ_{t−1}`, the
left side of (2.26). -/
def gH (κ lam xhat δ : ℝ) (x₀ φ₀ : Ω → ℝ) (x φ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => lam * (quasiDiff δ x₀ x t ω - xhat) - κ * φ t ω + δ * κ * lagW φ₀ φ t ω

/-- Woodford (2003), (2.25)–(2.26), p. 569: the first-order conditions as printed,
`π_t + φ_t − φ_{t−1} = 0` and `g_t = 0`. -/
def FOCh (κ lam xhat δ : ℝ) (x₀ φ₀ : Ω → ℝ) (π x φ : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω + φ t ω - lagW φ₀ φ t ω = 0 ∧ gH κ lam xhat δ x₀ φ₀ x φ t ω = 0

/-- Woodford (2003), (2.25)–(2.26) (survey E17): the RAW first-order conditions of the
Lagrangian, `π_t + φ_t − φ_{t−1} = 0` and `g_t − βδ E_t g_{t+1} = 0`. -/
def FOCraw (β κ lam xhat δ : ℝ) (x₀ φ₀ : Ω → ℝ) (π x φ : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω + φ t ω - lagW φ₀ φ t ω = 0 ∧
    gH κ lam xhat δ x₀ φ₀ x φ t ω -
      β * δ * 𝔼.E t (gH κ lam xhat δ x₀ φ₀ x φ (t + 1)) ω = 0

/-! ### The Lagrangian derivatives (survey E17) -/

/-- **Woodford (2003), (2.25)–(2.26), p. 569 (survey E17: the raw FOC)**: in the Lagrangian
`∑ βᵗ{½π_t² + ½λ(z_t − x̂*)² + φ_t[π_t − κ(z_t − βδ z_{t+1}) − β π_{t+1}]}`,
`z_t = x_t − δ x_{t−1}` (perfect foresight, divided by `βᵗ`), the terms containing `π_t` have
derivative `π_t + φ_t − φ_{t−1}` (2.25), and the terms containing `x_t = v` have derivative
`g_t − βδ g_{t+1}`, NOT `g_t` as printed in (2.26). -/
theorem lagrangian_derivs (β κ lam xhat δ xm xp φm φ φp v : ℝ) :
    HasDerivAt (fun v => v ^ 2 / 2 + φ * v - φm * v) (v + φ - φm) v ∧
      HasDerivAt (fun v => lam / 2 * (v - δ * xm - xhat) ^ 2 +
          β * (lam / 2) * (xp - δ * v - xhat) ^ 2 +
          φ * (-(κ * (v - δ * xm)) + κ * β * δ * (xp - δ * v)) + φm * κ * δ * v +
          β * φp * κ * δ * v)
        ((lam * (v - δ * xm - xhat) - κ * φ + δ * κ * φm) -
          β * δ * (lam * (xp - δ * v - xhat) - κ * φp + δ * κ * φ)) v := by
  refine ⟨?_, ?_⟩
  · have h := hasDerivAt_quad (1 / 2) (φ - φm) 0 v
    convert h using 1
    · funext v; ring
    · ring
  · have h := hasDerivAt_quad (lam / 2 + β * (lam / 2) * δ ^ 2)
      (-(lam * (δ * xm + xhat)) - β * lam * δ * (xp - xhat) - φ * κ - φ * κ * β * δ ^ 2 +
        φm * κ * δ + β * φp * κ * δ)
      (lam / 2 * (δ * xm + xhat) ^ 2 + β * (lam / 2) * (xp - xhat) ^ 2 + φ * κ * δ * xm +
        φ * κ * β * δ * xp) v
    convert h using 1
    · funext v; ring
    · ring

/-! ### Survey E17: the raw condition and (2.26) -/

/-- Woodford (2003), p. 569: `g` of a bounded plan with bounded multipliers is bounded. -/
theorem gH_bounded {κ lam xhat δ : ℝ} {x₀ φ₀ : Ω → ℝ} {x φ : ℕ → Ω → ℝ} {B C : ℝ}
    (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hφ₀ : ∀ ω, |φ₀ ω| ≤ C) (hx : BoundedProc x)
    (hφ : BoundedProc φ) : BoundedProc (gH κ lam xhat δ x₀ φ₀ x φ) := by
  obtain ⟨X, hX⟩ := hx
  obtain ⟨F, hF⟩ := hφ
  refine ⟨|lam| * (X + |δ| * max B X + |xhat|) + |κ| * F + |δ * κ| * max C F,
    fun t ω => ?_⟩
  simp only [gH, quasiDiff]
  refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul]
    gcongr
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hX t ω) ?_)) le_rfl)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (lagW_bounded hx₀ hX t ω) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF t ω) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (lagW_bounded hφ₀ hF t ω) (abs_nonneg _)

/-- **Woodford (2003), (2.26), p. 569 (survey E17, the correct statement)**: for `|βδ| < 1` and
bounded `x, φ` (bounded initial values), the raw condition `g_t − βδ E_t g_{t+1} = 0` for all
`t` holds iff `g_t = 0` for all `t` (forward iteration). -/
theorem raw_iff_g_zero {β κ lam xhat δ B C : ℝ} (hβδ : |β * δ| < 1) {x₀ φ₀ : Ω → ℝ}
    {x φ : ℕ → Ω → ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hφ₀ : ∀ ω, |φ₀ ω| ≤ C) (hx : BoundedProc x)
    (hφ : BoundedProc φ) :
    (∀ t ω, gH κ lam xhat δ x₀ φ₀ x φ t ω -
      β * δ * 𝔼.E t (gH κ lam xhat δ x₀ φ₀ x φ (t + 1)) ω = 0) ↔
      ∀ t ω, gH κ lam xhat δ x₀ φ₀ x φ t ω = 0 := by
  constructor
  · intro h
    have hsol : ∀ t, gH κ lam xhat δ x₀ φ₀ x φ t =
        (β * δ) • 𝔼.E t (gH κ lam xhat δ x₀ φ₀ x φ (t + 1)) + (fun _ : ℕ => (0 : Ω → ℝ)) t := by
      intro t; funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
      linarith [h t ω]
    have h0 : ∀ t, (0 : Ω → ℝ) = (β * δ) • 𝔼.E t (0 : Ω → ℝ) + (fun _ : ℕ => (0 : Ω → ℝ)) t :=
      fun t => by simp
    have := 𝔼.forward_unique hβδ hsol (z₂ := fun _ => 0) h0
      (gH_bounded hx₀ hφ₀ hx hφ) ⟨0, fun _ _ => by simp⟩
    intro t ω
    simpa using congrFun (congrFun this t) ω
  · intro h t ω
    have : gH κ lam xhat δ x₀ φ₀ x φ (t + 1) = 0 := funext (h (t + 1))
    rw [h t ω, this, map_zero]
    simp

/-- **Woodford (2003), (2.26), p. 569 (survey E17, counterexample)**: without boundedness the raw
condition does not imply (2.26): under perfect foresight, with `βδ ≠ 0`, `λ ≠ 0`, `π = φ = 0`,
`x_{t₀−1} = 0`, `z_t = x̂* + (βδ)^{−t}/λ` and the cost-push path that makes (2.23) hold, the
raw conditions hold at every date but `g_0 = 1 ≠ 0`. -/
theorem raw_not_imp_g_zero {β κ lam xhat δ : ℝ} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hlam : lam ≠ 0) :
    let z : ℕ → Unit → ℝ := fun t _ => xhat + ((β * δ) ^ t)⁻¹ / lam
    let x := backRec δ (fun _ => 0) z
    let u : ℕ → Unit → ℝ := fun t _ => -(κ * (z t () - β * δ * z (t + 1) ()))
    ASh perfectForesight β κ δ (fun _ => 0) u (fun _ _ => 0) x ∧
      FOCraw perfectForesight β κ lam xhat δ (fun _ => 0) (fun _ => 0) (fun _ _ => 0) x
        (fun _ _ => 0) ∧
      gH κ lam xhat δ (fun _ => 0) (fun _ => 0) x (fun _ _ => 0) 0 () = 1 := by
  intro z x u
  have hz : ∀ t ω, quasiDiff δ (fun _ => 0) x t ω = z t ω := fun t ω => by
    have := congrFun (backRec_eq δ (fun _ => 0) z t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [quasiDiff, x]
    linarith
  have hg : ∀ t, gH κ lam xhat δ (fun _ => 0) (fun _ => 0) x (fun _ _ => 0) t () =
      ((β * δ) ^ t)⁻¹ := fun t => by
    simp only [gH, hz, z]
    cases t <;> simp only [lagW_zero, lagW_succ] <;> field_simp <;> ring
  have hβδ : β * δ ≠ 0 := mul_ne_zero hβ hδ
  refine ⟨fun t ω => ?_, fun t ω => ⟨?_, ?_⟩, ?_⟩
  · cases ω
    change (0 : ℝ) = κ * (quasiDiff δ (fun _ => 0) x t () -
      β * δ * quasiDiff δ (fun _ => 0) x (t + 1) ()) + β * 0 + u t ()
    rw [hz, hz]
    simp only [u]
    ring
  · cases t <;> simp
  · cases ω
    change gH κ lam xhat δ (fun _ => 0) (fun _ => 0) x (fun _ _ => 0) t () -
      β * δ * gH κ lam xhat δ (fun _ => 0) (fun _ => 0) x (fun _ _ => 0) (t + 1) () = 0
    rw [hg, hg, pow_succ, mul_inv]
    field_simp
    ring
  · rw [hg]; simp

/-! ### Lagrangian sufficiency -/

/-- Woodford (2003), (2.24): the quasi-difference of a bounded process with a bounded initial
value is bounded. -/
theorem quasiDiff_bounded {δ B : ℝ} {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B)
    (hx : BoundedProc x) : BoundedProc (quasiDiff δ x₀ x) := by
  obtain ⟨X, hX⟩ := hx
  refine ⟨X + |δ| * max B X, fun t ω => ?_⟩
  simp only [quasiDiff]
  refine (abs_sub _ _).trans (add_le_add (hX t ω) ?_)
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (lagW_bounded hx₀ hX t ω) (abs_nonneg _)

/-- Woodford (2003), (2.23): `E_t z_{t+1} = E_t x_{t+1} − δ x_t` for adapted `x`. -/
theorem E_quasiDiff {δ : ℝ} {x₀ : Ω → ℝ} {x : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x) (t : ℕ)
    (ω : Ω) : 𝔼.E t (quasiDiff δ x₀ x (t + 1)) ω = 𝔼.E t (x (t + 1)) ω - δ * x t ω := by
  have : quasiDiff δ x₀ x (t + 1) = x (t + 1) - δ • x t := rfl
  rw [this, map_sub, map_smul, hxa t]
  rfl

/-- **Woodford (2003), (2.23)–(2.26) (the Lagrangian identity and sufficiency)**: if `(π*, x*)`
satisfies (2.25)–(2.26) with a bounded adapted multiplier and a bounded initial multiplier, and
`(π, x)` is any admissible plan (same `x_{t₀−1}`) with
`φ_{t₀−1}((π_0 − π*_0) − δκ(z_0 − z*_0)) = 0` (the timeless initial constraint, or a zero initial
multiplier), then the excess expected loss is `∑ βᵗ E_0((π_t − π*_t)² + λ(z_t − z*_t)²)`. -/
theorem habit_excess (hpo : 𝔼.PullOut) {β κ δ lam xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hlam : 0 ≤ lam) {x₀ φ₀ : Ω → ℝ} {u π x πs xs φ : ℕ → Ω → ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B)
    (hp : PlanH 𝔼 β κ δ x₀ u π x) (hps : PlanH 𝔼 β κ δ x₀ u πs xs) (hφa : 𝔼.Adapted φ)
    (hφb : BoundedProc φ) (hφ₀ : ∃ C, ∀ ω, |φ₀ ω| ≤ C)
    (hfoc : FOCh κ lam xhat δ x₀ φ₀ πs xs φ)
    (hinit : ∀ ω, φ₀ ω * ((π 0 ω - πs 0 ω) -
      δ * κ * (quasiDiff δ x₀ x 0 ω - quasiDiff δ x₀ xs 0 ω)) = 0) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2 +
        lam * (quasiDiff δ x₀ x t ω - quasiDiff δ x₀ xs t ω) ^ 2) ω)
      (expLossOf 𝔼 β (lossH lam xhat δ x₀ π x) ω -
        expLossOf 𝔼 β (lossH lam xhat δ x₀ πs xs) ω) := by
  obtain ⟨hn, -, hxa, hπb, hxb⟩ := hp
  obtain ⟨hns, -, hxsa, hπsb, hxsb⟩ := hps
  have hzb := quasiDiff_bounded (δ := δ) hx₀ hxb
  have hzsb := quasiDiff_bounded (δ := δ) hx₀ hxsb
  obtain ⟨L, hL⟩ := periodLoss_bounded (xstar := xhat) hlam hπb hzb
  obtain ⟨Ls, hLs⟩ := periodLoss_bounded (xstar := xhat) hlam hπsb hzsb
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨As, hAs⟩ := hπsb
  obtain ⟨Z, hZ⟩ := hzb
  obtain ⟨Zs, hZs⟩ := hzsb
  obtain ⟨F, hF⟩ := hφb
  obtain ⟨C, hC⟩ := hφ₀
  have hlag := lagW_bounded hC hF
  have hK : ∀ t ω, |(lagW φ₀ φ t * ((π t - πs t) - (δ * κ) •
      (quasiDiff δ x₀ x t - quasiDiff δ x₀ xs t))) ω| ≤
      max C F * ((A + As) + |δ * κ| * (Z + Zs)) := fun t ω => by
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, abs_mul]
    refine mul_le_mul (hlag t ω) ((abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (hA t ω) (hAs t ω))) ?_)) (abs_nonneg _)
      ((abs_nonneg _).trans (hlag t ω))
    rw [abs_mul (δ * κ), abs_mul δ κ]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hZ t ω) (hZs t ω)))
      (by positivity)
  refine excess_hasSum 𝔼 hβ0 hβ1 hL hLs (fun t ω => by positivity) hK
    (G := fun t => φ t * 𝔼.E t ((π (t + 1) - πs (t + 1)) - (δ * κ) •
      (quasiDiff δ x₀ x (t + 1) - quasiDiff δ x₀ xs (t + 1)))) (fun t ω => ?_) (fun t => ?_) ?_ ω
  · have n1 := hn t ω
    have n2 := hns t ω
    obtain ⟨f1, f2⟩ := hfoc t ω
    simp only [gH] at f2
    simp only [periodLoss, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      map_sub, map_smul]
    linear_combination 2 * (π t ω - πs t ω) * f1 +
      2 * (quasiDiff δ x₀ x t ω - quasiDiff δ x₀ xs t ω) * f2 - 2 * φ t ω * (n1 - n2)
  · exact E0_pull 𝔼 hpo (hφa t)
  · have : lagW φ₀ φ 0 * ((π 0 - πs 0) - (δ * κ) •
        (quasiDiff δ x₀ x 0 - quasiDiff δ x₀ xs 0)) = 0 := by
      funext ω'
      simp only [lagW_zero, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      rw [← hinit ω']
    rw [this, map_zero]

/-- **Woodford (2003), (2.25)–(2.26) (sufficiency)**: a plan satisfying (2.25)–(2.26) with
bounded adapted multipliers has the smallest expected loss among admissible plans satisfying
the initial constraint. -/
theorem habit_sufficient (hpo : 𝔼.PullOut) {β κ δ lam xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hlam : 0 ≤ lam) {x₀ φ₀ : Ω → ℝ} {u π x πs xs φ : ℕ → Ω → ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B)
    (hp : PlanH 𝔼 β κ δ x₀ u π x) (hps : PlanH 𝔼 β κ δ x₀ u πs xs) (hφa : 𝔼.Adapted φ)
    (hφb : BoundedProc φ) (hφ₀ : ∃ C, ∀ ω, |φ₀ ω| ≤ C)
    (hfoc : FOCh κ lam xhat δ x₀ φ₀ πs xs φ)
    (hinit : ∀ ω, φ₀ ω * ((π 0 ω - πs 0 ω) -
      δ * κ * (quasiDiff δ x₀ x 0 ω - quasiDiff δ x₀ xs 0 ω)) = 0) (ω : Ω) :
    expLossOf 𝔼 β (lossH lam xhat δ x₀ πs xs) ω ≤ expLossOf 𝔼 β (lossH lam xhat δ x₀ π x) ω :=
  expLossOf_le_of_excess 𝔼 hβ0 (fun t ω => by positivity)
    (habit_excess 𝔼 hpo hβ0 hβ1 hlam hx₀ hp hps hφa hφb hφ₀ hfoc hinit ω)

/-- **Woodford (2003), (2.25)–(2.26) (uniqueness)**: an admissible plan with the same expected
loss at `ω` as a plan satisfying the first-order conditions coincides with it in conditional
mean square: inflation, the quasi-differenced gap and the output gap itself. -/
theorem habit_unique (hpo : 𝔼.PullOut) {β κ δ lam xhat B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) {x₀ φ₀ : Ω → ℝ} {u π x πs xs φ : ℕ → Ω → ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B)
    (hp : PlanH 𝔼 β κ δ x₀ u π x) (hps : PlanH 𝔼 β κ δ x₀ u πs xs) (hφa : 𝔼.Adapted φ)
    (hφb : BoundedProc φ) (hφ₀ : ∃ C, ∀ ω, |φ₀ ω| ≤ C)
    (hfoc : FOCh κ lam xhat δ x₀ φ₀ πs xs φ)
    (hinit : ∀ ω, φ₀ ω * ((π 0 ω - πs 0 ω) -
      δ * κ * (quasiDiff δ x₀ x 0 ω - quasiDiff δ x₀ xs 0 ω)) = 0) (ω : Ω)
    (heq : expLossOf 𝔼 β (lossH lam xhat δ x₀ π x) ω =
      expLossOf 𝔼 β (lossH lam xhat δ x₀ πs xs) ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (quasiDiff δ x₀ x t ω - quasiDiff δ x₀ xs t ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 := by
  have hz : ∀ s, 𝔼.E 0 (fun ω => (π s ω - πs s ω) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (quasiDiff δ x₀ x s ω - quasiDiff δ x₀ xs s ω) ^ 2) ω = 0 := fun s =>
    E0_split_zero 𝔼 hlam (fun ω => sq_nonneg _) (fun ω => sq_nonneg _)
      (E0_eq_zero_of_excess 𝔼 hβ0 (fun t ω => by positivity)
        (habit_excess 𝔼 hpo hβ0.le hβ1 hlam.le hx₀ hp hps hφa hφb hφ₀ hfoc hinit ω) heq s)
  refine ⟨(hz t).1, (hz t).2, ?_⟩
  -- `x_t − x*_t = (z_t − z*_t) + δ (x_{t−1} − x*_{t−1})`, by induction
  have key : ∀ s, 𝔼.E 0 (fun ω => (lagW x₀ x s ω - lagW x₀ xs s ω) ^ 2) ω = 0 →
      𝔼.E 0 (fun ω => (x s ω - xs s ω) ^ 2) ω = 0 := by
    intro s hs
    have hle : (fun ω => (x s ω - xs s ω) ^ 2) ≤
        (2 : ℝ) • (fun ω => (quasiDiff δ x₀ x s ω - quasiDiff δ x₀ xs s ω) ^ 2) +
        (2 * δ ^ 2) • (fun ω => (lagW x₀ x s ω - lagW x₀ xs s ω) ^ 2) := fun ω' => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, quasiDiff]
      nlinarith [sq_nonneg (x s ω' - xs s ω' - 2 * δ * (lagW x₀ x s ω' - lagW x₀ xs s ω')),
        sq_nonneg (δ * (lagW x₀ x s ω' - lagW x₀ xs s ω')),
        sq_nonneg (x s ω' - xs s ω' - δ * (lagW x₀ x s ω' - lagW x₀ xs s ω') -
          δ * (lagW x₀ x s ω' - lagW x₀ xs s ω'))]
    have h1 := 𝔼.mono 0 hle ω
    rw [map_add, map_smul, map_smul] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, (hz s).2, hs, mul_zero,
      add_zero] at h1
    exact le_antisymm h1 (E_nonneg 𝔼 (fun ω => sq_nonneg _) 0 ω)
  induction t with
  | zero =>
    refine key 0 ?_
    simp only [lagW_zero, sub_self]
    have : (fun _ : Ω => (0 : ℝ) ^ 2) = 0 := by funext; simp
    rw [this, map_zero]; rfl
  | succ t ih => exact key (t + 1) ih

/-! ### p. 569: the time-invariant multiplier -/

/-- **Woodford (2003), p. 569**: with `x* = x̂*/(1 − δ)` and `d_t = φ_t − (λ/κ)(x_t − x*)`,
`g_t = −κ (d_t − δ d_{t−1})`. -/
theorem g_eq {κ lam xhat δ : ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 1) (x₀ φ₀ : Ω → ℝ) (x φ : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    gH κ lam xhat δ x₀ φ₀ x φ t ω = -κ * ((φ t ω - lam / κ * (x t ω - xhat / (1 - δ))) -
      δ * (lagW φ₀ φ t ω - lam / κ * (lagW x₀ x t ω - xhat / (1 - δ)))) := by
  have h1 : (1 : ℝ) - δ ≠ 0 := sub_ne_zero.2 (Ne.symm hδ)
  simp only [gH, quasiDiff]
  field_simp
  ring

/-- **Woodford (2003), p. 569 (the general solution of (2.26))**: with `x* = x̂*/(1 − δ)`,
(2.26) holds at every date iff `φ_t − (λ/κ)(x_t − x*) = δ^{t+1}(φ_{t₀−1} − (λ/κ)(x_{t₀−1} − x*))`;
the time-invariant identification `φ_t = (λ/κ)(x_t − x*)` corresponds to the self-consistent
initial multiplier. -/
theorem foc226_iff {κ lam xhat δ : ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 1) (x₀ φ₀ : Ω → ℝ)
    (x φ : ℕ → Ω → ℝ) :
    (∀ t ω, gH κ lam xhat δ x₀ φ₀ x φ t ω = 0) ↔
      ∀ t ω, φ t ω - lam / κ * (x t ω - xhat / (1 - δ)) =
        δ ^ (t + 1) * (φ₀ ω - lam / κ * (x₀ ω - xhat / (1 - δ))) := by
  constructor
  · intro h t ω
    induction t with
    | zero =>
      have := h 0 ω
      rw [g_eq hκ hδ] at this
      simp only [lagW_zero] at this
      have h2 := (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 hκ)
      linear_combination h2
    | succ t ih =>
      have := h (t + 1) ω
      rw [g_eq hκ hδ] at this
      simp only [lagW_succ] at this
      have h2 := (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 hκ)
      rw [pow_succ]
      linear_combination h2 + δ * ih
  · intro h t ω
    rw [g_eq hκ hδ]
    cases t with
    | zero => simp only [lagW_zero]; rw [h 0 ω]; ring
    | succ t => simp only [lagW_succ]; rw [h (t + 1) ω, h t ω]; ring

/-- **Woodford (2003), p. 569**: `φ_t = (λ/κ)(x_t − x*)`, `x* = x̂*/(1 − δ)`, with the
self-consistent `φ_{t₀−1} = (λ/κ)(x_{t₀−1} − x*)`, satisfies (2.26) at every date. -/
theorem phi_timeInvariant {κ lam xhat δ : ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 1) (x₀ : Ω → ℝ)
    (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    gH κ lam xhat δ x₀ (fun ω => lam / κ * (x₀ ω - xhat / (1 - δ))) x
      (fun s ω => lam / κ * (x s ω - xhat / (1 - δ))) t ω = 0 := by
  refine (foc226_iff hκ hδ x₀ _ x _).2 (fun t ω => ?_) t ω
  ring

/-! ### (2.27): the target criterion is the baseline one -/

/-- **Woodford (2003), (2.25)–(2.27), p. 569**: a plan satisfying (2.27)
`π_t + (λ/κ)(x_t − x_{t−1}) = 0` satisfies (2.25)–(2.26) with `φ_t = (λ/κ)(x_t − x*)` and the
self-consistent initial multiplier. -/
theorem criterion_foc_habit {κ lam xhat δ : ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 1) {x₀ : Ω → ℝ}
    {π x : ℕ → Ω → ℝ} (h : Criterion (lam / κ) x₀ π x) :
    FOCh κ lam xhat δ x₀ (fun ω => lam / κ * (x₀ ω - xhat / (1 - δ))) π x
      (fun s ω => lam / κ * (x s ω - xhat / (1 - δ))) := by
  intro t ω
  refine ⟨?_, phi_timeInvariant hκ hδ x₀ x t ω⟩
  rw [lagW_affine]
  linear_combination h t ω

/-- **Woodford (2003), (2.25)–(2.27), p. 569 (eliminating the multiplier)**: if a plan satisfies
(2.25)–(2.26) with the self-consistent initial multiplier `φ_{t₀−1} = (λ/κ)(x_{t₀−1} − x*)`, it
satisfies (2.27). -/
theorem foc_imp_criterion_habit {κ lam xhat δ : ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 1) {x₀ : Ω → ℝ}
    {π x φ : ℕ → Ω → ℝ}
    (h : FOCh κ lam xhat δ x₀ (fun ω => lam / κ * (x₀ ω - xhat / (1 - δ))) π x φ) :
    Criterion (lam / κ) x₀ π x := by
  have hφ := (foc226_iff hκ hδ x₀ _ x φ).1 (fun t ω => (h t ω).2)
  have hφ' : ∀ t ω, φ t ω = lam / κ * (x t ω - xhat / (1 - δ)) := fun t ω => by
    have := hφ t ω; simp only [sub_self, mul_zero] at this; linarith
  intro t ω
  have h1 := (h t ω).1
  have hl : lagW (fun ω => lam / κ * (x₀ ω - xhat / (1 - δ))) φ t ω =
      lam / κ * (lagW x₀ x t ω - xhat / (1 - δ)) := by
    cases t with
    | zero => rfl
    | succ t => exact hφ' t ω
  rw [hl, hφ' t ω] at h1
  linear_combination h1

/-- **Woodford (2003), (2.23) + (2.27)**: for an adapted output gap, under the criterion with
`κδ + φ ≠ 0` the aggregate-supply relation (2.23) is the workhorse equation
`β E_t x_{t+1} − (1 + β + c) x_t + x_{t−1} = u_t/(κδ + φ)`,
`c = κ(1 − δ)(1 − βδ)/(κδ + φ)`. -/
theorem as_iff_secondOrder_habit {β κ δ φ : ℝ} (ha : κ * δ + φ ≠ 0) {u π x : ℕ → Ω → ℝ}
    {x₀ : Ω → ℝ} (hxa : 𝔼.Adapted x) (hc : Criterion φ x₀ π x) :
    ASh 𝔼 β κ δ x₀ u π x ↔ SecondOrder 𝔼 β (κ * (1 - δ) * (1 - β * δ) / (κ * δ + φ)) x₀
      (fun t => (κ * δ + φ)⁻¹ • u t) x := by
  have hinv : (κ * δ + φ) * (κ * δ + φ)⁻¹ = 1 := mul_inv_cancel₀ ha
  constructor
  · intro h t ω
    have h1 := h t ω
    have h2 := hc t ω
    rw [E_infl_of_criterion 𝔼 hxa hc, E_quasiDiff 𝔼 hxa] at h1
    simp only [quasiDiff] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (κ * δ + φ)⁻¹ * h1 - (κ * δ + φ)⁻¹ * h2 -
      (β * 𝔼.E t (x (t + 1)) ω + lagW x₀ x t ω - (1 + β) * x t ω) * hinv
  · intro h t ω
    have h3 := h t ω
    have h2 := hc t ω
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    rw [E_infl_of_criterion 𝔼 hxa hc, E_quasiDiff 𝔼 hxa]
    simp only [quasiDiff]
    linear_combination h2 + (κ * δ + φ) * h3 +
      (u t ω + κ * (1 - δ) * (1 - β * δ) * x t ω) * hinv

/-- Woodford (2003), (2.27): the equilibrium output gap under (2.27) with habit persistence,
the workhorse solution for `c = κ(1 − δ)(1 − βδ)/(κδ + φ)` and forcing `u_t/(κδ + φ)`. -/
noncomputable def gapH (β κ δ φ : ℝ) (x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ysol 𝔼 β (κ * (1 - δ) * (1 - β * δ) / (κ * δ + φ)) x₀ (fun t => (κ * δ + φ)⁻¹ • u t)

/-- Woodford (2003), (2.27): equilibrium inflation, `π_t = −φ (x_t − x_{t−1})`. -/
noncomputable def inflH (β κ δ φ : ℝ) (x₀ : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => -φ * (gapH 𝔼 β κ δ φ x₀ u t ω - lagW x₀ (gapH 𝔼 β κ δ φ x₀ u) t ω)

/-- **Woodford (2003), (2.23) + (2.27) (determinacy)**: for `0 < β < 1`, `κ, φ > 0`,
`0 ≤ δ < 1`, every bounded adapted `u` and bounded date-0 `x_{t₀−1}`, (2.23) and (2.27) have
exactly one bounded adapted solution, `(inflH, gapH)`. -/
theorem habitRule_existsUnique {β κ δ φ M B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 < φ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) {x₀ : Ω → ℝ} (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hx₀a : 𝔼.E 0 x₀ = x₀) :
    (PlanH 𝔼 β κ δ x₀ u (inflH 𝔼 β κ δ φ x₀ u) (gapH 𝔼 β κ δ φ x₀ u) ∧
      Criterion φ x₀ (inflH 𝔼 β κ δ φ x₀ u) (gapH 𝔼 β κ δ φ x₀ u)) ∧
    ∀ π x, PlanH 𝔼 β κ δ x₀ u π x → Criterion φ x₀ π x →
      π = inflH 𝔼 β κ δ φ x₀ u ∧ x = gapH 𝔼 β κ δ φ x₀ u := by
  have ha : 0 < κ * δ + φ := by positivity
  have hβδ : 0 < 1 - β * δ := by nlinarith
  have hc : 0 < κ * (1 - δ) * (1 - β * δ) / (κ * δ + φ) := by
    have : 0 < 1 - δ := by linarith
    positivity
  have hfb : ∀ t ω, |(fun t => (κ * δ + φ)⁻¹ • u t) t ω| ≤ (κ * δ + φ)⁻¹ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hu t ω) (inv_nonneg.2 ha.le)
  have hfa : 𝔼.Adapted (fun t => (κ * δ + φ)⁻¹ • u t) := fun t => by
    simp only [map_smul, hua t]
  obtain ⟨⟨hso, hya, ⟨Y, hY⟩⟩, huniq⟩ := secondOrder_existsUnique 𝔼 hβ0 hβ1 hc hfb hfa hx₀ hx₀a
  have hya' : 𝔼.Adapted (gapH 𝔼 β κ δ φ x₀ u) := hya
  have hcrit : Criterion φ x₀ (inflH 𝔼 β κ δ φ x₀ u) (gapH 𝔼 β κ δ φ x₀ u) := fun t ω => by
    simp only [inflH]; ring
  refine ⟨⟨⟨(as_iff_secondOrder_habit 𝔼 ha.ne' hya' hcrit).2 hso,
    diff_adapted 𝔼 (a := -φ) hx₀a hya', hya', diff_bounded hx₀ hY, ⟨Y, hY⟩⟩, hcrit⟩,
    fun π x hp hcr => ?_⟩
  have hx : x = gapH 𝔼 β κ δ φ x₀ u :=
    huniq x ((as_iff_secondOrder_habit 𝔼 ha.ne' hp.2.2.1 hcr).1 hp.1) hp.2.2.1 hp.2.2.2.2
  refine ⟨?_, hx⟩
  funext t ω
  have := hcr t ω
  simp only [inflH, ← hx]
  linarith

/-- **Woodford (2003), (2.27), p. 569 (optimality)**: with `κ > 0`, `0 ≤ δ < 1`, every
admissible plan satisfying `π_t + (λ/κ)(x_t − x_{t−1}) = 0` (bounded date-0 `x_{t₀−1}`) is
optimal from a timeless perspective. -/
theorem habit_timeless (hpo : 𝔼.PullOut) {β κ δ lam xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hlam : 0 ≤ lam) (hκ : κ ≠ 0) (hδ : δ ≠ 1) {x₀ : Ω → ℝ} {u π x : ℕ → Ω → ℝ}
    (hx₀ : ∀ ω, |x₀ ω| ≤ B) (hp : PlanH 𝔼 β κ δ x₀ u π x) (hc : Criterion (lam / κ) x₀ π x) :
    TimelessOptimalH 𝔼 β κ δ lam xhat x₀ u π x := by
  refine ⟨hp, fun π' x' hp' h0 ω => ?_⟩
  refine habit_sufficient 𝔼 hpo hβ0 hβ1 hlam hx₀ hp' hp (affine_adapted 𝔼 _ _ hp.2.2.1)
    (affine_bounded _ _ hp.2.2.2.2)
    ⟨|lam / κ| * (B + |xhat / (1 - δ)|), fun ω => ?_⟩ (criterion_foc_habit hκ hδ hc)
    (fun ω => ?_) ω
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hx₀ ω) le_rfl))
      (abs_nonneg _)
  · have := h0 ω
    rw [show (π' 0 ω - π 0 ω) - δ * κ * (quasiDiff δ x₀ x' 0 ω - quasiDiff δ x₀ x 0 ω) = 0 by
      linarith, mul_zero]

/-- **Woodford (2003), Ch. 8 §1.3 Definition, for (2.23)–(2.24)**: a rule is robustly optimal if
for every bounded adapted `u` and bounded date-0 `x_{t₀−1}` it determines a unique bounded
adapted equilibrium and every equilibrium under it is optimal from a timeless perspective. -/
def RobustlyOptimalH (β κ δ lam xhat : ℝ)
    (Rule : (Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop) : Prop :=
  ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∀ x₀ : Ω → ℝ, (∃ B, ∀ ω, |x₀ ω| ≤ B) →
    𝔼.E 0 x₀ = x₀ →
    (∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), PlanH 𝔼 β κ δ x₀ u p.1 p.2 ∧ Rule x₀ p.1 p.2) ∧
    ∀ π x, PlanH 𝔼 β κ δ x₀ u π x → Rule x₀ π x → TimelessOptimalH 𝔼 β κ δ lam xhat x₀ u π x

/-- **Woodford (2003), (2.27), p. 569 (THE ROBUSTLY OPTIMAL CRITERION WITH HABIT PERSISTENCE,
independent of `η`)**: for `0 < β < 1`, `κ, λ > 0` and EVERY degree of habit persistence
`0 ≤ δ < 1`, the baseline criterion `π_t + (λ/κ)(x_t − x_{t−1}) = 0` — which does not involve
`δ` — is robustly optimal for (2.23)–(2.24). (The book writes `λ_x` in (2.27) for the `λ` of
(2.24).) -/
theorem habit_robustlyOptimal (hpo : 𝔼.PullOut) {β κ δ lam xhat : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    RobustlyOptimalH 𝔼 β κ δ lam xhat (fun x₀ π x => Criterion (lam / κ) x₀ π x) := by
  intro u ⟨M, hM⟩ hua x₀ ⟨B, hB⟩ hx₀a
  obtain ⟨hex, huniq⟩ := habitRule_existsUnique 𝔼 hβ0 hβ1 hκ (div_pos hlam hκ) hδ0 hδ1 hM hua
    hB hx₀a
  refine ⟨⟨(inflH 𝔼 β κ δ (lam / κ) x₀ u, gapH 𝔼 β κ δ (lam / κ) x₀ u), hex, ?_⟩, ?_⟩
  · rintro ⟨π, x⟩ ⟨hp, hc⟩
    obtain ⟨h1, h2⟩ := huniq π x hp hc
    simp [h1, h2]
  · intro π x hp hc
    exact habit_timeless 𝔼 hpo hβ0.le hβ1 hlam.le hκ.ne' hδ1.ne hB hp hc

/-- Woodford (2003), (2.27): the robust optimality holds on every finite event tree (genuine
uncertainty). -/
theorem habit_robustlyOptimal_finiteTree {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {β κ δ lam xhat : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    RobustlyOptimalH T.toExpectationSystem β κ δ lam xhat
      (fun x₀ π x => Criterion (lam / κ) x₀ π x) :=
  habit_robustlyOptimal _ (ExpectationsFiniteTree.finiteTree_pullOut T) hβ0 hβ1 hκ hlam hδ0
    hδ1

/-- **Woodford (2003), (2.27) and (2.5) (habit persistence does not change the criterion)**: the
SAME target criterion is robustly optimal in the baseline model (2.1)–(2.3) and in the
habit-persistence model (2.23)–(2.24) for every `0 ≤ δ < 1`. -/
theorem habit_criterion_eq_baseline (hpo : 𝔼.PullOut) {β κ lam xstar xhat : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    RobustlyOptimal 𝔼 β κ lam xstar (fun x₀ π x => Criterion (lam / κ) x₀ π x) ∧
      ∀ δ, 0 ≤ δ → δ < 1 →
        RobustlyOptimalH 𝔼 β κ δ lam xhat (fun x₀ π x => Criterion (lam / κ) x₀ π x) :=
  ⟨baseline_robustlyOptimal 𝔼 hpo hβ0 hβ1 hκ hlam,
    fun _ hδ0 hδ1 => habit_robustlyOptimal 𝔼 hpo hβ0 hβ1 hκ hlam hδ0 hδ1⟩

end Woodford.OptimalPolicyRules.InflTargetHabit
