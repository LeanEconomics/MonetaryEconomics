/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflTargetStickyWages

/-!
# The exact determinacy region for `κ_w ≠ κ_p` under every expectation system

Woodford (2003), *Interest and Prices*, Chapter 8, §2.2, pp. 565–567, (2.11)–(2.20).

`InflTargetStickyWages.determinacy_iff_stableRoots` proves the exact region (the root condition
`StableRoots`) under perfect foresight only: its "only if" half on the boundary of the ellipse
(`foc_not_exists_boundary`) uses a deterministic resonant cost-push path. This module extends the
whole equivalence to an **arbitrary expectation system** on a nonempty sample space (finite event
trees included, so genuine uncertainty).

The tool is the date-`t₀` forecast path: for any process `y` and any state `ω₀`,
`ŷ_t = E_{t₀} y_t (ω₀)` (`fc`). Every equation of the model and of the first-order conditions is
linear with expectations `E_t`, `t ≥ t₀`, so by the law of iterated expectations
`E_{t₀} E_t = E_{t₀}` the forecast path of a bounded solution is a bounded perfect-foresight
solution with the forecast disturbances (`planSW_fc`, `focSW_fc`). A deterministic disturbance is
its own forecast, so any expectation system that solves every deterministic problem yields a
perfect-foresight solution of it.

## Main results

* `foc_not_exists_boundary_any`: on the ellipse (a factor root `μ` of modulus one) the resonant
  path `u_t = Re μᵗ` has no bounded plan satisfying the first-order conditions, under every
  expectation system on a nonempty sample space.
* `stableRoots_of_exists`: existence of a bounded plan satisfying the first-order conditions for
  every bounded adapted disturbance and every pair of initial multipliers forces `StableRoots`.
* `determinacy_iff_stableRoots_any`, `determinate_iff_stableRoots_any`: the exact region (existence
  for all data; existence and uniqueness for all data) under every expectation system.
* `criterion_determinacy_iff_stableRoots_any`: the same for commitment to the corrected target
  criterion (2.20) from `t₀`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bStickyBoundary

open InflTargetInertia InflTargetStickyWages

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Forecast paths -/

/-- Woodford (2003), §2.2, p. 566 (date-`t₀` forecasts): the forecast path
`ŷ_t = E_{t₀} y_t (ω₀)` of a process `y` at the state `ω₀`, as a perfect-foresight process. -/
noncomputable def fc (ω0 : Ω) (y : ℕ → Ω → ℝ) : ℕ → Unit → ℝ :=
  fun t _ => 𝔼.E 0 (y t) ω0

/-- Woodford (2003), §2.2: the forecast path of a bounded process is bounded. -/
theorem fc_bounded (ω0 : Ω) {y : ℕ → Ω → ℝ} (hy : BoundedProc y) : BoundedProc (fc 𝔼 ω0 y) := by
  obtain ⟨M, hM⟩ := hy
  exact ⟨M, fun t _ => 𝔼.abs_E_le (hM t) 0 ω0⟩

/-- Woodford (2003), §2.2: a deterministic process is its own forecast path. -/
theorem fc_const (ω0 : Ω) (g : ℕ → Unit → ℝ) : fc 𝔼 ω0 (fun t _ => g t ()) = g := by
  funext t ω
  cases ω
  simp only [fc, 𝔼.const]

/-- Woodford (2003), §2.2: the forecast path of a lag with a constant initial value is the lag of
the forecast path. -/
theorem fc_lagW (ω0 : Ω) (c : ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.E 0 (lagW (fun _ => c) y t) ω0 = lagW (fun _ => c) (fc 𝔼 ω0 y) t () := by
  cases t with
  | zero => simp only [lagW_zero, 𝔼.const]
  | succ t => rfl

/-- Woodford (2003), (2.11)–(2.13) (the law of iterated expectations): the forecast path of a
bounded plan of (2.11)–(2.13) (constant `w_{t₀−1}`) is a bounded perfect-foresight plan for the
forecast disturbances. -/
theorem planSW_fc (P : SW) (ω0 : Ω) (c : ℝ) {u wn π πw x w : ℕ → Ω → ℝ}
    (hp : PlanSW 𝔼 P (fun _ => c) u wn π πw x w) :
    PlanSW perfectForesight P (fun _ => c) (fc 𝔼 ω0 u) (fc 𝔼 ω0 wn) (fc 𝔼 ω0 π) (fc 𝔼 ω0 πw)
      (fc 𝔼 ω0 x) (fc 𝔼 ω0 w) := by
  obtain ⟨h1, h2, h3, -, -, -, -, hπb, hπwb, hxb, hwb⟩ := hp
  refine ⟨fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fc_bounded 𝔼 ω0 hπb, fc_bounded 𝔼 ω0 hπwb, fc_bounded 𝔼 ω0 hxb,
    fc_bounded 𝔼 ω0 hwb⟩
  · have h : π t = P.kp • (x t + u t) + P.xip • (w t - wn t) + P.beta • 𝔼.E t (π (t + 1)) :=
      funext fun ω => h1 t ω
    have e := congrArg (fun f => 𝔼.E 0 f ω0) h
    simp only [map_add, map_smul, map_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, 𝔼.tower (Nat.zero_le t)] at e
    exact e
  · have h : πw t = P.kw • (x t + u t) + P.xiw • (wn t - w t) + P.beta • 𝔼.E t (πw (t + 1)) :=
      funext fun ω => h2 t ω
    have e := congrArg (fun f => 𝔼.E 0 f ω0) h
    simp only [map_add, map_smul, map_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, 𝔼.tower (Nat.zero_le t)] at e
    exact e
  · have h : w t = lagW (fun _ => c) w t + πw t - π t := funext fun ω => h3 t ω
    have e := congrArg (fun f => 𝔼.E 0 f ω0) h
    simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply] at e
    rw [fc_lagW] at e
    exact e

/-- Woodford (2003), (2.16)–(2.19) (the law of iterated expectations): the forecast paths of a
plan and of multipliers satisfying the first-order conditions (constant initial multipliers)
satisfy the perfect-foresight first-order conditions. -/
theorem focSW_fc (P : SW) (ω0 : Ω) (a b : ℝ) {π πw x mp mw ups : ℕ → Ω → ℝ}
    (hf : FOCsw 𝔼 P (fun _ => a) (fun _ => b) π πw x mp mw ups) :
    FOCsw perfectForesight P (fun _ => a) (fun _ => b) (fc 𝔼 ω0 π) (fc 𝔼 ω0 πw) (fc 𝔼 ω0 x)
      (fc 𝔼 ω0 mp) (fc 𝔼 ω0 mw) (fc 𝔼 ω0 ups) := by
  intro t _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : P.lp • π t + mp t - lagW (fun _ => a) mp t + ups t = 0 :=
      funext fun ω => (hf t ω).1
    have e := congrArg (fun f => 𝔼.E 0 f ω0) h
    simp only [map_add, map_smul, map_sub, map_zero, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      Pi.zero_apply, smul_eq_mul] at e
    rw [fc_lagW] at e
    exact e
  · have h : P.lw • πw t + mw t - lagW (fun _ => b) mw t - ups t = 0 :=
      funext fun ω => (hf t ω).2.1
    have e := congrArg (fun f => 𝔼.E 0 f ω0) h
    simp only [map_add, map_smul, map_sub, map_zero, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      Pi.zero_apply, smul_eq_mul] at e
    rw [fc_lagW] at e
    exact e
  · have h : P.lx • (x t - fun _ => P.xstar) - P.kp • mp t - P.kw • mw t = 0 :=
      funext fun ω => (hf t ω).2.2.1
    have e := congrArg (fun f => 𝔼.E 0 f ω0) h
    simp only [map_smul, map_sub, map_zero, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply,
      smul_eq_mul, 𝔼.const] at e
    exact e
  · have h : ups t = P.xip • mp t - P.xiw • mw t + P.beta • 𝔼.E t (ups (t + 1)) :=
      funext fun ω => (hf t ω).2.2.2
    have e := congrArg (fun f => 𝔼.E 0 f ω0) h
    simp only [map_add, map_smul, map_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, 𝔼.tower (Nat.zero_le t)] at e
    exact e

/-! ### The boundary of the root condition under every expectation system -/

/-- **Woodford (2003), (2.16)–(2.19), `κ_w ≠ κ_p` (FAILURE ON THE BOUNDARY OF THE ROOT
CONDITION, every expectation system)**: if a root `Z₁` of `P` has a factor root `μ` on the unit
circle, then under ANY expectation system on a nonempty sample space the bounded cost-push path
`u_t = Re μᵗ` (with `w^n = 0`) has no bounded plan satisfying the first-order conditions (zero
predetermined values): the date-`t₀` forecast path would be a perfect-foresight one
(`InflTargetStickyWages.foc_not_exists_boundary`). -/
theorem foc_not_exists_boundary_any [Nonempty Ω] {P : SW} (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp)
    (hkw : 0 < P.kw) (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) {Z1 Z2 Z3 : ℂ}
    (hv1 : Z1 + Z2 + Z3 = ((-(cp2 P / P.lx) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((cp1 P / P.lx : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(cp0 P / P.lx) : ℝ) : ℂ)) {μ : ℂ}
    (hr : (P.beta : ℂ) * μ ^ 2 - (1 + P.beta - Z1) * μ + 1 = 0) (hμ1 : ‖μ‖ = 1) :
    ¬ ∃ π πw x w mp mw ups, PlanSW 𝔼 P (fun _ => 0) (fun t _ => (μ ^ t).re) (fun _ _ => 0)
      π πw x w ∧ FOCsw 𝔼 P (fun _ => 0) (fun _ => 0) π πw x mp mw ups := by
  rintro ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩
  set ω0 : Ω := Classical.arbitrary Ω
  apply foc_not_exists_boundary hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hv1 hv2 hv3 hr hμ1
  refine ⟨fc 𝔼 ω0 π, fc 𝔼 ω0 πw, fc 𝔼 ω0 x, fc 𝔼 ω0 w, fc 𝔼 ω0 mp, fc 𝔼 ω0 mw, fc 𝔼 ω0 ups,
    ?_, focSW_fc 𝔼 P ω0 0 0 hf⟩
  have hu := fc_const 𝔼 ω0 (fun t _ => (μ ^ t).re)
  have hw := fc_const 𝔼 ω0 (fun _ _ => (0 : ℝ))
  have e := planSW_fc 𝔼 P ω0 0 hp
  rw [hu, hw] at e
  exact e

/-- **Woodford (2003), §2.2, `κ_w ≠ κ_p` (THE "ONLY IF" HALF, every expectation system)**: if,
under an expectation system on a nonempty sample space, a bounded plan satisfying the first-order
conditions exists for every bounded adapted disturbance and every pair of constant initial
multipliers (`w_{t₀−1} = 0`), then the root condition `StableRoots P` holds. Deterministic data
are adapted, and the forecast path of the solution solves the perfect-foresight problem, so
`InflTargetStickyWages.determinacy_iff_stableRoots` applies. -/
theorem stableRoots_of_exists [Nonempty Ω] {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp)
    (h : ∀ u wn : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → BoundedProc wn → 𝔼.Adapted wn →
      ∀ a b : ℝ, ∃ π πw x w mp mw ups, PlanSW 𝔼 P (fun _ => 0) u wn π πw x w ∧
        FOCsw 𝔼 P (fun _ => a) (fun _ => b) π πw x mp mw ups) :
    StableRoots P := by
  set ω0 : Ω := Classical.arbitrary Ω
  refine (determinacy_iff_stableRoots hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne).1 ?_
  intro u wn hu hwn a b
  obtain ⟨Mu, hMu⟩ := hu
  obtain ⟨Mw, hMw⟩ := hwn
  obtain ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩ := h (fun t _ => u t ()) (fun t _ => wn t ())
    ⟨Mu, fun t _ => hMu t ()⟩ (fun t => 𝔼.const t (u t ())) ⟨Mw, fun t _ => hMw t ()⟩
    (fun t => 𝔼.const t (wn t ())) a b
  refine ⟨fc 𝔼 ω0 π, fc 𝔼 ω0 πw, fc 𝔼 ω0 x, fc 𝔼 ω0 w, fc 𝔼 ω0 mp, fc 𝔼 ω0 mw, fc 𝔼 ω0 ups,
    ?_, focSW_fc 𝔼 P ω0 a b hf⟩
  have e := planSW_fc 𝔼 P ω0 0 hp
  rw [fc_const, fc_const] at e
  exact e

/-- **Woodford (2003), §2.2, `κ_w ≠ κ_p` (THE EXACT REGION, every expectation system)**: with all
parameters positive and `κ_w ≠ κ_p`, under any expectation system on a nonempty sample space, a
bounded plan satisfying the first-order conditions exists for every bounded adapted disturbance
process and every pair of constant initial multipliers (`w_{t₀−1} = 0`) if and only if
`StableRoots P` (every root of `P` strictly outside the ellipse `ellForm β Z ≤ 1`). This extends
`InflTargetStickyWages.determinacy_iff_stableRoots` from perfect foresight. -/
theorem determinacy_iff_stableRoots_any [Nonempty Ω] {P : SW} (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp)
    (hkw : 0 < P.kw) (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) :
    (∀ u wn : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → BoundedProc wn → 𝔼.Adapted wn →
      ∀ a b : ℝ, ∃ π πw x w mp mw ups, PlanSW 𝔼 P (fun _ => 0) u wn π πw x w ∧
        FOCsw 𝔼 P (fun _ => a) (fun _ => b) π πw x mp mw ups) ↔ StableRoots P := by
  refine ⟨stableRoots_of_exists 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne, ?_⟩
  intro hR u wn hu hua hwn hwna a b
  obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hf, -⟩, -⟩ := foc_existsUnique 𝔼 hβ0 hβ1 hlx hlp hlw
    hkp hkw hxip hxiw hne hR hu hua hwn hwna (w₀ := fun _ => 0) (mp₀ := fun _ => a)
    (mw₀ := fun _ => b) ⟨0, fun _ => by simp⟩ ⟨|a|, fun _ => le_rfl⟩ ⟨|b|, fun _ => le_rfl⟩
    (𝔼.const 0 0) (𝔼.const 0 a) (𝔼.const 0 b)
  exact ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩

/-- **Woodford (2003), §2.2, `κ_w ≠ κ_p` (DETERMINACY, every expectation system)**: under any
expectation system on a nonempty sample space, for every bounded adapted disturbance process and
every pair of constant initial multipliers there is EXACTLY ONE bounded plan with adapted
multipliers satisfying the first-order conditions if and only if `StableRoots P`. -/
theorem determinate_iff_stableRoots_any [Nonempty Ω] {P : SW} (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp)
    (hkw : 0 < P.kw) (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) :
    (∀ u wn : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → BoundedProc wn → 𝔼.Adapted wn →
      ∀ a b : ℝ, ∃ π πw x w mp mw ups, (PlanSW 𝔼 P (fun _ => 0) u wn π πw x w ∧
        FOCsw 𝔼 P (fun _ => a) (fun _ => b) π πw x mp mw ups ∧ 𝔼.Adapted mp ∧ 𝔼.Adapted mw) ∧
        ∀ π' πw' x' w' mp' mw' ups', PlanSW 𝔼 P (fun _ => 0) u wn π' πw' x' w' →
          FOCsw 𝔼 P (fun _ => a) (fun _ => b) π' πw' x' mp' mw' ups' → 𝔼.Adapted mp' →
          𝔼.Adapted mw' → BoundedProc ups' →
          π' = π ∧ πw' = πw ∧ x' = x ∧ w' = w ∧ mp' = mp ∧ mw' = mw ∧ ups' = ups) ↔
      StableRoots P := by
  constructor
  · intro h
    refine stableRoots_of_exists 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne ?_
    intro u wn hu hua hwn hwna a b
    obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hf, -⟩, -⟩ := h u wn hu hua hwn hwna a b
    exact ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩
  · intro hR u wn hu hua hwn hwna a b
    obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hf, hmpa, hmwa, -⟩, huniq⟩ := foc_existsUnique 𝔼 hβ0
      hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR hu hua hwn hwna (w₀ := fun _ => 0)
      (mp₀ := fun _ => a) (mw₀ := fun _ => b) ⟨0, fun _ => by simp⟩ ⟨|a|, fun _ => le_rfl⟩
      ⟨|b|, fun _ => le_rfl⟩ (𝔼.const 0 0) (𝔼.const 0 a) (𝔼.const 0 b)
    exact ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hf, hmpa, hmwa⟩, huniq⟩

/-- **Woodford (2003), (2.20) corrected, `κ_w ≠ κ_p` (THE EXACT REGION FOR THE TARGET CRITERION,
every expectation system)**: under any expectation system on a nonempty sample space, commitment
from `t₀` to the corrected criterion (dates `t > t₀` and the date-`t₀` condition with constant
predetermined `x_{t₀−1}`, `e₀`) determines a bounded equilibrium for every bounded adapted
disturbance process if and only if `StableRoots P`; in the region it is unique
(`InflTargetStickyWages.criterion_existsUnique`). -/
theorem criterion_determinacy_iff_stableRoots_any [Nonempty Ω] {P : SW} (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp)
    (hkw : 0 < P.kw) (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) :
    (∀ u wn : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → BoundedProc wn → 𝔼.Adapted wn →
      ∀ x₀ e₀ : ℝ, ∃ π πw x w, PlanSW 𝔼 P (fun _ => 0) u wn π πw x w ∧
        CriterionC 𝔼 P (fun _ => x₀) π πw x ∧
        ∀ ω, critC0 𝔼 P (fun _ => x₀) (fun _ => e₀) π πw x ω = 0) ↔ StableRoots P := by
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD : P.kp * P.xiw + P.kw * P.xip ≠ 0 := by positivity
  constructor
  · intro h
    refine stableRoots_of_exists 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne ?_
    intro u wn hu hua hwn hwna a b
    obtain ⟨π, πw, x, w, hp, hcr, h0⟩ := h u wn hu hua hwn hwna
      ((P.kp * a + P.kw * b) / P.lx + P.xstar) (-((P.kw - P.kp) * (P.xip * a - P.xiw * b)))
    obtain ⟨mp, mw, ups, hfoc, -, -, -⟩ := criterion_imp_foc 𝔼 hkp hkw hxip hxiw hne
      (B := |(P.kp * a + P.kw * b) / P.lx + P.xstar|) (fun _ => le_rfl) (𝔼.const 0 _) hp hcr h0
    have e1 : (fun ω : Ω => (P.xiw * (P.lx * ((fun _ => (P.kp * a + P.kw * b) / P.lx +
        P.xstar) ω - P.xstar)) + P.kw * (-(fun _ => -((P.kw - P.kp) * (P.xip * a -
        P.xiw * b))) ω / (P.kw - P.kp))) / (P.kp * P.xiw + P.kw * P.xip)) = fun _ => a := by
      funext ω; field_simp; ring
    have e2 : (fun ω : Ω => (P.xip * (P.lx * ((fun _ => (P.kp * a + P.kw * b) / P.lx +
        P.xstar) ω - P.xstar)) - P.kp * (-(fun _ => -((P.kw - P.kp) * (P.xip * a -
        P.xiw * b))) ω / (P.kw - P.kp))) / (P.kp * P.xiw + P.kw * P.xip)) = fun _ => b := by
      funext ω; field_simp; ring
    rw [e1, e2] at hfoc
    exact ⟨π, πw, x, w, mp, mw, ups, hp, hfoc⟩
  · intro hR u wn hu hua hwn hwna x₀ e₀
    obtain ⟨π, πw, x, w, h, -⟩ := criterion_existsUnique 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip
      hxiw hne hR hu hua hwn hwna (w₀ := fun _ => 0) (x₀ := fun _ => x₀) (e₀ := fun _ => e₀)
      ⟨0, fun _ => by simp⟩ ⟨|x₀|, fun _ => le_rfl⟩ ⟨|e₀|, fun _ => le_rfl⟩ (𝔼.const 0 0)
      (𝔼.const 0 x₀) (𝔼.const 0 e₀)
    exact ⟨π, πw, x, w, h⟩

/-- Woodford (2003), §2.2, `κ_w ≠ κ_p`, under genuine uncertainty: on every finite event tree
(here instantiated through any expectation system on a nonempty sample space, which includes the
finite trees of `ExpectationsFiniteTree.finiteTree_pullOut`), outside the root condition some
bounded adapted disturbance and constant initial multipliers have no bounded plan satisfying the
first-order conditions. -/
theorem not_exists_of_not_stableRoots [Nonempty Ω] {P : SW} (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp)
    (hkw : 0 < P.kw) (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp)
    (hR : ¬ StableRoots P) :
    ∃ u wn : ℕ → Ω → ℝ, BoundedProc u ∧ 𝔼.Adapted u ∧ BoundedProc wn ∧ 𝔼.Adapted wn ∧
      ∃ a b : ℝ, ¬ ∃ π πw x w mp mw ups, PlanSW 𝔼 P (fun _ => 0) u wn π πw x w ∧
        FOCsw 𝔼 P (fun _ => a) (fun _ => b) π πw x mp mw ups := by
  by_contra hc
  push Not at hc
  exact hR ((determinacy_iff_stableRoots_any 𝔼 hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne).1
    fun u wn hu hua hwn hwna a b => hc u wn hu hua hwn hwna a b)

end Woodford.OptimalPolicyRules.TidyR5bStickyBoundary
