/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.SimplestModel

/-!
# Inflation targets and equilibrium selection: King's form of the rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.2 "Inflation targets and
equilibrium selection", eqs. (16.12)–(16.14), pp. 366–368, and the `*`-notation statement of
§16.4, p. 369.

King's (2000) form of the policy rule is `i_t = i*_t + φ(π_t − π*_t)` (16.12) with the
interest-rate target `i*_t = E_t π*_{t+1}`. It translates into the standard form
`i_t = φ π_t + u_t` by `u_t = E_t π*_{t+1} − φ π*_t` (16.13), and back (for `|φ| > 1` and bounded
processes) by `π*_t = −∑ φ^{−(j+1)} E_t u_{t+j}`. With (16.1) the equilibrium condition becomes
`E_t(π_{t+1} − π*_{t+1}) = φ(π_t − π*_t)` (16.14): for `|φ| > 1` the only bounded equilibrium is
`π = π*`, for any target process, so the central bank can achieve any bounded adapted inflation
path. Interest-rate policy `i*` sets expected inflation; equilibrium-selection policy `φ` sets
unexpected inflation. In the fiscal theory the same rate path with the fiscal shock
`ε_{Σs} = −ΔE π*` gives the same inflation.

## Main results

* (16.12)–(16.13): `KingRule`, `toU`, `kingRule_iff`, `kingModel_iff_nk`, `toU_bounded`,
  `toU_adapted`.
* The translation is a bijection: `fwdSol_toU`, `toU_fwdSol`, `translation_bijOn` (bounded adapted
  targets ↔ bounded adapted disturbances, for `|φ| > 1`).
* (16.14): `eq1614_iff`, `target_solves`, `eq_target_of_bounded` (the only bounded equilibrium is
  `π = π*`, for any disturbance process), `deviation_expected` (§16.4,
  `E_t(π_{t+j} − π*_{t+j}) = φʲ(π_t − π*_t)`), `deviation_explodes`.
* p. 367: `any_target_attainable` (every bounded adapted `π*` is the unique bounded equilibrium
  of the rule with `u = toU φ π*`), `eqm_rate_eq_target` (`i_t = i*_t` in equilibrium),
  `expected_set_by_rate`, `unexpected_set_by_selection`; `thetaRule_iff` (the rule with
  `i*_t = θ π*_t + u_t` is a standard rule with disturbance `(θ − φ)π*_t + u_t`).
* p. 367 (comparison with the fiscal theory): `ftpl_same_inflation`.
-/

namespace Cochrane.NewKeynesianSelection.KingForm

open Filter Topology Innovation SimplestModel

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (16.12)–(16.13) -/

/-- Cochrane (2023), eq. (16.12), p. 366: King's form of the rule,
`i_t = i*_t + φ(π_t − π*_t)` with the interest-rate target `i*_t = E_t π*_{t+1}`. -/
def KingRule (φ : ℝ) (pistar i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (pistar (t + 1)) + φ • (π t - pistar t)

/-- Cochrane (2023), eq. (16.13), p. 366: the translation
`u_t = i*_t − φπ*_t = E_t π*_{t+1} − φπ*_t` into the disturbance of the standard form (16.2). -/
def toU (φ : ℝ) (pistar : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => 𝔼.E t (pistar (t + 1)) - φ • pistar t

/-- Cochrane (2023), eqs. (16.12)–(16.13), p. 366 ("This form of the policy rule is equivalent to
(16.2)"): King's rule holds iff `i_t = φπ_t + u_t` with `u` from (16.13). -/
theorem kingRule_iff {φ : ℝ} {pistar i π : ℕ → Ω → ℝ} :
    KingRule 𝔼 φ pistar i π ↔ ∀ t, i t = φ • π t + toU 𝔼 φ pistar t := by
  refine forall_congr' fun t => ?_
  rw [toU, smul_sub]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), eqs. (16.1), (16.12)–(16.13), p. 366: the Fisher equation with King's rule
is the simplest new-Keynesian model with the disturbance (16.13). -/
theorem kingModel_iff_nk {φ : ℝ} {pistar i π : ℕ → Ω → ℝ} :
    ((∀ t, i t = 𝔼.E t (π (t + 1))) ∧ KingRule 𝔼 φ pistar i π) ↔
      NKModel 𝔼 φ (toU 𝔼 φ pistar) i π := by
  rw [kingRule_iff]
  constructor
  · rintro ⟨h1, h2⟩ t
    exact ⟨h1 t, h2 t⟩
  · intro h
    exact ⟨fun t => (h t).1, fun t => (h t).2⟩

/-- Cochrane (2023), eq. (16.13), p. 366: a bounded target gives a bounded disturbance. -/
theorem toU_bounded {φ : ℝ} {pistar : ℕ → Ω → ℝ} (h : BoundedProc pistar) :
    BoundedProc (toU 𝔼 φ pistar) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M + |φ| * M, fun t ω => ?_⟩
  simp only [toU, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hM (t + 1)) t ω) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg φ)

/-- Cochrane (2023), eq. (16.13), p. 366: an adapted target gives an adapted disturbance. -/
theorem toU_adapted {φ : ℝ} {pistar : ℕ → Ω → ℝ} (h : 𝔼.Adapted pistar) :
    𝔼.Adapted (toU 𝔼 φ pistar) := fun t => by
  simp only [toU, map_sub, map_smul, 𝔼.E_E_self, h t]

/-! ### (16.14) -/

/-- Cochrane (2023), eq. (16.14), p. 367: with the disturbance (16.13), the equilibrium condition
(16.4) is `E_t(π_{t+1} − π*_{t+1}) = φ(π_t − π*_t)`. -/
theorem eq1614_iff {φ : ℝ} {pistar π : ℕ → Ω → ℝ} :
    Eq164 𝔼 φ (toU 𝔼 φ pistar) π ↔
      ∀ t, 𝔼.E t (π (t + 1) - pistar (t + 1)) = φ • (π t - pistar t) := by
  refine forall_congr' fun t => ?_
  rw [toU, map_sub, smul_sub, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (16.14), p. 367: the target itself is an equilibrium of (16.4) with the
disturbance (16.13). -/
theorem target_solves (φ : ℝ) (pistar : ℕ → Ω → ℝ) : Eq164 𝔼 φ (toU 𝔼 φ pistar) pistar :=
  (eq1614_iff 𝔼).mpr fun t => by rw [sub_self, sub_self, map_zero, smul_zero]

/-- Cochrane (2023), eq. (16.14), p. 367 ("If the central bank follows `φ > 1`, the only
nonexplosive equilibrium is `π_t = π*_t`. We reach this conclusion quickly, for any process of
the monetary policy disturbance, not just an AR(1)"): for `|φ| > 1` and any bounded adapted target,
every bounded equilibrium equals the target. -/
theorem eq_target_of_bounded {φ : ℝ} (hφ : 1 < |φ|) {pistar π : ℕ → Ω → ℝ}
    (hb : BoundedProc pistar) (ha : 𝔼.Adapted pistar) (hπb : BoundedProc π)
    (h : ∀ t, 𝔼.E t (π (t + 1) - pistar (t + 1)) = φ • (π t - pistar t)) : π = pistar := by
  obtain ⟨M, hM⟩ := toU_bounded 𝔼 (φ := φ) hb
  obtain ⟨-, -, -, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM (toU_adapted 𝔼 ha)
  exact (huniq π ((eq1614_iff 𝔼).mpr h) hπb).trans
    (huniq pistar (target_solves 𝔼 φ pistar) hb).symm

/-- Cochrane (2023), §16.4, p. 369 ("In `*` notation, the central bank deliberately makes
inflation diverge away from its target, `E_t(π_{t+1} − π*_{t+1}) = φ(π_t − π*_t)`"): in every
equilibrium, `E_t(π_{t+j} − π*_{t+j}) = φʲ(π_t − π*_t)`. -/
theorem deviation_expected {φ : ℝ} {pistar π : ℕ → Ω → ℝ} (ha : 𝔼.Adapted pistar)
    (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ (toU 𝔼 φ pistar) π) (t j : ℕ) :
    𝔼.E t (π (t + j) - pistar (t + j)) = φ ^ j • (π t - pistar t) := by
  rw [map_sub]
  exact sunspot_expected 𝔼 ha hπ (target_solves 𝔼 φ pistar) h t j

/-- Cochrane (2023), §16.2, p. 367 ("announces a threat to hyperinflate or deflate for any other
value of inflation"): for `|φ| > 1`, wherever inflation is off target the expected deviation
explodes, `|E_t(π_{t+j} − π*_{t+j})| → ∞`. -/
theorem deviation_explodes {φ : ℝ} (hφ : 1 < |φ|) {pistar π : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted pistar) (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ (toU 𝔼 φ pistar) π) {t : ℕ}
    {ω : Ω} (hω : π t ω ≠ pistar t ω) :
    Tendsto (fun j => |𝔼.E t (π (t + j) - pistar (t + j)) ω|) atTop atTop := by
  have e : (fun j => |𝔼.E t (π (t + j) - pistar (t + j)) ω|) =
      fun j => |φ| ^ j * |π t ω - pistar t ω| := by
    funext j
    rw [deviation_expected 𝔼 ha hπ h t j, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul,
      abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const
    (abs_pos.mpr (sub_ne_zero.mpr hω))

/-! ### The translation is a bijection -/

/-- Cochrane (2023), p. 367 ("going in the other direction, `π*_t = −∑ φ^{−(j+1)} E_t u_{t+j}`"):
for `|φ| > 1` and a bounded adapted target, the forward solution of the translated disturbance
recovers the target. -/
theorem fwdSol_toU {φ : ℝ} (hφ : 1 < |φ|) {pistar : ℕ → Ω → ℝ} (hb : BoundedProc pistar)
    (ha : 𝔼.Adapted pistar) : fwdSol 𝔼 φ (toU 𝔼 φ pistar) = pistar :=
  (eq_target_of_bounded 𝔼 hφ hb ha
    (fwdSol_existsUnique 𝔼 hφ (toU_bounded 𝔼 hb).choose_spec (toU_adapted 𝔼 ha)).2.1
    ((eq1614_iff 𝔼).mp
      (fwdSol_existsUnique 𝔼 hφ (toU_bounded 𝔼 hb).choose_spec (toU_adapted 𝔼 ha)).1))

/-- Cochrane (2023), eq. (16.13), p. 366–367 (`i*_t = E_t π*_{t+1}` and `u_t = i*_t − φ π*_t`):
for `|φ| > 1` and a bounded adapted disturbance, translating the forward solution back gives the
disturbance. -/
theorem toU_fwdSol {φ M : ℝ} (hφ : 1 < |φ|) {u : ℕ → Ω → ℝ} (hM : ∀ t ω, |u t ω| ≤ M)
    (hu : 𝔼.Adapted u) : toU 𝔼 φ (fwdSol 𝔼 φ u) = u := by
  obtain ⟨hs, -, -, -⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
  funext t
  rw [toU, hs t]
  abel

/-- Cochrane (2023), p. 367 ("The `i*_t`, `π*_t` notation is just a different way of writing the
disturbance term `u_t`"): for `|φ| > 1` the translation (16.13) is a bijection from bounded
adapted targets onto bounded adapted disturbances, with inverse the forward solution. -/
theorem translation_bijOn {φ : ℝ} (hφ : 1 < |φ|) :
    Set.BijOn (toU 𝔼 φ) {p : ℕ → Ω → ℝ | BoundedProc p ∧ 𝔼.Adapted p}
      {u : ℕ → Ω → ℝ | BoundedProc u ∧ 𝔼.Adapted u} := by
  refine ⟨fun p hp => ⟨toU_bounded 𝔼 hp.1, toU_adapted 𝔼 hp.2⟩, fun p hp q hq hpq => ?_,
    fun u hu => ?_⟩
  · rw [← fwdSol_toU 𝔼 hφ hp.1 hp.2, ← fwdSol_toU 𝔼 hφ hq.1 hq.2, hpq]
  · obtain ⟨⟨M, hM⟩, ha⟩ := hu
    obtain ⟨-, hb, hfa, -⟩ := fwdSol_existsUnique 𝔼 hφ hM ha
    exact ⟨fwdSol 𝔼 φ u, ⟨hb, hfa⟩, toU_fwdSol 𝔼 hφ hM ha⟩

/-! ### Any target is attainable -/

/-- Cochrane (2023), p. 367 ("the central bank can achieve any value of inflation it wishes in
this model"): for `|φ| > 1` and every bounded adapted target `π*`, the rule with disturbance
`u = toU φ π*` has exactly one bounded equilibrium, and it is `π*`. -/
theorem any_target_attainable {φ : ℝ} (hφ : 1 < |φ|) {pistar : ℕ → Ω → ℝ}
    (hb : BoundedProc pistar) (ha : 𝔼.Adapted pistar) :
    ∃! π, BoundedProc π ∧ Eq164 𝔼 φ (toU 𝔼 φ pistar) π := by
  refine ⟨pistar, ⟨hb, target_solves 𝔼 φ pistar⟩, fun π hπ => ?_⟩
  exact eq_target_of_bounded 𝔼 hφ hb ha hπ.1 ((eq1614_iff 𝔼).mp hπ.2)

/-- Cochrane (2023), p. 367 ("Interest-rate policy sets the path of interest rates which we
observe in equilibrium `i_t = i*_t`"): at the target equilibrium the rule gives `i_t = i*_t`. -/
theorem eqm_rate_eq_target {φ : ℝ} {pistar i : ℕ → Ω → ℝ} (h : KingRule 𝔼 φ pistar i pistar)
    (t : ℕ) : i t = 𝔼.E t (pistar (t + 1)) := by
  rw [h t, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 367 ("and sets expected inflation via `i_t = E_t π_{t+1}`"): in every
equilibrium `E_t π_{t+1} = i*_t + φ(π_t − π*_t)`, which is `i*_t` at the target equilibrium. -/
theorem expected_set_by_rate {φ : ℝ} {pistar i π : ℕ → Ω → ℝ}
    (hf : ∀ t, i t = 𝔼.E t (π (t + 1))) (h : KingRule 𝔼 φ pistar i π) (t : ℕ) :
    𝔼.E t (π (t + 1)) = 𝔼.E t (pistar (t + 1)) + φ • (π t - pistar t) := by
  rw [← hf t, h t]

/-- Cochrane (2023), p. 367 ("Equilibrium-selection policy `φ(π_t − π*_t)` ... sets unexpected
inflation in this model"): at the selected equilibrium unexpected inflation is that of the
target, `ΔE_{t+1} π_{t+1} = ΔE_{t+1} π*_{t+1}`, and for `|φ| > 1` the selected equilibrium is the
only bounded one (`eq_target_of_bounded`). -/
theorem unexpected_set_by_selection {φ : ℝ} (hφ : 1 < |φ|) {pistar π : ℕ → Ω → ℝ}
    (hb : BoundedProc pistar) (ha : 𝔼.Adapted pistar) (hπb : BoundedProc π)
    (h : Eq164 𝔼 φ (toU 𝔼 φ pistar) π) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = innov 𝔼 t (pistar (t + 1)) := by
  rw [eq_target_of_bounded 𝔼 hφ hb ha hπb ((eq1614_iff 𝔼).mp h)]

/-- Cochrane (2023), p. 367 ("Interest-rate policy can include rules, such as
`i*_t = θπ*_t + u_t`. Then the full monetary policy rule is `i_t = θπ*_t + u_t + φ(π_t − π*_t)`.
Again, we are just pulling more out of the disturbance term"): this rule is the standard form
`i_t = φπ_t + ũ_t` with `ũ_t = (θ − φ)π*_t + u_t`. -/
theorem thetaRule_iff {θ φ : ℝ} {pistar u i π : ℕ → Ω → ℝ} :
    (∀ t, i t = θ • pistar t + u t + φ • (π t - pistar t)) ↔
      ∀ t, i t = φ • π t + ((θ - φ) • pistar t + u t) := by
  refine forall_congr' fun t => ?_
  rw [smul_sub, sub_smul]
  constructor <;> intro h <;> rw [h] <;> abel

/-! ### Comparison with the fiscal theory (p. 367) -/

/-- Cochrane (2023), p. 367 ("The central bank determines the observed interest rate `i_t = i*_t`
in both cases ... In fiscal theory, shocks to the present value of surpluses determine
unexpected inflation"): in the fiscal-theory peg model with the rate path `i*_t = E_t π*_{t+1}`
and the fiscal shock `ε_{Σs,t+1} = −ΔE_{t+1} π*_{t+1}`, the unique equilibrium with `π_0 = π*_0`
is the target `π*`; no boundedness or `φ` is needed. -/
theorem ftpl_same_inflation {pistar : ℕ → Ω → ℝ} (ha : 𝔼.Adapted pistar) :
    ∃! π, 𝔼.Adapted π ∧ π 0 = pistar 0 ∧
      FTPLSimple.PegModel 𝔼 (fun t => 𝔼.E t (pistar (t + 1))) (FTPLSimple.passiveShock 𝔼 pistar)
        π := by
  have hi : 𝔼.Adapted (fun t => 𝔼.E t (pistar (t + 1))) := fun t => 𝔼.E_E_self t _
  obtain ⟨π, hπ, huniq⟩ :=
    FTPLSimple.peg_existsUnique 𝔼 (ha 0) hi (FTPLSimple.passiveShock_isShock 𝔼 pistar)
  have htarget : 𝔼.Adapted pistar ∧ pistar 0 = pistar 0 ∧
      FTPLSimple.PegModel 𝔼 (fun t => 𝔼.E t (pistar (t + 1)))
        (FTPLSimple.passiveShock 𝔼 pistar) pistar :=
    ⟨ha, rfl, FTPLSimple.passive_valuation_holds 𝔼 fun _ => rfl⟩
  exact ⟨pistar, htarget, fun q hq => (huniq q hq).trans (huniq pistar htarget).symm⟩

end Cochrane.NewKeynesianSelection.KingForm
