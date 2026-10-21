/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.Equivalence

/-!
# Non-identification of the equilibrium-selection parameters

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, p. 496 ("without
additional identifying assumptions, the parameters that separate regimes such as `γ` and `φ` are
not identified"), §22.3, pp. 500–502 ((22.7)–(22.11) and the discussion of the regressions
(22.4)–(22.5) and of disturbance restrictions), and Chapter 16, §16.5, pp. 370–372 (the
reverse-engineering argument).

## Main results

* NI-1: `eqmSet_eq_singleton`, `eqmSet_const_on_determinate`, `statistic_independent`: on the
  determinate set the set of admissible equilibria is the same singleton for every `(φ, γ)`, so
  every statistic of the observables (any likelihood) is constant in `(φ, γ)`;
  `target_mem_eqmSet`: the observed path is an admissible equilibrium for *every* `(φ, γ)`;
  `not_identified`: no function of the observed path recovers `(φ, γ)`.
* NI-2 (`θ` vs `φ`): `eqm_rate_theta` (`i_t = θπ_t + u_{i,t}` holds identically in equilibrium,
  whatever `φ`), `coef_from_moment` and `regression_identifies_theta` (a population moment
  condition recovers `θ`), `spec_forces_phi_eq_theta` (the specification `i_t = φπ_t + u_{i,t}`
  imposes `φ = θ`), `stationary_iff` (`|θ| < 1` is exactly the condition for inflation
  `π_{t+1} = θπ_t + w_t` to stay bounded for all bounded inputs), `thetaTarget`,
  `theta_target_unique` (any `|θ| < 1` combines with any `|φ| > 1`).
* NI-3 (`α` vs `γ`): `eqm_surplus_alpha`, `regression_identifies_alpha`,
  `spec_forces_gamma_eq_alpha`.
* Reverse engineering (§16.5, p. 371): `reverse_engineer_rule`, `reverse_engineer_leeper`,
  `rev_disturbances_differ`: any path obeying the Fisher equation and the flow condition is an
  equilibrium of the Leeper model for every `(φ, γ)`, with disturbances `u_i = i − φπ`,
  `u_{s,t+1} = s̃_{t+1} − γ v_t`.
* Disturbance restrictions (p. 502): `sshape_two_ways`, `leeper_sshape_two_ways` (a surplus
  response may come from `α > 0` with uncorrelated shocks or from `α = 0` with an s-shaped
  disturbance); the explicit impulse response `irfV`, `irfS`: `irf_flow`, `irf_surplus`,
  `irf_sshape` (positive on impact, negative afterwards for `0 < α < 1`) and `irf_pv_zero`
  (its present value is zero for `0 < α < 2`, so it moves no inflation).
-/

namespace Cochrane.ObservationalEquivalence.NonIdentification

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.FiscalRec Cochrane.ObservationalEquivalence.Equivalence

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §22.1, p. 496: the set of admissible equilibria of the `(φ, γ)` system. -/
def EqmSet (ρ φ γ : ℝ) (tg : Outcome Ω) : Set (Outcome Ω) :=
  {x | Eqm 𝔼 ρ φ γ tg x ∧ Admissible 𝔼 ρ x}

/-! ### NI-1 -/

/-- Cochrane (2023), §22.1, p. 496 (NI-1): on the determinate set the admissible equilibria are
exactly the target. -/
theorem eqmSet_eq_singleton {ρ φ γ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) : EqmSet 𝔼 ρ φ γ tg = {tg} := by
  ext x
  refine ⟨fun hx => unique_of_determinate 𝔼 hρ h hc htg x hx.1 hx.2, fun hx => ?_⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨starred_eqm 𝔼 φ γ hc, htg⟩

/-- Cochrane (2023), §22.1, p. 496 (NI-1, "the parameters that separate regimes such as `γ` and
`φ` are not identified"): the set of admissible equilibria is the same for all determinate
`(φ, γ)`. -/
theorem eqmSet_const_on_determinate {ρ φ₁ γ₁ φ₂ γ₂ : ℝ} (hρ : ρ ≠ 0) (h₁ : Determinate φ₁ γ₁)
    (h₂ : Determinate φ₂ γ₂) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : EqmSet 𝔼 ρ φ₁ γ₁ tg = EqmSet 𝔼 ρ φ₂ γ₂ tg := by
  rw [eqmSet_eq_singleton 𝔼 hρ h₁ hc htg, eqmSet_eq_singleton 𝔼 hρ h₂ hc htg]

/-- Cochrane (2023), §22.1, p. 496, and §16.5, p. 371 ("the likelihood function does not involve
`φ`"): any statistic `F` of the observed equilibrium path — a likelihood, a regression
coefficient, an impulse response — takes the same value for all determinate `(φ, γ)`. -/
theorem statistic_independent {X : Type*} (F : Outcome Ω → X) {ρ φ₁ γ₁ φ₂ γ₂ : ℝ} (hρ : ρ ≠ 0)
    (h₁ : Determinate φ₁ γ₁) (h₂ : Determinate φ₂ γ₂) {tg x₁ x₂ : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg) (hx₁ : x₁ ∈ EqmSet 𝔼 ρ φ₁ γ₁ tg)
    (hx₂ : x₂ ∈ EqmSet 𝔼 ρ φ₂ γ₂ tg) : F x₁ = F x₂ := by
  rw [eqmSet_eq_singleton 𝔼 hρ h₁ hc htg, Set.mem_singleton_iff] at hx₁
  rw [eqmSet_eq_singleton 𝔼 hρ h₂ hc htg, Set.mem_singleton_iff] at hx₂
  rw [hx₁, hx₂]

/-- Cochrane (2023), §22.1, p. 496 ("the equilibrium conditions are the same in each regime"):
the observed target path is an admissible equilibrium for every `(φ, γ)` whatsoever, so no value
of `(φ, γ)` is rejected by the data. -/
theorem target_mem_eqmSet {ρ : ℝ} (φ γ : ℝ) {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) : tg ∈ EqmSet 𝔼 ρ φ γ tg :=
  ⟨starred_eqm 𝔼 φ γ hc, htg⟩

/-- Cochrane (2023), §22.1, p. 496 (non-identification, formally): there is no estimator — no
function of the observed path — that returns `(φ, γ)` whenever the path is an admissible
equilibrium of the `(φ, γ)` system. -/
theorem not_identified {ρ : ℝ} {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) :
    ¬ ∃ est : Outcome Ω → ℝ × ℝ, ∀ φ γ x, x ∈ EqmSet 𝔼 ρ φ γ tg → est x = (φ, γ) := by
  rintro ⟨est, hest⟩
  have h1 := hest 2 0 tg (target_mem_eqmSet 𝔼 2 0 hc htg)
  have h2 := hest 3 0 tg (target_mem_eqmSet 𝔼 3 0 hc htg)
  rw [h1] at h2
  have := congrArg Prod.fst h2
  norm_num at this

/-! ### NI-2: `θ` versus `φ` -/

/-- Cochrane (2023), (22.7)–(22.8), p. 501 (NI-2): in every admissible equilibrium of a
determinate system with `i*_t = θπ*_t + u_{i,t}`, the observed rule is `i_t = θπ_t + u_{i,t}`
identically; `φ` does not appear. -/
theorem eqm_rate_theta {ρ φ γ θ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg x : Outcome Ω}
    {ui : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg)
    (hθ : ThetaRule θ tg.pi ui tg.i) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) :
    x.i t = θ • x.pi t + ui t := by
  rw [eqmSet_eq_singleton 𝔼 hρ h hc htg, Set.mem_singleton_iff] at hx
  rw [hx, hθ t]

omit 𝔼 in
/-- Cochrane (2023), p. 501 ("the interest-rate policy rule parameter `θ` can, in principle, be
measured"): with a population moment `m` (any linear functional, e.g. an unconditional
expectation), if `y = b x + u` with `m(u x) = 0` and `m(x²) ≠ 0`, then
`b = m(y x)/m(x²)` — the population regression coefficient. -/
theorem coef_from_moment (m : (Ω → ℝ) →ₗ[ℝ] ℝ) {y x u : Ω → ℝ} {b : ℝ} (h : y = b • x + u)
    (horth : m (u * x) = 0) (hvar : m (x * x) ≠ 0) : b = m (y * x) / m (x * x) := by
  have e : y * x = b • (x * x) + u * x := by
    rw [h]
    funext ω
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, map_add, map_smul, horth, add_zero, smul_eq_mul, mul_div_cancel_right₀ _ hvar]

/-- Cochrane (2023), p. 501 (NI-2): in a determinate equilibrium, regressing `i_t` on `π_t` with
a disturbance orthogonal to inflation recovers `θ` — never `φ`. -/
theorem regression_identifies_theta (m : (Ω → ℝ) →ₗ[ℝ] ℝ) {ρ φ γ θ : ℝ} (hρ : ρ ≠ 0)
    (h : Determinate φ γ) {tg x : Outcome Ω} {ui : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) (hθ : ThetaRule θ tg.pi ui tg.i) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg)
    (t : ℕ) (horth : m (ui t * x.pi t) = 0) (hvar : m (x.pi t * x.pi t) ≠ 0) :
    θ = m (x.i t * x.pi t) / m (x.pi t * x.pi t) :=
  coef_from_moment m (eqm_rate_theta 𝔼 hρ h hc htg hθ hx t) horth hvar

omit 𝔼 in
/-- Cochrane (2023), p. 501 ("the specification `i_t = φπ_t + u_{i,t}` thus adds an implicit
assumption, `φ = θ`"): if both `i_t = θπ_t + u_{i,t}` and `i_t = φπ_t + u_{i,t}` hold with the
same disturbance and `π_t` is not identically zero, then `φ = θ`. -/
theorem spec_forces_phi_eq_theta {θ φ : ℝ} {i π u : Ω → ℝ} (h1 : i = θ • π + u)
    (h2 : i = φ • π + u) {ω : Ω} (hω : π ω ≠ 0) : φ = θ := by
  have := congrFun (h1.symm.trans h2) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at this
  exact (mul_right_cancel₀ hω this).symm

/-- Cochrane (2023), (22.7)–(22.8), p. 501: in a determinate equilibrium inflation follows
`E_t π_{t+1} = θπ_t + u_{i,t}`. -/
theorem eqm_inflation_theta {ρ φ γ θ : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg x : Outcome Ω}
    {ui : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg)
    (hθ : ThetaRule θ tg.pi ui tg.i) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) :
    𝔼.E t (x.pi (t + 1)) = θ • x.pi t + ui t := by
  rw [← hx.1.1 t, eqm_rate_theta 𝔼 hρ h hc htg hθ hx t]

/-- Cochrane (2023), p. 501 ("we should have `θ < 1` if we wish stationary solutions"; survey
error E12: `|θ| < 1`): the inflation recursion `π_{t+1} = θπ_t + w_t` keeps inflation bounded for
every bounded input and bounded start iff `|θ| < 1`. -/
theorem stationary_iff [Nonempty Ω] (θ : ℝ) :
    (∀ w π : ℕ → Ω → ℝ, BoundedProc w → (∃ B, ∀ ω, |π 0 ω| ≤ B) →
      (∀ t, π (t + 1) = θ • π t + w t) → BoundedProc π) ↔ |θ| < 1 := by
  constructor
  · intro h
    by_contra hθ
    have h1 : 1 ≤ |θ| := not_lt.mp hθ
    set w : ℕ → Ω → ℝ := fun t _ => 1 * (if 0 ≤ θ then (1 : ℝ) else -1) ^ (t + 1) with hw
    have hwb : BoundedProc w := ⟨1, fun t ω => by
      simp only [hw, one_mul, abs_pow]
      split_ifs <;> norm_num⟩
    obtain ⟨M, hM⟩ := h w (dRec θ w 0) hwb ⟨0, fun ω => by simp [dRec]⟩ (fun t => rfl)
    have hgrow := rec_unbounded h1 zero_le_one (d := dRec θ w 0) (fun t => rfl) rfl
    obtain ⟨n, hn⟩ := exists_nat_gt M
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := hgrow n ω
    have := hM n ω
    linarith
  · rintro hθ w π ⟨K, hK⟩ ⟨B, hB⟩ hπ
    exact ⟨|B| + |K| / (1 - |θ|), rec_bounded hθ (abs_nonneg B) (abs_nonneg K)
      (fun t ω => (hK t ω).trans (le_abs_self K)) hπ (fun ω => (hB ω).trans (le_abs_self B))⟩

/-- Cochrane (2023), (22.8), p. 501: a target built from an interest-rate rule with coefficient
`θ`: `π*_0 = 0`, `π*_{t+1} = θπ*_t + u_{i,t}`, `i*_t = θπ*_t + u_{i,t}`, with debt and surplus
targets zero. -/
noncomputable def thetaTarget (θ : ℝ) (ui : ℕ → Ω → ℝ) : Outcome Ω where
  pi := dRec θ ui 0
  i := fun t => θ • dRec θ ui 0 t + ui t
  v := 0
  s := 0

/-- Cochrane (2023), (22.8), p. 501: the `θ`-target is consistent and, for `|θ| < 1` and bounded
adapted `u_i`, admissible. -/
theorem thetaTarget_ok {ρ θ : ℝ} (hθ : |θ| < 1) {ui : ℕ → Ω → ℝ} (hua : 𝔼.Adapted ui)
    (hub : BoundedProc ui) : Consistent 𝔼 ρ (thetaTarget θ ui) ∧
      Admissible 𝔼 ρ (thetaTarget θ ui) ∧ ThetaRule θ (thetaTarget θ ui).pi ui
        (thetaTarget θ ui).i := by
  have hpa : 𝔼.Adapted (dRec θ ui 0) := dRec_adapted (γ := θ) (b0 := 0) 𝔼 hua
  obtain ⟨K, hK⟩ := hub
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, ⟨hpa, fun t => by simp [thetaTarget], ?_, fun t ω => ?_⟩,
    fun t => rfl⟩
  · change θ • dRec θ ui 0 t + ui t = 𝔼.E t (θ • dRec θ ui 0 t + ui t)
    rw [map_add, map_smul, hpa t, hua t]
  · change ρ • (0 : Ω → ℝ) = 0 + (θ • dRec θ ui 0 t + ui t) - (θ • dRec θ ui 0 t + ui t) - 0
    simp
  · exact ⟨0 + |K| / (1 - |θ|), rec_bounded hθ le_rfl (abs_nonneg K)
      (fun t ω => (hK t ω).trans (le_abs_self K)) (fun t => rfl) (fun ω => by
        change |dRec θ ui 0 0 ω| ≤ 0
        simp [dRec])⟩
  · simp [thetaTarget]

/-- Cochrane (2023), p. 501 ("the parameters `θ` and `φ` have distinct economic functions … there
is no reason the parameters should be the same"): for every `|θ| < 1` (stationary inflation)
and every `|φ| > 1` (determinacy), the `θ`-target is the unique admissible equilibrium, and in it
`i_t = θπ_t + u_{i,t}`. -/
theorem theta_target_unique {ρ θ φ γ : ℝ} (hρ : ρ ≠ 0) (hθ : |θ| < 1) (hφ : 1 < |φ|)
    {ui : ℕ → Ω → ℝ} (hua : 𝔼.Adapted ui) (hub : BoundedProc ui) :
    UniqueEqm 𝔼 ρ φ γ (thetaTarget θ ui) ∧
      ∀ t, (thetaTarget θ ui).i t = θ • (thetaTarget θ ui).pi t + ui t := by
  obtain ⟨hc, htg, hth⟩ := thetaTarget_ok (ρ := ρ) 𝔼 hθ hua hub
  exact ⟨unique_of_active_money 𝔼 hρ hφ hc htg, hth⟩

/-! ### NI-3: `α` versus `γ` -/

/-- Cochrane (2023), (22.9), p. 501 (NI-3): in every admissible equilibrium of a determinate
system with `s̃*_{t+1} = α v*_t + u_{s,t+1}`, the observed surplus obeys
`s̃_{t+1} = α v_t + u_{s,t+1}` identically; `γ` does not appear. -/
theorem eqm_surplus_alpha {ρ φ γ α : ℝ} (hρ : ρ ≠ 0) (h : Determinate φ γ) {tg x : Outcome Ω}
    {us : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg) (htg : Admissible 𝔼 ρ tg)
    (hα : StarredSurplus α tg.v us tg.s) (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) :
    x.s (t + 1) = α • x.v t + us (t + 1) := by
  rw [eqmSet_eq_singleton 𝔼 hρ h hc htg, Set.mem_singleton_iff] at hx
  rw [hx, hα t]

/-- Cochrane (2023), p. 501 (NI-3): regressing `s̃_{t+1}` on `v_t` with a disturbance orthogonal
to debt recovers `α` — never `γ`. -/
theorem regression_identifies_alpha (m : (Ω → ℝ) →ₗ[ℝ] ℝ) {ρ φ γ α : ℝ} (hρ : ρ ≠ 0)
    (h : Determinate φ γ) {tg x : Outcome Ω} {us : ℕ → Ω → ℝ} (hc : Consistent 𝔼 ρ tg)
    (htg : Admissible 𝔼 ρ tg) (hα : StarredSurplus α tg.v us tg.s)
    (hx : x ∈ EqmSet 𝔼 ρ φ γ tg) (t : ℕ) (horth : m (us (t + 1) * x.v t) = 0)
    (hvar : m (x.v t * x.v t) ≠ 0) : α = m (x.s (t + 1) * x.v t) / m (x.v t * x.v t) :=
  coef_from_moment m (eqm_surplus_alpha 𝔼 hρ h hc htg hα hx t) horth hvar

omit 𝔼 in
/-- Cochrane (2023), p. 501 ("the identifying assumption in (22.5) `s_{t+1} = γ v_t + u_{s,t+1}`
is `α = γ`"): if both `s̃_{t+1} = α v_t + u_{s,t+1}` and `s̃_{t+1} = γ v_t + u_{s,t+1}` hold
with the same disturbance and `v_t` is not identically zero, then `γ = α`. -/
theorem spec_forces_gamma_eq_alpha {α γ : ℝ} {s v u : Ω → ℝ} (h1 : s = α • v + u)
    (h2 : s = γ • v + u) {ω : Ω} (hω : v ω ≠ 0) : γ = α :=
  spec_forces_phi_eq_theta h1 h2 hω

/-! ### Reverse engineering (§16.5, p. 371) -/

/-- Cochrane (2023), §16.5, p. 371 ("Choose any process `{π_t}`. … Choose any `φ`. Construct
`u_t = i_t − φπ_t`"): for any inflation process and any `φ`, with `i_t = E_t π_{t+1}` and
`u_t := i_t − φπ_t`, the Fisher equation and the rule `i_t = φπ_t + u_t` hold. -/
theorem reverse_engineer_rule (π : ℕ → Ω → ℝ) (φ : ℝ) :
    Fisher 𝔼 (fun t => 𝔼.E t (π (t + 1))) π ∧
      ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + (𝔼.E t (π (t + 1)) - φ • π t) :=
  ⟨fun _ => rfl, fun t => by abel⟩

/-- Cochrane (2023), §16.5, p. 371: the reverse-engineered monetary disturbance
`u_{i,t} = i_t − φπ_t`. -/
def revUi (φ : ℝ) (x : Outcome Ω) : ℕ → Ω → ℝ := fun t => x.i t - φ • x.pi t

/-- Cochrane (2023), §22.3, p. 502: the reverse-engineered fiscal disturbance
`u_{s,t+1} = s̃_{t+1} − γ v_t` (`u_{s,0} = s̃_0`). -/
def revUs (γ : ℝ) (x : Outcome Ω) : ℕ → Ω → ℝ
  | 0 => x.s 0
  | t + 1 => x.s (t + 1) - γ • x.v t

/-- Cochrane (2023), §16.5, p. 371, and §22.3, p. 500 (the regressions (22.4)–(22.5) "estimate
`φ` or `γ` only under restrictions"): any path obeying the Fisher equation and the flow condition
is an equilibrium of the Leeper model (22.3)–(22.6) for every `(φ, γ)`, with the
reverse-engineered disturbances. -/
theorem reverse_engineer_leeper {ρ : ℝ} {x : Outcome Ω} (hF : Fisher 𝔼 x.i x.pi)
    (hflow : Flow ρ x.v x.i x.pi x.s) (φ γ : ℝ) :
    LeeperEqm 𝔼 ρ φ γ (revUi φ x) (revUs γ x) (ρ • x.v 0 + x.pi 0) x := by
  refine ⟨hF, fun t => ?_, rfl, fun t => ?_, hflow, rfl⟩
  · simp only [revUi]; abel
  · simp only [revUs]; abel

omit 𝔼 in
/-- Cochrane (2023), §16.5, p. 371 ("these parameters and variables always appear together, so
there are different combinations of `φ`, `u_t` … which give the same time series"): changing
`φ` changes the reverse-engineered disturbance by `(φ₂ − φ₁) π_t`. -/
theorem rev_disturbances_differ (φ₁ φ₂ : ℝ) (x : Outcome Ω) (t : ℕ) :
    revUi φ₁ x t - revUi φ₂ x t = (φ₂ - φ₁) • x.pi t := by
  simp only [revUi, sub_smul]
  abel

/-! ### Disturbance restrictions and the s-shaped surplus (p. 502) -/

omit 𝔼 in
/-- Cochrane (2023), p. 502 ("the surplus process can have an s-shaped response by virtue of
`α > 0` … or by virtue of an s-shaped `{u_{s,t+1}}` process with `α = 0`"): any starred surplus
`s̃*_{t+1} = α v*_t + u_{s,t+1}` is also `s̃*_{t+1} = α' v*_t + u'_{s,t+1}` for every `α'`, with
`u'_{s,t+1} = s̃*_{t+1} − α' v*_t`; the equilibrium set depends only on `s̃*`. -/
theorem sshape_two_ways {vS sS : ℕ → Ω → ℝ} (α' : ℝ) :
    StarredSurplus α' vS (fun t => sS t - α' • lag vS t) sS := by
  intro t
  simp only [lag]
  abel

/-- Cochrane (2023), p. 502 (the Leeper form): an equilibrium of (22.3)–(22.6) with fiscal
coefficient `γ` and disturbance `u_s` is the same path as an equilibrium with `γ' = 0` and
disturbance `u'_{s,t+1} = γ v_t + u_{s,t+1}`. -/
theorem leeper_sshape_two_ways {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) :
    LeeperEqm 𝔼 ρ φ 0 ui (revUs 0 x) K x := by
  obtain ⟨hF, hm, -, -, hflow, h0⟩ := hx
  refine ⟨hF, hm, rfl, fun t => ?_, hflow, h0⟩
  simp only [revUs, zero_smul, sub_zero, zero_add]

/-- Cochrane (2023), p. 502 (an explicit s-shaped response): real debt after a unit surplus
disturbance at date 1 with no inflation surprise, `v_0 = 0`, `v_{t+1} = −ρ⁻¹((1 − α)/ρ)ᵗ`. -/
noncomputable def irfV (α ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => -ρ⁻¹ * ((1 - α) / ρ) ^ t

/-- Cochrane (2023), p. 502: the surplus response, `s̃_1 = 1` and `s̃_{t+2} = α v_{t+1}`. -/
noncomputable def irfS (α ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | t + 2 => α * irfV α ρ (t + 1)

/-- Cochrane (2023), p. 502: a unit surplus disturbance at date 1. -/
def impulse (t : ℕ) : ℝ := if t = 1 then 1 else 0

/-- Cochrane (2023), (22.10), p. 501, with no inflation surprise: the response obeys the flow
condition `ρ v_{t+1} = v_t − s̃_{t+1}`. -/
theorem irf_flow {α ρ : ℝ} (hρ : ρ ≠ 0) (t : ℕ) :
    ρ * irfV α ρ (t + 1) = irfV α ρ t - irfS α ρ (t + 1) := by
  rcases t with _ | t
  · simp [irfV, irfS, hρ]
  · simp only [irfV, irfS]
    have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ
    simp only [div_eq_mul_inv]
    rw [pow_succ]
    linear_combination (-(((1 - α) * ρ⁻¹) ^ t * ((1 - α) * ρ⁻¹))) * h1

/-- Cochrane (2023), (22.9), p. 501: the response is generated by `s̃_{t+1} = α v_t + u_{s,t+1}`
with the unit impulse `u_{s,1} = 1` — and equally by `α' = 0` with `u'_s = s̃` itself. -/
theorem irf_surplus (α ρ : ℝ) (t : ℕ) :
    irfS α ρ (t + 1) = α * irfV α ρ t + impulse (t + 1) ∧
      irfS α ρ (t + 1) = 0 * irfV α ρ t + irfS α ρ (t + 1) := by
  refine ⟨?_, by ring⟩
  rcases t with _ | t
  · simp [irfS, irfV, impulse]
  · simp [irfS, impulse]

/-- Cochrane (2023), p. 502 (the s-shape): for `0 < α < 1` and `ρ > 0` the surplus is positive
on impact and negative at every later date. -/
theorem irf_sshape {α ρ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) :
    irfS α ρ 1 = 1 ∧ ∀ t, irfS α ρ (t + 2) < 0 := by
  refine ⟨rfl, fun t => ?_⟩
  simp only [irfS, irfV]
  have h1 : 0 < ((1 - α) / ρ) ^ t := pow_pos (div_pos (by linarith) hρ) t
  have h2 : 0 < ρ⁻¹ := inv_pos.mpr hρ
  nlinarith [mul_pos h2 h1]

/-- Cochrane (2023), p. 502, and §4.2 (`a(ρ) = 0`): for `0 < α < 2` the present value of the
surplus response is zero, `∑_{j ≥ 0} ρʲ s̃_{1+j} = 0`, so the disturbance moves no inflation. -/
theorem irf_pv_zero {α ρ : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hρ : ρ ≠ 0) :
    HasSum (fun j => ρ ^ j * irfS α ρ (j + 1)) 0 := by
  have hq : |1 - α| < 1 := (abs_one_sub_lt_one_iff α).mpr ⟨hα0, hα2⟩
  have hg : HasSum (fun j : ℕ => -α * (1 - α) ^ j) (-α * (1 - (1 - α))⁻¹) :=
    (hasSum_geometric_of_abs_lt_one hq).mul_left (-α)
  have hval : -α * (1 - (1 - α))⁻¹ = 0 - ρ ^ 0 * irfS α ρ (0 + 1) := by
    rw [sub_sub_cancel, neg_mul, mul_inv_cancel₀ hα0.ne']
    simp [irfS]
  rw [hval] at hg
  have hshift : (fun j : ℕ => -α * (1 - α) ^ j) =
      fun j => ρ ^ (j + 1) * irfS α ρ (j + 1 + 1) := by
    funext j
    simp only [irfS, irfV]
    rw [pow_succ, div_pow]
    field_simp
  rw [hshift] at hg
  refine (hasSum_nat_add_iff' (f := fun j => ρ ^ j * irfS α ρ (j + 1)) 1).mp ?_
  rw [Finset.sum_range_one]
  exact hg

end Cochrane.ObservationalEquivalence.NonIdentification
