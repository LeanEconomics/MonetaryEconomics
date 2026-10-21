/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.SurplusProcess
import StickyPriceFiscal.ExpectationsFiniteTree

/-!
# A debt target, and active vs. passive fiscal policy

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.4.1, eqs. (5.29)–(5.42),
pp. 137–140, and §5.4.4, p. 146. All results hold for an arbitrary `ExpectationSystem`;
counterexamples use the coin-flip tree of `ExpectationsFiniteTree`.

## Main results

* The model (5.29)–(5.34) `VStarModel`; (5.35) `diff_535`, `diff_p136`, `diff_forward`.
* Selection of `v = v*`, `ΔE π = −β_s ε`: `select_bounded` (`|ρ| < 1`, bounded debt),
  `select_tvc` (any `ρ`, transversality conditions), `select` (`v*` satisfies its TVC
  automatically); `exists_equilibrium`, `unique_equilibrium`; survey E32:
  `rho_one_counterexample` (at `ρ = 1` a bounded solution with `v ≠ v*` exists).
* (5.39)–(5.41): `Reduced`, `reduced_of_model`, `model_of_reduced`; the printed debt equation
  of (5.41) has the wrong sign on `β_s ε` (`printed_541_sign`).
* (5.36)–(5.37): `GammaRule`, `gamma_rec`, `gamma_tvc`, `gamma_exists`, `gamma_passive`:
  every unexpected inflation is an equilibrium for `0 < γ < 2`; `gamma_passive_iff` (exactly
  `0 < γ < 2`, survey of Ch. 11–19 E6); `gamma_bounded`, `gamma_unbounded` (bounded debt needs
  `1 − ρ < γ < 1 + ρ`, survey E54); `e10_actual_debt_rule_passive` (survey E10).
* (5.38), survey E33: `tvc_v_iff_538` (`ρᵀ E_t v_{t+T} → (α − γ)(v_t − v*_t)/α`),
  `active_538` (`γ ≠ α` ⇒ active), `passive_538` (`γ = α` ⇒ passive), `active_iff_538`
  (active iff `γ ≠ α`), `printed_538_false` ("active iff γ = 0" is false).
* (5.42), observational equivalence: `Target`, `ActiveMoney`, `modelA_target`, `modelA_unique`,
  `modelA_phi_unique`, `modelB_target`, `modelB_passive`, `modelB_unique`,
  `observationally_equivalent`.
* Survey E31 (stationarity of `v*`): `vstar_bounded`, `vstar_unbounded`, `vstar_discounted`,
  `vstar_discounted_fails`.
* §5.4.4: `ar1_surplus_inflation` (`ΔE π = −ε/(1 − ρη)`; sign error E38, `printed_e38_false`),
  `au_rho`, `scaled_inflation_increasing`, `scaled_unexpected_inflation`.
-/

namespace Cochrane.StickyPriceFiscal.ActivePassive

open Filter Topology SurplusProcess
open SharedTools (TVC bounded_of_rec summable_of_rec tendsto_zero_of_rec)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### A scalar recursion lemma -/

/-- Cochrane (2023), pp. 137–138: if `ρ y_{j+1} = c y_j + b κ^{j+1}` with `|c| < 1` and
`|ρκ| < 1`, the discounted sequence `ρʲ y_j` is absolutely summable (hence tends to zero). -/
theorem summable_disc {ρ c b κ : ℝ} (hc : |c| < 1) (hκ : |ρ * κ| < 1) {y : ℕ → ℝ}
    (hrec : ∀ j, ρ * y (j + 1) = c * y j + b * κ ^ (j + 1)) :
    Summable (fun j => ρ ^ j * y j) := by
  refine summable_of_rec hc ((summable_geometric_of_abs_lt_one hκ).mul_left (b * κ))
    (fun j => ?_)
  rw [pow_succ, mul_assoc, hrec j, mul_pow, pow_succ]
  ring

/-! ### The v*/π* model (5.29)–(5.34) -/

/-- Cochrane (2023), eqs. (5.29)–(5.34), p. 137: `i_t = E_t π_{t+1}`,
`s̃_{t+1} = α v*_t + u_{t+1}`, `ρ v*_{t+1} = v*_t − ΔE_{t+1} π*_{t+1} − s̃_{t+1}`,
`ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s̃_{t+1}`, `ΔE_{t+1} π*_{t+1} = −β_s ε_{t+1}`,
`u_{t+1} = η u_t + ε_{t+1}`. -/
def VStarModel (ρ α βs η : ℝ) (ε i π πs s v vs u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ s (t + 1) = α • vs t + u (t + 1) ∧
    ρ • vs (t + 1) = vs t - surprise 𝔼 πs t - s (t + 1) ∧
    ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) ∧
    surprise 𝔼 πs t = -(βs • ε (t + 1)) ∧ u (t + 1) = η • u t + ε (t + 1)

variable {ρ α βs η γ : ℝ} {ε i π πs s v vs u : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 137: (5.30), (5.31), (5.33), (5.34) are the surplus process
(5.22)–(5.24). -/
theorem VStarModel.surplusProc (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) :
    IsSurplusProc ρ α βs η ε s vs u := fun t => by
  obtain ⟨-, h2, h3, -, h5, h6⟩ := h t
  refine ⟨h2, ?_, h6⟩
  rw [h3, h5]
  abel

/-- Cochrane (2023), p. 137: (5.29) and (5.32) are the frictionless model of (5.27). -/
theorem VStarModel.frictionless (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) :
    Frictionless 𝔼 ρ i π s v := fun t => by
  obtain ⟨h1, -, -, h4, -, -⟩ := h t
  refine ⟨h1, ?_⟩
  rw [h4, surprise, ← h1]
  abel

/-- Cochrane (2023), p. 137: differencing (5.31) and (5.32),
`ρ (v_{t+1} − v*_{t+1}) = (v_t − v*_t) − (ΔE_{t+1} π_{t+1} − ΔE_{t+1} π*_{t+1})`. -/
theorem diff_rho (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (t : ℕ) :
    ρ • (v (t + 1) - vs (t + 1)) = (v t - vs t) - (surprise 𝔼 π t - surprise 𝔼 πs t) := by
  obtain ⟨-, -, h3, h4, -, -⟩ := h t
  rw [smul_sub, h4, h3]
  abel

/-- Cochrane (2023), p. 136 (display before Figure 5.5):
`ρ (v_{t+1} − v*_{t+1}) = (v_t − v*_t) − (ΔE_{t+1} π_{t+1} + β_s ε_{t+1})`. -/
theorem diff_p136 (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (t : ℕ) :
    ρ • (v (t + 1) - vs (t + 1)) = (v t - vs t) - (surprise 𝔼 π t + βs • ε (t + 1)) := by
  rw [diff_rho 𝔼 h t, (h t).2.2.2.2.1]
  abel

/-- Cochrane (2023), eq. (5.35), p. 137:
`v_{t+1} − v*_{t+1} = ρ⁻¹ (v_t − v*_t) − ρ⁻¹ (ΔE_{t+1} π_{t+1} − ΔE_{t+1} π*_{t+1})`. -/
theorem diff_535 (hρ : ρ ≠ 0) (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (t : ℕ) :
    v (t + 1) - vs (t + 1) =
      ρ⁻¹ • (v t - vs t) - ρ⁻¹ • (surprise 𝔼 π t - surprise 𝔼 πs t) := by
  rw [← smul_sub, ← diff_rho 𝔼 h t, inv_smul_smul₀ hρ]

/-- Cochrane (2023), (5.35), p. 137: taking `E_t`, the gap `d = v − v*` is a forward-looking
process, `d_t = ρ E_t d_{t+1}` (root `ρ⁻¹`). -/
theorem diff_forward (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (hv : 𝔼.Adapted v)
    (hvs : 𝔼.Adapted vs) (t : ℕ) :
    v t - vs t = ρ • 𝔼.E t (v (t + 1) - vs (t + 1)) := by
  have hE := congrArg (𝔼.E t) (diff_rho 𝔼 h t)
  simp only [map_smul, map_sub, hv t, hvs t, E_surprise, sub_zero] at hE
  rw [map_sub, hE]

/-- Cochrane (2023), pp. 136–137 ("the condition that debt cannot explode means `v = v*`"),
for `|ρ| < 1`: if `v` and `v*` are bounded, then `v = v*` and
`ΔE_{t+1} π_{t+1} = ΔE_{t+1} π*_{t+1} = −β_s ε_{t+1}`. -/
theorem select_bounded (hρ : |ρ| < 1) (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u)
    (hv : 𝔼.Adapted v) (hvs : 𝔼.Adapted vs) (hbv : BoundedProc v) (hbvs : BoundedProc vs) :
    v = vs ∧ ∀ t, surprise 𝔼 π t = -(βs • ε (t + 1)) := by
  obtain ⟨M₁, hM₁⟩ := hbv
  obtain ⟨M₂, hM₂⟩ := hbvs
  have h₁ : ∀ t, (fun t => v t - vs t) t =
      ρ • 𝔼.E t ((fun t => v t - vs t) (t + 1)) + (0 : ℕ → Ω → ℝ) t := fun t => by
    simp only [Pi.zero_apply, add_zero]
    exact diff_forward 𝔼 h hv hvs t
  have h₂ : ∀ t, (fun _ => (0 : Ω → ℝ)) t =
      ρ • 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1)) + (0 : ℕ → Ω → ℝ) t := fun t => by simp
  have hd : (fun t => v t - vs t) = fun _ => 0 :=
    𝔼.forward_unique hρ h₁ h₂ ⟨M₁ + M₂, fun t ω => by
        simp only [Pi.sub_apply]
        exact (abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω))⟩ ⟨0, fun t ω => by simp⟩
  have hvv : ∀ t, v t = vs t := fun t => sub_eq_zero.mp (congrFun hd t)
  refine ⟨funext hvv, fun t => ?_⟩
  have h1 := diff_rho 𝔼 h t
  rw [hvv t, hvv (t + 1), sub_self, sub_self, smul_zero, zero_sub, eq_comm, neg_eq_zero,
    sub_eq_zero] at h1
  rw [h1, (h t).2.2.2.2.1]

/-- Cochrane (2023), pp. 136–137 and survey E32: for any `ρ ≠ 0` (including `ρ = 1`), the
transversality conditions on `v` and `v*` select `v = v*` and
`ΔE_{t+1} π_{t+1} = −β_s ε_{t+1}`. -/
theorem select_tvc (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (hv : 𝔼.Adapted v)
    (hvs : 𝔼.Adapted vs) (htv : TVC 𝔼 ρ v) (htvs : TVC 𝔼 ρ vs) :
    v = vs ∧ ∀ t, surprise 𝔼 π t = -(βs • ε (t + 1)) := by
  have hvv : ∀ t, v t = vs t := by
    intro t
    funext ω
    have hit : ∀ T, v t ω - vs t ω =
        ρ ^ T * 𝔼.E t (v (t + T)) ω - ρ ^ T * 𝔼.E t (vs (t + T)) ω := by
      intro T
      have := congrFun (𝔼.forward_iterate (d := fun t => v t - vs t)
        (fun t => diff_forward 𝔼 h hv hvs t) t T) ω
      simpa [map_sub, mul_sub] using this
    have hlim := (htv t ω).sub (htvs t ω)
    simp_rw [← hit, sub_zero] at hlim
    exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hlim)
  refine ⟨funext hvv, fun t => ?_⟩
  have h1 := diff_rho 𝔼 h t
  rw [hvv t, hvv (t + 1), sub_self, sub_self, smul_zero, zero_sub, eq_comm, neg_eq_zero,
    sub_eq_zero] at h1
  rw [h1, (h t).2.2.2.2.1]

/-- Cochrane (2023), pp. 136–138: in the model (5.29)–(5.34) with `0 < α < 2`, `|ρη| < 1` and
mean-zero shocks, `v*` satisfies its transversality condition automatically, so the
transversality condition on debt alone selects `v = v*`, `ΔE_{t+1} π_{t+1} = −β_s ε_{t+1}`. -/
theorem select (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (hεa : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε)
    (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) (hv : 𝔼.Adapted v)
    (htv : TVC 𝔼 ρ v) : v = vs ∧ ∀ t, surprise 𝔼 π t = -(βs • ε (t + 1)) :=
  select_tvc 𝔼 h hv (proc_adapted 𝔼 hρ h.surplusProc hεa hv0 hu0).2.1 htv
    (vstar_tvc 𝔼 hρ hα hη h.surplusProc hεa hε hv0 hu0)

/-- Cochrane (2023), p. 137: the inflation path of the active-fiscal equilibrium,
`π_{t+1} = i_t − β_s ε_{t+1}` (with `π_0 = 0`). -/
def eqPi (βs : ℝ) (i ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => i t - βs • ε (t + 1)

/-- Cochrane (2023), pp. 137–139 (existence): for any adapted interest-rate target `i`, the
processes `π = π* = eqPi`, `v = v*` solve (5.29)–(5.34). -/
theorem exists_equilibrium (hi : 𝔼.Adapted i) (hε : MeanZero 𝔼 ε)
    (h : IsSurplusProc ρ α βs η ε s vs u) :
    VStarModel 𝔼 ρ α βs η ε i (eqPi βs i ε) (eqPi βs i ε) s vs vs u := by
  have hsur : ∀ t, surprise 𝔼 (eqPi βs i ε) t = -(βs • ε (t + 1)) := fun t => by
    simp only [surprise, eqPi, map_sub, map_smul, hi t, hε t, smul_zero, sub_zero]
    abel
  intro t
  obtain ⟨h1, h2, h3⟩ := h t
  refine ⟨?_, h1, ?_, ?_, hsur t, h3⟩
  · simp only [eqPi, map_sub, map_smul, hi t, hε t, smul_zero, sub_zero]
  · rw [h2, hsur t]
    abel
  · rw [h2, hsur t]
    abel

/-- Cochrane (2023), pp. 137–139 (uniqueness): in every solution of (5.29)–(5.34) whose debt
satisfies the transversality condition, `π_{t+1} = i_t − β_s ε_{t+1}` and `v = v*`. -/
theorem unique_equilibrium (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (hεa : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε)
    (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0) (hv : 𝔼.Adapted v)
    (htv : TVC 𝔼 ρ v) : v = vs ∧ ∀ t, π (t + 1) = eqPi βs i ε (t + 1) := by
  obtain ⟨hvv, hs⟩ := select 𝔼 hρ hα hη h hεa hε hv0 hu0 hv htv
  refine ⟨hvv, fun t => ?_⟩
  have h1 := hs t
  rw [surprise, ← (h t).1] at h1
  rw [eqPi]
  calc π (t + 1) = (π (t + 1) - i t) + i t := by abel
    _ = i t - βs • ε (t + 1) := by rw [h1]; abel

/-- Cochrane (2023), eqs. (5.39)–(5.41), p. 139: the system "we see, estimate, and simulate":
`i_t = E_t π_{t+1}`, `ΔE_{t+1} π_{t+1} = −β_s ε_{t+1}`, `s̃_{t+1} = α v_t + u_{t+1}`,
`ρ v_{t+1} = v_t + β_s ε_{t+1} − s̃_{t+1}`, `u_{t+1} = η u_t + ε_{t+1}`. The book prints
`− β_s ε_{t+1}` in the debt equation of (5.41); the sign follows from (5.31) and (5.33) (and
agrees with (5.23)); see `printed_541_sign`. -/
def Reduced (ρ α βs η : ℝ) (ε i π s v u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ surprise 𝔼 π t = -(βs • ε (t + 1)) ∧
    s (t + 1) = α • v t + u (t + 1) ∧ ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1) ∧
    u (t + 1) = η • u t + ε (t + 1)

/-- Cochrane (2023), p. 139 ("the star variables disappear in equilibrium"): with `v = v*` and
`ΔE π = ΔE π*`, a solution of (5.29)–(5.34) satisfies (5.39)–(5.41). -/
theorem reduced_of_model (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (hvv : v = vs)
    (hpi : ∀ t, surprise 𝔼 π t = -(βs • ε (t + 1))) : Reduced 𝔼 ρ α βs η ε i π s v u := by
  intro t
  obtain ⟨h1, h2, -, h4, -, h6⟩ := h t
  refine ⟨h1, hpi t, by rw [hvv]; exact h2, ?_, h6⟩
  rw [h4, hpi t]
  abel

/-- Cochrane (2023), p. 139: conversely, every solution of (5.39)–(5.41) is a solution of
(5.29)–(5.34) with `v* = v` and `π* = π`. -/
theorem model_of_reduced (h : Reduced 𝔼 ρ α βs η ε i π s v u) :
    VStarModel 𝔼 ρ α βs η ε i π π s v v u := by
  intro t
  obtain ⟨h1, h2, h3, h4, h5⟩ := h t
  refine ⟨h1, h3, ?_, ?_, h2, h5⟩ <;>
  · rw [h4, h2]
    abel

/-! ### Survey E32: at `ρ = 1` boundedness does not select -/

open ExpectationsFiniteTree in
/-- Cochrane (2023), p. 137 (survey E32): in the coin-flip tree, the date-`t+1` shock is known at
date `t + 1`. -/
theorem coinShock_known (t : ℕ) :
    coinSystem.E (t + 1) (coinShock (t + 1)) = coinShock (t + 1) := by
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun ω' h => coinShock_measurable (t + 1) h

open ExpectationsFiniteTree in
/-- Cochrane (2023), p. 137 (survey E32): the counterexample inflation path, `π_1 = ±1` with a
fair coin, `π_t = 0` otherwise. -/
def cxPi (t : ℕ) (ω : Bool × Bool) : ℝ := if t = 1 then coinShock 1 ω else 0

open ExpectationsFiniteTree in
/-- Cochrane (2023), p. 137 (survey E32): the counterexample debt path, `v_t = −π_1` for
`t ≥ 1`, `v_0 = 0`. -/
def cxV (t : ℕ) (ω : Bool × Bool) : ℝ := if 1 ≤ t then -coinShock 1 ω else 0

open ExpectationsFiniteTree in
/-- Cochrane (2023), pp. 136–137, 148, survey E32: with `ρ = 1` the gap `v − v*` has a unit
root, and boundedness does not select. In the coin-flip tree, with no fiscal shocks
(`ε = u = s̃ = v* = π* = i = 0`), the debt path `cxV` and inflation `cxPi` solve (5.29)–(5.34)
for every `α, β_s, η`, all processes are bounded, yet `v ≠ v*` and
`ΔE_1 π_1 ≠ ΔE_1 π*_1`. The transversality condition fails, as `select_tvc` requires. -/
theorem rho_one_counterexample (α βs η : ℝ) :
    VStarModel coinSystem 1 α βs η 0 0 cxPi 0 0 cxV 0 0 ∧ BoundedProc cxV ∧
      BoundedProc (0 : ℕ → Bool × Bool → ℝ) ∧ cxV 1 ≠ 0 ∧
      surprise coinSystem cxPi 0 ≠ surprise coinSystem 0 0 ∧ ¬ TVC coinSystem 1 cxV := by
  have hE : ∀ t, coinSystem.E t (cxPi (t + 1)) = 0 := by
    intro t
    rcases t with _ | t
    · have : cxPi (0 + 1) = coinShock (0 + 1) := by funext ω; simp [cxPi]
      rw [this, coinShock_mean_zero]
    · have : cxPi (t + 1 + 1) = 0 := by funext ω; simp [cxPi]
      rw [this, map_zero]
  have hsur : ∀ t, surprise coinSystem cxPi t = cxPi (t + 1) := fun t => by
    rw [surprise, hE, sub_zero]
  have h0sur : ∀ t, surprise coinSystem (0 : ℕ → Bool × Bool → ℝ) t = 0 := fun t => by
    simp [surprise]
  have habs : ∀ ω, |coinShock 1 ω| ≤ 1 := fun ω => by
    unfold coinShock
    split_ifs <;> norm_num
  have hknown : ∀ T, coinSystem.E 1 (cxV (1 + T)) = cxV (1 + T) := fun T => by
    have : cxV (1 + T) = -coinShock 1 := by funext ω; simp [cxV]
    rw [this, map_neg, coinShock_known 0]
  refine ⟨fun t => ?_, ⟨1, fun t ω => ?_⟩, ⟨0, fun t ω => by simp⟩, ?_, ?_, ?_⟩
  · refine ⟨by simp [hE t], by simp, by simp [h0sur], ?_, by simp [h0sur], by simp⟩
    rw [hsur t, one_smul]
    funext ω
    rcases t with _ | t <;> simp [cxV, cxPi]
  · unfold cxV
    split_ifs
    · rw [abs_neg]; exact habs ω
    · norm_num
  · intro h1
    have := congrFun h1 (true, true)
    simp [cxV, coinShock] at this
  · rw [hsur, h0sur]
    intro h1
    have := congrFun h1 (true, true)
    simp [cxPi, coinShock] at this
  · intro htvc
    have hlim := htvc 1 (true, true)
    simp only [one_pow, one_mul, hknown] at hlim
    have hc : (fun T : ℕ => cxV (1 + T) (true, true)) = fun _ => -1 := by
      funext T
      simp [cxV, coinShock]
    rw [hc] at hlim
    have := tendsto_nhds_unique tendsto_const_nhds hlim
    norm_num at this

/-- Cochrane (2023), eq. (5.41), p. 139 (sign error in the printed debt equation): in an
equilibrium of (5.29)–(5.34) (`v = v*`), the printed `ρ v_{t+1} = v_t − β_s ε_{t+1} − s̃_{t+1}`
holds if and only if `β_s ε_{t+1} = 0`; the correct equation has `+ β_s ε_{t+1}`. -/
theorem printed_541_sign (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u) (hvv : v = vs)
    (hpi : ∀ t, surprise 𝔼 π t = -(βs • ε (t + 1))) (t : ℕ) :
    ρ • v (t + 1) = v t - βs • ε (t + 1) - s (t + 1) ↔ βs • ε (t + 1) = 0 := by
  have hr := ((reduced_of_model 𝔼 h hvv hpi) t).2.2.2.1
  rw [hr]
  constructor
  · intro h1
    have h2 : (2 : ℝ) • (βs • ε (t + 1)) = 0 := by
      rw [two_smul]
      have := congrArg (· - (v t - s (t + 1))) h1
      rw [show v t + βs • ε (t + 1) - s (t + 1) - (v t - s (t + 1)) = βs • ε (t + 1) by abel,
        show v t - βs • ε (t + 1) - s (t + 1) - (v t - s (t + 1)) = -(βs • ε (t + 1)) by abel]
        at this
      nth_rw 1 [this]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro h0
    rw [h0, add_zero, sub_zero]

/-! ### Responding to the actual value of debt: (5.36)–(5.37) -/

/-- Cochrane (2023), p. 138: a debt process driven by `ρ x_{t+1} = c x_t − δ_t − u_{t+1}` with
`|c| < 1`, `E_t δ_t = 0` and an AR(1) disturbance `u` (`|ρη| < 1`) satisfies the
transversality condition, whatever the shocks `δ`. -/
theorem tvc_of_rec {c : ℝ} (hc : |c| < 1) (hη : |ρ * η| < 1) {x δ : ℕ → Ω → ℝ}
    (hrec : ∀ t, ρ • x (t + 1) = c • x t - δ t - u (t + 1)) (hδ : ∀ t, 𝔼.E t (δ t) = 0)
    (hu : 𝔼.Adapted u) (hur : ∀ t, u (t + 1) = η • u t + ε (t + 1)) (hε : MeanZero 𝔼 ε) :
    TVC 𝔼 ρ x := by
  have hAR : 𝔼.IsAR1 η u := ⟨hu, fun t => by rw [hur, map_add, map_smul, hu t, hε t, add_zero]⟩
  intro t ω
  refine (summable_disc (c := c) (b := -u t ω) hc hη (y := fun j => 𝔼.E t (x (t + j)) ω)
    (fun j => ?_)).tendsto_atTop_zero
  have hE := congrArg (𝔼.E t) (hrec (t + j))
  have hδ' : 𝔼.E t (δ (t + j)) = 0 := by rw [← 𝔼.tower (Nat.le_add_right t j), hδ, map_zero]
  rw [map_smul, map_sub, map_sub, map_smul, hδ', sub_zero,
    show t + j + 1 = t + (j + 1) by omega, 𝔼.ar1_iterate hAR t (j + 1)] at hE
  have hE' := congrFun hE ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hE'
  rw [hE']
  ring

/-- Cochrane (2023), eqs. (5.36)–(5.37), p. 138: the surplus responds to the actual value of
debt, `s̃_{t+1} = γ v_t + u_{t+1}`, with `i_t = E_t π_{t+1}` and
`ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s̃_{t+1}`. -/
def GammaRule (ρ γ η : ℝ) (ε i π s v u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ s (t + 1) = γ • v t + u (t + 1) ∧
    ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) ∧ u (t + 1) = η • u t + ε (t + 1)

/-- Cochrane (2023), p. 138: substituting (5.36) into (5.37),
`ρ v_{t+1} = (1 − γ) v_t − ΔE_{t+1} π_{t+1} − u_{t+1}`. -/
theorem gamma_rec (h : GammaRule 𝔼 ρ γ η ε i π s v u) (t : ℕ) :
    ρ • v (t + 1) = (1 - γ) • v t - surprise 𝔼 π t - u (t + 1) := by
  obtain ⟨-, h2, h3, -⟩ := h t
  rw [h3, h2, sub_smul, one_smul]
  abel

/-- Cochrane (2023), p. 138 ("For γ > 0, debt grows at less than the interest rate, so the
transversality condition holds. Any unexpected inflation is an equilibrium"), corrected per the
survey of Chapters 11–19 (E6): for `0 < γ < 2` the transversality condition holds whatever the
unexpected-inflation process. (The upper bound `γ < 2` is needed: `gamma_passive_iff`.) -/
theorem gamma_tvc (hγ : |1 - γ| < 1) (hη : |ρ * η| < 1) (h : GammaRule 𝔼 ρ γ η ε i π s v u)
    (hε : MeanZero 𝔼 ε) (hu : 𝔼.Adapted u) : TVC 𝔼 ρ v :=
  tvc_of_rec 𝔼 hγ hη (gamma_rec 𝔼 h) (E_surprise 𝔼 π) hu (fun t => (h t).2.2.2) hε

/-- Cochrane (2023), p. 138: the process `x_0 = 0`, `x_{t+1} = f_t` (a variable first dated 1). -/
def succPath (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => f t

/-- Cochrane (2023), p. 138: the debt path of (5.37) for given shocks,
`v_{t+1} = ρ⁻¹((1 − γ) v_t − δ_t − u_{t+1})`. -/
noncomputable def gammaPath (ρ γ : ℝ) (v0 : Ω → ℝ) (δ u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => v0
  | t + 1 => ρ⁻¹ • ((1 - γ) • gammaPath ρ γ v0 δ u t - δ t - u (t + 1))

/-- Cochrane (2023), p. 138: the debt path is adapted when `v_0`, `δ` and `u` are. -/
theorem gammaPath_adapted {v0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hv0 : 𝔼.E 0 v0 = v0)
    (hδ1 : ∀ t, 𝔼.E (t + 1) (δ t) = δ t) (hu : 𝔼.Adapted u) :
    𝔼.Adapted (gammaPath ρ γ v0 δ u) := by
  intro t
  induction t with
  | zero => exact hv0
  | succ t ih =>
    simp only [gammaPath]
    rw [map_smul, map_sub, map_sub, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      hδ1 t, hu (t + 1)]

/-- Cochrane (2023), p. 138 ("Any unexpected inflation leads to a change in debt which leads to
changes in surpluses that validate that unexpected inflation"): for every mean-zero shock `δ`
there is a solution of (5.36)–(5.37) with `ΔE_{t+1} π_{t+1} = δ_t`. -/
theorem gamma_exists (hρ : ρ ≠ 0) (hi : 𝔼.Adapted i) {δ : ℕ → Ω → ℝ}
    (hδ : ∀ t, 𝔼.E t (δ t) = 0) (hur : ∀ t, u (t + 1) = η • u t + ε (t + 1)) (v0 : Ω → ℝ) :
    GammaRule 𝔼 ρ γ η ε i (succPath (fun t => i t + δ t))
        (succPath (fun t => γ • gammaPath ρ γ v0 δ u t + u (t + 1))) (gammaPath ρ γ v0 δ u) u ∧
      ∀ t, surprise 𝔼 (succPath (fun t => i t + δ t)) t = δ t := by
  have hsur : ∀ t, surprise 𝔼 (succPath (fun t => i t + δ t)) t = δ t := fun t => by
    simp only [surprise, succPath, map_add, hi t, hδ t, add_zero]
    abel
  refine ⟨fun t => ⟨?_, rfl, ?_, hur t⟩, hsur⟩
  · simp only [succPath, map_add, hi t, hδ t, add_zero]
  · rw [hsur t]
    simp only [succPath, gammaPath, smul_smul, mul_inv_cancel₀ hρ, one_smul, sub_smul]
    abel

/-- Cochrane (2023), p. 138 (passive fiscal policy): for `0 < γ < 2`, every mean-zero
unexpected-inflation process `δ` (known at `t + 1`) is an equilibrium of (5.36)–(5.37) whose
debt satisfies the transversality condition. -/
theorem gamma_passive (hρ : ρ ≠ 0) (hγ : |1 - γ| < 1) (hη : |ρ * η| < 1) (hi : 𝔼.Adapted i)
    (hε : MeanZero 𝔼 ε) (hu : 𝔼.Adapted u) (hur : ∀ t, u (t + 1) = η • u t + ε (t + 1))
    {δ : ℕ → Ω → ℝ} (hδ : ∀ t, 𝔼.E t (δ t) = 0) (v0 : Ω → ℝ) :
    ∃ π' s' v' : ℕ → Ω → ℝ, GammaRule 𝔼 ρ γ η ε i π' s' v' u ∧
      (∀ t, surprise 𝔼 π' t = δ t) ∧ v' 0 = v0 ∧ TVC 𝔼 ρ v' := by
  obtain ⟨h1, h2⟩ := gamma_exists 𝔼 hρ hi (γ := γ) hδ hur v0
  exact ⟨_, _, _, h1, h2, rfl, gamma_tvc 𝔼 hγ hη h1 hε hu⟩

/-- Cochrane (2023), p. 138 (survey E6 of Chapters 11–19): passivity holds exactly for
`0 < γ < 2`. Every debt path `ρ v_{t+1} = (1 − γ) v_t − ΔE_{t+1} π_{t+1}` (no disturbance)
satisfies the transversality condition, for every inflation process, iff `|1 − γ| < 1`. -/
theorem gamma_passive_iff [Nonempty Ω] (hρ : ρ ≠ 0) :
    (∀ π' v' : ℕ → Ω → ℝ, 𝔼.Adapted v' →
      (∀ t, ρ • v' (t + 1) = (1 - γ) • v' t - surprise 𝔼 π' t) → TVC 𝔼 ρ v') ↔
      |1 - γ| < 1 := by
  constructor
  · intro H
    set c := (1 - γ) / ρ with hc
    have hv : 𝔼.Adapted (fun t (_ : Ω) => c ^ t) := fun t => 𝔼.const t _
    have hrec : ∀ t, ρ • (fun t (_ : Ω) => c ^ t) (t + 1) =
        (1 - γ) • (fun t (_ : Ω) => c ^ t) t - surprise 𝔼 0 t := fun t => by
      have h0 : surprise 𝔼 (0 : ℕ → Ω → ℝ) t = 0 := by simp [surprise]
      rw [h0, sub_zero]
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, hc, pow_succ]
      field_simp
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have ht := H 0 _ hv hrec 0 ω
    simp only [zero_add, 𝔼.const] at ht
    have : (fun T : ℕ => ρ ^ T * c ^ T) = fun T => (1 - γ) ^ T := by
      funext T
      rw [← mul_pow, hc, mul_div_cancel₀ _ hρ]
    rw [this] at ht
    exact tendsto_pow_atTop_nhds_zero_iff.mp ht
  · intro hγ π' v' _ hrec
    refine tvc_of_rec 𝔼 (u := 0) (ε := 0) (η := 0) hγ (by simp) (fun t => ?_) (E_surprise 𝔼 π')
      (fun t => by simp) (fun t => by simp) (fun t => by simp)
    rw [hrec t, Pi.zero_apply, sub_zero]

/-- Cochrane (2023), p. 138 (survey E54): debt is bounded for every bounded unexpected inflation
when `|1 − γ| < ρ`, i.e. `1 − ρ < γ < 1 + ρ` (the book states only `γ > 1 − ρ`). -/
theorem gamma_bounded (hρ : 0 < ρ) (hγ : |1 - γ| < ρ) {x δ : ℕ → Ω → ℝ} {Mδ Mu V : ℝ}
    (hrec : ∀ t, ρ • x (t + 1) = (1 - γ) • x t - δ t - u (t + 1))
    (hδ : ∀ t ω, |δ t ω| ≤ Mδ) (hu : ∀ t ω, |u t ω| ≤ Mu) (hx0 : ∀ ω, |x 0 ω| ≤ V) :
    BoundedProc x := by
  refine ⟨V + ((|Mδ| + |Mu|) / ρ) / (1 - |1 - γ| / ρ), fun t ω => ?_⟩
  refine bounded_of_rec (x := fun t => x t ω) (c := |1 - γ| / ρ) (div_nonneg (abs_nonneg _) hρ.le)
    ((div_lt_one hρ).mpr hγ) (div_nonneg (by positivity) hρ.le) (hx0 ω) (fun t => ?_) t
  have hr := congrFun (hrec t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
  have hx1 : x (t + 1) ω = ((1 - γ) * x t ω - δ t ω - u (t + 1) ω) / ρ := by
    rw [← hr]; field_simp
  rw [hx1, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  have h1 := abs_sub ((1 - γ) * x t ω - δ t ω) (u (t + 1) ω)
  have h2 := abs_sub ((1 - γ) * x t ω) (δ t ω)
  have h3 : |δ t ω| ≤ |Mδ| := (hδ t ω).trans (le_abs_self _)
  have h4 : |u (t + 1) ω| ≤ |Mu| := (hu (t + 1) ω).trans (le_abs_self _)
  rw [abs_mul] at h2
  have : |1 - γ| / ρ * |x t ω| * ρ = |1 - γ| * |x t ω| := by field_simp
  have : (|Mδ| + |Mu|) / ρ * ρ = |Mδ| + |Mu| := by field_simp
  nlinarith

/-- Cochrane (2023), pp. 137–138: a geometric path `cᵗ` with `|c| > 1` is unbounded. -/
theorem not_bounded_pow [Nonempty Ω] {c : ℝ} (hc : 1 < |c|) :
    ¬ BoundedProc (fun t (_ : Ω) => c ^ t) := by
  rintro ⟨M, hM⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hc).eventually_gt_atTop M).exists
  have := hM n ω
  rw [abs_pow] at this
  linarith

/-- Cochrane (2023), p. 138 (survey E54): for `|1 − γ| > ρ` (e.g. `γ > 1 + ρ`) debt explodes even
with no shocks: `v_t = ((1 − γ)/ρ)ᵗ` solves (5.37) with `ΔE π = 0`, `u = 0`, and is unbounded. -/
theorem gamma_unbounded [Nonempty Ω] (hρ : 0 < ρ) (hγ : ρ < |1 - γ|) :
    ∃ x : ℕ → Ω → ℝ, (∀ t, ρ • x (t + 1) = (1 - γ) • x t - surprise 𝔼 0 t - 0) ∧
      ¬ BoundedProc x := by
  refine ⟨fun t _ => ((1 - γ) / ρ) ^ t, fun t => ?_, not_bounded_pow ?_⟩
  · have h0 : surprise 𝔼 (0 : ℕ → Ω → ℝ) t = 0 := by simp [surprise]
    rw [h0, sub_zero, sub_zero]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    field_simp
  · rw [abs_div, abs_of_pos hρ, one_lt_div hρ]
    exact hγ

/-- Cochrane (2023), Chapter 4, p. 96 (survey E10) and p. 139: a surplus responding to the
actual value of debt, `s̃_{t+1} = α v_t + u_{t+1}` with `0 < α < 2`, is a passive policy:
every unexpected-inflation process satisfies the transversality condition. -/
theorem e10_actual_debt_rule_passive (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : GammaRule 𝔼 ρ α η ε i π s v u) (hε : MeanZero 𝔼 ε) (hu : 𝔼.Adapted u) :
    TVC 𝔼 ρ v :=
  gamma_tvc 𝔼 hα hη h hε hu

/-! ### Equation (5.38): passive iff `γ = α` (survey E33) -/

/-- Cochrane (2023), eq. (5.38), p. 139: the surplus responds to the latent variable and to the
gap, `s̃_{t+1} = α v*_t + γ (v_t − v*_t) + u_{t+1}`, with (5.29), (5.31)–(5.34). -/
def Rule538 (ρ α γ βs η : ℝ) (ε i π πs s v vs u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ s (t + 1) = α • vs t + γ • (v t - vs t) + u (t + 1) ∧
    ρ • vs (t + 1) = vs t - surprise 𝔼 πs t - s (t + 1) ∧
    ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) ∧
    surprise 𝔼 πs t = -(βs • ε (t + 1)) ∧ u (t + 1) = η • u t + ε (t + 1)

/-- Cochrane (2023), p. 139: with `γ = 0`, (5.38) is the model (5.29)–(5.34). -/
theorem rule538_gamma_zero :
    Rule538 𝔼 ρ α 0 βs η ε i π πs s v vs u ↔ VStarModel 𝔼 ρ α βs η ε i π πs s v vs u := by
  simp only [Rule538, VStarModel, zero_smul, add_zero]

/-- Cochrane (2023), p. 139: with `γ = α`, (5.38) is the rule (5.36) on actual debt,
`s̃_{t+1} = α v_t + u_{t+1}`. -/
theorem rule538_gamma_alpha (h : Rule538 𝔼 ρ α α βs η ε i π πs s v vs u) :
    GammaRule 𝔼 ρ α η ε i π s v u := fun t => by
  obtain ⟨h1, h2, -, h4, -, h6⟩ := h t
  refine ⟨h1, ?_, h4, h6⟩
  rw [h2, smul_sub]
  abel

/-- Cochrane (2023), (5.38), p. 139: the debt equation under (5.38),
`ρ v_{t+1} = (1 − α) v_t + (α − γ)(v_t − v*_t) − ΔE_{t+1} π_{t+1} − u_{t+1}`. -/
theorem rule538_v_rec (h : Rule538 𝔼 ρ α γ βs η ε i π πs s v vs u) (t : ℕ) :
    ρ • v (t + 1) =
      (1 - α) • v t + (α - γ) • (v t - vs t) - surprise 𝔼 π t - u (t + 1) := by
  obtain ⟨-, h2, -, h4, -, -⟩ := h t
  rw [h4, h2]
  module

/-- Cochrane (2023), (5.38), p. 139: the gap `d = v − v*` follows
`ρ d_{t+1} = d_t − (ΔE_{t+1} π_{t+1} − ΔE_{t+1} π*_{t+1})` whatever `γ`, so
`d_t = ρ E_t d_{t+1}`. -/
theorem rule538_diff_forward (h : Rule538 𝔼 ρ α γ βs η ε i π πs s v vs u) (hv : 𝔼.Adapted v)
    (hvs : 𝔼.Adapted vs) (t : ℕ) : v t - vs t = ρ • 𝔼.E t (v (t + 1) - vs (t + 1)) := by
  have hd : ρ • (v (t + 1) - vs (t + 1)) =
      (v t - vs t) - (surprise 𝔼 π t - surprise 𝔼 πs t) := by
    obtain ⟨-, -, h3, h4, -, -⟩ := h t
    rw [smul_sub, h4, h3]
    abel
  have hE := congrArg (𝔼.E t) hd
  simp only [map_smul, map_sub, hv t, hvs t, E_surprise, sub_zero] at hE
  rw [map_sub, hE]

/-- Cochrane (2023), (5.38), p. 139, survey E33 (the key computation): with `0 < α < 2` and
`|ρη| < 1`, the discounted forecast of debt converges, `ρᵀ E_t v_{t+T} → (α − γ)(v_t − v*_t)/α`.
Hence the transversality condition on actual debt holds at `(t, ω)` iff
`(α − γ)(v_t − v*_t) = 0`: the explosive root `ρ⁻¹` of `v − v*` loads on `v` with weight
`(α − γ)/α`. -/
theorem tvc_v_iff_538 (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : Rule538 𝔼 ρ α γ βs η ε i π πs s v vs u) (hε : MeanZero 𝔼 ε) (hu : 𝔼.Adapted u)
    (hv : 𝔼.Adapted v) (hvs : 𝔼.Adapted vs) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0) ↔
      (α - γ) * (v t ω - vs t ω) = 0 := by
  obtain ⟨hα0, -⟩ := alpha_pos_of hα
  have hAR : 𝔼.IsAR1 η u :=
    ⟨hu, fun t => by rw [(h t).2.2.2.2.2, map_add, map_smul, hu t, hε t, add_zero]⟩
  set D := v t ω - vs t ω with hD
  set L := (α - γ) * D / α with hL
  have hdk : ∀ k, ρ ^ k * 𝔼.E t (v (t + k) - vs (t + k)) ω = D := by
    intro k
    have := congrFun (𝔼.forward_iterate (d := fun t => v t - vs t)
      (fun t => rule538_diff_forward 𝔼 h hv hvs t) t k) ω
    simpa using this.symm
  set w : ℕ → ℝ := fun j => ρ ^ j * 𝔼.E t (v (t + j)) ω with hw
  have hrec : ∀ j, w (j + 1) - L = (1 - α) * (w j - L) + (-(η * u t ω)) * (ρ * η) ^ j := by
    intro j
    have hE := congrArg (𝔼.E t) (rule538_v_rec 𝔼 h (t + j))
    have hsur : 𝔼.E t (surprise 𝔼 π (t + j)) = 0 := by
      rw [← 𝔼.tower (Nat.le_add_right t j), E_surprise, map_zero]
    rw [map_smul, map_sub, map_sub, map_add, map_smul, map_smul, hsur, sub_zero,
      show t + j + 1 = t + (j + 1) by omega, 𝔼.ar1_iterate hAR t (j + 1)] at hE
    have hE' := congrFun hE ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub] at hE'
    have hdj := hdk j
    simp only [map_sub, Pi.sub_apply] at hdj
    have key : w (j + 1) = (1 - α) * w j + (α - γ) * D + (-(η * u t ω)) * (ρ * η) ^ j := by
      simp only [hw]
      rw [pow_succ, mul_assoc, hE', ← hdj, mul_pow]
      ring
    rw [key, hL]
    field_simp
    ring
  have hz : Tendsto (fun j => w j - L) atTop (𝓝 0) :=
    tendsto_zero_of_rec hα ((summable_geometric_of_abs_lt_one hη).mul_left _) hrec
  have hwL : Tendsto w atTop (𝓝 L) := by
    simpa using hz.add_const L
  constructor
  · intro h0
    have hL0 : L = 0 := tendsto_nhds_unique hwL h0
    rw [hL, div_eq_zero_iff] at hL0
    exact hL0.resolve_right hα0.ne'
  · intro h0
    have hL0 : L = 0 := by rw [hL, h0, zero_div]
    rw [← hL0]
    exact hwL

/-- Cochrane (2023), (5.38), p. 139, survey E33: for every `γ ≠ α` fiscal policy is active: the
transversality condition on actual debt selects `v = v*` and
`ΔE_{t+1} π_{t+1} = ΔE_{t+1} π*_{t+1} = −β_s ε_{t+1}`. -/
theorem active_538 (hα : |1 - α| < 1) (hη : |ρ * η| < 1) (hγ : γ ≠ α)
    (h : Rule538 𝔼 ρ α γ βs η ε i π πs s v vs u) (hε : MeanZero 𝔼 ε) (hu : 𝔼.Adapted u)
    (hv : 𝔼.Adapted v) (hvs : 𝔼.Adapted vs) (htv : TVC 𝔼 ρ v) :
    v = vs ∧ ∀ t, surprise 𝔼 π t = surprise 𝔼 πs t := by
  have hvv : ∀ t, v t = vs t := fun t => funext fun ω => by
    have := (tvc_v_iff_538 𝔼 hα hη h hε hu hv hvs t ω).mp (htv t ω)
    have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hγ))
    exact sub_eq_zero.mp this
  refine ⟨funext hvv, fun t => ?_⟩
  obtain ⟨-, -, h3, h4, -, -⟩ := h t
  rw [hvv t, hvv (t + 1), h3] at h4
  have := congrArg (fun x => x - (vs t - s (t + 1))) h4
  rw [show vs t - surprise 𝔼 πs t - s (t + 1) - (vs t - s (t + 1)) = -surprise 𝔼 πs t by abel,
    show vs t - surprise 𝔼 π t - s (t + 1) - (vs t - s (t + 1)) = -surprise 𝔼 π t by abel]
    at this
  exact (neg_inj.mp this).symm

/-- Cochrane (2023), (5.38), p. 139, survey E33: for `γ = α` fiscal policy is passive: the
transversality condition on debt holds whatever unexpected inflation is. -/
theorem passive_538 (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (h : Rule538 𝔼 ρ α α βs η ε i π πs s v vs u) (hε : MeanZero 𝔼 ε) (hu : 𝔼.Adapted u) :
    TVC 𝔼 ρ v :=
  gamma_tvc 𝔼 hα hη (rule538_gamma_alpha 𝔼 h) hε hu

/-- Cochrane (2023), p. 139: "active" fiscal policy in (5.38): in every solution whose debt
satisfies the transversality condition, unexpected inflation equals the target's. -/
def Active538 (ρ α γ βs η : ℝ) : Prop :=
  ∀ ε i π πs s v vs u : ℕ → Ω → ℝ, MeanZero 𝔼 ε → 𝔼.Adapted u → 𝔼.Adapted v →
    𝔼.Adapted vs → Rule538 𝔼 ρ α γ βs η ε i π πs s v vs u → TVC 𝔼 ρ v →
    ∀ t, surprise 𝔼 π t = surprise 𝔼 πs t

/-- Cochrane (2023), p. 139: the latent debt of (5.31) with `ΔE π* = 0` and `v*_0 = 0`. -/
noncomputable def latentPath (ρ : ℝ) (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => ρ⁻¹ • (latentPath ρ s t - s (t + 1))

/-- Cochrane (2023), (5.38), p. 139, survey E33 (the corrected statement): whenever there is
genuine uncertainty (some mean-zero shock `δ` with `δ_0 ≠ 0`, known at `t + 1`), fiscal policy
in (5.38) is active if and only if `γ ≠ α`. The book's "active iff `γ = 0`" is false
(`printed_538_false`). -/
theorem active_iff_538 (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (hδex : ∃ δ : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (δ t) = 0) ∧ (∀ t, 𝔼.E (t + 1) (δ t) = δ t) ∧
      δ 0 ≠ 0) :
    Active538 𝔼 ρ α γ βs η ↔ γ ≠ α := by
  constructor
  · intro hA hγ
    subst hγ
    obtain ⟨δ, hδ, hδ1, hδ0⟩ := hδex
    set v' := gammaPath ρ γ 0 δ 0 with hv'
    set s' := succPath (fun t => γ • v' t) with hs'
    set vs' := latentPath ρ s' with hvs'
    set π' := succPath δ with hπ'
    have hv'a : 𝔼.Adapted v' :=
      gammaPath_adapted 𝔼 (by simp) hδ1 (fun t => by simp)
    have hsur : ∀ t, surprise 𝔼 π' t = δ t := fun t => by
      simp only [surprise, hπ', succPath, hδ t, sub_zero]
    have hsur0 : ∀ t, surprise 𝔼 (0 : ℕ → Ω → ℝ) t = 0 := fun t => by simp [surprise]
    have hvs'a : 𝔼.Adapted vs' := by
      intro t
      induction t with
      | zero => simp [hvs', latentPath]
      | succ t ih =>
        simp only [hvs', latentPath, hs', succPath]
        rw [map_smul, map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih, map_smul,
          ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hv'a t)]
    have hR : Rule538 𝔼 ρ γ γ βs η 0 0 π' 0 s' v' vs' 0 := by
      intro t
      refine ⟨?_, ?_, ?_, ?_, by simp [hsur0], by simp⟩
      · simp [hπ', succPath, hδ t]
      · simp only [hs', succPath, Pi.zero_apply, add_zero, smul_sub]
        abel
      · rw [hsur0, sub_zero]
        simp only [hvs', latentPath, smul_smul, mul_inv_cancel₀ hρ, one_smul]
      · rw [hsur t]
        simp only [hv', gammaPath, hs', succPath, smul_smul, mul_inv_cancel₀ hρ, one_smul,
          Pi.zero_apply, sub_zero, sub_smul]
        abel
    have htv : TVC 𝔼 ρ v' := passive_538 𝔼 hα hη hR (fun t => by simp) (fun t => by simp)
    have := hA 0 0 π' 0 s' v' vs' 0 (fun t => by simp) (fun t => by simp) hv'a hvs'a hR htv 0
    rw [hsur, hsur0] at this
    exact hδ0 this
  · intro hγ ε' i' π' πs' s' v' vs' u' hε hu hv hvs hR htv t
    exact (active_538 𝔼 hα hη hγ hR hε hu hv hvs htv).2 t

open ExpectationsFiniteTree in
/-- Cochrane (2023), p. 139: the coin-flip tree has a genuine mean-zero shock, `δ_t = ε_{t+1}`
of `coinShock`, known at `t + 1`, with `δ_0 = ±1 ≠ 0`. -/
theorem coin_shock_exists :
    ∃ δ : ℕ → Bool × Bool → ℝ, (∀ t, coinSystem.E t (δ t) = 0) ∧
      (∀ t, coinSystem.E (t + 1) (δ t) = δ t) ∧ δ 0 ≠ 0 := by
  refine ⟨fun t => coinShock (t + 1), coinShock_mean_zero, coinShock_known, fun h => ?_⟩
  have := congrFun h (true, true)
  simp [coinShock] at this

open ExpectationsFiniteTree in
/-- Cochrane (2023), p. 139 ("The condition for active fiscal policy is γ = 0, not α = 0"),
survey E33: the printed criterion is false. In the coin-flip tree with `ρ = 1`, `η = 0`,
`α = 1/10`, the rule with `γ = 1/5 ≠ 0` is active, so "active iff `γ = 0`" fails. -/
theorem printed_538_false (βs : ℝ) :
    ¬ ∀ α γ : ℝ, |1 - α| < 1 → (Active538 coinSystem 1 α γ βs 0 ↔ γ = 0) := by
  intro H
  have hα : |1 - (1 / 10 : ℝ)| < 1 := by norm_num [abs_of_pos]
  have hA := (active_iff_538 coinSystem (α := 1 / 10) (γ := 1 / 5) (βs := βs) (η := 0)
    one_ne_zero hα (by simp) coin_shock_exists).mpr (by norm_num)
  have := (H (1 / 10) (1 / 5) hα).mp hA
  norm_num at this

/-! ### Observational equivalence with active money: (5.42) -/

/-- Cochrane (2023), pp. 139–140: a target `(π*, i*, v*, s̃, u)`: `i*_t = E_t π*_{t+1}`,
`ΔE_{t+1} π*_{t+1} = −β_s ε_{t+1}`, and the surplus process (5.22)–(5.24) with latent `v*`. -/
def Target (ρ α βs η : ℝ) (ε is πs s vs u : ℕ → Ω → ℝ) : Prop :=
  (∀ t, is t = 𝔼.E t (πs (t + 1)) ∧ surprise 𝔼 πs t = -(βs • ε (t + 1))) ∧
    IsSurplusProc ρ α βs η ε s vs u

/-- Cochrane (2023), eq. (5.42), p. 140: active money, passive fiscal policy:
`i_t = E_t π_{t+1}`, `i_t = i*_t + φ(π_t − π*_t)`, `s̃_{t+1} = α v_t + u_{t+1}` (the passive rule
(5.38) with `γ = α`), `ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s̃_{t+1}`. -/
def ActiveMoney (ρ α φ η : ℝ) (ε is πs i π s v u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ i t = is t + φ • (π t - πs t) ∧
    s (t + 1) = α • v t + u (t + 1) ∧ ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) ∧
    u (t + 1) = η • u t + ε (t + 1)

variable {is : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 139: the target is an equilibrium of the active-fiscal model
(5.29)–(5.34) with `i = i*`. -/
theorem modelA_target (hT : Target 𝔼 ρ α βs η ε is πs s vs u) :
    VStarModel 𝔼 ρ α βs η ε is πs πs s vs vs u := fun t => by
  obtain ⟨hT1, hP⟩ := hT
  obtain ⟨p1, p2, p3⟩ := hP t
  have e : ρ • vs (t + 1) = vs t - surprise 𝔼 πs t - s (t + 1) := by
    rw [p2, (hT1 t).2]
    abel
  exact ⟨(hT1 t).1, p1, e, e, (hT1 t).2, p3⟩

/-- Cochrane (2023), pp. 139–140: every equilibrium of the active-fiscal model with `i = i*`
whose debt satisfies the transversality condition is the target: `π_{t+1} = π*_{t+1}`,
`v = v*`. -/
theorem modelA_unique (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    (hT : Target 𝔼 ρ α βs η ε is πs s vs u) (h : VStarModel 𝔼 ρ α βs η ε is π πs s v vs u)
    (hεa : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0)
    (hu0 : 𝔼.E 0 (u 0) = u 0) (hv : 𝔼.Adapted v) (htv : TVC 𝔼 ρ v) :
    (∀ t, π (t + 1) = πs (t + 1)) ∧ v = vs := by
  obtain ⟨hvv, hs⟩ := select 𝔼 hρ hα hη h hεa hε hv0 hu0 hv htv
  refine ⟨fun t => ?_, hvv⟩
  have e1 : π (t + 1) = 𝔼.E t (π (t + 1)) + surprise 𝔼 π t := by rw [surprise]; abel
  have e2 : πs (t + 1) = 𝔼.E t (πs (t + 1)) + surprise 𝔼 πs t := by rw [surprise]; abel
  rw [e1, e2, ← (h t).1, ← (hT.1 t).1, hs t, (hT.1 t).2]

/-- Cochrane (2023), p. 140 (active fiscal with passive money, `φ < 1`): if the interest rate
follows `i_t = i*_t + φ(π_t − π*_t)` (any `φ`) in (5.29)–(5.34), `π_0 = π*_0`, and debt satisfies
the transversality condition, then `π = π*`, `v = v*` and `i = i*`. -/
theorem modelA_phi_unique (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1) {φ : ℝ}
    (hT : Target 𝔼 ρ α βs η ε is πs s vs u) (h : VStarModel 𝔼 ρ α βs η ε i π πs s v vs u)
    (hi : ∀ t, i t = is t + φ • (π t - πs t)) (hπ0 : π 0 = πs 0)
    (hεa : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0)
    (hu0 : 𝔼.E 0 (u 0) = u 0) (hv : 𝔼.Adapted v) (htv : TVC 𝔼 ρ v) :
    π = πs ∧ v = vs ∧ i = is := by
  obtain ⟨hvv, hs⟩ := select 𝔼 hρ hα hη h hεa hε hv0 hu0 hv htv
  have hππ : ∀ t, π t = πs t := by
    intro t
    induction t with
    | zero => exact hπ0
    | succ t ih =>
      have e1 : π (t + 1) = 𝔼.E t (π (t + 1)) + surprise 𝔼 π t := by rw [surprise]; abel
      have e2 : πs (t + 1) = 𝔼.E t (πs (t + 1)) + surprise 𝔼 πs t := by rw [surprise]; abel
      rw [e1, e2, ← (h t).1, ← (hT.1 t).1, hs t, (hT.1 t).2, hi t, ih, sub_self, smul_zero,
        add_zero]
  refine ⟨funext hππ, hvv, funext fun t => ?_⟩
  rw [hi t, hππ t, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 140: the target is also an equilibrium of the active-money model
(5.42). -/
theorem modelB_target (φ : ℝ) (hT : Target 𝔼 ρ α βs η ε is πs s vs u) :
    ActiveMoney 𝔼 ρ α φ η ε is πs is πs s vs u := fun t => by
  obtain ⟨hT1, hP⟩ := hT
  obtain ⟨p1, p2, p3⟩ := hP t
  refine ⟨(hT1 t).1, by rw [sub_self, smul_zero, add_zero], p1, ?_, p3⟩
  rw [p2, (hT1 t).2]
  abel

/-- Cochrane (2023), p. 140 (passive fiscal policy in the active-money model): with
`0 < α < 2`, debt satisfies the transversality condition whatever inflation does. -/
theorem modelB_passive (hα : |1 - α| < 1) (hη : |ρ * η| < 1) {φ : ℝ}
    (h : ActiveMoney 𝔼 ρ α φ η ε is πs i π s v u) (hε : MeanZero 𝔼 ε) (hu : 𝔼.Adapted u) :
    TVC 𝔼 ρ v :=
  gamma_tvc 𝔼 hα hη (fun t => ⟨(h t).1, (h t).2.2.1, (h t).2.2.2.1, (h t).2.2.2.2⟩) hε hu

/-- Cochrane (2023), eq. (5.42), p. 140 ("`π_t ≠ π*_t` generates an explosion"): for
`|φ| > 1`, every equilibrium of the active-money model with `π − π*` bounded and `v_0 = v*_0`
is the target: `π = π*`, `v = v*`, `s̃ = s̃*`, `i = i*`. -/
theorem modelB_unique (hρ : ρ ≠ 0) {φ : ℝ} (hφ : 1 < |φ|)
    (hT : Target 𝔼 ρ α βs η ε is πs s vs u) {sB : ℕ → Ω → ℝ}
    (h : ActiveMoney 𝔼 ρ α φ η ε is πs i π sB v u)
    (hb : BoundedProc (fun t => π t - πs t)) (hv0 : v 0 = vs 0) :
    π = πs ∧ v = vs ∧ (∀ t, sB (t + 1) = s (t + 1)) ∧ i = is := by
  have hφ0 : φ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hφ
    linarith
  have hφi : |φ⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hφ
  have h₁ : ∀ t, (fun t => π t - πs t) t =
      φ⁻¹ • 𝔼.E t ((fun t => π t - πs t) (t + 1)) + (0 : ℕ → Ω → ℝ) t := fun t => by
    simp only [Pi.zero_apply, add_zero, map_sub]
    rw [← (h t).1, ← (hT.1 t).1, (h t).2.1, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hφ0, one_smul]
  have h₂ : ∀ t, (fun _ => (0 : Ω → ℝ)) t =
      φ⁻¹ • 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1)) + (0 : ℕ → Ω → ℝ) t := fun t => by simp
  have hx := 𝔼.forward_unique hφi h₁ h₂ hb ⟨0, fun t ω => by simp⟩
  have hππ : ∀ t, π t = πs t := fun t => sub_eq_zero.mp (congrFun hx t)
  have hπeq : π = πs := funext hππ
  have hvv : ∀ t, v t = vs t := by
    intro t
    induction t with
    | zero => exact hv0
    | succ t ih =>
      refine smul_right_injective _ hρ ?_
      obtain ⟨-, -, h3, h4, -⟩ := h t
      obtain ⟨p1, p2, -⟩ := hT.2 t
      change ρ • v (t + 1) = ρ • vs (t + 1)
      rw [h4, h3, p2, p1, ih, hπeq, (hT.1 t).2]
      abel
  refine ⟨hπeq, funext hvv, fun t => ?_, funext fun t => ?_⟩
  · rw [(h t).2.2.1, hvv t, (hT.2 t).1]
  · rw [(h t).2.1, hππ t, sub_self, smul_zero, add_zero]

/-- Cochrane (2023), p. 140 (observational equivalence): the active-fiscal/passive-money model
(5.29)–(5.34) (with `i = i*`, selection by the transversality condition) and the
active-money/passive-fiscal model (5.42) (`|φ| > 1`, selection by bounded `π − π*`) have the
same equilibrium observables `(π_{t+1}, i_t, s̃_{t+1}, v_t)` — those of the target. -/
theorem observationally_equivalent (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {φ : ℝ} (hφ : 1 < |φ|) (hT : Target 𝔼 ρ α βs η ε is πs s vs u)
    (hεa : 𝔼.Adapted ε) (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0)
    (hu0 : 𝔼.E 0 (u 0) = u 0) {πA vA : ℕ → Ω → ℝ}
    (hA : VStarModel 𝔼 ρ α βs η ε is πA πs s vA vs u) (hvA : 𝔼.Adapted vA)
    (htvA : TVC 𝔼 ρ vA) {iB πB sB vB : ℕ → Ω → ℝ}
    (hB : ActiveMoney 𝔼 ρ α φ η ε is πs iB πB sB vB u)
    (hbB : BoundedProc (fun t => πB t - πs t)) (hvB0 : vB 0 = vs 0) :
    ∀ t, πA (t + 1) = πB (t + 1) ∧ is t = iB t ∧ s (t + 1) = sB (t + 1) ∧ vA t = vB t := by
  obtain ⟨hπA, hvA'⟩ := modelA_unique 𝔼 hρ hα hη hT hA hεa hε hv0 hu0 hvA htvA
  obtain ⟨hπB', hvB', hsB, hiB⟩ := modelB_unique 𝔼 hρ hφ hT hB hbB hvB0
  intro t
  exact ⟨by rw [hπA, hπB'], by rw [hiB], (hsB t).symm, by rw [hvA', hvB']⟩

/-! ### Survey E31: when `v*` is stationary -/

/-- Cochrane (2023), p. 138 ("it is stationary for α > 1 − ρ"), survey E31: with bounded shocks
`v*` is bounded when `|1 − α| < ρ`, i.e. `1 − ρ < α < 1 + ρ` (the upper bound is missing). -/
theorem vstar_bounded (hρ : 0 < ρ) (hα : |1 - α| < ρ) (h : IsSurplusProc ρ α βs η ε s vs u)
    {Mε Mu V : ℝ} (hεb : ∀ t ω, |ε t ω| ≤ Mε) (hub : ∀ t ω, |u t ω| ≤ Mu)
    (hv0 : ∀ ω, |vs 0 ω| ≤ V) : BoundedProc vs := by
  refine gamma_bounded (γ := α) hρ hα (δ := fun t => -(βs • ε (t + 1))) (Mδ := |βs| * Mε)
    (fun t => ?_) (fun t ω => ?_) hub hv0
  · rw [vstar_rec h t]
    abel
  · simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left (hεb _ _) (abs_nonneg _)

/-- Cochrane (2023), p. 138, survey E31: for `|1 − α| > ρ` (e.g. `α > 1 + ρ`) `v*` explodes even
with no shocks: `v*_t = gᵗ`, `g = (1 − α)/ρ`, solves (5.22)–(5.24) with `ε = u = 0`. -/
theorem vstar_unbounded [Nonempty Ω] (hρ : 0 < ρ) (hα : ρ < |1 - α|) :
    ∃ s' vs' : ℕ → Ω → ℝ, IsSurplusProc ρ α βs η 0 s' vs' 0 ∧ ¬ BoundedProc vs' := by
  refine ⟨succPath (fun t => α • fun _ => ((1 - α) / ρ) ^ t), fun t _ => ((1 - α) / ρ) ^ t,
    fun t => ⟨by simp [succPath], ?_, by simp⟩, not_bounded_pow ?_⟩
  · funext ω
    simp only [succPath, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul,
      mul_zero, add_zero, pow_succ]
    field_simp
  · rw [abs_div, abs_of_pos hρ, one_lt_div hρ]
    exact hα

/-- Cochrane (2023), p. 138 ("v* grows at less than the steady-state interest rate for α > 0"),
survey E31: for `0 ≤ ρ < 1`, `0 < α < 2` and bounded shocks, `ρᵀ v*_T → 0` along every path. -/
theorem vstar_discounted (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hα : |1 - α| < 1)
    (h : IsSurplusProc ρ α βs η ε s vs u) {Mε Mu : ℝ} (hεb : ∀ t ω, |ε t ω| ≤ Mε)
    (hub : ∀ t ω, |u t ω| ≤ Mu) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * vs T ω) atTop (𝓝 0) := by
  have hf : Summable (fun T => ρ ^ T * (βs * ε (T + 1) ω - u (T + 1) ω)) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_right (|βs| * Mε + Mu)) (fun T => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 T)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ0 T)
    calc |βs * ε (T + 1) ω - u (T + 1) ω| ≤ |βs * ε (T + 1) ω| + |u (T + 1) ω| := abs_sub _ _
      _ ≤ |βs| * Mε + Mu := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hεb _ _) (abs_nonneg _)) (hub _ _)
  refine tendsto_zero_of_rec hα hf (fun T => ?_)
  have hr := congrFun (vstar_rec h T) ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hr
  rw [pow_succ, mul_assoc, hr]
  ring

/-- Cochrane (2023), p. 138, survey E31: without `α < 2` (for `|1 − α| ≥ 1`) the discounted
latent debt need not vanish: `v*_t = gᵗ` with no shocks has `ρᵀ v*_T = (1 − α)ᵀ`. -/
theorem vstar_discounted_fails [Nonempty Ω] (hρ : ρ ≠ 0) (hα : 1 ≤ |1 - α|) :
    ∃ s' vs' : ℕ → Ω → ℝ, IsSurplusProc ρ α βs η 0 s' vs' 0 ∧
      ¬ ∀ ω, Tendsto (fun T => ρ ^ T * vs' T ω) atTop (𝓝 0) := by
  refine ⟨succPath (fun t => α • fun _ => ((1 - α) / ρ) ^ t), fun t _ => ((1 - α) / ρ) ^ t,
    fun t => ⟨by simp [succPath], ?_, by simp⟩, fun H => ?_⟩
  · funext ω
    simp only [succPath, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul,
      mul_zero, add_zero, pow_succ]
    field_simp
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have ht := H ω
    have : (fun T : ℕ => ρ ^ T * ((1 - α) / ρ) ^ T) = fun T => (1 - α) ^ T := by
      funext T
      rw [← mul_pow, mul_div_cancel₀ _ hρ]
    rw [this, tendsto_pow_atTop_nhds_zero_iff] at ht
    linarith

/-! ### §5.4.4: thinking about the parameters -/

/-- Cochrane (2023), §5.4.4, p. 146 (AR(1) surplus in the frictionless model), survey E38: with
`s̃_{t+1} = η s̃_t + ε_{t+1}`, any debt path satisfying the transversality condition has
`ΔE_{t+1} π_{t+1} = −a(ρ) ε_{t+1} = −ε_{t+1}/(1 − ρη)` (the book prints `+ε_{t+1}/(1 − ρη)`). -/
theorem ar1_surplus_inflation (hη : |ρ * η| < 1) (hf : Frictionless 𝔼 ρ i π s v)
    (hs : 𝔼.Adapted s) (hsr : ∀ t, s (t + 1) = η • s t + ε (t + 1)) (hε : MeanZero 𝔼 ε)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    surprise 𝔼 π t = -((1 - ρ * η)⁻¹ • ε (t + 1)) := by
  have hAR : 𝔼.IsAR1 η s := ⟨hs, fun t => by rw [hsr, map_add, map_smul, hs t, hε t, add_zero]⟩
  have hEs : ∀ r j, 𝔼.E r (s (r + 1 + j)) = η ^ (1 + j) • s r := fun r j => by
    rw [show r + 1 + j = r + (1 + j) by omega, 𝔼.ar1_iterate hAR r (1 + j)]
  have hsum : ∀ r ω, Summable (fun j => ρ ^ j * 𝔼.E r (s (r + 1 + j)) ω) := fun r ω => by
    refine ((summable_geometric_of_abs_lt_one hη).mul_left (η * s r ω)).congr fun j => ?_
    rw [hEs r j, Pi.smul_apply, smul_eq_mul, mul_pow, pow_add]
    ring
  funext ω
  have H := unexpected_inflation_527 𝔼 hf hv htvc t (hs (t + 1)) ω (hsum t ω)
    (by simpa [add_assoc] using hsum (t + 1) ω)
  have H2 : HasSum (fun j => ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω))
      ((1 - ρ * η)⁻¹ * ε (t + 1) ω) := by
    refine ((hasSum_geometric_of_abs_lt_one hη).mul_right (ε (t + 1) ω)).congr_fun ?_
    intro j
    rw [𝔼.ar1_iterate hAR (t + 1) j, hEs t j]
    have hr := congrFun (hsr t) ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hr ⊢
    rw [hr, mul_pow, pow_add]
    ring
  have := H.unique H2
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Cochrane (2023), §5.4.4, p. 146, survey E38: the printed sign is wrong: whenever
`ε_{t+1} ≠ 0`, unexpected inflation is not `+ε_{t+1}/(1 − ρη)`. -/
theorem printed_e38_false (hη : |ρ * η| < 1) (hf : Frictionless 𝔼 ρ i π s v)
    (hs : 𝔼.Adapted s) (hsr : ∀ t, s (t + 1) = η • s t + ε (t + 1)) (hε : MeanZero 𝔼 ε)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) (ω : Ω) (hne : ε (t + 1) ω ≠ 0) :
    surprise 𝔼 π t ω ≠ (1 - ρ * η)⁻¹ * ε (t + 1) ω := by
  have h := congrFun (ar1_surplus_inflation 𝔼 hη hf hs hsr hε hv htvc t) ω
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h
  have hpos : 0 < 1 - ρ * η := by linarith [(abs_lt.mp hη).2]
  intro h'
  have : (1 - ρ * η)⁻¹ * ε (t + 1) ω = 0 := by linarith
  exact hne ((mul_eq_zero.mp this).resolve_left (inv_ne_zero hpos.ne'))

/-- Cochrane (2023), §5.4.4, p. 146: `a_u(ρ) = ∑ ρʲ ηʲ = 1/(1 − ρη)` (positive; the response of
`∑_{j ≥ 1} ρ^{j−1} u_j` to a unit *deficit* shock is `−a_u(ρ)`, `fig55_u_pv`; survey E38). -/
theorem au_rho (hη : |ρ * η| < 1) : HasSum (fun j : ℕ => ρ ^ j * η ^ j) (1 - ρ * η)⁻¹ := by
  simpa [mul_pow] using hasSum_geometric_of_abs_lt_one hη

/-- Cochrane (2023), §5.4.4, p. 146: with the proposed `β_s = β_{s,0}/(1 − ρη)` the government
inflates away the same fraction of the overall deficit shock, `a(ρ) = β_{s,0} a_u(ρ)`, so
unexpected inflation `β_{s,0}/(1 − ρη)` (per unit shock) rises with persistence `η`. -/
theorem scaled_inflation_increasing (hρ : 0 < ρ) {βs0 η₁ η₂ : ℝ} (hb : 0 < βs0)
    (h12 : η₁ < η₂) (h2 : ρ * η₂ < 1) :
    βs0 * (1 - ρ * η₁)⁻¹ < βs0 * (1 - ρ * η₂)⁻¹ := by
  have hp2 : 0 < 1 - ρ * η₂ := by linarith
  have hlt : 1 - ρ * η₂ < 1 - ρ * η₁ := by nlinarith
  exact mul_lt_mul_of_pos_left (inv_strictAnti₀ hp2 hlt) hb

/-- Cochrane (2023), §5.4.4, p. 146 ("If you hold β_s constant … those parameters cannot produce
a different value of unexpected inflation"): with `β_s = β_{s,0}/(1 − ρη)` the equilibrium of
`equilibrium_528` has `ΔE_{t+1} π_{t+1} = −β_{s,0} a_u(ρ) ε_{t+1}`. -/
theorem scaled_unexpected_inflation (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {βs0 : ℝ} (h : IsSurplusProc ρ α (βs0 * (1 - ρ * η)⁻¹) η ε s vs u) (hεa : 𝔼.Adapted ε)
    (hε : MeanZero 𝔼 ε) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (u 0) = u 0)
    (hf : Frictionless 𝔼 ρ i π s v) (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    surprise 𝔼 π t = -((βs0 * (1 - ρ * η)⁻¹) • ε (t + 1)) :=
  (equilibrium_528 𝔼 hρ hα hη h hεa hε hv0 hu0 hf hv htvc t).2

end Cochrane.StickyPriceFiscal.ActivePassive
