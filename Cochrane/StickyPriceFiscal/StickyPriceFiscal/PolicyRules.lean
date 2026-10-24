/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.BKCopy
import StickyPriceFiscal.SharedTools

/-!
# Responses and rules: the sticky-price fiscal model with policy rules

Cochrane (2023), Chapter 5, §5.5 "Responses and rules", pp. 147–160, eqs. (5.51)–(5.81), and
Online Appendix A1 §1.9 (pp. 573–577, the matrix method and the minimum-state-variable example
§1.9.1) and §1.11 (pp. 578–579, the matrix of the §5.5 model).

All model equations are stated for an arbitrary `ExpectationSystem` (perfect foresight and
genuine uncertainty alike), as equalities of random variables at every date. The innovation
`ΔE_{t+1} y = E_{t+1} y − E_t y` is `SharedTools.innov`. The definitional equations (5.53)
(interest-rate rule), (5.54)/(5.69) (surplus rule) and (5.60)/(5.73) (bond return) only define
one variable in terms of others; as in A1 §1.9 ("I use them to eliminate `i_t` and `s_t`") they
are the definitions `iRule`, `sNext`, `rnNext`, and the unknowns are output `x`, inflation `p`,
the log bond price `q`, the value of debt `v` (and in the full model `v*`, `π*`).

## Main results

* `eq_563` — the differenced fiscal equation (5.63), with the correct date (`π_{t+1}`, not the
  printed `π_t`; `printed_563_false`). `full_elim`: for `0 < ρ < 1` every bounded solution of the
  full model has `v* = v` and `π*_{t+1} = π_{t+1}`; `rho_one_not_elim`: at `ρ = 1` boundedness
  does not select `v* = v`. `full_to_red`, `red_to_full`: the full model (5.51)–(5.62) and the
  reduced model (5.64)–(5.73) have the same equilibria.
* The `(x, π)` block in Blanchard–Kahn form, with `π̂_{t+1} = π_{t+1} + β_sε_{s,t+1} +
  β_iε_{i,t+1} = E_tπ_{t+1}` predetermined (`blockMat`, `block_iff`). Its eigenvalues
  (`eigs_blockMat`), `charB_one`: `p(1) = (σ/β)(κ(θ_iπ − 1) + (1 − β)θ_ix)`.
  `stable_one_iff_passive`: one eigenvalue inside and none on the unit circle iff the
  passive-money condition `κ(θ_iπ − 1) + (1 − β)θ_ix < 0`. **Genericity** (the open item of the
  survey): `genericX_iff_kappa_ne_zero` —
  under that count the Blanchard–Kahn genericity condition holds iff
  `κ ≠ 0` (`not_genericX_of_kappa_zero`). `block_determinate_iff`: the block is determinate iff
  the passive-money condition holds.
* **`policyRules_determinate`**: under the passive-money condition, `0 ≤ ω < 1` and
  `|1 − α| < ρ` (so `α ∈ (1 − ρ, 1 + ρ)`), for every initial inflation and debt the reduced model
  has exactly one bounded equilibrium; `policyRules_full_determinate` for the full model.
  Necessity: `nonexist_of_active` (active money: no equilibrium for some initial inflation),
  `block_not_determinate_of_boundary` (a unit root, A1's "≥ 1", E20), `nonexist_of_alpha`.
  `thetaIpi_lt_one_insufficient` (E43): `θ_iπ < 1` alone is not enough.
* `closed_form`: in every equilibrium `x_t = g π_t − σ/(λ_u − η_i) u_{i,t}` and
  `E_tπ_{t+1} = λ_s π_t + κσ/(β(λ_u − η_i)) u_{i,t}`; consequences for §5.5.2–5.5.5
  (AR(1) inflation after fiscal shocks, output rises with inflation, unexpected output,
  `β_s = 0` gives no inflation).
* (5.74): `innov_sNext`, `betaHat_574`.
* (5.75)/(5.80) and E40: `fiscal_shock_sums`, `betaS_of_ratio` (`β_s = 0.4(1 − ωλ_s)/(1 − ρη_s)`),
  `lamS_bookRules`, `lamS_bookNoRules`, `rules_more_persistent`, `betaS_bookNoRules` (0.36),
  `betaS_bookRules_etaS` (0.14 needs `η_s = 0.5`), `table51_fiscal_yesRule_etaS`.
* Table 5.1: the identities (3.20), (3.21), (3.22) for every bounded solution
  (`identity_320`, `identity_321`, `identity_322`), and the corrected entries (E41):
  `table51_monetary_noRule_printed_false`, `table51_monetary_noRule_corrected` (2.58 → 0.26),
  `table51_monetary_noRule_panel1`, `table51_panel3`, `table51_order_of_magnitude_false`.
* A1 §1.9 and §1.11: `appA1_19_eigs` (eigenvalues `ρ⁻¹, η_i, η_s, λ±`), the corrected `λ±`
  (`appA1_lambda_pm`, `printed_lambda_pm_false`, E19), the counts `appA1_19_passive`,
  `appA1_19_active`, `appA1_19_unit` (E20), `appA1_111_eigs`, `appA1_111_count`,
  `appA1_111_rows`, and §1.9.1 with the sign corrected (`msv_unique`, `msv_exists`,
  `printed_msv_false`, `msv_B_coefficient`, E21).
* **Boundary cases at model level** (`ModelDeterminate`: unique bounded equilibrium for every
  admissible shock process and initial condition): `policyRules_unique` (at most one equilibrium
  for every `α`); `alpha_exists_iff` (for `|1 − α| ≥ ρ` an equilibrium exists iff the
  shock-driven part of debt `W_{t+1} = φW_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}` is bounded);
  `alpha_iff_pf` (perfect foresight: determinate iff `|1 − α| ≤ ρ`); `alpha_iff_trunc`
  (recurring news, `truncSystem`: determinate iff `|1 − α| < ρ`, or `|1 − α| = ρ` with
  `κ_s = κ_i = 0`). The unit root `κ(θ_iπ − 1) + (1 − β)θ_ix = 0`: `unitroot_unique`,
  `unitroot_exists_iff`, `unitroot_pf` (determinate under perfect foresight),
  `unitroot_iff_trunc` (with recurring news determinate iff `β_s = 0`, `β_i = k`).
-/

namespace Cochrane.StickyPriceFiscal.PolicyRules

open Filter Topology BKCopy.InvariantSplit BKCopy.GeneralBKForward BKCopy.GeneralBK
open SharedTools (innov innov_apply E_succ_of_adapted innov_known innov_succ innov_add innov_smul
  innov_sub abs_innov_le E_ar1 innov_ar1 bounded_of_rec)
open scoped Matrix

/-! ### Parameters, shocks and the model -/

/-- Cochrane (2023), eqs. (5.51)–(5.62), p. 147: the parameters of the sticky-price model with
policy rules and long-term debt. `omega` is the bond-return coefficient of (5.60) (the exact
first-order weight of Online Appendix (1.22)). -/
structure Params where
  /-- `σ`, the intertemporal substitution elasticity in (5.51). -/
  sigma : ℝ
  /-- `κ`, the Phillips-curve slope in (5.52). -/
  kappa : ℝ
  /-- `β`, the discount factor in (5.52). -/
  beta : ℝ
  /-- `θ_iπ`, the interest-rate reaction to inflation in (5.53). -/
  thIpi : ℝ
  /-- `θ_ix`, the interest-rate reaction to output in (5.53). -/
  thIx : ℝ
  /-- `θ_sπ`, the surplus reaction to inflation in (5.54). -/
  thSpi : ℝ
  /-- `θ_sx`, the surplus reaction to output in (5.54). -/
  thSx : ℝ
  /-- `α`, the surplus reaction to the value of debt in (5.54). -/
  alpha : ℝ
  /-- `ρ`, the linearisation constant of the flow identity (5.55)–(5.56). -/
  rho : ℝ
  /-- `ω`, the maturity parameter of (5.60). -/
  omega : ℝ
  /-- `η_i`, the persistence of the monetary disturbance (5.61). -/
  etaI : ℝ
  /-- `η_s`, the persistence of the fiscal disturbance (5.62). -/
  etaS : ℝ
  /-- `β_s`, the loading of unexpected inflation on the fiscal shock in (5.58). -/
  betaS : ℝ
  /-- `β_i`, the loading of unexpected inflation on the monetary shock in (5.58). -/
  betaI : ℝ

/-- Cochrane (2023), p. 147 (tool for counterexamples): all parameters zero. -/
def zeroParams : Params := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (5.61)–(5.62), p. 147: the exogenous disturbances. The shocks
`ε_i, ε_s` are bounded, adapted and unpredictable (`E_t ε_{t+1} = 0`); the disturbances
`u_i, u_s` are bounded adapted AR(1) processes driven by them. -/
def Shocks (P : Params) (ei es ui us : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted ei ∧ 𝔼.Adapted es ∧ 𝔼.Adapted ui ∧ 𝔼.Adapted us ∧
  BoundedProc ei ∧ BoundedProc es ∧ BoundedProc ui ∧ BoundedProc us ∧
  (∀ t, 𝔼.E t (ei (t + 1)) = 0) ∧ (∀ t, 𝔼.E t (es (t + 1)) = 0) ∧
  (∀ t, ui (t + 1) = P.etaI • ui t + ei (t + 1)) ∧ (∀ t, us (t + 1) = P.etaS • us t + es (t + 1))

/-- Cochrane (2023), (5.53)/(5.66), p. 147: the interest-rate rule
`i_t = θ_iπ π_t + θ_ix x_t + u_{i,t}`. -/
def iRule (P : Params) (x p ui : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  P.thIpi • p t + P.thIx • x t + ui t

/-- Cochrane (2023), (5.54)/(5.69), p. 147: the surplus rule
`s̃_{t+1} = θ_sπ π_{t+1} + θ_sx x_{t+1} + α v_t + u_{s,t+1}` (with `v*` in place of `v` in the full
model). -/
def sNext (P : Params) (x p v us : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  P.thSpi • p (t + 1) + P.thSx • x (t + 1) + P.alpha • v t + us (t + 1)

/-- Cochrane (2023), (5.60)/(5.73), p. 147: the nominal bond return `r^n_{t+1} = ω q_{t+1} − q_t`.
-/
def rnNext (P : Params) (q : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := P.omega • q (t + 1) - q t

/-- Cochrane (2023), eqs. (5.51)–(5.62), p. 147: the full model, with the latent value `v*` and
inflation target `π*`: (5.51) IS curve, (5.52) Phillips curve, (5.55) `v*` flow, (5.56) debt flow,
(5.57) `E_tπ*_{t+1} = E_tπ_{t+1}`, (5.58) unexpected `π*`, (5.59)–(5.60) expectations hypothesis
(with (5.53), (5.54), (5.60) substituted). -/
def FullSys (P : Params) (ei es ui us x p q v vs ps : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1)))) ∧
  (∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t) ∧
  (∀ t, P.rho • vs (t + 1) = vs t + rnNext P q t - ps (t + 1) - sNext P x p vs us t) ∧
  (∀ t, P.rho • v (t + 1) = v t + rnNext P q t - p (t + 1) - sNext P x p vs us t) ∧
  (∀ t, 𝔼.E t (ps (t + 1)) = 𝔼.E t (p (t + 1))) ∧
  (∀ t, innov 𝔼 t (ps (t + 1)) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)) ∧
  (∀ t, 𝔼.E t (rnNext P q t) = iRule P x p ui t)

/-- Cochrane (2023), p. 148: an equilibrium of the full model — a bounded adapted solution with
given initial inflation `π_0` and initial value of debt `v_0`. -/
def FullEquil (P : Params) (ei es ui us : ℕ → Ω → ℝ) (p0 v0 : ℝ)
    (x p q v vs ps : ℕ → Ω → ℝ) : Prop :=
  FullSys 𝔼 P ei es ui us x p q v vs ps ∧
  𝔼.Adapted x ∧ 𝔼.Adapted p ∧ 𝔼.Adapted q ∧ 𝔼.Adapted v ∧ 𝔼.Adapted vs ∧ 𝔼.Adapted ps ∧
  BoundedProc x ∧ BoundedProc p ∧ BoundedProc q ∧ BoundedProc v ∧ BoundedProc vs ∧
  BoundedProc ps ∧ p 0 = (fun _ => p0) ∧ v 0 = (fun _ => v0)

/-- Cochrane (2023), eqs. (5.64)–(5.73), pp. 148–149: the reduced model, with (5.66), (5.69),
(5.73) substituted: (5.64) IS curve, (5.65) Phillips curve, (5.68) unexpected inflation, (5.71)
debt flow, (5.72) expectations hypothesis. -/
def RedSys (P : Params) (ei es ui us x p q v : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1)))) ∧
  (∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t) ∧
  (∀ t, innov 𝔼 t (p (t + 1)) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)) ∧
  (∀ t, P.rho • v (t + 1) = v t + rnNext P q t - p (t + 1) - sNext P x p v us t) ∧
  (∀ t, 𝔼.E t (rnNext P q t) = iRule P x p ui t)

/-- Cochrane (2023), pp. 148–149: an equilibrium of the reduced model — a bounded adapted
solution with given initial inflation `π_0` and initial value of debt `v_0`. -/
def RedEquil (P : Params) (ei es ui us : ℕ → Ω → ℝ) (p0 v0 : ℝ) (x p q v : ℕ → Ω → ℝ) :
    Prop :=
  RedSys 𝔼 P ei es ui us x p q v ∧
  𝔼.Adapted x ∧ 𝔼.Adapted p ∧ 𝔼.Adapted q ∧ 𝔼.Adapted v ∧
  BoundedProc x ∧ BoundedProc p ∧ BoundedProc q ∧ BoundedProc v ∧
  p 0 = (fun _ => p0) ∧ v 0 = (fun _ => v0)

/-! ### (5.63): eliminating `v*` and `π*` -/

/-- Cochrane (2023), (5.63), p. 148 (corrected, E39): differencing (5.55) and (5.56),
`ρ(v*_{t+1} − v_{t+1}) = (v*_t − v_t) − (π*_{t+1} − π_{t+1})`. -/
theorem eq_563 {P : Params} {x p q v vs ps us : ℕ → Ω → ℝ}
    (h55 : ∀ t, P.rho • vs (t + 1) = vs t + rnNext P q t - ps (t + 1) - sNext P x p vs us t)
    (h56 : ∀ t, P.rho • v (t + 1) = v t + rnNext P q t - p (t + 1) - sNext P x p vs us t)
    (t : ℕ) :
    P.rho • (vs (t + 1) - v (t + 1)) = (vs t - v t) - (ps (t + 1) - p (t + 1)) := by
  rw [smul_sub, h55 t, h56 t]
  abel

/-- Cochrane (2023), (5.63), p. 148 (E39): the printed form, with `π_t` in place of `π_{t+1}`,
is false — a solution of (5.55)–(5.56) (with `ρ = 1`) violating it. -/
theorem printed_563_false : ∃ (P : Params) (x p q v vs ps us : ℕ → Unit → ℝ),
    (∀ t, P.rho • vs (t + 1) = vs t + rnNext P q t - ps (t + 1) - sNext P x p vs us t) ∧
    (∀ t, P.rho • v (t + 1) = v t + rnNext P q t - p (t + 1) - sNext P x p vs us t) ∧
    ¬ (P.rho • (vs 1 - v 1) = (vs 0 - v 0) - (ps 1 - p 0)) := by
  refine ⟨{ zeroParams with rho := 1 },
    0, fun t _ => if t = 0 then 0 else 1, 0, fun t _ => -(t : ℝ), fun t _ => -(t : ℝ),
    fun t _ => if t = 0 then 0 else 1, 0, fun t => ?_, fun t => ?_, ?_⟩
  · funext ω
    simp [rnNext, sNext, zeroParams]
    ring
  · funext ω
    simp [rnNext, sNext, zeroParams]
    ring
  · intro h
    have := congrFun h ()
    norm_num at this

/-- Cochrane (2023), p. 148 ("this equation has a forward-looking … root. Therefore, the unique
stationary equilibrium … includes `v_t = v*_t`, `π_t = π*_t`"): for `0 < ρ < 1`, every solution
of the full model with bounded adapted `v`, `v*` has `v* = v` and `π*_{t+1} = π_{t+1}` at every
date. -/
theorem full_elim {P : Params} (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1)
    {ei es ui us x p q v vs ps : ℕ → Ω → ℝ} (h : FullSys 𝔼 P ei es ui us x p q v vs ps)
    (hv : 𝔼.Adapted v) (hvs : 𝔼.Adapted vs) (hbv : BoundedProc v) (hbvs : BoundedProc vs) :
    vs = v ∧ ∀ t, ps (t + 1) = p (t + 1) := by
  obtain ⟨-, -, h55, h56, h57, -, -⟩ := h
  set d : ℕ → Ω → ℝ := fun t => vs t - v t with hd_def
  have hdiff := eq_563 h55 h56
  have hd : ∀ t, d t = P.rho • 𝔼.E t (d (t + 1)) + 0 := by
    intro t
    have e := congrArg (𝔼.E t) (hdiff t)
    rw [map_smul, map_sub, map_sub, map_sub, map_sub, hvs t, hv t, h57 t, sub_self,
      sub_zero] at e
    simp only [hd_def, add_zero, map_sub, e]
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = P.rho • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have hbd : BoundedProc d := by
    obtain ⟨M₁, hM₁⟩ := hbv
    obtain ⟨M₂, hM₂⟩ := hbvs
    exact ⟨M₂ + M₁, fun t ω => (abs_sub _ _).trans (add_le_add (hM₂ t ω) (hM₁ t ω))⟩
  have hρ : |P.rho| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have h0 := 𝔼.forward_unique hρ hd hz hbd ⟨0, fun _ _ => by simp⟩
  have hvv : vs = v := by
    funext t ω
    have := congrFun (congrFun h0 t) ω
    simpa [hd_def, sub_eq_zero] using this
  refine ⟨hvv, fun t => ?_⟩
  have e := hdiff t
  rw [hvv, sub_self, sub_self, smul_zero, zero_sub, zero_eq_neg] at e
  exact sub_eq_zero.mp e

/-- Cochrane (2023), p. 148 ("The parameter `ρ ≤ 1`, so this equation has a forward-looking or
unit root. Therefore …"): at `ρ = 1` boundedness does not select `v* = v` — a bounded
perfect-foresight solution of the full model with `v* ≠ v`. -/
theorem rho_one_not_elim : ∃ (P : Params) (ei es ui us x p q v vs ps : ℕ → Unit → ℝ),
    P.rho = 1 ∧ FullSys perfectForesight P ei es ui us x p q v vs ps ∧
    perfectForesight.Adapted v ∧ perfectForesight.Adapted vs ∧
    BoundedProc v ∧ BoundedProc vs ∧ vs ≠ v := by
  refine ⟨{ zeroParams with rho := 1 },
    0, 0, 0, 0, 0, 0, 0, 0, fun _ _ => 1, 0, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun _ => rfl, fun _ => rfl, ⟨0, fun _ _ => by simp⟩, ⟨1, fun _ _ => by simp⟩, ?_⟩
  · intro t; funext ω; simp [iRule]
  · intro t; funext ω; simp
  · intro t; funext ω; simp [rnNext, sNext, zeroParams]
  · intro t; funext ω; simp [rnNext, sNext, zeroParams]
  · intro t; rfl
  · intro t; funext ω; simp [innov]
  · intro t; funext ω; simp [rnNext, iRule, perfectForesight]
  · intro h
    have := congrFun (congrFun h 0) ()
    norm_num at this

/-- Cochrane (2023), pp. 148–149 ("we can also now just eliminate the ∗ variables, citing
(5.63)"): for `0 < ρ < 1`, an equilibrium of the full model (5.51)–(5.62) is an equilibrium of the
reduced model (5.64)–(5.73), with `v* = v` and `π*_{t+1} = π_{t+1}`. -/
theorem full_to_red {P : Params} (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1)
    {ei es ui us x p q v vs ps : ℕ → Ω → ℝ} {p0 v0 : ℝ}
    (h : FullEquil 𝔼 P ei es ui us p0 v0 x p q v vs ps) :
    RedEquil 𝔼 P ei es ui us p0 v0 x p q v ∧ vs = v ∧ ∀ t, ps (t + 1) = p (t + 1) := by
  obtain ⟨hs, hax, hap, haq, hav, havs, -, hbx, hbp, hbq, hbv, hbvs, -, hp0, hv0⟩ := h
  obtain ⟨hvv, hpp⟩ := full_elim 𝔼 hρ0 hρ1 hs hav havs hbv hbvs
  obtain ⟨h51, h52, -, h56, -, h58, h59⟩ := hs
  refine ⟨⟨⟨h51, h52, fun t => ?_, fun t => ?_, h59⟩, hax, hap, haq, hav, hbx, hbp, hbq, hbv,
    hp0, hv0⟩, hvv, hpp⟩
  · rw [← hpp t]; exact h58 t
  · have := h56 t; rwa [hvv] at this

/-- Cochrane (2023), pp. 148–149: conversely an equilibrium of the reduced model, with
`v* = v` and `π* = π`, is an equilibrium of the full model. -/
theorem red_to_full {P : Params} {ei es ui us x p q v : ℕ → Ω → ℝ} {p0 v0 : ℝ}
    (h : RedEquil 𝔼 P ei es ui us p0 v0 x p q v) :
    FullEquil 𝔼 P ei es ui us p0 v0 x p q v v p := by
  obtain ⟨⟨h64, h65, h68, h71, h72⟩, hax, hap, haq, hav, hbx, hbp, hbq, hbv, hp0, hv0⟩ := h
  exact ⟨⟨h64, h65, h71, h71, fun _ => rfl, h68, h72⟩, hax, hap, haq, hav, hav, hap, hbx, hbp,
    hbq, hbv, hbv, hbp, hp0, hv0⟩

/-! ### The `(x, π)` block in Blanchard–Kahn form -/

/-- Online Appendix A1 §1.11, p. 578 (tool): the determinant of a `2 × 2` matrix indexed by
`Fin 1 ⊕ Fin 1`. -/
theorem det_sum11 {R : Type*} [CommRing R] (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    M.det = M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) -
      M (Sum.inl 0) (Sum.inr 0) * M (Sum.inr 0) (Sum.inl 0) := by
  rw [← Matrix.det_reindex_self finSumFinEquiv, Matrix.det_fin_two]
  simp [Matrix.reindex_apply]
  rfl

/-- Online Appendix A1 §1.11, p. 578: the `x`–`x` entry `1 + σκ/β + σθ_ix` of the transition
matrix of the `(x, π)` block. -/
noncomputable def aXX (P : Params) : ℝ := 1 + P.sigma * P.kappa / P.beta + P.sigma * P.thIx

/-- Online Appendix A1 §1.11, p. 578: the `x`–`π` entry `σθ_iπ − σ/β`. -/
noncomputable def aXP (P : Params) : ℝ := P.sigma * (P.thIpi - 1 / P.beta)

/-- Online Appendix A1 §1.11, p. 579: the `π`–`x` entry `−κ/β`. -/
noncomputable def aPX (P : Params) : ℝ := -(P.kappa / P.beta)

/-- Online Appendix A1 §1.11, p. 579: the `π`–`π` entry `1/β`. -/
noncomputable def aPP (P : Params) : ℝ := 1 / P.beta

/-- Online Appendix A1 §1.11, pp. 578–579: the transition matrix of the `(x, π)` block of
(5.64)–(5.68), with `x` non-predetermined (`Sum.inl`) and `π̂` predetermined (`Sum.inr`). -/
noncomputable def blockMat (P : Params) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![aXX P] !![aXP P] !![aPX P] !![aPP P]

/-- Online Appendix A1 §1.9, p. 574: the trace of the `(x, π)` block. -/
noncomputable def trB (P : Params) : ℝ := aXX P + aPP P

/-- Online Appendix A1 §1.9, p. 574: the determinant of the `(x, π)` block. -/
noncomputable def detB (P : Params) : ℝ := aXX P * aPP P - aXP P * aPX P

/-- Online Appendix A1 §1.9, p. 574: the characteristic polynomial `z² − tr z + det` of the
`(x, π)` block, as a real function. -/
noncomputable def charB (P : Params) (z : ℝ) : ℝ := z ^ 2 - trB P * z + detB P

/-- Cochrane (2023), §5.5.3, p. 154 (the sign restrictions behind "a stationary passive-money
model"): `σ, κ > 0`, `0 < β < 1` and non-negative interest-rate reactions. -/
def Standard (P : Params) : Prop :=
  0 < P.sigma ∧ 0 < P.kappa ∧ 0 < P.beta ∧ P.beta < 1 ∧ 0 ≤ P.thIpi ∧ 0 ≤ P.thIx

/-- Cochrane (2023), §5.5.3, p. 154 (E43): the passive-money condition
`κ(θ_iπ − 1) + (1 − β)θ_ix < 0`. -/
def Passive (P : Params) : Prop := P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx < 0

/-- Online Appendix A1 §1.9, p. 574: the trace is `1 + 1/β + σκ/β + σθ_ix`. -/
theorem trB_eq (P : Params) :
    trB P = 1 + 1 / P.beta + P.sigma * P.kappa / P.beta + P.sigma * P.thIx := by
  simp only [trB, aXX, aPP]
  ring

/-- Online Appendix A1 §1.9, p. 574: the determinant is `(1 + σθ_ix + σκθ_iπ)/β`. -/
theorem detB_eq {P : Params} (hβ : P.beta ≠ 0) :
    detB P = (1 + P.sigma * P.thIx + P.sigma * P.kappa * P.thIpi) / P.beta := by
  simp only [detB, aXX, aXP, aPX, aPP]
  field_simp
  ring

/-- Cochrane (2023), §5.5.3, p. 154 (E43): the characteristic polynomial at `1` is
`(σ/β)(κ(θ_iπ − 1) + (1 − β)θ_ix)`. -/
theorem charB_one {P : Params} (hβ : P.beta ≠ 0) :
    charB P 1 = P.sigma / P.beta * (P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx) := by
  rw [charB, trB_eq, detB_eq hβ]
  field_simp
  ring

/-- Cochrane (2023), §5.5.3, p. 154: under the sign restrictions the characteristic polynomial is
positive at `−1`. -/
theorem charB_neg_one_pos {P : Params} (hP : Standard P) : 0 < charB P (-1) := by
  obtain ⟨hσ, hκ, hβ0, -, hθπ, hθx⟩ := hP
  have hT := trB_eq P
  have hD := detB_eq hβ0.ne'
  have h1 : 0 < 1 / P.beta := by positivity
  have h2 : 0 < P.sigma * P.kappa / P.beta := by positivity
  have h3 : 0 ≤ P.sigma * P.thIx := by positivity
  have h4 : 0 < (1 + P.sigma * P.thIx + P.sigma * P.kappa * P.thIpi) / P.beta := by positivity
  rw [charB]
  nlinarith

/-- Cochrane (2023), §5.5.3, p. 154: under the sign restrictions the determinant of the
`(x, π)` block exceeds one, so at least one root is explosive. -/
theorem one_lt_detB {P : Params} (hP : Standard P) : 1 < detB P := by
  obtain ⟨hσ, hκ, hβ0, hβ1, hθπ, hθx⟩ := hP
  rw [detB_eq hβ0.ne', lt_div_iff₀ hβ0]
  have : 0 ≤ P.sigma * P.thIx + P.sigma * P.kappa * P.thIpi := by positivity
  linarith

/-- Online Appendix A1 §1.9, p. 574: the characteristic polynomial of the `(x, π)` block,
`det(zI − A) = z² − tr z + det`, over `ℂ`. -/
theorem blockMat_charpoly_eval (P : Params) (z : ℂ) :
    ((blockMat P).map Complex.ofReal).charpoly.eval z =
      z ^ 2 - (trB P : ℂ) * z + (detB P : ℂ) := by
  rw [Matrix.eval_charpoly, det_sum11]
  simp [blockMat, trB, detB, Matrix.scalar_apply]
  ring

/-- Online Appendix A1 §1.9, p. 574: a factorisation of the characteristic polynomial identifies
the eigenvalues of the `(x, π)` block with multiplicity. -/
theorem eigs_blockMat_of_factor {P : Params} {l1 l2 : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - (trB P : ℂ) * z + (detB P : ℂ) = (z - l1) * (z - l2)) :
    eigs (blockMat P) = {l1} + {l2} := by
  have hp : ((blockMat P).map Complex.ofReal).charpoly =
      (Polynomial.X - Polynomial.C l1) * (Polynomial.X - Polynomial.C l2) := by
    refine Polynomial.funext fun z => ?_
    rw [blockMat_charpoly_eval, h z]
    simp
  rw [eigs, hp, Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero l1)
    (Polynomial.X_sub_C_ne_zero l2)), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]

/-- Online Appendix A1 §1.9, p. 574: the eigenvalues of the `(x, π)` block are the two roots of
`z² − tr z + det`. -/
theorem eigs_blockMat (P : Params) :
    eigs (blockMat P) = {root₁ (trB P) (detB P)} + {root₂ (trB P) (detB P)} :=
  eigs_blockMat_of_factor fun z => by
    have hs := root_sum (trB P) (detB P)
    have hp := root_prod (trB P) (detB P)
    linear_combination z * hs - hp

/-- Online Appendix A1 §1.9, p. 574 (tool): the number of eigenvalues of the block in the open
unit disc. -/
theorem stableCount_blockMat (P : Params) :
    stableCount (blockMat P) =
      (if ‖root₁ (trB P) (detB P)‖ < 1 then 1 else 0) +
        (if ‖root₂ (trB P) (detB P)‖ < 1 then 1 else 0) := by
  rw [stableCount, eigs_blockMat, Multiset.filter_add, Multiset.filter_singleton,
    Multiset.filter_singleton]
  split_ifs <;> simp

/-- Online Appendix A1 §1.9, p. 574 (tool): no eigenvalue of the block on the unit circle. -/
theorem noUnit_blockMat_iff (P : Params) :
    NoUnit (blockMat P) ↔
      ‖root₁ (trB P) (detB P)‖ ≠ 1 ∧ ‖root₂ (trB P) (detB P)‖ ≠ 1 := by
  rw [NoUnit, eigs_blockMat]
  simp

/-- Online Appendix A1 §1.9, pp. 574–575 (root location): if a real quadratic `z² − Tz + D` is
negative at `1` and positive at `−1`, its roots are real, one above `1` and one in `(−1, 1)`. -/
theorem real_roots_loc {T D : ℝ} (h1 : 1 - T + D < 0) (hm1 : 0 < 1 + T + D) :
    0 < disc T D ∧ 1 < (T + Real.sqrt (disc T D)) / 2 ∧ -1 < (T - Real.sqrt (disc T D)) / 2 ∧
      (T - Real.sqrt (disc T D)) / 2 < 1 := by
  have hd : disc T D = T ^ 2 - 4 * D := rfl
  have hpos : 0 < disc T D := by rw [hd]; nlinarith [sq_nonneg (T - 2)]
  have hT : 0 < T := by linarith
  set s := Real.sqrt (disc T D) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = T ^ 2 - 4 * D := by rw [hs, Real.sq_sqrt hpos.le, hd]
  have hu : 2 - T < s := by
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul hc hc hs0 (hs0.trans hc)]
  have hl : T - 2 < s := by
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul hc hc hs0 (hs0.trans hc)]
  have hm : s < T + 2 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul hc hc (by linarith : (0 : ℝ) ≤ T + 2) hs0]
  refine ⟨hpos, ?_, ?_, ?_⟩ <;> linarith

/-- Online Appendix A1 §1.9, p. 574 (tool): the two roots, as real numbers, when the discriminant
is non-negative: `z² − Tz + D = (z − (T + √Δ)/2)(z − (T − √Δ)/2)`. -/
theorem quad_factor_real {T D : ℝ} (h : 0 ≤ disc T D) (z : ℝ) :
    z ^ 2 - T * z + D =
      (z - (T + Real.sqrt (disc T D)) / 2) * (z - (T - Real.sqrt (disc T D)) / 2) := by
  have hs := Real.sq_sqrt h
  have hd : disc T D = T ^ 2 - 4 * D := rfl
  nlinarith [hs]

/-- Cochrane (2023), §5.5.3, p. 154 and A1 §1.9, p. 574 (the passive-money count): under the sign
restrictions, the `(x, π)` block has no eigenvalue on the unit circle and exactly one in the open
unit disc iff `κ(θ_iπ − 1) + (1 − β)θ_ix < 0` (E43: not `θ_iπ < 1`). -/
theorem stable_one_iff_passive {P : Params} (hP : Standard P) :
    (NoUnit (blockMat P) ∧ stableCount (blockMat P) = 1) ↔ Passive P := by
  have hβ := hP.2.2.1
  have hm1 := charB_neg_one_pos hP
  have h1 := charB_one hβ.ne'
  have hσβ : 0 < P.sigma / P.beta := div_pos hP.1 hβ
  rw [noUnit_blockMat_iff, stableCount_blockMat]
  set T := trB P with hT
  set D := detB P with hD
  constructor
  · rintro ⟨⟨hn1, hn2⟩, hc⟩
    by_cases hdisc : 0 ≤ disc T D
    · obtain ⟨e1, e2⟩ := norm_root_of_nonneg hdisc
      rw [e1, e2] at hc
      rw [e1] at hn1
      rw [e2] at hn2
      have hs0 : 0 ≤ Real.sqrt (disc T D) := Real.sqrt_nonneg _
      set u := (T + Real.sqrt (disc T D)) / 2 with hu
      set l := (T - Real.sqrt (disc T D)) / 2 with hl
      have hul : l ≤ u := by rw [hu, hl]; linarith
      have hf1 : charB P 1 = (1 - u) * (1 - l) := by
        rw [charB, ← hT, ← hD, quad_factor_real hdisc]
      have hfm : charB P (-1) = (-1 - u) * (-1 - l) := by
        rw [charB, ← hT, ← hD, quad_factor_real hdisc]
      have key : charB P 1 < 0 := by
        rw [hf1]
        split_ifs at hc with hcu hcl hcl
        · norm_num at hc
        · -- `|u| < 1`, `|l| ≥ 1`
          have hl1 : 1 < |l| := lt_of_le_of_ne (not_lt.mp hcl) (Ne.symm hn2)
          rcases abs_lt.mp hcu with ⟨hu1, hu2⟩
          have : l < -1 := by
            rcases lt_abs.mp hl1 with h | h
            · linarith
            · linarith
          rw [hfm] at hm1
          nlinarith
        · have hu1 : 1 < |u| := lt_of_le_of_ne (not_lt.mp hcu) (Ne.symm hn1)
          rcases abs_lt.mp hcl with ⟨hl1, hl2⟩
          have : 1 < u := by
            rcases lt_abs.mp hu1 with h | h
            · exact h
            · linarith
          nlinarith
        · norm_num at hc
      rw [h1] at key
      unfold Passive
      by_contra hc'
      push Not at hc'
      have := mul_nonneg hσβ.le hc'
      linarith
    · push Not at hdisc
      obtain ⟨e1, e2⟩ := normSq_root_of_neg hdisc
      have heq : ‖root₁ T D‖ = ‖root₂ T D‖ := by
        have := e1.trans e2.symm
        nlinarith [norm_nonneg (root₁ T D), norm_nonneg (root₂ T D)]
      rw [heq] at hc
      split_ifs at hc <;> norm_num at hc
  · intro hpass
    have hp1 : charB P 1 < 0 := by
      rw [h1]
      exact mul_neg_of_pos_of_neg hσβ hpass
    have hp1' : 1 - T + D < 0 := by
      have : charB P 1 = 1 - T + D := by rw [charB]; ring
      linarith
    have hm1' : 0 < 1 + T + D := by
      have : charB P (-1) = 1 + T + D := by rw [charB]; ring
      linarith
    obtain ⟨hd, hu, hl1, hl2⟩ := real_roots_loc hp1' hm1'
    obtain ⟨e1, e2⟩ := norm_root_of_nonneg hd.le
    rw [e1, e2]
    have hu' : 1 < |(T + Real.sqrt (disc T D)) / 2| := lt_of_lt_of_le hu (le_abs_self _)
    have hl' : |(T - Real.sqrt (disc T D)) / 2| < 1 := abs_lt.mpr ⟨hl1, hl2⟩
    refine ⟨⟨hu'.ne', hl'.ne⟩, ?_⟩
    simp [hl', not_lt.mpr hu'.le]

/-- Cochrane (2023), §5.5, p. 148 (tool): with exactly one eigenvalue in the open unit disc the
block has a real stable eigenvalue `λ` (`|λ| < 1`, a root of `z² − tr z + det`). -/
theorem exists_stable_root {P : Params} (hc : stableCount (blockMat P) = 1) :
    ∃ l : ℝ, |l| < 1 ∧ charB P l = 0 := by
  rw [stableCount_blockMat] at hc
  set T := trB P
  set D := detB P
  by_cases hdisc : 0 ≤ disc T D
  · obtain ⟨e1, e2⟩ := norm_root_of_nonneg hdisc
    rw [e1, e2] at hc
    have hroot : ∀ z, z = (T + Real.sqrt (disc T D)) / 2 ∨ z = (T - Real.sqrt (disc T D)) / 2 →
        charB P z = 0 := by
      intro z hz
      rw [charB, quad_factor_real hdisc]
      rcases hz with rfl | rfl <;> ring
    split_ifs at hc with h1 h2 h2
    · norm_num at hc
    · exact ⟨_, h1, hroot _ (Or.inl rfl)⟩
    · exact ⟨_, h2, hroot _ (Or.inr rfl)⟩
    · norm_num at hc
  · push Not at hdisc
    obtain ⟨e1, e2⟩ := normSq_root_of_neg hdisc
    have heq : ‖root₁ T D‖ = ‖root₂ T D‖ := by
      have := e1.trans e2.symm
      nlinarith [norm_nonneg (root₁ T D), norm_nonneg (root₂ T D)]
    rw [heq] at hc
    split_ifs at hc <;> norm_num at hc

/-- Cochrane (2023), §5.5, p. 148 (tool): the action of the block matrix on a vector. -/
theorem blockMat_mulVec (P : Params) (v : Fin 1 ⊕ Fin 1 → ℝ) :
    blockMat P *ᵥ v = Sum.elim (fun _ => aXX P * v (Sum.inl 0) + aXP P * v (Sum.inr 0))
      (fun _ => aPX P * v (Sum.inl 0) + aPP P * v (Sum.inr 0)) := by
  funext k
  rcases k with k | k <;>
    simp [blockMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.fin_one_eq_zero k]

/-- **Genericity** (Cochrane (2023), p. 148, and the survey's open item; Blanchard–Kahn
genericity, Woodford (2003) App. C.1 fn. 2): if `κ ≠ 0` and the block has one stable eigenvalue
and none on the unit circle, the stable subspace meets `{π̂ = 0}` only in `0`. The stable
eigenvector is `((λ_s − 1/β)/(−κ/β), 1)`, whose inflation component is nonzero. -/
theorem genericX_of_kappa_ne {P : Params} (hβ : P.beta ≠ 0) (hκ : P.kappa ≠ 0)
    (hnu : NoUnit (blockMat P)) (hc : stableCount (blockMat P) = 1) :
    GenericX (blockMat P) := by
  obtain ⟨l, hl, hroot⟩ := exists_stable_root hc
  have hc' : aPX P ≠ 0 := by
    simp only [aPX, neg_ne_zero]
    exact div_ne_zero hκ hβ
  set g : ℝ := (l - aPP P) / aPX P with hg
  set b : Fin 1 ⊕ Fin 1 → ℝ := Sum.elim (fun _ => g) (fun _ => 1) with hb
  have hAb : blockMat P *ᵥ b = l • b := by
    rw [blockMat_mulVec]
    funext k
    have hr : l ^ 2 - (aXX P + aPP P) * l + (aXX P * aPP P - aXP P * aPX P) = 0 := hroot
    rcases k with k | k
    · simp only [hb, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, hg]
      field_simp
      linear_combination (-1 : ℝ) * hr
    · simp only [hb, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, hg]
      field_simp
      ring
  have hbB : b ∈ boundedOrbits (blockMat P) := by
    refine ⟨|g| + 1, fun t k => ?_⟩
    rw [pow_mulVec_eigvec hAb t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    have hp : |l| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) hl.le
    have hbk : |b k| ≤ |g| + 1 := by
      rcases k with k | k <;> simp [hb]
    calc |l| ^ t * |b k| ≤ 1 * (|g| + 1) :=
          mul_le_mul hp hbk (abs_nonneg _) zero_le_one
      _ = |g| + 1 := one_mul _
  have hd : Module.finrank ℝ (boundedOrbits (blockMat P)) = 1 :=
    (finrank_eq_stableCount hnu).trans hc
  have hb0 : (⟨b, hbB⟩ : boundedOrbits (blockMat P)) ≠ 0 := by
    intro h0
    have := congrFun (congrArg Subtype.val h0) (Sum.inr 0)
    simp [hb] at this
  intro v hv hvx
  obtain ⟨c, hcv⟩ := (finrank_eq_one_iff_of_nonzero' _ hb0).mp hd ⟨v, hv⟩
  have hval : c • b = v := congrArg Subtype.val hcv
  have hc0 : c = 0 := by
    have := congrFun hval (Sum.inr 0)
    rw [hvx 0] at this
    simpa [hb] using this
  rw [← hval, hc0, zero_smul]

/-- Cochrane (2023), §5.5, p. 148 (the genericity condition is exactly `κ ≠ 0`): with `κ = 0`
and `0 < β < 1`, if the block has one stable eigenvalue and none on the unit circle, genericity
fails — the output direction `(1, 0)` is a bounded orbit with zero predetermined component. -/
theorem not_genericX_of_kappa_zero {P : Params} (hκ : P.kappa = 0) (hβ0 : 0 < P.beta)
    (hβ1 : P.beta < 1) (hc : stableCount (blockMat P) = 1) : ¬ GenericX (blockMat P) := by
  have hPX : aPX P = 0 := by simp [aPX, hκ]
  have hfac : ∀ z : ℂ, z ^ 2 - (trB P : ℂ) * z + (detB P : ℂ) =
      (z - (aXX P : ℂ)) * (z - (aPP P : ℂ)) := by
    intro z
    simp only [trB, detB, hPX, mul_zero, sub_zero]
    push_cast
    ring
  have he := eigs_blockMat_of_factor hfac
  have hPP : 1 < aPP P := by
    rw [aPP, lt_div_iff₀ hβ0]
    linarith
  have hXX : |aXX P| < 1 := by
    rw [stableCount, he, Multiset.filter_add, Multiset.filter_singleton,
      Multiset.filter_singleton] at hc
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < aPP P)] at hc
    by_contra h
    simp [h, not_lt.mpr hPP.le] at hc
  intro hg
  set b : Fin 1 ⊕ Fin 1 → ℝ := Sum.elim (fun _ => 1) (fun _ => 0) with hb
  have hAb : blockMat P *ᵥ b = aXX P • b := by
    rw [blockMat_mulVec]
    funext k
    rcases k with k | k <;> simp [hb, hPX]
  have hbB : b ∈ boundedOrbits (blockMat P) := by
    refine ⟨1, fun t k => ?_⟩
    rw [pow_mulVec_eigvec hAb t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    have hp : |aXX P| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) hXX.le
    rcases k with k | k
    · simpa [hb] using hp
    · simp [hb]
  have := hg b hbB (fun _ => by simp [hb])
  have h1 := congrFun this (Sum.inl 0)
  simp [hb] at h1

/-- Cochrane (2023), §5.5, p. 148 (the derived genericity condition): for `0 < β < 1`, with one
stable eigenvalue and none on the unit circle, Blanchard–Kahn genericity of the `(x, π)` block
holds iff `κ ≠ 0`. -/
theorem genericX_iff_kappa_ne_zero {P : Params} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hnu : NoUnit (blockMat P)) (hc : stableCount (blockMat P) = 1) :
    GenericX (blockMat P) ↔ P.kappa ≠ 0 :=
  ⟨fun hg hκ => not_genericX_of_kappa_zero hκ hβ0 hβ1 hc hg,
    fun hκ => genericX_of_kappa_ne hβ0.ne' hκ hnu hc⟩

/-- **Determinacy of the `(x, π)` block** (Cochrane (2023), pp. 148–149 and §5.5.3, p. 154;
A1 §1.9, pp. 574–575, via the general Blanchard–Kahn theorem): under the sign restrictions and
the passive-money condition, for every bounded adapted forcing and every initial `π̂_0` there is
exactly one bounded equilibrium, for any expectation system. -/
theorem block_determinate {P : Params} (hP : Standard P) (hpass : Passive P) :
    Determinate 𝔼 (blockMat P) := by
  obtain ⟨hnu, hc⟩ := (stable_one_iff_passive hP).mpr hpass
  have hg := genericX_of_kappa_ne hP.2.2.1.ne' hP.2.1.ne' hnu hc
  exact determinate_of 𝔼 hnu ((finrank_eq_iff_stableCount_eq hnu hg).mpr
    (by rw [Fintype.card_fin]; exact hc)) hg

/-- Cochrane (2023), §5.5.3, p. 154 (E43) and A1 §1.9, pp. 574–575: under the sign restrictions
the `(x, π)` block is determinate (for every bounded adapted forcing and initial condition) iff
the passive-money condition `κ(θ_iπ − 1) + (1 − β)θ_ix < 0` holds. -/
theorem block_determinate_iff [Nonempty Ω] {P : Params} (hP : Standard P) :
    Determinate 𝔼 (blockMat P) ↔ Passive P := by
  constructor
  · intro hd
    obtain ⟨hnu, hc, -⟩ := (determinate_iff_count 𝔼 (blockMat P)).mp hd
    rw [Fintype.card_fin] at hc
    exact (stable_one_iff_passive hP).mp ⟨hnu, hc⟩
  · exact block_determinate 𝔼 hP

/-- Online Appendix A1 §1.9, pp. 574–576 (E20: "we need two eigenvalues greater or equal to
one", "`λ_k ≥ 1` solved forward"): on the boundary `κ(θ_iπ − 1) + (1 − β)θ_ix = 0` the block has
the eigenvalue `1`, and it is not determinate — a unit eigenvalue is not a forward-looking one. -/
theorem block_not_determinate_of_boundary [Nonempty Ω] {P : Params} (hβ : P.beta ≠ 0)
    (h0 : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) :
    ¬ Determinate 𝔼 (blockMat P) := by
  have h1 : charB P 1 = 0 := by rw [charB_one hβ, h0, mul_zero]
  have hmem : (1 : ℂ) ∈ eigs (blockMat P) := by
    have hz : (1 : ℂ) ^ 2 - (trB P : ℂ) * 1 + (detB P : ℂ) = 0 := by
      have : ((charB P 1 : ℝ) : ℂ) = 0 := by rw [h1]; simp
      rw [← this, charB]
      push_cast
      ring
    rw [eigs_blockMat]
    rcases eq_root_of_eq hz with h | h
    · rw [← h]; simp
    · rw [← h]; simp
  exact not_determinate_of_unit 𝔼 hmem (by simp)

/-! ### Closure tools for bounded and adapted processes -/

/-- Cochrane (2023), p. 148 (tool): sums of bounded processes are bounded. -/
theorem bdd_add {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedProc (a + b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t ω => (abs_add_le _ _).trans (add_le_add (hA t ω) (hB t ω))⟩

/-- Cochrane (2023), p. 148 (tool): differences of bounded processes are bounded. -/
theorem bdd_sub {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedProc (a - b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t ω => (abs_sub _ _).trans (add_le_add (hA t ω) (hB t ω))⟩

/-- Cochrane (2023), p. 148 (tool): multiples of bounded processes are bounded. -/
theorem bdd_smul (c : ℝ) {a : ℕ → Ω → ℝ} (ha : BoundedProc a) : BoundedProc (c • a) := by
  obtain ⟨A, hA⟩ := ha
  refine ⟨|c| * A, fun t ω => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hA t ω) (abs_nonneg c)

/-- Cochrane (2023), p. 148 (tool): the one-period lead of a bounded process is bounded. -/
theorem bdd_shift {a : ℕ → Ω → ℝ} (ha : BoundedProc a) : BoundedProc (fun t => a (t + 1)) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun t ω => hA (t + 1) ω⟩

/-- Cochrane (2023), p. 148 (tool): sums of adapted processes are adapted. -/
theorem adapted_add {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.Adapted (a + b) := fun t => by
  simp only [Pi.add_apply, map_add, ha t, hb t]

/-- Cochrane (2023), p. 148 (tool): differences of adapted processes are adapted. -/
theorem adapted_sub {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.Adapted (a - b) := fun t => by
  simp only [Pi.sub_apply, map_sub, ha t, hb t]

/-- Cochrane (2023), p. 148 (tool): multiples of adapted processes are adapted. -/
theorem adapted_smul (c : ℝ) {a : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) : 𝔼.Adapted (c • a) :=
  fun t => by simp only [Pi.smul_apply, map_smul, ha t]

/-! ### The model in Blanchard–Kahn form -/

/-- Cochrane (2023), (5.68), p. 149: the exogenous part of unexpected inflation,
`ξ_{t+1} = −β_s ε_{s,t+1} − β_i ε_{i,t+1}` (and `ξ_0 = 0`). -/
def xi (P : Params) (ei es : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)

/-- Cochrane (2023), (5.68), p. 149 (tool): the value of `ξ_{t+1}`. -/
theorem xi_succ (P : Params) (ei es : ℕ → Ω → ℝ) (t : ℕ) :
    xi P ei es (t + 1) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1) := rfl

/-- Cochrane (2023), (5.68), p. 149 (tool): `ξ` is unpredictable, `E_t ξ_{t+1} = 0`. -/
theorem E_xi_succ {P : Params} {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us)
    (t : ℕ) : 𝔼.E t (xi P ei es (t + 1)) = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hei, hes, -, -⟩ := hsh
  rw [xi_succ, map_sub, map_neg, map_smul, map_smul, hei t, hes t]
  simp

/-- Cochrane (2023), (5.68), p. 149 (tool): `ξ` is adapted. -/
theorem xi_adapted {P : Params} {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) :
    𝔼.Adapted (xi P ei es) := by
  obtain ⟨hea, hesa, -, -, -, -, -, -, -, -, -, -⟩ := hsh
  intro t
  cases t with
  | zero => exact map_zero _
  | succ t => rw [xi_succ, map_sub, map_neg, map_smul, map_smul, hea, hesa]

/-- Cochrane (2023), (5.68), p. 149 (tool): `ξ` is bounded. -/
theorem xi_bounded {P : Params} {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) :
    BoundedProc (xi P ei es) := by
  obtain ⟨-, -, -, -, ⟨A, hA⟩, ⟨B, hB⟩, -, -, -, -, -, -⟩ := hsh
  refine ⟨|P.betaS| * |B| + |P.betaI| * |A|, fun t ω => ?_⟩
  cases t with
  | zero => simp only [xi, Pi.zero_apply, abs_zero]; positivity
  | succ t =>
    simp only [xi_succ, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    calc |-(P.betaS * es (t + 1) ω) - P.betaI * ei (t + 1) ω|
        ≤ |P.betaS * es (t + 1) ω| + |P.betaI * ei (t + 1) ω| := by
          have := abs_sub (-(P.betaS * es (t + 1) ω)) (P.betaI * ei (t + 1) ω)
          rwa [abs_neg] at this
      _ ≤ |P.betaS| * |B| + |P.betaI| * |A| := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_left ((hB _ _).trans (le_abs_self B)) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left ((hA _ _).trans (le_abs_self A)) (abs_nonneg _))

/-- Cochrane (2023), (5.64)–(5.68), pp. 148–149: the forcing of the `(x, π̂)` system,
`(σ(θ_iπ − 1/β) ξ_t + σ u_{i,t}, ξ_t/β)`. -/
noncomputable def blockForcing (P : Params) (ei es ui : ℕ → Ω → ℝ) (t : ℕ) :
    Fin 1 ⊕ Fin 1 → Ω → ℝ :=
  Sum.elim (fun _ => aXP P • xi P ei es t + P.sigma • ui t) (fun _ => aPP P • xi P ei es t)

/-- Cochrane (2023), (5.64)–(5.68), pp. 148–149: the state `(x_t, π̂_t)`, `π̂ = π − ξ` (so
`π̂_{t+1} = E_t π_{t+1}` is predetermined). -/
def blockState (P : Params) (ei es x p : ℕ → Ω → ℝ) (t : ℕ) : Fin 1 ⊕ Fin 1 → Ω → ℝ :=
  Sum.elim (fun _ => x t) (fun _ => p t - xi P ei es t)

/-- Cochrane (2023), p. 148 (tool): the block matrix acting on a random state. -/
theorem mv_blockMat (P : Params) (a : Fin 1 ⊕ Fin 1 → Ω → ℝ) :
    mv (blockMat P) a = Sum.elim (fun _ => aXX P • a (Sum.inl 0) + aXP P • a (Sum.inr 0))
      (fun _ => aPX P • a (Sum.inl 0) + aPP P • a (Sum.inr 0)) := by
  funext k
  rcases k with k | k <;>
    simp [mv, blockMat, Fintype.sum_sum_type, Fin.fin_one_eq_zero k]

/-- Cochrane (2023), pp. 148–149 and A1 §1.11, pp. 578–579: the IS curve (5.64), the Phillips
curve (5.65) and unexpected inflation (5.68), for bounded adapted `x, π` with initial `π_0`, are
exactly a bounded equilibrium of the Blanchard–Kahn system `E_t y_{t+1} = A y_t + w_t` in
`y = (x, π̂)` with `π̂_0 = π_0`. -/
theorem block_iff {P : Params} (hβ : P.beta ≠ 0) {ei es ui us : ℕ → Ω → ℝ}
    (hsh : Shocks 𝔼 P ei es ui us) (x p : ℕ → Ω → ℝ) (p0 : ℝ) :
    ((∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1)))) ∧
      (∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t) ∧
      (∀ t, innov 𝔼 t (p (t + 1)) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)) ∧
      𝔼.Adapted x ∧ 𝔼.Adapted p ∧ BoundedProc x ∧ BoundedProc p ∧ p 0 = (fun _ => p0)) ↔
    Equil 𝔼 (blockMat P) (blockForcing P ei es ui) (fun _ => p0) (blockState P ei es x p) := by
  have hxa := xi_adapted 𝔼 hsh
  have hxE := E_xi_succ 𝔼 hsh
  have hxb := xi_bounded 𝔼 hsh
  constructor
  · rintro ⟨h64, h65, h68, hax, hap, hbx, hbp, hp0⟩
    have hEp : ∀ t, 𝔼.E t (p (t + 1)) = p (t + 1) - xi P ei es (t + 1) := by
      intro t
      have := h68 t
      rw [innov_succ 𝔼 hap, ← xi_succ] at this
      rw [← this]
      abel
    refine ⟨fun t k => ?_, fun t k => ?_, fun t j => ?_, fun j => ?_, ?_⟩
    · rw [mv_blockMat]
      funext ω
      have e64 := congrFun (h64 t) ω
      have e65 := congrFun (h65 t) ω
      simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e64 e65
      rcases k with k | k
      · simp only [blockState, blockForcing, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul, aXX, aXP]
        linear_combination (norm := (field_simp; ring)) (-1 : ℝ) * e64 +
          (P.sigma / P.beta) * e65
      · simp only [blockState, blockForcing, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul, aPX, aPP, map_sub, hxE t, Pi.zero_apply,
          sub_zero]
        linear_combination (norm := (field_simp; ring)) (-1 / P.beta) * e65
    · rcases k with k | k
      · exact hax t
      · simp only [blockState, Sum.elim_inr, map_sub, hap t, hxa t]
    · simp only [blockState, Sum.elim_inr, map_sub, hxE t, sub_zero, hEp t]
    · simp only [blockState, Sum.elim_inr, hp0]
      funext ω
      simp [xi]
    · obtain ⟨A, hA⟩ := hbx
      obtain ⟨B, hB⟩ := bdd_sub hbp hxb
      refine ⟨A + B, fun t k ω => ?_⟩
      have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA t ω)
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB t ω)
      rcases k with k | k
      · exact (hA t ω).trans (by linarith)
      · exact (hB t ω).trans (by linarith)
  · rintro ⟨hs, ha, hk, h0, hb⟩
    have hap : 𝔼.Adapted p := by
      intro t
      have h1 := ha t (Sum.inr 0)
      simp only [blockState, Sum.elim_inr, map_sub, hxa t] at h1
      linear_combination h1
    have hEp : ∀ t, 𝔼.E t (p (t + 1)) = p (t + 1) - xi P ei es (t + 1) := by
      intro t
      have h1 := hk t 0
      simp only [blockState, Sum.elim_inr, map_sub, hxE t, sub_zero] at h1
      exact h1
    have h65 : ∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t := by
      intro t
      funext ω
      have e := congrFun (hs t (Sum.inr 0)) ω
      rw [mv_blockMat] at e
      simp only [blockState, blockForcing, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, aPX, aPP, map_sub, hxE t, sub_zero,
        Pi.zero_apply] at e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (norm := (field_simp; ring)) (-P.beta) * e
    refine ⟨fun t => ?_, h65, fun t => ?_, fun t => ha t (Sum.inl 0), hap, ?_, ?_, ?_⟩
    · funext ω
      have e := congrFun (hs t (Sum.inl 0)) ω
      have e65 := congrFun (h65 t) ω
      rw [mv_blockMat] at e
      simp only [blockState, blockForcing, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, aXX, aXP] at e
      simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e65 ⊢
      linear_combination (norm := (field_simp; ring)) (-1 : ℝ) * e + (P.sigma / P.beta) * e65
    · rw [innov_succ 𝔼 hap, hEp t, xi_succ]
      abel
    · obtain ⟨M, hM⟩ := hb
      exact ⟨M, fun t ω => hM t (Sum.inl 0) ω⟩
    · obtain ⟨M, hM⟩ := hb
      have : BoundedProc (fun t => blockState P ei es x p t (Sum.inr 0)) :=
        ⟨M, fun t ω => hM t (Sum.inr 0) ω⟩
      have h2 := bdd_add this hxb
      convert h2 using 1
      funext t ω
      simp [blockState]
    · have := h0 0
      simp only [blockState, Sum.elim_inr] at this
      rw [← this]
      funext ω
      simp [xi]

/-- Cochrane (2023), (5.72)–(5.73), p. 149: for an adapted bond price the expectations
hypothesis `E_t r^n_{t+1} = i_t` is the forward equation `q_t = ω E_t q_{t+1} − i_t`. -/
theorem eq572_iff {P : Params} {x p ui q : ℕ → Ω → ℝ} (hq : 𝔼.Adapted q) :
    (∀ t, 𝔼.E t (rnNext P q t) = iRule P x p ui t) ↔
      ForwardSolution.Solves 𝔼 P.omega (fun t => -iRule P x p ui t) q := by
  constructor
  · intro h t
    change q t = _ + -iRule P x p ui t
    rw [← h t, rnNext, map_sub, map_smul, hq t]
    abel
  · intro h t
    have e := h t
    simp only at e
    rw [rnNext, map_sub, map_smul, hq t]
    rw [e]
    abel

/-- Cochrane (2023), (5.69)–(5.71), p. 149: the debt flow, solved for `v_{t+1}`:
`v_{t+1} = ((1 − α)/ρ) v_t + g_t` with `g_t = ρ⁻¹(r^n_{t+1} − (1 + θ_sπ)π_{t+1} − θ_sx x_{t+1}
− u_{s,t+1})`. -/
noncomputable def gV (P : Params) (x p q us : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  P.rho⁻¹ • (rnNext P q t - (1 + P.thSpi) • p (t + 1) - P.thSx • x (t + 1) - us (t + 1))

/-- Cochrane (2023), (5.69)–(5.71), p. 149: with `ρ ≠ 0` the debt flow (5.71) is the backward
recursion `v_{t+1} = ((1 − α)/ρ) v_t + g_t`. -/
theorem eq571_iff {P : Params} (hρ : P.rho ≠ 0) {x p q v us : ℕ → Ω → ℝ} :
    (∀ t, P.rho • v (t + 1) = v t + rnNext P q t - p (t + 1) - sNext P x p v us t) ↔
      ∀ t, v (t + 1) = ((1 - P.alpha) / P.rho) • v t + gV P x p q us t := by
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [gV, sNext, rnNext, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    field_simp
    linear_combination e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [gV, sNext, rnNext, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    rw [e]
    field_simp
    ring

/-- Cochrane (2023), (5.71), p. 149 (tool): the backward recursion `v_{t+1} = φ v_t + g_t` from
`v_0`. -/
def backRec (φ : ℝ) (g : ℕ → Ω → ℝ) (v0 : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => v0
  | t + 1 => φ • backRec φ g v0 t + g t

/-- Cochrane (2023), (5.71), p. 149 (tool): with `|φ| < 1` and bounded `g` the backward
recursion is bounded by `|v_0| + M/(1 − |φ|)`. -/
theorem backRec_bound {φ M : ℝ} (hφ : |φ| < 1) {g : ℕ → Ω → ℝ} (hg : ∀ t ω, |g t ω| ≤ M)
    (v0 : ℝ) (t : ℕ) (ω : Ω) : |backRec φ g v0 t ω| ≤ |v0| + M / (1 - |φ|) := by
  refine bounded_of_rec (x := fun t => backRec φ g v0 t ω) (abs_nonneg φ) hφ
    ((abs_nonneg _).trans (hg 0 ω)) (by simp only [backRec]; rfl) (fun t => ?_) t
  simp only [backRec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← abs_mul]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (hg t ω))

/-- Cochrane (2023), (5.71), p. 149 (tool): the backward recursion is adapted when `g_t` is known
at date `t + 1`. -/
theorem backRec_adapted {φ : ℝ} {g : ℕ → Ω → ℝ} (hg : ∀ t, 𝔼.E (t + 1) (g t) = g t)
    (v0 : ℝ) : 𝔼.Adapted (backRec φ g v0) := by
  intro t
  induction t with
  | zero => exact 𝔼.const 0 v0
  | succ t ih =>
    simp only [backRec]
    rw [map_add, map_smul, hg t]
    congr 2
    have := 𝔼.known (Nat.le_succ t) (backRec φ g v0 t)
    rwa [ih] at this

/-- Cochrane (2023), (5.71), p. 149 (tool): any solution of the backward recursion from `v_0` is
`backRec`. -/
theorem eq_backRec {φ : ℝ} {g : ℕ → Ω → ℝ} {v0 : ℝ} {v : ℕ → Ω → ℝ}
    (h0 : v 0 = fun _ => v0) (h : ∀ t, v (t + 1) = φ • v t + g t) : v = backRec φ g v0 := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih => rw [h t, ih]; rfl

/-- **Determinacy of the sticky-price fiscal model with policy rules** (Cochrane (2023), §5.5,
pp. 148–149: "the unique stationary equilibrium"; A1 §1.11, pp. 578–579). Under the sign
restrictions, the passive-money condition `κ(θ_iπ − 1) + (1 − β)θ_ix < 0`, `|ω| < 1`, `ρ > 0` and
`|1 − α| < ρ` (i.e. `α ∈ (1 − ρ, 1 + ρ)`), for any expectation system, any bounded shocks and
every initial inflation `π_0` and value of debt `v_0`, the reduced model (5.64)–(5.73) has exactly
one bounded adapted equilibrium `(x, π, q, v)`. -/
theorem policyRules_determinate {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) (p0 v0 : ℝ) :
    ∃! y : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      RedEquil 𝔼 P ei es ui us p0 v0 y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hβ := hP.2.2.1.ne'
  have hsh' := hsh
  obtain ⟨-, -, hua, husa, -, -, hub, husb, -, -, -, -⟩ := hsh'
  have hxa := xi_adapted 𝔼 hsh
  have hxb := xi_bounded 𝔼 hsh
  have hwb : BoundedV (blockForcing P ei es ui) := by
    obtain ⟨A, hA⟩ := bdd_add (bdd_smul (aXP P) hxb) (bdd_smul P.sigma hub)
    obtain ⟨B, hB⟩ := bdd_smul (aPP P) hxb
    refine ⟨max A B, fun t k ω => ?_⟩
    rcases k with k | k
    · exact (hA t ω).trans (le_max_left _ _)
    · exact (hB t ω).trans (le_max_right _ _)
  have hwa : AdaptedV 𝔼 (blockForcing P ei es ui) := by
    intro t k
    rcases k with k | k
    · exact adapted_add 𝔼 (adapted_smul 𝔼 _ hxa) (adapted_smul 𝔼 _ hua) t
    · exact adapted_smul 𝔼 _ hxa t
  obtain ⟨yb, hyb, hyu⟩ := block_determinate 𝔼 hP hpass _ hwb hwa (fun _ => p0)
  set x : ℕ → Ω → ℝ := fun t => yb t (Sum.inl 0) with hx
  set p : ℕ → Ω → ℝ := fun t => yb t (Sum.inr 0) + xi P ei es t with hp
  have hys : blockState P ei es x p = yb := by
    funext t k
    rcases k with k | k <;> simp [blockState, hx, hp, Fin.fin_one_eq_zero k]
  rw [← hys] at hyb
  obtain ⟨h64, h65, h68, hax, hap, hbx, hbp, hp0⟩ := (block_iff 𝔼 hβ hsh x p p0).mpr hyb
  have hib : BoundedProc (fun t => -iRule P x p ui t) := by
    obtain ⟨M, hM⟩ := bdd_add (bdd_add (bdd_smul P.thIpi hbp) (bdd_smul P.thIx hbx)) hub
    refine ⟨M, fun t ω => ?_⟩
    rw [show (fun t => -iRule P x p ui t) t ω = -(iRule P x p ui t ω) from rfl, abs_neg]
    exact hM t ω
  have hia : 𝔼.Adapted (fun t => -iRule P x p ui t) := by
    intro t
    simp only [iRule, map_neg, map_add, map_smul, hap t, hax t, hua t]
  obtain ⟨q, ⟨hbq, hqs⟩, hqu⟩ := ForwardSolution.existsUnique_bounded 𝔼 hω hib hia
  have haq := ForwardSolution.solves_adapted 𝔼 hia hqs
  set φ := (1 - P.alpha) / P.rho with hφdef
  have hφ : |φ| < 1 := by rw [hφdef, abs_div, abs_of_pos hρ0, div_lt_one hρ0]; exact hα
  have hgb : BoundedProc (gV P x p q us) := by
    have h := bdd_smul P.rho⁻¹ (bdd_sub (bdd_sub (bdd_sub (bdd_sub (bdd_smul P.omega
      (bdd_shift hbq)) hbq) (bdd_smul (1 + P.thSpi) (bdd_shift hbp)))
      (bdd_smul P.thSx (bdd_shift hbx))) (bdd_shift husb))
    exact h
  have hga : ∀ t, 𝔼.E (t + 1) (gV P x p q us t) = gV P x p q us t := by
    intro t
    simp only [gV, rnNext, map_smul, map_sub, haq (t + 1), hap (t + 1), hax (t + 1),
      husa (t + 1), E_succ_of_adapted 𝔼 haq t]
  obtain ⟨Mg, hMg⟩ := hgb
  set v := backRec φ (gV P x p q us) v0 with hv
  refine ⟨(x, p, q, v), ⟨⟨h64, h65, h68, (eq571_iff hρ0.ne').mpr (fun t => rfl),
    (eq572_iff 𝔼 haq).mpr hqs⟩, hax, hap, haq, backRec_adapted 𝔼 hga v0, hbx, hbp, hbq,
    ⟨_, backRec_bound hφ hMg v0⟩, hp0, rfl⟩, ?_⟩
  rintro ⟨x', p', q', v'⟩ ⟨⟨h64', h65', h68', h71', h72'⟩, hax', hap', haq', hav', hbx', hbp',
    hbq', hbv', hp0', hv0'⟩
  have hblk := (block_iff 𝔼 hβ hsh x' p' p0).mp ⟨h64', h65', h68', hax', hap', hbx', hbp', hp0'⟩
  have hyy := hyu _ hblk
  rw [← hys] at hyy
  have hxx : x' = x := by
    funext t
    have := congrFun (congrFun hyy t) (Sum.inl 0)
    simpa [blockState] using this
  have hpp : p' = p := by
    funext t
    have := congrFun (congrFun hyy t) (Sum.inr 0)
    simp only [blockState, Sum.elim_inr] at this
    exact sub_left_injective this
  subst hxx hpp
  have hqq : q' = q := hqu q' ⟨hbq', (eq572_iff 𝔼 haq').mp h72'⟩
  subst hqq
  have hvv : v' = v := eq_backRec hv0' ((eq571_iff hρ0.ne').mp h71')
  subst hvv
  rfl

/-- Cochrane (2023), pp. 148–149: **determinacy of the full model** (5.51)–(5.62). Under the
conditions of `policyRules_determinate` and `ρ < 1` an equilibrium exists, and any two equilibria
agree in `x, π, q, v, v*` at every date and in `π*` from date `1` on (`π*_0` enters no
equation). -/
theorem policyRules_full_determinate {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1) (hα : |1 - P.alpha| < P.rho)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) (p0 v0 : ℝ) :
    (∃ x p q v vs ps, FullEquil 𝔼 P ei es ui us p0 v0 x p q v vs ps) ∧
    ∀ x p q v vs ps x' p' q' v' vs' ps', FullEquil 𝔼 P ei es ui us p0 v0 x p q v vs ps →
      FullEquil 𝔼 P ei es ui us p0 v0 x' p' q' v' vs' ps' →
      x = x' ∧ p = p' ∧ q = q' ∧ v = v' ∧ vs = vs' ∧ ∀ t, ps (t + 1) = ps' (t + 1) := by
  obtain ⟨y, hy, hu⟩ := policyRules_determinate 𝔼 hP hpass hω hρ0 hα hsh p0 v0
  refine ⟨⟨_, _, _, _, _, _, red_to_full 𝔼 hy⟩, ?_⟩
  intro x p q v vs ps x' p' q' v' vs' ps' h h'
  obtain ⟨hr, hvv, hpp⟩ := full_to_red 𝔼 hρ0 hρ1 h
  obtain ⟨hr', hvv', hpp'⟩ := full_to_red 𝔼 hρ0 hρ1 h'
  have e := (hu (x, p, q, v) hr).trans (hu (x', p', q', v') hr').symm
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact ⟨rfl, rfl, rfl, rfl, hvv.trans hvv'.symm, fun t => (hpp t).trans (hpp' t).symm⟩

/-- Cochrane (2023), p. 147 (tool): zero disturbances satisfy the shock assumptions. -/
theorem shocks_zero (P : Params) : Shocks 𝔼 P 0 0 0 0 := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, ⟨0, fun _ _ => by simp⟩,
    ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩, fun t => ?_,
    fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> simp

/-- Cochrane (2023), p. 148 (tool): with zero shocks the block forcing vanishes. -/
theorem blockForcing_zero (P : Params) :
    blockForcing P (0 : ℕ → Ω → ℝ) 0 0 = 0 := by
  funext t k
  have hxi : xi P (0 : ℕ → Ω → ℝ) 0 t = 0 := by
    cases t with
    | zero => rfl
    | succ t => simp [xi_succ]
  rcases k with k | k <;> simp [blockForcing, hxi]

/-- Cochrane (2023), §5.5.3, p. 154 (active money): if `κ(θ_iπ − 1) + (1 − β)θ_ix > 0`, both
eigenvalues of the `(x, π)` block lie outside the closed unit disc. -/
theorem both_unstable {P : Params} (hP : Standard P)
    (hact : 0 < P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx) :
    NoUnit (blockMat P) ∧ stableCount (blockMat P) = 0 := by
  have hβ := hP.2.2.1
  have hm1 := charB_neg_one_pos hP
  have hD1 := one_lt_detB hP
  have h1 : 0 < charB P 1 := by
    rw [charB_one hβ.ne']
    exact mul_pos (div_pos hP.1 hβ) hact
  rw [noUnit_blockMat_iff, stableCount_blockMat]
  suffices h : 1 < ‖root₁ (trB P) (detB P)‖ ∧ 1 < ‖root₂ (trB P) (detB P)‖ by
    refine ⟨⟨h.1.ne', h.2.ne'⟩, ?_⟩
    simp [not_lt.mpr h.1.le, not_lt.mpr h.2.le]
  set T := trB P with hT
  set D := detB P with hD
  by_cases hdisc : 0 ≤ disc T D
  · obtain ⟨e1, e2⟩ := norm_root_of_nonneg hdisc
    rw [e1, e2]
    have hs0 : 0 ≤ Real.sqrt (disc T D) := Real.sqrt_nonneg _
    set u := (T + Real.sqrt (disc T D)) / 2 with hu
    set l := (T - Real.sqrt (disc T D)) / 2 with hl
    have hul : l ≤ u := by rw [hu, hl]; linarith
    have hf1 : charB P 1 = (1 - u) * (1 - l) := by rw [charB, ← hT, ← hD, quad_factor_real hdisc]
    have hfm : charB P (-1) = (-1 - u) * (-1 - l) := by
      rw [charB, ← hT, ← hD, quad_factor_real hdisc]
    have hprod : u * l = D := by
      have := quad_factor_real hdisc 0
      rw [← hu, ← hl] at this
      linear_combination (-1 : ℝ) * this
    rw [hf1] at h1
    rw [hfm] at hm1
    rw [← hprod] at hD1
    rcases le_or_gt 0 l with hl0 | hl0
    · have hl1 : 1 < l := by
        by_contra hc
        push Not at hc
        have hu1 : u < 1 := by
          by_contra hc'
          push Not at hc'
          nlinarith
        nlinarith
      refine ⟨?_, ?_⟩
      · rw [abs_of_pos (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact hl1
    · have hu0 : u < 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      have hu1 : u < -1 := by
        by_contra hc
        push Not at hc
        have hl1 : -1 < l := by
          by_contra hc'
          push Not at hc'
          nlinarith
        nlinarith
      refine ⟨?_, ?_⟩
      · rw [abs_of_neg hu0]
        linarith
      · rw [abs_of_neg hl0]
        linarith
  · push Not at hdisc
    obtain ⟨e1, e2⟩ := normSq_root_of_neg hdisc
    constructor
    · nlinarith [norm_nonneg (root₁ T D)]
    · nlinarith [norm_nonneg (root₂ T D)]

/-- Cochrane (2023), §5.5, p. 148 and §5.5.3, p. 154 (necessity: active money and active fiscal
policy over-determine inflation): if `κ(θ_iπ − 1) + (1 − β)θ_ix > 0`, then even with zero shocks
there is an initial inflation `π_0` for which the model has no bounded equilibrium. -/
theorem nonexist_of_active [Nonempty Ω] {P : Params} (hP : Standard P)
    (hact : 0 < P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx) :
    ∃ p0 : ℝ, ∀ (v0 : ℝ) (x p q v : ℕ → Ω → ℝ), ¬ RedEquil 𝔼 P 0 0 0 0 p0 v0 x p q v := by
  obtain ⟨hnu, hc⟩ := both_unstable hP hact
  have hd : Module.finrank ℝ (boundedOrbits (blockMat P)) < Fintype.card (Fin 1) := by
    rw [finrank_eq_stableCount hnu, hc, Fintype.card_fin]
    norm_num
  obtain ⟨x0, hx0⟩ := nonexist_of_lt 𝔼 hd
  refine ⟨x0 0, fun v0 x p q v h => ?_⟩
  obtain ⟨⟨h64, h65, h68, -, -⟩, hax, hap, -, -, hbx, hbp, -, -, hp0, -⟩ := h
  have hE := (block_iff 𝔼 hP.2.2.1.ne' (shocks_zero 𝔼 P) x p (x0 0)).mp
    ⟨h64, h65, h68, hax, hap, hbx, hbp, hp0⟩
  rw [blockForcing_zero, show (fun _ : Fin 1 => x0 0) = x0 from
    funext fun j => by rw [Fin.fin_one_eq_zero j]] at hE
  exact hx0 _ hE

/-- Cochrane (2023), §5.4, pp. 137–138 and §5.5 (the surplus response to debt must satisfy
`α ∈ (1 − ρ, 1 + ρ)`): if `|1 − α| > ρ`, then (with the other conditions of
`policyRules_determinate`) the model with zero shocks, `π_0 = 0` and `v_0 = 1` has no bounded
equilibrium — the debt recursion `v_{t+1} = ((1 − α)/ρ) v_t` explodes. -/
theorem nonexist_of_alpha [Nonempty Ω] {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : P.rho < |1 - P.alpha|)
    (x p q v : ℕ → Ω → ℝ) : ¬ RedEquil 𝔼 P 0 0 0 0 0 1 x p q v := by
  intro h
  obtain ⟨⟨h64, h65, h68, h71, h72⟩, hax, hap, haq, -, hbx, hbp, hbq, hbv, hp0, hv0⟩ := h
  have hβ := hP.2.2.1.ne'
  have hE := (block_iff 𝔼 hβ (shocks_zero 𝔼 P) x p 0).mp
    ⟨h64, h65, h68, hax, hap, hbx, hbp, hp0⟩
  have hE0 := (block_iff 𝔼 hβ (shocks_zero 𝔼 P) 0 0 0).mp
    ⟨fun t => by simp [iRule], fun t => by simp, fun t => by simp [innov],
      fun t => by simp, fun t => by simp, ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩,
      rfl⟩
  rw [blockForcing_zero] at hE hE0
  obtain ⟨y, -, hyu⟩ := block_determinate 𝔼 hP hpass 0 ⟨0, fun _ _ _ => by simp⟩
    (fun _ _ => by simp) (fun _ => 0)
  have e := (hyu _ hE).trans (hyu _ hE0).symm
  have hxi : xi P (0 : ℕ → Ω → ℝ) 0 = 0 := by
    funext t
    cases t with
    | zero => rfl
    | succ t => simp [xi_succ]
  have hx0 : x = 0 := by
    funext t
    have := congrFun (congrFun e t) (Sum.inl 0)
    simpa [blockState] using this
  have hp0' : p = 0 := by
    funext t
    have := congrFun (congrFun e t) (Sum.inr 0)
    simpa [blockState, hxi] using this
  subst hx0 hp0'
  have hqs := (eq572_iff 𝔼 haq).mp h72
  have hq0 : q = 0 := 𝔼.forward_unique hω hqs (fun t => by simp [iRule]) hbq
    ⟨0, fun _ _ => by simp⟩
  subst hq0
  have hrec := (eq571_iff hρ0.ne').mp h71
  set φ := (1 - P.alpha) / P.rho with hφdef
  have hφ : 1 < |φ| := by
    rw [hφdef, abs_div, abs_of_pos hρ0, one_lt_div hρ0]
    exact hα
  have hvt : ∀ t, v t = fun _ => φ ^ t := by
    intro t
    induction t with
    | zero => rw [hv0]; simp
    | succ t ih =>
      rw [hrec t, ih]
      funext ω
      simp [gV, rnNext, pow_succ, mul_comm]
  obtain ⟨M, hM⟩ := hbv
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hφ).eventually_gt_atTop M).exists
  have := hM t ω₀
  rw [hvt t, abs_pow] at this
  linarith

/-- Cochrane (2023), §5.5.2–5.5.3, pp. 150 and 154: the book's parameters with policy rules,
(5.76)–(5.79): `σ = 0.5, κ = 0.5, β = 0.99, θ_iπ = 0.8, θ_ix = 0.5, θ_sπ = 0.25, θ_sx = 1,
α = 0.2, ρ = 0.99, ω = 0.9, η_i = 0.7, η_s = 0.5` (the value that reproduces Table 5.1, E40),
`β_s = 0.14`, `β_i = 0`. -/
noncomputable def bookRules : Params :=
  ⟨0.5, 0.5, 0.99, 0.8, 0.5, 0.25, 1, 0.2, 0.99, 0.9, 0.7, 0.5, 0.14, 0⟩

/-- Cochrane (2023), §5.5.2, p. 150: the book's parameters without policy rules (`θ = 0`). -/
noncomputable def bookNoRules : Params :=
  ⟨0.5, 0.5, 0.99, 0, 0, 0, 0, 0.2, 0.99, 0.9, 0.7, 0.5, 0.36, 0⟩

/-- Cochrane (2023), §5.5.3, p. 154: the book's parameters satisfy the sign restrictions. -/
theorem bookRules_standard : Standard bookRules := by
  norm_num [Standard, bookRules]

/-- Cochrane (2023), §5.5.3, p. 154 (E43): the book's rule is passive,
`κ(θ_iπ − 1) + (1 − β)θ_ix = −0.095 < 0`. -/
theorem bookRules_passive : Passive bookRules := by
  norm_num [Passive, bookRules]

/-- Cochrane (2023), §5.5.3, p. 154 (E43, "I specify … `θ_iπ` less than one, to easily generate a
stationary passive-money model"): `θ_iπ < 1` alone does not give a passive-money model — with the
book's other parameters and `θ_ix = 11`, `θ_iπ = 0.8 < 1` but the block is active, and some
initial inflation admits no bounded equilibrium. -/
theorem thetaIpi_lt_one_insufficient [Nonempty Ω] :
    ({ bookRules with thIx := 11 } : Params).thIpi < 1 ∧ Standard { bookRules with thIx := 11 } ∧
      ¬ Passive { bookRules with thIx := 11 } ∧
      ∃ p0 : ℝ, ∀ (v0 : ℝ) (x p q v : ℕ → Ω → ℝ),
        ¬ RedEquil 𝔼 { bookRules with thIx := 11 } 0 0 0 0 p0 v0 x p q v := by
  have hact : 0 < ({ bookRules with thIx := 11 } : Params).kappa *
      (({ bookRules with thIx := 11 } : Params).thIpi - 1) +
      (1 - ({ bookRules with thIx := 11 } : Params).beta) *
        ({ bookRules with thIx := 11 } : Params).thIx := by
    norm_num [bookRules]
  have hst : Standard { bookRules with thIx := 11 } := by norm_num [Standard, bookRules]
  refine ⟨by norm_num [bookRules], hst, fun h => ?_, nonexist_of_active 𝔼 hst hact⟩
  unfold Passive at h
  linarith

/-! ### The closed-form equilibrium and §5.5.2–5.5.5 -/

/-- Online Appendix A1 §1.9, p. 574 (`λ_+`): the explosive root `(tr + √(tr² − 4 det))/2` of the
`(x, π)` block. -/
noncomputable def lamU (P : Params) : ℝ := (trB P + Real.sqrt (disc (trB P) (detB P))) / 2

/-- Online Appendix A1 §1.9, p. 574 (`λ_−`): the stable root `(tr − √(tr² − 4 det))/2` of the
`(x, π)` block. -/
noncomputable def lamS (P : Params) : ℝ := (trB P - Real.sqrt (disc (trB P) (detB P))) / 2

/-- Cochrane (2023), §5.5.3, p. 154 and A1 §1.9, p. 574: under the passive-money condition the
roots are real, `λ_u > 1 > λ_s > −1`, with `λ_u + λ_s = tr` and `λ_u λ_s = det`. -/
theorem roots_passive {P : Params} (hP : Standard P) (hpass : Passive P) :
    0 < disc (trB P) (detB P) ∧ 1 < lamU P ∧ -1 < lamS P ∧ lamS P < 1 ∧
      lamU P + lamS P = trB P ∧ lamU P * lamS P = detB P := by
  have hβ := hP.2.2.1
  have hp1 : 1 - trB P + detB P < 0 := by
    have h := charB_one (P := P) hβ.ne'
    have : charB P 1 = 1 - trB P + detB P := by rw [charB]; ring
    rw [← this, h]
    exact mul_neg_of_pos_of_neg (div_pos hP.1 hβ) hpass
  have hm1 : 0 < 1 + trB P + detB P := by
    have h := charB_neg_one_pos hP
    have : charB P (-1) = 1 + trB P + detB P := by rw [charB]; ring
    linarith
  obtain ⟨hd, hu, hl1, hl2⟩ := real_roots_loc hp1 hm1
  refine ⟨hd, hu, hl1, hl2, by unfold lamU lamS; ring, ?_⟩
  have := quad_factor_real hd.le 0
  unfold lamU lamS
  linear_combination (-1 : ℝ) * this

/-- Online Appendix A1 §1.9, p. 574: under the passive-money condition
`z² − tr z + det = (z − λ_u)(z − λ_s)`. -/
theorem charB_factor {P : Params} (hP : Standard P) (hpass : Passive P) (z : ℝ) :
    charB P z = (z - lamU P) * (z - lamS P) := by
  rw [charB, quad_factor_real (roots_passive hP hpass).1.le z]
  rfl

/-- Cochrane (2023), §5.5.2, p. 152 (the output response): the gain `g = (1 − βλ_s)/κ` of
output on inflation. -/
noncomputable def gain (P : Params) : ℝ := (1 - P.beta * lamS P) / P.kappa

/-- Cochrane (2023), §5.5.2, p. 152 ("Output rises, following the forward-looking Phillips
curve"): the gain of output on inflation is positive. -/
theorem gain_pos {P : Params} (hP : Standard P) (hpass : Passive P) : 0 < gain P := by
  obtain ⟨-, -, -, hl2, -, -⟩ := roots_passive hP hpass
  obtain ⟨-, hκ, hβ0, hβ1, -, -⟩ := hP
  unfold gain
  apply div_pos _ hκ
  rcases le_or_gt 0 (lamS P) with h | h
  · nlinarith
  · nlinarith

/-- **The closed-form equilibrium** (Cochrane (2023), §5.5, pp. 150–158, and the two-sided
form of (5.5)): in every bounded solution of (5.64)–(5.65) under the passive-money condition,
`x_t = g π_t − σ/(λ_u − η_i) u_{i,t}` and
`E_t π_{t+1} = λ_s π_t + κσ/(β(λ_u − η_i)) u_{i,t}`. -/
theorem closed_form {P : Params} (hP : Standard P) (hpass : Passive P) (hηi : |P.etaI| < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) {x p : ℕ → Ω → ℝ}
    (h64 : ∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1))))
    (h65 : ∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t)
    (hbx : BoundedProc x) (hbp : BoundedProc p) :
    (∀ t, x t = gain P • p t - (P.sigma / (lamU P - P.etaI)) • ui t) ∧
    ∀ t, 𝔼.E t (p (t + 1)) =
      lamS P • p t + (P.kappa * P.sigma / (P.beta * (lamU P - P.etaI))) • ui t := by
  obtain ⟨-, hU, -, -, hsum, -⟩ := roots_passive hP hpass
  obtain ⟨-, -, hua, -, -, -, hub, -, hei, -, hul, -⟩ := hsh
  have hβ := hP.2.2.1.ne'
  have hκ := hP.2.1.ne'
  have hηU : lamU P - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2
    linarith
  have hU0 : lamU P ≠ 0 := by linarith
  have hch : charB P (lamS P) = 0 := by rw [charB_factor hP hpass]; ring
  have hU' : lamU P = trB P - lamS P := by linarith
  have hEu := E_ar1 𝔼 hua hei hul
  set c : ℝ := P.sigma / (lamU P - P.etaI) with hc
  have kx : 1 + P.sigma * P.thIx + P.sigma * P.kappa / P.beta + gain P * P.kappa / P.beta =
      lamU P := by
    rw [hU', trB_eq, gain]
    field_simp
    ring
  have key : P.sigma * P.thIpi - P.sigma / P.beta - gain P / P.beta + lamU P * gain P =
      P.beta / P.kappa * charB P (lamS P) := by
    rw [hU', charB, trB_eq, detB_eq hβ, gain]
    field_simp
    ring
  have kp : P.sigma * P.thIpi - P.sigma / P.beta - gain P / P.beta = -(lamU P * gain P) := by
    rw [hch, mul_zero] at key
    linarith
  have ku : P.sigma + c * P.etaI = lamU P * c := by
    rw [hc]
    field_simp
    ring
  set f : ℕ → Ω → ℝ := x - gain P • p + c • ui with hf
  have hEf : ∀ t, 𝔼.E t (f (t + 1)) = lamU P • f t := by
    intro t
    funext ω
    have e64 := congrFun (h64 t) ω
    have e65 := congrFun (h65 t) ω
    have eu := congrFun (hEu t) ω
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e64 e65 eu
    have hEp : 𝔼.E t (p (t + 1)) ω = (p t ω - P.kappa * x t ω) / P.beta := by
      field_simp
      linarith
    have hEx : 𝔼.E t (x (t + 1)) ω = x t ω +
        P.sigma * (P.thIpi * p t ω + P.thIx * x t ω + ui t ω) - P.sigma * 𝔼.E t (p (t + 1)) ω := by
      linarith
    simp only [hf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub,
      map_smul]
    rw [eu, hEx, hEp]
    linear_combination x t ω * kx + p t ω * kp + ui t ω * ku
  have hfs : ∀ t, f t = (lamU P)⁻¹ • 𝔼.E t (f (t + 1)) + 0 := by
    intro t
    rw [hEf t, smul_smul, inv_mul_cancel₀ hU0, one_smul, add_zero]
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = (lamU P)⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have hinv : |(lamU P)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lamU P)]
    exact inv_lt_one_of_one_lt₀ hU
  have hbf : BoundedProc f := bdd_add (bdd_sub hbx (bdd_smul _ hbp)) (bdd_smul _ hub)
  have hf0 := 𝔼.forward_unique hinv hfs hz hbf ⟨0, fun _ _ => by simp⟩
  have hx : ∀ t, x t = gain P • p t - c • ui t := by
    intro t
    funext ω
    have := congrFun (congrFun hf0 t) ω
    simp only [hf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this ⊢
    linarith
  refine ⟨hx, fun t => ?_⟩
  funext ω
  have e65 := congrFun (h65 t) ω
  have exx := congrFun (hx t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e65 exx ⊢
  have hEp : 𝔼.E t (p (t + 1)) ω = (p t ω - P.kappa * x t ω) / P.beta := by
    field_simp
    linarith
  rw [hEp, exx, hc, gain]
  field_simp
  ring

/-- Cochrane (2023), §5.5.2–5.5.3, pp. 152 and 155 ("Inflation then decays with an AR(1)
pattern"; "more drawn-out inflation"): after fiscal shocks only (`u_i ≡ 0`), in every bounded
solution `x_t = g π_t` and `E_t π_{t+1} = λ_s π_t` — inflation is an AR(1) with coefficient
`λ_s`, with or without policy rules. -/
theorem fiscal_ar1 {P : Params} (hP : Standard P) (hpass : Passive P) (hηi : |P.etaI| < 1)
    {es us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P 0 es 0 us) {x p : ℕ → Ω → ℝ}
    (h64 : ∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p 0 t - 𝔼.E t (p (t + 1))))
    (h65 : ∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t)
    (hbx : BoundedProc x) (hbp : BoundedProc p) :
    (∀ t, x t = gain P • p t) ∧ ∀ t, 𝔼.E t (p (t + 1)) = lamS P • p t := by
  obtain ⟨h1, h2⟩ := closed_form 𝔼 hP hpass hηi hsh h64 h65 hbx hbp
  exact ⟨fun t => by rw [h1 t]; simp, fun t => by rw [h2 t]; simp⟩

/-- Cochrane (2023), §5.5, p. 148 ("Equations (5.55)–(5.56) determine unexpected inflation,
while (5.51)–(5.52) then determine unexpected output"): in every bounded solution unexpected
output is `g` times unexpected inflation less `σ/(λ_u − η_i)` times the monetary shock. -/
theorem unexpected_output {P : Params} (hP : Standard P) (hpass : Passive P)
    (hηi : |P.etaI| < 1) {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us)
    {x p : ℕ → Ω → ℝ}
    (h64 : ∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1))))
    (h65 : ∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t)
    (hbx : BoundedProc x) (hbp : BoundedProc p) (t : ℕ) :
    innov 𝔼 t (x (t + 1)) =
      gain P • innov 𝔼 t (p (t + 1)) - (P.sigma / (lamU P - P.etaI)) • ei (t + 1) := by
  have hsh' := hsh
  obtain ⟨-, -, hua, -, -, -, -, -, hei, -, hul, -⟩ := hsh'
  obtain ⟨h1, -⟩ := closed_form 𝔼 hP hpass hηi hsh h64 h65 hbx hbp
  have hi := innov_ar1 𝔼 hua hei hul t
  rw [h1 (t + 1), ← hi]
  simp only [innov, map_sub, map_smul, smul_sub]
  abel

/-- Cochrane (2023), §5.5.2, p. 152 ("With `β_s = 0` … there would be no inflation"): with no
monetary disturbance, `β_s = 0` and `π_0 = 0`, inflation and output are zero in every
equilibrium. -/
theorem no_inflation_of_betaS_zero {P : Params} (hP : Standard P) (hpass : Passive P)
    (hηi : |P.etaI| < 1) (hβs : P.betaS = 0) {es us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P 0 es 0 us)
    {v0 : ℝ} {x p q v : ℕ → Ω → ℝ} (h : RedEquil 𝔼 P 0 es 0 us 0 v0 x p q v) :
    p = 0 ∧ x = 0 := by
  obtain ⟨⟨h64, h65, h68, -, -⟩, -, hap, -, -, hbx, hbp, -, -, hp0, -⟩ := h
  obtain ⟨hx, hEp⟩ := fiscal_ar1 𝔼 hP hpass hηi hsh h64 h65 hbx hbp
  have hpz : p = 0 := by
    funext t
    induction t with
    | zero => rw [hp0]; rfl
    | succ t ih =>
      have e := h68 t
      rw [innov_succ 𝔼 hap, hEp t, ih, hβs] at e
      simp only [smul_zero, zero_smul, neg_zero, sub_zero, Pi.zero_apply] at e
      rw [← sub_eq_zero]
      simpa using e
  refine ⟨hpz, ?_⟩
  funext t
  rw [hx t, hpz]
  simp

/-- Cochrane (2023), §5.5.2, p. 152 ("With neither monetary policy shock nor rule, the interest
rate `i_t` and therefore long-term nominal bond return `r^n_{t+1}` do not move"): with
`θ_iπ = θ_ix = 0` and no monetary disturbance, every equilibrium has `q ≡ 0` and `r^n ≡ 0`. -/
theorem bonds_zero_noRule {P : Params} (hθπ : P.thIpi = 0) (hθx : P.thIx = 0)
    (hω : |P.omega| < 1) {es us : ℕ → Ω → ℝ} {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ}
    (h : RedEquil 𝔼 P 0 es 0 us p0 v0 x p q v) : q = 0 ∧ ∀ t, rnNext P q t = 0 := by
  obtain ⟨⟨-, -, -, -, h72⟩, -, -, haq, -, -, -, hbq, -, -, -⟩ := h
  have hqs := (eq572_iff 𝔼 haq).mp h72
  have hq0 : q = 0 := 𝔼.forward_unique hω hqs (fun t => by simp [iRule, hθπ, hθx]) hbq
    ⟨0, fun _ _ => by simp⟩
  exact ⟨hq0, fun t => by simp [rnNext, hq0]⟩

/-- Cochrane (2023), §5.5.2, p. 152 ("Long-term debt therefore has no influence on these
responses, which are the same for any bond maturity `ω`"): the `(x, π)` block does not involve
`ω`. -/
theorem blockMat_omega_indep (P : Params) (w : ℝ) :
    blockMat { P with omega := w } = blockMat P := rfl

/-- Cochrane (2023), §5.5.4, p. 157 ("With no policy rule reactions `θ = 0`, the nominal interest
rate `i_t` … just follows the AR(1) shock process `u_{i,t}`"). -/
theorem i_follows_u_noRule {P : Params} (hθπ : P.thIpi = 0) (hθx : P.thIx = 0)
    (x p ui : ℕ → Ω → ℝ) (t : ℕ) : iRule P x p ui t = ui t := by
  simp [iRule, hθπ, hθx]

/-- Cochrane (2023), §5.5.2, p. 152 ("The real rate falls exactly as inflation rises"): with
`θ = 0` and no monetary disturbance the ex-ante real rate is `i_t − E_tπ_{t+1} = −E_tπ_{t+1}`. -/
theorem real_rate_noRule {P : Params} (hθπ : P.thIpi = 0) (hθx : P.thIx = 0)
    (x p : ℕ → Ω → ℝ) (t : ℕ) :
    iRule P x p 0 t - 𝔼.E t (p (t + 1)) = -𝔼.E t (p (t + 1)) := by
  simp [iRule, hθπ, hθx]

/-! ### Present values of AR(1) responses, (5.75) and E40 -/

/-- Cochrane (2023), (5.75), p. 151 and §5.5.2, p. 152 ("The cumulative fiscal disturbance is
`ΔE_1 ∑ ρʲ u_{s,1+j} = 1/(1 − ρη_s)`"): for a bounded AR(1) process `y` with
`E_t y_{t+1} = λ y_t` and weights `0 ≤ w < 1`, `|wλ| < 1`, the innovation of the weighted sum of
current and future values is `(1 − wλ)⁻¹` times the innovation of `y_{t+1}`. -/
theorem innov_weighted_ar1 {y : ℕ → Ω → ℝ} {lam w M : ℝ} (hy : 𝔼.IsAR1 lam y)
    (hb : ∀ t ω, |y t ω| ≤ M) (hw0 : 0 ≤ w) (hw1 : w < 1) (hwl : |w * lam| < 1) (t : ℕ) :
    innov 𝔼 t (fun ω => ∑' j, w ^ j * y (t + 1 + j) ω) =
      (1 - w * lam)⁻¹ • innov 𝔼 t (y (t + 1)) := by
  have hf : ∀ (k : ℕ) (ω : Ω), |(fun ω => w ^ k * y (t + 1 + k) ω) ω| ≤ w ^ k * M := by
    intro k ω
    simp only [abs_mul, abs_pow, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left (hb _ ω) (pow_nonneg hw0 k)
  have h1 : ∀ k, 𝔼.E (t + 1) (fun ω => w ^ k * y (t + 1 + k) ω) =
      (w * lam) ^ k • y (t + 1) := by
    intro k
    have e := 𝔼.ar1_iterate hy (t + 1) k
    rw [show (fun ω => w ^ k * y (t + 1 + k) ω) = w ^ k • y (t + 1 + k) from rfl, map_smul, e,
      smul_smul, mul_pow]
  have h2 : ∀ k, 𝔼.E t (fun ω => w ^ k * y (t + 1 + k) ω) =
      (w * lam) ^ k • 𝔼.E t (y (t + 1)) := by
    intro k
    rw [← 𝔼.tower (Nat.le_succ t), h1 k, map_smul]
  funext ω
  simp only [innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [𝔼.E_tsum hw0 hw1 hf, 𝔼.E_tsum hw0 hw1 hf]
  simp only [h1, h2, Pi.smul_apply, smul_eq_mul]
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_abs_lt_one hwl, hy.1 (t + 1)]
  ring

/-- Cochrane (2023), (5.75), p. 151 and Table 5.1 (the deficit-shock responses): after fiscal
shocks only, in every equilibrium the innovation in `ω`-weighted inflation is
`−β_s/(1 − ωλ_s) ε_{s,t+1}` and the innovation in the `ρ`-discounted fiscal disturbance is
`ε_{s,t+1}/(1 − ρη_s)`. -/
theorem fiscal_shock_sums {P : Params} (hP : Standard P) (hpass : Passive P)
    (hηi : |P.etaI| < 1) (hω0 : 0 ≤ P.omega) (hω1 : P.omega < 1) (hρ0 : 0 ≤ P.rho)
    (hρ1 : P.rho < 1) (hηs : |P.etaS| < 1) {es us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P 0 es 0 us)
    {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ} (h : RedEquil 𝔼 P 0 es 0 us p0 v0 x p q v) (t : ℕ) :
    innov 𝔼 t (fun ω => ∑' j, P.omega ^ j * p (t + 1 + j) ω) =
        (-(P.betaS / (1 - P.omega * lamS P))) • es (t + 1) ∧
      innov 𝔼 t (fun ω => ∑' j, P.rho ^ j * us (t + 1 + j) ω) =
        (1 - P.rho * P.etaS)⁻¹ • es (t + 1) := by
  have hsh' := hsh
  obtain ⟨-, -, -, husa, -, -, -, ⟨Mu, hMu⟩, -, hes, -, husl⟩ := hsh'
  obtain ⟨⟨h64, h65, h68, -, -⟩, -, hap, -, -, hbx, hbp, -, -, -, -⟩ := h
  obtain ⟨-, hEp⟩ := fiscal_ar1 𝔼 hP hpass hηi hsh h64 h65 hbx hbp
  obtain ⟨-, -, hl1, hl2, -, -⟩ := roots_passive hP hpass
  obtain ⟨Mp, hMp⟩ := hbp
  have hlam : |lamS P| < 1 := abs_lt.mpr ⟨hl1, hl2⟩
  have hwlam : |P.omega * lamS P| < 1 := by
    rw [abs_mul, abs_of_nonneg hω0]
    nlinarith [abs_nonneg (lamS P)]
  have hρη : |P.rho * P.etaS| < 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]
    nlinarith [abs_nonneg P.etaS]
  have hne : 1 - P.omega * lamS P ≠ 0 := by
    have := (abs_lt.mp hwlam).2
    linarith
  constructor
  · rw [innov_weighted_ar1 𝔼 ⟨hap, hEp⟩ hMp hω0 hω1 hwlam t, h68 t]
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul,
      mul_zero, sub_zero]
    field_simp
  · rw [innov_weighted_ar1 𝔼 ⟨husa, E_ar1 𝔼 husa hes husl⟩ hMu hρ0 hρ1 hρη t,
      innov_ar1 𝔼 husa hes husl t]

/-- Cochrane (2023), (5.75), p. 151 and (5.80), p. 154: choosing `β_s` so that the `ω`-weighted
inflation response is `0.4` times the fiscal disturbance (in absolute value; the two have
opposite signs) gives `β_s = 0.4 (1 − ωλ_s)/(1 − ρη_s)`. -/
theorem betaS_of_ratio {P : Params} (hP : Standard P) (hpass : Passive P) (hηi : |P.etaI| < 1)
    (hω0 : 0 ≤ P.omega) (hω1 : P.omega < 1) (hρ0 : 0 ≤ P.rho) (hρ1 : P.rho < 1)
    (hηs : |P.etaS| < 1) {es us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P 0 es 0 us) {p0 v0 : ℝ}
    {x p q v : ℕ → Ω → ℝ} (h : RedEquil 𝔼 P 0 es 0 us p0 v0 x p q v) (t : ℕ) (ω : Ω)
    (hε : es (t + 1) ω ≠ 0)
    (hratio : innov 𝔼 t (fun ω => ∑' j, P.omega ^ j * p (t + 1 + j) ω) ω =
      -(0.4 * innov 𝔼 t (fun ω => ∑' j, P.rho ^ j * us (t + 1 + j) ω) ω)) :
    P.betaS = 0.4 * (1 - P.omega * lamS P) / (1 - P.rho * P.etaS) := by
  obtain ⟨h1, h2⟩ := fiscal_shock_sums 𝔼 hP hpass hηi hω0 hω1 hρ0 hρ1 hηs hsh h t
  rw [h1, h2] at hratio
  simp only [Pi.smul_apply, smul_eq_mul] at hratio
  obtain ⟨-, -, hl1, hl2, -, -⟩ := roots_passive hP hpass
  have hne1 : 1 - P.omega * lamS P ≠ 0 := by
    have : P.omega * lamS P < 1 := by nlinarith
    linarith
  have hne2 : 1 - P.rho * P.etaS ≠ 0 := by
    have : P.rho * P.etaS < 1 := by nlinarith [(abs_lt.mp hηs).2, (abs_lt.mp hηs).1]
    linarith
  field_simp at hratio ⊢
  linear_combination (-1 : ℝ) * hratio

/-- Cochrane (2023), §5.5 (tool for the numerical claims): for `z < λ_u`, the characteristic
polynomial is positive at `z` iff `z < λ_s`. -/
theorem charB_pos_iff {P : Params} (hP : Standard P) (hpass : Passive P) {z : ℝ}
    (hz : z < lamU P) : 0 < charB P z ↔ z < lamS P := by
  rw [charB_factor hP hpass]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- Cochrane (2023), §5.5.3, p. 155 ("The policy rules produce even more drawn-out inflation"):
with the book's rules (5.76)–(5.77) the inflation persistence is `λ_s ∈ (0.919, 0.920)`. -/
theorem lamS_bookRules : 0.919 < lamS bookRules ∧ lamS bookRules < 0.92 := by
  have hP := bookRules_standard
  have hpass := bookRules_passive
  have hU := (roots_passive hP hpass).2.1
  have hval : ∀ z : ℝ, charB bookRules z = z ^ 2 - (1 + 0.5 * 0.5 / 0.99 + 0.5 * 0.5 + 1 / 0.99) * z
      + ((1 + 0.5 * 0.5 / 0.99 + 0.5 * 0.5) * (1 / 0.99) - 0.5 * (0.8 - 1 / 0.99) *
        (-(0.5 / 0.99))) := by
    intro z
    simp only [charB, trB, detB, aXX, aXP, aPX, aPP, bookRules]
  constructor
  · exact (charB_pos_iff hP hpass (by linarith)).mp (by rw [hval]; norm_num)
  · by_contra hc
    push Not at hc
    have h1 : ¬ (0 < charB bookRules 0.92) := by rw [hval]; norm_num
    rcases hc.lt_or_eq with h | h
    · exact h1 ((charB_pos_iff hP hpass (by linarith)).mpr h)
    · have : charB bookRules (lamS bookRules) = 0 := by
        rw [charB_factor hP hpass]; ring
      rw [← h] at this
      rw [hval] at this
      norm_num at this

/-- Cochrane (2023), §5.5.2, p. 152: without policy rules (`θ = 0`) the inflation persistence
is `λ_s ∈ (0.611, 0.612)`. -/
theorem lamS_bookNoRules : 0.611 < lamS bookNoRules ∧ lamS bookNoRules < 0.612 := by
  have hP : Standard bookNoRules := by norm_num [Standard, bookNoRules]
  have hpass : Passive bookNoRules := by norm_num [Passive, bookNoRules]
  have hU := (roots_passive hP hpass).2.1
  have hval : ∀ z : ℝ, charB bookNoRules z = z ^ 2 - (1 + 0.5 * 0.5 / 0.99 + 0.5 * 0 + 1 / 0.99)
      * z + ((1 + 0.5 * 0.5 / 0.99 + 0.5 * 0) * (1 / 0.99) - 0.5 * (0 - 1 / 0.99) *
        (-(0.5 / 0.99))) := by
    intro z
    simp only [charB, trB, detB, aXX, aXP, aPX, aPP, bookNoRules]
  constructor
  · exact (charB_pos_iff hP hpass (by linarith)).mp (by rw [hval]; norm_num)
  · by_contra hc
    push Not at hc
    have h1 : ¬ (0 < charB bookNoRules 0.612) := by rw [hval]; norm_num
    rcases hc.lt_or_eq with h | h
    · exact h1 ((charB_pos_iff hP hpass (by linarith)).mpr h)
    · have : charB bookNoRules (lamS bookNoRules) = 0 := by
        rw [charB_factor hP hpass]; ring
      rw [← h] at this
      rw [hval] at this
      norm_num at this

/-- Cochrane (2023), §5.5.3, p. 155: the policy rules make the inflation response to a fiscal
shock more persistent, `λ_s(rules) > λ_s(θ = 0)`. -/
theorem rules_more_persistent : lamS bookNoRules < lamS bookRules := by
  linarith [lamS_bookRules.1, lamS_bookNoRules.2]

/-- Cochrane (2023), (5.79)–(5.80), p. 154 and (5.75) (E40): with the book's rules, the 0.4-ratio
rule gives `β_s ∈ (0.136, 0.137)` (printed `0.14`) when `η_s = 0.5`, but `β_s ∈ (0.113, 0.115)`
with the printed `η_s = 0.4`. -/
theorem betaS_bookRules_etaS :
    (0.136 < 0.4 * (1 - 0.9 * lamS bookRules) / (1 - 0.99 * 0.5) ∧
      0.4 * (1 - 0.9 * lamS bookRules) / (1 - 0.99 * 0.5) < 0.137) ∧
    (0.113 < 0.4 * (1 - 0.9 * lamS bookRules) / (1 - 0.99 * 0.4) ∧
      0.4 * (1 - 0.9 * lamS bookRules) / (1 - 0.99 * 0.4) < 0.115) := by
  obtain ⟨h1, h2⟩ := lamS_bookRules
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- Cochrane (2023), (5.75), p. 151 ("The choice (5.75) produces `β_s = 0.36`"): without rules
the 0.4-ratio rule gives `β_s ∈ (0.355, 0.357)`. -/
theorem betaS_bookNoRules :
    0.355 < 0.4 * (1 - 0.9 * lamS bookNoRules) / (1 - 0.99 * 0.5) ∧
      0.4 * (1 - 0.9 * lamS bookNoRules) / (1 - 0.99 * 0.5) < 0.357 := by
  obtain ⟨h1, h2⟩ := lamS_bookNoRules
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- Cochrane (2023), Table 5.1 "Fiscal, yes θ" and (5.79) (E40): under the 0.4-ratio rule
(5.75) the `ω`-weighted inflation response to a unit deficit shock is `0.4/(1 − ρη_s)`; the
printed `0.79` is `η_s = 0.5` (0.792), not the printed `η_s = 0.4` (0.662). -/
theorem table51_fiscal_yesRule_etaS :
    |0.4 / (1 - 0.99 * 0.5) - 0.79| ≤ (0.005 : ℝ) ∧
      ¬ |0.4 / (1 - 0.99 * 0.4) - 0.79| ≤ (0.005 : ℝ) := by
  constructor
  · rw [abs_le]; constructor <;> norm_num
  · rw [abs_le]; norm_num

/-- Cochrane (2023), Table 5.1, p. 153, "Monetary, no θ", second panel (E41): with `π_1`,
`r^n_1` and the discount-rate term as printed (to rounding), identity (3.20) is violated by the
printed surplus term `2.58`. -/
theorem table51_monetary_noRule_printed_false {π1 rn1 S R : ℝ} (hπ : |π1 + 0.65| ≤ 0.005)
    (hrn : |rn1 + 2.43| ≤ 0.005) (hS : |S - 2.58| ≤ 0.005) (hR : |R - 2.04| ≤ 0.005) :
    π1 - rn1 ≠ -S + R := by
  intro h
  rw [abs_le] at hπ hrn hS hR
  obtain ⟨_, _⟩ := hπ
  obtain ⟨_, _⟩ := hrn
  obtain ⟨_, _⟩ := hS
  obtain ⟨_, _⟩ := hR
  linarith

/-- Cochrane (2023), Table 5.1, p. 153, "Monetary, no θ" (E41, corrected): identity (3.20) with
the printed `π_1, r^n_1` and discount-rate term forces the surplus term to be `0.26` (within
rounding), not `2.58`. -/
theorem table51_monetary_noRule_corrected {π1 rn1 S R : ℝ} (hπ : |π1 + 0.65| ≤ 0.005)
    (hrn : |rn1 + 2.43| ≤ 0.005) (hR : |R - 2.04| ≤ 0.005) (hid : π1 - rn1 = -S + R) :
    |S - 0.26| ≤ 0.015 := by
  rw [abs_le] at hπ hrn hR ⊢
  constructor <;> linarith [hπ.1, hπ.2, hrn.1, hrn.2, hR.1, hR.2]

/-- Cochrane (2023), Table 5.1, p. 153, "Monetary, no θ", first panel (E41): with
`∑ ωʲ π_{1+j} = 0` by construction (5.81), identity (3.22) makes the discount-rate term equal to
the corrected surplus term `≈ 0.26`; the printed `2.58` is impossible. -/
theorem table51_monetary_noRule_panel1 {S D : ℝ} (h322 : (0 : ℝ) = -S + D)
    (hS : |S - 0.26| ≤ 0.015) : |D - 0.26| ≤ 0.015 ∧ ¬ |D - 2.58| ≤ 0.005 := by
  have hD : D = S := by linarith
  subst hD
  refine ⟨hS, fun h => ?_⟩
  rw [abs_le] at hS h
  linarith [hS.2, h.1]

/-- Cochrane (2023), p. 158 ("the offsetting surplus and discount-rate effects are an order of
magnitude smaller, 0.28 not 2.58") is false (E41): the "Monetary, yes θ" row (3.20) gives
`0.28`, the corrected "no θ" value is `0.26`, and `0.28` is not an order of magnitude smaller. -/
theorem table51_order_of_magnitude_false {π1 rn1 S R S' : ℝ} (hπ : |π1 + 0.65| ≤ 0.005)
    (hrn : |rn1 + 2.43| ≤ 0.005) (hR : |R - 2.04| ≤ 0.005) (hid : π1 - rn1 = -S + R)
    {π1' rn1' R' : ℝ} (hπ' : |π1' + 0.69| ≤ 0.005) (hrn' : |rn1' + 1.75| ≤ 0.005)
    (hR' : |R' - 1.34| ≤ 0.005) (hid' : π1' - rn1' = -S' + R') :
    |S' - 0.28| ≤ 0.015 ∧ ¬ (10 * S' ≤ S) := by
  have hS := table51_monetary_noRule_corrected hπ hrn hR hid
  rw [abs_le] at hπ' hrn' hR' hS
  refine ⟨?_, fun h => ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hπ'.1, hπ'.2, hrn'.1, hrn'.2, hR'.1, hR'.2]
  · linarith [hπ'.1, hπ'.2, hrn'.1, hrn'.2, hR'.1, hR'.2, hS.1, hS.2]

/-- Cochrane (2023), Table 5.1, p. 153, third panel (E41): with `∑_{j≥0} ωʲ π_{1+j} = 0`,
identity (3.21) `r^n_1 = −∑_{j≥1} ωʲ r_{1+j} − ∑_{j≥1} ωʲ π_{1+j}` gives, for "Monetary, no θ",
the real-return term `≈ 1.78` (printed `0.64`), and for "Monetary, yes θ" the inflation term
`≈ 0.69` (printed `0.64`) with the real-return term `≈ 1.06`. -/
theorem table51_panel3 {π1 rn1 W Pw π1' rn1' W' Pw' : ℝ} (hπ : |π1 + 0.65| ≤ 0.005)
    (hrn : |rn1 + 2.43| ≤ 0.005) (hsum : π1 + Pw = 0) (h321 : rn1 = -W - Pw)
    (hπ' : |π1' + 0.69| ≤ 0.005) (hrn' : |rn1' + 1.75| ≤ 0.005) (hsum' : π1' + Pw' = 0)
    (h321' : rn1' = -W' - Pw') :
    (|W - 1.78| ≤ 0.01 ∧ ¬ |W - 0.64| ≤ 0.005) ∧
      (|Pw' - 0.69| ≤ 0.005 ∧ ¬ |Pw' - 0.64| ≤ 0.005 ∧ |W' - 1.06| ≤ 0.01) := by
  rw [abs_le] at hπ hrn hπ' hrn'
  refine ⟨⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_, ?_⟩⟩
  · rw [abs_le]; constructor <;> linarith [hπ.1, hπ.2, hrn.1, hrn.2]
  · rw [abs_le] at h; linarith [hπ.1, hπ.2, hrn.1, hrn.2, h.1, h.2]
  · rw [abs_le]; constructor <;> linarith [hπ'.1, hπ'.2]
  · rw [abs_le] at h; linarith [hπ'.1, hπ'.2, h.1, h.2]
  · rw [abs_le]; constructor <;> linarith [hπ'.1, hπ'.2, hrn'.1, hrn'.2]

/-! ### (5.74): splitting unexpected deficits -/

/-- Cochrane (2023), p. 150: with `θ_sx = 0` the surplus rule (5.54) gives
`ΔE_{t+1} s̃_{t+1} = θ_sπ ΔE_{t+1} π_{t+1} + ε_{s,t+1}`. -/
theorem innov_sNext {P : Params} (hθ : P.thSx = 0) {x p vs us es : ℕ → Ω → ℝ}
    (hvs : 𝔼.Adapted vs) (hus : 𝔼.Adapted us) (hes : ∀ t, 𝔼.E t (es (t + 1)) = 0)
    (hl : ∀ t, us (t + 1) = P.etaS • us t + es (t + 1)) (t : ℕ) :
    innov 𝔼 t (sNext P x p vs us t) = P.thSpi • innov 𝔼 t (p (t + 1)) + es (t + 1) := by
  rw [sNext, hθ, zero_smul, add_zero, innov_add, innov_add, innov_smul, innov_smul,
    innov_known 𝔼 hvs, innov_ar1 𝔼 hus hes hl, smul_zero, add_zero]

/-- Cochrane (2023), (5.74), p. 150: if unexpected inflation is a fraction `β̂_s` of the
unexpected deficit, `ΔE π = −β̂_s ΔE s̃`, and `ΔE s̃ = θ_sπ ΔE π + ε_s`, then
`ΔE π = −β̂_s/(1 + β̂_sθ_sπ) ε_s` (requires `1 + β̂_sθ_sπ ≠ 0`). -/
theorem betaHat_574 {θ bh : ℝ} (h1 : 1 + bh * θ ≠ 0) {dp ds e : Ω → ℝ}
    (hs : ds = θ • dp + e) (h574 : dp = -(bh • ds)) : dp = (-(bh / (1 + bh * θ))) • e := by
  funext ω
  have a := congrFun hs ω
  have b := congrFun h574 ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at a b ⊢
  linear_combination (norm := (field_simp; ring)) (b - bh * a) / (1 + bh * θ)

/-- Cochrane (2023), (5.74), p. 150 (the excluded case): if `1 + β̂_sθ_sπ = 0`, (5.74) and the
surplus rule are consistent only when the fiscal shock is zero. -/
theorem betaHat_574_degenerate {θ bh : ℝ} (h1 : 1 + bh * θ = 0) {dp ds e : Ω → ℝ}
    (hs : ds = θ • dp + e) (h574 : dp = -(bh • ds)) : e = 0 := by
  have hbh : bh ≠ 0 := by
    intro h
    rw [h] at h1
    norm_num at h1
  funext ω
  have a := congrFun hs ω
  have b := congrFun h574 ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at a b
  have : bh * e ω = 0 := by linear_combination b - bh * a - dp ω * h1
  simpa [hbh] using this

/-! ### Table 5.1: the identities (3.20)–(3.22) -/

/-- Cochrane (2023), (5.73) and (3.21), p. 65: the nominal bond return dated `t`,
`r^n_{t+1} = ω q_{t+1} − q_t` (and `0` at date `0`). -/
def rnSeq (w : ℝ) (q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => w • q (t + 1) - q t

/-- Cochrane (2023), (3.17), p. 63: the real return `r_t = r^n_t − π_t`. -/
def rSeq (w : ℝ) (q p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := rnSeq w q t - p t

/-- Cochrane (2023), (3.18)–(3.19), pp. 63–64: iterating the flow identity
`ρ v_{t+1} = v_t + r_{t+1} − s_{t+1}` forward with bounded `v` (`0 ≤ ρ < 1`), the value of debt is
the present value `v_t = ∑ ρʲ (s_{t+1+j} − r_{t+1+j})`, pathwise. -/
theorem pv_identity {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v r s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + r (t + 1) - s (t + 1)) (hbv : BoundedProc v)
    (hbs : BoundedProc s) (hbr : BoundedProc r) (t : ℕ) (ω : Ω) :
    v t ω = ∑' j, ρ ^ j * (s (t + 1 + j) ω - r (t + 1 + j) ω) := by
  obtain ⟨Mv, hMv⟩ := hbv
  obtain ⟨Ms, hMs⟩ := hbs
  obtain ⟨Mr, hMr⟩ := hbr
  have hsum : Summable fun j => ρ ^ j * (s (t + 1 + j) ω - r (t + 1 + j) ω) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right (Ms + Mr))
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 j)]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMs _ ω) (hMr _ ω)))
      (pow_nonneg hρ0 j)
  have hpart : ∀ N, ∑ j ∈ Finset.range N, ρ ^ j * (s (t + 1 + j) ω - r (t + 1 + j) ω) =
      v t ω - ρ ^ N * v (t + N) ω := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have e := congrFun (hflow (t + N)) ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
      rw [show t + (N + 1) = t + N + 1 by ring, show t + 1 + N = t + N + 1 by ring, pow_succ]
      linear_combination (ρ ^ N) * e
  have hlim : Tendsto (fun N => v t ω - ρ ^ N * v (t + N) ω) atTop (𝓝 (v t ω)) := by
    have h0 : Tendsto (fun N => ρ ^ N * v (t + N) ω) atTop (𝓝 0) := by
      have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const Mv
      rw [zero_mul] at hg
      refine squeeze_zero_norm (fun N => ?_) hg
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 N)]
      exact mul_le_mul_of_nonneg_left (hMv _ ω) (pow_nonneg hρ0 N)
    simpa using tendsto_const_nhds.sub h0
  have h1 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h1
  exact tendsto_nhds_unique hlim h1

/-- Cochrane (2023), (3.20)–(3.22) (tool): the innovation commutes with a geometrically
dominated series. -/
theorem innov_tsum {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ω, |f k ω| ≤ a ^ k * M) (t : ℕ) :
    innov 𝔼 t (fun ω => ∑' k, f k ω) = fun ω => ∑' k, innov 𝔼 t (f k) ω := by
  funext ω
  have hs : ∀ s, Summable fun k => 𝔼.E s (f k) ω := fun s =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right M)
      (fun k => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) s ω)
  simp only [innov, Pi.sub_apply]
  rw [𝔼.E_tsum ha0 ha1 hf, 𝔼.E_tsum ha0 ha1 hf, ← (hs (t + 1)).tsum_sub (hs t)]

/-- Cochrane (2023), (3.20)–(3.22) (tool): a geometric series with bounded coefficients
converges. -/
theorem summable_geom_bdd {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {g : ℕ → ℝ}
    (hg : ∀ k, |g k| ≤ M) : Summable fun k => a ^ k * g k :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right M)
    (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 k)]
      exact mul_le_mul_of_nonneg_left (hg k) (pow_nonneg ha0 k))

/-- Cochrane (2023), (3.21) (tool): the bond return of a bounded bond price is bounded. -/
theorem rnSeq_bounded {w : ℝ} {q : ℕ → Ω → ℝ} (hbq : BoundedProc q) : BoundedProc (rnSeq w q) := by
  obtain ⟨M, hM⟩ := bdd_sub (bdd_smul w (bdd_shift hbq)) hbq
  refine ⟨|M|, fun t ω => ?_⟩
  cases t with
  | zero => simp [rnSeq]
  | succ t => exact (hM t ω).trans (le_abs_self M)

/-- Cochrane (2023), (3.20)–(3.22) (tool): `ΔE_{t+1}` of the present value of the next period,
`ΔE_{t+1} v_{t+1} = ∑ ρʲ (ΔE_{t+1} s_{t+2+j} − ΔE_{t+1} r_{t+2+j})`. -/
theorem innov_pv_next {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v r s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + r (t + 1) - s (t + 1)) (hbv : BoundedProc v)
    (hbs : BoundedProc s) (hbr : BoundedProc r) (t : ℕ) :
    innov 𝔼 t (v (t + 1)) = fun ω => ∑' j, ρ ^ j *
      (innov 𝔼 t (s (t + 1 + (j + 1))) ω - innov 𝔼 t (r (t + 1 + (j + 1))) ω) := by
  obtain ⟨Ms, hMs⟩ := hbs
  obtain ⟨Mr, hMr⟩ := hbr
  have hv : v (t + 1) = fun ω => ∑' j, ρ ^ j *
      (s (t + 1 + (j + 1)) ω - r (t + 1 + (j + 1)) ω) := by
    funext ω
    rw [pv_identity hρ0 hρ1 hflow hbv ⟨Ms, hMs⟩ ⟨Mr, hMr⟩ (t + 1) ω]
    refine tsum_congr fun j => ?_
    rw [show t + 1 + 1 + j = t + 1 + (j + 1) by ring]
  rw [hv, innov_tsum 𝔼 hρ0 hρ1 (M := Ms + Mr) (fun k ω => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMs _ ω) (hMr _ ω)))
      (pow_nonneg hρ0 k)) t]
  funext ω
  refine tsum_congr fun j => ?_
  rw [show (fun ω => ρ ^ j * (s (t + 1 + (j + 1)) ω - r (t + 1 + (j + 1)) ω)) =
    ρ ^ j • (s (t + 1 + (j + 1)) - r (t + 1 + (j + 1))) from rfl, innov_smul, innov_sub]
  rfl

/-- **Identity (3.20)** (Cochrane (2023), p. 65; Table 5.1, second panel, p. 153): for any
bounded adapted value of debt `v`, bond price `q`, inflation `π` and surplus `s̃` satisfying the
flow identity (5.71) `ρ v_{t+1} = v_t + r_{t+1} − s̃_{t+1}` (`r = r^n − π`, `r^n` from (5.73)),
`ΔE π_{t+1} − ΔE r^n_{t+1} = −∑_{j≥0} ρʲ ΔE s̃_{t+1+j} + ∑_{j≥1} ρʲ ΔE r_{t+1+j}`. -/
theorem identity_320 {ρ w : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v q p s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + rSeq w q p (t + 1) - s (t + 1))
    (hav : 𝔼.Adapted v) (hbv : BoundedProc v) (hbq : BoundedProc q) (hbp : BoundedProc p)
    (hbs : BoundedProc s) (t : ℕ) :
    innov 𝔼 t (p (t + 1)) - innov 𝔼 t (rnSeq w q (t + 1)) =
      -(fun ω => ∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) +
        fun ω => ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω := by
  have hbr : BoundedProc (rSeq w q p) := bdd_sub (rnSeq_bounded hbq) hbp
  have hIv := innov_pv_next 𝔼 hρ0 hρ1 hflow hbv hbs hbr t
  obtain ⟨Ms, hMs⟩ := hbs
  obtain ⟨Mr, hMr⟩ := hbr
  have e1 : ρ • innov 𝔼 t (v (t + 1)) =
      innov 𝔼 t (rSeq w q p (t + 1)) - innov 𝔼 t (s (t + 1)) := by
    rw [← innov_smul, hflow t, innov_sub, innov_add, innov_known 𝔼 hav, zero_add]
  have er : innov 𝔼 t (rSeq w q p (t + 1)) =
      innov 𝔼 t (rnSeq w q (t + 1)) - innov 𝔼 t (p (t + 1)) := innov_sub 𝔼 t _ _
  funext ω
  have e1ω := congrFun e1 ω
  have erω := congrFun er ω
  rw [hIv] at e1ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1ω erω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
  set a : ℕ → ℝ := fun j => innov 𝔼 t (s (t + 1 + (j + 1))) ω with ha
  set b : ℕ → ℝ := fun j => innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω with hb
  have hsa : Summable fun j => ρ ^ j * a j :=
    summable_geom_bdd hρ0 hρ1 (fun k => abs_innov_le 𝔼 (hMs _) t ω)
  have hsb : Summable fun j => ρ ^ j * b j :=
    summable_geom_bdd hρ0 hρ1 (fun k => abs_innov_le 𝔼 (hMr _) t ω)
  have hsum0 : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω :=
    summable_geom_bdd hρ0 hρ1 (fun k => abs_innov_le 𝔼 (hMs _) t ω)
  have e3 : ∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω =
      innov 𝔼 t (s (t + 1)) ω + ∑' j, ρ ^ (j + 1) * a j := by
    rw [hsum0.tsum_eq_zero_add]
    simp [ha]
  have e4 : ρ * ∑' j, ρ ^ j * (a j - b j) =
      ∑' j, ρ ^ (j + 1) * a j - ∑' j, ρ ^ (j + 1) * b j := by
    have h1 : Summable fun j => ρ ^ (j + 1) * a j := (hsa.mul_left ρ).congr (fun j => by ring)
    have h2 : Summable fun j => ρ ^ (j + 1) * b j := (hsb.mul_left ρ).congr (fun j => by ring)
    rw [← h1.tsum_sub h2, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have e4' : ∑' j, ρ ^ (j + 1) * b j = ∑' j, ρ ^ (j + 1) * innov 𝔼 t
      (rSeq w q p (t + 1 + (j + 1))) ω := rfl
  rw [e3]
  linarith

/-- **Identity (3.21)** (Cochrane (2023), p. 65; Table 5.1, third panel, p. 153): for a bounded
adapted bond price `q` (`0 ≤ ω < 1`), with `r^n_{t+1} = ω q_{t+1} − q_t` (5.73) and
`r = r^n − π`, `ΔE r^n_{t+1} = −∑_{j≥1} ωʲ ΔE r_{t+1+j} − ∑_{j≥1} ωʲ ΔE π_{t+1+j}`. -/
theorem identity_321 {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {q p : ℕ → Ω → ℝ}
    (haq : 𝔼.Adapted q) (hbq : BoundedProc q) (hbp : BoundedProc p) (t : ℕ) :
    innov 𝔼 t (rnSeq w q (t + 1)) =
      -(fun ω => ∑' j, w ^ (j + 1) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω) -
        fun ω => ∑' j, w ^ (j + 1) * innov 𝔼 t (p (t + 1 + (j + 1))) ω := by
  have hbrn := rnSeq_bounded (w := w) hbq
  have hflow : ∀ t, w • q (t + 1) = q t + rnSeq w q (t + 1) - (0 : ℕ → Ω → ℝ) (t + 1) := by
    intro t
    simp only [rnSeq, Pi.zero_apply, sub_zero]
    abel
  have hIq := innov_pv_next 𝔼 hw0 hw1 hflow hbq ⟨0, fun _ _ => by simp⟩ hbrn t
  have e1 : innov 𝔼 t (rnSeq w q (t + 1)) = w • innov 𝔼 t (q (t + 1)) := by
    rw [show rnSeq w q (t + 1) = w • q (t + 1) - q t from rfl, innov_sub, innov_smul,
      innov_known 𝔼 haq, sub_zero]
  obtain ⟨Mp, hMp⟩ := hbp
  obtain ⟨Mr, hMr⟩ := bdd_sub hbrn ⟨Mp, hMp⟩
  rw [e1, hIq]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
  have hz : innov 𝔼 t (0 : Ω → ℝ) = 0 := by
    simp [innov]
  simp only [hz, Pi.zero_apply, zero_sub]
  have hsplit : ∀ j, innov 𝔼 t (rnSeq w q (t + 1 + (j + 1))) ω =
      innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω + innov 𝔼 t (p (t + 1 + (j + 1))) ω := by
    intro j
    rw [rSeq, innov_sub]
    simp
  simp only [hsplit]
  have hsa : Summable fun j => w ^ j * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω :=
    summable_geom_bdd hw0 hw1 (fun k => abs_innov_le 𝔼 (hMr _) t ω)
  have hsb : Summable fun j => w ^ j * innov 𝔼 t (p (t + 1 + (j + 1))) ω :=
    summable_geom_bdd hw0 hw1 (fun k => abs_innov_le 𝔼 (hMp _) t ω)
  have h1 : Summable fun j => w ^ (j + 1) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω :=
    (hsa.mul_left w).congr (fun j => by ring)
  have h2 : Summable fun j => w ^ (j + 1) * innov 𝔼 t (p (t + 1 + (j + 1))) ω :=
    (hsb.mul_left w).congr (fun j => by ring)
  rw [← tsum_mul_left, ← tsum_neg, ← h1.neg.tsum_sub h2]
  exact tsum_congr fun j => by ring

/-- **Identity (3.22)** (Cochrane (2023), p. 65; Table 5.1, first panel, p. 153): under the
hypotheses of (3.20) and (3.21),
`∑_{j≥0} ωʲ ΔE π_{t+1+j} = −∑_{j≥0} ρʲ ΔE s̃_{t+1+j} + ∑_{j≥1} (ρʲ − ωʲ) ΔE r_{t+1+j}`. -/
theorem identity_322 {ρ w : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    {v q p s : ℕ → Ω → ℝ} (hflow : ∀ t, ρ • v (t + 1) = v t + rSeq w q p (t + 1) - s (t + 1))
    (hav : 𝔼.Adapted v) (haq : 𝔼.Adapted q) (hbv : BoundedProc v) (hbq : BoundedProc q)
    (hbp : BoundedProc p) (hbs : BoundedProc s) (t : ℕ) :
    (fun ω => ∑' j, w ^ j * innov 𝔼 t (p (t + 1 + j)) ω) =
      -(fun ω => ∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) +
        fun ω => ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) *
          innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω := by
  have h20 := identity_320 𝔼 hρ0 hρ1 hflow hav hbv hbq hbp hbs t
  have h21 := identity_321 𝔼 hw0 hw1 haq hbq hbp t
  have hbr : BoundedProc (rSeq w q p) := bdd_sub (rnSeq_bounded hbq) hbp
  obtain ⟨Mp, hMp⟩ := hbp
  obtain ⟨Mr, hMr⟩ := hbr
  funext ω
  have e20 := congrFun h20 ω
  have e21 := congrFun h21 ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at e20 e21 ⊢
  have hsp : Summable fun j => w ^ j * innov 𝔼 t (p (t + 1 + j)) ω :=
    summable_geom_bdd hw0 hw1 (fun k => abs_innov_le 𝔼 (hMp _) t ω)
  have hsr1 : Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω := by
    have := (summable_geom_bdd hρ0 hρ1 (fun k => abs_innov_le 𝔼 (hMr (t + 1 + (k + 1))) t ω)
      (g := fun j => innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω)).mul_left ρ
    refine this.congr fun j => ?_
    ring
  have hsr2 : Summable fun j => w ^ (j + 1) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω := by
    have := (summable_geom_bdd hw0 hw1 (fun k => abs_innov_le 𝔼 (hMr (t + 1 + (k + 1))) t ω)
      (g := fun j => innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω)).mul_left w
    refine this.congr fun j => ?_
    ring
  have e5 : ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω =
      ∑' j, ρ ^ (j + 1) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω -
        ∑' j, w ^ (j + 1) * innov 𝔼 t (rSeq w q p (t + 1 + (j + 1))) ω := by
    rw [← hsr1.tsum_sub hsr2]
    refine tsum_congr fun j => ?_
    ring
  rw [hsp.tsum_eq_zero_add, e5]
  simp only [pow_zero, one_mul, add_zero]
  linarith

/-- Cochrane (2023), §5.5.2, p. 152 ("With `β_s = 0` … the discounted sum of all future surpluses
would be exactly zero"): if inflation and the bond price do not move, identity (3.20) forces the
innovation in the discounted sum of surpluses to vanish. -/
theorem pv_surplus_innov_zero {ρ w : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + rSeq w 0 0 (t + 1) - s (t + 1))
    (hav : 𝔼.Adapted v) (hbv : BoundedProc v) (hbs : BoundedProc s) (t : ℕ) :
    (fun ω => ∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) = 0 := by
  have h := identity_320 𝔼 hρ0 hρ1 hflow hav hbv ⟨0, fun _ _ => by simp⟩
    ⟨0, fun _ _ => by simp⟩ hbs t
  have hr : ∀ k, rSeq w (0 : ℕ → Ω → ℝ) 0 k = 0 := by
    intro k
    cases k with
    | zero => simp [rSeq, rnSeq]
    | succ k => simp [rSeq, rnSeq]
  have hrn : rnSeq w (0 : ℕ → Ω → ℝ) (t + 1) = 0 := by simp [rnSeq]
  have hz : innov 𝔼 t (0 : Ω → ℝ) = 0 := by simp [innov]
  simp only [hr, hrn, hz, Pi.zero_apply, mul_zero, tsum_zero] at h
  funext ω
  have := congrFun h ω
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_self] at this
  simp only [Pi.zero_apply]
  linarith

/-! ### Online Appendix A1 §§1.9 and 1.11: the matrices and their eigenvalues -/

/-- Online Appendix A1 §1.9, p. 574 (tool): for a block-triangular `5 × 5` matrix,
`det(zI − [A B; 0 D]) = det(zI − A) det(zI − D)`. -/
theorem det_scalar_sub_fromBlocks {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R)
    (B : Matrix (Fin 3) (Fin 2) R) (D : Matrix (Fin 2) (Fin 2) R) (z : R) :
    (Matrix.scalar (Fin 3 ⊕ Fin 2) z - Matrix.fromBlocks A B 0 D).det =
      (Matrix.scalar (Fin 3) z - A).det * (Matrix.scalar (Fin 2) z - D).det := by
  have : Matrix.scalar (Fin 3 ⊕ Fin 2) z - Matrix.fromBlocks A B 0 D =
      Matrix.fromBlocks (Matrix.scalar (Fin 3) z - A) (-B) 0 (Matrix.scalar (Fin 2) z - D) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [this, Matrix.det_fromBlocks_zero₂₁]

/-- Online Appendix A1 §§1.9–1.11, pp. 574 and 579: a `5 × 5` transition matrix whose first three
rows are `(x, π, ·)` with the `(x, π)` block `[a b; c d]` and a third forward variable with own
coefficient `g`, and whose last two rows are the AR(1) disturbances `η_i, η_s`. -/
def mat5 (a b c d e f g h1 h2 : ℝ) (B : Matrix (Fin 3) (Fin 2) ℝ) :
    Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![a, b, 0; c, d, 0; e, f, g] B 0 !![h1, 0; 0, h2]

/-- Online Appendix A1 §1.9, p. 574: the eigenvalues of the block-triangular `5 × 5` matrix are
the two roots of the `(x, π)` block, `g`, `η_i` and `η_s`. -/
theorem eigs_mat5 (a b c d e f g h1 h2 : ℝ) (B : Matrix (Fin 3) (Fin 2) ℝ) :
    eigs (mat5 a b c d e f g h1 h2 B) =
      {root₁ (a + d) (a * d - b * c)} + {root₂ (a + d) (a * d - b * c)} + {(g : ℂ)} +
        {(h1 : ℂ)} + {(h2 : ℂ)} := by
  set m : Multiset ℂ := {root₁ (a + d) (a * d - b * c)} + {root₂ (a + d) (a * d - b * c)} +
    {(g : ℂ)} + {(h1 : ℂ)} + {(h2 : ℂ)} with hm
  have hs := root_sum (a + d) (a * d - b * c)
  have hp := root_prod (a + d) (a * d - b * c)
  have hpoly : ((mat5 a b c d e f g h1 h2 B).map Complex.ofReal).charpoly =
      (m.map fun r => Polynomial.X - Polynomial.C r).prod := by
    refine Polynomial.funext fun z => ?_
    rw [Matrix.eval_charpoly, mat5, Matrix.fromBlocks_map, Matrix.map_zero _ (by simp),
      det_scalar_sub_fromBlocks, Matrix.det_fin_three, Matrix.det_fin_two,
      Polynomial.eval_multiset_prod]
    simp only [hm, Multiset.map_add, Multiset.map_singleton, Multiset.prod_add,
      Multiset.prod_singleton, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    simp [Matrix.scalar_apply]
    push_cast at hs hp
    linear_combination (z - g) * (z - h1) * (z - h2) * (z * hs - hp)
  rw [eigs, hpoly, Polynomial.roots_multiset_prod_X_sub_C]

/-- Online Appendix A1 §1.9, p. 574: the transition matrix of the simple model (5.15)–(5.16)
with the rule `i_t = θ_iπ π_t + u_{i,t}` (1.40)–(1.43), in the order `(x, π, v, u_i, u_s)` (with
`θ_ix = 0` the first two rows are `1 + κσ/β, σθ_iπ − σ/β` and `−κ/β, 1/β`, `appA19_entries`). -/
noncomputable def appA19 (P : Params) : Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) ℝ :=
  mat5 (aXX P) (aXP P) (aPX P) (aPP P) (P.kappa / (P.rho * P.beta))
    ((P.thIpi - 1 / P.beta) / P.rho) (1 / P.rho) P.etaI P.etaS
    !![P.sigma, 0; 0, 0; 1 / P.rho, -(P.etaS / P.rho)]

/-- Online Appendix A1 §1.9, p. 574: with `θ_ix = 0` the `(x, π)` entries are the printed
`1 + κσ/β`, `σθ_iπ − σ/β`, `−κ/β`, `1/β`. -/
theorem appA19_entries {P : Params} (h : P.thIx = 0) :
    aXX P = 1 + P.kappa * P.sigma / P.beta ∧ aXP P = P.sigma * P.thIpi - P.sigma / P.beta ∧
      aPX P = -(P.kappa / P.beta) ∧ aPP P = 1 / P.beta := by
  refine ⟨by simp only [aXX, h]; ring, by simp only [aXP]; ring, rfl, rfl⟩

/-- Online Appendix A1 §1.9, p. 574 ("The eigenvalues of the transition matrix are
`ρ⁻¹, η_i, η_s, λ_+, λ_−`"). -/
theorem appA1_19_eigs (P : Params) :
    eigs (appA19 P) = {root₁ (trB P) (detB P)} + {root₂ (trB P) (detB P)} +
      {((1 / P.rho : ℝ) : ℂ)} + {(P.etaI : ℂ)} + {(P.etaS : ℂ)} := eigs_mat5 _ _ _ _ _ _ _ _ _ _

/-- Online Appendix A1 §1.9, p. 574 (E19, corrected): with `θ_ix = 0` the roots of the `(x, π)`
block are `λ± = [1 + β + κσ ± √((1 + β + κσ)² − 4β(1 + κσθ_iπ))]/(2β)`. -/
theorem appA1_lambda_pm {P : Params} (hβ : P.beta ≠ 0) (hθx : P.thIx = 0)
    (hd : 0 ≤ (1 + P.beta + P.kappa * P.sigma) ^ 2 -
      4 * P.beta * (1 + P.kappa * P.sigma * P.thIpi)) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    charB P ((1 + P.beta + P.kappa * P.sigma + sgn * Real.sqrt ((1 + P.beta + P.kappa * P.sigma)
      ^ 2 - 4 * P.beta * (1 + P.kappa * P.sigma * P.thIpi))) / (2 * P.beta)) = 0 := by
  set A := 1 + P.beta + P.kappa * P.sigma with hA
  set C := 1 + P.kappa * P.sigma * P.thIpi with hC
  set sq := Real.sqrt (A ^ 2 - 4 * P.beta * C) with hsq
  have hs : sq ^ 2 = A ^ 2 - 4 * P.beta * C := Real.sq_sqrt hd
  have hsg : sgn ^ 2 = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hT : trB P = A / P.beta := by rw [trB_eq, hθx, hA]; field_simp; ring
  have hD : detB P = C / P.beta := by rw [detB_eq hβ, hθx, hC]; ring
  rw [charB, hT, hD]
  linear_combination (norm := (field_simp; ring))
    (sgn ^ 2 * hs + (A ^ 2 - 4 * P.beta * C) * hsg) / (4 * P.beta ^ 2)

/-- Online Appendix A1 §1.9, p. 574 (E19): the printed `λ_+`, with `(1 + β + κσ²)` under the root,
is not a root in general — at `σ = 2, κ = 1, β = 1/2, θ_iπ = θ_ix = 0` it is
`3.5 + √3.5`, where the characteristic polynomial `z² − 7z + 2` equals `−6.75`. -/
theorem printed_lambda_pm_false :
    charB { zeroParams with sigma := 2, kappa := 1, beta := 1 / 2 }
      ((1 + 1 / 2 + 1 * 2 + Real.sqrt ((1 + 1 / 2 + 1 * 2 ^ 2) - 4 * (1 / 2) * (1 + 1 * 2 * 0)))
        / (2 * (1 / 2))) ≠ 0 := by
  have hs : Real.sqrt ((1 + 1 / 2 + 1 * 2 ^ 2) - 4 * (1 / 2) * (1 + 1 * 2 * 0)) ^ 2 =
      (7 / 2 : ℝ) := by
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [charB, trB, detB, aXX, aXP, aPX, aPP, zeroParams]
  intro h
  nlinarith [hs]

/-- Online Appendix A1 §1.9, pp. 574–575 ("We use `θ_iπ < 1`, as `ρ⁻¹` provides the extra
explosive eigenvalue"): with `0 ≤ θ_iπ < 1`, `θ_ix = 0`, `0 < ρ < 1` and `|η_i|, |η_s| < 1`, no
eigenvalue lies on the unit circle and exactly two (`λ_+` and `ρ⁻¹`) lie outside — as many as the
expectational errors `δ_x, δ_π`. -/
theorem appA1_19_passive {P : Params} (hP : Standard P) (hθx : P.thIx = 0)
    (hθ : P.thIpi < 1) (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) : NoUnit (appA19 P) ∧ unstableCount (appA19 P) = 2 := by
  have hpass : Passive P := by
    unfold Passive
    rw [hθx, mul_zero, add_zero]
    exact mul_neg_of_pos_of_neg hP.2.1 (by linarith)
  obtain ⟨hnu, hc⟩ := (stable_one_iff_passive hP).mpr hpass
  rw [noUnit_blockMat_iff] at hnu
  rw [stableCount_blockMat] at hc
  have hr : 1 < (1 / P.rho : ℝ) := by rw [lt_div_iff₀ hρ0]; linarith
  have hr' : ‖((1 / P.rho : ℝ) : ℂ)‖ = 1 / P.rho := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hi : ‖(P.etaI : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hs : ‖(P.etaS : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  rw [NoUnit, unstableCount, appA1_19_eigs]
  obtain ⟨h1, h2⟩ := hnu
  refine ⟨?_, ?_⟩
  · intro μ hμ
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with (((rfl | rfl) | rfl) | rfl) | rfl
    · exact h1
    · exact h2
    · rw [hr']; exact hr.ne'
    · exact hi.ne
    · exact hs.ne
  · simp only [Multiset.filter_add, Multiset.filter_singleton, Multiset.card_add]
    rw [hr']
    simp only [hr, not_lt.mpr hi.le, not_lt.mpr hs.le, ↓reduceIte]
    split_ifs at hc ⊢ with ha hb hb' hc' hd' <;> simp_all <;> grind

/-- Online Appendix A1 §1.9, p. 574 (with `θ_iπ > 1`, "both `λ` are larger than one"): under the
sign restrictions with `θ_ix = 0`, `θ_iπ > 1`, `0 < ρ < 1` and `|η_i|, |η_s| < 1`, three eigenvalues
(`λ_±` and `ρ⁻¹`) lie outside the unit circle — one more than the two expectational errors. -/
theorem appA1_19_active {P : Params} (hP : Standard P) (hθx : P.thIx = 0)
    (hθ : 1 < P.thIpi) (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) : NoUnit (appA19 P) ∧ unstableCount (appA19 P) = 3 := by
  have hact : 0 < P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx := by
    rw [hθx, mul_zero, add_zero]
    exact mul_pos hP.2.1 (by linarith)
  obtain ⟨hnu, hc⟩ := both_unstable hP hact
  rw [noUnit_blockMat_iff] at hnu
  rw [stableCount_blockMat] at hc
  obtain ⟨h1, h2⟩ := hnu
  have g1 : 1 < ‖root₁ (trB P) (detB P)‖ := by
    by_contra h
    push Not at h
    have := lt_of_le_of_ne h h1
    simp [this] at hc
  have g2 : 1 < ‖root₂ (trB P) (detB P)‖ := by
    by_contra h
    push Not at h
    have := lt_of_le_of_ne h h2
    simp [this] at hc
  have hr : 1 < (1 / P.rho : ℝ) := by rw [lt_div_iff₀ hρ0]; linarith
  have hr' : ‖((1 / P.rho : ℝ) : ℂ)‖ = 1 / P.rho := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hi : ‖(P.etaI : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hs : ‖(P.etaS : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  rw [NoUnit, unstableCount, appA1_19_eigs]
  refine ⟨?_, ?_⟩
  · intro μ hμ
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with (((rfl | rfl) | rfl) | rfl) | rfl
    · exact g1.ne'
    · exact g2.ne'
    · rw [hr']; exact hr.ne'
    · exact hi.ne
    · exact hs.ne
  · simp only [Multiset.filter_add, Multiset.filter_singleton, Multiset.card_add]
    rw [hr']
    have hr2 : 1 < P.rho⁻¹ := by rwa [one_div] at hr
    have hi2 : ¬ 1 < |P.etaI| := not_lt.mpr hηi.le
    have hs2 : ¬ 1 < |P.etaS| := not_lt.mpr hηs.le
    simp [g1, g2, hr2, hi2, hs2]

/-- Online Appendix A1 §1.9, pp. 574–576 (E20: "we need two eigenvalues greater or equal to
one"): at `θ_iπ = 1` (with `θ_ix = 0`) the transition matrix has the eigenvalue `1`, which is
neither stable nor forward-looking; by `block_not_determinate_of_boundary` the block is then not
determinate for every bounded forcing. With the model's own stationary AR(1) forcing the
unit-root model is determinate under perfect foresight (`unitroot_pf`) but not with recurring
news unless `β_s = 0, β_i = k` (`unitroot_iff_trunc`). -/
theorem appA1_19_unit {P : Params} (hβ : P.beta ≠ 0) (hθx : P.thIx = 0) (hθ : P.thIpi = 1) :
    (1 : ℂ) ∈ eigs (appA19 P) := by
  have h1 : charB P 1 = 0 := by rw [charB_one hβ, hθx, hθ]; ring
  have hz : (1 : ℂ) ^ 2 - (trB P : ℂ) * 1 + (detB P : ℂ) = 0 := by
    have : ((charB P 1 : ℝ) : ℂ) = 0 := by rw [h1]; simp
    rw [← this, charB]
    push_cast
    ring
  rw [appA1_19_eigs]
  rcases eq_root_of_eq hz with h | h
  · rw [← h]; simp
  · rw [← h]; simp

/-- Online Appendix A1 §1.11, p. 579: the transition matrix of the reduced §5.5 model in the
order `(x, π, q, u_i, u_s)`. -/
noncomputable def appA111 (P : Params) : Matrix (Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 2) ℝ :=
  mat5 (aXX P) (aXP P) (aPX P) (aPP P) (P.thIx / P.omega) (P.thIpi / P.omega) (1 / P.omega)
    P.etaI P.etaS !![P.sigma, 0; 0, 0; 1 / P.omega, 0]

/-- Online Appendix A1 §1.11, p. 579: the eigenvalues of the §5.5 matrix are `λ_±`, `ω⁻¹`,
`η_i`, `η_s`. -/
theorem appA1_111_eigs (P : Params) :
    eigs (appA111 P) = {root₁ (trB P) (detB P)} + {root₂ (trB P) (detB P)} +
      {((1 / P.omega : ℝ) : ℂ)} + {(P.etaI : ℂ)} + {(P.etaS : ℂ)} :=
  eigs_mat5 _ _ _ _ _ _ _ _ _ _

/-- Online Appendix A1 §1.11, p. 578 ("I solve unstable eigenvalues forward and stable eigenvalues
backward"): under the passive-money condition, `0 < ω < 1` and `|η_i|, |η_s| < 1`, the §5.5
matrix has no eigenvalue on the unit circle and exactly two (`λ_+` and `ω⁻¹`) outside it — as
many as its expectational errors `δ_x, δ_q`. -/
theorem appA1_111_count {P : Params} (hP : Standard P) (hpass : Passive P) (hω0 : 0 < P.omega)
    (hω1 : P.omega < 1) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1) :
    NoUnit (appA111 P) ∧ unstableCount (appA111 P) = 2 := by
  obtain ⟨hnu, hc⟩ := (stable_one_iff_passive hP).mpr hpass
  rw [noUnit_blockMat_iff] at hnu
  rw [stableCount_blockMat] at hc
  have hr : 1 < (1 / P.omega : ℝ) := by rw [lt_div_iff₀ hω0]; linarith
  have hr' : ‖((1 / P.omega : ℝ) : ℂ)‖ = 1 / P.omega := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hi : ‖(P.etaI : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hs : ‖(P.etaS : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  rw [NoUnit, unstableCount, appA1_111_eigs]
  obtain ⟨h1, h2⟩ := hnu
  refine ⟨?_, ?_⟩
  · intro μ hμ
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with (((rfl | rfl) | rfl) | rfl) | rfl
    · exact h1
    · exact h2
    · rw [hr']; exact hr.ne'
    · exact hi.ne
    · exact hs.ne
  · simp only [Multiset.filter_add, Multiset.filter_singleton, Multiset.card_add]
    rw [hr']
    simp only [hr, not_lt.mpr hi.le, not_lt.mpr hs.le, ↓reduceIte]
    split_ifs at hc ⊢ with ha hb hb' hc' hd' <;> simp_all <;> grind

/-- Online Appendix A1 §1.11, pp. 578–579: the rows of the §5.5 matrix follow from the reduced
model — `E_t x_{t+1} = (1 + σκ/β + σθ_ix) x_t + (σθ_iπ − σ/β) π_t + σ u_{i,t}`,
`π_{t+1} = −(κ/β) x_t + π_t/β − (β_s ε_{s,t+1} + β_i ε_{i,t+1})` and
`E_t q_{t+1} = (θ_ix/ω) x_t + (θ_iπ/ω) π_t + q_t/ω + u_{i,t}/ω`. -/
theorem appA1_111_rows {P : Params} (hβ : P.beta ≠ 0) (hω : P.omega ≠ 0)
    {ei es ui us x p q v : ℕ → Ω → ℝ} (h : RedSys 𝔼 P ei es ui us x p q v)
    (hap : 𝔼.Adapted p) (haq : 𝔼.Adapted q) (t : ℕ) :
    𝔼.E t (x (t + 1)) = aXX P • x t + aXP P • p t + P.sigma • ui t ∧
    p (t + 1) = aPX P • x t + aPP P • p t - (P.betaS • es (t + 1) + P.betaI • ei (t + 1)) ∧
    𝔼.E t (q (t + 1)) = (P.thIx / P.omega) • x t + (P.thIpi / P.omega) • p t +
      (1 / P.omega) • q t + (1 / P.omega) • ui t := by
  obtain ⟨h64, h65, h68, -, h72⟩ := h
  have e64 := h64 t
  have e65 := h65 t
  have e68 := h68 t
  have e72 := h72 t
  rw [innov_succ 𝔼 hap] at e68
  rw [rnNext, map_sub, map_smul, haq t] at e72
  refine ⟨?_, ?_, ?_⟩ <;> funext ω
  · have a := congrFun e64 ω
    have b := congrFun e65 ω
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, aXX, aXP] at a b ⊢
    linear_combination (norm := (field_simp; ring)) (-1 : ℝ) * a + (P.sigma / P.beta) * b
  · have b := congrFun e65 ω
    have c := congrFun e68 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, aPX,
      aPP] at b c ⊢
    linear_combination (norm := (field_simp; ring)) c - (1 / P.beta) * b
  · have d := congrFun e72 ω
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at d ⊢
    linear_combination (norm := (field_simp; ring)) (1 / P.omega) * d

/-! ### Online Appendix A1 §1.9.1: the minimum-state-variable example, corrected (E21) -/

/-- Online Appendix A1 §1.9.1, pp. 576–577 (E21, corrected): in the model (1.47)–(1.50)
(`i_t = E_tπ_{t+1}`, `ρ v_{t+1} = v_t + i_t − π_{t+1} − s_{t+1}`, `i = u_i`, `s = u_s` AR(1)), every
bounded adapted value of debt is `v_t = η_s/(1 − ρη_s) u_{s,t}` and inflation is
`π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)` — the printed `+` is a sign error. Determinacy follows
from boundedness alone (`0 < ρ < 1`), not from the assumption that `v_t` is a time-invariant
function of the states. -/
theorem msv_unique {ρ ηs : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρη : 1 - ρ * ηs ≠ 0)
    {es ui us p v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (hus : 𝔼.Adapted us)
    (hes : ∀ t, 𝔼.E t (es (t + 1)) = 0)
    (hul : ∀ t, us (t + 1) = ηs • us t + es (t + 1)) (hbu : BoundedProc us)
    (h147 : ∀ t, ui t = 𝔼.E t (p (t + 1)))
    (h148 : ∀ t, ρ • v (t + 1) = v t + ui t - p (t + 1) - us (t + 1))
    (hav : 𝔼.Adapted v) (hbv : BoundedProc v) :
    (∀ t, v t = (ηs / (1 - ρ * ηs)) • us t) ∧
      ∀ t, p (t + 1) = ui t - (1 - ρ * ηs)⁻¹ • es (t + 1) := by
  have hρη' : 1 - ηs * ρ ≠ 0 := by rwa [mul_comm]
  set c := ηs / (1 - ρ * ηs) with hc
  have hEu := E_ar1 𝔼 hus hes hul
  set d : ℕ → Ω → ℝ := v - c • us with hd
  have hdeq : ∀ t, d t = ρ • 𝔼.E t (d (t + 1)) + 0 := by
    intro t
    have e := congrArg (𝔼.E t) (h148 t)
    rw [map_smul, map_sub, map_sub, map_add, hav t, hui t, ← h147 t, hEu t] at e
    funext ω
    have eω := congrFun e ω
    simp only [hd, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_sub, map_smul,
      hEu t, Pi.zero_apply, add_zero] at eω ⊢
    rw [hc]
    linear_combination (norm := (field_simp; ring)) (-1 : ℝ) * eω
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = ρ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hbd : BoundedProc d := bdd_sub hbv (bdd_smul c hbu)
  have hd0 := 𝔼.forward_unique hρa hdeq hz hbd ⟨0, fun _ _ => by simp⟩
  have hv : ∀ t, v t = c • us t := by
    intro t
    funext ω
    have := congrFun (congrFun hd0 t) ω
    simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith
  refine ⟨hv, fun t => ?_⟩
  funext ω
  have e := congrFun (h148 t) ω
  have a1 := congrFun (hv t) ω
  have a2 := congrFun (hv (t + 1)) ω
  have a3 := congrFun (hul t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e a1 a2 a3 ⊢
  rw [a1, a2, a3, hc] at e
  linear_combination (norm := (field_simp; ring)) e

/-- Online Appendix A1 §1.9.1, p. 576 ("We know the answer already"): the corrected solution
`v_t = η_s/(1 − ρη_s) u_{s,t}`, `π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)` does solve
(1.47)–(1.50), with `v` bounded and adapted. -/
theorem msv_exists {ρ ηs : ℝ} (hρη : 1 - ρ * ηs ≠ 0) {es ui us : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (hus : 𝔼.Adapted us) (hes : ∀ t, 𝔼.E t (es (t + 1)) = 0)
    (hul : ∀ t, us (t + 1) = ηs • us t + es (t + 1)) (hbu : BoundedProc us) :
    ∃ p v : ℕ → Ω → ℝ, (∀ t, ui t = 𝔼.E t (p (t + 1))) ∧
      (∀ t, ρ • v (t + 1) = v t + ui t - p (t + 1) - us (t + 1)) ∧
      𝔼.Adapted v ∧ BoundedProc v := by
  refine ⟨fun t => Nat.casesOn t 0 (fun t => ui t - (1 - ρ * ηs)⁻¹ • es (t + 1)),
    fun t => (ηs / (1 - ρ * ηs)) • us t, fun t => ?_, fun t => ?_,
    adapted_smul 𝔼 _ hus, bdd_smul _ hbu⟩
  · change ui t = 𝔼.E t (ui t - (1 - ρ * ηs)⁻¹ • es (t + 1))
    rw [map_sub, map_smul, hes t, hui t, smul_zero, sub_zero]
  · change ρ • ((ηs / (1 - ρ * ηs)) • us (t + 1)) = (ηs / (1 - ρ * ηs)) • us t + ui t -
      (ui t - (1 - ρ * ηs)⁻¹ • es (t + 1)) - us (t + 1)
    funext ω
    have a3 := congrFun (hul t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a3 ⊢
    rw [a3]
    field_simp
    ring

/-- Online Appendix A1 §1.9.1, p. 577 (E21): the book's own coefficient equation
`(1, −1) B = (0, −ρ) A + (0, −1)` with `A_vs = η_s/(1 − ρη_s)` gives
`B_πs = −ρ A_vs − 1 = −1/(1 − ρη_s)`, not the printed `+1/(1 − ρη_s)`. -/
theorem msv_B_coefficient {ρ ηs : ℝ} (h : 1 - ρ * ηs ≠ 0) :
    -ρ * (ηs / (1 - ρ * ηs)) - 1 = -(1 - ρ * ηs)⁻¹ ∧
      -ρ * (ηs / (1 - ρ * ηs)) - 1 ≠ (1 - ρ * ηs)⁻¹ := by
  have e : -ρ * (ηs / (1 - ρ * ηs)) - 1 = -(1 - ρ * ηs)⁻¹ := by
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e]
  intro h'
  have : (1 - ρ * ηs)⁻¹ = 0 := by linarith
  exact inv_ne_zero h this

/-- Online Appendix A1 §1.9.1, p. 576 (E21): the printed solution
`π_{t+1} = u_{i,t} + ε_{s,t+1}/(1 − ρη_s)` is wrong at every outcome with a nonzero fiscal shock. -/
theorem printed_msv_false {ρ ηs : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρη : 1 - ρ * ηs ≠ 0)
    {es ui us p v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (hus : 𝔼.Adapted us)
    (hes : ∀ t, 𝔼.E t (es (t + 1)) = 0)
    (hul : ∀ t, us (t + 1) = ηs • us t + es (t + 1)) (hbu : BoundedProc us)
    (h147 : ∀ t, ui t = 𝔼.E t (p (t + 1)))
    (h148 : ∀ t, ρ • v (t + 1) = v t + ui t - p (t + 1) - us (t + 1))
    (hav : 𝔼.Adapted v) (hbv : BoundedProc v) (t : ℕ) (ω : Ω) (hε : es (t + 1) ω ≠ 0) :
    p (t + 1) ω ≠ ui t ω + (1 - ρ * ηs)⁻¹ * es (t + 1) ω := by
  obtain ⟨-, hp⟩ := msv_unique 𝔼 hρ0 hρ1 hρη hui hus hes hul hbu h147 h148 hav hbv
  have e := congrFun (hp t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
  rw [e]
  intro h
  have h2 : (1 - ρ * ηs)⁻¹ * es (t + 1) ω = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact inv_ne_zero hρη h3
  · exact hε h3

/-- Cochrane (2023), §5.5, p. 148 ("The pair (5.51)–(5.52) has two expectational errors … but only
one forward-looking root"): under the passive-money condition the `(x, π)` block has exactly one
eigenvalue outside the unit circle; the fiscal combination (5.63) supplies the root
`ρ⁻¹ > 1` (`full_elim`). -/
theorem block_unstableCount_one {P : Params} (hP : Standard P) (hpass : Passive P) :
    unstableCount (blockMat P) = 1 := by
  obtain ⟨hnu, hc⟩ := (stable_one_iff_passive hP).mpr hpass
  have := stableCount_add_unstableCount hnu
  rw [hc] at this
  simp at this
  omega

/-- Cochrane (2023), §5.5.2, p. 152 ("The cumulative fiscal disturbance is
`ΔE_1 ∑ ρʲ u_{s,1+j} = 1/(1 − ρη_s) = −1.98%`", E38): for a unit shock the cumulative
disturbance is `1/(1 − 0.99 · 0.5) ≈ 1.980`; the book's `−1.98%` is the response to the deficit
shock `ε_{s,1} = −1`. -/
theorem cumulative_disturbance_value :
    1.98 < 1 / (1 - 0.99 * 0.5 : ℝ) ∧ 1 / (1 - 0.99 * 0.5 : ℝ) < 1.981 := by
  constructor <;> norm_num

/-! ### Boundary cases: `|1 − α| = ρ` and the unit root `p(1) = 0` -/

/-- Cochrane (2023), §5.5.2, p. 152 (tool): the output gain `g(λ) = (1 − βλ)/κ` for a stable
root `λ`. -/
noncomputable def gainOf (P : Params) (l : ℝ) : ℝ := (1 - P.beta * l) / P.kappa

/-- Cochrane (2023), §5.5 and A1 §1.9 (the closed form for any real factorisation
`z² − tr z + det = (z − λ_U)(z − λ_S)` with `λ_U > 1`, including the unit-root case `λ_S = 1`): in
every bounded solution of (5.64)–(5.65), `x_t = g(λ_S) π_t − σ/(λ_U − η_i) u_{i,t}` and
`E_t π_{t+1} = λ_S π_t + κσ/(β(λ_U − η_i)) u_{i,t}`, with `g(λ) = (1 − βλ)/κ`. -/
theorem closed_form_gen {P : Params} (hP : Standard P) {lU lS : ℝ} (hU : 1 < lU)
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) (hηi : |P.etaI| < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) {x p : ℕ → Ω → ℝ}
    (h64 : ∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1))))
    (h65 : ∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t)
    (hbx : BoundedProc x) (hbp : BoundedProc p) :
    (∀ t, x t = gainOf P lS • p t - (P.sigma / (lU - P.etaI)) • ui t) ∧
    ∀ t, 𝔼.E t (p (t + 1)) =
      lS • p t + (P.kappa * P.sigma / (P.beta * (lU - P.etaI))) • ui t := by
  obtain ⟨-, -, hua, -, -, -, hub, -, hei, -, hul, -⟩ := hsh
  have hβ := hP.2.2.1.ne'
  have hκ := hP.2.1.ne'
  have hηU : lU - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2
    linarith
  have hU0 : lU ≠ 0 := by linarith
  have hch : charB P lS = 0 := by rw [charB, ← hsum, ← hprod]; ring
  have hU' : lU = trB P - lS := by linarith
  have hEu := E_ar1 𝔼 hua hei hul
  set c : ℝ := P.sigma / (lU - P.etaI) with hc
  have kx : 1 + P.sigma * P.thIx + P.sigma * P.kappa / P.beta + gainOf P lS * P.kappa / P.beta =
      lU := by
    rw [hU', trB_eq, gainOf]
    field_simp
    ring
  have key : P.sigma * P.thIpi - P.sigma / P.beta - gainOf P lS / P.beta + lU * gainOf P lS =
      P.beta / P.kappa * charB P (lS) := by
    rw [hU', charB, trB_eq, detB_eq hβ, gainOf]
    field_simp
    ring
  have kp : P.sigma * P.thIpi - P.sigma / P.beta - gainOf P lS / P.beta = -(lU * gainOf P lS) := by
    rw [hch, mul_zero] at key
    linarith
  have ku : P.sigma + c * P.etaI = lU * c := by
    rw [hc]
    field_simp
    ring
  set f : ℕ → Ω → ℝ := x - gainOf P lS • p + c • ui with hf
  have hEf : ∀ t, 𝔼.E t (f (t + 1)) = lU • f t := by
    intro t
    funext ω
    have e64 := congrFun (h64 t) ω
    have e65 := congrFun (h65 t) ω
    have eu := congrFun (hEu t) ω
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e64 e65 eu
    have hEp : 𝔼.E t (p (t + 1)) ω = (p t ω - P.kappa * x t ω) / P.beta := by
      field_simp
      linarith
    have hEx : 𝔼.E t (x (t + 1)) ω = x t ω +
        P.sigma * (P.thIpi * p t ω + P.thIx * x t ω + ui t ω) - P.sigma * 𝔼.E t (p (t + 1)) ω := by
      linarith
    simp only [hf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub,
      map_smul]
    rw [eu, hEx, hEp]
    linear_combination x t ω * kx + p t ω * kp + ui t ω * ku
  have hfs : ∀ t, f t = (lU)⁻¹ • 𝔼.E t (f (t + 1)) + 0 := by
    intro t
    rw [hEf t, smul_smul, inv_mul_cancel₀ hU0, one_smul, add_zero]
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = (lU)⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have hinv : |(lU)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lU)]
    exact inv_lt_one_of_one_lt₀ hU
  have hbf : BoundedProc f := bdd_add (bdd_sub hbx (bdd_smul _ hbp)) (bdd_smul _ hub)
  have hf0 := 𝔼.forward_unique hinv hfs hz hbf ⟨0, fun _ _ => by simp⟩
  have hx : ∀ t, x t = gainOf P lS • p t - c • ui t := by
    intro t
    funext ω
    have := congrFun (congrFun hf0 t) ω
    simp only [hf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this ⊢
    linarith
  refine ⟨hx, fun t => ?_⟩
  funext ω
  have e65 := congrFun (h65 t) ω
  have exx := congrFun (hx t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e65 exx ⊢
  have hEp : 𝔼.E t (p (t + 1)) ω = (p t ω - P.kappa * x t ω) / P.beta := by
    field_simp
    linarith
  rw [hEp, exx, hc, gainOf]
  field_simp
  ring


/-- Cochrane (2023), §5.5 (converse of `closed_form_gen`): if `x_t = g(λ_S) π_t − d u_{i,t}` and
`E_t π_{t+1} = λ_S π_t + c u_{i,t}` with `d = σ/(λ_U − η_i)`, `c = κσ/(β(λ_U − η_i))`, where
`λ_U + λ_S = tr` and `λ_U λ_S = det`, then the IS curve (5.64) and Phillips curve (5.65) hold. -/
theorem closed_form_converse {P : Params} (hβ : P.beta ≠ 0) (hκ : P.kappa ≠ 0) {lU lS : ℝ}
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) (hηU : lU - P.etaI ≠ 0)
    {ui x p : ℕ → Ω → ℝ} (hEu : ∀ t, 𝔼.E t (ui (t + 1)) = P.etaI • ui t)
    (hx : ∀ t, x t = gainOf P lS • p t - (P.sigma / (lU - P.etaI)) • ui t)
    (hEp : ∀ t, 𝔼.E t (p (t + 1)) =
      lS • p t + (P.kappa * P.sigma / (P.beta * (lU - P.etaI))) • ui t) :
    (∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1)))) ∧
      ∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t := by
  have hch : charB P lS = 0 := by rw [charB, ← hsum, ← hprod]; ring
  have hU' : lU = trB P - lS := by linarith
  set G := gainOf P lS with hG
  set d := P.sigma / (lU - P.etaI) with hd
  set c := P.kappa * P.sigma / (P.beta * (lU - P.etaI)) with hc
  have kA : G * lS - G - P.sigma * P.thIpi - P.sigma * P.thIx * G + P.sigma * lS = 0 := by
    have key : G * lS - G - P.sigma * P.thIpi - P.sigma * P.thIx * G + P.sigma * lS =
        -(P.beta / P.kappa) * charB P lS := by
      rw [hG, charB, trB_eq, detB_eq hβ, gainOf]
      field_simp
      ring
    rw [key, hch, mul_zero]
  have hdU : d * (lU - P.etaI) = P.sigma := by rw [hd]; field_simp
  have hc' : c = P.kappa * d / P.beta := by rw [hc, hd]; field_simp
  have hT := trB_eq P
  have kB : G * c - d * P.etaI + d + P.sigma * P.thIx * d - P.sigma + P.sigma * c = 0 := by
    rw [hc', hG, gainOf]
    linear_combination (norm := (field_simp; ring)) hdU - d * hsum - d * hT
  have hxE : ∀ t, 𝔼.E t (x (t + 1)) = G • 𝔼.E t (p (t + 1)) - d • (P.etaI • ui t) := by
    intro t
    rw [hx (t + 1), map_sub, map_smul, map_smul, hEu t]
  constructor
  · intro t
    funext ω
    have e1 := congrFun (hxE t) ω
    have e2 := congrFun (hEp t) ω
    have e3 := congrFun (hx t) ω
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
    rw [e1, e2, e3]
    linear_combination (-(p t ω)) * kA - ui t ω * kB
  · intro t
    funext ω
    have e2 := congrFun (hEp t) ω
    have e3 := congrFun (hx t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e3 ⊢
    rw [e2, e3, hG, hc, hd, gainOf]
    have : lU - P.etaI ≠ 0 := hηU
    field_simp
    ring

/-- Cochrane (2023), (5.72)–(5.73): the bond-price coefficient on inflation,
`a = −(θ_iπ + θ_ix g)/(1 − ωλ_S)`. -/
noncomputable def qa (P : Params) (G lS : ℝ) : ℝ :=
  -(P.thIpi + P.thIx * G) / (1 - P.omega * lS)

/-- Cochrane (2023), (5.72)–(5.73): the bond-price coefficient on the monetary disturbance,
`b = (ω a c − (1 − θ_ix d))/(1 − ωη_i)`. -/
noncomputable def qb (P : Params) (G d c lS : ℝ) : ℝ :=
  (P.omega * qa P G lS * c - (1 - P.thIx * d)) / (1 - P.omega * P.etaI)

/-- Cochrane (2023), (5.72)–(5.73), p. 149: if output and expected inflation are linear in
`(π, u_i)` (`x = Gπ − d u_i`, `E_tπ_{t+1} = λ_S π_t + c u_{i,t}`), the bounded bond price is
`q_t = a π_t + b u_{i,t}`. -/
theorem q_closed {P : Params} {G d c lS : ℝ} (hω : |P.omega| < 1)
    (h1 : 1 - P.omega * lS ≠ 0) (h2 : 1 - P.omega * P.etaI ≠ 0) {ui x p q : ℕ → Ω → ℝ}
    (hEu : ∀ t, 𝔼.E t (ui (t + 1)) = P.etaI • ui t) (hx : ∀ t, x t = G • p t - d • ui t)
    (hEp : ∀ t, 𝔼.E t (p (t + 1)) = lS • p t + c • ui t) (haq : 𝔼.Adapted q)
    (h72 : ∀ t, 𝔼.E t (rnNext P q t) = iRule P x p ui t) (hbq : BoundedProc q)
    (hbp : BoundedProc p) (hbu : BoundedProc ui) :
    ∀ t, q t = qa P G lS • p t + qb P G d c lS • ui t := by
  have hs := (eq572_iff 𝔼 haq).mp h72
  have hqa : qa P G lS * (1 - P.omega * lS) = -(P.thIpi + P.thIx * G) := by
    rw [qa]; field_simp
  have hqb : qb P G d c lS * (1 - P.omega * P.etaI) =
      P.omega * qa P G lS * c - (1 - P.thIx * d) := by
    rw [qb]; field_simp
  set qt : ℕ → Ω → ℝ := qa P G lS • p + qb P G d c lS • ui with hqt
  have hs2 : ∀ t, qt t = P.omega • 𝔼.E t (qt (t + 1)) + (fun t => -iRule P x p ui t) t := by
    intro t
    funext ω
    have e1 := congrFun (hEp t) ω
    have e2 := congrFun (hEu t) ω
    have e3 := congrFun (hx t) ω
    simp only [hqt, iRule, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply,
      smul_eq_mul, map_add, map_smul] at e1 e2 e3 ⊢
    rw [e1, e2, e3]
    linear_combination p t ω * hqa + ui t ω * hqb
  have := 𝔼.forward_unique hω hs hs2 hbq (bdd_add (bdd_smul _ hbp) (bdd_smul _ hbu))
  intro t
  rw [this, hqt]
  rfl

/-- Cochrane (2023), pp. 148–149 (existence of the `(x, π, q)` part): under the sign
restrictions, the passive-money condition and `|ω| < 1`, for every initial inflation there are
bounded adapted `x, π, q` satisfying (5.64), (5.65), (5.68) and (5.72). -/
theorem exists_block_q {P : Params} (hP : Standard P) (hpass : Passive P) (hω : |P.omega| < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) (p0 : ℝ) :
    ∃ x p q : ℕ → Ω → ℝ,
      (∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1)))) ∧
      (∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t) ∧
      (∀ t, innov 𝔼 t (p (t + 1)) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)) ∧
      (∀ t, 𝔼.E t (rnNext P q t) = iRule P x p ui t) ∧
      𝔼.Adapted x ∧ 𝔼.Adapted p ∧ 𝔼.Adapted q ∧ BoundedProc x ∧ BoundedProc p ∧
      BoundedProc q ∧ p 0 = (fun _ => p0) := by
  have hβ := hP.2.2.1.ne'
  have hsh' := hsh
  obtain ⟨-, -, hua, -, -, -, hub, -, -, -, -, -⟩ := hsh'
  have hxa := xi_adapted 𝔼 hsh
  have hxb := xi_bounded 𝔼 hsh
  have hwb : BoundedV (blockForcing P ei es ui) := by
    obtain ⟨A, hA⟩ := bdd_add (bdd_smul (aXP P) hxb) (bdd_smul P.sigma hub)
    obtain ⟨B, hB⟩ := bdd_smul (aPP P) hxb
    refine ⟨max A B, fun t k ω => ?_⟩
    rcases k with k | k
    · exact (hA t ω).trans (le_max_left _ _)
    · exact (hB t ω).trans (le_max_right _ _)
  have hwa : AdaptedV 𝔼 (blockForcing P ei es ui) := by
    intro t k
    rcases k with k | k
    · exact adapted_add 𝔼 (adapted_smul 𝔼 _ hxa) (adapted_smul 𝔼 _ hua) t
    · exact adapted_smul 𝔼 _ hxa t
  obtain ⟨yb, hyb, -⟩ := block_determinate 𝔼 hP hpass _ hwb hwa (fun _ => p0)
  set x : ℕ → Ω → ℝ := fun t => yb t (Sum.inl 0) with hx
  set p : ℕ → Ω → ℝ := fun t => yb t (Sum.inr 0) + xi P ei es t with hp
  have hys : blockState P ei es x p = yb := by
    funext t k
    rcases k with k | k <;> simp [blockState, hx, hp, Fin.fin_one_eq_zero k]
  rw [← hys] at hyb
  obtain ⟨h64, h65, h68, hax, hap, hbx, hbp, hp0⟩ := (block_iff 𝔼 hβ hsh x p p0).mpr hyb
  have hib : BoundedProc (fun t => -iRule P x p ui t) := by
    obtain ⟨M, hM⟩ := bdd_add (bdd_add (bdd_smul P.thIpi hbp) (bdd_smul P.thIx hbx)) hub
    refine ⟨M, fun t ω => ?_⟩
    rw [show (fun t => -iRule P x p ui t) t ω = -(iRule P x p ui t ω) from rfl, abs_neg]
    exact hM t ω
  have hia : 𝔼.Adapted (fun t => -iRule P x p ui t) := by
    intro t
    simp only [iRule, map_neg, map_add, map_smul, hap t, hax t, hua t]
  obtain ⟨q, ⟨hbq, hqs⟩, -⟩ := ForwardSolution.existsUnique_bounded 𝔼 hω hib hia
  have haq := ForwardSolution.solves_adapted 𝔼 hia hqs
  exact ⟨x, p, q, h64, h65, h68, (eq572_iff 𝔼 haq).mpr hqs, hax, hap, haq, hbx, hbp, hbq, hp0⟩

/-- Cochrane (2023), pp. 148–149 (uniqueness for every `α`): under the sign restrictions, the
passive-money condition, `|ω| < 1` and `ρ ≠ 0`, the reduced model has **at most one** bounded
equilibrium, whatever the debt response `α` — the debt recursion is solved backward from `v_0`. -/
theorem policyRules_unique {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ : P.rho ≠ 0) {ei es ui us : ℕ → Ω → ℝ}
    (hsh : Shocks 𝔼 P ei es ui us) {p0 v0 : ℝ} {x p q v x' p' q' v' : ℕ → Ω → ℝ}
    (h : RedEquil 𝔼 P ei es ui us p0 v0 x p q v)
    (h' : RedEquil 𝔼 P ei es ui us p0 v0 x' p' q' v') :
    x = x' ∧ p = p' ∧ q = q' ∧ v = v' := by
  have hβ := hP.2.2.1.ne'
  have hsh' := hsh
  obtain ⟨-, -, hua, -, -, -, hub, -, -, -, -, -⟩ := hsh'
  have hxa := xi_adapted 𝔼 hsh
  have hxb := xi_bounded 𝔼 hsh
  have hwb : BoundedV (blockForcing P ei es ui) := by
    obtain ⟨A, hA⟩ := bdd_add (bdd_smul (aXP P) hxb) (bdd_smul P.sigma hub)
    obtain ⟨B, hB⟩ := bdd_smul (aPP P) hxb
    refine ⟨max A B, fun t k ω => ?_⟩
    rcases k with k | k
    · exact (hA t ω).trans (le_max_left _ _)
    · exact (hB t ω).trans (le_max_right _ _)
  have hwa : AdaptedV 𝔼 (blockForcing P ei es ui) := by
    intro t k
    rcases k with k | k
    · exact adapted_add 𝔼 (adapted_smul 𝔼 _ hxa) (adapted_smul 𝔼 _ hua) t
    · exact adapted_smul 𝔼 _ hxa t
  obtain ⟨yb, -, hyu⟩ := block_determinate 𝔼 hP hpass _ hwb hwa (fun _ => p0)
  obtain ⟨⟨h64, h65, h68, h71, h72⟩, hax, hap, haq, hav, hbx, hbp, hbq, hbv, hp0, hv0⟩ := h
  obtain ⟨⟨h64', h65', h68', h71', h72'⟩, hax', hap', haq', hav', hbx', hbp', hbq', hbv', hp0',
    hv0'⟩ := h'
  have e1 := hyu _ ((block_iff 𝔼 hβ hsh x p p0).mp ⟨h64, h65, h68, hax, hap, hbx, hbp, hp0⟩)
  have e2 := hyu _ ((block_iff 𝔼 hβ hsh x' p' p0).mp
    ⟨h64', h65', h68', hax', hap', hbx', hbp', hp0'⟩)
  have e := e1.trans e2.symm
  have hxx : x = x' := by
    funext t
    have := congrFun (congrFun e t) (Sum.inl 0)
    simpa [blockState] using this
  have hpp : p = p' := by
    funext t
    have := congrFun (congrFun e t) (Sum.inr 0)
    simp only [blockState, Sum.elim_inr] at this
    exact sub_left_injective this
  subst hxx hpp
  have hqq : q = q' := 𝔼.forward_unique hω ((eq572_iff 𝔼 haq).mp h72)
    ((eq572_iff 𝔼 haq').mp h72') hbq hbq'
  subst hqq
  have hvv : v = v' := (eq_backRec hv0 ((eq571_iff hρ).mp h71)).trans
    (eq_backRec hv0' ((eq571_iff hρ).mp h71')).symm
  exact ⟨rfl, rfl, rfl, hvv⟩

/-- Cochrane (2023), (5.71), p. 149 (the boundary case `|1 − α| = ρ`): the coefficients of the
closed-form equilibrium used to split the value of debt into a part driven by the state and a
part driven only by the shocks. -/
structure DCoef where
  /-- the output gain `g` (`x = gπ − d u_i`). -/
  G : ℝ
  /-- the output loading `d` on the monetary disturbance. -/
  d : ℝ
  /-- the expected-inflation loading `c` (`E_tπ_{t+1} = λ_S π_t + c u_{i,t}`). -/
  c : ℝ
  /-- the root `λ_S` governing expected inflation. -/
  lS : ℝ
  /-- the debt root `φ = (1 − α)/ρ`. -/
  phi : ℝ

/-- Cochrane (2023), (5.71): the coefficient of `π_{t+1}` in `g_t` (`v_{t+1} = φ v_t + g_t`). -/
noncomputable def cP1 (P : Params) (C : DCoef) : ℝ :=
  (P.omega * qa P C.G C.lS - 1 - P.thSpi - P.thSx * C.G) / P.rho

/-- Cochrane (2023), (5.71): the coefficient of `u_{i,t+1}` in `g_t`. -/
noncomputable def cU1 (P : Params) (C : DCoef) : ℝ :=
  (P.omega * qb P C.G C.d C.c C.lS + P.thSx * C.d) / P.rho

/-- Cochrane (2023), (5.71): the coefficient of `π_t` in `g_t`. -/
noncomputable def cP0 (P : Params) (C : DCoef) : ℝ := -qa P C.G C.lS / P.rho

/-- Cochrane (2023), (5.71): the coefficient of `u_{i,t}` in `g_t`. -/
noncomputable def cU0 (P : Params) (C : DCoef) : ℝ := -qb P C.G C.d C.c C.lS / P.rho

/-- Cochrane (2023), (5.71): the coefficient of `u_{s,t+1}` in `g_t`. -/
noncomputable def cS1 (P : Params) : ℝ := -1 / P.rho

/-- Cochrane (2023), (5.71): the loading of the state part of debt on inflation. -/
noncomputable def cKp (P : Params) (C : DCoef) : ℝ :=
  (cP1 P C * C.lS + cP0 P C) / (C.lS - C.phi)

/-- Cochrane (2023), (5.71): the loading of the state part of debt on `u_s`. -/
noncomputable def cKs (P : Params) (C : DCoef) : ℝ := cS1 P * P.etaS / (P.etaS - C.phi)

/-- Cochrane (2023), (5.71): the loading of the state part of debt on `u_i`. -/
noncomputable def cKu (P : Params) (C : DCoef) : ℝ :=
  ((cP1 P C - cKp P C) * C.c + cU1 P C * P.etaI + cU0 P C) / (P.etaI - C.phi)

/-- Cochrane (2023), (5.71) (boundary case): the loading `κ_s` of the shock part of debt on the
fiscal shock `ε_s`. -/
noncomputable def kapS (P : Params) (C : DCoef) : ℝ :=
  (cS1 P - cKs P C) - P.betaS * (cP1 P C - cKp P C)

/-- Cochrane (2023), (5.71) (boundary case): the loading `κ_i` of the shock part of debt on the
monetary shock `ε_i`. -/
noncomputable def kapI (P : Params) (C : DCoef) : ℝ :=
  (cU1 P C - cKu P C) - P.betaI * (cP1 P C - cKp P C)

/-- Cochrane (2023), (5.71): the state part of the value of debt,
`h_t = K_π π_t + K_i u_{i,t} + K_s u_{s,t}`. -/
noncomputable def hProc (P : Params) (C : DCoef) (p ui us : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  cKp P C • p t + cKu P C • ui t + cKs P C • us t

/-- Cochrane (2023), (5.71), p. 149 (the decomposition of the debt recursion): in the closed-form
equilibrium the forcing `g_t` of `v_{t+1} = φ v_t + g_t` is
`g_t = h_{t+1} − φ h_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}`, so `v − h` is driven by the shocks
alone. -/
theorem gV_decomp {P : Params} {C : DCoef} (hρ : P.rho ≠ 0) (h1 : C.lS ≠ C.phi)
    (h2 : P.etaI ≠ C.phi) (h3 : P.etaS ≠ C.phi) {ei es ui us x p q : ℕ → Ω → ℝ}
    (hx : ∀ t, x t = C.G • p t - C.d • ui t)
    (hq : ∀ t, q t = qa P C.G C.lS • p t + qb P C.G C.d C.c C.lS • ui t)
    (hp1 : ∀ t, p (t + 1) = C.lS • p t + C.c • ui t + xi P ei es (t + 1))
    (hu1 : ∀ t, ui (t + 1) = P.etaI • ui t + ei (t + 1))
    (hs1 : ∀ t, us (t + 1) = P.etaS • us t + es (t + 1)) (t : ℕ) :
    gV P x p q us t = hProc P C p ui us (t + 1) - C.phi • hProc P C p ui us t +
      kapS P C • es (t + 1) + kapI P C • ei (t + 1) := by
  have hK1 : cKp P C * (C.lS - C.phi) = cP1 P C * C.lS + cP0 P C := by
    rw [cKp]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h1)
  have hK2 : cKu P C * (P.etaI - C.phi) =
      (cP1 P C - cKp P C) * C.c + cU1 P C * P.etaI + cU0 P C := by
    rw [cKu]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h2)
  have hK3 : cKs P C * (P.etaS - C.phi) = cS1 P * P.etaS := by
    rw [cKs]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h3)
  funext ω
  have hg : gV P x p q us t ω = cP1 P C * p (t + 1) ω + cU1 P C * ui (t + 1) ω +
      cP0 P C * p t ω + cU0 P C * ui t ω + cS1 P * us (t + 1) ω := by
    rw [gV, rnNext, hq t, hq (t + 1), hx (t + 1)]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cP1, cU1, cP0, cU0, cS1]
    field_simp
    ring
  have e1 := congrFun (hp1 t) ω
  have e2 := congrFun (hu1 t) ω
  have e3 := congrFun (hs1 t) ω
  simp only [xi_succ, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul] at e1 e2 e3
  rw [hg]
  simp only [hProc, kapS, kapI, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, e3]
  linear_combination (-(p t ω)) * hK1 - ui t ω * hK2 - us t ω * hK3

/-- Cochrane (2023), (5.71) (tool): a process with a known date-0 value and
`W_{t+1} = φ W_t + g_t`, `g_t` known at `t + 1`, is adapted. -/
theorem adapted_of_rec {W g : ℕ → Ω → ℝ} {φ : ℝ} (h0 : 𝔼.E 0 (W 0) = W 0)
    (hg : ∀ t, 𝔼.E (t + 1) (g t) = g t) (h : ∀ t, W (t + 1) = φ • W t + g t) :
    𝔼.Adapted W := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [h t, map_add, map_smul, hg t]
    congr 2
    have := 𝔼.known (Nat.le_succ t) (W t)
    rwa [ih] at this

/-- Cochrane (2023), §5.5: the closed-form coefficients under the passive-money condition, with
debt root `φ`. -/
noncomputable def passiveCoef (P : Params) (φ : ℝ) : DCoef :=
  ⟨gain P, P.sigma / (lamU P - P.etaI), P.kappa * P.sigma / (P.beta * (lamU P - P.etaI)),
    lamS P, φ⟩

/-- Cochrane (2023), §5.5 (tool): the closed form, `q` and the realised-inflation law in every
equilibrium, in the form used by `gV_decomp`. -/
theorem passive_closed {P : Params} (hP : Standard P) (hpass : Passive P) (hω : |P.omega| < 1)
    (hηi : |P.etaI| < 1) (φ : ℝ) {ei es ui us x p q : ℕ → Ω → ℝ}
    (hsh : Shocks 𝔼 P ei es ui us)
    (h64 : ∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - 𝔼.E t (p (t + 1))))
    (h65 : ∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t)
    (h68 : ∀ t, innov 𝔼 t (p (t + 1)) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1))
    (h72 : ∀ t, 𝔼.E t (rnNext P q t) = iRule P x p ui t) (hap : 𝔼.Adapted p)
    (haq : 𝔼.Adapted q) (hbx : BoundedProc x) (hbp : BoundedProc p) (hbq : BoundedProc q) :
    (∀ t, x t = (passiveCoef P φ).G • p t - (passiveCoef P φ).d • ui t) ∧
    (∀ t, q t = qa P (passiveCoef P φ).G (passiveCoef P φ).lS • p t +
      qb P (passiveCoef P φ).G (passiveCoef P φ).d (passiveCoef P φ).c (passiveCoef P φ).lS •
        ui t) ∧
    ∀ t, p (t + 1) = (passiveCoef P φ).lS • p t + (passiveCoef P φ).c • ui t +
      xi P ei es (t + 1) := by
  have hsh' := hsh
  obtain ⟨-, -, hua, -, -, -, hub, -, hei, -, hul, -⟩ := hsh'
  obtain ⟨hx, hEp⟩ := closed_form 𝔼 hP hpass hηi hsh h64 h65 hbx hbp
  obtain ⟨-, -, hl1, hl2, -, -⟩ := roots_passive hP hpass
  have h1 : 1 - P.omega * lamS P ≠ 0 := by
    have : |P.omega * lamS P| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg P.omega, abs_lt.mpr ⟨hl1, hl2⟩, abs_nonneg (lamS P)]
    have := (abs_lt.mp this).2
    linarith
  have h2 : 1 - P.omega * P.etaI ≠ 0 := by
    have : |P.omega * P.etaI| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg P.omega, abs_nonneg P.etaI]
    have := (abs_lt.mp this).2
    linarith
  have hq := q_closed 𝔼 hω h1 h2 (E_ar1 𝔼 hua hei hul) hx hEp haq h72 hbq hbp hub
  refine ⟨hx, hq, fun t => ?_⟩
  have e := h68 t
  rw [innov_succ 𝔼 hap, hEp t, ← xi_succ] at e
  rw [← e]
  change p (t + 1) = lamS P • p t +
    (P.kappa * P.sigma / (P.beta * (lamU P - P.etaI))) • ui t + _
  abel

/-- Cochrane (2023), (5.71), p. 149: the debt root `φ = (1 − α)/ρ` of
`v_{t+1} = φ v_t + g_t`. -/
noncomputable def debtRoot (P : Params) : ℝ := (1 - P.alpha) / P.rho

/-- Cochrane (2023), §5.5: the closed-form coefficients with the model's debt root. -/
noncomputable def alphaCoef (P : Params) : DCoef := passiveCoef P (debtRoot P)

/-- Cochrane (2023), (5.71) (tool): the state part of debt as a sum of processes. -/
theorem hProc_eq (P : Params) (C : DCoef) (p ui us : ℕ → Ω → ℝ) :
    hProc P C p ui us = cKp P C • p + cKu P C • ui + cKs P C • us := rfl

/-- **Existence at any `α` with `|1 − α| ≥ ρ`** (Cochrane (2023), (5.71), p. 149; the boundary
case of `α ∈ (1 − ρ, 1 + ρ)`): under the sign restrictions, the passive-money condition,
`|ω|, |η_i|, |η_s| < 1` and `ρ > 0`, a bounded equilibrium exists iff the shock-driven recursion
`W_{t+1} = φ W_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}`, `W_0 = v_0 − h_0`, `φ = (1 − α)/ρ`, is bounded.
(The value of debt is `v = h + W`, `h` the bounded state part.) -/
theorem alpha_exists_iff {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1)
    (hφ : 1 ≤ |debtRoot P|) {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us)
    (p0 v0 : ℝ) :
    (∃ x p q v, RedEquil 𝔼 P ei es ui us p0 v0 x p q v) ↔
      ∃ W : ℕ → Ω → ℝ, BoundedProc W ∧
        W 0 = (fun _ => v0) - (cKp P (alphaCoef P) • (fun _ => p0) +
          cKu P (alphaCoef P) • ui 0 + cKs P (alphaCoef P) • us 0) ∧
        ∀ t, W (t + 1) = debtRoot P • W t + kapS P (alphaCoef P) • es (t + 1) +
          kapI P (alphaCoef P) • ei (t + 1) := by
  have hsh' := hsh
  obtain ⟨hea, hesa, hua, husa, -, -, hub, husb, -, -, hul, husl⟩ := hsh'
  obtain ⟨-, -, hl1, hl2, -, -⟩ := roots_passive hP hpass
  have hne1 : (alphaCoef P).lS ≠ (alphaCoef P).phi := by
    intro h
    change lamS P = debtRoot P at h
    have : |lamS P| < 1 := abs_lt.mpr ⟨hl1, hl2⟩
    rw [h] at this
    linarith
  have hne2 : P.etaI ≠ (alphaCoef P).phi := by
    intro h
    change P.etaI = debtRoot P at h
    rw [h] at hηi
    linarith
  have hne3 : P.etaS ≠ (alphaCoef P).phi := by
    intro h
    change P.etaS = debtRoot P at h
    rw [h] at hηs
    linarith
  have hphi : (alphaCoef P).phi = (1 - P.alpha) / P.rho := rfl
  have hbh : ∀ {p : ℕ → Ω → ℝ}, BoundedProc p →
      BoundedProc (hProc P (alphaCoef P) p ui us) := fun hbp => by
    rw [hProc_eq]
    exact bdd_add (bdd_add (bdd_smul _ hbp) (bdd_smul _ hub)) (bdd_smul _ husb)
  constructor
  · rintro ⟨x, p, q, v, ⟨⟨h64, h65, h68, h71, h72⟩, hax, hap, haq, hav, hbx, hbp, hbq, hbv,
      hp0, hv0⟩⟩
    obtain ⟨hx, hq, hp1⟩ := passive_closed 𝔼 hP hpass hω hηi (debtRoot P) hsh h64 h65 h68 h72
      hap haq hbx hbp hbq
    have hdec := gV_decomp (C := alphaCoef P) hρ0.ne' hne1 hne2 hne3 hx hq hp1 hul husl
    have hrec := (eq571_iff hρ0.ne').mp h71
    refine ⟨v - hProc P (alphaCoef P) p ui us, bdd_sub hbv (hbh hbp), ?_, fun t => ?_⟩
    · change v 0 - hProc P (alphaCoef P) p ui us 0 = _
      rw [hv0, hProc, hp0]
    · change v (t + 1) - hProc P (alphaCoef P) p ui us (t + 1) =
        debtRoot P • (v t - hProc P (alphaCoef P) p ui us t) + _ + _
      rw [hrec t, hdec t, hphi, debtRoot, smul_sub]
      abel
  · rintro ⟨W, hWb, hW0, hWr⟩
    obtain ⟨x, p, q, h64, h65, h68, h72, hax, hap, haq, hbx, hbp, hbq, hp0⟩ :=
      exists_block_q 𝔼 hP hpass hω hsh p0
    obtain ⟨hx, hq, hp1⟩ := passive_closed 𝔼 hP hpass hω hηi (debtRoot P) hsh h64 h65 h68 h72
      hap haq hbx hbp hbq
    have hdec := gV_decomp (C := alphaCoef P) hρ0.ne' hne1 hne2 hne3 hx hq hp1 hul husl
    have hWa : 𝔼.Adapted W := by
      refine adapted_of_rec 𝔼 (φ := debtRoot P)
        (g := fun t => kapS P (alphaCoef P) • es (t + 1) + kapI P (alphaCoef P) • ei (t + 1))
        ?_ (fun t => ?_) (fun t => by rw [hWr t, add_assoc])
      · rw [hW0]
        simp only [map_sub, map_add, map_smul, 𝔼.const, hua 0, husa 0]
      · simp only [map_add, map_smul, hesa (t + 1), hea (t + 1)]
    have hha : 𝔼.Adapted (hProc P (alphaCoef P) p ui us) := by
      rw [hProc_eq]
      exact adapted_add 𝔼 (adapted_add 𝔼 (adapted_smul 𝔼 _ hap) (adapted_smul 𝔼 _ hua))
        (adapted_smul 𝔼 _ husa)
    refine ⟨x, p, q, W + hProc P (alphaCoef P) p ui us, ⟨⟨h64, h65, h68,
      (eq571_iff hρ0.ne').mpr fun t => ?_, h72⟩, hax, hap, haq, adapted_add 𝔼 hWa hha, hbx, hbp,
      hbq, bdd_add hWb (hbh hbp), hp0, ?_⟩⟩
    · change W (t + 1) + hProc P (alphaCoef P) p ui us (t + 1) =
        ((1 - P.alpha) / P.rho) • (W t + hProc P (alphaCoef P) p ui us t) + gV P x p q us t
      rw [hWr t, hdec t, hphi, debtRoot, smul_add]
      abel
    · change W 0 + hProc P (alphaCoef P) p ui us 0 = _
      rw [hW0, hProc, hp0]
      abel

/-! ### Exact determinacy in `α` and the unit root, at model level -/

/-- Cochrane (2023), §5.5, p. 148 ("the unique stationary equilibrium"), at model level: for
**every** admissible shock process (bounded, adapted, unpredictable shocks and AR(1)
disturbances with the model's `η_i, η_s`) and every initial inflation and debt, the reduced model
has exactly one bounded equilibrium. -/
def ModelDeterminate (P : Params) : Prop :=
  ∀ ei es ui us : ℕ → Ω → ℝ, Shocks 𝔼 P ei es ui us → ∀ p0 v0 : ℝ,
    ∃! y : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      RedEquil 𝔼 P ei es ui us p0 v0 y.1 y.2.1 y.2.2.1 y.2.2.2

/-- Cochrane (2023), §5.5 (tool): existence plus `policyRules_unique` give a unique
equilibrium. -/
theorem existsUnique_of_exists {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ : P.rho ≠ 0) {ei es ui us : ℕ → Ω → ℝ}
    (hsh : Shocks 𝔼 P ei es ui us) {p0 v0 : ℝ}
    (h : ∃ x p q v, RedEquil 𝔼 P ei es ui us p0 v0 x p q v) :
    ∃! y : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      RedEquil 𝔼 P ei es ui us p0 v0 y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  obtain ⟨x, p, q, v, hr⟩ := h
  refine ⟨(x, p, q, v), hr, fun y hy => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := policyRules_unique 𝔼 hP hpass hω hρ hsh hy hr
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

/-- Cochrane (2023), (5.71) (boundary case `|1 − α| = ρ`): if the shock-driven part of debt has
no forcing (`κ_s ε_{s,t+1} + κ_i ε_{i,t+1} = 0` at every date — e.g. no news after date 0, or
`κ_s = κ_i = 0`), a bounded equilibrium exists. -/
theorem boundary_exists_of {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1)
    (h1 : |debtRoot P| = 1) {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us)
    (hz : ∀ t, kapS P (alphaCoef P) • es (t + 1) + kapI P (alphaCoef P) • ei (t + 1) = 0)
    (p0 v0 : ℝ) : ∃ x p q v, RedEquil 𝔼 P ei es ui us p0 v0 x p q v := by
  have hsh' := hsh
  obtain ⟨-, -, -, -, -, -, ⟨Mu, hMu⟩, ⟨Ms, hMs⟩, -, -, -, -⟩ := hsh'
  set W0 : Ω → ℝ := (fun _ => v0) - (cKp P (alphaCoef P) • (fun _ => p0) +
    cKu P (alphaCoef P) • ui 0 + cKs P (alphaCoef P) • us 0) with hW0
  refine (alpha_exists_iff 𝔼 hP hpass hω hρ0 hηi hηs h1.ge hsh p0 v0).mpr
    ⟨fun t => debtRoot P ^ t • W0, ⟨|v0| + |cKp P (alphaCoef P)| * |p0| +
      |cKu P (alphaCoef P)| * |Mu| + |cKs P (alphaCoef P)| * |Ms|, fun t ω => ?_⟩,
      by change debtRoot P ^ 0 • W0 = _; rw [pow_zero, one_smul, hW0], fun t => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, h1, one_pow, one_mul, hW0,
      Pi.sub_apply, Pi.add_apply]
    have a1 := (hMu 0 ω).trans (le_abs_self Mu)
    have a2 := (hMs 0 ω).trans (le_abs_self Ms)
    calc |v0 - (cKp P (alphaCoef P) * p0 + cKu P (alphaCoef P) * ui 0 ω +
          cKs P (alphaCoef P) * us 0 ω)|
        ≤ |v0| + (|cKp P (alphaCoef P) * p0| + |cKu P (alphaCoef P) * ui 0 ω| +
          |cKs P (alphaCoef P) * us 0 ω|) :=
          (abs_sub _ _).trans (add_le_add le_rfl ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)))
      _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_mul]
          have b1 := mul_le_mul_of_nonneg_left a1 (abs_nonneg (cKu P (alphaCoef P)))
          have b2 := mul_le_mul_of_nonneg_left a2 (abs_nonneg (cKs P (alphaCoef P)))
          linarith
  · rw [add_assoc, hz t, add_zero]
    change debtRoot P ^ (t + 1) • W0 = debtRoot P • (debtRoot P ^ t • W0)
    rw [pow_succ', mul_smul]

/-- Cochrane (2023), §5.5 (a degenerate but admissible expectation system used for
counterexamples): states are coin sequences `ω : ℕ → Bool`, and `E_t` evaluates at the path that
keeps the first `t` coins and sets all later coins to `false`. -/
def trunc (t : ℕ) (ω : ℕ → Bool) : ℕ → Bool := fun k => if k < t then ω k else false

/-- Cochrane (2023), §5.5 (tool): truncating later does not change an earlier truncation. -/
theorem trunc_trunc_of_le {s t : ℕ} (h : s ≤ t) (ω : ℕ → Bool) :
    trunc t (trunc s ω) = trunc s ω := by
  funext k
  simp only [trunc]
  split_ifs <;> first | rfl | omega

/-- Cochrane (2023), §5.5 (tool): truncating earlier after a later truncation. -/
theorem trunc_trunc_of_le' {s t : ℕ} (h : s ≤ t) (ω : ℕ → Bool) :
    trunc s (trunc t ω) = trunc s ω := by
  funext k
  simp only [trunc]
  split_ifs <;> first | rfl | omega

/-- Cochrane (2023), §5.5: the truncation expectation system (an `ExpectationSystem`: linear,
constants, monotone, law of iterated expectations, earlier information known later). Under it a
coin-driven shock `ε_{t+1} = 1{coin t}` is unpredictable, `E_t ε_{t+1} = 0`, yet can recur on
every date along a path. -/
def truncSystem : ExpectationSystem (ℕ → Bool) where
  E t := LinearMap.funLeft ℝ ℝ (trunc t)
  const _ _ := rfl
  mono t _ _ h := fun ω => h (trunc t ω)
  tower {s t} h x := by
    funext ω
    simp only [LinearMap.funLeft_apply, trunc_trunc_of_le h]
  known {s t} h x := by
    funext ω
    simp only [LinearMap.funLeft_apply, trunc_trunc_of_le' h]

/-- Cochrane (2023), §5.5 (tool): `E_t` in the truncation system. -/
theorem truncSystem_E (t : ℕ) (x : (ℕ → Bool) → ℝ) (ω : ℕ → Bool) :
    truncSystem.E t x ω = x (trunc t ω) := rfl

/-- Cochrane (2023), §5.5 (counterexample shocks): `ε_{t+1} = φ^{t+1} a` if coin `t` is heads,
else `0` (and `ε_0 = 0`). -/
noncomputable def bump (a φ : ℝ) : ℕ → (ℕ → Bool) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => if ω t then φ ^ (t + 1) * a else 0

/-- Cochrane (2023), §5.5 (tool): the bump shocks are adapted, unpredictable and bounded. -/
theorem bump_props (a φ : ℝ) (hφ : |φ| = 1) :
    truncSystem.Adapted (bump a φ) ∧ (∀ t, truncSystem.E t (bump a φ (t + 1)) = 0) ∧
      BoundedProc (bump a φ) := by
  refine ⟨fun t => ?_, fun t => ?_, ⟨|a|, fun t ω => ?_⟩⟩
  · funext ω
    cases t with
    | zero => rfl
    | succ t =>
      rw [truncSystem_E]
      simp [bump, trunc]
  · funext ω
    rw [truncSystem_E]
    simp [bump, trunc]
  · cases t with
    | zero => simp [bump]
    | succ t =>
      simp only [bump]
      split_ifs
      · rw [abs_mul, abs_pow, hφ, one_pow, one_mul]
      · simp

/-- Cochrane (2023), §5.5 (tool): the bump shocks with AR(1) disturbances driven by them satisfy
the shock assumptions under the truncation system. -/
theorem bump_shocks (P : Params) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1) (ki ks φ : ℝ)
    (hφ : |φ| = 1) :
    Shocks truncSystem P (bump ki φ) (bump ks φ)
      (backRec P.etaI (fun t => bump ki φ (t + 1)) 0)
      (backRec P.etaS (fun t => bump ks φ (t + 1)) 0) := by
  obtain ⟨ai, mi, ⟨Bi, hBi⟩⟩ := bump_props ki φ hφ
  obtain ⟨as, ms, ⟨Bs, hBs⟩⟩ := bump_props ks φ hφ
  refine ⟨ai, as, backRec_adapted truncSystem (fun t => ai (t + 1)) 0,
    backRec_adapted truncSystem (fun t => as (t + 1)) 0, ⟨Bi, hBi⟩, ⟨Bs, hBs⟩,
    ⟨_, backRec_bound hηi (fun t ω => hBi (t + 1) ω) 0⟩,
    ⟨_, backRec_bound hηs (fun t ω => hBs (t + 1) ω) 0⟩, mi, ms, fun t => rfl, fun t => rfl⟩

/-- Cochrane (2023), §5.5 (the non-existence mechanism): along the all-heads path the recursion
`W_{t+1} = φ W_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}` with `|φ| = 1`, `W_0 = 0` and bump shocks of
sizes `κ_s, κ_i` grows like `t (κ_s² + κ_i²)`, so it is unbounded unless `κ_s = κ_i = 0`. -/
theorem bump_unbounded {φ ks ki : ℝ} (hφ : |φ| = 1) (hk : ks ≠ 0 ∨ ki ≠ 0)
    {W : ℕ → (ℕ → Bool) → ℝ} (h0 : W 0 = 0)
    (hr : ∀ t, W (t + 1) = φ • W t + ks • bump ks φ (t + 1) + ki • bump ki φ (t + 1)) :
    ¬ BoundedProc W := by
  set ω₀ : ℕ → Bool := fun _ => true
  set K := ks ^ 2 + ki ^ 2 with hK
  have hK0 : 0 < K := by
    rcases hk with h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
  have hval : ∀ t : ℕ, W t ω₀ = t * φ ^ t * K := by
    intro t
    induction t with
    | zero => rw [h0]; simp
    | succ t ih =>
      have := congrFun (hr t) ω₀
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bump, ω₀, ↓reduceIte] at this
      rw [this, ih]
      push_cast
      ring
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (M / K)
  have := hM n ω₀
  rw [hval, abs_mul, abs_mul, abs_pow, hφ, one_pow, mul_one, abs_of_pos hK0,
    Nat.abs_cast] at this
  rw [div_lt_iff₀ hK0] at hn
  linarith

/-- **Exact determinacy in `α` under perfect foresight** (Cochrane (2023), §5.5, p. 148, and the
condition `α ∈ (1 − ρ, 1 + ρ)` of §5.4): with the sign restrictions, the passive-money condition,
`|ω|, |η_i|, |η_s| < 1` and `ρ > 0`, the model is determinate under perfect foresight iff
`|1 − α| ≤ ρ` — the boundary `|1 − α| = ρ` included, since without news the shock-driven part of
debt never moves. -/
theorem alpha_iff_pf {P : Params} (hP : Standard P) (hpass : Passive P) (hω : |P.omega| < 1)
    (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1) :
    ModelDeterminate perfectForesight P ↔ |1 - P.alpha| ≤ P.rho := by
  constructor
  · intro hd
    by_contra hc
    push Not at hc
    obtain ⟨y, hy, -⟩ := hd 0 0 0 0 (shocks_zero perfectForesight P) 0 1
    exact nonexist_of_alpha perfectForesight hP hpass hω hρ0 hc _ _ _ _ hy
  · intro h ei es ui us hsh p0 v0
    rcases h.lt_or_eq with h | h
    · exact policyRules_determinate perfectForesight hP hpass hω hρ0 h hsh p0 v0
    · have h1 : |debtRoot P| = 1 := by
        rw [debtRoot, abs_div, abs_of_pos hρ0, h, div_self hρ0.ne']
      have hsh' := hsh
      obtain ⟨-, -, -, -, -, -, -, -, hei, hes, -, -⟩ := hsh'
      refine existsUnique_of_exists perfectForesight hP hpass hω hρ0.ne' hsh
        (boundary_exists_of perfectForesight hP hpass hω hρ0 hηi hηs h1 hsh (fun t => ?_) p0 v0)
      have e1 : es (t + 1) = 0 := hes t
      have e2 : ei (t + 1) = 0 := hei t
      rw [e1, e2, smul_zero, smul_zero, add_zero]

/-- **Exact determinacy in `α` with recurring news** (Cochrane (2023), §5.5, p. 148): under the
truncation expectation system, with the sign restrictions, the passive-money condition,
`|ω|, |η_i|, |η_s| < 1` and `ρ > 0`, the model is determinate iff `|1 − α| < ρ`, or `|1 − α| = ρ`
and both shock loadings of the debt recursion vanish (`κ_s = κ_i = 0`). On the boundary with a
nonzero loading, repeated shocks drive debt along a unit root and no bounded equilibrium
exists. -/
theorem alpha_iff_trunc {P : Params} (hP : Standard P) (hpass : Passive P) (hω : |P.omega| < 1)
    (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1) :
    ModelDeterminate truncSystem P ↔ |1 - P.alpha| < P.rho ∨
      (|1 - P.alpha| = P.rho ∧ kapS P (alphaCoef P) = 0 ∧ kapI P (alphaCoef P) = 0) := by
  have hroot : ∀ h : |1 - P.alpha| = P.rho, |debtRoot P| = 1 := fun h => by
    rw [debtRoot, abs_div, abs_of_pos hρ0, h, div_self hρ0.ne']
  constructor
  · intro hd
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    rcases h1.lt_or_eq with h | h
    · obtain ⟨y, hy, -⟩ := hd 0 0 0 0 (shocks_zero truncSystem P) 0 1
      exact nonexist_of_alpha truncSystem hP hpass hω hρ0 h _ _ _ _ hy
    · have hk : kapS P (alphaCoef P) ≠ 0 ∨ kapI P (alphaCoef P) ≠ 0 := by
        by_contra hk
        push Not at hk
        exact h2 h.symm hk.1 hk.2
      have h1' := hroot h.symm
      have hsh := bump_shocks P hηi hηs (kapI P (alphaCoef P)) (kapS P (alphaCoef P))
        (debtRoot P) h1'
      obtain ⟨y, hy, -⟩ := hd _ _ _ _ hsh 0 0
      obtain ⟨W, hWb, hW0, hWr⟩ := (alpha_exists_iff truncSystem hP hpass hω hρ0 hηi hηs
        h1'.ge hsh 0 0).mp ⟨_, _, _, _, hy⟩
      refine bump_unbounded h1' (hk.imp id id) ?_ hWr hWb
      rw [hW0]
      funext ω
      simp [backRec]
  · rintro (h | ⟨h, hks, hki⟩) ei es ui us hsh p0 v0
    · exact policyRules_determinate truncSystem hP hpass hω hρ0 h hsh p0 v0
    · refine existsUnique_of_exists truncSystem hP hpass hω hρ0.ne' hsh
        (boundary_exists_of truncSystem hP hpass hω hρ0 hηi hηs (hroot h) hsh (fun t => ?_)
          p0 v0)
      rw [hks, hki, zero_smul, zero_smul, add_zero]

/-- Cochrane (2023), A1 §1.9, p. 574 (the unit-root case `θ_iπ = 1` of "two eigenvalues greater
or equal to one"): the loading `k = c/(1 − η_i)` of the inflation martingale on `u_i`, with
`c = κσ/(β(det − η_i))`. -/
noncomputable def urK (P : Params) : ℝ :=
  P.kappa * P.sigma / (P.beta * (detB P - P.etaI)) / (1 - P.etaI)

/-- Cochrane (2023), A1 §1.9, p. 574 (tool): on the boundary `κ(θ_iπ − 1) + (1 − β)θ_ix = 0` the
roots of the `(x, π)` block are `det > 1` and `1`. -/
theorem unitroot_roots {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) :
    1 < detB P ∧ detB P + 1 = trB P ∧ detB P * 1 = detB P := by
  have h1 : charB P 1 = 0 := by rw [charB_one hP.2.2.1.ne', hb, mul_zero]
  refine ⟨one_lt_detB hP, ?_, mul_one _⟩
  rw [charB] at h1
  linarith

/-- **The unit-root case, uniqueness** (Cochrane (2023), A1 §1.9, pp. 574–576, E20): on the
boundary `κ(θ_iπ − 1) + (1 − β)θ_ix = 0` (roots `det > 1` and `1`), with `|η_i| < 1`, `|ω| < 1`
and `ρ ≠ 0`, the reduced model has at most one bounded equilibrium. -/
theorem unitroot_unique {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hω : |P.omega| < 1) (hρ : P.rho ≠ 0) {ei es ui us : ℕ → Ω → ℝ}
    (hsh : Shocks 𝔼 P ei es ui us) {p0 v0 : ℝ} {x p q v x' p' q' v' : ℕ → Ω → ℝ}
    (h : RedEquil 𝔼 P ei es ui us p0 v0 x p q v)
    (h' : RedEquil 𝔼 P ei es ui us p0 v0 x' p' q' v') :
    x = x' ∧ p = p' ∧ q = q' ∧ v = v' := by
  obtain ⟨hD, hsum, hprod⟩ := unitroot_roots hP hb
  obtain ⟨⟨h64, h65, h68, h71, h72⟩, -, hap, haq, -, hbx, hbp, hbq, -, hp0, hv0⟩ := h
  obtain ⟨⟨h64', h65', h68', h71', h72'⟩, -, hap', haq', -, hbx', hbp', hbq', -, hp0', hv0'⟩ := h'
  obtain ⟨hx, hEp⟩ := closed_form_gen 𝔼 hP hD hsum hprod hηi hsh h64 h65 hbx hbp
  obtain ⟨hx', hEp'⟩ := closed_form_gen 𝔼 hP hD hsum hprod hηi hsh h64' h65' hbx' hbp'
  have hpp : p = p' := by
    funext t
    induction t with
    | zero => rw [hp0, hp0']
    | succ t ih =>
      have e := h68 t
      have e' := h68' t
      rw [innov_succ 𝔼 hap, hEp t] at e
      rw [innov_succ 𝔼 hap', hEp' t, ← ih] at e'
      rw [← sub_eq_zero]
      have := e.trans e'.symm
      rw [← sub_eq_zero] at this
      rw [← this]
      abel
  subst hpp
  have hxx : x = x' := by
    funext t
    rw [hx t, hx' t]
  subst hxx
  have hqq : q = q' := 𝔼.forward_unique hω ((eq572_iff 𝔼 haq).mp h72)
    ((eq572_iff 𝔼 haq').mp h72') hbq hbq'
  subst hqq
  have hvv : v = v' := (eq_backRec hv0 ((eq571_iff hρ).mp h71)).trans
    (eq_backRec hv0' ((eq571_iff hρ).mp h71')).symm
  exact ⟨rfl, rfl, rfl, hvv⟩

/-- **The unit-root case, existence** (Cochrane (2023), A1 §1.9, pp. 574–576, E20): on the
boundary `κ(θ_iπ − 1) + (1 − β)θ_ix = 0`, with `|η_i| < 1`, `|ω| < 1`, `ρ > 0` and
`|1 − α| < ρ`, a bounded equilibrium exists iff the inflation martingale
`W = π + k u_i` (`k = c/(1 − η_i)`), which obeys
`W_{t+1} = W_t − β_s ε_{s,t+1} + (k − β_i) ε_{i,t+1}` from `W_0 = π_0 + k u_{i,0}`, is bounded. -/
theorem unitroot_exists_iff {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : Shocks 𝔼 P ei es ui us) (p0 v0 : ℝ) :
    (∃ x p q v, RedEquil 𝔼 P ei es ui us p0 v0 x p q v) ↔
      ∃ W : ℕ → Ω → ℝ, BoundedProc W ∧ W 0 = (fun _ => p0) + urK P • ui 0 ∧
        ∀ t, W (t + 1) = W t + (-P.betaS) • es (t + 1) + (urK P - P.betaI) • ei (t + 1) := by
  obtain ⟨hD, hsum, hprod⟩ := unitroot_roots hP hb
  have hβ := hP.2.2.1.ne'
  have hκ := hP.2.1.ne'
  have hsh' := hsh
  obtain ⟨hea, hesa, hua, husa, -, -, hub, husb, hei, hes, hul, husl⟩ := hsh'
  have hη1 : 1 - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2; linarith
  have hηD : detB P - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2; linarith
  have hk : urK P * (1 - P.etaI) = P.kappa * P.sigma / (P.beta * (detB P - P.etaI)) := by
    rw [urK]; field_simp
  have hEu := E_ar1 𝔼 hua hei hul
  constructor
  · rintro ⟨x, p, q, v, ⟨⟨h64, h65, h68, -, -⟩, -, hap, -, -, hbx, hbp, -, -, hp0, -⟩⟩
    obtain ⟨-, hEp⟩ := closed_form_gen 𝔼 hP hD hsum hprod hηi hsh h64 h65 hbx hbp
    refine ⟨p + urK P • ui, bdd_add hbp (bdd_smul _ hub), by rw [Pi.add_apply, hp0]; rfl,
      fun t => ?_⟩
    have e := h68 t
    rw [innov_succ 𝔼 hap, hEp t] at e
    funext ω
    have eω := congrFun e ω
    have eu := congrFun (hul t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at eω eu ⊢
    rw [eu]
    linear_combination eω - ui t ω * hk
  · rintro ⟨W, hWb, hW0, hWr⟩
    have hWa : 𝔼.Adapted W := by
      refine adapted_of_rec 𝔼 (φ := 1)
        (g := fun t => (-P.betaS) • es (t + 1) + (urK P - P.betaI) • ei (t + 1)) ?_
        (fun t => ?_) (fun t => by rw [hWr t, one_smul, add_assoc])
      · rw [hW0]
        simp only [map_add, map_smul, 𝔼.const, hua 0]
      · simp only [map_add, map_smul, hesa (t + 1), hea (t + 1)]
    set p : ℕ → Ω → ℝ := W - urK P • ui with hp
    set d := P.sigma / (detB P - P.etaI) with hd
    set x : ℕ → Ω → ℝ := gainOf P 1 • p - d • ui with hx
    have hap : 𝔼.Adapted p := adapted_sub 𝔼 hWa (adapted_smul 𝔼 _ hua)
    have hax : 𝔼.Adapted x := adapted_sub 𝔼 (adapted_smul 𝔼 _ hap) (adapted_smul 𝔼 _ hua)
    have hbp : BoundedProc p := bdd_sub hWb (bdd_smul _ hub)
    have hbx : BoundedProc x := bdd_sub (bdd_smul _ hbp) (bdd_smul _ hub)
    have hEW : ∀ t, 𝔼.E t (W (t + 1)) = W t := by
      intro t
      rw [hWr t, map_add, map_add, map_smul, map_smul, hes t, hei t, hWa t, smul_zero,
        smul_zero, add_zero, add_zero]
    have hEp : ∀ t, 𝔼.E t (p (t + 1)) =
        (1 : ℝ) • p t + (P.kappa * P.sigma / (P.beta * (detB P - P.etaI))) • ui t := by
      intro t
      funext ω
      have e1 := congrFun (hEW t) ω
      have e2 := congrFun (hEu t) ω
      simp only [hp, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub,
        map_smul] at e1 e2 ⊢
      rw [e1, e2]
      linear_combination ui t ω * hk
    obtain ⟨h64, h65⟩ := closed_form_converse 𝔼 hβ hκ hsum hprod hηD hEu
      (x := x) (p := p) (fun t => by rw [hx, hd]; rfl) hEp
    have h68 : ∀ t, innov 𝔼 t (p (t + 1)) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1) := by
      intro t
      rw [innov_succ 𝔼 hap, hEp t]
      funext ω
      have e1 := congrFun (hWr t) ω
      have e2 := congrFun (hul t) ω
      simp only [hp, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
        smul_eq_mul] at e1 e2 ⊢
      rw [e1, e2]
      linear_combination ui t ω * hk
    have hib : BoundedProc (fun t => -iRule P x p ui t) := by
      obtain ⟨M, hM⟩ := bdd_add (bdd_add (bdd_smul P.thIpi hbp) (bdd_smul P.thIx hbx)) hub
      refine ⟨M, fun t ω => ?_⟩
      rw [show (fun t => -iRule P x p ui t) t ω = -(iRule P x p ui t ω) from rfl, abs_neg]
      exact hM t ω
    have hia : 𝔼.Adapted (fun t => -iRule P x p ui t) := by
      intro t
      simp only [iRule, map_neg, map_add, map_smul, hap t, hax t, hua t]
    obtain ⟨q, ⟨hbq, hqs⟩, -⟩ := ForwardSolution.existsUnique_bounded 𝔼 hω hib hia
    have haq := ForwardSolution.solves_adapted 𝔼 hia hqs
    set φ := (1 - P.alpha) / P.rho with hφdef
    have hφ : |φ| < 1 := by rw [hφdef, abs_div, abs_of_pos hρ0, div_lt_one hρ0]; exact hα
    have hgb : BoundedProc (gV P x p q us) :=
      bdd_smul P.rho⁻¹ (bdd_sub (bdd_sub (bdd_sub (bdd_sub (bdd_smul P.omega
        (bdd_shift hbq)) hbq) (bdd_smul (1 + P.thSpi) (bdd_shift hbp)))
        (bdd_smul P.thSx (bdd_shift hbx))) (bdd_shift husb))
    have hga : ∀ t, 𝔼.E (t + 1) (gV P x p q us t) = gV P x p q us t := by
      intro t
      simp only [gV, rnNext, map_smul, map_sub, haq (t + 1), hap (t + 1), hax (t + 1),
        husa (t + 1), E_succ_of_adapted 𝔼 haq t]
    obtain ⟨Mg, hMg⟩ := hgb
    refine ⟨x, p, q, backRec φ (gV P x p q us) v0, ⟨⟨h64, h65, h68,
      (eq571_iff hρ0.ne').mpr (fun t => rfl), (eq572_iff 𝔼 haq).mpr hqs⟩, hax, hap, haq,
      backRec_adapted 𝔼 hga v0, hbx, hbp, hbq, ⟨_, backRec_bound hφ hMg v0⟩, ?_, rfl⟩⟩
    rw [hp, Pi.sub_apply, hW0]
    funext ω
    simp

/-- **The unit-root case under perfect foresight** (Cochrane (2023), A1 §1.9, pp. 574–576; E20
refined): on the boundary `κ(θ_iπ − 1) + (1 − β)θ_ix = 0`, with `|η_i| < 1`, `|ω| < 1`, `ρ > 0`
and `|1 − α| < ρ`, the model **is** determinate under perfect foresight — with the model's own
stationary AR(1) forcing a unit eigenvalue does not break determinacy (inflation is constant
after the disturbance dies out). -/
theorem unitroot_pf {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho) :
    ModelDeterminate perfectForesight P := by
  intro ei es ui us hsh p0 v0
  have hsh' := hsh
  obtain ⟨-, -, -, -, -, -, ⟨Mu, hMu⟩, -, hei, hes, -, -⟩ := hsh'
  obtain ⟨x, p, q, v, hr⟩ := (unitroot_exists_iff perfectForesight hP hb hηi hω hρ0 hα hsh
    p0 v0).mpr ⟨fun _ => (fun _ => p0) + urK P • ui 0,
      ⟨|p0| + |urK P| * |Mu|, fun t ω => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hMu 0 ω).trans (le_abs_self Mu)) (abs_nonneg _)⟩,
      rfl, fun t => by
        have e1 : es (t + 1) = 0 := hes t
        have e2 : ei (t + 1) = 0 := hei t
        rw [e1, e2, smul_zero, smul_zero, add_zero, add_zero]⟩
  refine ⟨(x, p, q, v), hr, fun y hy => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := unitroot_unique perfectForesight hP hb hηi hω hρ0.ne' hsh hy hr
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

/-- **The unit-root case with recurring news** (Cochrane (2023), A1 §1.9, pp. 574–576; E20):
under the truncation expectation system, on the boundary `κ(θ_iπ − 1) + (1 − β)θ_ix = 0`, with
`|η_i|, |η_s|, |ω| < 1`, `ρ > 0` and `|1 − α| < ρ`, the model is determinate iff
`β_s = 0` and `β_i = k` — i.e. iff no shock moves the inflation martingale; otherwise repeated
shocks make inflation a random walk and no bounded equilibrium exists. -/
theorem unitroot_iff_trunc {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho) :
    ModelDeterminate truncSystem P ↔ P.betaS = 0 ∧ P.betaI = urK P := by
  constructor
  · intro hd
    by_contra hc
    have hk : -P.betaS ≠ 0 ∨ urK P - P.betaI ≠ 0 := by
      by_contra hk
      push Not at hk
      exact hc ⟨by linarith [hk.1], by linarith [hk.2]⟩
    have h1 : |(1 : ℝ)| = 1 := abs_one
    have hsh := bump_shocks P hηi hηs (urK P - P.betaI) (-P.betaS) 1 h1
    obtain ⟨y, hy, -⟩ := hd _ _ _ _ hsh 0 0
    obtain ⟨W, hWb, hW0, hWr⟩ := (unitroot_exists_iff truncSystem hP hb hηi hω hρ0 hα hsh
      0 0).mp ⟨_, _, _, _, hy⟩
    refine bump_unbounded h1 hk ?_ (fun t => by rw [hWr t, one_smul]) hWb
    rw [hW0]
    funext ω
    simp [backRec]
  · rintro ⟨hs, hi⟩ ei es ui us hsh p0 v0
    have hsh' := hsh
    obtain ⟨-, -, -, -, -, -, ⟨Mu, hMu⟩, -, -, -, -, -⟩ := hsh'
    obtain ⟨x, p, q, v, hr⟩ := (unitroot_exists_iff truncSystem hP hb hηi hω hρ0 hα hsh
      p0 v0).mpr ⟨fun _ => (fun _ => p0) + urK P • ui 0,
        ⟨|p0| + |urK P| * |Mu|, fun t ω => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((hMu 0 ω).trans (le_abs_self Mu)) (abs_nonneg _)⟩,
        rfl, fun t => by rw [hs, hi, neg_zero, sub_self, zero_smul, zero_smul, add_zero,
          add_zero]⟩
    refine ⟨(x, p, q, v), hr, fun y hy => ?_⟩
    obtain ⟨e1, e2, e3, e4⟩ := unitroot_unique truncSystem hP hb hηi hω hρ0.ne' hsh hy hr
    exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

end Cochrane.StickyPriceFiscal.PolicyRules
