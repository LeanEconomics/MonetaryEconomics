/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.LongTermDebt
import StickyPriceFiscal.PolicyRules
import StickyPriceFiscal.NonlinearCT
import StickyPriceFiscal.CTSimple
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Links between modules: the bond weight and the continuous-time transversality conditions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.2 (eqs. (5.17)–(5.21),
pp. 127–129), §5.5 (eqs. (5.51)–(5.73), pp. 147–149), Online Appendix A1 §1.3 (eq. (1.22),
p. 563), §5.4.2 (eq. (5.44), p. 140) and §5.7.1 (eq. (5.95), p. 165).

Two links that the library previously stated by docstring only.

## 1. The exact bond weight `ω̃` of `LongTermDebt` and the `omega` of `PolicyRules.Params`

* The identification map `idParams σ β κ ρ ω̃ η_i η_s β_s β_i`: all policy-rule coefficients
  `θ_iπ, θ_ix, θ_sπ, θ_sx, α` zero, `omega := ω̃`, the remaining parameters carried over
  (`idParams_rules`, `zeroRules_iff_idParams`: its image is exactly the parameter sets with
  zero rules).
* The weight: `exact_weight_iff` — the bond return `ω q_{t+1} − q_t` of (5.60) is the exact
  derivative (A1 (1.22)) of the log return of the geometric portfolio at its steady state **iff**
  `omega = ω/(1 + i)`, the weight `ω̃` of `LongTermDebt`; `printed_weight_not_exact` (E23: with
  `omega = ω`, `ω, i > 0`, it is not); `same_exact_return` (both modules' returns are the same
  exact derivative).
* Equations: `redSys_iff_core` (the reduced model (5.64)–(5.73) is its core plus (5.68)),
  `redCore_idParams`, `ltd_iff_redCore` (the long-term-debt model (5.17)–(5.21) is the core of
  the reduced model at the identified parameters, with `r^n` given by (5.21) and the date-0
  flow).
* Solutions: `redEquil_iff_ltdEquil` (an equilibrium of the reduced model at the identified
  parameters is exactly a bounded adapted long-term-debt equilibrium with pre-sample debt
  `vm1Of`, constant initial values, and unexpected inflation (5.68)); `redEquil_eq_ltd` (it is
  then the unique equilibrium of `LongTermDebt.ltd_determinate`).

## 2. `NonlinearCT.tvc_iff_integral` and `CTSimple.tvc_iff_forward`

`NonlinearCT` measures time relative to the valuation date `t` (`e^{−rT} b_{t+T}`, integrand
`e^{−rτ} s_{t+τ}` on `(0, ∞)`) and assumes a two-sided derivative at every `τ ≥ 0` plus a
continuous surplus; `CTSimple` uses absolute time (`e^{−aT} v_T`, integrability of `e^{−aτ} f_τ`
on `(t, ∞)`) and needs only continuity on `[t, ∞)` and a derivative on `(t, ∞)`.

* Change of variables: `tvc_rel_eq`, `tvc_rel_iff_abs`, `integrable_rel_iff_abs`,
  `valuation_rel_eq`.
* `integralStmt_of_forwardStmt`: the statement of `NonlinearCT.tvc_iff_integral` follows from
  that of `CTSimple.tvc_iff_forward`, even without the continuity of the surplus
  (`tvc_iff_integral_of_forward`).
* `forwardContStmt_of_integralStmt`: the statement of `CTSimple.tvc_iff_forward`, for forcing
  continuous on `[t, ∞)`, follows from that of `NonlinearCT.tvc_iff_integral` (the path is
  shifted to start at `0` and extended linearly to the left; its right derivative at the start
  is obtained from the limit of derivatives). `tvc_iff_forward_of_integral` is the instance.
* `forward_hyps_discontinuous`: `CTSimple`'s hypotheses do not force continuous forcing, so
  the converse cannot drop the continuity hypothesis by translating hypotheses alone.
-/

namespace Cochrane.StickyPriceFiscal.LinksTidy

open Filter Topology MeasureTheory

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### 1. The identification map -/

/-- Cochrane (2023), §§5.2 and 5.5, pp. 127, 147: the identification map from the
long-term-debt model of §5.2 into the parameters of the model with rules. The rule coefficients
`θ_iπ, θ_ix, θ_sπ, θ_sx, α` are zero, `σ, κ, β, ρ` are carried over, `omega` is the exact weight
`ω̃ = om` of §5.2, and `η_i, η_s, β_s, β_i` are free. -/
def idParams (σ β κ ρ om ηi ηs bS bI : ℝ) : PolicyRules.Params :=
  ⟨σ, κ, β, 0, 0, 0, 0, 0, ρ, om, ηi, ηs, bS, bI⟩

/-- Cochrane (2023), pp. 127, 147: the identified parameters have the stated components. -/
theorem idParams_rules (σ β κ ρ om ηi ηs bS bI : ℝ) :
    (idParams σ β κ ρ om ηi ηs bS bI).sigma = σ ∧ (idParams σ β κ ρ om ηi ηs bS bI).beta = β ∧
    (idParams σ β κ ρ om ηi ηs bS bI).kappa = κ ∧ (idParams σ β κ ρ om ηi ηs bS bI).rho = ρ ∧
    (idParams σ β κ ρ om ηi ηs bS bI).omega = om ∧
    (idParams σ β κ ρ om ηi ηs bS bI).thIpi = 0 ∧ (idParams σ β κ ρ om ηi ηs bS bI).thIx = 0 ∧
    (idParams σ β κ ρ om ηi ηs bS bI).thSpi = 0 ∧ (idParams σ β κ ρ om ηi ηs bS bI).thSx = 0 ∧
    (idParams σ β κ ρ om ηi ηs bS bI).alpha = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Cochrane (2023), p. 147: a parameter set of §5.5 is in the image of the identification map
iff all its rule coefficients are zero; it is then the image of its own components. -/
theorem zeroRules_iff_idParams (P : PolicyRules.Params) :
    (P.thIpi = 0 ∧ P.thIx = 0 ∧ P.thSpi = 0 ∧ P.thSx = 0 ∧ P.alpha = 0) ↔
      P = idParams P.sigma P.beta P.kappa P.rho P.omega P.etaI P.etaS P.betaS P.betaI := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    cases P
    simp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rfl
  · intro h
    rw [h]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Cochrane (2023), (5.53), p. 147: at the identified parameters the rate rule is
`i_t = u_{i,t}` (the exogenous rate of §5.2). -/
theorem iRule_idParams (σ β κ ρ om ηi ηs bS bI : ℝ) (x p ui : ℕ → Ω → ℝ) (t : ℕ) :
    PolicyRules.iRule (idParams σ β κ ρ om ηi ηs bS bI) x p ui t = ui t := by
  simp [PolicyRules.iRule, idParams]

/-- Cochrane (2023), (5.54), p. 147: at the identified parameters the surplus rule is
`s̃_{t+1} = u_{s,t+1}` (the exogenous surplus of §5.2). -/
theorem sNext_idParams (σ β κ ρ om ηi ηs bS bI : ℝ) (x p v us : ℕ → Ω → ℝ) (t : ℕ) :
    PolicyRules.sNext (idParams σ β κ ρ om ηi ηs bS bI) x p v us t = us (t + 1) := by
  simp [PolicyRules.sNext, idParams]

/-- Cochrane (2023), (5.60) and (5.21): at the identified parameters the bond return of §5.5
is the return `ω̃ q_{t+1} − q_t` of §5.2. -/
theorem rnNext_idParams (σ β κ ρ om ηi ηs bS bI : ℝ) (q : ℕ → Ω → ℝ) (t : ℕ) :
    PolicyRules.rnNext (idParams σ β κ ρ om ηi ηs bS bI) q t = om • q (t + 1) - q t := rfl

/-! ### The weight: `omega` is the exact derivative coefficient iff `omega = ω/(1 + i)` -/

/-- Cochrane (2023), (5.60), p. 147: pointwise, the bond return of §5.5 is the linear map
`(dq_{t+1}, dq_t) ↦ omega dq_{t+1} − dq_t` applied to `(q_{t+1}, q_t)`. -/
theorem rnNext_eq_linear (P : PolicyRules.Params) (q : ℕ → Ω → ℝ) (t : ℕ) (w : Ω) :
    PolicyRules.rnNext P q t w = (P.omega • ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ) (q (t + 1) w, q t w) := by
  simp [PolicyRules.rnNext]

/-- Cochrane (2023), (5.60), p. 147, and A1 (1.22), p. 563: for `0 ≤ ω < 1 + i`, `1 + i > 0`,
the return map `omega dq_{t+1} − dq_t` of §5.5 is the exact derivative of the log return of the
geometric portfolio at its steady state `Q = 1/(1 + i − ω)` **iff** `omega = ω/(1 + i)`, the
exact weight `ω̃` with which `LongTermDebt` writes the model. -/
theorem exact_weight_iff {ω i : ℝ} (hi : 0 < 1 + i) (hω0 : 0 ≤ ω) (hω : ω < 1 + i)
    (P : PolicyRules.Params) :
    HasFDerivAt (LongTermDebt.bondReturn ω (1 / (1 + i - ω)))
      (P.omega • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) ↔
      P.omega = ω / (1 + i) := by
  have hQ : 0 < 1 / (1 + i - ω) := by
    have : 0 < 1 + i - ω := by linarith
    positivity
  have hd := LongTermDebt.bondReturn_hasFDerivAt hω0 hQ
  rw [(LongTermDebt.bondReturn_ss hi hω0 hω).2] at hd
  constructor
  · intro h
    have hu := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (1, 0)) (h.unique hd)
    simpa using hu
  · intro h
    rw [h]
    exact hd

/-- Cochrane (2023), A1 (1.24), p. 563, survey error E23: with the printed weight
`omega = ω` (and `ω > 0`, `i > 0`, `ω < 1 + i`) the return of (5.60) is **not** the exact
derivative of the portfolio return. -/
theorem printed_weight_not_exact {ω i : ℝ} (hω0 : 0 < ω) (hi0 : 0 < i) (hω : ω < 1 + i)
    (P : PolicyRules.Params) (hP : P.omega = ω) :
    ¬ HasFDerivAt (LongTermDebt.bondReturn ω (1 / (1 + i - ω)))
      (P.omega • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) (0, 0) := by
  rw [exact_weight_iff (by linarith) hω0.le hω, hP]
  exact (LongTermDebt.e23_coef_lt hω0 hi0).ne'

/-- Cochrane (2023), (5.21), (5.60) and A1 (1.22): with `ω̃ = ω/(1 + i)`, the return of the
long-term-debt model and the return of the model with rules at the identified parameters are
both the exact derivative `L` of the portfolio return at the steady state, applied to
`(q_{t+1}, q_t)`. -/
theorem same_exact_return {ω i : ℝ} (hi : 0 < 1 + i) (hω0 : 0 ≤ ω) (hω : ω < 1 + i)
    (σ β κ ρ ηi ηs bS bI : ℝ) {q rn : ℕ → Ω → ℝ}
    (h21 : ∀ t, rn (t + 1) = (ω / (1 + i)) • q (t + 1) - q t) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (LongTermDebt.bondReturn ω (1 / (1 + i - ω))) L (0, 0) ∧
      (∀ t w, rn (t + 1) w = L (q (t + 1) w, q t w)) ∧
      ∀ t w, PolicyRules.rnNext (idParams σ β κ ρ (ω / (1 + i)) ηi ηs bS bI) q t w =
        L (q (t + 1) w, q t w) := by
  refine ⟨(ω / (1 + i)) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ,
    (exact_weight_iff hi hω0 hω (idParams σ β κ ρ (ω / (1 + i)) ηi ηs bS bI)).2 rfl,
    fun t w => ?_, fun t w => rnNext_eq_linear _ q t w⟩
  rw [h21 t]
  simp

/-! ### Equations: the reduced model of §5.5 and the long-term-debt model of §5.2 -/

/-- Cochrane (2023), eqs. (5.64)–(5.73), pp. 148–149: the reduced model without the
unexpected-inflation equation (5.68): IS curve, Phillips curve, debt flow and expectations
hypothesis. -/
def RedCore (P : PolicyRules.Params) (ui us x p q v : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t = 𝔼.E t (x (t + 1)) - P.sigma • (PolicyRules.iRule P x p ui t -
    𝔼.E t (p (t + 1)))) ∧
  (∀ t, p t = P.beta • 𝔼.E t (p (t + 1)) + P.kappa • x t) ∧
  (∀ t, P.rho • v (t + 1) = v t + PolicyRules.rnNext P q t - p (t + 1) -
    PolicyRules.sNext P x p v us t) ∧
  (∀ t, 𝔼.E t (PolicyRules.rnNext P q t) = PolicyRules.iRule P x p ui t)

/-- Cochrane (2023), eqs. (5.64)–(5.73), pp. 148–149: the reduced model is its core plus the
unexpected-inflation equation (5.68). -/
theorem redSys_iff_core (P : PolicyRules.Params) (ei es ui us x p q v : ℕ → Ω → ℝ) :
    PolicyRules.RedSys 𝔼 P ei es ui us x p q v ↔ RedCore 𝔼 P ui us x p q v ∧
      ∀ t, SharedTools.innov 𝔼 t (p (t + 1)) = -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1) := by
  unfold PolicyRules.RedSys RedCore
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h4, h5⟩, h3⟩
  · rintro ⟨⟨h1, h2, h4, h5⟩, h3⟩
    exact ⟨h1, h2, h3, h4, h5⟩

/-- Cochrane (2023), §§5.2, 5.5: at the identified parameters, the core of the reduced model is
the new-Keynesian model with rate `u_i`, the long-term-debt flow with surplus `u_s` and return
`ω̃ q_{t+1} − q_t`, and the expectations hypothesis. -/
theorem redCore_idParams (σ β κ ρ om ηi ηs bS bI : ℝ) (ui us x p q v : ℕ → Ω → ℝ) :
    RedCore 𝔼 (idParams σ β κ ρ om ηi ηs bS bI) ui us x p q v ↔
      NKModel.NK 𝔼 σ β κ ui x p ∧
      (∀ t, ρ • v (t + 1) = v t + (om • q (t + 1) - q t) - p (t + 1) - us (t + 1)) ∧
      ∀ t, 𝔼.E t (om • q (t + 1) - q t) = ui t := by
  unfold RedCore NKModel.NK NKModel.IS NKModel.PC
  simp only [iRule_idParams, sNext_idParams, rnNext_idParams]
  exact and_assoc.symm

/-- Cochrane (2023), eqs. (5.17)–(5.21), p. 127, and (5.64)–(5.73), pp. 148–149: **the
long-term-debt model is the reduced model with rules switched off.** For every rate `u_i`,
surplus `u_s`, pre-sample values and paths, `LongTermDebt.LTD` with weight `ω̃` holds iff the
core of the reduced model holds at `idParams σ β κ ρ ω̃ …`, the returns are those of (5.21),
and the date-0 flow holds. -/
theorem ltd_iff_redCore (σ β κ ρ om ηi ηs bS bI : ℝ) (ui us : ℕ → Ω → ℝ) (vm1 qm1 : Ω → ℝ)
    (x p v q rn : ℕ → Ω → ℝ) :
    LongTermDebt.LTD 𝔼 σ β κ ρ om ui us vm1 qm1 x p v q rn ↔
      RedCore 𝔼 (idParams σ β κ ρ om ηi ηs bS bI) ui us x p q v ∧
      rn = LongTermDebt.rnOf om q qm1 ∧ ρ • v 0 = vm1 + rn 0 - p 0 - us 0 := by
  rw [redCore_idParams]
  constructor
  · rintro ⟨hnk, hfl, h0, heh, h21, h21'⟩
    have hrn : rn = LongTermDebt.rnOf om q qm1 := by
      funext t
      cases t with
      | zero => exact h21'
      | succ t => exact h21 t
    refine ⟨⟨hnk, fun t => ?_, fun t => ?_⟩, hrn, h0⟩
    · rw [hfl t, h21 t]
    · rw [← h21 t]
      exact heh t
  · rintro ⟨⟨hnk, hfl, heh⟩, hrn, h0⟩
    subst hrn
    exact ⟨hnk, hfl, h0, heh, fun _ => rfl, rfl⟩

/-! ### Solutions -/

/-- Cochrane (2023), pp. 127–128: an equilibrium of the long-term-debt model — a solution of
(5.17)–(5.21) with the returns of (5.21), with adapted and bounded output, inflation, bond
prices and debt. -/
def LTDEquil (σ β κ ρ om : ℝ) (i s : ℕ → Ω → ℝ) (vm1 qm1 : Ω → ℝ) (x π v q : ℕ → Ω → ℝ) :
    Prop :=
  LongTermDebt.LTD 𝔼 σ β κ ρ om i s vm1 qm1 x π v q (LongTermDebt.rnOf om q qm1) ∧
  𝔼.Adapted x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted q ∧ 𝔼.Adapted v ∧
  BoundedProc x ∧ BoundedProc π ∧ BoundedProc q ∧ BoundedProc v

/-- Cochrane (2023), p. 127: the pre-sample debt for which the date-0 flow of §5.2 holds with
initial inflation `π_0 = p0`, initial debt `v_0 = v0` and pre-sample bond price `q_{−1}`,
`v_{−1} = ρ v_0 − (ω̃ q_0 − q_{−1}) + π_0 + s̃_0`. -/
def vm1Of (ρ om p0 v0 : ℝ) (q us : ℕ → Ω → ℝ) (qm1 : Ω → ℝ) : Ω → ℝ :=
  fun w => ρ * v0 - (om * q 0 w - qm1 w) + p0 + us 0 w

/-- Cochrane (2023), §§5.2, 5.5, pp. 127–129, 147–149: **equilibria agree.** For any pre-sample
bond price `q_{−1}`, `(x, π, q, v)` is an equilibrium of the reduced model at the identified
parameters with initial values `(π_0, v_0) = (p0, v0)` iff it is a long-term-debt equilibrium
with rate `u_i`, surplus `u_s` and pre-sample debt `vm1Of`, whose initial values are the
constants `p0`, `v0` and whose unexpected inflation is (5.68). -/
theorem redEquil_iff_ltdEquil (σ β κ ρ om ηi ηs bS bI : ℝ) (ei es ui us : ℕ → Ω → ℝ)
    (p0 v0 : ℝ) (qm1 : Ω → ℝ) (x p q v : ℕ → Ω → ℝ) :
    PolicyRules.RedEquil 𝔼 (idParams σ β κ ρ om ηi ηs bS bI) ei es ui us p0 v0 x p q v ↔
      LTDEquil 𝔼 σ β κ ρ om ui us (vm1Of ρ om p0 v0 q us qm1) qm1 x p v q ∧
      p 0 = (fun _ => p0) ∧ v 0 = (fun _ => v0) ∧
      ∀ t, SharedTools.innov 𝔼 t (p (t + 1)) = -(bS • es (t + 1)) - bI • ei (t + 1) := by
  have h0 : p 0 = (fun _ => p0) → v 0 = (fun _ => v0) →
      ρ • v 0 = vm1Of ρ om p0 v0 q us qm1 + LongTermDebt.rnOf om q qm1 0 - p 0 - us 0 := by
    intro hp hv
    rw [hp, hv]
    funext w
    simp only [vm1Of, LongTermDebt.rnOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  unfold PolicyRules.RedEquil LTDEquil
  rw [redSys_iff_core, ltd_iff_redCore 𝔼 σ β κ ρ om ηi ηs bS bI]
  constructor
  · rintro ⟨⟨hc, hinn⟩, hxa, hpa, hqa, hva, hxb, hpb, hqb, hvb, hp, hv⟩
    exact ⟨⟨⟨hc, rfl, h0 hp hv⟩, hxa, hpa, hqa, hva, hxb, hpb, hqb, hvb⟩, hp, hv, hinn⟩
  · rintro ⟨⟨⟨hc, _, _⟩, hxa, hpa, hqa, hva, hxb, hpb, hqb, hvb⟩, hp, hv, hinn⟩
    exact ⟨⟨hc, hinn⟩, hxa, hpa, hqa, hva, hxb, hpb, hqb, hvb, hp, hv⟩

/-- Cochrane (2023), p. 128 with §5.5: under the hypotheses of `LongTermDebt.ltd_determinate`
(`0 < ρ < 1`, `0 ≤ ω̃ < 1`, bounded adapted rate and surplus, a bounded date-0 pre-sample bond
price), an equilibrium of the reduced model at the identified parameters is **the** long-term-debt
equilibrium with pre-sample debt `vm1Of`: every solution of (5.17)–(5.21) with that pre-sample
debt, adapted bounded bond prices and bounded inflation and debt coincides with it. -/
theorem redEquil_eq_ltd {σ β κ ρ om ηi ηs bS bI Mi Ms Mq : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (huib : ∀ t w, |ui t w| ≤ Mi)
    (hus : 𝔼.Adapted us) (husb : ∀ t w, |us t w| ≤ Ms) {qm1 : Ω → ℝ} (hq0 : 𝔼.E 0 qm1 = qm1)
    (hqb : ∀ w, |qm1 w| ≤ Mq) {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ}
    (h : PolicyRules.RedEquil 𝔼 (idParams σ β κ ρ om ηi ηs bS bI) ei es ui us p0 v0 x p q v)
    {x' p' v' q' rn' : ℕ → Ω → ℝ}
    (h' : LongTermDebt.LTD 𝔼 σ β κ ρ om ui us (vm1Of ρ om p0 v0 q us qm1) qm1 x' p' v' q' rn')
    (hqa' : 𝔼.Adapted q') (hpb' : BoundedProc p') (hvb' : BoundedProc v')
    (hqb' : BoundedProc q') :
    x' = x ∧ p' = p ∧ v' = v ∧ q' = q ∧ rn' = LongTermDebt.rnOf om q qm1 := by
  obtain ⟨⟨hL, _, _, hqa, _, _, hpb, hqbb, hvb⟩, _, _, _⟩ :=
    (redEquil_iff_ltdEquil 𝔼 σ β κ ρ om ηi ηs bS bI ei es ui us p0 v0 qm1 x p q v).1 h
  obtain ⟨MQ, hMQ⟩ := hqbb
  have hvm : 𝔼.E 0 (vm1Of ρ om p0 v0 q us qm1) = vm1Of ρ om p0 v0 q us qm1 := by
    have he : vm1Of ρ om p0 v0 q us qm1 =
        (fun _ => ρ * v0 + p0) - om • q 0 + qm1 + us 0 := by
      funext w
      simp only [vm1Of, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, map_add, map_add, map_sub, map_smul, 𝔼.const, hqa 0, hq0, hus 0]
  have hvmb : ∀ w, |vm1Of ρ om p0 v0 q us qm1 w| ≤ |ρ * v0 + p0| + om * MQ + Mq + Ms := by
    intro w
    have e : vm1Of ρ om p0 v0 q us qm1 w = (ρ * v0 + p0) - om * q 0 w + qm1 w + us 0 w := by
      simp only [vm1Of]
      ring
    rw [e]
    have h1 : |om * q 0 w| ≤ om * MQ := by
      rw [abs_mul, abs_of_nonneg hom0]
      exact mul_le_mul_of_nonneg_left (hMQ 0 w) hom0
    have := abs_add_le ((ρ * v0 + p0) - om * q 0 w + qm1 w) (us 0 w)
    have := abs_add_le ((ρ * v0 + p0) - om * q 0 w) (qm1 w)
    have := abs_sub (ρ * v0 + p0) (om * q 0 w)
    linarith [hqb w, husb 0 w]
  obtain ⟨x0, p0', v0', q0, rn0, _, huniq⟩ := LongTermDebt.ltd_determinate 𝔼 hσ hκ hβ hρ0 hρ1
    hom0 hom1 hui huib hus husb hvm hvmb hq0 hqb
  obtain ⟨e1, e2, e3, e4, e5⟩ := huniq x' p' v' q' rn' h' hqa' hpb' hvb' hqb'
  obtain ⟨f1, f2, f3, f4, f5⟩ := huniq x p v q _ hL hqa hpb hvb ⟨MQ, hMQ⟩
  exact ⟨e1.trans f1.symm, e2.trans f2.symm, e3.trans f3.symm, e4.trans f4.symm,
    e5.trans f5.symm⟩

/-! ### 2. Relative and absolute time in the continuous-time transversality condition -/

/-- Cochrane (2023), (5.44), p. 140 and (5.95), p. 165: the relative-time discounted value is
the absolute-time one rescaled, `e^{−aT} v_{t+T} = e^{at} (e^{−a(t+T)} v_{t+T})`. -/
theorem tvc_rel_eq (a t T : ℝ) (v : ℝ → ℝ) :
    Real.exp (-a * T) * v (t + T) =
      Real.exp (a * t) * (Real.exp (-(a * (t + T))) * v (t + T)) := by
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), (5.44) and (5.95): **the change of variables `T ↦ t + T` in the
transversality condition**: `e^{−aT} v_{t+T} → 0` (NonlinearCT's form) iff `e^{−aT} v_T → 0`
(CTSimple's form). -/
theorem tvc_rel_iff_abs (a t : ℝ) (v : ℝ → ℝ) :
    Tendsto (fun T => Real.exp (-a * T) * v (t + T)) atTop (𝓝 0) ↔
      Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 0) := by
  have hs : Tendsto (fun T : ℝ => t + T) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  have hs' : Tendsto (fun T : ℝ => -t + T) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  constructor
  · intro h
    have h2 := (h.comp hs').const_mul (Real.exp (-(a * t)))
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    simp only [Function.comp_apply]
    rw [tvc_rel_eq a t (-t + T) v, show t + (-t + T) = T by ring, ← mul_assoc, ← Real.exp_add]
    simp
  · intro h
    have h2 := (h.comp hs).const_mul (Real.exp (a * t))
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    simp only [Function.comp_apply]
    rw [tvc_rel_eq a t T v]

/-- Cochrane (2023), (5.44) and (5.95): the change of variables in the integrability
hypothesis, `e^{−aτ} f_{t+τ}` integrable on `(0, ∞)` iff `e^{−aτ} f_τ` integrable on `(t, ∞)`. -/
theorem integrable_rel_iff_abs (a t : ℝ) (f : ℝ → ℝ) :
    IntegrableOn (fun τ => Real.exp (-a * τ) * f (t + τ)) (Set.Ioi 0) ↔
      IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t) := by
  have he : (fun τ => Real.exp (-a * τ) * f (t + τ)) =
      fun τ => Real.exp (a * t) * ((fun τ => Real.exp (-(a * τ)) * f τ) ∘ (t + ·)) τ := by
    funext τ
    simp only [Function.comp_apply]
    exact tvc_rel_eq a t τ f
  have hpre : (t + ·) ⁻¹' Set.Ioi t = Set.Ioi (0 : ℝ) := by
    ext τ
    simp
  rw [he, IntegrableOn, integrable_const_mul_iff (Real.exp_pos _).ne'.isUnit, ← IntegrableOn,
    ← hpre]
  exact (measurePreserving_add_left volume t).integrableOn_comp_preimage
    (measurableEmbedding_addLeft t)

/-- Cochrane (2023), (5.44) and (5.95): the two valuation integrals are the same number, and
equal `e^{at} ∫_t^∞ e^{−aτ} f_τ dτ` in absolute time. -/
theorem valuation_rel_eq (a t : ℝ) (f : ℝ → ℝ) :
    (∫ τ in Set.Ioi 0, Real.exp (-a * τ) * f (t + τ)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ) ∧
    (∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ)) =
      Real.exp (a * t) * ∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * f τ :=
  ⟨by simp only [neg_mul], CTSimple.integral_exp_shift a t f⟩

/-- Cochrane (2023), (5.95), p. 165: the statement of `CTSimple.tvc_iff_forward` (absolute time;
continuity on `[t, ∞)`, derivative on `(t, ∞)`). -/
def ForwardStmt : Prop :=
  ∀ (v f : ℝ → ℝ) (a t : ℝ), ContinuousOn v (Set.Ici t) →
    (∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ) →
    IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t) →
    (Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ))

/-- Cochrane (2023), (5.95), p. 165: `ForwardStmt` restricted to forcing continuous on
`[t, ∞)` (the class on which `NonlinearCT`'s hypotheses can be met). -/
def ForwardContStmt : Prop :=
  ∀ (v f : ℝ → ℝ) (a t : ℝ), ContinuousOn v (Set.Ici t) → ContinuousOn f (Set.Ici t) →
    (∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ) →
    IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t) →
    (Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ))

/-- Cochrane (2023), (5.44), p. 140: the statement of `NonlinearCT.tvc_iff_integral` (relative
time from a valuation date `t ≥ 0`; continuous surplus; flow with a derivative at every
`τ ≥ 0`). -/
def IntegralStmt : Prop :=
  ∀ (r : ℝ) (s b : ℝ → ℝ), ContinuousOn s (Set.Ici 0) → NonlinearCT.Flow r s b →
    ∀ t : ℝ, 0 ≤ t →
    IntegrableOn (fun τ => Real.exp (-r * τ) * s (t + τ)) (Set.Ioi 0) →
    (Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) ↔
      b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ))

/-- Cochrane (2023), (5.44) and (5.95): **NonlinearCT's form follows from CTSimple's** by the
change of variables, and without the continuity of the surplus: for a flow `db/dt = rb − s`
on `[0, ∞)`, `t ≥ 0` and integrable discounted surplus, the TVC holds iff
`b_t = ∫_0^∞ e^{−rτ} s_{t+τ} dτ`. -/
theorem integral_of_forward (H : ForwardStmt) {r : ℝ} {s b : ℝ → ℝ}
    (hb : NonlinearCT.Flow r s b) {t : ℝ} (ht : 0 ≤ t)
    (hint : IntegrableOn (fun τ => Real.exp (-r * τ) * s (t + τ)) (Set.Ioi 0)) :
    Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) ↔
      b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ) := by
  have hc : ContinuousOn b (Set.Ici t) := fun τ hτ =>
    (hb τ (le_trans ht hτ)).continuousAt.continuousWithinAt
  have hd : ∀ τ, t < τ → HasDerivAt b (r * b τ - s τ) τ := fun τ hτ => hb τ (by linarith)
  rw [tvc_rel_iff_abs, H b s r t hc hd ((integrable_rel_iff_abs r t s).1 hint),
    (valuation_rel_eq r t s).1]

/-- Cochrane (2023), (5.44) and (5.95): `ForwardStmt` implies `IntegralStmt`. -/
theorem integralStmt_of_forwardStmt (H : ForwardStmt) : IntegralStmt :=
  fun _ _ _ _ hb _ ht hint => integral_of_forward H hb ht hint

/-- Cochrane (2023), (5.44), p. 140: `NonlinearCT.tvc_iff_integral` re-derived from
`CTSimple.tvc_iff_forward`; the continuity of `s` is not needed. -/
theorem tvc_iff_integral_of_forward {r : ℝ} {s b : ℝ → ℝ} (hb : NonlinearCT.Flow r s b)
    {t : ℝ} (ht : 0 ≤ t)
    (hint : IntegrableOn (fun τ => Real.exp (-r * τ) * s (t + τ)) (Set.Ioi 0)) :
    Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) ↔
      b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ) :=
  integral_of_forward (fun _ _ _ _ hc hd hi => CTSimple.tvc_iff_forward hc hd hi) hb ht hint

/-- Cochrane (2023), (5.95), p. 165: the shifted path used to put CTSimple's data into
NonlinearCT's form: `v_{t+u}` for `u ≥ 0`, extended linearly with slope `a v_t − f_t` to
the left. -/
noncomputable def shiftExt (v f : ℝ → ℝ) (a t : ℝ) (u : ℝ) : ℝ :=
  if 0 ≤ u then v (t + u) else v t + u * (a * v t - f t)

/-- Cochrane (2023), (5.95), p. 165: for `v` continuous on `[t, ∞)` with derivative
`a v − f` on `(t, ∞)` and `f` continuous on `[t, ∞)`, the shifted and extended path satisfies
NonlinearCT's flow `db/du = a b − f_{t+u}` at every `u ≥ 0` (two-sided derivative at `u = 0`). -/
theorem shiftExt_flow {v f : ℝ → ℝ} {a t : ℝ} (hc : ContinuousOn v (Set.Ici t))
    (hf : ContinuousOn f (Set.Ici t)) (hd : ∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ) :
    NonlinearCT.Flow a (fun u => f (t + u)) (shiftExt v f a t) := by
  have hw : ∀ u, 0 < u → HasDerivAt (fun u => v (t + u)) (a * v (t + u) - f (t + u)) u :=
    fun u hu => HasDerivAt.comp_const_add t u (hd (t + u) (by linarith))
  have hmaps : Set.MapsTo (fun u : ℝ => t + u) (Set.Ici 0) (Set.Ici t) := fun u hu => by
    simp only [Set.mem_Ici] at hu ⊢
    linarith
  have hvc : ContinuousWithinAt (fun u => v (t + u)) (Set.Ici 0) 0 := by
    have h0 : ContinuousWithinAt v (Set.Ici t) (t + 0) := by
      rw [add_zero]
      exact hc t (Set.mem_Ici.mpr le_rfl)
    exact h0.comp (continuous_const_add t).continuousWithinAt hmaps
  have hfc : ContinuousWithinAt (fun u => f (t + u)) (Set.Ici 0) 0 := by
    have h0 : ContinuousWithinAt f (Set.Ici t) (t + 0) := by
      rw [add_zero]
      exact hf t (Set.mem_Ici.mpr le_rfl)
    exact h0.comp (continuous_const_add t).continuousWithinAt hmaps
  intro u hu
  have hb_eq : shiftExt v f a t u = v (t + u) := by simp [shiftExt, hu]
  rcases hu.lt_or_eq with hu | hu
  · have hev : shiftExt v f a t =ᶠ[𝓝 u] fun u => v (t + u) := by
      filter_upwards [lt_mem_nhds hu] with y hy
      simp [shiftExt, hy.le]
    rw [hb_eq]
    exact (hw u hu).congr_of_eventuallyEq hev
  · subst hu
    rw [hb_eq]
    simp only [add_zero]
    have hR : HasDerivWithinAt (fun u => v (t + u)) (a * v t - f t) (Set.Ici 0) 0 := by
      refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0) ?_ ?_
        self_mem_nhdsWithin ?_
      · exact fun y hy => (hw y hy).differentiableAt.differentiableWithinAt
      · exact hvc.mono Set.Ioi_subset_Ici_self
      · have hlim : Tendsto (fun u => a * v (t + u) - f (t + u)) (𝓝[>] 0)
            (𝓝 (a * v t - f t)) := by
          have h1 := ((hvc.const_mul a).sub hfc).tendsto
          have h2 : Tendsto ((fun x => a * v (t + x)) - fun u => f (t + u)) (𝓝[>] 0)
              (𝓝 (a * v t - f t)) := by
            simpa using h1.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
          exact h2
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hw y hy).deriv.symm
    have hR' : HasDerivWithinAt (shiftExt v f a t) (a * v t - f t) (Set.Ici 0) 0 :=
      hR.congr (fun y hy => by simp [shiftExt, Set.mem_Ici.mp hy])
        (by simp [shiftExt])
    have hlin : HasDerivAt (fun u => v t + u * (a * v t - f t)) (a * v t - f t) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a * v t - f t)).const_add (v t)
    have hL : HasDerivWithinAt (shiftExt v f a t) (a * v t - f t) (Set.Iic 0) 0 :=
      hlin.hasDerivWithinAt.congr (fun y hy => by
        rcases (Set.mem_Iic.mp hy).lt_or_eq with h | h
        · simp [shiftExt, not_le.mpr h]
        · subst h
          simp [shiftExt]) (by simp [shiftExt])
    have := hL.union hR'
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- Cochrane (2023), (5.44) and (5.95): **CTSimple's form follows from NonlinearCT's** for
forcing continuous on `[t, ∞)`: shift the origin to the valuation date (`shiftExt`), apply the
relative-time statement at date `0`, and change variables back. -/
theorem forwardContStmt_of_integralStmt (H : IntegralStmt) : ForwardContStmt := by
  intro v f a t hc hf hd hint
  have hflow := shiftExt_flow hc hf hd
  have hs : ContinuousOn (fun u => f (t + u)) (Set.Ici 0) :=
    hf.comp (continuous_const_add t).continuousOn fun u hu => by
      simp only [Set.mem_Ici] at hu ⊢
      linarith
  have hint' : IntegrableOn (fun τ => Real.exp (-a * τ) * (fun u => f (t + u)) (0 + τ))
      (Set.Ioi 0) := by
    simp only [zero_add]
    exact (integrable_rel_iff_abs a t f).2 hint
  have key := H a (fun u => f (t + u)) (shiftExt v f a t) hs hflow 0 le_rfl hint'
  have hb0 : shiftExt v f a t 0 = v t := by simp [shiftExt]
  have hev : (fun T => Real.exp (-a * T) * shiftExt v f a t (0 + T)) =ᶠ[atTop]
      fun T => Real.exp (-a * T) * v (t + T) := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    simp [shiftExt, hT]
  rw [tendsto_congr' hev, hb0] at key
  simp only [zero_add] at key
  rw [← tvc_rel_iff_abs, key, (valuation_rel_eq a t f).1]

/-- Cochrane (2023), (5.95), p. 165: `CTSimple.tvc_iff_forward` for continuous forcing,
re-derived from `NonlinearCT.tvc_iff_integral`. -/
theorem tvc_iff_forward_of_integral {v f : ℝ → ℝ} {a t : ℝ} (hc : ContinuousOn v (Set.Ici t))
    (hf : ContinuousOn f (Set.Ici t)) (hd : ∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(a * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * f (t + τ) :=
  forwardContStmt_of_integralStmt
    (fun _ _ _ hs hb _ ht hi => NonlinearCT.tvc_iff_integral hs hb ht hi) v f a t hc hf hd hint

/-- Cochrane (2023), (5.95), p. 165: CTSimple's hypotheses do not force the forcing to be
continuous on `[t, ∞)` (its value at `t` is unrestricted): `v ≡ 0`, `f = 𝟙_{0}`, `a = 0`,
`t = 0` satisfy them, while `f` is not continuous on `[0, ∞)`. -/
theorem forward_hyps_discontinuous :
    ∃ (v f : ℝ → ℝ) (a t : ℝ), ContinuousOn v (Set.Ici t) ∧
      (∀ τ, t < τ → HasDerivAt v (a * v τ - f τ) τ) ∧
      IntegrableOn (fun τ => Real.exp (-(a * τ)) * f τ) (Set.Ioi t) ∧
      ¬ ContinuousOn f (Set.Ici t) := by
  refine ⟨fun _ => 0, fun τ => if τ = 0 then 1 else 0, 0, 0, continuousOn_const,
    fun τ hτ => ?_, ?_, fun h => ?_⟩
  · simpa [hτ.ne'] using hasDerivAt_const τ (0 : ℝ)
  · refine (integrableOn_zero).congr_fun (fun τ hτ => ?_) measurableSet_Ioi
    simp [(Set.mem_Ioi.mp hτ).ne']
  · have h0 := (h 0 (Set.mem_Ici.mpr le_rfl)).tendsto
    have h1 : Tendsto (fun τ : ℝ => if τ = 0 then (1 : ℝ) else 0) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with y hy
        simp [(Set.mem_Ioi.mp hy).ne'])
    have h2 := h0.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    simp only [↓reduceIte] at h2
    have := tendsto_nhds_unique h2 h1
    norm_num at this

end Cochrane.StickyPriceFiscal.LinksTidy
