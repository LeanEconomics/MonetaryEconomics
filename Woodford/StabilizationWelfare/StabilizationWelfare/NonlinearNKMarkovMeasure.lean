/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovLinks
import StabilizationWelfare.ExpectationsMeasureIID

/-!
# The Markov equilibrium on a genuine probability space

Woodford (2003), *Interest and Prices*, Chapter 6, §1 and §5 (pp. 383–392, 455–463), Chapter 4,
(2.7)–(2.8), and Appendix A.3: the exact equilibrium conditions hold with conditional expectations
`E_t = μ[· | 𝓕_t]` (Mathlib's `condExp`, the copied measure core `ExpectationsMeasure`), almost
surely, along any adapted realisation of the exogenous Markov chain.

## Main results

* `MeasMarkovProp`: the chain's transition matrix gives the conditional expectations,
  `E_t[h(s_{t+1})] = (Ph)(s_t)` a.s.
* `meas_euler`, `meas_recF`, `meas_recK`: along a Markov equilibrium the Euler equation with the
  rule and the Calvo recursions for `F` and `K` hold a.s. in the book's level form
  `e^{F̂_t} = (1−αβ)e^{f̂_t} + αβE_t[e^{(θ−1)π_{t+1} + F̂_{t+1}}]`; `meas_priceIndex` holds surely;
  `adapted_proc`: the equilibrium processes are adapted when the shock process is.
* Link to the core (bridge (b), `ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`):
  `markovProp_of_meas` turns `MeasMarkovProp` on a finite fully supported space into the core
  `NonlinearNKMarkovLinks.MarkovProp`, and `calvoAS_of_meas` then gives the core statement
  `LargeDistortions.CalvoModel.CalvoAS` (the measure results specialise to the core ones).
* A genuine instance: the fair-coin chain (`coinChain`, `coinState`) built on the i.i.d.
  infinite product `ExpectationsMeasureIID.iidSystem coin`, where every history has probability
  zero (not finitely supported, so outside the core `ExpectationSystem`):
  `coin_measMarkovProp` and `coin_markov_equilibrium` (existence of the Markov equilibrium, the
  a.s. equilibrium conditions with `condExp`, adaptedness, and the Layer-B orders).
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovLinks ExpectationsMeasure

variable {p : Par} {S : Type*} [Fintype S]

/-- Woodford (2003), App. A.3, on a genuine probability space: conditional expectations of
functions of next period's exogenous state follow the transition matrix almost surely,
`μ[h(s_{t+1}) | 𝓕_t] = ∑_{s′} P(s_t, s′)h(s′)` a.s. -/
def MeasMarkovProp {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
    (P : S → S → ℝ) (sh : ℕ → Ω → S) : Prop :=
  ∀ t (h : S → ℝ), E.E t (fun ω => h (sh (t + 1) ω)) =ᵐ[E.μ] fun ω => chainOp P h (sh t ω)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) (**the Euler equation with the rule, almost surely**):
`E_t[e^{−σ(Ŷ_{t+1} − ĉ_{t+1}) − π_{t+1}}] = e^{−(φ_π π_t + φ_y Ŷ_t + ν_t + σ(Ŷ_t − ĉ_t))}` a.s. -/
theorem meas_euler (E : MeasExpectationSystem Ω) {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ)
    (w : S → Fin 4 → ℝ) (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S)
    (hM : MeasMarkovProp E P sh) (t : ℕ) :
    E.E t (fun ω => Real.exp (-(p.σ * (w (sh (t + 1) ω) 0 - ε * ξ (sh (t + 1) ω) 1)) -
        w (sh (t + 1) ω) 1)) =ᵐ[E.μ]
      fun ω => Real.exp (-(p.φ * w (sh t ω) 1 + p.φy * w (sh t ω) 0 + ε * ξ (sh t ω) 0 +
        p.σ * (w (sh t ω) 0 - ε * ξ (sh t ω) 1))) := by
  filter_upwards [hM t (fun s' => Real.exp (-(p.σ * (w s' 0 - ε * ξ s' 1)) - w s' 1))]
    with ω hω
  rw [hω]
  have h := eqm_comp hw (sh t ω) 0
  simp only [Qmap, Nmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h
  simp only [chainOp, LinearMap.coe_mk, AddHom.coe_mk]
  linear_combination h

/-- Woodford (2003), Ch. 3 and §5 (**the recursion for `F`, almost surely, in levels**):
`e^{F̂_t} = (1−αβ)e^{f̂_t} + αβE_t[e^{(θ−1)π_{t+1} + F̂_{t+1}}]` a.s. -/
theorem meas_recF (E : MeasExpectationSystem Ω) {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ)
    (w : S → Fin 4 → ℝ) (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S)
    (hM : MeasMarkovProp E P sh) (t : ℕ) :
    (fun ω => Real.exp (w (sh t ω) 2)) =ᵐ[E.μ] fun ω =>
      (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w (sh t ω) 0 + p.σ * (ε * ξ (sh t ω) 1) +
        ε * ξ (sh t ω) 2) + p.α * p.β * E.E t (fun ω =>
          Real.exp ((p.θ - 1) * w (sh (t + 1) ω) 1 + w (sh (t + 1) ω) 2)) ω := by
  filter_upwards [hM t (fun s' => Real.exp ((p.θ - 1) * w s' 1 + w s' 2))] with ω hω
  rw [hω]
  have h := eqm_comp hw (sh t ω) 1
  have hS1 : ∑ s', P (sh t ω) s' * Nmap p (ε • ξ s', w s') 1 =
      -(p.α * p.β) * ∑ s', P (sh t ω) s' * Real.exp ((p.θ - 1) * w s' 1 + w s' 2) := by
    simp only [Nmap, Matrix.cons_val]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hS1] at h
  simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h
  simp only [chainOp, LinearMap.coe_mk, AddHom.coe_mk]
  linear_combination h

/-- Woodford (2003), Ch. 3 and §5 (**the recursion for `K`, almost surely, in levels**):
`e^{K̂_t} = (1−αβ)e^{k̂_t} + αβE_t[e^{θ(1+ω)π_{t+1} + K̂_{t+1}}]` a.s. -/
theorem meas_recK (E : MeasExpectationSystem Ω) {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ)
    (w : S → Fin 4 → ℝ) (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S)
    (hM : MeasMarkovProp E P sh) (t : ℕ) :
    (fun ω => Real.exp (w (sh t ω) 3)) =ᵐ[E.μ] fun ω =>
      (1 - p.α * p.β) * Real.exp ((1 + p.ω) * w (sh t ω) 0 - p.ω * (ε * ξ (sh t ω) 3) +
        ε * ξ (sh t ω) 4) + p.α * p.β * E.E t (fun ω =>
          Real.exp (p.θ * (1 + p.ω) * w (sh (t + 1) ω) 1 + w (sh (t + 1) ω) 3)) ω := by
  filter_upwards [hM t (fun s' => Real.exp (p.θ * (1 + p.ω) * w s' 1 + w s' 3))] with ω hω
  rw [hω]
  have h := eqm_comp hw (sh t ω) 2
  have hS1 : ∑ s', P (sh t ω) s' * Nmap p (ε • ξ s', w s') 2 =
      -(p.α * p.β) * ∑ s', P (sh t ω) s' * Real.exp (p.θ * (1 + p.ω) * w s' 1 + w s' 3) := by
    simp only [Nmap, Matrix.cons_val]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hS1] at h
  simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h
  simp only [chainOp, LinearMap.coe_mk, AddHom.coe_mk]
  linear_combination h

omit [MeasurableSpace Ω] in
/-- Woodford (2003), §5: the price index with the optimal reset price holds at every state
(surely): `α(e^{(θ−1)π_t} − 1) + (1−α)(e^{−(θ−1)x̂_t} − 1) = 0`, `x̂ = (K̂ − F̂)/(1+ωθ)`. -/
theorem meas_priceIndex {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ)
    (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S) (t : ℕ) (ω : Ω) :
    p.α * (Real.exp ((p.θ - 1) * w (sh t ω) 1) - 1) + (1 - p.α) *
      (Real.exp (-((p.θ - 1) * ((w (sh t ω) 3 - w (sh t ω) 2) / p.c0))) - 1) = 0 := by
  have h := eqm_comp hw (sh t ω) 3
  simp only [Qmap, Nmap, Matrix.cons_val, mul_zero, Finset.sum_const_zero, add_zero] at h
  rw [mul_div_assoc] at h
  exact h

omit [Fintype S] in
/-- Woodford (2003), App. A.3: if the exogenous state is adapted then so is every equilibrium
process `g(s_t)` (a discrete state space makes every `g` measurable). -/
theorem adapted_proc [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (E : MeasExpectationSystem Ω) (sh : ℕ → Ω → S) (hsh : ∀ t, Measurable[E.𝓕 t] (sh t))
    (g : S → ℝ) : StronglyAdapted E.𝓕 (fun t ω => g (sh t ω)) := fun t =>
  ((Measurable.of_discrete (f := g)).comp (hsh t)).stronglyMeasurable

/-! ## The link to the core expectation system -/

/-- Bridge (b) (`MeasExpectationSystem.toExpectationSystem`): on a finite discrete state space
with full support, the almost-sure Markov property is the core `MarkovProp` of the associated
core `ExpectationSystem`. -/
theorem markovProp_of_meas [Finite Ω] [DiscreteMeasurableSpace Ω] (E : MeasExpectationSystem Ω)
    (hfull : ∀ ω, E.μ {ω} ≠ 0) {P : S → S → ℝ} {sh : ℕ → Ω → S} (hM : MeasMarkovProp E P sh) :
    MarkovProp (E.toExpectationSystem hfull) P sh := fun t h => by
  rw [MeasExpectationSystem.toExpectationSystem_E]
  exact E.eq_of_ae_eq hfull (hM t h)

/-- Woodford (2003), §5 (**the measure-theoretic results specialise to the core ones**): on a
finite fully supported probability space, a Markov equilibrium along a shock process with the
almost-sure Markov property satisfies the core exact Calvo model
`LargeDistortions.CalvoModel.CalvoAS` for the core system of bridge (b). -/
theorem calvoAS_of_meas (hp : p.Std) [Finite Ω] [DiscreteMeasurableSpace Ω]
    (E : MeasExpectationSystem Ω) (hfull : ∀ ω, E.μ {ω} ≠ 0) {P : S → S → ℝ}
    (hP : Stochastic P) (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ)
    (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S) (hM : MeasMarkovProp E P sh) :
    LargeDistortions.CalvoModel.CalvoAS (E.toExpectationSystem hfull) p.α p.β p.θ p.ω p.σ 1
      (fun t ω => w (sh t ω) 1) (fun t ω => (w (sh t ω) 3 - w (sh t ω) 2) / p.c0)
      (fun t ω => w (sh t ω) 2) (fun t ω => w (sh t ω) 3)
      (fun t ω => (1 - p.σ) * w (sh t ω) 0 + p.σ * (ε * ξ (sh t ω) 1) + ε * ξ (sh t ω) 2)
      (fun t ω => (1 + p.ω) * w (sh t ω) 0 - p.ω * (ε * ξ (sh t ω) 3) + ε * ξ (sh t ω) 4)
      (fun t ω => w (sh t ω) 0) (fun _ _ => 0) (fun t ω => ε * ξ (sh t ω) 1)
      (fun t ω => ε * ξ (sh t ω) 3) (fun t ω => ε * ξ (sh t ω) 4)
      (fun t ω => ε * ξ (sh t ω) 2) :=
  calvoAS_of_markov hp _ hP ξ ε w hw sh (markovProp_of_meas E hfull hM)

/-- Bridge consistency: on a finite fully supported space the core `F` recursion obtained from
`calvoAS_of_meas` and the almost-sure level recursion `meas_recF` are the same statement, since
`E_t` is the same function (`MeasExpectationSystem.toExpectationSystem_E`) and a.s. equality is
equality (`MeasExpectationSystem.eq_of_ae_eq`). -/
theorem recF_agree [Finite Ω] [DiscreteMeasurableSpace Ω] (E : MeasExpectationSystem Ω)
    (hfull : ∀ ω, E.μ {ω} ≠ 0) {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ)
    (w : S → Fin 4 → ℝ) (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S)
    (hM : MeasMarkovProp E P sh) (t : ℕ) :
    (fun ω => Real.exp (w (sh t ω) 2)) = fun ω =>
      (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w (sh t ω) 0 + p.σ * (ε * ξ (sh t ω) 1) +
        ε * ξ (sh t ω) 2) + p.α * p.β * (E.toExpectationSystem hfull).E t (fun ω =>
          Real.exp ((p.θ - 1) * w (sh (t + 1) ω) 1 + w (sh (t + 1) ω) 2)) ω :=
  E.eq_of_ae_eq hfull (meas_recF E ξ ε w hw sh hM t)

/-! ## A genuine instance: the fair-coin chain on the i.i.d. product space -/

open ExpectationsMeasureIID

/-- The two-state chain of fair coin flips: `P(s, s′) = 1/2`. -/
noncomputable def coinChain : Fin 2 → Fin 2 → ℝ := fun _ _ => 1 / 2

/-- The exogenous state `s_t = 0` if the date-`t` coin shows `+1`, `1` otherwise. -/
noncomputable def coinState (t : ℕ) (ω : ℕ → ℝ) : Fin 2 := if 0 < ω t then 0 else 1

/-- Woodford (2003), App. A.3: the fair-coin transition matrix is stochastic. -/
theorem coinChain_stochastic : Stochastic coinChain :=
  ⟨fun _ _ => by norm_num [coinChain], fun _ => by simp [coinChain]⟩

/-- Woodford (2003), App. A.3: the coin-state selector `x ↦ 1_{x ≤ 0}` is measurable. -/
theorem measurable_coinSel : Measurable (fun x : ℝ => (if 0 < x then 0 else 1 : Fin 2)) :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

/-- Woodford (2003), App. A.3, on the i.i.d. coin space (`ExpectationsMeasureIID.iidSystem coin`,
`Ω = ℕ → ℝ`): the coin state satisfies the almost-sure Markov property with
`P(s, s′) = 1/2`. -/
theorem coin_measMarkovProp : MeasMarkovProp (iidSystem coin) coinChain coinState := by
  intro t h
  have hf : Measurable (fun x : ℝ => h (if 0 < x then 0 else 1)) :=
    (Measurable.of_discrete (f := h)).comp measurable_coinSel
  have := E_shock_fun coin t hf
  refine this.trans (Eventually.of_forall fun ω => ?_)
  simp only [integral_coin, chainOp, coinChain, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_two]
  norm_num
  ring

/-- The coin state is adapted to the natural filtration. -/
theorem coinState_adapted (t : ℕ) : Measurable[(iidSystem coin).𝓕 t] (coinState t) :=
  measurable_coinSel.comp (measurable_shock coin (le_refl t))

/-- Woodford (2003), Ch. 6, §1, §5 and App. A.3 (**a Markov equilibrium of the exact nonlinear NK
model on a genuine infinite-horizon probability space**). Take the fair-coin chain on the i.i.d.
product `ν^ℕ` (every history has probability zero: not finitely supported). Under the Taylor
principle, for any disturbance pattern `ξ` there are `δ > 0` and a `C²` family of Markov
equilibria `z_ε` (`z₀ = 0`) such that for `|ε| < δ` and every date, along `s_t = coinState t`,
the Euler equation with the rule and the Calvo recursions hold almost surely with Mathlib's
conditional expectations, the price index holds surely, the processes are adapted, and the
Layer-B orders hold uniformly. -/
theorem coin_markov_equilibrium (hp : p.Std) (ξ : Fin 2 → Fin 5 → ℝ) :
    (∀ ω, (iidSystem coin).μ {ω} = 0) ∧
    ∃ δ > 0, ∃ z : ℝ → Fin 2 → Fin 4 → ℝ, z 0 = 0 ∧ ContDiffAt ℝ 2 z 0 ∧
      (∀ ε, |ε| < δ → IsMarkovEqm p (chainOp coinChain) ξ ε (z ε)) ∧
      (∀ ε, |ε| < δ → ∀ t,
        (iidSystem coin).E t (fun ω => Real.exp (-(p.σ * (z ε (coinState (t + 1) ω) 0 -
          ε * ξ (coinState (t + 1) ω) 1)) - z ε (coinState (t + 1) ω) 1)) =ᵐ[(iidSystem coin).μ]
        (fun ω => Real.exp (-(p.φ * z ε (coinState t ω) 1 + p.φy * z ε (coinState t ω) 0 +
          ε * ξ (coinState t ω) 0 + p.σ * (z ε (coinState t ω) 0 - ε * ξ (coinState t ω) 1)))) ∧
        (fun ω => Real.exp (z ε (coinState t ω) 2)) =ᵐ[(iidSystem coin).μ] (fun ω =>
          (1 - p.α * p.β) * Real.exp ((1 - p.σ) * z ε (coinState t ω) 0 +
            p.σ * (ε * ξ (coinState t ω) 1) + ε * ξ (coinState t ω) 2) +
          p.α * p.β * (iidSystem coin).E t (fun ω => Real.exp ((p.θ - 1) *
            z ε (coinState (t + 1) ω) 1 + z ε (coinState (t + 1) ω) 2)) ω) ∧
        (fun ω => Real.exp (z ε (coinState t ω) 3)) =ᵐ[(iidSystem coin).μ] (fun ω =>
          (1 - p.α * p.β) * Real.exp ((1 + p.ω) * z ε (coinState t ω) 0 -
            p.ω * (ε * ξ (coinState t ω) 3) + ε * ξ (coinState t ω) 4) +
          p.α * p.β * (iidSystem coin).E t (fun ω => Real.exp (p.θ * (1 + p.ω) *
            z ε (coinState (t + 1) ω) 1 + z ε (coinState (t + 1) ω) 3)) ω) ∧
        ∀ ω, p.α * (Real.exp ((p.θ - 1) * z ε (coinState t ω) 1) - 1) + (1 - p.α) *
          (Real.exp (-((p.θ - 1) * ((z ε (coinState t ω) 3 - z ε (coinState t ω) 2) /
            p.c0))) - 1) = 0) ∧
      (∀ ε (i : Fin 4), StronglyAdapted (iidSystem coin).𝓕 (fun t ω => z ε (coinState t ω) i)) ∧
      (∀ i : Fin 4, BridgeExtensions.UProc (𝓝 0) (proc z coinState i) (fun ε => ε ^ 1) ∧
        BridgeExtensions.UProc (𝓝 0)
          (fun ε t ω => proc z coinState i ε t ω - ε * deriv z 0 (coinState t ω) i)
          (fun ε => ε ^ 2)) := by
  refine ⟨iid_singleton coin_mean coin_var one_pos, ?_⟩
  obtain ⟨_, _, δ, hδ, z, hz0, hzC, hz, -⟩ := markov_equilibrium hp coinChain_stochastic ξ
  refine ⟨δ, hδ, z, hz0, hzC, fun ε hε => (hz ε hε).1, fun ε hε t => ?_, fun ε i =>
    adapted_proc _ coinState coinState_adapted (fun s => z ε s i), fun i =>
      ⟨uproc_order_one hz0 hzC coinState i, uproc_first_order hz0 hzC coinState i⟩⟩
  have hw := (hz ε hε).1
  exact ⟨meas_euler _ ξ ε (z ε) hw coinState coin_measMarkovProp t,
    meas_recF _ ξ ε (z ε) hw coinState coin_measMarkovProp t,
    meas_recK _ ξ ε (z ε) hw coinState coin_measMarkovProp t,
    fun ω => meas_priceIndex ξ ε (z ε) hw coinState t ω⟩

end Woodford.StabilizationWelfare.NonlinearNKMarkovMeasure
