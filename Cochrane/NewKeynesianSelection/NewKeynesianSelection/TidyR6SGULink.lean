/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6SGUStochasticMeasure
import NewKeynesianSelection.TidyR6StochasticPatches

/-!
# Stochastic uniqueness in the Schmitt-Grohé–Uribe example of §16.10.6

Cochrane (2023), §16.10.6, p. 393: with money in the utility function the dynamics are (16.32),
and "Woodford and Schmitt-Grohé and Uribe give examples of specifications of `u(c, M/P)`" for
which inflationary paths explode. The restated perfect-foresight results
(`SelectionPatches.SGU.sgu_unique_pf_equilibrium`) make `Π*` the unique perfect-foresight
equilibrium satisfying the transversality condition. Woodford (2003, p. 137) claims the same
"even allowing for stochastic equilibria of arbitrary form"; the Woodford Chapter 2 project
(restated here in TidyR6SGUStochastic and TidyR6SGUStochasticMeasure) found the claim false on a
genuine probability space. This module states the result in Cochrane's notation:

* `stochEq1632_iff_stochPath`: with `Φ(Π) = β(1 + φ(Π))` and `k(Π) = λ(φ(Π))`, the stochastic
  (16.32) `E_t[k(Π_{t+1})/Π_{t+1}] = k(Π_t)/Φ(Π_t)`
  (`TidyR6StochasticPatches.StochEq1632`) is the stochastic (4.5) of the restated module.
* `sgu_unique_finiteTree_1632`: on every finite event tree, `Π ≡ Π*` is the unique stochastic
  equilibrium of (16.32) satisfying the transversality condition (global stochastic uniqueness
  holds when information is eventually resolved).
* `sgu_sunspot_1632` (**counterexample**): on the geometric switching-date probability space
  (`Ω = ℕ`, Mathlib's `condExp`), with `θ = Ȳ = 1`, `β = 1/2`, `Π* = 1`, `φ_π = 5/4` (Taylor
  principle and the E5 condition) and `1 < μ̄ < 2`, there is an adapted positive equilibrium of
  (16.32), almost surely, satisfying the transversality condition, with `Π₀ ≠ Π*`. Global
  stochastic uniqueness fails; this is consistent with the Woodford Chapter 2 finding.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6SGULink

open MeasureTheory ProbabilityTheory Filter Topology
open SelectionPatches.SGU TidyR6SGUStochastic TidyR6SGUStochasticMeasure

/-- Cochrane (2023), eq. (16.32), p. 393, in the Schmitt-Grohé–Uribe model: with
`Φ(Π) = β(1 + φ(Π))` and `k(Π) = λ(φ(Π))`, the stochastic (16.32) holds iff
`E_t[B(Π_{t+1})] = A(Π_t)` (the stochastic (4.5) of TidyR6SGUStochastic). -/
theorem stochEq1632_iff_stochPath {Ω : Type*} (𝔼 : ExpectationSystem Ω) {θ Y β Pis φπ : ℝ}
    (hβ : 0 < β) (Pi_ : ℕ → Ω → ℝ) :
    TidyR6StochasticPatches.StochEq1632 𝔼 (fun x => β * (1 + phiSGU β Pis φπ x))
        (fun x => lamSGU θ Y (phiSGU β Pis φπ x)) Pi_ ↔
      ∀ t, 𝔼.E t (fun ω => sguB θ Y β Pis φπ (Pi_ (t + 1) ω)) =
        fun ω => sguA θ Y β Pis φπ (Pi_ t ω) := by
  have hB : ∀ t, (fun ω => sguB θ Y β Pis φπ (Pi_ (t + 1) ω)) =
      β • fun ω => lamSGU θ Y (phiSGU β Pis φπ (Pi_ (t + 1) ω)) / Pi_ (t + 1) ω := by
    intro t; funext ω; simp only [sguB, Pi.smul_apply, smul_eq_mul]; ring
  have hA : ∀ t, (fun ω => sguA θ Y β Pis φπ (Pi_ t ω)) =
      β • fun ω => lamSGU θ Y (phiSGU β Pis φπ (Pi_ t ω)) /
        (β * (1 + phiSGU β Pis φπ (Pi_ t ω))) := by
    intro t; funext ω
    simp only [sguA, Pi.smul_apply, smul_eq_mul]
    rw [← mul_div_assoc, mul_div_mul_left _ _ hβ.ne']
  refine forall_congr' fun t => ?_
  rw [hB, hA, map_smul]
  constructor
  · intro h; rw [h]
  · intro h; exact smul_right_injective _ hβ.ne' h

/-- Cochrane (2023), (16.32), p. 393, global stochastic uniqueness on finite event trees: in the
Schmitt-Grohé–Uribe model (`φ_π > 1`, `Π* > β`, the E5 condition `β + θΠ*(1 − φ_π) > 0`,
liabilities growing at `1 < μ̄ < Π*/β`), on every finite event tree every adapted positive
equilibrium of the stochastic (16.32) with adapted prices `P_{t+1} = Π_{t+1}P_t > 0` satisfying
the transversality condition is `Π ≡ Π*`, and `Π ≡ Π*` is such an equilibrium. -/
theorem sgu_unique_finiteTree_1632 {Ω' : Type*} [Fintype Ω'] [Nonempty Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {θ Y β Pis φπ μ P0 : ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ) (hμ : 1 < μ)
    (hμPis : β * μ < Pis) (hP0 : 0 < P0) {D : ℕ → ℝ} (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    StochTVC T.toExpectationSystem θ Y β Pis φπ (fun _ _ => Pis) (fun t _ => P0 * Pis ^ t) D ∧
    ∀ Pi_ P : ℕ → Ω' → ℝ, (∀ t ω, 0 < Pi_ t ω) →
      (∀ t, T.toExpectationSystem.E t (Pi_ t) = Pi_ t) →
      TidyR6StochasticPatches.StochEq1632 T.toExpectationSystem
        (fun x => β * (1 + phiSGU β Pis φπ x)) (fun x => lamSGU θ Y (phiSGU β Pis φπ x)) Pi_ →
      (∀ t ω, 0 < P t ω) → (∀ t ω, P (t + 1) ω = Pi_ (t + 1) ω * P t ω) →
      (∀ t, T.toExpectationSystem.E t (P t) = P t) →
      StochTVC T.toExpectationSystem θ Y β Pis φπ Pi_ P D → ∀ t ω, Pi_ t ω = Pis := by
  obtain ⟨⟨-, h1⟩, h2⟩ := sgu_finiteTree_unique T hθ hY hβ hφπ hPis hc hμ hμPis hP0 hD hDpos
  refine ⟨h1, fun Pi_ P hpos had h1632 hP hPrec hPad htvc => ?_⟩
  exact h2 Pi_ P ⟨hpos, had, (stochEq1632_iff_stochPath _ hβ Pi_).mp h1632⟩ hP hPrec hPad htvc

/-- Cochrane (2023), (16.32), p. 393, **counterexample to global stochastic uniqueness** on a
genuine probability space (consistent with the Woodford Chapter 2 finding on p. 137): on
`(ℕ, geometric(2/3))` with the switching-date filtration, `θ = Ȳ = 1`, `β = 1/2`, `Π* = 1`,
`φ_π = 5/4` (so `φ_π > 1`, `Π* > β` and the E5 condition hold) and `1 < μ̄ < 2` (`βμ̄ < Π*`), the
sunspot process (`Π = 1/3` until the switch, `Π*` afterwards) is adapted and positive, satisfies
the stochastic (16.32) almost surely with Mathlib's conditional expectation, satisfies the
transversality condition at every date and state, and has `Π₀ ≠ Π*`. -/
theorem sgu_sunspot_1632 {μ : ℝ} (hμ1 : 1 < μ) (hμ2 : μ < 2) :
    (0 < sguC 1 (1 / 2) 1 (5 / 4) ∧ (1 : ℝ) < 5 / 4 ∧ (1 / 2 : ℝ) < 1 ∧ 1 / 2 * μ < 1) ∧
    (∀ t, StronglyMeasurable[filtSw t] (sunPi t) ∧ StronglyMeasurable[filtSw t] (sunP t)) ∧
    (∀ t n, 0 < sunPi t n ∧ 0 < sunP t n ∧ sunP (t + 1) n = sunPi (t + 1) n * sunP t n) ∧
    (∀ t, muSw[fun m => lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi (t + 1) m)) /
        sunPi (t + 1) m | filtSw t] =ᵐ[muSw]
      fun n => lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi t n)) /
        (1 / 2 * (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi t n)))) ∧
    (∀ t n, Tendsto (fun T => muSw[sunV μ T | filtSw t] n) atTop (𝓝 0)) ∧
    (∀ n, sunPi 0 n ≠ 1) := by
  obtain ⟨h0, hm, hpos, heq, htvc, -, hne⟩ := sgu_sunspot_measure hμ1 hμ2
  refine ⟨h0, hm, hpos, fun t => ?_, htvc, hne⟩
  have hB : (fun m => sguB 1 1 (1 / 2) 1 (5 / 4) (sunPi (t + 1) m)) =
      (1 / 2 : ℝ) • fun m => lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi (t + 1) m)) /
        sunPi (t + 1) m := by
    funext m; simp only [sguB, Pi.smul_apply, smul_eq_mul]; ring
  have hsm := condExp_smul (μ := muSw) (m := filtSw t) (1 / 2 : ℝ)
    (fun m => lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi (t + 1) m)) / sunPi (t + 1) m)
  rw [← hB] at hsm
  filter_upwards [hsm] with n h
  have h1 := heq t n
  rw [h] at h1
  simp only [Pi.smul_apply, smul_eq_mul, sguA] at h1
  have e : lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi t n)) /
      (1 / 2 * (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi t n))) =
      2 * (lamSGU 1 1 (phiSGU (1 / 2) 1 (5 / 4) (sunPi t n)) /
        (1 + phiSGU (1 / 2) 1 (5 / 4) (sunPi t n))) := by
    rw [div_mul_eq_div_div_swap, div_div_eq_mul_div]; ring
  rw [e, ← h1]
  ring

end Cochrane.NewKeynesianSelection.TidyR6SGULink
