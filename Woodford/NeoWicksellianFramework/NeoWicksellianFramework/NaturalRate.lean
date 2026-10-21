/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.BasicModel
import NeoWicksellianFramework.ExpectationsFiniteTree
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# The natural rate of interest

Woodford (2003), *Interest and Prices*, Chapter 4, §2.1 (pp. 247–252).

Woodford (2003), *Interest and Prices*, Chapter 4, §2.1 (pp. 247–252).

All results hold for an arbitrary `ExpectationSystem` (perfect foresight and uncertainty).

## Zero inflation and the natural rate of output, exactly (p. 247)

* `zero_inflation_of_natural`: if `Y_t = Yⁿ(ξ_t)` always, a constant price level with
  `p*_t = P_{−1}` satisfies the **nonlinear** (1.4) and (1.5) (`Π₁` homogeneous of degree zero,
  `HomogeneousZero`; `Yⁿ` the root of `Π₁(1, 1, 1; Y, ξ) = 0`, `IsNaturalRate`).
* `natural_of_zero_inflation`: conversely, a constant price level satisfying the nonlinear
  (1.4)–(1.5) forces `Y_t = Yⁿ(ξ_t)` at every date and state.
* Without the two extra hypotheses: `natural_of_zero_inflation_finite` (finite state space;
  `E_tsum_finite`), `natural_of_zero_inflation_tree` (every finite event tree, `CellKnown`,
  `cellKnown_E`) and `natural_of_zero_inflation_pf` (perfect foresight).
* Log-linear: `gap_zero_of_pi_zero` (`π ≡ 0 ⟹ x ≡ 0`), `pi_zero_of_gap_zero` (`x ≡ 0 ⟹ π ≡ 0`
  for bounded inflation), `pi_ne_zero_of_gap_zero_unbounded` (boundedness is needed).

## The natural rate of interest (2.1)

* `natRate` (2.1); `euler_iff_natRate`: with zero inflation and `Y = Yⁿ`, (1.1) is `i_t = rⁿ_t`.
* `natRate_log_deriv`, `natRate_deriv_rnHat`: `r̂ⁿ = log(1 + rⁿ) + log β` is the exact derivative
  of the log of (2.1), and equals (1.15), when the natural rate of output is a `C²` function of
  the disturbances (general state space).
* `price_stability_iff` (`î = r̂ⁿ` under `π ≡ x ≡ 0`) and `inflation_target_iff` (`î = r̂ⁿ + π̄`,
  `x̄ = (1 − β)π̄/κ`).

## The natural rate of output (2.2)–(2.3)

* `realMC`, `natRateLog`, `natRateLog_eq_log`: the natural-rate condition `s(Yⁿ, Yⁿ; ξ̃) = µ⁻¹`
  in logs, with the disutility of supply `v(H(y/A); ξ_h)` (`H = f⁻¹`) and `u_c(Y − G; ξ_c)`.
* `naturalOutput_deriv`, `natRate_eq22`: the derivative of the natural rate along a disturbance
  direction is `(σ⁻¹ g + ω q)/(σ⁻¹ + ω)` with `g = Ĝ + s_C c̄`, `q = (1 + ω⁻¹)a + ω⁻¹νh̄`, `ω =
  ω_w + ω_p` (`omegaN`), `ν` (`nuL`), `h̄` (`hbarC`), all computed from the primitives;
  `natRateLog_hasFDerivAt`, `implicit_hasFDerivAt`, `natRate_hasDerivAt`,
  `natRate_hasDerivAt_of_mono`: the natural rate is differentiable (implicit-function step).
* Existence, uniqueness and smoothness: `naturalRate_existsUnique_iff`, `isoelastic_naturalRate`
  (restated from Chapter 3), `root_existsUnique_iff`, `root_function_existsUnique` (boundary
  conditions), `natRateF`, `natRateLog_eq_F`, `natRateF_contDiffAt`, `natRateF_fderiv_y`,
  `root_contDiffAt` (Mathlib's `ContDiff` implicit-function theorem), `natRate_contDiffAt`,
  `natRate_fderiv_eq22`, `natRate_existsUnique_smooth`; `natRate_log_deriv_primitives`: the
  exact derivative of the log natural rate of interest with no regularity assumed of `ŷⁿ`.
* `ynLin_expand` (the display after (2.3)), `ynLin_strictMono` (each of `Ĝ, c̄, a, h̄` raises
  `Ŷⁿ`).

## Proposition 4.1 and the p. 251 claim

* `prop41`: **Proposition 4.1**, (2.4), for AR(1) disturbances under any `ExpectationSystem`
  (independence is not needed); `prop41_signs`, `response_strictAntiOn` (larger effects for more
  transitory disturbances).
* `simple_rule_iff`: a simple Taylor rule implements price stability iff the required responses
  are collinear, `ω(1 − ρ_G) = ω(1 − ρ_c) = (ρ_a − 1)/σ = (ρ_h − 1)/σ`; `no_simple_rule`: never
  when a demand shock and a supply shock are both transitory; `simple_rule_iff_unit_roots`: under
  `ρ ≤ 1`, only when all disturbances have unit roots; `simple_rule_single_shock`: with a single
  type of disturbance a simple rule does work (hence the book's "in general").
-/

namespace Woodford.NeoWicksellianFramework.NaturalRate

open Filter Topology
open Woodford.NeoWicksellianFramework.BasicModel

variable {Ω X : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Zero inflation ⟺ output at its natural rate, exactly (p. 247) -/

/-- Woodford (2003), p. 240, fn. 7: the marginal profit `Π₁(p, p^I, P; Y, ξ̃)` is homogeneous of
degree zero in the prices `(p, p^I, P)` (since `Π` is homogeneous of degree one). -/
def HomogeneousZero (Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ) : Prop :=
  ∀ c p pI P Y (ξ : X), 0 < c → 0 < p → 0 < pI → 0 < P → Pi1 (c * p) (c * pI) (c * P) Y ξ =
    Pi1 p pI P Y ξ

/-- Woodford (2003), p. 247, and Chapter 3, (1.14) and (1.21): `Yⁿ(ξ)` is the natural rate of
output — at a symmetric point `p = p^I = P` the marginal profit vanishes exactly at `Y = Yⁿ(ξ)`
(among positive outputs). -/
def IsNaturalRate (Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ) (Yn : X → ℝ) : Prop :=
  ∀ (ξ : X) Y, 0 < Y → (Pi1 1 1 1 Y ξ = 0 ↔ Y = Yn ξ)

/-- Woodford (2003), p. 247 (**output at the natural rate makes zero inflation an equilibrium of the
aggregate-supply block, exactly**): if `Y_t = Yⁿ(ξ_t)` at all dates and states, a constant price
level `P_t = P_{−1}` with every reset price `p*_t = P_{−1}` satisfies the nonlinear (1.4) (for
`𝒫(P, P) = P`) and the nonlinear pricing condition (1.5) (each term of the sum vanishes). -/
theorem zero_inflation_of_natural {α β : ℝ} {uc : ℝ → X → ℝ} {Pagg : ℝ → ℝ → ℝ}
    {Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ} {Yn : X → ℝ} (hdiag : ∀ P, 0 < P → Pagg P P = P)
    (h0 : HomogeneousZero Pi1) (hn : IsNaturalRate Pi1 Yn) {G : ℕ → Ω → ℝ}
    {ξ : ℕ → Ω → X} {Pc : Ω → ℝ} (hPc : ∀ ω, 0 < Pc ω) (hYn : ∀ t ω, 0 < Yn (ξ t ω)) :
    Index14 Pagg (fun _ => Pc) (fun _ => Pc) ∧
      FOC15 𝔼 α β uc Pi1 G ξ (fun _ => Pc) (fun t ω => Yn (ξ t ω)) (fun _ => Pc) := by
  refine ⟨fun t ω => (hdiag (Pc ω) (hPc ω)).symm, fun t ω => ?_⟩
  have hz : ∀ k, (fun ω' => uc (Yn (ξ (t + k) ω') - G (t + k) ω') (ξ (t + k) ω') / Pc ω' *
      Pi1 (Pc ω') (Pc ω') (Pc ω') (Yn (ξ (t + k) ω')) (ξ (t + k) ω')) = 0 := by
    intro k
    funext ω'
    have h := h0 (Pc ω') 1 1 1 (Yn (ξ (t + k) ω')) (ξ (t + k) ω') (hPc ω') one_pos one_pos
      one_pos
    simp only [mul_one] at h
    rw [Pi.zero_apply, h, (hn (ξ (t + k) ω') _ (hYn (t + k) ω')).mpr rfl, mul_zero]
  simp only [hz, map_zero, Pi.zero_apply, mul_zero, tsum_zero]
  exact ⟨summable_zero, trivial⟩

/-- Woodford (2003), p. 247 (**zero inflation forces output to its natural rate, exactly**): let
`𝒫` be homogeneous of degree one with `𝒫(1, 1) = 1` and `𝒫(·, 1)` injective, `Π₁` homogeneous of
degree zero, and the price level constant, `P_t = P_{−1} > 0`. If the nonlinear (1.4) and (1.5)
hold, the discounted marginal-utility weights are positive, and the date-`T` term
`m_T = u_c(Y_T − G_T; ξ_T)/P_T · Π₁(1, 1, 1; Y_T, ξ_T)` is adapted and bounded, then
`Y_t = Yⁿ(ξ_t)` at every date and state (`0 ≤ αβ < 1`). The two hypotheses on `m` are needed for
a general `ExpectationSystem`: its axioms do not make a nonlinear function of known variables
known, nor let `E_t` pass through an infinite sum without domination. Both hold automatically on
finite event trees and under perfect foresight (`natural_of_zero_inflation_tree`,
`natural_of_zero_inflation_pf`). -/
theorem natural_of_zero_inflation {α β : ℝ} (hab0 : 0 ≤ α * β) (hab1 : α * β < 1)
    {uc : ℝ → X → ℝ} {Pagg : ℝ → ℝ → ℝ} {Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ} {Yn : X → ℝ}
    (hP : HomogeneousOne Pagg) (h11 : Pagg 1 1 = 1)
    (hinj : ∀ p q, 0 < p → 0 < q → Pagg p 1 = Pagg q 1 → p = q)
    (h0 : HomogeneousZero Pi1) (hn : IsNaturalRate Pi1 Yn) {G : ℕ → Ω → ℝ} {ξ : ℕ → Ω → X}
    {Pc : Ω → ℝ} {Y pstar : ℕ → Ω → ℝ} (hPc : ∀ ω, 0 < Pc ω) (hps : ∀ t ω, 0 < pstar t ω)
    (hY : ∀ t ω, 0 < Y t ω) (hw : ∀ t ω, 0 < uc (Y t ω - G t ω) (ξ t ω))
    (h14 : Index14 Pagg (fun _ => Pc) pstar)
    (h15 : FOC15 𝔼 α β uc Pi1 G ξ (fun _ => Pc) Y pstar) {M : ℝ}
    (hma : 𝔼.Adapted (fun T ω => uc (Y T ω - G T ω) (ξ T ω) / Pc ω * Pi1 1 1 1 (Y T ω) (ξ T ω)))
    (hmb : ∀ T ω, |uc (Y T ω - G T ω) (ξ T ω) / Pc ω * Pi1 1 1 1 (Y T ω) (ξ T ω)| ≤ M) :
    ∀ t ω, Y t ω = Yn (ξ t ω) := by
  set m : ℕ → Ω → ℝ := fun T ω => uc (Y T ω - G T ω) (ξ T ω) / Pc ω * Pi1 1 1 1 (Y T ω) (ξ T ω)
    with hm
  -- the reset price equals the constant price level
  have hpsP : ∀ t ω, pstar t ω = Pc ω := by
    intro t ω
    exact (zero_inflation_iff hP h11 hinj (hps t ω) (hPc ω)).mp (h14 t ω).symm
  -- (1.5) is the forward series of `m`
  have hfs : ∀ t, 𝔼.forwardSeries (α * β) m t = 0 := by
    intro t
    funext ω
    obtain ⟨-, h⟩ := h15 t ω
    rw [Pi.zero_apply, ← h]
    refine tsum_congr fun k => ?_
    have hmk : m (t + k) = fun ω' => uc (Y (t + k) ω' - G (t + k) ω') (ξ (t + k) ω') / Pc ω' *
        Pi1 (pstar t ω') (pstar t ω') (Pc ω') (Y (t + k) ω') (ξ (t + k) ω') := by
      funext ω'
      simp only [hm, hpsP t ω']
      have := h0 (Pc ω') 1 1 1 (Y (t + k) ω') (ξ (t + k) ω') (hPc ω') one_pos one_pos one_pos
      simp only [mul_one] at this
      rw [this]
    rw [hmk]
  intro t ω
  have hsol := congrFun (𝔼.forwardSeries_solves hab0 hab1 hmb hma t) ω
  rw [hfs t, hfs (t + 1), map_zero] at hsol
  simp only [Pi.zero_apply, Pi.add_apply, smul_zero, zero_add] at hsol
  have hmt : m t ω = 0 := hsol.symm
  simp only [hm] at hmt
  have hwpos : 0 < uc (Y t ω - G t ω) (ξ t ω) / Pc ω := div_pos (hw t ω) (hPc ω)
  have hPi : Pi1 1 1 1 (Y t ω) (ξ t ω) = 0 := (mul_eq_zero.mp hmt).resolve_left hwpos.ne'
  exact (hn (ξ t ω) (Y t ω) (hY t ω)).mp hPi

/-- Woodford (2003), pp. 240–241 (the sums in (1.5) on a finite state space): when `Ω` is finite,
`E_t` commutes with every pointwise-convergent series (`E_t` is then a continuous linear map on
the finite-dimensional space `Ω → ℝ`); no domination is needed. -/
theorem E_tsum_finite [Finite Ω] (t : ℕ) {g : ℕ → Ω → ℝ} (hs : ∀ ω, Summable fun j => g j ω) :
    𝔼.E t (fun ω => ∑' j, g j ω) = fun ω => ∑' j, 𝔼.E t (g j) ω := by
  have := Fintype.ofFinite Ω
  set L : (Ω → ℝ) →L[ℝ] (Ω → ℝ) := LinearMap.toContinuousLinearMap (𝔼.E t) with hL
  have hS : HasSum g (fun ω => ∑' j, g j ω) := Pi.hasSum.mpr fun ω => (hs ω).hasSum
  have hT := Pi.hasSum.mp (hS.mapL L)
  funext ω
  exact ((hT ω).tsum_eq).symm

/-- Woodford (2003), p. 247 (**zero inflation forces output to its natural rate, on a finite state
space, without the boundedness hypothesis**): as `natural_of_zero_inflation`, for finite `Ω`;
only the adaptedness of the date-`T` marginal-profit term is assumed. -/
theorem natural_of_zero_inflation_finite [Finite Ω] {α β : ℝ}
    {uc : ℝ → X → ℝ} {Pagg : ℝ → ℝ → ℝ} {Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ} {Yn : X → ℝ}
    (hP : HomogeneousOne Pagg) (h11 : Pagg 1 1 = 1)
    (hinj : ∀ p q, 0 < p → 0 < q → Pagg p 1 = Pagg q 1 → p = q)
    (h0 : HomogeneousZero Pi1) (hn : IsNaturalRate Pi1 Yn) {G : ℕ → Ω → ℝ} {ξ : ℕ → Ω → X}
    {Pc : Ω → ℝ} {Y pstar : ℕ → Ω → ℝ} (hPc : ∀ ω, 0 < Pc ω) (hps : ∀ t ω, 0 < pstar t ω)
    (hY : ∀ t ω, 0 < Y t ω) (hw : ∀ t ω, 0 < uc (Y t ω - G t ω) (ξ t ω))
    (h14 : Index14 Pagg (fun _ => Pc) pstar)
    (h15 : FOC15 𝔼 α β uc Pi1 G ξ (fun _ => Pc) Y pstar)
    (hma : 𝔼.Adapted (fun T ω => uc (Y T ω - G T ω) (ξ T ω) / Pc ω * Pi1 1 1 1 (Y T ω) (ξ T ω))) :
    ∀ t ω, Y t ω = Yn (ξ t ω) := by
  set m : ℕ → Ω → ℝ := fun T ω => uc (Y T ω - G T ω) (ξ T ω) / Pc ω * Pi1 1 1 1 (Y T ω) (ξ T ω)
    with hm
  set a := α * β
  have hpsP : ∀ t ω, pstar t ω = Pc ω := fun t ω =>
    (zero_inflation_iff hP h11 hinj (hps t ω) (hPc ω)).mp (h14 t ω).symm
  have hmk : ∀ t k, (fun ω' => uc (Y (t + k) ω' - G (t + k) ω') (ξ (t + k) ω') / Pc ω' *
      Pi1 (pstar t ω') (pstar t ω') (Pc ω') (Y (t + k) ω') (ξ (t + k) ω')) = m (t + k) := by
    intro t k
    funext ω'
    simp only [hm, hpsP t ω']
    have := h0 (Pc ω') 1 1 1 (Y (t + k) ω') (ξ (t + k) ω') (hPc ω') one_pos one_pos one_pos
    simp only [mul_one] at this
    rw [this]
  have hsum : ∀ t ω, Summable (fun k => a ^ k * 𝔼.E t (m (t + k)) ω) ∧
      ∑' k, a ^ k * 𝔼.E t (m (t + k)) ω = 0 := by
    intro t ω
    obtain ⟨h1, h2⟩ := h15 t ω
    simp only [hmk] at h1 h2
    exact ⟨h1, h2⟩
  intro t ω
  -- `E_t` of the date-`t+1` sum
  have hE : 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (m (t + 1 + k)) ω') ω =
      ∑' k, a ^ k * 𝔼.E t (m (t + 1 + k)) ω := by
    rw [E_tsum_finite 𝔼 t (fun ω' => (hsum (t + 1) ω').1)]
    refine tsum_congr fun k => ?_
    change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (m (t + 1 + k))) ω = _
    rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  have hzero : (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (m (t + 1 + k)) ω') = 0 := by
    funext ω'; exact (hsum (t + 1) ω').2
  rw [hzero, map_zero] at hE
  obtain ⟨hs, h0t⟩ := hsum t ω
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, hma t] at h0t
  have hshift : ∑' k, a ^ (k + 1) * 𝔼.E t (m (t + (k + 1))) ω =
      a * ∑' k, a ^ k * 𝔼.E t (m (t + 1 + k)) ω := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  rw [hshift, ← hE, Pi.zero_apply, mul_zero, add_zero] at h0t
  have hwpos : 0 < uc (Y t ω - G t ω) (ξ t ω) / Pc ω := div_pos (hw t ω) (hPc ω)
  have hPi : Pi1 1 1 1 (Y t ω) (ξ t ω) = 0 :=
    (mul_eq_zero.mp (show m t ω = 0 from h0t)).resolve_left hwpos.ne'
  exact (hn (ξ t ω) (Y t ω) (hY t ω)).mp hPi

/-- Woodford (2003), p. 247: a variable (with values in any type) is known at date `t` on a
finite event tree when it is constant on every date-`t` information cell. -/
def CellKnown {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') (t : ℕ)
    {Z : Type*} (z : Ω' → Z) : Prop :=
  ∀ ω ω', T.info t ω' ω → z ω' = z ω

/-- Woodford (2003), p. 247: on a finite event tree a real variable known at `t` is its own
conditional expectation. -/
theorem cellKnown_E {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    {t : ℕ} {x : Ω' → ℝ} (h : CellKnown T t x) : T.toExpectationSystem.E t x = x := by
  funext ω
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact T.condE_of_const_on_cell fun ω' h' => h ω ω' h'

/-- Woodford (2003), p. 247 (**zero inflation forces output to its natural rate, on every finite
event tree, with no extra hypotheses**): if output, government purchases and the disturbances
are known at their dates and the price level `P_{−1}` at date `0`, then on a finite event tree
the nonlinear (1.4)–(1.5) with a constant price level force `Y_t = Yⁿ(ξ_t)`: the marginal-profit
term is known (a function of known variables), and the sums need no domination. -/
theorem natural_of_zero_inflation_tree {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {α β : ℝ}
    {uc : ℝ → X → ℝ} {Pagg : ℝ → ℝ → ℝ} {Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ} {Yn : X → ℝ}
    (hP : HomogeneousOne Pagg) (h11 : Pagg 1 1 = 1)
    (hinj : ∀ p q, 0 < p → 0 < q → Pagg p 1 = Pagg q 1 → p = q)
    (h0 : HomogeneousZero Pi1) (hn : IsNaturalRate Pi1 Yn) {G : ℕ → Ω' → ℝ}
    {ξ : ℕ → Ω' → X} {Pc : Ω' → ℝ} {Y pstar : ℕ → Ω' → ℝ} (hPc : ∀ ω, 0 < Pc ω)
    (hps : ∀ t ω, 0 < pstar t ω) (hY : ∀ t ω, 0 < Y t ω)
    (hw : ∀ t ω, 0 < uc (Y t ω - G t ω) (ξ t ω))
    (hYk : ∀ t, CellKnown T t (Y t)) (hGk : ∀ t, CellKnown T t (G t))
    (hξk : ∀ t, CellKnown T t (ξ t)) (hPk : CellKnown T 0 Pc)
    (h14 : Index14 Pagg (fun _ => Pc) pstar)
    (h15 : FOC15 T.toExpectationSystem α β uc Pi1 G ξ (fun _ => Pc) Y pstar) :
    ∀ t ω, Y t ω = Yn (ξ t ω) := by
  refine natural_of_zero_inflation_finite T.toExpectationSystem hP h11 hinj h0 hn hPc hps hY hw
    h14 h15 fun t => cellKnown_E T fun ω ω' h => ?_
  have hP0 := hPk ω ω' (T.refines (Nat.zero_le t) ω' ω h)
  simp only [hYk t ω ω' h, hGk t ω ω' h, hξk t ω ω' h, hP0]

/-- Woodford (2003), p. 247 (**perfect foresight, with no extra hypotheses**): under perfect
foresight the nonlinear (1.4)–(1.5) with a constant price level force `Y_t = Yⁿ(ξ_t)`. -/
theorem natural_of_zero_inflation_pf {α β : ℝ}
    {uc : ℝ → X → ℝ} {Pagg : ℝ → ℝ → ℝ} {Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ} {Yn : X → ℝ}
    (hP : HomogeneousOne Pagg) (h11 : Pagg 1 1 = 1)
    (hinj : ∀ p q, 0 < p → 0 < q → Pagg p 1 = Pagg q 1 → p = q)
    (h0 : HomogeneousZero Pi1) (hn : IsNaturalRate Pi1 Yn) {G : ℕ → Unit → ℝ}
    {ξ : ℕ → Unit → X} {Pc : Unit → ℝ} {Y pstar : ℕ → Unit → ℝ} (hPc : ∀ ω, 0 < Pc ω)
    (hps : ∀ t ω, 0 < pstar t ω) (hY : ∀ t ω, 0 < Y t ω)
    (hw : ∀ t ω, 0 < uc (Y t ω - G t ω) (ξ t ω))
    (h14 : Index14 Pagg (fun _ => Pc) pstar)
    (h15 : FOC15 perfectForesight α β uc Pi1 G ξ (fun _ => Pc) Y pstar) :
    ∀ t ω, Y t ω = Yn (ξ t ω) :=
  natural_of_zero_inflation_finite perfectForesight hP h11 hinj h0 hn hPc hps hY hw h14 h15
    fun _ => rfl

/-! ### The log-linear statement: `π ≡ 0` iff `x ≡ 0` (among bounded paths) -/

/-- Woodford (2003), p. 247 ("`π_t = 0` at all times requires `x_t = 0` at all times"): under
the NKPC (1.13) with `κ ≠ 0`, zero inflation forces a zero output gap. -/
theorem gap_zero_of_pi_zero {β κ : ℝ} (hκ : κ ≠ 0) {π x : ℕ → Ω → ℝ}
    (h : NKPCurve 𝔼 β κ π x) (hπ : ∀ t, π t = 0) : ∀ t, x t = 0 := by
  intro t
  have h1 := h t
  rw [hπ t, hπ (t + 1), map_zero, smul_zero, add_zero] at h1
  funext ω
  have := congrFun h1 ω
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hκ

/-- Woodford (2003), p. 247 (the converse, among bounded paths): under (1.13) with `|β| < 1`, a
zero gap and bounded inflation give zero inflation. -/
theorem pi_zero_of_gap_zero {β κ : ℝ} (hβ : |β| < 1) {π x : ℕ → Ω → ℝ}
    (h : NKPCurve 𝔼 β κ π x) (hx : ∀ t, x t = 0) (hπb : BoundedProc π) : ∀ t, π t = 0 := by
  have h1 : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + 0 := by
    intro t
    rw [h t, hx t, smul_zero, zero_add, add_zero]
  have h2 : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have := 𝔼.forward_unique hβ h1 h2 hπb ⟨0, fun t ω => by simp⟩
  intro t
  rw [this]
  rfl

/-- Woodford (2003), p. 247 (**boundedness is needed for the converse**): under perfect foresight,
for `β ≠ 0`, `π_t = β⁻ᵗ` with `x ≡ 0` solves the NKPC (1.13) but inflation is not zero. -/
theorem pi_ne_zero_of_gap_zero_unbounded {β : ℝ} (hβ : β ≠ 0) (κ : ℝ) :
    NKPCurve perfectForesight β κ (fun t _ => (β⁻¹) ^ t) (fun _ _ => 0) ∧
      (fun (t : ℕ) (_ : Unit) => (β⁻¹) ^ t) 0 () ≠ 0 := by
  refine ⟨fun t => ?_, by simp⟩
  funext u
  simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_zero, zero_add, pow_succ]
  field_simp

/-! ### (2.1): the natural rate of interest -/

/-- Woodford (2003), eq. (2.1), p. 248 (**the Wicksellian natural rate of interest**):
`1 + rⁿ_t = β⁻¹ {E_t[u_c(Yⁿ_{t+1} − G_{t+1}; ξ_{t+1}) / u_c(Yⁿ_t − G_t; ξ_t)]}⁻¹` (the book
writes `u_c(Yⁿ; ξ)`, suppressing government purchases, which enter as in (1.1)). -/
noncomputable def natRate (β : ℝ) (uc : ℝ → X → ℝ) (G : ℕ → Ω → ℝ) (ξ : ℕ → Ω → X)
    (Yn : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  β⁻¹ * (𝔼.E t (fun ω' => uc (Yn (t + 1) ω' - G (t + 1) ω') (ξ (t + 1) ω') /
    uc (Yn t ω' - G t ω') (ξ t ω')) ω)⁻¹ - 1

/-- Woodford (2003), p. 247–248 (**with zero inflation and output at its natural rate, (1.1)
holds iff `i_t = rⁿ_t`**): if `P_t = P_{t+1}` (positive), the Euler equation (1.1) at `Y = Yⁿ`
is exactly `i_t = rⁿ_t`. -/
theorem euler_iff_natRate {β : ℝ} {uc : ℝ → X → ℝ} {G : ℕ → Ω → ℝ} {ξ : ℕ → Ω → X}
    {P Yn i : ℕ → Ω → ℝ} (t : ℕ) (hP : ∀ ω, P (t + 2) ω = P (t + 1) ω)
    (hPpos : ∀ ω, 0 < P (t + 1) ω) :
    Euler11 𝔼 β uc G ξ P Yn i t ↔ ∀ ω, i t ω = natRate 𝔼 β uc G ξ Yn t ω := by
  have hf : (fun ω' => uc (Yn (t + 1) ω' - G (t + 1) ω') (ξ (t + 1) ω') * P (t + 1) ω' /
      (uc (Yn t ω' - G t ω') (ξ t ω') * P (t + 2) ω')) = fun ω' =>
      uc (Yn (t + 1) ω' - G (t + 1) ω') (ξ (t + 1) ω') / uc (Yn t ω' - G t ω') (ξ t ω') := by
    funext ω'
    rw [hP ω', mul_div_mul_right _ _ (hPpos ω').ne']
  simp only [Euler11, natRate, hf]
  refine forall_congr' fun ω => ?_
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 248 (**`r̂ⁿ = log(1 + rⁿ) + log β` is the exact derivative of the log of
(2.1)**, general state space): let the natural rate of output be a `C²` function `ŷⁿ(s)` of the
disturbances `s = (Ĝ, ξ, …) ∈ S` with `ŷⁿ(0) = 0`, and `λ = lambdaG` the log marginal utility.
Along bounded disturbance paths `s_t`, scaled by `ε`,
`ε ↦ log(β(1 + rⁿ_t)) = −log E_t[exp(Λ(ε s_{t+1}) − Λ(ε s_t))]`, `Λ(s) = λ(ŷⁿ(s), Ĝ, ξ)`, has
derivative `E_t[DΛ(s_t) − DΛ(s_{t+1})]` at `ε = 0`, where `DΛ = −σ⁻¹(Dŷⁿ − g)`. -/
theorem natRate_log_deriv {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {uc : ℝ × ℝ → ℝ} {Ybar Gbar : ℝ} (hu : 0 < uc (Ybar - Gbar, 0))
    (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0)) {yn : S → ℝ} (hyn : ContDiffAt ℝ 2 yn 0)
    (hyn0 : yn 0 = 0) (Gof xiof : S →L[ℝ] ℝ) {s : ℕ → Ω → S} {K : ℝ}
    (hs : ∀ τ ω, ‖s τ ω‖ ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
        (lambdaG uc Ybar Gbar (yn (ε • s (t + 1) ω'), Gof (ε • s (t + 1) ω'),
            xiof (ε • s (t + 1) ω')) -
          lambdaG uc Ybar Gbar (yn (ε • s t ω'), Gof (ε • s t ω'), xiof (ε • s t ω')) -
          ε * 0)) ω))
      (𝔼.E t (fun ω' => fderiv ℝ (fun z : S => lambdaG uc Ybar Gbar (yn z, Gof z, xiof z)) 0
          (s t ω') -
        fderiv ℝ (fun z : S => lambdaG uc Ybar Gbar (yn z, Gof z, xiof z)) 0 (s (t + 1) ω') +
        0) ω) 0 := by
  set Λ : S → ℝ := fun z => lambdaG uc Ybar Gbar (yn z, Gof z, xiof z) with hΛ
  have hin : ContDiffAt ℝ 2 (fun z : S => ((yn z, Gof z, xiof z) : ℝ × ℝ × ℝ)) 0 :=
    hyn.prodMk (Gof.contDiff.contDiffAt.prodMk xiof.contDiff.contDiffAt)
  have hin0 : ((yn 0, Gof 0, xiof 0) : ℝ × ℝ × ℝ) = 0 := by
    simp [hyn0]
  have hΛ2 : ContDiffAt ℝ 2 Λ 0 :=
    ContDiffAt.comp (g := lambdaG uc Ybar Gbar) (0 : S)
      (by rw [hin0]; exact contDiffAt_lambdaG hu huc2) hin
  have hΛ0 : Λ 0 = 0 := by
    simp only [hΛ]
    rw [hin0]
    exact lambdaG_zero uc Ybar Gbar
  obtain ⟨C, r, hr, hrem⟩ := quadratic_remainder hΛ2
  have := hasDerivAt_neg_log_E_exp 𝔼 hr hΛ0 hrem (a := s (t + 1)) (b := s t)
    (p := fun _ => 0) (hs (t + 1)) (hs t) (fun _ => by simpa using (norm_nonneg _).trans (hs t ω))
    t ω
  exact this

/-- Woodford (2003), eq. (1.15) and p. 248 (**the derivative of the log natural rate is `r̂ⁿ` of
(1.15)**): under the hypotheses of `natRate_log_deriv`, with `u_c` having partial derivatives
`u_cc ≠ 0`, `u_cξ` at the steady state and `ŷⁿ` the derivative `Dŷⁿ`, the derivative of
`ε ↦ log(β(1 + rⁿ_t))` is `r̂ⁿ_t = σ⁻¹[(g_t − Ŷⁿ_t) − E_t(g_{t+1} − Ŷⁿ_{t+1})]`, where
`Ŷⁿ_τ = Dŷⁿ(s_τ)` and `g_τ = Ĝ_τ + s_C c̄_τ` are adapted, `σ = s_C σ̃`. -/
theorem natRate_deriv_rnHat {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc ucxi : ℝ} (hY : 0 < Ybar) (hC : 0 < Ybar - Gbar)
    (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0)) {yn : S → ℝ} {Dyn : S →L[ℝ] ℝ}
    (hyn : ContDiffAt ℝ 2 yn 0) (hDyn : HasFDerivAt yn Dyn 0) (hyn0 : yn 0 = 0)
    (Gof xiof : S →L[ℝ] ℝ) {s : ℕ → Ω → S} {K : ℝ} (hs : ∀ τ ω, ‖s τ ω‖ ≤ K)
    (hga : 𝔼.Adapted (fun τ ω => Gof (s τ ω) + gcoef Ybar Gbar ucc ucxi * xiof (s τ ω)))
    (hna : 𝔼.Adapted (fun τ ω => Dyn (s τ ω))) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε : ℝ => -Real.log (𝔼.E t (fun ω' => Real.exp
        (lambdaG uc Ybar Gbar (yn (ε • s (t + 1) ω'), Gof (ε • s (t + 1) ω'),
            xiof (ε • s (t + 1) ω')) -
          lambdaG uc Ybar Gbar (yn (ε • s t ω'), Gof (ε • s t ω'), xiof (ε • s t ω')))) ω))
      (rnHat 𝔼 (sigmaIS uc Ybar Gbar ucc)
        (fun τ ω => Gof (s τ ω) + gcoef Ybar Gbar ucc ucxi * xiof (s τ ω))
        (fun τ ω => Dyn (s τ ω)) t ω) 0 := by
  have h := natRate_log_deriv 𝔼 hu huc2 hyn hyn0 Gof xiof hs t ω
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr_deriv ?_
  have hF := hasFDerivAt_lambdaG hY hC hu hcc huc
  have hin : HasFDerivAt (fun z : S => ((yn z, Gof z, xiof z) : ℝ × ℝ × ℝ))
      (Dyn.prod (Gof.prod xiof)) 0 := hDyn.prodMk (Gof.hasFDerivAt.prodMk xiof.hasFDerivAt)
  have hin0 : ((yn 0, Gof 0, xiof 0) : ℝ × ℝ × ℝ) = 0 := by simp [hyn0]
  have hΛ := HasFDerivAt.comp (g := lambdaG uc Ybar Gbar) (0 : S) (by rw [hin0]; exact hF) hin
  rw [show (fun z : S => lambdaG uc Ybar Gbar (yn z, Gof z, xiof z)) =
    lambdaG uc Ybar Gbar ∘ (fun z : S => ((yn z, Gof z, xiof z) : ℝ × ℝ × ℝ)) from rfl,
    hΛ.fderiv]
  set σ := sigmaIS uc Ybar Gbar ucc
  set gc := gcoef Ybar Gbar ucc ucxi
  have hfun : (fun ω' => ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gc • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).comp (Dyn.prod (Gof.prod xiof)) (s t ω') -
      ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gc • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).comp (Dyn.prod (Gof.prod xiof))
              (s (t + 1) ω')) =
      σ⁻¹ • ((fun ω' => (Gof (s t ω') + gc * xiof (s t ω')) - Dyn (s t ω')) -
        (fun ω' => (Gof (s (t + 1) ω') + gc * xiof (s (t + 1) ω')) - Dyn (s (t + 1) ω'))) := by
    funext ω'
    simp
    ring
  rw [hfun, map_smul, map_sub]
  have h1 : 𝔼.E t (fun ω' => (Gof (s t ω') + gc * xiof (s t ω')) - Dyn (s t ω')) =
      fun ω' => (Gof (s t ω') + gc * xiof (s t ω')) - Dyn (s t ω') := by
    have : (fun ω' => (Gof (s t ω') + gc * xiof (s t ω')) - Dyn (s t ω')) =
        (fun ω' => Gof (s t ω') + gc * xiof (s t ω')) - fun ω' => Dyn (s t ω') := rfl
    rw [this, map_sub, hga t, hna t]
  rw [h1]
  simp only [rnHat, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rfl

/-! ### The inflation target (p. 248) -/

/-- Woodford (2003), p. 247 (**complete price stability requires `î = r̂ⁿ`**): with `π ≡ 0` and
`x ≡ 0`, the gap IS relation (1.12) holds iff `î_t = r̂ⁿ_t` at all dates (`σ ≠ 0`); the NKPC
(1.13) holds trivially. -/
theorem price_stability_iff {σ : ℝ} (hσ : σ ≠ 0) (β κ : ℝ) (ih rn : ℕ → Ω → ℝ) :
    NKPCurve 𝔼 β κ 0 0 ∧ (IS112 𝔼 σ 0 ih 0 rn ↔ ∀ t, ih t = rn t) := by
  refine ⟨fun t => by simp, ?_⟩
  constructor
  · intro h t
    have h1 := h t
    simp only [Pi.zero_apply, map_zero, zero_sub, sub_zero] at h1
    funext ω
    have := congrFun h1 ω
    simp only [Pi.zero_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
    have h2 : σ * (ih t ω - rn t ω) = 0 := by linarith
    have := (mul_eq_zero.mp h2).resolve_left hσ
    linarith
  · intro h t
    funext ω
    simp [h t]

/-- Woodford (2003), p. 248 (**the inflation-target version**): with constant inflation `π̄` and a
constant gap `x̄'`, the NKPC (1.13) holds iff `x̄' = (1 − β)π̄/κ`, and the gap IS relation (1.12)
holds iff `î_t = r̂ⁿ_t + π̄` at all dates (`κ, σ ≠ 0`): the responses to shocks are as under
`π̄ = 0`, only the constants change. -/
theorem inflation_target_iff [Nonempty Ω] {β κ σ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) (πbar xb : ℝ)
    (ih rn : ℕ → Ω → ℝ) :
    (NKPCurve 𝔼 β κ (fun _ _ => πbar) (fun _ _ => xb) ↔ xb = xbar β κ πbar) ∧
      (IS112 𝔼 σ (fun _ _ => xb) ih (fun _ _ => πbar) rn ↔ ∀ t, ih t = rn t + fun _ => πbar) := by
  refine ⟨const_nkpc_iff 𝔼 hκ πbar xb, ?_⟩
  have hE : ∀ t (c : ℝ), 𝔼.E t (fun _ : Ω => c) = fun _ => c := fun t c => 𝔼.const t c
  constructor
  · intro h t
    have h1 := h t
    rw [hE, hE] at h1
    funext ω
    have := congrFun h1 ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at this ⊢
    have h2 : σ * (ih t ω - πbar - rn t ω) = 0 := by linarith
    have := (mul_eq_zero.mp h2).resolve_left hσ
    linarith
  · intro h t
    rw [hE, hE]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h t, Pi.add_apply]
    ring

/-! ### (2.2)–(2.3): the natural rate of output -/

/-- Woodford (2003), Chapter 3, (1.10) and (1.13)–(1.14), and Chapter 4, p. 249: real marginal
cost `s(Y, Y; ξ̃) = ṽ_y(Y; ξ̃)/u_c(Y − G; ξ)` at a symmetric point, with the disutility of supply
`ṽ(y; ξ̃) = v(H(y/A); ξ_h)` (`H = f⁻¹` the labour requirement, `H'` its derivative), so
`ṽ_y = v_h(H(y/A); ξ_h) H'(y/A)/A`. The natural rate solves `s(Yⁿ, Yⁿ; ξ̃) = µ⁻¹`. -/
noncomputable def realMC (vh : ℝ × ℝ → ℝ) (H H' : ℝ → ℝ) (uc : ℝ × ℝ → ℝ)
    (Y G A xic xih : ℝ) : ℝ :=
  vh (H (Y / A), xih) * H' (Y / A) / (A * uc (Y - G, xic))

/-- Woodford (2003), p. 249: the log of real marginal cost relative to its steady-state value
along the disturbance direction `d = (Ĝ, ξ_c, a, ξ_h)` scaled by `ε` (`Y = Ȳ e^y`,
`G = Ḡ + Ȳ ε Ĝ`, `A = e^{ε a}`), written as a sum of logarithms. -/
noncomputable def natRateLog (vh : ℝ × ℝ → ℝ) (H H' : ℝ → ℝ) (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ)
    (d : ℝ × ℝ × ℝ × ℝ) (y ε : ℝ) : ℝ :=
  Real.log (vh (H (Ybar * Real.exp (y - ε * d.2.2.1)), ε * d.2.2.2)) +
    Real.log (H' (Ybar * Real.exp (y - ε * d.2.2.1))) - ε * d.2.2.1 -
    Real.log (uc (Ybar * Real.exp y - Gbar - Ybar * (ε * d.1), ε * d.2.1)) -
    (Real.log (vh (H Ybar, 0)) + Real.log (H' Ybar) - Real.log (uc (Ybar - Gbar, 0)))

/-- Woodford (2003), p. 249: with positive marginal disutility, labour requirement slope and
marginal utility, `natRateLog` is the log of the ratio of real marginal cost to its steady-state
value; so if the natural rate solves `s(Yⁿ, Yⁿ; ξ̃) = µ⁻¹ = s(Ȳ, Ȳ; 0)` then `natRateLog = 0`. -/
theorem natRateLog_eq_log {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ} {Ybar Gbar : ℝ}
    (d : ℝ × ℝ × ℝ × ℝ) (y ε : ℝ)
    (h1 : 0 < vh (H (Ybar * Real.exp (y - ε * d.2.2.1)), ε * d.2.2.2))
    (h2 : 0 < H' (Ybar * Real.exp (y - ε * d.2.2.1)))
    (h3 : 0 < uc (Ybar * Real.exp y - Gbar - Ybar * (ε * d.1), ε * d.2.1))
    (h4 : 0 < vh (H Ybar, 0)) (h5 : 0 < H' Ybar) (h6 : 0 < uc (Ybar - Gbar, 0)) :
    natRateLog vh H H' uc Ybar Gbar d y ε = Real.log (realMC vh H H' uc (Ybar * Real.exp y)
      (Gbar + Ybar * (ε * d.1)) (Real.exp (ε * d.2.2.1)) (ε * d.2.1) (ε * d.2.2.2) /
      realMC vh H H' uc Ybar Gbar 1 0 0) := by
  have hYA : Ybar * Real.exp y / Real.exp (ε * d.2.2.1) = Ybar * Real.exp (y - ε * d.2.2.1) := by
    rw [Real.exp_sub]; ring
  have hYG : Ybar * Real.exp y - (Gbar + Ybar * (ε * d.1)) =
      Ybar * Real.exp y - Gbar - Ybar * (ε * d.1) := by ring
  unfold realMC
  rw [hYA, hYG, div_one, one_mul]
  have hA := Real.exp_pos (ε * d.2.2.1)
  rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_mul h1.ne' h2.ne',
    Real.log_mul h4.ne' h5.ne', Real.log_mul hA.ne' h3.ne', Real.log_exp]
  unfold natRateLog
  ring

/-- Woodford (2003), p. 249: `ν = H̄ v_hh / v_h`, the inverse of the Frisch elasticity of labour
supply. -/
noncomputable def nuL (vh : ℝ × ℝ → ℝ) (H : ℝ → ℝ) (vhh Ybar : ℝ) : ℝ :=
  H Ybar * vhh / vh (H Ybar, 0)

/-- Woodford (2003), Chapter 3, (1.16): `ω = ω_w + ω_p`, the elasticity of real marginal cost with
respect to own output, with `ω_w = ν · Ȳ H'(Ȳ)/H̄` (the wage-demand elasticity) and
`ω_p = Ȳ H''(Ȳ)/H'(Ȳ)` (the elasticity of `Ψ = H' = 1/f'(f⁻¹)`). -/
noncomputable def omegaN (vh : ℝ × ℝ → ℝ) (H H' : ℝ → ℝ) (vhh H2 Ybar : ℝ) : ℝ :=
  nuL vh H vhh Ybar * (Ybar * H' Ybar / H Ybar) + Ybar * H2 / H' Ybar

/-- Woodford (2003), p. 249: the Frisch labour-supply shift per unit of the disutility shock,
`h̄ = −v_hξ ξ_h/(H̄ v_hh)`. -/
noncomputable def hbarC (H : ℝ → ℝ) (vhh vhxi Ybar : ℝ) : ℝ := -vhxi / (H Ybar * vhh)

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 249 (**the natural rate of output, as an exact
derivative**): let the natural rate along the disturbance direction `d = (Ĝ, ξ_c, a, ξ_h)` be
`Ŷⁿ(ε) = yn ε` with `yn 0 = 0`, `yn` differentiable at `0` with derivative `dn`, solving
`natRateLog = 0` for every `ε` (`natRateLog_eq_log`: real marginal cost equals `µ⁻¹`). If `v_h`,
`H`, `H'`, `u_c` are differentiable at the steady state, then
`(ω + σ⁻¹) dn = σ⁻¹ g + (1 + ω) a + ν h̄`, with `g = Ĝ + s_C c̄` and `h̄ = hbarC · ξ_h`; i.e.
`dn = (σ⁻¹ g + ω q)/(σ⁻¹ + ω)` with `q = (1 + ω⁻¹) a + ω⁻¹ ν h̄` (`natRate_eq22`). -/
theorem naturalOutput_deriv {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi dn : ℝ} (d : ℝ × ℝ × ℝ × ℝ) (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0)) (hvhh : vhh ≠ 0) (hcc : ucc ≠ 0)
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    {yn : ℝ → ℝ} (hyn : HasDerivAt yn dn 0) (hyn0 : yn 0 = 0)
    (himp : ∀ ε, natRateLog vh H H' uc Ybar Gbar d (yn ε) ε = 0) :
    (omegaN vh H H' vhh H2 Ybar + (sigmaIS uc Ybar Gbar ucc)⁻¹) * dn =
      (sigmaIS uc Ybar Gbar ucc)⁻¹ * (d.1 + gcoef Ybar Gbar ucc ucxi * d.2.1) +
        (1 + omegaN vh H H' vhh H2 Ybar) * d.2.2.1 +
        nuL vh H vhh Ybar * (hbarC H vhh vhxi Ybar * d.2.2.2) := by
  obtain ⟨Gd, xc, a, xh⟩ := d
  simp only at himp ⊢
  -- the log output-per-technology path `z(ε) = yn ε − ε a`
  have hz : HasDerivAt (fun ε => yn ε - ε * a) (dn - a) 0 := hyn.sub (hasDerivAt_mul_const a)
  have he : HasDerivAt (fun ε => Ybar * Real.exp (yn ε - ε * a)) (Ybar * (dn - a)) 0 := by
    have := (hz.exp).const_mul Ybar
    simpa [hyn0] using this
  have he0 : Ybar = (fun ε => Ybar * Real.exp (yn ε - ε * a)) 0 := by simp [hyn0]
  have hHc := HasDerivAt.comp_of_eq (hh₂ := hH) (hh := he) (hy := he0)
  have hH2c := HasDerivAt.comp_of_eq (hh₂ := hH2) (hh := he) (hy := he0)
  -- the hours/disutility term
  have hc1 : HasDerivAt (fun ε => (H (Ybar * Real.exp (yn ε - ε * a)), ε * xh))
      (H' Ybar * (Ybar * (dn - a)), xh) 0 := hHc.prodMk (hasDerivAt_mul_const xh)
  have hc10 : (H Ybar, (0 : ℝ)) = (fun ε => (H (Ybar * Real.exp (yn ε - ε * a)), ε * xh)) 0 := by
    simp [hyn0]
  have hV := (HasFDerivAt.comp_hasDerivAt_of_eq (hl := hvh) (hf := hc1) (hy := hc10)).log (by
    simpa [hyn0] using hvh0.ne')
  have hL := (hH2c.log (by simpa [hyn0] using hH'0.ne'))
  -- the marginal-utility term
  have hc2 : HasDerivAt (fun ε => (Ybar * Real.exp (yn ε) - Gbar - Ybar * (ε * Gd), ε * xc))
      (Ybar * dn - Ybar * Gd, xc) 0 := by
    have h1 := ((hyn.exp).const_mul Ybar).sub_const Gbar
    have h2 := ((hasDerivAt_mul_const (x := (0 : ℝ)) Gd).const_mul Ybar)
    have := (h1.sub h2).prodMk (hasDerivAt_mul_const xc)
    simpa [hyn0] using this
  have hc20 : (Ybar - Gbar, (0 : ℝ)) =
      (fun ε => (Ybar * Real.exp (yn ε) - Gbar - Ybar * (ε * Gd), ε * xc)) 0 := by
    simp [hyn0]
  have hU := (HasFDerivAt.comp_hasDerivAt_of_eq (hl := huc) (hf := hc2) (hy := hc20)).log (by
    simpa [hyn0] using hu.ne')
  have hall := (((hV.add hL).sub (hasDerivAt_mul_const a)).sub hU).sub_const
    (Real.log (vh (H Ybar, 0)) + Real.log (H' Ybar) - Real.log (uc (Ybar - Gbar, 0)))
  have hconst : HasDerivAt (fun ε => natRateLog vh H H' uc Ybar Gbar (Gd, xc, a, xh) (yn ε) ε)
      0 0 := by
    simp only [himp]
    exact hasDerivAt_const _ _
  have heq := hall.unique hconst
  simp [hyn0] at heq
  unfold omegaN nuL hbarC sigmaIS gcoef
  have hC' : Ybar - Gbar ≠ 0 := hC.ne'
  field_simp at heq ⊢
  linear_combination heq

/-- Woodford (2003), eq. (2.3), p. 249: `g = Ĝ + s_C c̄`. -/
def gLin (sC G c : ℝ) : ℝ := G + sC * c

/-- Woodford (2003), eq. (2.3), p. 249: `q = (1 + ω⁻¹) a + ω⁻¹ ν h̄`. -/
noncomputable def qLin (ω ν a h : ℝ) : ℝ := (1 + ω⁻¹) * a + ω⁻¹ * ν * h

/-- Woodford (2003), eq. (2.2), p. 249: `Ŷⁿ = (σ⁻¹ g + ω q)/(σ⁻¹ + ω)`. -/
noncomputable def ynLin (σ ω g q : ℝ) : ℝ := (σ⁻¹ * g + ω * q) / (σ⁻¹ + ω)

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 249 (**the natural rate of output**): under the
hypotheses of `naturalOutput_deriv`, with `ω ≠ 0` and `σ⁻¹ + ω ≠ 0`, the derivative of the natural
rate along `d = (Ĝ, ξ_c, a, ξ_h)` is `(σ⁻¹ g + ω q)/(σ⁻¹ + ω)` with `g = Ĝ + s_C c̄` and
`q = (1 + ω⁻¹) a + ω⁻¹ ν h̄`. -/
theorem natRate_eq22 {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi dn : ℝ} (d : ℝ × ℝ × ℝ × ℝ) (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0)) (hvhh : vhh ≠ 0) (hcc : ucc ≠ 0)
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    {yn : ℝ → ℝ} (hyn : HasDerivAt yn dn 0) (hyn0 : yn 0 = 0)
    (himp : ∀ ε, natRateLog vh H H' uc Ybar Gbar d (yn ε) ε = 0)
    (hω : omegaN vh H H' vhh H2 Ybar ≠ 0)
    (hden : (sigmaIS uc Ybar Gbar ucc)⁻¹ + omegaN vh H H' vhh H2 Ybar ≠ 0) :
    dn = ynLin (sigmaIS uc Ybar Gbar ucc) (omegaN vh H H' vhh H2 Ybar)
      (gLin ((Ybar - Gbar) / Ybar) d.1 (-ucxi / ((Ybar - Gbar) * ucc) * d.2.1))
      (qLin (omegaN vh H H' vhh H2 Ybar) (nuL vh H vhh Ybar) d.2.2.1
        (hbarC H vhh vhxi Ybar * d.2.2.2)) := by
  have h := naturalOutput_deriv d hY hC hHb hvh0 hH'0 hu hvhh hcc hH hH2 hvh huc hyn hyn0 himp
  have hg : gLin ((Ybar - Gbar) / Ybar) d.1 (-ucxi / ((Ybar - Gbar) * ucc) * d.2.1) =
      d.1 + gcoef Ybar Gbar ucc ucxi * d.2.1 := by
    unfold gLin gcoef; ring
  rw [hg]
  unfold ynLin qLin
  rw [eq_div_iff hden]
  have hω' : omegaN vh H H' vhh H2 Ybar * ((1 + (omegaN vh H H' vhh H2 Ybar)⁻¹) * d.2.2.1 +
      (omegaN vh H H' vhh H2 Ybar)⁻¹ * nuL vh H vhh Ybar * (hbarC H vhh vhxi Ybar * d.2.2.2)) =
      (1 + omegaN vh H H' vhh H2 Ybar) * d.2.2.1 +
        nuL vh H vhh Ybar * (hbarC H vhh vhxi Ybar * d.2.2.2) := by
    field_simp
    ring
  rw [hω']
  linear_combination h

/-- Woodford (2003), p. 249 (the display after (2.3)): substituting (2.3) in (2.2),
`Ŷⁿ = σ⁻¹/(σ⁻¹ + ω) (Ĝ + s_C c̄) + 1/(σ⁻¹ + ω) ((1 + ω) a + ν h̄)` (`ω ≠ 0`). -/
theorem ynLin_expand {σ ω ν sC : ℝ} (hω : ω ≠ 0) (G c a h : ℝ) :
    ynLin σ ω (gLin sC G c) (qLin ω ν a h) =
      σ⁻¹ / (σ⁻¹ + ω) * (G + sC * c) + 1 / (σ⁻¹ + ω) * ((1 + ω) * a + ν * h) := by
  unfold ynLin gLin qLin
  field_simp
  ring

/-- Woodford (2003), p. 249 (**each disturbance raises the natural rate of output**): for
`σ, ω, ν, s_C > 0`, `Ŷⁿ` is strictly increasing in each of `Ĝ`, `c̄`, `a` and `h̄`. -/
theorem ynLin_strictMono {σ ω ν sC : ℝ} (hσ : 0 < σ) (hω : 0 < ω) (hν : 0 < ν) (hsC : 0 < sC)
    (G c a h : ℝ) :
    StrictMono (fun G' => ynLin σ ω (gLin sC G' c) (qLin ω ν a h)) ∧
      StrictMono (fun c' => ynLin σ ω (gLin sC G c') (qLin ω ν a h)) ∧
      StrictMono (fun a' => ynLin σ ω (gLin sC G c) (qLin ω ν a' h)) ∧
      StrictMono (fun h' => ynLin σ ω (gLin sC G c) (qLin ω ν a h')) := by
  have hden : 0 < σ⁻¹ + ω := by positivity
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x y hxy => ?_, fun x y hxy => ?_⟩ <;>
    simp only [ynLin_expand hω.ne'] <;>
    · have h1 : 0 < σ⁻¹ / (σ⁻¹ + ω) := by positivity
      have h2 : 0 < 1 / (σ⁻¹ + ω) := by positivity
      nlinarith [mul_pos h1 hsC, mul_pos h2 hν, mul_pos h2 (show (0 : ℝ) < 1 + ω by linarith)]

/-! ### Proposition 4.1 -/

/-- Woodford (2003), **Proposition 4.1**, eq. (2.4), p. 250: let `Ĝ, c̄, a, h̄` be AR(1)
processes (`E_t x_{t+1} = ρ x_t`, any `ExpectationSystem`; independence is not needed), `g` and
`q` as in (2.3) and `Ŷⁿ` as in (2.2). Then the natural rate of interest (1.15) is
`r̂ⁿ_t = (σ + ω⁻¹)⁻¹[(1 − ρ_G)Ĝ_t + s_C(1 − ρ_c)c̄_t − (1 + ω⁻¹)(1 − ρ_a)a_t
− ω⁻¹ν(1 − ρ_h)h̄_t]` (`σ, ω > 0`). -/
theorem prop41 {σ ω ν sC ρG ρc ρa ρh : ℝ} (hσ : 0 < σ) (hω : 0 < ω)
    {Gh cb ah hb : ℕ → Ω → ℝ} (hG : 𝔼.IsAR1 ρG Gh) (hc : 𝔼.IsAR1 ρc cb)
    (ha : 𝔼.IsAR1 ρa ah) (hh : 𝔼.IsAR1 ρh hb) (t : ℕ) :
    rnHat 𝔼 σ (fun τ ω' => gLin sC (Gh τ ω') (cb τ ω'))
        (fun τ ω' => ynLin σ ω (gLin sC (Gh τ ω') (cb τ ω')) (qLin ω ν (ah τ ω') (hb τ ω'))) t =
      fun ω' => (σ + ω⁻¹)⁻¹ * ((1 - ρG) * Gh t ω' + sC * (1 - ρc) * cb t ω' -
        (1 + ω⁻¹) * (1 - ρa) * ah t ω' - ω⁻¹ * ν * (1 - ρh) * hb t ω') := by
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ
  have hden : σ⁻¹ + ω ≠ 0 := by positivity
  have hω0 : ω ≠ 0 := hω.ne'
  set k := ω / (σ⁻¹ + ω) with hk
  -- `g − Ŷⁿ = ω(g − q)/(σ⁻¹ + ω)` as a combination of the four shocks
  have hlin : ∀ τ, ((fun ω' => gLin sC (Gh τ ω') (cb τ ω')) -
      fun ω' => ynLin σ ω (gLin sC (Gh τ ω') (cb τ ω')) (qLin ω ν (ah τ ω') (hb τ ω'))) =
      k • Gh τ + (k * sC) • cb τ + (-(k * (1 + ω⁻¹))) • ah τ + (-(k * (ω⁻¹ * ν))) • hb τ := by
    intro τ
    funext ω'
    simp only [gLin, ynLin, qLin, hk, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  funext ω'
  simp only [rnHat, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have e1 := congrFun (hlin t) ω'
  have e2 : 𝔼.E t ((fun ω' => gLin sC (Gh (t + 1) ω') (cb (t + 1) ω')) -
      fun ω' => ynLin σ ω (gLin sC (Gh (t + 1) ω') (cb (t + 1) ω')) (qLin ω ν (ah (t + 1) ω')
        (hb (t + 1) ω'))) ω' =
      k * (ρG * Gh t ω') + k * sC * (ρc * cb t ω') + -(k * (1 + ω⁻¹)) * (ρa * ah t ω') +
        -(k * (ω⁻¹ * ν)) * (ρh * hb t ω') := by
    rw [hlin (t + 1)]
    simp only [map_add, map_smul, hG.2 t, hc.2 t, ha.2 t, hh.2 t, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1
  rw [e2, e1, hk]
  field_simp
  ring

/-- Woodford (2003), p. 250 (**signs of the responses**): with `σ, ω, ν, s_C > 0` and every
`ρ < 1` (stationarity), the natural rate of interest rises with `Ĝ` and `c̄` and falls with `a`
and `h̄`: the coefficients of (2.4) are positive, positive, negative, negative. -/
theorem prop41_signs {σ ω ν sC ρG ρc ρa ρh : ℝ} (hσ : 0 < σ) (hω : 0 < ω) (hν : 0 < ν)
    (hsC : 0 < sC) (hG : ρG < 1) (hc : ρc < 1) (ha : ρa < 1) (hh : ρh < 1) :
    0 < (σ + ω⁻¹)⁻¹ * (1 - ρG) ∧ 0 < (σ + ω⁻¹)⁻¹ * (sC * (1 - ρc)) ∧
      (σ + ω⁻¹)⁻¹ * (-((1 + ω⁻¹) * (1 - ρa))) < 0 ∧
      (σ + ω⁻¹)⁻¹ * (-(ω⁻¹ * ν * (1 - ρh))) < 0 := by
  have hk : 0 < (σ + ω⁻¹)⁻¹ := by positivity
  have h1 : 0 < 1 - ρG := by linarith
  have h2 : 0 < 1 - ρc := by linarith
  have h3 : 0 < 1 - ρa := by linarith
  have h4 : 0 < 1 - ρh := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · have : 0 < (1 + ω⁻¹) * (1 - ρa) := by positivity
    nlinarith
  · have : 0 < ω⁻¹ * ν * (1 - ρh) := by positivity
    nlinarith

/-- Woodford (2003), p. 250 (**"the effects upon the natural rate of interest are larger the more
temporary the disturbance"**): for a response coefficient `c(1 − ρ)` with `c ≠ 0`, its magnitude
`|c(1 − ρ)|` is strictly decreasing in `ρ` on `ρ ≤ 1`. (Each coefficient of (2.4) has this form,
with `c = (σ + ω⁻¹)⁻¹`, `(σ + ω⁻¹)⁻¹ s_C`, `−(σ + ω⁻¹)⁻¹(1 + ω⁻¹)`, `−(σ + ω⁻¹)⁻¹ω⁻¹ν`.) -/
theorem response_strictAntiOn {c : ℝ} (hc : c ≠ 0) :
    StrictAntiOn (fun ρ => |c * (1 - ρ)|) (Set.Iic 1) := by
  intro x hx y hy hxy
  simp only [Set.mem_Iic] at hx hy
  simp only [abs_mul, abs_of_nonneg (show 0 ≤ 1 - x by linarith),
    abs_of_nonneg (show 0 ≤ 1 - y by linarith)]
  have := abs_pos.mpr hc
  nlinarith

/-! ### No simple Taylor rule implements price stability (p. 251) -/

/-- Woodford (2003), eq. (2.4), p. 250: the required interest rate `r̂ⁿ` as a function of the
current disturbances `s = (Ĝ, c̄, a, h̄)`. -/
noncomputable def rReq (σ ω ν sC ρG ρc ρa ρh : ℝ) (s : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  (σ + ω⁻¹)⁻¹ * ((1 - ρG) * s.1 + sC * (1 - ρc) * s.2.1 - (1 + ω⁻¹) * (1 - ρa) * s.2.2.1 -
    ω⁻¹ * ν * (1 - ρh) * s.2.2.2)

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 249: equilibrium output `Ŷ = Ŷⁿ` under price
stability, as a function of `s = (Ĝ, c̄, a, h̄)`. -/
noncomputable def yReq (σ ω ν sC : ℝ) (s : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  ynLin σ ω (gLin sC s.1 s.2.1) (qLin ω ν s.2.2.1 s.2.2.2)

/-- Woodford (2003), p. 251 (**the exact condition**): in the price-stable equilibrium
(`π ≡ 0`, so the inflation response `φ_π` plays no role, and `Ŷ = Ŷⁿ`) a simple rule
`î = ī + φ_π π + φ_y Ŷ` with constant `ī, φ_π, φ_y` delivers the required `î = r̂ⁿ` for all
disturbance values iff the required interest-rate and output responses are collinear across the
four shocks: `ω(1 − ρ_G) = ω(1 − ρ_c) = (ρ_a − 1)/σ = (ρ_h − 1)/σ` (`σ, ω, ν, s_C > 0`). -/
theorem simple_rule_iff {σ ω ν sC ρG ρc ρa ρh : ℝ} (hσ : 0 < σ) (hω : 0 < ω) (hν : 0 < ν)
    (hsC : 0 < sC) :
    (∃ ib φπ φy : ℝ, ∀ s : ℝ × ℝ × ℝ × ℝ,
        rReq σ ω ν sC ρG ρc ρa ρh s = ib + φπ * 0 + φy * yReq σ ω ν sC s) ↔
      ω * (1 - ρG) = ω * (1 - ρc) ∧ ω * (1 - ρc) = (ρa - 1) / σ ∧ (ρa - 1) / σ = (ρh - 1) / σ := by
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ
  have hden : σ⁻¹ + ω ≠ 0 := by positivity
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hω0 : ω ≠ 0 := hω.ne'
  have hk : σ + ω⁻¹ ≠ 0 := by positivity
  constructor
  · rintro ⟨ib, φπ, φy, h⟩
    have h0 := h (0, 0, 0, 0)
    have h1 := h (1, 0, 0, 0)
    have h2 := h (0, 1, 0, 0)
    have h3 := h (0, 0, 1, 0)
    have h4 := h (0, 0, 0, 1)
    simp only [rReq, yReq, ynLin, gLin, qLin] at h0 h1 h2 h3 h4
    have hib : ib = 0 := by simpa using h0.symm
    subst hib
    field_simp at h1 h2 h3 h4
    have hpos : 0 < 1 + σ * ω := by positivity
    have e1 : φy = ω * (1 - ρG) := by
      have : (1 + σ * ω) * (ω * (1 - ρG) - φy) = 0 := by linear_combination h1
      have := (mul_eq_zero.mp this).resolve_left hpos.ne'
      linarith
    have e2 : φy = ω * (1 - ρc) := by
      have : (sC * (1 + σ * ω)) * (ω * (1 - ρc) - φy) = 0 := by linear_combination h2
      have := (mul_eq_zero.mp this).resolve_left (by positivity)
      linarith
    have e3 : φy = (ρa - 1) / σ := by
      have : ((1 + σ * ω) * (ω + 1)) * (-(1 - ρa) - φy * σ) = 0 := by linear_combination h3
      have := (mul_eq_zero.mp this).resolve_left (by positivity)
      field_simp
      linarith
    have e4 : φy = (ρh - 1) / σ := by
      have : ((1 + σ * ω) * ν) * (-(1 - ρh) - φy * σ) = 0 := by linear_combination h4
      have := (mul_eq_zero.mp this).resolve_left (by positivity)
      field_simp
      linarith
    exact ⟨by rw [← e1, ← e2], by rw [← e2, ← e3], by rw [← e3, ← e4]⟩
  · rintro ⟨h12, h23, h34⟩
    have hc : ρc = ρG := by
      have := mul_left_cancel₀ hω0 h12
      linarith
    have ha : ρa = 1 + σ * (ω * (1 - ρG)) := by
      rw [← hc] at h12 ⊢
      field_simp at h23
      linarith
    have hh : ρh = ρa := by
      field_simp at h34
      linarith
    refine ⟨0, 0, ω * (1 - ρG), fun s => ?_⟩
    simp only [rReq, yReq, ynLin, gLin, qLin, hc, hh, ha]
    field_simp
    ring

/-- Woodford (2003), p. 251 (**no simple Taylor rule implements price stability**): if some
demand-side disturbance (`Ĝ` or `c̄`) and some supply-side disturbance (`a` or `h̄`) are
transitory (`ρ < 1`), no rule `î = ī + φ_π π + φ_y Ŷ` with constant coefficients delivers
`î = r̂ⁿ` in the price-stable equilibrium: interest rates must move procyclically with the
demand shocks and countercyclically with the supply shocks, while `Ŷⁿ` rises with all four. -/
theorem no_simple_rule {σ ω ν sC ρG ρc ρa ρh : ℝ} (hσ : 0 < σ) (hω : 0 < ω) (hν : 0 < ν)
    (hsC : 0 < sC) (hdem : ρG < 1 ∨ ρc < 1) (hsup : ρa < 1 ∨ ρh < 1) :
    ¬ ∃ ib φπ φy : ℝ, ∀ s : ℝ × ℝ × ℝ × ℝ,
        rReq σ ω ν sC ρG ρc ρa ρh s = ib + φπ * 0 + φy * yReq σ ω ν sC s := by
  intro hex
  obtain ⟨h12, h23, h34⟩ := (simple_rule_iff hσ hω hν hsC).mp hex
  have hpos : 0 < ω * (1 - ρc) := by
    rcases hdem with h | h
    · rw [← h12]; exact mul_pos hω (by linarith)
    · exact mul_pos hω (by linarith)
  have hneg : (ρa - 1) / σ < 0 := by
    rcases hsup with h | h
    · exact div_neg_of_neg_of_pos (by linarith) hσ
    · rw [h34]; exact div_neg_of_neg_of_pos (by linarith) hσ
  linarith

/-- Woodford (2003), p. 251 (**the exact condition under stationarity**): if `ρ_G ≤ 1` and
`ρ_a ≤ 1` (in particular if every `ρ ≤ 1`), a simple rule implements price stability iff every
disturbance is a unit-root process
(`ρ_G = ρ_c = ρ_a = ρ_h = 1`), in which case `r̂ⁿ ≡ 0` and `φ_y = 0` works. -/
theorem simple_rule_iff_unit_roots {σ ω ν sC ρG ρc ρa ρh : ℝ} (hσ : 0 < σ) (hω : 0 < ω)
    (hν : 0 < ν) (hsC : 0 < sC) (hG : ρG ≤ 1) (ha : ρa ≤ 1) :
    (∃ ib φπ φy : ℝ, ∀ s : ℝ × ℝ × ℝ × ℝ,
        rReq σ ω ν sC ρG ρc ρa ρh s = ib + φπ * 0 + φy * yReq σ ω ν sC s) ↔
      ρG = 1 ∧ ρc = 1 ∧ ρa = 1 ∧ ρh = 1 := by
  rw [simple_rule_iff hσ hω hν hsC]
  constructor
  · rintro ⟨h12, h23, h34⟩
    have h1 : 0 ≤ ω * (1 - ρG) := mul_nonneg hω.le (by linarith)
    have h2 : (ρa - 1) / σ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hσ.le
    have hz : ω * (1 - ρG) = 0 := by linarith
    have hG1 : ρG = 1 := by
      have := (mul_eq_zero.mp hz).resolve_left hω.ne'
      linarith
    have hc1 : ρc = 1 := by
      have : ω * (1 - ρc) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hω.ne'
      linarith
    have ha1 : ρa = 1 := by
      have : (ρa - 1) / σ = 0 := by linarith
      rcases div_eq_zero_iff.mp this with h | h
      · linarith
      · exact absurd h hσ.ne'
    have hh1 : ρh = 1 := by
      have : (ρh - 1) / σ = 0 := by rw [← h34, ha1]; simp
      rcases div_eq_zero_iff.mp this with h | h
      · linarith
      · exact absurd h hσ.ne'
    exact ⟨hG1, hc1, ha1, hh1⟩
  · rintro ⟨h1, h2, h3, h4⟩
    subst h1 h2 h3 h4
    simp

/-- Woodford (2003), p. 251 ("in general"): with a single type of disturbance a simple rule
does work — e.g. if only `Ĝ` varies, `î = ω(1 − ρ_G) Ŷ` delivers `î = r̂ⁿ` (`σ, ω > 0`). -/
theorem simple_rule_single_shock {σ ω ν sC ρG ρc ρa ρh : ℝ} (hσ : 0 < σ) (hω : 0 < ω) (G : ℝ) :
    rReq σ ω ν sC ρG ρc ρa ρh (G, 0, 0, 0) = ω * (1 - ρG) * yReq σ ω ν sC (G, 0, 0, 0) := by
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ
  have hden : σ⁻¹ + ω ≠ 0 := by positivity
  have hk : σ + ω⁻¹ ≠ 0 := by positivity
  have hω0 : ω ≠ 0 := hω.ne'
  simp only [rReq, yReq, ynLin, gLin, qLin]
  field_simp
  ring

/-! ### Regularity of the natural rate (the implicit-function step) -/


/-- Woodford (2003), Ch. 3, p. 152: the root `n(z)` of an equation `F(k, z) = 0` that is strictly
increasing in `k` and continuous in `z` at `z₀` is continuous at `z₀` (continuity of the natural
rate in the shocks).
(Restated from the Chapter 3 project.) -/
theorem root_continuousAt {Z : Type*} [TopologicalSpace Z] {F : ℝ → Z → ℝ} {n : Z → ℝ}
    {z₀ : Z} (hmono : ∀ z, StrictMono fun k => F k z)
    (hcont : ∀ k, ContinuousAt (fun z => F k z) z₀) (hroot : ∀ z, F (n z) z = 0) :
    ContinuousAt n z₀ := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h0 : F a z₀ < 0 := by rw [← hroot z₀]; exact hmono z₀ ha
    filter_upwards [(hcont a).eventually (gt_mem_nhds h0)] with z hz
    by_contra hle
    push Not at hle
    have := (hmono z).monotone hle
    rw [hroot z] at this
    linarith
  · have h0 : 0 < F b z₀ := by rw [← hroot z₀]; exact hmono z₀ hb
    filter_upwards [(hcont b).eventually (lt_mem_nhds h0)] with z hz
    by_contra hle
    push Not at hle
    have := (hmono z).monotone hle
    rw [hroot z] at this
    linarith

/-- Woodford (2003), Ch. 3, p. 152 (the implicit-function step behind (1.15), proved here): let
`H(k, z)` be differentiable at `0` with `κ = ∂H/∂k ≠ 0`, and let `n` be continuous at `0` with
`n(0) = 0` and `H(n(z), z) = H(0)` near `0`. Then `n` is differentiable at `0` with
`Dn = −κ⁻¹ ∂H/∂z`.
(Restated from the Chapter 3 project.) -/
theorem implicit_hasFDerivAt {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {H : ℝ × Z → ℝ} {D : ℝ × Z →L[ℝ] ℝ} (hH : HasFDerivAt H D 0) (hκ : D (1, 0) ≠ 0)
    {n : Z → ℝ} (hn : ContinuousAt n 0) (hn0 : n 0 = 0)
    (hroot : ∀ᶠ z in 𝓝 (0 : Z), H (n z, z) = H 0) :
    HasFDerivAt n (-(D (1, 0))⁻¹ • D.comp (ContinuousLinearMap.inr ℝ ℝ Z)) 0 := by
  set κ := D (1, 0) with hκdef
  have hsplit : ∀ z, D (n z, z) = κ * n z + D (0, z) := by
    intro z
    have : ((n z, z) : ℝ × Z) = n z • ((1 : ℝ), (0 : Z)) + ((0 : ℝ), z) := by simp
    rw [this, map_add, map_smul, smul_eq_mul, hκdef]
    ring
  have hφ : Tendsto (fun z : Z => ((n z, z) : ℝ × Z)) (𝓝 0) (𝓝 0) := by
    have := hn.tendsto.prodMk_nhds (tendsto_id (x := 𝓝 (0 : Z)))
    rw [hn0] at this
    exact this
  have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hH).comp_tendsto hφ
  have he : (fun z => D (n z, z)) =o[𝓝 (0 : Z)] (fun z => ((n z, z) : ℝ × Z)) := by
    refine ho.neg_left.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hroot] with z hz
    simp only [Function.comp_apply, zero_add, hz]
    ring
  have hκpos : 0 < |κ| := abs_pos.2 hκ
  set C := 1 + 2 * ‖D‖ / |κ| with hC
  have hbig : (fun z => ((n z, z) : ℝ × Z)) =O[𝓝 (0 : Z)] (fun z => z) := by
    refine Asymptotics.IsBigO.of_bound (max C 1) ?_
    filter_upwards [he.def (c := |κ| / 2) (by positivity)] with z hz
    have hD0 : ‖D (0, z)‖ ≤ ‖D‖ * ‖z‖ := by
      have := D.le_opNorm (0, z)
      simpa using this
    rw [Prod.norm_mk] at hz ⊢
    rw [hsplit] at hz
    set a := ‖n z‖
    set b := ‖z‖
    have hb : 0 ≤ b := norm_nonneg _
    have ha : 0 ≤ a := norm_nonneg _
    have hka : |κ| * a ≤ |κ| / 2 * (a + b) + ‖D‖ * b := by
      have h1 : |κ| * a = ‖κ * n z‖ := by rw [norm_mul, Real.norm_eq_abs]
      have h2 : ‖κ * n z‖ ≤ ‖κ * n z + D (0, z)‖ + ‖D (0, z)‖ := by
        have := norm_sub_le (κ * n z + D (0, z)) (D (0, z))
        simpa using this
      have h3 : max a b ≤ a + b := max_le (by linarith) (by linarith)
      nlinarith
    have hac : a ≤ C * b := by
      have : |κ| * a ≤ |κ| * (C * b) := by
        have e : |κ| * (C * b) = |κ| * b + 2 * ‖D‖ * b := by
          rw [hC]; field_simp
        rw [e]
        linarith
      exact le_of_mul_le_mul_left this hκpos
    refine max_le (hac.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hb)) ?_
    calc b = 1 * b := (one_mul b).symm
      _ ≤ max C 1 * b := mul_le_mul_of_nonneg_right (le_max_right _ _) hb
  have he' := (he.trans_isBigO hbig).const_mul_left κ⁻¹
  have hL : ∀ z : Z, (-(D (1, 0))⁻¹ • D.comp (ContinuousLinearMap.inr ℝ ℝ Z)) z
      = -κ⁻¹ * D (0, z) := fun z => rfl
  refine hasFDerivAt_iff_isLittleO_nhds_zero.2 (he'.congr_left fun z => ?_)
  rw [hL, zero_add, hn0, sub_zero, hsplit]
  field_simp
  ring

/-- Woodford (2003), p. 249: at the steady state `natRateLog` vanishes. -/
theorem natRateLog_zero (vh : ℝ × ℝ → ℝ) (H H' : ℝ → ℝ) (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ)
    (d : ℝ × ℝ × ℝ × ℝ) : natRateLog vh H H' uc Ybar Gbar d 0 0 = 0 := by
  simp [natRateLog]

/-- Woodford (2003), p. 249 (**`natRateLog` is jointly differentiable at the steady state**,
with `∂/∂y = ω + σ⁻¹`): under the differentiability hypotheses of `naturalOutput_deriv`, the map
`(y, ε) ↦ natRateLog(y, ε)` has a Fréchet derivative `D` at `0` with `D(1, 0) = ω + σ⁻¹`. -/
theorem natRateLog_hasFDerivAt {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (d : ℝ × ℝ × ℝ × ℝ) (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0))
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0)) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ => natRateLog vh H H' uc Ybar Gbar d p.1 p.2) D 0 ∧
        D (1, 0) = omegaN vh H H' vhh H2 Ybar + (sigmaIS uc Ybar Gbar ucc)⁻¹ := by
  obtain ⟨Gd, xc, a, xh⟩ := d
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ)) (F := ℝ)
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ)) (E := ℝ)
  set e : ℝ × ℝ → ℝ := fun p => Ybar * Real.exp (p.1 - p.2 * a) with he_def
  have he := ((hf.sub (hs.mul_const a)).exp).const_mul Ybar
  have he0 : e 0 = Ybar := by simp [he_def]
  have hHe := HasFDerivAt.comp (g := H) (f := e) (0 : ℝ × ℝ)
    (by rw [he0]; exact hH.hasFDerivAt) he
  have hH2e := HasFDerivAt.comp (g := H') (f := e) (0 : ℝ × ℝ)
    (by rw [he0]; exact hH2.hasFDerivAt) he
  set c1 : ℝ × ℝ → ℝ × ℝ := fun p => (H (e p), p.2 * xh) with hc1_def
  have hc1 := hHe.prodMk (hs.mul_const xh)
  have hc10 : c1 0 = (H Ybar, 0) := by simp [hc1_def, he0]
  have hV := (HasFDerivAt.comp (g := vh) (f := c1) (0 : ℝ × ℝ) (by rw [hc10]; exact hvh)
    hc1).log (by simp only [Function.comp_apply, hc10]; exact hvh0.ne')
  have hL := hH2e.log (by simp only [Function.comp_apply, he0]; exact hH'0.ne')
  set c2 : ℝ × ℝ → ℝ × ℝ := fun p => (Ybar * Real.exp p.1 - Gbar - Ybar * (p.2 * Gd), p.2 * xc)
    with hc2_def
  have hc2 := (((hf.exp).const_mul Ybar).sub_const Gbar |>.sub
    ((hs.mul_const Gd).const_mul Ybar)).prodMk (hs.mul_const xc)
  have hc20 : c2 0 = (Ybar - Gbar, 0) := by simp [hc2_def]
  have hU := (HasFDerivAt.comp (g := uc) (f := c2) (0 : ℝ × ℝ) (by rw [hc20]; exact huc)
    hc2).log (by simp only [Function.comp_apply, hc20]; exact hu.ne')
  have hall := (((hV.add hL).sub (hs.mul_const a)).sub hU).sub_const
    (Real.log (vh (H Ybar, 0)) + Real.log (H' Ybar) - Real.log (uc (Ybar - Gbar, 0)))
  refine ⟨_, hall, ?_⟩
  simp only [Function.comp_apply, Pi.sub_apply, Prod.fst_zero, Prod.snd_zero, zero_mul, sub_self,
    Real.exp_zero, one_smul, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.fst_comp_prod, ContinuousLinearMap.snd_comp_prod, smul_add,
    sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul, ContinuousLinearMap.coe_snd',
    mul_zero, sub_zero, add_zero, mul_one, hc10, hc20, he_def]
  unfold omegaN nuL sigmaIS
  have hC' : Ybar - Gbar ≠ 0 := hC.ne'
  field_simp
  ring

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 249 (**the natural rate is differentiable, and its
derivative is (2.2)**): if the natural-rate path `yn` (solving `natRateLog = 0`, `yn 0 = 0`) is
continuous at `0` (e.g. by `root_continuousAt`, when real marginal cost is strictly increasing in
output), and `ω ≠ 0`, `σ⁻¹ + ω ≠ 0`, then `yn` is differentiable at `0` with derivative
`(σ⁻¹ g + ω q)/(σ⁻¹ + ω)`. -/
theorem natRate_hasDerivAt {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (d : ℝ × ℝ × ℝ × ℝ) (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0)) (hvhh : vhh ≠ 0) (hcc : ucc ≠ 0)
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    {yn : ℝ → ℝ} (hcont : ContinuousAt yn 0) (hyn0 : yn 0 = 0)
    (himp : ∀ ε, natRateLog vh H H' uc Ybar Gbar d (yn ε) ε = 0)
    (hω : omegaN vh H H' vhh H2 Ybar ≠ 0)
    (hden : (sigmaIS uc Ybar Gbar ucc)⁻¹ + omegaN vh H H' vhh H2 Ybar ≠ 0) :
    HasDerivAt yn (ynLin (sigmaIS uc Ybar Gbar ucc) (omegaN vh H H' vhh H2 Ybar)
      (gLin ((Ybar - Gbar) / Ybar) d.1 (-ucxi / ((Ybar - Gbar) * ucc) * d.2.1))
      (qLin (omegaN vh H H' vhh H2 Ybar) (nuL vh H vhh Ybar) d.2.2.1
        (hbarC H vhh vhxi Ybar * d.2.2.2))) 0 := by
  obtain ⟨D, hD, hD10⟩ := natRateLog_hasFDerivAt d hY hC hHb hvh0 hH'0 hu hH hH2 hvh huc
  have hκ : D (1, 0) ≠ 0 := by rw [hD10, add_comm]; exact hden
  have hroot : ∀ᶠ z in 𝓝 (0 : ℝ),
      (fun p : ℝ × ℝ => natRateLog vh H H' uc Ybar Gbar d p.1 p.2) (yn z, z) =
        (fun p : ℝ × ℝ => natRateLog vh H H' uc Ybar Gbar d p.1 p.2) 0 :=
    Filter.Eventually.of_forall fun z => by
      simp only [himp z, Prod.fst_zero, Prod.snd_zero, natRateLog_zero]
  have hF := implicit_hasFDerivAt hD hκ hcont hyn0 hroot
  have hd := hF.hasDerivAt
  have hval := natRate_eq22 d hY hC hHb hvh0 hH'0 hu hvhh hcc hH hH2 hvh huc hd hyn0 himp hω hden
  rw [← hval]
  exact hd

/-- Woodford (2003), p. 151 (Chapter 3) and p. 249 (**the natural rate from monotone real
marginal cost**): if real marginal cost is strictly increasing in output along the diagonal
(`natRateLog` strictly increasing in `y` for every `ε`) and continuous in the disturbance at
`ε = 0`, the natural-rate path is continuous at `0` (`root_continuousAt`), so
`natRate_hasDerivAt` applies: `yn` is differentiable with derivative (2.2). -/
theorem natRate_hasDerivAt_of_mono {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (d : ℝ × ℝ × ℝ × ℝ) (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0)) (hvhh : vhh ≠ 0) (hcc : ucc ≠ 0)
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (hmono : ∀ ε, StrictMono fun y => natRateLog vh H H' uc Ybar Gbar d y ε)
    (hcε : ∀ y, ContinuousAt (fun ε => natRateLog vh H H' uc Ybar Gbar d y ε) 0)
    {yn : ℝ → ℝ} (hyn0 : yn 0 = 0) (himp : ∀ ε, natRateLog vh H H' uc Ybar Gbar d (yn ε) ε = 0)
    (hω : omegaN vh H H' vhh H2 Ybar ≠ 0)
    (hden : (sigmaIS uc Ybar Gbar ucc)⁻¹ + omegaN vh H H' vhh H2 Ybar ≠ 0) :
    HasDerivAt yn (ynLin (sigmaIS uc Ybar Gbar ucc) (omegaN vh H H' vhh H2 Ybar)
      (gLin ((Ybar - Gbar) / Ybar) d.1 (-ucxi / ((Ybar - Gbar) * ucc) * d.2.1))
      (qLin (omegaN vh H H' vhh H2 Ybar) (nuL vh H vhh Ybar) d.2.2.1
        (hbarC H vhh vhxi Ybar * d.2.2.2))) 0 :=
  natRate_hasDerivAt d hY hC hHb hvh0 hH'0 hu hvhh hcc hH hH2 hvh huc
    (root_continuousAt (F := fun y ε => natRateLog vh H H' uc Ybar Gbar d y ε) hmono hcε himp)
    hyn0 himp hω hden

/-! ### Existence, uniqueness and smoothness of the natural rate -/

/-- Woodford (2003), Ch. 3, eq. (1.14), p. 151 (**existence and uniqueness of `Yⁿ`, minimal
conditions**): if `S(Y) = s(Y, Y; ξ̃)` is continuous and strictly increasing on `(0, ∞)`, then
`S(Yⁿ) = c` has a unique positive solution iff `c` lies between two values of `S` (a boundary
condition the book omits). (Restated from the Chapter 3 project.) -/
theorem naturalRate_existsUnique_iff {Sd : ℝ → ℝ} {c : ℝ} (hc : ContinuousOn Sd (Set.Ioi 0))
    (hm : StrictMonoOn Sd (Set.Ioi 0)) :
    (∃! Yn, 0 < Yn ∧ Sd Yn = c) ↔
      ∃ Y₁ Y₂, 0 < Y₁ ∧ 0 < Y₂ ∧ Sd Y₁ ≤ c ∧ c ≤ Sd Y₂ := by
  constructor
  · rintro ⟨Yn, ⟨hYn, hS⟩, -⟩
    exact ⟨Yn, Yn, hYn, hYn, hS.le, hS.ge⟩
  · rintro ⟨Y₁, Y₂, h₁, h₂, hS₁, hS₂⟩
    have hle : Y₁ ≤ Y₂ := by
      by_contra hlt
      push Not at hlt
      have := hm h₂ h₁ hlt
      linarith
    obtain ⟨Yn, hYn, hSn⟩ := intermediate_value_Icc hle
      (hc.mono fun y hy => lt_of_lt_of_le h₁ hy.1) ⟨hS₁, hS₂⟩
    have hpos : 0 < Yn := lt_of_lt_of_le h₁ hYn.1
    exact ⟨Yn, ⟨hpos, hSn⟩, fun Z ⟨hZ, hSZ⟩ => hm.injOn hZ hpos (hSZ.trans hSn.symm)⟩

/-- Woodford (2003), Ch. 3, eq. (1.14), p. 151 (a case where the natural rate exists): if
`s(Y, Y) = κ Y^e` with `κ, e > 0`, then `s(Yⁿ, Yⁿ) = c > 0` has the unique solution
`Yⁿ = (c/κ)^{1/e}`. (Restated from the Chapter 3 project.) -/
theorem isoelastic_naturalRate {κ e c : ℝ} (hκ : 0 < κ) (he : 0 < e) (hc : 0 < c) :
    ∃! Yn, 0 < Yn ∧ κ * Yn ^ e = c := by
  have hck : 0 < c / κ := div_pos hc hκ
  refine ⟨(c / κ) ^ (1 / e), ⟨Real.rpow_pos_of_pos hck _, ?_⟩, fun Y ⟨hY, hYe⟩ => ?_⟩
  · rw [one_div, Real.rpow_inv_rpow hck.le he.ne']
    field_simp
  · have : Y ^ e = c / κ := by rw [← hYe]; field_simp
    rw [← this, one_div, Real.rpow_rpow_inv hY.le he.ne']

/-- Woodford (2003), p. 249 (the natural rate in logs, existence and uniqueness): a continuous,
strictly increasing `F : ℝ → ℝ` has a unique zero iff it takes a nonpositive and a nonnegative
value (the boundary condition). -/
theorem root_existsUnique_iff {F : ℝ → ℝ} (hc : Continuous F) (hm : StrictMono F) :
    (∃! y, F y = 0) ↔ ∃ y₁ y₂, F y₁ ≤ 0 ∧ 0 ≤ F y₂ := by
  constructor
  · rintro ⟨y, hy, -⟩
    exact ⟨y, y, hy.le, hy.ge⟩
  · rintro ⟨y₁, y₂, h₁, h₂⟩
    have hle : y₁ ≤ y₂ := by
      by_contra hlt
      push Not at hlt
      have := hm hlt
      linarith
    obtain ⟨y, -, hFy⟩ := intermediate_value_Icc hle hc.continuousOn ⟨h₁, h₂⟩
    exact ⟨y, hFy, fun z hz => hm.injective (hz.trans hFy.symm)⟩

/-- Woodford (2003), p. 249 (**the natural-rate function exists and is unique**): if for every
disturbance `s` the map `y ↦ Φ(s, y)` is continuous, strictly increasing and satisfies the
boundary condition, there is exactly one function `ŷⁿ` with `Φ(s, ŷⁿ(s)) = 0` for all `s`. -/
theorem root_function_existsUnique {S : Type*} {Φ : S → ℝ → ℝ} (hc : ∀ s, Continuous (Φ s))
    (hm : ∀ s, StrictMono (Φ s)) (hb : ∀ s, ∃ y₁ y₂, Φ s y₁ ≤ 0 ∧ 0 ≤ Φ s y₂) :
    ∃! yn : S → ℝ, ∀ s, Φ s (yn s) = 0 := by
  have h := fun s => (root_existsUnique_iff (hc s) (hm s)).mpr (hb s)
  refine ⟨fun s => (h s).exists.choose, fun s => (h s).exists.choose_spec, fun yn hyn => ?_⟩
  funext s
  exact (h s).unique (hyn s) (h s).exists.choose_spec

/-- Woodford (2003), p. 249: the log natural-rate condition as a function of the disturbance
vector `s = (Ĝ, ξ_c, a, ξ_h)` and log output `y`: `natRateLog` along `ε d` is
`natRateF (ε d, y)` (`natRateLog_eq_F`). -/
noncomputable def natRateF (vh : ℝ × ℝ → ℝ) (H H' : ℝ → ℝ) (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ)
    (p : (ℝ × ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  Real.log (vh (H (Ybar * Real.exp (p.2 - p.1.2.2.1)), p.1.2.2.2)) +
    Real.log (H' (Ybar * Real.exp (p.2 - p.1.2.2.1))) - p.1.2.2.1 -
    Real.log (uc (Ybar * Real.exp p.2 - Gbar - Ybar * p.1.1, p.1.2.1)) -
    (Real.log (vh (H Ybar, 0)) + Real.log (H' Ybar) - Real.log (uc (Ybar - Gbar, 0)))

/-- Woodford (2003), p. 249: `natRateLog d y ε = natRateF (ε • d, y)`. -/
theorem natRateLog_eq_F (vh : ℝ × ℝ → ℝ) (H H' : ℝ → ℝ) (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ)
    (d : ℝ × ℝ × ℝ × ℝ) (y ε : ℝ) :
    natRateLog vh H H' uc Ybar Gbar d y ε = natRateF vh H H' uc Ybar Gbar (ε • d, y) := by
  obtain ⟨a, b, c, e⟩ := d
  simp [natRateLog, natRateF]

/-- Woodford (2003), p. 249: `natRateF` vanishes at the steady state. -/
theorem natRateF_zero (vh : ℝ × ℝ → ℝ) (H H' : ℝ → ℝ) (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ) :
    natRateF vh H H' uc Ybar Gbar 0 = 0 := by
  simp [natRateF]

/-- Woodford (2003), p. 249: if `y ↦ natRateF (0, y)` is injective, the natural rate at zero
disturbances is the steady state, `ŷⁿ(0) = 0`. -/
theorem natRate_zero_of_root {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ} {Ybar Gbar : ℝ}
    {yn : ℝ × ℝ × ℝ × ℝ → ℝ}
    (hinj : Function.Injective fun y => natRateF vh H H' uc Ybar Gbar (0, y))
    (hroot : natRateF vh H H' uc Ybar Gbar (0, yn 0) = 0) : yn 0 = 0 :=
  hinj (by
    change natRateF vh H H' uc Ybar Gbar (0, yn 0) = natRateF vh H H' uc Ybar Gbar (0, 0)
    rw [hroot, Prod.mk_zero_zero, natRateF_zero])

/-- Woodford (2003), p. 249: a continuous linear map `ℝ → ℝ` with `L 1 ≠ 0` is invertible. -/
theorem isInvertible_of_apply_one_ne {L : ℝ →L[ℝ] ℝ} (h : L 1 ≠ 0) : L.IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
  · ext
    simp [h]
  · ext
    simp [h]

/-- Woodford (2003), p. 249 (**the implicit-function step, with smoothness**): let `F : S × ℝ → ℝ`
be `C²` at `0` with `F 0 = 0` and `∂F/∂y (0) ≠ 0`, and let `ŷⁿ` solve `F(s, ŷⁿ(s)) = 0` for every
`s`, with `F(s, ·)` injective. Then `ŷⁿ` is `C²` at `0` (Mathlib's implicit-function theorem
with `ContDiff`). -/
theorem root_contDiffAt {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    {F : S × ℝ → ℝ} (hF : ContDiffAt ℝ 2 F 0) (hF0 : F 0 = 0)
    (hκ : fderiv ℝ F 0 ((0 : S), (1 : ℝ)) ≠ 0) {yn : S → ℝ} (hroot : ∀ s, F (s, yn s) = 0)
    (hinj : ∀ s, Function.Injective fun y => F (s, y)) : ContDiffAt ℝ 2 yn 0 := by
  have pn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have if₂ : (fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ S ℝ).IsInvertible :=
    isInvertible_of_apply_one_ne (by simpa using hκ)
  have hψ := hF.contDiffAt_implicitFunction pn if₂
  have hev := hF.eventually_apply_implicitFunction pn if₂
  rw [hF0] at hev
  rw [Prod.fst_zero] at hψ hev
  refine hψ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with s hs
  exact hinj s ((hroot s).trans hs.symm)

/-- Woodford (2003), p. 249: `natRateF` is `C²` at the steady state when `v_h`, `H`, `H'` and `u_c`
are `C²` there and the relevant values are positive. -/
theorem natRateF_contDiffAt {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ} {Ybar Gbar : ℝ}
    (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar) (hu : 0 < uc (Ybar - Gbar, 0))
    (hvh2 : ContDiffAt ℝ 2 vh (H Ybar, 0)) (hHc : ContDiffAt ℝ 2 H Ybar)
    (hH'c : ContDiffAt ℝ 2 H' Ybar) (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0)) :
    ContDiffAt ℝ 2 (natRateF vh H H' uc Ybar Gbar) 0 := by
  set e : (ℝ × ℝ × ℝ × ℝ) × ℝ → ℝ := fun p => Ybar * Real.exp (p.2 - p.1.2.2.1) with he
  have ha : ContDiff ℝ 2 fun p : (ℝ × ℝ × ℝ × ℝ) × ℝ => p.1.2.2.1 :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))
  have hec : ContDiff ℝ 2 e := contDiff_const.mul (Real.contDiff_exp.comp (contDiff_snd.sub ha))
  have he0 : e 0 = Ybar := by simp [he]
  have hHe : ContDiffAt ℝ 2 (H ∘ e) 0 :=
    ContDiffAt.comp (0 : (ℝ × ℝ × ℝ × ℝ) × ℝ) (by rw [he0]; exact hHc) hec.contDiffAt
  have hH'e : ContDiffAt ℝ 2 (H' ∘ e) 0 :=
    ContDiffAt.comp (0 : (ℝ × ℝ × ℝ × ℝ) × ℝ) (by rw [he0]; exact hH'c) hec.contDiffAt
  set c1 : (ℝ × ℝ × ℝ × ℝ) × ℝ → ℝ × ℝ := fun p => (H (e p), p.1.2.2.2) with hc1
  have hc1c : ContDiffAt ℝ 2 c1 0 := hHe.prodMk
    (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))).contDiffAt
  have hc10 : c1 0 = (H Ybar, 0) := by simp [hc1, he0]
  have hV : ContDiffAt ℝ 2 (vh ∘ c1) 0 :=
    ContDiffAt.comp (0 : (ℝ × ℝ × ℝ × ℝ) × ℝ) (by rw [hc10]; exact hvh2) hc1c
  set c2 : (ℝ × ℝ × ℝ × ℝ) × ℝ → ℝ × ℝ :=
    fun p => (Ybar * Real.exp p.2 - Gbar - Ybar * p.1.1, p.1.2.1) with hc2
  have hc2c : ContDiffAt ℝ 2 c2 0 := by
    refine ContDiff.contDiffAt (ContDiff.prodMk ?_ ?_)
    · exact ((contDiff_const.mul (Real.contDiff_exp.comp contDiff_snd)).sub contDiff_const).sub
        (contDiff_const.mul (contDiff_fst.comp contDiff_fst))
    · exact contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
  have hc20 : c2 0 = (Ybar - Gbar, 0) := by simp [hc2]
  have hU : ContDiffAt ℝ 2 (uc ∘ c2) 0 :=
    ContDiffAt.comp (0 : (ℝ × ℝ × ℝ × ℝ) × ℝ) (by rw [hc20]; exact huc2) hc2c
  have hVl := hV.log (by simp only [Function.comp_apply, hc10]; exact hvh0.ne')
  have hLl := hH'e.log (by simp only [Function.comp_apply, he0]; exact hH'0.ne')
  have hUl := hU.log (by simp only [Function.comp_apply, hc20]; exact hu.ne')
  exact (((hVl.add hLl).sub ha.contDiffAt).sub hUl).sub contDiffAt_const

/-- Woodford (2003), p. 249: the partial derivative of `natRateF` in log output at the steady state
is `ω + σ⁻¹` (via `natRateLog_hasFDerivAt` along the zero disturbance direction). -/
theorem natRateF_fderiv_y {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0))
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (hdiff : DifferentiableAt ℝ (natRateF vh H H' uc Ybar Gbar) 0) :
    fderiv ℝ (natRateF vh H H' uc Ybar Gbar) 0 ((0 : ℝ × ℝ × ℝ × ℝ), (1 : ℝ)) =
      omegaN vh H H' vhh H2 Ybar + (sigmaIS uc Ybar Gbar ucc)⁻¹ := by
  obtain ⟨D, hD, hD10⟩ :=
    natRateLog_hasFDerivAt (0 : ℝ × ℝ × ℝ × ℝ) hY hC hHb hvh0 hH'0 hu hH hH2 hvh huc
  set L : ℝ × ℝ →L[ℝ] (ℝ × ℝ × ℝ × ℝ) × ℝ :=
    (0 : ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ × ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) with hL
  have hL0 : L 0 = 0 := map_zero L
  have hcomp : HasFDerivAt (natRateF vh H H' uc Ybar Gbar ∘ L)
      ((fderiv ℝ (natRateF vh H H' uc Ybar Gbar) 0).comp L) 0 := by
    have h1 := hdiff.hasFDerivAt
    rw [← hL0] at h1
    exact h1.comp 0 L.hasFDerivAt
  have hfun : (fun p : ℝ × ℝ => natRateLog vh H H' uc Ybar Gbar 0 p.1 p.2) =
      natRateF vh H H' uc Ybar Gbar ∘ L := by
    funext p
    simp [natRateLog_eq_F, hL]
  rw [hfun] at hD
  rw [← hD10, hD.unique hcomp]
  simp [hL]

/-- Woodford (2003), p. 249 (**the natural rate of output is `C²` in the disturbances**): with
`C²` primitives, `σ⁻¹ + ω ≠ 0`, and `ŷⁿ` the (unique, by injectivity) root of
`natRateF (s, ·) = 0` for every disturbance vector `s`, the natural rate `ŷⁿ` is `C²` at `0`. -/
theorem natRate_contDiffAt {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0))
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (hvh2 : ContDiffAt ℝ 2 vh (H Ybar, 0)) (hHc : ContDiffAt ℝ 2 H Ybar)
    (hH'c : ContDiffAt ℝ 2 H' Ybar) (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0))
    (hden : (sigmaIS uc Ybar Gbar ucc)⁻¹ + omegaN vh H H' vhh H2 Ybar ≠ 0)
    {yn : ℝ × ℝ × ℝ × ℝ → ℝ} (hroot : ∀ s, natRateF vh H H' uc Ybar Gbar (s, yn s) = 0)
    (hinj : ∀ s, Function.Injective fun y => natRateF vh H H' uc Ybar Gbar (s, y)) :
    ContDiffAt ℝ 2 yn 0 := by
  have hF := natRateF_contDiffAt hvh0 hH'0 hu hvh2 hHc hH'c huc2
  refine root_contDiffAt hF (natRateF_zero vh H H' uc Ybar Gbar) ?_ hroot hinj
  rw [natRateF_fderiv_y hY hC hHb hvh0 hH'0 hu hH hH2 hvh huc
    (hF.differentiableAt (by norm_num)), add_comm]
  exact hden

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 249 (**the derivative of the natural-rate function**):
under the hypotheses of `natRate_contDiffAt` (and `ω ≠ 0`, `v_hh, u_cc ≠ 0`), for every
disturbance direction `d = (Ĝ, ξ_c, a, ξ_h)`, `Dŷⁿ(0) d = (σ⁻¹ g + ω q)/(σ⁻¹ + ω)`. -/
theorem natRate_fderiv_eq22 {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0)) (hvhh : vhh ≠ 0) (hcc : ucc ≠ 0)
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (hvh2 : ContDiffAt ℝ 2 vh (H Ybar, 0)) (hHc : ContDiffAt ℝ 2 H Ybar)
    (hH'c : ContDiffAt ℝ 2 H' Ybar) (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0))
    (hω : omegaN vh H H' vhh H2 Ybar ≠ 0)
    (hden : (sigmaIS uc Ybar Gbar ucc)⁻¹ + omegaN vh H H' vhh H2 Ybar ≠ 0)
    {yn : ℝ × ℝ × ℝ × ℝ → ℝ} (hroot : ∀ s, natRateF vh H H' uc Ybar Gbar (s, yn s) = 0)
    (hinj : ∀ s, Function.Injective fun y => natRateF vh H H' uc Ybar Gbar (s, y))
    (d : ℝ × ℝ × ℝ × ℝ) :
    fderiv ℝ yn 0 d = ynLin (sigmaIS uc Ybar Gbar ucc) (omegaN vh H H' vhh H2 Ybar)
      (gLin ((Ybar - Gbar) / Ybar) d.1 (-ucxi / ((Ybar - Gbar) * ucc) * d.2.1))
      (qLin (omegaN vh H H' vhh H2 Ybar) (nuL vh H vhh Ybar) d.2.2.1
        (hbarC H vhh vhxi Ybar * d.2.2.2)) := by
  have hyn := natRate_contDiffAt hY hC hHb hvh0 hH'0 hu hH hH2 hvh huc hvh2 hHc hH'c huc2 hden
    hroot hinj
  have hyn0 : yn 0 = 0 := natRate_zero_of_root (hinj 0) (hroot 0)
  have hD := (hyn.differentiableAt (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun ε : ℝ => ε • d) d 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const d
  have hD' : HasFDerivAt yn (fderiv ℝ yn 0) ((fun ε : ℝ => ε • d) 0) := by simpa using hD
  have hcomp := hD'.comp_hasDerivAt (0 : ℝ) hpath
  exact natRate_eq22 d hY hC hHb hvh0 hH'0 hu hvhh hcc hH hH2 hvh huc hcomp
    (by simpa using hyn0) (fun ε => by rw [natRateLog_eq_F]; exact hroot _) hω hden

/-- Woodford (2003), p. 248: a continuous linear function of disturbances whose four coordinate
processes are adapted is adapted. -/
theorem adapted_clm (L : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ) {s : ℕ → Ω → ℝ × ℝ × ℝ × ℝ}
    (h1 : 𝔼.Adapted fun τ ω => (s τ ω).1) (h2 : 𝔼.Adapted fun τ ω => (s τ ω).2.1)
    (h3 : 𝔼.Adapted fun τ ω => (s τ ω).2.2.1) (h4 : 𝔼.Adapted fun τ ω => (s τ ω).2.2.2) :
    𝔼.Adapted fun τ ω => L (s τ ω) := by
  intro τ
  change 𝔼.E τ (fun ω => L (s τ ω)) = fun ω => L (s τ ω)
  have hfun : (fun ω => L (s τ ω)) = L (1, 0, 0, 0) • (fun ω => (s τ ω).1) +
      L (0, 1, 0, 0) • (fun ω => (s τ ω).2.1) + L (0, 0, 1, 0) • (fun ω => (s τ ω).2.2.1) +
      L (0, 0, 0, 1) • (fun ω => (s τ ω).2.2.2) := by
    funext ω
    have : s τ ω = (s τ ω).1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)) +
        (s τ ω).2.1 • ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) +
        (s τ ω).2.2.1 • ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ)) +
        (s τ ω).2.2.2 • ((0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [this]
    simp only [map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    ring
  rw [hfun]
  simp only [map_add, map_smul, h1 τ, h2 τ, h3 τ, h4 τ]

/-- Woodford (2003), p. 248 and eq. (1.15) (**the natural rate of interest as an exact
derivative, from primitives only**): with `C²` primitives `v_h, H, H', u_c` (positive, with the
stated partial derivatives), `σ⁻¹ + ω ≠ 0`, and `ŷⁿ` the natural-rate function (the unique root
of `natRateF (s, ·)`, e.g. from `root_function_existsUnique`), along bounded disturbance paths
`s_t` with adapted coordinates the log natural rate of interest has derivative
`r̂ⁿ_t = σ⁻¹[(g_t − Ŷⁿ_t) − E_t(g_{t+1} − Ŷⁿ_{t+1})]` with `Ŷⁿ_t = Dŷⁿ(0) s_t`,
`g_t = Ĝ_t + s_C c̄_t`. No regularity of `ŷⁿ` is assumed. -/
theorem natRate_log_deriv_primitives {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (hvh2 : ContDiffAt ℝ 2 vh (H Ybar, 0)) (hHc : ContDiffAt ℝ 2 H Ybar)
    (hH'c : ContDiffAt ℝ 2 H' Ybar) (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0))
    (hden : (sigmaIS uc Ybar Gbar ucc)⁻¹ + omegaN vh H H' vhh H2 Ybar ≠ 0)
    {yn : ℝ × ℝ × ℝ × ℝ → ℝ} (hroot : ∀ s, natRateF vh H H' uc Ybar Gbar (s, yn s) = 0)
    (hinj : ∀ s, Function.Injective fun y => natRateF vh H H' uc Ybar Gbar (s, y))
    {s : ℕ → Ω → ℝ × ℝ × ℝ × ℝ} {K : ℝ} (hs : ∀ τ ω, ‖s τ ω‖ ≤ K)
    (h1 : 𝔼.Adapted fun τ ω => (s τ ω).1) (h2 : 𝔼.Adapted fun τ ω => (s τ ω).2.1)
    (h3 : 𝔼.Adapted fun τ ω => (s τ ω).2.2.1) (h4 : 𝔼.Adapted fun τ ω => (s τ ω).2.2.2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε : ℝ => -Real.log (𝔼.E t (fun ω' => Real.exp
        (lambdaG uc Ybar Gbar (yn (ε • s (t + 1) ω'), (ε • s (t + 1) ω').1,
            (ε • s (t + 1) ω').2.1) -
          lambdaG uc Ybar Gbar (yn (ε • s t ω'), (ε • s t ω').1, (ε • s t ω').2.1))) ω))
      (rnHat 𝔼 (sigmaIS uc Ybar Gbar ucc)
        (fun τ ω => (s τ ω).1 + gcoef Ybar Gbar ucc ucxi * (s τ ω).2.1)
        (fun τ ω => fderiv ℝ yn 0 (s τ ω)) t ω) 0 := by
  have hyn := natRate_contDiffAt hY hC hHb hvh0 hH'0 hu hH hH2 hvh huc hvh2 hHc hH'c huc2 hden
    hroot hinj
  have hyn0 : yn 0 = 0 := natRate_zero_of_root (hinj 0) (hroot 0)
  set Gof : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)
  set xiof : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))
  have hga : 𝔼.Adapted (fun τ ω => Gof (s τ ω) + gcoef Ybar Gbar ucc ucxi * xiof (s τ ω)) := by
    have := adapted_clm 𝔼 (Gof + gcoef Ybar Gbar ucc ucxi • xiof) h1 h2 h3 h4
    simpa using this
  have hna := adapted_clm 𝔼 (fderiv ℝ yn 0) h1 h2 h3 h4
  have := natRate_deriv_rnHat 𝔼 hY hC hu hcc huc huc2 hyn
    (hyn.differentiableAt (by norm_num)).hasFDerivAt hyn0 Gof xiof hs hga hna t ω
  simpa [Gof, xiof] using this

/-- Woodford (2003), p. 249 (**existence, uniqueness and smoothness of the natural rate, from
primitives and boundary conditions**): if for every disturbance vector `s` real marginal cost
along the diagonal is continuous and strictly increasing in log output (`y ↦ natRateF (s, y)`)
and takes a value `≤ 0` and a value `≥ 0` (relative to `µ⁻¹`), there is exactly one natural-rate
function `ŷⁿ`; under the `C²` hypotheses of `natRate_contDiffAt` it satisfies `ŷⁿ(0) = 0` and is
`C²` at `0`. -/
theorem natRate_existsUnique_smooth {vh : ℝ × ℝ → ℝ} {H H' : ℝ → ℝ} {uc : ℝ × ℝ → ℝ}
    {Ybar Gbar vhh vhxi H2 ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hHb : 0 < H Ybar) (hvh0 : 0 < vh (H Ybar, 0)) (hH'0 : 0 < H' Ybar)
    (hu : 0 < uc (Ybar - Gbar, 0))
    (hH : HasDerivAt H (H' Ybar) Ybar) (hH2 : HasDerivAt H' H2 Ybar)
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (H Ybar, 0))
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (hvh2 : ContDiffAt ℝ 2 vh (H Ybar, 0)) (hHc : ContDiffAt ℝ 2 H Ybar)
    (hH'c : ContDiffAt ℝ 2 H' Ybar) (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0))
    (hden : (sigmaIS uc Ybar Gbar ucc)⁻¹ + omegaN vh H H' vhh H2 Ybar ≠ 0)
    (hcont : ∀ s, Continuous fun y => natRateF vh H H' uc Ybar Gbar (s, y))
    (hmono : ∀ s, StrictMono fun y => natRateF vh H H' uc Ybar Gbar (s, y))
    (hbdry : ∀ s, ∃ y₁ y₂, natRateF vh H H' uc Ybar Gbar (s, y₁) ≤ 0 ∧
      0 ≤ natRateF vh H H' uc Ybar Gbar (s, y₂)) :
    (∃! yn : ℝ × ℝ × ℝ × ℝ → ℝ, ∀ s, natRateF vh H H' uc Ybar Gbar (s, yn s) = 0) ∧
      ∀ yn : ℝ × ℝ × ℝ × ℝ → ℝ, (∀ s, natRateF vh H H' uc Ybar Gbar (s, yn s) = 0) →
        yn 0 = 0 ∧ ContDiffAt ℝ 2 yn 0 := by
  refine ⟨root_function_existsUnique (Φ := fun s y => natRateF vh H H' uc Ybar Gbar (s, y))
    hcont hmono hbdry, fun yn hroot => ⟨natRate_zero_of_root (hmono 0).injective (hroot 0), ?_⟩⟩
  exact natRate_contDiffAt hY hC hHb hvh0 hH'0 hu hH hH2 hvh huc hvh2 hHc hH'c huc2 hden hroot
    fun s => (hmono s).injective

end Woodford.NeoWicksellianFramework.NaturalRate
