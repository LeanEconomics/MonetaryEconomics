/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6CalvoPC
import KeynesianStickyPrices.TidyR6DerivedModel

/-!
# The derived model with Calvo price setting

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, eqs. (17.15)–(17.17),
p. 407, and Chapter 5, §5.1, p. 118 ("a random probability of being allowed to change price").

The economy of TidyR6DerivedModel with the Rotemberg price setter replaced by Calvo price setters
(TidyR6CalvoReset, TidyR6CalvoPC): the household chooses consumption and bonds; every period a
fraction `1 − α` of the yeoman farmers resets its price optimally; the CES price index evolves by
the Calvo law of motion (`TidyR6CalvoPC.Index`, derived from the cohort masses in
`TidyR6CalvoReset.index_eq_of_cohort`). Consumption equals the CES output aggregate, which is
also the household's real sales income, so price dispersion enters none of the equilibrium
conditions.

## Main results

* `eqm_iff_model_calvo`: the household is optimal and every resetting price setter resets
  optimally **iff** (17.15)–(17.17) hold at every date, with `σ = 1/γ`, the Calvo slope
  `κ = (1 − α)(1 − αβ)(γ + ϕ)/(α(1 + εϕ))` and the explicit second-order disturbances
  `u_x = TidyR6EulerIS.isRem`, `u_π = TidyR6CalvoPC.calvoRem`.
* `Tree.eqm_iff_model_calvo`: on a finite tree, the project's `FullModel.Model`.
* `calvo_steady_state`: the zero-inflation steady state is a Calvo equilibrium on every
  probability space (the hypotheses are satisfiable).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6CalvoDerived

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6HouseholdMeasureTVC TidyR6EulerIS TidyR6CalvoReset
open TidyR6CalvoPC TidyR6RotembergPC TidyR6DerivedModel

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, **derived with Calvo price setting
(necessity and sufficiency)**. Let the Calvo parameters be valid with `γ > 0`, the household's
utility be concave, increasing and differentiable with CRRA marginal utility above the floor
(output above it), output gap and inflation bounded by `L` with `δe^{ηL} < 1`, the nominal rate
and the initial log price bounded at every date, reset prices adapted and bounded, the Calvo
index at every date, and the household's feasibility, admissibility, bond holdings,
integrability and transversality conditions. Then the household is optimal and every resetter is
optimal iff (17.15)–(17.17) hold at every date with `u_x = isRem` and `u_π = calvoRem`. -/
theorem eqm_iff_model_calvo {p : CalvoPar} (h : p.Valid) (hγ : 0 < p.γ) {a y : ℝ}
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-p.γ)) {x i π r s b : ℕ → Ω → ℝ} {pm b₀ : Ω → ℝ}
    {L Lr : ℝ} (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1)
    (hx : StronglyAdapted S.𝓕 x) (hi : StronglyAdapted S.𝓕 i) (hπ : StronglyAdapted S.𝓕 π)
    (hr : StronglyAdapted S.𝓕 r) (hib : ∀ t, BddAt S (i t))
    (hpm : StronglyMeasurable[S.𝓕 0] pm) (hpmb : BddAt S pm) (hrb : ∀ s ω, |r s ω| ≤ Lr)
    (hI : Index p π r) (hfl : ∀ t, ∀ᵐ ω ∂S.μ, a ≤ outp p.Ybar x t ω)
    (hfeas : Feasible S y (price pm π) s (bondPrice p.β i) b₀ (outp p.Ybar x) b)
    (hadm : Admissible S p.β u (outp p.Ybar x)) (hb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω)
    (hWb : ∀ n, Integrable (fun ω => u' (outp p.Ybar x n ω) * b n ω / price pm π n ω) S.μ)
    (htvc : Tendsto (fun N => p.β ^ N * ∫ ω, u' (outp p.Ybar x N ω) * b N ω /
      price pm π N ω ∂S.μ) atTop (𝓝 0)) :
    (Optimal S p.β y u (price pm π) s (bondPrice p.β i) b₀ (outp p.Ybar x) b ∧
      ∀ t, ResetOpt S t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t)) ↔
      ModelM S p.γ⁻¹ p.β p.κ (isRem S p.γ i x π) (calvoRem S p x π r) i (realRate S i π)
        x π := by
  have hreg : LogRegular S x i π pm :=
    ⟨hx, hi, hπ, hpm, fun t => ⟨L, Eventually.of_forall fun ω => (hB.2 t ω).1⟩, hib,
      fun t => ⟨L, Eventually.of_forall fun ω => (hB.2 t ω).2⟩, hpmb⟩
  rw [optimal_iff_IS h.2.2.1 hγ h.2.2.2.2.2.2.1 hu hu'c hconc hmono hu' hreg hfl hfeas hadm hb
    hWb htvc, calvo_iff_PC h hB hρ hx hπ hr hrb hI]
  exact ⟨fun hh t => ⟨(hh.1 t).1, (hh.1 t).2, hh.2 t⟩,
    fun hh => ⟨fun t => ⟨(hh t).1, (hh t).2.1⟩, fun t => (hh t).2.2⟩⟩

/-! ### The steady state is a Calvo equilibrium -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: at the zero-inflation steady state the discounted revenue weights
sum to `F̄`. -/
theorem wA_zero {p : CalvoPar} (h : p.Valid) (t : ℕ) (ω : Ω) :
    wA p (fun _ _ => 0) (fun _ _ => 0) t ω = p.Fbar := by
  have e : ∀ k, p.δ ^ k * aW p (fun _ _ => 0) (fun _ _ => 0) t k ω =
      p.Ybar ^ (1 - p.γ) * p.δ ^ k := fun k => by simp [aW, cumπ]; ring
  simp only [wA, e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h.δ_pos.le h.δ_lt, CalvoPar.Fbar, div_eq_mul_inv]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: at the steady state the discounted disutility weights sum to
`K̄`. -/
theorem wB_zero {p : CalvoPar} (h : p.Valid) (t : ℕ) (ω : Ω) :
    wB p (fun _ _ => 0) (fun _ _ => 0) t ω = p.Kbar := by
  have e : ∀ k, p.δ ^ k * bW p (fun _ _ => 0) (fun _ _ => 0) t k ω =
      p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * p.δ ^ k := fun k => by simp [bW, cumπ]; ring
  simp only [wB, e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one h.δ_pos.le h.δ_lt, CalvoPar.Kbar]
  have h1 : (1 : ℝ) + p.ϕ ≠ 0 := by linarith [h.2.2.2.2.2.1]
  have h2 : (1 : ℝ) - p.δ ≠ 0 := by linarith [h.δ_lt]
  field_simp

/-- Cochrane (2023), p. 118: at the steady state `f_t = k_t = 0` and the Calvo disturbance is
zero. -/
theorem calvoRem_zero {p : CalvoPar} (h : p.Valid) (t : ℕ) (ω : Ω) :
    calvoRem S p (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) t ω = 0 := by
  have hF : ∀ s, fc S p (fun _ _ => 0) (fun _ _ => 0) s = fun _ => 0 := fun s => by
    funext ω
    have e : wA (Ω := Ω) p (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) s = fun _ => p.Fbar :=
      funext fun ω => wA_zero h s ω
    simp only [fc, Fc, e, S.E_const, div_self h.Fbar_pos.ne', Real.log_one]
  have hK : ∀ s, kc S p (fun _ _ => 0) (fun _ _ => 0) s = fun _ => 0 := fun s => by
    funext ω
    have e : wB (Ω := Ω) p (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) s = fun _ => p.Kbar :=
      funext fun ω => wB_zero h s ω
    simp only [kc, Kc, e, S.E_const, div_self h.Kbar_pos.ne', Real.log_one]
  have hRI : ∀ s, RI (Ω := Ω) p (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) s = fun _ => 0 :=
      fun s => by
    funext ω; simp [RI]
  simp only [calvoRem, RK, RF, hF, hK, hRI, mul_zero, add_zero, S.E_const, sub_zero, zero_div]

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407: **the zero-inflation steady state is a Calvo
equilibrium** on every probability space: with steady-state output `Ȳ = ssY`, constant positive
government debt held by the household and the concrete CRRA utility `crraU`, the household is
optimal and every resetter optimally resets to the aggregate price. -/
theorem calvo_steady_state {p : CalvoPar} (h : p.Valid) (hγ : 0 < p.γ)
    (hY : p.Ybar = ssY p.ε p.γ p.ϕ) (y Bbar : ℝ) (hBb : 0 < Bbar) :
    Optimal S p.β y (crraU p.γ p.Ybar) (price (fun _ => 0) (fun _ _ => 0))
        (fun _ _ => y - p.Ybar + (1 - p.β) * Bbar) (bondPrice p.β (fun _ _ => 0))
        (fun _ => Bbar) (outp p.Ybar (fun _ _ => 0)) (fun _ _ => Bbar) ∧
      ∀ t, ResetOpt S t p.δ p.ε p.η (aW p (fun _ _ => 0) (fun _ _ => 0) t)
        (bW p (fun _ _ => 0) (fun _ _ => 0) t) (fun _ => 0) := by
  refine ⟨?_, ?_⟩
  · rw [hY]
    exact (steady_state_eqm (φ := 1) h.2.2.1 h.2.2.2.1 hγ h.2.2.2.2.1 h.2.2.2.2.2.1 one_pos y
      Bbar hBb).1
  · have hB : Bounded (Ω := Ω) (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) (0 : ℝ) :=
      ⟨le_rfl, fun _ _ => by simp⟩
    have hρ : p.δ * Real.exp (p.η * 0) < 1 := by simpa using h.δ_lt
    have hI : Index (Ω := Ω) p (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := fun _ _ => by simp
    have := (calvo_iff_PC (S := S) h hB hρ (fun _ => stronglyMeasurable_const)
      (fun _ => stronglyMeasurable_const) (fun _ => stronglyMeasurable_const) (Lr := 0)
      (fun _ _ => by simp) hI).2 fun t => Eventually.of_forall fun ω => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, calvoRem_zero h, S.E_const,
          mul_zero, add_zero]
    exact this

/-! ### Finite event trees -/

namespace Tree

open ExpectationsFiniteTree TreeBridge TidyR6EulerIS.Tree TidyR6CalvoPC.Tree

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, with Calvo price setting, **on a finite event
tree**: under the hypotheses of `eqm_iff_model_calvo` posed on the tree, the household and every
resetter are optimal iff the project's `FullModel.Model` holds in every state, with
`u_x = coreIsRem` and `u_π = calvoRem`. -/
theorem eqm_iff_model_calvo {p : CalvoPar} (h : p.Valid) (hγ : 0 < p.γ) {a y : ℝ}
    {u u' : ℝ → ℝ} (hu : ∀ c, HasDerivAt u (u' c) c) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu' : ∀ c, a ≤ c → u' c = c ^ (-p.γ)) {x i π r s b : ℕ → Ω' → ℝ} {pm b₀ : Ω' → ℝ}
    {L Lr : ℝ} (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1)
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hi : StronglyAdapted (treeSystem T).𝓕 i)
    (hπ : StronglyAdapted (treeSystem T).𝓕 π) (hr : StronglyAdapted (treeSystem T).𝓕 r)
    (hpm : StronglyMeasurable[(treeSystem T).𝓕 0] pm) (hrb : ∀ s ω, |r s ω| ≤ Lr)
    (hI : Index p π r) (hfl : ∀ t ω, a ≤ outp p.Ybar x t ω)
    (hfeas : Feasible (treeSystem T) y (price pm π) s (bondPrice p.β i) b₀ (outp p.Ybar x) b)
    (hadm : Admissible (treeSystem T) p.β u (outp p.Ybar x)) (hb : ∀ t ω, 0 < b (t + 1) ω)
    (htvc : Tendsto (fun N => p.β ^ N * ∫ ω, u' (outp p.Ybar x N ω) * b N ω /
      price pm π N ω ∂(treeSystem T).μ) atTop (𝓝 0)) :
    (Optimal (treeSystem T) p.β y u (price pm π) s (bondPrice p.β i) b₀ (outp p.Ybar x) b ∧
      ∀ t, ResetOpt (treeSystem T) t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t)) ↔
      FullModel.Model T.toExpectationSystem p.γ⁻¹ p.β p.κ
        (coreIsRem T.toExpectationSystem p.γ i x π) (calvoRem (treeSystem T) p x π r) i
        (coreRealRate T.toExpectationSystem i π) x π := by
  rw [TidyR6CalvoDerived.eqm_iff_model_calvo h hγ hu hu'c hconc hmono hu' hB hρ hx hi hπ hr
    (fun _ => Link.bddAt_tree T _) hpm (Link.bddAt_tree T _) hrb hI
    (fun t => Eventually.of_forall (hfl t)) hfeas hadm (fun t => Eventually.of_forall (hb t))
    (fun _ => Integrable.of_finite) htvc]
  have h1 := ISM_iff_IS T p.γ i x π
  have h2 := PCM_iff_PC_gen T p.β p.κ (calvoRem (treeSystem T) p x π r) x π
  constructor
  · intro hh
    exact ⟨h1.1 fun t => (hh t).1, fisher_coreRealRate _ i π, h2.1 fun t => (hh t).2.2⟩
  · intro hh t
    exact ⟨h1.2 hh.1 t, fisherM_realRate _ i π t, h2.2 hh.2.2 t⟩

end Tree

end Cochrane.KeynesianStickyPrices.TidyR6CalvoDerived
