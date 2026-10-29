/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR6bRuleSystemMeasure
import OptimalPolicyRules.TidyR5aLambdaILimitMeasure

/-!
# The limit `λᵢ → 0` on a probability space: existence of the equilibria

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, pp. 584 and 591: equilibria under the
optimal rule (3.7) of the basic model, and the Chapter 7 optimal paths (the criterion (2.5)), on
every filtered probability space with Mathlib's conditional expectation.

`TidyR5aLambdaILimitMeasure.paths_convergeM` proves that the paths under (3.7) converge a.s. to the
(2.5) paths as `λᵢ → 0`, taking the existence of both as hypotheses. This module proves both
existences, so the convergence theorem holds with no existence hypothesis
(`paths_convergeM_exists`):

* `rule_eqm_existsM`: for every admissible calibration, every essentially bounded adapted
  disturbance `(rⁿ, u)` and every history `x_{−1}, i_{−1}, i_{−2}`, an essentially bounded adapted
  equilibrium of (2.1), (3.1) and (3.7) exists (`TidyR5aLambdaILimitMeasure.RuleEqmM`). It is the
  `γ = 0` rule system of p. 593 (`TidyR6bRuleSystemMeasure.existsM_zero`) on the filtration
  delayed by two dates (`unshift2`), with the history placed at dates 0 and 1; at `γ = 0` the rule
  (3.16) is (3.7).
* `rule_eqm_uniqueM`: it is unique a.s. (`TidyR5aLambdaXZeroMeasure.rule_system_uniqueM` on the
  delayed filtration).
* `crit25_existsM`: an essentially bounded adapted solution of (2.1) and (2.5) exists:
  `x_t = μ₁x_{t−1} + z_t` with `z_t = βμ₁E_t z_{t+1} − (μ₁/φ)u_t` (the forward solution
  `ExpectationsMeasure.MeasExpectationSystem.forwardSol`), `φ = λₓ/κ`, `μ₁` the stable root of
  `βμ² − (1 + β + κ/φ)μ + 1` (`QuadraticRoots.lam1`), and `π_t = −φ(x_t − x_{t−1})`.
* `crit25_uniqueM`: it is unique a.s.
* `paths_convergeM_exists`: the equilibria exist for every `λᵢ = l_n > 0`, the (2.5) solution
  exists, and the paths converge a.s., uniformly in the date.
-/

namespace Woodford.OptimalPolicyRules.TidyR6bLambdaILimitExists

open MeasureTheory Filter Topology
open ExpectationsMeasure
open IRuleBasic (Calib lag rho1 rho2 phiPi phiX)
open TidyR5aLambdaXZeroMeasure (BndM AdaptedM RuleSolM HistoryM integrable_of_sm)
open TidyR5aLambdaILimitMeasure (ASb ISb RuleM RuleEqmM Crit25M i0M)
open InflationInertiaRules (ALi qtil)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The filtration delayed by two dates -/

/-- Woodford (2003), §3.1 and p. 593 (tool): the filtration delayed by two dates,
`𝓕'_k = 𝓕_{k−2}` (so the date-`t` information of §3.1 is the date-`t + 2` information of the rule
system of p. 593). -/
def unshift2 (S : MeasExpectationSystem Ω) : MeasExpectationSystem Ω where
  P := S.P
  𝓕 := ⟨fun s => S.𝓕 (s - 2), fun _ _ h => S.𝓕.mono (by omega), fun _ => S.𝓕.le _⟩

/-- Woodford (2003), p. 593 (tool): `E'_{t+2} = E_t` for the delayed filtration. -/
theorem unshift2_E (S : MeasExpectationSystem Ω) (t : ℕ) (x : Ω → ℝ) :
    (unshift2 S).E (t + 2) x = S.E t x := rfl

/-! ### Equilibria under the rule (3.7) -/

/-- **Woodford (2003), Proposition 8.5, p. 584 (existence), on every filtered probability space.**
For every admissible calibration, every essentially bounded adapted disturbance `(rⁿ, u)` and
every history `x_{−1}, i_{−1}, i_{−2}`, there is an essentially bounded adapted equilibrium of
(2.1), (3.1) and the optimal rule (3.7), with Mathlib's conditional expectation. -/
theorem rule_eqm_existsM (c : Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω)
    {rn u : ℕ → Ω → ℝ} (hra : AdaptedM S rn) (hrb : BndM S rn) (hua : AdaptedM S u)
    (hub : BndM S u) (xm1 im1 im2 : ℝ) :
    ∃ π x i : ℕ → Ω → ℝ, RuleEqmM S c rn u xm1 im1 im2 π x i ∧
      (AdaptedM S π ∧ AdaptedM S x ∧ AdaptedM S i) ∧ (BndM S π ∧ BndM S x ∧ BndM S i) := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hκ : c.κ ≠ 0 := hc.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  set S' := unshift2 S with hS'
  obtain ⟨Cu, hCu⟩ := hub
  obtain ⟨Cr, hCr⟩ := hrb
  have hh : HistoryM S' (fun _ => 0) (fun _ => xm1) (fun _ => im1) (fun _ => im2) :=
    ⟨stronglyMeasurable_const, stronglyMeasurable_const, stronglyMeasurable_const,
      stronglyMeasurable_const, |xm1| + |im1| + |im2|, Eventually.of_forall fun _ => by
        refine ⟨by simp only [abs_zero]; positivity, ?_, ?_, ?_⟩ <;>
        linarith [abs_nonneg xm1, abs_nonneg im1, abs_nonneg im2]⟩
  obtain ⟨π', x', i', h⟩ := TidyR6bRuleSystemMeasure.existsM_zero c hc S'
    (u := fun k => u (k - 2)) (rn := fun k => rn (k - 2)) (fun k => hua (k - 2))
    ⟨Cu, fun k => hCu (k - 2)⟩ (fun k => hra (k - 2)) ⟨Cr, fun k => hCr (k - 2)⟩ hh
  obtain ⟨hπa, hxa, hia, ⟨Cπ, hCπ⟩, ⟨Cx, hCx⟩, ⟨Ci, hCi⟩, hAS, hIS, hEu, h1, h2, h3, h4⟩ := h
  have hii : ∀ k, Integrable (i' k) S.μ := fun k =>
    integrable_of_sm S' (hia k) (hCi k)
  -- the lags
  have hl1 : ∀ t ω, lag im1 (fun t => i' (t + 2)) t ω = i' (t + 1) ω := by
    intro t ω
    cases t with
    | zero => simp only [lag, zero_add, h3]
    | succ s => rfl
  have hl2 : ∀ t ω, lag im2 (lag im1 (fun t => i' (t + 2))) t ω = i' t ω := by
    intro t ω
    rcases t with _ | _ | s
    · simp only [lag, h4]
    · simp only [lag, h3]
    · rfl
  have hlx : ∀ t ω, lag xm1 (fun t => x' (t + 2)) t ω = x' (t + 1) ω := by
    intro t ω
    cases t with
    | zero => simp only [lag, zero_add, h2]
    | succ s => rfl
  refine ⟨fun t => π' (t + 2), fun t => x' (t + 2), fun t => i' (t + 2), fun t => ⟨?_, ?_, ?_⟩,
    ⟨fun t => hπa (t + 2), fun t => hxa (t + 2), fun t => hia (t + 2)⟩,
    ⟨⟨Cπ, fun t => hCπ (t + 2)⟩, ⟨Cx, fun t => hCx (t + 2)⟩, ⟨Ci, fun t => hCi (t + 2)⟩⟩⟩
  · -- (2.1)
    filter_upwards [hAS (t + 2) (by omega)] with ω e
    have hf : (fun ω' => π' (t + 2 + 1) ω' - 0 * π' (t + 2) ω') = π' (t + 2 + 1) :=
      funext fun ω' => by ring
    rw [hf] at e
    change π' (t + 2) ω - 0 * π' (t + 1) ω =
      c.κ * x' (t + 2) ω + c.β * S.E t (π' (t + 3)) ω + u t ω at e
    change π' (t + 2) ω = c.κ * x' (t + 2) ω + c.β * S.E t (π' (t + 3)) ω + u t ω
    linarith
  · -- (3.1)
    filter_upwards [hIS (t + 2) (by omega)] with ω e
    exact e
  · -- the rule (3.7) is (3.16) at `γ = 0`
    have hA : ALi c.β 0 c.κ c.σ (fun k ω => i' k ω - c.istar) t = fun ω =>
        -(i' (t + 2) ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ * (i' (t + 1) ω - c.istar) -
          c.β⁻¹ * (i' t ω - c.istar) := by
      funext ω
      simp only [ALi]
      ring
    have hAk : StronglyMeasurable[S'.𝓕 (t + 2)] (fun ω =>
        -(i' (t + 2) ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ * (i' (t + 1) ω - c.istar) -
          c.β⁻¹ * (i' t ω - c.istar)) :=
      (((hia (t + 2)).sub stronglyMeasurable_const).neg.add
        ((((hia (t + 1)).mono (S'.𝓕.mono (by omega))).sub stronglyMeasurable_const).const_mul
          _)).sub
        ((((hia t).mono (S'.𝓕.mono (by omega))).sub stronglyMeasurable_const).const_mul _)
    have hAi : Integrable (fun ω =>
        -(i' (t + 2) ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ * (i' (t + 1) ω - c.istar) -
          c.β⁻¹ * (i' t ω - c.istar)) S.μ :=
      (((hii (t + 2)).sub (integrable_const _)).neg.add
        (((hii (t + 1)).sub (integrable_const _)).const_mul _)).sub
        (((hii t).sub (integrable_const _)).const_mul _)
    filter_upwards [hEu t] with ω e
    rw [hA, S'.E_of_stronglyMeasurable hAk hAi] at e
    simp only [TidyR5aLambdaXZeroMeasure.fbigM, qtil] at e
    rw [show t + 2 - 1 = t + 1 by omega] at e
    have e' : -(i' (t + 2) ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ *
        (i' (t + 1) ω - c.istar) - c.β⁻¹ * (i' t ω - c.istar) =
        -(c.κ * c.σ / c.li * ((π' (t + 2) ω - 0 * π' (t + 1) ω) +
          c.lx / c.κ * (x' (t + 2) ω - x' (t + 1) ω))) := by
      rw [e]
      ring
    change i' (t + 2) ω = (1 - rho1 c.β c.σ c.κ) * c.istar +
      rho1 c.β c.σ c.κ * lag im1 (fun t => i' (t + 2)) t ω +
      rho2 c.β * (lag im1 (fun t => i' (t + 2)) t ω -
        lag im2 (lag im1 (fun t => i' (t + 2))) t ω) +
      phiPi c.σ c.κ c.li * π' (t + 2) ω +
      phiX c.σ c.lx c.li / 4 * (x' (t + 2) ω - lag xm1 (fun t => x' (t + 2)) t ω)
    rw [hl1, hl2, hlx]
    unfold CubicRoots.coefA2 at e'
    unfold rho1 rho2 phiPi phiX
    field_simp at e' ⊢
    linear_combination -e'

/-- Woodford (2003), §3.1 and p. 593 (tool): a process of §3.1 placed at dates `≥ 2` of the rule
system, with the values `v₀, v₁` at dates 0 and 1. -/
def place (v0 v1 : ℝ) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => v0
  | 1 => fun _ => v1
  | k + 2 => f k

/-- **Woodford (2003), p. 584 and p. 593: an equilibrium under the rule (3.7) is a solution of the
rule system at `γ = 0` on the delayed filtration** (with the history at dates 0 and 1): at `γ = 0`
(3.7) is (3.16). -/
theorem ruleSolM_of_eqm (c : Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω)
    {rn u : ℕ → Ω → ℝ} (xm1 im1 im2 : ℝ) {π x i : ℕ → Ω → ℝ}
    (he : RuleEqmM S c rn u xm1 im1 im2 π x i) (hπa : AdaptedM S π) (hxa : AdaptedM S x)
    (hia : AdaptedM S i) (hπb : BndM S π) (hxb : BndM S x) (hib : BndM S i) :
    RuleSolM (unshift2 S) c 0 (fun k => u (k - 2)) (fun k => rn (k - 2)) (fun _ => 0)
      (fun _ => xm1) (fun _ => im1) (fun _ => im2) (place 0 0 π) (place 0 xm1 x)
      (place im2 im1 i) := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hκ : c.κ ≠ 0 := hc.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  set S' := unshift2 S with hS'
  obtain ⟨Cπ, hCπ⟩ := hπb
  obtain ⟨Cx, hCx⟩ := hxb
  obtain ⟨Ci, hCi⟩ := hib
  have hplA : ∀ (v0 v1 : ℝ) (f : ℕ → Ω → ℝ), AdaptedM S f → AdaptedM S' (place v0 v1 f) := by
    intro v0 v1 f hf k
    rcases k with _ | _ | k
    · exact stronglyMeasurable_const
    · exact stronglyMeasurable_const
    · exact hf k
  have hplB : ∀ (v0 v1 : ℝ) (f : ℕ → Ω → ℝ) (C : ℝ), (∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ C) →
      BndM S' (place v0 v1 f) := by
    intro v0 v1 f C hf
    refine ⟨max C (|v0| + |v1|), fun k => ?_⟩
    rcases k with _ | _ | k
    · exact Eventually.of_forall fun ω => le_max_of_le_right (by
        simp only [place]; linarith [abs_nonneg v1])
    · exact Eventually.of_forall fun ω => le_max_of_le_right (by
        simp only [place]; linarith [abs_nonneg v0])
    · exact (hf k).mono fun ω h => h.trans (le_max_left _ _)
  have hia' := hplA im2 im1 i hia
  have hii : ∀ k, Integrable (place im2 im1 i k) S.μ := fun k =>
    integrable_of_sm S' (hia' k) ((hplB im2 im1 i Ci hCi).choose_spec k)
  refine ⟨hplA 0 0 π hπa, hplA 0 xm1 x hxa, hia', hplB 0 0 π Cπ hCπ, hplB 0 xm1 x Cx hCx,
    hplB im2 im1 i Ci hCi, fun k hk => ?_, fun k hk => ?_, fun t => ?_, rfl, rfl, rfl, rfl⟩
  · obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
    filter_upwards [(he t).1] with ω e
    have hf : (fun ω' => place 0 0 π (t + 2 + 1) ω' - 0 * place 0 0 π (t + 2) ω') =
        π (t + 1) := funext fun ω' => by
      change π (t + 1) ω' - 0 * π t ω' = π (t + 1) ω'
      ring
    rw [hf]
    change π t ω - 0 * place 0 0 π (t + 1) ω =
      c.κ * x t ω + c.β * S.E t (π (t + 1)) ω + u t ω
    rw [e]
    ring
  · obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
    filter_upwards [(he t).2.1] with ω e
    exact e
  · have hA : ALi c.β 0 c.κ c.σ (fun k ω => place im2 im1 i k ω - c.istar) t = fun ω =>
        -(place im2 im1 i (t + 2) ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ *
          (place im2 im1 i (t + 1) ω - c.istar) - c.β⁻¹ * (place im2 im1 i t ω - c.istar) := by
      funext ω
      simp only [ALi]
      ring
    have hAk : StronglyMeasurable[S'.𝓕 (t + 2)] (fun ω =>
        -(place im2 im1 i (t + 2) ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ *
          (place im2 im1 i (t + 1) ω - c.istar) - c.β⁻¹ * (place im2 im1 i t ω - c.istar)) :=
      (((hia' (t + 2)).sub stronglyMeasurable_const).neg.add
        ((((hia' (t + 1)).mono (S'.𝓕.mono (by omega))).sub stronglyMeasurable_const).const_mul
          _)).sub
        ((((hia' t).mono (S'.𝓕.mono (by omega))).sub stronglyMeasurable_const).const_mul _)
    have hAi : Integrable (fun ω =>
        -(place im2 im1 i (t + 2) ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ *
          (place im2 im1 i (t + 1) ω - c.istar) - c.β⁻¹ * (place im2 im1 i t ω - c.istar)) S.μ :=
      (((hii (t + 2)).sub (integrable_const _)).neg.add
        (((hii (t + 1)).sub (integrable_const _)).const_mul _)).sub
        (((hii t).sub (integrable_const _)).const_mul _)
    have hl1 : ∀ ω, lag im1 i t ω = place im2 im1 i (t + 1) ω := by
      intro ω
      cases t <;> rfl
    have hl2 : ∀ ω, lag im2 (lag im1 i) t ω = place im2 im1 i t ω := by
      intro ω
      rcases t with _ | _ | s <;> rfl
    have hlx : ∀ ω, lag xm1 x t ω = place 0 xm1 x (t + 1) ω := by
      intro ω
      cases t <;> rfl
    filter_upwards [(he t).2.2] with ω e
    rw [hA, S'.E_of_stronglyMeasurable hAk hAi]
    simp only [TidyR5aLambdaXZeroMeasure.fbigM, qtil]
    rw [show t + 2 - 1 = t + 1 by omega]
    rw [hl1, hl2, hlx] at e
    change i t ω = _ at e
    change -(i t ω - c.istar) + CubicRoots.coefA2 c.β 0 c.κ c.σ *
        (place im2 im1 i (t + 1) ω - c.istar) - c.β⁻¹ * (place im2 im1 i t ω - c.istar) =
      -(c.κ * c.σ / c.li * ((π t ω - 0 * place 0 0 π (t + 1) ω) +
        c.lx / c.κ * (x t ω - place 0 xm1 x (t + 1) ω)) -
        c.β * 0 * S'.E (t + 2) (qtil 0 c.κ c.σ c.lx c.li (place 0 0 π) (place 0 xm1 x)
          (t + 2 + 1)) ω)
    unfold CubicRoots.coefA2
    unfold rho1 rho2 phiPi phiX at e
    field_simp at e ⊢
    linear_combination -e

/-- **Woodford (2003), Proposition 8.5, p. 584 (uniqueness), on every filtered probability
space**: two essentially bounded adapted equilibria under the optimal rule (3.7) with the same
disturbances and history agree a.s. at every date (`TidyR5aLambdaXZeroMeasure.rule_system_uniqueM`
on the delayed filtration, through `ruleSolM_of_eqm`). -/
theorem rule_eqm_uniqueM (c : Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω)
    {rn u : ℕ → Ω → ℝ} (xm1 im1 im2 : ℝ) {π x i π' x' i' : ℕ → Ω → ℝ}
    (he : RuleEqmM S c rn u xm1 im1 im2 π x i) (hπa : AdaptedM S π) (hxa : AdaptedM S x)
    (hia : AdaptedM S i) (hπb : BndM S π) (hxb : BndM S x) (hib : BndM S i)
    (he' : RuleEqmM S c rn u xm1 im1 im2 π' x' i') (hπa' : AdaptedM S π') (hxa' : AdaptedM S x')
    (hia' : AdaptedM S i') (hπb' : BndM S π') (hxb' : BndM S x') (hib' : BndM S i') :
    ∀ t, π' t =ᵐ[S.μ] π t ∧ x' t =ᵐ[S.μ] x t ∧ i' t =ᵐ[S.μ] i t := by
  intro t
  have h := TidyR5aLambdaXZeroMeasure.rule_system_uniqueM (unshift2 S) c hc.1 hc.2.1
    hc.2.2.2.1.ne' hc.2.2.1.ne' hc.2.2.2.2.2 hc.2.2.2.2.1.le
    (ruleSolM_of_eqm c hc S xm1 im1 im2 he' hπa' hxa' hia' hπb' hxb' hib')
    (ruleSolM_of_eqm c hc S xm1 im1 im2 he hπa hxa hia hπb hxb hib) (t + 2) (by omega)
  exact h

/-! ### The solution of (2.1) and (2.5) -/

/-- Woodford (2003), p. 540 (tool): `E_t(af + bg) = aE_tf + bg` a.s. for integrable `f` and
integrable `g` known at `t`, written in the form of `TidyR6bRuleSystemMeasure.E_aff22`. -/
theorem E_aff22' (S : MeasExpectationSystem Ω) (t : ℕ) {f g : Ω → ℝ} (hf : Integrable f S.μ)
    (hg : StronglyMeasurable[S.𝓕 t] g) (hgi : Integrable g S.μ) (a b : ℝ) :
    ∀ᵐ ω ∂S.μ, S.E t (fun ω => a * f ω + 0 * f ω + b * g ω + 0 * g ω + 0 * g ω + 0) ω =
      a * S.E t f ω + 0 * S.E t f ω + b * g ω + 0 * g ω + 0 * g ω + 0 :=
  TidyR6bRuleSystemMeasure.E_aff22 S t a 0 b 0 0 0 hf hf hg hg hg hgi hgi hgi

/-- Woodford (2003), (2.5)–(2.8), p. 561, survey §4.3: the stable root `μ₁` of
`βμ² − (1 + β + κ/φ)μ + 1`, `φ = λₓ/κ`. -/
noncomputable def mu25 (c : Calib) : ℝ := QuadraticRoots.lam1 c.β (c.κ / (c.lx / c.κ))

/-- Woodford (2003), (2.5)–(2.8), p. 561, with conditional expectations: the forward solution
`z_t = E_t ∑_k (βμ₁)ᵏ (−(μ₁/φ)u_{t+k})` of `z_t = βμ₁E_tz_{t+1} − (μ₁/φ)u_t`. -/
noncomputable def z25 (S : MeasExpectationSystem Ω) (c : Calib) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  S.forwardSol (c.β * mu25 c) (fun t ω => -(mu25 c / (c.lx / c.κ)) * u t ω)

/-- Woodford (2003), (2.5)–(2.8), p. 561, with conditional expectations: the output gap
`x_t = μ₁x_{t−1} + z_t`, `x_{−1}` given. -/
noncomputable def x25 (S : MeasExpectationSystem Ω) (c : Calib) (xm1 : ℝ) (u : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun ω => mu25 c * xm1 + z25 S c u 0 ω
  | t + 1 => fun ω => mu25 c * x25 S c xm1 u t ω + z25 S c u (t + 1) ω

/-- Woodford (2003), (2.5), p. 561: inflation from the criterion, `π_t = −φ(x_t − x_{t−1})`. -/
noncomputable def pi25 (S : MeasExpectationSystem Ω) (c : Calib) (xm1 : ℝ) (u : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => -(c.lx / c.κ) * (x25 S c xm1 u t ω - lag xm1 (x25 S c xm1 u) t ω)

/-- Woodford (2003), (2.5)–(2.8) (tool): `x_t = μ₁x_{t−1} + z_t` at every date. -/
theorem x25_eq (S : MeasExpectationSystem Ω) (c : Calib) (xm1 : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : x25 S c xm1 u t ω = mu25 c * lag xm1 (x25 S c xm1 u) t ω + z25 S c u t ω := by
  cases t <;> rfl

/-- Woodford (2003), survey §4.3 (tool): `0 < μ₁ < 1` and `|βμ₁| < 1` for an admissible
calibration. -/
theorem mu25_facts (c : Calib) (hc : c.Adm) :
    0 < mu25 c ∧ mu25 c < 1 ∧ |c.β * mu25 c| < 1 ∧
      c.β * mu25 c ^ 2 - (1 + c.β + c.κ / (c.lx / c.κ)) * mu25 c + 1 = 0 := by
  have hc' : 0 < c.κ / (c.lx / c.κ) := div_pos hc.2.2.2.1 (div_pos hc.2.2.2.2.1 hc.2.2.2.1)
  obtain ⟨h0, h1⟩ := QuadraticRoots.beta_lam1_mem hc.1 hc.2.1 hc'
  exact ⟨QuadraticRoots.lam1_pos hc.1 hc', QuadraticRoots.lam1_lt_one hc.1 hc',
    by unfold mu25; rw [abs_of_nonneg h0]; exact h1, QuadraticRoots.lam1_root hc.1 hc'⟩

/-- **Woodford (2003), (2.1) and (2.5), p. 561, on every filtered probability space: a solution
exists.** For an admissible calibration, every essentially bounded adapted cost-push disturbance
and every `x_{−1}`, `(pi25, x25)` is an essentially bounded adapted solution of (2.1) and the
criterion (2.5), with Mathlib's conditional expectation. -/
theorem crit25_existsM (c : Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω) {u : ℕ → Ω → ℝ}
    (hua : AdaptedM S u) (hub : BndM S u) (xm1 : ℝ) :
    AdaptedM S (pi25 S c xm1 u) ∧ AdaptedM S (x25 S c xm1 u) ∧ BndM S (pi25 S c xm1 u) ∧
      BndM S (x25 S c xm1 u) ∧ (∀ t, ASb S c u (pi25 S c xm1 u) (x25 S c xm1 u) t) ∧
      Crit25M S c xm1 (pi25 S c xm1 u) (x25 S c xm1 u) := by
  obtain ⟨hμ0, hμ1, ha, hr⟩ := mu25_facts c hc
  set μ := mu25 c with hμ
  set φ := c.lx / c.κ with hφ
  have hφ0 : φ ≠ 0 := (div_pos hc.2.2.2.2.1 hc.2.2.2.1).ne'
  obtain ⟨Cu, hCu⟩ := hub
  set g : ℕ → Ω → ℝ := fun t ω => -(μ / φ) * u t ω with hg
  have hga : StronglyAdapted S.𝓕 g := fun t => (hua t).const_mul _
  have hgb : ∀ t, ∀ᵐ ω ∂S.μ, |g t ω| ≤ |μ / φ| * Cu := fun t =>
    (hCu t).mono fun ω h => by
      simp only [hg, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hza : StronglyAdapted S.𝓕 (z25 S c u) := S.forwardSol_adapted _ _
  obtain ⟨Kz, hKz⟩ : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |z25 S c u t ω| ≤ K := S.forwardSol_bdd ha hgb
  have hzs : S.Solves (c.β * μ) g (z25 S c u) := S.forwardSol_solves ha hga hgb
  have hzi : ∀ t, Integrable (z25 S c u t) S.μ := fun t => integrable_of_sm S (hza t) (hKz t)
  -- adaptedness and bounds of `x`
  have hxa : AdaptedM S (x25 S c xm1 u) := by
    intro t
    induction t with
    | zero => exact stronglyMeasurable_const.add (hza 0)
    | succ s ih => exact (((ih.mono (S.𝓕.mono (Nat.le_succ s))).const_mul μ)).add (hza (s + 1))
  set B := max |xm1| (Kz / (1 - μ)) with hB
  have hKB : Kz ≤ (1 - μ) * B := by
    have h1 : Kz / (1 - μ) ≤ B := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at h1
    linarith
  have hB0 : 0 ≤ B := (abs_nonneg xm1).trans (le_max_left _ _)
  have hxb' : ∀ t, ∀ᵐ ω ∂S.μ, |x25 S c xm1 u t ω| ≤ B := by
    intro t
    induction t with
    | zero =>
      filter_upwards [hKz 0] with ω h
      change |μ * xm1 + z25 S c u 0 ω| ≤ B
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hμ0]
      have := mul_le_mul_of_nonneg_left (le_max_left |xm1| (Kz / (1 - μ))) hμ0.le
      linarith
    | succ s ih =>
      filter_upwards [ih, hKz (s + 1)] with ω h1 h2
      change |μ * x25 S c xm1 u s ω + z25 S c u (s + 1) ω| ≤ B
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hμ0]
      have := mul_le_mul_of_nonneg_left h1 hμ0.le
      linarith
  have hxb : BndM S (x25 S c xm1 u) := ⟨B, hxb'⟩
  have hxi : ∀ t, Integrable (x25 S c xm1 u t) S.μ := fun t => integrable_of_sm S (hxa t) (hxb' t)
  have hlag : ∀ t, StronglyMeasurable[S.𝓕 t] (lag xm1 (x25 S c xm1 u) t) := by
    intro t
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ s => exact (hxa s).mono (S.𝓕.mono (Nat.le_succ s))
  have hlagb : ∀ t, ∀ᵐ ω ∂S.μ, |lag xm1 (x25 S c xm1 u) t ω| ≤ B := by
    intro t
    cases t with
    | zero => exact Eventually.of_forall fun ω => le_max_left _ _
    | succ s => exact hxb' s
  refine ⟨fun t => ((hxa t).sub (hlag t)).const_mul _, hxa, ⟨|φ| * (B + B), fun t => ?_⟩, hxb,
    fun t => ?_, fun t => Eventually.of_forall fun ω => ?_⟩
  · filter_upwards [hxb' t, hlagb t] with ω h1 h2
    simp only [pi25]
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
  · -- (2.1)
    have eπ : pi25 S c xm1 u (t + 1) = fun ω => (-φ) * z25 S c u (t + 1) ω +
        0 * z25 S c u (t + 1) ω + (φ - φ * μ) * x25 S c xm1 u t ω + 0 * x25 S c xm1 u t ω +
        0 * x25 S c xm1 u t ω + 0 := by
      funext ω
      simp only [pi25, lag]
      rw [x25_eq S c xm1 u (t + 1) ω]
      simp only [lag]
      ring
    filter_upwards [E_aff22' S t (hzi (t + 1)) (hxa t) (hxi t) (-φ) (φ - φ * μ), hzs t]
      with ω eE ez
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ez
    rw [eπ, eE]
    simp only [pi25]
    have hx := x25_eq S c xm1 u t ω
    have key : μ * (-φ * (x25 S c xm1 u t ω - lag xm1 (x25 S c xm1 u) t ω) -
        (c.κ * x25 S c xm1 u t ω + c.β * (-φ * S.E t (z25 S c u (t + 1)) ω +
          (φ - φ * μ) * x25 S c xm1 u t ω) + u t ω)) = 0 := by
      have hφ' : φ * φ⁻¹ = 1 := mul_inv_cancel₀ hφ0
      have hκφ : c.κ / φ = c.κ * φ⁻¹ := div_eq_mul_inv _ _
      rw [hκφ] at hr
      linear_combination (φ * x25 S c xm1 u t ω) * hr - φ * ez - φ * hx +
        (c.κ * μ * x25 S c xm1 u t ω + μ * u t ω) * hφ'
    have := (mul_eq_zero.mp key).resolve_left hμ0.ne'
    linear_combination this
  · simp only [pi25]
    ring

/-- **Woodford (2003), (2.1) and (2.5), p. 561, on every filtered probability space: the solution
is unique a.s.** Two essentially bounded adapted solutions of (2.1) and (2.5) with the same
disturbance and the same `x_{−1}` agree a.s. at every date: `w_t = d_t − μ₁d_{t−1}` (`d` the
difference of the output gaps) solves `w_t = βμ₁E_tw_{t+1}`, so it vanishes
(`ExpectationsMeasure.MeasExpectationSystem.forward_unique`). -/
theorem crit25_uniqueM (c : Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω) {u : ℕ → Ω → ℝ}
    (xm1 : ℝ) {π1 x1 π2 x2 : ℕ → Ω → ℝ} (hπ1a : AdaptedM S π1) (hx1a : AdaptedM S x1)
    (hπ1b : BndM S π1) (hx1b : BndM S x1) (hAS1 : ∀ t, ASb S c u π1 x1 t)
    (hc1 : Crit25M S c xm1 π1 x1) (hπ2a : AdaptedM S π2) (hx2a : AdaptedM S x2)
    (hπ2b : BndM S π2) (hx2b : BndM S x2) (hAS2 : ∀ t, ASb S c u π2 x2 t)
    (hc2 : Crit25M S c xm1 π2 x2) :
    ∀ t, π1 t =ᵐ[S.μ] π2 t ∧ x1 t =ᵐ[S.μ] x2 t := by
  obtain ⟨hμ0, -, ha, hr⟩ := mu25_facts c hc
  set μ := mu25 c with hμ
  set φ := c.lx / c.κ with hφ
  have hφ0 : φ ≠ 0 := (div_pos hc.2.2.2.2.1 hc.2.2.2.1).ne'
  have hφ' : φ * φ⁻¹ = 1 := mul_inv_cancel₀ hφ0
  have hκφ : c.κ / φ = c.κ * φ⁻¹ := div_eq_mul_inv _ _
  rw [hκφ] at hr
  obtain ⟨Cπ1, hCπ1⟩ := hπ1b
  obtain ⟨Cπ2, hCπ2⟩ := hπ2b
  obtain ⟨Cx1, hCx1⟩ := hx1b
  obtain ⟨Cx2, hCx2⟩ := hx2b
  have iπ1 : ∀ k, Integrable (π1 k) S.μ := fun k => integrable_of_sm S (hπ1a k) (hCπ1 k)
  have iπ2 : ∀ k, Integrable (π2 k) S.μ := fun k => integrable_of_sm S (hπ2a k) (hCπ2 k)
  set d : ℕ → Ω → ℝ := fun t ω => x1 t ω - x2 t ω with hd
  set p : ℕ → Ω → ℝ := fun t ω => π1 t ω - π2 t ω with hp
  have hda : AdaptedM S d := fun t => (hx1a t).sub (hx2a t)
  have hdb : ∀ t, ∀ᵐ ω ∂S.μ, |d t ω| ≤ Cx1 + Cx2 := fun t => by
    filter_upwards [hCx1 t, hCx2 t] with ω h1 h2
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => integrable_of_sm S (hda t) (hdb t)
  have hL : ∀ t ω, lag xm1 x1 t ω - lag xm1 x2 t ω = lag 0 d t ω := by
    intro t ω
    cases t with
    | zero => simp [lag]
    | succ s => rfl
  have hcrit : ∀ t, ∀ᵐ ω ∂S.μ, p t ω = -φ * (d t ω - lag 0 d t ω) := fun t => by
    filter_upwards [hc1 t, hc2 t] with ω e1 e2
    rw [← hL]
    simp only [hp, hd]
    linear_combination e1 - e2
  have hASd : ∀ t, ∀ᵐ ω ∂S.μ, p t ω = c.κ * d t ω + c.β * S.E t (p (t + 1)) ω := fun t => by
    filter_upwards [hAS1 t, hAS2 t, S.E_sub (iπ1 (t + 1)) (iπ2 (t + 1)) t] with ω e1 e2 e3
    have e3' : S.E t (p (t + 1)) ω = S.E t (π1 (t + 1)) ω - S.E t (π2 (t + 1)) ω := e3
    rw [e3']
    simp only [hp, hd]
    linear_combination e1 - e2
  have hEp : ∀ t, S.E t (p (t + 1)) =ᵐ[S.μ] fun ω => -φ * S.E t (d (t + 1)) ω + 0 *
      S.E t (d (t + 1)) ω + φ * d t ω + 0 * d t ω + 0 * d t ω + 0 := by
    intro t
    have h1 : p (t + 1) =ᵐ[S.μ] fun ω => -φ * d (t + 1) ω + 0 * d (t + 1) ω + φ * d t ω +
        0 * d t ω + 0 * d t ω + 0 := by
      filter_upwards [hcrit (t + 1)] with ω e
      rw [e]
      simp only [lag]
      ring
    exact (S.E_congr h1 t).trans (TidyR6bRuleSystemMeasure.E_aff22 S t (-φ) 0 φ 0 0 0
      (hdi (t + 1)) (hdi (t + 1)) (hda t) (hda t) (hda t) (hdi t) (hdi t) (hdi t))
  set w : ℕ → Ω → ℝ := fun t ω => d t ω - μ * lag 0 d t ω with hw
  have hEw : ∀ t, S.E t (w (t + 1)) =ᵐ[S.μ] fun ω => 1 * S.E t (d (t + 1)) ω + 0 *
      S.E t (d (t + 1)) ω + (-μ) * d t ω + 0 * d t ω + 0 * d t ω + 0 := by
    intro t
    have h1 : w (t + 1) = fun ω => 1 * d (t + 1) ω + 0 * d (t + 1) ω + (-μ) * d t ω +
        0 * d t ω + 0 * d t ω + 0 := by
      funext ω
      simp only [hw, lag]
      ring
    rw [h1]
    exact TidyR6bRuleSystemMeasure.E_aff22 S t 1 0 (-μ) 0 0 0 (hdi (t + 1)) (hdi (t + 1)) (hda t)
      (hda t) (hda t) (hdi t) (hdi t) (hdi t)
  have hws : S.Solves (c.β * μ) 0 w := by
    intro t
    filter_upwards [hcrit t, hASd t, hEp t, hEw t] with ω e1 e2 e3 e4
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    rw [e4]
    rw [e3, e1] at e2
    have key : φ * (w t ω - c.β * μ * (1 * S.E t (d (t + 1)) ω + 0 * S.E t (d (t + 1)) ω +
        (-μ) * d t ω + 0 * d t ω + 0 * d t ω + 0)) = 0 := by
      simp only [hw]
      linear_combination (-μ) * e2 + (φ * d t ω) * hr + (c.κ * μ * d t ω) * hφ'
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hφ0)
  have hwm : ∀ t, AEStronglyMeasurable (w t) S.μ := fun t => by
    have hl : StronglyMeasurable[S.𝓕 t] (lag 0 d t) := by
      cases t with
      | zero => exact stronglyMeasurable_const
      | succ s => exact (hda s).mono (S.𝓕.mono (Nat.le_succ s))
    exact (((hda t).sub (hl.const_mul μ)).mono (S.𝓕.le t)).aestronglyMeasurable
  have hwb : S.BddProc w := ⟨max (Cx1 + Cx2) 0 + μ * max (Cx1 + Cx2) 0, fun t => by
    have hl : ∀ᵐ ω ∂S.μ, |lag 0 d t ω| ≤ max (Cx1 + Cx2) 0 := by
      cases t with
      | zero => exact Eventually.of_forall fun ω => by simp [lag]
      | succ s => exact (hdb s).mono fun ω h => h.trans (le_max_left _ _)
    filter_upwards [hdb t, hl] with ω h1 h2
    simp only [hw]
    refine (abs_sub _ _).trans (add_le_add (h1.trans (le_max_left _ _)) ?_)
    rw [abs_mul, abs_of_pos hμ0]
    exact mul_le_mul_of_nonneg_left h2 hμ0.le⟩
  have hw0 := S.forward_unique ha hws (S.solves_zero _) hwm
    (fun _ => aestronglyMeasurable_const) hwb ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩
  have hd0 : ∀ t, d t =ᵐ[S.μ] 0 := by
    intro t
    induction t with
    | zero =>
      filter_upwards [hw0 0] with ω e
      simpa [hw, lag] using e
    | succ s ih =>
      filter_upwards [hw0 (s + 1), ih] with ω e1 e2
      simp only [hw, lag, Pi.zero_apply] at e1 e2 ⊢
      rw [e2, mul_zero, sub_zero] at e1
      exact e1
  intro t
  have hp0 : p t =ᵐ[S.μ] 0 := by
    have hl0 : lag 0 d t =ᵐ[S.μ] 0 := by
      cases t with
      | zero => exact Eventually.of_forall fun ω => rfl
      | succ s => exact hd0 s
    filter_upwards [hcrit t, hd0 t, hl0] with ω e1 e2 e3
    simp only [Pi.zero_apply] at e2 e3 ⊢
    rw [e1, e2, e3]
    ring
  exact ⟨hp0.mono fun ω e => sub_eq_zero.mp e, (hd0 t).mono fun ω e => sub_eq_zero.mp e⟩

/-! ### The limit with no existence hypothesis -/

/-- **Woodford (2003), p. 591, on every filtered probability space, with existence.** Let `l_n > 0`,
`l_n → 0`. For every essentially bounded adapted disturbance `(rⁿ, u)` and every history
`x_{−1}, i_{−1}, i_{−2}`, there are essentially bounded adapted equilibria under the optimal rule
(3.7) with `λᵢ = l_n` (`rule_eqm_existsM`), the (2.5) solution `(pi25, x25)` exists
(`crit25_existsM`, unique a.s. by `crit25_uniqueM`), and the paths converge: for every `ε > 0`,
eventually, at every date, `|πⁿ_t − π⁰_t|, |xⁿ_t − x⁰_t|, |iⁿ_t − i⁰_t| ≤ ε` a.s.
(`TidyR5aLambdaILimitMeasure.paths_convergeM`). -/
theorem paths_convergeM_exists (c : Calib) (hc : c.Adm) {l : ℕ → ℝ} (hlpos : ∀ n, 0 < l n)
    (hl : Tendsto l atTop (𝓝 0)) (S : MeasExpectationSystem Ω) {rn u : ℕ → Ω → ℝ}
    (hra : AdaptedM S rn) (hrb : BndM S rn) (hua : AdaptedM S u) (hub : BndM S u)
    (xm1 im1 im2 : ℝ) :
    ∃ e : ℕ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      (∀ n, RuleEqmM S { c with li := l n } rn u xm1 im1 im2 (e n).1 (e n).2.1 (e n).2.2 ∧
        (AdaptedM S (e n).1 ∧ AdaptedM S (e n).2.1 ∧ AdaptedM S (e n).2.2) ∧
        (BndM S (e n).1 ∧ BndM S (e n).2.1 ∧ BndM S (e n).2.2)) ∧
      (∀ t, ASb S c u (pi25 S c xm1 u) (x25 S c xm1 u) t) ∧
      Crit25M S c xm1 (pi25 S c xm1 u) (x25 S c xm1 u) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ t, ∀ᵐ ω ∂S.μ, |(e n).1 t ω - pi25 S c xm1 u t ω| ≤ ε ∧
        |(e n).2.1 t ω - x25 S c xm1 u t ω| ≤ ε ∧
        |(e n).2.2 t ω - i0M S c rn (pi25 S c xm1 u) (x25 S c xm1 u) t ω| ≤ ε := by
  have hcn : ∀ n, ({ c with li := l n } : Calib).Adm := fun n =>
    ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hlpos n⟩
  have hex : ∀ n, ∃ e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      RuleEqmM S { c with li := l n } rn u xm1 im1 im2 e.1 e.2.1 e.2.2 ∧
        (AdaptedM S e.1 ∧ AdaptedM S e.2.1 ∧ AdaptedM S e.2.2) ∧
        (BndM S e.1 ∧ BndM S e.2.1 ∧ BndM S e.2.2) := fun n => by
    obtain ⟨π, x, i, h⟩ := rule_eqm_existsM _ (hcn n) S hra hrb hua hub xm1 im1 im2
    exact ⟨(π, x, i), h⟩
  choose e he using hex
  obtain ⟨hπ0a, hx0a, hπ0b, hx0b, hAS0, hcr0⟩ := crit25_existsM c hc S hua hub xm1
  exact ⟨e, he, hAS0, hcr0, TidyR5aLambdaILimitMeasure.paths_convergeM c hc hlpos hl hrb xm1 im1
    im2 (fun n => (he n).1) (fun n => (he n).2.1) (fun n => (he n).2.2) hπ0a hx0a hπ0b hx0b hAS0
    hcr0⟩

end Woodford.OptimalPolicyRules.TidyR6bLambdaILimitExists
