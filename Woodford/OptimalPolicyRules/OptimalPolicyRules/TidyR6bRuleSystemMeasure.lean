/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5aLambdaXZeroMeasure
import OptimalPolicyRules.OptimalRulesMeasureStabilityModels

/-!
# The rule system of p. 593 on a probability space: existence for every `λₓ ≥ 0`

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, pp. 592–594: the inflation-inertia model
(2.6) (corrected), (3.1) under commitment to the implicit instrument rule (3.16), on every filtered
probability space with Mathlib's conditional expectation (`TidyR5aLambdaXZeroMeasure.RuleSolM`).

`TidyR5aLambdaXZeroMeasure.rule_system_uniqueM` proves a.s. uniqueness for every `λₓ ≥ 0` and
`TidyR5aLambdaXZeroMeasure.rule_system_existsUniqueM_lx0` existence at `λₓ = 0`. This module
proves **existence for `λₓ > 0`** (every `0 ≤ γ ≤ 1`), porting `TidyRuleSystem.exists_pos` and
`TidyRuleSystem.exists_zero` to conditional expectations: the bounded optimal plan exists on every
probability space (`OptimalRulesMeasureStabilityModels.Inertia.in_m_assumption81MB`,
`OptimalRulesMeasureStabilityModels.NK.nk_m_assumption81MB`), its first-order conditions (3.15),
(3.4), (3.5) hold a.s., and they give the rule (3.16) a.s.

* `in_struct_atM`, `in_foc_atM`, `nk_struct_atM`, `nk_foc_atM`: the rows of (1.1) and (1.9) at
  `(t, ω)` with conditional expectations (read through the perfect-foresight row lemmas at a
  one-point sample space).
* `E_aff22`, `euler_alg`, `eulerM_of_focs`: (3.15), (3.4), (3.5) ⇒ (3.16), a.s.
* `existsM_pos` (`0 < γ ≤ 1`), `existsM_zero` (`γ = 0`): existence for every essentially bounded
  adapted disturbance and history.
* `rule_system_existsM`, `rule_system_existsUniqueM`: existence and a.s. uniqueness for
  `λₓ > 0`, `0 ≤ γ ≤ 1`; `rule_system_existsUniqueM_nonneg`: **for every `λₓ ≥ 0`**;
  `rule_system_existsM_iff`: a solution exists iff the history is essentially bounded and known
  at the right dates.
-/

namespace Woodford.OptimalPolicyRules.TidyR6bRuleSystemMeasure

open MeasureTheory Filter Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure
open TidyR5aLambdaXZeroMeasure (ASm ISm EulerM fbigM BndM AdaptedM RuleSolM HistoryM E_lin4
  integrable_of_sm)
open InflationInertiaRules (ALi qtil)
open GeneralLinks (piOf xOf iOf cNK)
open GeneralLinksInertia (inProblem Zof)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Tools -/

/-- Woodford (2003), p. 540 (tool): `E_t(a₁f₁ + a₂f₂ + b₁g₁ + b₂g₂ + b₃g₃ + k) =
a₁E_tf₁ + a₂E_tf₂ + b₁g₁ + b₂g₂ + b₃g₃ + k` a.s. for integrable `fᵢ` and integrable `gⱼ` known
at `t`. -/
theorem E_aff22 (S : MeasExpectationSystem Ω) (t : ℕ) (a1 a2 b1 b2 b3 k : ℝ)
    {f1 f2 g1 g2 g3 : Ω → ℝ} (h1 : Integrable f1 S.μ) (h2 : Integrable f2 S.μ)
    (k1 : StronglyMeasurable[S.𝓕 t] g1) (k2 : StronglyMeasurable[S.𝓕 t] g2)
    (k3 : StronglyMeasurable[S.𝓕 t] g3) (i1 : Integrable g1 S.μ) (i2 : Integrable g2 S.μ)
    (i3 : Integrable g3 S.μ) :
    ∀ᵐ ω ∂S.μ, S.E t (fun ω => a1 * f1 ω + a2 * f2 ω + b1 * g1 ω + b2 * g2 ω + b3 * g3 ω + k) ω =
      a1 * S.E t f1 ω + a2 * S.E t f2 ω + b1 * g1 ω + b2 * g2 ω + b3 * g3 ω + k := by
  have hk : StronglyMeasurable[S.𝓕 t] (fun ω => b1 * g1 ω + b2 * g2 ω + b3 * g3 ω + k) :=
    (((k1.const_mul b1).add (k2.const_mul b2)).add (k3.const_mul b3)).add
      stronglyMeasurable_const
  have hki : Integrable (fun ω => b1 * g1 ω + b2 * g2 ω + b3 * g3 ω + k) S.μ :=
    (((i1.const_mul b1).add (i2.const_mul b2)).add (i3.const_mul b3)).add (integrable_const k)
  have hfi : Integrable (fun ω => a1 * f1 ω + a2 * f2 ω + 0 * f1 ω + 0 * f1 ω) S.μ :=
    (((h1.const_mul a1).add (h2.const_mul a2)).add (h1.const_mul 0)).add (h1.const_mul 0)
  have e : (fun ω => a1 * f1 ω + a2 * f2 ω + b1 * g1 ω + b2 * g2 ω + b3 * g3 ω + k) =
      (fun ω => a1 * f1 ω + a2 * f2 ω + 0 * f1 ω + 0 * f1 ω) +
        fun ω => b1 * g1 ω + b2 * g2 ω + b3 * g3 ω + k := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [e]
  filter_upwards [S.E_add hfi hki t, E_lin4 S t a1 a2 0 0 h1 h2 h1 h1] with ω e1 e2
  rw [e1, Pi.add_apply, e2, S.E_of_stronglyMeasurable hk hki]
  ring

/-- Woodford (2003), eqs. (3.15), (3.4), (3.5) ⇒ (3.16), pp. 592–593 (the algebra, as in
`InflationInertiaRules.foc315_iff_euler`): with the multipliers substituted from (3.4)–(3.5),
(3.15) at date `t + 2` is the Euler equation (3.16) at `t + 2`, in terms of the date-`t + 2`
forecasts `E i_{t+3}`, `E x_{t+3}`, `E π_{t+3}`. -/
theorem euler_alg {β γ κ σ lx li xstar istar : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (hli : li ≠ 0) (Ei3 Ex3 Eπ3 i0 i1 i2 x1 x2 π1 π2 : ℝ)
    (h : π2 - γ * π1 - β * γ * (Eπ3 - γ * π2) - β⁻¹ * σ * (-(li / σ) * (i1 - istar)) -
      β * γ * ((lx * (Ex3 - xstar) + (-(li / σ)) * (Ei3 - istar) -
        β⁻¹ * (-(li / σ) * (i2 - istar))) / κ) +
      (1 + β * γ) * ((lx * (x2 - xstar) + (-(li / σ)) * (i2 - istar) -
        β⁻¹ * (-(li / σ) * (i1 - istar))) / κ) -
      (lx * (x1 - xstar) + (-(li / σ)) * (i1 - istar) - β⁻¹ * (-(li / σ) * (i0 - istar))) / κ =
        0) :
    β * γ * (Ei3 - istar) - (1 + γ + β * γ) * (i2 - istar) +
        CubicRoots.coefA2 β γ κ σ * (i1 - istar) - β⁻¹ * (i0 - istar) =
      -(κ * σ / li * ((π2 - γ * π1) + lx / κ * (x2 - x1)) -
        β * γ * (κ * σ / li * ((Eπ3 - γ * π2) + lx / κ * (Ex3 - x2)))) := by
  unfold CubicRoots.coefA2
  field_simp at h ⊢
  linear_combination h

/-- **Woodford (2003), eqs. (3.15), (3.4), (3.5) ⇒ (3.16), pp. 592–593, with conditional
expectations**: for essentially bounded adapted `π, x, i` and an integrable multiplier `Ξ₂`, with
`Ξ₁ = −(λᵢ/σ)(i − i*)` ((3.5)), (3.4) a.s. at `t + 1, t + 2, t + 3` and (3.15) a.s. at `t + 2`, the
Euler equation (3.16) holds a.s. at `t + 2`. -/
theorem eulerM_of_focs (S : MeasExpectationSystem Ω) {β γ κ σ lx li xstar istar : ℝ}
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : li ≠ 0) {π x i Ξ2 : ℕ → Ω → ℝ}
    (hπa : AdaptedM S π) (hxa : AdaptedM S x) (hia : AdaptedM S i)
    (hπi : ∀ k, Integrable (π k) S.μ) (hxi : ∀ k, Integrable (x k) S.μ)
    (hii : ∀ k, Integrable (i k) S.μ) (t : ℕ)
    (h4 : ∀ k, t + 1 ≤ k → k ≤ t + 3 → ∀ᵐ ω ∂S.μ, lx * (x k ω - xstar) +
      -(li / σ) * (i k ω - istar) - β⁻¹ * (-(li / σ) * (i (k - 1) ω - istar)) - κ * Ξ2 k ω = 0)
    (h15 : ∀ᵐ ω ∂S.μ, π (t + 2) ω - γ * π (t + 1) ω -
      β * γ * S.E (t + 2) (fun ω' => π (t + 3) ω' - γ * π (t + 2) ω') ω -
      β⁻¹ * σ * (-(li / σ) * (i (t + 1) ω - istar)) - β * γ * S.E (t + 2) (Ξ2 (t + 3)) ω +
      (1 + β * γ) * Ξ2 (t + 2) ω - Ξ2 (t + 1) ω = 0) :
    EulerM S β γ κ σ (fun k ω => i k ω - istar) (fbigM S β γ κ σ lx li π x) t := by
  -- `Ξ₂` at `t + 3` in terms of the target variables
  have hX3 : Ξ2 (t + 3) =ᵐ[S.μ] fun ω => lx / κ * x (t + 3) ω + (-(li / σ) / κ) * i (t + 3) ω +
      (β⁻¹ * (li / σ) / κ) * i (t + 2) ω + 0 * i (t + 2) ω + 0 * i (t + 2) ω +
        (-(lx * xstar) + li / σ * istar - β⁻¹ * (li / σ) * istar) / κ := by
    filter_upwards [h4 (t + 3) (by omega) le_rfl] with ω e
    rw [show t + 3 - 1 = t + 2 by omega] at e
    have h : Ξ2 (t + 3) ω = (lx * (x (t + 3) ω - xstar) + -(li / σ) * (i (t + 3) ω - istar) -
        β⁻¹ * (-(li / σ) * (i (t + 2) ω - istar))) / κ := by
      rw [eq_div_iff hκ]
      linear_combination -e
    rw [h]
    ring
  have hEX := S.E_congr hX3 (t + 2)
  have hEX' := E_aff22 S (t + 2) (lx / κ) (-(li / σ) / κ) (β⁻¹ * (li / σ) / κ) 0 0
    ((-(lx * xstar) + li / σ * istar - β⁻¹ * (li / σ) * istar) / κ) (hxi (t + 3)) (hii (t + 3))
    (hia (t + 2)) (hia (t + 2)) (hia (t + 2)) (hii (t + 2)) (hii (t + 2)) (hii (t + 2))
  have hEπ := E_aff22 S (t + 2) 1 0 (-γ) 0 0 0 (hπi (t + 3)) (hπi (t + 3)) (hπa (t + 2))
    (hπa (t + 2)) (hπa (t + 2)) (hπi (t + 2)) (hπi (t + 2)) (hπi (t + 2))
  have eπ : (fun ω' => π (t + 3) ω' - γ * π (t + 2) ω') = fun ω => 1 * π (t + 3) ω +
      0 * π (t + 3) ω + (-γ) * π (t + 2) ω + 0 * π (t + 2) ω + 0 * π (t + 2) ω + 0 := by
    funext ω
    ring
  have hEq := E_aff22 S (t + 2) (κ * σ / li) (κ * σ / li * (lx / κ)) (-(κ * σ / li * γ))
    (-(κ * σ / li * (lx / κ))) 0 0 (hπi (t + 3)) (hxi (t + 3)) (hπa (t + 2)) (hxa (t + 2))
    (hxa (t + 2)) (hπi (t + 2)) (hxi (t + 2)) (hxi (t + 2))
  have eq3 : qtil γ κ σ lx li π x (t + 2 + 1) = fun ω => κ * σ / li * π (t + 3) ω +
      κ * σ / li * (lx / κ) * x (t + 3) ω + (-(κ * σ / li * γ)) * π (t + 2) ω +
      (-(κ * σ / li * (lx / κ))) * x (t + 2) ω + 0 * x (t + 2) ω + 0 := by
    funext ω
    unfold qtil
    rw [show t + 2 + 1 - 1 = t + 2 by omega, show t + 2 + 1 = t + 3 by omega]
    ring
  have hEA := E_aff22 S (t + 2) (β * γ) 0 (-(1 + γ + β * γ)) (CubicRoots.coefA2 β γ κ σ) (-β⁻¹)
    (-(β * γ) * istar + (1 + γ + β * γ) * istar - CubicRoots.coefA2 β γ κ σ * istar +
      β⁻¹ * istar) (hii (t + 3)) (hii (t + 3)) (hia (t + 2))
    ((hia (t + 1)).mono (S.𝓕.mono (by omega))) ((hia t).mono (S.𝓕.mono (by omega)))
    (hii (t + 2)) (hii (t + 1)) (hii t)
  have eA : ALi β γ κ σ (fun k ω => i k ω - istar) t = fun ω => β * γ * i (t + 3) ω +
      0 * i (t + 3) ω + (-(1 + γ + β * γ)) * i (t + 2) ω +
      CubicRoots.coefA2 β γ κ σ * i (t + 1) ω + (-β⁻¹) * i t ω +
      (-(β * γ) * istar + (1 + γ + β * γ) * istar - CubicRoots.coefA2 β γ κ σ * istar +
        β⁻¹ * istar) := by
    funext ω
    unfold ALi
    ring
  filter_upwards [h15, hEX, hEX', hEπ, hEq, hEA, h4 (t + 2) (by omega) (by omega),
    h4 (t + 1) le_rfl (by omega)] with ω e15 eX eX' eπ' eq' eA' e2 e1
  rw [eπ, eπ', eX, eX'] at e15
  rw [show t + 2 - 1 = t + 1 by omega] at e2
  rw [show t + 1 - 1 = t by omega] at e1
  have hΞ2 : Ξ2 (t + 2) ω = (lx * (x (t + 2) ω - xstar) + -(li / σ) * (i (t + 2) ω - istar) -
      β⁻¹ * (-(li / σ) * (i (t + 1) ω - istar))) / κ := by
    rw [eq_div_iff hκ]
    linear_combination -e2
  have hΞ1 : Ξ2 (t + 1) ω = (lx * (x (t + 1) ω - xstar) + -(li / σ) * (i (t + 1) ω - istar) -
      β⁻¹ * (-(li / σ) * (i t ω - istar))) / κ := by
    rw [eq_div_iff hκ]
    linear_combination -e1
  rw [hΞ2, hΞ1] at e15
  unfold fbigM
  rw [eA, eA', eq3, eq']
  have key := euler_alg (γ := γ) (lx := lx) (xstar := xstar) (istar := istar) hβ hκ hσ hli
    (S.E (t + 2) (i (t + 3)) ω) (S.E (t + 2) (x (t + 3)) ω) (S.E (t + 2) (π (t + 3)) ω)
    (i t ω) (i (t + 1) ω) (i (t + 2) ω) (x (t + 1) ω) (x (t + 2) ω) (π (t + 1) ω) (π (t + 2) ω)
    (by linear_combination e15)
  unfold qtil
  rw [show t + 2 - 1 = t + 1 by omega]
  linear_combination key

/-! ### The rows of (1.1) and (1.9) with conditional expectations -/

/-- Woodford (2003), (1.1) for the inflation-inertia model at `(t, ω)` with conditional
expectations: `Z_{t+1} = π_t`, `βE_tπ_{t+1} = −γZ_t + (1 + βγ)π_t − κx_t + c₀` and
`σE_tπ_{t+1} + E_tx_{t+1} = x_t + σi_t + c₁` (the perfect-foresight row lemma
`InertiaFOCSystem.in_struct_at` read at a one-point sample space whose date-`t + 1` vector carries
the conditional forecasts). -/
theorem in_struct_atM (c : IRuleBasic.Calib) (γ : ℝ) (hc : c.Adm) (hγ : 0 ≤ γ)
    (S : MeasExpectationSystem Ω) (cd : ℕ → Ω → Fin 2 → ℝ)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω)
    (h1 : Zpart (y (t + 1) ω) = (inProblem c γ hc hγ).sys.A11 *ᵥ Zpart (y t ω) +
        (inProblem c γ hc hγ).sys.A12 *ᵥ zpart (y t ω))
    (h2 : (inProblem c γ hc hγ).sys.Et *ᵥ EVm S t (fun ω' => zpart (y (t + 1) ω')) ω =
        (inProblem c γ hc hγ).sys.A21 *ᵥ Zpart (y t ω) +
          (inProblem c γ hc hγ).sys.A22 *ᵥ zpart (y t ω) +
          ipart (y t ω) • (inProblem c γ hc hγ).sys.B2 + cd t ω) :
    Zof y (t + 1) ω = piOf y t ω ∧
        c.β * S.E t (piOf y (t + 1)) ω =
          -γ * Zof y t ω + (1 + c.β * γ) * piOf y t ω - c.κ * xOf y t ω + cd t ω 0 ∧
        c.σ * S.E t (piOf y (t + 1)) ω + S.E t (xOf y (t + 1)) ω =
          xOf y t ω + c.σ * iOf y t ω + cd t ω 1 := by
  let v1 : (Unit ⊕ Fin 2) ⊕ Unit → ℝ := Sum.elim (Sum.elim (Zpart (y (t + 1) ω))
    (EVm S t (fun ω' => zpart (y (t + 1) ω')) ω)) (fun _ => 0)
  let y' : ℕ → Unit → (Unit ⊕ Fin 2) ⊕ Unit → ℝ := fun s _ => match s with
    | 0 => y t ω
    | _ + 1 => v1
  exact (InertiaFOCSystem.in_struct_at c γ hc hγ perfectForesight (fun _ _ => cd t ω) y' 0
    ()).mp ⟨h1, h2⟩

/-- Woodford (2003), (1.9) for the inflation-inertia model at `(t, ω)` with conditional
expectations, pp. 541 and 592: the rows of `Z`, `π`, `x` and `i`, with the date-`t` forecasts of
`φ_{t+1}` (`GeneralLinksInertia.in_foc_at_iff` read at a one-point sample space). -/
theorem in_foc_atM (c : IRuleBasic.Calib) (γ : ℝ) (hc : c.Adm) (hγ : 0 ≤ γ)
    (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ)
    (φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ) (t : ℕ) (ω : Ω)
    (h : (inProblem c γ hc hγ).sys.Atilᵀ *ᵥ EVm S t (φ (t + 1)) ω +
      (inProblem c γ hc hγ).Tᵀ *ᵥ ((inProblem c γ hc hγ).W *ᵥ ((inProblem c γ hc hγ).T *ᵥ y t ω -
        (inProblem c γ hc hγ).τstar)) - (inProblem c γ hc hγ).β⁻¹ •
          ((inProblem c γ hc hγ).sys.Itilᵀ *ᵥ φ t ω) = 0) :
    -γ * S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 0)) ω - γ * (piOf y t ω - γ * Zof y t ω) -
        c.β⁻¹ * φ t ω (Sum.inl ()) = 0 ∧
      S.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω +
        (1 + c.β * γ) * S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 0)) ω +
        (piOf y t ω - γ * Zof y t ω) - c.β⁻¹ * (c.β * φ t ω (Sum.inr 0) +
          c.σ * φ t ω (Sum.inr 1)) = 0 ∧
      -c.κ * S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 0)) ω +
        S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 1)) ω + c.lx * (xOf y t ω - c.xstar) -
        c.β⁻¹ * φ t ω (Sum.inr 1) = 0 ∧
      c.σ * S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 1)) ω + c.li * (iOf y t ω - c.istar) = 0 := by
  let φ' : ℕ → Unit → Unit ⊕ Fin 2 → ℝ := fun s _ => match s with
    | 0 => φ t ω
    | _ + 1 => EVm S t (φ (t + 1)) ω
  exact (GeneralLinksInertia.in_foc_at_iff c γ hc hγ perfectForesight (fun _ _ => y t ω)
    (φ := φ') (fun _ _ => rfl) 0 ()).mp h

/-- Woodford (2003), (2.1) and (3.1) as (1.1) for the basic model at `(t, ω)` with conditional
expectations (`NKAssumption81.NK.nk_struct_at` read at a one-point sample space). -/
theorem nk_struct_atM (c : IRuleBasic.Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω)
    (cd : ℕ → Ω → Fin 2 → ℝ) (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω)
    (h2 : (GeneralLinks.nkProblem c hc).sys.Et *ᵥ EVm S t (fun ω' => zpart (y (t + 1) ω')) ω =
        (GeneralLinks.nkProblem c hc).sys.A21 *ᵥ Zpart (y t ω) +
          (GeneralLinks.nkProblem c hc).sys.A22 *ᵥ zpart (y t ω) +
          ipart (y t ω) • (GeneralLinks.nkProblem c hc).sys.B2 + cd t ω) :
    c.β * S.E t (piOf y (t + 1)) ω = piOf y t ω - c.κ * xOf y t ω + cd t ω 0 ∧
      c.σ * S.E t (piOf y (t + 1)) ω + S.E t (xOf y (t + 1)) ω =
        xOf y t ω + c.σ * iOf y t ω + cd t ω 1 := by
  let v1 : (Empty ⊕ Fin 2) ⊕ Unit → ℝ := Sum.elim (Sum.elim (Zpart (y (t + 1) ω))
    (EVm S t (fun ω' => zpart (y (t + 1) ω')) ω)) (fun _ => 0)
  let y' : ℕ → Unit → (Empty ⊕ Fin 2) ⊕ Unit → ℝ := fun s _ => match s with
    | 0 => y t ω
    | _ + 1 => v1
  exact (NKAssumption81.NK.nk_struct_at c hc.2.2.1.ne' perfectForesight (fun _ _ => cd t ω) y'
    0 ()).mp h2

/-- Woodford (2003), (3.3)–(3.5) as (1.9) for the basic model at `(t, ω)` with conditional
expectations, p. 584 (`GeneralLinks.nk_foc_at_iff` read at a one-point sample space). -/
theorem nk_foc_atM (c : IRuleBasic.Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω)
    (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) (φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ) (t : ℕ) (ω : Ω)
    (h : (GeneralLinks.nkProblem c hc).sys.Atilᵀ *ᵥ EVm S t (φ (t + 1)) ω +
      (GeneralLinks.nkProblem c hc).Tᵀ *ᵥ ((GeneralLinks.nkProblem c hc).W *ᵥ
        ((GeneralLinks.nkProblem c hc).T *ᵥ y t ω - (GeneralLinks.nkProblem c hc).τstar)) -
        (GeneralLinks.nkProblem c hc).β⁻¹ •
          ((GeneralLinks.nkProblem c hc).sys.Itilᵀ *ᵥ φ t ω) = 0) :
    piOf y t ω - c.σ / c.β * φ t ω (Sum.inr 1) + S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 0)) ω -
        φ t ω (Sum.inr 0) = 0 ∧
      c.lx * (xOf y t ω - c.xstar) + S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 1)) ω -
        c.β⁻¹ * φ t ω (Sum.inr 1) - c.κ * S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 0)) ω = 0 ∧
      c.li * (iOf y t ω - c.istar) + c.σ * S.E t (fun ω' => φ (t + 1) ω' (Sum.inr 1)) ω = 0 := by
  let φ' : ℕ → Unit → Empty ⊕ Fin 2 → ℝ := fun s _ => match s with
    | 0 => φ t ω
    | _ + 1 => EVm S t (φ (t + 1)) ω
  exact (GeneralLinks.nk_foc_at_iff c hc perfectForesight (fun _ _ => y t ω) (φ := φ')
    (fun _ _ => rfl) 0 ()).mp h

/-! ### Data: disturbances and pre-sample multipliers -/

/-- Woodford (2003), (2.1)/(2.6), (3.1) as (1.1) (tool): the disturbance vector `cNK` of
essentially bounded disturbances is essentially bounded. -/
theorem cNK_bddM (c : IRuleBasic.Calib) {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ}
    (hub : BndM S u) (hrb : BndM S rn) : MBoundedV S (cNK c u rn) := by
  obtain ⟨Cu, hCu⟩ := hub
  obtain ⟨Cr, hCr⟩ := hrb
  refine ⟨Cu + |c.σ| * Cr, fun t => ?_⟩
  filter_upwards [hCu t, hCr t] with ω h1 h2 j
  have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg c.σ)
  have h4 : 0 ≤ |c.σ| * |rn t ω| := by positivity
  have h5 : 0 ≤ |u t ω| := abs_nonneg _
  fin_cases j
  · change |-u t ω| ≤ _
    rw [abs_neg]
    linarith
  · change |-(c.σ * rn t ω)| ≤ _
    rw [abs_neg, abs_mul]
    linarith

/-- Woodford (2003), (2.1)/(2.6), (3.1) as (1.1) (tool): the disturbance vector `cNK` of adapted
disturbances is adapted. -/
theorem cNK_adaptedM (c : IRuleBasic.Calib) {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ}
    (hua : AdaptedM S u) (hra : AdaptedM S rn) : MAdaptedV S (cNK c u rn) := by
  intro t j
  fin_cases j
  · exact (hua t).neg
  · exact ((hra t).const_mul c.σ).neg

/-- Woodford (2003), (3.5), p. 584: the pre-sample multiplier `Ξ₁,₁ = −(λᵢ/σ)(i₁ − i*)` inferred
from the history. -/
noncomputable def X1of (c : IRuleBasic.Calib) (i1 : Ω → ℝ) : Ω → ℝ :=
  fun ω => -(c.li / c.σ) * (i1 ω - c.istar)

/-- Woodford (2003), (3.4)–(3.5), p. 584: the pre-sample multiplier
`Ξ₂,₁ = (λₓ(x₁ − x*) + Ξ₁,₁ − β⁻¹Ξ₁,₀)/κ` inferred from the history. -/
noncomputable def X2of (c : IRuleBasic.Calib) (x1 i1 i0 : Ω → ℝ) : Ω → ℝ :=
  fun ω => (c.lx * (x1 ω - c.xstar) + X1of c i1 ω - c.β⁻¹ * (-(c.li / c.σ) * (i0 ω - c.istar))) /
    c.κ

/-- Woodford (2003), p. 593: the pre-sample multipliers `M₁ = (Ξ₂,₁, Ξ₁,₁)` inferred from the
history `(x₁, i₁, i₀)`. -/
noncomputable def M0of (c : IRuleBasic.Calib) (x1 i1 i0 : Ω → ℝ) : Ω → Fin 2 → ℝ :=
  fun ω => ![X2of c x1 i1 i0 ω, X1of c i1 ω]

/-- Woodford (2003), p. 593 (tool): an affine combination of three random variables bounded by
`K` is bounded by `|a|K + |b|K + |d|K + |e|`. -/
theorem abs_lin3_le {f g h K a b d e : ℝ} (hf : |f| ≤ K) (hg : |g| ≤ K) (hh : |h| ≤ K) :
    |a * f + b * g + d * h + e| ≤ |a| * K + |b| * K + |d| * K + |e| := by
  have e1 := abs_add_le (a * f + b * g + d * h) e
  have e2 := abs_add_le (a * f + b * g) (d * h)
  have e3 := abs_add_le (a * f) (b * g)
  rw [abs_mul] at e2 e3
  rw [abs_mul] at e3
  have m1 := mul_le_mul_of_nonneg_left hf (abs_nonneg a)
  have m2 := mul_le_mul_of_nonneg_left hg (abs_nonneg b)
  have m3 := mul_le_mul_of_nonneg_left hh (abs_nonneg d)
  linarith

/-- Woodford (2003), p. 593: for an essentially bounded history known at the right dates, the
pre-sample multipliers `M₁` are essentially bounded and known at date 1. -/
theorem M0of_spec (c : IRuleBasic.Calib) {S : MeasExpectationSystem Ω} {p1 x1 i1 i0 : Ω → ℝ}
    (hh : HistoryM S p1 x1 i1 i0) : MKnownV S 1 (M0of c x1 i1 i0) ∧
      MBoundedRV S (M0of c x1 i1 i0) := by
  obtain ⟨-, hx1, hi1, hi0, K, hK⟩ := hh
  have hi0' : StronglyMeasurable[S.𝓕 1] i0 := hi0.mono (S.𝓕.mono (by norm_num))
  have eX1 : X1of c i1 = fun ω => -(c.li / c.σ) * i1 ω + 0 * x1 ω + 0 * i0 ω +
      c.li / c.σ * c.istar := by
    funext ω
    simp only [X1of]
    ring
  have eX2 : X2of c x1 i1 i0 = fun ω => c.lx / c.κ * x1 ω + (-(c.li / c.σ) / c.κ) * i1 ω +
      (c.β⁻¹ * (c.li / c.σ) / c.κ) * i0 ω +
        (-(c.lx * c.xstar) + c.li / c.σ * c.istar - c.β⁻¹ * (c.li / c.σ) * c.istar) / c.κ := by
    funext ω
    simp only [X2of, X1of]
    ring
  refine ⟨fun j => ?_, ⟨max (|-(c.li / c.σ)| * K + |0| * K + |0| * K + |c.li / c.σ * c.istar|)
    (|c.lx / c.κ| * K + |-(c.li / c.σ) / c.κ| * K + |c.β⁻¹ * (c.li / c.σ) / c.κ| * K +
      |(-(c.lx * c.xstar) + c.li / c.σ * c.istar - c.β⁻¹ * (c.li / c.σ) * c.istar) / c.κ|), ?_⟩⟩
  · fin_cases j
    · change StronglyMeasurable[S.𝓕 1] (X2of c x1 i1 i0)
      rw [eX2]
      exact (((hx1.const_mul _).add (hi1.const_mul _)).add (hi0'.const_mul _)).add
        stronglyMeasurable_const
    · change StronglyMeasurable[S.𝓕 1] (X1of c i1)
      rw [eX1]
      exact (((hi1.const_mul _).add (hx1.const_mul _)).add (hi0'.const_mul _)).add
        stronglyMeasurable_const
  · filter_upwards [hK] with ω h j
    obtain ⟨-, h2, h3, h4⟩ := h
    fin_cases j
    · change |X2of c x1 i1 i0 ω| ≤ _
      rw [eX2]
      exact (abs_lin3_le h2 h3 h4).trans (le_max_right _ _)
    · change |X1of c i1 ω| ≤ _
      rw [eX1]
      exact (abs_lin3_le h3 h2 h4).trans (le_max_left _ _)

/-! ### Existence for `0 < γ ≤ 1` -/

/-- **Woodford (2003), p. 593, on a filtered probability space: existence for `0 < γ ≤ 1` and
`λₓ > 0`.** For every essentially bounded adapted disturbance `(u, rⁿ)` and every essentially
bounded history `(π₁, x₁, i₁, i₀)` (`π₁, x₁, i₁` known at 1, `i₀` at 0), the rule system (2.6),
(3.1), (3.16) has an essentially bounded adapted solution with that history, with Mathlib's
conditional expectation: the bounded optimal plan from `t₀ = 2`
(`OptimalRulesMeasureStabilityModels.Inertia.in_m_assumption81MB`) with `Z₂ = π₁` and `M₁`
inferred from `(x₁, i₁, i₀)` (`M0of`), with the history glued in at dates 0 and 1. -/
theorem existsM_pos (c : IRuleBasic.Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (S : MeasExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u) (hub : BndM S u)
    (hra : AdaptedM S rn) (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : HistoryM S p1 x1 i1 i0) : ∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hκ : c.κ ≠ 0 := hc.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  have hb' : c.β⁻¹ * c.β = 1 := inv_mul_cancel₀ hβ
  have hb : c.β * c.β⁻¹ = 1 := mul_inv_cancel₀ hβ
  obtain ⟨hMk, hMb⟩ := M0of_spec c hh
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  set Z0 : Ω → Unit → ℝ := fun ω _ => p1 ω with hZ0d
  have hZk : MKnownV S 2 Z0 := fun _ => hp1.mono (S.𝓕.mono (by norm_num))
  have hZb : MBoundedRV S Z0 := ⟨K, hK.mono fun ω h _ => h.1⟩
  obtain ⟨y, φ, hs⟩ := (OptimalRulesMeasureStabilityModels.Inertia.in_m_assumption81MB c γ hc
    hγ0 hγ1 S 2).solvable (cNK c u rn) Z0 (M0of c x1 i1 i0) (cNK_bddM c hub hrb)
    (cNK_adaptedM c hua hra) hZk hZb hMb hMk
  obtain ⟨⟨hst, hZ0, ⟨My, hMy⟩, hya⟩, ⟨Kφ, hKφ⟩, hφm, hM, hMe, hfoc⟩ := hs
  -- the rows
  have hS : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, Zof y (k + 1) ω = piOf y k ω ∧
      c.β * S.E k (piOf y (k + 1)) ω =
        -γ * Zof y k ω + (1 + c.β * γ) * piOf y k ω - c.κ * xOf y k ω + cNK c u rn k ω 0 ∧
      c.σ * S.E k (piOf y (k + 1)) ω + S.E k (xOf y (k + 1)) ω =
        xOf y k ω + c.σ * iOf y k ω + cNK c u rn k ω 1 := fun k hk => by
    filter_upwards [(hst k hk).1, (hst k hk).2] with ω e1 e2
    exact in_struct_atM c γ hc hγ0.le S _ y k ω e1 e2
  have hφi : ∀ k j, Integrable (fun ω => φ k ω j) S.μ := fun k j =>
    integrable_of_bound (hφm k j) ((hKφ k).mono fun ω h => h j)
  have hEM : ∀ k j, S.E k (fun ω' => φ (k + 1) ω' (Sum.inr j)) =
      fun ω' => φ (k + 1) ω' (Sum.inr j) := fun k j =>
    S.E_of_stronglyMeasurable (hM k j) (hφi _ _)
  have hF : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ,
      -γ * φ (k + 1) ω (Sum.inr 0) - γ * (piOf y k ω - γ * Zof y k ω) -
        c.β⁻¹ * φ k ω (Sum.inl ()) = 0 ∧
      S.E k (fun ω' => φ (k + 1) ω' (Sum.inl ())) ω + (1 + c.β * γ) * φ (k + 1) ω (Sum.inr 0) +
        (piOf y k ω - γ * Zof y k ω) - c.β⁻¹ * (c.β * φ k ω (Sum.inr 0) +
          c.σ * φ k ω (Sum.inr 1)) = 0 ∧
      -c.κ * φ (k + 1) ω (Sum.inr 0) + φ (k + 1) ω (Sum.inr 1) + c.lx * (xOf y k ω - c.xstar) -
        c.β⁻¹ * φ k ω (Sum.inr 1) = 0 ∧
      c.σ * φ (k + 1) ω (Sum.inr 1) + c.li * (iOf y k ω - c.istar) = 0 := fun k hk =>
    (hfoc k hk).mono fun ω e => by
      have := in_foc_atM c γ hc hγ0.le S y φ k ω e
      simp only [hEM] at this
      exact this
  -- the glued processes
  set π : ℕ → Ω → ℝ := fun k => if k = 1 then p1 else piOf y k with hπd
  set x : ℕ → Ω → ℝ := fun k => if k = 1 then x1 else xOf y k with hxd
  set i : ℕ → Ω → ℝ := fun k => if k = 0 then i0 else if k = 1 then i1 else iOf y k with hid
  set Ξ2 : ℕ → Ω → ℝ := fun k ω => φ (k + 1) ω (Sum.inr 0) with hΞ2d
  have hπk : ∀ k, 2 ≤ k → π k = piOf y k := fun k hk => by
    simp only [hπd, show k ≠ 1 by omega, ↓reduceIte]
  have hxk : ∀ k, 2 ≤ k → x k = xOf y k := fun k hk => by
    simp only [hxd, show k ≠ 1 by omega, ↓reduceIte]
  have hik : ∀ k, 2 ≤ k → i k = iOf y k := fun k hk => by
    simp only [hid, show k ≠ 0 by omega, show k ≠ 1 by omega, ↓reduceIte]
  have hπ1 : π 1 = p1 := by simp only [hπd, ↓reduceIte]
  have hx1' : x 1 = x1 := by simp only [hxd, ↓reduceIte]
  have hi1' : i 1 = i1 := by simp only [hid, one_ne_zero, ↓reduceIte]
  have hi0' : i 0 = i0 := by simp only [hid, ↓reduceIte]
  have hπa : AdaptedM S π := fun k => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hπd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 0))
      · rw [hπ1]; exact hp1
    · rw [hπk k hk]; exact hya k (Sum.inl (Sum.inr 0))
  have hxa : AdaptedM S x := fun k => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hxd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 1))
      · rw [hx1']; exact hx1
    · rw [hxk k hk]; exact hya k (Sum.inl (Sum.inr 1))
  have hia : AdaptedM S i := fun k => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [hi0']; exact hi0
      · rw [hi1']; exact hi1
    · rw [hik k hk]; exact hya k (Sum.inr ())
  have hπb : BndM S π := ⟨max My K, fun k => by
    rcases eq_or_ne k 1 with rfl | hk
    · rw [hπ1]; exact hK.mono fun ω h => h.1.trans (le_max_right _ _)
    · simp only [hπd, hk, ↓reduceIte]
      exact (hMy k).mono fun ω h => (h _).trans (le_max_left _ _)⟩
  have hxb : BndM S x := ⟨max My K, fun k => by
    rcases eq_or_ne k 1 with rfl | hk
    · rw [hx1']; exact hK.mono fun ω h => h.2.1.trans (le_max_right _ _)
    · simp only [hxd, hk, ↓reduceIte]
      exact (hMy k).mono fun ω h => (h _).trans (le_max_left _ _)⟩
  have hib : BndM S i := ⟨max My K, fun k => by
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hi0']; exact hK.mono fun ω h => h.2.2.2.trans (le_max_right _ _)
    rcases eq_or_ne k 1 with rfl | hk
    · rw [hi1']; exact hK.mono fun ω h => h.2.2.1.trans (le_max_right _ _)
    · simp only [hid, hk0, hk, ↓reduceIte]
      exact (hMy k).mono fun ω h => (h _).trans (le_max_left _ _)⟩
  have hπi : ∀ k, Integrable (π k) S.μ := fun k =>
    integrable_of_sm S (hπa k) (hπb.choose_spec k)
  have hxi : ∀ k, Integrable (x k) S.μ := fun k =>
    integrable_of_sm S (hxa k) (hxb.choose_spec k)
  have hii : ∀ k, Integrable (i k) S.μ := fun k =>
    integrable_of_sm S (hia k) (hib.choose_spec k)
  have hΞi : ∀ k, Integrable (Ξ2 k) S.μ := fun k => hφi (k + 1) (Sum.inr 0)
  -- `Z_k = π_{k−1}`
  have hZ : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, Zof y k ω = π (k - 1) ω := by
    intro k hk
    rcases Nat.lt_or_ge k 3 with h3 | h3
    · obtain rfl : k = 2 := by omega
      filter_upwards [hZ0] with ω e
      rw [show 2 - 1 = 1 from rfl, hπ1]
      exact congrFun e ()
    · filter_upwards [hS (k - 1) (by omega)] with ω e
      have e1 := e.1
      rw [show k - 1 + 1 = k by omega] at e1
      rw [e1, hπk (k - 1) (by omega)]
  -- the multiplier `Ξ₁`
  have hXi1 : ∀ k, 1 ≤ k → ∀ᵐ ω ∂S.μ,
      φ (k + 1) ω (Sum.inr 1) = -(c.li / c.σ) * (i k ω - c.istar) := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      filter_upwards [hMe] with ω e
      have := congrFun e 1
      rw [hi1']
      exact this
    · filter_upwards [hF k h2] with ω e
      rw [hik k h2]
      field_simp
      linear_combination e.2.2.2
  have hXi21 : ∀ᵐ ω ∂S.μ, Ξ2 1 ω = X2of c x1 i1 i0 ω := by
    filter_upwards [hMe] with ω e
    exact congrFun e 0
  -- (3.4)
  have h4 : ∀ k, 1 ≤ k → ∀ᵐ ω ∂S.μ, c.lx * (x k ω - c.xstar) +
      -(c.li / c.σ) * (i k ω - c.istar) - c.β⁻¹ * (-(c.li / c.σ) * (i (k - 1) ω - c.istar)) -
        c.κ * Ξ2 k ω = 0 := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      filter_upwards [hXi21] with ω e
      rw [e, hx1', hi1', show 1 - 1 = 0 from rfl, hi0']
      simp only [X2of, X1of]
      field_simp
      ring
    · filter_upwards [hF k h2, hXi1 k (by omega), hXi1 (k - 1) (by omega)] with ω e e1 e2
      rw [show k - 1 + 1 = k by omega] at e2
      have e3 := e.2.2.1
      rw [e1, e2, ← hxk k h2] at e3
      simp only [hΞ2d]
      linear_combination e3
  -- (3.15)
  have h15 : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, π k ω - γ * π (k - 1) ω -
      c.β * γ * S.E k (fun ω' => π (k + 1) ω' - γ * π k ω') ω -
      c.β⁻¹ * c.σ * (-(c.li / c.σ) * (i (k - 1) ω - c.istar)) -
      c.β * γ * S.E k (Ξ2 (k + 1)) ω + (1 + c.β * γ) * Ξ2 k ω - Ξ2 (k - 1) ω = 0 := by
    intro k hk
    have hφ0 : (fun ω => φ (k + 1) ω (Sum.inl ())) =ᵐ[S.μ] fun ω => (-(c.β * γ)) * Ξ2 (k + 1) ω +
        (-(c.β * γ)) * π (k + 1) ω + (c.β * γ * γ) * π k ω + 0 * π k ω + 0 * π k ω + 0 := by
      filter_upwards [hF (k + 1) (by omega), hS k hk] with ω e es
      have e0 := e.1
      rw [es.1, ← hπk (k + 1) (by omega), ← hπk k hk] at e0
      simp only [hΞ2d]
      linear_combination (-c.β) * e0 - (φ (k + 1) ω (Sum.inl ())) * hb
    have hE1 := (S.E_congr hφ0 k).trans (E_aff22 S k (-(c.β * γ)) (-(c.β * γ)) (c.β * γ * γ) 0 0 0
      (hΞi (k + 1)) (hπi (k + 1)) (hπa k) (hπa k) (hπa k) (hπi k) (hπi k) (hπi k))
    have eπ : (fun ω' => π (k + 1) ω' - γ * π k ω') = fun ω => 1 * π (k + 1) ω +
        0 * π (k + 1) ω + (-γ) * π k ω + 0 * π k ω + 0 * π k ω + 0 := by
      funext ω
      ring
    have hEπ := E_aff22 S k 1 0 (-γ) 0 0 0 (hπi (k + 1)) (hπi (k + 1)) (hπa k) (hπa k) (hπa k)
      (hπi k) (hπi k) (hπi k)
    filter_upwards [hF k hk, hE1, hEπ, hZ k hk, hXi1 (k - 1) (by omega)] with ω e eE eP eZ eX
    rw [show k - 1 + 1 = k by omega] at eX
    have e2 := e.2.1
    rw [eE, eZ, eX, ← hπk k hk] at e2
    rw [eπ, eP]
    have hΞk1 : Ξ2 (k - 1) ω = φ k ω (Sum.inr 0) := by
      simp only [hΞ2d, show k - 1 + 1 = k by omega]
    rw [hΞk1]
    simp only [hΞ2d] at e2 ⊢
    linear_combination e2 + (φ k ω (Sum.inr 0)) * hb'
  -- (2.6) and (3.1)
  have hAS : ∀ k, 2 ≤ k → ASm S c.β γ c.κ u π x k := by
    intro k hk
    have eπ : (fun ω' => π (k + 1) ω' - γ * π k ω') = fun ω => 1 * π (k + 1) ω +
        0 * π (k + 1) ω + (-γ) * π k ω + 0 * π k ω + 0 * π k ω + 0 := by
      funext ω
      ring
    filter_upwards [hS k hk, hZ k hk, E_aff22 S k 1 0 (-γ) 0 0 0 (hπi (k + 1)) (hπi (k + 1))
      (hπa k) (hπa k) (hπa k) (hπi k) (hπi k) (hπi k)] with ω e eZ eP
    have e1 := e.2.1
    rw [← hπk (k + 1) (by omega), eZ, ← hπk k hk, ← hxk k hk] at e1
    rw [eπ, eP]
    simp only [cNK, Matrix.cons_val_zero] at e1
    linear_combination -e1
  have hIS : ∀ k, 2 ≤ k → ISm S c.σ rn π x i k := by
    intro k hk
    filter_upwards [hS k hk] with ω e
    have e1 := e.2.2
    rw [← hπk (k + 1) (by omega), ← hxk k hk, ← hxk (k + 1) (by omega), ← hik k hk] at e1
    simp only [cNK, Matrix.cons_val_one, Matrix.cons_val_zero] at e1
    linear_combination -e1
  refine ⟨π, x, i, hπa, hxa, hia, hπb, hxb, hib, hAS, hIS, fun t => ?_, hπ1, hx1', hi1', hi0'⟩
  refine eulerM_of_focs S hβ hκ hσ hli hπa hxa hia hπi hxi hii t
    (fun k hk1 _ => h4 k (by omega)) ?_
  have := h15 (t + 2) (by omega)
  rw [show t + 2 - 1 = t + 1 by omega, show t + 2 + 1 = t + 3 by omega] at this
  exact this

/-! ### Existence for `γ = 0` -/

/-- **Woodford (2003), p. 593, on a filtered probability space: existence for `γ = 0` and
`λₓ > 0`.** For every essentially bounded adapted disturbance and every essentially bounded
history known at the right dates, the rule system at `γ = 0` has an essentially bounded adapted
solution with that history: the bounded optimal plan of the basic problem from `t₀ = 2`
(`OptimalRulesMeasureStabilityModels.NK.nk_m_assumption81MB`) with `M₁` inferred from the history,
with the history glued in. -/
theorem existsM_zero (c : IRuleBasic.Calib) (hc : c.Adm) (S : MeasExpectationSystem Ω)
    {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u) (hub : BndM S u) (hra : AdaptedM S rn)
    (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ} (hh : HistoryM S p1 x1 i1 i0) :
    ∃ π x i, RuleSolM S c 0 u rn p1 x1 i1 i0 π x i := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hκ : c.κ ≠ 0 := hc.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  have hb' : c.β⁻¹ * c.β = 1 := inv_mul_cancel₀ hβ
  obtain ⟨hMk, hMb⟩ := M0of_spec c hh
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  set Z0 : Ω → Empty → ℝ := fun _ e => e.elim with hZ0d
  have hZk : MKnownV S 2 Z0 := fun e => e.elim
  have hZb : MBoundedRV S Z0 := ⟨0, Eventually.of_forall fun _ e => e.elim⟩
  obtain ⟨y, φ, hs⟩ := (OptimalRulesMeasureStabilityModels.NK.nk_m_assumption81MB c hc S
    2).solvable (cNK c u rn) Z0 (M0of c x1 i1 i0) (cNK_bddM c hub hrb)
    (cNK_adaptedM c hua hra) hZk hZb hMb hMk
  obtain ⟨⟨hst, -, ⟨My, hMy⟩, hya⟩, ⟨Kφ, hKφ⟩, hφm, hM, hMe, hfoc⟩ := hs
  have hS : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ,
      c.β * S.E k (piOf y (k + 1)) ω = piOf y k ω - c.κ * xOf y k ω + cNK c u rn k ω 0 ∧
      c.σ * S.E k (piOf y (k + 1)) ω + S.E k (xOf y (k + 1)) ω =
        xOf y k ω + c.σ * iOf y k ω + cNK c u rn k ω 1 := fun k hk => by
    filter_upwards [(hst k hk).2] with ω e2
    exact nk_struct_atM c hc S _ y k ω e2
  have hφi : ∀ k j, Integrable (fun ω => φ k ω j) S.μ := fun k j =>
    integrable_of_bound (hφm k j) ((hKφ k).mono fun ω h => h j)
  have hEM : ∀ k j, S.E k (fun ω' => φ (k + 1) ω' (Sum.inr j)) =
      fun ω' => φ (k + 1) ω' (Sum.inr j) := fun k j =>
    S.E_of_stronglyMeasurable (hM k j) (hφi _ _)
  have hF : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ,
      piOf y k ω - c.σ / c.β * φ k ω (Sum.inr 1) + φ (k + 1) ω (Sum.inr 0) -
        φ k ω (Sum.inr 0) = 0 ∧
      c.lx * (xOf y k ω - c.xstar) + φ (k + 1) ω (Sum.inr 1) - c.β⁻¹ * φ k ω (Sum.inr 1) -
        c.κ * φ (k + 1) ω (Sum.inr 0) = 0 ∧
      c.li * (iOf y k ω - c.istar) + c.σ * φ (k + 1) ω (Sum.inr 1) = 0 := fun k hk =>
    (hfoc k hk).mono fun ω e => by
      have := nk_foc_atM c hc S y φ k ω e
      simp only [hEM] at this
      exact this
  set π : ℕ → Ω → ℝ := fun k => if k = 1 then p1 else piOf y k with hπd
  set x : ℕ → Ω → ℝ := fun k => if k = 1 then x1 else xOf y k with hxd
  set i : ℕ → Ω → ℝ := fun k => if k = 0 then i0 else if k = 1 then i1 else iOf y k with hid
  set Ξ2 : ℕ → Ω → ℝ := fun k ω => φ (k + 1) ω (Sum.inr 0) with hΞ2d
  have hπk : ∀ k, 2 ≤ k → π k = piOf y k := fun k hk => by
    simp only [hπd, show k ≠ 1 by omega, ↓reduceIte]
  have hxk : ∀ k, 2 ≤ k → x k = xOf y k := fun k hk => by
    simp only [hxd, show k ≠ 1 by omega, ↓reduceIte]
  have hik : ∀ k, 2 ≤ k → i k = iOf y k := fun k hk => by
    simp only [hid, show k ≠ 0 by omega, show k ≠ 1 by omega, ↓reduceIte]
  have hπ1 : π 1 = p1 := by simp only [hπd, ↓reduceIte]
  have hx1' : x 1 = x1 := by simp only [hxd, ↓reduceIte]
  have hi1' : i 1 = i1 := by simp only [hid, one_ne_zero, ↓reduceIte]
  have hi0' : i 0 = i0 := by simp only [hid, ↓reduceIte]
  have hπa : AdaptedM S π := fun k => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hπd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 0))
      · rw [hπ1]; exact hp1
    · rw [hπk k hk]; exact hya k (Sum.inl (Sum.inr 0))
  have hxa : AdaptedM S x := fun k => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp only [hxd, zero_ne_one, ↓reduceIte]
        exact hya 0 (Sum.inl (Sum.inr 1))
      · rw [hx1']; exact hx1
    · rw [hxk k hk]; exact hya k (Sum.inl (Sum.inr 1))
  have hia : AdaptedM S i := fun k => by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [hi0']; exact hi0
      · rw [hi1']; exact hi1
    · rw [hik k hk]; exact hya k (Sum.inr ())
  have hπb : BndM S π := ⟨max My K, fun k => by
    rcases eq_or_ne k 1 with rfl | hk
    · rw [hπ1]; exact hK.mono fun ω h => h.1.trans (le_max_right _ _)
    · simp only [hπd, hk, ↓reduceIte]
      exact (hMy k).mono fun ω h => (h _).trans (le_max_left _ _)⟩
  have hxb : BndM S x := ⟨max My K, fun k => by
    rcases eq_or_ne k 1 with rfl | hk
    · rw [hx1']; exact hK.mono fun ω h => h.2.1.trans (le_max_right _ _)
    · simp only [hxd, hk, ↓reduceIte]
      exact (hMy k).mono fun ω h => (h _).trans (le_max_left _ _)⟩
  have hib : BndM S i := ⟨max My K, fun k => by
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hi0']; exact hK.mono fun ω h => h.2.2.2.trans (le_max_right _ _)
    rcases eq_or_ne k 1 with rfl | hk
    · rw [hi1']; exact hK.mono fun ω h => h.2.2.1.trans (le_max_right _ _)
    · simp only [hid, hk0, hk, ↓reduceIte]
      exact (hMy k).mono fun ω h => (h _).trans (le_max_left _ _)⟩
  have hπi : ∀ k, Integrable (π k) S.μ := fun k =>
    integrable_of_sm S (hπa k) (hπb.choose_spec k)
  have hxi : ∀ k, Integrable (x k) S.μ := fun k =>
    integrable_of_sm S (hxa k) (hxb.choose_spec k)
  have hii : ∀ k, Integrable (i k) S.μ := fun k =>
    integrable_of_sm S (hia k) (hib.choose_spec k)
  have hXi1 : ∀ k, 1 ≤ k → ∀ᵐ ω ∂S.μ,
      φ (k + 1) ω (Sum.inr 1) = -(c.li / c.σ) * (i k ω - c.istar) := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      filter_upwards [hMe] with ω e
      have := congrFun e 1
      rw [hi1']
      exact this
    · filter_upwards [hF k h2] with ω e
      rw [hik k h2]
      field_simp
      linear_combination e.2.2
  have hXi21 : ∀ᵐ ω ∂S.μ, Ξ2 1 ω = X2of c x1 i1 i0 ω := by
    filter_upwards [hMe] with ω e
    exact congrFun e 0
  have h4 : ∀ k, 1 ≤ k → ∀ᵐ ω ∂S.μ, c.lx * (x k ω - c.xstar) +
      -(c.li / c.σ) * (i k ω - c.istar) - c.β⁻¹ * (-(c.li / c.σ) * (i (k - 1) ω - c.istar)) -
        c.κ * Ξ2 k ω = 0 := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      filter_upwards [hXi21] with ω e
      rw [e, hx1', hi1', show 1 - 1 = 0 from rfl, hi0']
      simp only [X2of, X1of]
      field_simp
      ring
    · filter_upwards [hF k h2, hXi1 k (by omega), hXi1 (k - 1) (by omega)] with ω e e1 e2
      rw [show k - 1 + 1 = k by omega] at e2
      have e3 := e.2.1
      rw [e1, e2, ← hxk k h2] at e3
      simp only [hΞ2d]
      linear_combination e3
  have h15 : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, π k ω - 0 * π (k - 1) ω -
      c.β * 0 * S.E k (fun ω' => π (k + 1) ω' - 0 * π k ω') ω -
      c.β⁻¹ * c.σ * (-(c.li / c.σ) * (i (k - 1) ω - c.istar)) -
      c.β * 0 * S.E k (Ξ2 (k + 1)) ω + (1 + c.β * 0) * Ξ2 k ω - Ξ2 (k - 1) ω = 0 := by
    intro k hk
    filter_upwards [hF k hk, hXi1 (k - 1) (by omega)] with ω e eX
    rw [show k - 1 + 1 = k by omega] at eX
    have e1 := e.1
    rw [eX, ← hπk k hk] at e1
    have hΞk1 : Ξ2 (k - 1) ω = φ k ω (Sum.inr 0) := by
      simp only [hΞ2d, show k - 1 + 1 = k by omega]
    rw [hΞk1]
    simp only [hΞ2d]
    have hd : c.σ / c.β = c.β⁻¹ * c.σ := by rw [div_eq_inv_mul]
    rw [hd] at e1
    linear_combination e1
  have hAS : ∀ k, 2 ≤ k → ASm S c.β 0 c.κ u π x k := by
    intro k hk
    have eπ : (fun ω' => π (k + 1) ω' - 0 * π k ω') = π (k + 1) := by
      funext ω
      ring
    filter_upwards [hS k hk] with ω e
    have e1 := e.1
    rw [← hπk (k + 1) (by omega), ← hπk k hk, ← hxk k hk] at e1
    rw [eπ]
    simp only [cNK, Matrix.cons_val_zero] at e1
    linear_combination -e1
  have hIS : ∀ k, 2 ≤ k → ISm S c.σ rn π x i k := by
    intro k hk
    filter_upwards [hS k hk] with ω e
    have e1 := e.2
    rw [← hπk (k + 1) (by omega), ← hxk k hk, ← hxk (k + 1) (by omega), ← hik k hk] at e1
    simp only [cNK, Matrix.cons_val_one, Matrix.cons_val_zero] at e1
    linear_combination -e1
  refine ⟨π, x, i, hπa, hxa, hia, hπb, hxb, hib, hAS, hIS, fun t => ?_, hπ1, hx1', hi1', hi0'⟩
  refine eulerM_of_focs S hβ hκ hσ hli hπa hxa hia hπi hxi hii t
    (fun k hk1 _ => h4 k (by omega)) ?_
  have := h15 (t + 2) (by omega)
  rw [show t + 2 - 1 = t + 1 by omega, show t + 2 + 1 = t + 3 by omega] at this
  exact this

/-! ### Existence and uniqueness for every `λₓ ≥ 0` and `0 ≤ γ ≤ 1` -/

/-- **Woodford (2003), p. 593, on a filtered probability space: existence for `λₓ > 0` and every
`0 ≤ γ ≤ 1`.** -/
theorem rule_system_existsM (c : IRuleBasic.Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (S : MeasExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u)
    (hub : BndM S u) (hra : AdaptedM S rn) (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : HistoryM S p1 x1 i1 i0) : ∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i := by
  rcases hγ0.lt_or_eq with hγ | rfl
  · exact existsM_pos c hc hγ hγ1 S hua hub hra hrb hh
  · exact existsM_zero c hc S hua hub hra hrb hh

/-- **Woodford (2003), p. 593, on a filtered probability space: the rule system (3.16) is
determinate for `λₓ > 0` and every `0 ≤ γ ≤ 1`.** For every essentially bounded adapted
disturbance and every essentially bounded history known at the right dates, (2.6), (3.1),
(3.16) has an essentially bounded adapted solution with that history (Mathlib's conditional
expectation), and every such solution agrees with it a.s. at every date `≥ 1`. -/
theorem rule_system_existsUniqueM (c : IRuleBasic.Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (S : MeasExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u)
    (hub : BndM S u) (hra : AdaptedM S rn) (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : HistoryM S p1 x1 i1 i0) :
    ∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i ∧
      ∀ π' x' i', RuleSolM S c γ u rn p1 x1 i1 i0 π' x' i' →
        ∀ k, 1 ≤ k → π' k =ᵐ[S.μ] π k ∧ x' k =ᵐ[S.μ] x k ∧ i' k =ᵐ[S.μ] i k := by
  obtain ⟨π, x, i, hsol⟩ := rule_system_existsM c hc hγ0 hγ1 S hua hub hra hrb hh
  exact ⟨π, x, i, hsol, fun π' x' i' hsol' => TidyR5aLambdaXZeroMeasure.rule_system_uniqueM S c
    hc.1 hc.2.1 hc.2.2.2.1.ne' hc.2.2.1.ne' hc.2.2.2.2.2 hc.2.2.2.2.1.le hsol' hsol⟩

/-- **Woodford (2003), p. 593, on every filtered probability space: the rule system (3.16) is
determinate for every `λₓ ≥ 0` and every `0 ≤ γ ≤ 1`** (`0 < β < 1`, `σ, κ, λᵢ > 0`): existence and
a.s. uniqueness for every essentially bounded adapted disturbance and every essentially bounded
history known at the right dates (`λₓ = 0`:
`TidyR5aLambdaXZeroMeasure.rule_system_existsUniqueM_lx0`; `λₓ > 0`:
`rule_system_existsUniqueM`). -/
theorem rule_system_existsUniqueM_nonneg (c : IRuleBasic.Calib) (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hσ : 0 < c.σ) (hκ : 0 < c.κ) (hlx : 0 ≤ c.lx) (hli : 0 < c.li) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (S : MeasExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u)
    (hub : BndM S u) (hra : AdaptedM S rn) (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : HistoryM S p1 x1 i1 i0) :
    ∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i ∧
      ∀ π' x' i', RuleSolM S c γ u rn p1 x1 i1 i0 π' x' i' →
        ∀ k, 1 ≤ k → π' k =ᵐ[S.μ] π k ∧ x' k =ᵐ[S.μ] x k ∧ i' k =ᵐ[S.μ] i k := by
  rcases hlx.lt_or_eq with h | h
  · exact rule_system_existsUniqueM c ⟨hβ0, hβ1, hσ, hκ, h, hli⟩ hγ0 hγ1 S hua hub hra hrb hh
  · exact TidyR5aLambdaXZeroMeasure.rule_system_existsUniqueM_lx0 c h.symm hβ0 hβ1 hσ hκ hli hγ0
      hγ1 S hua hub hra hrb hh

/-- Woodford (2003), p. 593: a solution of the rule system on a probability space has an
essentially bounded history known at the right dates (the converse of `rule_system_existsM`). -/
theorem historyM_of_sol {S : MeasExpectationSystem Ω} {c : IRuleBasic.Calib} {γ : ℝ}
    {u rn : ℕ → Ω → ℝ} {p1 x1 i1 i0 : Ω → ℝ} {π x i : ℕ → Ω → ℝ}
    (h : RuleSolM S c γ u rn p1 x1 i1 i0 π x i) : HistoryM S p1 x1 i1 i0 := by
  obtain ⟨hπa, hxa, hia, ⟨Cπ, hCπ⟩, ⟨Cx, hCx⟩, ⟨Ci, hCi⟩, -, -, -, h1, h2, h3, h4⟩ := h
  subst h1 h2 h3 h4
  refine ⟨hπa 1, hxa 1, hia 1, hia 0, max (max Cπ Cx) Ci, ?_⟩
  filter_upwards [hCπ 1, hCx 1, hCi 1, hCi 0] with ω a b d e
  exact ⟨a.trans ((le_max_left _ _).trans (le_max_left _ _)),
    b.trans ((le_max_right _ _).trans (le_max_left _ _)), d.trans (le_max_right _ _),
    e.trans (le_max_right _ _)⟩

/-- **Woodford (2003), p. 593, on a filtered probability space, existence exactly characterised**
(`λₓ > 0`, `0 ≤ γ ≤ 1`): the rule system has an essentially bounded adapted solution with history
`(π₁, x₁, i₁, i₀)` iff that history is essentially bounded with `π₁, x₁, i₁` known at 1 and `i₀`
known at 0. -/
theorem rule_system_existsM_iff (c : IRuleBasic.Calib) (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (S : MeasExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u)
    (hub : BndM S u) (hra : AdaptedM S rn) (hrb : BndM S rn) (p1 x1 i1 i0 : Ω → ℝ) :
    (∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i) ↔ HistoryM S p1 x1 i1 i0 :=
  ⟨fun ⟨_, _, _, h⟩ => historyM_of_sol h,
    fun hh => rule_system_existsM c hc hγ0 hγ1 S hua hub hra hrb hh⟩

end Woodford.OptimalPolicyRules.TidyR6bRuleSystemMeasure
