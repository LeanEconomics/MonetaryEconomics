/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.CTRules

/-!
# Existence and uniqueness in the continuous-time policy-rules model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7.3–§5.7.5,
(5.105)–(5.113) after the `v = v*` elimination (p. 172), with short-term debt (Figs. 5.11–5.13,
Table 5.2, pp. 174–179).

After the elimination the debt dynamics are `dv/dt = (r − α)v + g` with
`g = i − (1 + θ_{sπ})π − θ_{sx}x − u_s`, `v₀ = 0` (instantaneous debt is not revalued), and the
transversality condition `e^{−rT}v_T → 0`.

## Main results

* `rules_unique_of_pi0`: for every `α`, two equilibria with the same `π₀` coincide.
* `α > 0` (the s-shaped surplus with `v*`, e.g. `α = 0.4` in Figs. 5.11–5.13):
  `rules_exists_pos` — for **every** `π₀` there is an equilibrium (the transversality condition
  never binds), so `π₀` is selected by the inflation-target innovation (5.111),
  `π₀ = −β_sε_s − β_iε_i` (`rules_exists_unique_beta`); `rules_v_bounded` (debt is bounded when
  `α > r`).
* `α ≤ 0` (including the `α = 0` rule of Fig. 5.11): the transversality condition pins `π₀`.
  `rules_valuation_nonpos`, `rules_pi0_nonpos` (`π₀ · Den = Rhs`, Laplace transforms at
  `r − α`), `rules_exists_nonpos` and `rules_unique_nonpos` (existence and uniqueness when
  `λ₁ ≠ r − α` and `Den ≠ 0`).
* The printed numbers as rational enclosures (by `norm_num`, `nlinarith`): `fig511_rate_path`
  (the rate path of Figs. 5.11–5.13 from (5.107), (5.112)), `integral_fig511i`, `fig511_lam`
  (`1.02531 < λ₁ < 1.0253125`), `fig511_pi0` (Fig. 5.11: the equilibrium exists, is unique and
  has `−0.8028 < π₀ < −0.8027`), `table52_pi0_bounds`, `rules_surplus_integrable` and
  `table52_betai` (Table 5.2 row 4 / Fig. 5.13: an `α = 0.4` equilibrium with a zero weighted
  sum of surpluses exists, and every one has `−0.5086 < β_i < −0.5085`, not the printed `−0.91`;
  survey E52).
-/

namespace Cochrane.StickyPriceFiscal.CTRulesEquilibrium

open Filter Topology MeasureTheory Cochrane.StickyPriceFiscal.CTSimple
  Cochrane.StickyPriceFiscal.CTRules

/-- Cochrane (2023), (5.106) with (5.108), p. 172: along a rules equilibrium the value of debt
obeys `dv/dt = (r − α)v + g`, `g = i − (1 + θ_{sπ})π − θ_{sx}x − u_s`. -/
theorem rules_deriv {r σ κ ρ θsπ θsx α : ℝ} {i us x π v s : ℝ → ℝ}
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s) (t : ℝ) (ht : 0 < t) :
    HasDerivAt v ((r - α) * v t + (i t - (1 + θsπ) * π t - θsx * x t - us t)) t :=
  (h.2.2.2.1 t ht).congr_deriv (by rw [h.2.1 t ht.le]; ring)

/-- Cochrane (2023), §5.7.3, p. 172: the forcing `g = i − (1 + θ_{sπ})π − θ_{sx}x − u_s` of the
debt equation is continuous and bounded on `[0, ∞)`. -/
theorem forcing_bdd {θsπ θsx M Mu Kx Kπ : ℝ} {i us x π : ℝ → ℝ}
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hu : ContinuousOn us (Set.Ici 0)) (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu)
    (hx : ContinuousOn x (Set.Ici 0)) (hπ : ContinuousOn π (Set.Ici 0))
    (hKx : ∀ t, 0 ≤ t → |x t| ≤ Kx) (hKπ : ∀ t, 0 ≤ t → |π t| ≤ Kπ) :
    ContinuousOn (fun t => i t - (1 + θsπ) * π t - θsx * x t - us t) (Set.Ici 0) ∧
      ∀ t, 0 ≤ t → |i t - (1 + θsπ) * π t - θsx * x t - us t| ≤
        M + |1 + θsπ| * Kπ + |θsx| * Kx + Mu := by
  refine ⟨((hi.sub (continuousOn_const.mul hπ)).sub (continuousOn_const.mul hx)).sub hu,
    fun t ht => ?_⟩
  calc |i t - (1 + θsπ) * π t - θsx * x t - us t|
      ≤ |i t| + |(1 + θsπ) * π t| + |θsx * x t| + |us t| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ M + |1 + θsπ| * Kπ + |θsx| * Kx + Mu := by
        rw [abs_mul, abs_mul]
        exact add_le_add (add_le_add (add_le_add (hM t ht)
          (mul_le_mul_of_nonneg_left (hKπ t ht) (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left (hKx t ht) (abs_nonneg _))) (hMu t ht)

/-- Cochrane (2023), §5.7.5 (infrastructure): if `r > 0` and `r + b > 0`, the backward integral
of a bounded continuous forcing satisfies `e^{−rT} ∫_0^T e^{−bτ} z_{T−τ} dτ → 0` (even when
`b < 0` and the integral grows). -/
theorem bwdInt_tvc {r b M : ℝ} {z : ℝ → ℝ} (hr : 0 < r) (hrb : 0 < r + b)
    (hM : ∀ s, |z s| ≤ M) :
    Tendsto (fun T => Real.exp (-(r * T)) * bwdInt b z T) atTop (𝓝 0) := by
  set m := max (-b) 0 with hm
  set c := r - m with hcdef
  have hc : 0 < c := by
    rcases le_total (-b) 0 with h | h
    · rw [hcdef, hm, max_eq_right h]; linarith
    · rw [hcdef, hm, max_eq_left h]; linarith
  have hbm : -b ≤ m := le_max_left _ _
  have hm0 : 0 ≤ m := le_max_right _ _
  have hbound : ∀ T, 0 ≤ T →
      |Real.exp (-(r * T)) * bwdInt b z T| ≤ M * (T * Real.exp (-(c * T))) := by
    intro T hT
    have h1 : ‖bwdInt b z T‖ ≤ Real.exp (m * T) * M * |T - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => by
        rw [Set.uIoc_of_le hT] at hτ
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        refine mul_le_mul (Real.exp_le_exp.2 ?_) (hM _) (abs_nonneg _) (Real.exp_pos _).le
        nlinarith [hτ.1, hτ.2]
    rw [sub_zero, abs_of_nonneg hT, Real.norm_eq_abs] at h1
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(c * T)) = Real.exp (-(r * T)) * Real.exp (m * T) := by
      rw [← Real.exp_add, hcdef]; ring_nf
    calc Real.exp (-(r * T)) * |bwdInt b z T|
        ≤ Real.exp (-(r * T)) * (Real.exp (m * T) * M * T) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = M * (T * Real.exp (-(c * T))) := by rw [he]; ring
  have hlim : Tendsto (fun T => M * (T * Real.exp (-(c * T)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hc)
    have h2 := h.const_mul (M / c)
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    simp only [Function.comp_apply, id, pow_one]
    field_simp
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [Real.norm_eq_abs]
  exact hbound T hT

/-- Cochrane (2023), p. 177 ("the interest-rate path sets the family of solutions"): **for every
`α`, an equilibrium is determined by `π₀`**: two rules equilibria with the same rules, rate path
and `π₀` coincide on `[0, ∞)` (output, inflation, debt and surpluses). -/
theorem rules_unique_of_pi0 {r σ κ ρ θsπ θsx α M : ℝ} {i us x π v s x' π' v' s' : ℝ → ℝ}
    (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s)
    (h' : IsRulesEq r σ κ ρ θsπ θsx α i us x' π' v' s') (h0 : π 0 = π' 0) :
    ∀ t, 0 ≤ t → x t = x' t ∧ π t = π' t ∧ v t = v' t ∧ s t = s' t := by
  have hp := ct_family_pinned_by_pi0 hκ hσ hi hM h.1 h'.1 h0
  have hw := decay_unique (b := α - r) (w := fun u => v u - v' u) (h.2.2.1.sub h'.2.2.1)
    (fun τ hτ => ((rules_deriv h τ hτ).sub (rules_deriv h' τ hτ)).congr_deriv (by
      rw [(hp τ hτ.le).1, (hp τ hτ.le).2]; ring))
  intro t ht
  have hv : v t = v' t := by
    have := hw t ht
    simp only [h.2.2.2.2.1, h'.2.2.2.2.1, sub_self, mul_zero] at this
    linarith
  refine ⟨(hp t ht).2, (hp t ht).1, hv, ?_⟩
  rw [h.2.1 t ht, h'.2.1 t ht, (hp t ht).1, (hp t ht).2, hv]

/-- Cochrane (2023), §5.7.3–§5.7.5, pp. 172–177: **existence for `α > 0`.** With a surplus rule
that responds to debt (`α > 0`, `r > 0`), for every initial inflation `π₀` there is a rules
equilibrium: the debt equation is solved backward from `v₀ = 0`, and the transversality condition
holds automatically. The valuation equation does not select `π₀`; the inflation-target innovation
(5.111) does. -/
theorem rules_exists_pos {r σ κ ρ θsπ θsx α M Mu : ℝ} {i us : ℝ → ℝ} (hr : 0 < r)
    (hα : 0 < α) (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0))
    (hM : ∀ t, 0 ≤ t → |i t| ≤ M) (hu : ContinuousOn us (Set.Ici 0))
    (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu) (π0 : ℝ) :
    ∃ x π v s : ℝ → ℝ, IsRulesEq r σ κ ρ θsπ θsx α i us x π v s ∧ π 0 = π0 := by
  obtain ⟨x, π, hsol, hπ0⟩ := ct_family_exists (ρ := ρ) hκ hσ hi hM π0
  obtain ⟨Kx, hKx⟩ := hsol.2.1
  obtain ⟨Kπ, hKπ⟩ := hsol.2.2
  obtain ⟨hgc, hgb⟩ := forcing_bdd (θsπ := θsπ) (θsx := θsx) hi hM hu hMu hsol.1.1 hsol.1.2.1
    hKx hKπ
  have hge := ext0_continuous hgc
  have hgeb := ext0_abs_le hgb
  refine ⟨x, π, bwdInt (α - r) (ext0 fun t => i t - (1 + θsπ) * π t - θsx * x t - us t),
    fun t => θsπ * π t + θsx * x t +
      α * bwdInt (α - r) (ext0 fun t => i t - (1 + θsπ) * π t - θsx * x t - us t) t + us t,
    ⟨hsol, fun t _ => rfl, (bwdInt_continuous hge).continuousOn,
      fun t ht => (bwdInt_hasDerivAt hge t).congr_deriv ?_, bwdInt_zero _ _,
      bwdInt_tvc hr (by linarith) hgeb⟩, hπ0⟩
  rw [ext0_eq ht.le]
  ring

/-- Cochrane (2023), (5.111) and p. 172: **existence and uniqueness for `α > 0`**: with
`π₀ = −β_sε_s − β_iε_i` (the inflation-target innovation (5.111), which equals inflation after
the elimination, `ct_elim_pi0`), there is exactly one rules equilibrium. -/
theorem rules_exists_unique_beta {r σ κ ρ θsπ θsx α M Mu βs βi es ei : ℝ} {i us : ℝ → ℝ}
    (hr : 0 < r) (hα : 0 < α) (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0))
    (hM : ∀ t, 0 ≤ t → |i t| ≤ M) (hu : ContinuousOn us (Set.Ici 0))
    (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu) :
    (∃ x π v s : ℝ → ℝ, IsRulesEq r σ κ ρ θsπ θsx α i us x π v s ∧
        π 0 = -βs * es - βi * ei) ∧
      ∀ x π v s x' π' v' s' : ℝ → ℝ, IsRulesEq r σ κ ρ θsπ θsx α i us x π v s →
        π 0 = -βs * es - βi * ei → IsRulesEq r σ κ ρ θsπ θsx α i us x' π' v' s' →
          π' 0 = -βs * es - βi * ei →
            ∀ t, 0 ≤ t → x t = x' t ∧ π t = π' t ∧ v t = v' t ∧ s t = s' t :=
  ⟨rules_exists_pos hr hα hκ hσ hi hM hu hMu _, fun _ _ _ _ _ _ _ _ h h0 h' h0' =>
    rules_unique_of_pi0 hκ hσ hi hM h h' (h0.trans h0'.symm)⟩

/-- Cochrane (2023), §5.7.5, p. 177: **with `α > r` the value of debt is bounded** in every
rules equilibrium ("as debt builds up, surpluses stay persistently larger to pay off the larger
debt"). -/
theorem rules_v_bounded {r σ κ ρ θsπ θsx α M Mu : ℝ} {i us x π v s : ℝ → ℝ} (hαr : r < α)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hu : ContinuousOn us (Set.Ici 0)) (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu)
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s) : ∃ K, ∀ t, 0 ≤ t → |v t| ≤ K := by
  obtain ⟨Kx, hKx⟩ := h.1.2.1
  obtain ⟨Kπ, hKπ⟩ := h.1.2.2
  obtain ⟨hgc, hgb⟩ := forcing_bdd (θsπ := θsπ) (θsx := θsx) hi hM hu hMu h.1.1.1 h.1.1.2.1
    hKx hKπ
  have hv := (ode_backward (b := α - r) (y := v) (ext0_continuous hgc)).1
    ⟨h.2.2.1, fun τ hτ => (rules_deriv h τ hτ).congr_deriv (by rw [ext0_eq hτ.le]; ring)⟩
  refine ⟨(M + |1 + θsπ| * Kπ + |θsx| * Kx + Mu) / (α - r), fun t ht => ?_⟩
  rw [hv t ht, h.2.2.2.2.1, mul_zero, zero_add]
  exact bwdInt_abs_le (by linarith) ht fun s _ _ => ext0_abs_le hgb s

/-! ## `α ≤ 0`: the transversality condition pins `π₀` -/

/-- Cochrane (2023), A1 §1.13, p. 582 ("with `α = 0` we must find `dδ_π` to match the initial
value of debt"): the denominator `Den = θ_{sx}(λ₁ − a)(a + λ₂) + (κ(1 + θ_{sπ}) − θ_{sx}(a − ρ))
(λ₁ − a)` of the `π₀` formula at Laplace rate `a = r − α`. -/
noncomputable def pi0Den (a ρ κ σ θsπ θsx : ℝ) : ℝ :=
  θsx * ((lam1 ρ κ σ - a) * (a + lam2 ρ κ σ)) +
    (κ * (1 + θsπ) - θsx * (a - ρ)) * (lam1 ρ κ σ - a)

/-- Cochrane (2023), §5.7.5: the right side
`Rhs = κ(I − U)(λ₁ − a)(a + λ₂) − (κ(1 + θ_{sπ}) − θ_{sx}(a − ρ))κσ(I − J)` of the `π₀`
formula. -/
noncomputable def pi0Rhs (a ρ κ σ θsπ θsx I J U : ℝ) : ℝ :=
  κ * (I - U) * ((lam1 ρ κ σ - a) * (a + lam2 ρ κ σ)) -
    (κ * (1 + θsπ) - θsx * (a - ρ)) * (κ * σ) * (I - J)

/-- Cochrane (2023), §5.7.5 (algebra): given the Laplace relations `κX = π₀ − (a − ρ)P` and
`(λ₁ − a)(a + λ₂)P = κσ(I − J) + (λ₁ − a)π₀`,
`π₀·Den − Rhs = (λ₁ − a)(a + λ₂)κ((1 + θ_{sπ})P + θ_{sx}X + U − I)`. -/
theorem pi0_algebra {a ρ κ σ θsπ θsx P X I J U π0 : ℝ} (hX : κ * X = π0 - (a - ρ) * P)
    (hP : (lam1 ρ κ σ - a) * (a + lam2 ρ κ σ) * P = κ * σ * (I - J) + (lam1 ρ κ σ - a) * π0) :
    π0 * pi0Den a ρ κ σ θsπ θsx - pi0Rhs a ρ κ σ θsπ θsx I J U =
      (lam1 ρ κ σ - a) * (a + lam2 ρ κ σ) * κ * ((1 + θsπ) * P + θsx * X + U - I) := by
  unfold pi0Den pi0Rhs
  linear_combination (-(κ * (1 + θsπ) - θsx * (a - ρ))) * hP +
    (-(θsx * ((lam1 ρ κ σ - a) * (a + lam2 ρ κ σ)))) * hX

/-- Cochrane (2023), §5.7.5: the discounted forcing splits as
`∫_0^∞ e^{−aτ}(−g_τ) dτ = (1 + θ_{sπ})P + θ_{sx}X + U − I` (all transforms at rate `a > 0`). -/
theorem rules_split {a θsπ θsx M Mu Kx Kπ : ℝ} {i us x π : ℝ → ℝ} (ha : 0 < a)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hu : ContinuousOn us (Set.Ici 0)) (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu)
    (hx : ContinuousOn x (Set.Ici 0)) (hπ : ContinuousOn π (Set.Ici 0))
    (hKx : ∀ t, 0 ≤ t → |x t| ≤ Kx) (hKπ : ∀ t, 0 ≤ t → |π t| ≤ Kπ) :
    ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) *
        -(i τ - (1 + θsπ) * π τ - θsx * x τ - us τ) =
      (1 + θsπ) * (∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * π τ) +
        θsx * (∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * x τ) +
          (∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * us τ) -
            ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * i τ := by
  have IP := integrableOn_of_contOn_bdd ha le_rfl hπ hKπ
  have IX := integrableOn_of_contOn_bdd ha le_rfl hx hKx
  have II := integrableOn_of_contOn_bdd ha le_rfl hi hM
  have IU := integrableOn_of_contOn_bdd ha le_rfl hu hMu
  have J1 : IntegrableOn (fun τ => (1 + θsπ) * (Real.exp (-(a * τ)) * π τ)) (Set.Ioi 0) :=
    IP.const_mul _
  have J2 : IntegrableOn (fun τ => θsx * (Real.exp (-(a * τ)) * x τ)) (Set.Ioi 0) :=
    IX.const_mul _
  have J12 : IntegrableOn (fun τ => (1 + θsπ) * (Real.exp (-(a * τ)) * π τ) +
      θsx * (Real.exp (-(a * τ)) * x τ)) (Set.Ioi 0) := J1.add J2
  have J123 : IntegrableOn (fun τ => (1 + θsπ) * (Real.exp (-(a * τ)) * π τ) +
      θsx * (Real.exp (-(a * τ)) * x τ) + Real.exp (-(a * τ)) * us τ) (Set.Ioi 0) := J12.add IU
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add J1 J2,
    ← integral_add J12 IU, ← integral_sub J123 II]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), §5.7.5 and A1 p. 582: **with `α ≤ 0` the valuation equation binds**: in any
rules equilibrium, with `a = r − α ≥ r > 0`,
`(1 + θ_{sπ})P + θ_{sx}X + U − I = 0` for the transforms at rate `a`. -/
theorem rules_valuation_nonpos {r σ κ ρ θsπ θsx α M Mu : ℝ} {i us x π v s : ℝ → ℝ}
    (hr : 0 < r) (hα : α ≤ 0) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hu : ContinuousOn us (Set.Ici 0)) (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu)
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s) :
    (1 + θsπ) * (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * π τ) +
        θsx * (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * x τ) +
          (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * us τ) -
            ∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * i τ = 0 := by
  have ha : 0 < r - α := by linarith
  obtain ⟨Kx, hKx⟩ := h.1.2.1
  obtain ⟨Kπ, hKπ⟩ := h.1.2.2
  obtain ⟨hgc, hgb⟩ := forcing_bdd (θsπ := θsπ) (θsx := θsx) hi hM hu hMu h.1.1.1 h.1.1.2.1
    hKx hKπ
  -- the transversality condition at rate `r − α`
  have htvc : Tendsto (fun T => Real.exp (-((r - α) * T)) * v T) atTop (𝓝 0) := by
    have hn := h.2.2.2.2.2.norm
    rw [norm_zero] at hn
    refine squeeze_zero_norm' ?_ hn
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) (abs_nonneg _)
  have hint := integrableOn_of_contOn_bdd (a := r - α)
    (g := fun τ => -(i τ - (1 + θsπ) * π τ - θsx * x τ - us τ)) ha le_rfl hgc.neg
    fun t ht => by rw [abs_neg]; exact hgb t ht
  have hv := (tvc_iff_forward (f := fun τ => -(i τ - (1 + θsπ) * π τ - θsx * x τ - us τ))
    (h.2.2.1.mono (Set.Ici_subset_Ici.2 le_rfl))
    (fun τ hτ => (rules_deriv h τ hτ).congr_deriv (by ring)) hint).1 htvc
  simp only [zero_add, h.2.2.2.2.1] at hv
  rw [← rules_split ha hi hM hu hMu h.1.1.1 h.1.1.2.1 hKx hKπ, ← hv]

/-- Cochrane (2023), §5.7.5, Fig. 5.11: **the `π₀` formula for `α ≤ 0`**: in any rules
equilibrium, `π₀ · Den = Rhs` with the Laplace transforms `I, U` at `a = r − α` and
`J = ∫ e^{−λ₁τ} i`. -/
theorem rules_pi0_nonpos {r σ κ ρ θsπ θsx α M Mu : ℝ} {i us x π v s : ℝ → ℝ} (hr : 0 < r)
    (hα : α ≤ 0) (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0))
    (hM : ∀ t, 0 ≤ t → |i t| ≤ M) (hu : ContinuousOn us (Set.Ici 0))
    (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu) (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s) :
    π 0 * pi0Den (r - α) ρ κ σ θsπ θsx =
      pi0Rhs (r - α) ρ κ σ θsπ θsx (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * i τ)
        (∫ τ in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * τ)) * i τ)
        (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * us τ) := by
  obtain ⟨hX, hP⟩ := laplace_P (r := r - α) (by linarith) hκ hσ hi hM h.1
  have hV := rules_valuation_nonpos hr hα hi hM hu hMu h
  have := pi0_algebra (θsπ := θsπ) (θsx := θsx)
    (U := ∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * us τ) hX hP
  rw [hV, mul_zero] at this
  linarith

/-- Cochrane (2023), §5.7.5 and A1 p. 582: **uniqueness for `α ≤ 0`**: if `Den ≠ 0`, every rules
equilibrium has `π₀ = Rhs/Den`, and any two rules equilibria coincide on `[0, ∞)`. -/
theorem rules_unique_nonpos {r σ κ ρ θsπ θsx α M Mu : ℝ} {i us x π v s x' π' v' s' : ℝ → ℝ}
    (hr : 0 < r) (hα : α ≤ 0) (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0))
    (hM : ∀ t, 0 ≤ t → |i t| ≤ M) (hu : ContinuousOn us (Set.Ici 0))
    (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu) (hden : pi0Den (r - α) ρ κ σ θsπ θsx ≠ 0)
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s)
    (h' : IsRulesEq r σ κ ρ θsπ θsx α i us x' π' v' s') :
    π 0 = pi0Rhs (r - α) ρ κ σ θsπ θsx (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * i τ)
        (∫ τ in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * τ)) * i τ)
        (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * us τ) / pi0Den (r - α) ρ κ σ θsπ θsx ∧
      ∀ t, 0 ≤ t → x t = x' t ∧ π t = π' t ∧ v t = v' t ∧ s t = s' t := by
  have e := rules_pi0_nonpos hr hα hκ hσ hi hM hu hMu h
  have e' := rules_pi0_nonpos hr hα hκ hσ hi hM hu hMu h'
  refine ⟨by rw [eq_div_iff hden]; exact e, rules_unique_of_pi0 hκ hσ hi hM h h' ?_⟩
  exact mul_right_cancel₀ hden (e.trans e'.symm)

/-- Cochrane (2023), §5.7.5, Fig. 5.11 and A1 p. 582: **existence for `α ≤ 0`**: if
`λ₁ ≠ r − α` and `Den ≠ 0`, the path in the family with `π₀ = Rhs/Den`, with debt
`v = −∫_0^∞ e^{−(r−α)τ} g_{t+τ} dτ`, is a rules equilibrium. -/
theorem rules_exists_nonpos {r σ κ ρ θsπ θsx α M Mu : ℝ} {i us : ℝ → ℝ} (hr : 0 < r)
    (hα : α ≤ 0) (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0))
    (hM : ∀ t, 0 ≤ t → |i t| ≤ M) (hu : ContinuousOn us (Set.Ici 0))
    (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu) (hne : lam1 ρ κ σ ≠ r - α)
    (hden : pi0Den (r - α) ρ κ σ θsπ θsx ≠ 0) :
    ∃ x π v s : ℝ → ℝ, IsRulesEq r σ κ ρ θsπ θsx α i us x π v s ∧
      π 0 = pi0Rhs (r - α) ρ κ σ θsπ θsx (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * i τ)
        (∫ τ in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * τ)) * i τ)
        (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * us τ) / pi0Den (r - α) ρ κ σ θsπ θsx := by
  have ha : 0 < r - α := by linarith
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set π0 := pi0Rhs (r - α) ρ κ σ θsπ θsx (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * i τ)
    (∫ τ in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * τ)) * i τ)
    (∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * us τ) / pi0Den (r - α) ρ κ σ θsπ θsx
  obtain ⟨x, π, hsol, hπ0⟩ := ct_family_exists (ρ := ρ) hκ hσ hi hM π0
  obtain ⟨Kx, hKx⟩ := hsol.2.1
  obtain ⟨Kπ, hKπ⟩ := hsol.2.2
  obtain ⟨hgc, hgb⟩ := forcing_bdd (θsπ := θsπ) (θsx := θsx) hi hM hu hMu hsol.1.1 hsol.1.2.1
    hKx hKπ
  have hge := ext0_continuous hgc
  have hgeb := ext0_abs_le hgb
  -- the valuation equation holds at this `π₀`
  obtain ⟨hX, hP⟩ := laplace_P (r := r - α) ha hκ hσ hi hM hsol
  have halg := pi0_algebra (θsπ := θsπ) (θsx := θsx)
    (U := ∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) * us τ) hX hP
  have hD : (lam1 ρ κ σ - (r - α)) * (r - α + lam2 ρ κ σ) * κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hne) (by linarith)) hκ.ne'
  rw [hπ0, div_mul_cancel₀ _ hden, sub_self] at halg
  have hV := (mul_eq_zero.1 halg.symm).resolve_left hD
  refine ⟨x, π, fun t => -fwdInt (r - α) (ext0 fun t =>
      i t - (1 + θsπ) * π t - θsx * x t - us t) t,
    fun t => θsπ * π t + θsx * x t + α * -fwdInt (r - α) (ext0 fun t =>
      i t - (1 + θsπ) * π t - θsx * x t - us t) t + us t,
    ⟨hsol, fun t _ => rfl, (fwdInt_continuous ha hge hgeb).neg.continuousOn,
      fun t ht => (fwdInt_hasDerivAt ha hge hgeb t).neg.congr_deriv ?_, ?_,
      tvc_of_bounded (t := 0) (K := (M + |1 + θsπ| * Kπ + |θsx| * Kx + Mu) / (r - α)) hr
        fun T _ => ?_⟩, hπ0⟩
  · rw [ext0_eq ht.le]
    ring
  · have e : fwdInt (r - α) (ext0 fun t => i t - (1 + θsπ) * π t - θsx * x t - us t) 0 =
        -∫ τ in Set.Ioi 0, Real.exp (-((r - α) * τ)) *
          -(i τ - (1 + θsπ) * π τ - θsx * x τ - us τ) := by
      rw [fwdInt, ← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : (0 : ℝ) < τ) => ?_
      simp only [zero_add, ext0_eq hτ.le]
      ring
    beta_reduce
    rw [e, rules_split ha hi hM hu hMu hsol.1.1 hsol.1.2.1 hKx hKπ, hV, neg_zero, neg_zero]
  · rw [abs_neg]
    exact fwdInt_abs_le ha fun u _ => hgeb u

/-! ## The printed numbers of Figs. 5.11–5.13 and Table 5.2, as rational enclosures -/

/-- Cochrane (2023), Figs. 5.11–5.13, pp. 175–179: the interest-rate path after a unit monetary
shock with `ζ_i = 1`, `η_i = 0.3`, `θ_{iε} = 0.25`, `θ_{iπ} = θ_{ix} = 0`:
`i_t = −(33/28)e^{−t} + (10/7)e^{−0.3t}`. -/
noncomputable def fig511i (t : ℝ) : ℝ :=
  -(33 / 28) * Real.exp (-(1 * t)) + 10 / 7 * Real.exp (-(3 / 10 * t))

/-- Cochrane (2023), (5.107), (5.112), p. 175: **the interest-rate path of Figs. 5.11–5.13.** With
`u_i = e^{−0.3t}` (the shock `dε_i = 1` at `0`), `di/dt = −ζ_i(i − u_i)` with `ζ_i = 1` on
`(0, ∞)` and `i₀ = θ_{iε} = 1/4`, the unique solution is `fig511i`; and `fig511i` solves it. -/
theorem fig511_rate_path :
    (fig511i 0 = 1 / 4 ∧ ∀ t, HasDerivAt fig511i
      (-(fig511i t - Real.exp (-(3 / 10 * t)))) t) ∧
      ∀ j : ℝ → ℝ, ContinuousOn j (Set.Ici 0) →
        (∀ t, 0 < t → HasDerivAt j (-(j t - Real.exp (-(3 / 10 * t)))) t) → j 0 = 1 / 4 →
          ∀ t, 0 ≤ t → j t = fig511i t := by
  have hd : ∀ t, HasDerivAt fig511i (-(fig511i t - Real.exp (-(3 / 10 * t)))) t := fun t =>
    (((hasDerivAt_expNeg 1 t).const_mul (-(33 / 28))).add
      ((hasDerivAt_expNeg (3 / 10) t).const_mul (10 / 7))).congr_deriv (by
        simp only [fig511i]; ring)
  have h0 : fig511i 0 = 1 / 4 := by simp [fig511i]; norm_num
  refine ⟨⟨h0, hd⟩, fun j hc hj hj0 t ht => ?_⟩
  have hfc : Continuous fig511i := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hw := decay_unique (b := 1) (w := fun u => j u - fig511i u) (hc.sub hfc.continuousOn)
    (fun τ hτ => ((hj τ hτ).sub (hd τ)).congr_deriv (by ring)) t ht
  rw [hj0, h0, sub_self, mul_zero] at hw
  linarith

/-- Cochrane (2023), Figs. 5.11–5.13: `fig511i` is continuous and `|i_t| ≤ 33/28 + 10/7` on
`[0, ∞)`. -/
theorem fig511i_bdd : ContinuousOn fig511i (Set.Ici 0) ∧
    ∀ t, 0 ≤ t → |fig511i t| ≤ 33 / 28 + 10 / 7 := by
  refine ⟨(by unfold fig511i; fun_prop : Continuous fig511i).continuousOn, fun t ht => ?_⟩
  have e1 : Real.exp (-(1 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have e2 : Real.exp (-(3 / 10 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have p1 := Real.exp_pos (-(1 * t))
  have p2 := Real.exp_pos (-(3 / 10 * t))
  unfold fig511i
  rw [abs_le]
  constructor <;> nlinarith

/-- Cochrane (2023), Table 5.2: the Laplace transform of the rate path,
`∫_0^∞ e^{−aτ} i_τ dτ = −(33/28)/(a + 1) + (10/7)/(a + 3/10)` for `a > 0`. -/
theorem integral_fig511i {a : ℝ} (ha : 0 < a) :
    ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * fig511i τ =
      -(33 / 28) / (a + 1) + 10 / 7 / (a + 3 / 10) := by
  have he : (fun τ => Real.exp (-(a * τ)) * fig511i τ) = fun τ =>
      -(33 / 28) * Real.exp (-((a + 1) * τ)) + 10 / 7 * Real.exp (-((a + 3 / 10) * τ)) := by
    funext τ
    have e1 : Real.exp (-((a + 1) * τ)) = Real.exp (-(a * τ)) * Real.exp (-(1 * τ)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-((a + 3 / 10) * τ)) =
        Real.exp (-(a * τ)) * Real.exp (-(3 / 10 * τ)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2, fig511i]
    ring
  have i1 : IntegrableOn (fun τ => -(33 / 28) * Real.exp (-((a + 1) * τ))) (Set.Ioi 0) :=
    (integrableOn_exp_Ioi (by linarith)).const_mul _
  have i2 : IntegrableOn (fun τ => 10 / 7 * Real.exp (-((a + 3 / 10) * τ))) (Set.Ioi 0) :=
    (integrableOn_exp_Ioi (by linarith)).const_mul _
  rw [he, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_exp_Ioi (by linarith), integral_exp_Ioi (by linarith)]
  ring

/-- Cochrane (2023), Figs. 5.11–5.13 (`ρ = 0.05`, `κ = 2`, `σ = 0.5`): `λ₁` satisfies
`λ₁² = λ₁/20 + 1`, `λ₂ = λ₁ − 1/20`, and `1.02531 < λ₁ < 1.0253125`. -/
theorem fig511_lam :
    lam1 (1 / 20) 2 (1 / 2) ^ 2 = 1 / 20 * lam1 (1 / 20) 2 (1 / 2) + 1 ∧
      lam2 (1 / 20) 2 (1 / 2) = lam1 (1 / 20) 2 (1 / 2) - 1 / 20 ∧
        102531 / 100000 < lam1 (1 / 20) 2 (1 / 2) ∧
          lam1 (1 / 20) 2 (1 / 2) < 10253125 / 10000000 := by
  have h1 := lam1_root (ρ := 1 / 20) (κ := 2) (σ := 1 / 2) (by norm_num) (by norm_num)
  have h2 := lam_sub (1 / 20) 2 (1 / 2)
  have hs1 : (200062 / 100000 : ℝ) < Real.sqrt ((1 / 20) ^ 2 + 4 * 2 * (1 / 2)) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt ((1 / 20) ^ 2 + 4 * 2 * (1 / 2)) < (2000625 / 1000000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨by rw [h1]; ring, by linarith, ?_, ?_⟩ <;> unfold lam1 <;> linarith

/-- Cochrane (2023), Fig. 5.11 and Table 5.2 row 1, p. 175: **`π₀ ≈ −0.803`, machine-checked.**
With `r = ρ = 0.05`, `κ = 2`, `σ = 0.5`, the surplus rule `s̃ = x + π` (`α = 0`, `u_s = 0`),
short-term debt and the Fig. 5.11 rate path, a rules equilibrium exists (it is unique by
`rules_unique_nonpos`), and every equilibrium has `−0.8028 < π₀ < −0.8027`. -/
theorem fig511_pi0 :
    (∃ x π v s : ℝ → ℝ, IsRulesEq (1 / 20) (1 / 2) 2 (1 / 20) 1 1 0 fig511i (fun _ => 0)
      x π v s) ∧
      ∀ x π v s : ℝ → ℝ, IsRulesEq (1 / 20) (1 / 2) 2 (1 / 20) 1 1 0 fig511i (fun _ => 0)
        x π v s → -(8028 / 10000) < π 0 ∧ π 0 < -(8027 / 10000) := by
  obtain ⟨hL2, hlam2, hl, hu⟩ := fig511_lam
  obtain ⟨hic, hib⟩ := fig511i_bdd
  set L := lam1 (1 / 20) 2 (1 / 2) with hLdef
  have hI : ∫ τ in Set.Ioi 0, Real.exp (-((1 / 20 - 0) * τ)) * fig511i τ = 145 / 49 := by
    rw [integral_fig511i (by norm_num)]
    norm_num
  have hJ := integral_fig511i (a := L) (by linarith)
  have hden : pi0Den (1 / 20 - 0) (1 / 20) 2 (1 / 2) 1 1 = 4 * L + 4 / 5 := by
    unfold pi0Den
    rw [hlam2]
    linear_combination hL2
  have hpos : (0 : ℝ) < 4 * L + 4 / 5 := by linarith
  have hval : pi0Rhs (1 / 20 - 0) (1 / 20) 2 (1 / 2) 1 1
      (∫ τ in Set.Ioi 0, Real.exp (-((1 / 20 - 0) * τ)) * fig511i τ)
      (∫ τ in Set.Ioi 0, Real.exp (-(L * τ)) * fig511i τ) 0 =
      4 * (-(33 / 28) / (L + 1) + 10 / 7 / (L + 3 / 10)) - 2 * (145 / 49) := by
    unfold pi0Rhs
    rw [hI, hJ, hlam2]
    have : (L - (1 / 20 - 0)) * (1 / 20 - 0 + (L - 1 / 20)) = 1 := by
      linear_combination hL2
    rw [this]
    ring
  have hden' : pi0Den (1 / 20 - 0) (1 / 20) 2 (1 / 2) 1 1 ≠ 0 := by rw [hden]; exact hpos.ne'
  have hne : L ≠ 1 / 20 - 0 := by intro h; rw [h] at hl; norm_num at hl
  refine ⟨?_, fun x π v s h => ?_⟩
  · obtain ⟨x, π, v, s, h, -⟩ := rules_exists_nonpos (r := 1 / 20) (σ := 1 / 2) (κ := 2)
      (ρ := 1 / 20) (θsπ := 1) (θsx := 1) (α := 0) (i := fig511i) (us := fun _ => 0)
      (M := 33 / 28 + 10 / 7) (Mu := 0)
      (by norm_num) le_rfl (by norm_num) (by norm_num) hic hib continuousOn_const
      (fun _ _ => by simp) hne hden'
    exact ⟨x, π, v, s, h⟩
  · have e := (rules_unique_nonpos (M := 33 / 28 + 10 / 7) (Mu := 0) (by norm_num) le_rfl
      (by norm_num) (by norm_num) hic hib continuousOn_const (fun _ _ => by simp) hden' h h).1
    simp only [mul_zero, integral_zero] at e
    rw [← hLdef] at e
    rw [e, hval, hden]
    have hq : 0 < (L + 1) * (L + 3 / 10) := by nlinarith
    have hL3 : L ^ 3 = 1 / 20 * L ^ 2 + L := by linear_combination L * hL2
    constructor
    · rw [lt_div_iff₀ hpos]
      have key : -(8028 / 10000) * (4 * L + 4 / 5) * ((L + 1) * (L + 3 / 10)) <
          (4 * (-(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1)) -
            2 * (145 / 49) * ((L + 1) * (L + 3 / 10))) := by
        nlinarith [hL2, hL3]
      have hJq : (4 * (-(33 / 28) / (L + 1) + 10 / 7 / (L + 3 / 10)) - 2 * (145 / 49)) *
          ((L + 1) * (L + 3 / 10)) = 4 * (-(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1)) -
            2 * (145 / 49) * ((L + 1) * (L + 3 / 10)) := by
        field_simp
      rw [← hJq] at key
      exact lt_of_mul_lt_mul_right key hq.le
    · rw [div_lt_iff₀ hpos]
      have key : (4 * (-(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1)) -
            2 * (145 / 49) * ((L + 1) * (L + 3 / 10))) <
          -(8027 / 10000) * (4 * L + 4 / 5) * ((L + 1) * (L + 3 / 10)) := by
        nlinarith [hL2, hL3]
      have hJq : (4 * (-(33 / 28) / (L + 1) + 10 / 7 / (L + 3 / 10)) - 2 * (145 / 49)) *
          ((L + 1) * (L + 3 / 10)) = 4 * (-(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1)) -
            2 * (145 / 49) * ((L + 1) * (L + 3 / 10)) := by
        field_simp
      rw [← hJq] at key
      exact lt_of_mul_lt_mul_right key hq.le

/-- Cochrane (2023), Table 5.2 row 4 and Fig. 5.13 (infrastructure): the zero-weighted-sum value
`π₀* = λ₁I − (I − J)/(λ₂)` (here `r + λ₂ = λ₁`, `λ₁ − r = λ₂`, `κσ = 1`) satisfies
`0.5085 < π₀* < 0.5086`. -/
theorem table52_pi0_bounds :
    (51 / 100 - 15 / 10000 : ℝ) <
        (1 / 20 + lam2 (1 / 20) 2 (1 / 2)) *
            (∫ τ in Set.Ioi 0, Real.exp (-(1 / 20 * τ)) * fig511i τ) -
          2 * (1 / 2) * ((∫ τ in Set.Ioi 0, Real.exp (-(1 / 20 * τ)) * fig511i τ) -
            ∫ τ in Set.Ioi 0, Real.exp (-(lam1 (1 / 20) 2 (1 / 2) * τ)) * fig511i τ) /
            (lam1 (1 / 20) 2 (1 / 2) - 1 / 20) ∧
      (1 / 20 + lam2 (1 / 20) 2 (1 / 2)) *
            (∫ τ in Set.Ioi 0, Real.exp (-(1 / 20 * τ)) * fig511i τ) -
          2 * (1 / 2) * ((∫ τ in Set.Ioi 0, Real.exp (-(1 / 20 * τ)) * fig511i τ) -
            ∫ τ in Set.Ioi 0, Real.exp (-(lam1 (1 / 20) 2 (1 / 2) * τ)) * fig511i τ) /
            (lam1 (1 / 20) 2 (1 / 2) - 1 / 20) < 51 / 100 - 14 / 10000 := by
  obtain ⟨hL2, hlam2, hl, hu⟩ := fig511_lam
  set L := lam1 (1 / 20) 2 (1 / 2)
  have hI : ∫ τ in Set.Ioi 0, Real.exp (-(1 / 20 * τ)) * fig511i τ = 145 / 49 := by
    rw [integral_fig511i (by norm_num)]
    norm_num
  rw [hI, integral_fig511i (a := L) (by linarith), hlam2]
  have hq : 0 < (L - 1 / 20) * ((L + 1) * (L + 3 / 10)) := by
    have : 0 < L - 1 / 20 := by linarith
    positivity
  have hL3 : L ^ 3 = 1 / 20 * L ^ 2 + L := by linear_combination L * hL2
  have hL4 : L ^ 4 = 1 / 20 * L ^ 3 + L ^ 2 := by linear_combination L ^ 2 * hL2
  have hE : ((1 / 20 + (L - 1 / 20)) * (145 / 49) - 2 * (1 / 2) * (145 / 49 -
      (-(33 / 28) / (L + 1) + 10 / 7 / (L + 3 / 10))) / (L - 1 / 20)) *
        ((L - 1 / 20) * ((L + 1) * (L + 3 / 10))) =
      L * (145 / 49) * ((L - 1 / 20) * ((L + 1) * (L + 3 / 10))) -
        (145 / 49 * ((L + 1) * (L + 3 / 10)) -
          (-(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1))) := by
    have hD : L - 1 / 20 ≠ 0 := by linarith
    have : L + 1 ≠ 0 := by linarith
    have : L + 3 / 10 ≠ 0 := by linarith
    have hJQ : (-(33 / 28) / (L + 1) + 10 / 7 / (L + 3 / 10)) * ((L + 1) * (L + 3 / 10)) =
        -(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1) := by
      field_simp
    have h1 : 2 * (1 / 2) * (145 / 49 - (-(33 / 28) / (L + 1) + 10 / 7 / (L + 3 / 10))) /
        (L - 1 / 20) * ((L - 1 / 20) * ((L + 1) * (L + 3 / 10))) =
        2 * (1 / 2) * (145 / 49 - (-(33 / 28) / (L + 1) + 10 / 7 / (L + 3 / 10))) *
          ((L + 1) * (L + 3 / 10)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hD]
    rw [sub_mul, h1]
    linear_combination hJQ
  constructor
  · have key : (51 / 100 - 15 / 10000) * ((L - 1 / 20) * ((L + 1) * (L + 3 / 10))) <
        L * (145 / 49) * ((L - 1 / 20) * ((L + 1) * (L + 3 / 10))) -
          (145 / 49 * ((L + 1) * (L + 3 / 10)) -
            (-(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1))) := by
      nlinarith [hL2, hL3, hL4]
    rw [← hE] at key
    exact lt_of_mul_lt_mul_right key hq.le
  · have key : L * (145 / 49) * ((L - 1 / 20) * ((L + 1) * (L + 3 / 10))) -
          (145 / 49 * ((L + 1) * (L + 3 / 10)) -
            (-(33 / 28) * (L + 3 / 10) + 10 / 7 * (L + 1))) <
        (51 / 100 - 14 / 10000) * ((L - 1 / 20) * ((L + 1) * (L + 3 / 10))) := by
      nlinarith [hL2, hL3, hL4]
    rw [← hE] at key
    exact lt_of_mul_lt_mul_right key hq.le

/-- Cochrane (2023), §5.7.5 (Table 5.2 setting): in any rules equilibrium with `α > r` and bounded
continuous rate and disturbance paths, the discounted surplus stream is integrable (the weighted
sum of surpluses exists). -/
theorem rules_surplus_integrable {r σ κ ρ θsπ θsx α M Mu : ℝ} {i us x π v s : ℝ → ℝ}
    (hr : 0 < r) (hαr : r < α) (hi : ContinuousOn i (Set.Ici 0))
    (hM : ∀ t, 0 ≤ t → |i t| ≤ M) (hu : ContinuousOn us (Set.Ici 0))
    (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu) (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s) :
    IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0) := by
  obtain ⟨Kv, hKv⟩ := rules_v_bounded hαr hi hM hu hMu h
  obtain ⟨Kx, hKx⟩ := h.1.2.1
  obtain ⟨Kπ, hKπ⟩ := h.1.2.2
  have hc : ContinuousOn s (Set.Ici 0) :=
    ((((continuousOn_const.mul h.1.1.2.1).add (continuousOn_const.mul h.1.1.1)).add
      (continuousOn_const.mul h.2.2.1)).add hu).congr fun t ht => h.2.1 t ht
  refine integrableOn_of_contOn_bdd (K := |θsπ| * Kπ + |θsx| * Kx + |α| * Kv + Mu) hr le_rfl hc
    fun t ht => ?_
  rw [h.2.1 t ht]
  calc |θsπ * π t + θsx * x t + α * v t + us t|
      ≤ |θsπ * π t| + |θsx * x t| + |α * v t| + |us t| :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_mul]
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hKπ t ht) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hKx t ht) (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left (hKv t ht) (abs_nonneg _))) (hMu t ht)

/-- Cochrane (2023), Table 5.2 row 4, Fig. 5.13 and p. 178 (survey E52): **the corrected
`β_i = −0.5085`, machine-checked.** With `α = 0.4`, `s̃ = x + π + 0.4v`, short-term debt and the
Fig. 5.11 parameters and rate path: (i) there is a rules equilibrium whose weighted sum of
surpluses `∫_0^∞ e^{−rτ}s̃_τ dτ` is zero; (ii) every such equilibrium has
`0.5085 < π₀ < 0.5086`, so the inflation-target loading `β_i = −π₀` (unit shock `ε_i = 1`,
(5.111)) satisfies `−0.5086 < β_i < −0.5085`, and the printed Table 5.2 value `−0.91` is wrong. -/
theorem table52_betai :
    (∃ x π v s : ℝ → ℝ, IsRulesEq (1 / 20) (1 / 2) 2 (1 / 20) 1 1 (2 / 5) fig511i (fun _ => 0)
        x π v s ∧ ∫ τ in Set.Ioi 0, Real.exp (-(1 / 20 * τ)) * s τ = 0) ∧
      ∀ x π v s : ℝ → ℝ, IsRulesEq (1 / 20) (1 / 2) 2 (1 / 20) 1 1 (2 / 5) fig511i (fun _ => 0)
        x π v s → ∫ τ in Set.Ioi 0, Real.exp (-(1 / 20 * τ)) * s τ = 0 →
          -(5086 / 10000) < -π 0 ∧ -π 0 < -(5085 / 10000) ∧ -π 0 ≠ -(91 / 100) := by
  obtain ⟨hic, hib⟩ := fig511i_bdd
  obtain ⟨-, -, hl, -⟩ := fig511_lam
  obtain ⟨b1, b2⟩ := table52_pi0_bounds
  have hne : lam1 (1 / 20) 2 (1 / 2) ≠ 1 / 20 := by intro h; rw [h] at hl; norm_num at hl
  have hiff := fun {x π v s : ℝ → ℝ}
      (h : IsRulesEq (1 / 20) (1 / 2) 2 (1 / 20) 1 1 (2 / 5) fig511i (fun _ => 0) x π v s) =>
    ct_zero_weighted_sum_iff (M := 33 / 28 + 10 / 7) (by norm_num) (by norm_num) (by norm_num)
      hic hib hne h (rules_surplus_integrable (Mu := 0) (by norm_num) (by norm_num) hic hib
        continuousOn_const (fun _ _ => by simp) h)
  refine ⟨?_, fun x π v s h h0 => ?_⟩
  · obtain ⟨x, π, v, s, h, hπ0⟩ := rules_exists_pos (r := 1 / 20) (σ := 1 / 2) (κ := 2)
      (ρ := 1 / 20) (θsπ := 1) (θsx := 1) (α := 2 / 5) (i := fig511i) (us := fun _ => 0)
      (M := 33 / 28 + 10 / 7) (Mu := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hic hib continuousOn_const (fun _ _ => by simp) _
    exact ⟨x, π, v, s, h, (hiff h).2 hπ0⟩
  · have e := (hiff h).1 h0
    rw [e]
    refine ⟨by linarith, by linarith, by intro h'; linarith⟩

end Cochrane.StickyPriceFiscal.CTRulesEquilibrium
