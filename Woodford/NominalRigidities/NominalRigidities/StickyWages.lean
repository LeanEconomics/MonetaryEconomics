/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Persistence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Nominal wage stickiness: the log-linear model

Woodford (2003), *Interest and Prices*, Chapter 3, §4 "Consequences of Nominal Wage Stickiness",
pp. 223–236: eqs. (4.6)–(4.25), Proposition 3.9, the Andersen and Huang–Liu cases, and the
joint wage/price dynamics. The nonlinear wage-setting problem (4.1)–(4.5) and the exact
linearisations behind (4.6)–(4.7) are in `WageSetting`.

All equations hold for an arbitrary `ExpectationSystem` (perfect foresight or uncertainty).
Processes are `ℕ → Ω → ℝ`; a lag is written with an explicit date-`(−1)` value via `prev`.

## Main results

* Calvo algebra (§4.1): `calvo_pc_iff` — given the index law (4.6) (with indexation rate `γ`),
  the recursive reset rule holds at `t` **iff** the (indexed) inflation equation
  `π̃_t = ξ (m_t − X_t) + β E_t π̃_{t+1}` holds at `t`; `forwardSeries_solves_growth`,
  `eq_forwardSeries_growth`, `reset_sum_iff_pc`: **(4.6)–(4.7) ⟺ (4.8)** (and its indexed
  version behind (4.23)–(4.24)) for processes growing at most geometrically at a rate
  `b < 1/(α β)`, so trending nominal levels are allowed; the same theorem with
  `(ω_p, θ_p)` gives the price equation (4.9).
* `price_gap_eq`, `printed_s_hat_iff` (**E14**): `ŝ_t = log W_t − log P_t − log w̄ + ψ̂_t`; the
  printed `ŝ_t = log W_t − log P_t + ψ̂_t` is right iff `w̄ = 1`.
* `hasDerivAt_logMRS`, `hasDerivAt_psihat`: (4.10) and `ψ̂ = ω_p Ŷ − (1 + ω_p) a` as
  exact derivatives; `vhat_alt`, `vhat_add_psihat`, `natural_output_iff`.
* **Proposition 3.9** `prop_3_9`; `natural_real_wage_iff`; `kappaW_pos`, `kappaP_pos`.
* (4.13)–(4.15): `eq414`, `kappaBar_pos`, `kappaBar_strictMonoOn_xiW`, `xi_strictAntiOn`,
  `kappaBar_strictAntiOn_alphaW`, `tendsto_kappaBar_alphaW`, `tendsto_weight_alphaW`,
  `kappaBar_flexible_wages_eq`, `tendsto_kappaBar_alphaP`, `tendsto_weight_alphaP`.
* (4.16)–(4.17): `eq416`, `nominal_wage_eq`, `kappaHat_eq`, `lam_gt_alpha_iff`; the impulse
  responses `wtilde_unique` (`w̃_k = 1 − λ^{k+1}`), `output_response`, and for an arbitrary
  expectation system `pc_iff_anchor`, `anchor_existsUnique`, `anchor_E_response` (which also
  give the price-level responses under (4.19)); **E13** `printed_output_response_ne`.
* Andersen and Huang–Liu (pp. 228–230): `andersen_wage`, `andersen_contract_multiplier_iff`,
  `andersen_price`, `huang_liu_tilde`, `huang_liu_common`, `huang_liu_specific_le_iff`,
  `specific_lt_common`; **E15** `zetaTilde_lt_zetaCommon` (correct condition `θ_w ≥ θ_p`) and
  `printed_E15_counterexample`.
* (4.18)–(4.22): `eq418`, `eq418_iff_secondOrder`, `secondOrder_existsUnique`, `eq422`,
  `realWage_indep_of_output`, `eq419`, **E12** `printed_eq419_counterexample`,
  `kappa_sticky_lt_flexible`, `output_response_larger`, `eq421`, `omega_gt_nu`,
  `phiH_gt_one`, `alphaW_existsUnique`, `alphaW_none_of_linear`, `tendsto_lam1_atTop`,
  `tendsto_inv_lam2_atTop`,
  `realWage_response_sign`, `natural_real_wage_solves_iff`, `bounded_natural_wage_const`.
* Flexible limit of (4.22) (p. 232): `secondOrder_flexible_bound`, `tendsto_flexBound`,
  `secondOrder_flexible_limit` (with forcing `z = c ẑ`, `log w_t − ẑ_t → 0` and
  `log w_t − λ₁ z_t → 0` uniformly), `forcing_factor`, `tendsto_ratio_flexible_wages`,
  `tendsto_ratio_flexible_prices`, `realWage_flexible_limit` (limits (4.21) and the
  flexible-price relation).
* (4.23)–(4.25): `eq423_424`, `eq425_flexible_prices`, `eq425_equal_indexation`.
* Fig. 3.18 (p. 233): `fig318_equal_stickiness` — with the Rotemberg–Woodford values
  `κ_w = κ_p` requires `ξ_w ≈ 0.055`, not the printed `0.55`.
-/

namespace Woodford.NominalRigidities.StickyWages

open Filter Topology QuadraticRoots
open Persistence (prev prev_zero prev_succ)

/-! ### Lags and the characteristic roots

The lag `prev` is `Persistence.prev`; the roots `λ₁ < λ₂` of `P(λ) = βλ² − (1 + β + c)λ + 1` and
their general properties are those of `QuadraticRoots`. The statements quoted for (4.22) are
restated here from that module. -/

/-- Woodford (2003), p. 231: `0 < λ₁` (restated from `QuadraticRoots.lam1_pos`). -/
theorem lam1_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < lam1 β c :=
  QuadraticRoots.lam1_pos hβ hc

/-- Woodford (2003), p. 231: `λ₁ < 1` (restated from `QuadraticRoots.lam1_lt_one`). -/
theorem lam1_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c < 1 :=
  QuadraticRoots.lam1_lt_one hβ hc

/-- Woodford (2003), p. 231: `λ₂ > β⁻¹` (so `0 < λ₁ < 1 < β⁻¹ < λ₂` when `β < 1`; restated from
`QuadraticRoots.inv_lt_lam2`). -/
theorem inv_beta_lt_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : β⁻¹ < lam2 β c :=
  inv_lt_lam2 hβ hc

/-- Woodford (2003), p. 231: the factorisation `βx² − (1 + β + c)x + 1 = β(x − λ₁)(x − λ₂)`
(restated from `QuadraticRoots.charPoly_factor`). -/
theorem quad_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (x : ℝ) :
    β * x ^ 2 - (1 + β + c) * x + 1 = β * (x - lam1 β c) * (x - lam2 β c) :=
  charPoly_factor hβ hc x

/-- Woodford (2003), p. 231: `(β λ₂)⁻¹ = λ₁`. -/
theorem inv_beta_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : (β * lam2 β c)⁻¹ = lam1 β c := by
  rw [mul_inv, inv_lam2 hβ hc, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]

/-- Woodford (2003), p. 192 (as used for (4.17) and p. 231): `λ₁` is strictly decreasing in
`c > 0` — a flatter slope gives a more persistent response (restated from
`QuadraticRoots.lam1_strictAntiOn`). -/
theorem lam1_strictAntiOn {β : ℝ} (hβ : 0 < β) : StrictAntiOn (lam1 β) (Set.Ioi 0) :=
  QuadraticRoots.lam1_strictAntiOn hβ

/-- Woodford (2003), p. 232: as the slope grows without bound, `λ₁ → 0` (restated from
`QuadraticRoots.tendsto_lam1_atTop`). -/
theorem tendsto_lam1_atTop {β : ℝ} (hβ : 0 < β) : Tendsto (lam1 β) atTop (𝓝 0) :=
  QuadraticRoots.tendsto_lam1_atTop hβ

/-- Woodford (2003), p. 232: as the slope grows without bound, `λ₂⁻¹ → 0` (restated from
`QuadraticRoots.tendsto_inv_lam2_atTop`). -/
theorem tendsto_inv_lam2_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun c => (lam2 β c)⁻¹) atTop (𝓝 0) :=
  QuadraticRoots.tendsto_inv_lam2_atTop hβ

/-! ### The second-order expectational difference equation (4.18)/(4.22) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eqs. (4.18) and (4.22), pp. 230–231 (and (2.16)): the equation
`β E_t ℓ_{t+1} − (1 + β + c) ℓ_t + ℓ_{t−1} = −z_t` for all `t ≥ 0`, with `ℓ_{−1} = ℓ₋₁`. -/
def SecondOrder (β c : ℝ) (ℓm1 : Ω → ℝ) (z ℓ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, β • 𝔼.E t (ℓ (t + 1)) - (1 + β + c) • ℓ t + prev ℓm1 ℓ t = -z t

/-- Woodford (2003), p. 231: the factorised form. If `ℓ_t = λ₁ ℓ_{t−1} + e_t` with
`e_t = λ₂⁻¹ E_t e_{t+1} + (βλ₂)⁻¹ z_t` and `ℓ` adapted, then `ℓ` solves (4.18)/(4.22). -/
theorem secondOrder_of_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {ℓm1 : Ω → ℝ}
    {z ℓ e : ℕ → Ω → ℝ} (hℓa : 𝔼.Adapted ℓ)
    (hℓ : ∀ t, ℓ t = lam1 β c • prev ℓm1 ℓ t + e t)
    (he : ∀ t, e t = (lam2 β c)⁻¹ • 𝔼.E t (e (t + 1)) + (β * lam2 β c)⁻¹ • z t) :
    SecondOrder 𝔼 β c ℓm1 z ℓ := by
  intro t
  have hl2 : lam2 β c ≠ 0 := (lt_trans one_pos (one_lt_lam2 hβ hc)).ne'
  have hE : 𝔼.E t (ℓ (t + 1)) = lam1 β c • ℓ t + 𝔼.E t (e (t + 1)) := by
    rw [hℓ (t + 1), map_add, map_smul, prev_succ, hℓa t]
  rw [hE]
  funext ω
  have h1 := congrFun (he t) ω
  have h2 := congrFun (hℓ t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply] at h1 h2 ⊢
  have hp := beta_mul_prod hβ hc
  have hs := beta_mul_sum (c := c) hβ
  have h1' : β * 𝔼.E t (e (t + 1)) ω = β * lam2 β c * e t ω - z t ω := by
    rw [h1]
    field_simp
    ring
  linear_combination h1' - β * lam2 β c * h2 + ℓ t ω * hs - prev ℓm1 ℓ t ω * hp

/-- Woodford (2003), p. 231: **uniqueness** — two bounded adapted solutions of (4.18)/(4.22)
with the same `ℓ₋₁` coincide (`0 < λ₁ < 1 < λ₂`; the unstable root forces the forward
component, the stable root and the initial condition pin down the rest). -/
theorem secondOrder_unique {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {ℓm1 : Ω → ℝ}
    {z ℓ ℓ' : ℕ → Ω → ℝ} (h : SecondOrder 𝔼 β c ℓm1 z ℓ) (h' : SecondOrder 𝔼 β c ℓm1 z ℓ')
    (ha : 𝔼.Adapted ℓ) (ha' : 𝔼.Adapted ℓ') (hb : BoundedProc ℓ) (hb' : BoundedProc ℓ') :
    ℓ = ℓ' := by
  set d : ℕ → Ω → ℝ := fun t => ℓ t - ℓ' t with hd
  set e : ℕ → Ω → ℝ := fun t => d t - lam1 β c • prev 0 d t with he
  have hl2 : lam2 β c ≠ 0 := (lt_trans one_pos (one_lt_lam2 hβ hc)).ne'
  have hprev : ∀ t, prev ℓm1 ℓ t - prev ℓm1 ℓ' t = prev 0 d t := by
    intro t; cases t <;> simp [hd]
  have hda : ∀ t, 𝔼.E t (d t) = d t := fun t => by simp [hd, map_sub, ha t, ha' t]
  -- `λ₂ e_t = E_t e_{t+1}`
  have key : ∀ t, lam2 β c • e t = 𝔼.E t (e (t + 1)) := by
    intro t
    have hEd : 𝔼.E t (e (t + 1)) = 𝔼.E t (ℓ (t + 1)) - 𝔼.E t (ℓ' (t + 1)) - lam1 β c • d t := by
      change 𝔼.E t (d (t + 1) - lam1 β c • d t) = _
      rw [map_sub, map_smul, hda t]
      simp only [hd, map_sub]
    rw [hEd]
    funext ω
    have k1 := congrFun (h t) ω
    have k2 := congrFun (h' t) ω
    have k3 := congrFun (hprev t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply] at k1 k2 k3
    have hp := beta_mul_prod hβ hc
    have hs := beta_mul_sum (c := c) hβ
    have hX : β * (lam2 β c * (d t ω - lam1 β c * prev 0 d t ω) - (𝔼.E t (ℓ (t + 1)) ω
        - 𝔼.E t (ℓ' (t + 1)) ω - lam1 β c * d t ω)) = 0 := by
      rw [← k3]
      simp only [hd, Pi.sub_apply]
      linear_combination (ℓ t ω - ℓ' t ω) * hs
        - (prev ℓm1 ℓ t ω - prev ℓm1 ℓ' t ω) * hp - (k1 - k2)
    have hX' := (mul_eq_zero.mp hX).resolve_left hβ.ne'
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hfe : ∀ t, e t = (lam2 β c)⁻¹ • 𝔼.E t (e (t + 1)) + 0 := fun t => by
    rw [← key t, smul_smul, inv_mul_cancel₀ hl2, one_smul, add_zero]
  have hebd : BoundedProc e := by
    obtain ⟨M, hM⟩ := hb
    obtain ⟨M', hM'⟩ := hb'
    refine ⟨(M + M') + |lam1 β c| * (M + M'), fun t ω => ?_⟩
    have hdb : ∀ s ω, |d s ω| ≤ M + M' := fun s ω => by
      simp only [hd, Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hM s ω) (hM' s ω))
    have hpb : |prev 0 d t ω| ≤ M + M' := by
      cases t with
      | zero =>
        simp only [prev_zero, Pi.zero_apply, abs_zero]
        exact le_trans (abs_nonneg _) (hdb 0 ω)
      | succ t => exact hdb t ω
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hdb t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hpb (abs_nonneg _)
  have ha2 : |(lam2 β c)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (lt_trans one_pos (one_lt_lam2 hβ hc))]
    exact inv_lt_one_of_one_lt₀ (one_lt_lam2 hβ hc)
  have he0 : e = 0 := 𝔼.forward_unique ha2 hfe (fun t => by simp) hebd ⟨0, fun _ _ => by simp⟩
  have hd0 : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero =>
      have := congrFun he0 0
      simpa [he] using this
    | succ t ih =>
      have := congrFun he0 (t + 1)
      simp only [he, prev_succ, ih, smul_zero, sub_zero, Pi.zero_apply] at this
      exact this
  funext t ω
  have := congrFun (hd0 t) ω
  simp only [hd, Pi.sub_apply, Pi.zero_apply] at this
  linarith

/-- Woodford (2003), eq. (4.22), p. 231: the forward component
`F_t = ∑ₖ λ₂^{−k} E_t[(βλ₂)⁻¹ z_{t+k}] = β⁻¹ ∑ⱼ λ₂^{−j−1} E_t z_{t+j}`. -/
noncomputable def fwdPart (β c : ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (lam2 β c)⁻¹ (fun t => (β * lam2 β c)⁻¹ • z t)

/-- Woodford (2003), eq. (4.22), p. 231: the solution
`ℓ_t = λ₁ ℓ_{t−1} + β⁻¹ ∑ⱼ λ₂^{−j−1} E_t z_{t+j}`, defined recursively from `ℓ₋₁`. -/
noncomputable def secondOrderSol (β c : ℝ) (ℓm1 : Ω → ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => lam1 β c • ℓm1 + fwdPart 𝔼 β c z 0
  | t + 1 => lam1 β c • secondOrderSol β c ℓm1 z t + fwdPart 𝔼 β c z (t + 1)

/-- Woodford (2003), eq. (4.22), p. 231: `ℓ_t = λ₁ ℓ_{t−1} + F_t` at every date. -/
theorem secondOrderSol_eq (β c : ℝ) (ℓm1 : Ω → ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) :
    secondOrderSol 𝔼 β c ℓm1 z t =
      lam1 β c • prev ℓm1 (secondOrderSol 𝔼 β c ℓm1 z) t + fwdPart 𝔼 β c z t := by
  cases t <;> rfl

/-- Woodford (2003), eq. (4.22), p. 231: the forward component in the printed form
`β⁻¹ ∑ⱼ λ₂^{−j−1} E_t z_{t+j}`. -/
theorem fwdPart_apply (β c : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    fwdPart 𝔼 β c z t ω = β⁻¹ * ∑' j, (lam2 β c ^ (j + 1))⁻¹ * 𝔼.E t (z (t + j)) ω := by
  unfold fwdPart ExpectationSystem.forwardSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, pow_succ, mul_inv, mul_inv,
    inv_pow]
  ring

/-- Woodford (2003), eq. (4.22), p. 231 (**existence and uniqueness**): for `0 < β ≤ 1`,
`c > 0`, a bounded adapted forcing process `z` and a bounded `ℓ₋₁` known at date 0, the
process (4.22) is a bounded adapted solution of (4.18)/(4.22), and it is the only one. -/
theorem secondOrder_existsUnique {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {z : ℕ → Ω → ℝ}
    (hz : BoundedProc z) (hza : 𝔼.Adapted z) {ℓm1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |ℓm1 ω| ≤ K) (hm0 : 𝔼.E 0 ℓm1 = ℓm1) :
    SecondOrder 𝔼 β c ℓm1 z (secondOrderSol 𝔼 β c ℓm1 z) ∧
      BoundedProc (secondOrderSol 𝔼 β c ℓm1 z) ∧ 𝔼.Adapted (secondOrderSol 𝔼 β c ℓm1 z) ∧
      ∀ ℓ, SecondOrder 𝔼 β c ℓm1 z ℓ → BoundedProc ℓ → 𝔼.Adapted ℓ →
        ℓ = secondOrderSol 𝔼 β c ℓm1 z := by
  obtain ⟨Mz, hMz⟩ := hz
  have hl2 : 1 < lam2 β c := one_lt_lam2 hβ hc
  have ha : |(lam2 β c)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (lt_trans one_pos hl2)]
    exact inv_lt_one_of_one_lt₀ hl2
  set u : ℕ → Ω → ℝ := fun t => (β * lam2 β c)⁻¹ • z t with hu
  have hub : ∀ t ω, |u t ω| ≤ |(β * lam2 β c)⁻¹| * Mz := fun t ω => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  have hua : 𝔼.Adapted u := fun t => by simp only [hu, map_smul, hza t]
  have hFs := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hub hua
  obtain ⟨BF, hBF⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hub
  have hFa := ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hub
  set ℓ := secondOrderSol 𝔼 β c ℓm1 z with hℓdef
  have hl1 := lam1_pos hβ hc
  have hl1' := lam1_lt_one hβ hc
  -- adaptedness
  have hadapt : 𝔼.Adapted ℓ := by
    intro t
    induction t with
    | zero =>
      change 𝔼.E 0 (lam1 β c • ℓm1 + fwdPart 𝔼 β c z 0) = _
      rw [map_add, map_smul, hm0]
      exact congrArg _ (hFa 0)
    | succ t ih =>
      change 𝔼.E (t + 1) (lam1 β c • ℓ t + fwdPart 𝔼 β c z (t + 1))
        = lam1 β c • ℓ t + fwdPart 𝔼 β c z (t + 1)
      rw [map_add, map_smul, ← ih, 𝔼.known (Nat.le_succ t), ih]
      congr 1
      exact hFa (t + 1)
  -- boundedness
  have hbdd : BoundedProc ℓ := by
    set B := max K (BF / (1 - lam1 β c)) with hB
    have hKB : K ≤ B := le_max_left _ _
    have hFB : BF ≤ (1 - lam1 β c) * B := by
      have := le_max_right K (BF / (1 - lam1 β c))
      rw [← hB, div_le_iff₀ (by linarith)] at this
      linarith
    refine ⟨B, fun t => ?_⟩
    induction t with
    | zero =>
      intro ω
      have e : ℓ 0 ω = lam1 β c * ℓm1 ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u 0 ω := rfl
      rw [e]
      have h1 : |lam1 β c * ℓm1 ω| ≤ lam1 β c * B := by
        rw [abs_mul, abs_of_pos hl1]
        exact mul_le_mul_of_nonneg_left ((hK ω).trans hKB) hl1.le
      calc |lam1 β c * ℓm1 ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u 0 ω|
          ≤ |lam1 β c * ℓm1 ω| + |𝔼.forwardSeries (lam2 β c)⁻¹ u 0 ω| := abs_add_le _ _
        _ ≤ lam1 β c * B + BF := add_le_add h1 (hBF 0 ω)
        _ ≤ B := by linarith
    | succ t ih =>
      intro ω
      have e : ℓ (t + 1) ω = lam1 β c * ℓ t ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u (t + 1) ω := rfl
      rw [e]
      have h1 : |lam1 β c * ℓ t ω| ≤ lam1 β c * B := by
        rw [abs_mul, abs_of_pos hl1]
        exact mul_le_mul_of_nonneg_left (ih ω) hl1.le
      calc |lam1 β c * ℓ t ω + 𝔼.forwardSeries (lam2 β c)⁻¹ u (t + 1) ω|
          ≤ |lam1 β c * ℓ t ω| + |𝔼.forwardSeries (lam2 β c)⁻¹ u (t + 1) ω| := abs_add_le _ _
        _ ≤ lam1 β c * B + BF := add_le_add h1 (hBF (t + 1) ω)
        _ ≤ B := by linarith
  have hsol : SecondOrder 𝔼 β c ℓm1 z ℓ :=
    secondOrder_of_factor 𝔼 hβ hc hadapt (e := 𝔼.forwardSeries (lam2 β c)⁻¹ u)
      (fun t => secondOrderSol_eq 𝔼 β c ℓm1 z t) (fun t => hFs t)
  exact ⟨hsol, hbdd, hadapt, fun ℓ' h' hb' ha' =>
    secondOrder_unique 𝔼 hβ hc h' hsol ha' hadapt hb' hbdd⟩

/-- Woodford (2003), p. 233 and footnote 77: the solution (4.22) is nonnegative when the forcing
process and the initial condition are nonnegative (`E_t` is monotone and `λ₁ > 0`). -/
theorem secondOrderSol_nonneg {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {z : ℕ → Ω → ℝ}
    {ℓm1 : Ω → ℝ} (hz0 : ∀ t ω, 0 ≤ z t ω) (hm : ∀ ω, 0 ≤ ℓm1 ω) (t : ℕ) (ω : Ω) :
    0 ≤ secondOrderSol 𝔼 β c ℓm1 z t ω := by
  have hl2 : 0 < lam2 β c := lt_trans one_pos (one_lt_lam2 hβ hc)
  have hF : ∀ s ω, 0 ≤ fwdPart 𝔼 β c z s ω := by
    intro s ω
    unfold fwdPart ExpectationSystem.forwardSeries
    refine tsum_nonneg fun k => mul_nonneg (pow_nonneg (inv_nonneg.mpr hl2.le) k) ?_
    have h0 : (0 : Ω → ℝ) ≤ (β * lam2 β c)⁻¹ • z (s + k) := fun ω' => by
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (mul_pos hβ hl2).le) (hz0 _ ω')
    have := 𝔼.mono s h0 ω
    simpa using this
  have hl1 := (lam1_pos hβ hc).le
  induction t generalizing ω with
  | zero =>
    change 0 ≤ lam1 β c * ℓm1 ω + fwdPart 𝔼 β c z 0 ω
    exact add_nonneg (mul_nonneg hl1 (hm ω)) (hF 0 ω)
  | succ t ih =>
    change 0 ≤ lam1 β c * secondOrderSol 𝔼 β c ℓm1 z t ω + fwdPart 𝔼 β c z (t + 1) ω
    exact add_nonneg (mul_nonneg hl1 (ih ω)) (hF (t + 1) ω)

/-- Woodford (2003), eq. (4.22), p. 231: with `ℓ₋₁ = 0` the solution is linear in the forcing
process, `ℓ[a z] = a ℓ[z]`. -/
theorem secondOrderSol_smul (β c a : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) :
    secondOrderSol 𝔼 β c 0 (fun s => a • z s) t = a • secondOrderSol 𝔼 β c 0 z t := by
  have hF : ∀ s, fwdPart 𝔼 β c (fun s => a • z s) s = a • fwdPart 𝔼 β c z s := by
    intro s
    funext ω
    unfold fwdPart ExpectationSystem.forwardSeries
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [smul_smul, mul_comm (β * lam2 β c)⁻¹ a, ← smul_smul, map_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  induction t with
  | zero =>
    change lam1 β c • (0 : Ω → ℝ) + fwdPart 𝔼 β c (fun s => a • z s) 0
      = a • (lam1 β c • (0 : Ω → ℝ) + fwdPart 𝔼 β c z 0)
    rw [hF, smul_zero, zero_add, zero_add]
  | succ t ih =>
    change lam1 β c • secondOrderSol 𝔼 β c 0 (fun s => a • z s) t
        + fwdPart 𝔼 β c (fun s => a • z s) (t + 1)
      = a • (lam1 β c • secondOrderSol 𝔼 β c 0 z t + fwdPart 𝔼 β c z (t + 1))
    rw [ih, hF, smul_add, smul_smul, smul_smul, mul_comm]

/-! ### Forward sums of geometrically growing processes (for (4.7) with trending levels) -/

/-- Woodford (2003), eq. (4.7), p. 223: the forward sum `∑ₖ aᵏ E_t y_{t+k}` of an adapted process
with `|y_s| ≤ M bˢ` and `a b < 1` (so nominal levels may trend) solves
`Z_t = a E_t Z_{t+1} + y_t`. -/
theorem forwardSeries_solves_growth {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b < 1)
    {y : ℕ → Ω → ℝ} (hy : ∀ s ω, |y s ω| ≤ M * b ^ s) (hya : 𝔼.Adapted y) (t : ℕ) :
    𝔼.forwardSeries a y t = a • 𝔼.E t (𝔼.forwardSeries a y (t + 1)) + y t := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  have hterm : ∀ s k ω, |a ^ k * 𝔼.E s (y (s + k)) ω| ≤ (a * b) ^ k * (M * b ^ s) := by
    intro s k ω
    rw [abs_mul, abs_of_nonneg (pow_nonneg ha k)]
    calc a ^ k * |𝔼.E s (y (s + k)) ω| ≤ a ^ k * (M * b ^ (s + k)) :=
          mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hy (s + k)) s ω) (pow_nonneg ha k)
      _ = (a * b) ^ k * (M * b ^ s) := by rw [pow_add, mul_pow]; ring
  have hsum : ∀ s ω, Summable fun k => a ^ k * 𝔼.E s (y (s + k)) ω := fun s ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hab0 hab).mul_right (M * b ^ s))
      fun k => by rw [Real.norm_eq_abs]; exact hterm s k ω
  funext ω
  have hE : 𝔼.E t (𝔼.forwardSeries a y (t + 1)) ω =
      ∑' k, a ^ k * 𝔼.E t (y (t + 1 + k)) ω := by
    change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (y (t + 1 + k)) ω') ω = _
    rw [𝔼.E_tsum hab0 hab (fun k ω' => hterm (t + 1) k ω') t ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (y (t + 1 + k))) ω = _
    rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, a ^ k * 𝔼.E t (y (t + k)) ω = _
  rw [hE, (hsum t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero, hya t, ← tsum_mul_left,
    add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Woodford (2003), eq. (4.7), p. 223: every solution of `Z_t = a E_t Z_{t+1} + y_t` with
`|Z_s| ≤ K bˢ` (`a b < 1`) is the forward sum `∑ₖ aᵏ E_t y_{t+k}`. -/
theorem eq_forwardSeries_growth {a b M K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b < 1)
    {y z : ℕ → Ω → ℝ} (hy : ∀ s ω, |y s ω| ≤ M * b ^ s) (hya : 𝔼.Adapted y)
    (hz : ∀ s ω, |z s ω| ≤ K * b ^ s) (hzs : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + y t) :
    z = 𝔼.forwardSeries a y := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  funext t ω
  have hsum : Summable fun k => a ^ k * 𝔼.E t (y (t + k)) ω := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hab0 hab).mul_right (M * b ^ t)) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha k)]
    calc a ^ k * |𝔼.E t (y (t + k)) ω| ≤ a ^ k * (M * b ^ (t + k)) :=
          mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hy (t + k)) t ω) (pow_nonneg ha k)
      _ = (a * b) ^ k * (M * b ^ t) := by rw [pow_add, mul_pow]; ring
  have hlim : Tendsto (fun k => ∑ j ∈ Finset.range k, a ^ j * 𝔼.E t (y (t + j)) ω) atTop
      (𝓝 (z t ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun k => (a * b) ^ k * (K * b ^ t)) (fun k => ?_) ?_
    · have h := congrFun (ForwardSolution.iterate_A15 𝔼 hya hzs t k) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
      rw [norm_norm, Real.norm_eq_abs, abs_sub_comm]
      have he : z t ω - ∑ j ∈ Finset.range k, a ^ j * 𝔼.E t (y (t + j)) ω =
          a ^ k * 𝔼.E t (z (t + k)) ω := by linarith
      rw [he, abs_mul, abs_of_nonneg (pow_nonneg ha k)]
      calc a ^ k * |𝔼.E t (z (t + k)) ω| ≤ a ^ k * (K * b ^ (t + k)) :=
            mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hz (t + k)) t ω) (pow_nonneg ha k)
        _ = (a * b) ^ k * (K * b ^ t) := by rw [pow_add, mul_pow]; ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hab0 hab).mul_const (K * b ^ t)
  exact tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat

/-! ### The Calvo algebra behind (4.8), (4.9), (4.23) and (4.24) -/

/-- Woodford (2003), eq. (4.6), p. 223 (with the indexation of p. 234): the log-linear law of
motion of a Calvo index, `X_t = α (X_{t−1} + γ ι_t) + (1 − α) x_t`, where `x_t` is the log reset
value and `ι_t` the indexation variable (`γ = 0`: no indexation). -/
def IndexLaw (α γ : ℝ) (Xm1 : Ω → ℝ) (X x ι : ℕ → Ω → ℝ) : Prop :=
  ∀ t, X t = α • (prev Xm1 X t + γ • ι t) + (1 - α) • x t

/-- Woodford (2003), eqs. (4.8) and (4.23), pp. 224 and 234: (indexed) inflation of the index,
`X_t − X_{t−1} − γ ι_t`. -/
def ixInfl (γ : ℝ) (Xm1 : Ω → ℝ) (X ι : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  X t - prev Xm1 X t - γ • ι t

/-- Woodford (2003), p. 224: `ξ > 0` for `0 < α < 1`, `αβ < 1` and `1 + εθ > 0`. -/
theorem xi_pos {α β ε θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hαβ : α * β < 1)
    (hεθ : 0 < 1 + ε * θ) : 0 < calvoXi α β (ε * θ) := by
  unfold calvoXi
  apply div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hα0 hεθ)

/-- Woodford (2003), p. 224 ("manipulations directly analogous to those used in the derivation
of (2.14)"): the scalar identity behind `calvo_pc_iff`. -/
theorem calvo_scalar {α β ε θ γ a b i EX Ei m : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hεθ : 1 + ε * θ ≠ 0) :
    (1 + ε * θ) * ((1 - α)⁻¹ * (a - α * (b + γ * i))
        - α * β * ((1 - α)⁻¹ * (EX - α * (a + γ * Ei))) + α * β * γ * Ei)
      = (1 - α * β) * (m + ε * θ * a) ↔
    a - b - γ * i = calvoXi α β (ε * θ) * (m - a) + β * (EX - a - γ * Ei) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h2 : α ≠ 0 := hα0.ne'
  have key : (1 + ε * θ) * ((1 - α)⁻¹ * (a - α * (b + γ * i))
        - α * β * ((1 - α)⁻¹ * (EX - α * (a + γ * Ei))) + α * β * γ * Ei)
      - (1 - α * β) * (m + ε * θ * a)
      = ((1 + ε * θ) * α / (1 - α)) *
        ((a - b - γ * i) - (calvoXi α β (ε * θ) * (m - a) + β * (EX - a - γ * Ei))) := by
    unfold calvoXi
    field_simp
    ring
  have hK : (1 + ε * θ) * α / (1 - α) ≠ 0 := div_ne_zero (mul_ne_zero hεθ h2) h1
  constructor
  · intro h
    have : ((1 + ε * θ) * α / (1 - α)) *
        ((a - b - γ * i) - (calvoXi α β (ε * θ) * (m - a) + β * (EX - a - γ * Ei))) = 0 := by
      rw [← key, h, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hK)
  · intro h
    have : (1 + ε * θ) * ((1 - α)⁻¹ * (a - α * (b + γ * i))
        - α * β * ((1 - α)⁻¹ * (EX - α * (a + γ * Ei))) + α * β * γ * Ei)
      - (1 - α * β) * (m + ε * θ * a) = 0 := by rw [key, h, sub_self, mul_zero]
    exact sub_eq_zero.mp this

/-- Woodford (2003), eqs. (4.6)–(4.8), pp. 223–224, and (4.23)–(4.24), p. 234 (**the Calvo
inflation equation**): given the index law (4.6) (with indexation), the recursive form of the
reset rule at date `t`,
`(1 + εθ)(x_t − αβ E_t x_{t+1} + αβγ E_t ι_{t+1}) = (1 − αβ)(m_t + εθ X_t)`, holds **iff**
`X_t − X_{t−1} − γι_t = ξ (m_t − X_t) + β E_t(X_{t+1} − X_t − γι_{t+1})`. With
`X = log W`, `m = log μ_w + log V`, `(ε, θ) = (ν, θ_w)`, `γ = 0` this is (4.8). -/
theorem calvo_pc_iff {α β ε θ γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hεθ : 1 + ε * θ ≠ 0)
    {Xm1 : Ω → ℝ} {X x m ι : ℕ → Ω → ℝ} (hlaw : IndexLaw α γ Xm1 X x ι)
    (hXa : 𝔼.Adapted X) (t : ℕ) :
    (1 + ε * θ) • (x t - (α * β) • 𝔼.E t (x (t + 1)) + (α * β * γ) • 𝔼.E t (ι (t + 1)))
        = (1 - α * β) • (m t + (ε * θ) • X t) ↔
      ixInfl γ Xm1 X ι t = calvoXi α β (ε * θ) • (m t - X t) +
        β • 𝔼.E t (ixInfl γ Xm1 X ι (t + 1)) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hx : ∀ s, x s = (1 - α)⁻¹ • (X s - α • (prev Xm1 X s + γ • ι s)) := by
    intro s
    have h := hlaw s
    funext ω
    have hω := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hω ⊢
    field_simp
    linarith
  have hEx : 𝔼.E t (x (t + 1)) =
      (1 - α)⁻¹ • (𝔼.E t (X (t + 1)) - α • (X t + γ • 𝔼.E t (ι (t + 1)))) := by
    rw [hx (t + 1), prev_succ, map_smul, map_sub, map_smul, map_add, map_smul, hXa t]
  have hEπ : 𝔼.E t (ixInfl γ Xm1 X ι (t + 1)) =
      𝔼.E t (X (t + 1)) - X t - γ • 𝔼.E t (ι (t + 1)) := by
    unfold ixInfl
    rw [prev_succ, map_sub, map_sub, map_smul, hXa t]
  rw [hEπ, hEx, hx t]
  unfold ixInfl
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact calvo_scalar hα0 hα1 hεθ

/-- Woodford (2003), eq. (4.7), p. 223: the scalar identity linking the forward-recursive form
of the (indexed) reset rule to its Calvo form. -/
theorem reset_scalar {a e γ x q Ex Eq m X : ℝ} (ha : a < 1) :
    (1 + e) / (1 - a) * (x - γ * q)
        = a * ((1 + e) / (1 - a) * (Ex - γ * Eq)) + (m + e * X - (1 + e) * γ * q) ↔
      (1 + e) * (x - a * Ex + a * γ * (Eq - q)) = (1 - a) * (m + e * X) := by
  have h1 : (1 : ℝ) - a ≠ 0 := by linarith
  have key : ((1 + e) / (1 - a) * (x - γ * q)
        - (a * ((1 + e) / (1 - a) * (Ex - γ * Eq)) + (m + e * X - (1 + e) * γ * q))) * (1 - a)
      = (1 + e) * (x - a * Ex + a * γ * (Eq - q)) - (1 - a) * (m + e * X) := by
    field_simp
    ring
  constructor
  · intro h
    rw [← sub_eq_zero, ← key, h, sub_self, zero_mul]
  · intro h
    have : ((1 + e) / (1 - a) * (x - γ * q)
        - (a * ((1 + e) / (1 - a) * (Ex - γ * Eq)) + (m + e * X - (1 + e) * γ * q))) * (1 - a)
        = 0 := by rw [key, h, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h1)

/-- Woodford (2003), eqs. (4.6)–(4.8), pp. 223–224, and the indexed system (4.23)–(4.24), p. 234
(**(4.6) and (4.7) ⟺ (4.6) and (4.8)**). Let the index obey the law of motion (4.6) with
indexation to `ι_t = q_t − q_{t−1}` (`q_t = log P_{t−1}`; `γ = 0` without indexation). For
processes growing at most like `bˢ` with `αβb < 1` (so nominal levels may drift), the reset
values satisfy the forward-looking rule (4.7),
`x_t − γ q_t = (1 − αβ)/(1 + εθ) ∑ₖ (αβ)ᵏ E_t[m_{t+k} + εθ X_{t+k} − (1 + εθ)γ q_{t+k}]`,
at every date **iff** the inflation equation
`π̃_t = ξ (m_t − X_t) + β E_t π̃_{t+1}` (`π̃_t = X_t − X_{t−1} − γι_t`) holds at every date. -/
theorem reset_sum_iff_pc {α β ε θ γ b M K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hεθ : 0 < 1 + ε * θ) (hb : 0 ≤ b) (hab : α * β * b < 1)
    {Xm1 qm1 : Ω → ℝ} {X x m q : ℕ → Ω → ℝ}
    (hlaw : IndexLaw α γ Xm1 X x (fun t => q t - prev qm1 q t))
    (hXa : 𝔼.Adapted X) (hma : 𝔼.Adapted m) (hqa : 𝔼.Adapted q)
    (hy : ∀ s ω, |m s ω + ε * θ * X s ω - (1 + ε * θ) * γ * q s ω| ≤ M * b ^ s)
    (hx : ∀ s ω, |x s ω - γ * q s ω| ≤ K * b ^ s) :
    (∀ t, x t - γ • q t = ((1 - α * β) / (1 + ε * θ)) •
        𝔼.forwardSeries (α * β) (fun s => m s + (ε * θ) • X s - ((1 + ε * θ) * γ) • q s) t) ↔
      ∀ t, ixInfl γ Xm1 X (fun t => q t - prev qm1 q t) t = calvoXi α β (ε * θ) • (m t - X t)
        + β • 𝔼.E t (ixInfl γ Xm1 X (fun t => q t - prev qm1 q t) (t + 1)) := by
  set y : ℕ → Ω → ℝ := fun s => m s + (ε * θ) • X s - ((1 + ε * θ) * γ) • q s with hydef
  set C : ℝ := (1 + ε * θ) / (1 - α * β) with hC
  set z : ℕ → Ω → ℝ := fun s => C • (x s - γ • q s) with hz
  have hαβ0 : 0 ≤ α * β := mul_nonneg hα0.le hβ0
  have hαβ : α * β < 1 := by nlinarith
  have hC0 : C ≠ 0 := div_ne_zero hεθ.ne' (by linarith)
  have hya : 𝔼.Adapted y := fun s => by
    simp only [hydef, map_sub, map_add, map_smul, hma s, hXa s, hqa s]
  have hyb : ∀ s ω, |y s ω| ≤ M * b ^ s := fun s ω => by
    simpa [hydef, smul_eq_mul] using hy s ω
  have hzb : ∀ s ω, |z s ω| ≤ (|C| * K) * b ^ s := fun s ω => by
    simp only [hz, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hx s ω) (abs_nonneg C)
  have stepA : (∀ t, x t - γ • q t = ((1 - α * β) / (1 + ε * θ)) •
      𝔼.forwardSeries (α * β) y t) ↔ ∀ t, z t = 𝔼.forwardSeries (α * β) y t := by
    refine forall_congr' fun t => ?_
    have hinv : (1 - α * β) / (1 + ε * θ) = C⁻¹ := by rw [hC, inv_div]
    rw [hinv]
    constructor
    · intro h
      simp only [hz]
      rw [h, smul_smul, mul_inv_cancel₀ hC0, one_smul]
    · intro h
      rw [← h]
      simp only [hz]
      rw [smul_smul, inv_mul_cancel₀ hC0, one_smul]
  have stepB : (∀ t, z t = 𝔼.forwardSeries (α * β) y t) ↔
      ∀ t, z t = (α * β) • 𝔼.E t (z (t + 1)) + y t := by
    constructor
    · intro h t
      rw [h t, h (t + 1)]
      exact forwardSeries_solves_growth 𝔼 hαβ0 hb hab hyb hya t
    · intro h t
      exact congrFun (eq_forwardSeries_growth 𝔼 hαβ0 hb hab hyb hya hzb h) t
  have stepC : ∀ t, (z t = (α * β) • 𝔼.E t (z (t + 1)) + y t) ↔
      (1 + ε * θ) • (x t - (α * β) • 𝔼.E t (x (t + 1))
        + (α * β * γ) • 𝔼.E t ((fun t => q t - prev qm1 q t) (t + 1)))
        = (1 - α * β) • (m t + (ε * θ) • X t) := by
    intro t
    have hEz : 𝔼.E t (z (t + 1)) = C • (𝔼.E t (x (t + 1)) - γ • 𝔼.E t (q (t + 1))) := by
      simp only [hz, map_smul, map_sub]
    have hEι : 𝔼.E t ((fun t => q t - prev qm1 q t) (t + 1)) = 𝔼.E t (q (t + 1)) - q t := by
      simp only [prev_succ, map_sub, hqa t]
    rw [hEz, hEι]
    simp only [hz, hydef]
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact reset_scalar hαβ
  rw [stepA, stepB]
  exact forall_congr' fun t => (stepC t).trans
    (calvo_pc_iff 𝔼 hα0 hα1 hεθ.ne' hlaw hXa t)

/-- Woodford (2003), eqs. (4.6)–(4.9), pp. 223–224 (**(4.6)–(4.7) ⟺ (4.8)**, no indexation):
with the index law `X_t = α X_{t−1} + (1 − α) x_t` and processes growing at most like `bˢ`
(`αβb < 1`), the reset rule (4.7)
`x_t = (1 − αβ)/(1 + εθ) ∑ₖ (αβ)ᵏ E_t[m_{t+k} + εθ X_{t+k}]` holds at every date iff
`X_t − X_{t−1} = ξ (m_t − X_t) + β E_t[X_{t+1} − X_t]` does. For wages
(`X = log W`, `m = log μ_w + log V`, `(ε, θ) = (ν, θ_w)`) this is (4.8); for prices
(`X = log P`, `m = log μ_p + log S`, `(ε, θ) = (ω_p, θ_p)`) it is (4.9). -/
theorem eq48_eq49_iff {α β ε θ b M K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hεθ : 0 < 1 + ε * θ) (hb : 0 ≤ b) (hab : α * β * b < 1)
    {Xm1 : Ω → ℝ} {X x m : ℕ → Ω → ℝ}
    (hlaw : ∀ t, X t = α • prev Xm1 X t + (1 - α) • x t)
    (hXa : 𝔼.Adapted X) (hma : 𝔼.Adapted m)
    (hy : ∀ s ω, |m s ω + ε * θ * X s ω| ≤ M * b ^ s) (hx : ∀ s ω, |x s ω| ≤ K * b ^ s) :
    (∀ t, x t = ((1 - α * β) / (1 + ε * θ)) •
        𝔼.forwardSeries (α * β) (fun s => m s + (ε * θ) • X s) t) ↔
      ∀ t, X t - prev Xm1 X t =
        calvoXi α β (ε * θ) • (m t - X t) + β • 𝔼.E t (X (t + 1) - X t) := by
  have hlaw' : IndexLaw α 0 Xm1 X x (fun t => (0 : ℕ → Ω → ℝ) t - prev 0 0 t) := fun t => by
    rw [hlaw t]
    simp
  have key := reset_sum_iff_pc 𝔼 (M := M) (K := K) hα0 hα1 hβ0 hβ1 hεθ hb hab hlaw' hXa hma
    (fun t => by simp) (fun s ω => by simpa using hy s ω) (fun s ω => by simpa using hx s ω)
  simpa [ixInfl] using key

/-- Woodford (2003), eq. (4.8), p. 224: the wage-equation bracket. With `V = v P` (average MRS
in money), `v̂ = log v − log v̄` and the steady state `w̄ = μ_w v̄`,
`log μ_w + log V_t − log W_t = v̂_t + log w̄ + log P_t − log W_t`. -/
theorem wage_gap_eq {lμ lv lvbar lP lW lwbar : ℝ} (hss : lwbar = lμ + lvbar) :
    lμ + (lv + lP) - lW = (lv - lvbar) + lwbar + lP - lW := by
  rw [hss]
  ring

/-- Woodford (2003), eq. (4.9), p. 224 (**corrected E14**): with nominal marginal cost
`S = W/(A f'(h))` (`lMPL = log(A f'(h))`), `ψ̂ = −(lMPL − log f'(h̄))` and the steady state
`P̄ = μ_p S̄`, i.e. `log μ_p + log w̄ − log f'(h̄) = 0`, the price-equation bracket is
`ŝ_t = log μ_p + log S_t − log P_t = log W_t − log P_t − log w̄ + ψ̂_t`. -/
theorem price_gap_eq {lμ lW lP lMPL lMPLbar lwbar ψhat : ℝ} (hss : lμ + lwbar - lMPLbar = 0)
    (hψ : ψhat = -(lMPL - lMPLbar)) :
    lμ + (lW - lMPL) - lP = lW - lP - lwbar + ψhat := by
  rw [hψ]
  linarith

/-- Woodford (2003), p. 224 (**E14**): the printed `ŝ_t = log W_t − log P_t + ψ̂_t` agrees with
the correct `ŝ_t = log W_t − log P_t − log w̄ + ψ̂_t` in every state iff `log w̄ = 0`, i.e. only
when the steady-state real wage is one. -/
theorem printed_s_hat_iff (lwbar : ℝ) :
    (∀ lW lP ψhat : ℝ, lW - lP + ψhat = lW - lP - lwbar + ψhat) ↔ lwbar = 0 := by
  constructor
  · intro h
    have := h 0 0 0
    linarith
  · intro h lW lP ψhat
    rw [h]
    ring

/-- Woodford (2003), p. 224 (**E14, counterexample**): at a steady state (`log W − log P = log w̄`,
`ψ̂ = 0`) with `w̄ ≠ 1` the correct `ŝ` is zero but the printed expression is not. -/
theorem printed_s_hat_counterexample : ∃ lwbar lW lP ψhat : ℝ,
    lW - lP = lwbar ∧ ψhat = 0 ∧ lW - lP - lwbar + ψhat = 0 ∧ lW - lP + ψhat ≠ 0 :=
  ⟨1, 1, 0, 0, by norm_num⟩

/-! ### The MRS and the marginal product of labour: (4.10) as exact derivatives -/

/-- Woodford (2003), eqs. (4.5) and (4.10), pp. 223–225: the log MRS `log V = log v_h − log u_c`
along the symmetric allocation, as a function of log output `lY`, technology `a`, the
labour-supply shift `H̄` and the demand shift `g`: hours are `f⁻¹(Y/A)`, the marginal
disutility is `v_h(h; ξ) = vh(h e^{−H̄})` and the marginal utility is `u_c(Y; ξ) = uc(Y e^{−g})`
(so `H̄` and `g` are the log shifts at constant marginal (dis)utility, as in the book). -/
noncomputable def logMRS (vh uc finv : ℝ → ℝ) (lY a Hs g : ℝ) : ℝ :=
  Real.log (vh (finv (Real.exp (lY - a)) * Real.exp (-Hs))) - Real.log (uc (Real.exp (lY - g)))

/-- Woodford (2003), eq. (4.10), p. 224 (**exact derivative**): along any direction
`(Ŷ, a, H̄, g)` from the steady state `(log Ȳ, 0, 0, 0)` the log MRS has derivative
`ν (φ_h (Ŷ − a) − H̄) + σ⁻¹ (Ŷ − g)`, with `ν = h̄ v_hh/v_h`, `φ_h = Ȳ/(h̄ f'(h̄))`
(`= Ȳ (f⁻¹)'(Ȳ)/h̄`) and `σ⁻¹ = −Ȳ u_cc/u_c`. -/
theorem hasDerivAt_logMRS {vh uc finv : ℝ → ℝ} {vh' uc' dfinv Ybar hbar Yh a Hs g : ℝ}
    (hY : 0 < Ybar) (hh0 : 0 < hbar) (hh : finv Ybar = hbar) (hfinv : HasDerivAt finv dfinv Ybar)
    (hvh : HasDerivAt vh vh' hbar) (hv : 0 < vh hbar) (huc : HasDerivAt uc uc' Ybar)
    (hu : 0 < uc Ybar) :
    HasDerivAt (fun s => logMRS vh uc finv (Real.log Ybar + s * Yh) (s * a) (s * Hs) (s * g))
      (vh' * hbar / vh hbar * (Ybar * dfinv / hbar * (Yh - a) - Hs)
        + -(uc' * Ybar / uc Ybar) * (Yh - g)) 0 := by
  have e1 : HasDerivAt (fun s : ℝ => Real.exp (Real.log Ybar + s * Yh - s * a))
      (Ybar * (Yh - a)) 0 := by
    have i1 : HasDerivAt (fun s : ℝ => Real.log Ybar + s * Yh - s * a) (Yh - a) 0 :=
      (HasDerivAt.sub (HasDerivAt.const_add (Real.log Ybar)
        ((hasDerivAt_id (0 : ℝ)).mul_const Yh)) ((hasDerivAt_id (0 : ℝ)).mul_const a)).congr_deriv
        (by simp)
    exact (HasDerivAt.exp i1).congr_deriv (by simp [Real.exp_log hY])
  have e2 : HasDerivAt (fun s : ℝ => finv (Real.exp (Real.log Ybar + s * Yh - s * a)))
      (dfinv * (Ybar * (Yh - a))) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) hfinv e1 (by simp [Real.exp_log hY])
  have e3 : HasDerivAt (fun s : ℝ => Real.exp (-(s * Hs))) (-Hs) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).mul_const Hs).neg).exp).congr_deriv (by simp)
  have e4 : HasDerivAt
      (fun s : ℝ => finv (Real.exp (Real.log Ybar + s * Yh - s * a)) * Real.exp (-(s * Hs)))
      (dfinv * (Ybar * (Yh - a)) * 1 + hbar * (-Hs)) 0 := by
    exact (e2.mul e3).congr_deriv (by simp [hh, Real.exp_log hY])
  have e5 : HasDerivAt
      (fun s : ℝ => vh (finv (Real.exp (Real.log Ybar + s * Yh - s * a)) * Real.exp (-(s * Hs))))
      (vh' * (dfinv * (Ybar * (Yh - a)) * 1 + hbar * (-Hs))) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) hvh e4 (by simp [hh, Real.exp_log hY])
  have e6 := e5.log (by simpa [hh, Real.exp_log hY] using hv.ne')
  have f1 : HasDerivAt (fun s : ℝ => Real.exp (Real.log Ybar + s * Yh - s * g))
      (Ybar * (Yh - g)) 0 := by
    have i1 : HasDerivAt (fun s : ℝ => Real.log Ybar + s * Yh - s * g) (Yh - g) 0 :=
      (HasDerivAt.sub (HasDerivAt.const_add (Real.log Ybar)
        ((hasDerivAt_id (0 : ℝ)).mul_const Yh)) ((hasDerivAt_id (0 : ℝ)).mul_const g)).congr_deriv
        (by simp)
    exact (HasDerivAt.exp i1).congr_deriv (by simp [Real.exp_log hY])
  have f2 : HasDerivAt (fun s : ℝ => uc (Real.exp (Real.log Ybar + s * Yh - s * g)))
      (uc' * (Ybar * (Yh - g))) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) huc f1 (by simp [Real.exp_log hY])
  have f3 := f2.log (by simpa [Real.exp_log hY] using hu.ne')
  have hfun : (fun s => logMRS vh uc finv (Real.log Ybar + s * Yh) (s * a) (s * Hs) (s * g))
      = fun s => Real.log (vh (finv (Real.exp (Real.log Ybar + s * Yh - s * a))
          * Real.exp (-(s * Hs)))) - Real.log (uc (Real.exp (Real.log Ybar + s * Yh - s * g))) :=
    rfl
  rw [hfun]
  convert HasDerivAt.sub e6 f3 using 1
  simp only [zero_mul, add_zero, sub_zero, neg_zero, Real.exp_zero, mul_one, Real.exp_log hY,
    hh]
  field_simp
  ring

/-- Woodford (2003), p. 224: the log marginal product of labour `log(A f'(f⁻¹(Y/A)))` as a
function of log output and technology. -/
noncomputable def logMPL (df finv : ℝ → ℝ) (lY a : ℝ) : ℝ :=
  a + Real.log (df (finv (Real.exp (lY - a))))

/-- Woodford (2003), p. 225 (**exact derivative**): `ψ̂ = −(log MPL − log f'(h̄))` has derivative
`ω_p Ŷ − (1 + ω_p) a` along `(Ŷ, a)`, with `ω_p = −Ȳ f''(h̄)/f'(h̄)²`
(`= −Ȳ f''(h̄) (f⁻¹)'(Ȳ)/f'(h̄)`), the elasticity of `Ψ(y) = 1/f'(f⁻¹(y))` of (1.9). -/
theorem hasDerivAt_psihat {df finv : ℝ → ℝ} {d2f dfinv Ybar hbar Yh a : ℝ} (hY : 0 < Ybar)
    (hh : finv Ybar = hbar) (hfinv : HasDerivAt finv dfinv Ybar) (hdf : HasDerivAt df d2f hbar)
    (hd : 0 < df hbar) :
    HasDerivAt (fun s => -(logMPL df finv (Real.log Ybar + s * Yh) (s * a)
        - logMPL df finv (Real.log Ybar) 0))
      (-(d2f * Ybar * dfinv / df hbar) * Yh - (1 + -(d2f * Ybar * dfinv / df hbar)) * a) 0 := by
  have e1 : HasDerivAt (fun s : ℝ => Real.exp (Real.log Ybar + s * Yh - s * a))
      (Ybar * (Yh - a)) 0 := by
    have i1 : HasDerivAt (fun s : ℝ => Real.log Ybar + s * Yh - s * a) (Yh - a) 0 :=
      (HasDerivAt.sub (HasDerivAt.const_add (Real.log Ybar)
        ((hasDerivAt_id (0 : ℝ)).mul_const Yh)) ((hasDerivAt_id (0 : ℝ)).mul_const a)).congr_deriv
        (by simp)
    exact (HasDerivAt.exp i1).congr_deriv (by simp [Real.exp_log hY])
  have e2 : HasDerivAt (fun s : ℝ => finv (Real.exp (Real.log Ybar + s * Yh - s * a)))
      (dfinv * (Ybar * (Yh - a))) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) hfinv e1 (by simp [Real.exp_log hY])
  have e3 : HasDerivAt (fun s : ℝ => df (finv (Real.exp (Real.log Ybar + s * Yh - s * a))))
      (d2f * (dfinv * (Ybar * (Yh - a)))) 0 :=
    HasDerivAt.comp_of_eq (0 : ℝ) hdf e2 (by simp [hh, Real.exp_log hY])
  have e4 := e3.log (by simpa [hh, Real.exp_log hY] using hd.ne')
  have e5 := ((((hasDerivAt_id (0 : ℝ)).mul_const a).add e4).sub_const
    (logMPL df finv (Real.log Ybar) 0)).neg
  have hfun : (fun s => -(logMPL df finv (Real.log Ybar + s * Yh) (s * a)
        - logMPL df finv (Real.log Ybar) 0))
      = fun s => -(id s * a + Real.log (df (finv (Real.exp (Real.log Ybar + s * Yh - s * a))))
        - logMPL df finv (Real.log Ybar) 0) := rfl
  rw [hfun]
  convert e5 using 1
  simp only [zero_mul, add_zero, sub_zero, Real.exp_log hY, hh]
  field_simp
  ring

/-- Woodford (2003), p. 225: the natural rate of output `Ŷⁿ`, the output level at which the
desired real wage (`μ_w` times the MRS) equals the real wage firms pay at the desired markup
(`v̂ + ψ̂ = 0`): `Ŷⁿ = ((1 + ω) a + ν H̄ + σ⁻¹ g)/(ω + σ⁻¹)`, `ω = ω_w + ω_p`, `ω_w = ν φ_h`. -/
noncomputable def natOutput (ν φh ωp σi a Hs g : ℝ) : ℝ :=
  ((1 + (ν * φh + ωp)) * a + ν * Hs + σi * g) / (ν * φh + ωp + σi)

/-- Woodford (2003), p. 225 (**alternative form of (4.10)**):
`v̂ = (ω_w + σ⁻¹) Ŷ − (ω + σ⁻¹) Ŷⁿ + (1 + ω_p) a`. -/
theorem vhat_alt {ν φh ωp σi Yh a Hs g : ℝ} (hd : ν * φh + ωp + σi ≠ 0) :
    ν * (φh * (Yh - a) - Hs) + σi * (Yh - g) =
      (ν * φh + σi) * Yh - (ν * φh + ωp + σi) * natOutput ν φh ωp σi a Hs g + (1 + ωp) * a := by
  unfold natOutput
  field_simp
  ring

/-- Woodford (2003), p. 225: `v̂ + ψ̂ = (ω + σ⁻¹)(Ŷ − Ŷⁿ)`, in accordance with (1.15). -/
theorem vhat_add_psihat {ν φh ωp σi Yh a Hs g : ℝ} (hd : ν * φh + ωp + σi ≠ 0) :
    (ν * (φh * (Yh - a) - Hs) + σi * (Yh - g)) + (ωp * Yh - (1 + ωp) * a) =
      (ν * φh + ωp + σi) * (Yh - natOutput ν φh ωp σi a Hs g) := by
  unfold natOutput
  field_simp
  ring

/-- Woodford (2003), p. 225: with `ω + σ⁻¹ > 0`, the flexible-wage real marginal cost
`v̂ + ψ̂` vanishes iff output is at its natural rate. -/
theorem natural_output_iff {ν φh ωp σi Yh a Hs g : ℝ} (hd : 0 < ν * φh + ωp + σi) :
    (ν * (φh * (Yh - a) - Hs) + σi * (Yh - g)) + (ωp * Yh - (1 + ωp) * a) = 0 ↔
      Yh = natOutput ν φh ωp σi a Hs g := by
  rw [vhat_add_psihat hd.ne', mul_eq_zero, sub_eq_zero]
  exact or_iff_right hd.ne'

/-! ### Proposition 3.9 -/

/-- Woodford (2003), p. 225: `κ_w = ξ_w (ω_w + σ⁻¹)`. -/
noncomputable def kappaW (ξw ωw σi : ℝ) : ℝ := ξw * (ωw + σi)

/-- Woodford (2003), p. 225: `κ_p = ξ_p ω_p`. -/
noncomputable def kappaP (ξp ωp : ℝ) : ℝ := ξp * ωp

/-- Woodford (2003), p. 225: the natural real wage
`log wⁿ_t = log w̄ + (1 + ω_p) a_t − ω_p Ŷⁿ_t`. -/
noncomputable def natRealWage (lwbar ωp : ℝ) (a Yn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => lwbar + (1 + ωp) * a t ω - ωp * Yn t ω

/-- Woodford (2003), **Proposition 3.9**, eqs. (4.11)–(4.12), p. 225. If wage and price
inflation obey (4.8) and (4.9), the log MRS deviation is (4.10) in the form
`v̂ = (ω_w + σ⁻¹)Ŷ − (ω + σ⁻¹)Ŷⁿ + (1 + ω_p)a` and `ψ̂ = ω_p Ŷ − (1 + ω_p)a`, then
`π^w_t = κ_w(Ŷ_t − Ŷⁿ_t) + ξ_w(log wⁿ_t + log P_t − log W_t) + β E_t π^w_{t+1}` and
`π_t = κ_p(Ŷ_t − Ŷⁿ_t) + ξ_p(log W_t − log P_t − log wⁿ_t) + β E_t π_{t+1}`. -/
theorem prop_3_9 {β ξw ξp ωw ωp σi lwbar : ℝ} {πw πp lW lP vhat ψhat Yh Yn a : ℕ → Ω → ℝ}
    (h48 : ∀ t, πw t = ξw • (vhat t + (fun _ => lwbar) + lP t - lW t) + β • 𝔼.E t (πw (t + 1)))
    (h49 : ∀ t, πp t = ξp • (ψhat t - (fun _ => lwbar) + lW t - lP t) + β • 𝔼.E t (πp (t + 1)))
    (hv : ∀ t, vhat t = (ωw + σi) • Yh t - (ωw + ωp + σi) • Yn t + (1 + ωp) • a t)
    (hψ : ∀ t, ψhat t = ωp • Yh t - (1 + ωp) • a t) :
    (∀ t, πw t = kappaW ξw ωw σi • (Yh t - Yn t)
      + ξw • (natRealWage lwbar ωp a Yn t + lP t - lW t) + β • 𝔼.E t (πw (t + 1))) ∧
    (∀ t, πp t = kappaP ξp ωp • (Yh t - Yn t)
      + ξp • (lW t - lP t - natRealWage lwbar ωp a Yn t) + β • 𝔼.E t (πp (t + 1))) := by
  constructor
  · intro t
    rw [h48 t, hv t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaW, natRealWage]
    ring
  · intro t
    rw [h49 t, hψ t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaP, natRealWage]
    ring

/-- Woodford (2003), p. 225 (**the natural real wage**): with fully flexible wages and prices
(both brackets of (4.8)–(4.9) zero) output is at its natural rate and the real wage is
`log wⁿ = log w̄ + (1 + ω_p) a − ω_p Ŷⁿ`, and conversely (`ω + σ⁻¹ > 0`). -/
theorem natural_real_wage_iff {ωw ωp σi lwbar Y Yn a lW lP : ℝ} (hω : 0 < ωw + ωp + σi) :
    ((ωw + σi) * Y - (ωw + ωp + σi) * Yn + (1 + ωp) * a + lwbar + lP - lW = 0 ∧
        ωp * Y - (1 + ωp) * a - lwbar + lW - lP = 0) ↔
      (Y = Yn ∧ lW - lP = lwbar + (1 + ωp) * a - ωp * Yn) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hY : (ωw + ωp + σi) * (Y - Yn) = 0 := by linarith
    have hY' : Y = Yn := sub_eq_zero.mp ((mul_eq_zero.mp hY).resolve_left hω.ne')
    subst hY'
    exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, h⟩
    constructor <;> linarith

/-- Woodford (2003), p. 225: `κ_w > 0` when `ξ_w > 0` and `ω_w + σ⁻¹ > 0`. -/
theorem kappaW_pos {ξw ωw σi : ℝ} (hξ : 0 < ξw) (hω : 0 < ωw + σi) : 0 < kappaW ξw ωw σi :=
  mul_pos hξ hω

/-- Woodford (2003), p. 225: `κ_p > 0` when `ξ_p > 0` and `ω_p > 0`. -/
theorem kappaP_pos {ξp ωp : ℝ} (hξ : 0 < ξp) (hω : 0 < ωp) : 0 < kappaP ξp ωp :=
  mul_pos hξ hω

/-! ### The composite inflation index (4.13)–(4.15) -/

/-- Woodford (2003), eq. (4.13), p. 226: `π̄ = (ξ_p⁻¹ π + ξ_w⁻¹ π^w)/(ξ_p⁻¹ + ξ_w⁻¹)`. -/
noncomputable def piBar (ξw ξp : ℝ) (πw πp : Ω → ℝ) : Ω → ℝ :=
  (ξp⁻¹ + ξw⁻¹)⁻¹ • (ξp⁻¹ • πp + ξw⁻¹ • πw)

/-- Woodford (2003), eq. (4.15), p. 226: `κ = (σ⁻¹ + ω)/(ξ_p⁻¹ + ξ_w⁻¹)`. -/
noncomputable def kappaBar (ξw ξp ω σi : ℝ) : ℝ := (σi + ω) / (ξp⁻¹ + ξw⁻¹)

/-- Woodford (2003), eqs. (4.13)–(4.15), p. 226: the weighted average of (4.11) and (4.12)
is the Phillips curve `π̄_t = κ (Ŷ_t − Ŷⁿ_t) + β E_t π̄_{t+1}` (the real-wage terms cancel). -/
theorem eq414 {β ξw ξp ωw ωp σi : ℝ} (hξw : 0 < ξw) (hξp : 0 < ξp)
    {πw πp gap lw lwn : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = kappaW ξw ωw σi • gap t + ξw • (lwn t - lw t) + β • 𝔼.E t (πw (t + 1)))
    (h412 : ∀ t, πp t = kappaP ξp ωp • gap t + ξp • (lw t - lwn t) + β • 𝔼.E t (πp (t + 1)))
    (t : ℕ) :
    piBar ξw ξp (πw t) (πp t) = kappaBar ξw ξp (ωw + ωp) σi • gap t
      + β • 𝔼.E t (piBar ξw ξp (πw (t + 1)) (πp (t + 1))) := by
  have hE : 𝔼.E t (piBar ξw ξp (πw (t + 1)) (πp (t + 1)))
      = (ξp⁻¹ + ξw⁻¹)⁻¹ • (ξp⁻¹ • 𝔼.E t (πp (t + 1)) + ξw⁻¹ • 𝔼.E t (πw (t + 1))) := by
    simp only [piBar, map_smul, map_add]
  rw [hE]
  unfold piBar kappaBar
  rw [h411 t, h412 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaW, kappaP]
  have h1 := hξw.ne'
  have h2 := hξp.ne'
  have h3 : ξp⁻¹ + ξw⁻¹ ≠ 0 := (add_pos (inv_pos.mpr hξp) (inv_pos.mpr hξw)).ne'
  field_simp
  ring

/-- Woodford (2003), eq. (4.15), p. 226: `κ > 0`. -/
theorem kappaBar_pos {ξw ξp ω σi : ℝ} (hξw : 0 < ξw) (hξp : 0 < ξp) (hω : 0 < σi + ω) :
    0 < kappaBar ξw ξp ω σi :=
  div_pos hω (add_pos (inv_pos.mpr hξp) (inv_pos.mpr hξw))

/-- Woodford (2003), p. 226: `κ` is strictly increasing in `ξ_w` (and symmetrically in `ξ_p`). -/
theorem kappaBar_strictMonoOn_xiW {ξp ω σi : ℝ} (hξp : 0 < ξp) (hω : 0 < σi + ω) :
    StrictMonoOn (fun ξw => kappaBar ξw ξp ω σi) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  unfold kappaBar
  refine div_lt_div_of_pos_left hω (add_pos (inv_pos.mpr hξp) (inv_pos.mpr hy)) ?_
  linarith [inv_strictAnti₀ hx hxy]

/-- Woodford (2003), p. 226 (and p. 188): the Calvo slope `ξ` is strictly decreasing in the
stickiness `α ∈ (0, 1)` (for `0 ≤ β ≤ 1`, `1 + εθ > 0`). -/
theorem xi_strictAntiOn {β ε θ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hεθ : 0 < 1 + ε * θ) :
    StrictAntiOn (fun α => calvoXi α β (ε * θ)) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  unfold calvoXi
  rw [div_lt_div_iff₀ (mul_pos hy0 hεθ) (mul_pos hx0 hεθ)]
  have hN : (1 - y) * (1 - y * β) ≤ (1 - x) * (1 - x * β) := by
    apply mul_le_mul (by linarith) (by nlinarith) (by nlinarith) (by linarith)
  have hN0 : 0 < (1 - y) * (1 - y * β) := mul_pos (by linarith) (by nlinarith)
  have h3 : (1 - y) * (1 - y * β) * x < (1 - x) * (1 - x * β) * y :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left hxy hN0) (mul_le_mul_of_nonneg_right hN hy0.le)
  have := mul_lt_mul_of_pos_right h3 hεθ
  linarith

/-- Woodford (2003), p. 226 ("smaller the greater the degree of rigidity"): `κ` is strictly
decreasing in the wage stickiness `α_w ∈ (0, 1)`. -/
theorem kappaBar_strictAntiOn_alphaW {β ν θw ξp ω σi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hνθ : 0 < 1 + ν * θw) (hξp : 0 < ξp) (hω : 0 < σi + ω) :
    StrictAntiOn (fun αw => kappaBar (calvoXi αw β (ν * θw)) ξp ω σi) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have hpos : ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 < calvoXi z β (ν * θw) := fun z hz =>
    xi_pos hz.1 hz.2 (by nlinarith [hz.1, hz.2]) hνθ
  exact kappaBar_strictMonoOn_xiW hξp hω (hpos y hy) (hpos x hx)
    (xi_strictAntiOn hβ0 hβ1 hνθ hx hy hxy)

/-- Woodford (2003), p. 226: as `α → 0⁺`, `ξ → ∞`. -/
theorem tendsto_xi_zero {β ε θ : ℝ} (hεθ : 0 < 1 + ε * θ) :
    Tendsto (fun α => calvoXi α β (ε * θ)) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun α : ℝ => (1 - α) * (1 - α * β) / (1 + ε * θ)) (𝓝[>] 0)
      (𝓝 ((1 - 0) * (1 - 0 * β) / (1 + ε * θ))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact ((continuous_const.sub continuous_id).mul
      (continuous_const.sub (continuous_id.mul continuous_const))).div_const _ |>.tendsto 0
  have h2 : (1 - 0) * (1 - 0 * β) / (1 + ε * θ) = (1 + ε * θ)⁻¹ := by ring
  rw [h2] at h1
  have h3 := h1.pos_mul_atTop (inv_pos.mpr hεθ) tendsto_inv_nhdsGT_zero
  refine h3.congr fun α => ?_
  unfold calvoXi
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Woodford (2003), p. 226: as `α_w → 0⁺` (flexible wages) `κ → ξ_p (σ⁻¹ + ω)`. -/
theorem tendsto_kappaBar_alphaW {β ν θw ξp ω σi : ℝ} (hνθ : 0 < 1 + ν * θw) (hξp : 0 < ξp) :
    Tendsto (fun αw => kappaBar (calvoXi αw β (ν * θw)) ξp ω σi) (𝓝[>] 0)
      (𝓝 (ξp * (σi + ω))) := by
  have h1 : Tendsto (fun αw => (calvoXi αw β (ν * θw))⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_xi_zero hνθ)
  have h2 := (tendsto_const_nhds (x := σi + ω)).div (h1.const_add ξp⁻¹)
    (by rw [add_zero]; exact (inv_pos.mpr hξp).ne')
  rw [add_zero, div_inv_eq_mul, mul_comm (σi + ω) ξp] at h2
  exact h2

/-- Woodford (2003), p. 226: as `α_w → 0⁺` the weight of wage inflation in `π̄` vanishes,
so `π̄` simply measures price inflation. -/
theorem tendsto_weight_alphaW {β ν θw ξp : ℝ} (hνθ : 0 < 1 + ν * θw) (hξp : 0 < ξp) :
    Tendsto (fun αw => (ξp⁻¹ + (calvoXi αw β (ν * θw))⁻¹)⁻¹ * (calvoXi αw β (ν * θw))⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun αw => (calvoXi αw β (ν * θw))⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_xi_zero hνθ)
  have h2 := ((h1.const_add ξp⁻¹).inv₀ (by rw [add_zero]; exact (inv_pos.mpr hξp).ne')).mul h1
  rw [mul_zero] at h2
  exact h2

/-- Woodford (2003), p. 226: the flexible-wage limit `ξ_p (σ⁻¹ + ω)` is the slope (2.13)
`(1 − α_p)(1 − α_pβ)/α_p · ζ` with `ζ = (ω + σ⁻¹)/(1 + ω_pθ_p)` from (1.37). -/
theorem kappaBar_flexible_wages_eq (αp β ωp θp ω σi : ℝ) :
    calvoXi αp β (ωp * θp) * (σi + ω) =
      (1 - αp) * (1 - αp * β) / αp * ((ω + σi) / (1 + ωp * θp)) := by
  unfold calvoXi
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Woodford (2003), p. 226: as `α_p → 0⁺` (only wages sticky) `κ → ξ_w (σ⁻¹ + ω)`. -/
theorem tendsto_kappaBar_alphaP {β ωp θp ξw ω σi : ℝ} (hωθ : 0 < 1 + ωp * θp) (hξw : 0 < ξw) :
    Tendsto (fun αp => kappaBar ξw (calvoXi αp β (ωp * θp)) ω σi) (𝓝[>] 0)
      (𝓝 (ξw * (σi + ω))) := by
  have h1 : Tendsto (fun αp => (calvoXi αp β (ωp * θp))⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_xi_zero hωθ)
  have h2 := (tendsto_const_nhds (x := σi + ω)).div (h1.add_const ξw⁻¹)
    (by rw [zero_add]; exact (inv_pos.mpr hξw).ne')
  rw [zero_add, div_inv_eq_mul, mul_comm (σi + ω) ξw] at h2
  exact h2

/-- Woodford (2003), p. 226: as `α_p → 0⁺` the weight of price inflation in `π̄` vanishes, so
(4.14) becomes a Phillips curve for wages. -/
theorem tendsto_weight_alphaP {β ωp θp ξw : ℝ} (hωθ : 0 < 1 + ωp * θp) (hξw : 0 < ξw) :
    Tendsto (fun αp => ((calvoXi αp β (ωp * θp))⁻¹ + ξw⁻¹)⁻¹ * (calvoXi αp β (ωp * θp))⁻¹)
      (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun αp => (calvoXi αp β (ωp * θp))⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_xi_zero hωθ)
  have h2 := ((h1.add_const ξw⁻¹).inv₀ (by rw [zero_add]; exact (inv_pos.mpr hξw).ne')).mul h1
  rw [mul_zero] at h2
  exact h2

/-! ### Sticky wages and flexible prices: (4.16)–(4.17) and the impulse responses -/

/-- Woodford (2003), p. 227: the bracket of (4.12) is the flexible-price condition: with
`ψ̂ = ω_p Ŷ − (1 + ω_p) a` and the natural real wage, `(κ_p/ξ_p)(Ŷ − Ŷⁿ) + log w − log wⁿ` equals
`ψ̂ − log w̄ + log w`, which vanishes when prices are set at the desired markup. -/
theorem price_bracket_eq (ωp lwbar Yh Yn a lw : ℝ) :
    ωp * (Yh - Yn) + (lw - (lwbar + (1 + ωp) * a - ωp * Yn)) =
      (ωp * Yh - (1 + ωp) * a) - lwbar + lw := by
  ring

/-- Woodford (2003), p. 227: (4.12) says the price bracket equals `ξ_p⁻¹(π_t − β E_t π_{t+1})`,
which tends to zero as `ξ_p → ∞` (purely flexible prices) for a given inflation path
(`tendsto_flexible_bracket`). -/
theorem eq412_bracket {β ξp ωp : ℝ} (hξ : 0 < ξp) {πp gap lw lwn : ℕ → Ω → ℝ}
    (h412 : ∀ t, πp t = kappaP ξp ωp • gap t + ξp • (lw t - lwn t) + β • 𝔼.E t (πp (t + 1)))
    (t : ℕ) : ωp • gap t + (lw t - lwn t) = ξp⁻¹ • (πp t - β • 𝔼.E t (πp (t + 1))) := by
  rw [h412 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaP]
  field_simp
  ring

/-- Woodford (2003), pp. 227 and 231: `ξ⁻¹ x → 0` as `ξ → ∞`, so the brackets of (4.12) and (4.11)
vanish in the limits of flexible prices and flexible wages. -/
theorem tendsto_flexible_bracket (x : ℝ) : Tendsto (fun ξ : ℝ => ξ⁻¹ * x) atTop (𝓝 0) := by
  simpa using tendsto_inv_atTop_zero.mul_const x

/-- Woodford (2003), eq. (4.16), p. 227: with purely flexible prices
(`ψ̂ − log w̄ + log W − log P = 0`), `Ŷ − Ŷⁿ = log Y − log Yⁿ` and nominal GDP
`log 𝒴 = log P + log Y`,
`log W − log P = log wⁿ − ω_p/(1 + ω_p)(log 𝒴 − log W + log wⁿ − log Yⁿ)` and
`log Y = log Yⁿ + (1 + ω_p)⁻¹(log 𝒴 − log W + log wⁿ − log Yⁿ)`. -/
theorem eq416 {ωp lwbar lW lP lY lYn lNom a Yh Yn : ℝ} (hωp : 0 < 1 + ωp)
    (hflex : ωp * Yh - (1 + ωp) * a - lwbar + (lW - lP) = 0)
    (hgap : Yh - Yn = lY - lYn) (hnom : lNom = lP + lY) :
    lW - lP = (lwbar + (1 + ωp) * a - ωp * Yn) - ωp / (1 + ωp) *
        (lNom - lW + (lwbar + (1 + ωp) * a - ωp * Yn) - lYn) ∧
      lY = lYn + 1 / (1 + ωp) * (lNom - lW + (lwbar + (1 + ωp) * a - ωp * Yn) - lYn) := by
  have hne : 1 + ωp ≠ 0 := hωp.ne'
  have h1 : (1 + ωp) * (lW - lP) = (1 + ωp) * (lwbar + (1 + ωp) * a - ωp * Yn)
      - ωp * (lNom - lW + (lwbar + (1 + ωp) * a - ωp * Yn) - lYn) := by
    linear_combination hflex + ωp * hnom - ωp * hgap
  have h2 : (1 + ωp) * lY = (1 + ωp) * lYn
      + (lNom - lW + (lwbar + (1 + ωp) * a - ωp * Yn) - lYn) := by
    linear_combination hflex - ωp * hgap - hnom
  constructor
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2

/-- Woodford (2003), p. 227: substituting (4.16) into (4.11) gives the nominal-wage equation
`π^w_t = κ̂ (log 𝒴_t − log W_t + log wⁿ_t − log Yⁿ_t) + β E_t π^w_{t+1}` with
`κ̂ = ξ_w(ω + σ⁻¹)/(1 + ω_p)` (`= κ/(1 + ω_p)`, `κ` the flexible-price limit of (4.15)). -/
theorem nominal_wage_eq {β ξw ωw ωp σi : ℝ} (hωp : 0 < 1 + ωp)
    {πw gap lw lwn Z : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = kappaW ξw ωw σi • gap t + ξw • (lwn t - lw t) + β • 𝔼.E t (πw (t + 1)))
    (hw : ∀ t, lw t = lwn t - (ωp / (1 + ωp)) • Z t)
    (hy : ∀ t, gap t = (1 / (1 + ωp)) • Z t) (t : ℕ) :
    πw t = (ξw * (ωw + ωp + σi) / (1 + ωp)) • Z t + β • 𝔼.E t (πw (t + 1)) := by
  rw [h411 t, hw t, hy t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaW]
  field_simp
  ring

/-- Woodford (2003), eq. (4.17), p. 228: `κ̂ = (1 − α_w)(1 − α_wβ)/α_w · ζ̃` with
`ζ̃ = (ω + σ⁻¹)/((1 + νθ_w)(1 + ω_p))`. -/
theorem kappaHat_eq (αw β ν θw ω ωp σi : ℝ) :
    calvoXi αw β (ν * θw) * (ω + σi) / (1 + ωp) =
      (1 - αw) * (1 - αw * β) / αw * ((ω + σi) / ((1 + ν * θw) * (1 + ωp))) := by
  unfold calvoXi
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Woodford (2003), p. 228 (**the contract multiplier**, (4.17)): with
`κ̂ = (1 − α)(1 − αβ)/α · ζ̃`, `ζ̃ > 0`, the smaller root `λ` of (2.19) with `κ̂` exceeds `α`
(output effects outlast the wage contracts) **iff** `ζ̃ < 1`. The same holds for prices with
`ζ` of (1.37). -/
theorem lam_gt_alpha_iff {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hζ : 0 < ζ) : α < lam1 β ((1 - α) * (1 - α * β) / α * ζ) ↔ ζ < 1 := by
  set c := (1 - α) * (1 - α * β) / α * ζ with hcdef
  have hαβ : α * β < 1 := by nlinarith
  have hc : 0 < c := mul_pos (div_pos (mul_pos (by linarith) (by linarith)) hα0) hζ
  have hcα : c * α = (1 - α) * (1 - α * β) * ζ := by
    rw [hcdef]
    field_simp
  have hP : β * α ^ 2 - (1 + β + c) * α + 1 = (1 - α) * (1 - α * β) * (1 - ζ) := by
    linear_combination (-1 : ℝ) * hcα
  have hF := quad_factor hβ0 hc α
  have hl2 : α - lam2 β c < 0 := by linarith [one_lt_lam2 hβ0 hc]
  have hN : 0 < (1 - α) * (1 - α * β) := mul_pos (by linarith) (by linarith)
  constructor
  · intro h
    have h1 : 0 < β * (α - lam1 β c) * (α - lam2 β c) :=
      mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hβ0 (by linarith)) hl2
    have h2 : 0 < (1 - α) * (1 - α * β) * (1 - ζ) := by linarith
    have := (pos_iff_pos_of_mul_pos h2).mp hN
    linarith
  · intro h
    have h2 : 0 < β * (α - lam1 β c) * (α - lam2 β c) := by
      have : 0 < (1 - α) * (1 - α * β) * (1 - ζ) := mul_pos hN (by linarith)
      linarith
    by_contra hc'
    push Not at hc'
    have : β * (α - lam1 β c) * (α - lam2 β c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hβ0.le (by linarith)) hl2.le
    linarith

/-- Woodford (2003), eq. (2.16) analogue on p. 227: the impulse response `w̃_k` of
`E_t log W_{t+k}` to a unit innovation in nominal GDP (`(2.15)`, `log W_{−1} = 0`) solves
`w̃_0 − 0 = κ̂(1 − w̃_0) + β(w̃_1 − w̃_0)` and
`w̃_{k+1} − w̃_k = κ̂(1 − w̃_{k+1}) + β(w̃_{k+2} − w̃_{k+1})`. -/
def WtildeEq (β c : ℝ) (w : ℕ → ℝ) : Prop :=
  w 0 - 0 = c * (1 - w 0) + β * (w 1 - w 0) ∧
    ∀ k, w (k + 1) - w k = c * (1 - w (k + 1)) + β * (w (k + 2) - w (k + 1))

/-- Woodford (2003), p. 227: a solution of the `w̃` recurrence gives, for its gap from the new
nominal-GDP level, the second-order equation (4.18)/(4.22) under perfect foresight with
`ℓ₋₁ = 0` and forcing `z_0 = −1`, `z_k = 0` for `k ≥ 1`. -/
theorem wtildeEq_secondOrder {β c : ℝ} {w : ℕ → ℝ} (hw : WtildeEq β c w) :
    SecondOrder perfectForesight β c (fun _ => 0) (fun k _ => if k = 0 then -1 else 0)
      (fun k _ => w k - 1) := by
  intro t
  funext ω
  cases t with
  | zero =>
    have h := hw.1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, prev_zero,
      Pi.neg_apply, ↓reduceIte]
    change β * (w (0 + 1) - 1) - (1 + β + c) * (w 0 - 1) + 0 = -(-1)
    simp only [zero_add]
    linarith
  | succ k =>
    have h := hw.2 k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, prev_succ,
      Pi.neg_apply, Nat.succ_ne_zero, ↓reduceIte]
    change β * (w (k + 1 + 1) - 1) - (1 + β + c) * (w (k + 1) - 1) + (w k - 1) = -0
    linarith

/-- Woodford (2003), p. 227 (**the sticky-wage impulse response**): for `0 < β ≤ 1`, `κ̂ > 0`,
the unique bounded solution of the `w̃` recurrence is `w̃_k = 1 − λ^{k+1}`, with `λ` the smaller
root of `βλ² − (1 + β + κ̂)λ + 1 = 0` (2.19). -/
theorem wtilde_unique {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (w : ℕ → ℝ)
    (hwb : ∃ M, ∀ k, |w k| ≤ M) : WtildeEq β c w ↔ w = fun k => 1 - lam1 β c ^ (k + 1) := by
  set l := lam1 β c with hl
  have hroot : β * l ^ 2 - (1 + β + c) * l + 1 = 0 := charPoly_lam1 hβ hc
  have hcand : WtildeEq β c (fun k => 1 - l ^ (k + 1)) := by
    constructor
    · simp only [zero_add, pow_one]
      linear_combination hroot
    · intro k
      linear_combination l ^ (k + 1) * hroot
  constructor
  · intro hw
    have hpf : ∀ (x : ℕ → Unit → ℝ), perfectForesight.Adapted x := fun _ _ => rfl
    have hb1 : BoundedProc (fun k (_ : Unit) => w k - 1) := by
      obtain ⟨M, hM⟩ := hwb
      exact ⟨M + 1, fun k _ => (abs_sub _ _).trans (by rw [abs_one]; linarith [hM k])⟩
    have hb2 : BoundedProc (fun k (_ : Unit) => (1 - l ^ (k + 1)) - 1) := by
      refine ⟨1, fun k _ => ?_⟩
      have h0 := (lam1_pos hβ hc).le
      have h1 := (lam1_lt_one hβ hc).le
      simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_nonneg (pow_nonneg h0 _)]
      exact pow_le_one₀ h0 h1
    have heq := secondOrder_unique perfectForesight hβ hc (wtildeEq_secondOrder hw)
      (wtildeEq_secondOrder hcand) (hpf _) (hpf _) hb1 hb2
    funext k
    have := congrFun (congrFun heq k) ()
    change w k - 1 = (1 - l ^ (k + 1)) - 1 at this
    linarith
  · rintro rfl
    exact hcand

/-- Woodford (2003), p. 227 (**corrected output response**): with sticky wages and flexible
prices, the response of `log Y_{t+k} − log Yⁿ_{t+k}` is
`(1 + ω_p)⁻¹(1 − w̃_k) = (1 + ω_p)⁻¹ λ^{k+1}`. -/
theorem output_response (ωp l : ℝ) (k : ℕ) :
    (1 + ωp)⁻¹ * (1 - (1 - l ^ (k + 1))) = (1 + ωp)⁻¹ * l ^ (k + 1) := by
  ring

/-- Woodford (2003), p. 227 (**E13**): the printed middle expression `−(1 + ω_p)⁻¹ w̃_k` never
equals the (correct) right-hand side `(1 + ω_p)⁻¹ λ^{k+1}`: they differ by `(1 + ω_p)⁻¹ ≠ 0`. -/
theorem printed_output_response_ne {ωp : ℝ} (hωp : 1 + ωp ≠ 0) (l : ℝ) (k : ℕ) :
    -(1 + ωp)⁻¹ * (1 - l ^ (k + 1)) ≠ (1 + ωp)⁻¹ * l ^ (k + 1) := by
  intro h
  have : (1 + ωp)⁻¹ = 0 := by linear_combination (-1 : ℝ) * h
  exact inv_ne_zero hωp this

/-! ### The nominal anchor: impulse responses under uncertainty -/

/-- Woodford (2003), pp. 227 and 230: the nominal-adjustment equation
`x_t − x_{t−1} = c(y_t − x_t + r_t) + β(E_t x_{t+1} − x_t)` (the nominal-wage equation with
`x = log W`, `y = log 𝒴`, `c = κ̂`; or (4.19) for the price level with `c = κ`), where `r` collects
the exogenous real terms. -/
def AnchorEq (β c : ℝ) (xm1 : Ω → ℝ) (x y r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t - prev xm1 x t = c • (y t - x t + r t) + β • (𝔼.E t (x (t + 1)) - x t)

/-- Woodford (2003), p. 227: the solution `x_t = λ x_{t−1} + (1 − λ) y_t + q_t`, with `q` the
forward sum of the real terms. -/
noncomputable def anchorSol (β c : ℝ) (xm1 : Ω → ℝ) (y q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => lam1 β c • xm1 + (1 - lam1 β c) • y 0 + q 0
  | t + 1 => lam1 β c • anchorSol β c xm1 y q t + (1 - lam1 β c) • y (t + 1) + q (t + 1)

/-- Woodford (2003), p. 227: `x_t = λ x_{t−1} + (1 − λ) y_t + q_t` at every date. -/
theorem anchorSol_eq (β c : ℝ) (xm1 : Ω → ℝ) (y q : ℕ → Ω → ℝ) (t : ℕ) :
    anchorSol β c xm1 y q t = lam1 β c • prev xm1 (anchorSol β c xm1 y q) t
      + (1 - lam1 β c) • y t + q t := by
  cases t <;> rfl

/-- Woodford (2003), eq. (2.15), p. 189: a random walk `y_t = y_{t−1} + ε_t` with adapted,
unforecastable innovations (`E_t ε_{t+1} = 0`) and `y₋₁` known at date 0 is an adapted
martingale: `E_t y_{t+j} = y_t`. -/
theorem randomWalk_E {ym1 : Ω → ℝ} {y ε : ℕ → Ω → ℝ} (hy : ∀ t, y t = prev ym1 y t + ε t)
    (hε : 𝔼.Adapted ε) (hε1 : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (hym1 : 𝔼.E 0 ym1 = ym1) :
    𝔼.Adapted y ∧ ∀ t j, 𝔼.E t (y (t + j)) = y t := by
  have ha : 𝔼.Adapted y := by
    intro t
    induction t with
    | zero => rw [hy 0, prev_zero, map_add, hym1, hε 0]
    | succ t ih =>
      rw [hy (t + 1), prev_succ, map_add, hε (t + 1), ← ih, 𝔼.known (Nat.le_succ t), ih]
  refine ⟨ha, fun t j => ?_⟩
  induction j with
  | zero => exact ha t
  | succ j ih =>
    rw [← add_assoc, hy (t + j + 1), prev_succ, map_add, ih,
      ← 𝔼.tower (Nat.le_add_right t j) (ε (t + j + 1)), hε1 (t + j), map_zero, add_zero]

/-- Woodford (2003), pp. 227 and 230: for adapted `x`, the nominal-adjustment equation holds iff
the gap `g = x − y` solves the second-order equation (4.22) with `g₋₁ = x₋₁ − y₋₁` and forcing
`z_t = c r_t − ε_t`. -/
theorem anchor_iff_secondOrder {β c : ℝ} {xm1 ym1 : Ω → ℝ} {x y ε r : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = prev ym1 y t + ε t) (hEy : ∀ t, 𝔼.E t (y (t + 1)) = y t) :
    AnchorEq 𝔼 β c xm1 x y r ↔
      SecondOrder 𝔼 β c (xm1 - ym1) (fun t => c • r t - ε t) (fun t => x t - y t) := by
  refine forall_congr' fun t => ?_
  have hp : prev (xm1 - ym1) (fun t => x t - y t) t = prev xm1 x t - prev ym1 y t := by
    cases t <;> rfl
  have hEx : 𝔼.E t (x (t + 1) - y (t + 1)) = 𝔼.E t (x (t + 1)) - y t := by
    rw [map_sub, hEy t]
  rw [hp, hEx]
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  have k := congrFun (hy t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at k ⊢
  constructor <;> intro h <;> linarith

/-- Woodford (2003), pp. 227 and 230 (**existence and uniqueness with a nominal anchor**): let
nominal spending be a random walk `y_t = y_{t−1} + ε_t` with bounded adapted unforecastable
innovations (2.15), let `r` be bounded adapted, and `x₋₁`, `y₋₁` known at date 0 with
`x₋₁ − y₋₁` bounded. Then `x_t = λ x_{t−1} + (1 − λ) y_t + q_t`, with
`q_t = β⁻¹ ∑ⱼ λ₂^{−j−1} E_t[c r_{t+j}]`, solves the nominal-adjustment equation, is adapted, keeps
`x − y` bounded, and is the only adapted solution with `x − y` bounded. -/
theorem anchor_existsUnique {β c K : ℝ} (hβ : 0 < β) (hc : 0 < c) {xm1 ym1 : Ω → ℝ}
    {y ε r : ℕ → Ω → ℝ} (hy : ∀ t, y t = prev ym1 y t + ε t) (hε : 𝔼.Adapted ε)
    (hεb : BoundedProc ε) (hε1 : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (hym1 : 𝔼.E 0 ym1 = ym1)
    (hxm1 : 𝔼.E 0 xm1 = xm1) (hK : ∀ ω, |xm1 ω - ym1 ω| ≤ K) (hr : BoundedProc r)
    (hra : 𝔼.Adapted r) :
    let X := anchorSol β c xm1 y (fwdPart 𝔼 β c (fun t => c • r t))
    AnchorEq 𝔼 β c xm1 X y r ∧ 𝔼.Adapted X ∧ BoundedProc (fun t => X t - y t) ∧
      ∀ x, AnchorEq 𝔼 β c xm1 x y r → 𝔼.Adapted x → BoundedProc (fun t => x t - y t) →
        x = X := by
  intro X
  obtain ⟨hya, hEy⟩ := randomWalk_E 𝔼 hy hε hε1 hym1
  have hEy1 : ∀ t, 𝔼.E t (y (t + 1)) = y t := fun t => hEy t 1
  set q := fwdPart 𝔼 β c (fun t => c • r t) with hq
  set z : ℕ → Ω → ℝ := fun t => c • r t - ε t with hz
  have hl2 : 1 < lam2 β c := one_lt_lam2 hβ hc
  have ha : |(lam2 β c)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (lt_trans one_pos hl2)]
    exact inv_lt_one_of_one_lt₀ hl2
  -- the real part `q`
  obtain ⟨Mr, hMr⟩ := hr
  have hu : ∀ t ω, |(fun t => (β * lam2 β c)⁻¹ • (fun t => c • r t) t) t ω|
      ≤ |(β * lam2 β c)⁻¹| * (|c| * Mr) := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMr t ω) (abs_nonneg c))
      (abs_nonneg _)
  have hua : 𝔼.Adapted (fun t => (β * lam2 β c)⁻¹ • (fun t => c • r t) t) := fun t => by
    simp only [map_smul, hra t]
  have hqs := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hu hua
  have hqa := ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hu
  obtain ⟨Bq, hBq⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hu
  -- the factor `e = q − λ ε` is the forward component of the gap equation
  set e : ℕ → Ω → ℝ := fun t => q t - lam1 β c • ε t with he
  have hes : ForwardSolution.Solves 𝔼 (lam2 β c)⁻¹ (fun t => (β * lam2 β c)⁻¹ • z t) e := by
    intro t
    have h1 := hqs t
    have hinv := inv_beta_lam2 hβ hc
    simp only [he, hz, map_sub, map_smul, hε1 t, smul_zero, sub_zero]
    change q t - lam1 β c • ε t = (lam2 β c)⁻¹ • 𝔼.E t (q (t + 1))
      + (β * lam2 β c)⁻¹ • (c • r t - ε t)
    rw [show q t = (lam2 β c)⁻¹ • 𝔼.E t (q (t + 1)) + (β * lam2 β c)⁻¹ • (c • r t) from h1,
      hinv, smul_sub]
    abel
  obtain ⟨Mε, hMε⟩ := hεb
  have heb : BoundedProc e := ⟨Bq + |lam1 β c| * Mε, fun t ω => by
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hBq t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMε t ω) (abs_nonneg _)⟩
  have hzb : BoundedProc z := ⟨|c| * Mr + Mε, fun t ω => by
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add ?_ (hMε t ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMr t ω) (abs_nonneg _)⟩
  have hza : 𝔼.Adapted z := fun t => by simp only [hz, map_sub, map_smul, hra t, hε t]
  obtain ⟨Mz, hMz⟩ := hzb
  have hub : ∀ t ω, |(fun t => (β * lam2 β c)⁻¹ • z t) t ω| ≤ |(β * lam2 β c)⁻¹| * Mz :=
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hMz t ω) (abs_nonneg _)
  have huz : 𝔼.Adapted (fun t => (β * lam2 β c)⁻¹ • z t) := fun t => by
    simp only [map_smul, hza t]
  have heF : e = fwdPart 𝔼 β c z :=
    ForwardSolution.eq_forwardSeries_abs 𝔼 ha hub huz hes heb
  -- the gap of `X` is the solution of (4.22)
  have hm0 : 𝔼.E 0 (xm1 - ym1) = xm1 - ym1 := by rw [map_sub, hxm1, hym1]
  obtain ⟨hsol, hsb, hsa, hsu⟩ := secondOrder_existsUnique 𝔼 hβ hc ⟨Mz, hMz⟩ hza
    (fun ω => by simpa using hK ω) hm0
  have hgap : (fun t => X t - y t) = secondOrderSol 𝔼 β c (xm1 - ym1) z := by
    funext t
    induction t with
    | zero =>
      change lam1 β c • xm1 + (1 - lam1 β c) • y 0 + q 0 - y 0
        = lam1 β c • (xm1 - ym1) + fwdPart 𝔼 β c z 0
      rw [← heF, hy 0, prev_zero]
      simp only [he, smul_sub, sub_smul, one_smul, smul_add]
      abel
    | succ t ih =>
      change lam1 β c • X t + (1 - lam1 β c) • y (t + 1) + q (t + 1) - y (t + 1)
        = lam1 β c • secondOrderSol 𝔼 β c (xm1 - ym1) z t + fwdPart 𝔼 β c z (t + 1)
      rw [← ih, ← heF, hy (t + 1), prev_succ]
      simp only [he, smul_sub, sub_smul, one_smul, smul_add]
      abel
  have hXa : 𝔼.Adapted X := fun t => by
    have h1 : X t = (X t - y t) + y t := by abel
    have h2 := hsa t
    rw [← hgap] at h2
    rw [h1, map_add, h2, hya t]
  refine ⟨?_, hXa, hgap ▸ hsb, ?_⟩
  · rw [anchor_iff_secondOrder 𝔼 hy hEy1, hgap]
    exact hsol
  · intro x hx hxa hxb
    have h1 := (anchor_iff_secondOrder 𝔼 hy hEy1).mp hx
    have h2 := hsu _ h1 hxb (fun t => by rw [map_sub, hxa t, hya t])
    rw [← hgap] at h2
    funext t
    have := congrFun h2 t
    simpa using this

/-- Woodford (2003), pp. 227 and 230: for adapted levels `x` with `π_t = x_t − x_{t−1}`, the
Phillips-curve form `π_t = c(y_t − x_t + r_t) + β E_t π_{t+1}` is the nominal-adjustment
equation `AnchorEq` (the nominal-wage equation of p. 227 with `c = κ̂`, `r = log wⁿ − log Yⁿ`;
(4.19) for the price level with `c = κ`, `r = −log Ȳ − Ŷⁿ + u/κ`). -/
theorem pc_iff_anchor {β c : ℝ} {xm1 : Ω → ℝ} {x y r : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x) :
    (∀ t, x t - prev xm1 x t = c • (y t - x t + r t)
        + β • 𝔼.E t (x (t + 1) - prev xm1 x (t + 1))) ↔ AnchorEq 𝔼 β c xm1 x y r := by
  refine forall_congr' fun t => ?_
  rw [prev_succ, map_sub, hxa t]

/-- Woodford (2003), p. 227: the accumulated response of the real terms,
`R_0 = Q_0`, `R_{k+1} = λ R_k + Q_{k+1}` (with `Q_j = E_t q_{t+j}`). -/
noncomputable def respR (l : ℝ) (Q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => Q 0
  | k + 1 => l • respR l Q k + Q (k + 1)

/-- Woodford (2003), p. 227 (**`w̃_k = 1 − λ^{k+1}` under uncertainty**): along the solution,
`E_t x_{t+k} = λ^{k+1} x_{t−1} + (1 − λ^{k+1}) y_t + R_k`, where `R_k` depends only on the real
terms. Since `y_t = y_{t−1} + ε_t`, the change in `E_t x_{t+k}` made by a unit increase in the
innovation `ε_t` is `1 − λ^{k+1}`. -/
theorem anchor_E_response {β c : ℝ} {xm1 ym1 : Ω → ℝ} {y ε q : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = prev ym1 y t + ε t) (hε : 𝔼.Adapted ε) (hε1 : ∀ t, 𝔼.E t (ε (t + 1)) = 0)
    (hym1 : 𝔼.E 0 ym1 = ym1) (hXa : 𝔼.Adapted (anchorSol β c xm1 y q)) (hqa : 𝔼.Adapted q)
    (t k : ℕ) :
    𝔼.E t (anchorSol β c xm1 y q (t + k)) = lam1 β c ^ (k + 1) • prev xm1 (anchorSol β c xm1 y q) t
      + (1 - lam1 β c ^ (k + 1)) • y t + respR (lam1 β c) (fun j => 𝔼.E t (q (t + j))) k := by
  obtain ⟨_, hEy⟩ := randomWalk_E 𝔼 hy hε hε1 hym1
  set X := anchorSol β c xm1 y q with hX
  set l := lam1 β c with hl
  have hXeq : ∀ s, X s = l • prev xm1 X s + (1 - l) • y s + q s := fun s =>
    anchorSol_eq β c xm1 y q s
  induction k with
  | zero =>
    change 𝔼.E t (X (t + 0)) = l ^ (0 + 1) • prev xm1 X t + (1 - l ^ (0 + 1)) • y t
      + 𝔼.E t (q (t + 0))
    rw [add_zero, hXa t, hqa t, zero_add, pow_one]
    exact hXeq t
  | succ k ih =>
    change 𝔼.E t (X (t + (k + 1))) = l ^ (k + 1 + 1) • prev xm1 X t
      + (1 - l ^ (k + 1 + 1)) • y t
      + (l • respR l (fun j => 𝔼.E t (q (t + j))) k + 𝔼.E t (q (t + (k + 1))))
    rw [show t + (k + 1) = t + k + 1 by omega, hXeq (t + k + 1), prev_succ,
      map_add, map_add, map_smul, map_smul, ih]
    have hy1 : 𝔼.E t (y (t + k + 1)) = y t := by rw [add_assoc]; exact hEy t (k + 1)
    rw [hy1]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Woodford (2003), p. 227: with no real disturbances (`r = 0`) the forward real term vanishes,
and `E_t x_{t+k} = λ^{k+1} x_{t−1} + (1 − λ^{k+1}) y_t`. -/
theorem fwdPart_zero (β c : ℝ) : fwdPart 𝔼 β c (fun _ => 0) = fun _ => 0 := by
  funext t ω
  simp [fwdPart, ExpectationSystem.forwardSeries]

/-! ### The Andersen and Huang–Liu comparisons (pp. 228–230) and E15 -/

/-- Woodford (2003), eq. (4.17), p. 228: `ζ̃ = (ω + σ⁻¹)/((1 + νθ_w)(1 + ω_p))`. -/
noncomputable def zetaTilde (ω σi ν θw ωp : ℝ) : ℝ := (ω + σi) / ((1 + ν * θw) * (1 + ωp))

/-- Woodford (2003), eq. (1.37), p. 167: `ζ = (ω + σ⁻¹)/(1 + ω_pθ_p)` (common labour market). -/
noncomputable def zetaCommon (ω σi ωp θp : ℝ) : ℝ := (ω + σi) / (1 + ωp * θp)

/-- Woodford (2003), eq. (1.35), p. 164: `ζ = (ω + σ⁻¹)/(1 + ωθ_p)` (specific labour markets). -/
noncomputable def zetaSpecific (ω σi θp : ℝ) : ℝ := (ω + σi) / (1 + ω * θp)

/-- Woodford (2003), p. 228 (Andersen's sticky-wage case): `ν = σ⁻¹ = 0` (so `ω_w = νφ_h = 0`)
gives `ζ̃ = ω_p/(1 + ω_p) < 1` for every `ω_p ≥ 0`: a contract multiplier. -/
theorem andersen_wage {ωp φh θw : ℝ} (hωp : 0 ≤ ωp) :
    zetaTilde (0 * φh + ωp) 0 0 θw ωp = ωp / (1 + ωp) ∧ zetaTilde (0 * φh + ωp) 0 0 θw ωp < 1 := by
  have h : zetaTilde (0 * φh + ωp) 0 0 θw ωp = ωp / (1 + ωp) := by
    unfold zetaTilde
    ring_nf
  refine ⟨h, ?_⟩
  rw [h, div_lt_one (by linarith)]
  linarith

/-- Woodford (2003), p. 228: with `ν = 0` (so `ω_w = 0`) but `σ⁻¹ > 0`, the contract multiplier
can be less than one: `ζ̃ > 1` iff `σ⁻¹ > 1`, i.e. `σ < 1`. -/
theorem andersen_contract_multiplier_iff {ωp φh θw σi : ℝ} (hωp : 0 < 1 + ωp) :
    1 < zetaTilde (0 * φh + ωp) σi 0 θw ωp ↔ 1 < σi := by
  unfold zetaTilde
  rw [show (1 + 0 * θw) * (1 + ωp) = 1 + ωp by ring, one_lt_div hωp]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 228 (Andersen's sticky-price case): with a linear technology
(`ω_p = 0`, `φ_h = 1`, hence `ω_w = ν`) and `σ⁻¹ = 0`, (1.37) gives `ζ = ν`. -/
theorem andersen_price (ν θp : ℝ) : zetaCommon (ν * 1 + 0) 0 0 θp = ν := by
  unfold zetaCommon
  ring

/-- Woodford (2003), pp. 228–229: a linear technology `f(h) = a h` (`a > 0`) has
`φ_h = f(h̄)/(h̄ f'(h̄)) = 1` and `ω_p = −f(h̄) f''(h̄)/f'(h̄)² = 0`. -/
theorem linear_production {a hbar : ℝ} (ha : 0 < a) (hh : 0 < hbar) :
    HasDerivAt (fun h => a * h) a hbar ∧ HasDerivAt (fun _ : ℝ => a) 0 hbar ∧
      (a * hbar) / (hbar * a) = 1 ∧ -((a * hbar) * 0) / a ^ 2 = 0 := by
  refine ⟨by simpa using (hasDerivAt_id hbar).const_mul a, hasDerivAt_const _ _, ?_, by simp⟩
  field_simp

/-- Woodford (2003), p. 229 (Huang and Liu): `ω_p = 0`, `φ_h = 1` (so `ω_w = ν`) and `σ = 1`
give `ζ̃ = (1 + ν)/(1 + νθ_w) < 1` (for `ν > 0`, `θ_w > 1`). -/
theorem huang_liu_tilde {ν θw : ℝ} (hν : 0 < ν) (hθ : 1 < θw) :
    zetaTilde (ν * 1 + 0) 1 ν θw 0 = (1 + ν) / (1 + ν * θw) ∧
      zetaTilde (ν * 1 + 0) 1 ν θw 0 < 1 := by
  have h : zetaTilde (ν * 1 + 0) 1 ν θw 0 = (1 + ν) / (1 + ν * θw) := by
    unfold zetaTilde
    ring_nf
  refine ⟨h, ?_⟩
  rw [h, div_lt_one (by nlinarith)]
  nlinarith

/-- Woodford (2003), p. 229 (Huang and Liu): with a common labour market (1.37) and the same
assumptions, `ζ = 1 + ν > 1`. -/
theorem huang_liu_common {ν θp : ℝ} (hν : 0 < ν) :
    zetaCommon (ν * 1 + 0) 1 0 θp = 1 + ν ∧ 1 < zetaCommon (ν * 1 + 0) 1 0 θp := by
  have h : zetaCommon (ν * 1 + 0) 1 0 θp = 1 + ν := by
    unfold zetaCommon
    ring
  exact ⟨h, by rw [h]; linarith⟩

/-- Woodford (2003), pp. 229–230 (Huang and Liu with specific labour markets (1.35)):
`ζ = (1 + ν)/(1 + νθ_p)`, which is at most `ζ̃ = (1 + ν)/(1 + νθ_w)` iff `θ_p ≥ θ_w`. -/
theorem huang_liu_specific_le_iff {ν θw θp : ℝ} (hν : 0 < ν) (hθw : 0 < θw) (hθp : 0 < θp) :
    zetaSpecific (ν * 1 + 0) 1 θp = (1 + ν) / (1 + ν * θp) ∧
      (zetaSpecific (ν * 1 + 0) 1 θp ≤ zetaTilde (ν * 1 + 0) 1 ν θw 0 ↔ θw ≤ θp) := by
  have h1 : zetaSpecific (ν * 1 + 0) 1 θp = (1 + ν) / (1 + ν * θp) := by
    unfold zetaSpecific
    ring_nf
  have h2 : zetaTilde (ν * 1 + 0) 1 ν θw 0 = (1 + ν) / (1 + ν * θw) := by
    unfold zetaTilde
    ring_nf
  refine ⟨h1, ?_⟩
  rw [h1, h2, div_le_div_iff_of_pos_left (by linarith) (by positivity) (by positivity)]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- Woodford (2003), p. 229: with specific labour markets the denominator `1 + ωθ_p` of (1.35)
exceeds the `1 + ω_pθ_p` of (1.37) (`ω = ω_w + ω_p`, `ω_w > 0`), so (1.35) gives the smaller
`ζ` (more strategic complementarity). -/
theorem specific_lt_common {ωw ωp σi θp : ℝ} (hωw : 0 < ωw) (hωp : 0 ≤ ωp) (hθp : 0 < θp)
    (hpos : 0 < ωw + ωp + σi) :
    zetaSpecific (ωw + ωp) σi θp < zetaCommon (ωw + ωp) σi ωp θp := by
  unfold zetaSpecific zetaCommon
  have h0 : 0 ≤ ωp * θp := mul_nonneg hωp hθp.le
  exact div_lt_div_of_pos_left (by linarith) (by linarith) (by nlinarith)

/-- Woodford (2003), p. 229 (**E15, corrected**): if `ν ≥ ω_p ≥ 0`, `ν > 0` and there is at least
as much substitutability among types of labour as among goods, **`θ_w ≥ θ_p`** (`θ_p > 0`),
then `ζ̃ < ζ` of (1.37): wage stickiness gives more persistence than price stickiness. -/
theorem zetaTilde_lt_zetaCommon {ω σi ν θw ωp θp : ℝ} (hν : 0 < ν) (hνωp : ωp ≤ ν)
    (hωp : 0 ≤ ωp) (hθ : θp ≤ θw) (hθp : 0 < θp) (hpos : 0 < ω + σi) :
    zetaTilde ω σi ν θw ωp < zetaCommon ω σi ωp θp := by
  unfold zetaTilde zetaCommon
  have h1 : ωp * θp ≤ ν * θw := mul_le_mul hνωp hθ hθp.le hν.le
  have h0 : 0 ≤ ωp * θp := mul_nonneg hωp hθp.le
  refine div_lt_div_of_pos_left hpos (by linarith) ?_
  rcases hωp.eq_or_lt with h | h
  · subst h
    nlinarith
  · have hw : 0 < 1 + ν * θw := by nlinarith [mul_pos hν (lt_of_lt_of_le hθp hθ)]
    nlinarith [mul_pos h hw]

/-- Woodford (2003), p. 229 (**E15, counterexample**): the printed sufficient condition
"`ω_w ≥ ω_p`" (with `ν` larger than `ω_p`) does not deliver `ζ̃ < ζ`: with `ν = 10`,
`ω_p = 1/10`, `φ_h = 2` (`ω_w = 20 ≥ ω_p`), `σ⁻¹ = 1`, `θ_w = 2` and `θ_p = 1000`,
`ζ̃ ≈ 0.91 > ζ ≈ 0.21`. -/
theorem printed_E15_counterexample : ∃ ν ωp φh θw θp σi : ℝ,
    ωp < ν ∧ 0 < ωp ∧ ωp ≤ ν * φh ∧ 1 < φh ∧ 1 < θw ∧ 1 < θp ∧ 0 < σi ∧
      zetaCommon (ν * φh + ωp) σi ωp θp < zetaTilde (ν * φh + ωp) σi ν θw ωp := by
  refine ⟨10, 1 / 10, 2, 2, 1000, 1, ?_⟩
  norm_num [zetaCommon, zetaTilde]

/-! ### The real wage: (4.18)–(4.22) -/

/-- Woodford (2003), eq. (4.18), p. 230: subtracting (4.12) from (4.11), real-wage inflation
`Δ log w_t = π^w_t − π_t` satisfies
`Δ log w_t = −(ξ_w + ξ_p)(log w_t − log wⁿ_t) + (κ_w − κ_p)(Ŷ_t − Ŷⁿ_t) + β E_t Δ log w_{t+1}`. -/
theorem eq418 {β ξw ξp ωw ωp σi : ℝ} {πw πp gap lw lwn : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = kappaW ξw ωw σi • gap t + ξw • (lwn t - lw t) + β • 𝔼.E t (πw (t + 1)))
    (h412 : ∀ t, πp t = kappaP ξp ωp • gap t + ξp • (lw t - lwn t) + β • 𝔼.E t (πp (t + 1)))
    (t : ℕ) :
    πw t - πp t = -(ξw + ξp) • (lw t - lwn t) + (kappaW ξw ωw σi - kappaP ξp ωp) • gap t
      + β • 𝔼.E t (πw (t + 1) - πp (t + 1)) := by
  rw [h411 t, h412 t, map_sub]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eqs. (4.18) and (4.22), pp. 230–231: for an adapted real wage `ℓ = log w`
with `ℓ₋₁` given, (4.18) at every date is the second-order equation
`β E_t ℓ_{t+1} − (1 + β + ξ) ℓ_t + ℓ_{t−1} = −z_t` with `ξ = ξ_w + ξ_p` and
`z_t = ξ log wⁿ_t + (κ_w − κ_p)(Ŷ_t − Ŷⁿ_t)`. -/
theorem eq418_iff_secondOrder {β ξ κd : ℝ} {lwm1 : Ω → ℝ} {lw lwn gap : ℕ → Ω → ℝ}
    (hla : 𝔼.Adapted lw) :
    (∀ t, lw t - prev lwm1 lw t = -ξ • (lw t - lwn t) + κd • gap t
        + β • 𝔼.E t (lw (t + 1) - lw t)) ↔
      SecondOrder 𝔼 β ξ lwm1 (fun t => ξ • lwn t + κd • gap t) lw := by
  refine forall_congr' fun t => ?_
  rw [map_sub, hla t, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), eq. (4.22), pp. 231–232 (**the real wage under wage and price
stickiness**): for `0 < β`, `ξ_w + ξ_p > 0`, bounded adapted `log wⁿ` and output gap and a
bounded `log w₋₁` known at date 0, (4.18) has exactly one bounded adapted solution, namely
`log w_t = λ₁ log w_{t−1} + β⁻¹ ∑ⱼ λ₂^{−j−1} E_t z_{t+j}`, where `0 < λ₁ < 1 < λ₂` are the roots
of `P(λ) = βλ² − (1 + β + ξ_w + ξ_p)λ + 1`. -/
theorem eq422 {β ξ κd K : ℝ} (hβ : 0 < β) (hξ : 0 < ξ) {lwm1 : Ω → ℝ}
    {lwn gap : ℕ → Ω → ℝ} (hlwn : BoundedProc lwn) (hgap : BoundedProc gap)
    (hlwna : 𝔼.Adapted lwn) (hgapa : 𝔼.Adapted gap) (hK : ∀ ω, |lwm1 ω| ≤ K)
    (hm0 : 𝔼.E 0 lwm1 = lwm1) :
    let ℓ := secondOrderSol 𝔼 β ξ lwm1 (fun t => ξ • lwn t + κd • gap t)
    (∀ t, ℓ t - prev lwm1 ℓ t = -ξ • (ℓ t - lwn t) + κd • gap t + β • 𝔼.E t (ℓ (t + 1) - ℓ t)) ∧
      BoundedProc ℓ ∧ 𝔼.Adapted ℓ ∧
      (∀ lw, (∀ t, lw t - prev lwm1 lw t = -ξ • (lw t - lwn t) + κd • gap t
          + β • 𝔼.E t (lw (t + 1) - lw t)) → BoundedProc lw → 𝔼.Adapted lw → lw = ℓ) ∧
      ∀ t ω, ℓ t ω = lam1 β ξ * prev lwm1 ℓ t ω
        + β⁻¹ * ∑' j, (lam2 β ξ ^ (j + 1))⁻¹ * 𝔼.E t (ξ • lwn (t + j) + κd • gap (t + j)) ω := by
  intro ℓ
  obtain ⟨M1, hM1⟩ := hlwn
  obtain ⟨M2, hM2⟩ := hgap
  have hzb : BoundedProc (fun t => ξ • lwn t + κd • gap t) := ⟨|ξ| * M1 + |κd| * M2, fun t ω => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hM1 t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hM2 t ω) (abs_nonneg _)⟩
  have hza : 𝔼.Adapted (fun t => ξ • lwn t + κd • gap t) := fun t => by
    simp only [map_add, map_smul, hlwna t, hgapa t]
  obtain ⟨hs, hb, ha, hu⟩ := secondOrder_existsUnique 𝔼 hβ hξ hzb hza hK hm0
  refine ⟨(eq418_iff_secondOrder 𝔼 ha).mpr hs, hb, ha,
    fun lw h hlb hla => hu lw ((eq418_iff_secondOrder 𝔼 hla).mp h) hlb hla, fun t ω => ?_⟩
  have h := congrFun (secondOrderSol_eq 𝔼 β ξ lwm1 (fun t => ξ • lwn t + κd • gap t) t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  change secondOrderSol 𝔼 β ξ lwm1 (fun t => ξ • lwn t + κd • gap t) t ω
    = lam1 β ξ * prev lwm1 (secondOrderSol 𝔼 β ξ lwm1 (fun t => ξ • lwn t + κd • gap t)) t ω
      + β⁻¹ * ∑' j, (lam2 β ξ ^ (j + 1))⁻¹ * 𝔼.E t (ξ • lwn (t + j) + κd • gap (t + j)) ω
  rw [h, fwdPart_apply]

/-- Woodford (2003), p. 230 (**the real wage is independent of monetary policy when
`κ_w = κ_p`**): then output drops out of (4.18), and the bounded adapted solutions for any two
output-gap paths coincide; the real wage `w̄` is determined by `wⁿ` and `w₋₁` alone. -/
theorem realWage_indep_of_output {β ξ : ℝ} (hβ : 0 < β) (hξ : 0 < ξ) {lwm1 : Ω → ℝ}
    {lwn gap₁ gap₂ lw₁ lw₂ : ℕ → Ω → ℝ}
    (h₁ : ∀ t, lw₁ t - prev lwm1 lw₁ t = -ξ • (lw₁ t - lwn t) + (0 : ℝ) • gap₁ t
      + β • 𝔼.E t (lw₁ (t + 1) - lw₁ t))
    (h₂ : ∀ t, lw₂ t - prev lwm1 lw₂ t = -ξ • (lw₂ t - lwn t) + (0 : ℝ) • gap₂ t
      + β • 𝔼.E t (lw₂ (t + 1) - lw₂ t))
    (hb₁ : BoundedProc lw₁) (hb₂ : BoundedProc lw₂) (ha₁ : 𝔼.Adapted lw₁)
    (ha₂ : 𝔼.Adapted lw₂) : lw₁ = lw₂ := by
  have s₁ := (eq418_iff_secondOrder 𝔼 ha₁).mp h₁
  have s₂ := (eq418_iff_secondOrder 𝔼 ha₂).mp h₂
  have hz : (fun t => ξ • lwn t + (0 : ℝ) • gap₂ t) = fun t => ξ • lwn t + (0 : ℝ) • gap₁ t := by
    simp only [zero_smul]
  rw [hz] at s₂
  exact secondOrder_unique 𝔼 hβ hξ s₁ s₂ ha₁ ha₂ hb₁ hb₂

/-- Woodford (2003), eqs. (4.19)–(4.20), p. 230 (**corrected E12**): with `κ_w = κ_p = κ` and the
real wage `w̄` solving (4.18), (4.12) becomes
`π_t = κ (Ŷ_t − Ŷⁿ_t) + β E_t π_{t+1} + u_t` with `u_t = ξ_p (log w̄_t − log wⁿ_t)`. -/
theorem eq419 {β κ ξp : ℝ} {πp gap wbar lwn : ℕ → Ω → ℝ}
    (h412 : ∀ t, πp t = κ • gap t + ξp • (wbar t - lwn t) + β • 𝔼.E t (πp (t + 1))) (t : ℕ) :
    πp t = κ • gap t + β • 𝔼.E t (πp (t + 1)) + ξp • (wbar t - lwn t) := by
  rw [h412 t]
  abel

/-- Woodford (2003), p. 230 (**E12**): given the correct (4.19), the printed version (with
`E_t π_{t+1}` in place of `β E_t π_{t+1}`) holds at `t` iff `(1 − β) E_t π_{t+1} = 0`. -/
theorem printed_eq419_iff {β κ : ℝ} {πp gap u : ℕ → Ω → ℝ}
    (h419 : ∀ t, πp t = κ • gap t + β • 𝔼.E t (πp (t + 1)) + u t) (t : ℕ) :
    πp t = κ • gap t + 𝔼.E t (πp (t + 1)) + u t ↔ (1 - β) • 𝔼.E t (πp (t + 1)) = 0 := by
  rw [h419 t, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 230 (**E12, counterexample**): under perfect foresight with `β = 1/2`,
`κ_w = κ_p = κ = 1`, `ξ_w = ξ_p = 1`, constant inflation `π = π^w = 1`, output gap `1/2` and
`log w = log wⁿ = 0`, (4.11), (4.12) and the corrected (4.19) hold but the printed (4.19) fails. -/
theorem printed_eq419_counterexample :
    ∃ (β κ ξw ξp : ℝ) (πw πp gap lw lwn : ℕ → Unit → ℝ),
      0 < β ∧ β < 1 ∧ 0 < κ ∧ 0 < ξw ∧ 0 < ξp ∧
      (∀ t, πw t = κ • gap t + ξw • (lwn t - lw t) + β • perfectForesight.E t (πw (t + 1))) ∧
      (∀ t, πp t = κ • gap t + ξp • (lw t - lwn t) + β • perfectForesight.E t (πp (t + 1))) ∧
      (∀ t, πp t = κ • gap t + β • perfectForesight.E t (πp (t + 1)) + ξp • (lw t - lwn t)) ∧
      ¬ ∀ t, πp t = κ • gap t + perfectForesight.E t (πp (t + 1)) + ξp • (lw t - lwn t) := by
  refine ⟨1 / 2, 1, 1, 1, fun _ _ => 1, fun _ _ => 1, fun _ _ => 1 / 2, fun _ _ => 0,
    fun _ _ => 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro t; funext ω; change (1 : ℝ) = 1 * (1 / 2) + 1 * (0 - 0) + 1 / 2 * 1; norm_num
  · intro t; funext ω; change (1 : ℝ) = 1 * (1 / 2) + 1 * (0 - 0) + 1 / 2 * 1; norm_num
  · intro t; funext ω; change (1 : ℝ) = 1 * (1 / 2) + 1 / 2 * 1 + 1 * (0 - 0); norm_num
  · intro h
    have := congrFun (h 0) ()
    change (1 : ℝ) = 1 * (1 / 2) + 1 + 1 * (0 - 0) at this
    norm_num at this

/-- Woodford (2003), p. 231: with sticky wages the slope `κ = ξ_p ω_p` is smaller than the
flexible-wage slope `ξ_p(ω + σ⁻¹)` (`ω = ω_w + ω_p`, `ω_w + σ⁻¹ > 0`, `ξ_p > 0`). -/
theorem kappa_sticky_lt_flexible {ξp ωw ωp σi : ℝ} (hξ : 0 < ξp) (hω : 0 < ωw + σi) :
    ξp * ωp < ξp * (ωw + ωp + σi) := by
  nlinarith

/-- Woodford (2003), p. 231 ("both larger and more persistent output effects"): a smaller slope
gives a larger root, so the output response `λ^{k+1}` is larger at every horizon. -/
theorem output_response_larger {β c₁ c₂ : ℝ} (hβ : 0 < β) (hc₁ : 0 < c₁) (h : c₁ < c₂) (k : ℕ) :
    lam1 β c₂ ^ (k + 1) < lam1 β c₁ ^ (k + 1) :=
  pow_lt_pow_left₀ (lam1_strictAntiOn hβ hc₁ (lt_trans hc₁ h) h) (lam1_pos hβ (hc₁.trans h)).le
    (Nat.succ_ne_zero k)

/-- Woodford (2003), eq. (4.21), p. 231: (4.11) says its bracket
`(ω_w + σ⁻¹)(Ŷ − Ŷⁿ) + log wⁿ − log w` equals `ξ_w⁻¹(π^w_t − β E_t π^w_{t+1})`, which vanishes as
`ξ_w → ∞` (flexible wages, `tendsto_flexible_bracket`). -/
theorem eq411_bracket {β ξw ωw σi : ℝ} (hξ : 0 < ξw) {πw gap lw lwn : ℕ → Ω → ℝ}
    (h411 : ∀ t, πw t = kappaW ξw ωw σi • gap t + ξw • (lwn t - lw t) + β • 𝔼.E t (πw (t + 1)))
    (t : ℕ) : (ωw + σi) • gap t + (lwn t - lw t) = ξw⁻¹ • (πw t - β • 𝔼.E t (πw (t + 1))) := by
  rw [h411 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaW]
  field_simp
  ring

/-- Woodford (2003), eq. (4.21), p. 231: with flexible wages (bracket of (4.11) zero),
`log W − log P = log wⁿ + (ω_w + σ⁻¹)(Ŷ − Ŷⁿ)`: real wages move with output. -/
theorem eq421 (ωw σi g lwn lw : ℝ) :
    (ωw + σi) * g + (lwn - lw) = 0 ↔ lw = lwn + (ωw + σi) * g := by
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 231: `ω > ν`, since `ω = νφ_h + ω_p` with `φ_h > 1`, `ν > 0`,
`ω_p ≥ 0`. -/
theorem omega_gt_nu {ν φh ωp : ℝ} (hν : 0 < ν) (hφ : 1 < φh) (hωp : 0 ≤ ωp) :
    ν < ν * φh + ωp := by
  nlinarith

/-- Woodford (2003), p. 224: `φ_h = f(h̄)/(h̄ f'(h̄)) > 1` for a production function with
`f(0) ≥ 0`, differentiable on `[0, h̄]` with strictly decreasing marginal product `f' > 0`
(strict concavity), by the mean value theorem. -/
theorem phiH_gt_one {f df : ℝ → ℝ} {hbar : ℝ} (hh : 0 < hbar) (hf0 : 0 ≤ f 0)
    (hd : ∀ x ∈ Set.Icc 0 hbar, HasDerivAt f (df x) x)
    (hanti : StrictAntiOn df (Set.Icc 0 hbar)) (hdf : 0 < df hbar) :
    1 < f hbar / (hbar * df hbar) := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f df hh
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  have hlt : df hbar < df c :=
    hanti (Set.Ioo_subset_Icc_self hc) (Set.right_mem_Icc.mpr hh.le) hc.2
  rw [sub_zero, eq_div_iff hh.ne'] at hslope
  rw [one_lt_div (mul_pos hh hdf)]
  nlinarith

/-- Woodford (2003), p. 231 ("it is possible to arrange that `κ_w = κ_p` simply by assigning an
appropriate value to `α_w`"): if `ω_p > 0` (so `κ_p > 0`), there is exactly one
`α_w ∈ (0, 1)` with `κ_w = κ_p`, namely the smaller root of
`βα² − (1 + β + C)α + 1` with `C = ξ_pω_p(1 + νθ_w)/(ω_w + σ⁻¹)`. -/
theorem alphaW_existsUnique {β ν θw ωw σi ξp ωp : ℝ} (hβ0 : 0 < β) (hνθ : 0 < 1 + ν * θw)
    (hω : 0 < ωw + σi) (hξp : 0 < ξp) (hωp : 0 < ωp) :
    ∃! αw, αw ∈ Set.Ioo (0 : ℝ) 1 ∧ kappaW (calvoXi αw β (ν * θw)) ωw σi = kappaP ξp ωp := by
  set C := ξp * ωp * (1 + ν * θw) / (ωw + σi) with hC
  have hC0 : 0 < C := div_pos (mul_pos (mul_pos hξp hωp) hνθ) hω
  have key : ∀ α, 0 < α → (kappaW (calvoXi α β (ν * θw)) ωw σi = kappaP ξp ωp ↔
      β * α ^ 2 - (1 + β + C) * α + 1 = 0) := by
    intro α hα
    have e1 : kappaW (calvoXi α β (ν * θw)) ωw σi - kappaP ξp ωp =
        (ωw + σi) / (α * (1 + ν * θw)) * (β * α ^ 2 - (1 + β + C) * α + 1) := by
      unfold kappaW kappaP calvoXi
      rw [hC]
      field_simp
      ring
    have hne : (ωw + σi) / (α * (1 + ν * θw)) ≠ 0 :=
      div_ne_zero hω.ne' (mul_pos hα hνθ).ne'
    rw [← sub_eq_zero, e1, mul_eq_zero]
    exact or_iff_right hne
  refine ⟨lam1 β C, ⟨⟨lam1_pos hβ0 hC0, lam1_lt_one hβ0 hC0⟩,
    (key _ (lam1_pos hβ0 hC0)).mpr (charPoly_lam1 hβ0 hC0)⟩, fun α ⟨hα, h⟩ => ?_⟩
  have hP := (key α hα.1).mp h
  rw [quad_factor hβ0 hC0] at hP
  have h2 : α - lam2 β C ≠ 0 := by linarith [one_lt_lam2 hβ0 hC0, hα.2]
  have := (mul_eq_zero.mp hP).resolve_right h2
  have := (mul_eq_zero.mp this).resolve_left hβ0.ne'
  linarith

/-- Woodford (2003), p. 231 (**imprecision**): "for any values of the other parameters" needs
`ω_p > 0`; with a linear technology (`ω_p = 0`, the Huang–Liu case) `κ_p = 0 < κ_w` for every
`α_w ∈ (0, 1)`, so no degree of wage stickiness equates them. -/
theorem alphaW_none_of_linear {β ν θw ωw σi ξp : ℝ} (hβ1 : β ≤ 1) (hνθ : 0 < 1 + ν * θw)
    (hω : 0 < ωw + σi) :
    ∀ αw ∈ Set.Ioo (0 : ℝ) 1, kappaW (calvoXi αw β (ν * θw)) ωw σi ≠ kappaP ξp 0 := by
  intro αw hα
  have hαβ : αw * β < 1 := by nlinarith [hα.1, hα.2]
  have h := kappaW_pos (xi_pos hα.1 hα.2 hαβ hνθ) hω
  unfold kappaP
  rw [mul_zero]
  exact h.ne'

/-- Woodford (2003), p. 233 and footnote 77 (**the sign of the real-wage response**): the
response `ℓ̃` of the real wage to a monetary disturbance solves (4.18) with `ℓ̃₋₁ = 0` and forcing
`(κ_w − κ_p) ŷ`, where `ŷ` is the output response. It equals `(κ_w − κ_p) L` with `L ≥ 0`
whenever `ŷ ≥ 0`: none when `κ_w = κ_p`, procyclical when `κ_w > κ_p`, countercyclical when
wages are stickier (`κ_w < κ_p`). -/
theorem realWage_response_sign {β ξ κd : ℝ} (hβ : 0 < β) (hξ : 0 < ξ) {yhat : ℕ → Ω → ℝ}
    (hy0 : ∀ t ω, 0 ≤ yhat t ω) :
    (∀ t, secondOrderSol 𝔼 β ξ 0 (fun s => κd • yhat s) t = κd • secondOrderSol 𝔼 β ξ 0 yhat t) ∧
      ∀ t ω, 0 ≤ secondOrderSol 𝔼 β ξ 0 yhat t ω :=
  ⟨fun t => secondOrderSol_smul 𝔼 β ξ κd yhat t,
    fun t ω => secondOrderSol_nonneg 𝔼 hβ hξ hy0 (fun _ => le_rfl) t ω⟩

/-- Woodford (2003), p. 233: with `κ_w = κ_p`, the natural real wage `w = wⁿ` solves (4.18) iff
`Δ log wⁿ_t = β E_t Δ log wⁿ_{t+1}` at every date. -/
theorem natural_real_wage_solves_iff {β ξ : ℝ} {lwnm1 : Ω → ℝ} {lwn gap : ℕ → Ω → ℝ} :
    (∀ t, lwn t - prev lwnm1 lwn t = -ξ • (lwn t - lwn t) + (0 : ℝ) • gap t
        + β • 𝔼.E t (lwn (t + 1) - lwn t)) ↔
      ∀ t, lwn t - prev lwnm1 lwn t = β • 𝔼.E t (lwn (t + 1) - prev lwnm1 lwn (t + 1)) := by
  refine forall_congr' fun t => ?_
  simp only [sub_self, smul_zero, zero_smul, zero_add, prev_succ]

/-- Woodford (2003), p. 233: if `wⁿ` is bounded (e.g. stationary) and
`Δ log wⁿ_t = β E_t Δ log wⁿ_{t+1}` at every date (`0 ≤ β < 1`), then `wⁿ` is constant: the
condition for `w = wⁿ` holds only if real disturbances never move the natural real wage. -/
theorem bounded_natural_wage_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {lwnm1 : Ω → ℝ}
    {lwn : ℕ → Ω → ℝ} (hb : BoundedProc lwn) {K : ℝ} (hK : ∀ ω, |lwnm1 ω| ≤ K)
    (h : ∀ t, lwn t - prev lwnm1 lwn t = β • 𝔼.E t (lwn (t + 1) - prev lwnm1 lwn (t + 1))) :
    ∀ t, lwn t = lwnm1 := by
  set d : ℕ → Ω → ℝ := fun t => lwn t - prev lwnm1 lwn t with hd
  obtain ⟨M, hM⟩ := hb
  have hdb : BoundedProc d := ⟨M + max M K, fun t ω => by
    simp only [hd, Pi.sub_apply]
    refine (abs_sub _ _).trans (add_le_add (hM t ω) ?_)
    cases t with
    | zero => exact (hK ω).trans (le_max_right _ _)
    | succ t => exact (hM t ω).trans (le_max_left _ _)⟩
  have hβa : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have hd0 : d = 0 :=
    𝔼.forward_unique hβa (fun t => by rw [add_zero]; exact h t) (fun t => by simp)
      hdb ⟨0, fun _ _ => by simp⟩
  intro t
  induction t with
  | zero =>
    have := congrFun hd0 0
    simp only [hd, prev_zero, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  | succ t ih =>
    have := congrFun hd0 (t + 1)
    simp only [hd, prev_succ, Pi.zero_apply] at this
    rw [sub_eq_zero.mp this, ih]

/-! ### The flexible limit of (4.22) -/

/-- Woodford (2003), eq. (4.22), p. 231: the forward sum of a process bounded by `M` with
`0 ≤ a < 1` is bounded by `M/(1 − a)`. -/
theorem abs_forwardSeries_le {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) : |𝔼.forwardSeries a u t ω| ≤ M / (1 - a) := by
  have hg : HasSum (fun k : ℕ => M * a ^ k) (M / (1 - a)) := by
    have := (hasSum_geometric_of_lt_one ha0 ha1).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun k => a ^ k * 𝔼.E t (u (t + k)) ω) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 k), mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg ha0 k)
  simpa [ExpectationSystem.forwardSeries, Real.norm_eq_abs] using this

/-- Woodford (2003), p. 232: the bound `λ₁ c M/(1 − λ₂⁻¹)` on the forward component of (4.22)
when the forcing is `c ẑ` with `|ẑ| ≤ M`. -/
noncomputable def flexBF (β M c : ℝ) : ℝ := lam1 β c * c * M / (1 - (lam2 β c)⁻¹)

/-- Woodford (2003), p. 232: the explicit error bound in the flexible limit of (4.22),
`λ₁(K + BF/(1 − λ₁)) + λ₂⁻¹ BF + 2|λ₁c − 1| M`. -/
noncomputable def flexBound (β K M c : ℝ) : ℝ :=
  lam1 β c * (K + flexBF β M c / (1 - lam1 β c)) + (lam2 β c)⁻¹ * flexBF β M c
    + 2 * |lam1 β c * c - 1| * M

/-- Woodford (2003), p. 232 (**the flexible limit of (4.22), explicit bound**): write the forcing
of (4.18) as `z = c ẑ` (`c = ξ_w + ξ_p`, `ẑ = log wⁿ + ((κ_w − κ_p)/c)(Ŷ − Ŷⁿ)`). For any bounded
adapted `ẑ` with `|ẑ| ≤ M` and `|ℓ₋₁| ≤ K`, the unique bounded solution (4.22) satisfies
`|ℓ_t − ẑ_t| ≤ flexBound` and `|ℓ_t − λ₁ z_t| ≤ flexBound` at every date and state. -/
theorem secondOrder_flexible_bound {β c K M : ℝ} (hβ : 0 < β) (hc : 0 < c) (hK : 0 ≤ K)
    (hM : 0 ≤ M) {zh : ℕ → Ω → ℝ} (hz : ∀ t ω, |zh t ω| ≤ M) (hza : 𝔼.Adapted zh)
    {ℓm1 : Ω → ℝ} (hm : ∀ ω, |ℓm1 ω| ≤ K) (t : ℕ) (ω : Ω) :
    |secondOrderSol 𝔼 β c ℓm1 (fun t => c • zh t) t ω - zh t ω| ≤ flexBound β K M c ∧
      |secondOrderSol 𝔼 β c ℓm1 (fun t => c • zh t) t ω - lam1 β c * (c * zh t ω)|
        ≤ flexBound β K M c := by
  set l := lam1 β c with hl
  set a := (lam2 β c)⁻¹ with ha
  have hl0 := lam1_pos hβ hc
  have hl1 := lam1_lt_one hβ hc
  have hl2 := one_lt_lam2 hβ hc
  have ha0 : 0 ≤ a := (inv_pos.mpr (lt_trans one_pos hl2)).le
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hl2
  have haa : |a| < 1 := by rwa [abs_of_nonneg ha0]
  set u : ℕ → Ω → ℝ := fun t => (β * lam2 β c)⁻¹ • (fun t => c • zh t) t with hu
  have huv : ∀ t ω, u t ω = l * c * zh t ω := fun t ω => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, inv_beta_lam2 hβ hc, hl]
    ring
  have hub : ∀ t ω, |u t ω| ≤ l * c * M := fun t ω => by
    rw [huv, abs_mul, abs_of_pos (mul_pos hl0 hc)]
    exact mul_le_mul_of_nonneg_left (hz t ω) (mul_pos hl0 hc).le
  have hua : 𝔼.Adapted u := fun t => by simp only [hu, map_smul, hza t]
  set BF := flexBF β M c with hBF
  have hBFv : BF = l * c * M / (1 - a) := rfl
  have hBF0 : 0 ≤ BF := by rw [hBFv]; exact div_nonneg (by positivity) (by linarith)
  have hFb : ∀ t ω, |𝔼.forwardSeries a u t ω| ≤ BF := fun t ω => by
    rw [hBFv]; exact abs_forwardSeries_le 𝔼 ha0 ha1 hub t ω
  have hFs := ForwardSolution.forwardSeries_solves_abs 𝔼 haa hub hua
  have hFu : ∀ t ω, |𝔼.forwardSeries a u t ω - l * c * zh t ω| ≤ a * BF := fun t ω => by
    have h := congrFun (hFs t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [h, huv, add_sub_cancel_right, abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hFb (t + 1)) t ω) ha0
  set B := K + BF / (1 - l) with hB
  have hstep : l * B + BF ≤ B := by
    have hl' : (1 : ℝ) - l ≠ 0 := by linarith
    have : BF = (1 - l) * (BF / (1 - l)) := by field_simp
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - l) hK]
  have hKB : K ≤ B := by
    have : 0 ≤ BF / (1 - l) := div_nonneg hBF0 (by linarith)
    linarith
  set ℓ := secondOrderSol 𝔼 β c ℓm1 (fun t => c • zh t) with hℓ
  have hrec : ∀ s ω, ℓ s ω = l * prev ℓm1 ℓ s ω + 𝔼.forwardSeries a u s ω := fun s ω => by
    have := congrFun (secondOrderSol_eq 𝔼 β c ℓm1 (fun t => c • zh t) s) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hℓb : ∀ s ω, |ℓ s ω| ≤ B := by
    intro s
    induction s with
    | zero =>
      intro ω
      rw [hrec, prev_zero]
      calc |l * ℓm1 ω + 𝔼.forwardSeries a u 0 ω| ≤ l * B + BF := by
            refine (abs_add_le _ _).trans (add_le_add ?_ (hFb 0 ω))
            rw [abs_mul, abs_of_pos hl0]
            exact mul_le_mul_of_nonneg_left ((hm ω).trans hKB) hl0.le
        _ ≤ B := hstep
    | succ s ih =>
      intro ω
      rw [hrec, prev_succ]
      calc |l * ℓ s ω + 𝔼.forwardSeries a u (s + 1) ω| ≤ l * B + BF := by
            refine (abs_add_le _ _).trans (add_le_add ?_ (hFb (s + 1) ω))
            rw [abs_mul, abs_of_pos hl0]
            exact mul_le_mul_of_nonneg_left (ih ω) hl0.le
        _ ≤ B := hstep
  have hpb : |prev ℓm1 ℓ t ω| ≤ B := by
    cases t with
    | zero => exact (hm ω).trans hKB
    | succ s => exact hℓb s ω
  have h1 : |l * prev ℓm1 ℓ t ω| ≤ l * B := by
    rw [abs_mul, abs_of_pos hl0]
    exact mul_le_mul_of_nonneg_left hpb hl0.le
  have h3 : |(l * c - 1) * zh t ω| ≤ |l * c - 1| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hz t ω) (abs_nonneg _)
  have hfb : flexBound β K M c = l * B + a * BF + 2 * |l * c - 1| * M := rfl
  have hM' : 0 ≤ |l * c - 1| * M := mul_nonneg (abs_nonneg _) hM
  constructor
  · have e : ℓ t ω - zh t ω = l * prev ℓm1 ℓ t ω
        + (𝔼.forwardSeries a u t ω - l * c * zh t ω) + (l * c - 1) * zh t ω := by
      rw [hrec]; ring
    rw [e, hfb]
    calc _ ≤ |l * prev ℓm1 ℓ t ω + (𝔼.forwardSeries a u t ω - l * c * zh t ω)|
          + |(l * c - 1) * zh t ω| := abs_add_le _ _
      _ ≤ l * B + a * BF + |l * c - 1| * M :=
          add_le_add ((abs_add_le _ _).trans (add_le_add h1 (hFu t ω))) h3
      _ ≤ _ := by linarith
  · have e : ℓ t ω - l * (c * zh t ω) = l * prev ℓm1 ℓ t ω
        + (𝔼.forwardSeries a u t ω - l * c * zh t ω) := by
      rw [hrec]; ring
    rw [e, hfb]
    calc _ ≤ l * B + a * BF := (abs_add_le _ _).trans (add_le_add h1 (hFu t ω))
      _ ≤ _ := by linarith

/-- Woodford (2003), p. 232: `λ₁ c → 1` as `c → ∞` (from `βλ₁² − (1 + β + c)λ₁ + 1 = 0`). -/
theorem tendsto_lam1_mul {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun c => lam1 β c * c) atTop (𝓝 1) := by
  have hl := tendsto_lam1_atTop hβ
  have h : Tendsto (fun c => 1 - (1 + β) * lam1 β c + β * lam1 β c ^ 2) atTop
      (𝓝 (1 - (1 + β) * 0 + β * 0 ^ 2)) :=
    ((tendsto_const_nhds.sub (hl.const_mul (1 + β))).add ((hl.pow 2).const_mul β))
  rw [show (1 : ℝ) - (1 + β) * 0 + β * 0 ^ 2 = 1 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have : β * lam1 β c ^ 2 - (1 + β + c) * lam1 β c + 1 = 0 := charPoly_lam1 hβ hc
  linarith

/-- Woodford (2003), p. 232: the error bound of `secondOrder_flexible_bound` tends to zero as
`c = ξ_w + ξ_p → ∞`. -/
theorem tendsto_flexBound {β K M : ℝ} (hβ : 0 < β) :
    Tendsto (flexBound β K M) atTop (𝓝 0) := by
  have hl := tendsto_lam1_atTop hβ
  have ha := tendsto_inv_lam2_atTop hβ
  have hlc := tendsto_lam1_mul hβ
  have hBF : Tendsto (flexBF β M) atTop (𝓝 (1 * M / (1 - 0))) :=
    (hlc.mul_const M).div (tendsto_const_nhds.sub ha) (by norm_num)
  have hB : Tendsto (fun c => K + flexBF β M c / (1 - lam1 β c)) atTop
      (𝓝 (K + 1 * M / (1 - 0) / (1 - 0))) :=
    tendsto_const_nhds.add (hBF.div (tendsto_const_nhds.sub hl) (by norm_num))
  have h := ((hl.mul hB).add (ha.mul hBF)).add
    ((((hlc.sub_const 1).abs).const_mul 2).mul_const M)
  simp only [zero_mul, sub_self, abs_zero, mul_zero, add_zero] at h
  exact h

/-- Woodford (2003), p. 232 (**the flexible limit of (4.22)**): "when either wages or prices are
perfectly flexible (`ξ_w` or `ξ_p` unboundedly large) … `log w_t` is a multiple of `z_t`".
Uniformly over all bounded adapted `ẑ` (`|ẑ| ≤ M`) and initial values `|ℓ₋₁| ≤ K`, as
`c = ξ_w + ξ_p → ∞` the unique bounded solution of (4.22) with forcing `z = c ẑ` satisfies
`ℓ_t − ẑ_t → 0` and `ℓ_t − λ₁ z_t → 0` uniformly in `t` and the state:
`log w_t ≈ λ₁ z_t ≈ z_t/c`. -/
theorem secondOrder_flexible_limit {β K M : ℝ} (hβ : 0 < β) (hK : 0 ≤ K) (hM : 0 ≤ M) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ c in atTop, ∀ zh : ℕ → Ω → ℝ, (∀ t ω, |zh t ω| ≤ M) → 𝔼.Adapted zh →
      ∀ ℓm1 : Ω → ℝ, (∀ ω, |ℓm1 ω| ≤ K) → ∀ t ω,
        |secondOrderSol 𝔼 β c ℓm1 (fun t => c • zh t) t ω - zh t ω| ≤ η ∧
        |secondOrderSol 𝔼 β c ℓm1 (fun t => c • zh t) t ω - lam1 β c * (c * zh t ω)| ≤ η := by
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_flexBound (K := K) (M := M) hβ).eventually (gt_mem_nhds hη)]
    with c hc hb zh hz hza ℓm1 hm t ω
  obtain ⟨h1, h2⟩ := secondOrder_flexible_bound 𝔼 hβ hc hK hM hz hza hm t ω
  exact ⟨h1.trans hb.le, h2.trans hb.le⟩

/-- Woodford (2003), p. 231: the forcing of (4.18) factors as
`ξ log wⁿ + κ_d(Ŷ − Ŷⁿ) = ξ (log wⁿ + (κ_d/ξ)(Ŷ − Ŷⁿ))` (`κ_d = κ_w − κ_p`, `ξ = ξ_w + ξ_p`). -/
theorem forcing_factor {ξ κd : ℝ} (hξ : ξ ≠ 0) (lwn gap : ℕ → Ω → ℝ) :
    (fun t => ξ • lwn t + κd • gap t) = fun t => ξ • (lwn t + (κd / ξ) • gap t) := by
  funext t
  rw [smul_add, smul_smul, mul_div_cancel₀ _ hξ]

/-- Woodford (2003), p. 232 (flexible wages, `ξ_w = c − ξ_p → ∞` with `ξ_p` fixed):
`(κ_w − κ_p)/(ξ_w + ξ_p) = ((c − ξ_p)(ω_w + σ⁻¹) − ξ_pω_p)/c → ω_w + σ⁻¹`. -/
theorem tendsto_ratio_flexible_wages (ξp ωw ωp σi : ℝ) :
    Tendsto (fun c => ((c - ξp) * (ωw + σi) - ξp * ωp) / c) atTop (𝓝 (ωw + σi)) := by
  have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (ξp * (ωw + σi) + ξp * ωp)
  have h2 := (tendsto_const_nhds (x := ωw + σi)).sub h
  rw [mul_zero, sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  field_simp
  ring

/-- Woodford (2003), p. 232 (flexible prices, `ξ_p = c − ξ_w → ∞` with `ξ_w` fixed):
`(κ_w − κ_p)/(ξ_w + ξ_p) = (ξ_w(ω_w + σ⁻¹) − (c − ξ_w)ω_p)/c → −ω_p`. -/
theorem tendsto_ratio_flexible_prices (ξw ωw ωp σi : ℝ) :
    Tendsto (fun c => (ξw * (ωw + σi) - (c - ξw) * ωp) / c) atTop (𝓝 (-ωp)) := by
  have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (ξw * (ωw + σi) + ξw * ωp)
  have h2 := (tendsto_const_nhds (x := -ωp)).add h
  rw [mul_zero, add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  field_simp
  ring

/-- Woodford (2003), p. 232 (**the real wage in the flexible limit**): let `r(c) → r*` be the
ratio `(κ_w − κ_p)/(ξ_w + ξ_p)` along a sequence with `c = ξ_w + ξ_p → ∞`
(`tendsto_ratio_flexible_wages`: `r* = ω_w + σ⁻¹`, giving (4.21);
`tendsto_ratio_flexible_prices`: `r* = −ω_p`, the flexible-price relation of (4.12)/(4.16)).
Then the unique bounded solution (4.22) converges to `log wⁿ_t + r* (Ŷ_t − Ŷⁿ_t)` uniformly in
the date and the state. -/
theorem realWage_flexible_limit {β K Ml Mg rs : ℝ} (hβ : 0 < β) (hK : 0 ≤ K) (hMl : 0 ≤ Ml)
    (hMg : 0 ≤ Mg) {lwn gap : ℕ → Ω → ℝ} (hl : ∀ t ω, |lwn t ω| ≤ Ml)
    (hg : ∀ t ω, |gap t ω| ≤ Mg) (hla : 𝔼.Adapted lwn) (hga : 𝔼.Adapted gap)
    {ℓm1 : Ω → ℝ} (hm : ∀ ω, |ℓm1 ω| ≤ K) {r : ℝ → ℝ} (hr : Tendsto r atTop (𝓝 rs)) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ c in atTop, ∀ t ω,
      |secondOrderSol 𝔼 β c ℓm1 (fun t => c • (lwn t + r c • gap t)) t ω
        - (lwn t ω + rs * gap t ω)| ≤ η := by
  set M := Ml + (|rs| + 1) * Mg with hMdef
  have hM : 0 ≤ M := by positivity
  set δ := min 1 (η / (2 * (Mg + 1))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hrδ : ∀ᶠ c in atTop, |r c - rs| < δ := by
    have := (Metric.tendsto_nhds.mp hr) δ hδ0
    filter_upwards [this] with c hc
    rwa [Real.dist_eq] at hc
  filter_upwards [hrδ, secondOrder_flexible_limit 𝔼 hβ hK hM (half_pos hη)] with c hc hlim t ω
  have hrc : |r c| ≤ |rs| + 1 := by
    have := abs_sub_abs_le_abs_sub (r c) rs
    linarith [min_le_left 1 (η / (2 * (Mg + 1)))]
  have hzb : ∀ t ω, |(fun t => lwn t + r c • gap t) t ω| ≤ M := fun t ω => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hl t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul hrc (hg t ω) (abs_nonneg _) (by positivity)
  have hza : 𝔼.Adapted (fun t => lwn t + r c • gap t) := fun t => by
    simp only [map_add, map_smul, hla t, hga t]
  have h1 := (hlim _ hzb hza ℓm1 hm t ω).1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : |r c - rs| * |gap t ω| ≤ η / 2 := by
    have hδ' : δ ≤ η / (2 * (Mg + 1)) := min_le_right _ _
    calc |r c - rs| * |gap t ω| ≤ δ * Mg :=
          mul_le_mul hc.le (hg t ω) (abs_nonneg _) hδ0.le
      _ ≤ η / (2 * (Mg + 1)) * Mg := mul_le_mul_of_nonneg_right hδ' hMg
      _ ≤ η / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have e : secondOrderSol 𝔼 β c ℓm1 (fun t => c • (lwn t + r c • gap t)) t ω
      - (lwn t ω + rs * gap t ω)
      = (secondOrderSol 𝔼 β c ℓm1 (fun t => c • (lwn t + r c • gap t)) t ω
        - (lwn t ω + r c * gap t ω)) + (r c - rs) * gap t ω := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (r c - rs)]
  linarith


/-! ### Indexation: (4.23)–(4.25) -/

/-- Woodford (2003), eqs. (4.23)–(4.24), p. 234: if indexed wage and price inflation obey the
Calvo equations in bracket form (`calvo_pc_iff`/`reset_sum_iff_pc` with indexation to lagged
price inflation, `ι_t = π_{t−1}`), and `v̂`, `ψ̂` are as in (4.10), then
`π^w_t − γ_w π_{t−1} = κ_w(Ŷ_t − Ŷⁿ_t) + ξ_w(log wⁿ_t − log w_t) + β E_t[π^w_{t+1} − γ_w π_t]`
and
`π_t − γ_p π_{t−1} = κ_p(Ŷ_t − Ŷⁿ_t) + ξ_p(log w_t − log wⁿ_t) + β E_t[π_{t+1} − γ_p π_t]`. -/
theorem eq423_424 {β ξw ξp ωw ωp σi lwbar γw γp : ℝ} {πm1 : Ω → ℝ}
    {πw πp lW lP vhat ψhat Yh Yn a : ℕ → Ω → ℝ}
    (hw : ∀ t, πw t - γw • prev πm1 πp t = ξw • (vhat t + (fun _ => lwbar) + lP t - lW t)
      + β • 𝔼.E t (πw (t + 1) - γw • πp t))
    (hp : ∀ t, πp t - γp • prev πm1 πp t = ξp • (ψhat t - (fun _ => lwbar) + lW t - lP t)
      + β • 𝔼.E t (πp (t + 1) - γp • πp t))
    (hv : ∀ t, vhat t = (ωw + σi) • Yh t - (ωw + ωp + σi) • Yn t + (1 + ωp) • a t)
    (hψ : ∀ t, ψhat t = ωp • Yh t - (1 + ωp) • a t) :
    (∀ t, πw t - γw • prev πm1 πp t = kappaW ξw ωw σi • (Yh t - Yn t)
      + ξw • (natRealWage lwbar ωp a Yn t - (lW t - lP t))
      + β • 𝔼.E t (πw (t + 1) - γw • πp t)) ∧
    (∀ t, πp t - γp • prev πm1 πp t = kappaP ξp ωp • (Yh t - Yn t)
      + ξp • ((lW t - lP t) - natRealWage lwbar ωp a Yn t)
      + β • 𝔼.E t (πp (t + 1) - γp • πp t)) := by
  constructor
  · intro t
    rw [hw t, hv t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaW, natRealWage]
    ring
  · intro t
    rw [hp t, hψ t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappaP, natRealWage]
    ring

/-- Woodford (2003), p. 235: with flexible prices and a linear technology (`ω_p = 0`), (4.16)
reduces to `log w = log wⁿ`. -/
theorem eq416_linear {lwbar lW lP a Yh Yn : ℝ}
    (hflex : 0 * Yh - (1 + 0) * a - lwbar + (lW - lP) = 0) :
    lW - lP = lwbar + (1 + 0) * a - 0 * Yn := by
  linarith

/-- Woodford (2003), eq. (4.25), p. 235 (flexible prices, `ω_p = 0`, indexed sticky wages): with
`log w = log wⁿ` (so `π^w_t = π_t + Δ log wⁿ_t`), (4.23) gives
`π_t − γπ_{t−1} = κ(Ŷ_t − Ŷⁿ_t) + β E_t[π_{t+1} − γπ_t] + u_t` with `γ = γ_w`, `κ = κ_w` and
`u_t = β E_t Δ log wⁿ_{t+1} − Δ log wⁿ_t`. -/
theorem eq425_flexible_prices {β κ ξw γ : ℝ} {πm1 lwnm1 : Ω → ℝ}
    {πw πp gap lw lwn : ℕ → Ω → ℝ}
    (h423 : ∀ t, πw t - γ • prev πm1 πp t = κ • gap t + ξw • (lwn t - lw t)
      + β • 𝔼.E t (πw (t + 1) - γ • πp t))
    (hlw : ∀ t, lw t = lwn t) (hΔ : ∀ t, πw t = πp t + (lwn t - prev lwnm1 lwn t)) (t : ℕ) :
    πp t - γ • prev πm1 πp t = κ • gap t + β • 𝔼.E t (πp (t + 1) - γ • πp t)
      + (β • 𝔼.E t (lwn (t + 1) - lwn t) - (lwn t - prev lwnm1 lwn t)) := by
  have h := h423 t
  rw [hlw t, hΔ t, hΔ (t + 1), prev_succ] at h
  have e : 𝔼.E t (πp (t + 1) + (lwn (t + 1) - lwn t) - γ • πp t)
      = 𝔼.E t (πp (t + 1) - γ • πp t) + 𝔼.E t (lwn (t + 1) - lwn t) := by
    rw [← map_add]
    congr 1
    abel
  rw [e] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hω ⊢
  linarith

/-- Woodford (2003), eq. (4.25), p. 235 (equal indexation `γ_w = γ_p = γ` and `κ_w = κ_p = κ`):
subtracting (4.24) from (4.23) gives the real-wage equation free of output and monetary policy,
`Δ log w_t = −(ξ_w + ξ_p)(log w_t − log wⁿ_t) + β E_t Δ log w_{t+1}`; and with its solution
`w̄`, (4.24) becomes (4.25) with `u_t = ξ_p(log w̄_t − log wⁿ_t)` as in (4.20). -/
theorem eq425_equal_indexation {β κ ξw ξp γ : ℝ} {πm1 : Ω → ℝ}
    {πw πp gap lw lwn wbar : ℕ → Ω → ℝ}
    (h423 : ∀ t, πw t - γ • prev πm1 πp t = κ • gap t + ξw • (lwn t - lw t)
      + β • 𝔼.E t (πw (t + 1) - γ • πp t))
    (h424 : ∀ t, πp t - γ • prev πm1 πp t = κ • gap t + ξp • (lw t - lwn t)
      + β • 𝔼.E t (πp (t + 1) - γ • πp t)) :
    (∀ t, πw t - πp t = -(ξw + ξp) • (lw t - lwn t) + β • 𝔼.E t (πw (t + 1) - πp (t + 1))) ∧
      (lw = wbar → ∀ t, πp t - γ • prev πm1 πp t = κ • gap t
        + β • 𝔼.E t (πp (t + 1) - γ • πp t) + ξp • (wbar t - lwn t)) := by
  constructor
  · intro t
    have h1 := h423 t
    have h2 := h424 t
    have e : 𝔼.E t (πw (t + 1) - πp (t + 1))
        = 𝔼.E t (πw (t + 1) - γ • πp t) - 𝔼.E t (πp (t + 1) - γ • πp t) := by
      rw [← map_sub]
      congr 1
      abel
    rw [e]
    funext ω
    have k1 := congrFun h1 ω
    have k2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at k1 k2 ⊢
    linarith
  · rintro rfl t
    rw [h424 t]
    abel

/-! ### Figure 3.18 -/

/-- Woodford (2003), p. 233 and Fig. 3.18 (**suspected misprint**): with the Rotemberg–Woodford
values (Table 5.1, cited as "Table 4.1") `α = 0.66`, `β = 0.99`, `ω_p = 0.33`, `θ_p = 7.88`,
`ω_w = 0.14`, `σ⁻¹ = 0.16`, the economy-wide-labour-market slope is `ξ_p ≈ 0.0496`, so
`κ_w = κ_p` requires `ξ_w = ξ_pω_p/(ω_w + σ⁻¹) ≈ 0.0546`; at the printed `ξ_w = 0.55`, `κ_w`
exceeds ten times `κ_p`. -/
theorem fig318_equal_stickiness :
    (0.0495 : ℝ) < calvoXi 0.66 0.99 (0.33 * 7.88) ∧
      calvoXi (0.66 : ℝ) 0.99 (0.33 * 7.88) < 0.0497 ∧
      (0.054 : ℝ) < calvoXi 0.66 0.99 (0.33 * 7.88) * 0.33 / (0.14 + 0.16) ∧
      calvoXi (0.66 : ℝ) 0.99 (0.33 * 7.88) * 0.33 / (0.14 + 0.16) < 0.055 ∧
      10 * kappaP (calvoXi 0.66 0.99 (0.33 * 7.88)) 0.33 < kappaW (0.55 : ℝ) 0.14 0.16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [calvoXi, kappaP, kappaW]

end Woodford.NominalRigidities.StickyWages
