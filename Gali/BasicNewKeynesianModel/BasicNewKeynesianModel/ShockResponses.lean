/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.TaylorRuleSystem

/-!
# Responses to shocks under the interest-rate rule

Galí (2015), Chapter 3, §§3.4.1.1–3.4.1.3, pp. 66–72. Under condition (28)
the unique bounded equilibrium is the MSV solution (29)–(30) of
`TaylorRuleSystem`. This module specialises it to the three shocks of the
basic model.

## Main results

* `monetary_shock`, `monetary_money_supply` (pp. 66–67): output gap,
  inflation, real rate, nominal rate and money supply after a monetary policy
  shock `v`; `liquidity_effect_iff` and `money_contracts_of_nominal_rises`.
* `discount_shock`, `discount_eq_monetary` (pp. 70–71): a discount-rate shock
  `z` moves `(ỹ, π)` exactly like a monetary shock `v = −(1 − ρ_z) z`.
  `discount_natRate_falls` and `discount_natRate_book_numbers` record the
  correction C3-5: the natural rate **falls** after the book's shock.
* `technology_shock`, `technology_output`, `technology_employment`
  (pp. 71–72): responses of `ỹ`, `π`, `y`, `n` to technology, with the
  corrected employment coefficient (C3-3, a missing `1/(1 − α)`), and
  `techNCoef_sub_printed` showing that the printed formula differs.
* `techOutputCoef_mem` and `techOutputCoef_counterexample` (C3-4): the output
  coefficient `κ (φ_π − ρ_a) Λ_a` lies in `(0, 1)` when `φ_π > ρ_a`, but can
  be negative under (28) alone.
* `techNCoef_neg_of_one_le_sigma`, `techNCoef_neg_of_phiy_large` (p. 72):
  employment falls after a technology improvement if `σ ≥ 1` (given
  `φ_π ≥ ρ_a`) or if `φ_y` is large.
-/

namespace Gali.BasicNewKeynesianModel.ShockResponses

open TaylorRuleSystem

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- A scalar multiple of a bounded process is bounded. -/
theorem boundedProc_smul {s : ℕ → Ω → ℝ} (hs : BoundedProc s) (c : ℝ) :
    BoundedProc (fun t => c • s t) := by
  obtain ⟨M, hM⟩ := hs
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), p. 66: if the composite shock is `u_t = c s_t` for a bounded
AR(1) process `s` with persistence `ρ_u < 1`, then under (28) every
equilibrium with bounded adapted `ỹ`, `π` has `ỹ_t = ψ_y c s_t` and
`π_t = ψ_π c s_t`. -/
theorem eq_msv_of_shock {β σ κ ρ φπ φy ρu c : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {s rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 ρu s) (hsb : BoundedProc s) (hU : ∀ t, shockU ρ φy rn yhatn v t = c • s t)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    (∀ t, ygap t = (msvPsiY β σ κ φπ φy ρu * c) • s t) ∧
      (∀ t, infl t = (msvPsiPi β σ κ φπ φy ρu * c) • s t) := by
  have hU' : shockU ρ φy rn yhatn v = fun t => c • s t := funext hU
  have hu : 𝔼.IsAR1 ρu (shockU ρ φy rn yhatn v) := by
    rw [hU']; exact isAR1_smul 𝔼 hs c
  have hub : BoundedProc (shockU ρ φy rn yhatn v) := by
    rw [hU']; exact boundedProc_smul hsb c
  obtain ⟨h1, h2, -⟩ :=
    (equilibrium_iff_msv 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hu hub ha hb hba hbb).mp he
  exact ⟨fun t => by simp only [h1, hU, smul_smul], fun t => by simp only [h2, hU, smul_smul]⟩

/-! ### Monetary policy shock (§3.4.1.1, pp. 66–67) -/

/-- Galí (2015), p. 66: output-gap response to a monetary shock,
`−(1 − βρ_v) Λ_v`. -/
noncomputable def monYgapCoef (β σ κ φπ φy ρv : ℝ) : ℝ :=
  -((1 - β * ρv) * msvLambda β σ κ φπ φy ρv)

/-- Galí (2015), p. 66: inflation response to a monetary shock, `−κ Λ_v`. -/
noncomputable def monInflCoef (β σ κ φπ φy ρv : ℝ) : ℝ := -(κ * msvLambda β σ κ φπ φy ρv)

/-- Galí (2015), p. 66: real-rate response to a monetary shock,
`σ (1 − ρ_v)(1 − βρ_v) Λ_v`. -/
noncomputable def monRealCoef (β σ κ φπ φy ρv : ℝ) : ℝ :=
  σ * (1 - ρv) * (1 - β * ρv) * msvLambda β σ κ φπ φy ρv

/-- Galí (2015), p. 67: nominal-rate response to a monetary shock,
`[σ (1 − ρ_v)(1 − βρ_v) − ρ_v κ] Λ_v`. -/
noncomputable def monNomCoef (β σ κ φπ φy ρv : ℝ) : ℝ :=
  (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ) * msvLambda β σ κ φπ φy ρv

/-- Galí (2015), p. 67: money-supply response to a monetary shock,
`−Λ_v [(1 − βρ_v)(1 + ησ (1 − ρ_v)) + (1 − ηρ_v) κ]`. -/
noncomputable def monMoneyCoef (β σ κ φπ φy ρv η : ℝ) : ℝ :=
  -(msvLambda β σ κ φπ φy ρv * ((1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ))

/-- **Monetary policy shock** (Galí 2015, pp. 66–67): with `a = z = 0`
(so `r^n_t = ρ` and `ŷ^n_t = 0`), an AR(1) monetary shock `v` with
persistence `ρ_v < 1` and (28), every equilibrium with bounded adapted `ỹ`, `π`
has `ỹ_t = −(1 − βρ_v) Λ_v v_t`, `π_t = −κ Λ_v v_t`,
`r̂_t = σ (1 − ρ_v)(1 − βρ_v) Λ_v v_t` and
`î_t = [σ (1 − ρ_v)(1 − βρ_v) − ρ_v κ] Λ_v v_t`. -/
theorem monetary_shock {β σ κ ρ φπ φy ρv : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (hv : 𝔼.IsAR1 ρv v) (hvb : BoundedProc v) (hrn : ∀ t, rn t = fun _ => ρ)
    (hyn : ∀ t, yhatn t = 0) (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    (∀ t, ygap t = monYgapCoef β σ κ φπ φy ρv • v t) ∧
      (∀ t, infl t = monInflCoef β σ κ φπ φy ρv • v t) ∧
      (∀ t, DIS.realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β σ κ φπ φy ρv • v t) ∧
      (∀ t, i t - (fun _ => ρ) = monNomCoef β σ κ φπ φy ρv • v t) := by
  have hU : ∀ t, shockU ρ φy rn yhatn v t = (-1 : ℝ) • v t := by
    intro t
    simp [shockU, hrn, hyn]
  obtain ⟨h1, h2⟩ := eq_msv_of_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hv hvb hU he ha hb hba hbb
  have hy : ∀ t, ygap t = monYgapCoef β σ κ φπ φy ρv • v t := fun t => by
    rw [h1 t, monYgapCoef, msvPsiY, mul_neg_one]
  have hp : ∀ t, infl t = monInflCoef β σ κ φπ φy ρv • v t := fun t => by
    rw [h2 t, monInflCoef, msvPsiPi, mul_neg_one]
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  have hr : ∀ t, DIS.realRate 𝔼 i infl t - (fun _ => ρ) = monRealCoef β σ κ φπ φy ρv • v t := by
    intro t
    have hd := he.2.1 t
    rw [hy t, hy (t + 1), map_smul, hv.2 t, hrn t] at hd
    funext ω
    have e := congrFun hd ω
    simp only [DIS.realRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    simp only [monYgapCoef, monRealCoef] at e ⊢
    linear_combination σ * e - (i t ω - (𝔼.E t) (infl (t + 1)) ω - ρ) * hinv
  refine ⟨hy, hp, hr, fun t => ?_⟩
  have h := hr t
  rw [DIS.realRate, hp (t + 1), map_smul, hv.2 t] at h
  funext ω
  have e := congrFun h ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  simp only [monInflCoef, monRealCoef, monNomCoef] at e ⊢
  linear_combination e

/-- **Money supply after a monetary shock** (Galí 2015, p. 67): with money
demand (4) `m_t = p_t + y_t − η i_t`, the price level `p_{t+1} = p_t + π_{t+1}`
and output `y_t = ỹ_t + ȳ` (natural output is constant when `a = 0`),
`m_{t+1} = p_t + (ȳ − ηρ) − Λ_v [(1 − βρ_v)(1 + ησ (1 − ρ_v)) + (1 − ηρ_v) κ] v_{t+1}`. -/
theorem monetary_money_supply {β σ κ ρ φπ φy ρv η ybar : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρv < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v ygap infl i m p y : ℕ → Ω → ℝ}
    (hv : 𝔼.IsAR1 ρv v) (hvb : BoundedProc v) (hrn : ∀ t, rn t = fun _ => ρ)
    (hyn : ∀ t, yhatn t = 0) (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) (hm : ∀ t, m t = p t + y t - η • i t)
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hy : ∀ t, y t = ygap t + fun _ => ybar)
    (t : ℕ) :
    m (t + 1) = p t + (fun _ => ybar - η * ρ) + monMoneyCoef β σ κ φπ φy ρv η • v (t + 1) := by
  obtain ⟨h1, h2, -, h4⟩ :=
    monetary_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hv hvb hrn hyn he ha hb hba hbb
  have hi : i (t + 1) = (fun _ => ρ) + monNomCoef β σ κ φπ φy ρv • v (t + 1) := by
    rw [← h4 (t + 1)]; abel
  rw [hm, hp, hy, hi, h1, h2]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [monYgapCoef, monInflCoef, monNomCoef, monMoneyCoef]
  ring

/-- Galí (2015), p. 66: under (28) and `ρ_v < 1`, a monetary tightening lowers
the output gap and inflation and raises the real rate. -/
theorem monetary_signs {β σ κ φπ φy ρv : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρv < 1) (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) :
    monYgapCoef β σ κ φπ φy ρv < 0 ∧ monInflCoef β σ κ φπ φy ρv < 0 ∧
      0 < monRealCoef β σ κ φπ φy ρv := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h28
  have hbr : 0 < 1 - β * ρv := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold monYgapCoef; nlinarith [mul_pos hbr hL]
  · unfold monInflCoef; nlinarith [mul_pos hκ hL]
  · unfold monRealCoef
    have : 0 < σ * (1 - ρv) := mul_pos hσ (by linarith)
    positivity

/-- Galí (2015), p. 67: the nominal rate falls after a monetary tightening if
and only if `σ (1 − ρ_v)(1 − βρ_v) < ρ_v κ` (high persistence). -/
theorem monNomCoef_neg_iff {β σ κ φπ φy ρv : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρv) :
    monNomCoef β σ κ φπ φy ρv < 0 ↔ σ * (1 - ρv) * (1 - β * ρv) < ρv * κ := by
  unfold monNomCoef
  rw [mul_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h; exact Or.inr ⟨by linarith, hL⟩

/-- Galí (2015), p. 67: the money-supply bracket is
`(1 − βρ_v) + κ + η [σ (1 − ρ_v)(1 − βρ_v) − ρ_v κ]`. -/
theorem money_bracket_eq (β σ κ ρv η : ℝ) :
    (1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ
      = (1 - β * ρv) + κ + η * (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ) := by
  ring

/-- Galí (2015), p. 67: with `Λ_v > 0`, money contracts after a tightening
(`m` coefficient negative) if and only if
`(1 − βρ_v)(1 + ησ (1 − ρ_v)) + (1 − ηρ_v) κ > 0`. -/
theorem monMoneyCoef_neg_iff {β σ κ φπ φy ρv η : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρv) :
    monMoneyCoef β σ κ φπ φy ρv η < 0 ↔
      0 < (1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ := by
  unfold monMoneyCoef
  rw [neg_lt_zero]
  exact ⟨fun h => pos_of_mul_pos_right h hL.le, fun h => mul_pos hL h⟩

/-- Galí (2015), p. 67: `di_t/dv_t > 0` is sufficient for a contraction in the
money supply, for `η ≥ 0`, `κ > 0` and `βρ_v < 1`. -/
theorem money_contracts_of_nominal_rises {β σ κ φπ φy ρv η : ℝ} (hκ : 0 < κ)
    (hbr : β * ρv < 1) (hη : 0 ≤ η) (hL : 0 < msvLambda β σ κ φπ φy ρv)
    (hi : 0 < monNomCoef β σ κ φπ φy ρv) : monMoneyCoef β σ κ φπ φy ρv η < 0 := by
  rw [monMoneyCoef_neg_iff hL, money_bracket_eq]
  have hb : 0 < σ * (1 - ρv) * (1 - β * ρv) - ρv * κ := pos_of_mul_pos_left hi hL.le
  have : 0 ≤ η * (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ) := mul_nonneg hη hb.le
  linarith

/-- **Liquidity effect** (Galí 2015, p. 67): the nominal rate and the money
supply move in opposite directions after a monetary shock if and only if the
nominal-rate bracket and the money-supply bracket have the same sign. -/
theorem liquidity_effect_iff {β σ κ φπ φy ρv η : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρv) :
    monNomCoef β σ κ φπ φy ρv * monMoneyCoef β σ κ φπ φy ρv η < 0 ↔
      0 < (σ * (1 - ρv) * (1 - β * ρv) - ρv * κ)
        * ((1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ) := by
  have e : monNomCoef β σ κ φπ φy ρv * monMoneyCoef β σ κ φπ φy ρv η
      = -(msvLambda β σ κ φπ φy ρv ^ 2 * ((σ * (1 - ρv) * (1 - β * ρv) - ρv * κ)
        * ((1 - β * ρv) * (1 + η * σ * (1 - ρv)) + (1 - η * ρv) * κ))) := by
    unfold monNomCoef monMoneyCoef; ring
  rw [e, neg_lt_zero]
  have h2 : 0 < msvLambda β σ κ φπ φy ρv ^ 2 := by positivity
  exact ⟨fun h => pos_of_mul_pos_right h h2.le, fun h => mul_pos h2 h⟩

/-- Galí (2015), p. 67: `di_t/dv_t > 0` is sufficient for a liquidity effect. -/
theorem liquidity_effect_of_nominal_rises {β σ κ φπ φy ρv η : ℝ} (hκ : 0 < κ)
    (hbr : β * ρv < 1) (hη : 0 ≤ η) (hL : 0 < msvLambda β σ κ φπ φy ρv)
    (hi : 0 < monNomCoef β σ κ φπ φy ρv) :
    monNomCoef β σ κ φπ φy ρv * monMoneyCoef β σ κ φπ φy ρv η < 0 :=
  mul_neg_of_pos_of_neg hi (money_contracts_of_nominal_rises hκ hbr hη hL hi)

/-! ### Discount-rate shock (§3.4.1.2, pp. 70–71) -/

/-- **Discount-rate shock** (Galí 2015, pp. 70–71): with `a = v = 0` the
natural rate is `r^n_t = ρ + (1 − ρ_z) z_t` (eq. (24)) and `ŷ^n_t = 0`; for an
AR(1) preference shock with `ρ_z < 1` and (28), every equilibrium with bounded
adapted `ỹ`, `π` has `ỹ_t = (1 − βρ_z) Λ_z (1 − ρ_z) z_t`,
`π_t = κ Λ_z (1 − ρ_z) z_t`, `î_t = (φ_π κ + φ_y (1 − βρ_z)) Λ_z (1 − ρ_z) z_t`
and `r̂_t = (1 − ρ_z)(1 − σ (1 − ρ_z)(1 − βρ_z) Λ_z) z_t`. -/
theorem discount_shock {β σ κ ρ φπ φy ρz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρz < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v z ygap infl i : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ρz z) (hzb : BoundedProc z) (hrn : ∀ t, rn t = (fun _ => ρ) + (1 - ρz) • z t)
    (hyn : ∀ t, yhatn t = 0) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    (∀ t, ygap t = ((1 - β * ρz) * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t) ∧
      (∀ t, infl t = (κ * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t) ∧
      (∀ t, i t - (fun _ => ρ)
        = ((φπ * κ + φy * (1 - β * ρz)) * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t) ∧
      (∀ t, DIS.realRate 𝔼 i infl t - (fun _ => ρ)
        = ((1 - ρz) * (1 - σ * (1 - ρz) * (1 - β * ρz) * msvLambda β σ κ φπ φy ρz)) • z t) := by
  have hU : ∀ t, shockU ρ φy rn yhatn v t = (1 - ρz) • z t := by
    intro t
    simp [shockU, hrn, hyn, hv0]
  obtain ⟨h1, h2⟩ := eq_msv_of_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hz hzb hU he ha hb hba hbb
  have hy : ∀ t, ygap t = ((1 - β * ρz) * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t :=
    fun t => by rw [h1 t, msvPsiY]
  have hp : ∀ t, infl t = (κ * msvLambda β σ κ φπ φy ρz * (1 - ρz)) • z t :=
    fun t => by rw [h2 t, msvPsiPi]
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
  refine ⟨hy, hp, fun t => ?_, fun t => ?_⟩
  · rw [he.2.2 t, hyn t, hv0 t, hy t, hp t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  · have hd := he.2.1 t
    rw [hy t, hy (t + 1), map_smul, hz.2 t, hrn t] at hd
    funext ω
    have e := congrFun hd ω
    simp only [DIS.realRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination σ * e - (i t ω - (𝔼.E t) (infl (t + 1)) ω - (ρ + (1 - ρz) * z t ω))
      * hinv

/-- Galí (2015), p. 71: the discount-rate shock and a monetary shock enter the
system (27) symmetrically. An equilibrium under a discount-rate shock `z` and
one under the monetary shock `v_t = −(1 − ρ_z) z_t` (with constant natural
rate) have the same output gap and inflation. -/
theorem discount_eq_monetary {β σ κ ρ φπ φy ρz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρz < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn yhatn v z ygap infl i rn' yhatn' v' ygap' infl' i' : ℕ → Ω → ℝ}
    (hz : 𝔼.IsAR1 ρz z) (hzb : BoundedProc z) (hrn : ∀ t, rn t = (fun _ => ρ) + (1 - ρz) • z t)
    (hyn : ∀ t, yhatn t = 0) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hrn' : ∀ t, rn' t = fun _ => ρ) (hyn' : ∀ t, yhatn' t = 0)
    (hv' : ∀ t, v' t = (-(1 - ρz)) • z t)
    (he' : Equilibrium 𝔼 β σ κ ρ φπ φy rn' yhatn' v' ygap' infl' i') (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' := by
  obtain ⟨h1, h2, -, -⟩ :=
    discount_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hz hzb hrn hyn hv0 he ha hb hba hbb
  have hvf : v' = fun t => (-(1 - ρz)) • z t := funext hv'
  have hvA : 𝔼.IsAR1 ρz v' := by rw [hvf]; exact isAR1_smul 𝔼 hz _
  have hvB : BoundedProc v' := by rw [hvf]; exact boundedProc_smul hzb _
  obtain ⟨g1, g2, -, -⟩ :=
    monetary_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hvA hvB hrn' hyn' he' ha' hb' hba' hbb'
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · rw [h1 t, g1 t, hv' t, smul_smul, monYgapCoef]; ring_nf
  · rw [h2 t, g2 t, hv' t, smul_smul, monInflCoef]; ring_nf

/-- Galí (2015), p. 71: the nominal-rate and real-rate coefficients of the
discount-rate shock are positive under (28) when `φ_π ≥ ρ_z`, so a fall in
`z` lowers both interest rates, as the text says. -/
theorem discount_rates_fall {β σ κ φπ φy ρz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρz < 1) (hρπ : ρz ≤ φπ)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) :
    0 < (φπ * κ + φy * (1 - β * ρz)) * msvLambda β σ κ φπ φy ρz * (1 - ρz) ∧
      0 < (1 - ρz) * (1 - σ * (1 - ρz) * (1 - β * ρz) * msvLambda β σ κ φπ φy ρz) := by
  have hL := msvLambda_pos hσ hκ hβ0 hβ1 hφy hρ1 h28
  have hD := msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28
  have hbr : 0 < 1 - β * ρz := by nlinarith
  have h1ρ : 0 < 1 - ρz := by linarith
  refine ⟨?_, ?_⟩
  · have : 0 < φπ * κ + φy * (1 - β * ρz) := by
      rcases hφπ.lt_or_eq with h | h
      · have := mul_pos h hκ; nlinarith
      · subst h
        have : φy ≠ 0 := by rintro rfl; nlinarith
        have := lt_of_le_of_ne hφy (Ne.symm this)
        nlinarith
    positivity
  · apply mul_pos h1ρ
    have e : 1 - σ * (1 - ρz) * (1 - β * ρz) * msvLambda β σ κ φπ φy ρz
        = ((1 - β * ρz) * φy + κ * (φπ - ρz)) * msvLambda β σ κ φπ φy ρz := by
      unfold msvLambda
      field_simp
      unfold msvDen
      ring
    rw [e]
    apply mul_pos _ hL
    have : 0 ≤ κ * (φπ - ρz) := mul_nonneg hκ.le (by linarith)
    rcases (mul_nonneg hbr.le hφy).lt_or_eq with h | h
    · linarith
    · -- `φ_y = 0`, so (28) forces `φ_π > 1 > ρ_z`
      have hφy0 : φy = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · linarith
        · exact h'
      subst hφy0
      have : 1 < φπ := by nlinarith
      nlinarith

/-- **Correction C3-5** (Galí 2015, p. 71): a fall in `z` lowers the natural
rate. If `z_t = ε` with `ε < 0` and `ρ_z < 1`, then by (24) (with `a = 0`)
`r^n_t − ρ = (1 − ρ_z) ε < 0`; the text says the natural rate increases. -/
theorem discount_natRate_falls {ρ ρz ε : ℝ} (hρ1 : ρz < 1) (hε : ε < 0)
    {rn z : ℕ → Ω → ℝ} {t : ℕ} (hrn : rn t = (fun _ => ρ) + (1 - ρz) • z t)
    (hzt : z t = fun _ => ε) :
    rn t - (fun _ => ρ) = (fun _ => (1 - ρz) * ε) ∧ (1 - ρz) * ε < 0 := by
  refine ⟨?_, mul_neg_of_pos_of_neg (by linarith) hε⟩
  rw [hrn, hzt]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Correction C3-5**, the book's numbers (Galí 2015, p. 71): with
`ρ_z = 0.5` and `ε^z = −0.5` the natural rate changes by
`(1 − ρ_z) ε^z = −0.25` per quarter, i.e. by `−1` percentage point at an
annual rate: a fall, not an increase. -/
theorem discount_natRate_book_numbers :
    (1 - (1 / 2 : ℝ)) * (-1 / 2) = -1 / 4 ∧ 4 * ((1 - (1 / 2 : ℝ)) * (-1 / 2)) = -1 := by
  norm_num

/-! ### Technology shock (§3.4.1.3, pp. 71–72) -/

/-- Galí (2015), p. 71: output-gap response to technology,
`−ψ_ya (φ_y + σ (1 − ρ_a))(1 − βρ_a) Λ_a`. -/
noncomputable def techYgapCoef (β σ κ φπ φy ρa ψya : ℝ) : ℝ :=
  -(ψya * (φy + σ * (1 - ρa)) * (1 - β * ρa) * msvLambda β σ κ φπ φy ρa)

/-- Galí (2015), p. 72: inflation response to technology,
`−ψ_ya (φ_y + σ (1 − ρ_a)) κ Λ_a`. -/
noncomputable def techInflCoef (β σ κ φπ φy ρa ψya : ℝ) : ℝ :=
  -(ψya * (φy + σ * (1 - ρa)) * κ * msvLambda β σ κ φπ φy ρa)

/-- Galí (2015), p. 72: the factor `κ (φ_π − ρ_a) Λ_a` of the output response
to technology. -/
noncomputable def techOutputCoef (β σ κ φπ φy ρa : ℝ) : ℝ :=
  κ * (φπ - ρa) * msvLambda β σ κ φπ φy ρa

/-- **Corrected** employment response to technology (Galí 2015, p. 72, with
correction C3-3):
`Λ_a [(1 − σ) κ (φ_π − ρ_a)/(σ (1 − α) + φ + α) − (φ_y + σ (1 − ρ_a))(1 − βρ_a)/(1 − α)]`. -/
noncomputable def techNCoef (β σ κ φπ φy ρa φ α : ℝ) : ℝ :=
  msvLambda β σ κ φπ φy ρa * ((1 - σ) * κ * (φπ - ρa) / (σ * (1 - α) + φ + α)
    - (φy + σ * (1 - ρa)) * (1 - β * ρa) / (1 - α))

/-- The employment coefficient **as printed** in Galí (2015), p. 72:
`Λ_a [(1 − σ) κ (φ_π − ρ_a)/(σ (1 − α) + φ + α) − (φ_y + σ (1 − ρ_a))(1 − βρ_a)]`
(missing the factor `1/(1 − α)` on the second term). -/
noncomputable def techNCoefPrinted (β σ κ φπ φy ρa φ α : ℝ) : ℝ :=
  msvLambda β σ κ φπ φy ρa * ((1 - σ) * κ * (φπ - ρa) / (σ * (1 - α) + φ + α)
    - (φy + σ * (1 - ρa)) * (1 - β * ρa))

/-- **Technology shock** (Galí 2015, pp. 71–72): with `z = v = 0`,
`r^n_t = ρ − σ (1 − ρ_a) ψ_ya a_t` (eq. (24)) and `ŷ^n_t = ψ_ya a_t`, an AR(1)
technology process with `ρ_a < 1` and (28), every equilibrium with bounded
adapted `ỹ`, `π` has `ỹ_t = −ψ_ya (φ_y + σ (1 − ρ_a))(1 − βρ_a) Λ_a a_t` and
`π_t = −ψ_ya (φ_y + σ (1 − ρ_a)) κ Λ_a a_t`. -/
theorem technology_shock {β σ κ ρ φπ φy ρa ψya : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρa < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v a ygap infl i : ℕ → Ω → ℝ}
    (hav : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hrn : ∀ t, rn t = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t)
    (hyn : ∀ t, yhatn t = ψya • a t) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    (∀ t, ygap t = techYgapCoef β σ κ φπ φy ρa ψya • a t) ∧
      (∀ t, infl t = techInflCoef β σ κ φπ φy ρa ψya • a t) := by
  have hU : ∀ t, shockU ρ φy rn yhatn v t = (-(ψya * (φy + σ * (1 - ρa)))) • a t := by
    intro t
    rw [shockU, hrn, hyn, hv0]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  obtain ⟨h1, h2⟩ := eq_msv_of_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hav hab hU he ha hb hba hbb
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [h1 t, msvPsiY, techYgapCoef]; ring_nf
  · rw [h2 t, msvPsiPi, techInflCoef]; ring_nf

/-- Galí (2015), p. 72: the output response decomposes as
`ψ_ya + (ỹ coefficient) = ψ_ya κ (φ_π − ρ_a) Λ_a`. -/
theorem techOutput_eq {β σ κ φπ φy ρa ψya : ℝ} (hD : msvDen β σ κ φπ φy ρa ≠ 0) :
    techYgapCoef β σ κ φπ φy ρa ψya + ψya = ψya * techOutputCoef β σ κ φπ φy ρa := by
  unfold techYgapCoef techOutputCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- **Output after a technology shock** (Galí 2015, p. 72): with
`y_t = ỹ_t + y^n_t` and `y^n_t = ψ_ya a_t + ψ_y`, the equilibrium output is
`y_t = ψ_y + ψ_ya κ (φ_π − ρ_a) Λ_a a_t`. -/
theorem technology_output {β σ κ ρ φπ φy ρa ψya ψy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρa < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v a ygap infl i y : ℕ → Ω → ℝ}
    (hav : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hrn : ∀ t, rn t = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t)
    (hyn : ∀ t, yhatn t = ψya • a t) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hy : ∀ t, y t = ygap t + DIS.natOutput ψya ψy a t) (t : ℕ) :
    y t = (fun _ => ψy) + (ψya * techOutputCoef β σ κ φπ φy ρa) • a t := by
  obtain ⟨h1, -⟩ := technology_shock 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hav hab hrn hyn hv0
    he ha hb hba hbb
  rw [hy, h1, DIS.natOutput, ← techOutput_eq (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne',
    add_smul]
  abel

/-- The corrected employment coefficient: `ψ_ya κ (φ_π − ρ_a) Λ_a − 1`
divided by `1 − α` equals `techNCoef` (Galí 2015, p. 72, correction C3-3),
when `ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)`. -/
theorem techNCoef_eq {β σ κ φπ φy ρa φ α : ℝ} (hD : msvDen β σ κ φπ φy ρa ≠ 0)
    (hd : σ * (1 - α) + φ + α ≠ 0) (hα : 1 - α ≠ 0) :
    (DIS.psiYA σ φ α * techOutputCoef β σ κ φπ φy ρa - 1) / (1 - α)
      = techNCoef β σ κ φπ φy ρa φ α := by
  unfold DIS.psiYA techOutputCoef techNCoef msvLambda
  field_simp
  unfold msvDen
  ring

/-- **Employment after a technology shock, corrected** (Galí 2015, p. 72,
correction C3-3): with `y_t = ỹ_t + ψ_ya a_t + ψ_y`,
`ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)` and the first-order production relation
(14) `(1 − α) n_t = y_t − a_t`, employment is `n_t = ψ_y/(1 − α) + c_n a_t`
with
`c_n = Λ_a [(1 − σ) κ (φ_π − ρ_a)/(σ (1 − α) + φ + α) − (φ_y + σ (1 − ρ_a))(1 − βρ_a)/(1 − α)]`. -/
theorem technology_employment {β σ κ ρ φπ φy ρa ψy φ α : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρa < 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v a ygap infl i y n : ℕ → Ω → ℝ}
    (hav : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hrn : ∀ t, rn t = (fun _ => ρ) - (σ * (1 - ρa) * DIS.psiYA σ φ α) • a t)
    (hyn : ∀ t, yhatn t = DIS.psiYA σ φ α • a t) (hv0 : ∀ t, v t = 0)
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hy : ∀ t, y t = ygap t + DIS.natOutput (DIS.psiYA σ φ α) ψy a t)
    (hn : ∀ t, n t = (1 - α)⁻¹ • (y t - a t)) (t : ℕ) :
    n t = (fun _ => ψy / (1 - α)) + techNCoef β σ κ φπ φy ρa φ α • a t := by
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne'
  have hd : σ * (1 - α) + φ + α ≠ 0 := by nlinarith
  have hα : 1 - α ≠ 0 := by linarith
  rw [hn, technology_output 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hav hab hrn hyn hv0 he ha hb hba
    hbb hy t, ← techNCoef_eq hD hd hα]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **The printed employment formula is wrong** (Galí 2015, p. 72, C3-3): the
corrected coefficient minus the printed one is
`−α/(1 − α) · (φ_y + σ (1 − ρ_a))(1 − βρ_a) Λ_a`. -/
theorem techNCoef_sub_printed (β σ κ φπ φy ρa φ α : ℝ) (hα : 1 - α ≠ 0) :
    techNCoef β σ κ φπ φy ρa φ α - techNCoefPrinted β σ κ φπ φy ρa φ α
      = -(α / (1 - α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa) * msvLambda β σ κ φπ φy ρa)) := by
  unfold techNCoef techNCoefPrinted
  field_simp
  ring

/-- Galí (2015), p. 72, C3-3: the printed and corrected employment
coefficients differ whenever `α ≠ 0` (with `ρ_a < 1`, `0 < β < 1`, `σ > 0`,
`φ_y ≥ 0` and `Λ_a ≠ 0`). -/
theorem techNCoef_ne_printed {β σ κ φπ φy ρa φ α : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hα : α ≠ 0) (hα1 : α < 1)
    (hL : msvLambda β σ κ φπ φy ρa ≠ 0) :
    techNCoef β σ κ φπ φy ρa φ α ≠ techNCoefPrinted β σ κ φπ φy ρa φ α := by
  intro h
  have e := techNCoef_sub_printed β σ κ φπ φy ρa φ α (by linarith)
  rw [h, sub_self] at e
  have hX : 0 < (φy + σ * (1 - ρa)) * (1 - β * ρa) := by
    apply mul_pos
    · nlinarith
    · nlinarith
  have hne : α / (1 - α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa) * msvLambda β σ κ φπ φy ρa)
      ≠ 0 := by
    apply mul_ne_zero (div_ne_zero hα (by linarith)) (mul_ne_zero hX.ne' hL)
  exact hne (by linarith)

/-- **Correction C3-4** (Galí 2015, p. 72): if `φ_π > ρ_a` (and `ρ_a < 1`),
then `κ (φ_π − ρ_a) Λ_a ∈ (0, 1)`; so output rises after a technology
improvement, but by less than natural output. -/
theorem techOutputCoef_mem {β σ κ φπ φy ρa : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hρπ : ρa < φπ) :
    0 < techOutputCoef β σ κ φπ φy ρa ∧ techOutputCoef β σ κ φπ φy ρa < 1 := by
  have hbr : 0 < 1 - β * ρa := by nlinarith
  have hA : 0 < (1 - β * ρa) * (σ * (1 - ρa) + φy) := by
    apply mul_pos hbr; nlinarith
  have hB : 0 < κ * (φπ - ρa) := mul_pos hκ (by linarith)
  have hD : 0 < msvDen β σ κ φπ φy ρa := by unfold msvDen; linarith
  unfold techOutputCoef msvLambda
  rw [mul_one_div]
  refine ⟨div_pos hB hD, ?_⟩
  rw [div_lt_one hD]
  unfold msvDen
  linarith

/-- **Counterexample to the printed claim** (Galí 2015, p. 72, C3-4): with
`φ_π = 0`, `φ_y = 20`, `ρ_a = 0.9`, `β = 0.99`, `σ = 1`, `κ = 0.1717`,
condition (28) holds, yet `κ (φ_π − ρ_a) Λ_a < 0`: output **falls** after a
technology improvement. -/
theorem techOutputCoef_counterexample :
    0 < (0.1717 : ℝ) * (0 - 1) + (1 - 0.99) * 20 ∧
      techOutputCoef 0.99 1 0.1717 0 20 0.9 < 0 := by
  unfold techOutputCoef msvLambda msvDen
  norm_num

/-- Galí (2015), p. 72, C3-4: the claim also fails at the boundary `ρ_a = 1`,
`φ_y = 0` (allowed in the book's `ρ_a ∈ [0, 1]`): the coefficient equals 1. -/
theorem techOutputCoef_unit_root {β σ κ φπ : ℝ} (hκ : κ ≠ 0) (hφπ : φπ ≠ 1) :
    techOutputCoef β σ κ φπ 0 1 = 1 := by
  have : κ * (φπ - 1) ≠ 0 := mul_ne_zero hκ (sub_ne_zero.mpr hφπ)
  unfold techOutputCoef msvLambda msvDen
  field_simp
  ring

/-- Galí (2015), p. 72: with `Λ_a > 0`, `0 ≤ α < 1` and `σ (1 − α) + φ + α > 0`,
employment falls after a technology improvement if and only if
`(1 − σ) κ (φ_π − ρ_a)(1 − α) < (σ (1 − α) + φ + α)(φ_y + σ (1 − ρ_a))(1 − βρ_a)`. -/
theorem techNCoef_neg_iff {β σ κ φπ φy ρa φ α : ℝ} (hL : 0 < msvLambda β σ κ φπ φy ρa)
    (hα1 : α < 1) (hd : 0 < σ * (1 - α) + φ + α) :
    techNCoef β σ κ φπ φy ρa φ α < 0 ↔
      (1 - σ) * κ * (φπ - ρa) * (1 - α)
        < (σ * (1 - α) + φ + α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa)) := by
  have h1α : 0 < 1 - α := by linarith
  unfold techNCoef
  rw [mul_neg_iff]
  have key : (1 - σ) * κ * (φπ - ρa) / (σ * (1 - α) + φ + α)
      - (φy + σ * (1 - ρa)) * (1 - β * ρa) / (1 - α)
      = ((1 - σ) * κ * (φπ - ρa) * (1 - α)
        - (σ * (1 - α) + φ + α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa)))
        / ((σ * (1 - α) + φ + α) * (1 - α)) := by
    field_simp
  rw [key]
  have hp : 0 < (σ * (1 - α) + φ + α) * (1 - α) := mul_pos hd h1α
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · rw [div_neg_iff] at h
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · linarith
      · linarith
    · linarith
  · intro h
    exact Or.inl ⟨hL, div_neg_of_neg_of_pos (by linarith) hp⟩

/-- Galí (2015), p. 72: `σ ≥ 1` is sufficient for employment to fall after a
technology improvement, provided `φ_π ≥ ρ_a` (the book omits this condition;
see C3-4), with `ρ_a < 1`, `α < 1`, `φ ≥ 0`. -/
theorem techNCoef_neg_of_one_le_sigma {β σ κ φπ φy ρa φ α : ℝ} (hσ : 1 ≤ σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hρπ : ρa ≤ φπ)
    (hφ : 0 ≤ φ) (hα1 : α < 1) : techNCoef β σ κ φπ φy ρa φ α < 0 := by
  have hbr : 0 < 1 - β * ρa := by nlinarith
  have hA : 0 < (1 - β * ρa) * (σ * (1 - ρa) + φy) := by
    apply mul_pos hbr; nlinarith
  have hD : 0 < msvDen β σ κ φπ φy ρa := by
    unfold msvDen; have := mul_nonneg hκ.le (sub_nonneg.mpr hρπ); linarith
  have hL : 0 < msvLambda β σ κ φπ φy ρa := one_div_pos.mpr hD
  have hd : 0 < σ * (1 - α) + φ + α := by nlinarith
  rw [techNCoef_neg_iff hL hα1 hd]
  have h1 : (1 - σ) * κ * (φπ - ρa) * (1 - α) ≤ 0 := by
    have : 0 ≤ κ * (φπ - ρa) * (1 - α) :=
      mul_nonneg (mul_nonneg hκ.le (sub_nonneg.mpr hρπ)) (by linarith)
    nlinarith
  have h2 : 0 < (σ * (1 - α) + φ + α) * ((φy + σ * (1 - ρa)) * (1 - β * ρa)) := by
    apply mul_pos hd; nlinarith
  linarith

/-- Galí (2015), p. 72: employment also falls when `φ_y` is large enough:
precisely, whenever `(1 − σ) κ (φ_π − ρ_a)(1 − α) ≤ (σ (1 − α) + φ + α) φ_y (1 − βρ_a)`,
which holds for all sufficiently large `φ_y` (with `φ_π ≥ ρ_a`, `ρ_a < 1`). -/
theorem techNCoef_neg_of_phiy_large {β σ κ φπ φy ρa φ α : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρa < 1) (hρπ : ρa ≤ φπ)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlarge : (1 - σ) * κ * (φπ - ρa) * (1 - α) ≤ (σ * (1 - α) + φ + α) * φy * (1 - β * ρa)) :
    techNCoef β σ κ φπ φy ρa φ α < 0 := by
  have hbr : 0 < 1 - β * ρa := by nlinarith
  have hA : 0 < (1 - β * ρa) * (σ * (1 - ρa) + φy) := by
    apply mul_pos hbr; nlinarith
  have hD : 0 < msvDen β σ κ φπ φy ρa := by
    unfold msvDen; have := mul_nonneg hκ.le (sub_nonneg.mpr hρπ); linarith
  have hL : 0 < msvLambda β σ κ φπ φy ρa := one_div_pos.mpr hD
  have hd : 0 < σ * (1 - α) + φ + α := by nlinarith
  rw [techNCoef_neg_iff hL hα1 hd]
  have h2 : 0 < (σ * (1 - α) + φ + α) * (σ * (1 - ρa) * (1 - β * ρa)) := by
    apply mul_pos hd; apply mul_pos _ hbr; nlinarith
  nlinarith

end Gali.BasicNewKeynesianModel.ShockResponses
