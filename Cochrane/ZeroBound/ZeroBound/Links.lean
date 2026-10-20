/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.Covid
import ZeroBound.FutureSelection
import ZeroBound.Gabaix
import ZeroBound.ForwardGuidance
import ZeroBound.Multipliers
import ZeroBound.ZLBWelfare

/-!
# Links between the sections of Chapters 20–21

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, pp. 465–485 (and §5.7.1,
p. 165, for the discrete-to-continuous-time limit). The discrete-time sections (§20.1 peg,
§20.2.1 rule with a bound, §20.2.6 Gabaix, Ch. 21) and the continuous-time sections (§§20.2.2–
20.2.5, Werning's model, and §20.3 welfare) were formalised separately; this module proves how
their overlapping objects relate.

* Roots. The discrete roots (5.6) of `ZLBPeg` with period length `h` (`β = 1 − ρh`, slopes
  `σh`, `κh`) are `λ₁ = 1 + h·scaledRoot` exactly (`lam1_scaled_eq`, `lam2_scaled_eq`), and
  `(λ₁ − 1)/h → λ^b`, `(λ₂ − 1)/h → −λ^f`, the continuous-time roots of `ContinuousTimeNK`
  (`tendsto_lam1_scaled`, `tendsto_lam2_scaled`); the per-period decay `λ₁^{−n}` over `n`
  periods of length `t/n` tends to `e^{−λ^b t}` (`tendsto_peg_decay`).
* The indeterminate peg. Under perfect foresight every bounded `ZLBPeg` equilibrium is
  `π_t − ī = λ₁^{−t}(π₀ − ī)` (`peg_pf_path`), a one-parameter family like the continuous-time
  family `WerningModel.bdd_path_iff`; with the same initial inflation the discrete equilibria
  converge to the continuous-time one (`peg_paths_converge`). Both families are uncountable
  (`ZLBPeg.peg_continuum`, `werning_continuum`).
* Fiscal selection. The discrete impact coefficient `1 − ρ/λ₁` of
  `ZLBPeg.fiscal_unexpected_inflation`, per unit of time, tends to the coefficient `r + λ^b` of
  `ZLBSelection.jump_eq_fiscal` (`tendsto_peg_impact`); in the frictionless limit it is `1`, the
  coefficient of `Covid.fiscal_news_only_unexpected` (`fiscal_impact_frictionless`).
* Future selection. The continuous-time counterpart of `FutureSelection.future_selection` and
  `ZLBRule.fig203_selection`: an active rule after the trap selects the `π_T = 0` member of the
  Werning family (`werning_future_selection`).
* Gabaix. At `M = M^f = 1` the Gabaix matrix is the peg matrix, the determinacy condition fails
  and the roots straddle the unit circle (`gabaix_rational_eq_peg`, `gabaixEq_rational_iff`,
  `gabaix_rational_straddle`).
* The lower-bound steady state. `Π_L = β` (`ZLBWelfare.zlb_steady_state`) is the fixed point of
  the Chapter 16 map at the bound (`map46_fixed_beta_iff`, `zlb_fixed_point_eq_beta`), and its
  logarithm is the zero-bound steady state `−u` of `ZLBRule` with natural rate `u = −log β`
  (`zlb_steady_log`).
-/

namespace Cochrane.ZeroBound.Links

open Filter Topology
open Cochrane.ZeroBound

/-! ## The roots: discrete (5.6) and continuous time -/

/-- Cochrane (2023), §5.7.1, p. 165 (restated from the Cochrane Chapter 5 project): the scaled
root `(−ρ + σκh + √((ρ − σκh)² + 4σκ))/2`, a continuous function of the period length `h`. -/
noncomputable def scaledRoot (ρ σ κ h : ℝ) : ℝ :=
  (-ρ + σ * κ * h + Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2

/-- Cochrane (2023), eq. (5.6), p. 119 and §5.7.1, p. 165: with period length `h > 0`
(`β = 1 − ρh`, IS slope `σh`, Phillips-curve slope `κh`) the peg root of `ZLBPeg` is exactly
`λ₁ = 1 + h·scaledRoot ρ σ κ h`. -/
theorem lam1_scaled_eq {ρ σ κ h : ℝ} (hh : 0 < h) :
    ZLBPeg.lam1 (1 - ρ * h) (σ * h) (κ * h) = 1 + h * scaledRoot ρ σ κ h := by
  have hd : discQ (1 + (1 - ρ * h) + σ * h * (κ * h)) (1 - ρ * h) =
      h ^ 2 * ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by
    unfold discQ
    ring
  rw [ZLBPeg.lam1, hd, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le, scaledRoot]
  ring

/-- Cochrane (2023), eq. (5.6), p. 119 and §5.7.1, p. 165: with period length `h > 0` the stable
root of `ZLBPeg` is `λ₂ = 1 + h(−ρ + σκh − √((ρ − σκh)² + 4σκ))/2`. -/
theorem lam2_scaled_eq {ρ σ κ h : ℝ} (hh : 0 < h) :
    ZLBPeg.lam2 (1 - ρ * h) (σ * h) (κ * h) =
      1 + h * ((-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2) := by
  have hd : discQ (1 + (1 - ρ * h) + σ * h * (κ * h)) (1 - ρ * h) =
      h ^ 2 * ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by
    unfold discQ
    ring
  rw [ZLBPeg.lam2, hd, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le]
  ring

/-- Cochrane (2023), §5.7.1, p. 165 and p. 475: at `h = 0` the scaled root is the
continuous-time root `λ^b = (√(ρ² + 4κσ) − ρ)/2` of `ContinuousTimeNK`. -/
theorem scaledRoot_zero (ρ σ κ : ℝ) : scaledRoot ρ σ κ 0 = ContinuousTimeNK.lamb ρ κ σ := by
  rw [scaledRoot, ContinuousTimeNK.lamb]
  simp only [mul_zero, add_zero, sub_zero]
  rw [show 4 * (σ * κ) = 4 * κ * σ by ring]
  ring

/-- Cochrane (2023), §5.7.1, p. 165 (the scaled root is continuous in `h`). -/
theorem continuous_scaledRoot (ρ σ κ : ℝ) : Continuous (scaledRoot ρ σ κ) := by
  unfold scaledRoot
  fun_prop

/-- Cochrane (2023), §5.7.1, p. 165 (tool): for `σκ > 0` the scaled root is positive. -/
theorem scaledRoot_pos {ρ σ κ : ℝ} (ha : 0 < σ * κ) (h : ℝ) : 0 < scaledRoot ρ σ κ h := by
  unfold scaledRoot
  have hlt : |ρ - σ * κ * h| < Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have := le_abs_self (ρ - σ * κ * h)
  linarith

/-- Cochrane (2023), (5.6), p. 119 (§20.1, p. 467) → p. 475 (**discrete → continuous time**): as
the period length `h → 0⁺`, `(λ₁ − 1)/h` converges to the continuous-time root `λ^b` of
`ContinuousTimeNK` (the discrete unstable root `λ₁ > 1` is the per-period decay factor of the
peg equilibria, `λ^b` their continuous-time decay rate). -/
theorem tendsto_lam1_scaled (ρ σ κ : ℝ) :
    Tendsto (fun h => (ZLBPeg.lam1 (1 - ρ * h) (σ * h) (κ * h) - 1) / h) (𝓝[>] 0)
      (𝓝 (ContinuousTimeNK.lamb ρ κ σ)) := by
  rw [← scaledRoot_zero]
  refine ((continuous_scaledRoot ρ σ κ).tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  rw [lam1_scaled_eq hh]
  field_simp
  ring

/-- Cochrane (2023), (5.6), p. 119 → p. 475: as `h → 0⁺`, `(λ₂ − 1)/h` converges to minus the
continuous-time root `λ^f` of `ContinuousTimeNK`. -/
theorem tendsto_lam2_scaled (ρ σ κ : ℝ) :
    Tendsto (fun h => (ZLBPeg.lam2 (1 - ρ * h) (σ * h) (κ * h) - 1) / h) (𝓝[>] 0)
      (𝓝 (-ContinuousTimeNK.lamf ρ κ σ)) := by
  have hc : Continuous fun h : ℝ =>
      (-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2 := by fun_prop
  have h0 : (fun h : ℝ =>
      (-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2) 0 =
      -ContinuousTimeNK.lamf ρ κ σ := by
    simp only [ContinuousTimeNK.lamf, mul_zero, add_zero, sub_zero]
    rw [show 4 * (σ * κ) = 4 * κ * σ by ring]
    ring
  rw [← h0]
  refine (hc.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  rw [lam2_scaled_eq hh]
  field_simp
  ring

/-- Cochrane (2023), §20.1, p. 467 (peg equilibria decay like `λ₁^{−j}` per period) → p. 475
(`WerningModel.homog_bdd`: decay `e^{−λ^b t}`): over a fixed time `t > 0` cut into `n` periods
of length `t/n`, the discrete decay factor `λ₁^{−n}` converges to `e^{−λ^b t}` (restated from
the Cochrane Chapter 5 project). -/
theorem tendsto_peg_decay {ρ σ κ t : ℝ} (ha : 0 < σ * κ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (ZLBPeg.lam1 (1 - ρ * (t / n)) (σ * (t / n)) (κ * (t / n)))⁻¹ ^ n)
      atTop (𝓝 (Real.exp (-(ContinuousTimeNK.lamb ρ κ σ * t)))) := by
  have hgt : Tendsto (fun n : ℕ => scaledRoot ρ σ κ (t / n)) atTop
      (𝓝 (ContinuousTimeNK.lamb ρ κ σ)) := by
    rw [← scaledRoot_zero]
    exact ((continuous_scaledRoot ρ σ κ).tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hup : Tendsto (fun n : ℕ => t * scaledRoot ρ σ κ (t / n)) atTop
      (𝓝 (t * ContinuousTimeNK.lamb ρ κ σ)) := hgt.const_mul t
  have hlo : Tendsto (fun n : ℕ => t * scaledRoot ρ σ κ (t / n) /
      (1 + t / n * scaledRoot ρ σ κ (t / n))) atTop (𝓝 (t * ContinuousTimeNK.lamb ρ κ σ)) := by
    have hd : Tendsto (fun n : ℕ => 1 + t / n * scaledRoot ρ σ κ (t / n)) atTop
        (𝓝 (1 + 0 * ContinuousTimeNK.lamb ρ κ σ)) :=
      tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat t).mul hgt)
    rw [zero_mul, add_zero] at hd
    have := hup.div hd one_ne_zero
    rw [div_one] at this
    exact this
  have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 + t / n * scaledRoot ρ σ κ (t / n)))
      atTop (𝓝 (t * ContinuousTimeNK.lamb ρ κ σ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hy : 0 < t / n * scaledRoot ρ σ κ (t / n) :=
        mul_pos (div_pos ht hn') (scaledRoot_pos ha _)
      have hl := Real.one_sub_inv_le_log_of_pos
        (by linarith : (0 : ℝ) < 1 + t / n * scaledRoot ρ σ κ (t / n))
      have e : t * scaledRoot ρ σ κ (t / n) / (1 + t / n * scaledRoot ρ σ κ (t / n)) =
          n * (1 - (1 + t / n * scaledRoot ρ σ κ (t / n))⁻¹) := by
        have h1 : (1 + t / n * scaledRoot ρ σ κ (t / n)) ≠ 0 := by linarith
        have hty : t * scaledRoot ρ σ κ (t / n) = n * (t / n * scaledRoot ρ σ κ (t / n)) := by
          field_simp
        rw [hty, mul_div_assoc]
        congr 1
        generalize t / n * scaledRoot ρ σ κ (t / n) = y at h1 ⊢
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hl hn'.le
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hy : 0 < t / n * scaledRoot ρ σ κ (t / n) :=
        mul_pos (div_pos ht hn') (scaledRoot_pos ha _)
      have hl := Real.log_le_sub_one_of_pos
        (by linarith : (0 : ℝ) < 1 + t / n * scaledRoot ρ σ κ (t / n))
      have e : t * scaledRoot ρ σ κ (t / n) =
          n * (1 + t / n * scaledRoot ρ σ κ (t / n) - 1) := by
        rw [add_sub_cancel_left]
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hl hn'.le
  have hexp := (Real.continuous_exp.tendsto _).comp hlog.neg
  rw [show -(ContinuousTimeNK.lamb ρ κ σ * t) = -(t * ContinuousTimeNK.lamb ρ κ σ) by ring]
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < 1 + t / n * scaledRoot ρ σ κ (t / n) := by
    have := mul_pos (div_pos ht hn') (scaledRoot_pos (ρ := ρ) ha (t / n))
    linarith
  rw [lam1_scaled_eq (div_pos ht hn'), inv_pow, ← Real.exp_log (pow_pos hpos n), Real.log_pow,
    ← Real.exp_neg]
  rfl

/-! ## The indeterminate peg: discrete and continuous families -/

/-- Cochrane (2023), §20.1, p. 467, under perfect foresight: every bounded equilibrium at the
peg is `π_t − ī = λ₁^{−t}(π₀ − ī)`, a one-parameter family indexed by `π₀` (the discrete
counterpart of the continuous-time family `WerningModel.bdd_path_iff`, p. 475). -/
theorem peg_pf_path {β σ κ ibar : ℝ} (hβ : 0 < β) (hσκ : 0 < σ * κ) {x π : ℕ → Unit → ℝ}
    (hbx : BoundedProc x) (hbπ : BoundedProc π) (h : ZLBPeg.PegEq perfectForesight β σ κ ibar x π)
    (t : ℕ) : π t () - ibar = (ZLBPeg.lam1 β σ κ)⁻¹ ^ t * (π 0 () - ibar) := by
  have hl : ZLBPeg.lam1 β σ κ ≠ 0 := by linarith [ZLBPeg.one_lt_lam1 hβ hσκ]
  induction t with
  | zero => simp
  | succ t ih =>
    have hr := ZLBPeg.peg_pi_rec perfectForesight hβ hσκ hbx hbπ h t ()
    change π t () - ibar = ZLBPeg.lam1 β σ κ * (π (t + 1) () - ibar) at hr
    have hs : π (t + 1) () - ibar = (ZLBPeg.lam1 β σ κ)⁻¹ * (π t () - ibar) := by
      rw [hr]
      field_simp
    rw [hs, ih, pow_succ]
    ring

/-- Cochrane (2023), §20.1, p. 467 → §20.2.2, p. 475 (**the discrete peg converges to the
continuous-time peg**): take the peg model with period length `t/n` (`β = 1 − ρt/n`, slopes
`σt/n`, `κt/n`), and for each `n` a bounded perfect-foresight equilibrium with initial inflation
`ī + c`. Let `(x, π)` be a bounded path of the continuous-time model (20.5)–(20.6) at the peg with
no shocks and `π₀ = c`. Then inflation after `n` periods (time `t`) converges to `π_t`:
`π^{(n)}_n − ī → π_t = e^{−λ^b t}c`. -/
theorem peg_paths_converge {ρ σ κ t ibar c : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 < t)
    {X P : ℕ → ℕ → Unit → ℝ}
    (hP : ∀ n : ℕ, 0 < n → ZLBPeg.PegEq perfectForesight (1 - ρ * (t / n)) (σ * (t / n))
      (κ * (t / n)) ibar (X n) (P n) ∧ BoundedProc (X n) ∧ BoundedProc (P n))
    (h0 : ∀ n, P n 0 () = ibar + c) {S : Set ℝ} (hS : S.Countable) {x π : ℝ → ℝ}
    (hc : WerningModel.IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (fun _ => 0) S x π)
    (hxb : WerningModel.BddOnIci x) (hπb : WerningModel.BddOnIci π) (hπ0 : π 0 = c) :
    Tendsto (fun n => P n n () - ibar) atTop (𝓝 (π t)) := by
  have hdec := tendsto_peg_decay (ρ := ρ) (mul_pos hσ hκ) ht
  rw [(WerningModel.homog_bdd hσ hκ hS hc hxb hπb t ht.le).1, hπ0]
  have hsmall : ∀ᶠ n : ℕ in atTop, ρ * (t / n) < 1 := by
    have hlim : Tendsto (fun n : ℕ => ρ * (t / n)) atTop (𝓝 (ρ * 0)) :=
      (tendsto_const_div_atTop_nhds_zero_nat t).const_mul ρ
    rw [mul_zero] at hlim
    exact hlim.eventually (gt_mem_nhds one_pos)
  refine (hdec.mul_const c).congr' ?_
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hβ : 0 < 1 - ρ * (t / n) := by linarith
  have hσκ : 0 < σ * (t / n) * (κ * (t / n)) := by positivity
  obtain ⟨hpeg, hbx, hbπ⟩ := hP n hn0
  have := peg_pf_path hβ hσκ hbx hbπ hpeg n
  rw [this, h0]
  ring

/-- Cochrane (2023), §20.2.2, pp. 474–475 (the continuous-time counterpart of
`ZLBPeg.peg_continuum`, p. 467): the bounded paths of the zero-bound experiment form an
uncountable set (they are indexed injectively by `π_T`). -/
theorem werning_continuum {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) :
    ¬ {p : (ℝ → ℝ) × (ℝ → ℝ) | WerningModel.IsPath σ ρ κ (fun _ => 0)
      (WerningModel.trapStep u T) (WerningModel.trapStep g T) {T} p.1 p.2 ∧
      WerningModel.BddOnIci p.1 ∧ WerningModel.BddOnIci p.2}.Countable := by
  intro hc
  let f : ℝ → (ℝ → ℝ) × (ℝ → ℝ) := fun c =>
    (WerningModel.wX σ κ ρ T u g c, WerningModel.wPi σ κ ρ T u g c)
  have hmaps : Set.MapsTo f Set.univ {p : (ℝ → ℝ) × (ℝ → ℝ) | WerningModel.IsPath σ ρ κ
      (fun _ => 0) (WerningModel.trapStep u T) (WerningModel.trapStep g T) {T} p.1 p.2 ∧
      WerningModel.BddOnIci p.1 ∧ WerningModel.BddOnIci p.2} := fun c _ =>
    (WerningModel.bdd_path_iff hκ hσ).2 ⟨c, fun _ _ => ⟨rfl, rfl⟩⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    have := congrFun (congrArg Prod.snd h) T
    simpa [f, WerningModel.wPi_T hκ hσ] using this
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-! ## Fiscal selection: discrete and continuous impact coefficients -/

/-- Cochrane (2023), §20.1, p. 469 (`ZLBPeg.fiscal_unexpected_inflation`: unexpected inflation
`−(1 − ρ_v/λ₁)ε`) → §20.2.2, p. 476 (`ZLBSelection.jump_eq_fiscal`: inflation jump
`−(r + λ^b)×` the fiscal innovation): with period length `h`, valuation discount
`ρ_v = 1 − rh` and `β = 1 − ρh` in the Phillips curve, the discrete impact coefficient per unit
of time converges to the continuous-time one, `(1 − (1 − rh)/λ₁)/h → r + λ^b` as `h → 0⁺`
(restated from the Cochrane Chapter 5 project). -/
theorem tendsto_peg_impact {ρ σ κ : ℝ} (r : ℝ) (ha : 0 < σ * κ) :
    Tendsto (fun h => (1 - (1 - r * h) / ZLBPeg.lam1 (1 - ρ * h) (σ * h) (κ * h)) / h)
      (𝓝[>] 0) (𝓝 (r + ContinuousTimeNK.lamb ρ κ σ)) := by
  have hg := (continuous_scaledRoot ρ σ κ).tendsto 0
  have hnum : Tendsto (fun h => scaledRoot ρ σ κ h + r) (𝓝 0) (𝓝 (scaledRoot ρ σ κ 0 + r)) :=
    hg.add_const r
  have hden : Tendsto (fun h => 1 + h * scaledRoot ρ σ κ h) (𝓝 0)
      (𝓝 (1 + 0 * scaledRoot ρ σ κ 0)) :=
    tendsto_const_nhds.add (tendsto_id.mul hg)
  rw [zero_mul, add_zero] at hden
  have hlim := hnum.div hden one_ne_zero
  rw [div_one, scaledRoot_zero, add_comm] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < 1 + h * scaledRoot ρ σ κ h := by
    have := mul_pos (Set.mem_Ioi.mp hh) (scaledRoot_pos (ρ := ρ) ha h)
    linarith
  change (scaledRoot ρ σ κ h + r) / (1 + h * scaledRoot ρ σ κ h) = _
  rw [lam1_scaled_eq hh]
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  have hp' : 1 + h * scaledRoot ρ σ κ h ≠ 0 := hp.ne'
  rw [eq_div_iff hh', div_mul_eq_mul_div, eq_comm, sub_eq_iff_eq_add, ← add_div,
    eq_div_iff hp']
  ring

/-- Cochrane (2023), §20.1, p. 469 → Ch. 21, p. 491 (`Covid.fiscal_news_only_unexpected`: in the
frictionless model unexpected inflation is `−ε` one for one): as prices become flexible
(`κ → ∞`), the impact coefficient `1 − ρ/λ₁` of `ZLBPeg.fiscal_unexpected_inflation` tends to
`1`. -/
theorem fiscal_impact_frictionless {β σ ρ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ => 1 - ρ / ZLBPeg.lam1 β σ κ) atTop (𝓝 1) := by
  have hlow : Tendsto (fun κ => (1 + β + σ * κ) / 2) atTop atTop := by
    refine Tendsto.atTop_div_const two_pos ?_
    exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hσ)
  have hlam : Tendsto (fun κ => ZLBPeg.lam1 β σ κ) atTop atTop := by
    refine tendsto_atTop_mono (fun κ => ?_) hlow
    unfold ZLBPeg.lam1
    linarith [Real.sqrt_nonneg (discQ (1 + β + σ * κ) β)]
  have h0 : Tendsto (fun κ => ρ / ZLBPeg.lam1 β σ κ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlam
  simpa using h0.const_sub 1

/-! ## Future selection in continuous time -/

/-- Cochrane (2023), (20.7), p. 474, with §20.2.2, p. 475 (the continuous-time counterpart of
`FutureSelection.future_selection` and `ZLBRule.fig203_selection`, §20.2.1, p. 472): in the
zero-bound experiment, if the interest rate is pegged at zero during the trap and follows the
active rule `i = φπ` (`φ > 1`) from `T` on, then every bounded path is the `π_T = 0` member of
the Werning family `(wX 0, wPi 0)`: the expected future rule selects the equilibrium. -/
theorem werning_future_selection {σ κ ρ φ T u g : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hφ : 1 < φ) (hT : 0 ≤ T) {x π : ℝ → ℝ}
    (h : WerningModel.IsPath σ ρ κ (fun t => if t < T then 0 else φ * π t)
      (WerningModel.trapStep u T) (WerningModel.trapStep g T) {T} x π)
    (hx : WerningModel.BddOnIci x) (hπ : WerningModel.BddOnIci π) :
    ∀ t, 0 ≤ t → π t = WerningModel.wPi σ κ ρ T u g 0 t ∧
      x t = WerningModel.wX σ κ ρ T u g 0 t := by
  obtain ⟨hxc, hπc, hd⟩ := h
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨Kπ, hKπ⟩ := hπ
  have hsel := WerningModel.eq20_7_selects (istar := fun _ => 0)
    (u := WerningModel.trapStep u T) (g := WerningModel.trapStep g T) (xs := fun _ => 0)
    (πs := fun _ => 0) (Set.countable_singleton T) hσ hκ hρ hφ
    (hxc.mono (Set.Ici_subset_Ici.2 hT)) (hπc.mono (Set.Ici_subset_Ici.2 hT))
    continuousOn_const continuousOn_const
    (fun t ht htS => by
      obtain ⟨a, b⟩ := hd t (lt_of_le_of_lt hT ht) htS
      have hnot : ¬ t < T := not_lt.2 ht.le
      refine ⟨a.congr_deriv ?_, b⟩
      simp only [hnot, ↓reduceIte]
      ring)
    (fun t ht _ => by
      have hnot : ¬ t < T := not_lt.2 ht.le
      simp only [WerningModel.trapStep, hnot, ↓reduceIte]
      exact ⟨(hasDerivAt_const t (0 : ℝ)).congr_deriv (by ring),
        (hasDerivAt_const t (0 : ℝ)).congr_deriv (by ring)⟩)
    Kx Kπ 0 0 (fun t ht => hKx t (hT.trans ht)) (fun t ht => hKπ t (hT.trans ht))
    (fun _ _ => by simp) (fun _ _ => by simp)
  have hpath : WerningModel.IsPath σ ρ κ (fun _ => 0) (WerningModel.trapStep u T)
      (WerningModel.trapStep g T) {T} x π := by
    refine ⟨hxc, hπc, fun t ht htS => ?_⟩
    obtain ⟨a, b⟩ := hd t ht htS
    refine ⟨a.congr_deriv ?_, b⟩
    by_cases htT : t < T
    · simp only [htT, ↓reduceIte]
    · have h0 := (hsel t (not_lt.1 htT)).1
      simp only [htT, ↓reduceIte, h0, mul_zero]
  obtain ⟨πT, hπT⟩ := (WerningModel.bdd_path_iff hκ hσ).1 ⟨hpath, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩
  have h0 : πT = 0 := by
    have := (hπT T hT).1
    rw [WerningModel.wPi_T hκ hσ] at this
    rw [← this]
    exact (hsel T le_rfl).1
  intro t ht
  rw [← h0]
  exact hπT t ht

/-! ## Gabaix at the rational limit is the peg -/

/-- Cochrane (2023), (20.11)–(20.12), p. 482, at `M = M^f = 1` (rational expectations): the
Gabaix matrix is the peg matrix of (5.1)–(5.2), §20.1, p. 467. -/
theorem gabaix_rational_eq_peg (β σ κ : ℝ) :
    Gabaix.gabaixMatrix 1 1 β σ κ = ZLBPeg.pegMatrix β σ κ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gabaix.gabaixMatrix, ZLBPeg.pegMatrix]

/-- Cochrane (2023), (20.11)–(20.12), p. 482 and (5.1)–(5.2), p. 118: at `M = M^f = 1` the Gabaix
model at a peg is the standard new-Keynesian model at a peg, under any `ExpectationSystem`. -/
theorem gabaixEq_rational_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β σ κ ibar : ℝ)
    (x π : ℕ → Ω → ℝ) :
    Gabaix.GabaixEq 𝔼 1 1 β σ κ ibar x π ↔ ZLBPeg.PegEq 𝔼 β σ κ ibar x π := by
  rw [Gabaix.gabaixEq_iff_solves, ZLBPeg.pegEq_iff_solves, gabaix_rational_eq_peg]
  rfl

/-- Cochrane (2023), pp. 482–483 → §20.1, p. 467: at `M = M^f = 1` the Gabaix determinacy
condition `(1 − M)(1 − βM^f) > σκ` reads `0 > σκ` and fails, and correspondingly the roots of the
Gabaix matrix are the (5.6) roots `λ₁`, `λ₂` of `ZLBPeg`, which straddle the unit circle:
`‖λ₂‖ < 1 < ‖λ₁‖` (indeterminacy). -/
theorem gabaix_rational_straddle {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 < σ * κ) :
    ((‖root₁ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ < 1 ∧
      ‖root₂ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ < 1)
        ↔ σ * κ < (1 - 1) * (1 - β * 1)) ∧
      ¬ σ * κ < (1 - 1) * (1 - β * 1) ∧
      root₁ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ)) =
        (ZLBPeg.lam1 β σ κ : ℂ) ∧
      root₂ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ)) =
        (ZLBPeg.lam2 β σ κ : ℂ) ∧
      ‖root₂ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ < 1 ∧
      1 < ‖root₁ (tr2 (Gabaix.gabaixMatrix 1 1 β σ κ)) (det2 (Gabaix.gabaixMatrix 1 1 β σ κ))‖ := by
  refine ⟨Gabaix.gabaix_roots_iff zero_le_one le_rfl zero_le_one le_rfl hβ0 hβ1 hσκ.le, ?_, ?_⟩
  · rw [sub_self, zero_mul]
    exact not_lt.2 hσκ.le
  · rw [gabaix_rational_eq_peg]
    exact ZLBPeg.pegMatrix_roots hβ0 hσκ

/-! ## The lower-bound steady state `Π_L = β` -/

/-- Cochrane (2023), (16.28), p. 379 and §20.3, p. 484, with the global map
`Π' = β(1 + φ(Π))` of `GlobalDynamics.map46` (Woodford (2003), eq. (4.6), p. 125): `β` is a
steady state iff the rule sets the rate to zero there, `φ(β) = 0` (`β ≠ 0`). -/
theorem map46_fixed_beta_iff {β : ℝ} (hβ : β ≠ 0) (φ : ℝ → ℝ) :
    GlobalDynamics.map46 β φ β = β ↔ φ β = 0 := by
  change β * (1 + φ β) = β ↔ φ β = 0
  constructor
  · intro h
    have := mul_left_cancel₀ hβ (h.trans (mul_one β).symm)
    linarith
  · intro h
    rw [h]
    ring

/-- Cochrane (2023), §20.3, p. 484 (E9, `ZLBWelfare.zlb_steady_state`) and (16.28), p. 379: any
steady state of the Chapter 16 map `GlobalDynamics.map46` at which the rule is at the bound,
`φ(Π) = 0`, is the zero-bound steady state `Π_L = β` of §20.3. -/
theorem zlb_fixed_point_eq_beta {β P : ℝ} {φ : ℝ → ℝ} (hfix : GlobalDynamics.map46 β φ P = P)
    (hφ : φ P = 0) : P = β :=
  ZLBWelfare.zlb_steady_state (i := φ P) hfix.symm hφ

/-- Cochrane (2023), §20.2.1, p. 472 (`ZLBRule`, the lower steady state `π = −u` with `i = 0`)
and §20.3, p. 484 (`Π_L = β`): with natural rate `u = −log β` (`β > 0`) and `log β` on the
zero-bound branch, `π = log β` is a steady state of the (20.2) map, the rule is at the bound
there, and `e^{log β} = β(1 + 0)` is the gross steady state `Π_L` of
`ZLBWelfare.zlb_steady_state`. -/
theorem zlb_steady_log {σ κ φ πs β : ℝ} (hφ : 1 < φ) (hσκ : 0 < σ * κ) (hβ : 0 < β)
    (hk : Real.log β ≤ ZLBRule.kink φ πs) :
    ZLBRule.fmap σ κ φ πs (-Real.log β) (Real.log β) = Real.log β ∧
      ZLBRule.rule φ πs (Real.log β) = 0 ∧ Real.exp (Real.log β) = β := by
  have h := (ZLBRule.both_steady (σ := σ) (κ := κ) hφ hσκ (u := -Real.log β)
    (by rwa [neg_neg])).1
  rw [neg_neg] at h
  refine ⟨h, ?_, Real.exp_log hβ⟩
  have := (ZLBRule.kink_iff (π := Real.log β) (by linarith : (0 : ℝ) < φ)).2 hk
  unfold ZLBRule.rule
  exact max_eq_right this

end Cochrane.ZeroBound.Links
