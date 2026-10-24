/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.PolicyRules
import StickyPriceFiscal.LongTermDebt
import StickyPriceFiscal.ActivePassive
import StickyPriceFiscal.NonlinearCT
import StickyPriceFiscal.Sims

/-!
# Links between the sections of Chapter 5

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, pp. 117–181, and Online
Appendix A1 §§1.7–1.13. The sections of Chapter 5 were formalised separately; this module proves
that their overlapping objects agree.

* Innovations: `surprise_eq_innov` (the §5.4 `surprise` is the §5.5 `ΔE_{t+1}`).
* The roots of the new-Keynesian model: with no interest-rate rule the §5.5 roots of the
  `(x, π)` block are the reciprocals of the (5.6) roots (`lamS_lamU_noRule`); the discrete
  roots, with period length `h`, converge to the continuous-time roots of §5.7.1
  (`lam1_scaled_eq`, `lam2_scaled_eq`, `tendsto_lam1_scaled`, `tendsto_lam2_scaled`), and so do
  the impact coefficient and the decay of the peg response (`tendsto_peg_impact`,
  `tendsto_peg_decay`: `FiscalNK`'s `(1 − ρ/λ₁)λ₁^{−t}` against `CTSimple`'s
  `(r + λ₂)e^{−λ₂ t}`); the habit roots of §5.7.6 are the §5.7.1 roots (`habit_roots_eq`).
* The models: the IS and Phillips curves of (5.64)–(5.65) are (5.1)–(5.2) (`redSys_nk`); with
  no policy rules (`θ = 0`, `α = 0`) the §5.5 model is the long-term-debt model (5.17)–(5.21)
  (`redSys_noRule_ltd`) and, with one-period debt, the model (5.15)–(5.16)
  (`redSys_noRule_short`); every such §5.5 equilibrium is the unique §5.2 / §5.1.2 equilibrium
  with the same initial debt (`redEquil_noRule_eq_ltd`, `redEquil_noRule_eq_fiscalNK`).
* Bond returns: `rnOf_succ_eq_rnNext`, `rnSeq_succ_eq_rnOf`.
* Fiscal rules: `debtRoot_eq_gRoot`, `alpha_iff_pf_gRoot` (§5.5 determinacy in `α` is
  `|g| ≤ 1` for the §5.4 root `g = (1 − α)/ρ`), `determinate_region_passive` (in the §5.5
  determinacy region the surplus rule is passive in the §5.4 sense).
* Continuous time: `odeSol_eq_bwdInt` (the §5.4.2 ODE solution is the A1 §1.12 backward
  integral).
-/

namespace Cochrane.StickyPriceFiscal.Links

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Innovations -/

/-- Cochrane (2023), (5.27), p. 135 and (5.58), p. 147: for an adapted process the §5.4
`surprise` `π_{t+1} − E_t π_{t+1}` is the §5.5 innovation `ΔE_{t+1} π_{t+1}`. -/
theorem surprise_eq_innov {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (t : ℕ) :
    SurplusProcess.surprise 𝔼 π t = SharedTools.innov 𝔼 t (π (t + 1)) := by
  rw [SharedTools.innov_succ 𝔼 hπ t]
  rfl

/-! ### The roots of the new-Keynesian model -/

/-- Cochrane (2023), eq. (5.6), p. 119 and A1 §1.9, p. 574: with no interest-rate rule
(`θ_iπ = θ_ix = 0`) the stable and unstable roots of the §5.5 `(x, π)` block are the reciprocals
of the roots (5.6): `λ_s = λ₁⁻¹` and `λ_u = λ₂⁻¹`. -/
theorem lamS_lamU_noRule {P : PolicyRules.Params} (hP : PolicyRules.Standard P)
    (h1 : P.thIpi = 0) (h2 : P.thIx = 0) :
    PolicyRules.lamS P = (NKModel.lam1 P.sigma P.beta P.kappa)⁻¹ ∧
      PolicyRules.lamU P = (NKModel.lam2 P.sigma P.beta P.kappa)⁻¹ := by
  obtain ⟨hσ, hκ, hβ0, -, -, -⟩ := id hP
  have ha := mul_pos hσ hκ
  have hpass : PolicyRules.Passive P := by
    unfold PolicyRules.Passive
    rw [h1, h2]
    linarith
  obtain ⟨-, hU, -, hS, -, -⟩ := PolicyRules.roots_passive hP hpass
  have hroot : ∀ l : ℝ, l ≠ 0 →
      l ^ 2 - (1 + P.beta + P.sigma * P.kappa) * l + P.beta = 0 → PolicyRules.charB P l⁻¹ = 0 := by
    intro l hl hr
    have e : PolicyRules.charB P l⁻¹ =
        (l ^ 2 - (1 + P.beta + P.sigma * P.kappa) * l + P.beta) / (P.beta * l ^ 2) := by
      rw [PolicyRules.charB, PolicyRules.trB_eq, PolicyRules.detB_eq hβ0.ne', h1, h2]
      field_simp
      ring
    rw [e, hr, zero_div]
  have hfac := PolicyRules.charB_factor hP hpass
  have l1 := NKModel.one_lt_lam1 ha hβ0
  have l2p := NKModel.lam2_pos ha hβ0
  have l2 := NKModel.lam2_lt_one ha hβ0
  constructor
  · have h0 := hroot _ (by linarith) (NKModel.lam1_root ha hβ0)
    rw [hfac] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · have : (NKModel.lam1 P.sigma P.beta P.kappa)⁻¹ < 1 := inv_lt_one_of_one_lt₀ l1
      linarith [sub_eq_zero.mp h]
    · exact (sub_eq_zero.mp h).symm
  · have h0 := hroot _ l2p.ne' (NKModel.lam2_root ha hβ0)
    rw [hfac] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact (sub_eq_zero.mp h).symm
    · have : 1 < (NKModel.lam2 P.sigma P.beta P.kappa)⁻¹ := one_lt_inv₀ l2p |>.mpr l2
      linarith [sub_eq_zero.mp h]

/-- Cochrane (2023), §5.7.1, p. 165 and A1 §1.12, p. 579 (tool for the discrete-time limit): the
scaled root `(−ρ + σκh + √((ρ − σκh)² + 4σκ))/2`, a continuous function of the period length
`h`. -/
noncomputable def scaledRoot (ρ σ κ h : ℝ) : ℝ :=
  (-ρ + σ * κ * h + Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2

/-- Cochrane (2023), eq. (5.6), p. 119 and §5.7.1, p. 165: with period length `h > 0`
(`β = 1 − ρh`, IS slope `σh`, Phillips-curve slope `κh`) the unstable root (5.6) is exactly
`λ₁ = 1 + h·scaledRoot ρ σ κ h`. -/
theorem lam1_scaled_eq {ρ σ κ h : ℝ} (hh : 0 < h) :
    NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h) = 1 + h * scaledRoot ρ σ κ h := by
  have hd : (1 + (1 - ρ * h) + σ * h * (κ * h)) ^ 2 - 4 * (1 - ρ * h) =
      h ^ 2 * ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by ring
  rw [NKModel.lam1, hd, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le, scaledRoot]
  ring

/-- Cochrane (2023), eq. (5.6), p. 119 and §5.7.1, p. 165: with period length `h > 0` the
stable root (5.6) is `λ₂ = 1 + h(−ρ + σκh − √((ρ − σκh)² + 4σκ))/2`. -/
theorem lam2_scaled_eq {ρ σ κ h : ℝ} (hh : 0 < h) :
    NKModel.lam2 (σ * h) (1 - ρ * h) (κ * h) =
      1 + h * ((-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2) := by
  have hd : (1 + (1 - ρ * h) + σ * h * (κ * h)) ^ 2 - 4 * (1 - ρ * h) =
      h ^ 2 * ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by ring
  rw [NKModel.lam2, hd, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le]
  ring

/-- Cochrane (2023), §5.7.1, p. 165: at `h = 0` the scaled root is the continuous-time root
`λ₂ = (−ρ + √(ρ² + 4κσ))/2` of `CTSimple`. -/
theorem scaledRoot_zero (ρ σ κ : ℝ) : scaledRoot ρ σ κ 0 = CTSimple.lam2 ρ κ σ := by
  rw [scaledRoot, CTSimple.lam2]
  congr 2
  · ring
  · congr 1
    ring

/-- Cochrane (2023), §5.7.1, p. 165 (the scaled root is continuous in `h`). -/
theorem continuous_scaledRoot (ρ σ κ : ℝ) : Continuous (scaledRoot ρ σ κ) := by
  unfold scaledRoot
  fun_prop

/-- Cochrane (2023), (5.6), p. 119 → §5.7.1, p. 165 (**discrete → continuous time**): as the
period length `h → 0⁺`, `(λ₁ − 1)/h` converges to the continuous-time stable root `λ₂` of
`CTSimple` (the discrete unstable root `λ₁ > 1` is the per-period decay factor of the forward
solution). -/
theorem tendsto_lam1_scaled (ρ σ κ : ℝ) :
    Tendsto (fun h => (NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h) - 1) / h) (𝓝[>] 0)
      (𝓝 (CTSimple.lam2 ρ κ σ)) := by
  rw [← scaledRoot_zero]
  refine ((continuous_scaledRoot ρ σ κ).tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  rw [lam1_scaled_eq hh]
  field_simp
  ring

/-- Cochrane (2023), (5.6), p. 119 → §5.7.1, p. 165: as `h → 0⁺`, `(λ₂ − 1)/h` converges to minus
the continuous-time unstable root `λ₁` of `CTSimple`. -/
theorem tendsto_lam2_scaled (ρ σ κ : ℝ) :
    Tendsto (fun h => (NKModel.lam2 (σ * h) (1 - ρ * h) (κ * h) - 1) / h) (𝓝[>] 0)
      (𝓝 (-CTSimple.lam1 ρ κ σ)) := by
  have hc : Continuous fun h : ℝ =>
      (-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2 := by fun_prop
  have h0 : (fun h : ℝ =>
      (-ρ + σ * κ * h - Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))) / 2) 0 =
      -CTSimple.lam1 ρ κ σ := by
    simp only [CTSimple.lam1, mul_zero, add_zero, sub_zero]
    rw [show 4 * (σ * κ) = 4 * κ * σ by ring]
    ring
  rw [← h0]
  refine (hc.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := (Set.mem_Ioi.mp hh).ne'
  rw [lam2_scaled_eq hh]
  field_simp
  ring

/-- Cochrane (2023), §5.7.1, p. 165 (tool): for `σκ > 0` the scaled root is positive. -/
theorem scaledRoot_pos {ρ σ κ : ℝ} (ha : 0 < σ * κ) (h : ℝ) : 0 < scaledRoot ρ σ κ h := by
  unfold scaledRoot
  have hlt : |ρ - σ * κ * h| < Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have := le_abs_self (ρ - σ * κ * h)
  linarith

/-- Cochrane (2023), Fig. 5.1, pp. 122–123 (`FiscalNK.perm_rise`: impact coefficient
`1 − ρ/λ₁`) → §5.7.1, (5.96), p. 166 (`CTSimple.ct_step_solution`: coefficient `r + λ₂`): with
period length `h`, discount `ρ = 1 − rh` in the flow and `β = 1 − ρ_π h` in the Phillips curve,
`(1 − (1 − rh)/λ₁)/h → r + λ₂` as `h → 0⁺`. -/
theorem tendsto_peg_impact {ρ σ κ : ℝ} (r : ℝ) (ha : 0 < σ * κ) :
    Tendsto (fun h => (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h)
      (𝓝[>] 0) (𝓝 (r + CTSimple.lam2 ρ κ σ)) := by
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

/-- Cochrane (2023), Fig. 5.1, pp. 122–123 (`FiscalNK.perm_rise`: the response decays like
`λ₁^{−j}` per period) → §5.7.1, (5.96), p. 166 (`CTSimple.ct_step_solution`: decay `e^{−λ₂ t}`):
over a fixed time `t > 0` cut into `n` periods of length `t/n`, the discrete decay factor
`λ₁^{−n}` converges to `e^{−λ₂ t}`. -/
theorem tendsto_peg_decay {ρ σ κ t : ℝ} (ha : 0 < σ * κ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (NKModel.lam1 (σ * (t / n)) (1 - ρ * (t / n)) (κ * (t / n)))⁻¹ ^ n)
      atTop (𝓝 (Real.exp (-(CTSimple.lam2 ρ κ σ * t)))) := by
  have hgt : Tendsto (fun n : ℕ => scaledRoot ρ σ κ (t / n)) atTop
      (𝓝 (CTSimple.lam2 ρ κ σ)) := by
    rw [← scaledRoot_zero]
    exact ((continuous_scaledRoot ρ σ κ).tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat t)
  have hup : Tendsto (fun n : ℕ => t * scaledRoot ρ σ κ (t / n)) atTop
      (𝓝 (t * CTSimple.lam2 ρ κ σ)) := hgt.const_mul t
  have hlo : Tendsto (fun n : ℕ => t * scaledRoot ρ σ κ (t / n) /
      (1 + t / n * scaledRoot ρ σ κ (t / n))) atTop (𝓝 (t * CTSimple.lam2 ρ κ σ)) := by
    have hd : Tendsto (fun n : ℕ => 1 + t / n * scaledRoot ρ σ κ (t / n)) atTop
        (𝓝 (1 + 0 * CTSimple.lam2 ρ κ σ)) :=
      tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat t).mul hgt)
    rw [zero_mul, add_zero] at hd
    have := hup.div hd one_ne_zero
    rw [div_one] at this
    exact this
  have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 + t / n * scaledRoot ρ σ κ (t / n)))
      atTop (𝓝 (t * CTSimple.lam2 ρ κ σ)) := by
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
  rw [show -(CTSimple.lam2 ρ κ σ * t) = -(t * CTSimple.lam2 ρ κ σ) by ring]
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < 1 + t / n * scaledRoot ρ σ κ (t / n) := by
    have := mul_pos (div_pos ht hn') (scaledRoot_pos (ρ := ρ) ha (t / n))
    linarith
  rw [lam1_scaled_eq (div_pos ht hn'), inv_pow, ← Real.exp_log (pow_pos hpos n), Real.log_pow,
    ← Real.exp_neg]
  rfl

/-- Cochrane (2023), §5.7.6, (5.124)–(5.125), p. 181 and §5.7.1, p. 165: the habit roots
`μ± = (r ± √(r² + 4σψ))/2` of `Sims.habit_roots` are the continuous-time roots of `CTSimple`
(with `κ ↦ σ`, `σ ↦ ψ`): `μ₊ = λ₁`, `μ₋ = −λ₂`. -/
theorem habit_roots_eq (r σ ψ : ℝ) :
    (r + Real.sqrt (r ^ 2 + 4 * (σ * ψ))) / 2 = CTSimple.lam1 r σ ψ ∧
      (r - Real.sqrt (r ^ 2 + 4 * (σ * ψ))) / 2 = -CTSimple.lam2 r σ ψ := by
  unfold CTSimple.lam1 CTSimple.lam2
  rw [← mul_assoc]
  exact ⟨rfl, by ring⟩

/-! ### The models -/

/-- Cochrane (2023), (5.64)–(5.65), p. 148 and (5.1)–(5.2), p. 118: the IS and Phillips curves of
the §5.5 model are the new-Keynesian model with the rule-implied rate `i = iRule`. -/
theorem redSys_nk {P : PolicyRules.Params} {ei es ui us x p q v : ℕ → Ω → ℝ}
    (h : PolicyRules.RedSys 𝔼 P ei es ui us x p q v) :
    NKModel.NK 𝔼 P.sigma P.beta P.kappa (PolicyRules.iRule P x p ui) x p :=
  ⟨h.1, h.2.1⟩

/-- Cochrane (2023), (5.53), p. 147: with `θ_iπ = θ_ix = 0` the rate is the disturbance,
`i = u_i`. -/
theorem iRule_noRule {P : PolicyRules.Params} (h1 : P.thIpi = 0) (h2 : P.thIx = 0)
    (x p ui : ℕ → Ω → ℝ) : PolicyRules.iRule P x p ui = ui := by
  funext t
  simp [PolicyRules.iRule, h1, h2]

/-- Cochrane (2023), (5.54), p. 147: with `θ_sπ = θ_sx = α = 0` the surplus is the disturbance,
`s̃_{t+1} = u_{s,t+1}`. -/
theorem sNext_noRule {P : PolicyRules.Params} (h3 : P.thSpi = 0) (h4 : P.thSx = 0)
    (h5 : P.alpha = 0) (x p v us : ℕ → Ω → ℝ) (t : ℕ) :
    PolicyRules.sNext P x p v us t = us (t + 1) := by
  simp [PolicyRules.sNext, h3, h4, h5]

/-- Cochrane (2023), (5.73), p. 149 and (5.21), p. 127: the §5.5 bond return is the §5.2
return. -/
theorem rnOf_succ_eq_rnNext (P : PolicyRules.Params) (q : ℕ → Ω → ℝ) (qm1 : Ω → ℝ) (t : ℕ) :
    LongTermDebt.rnOf P.omega q qm1 (t + 1) = PolicyRules.rnNext P q t := rfl

/-- Cochrane (2023), Table 5.1 identities, p. 153 and (5.21), p. 127: the return sequence of the
Table 5.1 identities is the §5.2 return. -/
theorem rnSeq_succ_eq_rnOf (w : ℝ) (q : ℕ → Ω → ℝ) (qm1 : Ω → ℝ) (t : ℕ) :
    PolicyRules.rnSeq w q (t + 1) = LongTermDebt.rnOf w q qm1 (t + 1) := rfl

/-- **The §5.5 model without rules is the §5.2 model** (Cochrane (2023), (5.64)–(5.73),
pp. 148–149 and (5.17)–(5.21), p. 127): with `θ_iπ = θ_ix = θ_sπ = θ_sx = α = 0`, every solution of
the reduced model solves the long-term-debt model with `i = u_i`, `s̃ = u_s`, pre-sample price
`q_{−1} = ω q_0` and pre-sample debt `v_{−1} = ρ v_0 + π_0 + u_{s,0}`. -/
theorem redSys_noRule_ltd {P : PolicyRules.Params} (h1 : P.thIpi = 0) (h2 : P.thIx = 0)
    (h3 : P.thSpi = 0) (h4 : P.thSx = 0) (h5 : P.alpha = 0)
    {ei es ui us x p q v : ℕ → Ω → ℝ} (h : PolicyRules.RedSys 𝔼 P ei es ui us x p q v) :
    LongTermDebt.LTD 𝔼 P.sigma P.beta P.kappa P.rho P.omega ui us (P.rho • v 0 + p 0 + us 0)
      (P.omega • q 0) x p v q (LongTermDebt.rnOf P.omega q (P.omega • q 0)) := by
  obtain ⟨h64, h65, -, h71, h72⟩ := h
  rw [iRule_noRule h1 h2] at h64 h72
  refine ⟨⟨h64, h65⟩, fun t => ?_, ?_, h72, fun t => rfl, rfl⟩
  · rw [h71 t, sNext_noRule h3 h4 h5]
    rfl
  · change _ = _ + (P.omega • q 0 - P.omega • q 0) - _ - _
    rw [sub_self, add_zero]
    abel

/-- **The §5.5 model without rules and with one-period debt is the §5.1.2 model** (Cochrane
(2023), (5.64)–(5.73), pp. 148–149 and (5.15)–(5.16), p. 121): with no rules, `ω = 0` and an
adapted bond price, every solution of the reduced model solves (5.15)–(5.16) with `i = u_i`,
`s̃ = u_s` and `b_0 = ρ v_0 + π_0 + u_{s,0}`. -/
theorem redSys_noRule_short {P : PolicyRules.Params} (h1 : P.thIpi = 0) (h2 : P.thIx = 0)
    (h3 : P.thSpi = 0) (h4 : P.thSx = 0) (h5 : P.alpha = 0) (hω : P.omega = 0)
    {ei es ui us x p q v : ℕ → Ω → ℝ} (h : PolicyRules.RedSys 𝔼 P ei es ui us x p q v)
    (hq : 𝔼.Adapted q) :
    FiscalNK.FTPLNK 𝔼 P.sigma P.beta P.kappa P.rho ui us (P.rho • v 0 + p 0 + us 0) x p v := by
  obtain ⟨h64, h65, -, h71, h72⟩ := h
  rw [iRule_noRule h1 h2] at h64 h72
  refine ⟨⟨h64, h65⟩, fun t => ?_, by abel⟩
  have hr : PolicyRules.rnNext P q t = ui t := by
    rw [← h72 t]
    simp only [PolicyRules.rnNext, hω, zero_smul, zero_sub, map_neg, hq t]
  rw [h71 t, hr, sNext_noRule h3 h4 h5]

/-- **Uniqueness transfer, §5.5 → §5.2** (Cochrane (2023), p. 128 and pp. 148–149): with no
rules, `0 < ρ < 1` and `0 ≤ ω < 1`, a bounded equilibrium of the §5.5 model is the unique
bounded equilibrium of the long-term-debt model (5.17)–(5.21) with the same initial debt: every
bounded equilibrium of (5.17)–(5.21) with `v_{−1} = ρ v_0 + π_0 + u_{s,0}`, `q_{−1} = ω q_0`
coincides with it. -/
theorem redEquil_noRule_eq_ltd {P : PolicyRules.Params} (hP : PolicyRules.Standard P)
    (h1 : P.thIpi = 0) (h2 : P.thIx = 0) (h3 : P.thSpi = 0) (h4 : P.thSx = 0) (h5 : P.alpha = 0)
    (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1) (hω0 : 0 ≤ P.omega) (hω1 : P.omega < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : PolicyRules.Shocks 𝔼 P ei es ui us) {p0 v0 : ℝ}
    {x p q v : ℕ → Ω → ℝ} (h : PolicyRules.RedEquil 𝔼 P ei es ui us p0 v0 x p q v) :
    ∀ x' π' v' q' rn', LongTermDebt.LTD 𝔼 P.sigma P.beta P.kappa P.rho P.omega ui us
      (P.rho • v 0 + p 0 + us 0) (P.omega • q 0) x' π' v' q' rn' → 𝔼.Adapted q' →
      BoundedProc π' → BoundedProc v' → BoundedProc q' →
      x' = x ∧ π' = p ∧ v' = v ∧ q' = q := by
  intro x' π' v' q' rn' hL' haq' hbp' hbv' hbq'
  obtain ⟨hs, -, hap, haq, hav, -, hbp, hbq, hbv, -, -⟩ := h
  obtain ⟨hσ, hκ, hβ, -, -, -⟩ := hP
  obtain ⟨-, -, hui, hus, -, -, ⟨Mi, hMi⟩, ⟨Ms, hMs⟩, -⟩ := hsh
  obtain ⟨Mv, hMv⟩ := id hbv
  obtain ⟨Mp, hMp⟩ := id hbp
  obtain ⟨Mq, hMq⟩ := id hbq
  have hL := redSys_noRule_ltd 𝔼 h1 h2 h3 h4 h5 hs
  obtain ⟨X, P1, V, Q, R, -, huniq⟩ := LongTermDebt.ltd_determinate 𝔼 hσ hκ hβ hρ0 hρ1 hω0
    hω1 hui hMi hus hMs (vm1 := P.rho • v 0 + p 0 + us 0) (qm1 := P.omega • q 0)
    (by rw [map_add, map_add, map_smul, hav 0, hap 0, hus 0])
    (Mv := |P.rho| * Mv + Mp + Ms)
    (fun ω => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add ?_ (hMp 0 ω))) (hMs 0 ω))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMv 0 ω) (abs_nonneg _))
    (by rw [map_smul, haq 0]) (Mq := |P.omega| * Mq)
    (fun ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hMq 0 ω) (abs_nonneg _))
  obtain ⟨e1, e2, e3, e4, -⟩ := huniq _ _ _ _ _ hL haq hbp hbv hbq
  obtain ⟨f1, f2, f3, f4, -⟩ := huniq _ _ _ _ _ hL' haq' hbp' hbv' hbq'
  exact ⟨f1.trans e1.symm, f2.trans e2.symm, f3.trans e3.symm, f4.trans e4.symm⟩

/-- **FiscalNK determinacy as the `θ = 0` special case** (Cochrane (2023), (5.15)–(5.16),
p. 121 and §5.5, pp. 148–149): with no rules, one-period debt (`ω = 0`) and `0 < ρ < 1`, a
bounded equilibrium of the §5.5 model is the unique bounded equilibrium of (5.15)–(5.16) with
`i = u_i`, `s̃ = u_s` and `b_0 = ρ v_0 + π_0 + u_{s,0}` (`FiscalNK.fiscalNK_determinate`). -/
theorem redEquil_noRule_eq_fiscalNK {P : PolicyRules.Params} (hP : PolicyRules.Standard P)
    (h1 : P.thIpi = 0) (h2 : P.thIx = 0) (h3 : P.thSpi = 0) (h4 : P.thSx = 0) (h5 : P.alpha = 0)
    (hω : P.omega = 0) (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : PolicyRules.Shocks 𝔼 P ei es ui us) {p0 v0 : ℝ}
    {x p q v : ℕ → Ω → ℝ} (h : PolicyRules.RedEquil 𝔼 P ei es ui us p0 v0 x p q v) :
    ∀ x' π' v', FiscalNK.FTPLNK 𝔼 P.sigma P.beta P.kappa P.rho ui us
      (P.rho • v 0 + p 0 + us 0) x' π' v' → BoundedProc π' → BoundedProc v' →
      x' = x ∧ π' = p ∧ v' = v := by
  intro x' π' v' hF' hbp' hbv'
  obtain ⟨hs, -, hap, haq, hav, -, hbp, -, hbv, -, -⟩ := h
  obtain ⟨hσ, hκ, hβ, -, -, -⟩ := hP
  obtain ⟨-, -, hui, hus, -, -, ⟨Mi, hMi⟩, ⟨Ms, hMs⟩, -⟩ := hsh
  obtain ⟨Mv, hMv⟩ := id hbv
  obtain ⟨Mp, hMp⟩ := id hbp
  have hF := redSys_noRule_short 𝔼 h1 h2 h3 h4 h5 hω hs haq
  obtain ⟨X, P1, V, -, huniq⟩ := FiscalNK.fiscalNK_determinate 𝔼 hσ hκ hβ hρ0 hρ1 hui hMi
    hus hMs (b0 := P.rho • v 0 + p 0 + us 0)
    (by rw [map_add, map_add, map_smul, hav 0, hap 0, hus 0])
    (Mb := |P.rho| * Mv + Mp + Ms)
    (fun ω => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add ?_ (hMp 0 ω))) (hMs 0 ω))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMv 0 ω) (abs_nonneg _))
  obtain ⟨e1, e2, e3⟩ := huniq _ _ _ hF hbp hbv
  obtain ⟨f1, f2, f3⟩ := huniq _ _ _ hF' hbp' hbv'
  exact ⟨f1.trans e1.symm, f2.trans e2.symm, f3.trans e3.symm⟩

/-! ### Fiscal rules: §5.4 vs §5.5 -/

/-- Cochrane (2023), (5.71), p. 149 and p. 135: the §5.5 debt root `(1 − α)/ρ` is the §5.4 root
`g` of the surplus process. -/
theorem debtRoot_eq_gRoot (P : PolicyRules.Params) :
    PolicyRules.debtRoot P = SurplusProcess.gRoot P.rho P.alpha := rfl

/-- Cochrane (2023), §5.4, pp. 137–138 and §5.5, pp. 148–149: under perfect foresight the §5.5
model is determinate iff the §5.4 root satisfies `|g| = |(1 − α)/ρ| ≤ 1`. -/
theorem alpha_iff_pf_gRoot {P : PolicyRules.Params} (hP : PolicyRules.Standard P)
    (hpass : PolicyRules.Passive P) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) :
    PolicyRules.ModelDeterminate perfectForesight P ↔
      |SurplusProcess.gRoot P.rho P.alpha| ≤ 1 := by
  rw [PolicyRules.alpha_iff_pf hP hpass hω hρ0 hηi hηs, SurplusProcess.gRoot, abs_div,
    abs_of_pos hρ0, div_le_one hρ0]

/-- Cochrane (2023), p. 138 and §5.5, pp. 148–149: in the §5.5 determinacy region
`|1 − α| < ρ` (with `0 < ρ ≤ 1`) the surplus rule `s̃_{t+1} = α v_t + …` is passive in the §5.4
sense (`ActivePassive.gamma_passive_iff`): every debt path satisfies the transversality
condition, whatever inflation does. (The same region is where `ActivePassive.gamma_bounded`
keeps debt bounded.) -/
theorem determinate_region_passive [Nonempty Ω] {ρ α : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : |1 - α| < ρ) :
    ∀ π' v' : ℕ → Ω → ℝ, 𝔼.Adapted v' →
      (∀ t, ρ • v' (t + 1) = (1 - α) • v' t - SurplusProcess.surprise 𝔼 π' t) →
        SharedTools.TVC 𝔼 ρ v' :=
  (ActivePassive.gamma_passive_iff 𝔼 (ρ := ρ) (γ := α) hρ0.ne').mpr (lt_of_lt_of_le h hρ1)

/-! ### Continuous time -/

/-- Cochrane (2023), §5.4.2, p. 142 (`NonlinearCT.odeSol`) and A1 §1.12, p. 580
(`CTSimple.bwdInt`): the solution of `x' = c x − f` from `x_0` is
`e^{ct} x_0 + B_{−c}(−f)(t)`. -/
theorem odeSol_eq_bwdInt (c : ℝ) (f : ℝ → ℝ) (x0 τ : ℝ) :
    NonlinearCT.odeSol c f x0 τ =
      Real.exp (c * τ) * x0 + CTSimple.bwdInt (-c) (fun s => -f s) τ := by
  rw [NonlinearCT.odeSol, CTSimple.bwdInt_eq]
  simp only [neg_mul, neg_neg, mul_neg, intervalIntegral.integral_neg]
  ring

end Cochrane.StickyPriceFiscal.Links
