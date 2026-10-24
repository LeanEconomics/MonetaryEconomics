/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.LinksGaliWoodford

/-!
# The discrete Werning trap paths converge to the continuous-time ones

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476
(the Werning model (20.5)–(20.6) and its family of equilibria indexed by `π_T`), and §5.7.1,
p. 165 (discrete and continuous time).

Galí's discrete model with period length `h` (`β = 1 − ρh`, IS slope `σ⁻¹ = σh`, Phillips-curve
slope `κh`, rates per unit of time) during a zero-bound trap with natural rate `u`
(`η = −u`) is solved backward from the end-of-trap state `(c v_x, c)` of the discrete Werning
family (`LinksGaliWoodford.wState`). We prove the exact closed form of the discrete trap path
(two geometric modes `λ₁ᵐ`, `λ₂ᵐ` around the trap steady state) and that, cutting the time
`T − t` before the end of the trap into `n + 1` periods, the discrete output gap and inflation at
the date `n + 1` periods before the end converge to the continuous-time Werning paths
`WerningModel.wX`, `WerningModel.wPi` (with `π_T = c`, `g = 0`) at time `t`.

## Main results

* `tendsto_one_add_pow`: `(1 + τ g_n/(n+1))^{n+1} → e^{τL}` when `g_n → L`.
* `backState_modes`: the discrete trap path is `s̄ + λ₁ᵐ a v₁ + λ₂ᵐ b v₂` exactly.
* `trapDisc_closed`: the closed form at period length `h`, with the scaled roots `sr1`, `sr2`.
* `trapDisc_eq_wState`: the trap path is the discrete Werning family member `wState`.
* `trap_tendsto`, `trap_pi_tendsto`, `trap_x_tendsto`: **convergence of whole trap paths** to
  `wPi`, `wX` at every time `t < T`.
-/

namespace Cochrane.ZeroBound.LinksGaliWoodfordLimit

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford

/-- Cochrane (2023), §5.7.1, p. 165 (the exponential limit of compounding over `n + 1`
periods): if `g_n → L` then `(1 + τ g_n/(n + 1))^{n+1} → e^{τL}`. -/
theorem tendsto_one_add_pow {g : ℕ → ℝ} {L τ : ℝ} (hg : Tendsto g atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (1 + τ / ((n : ℝ) + 1) * g n) ^ (n + 1)) atTop
      (𝓝 (Real.exp (τ * L))) := by
  set y : ℕ → ℝ := fun n => τ / ((n : ℝ) + 1) * g n with hy
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => τ / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hy0 : Tendsto y atTop (𝓝 0) := by
    have := hdiv.mul hg
    rwa [zero_mul] at this
  have hny : ∀ n : ℕ, ((n : ℝ) + 1) * y n = τ * g n := by
    intro n
    simp only [hy]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hev : ∀ᶠ n in atTop, -(1 / 2 : ℝ) < y n :=
    hy0.eventually (lt_mem_nhds (by norm_num))
  have hup : Tendsto (fun n : ℕ => τ * g n) atTop (𝓝 (τ * L)) := hg.const_mul τ
  have hlo : Tendsto (fun n : ℕ => τ * g n / (1 + y n)) atTop (𝓝 (τ * L)) := by
    have h1 : Tendsto (fun n : ℕ => 1 + y n) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hy0
    rw [add_zero] at h1
    have := hup.div h1 one_ne_zero
    rwa [div_one] at this
  have hlog : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.log (1 + y n)) atTop
      (𝓝 (τ * L)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
    · filter_upwards [hev] with n hn
      have hpos : 0 < 1 + y n := by linarith
      have hl := Real.one_sub_inv_le_log_of_pos hpos
      have e : τ * g n / (1 + y n) = ((n : ℝ) + 1) * (1 - (1 + y n)⁻¹) := by
        rw [← hny n]
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hl (by positivity)
    · filter_upwards [hev] with n hn
      have hpos : 0 < 1 + y n := by linarith
      have hl := Real.log_le_sub_one_of_pos hpos
      rw [← hny n]
      have : Real.log (1 + y n) ≤ y n := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
  have hexp := (Real.continuous_exp.tendsto _).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hev] with n hn
  have hpos : 0 < 1 + y n := by linarith
  simp only [Function.comp_apply]
  rw [← Real.exp_log (pow_pos hpos (n + 1)), Real.log_pow]
  push_cast
  rfl

/-! ## The exact closed form of a discrete trap path -/

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), §20.2.2, p. 475 (two modes around the trap
steady state `(x̄, π̄) = ((1 − β)η/κ, η)`): if `λ₁, λ₂` solve
`λ² − (1 + β + κ/σ)λ + β = 0`, the backward step maps `s̄ + a v₁ + b v₂` to
`s̄ + λ₁ a v₁ + λ₂ b v₂`, `v_i = (1, σ(λ_i − 1))`. -/
theorem backStep_modes {β κ σ η l1 l2 a b : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (h1 : l1 ^ 2 - (1 + β + κ / σ) * l1 + β = 0) (h2 : l2 ^ 2 - (1 + β + κ / σ) * l2 + β = 0) :
    backStep β κ σ η ((1 - β) * η / κ + a + b, η + a * σ * (l1 - 1) + b * σ * (l2 - 1)) =
      ((1 - β) * η / κ + l1 * a + l2 * b,
        η + l1 * a * σ * (l1 - 1) + l2 * b * σ * (l2 - 1)) := by
  simp only [backStep]
  ext
  · simp only
    field_simp
    ring
  · simp only
    field_simp
    have hσ' : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
    linear_combination (-(a * σ ^ 2)) * h1 - b * σ ^ 2 * h2 - κ * σ * (a * l1 + b * l2) * hσ'

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), §20.2.2, p. 475: `m` backward steps act on
the modes by `λ₁ᵐ`, `λ₂ᵐ` — the exact closed form of the discrete trap path. -/
theorem backState_modes {β κ σ η l1 l2 a b : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (h1 : l1 ^ 2 - (1 + β + κ / σ) * l1 + β = 0) (h2 : l2 ^ 2 - (1 + β + κ / σ) * l2 + β = 0)
    (m : ℕ) :
    backState β κ σ η ((1 - β) * η / κ + a + b, η + a * σ * (l1 - 1) + b * σ * (l2 - 1)) m =
      ((1 - β) * η / κ + l1 ^ m * a + l2 ^ m * b,
        η + l1 ^ m * a * σ * (l1 - 1) + l2 ^ m * b * σ * (l2 - 1)) := by
  induction m with
  | zero => simp [backState]
  | succ m ih =>
    rw [backState, ih, backStep_modes hκ hσ h1 h2, pow_succ, pow_succ]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring

/-! ## Period length `h`: scaled roots -/

/-- Cochrane (2023), §5.7.1, p. 165: `S(h) = √((ρ − σκh)² + 4σκ)`. -/
noncomputable def sqS (ρ σ κ h : ℝ) : ℝ := Real.sqrt ((ρ - σ * κ * h) ^ 2 + 4 * (σ * κ))

/-- Cochrane (2023), §5.7.1, p. 165: the scaled unstable root `(λ₁ − 1)/h` (`Links.scaledRoot`). -/
noncomputable def sr1 (ρ σ κ h : ℝ) : ℝ := (-ρ + σ * κ * h + sqS ρ σ κ h) / 2

/-- Cochrane (2023), §5.7.1, p. 165: the scaled stable root `(λ₂ − 1)/h`. -/
noncomputable def sr2 (ρ σ κ h : ℝ) : ℝ := (-ρ + σ * κ * h - sqS ρ σ κ h) / 2

/-- Cochrane (2023), §5.7.1, p. 165: both scaled roots solve `g² + (ρ − σκh)g − σκ = 0`. -/
theorem sr_root {ρ σ κ h : ℝ} (hσκ : 0 < σ * κ) :
    sr1 ρ σ κ h ^ 2 + (ρ - σ * κ * h) * sr1 ρ σ κ h - σ * κ = 0 ∧
      sr2 ρ σ κ h ^ 2 + (ρ - σ * κ * h) * sr2 ρ σ κ h - σ * κ = 0 := by
  have hs : sqS ρ σ κ h ^ 2 = (ρ - σ * κ * h) ^ 2 + 4 * (σ * κ) :=
    Real.sq_sqrt (by positivity)
  unfold sr1 sr2
  constructor <;> linear_combination hs / 4

/-- Cochrane (2023), §5.7.1, p. 165: `sr1 − sr2 = S(h) > 0`. -/
theorem sr_sub_pos {ρ σ κ h : ℝ} (hσκ : 0 < σ * κ) : 0 < sr1 ρ σ κ h - sr2 ρ σ κ h := by
  have : 0 < sqS ρ σ κ h := Real.sqrt_pos.2 (by positivity)
  unfold sr1 sr2
  linarith

/-- Cochrane (2023), §5.7.1, p. 165 and p. 475: at `h = 0`, `sr1 = λ^b` and `sr2 = −λ^f`. -/
theorem sr_zero (ρ σ κ : ℝ) :
    sr1 ρ σ κ 0 = ContinuousTimeNK.lamb ρ κ σ ∧ sr2 ρ σ κ 0 = -ContinuousTimeNK.lamf ρ κ σ := by
  unfold sr1 sr2 sqS ContinuousTimeNK.lamb ContinuousTimeNK.lamf
  simp only [mul_zero, add_zero, sub_zero]
  rw [show 4 * (σ * κ) = 4 * κ * σ by ring]
  constructor <;> ring

/-- Cochrane (2023), §5.7.1, p. 165: the scaled roots are continuous in `h`. -/
theorem sr_continuous (ρ σ κ : ℝ) : Continuous (sr1 ρ σ κ) ∧ Continuous (sr2 ρ σ κ) := by
  unfold sr1 sr2 sqS
  constructor <;> fun_prop

/-- Cochrane (2023), §5.7.1, p. 165: with `β = 1 − ρh`, Galí's IS slope `σ⁻¹ = σh` and `κh`,
`λ = 1 + h g` solves Galí's characteristic equation `λ² − (1 + β + κ_G/σ_G)λ + β = 0` whenever
`g` solves `g² + (ρ − σκh)g − σκ = 0`. -/
theorem char_of_scaled {ρ σ κ h g : ℝ} (hg : g ^ 2 + (ρ - σ * κ * h) * g - σ * κ = 0) :
    (1 + h * g) ^ 2 - (1 + (1 - ρ * h) + κ * h / (σ * h)⁻¹) * (1 + h * g) + (1 - ρ * h) = 0 := by
  rw [div_inv_eq_mul]
  linear_combination h ^ 2 * hg

/-- Cochrane (2023), §20.2.2, p. 475: the discrete trap path at period length `h`, `m` periods
before the end of the trap, from the end-of-trap state `(c v_x, c)`, `v_x = −sr2/κ`. -/
noncomputable def trapDisc (σ κ ρ u c h : ℝ) (m : ℕ) : ℝ × ℝ :=
  backState (1 - ρ * h) (κ * h) (σ * h)⁻¹ (-u) (c * (-sr2 ρ σ κ h / κ), c) m

/-- Cochrane (2023), §20.2.2, p. 475: the weight on the unstable mode for scaled roots
`g₁, g₂`: `A = (σ(c + u) − g₂D)/(g₁ − g₂)`, `D = (−g₂c + ρu)/κ = c v_x − x̄`. -/
noncomputable def coefA (σ κ ρ u c g1 g2 : ℝ) : ℝ :=
  (σ * (c + u) - g2 * ((-g2 * c + ρ * u) / κ)) / (g1 - g2)

/-- Cochrane (2023), §20.2.2, p. 475: the weight on the stable mode,
`B = (g₁D − σ(c + u))/(g₁ − g₂)`. -/
noncomputable def coefB (σ κ ρ u c g1 g2 : ℝ) : ℝ :=
  (g1 * ((-g2 * c + ρ * u) / κ) - σ * (c + u)) / (g1 - g2)

/-- Cochrane (2023), §20.2.2, p. 475 and §5.7.1, p. 165: **the exact closed form of the discrete
trap path** at period length `h ≠ 0`, for any two distinct solutions `g₁, g₂` of
`g² + (ρ − σκh)g − σκ = 0` (the scaled roots, `λ_i = 1 + h g_i`), starting from the end-of-trap
state `(c v_x, c)`, `v_x = −g₂/κ`: `x_m = −ρu/κ + λ₁ᵐA + λ₂ᵐB`,
`π_m = −u + λ₁ᵐA g₁/σ + λ₂ᵐB g₂/σ`. -/
theorem closed_generic {σ κ ρ u c h g1 g2 : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hh : h ≠ 0)
    (hd : g1 - g2 ≠ 0) (r1 : g1 ^ 2 + (ρ - σ * κ * h) * g1 - σ * κ = 0)
    (r2 : g2 ^ 2 + (ρ - σ * κ * h) * g2 - σ * κ = 0) (m : ℕ) :
    backState (1 - ρ * h) (κ * h) (σ * h)⁻¹ (-u) (c * (-g2 / κ), c) m =
      (-(ρ * u) / κ + (1 + h * g1) ^ m * coefA σ κ ρ u c g1 g2 +
          (1 + h * g2) ^ m * coefB σ κ ρ u c g1 g2,
        -u + (1 + h * g1) ^ m * coefA σ κ ρ u c g1 g2 * g1 / σ +
          (1 + h * g2) ^ m * coefB σ κ ρ u c g1 g2 * g2 / σ) := by
  have hκh : κ * h ≠ 0 := mul_ne_zero hκ hh
  have hσh : (σ * h)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσ hh)
  have key := backState_modes (β := 1 - ρ * h) (η := -u) (a := coefA σ κ ρ u c g1 g2)
    (b := coefB σ κ ρ u c g1 g2) hκh hσh (char_of_scaled r1) (char_of_scaled r2) m
  have hstart : (c * (-g2 / κ), c) =
      ((1 - (1 - ρ * h)) * -u / (κ * h) + coefA σ κ ρ u c g1 g2 + coefB σ κ ρ u c g1 g2,
        -u + coefA σ κ ρ u c g1 g2 * (σ * h)⁻¹ * (1 + h * g1 - 1) +
          coefB σ κ ρ u c g1 g2 * (σ * h)⁻¹ * (1 + h * g2 - 1)) := by
    unfold coefA coefB
    refine Prod.ext ?_ ?_
    · simp only
      field_simp
      ring
    · simp only
      field_simp
      ring
  rw [hstart, key]
  unfold coefA coefB
  refine Prod.ext ?_ ?_
  · simp only
    field_simp
    ring
  · simp only
    field_simp
    ring

/-- Cochrane (2023), §20.2.2, p. 475: the closed form with the scaled roots `sr1`, `sr2`
(`h > 0`). -/
theorem trapDisc_closed {σ κ ρ u c h : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hh : 0 < h) (m : ℕ) :
    trapDisc σ κ ρ u c h m =
      (-(ρ * u) / κ + (1 + h * sr1 ρ σ κ h) ^ m * coefA σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h) +
          (1 + h * sr2 ρ σ κ h) ^ m * coefB σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h),
        -u + (1 + h * sr1 ρ σ κ h) ^ m * coefA σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h) *
            sr1 ρ σ κ h / σ +
          (1 + h * sr2 ρ σ κ h) ^ m * coefB σ κ ρ u c (sr1 ρ σ κ h) (sr2 ρ σ κ h) *
            sr2 ρ σ κ h / σ) := by
  have hσκ : 0 < σ * κ := mul_pos hσ hκ
  obtain ⟨r1, r2⟩ := sr_root (ρ := ρ) (h := h) hσκ
  exact closed_generic hσ.ne' hκ.ne' hh.ne' (sr_sub_pos hσκ).ne' r1 r2 m

/-- Cochrane (2023), §20.2.2, p. 475: the discrete trap path is the trap part of the discrete
Werning family member `LinksGaliWoodford.wState` (Galí's parameters `1 − ρh`, `κh`, `(σh)⁻¹`,
`η = −u`): at the date `k ≤ t_Z`, `m = t_Z + 1 − k` periods before the end. -/
theorem trapDisc_eq_wState {σ κ ρ u c h : ℝ} (hκ : 0 < κ) (hh : 0 < h)
    {tZ k : ℕ} (hk : k ≤ tZ) :
    wState (1 - ρ * h) (κ * h) (σ * h)⁻¹ (-u) tZ c k = trapDisc σ κ ρ u c h (tZ + 1 - k) := by
  have hv : vx (1 - ρ * h) (σ * h)⁻¹ (κ * h) = -sr2 ρ σ κ h / κ := by
    unfold vx l2
    rw [inv_inv, Links.lam2_scaled_eq hh]
    have : κ * h ≠ 0 := by positivity
    unfold sr2 sqS
    field_simp
    ring
  simp only [wState, hk, ↓reduceIte, trapDisc, hv]

/-! ## Convergence to the continuous-time Werning paths -/

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.wPi` with `g = 0`, `π_T = c`): during the
trap, `π_t = −u + A₀e^{λ^b s} + B₀e^{−λ^f s}`, `s = T − t`, with `A₀ = c + uλ^f/(λ^f + λ^b)` and
`B₀ = uλ^b/(λ^f + λ^b)`. -/
theorem wPi_modes {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t ≤ T) :
    WerningModel.wPi σ κ ρ T u 0 c t =
      -u + (c + u * ContinuousTimeNK.lamf ρ κ σ /
          (ContinuousTimeNK.lamf ρ κ σ + ContinuousTimeNK.lamb ρ κ σ)) *
          Real.exp (ContinuousTimeNK.lamb ρ κ σ * (T - t)) +
        u * ContinuousTimeNK.lamb ρ κ σ /
          (ContinuousTimeNK.lamf ρ κ σ + ContinuousTimeNK.lamb ρ κ σ) *
          Real.exp (-(ContinuousTimeNK.lamf ρ κ σ * (T - t))) := by
  have hS := ContinuousTimeNK.lamf_add_lamb_pos (ρ := ρ) hκ hσ
  simp only [WerningModel.wPi, ht, ↓reduceIte, WerningModel.trapPi, WerningModel.hh,
    WerningModel.kk]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (algebra of the limit): with `λ^fλ^b = κσ` and
`λ^f − λ^b = ρ`, the limit weight of the unstable mode in inflation is `c + uλ^f/(λ^f + λ^b)`. -/
theorem algA {σ κ ρ u c lf lb : ℝ} (hσ : 0 < σ) (hlf : 0 < lf) (hlb : 0 < lb)
    (hm : lf * lb = κ * σ) (hs : lf - lb = ρ) :
    coefA σ κ ρ u c lb (-lf) * lb / σ = c + u * lf / (lf + lb) := by
  have hκ : κ = lf * lb / σ := by field_simp; linarith
  subst hκ hs
  unfold coefA
  have : lb - -lf ≠ 0 := by linarith
  have : lf + lb ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (algebra of the limit): the limit weight of the stable mode
in inflation is `uλ^b/(λ^f + λ^b)`. -/
theorem algB {σ κ ρ u c lf lb : ℝ} (hσ : 0 < σ) (hlf : 0 < lf) (hlb : 0 < lb)
    (hm : lf * lb = κ * σ) (hs : lf - lb = ρ) :
    coefB σ κ ρ u c lb (-lf) * -lf / σ = u * lb / (lf + lb) := by
  have hκ : κ = lf * lb / σ := by field_simp; linarith
  subst hκ hs
  unfold coefB
  have : lb - -lf ≠ 0 := by linarith
  have : lf + lb ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), (20.10), p. 475 (algebra of the limit): the output gap of the two-mode
limit is the continuous-time trap output gap `(λ^f π − y)/κ`. -/
theorem algX {σ κ ρ u c lf lb E1 E2 : ℝ} (hσ : 0 < σ) (hlf : 0 < lf) (hlb : 0 < lb)
    (hm : lf * lb = κ * σ) (hs : lf - lb = ρ) :
    -(ρ * u) / κ + E1 * coefA σ κ ρ u c lb (-lf) + E2 * coefB σ κ ρ u c lb (-lf) =
      (lf * (c * E1 + -u * (1 - (lf * E1 + lb * E2) / (lf + lb))) -
        lb * -u * (1 - E2)) / κ := by
  have hκ : κ = lf * lb / σ := by field_simp; linarith
  subst hκ hs
  unfold coefA coefB
  have : lb - -lf ≠ 0 := by linarith
  have : lf + lb ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 and §5.7.1, p. 165 (**whole trap paths converge**): fix
`t < T` and cut the time `T − t` to the end of the trap into `n + 1` periods of length
`h_n = (T − t)/(n + 1)`. The discrete Werning trap path (Galí's model with `β = 1 − ρh_n`,
slopes `σh_n`, `κh_n`, natural rate `u`, end-of-trap inflation `c`), taken `n + 1` periods
before the trap ends, converges — output gap and inflation — to the continuous-time Werning path
`(wX, wPi)` with `π_T = c`, `g = 0`, at time `t`. -/
theorem trap_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T) :
    Tendsto (fun n : ℕ => trapDisc σ κ ρ u c ((T - t) / ((n : ℝ) + 1)) (n + 1)) atTop
      (𝓝 (WerningModel.wX σ κ ρ T u 0 c t, WerningModel.wPi σ κ ρ T u 0 c t)) := by
  have hτ : 0 < T - t := by linarith
  have hσκ : 0 < σ * κ := mul_pos hσ hκ
  have hlf := ContinuousTimeNK.lamf_pos (ρ := ρ) hκ hσ
  have hlb := ContinuousTimeNK.lamb_pos (ρ := ρ) hκ hσ
  have hm := ContinuousTimeNK.lamf_mul_lamb (ρ := ρ) hκ hσ
  have hs := ContinuousTimeNK.lamf_sub_lamb ρ κ σ
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hh0 : Tendsto (fun n : ℕ => (T - t) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hpos : ∀ n : ℕ, 0 < (T - t) / ((n : ℝ) + 1) := fun n => by positivity
  obtain ⟨z1, z2⟩ := sr_zero ρ σ κ
  obtain ⟨c1, c2⟩ := sr_continuous ρ σ κ
  have G1 : Tendsto (fun n : ℕ => sr1 ρ σ κ ((T - t) / ((n : ℝ) + 1))) atTop
      (𝓝 (ContinuousTimeNK.lamb ρ κ σ)) := by
    rw [← z1]; exact (c1.tendsto 0).comp hh0
  have G2 : Tendsto (fun n : ℕ => sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1))) atTop
      (𝓝 (-ContinuousTimeNK.lamf ρ κ σ)) := by
    rw [← z2]; exact (c2.tendsto 0).comp hh0
  have P1 := tendsto_one_add_pow (τ := T - t) G1
  have P2 := tendsto_one_add_pow (τ := T - t) G2
  have hne : ContinuousTimeNK.lamb ρ κ σ - -ContinuousTimeNK.lamf ρ κ σ ≠ 0 := by linarith
  have hD : Tendsto (fun n : ℕ => (-sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1)) * c + ρ * u) / κ) atTop
      (𝓝 ((-(-ContinuousTimeNK.lamf ρ κ σ) * c + ρ * u) / κ)) :=
    ((G2.neg.mul tendsto_const_nhds).add tendsto_const_nhds).div_const κ
  have hA : Tendsto (fun n : ℕ => coefA σ κ ρ u c (sr1 ρ σ κ ((T - t) / ((n : ℝ) + 1)))
      (sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1)))) atTop
      (𝓝 (coefA σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ))) := by
    unfold coefA
    exact (tendsto_const_nhds.sub (G2.mul hD)).div (G1.sub G2) hne
  have hB : Tendsto (fun n : ℕ => coefB σ κ ρ u c (sr1 ρ σ κ ((T - t) / ((n : ℝ) + 1)))
      (sr2 ρ σ κ ((T - t) / ((n : ℝ) + 1)))) atTop
      (𝓝 (coefB σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ))) := by
    unfold coefB
    exact ((G1.mul hD).sub tendsto_const_nhds).div (G1.sub G2) hne
  have hX := (tendsto_const_nhds (x := -(ρ * u) / κ)).add (P1.mul hA) |>.add (P2.mul hB)
  have hP := ((tendsto_const_nhds (x := -u)).add (((P1.mul hA).mul G1).div_const σ)).add
    (((P2.mul hB).mul G2).div_const σ)
  have hvx : WerningModel.wX σ κ ρ T u 0 c t =
      -(ρ * u) / κ + Real.exp ((T - t) * ContinuousTimeNK.lamb ρ κ σ) *
          coefA σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) +
        Real.exp ((T - t) * -ContinuousTimeNK.lamf ρ κ σ) *
          coefB σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) := by
    rw [algX hσ hlf hlb hm hs]
    simp only [WerningModel.wX, ht.le, ↓reduceIte, WerningModel.trapPi, WerningModel.trapY,
      WerningModel.hh, WerningModel.kk, mul_zero, zero_mul, add_zero, sub_zero]
    rw [show (T - t) * ContinuousTimeNK.lamb ρ κ σ = ContinuousTimeNK.lamb ρ κ σ * (T - t) by
      ring, show (T - t) * -ContinuousTimeNK.lamf ρ κ σ = -(ContinuousTimeNK.lamf ρ κ σ *
        (T - t)) by ring]
  have hvp : WerningModel.wPi σ κ ρ T u 0 c t =
      -u + Real.exp ((T - t) * ContinuousTimeNK.lamb ρ κ σ) *
          coefA σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) *
          ContinuousTimeNK.lamb ρ κ σ / σ +
        Real.exp ((T - t) * -ContinuousTimeNK.lamf ρ κ σ) *
          coefB σ κ ρ u c (ContinuousTimeNK.lamb ρ κ σ) (-ContinuousTimeNK.lamf ρ κ σ) *
          -ContinuousTimeNK.lamf ρ κ σ / σ := by
    have a := algA (u := u) (c := c) hσ hlf hlb hm hs
    have b := algB (u := u) (c := c) hσ hlf hlb hm hs
    rw [wPi_modes hσ hκ ht.le, show ContinuousTimeNK.lamb ρ κ σ * (T - t) =
      (T - t) * ContinuousTimeNK.lamb ρ κ σ by ring, show -(ContinuousTimeNK.lamf ρ κ σ * (T - t)) =
      (T - t) * -ContinuousTimeNK.lamf ρ κ σ by ring]
    linear_combination (-Real.exp ((T - t) * ContinuousTimeNK.lamb ρ κ σ)) * a -
      Real.exp ((T - t) * -ContinuousTimeNK.lamf ρ κ σ) * b
  rw [hvx, hvp]
  refine (hX.prodMk_nhds hP).congr fun n => ?_
  rw [trapDisc_closed hσ hκ (hpos n) (n + 1)]

/-- Cochrane (2023), §20.2.2, p. 475: the convergence of `trap_tendsto` for inflation. -/
theorem trap_pi_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T) :
    Tendsto (fun n : ℕ => (trapDisc σ κ ρ u c ((T - t) / ((n : ℝ) + 1)) (n + 1)).2) atTop
      (𝓝 (WerningModel.wPi σ κ ρ T u 0 c t)) :=
  (continuous_snd.tendsto _).comp (trap_tendsto hσ hκ ht)

/-- Cochrane (2023), §20.2.2, p. 475: the convergence of `trap_tendsto` for the output gap. -/
theorem trap_x_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T) :
    Tendsto (fun n : ℕ => (trapDisc σ κ ρ u c ((T - t) / ((n : ℝ) + 1)) (n + 1)).1) atTop
      (𝓝 (WerningModel.wX σ κ ρ T u 0 c t)) :=
  (continuous_fst.tendsto _).comp (trap_tendsto hσ hκ ht)

/-- Cochrane (2023), §20.2.2, p. 475: the same convergence stated for the discrete Werning family
member itself: for any trap `[0, t_Z]` and date `k ≤ t_Z` with `t_Z + 1 − k = n + 1` periods to
the end of the trap, `wState` at `k` (period length `(T − t)/(n + 1)`) converges to
`(wX, wPi)` at `t`. -/
theorem wState_tendsto {σ κ ρ T u c t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : t < T)
    {tZ k : ℕ → ℕ} (hk : ∀ n, k n ≤ tZ n) (hlen : ∀ n, tZ n + 1 - k n = n + 1) :
    Tendsto (fun n : ℕ => wState (1 - ρ * ((T - t) / ((n : ℝ) + 1)))
        (κ * ((T - t) / ((n : ℝ) + 1))) (σ * ((T - t) / ((n : ℝ) + 1)))⁻¹ (-u) (tZ n) c (k n))
      atTop (𝓝 (WerningModel.wX σ κ ρ T u 0 c t, WerningModel.wPi σ κ ρ T u 0 c t)) := by
  refine (trap_tendsto hσ hκ ht).congr fun n => ?_
  have hp : 0 < (T - t) / ((n : ℝ) + 1) := div_pos (by linarith) (by positivity)
  rw [trapDisc_eq_wState hκ hp (hk n), hlen n]

end Cochrane.ZeroBound.LinksGaliWoodfordLimit
