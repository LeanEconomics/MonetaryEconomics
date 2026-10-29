/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergTrendWelfare

/-!
# Trend-inflation welfare, Rotemberg versus Calvo, for every `σ > 0` including log utility

Woodford (2003), *Interest and Prices*, Chapter 6, §2 (pp. 393–400) and §4.1 (the distortion
`Φ = 1 − m`), Chapter 3, §2 and footnote 44 (the Calvo and Rotemberg pricing conditions).
`NonlinearRotembergTrendWelfare.trend_welfare` compares the second-order welfare of trend
inflation with the CRRA utility `u(c) = (e^{(1−σ)ĉ} − 1)/(1 − σ)` and excludes `σ = 1`, where that
formula is `0/0`. Here the utility is `uG σ` (`= ĉ`, i.e. `log C` in units `u_cȲ = 1`, at
`σ = 1`, and the CRRA formula otherwise); `tendsto_uu_log` shows it is the limit of the CRRA
utilities as `σ → 1`.

## Main results

* **`trend_welfare_log`**: at `σ = 1` (log utility), under the equivalence map, the first
  derivatives coincide and the second derivatives differ by exactly the expression of
  `NonlinearRotembergTrendWelfare.trend_welfare` evaluated at `σ = 1`.
* **`trend_welfare_all`**: the same for every parameter vector, with no restriction on `σ`.
* **`trend_welfare_log_differ`**: at `σ = 1` the difference is `Dm` of
  `NonlinearRotembergTrendWelfare`, strictly positive at `m = 1` and zero for at most two values
  of `m`: the totals do not coincide under log utility either.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergLogWelfare

open Filter Topology
open NonlinearRotemberg
open NonlinearRotembergJets
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergBoundary (ssY)
open NonlinearRotembergTrendWelfare (uu vv cR KR J_YR J_lw J_vv yC LD J_yC J_LD Dm
  trend_welfare_differ)

variable {p : Par}

/-- Woodford (2003), Ch. 2 and Ch. 6 (utility in units `u_cȲ = 1`): `ĉ` (`log C`) at `σ = 1`
and `(e^{(1−σ)ĉ} − 1)/(1 − σ)` otherwise. -/
noncomputable def uG (σ c : ℝ) : ℝ := if σ = 1 then c else uu σ c

/-- Woodford (2003), Ch. 2 (**log utility is the `σ → 1` limit of CRRA**): for every `ĉ`,
`(e^{(1−σ)ĉ} − 1)/(1 − σ) → ĉ` as `σ → 1`, `σ ≠ 1`. -/
theorem tendsto_uu_log (c : ℝ) : Tendsto (fun σ => uu σ c) (𝓝[≠] 1) (𝓝 c) := by
  have hd : HasDerivAt (fun h : ℝ => Real.exp (h * c)) c 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const c).exp
    simpa using this
  have hs := hd.tendsto_slope_zero
  have hmap : Tendsto (fun σ : ℝ => 1 - σ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun σ : ℝ => 1 - σ) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact sub_ne_zero.2 (Ne.symm hσ)
  have := hs.comp hmap
  refine this.congr fun σ => ?_
  simp only [Function.comp, uu, zero_add, zero_mul, Real.exp_zero, smul_eq_mul]
  ring

/-- Woodford (2003), App. A.3: `uG` is the CRRA utility away from `σ = 1`. -/
theorem uG_of_ne {σ : ℝ} (hσ : σ ≠ 1) (c : ℝ) : uG σ c = uu σ c := by
  simp [uG, hσ]

/-- Woodford (2003), App. A.3: `uG` is `ĉ` at `σ = 1`. -/
theorem uG_one (c : ℝ) : uG 1 c = c := by simp [uG]

/-- Woodford (2003), App. A.3: Jets of `uG ∘ f` with `f 0 = 0`, for EVERY `σ`: `(a₁, (1−σ)a₁² +
a₂)`. -/
theorem J_uG (σ : ℝ) {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) (h0 : f 0 = 0) :
    J2 (fun x => uG σ (f x)) a1 ((1 - σ) * a1 * a1 + a2) := by
  by_cases hσ : σ = 1
  · subst hσ
    exact J2_eq (J2_congr hf fun x => uG_one _) rfl (by ring)
  · exact J2_congr (NonlinearRotembergTrendWelfare.J_uu hσ hf h0) fun x => uG_of_ne hσ _

/-- Woodford (2003), Ch. 6: Rotemberg steady-state welfare at trend inflation, utility `uG`. -/
noncomputable def WRG (p : Par) (π : ℝ) : ℝ := uG p.σ (cR p π) - p.m * vv p.ω (ssY p π)

/-- Woodford (2003), Ch. 6: Calvo steady-state welfare at trend inflation, utility `uG`. -/
noncomputable def WCG (p : Par) (α π : ℝ) : ℝ :=
  uG p.σ (yC p α π) - p.m * vv p.ω (yC p α π + LD p α π / (1 + p.ω))

/-- Woodford (2003), App. A.3: `WRG` is `NonlinearRotembergTrendWelfare.WR` for `σ ≠ 1`. -/
theorem WRG_eq (hσ : p.σ ≠ 1) (π : ℝ) : WRG p π = NonlinearRotembergTrendWelfare.WR p π := by
  simp [WRG, NonlinearRotembergTrendWelfare.WR, uG_of_ne hσ]

/-- Woodford (2003), App. A.3: `WCG` is `NonlinearRotembergTrendWelfare.WC` for `σ ≠ 1`. -/
theorem WCG_eq (hσ : p.σ ≠ 1) (α π : ℝ) :
    WCG p α π = NonlinearRotembergTrendWelfare.WC p α π := by
  simp [WCG, NonlinearRotembergTrendWelfare.WC, uG_of_ne hσ]

/-- Woodford (2003), Ch. 6 (**Rotemberg trend-inflation welfare to second order, every `σ`**). -/
theorem J_WRG (hp : p.Basic) :
    J2 (WRG p) ((1 - p.m) * (KR p / (p.σ + p.ω)))
      ((1 - p.σ) * (KR p / (p.σ + p.ω)) ^ 2 +
          ((3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω) - p.ψ) -
        p.m * ((1 + p.ω) * (KR p / (p.σ + p.ω)) ^ 2 +
          (3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω))) := by
  have hY := J_YR hp
  have hY0 : ssY p 0 = 0 := by simp [ssY, wedge]
  have hC := J2_add hY (J_lw p.ψ)
  have hC0 : (fun x => ssY p x + Real.log (wedge p.ψ x)) 0 = 0 := by simp [hY0, wedge]
  have hu := J_uG p.σ hC hC0
  have hv := J_vv hp.ω_nonneg hY hY0
  have := J2_sub hu (J2_const_mul p.m hv)
  refine J2_eq (J2_congr this fun x => rfl) (by ring) (by ring)

/-- Woodford (2003), Ch. 6 (**Calvo trend-inflation welfare to second order, every `σ`**). -/
theorem J_WCG (hp : p.Basic) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    J2 (WCG p α)
      ((1 - p.m) * (((1 + p.ω * p.θ) * (α / (1 - α)) - (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
          (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω)))
      ((1 - p.σ) * ((((1 + p.ω * p.θ) * (α / (1 - α)) -
          (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
          (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω)) ^ 2) +
        (((1 + p.ω * p.θ) * (α * (p.θ - 1) / (1 - α) ^ 2) -
          (-(α * p.β * (p.θ - 1) ^ 2) / (1 - α * p.β) ^ 2) +
          (-(α * p.β * (p.θ * (1 + p.ω)) ^ 2) / (1 - α * p.β) ^ 2)) / (p.σ + p.ω)) -
        p.m * ((1 + p.ω) * ((((1 + p.ω * p.θ) * (α / (1 - α)) -
          (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
          (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω)) ^ 2) +
          ((((1 + p.ω * p.θ) * (α * (p.θ - 1) / (1 - α) ^ 2) -
            (-(α * p.β * (p.θ - 1) ^ 2) / (1 - α * p.β) ^ 2) +
            (-(α * p.β * (p.θ * (1 + p.ω)) ^ 2) / (1 - α * p.β) ^ 2)) / (p.σ + p.ω)) +
            α * (p.θ * (1 + p.ω)) * (1 + p.ω * p.θ) / (1 - α) ^ 2 / (1 + p.ω)))) := by
  have hy := J_yC hp hα0 hα1
  have hl := J_LD hp hα1
  have hy0 : yC p α 0 = 0 := by
    simp [yC, NonlinearRotembergTrendWelfare.lx, NonlinearRotembergTrendWelfare.ell]
  have hl0 : LD p α 0 = 0 := by
    simp [LD, NonlinearRotembergTrendWelfare.lx, NonlinearRotembergTrendWelfare.ell]
  have hh := J2_add hy (J2_const_mul (1 / (1 + p.ω)) hl)
  have hh0 : (fun x => yC p α x + 1 / (1 + p.ω) * LD p α x) 0 = 0 := by simp [hy0, hl0]
  have hu := J_uG p.σ hy hy0
  have hv := J_vv hp.ω_nonneg hh hh0
  have := J2_sub hu (J2_const_mul p.m hv)
  refine J2_eq (J2_congr this fun x => by simp only [WCG]; ring_nf) (by ring) (by ring)

/-- Woodford (2003), Ch. 6, §2 and §4.1 (**the second-order welfare of trend inflation, Rotemberg
versus Calvo, for EVERY `σ`**, including log utility): under the equivalence map
`ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, the first derivatives at zero inflation coincide, `(1 − m)Y₁`, and
the second derivatives differ by
`(1 − m)(Y₂ᴿ − Y₂ᶜ) + mθα²(1+ωθ)(1−β)/((1−α)²(1−αβ))` (as in
`NonlinearRotembergTrendWelfare.trend_welfare`). -/
theorem trend_welfare_all (hp : p.Basic) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hψ : p.ψ = p.θ * p.m * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) :
    deriv (WRG p) 0 = (1 - p.m) * ((1 - p.β) * α * (1 + p.ω * p.θ) /
        ((1 - α) * (1 - α * p.β) * (p.σ + p.ω))) ∧
      deriv (WCG p α) 0 = (1 - p.m) * ((1 - p.β) * α * (1 + p.ω * p.θ) /
        ((1 - α) * (1 - α * p.β) * (p.σ + p.ω))) ∧
      deriv (deriv (WRG p)) 0 - deriv (deriv (WCG p α)) 0 =
        (1 - p.m) * ((3 * ((1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) -
            ((1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) ^ 2 +
            p.σ * p.ψ) / (p.σ + p.ω) -
          ((1 + p.ω * p.θ) * α * (p.θ - 1) / (1 - α) ^ 2 +
            α * p.β * (p.θ - 1) ^ 2 / (1 - α * p.β) ^ 2 -
            α * p.β * (p.θ * (1 + p.ω)) ^ 2 / (1 - α * p.β) ^ 2) / (p.σ + p.ω)) +
        p.m * p.θ * α ^ 2 * (1 + p.ω * p.θ) * (1 - p.β) / ((1 - α) ^ 2 * (1 - α * p.β)) := by
  obtain ⟨r1, r2⟩ := J2_deriv (J_WRG hp)
  obtain ⟨c1, c2⟩ := J2_deriv (J_WCG hp hα0 hα1)
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm0 : p.m ≠ 0 := hp.m_pos.ne'
  have h1α : 1 - α ≠ 0 := by linarith
  have hab : 1 - α * p.β ≠ 0 := by nlinarith [hp.β_lt_one, hp.β_pos]
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hω : 1 + p.ω ≠ 0 := by linarith [hp.ω_nonneg]
  have hK : KR p = (1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β)) := by
    unfold KR; rw [hψ]; field_simp
  have hY1 : ((1 + p.ω * p.θ) * (α / (1 - α)) - (-(α * p.β * (p.θ - 1)) / (1 - α * p.β)) +
      (-(α * p.β * (p.θ * (1 + p.ω))) / (1 - α * p.β))) / (p.σ + p.ω) =
      (1 - p.β) * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β)) / (p.σ + p.ω) := by
    field_simp; ring
  have key : -p.ψ + p.m * (α * (p.θ * (1 + p.ω)) * (1 + p.ω * p.θ) / (1 - α) ^ 2 / (1 + p.ω)) =
      p.m * p.θ * α ^ 2 * (1 + p.ω * p.θ) * (1 - p.β) / ((1 - α) ^ 2 * (1 - α * p.β)) := by
    rw [hψ]; field_simp; ring
  rw [r1, c1, r2, c2, hK, hY1]
  refine ⟨by field_simp, by field_simp, ?_⟩
  linear_combination key

/-- Woodford (2003), Ch. 6, §2 and §4.1 (**trend-inflation welfare under LOG utility**,
`σ = 1`): under the equivalence map the first derivatives coincide, and the second derivatives
differ by `(1 − m)(Y₂ᴿ − Y₂ᶜ) + mθα²(1+ωθ)(1−β)/((1−α)²(1−αβ))` at `σ = 1`, where the utility is
`u = ĉ = log C − log Ȳ`. -/
theorem trend_welfare_log (hp : p.Basic) (hσ : p.σ = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hψ : p.ψ = p.θ * p.m * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β))) :
    (∀ π, WRG p π = cR p π - p.m * vv p.ω (ssY p π)) ∧
      (∀ π, WCG p α π = yC p α π - p.m * vv p.ω (yC p α π + LD p α π / (1 + p.ω))) ∧
      deriv (WRG p) 0 = (1 - p.m) * ((1 - p.β) * α * (1 + p.ω * p.θ) /
        ((1 - α) * (1 - α * p.β) * (1 + p.ω))) ∧
      deriv (WCG p α) 0 = (1 - p.m) * ((1 - p.β) * α * (1 + p.ω * p.θ) /
        ((1 - α) * (1 - α * p.β) * (1 + p.ω))) ∧
      deriv (deriv (WRG p)) 0 - deriv (deriv (WCG p α)) 0 = Dm p.β 1 p.ω p.θ α p.m := by
  obtain ⟨h1, h2, h3⟩ := trend_welfare_all hp hα0 hα1 hψ
  refine ⟨fun π => by simp [WRG, hσ, uG_one], fun π => by simp [WCG, hσ, uG_one], ?_, ?_, ?_⟩
  · rw [h1, hσ, add_comm 1 p.ω]
  · rw [h2, hσ, add_comm 1 p.ω]
  · rw [h3, hψ, hσ]; rfl

/-- Woodford (2003), Ch. 6, §2 and §4.1 (**the totals do not coincide under log utility**): at
`σ = 1` the second-order difference `Dm` is strictly positive at `m = 1` and vanishes for at most
two values of `m`. -/
theorem trend_welfare_log_differ {β ω θ α : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hθ : 1 < θ) (hα0 : 0 < α) (hα1 : α < 1) :
    0 < Dm β 1 ω θ α 1 ∧ ∀ m1 m2 m3 : ℝ, m1 ≠ m2 → m1 ≠ m3 → m2 ≠ m3 →
      Dm β 1 ω θ α m1 = 0 → Dm β 1 ω θ α m2 = 0 → Dm β 1 ω θ α m3 = 0 → False :=
  trend_welfare_differ hβ0 hβ1 hω hθ hα0 hα1

end Woodford.StabilizationWelfare.NonlinearRotembergLogWelfare
