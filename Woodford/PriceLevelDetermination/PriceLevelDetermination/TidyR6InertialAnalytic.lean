/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.TidyR6InertialEveryRule
import PriceLevelDetermination.TidyR6CriticalAnalytic

/-!
# The boundary of Proposition 2.8 for every analytic rule

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 632–634. For every
rule `Ψ` analytic at the steady state with slopes `φ_π ≠ 0`, `ρ`, `|φ_π + ρ| = 1`, the sunspot
question on the boundary is decided by the higher-order terms of the diagonal `D(y) = Ψ(y, y)`
in every case: either `D ∘ D` is the identity near the steady state (random sunspots), or
`D(D(y)) = y + c yᵐ + o(yᵐ)` with `c ≠ 0`, `m ≥ 2`, and `TidyR6InertialEveryRule.inertial_coin_iff`
applies.

## Main results

* `inertial_coin_sunspot_of_involutive`: `D ∘ D = id` near `0` ⟹ random sunspots.
* `inertial_analytic_iff` (**the characterisation**): random sunspots at every scale on the coin
  tree iff `D ∘ D = id` near `0`, or the leading coefficient `c` of `D ∘ D − id` is negative, or
  its order is even.
-/

namespace Woodford.PriceLevelDetermination.TidyR6InertialAnalytic

open scoped Topology
open Asymptotics Filter
open LocalIFTSystemsApps (ruleD)
open TidyR6InertialEveryRule (InertialCoinSunspots inertial_coin_sunspot_of_side inertial_coin_iff
  hasDerivAt_diag)
open TidyR6CriticalAnalytic (analytic_dichotomy)

/-- **Random sunspots when the two-step diagonal is the identity** (Woodford (2003), Prop. 2.8,
p. 96): for a rule strictly differentiable at the steady state with `φ_π ≠ 0`, `|φ_π + ρ| = 1`,
`Ψ(0) = 0`, if `D(D(y)) = y` near `0` (`D(y) = Ψ(y, y)`), the exact model has random sunspots at
every scale on the coin tree. -/
theorem inertial_coin_sunspot_of_involutive {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨ : HasStrictFDerivAt Ψ (ruleD φ ρ) 0) (hΨ0 : Ψ 0 = 0) (hφ : φ ≠ 0)
    (hσ : (φ + ρ) * (φ + ρ) = 1) (hinv : ∀ᶠ y in 𝓝 0, Ψ (Ψ (y, y), Ψ (y, y)) = y) :
    InertialCoinSunspots Ψ := by
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.mp hinv
  refine inertial_coin_sunspot_of_side hΨ hΨ0 hφ hσ (s := 1) (ρ1 := r / 2) (by norm_num)
    (by positivity) fun z hz1 hz2 => ?_
  have hz : 0 < z := by simpa using hz1
  have hz' : z ≤ r / 2 := by simpa using hz2
  have h := hrP (show dist z 0 < r by rw [Real.dist_0_eq_abs, abs_of_pos hz]; linarith)
  simp only [one_mul, h]
  exact ⟨hz, le_rfl⟩

/-- **For analytic rules the higher-order terms always decide** (Woodford (2003), Prop. 2.8,
p. 96; App. A.3, pp. 632–634; the complete characterisation on the boundary `φ_π ≠ 0`,
`|φ_π + ρ| = 1`): for a rule `Ψ` analytic at the steady state with `Ψ(0) = 0` and slopes
`φ_π ≠ 0`, `ρ`, the exact model has random sunspots at every scale on the coin tree **iff**
`D ∘ D` is the identity near `0`, or `D(D(y)) = y + c yᵐ + o(yᵐ)` with `c ≠ 0`, `m ≥ 2` and
(`c < 0` or `m` even); here `D(y) = Ψ(y, y)`. -/
theorem inertial_analytic_iff {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (han : AnalyticAt ℝ Ψ 0)
    (hΨd : HasFDerivAt Ψ (ruleD φ ρ) 0) (hΨ0 : Ψ 0 = 0) (hφ : φ ≠ 0)
    (hσ : (φ + ρ) * (φ + ρ) = 1) :
    InertialCoinSunspots Ψ ↔ ((∀ᶠ y in 𝓝 0, Ψ (Ψ (y, y), Ψ (y, y)) = y) ∨
      ∃ c : ℝ, ∃ m : ℕ, c ≠ 0 ∧ 2 ≤ m ∧
        ((fun y => Ψ (Ψ (y, y), Ψ (y, y)) - y - c * y ^ m) =o[𝓝 0] fun y => y ^ m) ∧
        (c < 0 ∨ Even m)) := by
  have hstrict : HasStrictFDerivAt Ψ (ruleD φ ρ) 0 := by
    have := han.hasStrictFDerivAt
    rwa [hΨd.fderiv] at this
  have h00 : Ψ ((0 : ℝ), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero]; exact hΨ0
  have hdiag : AnalyticAt ℝ (fun y : ℝ => Ψ (y, y)) 0 := by
    have hpair : AnalyticAt ℝ (fun y : ℝ => ((y, y) : ℝ × ℝ)) 0 :=
      analyticAt_id.prod analyticAt_id
    have han' : AnalyticAt ℝ Ψ ((fun y : ℝ => ((y, y) : ℝ × ℝ)) 0) := by
      rw [show ((fun y : ℝ => ((y, y) : ℝ × ℝ)) 0) = 0 from Prod.mk_zero_zero]
      exact han
    exact AnalyticAt.comp (g := Ψ) (f := fun y : ℝ => ((y, y) : ℝ × ℝ)) han' hpair
  have hDd := hasDerivAt_diag hΨd
  constructor
  · intro hsun
    rcases analytic_dichotomy (g := fun y => Ψ (y, y)) hσ h00 hDd hdiag with
      h | ⟨c, m, hc, hm, hexp⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, m, hc, hm, hexp,
        (inertial_coin_iff hstrict hΨ0 hφ hσ hm hc hexp).mp hsun⟩
  · rintro (h | ⟨c, m, hc, hm, hexp, hcrit⟩)
    · exact inertial_coin_sunspot_of_involutive hstrict hΨ0 hφ hσ h
    · exact (inertial_coin_iff hstrict hΨ0 hφ hσ hm hc hexp).mpr hcrit

end Woodford.PriceLevelDetermination.TidyR6InertialAnalytic
