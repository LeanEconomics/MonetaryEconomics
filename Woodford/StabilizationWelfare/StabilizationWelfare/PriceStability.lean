/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.HabitWelfare
import StabilizationWelfare.CrossSection
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The case for price stability

Woodford (2003), *Interest and Prices*, Chapter 6, §3, pp. 405–419 (with App. E.2, p. 695).

The Calvo cross-section is modelled exactly: the date-`t` distribution of log prices is the
measure `α·(old distribution shifted by the indexation increment) + (1 − α)·δ_{log p*_t}`, and
dispersion, the mean log price and the Dixit–Stiglitz index are integrals against it. The
second-order (Proposition 6.3) form of the dispersion law is treated alongside. Expectational
results hold for an arbitrary `ExpectationSystem` with bounded processes and genuine `tsum`s.

## Main results

* Exact Calvo cross-section: one period of staggered pricing is `CrossSection.calvoMixIdx`;
  `calvoAux`, moment recursions
  (`calvo_mean`, `calvo_zmom`, `calvo_mass`), the exact dispersion law (E.8)/(2.24) `calvo_disp`,
  `disp_nonneg`, `zero_disp_zmom` (zero dispersion ⇒ `log P = P̄`).
* Price stability eliminates dispersion: `reset_price_of_stable`, `price_stability_disp`
  (`Δ_t = α^{t+1}Δ_{−1} + α^{t+1}(1 − α^{t+1})(P̄_{−1} − log P)²`, exact),
  `price_stability_eliminates_dispersion`; and is necessary: `zero_dispersion_iff`,
  `zero_dispersion_inflation`, `calvo_zero_dispersion_iff` (zero dispersion at all dates ⟺ no
  initial dispersion and a constant price level).
* Second-order form (integrated by `Sequences.disp_integrated`): `disp_of_zero_inflation`
  (`π ≡ 0 ⇒ Δ_t = α^{t+1}Δ_{−1}`),
  `disp_zero_iff`; indexation (fn. 30): `indexation_path` (`π_t = γ^{t+1}π_{−1}`),
  `indexation_path_tendsto`, `indexation_stationary`.
* §3.1 (`Φ_y = 0`): `zero_path_feasible`, `zero_path_optimal`, `zero_loss_iff` (Calvo);
  `nc_predictable_zero_loss`, `nc_optimal_path`, `nc_zero_gap_iff` (New Classical, initial
  condition `E_{−1}π_0`); `idx_optimal_path`, `idx_unique` (indexation, `π_t = γ^{t+1}π_{−1}`);
  `habit_optimal_path` (habits + indexation, fn. 31 and p. 409).
* §3.2: `eq31`, `nc_E0_x` (`E_0x_t = 0`, `t ≥ 1`), `eq32` (3.2), `eq34` (3.4), `eq35` (3.5),
  `xss_iff` (`x_ss = (1 − β)κ⁻¹π_ss`).
* p. 415, the LQ steady-state calculation: `commit_gap`, `commit_optimal` (the first-order
  conditions characterise the unique optimal commitment), `commit_limits`,
  `longrun_inflation_zero` (coefficient `β`), `longrun_inflation_negative` (coefficient one:
  `π̄ = −(1 − β)λx*/(βκ) < 0` with `x̄ = 0`).
-/

namespace Woodford.StabilizationWelfare.PriceStability

open Filter Topology MeasureTheory HabitWelfare Sequences
open CrossSection (calvoMixIdx integral_calvoMixIdx integrable_calvoMixIdx)

/-! ### The exact Calvo cross-section of log prices -/

/-- Woodford (2003), App. E.2, p. 695: a cross-sectional distribution of log prices with finite
mass, mean, second moment, and `∫ e^{a p}` (`a = 1 − θ` gives the Dixit–Stiglitz index). -/
def Nice (a : ℝ) (ν : Measure ℝ) : Prop :=
  Integrable (fun _ => (1 : ℝ)) ν ∧ Integrable (fun p => p) ν ∧ Integrable (fun p => p ^ 2) ν ∧
    Integrable (fun p => Real.exp (a * p)) ν

/-- Woodford (2003), p. 695: shifted moments of a `Nice` distribution are integrable. -/
theorem Nice.shift {a : ℝ} {ν : Measure ℝ} (h : Nice a ν) (κ : ℝ) :
    Integrable (fun p => p + κ) ν ∧ Integrable (fun p => (p + κ) ^ 2) ν ∧
      Integrable (fun p => Real.exp (a * (p + κ))) ν := by
  obtain ⟨h1, hp, hp2, he⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have := hp.add (h1.const_mul κ)
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, mul_one]
  · have := (hp2.add ((hp.const_mul (2 * κ)))).add (h1.const_mul (κ ^ 2))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, mul_one]
    ring
  · have := he.const_mul (Real.exp (a * κ))
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [← Real.exp_add]
    ring_nf

/-- Woodford (2003), p. 695: one period of staggered pricing preserves `Nice`. -/
theorem Nice.step {a : ℝ} {ν : Measure ℝ} (h : Nice a ν) (α κ c : ℝ) :
    Nice a (calvoMixIdx α κ ν c) := by
  obtain ⟨hs1, hs2, hs3⟩ := h.shift κ
  exact ⟨integrable_calvoMixIdx α κ c h.1, integrable_calvoMixIdx α κ c hs1,
    integrable_calvoMixIdx α κ c hs2, integrable_calvoMixIdx α κ c hs3⟩

/-- Woodford (2003), App. E.2, p. 695: the date-`t` distribution of log prices is
`calvoAux (t + 1)`, starting from the pre-existing distribution `μ_{−1}` (`calvoAux 0`), with
indexation increments `k_t` (zero under Calvo) and new prices `p*_t`. -/
noncomputable def calvoAux (μm1 : Measure ℝ) (α : ℝ) (k pstar : ℕ → ℝ) : ℕ → Measure ℝ
  | 0 => μm1
  | t + 1 => calvoMixIdx α (k t) (calvoAux μm1 α k pstar t) (pstar t)

/-- Woodford (2003), p. 695: the total mass `∫ 1`. -/
noncomputable def mass (ν : Measure ℝ) : ℝ := ∫ _, (1 : ℝ) ∂ν

/-- Woodford (2003), p. 695: `P̄ ≡ E_i log p(i)`. -/
noncomputable def mean (ν : Measure ℝ) : ℝ := ∫ p, p ∂ν

/-- Woodford (2003), p. 695: `E_i (log p(i))²`. -/
noncomputable def smom (ν : Measure ℝ) : ℝ := ∫ p, p ^ 2 ∂ν

/-- Woodford (2003), (2.20), p. 399: price dispersion `Δ ≡ var_i log p(i)`. -/
noncomputable def disp (ν : Measure ℝ) : ℝ := smom ν - mean ν ^ 2

/-- Woodford (2003), Ch. 3 eq. (1.3): `Z ≡ E_i p(i)^{1−θ} = ∫ e^{(1−θ) log p}`, so that the
Dixit–Stiglitz index is `P = Z^{1/(1−θ)}` (`a = 1 − θ`). -/
noncomputable def zmom (a : ℝ) (ν : Measure ℝ) : ℝ := ∫ p, Real.exp (a * p) ∂ν

/-- Woodford (2003), p. 695: `∫(p + κ) = P̄ + κ·mass`. -/
theorem integral_shift1 {a : ℝ} {ν : Measure ℝ} (h : Nice a ν) (κ : ℝ) :
    ∫ p, (p + κ) ∂ν = mean ν + κ * mass ν := by
  have e : (fun p : ℝ => p + κ) = fun p => p + κ * (1 : ℝ) := by funext p; ring
  rw [e, integral_add h.2.1 (h.1.const_mul κ), integral_const_mul]
  rfl

/-- Woodford (2003), p. 695: `∫(p + κ)² = E p² + 2κP̄ + κ²·mass`. -/
theorem integral_shift2 {a : ℝ} {ν : Measure ℝ} (h : Nice a ν) (κ : ℝ) :
    ∫ p, (p + κ) ^ 2 ∂ν = smom ν + 2 * κ * mean ν + κ ^ 2 * mass ν := by
  have e : (fun p : ℝ => (p + κ) ^ 2) = fun p => (p ^ 2 + 2 * κ * p) + κ ^ 2 * (1 : ℝ) := by
    funext p; ring
  rw [e, integral_add (f := fun p : ℝ => p ^ 2 + 2 * κ * p) (g := fun _ => κ ^ 2 * (1 : ℝ))
    (h.2.2.1.add (h.2.1.const_mul _)) (h.1.const_mul _),
    integral_add (f := fun p : ℝ => p ^ 2) (g := fun p => 2 * κ * p) h.2.2.1
    (h.2.1.const_mul _), integral_const_mul, integral_const_mul]
  rfl

/-- Woodford (2003), p. 695: `∫ e^{a(p + κ)} = e^{aκ} ∫ e^{ap}`. -/
theorem integral_shiftZ {a : ℝ} {ν : Measure ℝ} (κ : ℝ) :
    ∫ p, Real.exp (a * (p + κ)) ∂ν = Real.exp (a * κ) * zmom a ν := by
  have e : (fun p : ℝ => Real.exp (a * (p + κ))) =
      fun p => Real.exp (a * κ) * Real.exp (a * p) := by
    funext p; rw [← Real.exp_add]; ring_nf
  rw [e, integral_const_mul]
  rfl

/-- Woodford (2003), p. 695: the mass after one pricing period. -/
theorem mass_step {a α : ℝ} {ν : Measure ℝ} (h : Nice a ν) (κ c : ℝ) (h0 : 0 ≤ α)
    (h1 : α ≤ 1) : mass (calvoMixIdx α κ ν c) = α * mass ν + (1 - α) := by
  unfold mass
  rw [integral_calvoMixIdx h0 h1 κ c h.1]
  ring

/-- Woodford (2003), p. 695: `P̄_t = α(P̄_{t−1} + κ_t) + (1 − α) log p*_t` (unit mass). -/
theorem mean_step {a α : ℝ} {ν : Measure ℝ} (h : Nice a ν) (hm : mass ν = 1) (κ c : ℝ)
    (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    mean (calvoMixIdx α κ ν c) = α * (mean ν + κ) + (1 - α) * c := by
  have := integral_calvoMixIdx (f := fun p => p) h0 h1 κ c (h.shift κ).1
  rw [integral_shift1 h, hm, mul_one] at this
  exact this

/-- Woodford (2003), p. 695: the second moment after one pricing period (unit mass). -/
theorem smom_step {a α : ℝ} {ν : Measure ℝ} (h : Nice a ν) (hm : mass ν = 1) (κ c : ℝ)
    (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    smom (calvoMixIdx α κ ν c) = α * (smom ν + 2 * κ * mean ν + κ ^ 2) + (1 - α) * c ^ 2 := by
  have := integral_calvoMixIdx (f := fun p => p ^ 2) h0 h1 κ c (h.shift κ).2.1
  rw [integral_shift2 h, hm, mul_one] at this
  exact this

/-- Woodford (2003), Ch. 3 eq. (2.2): `Z_t = αe^{aκ_t}Z_{t−1} + (1 − α)e^{a log p*_t}`. -/
theorem zmom_step {a α : ℝ} {ν : Measure ℝ} (h : Nice a ν) (κ c : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    zmom a (calvoMixIdx α κ ν c) = α * (Real.exp (a * κ) * zmom a ν) +
      (1 - α) * Real.exp (a * c) := by
  have := integral_calvoMixIdx (f := fun p => Real.exp (a * p)) h0 h1 κ c (h.shift κ).2.2
  rw [integral_shiftZ] at this
  exact this

/-- **Woodford (2003), (E.8), p. 695, and (2.24), p. 402, EXACT.** For a unit-mass distribution and
`0 ≤ α < 1`, one period of staggered pricing (with indexation increment `κ`) gives
`Δ_t = αΔ_{t−1} + α/(1 − α)·(P̄_t − P̄_{t−1} − κ)²`. -/
theorem disp_step {a α : ℝ} {ν : Measure ℝ} (h : Nice a ν) (hm : mass ν = 1) (κ c : ℝ)
    (h0 : 0 ≤ α) (h1 : α < 1) :
    disp (calvoMixIdx α κ ν c) = α * disp ν +
      α / (1 - α) * (mean (calvoMixIdx α κ ν c) - mean ν - κ) ^ 2 := by
  unfold disp
  exact Moments.mix_var_meanChange (by linarith) (mean_step h hm κ c h0 h1.le)
    (smom_step h hm κ c h0 h1.le)

/-- Woodford (2003), p. 695: every date's distribution is `Nice`. -/
theorem calvo_nice {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1) (t : ℕ) :
    Nice a (calvoAux μm1 α k pstar t) := by
  induction t with
  | zero => exact h
  | succ t ih => exact ih.step α (k t) (pstar t)

/-- Woodford (2003), p. 695: every date's distribution has unit mass. -/
theorem calvo_mass {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (hm : mass μm1 = 1) (h0 : 0 ≤ α) (h1 : α ≤ 1) (t : ℕ) :
    mass (calvoAux μm1 α k pstar t) = 1 := by
  induction t with
  | zero => exact hm
  | succ t ih =>
    change mass (calvoMixIdx α (k t) _ (pstar t)) = 1
    rw [mass_step (calvo_nice h t) _ _ h0 h1, ih]
    ring

/-- **Woodford (2003), (E.8), p. 695 / (2.24), p. 402 (exact, every date).**
`Δ_t = αΔ_{t−1} + α/(1 − α)(P̄_t − P̄_{t−1} − k_t)²`. -/
theorem calvo_disp {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (hm : mass μm1 = 1) (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    disp (calvoAux μm1 α k pstar (t + 1)) = α * disp (calvoAux μm1 α k pstar t) +
      α / (1 - α) * (mean (calvoAux μm1 α k pstar (t + 1)) -
        mean (calvoAux μm1 α k pstar t) - k t) ^ 2 :=
  disp_step (calvo_nice h t) (calvo_mass h hm h0 h1.le t) (k t) (pstar t) h0 h1

/-- Woodford (2003), p. 695: `P̄_t = α(P̄_{t−1} + k_t) + (1 − α) log p*_t`. -/
theorem calvo_mean {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (hm : mass μm1 = 1) (h0 : 0 ≤ α) (h1 : α ≤ 1) (t : ℕ) :
    mean (calvoAux μm1 α k pstar (t + 1)) =
      α * (mean (calvoAux μm1 α k pstar t) + k t) + (1 - α) * pstar t :=
  mean_step (calvo_nice h t) (calvo_mass h hm h0 h1 t) (k t) (pstar t) h0 h1

/-- Woodford (2003), Ch. 3 (1.3)/(2.2): `Z_t = αe^{ak_t}Z_{t−1} + (1 − α)e^{a log p*_t}`. -/
theorem calvo_zmom {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (h0 : 0 ≤ α) (h1 : α ≤ 1) (t : ℕ) :
    zmom a (calvoAux μm1 α k pstar (t + 1)) =
      α * (Real.exp (a * k t) * zmom a (calvoAux μm1 α k pstar t)) +
        (1 - α) * Real.exp (a * pstar t) :=
  zmom_step (calvo_nice h t) (k t) (pstar t) h0 h1

/-- Woodford (2003), (2.20): dispersion is nonnegative, `Δ = ∫(p − P̄)² ≥ 0`. -/
theorem disp_nonneg {a : ℝ} {ν : Measure ℝ} (h : Nice a ν) (hm : mass ν = 1) : 0 ≤ disp ν := by
  have e := integral_shift2 h (-mean ν)
  rw [hm] at e
  have : disp ν = ∫ p, (p + -mean ν) ^ 2 ∂ν := by rw [e]; unfold disp; ring
  rw [this]
  exact integral_nonneg fun p => sq_nonneg _

/-- **Woodford (2003), p. 405 ("eventually all goods prices are equal").** With zero dispersion
all log prices equal `P̄` almost everywhere, so the Dixit–Stiglitz index satisfies
`log P = P̄`: `Z = e^{aP̄}`. -/
theorem zero_disp_zmom {a : ℝ} {ν : Measure ℝ} (h : Nice a ν) (hm : mass ν = 1)
    (hd : disp ν = 0) : zmom a ν = Real.exp (a * mean ν) := by
  have e := integral_shift2 h (-mean ν)
  rw [hm] at e
  have hI : ∫ p, (p + -mean ν) ^ 2 ∂ν = 0 := by rw [e]; unfold disp at hd; linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg (p + -mean ν))
    (h.shift (-mean ν)).2.1).mp hI
  have hcongr : (fun p => Real.exp (a * p)) =ᵐ[ν] fun _ => Real.exp (a * mean ν) * 1 := by
    filter_upwards [hae] with p hp
    have : p + -mean ν = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hp
    rw [mul_one, show p = mean ν by linarith]
  unfold zmom
  rw [integral_congr_ae hcongr, integral_const_mul]
  change Real.exp (a * mean ν) * mass ν = _
  rw [hm, mul_one]

/-! ### Price stability eliminates dispersion (Calvo, exact) -/

/-- **Woodford (2003), p. 405: a stable price level makes all new prices equal.** Under Calvo
pricing (`k ≡ 0`), if the Dixit–Stiglitz index is constant (`Z_t = Z_{t−1}` for all `t ≥ 0`,
`a = 1 − θ ≠ 0`), then every new price is `log p*_t = log P_{−1} = (log Z_{−1})/a`. -/
theorem reset_price_of_stable {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (ha : a ≠ 0) (h0 : 0 ≤ α) (h1 : α < 1) (hk : ∀ t, k t = 0)
    (hstab : ∀ t, zmom a (calvoAux μm1 α k pstar (t + 1)) = zmom a (calvoAux μm1 α k pstar t))
    (t : ℕ) : pstar t = Real.log (zmom a μm1) / a := by
  have hconst : ∀ s, zmom a (calvoAux μm1 α k pstar s) = zmom a μm1 := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [hstab s, ih]
  have hz := calvo_zmom (k := k) (pstar := pstar) h h0 h1.le t
  rw [hstab t, hk t, mul_zero, Real.exp_zero, one_mul] at hz
  have h1α : 1 - α ≠ 0 := by linarith
  have he : zmom a (calvoAux μm1 α k pstar t) = Real.exp (a * pstar t) := by
    have : (1 - α) * (zmom a (calvoAux μm1 α k pstar t) - Real.exp (a * pstar t)) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h1α
    · linarith
  rw [hconst t] at he
  rw [he, Real.log_exp]
  field_simp

/-- **Woodford (2003), p. 405 and §3, exact: under price stability dispersion decays.** Under
Calvo pricing with a constant price level, with `c = log P_{−1}`,
`P̄_t − c = α^{t+1}(P̄_{−1} − c)` and
`Δ_t = α^{t+1}Δ_{−1} + α^{t+1}(1 − α^{t+1})(P̄_{−1} − c)²`. (The second term, absent from the
second-order statement `Δ_t = α^{t+1}Δ_{−1}`, is of fourth order: `P̄_{−1} − log P_{−1} =
O(Δ_{−1})`.) -/
theorem price_stability_disp {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (hm : mass μm1 = 1) (ha : a ≠ 0) (h0 : 0 ≤ α) (h1 : α < 1) (hk : ∀ t, k t = 0)
    (hstab : ∀ t, zmom a (calvoAux μm1 α k pstar (t + 1)) = zmom a (calvoAux μm1 α k pstar t))
    (t : ℕ) :
    mean (calvoAux μm1 α k pstar t) - Real.log (zmom a μm1) / a =
        α ^ t * (mean μm1 - Real.log (zmom a μm1) / a) ∧
      disp (calvoAux μm1 α k pstar t) = α ^ t * disp μm1 +
        α ^ t * (1 - α ^ t) * (mean μm1 - Real.log (zmom a μm1) / a) ^ 2 := by
  set c := Real.log (zmom a μm1) / a with hc
  have hp := reset_price_of_stable h ha h0 h1 hk hstab
  induction t with
  | zero => exact ⟨by simp; rfl, by simp; rfl⟩
  | succ t ih =>
    have hmean := calvo_mean (k := k) (pstar := pstar) h hm h0 h1.le t
    rw [hk t, hp t, add_zero] at hmean
    have hdisp := calvo_disp (k := k) (pstar := pstar) h hm h0 h1 t
    rw [hk t, sub_zero] at hdisp
    have h1α : 1 - α ≠ 0 := by linarith
    refine ⟨?_, ?_⟩
    · rw [hmean, pow_succ]
      linear_combination α * ih.1
    · rw [hdisp, ih.2, hmean]
      have hm' := ih.1
      have e : α * mean (calvoAux μm1 α k pstar t) + (1 - α) * c -
          mean (calvoAux μm1 α k pstar t) = -(1 - α) * (α ^ t * (mean μm1 - c)) := by
        linear_combination (-(1 - α)) * hm'
      rw [e]
      field_simp
      ring

/-- **Woodford (2003), p. 405: price stability eliminates dispersion.** Under Calvo pricing with a
constant price level, dispersion vanishes in the limit, and is zero at all dates if the initial
distribution has no dispersion. -/
theorem price_stability_eliminates_dispersion {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ}
    (h : Nice a μm1) (hm : mass μm1 = 1) (ha : a ≠ 0) (h0 : 0 ≤ α) (h1 : α < 1)
    (hk : ∀ t, k t = 0)
    (hstab : ∀ t, zmom a (calvoAux μm1 α k pstar (t + 1)) = zmom a (calvoAux μm1 α k pstar t)) :
    Tendsto (fun t => disp (calvoAux μm1 α k pstar t)) atTop (𝓝 0) ∧
      (disp μm1 = 0 → ∀ t, disp (calvoAux μm1 α k pstar t) = 0) := by
  have hf := fun t => (price_stability_disp h hm ha h0 h1 hk hstab t).2
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  refine ⟨?_, fun hd t => ?_⟩
  · simp_rw [hf]
    have := ((hpow.mul_const (disp μm1)).add ((hpow.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub
      hpow)).mul_const ((mean μm1 - Real.log (zmom a μm1) / a) ^ 2)))
    simpa using this
  · rw [hf t, hd]
    have hz := zero_disp_zmom h hm hd
    rw [hz, Real.log_exp]
    field_simp
    ring

/-- Woodford (2003), App. E.3: if `x, y ≥ 0`, `p, q > 0` and `p x + q y = 0` then `x = y = 0`. -/
theorem nonneg_sum_zero {p q x y : ℝ} (hp : 0 < p) (hq : 0 < q) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : p * x + q * y = 0) : x = 0 ∧ y = 0 := by
  have h1 : p * x = 0 := by nlinarith [mul_nonneg hp.le hx, mul_nonneg hq.le hy]
  have h2 : q * y = 0 := by linarith
  exact ⟨(mul_eq_zero.mp h1).resolve_left hp.ne', (mul_eq_zero.mp h2).resolve_left hq.ne'⟩

/-- **Woodford (2003), pp. 405–406 and fn. 30 (exact): zero dispersion at every date holds iff
there is no initial dispersion and the mean log price moves exactly with the indexation
increment, `P̄_t − P̄_{t−1} = k_t`** (`k ≡ 0`: the price level is constant). -/
theorem zero_dispersion_iff {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (hm : mass μm1 = 1) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ t, disp (calvoAux μm1 α k pstar (t + 1)) = 0) ↔
      disp μm1 = 0 ∧ ∀ t, mean (calvoAux μm1 α k pstar (t + 1)) -
        mean (calvoAux μm1 α k pstar t) = k t := by
  have hq : 0 < α / (1 - α) := div_pos hα0 (by linarith)
  constructor
  · intro hz
    have key : ∀ t, disp (calvoAux μm1 α k pstar t) = 0 ∧
        (mean (calvoAux μm1 α k pstar (t + 1)) - mean (calvoAux μm1 α k pstar t) - k t) ^ 2
          = 0 := by
      intro t
      have hd := calvo_disp (k := k) (pstar := pstar) h hm hα0.le hα1 t
      rw [hz t] at hd
      exact nonneg_sum_zero hα0 hq (disp_nonneg (calvo_nice h t)
        (calvo_mass h hm hα0.le hα1.le t)) (sq_nonneg _) hd.symm
    refine ⟨(key 0).1, fun t => ?_⟩
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (key t).2
    linarith
  · rintro ⟨hd0, hk⟩ t
    induction t with
    | zero =>
      rw [calvo_disp h hm hα0.le hα1 0, show calvoAux μm1 α k pstar 0 = μm1 from rfl, hd0]
      have := hk 0
      simp only [show calvoAux μm1 α k pstar 0 = μm1 from rfl] at this
      rw [show mean (calvoAux μm1 α k pstar (0 + 1)) - mean μm1 - k 0 = 0 by linarith]
      ring
    | succ t ih =>
      rw [calvo_disp h hm hα0.le hα1 (t + 1), ih,
        show mean (calvoAux μm1 α k pstar (t + 1 + 1)) - mean (calvoAux μm1 α k pstar (t + 1)) -
          k (t + 1) = 0 by linarith [hk (t + 1)]]
      ring

/-- **Woodford (2003), p. 406 and fn. 30 (exact): with zero dispersion, inflation of the
Dixit–Stiglitz index equals the indexation increment**, `log P_t − log P_{t−1} = k_t` (so under
Calvo pricing, `π_t = 0`; with indexation `k_t = γπ_{t−1}`, `π_t = γπ_{t−1}`). -/
theorem zero_dispersion_inflation {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ} (h : Nice a μm1)
    (hm : mass μm1 = 1) (ha : a ≠ 0) (hα0 : 0 < α) (hα1 : α < 1)
    (hz : ∀ t, disp (calvoAux μm1 α k pstar (t + 1)) = 0) (t : ℕ) :
    Real.log (zmom a (calvoAux μm1 α k pstar (t + 1))) / a -
      Real.log (zmom a (calvoAux μm1 α k pstar t)) / a = k t := by
  obtain ⟨hd0, hk⟩ := (zero_dispersion_iff h hm hα0 hα1).mp hz
  have hzero : ∀ s, disp (calvoAux μm1 α k pstar s) = 0 := by
    intro s; cases s with
    | zero => exact hd0
    | succ s => exact hz s
  have hlog : ∀ s, Real.log (zmom a (calvoAux μm1 α k pstar s)) / a =
      mean (calvoAux μm1 α k pstar s) := by
    intro s
    rw [zero_disp_zmom (calvo_nice h s) (calvo_mass h hm hα0.le hα1.le s) (hzero s),
      Real.log_exp]
    field_simp
  rw [hlog, hlog, hk t]

/-- **Woodford (2003), pp. 405–406 (exact, Calvo): zero dispersion at every date ⟺ no initial
dispersion and a constant price level** (`Z_t = Z_{t−1}`, i.e. `π_t = 0`). Price stability is
both sufficient and necessary. -/
theorem calvo_zero_dispersion_iff {a α : ℝ} {μm1 : Measure ℝ} {k pstar : ℕ → ℝ}
    (h : Nice a μm1) (hm : mass μm1 = 1) (ha : a ≠ 0) (hα0 : 0 < α) (hα1 : α < 1)
    (hk : ∀ t, k t = 0) :
    (∀ t, disp (calvoAux μm1 α k pstar (t + 1)) = 0) ↔
      disp μm1 = 0 ∧ ∀ t, zmom a (calvoAux μm1 α k pstar (t + 1)) =
        zmom a (calvoAux μm1 α k pstar t) := by
  constructor
  · intro hz
    refine ⟨((zero_dispersion_iff h hm hα0 hα1).mp hz).1, fun t => ?_⟩
    have hi := zero_dispersion_inflation h hm ha hα0 hα1 hz t
    rw [hk t, sub_eq_zero, div_left_inj' ha] at hi
    have hpos : ∀ s, 0 < zmom a (calvoAux μm1 α k pstar s) := by
      obtain ⟨hd0, -⟩ := (zero_dispersion_iff h hm hα0 hα1).mp hz
      intro s
      have hd : disp (calvoAux μm1 α k pstar s) = 0 := by
        cases s with
        | zero => exact hd0
        | succ s => exact hz s
      rw [zero_disp_zmom (calvo_nice h s) (calvo_mass h hm hα0.le hα1.le s) hd]
      exact Real.exp_pos _
    exact Real.log_injOn_pos (hpos (t + 1)) (hpos t) hi
  · rintro ⟨hd0, hstab⟩ t
    exact (price_stability_eliminates_dispersion h hm ha hα0.le hα1 hk hstab).2 hd0 (t + 1)

/-! ### The second-order dispersion law (Proposition 6.3 form) -/

/-- **Woodford (2003), p. 405 (second-order form): price stability eliminates dispersion.** If
`p ≡ 0` (`π ≡ 0`, or `π_t = γπ_{t−1}` under indexation) then `Δ_t = α^{t+1}Δ_{−1}`. -/
theorem disp_of_zero_inflation {α Δm1 : ℝ} {Δ p : ℕ → ℝ}
    (hrec : ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2) (hp : ∀ t, p t = 0) (t : ℕ) :
    Δ t = α ^ (t + 1) * Δm1 := by
  have h := Sequences.disp_integrated (V := lagS Δm1 Δ) (q := fun t => p t ^ 2)
    (c := α / (1 - α)) (fun t => by rw [lagS_succ]; exact hrec t) t
  simp only [lagS_succ, lagS_zero] at h
  rw [h]
  simp [hp]

/-- **Woodford (2003), pp. 405–406 (second-order form): price stability is also necessary.** For
`0 < α < 1` and `Δ_{−1} ≥ 0`: `Δ_t = 0` for all `t ≥ 0` iff `Δ_{−1} = 0` and `p_t = 0` for all
`t` (`π_t = 0`; under indexation `π_t = γπ_{t−1}`). -/
theorem disp_zero_iff {α Δm1 : ℝ} {Δ p : ℕ → ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hm : 0 ≤ Δm1)
    (hrec : ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2) :
    (∀ t, Δ t = 0) ↔ Δm1 = 0 ∧ ∀ t, p t = 0 := by
  have hq : 0 < α / (1 - α) := div_pos hα0 (by linarith)
  constructor
  · intro hz
    have h0 := hrec 0
    rw [hz 0, lagS_zero] at h0
    have k0 := nonneg_sum_zero hα0 hq hm (sq_nonneg _) h0.symm
    refine ⟨k0.1, fun t => ?_⟩
    cases t with
    | zero => exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp k0.2
    | succ t =>
      have ht := hrec (t + 1)
      rw [hz (t + 1), lagS_succ, hz t] at ht
      have := nonneg_sum_zero hα0 hq le_rfl (sq_nonneg _) ht.symm
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.2
  · rintro ⟨hd, hp⟩ t
    rw [disp_of_zero_inflation hrec hp t, hd, mul_zero]

/-- **Woodford (2003), fn. 30, p. 406 and p. 408:** `π_t = γπ_{t−1}` for all `t ≥ 0` iff
`π_t = γ^{t+1}π_{−1}`. -/
theorem indexation_path (γ πm1 : ℝ) (π : ℕ → ℝ) :
    (∀ t, π t - γ * lagS πm1 π t = 0) ↔ ∀ t, π t = γ ^ (t + 1) * πm1 := by
  constructor
  · intro h t
    induction t with
    | zero => have := h 0; rw [lagS_zero] at this; rw [zero_add, pow_one]; linarith
    | succ t ih => have := h (t + 1); rw [lagS_succ, ih] at this; rw [pow_succ]; linarith
  · intro h t
    cases t with
    | zero => rw [h 0, lagS_zero]; ring
    | succ t => rw [lagS_succ, h (t + 1), h t]; ring

/-- **Woodford (2003), fn. 30, p. 406:** for `|γ| < 1`, `π_t = γ^{t+1}π_{−1} → 0` ("zero inflation
… at least asymptotically"). -/
theorem indexation_path_tendsto {γ πm1 : ℝ} (hγ : |γ| < 1) :
    Tendsto (fun t : ℕ => γ ^ (t + 1) * πm1) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hγ).comp (tendsto_add_atTop_nat 1)
  simpa using h.mul_const πm1

/-- **Woodford (2003), fn. 30, p. 406:** a stationary (constant) inflation rate with
`π_t = γπ_{t−1}` and `γ ≠ 1` is zero. -/
theorem indexation_stationary {γ πbar : ℝ} (hγ : γ ≠ 1) {π : ℕ → ℝ} (hc : ∀ t, π t = πbar)
    (hp : ∀ t, π t - γ * lagS πbar π t = 0) : πbar = 0 := by
  have h := hp 1
  rw [lagS_succ, hc 1, hc 0] at h
  have : (1 - γ) * πbar = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hγ))

/-! ### Optimality of price stability with an efficient natural rate (§3.1) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (2.18), p. 399: the New Keynesian AS relation
`π_t = κx_t + βE_tπ_{t+1}`. -/
def NKPC (κ β : ℝ) (π x : ℕ → Ω → ℝ) : Prop := ∀ t, π t = κ • x t + β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), (2.21)–(2.22), p. 400 with `x* = 0`: the realised discounted loss
`∑ βᵗ(π_t² + λx_t²)`. -/
noncomputable def lossDisc (β lam : ℝ) (π x : ℕ → Ω → ℝ) (w : Ω) : ℝ :=
  ∑' t, β ^ t * (π t w ^ 2 + lam * x t w ^ 2)

/-- **Woodford (2003), p. 407: `π = x = 0` is feasible under (2.18)** from any initial condition
(the relation is purely forward-looking), for any expectation system. -/
theorem zero_path_feasible (κ β : ℝ) : NKPC 𝔼 κ β (fun _ => 0) (fun _ => 0) := by
  intro t
  rw [map_zero, smul_zero, smul_zero, add_zero]

/-- **Woodford (2003), p. 407: with `Φ_y = 0`, `π = x = 0` attains the global minimum (zero) of the
expected discounted loss (2.22)** among all paths (in particular all feasible ones). -/
theorem zero_path_optimal {β lam : ℝ} (h0 : 0 ≤ β) (hlam : 0 ≤ lam) (π x : ℕ → Ω → ℝ) (w : Ω) :
    𝔼.E 0 (lossDisc β lam (fun _ => 0) (fun _ => 0)) w ≤ 𝔼.E 0 (lossDisc β lam π x) w := by
  have hz : lossDisc β lam (fun _ => (0 : Ω → ℝ)) (fun _ => 0) = fun _ => 0 := by
    funext w'; simp [lossDisc]
  rw [hz, 𝔼.const]
  have hnn : (fun _ : Ω => (0 : ℝ)) ≤ lossDisc β lam π x := fun w' =>
    tsum_nonneg fun t => mul_nonneg (pow_nonneg h0 t) (by positivity)
  have := 𝔼.mono 0 hnn w
  rw [𝔼.const] at this
  exact this

/-- **Woodford (2003), p. 407 ("if and only if"): the minimum is attained only by `π = x = 0`**
(pathwise, `λ > 0`, `0 < β < 1`, bounded paths): a zero discounted loss forces `π_t = x_t = 0`. -/
theorem zero_loss_iff {β lam : ℝ} (h0 : 0 < β) (h1 : β < 1) (hlam : 0 < lam) {π x : ℕ → ℝ}
    (hπ : Bdd π) (hx : Bdd x) :
    ∑' t, β ^ t * (π t ^ 2 + lam * x t ^ 2) = 0 ↔ ∀ t, π t = 0 ∧ x t = 0 := by
  have hs : Summable (fun t => β ^ t * (π t ^ 2 + lam * x t ^ 2)) :=
    ((hπ.pow 2).add ((Bdd.const lam).mul (hx.pow 2))).summable h0.le h1
  have hnn : 0 ≤ fun t => β ^ t * (π t ^ 2 + lam * x t ^ 2) := fun t =>
    mul_nonneg (pow_nonneg h0.le t) (by positivity)
  constructor
  · intro h t
    have hz := (hasSum_zero_iff_of_nonneg hnn).mp (h ▸ hs.hasSum)
    have ht := congrFun hz t
    simp only [Pi.zero_apply] at ht
    have hb : 0 < β ^ t := pow_pos h0 t
    have h2 : π t ^ 2 + lam * x t ^ 2 = 0 := (mul_eq_zero.mp ht).resolve_left hb.ne'
    have := nonneg_sum_zero one_pos hlam (sq_nonneg (π t)) (sq_nonneg (x t)) (by linarith)
    exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.1,
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.2⟩
  · intro h
    simp [h]

/-- Woodford (2003), eq. (2.14), p. 397: the previous-period expectation `E_{t−1}π_t`, with the
pre-commitment expectation `E_{−1}π_0 = e₀` given. -/
def Eprev (π : ℕ → Ω → ℝ) (e0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => e0
  | t + 1 => 𝔼.E t (π (t + 1))

/-- Woodford (2003), eq. (2.14), p. 397: the New Classical AS relation `π_t = κx_t + E_{t−1}π_t`. -/
def NCAS (κ : ℝ) (e0 : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop := ∀ t, π t = κ • x t + Eprev 𝔼 π e0 t

/-- **Woodford (2003), p. 408 (New Classical case, `Φ_y = 0`).** Committing to any path that is
predictable a period in advance (`E_tπ_{t+1} = π_{t+1}`) with `π_0 = E_{−1}π_0` and `x ≡ 0` is
feasible under (2.14) and makes every term of the loss (2.16) zero; e.g. `π_0 = E_{−1}π_0`,
`π_t = 0` for `t ≥ 1`. -/
theorem nc_predictable_zero_loss (κ : ℝ) {e0 : Ω → ℝ} {π : ℕ → Ω → ℝ} (h0 : π 0 = e0)
    (hpred : ∀ t, 𝔼.E t (π (t + 1)) = π (t + 1)) :
    NCAS 𝔼 κ e0 π (fun _ => 0) ∧ ∀ t, π t - Eprev 𝔼 π e0 t = 0 := by
  have hz : ∀ t, π t - Eprev 𝔼 π e0 t = 0 := by
    intro t
    cases t with
    | zero => rw [h0]; exact sub_self e0
    | succ t => change π (t + 1) - 𝔼.E t (π (t + 1)) = 0; rw [hpred t, sub_self]
  exact ⟨fun t => by rw [smul_zero, zero_add]; exact sub_eq_zero.mp (hz t), hz⟩

/-- Woodford (2003), p. 408: the particular path `π_0 = E_{−1}π_0`, `π_t = 0` (`t ≥ 1`). -/
theorem nc_optimal_path (κ : ℝ) (e0 : Ω → ℝ) :
    NCAS 𝔼 κ e0 (fun t => if t = 0 then e0 else 0) (fun _ => 0) ∧
      ∀ t, (fun t => if t = 0 then e0 else 0) t - Eprev 𝔼 (fun t => if t = 0 then e0 else 0) e0 t
        = 0 :=
  nc_predictable_zero_loss 𝔼 κ (by simp) (fun t => by simp)

/-- **Woodford (2003), pp. 398, 408: under (2.14) the loss (2.16) with `x* = 0` is zero at every
date iff the output gap is identically zero iff inflation is never a surprise**
(`κ ≠ 0`: `π_t − E_{t−1}π_t = κx_t`). -/
theorem nc_zero_gap_iff {κ : ℝ} (hκ : κ ≠ 0) {e0 : Ω → ℝ} {π x : ℕ → Ω → ℝ}
    (hAS : NCAS 𝔼 κ e0 π x) : (∀ t, x t = 0) ↔ ∀ t, π t = Eprev 𝔼 π e0 t := by
  refine forall_congr' fun t => ?_
  have h := hAS t
  constructor
  · intro hx; rw [h, hx, smul_zero, zero_add]
  · intro hπ
    have : κ • x t = 0 := by rw [hπ] at h; exact (add_eq_right.mp h.symm)
    exact (smul_eq_zero.mp this).resolve_left hκ

/-- Woodford (2003), eq. (2.23), p. 402: the AS relation with indexation
`π_t − γπ_{t−1} = κx_t + βE_t[π_{t+1} − γπ_t]`. -/
def ASidx (κ β γ : ℝ) (πm1 : Ω → ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t - γ • lagP πm1 π t = κ • x t + β • 𝔼.E t (π (t + 1) - γ • π t)

/-- Woodford (2003), p. 408: the deterministic indexation path `π_t = γ^{t+1}π_{−1}`. -/
def idxPath (γ : ℝ) (πm1 : Ω → ℝ) (t : ℕ) : Ω → ℝ := fun w => γ ^ (t + 1) * πm1 w

/-- Woodford (2003), p. 408: along the indexation path `π_t − γπ_{t−1} = 0`. -/
theorem idxPath_quasi (γ : ℝ) (πm1 : Ω → ℝ) (t : ℕ) :
    idxPath γ πm1 t - γ • lagP πm1 (idxPath γ πm1) t = 0 := by
  funext w
  cases t with
  | zero =>
    simp only [idxPath, lagP, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  | succ t =>
    simp only [idxPath, lagP, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring

/-- **Woodford (2003), p. 408 (indexation, `Φ_y = 0`): `π_t = γ^{t+1}π_{−1}`, `x_t = 0` is feasible
under (2.23) and makes the loss (2.25) zero at every date**, whatever the initial condition. -/
theorem idx_optimal_path (κ β γ : ℝ) (πm1 : Ω → ℝ) :
    ASidx 𝔼 κ β γ πm1 (fun _ => 0) (idxPath γ πm1) ∧
      ∀ t, idxPath γ πm1 t - γ • lagP πm1 (idxPath γ πm1) t = 0 := by
  refine ⟨fun t => ?_, idxPath_quasi γ πm1⟩
  have h : idxPath γ πm1 (t + 1) - γ • idxPath γ πm1 t = 0 := idxPath_quasi γ πm1 (t + 1)
  rw [idxPath_quasi, h, map_zero, smul_zero, smul_zero, add_zero]

/-- **Woodford (2003), p. 408: the optimum under indexation is unique** (pathwise, `λ > 0`,
`0 < β < 1`, bounded paths): a zero discounted loss (2.25) forces `x ≡ 0` and
`π_t = γ^{t+1}π_{−1}`. -/
theorem idx_unique {β lam γ πm1 : ℝ} (h0 : 0 < β) (h1 : β < 1) (hlam : 0 < lam) {π x : ℕ → ℝ}
    (hπ : Bdd π) (hx : Bdd x)
    (hz : ∑' t, β ^ t * ((π t - γ * lagS πm1 π t) ^ 2 + lam * x t ^ 2) = 0) :
    (∀ t, x t = 0) ∧ ∀ t, π t = γ ^ (t + 1) * πm1 := by
  have h := (zero_loss_iff h0 h1 hlam (hπ.sub ((Bdd.const γ).mul (hπ.lagS πm1))) hx).mp hz
  exact ⟨fun t => (h t).2, (indexation_path γ πm1 π).mp fun t => (h t).1⟩

/-- **Woodford (2003), fn. 31, p. 407, and p. 409 (habit persistence and indexation,
`Φ_y = 0`).** The deterministic path `π_t = γ^{t+1}π_{−1}`, `x_t = δ^{t+1}x_{−1}` is feasible under
(2.31) and makes both terms of (2.29) zero (`x̂* = 0`, `xhat_of_Phi_zero`). -/
theorem habit_optimal_path (κ δ β γ : ℝ) (πm1 xm1 : Ω → ℝ) :
    AS231 𝔼 κ δ β γ πm1 xm1 (idxPath δ xm1) (idxPath γ πm1) ∧
      (∀ t, idxPath γ πm1 t - γ • lagP πm1 (idxPath γ πm1) t = 0) ∧
      ∀ t, idxPath δ xm1 t - δ • lagP xm1 (idxPath δ xm1) t = 0 := by
  refine ⟨fun t => ?_, idxPath_quasi γ πm1, idxPath_quasi δ xm1⟩
  have hx : idxPath δ xm1 (t + 1) - δ • idxPath δ xm1 t = 0 := idxPath_quasi δ xm1 (t + 1)
  have hp : idxPath γ πm1 (t + 1) - γ • idxPath γ πm1 t = 0 := idxPath_quasi γ πm1 (t + 1)
  unfold xTildeP
  rw [idxPath_quasi, idxPath_quasi, hx, hp, map_zero, smul_zero, sub_zero, smul_zero, smul_zero,
    add_zero]

/-! ### A mildly inefficient natural rate (§3.2): (3.1)–(3.5) -/

/-- **Woodford (2003), eqs. (3.1) and (3.3), pp. 412–413:**
`L = (π − π^e)² + λ(x − x*)² = (π − π^e)² − 2λx*x + λx² + λx*²` (`π^e = E_{t−1}π_t`, or `0` in
(3.3)); `λx*²` is t.i.p. -/
theorem eq31 (π pe x xs lam : ℝ) :
    (π - pe) ^ 2 + lam * (x - xs) ^ 2 = (π - pe) ^ 2 - 2 * lam * xs * x + lam * x ^ 2 +
      lam * xs ^ 2 := by ring

/-- **Woodford (2003), p. 412: under (2.14), `E_0 x_t = 0` for `t ≥ 1` regardless of policy**
(`κ ≠ 0`; the law of iterated expectations). -/
theorem nc_E0_x {κ : ℝ} (hκ : κ ≠ 0) {e0 : Ω → ℝ} {π x : ℕ → Ω → ℝ} (hAS : NCAS 𝔼 κ e0 π x)
    (t : ℕ) : 𝔼.E 0 (x (t + 1)) = 0 := by
  have h := hAS (t + 1)
  change π (t + 1) = κ • x (t + 1) + 𝔼.E t (π (t + 1)) at h
  have hk : κ • x (t + 1) = π (t + 1) - 𝔼.E t (π (t + 1)) := by
    rw [eq_sub_iff_add_eq]; exact h.symm
  have : κ • 𝔼.E 0 (x (t + 1)) = 0 := by
    rw [← map_smul, hk, map_sub, 𝔼.tower (Nat.zero_le t), sub_self]
  exact (smul_eq_zero.mp this).resolve_left hκ

/-- Woodford (2003), pp. 412–413: `E_0 ∑ βᵗx_t = ∑ βᵗE_0x_t` for a bounded process. -/
theorem E0_tsum_x {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {x : ℕ → Ω → ℝ}
    (hx : ∀ t w, |x t w| ≤ M) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, β ^ t * x t w') w = ∑' t, β ^ t * 𝔼.E 0 (x t) w := by
  have hb : ∀ k w', |β ^ k * x k w'| ≤ β ^ k * M := fun k w' => by
    rw [abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hx k w') (pow_nonneg h0 k)
  rw [𝔼.E_tsum h0 h1 hb 0 w]
  refine tsum_congr fun k => ?_
  change 𝔼.E 0 (β ^ k • x k) w = _
  rw [map_smul]
  rfl

/-- Woodford (2003), p. 412: under (2.14), `E_0 ∑ βᵗx_t = x_0` (`x` adapted). -/
theorem nc_E0_tsum_x {κ β M : ℝ} (hκ : κ ≠ 0) (h0 : 0 ≤ β) (h1 : β < 1) {e0 : Ω → ℝ}
    {π x : ℕ → Ω → ℝ} (hAS : NCAS 𝔼 κ e0 π x) (hx : ∀ t w, |x t w| ≤ M)
    (hxa : 𝔼.Adapted x) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, β ^ t * x t w') w = x 0 w := by
  rw [E0_tsum_x 𝔼 h0 h1 hx w, tsum_eq_single 0 (fun t ht => by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
    rw [nc_E0_x 𝔼 hκ hAS s]; simp), pow_zero, one_mul, hxa 0]

/-- Woodford (2003), p. 412: the pathwise split of the discounted loss with a linear term,
`∑ βᵗ[A_t + λ(x_t − x*)² − λx_t²] = ∑ βᵗA_t − 2λx*∑ βᵗx_t + λx*²/(1 − β)`. -/
theorem tsum_loss_split {β lam xs : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {A x : ℕ → ℝ} (hA : Bdd A)
    (hx : Bdd x) :
    ∑' t, β ^ t * (A t + lam * (x t - xs) ^ 2) =
      ∑' t, β ^ t * (A t + lam * x t ^ 2) - 2 * lam * xs * ∑' t, β ^ t * x t +
        lam * xs ^ 2 / (1 - β) := by
  have hB : Bdd (fun t => A t + lam * x t ^ 2) := hA.add ((Bdd.const lam).mul (hx.pow 2))
  have e : ∀ t, β ^ t * (A t + lam * (x t - xs) ^ 2) =
      β ^ t * ((-(2 * lam * xs)) * x t + (A t + lam * x t ^ 2) + lam * xs ^ 2) := by
    intro t; ring
  rw [tsum_congr e, tsum_add3 h0 h1 _ hx hB (Bdd.const (lam * xs ^ 2))]
  have hg : ∑' t : ℕ, β ^ t * (lam * xs ^ 2) = lam * xs ^ 2 / (1 - β) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]; ring
  rw [hg]
  ring

/-- **Woodford (2003), eq. (3.2), p. 412 (New Classical model, any expectation system).** Under
(2.14) with `κ ≠ 0`, `λ = κ/θ`, bounded `π, x` (`x` adapted):
`E_0 ∑ βᵗL_t = −2θ⁻¹x*π_0 + E_0 ∑ βᵗ[(π_t − E_{t−1}π_t)² + λx_t²] + t.i.p.`, with
t.i.p. `= 2θ⁻¹x*E_{−1}π_0 + λx*²/(1 − β)`. -/
theorem eq32 {κ θ lam β M xs : ℝ} (hκ : κ ≠ 0) (hθ : θ ≠ 0) (hlam : lam = κ / θ) (h0 : 0 ≤ β)
    (h1 : β < 1) {e0 : Ω → ℝ} {π x : ℕ → Ω → ℝ} (hAS : NCAS 𝔼 κ e0 π x)
    (hπ : ∀ t w, |π t w| ≤ M) (hx : ∀ t w, |x t w| ≤ M) (hxa : 𝔼.Adapted x) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, β ^ t * ((π t w' - Eprev 𝔼 π e0 t w') ^ 2 +
      lam * (x t w' - xs) ^ 2)) w =
      -2 * θ⁻¹ * xs * π 0 w + 𝔼.E 0 (fun w' => ∑' t, β ^ t * ((π t w' - Eprev 𝔼 π e0 t w') ^ 2 +
        lam * x t w' ^ 2)) w + (2 * θ⁻¹ * xs * e0 w + lam * xs ^ 2 / (1 - β)) := by
  have hEb : ∀ w', Bdd (fun t => Eprev 𝔼 π e0 t w') := fun w' =>
    ⟨max |e0 w'| M, fun t => by
      cases t with
      | zero => exact le_max_left _ _
      | succ t => exact le_max_of_le_right (𝔼.abs_E_le (hπ (t + 1)) t w')⟩
  have hsplit : (fun w' => ∑' t, β ^ t * ((π t w' - Eprev 𝔼 π e0 t w') ^ 2 +
      lam * (x t w' - xs) ^ 2)) = (fun w' => ∑' t, β ^ t * ((π t w' - Eprev 𝔼 π e0 t w') ^ 2 +
        lam * x t w' ^ 2)) + (-(2 * lam * xs)) • (fun w' => ∑' t, β ^ t * x t w') +
        fun _ => lam * xs ^ 2 / (1 - β) := by
    funext w'
    have hxw : Bdd (fun t => x t w') := ⟨M, fun t => hx t w'⟩
    have hπw : Bdd (fun t => π t w') := ⟨M, fun t => hπ t w'⟩
    rw [tsum_loss_split h0 h1 ((hπw.sub (hEb w')).pow 2) hxw]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, map_add, map_add, map_smul, 𝔼.const]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [nc_E0_tsum_x 𝔼 hκ h0 h1 hAS hx hxa w]
  have h00 := congrFun (hAS 0) w
  change π 0 w = κ * x 0 w + e0 w at h00
  have hx0 : x 0 w = (π 0 w - e0 w) / κ := by field_simp; linarith
  have hl : lam / κ = θ⁻¹ := by rw [hlam]; field_simp
  rw [hx0]
  linear_combination (-2 * xs * (π 0 w - e0 w)) * hl

/-- **Woodford (2003), eq. (3.4), p. 413 (any expectation system).** For bounded `π, x` (`x`
adapted) satisfying (2.18) with `0 ≤ β < 1`: `π_0 = κE_0 ∑ βᵗx_t` (the forward solution). -/
theorem eq34 {κ β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {π x : ℕ → Ω → ℝ} (hAS : NKPC 𝔼 κ β π x)
    (hπ : ∀ t w, |π t w| ≤ M) (hx : ∀ t w, |x t w| ≤ M) (hxa : 𝔼.Adapted x) (w : Ω) :
    π 0 w = κ * 𝔼.E 0 (fun w' => ∑' t, β ^ t * x t w') w := by
  have hu : ∀ t w', |(fun t => κ • x t) t w'| ≤ |κ| * M := fun t w' => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hx t w') (abs_nonneg κ)
  have hua : 𝔼.Adapted (fun t => κ • x t) := fun t => by
    simp only [map_smul, hxa t]
  have hz : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + (fun t => κ • x t) t := fun t => by
    rw [hAS t, add_comm]
  have hfs := 𝔼.eq_forwardSeries h0 h1 hu hua hz ⟨M, hπ⟩
  rw [hfs, E0_tsum_x 𝔼 h0 h1 hx w, ← tsum_mul_left]
  change ∑' k, β ^ k * 𝔼.E 0 ((fun t => κ • x t) (0 + k)) w = _
  refine tsum_congr fun k => ?_
  simp only [zero_add, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Woodford (2003), eq. (3.5), p. 413 (any expectation system).** Under (2.18) with `κ ≠ 0`,
`λ = κ/θ`: `E_0 ∑ βᵗ[π_t² + λ(x_t − x*)²] = −2θ⁻¹x*π_0 + E_0 ∑ βᵗ[π_t² + λx_t²] + λx*²/(1 − β)`. -/
theorem eq35 {κ θ lam β M xs : ℝ} (hκ : κ ≠ 0) (hθ : θ ≠ 0) (hlam : lam = κ / θ) (h0 : 0 ≤ β)
    (h1 : β < 1) {π x : ℕ → Ω → ℝ} (hAS : NKPC 𝔼 κ β π x) (hπ : ∀ t w, |π t w| ≤ M)
    (hx : ∀ t w, |x t w| ≤ M) (hxa : 𝔼.Adapted x) (w : Ω) :
    𝔼.E 0 (fun w' => ∑' t, β ^ t * (π t w' ^ 2 + lam * (x t w' - xs) ^ 2)) w =
      -2 * θ⁻¹ * xs * π 0 w + 𝔼.E 0 (fun w' => ∑' t, β ^ t * (π t w' ^ 2 + lam * x t w' ^ 2)) w +
        lam * xs ^ 2 / (1 - β) := by
  have hsplit : (fun w' => ∑' t, β ^ t * (π t w' ^ 2 + lam * (x t w' - xs) ^ 2)) =
      (fun w' => ∑' t, β ^ t * (π t w' ^ 2 + lam * x t w' ^ 2)) +
        (-(2 * lam * xs)) • (fun w' => ∑' t, β ^ t * x t w') +
        fun _ => lam * xs ^ 2 / (1 - β) := by
    funext w'
    have hxw : Bdd (fun t => x t w') := ⟨M, fun t => hx t w'⟩
    have hπw : Bdd (fun t => π t w') := ⟨M, fun t => hπ t w'⟩
    rw [tsum_loss_split h0 h1 (hπw.pow 2) hxw]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, map_add, map_add, map_smul, 𝔼.const]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h34 := eq34 𝔼 h0 h1 hAS hπ hx hxa w
  have hX : 𝔼.E 0 (fun w' => ∑' t, β ^ t * x t w') w = π 0 w / κ := by
    rw [h34]; field_simp
  have hl : lam / κ = θ⁻¹ := by rw [hlam]; field_simp
  rw [hX]
  linear_combination (-2 * xs * π 0 w) * hl

/-- **Woodford (2003), p. 415: the steady states of (2.18) satisfy `x_ss = (1 − β)κ⁻¹π_ss`.**
Constant paths solve (2.18) iff this relation holds (`κ ≠ 0`, nonempty state space). -/
theorem xss_iff [Nonempty Ω] {κ β : ℝ} (hκ : κ ≠ 0) (πss xss : ℝ) :
    NKPC 𝔼 κ β (fun _ _ => πss) (fun _ _ => xss) ↔ xss = (1 - β) * κ⁻¹ * πss := by
  unfold NKPC
  simp only [𝔼.const]
  constructor
  · intro h
    have := congrFun (h 0) (Classical.arbitrary Ω)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    field_simp
    linarith
  · intro h t
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]
    field_simp
    ring

/-! ### Why a unit coefficient on expected inflation would make long-run inflation negative
(p. 415): an LQ steady-state calculation -/

/-- Woodford (2003), p. 415: the (deterministic) AS relation with coefficient `b` on expected
inflation, `π_t = κx_t + bπ_{t+1}` (`b = β` is (2.18); `b = 1` is the "simplified" version). -/
def ASb (κ b : ℝ) (π x : ℕ → ℝ) : Prop := ∀ t, π t = κ * x t + b * π (t + 1)

/-- Woodford (2003), p. 415 (and Ch. 7 §1): the first-order conditions of the Lagrangian
`∑ βᵗ[½(π_t² + λ(x_t − x*)²) + μ_t(π_t − κx_t − bπ_{t+1})]` for commitment from date 0
(`μ_{−1} = 0`): `π_t + μ_t − (b/β)μ_{t−1} = 0` and `λ(x_t − x*) = κμ_t`. -/
def CommitFOC (b β κ lam xs : ℝ) (π x μ : ℕ → ℝ) : Prop :=
  ∀ t, π t + μ t - b / β * lagS 0 μ t = 0 ∧ lam * (x t - xs) = κ * μ t

/-- Woodford (2003), (3.3), p. 413: the discounted loss `∑ βᵗ[π_t² + λ(x_t − x*)²]`. -/
noncomputable def Jloss (β lam xs : ℝ) (π x : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * (π t ^ 2 + lam * (x t - xs) ^ 2)

/-- Woodford (2003), p. 415: for a path satisfying the AS relation and the first-order conditions,
any other bounded feasible path has loss `J' = J + ∑ βᵗ[(π'_t − π_t)² + λ(x'_t − x_t)²]`. -/
theorem commit_gap {b β κ lam xs : ℝ} (h0 : 0 < β) (h1 : β < 1) {π x μ π' x' : ℕ → ℝ}
    (hπ : Bdd π) (hx : Bdd x) (hμ : Bdd μ) (hπ' : Bdd π') (hx' : Bdd x')
    (hAS : ASb κ b π x) (hFOC : CommitFOC b β κ lam xs π x μ) (hAS' : ASb κ b π' x') :
    Jloss β lam xs π' x' = Jloss β lam xs π x +
      ∑' t, β ^ t * ((π' t - π t) ^ 2 + lam * (x' t - x t) ^ 2) := by
  have hL : Bdd (fun t => π t ^ 2 + lam * (x t - xs) ^ 2) :=
    (hπ.pow 2).add ((Bdd.const lam).mul ((hx.sub (Bdd.const xs)).pow 2))
  have hD : Bdd (fun t => (π' t - π t) ^ 2 + lam * (x' t - x t) ^ 2) :=
    ((hπ'.sub hπ).pow 2).add ((Bdd.const lam).mul ((hx'.sub hx).pow 2))
  have hK : Bdd (fun t => 2 * (b / β * lagS 0 μ t * (π' t - π t))) :=
    (Bdd.const 2).mul (((Bdd.const _).mul (hμ.lagS 0)).mul (hπ'.sub hπ))
  have hβ : β * (b / β) = b := mul_div_cancel₀ b h0.ne'
  unfold Jloss
  rw [tsum_telescope_add h0.le h1 (hL.add hD) hK (fun t => ?_)]
  · simp only [lagS_zero, mul_zero, zero_mul, add_zero]
    rw [(hL.summable h0.le h1).tsum_add (hD.summable h0.le h1) |>.symm]
    congr 1; funext t; ring
  · obtain ⟨hf1, hf2⟩ := hFOC t
    have ha := hAS t
    have ha' := hAS' t
    simp only [lagS_succ]
    linear_combination (2 * (π' t - π t)) * hf1 + (2 * (x' t - x t)) * hf2 +
      (-2 * μ t) * (ha' - ha) + (2 * μ t * (π' (t + 1) - π (t + 1))) * hβ

/-- **Woodford (2003), p. 415 (and Ch. 7): a bounded path satisfying the AS relation and the
first-order conditions is the unique optimal commitment** among bounded feasible paths
(`λ > 0`, `0 < β < 1`). -/
theorem commit_optimal {b β κ lam xs : ℝ} (h0 : 0 < β) (h1 : β < 1) (hlam : 0 < lam)
    {π x μ : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x) (hμ : Bdd μ) (hAS : ASb κ b π x)
    (hFOC : CommitFOC b β κ lam xs π x μ) {π' x' : ℕ → ℝ} (hπ' : Bdd π') (hx' : Bdd x')
    (hAS' : ASb κ b π' x') :
    Jloss β lam xs π x ≤ Jloss β lam xs π' x' ∧
      (Jloss β lam xs π' x' = Jloss β lam xs π x → π' = π ∧ x' = x) := by
  rw [commit_gap h0 h1 hπ hx hμ hπ' hx' hAS hFOC hAS']
  have hnn : 0 ≤ ∑' t, β ^ t * ((π' t - π t) ^ 2 + lam * (x' t - x t) ^ 2) :=
    tsum_nonneg fun t => mul_nonneg (pow_nonneg h0.le t) (by positivity)
  refine ⟨by linarith, fun h => ?_⟩
  have hz : ∑' t, β ^ t * ((π' t - π t) ^ 2 + lam * (x' t - x t) ^ 2) = 0 := by linarith
  have := (zero_loss_iff h0 h1 hlam (hπ'.sub hπ) (hx'.sub hx)).mp hz
  exact ⟨funext fun t => by linarith [(this t).1], funext fun t => by linarith [(this t).2]⟩

/-- **Woodford (2003), p. 415: the long-run steady state of the optimal commitment.** If the
optimal path (AS relation and first-order conditions) converges, `π_t → π̄`, `x_t → x̄`,
`μ_t → μ̄`, then `π̄ + μ̄ − (b/β)μ̄ = 0`, `λ(x̄ − x*) = κμ̄` and `π̄ = κx̄ + bπ̄`. -/
theorem commit_limits {b β κ lam xs πbar xbar μbar : ℝ} {π x μ : ℕ → ℝ} (hAS : ASb κ b π x)
    (hFOC : CommitFOC b β κ lam xs π x μ) (hπ : Tendsto π atTop (𝓝 πbar))
    (hx : Tendsto x atTop (𝓝 xbar)) (hμ : Tendsto μ atTop (𝓝 μbar)) :
    πbar + μbar - b / β * μbar = 0 ∧ lam * (xbar - xs) = κ * μbar ∧
      πbar = κ * xbar + b * πbar := by
  have hπ1 := hπ.comp (tendsto_add_atTop_nat 1)
  have hμ1 := hμ.comp (tendsto_add_atTop_nat 1)
  refine ⟨?_, ?_, ?_⟩
  · have hlim : Tendsto (fun t => π (t + 1) + μ (t + 1) - b / β * μ t) atTop
        (𝓝 (πbar + μbar - b / β * μbar)) := (hπ1.add hμ1).sub (hμ.const_mul _)
    have hz : (fun t => π (t + 1) + μ (t + 1) - b / β * μ t) = fun _ => 0 := by
      funext t; have := (hFOC (t + 1)).1; rw [lagS_succ] at this; exact this
    rw [hz] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · have hlim : Tendsto (fun t => lam * (x t - xs) - κ * μ t) atTop
        (𝓝 (lam * (xbar - xs) - κ * μbar)) :=
      ((hx.sub tendsto_const_nhds).const_mul lam).sub (hμ.const_mul κ)
    have hz : (fun t => lam * (x t - xs) - κ * μ t) = fun _ => 0 := by
      funext t; rw [(hFOC t).2, sub_self]
    rw [hz] at hlim
    exact sub_eq_zero.mp (tendsto_nhds_unique hlim tendsto_const_nhds)
  · have hlim : Tendsto (fun t => π t - (κ * x t + b * π (t + 1))) atTop
        (𝓝 (πbar - (κ * xbar + b * πbar))) := hπ.sub ((hx.const_mul κ).add (hπ1.const_mul b))
    have hz : (fun t => π t - (κ * x t + b * π (t + 1))) = fun _ => 0 := by
      funext t; rw [← hAS t, sub_self]
    rw [hz] at hlim
    exact sub_eq_zero.mp (tendsto_nhds_unique hlim tendsto_const_nhds)

/-- **Woodford (2003), p. 415 (with (2.18), `b = β`): the optimal long-run inflation rate is
zero**, even though `x* > 0` and (2.18) has a long-run trade-off. -/
theorem longrun_inflation_zero {β κ lam xs πbar xbar μbar : ℝ} (hβ : β ≠ 0) {π x μ : ℕ → ℝ}
    (hAS : ASb κ β π x) (hFOC : CommitFOC β β κ lam xs π x μ) (hπ : Tendsto π atTop (𝓝 πbar))
    (hx : Tendsto x atTop (𝓝 xbar)) (hμ : Tendsto μ atTop (𝓝 μbar)) : πbar = 0 := by
  have h := (commit_limits hAS hFOC hπ hx hμ).1
  rw [div_self hβ] at h
  linarith

/-- **Woodford (2003), p. 415: with a coefficient of one on expected inflation the optimal
long-run inflation rate would be NEGATIVE**: `π̄ = −(1 − β)λx*/(βκ) < 0` (`x* > 0`, `λ, κ > 0`,
`0 < β < 1`), while the long-run output gap is `x̄ = 0` ("no long-run output increase"). -/
theorem longrun_inflation_negative {β κ lam xs πbar xbar μbar : ℝ} (h0 : 0 < β) (h1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) (hxs : 0 < xs) {π x μ : ℕ → ℝ} (hAS : ASb κ 1 π x)
    (hFOC : CommitFOC 1 β κ lam xs π x μ) (hπ : Tendsto π atTop (𝓝 πbar))
    (hx : Tendsto x atTop (𝓝 xbar)) (hμ : Tendsto μ atTop (𝓝 μbar)) :
    xbar = 0 ∧ πbar = -((1 - β) * lam * xs / (β * κ)) ∧ πbar < 0 := by
  obtain ⟨hf, hg, ha⟩ := commit_limits hAS hFOC hπ hx hμ
  have hxbar : xbar = 0 := by
    have : κ * xbar = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hκ.ne'
  have hμbar : μbar = -(lam * xs) / κ := by
    rw [hxbar] at hg; field_simp; linarith
  have hπbar : πbar = -((1 - β) * lam * xs / (β * κ)) := by
    rw [hμbar] at hf
    field_simp at hf ⊢
    linarith
  refine ⟨hxbar, hπbar, ?_⟩
  rw [hπbar, neg_lt_zero]
  have : 0 < 1 - β := by linarith
  positivity

end Woodford.StabilizationWelfare.PriceStability
