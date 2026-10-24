/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.RulesAdaptiveRE

/-!
# Responses to AR(1) monetary-policy disturbances

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.3.1 "Responses with
policy rules", pp. 403–405, §17.4.3 "Responses to AR(1) monetary policy disturbances",
pp. 415–416, and Online Appendix A1, §1.8 "Three-equation model solution", pp. 571–572, and
§1.13.1 "Calculating responses of the standard new-Keynesian model", pp. 586–588.

## The simple sticky-price model (17.11)

With an AR(1) disturbance `E_t u_{t+1} = η u_t`, `|η| ≤ 1`, and a determinate rule:

* (17.12): the unique bounded equilibrium is `π_t = −u_t/(φ − η + (1−η)/(σκ))`
  (`eq_17_12`), equal to the forward-series form (`eq_17_12_series`, `coeff_17_12_forms`);
* (17.13): `i_t = −(η − (1−η)/(σκ))/(φ − η + (1−η)/(σκ)) u_t` (`eq_17_13`,
  `coeff_17_13_forms`);
* the frictionless limits `κ → ∞` are (16.9) and (16.11) (`tendsto_17_12`, `tendsto_17_13`);
* `η = 1` is super-Fisherian, `π = i = −u/(φ−1)` (`superFisher_simple`); `η = 1/(1+σκ)` is the
  open-mouth case `π = −u/φ`, `i = 0` (`openMouth_simple`); and for `φ > 1` the interest rate
  moves with the disturbance iff `η < 1/(1+σκ)` (`i_coeff_pos_iff`, Figure 17.3: `fig17_3`).

## The three-equation model (17.15)–(17.17), (17.20)–(17.21)

* A1 (1.59): undetermined coefficients (`msv_solves`, `coeffs_of_msv`); (1.60)–(1.62)
  (`eq_1_59_iff`, `msv_i_eq`); for `φ > 1` the minimal-state-variable solution is the unique
  bounded equilibrium (`msv_unique`, via `threeEq_solves` and `schurStable_of_one_lt`).
* A1 §1.8: the lag-operator form `−σκ/((1+σκφ)(1−λ₁η)(1−λ₂η))` equals (1.60) (`lag_form`,
  `lag_factor`, `partial_fractions`, `lag_sum_ar1`). Survey error **E11** (confirmed): the book
  says "both roots unstable, `λ₁ < 1` and `λ₂ < 1`", but the roots can be complex
  (`lag_roots_complex_example`, `φ = 1.5, β = 0.99, σ = 1, κ = 0.5`); the correct statement is
  that both have modulus below one (`lag_roots_norm_lt_one`).
* p. 415: `η = 1` is super-Fisherian, `π = i = −u/(φ−1)`, `x = (1−β)/κ · π`
  (`superFisher_full`).
* p. 416: the open-mouth persistence `η*` is the unique root in `(0,1)` of
  `βη² − (1+β+σκ)η + 1 = 0` (`etaStar_root`, `etaStar_mem`, `eq_etaStar`); there
  `i = 0` and `π = −u/φ` (`openMouth_full`); for Figure 17.8 (`β = .95, κ = .5, σ = 1`)
  `0.508 < η* < 0.509` (`etaStar_fig17_8`); a negative disturbance lowers `i` and raises `π` iff
  `η < η*` (`full_i_coeff_pos_of_lt`, `full_i_coeff_neg_of_gt`, `fig17_8_transitory`).
* (1.60) generalises (17.12) (`β = 0`, `msv_beta_zero`) and (16.9) (`κ → ∞`, `tendsto_1_60`).
-/

namespace Cochrane.KeynesianStickyPrices.AR1Responses

open Filter Topology StaticIS RulesAdaptiveRE ForwardSolution
open SharedTools (Pmat Qmat solvedA det2_Pmat)

variable {Ω : Type*}

/-! ### The simple model: (17.12)–(17.13) -/

/-- Cochrane (2023), eq. (17.12), p. 403: the denominator `φ − η + (1−η)/(σκ)`. -/
noncomputable def den (σ κ φ η : ℝ) : ℝ := φ - η + (1 - η) / (σ * κ)

/-- Cochrane (2023), eq. (17.12), p. 403: `σκ (φ − η + (1−η)/(σκ)) = (1 + σκφ) − η(1 + σκ)`. -/
theorem den_mul {σ κ φ η : ℝ} (hσκ : σ * κ ≠ 0) :
    σ * κ * den σ κ φ η = 1 + σ * κ * φ - η * (1 + σ * κ) := by
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  unfold den; field_simp; ring

/-- Cochrane (2023), eq. (17.12), p. 403: with a determinate rule and `|η| ≤ 1` the denominator
is nonzero. -/
theorem den_ne_zero {σ κ φ η : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ))
    (hη : |η| ≤ 1) : den σ κ φ η ≠ 0 := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  intro h0
  have e := den_mul (φ := φ) (η := η) hσκ.ne'
  rw [h0, mul_zero] at e
  have e' : 1 + σ * κ * φ = η * (1 + σ * κ) := by linarith
  rw [e', abs_mul] at hc
  have : |η| * |1 + σ * κ| ≤ |1 + σ * κ| := by
    calc |η| * |1 + σ * κ| ≤ 1 * |1 + σ * κ| := mul_le_mul_of_nonneg_right hη (abs_nonneg _)
      _ = |1 + σ * κ| := one_mul _
  linarith

/-- Cochrane (2023), eq. (17.12), p. 403: for `φ > 1`, `η ≤ 1` the denominator is positive. -/
theorem den_pos {σ κ φ η : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hη : η ≤ 1) :
    0 < den σ κ φ η := by
  have e := den_mul (φ := φ) (η := η) hσκ.ne'
  have : 0 < σ * κ * den σ κ φ η := by rw [e]; nlinarith
  exact pos_of_mul_pos_right this hσκ.le

/-- Cochrane (2023), eq. (17.12), p. 403: with an AR(1) disturbance, `π_t = −u_t/den` is an
equilibrium of (17.11). -/
theorem ar1_solves (𝔼 : ExpectationSystem Ω) {σ κ φ η : ℝ} (hσκ : σ * κ ≠ 0)
    (hD : den σ κ φ η ≠ 0) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) :
    RERule 𝔼 σ κ φ u (fun t => (-1 / den σ κ φ η) • u t) := by
  refine ⟨fun t => by rw [map_smul, hu.1 t], fun t ω => ?_⟩
  rw [map_smul, hu.2 t]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e := den_mul (φ := φ) (η := η) hσκ
  field_simp
  linear_combination u t ω * e

/-- Cochrane (2023), eq. (17.12), p. 403: with an AR(1) disturbance (`|η| ≤ 1`), bounded
adapted `u` and a determinate rule, the unique bounded equilibrium of (17.11) is
`π_t = −u_t/(φ − η + (1−η)/(σκ))`. -/
theorem eq_17_12 (𝔼 : ExpectationSystem Ω) {σ κ φ η M : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) (hη : |η| ≤ 1) {u π : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hM : ∀ t ω, |u t ω| ≤ M) (hπb : BoundedProc π)
    (hπ : RERule 𝔼 σ κ φ u π) (t : ℕ) (ω : Ω) :
    π t ω = -1 / den σ κ φ η * u t ω := by
  have hD := den_ne_zero hσκ hφ hη
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  have hf : ∀ t ω, |(fun t => (-(σ * κ)) • u t) t ω| ≤ σ * κ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hσκ]
    exact mul_le_mul_of_nonneg_left (hM t ω) hσκ.le
  have hfa : 𝔼.Adapted (fun t => (-(σ * κ)) • u t) := fun t => by rw [map_smul, hu.1 t]
  obtain ⟨-, -, -, huniq⟩ := scalar_existsUnique 𝔼 hc hf hfa
  have hs := ar1_solves 𝔼 hσκ.ne' hD hu
  have hb : BoundedProc (fun t => (-1 / den σ κ φ η) • u t) := ⟨|-1 / den σ κ φ η| * M,
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have e := (huniq π ((reRule_iff_scalar 𝔼 σ κ φ u π).mp hπ).2 hπb).trans
    (huniq _ ((reRule_iff_scalar 𝔼 σ κ φ u _).mp hs).2 hb).symm
  rw [e]; rfl

/-- Cochrane (2023), eq. (17.12), p. 403: the two printed forms agree,
`σκ/((1+σκφ)(1 − η(1+σκ)/(1+σκφ))) = 1/(φ − η + (1−η)/(σκ))`. -/
theorem coeff_17_12_forms {σ κ φ η : ℝ} (hσκ : σ * κ ≠ 0) (hM : 1 + σ * κ * φ ≠ 0)
    (hD : den σ κ φ η ≠ 0) :
    σ * κ / ((1 + σ * κ * φ) * (1 - η * ((1 + σ * κ) / (1 + σ * κ * φ)))) =
      1 / den σ κ φ η := by
  have e := den_mul (φ := φ) (η := η) hσκ
  have h2 : (1 + σ * κ * φ) * (1 - η * ((1 + σ * κ) / (1 + σ * κ * φ))) =
      σ * κ * den σ κ φ η := by rw [e]; field_simp
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  rw [h2]; field_simp

/-- Cochrane (2023), p. 403 and eq. (17.12): the forward series evaluated at an AR(1)
disturbance, `−σκ/(1+σκφ) ∑ ((1+σκ)/(1+σκφ))ʲ E_t u_{t+j} = −u_t/den`. -/
theorem eq_17_12_series (𝔼 : ExpectationSystem Ω) {σ κ φ η : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) (hη : |η| ≤ 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (t : ℕ) (ω : Ω) :
    -(σ * κ) / (1 + σ * κ * φ) *
      ∑' j, ((1 + σ * κ) / (1 + σ * κ * φ)) ^ j * 𝔼.E t (u (t + j)) ω =
      -1 / den σ κ φ η * u t ω := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  have hM : 1 + σ * κ * φ ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith [abs_nonneg (1 + σ * κ)]
  have hD := den_ne_zero hσκ hφ hη
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  have hcη : |c * η| < 1 := by
    rw [abs_mul]
    have hc1 : |c| < 1 := by
      rw [abs_div, div_lt_one (abs_pos.mpr hM)]; exact hc
    calc |c| * |η| ≤ |c| * 1 := mul_le_mul_of_nonneg_left hη (abs_nonneg c)
      _ < 1 := by rw [mul_one]; exact hc1
  have hterm : ∀ j : ℕ, c ^ j * 𝔼.E t (u (t + j)) ω = u t ω * (c * η) ^ j := fun j => by
    rw [𝔼.ar1_iterate hu t j, Pi.smul_apply, smul_eq_mul, mul_pow]; ring
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hcη]
  have h1 : 1 - c * η ≠ 0 := by
    intro h0
    have : c * η = 1 := by linarith
    rw [this, abs_one] at hcη; exact lt_irrefl _ hcη
  have hf := coeff_17_12_forms hσκ.ne' hM hD
  rw [mul_comm η c] at hf
  have e2 : -(σ * κ) / (1 + σ * κ * φ) * (u t ω * (1 - c * η)⁻¹) =
      -(σ * κ / ((1 + σ * κ * φ) * (1 - c * η))) * u t ω := by
    field_simp
  rw [e2, hf]
  ring

/-- Cochrane (2023), eq. (17.13), p. 404: the two printed forms of the interest-rate
coefficient agree, `1 − φ/den = −(η − (1−η)/(σκ))/den`. -/
theorem coeff_17_13_forms {σ κ φ η : ℝ} (hD : den σ κ φ η ≠ 0) :
    1 - φ / den σ κ φ η = -(η - (1 - η) / (σ * κ)) / den σ κ φ η := by
  rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
  unfold den; ring

/-- Cochrane (2023), eq. (17.13), p. 404: in the equilibrium of (17.12) the interest rate is
`i_t = φ π_t + u_t = −(η − (1−η)/(σκ))/den · u_t`. -/
theorem eq_17_13 {σ κ φ η : ℝ} (hD : den σ κ φ η ≠ 0) (u : ℝ) :
    φ * (-1 / den σ κ φ η * u) + u = -(η - (1 - η) / (σ * κ)) / den σ κ φ η * u := by
  rw [← coeff_17_13_forms hD]; field_simp; ring

/-- Cochrane (2023), p. 404, "The frictionless limit `κ → ∞` reduces to the frictionless AR(1)
responses": `−1/den → −1/(φ − η)`, which is (16.9). -/
theorem tendsto_17_12 {σ φ η : ℝ} (hσ : 0 < σ) (hφη : φ - η ≠ 0) :
    Tendsto (fun κ : ℝ => -1 / den σ κ φ η) atTop (𝓝 (-1 / (φ - η))) := by
  have h1 : Tendsto (fun κ : ℝ => σ * κ) atTop atTop := Tendsto.const_mul_atTop hσ tendsto_id
  have h2 : Tendsto (fun κ : ℝ => (1 - η) / (σ * κ)) atTop (𝓝 0) :=
    h1.const_div_atTop (1 - η)
  have h3 : Tendsto (fun κ : ℝ => den σ κ φ η) atTop (𝓝 (φ - η)) := by
    simpa [den] using h2.const_add (φ - η)
  exact tendsto_const_nhds.div h3 hφη

/-- Cochrane (2023), p. 404: the frictionless limit of (17.13) is (16.11),
`i_t = −η/(φ − η) u_t`. -/
theorem tendsto_17_13 {σ φ η : ℝ} (hσ : 0 < σ) (hφη : φ - η ≠ 0) :
    Tendsto (fun κ : ℝ => -(η - (1 - η) / (σ * κ)) / den σ κ φ η) atTop
      (𝓝 (-η / (φ - η))) := by
  have h1 : Tendsto (fun κ : ℝ => σ * κ) atTop atTop := Tendsto.const_mul_atTop hσ tendsto_id
  have h2 : Tendsto (fun κ : ℝ => (1 - η) / (σ * κ)) atTop (𝓝 0) :=
    h1.const_div_atTop (1 - η)
  have h3 : Tendsto (fun κ : ℝ => den σ κ φ η) atTop (𝓝 (φ - η)) := by
    simpa [den] using h2.const_add (φ - η)
  have h4 : Tendsto (fun κ : ℝ => -(η - (1 - η) / (σ * κ))) atTop (𝓝 (-η)) := by
    simpa using (h2.const_sub η).neg
  exact h4.div h3 hφη

/-- Cochrane (2023), p. 404, "a persistent shock `η = 1` produces a super-Fisherian result":
`π_t = i_t = −u_t/(φ − 1)`. -/
theorem superFisher_simple (σ κ φ : ℝ) :
    -1 / den σ κ φ 1 = -1 / (φ - 1) ∧ -(1 - (1 - 1) / (σ * κ)) / den σ κ φ 1 = -1 / (φ - 1) := by
  unfold den; constructor <;> norm_num

/-- Cochrane (2023), p. 405, the open-mouth case: for `η = 1/(1+σκ)`, (17.12)–(17.13) give
`π_t = −u_t/φ` and `i_t = 0`. -/
theorem openMouth_simple {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    -1 / den σ κ φ (1 / (1 + σ * κ)) = -1 / φ ∧
      -(1 / (1 + σ * κ) - (1 - 1 / (1 + σ * κ)) / (σ * κ)) / den σ κ φ (1 / (1 + σ * κ)) =
        0 := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have hσ := left_ne_zero_of_mul hσκ.ne'
  have hκ := right_ne_zero_of_mul hσκ.ne'
  have h2 : 1 / (1 + σ * κ) - (1 - 1 / (1 + σ * κ)) / (σ * κ) = 0 := by
    field_simp; ring
  have h3 : den σ κ φ (1 / (1 + σ * κ)) = φ := by
    unfold den; linear_combination (-1 : ℝ) * h2
  rw [h2, h3]; simp

/-- Cochrane (2023), p. 405: the sign of the interest-rate response. For `s = σκ > 0`,
`η − (1−η)/s > 0` iff `η > 1/(1+s)`. -/
theorem num_pos_iff {s η : ℝ} (hs : 0 < s) : 0 < η - (1 - η) / s ↔ 1 / (1 + s) < η := by
  rw [sub_pos, div_lt_iff₀ hs, div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 405, "the actual interest rate goes in the direction of the disturbance,
and inflation goes in the opposite direction … only … for sufficiently transitory shocks": for
`φ > 1` and `η ≤ 1`, inflation always moves opposite to `u`, and the interest rate moves with
`u` iff `η < 1/(1+σκ)`. -/
theorem i_coeff_pos_iff {σ κ φ η : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) (hη : η ≤ 1) :
    -1 / den σ κ φ η < 0 ∧
      (0 < -(η - (1 - η) / (σ * κ)) / den σ κ φ η ↔ η < 1 / (1 + σ * κ)) := by
  have hD := den_pos hσκ hφ hη
  refine ⟨div_neg_of_neg_of_pos (by norm_num) hD, ?_⟩
  rw [div_pos_iff_of_pos_right hD, neg_pos, sub_neg, lt_div_iff₀ hσκ,
    lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + σ * κ)]
  constructor <;> intro h <;> nlinarith

/-- Cochrane (2023), Figure 17.3, p. 404 (`σ = 1`, `κ = 1/2`, any `φ > 1`): `1/(1+σκ) = 2/3`;
at `η = 0.3` the rate moves with the disturbance, at `η = 0.9` against it (Fisherian), and at
`η = 2/3` not at all. -/
theorem fig17_3 {φ : ℝ} (hφ : 1 < φ) :
    (1 : ℝ) / (1 + 1 * (1 / 2)) = 2 / 3 ∧
      0 < -((0.3 : ℝ) - (1 - 0.3) / (1 * (1 / 2))) / den 1 (1 / 2) φ 0.3 ∧
      -((0.9 : ℝ) - (1 - 0.9) / (1 * (1 / 2))) / den 1 (1 / 2) φ 0.9 < 0 ∧
      -((2 / 3 : ℝ) - (1 - 2 / 3) / (1 * (1 / 2))) / den 1 (1 / 2) φ (2 / 3) = 0 := by
  refine ⟨by norm_num, ?_, ?_, by norm_num⟩
  · exact div_pos (by norm_num) (den_pos (by norm_num) hφ (by norm_num))
  · exact div_neg_of_neg_of_pos (by norm_num) (den_pos (by norm_num) hφ (by norm_num))

/-! ### The three-equation model: A1 §1.13.1, (1.59)–(1.62) -/

/-- Cochrane (2023), eqs. (17.15)–(17.17), (17.20) and A1 §1.8, p. 571: the three-equation
model with the rule substituted, `x_t = E_t x_{t+1} − σ(φπ_t + u_t − E_t π_{t+1})`,
`π_t = β E_t π_{t+1} + κ x_t` (so `i_t = φπ_t + u_t`), with `x`, `π` adapted. -/
def ThreeEq (𝔼 : ExpectationSystem Ω) (σ κ β φ : ℝ) (u x π : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted x ∧ 𝔼.Adapted π ∧ ∀ t ω,
    x t ω = 𝔼.E t (x (t + 1)) ω - σ * (φ * π t ω + u t ω - 𝔼.E t (π (t + 1)) ω) ∧
    π t ω = β * 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), A1 eq. (1.60), p. 588: the denominator
`φ − η + (1 − βη)(1 − η)/(σκ)`. -/
noncomputable def denF (σ κ β φ η : ℝ) : ℝ := φ - η + (1 - β * η) * (1 - η) / (σ * κ)

/-- Cochrane (2023), A1 eq. (1.60), p. 588:
`σκ · denF = βη² − (1 + β + σκ)η + 1 + σκφ`. -/
theorem denF_mul {σ κ β φ η : ℝ} (hσκ : σ * κ ≠ 0) :
    σ * κ * denF σ κ β φ η = β * η ^ 2 - (1 + β + σ * κ) * η + 1 + σ * κ * φ := by
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  unfold denF; field_simp; ring

/-- Cochrane (2023), A1 eq. (1.60), p. 588: for `φ > 1`, `0 ≤ β ≤ 1` and `η ≤ 1` the
denominator is positive. -/
theorem denF_pos {σ κ β φ η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hφ : 1 < φ)
    (hη : η ≤ 1) : 0 < denF σ κ β φ η := by
  have e := denF_mul (β := β) (φ := φ) (η := η) hσκ.ne'
  have key : β * η ^ 2 - (1 + β + σ * κ) * η + 1 + σ * κ * φ =
      σ * κ * (φ - 1) + (η - 1) * (β * η - 1 - σ * κ) := by ring
  have h2 : 0 ≤ (η - 1) * (β * η - 1 - σ * κ) := by
    apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
    nlinarith
  have : 0 < σ * κ * denF σ κ β φ η := by rw [e, key]; nlinarith
  exact pos_of_mul_pos_right this hσκ.le

/-- Cochrane (2023), A1 eq. (1.59), p. 588: undetermined coefficients. If `u` is AR(1) and
`(απ, αx)` solve (1.59), then `π_t = απ u_t`, `x_t = αx u_t` solve the three-equation
model. -/
theorem msv_solves (𝔼 : ExpectationSystem Ω) {σ κ β φ η aπ ax : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (h1 : (1 - η) * ax = -σ * (1 + (φ - η) * aπ))
    (h2 : (1 - β * η) * aπ = κ * ax) :
    ThreeEq 𝔼 σ κ β φ u (fun t => ax • u t) (fun t => aπ • u t) := by
  refine ⟨fun t => by rw [map_smul, hu.1 t], fun t => by rw [map_smul, hu.1 t],
    fun t ω => ⟨?_, ?_⟩⟩ <;>
  · simp only [map_smul, hu.2 t, Pi.smul_apply, smul_eq_mul]
    first
    | linear_combination u t ω * h1
    | linear_combination u t ω * h2

/-- Cochrane (2023), A1 p. 588, "Since these equations must hold for any `u_{i,t}`, conclude"
(1.59): if the guess solves the model and the disturbance is nonzero somewhere, the
coefficients satisfy (1.59). -/
theorem coeffs_of_msv (𝔼 : ExpectationSystem Ω) {σ κ β φ η aπ ax : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (h : ThreeEq 𝔼 σ κ β φ u (fun t => ax • u t) (fun t => aπ • u t))
    {t : ℕ} {ω : Ω} (hne : u t ω ≠ 0) :
    (1 - η) * ax = -σ * (1 + (φ - η) * aπ) ∧ (1 - β * η) * aπ = κ * ax := by
  obtain ⟨e1, e2⟩ := h.2.2 t ω
  simp only [map_smul, hu.2 t, Pi.smul_apply, smul_eq_mul] at e1 e2
  constructor
  · apply mul_right_cancel₀ hne; linear_combination e1
  · apply mul_right_cancel₀ hne; linear_combination e2

/-- Cochrane (2023), A1 eqs. (1.59)–(1.61), p. 588: (1.59) holds iff
`απ = −1/(φ − η + (1−βη)(1−η)/(σκ))` (1.60) and `αx = (1 − βη)/κ · απ` (1.61). -/
theorem eq_1_59_iff {σ κ β φ η aπ ax : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hD : denF σ κ β φ η ≠ 0) :
    ((1 - η) * ax = -σ * (1 + (φ - η) * aπ) ∧ (1 - β * η) * aπ = κ * ax) ↔
      (aπ = -1 / denF σ κ β φ η ∧ ax = (1 - β * η) / κ * aπ) := by
  have e := denF_mul (β := β) (φ := φ) (η := η) (mul_ne_zero hσ hκ)
  constructor
  · rintro ⟨h1, h2⟩
    have hax : ax = (1 - β * η) / κ * aπ := by field_simp; linear_combination -h2
    refine ⟨?_, hax⟩
    rw [hax] at h1
    rw [eq_div_iff hD]
    have h3 : σ * κ * (aπ * denF σ κ β φ η) = σ * κ * (-1) := by
      rw [← mul_assoc, mul_comm (σ * κ) aπ, mul_assoc, e]
      field_simp at h1
      linear_combination h1
    exact mul_left_cancel₀ (mul_ne_zero hσ hκ) h3
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by rw [h2]; field_simp⟩
    rw [h2, h1]
    field_simp
    linear_combination e

/-- Cochrane (2023), A1 eq. (1.62), p. 588: with (1.60), the interest rate
`i_t = φ π_t + u_t` equals `(η − (1−βη)(1−η)/(σκ)) π_t`. -/
theorem msv_i_eq {σ κ β φ η : ℝ} (hD : denF σ κ β φ η ≠ 0) (u : ℝ) :
    φ * (-1 / denF σ κ β φ η * u) + u =
      (η - (1 - β * η) * (1 - η) / (σ * κ)) * (-1 / denF σ κ β φ η * u) := by
  field_simp
  unfold denF
  ring

/-- Cochrane (2023), A1 eq. (1.55), p. 586, and p. 420: the transition matrix of the
forward-looking form `(x_t, π_t) = A E_t(x_{t+1}, π_{t+1}) + w_t` of the three-equation model,
`A = P⁻¹Q` with the structural matrices `P`, `Q` of (17.29)–(17.32) at `φ_x = 0` (the same
matrices as the determinacy analysis, `SharedTools.Pmat`, `SharedTools.Qmat`). -/
noncomputable def transA (σ κ β φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  solvedA (Pmat σ κ φ 0) (Qmat σ β)

/-- Cochrane (2023), A1 eq. (1.55), p. 586: the entries of the transition matrix,
`A = (1 + σκφ)⁻¹ [[1, σ(1 − φβ)], [κ, β + σκ]]`. -/
theorem transA_explicit (σ κ β φ : ℝ) :
    transA σ κ β φ = !![1 / (1 + σ * κ * φ), σ * (1 - φ * β) / (1 + σ * κ * φ);
      κ / (1 + σ * κ * φ), (β + σ * κ) / (1 + σ * κ * φ)] := by
  have hD : det2 (Pmat σ κ φ 0) = 1 + σ * κ * φ := by rw [det2_Pmat]; ring
  unfold transA solvedA
  rw [hD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pmat, Qmat] <;> ring

/-- Cochrane (2023), A1 §1.8 and (1.55), pp. 571, 586: every solution of the three-equation
model solves the vector system `X_t = A E_t X_{t+1} + w_t` with `X = (x, π)`. -/
theorem threeEq_solves (𝔼 : ExpectationSystem Ω) {σ κ β φ : ℝ} (hM : 1 + σ * κ * φ ≠ 0)
    {u x π : ℕ → Ω → ℝ} (h : ThreeEq 𝔼 σ κ β φ u x π) :
    𝔼.Solves (transA σ κ β φ)
      (fun t => ![(-σ / (1 + σ * κ * φ)) • u t, (-(σ * κ) / (1 + σ * κ * φ)) • u t])
      (fun t => ![x t, π t]) := by
  intro t j
  funext ω
  obtain ⟨e1, e2⟩ := h.2.2 t ω
  have g0 : x t ω = 1 / (1 + σ * κ * φ) * 𝔼.E t (x (t + 1)) ω +
      σ * (1 - φ * β) / (1 + σ * κ * φ) * 𝔼.E t (π (t + 1)) ω +
      -σ / (1 + σ * κ * φ) * u t ω := by
    field_simp
    linear_combination e1 - σ * φ * e2
  have g1 : π t ω = κ / (1 + σ * κ * φ) * 𝔼.E t (x (t + 1)) ω +
      (β + σ * κ) / (1 + σ * κ * φ) * 𝔼.E t (π (t + 1)) ω +
      -(σ * κ) / (1 + σ * κ * φ) * u t ω := by
    have k1 : π t ω * (1 + σ * κ * φ) = κ * 𝔼.E t (x (t + 1)) ω +
        (β + σ * κ) * 𝔼.E t (π (t + 1)) ω + -(σ * κ) * u t ω := by
      linear_combination e2 + κ * e1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      ← add_div, eq_div_iff hM]
    linear_combination k1
  fin_cases j <;> simp [transA_explicit]
  · linear_combination g0
  · linear_combination g1

/-- Cochrane (2023), A1 p. 587: for `φ > 1` (and `0 < β < 1`, `σκ > 0`) the transition matrix
satisfies the Schur–Cohn condition (both eigenvalues of `A` inside the unit circle, i.e. both
eigenvalues of the matrix of (1.55) outside it). -/
theorem schurStable_of_one_lt {σ κ β φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) : SchurStable (tr2 (transA σ κ β φ)) (det2 (transA σ κ β φ)) := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  have htr : tr2 (transA σ κ β φ) = (1 + β + σ * κ) / (1 + σ * κ * φ) := by
    simp [tr2, transA_explicit]; field_simp; ring
  have hdet : det2 (transA σ κ β φ) = β / (1 + σ * κ * φ) := by
    simp [det2, transA_explicit]; field_simp; ring
  rw [htr, hdet]
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos (by positivity), div_lt_one hM]; nlinarith
  · rw [abs_of_pos (by positivity), div_lt_iff₀ hM, add_mul, div_mul_cancel₀ _ hM.ne']
    nlinarith

/-- Cochrane (2023), A1 pp. 587–588 and p. 415: for `φ > 1` the minimal-state-variable solution
`π_t = −u_t/denF`, `x_t = (1−βη)/κ · π_t` is the unique bounded equilibrium of the
three-equation model with a bounded AR(1) disturbance (`|η| ≤ 1`). -/
theorem msv_unique (𝔼 : ExpectationSystem Ω) {σ κ β φ η M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φ) (hη : |η| ≤ 1) {u x π : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hM : ∀ t ω, |u t ω| ≤ M) (h : ThreeEq 𝔼 σ κ β φ u x π)
    (hxb : BoundedProc x) (hπb : BoundedProc π) :
    π = (fun t => (-1 / denF σ κ β φ η) • u t) ∧
      x = (fun t => ((1 - β * η) / κ * (-1 / denF σ κ β φ η)) • u t) := by
  have hσκ : 0 < σ * κ := mul_pos hσ hκ
  have hD := (denF_pos hσκ hβ0.le hβ1.le hφ (abs_le.mp hη).2).ne'
  have hMM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  obtain ⟨h1, h2⟩ := (eq_1_59_iff hσ.ne' hκ.ne' hD).mpr ⟨rfl, rfl⟩
  have hs := msv_solves 𝔼 hu h1 h2
  have hS := schurStable_of_one_lt hσκ hβ0 hβ1 hφ
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπ, hMπ⟩ := hπb
  set aπ := -1 / denF σ κ β φ η
  set ax := (1 - β * η) / κ * aπ
  have e := 𝔼.system_unique hS (threeEq_solves 𝔼 hMM h) (threeEq_solves 𝔼 hMM hs)
    (fun t j => by fin_cases j <;> simp [h.1 t, h.2.1 t])
    (fun t j => by fin_cases j <;> simp [hs.1 t, hs.2.1 t])
    ⟨max Mx Mπ, fun t j ω => by
      fin_cases j
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMπ t ω).trans (le_max_right _ _)⟩
    ⟨max (|ax| * M) (|aπ| * M), fun t j ω => by
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_left _ _)
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
          smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_right _ _)⟩
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · simpa using congrFun (congrFun e t) 1
  · simpa using congrFun (congrFun e t) 0

/-- Cochrane (2023), p. 415, the super-Fisherian full model: for `η = 1`,
`π = −u/(φ−1)`, `x = −(1−β)/κ · u/(φ−1)` and `i = −u/(φ−1)`. -/
theorem superFisher_full (σ κ β φ : ℝ) :
    -1 / denF σ κ β φ 1 = -1 / (φ - 1) ∧
      (1 - β * 1) / κ * (-1 / denF σ κ β φ 1) = -((1 - β) / κ) * (1 / (φ - 1)) ∧
      (1 - (1 - β * 1) * (1 - 1) / (σ * κ)) * (-1 / denF σ κ β φ 1) = -1 / (φ - 1) := by
  unfold denF
  refine ⟨by norm_num, by ring, by norm_num⟩

/-- Cochrane (2023), p. 415: in the super-Fisherian case a negative disturbance raises the
interest rate and (with `β < 1`) output, "because the `φπ_t` term … wins". -/
theorem superFisher_full_signs {κ β φ u : ℝ} (hκ : 0 < κ) (hβ : β < 1) (hφ : 1 < φ)
    (hu : u < 0) : 0 < -1 / (φ - 1) * u ∧ 0 < -((1 - β) / κ) * (1 / (φ - 1)) * u := by
  have h1 : 0 < φ - 1 := by linarith
  have h2 : 0 < (1 - β) / κ := div_pos (by linarith) hκ
  constructor
  · rw [neg_div]; nlinarith [div_pos one_pos h1]
  · have : 0 < (1 - β) / κ * (1 / (φ - 1)) := mul_pos h2 (div_pos one_pos h1)
    nlinarith

/-- Cochrane (2023), A1 p. 588: (1.60) generalises the simple model (17.12): at `β = 0` the
denominators coincide. -/
theorem msv_beta_zero (σ κ φ η : ℝ) : denF σ κ 0 φ η = den σ κ φ η := by
  unfold denF den; ring

/-- Cochrane (2023), A1 p. 588: (1.60) generalises the frictionless model (16.9): as `κ → ∞`,
`−1/denF → −1/(φ − η)`. -/
theorem tendsto_1_60 {σ β φ η : ℝ} (hσ : 0 < σ) (hφη : φ - η ≠ 0) :
    Tendsto (fun κ : ℝ => -1 / denF σ κ β φ η) atTop (𝓝 (-1 / (φ - η))) := by
  have h1 : Tendsto (fun κ : ℝ => σ * κ) atTop atTop := Tendsto.const_mul_atTop hσ tendsto_id
  have h2 : Tendsto (fun κ : ℝ => (1 - β * η) * (1 - η) / (σ * κ)) atTop (𝓝 0) :=
    h1.const_div_atTop _
  have h3 : Tendsto (fun κ : ℝ => denF σ κ β φ η) atTop (𝓝 (φ - η)) := by
    simpa [denF] using h2.const_add (φ - η)
  exact tendsto_const_nhds.div h3 hφη

/-! ### A1 §1.8: the lag-operator form -/

/-- Cochrane (2023), A1 §1.8, p. 572: the lag polynomial
`1 − (1+β+σκ)/(1+σκφ) z + β/(1+σκφ) z²` evaluated at `η` equals `σκ · denF/(1+σκφ)`, so the
lag-operator solution `−σκ/((1+σκφ)(1−λ₁η)(1−λ₂η)) u` is (1.60). -/
theorem lag_form {σ κ β φ η : ℝ} (hσκ : σ * κ ≠ 0) (hM : 1 + σ * κ * φ ≠ 0)
    (hD : denF σ κ β φ η ≠ 0) :
    -(σ * κ) / ((1 + σ * κ * φ) * (1 - (1 + β + σ * κ) / (1 + σ * κ * φ) * η +
      β / (1 + σ * κ * φ) * η ^ 2)) = -1 / denF σ κ β φ η := by
  have e := denF_mul (β := β) (φ := φ) (η := η) hσκ
  have h2 : (1 + σ * κ * φ) * (1 - (1 + β + σ * κ) / (1 + σ * κ * φ) * η +
      β / (1 + σ * κ * φ) * η ^ 2) = σ * κ * denF σ κ β φ η := by
    rw [e]; field_simp; ring
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  rw [h2]; field_simp

/-- Cochrane (2023), A1 §1.8, p. 572: factoring the lag polynomial with the roots of
`z² − T z + D` (`T = (1+β+σκ)/(1+σκφ)`, `D = β/(1+σκφ)`), complex in general:
`(1 − λ₁η)(1 − λ₂η) = 1 − Tη + Dη²`. -/
theorem lag_factor (T D : ℝ) (η : ℂ) :
    (1 - root₁ T D * η) * (1 - root₂ T D * η) = 1 - T * η + D * η ^ 2 := by
  rw [← root_sum T D, ← root_prod T D]; ring

/-- Cochrane (2023), A1 §1.8, p. 572: the partial-fraction step,
`(1/(λ₁−λ₂))(−λ₁/(1−λ₁η) + λ₂/(1−λ₂η)) = −1/((1−λ₁η)(1−λ₂η))`, in any field. -/
theorem partial_fractions {K : Type*} [Field K] {l1 l2 η : K} (h12 : l1 - l2 ≠ 0)
    (h1 : 1 - l1 * η ≠ 0) (h2 : 1 - l2 * η ≠ 0) :
    1 / (l1 - l2) * (-l1 / (1 - l1 * η) + l2 / (1 - l2 * η)) =
      -1 / ((1 - l1 * η) * (1 - l2 * η)) := by
  field_simp
  ring

/-- Cochrane (2023), A1 §1.8, p. 572: the forward sums at an AR(1) disturbance,
`∑ λʲ ηʲ = 1/(1 − λη)` for `‖λη‖ < 1` (complex `λ`). -/
theorem lag_sum_ar1 {l η : ℂ} (h : ‖l * η‖ < 1) :
    HasSum (fun j : ℕ => l ^ j * η ^ j) (1 - l * η)⁻¹ := by
  simpa [mul_pow] using hasSum_geometric_of_norm_lt_one h

/-- Cochrane (2023), A1 §1.8, p. 572 (survey error E11, corrected): for `φ > 1` both lag roots
`λ₁, λ₂` (roots of `z² − Tz + D`) have modulus strictly below one, so both are solved
forward. -/
theorem lag_roots_norm_lt_one {σ κ β φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) :
    ‖root₁ ((1 + β + σ * κ) / (1 + σ * κ * φ)) (β / (1 + σ * κ * φ))‖ < 1 ∧
      ‖root₂ ((1 + β + σ * κ) / (1 + σ * κ * φ)) (β / (1 + σ * κ * φ))‖ < 1 := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  rw [← schurStable_iff_roots]
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos (by positivity), div_lt_one hM]; nlinarith
  · rw [abs_of_pos (by positivity), div_lt_iff₀ hM, add_mul, div_mul_cancel₀ _ hM.ne']
    nlinarith

/-- Cochrane (2023), A1 §1.8, p. 572, survey error E11: the printed "both roots unstable,
`λ₁ < 1` and `λ₂ < 1`" treats the roots as real, but they can be complex: with `φ = 1.5`,
`β = 0.99`, `σ = 1`, `κ = 0.5` the discriminant is negative and `λ₁` has nonzero imaginary
part. -/
theorem lag_roots_complex_example :
    discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5)) (0.99 / (1 + 1 * 0.5 * 1.5)) < 0 ∧
      (root₁ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5)) (0.99 / (1 + 1 * 0.5 * 1.5))).im ≠
        0 := by
  have hd : discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5) : ℝ)
      (0.99 / (1 + 1 * 0.5 * 1.5)) < 0 := by
    unfold discQ; norm_num
  refine ⟨hd, ?_⟩
  have hn : ¬ (0 ≤ discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5) : ℝ)
      (0.99 / (1 + 1 * 0.5 * 1.5))) := not_le.mpr hd
  unfold root₁
  simp only [hn, ↓reduceIte]
  have : 0 < Real.sqrt (-discQ ((1 + 0.99 + 1 * 0.5) / (1 + 1 * 0.5 * 1.5) : ℝ)
      (0.99 / (1 + 1 * 0.5 * 1.5))) := Real.sqrt_pos.mpr (by linarith)
  simp only [ne_eq]
  positivity

/-! ### The open-mouth persistence `η*` (p. 416) -/

/-- Cochrane (2023), p. 416: the open-mouth condition `η − (1−βη)(1−η)/(σκ) = 0` is
`βη² − (1 + β + σκ)η + 1 = 0`. -/
theorem openMouth_iff_quadratic {σ κ β η : ℝ} (hσκ : σ * κ ≠ 0) :
    η - (1 - β * η) * (1 - η) / (σ * κ) = 0 ↔ β * η ^ 2 - (1 + β + σ * κ) * η + 1 = 0 := by
  rw [sub_eq_zero, eq_div_iff hσκ]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 416: the smaller root of `βη² − (1 + β + σκ)η + 1 = 0`. -/
noncomputable def etaStar (σ κ β : ℝ) : ℝ :=
  ((1 + β + σ * κ) - Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / (2 * β)

/-- Cochrane (2023), p. 416: `η*` is a root of `βη² − (1 + β + σκ)η + 1`. -/
theorem etaStar_root {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    β * etaStar σ κ β ^ 2 - (1 + β + σ * κ) * etaStar σ κ β + 1 = 0 := by
  have hdisc : 0 ≤ (1 + β + σ * κ) ^ 2 - 4 * β := by nlinarith
  have hs := Real.sq_sqrt hdisc
  unfold etaStar
  set r := Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)
  field_simp
  linear_combination hs

/-- Cochrane (2023), p. 416: `0 < η* < 1`. -/
theorem etaStar_mem {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < etaStar σ κ β ∧ etaStar σ κ β < 1 := by
  set S := 1 + β + σ * κ
  have hdisc : 0 ≤ S ^ 2 - 4 * β := by nlinarith
  set r := Real.sqrt (S ^ 2 - 4 * β)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs : r ^ 2 = S ^ 2 - 4 * β := Real.sq_sqrt hdisc
  have hS : 0 < S := by positivity
  have hrS : r < S := by nlinarith
  have hr2 : S - 2 * β < r := by nlinarith
  unfold etaStar
  constructor
  · exact div_pos (by linarith) (by positivity)
  · rw [div_lt_one (by positivity)]; linarith

/-- Cochrane (2023), p. 416: the factorisation used for uniqueness and signs,
`f(a) − f(b) = (a − b)(β(a + b) − (1 + β + σκ))` for `f(η) = βη² − (1+β+σκ)η + 1`. -/
theorem quad_sub (σ κ β a b : ℝ) :
    (β * a ^ 2 - (1 + β + σ * κ) * a + 1) - (β * b ^ 2 - (1 + β + σ * κ) * b + 1) =
      (a - b) * (β * (a + b) - (1 + β + σ * κ)) := by ring

/-- Cochrane (2023), p. 416: `η*` is the only root of the open-mouth condition with `η ≤ 1`
(in particular the only one in `(0, 1)`). -/
theorem eq_etaStar {σ κ β η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hη : η ≤ 1)
    (h : β * η ^ 2 - (1 + β + σ * κ) * η + 1 = 0) : η = etaStar σ κ β := by
  have h0 := etaStar_root hσκ hβ0 hβ1
  obtain ⟨-, h1⟩ := etaStar_mem hσκ hβ0 hβ1
  have e := quad_sub σ κ β η (etaStar σ κ β)
  rw [h, h0, sub_zero] at e
  have hneg : β * (η + etaStar σ κ β) - (1 + β + σ * κ) < 0 := by nlinarith
  have := mul_eq_zero.mp e.symm
  rcases this with h2 | h2
  · linarith
  · linarith

/-- Cochrane (2023), p. 416, open mouth in the full model: at `η = η*` the interest rate does
not move, `i = 0`, and `π = −u/φ`. -/
theorem openMouth_full {σ κ β φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    denF σ κ β φ (etaStar σ κ β) = φ ∧
      etaStar σ κ β - (1 - β * etaStar σ κ β) * (1 - etaStar σ κ β) / (σ * κ) = 0 := by
  have h0 := (openMouth_iff_quadratic hσκ.ne').mpr (etaStar_root hσκ hβ0 hβ1)
  refine ⟨?_, h0⟩
  unfold denF
  linear_combination (-1 : ℝ) * h0

/-- Cochrane (2023), p. 416 and Figure 17.8 (`β = 0.95`, `κ = 1/2`, `σ = 1`): the open-mouth
persistence is `η* ≈ 0.51`; precisely `0.508 < η* < 0.509`. -/
theorem etaStar_fig17_8 : (0.508 : ℝ) < etaStar 1 (1 / 2) 0.95 ∧
    etaStar 1 (1 / 2) 0.95 < 0.509 := by
  have hr := etaStar_root (σ := 1) (κ := 1 / 2) (β := 0.95) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨h0, h1⟩ := etaStar_mem (σ := 1) (κ := 1 / 2) (β := 0.95) (by norm_num) (by norm_num)
    (by norm_num)
  set e := etaStar 1 (1 / 2) 0.95
  constructor
  · by_contra hc
    push Not at hc
    have := quad_sub 1 (1 / 2) 0.95 e 0.508
    nlinarith
  · by_contra hc
    push Not at hc
    have := quad_sub 1 (1 / 2) 0.95 e 0.509
    nlinarith

/-- Cochrane (2023), p. 416, "for more transitory `η`, … a negative `u_{i,t}` shock lowers
interest rates `i_t` and raises inflation": for `φ > 1` and `η < η*`, the interest-rate
coefficient `(η − (1−βη)(1−η)/(σκ))·(−1/denF)` is positive and the inflation coefficient
negative. -/
theorem full_i_coeff_pos_of_lt {σ κ β φ η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) (hη : η < etaStar σ κ β) :
    -1 / denF σ κ β φ η < 0 ∧
      0 < (η - (1 - β * η) * (1 - η) / (σ * κ)) * (-1 / denF σ κ β φ η) := by
  obtain ⟨-, h1⟩ := etaStar_mem hσκ hβ0 hβ1
  have hD := denF_pos (η := η) hσκ hβ0.le hβ1.le hφ (by linarith)
  have hneg : -1 / denF σ κ β φ η < 0 := div_neg_of_neg_of_pos (by norm_num) hD
  refine ⟨hneg, mul_pos_of_neg_of_neg ?_ hneg⟩
  have hf : 0 < β * η ^ 2 - (1 + β + σ * κ) * η + 1 := by
    have e := quad_sub σ κ β η (etaStar σ κ β)
    rw [etaStar_root hσκ hβ0 hβ1, sub_zero] at e
    rw [e]
    exact mul_pos_of_neg_of_neg (by linarith) (by nlinarith)
  have : η * (σ * κ) - (1 - β * η) * (1 - η) < 0 := by nlinarith
  rw [sub_neg, lt_div_iff₀ hσκ]
  linarith

/-- Cochrane (2023), pp. 415–416: for `φ > 1` and `η* < η ≤ 1` the interest rate moves with
inflation (opposite to the disturbance): the interest-rate coefficient is negative. -/
theorem full_i_coeff_neg_of_gt {σ κ β φ η : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) (hη1 : etaStar σ κ β < η) (hη : η ≤ 1) :
    (η - (1 - β * η) * (1 - η) / (σ * κ)) * (-1 / denF σ κ β φ η) < 0 := by
  have hD := denF_pos hσκ hβ0.le hβ1.le hφ hη
  have hneg : -1 / denF σ κ β φ η < 0 := div_neg_of_neg_of_pos (by norm_num) hD
  refine mul_neg_of_pos_of_neg ?_ hneg
  have hf : β * η ^ 2 - (1 + β + σ * κ) * η + 1 < 0 := by
    have e := quad_sub σ κ β η (etaStar σ κ β)
    rw [etaStar_root hσκ hβ0 hβ1, sub_zero] at e
    rw [e]
    exact mul_neg_of_pos_of_neg (by linarith) (by nlinarith)
  rw [sub_pos, div_lt_iff₀ hσκ]
  nlinarith

/-- Cochrane (2023), Figure 17.8, p. 416 (`β = 0.95`, `κ = 1/2`, `σ = 1`, `φ = 1.5`,
`η = 0.3`): a negative disturbance lowers the interest rate and raises inflation. -/
theorem fig17_8_transitory {u : ℝ} (hu : u < 0) :
    0 < -1 / denF 1 (1 / 2) 0.95 1.5 0.3 * u ∧
      (0.3 - (1 - 0.95 * 0.3) * (1 - 0.3) / (1 * (1 / 2))) *
        (-1 / denF 1 (1 / 2) 0.95 1.5 0.3) * u < 0 := by
  have hlt : (0.3 : ℝ) < etaStar 1 (1 / 2) 0.95 := by linarith [etaStar_fig17_8.1]
  obtain ⟨h1, h2⟩ := full_i_coeff_pos_of_lt (σ := 1) (κ := 1 / 2) (β := 0.95) (φ := 1.5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlt
  exact ⟨mul_pos_of_neg_of_neg h1 hu, mul_neg_of_pos_of_neg h2 hu⟩

end Cochrane.KeynesianStickyPrices.AR1Responses
