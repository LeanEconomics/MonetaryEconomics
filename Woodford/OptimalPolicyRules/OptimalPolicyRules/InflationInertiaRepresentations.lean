/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.ExpectationTools
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

/-!
# Inflation inertia: instrument-rule and targeting-rule representations

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2 (pp. 592–604) and Appendix G.6–G.10
(pp. 724–745).

With inflation inertia (indexation `γ`), the optimal plan satisfies the Euler equation (3.21),
`E_t[A(L) ı̂_{t+1}] = −f̂_t`, with the cubic `A(L) = βγ(1 − λ₁L)(1 − λ₂L)(1 − λ₃L)` of (3.17),
(3.20) and `f̂_t = q̃_t − βγE_t q̃_{t+1}` of (3.18)–(3.19). The roots are supplied by
Proposition 8.7 (proved in a companion module): here they enter as the hypothesis structure
`InertiaRoots` (Vieta relations (G.19)–(G.20), `0 < λ₁ < 1`, and `λ₂, λ₃` real and above one
or a complex-conjugate pair with real part above one).

## Main results

* `prop_8_10`: **Proposition 8.10** — for bounded adapted `{ı̂, f̂}`, the pure targeting rule
  (3.26) holds at all `t ≥ t₀` iff the Euler equation (3.21) does, for real or complex roots.
* `prop_8_9_ruleI`, `prop_8_9_ruleII`, `prop_8_9_ruleIII`: **Proposition 8.9** — each rule is
  equivalent to the representation (3.25) with `ρ₁ > 1`, `ρ₂ > 0`, `0 < θ_π ≤ φ_π`,
  `0 < θₓ = φₓ` and forecast weights summing to one; `prop_8_9_rule_real_levels`,
  `prop_8_9_ruleIII_levels`: the same in levels (intercept `(1 − ρ₁)i*`);
  `rule_real_formulas`, `InertiaRoots.ruleIII_formulas`: the printed coefficient formulas
  (G.34)–(G.35), (G.39)–(G.47); `prop_8_9_ruleI_limit` (`γ → 0`: `θ_π → 0`, `φ_π → κσ/λᵢ`,
  Rule I → (3.10)) and `prop_8_9_ruleIII_limit_one` (`γ → 1`: `θ_π, φ_π` → the same positive
  limit).
* `prop_8_11`, `prop_8_11_levels`: **Proposition 8.11** — the target criterion (3.26) is
  equivalent to (3.27) with `φₓ = θₓ > 0`, `0 < θ_π ≤ 1`, `θᵢ, θ_Δ > 0`;
  `prop_8_11_limit_zero` (`γ → 0`: `θ_π → 0` and all other coefficients and weights → those of
  (3.13)) and `prop_8_11_limit_one` (`γ → 1`: `θ_π → 1`, `φₓ → 4λₓ/κ`);
  `InertiaRoots.SpiK_partial_fractions` (distinct roots, (G.55)) and
  `InertiaRoots.repeated_root` (`λ₂ = λ₃`: `K_j = (1 + j)λ^{−j}`,
  `∑(1 + j)λ^{−j} = (1 − λ⁻¹)^{−2}`).
* `lemma_G2`: **Lemma G.2**, with the missing boundedness step proved: `γλ₃ → β⁻¹`, `λ₃⁻¹ → 0`,
  and `λ₁, λ₂ →` the roots of the `γ = 0` quadratic; `l1_tendsto_one`, `s_p_tendsto_one`:
  continuity of the roots at `γ = 1`.
* Numbers: `gamma_bar_table61` (at Table 6.1, the roots are real for `γ ≤ 0.353` and a complex
  pair for `γ ≥ 0.354`, so `γ̄ ≈ .35`), `fig_8_4_mean_horizon` (closed form
  `meanHorizon_gamma_one`; at Table 6.1 and `γ = 1`, `0.564 < λ₁ < 0.565` and the mean horizon
  of the Rule III weights lies in `(2.2, 2.25)`), `fig_8_4_abs_weight_ratio`
  (`0.386 < ∑_{j>0}|α_j|/α_0 < 0.389`, by interval arithmetic), `InertiaRoots.gamma_one_coeffs` and
  `fig_8_5_phiX` (`φₓ(γ = 1) = 4λₓ/κ = 4/θ ≈ 0.508`).

## Method

The double forward inverse `(1 − λ₂⁻¹L⁻¹)⁻¹(1 − λ₃⁻¹L⁻¹)⁻¹` is represented by its real kernel
`K_j` (`Kker`: `K_0 = 1`, `K_1 = s/p`, `K_{j+2} = (s/p)K_{j+1} − p⁻¹K_j`, with real
`s = λ₂ + λ₃`, `p = λ₂λ₃`), which equals the complex Cauchy product
`∑_{k≤j} λ₂^{−k}λ₃^{−(j−k)}` (`Kker_eq_cauchy`) — so one treatment covers distinct real,
repeated and complex roots. Absolute summability comes from `|K_j| ≤ (j + 1) rʲ`,
`r = max(|λ₂|⁻¹, |λ₃|⁻¹) < 1`. Uniqueness in Proposition 8.10 iterates the homogeneous
equation with the same kernel (`homog_eq_zero`). The book's route through complex-valued
processes is also used: the complex conditional expectation `ExpectationTools.EC`, the complex
forward-inverse lemma (`ExpectationTools.fwdC_solves`, `ExpectationTools.fwdC_unique`), and
`InertiaRoots.double_forward_inverse`, which shows that the two successive complex forward
inverses equal the real kernel forecast; `InertiaRoots.ruleIII_rhs` does the same for Rule III.
All infinite sums are genuine `tsum`s with proved summability.
Equations hold for an arbitrary `ExpectationSystem`, so results hold under perfect foresight
and under uncertainty. Dates `t ≥ 2` are written `n + 2` (two lags appear).
-/

namespace Woodford.OptimalPolicyRules.InflationInertiaRepresentations

open Filter Topology
open ExpectationTools (EC EC_add EC_smul EC_ofReal EC_tower norm_EC_le EC_tsum fwdC EC_fwdC
  fwdC_solves fwdC_unique)

/-! ### Kernels: sequences of weights on forecasts -/

/-- Woodford (2003), App. G.8, p. 731: the kernel lagged once, `wPrev w j = w (j − 1)` for
`j ≥ 1` and `wPrev w 0 = 0` (the weight `w_{j−1}` in (G.29), with `w_{−1} = 0`). -/
def wPrev (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => w j

/-- Woodford (2003), (G.27)–(G.32), pp. 731–732: substituting `f̂_{t+j} = a y_{t+j−1} + b y_{t+j}
+ c y_{t+j+1}` into `∑ w_j E_t f̂_{t+j}` gives the weight `c w_{j−1} + b w_j + a w_{j+1}` on
`E_t y_{t+j}` (`j ≥ 0`). -/
def conv3 (a b c : ℝ) (w : ℕ → ℝ) (j : ℕ) : ℝ := c * wPrev w j + b * w j + a * w (j + 1)

/-- Woodford (2003), App. G.8, p. 731: `∑_j w_{j−1} = ∑_j w_j`. -/
theorem hasSum_wPrev {w : ℕ → ℝ} {W : ℝ} (hw : HasSum w W) : HasSum (wPrev w) W := by
  have h : HasSum (fun n => wPrev w (n + 1)) (W - ∑ i ∈ Finset.range 1, wPrev w i) := by
    simpa [wPrev] using hw
  exact (hasSum_nat_add_iff' 1).mp h

/-- Woodford (2003), App. G.8, p. 731: `∑_j w_{j+1} = ∑_j w_j − w_0`. -/
theorem hasSum_shift {w : ℕ → ℝ} {W : ℝ} (hw : HasSum w W) :
    HasSum (fun j => w (j + 1)) (W - w 0) := by
  have := (hasSum_nat_add_iff' 1).mpr hw
  simpa using this

/-- Woodford (2003), App. G.8, pp. 732–733 (the sums `S_π` and `∑ α_{x,j}`): the weights
`conv3 a b c w` sum to `(a + b + c) W − a w_0`. -/
theorem hasSum_conv3 {w : ℕ → ℝ} {W : ℝ} (hw : HasSum w W) (a b c : ℝ) :
    HasSum (conv3 a b c w) ((a + b + c) * W - a * w 0) := by
  have h1 := (hasSum_wPrev hw).mul_left c
  have h2 := hw.mul_left b
  have h3 := (hasSum_shift hw).mul_left a
  have e : (a + b + c) * W - a * w 0 = c * W + b * W + a * (W - w 0) := by ring
  rw [e]
  exact (h1.add h2).add h3

/-- Woodford (2003), App. G.8: `|w_{j−1}|` is summable when `|w_j|` is. -/
theorem summable_abs_wPrev {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) :
    Summable (fun j => |wPrev w j|) := by
  have h : Summable (fun n => |wPrev w (n + 1)|) := hw
  exact (summable_nat_add_iff 1).mp h

/-- Woodford (2003), App. G.8: the weights `conv3 a b c w` are absolutely summable. -/
theorem summable_abs_conv3 {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) (a b c : ℝ) :
    Summable (fun j => |conv3 a b c w j|) := by
  have h1 := (summable_abs_wPrev hw).mul_left |c|
  have h2 := hw.mul_left |b|
  have h3 := ((summable_nat_add_iff 1).mpr hw).mul_left |a|
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_) ((h1.add h2).add h3)
  unfold conv3
  calc |c * wPrev w j + b * w j + a * w (j + 1)|
      ≤ |c * wPrev w j| + |b * w j| + |a * w (j + 1)| := abs_add_three _ _ _
    _ = |c| * |wPrev w j| + |b| * |w j| + |a| * |w (j + 1)| := by
        rw [abs_mul, abs_mul, abs_mul]

/-- Woodford (2003), App. G.9–G.10, pp. 737–745: the second-order linear recurrence
`x_{j+2} = a x_{j+1} + b x_j` with initial values `x_0, x_1`. The double forward inverse
`(1 − λ₂⁻¹L⁻¹)⁻¹(1 − λ₃⁻¹L⁻¹)⁻¹` has coefficients of this form. -/
def rec2 (a b x0 x1 : ℝ) : ℕ → ℝ
  | 0 => x0
  | 1 => x1
  | j + 2 => a * rec2 a b x0 x1 (j + 1) + b * rec2 a b x0 x1 j

/-- Woodford (2003), App. G.10: the defining recurrence of `rec2`. -/
theorem rec2_succ_succ (a b x0 x1 : ℝ) (j : ℕ) :
    rec2 a b x0 x1 (j + 2) = a * rec2 a b x0 x1 (j + 1) + b * rec2 a b x0 x1 j := rfl

/-- Woodford (2003), (G.55), p. 741: the sum of a summable second-order recurrence,
`(1 − a − b) ∑ x_j = x_0 + x_1 − a x_0`. -/
theorem tsum_rec2 {a b x0 x1 : ℝ} (hs : Summable (rec2 a b x0 x1)) :
    (1 - a - b) * ∑' j, rec2 a b x0 x1 j = x0 + x1 - a * x0 := by
  set W := ∑' j, rec2 a b x0 x1 j
  have hW : HasSum (rec2 a b x0 x1) W := hs.hasSum
  have h1 : HasSum (fun j => rec2 a b x0 x1 (j + 1)) (W - x0) := hasSum_shift hW
  have h2 : HasSum (fun j => rec2 a b x0 x1 (j + 2)) (W - x0 - x1) := by
    have := hasSum_shift h1
    simpa [rec2] using this
  have h3 : HasSum (fun j => rec2 a b x0 x1 (j + 2)) (a * (W - x0) + b * W) := by
    have := (h1.mul_left a).add (hW.mul_left b)
    simpa [rec2_succ_succ] using this
  have := h2.unique h3
  linear_combination this

/-- Woodford (2003), App. G.10: a complex sequence satisfying the same recurrence with the same
initial values coincides with the real recurrence. -/
theorem rec2_ofReal {a b x0 x1 : ℝ} {z : ℕ → ℂ}
    (hz : ∀ j, z (j + 2) = (a : ℂ) * z (j + 1) + (b : ℂ) * z j) (h0 : z 0 = x0)
    (h1 : z 1 = x1) (j : ℕ) : ((rec2 a b x0 x1 j : ℝ) : ℂ) = z j := by
  have key : ∀ j, ((rec2 a b x0 x1 j : ℝ) : ℂ) = z j ∧
      ((rec2 a b x0 x1 (j + 1) : ℝ) : ℂ) = z (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨h0.symm, h1.symm⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [rec2_succ_succ, hz j]
      push_cast
      rw [ih.1, ih.2]
  exact (key j).1

/-! ### The complex kernels: Cauchy products and power sums of inverse roots -/

/-- Woodford (2003), (3.26), p. 601 and App. G.9: the coefficients of the product of the two
geometric series `(1 − μ₂L⁻¹)⁻¹(1 − μ₃L⁻¹)⁻¹`, defined recursively by `C_0 = 1`,
`C_{j+1} = μ₃ C_j + μ₂^{j+1}` (so `C_j = ∑_{k ≤ j} μ₂ᵏ μ₃^{j−k}`). -/
def cauchyK (μ2 μ3 : ℂ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => μ3 * cauchyK μ2 μ3 j + μ2 ^ (j + 1)

/-- Woodford (2003), App. G.9: `C_j = ∑_{k ≤ j} μ₂ᵏ μ₃^{j−k}` is the Cauchy product of the
two geometric kernels `μ₂ᵏ` and `μ₃ᵏ`. -/
theorem cauchyK_eq_sum (μ2 μ3 : ℂ) (j : ℕ) :
    cauchyK μ2 μ3 j = ∑ k ∈ Finset.range (j + 1), μ2 ^ k * μ3 ^ (j - k) := by
  induction j with
  | zero => simp [cauchyK]
  | succ j ih =>
    rw [cauchyK, ih, Finset.sum_range_succ _ (j + 1), Finset.mul_sum, Nat.sub_self, pow_zero,
      mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show j + 1 - k = (j - k) + 1 by omega, pow_succ]
    ring

/-- Woodford (2003), App. G.9: the Cauchy-product kernel satisfies
`C_{j+2} = (μ₂ + μ₃) C_{j+1} − μ₂μ₃ C_j`. -/
theorem cauchyK_rec (μ2 μ3 : ℂ) (j : ℕ) :
    cauchyK μ2 μ3 (j + 2) = (μ2 + μ3) * cauchyK μ2 μ3 (j + 1) + (-(μ2 * μ3)) * cauchyK μ2 μ3 j := by
  have h1 : cauchyK μ2 μ3 (j + 2) = μ3 * cauchyK μ2 μ3 (j + 1) + μ2 ^ (j + 2) := rfl
  have h2 : cauchyK μ2 μ3 (j + 1) = μ3 * cauchyK μ2 μ3 j + μ2 ^ (j + 1) := rfl
  rw [h1, h2]
  ring

/-- Woodford (2003), App. G.9: `‖C_j‖ ≤ (j + 1) rʲ` when `‖μ₂‖, ‖μ₃‖ ≤ r`. -/
theorem norm_cauchyK_le {μ2 μ3 : ℂ} {r : ℝ} (h2 : ‖μ2‖ ≤ r) (h3 : ‖μ3‖ ≤ r) (j : ℕ) :
    ‖cauchyK μ2 μ3 j‖ ≤ ((j : ℝ) + 1) * r ^ j := by
  have hr : 0 ≤ r := (norm_nonneg _).trans h2
  induction j with
  | zero => simp [cauchyK]
  | succ j ih =>
    change ‖μ3 * cauchyK μ2 μ3 j + μ2 ^ (j + 1)‖ ≤ _
    calc ‖μ3 * cauchyK μ2 μ3 j + μ2 ^ (j + 1)‖
        ≤ ‖μ3‖ * ‖cauchyK μ2 μ3 j‖ + ‖μ2‖ ^ (j + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ r * (((j : ℝ) + 1) * r ^ j) + r ^ (j + 1) := by
          gcongr
      _ = (((j + 1 : ℕ) : ℝ) + 1) * r ^ (j + 1) := by
          push_cast
          ring

/-- Woodford (2003), (G.53)–(G.54), p. 740 (partial fractions, distinct roots): with
`c₂ = λ₃/(λ₃ − λ₂)`, `c₃ = λ₂/(λ₃ − λ₂)` and `μ_k = λ_k⁻¹`,
`C_j = c₂ λ₂^{−j} − c₃ λ₃^{−j}`. -/
theorem cauchyK_partial_fractions {l2 l3 : ℂ} (h2 : l2 ≠ 0) (h3 : l3 ≠ 0) (h23 : l2 ≠ l3)
    (j : ℕ) :
    cauchyK l2⁻¹ l3⁻¹ j = l3 / (l3 - l2) * l2⁻¹ ^ j - l2 / (l3 - l2) * l3⁻¹ ^ j := by
  have hsub : l3 - l2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
  have key : (l2⁻¹ - l3⁻¹) * cauchyK l2⁻¹ l3⁻¹ j = l2⁻¹ ^ (j + 1) - l3⁻¹ ^ (j + 1) := by
    induction j with
    | zero => simp [cauchyK]
    | succ j ih =>
      change (l2⁻¹ - l3⁻¹) * (l3⁻¹ * cauchyK l2⁻¹ l3⁻¹ j + l2⁻¹ ^ (j + 1)) = _
      linear_combination l3⁻¹ * ih
  have hd : l2⁻¹ - l3⁻¹ ≠ 0 := by
    intro h
    apply h23
    have := sub_eq_zero.mp h
    exact inv_injective this
  have hC : cauchyK l2⁻¹ l3⁻¹ j = (l2⁻¹ ^ (j + 1) - l3⁻¹ ^ (j + 1)) / (l2⁻¹ - l3⁻¹) := by
    rw [← key]
    field_simp
  rw [hC, div_eq_iff hd, pow_succ, pow_succ]
  field_simp

/-- Woodford (2003), App. G.10, p. 743 (repeated root `λ₂ = λ₃`):
`C_j = (1 + j) λ^{−j}`. -/
theorem cauchyK_repeated (μ : ℂ) (j : ℕ) : cauchyK μ μ j = ((j : ℂ) + 1) * μ ^ j := by
  induction j with
  | zero => simp [cauchyK]
  | succ j ih =>
    change μ * cauchyK μ μ j + μ ^ (j + 1) = _
    rw [ih]
    push_cast
    ring

/-- Woodford (2003), App. G.10, pp. 743–745: `∑_j (1 + j) λ^{−j} = (1 − λ⁻¹)^{−2}` for `|λ| > 1`
(stated for `μ = λ⁻¹`, `‖μ‖ < 1`). -/
theorem hasSum_one_add_mul_geometric {μ : ℂ} (hμ : ‖μ‖ < 1) :
    HasSum (fun j : ℕ => ((j : ℂ) + 1) * μ ^ j) ((1 - μ)⁻¹ ^ 2) := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hμ
  have h2 := hasSum_geometric_of_norm_lt_one hμ
  have hne : 1 - μ ≠ 0 := by
    intro h
    have : μ = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at hμ
    exact lt_irrefl _ hμ
  convert h1.add h2 using 1
  · funext j
    ring
  · field_simp
    ring

/-- Woodford (2003), App. G.8–G.10: `∑ (j + 1) rʲ` converges for `0 ≤ r < 1`. -/
theorem summable_succ_mul_geometric {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) * r ^ j) := by
  have ha : Summable (fun j : ℕ => (j : ℝ) ^ 1 * r ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have hb := summable_geometric_of_lt_one h0 h1
  refine (ha.add hb).congr fun j => ?_
  ring


/-! ### Rearranging forecast series (pure sequence lemmas) -/

/-- Woodford (2003), App. G.8: a series `∑ u_j H_j` with `∑ |u_j| < ∞` and `|H_j| ≤ M`
converges. -/
theorem summable_mul_of_abs {u H : ℕ → ℝ} {M : ℝ} (hu : Summable (fun j => |u j|))
    (hH : ∀ j, |H j| ≤ M) : Summable (fun j => u j * H j) := by
  refine Summable.of_norm_bounded (hu.mul_right M) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hH j) (abs_nonneg _)

/-- Woodford (2003), (G.29) and (G.32), pp. 731–732: substituting the three-term expression
`a y_{t+j−1} + b y_{t+j} + c y_{t+j+1}` (here `Y_k = y_{t−1+k}`) into a kernel series:
`∑_j w_j (a Y_j + b Y_{j+1} + c Y_{j+2}) = a w_0 Y_0 + ∑_j (c w_{j−1} + b w_j + a w_{j+1}) Y_{j+1}`.
-/
theorem tsum_three_term {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) {Y : ℕ → ℝ} {M : ℝ}
    (hY : ∀ k, |Y k| ≤ M) (a b c : ℝ) :
    ∑' j, w j * (a * Y j + b * Y (j + 1) + c * Y (j + 2)) =
      a * w 0 * Y 0 + ∑' j, conv3 a b c w j * Y (j + 1) := by
  have hw1 : Summable (fun j => |w (j + 1)|) := (summable_nat_add_iff 1).mpr hw
  have s0 := summable_mul_of_abs hw hY
  have s1 := summable_mul_of_abs hw (fun j => hY (j + 1))
  have s2 := summable_mul_of_abs hw (fun j => hY (j + 2))
  have sP := summable_mul_of_abs (summable_abs_wPrev hw) (fun j => hY (j + 1))
  have sS := summable_mul_of_abs hw1 (fun j => hY (j + 1))
  have e0 : ∑' j, w j * Y j = w 0 * Y 0 + ∑' j, w (j + 1) * Y (j + 1) := s0.tsum_eq_zero_add
  have eP : ∑' j, wPrev w j * Y (j + 1) = ∑' j, w j * Y (j + 2) := by
    rw [sP.tsum_eq_zero_add]
    simp [wPrev]
  have lhs : ∑' j, w j * (a * Y j + b * Y (j + 1) + c * Y (j + 2)) =
      a * ∑' j, w j * Y j + b * ∑' j, w j * Y (j + 1) + c * ∑' j, w j * Y (j + 2) := by
    have H := ((s0.hasSum.mul_left a).add (s1.hasSum.mul_left b)).add (s2.hasSum.mul_left c)
    rw [← H.tsum_eq]
    exact tsum_congr fun j => by ring
  have rhs : ∑' j, conv3 a b c w j * Y (j + 1) =
      c * ∑' j, wPrev w j * Y (j + 1) + b * ∑' j, w j * Y (j + 1) +
        a * ∑' j, w (j + 1) * Y (j + 1) := by
    have H := ((sP.hasSum.mul_left c).add (s1.hasSum.mul_left b)).add (sS.hasSum.mul_left a)
    rw [← H.tsum_eq]
    exact tsum_congr fun j => by unfold conv3; ring
  rw [lhs, rhs, e0, eP]
  ring

/-- Woodford (2003), App. G.9 (the recursion behind the double forward inverse): for a kernel
with `w_1 = a w_0` and `w_{j+2} = a w_{j+1} + b w_j`, and bounded `G`,
`∑ w_j G_j = w_0 G_0 + a ∑ w_j G_{j+1} + b ∑ w_j G_{j+2}`. -/
theorem tsum_rec2_identity {a b : ℝ} {w : ℕ → ℝ} (hw : Summable (fun j => |w j|))
    (hw1 : w 1 = a * w 0) (hrec : ∀ j, w (j + 2) = a * w (j + 1) + b * w j)
    {G : ℕ → ℝ} {M : ℝ} (hG : ∀ k, |G k| ≤ M) :
    ∑' j, w j * G j = w 0 * G 0 + a * ∑' j, w j * G (j + 1) + b * ∑' j, w j * G (j + 2) := by
  have hw1' : Summable (fun j => |w (j + 1)|) := (summable_nat_add_iff 1).mpr hw
  have s0 := summable_mul_of_abs hw hG
  have s1 := summable_mul_of_abs hw (fun j => hG (j + 1))
  have s2 := summable_mul_of_abs hw (fun j => hG (j + 2))
  have s11 := summable_mul_of_abs hw1' (fun j => hG (j + 1))
  have s12 := summable_mul_of_abs hw1' (fun j => hG (j + 2))
  have e0 : ∑' j, w j * G j = w 0 * G 0 + ∑' j, w (j + 1) * G (j + 1) := s0.tsum_eq_zero_add
  have e1 : ∑' j, w (j + 1) * G (j + 1) = w 1 * G 1 + ∑' j, w (j + 2) * G (j + 2) :=
    s11.tsum_eq_zero_add
  have e2 : ∑' j, w j * G (j + 1) = w 0 * G 1 + ∑' j, w (j + 1) * G (j + 2) :=
    s1.tsum_eq_zero_add
  have e3 : ∑' j, w (j + 2) * G (j + 2) =
      a * ∑' j, w (j + 1) * G (j + 2) + b * ∑' j, w j * G (j + 2) := by
    have H := (s12.hasSum.mul_left a).add (s2.hasSum.mul_left b)
    rw [← H.tsum_eq]
    exact tsum_congr fun j => by rw [hrec j]; ring
  rw [e0, e1, e3, e2, hw1]
  ring

/-! ### The roots of `A(L)` (supplied by Proposition 8.7) -/

variable (β γ κ σ l1 : ℝ) (l2 l3 : ℂ)

/-- Woodford (2003), Proposition 8.7, p. 594, and (3.20), (G.16)–(G.20), pp. 724–725: the
factorization `A(L) = βγ(1 − λ₁L)(1 − λ₂L)(1 − λ₃L)` of the cubic (3.17), recorded through its
Vieta relations (G.19)–(G.20), with `0 < λ₁ < 1` and `λ₂, λ₃` either real and greater than one
or a complex-conjugate pair with real part greater than one. These are the conclusions of
Proposition 8.7 (proved in the companion module on the root location); here they are
hypotheses. -/
structure InertiaRoots where
  /-- `λ₁ > 0`. -/
  l1_pos : 0 < l1
  /-- `λ₁ < 1`. -/
  l1_lt_one : l1 < 1
  /-- Either two real roots above one, or a conjugate pair with real part above one. -/
  shape : (l2.im = 0 ∧ l3.im = 0 ∧ 1 < l2.re ∧ 1 < l3.re) ∨ (l3 = (starRingEnd ℂ) l2 ∧ 1 < l2.re)
  /-- (G.20): `βγ(λ₁ + λ₂ + λ₃) = 1 + γ + βγ`. -/
  vieta1 : (β * γ : ℂ) * (l1 + l2 + l3) = 1 + γ + β * γ
  /-- Coefficient of `L²`: `βγ(λ₁λ₂ + λ₁λ₃ + λ₂λ₃) = 1 + γ + β⁻¹(1 + κσ)`. -/
  vieta2 : (β * γ : ℂ) * (l1 * l2 + l1 * l3 + l2 * l3) = 1 + γ + (1 + κ * σ) / β
  /-- (G.19): `βγ λ₁λ₂λ₃ = β⁻¹`. -/
  vieta3 : (β * γ : ℂ) * (l1 * l2 * l3) = β⁻¹

variable {β γ κ σ l1 l2 l3}

/-- Woodford (2003), (3.24), p. 595: the real sum `s = λ₂ + λ₃` of the two outer roots. -/
def sR (l2 l3 : ℂ) : ℝ := (l2 + l3).re

/-- Woodford (2003), (3.26), p. 601: the real product `p = λ₂λ₃` of the two outer roots. -/
def pR (l2 l3 : ℂ) : ℝ := (l2 * l3).re

/-- Woodford (2003), App. G.8, p. 735: `λ₂ + λ₃` is real. -/
theorem InertiaRoots.sum_im (h : InertiaRoots β γ κ σ l1 l2 l3) : (l2 + l3).im = 0 := by
  rcases h.shape with ⟨h2, h3, -, -⟩ | ⟨hc, -⟩
  · simp [Complex.add_im, h2, h3]
  · rw [hc]
    simp [Complex.add_im]

/-- Woodford (2003), App. G.8, p. 736: `λ₂λ₃` is real. -/
theorem InertiaRoots.prod_im (h : InertiaRoots β γ κ σ l1 l2 l3) : (l2 * l3).im = 0 := by
  rcases h.shape with ⟨h2, h3, -, -⟩ | ⟨hc, -⟩
  · simp [Complex.mul_im, h2, h3]
  · rw [hc, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring

/-- Woodford (2003), App. G.8: `λ₂ + λ₃ = s` as complex numbers. -/
theorem InertiaRoots.coe_s (h : InertiaRoots β γ κ σ l1 l2 l3) :
    ((sR l2 l3 : ℝ) : ℂ) = l2 + l3 :=
  Complex.ext (by simp [sR]) (by simp [h.sum_im])

/-- Woodford (2003), App. G.8: `λ₂λ₃ = p` as complex numbers. -/
theorem InertiaRoots.coe_p (h : InertiaRoots β γ κ σ l1 l2 l3) :
    ((pR l2 l3 : ℝ) : ℂ) = l2 * l3 :=
  Complex.ext (by simp [pR]) (by simp [h.prod_im])

/-- Woodford (2003), App. G.6, p. 725: `(λ₂ + λ₃)/2 > 1`, i.e. `s > 2`. -/
theorem InertiaRoots.two_lt_s (h : InertiaRoots β γ κ σ l1 l2 l3) : 2 < sR l2 l3 := by
  unfold sR
  rcases h.shape with ⟨-, -, h2, h3⟩ | ⟨hc, hr⟩
  · rw [Complex.add_re]
    linarith
  · rw [hc, Complex.add_re, Complex.conj_re]
    linarith

/-- Woodford (2003), App. G.8: `p = λ₂λ₃ > 1`. -/
theorem InertiaRoots.one_lt_p (h : InertiaRoots β γ κ σ l1 l2 l3) : 1 < pR l2 l3 := by
  unfold pR
  rcases h.shape with ⟨h2i, h3i, h2, h3⟩ | ⟨hc, hr⟩
  · rw [Complex.mul_re, h2i, h3i]
    nlinarith
  · rw [hc, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg l2.im]

/-- Woodford (2003), App. G.8, (G.37): `(1 − λ₂)(1 − λ₃) = 1 − s + p > 0`. -/
theorem InertiaRoots.one_sub_s_add_p_pos (h : InertiaRoots β γ κ σ l1 l2 l3) :
    0 < 1 - sR l2 l3 + pR l2 l3 := by
  unfold sR pR
  rcases h.shape with ⟨h2i, h3i, h2, h3⟩ | ⟨hc, hr⟩
  · rw [Complex.mul_re, Complex.add_re, h2i, h3i]
    nlinarith
  · rw [hc, Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg l2.im]

/-- Woodford (2003), Proposition 8.7: `|λ₂| > 1`. -/
theorem InertiaRoots.one_lt_norm_l2 (h : InertiaRoots β γ κ σ l1 l2 l3) : 1 < ‖l2‖ := by
  have hre : 1 < l2.re := by
    rcases h.shape with ⟨-, -, h2, -⟩ | ⟨-, hr⟩
    · exact h2
    · exact hr
  exact hre.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm l2))

/-- Woodford (2003), Proposition 8.7: `|λ₃| > 1`. -/
theorem InertiaRoots.one_lt_norm_l3 (h : InertiaRoots β γ κ σ l1 l2 l3) : 1 < ‖l3‖ := by
  rcases h.shape with ⟨-, -, -, h3⟩ | ⟨hc, -⟩
  · exact h3.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm l3))
  · rw [hc, Complex.norm_conj]
    exact h.one_lt_norm_l2

/-- Woodford (2003), (G.20), p. 725, in real form: `βγ(λ₁ + s) = 1 + γ + βγ`. -/
theorem InertiaRoots.vieta1_real (h : InertiaRoots β γ κ σ l1 l2 l3) :
    β * γ * (l1 + sR l2 l3) = 1 + γ + β * γ := by
  have := h.vieta1
  rw [add_assoc, ← h.coe_s] at this
  exact_mod_cast this

/-- Woodford (2003), (G.18), p. 725, in real form: `βγ(λ₁ s + p) = 1 + γ + β⁻¹(1 + κσ)`. -/
theorem InertiaRoots.vieta2_real (h : InertiaRoots β γ κ σ l1 l2 l3) :
    β * γ * (l1 * sR l2 l3 + pR l2 l3) = 1 + γ + (1 + κ * σ) / β := by
  have := h.vieta2
  rw [show (l1 : ℂ) * l2 + l1 * l3 + l2 * l3 = l1 * (l2 + l3) + l2 * l3 by ring, ← h.coe_s,
    ← h.coe_p] at this
  exact_mod_cast this

/-- Woodford (2003), (G.19), p. 725, in real form: `βγ λ₁ p = β⁻¹`. -/
theorem InertiaRoots.vieta3_real (h : InertiaRoots β γ κ σ l1 l2 l3) :
    β * γ * (l1 * pR l2 l3) = β⁻¹ := by
  have := h.vieta3
  rw [mul_assoc (l1 : ℂ), ← h.coe_p] at this
  exact_mod_cast this

/-- Woodford (2003), Proposition 8.7: `λ₂ ≠ 0`. -/
theorem InertiaRoots.l2_ne_zero (h : InertiaRoots β γ κ σ l1 l2 l3) : l2 ≠ 0 := fun h0 => by
  have := h.one_lt_norm_l2
  rw [h0, norm_zero] at this
  linarith

/-- Woodford (2003), Proposition 8.7: `λ₃ ≠ 0`. -/
theorem InertiaRoots.l3_ne_zero (h : InertiaRoots β γ κ σ l1 l2 l3) : l3 ≠ 0 := fun h0 => by
  have := h.one_lt_norm_l3
  rw [h0, norm_zero] at this
  linarith

/-- Woodford (2003), App. G.8–G.9: the inverse roots satisfy `λ₂⁻¹ + λ₃⁻¹ = s/p`. -/
theorem InertiaRoots.inv_add_inv (h : InertiaRoots β γ κ σ l1 l2 l3) :
    l2⁻¹ + l3⁻¹ = ((sR l2 l3 / pR l2 l3 : ℝ) : ℂ) := by
  have h2 := h.l2_ne_zero
  have h3 := h.l3_ne_zero
  push_cast
  rw [h.coe_s, h.coe_p]
  field_simp
  ring

/-- Woodford (2003), App. G.8–G.9: `λ₂⁻¹λ₃⁻¹ = 1/p`. -/
theorem InertiaRoots.inv_mul_inv (h : InertiaRoots β γ κ σ l1 l2 l3) :
    l2⁻¹ * l3⁻¹ = ((1 / pR l2 l3 : ℝ) : ℂ) := by
  push_cast
  rw [h.coe_p, one_div, mul_inv]

/-! ### The kernels of the three representations -/

/-- Woodford (2003), (3.26), p. 601 and (G.49)–(G.54): the real coefficients `K_j` of the double
forward inverse `(1 − λ₂⁻¹L⁻¹)⁻¹(1 − λ₃⁻¹L⁻¹)⁻¹`, defined by the recursion
`K_0 = 1`, `K_1 = s/p`, `K_{j+2} = (s/p)K_{j+1} − p⁻¹K_j`. -/
noncomputable def Kker (s p : ℝ) : ℕ → ℝ := rec2 (s / p) (-1 / p) 1 (s / p * 1)

/-- Woodford (2003), (3.24), p. 595 and (G.38)–(G.42): the power sums `P_j = λ₂^{−j} + λ₃^{−j}`
as a real recursion (`P_0 = 2`, `P_1 = s/p`). -/
noncomputable def Pker (s p : ℝ) : ℕ → ℝ := rec2 (s / p) (-1 / p) 2 (s / p)

/-- Woodford (2003), (3.24), p. 595 and (G.38): the kernel of Rule III,
`½(βγλ₃)⁻¹∑λ₃^{−j} + ½(βγλ₂)⁻¹∑λ₂^{−j} = (βγ)⁻¹ ∑ ½(λ₂^{−j−1} + λ₃^{−j−1})`, i.e. weights
`P_{j+1}/2`. -/
noncomputable def ruleIIIker (s p : ℝ) (j : ℕ) : ℝ := Pker s p (j + 1) / 2

/-- Woodford (2003), (3.22)–(3.23), p. 595: the geometric kernel `μʲ` (`μ = λ₃⁻¹` for Rule I,
`μ = λ₂⁻¹` for Rule II). -/
def geomKer (μ : ℝ) (j : ℕ) : ℝ := μ ^ j

/-- Woodford (2003), (3.26), p. 601: `K_j` is the Cauchy product `∑_{k ≤ j} λ₂^{−k}λ₃^{−(j−k)}`
of the two geometric kernels. -/
theorem InertiaRoots.Kker_eq_cauchy (h : InertiaRoots β γ κ σ l1 l2 l3) (j : ℕ) :
    ((Kker (sR l2 l3) (pR l2 l3) j : ℝ) : ℂ) = cauchyK l2⁻¹ l3⁻¹ j := by
  refine rec2_ofReal (z := cauchyK l2⁻¹ l3⁻¹) (fun j => ?_) (by simp [cauchyK]) ?_ j
  · rw [cauchyK_rec, ← h.inv_add_inv]
    have hm : ((-1 / pR l2 l3 : ℝ) : ℂ) = -(l2⁻¹ * l3⁻¹) := by
      rw [h.inv_mul_inv]
      push_cast
      ring
    rw [hm]
  · rw [mul_one, ← h.inv_add_inv]
    simp [cauchyK]
    ring

/-- Woodford (2003), (G.41)–(G.42): `P_j = λ₂^{−j} + λ₃^{−j}`. -/
theorem InertiaRoots.Pker_eq_powers (h : InertiaRoots β γ κ σ l1 l2 l3) (j : ℕ) :
    ((Pker (sR l2 l3) (pR l2 l3) j : ℝ) : ℂ) = l2⁻¹ ^ j + l3⁻¹ ^ j := by
  refine rec2_ofReal (z := fun j => l2⁻¹ ^ j + l3⁻¹ ^ j) (fun j => ?_) (by norm_num) ?_ j
  · rw [← h.inv_add_inv]
    have hm : ((-1 / pR l2 l3 : ℝ) : ℂ) = -(l2⁻¹ * l3⁻¹) := by
      rw [h.inv_mul_inv]
      push_cast
      ring
    rw [hm]
    ring
  · rw [← h.inv_add_inv]
    simp

/-- Woodford (2003), (3.24), p. 595: the Rule III kernel is
`½(λ₃⁻¹ λ₃^{−j} + λ₂⁻¹ λ₂^{−j})`, the combination of the two forward inverses. -/
theorem InertiaRoots.ruleIIIker_eq (h : InertiaRoots β γ κ σ l1 l2 l3) (j : ℕ) :
    ((ruleIIIker (sR l2 l3) (pR l2 l3) j : ℝ) : ℂ) =
      (l3⁻¹ * l3⁻¹ ^ j + l2⁻¹ * l2⁻¹ ^ j) / 2 := by
  unfold ruleIIIker
  push_cast
  rw [h.Pker_eq_powers, pow_succ, pow_succ]
  ring

/-- Woodford (2003), Proposition 8.7: the larger of `|λ₂|⁻¹, |λ₃|⁻¹` is below one. -/
theorem InertiaRoots.rmax_lt_one (h : InertiaRoots β γ κ σ l1 l2 l3) :
    max ‖l2⁻¹‖ ‖l3⁻¹‖ < 1 := by
  rw [norm_inv, norm_inv]
  exact max_lt (inv_lt_one_of_one_lt₀ h.one_lt_norm_l2) (inv_lt_one_of_one_lt₀ h.one_lt_norm_l3)

/-- Woodford (2003), App. G.9: `∑ |K_j| < ∞` (the double forward inverse is a bounded operator),
from `|K_j| ≤ (j + 1) rʲ` with `r = max(|λ₂|⁻¹, |λ₃|⁻¹) < 1`. -/
theorem InertiaRoots.summable_abs_Kker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    Summable (fun j => |Kker (sR l2 l3) (pR l2 l3) j|) := by
  set r := max ‖l2⁻¹‖ ‖l3⁻¹‖
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (le_max_left _ _)
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_)
    (summable_succ_mul_geometric hr0 h.rmax_lt_one)
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h.Kker_eq_cauchy]
  exact norm_cauchyK_le (le_max_left _ _) (le_max_right _ _) j

/-- Woodford (2003), (G.41)–(G.42): `∑ |P_j| < ∞`, from `|P_j| ≤ 2 rʲ`. -/
theorem InertiaRoots.summable_abs_Pker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    Summable (fun j => |Pker (sR l2 l3) (pR l2 l3) j|) := by
  set r := max ‖l2⁻¹‖ ‖l3⁻¹‖
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (le_max_left _ _)
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_)
    ((summable_geometric_of_lt_one hr0 h.rmax_lt_one).mul_left 2)
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h.Pker_eq_powers]
  calc ‖l2⁻¹ ^ j + l3⁻¹ ^ j‖ ≤ ‖l2⁻¹‖ ^ j + ‖l3⁻¹‖ ^ j := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_pow, norm_pow]
    _ ≤ r ^ j + r ^ j := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = 2 * r ^ j := by ring

/-- Woodford (2003), (G.38): the Rule III kernel is absolutely summable. -/
theorem InertiaRoots.summable_abs_ruleIIIker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    Summable (fun j => |ruleIIIker (sR l2 l3) (pR l2 l3) j|) := by
  have := ((summable_nat_add_iff 1).mpr h.summable_abs_Pker).mul_left (1 / 2)
  refine this.congr fun j => ?_
  unfold ruleIIIker
  rw [abs_div, abs_two]
  ring

/-- Woodford (2003), (G.55), p. 741: `∑_j K_j = ((1 − λ₂⁻¹)(1 − λ₃⁻¹))⁻¹ = p/(1 − s + p)`. -/
theorem InertiaRoots.hasSum_Kker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    HasSum (Kker (sR l2 l3) (pR l2 l3)) (pR l2 l3 / (1 - sR l2 l3 + pR l2 l3)) := by
  have hs : Summable (Kker (sR l2 l3) (pR l2 l3)) := summable_abs_iff.mp h.summable_abs_Kker
  have key := tsum_rec2 hs
  have hp : pR l2 l3 ≠ 0 := by linarith [h.one_lt_p]
  have hq := h.one_sub_s_add_p_pos
  set T := ∑' j, Kker (sR l2 l3) (pR l2 l3) j
  have k1 : (1 - sR l2 l3 / pR l2 l3 - -1 / pR l2 l3) * T = 1 := by
    exact key.trans (by ring)
  have hm : pR l2 l3 * (1 - sR l2 l3 / pR l2 l3 - -1 / pR l2 l3) = 1 - sR l2 l3 + pR l2 l3 := by
    field_simp
    ring
  have k2 : (1 - sR l2 l3 + pR l2 l3) * T = pR l2 l3 := by
    rw [← hm, mul_assoc, k1, mul_one]
  rw [show pR l2 l3 / (1 - sR l2 l3 + pR l2 l3) = T by
    rw [div_eq_iff hq.ne']
    linarith]
  exact hs.hasSum

/-- Woodford (2003), (G.41)–(G.42): `∑_j P_j = (2p − s)/(1 − s + p)`. -/
theorem InertiaRoots.hasSum_Pker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    HasSum (Pker (sR l2 l3) (pR l2 l3))
      ((2 * pR l2 l3 - sR l2 l3) / (1 - sR l2 l3 + pR l2 l3)) := by
  have hs : Summable (Pker (sR l2 l3) (pR l2 l3)) := summable_abs_iff.mp h.summable_abs_Pker
  have key := tsum_rec2 hs
  have hp : pR l2 l3 ≠ 0 := by linarith [h.one_lt_p]
  have hq := h.one_sub_s_add_p_pos
  set T := ∑' j, Pker (sR l2 l3) (pR l2 l3) j
  have k1 : (1 - sR l2 l3 / pR l2 l3 - -1 / pR l2 l3) * T =
      2 + sR l2 l3 / pR l2 l3 - sR l2 l3 / pR l2 l3 * 2 := key
  have hm : pR l2 l3 * (1 - sR l2 l3 / pR l2 l3 - -1 / pR l2 l3) = 1 - sR l2 l3 + pR l2 l3 := by
    field_simp
    ring
  have hm2 : pR l2 l3 * (2 + sR l2 l3 / pR l2 l3 - sR l2 l3 / pR l2 l3 * 2) =
      2 * pR l2 l3 - sR l2 l3 := by
    field_simp
    ring
  have k2 : (1 - sR l2 l3 + pR l2 l3) * T = 2 * pR l2 l3 - sR l2 l3 := by
    rw [← hm, ← hm2, mul_assoc, k1]
  rw [show (2 * pR l2 l3 - sR l2 l3) / (1 - sR l2 l3 + pR l2 l3) = T by
    rw [div_eq_iff hq.ne']
    linarith]
  exact hs.hasSum

/-- Woodford (2003), (G.38)–(G.47): the Rule III kernel sums to `(s − 2)/(2(1 − s + p))`. -/
theorem InertiaRoots.hasSum_ruleIIIker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    HasSum (ruleIIIker (sR l2 l3) (pR l2 l3))
      ((sR l2 l3 - 2) / (2 * (1 - sR l2 l3 + pR l2 l3))) := by
  have h1 := (hasSum_shift h.hasSum_Pker).div_const 2
  have hq := h.one_sub_s_add_p_pos
  have h0 : Pker (sR l2 l3) (pR l2 l3) 0 = 2 := rfl
  have e : ((2 * pR l2 l3 - sR l2 l3) / (1 - sR l2 l3 + pR l2 l3) -
      Pker (sR l2 l3) (pR l2 l3) 0) / 2 = (sR l2 l3 - 2) / (2 * (1 - sR l2 l3 + pR l2 l3)) := by
    rw [h0]
    field_simp
    ring
  rw [e] at h1
  exact h1


/-! ### The cubic lag polynomial `A(L)` -/

/-- Woodford (2003), eq. (3.17), p. 593 (and (G.17), p. 724): the cubic lag polynomial
`A(z) = βγ − (1 + γ + βγ) z + (1 + γ + β⁻¹(1 + κσ)) z² − β⁻¹ z³`. -/
noncomputable def Apoly (β γ κ σ : ℝ) (z : ℂ) : ℂ :=
  β * γ - (1 + γ + β * γ) * z + (1 + γ + (1 + κ * σ) / β) * z ^ 2 - β⁻¹ * z ^ 3

/-- Woodford (2003), eq. (3.20), p. 594 (and (G.16)): the Vieta relations of Proposition 8.7 give
the factorization `A(z) = βγ(1 − λ₁z)(1 − λ₂z)(1 − λ₃z)`. -/
theorem InertiaRoots.factorization (h : InertiaRoots β γ κ σ l1 l2 l3) (z : ℂ) :
    Apoly β γ κ σ z = β * γ * (1 - l1 * z) * (1 - l2 * z) * (1 - l3 * z) := by
  unfold Apoly
  linear_combination z * h.vieta1 - z ^ 2 * h.vieta2 + z ^ 3 * h.vieta3

/-- Woodford (2003), App. G.6, p. 724: `A(1) = β⁻¹κσ`. -/
theorem Apoly_one (β γ κ σ : ℝ) : Apoly β γ κ σ 1 = κ * σ / β := by
  unfold Apoly
  push_cast
  field_simp
  ring

/-- Woodford (2003), (G.37), p. 734, and App. G.10, p. 743: `A(1) = βγ(1 − λ₁)(1 − λ₂)(1 − λ₃)`
in real form, `βγ(1 − λ₁)(1 − s + p) = κσ/β`. -/
theorem InertiaRoots.A_one_real (h : InertiaRoots β γ κ σ l1 l2 l3) (hβ : β ≠ 0) :
    β * γ * (1 - l1) * (1 - sR l2 l3 + pR l2 l3) = κ * σ / β := by
  have h1 := h.vieta1_real
  have h2 := h.vieta2_real
  have h3 := h.vieta3_real
  have e : κ * σ / β = β * γ - (1 + γ + β * γ) + (1 + γ + (1 + κ * σ) / β) - β⁻¹ := by
    field_simp
    ring
  rw [e]
  linear_combination -h1 + h2 - h3

/-! ### Kernel forecasts `∑_j w_j E_t g_{t+j}` of processes -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (3.25) and (3.27), pp. 597, 601 (the forecast combinations `F_t(z)`) and
(G.21)–(G.23), (G.49): the kernel forecast `∑_j w_j E_t g_{t+j}`. -/
noncomputable def fwd (w : ℕ → ℝ) (g : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, w j * 𝔼.E t (g (t + j)) ω

/-- Woodford (2003), App. G.9: for `s ≤ t`, `E_s` passes through the kernel forecast,
`E_s ∑_j w_j E_t g_{t+j} = ∑_j w_j E_s g_{t+j}`. -/
theorem E_fwd {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) {g : ℕ → Ω → ℝ} {M : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ M) {s t : ℕ} (hst : s ≤ t) (ω : Ω) :
    𝔼.E s (fwd 𝔼 w g t) ω = ∑' j, w j * 𝔼.E s (g (t + j)) ω := by
  have hb : ∀ j ω', |w j * 𝔼.E t (g (t + j)) ω'| ≤ |w j| * M := fun j ω' => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hg (t + j)) t ω') (abs_nonneg _)
  have := ForwardSolution.E_tsum_dom 𝔼 (hw.mul_right M)
    (f := fun j ω' => w j * 𝔼.E t (g (t + j)) ω') hb s ω
  rw [show fwd 𝔼 w g t = fun ω' => ∑' j, w j * 𝔼.E t (g (t + j)) ω' from rfl, this]
  refine tsum_congr fun j => ?_
  change 𝔼.E s (w j • 𝔼.E t (g (t + j))) ω = _
  rw [map_smul, 𝔼.tower hst, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), App. G.9: the kernel forecast is known at date `t`. -/
theorem E_fwd_self {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) {g : ℕ → Ω → ℝ} {M : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ M) (t : ℕ) : 𝔼.E t (fwd 𝔼 w g t) = fwd 𝔼 w g t := by
  funext ω
  rw [E_fwd 𝔼 hw hg le_rfl]
  rfl

/-- Woodford (2003), (3.22)–(3.26), p. 595 and p. 601: the kernel forecast of a bounded process
is bounded, `|∑ w_j E_t g_{t+j}| ≤ (∑ |w_j|) M`. -/
theorem abs_fwd_le {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) {g : ℕ → Ω → ℝ} {M : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |fwd 𝔼 w g t ω| ≤ (∑' j, |w j|) * M := by
  have hb : ∀ j, |w j * 𝔼.E t (g (t + j)) ω| ≤ |w j| * M := fun j => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hg (t + j)) t ω) (abs_nonneg _)
  have hs : Summable (fun j => w j * 𝔼.E t (g (t + j)) ω) :=
    summable_mul_of_abs hw (fun j => 𝔼.abs_E_le (hg (t + j)) t ω)
  have hg' : Summable (fun j => |w j| * M) := hw.mul_right M
  have hup : ∑' j, w j * 𝔼.E t (g (t + j)) ω ≤ ∑' j, |w j| * M :=
    Summable.tsum_le_tsum (fun j => (le_abs_self _).trans (hb j)) hs hg'
  have hlo : -∑' j, |w j| * M ≤ ∑' j, w j * 𝔼.E t (g (t + j)) ω := by
    rw [← tsum_neg]
    refine Summable.tsum_le_tsum (fun j => ?_) hg'.neg hs
    have h1 := neg_abs_le (w j * 𝔼.E t (g (t + j)) ω)
    have h2 := hb j
    linarith
  rw [← tsum_mul_right]
  change |∑' j, w j * 𝔼.E t (g (t + j)) ω| ≤ _
  exact abs_le.mpr ⟨hlo, hup⟩

/-- Woodford (2003), App. G.9: the kernel forecast of a bounded process is a bounded process. -/
theorem fwd_bounded {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) {g : ℕ → Ω → ℝ}
    (hg : BoundedProc g) : BoundedProc (fwd 𝔼 w g) := by
  obtain ⟨M, hM⟩ := hg
  exact ⟨(∑' j, |w j|) * M, fun t ω => abs_fwd_le 𝔼 hw hM t ω⟩

/-- Woodford (2003), App. G.9 (the double forward inverse solves its defining second-order
relation): if `w_1 = a w_0` and `w_{j+2} = a w_{j+1} + b w_j`, then for bounded adapted `g`,
`Φ_t = w_0 g_t + a E_t Φ_{t+1} + b E_t Φ_{t+2}` where `Φ_t = ∑ w_j E_t g_{t+j}`. -/
theorem fwd_rec {a b : ℝ} {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) (hw1 : w 1 = a * w 0)
    (hrec : ∀ j, w (j + 2) = a * w (j + 1) + b * w j) {g : ℕ → Ω → ℝ} {M : ℝ}
    (hg : ∀ t ω, |g t ω| ≤ M) (hga : 𝔼.Adapted g) (t : ℕ) :
    fwd 𝔼 w g t = w 0 • g t + a • 𝔼.E t (fwd 𝔼 w g (t + 1)) + b • 𝔼.E t (fwd 𝔼 w g (t + 2)) := by
  funext ω
  have key := tsum_rec2_identity hw hw1 hrec (G := fun k => 𝔼.E t (g (t + k)) ω)
    (fun k => 𝔼.abs_E_le (hg (t + k)) t ω)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [E_fwd 𝔼 hw hg (Nat.le_succ t), E_fwd 𝔼 hw hg (by omega : t ≤ t + 2)]
  change ∑' j, w j * 𝔼.E t (g (t + j)) ω = _
  have q1 : ∑' j, w j * 𝔼.E t (g (t + (j + 1))) ω = ∑' j, w j * 𝔼.E t (g (t + 1 + j)) ω :=
    tsum_congr fun j => by rw [show t + (j + 1) = t + 1 + j by omega]
  have q2 : ∑' j, w j * 𝔼.E t (g (t + (j + 2))) ω = ∑' j, w j * 𝔼.E t (g (t + 2 + j)) ω :=
    tsum_congr fun j => by rw [show t + (j + 2) = t + 2 + j by omega]
  rw [key, q1, q2, add_zero, hga t]

/-! ### The model: (3.18)–(3.19) and the Euler equation (3.21) -/

/-- Woodford (2003), eq. (3.19), p. 593: `q̃_t = (κσ/λᵢ)[π_t − γπ_{t−1} + (λₓ/κ)Δx_t]`
(with `π_t^{qd} = π_t − γπ_{t−1}` as in (2.8)). Variables are deviations from steady state. -/
noncomputable def qtilde (γ κ σ lx li : ℝ) (infl x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (κ * σ / li) • (infl t - γ • infl (t - 1) + (lx / κ) • (x t - x (t - 1)))

/-- Woodford (2003), eq. (3.18), p. 593: `f̂_t = q̃_t − βγ E_t q̃_{t+1}`. -/
noncomputable def fhat (β γ κ σ lx li : ℝ) (infl x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  qtilde γ κ σ lx li infl x t - (β * γ) • 𝔼.E t (qtilde γ κ σ lx li infl x (t + 1))

/-- Woodford (2003), App. G.8, p. 731: the expansion
`E_t f̂_{t+k} = (κσ/λᵢ) E_t[−γπ_{t+k−1} + (1 + βγ²)π_{t+k} − βγπ_{t+k+1}]
 + (λₓσ/λᵢ) E_t[−x_{t+k−1} + (1 + βγ)x_{t+k} − βγx_{t+k+1}]` (stated at date `t = n + 1`). -/
theorem E_fhat_expand {β γ κ σ lx li : ℝ} (hκ : κ ≠ 0) (infl x : ℕ → Ω → ℝ) (n k : ℕ)
    (ω : Ω) :
    𝔼.E (n + 1) (fhat 𝔼 β γ κ σ lx li infl x (n + 1 + k)) ω =
      κ * σ / li * (-γ * 𝔼.E (n + 1) (infl (n + k)) ω +
        (1 + β * γ ^ 2) * 𝔼.E (n + 1) (infl (n + (k + 1))) ω +
          -(β * γ) * 𝔼.E (n + 1) (infl (n + (k + 2))) ω) +
      lx * σ / li * (-1 * 𝔼.E (n + 1) (x (n + k)) ω +
        (1 + β * γ) * 𝔼.E (n + 1) (x (n + (k + 1))) ω +
          -(β * γ) * 𝔼.E (n + 1) (x (n + (k + 2))) ω) := by
  have e1 : n + 1 + k - 1 = n + k := by omega
  have e2 : n + 1 + k = n + (k + 1) := by omega
  have e3 : n + 1 + k + 1 - 1 = n + (k + 1) := by omega
  have e4 : n + 1 + k + 1 = n + (k + 2) := by omega
  have ht : n + 1 ≤ n + (k + 1) := by omega
  unfold fhat qtilde
  rw [e1, e3, e4, e2]
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    𝔼.tower ht]
  field_simp
  ring

/-- Woodford (2003), eq. (3.21), p. 594 (the Euler equation (3.16) in deviations, with `A(L)` as
in (3.17)): `βγ E_t ı̂_{t+1} − (1 + γ + βγ) ı̂_t + (1 + γ + β⁻¹(1 + κσ)) ı̂_{t−1} − β⁻¹ ı̂_{t−2}
= −f̂_t`, i.e. `E_t[A(L) ı̂_{t+1}] = −f̂_t`. -/
def Euler (β γ κ σ : ℝ) (i f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  (β * γ) • 𝔼.E t (i (t + 1)) - (1 + γ + β * γ) • i t + (1 + γ + (1 + κ * σ) / β) • i (t - 1) -
    β⁻¹ • i (t - 2) = -f t

/-- Woodford (2003), eq. (3.26), p. 601 (and (G.49)): the pure targeting rule
`(1 − λ₁L) ı̂_{t−1} = −(βγλ₂λ₃)⁻¹ E_t[(1 − λ₂⁻¹L⁻¹)⁻¹(1 − λ₃⁻¹L⁻¹)⁻¹ f̂_t]`, with the double forward
inverse written through its real kernel `K_j` (`s = λ₂ + λ₃`, `p = λ₂λ₃`). -/
def TargetRule (β γ l1 s p : ℝ) (i f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i (t - 1) - l1 • i (t - 2) = -(β * γ * p)⁻¹ • fwd 𝔼 (Kker s p) f t

/-! ### Proposition 8.10: the pure targeting rule is equivalent to the Euler equation -/

/-- Woodford (2003), App. G.9, p. 738: the Euler equation in factored form,
`E_t[A(L)ı̂_{t+1}] = βγ E_t[(1 − λ₂L)(1 − λ₃L) h_{t+1}]` with `h_t = ı̂_t − λ₁ı̂_{t−1}`. -/
theorem InertiaRoots.euler_lhs_factored (h : InertiaRoots β γ κ σ l1 l2 l3) (a0 a1 a2 a3 : ℝ) :
    β * γ * a3 - (1 + γ + β * γ) * a2 + (1 + γ + (1 + κ * σ) / β) * a1 - β⁻¹ * a0 =
      β * γ * ((a3 - l1 * a2) - sR l2 l3 * (a2 - l1 * a1) + pR l2 l3 * (a1 - l1 * a0)) := by
  linear_combination a2 * h.vieta1_real - a1 * h.vieta2_real + a0 * h.vieta3_real

/-- Woodford (2003), App. G.9 (uniqueness step in the proof of Proposition 8.10): if a bounded
process satisfies `d_t = (s/p) E_t d_{t+1} − p⁻¹ E_t d_{t+2}` for all `t ≥ t₀` and the kernel
`K_j` tends to zero, then `d_t = 0` for all `t ≥ t₀`. Iterating gives
`d_t = K_{n+1} E_t d_{t+n+1} − p⁻¹ K_n E_t d_{t+n+2}`. -/
theorem homog_eq_zero {s p : ℝ} (hK : Tendsto (Kker s p) atTop (𝓝 0)) {d : ℕ → Ω → ℝ}
    (hd : BoundedProc d) {t0 : ℕ}
    (heq : ∀ m, t0 ≤ m → d m = (s / p) • 𝔼.E m (d (m + 1)) + (-1 / p) • 𝔼.E m (d (m + 2))) :
    ∀ m, t0 ≤ m → d m = 0 := by
  obtain ⟨M, hM⟩ := hd
  intro m hm
  have iter : ∀ n, d m = Kker s p (n + 1) • 𝔼.E m (d (m + n + 1)) +
      ((-1 / p) * Kker s p n) • 𝔼.E m (d (m + n + 2)) := by
    intro n
    induction n with
    | zero =>
      rw [heq m hm]
      simp [Kker, rec2]
    | succ n ih =>
      have hstep := congrArg (𝔼.E m) (heq (m + n + 1) (by omega))
      rw [map_add, map_smul, map_smul, 𝔼.tower (by omega : m ≤ m + n + 1),
        𝔼.tower (by omega : m ≤ m + n + 1)] at hstep
      rw [show m + (n + 1) + 1 = m + n + 1 + 1 by omega,
        show m + (n + 1) + 2 = m + n + 1 + 2 by omega, ih,
        show m + n + 2 = m + n + 1 + 1 by omega, hstep]
      have hK2 : Kker s p (n + 1 + 1) = s / p * Kker s p (n + 1) + -1 / p * Kker s p n := rfl
      rw [hK2]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  funext ω
  have hb : ∀ n, |d m ω| ≤ |Kker s p (n + 1)| * M + |-1 / p| * |Kker s p n| * M := by
    intro n
    rw [iter n]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul]
    gcongr
    · exact 𝔼.abs_E_le (hM _) m ω
    · exact 𝔼.abs_E_le (hM _) m ω
  have hlim : Tendsto (fun n => |Kker s p (n + 1)| * M + |-1 / p| * |Kker s p n| * M) atTop
      (𝓝 (|0| * M + |-1 / p| * |0| * M)) := by
    have h1 : Tendsto (fun n => Kker s p (n + 1)) atTop (𝓝 0) :=
      hK.comp (tendsto_add_atTop_nat 1)
    exact ((h1.abs.mul_const M).add ((hK.abs.const_mul _).mul_const M))
  simp only [abs_zero, zero_mul, mul_zero, add_zero] at hlim
  have : |d m ω| ≤ 0 := ge_of_tendsto' hlim hb
  exact abs_nonpos_iff.mp this

/-- Woodford (2003), (G.49)–(G.50): the forward sum `Φ_t = ∑ K_j E_t f̂_{t+j}` satisfies
`Φ_t = f̂_t + (s/p) E_t Φ_{t+1} − p⁻¹ E_t Φ_{t+2}`. -/
theorem InertiaRoots.fwd_Kker_rec (h : InertiaRoots β γ κ σ l1 l2 l3) {f : ℕ → Ω → ℝ} {M : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) (t : ℕ) :
    fwd 𝔼 (Kker (sR l2 l3) (pR l2 l3)) f t =
      f t + (sR l2 l3 / pR l2 l3) • 𝔼.E t (fwd 𝔼 (Kker (sR l2 l3) (pR l2 l3)) f (t + 1)) +
        (-1 / pR l2 l3) • 𝔼.E t (fwd 𝔼 (Kker (sR l2 l3) (pR l2 l3)) f (t + 2)) := by
  have := fwd_rec 𝔼 h.summable_abs_Kker (a := sR l2 l3 / pR l2 l3) (b := -1 / pR l2 l3)
    (by simp [Kker, rec2]) (fun j => rfl) hf hfa t
  rw [this]
  simp [Kker, rec2]

/-- **Proposition 8.10** (Woodford (2003), p. 601; proof App. G.9, pp. 737–739). Under the
assumptions of Proposition 8.7 (supplied as `InertiaRoots`), a pair of bounded adapted
processes `{ı̂_t, f̂_t}` satisfies the pure targeting rule (3.26) at all dates `t ≥ t₀` if and
only if it satisfies the Euler equation (3.21) at all those dates. The roots `λ₂, λ₃` may be a
complex pair: the double forward inverse has the real kernel `K_j` (`Kker_eq_cauchy`). -/
theorem prop_8_10 (hβ : 0 < β) (hγ : 0 < γ) (h : InertiaRoots β γ κ σ l1 l2 l3)
    {i f : ℕ → Ω → ℝ} (hib : BoundedProc i) (hia : 𝔼.Adapted i) (hfb : BoundedProc f)
    (hfa : 𝔼.Adapted f) {t0 : ℕ} (ht0 : 2 ≤ t0) :
    (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ i f t) ↔
      (∀ t, t0 ≤ t → TargetRule 𝔼 β γ l1 (sR l2 l3) (pR l2 l3) i f t) := by
  set s := sR l2 l3 with hs
  set p := pR l2 l3 with hp'
  obtain ⟨Mf, hMf⟩ := hfb
  have hp : p ≠ 0 := by linarith [h.one_lt_p]
  have hβγ : β * γ ≠ 0 := (mul_pos hβ hγ).ne'
  set c := (β * γ * p)⁻¹ with hc
  set Φ := fwd 𝔼 (Kker s p) f with hΦ
  have hrec : ∀ n ω, Φ (n + 2) ω = f (n + 2) ω + s / p * 𝔼.E (n + 2) (Φ (n + 3)) ω +
      -1 / p * 𝔼.E (n + 2) (Φ (n + 4)) ω := by
    intro n ω
    have := congrFun (h.fwd_Kker_rec 𝔼 hMf hfa (n + 2)) ω
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hEi : ∀ m k, k ≤ m → 𝔼.E m (i k) = i k := fun m k hk =>
    ForwardSolution.E_of_known 𝔼 hk (hia k)
  -- the Euler equation in factored form, at date `n + 2`
  have hEul : ∀ n, Euler 𝔼 β γ κ σ i f (n + 2) ↔
      ∀ ω, β * γ * ((𝔼.E (n + 2) (i (n + 3)) ω - l1 * i (n + 2) ω) -
        s * (i (n + 2) ω - l1 * i (n + 1) ω) + p * (i (n + 1) ω - l1 * i n ω)) =
          -f (n + 2) ω := by
    intro n
    unfold Euler
    rw [funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      show n + 2 + 1 = n + 3 by omega, show n + 2 - 1 = n + 1 by omega,
      show n + 2 - 2 = n by omega]
    rw [h.euler_lhs_factored]
  -- the target rule at date `n + 2`, pointwise
  have hTR : ∀ n, TargetRule 𝔼 β γ l1 s p i f (n + 2) ↔
      ∀ ω, i (n + 1) ω - l1 * i n ω = -c * Φ (n + 2) ω := by
    intro n
    unfold TargetRule
    rw [funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, show n + 2 - 1 = n + 1 by omega,
      show n + 2 - 2 = n by omega, hΦ, hc]
  constructor
  · intro hE
    -- `d_m = h_{m−1} + c Φ_m` solves the homogeneous equation
    set d : ℕ → Ω → ℝ := fun m => (i (m - 1) - l1 • i (m - 2)) + c • Φ m with hd
    have hdb : BoundedProc d := by
      obtain ⟨Mi, hMi⟩ := hib
      obtain ⟨MΦ, hMΦ⟩ := fwd_bounded 𝔼 h.summable_abs_Kker ⟨Mf, hMf⟩
      refine ⟨Mi + |l1| * Mi + |c| * MΦ, fun t ω => ?_⟩
      simp only [hd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans ?_
      have := abs_sub (i (t - 1) ω) (l1 * i (t - 2) ω)
      rw [abs_mul] at this ⊢
      have h1 := hMi (t - 1) ω
      have h2 := mul_le_mul_of_nonneg_left (hMi (t - 2) ω) (abs_nonneg l1)
      have h3 := mul_le_mul_of_nonneg_left (hMΦ t ω) (abs_nonneg c)
      linarith
    have hdeq : ∀ m, t0 ≤ m → d m = (s / p) • 𝔼.E m (d (m + 1)) +
        (-1 / p) • 𝔼.E m (d (m + 2)) := by
      intro m hm
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
      have hEn := (hEul n).mp (hE (n + 2) hm)
      funext ω
      have e1 := hEn ω
      have e2 := hrec n ω
      simp only [hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_smul,
        Pi.sub_apply, show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega,
        show n + 2 + 1 - 1 = n + 2 by omega, show n + 2 + 1 - 2 = n + 1 by omega,
        show n + 2 + 2 - 1 = n + 3 by omega, show n + 2 + 2 - 2 = n + 2 by omega,
        show n + 2 + 1 = n + 3 by omega, show n + 2 + 2 = n + 4 by omega,
        hEi (n + 2) (n + 1) (by omega), hEi (n + 2) (n + 2) le_rfl]
      have key : i (n + 1) ω - l1 * i n ω + c * Φ (n + 2) ω -
          (s / p * (i (n + 2) ω - l1 * i (n + 1) ω + c * 𝔼.E (n + 2) (Φ (n + 3)) ω) +
            -1 / p * (𝔼.E (n + 2) (i (n + 3)) ω - l1 * i (n + 2) ω +
              c * 𝔼.E (n + 2) (Φ (n + 4)) ω)) =
          (p⁻¹ * (β * γ)⁻¹) * (β * γ * ((𝔼.E (n + 2) (i (n + 3)) ω - l1 * i (n + 2) ω) -
            s * (i (n + 2) ω - l1 * i (n + 1) ω) + p * (i (n + 1) ω - l1 * i n ω)) +
              f (n + 2) ω) +
          c * (Φ (n + 2) ω - (f (n + 2) ω + s / p * 𝔼.E (n + 2) (Φ (n + 3)) ω +
            -1 / p * 𝔼.E (n + 2) (Φ (n + 4)) ω)) := by
        rw [hc]
        field_simp
        ring
      rw [← sub_eq_zero, key, e1, ← e2]
      ring
    have hd0 := homog_eq_zero 𝔼 (summable_abs_iff.mp h.summable_abs_Kker).tendsto_atTop_zero
      hdb hdeq
    intro t ht
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
    refine (hTR n).mpr fun ω => ?_
    have hω := congrFun (hd0 (n + 2) ht) ω
    simp only [hd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at hω
    linarith
  · intro hT t ht
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
    refine (hEul n).mpr fun ω => ?_
    have t0' := (hTR n).mp (hT (n + 2) ht) ω
    have T1 : i (n + 2) - l1 • i (n + 1) = -(β * γ * p)⁻¹ • fwd 𝔼 (Kker s p) f (n + 3) := by
      have := hT (n + 3) (by omega)
      unfold TargetRule at this
      rw [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] at this
      exact this
    have T2 : i (n + 3) - l1 • i (n + 2) = -(β * γ * p)⁻¹ • fwd 𝔼 (Kker s p) f (n + 4) := by
      have := hT (n + 4) (by omega)
      unfold TargetRule at this
      rw [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega] at this
      exact this
    have t1 := congrFun (congrArg (𝔼.E (n + 2)) T1) ω
    have t2 := congrFun (congrArg (𝔼.E (n + 2)) T2) ω
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hEi (n + 2) (n + 1) (by omega), hEi (n + 2) (n + 2) le_rfl] at t1 t2
    have e2 := hrec n ω
    have : β * γ * ((𝔼.E (n + 2) (i (n + 3)) ω - l1 * i (n + 2) ω) -
        s * (i (n + 2) ω - l1 * i (n + 1) ω) + p * (i (n + 1) ω - l1 * i n ω)) =
        -(β * γ * c) * (𝔼.E (n + 2) (Φ (n + 4)) ω - s * 𝔼.E (n + 2) (Φ (n + 3)) ω +
          p * Φ (n + 2) ω) := by
      rw [t0', t1, t2]
      ring
    rw [this, e2, hc]
    field_simp
    ring


/-! ### Normalized forecast weights `α_{π,j}`, `α_{x,j}` -/

/-- Woodford (2003), (G.33), p. 732, and (G.55), p. 741: the normalizing sum
`S_π = ∑_{j≥0} α̃_{π,j} = (1 − γ)(1 − βγ) ∑_j w_j + γ w_0` for a kernel `w`. -/
noncomputable def SpiK (β γ : ℝ) (w : ℕ → ℝ) : ℝ := (1 - γ) * (1 - β * γ) * ∑' j, w j + γ * w 0

/-- Woodford (2003), (G.27)–(G.29) and (G.33), pp. 732: the inflation-forecast weights
`α_{π,j} = α̃_{π,j}/S_π`, `α̃_{π,j} = −βγ w_{j−1} + (1 + βγ²) w_j − γ w_{j+1}`. -/
noncomputable def alphaPi (β γ : ℝ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  conv3 (-γ) (1 + β * γ ^ 2) (-(β * γ)) w j / SpiK β γ w

/-- Woodford (2003), (G.30)–(G.32), p. 732: the output-gap-forecast weights
`α_{x,j} = (−βγ w_{j−1} + (1 + βγ) w_j − w_{j+1})/w_0`. -/
noncomputable def alphaX (β γ : ℝ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  conv3 (-1) (1 + β * γ) (-(β * γ)) w j / w 0

/-- Woodford (2003), p. 732: the inflation-forecast weights sum to one, `∑_j α_{π,j} = 1`. -/
theorem hasSum_alphaPi {β γ : ℝ} {w : ℕ → ℝ} {W : ℝ} (hw : HasSum w W)
    (hS : SpiK β γ w ≠ 0) : HasSum (alphaPi β γ w) 1 := by
  have h := (hasSum_conv3 hw (-γ) (1 + β * γ ^ 2) (-(β * γ))).div_const (SpiK β γ w)
  have e : ((-γ + (1 + β * γ ^ 2) + -(β * γ)) * W - -γ * w 0) / SpiK β γ w = 1 := by
    rw [div_eq_one_iff_eq hS]
    unfold SpiK
    rw [hw.tsum_eq]
    ring
  rw [e] at h
  exact h

/-- Woodford (2003), p. 733: the output-gap-forecast weights sum to one, `∑_j α_{x,j} = 1`. -/
theorem hasSum_alphaX {β γ : ℝ} {w : ℕ → ℝ} {W : ℝ} (hw : HasSum w W) (hw0 : w 0 ≠ 0) :
    HasSum (alphaX β γ w) 1 := by
  have h := (hasSum_conv3 hw (-1) (1 + β * γ) (-(β * γ))).div_const (w 0)
  have e : ((-1 + (1 + β * γ) + -(β * γ)) * W - -1 * w 0) / w 0 = 1 := by
    rw [div_eq_one_iff_eq hw0]
    ring
  rw [e] at h
  exact h

/-- Woodford (2003), App. G.8: the weights `α_{π,j}` are absolutely summable. -/
theorem summable_abs_alphaPi {β γ : ℝ} {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) :
    Summable (fun j => |alphaPi β γ w j|) := by
  refine ((summable_abs_conv3 hw (-γ) (1 + β * γ ^ 2) (-(β * γ))).div_const
    |SpiK β γ w|).congr fun j => ?_
  unfold alphaPi
  rw [abs_div]

/-- Woodford (2003), App. G.8: the weights `α_{x,j}` are absolutely summable. -/
theorem summable_abs_alphaX {β γ : ℝ} {w : ℕ → ℝ} (hw : Summable (fun j => |w j|)) :
    Summable (fun j => |alphaX β γ w j|) := by
  refine ((summable_abs_conv3 hw (-1) (1 + β * γ) (-(β * γ))).div_const |w 0|).congr fun j => ?_
  unfold alphaX
  rw [abs_div]

/-- Woodford (2003), App. G.8: a bound for the three-term expression,
`|a Y_j + b Y_{j+1} + c Y_{j+2}| ≤ (|a| + |b| + |c|) M`. -/
theorem abs_three_le {Y : ℕ → ℝ} {M : ℝ} (hY : ∀ k, |Y k| ≤ M) (a b c : ℝ) (j : ℕ) :
    |a * Y j + b * Y (j + 1) + c * Y (j + 2)| ≤ (|a| + |b| + |c|) * M := by
  calc |a * Y j + b * Y (j + 1) + c * Y (j + 2)|
      ≤ |a * Y j| + |b * Y (j + 1)| + |c * Y (j + 2)| := abs_add_three _ _ _
    _ = |a| * |Y j| + |b| * |Y (j + 1)| + |c| * |Y (j + 2)| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |a| * M + |b| * M + |c| * M := by
        gcongr
        · exact hY j
        · exact hY (j + 1)
        · exact hY (j + 2)
    _ = (|a| + |b| + |c|) * M := by ring

/-- Woodford (2003), (G.33), p. 732 (and (G.43), (G.54)): for any absolutely summable kernel `w`,
`∑_j w_j E_t f̂_{t+j} = (κσ/λᵢ)[S_π F_t(π̂) − γ w_0 π̂_{t−1}]
+ (λₓσ/λᵢ)[w_0 F_t(x̂) − w_0 x̂_{t−1}]` with `F_t(z) = ∑_j α_{z,j} E_t z_{t+j}`
(stated at date `t = n + 1`). -/
theorem fwd_fhat {β γ κ σ lx li : ℝ} (hκ : κ ≠ 0) {w : ℕ → ℝ} (hw : Summable (fun j => |w j|))
    (hS : SpiK β γ w ≠ 0) (hw0 : w 0 ≠ 0) {infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl)
    (hπa : 𝔼.Adapted infl) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) (n : ℕ) :
    fwd 𝔼 w (fhat 𝔼 β γ κ σ lx li infl x) (n + 1) =
      (κ * σ / li) • (SpiK β γ w • fwd 𝔼 (alphaPi β γ w) infl (n + 1) - (γ * w 0) • infl n) +
        (lx * σ / li) • (w 0 • fwd 𝔼 (alphaX β γ w) x (n + 1) - w 0 • x n) := by
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  funext ω
  set Yπ : ℕ → ℝ := fun m => 𝔼.E (n + 1) (infl (n + m)) ω with hYπ
  set Yx : ℕ → ℝ := fun m => 𝔼.E (n + 1) (x (n + m)) ω with hYx
  have bπ : ∀ k, |Yπ k| ≤ Mπ := fun k => 𝔼.abs_E_le (hMπ _) _ ω
  have bx : ∀ k, |Yx k| ≤ Mx := fun k => 𝔼.abs_E_le (hMx _) _ ω
  have sπ := summable_mul_of_abs hw (abs_three_le bπ (-γ) (1 + β * γ ^ 2) (-(β * γ)))
  have sx := summable_mul_of_abs hw (abs_three_le bx (-1) (1 + β * γ) (-(β * γ)))
  have hL : fwd 𝔼 w (fhat 𝔼 β γ κ σ lx li infl x) (n + 1) ω =
      κ * σ / li * ∑' j, w j * ((-γ) * Yπ j + (1 + β * γ ^ 2) * Yπ (j + 1) +
          (-(β * γ)) * Yπ (j + 2)) +
        lx * σ / li * ∑' j, w j * (-1 * Yx j + (1 + β * γ) * Yx (j + 1) +
          (-(β * γ)) * Yx (j + 2)) := by
    have H := (sπ.hasSum.mul_left (κ * σ / li)).add (sx.hasSum.mul_left (lx * σ / li))
    rw [← H.tsum_eq]
    change ∑' j, w j * 𝔼.E (n + 1) (fhat 𝔼 β γ κ σ lx li infl x (n + 1 + j)) ω = _
    refine tsum_congr fun j => ?_
    rw [E_fhat_expand 𝔼 hκ infl x n j ω]
    ring
  have h3π := tsum_three_term hw bπ (-γ) (1 + β * γ ^ 2) (-(β * γ))
  have h3x := tsum_three_term hw bx (-1) (1 + β * γ) (-(β * γ))
  have hY0π : Yπ 0 = infl n ω := by
    simp only [hYπ, add_zero]
    rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ n) (hπa n)]
  have hY0x : Yx 0 = x n ω := by
    simp only [hYx, add_zero]
    rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ n) (hxa n)]
  have hFπ : ∑' j, conv3 (-γ) (1 + β * γ ^ 2) (-(β * γ)) w j * Yπ (j + 1) =
      SpiK β γ w * fwd 𝔼 (alphaPi β γ w) infl (n + 1) ω := by
    change _ = SpiK β γ w * ∑' j, alphaPi β γ w j * 𝔼.E (n + 1) (infl (n + 1 + j)) ω
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hYπ, alphaPi, show n + (j + 1) = n + 1 + j by omega]
    field_simp
  have hFx : ∑' j, conv3 (-1) (1 + β * γ) (-(β * γ)) w j * Yx (j + 1) =
      w 0 * fwd 𝔼 (alphaX β γ w) x (n + 1) ω := by
    change _ = w 0 * ∑' j, alphaX β γ w j * 𝔼.E (n + 1) (x (n + 1 + j)) ω
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hYx, alphaX, show n + (j + 1) = n + 1 + j by omega]
    field_simp
  rw [hL, h3π, h3x, hY0π, hY0x, hFπ, hFx]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The instrument rules I, II, III and the representation (3.25) -/

/-- Woodford (2003), eqs. (3.22)–(3.24), p. 595 (and (G.21)–(G.23)): an implicit instrument rule
`(1 − λ₁L)(1 − mL) ı̂_t = c ∑_j w_j E_t f̂_{t+j}`. Rule I: `m = λ₂`, `c = (βγλ₃)⁻¹`,
`w_j = λ₃^{−j}`; Rule II: `λ₂ ↔ λ₃`; Rule III: `m = (λ₂ + λ₃)/2`, `c = (βγ)⁻¹`,
`w_j = ½(λ₂^{−j−1} + λ₃^{−j−1})`. -/
def KernelRule (l1 m coef : ℝ) (w : ℕ → ℝ) (i f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t - (l1 + m) • i (t - 1) + (l1 * m) • i (t - 2) = coef • fwd 𝔼 w f t

/-- Woodford (2003), eq. (3.25), p. 597 and (G.34), p. 733, in deviations from steady state:
`ı̂_t = ρ₁ı̂_{t−1} + ρ₂Δı̂_{t−1} + φ_π F_t(π̂) + (φₓ/4) F_t(x̂) − θ_π π̂_{t−1}
− (θₓ/4) x̂_{t−1}`. -/
def Rep325 (ρ1 ρ2 φπ φx θπ θx : ℝ) (απ αx : ℕ → ℝ) (i infl x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = ρ1 • i (t - 1) + ρ2 • (i (t - 1) - i (t - 2)) + φπ • fwd 𝔼 απ infl t +
    (φx / 4) • fwd 𝔼 αx x t - θπ • infl (t - 1) - (θx / 4) • x (t - 1)

/-- Woodford (2003), (G.26) and (G.39), pp. 731, 735: `ρ₁ = 1 + (m − 1)(1 − λ₁)`. -/
def rho1 (l1 m : ℝ) : ℝ := 1 + (m - 1) * (1 - l1)

/-- Woodford (2003), (G.26) and (G.40): `ρ₂ = λ₁ m`. -/
def rho2 (l1 m : ℝ) : ℝ := l1 * m

/-- Woodford (2003), (G.34) and (G.44): `φ_π = c (κσ/λᵢ) S_π`. -/
noncomputable def phiPi (β γ κ σ li coef : ℝ) (w : ℕ → ℝ) : ℝ := coef * (κ * σ / li) * SpiK β γ w

/-- Woodford (2003), (G.34) and (G.45): `θ_π = c (κσ/λᵢ) γ w_0` (coefficient on `π̂_{t−1}`). -/
noncomputable def thetaPi (γ κ σ li coef : ℝ) (w : ℕ → ℝ) : ℝ := coef * (κ * σ / li) * (γ * w 0)

/-- Woodford (2003), (G.34) and (G.46): `φₓ = 4c(λₓσ/λᵢ) ∑_j α̃_{x,j}`, where `∑ α̃_{x,j} = w_0`
(coefficient on the output-gap forecast). -/
noncomputable def phiX (σ lx li coef : ℝ) (w : ℕ → ℝ) : ℝ := 4 * (coef * (lx * σ / li)) * w 0

/-- Woodford (2003), (G.34) and (G.46): `θₓ = 4c(λₓσ/λᵢ)(−α̃_{x,−1}) w_0`, the coefficient on
`x̂_{t−1}` (with `α̃_{x,−1} = −1`). -/
noncomputable def thetaX (σ lx li coef : ℝ) (w : ℕ → ℝ) : ℝ :=
  4 * (coef * (lx * σ / li)) * (1 * w 0)

/-- Woodford (2003), Proposition 8.9: `θₓ = φₓ` (both arise from
`∑_j α̃_{x,j} = −α̃_{x,−1} w_0`). -/
theorem thetaX_eq_phiX (σ lx li coef : ℝ) (w : ℕ → ℝ) :
    thetaX σ lx li coef w = phiX σ lx li coef w := by
  unfold thetaX phiX
  ring

/-- Woodford (2003), App. G.8 (rewriting (G.26) with (G.33) as (G.34)): any kernel rule of the
form (3.22)–(3.24) is equivalent, date by date, to the representation (3.25) with
`ρ₁ = 1 + (m − 1)(1 − λ₁)`, `ρ₂ = λ₁ m` and the coefficients `phiPi`, `phiX`, `thetaPi`,
`thetaX`. -/
theorem kernelRule_iff_rep {β γ κ σ lx li l1 m coef : ℝ} (hκ : κ ≠ 0) {w : ℕ → ℝ}
    (hw : Summable (fun j => |w j|)) (hS : SpiK β γ w ≠ 0) (hw0 : w 0 ≠ 0)
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) (n : ℕ) :
    KernelRule 𝔼 l1 m coef w i (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Rep325 𝔼 (rho1 l1 m) (rho2 l1 m) (phiPi β γ κ σ li coef w) (phiX σ lx li coef w)
        (thetaPi γ κ σ li coef w) (thetaX σ lx li coef w) (alphaPi β γ w) (alphaX β γ w)
        i infl x (n + 2) := by
  unfold KernelRule Rep325
  rw [fwd_fhat 𝔼 hκ hw hS hw0 hπb hπa hxb hxa (n + 1), funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
  unfold rho1 rho2 phiPi phiX thetaPi thetaX
  constructor <;> intro h <;> linear_combination h

/-- Woodford (2003), Proposition 8.9 and (G.26)/(G.39): `ρ₁ > 1` whenever `m > 1`. -/
theorem one_lt_rho1 {l1 m : ℝ} (hl1 : l1 < 1) (hm : 1 < m) : 1 < rho1 l1 m := by
  unfold rho1
  nlinarith

/-- Woodford (2003), Proposition 8.9 and (G.26)/(G.40): `ρ₂ > 0`. -/
theorem rho2_pos {l1 m : ℝ} (hl1 : 0 < l1) (hm : 0 < m) : 0 < rho2 l1 m := mul_pos hl1 hm

/-- Woodford (2003), (G.26) and (G.39): `ρ₁ + ρ₂ = λ₁ + m` and `ρ₂ = λ₁ m`, so
`(1 − λ₁L)(1 − mL) = 1 − ρ₁L − ρ₂(L − L²)`; also `1 − ρ₁ = (1 − λ₁)(1 − m)`. -/
theorem rho_relations (l1 m : ℝ) :
    rho1 l1 m + rho2 l1 m = l1 + m ∧ 1 - rho1 l1 m = (1 - l1) * (1 - m) := by
  unfold rho1 rho2
  constructor <;> ring

/-- Woodford (2003), Proposition 8.9: sign properties of the coefficients of (3.25) for any kernel
rule with `c > 0`, `w_0 > 0`, `∑ w ≥ 0`, `0 < γ ≤ 1`, `0 < β < 1`, `κ, σ, λₓ, λᵢ > 0`:
`0 < θ_π ≤ φ_π` and `0 < φₓ = θₓ`, with
`φ_π − θ_π = c (κσ/λᵢ)(1 − γ)(1 − βγ) ∑ w ≥ 0` (cf. (G.35), (G.47)). -/
theorem coeff_signs {β γ κ σ lx li coef : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (hc : 0 < coef)
    {w : ℕ → ℝ} (hw0 : 0 < w 0) (hW : 0 ≤ ∑' j, w j) :
    0 < thetaPi γ κ σ li coef w ∧ thetaPi γ κ σ li coef w ≤ phiPi β γ κ σ li coef w ∧
      phiPi β γ κ σ li coef w - thetaPi γ κ σ li coef w =
        coef * (κ * σ / li) * ((1 - γ) * (1 - β * γ) * ∑' j, w j) ∧
      0 < phiX σ lx li coef w ∧ thetaX σ lx li coef w = phiX σ lx li coef w := by
  have hk : 0 < coef * (κ * σ / li) := mul_pos hc (div_pos (mul_pos hκ hσ) hli)
  have hβγ : β * γ ≤ β := by nlinarith
  have hD : 0 ≤ (1 - γ) * (1 - β * γ) * ∑' j, w j :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hW
  have hdiff : phiPi β γ κ σ li coef w - thetaPi γ κ σ li coef w =
      coef * (κ * σ / li) * ((1 - γ) * (1 - β * γ) * ∑' j, w j) := by
    unfold phiPi thetaPi SpiK
    ring
  refine ⟨mul_pos hk (mul_pos hγ0 hw0), ?_, hdiff, ?_, thetaX_eq_phiX σ lx li coef w⟩
  · have := mul_nonneg hk.le hD
    linarith
  · unfold phiX
    exact mul_pos (mul_pos (by norm_num) (mul_pos hc (div_pos (mul_pos hlx hσ) hli))) hw0


/-! ### The representation in levels: constant terms (G.36)–(G.37) -/

/-- Woodford (2003), p. 597 and (G.36): a process in levels, `z_t = z̄ + ẑ_t`. -/
def levelOf (c : ℝ) (y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => c + y t ω

/-- Woodford (2003), eq. (3.25), p. 597 and (G.25), p. 730, in levels:
`i_t = (1 − ρ₁)i* + ρ₁i_{t−1} + ρ₂Δi_{t−1} + φ_π F_t(π) + (φₓ/4)F_t(x) − θ_π π_{t−1}
− (θₓ/4)x_{t−1}`. -/
def Level325 (istar ρ1 ρ2 φπ φx θπ θx : ℝ) (απ αx : ℕ → ℝ) (iL πL xL : ℕ → Ω → ℝ) (t : ℕ) :
    Prop :=
  iL t = (fun _ => (1 - ρ1) * istar) + ρ1 • iL (t - 1) + ρ2 • (iL (t - 1) - iL (t - 2)) +
    φπ • fwd 𝔼 απ πL t + (φx / 4) • fwd 𝔼 αx xL t - θπ • πL (t - 1) - (θx / 4) • xL (t - 1)

/-- Woodford (2003), p. 597: since the weights of `F_t` sum to one, `F_t(z̄ + ẑ) = z̄ + F_t(ẑ)`. -/
theorem fwd_levelOf {α : ℕ → ℝ} (hα : HasSum α 1) (hαs : Summable (fun j => |α j|)) {c : ℝ}
    {y : ℕ → Ω → ℝ} (hy : BoundedProc y) (t : ℕ) (ω : Ω) :
    fwd 𝔼 α (levelOf c y) t ω = c + fwd 𝔼 α y t ω := by
  obtain ⟨M, hM⟩ := hy
  have hs := summable_mul_of_abs hαs (fun j => 𝔼.abs_E_le (hM (t + j)) t ω)
  have hE : ∀ j, 𝔼.E t (levelOf c y (t + j)) ω = c + 𝔼.E t (y (t + j)) ω := fun j => by
    rw [show levelOf c y (t + j) = (fun _ => c) + y (t + j) from rfl, map_add, 𝔼.const]
    rfl
  have H := (hα.mul_right c).add hs.hasSum
  change ∑' j, α j * 𝔼.E t (levelOf c y (t + j)) ω = c + ∑' j, α j * 𝔼.E t (y (t + j)) ω
  rw [one_mul] at H
  rw [← H.tsum_eq]
  exact tsum_congr fun j => by rw [hE j]; ring

/-- Woodford (2003), (G.36)–(G.37), pp. 733–734: given `θₓ = φₓ`, normalized weights and the
steady-state relation `(1 − ρ₁)i* = (1 − ρ₁)ī − (φ_π − θ_π)π̄`, the representation (3.25) in
deviations is equivalent to (3.25) in levels (`i = ī + ı̂`, `π = π̄ + π̂`, `x = x̄ + x̂`). -/
theorem rep325_iff_level {istar ibar pibar xbar ρ1 ρ2 φπ φx θπ θx : ℝ} {απ αx : ℕ → ℝ}
    (hθx : θx = φx) (hαπ : HasSum απ 1) (hαx : HasSum αx 1)
    (hαπs : Summable (fun j => |απ j|)) (hαxs : Summable (fun j => |αx j|))
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hxb : BoundedProc x)
    (hconst : (1 - ρ1) * istar = (1 - ρ1) * ibar - (φπ - θπ) * pibar) (n : ℕ) :
    Rep325 𝔼 ρ1 ρ2 φπ φx θπ θx απ αx i infl x (n + 2) ↔
      Level325 𝔼 istar ρ1 ρ2 φπ φx θπ θx απ αx (levelOf ibar i) (levelOf pibar infl)
        (levelOf xbar x) (n + 2) := by
  unfold Rep325 Level325
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    fwd_levelOf 𝔼 hαπ hαπs hπb, fwd_levelOf 𝔼 hαx hαxs hxb]
  simp only [levelOf, hθx]
  constructor
  · intro h
    linear_combination h - hconst
  · intro h
    linear_combination h + hconst

/-- Woodford (2003), (G.37), p. 734: the steady state of (3.16), `A(1)(ī − i*) = −f̄` with
`A(1) = κσ/β` (`Apoly_one`) and `f̄ = (κσ/λᵢ)(1 − βγ)(1 − γ)π̄`, gives
`(1 − ρ₁)i* = (1 − ρ₁)ī − (φ_π − θ_π)π̄` for any kernel rule whose coefficients satisfy
`(1 − ρ₁)β = −c κσ ∑ w` (checked for each rule below). -/
theorem level_const {β γ κ σ li ρ1 coef ibar istar pibar : ℝ} {w : ℕ → ℝ} (hβ : β ≠ 0)
    (hκσ : κ * σ ≠ 0) (hli : li ≠ 0)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar))
    (hR : (1 - ρ1) * β = -(coef * (κ * σ) * ∑' j, w j)) :
    (1 - ρ1) * istar = (1 - ρ1) * ibar -
      (phiPi β γ κ σ li coef w - thetaPi γ κ σ li coef w) * pibar := by
  have hi : istar = ibar + β / li * (1 - β * γ) * (1 - γ) * pibar := by
    have hk : κ * σ / β ≠ 0 := div_ne_zero hκσ hβ
    have : κ * σ / β * (istar - ibar) = κ * σ / β * (β / li * (1 - β * γ) * (1 - γ) * pibar) := by
      rw [show κ * σ / β * (istar - ibar) = -(κ * σ / β * (ibar - istar)) by ring, hss]
      field_simp
    linarith [mul_left_cancel₀ hk this]
  unfold phiPi thetaPi SpiK
  rw [hi]
  have e : (1 - ρ1) * (β / li * (1 - β * γ) * (1 - γ) * pibar) =
      -(coef * (κ * σ) * ∑' j, w j) / li * (1 - β * γ) * (1 - γ) * pibar := by
    rw [← hR]
    ring
  linear_combination e

/-! ### Proposition 8.9: Rules I and II (three real roots) -/

/-- Woodford (2003), (3.22), p. 595: the geometric kernel starts at `μ⁰ = 1`. -/
theorem geomKer_zero (μ : ℝ) : geomKer μ 0 = 1 := pow_zero μ

/-- Woodford (2003), (G.26): `∑ |μʲ| < ∞` for `0 ≤ μ < 1`. -/
theorem summable_abs_geomKer {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ < 1) :
    Summable (fun j => |geomKer μ j|) := by
  refine (summable_geometric_of_lt_one h0 h1).congr fun j => ?_
  unfold geomKer
  rw [abs_of_nonneg (pow_nonneg h0 j)]

/-- Woodford (2003), p. 732: `∑_j λ^{−j} = (1 − λ⁻¹)⁻¹`. -/
theorem hasSum_geomKer {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ < 1) : HasSum (geomKer μ) (1 - μ)⁻¹ :=
  hasSum_geometric_of_lt_one h0 h1

/-- Woodford (2003), Proposition 8.7: `Re λ₂ > 1`. -/
theorem InertiaRoots.one_lt_re_l2 (h : InertiaRoots β γ κ σ l1 l2 l3) : 1 < l2.re := by
  rcases h.shape with ⟨-, -, h2, -⟩ | ⟨-, hr⟩
  · exact h2
  · exact hr

/-- Woodford (2003), Proposition 8.7: `Re λ₃ > 1`. -/
theorem InertiaRoots.one_lt_re_l3 (h : InertiaRoots β γ κ σ l1 l2 l3) : 1 < l3.re := by
  rcases h.shape with ⟨-, -, -, h3⟩ | ⟨hc, hr⟩
  · exact h3
  · rw [hc, Complex.conj_re]
    exact hr

/-- Woodford (2003), Proposition 8.7 (case of three real roots): real outer roots are both
greater than one, with `s = λ₂ + λ₃`, `p = λ₂λ₃`. -/
theorem InertiaRoots.real_roots {a b : ℝ} (h : InertiaRoots β γ κ σ l1 (a : ℂ) (b : ℂ)) :
    1 < a ∧ 1 < b ∧ sR a b = a + b ∧ pR a b = a * b := by
  have h2 := h.one_lt_re_l2
  have h3 := h.one_lt_re_l3
  simp only [Complex.ofReal_re] at h2 h3
  refine ⟨h2, h3, ?_, ?_⟩
  · simp [sR]
  · simp [pR]

/-- Woodford (2003), Proposition 8.9 for an instrument rule obtained by solving one real root
`λ_b > 1` forward and keeping `λ_a > 1` (Rule I: `a = 2, b = 3`; Rule II: `a = 3, b = 2`):
`(1 − λ₁L)(1 − λ_aL) ı̂_t = (βγλ_b)⁻¹ ∑_j λ_b^{−j} E_t f̂_{t+j}` has the representation (3.25) with
`ρ₁ = 1 + (λ_a − 1)(1 − λ₁) > 1`, `ρ₂ = λ₁λ_a > 0`, `0 < θ_π ≤ φ_π`, `0 < θₓ = φₓ`, and
forecast weights summing to one. -/
theorem rule_real_rep {β γ κ σ lx li l1 la lb : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (hl10 : 0 < l1)
    (hl11 : l1 < 1) (hla : 1 < la) (hlb : 1 < lb) {i infl x : ℕ → Ω → ℝ}
    (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, KernelRule 𝔼 l1 la (β * γ * lb)⁻¹ (geomKer lb⁻¹) i (fhat 𝔼 β γ κ σ lx li infl x)
        (n + 2) ↔
      Rep325 𝔼 (rho1 l1 la) (rho2 l1 la) (phiPi β γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹))
        (phiX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹))
        (thetaPi γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹))
        (thetaX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹)) (alphaPi β γ (geomKer lb⁻¹))
        (alphaX β γ (geomKer lb⁻¹)) i infl x (n + 2)) ∧
    1 < rho1 l1 la ∧ 0 < rho2 l1 la ∧
    0 < thetaPi γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) ∧
    thetaPi γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) ≤
      phiPi β γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) ∧
    0 < phiX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹) ∧
    thetaX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹) = phiX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹) ∧
    HasSum (alphaPi β γ (geomKer lb⁻¹)) 1 ∧ HasSum (alphaX β γ (geomKer lb⁻¹)) 1 := by
  have hμ0 : 0 ≤ lb⁻¹ := inv_nonneg.mpr (by linarith)
  have hμ1 : lb⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlb
  have hW := hasSum_geomKer hμ0 hμ1
  have hWpos : 0 ≤ ∑' j, geomKer lb⁻¹ j := by
    rw [hW.tsum_eq]
    exact inv_nonneg.mpr (by linarith)
  have hc : 0 < (β * γ * lb)⁻¹ := inv_pos.mpr (by positivity)
  have hw0 : 0 < geomKer lb⁻¹ 0 := by rw [geomKer_zero]; norm_num
  have hsg := coeff_signs hβ0 hβ1 hγ0 hγ1 hκ hσ hlx hli hc hw0 hWpos
  have hS : SpiK β γ (geomKer lb⁻¹) ≠ 0 := by
    have : 0 < SpiK β γ (geomKer lb⁻¹) := by
      have hβγ : β * γ ≤ β := by nlinarith
      unfold SpiK
      have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - γ)
        (by linarith : (0 : ℝ) ≤ 1 - β * γ)) hWpos
      nlinarith
    exact this.ne'
  refine ⟨fun n => kernelRule_iff_rep 𝔼 hκ.ne' (summable_abs_geomKer hμ0 hμ1) hS hw0.ne' hπb hπa
    hxb hxa n, one_lt_rho1 hl11 hla, rho2_pos hl10 (by linarith), hsg.1, hsg.2.1, hsg.2.2.2.1,
    hsg.2.2.2.2, hasSum_alphaPi hW hS, hasSum_alphaX hW hw0.ne'⟩

/-- Woodford (2003), (G.34)–(G.35), p. 733: the coefficients of Rule I (with `λ_b = λ₃`) are
`θ_π = κσ/(λᵢβλ₃)`, `φₓ = θₓ = 4λₓσ/(λᵢβγλ₃)`,
`φ_π = (κσ/λᵢ)(1 + βγ² − βγ − λ₃⁻¹γ)/(βλ₃γ(1 − λ₃⁻¹))`, and
`φ_π = θ_π(1 + (1 − γ)(1 − βγ)/(γ(1 − λ₃⁻¹)))`. -/
theorem rule_real_formulas {β γ κ σ lx li lb : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hli : 0 < li)
    (hlb : 1 < lb) :
    thetaPi γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) = κ * σ / (li * β * lb) ∧
    phiX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹) = 4 * lx * σ / (li * β * γ * lb) ∧
    phiPi β γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) =
      κ * σ / li * (1 + β * γ ^ 2 - β * γ - lb⁻¹ * γ) / (β * lb * γ * (1 - lb⁻¹)) ∧
    phiPi β γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) =
      thetaPi γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) *
        (1 + (1 - γ) * (1 - β * γ) / (γ * (1 - lb⁻¹))) := by
  have hμ0 : 0 ≤ lb⁻¹ := inv_nonneg.mpr (by linarith)
  have hμ1 : lb⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlb
  have hW := (hasSum_geomKer hμ0 hμ1).tsum_eq
  have hlb0 : lb ≠ 0 := by positivity
  have h1 : 1 - lb⁻¹ ≠ 0 := by linarith
  have hb : β ≠ 0 := hβ0.ne'
  have hg : γ ≠ 0 := hγ0.ne'
  have hl : li ≠ 0 := hli.ne'
  unfold thetaPi phiX phiPi SpiK
  rw [hW, geomKer_zero]
  generalize lb⁻¹ = μ at h1 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · field_simp
    ring
  · field_simp
    ring

/-- **Proposition 8.9, Rule I** (Woodford (2003), p. 597; proof App. G.8, pp. 730–734). With
three real roots (`λ₂, λ₃` real; by Proposition 8.7 then `λ₂, λ₃ > 1`), Rule I (3.22) has the
representation (3.25) with `ρ₁ = 1 + (λ₂ − 1)(1 − λ₁) > 1`, `ρ₂ = λ₁λ₂ > 0`,
`0 < θ_π ≤ φ_π`, `0 < θₓ = φₓ` and forecast weights summing to one. -/
theorem prop_8_9_ruleI {β γ κ σ lx li l1 l2 l3 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li)
    (h : InertiaRoots β γ κ σ l1 (l2 : ℂ) (l3 : ℂ)) {i infl x : ℕ → Ω → ℝ}
    (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, KernelRule 𝔼 l1 l2 (β * γ * l3)⁻¹ (geomKer l3⁻¹) i (fhat 𝔼 β γ κ σ lx li infl x)
        (n + 2) ↔
      Rep325 𝔼 (rho1 l1 l2) (rho2 l1 l2) (phiPi β γ κ σ li (β * γ * l3)⁻¹ (geomKer l3⁻¹))
        (phiX σ lx li (β * γ * l3)⁻¹ (geomKer l3⁻¹))
        (thetaPi γ κ σ li (β * γ * l3)⁻¹ (geomKer l3⁻¹))
        (thetaX σ lx li (β * γ * l3)⁻¹ (geomKer l3⁻¹)) (alphaPi β γ (geomKer l3⁻¹))
        (alphaX β γ (geomKer l3⁻¹)) i infl x (n + 2)) ∧
    1 < rho1 l1 l2 ∧ 0 < rho2 l1 l2 ∧
    0 < thetaPi γ κ σ li (β * γ * l3)⁻¹ (geomKer l3⁻¹) ∧
    thetaPi γ κ σ li (β * γ * l3)⁻¹ (geomKer l3⁻¹) ≤
      phiPi β γ κ σ li (β * γ * l3)⁻¹ (geomKer l3⁻¹) ∧
    0 < phiX σ lx li (β * γ * l3)⁻¹ (geomKer l3⁻¹) ∧
    thetaX σ lx li (β * γ * l3)⁻¹ (geomKer l3⁻¹) = phiX σ lx li (β * γ * l3)⁻¹ (geomKer l3⁻¹) ∧
    HasSum (alphaPi β γ (geomKer l3⁻¹)) 1 ∧ HasSum (alphaX β γ (geomKer l3⁻¹)) 1 := by
  obtain ⟨h2, h3, -, -⟩ := h.real_roots
  exact rule_real_rep 𝔼 hβ0 hβ1 hγ0 hγ1 hκ hσ hlx hli h.l1_pos h.l1_lt_one h2 h3 hπb hπa hxb hxa

/-- **Proposition 8.9, Rule II** (Woodford (2003), p. 597; App. G.8, pp. 734–735): Rule II (3.23),
`(1 − λ₁L)(1 − λ₃L) ı̂_t = (βγλ₂)⁻¹ ∑_j λ₂^{−j} E_t f̂_{t+j}`, has the representation (3.25) with
`ρ₁ = 1 + (λ₃ − 1)(1 − λ₁) > 1`, `ρ₂ = λ₁λ₃ > 0`, `0 < θ_π ≤ φ_π`, `0 < θₓ = φₓ`. -/
theorem prop_8_9_ruleII {β γ κ σ lx li l1 l2 l3 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li)
    (h : InertiaRoots β γ κ σ l1 (l2 : ℂ) (l3 : ℂ)) {i infl x : ℕ → Ω → ℝ}
    (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl) (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, KernelRule 𝔼 l1 l3 (β * γ * l2)⁻¹ (geomKer l2⁻¹) i (fhat 𝔼 β γ κ σ lx li infl x)
        (n + 2) ↔
      Rep325 𝔼 (rho1 l1 l3) (rho2 l1 l3) (phiPi β γ κ σ li (β * γ * l2)⁻¹ (geomKer l2⁻¹))
        (phiX σ lx li (β * γ * l2)⁻¹ (geomKer l2⁻¹))
        (thetaPi γ κ σ li (β * γ * l2)⁻¹ (geomKer l2⁻¹))
        (thetaX σ lx li (β * γ * l2)⁻¹ (geomKer l2⁻¹)) (alphaPi β γ (geomKer l2⁻¹))
        (alphaX β γ (geomKer l2⁻¹)) i infl x (n + 2)) ∧
    1 < rho1 l1 l3 ∧ 0 < rho2 l1 l3 ∧
    0 < thetaPi γ κ σ li (β * γ * l2)⁻¹ (geomKer l2⁻¹) ∧
    thetaPi γ κ σ li (β * γ * l2)⁻¹ (geomKer l2⁻¹) ≤
      phiPi β γ κ σ li (β * γ * l2)⁻¹ (geomKer l2⁻¹) ∧
    0 < phiX σ lx li (β * γ * l2)⁻¹ (geomKer l2⁻¹) ∧
    thetaX σ lx li (β * γ * l2)⁻¹ (geomKer l2⁻¹) = phiX σ lx li (β * γ * l2)⁻¹ (geomKer l2⁻¹) ∧
    HasSum (alphaPi β γ (geomKer l2⁻¹)) 1 ∧ HasSum (alphaX β γ (geomKer l2⁻¹)) 1 := by
  obtain ⟨h2, h3, -, -⟩ := h.real_roots
  exact rule_real_rep 𝔼 hβ0 hβ1 hγ0 hγ1 hκ hσ hlx hli h.l1_pos h.l1_lt_one h3 h2 hπb hπa hxb hxa

/-- Woodford (2003), (G.36)–(G.37), pp. 733–734: for Rules I and II, the steady-state relation
`A(1)(ī − i*) = −f̄` gives `(1 − ρ₁)i* = (1 − ρ₁)ī − (φ_π − θ_π)π̄`, so (G.34) in deviations is
equivalent to (3.25) in levels. -/
theorem rule_real_const {β γ κ σ li l1 la lb ibar istar pibar : ℝ} (hβ0 : 0 < β)
    (hγ0 : 0 < γ) (hκσ : κ * σ ≠ 0) (hli : li ≠ 0) (hlb : 1 < lb)
    (hA : β * γ * (1 - l1) * ((1 - la) * (1 - lb)) = κ * σ / β)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar)) :
    (1 - rho1 l1 la) * istar = (1 - rho1 l1 la) * ibar -
      (phiPi β γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹) -
        thetaPi γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹)) * pibar := by
  refine level_const hβ0.ne' hκσ hli hss ?_
  have hμ0 : 0 ≤ lb⁻¹ := inv_nonneg.mpr (by linarith)
  have hμ1 : lb⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlb
  rw [(hasSum_geomKer hμ0 hμ1).tsum_eq]
  have hlb0 : lb ≠ 0 := by positivity
  have h1 : 1 - lb⁻¹ ≠ 0 := by linarith
  have h2 : lb - 1 ≠ 0 := by linarith
  have hb : β ≠ 0 := hβ0.ne'
  have hg : γ ≠ 0 := hγ0.ne'
  have hk : κ * σ = β * (β * γ * (1 - l1) * ((1 - la) * (1 - lb))) := by
    rw [hA]
    field_simp
  rw [hk]
  unfold rho1
  field_simp
  ring

/-! ### Proposition 8.9: Rule III (real roots or a complex pair) -/

/-- Woodford (2003), (G.39): `m = (λ₂ + λ₃)/2 = s/2`. -/
theorem InertiaRoots.Pker_one (h : InertiaRoots β γ κ σ l1 l2 l3) :
    ruleIIIker (sR l2 l3) (pR l2 l3) 0 = sR l2 l3 / (2 * pR l2 l3) := by
  have : Pker (sR l2 l3) (pR l2 l3) 1 = sR l2 l3 / pR l2 l3 := rfl
  unfold ruleIIIker
  rw [this]
  have hp : pR l2 l3 ≠ 0 := by linarith [h.one_lt_p]
  field_simp

/-- **Proposition 8.9, Rule III** (Woodford (2003), p. 597; App. G.8, pp. 735–737). For any
roots supplied by Proposition 8.7 (three real roots or a complex pair), Rule III (3.24),
`(1 − λ₁L)(1 − ½(λ₂ + λ₃)L) ı̂_t = ½(βγλ₃)⁻¹E_t∑λ₃^{−j}f̂_{t+j} + ½(βγλ₂)⁻¹E_t∑λ₂^{−j}f̂_{t+j}`
(real kernel `ruleIIIker`, see `ruleIIIker_eq`), has the representation (3.25) with
`ρ₁ = 1 + ((λ₂ + λ₃)/2 − 1)(1 − λ₁) > 1`, `ρ₂ = λ₁(λ₂ + λ₃)/2 > 0`, `0 < θ_π ≤ φ_π`,
`0 < θₓ = φₓ` and forecast weights summing to one. -/
theorem prop_8_9_ruleIII {lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (h : InertiaRoots β γ κ σ l1 l2 l3)
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, KernelRule 𝔼 l1 (sR l2 l3 / 2) (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) i
        (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Rep325 𝔼 (rho1 l1 (sR l2 l3 / 2)) (rho2 l1 (sR l2 l3 / 2))
        (phiPi β γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (phiX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (thetaX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (alphaPi β γ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (alphaX β γ (ruleIIIker (sR l2 l3) (pR l2 l3))) i infl x (n + 2)) ∧
    1 < rho1 l1 (sR l2 l3 / 2) ∧ 0 < rho2 l1 (sR l2 l3 / 2) ∧
    0 < thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) ∧
    thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) ≤
      phiPi β γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) ∧
    0 < phiX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) ∧
    thetaX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) =
      phiX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) ∧
    HasSum (alphaPi β γ (ruleIIIker (sR l2 l3) (pR l2 l3))) 1 ∧
    HasSum (alphaX β γ (ruleIIIker (sR l2 l3) (pR l2 l3))) 1 := by
  have hs2 := h.two_lt_s
  have hp1 := h.one_lt_p
  have hq := h.one_sub_s_add_p_pos
  have hW := h.hasSum_ruleIIIker
  have hWpos : 0 ≤ ∑' j, ruleIIIker (sR l2 l3) (pR l2 l3) j := by
    rw [hW.tsum_eq]
    exact div_nonneg (by linarith) (by linarith)
  have hc : 0 < (β * γ)⁻¹ := inv_pos.mpr (by positivity)
  have hw0 : 0 < ruleIIIker (sR l2 l3) (pR l2 l3) 0 := by
    rw [h.Pker_one]
    exact div_pos (by linarith) (by linarith)
  have hsg := coeff_signs hβ0 hβ1 hγ0 hγ1 hκ hσ hlx hli hc hw0 hWpos
  have hS : SpiK β γ (ruleIIIker (sR l2 l3) (pR l2 l3)) ≠ 0 := by
    have : 0 < SpiK β γ (ruleIIIker (sR l2 l3) (pR l2 l3)) := by
      have hβγ : β * γ ≤ β := by nlinarith
      unfold SpiK
      have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - γ)
        (by linarith : (0 : ℝ) ≤ 1 - β * γ)) hWpos
      nlinarith [mul_pos hγ0 hw0]
    exact this.ne'
  refine ⟨fun n => kernelRule_iff_rep 𝔼 hκ.ne' h.summable_abs_ruleIIIker hS hw0.ne' hπb hπa
    hxb hxa n, one_lt_rho1 h.l1_lt_one (by linarith), rho2_pos h.l1_pos (by linarith), hsg.1,
    hsg.2.1, hsg.2.2.2.1, hsg.2.2.2.2, hasSum_alphaPi hW hS, hasSum_alphaX hW hw0.ne'⟩

/-- Woodford (2003), (G.39)–(G.40) and (G.45)–(G.47), pp. 735–737: the coefficients of Rule III are
`ρ₁ = λ₁ + (λ₂ + λ₃)/2 − λ₁(λ₂ + λ₃)/2`, `θ_π = (κσ/(λᵢβ))(λ₂⁻¹ + λ₃⁻¹)/2`,
`φₓ = θₓ = (4λₓσ/(λᵢβγ))(λ₂⁻¹ + λ₃⁻¹)/2` and
`φ_π = θ_π − κσ(1 − γ)(1 − βγ)(1 − (λ₂ + λ₃)/2)/(λᵢβγ(1 − λ₂)(1 − λ₃))`
(with `λ₂⁻¹ + λ₃⁻¹ = s/p` and `(1 − λ₂)(1 − λ₃) = 1 − s + p`). -/
theorem InertiaRoots.ruleIII_formulas {lx li : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hli : 0 < li)
    (h : InertiaRoots β γ κ σ l1 l2 l3) :
    rho1 l1 (sR l2 l3 / 2) = l1 + sR l2 l3 / 2 - l1 * (sR l2 l3 / 2) ∧
    thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) =
      κ * σ / (li * β) * (sR l2 l3 / pR l2 l3 / 2) ∧
    phiX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) =
      4 * lx * σ / (li * β * γ) * (sR l2 l3 / pR l2 l3 / 2) ∧
    phiPi β γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) =
      thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) -
        κ * σ * (1 - γ) * (1 - β * γ) * (1 - sR l2 l3 / 2) /
          (li * β * γ * (1 - sR l2 l3 + pR l2 l3)) := by
  have hp : pR l2 l3 ≠ 0 := by linarith [h.one_lt_p]
  have hq : 1 - sR l2 l3 + pR l2 l3 ≠ 0 := h.one_sub_s_add_p_pos.ne'
  have hb : β ≠ 0 := hβ0.ne'
  have hg : γ ≠ 0 := hγ0.ne'
  have hl : li ≠ 0 := hli.ne'
  unfold rho1 thetaPi phiX phiPi SpiK
  rw [h.hasSum_ruleIIIker.tsum_eq, h.Pker_one]
  refine ⟨by ring, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · field_simp
    ring

/-- Woodford (2003), (G.48), p. 737: for Rule III the steady-state relation gives
`(1 − ρ₁)i* = (1 − ρ₁)ī − (φ_π − θ_π)π̄`, so (G.43) in deviations is equivalent to (3.25) in
levels. -/
theorem InertiaRoots.ruleIII_const {li ibar istar pibar : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hκσ : κ * σ ≠ 0) (hli : li ≠ 0) (h : InertiaRoots β γ κ σ l1 l2 l3)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar)) :
    (1 - rho1 l1 (sR l2 l3 / 2)) * istar = (1 - rho1 l1 (sR l2 l3 / 2)) * ibar -
      (phiPi β γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) -
        thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3))) * pibar := by
  refine level_const hβ0.ne' hκσ hli hss ?_
  rw [h.hasSum_ruleIIIker.tsum_eq]
  have hq : 1 - sR l2 l3 + pR l2 l3 ≠ 0 := h.one_sub_s_add_p_pos.ne'
  have hb : β ≠ 0 := hβ0.ne'
  have hg : γ ≠ 0 := hγ0.ne'
  have hk : κ * σ = β * (β * γ * (1 - l1) * (1 - sR l2 l3 + pR l2 l3)) := by
    rw [h.A_one_real hb]
    field_simp
  rw [hk]
  unfold rho1
  field_simp
  ring


/-! ### Proposition 8.11: the optimal target criterion (3.27) -/

/-- Woodford (2003), eq. (3.27), p. 601 and (G.52), in deviations from steady state:
`F_t(π̂) + (φₓ/4)F_t(x̂) = θ_π π̂_{t−1} + (θₓ/4)x̂_{t−1} − θᵢ ı̂_{t−1} − θ_Δ Δı̂_{t−1}`. -/
def Rep327 (φx θπ θx θi θΔ : ℝ) (απ αx : ℕ → ℝ) (i infl x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  fwd 𝔼 απ infl t + (φx / 4) • fwd 𝔼 αx x t =
    θπ • infl (t - 1) + (θx / 4) • x (t - 1) - θi • i (t - 1) - θΔ • (i (t - 1) - i (t - 2))

/-- Woodford (2003), (G.56), p. 742: `φₓ = 4λₓ/(κS_π)`. -/
noncomputable def phiX327 (β γ κ lx s p : ℝ) : ℝ := 4 * lx / (κ * SpiK β γ (Kker s p))

/-- Woodford (2003), (G.56): `θₓ = 4(λₓ/κ)/S_π` (the coefficient on `x̂_{t−1}`). -/
noncomputable def thetaX327 (β γ κ lx s p : ℝ) : ℝ := 4 * (lx / κ) / SpiK β γ (Kker s p)

/-- Woodford (2003), (G.56): `θ_π = γ/S_π`. -/
noncomputable def thetaPi327 (β γ s p : ℝ) : ℝ := γ / SpiK β γ (Kker s p)

/-- Woodford (2003), (G.56): `θᵢ = λᵢβγ(1 − λ₁)λ₂λ₃/(κσS_π)`. -/
noncomputable def thetaI327 (β γ κ σ li l1 s p : ℝ) : ℝ :=
  li * β * γ * (1 - l1) * p / (κ * σ * SpiK β γ (Kker s p))

/-- Woodford (2003), (G.56): `θ_Δ = λᵢβγλ₁λ₂λ₃/(κσS_π)`. -/
noncomputable def thetaD327 (β γ κ σ li l1 s p : ℝ) : ℝ :=
  li * β * γ * l1 * p / (κ * σ * SpiK β γ (Kker s p))

/-- Woodford (2003), (G.55), p. 741: `S_π = γ + (1 − γ)(1 − βγ)/((1 − λ₂⁻¹)(1 − λ₃⁻¹))
= γ + (1 − γ)(1 − βγ) p/(1 − s + p)`. -/
theorem InertiaRoots.SpiK_Kker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    SpiK β γ (Kker (sR l2 l3) (pR l2 l3)) =
      γ + (1 - γ) * (1 - β * γ) * (pR l2 l3 / (1 - sR l2 l3 + pR l2 l3)) := by
  unfold SpiK
  rw [h.hasSum_Kker.tsum_eq]
  have : Kker (sR l2 l3) (pR l2 l3) 0 = 1 := rfl
  rw [this]
  ring

/-- Woodford (2003), (G.55): in terms of the roots, `p/(1 − s + p) = ((1 − λ₂⁻¹)(1 − λ₃⁻¹))⁻¹`. -/
theorem InertiaRoots.p_div_eq (h : InertiaRoots β γ κ σ l1 l2 l3) :
    ((pR l2 l3 / (1 - sR l2 l3 + pR l2 l3) : ℝ) : ℂ) = ((1 - l2⁻¹) * (1 - l3⁻¹))⁻¹ := by
  have h2 := h.l2_ne_zero
  have h3 := h.l3_ne_zero
  have hq : ((1 - sR l2 l3 + pR l2 l3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.one_sub_s_add_p_pos.ne'
  push_cast at hq ⊢
  rw [h.coe_s, h.coe_p] at hq ⊢
  rw [eq_comm, inv_eq_iff_eq_inv, inv_div]
  field_simp
  ring

/-- Woodford (2003), (G.55), p. 741 (distinct roots `λ₂ ≠ λ₃`): the printed partial-fraction form
`S_π = λ₃(1 + βγ² − βγ − λ₂⁻¹γ)/((λ₃ − λ₂)(1 − λ₂⁻¹))
− λ₂(1 + βγ² − βγ − λ₃⁻¹γ)/((λ₃ − λ₂)(1 − λ₃⁻¹))`
agrees with `γ + (1 − γ)(1 − βγ)/((1 − λ₂⁻¹)(1 − λ₃⁻¹))`. -/
theorem InertiaRoots.SpiK_partial_fractions (h : InertiaRoots β γ κ σ l1 l2 l3) (h23 : l2 ≠ l3) :
    ((SpiK β γ (Kker (sR l2 l3) (pR l2 l3)) : ℝ) : ℂ) =
      l3 * (1 + β * γ ^ 2 - β * γ - l2⁻¹ * γ) / ((l3 - l2) * (1 - l2⁻¹)) -
        l2 * (1 + β * γ ^ 2 - β * γ - l3⁻¹ * γ) / ((l3 - l2) * (1 - l3⁻¹)) := by
  have h2 := h.l2_ne_zero
  have h3 := h.l3_ne_zero
  have hsub : l3 - l2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
  have h2' : 1 - l2⁻¹ ≠ 0 := by
    intro h0
    have : l2 = 1 := by
      have := sub_eq_zero.mp h0
      rw [eq_comm, inv_eq_one] at this
      exact this
    have := h.one_lt_norm_l2
    rw [‹l2 = 1›, norm_one] at this
    exact lt_irrefl _ this
  have h3' : 1 - l3⁻¹ ≠ 0 := by
    intro h0
    have : l3 = 1 := by
      have := sub_eq_zero.mp h0
      rw [eq_comm, inv_eq_one] at this
      exact this
    have := h.one_lt_norm_l3
    rw [‹l3 = 1›, norm_one] at this
    exact lt_irrefl _ this
  have e : ((pR l2 l3 : ℝ) : ℂ) / (1 - (sR l2 l3 : ℝ) + (pR l2 l3 : ℝ)) =
      ((1 - l2⁻¹) * (1 - l3⁻¹))⁻¹ := by
    have := h.p_div_eq
    push_cast at this
    exact this
  have n2 : l2 - 1 ≠ 0 := fun h0 => h2' (by
    rw [show l2 = 1 by linear_combination h0, inv_one, sub_self])
  have n3 : l3 - 1 ≠ 0 := fun h0 => h3' (by
    rw [show l3 = 1 by linear_combination h0, inv_one, sub_self])
  have n23 : (l2 - 1) * (l3 - 1) ≠ 0 := mul_ne_zero n2 n3
  have e2 : ((1 - l2⁻¹) * (1 - l3⁻¹))⁻¹ = l2 * l3 / ((l2 - 1) * (l3 - 1)) := by
    rw [inv_eq_iff_eq_inv, inv_div]
    field_simp
  have e3 : l3 * (1 + β * γ ^ 2 - β * γ - l2⁻¹ * γ) / ((l3 - l2) * (1 - l2⁻¹)) =
      l3 * (l2 * (1 + β * γ ^ 2 - β * γ) - γ) / ((l3 - l2) * (l2 - 1)) := by
    field_simp
  have e4 : l2 * (1 + β * γ ^ 2 - β * γ - l3⁻¹ * γ) / ((l3 - l2) * (1 - l3⁻¹)) =
      l2 * (l3 * (1 + β * γ ^ 2 - β * γ) - γ) / ((l3 - l2) * (l3 - 1)) := by
    field_simp
  rw [h.SpiK_Kker]
  push_cast
  rw [e, e2, e3, e4, div_sub_div _ _ (mul_ne_zero hsub n2) (mul_ne_zero hsub n3),
    eq_div_iff (mul_ne_zero (mul_ne_zero hsub n2) (mul_ne_zero hsub n3))]
  field_simp
  ring

/-- Woodford (2003), (G.53)–(G.54), p. 740 (distinct roots): `K_j = c₂λ₂^{−j} − c₃λ₃^{−j}` with
`c₂ = λ₃/(λ₃ − λ₂)`, `c₃ = λ₂/(λ₃ − λ₂)`. -/
theorem InertiaRoots.Kker_partial_fractions (h : InertiaRoots β γ κ σ l1 l2 l3) (h23 : l2 ≠ l3)
    (j : ℕ) : ((Kker (sR l2 l3) (pR l2 l3) j : ℝ) : ℂ) =
      l3 / (l3 - l2) * l2⁻¹ ^ j - l2 / (l3 - l2) * l3⁻¹ ^ j := by
  rw [h.Kker_eq_cauchy]
  exact cauchyK_partial_fractions h.l2_ne_zero h.l3_ne_zero h23 j

/-- Woodford (2003), App. G.10, pp. 743–745 (repeated root `λ₂ = λ₃ = λ`): `K_j = (1 + j)λ^{−j}`,
`∑_j K_j = (1 − λ⁻¹)^{−2}` and `S_π = γ + (1 − γ)(1 − βγ)/(1 − λ⁻¹)²`. -/
theorem InertiaRoots.repeated_root (h : InertiaRoots β γ κ σ l1 l2 l2) :
    (∀ j, ((Kker (sR l2 l2) (pR l2 l2) j : ℝ) : ℂ) = ((j : ℂ) + 1) * l2⁻¹ ^ j) ∧
    HasSum (fun j : ℕ => ((j : ℂ) + 1) * l2⁻¹ ^ j) ((1 - l2⁻¹)⁻¹ ^ 2) ∧
    ((SpiK β γ (Kker (sR l2 l2) (pR l2 l2)) : ℝ) : ℂ) =
      γ + (1 - γ) * (1 - β * γ) * ((1 - l2⁻¹)⁻¹ ^ 2) := by
  refine ⟨fun j => by rw [h.Kker_eq_cauchy, cauchyK_repeated], ?_, ?_⟩
  · refine hasSum_one_add_mul_geometric ?_
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ h.one_lt_norm_l2
  · have e : ((pR l2 l2 : ℝ) : ℂ) / (1 - (sR l2 l2 : ℝ) + (pR l2 l2 : ℝ)) =
        ((1 - l2⁻¹) * (1 - l2⁻¹))⁻¹ := by
      have := h.p_div_eq
      push_cast at this
      exact this
    rw [h.SpiK_Kker]
    push_cast
    rw [e, mul_inv]
    ring

/-- Woodford (2003), App. G.10: with `0 < γ ≤ 1`, `0 < β < 1`, `S_π ≥ γ > 0`. -/
theorem InertiaRoots.SpiK_Kker_ge (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (h : InertiaRoots β γ κ σ l1 l2 l3) :
    γ ≤ SpiK β γ (Kker (sR l2 l3) (pR l2 l3)) ∧ 0 < SpiK β γ (Kker (sR l2 l3) (pR l2 l3)) := by
  rw [h.SpiK_Kker]
  have hq := h.one_sub_s_add_p_pos
  have hp := h.one_lt_p
  have hβγ : β * γ ≤ β := by nlinarith
  have : 0 ≤ (1 - γ) * (1 - β * γ) * (pR l2 l3 / (1 - sR l2 l3 + pR l2 l3)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) hq.le)
  constructor <;> linarith

/-- **Proposition 8.11** (Woodford (2003), p. 602; proof App. G.10, pp. 739–745). Under the
assumptions of Proposition 8.9 (roots from Proposition 8.7, possibly a complex pair or a
repeated root), the optimal target criterion (3.26) is equivalent, date by date, to the
representation (3.27) with forecast weights summing to one, and
`φₓ = θₓ > 0`, `0 < θ_π ≤ 1`, `θᵢ > 0`, `θ_Δ > 0`. -/
theorem prop_8_11 {lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (h : InertiaRoots β γ κ σ l1 l2 l3)
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) :
    (∀ n, TargetRule 𝔼 β γ l1 (sR l2 l3) (pR l2 l3) i (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Rep327 𝔼 (phiX327 β γ κ lx (sR l2 l3) (pR l2 l3)) (thetaPi327 β γ (sR l2 l3) (pR l2 l3))
        (thetaX327 β γ κ lx (sR l2 l3) (pR l2 l3)) (thetaI327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3))
        (thetaD327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3))
        (alphaPi β γ (Kker (sR l2 l3) (pR l2 l3))) (alphaX β γ (Kker (sR l2 l3) (pR l2 l3)))
        i infl x (n + 2)) ∧
    thetaX327 β γ κ lx (sR l2 l3) (pR l2 l3) = phiX327 β γ κ lx (sR l2 l3) (pR l2 l3) ∧
    0 < phiX327 β γ κ lx (sR l2 l3) (pR l2 l3) ∧
    0 < thetaPi327 β γ (sR l2 l3) (pR l2 l3) ∧ thetaPi327 β γ (sR l2 l3) (pR l2 l3) ≤ 1 ∧
    0 < thetaI327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3) ∧
    0 < thetaD327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3) ∧
    HasSum (alphaPi β γ (Kker (sR l2 l3) (pR l2 l3))) 1 ∧
    HasSum (alphaX β γ (Kker (sR l2 l3) (pR l2 l3))) 1 := by
  obtain ⟨hSge, hSpos⟩ := h.SpiK_Kker_ge hβ0 hβ1 hγ0 hγ1
  set S := SpiK β γ (Kker (sR l2 l3) (pR l2 l3)) with hSdef
  have hp := h.one_lt_p
  have hK0 : Kker (sR l2 l3) (pR l2 l3) 0 = 1 := rfl
  have hw0 : Kker (sR l2 l3) (pR l2 l3) 0 ≠ 0 := by rw [hK0]; norm_num
  have hb : β ≠ 0 := hβ0.ne'
  have hg : γ ≠ 0 := hγ0.ne'
  have hk : κ ≠ 0 := hκ.ne'
  have hs : σ ≠ 0 := hσ.ne'
  have hl : li ≠ 0 := hli.ne'
  have hp0 : pR l2 l3 ≠ 0 := by linarith
  have hS0 : S ≠ 0 := hSpos.ne'
  refine ⟨fun n => ?_, ?_, ?_, ?_, ?_, ?_, ?_, hasSum_alphaPi h.hasSum_Kker hS0,
    hasSum_alphaX h.hasSum_Kker hw0⟩
  · unfold TargetRule Rep327
    rw [show n + 2 = n + 1 + 1 by omega, fwd_fhat 𝔼 hk h.summable_abs_Kker hS0 hw0 hπb hπa hxb
      hxa (n + 1), funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hK0,
      show n + 1 + 1 - 1 = n + 1 by omega, show n + 1 + 1 - 2 = n by omega]
    unfold phiX327 thetaPi327 thetaX327 thetaI327 thetaD327
    rw [← hSdef]
    set Fπ := fwd 𝔼 (alphaPi β γ (Kker (sR l2 l3) (pR l2 l3))) infl (n + 1 + 1) ω
    set Fx := fwd 𝔼 (alphaX β γ (Kker (sR l2 l3) (pR l2 l3))) x (n + 1 + 1) ω
    set D := li * β * γ * pR l2 l3 / (κ * σ * S)
    have hD : D ≠ 0 := by positivity
    have key : Fπ + 4 * lx / (κ * S) / 4 * Fx -
        (γ / S * infl (n + 1) ω + 4 * (lx / κ) / S / 4 * x (n + 1) ω -
          li * β * γ * (1 - l1) * pR l2 l3 / (κ * σ * S) * i (n + 1) ω -
          li * β * γ * l1 * pR l2 l3 / (κ * σ * S) * (i (n + 1) ω - i n ω)) =
        D * ((i (n + 1) ω - l1 * i n ω) - -(β * γ * pR l2 l3)⁻¹ *
          (κ * σ / li * (S * Fπ - γ * 1 * infl (n + 1) ω) +
            lx * σ / li * (1 * Fx - 1 * x (n + 1) ω))) := by
      simp only [D]
      field_simp
      ring
    constructor
    · intro h1
      rw [← sub_eq_zero, key, h1, sub_self, mul_zero]
    · intro h1
      rw [← sub_eq_zero] at h1 ⊢
      rw [key] at h1
      exact (mul_eq_zero.mp h1).resolve_left hD
  · unfold thetaX327 phiX327
    field_simp
  · unfold phiX327
    rw [← hSdef]
    positivity
  · unfold thetaPi327
    rw [← hSdef]
    positivity
  · unfold thetaPi327
    rw [← hSdef, div_le_one hSpos]
    exact hSge
  · unfold thetaI327
    rw [← hSdef]
    have := h.l1_lt_one
    have : 0 < 1 - l1 := by linarith
    positivity
  · unfold thetaD327
    rw [← hSdef]
    have := h.l1_pos
    positivity

/-- Woodford (2003), eq. (3.27), p. 601 and (G.52), p. 739, in levels:
`F_t(π) + (φₓ/4)F_t(x) = θ_π π_{t−1} + (θₓ/4)x_{t−1} − θᵢ(i_{t−1} − i*) − θ_Δ Δi_{t−1}`. -/
def Level327 (istar φx θπ θx θi θΔ : ℝ) (απ αx : ℕ → ℝ) (iL πL xL : ℕ → Ω → ℝ) (t : ℕ) :
    Prop :=
  fwd 𝔼 απ πL t + (φx / 4) • fwd 𝔼 αx xL t =
    θπ • πL (t - 1) + (θx / 4) • xL (t - 1) - θi • (iL (t - 1) - fun _ => istar) -
      θΔ • (iL (t - 1) - iL (t - 2))

/-- Woodford (2003), (G.56) and p. 743: given `θₓ = φₓ`, normalized weights and the steady-state
relation `θᵢi* = θᵢī + (1 − θ_π)π̄`, (3.27) in deviations is equivalent to (3.27) in levels. -/
theorem rep327_iff_level {istar ibar pibar xbar φx θπ θx θi θΔ : ℝ} {απ αx : ℕ → ℝ}
    (hθx : θx = φx) (hαπ : HasSum απ 1) (hαx : HasSum αx 1)
    (hαπs : Summable (fun j => |απ j|)) (hαxs : Summable (fun j => |αx j|))
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hxb : BoundedProc x)
    (hconst : θi * istar = θi * ibar + (1 - θπ) * pibar) (n : ℕ) :
    Rep327 𝔼 φx θπ θx θi θΔ απ αx i infl x (n + 2) ↔
      Level327 𝔼 istar φx θπ θx θi θΔ απ αx (levelOf ibar i) (levelOf pibar infl)
        (levelOf xbar x) (n + 2) := by
  unfold Rep327 Level327
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    fwd_levelOf 𝔼 hαπ hαπs hπb, fwd_levelOf 𝔼 hαx hαxs hxb]
  simp only [levelOf, hθx]
  constructor
  · intro h
    linear_combination h - hconst
  · intro h
    linear_combination h + hconst

/-- Woodford (2003), pp. 742–743: the steady state of (3.16), `A(1)(ī − i*) = −f̄`, gives
`θᵢ i* = θᵢ ī + (1 − θ_π) π̄` for the coefficients of (3.27). -/
theorem InertiaRoots.target_const {li ibar istar pibar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hκσ : κ * σ ≠ 0) (hli : li ≠ 0)
    (h : InertiaRoots β γ κ σ l1 l2 l3)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar)) :
    thetaI327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3) * istar =
      thetaI327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3) * ibar +
        (1 - thetaPi327 β γ (sR l2 l3) (pR l2 l3)) * pibar := by
  have hb : β ≠ 0 := hβ0.ne'
  have hi : istar = ibar + β / li * (1 - β * γ) * (1 - γ) * pibar := by
    have hk : κ * σ / β ≠ 0 := div_ne_zero hκσ hb
    have : κ * σ / β * (istar - ibar) = κ * σ / β * (β / li * (1 - β * γ) * (1 - γ) * pibar) := by
      rw [show κ * σ / β * (istar - ibar) = -(κ * σ / β * (ibar - istar)) by ring, hss]
      field_simp
    linarith [mul_left_cancel₀ hk this]
  obtain ⟨-, hSpos⟩ := h.SpiK_Kker_ge hβ0 hβ1 hγ0 hγ1
  have hS0 := hSpos.ne'
  have hS := h.SpiK_Kker
  have hq : 1 - sR l2 l3 + pR l2 l3 ≠ 0 := h.one_sub_s_add_p_pos.ne'
  have hg : γ ≠ 0 := hγ0.ne'
  have hk : κ * σ = β * (β * γ * (1 - l1) * (1 - sR l2 l3 + pR l2 l3)) := by
    rw [h.A_one_real hb]
    field_simp
  unfold thetaI327 thetaPi327
  set S := SpiK β γ (Kker (sR l2 l3) (pR l2 l3))
  rw [hi, hk]
  have hl1 : 1 - l1 ≠ 0 := by linarith [h.l1_lt_one]
  field_simp
  rw [hS]
  field_simp
  ring


/-! ### Limits of the roots as `γ → 0` (Lemma G.2) and `γ → 1` -/

/-- Woodford (2003), (G.17)–(G.18), p. 724: the characteristic polynomial
`χ_γ(λ) = λ³A(λ⁻¹) = βγλ³ − (1 + γ + βγ)λ² + (1 + γ + β⁻¹(1 + κσ))λ − β⁻¹`, whose roots are
`λ₁, λ₂, λ₃`. -/
noncomputable def chi (β γ κ σ lam : ℝ) : ℝ :=
  β * γ * lam ^ 3 - (1 + γ + β * γ) * lam ^ 2 + (1 + γ + (1 + κ * σ) / β) * lam - β⁻¹

/-- Woodford (2003), (G.18): `χ_γ(λ) = βγ(λ − λ₁)(λ − λ₂)(λ − λ₃)` for real `λ`. -/
theorem InertiaRoots.chi_factor (h : InertiaRoots β γ κ σ l1 l2 l3) (lam : ℝ) :
    ((chi β γ κ σ lam : ℝ) : ℂ) = β * γ * (lam - l1) * (lam - l2) * (lam - l3) := by
  have hc : ((β⁻¹ : ℝ) : ℂ) = (β : ℂ)⁻¹ := Complex.ofReal_inv β
  unfold chi
  push_cast
  linear_combination (lam : ℂ) ^ 2 * h.vieta1 - (lam : ℂ) * h.vieta2 + h.vieta3 + hc

/-- Woodford (2003), Proposition 8.7: `λ₁` is a root of `χ_γ`. -/
theorem InertiaRoots.chi_l1 (h : InertiaRoots β γ κ σ l1 l2 l3) : chi β γ κ σ l1 = 0 := by
  have := h.chi_factor l1
  rw [sub_self, mul_zero, zero_mul, zero_mul] at this
  exact_mod_cast this

/-- Woodford (2003), Lemma G.2, p. 720: `χ_γ(λ) − χ_{γ'}(λ) = (γ − γ')(βλ³ − (1 + β)λ² + λ)`. -/
theorem chi_sub (β γ γ' κ σ lam : ℝ) :
    chi β γ κ σ lam - chi β γ' κ σ lam = (γ - γ') * (β * lam ^ 3 - (1 + β) * lam ^ 2 + lam) := by
  unfold chi
  ring

/-- Woodford (2003), Lemma G.2: for `0 ≤ λ ≤ R`, `|βλ³ − (1 + β)λ² + λ| ≤ βR³ + (1 + β)R² + R`. -/
theorem abs_cubic_le {β lam R : ℝ} (hβ : 0 ≤ β) (h0 : 0 ≤ lam) (hR : lam ≤ R) :
    |β * lam ^ 3 - (1 + β) * lam ^ 2 + lam| ≤ β * R ^ 3 + (1 + β) * R ^ 2 + R := by
  have h3 : lam ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ h0 hR 3
  have h2 : lam ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 hR 2
  have p3 : 0 ≤ lam ^ 3 := pow_nonneg h0 3
  have p2 : 0 ≤ lam ^ 2 := pow_nonneg h0 2
  rw [abs_le]
  constructor <;> nlinarith

/-- Woodford (2003), Lemma G.2: if `|f γ − a| ≤ Cγ` for `γ ∈ (0, γ₀)`, then `f γ → a` as
`γ → 0⁺`. -/
theorem tendsto_nhdsGT_of_bound {f : ℝ → ℝ} {a C γ0 : ℝ} (hγ0 : 0 < γ0)
    (hb : ∀ γ ∈ Set.Ioo 0 γ0, |f γ - a| ≤ C * γ) : Tendsto f (𝓝[>] 0) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hC : Tendsto (fun γ : ℝ => C * γ) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun γ : ℝ => C * γ) (𝓝 0) (𝓝 (C * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hC
  filter_upwards [Ioo_mem_nhdsGT hγ0] with γ hγ
  rw [Real.norm_eq_abs]
  exact hb γ hγ

/-- Woodford (2003), Proposition 8.9/8.11 (`γ → 1`): if `|f γ − a| ≤ C(1 − γ)` for
`γ ∈ (γ₁, 1)`, then `f γ → a` as `γ → 1⁻`. -/
theorem tendsto_nhdsLT_of_bound {f : ℝ → ℝ} {a C γ1 : ℝ} (hγ1 : γ1 < 1)
    (hb : ∀ γ ∈ Set.Ioo γ1 1, |f γ - a| ≤ C * (1 - γ)) : Tendsto f (𝓝[<] 1) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hC : Tendsto (fun γ : ℝ => C * (1 - γ)) (𝓝[<] 1) (𝓝 0) := by
    have : Tendsto (fun γ : ℝ => C * (1 - γ)) (𝓝 1) (𝓝 (C * (1 - 1))) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).tendsto 1
    rw [sub_self, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hC
  filter_upwards [Ioo_mem_nhdsLT hγ1] with γ hγ
  rw [Real.norm_eq_abs]
  exact hb γ hγ

/-- Woodford (2003), (3.10), p. 588, and Lemma G.2: the roots `λ₁⁰ < λ₂⁰` of the `γ = 0` quadratic
`β − (1 + β + κσ)L + L²` (in inverse form: `λ₁⁰ + λ₂⁰ = 1 + β⁻¹(1 + κσ)`, `λ₁⁰λ₂⁰ = β⁻¹`) satisfy
`0 < λ₁⁰ < 1 < λ₂⁰`. -/
theorem roots_zero_location {β κ σ m1 m2 : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    (hm1 : m1 + m2 = 1 + (1 + κ * σ) / β) (hm2 : m1 * m2 = β⁻¹) (hm12 : m1 < m2) :
    0 < m1 ∧ m1 < 1 ∧ 1 < m2 := by
  have hprod : (1 - m1) * (1 - m2) = -(κ * σ / β) := by
    have : (1 - m1) * (1 - m2) = 1 - (m1 + m2) + m1 * m2 := by ring
    rw [this, hm1, hm2]
    field_simp
    ring
  have hneg : (1 - m1) * (1 - m2) < 0 := by
    rw [hprod]
    have : 0 < κ * σ / β := by positivity
    linarith
  have h1 : m1 < 1 ∧ 1 < m2 := by
    rcases lt_or_ge m1 1 with h | h
    · refine ⟨h, ?_⟩
      by_contra hc
      push Not at hc
      nlinarith
    · nlinarith
  refine ⟨?_, h1⟩
  have : 0 < m1 * m2 := by rw [hm2]; positivity
  by_contra hc
  push Not at hc
  nlinarith

/-- Woodford (2003), (3.10) and Lemma G.2: the `γ = 0` characteristic polynomial factors as
`χ_0(λ) = −(λ − λ₁⁰)(λ − λ₂⁰)`. -/
theorem chi_zero_factor {β κ σ m1 m2 : ℝ}
    (hm1 : m1 + m2 = 1 + (1 + κ * σ) / β) (hm2 : m1 * m2 = β⁻¹) (lam : ℝ) :
    chi β 0 κ σ lam = -((lam - m1) * (lam - m2)) := by
  unfold chi
  have : (lam - m1) * (lam - m2) = lam ^ 2 - (m1 + m2) * lam + m1 * m2 := by ring
  rw [this, hm1, hm2]
  ring

/-- **Lemma G.2, corrected and proved** (Woodford (2003), p. 720; cf. Proposition 8.7 and
footnote 44, p. 596). Suppose that for `γ ∈ (0, γ₀)`, `γ₀ ≤ 1`, the roots are real (Proposition
8.7 guarantees this for small `γ`) with `λ₂ ≤ λ₃`. Then as `γ → 0⁺`: `γλ₃ → β⁻¹`,
`λ₃⁻¹ → 0`, and `λ₁ → λ₁⁰`, `λ₂ → λ₂⁰`, the roots of the `γ = 0` quadratic (3.10). The
printed proof assumes that `λ₁, λ₂` stay bounded; here this is proved (`λ₂ < 2(2 + β⁻¹(1 + κσ))`)
from the Vieta relations. -/
theorem lemma_G2 {β κ σ γ0 m1 m2 : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    (hγ0 : 0 < γ0) (hγ01 : γ0 ≤ 1) {L1 L2 L3 : ℝ → ℝ}
    (hR : ∀ γ ∈ Set.Ioo 0 γ0, InertiaRoots β γ κ σ (L1 γ) (L2 γ : ℂ) (L3 γ : ℂ))
    (hord : ∀ γ ∈ Set.Ioo 0 γ0, L2 γ ≤ L3 γ)
    (hm1 : m1 + m2 = 1 + (1 + κ * σ) / β) (hm2 : m1 * m2 = β⁻¹) (hm12 : m1 < m2) :
    Tendsto (fun γ => γ * L3 γ) (𝓝[>] 0) (𝓝 β⁻¹) ∧
      Tendsto (fun γ => (L3 γ)⁻¹) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto L1 (𝓝[>] 0) (𝓝 m1) ∧ Tendsto L2 (𝓝[>] 0) (𝓝 m2) := by
  obtain ⟨hm10, hm11, hm21⟩ := roots_zero_location hβ0 hκ hσ hm1 hm2 hm12
  set B := 2 + (1 + κ * σ) / β with hB
  have hB0 : 0 < B := by positivity
  -- facts at each `γ ∈ (0, γ₀)`
  have facts : ∀ γ ∈ Set.Ioo 0 γ0, 0 < L1 γ ∧ L1 γ < 1 ∧ 1 < L2 γ ∧ L2 γ < 2 * B ∧
      β * γ * (L1 γ + (L2 γ + L3 γ)) = 1 + γ + β * γ := by
    intro γ hγ
    have h := hR γ hγ
    obtain ⟨h2, h3, hs, hp⟩ := h.real_roots
    have v1 := h.vieta1_real
    have v2 := h.vieta2_real
    rw [hs] at v1 v2
    rw [hp] at v2
    have hl0 := h.l1_pos
    have hl1 := h.l1_lt_one
    have hγ' : 0 < γ := hγ.1
    have hγ1 : γ ≤ 1 := by linarith [hγ.2]
    have hbg : 0 < β * γ := mul_pos hβ0 hγ'
    have hpos : 0 < β * γ * (L1 γ * (L2 γ + L3 γ)) := by positivity
    have hab : β * γ * (L2 γ * L3 γ) ≤ B := by
      have : 1 + γ + (1 + κ * σ) / β ≤ B := by rw [hB]; linarith
      nlinarith
    have hsum : 1 < β * γ * (L2 γ + L3 γ) := by
      have : β * γ * L1 γ < β * γ := by nlinarith
      nlinarith
    have hb3 : 1 / 2 < β * γ * L3 γ := by nlinarith [hord γ hγ]
    have hl2 : L2 γ < 2 * B := by nlinarith
    exact ⟨hl0, hl1, h2, hl2, v1⟩
  have hl3 : Tendsto (fun γ => γ * L3 γ) (𝓝[>] 0) (𝓝 β⁻¹) := by
    refine tendsto_nhdsGT_of_bound (C := β⁻¹ + 1 + 1 + 2 * B) hγ0 fun γ hγ => ?_
    obtain ⟨hl0, hl1, h2, hl2, v1⟩ := facts γ hγ
    have hγ' : 0 < γ := hγ.1
    have e : γ * L3 γ - β⁻¹ = γ * β⁻¹ + γ - γ * (L1 γ + L2 γ) := by
      field_simp
      linear_combination v1
    rw [e]
    have hb' : 0 < β⁻¹ := inv_pos.mpr hβ0
    rw [abs_le]
    constructor <;> nlinarith
  have hγ : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun γ => (L3 γ)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have := hγ.div hl3 (inv_ne_zero hβ0.ne')
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hγ0] with γ hγ'
    have hγp : 0 < γ := hγ'.1
    have hL3 : L3 γ ≠ 0 := by linarith [(hR γ hγ').real_roots.2.1]
    rw [Pi.div_apply]
    field_simp
  refine ⟨hl3, hinv, ?_, ?_⟩
  · refine tendsto_nhdsGT_of_bound (C := (β + (1 + β) + 1) / (m2 - 1)) hγ0 fun γ hγ => ?_
    obtain ⟨hl0, hl1, -, -, -⟩ := facts γ hγ
    have hc := (hR γ hγ).chi_l1
    have hd := chi_sub β γ 0 κ σ (L1 γ)
    rw [hc, chi_zero_factor hm1 hm2, sub_zero] at hd
    have hcub := abs_cubic_le hβ0.le hl0.le hl1.le
    simp only [one_pow, mul_one] at hcub
    have hprod : |L1 γ - m1| * |L1 γ - m2| ≤ γ * (β + (1 + β) + 1) := by
      rw [← abs_mul]
      have hd' : (L1 γ - m1) * (L1 γ - m2) =
          γ * (β * L1 γ ^ 3 - (1 + β) * L1 γ ^ 2 + L1 γ) := by linarith [hd]
      have : |(L1 γ - m1) * (L1 γ - m2)| = γ * |β * L1 γ ^ 3 - (1 + β) * L1 γ ^ 2 + L1 γ| := by
        rw [hd', abs_mul, abs_of_pos hγ.1]
      rw [this]
      exact mul_le_mul_of_nonneg_left hcub hγ.1.le
    have hm2' : m2 - 1 ≤ |L1 γ - m2| := by
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    have hm2p : 0 < m2 - 1 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hm2p]
    nlinarith [abs_nonneg (L1 γ - m1)]
  · set R := 2 * B
    refine tendsto_nhdsGT_of_bound (C := (β * R ^ 3 + (1 + β) * R ^ 2 + R) / (1 - m1)) hγ0
      fun γ hγ => ?_
    obtain ⟨-, -, h2, hl2, -⟩ := facts γ hγ
    have hc := (hR γ hγ).real_roots
    have hc' : chi β γ κ σ (L2 γ) = 0 := by
      have := (hR γ hγ).chi_factor (L2 γ)
      rw [sub_self, mul_zero, zero_mul] at this
      exact_mod_cast this
    have hd := chi_sub β γ 0 κ σ (L2 γ)
    rw [hc', chi_zero_factor hm1 hm2, sub_zero] at hd
    have hcub := abs_cubic_le hβ0.le (by linarith : (0 : ℝ) ≤ L2 γ) hl2.le
    have hprod : |L2 γ - m1| * |L2 γ - m2| ≤ γ * (β * R ^ 3 + (1 + β) * R ^ 2 + R) := by
      rw [← abs_mul]
      have hd' : (L2 γ - m1) * (L2 γ - m2) =
          γ * (β * L2 γ ^ 3 - (1 + β) * L2 γ ^ 2 + L2 γ) := by linarith [hd]
      have : |(L2 γ - m1) * (L2 γ - m2)| = γ * |β * L2 γ ^ 3 - (1 + β) * L2 γ ^ 2 + L2 γ| := by
        rw [hd', abs_mul, abs_of_pos hγ.1]
      rw [this]
      exact mul_le_mul_of_nonneg_left hcub hγ.1.le
    have hm1' : 1 - m1 ≤ |L2 γ - m1| := by
      rw [abs_of_pos (by linarith)]
      linarith
    have hm1p : 0 < 1 - m1 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hm1p]
    nlinarith [abs_nonneg (L2 γ - m2)]

/-- Woodford (2003), Proposition 8.7 (continuity of the stable root, used for the `γ → 1` limits
of Propositions 8.9 and 8.11): if roots exist for every `γ ∈ (γ₁, 1]`, then `λ₁(γ) → λ₁(1)` as
`γ → 1⁻`, with the explicit bound
`|λ₁(γ) − λ₁(1)| ≤ (2 + 2β)(1 − γ)/(β(|λ₂(1)| − 1)(|λ₃(1)| − 1))`. -/
theorem l1_tendsto_one {β κ σ γ1 : ℝ} (hβ0 : 0 < β) (hγ1 : γ1 < 1) {L1 : ℝ → ℝ}
    {L2 L3 : ℝ → ℂ} (hR : ∀ γ ∈ Set.Ioc γ1 1, InertiaRoots β γ κ σ (L1 γ) (L2 γ) (L3 γ)) :
    Tendsto L1 (𝓝[<] 1) (𝓝 (L1 1)) := by
  have h1 := hR 1 ⟨hγ1, le_rfl⟩
  set d2 := ‖L2 1‖ - 1
  set d3 := ‖L3 1‖ - 1
  have hd2 : 0 < d2 := by linarith [h1.one_lt_norm_l2]
  have hd3 : 0 < d3 := by linarith [h1.one_lt_norm_l3]
  refine tendsto_nhdsLT_of_bound (C := (2 + 2 * β) / (β * d2 * d3)) hγ1 fun γ hγ => ?_
  have h := hR γ ⟨hγ.1, hγ.2.le⟩
  set lam := L1 γ
  have hl0 := h.l1_pos
  have hl1 := h.l1_lt_one
  have hc := h.chi_l1
  have hd := chi_sub β 1 γ κ σ lam
  rw [hc, sub_zero] at hd
  have hcub := abs_cubic_le hβ0.le hl0.le hl1.le
  simp only [one_pow, mul_one] at hcub
  have hup : |chi β 1 κ σ lam| ≤ (1 - γ) * (2 + 2 * β) := by
    rw [hd, abs_mul, abs_of_pos (by linarith [hγ.2] : (0 : ℝ) < 1 - γ)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith [hγ.2])
  have hfac := h1.chi_factor lam
  have hfac' : ((chi β 1 κ σ lam : ℝ) : ℂ) =
      (β : ℂ) * ((lam - L1 1 : ℝ) : ℂ) * ((lam : ℂ) - L2 1) * ((lam : ℂ) - L3 1) := by
    rw [hfac]
    push_cast
    ring
  have hnorm : |chi β 1 κ σ lam| =
      β * |lam - L1 1| * ‖(lam : ℂ) - L2 1‖ * ‖(lam : ℂ) - L3 1‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hfac', norm_mul, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hβ0]
  have hk2 : d2 ≤ ‖(lam : ℂ) - L2 1‖ := by
    have := norm_sub_norm_le (L2 1) (lam : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0, norm_sub_rev] at this
    simp only [d2]
    linarith
  have hk3 : d3 ≤ ‖(lam : ℂ) - L3 1‖ := by
    have := norm_sub_norm_le (L3 1) (lam : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0, norm_sub_rev] at this
    simp only [d3]
    linarith
  have hlow : β * |lam - L1 1| * (d2 * d3) ≤ |chi β 1 κ σ lam| := by
    rw [hnorm, mul_assoc (β * |lam - L1 1|)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hk2 hk3 hd3.le (norm_nonneg _))
      (mul_nonneg hβ0.le (abs_nonneg _))
  have hpos : 0 < β * d2 * d3 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith

/-- Woodford (2003), (G.20): `s(γ) = λ₂ + λ₃ = (1 + γ + βγ)/(βγ) − λ₁` and
`p(γ) = λ₂λ₃ = (β²γλ₁)⁻¹`, so `s, p` are continuous wherever `λ₁` is. -/
theorem InertiaRoots.s_p_formulas (hβ0 : 0 < β) (hγ0 : 0 < γ) (h : InertiaRoots β γ κ σ l1 l2 l3) :
    sR l2 l3 = (1 + γ + β * γ) / (β * γ) - l1 ∧ pR l2 l3 = 1 / (β * β * γ * l1) := by
  have v1 := h.vieta1_real
  have v3 := h.vieta3_real
  have hl := h.l1_pos.ne'
  have hb := hβ0.ne'
  have hg := hγ0.ne'
  constructor
  · field_simp
    linear_combination v1
  · field_simp
    field_simp at v3
    linear_combination v3

/-- Woodford (2003), Propositions 8.9 and 8.11 (`γ → 1`): `s(γ) → s(1)` and `p(γ) → p(1)`. -/
theorem s_p_tendsto_one {β κ σ γ1 : ℝ} (hβ0 : 0 < β) (hγ1 : γ1 < 1) (hγ10 : 0 ≤ γ1)
    {L1 : ℝ → ℝ} {L2 L3 : ℝ → ℂ}
    (hR : ∀ γ ∈ Set.Ioc γ1 1, InertiaRoots β γ κ σ (L1 γ) (L2 γ) (L3 γ)) :
    Tendsto (fun γ => sR (L2 γ) (L3 γ)) (𝓝[<] 1) (𝓝 (sR (L2 1) (L3 1))) ∧
      Tendsto (fun γ => pR (L2 γ) (L3 γ)) (𝓝[<] 1) (𝓝 (pR (L2 1) (L3 1))) := by
  have hl1 := l1_tendsto_one hβ0 hγ1 hR
  have h1 := hR 1 ⟨hγ1, le_rfl⟩
  obtain ⟨hs1, hp1⟩ := h1.s_p_formulas hβ0 one_pos
  have hγ : Tendsto (fun γ : ℝ => γ) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ γ in 𝓝[<] 1, γ ∈ Set.Ioo γ1 1 := Ioo_mem_nhdsLT hγ1
  have hl10 : L1 1 ≠ 0 := h1.l1_pos.ne'
  constructor
  · have hlim : Tendsto (fun γ => (1 + γ + β * γ) / (β * γ) - L1 γ) (𝓝[<] 1)
        (𝓝 ((1 + 1 + β * 1) / (β * 1) - L1 1)) :=
      ((((tendsto_const_nhds (x := (1 : ℝ))).add hγ).add (hγ.const_mul β)).div
        (hγ.const_mul β) (by simp [hβ0.ne'])).sub hl1
    rw [hs1]
    refine hlim.congr' ?_
    filter_upwards [hev] with γ hγ'
    exact ((hR γ ⟨hγ'.1, hγ'.2.le⟩).s_p_formulas hβ0 (by linarith [hγ'.1])).1.symm
  · have hlim : Tendsto (fun γ => 1 / (β * β * γ * L1 γ)) (𝓝[<] 1)
        (𝓝 (1 / (β * β * 1 * L1 1))) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div ((hγ.const_mul (β * β)).mul hl1)
        (by simp [hβ0.ne', hl10])
    rw [hp1]
    refine hlim.congr' ?_
    filter_upwards [hev] with γ hγ'
    exact ((hR γ ⟨hγ'.1, hγ'.2.le⟩).s_p_formulas hβ0 (by linarith [hγ'.1])).2.symm


/-! ### Limits of the coefficients as `γ → 0` and `γ → 1` -/

/-- **Proposition 8.9, limit `γ → 0` for Rule I** (Woodford (2003), p. 597, App. G.8, p. 734;
and p. 596 with footnote 44). Along any family of real roots (as in `lemma_G2`):
`θ_π → 0`, `φ_π → κσ/λᵢ > 0`, `φₓ → 4λₓσ/λᵢ`, and Rule I tends to the instrument rule (3.10):
the coefficient `(βγλ₃)⁻¹` on `∑λ₃^{−j}E_t f̂_{t+j}` tends to one, `ρ₁ → 1 + κσ/β` and
`ρ₂ → β⁻¹` (the values (3.8)–(3.9) of the `γ = 0` rule (3.7)). -/
theorem prop_8_9_ruleI_limit {β κ σ lx li γ0 m1 m2 : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hli : 0 < li) (hγ0 : 0 < γ0) (hγ01 : γ0 ≤ 1) {L1 L2 L3 : ℝ → ℝ}
    (hR : ∀ γ ∈ Set.Ioo 0 γ0, InertiaRoots β γ κ σ (L1 γ) (L2 γ : ℂ) (L3 γ : ℂ))
    (hord : ∀ γ ∈ Set.Ioo 0 γ0, L2 γ ≤ L3 γ)
    (hm1 : m1 + m2 = 1 + (1 + κ * σ) / β) (hm2 : m1 * m2 = β⁻¹) (hm12 : m1 < m2) :
    Tendsto (fun γ => thetaPi γ κ σ li (β * γ * L3 γ)⁻¹ (geomKer (L3 γ)⁻¹)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun γ => phiPi β γ κ σ li (β * γ * L3 γ)⁻¹ (geomKer (L3 γ)⁻¹)) (𝓝[>] 0)
      (𝓝 (κ * σ / li)) ∧ 0 < κ * σ / li ∧
    Tendsto (fun γ => phiX σ lx li (β * γ * L3 γ)⁻¹ (geomKer (L3 γ)⁻¹)) (𝓝[>] 0)
      (𝓝 (4 * lx * σ / li)) ∧
    Tendsto (fun γ => (β * γ * L3 γ)⁻¹) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun γ => rho1 (L1 γ) (L2 γ)) (𝓝[>] 0) (𝓝 (1 + κ * σ / β)) ∧
    Tendsto (fun γ => rho2 (L1 γ) (L2 γ)) (𝓝[>] 0) (𝓝 β⁻¹) := by
  obtain ⟨hl3, hinv, hl1, hl2⟩ := lemma_G2 hβ0 hκ hσ hγ0 hγ01 hR hord hm1 hm2 hm12
  have hγ : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ γ in 𝓝[>] 0, γ ∈ Set.Ioo 0 γ0 := Ioo_mem_nhdsGT hγ0
  have hb : β ≠ 0 := hβ0.ne'
  have hbi : β⁻¹ ≠ 0 := inv_ne_zero hb
  have hl : li ≠ 0 := hli.ne'
  have form : ∀ γ ∈ Set.Ioo 0 γ0, 1 < L3 γ ∧
      thetaPi γ κ σ li (β * γ * L3 γ)⁻¹ (geomKer (L3 γ)⁻¹) = κ * σ / (li * β * L3 γ) ∧
      phiX σ lx li (β * γ * L3 γ)⁻¹ (geomKer (L3 γ)⁻¹) = 4 * lx * σ / (li * β * γ * L3 γ) ∧
      phiPi β γ κ σ li (β * γ * L3 γ)⁻¹ (geomKer (L3 γ)⁻¹) = κ * σ / li *
        (1 + β * γ ^ 2 - β * γ - (L3 γ)⁻¹ * γ) / (β * L3 γ * γ * (1 - (L3 γ)⁻¹)) := by
    intro γ hγ'
    have h3 := (hR γ hγ').real_roots.2.1
    obtain ⟨f1, f2, f3, -⟩ := rule_real_formulas (lx := lx) (κ := κ) (σ := σ) hβ0 hγ'.1 hli h3
    exact ⟨h3, f1, f2, f3⟩
  refine ⟨?_, ?_, by positivity, ?_, ?_, ?_, ?_⟩
  · have := hinv.const_mul (κ * σ / (li * β))
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    rw [(form γ hγ').2.1]
    field_simp
  · have hden : Tendsto (fun γ => β * (γ * L3 γ) * (1 - (L3 γ)⁻¹)) (𝓝[>] 0)
        (𝓝 (β * β⁻¹ * (1 - 0))) := (hl3.const_mul β).mul (tendsto_const_nhds.sub hinv)
    have hnum : Tendsto (fun γ => κ * σ / li * (1 + β * γ ^ 2 - β * γ - (L3 γ)⁻¹ * γ))
        (𝓝[>] 0) (𝓝 (κ * σ / li * (1 + β * 0 ^ 2 - β * 0 - 0 * 0))) :=
      ((((tendsto_const_nhds.add ((hγ.pow 2).const_mul β)).sub (hγ.const_mul β)).sub
        (hinv.mul hγ))).const_mul _
    have := hnum.div hden (by simp [hb])
    have e : κ * σ / li * (1 + β * 0 ^ 2 - β * 0 - 0 * 0) / (β * β⁻¹ * (1 - 0)) = κ * σ / li := by
      rw [show (1 + β * 0 ^ 2 - β * 0 - 0 * 0 : ℝ) = 1 by ring, show (1 : ℝ) - 0 = 1 by ring]
      field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    rw [(form γ hγ').2.2.2]
    simp only [Pi.div_apply]
    ring
  · have := (hl3.const_mul β).inv₀ (by simp [hb]) |>.const_mul (4 * lx * σ / li)
    have e : 4 * lx * σ / li * (β * β⁻¹)⁻¹ = 4 * lx * σ / li := by field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    rw [(form γ hγ').2.2.1]
    have : L3 γ ≠ 0 := by linarith [(form γ hγ').1]
    have : γ ≠ 0 := hγ'.1.ne'
    field_simp
  · have := (hl3.const_mul β).inv₀ (by simp [hb])
    rw [mul_inv_cancel₀ hb, inv_one] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    ring_nf
  · have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((hl2.sub (tendsto_const_nhds (x := (1 : ℝ)))).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hl1))
    have e : 1 + (m2 - 1) * (1 - m1) = 1 + κ * σ / β := by
      have : (m2 - 1) * (1 - m1) = (m1 + m2) - 1 - m1 * m2 := by ring
      rw [this, hm1, hm2]
      field_simp
      ring
    rw [e] at this
    exact this
  · have := hl1.mul hl2
    rw [hm2] at this
    exact this

/-- Woodford (2003), App. G.10: the Cauchy-product kernel with real inverse roots. -/
def cauchyKR (μ2 μ3 : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => μ3 * cauchyKR μ2 μ3 j + μ2 ^ (j + 1)

/-- Woodford (2003), App. G.10: the real Cauchy-product kernel is the complex one. -/
theorem cauchyKR_coe (μ2 μ3 : ℝ) (j : ℕ) :
    ((cauchyKR μ2 μ3 j : ℝ) : ℂ) = cauchyK μ2 μ3 j := by
  induction j with
  | zero => simp [cauchyKR, cauchyK]
  | succ j ih =>
    change ((μ3 * cauchyKR μ2 μ3 j + μ2 ^ (j + 1) : ℝ) : ℂ) = (μ3 : ℂ) * cauchyK μ2 μ3 j +
      (μ2 : ℂ) ^ (j + 1)
    push_cast
    rw [ih]

/-- Woodford (2003), App. G.10: with real roots, `K_j = ∑_{k≤j} λ₂^{−k}λ₃^{−(j−k)}` (real form). -/
theorem InertiaRoots.Kker_real {a b : ℝ} (h : InertiaRoots β γ κ σ l1 (a : ℂ) (b : ℂ)) (j : ℕ) :
    Kker (sR a b) (pR a b) j = cauchyKR a⁻¹ b⁻¹ j := by
  apply Complex.ofReal_injective
  rw [h.Kker_eq_cauchy, cauchyKR_coe]
  push_cast
  rfl

/-- Woodford (2003), App. G.10, p. 743: if `μ₂ → μ` and `μ₃ → 0`, then
`∑_{k≤j} μ₂ᵏμ₃^{j−k} → μʲ` for every `j`. -/
theorem tendsto_cauchyKR {α : Type*} {l : Filter α} {f2 f3 : α → ℝ} {μ : ℝ}
    (h2 : Tendsto f2 l (𝓝 μ)) (h3 : Tendsto f3 l (𝓝 0)) (j : ℕ) :
    Tendsto (fun a => cauchyKR (f2 a) (f3 a) j) l (𝓝 (μ ^ j)) := by
  induction j with
  | zero => simpa [cauchyKR] using tendsto_const_nhds
  | succ j ih =>
    have := (h3.mul ih).add (h2.pow (j + 1))
    rw [zero_mul, zero_add] at this
    exact this

/-- **Proposition 8.11, limit `γ → 0`** (Woodford (2003), p. 602; App. G.10, p. 743). Along any
family of real roots (as in `lemma_G2`), `S_π → (1 − 1/λ₂⁰)⁻¹`, `θ_π → 0`, and the other
coefficients approach the nonzero values of the target criterion (3.13):
`φₓ = θₓ → 4(1 − 1/λ₂⁰)λₓ/κ`, `θᵢ → λ₂⁰(1 − λ₁⁰)(1 − 1/λ₂⁰)λᵢ/(κσ)`,
`θ_Δ → λ₁⁰λ₂⁰(1 − 1/λ₂⁰)λᵢ/(κσ)`; and the weights `α_{π,j}, α_{x,j} → (1 − 1/λ₂⁰)λ₂⁰^{−j}`. -/
theorem prop_8_11_limit_zero {β κ σ lx li γ0 m1 m2 : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hli : 0 < li) (hγ0 : 0 < γ0) (hγ01 : γ0 ≤ 1) {L1 L2 L3 : ℝ → ℝ}
    (hR : ∀ γ ∈ Set.Ioo 0 γ0, InertiaRoots β γ κ σ (L1 γ) (L2 γ : ℂ) (L3 γ : ℂ))
    (hord : ∀ γ ∈ Set.Ioo 0 γ0, L2 γ ≤ L3 γ)
    (hm1 : m1 + m2 = 1 + (1 + κ * σ) / β) (hm2 : m1 * m2 = β⁻¹) (hm12 : m1 < m2) :
    Tendsto (fun γ => SpiK β γ (Kker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ)))) (𝓝[>] 0)
      (𝓝 (1 - m2⁻¹)⁻¹) ∧
    Tendsto (fun γ => thetaPi327 β γ (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun γ => phiX327 β γ κ lx (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))) (𝓝[>] 0)
      (𝓝 (4 * (1 - m2⁻¹) * lx / κ)) ∧
    Tendsto (fun γ => thetaI327 β γ κ σ li (L1 γ) (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ)))
      (𝓝[>] 0) (𝓝 (m2 * (1 - m1) * (1 - m2⁻¹) * li / (κ * σ))) ∧
    Tendsto (fun γ => thetaD327 β γ κ σ li (L1 γ) (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ)))
      (𝓝[>] 0) (𝓝 (m1 * m2 * (1 - m2⁻¹) * li / (κ * σ))) ∧
    (∀ j, Tendsto (fun γ => alphaPi β γ (Kker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))) j)
      (𝓝[>] 0) (𝓝 ((1 - m2⁻¹) * m2⁻¹ ^ j))) ∧
    (∀ j, Tendsto (fun γ => alphaX β γ (Kker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))) j)
      (𝓝[>] 0) (𝓝 ((1 - m2⁻¹) * m2⁻¹ ^ j))) := by
  obtain ⟨hl3, hinv, hl1, hl2⟩ := lemma_G2 hβ0 hκ hσ hγ0 hγ01 hR hord hm1 hm2 hm12
  obtain ⟨hm10, hm11, hm21⟩ := roots_zero_location hβ0 hκ hσ hm1 hm2 hm12
  have hγ : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ γ in 𝓝[>] 0, γ ∈ Set.Ioo 0 γ0 := Ioo_mem_nhdsGT hγ0
  have hb : β ≠ 0 := hβ0.ne'
  have hm2' : m2 ≠ 0 := by linarith
  have hμ : 1 - m2⁻¹ ≠ 0 := by
    have : m2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hm21
    linarith
  have hinv2 : Tendsto (fun γ => (L2 γ)⁻¹) (𝓝[>] 0) (𝓝 m2⁻¹) := hl2.inv₀ hm2'
  -- `p/(1 − s + p) = ((1 − λ₂⁻¹)(1 − λ₃⁻¹))⁻¹`
  have hW : Tendsto (fun γ => pR (L2 γ : ℂ) (L3 γ : ℂ) /
      (1 - sR (L2 γ : ℂ) (L3 γ : ℂ) + pR (L2 γ : ℂ) (L3 γ : ℂ))) (𝓝[>] 0) (𝓝 (1 - m2⁻¹)⁻¹) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub hinv2).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv)).inv₀
      (by simp [hμ] : (1 - m2⁻¹) * (1 - 0) ≠ 0)
    rw [sub_zero, mul_one] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    obtain ⟨h2, h3, hs, hp⟩ := (hR γ hγ').real_roots
    rw [hs, hp]
    have : L2 γ ≠ 0 := by linarith
    have : L3 γ ≠ 0 := by linarith
    have : L2 γ - 1 ≠ 0 := by linarith
    have : L3 γ - 1 ≠ 0 := by linarith
    have : 1 - (L2 γ + L3 γ) + L2 γ * L3 γ ≠ 0 := by nlinarith
    field_simp
    ring
  have hS : Tendsto (fun γ => SpiK β γ (Kker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ)))) (𝓝[>] 0)
      (𝓝 (1 - m2⁻¹)⁻¹) := by
    have := hγ.add ((((tendsto_const_nhds (x := (1 : ℝ))).sub hγ).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hγ.const_mul β))).mul hW)
    rw [zero_add, sub_zero, mul_zero, sub_zero, one_mul, one_mul] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    rw [(hR γ hγ').SpiK_Kker]
  have hSne : (1 - m2⁻¹)⁻¹ ≠ 0 := inv_ne_zero hμ
  refine ⟨hS, ?_, ?_, ?_, ?_, fun j => ?_, fun j => ?_⟩
  · have := hγ.div hS hSne
    rw [zero_div] at this
    exact this
  · have := (tendsto_const_nhds (x := 4 * lx)).div (hS.const_mul κ) (by simp [hκ.ne', hμ])
    have e : 4 * lx / (κ * (1 - m2⁻¹)⁻¹) = 4 * (1 - m2⁻¹) * lx / κ := by
      field_simp
    rw [e] at this
    exact this
  · -- `θᵢ = λᵢ(β(γλ₃))(1 − λ₁)λ₂/(κσS)`
    have := ((((hl3.const_mul β).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hl1)).mul
      hl2).const_mul li).div
      (hS.const_mul (κ * σ)) (by simp [hκ.ne', hσ.ne', hμ])
    have e : li * (β * β⁻¹ * (1 - m1) * m2) / (κ * σ * (1 - m2⁻¹)⁻¹) =
        m2 * (1 - m1) * (1 - m2⁻¹) * li / (κ * σ) := by
      field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    obtain ⟨-, -, -, hp⟩ := (hR γ hγ').real_roots
    simp only [Pi.div_apply]
    unfold thetaI327
    rw [hp]
    ring
  · have := ((((hl3.const_mul β).mul hl1).mul hl2).const_mul li).div
      (hS.const_mul (κ * σ)) (by simp [hκ.ne', hσ.ne', hμ])
    have e : li * (β * β⁻¹ * m1 * m2) / (κ * σ * (1 - m2⁻¹)⁻¹) =
        m1 * m2 * (1 - m2⁻¹) * li / (κ * σ) := by
      field_simp
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    obtain ⟨-, -, -, hp⟩ := (hR γ hγ').real_roots
    simp only [Pi.div_apply]
    unfold thetaD327
    rw [hp]
    ring
  · -- the kernel `K_j(γ) → λ₂⁰^{−j}`
    have hK : ∀ k, Tendsto (fun γ => Kker (sR (L2 γ : ℂ) (L3 γ : ℂ)) (pR (L2 γ : ℂ) (L3 γ : ℂ)) k)
        (𝓝[>] 0) (𝓝 (m2⁻¹ ^ k)) := fun k => by
      refine (tendsto_cauchyKR hinv2 hinv k).congr' ?_
      filter_upwards [hev] with γ hγ'
      exact ((hR γ hγ').Kker_real k).symm
    have hP : Tendsto (fun γ => wPrev (Kker (sR (L2 γ : ℂ) (L3 γ : ℂ))
        (pR (L2 γ : ℂ) (L3 γ : ℂ))) j) (𝓝[>] 0) (𝓝 (wPrev (fun k => m2⁻¹ ^ k) j)) := by
      cases j with
      | zero => simp [wPrev]
      | succ k => exact hK k
    have := ((((hγ.const_mul β).mul hP).neg.add
      (((tendsto_const_nhds (x := (1 : ℝ))).add ((hγ.pow 2).const_mul β)).mul (hK j))).add
      (hγ.neg.mul (hK (j + 1)))).div hS hSne
    have e : (-(β * 0 * wPrev (fun k => m2⁻¹ ^ k) j) + (1 + β * 0 ^ 2) * m2⁻¹ ^ j +
        -0 * m2⁻¹ ^ (j + 1)) / (1 - m2⁻¹)⁻¹ = (1 - m2⁻¹) * m2⁻¹ ^ j := by
      rw [div_inv_eq_mul]
      ring
    rw [e] at this
    refine this.congr' (Eventually.of_forall fun γ => ?_)
    simp only [Pi.div_apply, alphaPi, conv3]
    ring
  · have hK : ∀ k, Tendsto (fun γ => Kker (sR (L2 γ : ℂ) (L3 γ : ℂ)) (pR (L2 γ : ℂ) (L3 γ : ℂ)) k)
        (𝓝[>] 0) (𝓝 (m2⁻¹ ^ k)) := fun k => by
      refine (tendsto_cauchyKR hinv2 hinv k).congr' ?_
      filter_upwards [hev] with γ hγ'
      exact ((hR γ hγ').Kker_real k).symm
    have hP : Tendsto (fun γ => wPrev (Kker (sR (L2 γ : ℂ) (L3 γ : ℂ))
        (pR (L2 γ : ℂ) (L3 γ : ℂ))) j) (𝓝[>] 0) (𝓝 (wPrev (fun k => m2⁻¹ ^ k) j)) := by
      cases j with
      | zero => simp [wPrev]
      | succ k => exact hK k
    have := (((hγ.const_mul β).mul hP).neg.add
      (((tendsto_const_nhds (x := (1 : ℝ))).add (hγ.const_mul β)).mul (hK j))).sub (hK (j + 1))
    have e : -(β * 0 * wPrev (fun k => m2⁻¹ ^ k) j) + (1 + β * 0) * m2⁻¹ ^ j - m2⁻¹ ^ (j + 1) =
        (1 - m2⁻¹) * m2⁻¹ ^ j := by
      ring
    rw [e] at this
    refine this.congr' (Eventually.of_forall fun γ => ?_)
    have h0 : Kker (sR (L2 γ : ℂ) (L3 γ : ℂ)) (pR (L2 γ : ℂ) (L3 γ : ℂ)) 0 = 1 := rfl
    simp only [alphaX, conv3, h0, div_one]
    ring

/-- **Proposition 8.9, limit `γ → 1` for Rule III** (Woodford (2003), p. 597; App. G.8, p. 737).
For roots defined for every `γ ∈ (γ₁, 1]`, as `γ → 1⁻` the coefficients `θ_π` and `φ_π` of
Rule III converge to the same positive limit `(κσ/(λᵢβ))(λ₂⁻¹ + λ₃⁻¹)/2` evaluated at `γ = 1`.
(The printed proof only evaluates at `γ = 1`; the limit needs the continuity of the roots,
`s_p_tendsto_one`.) -/
theorem prop_8_9_ruleIII_limit_one {β κ σ li γ1 : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    (hli : 0 < li) (hγ1 : γ1 < 1) (hγ10 : 0 ≤ γ1) {L1 : ℝ → ℝ} {L2 L3 : ℝ → ℂ}
    (hR : ∀ γ ∈ Set.Ioc γ1 1, InertiaRoots β γ κ σ (L1 γ) (L2 γ) (L3 γ)) :
    Tendsto (fun γ => thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))))
      (𝓝[<] 1) (𝓝 (κ * σ / (li * β) * (sR (L2 1) (L3 1) / pR (L2 1) (L3 1) / 2))) ∧
    Tendsto (fun γ => phiPi β γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))))
      (𝓝[<] 1) (𝓝 (κ * σ / (li * β) * (sR (L2 1) (L3 1) / pR (L2 1) (L3 1) / 2))) ∧
    0 < κ * σ / (li * β) * (sR (L2 1) (L3 1) / pR (L2 1) (L3 1) / 2) := by
  obtain ⟨hs, hp⟩ := s_p_tendsto_one hβ0 hγ1 hγ10 hR
  have h1 := hR 1 ⟨hγ1, le_rfl⟩
  have hγ : Tendsto (fun γ : ℝ => γ) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ γ in 𝓝[<] 1, γ ∈ Set.Ioo γ1 1 := Ioo_mem_nhdsLT hγ1
  have hp1 : pR (L2 1) (L3 1) ≠ 0 := by linarith [h1.one_lt_p]
  have hq1 : 1 - sR (L2 1) (L3 1) + pR (L2 1) (L3 1) ≠ 0 := h1.one_sub_s_add_p_pos.ne'
  have hθ : Tendsto (fun γ => κ * σ / (li * β) * (sR (L2 γ) (L3 γ) / pR (L2 γ) (L3 γ) / 2))
      (𝓝[<] 1) (𝓝 (κ * σ / (li * β) * (sR (L2 1) (L3 1) / pR (L2 1) (L3 1) / 2))) :=
    ((hs.div hp hp1).div_const 2).const_mul _
  have hθeq : ∀ γ ∈ Set.Ioo γ1 1,
      thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))) =
        κ * σ / (li * β) * (sR (L2 γ) (L3 γ) / pR (L2 γ) (L3 γ) / 2) := fun γ hγ' =>
    ((hR γ ⟨hγ'.1, hγ'.2.le⟩).ruleIII_formulas (lx := 0) hβ0 (by linarith [hγ'.1]) hli).2.1
  refine ⟨hθ.congr' ?_, ?_, ?_⟩
  · filter_upwards [hev] with γ hγ'
    exact (hθeq γ hγ').symm
  · have hcorr : Tendsto (fun γ => κ * σ * (1 - γ) * (1 - β * γ) * (1 - sR (L2 γ) (L3 γ) / 2) /
        (li * β * γ * (1 - sR (L2 γ) (L3 γ) + pR (L2 γ) (L3 γ)))) (𝓝[<] 1)
        (𝓝 (κ * σ * (1 - 1) * (1 - β * 1) * (1 - sR (L2 1) (L3 1) / 2) /
          (li * β * 1 * (1 - sR (L2 1) (L3 1) + pR (L2 1) (L3 1))))) :=
      ((((tendsto_const_nhds.mul (tendsto_const_nhds.sub hγ)).mul
        (tendsto_const_nhds.sub (hγ.const_mul β))).mul
        (tendsto_const_nhds.sub (hs.div_const 2))).div
        ((hγ.const_mul (li * β)).mul ((tendsto_const_nhds.sub hs).add hp))
        (by simp [hli.ne', hβ0.ne', hq1]))
    rw [sub_self, mul_zero, zero_mul, zero_mul, zero_div] at hcorr
    have := hθ.sub hcorr
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    rw [((hR γ ⟨hγ'.1, hγ'.2.le⟩).ruleIII_formulas (lx := 0) hβ0 (by linarith [hγ'.1]) hli).2.2.2,
      hθeq γ hγ']
  · have := h1.two_lt_s
    have := h1.one_lt_p
    have : 0 < κ * σ / (li * β) := by positivity
    positivity

/-- **Proposition 8.11, limit `γ → 1`** (Woodford (2003), p. 602; App. G.10, p. 743): for roots
defined for every `γ ∈ (γ₁, 1]`, `S_π → 1`, hence `θ_π → 1` and `φₓ = θₓ → 4λₓ/κ`
as `γ → 1⁻`. -/
theorem prop_8_11_limit_one {β κ σ lx γ1 : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hγ1 : γ1 < 1)
    (hγ10 : 0 ≤ γ1) {L1 : ℝ → ℝ} {L2 L3 : ℝ → ℂ}
    (hR : ∀ γ ∈ Set.Ioc γ1 1, InertiaRoots β γ κ σ (L1 γ) (L2 γ) (L3 γ)) :
    Tendsto (fun γ => SpiK β γ (Kker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ)))) (𝓝[<] 1) (𝓝 1) ∧
    Tendsto (fun γ => thetaPi327 β γ (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))) (𝓝[<] 1) (𝓝 1) ∧
    Tendsto (fun γ => phiX327 β γ κ lx (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ))) (𝓝[<] 1)
      (𝓝 (4 * lx / κ)) := by
  obtain ⟨hs, hp⟩ := s_p_tendsto_one hβ0 hγ1 hγ10 hR
  have h1 := hR 1 ⟨hγ1, le_rfl⟩
  have hγ : Tendsto (fun γ : ℝ => γ) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ γ in 𝓝[<] 1, γ ∈ Set.Ioo γ1 1 := Ioo_mem_nhdsLT hγ1
  have hq1 : 1 - sR (L2 1) (L3 1) + pR (L2 1) (L3 1) ≠ 0 := h1.one_sub_s_add_p_pos.ne'
  have hS : Tendsto (fun γ => SpiK β γ (Kker (sR (L2 γ) (L3 γ)) (pR (L2 γ) (L3 γ)))) (𝓝[<] 1)
      (𝓝 1) := by
    have := hγ.add ((((tendsto_const_nhds (x := (1 : ℝ))).sub hγ).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hγ.const_mul β))).mul
      (hp.div (((tendsto_const_nhds (x := (1 : ℝ))).sub hs).add hp) hq1))
    rw [sub_self, zero_mul, zero_mul, add_zero] at this
    refine this.congr' ?_
    filter_upwards [hev] with γ hγ'
    rw [(hR γ ⟨hγ'.1, hγ'.2.le⟩).SpiK_Kker]
    simp only [Pi.div_apply]
  refine ⟨hS, ?_, ?_⟩
  · have := hγ.div hS one_ne_zero
    rw [div_one] at this
    exact this
  · have := (tendsto_const_nhds (x := 4 * lx)).div (hS.const_mul κ) (by simp [hκ.ne'])
    rw [mul_one] at this
    exact this


/-! ### The numbers of Figures 8.3–8.5 -/

/-- Woodford (2003), Figure 8.5, p. 603 and p. 603 text ("the optimal `φₓ` approaches the value
0.51 for `γ = 1`"): at `γ = 1`, `S_π = 1`, so `θ_π = 1` and `φₓ = θₓ = 4λₓ/κ` exactly. -/
theorem InertiaRoots.gamma_one_coeffs {lx : ℝ} (h : InertiaRoots β 1 κ σ l1 l2 l3) :
    SpiK β 1 (Kker (sR l2 l3) (pR l2 l3)) = 1 ∧ thetaPi327 β 1 (sR l2 l3) (pR l2 l3) = 1 ∧
      phiX327 β 1 κ lx (sR l2 l3) (pR l2 l3) = 4 * lx / κ := by
  have hS : SpiK β 1 (Kker (sR l2 l3) (pR l2 l3)) = 1 := by
    rw [h.SpiK_Kker]
    ring
  refine ⟨hS, ?_, ?_⟩
  · unfold thetaPi327
    rw [hS, div_one]
  · unfold phiX327
    rw [hS, mul_one]

/-- Woodford (2003), Figure 8.5, p. 603: with `λₓ = κ/θ` (Chapter 6) and `θ = 7.88` (Table 6.1),
`φₓ(γ = 1) = 4λₓ/κ = 4/θ ≈ 0.508`, which rounds to the printed 0.51. -/
theorem fig_8_5_phiX {κ : ℝ} (hκ : κ ≠ 0) :
    4 * (κ / 7.88) / κ = 4 / (7.88 : ℝ) ∧ (0.505 : ℝ) < 4 / 7.88 ∧ 4 / (7.88 : ℝ) < 0.515 := by
  refine ⟨by field_simp, by norm_num, by norm_num⟩

/-- Woodford (2003), App. G.6, p. 726: the discriminant of a cubic `a z³ + b z² + c z + d`. -/
def cubicDisc {R : Type*} [CommRing R] (a b c d : R) : R :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

/-- Woodford (2003), App. G.6 (Cardano): in terms of the roots, the discriminant of
`a(z − r₁)(z − r₂)(z − r₃)` is `a⁴((r₁ − r₂)(r₁ − r₃)(r₂ − r₃))²`. -/
theorem cubicDisc_roots {R : Type*} [CommRing R] (a r1 r2 r3 : R) :
    cubicDisc a (-(a * (r1 + r2 + r3))) (a * (r1 * r2 + r1 * r3 + r2 * r3))
      (-(a * (r1 * r2 * r3))) = a ^ 4 * ((r1 - r2) * (r1 - r3) * (r2 - r3)) ^ 2 := by
  unfold cubicDisc
  ring

/-- Woodford (2003), App. G.6, pp. 726–727: the discriminant of the characteristic polynomial
`χ_γ(λ) = βγλ³ − (1 + γ + βγ)λ² + (1 + γ + β⁻¹(1 + κσ))λ − β⁻¹` (the book's `Δ(γ)` up to a
negative factor). -/
noncomputable def modelDisc (β γ κ σ : ℝ) : ℝ :=
  cubicDisc (β * γ) (-(1 + γ + β * γ)) (1 + γ + (1 + κ * σ) / β) (-β⁻¹)

/-- Woodford (2003), App. G.6: `disc = (βγ)⁴((λ₁ − λ₂)(λ₁ − λ₃)(λ₂ − λ₃))²`. -/
theorem InertiaRoots.modelDisc_eq (h : InertiaRoots β γ κ σ l1 l2 l3) :
    ((modelDisc β γ κ σ : ℝ) : ℂ) =
      ((β : ℂ) * γ) ^ 4 * ((l1 - l2) * (l1 - l3) * (l2 - l3)) ^ 2 := by
  have e1 : ((-(1 + γ + β * γ) : ℝ) : ℂ) = -((β : ℂ) * γ * (l1 + l2 + l3)) := by
    rw [h.vieta1]
    push_cast
    ring
  have e2 : ((1 + γ + (1 + κ * σ) / β : ℝ) : ℂ) = (β : ℂ) * γ * (l1 * l2 + l1 * l3 + l2 * l3) := by
    rw [h.vieta2]
    push_cast
    ring
  have e3 : ((-β⁻¹ : ℝ) : ℂ) = -((β : ℂ) * γ * (l1 * l2 * l3)) := by
    rw [h.vieta3]
    push_cast
    ring
  unfold modelDisc cubicDisc
  push_cast
  rw [show -(1 + (γ : ℂ) + β * γ) = ((-(1 + γ + β * γ) : ℝ) : ℂ) by push_cast; ring,
    show (1 + (γ : ℂ) + (1 + κ * σ) / β) = ((1 + γ + (1 + κ * σ) / β : ℝ) : ℂ) by push_cast; ring,
    show -(β : ℂ)⁻¹ = ((-β⁻¹ : ℝ) : ℂ) by push_cast; ring, e1, e2, e3]
  have := cubicDisc_roots ((β : ℂ) * γ) (l1 : ℂ) l2 l3
  unfold cubicDisc at this
  rw [← this]

/-- Woodford (2003), App. G.6: with three real roots the discriminant is nonnegative. -/
theorem InertiaRoots.modelDisc_nonneg_of_real (h : InertiaRoots β γ κ σ l1 l2 l3)
    (h2 : l2.im = 0) (h3 : l3.im = 0) : 0 ≤ modelDisc β γ κ σ := by
  have e2 : l2 = (l2.re : ℂ) := Complex.ext (by simp) (by simp [h2])
  have e3 : l3 = (l3.re : ℂ) := Complex.ext (by simp) (by simp [h3])
  have key := h.modelDisc_eq
  rw [e2, e3] at key
  have : modelDisc β γ κ σ = (β * γ) ^ 4 * ((l1 - l2.re) * (l1 - l3.re) * (l2.re - l3.re)) ^ 2 := by
    apply Complex.ofReal_injective
    rw [key]
    push_cast
    ring
  rw [this]
  positivity

/-- Woodford (2003), App. G.6: with a genuinely complex pair (`λ₃ = λ̄₂`, `Im λ₂ ≠ 0`) and
`βγ ≠ 0`, the discriminant is negative. -/
theorem InertiaRoots.modelDisc_neg_of_complex (h : InertiaRoots β γ κ σ l1 l2 l3)
    (hβγ : β * γ ≠ 0) (hc : l3 = (starRingEnd ℂ) l2) (him : l2.im ≠ 0) :
    modelDisc β γ κ σ < 0 := by
  set N := Complex.normSq ((l1 : ℂ) - l2)
  have hN : 0 < N := by
    refine Complex.normSq_pos.mpr fun h0 => him ?_
    have := congrArg Complex.im h0
    simp at this
    linarith
  have e1 : ((l1 : ℂ) - l2) * ((l1 : ℂ) - (starRingEnd ℂ) l2) = (N : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    simp [map_sub, Complex.conj_ofReal]
  have key := h.modelDisc_eq
  rw [hc] at key
  have : modelDisc β γ κ σ = -(4 * (β * γ) ^ 4 * N ^ 2 * l2.im ^ 2) := by
    apply Complex.ofReal_injective
    have e2 : ((l1 : ℂ) - l2) * ((l1 : ℂ) - (starRingEnd ℂ) l2) * (l2 - (starRingEnd ℂ) l2) =
        (N : ℂ) * (((2 * l2.im : ℝ) : ℂ) * Complex.I) := by
      rw [e1, Complex.sub_conj]
    rw [key, e2]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this]
  have : 0 < (β * γ) ^ 4 := by positivity
  have : 0 < l2.im ^ 2 := by positivity
  have : 0 < N ^ 2 := by positivity
  nlinarith [mul_pos (mul_pos ‹0 < (β * γ) ^ 4› ‹0 < N ^ 2›) ‹0 < l2.im ^ 2›]

/-- Woodford (2003), App. G.6 at the Table 6.1 values `β = 0.99`, `κσ = 0.024 · 6.25 = 0.15`: the
discriminant of `χ_γ` is the quartic
`D(γ) = 6196/9801 − (560942/245025)γ + (39888649/24502500)γ² − (37148/61875)γ³ + γ⁴/10000`. -/
theorem modelDisc_table61 {κ σ : ℝ} (hκσ : κ * σ = 0.15) (γ : ℝ) :
    modelDisc 0.99 γ κ σ = 6196 / 9801 - 560942 / 245025 * γ + 39888649 / 24502500 * γ ^ 2 -
      37148 / 61875 * γ ^ 3 + γ ^ 4 / 10000 := by
  unfold modelDisc cubicDisc
  rw [hκσ]
  norm_num
  ring

/-- Woodford (2003), p. 599 and Figure 8.3 ("for all values `γ < γ̄ = .35`, there are three real
roots ... for `γ > γ̄` only rule III is defined"), at the Table 6.1 values `β = 0.99`,
`κσ = 0.15`: for every `γ ∈ (0, 0.353]` the roots supplied by Proposition 8.7 are real, and for
every `γ ∈ [0.354, 1]` they are a genuinely complex pair. Hence the bifurcation point lies in
`(0.353, 0.354)`, i.e. `γ̄ ≈ .35`. -/
theorem gamma_bar_table61 {κ σ : ℝ} (hκσ : κ * σ = 0.15) :
    (∀ γ ∈ Set.Ioc (0 : ℝ) 0.353, ∀ l1 : ℝ, ∀ l2 l3 : ℂ, InertiaRoots 0.99 γ κ σ l1 l2 l3 →
      l2.im = 0 ∧ l3.im = 0) ∧
    (∀ γ ∈ Set.Icc (0.354 : ℝ) 1, ∀ l1 : ℝ, ∀ l2 l3 : ℂ, InertiaRoots 0.99 γ κ σ l1 l2 l3 →
      l3 = (starRingEnd ℂ) l2 ∧ l2.im ≠ 0) := by
  constructor
  · intro γ hγ l1 l2 l3 h
    have hD : 0 < modelDisc 0.99 γ κ σ := by
      rw [modelDisc_table61 hκσ]
      obtain ⟨h0, h1⟩ := hγ
      have a1 : 0 ≤ (0.353 - γ) := by linarith
      have a2 := mul_nonneg a1 h0.le
      have a3 := mul_nonneg a2 h0.le
      have a4 := mul_nonneg a3 h0.le
      have a5 := mul_nonneg a1 (by linarith : (0 : ℝ) ≤ 1 - γ)
      have a7 := mul_nonneg a3 (by linarith : (0 : ℝ) ≤ 1 - γ)
      nlinarith
    rcases h.shape with ⟨h2, h3, -, -⟩ | ⟨hc, -⟩
    · exact ⟨h2, h3⟩
    · by_cases him : l2.im = 0
      · refine ⟨him, ?_⟩
        rw [hc, Complex.conj_im, him, neg_zero]
      · exact absurd (h.modelDisc_neg_of_complex (mul_pos (by norm_num) hγ.1).ne' hc him)
          (not_lt.mpr hD.le)
  · intro γ hγ l1 l2 l3 h
    have hD : modelDisc 0.99 γ κ σ < 0 := by
      rw [modelDisc_table61 hκσ]
      obtain ⟨h0, h1⟩ := hγ
      have a1 : 0 ≤ (γ - 0.354) := by linarith
      have hg0 : (0 : ℝ) ≤ γ := by linarith
      have a2 := mul_nonneg a1 hg0
      have a3 := mul_nonneg a2 hg0
      have a4 := mul_nonneg a3 hg0
      have a5 := mul_nonneg a1 (by linarith : (0 : ℝ) ≤ 1 - γ)
      have a7 := mul_nonneg a3 (by linarith : (0 : ℝ) ≤ 1 - γ)
      nlinarith
    have hγ0 : (0 : ℝ) < γ := by linarith [hγ.1]
    rcases h.shape with ⟨h2, h3, -, -⟩ | ⟨hc, -⟩
    · exact absurd (h.modelDisc_nonneg_of_real h2 h3) (not_le.mpr hD)
    · refine ⟨hc, fun him => ?_⟩
      have h3 : l3.im = 0 := by rw [hc, Complex.conj_im, him, neg_zero]
      exact absurd (h.modelDisc_nonneg_of_real him h3) (not_le.mpr hD)


/-! ### Complex forward inverses: the book's route through `λ₂, λ₃ ∈ ℂ`

The proofs in App. G.7–G.9 apply the forward inverses `(1 − λ₃⁻¹L⁻¹)⁻¹` and `(1 − λ₂⁻¹L⁻¹)⁻¹`
one after the other, with complex `λ₂, λ₃` when the roots form a complex pair; the intermediate
process is then complex-valued. The complex conditional expectation (componentwise) and the
complex forward-inverse lemma (existence and uniqueness of bounded solutions of
`z_t = a E_t z_{t+1} + u_t` for `|a| < 1`) are in `ExpectationTools`; this part shows that the
iterated complex forward inverse is exactly the real kernel forecast `∑ K_j E_t f̂_{t+j}` used
in (3.26). -/

/-- Woodford (2003), App. G.9, p. 739 (regrouping the iterated forward sums): for `|μ₂|, |μ₃| < 1`
and bounded `a`, `∑_j μ₂ʲ ∑_k μ₃ᵏ a_{j+k} = ∑_n C_n a_n` with the Cauchy-product kernel
`C_n = ∑_{k≤n} μ₂ᵏμ₃^{n−k}`. -/
theorem tsum_tsum_eq_cauchyK {μ2 μ3 : ℂ} (h2 : ‖μ2‖ < 1) (h3 : ‖μ3‖ < 1) {a : ℕ → ℂ} {M : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ M) :
    ∑' j, μ2 ^ j * ∑' k, μ3 ^ k * a (j + k) = ∑' n, cauchyK μ2 μ3 n * a n := by
  set F : ℕ × ℕ → ℂ := fun p => μ2 ^ p.1 * (μ3 ^ p.2 * a (p.1 + p.2)) with hFdef
  have hM : 0 ≤ M := (norm_nonneg _).trans (ha 0)
  have hF : Summable F := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) h2).mul_of_nonneg
      ((summable_geometric_of_lt_one (norm_nonneg _) h3).mul_right M)
      (fun _ => by positivity) (fun _ => by positivity)) (fun p => ?_)
    simp only [hFdef, norm_mul, norm_pow]
    gcongr
    exact ha _
  have e1 : ∑' j, μ2 ^ j * ∑' k, μ3 ^ k * a (j + k) = ∑' p, F p := by
    rw [hF.tsum_prod' (fun b => hF.prod_factor b)]
    exact tsum_congr fun j => by rw [← tsum_mul_left]
  have e2 : ∑' p, F p = ∑' n, ∑ ij ∈ Finset.antidiagonal n, F ij := by
    rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq F]
    have hFe : Summable (fun c => F (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c)) :=
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).summable_iff.mpr hF
    rw [hFe.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
    refine tsum_congr fun n => ?_
    rw [tsum_fintype]
    exact Finset.sum_coe_sort (Finset.antidiagonal n) (fun ij => F ij)
  have e3 : ∀ n, ∑ ij ∈ Finset.antidiagonal n, F ij = cauchyK μ2 μ3 n * a n := by
    intro n
    have : ∀ ij ∈ Finset.antidiagonal n, F ij = μ2 ^ ij.1 * μ3 ^ ij.2 * a n := by
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      simp only [hFdef, hij]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, cauchyK_eq_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => μ2 ^ i * μ3 ^ j)]
  rw [e1, e2]
  exact tsum_congr e3

/-- Woodford (2003), (3.26), p. 601 and App. G.9, pp. 738–739: the book's double forward inverse,
computed as two successive complex forward inverses
`E_t[(1 − λ₂⁻¹L⁻¹)⁻¹ (E_·[(1 − λ₃⁻¹L⁻¹)⁻¹ f̂])]`, equals the real kernel forecast
`∑_n K_n E_t f̂_{t+n}` used in `TargetRule` (for real or complex-conjugate roots). -/
theorem InertiaRoots.double_forward_inverse (h : InertiaRoots β γ κ σ l1 l2 l3)
    {f : ℕ → Ω → ℝ} {M : ℝ} (hf : ∀ t ω, |f t ω| ≤ M) (t : ℕ) (ω : Ω) :
    fwdC 𝔼 l2⁻¹ (fwdC 𝔼 l3⁻¹ (fun t ω => (f t ω : ℂ))) t ω =
      ((fwd 𝔼 (Kker (sR l2 l3) (pR l2 l3)) f t ω : ℝ) : ℂ) := by
  have hμ2 : ‖l2⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h.one_lt_norm_l2
  have hμ3 : ‖l3⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h.one_lt_norm_l3
  have hfC : ∀ t ω, ‖((f t ω : ℝ) : ℂ)‖ ≤ M := fun t ω => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf t ω
  set a : ℕ → ℂ := fun n => ((𝔼.E t (f (t + n)) ω : ℝ) : ℂ) with ha
  have hab : ∀ n, ‖a n‖ ≤ M := fun n => by
    simp only [ha, Complex.norm_real, Real.norm_eq_abs]
    exact 𝔼.abs_E_le (hf _) t ω
  have hinner : ∀ j, EC 𝔼 t (fwdC 𝔼 l3⁻¹ (fun t ω => (f t ω : ℂ)) (t + j)) ω =
      ∑' k, l3⁻¹ ^ k * a (j + k) := by
    intro j
    rw [EC_fwdC 𝔼 hμ3 hfC (by omega : t ≤ t + j)]
    refine tsum_congr fun k => ?_
    rw [show (fun ω => ((f (t + j + k) ω : ℝ) : ℂ)) = fun ω => ((f (t + j + k) ω : ℝ) : ℂ) from rfl,
      EC_ofReal]
    simp only [ha, show t + j + k = t + (j + k) by omega]
  change ∑' j, l2⁻¹ ^ j * EC 𝔼 t (fwdC 𝔼 l3⁻¹ (fun t ω => (f t ω : ℂ)) (t + j)) ω = _
  simp only [hinner]
  rw [tsum_tsum_eq_cauchyK hμ2 hμ3 hab]
  change _ = ((∑' n, Kker (sR l2 l3) (pR l2 l3) n * 𝔼.E t (f (t + n)) ω : ℝ) : ℂ)
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast
  rw [h.Kker_eq_cauchy]

/-- Woodford (2003), (3.24), p. 595 and (G.38): the right side of Rule III,
`½(βγλ₃)⁻¹E_t∑λ₃^{−j}f̂_{t+j} + ½(βγλ₂)⁻¹E_t∑λ₂^{−j}f̂_{t+j}` (complex forward inverses when
`λ₂, λ₃` are a complex pair), equals `(βγ)⁻¹ ∑_j w_j E_t f̂_{t+j}` with the real kernel
`ruleIIIker`, so it is real. -/
theorem InertiaRoots.ruleIII_rhs (h : InertiaRoots β γ κ σ l1 l2 l3) {f : ℕ → Ω → ℝ} {M : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (t : ℕ) (ω : Ω) :
    (1 / 2 : ℂ) * ((β : ℂ) * γ * l3)⁻¹ * fwdC 𝔼 l3⁻¹ (fun t ω => (f t ω : ℂ)) t ω +
      (1 / 2 : ℂ) * ((β : ℂ) * γ * l2)⁻¹ * fwdC 𝔼 l2⁻¹ (fun t ω => (f t ω : ℂ)) t ω =
      (((β * γ)⁻¹ * fwd 𝔼 (ruleIIIker (sR l2 l3) (pR l2 l3)) f t ω : ℝ) : ℂ) := by
  have hμ2 : ‖l2⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h.one_lt_norm_l2
  have hμ3 : ‖l3⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h.one_lt_norm_l3
  set a : ℕ → ℂ := fun n => ((𝔼.E t (f (t + n)) ω : ℝ) : ℂ) with ha
  have hab : ∀ n, ‖a n‖ ≤ M := fun n => by
    simp only [ha, Complex.norm_real, Real.norm_eq_abs]
    exact 𝔼.abs_E_le (hf _) t ω
  have hfw : ∀ μ : ℂ, fwdC 𝔼 μ (fun t ω => (f t ω : ℂ)) t ω = ∑' k, μ ^ k * a k := by
    intro μ
    refine tsum_congr fun k => ?_
    rw [EC_ofReal]
  have hs : ∀ μ : ℂ, ‖μ‖ < 1 → Summable (fun k => μ ^ k * a k) := by
    intro μ hμ
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg _) hμ).mul_right M) (fun k => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hab k) (pow_nonneg (norm_nonneg _) k)
  rw [hfw, hfw]
  change _ = (((β * γ)⁻¹ * ∑' n, ruleIIIker (sR l2 l3) (pR l2 l3) n * 𝔼.E t (f (t + n)) ω : ℝ) : ℂ)
  push_cast
  have H := ((hs _ hμ3).hasSum.mul_left ((1 / 2 : ℂ) * ((β : ℂ) * γ * l3)⁻¹)).add
    ((hs _ hμ2).hasSum.mul_left ((1 / 2 : ℂ) * ((β : ℂ) * γ * l2)⁻¹))
  rw [← H.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [h.ruleIIIker_eq]
  simp only [ha, mul_inv]
  ring


/-! ### The representations in levels -/

/-- **Proposition 8.9, Rule III in levels** (Woodford (2003), (3.25), p. 597 and (G.25), (G.48),
p. 737). Given the steady state of (3.16), `A(1)(ī − i*) = −f̄`, Rule III for the deviations
`ı̂ = i − ī`, `π̂ = π − π̄`, `x̂ = x − x̄` is equivalent, date by date, to the rule (3.25) in
levels with intercept `(1 − ρ₁)i*`. -/
theorem prop_8_9_ruleIII_levels {lx li ibar istar pibar xbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li)
    (h : InertiaRoots β γ κ σ l1 l2 l3)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar))
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) (n : ℕ) :
    KernelRule 𝔼 l1 (sR l2 l3 / 2) (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)) i
        (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Level325 𝔼 istar (rho1 l1 (sR l2 l3 / 2)) (rho2 l1 (sR l2 l3 / 2))
        (phiPi β γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (phiX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (thetaPi γ κ σ li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (thetaX σ lx li (β * γ)⁻¹ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (alphaPi β γ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (alphaX β γ (ruleIIIker (sR l2 l3) (pR l2 l3)))
        (levelOf ibar i) (levelOf pibar infl) (levelOf xbar x) (n + 2) := by
  obtain ⟨hrep, -, -, -, -, -, hθ, hαπ, hαx⟩ :=
    prop_8_9_ruleIII 𝔼 hβ0 hβ1 hγ0 hγ1 hκ hσ hlx hli h hπb hπa hxb hxa (i := i)
  exact (hrep n).trans (rep325_iff_level 𝔼 hθ hαπ hαx
    (summable_abs_alphaPi h.summable_abs_ruleIIIker) (summable_abs_alphaX h.summable_abs_ruleIIIker)
    hπb hxb (h.ruleIII_const hβ0 hγ0 (mul_pos hκ hσ).ne' hli.ne' hss) n)

/-- **Proposition 8.9, Rules I and II in levels** (Woodford (2003), (3.25) and (G.36)–(G.37),
pp. 733–734): with three real roots, Rule I (`a = 2, b = 3`) or Rule II (`a = 3, b = 2`) for the
deviations is equivalent to the rule (3.25) in levels with intercept `(1 − ρ₁)i*`. -/
theorem prop_8_9_rule_real_levels {β γ κ σ lx li l1 la lb ibar istar pibar xbar : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hlx : 0 < lx) (hli : 0 < li) (hl10 : 0 < l1) (hl11 : l1 < 1) (hla : 1 < la) (hlb : 1 < lb)
    (hA : β * γ * (1 - l1) * ((1 - la) * (1 - lb)) = κ * σ / β)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar))
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) (n : ℕ) :
    KernelRule 𝔼 l1 la (β * γ * lb)⁻¹ (geomKer lb⁻¹) i (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Level325 𝔼 istar (rho1 l1 la) (rho2 l1 la)
        (phiPi β γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹))
        (phiX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹))
        (thetaPi γ κ σ li (β * γ * lb)⁻¹ (geomKer lb⁻¹))
        (thetaX σ lx li (β * γ * lb)⁻¹ (geomKer lb⁻¹))
        (alphaPi β γ (geomKer lb⁻¹)) (alphaX β γ (geomKer lb⁻¹))
        (levelOf ibar i) (levelOf pibar infl) (levelOf xbar x) (n + 2) := by
  obtain ⟨hrep, -, -, -, -, -, hθ, hαπ, hαx⟩ :=
    rule_real_rep 𝔼 hβ0 hβ1 hγ0 hγ1 hκ hσ hlx hli hl10 hl11 hla hlb hπb hπa hxb hxa (i := i)
  have hμ0 : 0 ≤ lb⁻¹ := inv_nonneg.mpr (by linarith)
  have hμ1 : lb⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlb
  exact (hrep n).trans (rep325_iff_level 𝔼 hθ hαπ hαx
    (summable_abs_alphaPi (summable_abs_geomKer hμ0 hμ1))
    (summable_abs_alphaX (summable_abs_geomKer hμ0 hμ1)) hπb hxb
    (rule_real_const hβ0 hγ0 (mul_pos hκ hσ).ne' hli.ne' hlb hA hss) n)

/-- Woodford (2003), (G.37): for real roots the factorization at `z = 1` reads
`βγ(1 − λ₁)(1 − λ₂)(1 − λ₃) = κσ/β`. -/
theorem InertiaRoots.A_one_real_roots {a b : ℝ} (hβ0 : 0 < β)
    (h : InertiaRoots β γ κ σ l1 (a : ℂ) (b : ℂ)) :
    β * γ * (1 - l1) * ((1 - a) * (1 - b)) = κ * σ / β := by
  obtain ⟨-, -, hs, hp⟩ := h.real_roots
  have := h.A_one_real hβ0.ne'
  rw [hs, hp] at this
  linear_combination this

/-- **Proposition 8.11 in levels** (Woodford (2003), (3.27), p. 601 and (G.52), p. 739): given the
steady state of (3.16), the optimal target criterion (3.26) for the deviations is equivalent,
date by date, to (3.27) in levels,
`F_t(π) + (φₓ/4)F_t(x) = θ_π π_{t−1} + (θₓ/4)x_{t−1} − θᵢ(i_{t−1} − i*) − θ_Δ Δi_{t−1}`. -/
theorem prop_8_11_levels {lx li ibar istar pibar xbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li)
    (h : InertiaRoots β γ κ σ l1 l2 l3)
    (hss : κ * σ / β * (ibar - istar) = -(κ * σ / li * (1 - β * γ) * (1 - γ) * pibar))
    {i infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hπa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hxa : 𝔼.Adapted x) (n : ℕ) :
    TargetRule 𝔼 β γ l1 (sR l2 l3) (pR l2 l3) i (fhat 𝔼 β γ κ σ lx li infl x) (n + 2) ↔
      Level327 𝔼 istar (phiX327 β γ κ lx (sR l2 l3) (pR l2 l3))
        (thetaPi327 β γ (sR l2 l3) (pR l2 l3)) (thetaX327 β γ κ lx (sR l2 l3) (pR l2 l3))
        (thetaI327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3))
        (thetaD327 β γ κ σ li l1 (sR l2 l3) (pR l2 l3))
        (alphaPi β γ (Kker (sR l2 l3) (pR l2 l3))) (alphaX β γ (Kker (sR l2 l3) (pR l2 l3)))
        (levelOf ibar i) (levelOf pibar infl) (levelOf xbar x) (n + 2) := by
  obtain ⟨hrep, hθ, -, -, -, -, -, hαπ, hαx⟩ :=
    prop_8_11 𝔼 hβ0 hβ1 hγ0 hγ1 hκ hσ hlx hli h hπb hπa hxb hxa (i := i)
  exact (hrep n).trans (rep327_iff_level 𝔼 hθ hαπ hαx
    (summable_abs_alphaPi h.summable_abs_Kker) (summable_abs_alphaX h.summable_abs_Kker)
    hπb hxb (h.target_const hβ0 hβ1 hγ0 hγ1 (mul_pos hκ hσ).ne' hli.ne' hss) n)


/-! ### Figure 8.4: the mean forecast horizon of Rule III at `γ = 1` -/

/-- Woodford (2003), p. 600: the mean future horizon of a forecast combination,
`∑_{j≥1} α_j j / ∑_{j≥1} α_j`. -/
noncomputable def meanHorizon (α : ℕ → ℝ) : ℝ := (∑' j : ℕ, (j : ℝ) * α j) / ∑' j, α (j + 1)

/-- Woodford (2003), App. G.8:
`∑_j j (c w_{j−1} + b w_j + a w_{j+1}) = (a + b + c)J + (c − a)W + a w_0`
when `∑ w_j = W` and `∑ j w_j = J`. -/
theorem hasSum_nat_mul_conv3 {w : ℕ → ℝ} {W J : ℝ} (hw : HasSum w W)
    (hJ : HasSum (fun j : ℕ => (j : ℝ) * w j) J) (a b c : ℝ) :
    HasSum (fun j : ℕ => (j : ℝ) * conv3 a b c w j) ((a + b + c) * J + (c - a) * W + a * w 0) := by
  have hP : HasSum (fun j : ℕ => (j : ℝ) * wPrev w j) (J + W) := by
    have h1 : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * wPrev w (j + 1)) (J + W) := by
      refine (hJ.add hw).congr_fun fun j => ?_
      simp only [wPrev]
      push_cast
      ring
    have h2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * wPrev w (n + 1))
        ((J + W) - ∑ i ∈ Finset.range 1, (i : ℝ) * wPrev w i) := by
      simpa using h1
    exact (hasSum_nat_add_iff' 1).mp h2
  have hS : HasSum (fun j : ℕ => (j : ℝ) * w (j + 1)) (J - (W - w 0)) := by
    have h1 : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * w (j + 1)) J := by
      have := (hasSum_nat_add_iff' 1).mpr hJ
      simpa using this
    refine (h1.sub (hasSum_shift hw)).congr_fun fun j => ?_
    push_cast
    ring
  have H := ((hP.mul_left c).add (hJ.mul_left b)).add (hS.mul_left a)
  convert H using 1
  · funext j
    unfold conv3
    ring
  · ring

/-- Woodford (2003), p. 600 and (G.43): at `γ = 1` the inflation- and output-forecast weights
coincide, and the mean horizon of a kernel rule is `((1 − β)W − w_0)/(w_1 − βw_0)`
(`W = ∑ w_j`), independent of the normalization. -/
theorem meanHorizon_gamma_one {β : ℝ} {w : ℕ → ℝ} {W J : ℝ} (hw : HasSum w W)
    (hJ : HasSum (fun j : ℕ => (j : ℝ) * w j) J) (hS : SpiK β 1 w ≠ 0) :
    alphaX β 1 w = alphaPi β 1 w ∧
      meanHorizon (alphaPi β 1 w) = ((1 - β) * W - w 0) / (w 1 - β * w 0) := by
  have hS1 : SpiK β 1 w = w 0 := by
    unfold SpiK
    ring
  have hw0 : w 0 ≠ 0 := hS1 ▸ hS
  constructor
  · funext j
    unfold alphaX alphaPi
    rw [hS1]
    norm_num
  · have hN := (hasSum_nat_mul_conv3 hw hJ (-1) (1 + β * 1 ^ 2) (-(β * 1))).div_const
      (SpiK β 1 w)
    have hD := (hasSum_shift (hasSum_conv3 hw (-1) (1 + β * 1 ^ 2) (-(β * 1)))).div_const
      (SpiK β 1 w)
    unfold meanHorizon
    have e1 : ∑' j : ℕ, (j : ℝ) * alphaPi β 1 w j = ((-1 + (1 + β * 1 ^ 2) + -(β * 1)) * J +
        (-(β * 1) - -1) * W + -1 * w 0) / SpiK β 1 w := by
      rw [← hN.tsum_eq]
      exact tsum_congr fun j => by unfold alphaPi; ring
    have e2 : ∑' j, alphaPi β 1 w (j + 1) = (((-1 + (1 + β * 1 ^ 2) + -(β * 1)) * W - -1 * w 0) -
        conv3 (-1) (1 + β * 1 ^ 2) (-(β * 1)) w 0) / SpiK β 1 w := by
      rw [← hD.tsum_eq]
      rfl
    rw [e1, e2, hS1]
    unfold conv3
    simp only [wPrev]
    field_simp
    ring

/-- Woodford (2003), (G.38)–(G.42): for the Rule III kernel, `∑_j j w_j` converges. -/
theorem InertiaRoots.summable_nat_mul_ruleIIIker (h : InertiaRoots β γ κ σ l1 l2 l3) :
    Summable (fun j : ℕ => (j : ℝ) * ruleIIIker (sR l2 l3) (pR l2 l3) j) := by
  set r := max ‖l2⁻¹‖ ‖l3⁻¹‖
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (le_max_left _ _)
  have hr1 := h.rmax_lt_one
  have hsum : Summable (fun j : ℕ => r * ((j : ℝ) ^ 1 * r ^ j)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left r
  refine Summable.of_norm_bounded hsum (fun j => ?_)
  have hP : |Pker (sR l2 l3) (pR l2 l3) (j + 1)| ≤ 2 * r ^ (j + 1) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h.Pker_eq_powers]
    calc ‖l2⁻¹ ^ (j + 1) + l3⁻¹ ^ (j + 1)‖ ≤ ‖l2⁻¹‖ ^ (j + 1) + ‖l3⁻¹‖ ^ (j + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_pow, norm_pow]
      _ ≤ r ^ (j + 1) + r ^ (j + 1) := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = 2 * r ^ (j + 1) := by ring
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  unfold ruleIIIker
  rw [abs_div, abs_two]
  calc (j : ℝ) * (|Pker (sR l2 l3) (pR l2 l3) (j + 1)| / 2) ≤ (j : ℝ) * (2 * r ^ (j + 1) / 2) := by
        gcongr
    _ = r * ((j : ℝ) ^ 1 * r ^ j) := by ring

/-- Woodford (2003), p. 594 and App. G.6: for `0 ≤ λ ≤ 1`,
`χ_γ(λ) = βγ(λ − λ₁)(λ² − sλ + p)` with `λ² − sλ + p > 0`; so `χ_γ(λ)` has the sign of
`λ − λ₁`, which brackets `λ₁` by evaluating `χ_γ`. -/
theorem InertiaRoots.chi_sign (h : InertiaRoots β γ κ σ l1 l2 l3) {lam : ℝ} (h1 : lam ≤ 1) :
    chi β γ κ σ lam = β * γ * (lam - l1) * (lam ^ 2 - sR l2 l3 * lam + pR l2 l3) ∧
      0 < lam ^ 2 - sR l2 l3 * lam + pR l2 l3 := by
  constructor
  · unfold chi
    linear_combination lam ^ 2 * h.vieta1_real - lam * h.vieta2_real + h.vieta3_real
  · have hs := h.two_lt_s
    have hq := h.one_sub_s_add_p_pos
    nlinarith

/-- **Figure 8.4, mean horizon** (Woodford (2003), p. 600: "equal to only 2.2 quarters in the
case of the calibrated example with `γ = 1`"). At the Table 6.1 values `β = 0.99`, `κσ = 0.15`
and `γ = 1`, the stable root lies in `(0.564, 0.565)` and the mean horizon of the Rule III
forecast weights (the same for inflation and the output gap) lies in `(2.2, 2.25)`. -/
theorem fig_8_4_mean_horizon {κ σ l1 : ℝ} {l2 l3 : ℂ} (hκσ : κ * σ = 0.15)
    (h : InertiaRoots 0.99 1 κ σ l1 l2 l3) :
    0.564 < l1 ∧ l1 < 0.565 ∧
      alphaX 0.99 1 (ruleIIIker (sR l2 l3) (pR l2 l3)) =
        alphaPi 0.99 1 (ruleIIIker (sR l2 l3) (pR l2 l3)) ∧
      2.2 < meanHorizon (alphaPi 0.99 1 (ruleIIIker (sR l2 l3) (pR l2 l3))) ∧
      meanHorizon (alphaPi 0.99 1 (ruleIIIker (sR l2 l3) (pR l2 l3))) < 2.25 := by
  -- bracket the stable root
  have hb : (0 : ℝ) < 0.99 * 1 := by norm_num
  have hlo : 0.564 < l1 := by
    obtain ⟨e, hpos⟩ := h.chi_sign (lam := 0.564) (by norm_num)
    have hv : chi 0.99 1 κ σ 0.564 < 0 := by
      unfold chi
      rw [hκσ]
      norm_num
    rw [e] at hv
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.564 - l1) hpos.le]
  have hhi : l1 < 0.565 := by
    obtain ⟨e, hpos⟩ := h.chi_sign (lam := 0.565) (by norm_num)
    have hv : 0 < chi 0.99 1 κ σ 0.565 := by
      unfold chi
      rw [hκσ]
      norm_num
    rw [e] at hv
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ l1 - 0.565) hpos.le]
  -- the sum and product of the outer roots
  obtain ⟨hs, hp⟩ := h.s_p_formulas (by norm_num) one_pos
  set s := sR l2 l3
  set p := pR l2 l3
  have hs1 : 2.455 ≤ s := by rw [hs]; norm_num; linarith
  have hs2 : s ≤ 2.457 := by rw [hs]; norm_num; linarith
  have hp1 : 1.805 ≤ p := by
    rw [hp, le_div_iff₀ (by positivity)]
    nlinarith
  have hp2 : p ≤ 1.81 := by
    rw [hp, div_le_iff₀ (by positivity)]
    nlinarith
  -- the closed form of the mean horizon
  have hW := h.hasSum_ruleIIIker
  have hJ := h.summable_nat_mul_ruleIIIker.hasSum
  have hw0 : ruleIIIker s p 0 = s / (2 * p) := h.Pker_one
  have hw1 : ruleIIIker s p 1 = (s / p * (s / p) + -1 / p * 2) / 2 := rfl
  have hp0 : 0 < p := by linarith
  have hS : SpiK 0.99 1 (ruleIIIker s p) ≠ 0 := by
    have e : SpiK 0.99 1 (ruleIIIker s p) = s / (2 * p) := by
      unfold SpiK
      rw [hw0]
      ring
    rw [e]
    have : 0 < s := by linarith
    positivity
  obtain ⟨hαx, hMH⟩ := meanHorizon_gamma_one hW hJ hS
  refine ⟨hlo, hhi, hαx, ?_⟩
  rw [hMH, hw0, hw1]
  have hq : 0 < 1 - s + p := by linarith
  have hE : 0 < 2 * p + 0.99 * s * p - s ^ 2 := by nlinarith
  have hq0 : 1 - s + p ≠ 0 := hq.ne'
  have hp00 : p ≠ 0 := hp0.ne'
  have n1 : (1 - 0.99) * ((s - 2) / (2 * (1 - s + p))) - s / (2 * p) =
      -((s * (1 - s + p) - (1 - 0.99) * (s - 2) * p) / (2 * p * (1 - s + p))) := by
    field_simp
    ring
  have d1 : (s / p * (s / p) + -1 / p * 2) / 2 - 0.99 * (s / (2 * p)) =
      -((2 * p + 0.99 * s * p - s ^ 2) / (2 * p ^ 2)) := by
    field_simp
    ring
  have key : ((1 - 0.99) * ((s - 2) / (2 * (1 - s + p))) - s / (2 * p)) /
      ((s / p * (s / p) + -1 / p * 2) / 2 - 0.99 * (s / (2 * p))) =
      p * (s * (1 - s + p) - (1 - 0.99) * (s - 2) * p) /
        ((1 - s + p) * (2 * p + 0.99 * s * p - s ^ 2)) := by
    rw [n1, d1, neg_div_neg_eq, div_div_div_eq,
      div_eq_div_iff (mul_pos (mul_pos (by positivity) hq) hE).ne' (mul_pos hq hE).ne']
    ring
  rw [key]
  have hD : 0 < (1 - s + p) * (2 * p + 0.99 * s * p - s ^ 2) := mul_pos hq hE
  constructor
  · rw [lt_div_iff₀ hD]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hp1),
      mul_nonneg (sub_nonneg.mpr hs2) (sub_nonneg.mpr hp2),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hp2),
      mul_nonneg (sub_nonneg.mpr hs2) (sub_nonneg.mpr hp1),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hs2),
      mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hp2)]
  · rw [div_lt_iff₀ hD]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hp1),
      mul_nonneg (sub_nonneg.mpr hs2) (sub_nonneg.mpr hp2),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hp2),
      mul_nonneg (sub_nonneg.mpr hs2) (sub_nonneg.mpr hp1),
      mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hs2),
      mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hp2)]


/-! ### Figure 8.4: the absolute forecast weights of Rule III at `γ = 1` -/

/-- Woodford (2003), Figure 8.4, p. 600 (interval arithmetic step for `Σ|α_j|/α_0`): if
`A ∈ [A_l, A_u]` and `N ∈ [N_l, N_u]` with `A_l, N_l ≥ 0`, `x ∈ [x_l, x_u]`, `y ∈ [y_l, y_u]`,
then `A x − N y` lies in `[lo, hi]` whenever `lo` and `hi` bound the corner values. -/
theorem rec_step_bounds {A Al Au Nn Nl Nu x xl xu y yl yu lo hi : ℝ} (hAl : 0 ≤ Al)
    (hA : Al ≤ A ∧ A ≤ Au) (hNl : 0 ≤ Nl) (hN : Nl ≤ Nn ∧ Nn ≤ Nu) (hx : xl ≤ x ∧ x ≤ xu)
    (hy : yl ≤ y ∧ y ≤ yu)
    (l1 : lo ≤ Al * xl - Nl * yu) (l2 : lo ≤ Al * xl - Nu * yu) (l3 : lo ≤ Au * xl - Nl * yu)
    (l4 : lo ≤ Au * xl - Nu * yu) (u1 : Al * xu - Nl * yl ≤ hi) (u2 : Al * xu - Nu * yl ≤ hi)
    (u3 : Au * xu - Nl * yl ≤ hi) (u4 : Au * xu - Nu * yl ≤ hi) :
    lo ≤ A * x - Nn * y ∧ A * x - Nn * y ≤ hi := by
  have hA0 : 0 ≤ A := hAl.trans hA.1
  have hN0 : 0 ≤ Nn := hNl.trans hN.1
  have ax : A * xl ≤ A * x := mul_le_mul_of_nonneg_left hx.1 hA0
  have ax' : A * x ≤ A * xu := mul_le_mul_of_nonneg_left hx.2 hA0
  have ny : Nn * yl ≤ Nn * y := mul_le_mul_of_nonneg_left hy.1 hN0
  have ny' : Nn * y ≤ Nn * yu := mul_le_mul_of_nonneg_left hy.2 hN0
  have a1 := sub_nonneg.2 hA.1
  have a2 := sub_nonneg.2 hA.2
  have n1 := sub_nonneg.2 hN.1
  have n2 := sub_nonneg.2 hN.2
  constructor
  · rcases le_total 0 xl with h1 | h1 <;> rcases le_total 0 yu with h2 | h2
    · nlinarith [mul_nonneg a1 h1, mul_nonneg n2 h2]
    · nlinarith [mul_nonneg a1 h1, mul_nonpos_of_nonneg_of_nonpos n1 h2]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos a2 h1, mul_nonneg n2 h2]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos a2 h1, mul_nonpos_of_nonneg_of_nonpos n1 h2]
  · rcases le_total 0 xu with h1 | h1 <;> rcases le_total 0 yl with h2 | h2
    · nlinarith [mul_nonneg a2 h1, mul_nonneg n1 h2]
    · nlinarith [mul_nonneg a2 h1, mul_nonpos_of_nonneg_of_nonpos n2 h2]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 h1, mul_nonneg n1 h2]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos a1 h1, mul_nonpos_of_nonneg_of_nonpos n2 h2]

set_option maxHeartbeats 8000000 in
-- thirty interval-arithmetic steps with 18-digit rational endpoints, each checked by `norm_num`
/-- Woodford (2003), Figure 8.4, p. 600 (interval arithmetic for `Σ|α_j|/α_0`): for a sequence
`w` with `w_0 = A/2`, `w_1 = (A² − 2N)/2` and `w_{j+2} = A w_{j+1} − N w_j`, where `A`, `N` lie in
the rational boxes enclosing `s/p` and `1/p` at the Table 6.1 values and `γ = 1`, the first
30 absolute Rule III weights `|−0.99 w_j + 1.99 w_{j+1} − w_{j+2}|` and the weight
`1.99 w_0 − w_1` lie in explicit intervals. -/
theorem table61_partial_abs_sum {w : ℕ → ℝ} {A Nn : ℝ}
    (hA : (1.358854888232485587 : ℝ) ≤ A ∧ A ≤ (1.358854888232487441 : ℝ))
    (hN : (0.5533708071056408595 : ℝ) ≤ Nn ∧ Nn ≤ (0.5533708071056418396 : ℝ))
    (hw0 : w 0 = A / 2) (hw1 : w 1 = (A * A - 2 * Nn) / 2)
    (hrec : ∀ j, w (j + 2) = A * w (j + 1) - Nn * w j) :
    (0.379972844245741216 : ℝ) ≤
        ∑ j ∈ Finset.range 30, |-(0.99 * w j) + 1.99 * w (j + 1) - w (j + 2)| ∧
      ∑ j ∈ Finset.range 30, |-(0.99 * w j) + 1.99 * w (j + 1) - w (j + 2)| ≤
        (0.379973011050914059 : ℝ) ∧
      (0.98218811726030105 : ℝ) ≤ 1.99 * w 0 - w 1 ∧
      1.99 * w 0 - w 1 ≤ (0.982188117260306396 : ℝ) := by
  have hAl : (0 : ℝ) ≤ (1.358854888232485587 : ℝ) := by norm_num
  have hNl : (0 : ℝ) ≤ (0.5533708071056408595 : ℝ) := by norm_num
  have b0 : (0.6794274441162427935 : ℝ) ≤ w 0 ∧ w 0 ≤ (0.6794274441162437205 : ℝ) := by
    rw [hw0]
    constructor <;> linarith [hA.1, hA.2]
  have b1 : (0.369872496531018608 : ℝ) ≤ w 1 ∧ w 1 ≤ (0.369872496531022109 : ℝ) := by
    rw [hw1]
    have h1 : (1.358854888232485587 : ℝ) * (1.358854888232485587 : ℝ) ≤ A * A :=
      mul_le_mul hA.1 hA.1 hAl (hAl.trans hA.1)
    have h2 : A * A ≤ (1.358854888232487441 : ℝ) * (1.358854888232487441 : ℝ) :=
      mul_le_mul hA.2 hA.2 (hAl.trans hA.1) (by norm_num)
    constructor <;> nlinarith [hN.1, hN.2]
  have b2 : (0.126627736813598549 : ℝ) ≤ w 2 ∧ w 2 ≤ (0.126627736813605172 : ℝ) := by
    rw [show w 2 = A * w 1 - Nn * w 0 from hrec 0]
    exact rec_step_bounds hAl hA hNl hN b1 b0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b3 : (-0.03260792277657536 : ℝ) ≤ w 3 ∧ w 3 ≤ (-0.032607922776563824 : ℝ) := by
    rw [show w 3 = A * w 2 - Nn * w 1 from hrec 1]
    exact rec_step_bounds hAl hA hNl hN b2 b1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b4 : (-0.114381528182562383 : ℝ) ≤ w 4 ∧ w 4 ≤ (-0.114381528182542856 : ℝ) := by
    rw [show w 4 = A * w 3 - Nn * w 2 from hrec 2]
    exact rec_step_bounds hAl hA hNl hN b3 b2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b5 : (-0.137383626149471387 : ℝ) ≤ w 5 ∧ w 5 ≤ (-0.137383626149438224 : ℝ) := by
    rw [show w 5 = A * w 4 - Nn * w 3 from hrec 3]
    exact rec_step_bounds hAl hA hNl hN b4 b3 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b6 : (-0.123389013387963435 : ℝ) ≤ w 6 ∧ w 6 ≤ (-0.123389013387907197 : ℝ) := by
    rw [show w 6 = A * w 5 - Nn * w 4 from hrec 4]
    exact rec_step_bounds hAl hA hNl hN b5 b4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b7 : (-0.091643675911003694 : ℝ) ≤ w 7 ∧ w 7 ≤ (-0.091643675910908558 : ℝ) := by
    rw [show w 7 = A * w 6 - Nn * w 5 from hrec 5]
    exact rec_step_bounds hAl hA hNl hN b6 b5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b8 : (-0.056250579060826296 : ℝ) ≤ w 8 ∧ w 8 ≤ (-0.056250579060665607 : ℝ) := by
    rw [show w 8 = A * w 7 - Nn * w 6 from hrec 6]
    exact rec_step_bounds hAl hA hNl hN b7 b6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b9 : (-0.02572343941776457 : ℝ) ≤ w 9 ∧ w 9 ≤ (-0.025723439417493376 : ℝ) := by
    rw [show w 9 = A * w 8 - Nn * w 7 from hrec 7]
    exact rec_step_bounds hAl hA hNl hN b8 b7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b10 : (-0.003826993060021449 : ℝ) ≤ w 10 ∧ w 10 ≤ (-0.003826993059563911 : ℝ) := by
    rw [show w 10 = A * w 9 - Nn * w 8 from hrec 8]
    exact rec_step_bounds hAl hA hNl hN b9 b8 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b11 : (0.009034272205149414 : ℝ) ≤ w 11 ∧ w 11 ≤ (0.009034272205921246 : ℝ) := by
    rw [show w 11 = A * w 10 - Nn * w 9 from hrec 9]
    exact rec_step_bounds hAl hA hNl hN b10 b9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b12 : (0.014394011185748725 : ℝ) ≤ w 12 ∧ w 12 ≤ (0.014394011187050742 : ℝ) := by
    rw [show w 12 = A * w 11 - Nn * w 10 from hrec 10]
    exact rec_step_bounds hAl hA hNl hN b11 b10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b13 : (0.014560069958825023 : ℝ) ≤ w 13 ∧ w 13 ≤ (0.014560069961021421 : ℝ) := by
    rw [show w 13 = A * w 12 - Nn * w 11 from hrec 11]
    exact rec_step_bounds hAl hA hNl hN b12 b11 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b14 : (0.01181979664849044 : ℝ) ≤ w 14 ∧ w 14 ≤ (0.011819796652195567 : ℝ) := by
    rw [show w 14 = A * w 13 - Nn * w 12 from hrec 12]
    exact rec_step_bounds hAl hA hNl hN b13 b12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b15 : (0.008004270787870149 : ℝ) ≤ w 15 ∧ w 15 ≤ (0.008004270794120339 : ℝ) := by
    rw [show w 15 = A * w 14 - Nn * w 13 from hrec 13]
    exact rec_step_bounds hAl hA hNl hN b14 b13 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b16 : (0.004335912073583816 : ℝ) ≤ w 16 ∧ w 16 ≤ (0.004335912084127254 : ℝ) := by
    rw [show w 16 = A * w 15 - Nn * w 14 from hrec 14]
    exact rec_step_bounds hAl hA hNl hN b15 b14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b17 : (0.001462545526501132 : ℝ) ≤ w 17 ∧ w 17 ≤ (0.001462545544286824 : ℝ) := by
    rw [show w 17 = A * w 16 - Nn * w 15 from hrec 15]
    exact rec_step_bounds hAl hA hNl hN b16 b15 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b18 : (-0.000411980031583987 : ℝ) ≤ w 18 ∧ w 18 ≤ (-0.000411980001581374 : ℝ) := by
    rw [show w 18 = A * w 17 - Nn * w 16 from hrec 16]
    exact rec_step_bounds hAl hA hNl hN b17 b16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b19 : (-0.001369151088042836 : ℝ) ≤ w 19 ∧ w 19 ≤ (-0.001369151037431553 : ℝ) := by
    rw [show w 19 = A * w 18 - Nn * w 17 from hrec 17]
    exact rec_step_bounds hAl hA hNl hN b18 b17 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b20 : (-0.001632499942729369 : ℝ) ≤ w 20 ∧ w 20 ≤ (-0.001632499857353405 : ℝ) := by
    rw [show w 20 = A * w 19 - Nn * w 18 from hrec 18]
    exact rec_step_bounds hAl hA hNl hN b19 b18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b21 : (-0.001460682312584035 : ℝ) ≤ w 21 ∧ w 21 ≤ (-0.001460682168563677 : ℝ) := by
    rw [show w 21 = A * w 20 - Nn * w 19 from hrec 19]
    exact rec_step_bounds hAl hA hNl hN b20 b19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b22 : (-0.001081477536946053 : ℝ) ≤ w 22 ∧ w 22 ≤ (-0.001081477293998714 : ℝ) := by
    rw [show w 22 = A * w 21 - Nn * w 20 from hrec 20]
    exact rec_step_bounds hAl hA hNl hN b21 b20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b23 : (-0.000661272167049875 : ℝ) ≤ w 23 ∧ w 23 ≤ (-0.00066127175722303 : ℝ) := by
    rw [show w 23 = A * w 22 - Nn * w 21 from hrec 21]
    exact rec_step_bounds hAl hA hNl hN b22 b21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b24 : (-0.00030011495360132 : ℝ) ≤ w 24 ∧ w 24 ≤ (-0.00030011426226614 : ℝ) := by
    rw [show w 24 = A * w 23 - Nn * w 22 from hrec 22]
    exact rec_step_bounds hAl hA hNl hN b23 b22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b25 : (-0.000041884185722147 : ℝ) ≤ w 25 ∧ w 25 ≤ (-0.000041883019511744 : ℝ) := by
    rw [show w 25 = A * w 24 - Nn * w 23 from hrec 23]
    exact rec_step_bounds hAl hA hNl hN b24 b23 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b26 : (0.000109159941025951 : ℝ) ≤ w 26 ∧ w 26 ≤ (0.000109161908301365 : ℝ) := by
    rw [show w 26 = A * w 25 - Nn * w 24 from hrec 24]
    exact rec_step_bounds hAl hA hNl hN b25 b24 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b27 : (0.000171509359773518 : ℝ) ≤ w 27 ∧ w 27 ≤ (0.000171512678362124 : ℝ) := by
    rw [show w 27 = A * w 26 - Nn * w 25 from hrec 25]
    exact rec_step_bounds hAl hA hNl hN b26 b25 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b28 : (0.00017264931860395 : ℝ) ≤ w 28 ∧ w 28 ≤ (0.000172654916717084 : ℝ) := by
    rw [show w 28 = A * w 27 - Nn * w 26 from hrec 26]
    exact rec_step_bounds hAl hA hNl hN b27 b26 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b29 : (0.000139695261280886 : ℝ) ≤ w 29 ∧ w 29 ≤ (0.00013970470471434 : ℝ) := by
    rw [show w 29 = A * w 28 - Nn * w 27 from hrec 27]
    exact rec_step_bounds hAl hA hNl hN b28 b27 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b30 : (0.000094283398039956 : ℝ) ≤ w 30 ∧ w 30 ≤ (0.000094299328128051 : ℝ) := by
    rw [show w 30 = A * w 29 - Nn * w 28 from hrec 28]
    exact rec_step_bounds hAl hA hNl hN b29 b28 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b31 : (0.000050808951101533 : ℝ) ≤ w 31 ∧ w 31 ≤ (0.000050835823500005 : ℝ) := by
    rw [show w 31 = A * w 30 - Nn * w 29 from hrec 29]
    exact rec_step_bounds hAl hA hNl hN b30 b29 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have a0 : (0.063214638391944917 : ℝ) ≤ |-(0.99 * w 0) + 1.99 * w 1 - w 2| ∧
      |-(0.99 * w 0) + 1.99 * w 1 - w 2| ≤ (0.063214638391959426 : ℝ) := by
    rw [abs_of_neg (by linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2])]
    constructor <;> linarith [b0.1, b0.2, b1.1, b1.2, b2.1, b2.2]
  have a1 : (0.081576652530058769 : ℝ) ≤ |-(0.99 * w 1) + 1.99 * w 2 - w 3| ∧
      |-(0.99 * w 1) + 1.99 * w 2 - w 3| ≤ (0.081576652530086952 : ℝ) := by
    rw [abs_of_neg (by linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2])]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
  have a2 : (0.07586969758826219 : ℝ) ≤ |-(0.99 * w 2) + 1.99 * w 3 - w 4| ∧
      |-(0.99 * w 2) + 1.99 * w 3 - w 4| ≤ (0.075869697588311231 : ℝ) := by
    rw [abs_of_neg (by linarith [b2.1, b2.2, b3.1, b3.2, b4.1, b4.2])]
    constructor <;> linarith [b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
  have a3 : (0.05795377138497929 : ℝ) ≤ |-(0.99 * w 3) + 1.99 * w 4 - w 5| ∧
      |-(0.99 * w 3) + 1.99 * w 4 - w 5| ≤ (0.057953771385062733 : ℝ) := by
    rw [abs_of_neg (by linarith [b3.1, b3.2, b4.1, b4.2, b5.1, b5.2])]
    constructor <;> linarith [b3.1, b3.2, b4.1, b4.2, b5.1, b5.2]
  have a4 : (0.036766689748681871 : ℝ) ≤ |-(0.99 * w 4) + 1.99 * w 5 - w 6| ∧
      |-(0.99 * w 4) + 1.99 * w 5 - w 6| ≤ (0.036766689748823436 : ℝ) := by
    rw [abs_of_neg (by linarith [b4.1, b4.2, b5.1, b5.2, b6.1, b6.2])]
    constructor <;> linarith [b4.1, b4.2, b5.1, b5.2, b6.1, b6.2]
  have a5 : (0.017890670842954954 : ℝ) ≤ |-(0.99 * w 5) + 1.99 * w 6 - w 7| ∧
      |-(0.99 * w 5) + 1.99 * w 6 - w 7| ≤ (0.017890670843194836 : ℝ) := by
    rw [abs_of_neg (by linarith [b5.1, b5.2, b6.1, b6.2, b7.1, b7.2])]
    constructor <;> linarith [b5.1, b5.2, b6.1, b6.2, b7.1, b7.2]
  have a6 : (0.003965212747797933 : ℝ) ≤ |-(0.99 * w 6) + 1.99 * w 7 - w 8| ∧
      |-(0.99 * w 6) + 1.99 * w 7 - w 8| ≤ (0.00396521274820362 : ℝ) := by
    rw [abs_of_neg (by linarith [b6.1, b6.2, b7.1, b7.2, b8.1, b8.2])]
    constructor <;> linarith [b6.1, b6.2, b7.1, b7.2, b8.1, b8.2]
  have a7 : (0.004512026238248519 : ℝ) ≤ |-(0.99 * w 7) + 1.99 * w 8 - w 9| ∧
      |-(0.99 * w 7) + 1.99 * w 8 - w 9| ≤ (0.00451202623893367 : ℝ) := by
    rw [abs_of_pos (by linarith [b7.1, b7.2, b8.1, b8.2, b9.1, b9.2])]
    constructor <;> linarith [b7.1, b7.2, b8.1, b8.2, b9.1, b9.2]
  have a8 : (0.008325421888271367 : ℝ) ≤ |-(0.99 * w 8) + 1.99 * w 9 - w 10| ∧
      |-(0.99 * w 8) + 1.99 * w 9 - w 10| ≤ (0.008325421889427664 : ℝ) := by
    rw [abs_of_pos (by linarith [b8.1, b8.2, b9.1, b9.2, b10.1, b10.2])]
    constructor <;> linarith [b8.1, b8.2, b9.1, b9.2, b10.1, b10.2]
  have a9 : (0.008816216627954512 : ℝ) ≤ |-(0.99 * w 9) + 1.99 * w 10 - w 11| ∧
      |-(0.99 * w 9) + 1.99 * w 10 - w 11| ≤ (0.008816216629905328 : ℝ) := by
    rw [abs_of_pos (by linarith [b9.1, b9.2, b10.1, b10.2, b11.1, b11.2])]
    constructor <;> linarith [b9.1, b9.2, b10.1, b10.2, b11.1, b11.2]
  have a10 : (0.007372913630164863 : ℝ) ≤ |-(0.99 * w 10) + 1.99 * w 11 - w 12| ∧
      |-(0.99 * w 10) + 1.99 * w 11 - w 12| ≤ (0.00737291363345579 : ℝ) := by
    rw [abs_of_pos (by linarith [b10.1, b10.2, b11.1, b11.2, b12.1, b12.2])]
    constructor <;> linarith [b10.1, b10.2, b11.1, b11.2, b12.1, b12.2]
  have a11 : (0.005140082814756508 : ℝ) ≤ |-(0.99 * w 11) + 1.99 * w 12 - w 13| ∧
      |-(0.99 * w 11) + 1.99 * w 12 - w 13| ≤ (0.005140082820308034 : ℝ) := by
    rw [abs_of_pos (by linarith [b11.1, b11.2, b12.1, b12.2, b13.1, b13.2])]
    constructor <;> linarith [b11.1, b11.2, b12.1, b12.2, b13.1, b13.2]
  have a12 : (0.002904671490685994 : ℝ) ≤ |-(0.99 * w 12) + 1.99 * w 13 - w 14| ∧
      |-(0.99 * w 12) + 1.99 * w 13 - w 14| ≤ (0.002904671500050951 : ℝ) := by
    rw [abs_of_pos (by linarith [b12.1, b12.2, b13.1, b13.2, b14.1, b14.2])]
    constructor <;> linarith [b12.1, b12.2, b13.1, b13.2, b14.1, b14.2]
  have a13 : (0.001102655274964429 : ℝ) ≤ |-(0.99 * w 13) + 1.99 * w 14 - w 15| ∧
      |-(0.99 * w 13) + 1.99 * w 14 - w 15| ≤ (0.001102655290762257 : ℝ) := by
    rw [abs_of_pos (by linarith [b13.1, b13.2, b14.1, b14.2, b15.1, b15.2])]
    constructor <;> linarith [b13.1, b13.2, b14.1, b14.2, b15.1, b15.2]
  have a14 : (0.000109011875289876 : ℝ) ≤ |-(0.99 * w 14) + 1.99 * w 15 - w 16| ∧
      |-(0.99 * w 14) + 1.99 * w 15 - w 16| ≤ (0.000109011901939269 : ℝ) := by
    rw [abs_of_neg (by linarith [b14.1, b14.2, b15.1, b15.2, b16.1, b16.2])]
    constructor <;> linarith [b14.1, b14.2, b15.1, b15.2, b16.1, b16.2]
  have a15 : (0.000758308559079344 : ℝ) ≤ |-(0.99 * w 15) + 1.99 * w 16 - w 17| ∧
      |-(0.99 * w 15) + 1.99 * w 16 - w 17| ≤ (0.000758308604034166 : ℝ) := by
    rw [abs_of_neg (by linarith [b15.1, b15.2, b16.1, b16.2, b17.1, b17.2])]
    constructor <;> linarith [b15.1, b15.2, b16.1, b16.2, b17.1, b17.2]
  have a16 : (0.000970107288133211 : ℝ) ≤ |-(0.99 * w 16) + 1.99 * w 17 - w 18| ∧
      |-(0.99 * w 16) + 1.99 * w 17 - w 18| ≤ (0.000970107363967355 : ℝ) := by
    rw [abs_of_neg (by linarith [b16.1, b16.2, b17.1, b17.2, b18.1, b18.2])]
    constructor <;> linarith [b16.1, b16.2, b17.1, b17.2, b18.1, b18.2]
  have a17 : (0.000898609186340218 : ℝ) ≤ |-(0.99 * w 17) + 1.99 * w 18 - w 19| ∧
      |-(0.99 * w 17) + 1.99 * w 18 - w 19| ≤ (0.000898609314264537 : ℝ) := by
    rw [abs_of_neg (by linarith [b17.1, b17.2, b18.1, b18.2, b19.1, b19.2])]
    constructor <;> linarith [b17.1, b17.2, b18.1, b18.2, b19.1, b19.2]
  have a18 : (0.000684250390491274 : ℝ) ≤ |-(0.99 * w 18) + 1.99 * w 19 - w 20| ∧
      |-(0.99 * w 18) + 1.99 * w 19 - w 20| ≤ (0.000684250606286279 : ℝ) := by
    rw [abs_of_neg (by linarith [b18.1, b18.2, b19.1, b19.2, b20.1, b20.2])]
    constructor <;> linarith [b18.1, b18.2, b19.1, b19.2, b20.1, b20.2]
  have a19 : (0.000432532826386833 : ℝ) ≤ |-(0.99 * w 19) + 1.99 * w 20 - w 21| ∧
      |-(0.99 * w 19) + 1.99 * w 20 - w 21| ≤ (0.00043253319041053 : ℝ) := by
    rw [abs_of_neg (by linarith [b19.1, b19.2, b20.1, b20.2, b21.1, b21.2])]
    constructor <;> linarith [b19.1, b19.2, b20.1, b20.2, b21.1, b21.2]
  have a20 : (0.000209105035193588 : ℝ) ≤ |-(0.99 * w 20) + 1.99 * w 21 - w 22| ∧
      |-(0.99 * w 20) + 1.99 * w 21 - w 22| ≤ (0.000209105649263645 : ℝ) := by
    rw [abs_of_neg (by linarith [b20.1, b20.2, b21.1, b21.2, b22.1, b22.2])]
    constructor <;> linarith [b20.1, b20.2, b21.1, b21.2, b22.1, b22.2]
  have a21 : (0.000044792158549371 : ℝ) ≤ |-(0.99 * w 21) + 1.99 * w 22 - w 23| ∧
      |-(0.99 * w 21) + 1.99 * w 22 - w 23| ≤ (0.000044793194421576 : ℝ) := by
    rw [abs_of_neg (by linarith [b21.1, b21.2, b22.1, b22.2, b23.1, b23.2])]
    constructor <;> linarith [b21.1, b21.2, b22.1, b22.2, b23.1, b23.2]
  have a22 : (0.000054845170895615 : ℝ) ≤ |-(0.99 * w 22) + 1.99 * w 23 - w 24| ∧
      |-(0.99 * w 22) + 1.99 * w 23 - w 24| ≤ (0.000054846918304083 : ℝ) := by
    rw [abs_of_pos (by linarith [b22.1, b22.2, b23.1, b23.2, b24.1, b24.2])]
    constructor <;> linarith [b22.1, b22.2, b23.1, b23.2, b24.1, b24.2]
  have a23 : (0.000099313301495916 : ℝ) ≤ |-(0.99 * w 23) + 1.99 * w 24 - w 25| ∧
      |-(0.99 * w 23) + 1.99 * w 24 - w 25| ≤ (0.000099316249191905 : ℝ) := by
    rw [abs_of_pos (by linarith [b23.1, b23.2, b24.1, b24.2, b25.1, b25.2])]
    constructor <;> linarith [b23.1, b23.2, b24.1, b24.2, b25.1, b25.2]
  have a24 : (0.000104601681755041 : ℝ) ≤ |-(0.99 * w 24) + 1.99 * w 25 - w 26| ∧
      |-(0.99 * w 24) + 1.99 * w 25 - w 26| ≤ (0.000104606654210986 : ℝ) := by
    rw [abs_of_pos (by linarith [b24.1, b24.2, b25.1, b25.2, b26.1, b26.2])]
    constructor <;> linarith [b24.1, b24.2, b25.1, b25.2, b26.1, b26.2]
  have a25 : (0.000087179793596145 : ℝ) ≤ |-(0.99 * w 25) + 1.99 * w 26 - w 27| ∧
      |-(0.99 * w 25) + 1.99 * w 26 - w 27| ≤ (0.000087188181611124 : ℝ) := by
    rw [abs_of_pos (by linarith [b25.1, b25.2, b26.1, b26.2, b27.1, b27.2])]
    constructor <;> linarith [b25.1, b25.2, b26.1, b26.2, b27.1, b27.2]
  have a26 : (0.000060578420013865 : ℝ) ≤ |-(0.99 * w 26) + 1.99 * w 27 - w 28| ∧
      |-(0.99 * w 26) + 1.99 * w 27 - w 28| ≤ (0.000060592569720986 : ℝ) := by
    rw [abs_of_pos (by linarith [b26.1, b26.2, b27.1, b27.2, b28.1, b28.2])]
    constructor <;> linarith [b26.1, b26.2, b27.1, b27.2, b28.1, b28.2]
  have a27 : (0.000034069887729017 : ℝ) ≤ |-(0.99 * w 27) + 1.99 * w 28 - w 29| ∧
      |-(0.99 * w 27) + 1.99 * w 28 - w 29| ≤ (0.000034093756810329 : ℝ) := by
    rw [abs_of_pos (by linarith [b27.1, b27.2, b28.1, b28.2, b29.1, b29.2])]
    constructor <;> linarith [b27.1, b27.2, b28.1, b28.2, b29.1, b29.2]
  have a28 : (0.000012765874270998 : ℝ) ≤ |-(0.99 * w 28) + 1.99 * w 29 - w 30| ∧
      |-(0.99 * w 28) + 1.99 * w 29 - w 30| ≤ (0.000012806138923671 : ℝ) := by
    rw [abs_of_pos (by linarith [b28.1, b28.2, b29.1, b29.2, b30.1, b30.2])]
    constructor <;> linarith [b28.1, b28.2, b29.1, b29.2, b30.1, b30.2]
  have a29 : (0.000001451596794788 : ℝ) ≤ |-(0.99 * w 29) + 1.99 * w 30 - w 31| ∧
      |-(0.99 * w 29) + 1.99 * w 30 - w 31| ≤ (0.00000151951906769 : ℝ) := by
    rw [abs_of_neg (by linarith [b29.1, b29.2, b30.1, b30.2, b31.1, b31.2])]
    constructor <;> linarith [b29.1, b29.2, b30.1, b30.2, b31.1, b31.2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2,
      a5.1, a5.2, a6.1, a6.2, a7.1, a7.2, a8.1, a8.2, a9.1, a9.2,
      a10.1, a10.2, a11.1, a11.2, a12.1, a12.2, a13.1, a13.2, a14.1, a14.2,
      a15.1, a15.2, a16.1, a16.2, a17.1, a17.2, a18.1, a18.2, a19.1, a19.2,
      a20.1, a20.2, a21.1, a21.2, a22.1, a22.2, a23.1, a23.2, a24.1, a24.2,
      a25.1, a25.2, a26.1, a26.2, a27.1, a27.2, a28.1, a28.2, a29.1, a29.2]
  · linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2,
      a5.1, a5.2, a6.1, a6.2, a7.1, a7.2, a8.1, a8.2, a9.1, a9.2,
      a10.1, a10.2, a11.1, a11.2, a12.1, a12.2, a13.1, a13.2, a14.1, a14.2,
      a15.1, a15.2, a16.1, a16.2, a17.1, a17.2, a18.1, a18.2, a19.1, a19.2,
      a20.1, a20.2, a21.1, a21.2, a22.1, a22.2, a23.1, a23.2, a24.1, a24.2,
      a25.1, a25.2, a26.1, a26.2, a27.1, a27.2, a28.1, a28.2, a29.1, a29.2]
  · linarith [b0.1, b0.2, b1.1, b1.2]
  · linarith [b0.1, b0.2, b1.1, b1.2]


/-- Woodford (2003), p. 600: the total relative weight on future forecasts,
`∑_{j>0} |α_j| / α_0`. -/
noncomputable def absWeightRatio (α : ℕ → ℝ) : ℝ := (∑' j, |α (j + 1)|) / α 0

/-- Woodford (2003), (G.41)–(G.42): if `|λ₂⁻¹|, |λ₃⁻¹| ≤ ρ`, the Rule III kernel satisfies
`|w_j| ≤ ρ^{j+1}`. -/
theorem InertiaRoots.abs_ruleIIIker_le (h : InertiaRoots β γ κ σ l1 l2 l3) {ρ : ℝ}
    (h2 : ‖l2⁻¹‖ ≤ ρ) (h3 : ‖l3⁻¹‖ ≤ ρ) (j : ℕ) :
    |ruleIIIker (sR l2 l3) (pR l2 l3) j| ≤ ρ ^ (j + 1) := by
  have hP : |Pker (sR l2 l3) (pR l2 l3) (j + 1)| ≤ 2 * ρ ^ (j + 1) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h.Pker_eq_powers]
    calc ‖l2⁻¹ ^ (j + 1) + l3⁻¹ ^ (j + 1)‖ ≤ ‖l2⁻¹‖ ^ (j + 1) + ‖l3⁻¹‖ ^ (j + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_pow, norm_pow]
      _ ≤ ρ ^ (j + 1) + ρ ^ (j + 1) := by gcongr
      _ = 2 * ρ ^ (j + 1) := by ring
  unfold ruleIIIker
  rw [abs_div, abs_two]
  linarith

/-- Woodford (2003), Figure 8.4 at the Table 6.1 values (`β = 0.99`, `κσ = 0.15`) and `γ = 1`:
rational enclosures `λ₁ ∈ [0.564606475977595, 0.564606475977596]`, boxes for `s/p` and `1/p`,
the complex pair `λ₃ = λ̄₂`, and `|λ₂⁻¹| = |λ₃⁻¹| ≤ 0.745`. -/
theorem table61_gamma_one_box {κ σ l1 : ℝ} {l2 l3 : ℂ} (hκσ : κ * σ = 0.15)
    (h : InertiaRoots 0.99 1 κ σ l1 l2 l3) :
    ((1.358854888232485587 : ℝ) ≤ sR l2 l3 / pR l2 l3 ∧
      sR l2 l3 / pR l2 l3 ≤ (1.358854888232487441 : ℝ)) ∧
    ((0.5533708071056408595 : ℝ) ≤ 1 / pR l2 l3 ∧
      1 / pR l2 l3 ≤ (0.5533708071056418396 : ℝ)) ∧
    ‖l2⁻¹‖ ≤ 0.745 ∧ ‖l3⁻¹‖ ≤ 0.745 := by
  have hlo : (0.564606475977595 : ℝ) < l1 := by
    obtain ⟨e, hpos⟩ := h.chi_sign (lam := 0.564606475977595) (by norm_num)
    have hv : chi 0.99 1 κ σ 0.564606475977595 < 0 := by
      unfold chi
      rw [hκσ]
      norm_num
    rw [e] at hv
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.564606475977595 - l1) hpos.le]
  have hhi : l1 < (0.564606475977596 : ℝ) := by
    obtain ⟨e, hpos⟩ := h.chi_sign (lam := 0.564606475977596) (by norm_num)
    have hv : 0 < chi 0.99 1 κ σ 0.564606475977596 := by
      unfold chi
      rw [hκσ]
      norm_num
    rw [e] at hv
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ l1 - 0.564606475977596) hpos.le]
  obtain ⟨hs, hp⟩ := h.s_p_formulas (by norm_num) one_pos
  have hN : 1 / pR l2 l3 = 0.99 * 0.99 * 1 * l1 := by rw [hp, one_div_one_div]
  have hA : sR l2 l3 / pR l2 l3 =
      ((1 + 1 + 0.99 * 1) / (0.99 * 1) - l1) * (0.99 * 0.99 * 1 * l1) := by
    rw [div_eq_mul_one_div, hN, hs]
  have hNb : (0.5533708071056408595 : ℝ) ≤ 1 / pR l2 l3 ∧
      1 / pR l2 l3 ≤ (0.5533708071056418396 : ℝ) := by
    rw [hN]
    constructor <;> linarith
  refine ⟨?_, hNb, ?_⟩
  · rw [hA]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ l1 - 0.564606475977595)
        (by linarith : (0 : ℝ) ≤ 2.9601 - 0.9801 * (l1 + 0.564606475977595))]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 0.564606475977596 - l1)
        (by linarith : (0 : ℝ) ≤ 2.9601 - 0.9801 * (l1 + 0.564606475977596))]
  · obtain ⟨hc, -⟩ := (gamma_bar_table61 hκσ).2 1 ⟨by norm_num, le_rfl⟩ l1 l2 l3 h
    have hpn : pR l2 l3 = ‖l2‖ ^ 2 := by
      unfold pR
      rw [hc, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hn : 0 < ‖l2‖ := norm_pos_iff.mpr h.l2_ne_zero
    have hinv : ‖l2⁻¹‖ ^ 2 = 1 / pR l2 l3 := by
      rw [hpn, norm_inv, inv_pow, one_div]
    have h2 : ‖l2⁻¹‖ ≤ 0.745 := by
      nlinarith [norm_nonneg l2⁻¹, hNb.2]
    refine ⟨h2, ?_⟩
    rw [hc, ← map_inv₀, Complex.norm_conj]
    exact h2

set_option maxHeartbeats 2000000 in
-- the assembly combines thirty enclosures, a geometric tail and the normalization
/-- **Figure 8.4, relative weight on future forecasts** (Woodford (2003), p. 600: "the sum of the
relative weights on all future quarters ... is equal to only 0.39 even in the extreme case
`γ = 1`"). At the Table 6.1 values `β = 0.99`, `κσ = 0.15` and `γ = 1`, for the Rule III
forecast weights (the same for inflation and the output gap),
`0.386 < ∑_{j>0} |α_j| / α_0 < 0.389`. The proof encloses `λ₁` in an interval of width `10⁻¹⁵`,
propagates rational intervals through the real kernel recursion for the first 30 weights
(`table61_partial_abs_sum`), and bounds the tail by `∑_{j≥30} (0.99 + 1.99ρ + ρ²)ρ^{j+1}`
with `ρ = 0.745 ≥ |λ₂⁻¹| = |λ₃⁻¹|`. -/
theorem fig_8_4_abs_weight_ratio {κ σ l1 : ℝ} {l2 l3 : ℂ} (hκσ : κ * σ = 0.15)
    (h : InertiaRoots 0.99 1 κ σ l1 l2 l3) :
    0.386 < absWeightRatio (alphaPi 0.99 1 (ruleIIIker (sR l2 l3) (pR l2 l3))) ∧
      absWeightRatio (alphaPi 0.99 1 (ruleIIIker (sR l2 l3) (pR l2 l3))) < 0.389 := by
  obtain ⟨hA, hN, hr2, hr3⟩ := table61_gamma_one_box hκσ h
  set s := sR l2 l3
  set p := pR l2 l3
  set w := ruleIIIker s p with hwdef
  set c : ℕ → ℝ := conv3 (-1) (1 + 0.99 * 1 ^ 2) (-(0.99 * 1)) w with hcdef
  have hp0 : p ≠ 0 := by linarith [h.one_lt_p]
  -- the kernel facts
  have hw0 : w 0 = s / p / 2 := by
    have e : ruleIIIker s p 0 = s / (2 * p) := h.Pker_one
    rw [hwdef, e]
    field_simp
  have hw1 : w 1 = (s / p * (s / p) - 2 * (1 / p)) / 2 := by
    change (s / p * (s / p) + -1 / p * 2) / 2 = _
    ring
  have hrec : ∀ j, w (j + 2) = s / p * w (j + 1) - 1 / p * w j := by
    intro j
    change (s / p * Pker s p (j + 2) + -1 / p * Pker s p (j + 1)) / 2 =
      s / p * (Pker s p (j + 2) / 2) - 1 / p * (Pker s p (j + 1) / 2)
    ring
  obtain ⟨hPl, hPu, hc0l, hc0u⟩ := table61_partial_abs_sum hA hN hw0 hw1 hrec
  have hcs : ∀ j, c (j + 1) = -(0.99 * w j) + 1.99 * w (j + 1) - w (j + 2) := by
    intro j
    change -(0.99 * 1) * w j + (1 + 0.99 * 1 ^ 2) * w (j + 1) + -1 * w (j + 1 + 1) = _
    ring
  have hc0 : c 0 = 1.99 * w 0 - w 1 := by
    change -(0.99 * 1) * 0 + (1 + 0.99 * 1 ^ 2) * w 0 + -1 * w (0 + 1) = _
    ring
  -- normalization: `α_j = c_j / S` with `S = w_0 > 0`
  have hS : SpiK 0.99 1 w = w 0 := by
    unfold SpiK
    ring
  have hw0pos : 0 < w 0 := by
    rw [hw0]
    linarith [hA.1]
  have hα : ∀ j, alphaPi 0.99 1 w j = c j / w 0 := fun j => by
    unfold alphaPi
    rw [hS]
  have hsum : Summable (fun j => |c (j + 1)|) :=
    (summable_nat_add_iff 1).mpr (summable_abs_conv3 h.summable_abs_ruleIIIker _ _ _)
  have hratio : absWeightRatio (alphaPi 0.99 1 w) = (∑' j, |c (j + 1)|) / c 0 := by
    unfold absWeightRatio
    simp only [hα, abs_div, abs_of_pos hw0pos]
    rw [tsum_div_const]
    have : c 0 ≠ 0 := by rw [hc0]; linarith
    field_simp
  -- split off the first thirty terms
  have hsplit := (hsum.sum_add_tsum_nat_add 30).symm
  have hfin : ∑ j ∈ Finset.range 30, |c (j + 1)| =
      ∑ j ∈ Finset.range 30, |-(0.99 * w j) + 1.99 * w (j + 1) - w (j + 2)| :=
    Finset.sum_congr rfl fun j _ => by rw [hcs j]
  -- the tail
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = 0.745 := ⟨_, rfl⟩
  have hwb : ∀ j, |w j| ≤ ρ ^ (j + 1) := fun j =>
    h.abs_ruleIIIker_le (hρ ▸ hr2) (hρ ▸ hr3) j
  have hcb : ∀ j, |c (j + 1)| ≤ (0.99 + 1.99 * ρ + ρ ^ 2) * ρ ^ (j + 1) := by
    intro j
    rw [hcs j]
    have h1 := hwb j
    have h2 := hwb (j + 1)
    have h3 := hwb (j + 2)
    have e : (0.99 + 1.99 * ρ + ρ ^ 2) * ρ ^ (j + 1) =
        0.99 * ρ ^ (j + 1) + 1.99 * ρ ^ (j + 1 + 1) + ρ ^ (j + 2 + 1) := by ring
    rw [e]
    calc |-(0.99 * w j) + 1.99 * w (j + 1) - w (j + 2)|
        ≤ |-(0.99 * w j)| + |1.99 * w (j + 1)| + |w (j + 2)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ = 0.99 * |w j| + 1.99 * |w (j + 1)| + |w (j + 2)| := by
          rw [abs_neg, abs_mul, abs_mul]
          norm_num
      _ ≤ _ := by gcongr
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 0.99 + 1.99 * ρ + ρ ^ 2 := ⟨_, rfl⟩
  rw [← hK] at hcb
  have hgeo : HasSum (fun j : ℕ => K * ρ ^ (j + 30 + 1)) (K * ρ ^ 31 / (1 - ρ)) := by
    have := (hasSum_geometric_of_lt_one (by rw [hρ]; norm_num : (0 : ℝ) ≤ ρ)
      (by rw [hρ]; norm_num)).mul_left
      (K * ρ ^ 31)
    convert this using 1
    · funext j
      ring
    · rw [div_eq_mul_inv]
  have htail_le : ∑' j, |c (j + 30 + 1)| ≤ K * ρ ^ 31 / (1 - ρ) := by
    have hsum30 : Summable (fun j => |c (j + 30 + 1)|) := (summable_nat_add_iff 30).mpr hsum
    rw [← hgeo.tsum_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) hsum30 hgeo.summable
    exact hcb (j + 30)
  have htail_num : K * ρ ^ 31 / (1 - ρ) ≤ (0.002 : ℝ) := by
    have r2 : ρ ^ 2 ≤ 0.5551 := by rw [hρ]; norm_num
    have r0 : 0 ≤ ρ := by rw [hρ]; norm_num
    have r4 : ρ ^ 4 ≤ 0.3082 := by
      have : ρ ^ 4 = ρ ^ 2 * ρ ^ 2 := by ring
      rw [this]
      nlinarith [pow_nonneg r0 2]
    have r8 : ρ ^ 8 ≤ 0.095 := by
      have : ρ ^ 8 = ρ ^ 4 * ρ ^ 4 := by ring
      rw [this]
      nlinarith [pow_nonneg r0 4]
    have r16 : ρ ^ 16 ≤ 0.00903 := by
      have : ρ ^ 16 = ρ ^ 8 * ρ ^ 8 := by ring
      rw [this]
      nlinarith [pow_nonneg r0 8]
    have r31 : ρ ^ 31 ≤ 0.00903 * 0.095 * 0.3082 * 0.5551 * 0.745 := by
      have : ρ ^ 31 = ρ ^ 16 * ρ ^ 8 * ρ ^ 4 * ρ ^ 2 * ρ := by ring
      rw [this]
      have hρ1 : ρ ≤ 0.745 := le_of_eq hρ
      gcongr
    rw [hK, div_le_iff₀ (by rw [hρ]; norm_num)]
    rw [hρ] at r31 ⊢
    nlinarith
  have htail_nonneg : 0 ≤ ∑' j, |c (j + 30 + 1)| := tsum_nonneg fun j => abs_nonneg _
  rw [hratio, hsplit, hfin, hc0]
  have hc0pos : 0 < 1.99 * w 0 - w 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hc0pos]
    nlinarith
  · rw [div_lt_iff₀ hc0pos]
    nlinarith

end Woodford.OptimalPolicyRules.InflationInertiaRepresentations
