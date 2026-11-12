/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TaylorDeterminacy

/-!
# The full model on ℤ for any rate path, and real explosions at and above `φ = 1/β`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4.1, eq. (17.18),
p. 408 and eq. (5.5), p. 119 (with Online Appendix A1, §1.7, pp. 569–571), and §17.5.2,
eqs. (17.29)–(17.33), pp. 420–421.

## Part 1: bounded paths on ℤ for an arbitrary bounded rate path

`FullModel.secondZ_unique` proves that (17.18) on `ℤ` has at most one bounded solution;
existence was known only for the step of Figure 17.5 (`FullModel.zPath_existsUnique`). Here the
factorisation of `π_t − (1 + β + σκ) π_{t+1} + β π_{t+2}` with roots `λ₂ < 1 < λ₁` builds the
solution for **every** bounded rate path `i : ℤ → ℝ`: the `λ₂` factor is solved forward,
`F_t = ∑_{k≥0} λ₂ᵏ i_{t+k}` (`FZ`), and the `λ₁` factor backward over the infinite past,
`B_t = ∑_{j≥0} λ₁^{−j} i_{t−1−j}` (`BZ`), giving `π_t = c (B_t + λ₂ F_t)`, `c = σκ/(λ₁ − λ₂)`
(`piZ`). It solves the factored equation (`piZ_factor`) and (17.18) (`piZ_second`), is bounded
(`piZ_bounded`), and is therefore the unique bounded solution (`secondZ_existsUnique`,
`eq_piZ`). As a genuine two-sided sum over `ℤ`, `π_t = ∑_{n∈ℤ} K_n i_{t+n}` with
`K_n = c λ₂^{n+1}` for `n ≥ 0` and `K_n = c λ₁^{n+1}` for `n < 0` (`piZ_hasSum`,
`piZ_eq_tsum_int`). The response anticipated from the infinite past of Figure 17.5 is the
special case `i = 1{t ≥ T}` (`zPath_eq_piZ`). With output, the perfect-foresight equilibrium
`(x, π)` of (17.15)–(17.17) on `ℤ` exists and is unique among bounded paths
(`eqmZ_existsUnique`).

## Part 2: real explosions (p. 421) for every `φ`, in particular `φ ≥ 1/β`

Under perfect foresight the deviation system (17.29)–(17.32) is `PFDev`
(`deviation_iff_pfDev`). In the discounted variables `y_t = βᵗ x̃_t`, `q_t = βᵗ π̃_t` it is
`q_{t+1} = q_t − κ y_t`, `y_{t+1} = (β + σκ) y_t + σ(βφ − 1) q_t` (`scaled_of_pfDev`), so
`y_{t+2} = A y_{t+1} − B y_t` with `A = 1 + β + σκ`, `B = β(1 + σκφ)` (`y_rec`), and at
`φ = 1/β` simply `y_t = (β + σκ)ᵗ x̃_0` (`y_at_inv_beta`). The quadratic form
`Q(u, v) = v² − A u v + B u²` satisfies `Q_{t+1} = B Q_t` (`Qf_step`). For `σ, κ, β > 0`
and every `φ`:

* `explodes_atTop_iff` (the literal claim "`βʲ x_{t+j} → ∞`"): some deviation has
  `βᵗ x̃_t → +∞` iff `φ < 1/β` or (`β + σκ > 1` and `4β(1 + σκφ) ≤ (1 + β + σκ)²`) — the
  latter is the condition for a real characteristic root above one when `φ ≥ 1/β`
  (`explodes_atBot_iff` for `−∞`).
* `unbounded_iff` (real explosion as unboundedness): some deviation has `βᵗ x̃_t` unbounded iff
  `φ < 1/β` or `β(1 + σκφ) > 1`.
* `tvc_fails_iff` (violation of the real transversality condition `βᵗ x̃_t → 0`): iff
  `φ < 1/β` or `β(1 + σκφ) ≥ 1`.

So the claim changes form at and above `1/β`. At the book's own calibrations
(`β = 0.95, σ = 1, κ = 1/2, φ = 1.5`, Fig. 17.8, p. 416; `κ = 0.25, φ = 1.2`, Fig. 17.7,
p. 413) the roots are complex: real explosions exist but oscillate, and **no** deviation has
`βᵗ x̃_t → ±∞` (`book_calibration_oscillates`, `fig17_7_calibration_oscillates`). With
`β = 0.95, σ = 1, κ = 1/25, φ = 1.2` the deviation system is determinate (`φ > 1`), nominal
explosions exist, yet **every** deviation satisfies the real transversality condition
(`tvc_cannot_rule_out`). At `φ = 1/β` there is always a nominal explosion with no output
movement at all, `x̃ = 0`, `π̃_t = β^{−t}` (`nominal_only_at_inv_beta`).
-/

namespace Cochrane.KeynesianStickyPrices.FullModelTidy

open Filter Topology FullModel TaylorDeterminacy

/-! ### Part 1: forward and backward sums on ℤ -/

/-- Cochrane (2023), eq. (5.5), p. 119, on `ℤ`: the forward sum `F_t = ∑_{k≥0} qᵏ i_{t+k}`. -/
noncomputable def FZ (q : ℝ) (i : ℤ → ℝ) (t : ℤ) : ℝ := ∑' k : ℕ, q ^ k * i (t + k)

/-- Cochrane (2023), eq. (5.5), p. 119, on `ℤ`: the backward sum over the infinite past
`B_t = ∑_{j≥0} aʲ i_{t−1−j}`. -/
noncomputable def BZ (a : ℝ) (i : ℤ → ℝ) (t : ℤ) : ℝ := ∑' j : ℕ, a ^ j * i (t - 1 - j)

/-- Cochrane (2023), eq. (5.5): the forward sum on `ℤ` converges for bounded `i`, `0 ≤ q < 1`. -/
theorem FZ_summable {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℤ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℤ) : Summable (fun k : ℕ => q ^ k * i (t + k)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right M) (fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg hq0 k))

/-- Cochrane (2023), eq. (5.5): the backward sum on `ℤ` converges for bounded `i`,
`0 ≤ a < 1`. -/
theorem BZ_summable {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {i : ℤ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℤ) : Summable (fun j : ℕ => a ^ j * i (t - 1 - j)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right M) (fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg ha0 j))

/-- Cochrane (2023), eq. (5.5): `F_t = i_t + q F_{t+1}` on `ℤ`. -/
theorem FZ_rec {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℤ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℤ) : FZ q i t = i t + q * FZ q i (t + 1) := by
  unfold FZ
  rw [(FZ_summable hq0 hq1 hi t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, add_zero]
  congr 1
  refine tsum_congr fun k => ?_
  rw [pow_succ, show t + ((k + 1 : ℕ) : ℤ) = t + 1 + k by push_cast; ring]
  ring

/-- Cochrane (2023), eq. (5.5): `B_{t+1} = a B_t + i_t` on `ℤ`. -/
theorem BZ_rec {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {i : ℤ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℤ) : BZ a i (t + 1) = a * BZ a i t + i t := by
  unfold BZ
  rw [(BZ_summable ha0 ha1 hi (t + 1)).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, add_sub_cancel_right]
  rw [add_comm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t - ((j + 1 : ℕ) : ℤ) = t - 1 - j by push_cast; ring]
  ring

/-- The forward sum on `ℤ` is bounded by `M/(1 − q)`. -/
theorem FZ_bound {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℤ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℤ) : |FZ q i t| ≤ M / (1 - q) := by
  have hb : ∀ k : ℕ, ‖q ^ k * i (t + k)‖ ≤ q ^ k * M := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg hq0 k)
  have := tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq0 hq1).mul_right M) hb
  rw [Real.norm_eq_abs] at this
  unfold FZ
  simpa [div_eq_mul_inv, mul_comm] using this

/-- The backward sum on `ℤ` is bounded by `M/(1 − a)`. -/
theorem BZ_bound {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {i : ℤ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℤ) : |BZ a i t| ≤ M / (1 - a) := by
  have hb : ∀ j : ℕ, ‖a ^ j * i (t - 1 - j)‖ ≤ a ^ j * M := fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg ha0 j)
  have := tsum_of_norm_bounded ((hasSum_geometric_of_lt_one ha0 ha1).mul_right M) hb
  rw [Real.norm_eq_abs] at this
  unfold BZ
  simpa [div_eq_mul_inv, mul_comm] using this

/-! ### Part 1: the two-sided solution -/

/-- Cochrane (2023), eq. (5.5), p. 119 and §17.4.1, p. 408, on `ℤ`: the two-sided moving
average `π_t = c [∑_{j≥0} λ₁^{−j} i_{t−1−j} + λ₂ ∑_{k≥0} λ₂ᵏ i_{t+k}]`,
`c = σκ/(λ₁ − λ₂)`. -/
noncomputable def piZ (σ β κ : ℝ) (i : ℤ → ℝ) (t : ℤ) : ℝ :=
  coef σ β κ * (BZ (lam1 σ β κ)⁻¹ i t + lam2 σ β κ * FZ (lam2 σ β κ) i t)

/-- Cochrane (2023), A1 §1.7, p. 570, on `ℤ`: the two-sided moving average satisfies the
factored equation `λ₁ π_{t+1} = π_t + σκ F_t`. -/
theorem piZ_factor {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℤ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (t : ℤ) :
    lam1 σ β κ * piZ σ β κ i (t + 1) = piZ σ β κ i t + σ * κ * FZ (lam2 σ β κ) i t := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hll : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0.ne'
  have hb := BZ_rec (inv_nonneg.mpr hl0.le) (inv_lt_one_of_one_lt₀ hl1) hi t
  have hf := FZ_rec (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hi t
  have hc := coef_mul ha hβ
  unfold piZ
  linear_combination (coef σ β κ * lam1 σ β κ) * hb - (coef σ β κ * lam1 σ β κ) * hf +
    (coef σ β κ * BZ (lam1 σ β κ)⁻¹ i t) * hll + FZ (lam2 σ β κ) i t * hc

/-- Cochrane (2023), eq. (17.18), p. 408, on `ℤ`: for every bounded rate path the two-sided
moving average solves `π_t − (1 + β + σκ) π_{t+1} + β π_{t+2} = −σκ i_t` at every date. -/
theorem piZ_second {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℤ → ℝ}
    (hi : ∀ t, |i t| ≤ M) : SecondZ σ β κ i (piZ σ β κ i) := by
  intro t
  have e1 := piZ_factor ha hβ hi t
  have e2 := piZ_factor ha hβ hi (t + 1)
  have f := FZ_rec (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hi t
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  rw [show t + 1 + 1 = t + 2 by ring] at e2
  linear_combination piZ σ β κ i (t + 1) * h1 - piZ σ β κ i (t + 2) * h2 - e1 +
    lam2 σ β κ * e2 - (σ * κ) * f

/-- Cochrane (2023), eq. (5.5), on `ℤ`: the two-sided moving average of a bounded rate path is
bounded, `|π_t| ≤ c (M/(1 − λ₁⁻¹) + λ₂ M/(1 − λ₂))`. -/
theorem piZ_bounded {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℤ → ℝ}
    (hi : ∀ t, |i t| ≤ M) : BoundedZ (piZ σ β κ i) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have h2 := lam2_pos ha hβ
  have hc := coef_pos ha hβ
  refine ⟨coef σ β κ * (M / (1 - (lam1 σ β κ)⁻¹) + lam2 σ β κ * (M / (1 - lam2 σ β κ))),
    fun t => ?_⟩
  unfold piZ
  rw [abs_mul, abs_of_pos hc]
  gcongr
  refine (abs_add_le _ _).trans (add_le_add
    (BZ_bound (inv_nonneg.mpr hl0.le) (inv_lt_one_of_one_lt₀ hl1) hi t) ?_)
  rw [abs_mul, abs_of_pos h2]
  gcongr
  exact FZ_bound h2.le (lam2_lt_one ha hβ) hi t

/-- Cochrane (2023), §17.4.1, p. 408 and eq. (5.5), on `ℤ` (perfect foresight, infinite past):
for `σκ > 0`, `β > 0` and **every** bounded rate path there is exactly one bounded inflation
path solving (17.18) at every date. -/
theorem secondZ_existsUnique {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℤ → ℝ}
    (hi : ∀ t, |i t| ≤ M) : ∃! π : ℤ → ℝ, BoundedZ π ∧ SecondZ σ β κ i π :=
  ⟨piZ σ β κ i, ⟨piZ_bounded ha hβ hi, piZ_second ha hβ hi⟩,
    fun _ ⟨hb, hs⟩ => secondZ_unique ha hβ hs (piZ_second ha hβ hi) hb (piZ_bounded ha hβ hi)⟩

/-- Cochrane (2023), eq. (5.5), on `ℤ`: every bounded solution of (17.18) on `ℤ` is the
two-sided moving average. -/
theorem eq_piZ {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℤ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hb : BoundedZ π) (hs : SecondZ σ β κ i π) : π = piZ σ β κ i :=
  secondZ_unique ha hβ hs (piZ_second ha hβ hi) hb (piZ_bounded ha hβ hi)

/-- Cochrane (2023), eq. (5.5): the two-sided kernel `K_n = c λ₂^{n+1}` for `n ≥ 0` and
`K_n = c λ₁^{n+1} = c (λ₁⁻¹)^{−n−1}` for `n < 0`, the weight of `i_{t+n}` in `π_t`. -/
noncomputable def kernel (σ β κ : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then coef σ β κ * lam2 σ β κ ^ (n + 1).toNat
  else coef σ β κ * (lam1 σ β κ)⁻¹ ^ (-n - 1).toNat

/-- Cochrane (2023), eq. (5.5), p. 119, on `ℤ`: the solution is a genuine two-sided sum,
`∑_{n∈ℤ} K_n i_{t+n}` converges (unconditionally) to `π_t`. -/
theorem piZ_hasSum {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℤ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (t : ℤ) :
    HasSum (fun n : ℤ => kernel σ β κ n * i (t + n)) (piZ σ β κ i t) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hF := ((FZ_summable (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hi t).hasSum).mul_left
    (coef σ β κ * lam2 σ β κ)
  have hB := ((BZ_summable (inv_nonneg.mpr hl0.le) (inv_lt_one_of_one_lt₀ hl1) hi t).hasSum
    ).mul_left (coef σ β κ)
  have h := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => kernel σ β κ n * i (t + n))
    (hF.congr_fun fun n => ?_) (hB.congr_fun fun n => ?_)
  · convert h using 1
    unfold piZ FZ BZ
    ring
  · unfold kernel
    simp only [Nat.cast_nonneg, ↓reduceIte]
    rw [show ((n : ℤ) + 1).toNat = n + 1 by omega, pow_succ]
    ring
  · unfold kernel
    have hn : ¬ (0 ≤ -((n : ℤ) + 1)) := by omega
    simp only [hn, ↓reduceIte]
    rw [show (-(-((n : ℤ) + 1)) - 1).toNat = n by omega,
      show t + -((n : ℤ) + 1) = t - 1 - n by ring]
    ring

/-- Cochrane (2023), eq. (5.5), p. 119, on `ℤ`: `π_t = ∑_{n∈ℤ} K_n i_{t+n}`. -/
theorem piZ_eq_tsum_int {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℤ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (t : ℤ) :
    piZ σ β κ i t = ∑' n : ℤ, kernel σ β κ n * i (t + n) :=
  (piZ_hasSum ha hβ hi t).tsum_eq.symm

/-- Cochrane (2023), Fig. 17.5, p. 409: the response to the rise anticipated from the infinite
past (`FullModel.zPath`) is the two-sided moving average of the step. -/
theorem zPath_eq_piZ {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    zPath σ β κ T = piZ σ β κ (stepZ T) := by
  have hs : ∀ t, |stepZ T t| ≤ 1 := fun t => by
    unfold stepZ; split_ifs <;> simp
  exact eq_piZ ha hβ hs (zPath_bounded ha hβ T) (zPath_second ha hβ T)

/-! ### Part 1: the equilibrium with output on ℤ -/

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, under perfect foresight on `ℤ` with no
disturbances: `x_t = x_{t+1} − σ(i_t − π_{t+1})` and `π_t = β π_{t+1} + κ x_t`. -/
def PFEqmZ (σ β κ : ℝ) (i x π : ℤ → ℝ) : Prop :=
  ∀ t, x t = x (t + 1) - σ * (i t - π (t + 1)) ∧ π t = β * π (t + 1) + κ * x t

/-- Cochrane (2023), eq. (17.18), p. 408, on `ℤ`: for `κ ≠ 0`, `(x, π)` is an equilibrium iff
`x_t = (π_t − β π_{t+1})/κ` and inflation solves (17.18). -/
theorem pfEqmZ_iff_secondZ {σ β κ : ℝ} (hκ : κ ≠ 0) (i x π : ℤ → ℝ) :
    PFEqmZ σ β κ i x π ↔ (∀ t, x t = (π t - β * π (t + 1)) / κ) ∧ SecondZ σ β κ i π := by
  constructor
  · intro h
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [eq_div_iff hκ]
      linarith [(h t).2]
    · obtain ⟨h1, h2⟩ := h t
      have h3 := (h (t + 1)).2
      rw [show t + 1 + 1 = t + 2 by ring] at h3
      linear_combination h2 - h3 + κ * h1
  · rintro ⟨hx, hs⟩ t
    refine ⟨?_, ?_⟩
    · rw [hx t, hx (t + 1), show t + 1 + 1 = t + 2 by ring]
      field_simp
      linear_combination hs t
    · rw [hx t]
      field_simp
      ring

/-- Cochrane (2023), §17.4.1, p. 408, on `ℤ`: for `σκ > 0`, `κ ≠ 0`, `β > 0` and every bounded
rate path, there is exactly one bounded perfect-foresight equilibrium `(x, π)` on `ℤ`:
`π = piZ` and `x_t = (π_t − β π_{t+1})/κ`. -/
theorem eqmZ_existsUnique {σ β κ M : ℝ} (ha : 0 < σ * κ) (hκ : κ ≠ 0) (hβ : 0 < β)
    {i : ℤ → ℝ} (hi : ∀ t, |i t| ≤ M) :
    ∃! p : (ℤ → ℝ) × (ℤ → ℝ), BoundedZ p.1 ∧ BoundedZ p.2 ∧ PFEqmZ σ β κ i p.1 p.2 := by
  obtain ⟨Mp, hMp⟩ := piZ_bounded ha hβ hi
  refine ⟨(fun t => (piZ σ β κ i t - β * piZ σ β κ i (t + 1)) / κ, piZ σ β κ i),
    ⟨⟨(Mp + |β| * Mp) / |κ|, fun t => ?_⟩, ⟨Mp, hMp⟩,
      (pfEqmZ_iff_secondZ hκ _ _ _).mpr ⟨fun _ => rfl, piZ_second ha hβ hi⟩⟩, ?_⟩
  · simp only
    rw [abs_div]
    gcongr
    refine (abs_sub _ _).trans (add_le_add (hMp t) ?_)
    rw [abs_mul]
    gcongr
    exact hMp (t + 1)
  · rintro ⟨x, π⟩ ⟨_, hbπ, he⟩
    obtain ⟨hx, hs⟩ := (pfEqmZ_iff_secondZ hκ _ _ _).mp he
    have hπ : π = piZ σ β κ i := eq_piZ ha hβ hi hbπ hs
    simp only at hx hπ ⊢
    subst hπ
    exact Prod.ext (funext hx) rfl


/-! ### Part 2: the perfect-foresight deviation system -/

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, under perfect foresight with `ĩ = φπ̃` and
`r̃ = ĩ − π̃_{t+1}` eliminated: `π̃_t = β π̃_{t+1} + κ x̃_t`,
`x̃_t = x̃_{t+1} − σ(φ π̃_t − π̃_{t+1})`. -/
def PFDev (σ β κ φ : ℝ) (x π : ℕ → ℝ) : Prop :=
  ∀ t, π t = β * π (t + 1) + κ * x t ∧ x t = x (t + 1) - σ * (φ * π t - π (t + 1))

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420: under perfect foresight the deviation system
(`TaylorDeterminacy.Deviation`, `φ_x = 0`) holds iff `ĩ = φπ̃`, `r̃_t = ĩ_t − π̃_{t+1}` and
`(x̃, π̃)` solves `PFDev`. -/
theorem deviation_iff_pfDev (σ β κ φ : ℝ) (i r x π : ℕ → Unit → ℝ) :
    Deviation perfectForesight σ β κ φ 0 i r x π ↔
      (∀ t, i t () = φ * π t ()) ∧ (∀ t, r t () = i t () - π (t + 1) ()) ∧
        PFDev σ β κ φ (fun t => x t ()) (fun t => π t ()) := by
  constructor
  · intro h
    have e : ∀ t, i t () = r t () + π (t + 1) () ∧ x t () = x (t + 1) () - σ * r t () ∧
        π t () = β * π (t + 1) () + κ * x t () ∧ i t () = φ * π t () := fun t => by
      obtain ⟨h1, h2, h3, h4⟩ := h t
      have a1 := congrFun h1 ()
      have a2 := congrFun h2 ()
      have a3 := congrFun h3 ()
      have a4 := congrFun h4 ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero] at a1 a2 a3 a4
      exact ⟨a1, a2, a3, a4⟩
    refine ⟨fun t => (e t).2.2.2, fun t => by linarith [(e t).1], fun t => ⟨(e t).2.2.1, ?_⟩⟩
    obtain ⟨a1, a2, _, a4⟩ := e t
    linear_combination a2 + σ * (a1 - a4)
  · rintro ⟨hi, hr, hd⟩ t
    refine ⟨?_, ?_, ?_, ?_⟩ <;> funext u <;> cases u <;>
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]
    · linarith [hr t]
    · rw [hr t, hi t]
      linarith [(hd t).2]
    · exact (hd t).1
    · exact hi t

/-- Cochrane (2023), p. 420: a property of output deviations holds for some solution of the
perfect-foresight deviation system (17.29)–(17.32) iff it holds for some solution of
`PFDev`. -/
theorem exists_deviation_iff (σ β κ φ : ℝ) (P : (ℕ → ℝ) → Prop) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ 0 i r x π ∧
        P (fun t => x t ())) ↔ ∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ P x := by
  constructor
  · rintro ⟨i, r, x, π, h, hP⟩
    exact ⟨fun t => x t (), fun t => π t (), ((deviation_iff_pfDev σ β κ φ i r x π).mp h).2.2,
      hP⟩
  · rintro ⟨x, π, hd, hP⟩
    exact ⟨fun t _ => φ * π t, fun t _ => φ * π t - π (t + 1), fun t _ => x t, fun t _ => π t,
      (deviation_iff_pfDev σ β κ φ _ _ _ _).mpr ⟨fun _ => rfl, fun _ => rfl, hd⟩, hP⟩

/-- Cochrane (2023), p. 420: the deviation system is linear; the negative of a solution is a
solution. -/
theorem pfDev_neg {σ β κ φ : ℝ} {x π : ℕ → ℝ} (h : PFDev σ β κ φ x π) :
    PFDev σ β κ φ (fun t => -x t) (fun t => -π t) := fun t => by
  obtain ⟨h1, h2⟩ := h t
  exact ⟨by linear_combination -h1, by linear_combination -h2⟩

/-! ### Part 2: discounted variables `y_t = βᵗ x̃_t`, `q_t = βᵗ π̃_t` -/

/-- Cochrane (2023), p. 421 ("faster than the interest rate"): in the discounted variables
`y_t = βᵗ x̃_t`, `q_t = βᵗ π̃_t` the deviation system reads `q_{t+1} = q_t − κ y_t`,
`y_{t+1} = (β + σκ) y_t + σ(βφ − 1) q_t`. -/
theorem scaled_of_pfDev {σ β κ φ : ℝ} {x π : ℕ → ℝ} (h : PFDev σ β κ φ x π) (t : ℕ) :
    β ^ (t + 1) * π (t + 1) = β ^ t * π t - κ * (β ^ t * x t) ∧
      β ^ (t + 1) * x (t + 1) =
        (β + σ * κ) * (β ^ t * x t) + σ * (β * φ - 1) * (β ^ t * π t) := by
  obtain ⟨h1, h2⟩ := h t
  rw [pow_succ]
  exact ⟨by linear_combination (-β ^ t) * h1,
    by linear_combination (-(β ^ t * β)) * h2 + (σ * β ^ t) * h1⟩

/-- Cochrane (2023), p. 421 and A1 (1.57), p. 587: discounted output `y_t = βᵗ x̃_t` of every
perfect-foresight deviation solves `y_{t+2} = (1 + β + σκ) y_{t+1} − β(1 + σκφ) y_t`. -/
theorem y_rec {σ β κ φ : ℝ} {x π : ℕ → ℝ} (h : PFDev σ β κ φ x π) (t : ℕ) :
    β ^ (t + 2) * x (t + 2) =
      (1 + β + σ * κ) * (β ^ (t + 1) * x (t + 1)) - β * (1 + σ * κ * φ) * (β ^ t * x t) := by
  have s0 := scaled_of_pfDev h t
  have s1 := scaled_of_pfDev h (t + 1)
  rw [show t + 1 + 1 = t + 2 by ring] at s1
  linear_combination s1.2 + σ * (β * φ - 1) * s0.1 - s0.2

/-- Cochrane (2023), p. 421: at `φ = 1/β` the discounted output decouples,
`βᵗ x̃_t = (β + σκ)ᵗ x̃_0`. -/
theorem y_at_inv_beta {σ β κ φ : ℝ} {x π : ℕ → ℝ} (h : PFDev σ β κ φ x π) (hφ : β * φ = 1)
    (t : ℕ) : β ^ t * x t = (β + σ * κ) ^ t * x 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [(scaled_of_pfDev h t).2, hφ, ih, pow_succ]
    ring

/-! ### Part 2: the second-order recursion `y_{t+2} = A y_{t+1} − B y_t` -/

/-- The invariant quadratic form `Q(u, v) = v² − A u v + B u²` of `y_{t+2} = A y_{t+1} − B y_t`
(Cochrane (2023), A1 (1.57), p. 587: `A` is the trace and `B` the determinant). -/
def Qf (A B u v : ℝ) : ℝ := v ^ 2 - A * u * v + B * u ^ 2

/-- Cochrane (2023), A1 (1.57): `Q(y_{t+1}, y_{t+2}) = B Q(y_t, y_{t+1})`. -/
theorem Qf_step {A B : ℝ} {y : ℕ → ℝ} (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t)
    (t : ℕ) : Qf A B (y (t + 1)) (y (t + 2)) = B * Qf A B (y t) (y (t + 1)) := by
  unfold Qf
  rw [hy t]
  ring

/-- Cochrane (2023), A1 (1.57): `Q(y_t, y_{t+1}) = Bᵗ Q(y_0, y_1)`. -/
theorem Qf_pow {A B : ℝ} {y : ℕ → ℝ} (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t)
    (t : ℕ) : Qf A B (y t) (y (t + 1)) = B ^ t * Qf A B (y 0) (y 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show t + 1 + 1 = t + 2 by ring, Qf_step hy t, ih, pow_succ]
    ring

/-- `4Q(u, v) ≥ (4B − A²) u²`. -/
theorem Qf_lower (A B u v : ℝ) : (4 * B - A ^ 2) * u ^ 2 ≤ 4 * Qf A B u v := by
  unfold Qf
  nlinarith [sq_nonneg (2 * v - A * u)]

/-- A convergent real sequence is bounded. -/
theorem bounded_of_tendsto {y : ℕ → ℝ} {L : ℝ} (h : Tendsto y atTop (𝓝 L)) :
    ∃ M, ∀ t, |y t| ≤ M := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto y h)
  exact ⟨C, fun t => hC _ ⟨t, rfl⟩⟩

/-- Complex roots of modulus at most one (`A² < 4B ≤ 4`): every solution is bounded. -/
theorem complex_bounded {A B : ℝ} (hD : A ^ 2 < 4 * B) (hB1 : B ≤ 1) {y : ℕ → ℝ}
    (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t) : ∃ M, ∀ t, |y t| ≤ M := by
  have hpos : 0 < 4 * B - A ^ 2 := by linarith
  have hB0 : 0 ≤ B := by nlinarith [sq_nonneg A]
  have hQ0 : 0 ≤ Qf A B (y 0) (y 1) := by
    have := Qf_lower A B (y 0) (y 1)
    nlinarith [sq_nonneg (y 0)]
  refine ⟨1 + 4 * Qf A B (y 0) (y 1) / (4 * B - A ^ 2), fun t => ?_⟩
  have hsq : y t ^ 2 ≤ 4 * Qf A B (y 0) (y 1) / (4 * B - A ^ 2) := by
    rw [le_div_iff₀ hpos]
    have h1 := Qf_lower A B (y t) (y (t + 1))
    rw [Qf_pow hy t] at h1
    have h2 : B ^ t ≤ 1 := pow_le_one₀ hB0 hB1
    nlinarith
  nlinarith [sq_abs (y t), sq_nonneg (|y t| - 1 / 2)]

/-- Complex roots of modulus below one (`A² < 4B < 4`): every solution tends to zero. -/
theorem complex_tendsto_zero {A B : ℝ} (hD : A ^ 2 < 4 * B) (hB1 : B < 1) {y : ℕ → ℝ}
    (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t) : Tendsto y atTop (𝓝 0) := by
  have hpos : 0 < 4 * B - A ^ 2 := by linarith
  have hB0 : 0 ≤ B := by nlinarith [sq_nonneg A]
  have hlim : Tendsto (fun t : ℕ => 4 * (B ^ t * Qf A B (y 0) (y 1)) / (4 * B - A ^ 2))
      atTop (𝓝 0) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one hB0 hB1).mul_const
      (Qf A B (y 0) (y 1))).const_mul 4).div_const (4 * B - A ^ 2)
  have hs := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [Real.sqrt_zero] at hs
  refine squeeze_zero_norm (fun t => ?_) hs
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, Function.comp_apply]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hpos]
  have h1 := Qf_lower A B (y t) (y (t + 1))
  rw [Qf_pow hy t] at h1
  linarith

/-- Real roots in `(0, 1)` (`A² ≥ 4B`, `A, B > 0`, `1 − A + B > 0`, `B ≤ 1`): every solution
tends to zero. -/
theorem real_tendsto_zero {A B : ℝ} (hD : 4 * B ≤ A ^ 2) (hA : 0 < A) (hB : 0 < B)
    (hp : 0 < 1 - A + B) (hB1 : B ≤ 1) {y : ℕ → ℝ}
    (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t) : Tendsto y atTop (𝓝 0) := by
  set s := Real.sqrt (A ^ 2 - 4 * B) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = A ^ 2 - 4 * B := Real.sq_sqrt (by linarith)
  set m1 := (A + s) / 2 with hm1
  set m2 := (A - s) / 2 with hm2
  have hsum : m1 + m2 = A := by rw [hm1, hm2]; ring
  have hprod : m1 * m2 = B := by rw [hm1, hm2]; linear_combination -hs2 / 4
  have h1pos : 0 < m1 := by rw [hm1]; linarith
  have h2le : m2 ≤ m1 := by rw [hm1, hm2]; linarith
  have h2pos : 0 < m2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h1lt : m1 < 1 := by
    by_contra hc
    push Not at hc
    have : m2 ≤ 1 := by nlinarith
    nlinarith
  set w : ℕ → ℝ := fun t => y (t + 1) - m1 * y t with hw
  have hwrec : ∀ t, w (t + 1) = m2 * w t := fun t => by
    simp only [hw]
    rw [show t + 1 + 1 = t + 2 by ring, hy t]
    linear_combination (y (t + 1)) * hsum - (y t) * hprod - (y t / 2) * hs2
  have hwpow : ∀ t, w t = m2 ^ t * w 0 := fun t => by
    induction t with
    | zero => simp
    | succ t ih => rw [hwrec t, ih, pow_succ]; ring
  have hw0 : Tendsto w atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one h2pos.le (h2le.trans_lt h1lt)).mul_const
      (w 0)
    rw [zero_mul] at this
    exact this.congr fun t => (hwpow t).symm
  have hm1abs : |m1| < 1 := by rw [abs_of_pos h1pos]; exact h1lt
  exact SharedTools.tendsto_zero_of_stable hm1abs (f := w) (fun t => by simp only [hw]; ring)
    hw0

/-- If `B > 1` and `Q(y_0, y_1) > 0`, the solution is unbounded (`Q_t = Bᵗ Q_0 → ∞`). -/
theorem unbounded_of_Q {A B : ℝ} (hB : 1 < B) {y : ℕ → ℝ}
    (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t) (hQ : 0 < Qf A B (y 0) (y 1)) :
    ¬ ∃ M, ∀ t, |y t| ≤ M := by
  rintro ⟨M, hM⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hb : ∀ t, B ^ t * Qf A B (y 0) (y 1) ≤ M ^ 2 + |A| * M ^ 2 + B * M ^ 2 := fun t => by
    rw [← Qf_pow hy t]
    unfold Qf
    have h1 := hM t
    have h2 := hM (t + 1)
    have a1 : y (t + 1) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have a2 : y t ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have a3 : -(A * y t * y (t + 1)) ≤ |A| * M ^ 2 := by
      calc -(A * y t * y (t + 1)) ≤ |A * y t * y (t + 1)| := neg_le_abs _
        _ = |A| * (|y t| * |y (t + 1)|) := by rw [abs_mul, abs_mul, mul_assoc]
        _ ≤ |A| * (M * M) := by gcongr
        _ = |A| * M ^ 2 := by ring
    have a4 : B * y t ^ 2 ≤ B * M ^ 2 := mul_le_mul_of_nonneg_left a2 (by linarith)
    linarith
  obtain ⟨t, ht⟩ := ((Tendsto.atTop_mul_const hQ (tendsto_pow_atTop_atTop_of_one_lt hB)
    ).eventually_gt_atTop (M ^ 2 + |A| * M ^ 2 + B * M ^ 2)).exists
  linarith [hb t]

/-- If `B = 1` and `Q(y_0, y_1) ≠ 0`, the solution does not tend to zero (`Q_t = Q_0`). -/
theorem not_tendsto_zero_of_Q {A B : ℝ} (hB : B = 1) {y : ℕ → ℝ}
    (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t) (hQ : Qf A B (y 0) (y 1) ≠ 0) :
    ¬ Tendsto y atTop (𝓝 0) := by
  intro h
  have hc : Continuous fun p : ℝ × ℝ => Qf A B p.1 p.2 := by unfold Qf; fun_prop
  have h1 := (hc.tendsto ((0 : ℝ), (0 : ℝ))).comp
    (h.prodMk_nhds (h.comp (tendsto_add_atTop_nat 1)))
  have h2 : (fun t => Qf A B (y t) (y (t + 1))) = fun _ => Qf A B (y 0) (y 1) := by
    funext t
    rw [Qf_pow hy t, hB, one_pow, one_mul]
  have h3 : Tendsto (fun _ : ℕ => Qf A B (y 0) (y 1)) atTop (𝓝 (Qf A B 0 0)) := by
    rw [← h2]; exact h1
  apply hQ
  rw [tendsto_nhds_unique tendsto_const_nhds h3]
  simp [Qf]

/-- Complex roots (`A² < 4B`): no solution tends to `+∞` — the ratio `r_t = y_{t+1}/y_t` would
satisfy `r_{t+1} = A − B/r_t ≤ r_t − δ` and become negative. -/
theorem complex_not_atTop {A B : ℝ} (hD : A ^ 2 < 4 * B) {y : ℕ → ℝ}
    (hy : ∀ t, y (t + 2) = A * y (t + 1) - B * y t) : ¬ Tendsto y atTop atTop := by
  intro h
  obtain ⟨T, hT⟩ := eventually_atTop.mp (h.eventually_gt_atTop 0)
  set r : ℕ → ℝ := fun n => y (T + n + 1) / y (T + n) with hr
  have hrpos : ∀ n, 0 < r n := fun n =>
    div_pos (hT _ (by omega)) (hT _ (by omega))
  have hrrec : ∀ n, r (n + 1) = A - B / r n := fun n => by
    have h0 := hT (T + n) (by omega)
    have h1 := hT (T + n + 1) (by omega)
    simp only [hr]
    rw [show T + (n + 1) + 1 = T + n + 2 by ring, show T + (n + 1) = T + n + 1 by ring,
      hy (T + n)]
    field_simp
  set e := (4 * B - A ^ 2) / 4 with he
  have hepos : 0 < e := by rw [he]; linarith
  set δ := e / r 0 with hδ
  have hδpos : 0 < δ := div_pos hepos (hrpos 0)
  have key : ∀ n : ℕ, r n ≤ r 0 - n * δ := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have hρ := hrpos n
      have hρ0 : r n ≤ r 0 := by
        have : 0 ≤ (n : ℝ) * δ := by positivity
        linarith
      have hq : e ≤ r n ^ 2 - A * r n + B := by
        rw [he]; nlinarith [sq_nonneg (2 * r n - A)]
      have hδr : δ * r n ≤ e := by
        rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (hrpos 0)]
        nlinarith
      have hstep : r (n + 1) ≤ r n - δ := by
        rw [hrrec n, show A - B / r n = (A * r n - B) / r n by field_simp, div_le_iff₀ hρ]
        nlinarith
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (r 0 / δ)
  have hn' : r 0 < n * δ := by rwa [div_lt_iff₀ hδpos] at hn
  linarith [key n, hrpos n]

/-! ### Part 2: explicit solutions -/

/-- Cochrane (2023), A1 (1.57), p. 587: for a root `μ` of
`μ² − (1 + β + σκ) μ + β(1 + σκφ) = 0` (`μ = βν`, `ν` an eigenvalue of (17.33)),
`x̃_t = c(1 − μ)(μ/β)ᵗ`, `π̃_t = cκ(μ/β)ᵗ` solves the deviation system. -/
theorem eigen_pfDev {σ β κ φ μ : ℝ} (hβ : β ≠ 0)
    (hμ : μ ^ 2 - (1 + β + σ * κ) * μ + β * (1 + σ * κ * φ) = 0) (c : ℝ) :
    PFDev σ β κ φ (fun t => c * (1 - μ) * (μ / β) ^ t) (fun t => c * κ * (μ / β) ^ t) := by
  intro t
  have hβμ : β * (μ / β) = μ := mul_div_cancel₀ μ hβ
  have hbr : (1 - μ) - (1 - μ) * (μ / β) + σ * φ * κ - σ * κ * (μ / β) = 0 := by
    field_simp
    linear_combination hμ
  simp only
  rw [pow_succ]
  exact ⟨by linear_combination (-(c * κ * (μ / β) ^ t)) * hβμ,
    by linear_combination (c * (μ / β) ^ t) * hbr⟩

/-- For the eigen-solution, discounted output is `βᵗ x̃_t = c(1 − μ)μᵗ`. -/
theorem eigen_scaled {β μ : ℝ} (hβ : β ≠ 0) (c : ℝ) (t : ℕ) :
    β ^ t * (c * (1 - μ) * (μ / β) ^ t) = c * (1 - μ) * μ ^ t := by
  rw [div_pow]
  field_simp

/-- Cochrane (2023), p. 421: a real root `μ > 1` gives a deviation with `βᵗ x̃_t → +∞`. -/
theorem explode_of_root {σ β κ φ μ : ℝ} (hβ : 0 < β) (hμ1 : 1 < μ)
    (hμ : μ ^ 2 - (1 + β + σ * κ) * μ + β * (1 + σ * κ * φ) = 0) :
    ∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ Tendsto (fun t => β ^ t * x t) atTop atTop := by
  refine ⟨_, _, eigen_pfDev hβ.ne' hμ (-1), ?_⟩
  have h := Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < μ - 1)
    (tendsto_pow_atTop_atTop_of_one_lt hμ1)
  refine h.congr fun t => ?_
  rw [eigen_scaled hβ.ne']
  ring

/-- Cochrane (2023), p. 421 (as in `TaylorDeterminacy.real_explosion`): for `φ < 1/β` the
characteristic polynomial has a real root above one. -/
theorem root_of_lt {σ β κ φ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hφβ : φ < 1 / β) :
    ∃ μ : ℝ, 1 < μ ∧ μ ^ 2 - (1 + β + σ * κ) * μ + β * (1 + σ * κ * φ) = 0 := by
  set A := 1 + β + σ * κ with hA
  set B := β * (1 + σ * κ * φ) with hB
  have hβφ : β * φ < 1 := by rwa [lt_div_iff₀ hβ, mul_comm] at hφβ
  have hq1 : 1 - A + B < 0 := by
    have : σ * κ * (β * φ - 1) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
    nlinarith
  have hdisc : (A - 2) ^ 2 < A ^ 2 - 4 * B := by nlinarith
  have hsq2 : Real.sqrt (A ^ 2 - 4 * B) ^ 2 = A ^ 2 - 4 * B :=
    Real.sq_sqrt (by nlinarith [sq_nonneg (A - 2)])
  have hlt : |A - 2| < Real.sqrt (A ^ 2 - 4 * B) :=
    (Real.lt_sqrt (abs_nonneg _)).mpr (by rw [sq_abs]; exact hdisc)
  refine ⟨(A + Real.sqrt (A ^ 2 - 4 * B)) / 2, ?_, ?_⟩
  · have := neg_abs_le (A - 2)
    linarith
  · nlinarith [hsq2]

/-- Cochrane (2023), A1 (1.57): with a non-negative discriminant the larger root
`(A + √(A² − 4B))/2` is a root and is at least `A/2`. -/
theorem root_of_disc {A B : ℝ} (hD : 4 * B ≤ A ^ 2) :
    ((A + Real.sqrt (A ^ 2 - 4 * B)) / 2) ^ 2 - A * ((A + Real.sqrt (A ^ 2 - 4 * B)) / 2) +
      B = 0 ∧ A / 2 ≤ (A + Real.sqrt (A ^ 2 - 4 * B)) / 2 := by
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A ^ 2 - 4 * B)
  refine ⟨by linear_combination hs / 4, ?_⟩
  have := Real.sqrt_nonneg (A ^ 2 - 4 * B)
  linarith

/-- Cochrane (2023), p. 420: the deviation path from arbitrary initial discounted values
`(y_0, q_0)`, iterating `y_{t+1} = (β + σκ) y_t + σ(βφ − 1) q_t`, `q_{t+1} = q_t − κ y_t`. -/
noncomputable def sPath (σ β κ φ y0 q0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (y0, q0)
  | t + 1 => ((β + σ * κ) * (sPath σ β κ φ y0 q0 t).1 +
      σ * (β * φ - 1) * (sPath σ β κ φ y0 q0 t).2,
      (sPath σ β κ φ y0 q0 t).2 - κ * (sPath σ β κ φ y0 q0 t).1)

/-- Cochrane (2023), p. 420: `x̃_t = y_t/βᵗ`, `π̃_t = q_t/βᵗ` from `sPath` solves the
deviation system (every pair of initial values is attained). -/
theorem sPath_pfDev {σ β κ φ : ℝ} (hβ : β ≠ 0) (y0 q0 : ℝ) :
    PFDev σ β κ φ (fun t => (sPath σ β κ φ y0 q0 t).1 / β ^ t)
      (fun t => (sPath σ β κ φ y0 q0 t).2 / β ^ t) := by
  intro t
  have hb : β ^ t ≠ 0 := pow_ne_zero t hβ
  simp only [sPath]
  rw [pow_succ]
  constructor <;> field_simp <;> ring

/-- The discounted output of the `sPath` deviation is `y_t`. -/
theorem sPath_scaled {σ β κ φ : ℝ} (hβ : β ≠ 0) (y0 q0 : ℝ) (t : ℕ) :
    β ^ t * ((sPath σ β κ φ y0 q0 t).1 / β ^ t) = (sPath σ β κ φ y0 q0 t).1 :=
  mul_div_cancel₀ _ (pow_ne_zero t hβ)

/-! ### Part 2: what holds for `φ ≥ 1/β` -/

/-- A bounded real sequence does not tend to `+∞`. -/
theorem not_atTop_of_bounded {y : ℕ → ℝ} (hb : ∃ M, ∀ t, |y t| ≤ M) :
    ¬ Tendsto y atTop atTop := by
  obtain ⟨M, hM⟩ := hb
  intro h
  obtain ⟨t, ht⟩ := (h.eventually_gt_atTop M).exists
  linarith [le_abs_self (y t), hM t]

/-- Cochrane (2023), p. 421: for `φ ≥ 1/β` and `β(1 + σκφ) < 1`, **every** perfect-foresight
deviation satisfies the real transversality condition `βᵗ x̃_t → 0`. -/
theorem all_tendsto_zero {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβφ : 1 ≤ β * φ) (hB : β * (1 + σ * κ * φ) < 1) {x π : ℕ → ℝ}
    (hd : PFDev σ β κ φ x π) : Tendsto (fun t => β ^ t * x t) atTop (𝓝 0) := by
  have ha := mul_pos hσ hκ
  rcases hβφ.eq_or_lt with h | h
  · have hy := y_at_inv_beta hd h.symm
    have hBe : β * (1 + σ * κ * φ) = β + σ * κ := by linear_combination (σ * κ) * h.symm
    have h0 : 0 ≤ β + σ * κ := by positivity
    have h1 : β + σ * κ < 1 := by linarith
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const (x 0)
    rw [zero_mul] at this
    exact this.congr fun t => (hy t).symm
  · have hrec := y_rec hd
    have hBpos : 0 < β * (1 + σ * κ * φ) := by
      have := mul_pos ha (by linarith : (0 : ℝ) < β * φ)
      nlinarith
    have hp : 0 < 1 - (1 + β + σ * κ) + β * (1 + σ * κ * φ) := by
      have := mul_pos ha (sub_pos.mpr h)
      nlinarith
    by_cases hD : (1 + β + σ * κ) ^ 2 < 4 * (β * (1 + σ * κ * φ))
    · exact complex_tendsto_zero hD hB hrec
    · push Not at hD
      exact real_tendsto_zero hD (by positivity) hBpos hp hB.le hrec

/-- Cochrane (2023), p. 421: for `φ ≥ 1/β` and `β(1 + σκφ) ≤ 1`, every perfect-foresight
deviation has bounded discounted output `βᵗ x̃_t` (no real explosion). -/
theorem all_bounded {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβφ : 1 ≤ β * φ) (hB : β * (1 + σ * κ * φ) ≤ 1) {x π : ℕ → ℝ}
    (hd : PFDev σ β κ φ x π) : ∃ M, ∀ t, |β ^ t * x t| ≤ M := by
  have ha := mul_pos hσ hκ
  rcases hβφ.eq_or_lt with h | h
  · have hy := y_at_inv_beta hd h.symm
    have hBe : β * (1 + σ * κ * φ) = β + σ * κ := by linear_combination (σ * κ) * h.symm
    have h0 : 0 ≤ β + σ * κ := by positivity
    have h1 : β + σ * κ ≤ 1 := by linarith
    refine ⟨|x 0|, fun t => ?_⟩
    rw [hy t, abs_mul, abs_of_nonneg (pow_nonneg h0 t)]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ h0 h1)
  · have hrec := y_rec hd
    have hBpos : 0 < β * (1 + σ * κ * φ) := by
      have := mul_pos ha (by linarith : (0 : ℝ) < β * φ)
      nlinarith
    have hp : 0 < 1 - (1 + β + σ * κ) + β * (1 + σ * κ * φ) := by
      have := mul_pos ha (sub_pos.mpr h)
      nlinarith
    by_cases hD : (1 + β + σ * κ) ^ 2 < 4 * (β * (1 + σ * κ * φ))
    · exact complex_bounded hD hB hrec
    · push Not at hD
      exact bounded_of_tendsto (real_tendsto_zero hD (by positivity) hBpos hp hB hrec)

/-- The discounted values of the `sPath` deviation started at `(y_0, q_0) = (0, 1)` give
`Q(y_0, y_1) = (σ(βφ − 1))²`. -/
theorem sPath_Q {σ β κ φ : ℝ} (hβ : β ≠ 0) :
    Qf (1 + β + σ * κ) (β * (1 + σ * κ * φ))
        (β ^ 0 * ((sPath σ β κ φ 0 1 0).1 / β ^ 0))
        (β ^ (0 + 1) * ((sPath σ β κ φ 0 1 (0 + 1)).1 / β ^ (0 + 1))) =
      (σ * (β * φ - 1)) ^ 2 := by
  rw [sPath_scaled hβ, sPath_scaled hβ]
  simp only [sPath, Qf]
  ring

/-- Cochrane (2023), p. 421: for `σ, κ, β > 0` and every `φ`, some perfect-foresight deviation
has discounted output `βᵗ x̃_t → +∞` iff `φ < 1/β`, or `β + σκ > 1` and the characteristic
roots are real, `4β(1 + σκφ) ≤ (1 + β + σκ)²`. -/
theorem explodes_pf_iff {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ Tendsto (fun t => β ^ t * x t) atTop atTop) ↔
      φ < 1 / β ∨ (1 < β + σ * κ ∧ 4 * (β * (1 + σ * κ * φ)) ≤ (1 + β + σ * κ) ^ 2) := by
  have ha := mul_pos hσ hκ
  constructor
  · rintro ⟨x, π, hd, ht⟩
    by_contra hc
    push Not at hc
    obtain ⟨hφ, hc2⟩ := hc
    have hβφ : 1 ≤ β * φ := by rw [div_le_iff₀ hβ] at hφ; linarith
    rcases hβφ.eq_or_lt with h | h
    · have hBe : β * (1 + σ * κ * φ) = β + σ * κ := by linear_combination (σ * κ) * h.symm
      have hs : β + σ * κ ≤ 1 := by
        by_contra hs
        push Not at hs
        have := hc2 hs
        rw [hBe] at this
        nlinarith [sq_nonneg (1 - (β + σ * κ))]
      exact not_atTop_of_bounded (all_bounded hσ hκ hβ hβφ (by linarith) hd) ht
    · by_cases hD : (1 + β + σ * κ) ^ 2 < 4 * (β * (1 + σ * κ * φ))
      · exact complex_not_atTop hD (y_rec hd) ht
      · push Not at hD
        have hs : β + σ * κ ≤ 1 := by
          by_contra hs
          push Not at hs
          linarith [hc2 hs]
        have hB1 : β * (1 + σ * κ * φ) ≤ 1 := by nlinarith
        exact not_atTop_of_bounded (all_bounded hσ hκ hβ hβφ hB1 hd) ht
  · rintro (h | ⟨h1, h2⟩)
    · obtain ⟨μ, hμ1, hμ⟩ := root_of_lt ha hβ h
      exact explode_of_root hβ hμ1 hμ
    · obtain ⟨hμ, hμA⟩ := root_of_disc h2
      exact explode_of_root hβ (by linarith) hμ

/-- Cochrane (2023), p. 421: some perfect-foresight deviation has `βᵗ x̃_t` unbounded iff
`φ < 1/β` or `β(1 + σκφ) > 1`. -/
theorem unbounded_pf_iff {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ ¬ ∃ M, ∀ t, |β ^ t * x t| ≤ M) ↔
      φ < 1 / β ∨ 1 < β * (1 + σ * κ * φ) := by
  have ha := mul_pos hσ hκ
  have hlt : φ < 1 / β → ∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ ¬ ∃ M, ∀ t, |β ^ t * x t| ≤ M :=
    fun h => by
      obtain ⟨x, π, hd, ht⟩ := (explodes_pf_iff hσ hκ hβ).mpr (Or.inl h)
      exact ⟨x, π, hd, fun hb => not_atTop_of_bounded hb ht⟩
  constructor
  · rintro ⟨x, π, hd, hu⟩
    by_contra hc
    push Not at hc
    obtain ⟨hφ, hB⟩ := hc
    have hβφ : 1 ≤ β * φ := by rw [div_le_iff₀ hβ] at hφ; linarith
    exact hu (all_bounded hσ hκ hβ hβφ hB hd)
  · rintro (h | h)
    · exact hlt h
    · by_cases hφ : φ < 1 / β
      · exact hlt hφ
      push Not at hφ
      have hβφ : 1 ≤ β * φ := by rw [div_le_iff₀ hβ] at hφ; linarith
      rcases hβφ.eq_or_lt with h1 | h1
      · have hBe : β * (1 + σ * κ * φ) = β + σ * κ := by linear_combination (σ * κ) * h1.symm
        have hμ : (β + σ * κ) ^ 2 - (1 + β + σ * κ) * (β + σ * κ) +
            β * (1 + σ * κ * φ) = 0 := by rw [hBe]; ring
        obtain ⟨x, π, hd, ht⟩ := explode_of_root hβ (by linarith) hμ
        exact ⟨x, π, hd, fun hb => not_atTop_of_bounded hb ht⟩
      · refine ⟨_, _, sPath_pfDev hβ.ne' 0 1, unbounded_of_Q h (y_rec (sPath_pfDev hβ.ne' 0 1))
          ?_⟩
        rw [sPath_Q hβ.ne']
        exact pow_pos (mul_pos hσ (sub_pos.mpr h1)) 2

/-- Cochrane (2023), p. 421 (the real transversality condition `βᵗ x̃_t → 0`): some
perfect-foresight deviation violates it iff `φ < 1/β` or `β(1 + σκφ) ≥ 1`. -/
theorem tvc_fails_pf_iff {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ ¬ Tendsto (fun t => β ^ t * x t) atTop (𝓝 0)) ↔
      φ < 1 / β ∨ 1 ≤ β * (1 + σ * κ * φ) := by
  have ha := mul_pos hσ hκ
  have hub : (∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ ¬ ∃ M, ∀ t, |β ^ t * x t| ≤ M) →
      ∃ x π : ℕ → ℝ, PFDev σ β κ φ x π ∧ ¬ Tendsto (fun t => β ^ t * x t) atTop (𝓝 0) := by
    rintro ⟨x, π, hd, hu⟩
    exact ⟨x, π, hd, fun h => hu (bounded_of_tendsto h)⟩
  constructor
  · rintro ⟨x, π, hd, hn⟩
    by_contra hc
    push Not at hc
    obtain ⟨hφ, hB⟩ := hc
    have hβφ : 1 ≤ β * φ := by rw [div_le_iff₀ hβ] at hφ; linarith
    exact hn (all_tendsto_zero hσ hκ hβ hβφ hB hd)
  · rintro (h | h)
    · exact hub ((unbounded_pf_iff hσ hκ hβ).mpr (Or.inl h))
    · by_cases hφ : φ < 1 / β
      · exact hub ((unbounded_pf_iff hσ hκ hβ).mpr (Or.inl hφ))
      push Not at hφ
      have hβφ : 1 ≤ β * φ := by rw [div_le_iff₀ hβ] at hφ; linarith
      rcases h.eq_or_lt with hB | hB
      · rcases hβφ.eq_or_lt with h1 | h1
        · have hBe : β * (1 + σ * κ * φ) = β + σ * κ := by
            linear_combination (σ * κ) * h1.symm
          have hd := sPath_pfDev (σ := σ) (κ := κ) (φ := φ) hβ.ne' 1 0
          refine ⟨_, _, hd, fun ht => ?_⟩
          have hy := y_at_inv_beta hd h1.symm
          obtain ⟨t, htt⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
          rw [hy t] at htt
          simp only [sPath, pow_zero, div_one, mul_one] at htt
          have : 1 ≤ (β + σ * κ) ^ t := one_le_pow₀ (by linarith)
          linarith
        · refine ⟨_, _, sPath_pfDev hβ.ne' 0 1,
            not_tendsto_zero_of_Q hB.symm (y_rec (sPath_pfDev hβ.ne' 0 1)) ?_⟩
          rw [sPath_Q hβ.ne']
          exact (pow_pos (mul_pos hσ (sub_pos.mpr h1)) 2).ne'
      · exact hub ((unbounded_pf_iff hσ hκ hβ).mpr (Or.inr hB))

/-! ### Part 2: the statements for the deviation system (17.29)–(17.32) -/

/-- Cochrane (2023), p. 421 ("real explosions faster than the interest rate so
`E_t βʲ x_{t+j} → ∞`"), in full: for `σ, κ, β > 0` and **every** `φ`, the perfect-foresight
deviation system (17.29)–(17.32) has a solution with `βᵗ x̃_t → +∞` iff `φ < 1/β` (covered by
`TaylorDeterminacy.real_explosion`) or `β + σκ > 1` and `4β(1 + σκφ) ≤ (1 + β + σκ)²`. -/
theorem explodes_atTop_iff {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ 0 i r x π ∧
        Tendsto (fun t => β ^ t * x t ()) atTop atTop) ↔
      φ < 1 / β ∨ (1 < β + σ * κ ∧ 4 * (β * (1 + σ * κ * φ)) ≤ (1 + β + σ * κ) ^ 2) :=
  (exists_deviation_iff σ β κ φ fun y => Tendsto (fun t => β ^ t * y t) atTop atTop).trans
    (explodes_pf_iff hσ hκ hβ)

/-- Cochrane (2023), p. 421: the same condition characterises `βᵗ x̃_t → −∞` (the deviation
system is linear). -/
theorem explodes_atBot_iff {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ 0 i r x π ∧
        Tendsto (fun t => β ^ t * x t ()) atTop atBot) ↔
      φ < 1 / β ∨ (1 < β + σ * κ ∧ 4 * (β * (1 + σ * κ * φ)) ≤ (1 + β + σ * κ) ^ 2) := by
  refine (exists_deviation_iff σ β κ φ fun y => Tendsto (fun t => β ^ t * y t) atTop atBot
    ).trans (Iff.trans ?_ (explodes_pf_iff hσ hκ hβ))
  constructor
  · rintro ⟨x, π, hd, ht⟩
    refine ⟨_, _, pfDev_neg hd, ?_⟩
    simp only [mul_neg]
    exact tendsto_neg_atTop_iff.mpr ht
  · rintro ⟨x, π, hd, ht⟩
    refine ⟨_, _, pfDev_neg hd, ?_⟩
    simp only [mul_neg]
    exact tendsto_neg_atBot_iff.mpr ht

/-- Cochrane (2023), p. 421 (real explosion as unboundedness of `βᵗ x̃_t`): for `σ, κ, β > 0`
and every `φ`, some perfect-foresight deviation has `βᵗ x̃_t` unbounded iff `φ < 1/β` or
`β(1 + σκφ) > 1`; for `φ ≥ 1/β` the explosion is oscillating whenever the roots are complex. -/
theorem unbounded_iff {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ 0 i r x π ∧
        ¬ ∃ M, ∀ t, |β ^ t * x t ()| ≤ M) ↔
      φ < 1 / β ∨ 1 < β * (1 + σ * κ * φ) :=
  (exists_deviation_iff σ β κ φ fun y => ¬ ∃ M, ∀ t, |β ^ t * y t| ≤ M).trans
    (unbounded_pf_iff hσ hκ hβ)

/-- Cochrane (2023), p. 421 ("one might rule out such solutions by appeal to the real
transversality condition"): for `σ, κ, β > 0` and every `φ`, some perfect-foresight deviation
violates `βᵗ x̃_t → 0` iff `φ < 1/β` or `β(1 + σκφ) ≥ 1`. -/
theorem tvc_fails_iff {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ 0 i r x π ∧
        ¬ Tendsto (fun t => β ^ t * x t ()) atTop (𝓝 0)) ↔
      φ < 1 / β ∨ 1 ≤ β * (1 + σ * κ * φ) :=
  (exists_deviation_iff σ β κ φ fun y => ¬ Tendsto (fun t => β ^ t * y t) atTop (𝓝 0)).trans
    (tvc_fails_pf_iff hσ hκ hβ)

/-! ### Part 2: counterexamples to the printed form -/

/-- Cochrane (2023), p. 421, at the calibration of Fig. 17.8, p. 416 (`β = 0.95`, `σ = 1`,
`κ = 1/2`, `φ = 1.5 ≥ 1/β`): real explosions exist (`βᵗ x̃_t` unbounded), but no deviation has
`βᵗ x̃_t → +∞` or `→ −∞` — the roots are complex and every real explosion oscillates. -/
theorem book_calibration_oscillates :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight 1 (19 / 20) (1 / 2) (3 / 2) 0 i r x π ∧
        ¬ ∃ M, ∀ t, |(19 / 20 : ℝ) ^ t * x t ()| ≤ M) ∧
      (¬ ∃ i r x π : ℕ → Unit → ℝ,
        Deviation perfectForesight 1 (19 / 20) (1 / 2) (3 / 2) 0 i r x π ∧
          Tendsto (fun t => (19 / 20 : ℝ) ^ t * x t ()) atTop atTop) ∧
      ¬ ∃ i r x π : ℕ → Unit → ℝ,
        Deviation perfectForesight 1 (19 / 20) (1 / 2) (3 / 2) 0 i r x π ∧
          Tendsto (fun t => (19 / 20 : ℝ) ^ t * x t ()) atTop atBot := by
  refine ⟨(unbounded_iff one_pos (by norm_num) (by norm_num)).mpr (Or.inr (by norm_num)),
    fun h => ?_, fun h => ?_⟩
  · rcases (explodes_atTop_iff one_pos (by norm_num) (by norm_num)).mp h with h | ⟨_, h⟩ <;>
      norm_num at h
  · rcases (explodes_atBot_iff one_pos (by norm_num) (by norm_num)).mp h with h | ⟨_, h⟩ <;>
      norm_num at h

/-- Cochrane (2023), p. 421, at the calibration of Fig. 17.7, p. 413 (`β = 0.95`, `σ = 1`,
`κ = 0.25`, `φ = 1.2 ≥ 1/β`): real explosions exist but none has `βᵗ x̃_t → ±∞`. -/
theorem fig17_7_calibration_oscillates :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight 1 (19 / 20) (1 / 4) (6 / 5) 0 i r x π ∧
        ¬ ∃ M, ∀ t, |(19 / 20 : ℝ) ^ t * x t ()| ≤ M) ∧
      (¬ ∃ i r x π : ℕ → Unit → ℝ,
        Deviation perfectForesight 1 (19 / 20) (1 / 4) (6 / 5) 0 i r x π ∧
          Tendsto (fun t => (19 / 20 : ℝ) ^ t * x t ()) atTop atTop) ∧
      ¬ ∃ i r x π : ℕ → Unit → ℝ,
        Deviation perfectForesight 1 (19 / 20) (1 / 4) (6 / 5) 0 i r x π ∧
          Tendsto (fun t => (19 / 20 : ℝ) ^ t * x t ()) atTop atBot := by
  refine ⟨(unbounded_iff one_pos (by norm_num) (by norm_num)).mpr (Or.inr (by norm_num)),
    fun h => ?_, fun h => ?_⟩
  · rcases (explodes_atTop_iff one_pos (by norm_num) (by norm_num)).mp h with h | ⟨_, h⟩ <;>
      norm_num at h
  · rcases (explodes_atBot_iff one_pos (by norm_num) (by norm_num)).mp h with h | ⟨_, h⟩ <;>
      norm_num at h

/-- Cochrane (2023), p. 421 ("one might rule out such solutions by appeal to the real
transversality condition"), counterexample: at `β = 0.95`, `σ = 1`, `κ = 1/25`, `φ = 1.2` the
deviation system is determinate (`φ > 1`), so a nonzero deviation is an explosion, yet **every**
perfect-foresight deviation satisfies the real transversality condition `βᵗ x̃_t → 0`. -/
theorem tvc_cannot_rule_out :
    (∀ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight 1 (19 / 20) (1 / 25) (6 / 5) 0 i r x π →
        Tendsto (fun t => (19 / 20 : ℝ) ^ t * x t ()) atTop (𝓝 0)) ∧
      Determinate perfectForesight 1 (19 / 20) (1 / 25) (6 / 5) 0 ∧
      ∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight 1 (19 / 20) (1 / 25) (6 / 5) 0 i r x π ∧
        ¬ (BoundedProc x ∧ BoundedProc π) := by
  have hdet : Determinate perfectForesight 1 (19 / 20) (1 / 25) (6 / 5) 0 :=
    (determinate_iff_phi perfectForesight one_pos (by norm_num) (by norm_num) (by norm_num)).mpr
      (Or.inl (by norm_num))
  refine ⟨fun i r x π hd => ?_, hdet, ?_⟩
  · by_contra hn
    rcases (tvc_fails_iff one_pos (by norm_num) (by norm_num)).mp ⟨i, r, x, π, hd, hn⟩ with h | h
      <;> norm_num at h
  · have hp := sPath_pfDev (σ := 1) (κ := 1 / 25) (φ := 6 / 5) (by norm_num : (19 / 20 : ℝ) ≠ 0)
      0 1
    set X : ℕ → ℝ := fun t => (sPath 1 (19 / 20) (1 / 25) (6 / 5) 0 1 t).1 / (19 / 20) ^ t
      with hX
    set P : ℕ → ℝ := fun t => (sPath 1 (19 / 20) (1 / 25) (6 / 5) 0 1 t).2 / (19 / 20) ^ t
      with hP
    have hdev := (deviation_iff_pfDev 1 (19 / 20) (1 / 25) (6 / 5) (fun t _ => 6 / 5 * P t)
      (fun t _ => 6 / 5 * P t - P (t + 1)) (fun t _ => X t) (fun t _ => P t)).mpr
        ⟨fun _ => rfl, fun _ => rfl, hp⟩
    refine ⟨_, _, _, _, hdev, fun ⟨hbx, hbπ⟩ => ?_⟩
    have h0 := (hdet _ _ _ _ (fun _ => rfl) (fun _ => rfl) hbx hbπ hdev).2
    have := congrFun (congrFun h0 0) ()
    rw [hP] at this
    simp [sPath] at this

/-- Cochrane (2023), p. 421: at `φ = 1/β` (`0 < β < 1`) there is always a purely nominal
explosion, `x̃ = 0`, `π̃_t = β^{−t} → ∞`: inflation explodes with no real explosion at all. -/
theorem nominal_only_at_inv_beta {σ β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    PFDev σ β κ (1 / β) (fun _ => 0) (fun t => β⁻¹ ^ t) ∧
      Tendsto (fun t : ℕ => β⁻¹ ^ t) atTop atTop := by
  refine ⟨fun t => ⟨?_, ?_⟩, tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hβ).mpr hβ1)⟩
  · simp only
    rw [pow_succ]
    field_simp
    ring
  · simp only
    rw [pow_succ]
    field_simp
    ring

end Cochrane.KeynesianStickyPrices.FullModelTidy
