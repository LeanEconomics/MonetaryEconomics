/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ForwardSolution
import GainsFromCommitment.Sequences
import Mathlib.Analysis.Real.Sqrt

/-!
# The second-order expectational difference equation

Woodford (2003), *Interest and Prices*, Chapter 7, eqs. (1.10)–(1.12), pp. 472–473, eq. (2.7),
p. 489, eq. (2.29), p. 505, and Appendix F, eq. (F.10), p. 713 (the workhorse of Chapter 7).

For `β > 0` and `c > 0` the equation

  `β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t`,  `t ≥ 0`, with `y_{−1}` given,

has, for every bounded adapted forcing process `f`, exactly one bounded adapted solution, namely

  `y_t = μ₁ y_{t−1} − β⁻¹ ∑_{j ≥ 0} μ₂^{−j−1} E_t f_{t+j}`,

where `0 < μ₁ < 1 < μ₂` are the roots of `βμ² − (1 + β + c)μ + 1` (eq. (1.11)). Everything is
stated for an arbitrary `ExpectationSystem`, so the results hold under perfect foresight and under
genuine uncertainty; a start date `t₀ > 0` is handled by the shifted system `shiftSys 𝔼 t₀`.

## Main results

* Root facts: `mu1_mul_mu2` (`μ₁μ₂ = β⁻¹`), `beta_mul_sum`, `root_location`
  (`0 < μ₁ < 1 < μ₂`), `beta_one_sub_mul_one_sub` (`β(1 − μ₁)(1 − μ₂) = −c`), `inv_mu2`.
* `forward_inverse`: for `|a| < 1` the forward sum `∑ aʲ E_t g_{t+j}` is the unique bounded
  solution of `v_t = g_t + a E_t v_{t+1}`, and it is bounded and adapted.
* `backward_unique`, `backward_eq_sum`, `backward_bounded`, `backward_adapted`: the backward
  equation `y_t = μ y_{t−1} + h_t` given `y_{−1}`.
* `secondOrder_iff_factored`: the factorisation `(1 − μ₂⁻¹ L⁻¹)(1 − μ₁ L) y = −(βμ₂)⁻¹ f`.
* `bounded_solution_unique`, `eq_solution`, `solution_formula`: existence, uniqueness and the
  explicit formula; `bounded_solution_unique_det`: the deterministic special case;
  `bounded_solution_unique_from`: an arbitrary start date.
* `eq_constant_forcing`: with constant forcing `F` the solution is
  `y_t = ȳ + μ₁^{t+1}(y_{−1} − ȳ)`, `ȳ = −F/c` (used for (1.12)).
-/

namespace Woodford.GainsFromCommitment.SecondOrderRE

open Filter Topology
open Sequences (lagged lagged_zero lagged_succ)

/-! ### The roots of `βμ² − (1 + β + c)μ + 1` -/

/-- Woodford (2003), eq. (1.11), p. 472: the characteristic polynomial
`P(μ) = βμ² − (1 + β + c)μ + 1` (with `c = κ²/λ` in (1.11)). -/
def charPoly (β c μ : ℝ) : ℝ := β * μ ^ 2 - (1 + β + c) * μ + 1

/-- Woodford (2003), eq. (1.11), p. 472: the discriminant `(1 + β + c)² − 4β` of (1.11). -/
def disc (β c : ℝ) : ℝ := (1 + β + c) ^ 2 - 4 * β

/-- Woodford (2003), p. 473: the smaller root `μ₁ = ((1 + β + c) − √disc)/(2β)` of (1.11). -/
noncomputable def mu1 (β c : ℝ) : ℝ := ((1 + β + c) - Real.sqrt (disc β c)) / (2 * β)

/-- Woodford (2003), p. 473: the larger root `μ₂ = ((1 + β + c) + √disc)/(2β)` of (1.11). -/
noncomputable def mu2 (β c : ℝ) : ℝ := ((1 + β + c) + Real.sqrt (disc β c)) / (2 * β)

/-- Woodford (2003), eq. (1.11), p. 472: the discriminant is positive for `β, c > 0`. -/
theorem disc_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < disc β c := by
  unfold disc
  nlinarith [sq_nonneg (1 - β)]

/-- Woodford (2003), p. 473 (Vieta): `μ₁ + μ₂ = (1 + β + c)/β`. -/
theorem mu1_add_mu2 {β c : ℝ} (hβ : 0 < β) : mu1 β c + mu2 β c = (1 + β + c) / β := by
  unfold mu1 mu2
  field_simp
  ring

/-- Woodford (2003), p. 473 (Vieta, cleared of `β`): `β(μ₁ + μ₂) = 1 + β + c`. -/
theorem beta_mul_sum {β c : ℝ} (hβ : 0 < β) : β * (mu1 β c + mu2 β c) = 1 + β + c := by
  rw [mu1_add_mu2 hβ]
  field_simp

/-- Woodford (2003), p. 473 (Vieta, cleared of `β`): `βμ₁μ₂ = 1`. -/
theorem beta_mul_prod {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : β * (mu1 β c * mu2 β c) = 1 := by
  have h := Real.sq_sqrt (disc_pos hβ hc).le
  unfold mu1 mu2
  generalize Real.sqrt (disc β c) = s at h ⊢
  unfold disc at h
  field_simp
  linear_combination (-1 : ℝ) * h

/-- Woodford (2003), survey §4.3 (Vieta): `μ₁μ₂ = β⁻¹`. -/
theorem mu1_mul_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : mu1 β c * mu2 β c = β⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (beta_mul_prod hβ hc)

/-- Woodford (2003), eq. (1.11), p. 472: the factorisation `P(μ) = β(μ − μ₁)(μ − μ₂)`. -/
theorem charPoly_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (μ : ℝ) :
    charPoly β c μ = β * (μ - mu1 β c) * (μ - mu2 β c) := by
  have hs := beta_mul_sum (c := c) hβ
  have hp := beta_mul_prod hβ hc
  unfold charPoly
  linear_combination μ * hs - hp

/-- Woodford (2003), eq. (1.11), p. 472: `μ₁` is a root. -/
theorem charPoly_mu1 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : charPoly β c (mu1 β c) = 0 := by
  rw [charPoly_factor hβ hc]; ring

/-- Woodford (2003), eq. (1.11), p. 472: `μ₂` is a root. -/
theorem charPoly_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : charPoly β c (mu2 β c) = 0 := by
  rw [charPoly_factor hβ hc]; ring

/-- Woodford (2003), eq. (1.11), p. 472: `μ₁` and `μ₂` are the only roots. -/
theorem charPoly_eq_zero_iff {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (μ : ℝ) :
    charPoly β c μ = 0 ↔ μ = mu1 β c ∨ μ = mu2 β c := by
  rw [charPoly_factor hβ hc, mul_assoc, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  exact ⟨fun h => h.resolve_left hβ.ne', Or.inr⟩

/-- Woodford (2003), p. 473: `μ₁ < μ₂`. -/
theorem mu1_lt_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : mu1 β c < mu2 β c := by
  have h := Real.sqrt_pos.mpr (disc_pos hβ hc)
  unfold mu1 mu2
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- Woodford (2003), p. 472: `P(1) = −c`. -/
theorem charPoly_one (β c : ℝ) : charPoly β c 1 = -c := by
  unfold charPoly; ring

/-- Woodford (2003), p. 473, survey §4.3: `β(1 − μ₁)(1 − μ₂) = −c`. -/
theorem beta_one_sub_mul_one_sub {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    β * (1 - mu1 β c) * (1 - mu2 β c) = -c := by
  rw [← charPoly_one β c, charPoly_factor hβ hc]

/-- Woodford (2003), p. 473: `μ₁ < 1 < μ₂` (the polynomial is negative at `1`). -/
theorem mu1_lt_one_lt_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    mu1 β c < 1 ∧ 1 < mu2 β c := by
  have h := beta_one_sub_mul_one_sub hβ hc
  have hlt := mu1_lt_mu2 hβ hc
  have hneg : (1 - mu1 β c) * (1 - mu2 β c) < 0 := by
    have : β * ((1 - mu1 β c) * (1 - mu2 β c)) < 0 := by rw [← mul_assoc, h]; linarith
    exact neg_of_mul_neg_right this hβ.le
  rcases mul_neg_iff.mp hneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith, by linarith⟩
  · exact absurd hlt (by linarith)

/-- Woodford (2003), p. 473, eq. (1.11) (**root location**): `0 < μ₁ < 1 < μ₂`. -/
theorem root_location {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    0 < mu1 β c ∧ mu1 β c < 1 ∧ 1 < mu2 β c := by
  obtain ⟨h1, h2⟩ := mu1_lt_one_lt_mu2 hβ hc
  refine ⟨?_, h1, h2⟩
  have hp := beta_mul_prod hβ hc
  by_contra hn
  push Not at hn
  have : β * (mu1 β c * mu2 β c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hβ.le (mul_nonpos_of_nonpos_of_nonneg hn (by linarith))
  linarith

/-- Woodford (2003), p. 473: `μ₁ > 0`. -/
theorem mu1_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < mu1 β c := (root_location hβ hc).1

/-- Woodford (2003), p. 473: `μ₁ < 1`. -/
theorem mu1_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : mu1 β c < 1 := (root_location hβ hc).2.1

/-- Woodford (2003), p. 473: `μ₂ > 1`. -/
theorem one_lt_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 1 < mu2 β c := (root_location hβ hc).2.2

/-- Woodford (2003), survey §4.3: `μ₂⁻¹ = βμ₁`. -/
theorem inv_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : (mu2 β c)⁻¹ = β * mu1 β c := by
  have hp := beta_mul_prod hβ hc
  exact (eq_inv_of_mul_eq_one_left (by linear_combination hp)).symm

/-- Woodford (2003), survey §4.3: `(βμ₂)⁻¹ = μ₁`. -/
theorem inv_beta_mul_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : (β * mu2 β c)⁻¹ = mu1 β c := by
  exact (eq_inv_of_mul_eq_one_left (by linear_combination beta_mul_prod hβ hc)).symm

/-- Woodford (2003), p. 472 (Vieta, in the form used for (2.6)–(2.7)): `β μ₁ μ₂ = 1`. -/
theorem beta_mul_mu1_mul_mu2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    β * mu1 β c * mu2 β c = 1 := by
  rw [mul_assoc]; exact beta_mul_prod hβ hc

/-- Woodford (2003), p. 489 (survey §1): `β (1 − μ₁)(μ₂ − 1) = c`. -/
theorem mu_key {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    β * (1 - mu1 β c) * (mu2 β c - 1) = c := by
  linear_combination -(beta_one_sub_mul_one_sub hβ hc)

/-- Woodford (2003), eq. (1.11), p. 472: both roots solve `β μ² − (1 + β + c) μ + 1 = 0`. -/
theorem mu_roots {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    β * mu1 β c ^ 2 - (1 + β + c) * mu1 β c + 1 = 0 ∧
      β * mu2 β c ^ 2 - (1 + β + c) * mu2 β c + 1 = 0 :=
  ⟨charPoly_mu1 hβ hc, charPoly_mu2 hβ hc⟩

/-- Woodford (2003), eq. (1.11), p. 472: `(1 + β + c − s)(1 + β + c + s) = 4β` for the square
root `s` of the discriminant. -/
theorem root_prod_aux {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    (1 + β + c - Real.sqrt (disc β c)) * (1 + β + c + Real.sqrt (disc β c)) = 4 * β := by
  have hs := Real.sq_sqrt (disc_pos hβ hc).le
  unfold disc at hs ⊢
  linear_combination -hs

/-- Woodford (2003), p. 473: the square root of the discriminant exceeds `|1 − β + c|`. -/
theorem sqrt_disc_gt {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    |1 - β + c| < Real.sqrt (disc β c) := by
  have hs := Real.sq_sqrt (disc_pos hβ hc).le
  have hs0 := Real.sqrt_nonneg (disc β c)
  have hsq : (1 - β + c) ^ 2 < Real.sqrt (disc β c) ^ 2 := by
    rw [hs]
    unfold disc
    nlinarith
  exact abs_lt_of_sq_lt_sq hsq hs0

/-- Woodford (2003), p. 471: `P(x) < 0` forces `μ₁ < x < μ₂`. -/
theorem between_roots_of_neg {β c x : ℝ} (hβ : 0 < β) (hc : 0 < c) (hx : charPoly β c x < 0) :
    mu1 β c < x ∧ x < mu2 β c := by
  rw [charPoly_factor hβ hc] at hx
  have h12 := mu1_lt_mu2 hβ hc
  constructor
  · by_contra h
    push Not at h
    have : 0 ≤ β * (x - mu1 β c) * (x - mu2 β c) :=
      mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith))
        (by linarith)
    linarith
  · by_contra h
    push Not at h
    have : 0 ≤ β * (x - mu1 β c) * (x - mu2 β c) :=
      mul_nonneg (mul_nonneg hβ.le (by linarith)) (by linarith)
    linarith

/-- Woodford (2003), eq. (1.12), p. 473: `1 − (1 + c)μ₁ = βμ₁(1 − μ₁) > 0`, i.e.
`(1 + c)μ₁ < 1` (used to rank the inflation paths of Figure 7.1). -/
theorem one_add_mul_mu1_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : (1 + c) * mu1 β c < 1 := by
  have h := charPoly_mu1 hβ hc
  have h0 := mu1_pos hβ hc
  have h1 := mu1_lt_one hβ hc
  unfold charPoly at h
  nlinarith [mul_pos hβ (mul_pos h0 (sub_pos.mpr h1))]

/-- Woodford (2003), eq. (1.12), p. 473: `∑_{j ≥ 0} μ₂^{−j−1} = 1/(μ₂ − 1)`. -/
theorem hasSum_inv_mu2_pow {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    HasSum (fun j : ℕ => ((mu2 β c) ^ (j + 1))⁻¹) (mu2 β c - 1)⁻¹ := by
  have h1 := one_lt_mu2 hβ hc
  have hq0 : 0 ≤ (mu2 β c)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (mu2 β c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (mu2 β c)⁻¹
  have hval : (mu2 β c)⁻¹ * (1 - (mu2 β c)⁻¹)⁻¹ = (mu2 β c - 1)⁻¹ := by
    have : mu2 β c ≠ 0 := by linarith
    have : mu2 β c - 1 ≠ 0 := by linarith
    field_simp
  rw [hval] at hg
  refine hg.congr_fun fun j => ?_
  rw [← inv_pow, pow_succ']

/-! ### The shifted expectation system

The lag `lagged ym y` (with `y_{−1} = ym`) is the shared `Sequences.lagged`. -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), Ch. 7, §2.1, p. 489 (the commitment problem "from date `t₀` onward"): the
expectation system seen from date `s`, `E'_t = E_{s+t}`. Applying a date-0 result to it gives
the same result from an arbitrary start date `t₀ = s`. -/
def shiftSys (s : ℕ) : ExpectationSystem Ω where
  E t := 𝔼.E (s + t)
  const t c := 𝔼.const (s + t) c
  mono t _ _ h := 𝔼.mono (s + t) h
  tower h x := 𝔼.tower (Nat.add_le_add_left h s) x
  known h x := 𝔼.known (Nat.add_le_add_left h s) x

/-- Woodford (2003), Ch. 7, p. 489: `E'_t = E_{s+t}` in the shifted system. -/
@[simp] theorem shiftSys_E (s t : ℕ) : (shiftSys 𝔼 s).E t = 𝔼.E (s + t) := rfl

/-- Woodford (2003), Ch. 7, p. 489: the shifted system inherits the pull-out property. -/
theorem shiftSys_pullOut {s : ℕ} (h : 𝔼.PullOut) : (shiftSys 𝔼 s).PullOut :=
  fun t a y ha => h (s + t) a y ha

/-! ### The forward inverse -/

/-- Woodford (2003), survey §4.3, ingredient 2 (**forward-inverse lemma**; App. A, (A.16)):
for `|a| < 1` and a bounded adapted `g`, `v_t = ∑ aʲ E_t g_{t+j}` is bounded, adapted, solves
`v_t = g_t + a E_t v_{t+1}`, and is the only bounded solution of that equation. -/
theorem forward_inverse {a M : ℝ} (ha : |a| < 1) {g : ℕ → Ω → ℝ} (hg : ∀ t ω, |g t ω| ≤ M)
    (hga : 𝔼.Adapted g) :
    BoundedProc (𝔼.forwardSeries a g) ∧ 𝔼.Adapted (𝔼.forwardSeries a g) ∧
      (∀ t, 𝔼.forwardSeries a g t = g t + a • 𝔼.E t (𝔼.forwardSeries a g (t + 1))) ∧
      ∀ v, BoundedProc v → (∀ t, v t = g t + a • 𝔼.E t (v (t + 1))) →
        v = 𝔼.forwardSeries a g := by
  refine ⟨ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hg,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hg, fun t => ?_, fun v hvb hv => ?_⟩
  · rw [ForwardSolution.forwardSeries_solves_abs 𝔼 ha hg hga t, add_comm]
  · refine ForwardSolution.eq_forwardSeries_abs 𝔼 ha hg hga (fun t => ?_) hvb
    rw [hv t, add_comm]

/-! ### The backward equation `y_t = μ y_{t−1} + h_t` -/

/-- Woodford (2003), survey §4.3, ingredient 3: the solution of `y_t = μ y_{t−1} + h_t`
given `y_{−1}`, defined recursively. -/
def backward (μ : ℝ) (ym : Ω → ℝ) (h : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => μ • ym + h 0
  | t + 1 => μ • backward μ ym h t + h (t + 1)

/-- Woodford (2003), survey §4.3: `backward` solves `y_t = μ y_{t−1} + h_t` with
`y_{−1} = ym`. -/
theorem backward_spec (μ : ℝ) (ym : Ω → ℝ) (h : ℕ → Ω → ℝ) (t : ℕ) :
    backward μ ym h t = μ • lagged ym (backward μ ym h) t + h t := by
  cases t <;> rfl

/-- Woodford (2003), survey §4.3: the backward equation has exactly one solution given
`y_{−1}`. -/
theorem backward_unique {μ : ℝ} {ym : Ω → ℝ} {h y : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = μ • lagged ym y t + h t) : y = backward μ ym h := by
  funext t
  induction t with
  | zero => exact hy 0
  | succ t ih =>
    rw [hy (t + 1), lagged_succ, ih]
    rfl

/-- Woodford (2003), eq. (1.12), p. 473, survey §4.3: the explicit backward solution
`y_t = μ^{t+1} y_{−1} + ∑_{s ≤ t} μ^{t−s} h_s`. -/
theorem backward_eq_sum (μ : ℝ) (ym : Ω → ℝ) (h : ℕ → Ω → ℝ) (t : ℕ) :
    backward μ ym h t =
      μ ^ (t + 1) • ym + ∑ s ∈ Finset.range (t + 1), μ ^ (t - s) • h s := by
  induction t with
  | zero => simp [backward]
  | succ t ih =>
    rw [show backward μ ym h (t + 1) = μ • backward μ ym h t + h (t + 1) from rfl, ih,
      Finset.sum_range_succ _ (t + 1), Nat.sub_self, pow_zero, one_smul, smul_add, smul_smul,
      ← pow_succ', Finset.smul_sum, add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [smul_smul, ← pow_succ']
    congr 2
    have := Finset.mem_range.mp hs
    omega

/-- Woodford (2003), survey §4.3: for `|μ| < 1`, a bounded `y_{−1}` and bounded `h`, the backward
solution is bounded. -/
theorem backward_bounded {μ B M : ℝ} (hμ : |μ| < 1) {ym : Ω → ℝ} (hym : ∀ ω, |ym ω| ≤ B)
    {h : ℕ → Ω → ℝ} (hh : ∀ t ω, |h t ω| ≤ M) : BoundedProc (backward μ ym h) := by
  refine ⟨|B| + |M| / (1 - |μ|), fun t ω => ?_⟩
  have hd : 0 < 1 - |μ| := by linarith
  have hK : |M| ≤ (1 - |μ|) * (|B| + |M| / (1 - |μ|)) := by
    rw [mul_add, mul_div_cancel₀ _ hd.ne']
    nlinarith [abs_nonneg B, abs_nonneg μ]
  have hKnn : 0 ≤ |B| + |M| / (1 - |μ|) := by positivity
  have hstep : ∀ v : ℝ, |v| ≤ |B| + |M| / (1 - |μ|) → ∀ s,
      |μ * v + h s ω| ≤ |B| + |M| / (1 - |μ|) := by
    intro v hv s
    calc |μ * v + h s ω| ≤ |μ| * |v| + |M| := by
          rw [← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add le_rfl ((hh s ω).trans (le_abs_self M)))
      _ ≤ |μ| * (|B| + |M| / (1 - |μ|)) + |M| :=
          add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg μ)) le_rfl
      _ ≤ |B| + |M| / (1 - |μ|) := by nlinarith
  induction t with
  | zero =>
    exact hstep (ym ω) ((hym ω).trans ((le_abs_self B).trans (by
      have : 0 ≤ |M| / (1 - |μ|) := by positivity
      linarith))) 0
  | succ t ih => exact hstep _ ih (t + 1)

/-- Woodford (2003), survey §4.3: with `y_{−1}` known at date `0` and `h` adapted, the backward
solution is adapted. -/
theorem backward_adapted {μ : ℝ} {ym : Ω → ℝ} (hym : 𝔼.E 0 ym = ym) {h : ℕ → Ω → ℝ}
    (hh : 𝔼.Adapted h) : 𝔼.Adapted (backward μ ym h) := by
  intro t
  induction t with
  | zero =>
    change 𝔼.E 0 (μ • ym + h 0) = μ • ym + h 0
    rw [map_add, map_smul, hym, hh 0]
  | succ t ih =>
    change 𝔼.E (t + 1) (μ • backward μ ym h t + h (t + 1)) = μ • backward μ ym h t + h (t + 1)
    rw [map_add, map_smul, hh (t + 1), ← ih, 𝔼.known (Nat.le_succ t)]

/-! ### The second-order equation and its factorisation -/

/-- Woodford (2003), eq. (1.10), p. 472, eq. (2.7), p. 489, and (F.10), p. 713: `y` solves
`β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t` for all `t ≥ 0`, with `y_{−1} = ym`. -/
def SecondOrderEq (β c : ℝ) (f : ℕ → Ω → ℝ) (ym : Ω → ℝ) (y : ℕ → Ω → ℝ) : Prop :=
  ∀ t, β • 𝔼.E t (y (t + 1)) - (1 + β + c) • y t + lagged ym y t = f t

/-- Woodford (2003), survey §4.3, ingredient 4 (**factorisation**): for an adapted `y`, the
second-order equation is equivalent to the first-order forward equation
`w_t = μ₂⁻¹ E_t w_{t+1} − β⁻¹μ₂⁻¹ f_t` for the quasi-difference `w_t = y_t − μ₁ y_{t−1}`;
in lag-operator form, `(1 − μ₂⁻¹L⁻¹)(1 − μ₁L) y = −β⁻¹μ₂⁻¹ f`. -/
theorem secondOrder_iff_factored {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → Ω → ℝ}
    {ym : Ω → ℝ} {y : ℕ → Ω → ℝ} (hya : 𝔼.Adapted y) :
    SecondOrderEq 𝔼 β c f ym y ↔
      ∀ t, y t - mu1 β c • lagged ym y t =
        (mu2 β c)⁻¹ • 𝔼.E t (y (t + 1) - mu1 β c • lagged ym y (t + 1)) +
          (-(β⁻¹ * (mu2 β c)⁻¹)) • f t := by
  have hr := charPoly_mu1 hβ hc
  have h1 := mu1_pos hβ hc
  have hinv : β⁻¹ * (mu2 β c)⁻¹ = mu1 β c := by
    rw [← mul_inv, inv_beta_mul_mu2 hβ hc]
  unfold charPoly at hr
  refine forall_congr' fun t => ?_
  rw [lagged_succ, map_sub, map_smul, hya t, hinv, inv_mu2 hβ hc, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    linear_combination (-mu1 β c) * h + y t ω * hr
  · intro h
    apply mul_left_cancel₀ h1.ne'
    linear_combination (-1 : ℝ) * h + y t ω * hr

/-! ### Existence, uniqueness, and the explicit formula -/

/-- Woodford (2003), survey §4.3: the forward part `w_t = −β⁻¹ ∑ μ₂^{−j−1} E_t f_{t+j}` of the
solution, as the forward series of `−β⁻¹μ₂⁻¹ f` with ratio `μ₂⁻¹`. -/
noncomputable def wSol (β c : ℝ) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (mu2 β c)⁻¹ (fun t => (-(β⁻¹ * (mu2 β c)⁻¹)) • f t)

/-- Woodford (2003), (2.7), p. 489, and (F.10), p. 713: the unique bounded solution,
`y_t = μ₁ y_{t−1} + w_t`. -/
noncomputable def solution (β c : ℝ) (f : ℕ → Ω → ℝ) (ym : Ω → ℝ) : ℕ → Ω → ℝ :=
  backward (mu1 β c) ym (wSol 𝔼 β c f)

/-- Woodford (2003), (2.7), p. 489: `w_t = −β⁻¹ ∑_{j ≥ 0} μ₂^{−j−1} E_t f_{t+j}`. -/
theorem wSol_apply (β c : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    wSol 𝔼 β c f t ω = -β⁻¹ * ∑' j, ((mu2 β c) ^ (j + 1))⁻¹ * 𝔼.E t (f (t + j)) ω := by
  unfold wSol ExpectationSystem.forwardSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, pow_succ, mul_inv, inv_pow]
  ring

/-- Woodford (2003), survey §4.3: the ratio `μ₂⁻¹` of the forward part is less than one in
absolute value. -/
theorem abs_inv_mu2_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : |(mu2 β c)⁻¹| < 1 := by
  have h := one_lt_mu2 hβ hc
  rw [abs_of_pos (inv_pos.mpr (by linarith))]
  exact inv_lt_one_of_one_lt₀ h

/-- Woodford (2003), survey §4.3: a bound on the scaled forcing `−β⁻¹μ₂⁻¹ f`. -/
theorem scaled_bound {β c M : ℝ} {f : ℕ → Ω → ℝ} (hf : ∀ t ω, |f t ω| ≤ M) :
    ∀ t ω, |((fun t => (-(β⁻¹ * (mu2 β c)⁻¹)) • f t) t) ω| ≤ |β⁻¹ * (mu2 β c)⁻¹| * M := by
  intro t ω
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (hf t ω) (by positivity)

/-- Woodford (2003), survey §4.3: the scaled forcing is adapted. -/
theorem scaled_adapted {β c : ℝ} {f : ℕ → Ω → ℝ} (hfa : 𝔼.Adapted f) :
    𝔼.Adapted (fun t => (-(β⁻¹ * (mu2 β c)⁻¹)) • f t) := fun t => by
  simp only [map_smul, hfa t]

/-- Woodford (2003), (2.7), p. 489: the forward part solves
`w_t = μ₂⁻¹ E_t w_{t+1} − β⁻¹μ₂⁻¹ f_t`, and is bounded and adapted. -/
theorem wSol_spec {β c M : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) :
    BoundedProc (wSol 𝔼 β c f) ∧ 𝔼.Adapted (wSol 𝔼 β c f) ∧
      ∀ t, wSol 𝔼 β c f t =
        (mu2 β c)⁻¹ • 𝔼.E t (wSol 𝔼 β c f (t + 1)) + (-(β⁻¹ * (mu2 β c)⁻¹)) • f t := by
  have ha := abs_inv_mu2_lt_one hβ hc
  have hb := scaled_bound (β := β) (c := c) hf
  have hsa := scaled_adapted 𝔼 (β := β) (c := c) hfa
  exact ⟨ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hb,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hb,
    ForwardSolution.forwardSeries_solves_abs 𝔼 ha hb hsa⟩

/-- Woodford (2003), (2.7), p. 489: the candidate solution is bounded, adapted and solves the
second-order equation. -/
theorem solution_spec {β c M B : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {ym : Ω → ℝ} (hym : 𝔼.E 0 ym = ym)
    (hymb : ∀ ω, |ym ω| ≤ B) :
    BoundedProc (solution 𝔼 β c f ym) ∧ 𝔼.Adapted (solution 𝔼 β c f ym) ∧
      SecondOrderEq 𝔼 β c f ym (solution 𝔼 β c f ym) := by
  obtain ⟨⟨Mw, hMw⟩, hwa, hw⟩ := wSol_spec 𝔼 hβ hc hf hfa
  have hμ : |mu1 β c| < 1 := by
    rw [abs_of_pos (mu1_pos hβ hc)]; exact mu1_lt_one hβ hc
  have hya : 𝔼.Adapted (solution 𝔼 β c f ym) := backward_adapted 𝔼 hym hwa
  refine ⟨backward_bounded hμ hymb hMw, hya, (secondOrder_iff_factored 𝔼 hβ hc hya).mpr ?_⟩
  intro t
  have hq : ∀ s, solution 𝔼 β c f ym s - mu1 β c • lagged ym (solution 𝔼 β c f ym) s =
      wSol 𝔼 β c f s := fun s => by
    rw [solution, backward_spec, add_sub_cancel_left]
  rw [hq t, hq (t + 1)]
  exact hw t

/-- Woodford (2003), p. 489 and App. F.5, p. 714 (**uniqueness without hypotheses on the
forcing**): two bounded adapted solutions of the second-order equation with the same forcing `f`
and the same `y_{−1}` coincide (`β, c > 0`; `f` need be neither bounded nor adapted). The proof
works with the difference `d = y − y'`, whose quasi-difference `e_t = d_t − μ₁ d_{t−1}` solves
`e_t = μ₂⁻¹ E_t e_{t+1}` and is bounded, hence zero. -/
theorem eq_of_secondOrderEq {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → Ω → ℝ} {ym : Ω → ℝ}
    {y y' : ℕ → Ω → ℝ} (h : SecondOrderEq 𝔼 β c f ym y) (h' : SecondOrderEq 𝔼 β c f ym y')
    (ha : 𝔼.Adapted y) (ha' : 𝔼.Adapted y') (hb : BoundedProc y) (hb' : BoundedProc y') :
    y = y' := by
  set d : ℕ → Ω → ℝ := fun t => y t - y' t with hd
  set e : ℕ → Ω → ℝ := fun t => d t - mu1 β c • lagged 0 d t with he
  have hl2 : mu2 β c ≠ 0 := (lt_trans one_pos (one_lt_mu2 hβ hc)).ne'
  have hprev : ∀ t, lagged ym y t - lagged ym y' t = lagged 0 d t := by
    intro t; cases t <;> simp [hd]
  have hda : ∀ t, 𝔼.E t (d t) = d t := fun t => by simp [hd, map_sub, ha t, ha' t]
  have key : ∀ t, mu2 β c • e t = 𝔼.E t (e (t + 1)) := by
    intro t
    have hEd : 𝔼.E t (e (t + 1)) = 𝔼.E t (y (t + 1)) - 𝔼.E t (y' (t + 1)) - mu1 β c • d t := by
      change 𝔼.E t (d (t + 1) - mu1 β c • d t) = _
      rw [map_sub, map_smul, hda t]
      simp only [hd, map_sub]
    rw [hEd]
    funext ω
    have k1 := congrFun (h t) ω
    have k2 := congrFun (h' t) ω
    have k3 := congrFun (hprev t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at k1 k2 k3
    have hp := beta_mul_prod hβ hc
    have hs := beta_mul_sum (c := c) hβ
    have hX : β * (mu2 β c * (d t ω - mu1 β c * lagged 0 d t ω) - (𝔼.E t (y (t + 1)) ω
        - 𝔼.E t (y' (t + 1)) ω - mu1 β c * d t ω)) = 0 := by
      rw [← k3]
      simp only [hd, Pi.sub_apply]
      linear_combination (y t ω - y' t ω) * hs
        - (lagged ym y t ω - lagged ym y' t ω) * hp - (k1 - k2)
    have hX' := (mul_eq_zero.mp hX).resolve_left hβ.ne'
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hfe : ∀ t, e t = (mu2 β c)⁻¹ • 𝔼.E t (e (t + 1)) + 0 := fun t => by
    rw [← key t, smul_smul, inv_mul_cancel₀ hl2, one_smul, add_zero]
  have hebd : BoundedProc e := by
    obtain ⟨M, hM⟩ := hb
    obtain ⟨M', hM'⟩ := hb'
    refine ⟨(M + M') + |mu1 β c| * (M + M'), fun t ω => ?_⟩
    have hdb : ∀ s ω, |d s ω| ≤ M + M' := fun s ω => by
      simp only [hd, Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hM s ω) (hM' s ω))
    have hpb : |lagged 0 d t ω| ≤ M + M' := by
      cases t with
      | zero =>
        simp only [lagged_zero, Pi.zero_apply, abs_zero]
        exact le_trans (abs_nonneg _) (hdb 0 ω)
      | succ t => exact hdb t ω
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hdb t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hpb (abs_nonneg _)
  have he0 : e = 0 := 𝔼.forward_unique (abs_inv_mu2_lt_one hβ hc) hfe (fun t => by simp) hebd
    ⟨0, fun _ _ => by simp⟩
  have hd0 : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero =>
      have := congrFun he0 0
      simpa [he] using this
    | succ t ih =>
      have := congrFun he0 (t + 1)
      simp only [he, lagged_succ, ih, smul_zero, sub_zero, Pi.zero_apply] at this
      exact this
  funext t ω
  have := congrFun (hd0 t) ω
  simp only [hd, Pi.sub_apply, Pi.zero_apply] at this
  linarith

/-- Woodford (2003), (2.7), p. 489, survey §4.3 (**uniqueness**): every bounded adapted solution
of the second-order equation is `solution`. -/
theorem eq_solution {β c M : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {ym : Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hyb : BoundedProc y) (hya : 𝔼.Adapted y) (hy : SecondOrderEq 𝔼 β c f ym y) :
    y = solution 𝔼 β c f ym := by
  have hfac := (secondOrder_iff_factored 𝔼 hβ hc hya).mp hy
  obtain ⟨Y, hY⟩ := hyb
  have hlag : ∀ t ω, |lagged ym y t ω| ≤ M + β * Y + (1 + β + c) * Y := by
    intro t ω
    cases t with
    | zero =>
      have h0 := congrFun (hy 0) ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lagged_zero] at h0
      have e : ym ω = f 0 ω - β * 𝔼.E 0 (y 1) ω + (1 + β + c) * y 0 ω := by linarith
      rw [lagged_zero, e]
      have hE := 𝔼.abs_E_le (hY 1) 0 ω
      calc |f 0 ω - β * 𝔼.E 0 (y 1) ω + (1 + β + c) * y 0 ω|
          ≤ |f 0 ω| + β * |𝔼.E 0 (y 1) ω| + (1 + β + c) * |y 0 ω| := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
              (add_le_add le_rfl ?_)) ?_)
            · rw [abs_mul, abs_of_pos hβ]
            · rw [abs_mul, abs_of_pos (by linarith)]
        _ ≤ M + β * Y + (1 + β + c) * Y := by
            gcongr
            · exact hf 0 ω
            · exact hY 0 ω
    | succ t =>
      have hY0 : 0 ≤ Y := (abs_nonneg _).trans (hY 0 ω)
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hf 0 ω)
      rw [lagged_succ]
      nlinarith [hY t ω]
  have hwb : BoundedProc (fun t => y t - mu1 β c • lagged ym y t) := by
    refine ⟨Y + mu1 β c * (M + β * Y + (1 + β + c) * Y), fun t ω => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hY t ω) ?_)
    rw [abs_mul, abs_of_pos (mu1_pos hβ hc)]
    exact mul_le_mul_of_nonneg_left (hlag t ω) (mu1_pos hβ hc).le
  have hw : (fun t => y t - mu1 β c • lagged ym y t) = wSol 𝔼 β c f :=
    ForwardSolution.eq_forwardSeries_abs 𝔼 (abs_inv_mu2_lt_one hβ hc) (scaled_bound hf)
      (scaled_adapted 𝔼 hfa) hfac hwb
  refine backward_unique fun t => ?_
  have := congrFun hw t
  rw [← this]
  abel

/-- Woodford (2003), (1.12), p. 473, (2.7), p. 489, survey §4.3 (**the workhorse**): for
`β, c > 0`, bounded adapted forcing `f`, and a bounded initial value `y_{−1}` known at date `0`,
the equation `β E_t y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t` has exactly one bounded adapted
solution. -/
theorem bounded_solution_unique {β c M B : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {ym : Ω → ℝ} (hym : 𝔼.E 0 ym = ym)
    (hymb : ∀ ω, |ym ω| ≤ B) :
    ∃! y, BoundedProc y ∧ 𝔼.Adapted y ∧ SecondOrderEq 𝔼 β c f ym y :=
  ⟨solution 𝔼 β c f ym, solution_spec 𝔼 hβ hc hf hfa hym hymb,
    fun _ h => eq_solution 𝔼 hβ hc hf hfa h.1 h.2.1 h.2.2⟩

/-- Woodford (2003), (2.7), p. 489, and survey §4.3 (**the explicit formula**): every bounded
adapted solution satisfies `y_t = μ₁ y_{t−1} − β⁻¹ ∑_{j ≥ 0} μ₂^{−j−1} E_t f_{t+j}`. -/
theorem solution_formula {β c M : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → Ω → ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {ym : Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hyb : BoundedProc y) (hya : 𝔼.Adapted y) (hy : SecondOrderEq 𝔼 β c f ym y) (t : ℕ)
    (ω : Ω) :
    y t ω = mu1 β c * lagged ym y t ω -
      β⁻¹ * ∑' j, ((mu2 β c) ^ (j + 1))⁻¹ * 𝔼.E t (f (t + j)) ω := by
  have he := eq_solution 𝔼 hβ hc hf hfa hyb hya hy
  have hs := congrFun (backward_spec (mu1 β c) ym (wSol 𝔼 β c f) t) ω
  rw [← solution, ← he] at hs
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, wSol_apply]
  ring

/-- Woodford (2003), Ch. 7, p. 489 (**arbitrary start date**): the workhorse from date `t₀`. With
`y_s` standing for the value at date `t₀ + s`, the equation
`β E_{t₀+s} y_{s+1} − (1 + β + c) y_s + y_{s−1} = f_{t₀+s}` (`s ≥ 0`, `y_{−1} = y_{t₀−1}` given and
known at `t₀`) has exactly one bounded solution adapted to the information from `t₀` on. -/
theorem bounded_solution_unique_from (t₀ : ℕ) {β c M B : ℝ} (hβ : 0 < β) (hc : 0 < c)
    {f : ℕ → Ω → ℝ} (hf : ∀ t ω, |f t ω| ≤ M) (hfa : ∀ s, 𝔼.E (t₀ + s) (f (t₀ + s)) = f (t₀ + s))
    {ym : Ω → ℝ} (hym : 𝔼.E t₀ ym = ym) (hymb : ∀ ω, |ym ω| ≤ B) :
    ∃! y : ℕ → Ω → ℝ, BoundedProc y ∧ (∀ s, 𝔼.E (t₀ + s) (y s) = y s) ∧
      ∀ s, β • 𝔼.E (t₀ + s) (y (s + 1)) - (1 + β + c) • y s + lagged ym y s = f (t₀ + s) :=
  bounded_solution_unique (shiftSys 𝔼 t₀) hβ hc (f := fun s => f (t₀ + s))
    (fun s ω => hf (t₀ + s) ω) hfa (by simpa using hym) hymb

/-! ### Constant forcing -/

/-- Woodford (2003), eq. (1.12), p. 473: the solution with constant forcing `F` and initial
value `Y₀`, `y_t = ȳ + μ₁^{t+1}(Y₀ − ȳ)` with steady state `ȳ = −F/c`. -/
noncomputable def constSol (β c F Y₀ : ℝ) (t : ℕ) : ℝ :=
  -F / c + mu1 β c ^ (t + 1) * (Y₀ + F / c)

/-- Woodford (2003), eq. (1.12), p. 473: `constSol` solves the deterministic equation
`β y_{t+1} − (1 + β + c) y_t + y_{t−1} = F` with `y_{−1} = Y₀`. -/
theorem constSol_eq {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (F Y₀ : ℝ) (t : ℕ) :
    β * constSol β c F Y₀ (t + 1) - (1 + β + c) * constSol β c F Y₀ t +
      lagged Y₀ (constSol β c F Y₀) t = F := by
  have hr := charPoly_mu1 hβ hc
  unfold charPoly at hr
  cases t with
  | zero =>
    simp only [constSol, lagged_zero]
    field_simp
    linear_combination (c * Y₀ + F) * hr
  | succ t =>
    simp only [constSol, lagged_succ]
    field_simp
    linear_combination (c * Y₀ + F) * mu1 β c ^ (t + 1) * hr

/-- Woodford (2003), eq. (1.12), p. 473 (**constant forcing**): with forcing `f_t ≡ F` and
`y_{−1} ≡ Y₀`, the unique bounded adapted solution is `y_t = ȳ + μ₁^{t+1}(Y₀ − ȳ)`,
`ȳ = −F/c`, the same in every state. -/
theorem eq_constant_forcing {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (F Y₀ : ℝ) {y : ℕ → Ω → ℝ}
    (hyb : BoundedProc y) (hya : 𝔼.Adapted y)
    (hy : SecondOrderEq 𝔼 β c (fun _ _ => F) (fun _ => Y₀) y) :
    y = fun t _ => constSol β c F Y₀ t := by
  have hF : ∀ t (ω : Ω), |(fun _ _ => F : ℕ → Ω → ℝ) t ω| ≤ |F| := fun _ _ => le_rfl
  have hFa : 𝔼.Adapted (fun _ _ => F : ℕ → Ω → ℝ) := fun t => 𝔼.const t F
  have hμ0 := mu1_pos hβ hc
  have hμ1 := mu1_lt_one hβ hc
  have hcb : BoundedProc (fun t (_ : Ω) => constSol β c F Y₀ t) := by
    refine ⟨|F / c| + |Y₀ + F / c|, fun t _ => ?_⟩
    unfold constSol
    refine (abs_add_le _ _).trans (add_le_add (by rw [neg_div, abs_neg]) ?_)
    rw [abs_mul, abs_pow, abs_of_pos hμ0]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hμ0.le hμ1.le)
  have hca : 𝔼.Adapted (fun t (_ : Ω) => constSol β c F Y₀ t) := fun t => 𝔼.const t _
  have hcs : SecondOrderEq 𝔼 β c (fun _ _ => F) (fun _ => Y₀)
      (fun t (_ : Ω) => constSol β c F Y₀ t) := by
    intro t
    rw [𝔼.const]
    funext ω
    have := constSol_eq hβ hc F Y₀ t
    cases t <;> simpa using this
  rw [eq_solution 𝔼 hβ hc hF hFa hyb hya hy, eq_solution 𝔼 hβ hc hF hFa hcb hca hcs]

/-! ### The deterministic special case -/

/-- Woodford (2003), eq. (1.10), p. 472 (perfect foresight): the deterministic second-order
equation `β y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t` with `y_{−1} = ym`. -/
def SecondOrderDet (β c : ℝ) (f : ℕ → ℝ) (ym : ℝ) (y : ℕ → ℝ) : Prop :=
  ∀ t, β * y (t + 1) - (1 + β + c) * y t + lagged ym y t = f t

/-- Woodford (2003), eq. (1.10), p. 472: a deterministic sequence solves the deterministic
equation iff its constant-in-the-state lift solves the equation under perfect foresight. -/
theorem secondOrderDet_iff (β c : ℝ) (f : ℕ → ℝ) (ym : ℝ) (y : ℕ → ℝ) :
    SecondOrderDet β c f ym y ↔
      SecondOrderEq perfectForesight β c (fun t _ => f t) (fun _ => ym) (fun t _ => y t) := by
  refine forall_congr' fun t => ?_
  rw [funext_iff]
  cases t <;> simp [perfectForesight]

/-- Woodford (2003), eqs. (1.10)–(1.12), pp. 472–473 (**deterministic workhorse**): for
`β, c > 0`, a bounded sequence `f` and any `y_{−1}`, there is exactly one bounded sequence
solving `β y_{t+1} − (1 + β + c) y_t + y_{t−1} = f_t` for all `t ≥ 0`; it satisfies
`y_t = μ₁ y_{t−1} − β⁻¹ ∑_j μ₂^{−j−1} f_{t+j}`. -/
theorem bounded_solution_unique_det {β c M : ℝ} (hβ : 0 < β) (hc : 0 < c) {f : ℕ → ℝ}
    (hf : ∀ t, |f t| ≤ M) (ym : ℝ) :
    (∃! y : ℕ → ℝ, (∃ K, ∀ t, |y t| ≤ K) ∧ SecondOrderDet β c f ym y) ∧
      ∀ y : ℕ → ℝ, (∃ K, ∀ t, |y t| ≤ K) → SecondOrderDet β c f ym y → ∀ t,
        y t = mu1 β c * lagged ym y t - β⁻¹ * ∑' j, ((mu2 β c) ^ (j + 1))⁻¹ * f (t + j) := by
  have hf' : ∀ t (ω : Unit), |(fun t _ => f t : ℕ → Unit → ℝ) t ω| ≤ M := fun t _ => hf t
  have hfa : perfectForesight.Adapted (fun t _ => f t : ℕ → Unit → ℝ) := fun _ => rfl
  obtain ⟨Y, ⟨hYb, -, hYs⟩, -⟩ := bounded_solution_unique perfectForesight hβ hc hf' hfa
    (ym := fun _ => ym) rfl (fun _ => le_refl |ym|)
  have hform : ∀ y : ℕ → ℝ, (∃ K, ∀ t, |y t| ≤ K) → SecondOrderDet β c f ym y → ∀ t,
      y t = mu1 β c * lagged ym y t - β⁻¹ * ∑' j, ((mu2 β c) ^ (j + 1))⁻¹ * f (t + j) := by
    intro y ⟨K, hK⟩ hy t
    have := solution_formula perfectForesight hβ hc hf' hfa ⟨K, fun t _ => hK t⟩
      (fun _ => rfl) ((secondOrderDet_iff β c f ym y).mp hy) t ()
    cases t <;> simpa [perfectForesight] using this
  refine ⟨⟨fun t => Y t (), ⟨?_, ?_⟩, ?_⟩, hform⟩
  · obtain ⟨K, hK⟩ := hYb
    exact ⟨K, fun t => hK t ()⟩
  · rw [secondOrderDet_iff]
    exact hYs
  · intro y ⟨⟨K, hK⟩, hy⟩
    have e1 := eq_solution perfectForesight hβ hc hf' hfa ⟨K, fun t _ => hK t⟩ (fun _ => rfl)
      ((secondOrderDet_iff β c f ym y).mp hy)
    have e2 := eq_solution perfectForesight hβ hc hf' hfa hYb (fun _ => rfl) hYs
    funext t
    have := congrFun (congrFun (e1.trans e2.symm) t) ()
    exact this

end Woodford.GainsFromCommitment.SecondOrderRE
