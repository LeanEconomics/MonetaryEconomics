/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.GeneralFormula

/-!
# The weighted present value state by state

Cochrane (2023), §7.4, pp. 224–226, equations (7.14) and (7.17).

The weighted present value (7.17) `y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` is built from the
*pathwise* weighted sum `Z_t = ∑_m β^m W_t^{(m)} s_{t+m}`, a series of real numbers at each state.
This module proves two facts used by the existence results of the later TidyR5 modules:

* `pathZ_solves`: state by state, `Z` solves the flow system (7.14) without expectations,
  `Z_t = s_t + ∑_j β^{j+1} A_t^{(t+j+1)} Z_{t+j+1}`, whenever the weights are absolutely summable
  along every row. This is the perfect-foresight content of (7.17), with no row or column
  condition beyond absolute summability.
* `formulaW_solves_of_exchange`: if `E_t` passes through the two series involved (the series
  for `Z_t` and the series on the right of (7.14)), then `y_t = E_t Z_t` is (7.17) and solves the
  flow system (7.14) under uncertainty.

`weight_apply` evaluates Cochrane's weights at a state, and `hasSum_E_of_dom` is the dominated
interchange of `E_t` and a series in `HasSum` form.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5Pathwise

open Filter Topology MaturityStructure GeneralFormula

/-- Cochrane (2023), §7.4, p. 226: the weights of random sale fractions, evaluated at a state, are
the weights of the sale fractions at that state. -/
theorem weight_apply {Ω : Type*} (A : ℕ → ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    ∀ t, weight A t m ω = weight (fun u v => A u v ω) t m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t
    rcases m with _ | k
    · simp [weight_zero]
    · rw [weight_succ, weight_succ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Pi.mul_apply, ih n (Finset.mem_range.mp hn) t]

/-- Cochrane (2023), eq. (7.17), p. 225: the pathwise weighted present value
`Z_t = ∑_m β^m W_t^{(m)} s_{t+m}` for deterministic sale fractions and surpluses. -/
noncomputable def pathZ (β : ℝ) (A : ℕ → ℕ → ℝ) (s : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑' m, β ^ m * (weight A t m * s (t + m))

/-- Cochrane (2023), eq. (7.17), p. 225: the pathwise weighted present value at each state,
`Z_t(ω) = ∑_m β^m W_t^{(m)}(ω) s_{t+m}(ω)`. -/
noncomputable def pathZΩ {Ω : Type*} (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  pathZ β (fun u v => A u v ω) (fun u => s u ω) t

/-- Cochrane (2023), eq. (7.17), p. 225: with `0 ≤ β`, `|s| ≤ M` and `∑_m β^m |W_t^{(m)}| ≤ C`,
the series for `Z_t` converges absolutely and `|Z_t| ≤ C M`. -/
theorem pathZ_summable_bound {β M C : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → ℝ} {s : ℕ → ℝ}
    (hsb : ∀ u, |s u| ≤ M) {t : ℕ} (hW : Summable (fun m => β ^ m * |weight A t m|))
    (hWC : ∑' m, β ^ m * |weight A t m| ≤ C) :
    Summable (fun m => |β ^ m * (weight A t m * s (t + m))|) ∧ |pathZ β A s t| ≤ C * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0)
  have hb : ∀ m, |β ^ m * (weight A t m * s (t + m))| ≤ β ^ m * |weight A t m| * M := by
    intro m
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hsb _) (abs_nonneg _))
      (pow_nonneg hβ0 m)
  have hdom : Summable (fun m => β ^ m * |weight A t m| * M) := hW.mul_right M
  have hs : Summable (fun m => |β ^ m * (weight A t m * s (t + m))|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hb hdom
  refine ⟨hs, ?_⟩
  have h0 := norm_tsum_le_tsum_norm (f := fun m => β ^ m * (weight A t m * s (t + m)))
    (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at h0
  refine h0.trans ((Summable.tsum_le_tsum hb hs hdom).trans ?_)
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right hWC hM

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: **the pathwise weighted present value
solves the flow system.** With `0 ≤ β`, bounded surpluses, weights absolutely summable along every
row (`∑_m β^m |W_u^{(m)}| ≤ C`) and an absolutely summable row `∑_j β^{j+1}|A_t^{(t+j+1)}|`,
`Z_t = s_t + ∑_j β^{j+1} A_t^{(t+j+1)} Z_{t+j+1}`. The proof regroups an absolutely convergent
double series by antidiagonals, using `GeneralFormula.weight_first_step`. -/
theorem pathZ_solves {β M C : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → ℝ} {s : ℕ → ℝ}
    (hsb : ∀ u, |s u| ≤ M) (hW : ∀ u, Summable (fun m => β ^ m * |weight A u m|))
    (hWC : ∀ u, ∑' m, β ^ m * |weight A u m| ≤ C) (t : ℕ)
    (hrow : Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1))|)) :
    HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) * pathZ β A s (t + (j + 1))))
      (pathZ β A s t - s t) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0)
  have hC : 0 ≤ C := (tsum_nonneg fun m => mul_nonneg (pow_nonneg hβ0 m) (abs_nonneg _)).trans
    (hWC 0)
  set Gf : ℕ × ℕ → ℝ := fun p => β ^ (p.1 + 1) * (A t (t + (p.1 + 1)) *
    (β ^ p.2 * (weight A (t + (p.1 + 1)) p.2 * s (t + (p.1 + 1) + p.2)))) with hGf
  set g : ℕ × ℕ → ℝ := fun p => β ^ (p.1 + 1) * |A t (t + (p.1 + 1))| *
    (β ^ p.2 * |weight A (t + (p.1 + 1)) p.2| * M) with hg
  have hg0 : 0 ≤ g := fun p => mul_nonneg (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
    (mul_nonneg (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _)) hM)
  have hGb : ∀ p, ‖Gf p‖ ≤ g p := by
    intro p
    rw [Real.norm_eq_abs, hGf, hg]
    simp only [abs_mul, abs_pow, abs_of_nonneg hβ0]
    have h1 : |s (t + (p.1 + 1) + p.2)| ≤ M := hsb _
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (pow_nonneg hβ0 (p.1 + 1))
      (abs_nonneg (A t (t + (p.1 + 1))))) (mul_nonneg (pow_nonneg hβ0 p.2)
        (abs_nonneg (weight A (t + (p.1 + 1)) p.2))))
    refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_)) <;> ring
  have hgsum : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨fun j => ?_, ?_⟩
    · simp only [hg]
      exact ((hW (t + (j + 1))).mul_right M).mul_left (β ^ (j + 1) * |A t (t + (j + 1))|)
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun m => hg0 (j, m)) (fun j => ?_)
      (hrow.mul_right (C * M))
    simp only [hg]
    rw [tsum_mul_left, tsum_mul_right]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hWC _) hM)
      (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
  have hGsum : Summable Gf := Summable.of_norm_bounded hgsum hGb
  -- (i) the fibres
  have hfib : ∀ j, HasSum (fun m => Gf (j, m))
      (β ^ (j + 1) * (A t (t + (j + 1)) * pathZ β A s (t + (j + 1)))) := by
    intro j
    have hin := (pathZ_summable_bound hβ0 hsb (hW (t + (j + 1))) (hWC _)).1
    exact ((hin.of_abs).hasSum.mul_left (A t (t + (j + 1)))).mul_left (β ^ (j + 1))
  have hrowsum := hGsum.hasSum.prod_fiberwise hfib
  -- (ii) the antidiagonals
  have hdiag : HasSum (fun k => β ^ (k + 1) * (weight A t (k + 1) * s (t + (k + 1))))
      (∑' p, Gf p) := by
    have h1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := Gf)).mpr
      hGsum.hasSum
    have h2 := h1.sigma (fun k => hasSum_fintype _)
    convert h2 using 1
    funext k
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal k) Gf,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, weight_first_step, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [hGf]
    rw [show t + (j + 1) + (k - j) = t + (k + 1) by omega,
      show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by rw [← pow_add]; congr 1; omega]
    ring
  -- (iii) the value at `t`
  have hzs := (pathZ_summable_bound hβ0 hsb (hW t) (hWC t)).1.of_abs
  have hz : pathZ β A s t = s t + ∑' p, Gf p := by
    rw [pathZ, hzs.tsum_eq_zero_add, hdiag.tsum_eq]
    simp [weight_zero]
  rw [hz, add_sub_cancel_left]
  exact hrowsum

/-- Cochrane (2023), §7.4 (used for (7.17)): `E_t` passes through a series of random variables
dominated by a summable sequence, in `HasSum` form. -/
theorem hasSum_E_of_dom {Ω : Type*} (𝔼 : ExpectationSystem Ω) {u : ℕ → ℝ} (hu : Summable u)
    {f : ℕ → Ω → ℝ} (hf : ∀ k ω, |f k ω| ≤ u k) (t : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω) := by
  rw [ForwardSolution.E_tsum_dom 𝔼 hu hf t ω]
  exact (Summable.of_norm_bounded hu (fun k => by
    rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)).hasSum

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (7.17), p. 225: if `E_t` passes through the series for `Z_t`, the
weighted present value (7.17) is `E_t Z_t`. -/
theorem formulaW_eq_E {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {s Z : ℕ → Ω → ℝ}
    (hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (𝔼.E t (Z t) ω)) (t : ℕ) :
    formulaW 𝔼 β A s t = 𝔼.E t (Z t) :=
  funext fun ω => (hex1 t ω).tsum_eq

/-- Cochrane (2023), eq. (7.17), p. 225: if `E_t` passes through the series for `Z_t`, the
weighted present value (7.17) is known at `t`. -/
theorem formulaW_adapted_of_exchange {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {s Z : ℕ → Ω → ℝ}
    (hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (𝔼.E t (Z t) ω)) (t : ℕ) :
    𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t := by
  rw [formulaW_eq_E 𝔼 hex1, 𝔼.E_E_self]

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: **(7.17) solves the flow system, given the
two interchanges.** Let `Z` solve the flow system state by state, each sale fraction
`A_t^{(t+j+1)}` be known at `t + j`, surpluses be adapted, and suppose `E_t` passes through the
series for `Z_t` (hypothesis hex1) and through the series `∑_j β^{j+1} A_t^{(t+j+1)} Z_{t+j+1}`
(hypothesis hex2).
Then `y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` satisfies (7.14) at `t`, under uncertainty. -/
theorem formulaW_solves_of_exchange (hpo : 𝔼.PullOut) {β : ℝ} {A : ℕ → ℕ → Ω → ℝ}
    {s Z : ℕ → Ω → ℝ} (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    (hs : 𝔼.Adapted s)
    (hpw : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) ω * Z (t + (j + 1)) ω))
      (Z t ω - s t ω))
    (hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (𝔼.E t (Z t) ω))
    (hex2 : ∀ t ω, HasSum (fun j : ℕ => 𝔼.E t (fun ω' => β ^ (j + 1) *
      (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) ω)
      (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) ω))
    (t : ℕ) : MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t := by
  intro ω
  have hfw := formulaW_eq_E 𝔼 hex1
  have hterm : ∀ j, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * formulaW 𝔼 β A s (t + (j + 1))) ω =
      𝔼.E t (fun ω' => β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) ω := by
    intro j
    have hAk : 𝔼.E (t + (j + 1)) (A t (t + (j + 1))) = A t (t + (j + 1)) :=
      ForwardSolution.E_of_known 𝔼 (by omega) (hA t j)
    rw [hfw, ← hpo _ _ _ hAk, 𝔼.tower (by omega),
      show (fun ω' => β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) =
        β ^ (j + 1) • (A t (t + (j + 1)) * Z (t + (j + 1))) from rfl, map_smul]
    rfl
  have hsum : (fun ω' => ∑' j : ℕ, β ^ (j + 1) * (A t (t + (j + 1)) ω' * Z (t + (j + 1)) ω')) =
      Z t - s t := funext fun ω' => (hpw t ω').tsum_eq
  have h := hex2 t ω
  rw [hsum, map_sub, hs t] at h
  simp only [hterm]
  rw [hfw t]
  exact h

end Cochrane.LongTermDebtDynamics.TidyR5Pathwise
