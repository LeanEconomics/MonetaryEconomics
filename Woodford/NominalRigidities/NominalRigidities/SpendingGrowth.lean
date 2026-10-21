/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Persistence

/-!
# Persistent growth of nominal spending

Woodford (2003), *Interest and Prices*, Chapter 3, §2.4, pp. 197–200, and Appendix B.6,
pp. 664–666 (Proposition 3.7).

## Main results

* (2.21) and (B.23): the nominal-spending response `Ỹ_k = 1 − ρ^{k+1}` (`Ytil`, `Ytil_eq_sum`,
  `unit_response`); the printed (B.23) `1 − ρ^k` is false (`printed_B23_false`); the innovation
  in the stochastic process (2.21) moves spending by exactly this path (`arGrowth_shock`).
* (B.24) ⟺ (B.25) (`irfEq_Ytil_iff`, `lag_Ytil`); **Proposition 3.7** with the terminal condition
  (`prop_3_7`), the bounded class and the unbounded continuum outside it (`prop_3_7_classes`),
  for every `0 ≤ ρ < 1`, in the form `ỹ_k = C ∑_{i ≤ k} λⁱρ^{k−i}`.
* The book's route through App. B.6: the forward sum as a `HasSum` (`B6_forward_hasSum`,
  `B6_value`), (B.26) and `ỹ_0 = C` (`B26`), the general solution with distinct roots and its
  coefficients `A₁`, `A₂` (`general_solution`, `general_solution_eq_B22`), (B.22)
  (`y37_closed`), the case `ρ = 0` (`rho_zero`) and the excluded case `ρ = λ` (`rho_eq_lam`).
* Signs and shape: `Cc_pos`, `coeff_signs`, `y37_pos`, `y37_unimodal`, the hump criterion
  `hump_iff` (`λ + ρ > 1`), the index slip E3 (`E3_index`), and Fig. 3.9 (`fig39_hump`).
* p. 200: prices rise and output stays below spending (`p37_pos`), the peak output effect can be
  arbitrarily close to one for small `κ` (`peak_near_one`), while under (1.32) it is at most
  `1 − ρ` (`nc_peak_bound`).
* Proposition 3.7 for an arbitrary expectation system (`prop_3_7_stochastic`).
-/

namespace Woodford.NominalRigidities.SpendingGrowth

open Filter Topology Woodford.NominalRigidities.Persistence
open Woodford.NominalRigidities.QuadraticRoots hiding charPoly_alpha lagPoly_factor lam1_mul_lam2
  root_location

/-! ### The nominal-spending response under (2.21) -/

/-- Woodford (2003), (B.23), p. 665, corrected: the response of `(1 − ρ) E_t log 𝒴_{t+k}` to the
innovation, `Ỹ_k = 1 − ρ^{k+1}` (printed `1 − ρ^k`). -/
noncomputable def Ytil (ρ : ℝ) (k : ℕ) : ℝ := 1 - ρ ^ (k + 1)

/-- Woodford (2003), (B.23): `Ỹ_{k−1} = 1 − ρ^k` for every `k ≥ 0`, so (B.23) also holds at
`k = −1` (`Ỹ_{−1} = 0`). -/
theorem prevZ_Ytil (ρ : ℝ) (k : ℕ) : prev 0 (Ytil ρ) k = 1 - ρ ^ k := by
  cases k <;> simp [Ytil]

/-- Woodford (2003), p. 197: the growth-rate response to the innovation `1 − ρ` is
`(1 − ρ)ρ^k`, so the level response is the partial sum `Ỹ_k = ∑_{j ≤ k} (1 − ρ)ρ^j`. -/
theorem Ytil_eq_sum (ρ : ℝ) (k : ℕ) :
    Ytil ρ k = ∑ j ∈ Finset.range (k + 1), (1 - ρ) * ρ ^ j := by
  induction k with
  | zero => simp [Ytil]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold Ytil
    ring

/-- Woodford (2003), p. 197: a unit innovation raises `E_t log 𝒴_{t+k}` by
`(1 − ρ)⁻¹(1 − ρ^{k+1})`, increasing in `k` towards `(1 − ρ)⁻¹ > 1` times the impact effect. -/
theorem unit_response {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    StrictMono (fun k : ℕ => (1 - ρ)⁻¹ * Ytil ρ k) ∧
      Tendsto (fun k : ℕ => (1 - ρ)⁻¹ * Ytil ρ k) atTop (𝓝 (1 - ρ)⁻¹) ∧
      (1 - ρ)⁻¹ * Ytil ρ 0 = 1 ∧ 1 < (1 - ρ)⁻¹ := by
  have h1 : 0 < 1 - ρ := by linarith
  refine ⟨strictMono_nat_of_lt_succ fun k => ?_, ?_, ?_, ?_⟩
  · apply mul_lt_mul_of_pos_left _ (inv_pos.2 h1)
    unfold Ytil
    have : ρ ^ (k + 1 + 1) < ρ ^ (k + 1) := pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 (by omega)
    linarith
  · have : Tendsto (fun k : ℕ => ρ ^ (k + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp (tendsto_add_atTop_nat 1)
    simpa [Ytil] using ((tendsto_const_nhds (x := (1 : ℝ))).sub this).const_mul (1 - ρ)⁻¹
  · simp only [Ytil, zero_add, pow_one]
    field_simp
  · exact (one_lt_inv₀ h1).2 (by linarith)

/-- Woodford (2003), (B.23) as printed, `Ỹ_k = 1 − ρ^k`, is false: it gives `Ỹ_0 = 0`, while an
innovation of size `1 − ρ > 0` raises nominal spending on impact by `1 − ρ`; and at `k = −1` it
gives `1 − ρ⁻¹ ≠ 0`. -/
theorem printed_B23_false {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (1 - ρ ^ 0 ≠ Ytil ρ 0) ∧ (1 - ρ⁻¹ ≠ prev 0 (Ytil ρ) 0) := by
  constructor
  · simp only [pow_zero, sub_self, Ytil, zero_add, pow_one]
    linarith
  · rw [prev_zero]
    have : 1 < ρ⁻¹ := (one_lt_inv₀ hρ0).2 hρ1
    linarith

/-! ### The innovation in the stochastic process (2.21) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (2.21), p. 197: `Δ log 𝒴_t = ρ Δ log 𝒴_{t−1} + ε_t + q_t`, for log nominal
spending `n` with inherited `log 𝒴_{−1}`, written with the total innovation `e = ε + q`. -/
def ARGrowth (ρ : ℝ) (nm1 : Ω → ℝ) (e n : ℕ → Ω → ℝ) : Prop :=
  ∀ t, n (t + 1) - n t = ρ • (n t - prev nm1 n t) + e (t + 1)

/-- Woodford (2003), (2.21) and p. 197: the effect of an innovation. If `n` and `n'` solve (2.21)
from the same initial conditions and the innovations differ only by `c (1 − ρ) ε` at date
`s ≥ 1`, then `n' − n = c Ỹ_{r−s} ε` from date `s` on (zero before): the innovation raises
nominal spending `k` periods later by `c(1 − ρ^{k+1})ε`, whatever the other components `q`. -/
theorem arGrowth_shock {ρ : ℝ} {nm1 : Ω → ℝ} {e n n' : ℕ → Ω → ℝ} {s : ℕ} (hs : 1 ≤ s)
    {ε : Ω → ℝ} (c : ℝ) (hn : ARGrowth ρ nm1 e n)
    (hn' : ARGrowth ρ nm1 (fun t => e t + if t = s then (c * (1 - ρ)) • ε else 0) n')
    (h0 : n' 0 = n 0) : ∀ t, n' t - n t = c • shockPath s (Ytil ρ) ε t := by
  set d : ℕ → Ω → ℝ := fun t => n' t - n t
  set P : ℕ → Ω → ℝ := fun t => c • shockPath s (Ytil ρ) ε t
  -- both `d` and `P` solve the same second-order recursion from the same initial values
  have hd : ∀ t, d (t + 1) - d t =
      ρ • (d t - prev 0 d t) + if t + 1 = s then (c * (1 - ρ)) • ε else 0 := by
    intro t
    have a := hn t
    have b := hn' t
    have hl : prev nm1 n' t - prev nm1 n t = prev 0 d t := prev_sub nm1 n' n t
    simp only [d]
    rw [← hl]
    funext ω
    have a' := congrFun a ω
    have b' := congrFun b ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a' b' ⊢
    linarith
  have hP : ∀ t, P (t + 1) - P t =
      ρ • (P t - prev 0 P t) + if t + 1 = s then (c * (1 - ρ)) • ε else 0 := by
    intro t
    have hl : prev 0 P t = c • prev 0 (shockPath s (Ytil ρ) ε) t := by
      cases t with
      | zero => simp
      | succ t => rfl
    rw [hl, prev_shockPath]
    simp only [P, shockPath]
    by_cases h : s ≤ t
    · have h1 : s ≤ t + 1 := by omega
      have h2 : t + 1 ≠ s := by omega
      simp only [h, h1, h2, ↓reduceIte, add_zero]
      rw [show t + 1 - s = t - s + 1 by omega, prevZ_Ytil]
      funext ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Ytil]
      ring
    · by_cases h' : t + 1 = s
      · subst h'
        simp only [h, le_refl, ↓reduceIte, Nat.sub_self]
        funext ω
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
          Ytil]
        ring
      · have h1 : ¬ s ≤ t + 1 := by omega
        simp only [h, h1, h', ↓reduceIte, smul_zero, sub_zero, add_zero]
  have key : ∀ t, d t = P t ∧ d (t + 1) = P (t + 1) := by
    intro t
    induction t with
    | zero =>
      have hd0 : d 0 = 0 := by simp only [d, h0, sub_self]
      have hP0 : P 0 = 0 := by
        have : ¬ s ≤ 0 := by omega
        simp only [P, shockPath, this, ↓reduceIte, smul_zero]
      refine ⟨hd0.trans hP0.symm, ?_⟩
      have a := hd 0
      have b := hP 0
      rw [hd0, prev_zero] at a
      rw [hP0, prev_zero] at b
      rw [sub_zero] at a b
      rw [a, b]
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      have a := hd (t + 1)
      have b := hP (t + 1)
      simp only [prev_succ] at a b
      rw [ih.1, ih.2] at a
      rw [sub_eq_iff_eq_add] at a b
      rw [a, b]
  intro t
  exact (key t).1

/-! ### Proposition 3.7: the deterministic impulse responses -/

/-- Woodford (2003), App. B.6, p. 665: `C ≡ (1 − ρ)(1 − βρ)/(λ₁⁻¹ − βρ)`. -/
noncomputable def Cc (β κ ρ : ℝ) : ℝ := (1 - ρ) * (1 - β * ρ) / ((lam1 β κ)⁻¹ - β * ρ)

/-- Woodford (2003), p. 198: the complete homogeneous sum `∑_{i ≤ k} λⁱ ρ^{k−i}`, which equals
`(λ^{k+1} − ρ^{k+1})/(λ − ρ)` when `λ ≠ ρ` (`hsum_closed`) and `(k + 1)λ^k` when `λ = ρ`. -/
noncomputable def hsum (l ρ : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), l ^ i * ρ ^ (k - i)

/-- Woodford (2003), Prop. 3.7, p. 198: the output response `ỹ_k = C ∑_{i ≤ k} λⁱ ρ^{k−i}`
(this form is valid for every `ρ`, including the case `ρ = λ` excluded in the book). -/
noncomputable def y37 (β κ ρ : ℝ) (k : ℕ) : ℝ := Cc β κ ρ * hsum (lam1 β κ) ρ k

/-- Woodford (2003), Prop. 3.7, p. 198: the price response `p̃_k = 1 − ρ^{k+1} − ỹ_k`. -/
noncomputable def p37 (β κ ρ : ℝ) (k : ℕ) : ℝ := Ytil ρ k - y37 β κ ρ k

/-- Woodford (2003), (B.25), p. 665: `A(L) ỹ_{k+1} = −(1 − ρ)(1 − βρ)ρ^k` for `k ≥ 0`, with
`ỹ_{−1} = 0`. -/
def OutEq (β κ ρ : ℝ) (y : ℕ → ℝ) : Prop :=
  ∀ k, prev 0 y k - (1 + β + κ) * y k + β * y (k + 1) = -((1 - ρ) * (1 - β * ρ) * ρ ^ k)

/-- Woodford (2003), p. 198: `∑_{i ≤ k+1} λⁱρ^{k+1−i} = λ ∑_{i ≤ k} λⁱρ^{k−i} + ρ^{k+1}`. -/
theorem hsum_succ (l ρ : ℝ) (k : ℕ) : hsum l ρ (k + 1) = l * hsum l ρ k + ρ ^ (k + 1) := by
  unfold hsum
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show k + 1 - (i + 1) = k - i by omega, pow_succ]
  ring

/-- Woodford (2003), p. 198: `∑_{i ≤ k+1} λⁱρ^{k+1−i} = ρ ∑_{i ≤ k} λⁱρ^{k−i} + λ^{k+1}`. -/
theorem hsum_succ' (l ρ : ℝ) (k : ℕ) : hsum l ρ (k + 1) = ρ * hsum l ρ k + l ^ (k + 1) := by
  unfold hsum
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [show k + 1 - i = k - i + 1 by omega, pow_succ]
  ring

/-- Woodford (2003), p. 198: `hsum` at `k = 0` and `k = 1`. -/
theorem hsum_zero_one (l ρ : ℝ) : hsum l ρ 0 = 1 ∧ hsum l ρ 1 = l + ρ := by
  constructor
  · simp [hsum]
  · rw [hsum_succ]; simp [hsum]

/-- Woodford (2003), (B.22): for `λ ≠ ρ`, `∑_{i ≤ k} λⁱρ^{k−i} = (λ^{k+1} − ρ^{k+1})/(λ − ρ)`. -/
theorem hsum_closed {l ρ : ℝ} (h : l ≠ ρ) (k : ℕ) :
    hsum l ρ k = (l ^ (k + 1) - ρ ^ (k + 1)) / (l - ρ) := by
  have hne : l - ρ ≠ 0 := sub_ne_zero.2 h
  induction k with
  | zero => simp [hsum]; field_simp
  | succ k ih =>
    rw [hsum_succ, ih]
    field_simp
    ring

/-- Woodford (2003), p. 198 (the excluded case): for `ρ = λ`, `∑_{i ≤ k} λⁱλ^{k−i} = (k + 1)λ^k`. -/
theorem hsum_diag (l : ℝ) (k : ℕ) : hsum l l k = (k + 1) * l ^ k := by
  unfold hsum
  rw [Finset.sum_congr rfl fun i hi => by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]]
  simp

/-- Woodford (2003), p. 198: `hsum ≥ 0` and `hsum > 0` for `λ > 0`, `ρ ≥ 0`. -/
theorem hsum_pos {l ρ : ℝ} (hl : 0 < l) (hρ : 0 ≤ ρ) (k : ℕ) : 0 < hsum l ρ k := by
  induction k with
  | zero => simp [hsum]
  | succ k ih => rw [hsum_succ]; positivity

/-- Woodford (2003), p. 198: `hsum ≥ 0` for `λ, ρ ≥ 0`. -/
theorem hsum_pos_or_zero {l ρ : ℝ} (hl : 0 ≤ l) (hρ : 0 ≤ ρ) (k : ℕ) : 0 ≤ hsum l ρ k := by
  unfold hsum
  exact Finset.sum_nonneg fun i _ => by positivity

/-- Woodford (2003), p. 198: `|∑_{i ≤ k} λⁱρ^{k−i}| ≤ (k + 1) μ^k` for `0 ≤ λ, ρ ≤ μ`. -/
theorem hsum_le {l ρ μ : ℝ} (hl : 0 ≤ l) (hρ : 0 ≤ ρ) (hlμ : l ≤ μ) (hρμ : ρ ≤ μ) (k : ℕ) :
    hsum l ρ k ≤ (k + 1) * μ ^ k := by
  unfold hsum
  calc ∑ i ∈ Finset.range (k + 1), l ^ i * ρ ^ (k - i)
      ≤ ∑ i ∈ Finset.range (k + 1), μ ^ k := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        calc l ^ i * ρ ^ (k - i) ≤ μ ^ i * μ ^ (k - i) :=
              mul_le_mul (pow_le_pow_left₀ hl hlμ i) (pow_le_pow_left₀ hρ hρμ _)
                (pow_nonneg hρ _) (pow_nonneg (hl.trans hlμ) _)
          _ = μ ^ k := by rw [← pow_add, Nat.add_sub_cancel' hi']
    _ = (k + 1) * μ ^ k := by simp

/-- Woodford (2003), p. 198: `∑_{i ≤ k} λⁱρ^{k−i} → 0` for `0 ≤ λ, ρ < 1`. -/
theorem hsum_tendsto {l ρ : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (hsum l ρ) atTop (𝓝 0) := by
  set μ := max l ρ
  have hμ0 : 0 ≤ μ := le_max_of_le_left hl
  have hμ1 : μ < 1 := max_lt hl1 hρ1
  have h1 := tendsto_self_mul_const_pow_of_lt_one hμ0 hμ1
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hμ0 hμ1
  have hub : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * μ ^ k) atTop (𝓝 0) := by
    simpa [add_mul] using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub (fun k => ?_)
    (fun k => hsum_le hl hρ (le_max_left _ _) (le_max_right _ _) k)
  exact (hsum_pos_or_zero hl hρ k)

/-- Woodford (2003), App. B.6: `λ₁⁻¹ − βρ > 0` (indeed `λ₁⁻¹ > 1 > βρ`) for `ρ < 1`. -/
theorem denom_pos {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ1 : ρ < 1) :
    0 < (lam1 β κ)⁻¹ - β * ρ := by
  have h0 := lam1_pos hβ hκ
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have : 1 < (lam1 β κ)⁻¹ := (one_lt_inv₀ h0).2 h1
  nlinarith

/-- Woodford (2003), App. B.6, p. 665: `C > 0`. -/
theorem Cc_pos {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ1 : ρ < 1) :
    0 < Cc β κ ρ := by
  have := denom_pos hβ hβ1 hκ hρ1
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 - β * ρ := by nlinarith
  unfold Cc
  positivity

/-- Woodford (2003), App. B.6, pp. 665–666: `(1 − λ₁L)ỹ_k = Cρ^k` (with `ỹ_{−1} = 0`) implies
(B.25). -/
theorem outEq_of_z {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ1 : ρ < 1)
    {y : ℕ → ℝ} (hz : ∀ k, y k - lam1 β κ * prev 0 y k = Cc β κ ρ * ρ ^ k) :
    OutEq β κ ρ y := by
  intro k
  have e1 := beta_mul_sum (c := κ) hβ
  have e2 := beta_mul_prod hβ hκ
  have hd := denom_pos hβ hβ1 hκ hρ1
  have h0 := lam1_pos hβ hκ
  have hinv : (lam1 β κ)⁻¹ = β * lam2 β κ := by
    field_simp
    linarith
  have hC : Cc β κ ρ * (β * lam2 β κ - β * ρ) = (1 - ρ) * (1 - β * ρ) := by
    unfold Cc
    rw [← hinv]
    exact div_mul_cancel₀ _ hd.ne'
  have A := hz k
  have B := hz (k + 1)
  rw [prev_succ] at B
  linear_combination β * B + y k * e1 - β * lam2 β κ * A - prev 0 y k * e2 - ρ ^ k * hC

/-- Woodford (2003), p. 198: the output response of Proposition 3.7 satisfies
`(1 − λL)ỹ_k = Cρ^k`. -/
theorem y37_z (β κ ρ : ℝ) (k : ℕ) :
    y37 β κ ρ k - lam1 β κ * prev 0 (y37 β κ ρ) k = Cc β κ ρ * ρ ^ k := by
  cases k with
  | zero => simp [y37, (hsum_zero_one _ _).1]
  | succ k =>
    rw [prev_succ]
    unfold y37
    rw [hsum_succ]
    ring

/-- Woodford (2003), (B.24) ⟺ (B.25), p. 665: with `ỹ = Ỹ − p̃` (the identity
`log 𝒴 = log P + log Y`), the price equation (B.24) for `p̃` is equivalent to the output
equation (B.25) for `ỹ`. -/
theorem irfEq_Ytil_iff (β κ ρ : ℝ) (p : ℕ → ℝ) :
    IRFEq β κ (Ytil ρ) p ↔ OutEq β κ ρ (fun k => Ytil ρ k - p k) := by
  rw [irfEq_iff_lag]
  refine forall_congr' fun k => ?_
  have hprev : prev 0 (fun k => Ytil ρ k - p k) k = (1 - ρ ^ k) - prev 0 p k := by
    cases k <;> simp [Ytil]
  rw [hprev]
  simp only [Ytil]
  constructor
  · intro h
    linear_combination (-1 : ℝ) * h
  · intro h
    linear_combination (-1 : ℝ) * h

/-- Woodford (2003), App. B.6, p. 665: the printed display
`A(L)Ỹ_{k+1} = β(1 − ρ^{k+2}) − (1 + β + κ)(1 − ρ^{k+1}) + (1 − ρ^k)` (with the corrected
(B.23)). -/
theorem lag_Ytil (β κ ρ : ℝ) (k : ℕ) :
    prev 0 (Ytil ρ) k - (1 + β + κ) * Ytil ρ k + β * Ytil ρ (k + 1) =
      β * (1 - ρ ^ (k + 2)) - (1 + β + κ) * (1 - ρ ^ (k + 1)) + (1 - ρ ^ k) := by
  rw [prevZ_Ytil]
  unfold Ytil
  ring

/-- Woodford (2003), Prop. 3.7: `ỹ_k > 0` for all `k` (p. 198), for `0 ≤ ρ < 1`. -/
theorem y37_pos {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (k : ℕ) : 0 < y37 β κ ρ k :=
  mul_pos (Cc_pos hβ hβ1 hκ hρ1) (hsum_pos (lam1_pos hβ hκ) hρ0 k)

/-- Woodford (2003), p. 198: `ỹ_k → 0` (the terminal condition of App. B.6). -/
theorem y37_tendsto {β κ ρ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (y37 β κ ρ) atTop (𝓝 0) := by
  have h := (hsum_tendsto (lam1_pos hβ hκ).le (lam1_lt_one_lt_lam2 hβ hκ).1 hρ0 hρ1).const_mul
    (Cc β κ ρ)
  rw [mul_zero] at h
  exact h

/-- Woodford (2003), p. 197: `Ỹ_k = 1 − ρ^{k+1} → 1`. -/
theorem Ytil_tendsto {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : Tendsto (Ytil ρ) atTop (𝓝 1) := by
  have : Tendsto (fun k : ℕ => ρ ^ (k + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun k : ℕ => 1 - ρ ^ (k + 1)) atTop (𝓝 1)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

/-- Woodford (2003), Prop. 3.7: `p̃_k = 1 − ρ^{k+1} − ỹ_k` solves (B.24) with `p̃_{−1} = 0`. -/
theorem p37_irfEq {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ1 : ρ < 1) :
    IRFEq β κ (Ytil ρ) (p37 β κ ρ) := by
  rw [irfEq_Ytil_iff]
  have e : (fun k => Ytil ρ k - p37 β κ ρ k) = y37 β κ ρ := by
    funext k; unfold p37; ring
  rw [e]
  exact outEq_of_z hβ hβ1 hκ hρ1 (y37_z β κ ρ)

/-- Woodford (2003), Prop. 3.7: `p̃_k → 1`. -/
theorem p37_tendsto {β κ ρ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (p37 β κ ρ) atTop (𝓝 1) := by
  change Tendsto (fun k => Ytil ρ k - y37 β κ ρ k) atTop (𝓝 1)
  simpa using (Ytil_tendsto hρ0 hρ1).sub (y37_tendsto hβ hκ hρ0 hρ1)

/-- **Proposition 3.7** (Woodford 2003, p. 198; App. B.6, pp. 664–666) in full: among sequences
satisfying (B.24) with `p̃_{−1} = 0`, exactly one has output returning to trend (`ỹ_k → 0`),
namely `p̃_k = 1 − ρ^{k+1} − ỹ_k` with `ỹ_k = C ∑_{i ≤ k} λⁱρ^{k−i}`. Here `0 ≤ ρ < 1`
(no `ρ ≠ λ` needed in this form). -/
theorem prop_3_7 {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (p : ℕ → ℝ) :
    (IRFEq β κ (Ytil ρ) p ∧ Tendsto (fun k => Ytil ρ k - p k) atTop (𝓝 0)) ↔
      p = p37 β κ ρ := by
  constructor
  · rintro ⟨hp, ht⟩
    have hb : ∃ M, ∀ k, |p k| ≤ M := by
      have := (Ytil_tendsto hρ0 hρ1).sub ht
      rw [sub_zero] at this
      obtain ⟨M, hM⟩ := bounded_of_tendsto this
      exact ⟨M, fun k => by simpa using hM k⟩
    exact irfEq_bounded_unique hβ hκ hp (p37_irfEq hβ hβ1 hκ hρ1) hb
      (bounded_of_tendsto (p37_tendsto hβ hκ hρ0 hρ1))
  · rintro rfl
    refine ⟨p37_irfEq hβ hβ1 hκ hρ1, ?_⟩
    have e : (fun k => Ytil ρ k - p37 β κ ρ k) = y37 β κ ρ := by
      funext k; unfold p37; ring
    rw [e]
    exact y37_tendsto hβ hκ hρ0 hρ1

/-- Woodford (2003), Prop. 3.7: uniqueness also among all bounded sequences, and the solutions of
(B.24) are exactly `p̃ + c(λ₂^{k+1} − λ₁^{k+1})`, unbounded for `c ≠ 0`. -/
theorem prop_3_7_classes {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (p : ℕ → ℝ) :
    ((IRFEq β κ (Ytil ρ) p ∧ ∃ M, ∀ k, |p k| ≤ M) ↔ p = p37 β κ ρ) ∧
      (IRFEq β κ (Ytil ρ) p ↔ ∃ c : ℝ, p = fun k => p37 β κ ρ k + c * hom β κ k) ∧
      ∀ c : ℝ, c ≠ 0 → ¬ ∃ M, ∀ k, |p37 β κ ρ k + c * hom β κ k| ≤ M := by
  have hb := bounded_of_tendsto (p37_tendsto hβ hκ hρ0 hρ1)
  have hirf := p37_irfEq hβ hβ1 hκ hρ1
  refine ⟨⟨fun ⟨hp, hpb⟩ => irfEq_bounded_unique hβ hκ hp hirf hpb hb, ?_⟩,
    irfEq_iff_exists hβ hκ hirf, fun c hc => (irfEq_unbounded_family hβ hκ hirf hb hc).2⟩
  rintro rfl
  exact ⟨hirf, hb⟩

/-! ### The book's route through App. B.6 -/

/-- Woodford (2003), App. B.6, p. 665: for a bounded solution of (B.25),
`(1 − λ₁L)ỹ_k = β⁻¹λ₂⁻¹(1 − ρ)(1 − βρ) ∑_{j ≥ 0} λ₂^{−j} ρ^{j+k}` (a genuine `HasSum`). -/
theorem B6_forward_hasSum {β κ ρ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {y : ℕ → ℝ} (hy : OutEq β κ ρ y) (hb : ∃ M, ∀ k, |y k| ≤ M) (k : ℕ) :
    HasSum (fun j : ℕ => β⁻¹ * (lam2 β κ)⁻¹ * ((1 - ρ) * (1 - β * ρ)) *
      ((lam2 β κ)⁻¹ ^ j * ρ ^ (j + k))) (y k - lam1 β κ * prev 0 y k) := by
  obtain ⟨M, hM⟩ := hb
  set Yaux : ℕ → ℝ := fun k => (1 - ρ) * (1 - β * ρ) * ρ ^ k / κ
  have hirf : IRFEq β κ Yaux y := by
    rw [irfEq_iff_lag]
    intro k
    have := hy k
    simp only [Yaux]
    field_simp
    linarith
  have hYb : ∀ k, |Yaux k| ≤ |(1 - ρ) * (1 - β * ρ) / κ| := by
    intro k
    simp only [Yaux]
    rw [show (1 - ρ) * (1 - β * ρ) * ρ ^ k / κ = (1 - ρ) * (1 - β * ρ) / κ * ρ ^ k by ring,
      abs_mul]
    have : |ρ ^ k| ≤ 1 := by rw [abs_pow, abs_of_nonneg hρ0]; exact pow_le_one₀ hρ0 hρ1.le
    nlinarith [abs_nonneg ((1 - ρ) * (1 - β * ρ) / κ)]
  have h := irf_forward_hasSum hβ hκ hYb hirf hM k
  convert h using 1
  funext j
  simp only [Yaux]
  have h2 : lam2 β κ ≠ 0 := by linarith [(lam1_lt_one_lt_lam2 hβ hκ).2]
  rw [show k + j = j + k by ring]
  field_simp

/-- Woodford (2003), App. B.6, p. 665: the forward sum equals `Cρ^k`. -/
theorem B6_value {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (k : ℕ) :
    HasSum (fun j : ℕ => β⁻¹ * (lam2 β κ)⁻¹ * ((1 - ρ) * (1 - β * ρ)) *
      ((lam2 β κ)⁻¹ ^ j * ρ ^ (j + k))) (Cc β κ ρ * ρ ^ k) := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have h20 : lam2 β κ ≠ 0 := by linarith
  have e2 := beta_mul_prod hβ hκ
  have hr0 : 0 ≤ ρ / lam2 β κ := div_nonneg hρ0 (by linarith)
  have hr1 : ρ / lam2 β κ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (β⁻¹ * (lam2 β κ)⁻¹ * ((1 - ρ) * (1 - β * ρ)) * ρ ^ k)
  convert hg using 1
  · funext j
    rw [pow_add, div_pow, inv_pow]
    field_simp
  · have h0 := lam1_pos hβ hκ
    have hinv : (lam1 β κ)⁻¹ = β * lam2 β κ := by field_simp; linarith
    have hd : lam2 β κ - ρ ≠ 0 := by linarith
    have hd' : 1 - ρ / lam2 β κ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ / lam2 β κ).ne'
    unfold Cc
    rw [hinv]
    have hβl : β * lam2 β κ - β * ρ = β * (lam2 β κ - ρ) := by ring
    rw [hβl]
    field_simp

/-- Woodford (2003), App. B.6, pp. 665–666: for any bounded solution of (B.25),
`(1 − λ₁L)ỹ_k = Cρ^k`; hence (B.26) `(1 − ρL)(1 − λ₁L)ỹ_{k+1} = 0` and the additional initial
condition `ỹ_0 = C`. -/
theorem B26 {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {y : ℕ → ℝ} (hy : OutEq β κ ρ y) (hb : ∃ M, ∀ k, |y k| ≤ M) :
    (∀ k, y k - lam1 β κ * prev 0 y k = Cc β κ ρ * ρ ^ k) ∧
      (∀ k, y (k + 1) - (ρ + lam1 β κ) * y k + ρ * lam1 β κ * prev 0 y k = 0) ∧
      y 0 = Cc β κ ρ := by
  have hz : ∀ k, y k - lam1 β κ * prev 0 y k = Cc β κ ρ * ρ ^ k := fun k =>
    (B6_forward_hasSum hβ hκ hρ0 hρ1 hy hb k).unique (B6_value hβ hβ1 hκ hρ0 hρ1 k)
  refine ⟨hz, fun k => ?_, ?_⟩
  · have a := hz k
    have b := hz (k + 1)
    rw [prev_succ] at b
    linear_combination b - ρ * a
  · have := hz 0
    simpa using this

/-- Woodford (2003), App. B.6, p. 666: the general solution with distinct roots. If
`(1 − λL)y_k = Cρ^k` with `y_{−1} = 0`, `λ, ρ ≠ 0`, `ρ ≠ λ`, then the coefficients `(A₁, A₂)` are
uniquely determined by the initial conditions at `k = −1` and `k = 0`
(`A₁λ⁻¹ + A₂ρ⁻¹ = 0`, `A₁ + A₂ = C`), they are `A₁ = λC/(λ − ρ)`, `A₂ = ρC/(ρ − λ)`, and
`y_k = A₁λ^k + A₂ρ^k`. -/
theorem general_solution {l ρ C : ℝ} (hl : l ≠ 0) (hρ : ρ ≠ 0) (hne : ρ ≠ l) {y : ℕ → ℝ}
    (hz : ∀ k, y k - l * prev 0 y k = C * ρ ^ k) :
    (∃! A : ℝ × ℝ, A.1 * l⁻¹ + A.2 * ρ⁻¹ = 0 ∧ A.1 + A.2 = C) ∧
      (l * C / (l - ρ)) * l⁻¹ + (ρ * C / (ρ - l)) * ρ⁻¹ = 0 ∧
      l * C / (l - ρ) + ρ * C / (ρ - l) = C ∧
      ∀ k, y k = (l * C / (l - ρ)) * l ^ k + (ρ * C / (ρ - l)) * ρ ^ k := by
  have h1 : l - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have h2 : ρ - l ≠ 0 := sub_ne_zero.2 hne
  have c1 : (l * C / (l - ρ)) * l⁻¹ + (ρ * C / (ρ - l)) * ρ⁻¹ = 0 := by
    field_simp
    ring
  have c2 : l * C / (l - ρ) + ρ * C / (ρ - l) = C := by
    field_simp
    ring
  refine ⟨⟨(l * C / (l - ρ), ρ * C / (ρ - l)), ⟨c1, c2⟩, ?_⟩, c1, c2, ?_⟩
  · rintro ⟨A₁, A₂⟩ ⟨d1, d2⟩
    simp only at d1 d2
    have hA₂ : A₂ = C - A₁ := by linarith
    subst hA₂
    have key : A₁ * (l - ρ) = l * C := by
      field_simp at d1
      linarith
    have : A₁ = l * C / (l - ρ) := by rw [eq_div_iff h1]; exact key
    rw [this, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    field_simp
    ring
  · intro k
    induction k with
    | zero =>
      have := hz 0
      simp only [prev_zero, mul_zero, sub_zero, pow_zero, mul_one] at this
      rw [this, pow_zero, pow_zero, mul_one, mul_one, c2]
    | succ k ih =>
      have := hz (k + 1)
      rw [prev_succ, ih] at this
      rw [show y (k + 1) = l * ((l * C / (l - ρ)) * l ^ k + (ρ * C / (ρ - l)) * ρ ^ k) +
        C * ρ ^ (k + 1) by linarith]
      field_simp
      ring

/-- Woodford (2003), Prop. 3.7, (B.22), p. 664: for `ρ ≠ λ`,
`ỹ_k = (1 − ρ)(1 − βρ)/((λ − ρ)(λ⁻¹ − βρ)) · (λ^{k+1} − ρ^{k+1})`. -/
theorem y37_closed {β κ ρ : ℝ} (hne : ρ ≠ lam1 β κ) (k : ℕ) :
    y37 β κ ρ k = (1 - ρ) * (1 - β * ρ) / ((lam1 β κ - ρ) * ((lam1 β κ)⁻¹ - β * ρ)) *
      (lam1 β κ ^ (k + 1) - ρ ^ (k + 1)) := by
  unfold y37 Cc
  rw [hsum_closed (Ne.symm hne)]
  rw [div_mul_div_comm, mul_comm (lam1 β κ - ρ)]
  ring

/-- Woodford (2003), App. B.6, p. 666: the coefficients of the general solution reproduce
(B.22): `A₁λ^k + A₂ρ^k = C(λ^{k+1} − ρ^{k+1})/(λ − ρ)`. -/
theorem general_solution_eq_B22 {l ρ C : ℝ} (hl : l ≠ 0) (hne : ρ ≠ l) (k : ℕ) :
    (l * C / (l - ρ)) * l ^ k + (ρ * C / (ρ - l)) * ρ ^ k =
      C * (l ^ (k + 1) - ρ ^ (k + 1)) / (l - ρ) := by
  have h1 : l - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have h2 : ρ - l ≠ 0 := sub_ne_zero.2 hne
  have _ := hl
  field_simp
  ring

/-- Woodford (2003), p. 198: "in the limiting case `ρ = 0`, these solutions reduce to those given
in Proposition 3.6": `ỹ_k = λ^{k+1}` and `p̃_k = 1 − λ^{k+1}`. -/
theorem rho_zero {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    y37 β κ 0 = y36 β κ ∧ p37 β κ 0 = p36 β κ ∧ Ytil 0 = fun _ => 1 := by
  have h0 := lam1_pos hβ hκ
  have hy : y37 β κ 0 = y36 β κ := by
    funext k
    have hne : (0 : ℝ) ≠ lam1 β κ := h0.ne
    rw [y37_closed hne]
    unfold y36
    field_simp
    ring
  refine ⟨hy, ?_, ?_⟩
  · funext k
    rw [p37, hy, y36_eq]
    simp [Ytil]
  · funext k
    simp [Ytil]

/-- Woodford (2003), p. 198, the case excluded by `ρ ≠ λ`: for `ρ = λ` the unique solution of
Proposition 3.7 is `ỹ_k = C (k + 1) λ^k`, with `C = (1 − λ)(1 − βλ)/(λ⁻¹ − βλ)`. -/
theorem rho_eq_lam (β κ : ℝ) (k : ℕ) :
    y37 β κ (lam1 β κ) k = Cc β κ (lam1 β κ) * ((k + 1) * lam1 β κ ^ k) := by
  unfold y37
  rw [hsum_diag]

/-! ### Signs, positivity and the hump (pp. 198 and 666) -/

/-- Woodford (2003), App. B.6, p. 666: "`A₁ > 0`, `A₂ < 0` if `0 < ρ < λ₁`, while the signs are
reversed if `λ₁ < ρ < 1`"; in each case the positive term is the larger one at every `k`
(it decays less rapidly). -/
theorem coeff_signs {l ρ C : ℝ} (hC : 0 < C) (hl : 0 < l) (hρ : 0 < ρ) :
    (ρ < l → 0 < l * C / (l - ρ) ∧ ρ * C / (ρ - l) < 0 ∧
      ∀ k : ℕ, |ρ * C / (ρ - l) * ρ ^ k| < l * C / (l - ρ) * l ^ k) ∧
    (l < ρ → l * C / (l - ρ) < 0 ∧ 0 < ρ * C / (ρ - l) ∧
      ∀ k : ℕ, |l * C / (l - ρ) * l ^ k| < ρ * C / (ρ - l) * ρ ^ k) := by
  constructor
  · intro h
    have hd : 0 < l - ρ := by linarith
    refine ⟨by positivity, div_neg_of_pos_of_neg (by positivity) (by linarith), fun k => ?_⟩
    rw [abs_mul, abs_div, abs_of_pos (by positivity : 0 < ρ * C),
      abs_of_neg (by linarith : ρ - l < 0), abs_of_pos (by positivity : 0 < ρ ^ k),
      show -(ρ - l) = l - ρ by ring]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hd]
    have : ρ ^ (k + 1) < l ^ (k + 1) := pow_lt_pow_left₀ h hρ.le (by omega)
    rw [pow_succ, pow_succ] at this
    nlinarith
  · intro h
    have hd : 0 < ρ - l := by linarith
    refine ⟨div_neg_of_pos_of_neg (by positivity) (by linarith), by positivity, fun k => ?_⟩
    rw [abs_mul, abs_div, abs_of_pos (by positivity : 0 < l * C),
      abs_of_neg (by linarith : l - ρ < 0), abs_of_pos (by positivity : 0 < l ^ k),
      show -(l - ρ) = ρ - l by ring]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hd]
    have : l ^ (k + 1) < ρ ^ (k + 1) := pow_lt_pow_left₀ h hl.le (by omega)
    rw [pow_succ, pow_succ] at this
    nlinarith

/-- Woodford (2003), p. 198: the increments of `∑_{i ≤ k} λⁱρ^{k−i}` satisfy
`Δ_{k+1} = ρ Δ_k − λ^{k+1}(1 − λ)`, so once non-positive they stay negative. -/
theorem hsum_step {l ρ : ℝ} (hl : 0 < l) (hl1 : l < 1) (hρ : 0 ≤ ρ) {k : ℕ}
    (h : hsum l ρ (k + 1) - hsum l ρ k ≤ 0) :
    hsum l ρ (k + 2) - hsum l ρ (k + 1) < 0 := by
  have e1 := hsum_succ' l ρ (k + 1)
  have e2 := hsum_succ' l ρ k
  have hpow : 0 < l ^ (k + 1) := pow_pos hl _
  have : hsum l ρ (k + 2) - hsum l ρ (k + 1) =
      ρ * (hsum l ρ (k + 1) - hsum l ρ k) - l ^ (k + 1) * (1 - l) := by
    rw [e1, e2]; ring
  rw [this]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ h, mul_pos hpow (by linarith : (0 : ℝ) < 1 - l)]

/-- Woodford (2003), p. 198: once the response stops rising it falls strictly ever after. -/
theorem hsum_decr_after {l ρ : ℝ} (hl : 0 < l) (hl1 : l < 1) (hρ : 0 ≤ ρ) {K : ℕ}
    (h : hsum l ρ (K + 1) - hsum l ρ K ≤ 0) (k : ℕ) (hk : K < k) :
    hsum l ρ (k + 1) - hsum l ρ k < 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
    · exact hsum_step hl hl1 hρ (ih hk').le
    · subst hk'; exact hsum_step hl hl1 hρ h

/-- Woodford (2003), p. 198: the response cannot rise for ever (it returns to zero). -/
theorem hsum_exists_nonpos {l ρ : ℝ} (hl : 0 < l) (hl1 : l < 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ k, hsum l ρ (k + 1) - hsum l ρ k ≤ 0 := by
  by_contra hc
  push Not at hc
  have hmono : StrictMono (hsum l ρ) := strictMono_nat_of_lt_succ fun k => by linarith [hc k]
  have hlim := hsum_tendsto hl.le hl1 hρ hρ1
  have h0 : hsum l ρ 0 = 1 := (hsum_zero_one l ρ).1
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  have := hmono.monotone (Nat.zero_le k)
  linarith

/-- Woodford (2003), p. 198: "A difference of two exponentials of this kind either decays
monotonically back to zero after a peak in the period of the shock, or it first increases to a
peak, and then decays monotonically back to zero". For `0 ≤ ρ < 1` there is a peak date `K`
with `ỹ` strictly increasing before `K` and strictly decreasing after `K + 1` (non-increasing
from `K`); the response is hump-shaped (`K ≥ 1`) **iff `λ + ρ > 1`**. -/
theorem y37_unimodal {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) :
    ∃ K : ℕ, (∀ k < K, y37 β κ ρ k < y37 β κ ρ (k + 1)) ∧
      (∀ k, K ≤ k → y37 β κ ρ (k + 1) ≤ y37 β κ ρ k) ∧
      (∀ k, K < k → y37 β κ ρ (k + 1) < y37 β κ ρ k) ∧
      (1 ≤ K ↔ 1 < lam1 β κ + ρ) := by
  have hl := lam1_pos hβ hκ
  have hl1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have hC := Cc_pos hβ hβ1 hκ hρ1
  classical
  have hex := hsum_exists_nonpos hl hl1 hρ0 hρ1
  set K := Nat.find hex
  have hK : hsum (lam1 β κ) ρ (K + 1) - hsum (lam1 β κ) ρ K ≤ 0 := Nat.find_spec hex
  have hbefore : ∀ k < K, 0 < hsum (lam1 β κ) ρ (k + 1) - hsum (lam1 β κ) ρ k := by
    intro k hk
    have := Nat.find_min hex hk
    push Not at this
    exact this
  have hafter := hsum_decr_after hl hl1 hρ0 hK
  refine ⟨K, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · unfold y37
    have := hbefore k hk
    nlinarith
  · unfold y37
    rcases Nat.lt_or_eq_of_le hk with hk' | hk'
    · have := hafter k hk'
      nlinarith
    · subst hk'
      nlinarith
  · unfold y37
    have := hafter k hk
    nlinarith
  · have h01 : hsum (lam1 β κ) ρ 1 - hsum (lam1 β κ) ρ 0 = lam1 β κ + ρ - 1 := by
      rw [(hsum_zero_one _ _).1, (hsum_zero_one _ _).2]
    constructor
    · intro h
      have := hbefore 0 (by omega)
      linarith
    · intro h
      by_contra hc
      push Not at hc
      have hK0 : K = 0 := by omega
      rw [hK0] at hK
      linarith

/-- Woodford (2003), p. 198: **the hump criterion**. The output response first rises above its
impact value (a hump-shaped response) if and only if `λ + ρ > 1`, i.e. `ρ > 1 − λ`. -/
theorem hump_iff {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) : (∃ k, y37 β κ ρ 0 < y37 β κ ρ k) ↔ 1 < lam1 β κ + ρ := by
  have hl := lam1_pos hβ hκ
  have hl1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have hC := Cc_pos hβ hβ1 hκ hρ1
  have h01 : y37 β κ ρ 1 - y37 β κ ρ 0 = Cc β κ ρ * (lam1 β κ + ρ - 1) := by
    unfold y37
    rw [(hsum_zero_one _ _).1, (hsum_zero_one _ _).2]
    ring
  constructor
  · rintro ⟨k, hk⟩
    by_contra hc
    push Not at hc
    have hd0 : hsum (lam1 β κ) ρ (0 + 1) - hsum (lam1 β κ) ρ 0 ≤ 0 := by
      rw [(hsum_zero_one _ _).1, zero_add, (hsum_zero_one _ _).2]; linarith
    have hanti : ∀ k, hsum (lam1 β κ) ρ k ≤ hsum (lam1 β κ) ρ 0 := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; linarith
        · linarith [hsum_decr_after hl hl1 hρ0 hd0 k h0]
    have := hanti k
    unfold y37 at hk
    nlinarith
  · intro h
    exact ⟨1, by nlinarith⟩

/-- Woodford (2003), p. 198, survey error E3: the printed "`ỹ₂ = (λ + ρ)ỹ₁`" is an index slip.
In fact `ỹ₁ = (λ + ρ)ỹ₀`, while `ỹ₂ − (λ + ρ)ỹ₁ = −Cλρ`, which is non-zero whenever
`0 < ρ < 1`: the printed relation is false. -/
theorem E3_index {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    y37 β κ ρ 1 = (lam1 β κ + ρ) * y37 β κ ρ 0 ∧
      y37 β κ ρ 2 - (lam1 β κ + ρ) * y37 β κ ρ 1 = -(Cc β κ ρ * lam1 β κ * ρ) ∧
      y37 β κ ρ 2 ≠ (lam1 β κ + ρ) * y37 β κ ρ 1 := by
  have hl := lam1_pos hβ hκ
  have hC := Cc_pos hβ hβ1 hκ hρ1
  have h2 : hsum (lam1 β κ) ρ 2 = lam1 β κ ^ 2 + lam1 β κ * ρ + ρ ^ 2 := by
    rw [hsum_succ, (hsum_zero_one _ _).2]; ring
  have e2 : y37 β κ ρ 2 - (lam1 β κ + ρ) * y37 β κ ρ 1 = -(Cc β κ ρ * lam1 β κ * ρ) := by
    unfold y37; rw [h2, (hsum_zero_one _ _).2]; ring
  refine ⟨by unfold y37; rw [(hsum_zero_one _ _).1, (hsum_zero_one _ _).2]; ring, e2, ?_⟩
  intro h
  rw [h, sub_self] at e2
  have : 0 < Cc β κ ρ * lam1 β κ * ρ := by positivity
  linarith

/-- Woodford (2003), Fig. 3.9, p. 199 (`β = .99`, `κ = .024`, `ρ = .4`): `λ + ρ > 1`, so the
output response plotted there is hump-shaped. -/
theorem fig39_hump : (∃ k, y37 0.99 0.024 0.4 0 < y37 0.99 0.024 0.4 k) := by
  rw [hump_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  linarith [lam1_fig37.1]

/-! ### Peak output effects: New Keynesian versus New Classical (pp. 199–200) -/

/-- Woodford (2003), p. 198: prices rise in response to the shock, `p̃_k > 0`; hence the output
response stays below the nominal-spending response, `ỹ_k < Ỹ_k = 1 − ρ^{k+1} < 1` ("a fraction
of 1"). -/
theorem p37_pos {β κ ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (k : ℕ) : 0 < p37 β κ ρ k ∧ y37 β κ ρ k < Ytil ρ k ∧ y37 β κ ρ k < 1 := by
  have hl := lam1_pos hβ hκ
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have hYpos : ∀ m, 0 < Ytil ρ m := fun m => by
    unfold Ytil; have := pow_lt_one₀ hρ0 hρ1 (n := m + 1) (by omega); linarith
  have hYb : ∀ m, |Ytil ρ m| ≤ 1 := fun m => by
    rw [abs_of_pos (hYpos m)]; unfold Ytil; have := pow_nonneg hρ0 (m + 1); linarith
  obtain ⟨M, hM⟩ := bounded_of_tendsto (p37_tendsto hβ hκ hρ0 hρ1)
  have hz : ∀ m, 0 < p37 β κ ρ m - lam1 β κ * prev 0 (p37 β κ ρ) m := by
    intro m
    have h := irf_forward_hasSum hβ hκ hYb (p37_irfEq hβ hβ1 hκ hρ1) hM m
    rw [← h.tsum_eq]
    have hc : 0 < κ / (β * lam2 β κ) := div_pos hκ (mul_pos hβ (by linarith))
    have hr : 0 < (lam2 β κ)⁻¹ := inv_pos.2 (by linarith)
    refine h.summable.tsum_pos (fun j => ?_) 0 ?_
    · exact (mul_pos (pow_pos hr j) (mul_pos hc (hYpos _))).le
    · simpa using mul_pos hc (hYpos m)
  have hp : 0 < p37 β κ ρ k := by
    rw [backward_sum (p := p37 β κ ρ) (l := lam1 β κ)
      (z := fun m => p37 β κ ρ m - lam1 β κ * prev 0 (p37 β κ ρ) m) (fun m => rfl) k]
    refine Finset.sum_pos (fun i _ => mul_pos (pow_pos hl i) (hz _)) ⟨0, by simp⟩
  have hy : y37 β κ ρ k < Ytil ρ k := by unfold p37 at hp; linarith
  refine ⟨hp, hy, ?_⟩
  have : Ytil ρ k ≤ 1 := by unfold Ytil; have := pow_nonneg hρ0 (k + 1); linarith
  linarith

/-- Woodford (2003), p. 200: `(1 − ρ) ∑_{i ≤ k} ρ^{k−i} = 1 − ρ^{k+1}` (the value of the output
response formula at `λ = 1`). -/
theorem hsum_one (ρ : ℝ) (k : ℕ) : (1 - ρ) * hsum 1 ρ k = Ytil ρ k := by
  induction k with
  | zero => simp [hsum, Ytil]
  | succ k ih =>
    rw [hsum_succ', one_pow]
    unfold Ytil at ih ⊢
    linear_combination ρ * ih

/-- Woodford (2003), p. 200: as `κ → 0` (so `λ → 1`), the output response at each horizon tends
to the nominal-spending response: `ỹ_k → 1 − ρ^{k+1}`. -/
theorem y37_tendsto_kappa {β ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (k : ℕ) :
    Tendsto (fun κ => y37 β κ ρ k) (𝓝[>] 0) (𝓝 (Ytil ρ k)) := by
  have hd : (1 : ℝ)⁻¹ - β * ρ ≠ 0 := by nlinarith
  have hcont : ContinuousAt (fun l : ℝ => (1 - ρ) * (1 - β * ρ) / (l⁻¹ - β * ρ) * hsum l ρ k)
      1 := by
    have hs : Continuous (fun l : ℝ => hsum l ρ k) := by unfold hsum; fun_prop
    exact (continuousAt_const.div ((continuousAt_inv₀ one_ne_zero).sub continuousAt_const)
      hd).mul hs.continuousAt
  have h := hcont.tendsto.comp (lam1_tendsto_one hβ hβ1)
  have hv : (1 - ρ) * (1 - β * ρ) / ((1 : ℝ)⁻¹ - β * ρ) * hsum 1 ρ k = Ytil ρ k := by
    rw [← hsum_one]
    have : (1 : ℝ) - ρ * β ≠ 0 := by nlinarith
    rw [inv_one]
    field_simp
  rw [hv] at h
  exact h

/-- Woodford (2003), pp. 199–200: with nominal-spending growth persistence the peak output effect
"may be an arbitrarily large fraction of 1" although spending rises on impact only by `1 − ρ`:
for every `ε > 0` there is `κ₀ > 0` such that for all `0 < κ < κ₀` some `ỹ_k > 1 − ε`. -/
theorem peak_near_one {β ρ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    Ytil ρ 0 = 1 - ρ ∧ ∃ κ₀ > 0, ∀ κ, 0 < κ → κ < κ₀ → ∃ k, 1 - ε < y37 β κ ρ k := by
  refine ⟨by simp [Ytil], ?_⟩
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).eventually
    (gt_mem_nhds (half_pos hε))).exists
  have hev := (y37_tendsto_kappa hβ hβ1 hρ1 k).eventually
    (lt_mem_nhds (show 1 - ε < Ytil ρ k by
      unfold Ytil
      have : ρ ^ (k + 1) ≤ ρ ^ k := pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
      linarith))
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨δ, hδ, fun κ hκ hκδ => ⟨k, hδP ?_ hκ⟩⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hκ]
  exact hκδ

/-- Woodford (2003), p. 200: under the New Classical aggregate-supply relation (1.32) the peak
output effect occurs in the period of the shock and is bounded by `1 − ρ`: the output gap moves
by `c(1 − ρ)ε/(1 + κ)` at the shock date and not at all otherwise, and `(1 − ρ)/(1 + κ) < 1 − ρ`. -/
theorem nc_peak_bound {Ω : Type*} (𝔼 : ExpectationSystem Ω) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ1 : ρ < 1) {x p q : ℕ → Ω → ℝ} {s : ℕ} (hs : 1 ≤ s) {ε : Ω → ℝ}
    (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0) (c : ℝ) (hp : NCPC 𝔼 κ x p)
    (hpa : 𝔼.Adapted p) (hq : NCPC 𝔼 κ (fun t => x t + c • shockPath s (Ytil ρ) ε t) q)
    (hqa : 𝔼.Adapted q) :
    (∀ t, (x (t + 1) + c • shockPath s (Ytil ρ) ε (t + 1) - q (t + 1)) - (x (t + 1) - p (t + 1)) =
      if t + 1 = s then (c * (1 - ρ) / (1 + κ)) • ε else 0) ∧ (1 - ρ) / (1 + κ) < 1 - ρ := by
  refine ⟨fun t => ?_, ?_⟩
  · rw [ncpc_shock_gap 𝔼 hκ hs hεs hunf c hp hpa hq hqa t]
    simp [Ytil]
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith

/-! ### Proposition 3.7 for an arbitrary expectation system -/

/-- **Proposition 3.7** (Woodford 2003, p. 198) for an arbitrary expectation system. Let log
nominal spending follow (2.21) (`n` with innovations `e`, `n'` with the extra date-`s` innovation
`c(1 − ρ)ε`, unforecastable before `s`), natural output `yn` be unaffected, and `p` be the
equilibrium (2.12) for `x = n − yn` in the linear-growth class. Then the equilibrium for
`x' = n' − yn` in that class is `p + c p̃_{r−s} ε`; at date `s` expected log nominal spending
`k` periods ahead rises by `c(1 − ρ^{k+1})ε`, the expected log price level by `c p̃_k ε` and
expected log output (relative to `Yⁿ`) by `c ỹ_k ε`. -/
theorem prop_3_7_stochastic {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ ρ : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {nm1 pm1 : Ω → ℝ}
    {e n n' yn p q : ℕ → Ω → ℝ} {s : ℕ} (hs : 1 ≤ s) {ε : Ω → ℝ} (hεs : 𝔼.E s ε = ε)
    (hunf : ∀ r < s, 𝔼.E r ε = 0) (hεb : ∃ M, ∀ ω, |ε ω| ≤ M) (c : ℝ)
    (hn : ARGrowth ρ nm1 e n)
    (hn' : ARGrowth ρ nm1 (fun t => e t + if t = s then (c * (1 - ρ)) • ε else 0) n')
    (h0 : n' 0 = n 0)
    (hp : NKPC 𝔼 β κ pm1 (fun t => n t - yn t) p) (hpa : 𝔼.Adapted p) (hpg : LinGrowth 𝔼 p)
    (hq : NKPC 𝔼 β κ pm1 (fun t => n' t - yn t) q) (hqa : 𝔼.Adapted q)
    (hqg : LinGrowth 𝔼 q) :
    q = (fun t => p t + c • shockPath s (p37 β κ ρ) ε t) ∧
      ∀ k, 𝔼.E s (n' (s + k) - n (s + k)) = (c * (1 - ρ ^ (k + 1))) • ε ∧
        𝔼.E s (q (s + k)) = 𝔼.E s (p (s + k)) + (c * p37 β κ ρ k) • ε ∧
        𝔼.E s ((n' (s + k) - yn (s + k)) - q (s + k)) =
          𝔼.E s ((n (s + k) - yn (s + k)) - p (s + k)) + (c * y37 β κ ρ k) • ε := by
  have hdec := arGrowth_shock hs c hn hn' h0
  have hx : (fun t => n' t - yn t) = fun t => (n t - yn t) + c • shockPath s (Ytil ρ) ε t := by
    funext t
    rw [← hdec t]
    abel
  rw [hx] at hq
  have hb := bounded_of_tendsto (p37_tendsto hβ hκ hρ0 hρ1)
  have hirf := p37_irfEq hβ hβ1 hκ hρ1
  have hqe := shock_response 𝔼 hβ hκ hp hpa hpg hirf hb hεs hunf hεb c hq hqa hqg
  obtain ⟨h1, -, h3⟩ := shock_response_expect 𝔼 hβ hκ hp hpa hpg hirf hb hεs hunf hεb c hq
    hqa hqg
  refine ⟨hqe, fun k => ⟨?_, h1 k, ?_⟩⟩
  · rw [hdec, map_smul]
    simp [shockPath, hεs, smul_smul, Ytil]
  · have e1 : n' (s + k) - yn (s + k) = (n (s + k) - yn (s + k)) +
        c • shockPath s (Ytil ρ) ε (s + k) := by
      rw [← hdec]; abel
    rw [e1, h3 k]
    congr 2
    unfold p37
    ring

end Woodford.NominalRigidities.SpendingGrowth
