/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureMultiplicity

/-!
# Example B: the full next-state kernel `K^N_k`

Woodford (2003), *Interest and Prices*, Chapter 8, p. 539 and Assumption 8.1 (p. 541), for the
counterexample `OptimalRulesMeasureCounterexample.eBP` (`Z_{t+1} = Z_t + z_t`,
`E_t z_{t+1} = Z_t + z_t + i_t + c_t`, loss `½(z² + i²)`, `β = 1/2`). The next state
`(Z_1, M_0)` responds to the forcing path through the kernel
`N(n, g) = N(n, 0) + ∑_k K^N_k g_k` (`OptimalRulesMeasureGeneral.nextS_hasSum`);
`OptimalRulesMeasureCounterexample.eB_KN0` computed `K^N_0` only.

## Results

* `eB_KN`: **for every `k`**, `K^N_k = (−2^{−k}/3, 2^{−k}/15 + [k = 0]/5)'` — a unit `c_k` (news
  at horizon `k`) moves `Z_1` by `−2^{−k}/3` and `M_0` by `2^{−k}/15`, plus `1/5` on impact.
* `eB_eKN_all`: along the unit-root left eigen-direction `e = (1, 2)` of `H`,
  `e'K^N_0 = 1/5` and `e'K^N_k = −2^{−k}/5` for `k ≥ 1`; in particular **`e'K^N_k ≠ 0` for every
  `k`** (`eB_eKN_ne_zero`): every horizon of news feeds the conserved direction.
* `eB_eKN_partial`, `eB_eKN_hasSum`: the cumulative responses are `∑_{j ≤ k} e'K^N_j = 2^{−k}/5`,
  so `∑_k e'K^N_k = 0` and `∑_k |∑_{j ≤ k} e'K^N_j| = 2/5 < ∞` — exactly the summability that the
  perfect-foresight bound permits (`OptimalRulesMeasureKernel.kernel_summable`), while
  `∑_k |e'K^N_k| = 2/5 ≠ 0`.
* `eB_eulerRoot_two`: by the symplectic pairing the Euler pencil of `eBP` has, besides the unit
  root `1` (`OptimalRulesMeasureSpectrum.eB_eulerRoot_one`), its partner `1/(β·1) = 2 = β⁻¹`,
  on the edge of the spectral gap (`OptimalRulesMeasureMultiplicity.eulerRoot_gap`).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureKernelB

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ OptimalRulesMeasureKernel
  OptimalRulesMeasureGeneral OptimalRulesMeasureCounterexample

/-- Woodford (2003), App. G (tool): the unit impulse at date `k` as a scalar path. -/
theorem imp_apply (k j : ℕ) : imp k () j () = if j = k then (1 : ℝ) else 0 := by
  by_cases hj : j = k
  · subst hj
    simp [imp]
  · simp [imp, hj]

/-- Woodford (2003), App. G (tool): the forward sum of the impulse at `k`,
`U_0 = −∑_m 2^{−m} [m = k] = −2^{−k}`. -/
theorem fwd_imp_zero (k : ℕ) : fwd (fun j => imp k () j ()) 0 = -(1 / 2 : ℝ) ^ k := by
  rw [fwd, tsum_eq_single k fun j hj => by simp [imp_apply, hj]]
  simp [imp_apply]

/-- Woodford (2003), App. G (tool): `U_1 = 2U_0 + 2c_0 = −2·2^{−k} + 2[k = 0]`. -/
theorem fwd_imp_one (k : ℕ) :
    fwd (fun j => imp k () j ()) 1 = -2 * (1 / 2 : ℝ) ^ k + 2 * (if k = 0 then 1 else 0) := by
  have hb : ∀ j, |(fun j => imp k () j ()) j| ≤ 1 := fun j => by
    simp only [imp_apply]
    split_ifs <;> simp
  rw [fwd_succ hb 0, fwd_imp_zero, imp_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · simp only [show ¬ (0 = k) from fun h => hk h.symm, hk, ↓reduceIte]
    ring

/-- Woodford (2003), p. 539, for `eBP`: **the next-state kernel at every lag**,
`K^N_k = (−2^{−k}/3, 2^{−k}/15 + [k = 0]/5)'` — the response of `(Z_1, M_0)` to a unit `c_k`. -/
theorem eB_KN (k : ℕ) :
    KN eB_pf k = Matrix.of fun a _ => Sum.elim (fun _ => -(1 / 2 : ℝ) ^ k / 3)
      (fun _ => (1 / 2 : ℝ) ^ k / 15 + (if k = 0 then 1 / 5 else 0)) a := by
  have hg0 : imp k () 0 () = if k = 0 then (1 : ℝ) else 0 := by
    rw [imp_apply]
    simp only [eq_comm]
  ext a i
  rcases i
  rcases a with u | u <;> rcases u
  · simp only [KN, KY, Matrix.of_apply, Sum.elim_inl,
      (eB_sol 0 (bddSeq_imp k ()) 1).1, (eB_sol 0 (bddSeq_zero (ι := Unit)) 1).1, eBy, eBS, eBL,
      fwd_zero, fwd_imp_zero, fwd_imp_one, hg0]
    by_cases hk : k = 0 <;> simp [hk] <;> ring
  · simp only [KN, KΦ, Matrix.of_apply, Sum.elim_inr,
      (eB_sol 0 (bddSeq_imp k ()) 1).2, (eB_sol 0 (bddSeq_zero (ι := Unit)) 1).2, eBφ, eBS, eBL,
      fwd_zero, fwd_imp_zero, hg0]
    by_cases hk : k = 0 <;> simp [hk] <;> ring

/-- Woodford (2003), p. 539, for `eBP`: `K^N_k` at `k = 0` agrees with
`OptimalRulesMeasureCounterexample.eB_KN0`. -/
theorem eB_KN_zero_eq : KN eB_pf 0 = Matrix.of fun a _ =>
    Sum.elim (fun _ => -1 / 3) (fun _ => (4 / 15 : ℝ)) a := eB_KN0

/-- Woodford (2003), p. 539, for `eBP`: **the forcing of the unit-root direction `e = (1, 2)` at
every lag**, `e'K^N_k = 1/5` for `k = 0` and `−2^{−k}/5` for `k ≥ 1`. -/
theorem eB_eKN_all (k : ℕ) :
    Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf k =
      fun _ => if k = 0 then 1 / 5 else -(1 / 2 : ℝ) ^ k / 5 := by
  rw [eB_KN]
  funext j
  by_cases hk : k = 0
  · subst hk
    simp [vecMul, dotProduct, Fintype.sum_sum_type]
    norm_num
  · simp [vecMul, dotProduct, Fintype.sum_sum_type, hk]
    ring

/-- Woodford (2003), Assumption 8.1, p. 541, for `eBP`: **`e'K^N_k ≠ 0` at every lag `k`** — news
at every horizon feeds the unit-root left eigen-direction of `H`. -/
theorem eB_eKN_ne_zero (k : ℕ) :
    (Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf k) () ≠ 0 := by
  rw [eB_eKN_all]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
    intro h
    linarith

/-- Woodford (2003), p. 539, for `eBP`: the cumulative forcing of `e`,
`∑_{j ≤ k} e'K^N_j = 2^{−k}/5`. -/
theorem eB_eKN_partial (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf j) () =
      (1 / 2 : ℝ) ^ k / 5 := by
  induction k with
  | zero => simp [eB_eKN_all]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, eB_eKN_all]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    ring

/-- Woodford (2003), p. 539 and Assumption 8.1, for `eBP`: **the total forcing of `e` vanishes**,
`∑_k e'K^N_k = 0`, although no term does (`eB_eKN_ne_zero`). -/
theorem eB_eKN_hasSum :
    HasSum (fun k => (Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf k) ()) 0 := by
  rw [← hasSum_nat_add_iff' 1]
  have h : (fun k => (Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf (k + 1)) ()) =
      fun k => -(1 / 10 : ℝ) * (1 / 2) ^ k := by
    funext k
    rw [eB_eKN_all]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, pow_succ]
    ring
  rw [h, Finset.sum_range_one, eB_eKN_all]
  simp only [↓reduceIte]
  have := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
    (-(1 / 10 : ℝ))
  convert this using 1
  norm_num

/-- Woodford (2003), p. 539, for `eBP`: the absolute forcing `∑_k |e'K^N_k| = 2/5` and the
absolute cumulative forcing `∑_k |∑_{j ≤ k} e'K^N_j| = 2/5`, both finite (the perfect-foresight
bound). -/
theorem eB_eKN_abs_hasSum :
    HasSum (fun k => |(Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf k) ()|) (2 / 5) ∧
      HasSum (fun k => |∑ j ∈ Finset.range (k + 1),
        (Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf j) ()|) (2 / 5) := by
  have hg := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [← hasSum_nat_add_iff' 1]
    have h : (fun k => |(Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf (k + 1)) ()|) =
        fun k => (1 / 10 : ℝ) * (1 / 2) ^ k := by
      funext k
      rw [eB_eKN_all]
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2) ^ (k + 1)),
        abs_of_pos (by norm_num : (0 : ℝ) < 5), pow_succ]
      ring
    rw [h, Finset.sum_range_one, eB_eKN_all]
    simp only [↓reduceIte]
    convert hg.mul_left (1 / 10 : ℝ) using 1
    norm_num
  · have h : (fun k => |∑ j ∈ Finset.range (k + 1),
        (Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf j) ()|) =
        fun k => (1 / 5 : ℝ) * (1 / 2) ^ k := by
      funext k
      rw [eB_eKN_partial, abs_of_nonneg (by positivity)]
      ring
    rw [h]
    convert hg.mul_left (1 / 5 : ℝ) using 1
    norm_num

/-- Woodford (2003), App. G.1, for `eBP`: **the Euler pencil has the root `2 = 1/(β·1)`**, the
symplectic partner of the unit root `1` (`β = 1/2`). -/
theorem eB_eulerRoot_two : OptimalRulesMeasureSpectrum.EulerRoot eBP 2 := by
  have h := (OptimalRulesMeasureEulerPencil.eulerRoot_pairMap_iff eBP one_ne_zero).mpr
    OptimalRulesMeasureSpectrum.eB_eulerRoot_one
  have h2 : OptimalRulesMeasureEulerPencil.pairMap eBP.β 1 = 2 := by
    simp [OptimalRulesMeasureEulerPencil.pairMap, eBP]
  rwa [h2] at h

end Woodford.OptimalPolicyRules.OptimalRulesMeasureKernelB
