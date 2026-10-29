/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bGovRamseyIFT
import StabilizationWelfare.NonlinearRotembergRamseyDegenerate

/-!
# The Ramsey problem with purchases when the commitment polynomial has no stable root

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2, (1.20), pp. 475–476 (the root condition
of the optimal commitment system), Chapter 6, §5 (government purchases), and Appendix A.3.

With purchases, `TidyR6bGovRamseyIFT` gives existence and uniqueness when `H = A_uG − γ_G ≠ 0`
and `κθ_X > 0` or `κθ_X < −2(1+β)` (`TidyR6bGovRamseyTree.RootOK`), and
`TidyR6bGovRamseyZero` when `H = 0`, `A_uG ≠ 0`. The remaining cases are
`H ≠ 0` with `−2(1+β) < κθ_X < 0` (both roots of `βz² − (1+β+κθ_X)z + 1` outside the unit
circle; it occurs for admissible parameters, `TidyR6bGovRamseyIFT.excluded_case`) and
`A_uG = 0 ≠ H` (`κθ_X = 0`: the roots are `1` and `1/β`). In both the linearised Ramsey operator
has NO bounded right inverse: already under perfect foresight, a constant unit forcing of the
inflation condition has no bounded solution. Hence no inverse with the properties used by the
Newton contraction exists (`TidyR6bRamseyNewton.InvBound` fails), and the sequence-space implicit
function theorem does not apply.

* `pfTree`: the perfect-foresight event tree on `ℕ` (`M f(t) = f(t+1)`, `par t = t − 1`).
* `pf_reduce`: on `pfTree`, a solution of the linearised conditions with forcing `(0, 1, 0, …)`
  has `Δ̂ = μ = 0`, the NKPC without forcing, and the targeting rule
  `H(ŷ_t − ŷ_{t−1}) + A_uGθπ_t = −(1−αβ)(σ+ω)(1−α)/(αc₀)` with `ŷ_{−1} = 0`.
* **`no_bounded_solution_inside`** (`−2(1+β) < κθ_X < 0`, `H ≠ 0`) and
  **`no_bounded_solution_unit`** (`A_uG = 0`, `H ≠ 0`): no bounded solution exists.
* **`no_bounded_solution_boundary`** (`κθ_X = −2(1+β)`, `H ≠ 0`, roots `−1`, `−1/β`): the
  alternating forcing `(−1)ᵗ(0, 1, 0, …)` resonates; no bounded solution exists.
* **`not_invBound_inside`**, **`not_invBound_unit`**, **`not_invBound_boundary`**: hence for the
  conditions with purchases no inverse family with the three properties exists.

Together with `TidyR6bGovRamseyIFT` (`TidyR6bGovRamseyTree.RootOK`: `H ≠ 0` and
`κθ_X ∉ [−2(1+β), 0]`) and
`TidyR6bGovRamseyZero` (`H = 0 ≠ A_uG`) this covers every parameter configuration with
`A_uG ≠ 0` or `H ≠ 0`. The only remaining configuration `A_uG = H = 0` forces `γ_G = 0`
(`s_C = 1`, or `ΦA_u = 0`); the linearisation is then that of the `s_C = 1` model with
`A_uG = 0`, characterised in `TidyR6bCalvoDegenerate`.
-/

namespace Woodford.StabilizationWelfare.TidyR6bGovRamseyNoRoot

universe u

open Filter Topology
open NonlinearNKMarkov hiding M_lin
open NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree TidyR6bGovRamsey TidyR6bGovRamseyTree TidyR6bRamseyNewton

/-- Woodford (2003), Ch. 7 (perfect foresight as an event tree): the next-period value. -/
def shiftL : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun f t := f (t + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Woodford (2003), Ch. 7 (**the perfect-foresight event tree**): dates `t ∈ ℕ`, the expectation
of next-period values is the next value, the parent of `t + 1` is `t`. -/
def pfTree : LagTree ℕ where
  M := shiftL
  markov := ⟨rfl, fun _ _ hC t => hC (t + 1)⟩
  par t := t - 1
  depth t := t
  depth_par x hx := by omega
  M_par f := by funext t; change f (t + 1 - 1) = f t; rw [Nat.add_sub_cancel]
  M_root f g h := by funext t; exact h (t + 1) (by omega)

/-- Woodford (2003), Ch. 7 and App. A.3: the unit forcing of the inflation condition. -/
def eOne : Fin 9 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0, 0]

/-- Woodford (2003), Ch. 7: the lag on the perfect-foresight tree. -/
theorem lag_pf (f : ℕ → ℝ) (t : ℕ) : lag0 pfTree f (t + 1) = f t := by
  simp [lag0, pfTree]

/-- Woodford (2003), Ch. 7: the lag at the root of the perfect-foresight tree. -/
theorem lag_pf_zero (f : ℕ → ℝ) : lag0 pfTree f 0 = 0 := by
  simp [lag0, pfTree]

/-- Woodford (2003), Ch. 7 and (1.20) (**the reduction under perfect foresight with a forcing
      `a_t` of the inflation condition**): a solution has `Δ̂ = μ = 0`, the NKPC
`π_t = κŷ_t + βπ_{t+1}` and the targeting rule
`H(ŷ_t − ŷ_{t−1}) + A_uGθπ_t = −(1−αβ)(σ+ω)(1−α)a_t/(αc₀)` with `ŷ_{−1} = 0`. -/
theorem pf_reduce_gen {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) {v : ℕ → Fin 9 → ℝ}
    (a : ℕ → ℝ) (hv : LRX pfTree p R γ v = fun t => a t • eOne) (t : ℕ) :
    v t 1 = p.κ * v t 0 + p.β * v (t + 1) 1 ∧
      (R.Au * Gw p R - γ) * (v t 0 - lag0 pfTree (fun s => v s 0) t) +
        R.Au * Gw p R * p.θ * v t 1 =
          -((1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0))) * a t := by
  have hr : ∀ s k, (DQrX p R γ (lagv pfTree v s) (v s) + DNr p R (Mv pfTree.M v s)) k =
      a s * eOne k := fun s k => congrFun (congrFun hv s) k
  have hM : ∀ s, Mv pfTree.M v s = v (s + 1) := fun s => rfl
  have hl : ∀ s k, lagv pfTree v s k = lag0 pfTree (fun s => v s k) s := fun _ _ => rfl
  -- the predetermined block vanishes
  have hD : ∀ s, v s 4 = 0 := zero_of_eq_lag pfTree (c := p.α) fun s => by
    have := red_DX R hp γ (lagv pfTree v s) (v s) (Mv pfTree.M v s)
    rw [hr, hr, hl] at this; simpa [eOne] using this
  have hμ : ∀ s, v s 5 + v s 6 = 0 := zero_of_eq_lag pfTree (c := p.α)
    (g := fun s => v s 5 + v s 6) fun s => by
      have := red_muX R hp γ (lagv pfTree v s) (v s) (Mv pfTree.M v s)
      rw [hr, hr, hr, hl, hl] at this
      have e := lag0_lin pfTree 1 1 (fun z => v z 5) (fun z => v z 6) s
      simp only [one_mul] at e
      simp only [e]; simpa [eOne] using this
  have hDf : (fun s => v s 4) = fun _ => 0 := funext hD
  have h7 : ∀ s, p.α * (p.θ - 1) * v s 1 - (1 - p.α) * (p.θ - 1) * ((v s 3 - v s 2) / p.c0) = 0 :=
    fun s => by rw [← red_xX R γ (lagv pfTree v s) (v s) (Mv pfTree.M v s), hr]; simp [eOne]
  refine ⟨?_, ?_⟩
  · have := red_pcX R hp γ (lagv pfTree v t) (v t) (Mv pfTree.M v t)
    rw [hr, hr, hr, hM, h7 (t + 1)] at this
    simpa [eOne] using this
  · have h0m : -((R.Au * Gw p R - γ) * lagv pfTree v t 0) - (1 - R.Φ) * R.Au * lagv pfTree v t 4 +
        (1 - p.α * p.β) * (p.σ + p.ω) * lagv pfTree v t 5 -
          (1 - p.α * p.β) * (1 + p.ω) * (lagv pfTree v t 5 + lagv pfTree v t 6) = 0 := by
      cases t with
      | zero => simp only [hl, lag_pf_zero]; ring
      | succ s =>
        simp only [hl, lag_pf]
        have := red_l1X R hp γ (lagv pfTree v s) (v s) (Mv pfTree.M v s)
        rw [hr] at this; simpa [eOne] using this
    have h := red_targetX R hp γ (lagv pfTree v t) (v t) (Mv pfTree.M v t) 0 h0m
    rw [hr, hr, hr, hr] at h
    have hl4 : lagv pfTree v t 4 = 0 := by
      rw [hl, show (fun s => v s 4) = fun _ => (0 : ℝ) from hDf]; simp [lag0]
    have hl56 : lagv pfTree v t 5 + lagv pfTree v t 6 = 0 := by
      rw [hl, hl]
      have e := lag0_lin pfTree 1 1 (fun z => v z 5) (fun z => v z 6) t
      simp only [one_mul] at e
      rw [← e, show (fun s => v s 5 + v s 6) = fun _ => (0 : ℝ) from funext hμ]; simp [lag0]
    rw [hl4, hl56, hD t, hμ t, hl] at h
    simp [eOne] at h
    linear_combination h

/-- Woodford (2003), Ch. 7 and (1.20): `pf_reduce_gen` with the constant unit forcing. -/
theorem pf_reduce {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) {v : ℕ → Fin 9 → ℝ}
    (hv : LRX pfTree p R γ v = fun _ => eOne) (t : ℕ) :
    v t 1 = p.κ * v t 0 + p.β * v (t + 1) 1 ∧
      (R.Au * Gw p R - γ) * (v t 0 - lag0 pfTree (fun s => v s 0) t) +
        R.Au * Gw p R * p.θ * v t 1 =
          -((1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0))) := by
  have h := pf_reduce_gen R hp γ (fun _ => 1) (by rw [hv]; funext t; simp) t
  simpa using h

/-- **Woodford (2003), Ch. 7, (1.20) (no bounded solution when both roots lie outside the unit
circle).** If `H ≠ 0` and `−2(1+β) < κθ_X < 0`, the linearised Ramsey system with purchases has
NO bounded solution under perfect foresight with the constant forcing `(0, 1, 0, …)`. -/
theorem no_bounded_solution_inside {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH : R.Au * Gw p R - γ ≠ 0) (hc0 : p.κ * thX p R γ < 0)
    (hc1 : -(2 * (1 + p.β)) < p.κ * thX p R γ) {v : ℕ → Fin 9 → ℝ} (B : ℝ)
    (hB : ∀ t k, |v t k| ≤ B) : LRX pfTree p R γ v ≠ fun _ => eOne := by
  intro hv
  have hθ := lt_trans one_pos hp.one_lt_θ
  have hκ := hp.κ_pos
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  have ht0 : thX p R γ ≠ 0 := fun h => by rw [h, mul_zero] at hc0; exact lt_irrefl _ hc0
  have hAG : R.Au * Gw p R ≠ 0 := fun h => ht0 (by unfold thX; rw [h]; simp)
  have hHth : (R.Au * Gw p R - γ) * thX p R γ = R.Au * Gw p R * p.θ := by unfold thX; field_simp
  set c := p.κ * thX p R γ with hc
  set K := -((1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0))) with hK
  have hK0 : K ≠ 0 := by
    have : 0 < (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) := by
      have := hp.ab_lt_one; have := hp.σ_pos; have := hp.ω_nonneg; have := hp.α_lt_one
      have := hp.α_pos; have := hp.c0_pos
      apply mul_pos (mul_pos (by linarith) (by linarith)) (div_pos (by linarith) (by positivity))
    rw [hK]; exact neg_ne_zero.2 this.ne'
  -- the scalar recursion for `ℓ_t = ŷ_{t−1}`
  set H := R.Au * Gw p R - γ with hHd
  set P := R.Au * Gw p R * p.θ with hPd
  have hP0 : P ≠ 0 := mul_ne_zero hAG hθ.ne'
  have hcH : c * H = p.κ * P := by
    rw [hc, mul_assoc, mul_comm (thX p R γ) H, hHth]
  set ℓ : ℕ → ℝ := fun t => lag0 pfTree (fun s => v s 0) t with hℓ
  have hℓs : ∀ t, ℓ (t + 1) = v t 0 := fun t => lag_pf _ t
  have hℓ0 : ℓ 0 = 0 := lag_pf_zero _
  have key : ∀ t, H * (p.β * ℓ (t + 2) - (1 + p.β + c) * ℓ (t + 1) + ℓ t) + (1 - p.β) * K = 0 :=
    fun t => by
      have h1 := (pf_reduce R hp γ hv t).1
      have T0 := (pf_reduce R hp γ hv t).2
      have T1 := (pf_reduce R hp γ hv (t + 1)).2
      rw [← hK] at T0 T1
      rw [show lag0 pfTree (fun s => v s 0) (t + 1) = v t 0 from lag_pf _ t] at T1
      rw [show lag0 pfTree (fun s => v s 0) t = ℓ t from rfl] at T0
      rw [show ℓ (t + 2) = v (t + 1) 0 from hℓs (t + 1), hℓs t]
      linear_combination P * h1 - T0 + p.β * T1 - v t 0 * hcH
  set ℓst := (1 - p.β) * K / (H * c) with hℓst
  have hc0' : c ≠ 0 := hc0.ne
  have hrec : ∀ t, p.β * (ℓ (t + 2) - ℓst) - (1 + p.β + c) * (ℓ (t + 1) - ℓst) +
      (ℓ t - ℓst) = 0 := fun t => by
    have h := key t
    have e : p.β * (ℓ (t + 2) - ℓst) - (1 + p.β + c) * (ℓ (t + 1) - ℓst) + (ℓ t - ℓst) =
        (H * (p.β * ℓ (t + 2) - (1 + p.β + c) * ℓ (t + 1) + ℓ t) + (1 - p.β) * K) / H := by
      rw [hℓst]; field_simp; ring
    rw [e, h, zero_div]
  have hbd : ∀ t, |ℓ t - ℓst| ≤ |B| + |ℓst| := fun t => by
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    cases t with
    | zero => rw [hℓ0, abs_zero]; exact abs_nonneg _
    | succ s => rw [hℓs s]; exact (hB s 0).trans (le_abs_self B)
  have hs : |1 + p.β + c| < 1 + p.β := by rw [abs_lt]; constructor <;> linarith
  have hz := NonlinearRotembergRamseyDegenerate.rec_bounded_zero hβ hβ1 hs
    (ℓ := fun t => ℓ t - ℓst) (B := |B| + |ℓst|) (fun t => hrec t) hbd 0
  simp only [hℓ0, zero_sub, neg_eq_zero] at hz
  rw [hℓst] at hz
  have : (1 - p.β) * K ≠ 0 := mul_ne_zero (by linarith) hK0
  exact this (by rw [div_eq_zero_iff] at hz; exact hz.resolve_right (mul_ne_zero hH hc0'))

/-- **Woodford (2003), Ch. 7, (1.20) (no bounded solution with a unit root).** If `A_uG = 0` and
`H ≠ 0` (so `κθ_X = 0`, roots `1` and `1/β`), the linearised Ramsey system with purchases has NO
bounded solution under perfect foresight with the constant forcing `(0, 1, 0, …)`: output then
grows linearly. -/
theorem no_bounded_solution_unit {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hAG : R.Au * Gw p R = 0) (hH : R.Au * Gw p R - γ ≠ 0) {v : ℕ → Fin 9 → ℝ} (B : ℝ)
    (hB : ∀ t k, |v t k| ≤ B) : LRX pfTree p R γ v ≠ fun _ => eOne := by
  intro hv
  set K := -((1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0))) with hK
  have hK0 : K ≠ 0 := by
    have : 0 < (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) := by
      have := hp.ab_lt_one; have := hp.σ_pos; have := hp.ω_nonneg; have := hp.α_lt_one
      have := hp.α_pos; have := hp.c0_pos
      apply mul_pos (mul_pos (by linarith) (by linarith)) (div_pos (by linarith) (by positivity))
    rw [hK]; exact neg_ne_zero.2 this.ne'
  -- output grows linearly
  have hy : ∀ t, v t 0 = (t + 1) * (K / (R.Au * Gw p R - γ)) := by
    intro t
    induction t with
    | zero =>
      have T := (pf_reduce R hp γ hv 0).2
      rw [← hK, lag_pf_zero] at T
      have h0 : R.Au * Gw p R * p.θ * v 0 1 = 0 := by rw [hAG]; ring
      have T' : (R.Au * Gw p R - γ) * v 0 0 = K := by linarith
      field_simp; push_cast; linarith
    | succ s ih =>
      have T := (pf_reduce R hp γ hv (s + 1)).2
      rw [← hK, lag_pf] at T
      have h0 : R.Au * Gw p R * p.θ * v (s + 1) 1 = 0 := by rw [hAG]; ring
      have T' : (R.Au * Gw p R - γ) * (v (s + 1) 0 - v s 0) = K := by linarith
      rw [ih] at T'
      field_simp at T' ⊢; push_cast; linarith
  obtain ⟨t, ht⟩ := exists_nat_gt ((|B| + 1) / |K / (R.Au * Gw p R - γ)|)
  have hKH : 0 < |K / (R.Au * Gw p R - γ)| := abs_pos.2 (div_ne_zero hK0 hH)
  have h1 := hB t 0
  rw [hy t, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t + 1)] at h1
  rw [div_lt_iff₀ hKH] at ht
  nlinarith [le_abs_self B, abs_nonneg (K / (R.Au * Gw p R - γ))]

/-- **Woodford (2003), Ch. 7, (1.20) (no bounded solution on the boundary `κθ_X = −2(1+β)`).**
If `H ≠ 0` and `κθ_X = −2(1+β)` (roots `−1` and `−1/β`), the linearised Ramsey system with
purchases has NO bounded solution under perfect foresight with the alternating forcing
`(−1)ᵗ(0, 1, 0, …)` (resonance with the root `−1`). -/
theorem no_bounded_solution_boundary {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH : R.Au * Gw p R - γ ≠ 0) (hc : p.κ * thX p R γ = -(2 * (1 + p.β)))
    {v : ℕ → Fin 9 → ℝ} (B : ℝ) (hB : ∀ t k, |v t k| ≤ B) :
    LRX pfTree p R γ v ≠ fun t => (-1 : ℝ) ^ t • eOne := by
  intro hv
  have hθ := lt_trans one_pos hp.one_lt_θ
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  have ht0 : thX p R γ ≠ 0 := fun h => by rw [h, mul_zero] at hc; linarith
  have hAG : R.Au * Gw p R ≠ 0 := fun h => ht0 (by unfold thX; rw [h]; simp)
  have hHth : (R.Au * Gw p R - γ) * thX p R γ = R.Au * Gw p R * p.θ := by unfold thX; field_simp
  set K := -((1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0))) with hK
  have hK0 : K ≠ 0 := by
    have : 0 < (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) := by
      have := hp.ab_lt_one; have := hp.σ_pos; have := hp.ω_nonneg; have := hp.α_lt_one
      have := hp.α_pos; have := hp.c0_pos
      apply mul_pos (mul_pos (by linarith) (by linarith)) (div_pos (by linarith) (by positivity))
    rw [hK]; exact neg_ne_zero.2 this.ne'
  set H := R.Au * Gw p R - γ with hHd
  set P := R.Au * Gw p R * p.θ with hPd
  have hcH : -(2 * (1 + p.β)) * H = p.κ * P := by
    rw [← hc, mul_assoc, mul_comm (thX p R γ) H, hHth]
  set ℓ : ℕ → ℝ := fun t => lag0 pfTree (fun s => v s 0) t with hℓ
  have hℓs : ∀ t, ℓ (t + 1) = v t 0 := fun t => lag_pf _ t
  have hℓ0 : ℓ 0 = 0 := lag_pf_zero _
  have key : ∀ t, H * (p.β * ℓ (t + 2) + (1 + p.β) * ℓ (t + 1) + ℓ t) +
      (K * (-1) ^ t - p.β * (K * (-1) ^ (t + 1))) = 0 := fun t => by
    have h1 := (pf_reduce_gen R hp γ (fun t => (-1 : ℝ) ^ t) hv t).1
    have T0 := (pf_reduce_gen R hp γ (fun t => (-1 : ℝ) ^ t) hv t).2
    have T1 := (pf_reduce_gen R hp γ (fun t => (-1 : ℝ) ^ t) hv (t + 1)).2
    rw [← hK] at T0 T1
    rw [show lag0 pfTree (fun s => v s 0) (t + 1) = v t 0 from lag_pf _ t] at T1
    rw [show lag0 pfTree (fun s => v s 0) t = ℓ t from rfl] at T0
    rw [show ℓ (t + 2) = v (t + 1) 0 from hℓs (t + 1), hℓs t]
    linear_combination P * h1 - T0 + p.β * T1 - v t 0 * hcH
  -- `u_t = (−1)ᵗℓ_t` has a unit root and a constant forcing
  set u : ℕ → ℝ := fun t => (-1) ^ t * ℓ t with hu
  set F := -((1 + p.β) * K / H) with hF
  have hurec : ∀ t, p.β * (u (t + 2) - u (t + 1)) - (u (t + 1) - u t) = F := fun t => by
    have h := key t
    simp only [hu, hF]
    have e2 : (-1 : ℝ) ^ (t + 2) = (-1) ^ t := by rw [pow_add]; norm_num
    have e1 : (-1 : ℝ) ^ (t + 1) = -(-1) ^ t := by rw [pow_succ]; ring
    rw [e2, e1]
    have hsq : ((-1 : ℝ) ^ t) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e1] at h
    rw [show -((1 + p.β) * K / H) = (-((1 + p.β) * K)) / H by ring, eq_div_iff hH]
    linear_combination (-1 : ℝ) ^ t * h - (1 + p.β) * K * hsq
  -- the increments are pinned at the fixed point, so `u` grows linearly
  have hFne : F ≠ 0 := by
    rw [hF]; exact neg_ne_zero.2 (div_ne_zero (mul_ne_zero (by linarith) hK0) hH)
  set dst := F / (p.β - 1) with hdst
  have hdst0 : dst ≠ 0 := div_ne_zero hFne (by linarith)
  have hub : ∀ t, |u t| ≤ |B| := fun t => by
    simp only [hu, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    cases t with
    | zero => rw [hℓ0, abs_zero]; exact abs_nonneg _
    | succ s => rw [hℓs s]; exact (hB s 0).trans (le_abs_self B)
  have he : ∀ t, (u (t + 1) - u t - dst) = (1 / p.β) ^ t * (u 1 - u 0 - dst) := fun t => by
    induction t with
    | zero => simp
    | succ k ih =>
      have h := hurec k
      have hb1 : p.β - 1 ≠ 0 := by linarith
      have hd : dst * (p.β - 1) = F := by rw [hdst]; field_simp
      have step : u (k + 2) - u (k + 1) - dst = 1 / p.β * (u (k + 1) - u k - dst) := by
        field_simp; linear_combination h - hd
      rw [show k + 1 + 1 = k + 2 from rfl, step, ih, pow_succ]
      ring
  have hz : u 1 - u 0 - dst = 0 := by
    refine NonlinearRotembergRamseyDegenerate.geom_bounded_zero (r := 1 / p.β)
      (C := |B| + |B| + |dst|) ?_ fun t => ?_
    · rw [abs_of_pos (by positivity), lt_div_iff₀ hβ]; linarith
    · rw [← he t]
      exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hub _) (hub _)))
        le_rfl)
  have hlin : ∀ t, u t = u 0 + t * dst := fun t => by
    induction t with
    | zero => simp
    | succ k ih =>
      have := he k
      rw [hz, mul_zero] at this
      push_cast
      linarith
  obtain ⟨t, ht⟩ := exists_nat_gt ((2 * |B| + 1) / |dst|)
  have hd : 0 < |dst| := abs_pos.2 hdst0
  rw [div_lt_iff₀ hd] at ht
  have h1 := hub t
  have h0 := hub 0
  rw [hlin t] at h1
  have : |(t : ℝ) * dst| ≤ |B| + |B| := by
    have := abs_sub (u 0 + t * dst) (u 0)
    simp only [add_sub_cancel_left] at this
    linarith
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg t)] at this
  linarith

/-- **Woodford (2003), Ch. 7 (no inverse when both roots lie outside the unit circle).** If
`s_C > 0`, `H ≠ 0` and `−2(1+β) < κθ_X < 0`, no inverse family of the linearised Ramsey
operator with purchases has the three properties of `TidyR6bRamseyNewton.InvBound`. -/
theorem not_invBound_inside {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH : Hy p R sC ≠ 0) (hc0 : p.κ * thX p R (gamG p R sC) < 0)
    (hc1 : -(2 * (1 + p.β)) < p.κ * thX p R (gamG p R sC))
    (Li : ∀ {Y : Type}, LagTree Y → (Y → Fin 9 → ℝ) → Y → Fin 9 → ℝ) :
    ¬ InvBound (QdG p R sC) (Nd p R) Li := by
  rintro ⟨⟨K, hK0, hK⟩, hR, -⟩
  have hr : ∀ (t : ℕ) k, |(fun _ : ℕ => eOne) t k| ≤ 1 := fun t k => by
    fin_cases k <;> simp [eOne]
  have hRt := hR pfTree (fun _ => eOne) 1 zero_le_one hr
  have hb : ∀ y, ‖(fun _ : ℕ => eOne) y‖ ≤ 1 := fun y =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by rw [Real.norm_eq_abs]; exact hr y k
  refine no_bounded_solution_inside R hp (gamG p R sC) hH hc0 hc1 (v := Li pfTree fun _ => eOne)
    (K * 1) (fun t k => ?_) ?_
  · have := (norm_le_pi_norm _ k).trans (hK pfTree _ 1 zero_le_one hb t)
    rwa [Real.norm_eq_abs] at this
  · funext x
    rw [← TidyR6bGovRamseyIFT.LG_QdG R hp hs]
    exact congrFun hRt x

/-- **Woodford (2003), Ch. 7 (no inverse with a unit root).** If `s_C > 0`, `A_uG = 0` and
`H ≠ 0`, no inverse family of the linearised Ramsey operator with purchases has the three
properties of `TidyR6bRamseyNewton.InvBound`. -/
theorem not_invBound_unit {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hAG : R.Au * Gw p R = 0) (hH : Hy p R sC ≠ 0)
    (Li : ∀ {Y : Type}, LagTree Y → (Y → Fin 9 → ℝ) → Y → Fin 9 → ℝ) :
    ¬ InvBound (QdG p R sC) (Nd p R) Li := by
  rintro ⟨⟨K, hK0, hK⟩, hR, -⟩
  have hr : ∀ (t : ℕ) k, |(fun _ : ℕ => eOne) t k| ≤ 1 := fun t k => by
    fin_cases k <;> simp [eOne]
  have hRt := hR pfTree (fun _ => eOne) 1 zero_le_one hr
  have hb : ∀ y, ‖(fun _ : ℕ => eOne) y‖ ≤ 1 := fun y =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by rw [Real.norm_eq_abs]; exact hr y k
  refine no_bounded_solution_unit R hp (gamG p R sC) hAG hH (v := Li pfTree fun _ => eOne)
    (K * 1) (fun t k => ?_) ?_
  · have := (norm_le_pi_norm _ k).trans (hK pfTree _ 1 zero_le_one hb t)
    rwa [Real.norm_eq_abs] at this
  · funext x
    rw [← TidyR6bGovRamseyIFT.LG_QdG R hp hs]
    exact congrFun hRt x

/-- **Woodford (2003), Ch. 7 (no inverse on the boundary `κθ_X = −2(1+β)`).** If `s_C > 0`,
`H ≠ 0` and `κθ_X = −2(1+β)`, no inverse family of the linearised Ramsey operator with purchases
has the three properties of `TidyR6bRamseyNewton.InvBound`. -/
theorem not_invBound_boundary {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH : Hy p R sC ≠ 0) (hc : p.κ * thX p R (gamG p R sC) = -(2 * (1 + p.β)))
    (Li : ∀ {Y : Type}, LagTree Y → (Y → Fin 9 → ℝ) → Y → Fin 9 → ℝ) :
    ¬ InvBound (QdG p R sC) (Nd p R) Li := by
  rintro ⟨⟨K, hK0, hK⟩, hR, -⟩
  have hr : ∀ (t : ℕ) k, |(fun t : ℕ => (-1 : ℝ) ^ t • eOne) t k| ≤ 1 := fun t k => by
    fin_cases k <;> simp [eOne]
  have hRt := hR pfTree (fun t => (-1 : ℝ) ^ t • eOne) 1 zero_le_one hr
  have hb : ∀ y, ‖(fun t : ℕ => (-1 : ℝ) ^ t • eOne) y‖ ≤ 1 := fun y =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by rw [Real.norm_eq_abs]; exact hr y k
  refine no_bounded_solution_boundary R hp (gamG p R sC) hH hc
    (v := Li pfTree fun t => (-1 : ℝ) ^ t • eOne) (K * 1) (fun t k => ?_) ?_
  · have := (norm_le_pi_norm _ k).trans (hK pfTree _ 1 zero_le_one hb t)
    rwa [Real.norm_eq_abs] at this
  · funext x
    rw [← TidyR6bGovRamseyIFT.LG_QdG R hp hs]
    exact congrFun hRt x

end Woodford.StabilizationWelfare.TidyR6bGovRamseyNoRoot
