/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralFOC
import OptimalPolicyRules.Adjugate

/-!
# The optimal target criterion (1.23) and optimal instrument rules

Woodford (2003), *Interest and Prices*, Chapter 8, Sections 1.4–1.5 (pp. 552–559) and
Appendix G.2 (p. 719).

The general Giannoni–Woodford theory (Proposition 8.1 and the proofs of Propositions 8.2–8.4,
in Giannoni and Woodford 2002a) is deferred. Proposition 8.1's conclusion is the
hypothesis structure `Prop81Conclusion`; everything that follows from it is proved here.

## Lag-operator conventions

* Matrix lag polynomials act through their coefficient matrices `Bc B j`:
  `B(L) q_t = ∑_{j ≤ D} B_j q_{t-j}`, with `D` a bound on the degrees.
* For the scalar results of Section 1.5, `lagOp` is the backward lag `L` on real processes (with
  zero pre-sample values) and `fwdOp 𝔼` is the forward operator `(F x)_t = E_t x_{t+1}`; a
  polynomial `φ(L⁻¹)` acts as `aeval (fwdOp 𝔼) φ`, which equals `E_t φ(L⁻¹) x_t` on adapted
  processes (`aeval_fwdOp_apply`).

## Main results

* `eq122_coeff_zero`, `eq122_coeff_succ`: (1.22) coefficient by coefficient.
* `lag_identity`: `B(L) (I − ΛL) M_t = α(L) M_t` for any sequence.
* `eq123_of_eq119_eq120`: (1.23) holds for `t ≥ t₀ + D` when (1.19) and (1.20) hold for `t ≥ t₀`
  (footnote 14); `eq120_of_criterion`: the converse on p. 554.
* `instrument_coefficient`, `instrument_coefficient_A86`: the coefficient of `i_t` in (1.23),
  `T_i'WT_i + B₂'Q(0)T̃'WT_i`, equal to `λ_i` under Assumption 8.6 (p. 556).
* `eq128_iff`: (1.23) ⟺ the implicit instrument rule (1.28) when `λ_i ≠ 0`; `eq129`: (1.29).
* `initial_multiplier_unique`: Assumption 8.5 makes `M_{t₀-1}` uniquely recoverable from the
  history of the target variables (the essential step in Prop 8.2).
* `Prop82.prop82_optimal`, `prop82_unique`, `prop82_exists`: Proposition 8.2, conditional on
  Proposition 8.1's conclusion.
* `eq_zero_of_aeval_fwdOp_eq_zero`, `eq130_iff_eq131`: the lemma (1.30) ⟺ (1.31), proved in
  full.
* `aeval_fwdOp_reverse_lag`, `p558_identity`: the lag-operator identity of p. 558.
* `prop84_conditional`: Proposition 8.4 given the factorisation of Proposition 8.3.
-/

namespace Woodford.OptimalPolicyRules.TargetCriterion

open Matrix Polynomial Filter Topology GeneralSetup GeneralFOC GeneralFOC.LQ Adjugate
open ExpectationTools (EC EC_smul EC_add norm_EC_le EC_tower BoundedC)

variable {Ω : Type*}

/-! ### Lag polynomials with matrix coefficients -/

namespace Lag

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), p. 553: the `j`-th coefficient matrix `B_j` of a matrix lag polynomial
`B(L) = ∑_j B_j L^j`. -/
noncomputable def Bc (B : Matrix ι ι ℝ[X]) (j : ℕ) : Matrix ι ι ℝ := B.map (fun p => p.coeff j)

/-- Woodford (2003), eq. (1.22), p. 553, coefficient `0`: `B_0 = α_0 I`. -/
theorem eq122_coeff_zero {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) : Bc B 0 = α.coeff 0 • (1 : Matrix ι ι ℝ) := by
  have hB : B * lagMat Λ = B - (X : ℝ[X]) • (B * Λ.map C) := by
    rw [lagMat, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  rw [hB] at h
  ext i c
  have := congrArg (fun p => p.coeff 0) (congrFun (congrFun h i) c)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, coeff_sub, coeff_X_mul_zero,
    sub_zero] at this
  rw [Bc, map_apply, this, Matrix.smul_apply, smul_eq_mul, one_apply, one_apply]
  split_ifs <;> simp

/-- Woodford (2003), eq. (1.22), p. 553, coefficient `k + 1`: `B_{k+1} − B_k Λ = α_{k+1} I`. -/
theorem eq122_coeff_succ {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) (k : ℕ) :
    Bc B (k + 1) - Bc B k * Λ = α.coeff (k + 1) • (1 : Matrix ι ι ℝ) := by
  have hB : B * lagMat Λ = B - (X : ℝ[X]) • (B * Λ.map C) := by
    rw [lagMat, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  rw [hB] at h
  ext i c
  have := congrArg (fun p => p.coeff (k + 1)) (congrFun (congrFun h i) c)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, coeff_sub, coeff_X_mul,
    mul_apply, map_apply, finsetSum_coeff, coeff_mul_C] at this
  simp only [Matrix.sub_apply, Bc, map_apply, mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [this, one_apply, one_apply]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), eq. (1.22): the coefficient matrices of `B` vanish above its degree. -/
theorem Bc_eq_zero_of_natDegree {B : Matrix ι ι ℝ[X]} {D : ℕ}
    (hB : ∀ i c, (B i c).natDegree ≤ D) {j : ℕ} (hj : D < j) : Bc B j = 0 := by
  ext i c
  exact coeff_eq_zero_of_natDegree_lt ((hB i c).trans_lt hj)

/-- Woodford (2003), p. 553: `B(L) (I − Λ L) M = α(L) M`, as an identity of finite sums for an
arbitrary sequence `g_j = M_{t-j}`: `∑_{j ≤ D} B_j (g_j − Λ g_{j+1}) = ∑_{j ≤ D} α_j g_j` when the
degrees of `B` and `α` are at most `D`. -/
theorem lag_identity {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) {D : ℕ} (hB : ∀ i c, (B i c).natDegree ≤ D)
    (hα : α.natDegree ≤ D) (g : ℕ → ι → ℝ) :
    ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ (g j - Λ *ᵥ g (j + 1)) =
      ∑ j ∈ Finset.range (D + 1), α.coeff j • g j := by
  -- the general identity with a boundary term
  have key : ∀ N, ∑ j ∈ Finset.range (N + 1), Bc B j *ᵥ (g j - Λ *ᵥ g (j + 1)) =
      ∑ j ∈ Finset.range (N + 1), α.coeff j • g j - (Bc B N * Λ) *ᵥ g (N + 1) := by
    intro N
    induction N with
    | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, eq122_coeff_zero h,
        mulVec_sub, smul_mulVec, one_mulVec, smul_mul, Matrix.one_mul]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j => α.coeff j • g j) (N + 1)]
      have hv := congrArg (fun M : Matrix ι ι ℝ => M *ᵥ g (N + 1)) (eq122_coeff_succ h N)
      simp only [sub_mulVec, smul_mulVec, one_mulVec] at hv
      rw [mulVec_sub, mulVec_mulVec]
      linear_combination (norm := module) hv
  rw [key D]
  have hs := eq122_coeff_succ h D
  rw [Bc_eq_zero_of_natDegree hB (Nat.lt_succ_self D),
    coeff_eq_zero_of_natDegree_lt (hα.trans_lt (Nat.lt_succ_self D)), zero_smul, zero_sub,
    neg_eq_zero] at hs
  rw [hs, zero_mulVec, sub_zero]

end Lag

open Lag

/-! ### The target criterion (1.23) -/

namespace Crit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), eq. (1.23), p. 554: the left side
`α(L) v_t + B₂' B(L) q_t = ∑_{j ≤ D} α_j v_{t-j} + B₂' ∑_{j ≤ D} B_j q_{t-j}`, with
`v_t = T_i'W(τ_t − τ*)` (1.26) and `q_t = E_t Q(L⁻¹) T̃'W(τ_t − τ*)` (1.25). -/
noncomputable def crit (α : ℝ[X]) (B : Matrix ι ι ℝ[X]) (D : ℕ) (B2 : ι → ℝ)
    (v : ℕ → Ω → ℝ) (q : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (D + 1), α.coeff j * v (t - j) ω +
    B2 ⬝ᵥ ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ q (t - j) ω

/-- Woodford (2003), p. 553: premultiplying (1.20) by `B(L)`:
`α(L) M_t = B(L) q_t` for `t ≥ t₀ + D` when (1.20) `M_t = Λ M_{t-1} + q_t` holds for `t ≥ t₀`. -/
theorem alphaM_eq_Bq {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) {D : ℕ} (hB : ∀ i c, (B i c).natDegree ≤ D)
    (hα : α.natDegree ≤ D) {M q : ℕ → Ω → ι → ℝ} {t0 : ℕ}
    (h120 : ∀ t, t0 ≤ t → ∀ ω, M t ω = Λ *ᵥ M (t - 1) ω + q t ω) {t : ℕ} (ht : t0 + D ≤ t)
    (ω : Ω) :
    ∑ j ∈ Finset.range (D + 1), α.coeff j • M (t - j) ω =
      ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ q (t - j) ω := by
  rw [← lag_identity h hB hα (fun j => M (t - j) ω)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 := h120 (t - j) (by omega) ω
  have h2 : t - (j + 1) = t - j - 1 := by omega
  rw [h2, h1, add_sub_cancel_left]

/-- Woodford (2003), eq. (1.23) and fn 14, p. 554: if (1.19) `B₂' M_t + v_t = 0` and (1.20)
`M_t = Λ M_{t-1} + q_t` hold for all `t ≥ t₀`, then the target criterion
`α(L) v_t + B₂' B(L) q_t = 0` holds for all `t ≥ t₀ + D` (`D` bounding the degrees of `α`, `B`;
`D = rank Λ` works, `Adjugate.natDegree_alpha_le_rank`, `natDegree_Bpoly_le_rank`). -/
theorem eq123_of_eq119_eq120 {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) {D : ℕ} (hB : ∀ i c, (B i c).natDegree ≤ D)
    (hα : α.natDegree ≤ D) (B2 : ι → ℝ) {M q : ℕ → Ω → ι → ℝ} {v : ℕ → Ω → ℝ} {t0 : ℕ}
    (h119 : ∀ t, t0 ≤ t → ∀ ω, B2 ⬝ᵥ M t ω + v t ω = 0)
    (h120 : ∀ t, t0 ≤ t → ∀ ω, M t ω = Λ *ᵥ M (t - 1) ω + q t ω) :
    ∀ t, t0 + D ≤ t → ∀ ω, crit α B D B2 v q t ω = 0 := by
  intro t ht ω
  unfold crit
  rw [← alphaM_eq_Bq h hB hα h120 ht ω, dotProduct_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have := h119 (t - j) (by omega) ω
  rw [dotProduct_smul, smul_eq_mul]
  linear_combination α.coeff j * this

/-- Woodford (2003), eq. (1.23), p. 554, with the adjugate: for `α = det(I − ΛL)`,
`B = adj(I − ΛL)` the criterion holds for all `t ≥ t₀ + k`, `k = rank Λ`, as stated in the book
(the degree bounds are `Adjugate.natDegree_alpha_le_rank`, `natDegree_Bpoly_le_rank`). -/
theorem eq123_adjugate (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ) {M q : ℕ → Ω → ι → ℝ}
    {v : ℕ → Ω → ℝ} {t0 : ℕ} (h119 : ∀ t, t0 ≤ t → ∀ ω, B2 ⬝ᵥ M t ω + v t ω = 0)
    (h120 : ∀ t, t0 ≤ t → ∀ ω, M t ω = Λ *ᵥ M (t - 1) ω + q t ω) :
    ∀ t, t0 + Λ.rank ≤ t → ∀ ω, crit (alpha Λ) (Bpoly Λ) Λ.rank B2 v q t ω = 0 :=
  eq123_of_eq119_eq120 (eq122 Λ) (natDegree_Bpoly_le_rank Λ) (natDegree_alpha_le_rank Λ) B2
    h119 h120

/-- Woodford (2003), p. 554: conversely, if (1.20) holds for `t₀ ≤ t < t₀ + D` and
`α(L) M_t = B(L) q_t` holds for all `t ≥ t₀ + D`, then (1.20) holds for all `t ≥ t₀`
(`α(0) = 1`). -/
theorem eq120_of_criterion {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) (hα0 : α.coeff 0 = 1) {D : ℕ}
    (hB : ∀ i c, (B i c).natDegree ≤ D) (hα : α.natDegree ≤ D) {M q : ℕ → Ω → ι → ℝ}
    {t0 : ℕ} (hinit : ∀ t, t0 ≤ t → t < t0 + D → ∀ ω, M t ω = Λ *ᵥ M (t - 1) ω + q t ω)
    (hcrit : ∀ t, t0 + D ≤ t → ∀ ω, ∑ j ∈ Finset.range (D + 1), α.coeff j • M (t - j) ω =
      ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ q (t - j) ω) :
    ∀ t, t0 ≤ t → ∀ ω, M t ω = Λ *ᵥ M (t - 1) ω + q t ω := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht ω
    by_cases hlt : t < t0 + D
    · exact hinit t ht hlt ω
    · push Not at hlt
      set e : ℕ → ι → ℝ := fun s => M s ω - Λ *ᵥ M (s - 1) ω - q s ω with he
      have hlag := lag_identity h hB hα (fun j => M (t - j) ω)
      have hc := hcrit t hlt ω
      have hsum : ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ e (t - j) = 0 := by
        have : ∀ j ∈ Finset.range (D + 1), Bc B j *ᵥ e (t - j) =
            Bc B j *ᵥ (M (t - j) ω - Λ *ᵥ M (t - (j + 1)) ω) - Bc B j *ᵥ q (t - j) ω := by
          intro j _
          rw [he]
          simp only
          rw [show t - j - 1 = t - (j + 1) by omega, mulVec_sub]
        rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hlag, hc, sub_self]
      rw [Finset.sum_range_succ', Nat.sub_zero, eq122_coeff_zero h, hα0, one_smul,
        one_mulVec] at hsum
      have hrest : ∑ j ∈ Finset.range D, Bc B (j + 1) *ᵥ e (t - (j + 1)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjD := Finset.mem_range.mp hj
        have := ih (t - (j + 1)) (by omega) (by omega) ω
        have he0 : e (t - (j + 1)) = 0 := by
          rw [he]
          simp only
          rw [this]
          abel
        rw [he0, mulVec_zero]
      rw [hrest, zero_add] at hsum
      have : M t ω - Λ *ᵥ M (t - 1) ω - q t ω = 0 := hsum
      rw [sub_sub, sub_eq_zero] at this
      exact this

/-- Woodford (2003), p. 555 (the essential idea of Prop 8.2): if (1.20) holds from `t₁` on,
(1.19) holds on the history window `t₁ ≤ t < t₀` (`t₁ + D ≤ t₀`), and the target criterion
(1.23) holds for all `t ≥ t₀`, then (1.19) holds for all `t ≥ t₁` (`α(0) = 1`). -/
theorem eq119_of_criterion {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) (hα0 : α.coeff 0 = 1) {D : ℕ}
    (hB : ∀ i c, (B i c).natDegree ≤ D) (hα : α.natDegree ≤ D) (B2 : ι → ℝ)
    {M q : ℕ → Ω → ι → ℝ} {v : ℕ → Ω → ℝ} {t1 t0 : ℕ} (hwin : t1 + D ≤ t0)
    (h120 : ∀ t, t1 ≤ t → ∀ ω, M t ω = Λ *ᵥ M (t - 1) ω + q t ω)
    (h119 : ∀ t, t1 ≤ t → t < t0 → ∀ ω, B2 ⬝ᵥ M t ω + v t ω = 0)
    (hcrit : ∀ t, t0 ≤ t → ∀ ω, crit α B D B2 v q t ω = 0) :
    ∀ t, t1 ≤ t → ∀ ω, B2 ⬝ᵥ M t ω + v t ω = 0 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht ω
    by_cases hlt : t < t0
    · exact h119 t ht hlt ω
    · push Not at hlt
      have hc := hcrit t hlt ω
      unfold crit at hc
      rw [← alphaM_eq_Bq h hB hα h120 (by omega) ω, dotProduct_sum, ← Finset.sum_add_distrib,
        Finset.sum_range_succ'] at hc
      have hrest : ∑ j ∈ Finset.range D, (α.coeff (j + 1) * v (t - (j + 1)) ω +
          B2 ⬝ᵥ α.coeff (j + 1) • M (t - (j + 1)) ω) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hjD := Finset.mem_range.mp hj
        have := ih (t - (j + 1)) (by omega) (by omega) ω
        rw [dotProduct_smul, smul_eq_mul]
        linear_combination α.coeff (j + 1) * this
      rw [hrest, zero_add, Nat.sub_zero, hα0, one_mul, one_smul] at hc
      linarith

/-- Woodford (2003), p. 555 and fn 16: the coefficient of the current instrument in (1.23). If
`v_t = a + κ_v i_t` and `q_t = Q(0) (b + i_t x_i) + r_t` (with `r_t` the forward-looking part of
`E_t Q(L⁻¹) …`), then (1.23) is `(κ_v + B₂' Q(0) x_i) i_t + (terms without the current
instrument)`, using `α(0) = 1` and `B(0) = I`. -/
theorem instrument_coefficient {Λ : Matrix ι ι ℝ} {B : Matrix ι ι ℝ[X]} {α : ℝ[X]}
    (h : B * lagMat Λ = α • (1 : Matrix ι ι ℝ[X])) (hα0 : α.coeff 0 = 1) {D : ℕ} (B2 : ι → ℝ)
    {κ : Type*} [Fintype κ] (Q0 : Matrix ι κ ℝ) {v : ℕ → Ω → ℝ} {q : ℕ → Ω → ι → ℝ} {t : ℕ}
    {ω : Ω} {a κv i : ℝ} {b xi : κ → ℝ} {r : ι → ℝ} (hv : v t ω = a + κv * i)
    (hq : q t ω = Q0 *ᵥ (b + i • xi) + r) :
    crit α B D B2 v q t ω = (κv + B2 ⬝ᵥ (Q0 *ᵥ xi)) * i +
      (a + ∑ j ∈ Finset.range D, α.coeff (j + 1) * v (t - (j + 1)) ω +
        B2 ⬝ᵥ (Q0 *ᵥ b + r + ∑ j ∈ Finset.range D, Bc B (j + 1) *ᵥ q (t - (j + 1)) ω)) := by
  unfold crit
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  try simp only [Nat.sub_zero]
  rw [hα0, eq122_coeff_zero h, hα0, one_smul, one_mulVec, hv, hq, mulVec_add, mulVec_smul]
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

end Crit

open Crit

/-! ### Assumption 8.6 and the implicit instrument rule (1.28) -/

namespace A86

variable {ιZ ιz κ : Type*} [Fintype ιz] [Fintype κ] [DecidableEq ιz]

/-- Woodford (2003), Assumption 8.6, p. 556: the target variables are `τ = (τ̂, i)` with `τ̂`
not depending on the instrument, and the loss is block-diagonal,
`L = ½ (τ̂ − τ̂*)' Ŵ (τ̂ − τ̂*) + (λ_i/2) (i − i*)²`. -/
structure Assumption86 (P : LQProblem ιZ ιz (κ ⊕ Unit)) where
  lam : ℝ
  Ti_eq : P.Ti = Sum.elim (0 : κ → ℝ) (fun _ => (1 : ℝ))
  Ttil_inr : ∀ c, P.Ttil (Sum.inr ()) c = 0
  W_inl_inr : ∀ a, P.W (Sum.inl a) (Sum.inr ()) = 0
  W_inr_inl : ∀ a, P.W (Sum.inr ()) (Sum.inl a) = 0
  W_inr_inr : P.W (Sum.inr ()) (Sum.inr ()) = lam

namespace Assumption86

variable {P : LQProblem ιZ ιz (κ ⊕ Unit)} (A : Assumption86 P)

include A in
/-- Woodford (2003), p. 556: under Assumption 8.6, `T̃' W T_i = 0`. -/
theorem Ttil_W_Ti : P.Ttilᵀ *ᵥ (P.W *ᵥ P.Ti) = 0 := by
  funext c
  simp [mulVec, dotProduct, Fintype.sum_sum_type, A.Ti_eq, A.W_inl_inr, A.Ttil_inr]

/-- Woodford (2003), p. 556: under Assumption 8.6, `T_i' W T_i = λ_i`. -/
theorem Ti_W_Ti : P.Ti ⬝ᵥ (P.W *ᵥ P.Ti) = A.lam := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, A.Ti_eq, A.W_inr_inr]

/-- Woodford (2003), p. 556: under Assumption 8.6, `v_t = T_i' W (τ_t − τ*) = λ_i (i_t − i*)`. -/
theorem Ti_W_gap (w : κ ⊕ Unit → ℝ) : P.Ti ⬝ᵥ (P.W *ᵥ w) = A.lam * w (Sum.inr ()) := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, A.Ti_eq, A.W_inr_inl, A.W_inr_inr]

omit [Fintype κ] in
/-- Woodford (2003), p. 538 vs Assumption 8.6, p. 556: with `W ≻ 0` (p. 538) the weight `λ_i` is
automatically positive, so the case `λ_i = 0` of (1.29) needs `W ⪰ 0` only. -/
theorem lam_pos : 0 < A.lam := by
  rw [← A.W_inr_inr]
  exact P.W_posDef.diag_pos

end Assumption86

/-- Woodford (2003), p. 556: under Assumption 8.6 the coefficient of the current instrument in
(1.23), `T_i'WT_i + B₂'Q(0)T̃'WT_i`, is `λ_i`. -/
theorem instrument_coefficient_A86 [Fintype ιZ] {P : LQProblem ιZ ιz (κ ⊕ Unit)}
    (A : Assumption86 P) (Q0 : Matrix ιz (ιZ ⊕ ιz) ℝ) :
    P.Ti ⬝ᵥ (P.W *ᵥ P.Ti) + P.sys.B2 ⬝ᵥ (Q0 *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ P.Ti))) = A.lam := by
  rw [A.Ti_W_Ti, A.Ttil_W_Ti, mulVec_zero, dotProduct_zero, add_zero]

end A86

open A86

namespace Rule128

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), eq. (1.28), p. 556: writing `α(L) = 1 − γ(L) L`, `γ_k = −α_{k+1}`. -/
noncomputable def γc (α : ℝ[X]) (k : ℕ) : ℝ := -α.coeff (k + 1)

/-- Woodford (2003), eq. (1.28), p. 556: with `v_t = λ_i (i_t − i*)`, `λ_i ≠ 0` and `α(0) = 1`,
the target criterion (1.23) is equivalent to the implicit instrument rule
`i_t = (1 − γ(1)) i* + γ(L) i_{t-1} − λ_i⁻¹ B₂' B(L) q_t`. -/
theorem eq128_iff {B : Matrix ι ι ℝ[X]} {α : ℝ[X]} (hα0 : α.coeff 0 = 1) {D : ℕ} (B2 : ι → ℝ)
    {lam istar : ℝ} (hlam : lam ≠ 0) {i v : ℕ → Ω → ℝ}
    (hv : ∀ s ω, v s ω = lam * (i s ω - istar)) (q : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Ω) :
    crit α B D B2 v q t ω = 0 ↔
      i t ω = (1 - ∑ k ∈ Finset.range D, γc α k) * istar +
        ∑ k ∈ Finset.range D, γc α k * i (t - 1 - k) ω -
        lam⁻¹ * (B2 ⬝ᵥ ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ q (t - j) ω) := by
  unfold crit
  rw [Finset.sum_range_succ', Nat.sub_zero, hα0, one_mul, hv t ω]
  have hs : ∑ k ∈ Finset.range D, α.coeff (k + 1) * v (t - (k + 1)) ω =
      lam * (∑ k ∈ Finset.range D, γc α k) * istar -
        lam * ∑ k ∈ Finset.range D, γc α k * i (t - 1 - k) ω := by
    rw [mul_assoc, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hv, show t - (k + 1) = t - 1 - k by omega, γc]
    ring
  rw [hs]
  set S := B2 ⬝ᵥ ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ q (t - j) ω
  constructor
  · intro h0
    field_simp
    linarith
  · intro h1
    rw [h1]
    field_simp
    ring

/-- Woodford (2003), eq. (1.29), p. 557: when the instrument carries no loss weight
(`v ≡ 0`), the criterion (1.23) is the pure targeting rule `B₂' B(L) q_t = 0`. -/
theorem eq129 {B : Matrix ι ι ℝ[X]} (α : ℝ[X]) {D : ℕ} (B2 : ι → ℝ) {v : ℕ → Ω → ℝ}
    (hv : ∀ s ω, v s ω = 0) (q : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Ω) :
    crit α B D B2 v q t ω = B2 ⬝ᵥ ∑ j ∈ Finset.range (D + 1), Bc B j *ᵥ q (t - j) ω := by
  unfold crit
  simp [hv]

end Rule128

open Rule128

/-! ### Assumption 8.5: recovering the initial multipliers -/

namespace Krylov

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), Assumption 8.5 (second part), p. 719: the vectors `B₂'Λʲ`, `j = 1, …, k`,
are linearly independent, where `k = rank Λ`. -/
def Assumption85b (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ) : Prop :=
  LinearIndependent ℝ (fun j : Fin Λ.rank => B2 ᵥ* Λ ^ (j.val + 1))

/-- Woodford (2003), App. G.2, p. 719: under Assumption 8.5, the `k` vectors `B₂'Λʲ` span the row
space of `Λ` (`k = rank Λ`), so `B₂'Λʲ w = 0` for `j = 1, …, k` forces `Λ w = 0`. -/
theorem mulVec_eq_zero_of_krylov {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} (h85 : Assumption85b Λ B2)
    {w : ι → ℝ} (hw : ∀ j : Fin Λ.rank, (B2 ᵥ* Λ ^ (j.val + 1)) ⬝ᵥ w = 0) : Λ *ᵥ w = 0 := by
  set R := LinearMap.range Λᵀ.mulVecLin with hR
  set S := Submodule.span ℝ (Set.range (fun j : Fin Λ.rank => B2 ᵥ* Λ ^ (j.val + 1))) with hS
  have hSR : S ≤ R := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨B2 ᵥ* Λ ^ j.val, ?_⟩
    rw [mulVecLin_apply, mulVec_transpose, vecMul_vecMul, ← pow_succ]
  have hrank : Module.finrank ℝ R = Λ.rank := by
    rw [hR]
    exact rank_transpose Λ
  have hSfin : Module.finrank ℝ S = Λ.rank := by
    rw [hS, finrank_span_eq_card h85, Fintype.card_fin]
  have hSeq : S = R := Submodule.eq_of_le_of_finrank_eq hSR (by rw [hSfin, hrank])
  let Lw : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => u ⬝ᵥ w
      map_add' := fun u u' => add_dotProduct u u' w
      map_smul' := fun c u => smul_dotProduct c u w }
  have hSker : S ≤ LinearMap.ker Lw := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hw j
  have hmem : Λᵀ *ᵥ (Λ *ᵥ w) ∈ S := by
    rw [hSeq]
    exact ⟨Λ *ᵥ w, rfl⟩
  have h0 : (Λᵀ *ᵥ (Λ *ᵥ w)) ⬝ᵥ w = 0 := hSker hmem
  rw [transpose_mulVec_dot] at h0
  exact dotProduct_self_eq_zero.mp h0

/-- Woodford (2003), p. 555 and App. G.2 (Assumption 8.5): the initial multipliers are uniquely
recoverable from the history. If two multiplier histories satisfy (1.20) and (1.19) with the same
`q` and `v` on a window of `K ≥ max(1, rank Λ)` periods ending at `t₀ − 1 = s₀ + K`, they agree
at `t₀ − 1`. -/
theorem initial_multiplier_unique {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} (h85 : Assumption85b Λ B2)
    {K s0 : ℕ} (hK1 : 1 ≤ K) (hKk : Λ.rank ≤ K) {M M' q : ℕ → Ω → ι → ℝ} {v : ℕ → Ω → ℝ}
    (h120 : ∀ j, 1 ≤ j → j ≤ K → ∀ ω, M (s0 + j) ω = Λ *ᵥ M (s0 + j - 1) ω + q (s0 + j) ω)
    (h120' : ∀ j, 1 ≤ j → j ≤ K → ∀ ω, M' (s0 + j) ω = Λ *ᵥ M' (s0 + j - 1) ω + q (s0 + j) ω)
    (h119 : ∀ j, 1 ≤ j → j ≤ K → ∀ ω, B2 ⬝ᵥ M (s0 + j) ω + v (s0 + j) ω = 0)
    (h119' : ∀ j, 1 ≤ j → j ≤ K → ∀ ω, B2 ⬝ᵥ M' (s0 + j) ω + v (s0 + j) ω = 0) (ω : Ω) :
    M (s0 + K) ω = M' (s0 + K) ω := by
  set d : ℕ → ι → ℝ := fun j => M (s0 + j) ω - M' (s0 + j) ω with hd
  have hrec : ∀ j, 1 ≤ j → j ≤ K → d j = Λ *ᵥ d (j - 1) := by
    intro j hj1 hjK
    simp only [hd]
    rw [h120 j hj1 hjK ω, h120' j hj1 hjK ω, mulVec_sub, show s0 + (j - 1) = s0 + j - 1 by omega]
    abel
  have hpow : ∀ j, j ≤ K → d j = (Λ ^ j) *ᵥ d 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [hrec (j + 1) (by omega) hj, Nat.add_sub_cancel, ih (by omega), mulVec_mulVec,
        pow_succ']
  have hB : ∀ j, 1 ≤ j → j ≤ K → B2 ⬝ᵥ d j = 0 := by
    intro j hj1 hjK
    simp only [hd, dotProduct_sub]
    linarith [h119 j hj1 hjK ω, h119' j hj1 hjK ω]
  have hkill : Λ *ᵥ d 0 = 0 := by
    refine mulVec_eq_zero_of_krylov h85 fun j => ?_
    rw [← dotProduct_mulVec, ← hpow (j.val + 1) (by omega)]
    exact hB _ (by omega) (by omega)
  have hK : d K = 0 := by
    rw [hpow K le_rfl]
    obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le hK1
    rw [add_comm, pow_succ, ← mulVec_mulVec, hkill, mulVec_zero]
  have := congrFun hK
  funext i
  have hi := this i
  simp only [hd, Pi.sub_apply, Pi.zero_apply] at hi
  linarith

end Krylov

open Krylov

/-! ### Proposition 8.1's conclusion as a hypothesis, and Proposition 8.2 -/

namespace Recursion

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), eq. (1.20), p. 553: the multiplier recursion `m_k = Λ m_{k-1} + u_k` started
from `m_{-1} = m₀`. -/
def mrec (Λ : Matrix ι ι ℝ) (m0 : Ω → ι → ℝ) (u : ℕ → Ω → ι → ℝ) : ℕ → Ω → ι → ℝ
  | 0 => fun ω => Λ *ᵥ m0 ω + u 0 ω
  | k + 1 => fun ω => Λ *ᵥ mrec Λ m0 u k ω + u (k + 1) ω

/-- Woodford (2003), p. 553: the multiplier recursion (1.20) is stable: bounded forcing and a
bounded start give a bounded multiplier path. (Under Proposition 8.1 the eigenvalues of `Λ`
satisfy only `|μ| < β⁻¹`, so this is an additional hypothesis; it holds when they lie inside the
unit circle.) -/
def MultStable (Ω' : Type*) (Λ : Matrix ι ι ℝ) : Prop :=
  ∀ (m0 : Ω' → ι → ℝ) (u : ℕ → Ω' → ι → ℝ), (∃ K, ∀ ω i, |m0 ω i| ≤ K) → BoundedV u →
    BoundedV (mrec Λ m0 u)

/-- Woodford (2003), p. 555: the multiplier path: the history `M_s = Mh_s` before `t₀`, then
(1.20) `M_t = Λ M_{t-1} + q_t` from `t₀` on. -/
def Mseq (Λ : Matrix ι ι ℝ) (Mh : ℕ → Ω → ι → ℝ) (t0 : ℕ) (q : ℕ → Ω → ι → ℝ) (s : ℕ) :
    Ω → ι → ℝ :=
  if s < t0 then Mh s else mrec Λ (Mh (t0 - 1)) (fun k => q (t0 + k)) (s - t0)

/-- Woodford (2003), eq. (1.20): `Mseq` satisfies (1.20) from `t₀ ≥ 1` on. -/
theorem Mseq_rec {Λ : Matrix ι ι ℝ} {Mh q : ℕ → Ω → ι → ℝ} {t0 : ℕ} (ht0 : 1 ≤ t0) :
    ∀ s, t0 ≤ s → ∀ ω, Mseq Λ Mh t0 q s ω = Λ *ᵥ Mseq Λ Mh t0 q (s - 1) ω + q s ω := by
  intro s hs ω
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  cases k with
  | zero =>
    simp only [Mseq, add_zero, lt_irrefl, ↓reduceIte, Nat.sub_self, mrec,
      show t0 - 1 < t0 by omega]
  | succ k =>
    simp only [Mseq, show ¬ t0 + (k + 1) < t0 by omega, ↓reduceIte,
      show t0 + (k + 1) - t0 = k + 1 by omega, mrec, show t0 + (k + 1) - 1 = t0 + k by omega,
      show ¬ t0 + k < t0 by omega, show t0 + k - t0 = k by omega]

/-- Woodford (2003), p. 554 ((1.24): the predetermined state includes `q_{t-1}, …`): the process
`q̂` equal to given history values `qh` before `t₀` and to `q` from `t₀` on. -/
def splice {β' : Type*} (t0 : ℕ) (h x : ℕ → Ω → β') : ℕ → Ω → β' :=
  fun s => if s < t0 then h s else x s

end Recursion

open Recursion

namespace Prop81

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), p. 553: `T̃' W (τ_t − τ*)`, the forcing of (1.18). -/
def xproc (P : LQProblem ιZ ιz ιτ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun t ω => P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar))

/-- Woodford (2003), eq. (1.26), p. 554: `v_t = T_i' W (τ_t − τ*)`. -/
def vproc (P : LQProblem ιZ ιz ιτ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => P.Ti ⬝ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar))

/-- Woodford (2003), p. 540: the multipliers `ξ_t` on the predetermined rows in
`φ_t = (ξ_t, M_{t-1})`. -/
def ξpart (v : ιZ ⊕ ιz → ℝ) : ιZ → ℝ := fun r => v (Sum.inl r)

/-- Woodford (2003), eq. (1.18), p. 552, for all `t ≥ t₀`. -/
def Eq118 (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ ω, P.sys.Ahatᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
    P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) - P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ φ t ω) = 0

/-- Woodford (2003), eq. (1.20), p. 553, for all `t ≥ t₀`, in terms of `φ_t = (ξ_t, M_{t-1})`:
`M_t = Λ M_{t-1} + q_t`. -/
def Eq120 (t0 : ℕ) (Λ : Matrix ιz ιz ℝ) (q : ℕ → Ω → ιz → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) :
    Prop :=
  ∀ t, t0 ≤ t → ∀ ω, Mpart (φ (t + 1) ω) = Λ *ᵥ Mpart (φ t ω) + q t ω

/-- Woodford (2003), eq. (1.21), p. 553, for all `t ≥ t₀`: `ξ_t = Υ M_{t-1} + r_t`. -/
def Eq121 (t0 : ℕ) (Υ : Matrix ιZ ιz ℝ) (r : ℕ → Ω → ιZ → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) :
    Prop :=
  ∀ t, t0 ≤ t → ∀ ω, ξpart (φ t ω) = Υ *ᵥ Mpart (φ t ω) + r t ω

/-- Woodford (2003), Proposition 8.1, p. 553 (the equivalence): bounded `(φ, τ)` satisfy (1.18)
for all `t ≥ t₀` iff they satisfy (1.20) and (1.21), with `q = E_t Q(L⁻¹) T̃'W(τ − τ*)` and
`r = E_t R(L⁻¹) T̃'W(τ − τ*)` given by operators `Qop`, `Rop`. -/
def Prop81Equiv (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ)
    (Qop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (Rop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιZ → ℝ) : Prop :=
  ∀ y φ, BoundedV y → BoundedV φ →
    (Eq118 P 𝔼 t0 y φ ↔ Eq120 t0 Λ (Qop (xproc P y)) φ ∧ Eq121 t0 Υ (Rop (xproc P y)) φ)

variable (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)

/-- Woodford (2003), Proposition 8.1, p. 553, **as a hypothesis** (its proof, in Giannoni and
Woodford 2002a, is deferred): matrices `Λ`, `Υ` and operators `Q(L⁻¹)`, `R(L⁻¹)` mapping
bounded processes to bounded (adapted) processes, such that bounded `(φ, τ)` satisfy (1.18) iff
they satisfy (1.20)–(1.21). -/
structure Prop81Conclusion where
  Λ : Matrix ιz ιz ℝ
  Υ : Matrix ιZ ιz ℝ
  Qop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ
  Rop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιZ → ℝ
  equiv : Prop81Equiv P 𝔼 t0 Λ Υ Qop Rop
  Qbounded : ∀ x, BoundedV x → BoundedV (Qop x)
  Rbounded : ∀ x, BoundedV x → BoundedV (Rop x)
  Qadapted : ∀ x, AdaptedV 𝔼 (Qop x)

variable {P 𝔼 t0}

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 553: `T̃'W(τ − τ*)` is bounded for bounded plans. -/
theorem boundedV_xproc {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : BoundedV y) :
    BoundedV (xproc P y) := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.T M
  obtain ⟨K2, hK2⟩ := exists_bound_mulVec P.W (K1 + ∑ b, |P.τstar b|)
  obtain ⟨K3, hK3⟩ := exists_bound_mulVec P.Ttilᵀ K2
  refine ⟨K3, fun t ω i => hK3 _ (fun a => hK2 _ (fun b => ?_) a) i⟩
  have h2 : |P.τstar b| ≤ ∑ b, |P.τstar b| :=
    Finset.single_le_sum (f := fun b => |P.τstar b|) (fun b _ => abs_nonneg _)
      (Finset.mem_univ b)
  simp only [Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add (hK1 _ (hM t ω) b) h2)

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540: `E_t (A a + b) = A a + b` when `a`, `b` are known at `t`. -/
theorem KnownV.mulVec_add {𝔼' : ExpectationSystem Ω} {κ : Type*} {s : ℕ}
    (A : Matrix κ ιz ℝ) {a : Ω → ιz → ℝ} {b : Ω → κ → ℝ} (ha : KnownV 𝔼' s a)
    (hb : KnownV 𝔼' s b) : KnownV 𝔼' s (fun ω => A *ᵥ a ω + b ω) := by
  intro i
  have h := EV_mulVec 𝔼' s A a
  rw [EV_of_known 𝔼' ha] at h
  have hA : 𝔼'.E s (fun ω => (A *ᵥ a ω) i) = fun ω => (A *ᵥ a ω) i :=
    funext fun ω => congrFun (congrFun h ω) i
  have : (fun ω => (A *ᵥ a ω + b ω) i) = (fun ω => (A *ᵥ a ω) i) + fun ω => b ω i := rfl
  rw [this, map_add, hA, hb i]

end Prop81

open Prop81

namespace Prop82

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}

/-- Woodford (2003), p. 555: the history before `t₀` is consistent with an optimal commitment
chosen in the past: on the window `t₀ − D ≤ s < t₀` the multipliers `Mh` satisfy (1.20) and
(1.19) with the historical `q`, `v` (which, with `Z_{t₀}`, make up the predetermined state
`Z̄_{t₀}` of (1.24)). -/
def HistoryOK (Λ : Matrix ιz ιz ℝ) (B2 : ιz → ℝ) (t0 D : ℕ) (Mh qh : ℕ → Ω → ιz → ℝ)
    (vh : ℕ → Ω → ℝ) : Prop :=
  (∀ s, t0 - D ≤ s → s < t0 → ∀ ω, Mh s ω = Λ *ᵥ Mh (s - 1) ω + qh s ω) ∧
    ∀ s, t0 - D ≤ s → s < t0 → ∀ ω, B2 ⬝ᵥ Mh s ω + vh s ω = 0

/-- Woodford (2003), eq. (1.23), p. 554: commitment to the target criterion at all `t ≥ t₀`,
with `α = det(I − ΛL)`, `B = adj(I − ΛL)`, the historical `q`, `v` before `t₀` and the plan's
own `q_t = E_t Q(L⁻¹) T̃'W(τ_t − τ*)`, `v_t = T_i'W(τ_t − τ*)` from `t₀` on. -/
def Criterion (H : Prop81Conclusion P 𝔼 t0) (D : ℕ) (qh : ℕ → Ω → ιz → ℝ) (vh : ℕ → Ω → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ ω, crit (alpha H.Λ) (Bpoly H.Λ) D P.sys.B2 (splice t0 vh (vproc P y))
    (splice t0 qh (H.Qop (xproc P y))) t ω = 0

/-- Woodford (2003), p. 555: the multipliers implied by a plan under the criterion:
`M_t` from (1.20) (history before `t₀`), `ξ_t` from (1.21), `φ_t = (ξ_t, M_{t-1})`. -/
def φcon (H : Prop81Conclusion P 𝔼 t0) (Mh : ℕ → Ω → ιz → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun s ω => Sum.elim
    (if t0 ≤ s then H.Υ *ᵥ Mseq H.Λ Mh t0 (H.Qop (xproc P y)) (s - 1) ω +
      H.Rop (xproc P y) s ω else 0)
    (Mseq H.Λ Mh t0 (H.Qop (xproc P y)) (s - 1) ω)

/-- Woodford (2003), p. 555: the multiplier path is bounded when the history is bounded and the
recursion (1.20) is stable. -/
theorem boundedV_Mseq (H : Prop81Conclusion P 𝔼 t0) {Mh : ℕ → Ω → ιz → ℝ} (hMhb : BoundedV Mh)
    (hstab : MultStable Ω H.Λ) {x : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hx : BoundedV x) :
    BoundedV (Mseq H.Λ Mh t0 (H.Qop x)) := by
  obtain ⟨K1, hK1⟩ := hMhb
  obtain ⟨Kq, hKq⟩ := H.Qbounded x hx
  obtain ⟨K2, hK2⟩ := hstab (Mh (t0 - 1)) (fun k => H.Qop x (t0 + k))
    ⟨K1, fun ω i => hK1 _ ω i⟩ ⟨Kq, fun k ω i => hKq _ ω i⟩
  refine ⟨max K1 K2, fun s ω i => ?_⟩
  unfold Mseq
  split_ifs
  · exact (hK1 s ω i).trans (le_max_left _ _)
  · exact (hK2 _ ω i).trans (le_max_right _ _)

/-- Woodford (2003), p. 540: the constructed `M_t` is known at `t`. -/
theorem known_Mseq (H : Prop81Conclusion P 𝔼 t0) (ht0 : 1 ≤ t0) {Mh : ℕ → Ω → ιz → ℝ}
    (hMhk : AdaptedV 𝔼 Mh) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) :
    ∀ s, KnownV 𝔼 s (Mseq H.Λ Mh t0 (H.Qop x) s) := by
  intro s
  by_cases hs : s < t0
  · simp only [Mseq, hs, ↓reduceIte]
    exact hMhk s
  · push Not at hs
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    simp only [Mseq, show ¬ t0 + k < t0 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    induction k with
    | zero =>
      exact KnownV.mulVec_add H.Λ (KnownV.mono 𝔼 (by omega) (hMhk (t0 - 1)))
        (H.Qadapted x (t0 + 0))
    | succ k ih =>
      exact KnownV.mulVec_add H.Λ (KnownV.mono 𝔼 (by omega) (ih (by omega)))
        (H.Qadapted x (t0 + (k + 1)))

/-- Woodford (2003), p. 555 (Proposition 8.2, the key step, conditional on Proposition 8.1):
a bounded feasible plan satisfying the target criterion (1.23) at all `t ≥ t₀`, given a
consistent history, solves (1.1) + (1.9) with the initial multipliers `M_{t₀-1} = Mh_{t₀-1}`
(the multipliers are recovered from (1.20)–(1.21); the criterion forces (1.19)). -/
theorem focSystem_of_criterion (H : Prop81Conclusion P 𝔼 t0) {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D) (hα : (alpha H.Λ).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ} (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hstab : MultStable Ω H.Λ)
    {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.Feasible 𝔼 c t0 Z0 y) (hcrit : Criterion H D qh vh y) :
    FOCSystem P 𝔼 c t0 Z0 (Mh (t0 - 1)) y (φcon H Mh y) := by
  set x := xproc P y with hx
  set Ms := Mseq H.Λ Mh t0 (H.Qop x) with hMs
  have hxb : BoundedV x := boundedV_xproc hy.2.2.1
  have hMsb : BoundedV Ms := boundedV_Mseq H hMhb hstab hxb
  have hMpart : ∀ s ω, Mpart (φcon H Mh y s ω) = Ms (s - 1) ω := fun _ _ => rfl
  have hξ : ∀ s, t0 ≤ s → ∀ ω, ξpart (φcon H Mh y s ω) = H.Υ *ᵥ Ms (s - 1) ω + H.Rop x s ω := by
    intro s hs ω
    funext r
    simp [φcon, ξpart, hs, hMs, hx]
  have hφb : BoundedV (φcon H Mh y) := by
    obtain ⟨K1, hK1⟩ := hMsb
    obtain ⟨KR, hKR⟩ := H.Rbounded x hxb
    obtain ⟨KΥ, hKΥ⟩ := exists_bound_mulVec H.Υ K1
    refine ⟨max (max (KΥ + KR) K1) 0, fun s ω i => ?_⟩
    rcases i with r | r
    · by_cases hs : t0 ≤ s
      · have := congrFun (hξ s hs ω) r
        simp only [ξpart, Pi.add_apply] at this
        rw [this]
        exact (abs_add_le _ _).trans ((add_le_add (hKΥ _ (hK1 _ ω) r) (hKR s ω r)).trans
          ((le_max_left _ _).trans (le_max_left _ _)))
      · simp only [φcon, hs, ↓reduceIte, Sum.elim_inl, Pi.zero_apply, abs_zero]
        exact le_max_right _ _
    · exact (hK1 _ ω r).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hmeas : MultiplierMeas 𝔼 (φcon H Mh y) := by
    intro t r
    have := known_Mseq H (by omega) hMhk x t r
    simpa [φcon, hMs] using this
  have h120 : Eq120 t0 H.Λ (H.Qop x) (φcon H Mh y) := by
    intro t ht ω
    rw [hMpart, hMpart, Nat.add_sub_cancel]
    exact Mseq_rec (by omega) t ht ω
  have h121 : Eq121 t0 H.Υ (H.Rop x) (φcon H Mh y) := by
    intro t ht ω
    rw [hξ t ht ω, hMpart]
  have h118 := (H.equiv y (φcon H Mh y) hy.2.2.1 hφb).mpr ⟨h120, h121⟩
  -- (1.19) from the criterion
  have h120' : ∀ s, t0 - D ≤ s → ∀ ω,
      Ms s ω = H.Λ *ᵥ Ms (s - 1) ω + splice t0 qh (H.Qop x) s ω := by
    intro s hs ω
    by_cases hlt : s < t0
    · simp only [hMs, Mseq, splice, hlt, ↓reduceIte, show s - 1 < t0 by omega]
      exact hhist.1 s hs hlt ω
    · simp only [splice, hlt, ↓reduceIte]
      exact Mseq_rec (by omega) s (by omega) ω
  have h119' : ∀ s, t0 - D ≤ s → s < t0 → ∀ ω,
      P.sys.B2 ⬝ᵥ Ms s ω + splice t0 vh (vproc P y) s ω = 0 := by
    intro s hs hlt ω
    simp only [hMs, Mseq, splice, hlt, ↓reduceIte]
    exact hhist.2 s hs hlt ω
  have h119 := eq119_of_criterion (eq122 H.Λ) (alpha_coeff_zero H.Λ) hB hα P.sys.B2
    (show t0 - D + D ≤ t0 by omega) h120' h119' hcrit
  refine ⟨hy, hφb, hmeas, fun ω => ?_, fun t ht ω => ?_⟩
  · rw [hMpart]
    simp only [hMs, Mseq, show t0 - 1 < t0 by omega, ↓reduceIte]
  · refine (foc_iff_split P hmeas y t ω).mpr ⟨h118 t ht ω, ?_⟩
    have := h119 t (by omega) ω
    simp only [splice, show ¬ t < t0 by omega, ↓reduceIte] at this
    rw [hMpart, Nat.add_sub_cancel]
    exact this

/-- Woodford (2003), Proposition 8.2 (second part), p. 555, conditional on Proposition 8.1: the
plan determined by commitment to (1.23) is optimal subject to the initial constraint (1.27)
`Ẽ z_{t₀} = ē` (Lagrangian sufficiency; any expectation system with pull-out). -/
theorem prop82_optimal (hpull : 𝔼.PullOut) (H : Prop81Conclusion P 𝔼 t0) {D : ℕ}
    (hD : D + 1 ≤ t0) (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D)
    (hα : (alpha H.Λ).natDegree ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh)
    (hstab : MultStable Ω H.Λ) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.Feasible 𝔼 c t0 Z0 y)
    (hcrit : Criterion H D qh vh y) :
    P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y :=
  optimalSubjectTo_of_focSystem P hpull
    (focSystem_of_criterion H hD hB hα hhist hMhb hMhk hstab hy hcrit)

/-- Woodford (2003), Proposition 8.2 (determinacy, uniqueness), p. 555, conditional on
Proposition 8.1: under Assumption 8.1 two bounded feasible plans that both satisfy the criterion
(1.23) at all `t ≥ t₀` (with the same history) coincide from `t₀` on. -/
theorem prop82_unique (hA : Assumption81 P 𝔼 t0) (H : Prop81Conclusion P 𝔼 t0) {D : ℕ}
    (hD : D + 1 ≤ t0) (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D)
    (hα : (alpha H.Λ).natDegree ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh)
    (hstab : MultStable Ω H.Λ) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.Feasible 𝔼 c t0 Z0 y)
    (hy' : P.Feasible 𝔼 c t0 Z0 y') (hcrit : Criterion H D qh vh y)
    (hcrit' : Criterion H D qh vh y') : ∀ t, t0 ≤ t → y t = y' t := fun t ht =>
  (hA.unique c Z0 (Mh (t0 - 1)) y y' _ _
    (focSystem_of_criterion H hD hB hα hhist hMhb hMhk hstab hy hcrit)
    (focSystem_of_criterion H hD hB hα hhist hMhb hMhk hstab hy' hcrit') t ht).1

/-- Woodford (2003), Proposition 8.2 (determinacy, existence), p. 555, conditional on
Proposition 8.1: under Assumption 8.1 the bounded solution of (1.1) + (1.9) with initial
multipliers `M_{t₀-1} = Mh_{t₀-1}` satisfies the criterion (1.23) at every `t ≥ t₀` (using the
history for the lagged terms; footnote 14). -/
theorem prop82_exists (hA : Assumption81 P 𝔼 t0) (H : Prop81Conclusion P 𝔼 t0) {D : ℕ}
    (hD : D + 1 ≤ t0) (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D)
    (hα : (alpha H.Λ).natDegree ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) (hMhk : AdaptedV 𝔼 Mh)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    (hZ0 : KnownV 𝔼 t0 Z0) :
    ∃ y, P.Feasible 𝔼 c t0 Z0 y ∧ Criterion H D qh vh y := by
  have hM0 : KnownV 𝔼 t0 (Mh (t0 - 1)) := KnownV.mono 𝔼 (by omega) (hMhk (t0 - 1))
  obtain ⟨y, φ, hfe, hbφ, hmφ, hM, hfoc⟩ := hA.solvable c Z0 (Mh (t0 - 1)) hbc hac hZ0 hM0
  refine ⟨y, hfe, ?_⟩
  have hsplit := fun t (ht : t0 ≤ t) ω => (foc_iff_split P hmφ y t ω).mp (hfoc t ht ω)
  have h120 := ((H.equiv y φ hfe.2.2.1 hbφ).mp fun t ht ω => (hsplit t ht ω).1).1
  set x := xproc P y with hx
  set Mst : ℕ → Ω → ιz → ℝ := fun s => if s < t0 then Mh s else fun ω => Mpart (φ (s + 1) ω)
    with hMst
  have h120' : ∀ s, t0 - D ≤ s → ∀ ω,
      Mst s ω = H.Λ *ᵥ Mst (s - 1) ω + splice t0 qh (H.Qop x) s ω := by
    intro s hs ω
    by_cases hlt : s < t0
    · simp only [hMst, splice, hlt, ↓reduceIte, show s - 1 < t0 by omega]
      exact hhist.1 s hs hlt ω
    · simp only [hMst, splice, hlt, ↓reduceIte]
      rw [h120 s (by omega) ω]
      congr 2
      by_cases heq : s = t0
      · subst heq
        simp only [show s - 1 < s by omega, ↓reduceIte]
        exact hM ω
      · simp only [show ¬ s - 1 < t0 by omega, ↓reduceIte, show s - 1 + 1 = s by omega]
  have h119' : ∀ s, t0 - D ≤ s → ∀ ω,
      P.sys.B2 ⬝ᵥ Mst s ω + splice t0 vh (vproc P y) s ω = 0 := by
    intro s hs ω
    by_cases hlt : s < t0
    · simp only [hMst, splice, hlt, ↓reduceIte]
      exact hhist.2 s hs hlt ω
    · simp only [hMst, splice, hlt, ↓reduceIte, vproc]
      exact (hsplit s (by omega) ω).2
  have hc := eq123_of_eq119_eq120 (eq122 H.Λ) hB hα P.sys.B2 h119' h120'
  intro t ht ω
  exact hc t (by omega) ω

/-- Woodford (2003), p. 555 and Assumption 8.5 (App. G.2): the initial multipliers implied by
the history do not depend on which consistent multiplier history is used: two histories
consistent with the same `q`, `v` on a window of `D ≥ max(1, rank Λ)` periods give the same
`M_{t₀-1}`, hence (by `prop82_unique`) the same equilibrium. -/
theorem prop82_history_independent {Λ : Matrix ιz ιz ℝ} {B2 : ιz → ℝ}
    (h85 : Assumption85b Λ B2) {D : ℕ} (hD : D + 1 ≤ t0) (hD1 : 1 ≤ D) (hDk : Λ.rank ≤ D)
    {Mh Mh' qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ} (hh : HistoryOK Λ B2 t0 D Mh qh vh)
    (hh' : HistoryOK Λ B2 t0 D Mh' qh vh) (ω : Ω) : Mh (t0 - 1) ω = Mh' (t0 - 1) ω := by
  have key := initial_multiplier_unique (s0 := t0 - D - 1) (v := vh) h85 hD1 hDk
    (M := Mh) (M' := Mh') (q := qh)
    (fun j hj1 hjK ω => hh.1 _ (by omega) (by omega) ω)
    (fun j hj1 hjK ω => hh'.1 _ (by omega) (by omega) ω)
    (fun j hj1 hjK ω => hh.2 _ (by omega) (by omega) ω)
    (fun j hj1 hjK ω => hh'.2 _ (by omega) (by omega) ω) ω
  rwa [show t0 - D - 1 + D = t0 - 1 by omega] at key

end Prop82

open Prop82

/-! ### Forward and backward lag operators; the lemma (1.30) ⟺ (1.31) -/

/-- Woodford (2003), p. 557: the forward operator with expectations, `(F x)_t = E_t x_{t+1}`, so
that `E_t φ(L⁻¹) x_t = (φ(F) x)_t` for adapted `x` (`aeval_fwdOp_apply`). -/
def fwdOp (𝔼 : ExpectationSystem Ω) : (ℕ → Ω → ℝ) →ₗ[ℝ] (ℕ → Ω → ℝ) where
  toFun x t := 𝔼.E t (x (t + 1))
  map_add' x y := by
    funext t
    change 𝔼.E t (x (t + 1) + y (t + 1)) = 𝔼.E t (x (t + 1)) + 𝔼.E t (y (t + 1))
    exact map_add _ _ _
  map_smul' c x := by
    funext t
    change 𝔼.E t (c • x (t + 1)) = c • 𝔼.E t (x (t + 1))
    exact map_smul _ _ _

/-- Woodford (2003), p. 558: the lag operator `(L x)_t = x_{t-1}` (pre-sample values zero). -/
def lagOp : (ℕ → Ω → ℝ) →ₗ[ℝ] (ℕ → Ω → ℝ) where
  toFun x t := match t with
    | 0 => 0
    | t + 1 => x t
  map_add' x y := by
    funext t
    cases t <;> simp
  map_smul' c x := by
    funext t
    cases t <;> simp

/-- Woodford (2003), p. 557: `(F^{j+1} x)_t = E_t x_{t+j+1}` (law of iterated expectations). -/
theorem fwdOp_pow_succ_apply (𝔼 : ExpectationSystem Ω) (x : ℕ → Ω → ℝ) (j t : ℕ) :
    ((fwdOp 𝔼) ^ (j + 1)) x t = 𝔼.E t (x (t + j + 1)) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    change 𝔼.E t (((fwdOp 𝔼) ^ (j + 1)) x (t + 1)) = _
    rw [ih, 𝔼.tower (Nat.le_succ t)]
    congr 2
    omega

/-- Woodford (2003), pp. 557–558: on adapted processes, `(φ(F) x)_t = ∑_j φ_j E_t x_{t+j}`, i.e.
`aeval (fwdOp 𝔼) φ` is Woodford's `E_t φ(L⁻¹)`. -/
theorem aeval_fwdOp_apply (𝔼 : ExpectationSystem Ω) {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (φ : ℝ[X]) (t : ℕ) :
    (aeval (fwdOp 𝔼) φ) x t =
      ∑ j ∈ Finset.range (φ.natDegree + 1), φ.coeff j • 𝔼.E t (x (t + j)) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply]
  congr 1
  cases j with
  | zero =>
    rw [pow_zero, Module.End.one_apply, add_zero, hx t]
  | succ j =>
    rw [fwdOp_pow_succ_apply, add_assoc]

/-- Woodford (2003), p. 557: `E_t` of a real linear combination `a f − b g`. -/
theorem E_lin2 (𝔼 : ExpectationSystem Ω) (t : ℕ) (a b : ℝ) (f g : Ω → ℝ) :
    𝔼.E t (fun ω => a * f ω - b * g ω) = fun ω => a * 𝔼.E t f ω - b * 𝔼.E t g ω := by
  have h : (fun ω => a * f ω - b * g ω) = a • f - b • g := rfl
  rw [h, map_sub, map_smul, map_smul]
  rfl

/-- Woodford (2003), p. 557: `E_t` of a real linear combination `a f + b g`. -/
theorem E_lin2' (𝔼 : ExpectationSystem Ω) (t : ℕ) (a b : ℝ) (f g : Ω → ℝ) :
    𝔼.E t (fun ω => a * f ω + b * g ω) = fun ω => a * 𝔼.E t f ω + b * 𝔼.E t g ω := by
  have h : (fun ω => a * f ω + b * g ω) = a • f + b • g := rfl
  rw [h, map_add, map_smul, map_smul]
  rfl

/-- Woodford (2003), p. 557: the complexified forward operator `(F u)_t = E_t u_{t+1}`
(`ℂ`-linear). -/
def fwdC (𝔼 : ExpectationSystem Ω) : (ℕ → Ω → ℂ) →ₗ[ℂ] (ℕ → Ω → ℂ) where
  toFun x t := EC 𝔼 t (x (t + 1))
  map_add' x y := by
    funext t
    exact EC_add 𝔼 t _ _
  map_smul' c x := by
    funext t
    exact EC_smul 𝔼 t c _

/-- Woodford (2003), pp. 557–558: the stable first-order factor. If a bounded complex process
satisfies `E_t u_{t+1} = r u_t` with `|r| > 1` (`(1 − r⁻¹L⁻¹)` applied with `E_t`), then `u = 0`
(forward iteration `u_t = r^{-k} E_t u_{t+k} → 0`). -/
theorem eq_zero_of_fwdC_eq {𝔼 : ExpectationSystem Ω} {r : ℂ} (hr : 1 < ‖r‖)
    {u : ℕ → Ω → ℂ} (hu : BoundedC u) (h : ∀ t, EC 𝔼 t (u (t + 1)) = r • u t) : u = 0 := by
  obtain ⟨M, hM⟩ := hu
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hr
    linarith
  have hut : ∀ t, u t = r⁻¹ • EC 𝔼 t (u (t + 1)) := by
    intro t
    rw [h t, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hiter : ∀ k t, u t = (r⁻¹) ^ (k + 1) • EC 𝔼 t (u (t + k + 1)) := by
    intro k
    induction k with
    | zero => intro t; simpa using hut t
    | succ k ih =>
      intro t
      rw [ih t, hut (t + k + 1), EC_smul, EC_tower 𝔼 (by omega), smul_smul, ← pow_succ,
        show t + k + 1 + 1 = t + (k + 1) + 1 by omega]
  funext t ω
  have hbound : ∀ k : ℕ, ‖u t ω‖ ≤ ‖r‖⁻¹ ^ (k + 1) * (2 * M) := by
    intro k
    rw [hiter k t]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow, norm_inv]
    exact mul_le_mul_of_nonneg_left (norm_EC_le 𝔼 (fun ω' => hM _ ω') t ω)
      (pow_nonneg (inv_nonneg.mpr (norm_nonneg r)) _)
  have hlt : ‖r‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hlim : Tendsto (fun k : ℕ => ‖r‖⁻¹ ^ (k + 1) * (2 * M)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (norm_nonneg r)) hlt).comp
      (tendsto_add_atTop_nat 1)).mul_const (2 * M)
    simpa using this
  have h0 : ‖u t ω‖ ≤ 0 := ge_of_tendsto' hlim hbound
  simpa using h0

/-- Woodford (2003), p. 557: bounded complex processes are mapped to bounded processes by every
forward lag polynomial `φ(F)`. -/
theorem boundedC_aeval (𝔼 : ExpectationSystem Ω) (p : ℂ[X]) :
    ∀ u, BoundedC u → BoundedC ((aeval (fwdC 𝔼) p) u) := by
  induction p using Polynomial.induction_on with
  | C a =>
    intro u ⟨M, hM⟩
    refine ⟨‖a‖ * M, fun t ω => ?_⟩
    simp only [aeval_C, Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (norm_nonneg a)
  | add p q hp hq =>
    intro u hu
    obtain ⟨M1, h1⟩ := hp u hu
    obtain ⟨M2, h2⟩ := hq u hu
    refine ⟨M1 + M2, fun t ω => ?_⟩
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (h1 t ω) (h2 t ω))
  | monomial n a ih =>
    intro u hu
    have hFu : BoundedC (fwdC 𝔼 u) := by
      obtain ⟨M, hM⟩ := hu
      exact ⟨2 * M, fun t ω => norm_EC_le 𝔼 (fun ω' => hM _ ω') t ω⟩
    have := ih (fwdC 𝔼 u) hFu
    rwa [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]

/-- Woodford (2003), p. 557: **the key lemma behind (1.30) ⟺ (1.31), complex form.** If every
root of the nonzero polynomial `φ` lies outside the unit circle, then `φ(F) u = 0` for a bounded
complex process `u` forces `u = 0`. -/
theorem eq_zero_of_aeval_fwdC_eq_zero {𝔼 : ExpectationSystem Ω} :
    ∀ (n : ℕ) (p : ℂ[X]), p.natDegree = n → p ≠ 0 → (∀ z ∈ p.roots, 1 < ‖z‖) →
      ∀ u, BoundedC u → (aeval (fwdC 𝔼) p) u = 0 → u = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hn hp _ u _ hzero
    rw [eq_C_of_natDegree_eq_zero hn, aeval_C, Module.algebraMap_end_apply] at hzero
    have hc : p.coeff 0 ≠ 0 := by
      intro h0
      apply hp
      rw [eq_C_of_natDegree_eq_zero hn, h0, map_zero]
    exact (smul_eq_zero.mp hzero).resolve_left hc
  | succ n ih =>
    intro p hn hp hroots u hu hzero
    obtain ⟨z, hz⟩ := Complex.exists_root (f := p) (by
      rw [degree_eq_natDegree hp, hn]
      exact_mod_cast Nat.succ_pos n)
    set q := p /ₘ (X - C z) with hq
    have hfac : (X - C z) * q = p := mul_divByMonic_eq_iff_isRoot.mpr hz
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfac
      exact hp hfac.symm
    have hqdeg : q.natDegree = n := by
      have := congrArg natDegree hfac
      rw [natDegree_mul (X_sub_C_ne_zero z) hq0, natDegree_X_sub_C, hn] at this
      omega
    have hqroots : ∀ w ∈ q.roots, 1 < ‖w‖ := by
      intro w hw
      apply hroots
      rw [← hfac, roots_mul (by rw [hfac]; exact hp), roots_X_sub_C]
      exact Multiset.mem_add.mpr (Or.inr hw)
    have hzroot : 1 < ‖z‖ := hroots z ((mem_roots hp).mpr hz)
    set w := (aeval (fwdC 𝔼) q) u with hw
    have hwb : BoundedC w := boundedC_aeval 𝔼 q u hu
    have hw0 : w = 0 := by
      refine eq_zero_of_fwdC_eq (𝔼 := 𝔼) hzroot hwb fun t => ?_
      rw [← hfac, map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C,
        LinearMap.sub_apply, Module.algebraMap_end_apply] at hzero
      have h2 := congrFun hzero t
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at h2
      rw [← hw] at h2
      exact sub_eq_zero.mp h2
    exact ih q hqdeg hq0 hqroots u hu hw0

/-- Woodford (2003), p. 557: complexification commutes with the forward operator. -/
theorem fwdC_ofReal (𝔼 : ExpectationSystem Ω) (x : ℕ → Ω → ℝ) :
    fwdC 𝔼 (fun t ω => (x t ω : ℂ)) = fun t ω => ((fwdOp 𝔼 x) t ω : ℂ) := by
  funext t ω
  apply Complex.ext
  · simp [fwdC, EC, fwdOp]
  · simp only [fwdC, EC, LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_im]
    have : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
    rw [this, map_zero]
    rfl

/-- Woodford (2003), p. 557: complexification commutes with real forward lag polynomials. -/
theorem aeval_fwdC_ofReal (𝔼 : ExpectationSystem Ω) (φ : ℝ[X]) (x : ℕ → Ω → ℝ) :
    (aeval (fwdC 𝔼) (φ.map Complex.ofRealHom)) (fun t ω => (x t ω : ℂ)) =
      fun t ω => ((aeval (fwdOp 𝔼) φ) x t ω : ℂ) := by
  have hpow : ∀ j (x : ℕ → Ω → ℝ), ((fwdC 𝔼) ^ j) (fun t ω => (x t ω : ℂ)) =
      fun t ω => (((fwdOp 𝔼) ^ j) x t ω : ℂ) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, fwdC_ofReal, ih, pow_succ, Module.End.mul_apply]
  rw [aeval_eq_sum_range, aeval_eq_sum_range,
    natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  funext t ω
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, hpow,
    Pi.smul_apply, coeff_map, smul_eq_mul, Complex.ofRealHom_eq_coe, Complex.ofReal_sum,
    Complex.ofReal_mul]

/-- Woodford (2003), p. 557: **the lemma behind (1.30) ⟺ (1.31), proved in full.** Let `φ` be a
nonzero real polynomial all of whose (complex) roots lie outside the unit circle ("invertible").
If a bounded process `y` satisfies `E_t φ(L⁻¹) y_t = 0` for all `t` (i.e. `φ(F) y = 0`), then
`y = 0`. -/
theorem eq_zero_of_aeval_fwdOp_eq_zero {𝔼 : ExpectationSystem Ω} {φ : ℝ[X]} (hφ : φ ≠ 0)
    (hroots : ∀ z ∈ (φ.map Complex.ofRealHom).roots, 1 < ‖z‖) {y : ℕ → Ω → ℝ}
    (hy : BoundedProc y) (h : (aeval (fwdOp 𝔼) φ) y = 0) : y = 0 := by
  obtain ⟨M, hM⟩ := hy
  have hφc : φ.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hφ
  have hb : BoundedC (fun t ω => (y t ω : ℂ)) :=
    ⟨M, fun t ω => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM t ω⟩
  have hc : (aeval (fwdC 𝔼) (φ.map Complex.ofRealHom)) (fun t ω => (y t ω : ℂ)) = 0 := by
    rw [aeval_fwdC_ofReal, h]
    rfl
  have h0 := eq_zero_of_aeval_fwdC_eq_zero _ _ rfl hφc hroots _ hb hc
  funext t ω
  have := congrFun (congrFun h0 t) ω
  simpa using this

/-- Woodford (2003), p. 557, the lemma as stated in the task: a bounded adapted `y` with
`E_t ∑_j φ_j y_{t+j} = 0` for all `t`, `φ` invertible, is zero. -/
theorem eq_zero_of_forward_sum_eq_zero {𝔼 : ExpectationSystem Ω} {φ : ℝ[X]} (hφ : φ ≠ 0)
    (hroots : ∀ z ∈ (φ.map Complex.ofRealHom).roots, 1 < ‖z‖) {y : ℕ → Ω → ℝ}
    (hy : BoundedProc y) (hya : 𝔼.Adapted y)
    (h : ∀ t, ∑ j ∈ Finset.range (φ.natDegree + 1), φ.coeff j • 𝔼.E t (y (t + j)) = 0) :
    y = 0 := by
  refine eq_zero_of_aeval_fwdOp_eq_zero (𝔼 := 𝔼) hφ hroots hy ?_
  funext t
  rw [aeval_fwdOp_apply 𝔼 hya, h t]
  rfl

/-- Woodford (2003), eqs. (1.30)–(1.31), pp. 557–558: for a bounded criterion process
`w_t = a(L) E_t Φ(L⁻¹)(τ_t − τ*)` and an invertible `φ`, the rules (1.30) `w_t = 0 ∀t` and
(1.31) `E_t φ(L⁻¹) w_t = 0 ∀t` are equivalent. -/
theorem eq130_iff_eq131 {𝔼 : ExpectationSystem Ω} {φ : ℝ[X]} (hφ : φ ≠ 0)
    (hroots : ∀ z ∈ (φ.map Complex.ofRealHom).roots, 1 < ‖z‖) {w : ℕ → Ω → ℝ}
    (hw : BoundedProc w) : w = 0 ↔ (aeval (fwdOp 𝔼) φ) w = 0 := by
  constructor
  · rintro rfl
    exact map_zero _
  · exact eq_zero_of_aeval_fwdOp_eq_zero hφ hroots hw

/-! ### The lag-operator identity of p. 558 and Proposition 8.4 -/

/-- Woodford (2003), p. 558: lags of adapted processes are adapted. -/
theorem lagOp_adapted {𝔼 : ExpectationSystem Ω} {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    𝔼.Adapted (lagOp x) := by
  intro t
  cases t with
  | zero =>
    change 𝔼.E 0 (fun _ => 0) = fun _ => 0
    exact 𝔼.const 0 0
  | succ t =>
    change 𝔼.E (t + 1) (x t) = x t
    rw [← hx t, 𝔼.known (Nat.le_succ t), hx t]

/-- Woodford (2003), p. 558: `E_t L⁻¹ L x_t = x_t` for adapted `x`, i.e. `F (L x) = x`. -/
theorem fwdOp_lagOp {𝔼 : ExpectationSystem Ω} {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    fwdOp 𝔼 (lagOp x) = x := by
  funext t
  exact hx t

/-- Woodford (2003), p. 558: `F^j L^m x = L^{m-j} x` for adapted `x`, `j ≤ m`. -/
theorem fwdOp_pow_lagOp_pow {𝔼 : ExpectationSystem Ω} :
    ∀ (j m : ℕ) {x : ℕ → Ω → ℝ}, 𝔼.Adapted x → j ≤ m →
      ((fwdOp 𝔼) ^ j) (((lagOp (Ω := Ω)) ^ m) x) = ((lagOp (Ω := Ω)) ^ (m - j)) x := by
  intro j
  induction j with
  | zero => intro m x _ _; rfl
  | succ j ih =>
    intro m x hx hjm
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ m by omega)
    have hadapt : ∀ k, 𝔼.Adapted (((lagOp (Ω := Ω)) ^ k) x) := by
      intro k
      induction k with
      | zero => exact hx
      | succ k ihk =>
        rw [pow_succ', Module.End.mul_apply]
        exact lagOp_adapted ihk
    rw [pow_succ, Module.End.mul_apply, add_comm 1 m', pow_succ', Module.End.mul_apply,
      fwdOp_lagOp (hadapt m'), ih m' hx (by omega), show m' + 1 - (j + 1) = m' - j by omega]

/-- Woodford (2003), p. 558: for `γ̃(L⁻¹) = γ(L) L^{-m}` (the reverse of `γ`, `deg γ = m`) and
adapted `g`, `E_t γ̃(L⁻¹) g_{t-m} = γ(L) g_t`, i.e. `γ̃(F) L^m g = γ(L) g`. -/
theorem aeval_fwdOp_reverse_lag {𝔼 : ExpectationSystem Ω} {γ : ℝ[X]} {m : ℕ}
    (hm : γ.natDegree = m) {g : ℕ → Ω → ℝ} (hg : 𝔼.Adapted g) :
    (aeval (fwdOp 𝔼) γ.reverse) (((lagOp (Ω := Ω)) ^ m) g) = (aeval (lagOp (Ω := Ω)) γ) g := by
  rw [aeval_eq_sum_range' (n := m + 1) (Nat.lt_succ_of_le (hm ▸ reverse_natDegree_le γ)),
    aeval_eq_sum_range' (n := m + 1) (by omega)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e1 : m + 1 - 1 - j ≤ m := by omega
  have e2 : m - (m + 1 - 1 - j) = j := by omega
  rw [coeff_reverse, hm, revAt_le e1, e2, fwdOp_pow_lagOp_pow _ _ hg e1, e2]

/-- Woodford (2003), p. 558: lag polynomials preserve adaptedness. -/
theorem aeval_lagOp_adapted {𝔼 : ExpectationSystem Ω} (p : ℝ[X]) {x : ℕ → Ω → ℝ}
    (hx : 𝔼.Adapted x) : 𝔼.Adapted ((aeval (lagOp (Ω := Ω)) p) x) := by
  have hadapt : ∀ k, 𝔼.Adapted (((lagOp (Ω := Ω)) ^ k) x) := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply]
      exact lagOp_adapted ihk
  intro t
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, map_smul, hadapt c t]

/-- Woodford (2003), p. 558: **the lag-operator identity.** If `aᵢ(L) = γ₁(L) γ₂(L)` with
`deg γ₁ = m` and `γ̃₁(L⁻¹) = γ₁(L) L^{-m}`, then for adapted `x`,
`E_t γ̃₁(L⁻¹) [γ₂(L) x_{t-m}] = aᵢ(L) x_t`. -/
theorem p558_identity {𝔼 : ExpectationSystem Ω} {γ1 γ2 : ℝ[X]} {m : ℕ}
    (hm : γ1.natDegree = m) {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) :
    (aeval (fwdOp 𝔼) γ1.reverse) (((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) γ2) x)) =
      (aeval (lagOp (Ω := Ω)) (γ1 * γ2)) x := by
  rw [aeval_fwdOp_reverse_lag hm (aeval_lagOp_adapted γ2 hx), map_mul, Module.End.mul_apply]

/-- Woodford (2003), p. 558: lags preserve boundedness (pre-sample values are zero). -/
theorem boundedProc_lagOp {x : ℕ → Ω → ℝ} (hx : BoundedProc x) :
    BoundedProc (lagOp (Ω := Ω) x) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨max M 0, fun t ω => ?_⟩
  cases t with
  | zero =>
    change |(0 : ℝ)| ≤ _
    rw [abs_zero]
    exact le_max_right _ _
  | succ t => exact (hM t ω).trans (le_max_left _ _)

/-- Woodford (2003), p. 558: lag polynomials preserve boundedness. -/
theorem boundedProc_aeval_lagOp (p : ℝ[X]) :
    ∀ x : ℕ → Ω → ℝ, BoundedProc x → BoundedProc ((aeval (lagOp (Ω := Ω)) p) x) := by
  induction p using Polynomial.induction_on with
  | C a =>
    intro x ⟨M, hM⟩
    refine ⟨|a| * M, fun t ω => ?_⟩
    simp only [aeval_C, Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg a)
  | add p q hp hq =>
    intro x hx
    obtain ⟨M1, h1⟩ := hp x hx
    obtain ⟨M2, h2⟩ := hq x hx
    refine ⟨M1 + M2, fun t ω => ?_⟩
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (h1 t ω) (h2 t ω))
  | monomial n a ih =>
    intro x hx
    have := ih (lagOp x) (boundedProc_lagOp hx)
    rwa [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]

/-- Woodford (2003), p. 558: if all roots of `γ` lie inside the unit circle, all roots of its
reverse `γ̃(μ) = μ^m γ(1/μ)` lie outside it. -/
theorem roots_reverse_outside {p : ℂ[X]} (hin : ∀ z ∈ p.roots, ‖z‖ < 1) :
    ∀ z ∈ p.reverse.roots, 1 < ‖z‖ := by
  intro z hz
  have hrev : p.reverse ≠ 0 := ne_zero_of_mem_roots hz
  have hp : p ≠ 0 := fun h => hrev (by rw [h, reverse_zero])
  have hroot : IsRoot p.reverse z := isRoot_of_mem_roots hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_reverse] at hroot
    exact hp (leadingCoeff_eq_zero.mp hroot)
  let _ : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have h1 : eval₂ (RingHom.id ℂ) (⅟(z⁻¹)) p.reverse = 0 := by
    rw [invOf_eq_inv, inv_inv]
    exact hroot
  rw [eval₂_reverse_eq_zero_iff] at h1
  have hmem : z⁻¹ ∈ p.roots := (mem_roots hp).mpr h1
  have := hin _ hmem
  rw [norm_inv] at this
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  exact (inv_lt_one₀ hn).mp this

/-- Woodford (2003), p. 558: the reverse of a real polynomial, complexified, is the reverse of
the complexified polynomial. -/
theorem map_reverse_ofReal (p : ℝ[X]) :
    p.reverse.map Complex.ofRealHom = (p.map Complex.ofRealHom).reverse := by
  ext n
  rw [coeff_map, coeff_reverse, coeff_reverse, coeff_map,
    natDegree_map_eq_of_injective Complex.ofRealHom.injective]

/-- Woodford (2003), p. 558: **uniqueness in the lag identity.** With `aᵢ = γ₁ γ₂`, `deg γ₁ = m`
and `γ̃₁` invertible (roots outside the unit circle), `γ₂(L) x_{t-m}` is the unique bounded process
`u` with `E_t γ̃₁(L⁻¹) u_t = aᵢ(L) x_t`; i.e. `E_t φ(L⁻¹) aᵢ(L) x_t = γ₂(L) x_{t-m}` for
`φ = γ̃₁⁻¹`. -/
theorem p558_unique {𝔼 : ExpectationSystem Ω} {γ1 γ2 : ℝ[X]} {m : ℕ} (hm : γ1.natDegree = m)
    (hγ1 : γ1 ≠ 0) (hroots : ∀ z ∈ (γ1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖)
    {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hxb : BoundedProc x) {u : ℕ → Ω → ℝ}
    (hub : BoundedProc u) (hu : (aeval (fwdOp 𝔼) γ1.reverse) u = (aeval lagOp (γ1 * γ2)) x) :
    u = ((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) γ2) x) := by
  have hrev : γ1.reverse ≠ 0 := fun h => hγ1 (reverse_eq_zero.mp h)
  have hb2 : BoundedProc (((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) γ2) x)) := by
    have := boundedProc_aeval_lagOp (X ^ m) _ (boundedProc_aeval_lagOp γ2 x hxb)
    rwa [map_pow, aeval_X] at this
  have hdiff : (aeval (fwdOp 𝔼) γ1.reverse)
      (u - ((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) γ2) x)) = 0 := by
    rw [map_sub, hu, p558_identity hm hx, sub_self]
  have hbd : BoundedProc (u - ((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) γ2) x)) := by
    obtain ⟨M1, h1⟩ := hub
    obtain ⟨M2, h2⟩ := hb2
    exact ⟨M1 + M2, fun t ω => (abs_sub _ _).trans (add_le_add (h1 t ω) (h2 t ω))⟩
  exact sub_eq_zero.mp (eq_zero_of_aeval_fwdOp_eq_zero hrev hroots hbd hdiff)

/-- Woodford (2003), Assumption 8.7 and Proposition 8.3, pp. 556–557: the number of zeros of a
lag polynomial `α(L)` inside the unit circle (counted with multiplicity). -/
noncomputable def zerosInside (α : ℝ[X]) : ℕ :=
  Multiset.card ((α.map Complex.ofRealHom).roots.filter (fun z => ‖z‖ < 1))

/-- Woodford (2003), Proposition 8.3, pp. 556–557, **stated (not proved here)**: under
Assumptions 8.1–8.7 (with `n_Z + m` roots `|μ| < β⁻¹`) and `λ_i > 0`, the lag polynomial
`α(L) = det(I − ΛL)` of the optimal instrument rule (1.28) has `m` zeros inside the unit circle
(superinertia). Its proof is in Giannoni and Woodford (2002a) and is deferred; the concrete
instances (Propositions 8.5–8.11) are proved in the chapter's other modules. -/
def Prop83Claim {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
    [DecidableEq ιz] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (H : Prop81Conclusion P 𝔼 t0) : Prop :=
  ∀ m : ℕ, P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m → 1 ≤ m → zerosInside (alpha H.Λ) = m

/-- Woodford (2003), Proposition 8.4, p. 558, **conditional on the factorisation of
Proposition 8.3**: let `α(L) = α₁(L) α₂(L)` with `deg α₁ = m` and `α̃₁(L⁻¹) = α₁(L) L^{-m}` having
all its zeros outside the unit circle, and let `w_t = B₂' B(L) E_t Q(L⁻¹) T̂'Ŵ(τ̂_t − τ̂*)` be
bounded with `g = α̃₁(L⁻¹)⁻¹ w` (the bounded solution of `E_t α̃₁(L⁻¹) g_t = w_t`). Then for a
bounded adapted instrument path, the instrument rule (1.28) in the form
`λ_i α(L)(i_t − i*) + w_t = 0` holds for all `t` iff the targeting rule (1.32)
`g_t + λ_i α₂(L)(i_{t-m} − i*) = 0` holds for all `t`. -/
theorem prop84_conditional {𝔼 : ExpectationSystem Ω} {α1 α2 : ℝ[X]} {m : ℕ}
    (hm : α1.natDegree = m) (hα1 : α1 ≠ 0)
    (hroots : ∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖) {lam istar : ℝ}
    {i w g : ℕ → Ω → ℝ} (hib : BoundedProc i) (hia : 𝔼.Adapted i) (hgb : BoundedProc g)
    (hg : (aeval (fwdOp 𝔼) α1.reverse) g = w) :
    lam • (aeval (lagOp (Ω := Ω)) (α1 * α2)) (fun t ω => i t ω - istar) + w = 0 ↔
      g + lam • ((lagOp (Ω := Ω)) ^ m)
        ((aeval (lagOp (Ω := Ω)) α2) (fun t ω => i t ω - istar)) = 0 := by
  have hrev : α1.reverse ≠ 0 := fun h => hα1 (reverse_eq_zero.mp h)
  have hgapA : 𝔼.Adapted (fun t ω => i t ω - istar) := by
    intro t
    have e : (fun ω => i t ω - istar) = i t - fun _ => istar := rfl
    change 𝔼.E t (fun ω => i t ω - istar) = fun ω => i t ω - istar
    rw [e, map_sub, hia t, 𝔼.const]
  have hgapB : BoundedProc (fun t ω => i t ω - istar) := by
    obtain ⟨M, hM⟩ := hib
    exact ⟨M + |istar|, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)⟩
  set u := lam • ((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) α2)
    (fun t ω => i t ω - istar)) with hu
  have hub : BoundedProc u := by
    have := boundedProc_aeval_lagOp (X ^ m) _ (boundedProc_aeval_lagOp α2 _ hgapB)
    rw [map_pow, aeval_X] at this
    obtain ⟨M, hM⟩ := this
    refine ⟨|lam| * M, fun t ω => ?_⟩
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg lam)
  have key : (aeval (fwdOp 𝔼) α1.reverse) u =
      lam • (aeval (lagOp (Ω := Ω)) (α1 * α2)) (fun t ω => i t ω - istar) := by
    rw [hu, map_smul, p558_identity hm hgapA]
  constructor
  · intro h
    have hz : (aeval (fwdOp 𝔼) α1.reverse) (g + u) = 0 := by
      rw [map_add, hg, key, add_comm]
      exact h
    have hb : BoundedProc (g + u) := by
      obtain ⟨M1, h1⟩ := hgb
      obtain ⟨M2, h2⟩ := hub
      exact ⟨M1 + M2, fun t ω => (abs_add_le _ _).trans (add_le_add (h1 t ω) (h2 t ω))⟩
    exact eq_zero_of_aeval_fwdOp_eq_zero hrev hroots hb hz
  · intro h
    have := congrArg (aeval (fwdOp 𝔼) α1.reverse) h
    rw [map_add, hg, key, map_zero, add_comm] at this
    exact this

end Woodford.OptimalPolicyRules.TargetCriterion
