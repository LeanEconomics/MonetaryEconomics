/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovLinks

/-!
# The Markov equilibrium on a general shock space, and sequence-space determinacy

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392) and §5 (pp. 455–463),
Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3 (pp. 631–635).

`NonlinearNKMarkov` proved existence on a FINITE Markov chain (finite dimension) and the a-priori
bound on every state space. This module removes the finiteness.

## Main results

* The linearised operator is INVERTIBLE on bounded functions of ANY state space with ANY Markov
  operator: `fwdSol`, `fwdSol_spec` (the forward series `u = ∑ Aᵏ Mᵏ b`, convergent because
  `∑ mnorm(Aᵏ) < ∞` under the Taylor principle, `summable_mnorm_pow`), `linSol`, `linSol_spec`
  (`L(linSol r) = r`), `linSol_Lop` (`linSol(Lv) = v`), `norm_linSol_le` (`‖linSol r‖ ≤ K‖r‖`).
* `general_existence` and **`markov_equilibrium_general`**: a quantitative implicit function theorem
  on the Banach space of bounded functions (Newton contraction `z ↦ z − L⁻¹Φ(ε, z)`): there are
  `r, δ > 0` depending ONLY on the parameters such that for EVERY state space, EVERY Markov
  operator and EVERY disturbance pattern with `‖εξ‖ ≤ δ` there is exactly one Markov equilibrium
  with `‖z‖ ≤ r`. Regularity used: the pointwise maps `Q, N` are `C²` (`C¹` suffices for
  existence and uniqueness) and the disturbances are bounded.
* **`second_order_general`**: `‖z_ε‖ ≤ K₁|ε|Ξ` and `‖z_ε − εz₁‖ ≤ K₂(|ε|Ξ)²` with
  `z₁ = L⁻¹(−∂Φ/∂ε)`, uniformly in the state (`taylor2_bound`, `Phi_expand`); **`layerB_general`**:
  the Layer-B family hypothesis (`BridgeExtensions.UProc`) on a general state space.
* A continuous-state instance: `ifsOp` (finitely many successor maps), and **`ar1_equilibrium`**:
  the AR(1) state `x′ = ρx + e`, `e` with finite support, on the bounded interval
  `|x| ≤ ā/(1 − |ρ|)` (uncountably many states, bounded support).
* **Sequence-space determinacy** (`seqOp`, `seqOp_isMarkov`, `seq_uniqueness`,
  `seq_existence`, `markov_is_unique_process`): for ANY `ExpectationSystem` and ANY bounded
  disturbance process, two bounded solutions `z_t(ω)` of the exact stochastic equilibrium
  conditions within `ρ` of the steady state coincide (no Markov structure and no adaptedness
  assumed); in particular the Markov equilibrium is the unique bounded solution near the steady
  state among ALL processes.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovGeneral

open Filter Topology Asymptotics
open NonlinearNKMarkov NonlinearNKMarkovLinks

variable {p : Par} {X : Type*}

/-! ## Matrix power series -/

/-- The entrywise size is submultiplicative. -/
theorem mnorm_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : mnorm (A * B) ≤ mnorm A * mnorm B := by
  unfold mnorm
  calc ∑ i, ∑ j, |(A * B) i j| ≤ ∑ i, ∑ j, ∑ k, |A i k| * |B k j| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        simp only [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ = ∑ i, ∑ k, |A i k| * ∑ j, |B k j| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, |A i k| * ∑ k', ∑ j, |B k' j| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun k' => ∑ j, |B k' j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k))
          (abs_nonneg _)
    _ = (∑ i, ∑ k, |A i k|) * ∑ k', ∑ j, |B k' j| := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]

/-- Woodford (2003), App. A.3: if `mnorm(B^N) ≤ 1/2` then `∑ mnorm(Bᵏ) < ∞`. -/
theorem summable_mnorm_pow {n N : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hN : mnorm (B ^ N) ≤ 1 / 2) (hN0 : 0 < N) : Summable fun k => mnorm (B ^ k) := by
  set C := ∑ k ∈ Finset.range N, mnorm (B ^ k)
  have hq : ∀ q, ∑ k ∈ Finset.range (N * q), mnorm (B ^ k) ≤ 2 * C := by
    intro q
    induction q with
    | zero =>
      rw [mul_zero, Finset.sum_range_zero]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => mnorm_nonneg _)
    | succ q ih =>
      rw [show N * (q + 1) = N + N * q by ring, Finset.sum_range_add]
      have h : ∑ k ∈ Finset.range (N * q), mnorm (B ^ (N + k)) ≤
          1 / 2 * ∑ k ∈ Finset.range (N * q), mnorm (B ^ k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [pow_add]
        exact (mnorm_mul _ _).trans (mul_le_mul_of_nonneg_right hN (mnorm_nonneg _))
      linarith
  refine summable_of_sum_range_le (fun k => mnorm_nonneg _) (c := 2 * C) fun m => ?_
  refine le_trans ?_ (hq m)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2
    (Nat.le_mul_of_pos_left m hN0)) fun _ _ _ => mnorm_nonneg _

/-- Woodford (2003), App. A.3: if `mnorm B < 1` then `∑ mnorm(Bᵏ) < ∞`. -/
theorem summable_mnorm_pow_of_lt {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} (hB : mnorm B < 1) :
    Summable fun k => mnorm (B ^ k) := by
  have h : ∀ k, mnorm (B ^ k) ≤ mnorm (1 : Matrix (Fin n) (Fin n) ℝ) * mnorm B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc mnorm (B ^ k * B) ≤ mnorm (B ^ k) * mnorm B := mnorm_mul _ _
        _ ≤ mnorm (1 : Matrix (Fin n) (Fin n) ℝ) * mnorm B ^ k * mnorm B :=
          mul_le_mul_of_nonneg_right ih (mnorm_nonneg _)
        _ = _ := by ring
  exact Summable.of_nonneg_of_le (fun k => mnorm_nonneg _) h
    ((summable_geometric_of_lt_one (mnorm_nonneg _) hB).mul_left _)

/-- Woodford (2003), Proposition 4.3: under the Taylor principle `∑ mnorm(Aᵏ) < ∞` for the
IS–AS block. -/
theorem summable_mnorm_Amat (hp : p.Std) : Summable fun k => mnorm (Amat p ^ k) := by
  have hN := mnorm_Nhalf hp
  refine summable_mnorm_pow hN (Nat.pos_of_ne_zero fun h0 => ?_)
  rw [h0, pow_zero] at hN
  have : mnorm (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
    norm_num [mnorm, Fin.sum_univ_two, Matrix.one_apply]
  linarith

/-! ## The forward solution of `u = BMu + b` on bounded functions -/

/-- Woodford (2003), (A.13) in Markov form: the forward series `u = ∑ₖ Bᵏ Mᵏ b`. -/
noncomputable def fwdSol {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ))
    (b : X → Fin n → ℝ) : X → Fin n → ℝ :=
  fun x => ∑' k, (B ^ k).mulVec ((Mv M)^[k] b x)

/-- `Mv` of the zero function. -/
theorem Mv_zero {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :
    Mv M (fun _ => (0 : Fin n → ℝ)) = fun _ => 0 := by
  funext x i
  simp only [Mv, Pi.zero_apply]
  have : (fun _ : X => (0 : ℝ)) = 0 := rfl
  rw [this, map_zero]; rfl

/-- `Mv` commutes with finite sums. -/
theorem Mv_sum {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (f : ℕ → X → Fin n → ℝ) (m : ℕ) :
    Mv M (fun x => ∑ k ∈ Finset.range m, f k x) = fun x => ∑ k ∈ Finset.range m, Mv M (f k) x := by
  induction m with
  | zero => simp only [Finset.sum_range_zero]; exact Mv_zero M
  | succ m ih =>
    simp only [Finset.sum_range_succ]
    rw [Mv_add M (fun x => ∑ k ∈ Finset.range m, f k x) (f m), ih]

/-- Woodford (2003), (A.13) and App. A.3 (**the forward solution on ANY state space**): if
`∑ mnorm(Bᵏ) < ∞`, `M` is a Markov operator and `‖b‖ ≤ B̄`, the forward series converges,
`‖u‖ ≤ (∑ mnorm(Bᵏ))B̄`, and `u = BMu + b`. -/
theorem fwdSol_spec {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : Summable fun k => mnorm (B ^ k)) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {b : X → Fin n → ℝ} {Bb : ℝ} (hBb : 0 ≤ Bb) (hb : ∀ x, ‖b x‖ ≤ Bb) :
    (∀ x, ‖fwdSol B M b x‖ ≤ (∑' k, mnorm (B ^ k)) * Bb) ∧
      ∀ x, fwdSol B M b x = B.mulVec (Mv M (fwdSol B M b) x) + b x := by
  set f : ℕ → X → Fin n → ℝ := fun k x => (B ^ k).mulVec ((Mv M)^[k] b x) with hf
  have hfb : ∀ k x, ‖f k x‖ ≤ mnorm (B ^ k) * Bb := fun k x =>
    (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (iter_norm_le hM k hBb hb x)
      (mnorm_nonneg _))
  have hsB : Summable fun k => mnorm (B ^ k) * Bb := hB.mul_right Bb
  have hsum : ∀ x, Summable fun k => f k x := fun x =>
    Summable.of_norm_bounded hsB fun k => hfb k x
  have hbound : ∀ x, ‖fwdSol B M b x‖ ≤ (∑' k, mnorm (B ^ k)) * Bb := fun x => by
    rw [← tsum_mul_right]
    exact tsum_of_norm_bounded hsB.hasSum fun k => hfb k x
  refine ⟨hbound, fun x => ?_⟩
  -- tails
  have htail : ∀ m x', ‖fwdSol B M b x' - ∑ k ∈ Finset.range m, f k x'‖ ≤
      ∑' k, mnorm (B ^ (k + m)) * Bb := fun m x' => by
    have h := (hsum x').sum_add_tsum_nat_add m
    have e : fwdSol B M b x' - ∑ k ∈ Finset.range m, f k x' = ∑' k, f (k + m) x' := by
      change ∑' k, f k x' - _ = _
      rw [← h]; abel
    rw [e]
    exact tsum_of_norm_bounded ((summable_nat_add_iff m).2 hsB).hasSum fun k => hfb (k + m) x'
  have htail0 : Tendsto (fun m => ∑' k, mnorm (B ^ (k + m)) * Bb) atTop (𝓝 0) :=
    tendsto_sum_nat_add fun k => mnorm (B ^ k) * Bb
  -- `M` passes through the series
  have hMf : ∀ k x', Mv M (f k) x' = (B ^ k).mulVec ((Mv M)^[k + 1] b x') := fun k x' => by
    rw [Function.iterate_succ_apply', hf]
    exact congrFun (Mv_mulVec M (B ^ k) ((Mv M)^[k] b)) x'
  have hsumM : Summable fun k => Mv M (f k) x := by
    refine Summable.of_norm_bounded hsB fun k => ?_
    rw [hMf]
    exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left
      (iter_norm_le hM (k + 1) hBb hb x) (mnorm_nonneg _))
  have hlim : Tendsto (fun m => ∑ k ∈ Finset.range m, Mv M (f k) x) atTop
      (𝓝 (Mv M (fwdSol B M b) x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) htail0
    have e := congrFun (Mv_sum M f m) x
    rw [← e, norm_sub_rev]
    have e2 := congrFun (Mv_sub M (fwdSol B M b) (fun x' => ∑ k ∈ Finset.range m, f k x')) x
    rw [← e2]
    exact Mv_norm_le hM (tsum_nonneg fun k => mul_nonneg (mnorm_nonneg _) hBb)
      (fun x' => htail m x') x
  have hMu : Mv M (fwdSol B M b) x = ∑' k, Mv M (f k) x :=
    tendsto_nhds_unique hlim hsumM.hasSum.tendsto_sum_nat
  -- the recursion
  have h0 := (hsum x).tsum_eq_zero_add
  change ∑' k, f k x = _
  rw [h0, hMu]
  have hlin : B.mulVec (∑' k, Mv M (f k) x) = ∑' k, B.mulVec (Mv M (f k) x) := by
    have := (Matrix.mulVecLin B).toContinuousLinearMap.map_tsum hsumM
    simpa using this
  rw [hlin]
  have e1 : (fun k => f (k + 1) x) = fun k => B.mulVec (Mv M (f k) x) := funext fun k => by
    rw [hMf, Matrix.mulVec_mulVec, ← pow_succ']
  have e0 : f 0 x = b x := by simp [hf]
  rw [e1, e0, add_comm]

/-! ## The inverse of the linearised operator on bounded functions -/

/-- The NKPC forcing `s₁` built from the right-hand side `r`. -/
noncomputable def s1F (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 4 → ℝ) : X → ℝ :=
  fun x => (r x 2 - r x 1 + p.k3 * r x 3 - p.α * p.β * p.k3 * M (fun x' => r x' 3) x) / p.cR

/-- The forcing of the IS–AS block built from `r`. -/
noncomputable def bF (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 4 → ℝ) :
    X → Fin 2 → ℝ :=
  fun x => ![(r x 0 - p.φ * s1F p M r x) / p.dd,
    (p.κ * r x 0 + (p.σ + p.φy) * s1F p M r x) / p.dd]

/-- The IS–AS block `(ŷ, π)` solving `u = AMu + b` forward. -/
noncomputable def uF (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 4 → ℝ) :
    X → Fin 2 → ℝ :=
  fwdSol (Amat p) M (bF p M r)

/-- The forcing of the `F` recursion. -/
noncomputable def gF (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 4 → ℝ) : X → ℝ :=
  fun x => r x 1 + (1 - p.α * p.β) * (1 - p.σ) * uF p M r x 0 +
    p.α * p.β * (p.θ - 1) * M (fun x' => uF p M r x' 1) x

/-- `F̂` solving `F = αβMF + g` forward. -/
noncomputable def FF (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 4 → ℝ) : X → ℝ :=
  fun x => fwdSol !![p.α * p.β] M (fun x => ![gF p M r x]) x 0

/-- Woodford (2003), App. A.3, (A.13) (**the inverse of the linearised operator**): `ŷ, π` from
the IS–AS block, `F̂` from its forward recursion, `K̂ = F̂ + cπ − k₃r₃` from the price index. -/
noncomputable def linSol (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 4 → ℝ) :
    X → Fin 4 → ℝ :=
  fun x => ![uF p M r x 0, uF p M r x 1, FF p M r x,
    FF p M r x + p.cR * uF p M r x 1 - p.k3 * r x 3]

/-- `mnorm` of the `1 × 1` matrix `(αβ)`. -/
theorem mnorm_ab : mnorm !![p.α * p.β] = |p.α * p.β| := by
  simp [mnorm]

/-- Woodford (2003), App. A.3, (A.12)–(A.13) (**the linearised operator is ONTO bounded
functions, for any Markov operator**): for bounded `r`, `linSol r` is bounded and
`L(linSol r) = r`. -/
theorem linSol_spec (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {r : X → Fin 4 → ℝ} {a : ℝ} (ha0 : 0 ≤ a) (hr : ∀ x, ‖r x‖ ≤ a) :
    (∃ C, ∀ x, ‖linSol p M r x‖ ≤ C) ∧ Lop p M (linSol p M r) = r := by
  have hrc : ∀ i x, |r x i| ≤ a := fun i x => by
    have := norm_le_pi_norm (r x) i; rw [Real.norm_eq_abs] at this; exact this.trans (hr x)
  have hd := hp.dd_pos
  have hcR := hp.cR_pos
  have hk3 := hp.k3_pos
  have hab0 := hp.ab_pos
  have hab1 := hp.ab_lt_one
  -- bounds
  have hm3 : ∀ x, |M (fun x' => r x' 3) x| ≤ a := hM.2 _ a (fun x' => hrc 3 x')
  have hs1 : ∀ x, |s1F p M r x| ≤ (2 + p.k3 + p.α * p.β * p.k3) / p.cR * a := fun x => by
    unfold s1F
    rw [abs_div, abs_of_pos hcR, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcR]
    calc |r x 2 - r x 1 + p.k3 * r x 3 - p.α * p.β * p.k3 * M (fun x' => r x' 3) x|
        ≤ |r x 2| + |r x 1| + p.k3 * |r x 3| + p.α * p.β * p.k3 * |M (fun x' => r x' 3) x| := by
          have e1 := abs_sub (r x 2 - r x 1 + p.k3 * r x 3)
            (p.α * p.β * p.k3 * M (fun x' => r x' 3) x)
          have e2 := abs_add_le (r x 2 - r x 1) (p.k3 * r x 3)
          have e3 := abs_sub (r x 2) (r x 1)
          rw [abs_mul (p.α * p.β * p.k3), abs_of_pos (by positivity : 0 < p.α * p.β * p.k3),
            abs_mul, abs_of_pos hk3] at *
          linarith
      _ ≤ a + a + p.k3 * a + p.α * p.β * p.k3 * a := by
          gcongr
          · exact hrc 2 x
          · exact hrc 1 x
          · exact hrc 3 x
          · exact hm3 x
      _ = (2 + p.k3 + p.α * p.β * p.k3) * a := by ring
  set S1 := (2 + p.k3 + p.α * p.β * p.k3) / p.cR * a with hS1
  have hS10 : 0 ≤ S1 := by positivity
  set Bb := (a + p.φ * S1 + p.κ * a + (p.σ + p.φy) * S1) / p.dd with hBb
  have hBb0 : 0 ≤ Bb := by
    have := hp.φ_nonneg; have := hp.κ_pos; have := hp.σ_pos; have := hp.φy_nonneg
    positivity
  have hbb : ∀ x, ‖bF p M r x‖ ≤ Bb := fun x => by
    refine (pi_norm_le_iff_of_nonneg hBb0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have h0 := hrc 0 x
    have hs := hs1 x
    have hφ := hp.φ_nonneg
    have hκ := hp.κ_pos
    have hσφ : 0 ≤ p.σ + p.φy := by linarith [hp.σ_pos, hp.φy_nonneg]
    fin_cases i
    · simp only [bF, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hd, hBb]
      refine div_le_div_of_nonneg_right ?_ hd.le
      have := abs_sub (r x 0) (p.φ * s1F p M r x)
      rw [abs_mul, abs_of_nonneg hφ] at this
      have := mul_le_mul_of_nonneg_left hs hφ
      nlinarith [mul_nonneg hκ.le ha0, mul_nonneg hσφ hS10]
    · simp only [bF, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hd, hBb]
      refine div_le_div_of_nonneg_right ?_ hd.le
      have := abs_add_le (p.κ * r x 0) ((p.σ + p.φy) * s1F p M r x)
      rw [abs_mul, abs_of_pos hκ, abs_mul, abs_of_nonneg hσφ] at this
      have := mul_le_mul_of_nonneg_left hs hσφ
      have := mul_le_mul_of_nonneg_left h0 hκ.le
      nlinarith [mul_nonneg hφ hS10]
  obtain ⟨huB, hueq⟩ := fwdSol_spec (summable_mnorm_Amat hp) hM hBb0 hbb
  set U := (∑' k, mnorm (Amat p ^ k)) * Bb with hU
  have hU0 : 0 ≤ U := mul_nonneg (tsum_nonneg fun _ => mnorm_nonneg _) hBb0
  have huc : ∀ i x, |uF p M r x i| ≤ U := fun i x => by
    have := norm_le_pi_norm (uF p M r x) i; rw [Real.norm_eq_abs] at this
    exact this.trans (huB x)
  have hmu : ∀ i x, |M (fun x' => uF p M r x' i) x| ≤ U := fun i x => hM.2 _ U (huc i) x
  set G := a + (1 - p.α * p.β) * |1 - p.σ| * U + p.α * p.β * (p.θ - 1) * U with hG
  have hθ1 : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have hG0 : 0 ≤ G := by
    have : 0 < 1 - p.α * p.β := by linarith
    positivity
  have hgb : ∀ x, ‖(fun x => ![gF p M r x]) x‖ ≤ G := fun x => by
    refine (pi_norm_le_iff_of_nonneg hG0).2 fun i => ?_
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, Real.norm_eq_abs, gF]
    have e1 := abs_add_le (r x 1 + (1 - p.α * p.β) * (1 - p.σ) * uF p M r x 0)
      (p.α * p.β * (p.θ - 1) * M (fun x' => uF p M r x' 1) x)
    have e2 := abs_add_le (r x 1) ((1 - p.α * p.β) * (1 - p.σ) * uF p M r x 0)
    have t1 : |(1 - p.α * p.β) * (1 - p.σ) * uF p M r x 0| ≤
        (1 - p.α * p.β) * |1 - p.σ| * U := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 - p.α * p.β)]
      exact mul_le_mul_of_nonneg_left (huc 0 x) (mul_nonneg
        (by linarith : (0 : ℝ) ≤ 1 - p.α * p.β) (abs_nonneg (1 - p.σ)))
    have t2 : |p.α * p.β * (p.θ - 1) * M (fun x' => uF p M r x' 1) x| ≤
        p.α * p.β * (p.θ - 1) * U := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < p.α * p.β * (p.θ - 1))]
      exact mul_le_mul_of_nonneg_left (hmu 1 x) (by positivity)
    have := hrc 1 x
    linarith
  have habs : mnorm !![p.α * p.β] < 1 := by
    rw [mnorm_ab, abs_of_pos hab0]; exact hab1
  obtain ⟨hFB, hFeq⟩ := fwdSol_spec (summable_mnorm_pow_of_lt habs) hM hG0 hgb
  set W := (∑' k, mnorm (!![p.α * p.β] ^ k)) * G with hW
  have hFc : ∀ x, |FF p M r x| ≤ W := fun x => by
    have := norm_le_pi_norm (fwdSol !![p.α * p.β] M (fun x => ![gF p M r x]) x) 0
    rw [Real.norm_eq_abs] at this
    exact this.trans (hFB x)
  refine ⟨⟨U + W + (W + p.cR * U + p.k3 * a), fun x => ?_⟩, ?_⟩
  · have hW0 : 0 ≤ W := (abs_nonneg _).trans (hFc x)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have hK : |FF p M r x + p.cR * uF p M r x 1 - p.k3 * r x 3| ≤ W + p.cR * U + p.k3 * a := by
      have e1 := abs_sub (FF p M r x + p.cR * uF p M r x 1) (p.k3 * r x 3)
      have e2 := abs_add_le (FF p M r x) (p.cR * uF p M r x 1)
      rw [abs_mul, abs_of_pos hcR] at e2
      rw [abs_mul p.k3, abs_of_pos hk3] at e1
      have := mul_le_mul_of_nonneg_left (huc 1 x) hcR.le
      have := mul_le_mul_of_nonneg_left (hrc 3 x) hk3.le
      have := hFc x
      linarith
    fin_cases i
    · simp only [linSol, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [huc 0 x, mul_nonneg hcR.le hU0, mul_nonneg hk3.le ha0, hW0]
    · simp only [linSol, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [huc 1 x, mul_nonneg hcR.le hU0, mul_nonneg hk3.le ha0, hW0]
    · simp only [linSol, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      linarith [hFc x, mul_nonneg hcR.le hU0, mul_nonneg hk3.le ha0, hU0]
    · simp only [linSol, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      linarith
  · -- the equations
    set v := linSol p M r with hv
    have hv0 : ∀ x, v x 0 = uF p M r x 0 := fun x => rfl
    have hv1 : ∀ x, v x 1 = uF p M r x 1 := fun x => rfl
    have hv2 : ∀ x, v x 2 = FF p M r x := fun x => rfl
    have hv3 : ∀ x, v x 3 = FF p M r x + p.cR * uF p M r x 1 - p.k3 * r x 3 := fun x => rfl
    -- the IS–AS block
    have hu : ∀ x, p.dd * uF p M r x 0 = p.σ * M (fun x' => uF p M r x' 0) x +
          (1 - p.φ * p.β) * M (fun x' => uF p M r x' 1) x + (r x 0 - p.φ * s1F p M r x) ∧
        p.dd * uF p M r x 1 = p.κ * p.σ * M (fun x' => uF p M r x' 0) x +
          (p.κ + p.β * (p.σ + p.φy)) * M (fun x' => uF p M r x' 1) x +
          (p.κ * r x 0 + (p.σ + p.φy) * s1F p M r x) := fun x => by
      have h := hueq x
      rw [← show uF p M r = fwdSol (Amat p) M (bF p M r) from rfl] at h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Amat, bF, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Mv] at h0 h1
      have hd' := hd.ne'
      constructor
      · rw [h0]; field_simp
      · rw [h1]; field_simp
    have hNK : ∀ x, uF p M r x 1 - p.β * M (fun x' => uF p M r x' 1) x -
        p.κ * uF p M r x 0 = s1F p M r x := fun x => by
      obtain ⟨h0, h1⟩ := hu x
      have hd' := hd.ne'
      have : p.dd * (uF p M r x 1 - p.β * M (fun x' => uF p M r x' 1) x -
          p.κ * uF p M r x 0) = p.dd * s1F p M r x := by
        have e : p.dd = p.σ + p.φy + p.φ * p.κ := rfl
        linear_combination h1 - p.κ * h0 -
          (p.β * M (fun x' => uF p M r x' 1) x + s1F p M r x) * e
      exact mul_left_cancel₀ hd' this
    -- `F`
    have hF : ∀ x, FF p M r x = p.α * p.β * M (FF p M r) x + gF p M r x := fun x => by
      have h := congrFun (hFeq x) 0
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.add_apply, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Mv] at h
      exact h
    have hMK : ∀ x, M (fun x' => v x' 3) x = M (FF p M r) x +
        p.cR * M (fun x' => uF p M r x' 1) x - p.k3 * M (fun x' => r x' 3) x := fun x => by
      have e : (fun x' => v x' 3) = fun x' => (1 * FF p M r x' + p.cR * uF p M r x' 1) +
          -p.k3 * r x' 3 := by funext x'; rw [hv3]; ring
      rw [e]
      have e1 := M_lin M 1 (-p.k3) (fun x' => 1 * FF p M r x' + p.cR * uF p M r x' 1)
        (fun x' => r x' 3) x
      have e2 := M_lin M 1 p.cR (FF p M r) (fun x' => uF p M r x' 1) x
      simp only [one_mul] at e1 e2 ⊢
      rw [e1, e2]; ring
    funext x i
    obtain ⟨c0, c1, c2, c3⟩ := Lop_apply (p := p) M v x
    have hab := hp.ab_c
    have hk' : p.κ * p.cR = (1 - p.α * p.β) * (p.ω + p.σ) := by
      rw [hp.κ_eq]; field_simp
    have hcRc : (1 - p.α) * p.cR = p.α * p.c0 := by
      unfold Par.cR; have : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
      field_simp
    have hk3c : (1 - p.α) * (p.θ - 1) * p.k3 = p.c0 := by
      unfold Par.k3; have : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
      field_simp
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [c0, hv0, hv1]
      have hMv0 : M (fun x' => v x' 0) x = M (fun x' => uF p M r x' 0) x := rfl
      have hMv1 : M (fun x' => v x' 1) x = M (fun x' => uF p M r x' 1) x := rfl
      rw [hMv0, hMv1]
      obtain ⟨h0, -⟩ := hu x
      have hnk := hNK x
      have e : p.dd = p.σ + p.φy + p.φ * p.κ := rfl
      rw [e] at h0
      linear_combination h0 + p.φ * hnk
    · simp only [Fin.mk_one, Fin.isValue]
      rw [c1, hv2, hv0]
      have hMv1 : M (fun x' => v x' 1) x = M (fun x' => uF p M r x' 1) x := rfl
      have hMv2 : M (fun x' => v x' 2) x = M (FF p M r) x := rfl
      rw [hMv1, hMv2, hF x]
      simp only [gF]
      ring
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [c2, hv3, hv0, hMK x]
      have hMv1 : M (fun x' => v x' 1) x = M (fun x' => uF p M r x' 1) x := rfl
      rw [hMv1, hF x]
      have hnk := hNK x
      have hs1' : p.cR * s1F p M r x = r x 2 - r x 1 + p.k3 * r x 3 -
          p.α * p.β * p.k3 * M (fun x' => r x' 3) x := by
        unfold s1F; field_simp
      simp only [gF]
      unfold Par.c0 at hab
      linear_combination p.cR * hnk + hs1' + uF p M r x 0 * hk' -
        M (fun x' => uF p M r x' 1) x * hab
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [c3, hv1, hv2, hv3]
      have hc0 := hp.c0_pos.ne'
      have e : (1 - p.α) * (p.θ - 1) * (FF p M r x + p.cR * uF p M r x 1 - p.k3 * r x 3 -
          FF p M r x) / p.c0 = p.α * (p.θ - 1) * uF p M r x 1 - r x 3 := by
        rw [div_eq_iff hc0]
        linear_combination (p.θ - 1) * uF p M r x 1 * hcRc - r x 3 * hk3c
      rw [e]; ring

/-! ## Linearity, boundedness and the inverse bound -/

/-- `DQ` is additive in differences. -/
theorem DQ0_sub (a b : Fin 4 → ℝ) : DQ0 p (a - b) = DQ0 p a - DQ0 p b := by
  funext i; fin_cases i <;> simp [DQ0] <;> ring

/-- `DN` is additive in differences. -/
theorem DN0_sub (a b : Fin 4 → ℝ) : DN0 p (a - b) = DN0 p a - DN0 p b := by
  funext i; fin_cases i <;> simp [DN0] <;> ring

/-- Woodford (2003), App. A.3: the linearised operator is additive in differences. -/
theorem Lop_sub (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v w : X → Fin 4 → ℝ) :
    Lop p M (fun x => v x - w x) = fun x => Lop p M v x - Lop p M w x := by
  funext x
  simp only [Lop, DQ0_sub]
  have := congrFun (Mv_sub M (fun x' => DN0 p (v x')) (fun x' => DN0 p (w x'))) x
  simp only [← DN0_sub] at this
  rw [show (fun x' => DN0 p (v x' - w x')) = fun x' => DN0 p ((fun x => v x - w x) x') from rfl]
    at this
  rw [this]; abel

/-- `‖(0, w)‖ = ‖w‖`. -/
theorem norm_pair_zero (w : Fin 4 → ℝ) : ‖((0 : Fin 5 → ℝ), w)‖ = ‖w‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

/-- Woodford (2003), App. A.3: the linearised operator maps bounded functions to bounded
functions. -/
theorem Lop_bounded {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) {v : X → Fin 4 → ℝ} {V : ℝ}
    (hV : 0 ≤ V) (hv : ∀ x, ‖v x‖ ≤ V) :
    ∀ x, ‖Lop p M v x‖ ≤ (‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖) * V := by
  intro x
  have hq : ∀ w, ‖DQ0 p w‖ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * ‖w‖ := fun w => by
    rw [← fderiv_Qmap_inr, ← norm_pair_zero w]; exact ContinuousLinearMap.le_opNorm _ _
  have hn : ∀ w, ‖DN0 p w‖ ≤ ‖fderiv ℝ (Nmap p) (0, 0)‖ * ‖w‖ := fun w => by
    rw [← fderiv_Nmap_inr, ← norm_pair_zero w]; exact ContinuousLinearMap.le_opNorm _ _
  have h2 := Mv_norm_le hM (mul_nonneg (norm_nonneg _) hV) (fun x' => (hn (v x')).trans
    (mul_le_mul_of_nonneg_left (hv x') (norm_nonneg _))) x
  calc ‖Lop p M v x‖ ≤ ‖DQ0 p (v x)‖ + ‖Mv M (fun x' => DN0 p (v x')) x‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * V + ‖fderiv ℝ (Nmap p) (0, 0)‖ * V :=
        add_le_add ((hq _).trans (mul_le_mul_of_nonneg_left (hv x) (norm_nonneg _))) h2
    _ = _ := by ring

/-- Woodford (2003), App. A.3: `‖linSol r‖ ≤ K sup‖r‖` (`K = Kap p`). -/
theorem norm_linSol_le (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {r : X → Fin 4 → ℝ} {a : ℝ} (ha0 : 0 ≤ a) (hr : ∀ x, ‖r x‖ ≤ a) (x : X) :
    ‖linSol p M r x‖ ≤ Kap p * a := by
  obtain ⟨⟨C, hC⟩, hL⟩ := linSol_spec hp hM ha0 hr
  exact apriori hp hM hC (fun x => by rw [hL]; exact hr x) x

/-- Woodford (2003), App. A.3: `linSol` inverts `L` on bounded functions, `linSol(Lv) = v`. -/
theorem linSol_Lop (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {v : X → Fin 4 → ℝ} {V : ℝ} (hV : 0 ≤ V) (hv : ∀ x, ‖v x‖ ≤ V) :
    linSol p M (Lop p M v) = v := by
  have hb := Lop_bounded (p := p) hM hV hv
  obtain ⟨⟨C, hC⟩, hL⟩ := linSol_spec hp hM (by positivity) hb
  have hd : (fun x => linSol p M (Lop p M v) x - v x) = 0 := by
    refine Lop_injective hp hM (V0 := C + V) (fun x => (norm_sub_le _ _).trans
      (add_le_add (hC x) (hv x))) ?_
    rw [Lop_sub, hL]; funext x; simp
  funext x
  exact sub_eq_zero.1 (congrFun hd x)

/-- Woodford (2003), App. A.3: `linSol` is additive in differences on bounded functions. -/
theorem linSol_sub (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {r r' : X → Fin 4 → ℝ} {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hr : ∀ x, ‖r x‖ ≤ a)
    (hr' : ∀ x, ‖r' x‖ ≤ a') :
    linSol p M (fun x => r x - r' x) = fun x => linSol p M r x - linSol p M r' x := by
  have hd : ∀ x, ‖r x - r' x‖ ≤ a + a' := fun x => (norm_sub_le _ _).trans (add_le_add (hr x)
    (hr' x))
  obtain ⟨⟨C1, hC1⟩, hL1⟩ := linSol_spec hp hM (add_nonneg ha ha') hd
  obtain ⟨⟨C2, hC2⟩, hL2⟩ := linSol_spec hp hM ha hr
  obtain ⟨⟨C3, hC3⟩, hL3⟩ := linSol_spec hp hM ha' hr'
  have h0 : (fun x => linSol p M (fun x => r x - r' x) x -
      (linSol p M r x - linSol p M r' x)) = 0 := by
    refine Lop_injective hp hM (V0 := C1 + (C2 + C3)) (fun x => (norm_sub_le _ _).trans
      (add_le_add (hC1 x) ((norm_sub_le _ _).trans (add_le_add (hC2 x) (hC3 x))))) ?_
    rw [Lop_sub, hL1, Lop_sub, hL2, hL3]; funext x; simp
  funext x
  exact sub_eq_zero.1 (congrFun h0 x)

/-! ## Existence on a general state space: the Newton contraction -/

/-- Woodford (2003), App. A.3: the residual minus its linearisation is small: for `z, z′` and
disturbances within the radii of `remainder_small`, `‖Φz − Φz′ − L(z − z′)‖ ≤ 2η sup‖z − z′‖`. -/
theorem resid_diff_bound {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) {η ρQ ρN : ℝ}
    (hη0 : 0 ≤ η)
    (hQ : ∀ e w w', ‖e‖ ≤ ρQ → ‖w‖ ≤ ρQ → ‖w'‖ ≤ ρQ →
      ‖Qmap p (e, w) - Qmap p (e, w') - fderiv ℝ (Qmap p) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    (hN : ∀ e w w', ‖e‖ ≤ ρN → ‖w‖ ≤ ρN → ‖w'‖ ≤ ρN →
      ‖Nmap p (e, w) - Nmap p (e, w') - fderiv ℝ (Nmap p) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    {ξ : X → Fin 5 → ℝ} {ε : ℝ} {z z' : X → Fin 4 → ℝ}
    (he : ∀ x, ‖ε • ξ x‖ ≤ min ρQ ρN) (hz : ∀ x, ‖z x‖ ≤ min ρQ ρN)
    (hz' : ∀ x, ‖z' x‖ ≤ min ρQ ρN) {D : ℝ} (hD : ∀ x, ‖z x - z' x‖ ≤ D) (x : X) :
    ‖Phi p M ξ ε z x - Phi p M ξ ε z' x - Lop p M (fun x => z x - z' x) x‖ ≤ 2 * η * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
  have e2 : ∀ x', ‖Nmap p (ε • ξ x', z x') - Nmap p (ε • ξ x', z' x') -
      fderiv ℝ (Nmap p) (0, 0) (0, z x' - z' x')‖ ≤ η * D := fun x' =>
    (hN _ _ _ ((he x').trans (min_le_right _ _)) ((hz x').trans (min_le_right _ _))
      ((hz' x').trans (min_le_right _ _))).trans (mul_le_mul_of_nonneg_left (hD x') hη0)
  have e1 := (hQ (ε • ξ x) (z x) (z' x) ((he x).trans (min_le_left _ _))
    ((hz x).trans (min_le_left _ _)) ((hz' x).trans (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_left (hD x) hη0)
  have e3 := Mv_norm_le hM (mul_nonneg hη0 hD0) e2 x
  have key : Phi p M ξ ε z x - Phi p M ξ ε z' x - Lop p M (fun x => z x - z' x) x =
      (Qmap p (ε • ξ x, z x) - Qmap p (ε • ξ x, z' x) -
        fderiv ℝ (Qmap p) (0, 0) (0, z x - z' x)) +
      Mv M (fun x' => Nmap p (ε • ξ x', z x') - Nmap p (ε • ξ x', z' x') -
        fderiv ℝ (Nmap p) (0, 0) (0, z x' - z' x')) x := by
    simp only [fderiv_Qmap_inr, fderiv_Nmap_inr]
    have m1 := congrFun (Mv_sub M (fun x' => Nmap p (ε • ξ x', z x') -
      Nmap p (ε • ξ x', z' x')) (fun x' => DN0 p (z x' - z' x'))) x
    have m2 := congrFun (Mv_sub M (fun x' => Nmap p (ε • ξ x', z x'))
      (fun x' => Nmap p (ε • ξ x', z' x'))) x
    rw [m1, m2]
    simp only [Phi, Lop]
    abel
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ η * D + η * D := add_le_add e1 e3
    _ = 2 * η * D := by ring

/-- `Φ(ε, 0)` at the steady state: `Φ(ε, 0) = [Q(εξ, 0) − Q(0, 0)] + M[N(εξ, 0) − N(0, 0)]`. -/
theorem Phi_zero_eq {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) (ξ : X → Fin 5 → ℝ) (ε : ℝ)
    (x : X) : Phi p M ξ ε 0 x = (Qmap p (ε • ξ x, 0) - Qmap p (0, 0)) +
      Mv M (fun x' => Nmap p (ε • ξ x', 0) - Nmap p (0, 0)) x := by
  have hs : Qmap p (0, 0) + Mv M (fun _ => Nmap p (0, 0)) x = 0 := by
    have := congrFun (steadyState_eqm (p := p) hM ξ) x
    simpa [Phi] using this
  have m := congrFun (Mv_sub M (fun x' => Nmap p (ε • ξ x', 0))
    (fun _ => Nmap p (0, 0))) x
  simp only [Phi, Pi.zero_apply]
  rw [m]
  linear_combination hs

/-- Woodford (2003), App. A.3 (**a quantitative implicit function theorem on bounded functions:
existence**). Under the Taylor principle there is `r₀ > 0` such that for every radius
`0 < r ≤ r₀` there is `δ > 0`, depending ONLY on the parameters, with: for EVERY state space, EVERY
Markov operator and EVERY disturbance pattern with `‖εξ(x)‖ ≤ δ`, a Markov equilibrium with
`‖z(x)‖ ≤ r` exists (the limit of the Newton iteration `z ↦ z − L⁻¹Φ(ε, z)`, a contraction with
factor `1/2` on the ball). -/
theorem general_existence (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)),
      IsMarkov M → ∀ (ξ : X → Fin 5 → ℝ) (ε : ℝ), (∀ x, ‖ε • ξ x‖ ≤ δ) →
        ∃ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) ∧ IsMarkovEqm p M ξ ε z := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_small (contDiff_Qmap (p := p) (n := 1)) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_small (contDiff_Nmap (p := p) (n := 1)) hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  -- bounds of `Q`, `N` on the ball
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Qmap (p := p) (n := 0)).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  refine ⟨r0, hr00, fun r hr hrr0 => ?_⟩
  set τ := r / (4 * Kap p) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin 5 → ℝ => Qmap p (e, 0)) 0 :=
    ((contDiff_Qmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  have hcN : ContinuousAt (fun e : Fin 5 → ℝ => Nmap p (e, 0)) 0 :=
    ((contDiff_Nmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  refine ⟨min r (min (δQ / 2) (δN / 2)), lt_min hr (lt_min (by positivity) (by positivity)),
    fun X M hM ξ ε hξ => ?_⟩
  have hξr : ∀ x, ‖ε • ξ x‖ ≤ r := fun x => (hξ x).trans (min_le_left _ _)
  have hξ0 : ∀ x, ‖ε • ξ x‖ ≤ r0 := fun x => (hξr x).trans hrr0
  -- `Φ` is bounded on the ball
  have hPhiB : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖Phi p M ξ ε z x‖ ≤ CQ + CN := by
    intro z hz x
    have hin : ∀ x', (ε • ξ x', z x') ∈ Metric.closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ)) r0 :=
      fun x' => by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        exact max_le (hξ0 x') ((hz x').trans hrr0)
    have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN _ (hin x))
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (hin x))
      (Mv_norm_le hM hCN0 (fun x' => hCN _ (hin x')) x))
  -- the Newton map
  set T : (X → Fin 4 → ℝ) → (X → Fin 4 → ℝ) := fun z x => z x - linSol p M (Phi p M ξ ε z) x
    with hT
  have hCQN : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → 0 ≤ CQ + CN := fun z hz => by
    by_cases hX : Nonempty X
    · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hPhiB z hz x)
    · have hin : ((0 : Fin 5 → ℝ), (0 : Fin 4 → ℝ)) ∈ Metric.closedBall 0 r0 :=
        Metric.mem_closedBall_self hr00.le
      exact add_nonneg ((norm_nonneg _).trans (hCQ _ hin)) ((norm_nonneg _).trans (hCN _ hin))
  have hcontr : ∀ z z' : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → (∀ x, ‖z' x‖ ≤ r) → ∀ D,
      (∀ x, ‖z x - z' x‖ ≤ D) → ∀ x, ‖T z x - T z' x‖ ≤ D / 2 := by
    intro z z' hz hz' D hD x
    have hD0 : 0 ≤ D := by
      by_cases hX : Nonempty X
      · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hD x)
      · exact absurd ⟨x⟩ hX
    have hz0 : ∀ x, ‖z x‖ ≤ r0 := fun x => (hz x).trans hrr0
    have hz'0 : ∀ x, ‖z' x‖ ≤ r0 := fun x => (hz' x).trans hrr0
    have hC := hCQN z hz
    have hLd := Lop_bounded (p := p) hM hD0 hD
    set c := (‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖) * D
    have hc0 : 0 ≤ c := mul_nonneg (by positivity) hD0
    have hres := resid_diff_bound (p := p) hM hη0.le hQ hN hξ0 hz0 hz'0 hD
    -- `T z − T z′ = −L⁻¹(Φz − Φz′ − L(z − z′))`
    have e1 := linSol_sub hp hM hC hC (hPhiB z hz) (hPhiB z' hz')
    have e2 := linSol_sub hp hM (a := CQ + CN + (CQ + CN)) (a' := c) (by positivity) hc0
      (r := fun x => Phi p M ξ ε z x - Phi p M ξ ε z' x)
      (fun x => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz x) (hPhiB z' hz' x))) hLd
    have e3 := linSol_Lop hp hM hD0 hD
    have key : T z x - T z' x = -linSol p M (fun x => Phi p M ξ ε z x - Phi p M ξ ε z' x -
        Lop p M (fun x => z x - z' x) x) x := by
      rw [e2, e1, e3]
      simp only [hT]
      ring
    rw [key, norm_neg]
    have hr2 := norm_linSol_le hp hM (by positivity) hres x
    calc _ ≤ Kap p * (2 * η * D) := hr2
      _ = D / 2 := by rw [hη]; field_simp; ring
  -- `T 0` is small
  have hT0 : ∀ x, ‖T 0 x‖ ≤ r / 2 := by
    intro x
    have hb : ∀ x, ‖Phi p M ξ ε 0 x‖ ≤ 2 * τ := fun x => by
      rw [Phi_zero_eq hM]
      have hq : ∀ x', ‖Qmap p (ε • ξ x', 0) - Qmap p (0, 0)‖ ≤ τ := fun x' => by
        have h := hQc (x := ε • ξ x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have hn : ∀ x', ‖Nmap p (ε • ξ x', 0) - Nmap p (0, 0)‖ ≤ τ := fun x' => by
        have h := hNc (x := ε • ξ x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ τ + τ := add_le_add (hq x) (Mv_norm_le hM hτ0.le hn x)
        _ = 2 * τ := by ring
    have h := norm_linSol_le hp hM (by positivity) hb x
    simp only [hT, Pi.zero_apply, zero_sub, norm_neg]
    calc _ ≤ Kap p * (2 * τ) := h
      _ = r / 2 := by rw [hτ]; field_simp; ring
  have hball : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖T z x‖ ≤ r := by
    intro z hz x
    have h1 := hcontr z 0 hz (fun x => by simp [hr.le]) r (fun x => by simpa using hz x) x
    calc ‖T z x‖ ≤ ‖T z x - T 0 x‖ + ‖T 0 x‖ := by
          have := norm_add_le (T z x - T 0 x) (T 0 x); simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add h1 (hT0 x)
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → X → Fin 4 → ℝ := fun n => T^[n] 0 with hzs
  have hzsB : ∀ n x, ‖zs n x‖ ≤ r := by
    intro n
    induction n with
    | zero => intro x; simp [hzs, hr.le]
    | succ n ih =>
      intro x
      simp only [hzs, Function.iterate_succ_apply']
      exact hball _ ih x
  have hstep : ∀ n x, ‖zs n x - zs (n + 1) x‖ ≤ r / 2 / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hT0 x
    | succ n ih =>
      intro x
      have h := hcontr (zs (n + 1)) (zs n) (hzsB _) (hzsB _) (r / 2 / 2 ^ n)
        (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (n + 1 + 1) = T (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) x = T (zs n) x from congrFun e2 x]
      calc _ ≤ r / 2 / 2 ^ n / 2 := h
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun n => zs n x := fun x =>
    cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hstep n x
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzdist : ∀ n x, ‖zs n x - z x‖ ≤ r / 2 ^ n := fun n x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n x)
      (fun n => by rw [dist_eq_norm]; exact hstep n x) (hz x) n
    rwa [dist_eq_norm] at this
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x =>
    le_of_tendsto' ((hz x).norm) fun n => hzsB n x
  -- `z` is a fixed point of `T`
  have hfix : T z = z := by
    funext x
    have hlim : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (T z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => r / 2 ^ n / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hcontr z (zs n) hzB (hzsB n) (r / 2 ^ n) (fun x => by
        rw [norm_sub_rev]; exact hzdist n x) x
    have hlim2 : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (z x)) :=
      (hz x).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hlim hlim2
  refine ⟨z, hzB, ?_⟩
  -- the fixed point solves `Φ = 0`
  have hl : linSol p M (Phi p M ξ ε z) = 0 := by
    funext x
    have := congrFun hfix x
    simp only [hT] at this
    have h2 : linSol p M (Phi p M ξ ε z) x = 0 := by
      have := congrArg (fun v => z x - v) this
      simp only [sub_sub_cancel, sub_self] at this
      exact this
    exact h2
  obtain ⟨-, hL⟩ := linSol_spec hp hM (hCQN z hzB) (hPhiB z hzB)
  unfold IsMarkovEqm
  rw [← hL, hl]
  funext x
  have := congrFun (Lop_sub (p := p) M (0 : X → Fin 4 → ℝ) 0) x
  simp only [Pi.zero_apply, sub_self] at this
  exact this

/-- Woodford (2003), Ch. 6, §1, App. A.3 and Proposition 4.3 (**EXISTENCE AND LOCAL UNIQUENESS OF
A MARKOV EQUILIBRIUM ON A GENERAL SHOCK SPACE**). Under the Taylor principle there are `r, δ > 0`,
depending ONLY on the parameters, such that for every state space `X`, every Markov operator
`M` (`E_t[h(x_{t+1})] = (Mh)(x_t)`) and every bounded disturbance pattern with `‖εξ(x)‖ ≤ δ`,
there is exactly one Markov equilibrium `z : X → ℝ⁴` with `‖z(x)‖ ≤ r` for all `x`. -/
theorem markov_equilibrium_general (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (ξ : X → Fin 5 → ℝ) (ε : ℝ), (∀ x, ‖ε • ξ x‖ ≤ δ) →
        ∃ z : X → Fin 4 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ IsMarkovEqm p M ξ ε z) ∧
          ∀ z' : X → Fin 4 → ℝ, (∀ x, ‖z' x‖ ≤ r) → IsMarkovEqm p M ξ ε z' → z' = z := by
  obtain ⟨ρ, hρ, huniq⟩ := uniform_uniqueness hp
  obtain ⟨r0, hr0, hex⟩ := general_existence hp
  obtain ⟨δ1, hδ1, hex1⟩ := hex (min r0 ρ) (lt_min hr0 hρ) (min_le_left _ _)
  refine ⟨min r0 ρ, lt_min hr0 hρ, min δ1 ρ, lt_min hδ1 hρ, fun X M hM ξ ε hξ => ?_⟩
  obtain ⟨z, hzB, hz⟩ := hex1 X M hM ξ ε fun x => (hξ x).trans (min_le_left _ _)
  refine ⟨z, ⟨hzB, hz⟩, fun z' hz'B hz' => huniq X M hM ξ ε z' z
    (fun x => (hξ x).trans (min_le_right _ _)) (fun x => (hz'B x).trans (min_le_right _ _))
    (fun x => (hzB x).trans (min_le_right _ _)) hz' hz⟩

/-! ## First- and second-order accuracy on a general state space (Layer B) -/

/-- Woodford (2003), §1, eq. (1.2) (**a uniform second-order Taylor bound**): for a `C²` map `g` on
a finite-dimensional space, `‖g(q) − g(0) − Dg(0)q‖ ≤ C‖q‖²` for `‖q‖ ≤ 1`. -/
theorem taylor2_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
    (hg : ContDiff ℝ 2 g) :
    ∃ C, 0 ≤ C ∧ ∀ q, ‖q‖ ≤ 1 → ‖g q - g 0 - fderiv ℝ g 0 q‖ ≤ C * ‖q‖ ^ 2 := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    (hg1.continuous_fderiv one_ne_zero).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Metric.mem_closedBall_self zero_le_one))
  have hlip : ∀ u ∈ Metric.closedBall (0 : E) 1, ‖fderiv ℝ g u - fderiv ℝ g 0‖ ≤ C * ‖u‖ :=
    fun u hu => by
      have := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
        (fun x _ => (hg1.differentiable one_ne_zero) x) hC
        (Metric.mem_closedBall_self zero_le_one) hu
      simpa using this
  refine ⟨C, hC0, fun q hq => ?_⟩
  set s := Metric.closedBall (0 : E) ‖q‖
  have hs1 : s ⊆ Metric.closedBall 0 1 := Metric.closedBall_subset_closedBall hq
  have hd : ∀ u ∈ s, HasFDerivWithinAt (fun u => g u - fderiv ℝ g 0 u)
      (fderiv ℝ g u - fderiv ℝ g 0) s u := fun u _ =>
    (((hg.differentiable (by norm_num)) u).hasFDerivAt.sub
      (fderiv ℝ g 0).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ u ∈ s, ‖fderiv ℝ g u - fderiv ℝ g 0‖ ≤ C * ‖q‖ := fun u hu => by
    refine (hlip u (hs1 hu)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    simpa [s] using hu
  have h0s : (0 : E) ∈ s := Metric.mem_closedBall_self (norm_nonneg q)
  have hqs : q ∈ s := by simp [s]
  have := (convex_closedBall (0 : E) ‖q‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb
    h0s hqs
  simp only [map_zero, sub_zero] at this
  calc ‖g q - g 0 - fderiv ℝ g 0 q‖ = ‖g q - fderiv ℝ g 0 q - g 0‖ := by congr 1; abel
    _ ≤ C * ‖q‖ * ‖q‖ := this
    _ = C * ‖q‖ ^ 2 := by ring

/-- `DQ_e` is homogeneous. -/
theorem DQe_smul (c : ℝ) (e : Fin 5 → ℝ) : DQe p (c • e) = c • DQe p e := by
  funext i; fin_cases i <;> simp [DQe] <;> ring

/-- `DN_e` is homogeneous. -/
theorem DNe_smul (c : ℝ) (e : Fin 5 → ℝ) : DNe p (c • e) = c • DNe p e := by
  funext i; fin_cases i <;> simp [DNe]
  ring

/-- Woodford (2003), App. A.3: the derivative of `Q` at the steady state in the direction
`(e, w)` is `DQ_e e + DQ w`. -/
theorem fderiv_Qmap_split (e : Fin 5 → ℝ) (w : Fin 4 → ℝ) :
    fderiv ℝ (Qmap p) (0, 0) (e, w) = DQe p e + DQ0 p w := by
  have hd : HasFDerivAt (Qmap p) (fderiv ℝ (Qmap p) (0, 0)) (0, 0) :=
    ((contDiff_Qmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => (t • e, (0 : Fin 4 → ℝ))) (e, 0) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).prodMk (hasDerivAt_const (0 : ℝ)
      (0 : Fin 4 → ℝ))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have he : fderiv ℝ (Qmap p) (0, 0) (e, 0) = DQe p e :=
    hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Qmap_eps e i)
  rw [show (e, w) = (e, (0 : Fin 4 → ℝ)) + ((0 : Fin 5 → ℝ), w) by simp, map_add, he,
    fderiv_Qmap_inr]

/-- Woodford (2003), App. A.3: the derivative of `N` at the steady state in the direction
`(e, w)` is `DN_e e + DN w`. -/
theorem fderiv_Nmap_split (e : Fin 5 → ℝ) (w : Fin 4 → ℝ) :
    fderiv ℝ (Nmap p) (0, 0) (e, w) = DNe p e + DN0 p w := by
  have hd : HasFDerivAt (Nmap p) (fderiv ℝ (Nmap p) (0, 0)) (0, 0) :=
    ((contDiff_Nmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => (t • e, (0 : Fin 4 → ℝ))) (e, 0) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).prodMk (hasDerivAt_const (0 : ℝ)
      (0 : Fin 4 → ℝ))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have he : fderiv ℝ (Nmap p) (0, 0) (e, 0) = DNe p e :=
    hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Nmap_eps e i)
  rw [show (e, w) = (e, (0 : Fin 4 → ℝ)) + ((0 : Fin 5 → ℝ), w) by simp, map_add, he,
    fderiv_Nmap_inr]

/-- `Mv` of a constant is the constant. -/
theorem Mv_const {n : ℕ} {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) (c : Fin n → ℝ) (x : X) :
    Mv M (fun _ => c) x = c := by
  funext i
  simp only [Mv]
  have : (fun _ : X => c i) = c i • fun _ => (1 : ℝ) := by funext; simp
  rw [this, map_smul, hM.1]; simp

/-- `Mv` is homogeneous. -/
theorem Mv_smul {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (c : ℝ) (h : X → Fin n → ℝ) (x : X) :
    Mv M (fun x' => c • h x') x = c • Mv M h x := by
  funext i
  simp only [Mv, Pi.smul_apply]
  have : (fun x' => c • h x' i) = c • fun x' => h x' i := rfl
  rw [this, map_smul]; rfl

/-- Woodford (2003), App. A.3: the linearised operator is homogeneous. -/
theorem Lop_smul (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (c : ℝ) (v : X → Fin 4 → ℝ) :
    Lop p M (fun x => c • v x) = fun x => c • Lop p M v x := by
  have hq : ∀ a : Fin 4 → ℝ, DQ0 p (c • a) = c • DQ0 p a := fun a => by
    funext i; fin_cases i <;> simp [DQ0] <;> ring
  have hn : ∀ a : Fin 4 → ℝ, DN0 p (c • a) = c • DN0 p a := fun a => by
    funext i; fin_cases i <;> simp [DN0] <;> ring
  funext x
  simp only [Lop, hq, hn, Mv_smul, smul_add]

/-- Woodford (2003), App. A.3: the derivative of the residual in the amplitude on a general state
space, `(∂Φ/∂ε)(x) = DQ_e ξ(x) + M[DN_e ξ](x)`. -/
noncomputable def DepsG (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (ξ : X → Fin 5 → ℝ) :
    X → Fin 4 → ℝ :=
  fun x => DQe p (ξ x) + Mv M (fun x' => DNe p (ξ x')) x

/-- Woodford (2003), (1.2) applied to the conditions (**the second-order expansion of the
residual**): `Φ(ε, z) = εDΦ_ε + Lz + R`, `R = R_Q + M[R_N]` with
`R_Q(x) = Q(εξ(x), z(x)) − Q(0) − DQ(0)(εξ(x), z(x))` and `R_N` likewise. -/
theorem Phi_expand {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) (ξ : X → Fin 5 → ℝ) (ε : ℝ)
    (z : X → Fin 4 → ℝ) (x : X) :
    Phi p M ξ ε z x = (ε • DepsG p M ξ x + Lop p M z x) +
      ((Qmap p (ε • ξ x, z x) - Qmap p (0, 0) - fderiv ℝ (Qmap p) (0, 0) (ε • ξ x, z x)) +
        Mv M (fun x' => Nmap p (ε • ξ x', z x') - Nmap p (0, 0) -
          fderiv ℝ (Nmap p) (0, 0) (ε • ξ x', z x')) x) := by
  have h0 : Qmap p (0, 0) + Nmap p (0, 0) = 0 := by
    funext i; fin_cases i <;> simp [Qmap, Nmap]
  have m1 := congrFun (Mv_sub M (fun x' => Nmap p (ε • ξ x', z x') - Nmap p (0, 0))
    (fun x' => fderiv ℝ (Nmap p) (0, 0) (ε • ξ x', z x'))) x
  have m2 := congrFun (Mv_sub M (fun x' => Nmap p (ε • ξ x', z x'))
    (fun _ => Nmap p (0, 0))) x
  have m3 : Mv M (fun x' => fderiv ℝ (Nmap p) (0, 0) (ε • ξ x', z x')) x =
      ε • Mv M (fun x' => DNe p (ξ x')) x + Mv M (fun x' => DN0 p (z x')) x := by
    simp only [fderiv_Nmap_split, DNe_smul]
    have := congrFun (Mv_add M (fun x' => ε • DNe p (ξ x')) (fun x' => DN0 p (z x'))) x
    rw [this, Mv_smul]
  rw [m1, m2, m3, Mv_const hM, fderiv_Qmap_split, DQe_smul]
  simp only [Phi, DepsG, Lop, smul_add]
  linear_combination (norm := abel_nf) h0

/-- Woodford (2003), §1 and App. A.3 (**size and first-order accuracy on a general state space**).
Under the Taylor principle there are `r₁ > 0` and constants `K₁, K₂`, depending ONLY on the
parameters, such that on every state space with every Markov operator, for disturbances with
`‖ξ‖ ≤ Ξ` and `|ε|Ξ ≤ r₁`, every Markov equilibrium with `‖z‖ ≤ r₁` satisfies
`‖z‖ ≤ K₁|ε|Ξ` and `‖z − εz₁‖ ≤ K₂(|ε|Ξ)²` with `z₁ = L⁻¹(−∂Φ/∂ε)` (the log-linear Markov
solution). -/
theorem second_order_general (hp : p.Std) :
    ∃ r1 > 0, ∃ K1 K2 : ℝ, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (ξ : X → Fin 5 → ℝ) (Ξ : ℝ), 0 ≤ Ξ → (∀ x, ‖ξ x‖ ≤ Ξ) → ∀ (ε : ℝ)
        (z : X → Fin 4 → ℝ), |ε| * Ξ ≤ r1 → (∀ x, ‖z x‖ ≤ r1) → IsMarkovEqm p M ξ ε z →
          (∀ x, ‖z x‖ ≤ K1 * (|ε| * Ξ)) ∧
          ∀ x, ‖z x - ε • linSol p M (fun x => -DepsG p M ξ x) x‖ ≤ K2 * (|ε| * Ξ) ^ 2 := by
  obtain ⟨CQ, hCQ0, hCQ⟩ := taylor2_bound (contDiff_Qmap (p := p) (n := 2))
  obtain ⟨CN, hCN0, hCN⟩ := taylor2_bound (contDiff_Nmap (p := p) (n := 2))
  have hK := Kap_pos hp
  set C2 := CQ + CN with hC2
  have hC20 : 0 ≤ C2 := add_nonneg hCQ0 hCN0
  set Lq := ‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖ with hLq
  have hLq0 : 0 ≤ Lq := by positivity
  set r1 := min (1 / 2) (1 / (16 * Kap p * C2 + 1)) with hr1
  have hr10 : 0 < r1 := lt_min (by norm_num) (by positivity)
  set K1 := 2 * Kap p * Lq + 1 with hK1
  have hK10 : 0 ≤ K1 := by positivity
  refine ⟨r1, hr10, K1, Kap p * C2 * (1 + K1) ^ 2, fun X M hM ξ Ξ hΞ hξ ε z hεΞ hz hE => ?_⟩
  have hεξ : ∀ x, ‖ε • ξ x‖ ≤ |ε| * Ξ := fun x => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hξ x) (abs_nonneg _)
  have hmax : ∀ x, ‖(ε • ξ x, z x)‖ ≤ |ε| * Ξ + ‖z x‖ := fun x => by
    rw [Prod.norm_def]
    exact max_le ((hεξ x).trans (le_add_of_nonneg_right (norm_nonneg _)))
      (le_add_of_nonneg_left (by positivity))
  have hr11 : r1 ≤ 1 / 2 := min_le_left _ _
  have hin : ∀ x, ‖(ε • ξ x, z x)‖ ≤ 1 := fun x => (hmax x).trans (by linarith [hz x])
  -- the remainder
  set R : X → Fin 4 → ℝ := fun x =>
    (Qmap p (ε • ξ x, z x) - Qmap p (0, 0) - fderiv ℝ (Qmap p) (0, 0) (ε • ξ x, z x)) +
      Mv M (fun x' => Nmap p (ε • ξ x', z x') - Nmap p (0, 0) -
        fderiv ℝ (Nmap p) (0, 0) (ε • ξ x', z x')) x with hR
  have hRb : ∀ Z, (∀ x, ‖z x‖ ≤ Z) → ∀ x, ‖R x‖ ≤ C2 * (|ε| * Ξ + Z) ^ 2 := by
    intro Z hZ x
    have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ x)
    have hq : ∀ x, ‖(ε • ξ x, z x)‖ ^ 2 ≤ (|ε| * Ξ + Z) ^ 2 := fun x =>
      pow_le_pow_left₀ (norm_nonneg _) ((hmax x).trans (by linarith [hZ x])) 2
    have e1 := (hCQ _ (hin x)).trans (mul_le_mul_of_nonneg_left (hq x) hCQ0)
    have e2 := Mv_norm_le hM (mul_nonneg hCN0 (sq_nonneg (|ε| * Ξ + Z)))
      (fun x' => (hCN _ (hin x')).trans (mul_le_mul_of_nonneg_left (hq x') hCN0)) x
    calc ‖R x‖ ≤ _ := norm_add_le _ _
      _ ≤ CQ * (|ε| * Ξ + Z) ^ 2 + CN * (|ε| * Ξ + Z) ^ 2 := add_le_add e1 e2
      _ = C2 * (|ε| * Ξ + Z) ^ 2 := by ring
  have hLz : ∀ x, Lop p M z x = -(ε • DepsG p M ξ x) - R x := fun x => by
    have h := Phi_expand (p := p) hM ξ ε z x
    rw [congrFun hE x] at h
    simp only [Pi.zero_apply] at h
    have hRx : R x = (Qmap p (ε • ξ x, z x) - Qmap p (0, 0) -
        fderiv ℝ (Qmap p) (0, 0) (ε • ξ x, z x)) + Mv M (fun x' => Nmap p (ε • ξ x', z x') -
          Nmap p (0, 0) - fderiv ℝ (Nmap p) (0, 0) (ε • ξ x', z x')) x := rfl
    rw [← hRx] at h
    calc Lop p M z x = (ε • DepsG p M ξ x + Lop p M z x + R x) - ε • DepsG p M ξ x - R x := by
          abel
      _ = -(ε • DepsG p M ξ x) - R x := by rw [← h]; abel
  have hDb : ∀ x, ‖DepsG p M ξ x‖ ≤ Lq * Ξ := fun x => by
    have hq : ∀ e, ‖DQe p e‖ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * ‖e‖ := fun e => by
      have h := (fderiv ℝ (Qmap p) (0, 0)).le_opNorm (e, 0)
      rw [fderiv_Qmap_split, show DQ0 p 0 = 0 by funext i; fin_cases i <;> simp [DQ0],
        add_zero] at h
      simpa [Prod.norm_def] using h
    have hn : ∀ e, ‖DNe p e‖ ≤ ‖fderiv ℝ (Nmap p) (0, 0)‖ * ‖e‖ := fun e => by
      have h := (fderiv ℝ (Nmap p) (0, 0)).le_opNorm (e, 0)
      rw [fderiv_Nmap_split, show DN0 p 0 = 0 by funext i; fin_cases i <;> simp [DN0],
        add_zero] at h
      simpa [Prod.norm_def] using h
    have e2 := Mv_norm_le hM (mul_nonneg (norm_nonneg _) hΞ) (fun x' => (hn (ξ x')).trans
      (mul_le_mul_of_nonneg_left (hξ x') (norm_nonneg _))) x
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * Ξ + ‖fderiv ℝ (Nmap p) (0, 0)‖ * Ξ :=
        add_le_add ((hq _).trans (mul_le_mul_of_nonneg_left (hξ x) (norm_nonneg _))) e2
      _ = Lq * Ξ := by ring
  -- size
  have hsize : ∀ x, ‖z x‖ ≤ K1 * (|ε| * Ξ) := by
    have himp : ∀ U, (∀ x, ‖z x‖ ≤ U) → ∀ x,
        ‖z x‖ ≤ (Kap p * Lq + 1 / 2) * (|ε| * Ξ) + 1 / 2 * U := by
      intro U hU x
      have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU x)
      set Z := min U r1
      have hZ : ∀ x, ‖z x‖ ≤ Z := fun x => le_min (hU x) (hz x)
      have hZ0 : 0 ≤ Z := le_min hU0 hr10.le
      have hb : ∀ x, ‖Lop p M z x‖ ≤ |ε| * (Lq * Ξ) + C2 * (|ε| * Ξ + Z) ^ 2 := fun x => by
        rw [hLz]
        calc _ ≤ ‖ε • DepsG p M ξ x‖ + ‖R x‖ := by
              have := norm_sub_le (-(ε • DepsG p M ξ x)) (R x); rwa [norm_neg] at this
          _ ≤ _ := by
              rw [norm_smul, Real.norm_eq_abs]
              exact add_le_add (mul_le_mul_of_nonneg_left (hDb x) (abs_nonneg _)) (hRb Z hZ x)
      have h := apriori hp hM hz hb x
      have hsq : C2 * (|ε| * Ξ + Z) ^ 2 ≤ 1 / (8 * Kap p) * (|ε| * Ξ + Z) := by
        have hs : |ε| * Ξ + Z ≤ 2 * r1 := by linarith [min_le_right U r1]
        have hr1' : r1 ≤ 1 / (16 * Kap p * C2 + 1) := min_le_right _ _
        have hpos : 0 ≤ |ε| * Ξ + Z := by positivity
        have h16 : 0 < 16 * Kap p * C2 + 1 := by positivity
        have hr1m : r1 * (16 * Kap p * C2 + 1) ≤ 1 := by
          rw [← le_div_iff₀ h16]; exact hr1'
        have : C2 * (|ε| * Ξ + Z) ≤ 1 / (8 * Kap p) := by
          rw [le_div_iff₀ (by positivity)]
          have e1 : C2 * (|ε| * Ξ + Z) ≤ C2 * (2 * r1) := mul_le_mul_of_nonneg_left hs hC20
          have e2 : 0 ≤ Kap p * C2 * r1 := by positivity
          nlinarith
        calc C2 * (|ε| * Ξ + Z) ^ 2 = (C2 * (|ε| * Ξ + Z)) * (|ε| * Ξ + Z) := by ring
          _ ≤ 1 / (8 * Kap p) * (|ε| * Ξ + Z) := mul_le_mul_of_nonneg_right this hpos
      calc ‖z x‖ ≤ Kap p * (|ε| * (Lq * Ξ) + C2 * (|ε| * Ξ + Z) ^ 2) := h
        _ ≤ Kap p * (|ε| * (Lq * Ξ) + 1 / (8 * Kap p) * (|ε| * Ξ + Z)) :=
            mul_le_mul_of_nonneg_left (by linarith) hK.le
        _ = Kap p * Lq * (|ε| * Ξ) + 1 / 8 * (|ε| * Ξ) + 1 / 8 * Z := by field_simp; ring
        _ ≤ (Kap p * Lq + 1 / 2) * (|ε| * Ξ) + 1 / 2 * U := by
            have : Z ≤ U := min_le_left _ _
            nlinarith [abs_nonneg ε]
    intro x
    have h := bound_of_improve (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hz himp x
    calc ‖z x‖ ≤ (Kap p * Lq + 1 / 2) * (|ε| * Ξ) / (1 - 1 / 2) := h
      _ = K1 * (|ε| * Ξ) := by rw [hK1]; ring
  refine ⟨hsize, fun x => ?_⟩
  -- second order
  have hD0 : 0 ≤ Lq * Ξ := mul_nonneg hLq0 hΞ
  have hnD : ∀ x, ‖-DepsG p M ξ x‖ ≤ Lq * Ξ := fun x => by rw [norm_neg]; exact hDb x
  obtain ⟨⟨C1, hC1⟩, hL1⟩ := linSol_spec hp hM hD0 hnD
  set z1 := linSol p M (fun x => -DepsG p M ξ x)
  have hdB : ∀ x, ‖z x - ε • z1 x‖ ≤ r1 + |ε| * C1 := fun x => by
    refine (norm_sub_le _ _).trans (add_le_add (hz x) ?_)
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hC1 x) (abs_nonneg _)
  have hLd : ∀ x, Lop p M (fun x => z x - ε • z1 x) x = -R x := fun x => by
    rw [Lop_sub, Lop_smul, hL1]
    simp only [hLz]
    simp only [smul_neg]
    abel
  have hRb2 : ∀ x, ‖R x‖ ≤ C2 * (1 + K1) ^ 2 * (|ε| * Ξ) ^ 2 := fun x => by
    have := hRb (K1 * (|ε| * Ξ)) hsize x
    calc _ ≤ _ := this
      _ = _ := by ring
  have := apriori hp hM hdB (a := C2 * (1 + K1) ^ 2 * (|ε| * Ξ) ^ 2)
    (fun x => by rw [hLd, norm_neg]; exact hRb2 x) x
  calc _ ≤ _ := this
    _ = _ := by ring

/-- Woodford (2003), Ch. 6, §1 and §2, p. 394 (**the Layer-B family hypothesis discharged on a
GENERAL state space**). Under the Taylor principle there is `r > 0` such that for every state
space, Markov operator and bounded disturbance pattern `‖ξ‖ ≤ Ξ` there are `δ > 0` and a family
`ε ↦ z_ε` with: for `|ε| ≤ δ`, `z_ε` is the unique Markov equilibrium within `r`; and along ANY
path `x_t(ω)` of the state the processes `z_ε(x_t)ᵢ` are `O(ε)` and
`z_ε(x_t)ᵢ − εz₁(x_t)ᵢ = O(ε²)` uniformly in `(t, ω)` (`BridgeExtensions.UProc`), with
`z₁ = L⁻¹(−∂Φ/∂ε)` bounded. -/
theorem layerB_general (hp : p.Std) :
    ∃ r > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (ξ : X → Fin 5 → ℝ) (Ξ : ℝ), 0 ≤ Ξ → (∀ x, ‖ξ x‖ ≤ Ξ) →
        ∃ δ > 0, ∃ z : ℝ → X → Fin 4 → ℝ,
          (∀ ε, |ε| ≤ δ → ((∀ x, ‖z ε x‖ ≤ r) ∧ IsMarkovEqm p M ξ ε (z ε)) ∧
            ∀ z' : X → Fin 4 → ℝ, (∀ x, ‖z' x‖ ≤ r) → IsMarkovEqm p M ξ ε z' → z' = z ε) ∧
          ∀ (Ω : Type*) (xs : ℕ → Ω → X) (i : Fin 4),
            BridgeExtensions.UProc (𝓝 0) (fun ε t ω => z ε (xs t ω) i -
              ε * linSol p M (fun x => -DepsG p M ξ x) (xs t ω) i) (fun ε => ε ^ 2) ∧
            BridgeExtensions.UProc (𝓝 0) (fun ε t ω => z ε (xs t ω) i) (fun ε => ε ^ 1) := by
  obtain ⟨ru, hru, δu, hδu, hu⟩ := markov_equilibrium_general hp
  obtain ⟨r1, hr1, K1, K2, hso⟩ := second_order_general hp
  obtain ⟨r0, hr0, hex⟩ := general_existence hp
  set ρ' := min r1 (min ru r0) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hr1 (lt_min hru hr0)
  obtain ⟨δe, hδe, hexe⟩ := hex ρ' hρ'0 ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ru, hru, fun X M hM ξ Ξ hΞ hξ => ?_⟩
  set δ := min δe (min δu r1) / (Ξ + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hsmall : ∀ ε, |ε| ≤ δ → |ε| * Ξ ≤ min δe (min δu r1) := fun ε hε => by
    have h1 : |ε| * (Ξ + 1) ≤ min δe (min δu r1) := by
      rw [hδ, le_div_iff₀ (by positivity)] at hε; exact hε
    nlinarith [abs_nonneg ε]
  have hεξ : ∀ ε, |ε| ≤ δ → ∀ x, ‖ε • ξ x‖ ≤ |ε| * Ξ := fun ε _ x => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hξ x) (abs_nonneg _)
  have H : ∀ ε : ℝ, ∃ w : X → Fin 4 → ℝ, |ε| ≤ δ → (∀ x, ‖w x‖ ≤ ρ') ∧ IsMarkovEqm p M ξ ε w :=
    fun ε => by
      by_cases hε : |ε| ≤ δ
      · obtain ⟨w, hw⟩ := hexe X M hM ξ ε fun x =>
          (hεξ ε hε x).trans ((hsmall ε hε).trans (min_le_left _ _))
        exact ⟨w, fun _ => hw⟩
      · exact ⟨0, fun h => absurd h hε⟩
  choose z hz using H
  have hzr : ∀ ε, |ε| ≤ δ → ∀ x, ‖z ε x‖ ≤ ru := fun ε hε x =>
    ((hz ε hε).1 x).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbound : ∀ ε, |ε| ≤ δ → ∀ x,
      ‖z ε x - ε • linSol p M (fun x => -DepsG p M ξ x) x‖ ≤ K2 * Ξ ^ 2 * ε ^ 2 := by
    intro ε hε x
    have h := (hso X M hM ξ Ξ hΞ hξ ε (z ε)
      ((hsmall ε hε).trans ((min_le_right _ _).trans (min_le_right _ _)))
      (fun x => ((hz ε hε).1 x).trans (min_le_left _ _)) (hz ε hε).2).2 x
    calc _ ≤ K2 * (|ε| * Ξ) ^ 2 := h
      _ = K2 * Ξ ^ 2 * ε ^ 2 := by rw [mul_pow, sq_abs]; ring
  refine ⟨δ, hδ0, z, fun ε hε => ⟨⟨hzr ε hε, (hz ε hε).2⟩, fun z' hz' hE' =>
    (hu X M hM ξ ε fun x => (hεξ ε hε x).trans ((hsmall ε hε).trans
      ((min_le_right _ _).trans (min_le_left _ _)))).choose_spec.2 z' hz' hE' |>.trans
    ((hu X M hM ξ ε fun x => (hεξ ε hε x).trans ((hsmall ε hε).trans
      ((min_le_right _ _).trans (min_le_left _ _)))).choose_spec.2 (z ε) (hzr ε hε)
        (hz ε hε).2).symm⟩, fun Ω xs i => ?_⟩
  have hD0 : 0 ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖ := by positivity
  obtain ⟨⟨C1, hC1⟩, -⟩ := linSol_spec hp hM (r := fun x => -DepsG p M ξ x)
    (a := (‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖) * Ξ)
    (mul_nonneg hD0 hΞ) fun x => by
      rw [norm_neg]
      have hq : ∀ e, ‖DQe p e‖ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * ‖e‖ := fun e => by
        have h := (fderiv ℝ (Qmap p) (0, 0)).le_opNorm (e, 0)
        rw [fderiv_Qmap_split, show DQ0 p 0 = 0 by funext i; fin_cases i <;> simp [DQ0],
          add_zero] at h
        simpa [Prod.norm_def] using h
      have hn : ∀ e, ‖DNe p e‖ ≤ ‖fderiv ℝ (Nmap p) (0, 0)‖ * ‖e‖ := fun e => by
        have h := (fderiv ℝ (Nmap p) (0, 0)).le_opNorm (e, 0)
        rw [fderiv_Nmap_split, show DN0 p 0 = 0 by funext i; fin_cases i <;> simp [DN0],
          add_zero] at h
        simpa [Prod.norm_def] using h
      have e2 := Mv_norm_le hM (mul_nonneg (norm_nonneg _) hΞ) (fun x' => (hn (ξ x')).trans
        (mul_le_mul_of_nonneg_left (hξ x') (norm_nonneg _))) x
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ ‖fderiv ℝ (Qmap p) (0, 0)‖ * Ξ + ‖fderiv ℝ (Nmap p) (0, 0)‖ * Ξ :=
          add_le_add ((hq _).trans (mul_le_mul_of_nonneg_left (hξ x) (norm_nonneg _))) e2
        _ = _ := by ring
  set z1 := linSol p M (fun x => -DepsG p M ξ x)
  have hfirst : BridgeExtensions.UProc (𝓝 0) (fun ε t ω => z ε (xs t ω) i -
      ε * z1 (xs t ω) i) (fun ε => ε ^ 2) := by
    refine IsBigO.of_bound (K2 * Ξ ^ 2) ?_
    have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| ≤ δ := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ0] with ε hε
      simpa [Real.dist_eq] using hε
    filter_upwards [hev.prod_inl ⊤] with q hq
    have h1 := norm_le_pi_norm (z q.1 (xs q.2.1 q.2.2) - q.1 • z1 (xs q.2.1 q.2.2)) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q.1)]
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hbound q.1 hq _)
  refine ⟨hfirst, BridgeExtensions.first_order_o (e := fun ε : ℝ => ε) tendsto_id
    ⟨C1, fun t ω => ?_⟩ hfirst⟩
  have := norm_le_pi_norm (z1 (xs t ω)) i
  rw [Real.norm_eq_abs] at this
  exact this.trans (hC1 _)

/-! ## A continuous-state instance: finitely many successors, the AR(1) -/

/-- Woodford (2003), App. A.3: the Markov operator of a random map with finitely many outcomes,
`(Mh)(x) = ∑ⱼ wⱼ h(fⱼ(x))` (the state `x′ = fⱼ(x)` with probability `wⱼ`). -/
noncomputable def ifsOp {m : ℕ} (w : Fin m → ℝ) (f : Fin m → X → X) : (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun h x := ∑ j, w j * h (f j x)
  map_add' h k := by funext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c h := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Woodford (2003), App. A.3: with probability weights, `ifsOp` is a Markov operator. -/
theorem ifsOp_isMarkov {m : ℕ} {w : Fin m → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (f : Fin m → X → X) : IsMarkov (ifsOp w f) := by
  refine ⟨?_, fun h C hC x => ?_⟩
  · funext x; simp [ifsOp, hw1]
  · change |∑ j, w j * h (f j x)| ≤ C
    calc |∑ j, w j * h (f j x)| ≤ ∑ j, |w j * h (f j x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, w j * C := Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg (hw0 j)]
          exact mul_le_mul_of_nonneg_left (hC _) (hw0 j)
      _ = C := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The bounded AR(1) state space `{x : |x| ≤ B}`. -/
abbrev ARState (B : ℝ) : Type := {x : ℝ // |x| ≤ B}

/-- The AR(1) transition `x′ = ρx + eⱼ` stays in `|x| ≤ B` when `|eⱼ| ≤ (1 − |ρ|)B`. -/
noncomputable def arMap {m : ℕ} {ρ B : ℝ} (e : Fin m → ℝ) (he : ∀ j, |e j| ≤ (1 - |ρ|) * B)
    (j : Fin m) (x : ARState B) : ARState B :=
  ⟨ρ * x.1 + e j, by
    have h1 := abs_add_le (ρ * x.1) (e j)
    rw [abs_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left x.2 (abs_nonneg ρ)
    have h3 := he j
    linarith⟩

/-- Woodford (2003), Ch. 6, §1 and App. A.3 (**a continuous-state instance: the AR(1) with
bounded support**). The exogenous state follows `x′ = ρx + e` with `e = eⱼ` with probability `wⱼ`
on the interval `|x| ≤ B` (`|eⱼ| ≤ (1 − |ρ|)B`); the disturbances are `εx·c` for a direction
`c ∈ ℝ⁵`. Under the Taylor principle, for `|ε|` small there is exactly one Markov equilibrium
`z : [−B, B] → ℝ⁴` within `r` of the steady state. -/
theorem ar1_equilibrium (hp : p.Std) {m : ℕ} {w : Fin m → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) {ρ B : ℝ} (e : Fin m → ℝ) (he : ∀ j, |e j| ≤ (1 - |ρ|) * B)
    (c : Fin 5 → ℝ) :
    ∃ r > 0, ∃ δ > 0, ∀ ε, |ε| * (|B| * ‖c‖) ≤ δ →
      ∃ z : ARState B → Fin 4 → ℝ,
        ((∀ x, ‖z x‖ ≤ r) ∧ IsMarkovEqm p (ifsOp w (arMap e he)) (fun x => x.1 • c) ε z) ∧
        ∀ z' : ARState B → Fin 4 → ℝ, (∀ x, ‖z' x‖ ≤ r) →
          IsMarkovEqm p (ifsOp w (arMap e he)) (fun x => x.1 • c) ε z' → z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := markov_equilibrium_general hp
  refine ⟨r, hr, δ, hδ, fun ε hε => h (ARState B) _ (ifsOp_isMarkov hw0 hw1 _) _ ε fun x => ?_⟩
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  refine le_trans ?_ hε
  have := x.2
  have hB : |x.1| ≤ |B| := this.trans (le_abs_self B)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
    (abs_nonneg _)

/-! ## Sequence-space determinacy: uniqueness among ALL bounded processes -/

/-- Woodford (2003), App. A.3, (A.11) (**the conditional expectation as a Markov operator on
dates × states**): on `X = ℕ × Ω`, `(Mh)(t, ω) = E_t[h(t+1, ·)](ω)`. -/
noncomputable def seqOp {Ω : Type*} (𝔼 : ExpectationSystem Ω) :
    (ℕ × Ω → ℝ) →ₗ[ℝ] (ℕ × Ω → ℝ) where
  toFun h q := 𝔼.E q.1 (fun ω => h (q.1 + 1, ω)) q.2
  map_add' h k := by
    funext q
    change 𝔼.E q.1 ((fun ω => h (q.1 + 1, ω)) + fun ω => k (q.1 + 1, ω)) q.2 = _
    rw [map_add]; rfl
  map_smul' c h := by
    funext q
    change 𝔼.E q.1 (c • fun ω => h (q.1 + 1, ω)) q.2 = _
    rw [map_smul]; rfl

/-- Woodford (2003), App. A.3: the expectation operator on `ℕ × Ω` is a Markov operator (constants
are known; `|h| ≤ C ⇒ |E_t h| ≤ C`). -/
theorem seqOp_isMarkov {Ω : Type*} (𝔼 : ExpectationSystem Ω) : IsMarkov (seqOp 𝔼) := by
  refine ⟨?_, fun h C hC q => ?_⟩
  · funext q
    change 𝔼.E q.1 (fun _ => (1 : ℝ)) q.2 = 1
    rw [𝔼.const]
  · exact 𝔼.abs_E_le (fun ω => hC (q.1 + 1, ω)) q.1 q.2

/-- Woodford (2003), (A.11) (**the exact stochastic equilibrium conditions in sequence space**):
the process `z_t(ω)` with disturbances `e_t(ω)` satisfies, at every date and state,
`Q(e_t, z_t) + E_t[N(e_{t+1}, z_{t+1})] = 0` (the Euler equation with the rule, the Calvo
recursions, the price index). No Markov structure and no adaptedness are imposed. -/
def SeqEqm {Ω : Type*} (p : Par) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ)
    (z : ℕ → Ω → Fin 4 → ℝ) : Prop :=
  ∀ t ω, Qmap p (e t ω, z t ω) +
    (fun i => 𝔼.E t (fun ω' => Nmap p (e (t + 1) ω', z (t + 1) ω') i) ω) = 0

/-- The sequence-space conditions are the Markov conditions on `ℕ × Ω` with `seqOp`. -/
theorem seqEqm_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ)
    (z : ℕ → Ω → Fin 4 → ℝ) :
    SeqEqm p 𝔼 e z ↔
      IsMarkovEqm p (seqOp 𝔼) (fun q => e q.1 q.2) 1 (fun q => z q.1 q.2) := by
  constructor
  · intro h
    funext q
    simp only [Phi, one_smul, Pi.zero_apply]
    exact h q.1 q.2
  · intro h t ω
    have := congrFun h (t, ω)
    simp only [Phi, one_smul, Pi.zero_apply] at this
    exact this

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**SEQUENCE-SPACE DETERMINACY: uniqueness among
ALL bounded processes**). Under the Taylor principle there is `ρ > 0` such that for EVERY
expectation system and EVERY disturbance process with `‖e_t(ω)‖ ≤ ρ`, two solutions of the exact
stochastic equilibrium conditions with `‖z_t(ω)‖, ‖z′_t(ω)‖ ≤ ρ` coincide. Neither the Markov
property nor adaptedness is assumed. -/
theorem seq_uniqueness (hp : p.Std) :
    ∃ ρ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ)
      (z z' : ℕ → Ω → Fin 4 → ℝ), (∀ t ω, ‖e t ω‖ ≤ ρ) → (∀ t ω, ‖z t ω‖ ≤ ρ) →
        (∀ t ω, ‖z' t ω‖ ≤ ρ) → SeqEqm p 𝔼 e z → SeqEqm p 𝔼 e z' → z = z' := by
  obtain ⟨ρ, hρ, h⟩ := uniform_uniqueness hp
  refine ⟨ρ, hρ, fun Ω 𝔼 e z z' he hz hz' hE hE' => ?_⟩
  have := h (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼) (fun q => e q.1 q.2) 1
    (fun q => z q.1 q.2) (fun q => z' q.1 q.2) (fun q => by simpa using he q.1 q.2)
    (fun q => hz q.1 q.2) (fun q => hz' q.1 q.2) ((seqEqm_iff 𝔼 e z).1 hE)
    ((seqEqm_iff 𝔼 e z').1 hE')
  funext t ω
  exact congrFun this (t, ω)

/-- Woodford (2003), App. A.3 (**sequence-space existence**): for every expectation system and
every disturbance process with `‖e_t(ω)‖ ≤ δ`, a bounded solution of the exact stochastic
equilibrium conditions within `r` exists, and it is the only one within `r`. -/
theorem seq_existence (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ),
      (∀ t ω, ‖e t ω‖ ≤ δ) → ∃ z : ℕ → Ω → Fin 4 → ℝ, ((∀ t ω, ‖z t ω‖ ≤ r) ∧
        SeqEqm p 𝔼 e z) ∧ ∀ z' : ℕ → Ω → Fin 4 → ℝ, (∀ t ω, ‖z' t ω‖ ≤ r) →
          SeqEqm p 𝔼 e z' → z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := markov_equilibrium_general hp
  refine ⟨r, hr, δ, hδ, fun Ω 𝔼 e he => ?_⟩
  obtain ⟨z, ⟨hzB, hz⟩, hu⟩ := h (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼) (fun q => e q.1 q.2) 1
    (fun q => by simpa using he q.1 q.2)
  refine ⟨fun t ω => z (t, ω), ⟨fun t ω => hzB (t, ω), (seqEqm_iff 𝔼 e _).2 hz⟩,
    fun z' hz'B hz' => ?_⟩
  have := hu (fun q => z' q.1 q.2) (fun q => hz'B q.1 q.2) ((seqEqm_iff 𝔼 e z').1 hz')
  funext t ω; exact congrFun this (t, ω)

/-- Woodford (2003), App. A.3 (**the Markov equilibrium is the unique bounded process**): if the
expectation system follows a finite chain along `s_t(ω)` (`MarkovProp`) and `w` is a Markov
equilibrium of amplitude `ε`, then `w(s_t(ω))` solves the sequence-space conditions with
`e_t = εξ(s_t)`; hence every bounded solution within `ρ` of `seq_uniqueness` equals it. -/
theorem markov_is_process {S : Type*} [Fintype S] {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ)
    (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S) (hM : MarkovProp 𝔼 P sh) :
    SeqEqm p 𝔼 (fun t ω => ε • ξ (sh t ω)) (fun t ω => w (sh t ω)) := by
  intro t ω
  funext i
  have h := eqm_comp hw (sh t ω) i
  have hE := congrFun (hM t (fun s' => Nmap p (ε • ξ s', w s') i)) ω
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [hE]
  exact h

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**uniqueness of the Markov equilibrium among
ALL bounded stochastic processes**): with `ρ` of `seq_uniqueness`, if the expectation system
follows the chain, `w` is a Markov equilibrium with `‖w‖ ≤ ρ` and `‖εξ‖ ≤ ρ`, then every process
`z` with `‖z_t(ω)‖ ≤ ρ` solving the exact stochastic conditions is `z_t(ω) = w(s_t(ω))`. -/
theorem markov_is_unique_process (hp : p.Std) :
    ∃ ρ > 0, ∀ (S : Type*) [Fintype S] (Ω : Type*) (𝔼 : ExpectationSystem Ω)
      (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ)
      (sh : ℕ → Ω → S), IsMarkovEqm p (chainOp P) ξ ε w → MarkovProp 𝔼 P sh →
        (∀ s, ‖ε • ξ s‖ ≤ ρ) → (∀ s, ‖w s‖ ≤ ρ) → ∀ z : ℕ → Ω → Fin 4 → ℝ,
          (∀ t ω, ‖z t ω‖ ≤ ρ) → SeqEqm p 𝔼 (fun t ω => ε • ξ (sh t ω)) z →
            z = fun t ω => w (sh t ω) := by
  obtain ⟨ρ, hρ, h⟩ := seq_uniqueness hp
  exact ⟨ρ, hρ, fun S _ Ω 𝔼 P ξ ε w sh hw hM he hwB z hzB hz =>
    h Ω 𝔼 _ z _ (fun t ω => he _) hzB (fun t ω => hwB _) hz
      (markov_is_process 𝔼 ξ ε w hw sh hM)⟩

end Woodford.StabilizationWelfare.NonlinearNKMarkovGeneral
