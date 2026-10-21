/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Expectations
import GainsFromCommitment.Sequences

/-!
# Lagrangian sufficiency for discounted linear-quadratic problems

Woodford (2003), *Interest and Prices*, Chapter 7, §1.1, pp. 472–475 (the Lagrangian and the
first-order conditions (1.7)–(1.9)), §1.2, pp. 477–478 ((1.16)–(1.18)), §2.1, pp. 487–490 (the
stochastic Lagrangian (2.4) and conditions (2.5)–(2.6)), and Chapter 8, §1.1, pp. 536–540.

The book characterises optimal policy by writing a Lagrangian, taking first-order conditions and
solving them for their unique bounded solution, and then calls that solution optimal
("the only one satisfying the relevant transversality condition"). This module proves the
step the book omits: **first-order conditions plus feasibility imply optimality** (survey §4.4).

The problem: `n` variables `z_t = (z_{t,i})_{i ∈ ι}` and `m` constraints `k ∈ K`,

* loss `E_0 ∑_{t ≥ 0} βᵗ ∑_i w_i (z_{t,i} − z̄_{t,i})²` with weights `w_i ≥ 0`;
* constraints `∑_i (C_{k i} z_{t−1,i} + A_{k i} z_{t,i} + B_{k i} E_t z_{t+1,i}) = g_{t,k}`,
  `t ≥ 0`, with the initial values `z_{−1}` given (lags, current values and one-period-ahead
  expectations, the form of every constraint in Chapters 7–8);
* first-order conditions, with multipliers `φ_{t,k}` and an initial multiplier `φ_{−1,k}`:
  `w_i (z_{t,i} − z̄_{t,i}) + ∑_k (A_{k i} φ_{t,k} + β⁻¹ B_{k i} φ_{t−1,k} +
  β C_{k i} E_t φ_{t+1,k}) = 0`.

## Main results

* `expLoss_sub_hasSum` (**the Lagrangian identity**): for two bounded adapted feasible plans `z`
  and `z*`, where `z*` satisfies the first-order conditions with a bounded adapted multiplier,
  `E_0 L(z) − E_0 L(z*) = ∑ βᵗ E_0 ∑_i w_i (z_{t,i} − z*_{t,i})² −
    2β⁻¹ ∑_k E_0[φ_{−1,k} ∑_i B_{k i}(z_{0,i} − z*_{0,i})]`,
  a genuine convergent series (telescoping, with `E_0` interchanged with the infinite sum, the law
  of iterated expectations and the pull-out property).
* `expLoss_le_of_foc`, `isOptimalAmong_of_foc`, `isOptimal_of_foc_noInit`: hence `z*` minimises
  the expected loss, state by state, among all bounded adapted feasible plans that respect the
  initial commitment (automatically when `φ_{−1} = 0`).
* `eq_of_expLoss_eq`: strict convexity in the target variables: a plan with the same expected loss
  agrees with `z*` in conditional mean square on every coordinate with `w_i > 0`.
* `det_loss_le_of_foc`: the deterministic (perfect-foresight) version.
-/

namespace Woodford.GainsFromCommitment.LQSufficiency

open Filter Topology
open Sequences (lagged lagged_zero lagged_succ)

variable (Ω ι K : Type*)

/-- Woodford (2003), Ch. 7, §1.1, p. 472, §2.1, p. 489, and Ch. 8, §1.1, p. 536: a discounted
linear-quadratic problem with variables indexed by `ι` and constraints indexed by `K`. -/
structure LQProblem where
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The loss weights `w_i ≥ 0`. -/
  w : ι → ℝ
  /-- The target values `z̄_{t,i}`. -/
  target : ℕ → ι → Ω → ℝ
  /-- The coefficients `C_{k i}` on lagged variables in constraint `k`. -/
  lagCoef : K → ι → ℝ
  /-- The coefficients `A_{k i}` on current variables in constraint `k`. -/
  curCoef : K → ι → ℝ
  /-- The coefficients `B_{k i}` on expected next-period variables in constraint `k`. -/
  leadCoef : K → ι → ℝ
  /-- The forcing terms `g_{t,k}` of the constraints. -/
  forcing : ℕ → K → Ω → ℝ
  /-- The given initial values `z_{−1,i}`. -/
  init : ι → Ω → ℝ

variable {Ω ι K}

variable [Fintype ι] [Fintype K]

/-- Woodford (2003), Ch. 7, p. 472: the linear combination `∑_i a_i v_i` of random variables. -/
def dotC (a : ι → ℝ) (v : ι → Ω → ℝ) : Ω → ℝ := fun ω => ∑ i, a i * v i ω

variable (𝔼 : ExpectationSystem Ω) (P : LQProblem Ω ι K)

/-- Woodford (2003), Ch. 7, (1.1) and (2.1), pp. 469, 487: the plan `z` satisfies every
constraint `∑_i (C_{k i} z_{t−1,i} + A_{k i} z_{t,i} + B_{k i} E_t z_{t+1,i}) = g_{t,k}`,
`t ≥ 0`, with `z_{−1}` the given initial values. -/
def Feasible (z : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t k ω, ∑ i, (P.lagCoef k i * lagged P.init z t i ω + P.curCoef k i * z t i ω +
    P.leadCoef k i * 𝔼.E t (z (t + 1) i) ω) = P.forcing t k ω

/-- Woodford (2003), Ch. 7, pp. 472, 488: an admissible plan: feasible, adapted and bounded
(the book's "bounded paths"). -/
def Plan (z : ℕ → ι → Ω → ℝ) : Prop :=
  Feasible 𝔼 P z ∧ (∀ t i, 𝔼.E t (z t i) = z t i) ∧ ∃ M, ∀ t i ω, |z t i ω| ≤ M

/-- Woodford (2003), eq. (1.2), p. 469, and (2.4), p. 488: the period loss
`∑_i w_i (z_{t,i} − z̄_{t,i})²`. -/
def periodLoss (z : ℕ → ι → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑ i, P.w i * (z t i ω - P.target t i ω) ^ 2

/-- Woodford (2003), eq. (1.2), p. 469, and Ch. 7, §2.1, p. 488: the expected discounted loss
`E_0 ∑_{t ≥ 0} βᵗ ∑_i w_i (z_{t,i} − z̄_{t,i})²` (a date-0 random variable). -/
noncomputable def expLoss (z : ℕ → ι → Ω → ℝ) : Ω → ℝ :=
  𝔼.E 0 (fun ω => ∑' t, P.β ^ t * periodLoss P z t ω)

/-- Woodford (2003), (1.7)–(1.9), p. 472, (2.5)–(2.6), p. 489, and (1.16)–(1.18), p. 477: the
first-order conditions of the Lagrangian with multipliers `φ_{t,k}` and initial multiplier
`φ_{−1,k} = φm k`:
`w_i (z_{t,i} − z̄_{t,i}) + ∑_k (A_{k i} φ_{t,k} + β⁻¹ B_{k i} φ_{t−1,k} + β C_{k i} E_t φ_{t+1,k})
= 0`. -/
def FOC (z : ℕ → ι → Ω → ℝ) (φm : K → Ω → ℝ) (φ : ℕ → K → Ω → ℝ) : Prop :=
  ∀ t i ω, P.w i * (z t i ω - P.target t i ω) + ∑ k, (P.curCoef k i * φ t k ω +
    P.β⁻¹ * P.leadCoef k i * lagged φm φ t k ω + P.β * P.lagCoef k i * 𝔼.E t (φ (t + 1) k) ω)
    = 0

/-! ### Linear algebra and bounds -/

omit [Fintype K] in
/-- Woodford (2003), Ch. 7, p. 489: `E_t` commutes with finite linear combinations,
`E_t(∑_i a_i v_i) = ∑_i a_i E_t v_i`. -/
theorem E_dotC (t : ℕ) (a : ι → ℝ) (v : ι → Ω → ℝ) (ω : Ω) :
    𝔼.E t (dotC a v) ω = ∑ i, a i * 𝔼.E t (v i) ω := by
  have h : dotC a v = ∑ i, a i • v i := by
    funext ω'
    simp [dotC, Finset.sum_apply]
  rw [h, map_sum, Finset.sum_apply]
  simp [map_smul]

omit [Fintype K] in
/-- Woodford (2003), Ch. 7, p. 489: a linear combination of variables known at `t` is known
at `t`. -/
theorem E_dotC_known {t : ℕ} (a : ι → ℝ) {v : ι → Ω → ℝ} (hv : ∀ i, 𝔼.E t (v i) = v i) :
    𝔼.E t (dotC a v) = dotC a v := by
  funext ω
  rw [E_dotC]
  simp [dotC, hv]

omit [Fintype K] in
/-- Woodford (2003), Ch. 7, p. 472: `|∑_i a_i v_i| ≤ (∑_i |a_i|) V` when every `|v_i| ≤ V`. -/
theorem abs_dotC_le (a : ι → ℝ) {v : ι → Ω → ℝ} {V : ℝ} (hv : ∀ i ω, |v i ω| ≤ V) (ω : Ω) :
    |dotC a v ω| ≤ (∑ i, |a i|) * V := by
  unfold dotC
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hv i ω) (abs_nonneg _)

/-- Woodford (2003), Ch. 7, p. 489: `E_t` of a nonnegative random variable is nonnegative. -/
theorem E_nonneg {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have := 𝔼.mono t (show (0 : Ω → ℝ) ≤ f from hf) ω
  rwa [map_zero] at this

omit [Fintype K] in
/-- Woodford (2003), eq. (1.2), p. 469: the period loss of a bounded plan is bounded. -/
theorem periodLoss_bound (hw : ∀ i, 0 ≤ P.w i) {z : ℕ → ι → Ω → ℝ} {M T : ℝ}
    (hz : ∀ t i ω, |z t i ω| ≤ M) (hT : ∀ t i ω, |P.target t i ω| ≤ T) (t : ℕ) (ω : Ω) :
    |periodLoss P z t ω| ≤ ∑ i, P.w i * (M + T) ^ 2 := by
  unfold periodLoss
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    ((abs_sub _ _).trans (add_le_add (hz t i ω) (hT t i ω))) 2

omit [Fintype K] in
/-- Woodford (2003), eq. (1.2), p. 469, and (2.4), p. 488: for a bounded plan the expected loss
is the genuine infinite sum `∑ βᵗ E_0 ℓ_t` (`E_0` commutes with the geometrically dominated
series). -/
theorem expLoss_hasSum (hβ0 : 0 ≤ P.β) (hβ1 : P.β < 1) (hw : ∀ i, 0 ≤ P.w i)
    {z : ℕ → ι → Ω → ℝ} {M T : ℝ} (hz : ∀ t i ω, |z t i ω| ≤ M)
    (hT : ∀ t i ω, |P.target t i ω| ≤ T) (ω : Ω) :
    HasSum (fun t => P.β ^ t * 𝔼.E 0 (periodLoss P z t) ω) (expLoss 𝔼 P z ω) := by
  set L := ∑ i, P.w i * (M + T) ^ 2 with hL
  have hpl := periodLoss_bound P hw hz hT
  have hf : ∀ k ω, |P.β ^ k * periodLoss P z k ω| ≤ P.β ^ k * L := by
    intro k ω
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (hpl k ω) (pow_nonneg hβ0 k)
  have hE : 𝔼.E 0 (fun ω' => ∑' k, P.β ^ k * periodLoss P z k ω') ω =
      ∑' k, 𝔼.E 0 (fun ω' => P.β ^ k * periodLoss P z k ω') ω := 𝔼.E_tsum hβ0 hβ1 hf 0 ω
  have heq : ∀ k, 𝔼.E 0 (fun ω' => P.β ^ k * periodLoss P z k ω') ω =
      P.β ^ k * 𝔼.E 0 (periodLoss P z k) ω := fun k => by
    have : (fun ω' => P.β ^ k * periodLoss P z k ω') = P.β ^ k • periodLoss P z k := rfl
    rw [this, map_smul]; rfl
  have hs : Summable (fun t => P.β ^ t * 𝔼.E 0 (periodLoss P z t) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right L) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hpl k) 0 ω) (pow_nonneg hβ0 k))
  convert hs.hasSum using 1
  change 𝔼.E 0 (fun ω' => ∑' k, P.β ^ k * periodLoss P z k ω') ω = _
  rw [hE]
  exact tsum_congr heq

/-! ### The one-period Lagrangian identity -/

omit [Fintype ι] [Fintype K] in
/-- Woodford (2003), Ch. 7, pp. 472, 489 (survey §4.4; the algebra behind the Lagrangian): if
`z*` satisfies the first-order conditions and `z`, `z*` satisfy the same linear constraints, then
`∑ w(z − z̄)² − ∑ w(z* − z̄)² = ∑ w (z − z*)² + 2 ∑_k [φ_k C_k·(z₋ − z*₋) + φ_k B_k·(Ez − Ez*)
− β⁻¹ φ₋_k B_k·(z − z*) − β Eφ₊_k C_k·(z − z*)]`. -/
theorem key_identity [Fintype ι] [Fintype K] (w : ι → ℝ) (A B C : K → ι → ℝ) (β : ℝ)
    (z zs zb pz pzs ez ezs : ι → ℝ) (φ φm eφ : K → ℝ)
    (hfoc : ∀ i, w i * (zs i - zb i) +
      ∑ k, (A k i * φ k + β⁻¹ * B k i * φm k + β * C k i * eφ k) = 0)
    (hf : ∀ k, ∑ i, (C k i * pz i + A k i * z i + B k i * ez i) =
      ∑ i, (C k i * pzs i + A k i * zs i + B k i * ezs i)) :
    ∑ i, w i * (z i - zb i) ^ 2 - ∑ i, w i * (zs i - zb i) ^ 2 =
      ∑ i, w i * (z i - zs i) ^ 2 + 2 * ∑ k, (φ k * ∑ i, C k i * (pz i - pzs i) +
        φ k * ∑ i, B k i * (ez i - ezs i) - β⁻¹ * φm k * ∑ i, B k i * (z i - zs i) -
        β * eφ k * ∑ i, C k i * (z i - zs i)) := by
  have e1 : ∑ i, w i * (z i - zb i) ^ 2 - ∑ i, w i * (zs i - zb i) ^ 2 =
      ∑ i, w i * (z i - zs i) ^ 2 + 2 * ∑ i, w i * (zs i - zb i) * (z i - zs i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, w i * (zs i - zb i) * (z i - zs i) =
      -∑ k, (φ k * ∑ i, A k i * (z i - zs i) + β⁻¹ * φm k * ∑ i, B k i * (z i - zs i) +
        β * eφ k * ∑ i, C k i * (z i - zs i)) := by
    have : ∀ i, w i * (zs i - zb i) * (z i - zs i) =
        -∑ k, (A k i * φ k + β⁻¹ * B k i * φm k + β * C k i * eφ k) * (z i - zs i) := by
      intro i
      rw [← Finset.sum_mul, show w i * (zs i - zb i) =
        -∑ k, (A k i * φ k + β⁻¹ * B k i * φm k + β * C k i * eφ k) by linarith [hfoc i]]
      ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∀ k, ∑ i, A k i * (z i - zs i) =
      -∑ i, C k i * (pz i - pzs i) - ∑ i, B k i * (ez i - ezs i) := by
    intro k
    have h := hf k
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h
    have h' : ∑ i, (C k i * (pz i - pzs i) + A k i * (z i - zs i) + B k i * (ez i - ezs i)) = 0 :=
      by rw [← h]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h'
    linarith
  rw [e1, e2]
  congr 1
  rw [mul_neg, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e4 k]
  ring

/-! ### The telescoping argument -/

/-- Woodford (2003), Ch. 7, p. 473 ("the only one satisfying the relevant transversality
condition"; survey §4.4): if `g_t = D_t + 2(h_t − h_{t+1})` with `D_t ≥ 0`, `∑ g_t = G` and
`h_t → 0`, then `∑ D_t = G − 2h_0`. -/
theorem hasSum_of_telescope {g D h : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) (hD : ∀ t, 0 ≤ D t)
    (hgt : ∀ t, g t = D t + 2 * (h t - h (t + 1))) (hh : Tendsto h atTop (𝓝 0)) :
    HasSum D (G - 2 * h 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hD]
  have hpart : (fun n => ∑ t ∈ Finset.range n, D t) =
      fun n => ∑ t ∈ Finset.range n, g t - 2 * h 0 + 2 * h n := by
    funext n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hgt n]; ring
  rw [hpart]
  simpa using (hg.tendsto_sum_nat.sub_const (2 * h 0)).add (hh.const_mul 2)

/-! ### The Lagrangian identity for the expected loss -/

/-- Woodford (2003), Ch. 7, p. 473 (survey §4.4): the boundary term
`h_t = ∑_k (βᵗ E_0[φ_{t,k} C_k·(z_{t−1} − z*_{t−1})] − βᵗβ⁻¹ E_0[φ_{t−1,k} B_k·(z_t − z*_t)])`
of the telescoping sum. -/
noncomputable def telTerm (z zs : ℕ → ι → Ω → ℝ) (φm : K → Ω → ℝ) (φ : ℕ → K → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  ∑ k, (P.β ^ t * 𝔼.E 0 (φ t k * dotC (P.lagCoef k)
      (fun i => lagged P.init z t i - lagged P.init zs t i)) ω -
    P.β ^ t * P.β⁻¹ * 𝔼.E 0 (lagged φm φ t k * dotC (P.leadCoef k)
      (fun i => z t i - zs t i)) ω)

/-- Woodford (2003), Ch. 7, p. 489 (survey §4.4: law of iterated expectations and pull-out):
the one-period Lagrangian identity in expectation,
`βᵗ(E_0 ℓ_t(z) − E_0 ℓ_t(z*)) = βᵗ E_0 ∑_i w_i (z_{t,i} − z*_{t,i})² + 2(h_t − h_{t+1})`. -/
theorem period_identity (hpo : 𝔼.PullOut) (hβ : P.β ≠ 0) {z zs : ℕ → ι → Ω → ℝ}
    {φm : K → Ω → ℝ} {φ : ℕ → K → Ω → ℝ} (hz : Plan 𝔼 P z) (hzs : Plan 𝔼 P zs)
    (hfoc : FOC 𝔼 P zs φm φ) (hφa : ∀ t k, 𝔼.E t (φ t k) = φ t k) (t : ℕ) (ω : Ω) :
    P.β ^ t * (𝔼.E 0 (periodLoss P z t) ω - 𝔼.E 0 (periodLoss P zs t) ω) =
      P.β ^ t * 𝔼.E 0 (fun ω => ∑ i, P.w i * (z t i ω - zs t i ω) ^ 2) ω +
        2 * (telTerm 𝔼 P z zs φm φ t ω - telTerm 𝔼 P z zs φm φ (t + 1) ω) := by
  obtain ⟨hzf, hza, -⟩ := hz
  obtain ⟨hzsf, hzsa, -⟩ := hzs
  set cP : K → Ω → ℝ := fun k => dotC (P.lagCoef k)
    (fun i => lagged P.init z t i - lagged P.init zs t i) with hcP
  set bL : K → Ω → ℝ := fun k => dotC (P.leadCoef k) (fun i => z (t + 1) i - zs (t + 1) i)
    with hbL
  set bC : K → Ω → ℝ := fun k => dotC (P.leadCoef k) (fun i => z t i - zs t i) with hbC
  set cC : K → Ω → ℝ := fun k => dotC (P.lagCoef k) (fun i => z t i - zs t i) with hcC
  -- the pointwise identity, as an identity of random variables
  have hfun : periodLoss P z t - periodLoss P zs t =
      (fun ω => ∑ i, P.w i * (z t i ω - zs t i ω) ^ 2) + (2 : ℝ) • ∑ k,
        (φ t k * cP k + φ t k * 𝔼.E t (bL k) - P.β⁻¹ • (lagged φm φ t k * bC k) -
          P.β • (𝔼.E t (φ (t + 1) k) * cC k)) := by
    funext ω'
    have hk := key_identity P.w P.curCoef P.leadCoef P.lagCoef P.β (fun i => z t i ω')
      (fun i => zs t i ω') (fun i => P.target t i ω') (fun i => lagged P.init z t i ω')
      (fun i => lagged P.init zs t i ω') (fun i => 𝔼.E t (z (t + 1) i) ω')
      (fun i => 𝔼.E t (zs (t + 1) i) ω') (fun k => φ t k ω') (fun k => lagged φm φ t k ω')
      (fun k => 𝔼.E t (φ (t + 1) k) ω') (fun i => hfoc t i ω')
      (fun k => (hzf t k ω').trans (hzsf t k ω').symm)
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Pi.mul_apply, periodLoss]
    rw [hk]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbL, E_dotC]
    simp only [hcP, hbC, hcC, dotC, map_sub, Pi.sub_apply]
    ring
  -- the two pull-out steps
  have hp1 : ∀ k, 𝔼.E 0 (φ t k * 𝔼.E t (bL k)) = 𝔼.E 0 (φ t k * bL k) := fun k => by
    rw [← hpo t _ _ (hφa t k), 𝔼.tower (Nat.zero_le t)]
  have hcCa : ∀ k, 𝔼.E t (cC k) = cC k := fun k =>
    E_dotC_known 𝔼 _ fun i => by rw [map_sub, hza t i, hzsa t i]
  have hp2 : ∀ k, 𝔼.E 0 (𝔼.E t (φ (t + 1) k) * cC k) = 𝔼.E 0 (cC k * φ (t + 1) k) := fun k => by
    rw [mul_comm, ← hpo t _ _ (hcCa k), 𝔼.tower (Nat.zero_le t)]
  have hE := congrFun (congrArg (𝔼.E 0) hfun) ω
  simp only [map_sub, map_add, map_smul, map_sum, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_apply, hp1, hp2] at hE
  rw [hE]
  unfold telTerm
  rw [mul_add, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [lagged_succ, hcP, hbL, hbC, hcC]
  rw [mul_comm (dotC (P.lagCoef k) (fun i => z t i - zs t i)) (φ (t + 1) k), pow_succ]
  field_simp
  ring

/-- **Woodford (2003), Ch. 7, pp. 472–475, 489 (the Lagrangian identity; survey §4.4)**: for
bounded adapted feasible plans `z` and `z*`, where `z*` satisfies the first-order conditions with
a bounded adapted multiplier `φ` and a bounded initial multiplier `φ_{−1}`,
`∑_t βᵗ E_0 ∑_i w_i (z_{t,i} − z*_{t,i})² = E_0 L(z) − E_0 L(z*) +
2β⁻¹ ∑_k E_0[φ_{−1,k} ∑_i B_{k i}(z_{0,i} − z*_{0,i})]`, the series converging. -/
theorem expLoss_sub_hasSum (hpo : 𝔼.PullOut) (hβ0 : 0 < P.β) (hβ1 : P.β < 1)
    (hw : ∀ i, 0 ≤ P.w i) (hT : ∃ T, ∀ t i ω, |P.target t i ω| ≤ T)
    {z zs : ℕ → ι → Ω → ℝ} {φm : K → Ω → ℝ} {φ : ℕ → K → Ω → ℝ} (hz : Plan 𝔼 P z)
    (hzs : Plan 𝔼 P zs) (hfoc : FOC 𝔼 P zs φm φ) (hφa : ∀ t k, 𝔼.E t (φ t k) = φ t k)
    (hφb : ∃ F, ∀ t k ω, |φ t k ω| ≤ F) (hφmb : ∃ F, ∀ k ω, |φm k ω| ≤ F) (ω : Ω) :
    HasSum (fun t => P.β ^ t * 𝔼.E 0 (fun ω => ∑ i, P.w i * (z t i ω - zs t i ω) ^ 2) ω)
      (expLoss 𝔼 P z ω - expLoss 𝔼 P zs ω +
        2 * P.β⁻¹ * ∑ k, 𝔼.E 0 (φm k * dotC (P.leadCoef k) (fun i => z 0 i - zs 0 i)) ω) := by
  obtain ⟨T, hT⟩ := hT
  obtain ⟨M1, hM1⟩ := hz.2.2
  obtain ⟨M2, hM2⟩ := hzs.2.2
  obtain ⟨F1, hF1⟩ := hφb
  obtain ⟨F2, hF2⟩ := hφmb
  have hg := (expLoss_hasSum 𝔼 P hβ0.le hβ1 hw hM1 hT ω).sub
    (expLoss_hasSum 𝔼 P hβ0.le hβ1 hw hM2 hT ω)
  -- bounds for the boundary term
  set F := |F1| + |F2| with hF
  set Md := |M1| + |M2| with hMd
  have hlagφ : ∀ t k ω, |lagged φm φ t k ω| ≤ F := by
    intro t k ω
    cases t with
    | zero => exact (hF2 k ω).trans ((le_abs_self F2).trans (by simp [hF]))
    | succ t => exact (hF1 t k ω).trans ((le_abs_self F1).trans (by simp [hF]))
  have hdiff : ∀ t i ω, |z t i ω - zs t i ω| ≤ Md := fun t i ω =>
    (abs_sub _ _).trans (add_le_add ((hM1 t i ω).trans (le_abs_self _))
      ((hM2 t i ω).trans (le_abs_self _)))
  have hldiff : ∀ t i ω, |lagged P.init z t i ω - lagged P.init zs t i ω| ≤ Md := by
    intro t i ω
    cases t with
    | zero => simp only [lagged_zero, sub_self, abs_zero]; positivity
    | succ t => exact hdiff t i ω
  set CB := ∑ k, ((∑ i, |P.lagCoef k i|) + P.β⁻¹ * ∑ i, |P.leadCoef k i|) * (F * Md) with hCB
  have htel : ∀ t, |telTerm 𝔼 P z zs φm φ t ω| ≤ P.β ^ t * CB := by
    intro t
    unfold telTerm
    rw [hCB, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hb1 : ∀ ω', |(φ t k * dotC (P.lagCoef k)
        (fun i => lagged P.init z t i - lagged P.init zs t i)) ω'| ≤
        F * ((∑ i, |P.lagCoef k i|) * Md) := fun ω' => by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul ((hF1 t k ω').trans ((le_abs_self F1).trans (by simp [hF])))
        (abs_dotC_le _ (fun i ω => hldiff t i ω) ω') (abs_nonneg _) (by positivity)
    have hb2 : ∀ ω', |(lagged φm φ t k * dotC (P.leadCoef k)
        (fun i => z t i - zs t i)) ω'| ≤ F * ((∑ i, |P.leadCoef k i|) * Md) := fun ω' => by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hlagφ t k ω') (abs_dotC_le _ (fun i ω => hdiff t i ω) ω')
        (abs_nonneg _) (by positivity)
    have e1 := 𝔼.abs_E_le hb1 0 ω
    have e2 := 𝔼.abs_E_le hb2 0 ω
    have hβt : 0 ≤ P.β ^ t := pow_nonneg hβ0.le t
    have hβi : 0 ≤ P.β⁻¹ := inv_nonneg.mpr hβ0.le
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hβt, abs_of_nonneg hβi]
    have := mul_le_mul_of_nonneg_left e1 hβt
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 hβi) hβt
    nlinarith
  have hlim : Tendsto (fun t => telTerm 𝔼 P z zs φm φ t ω) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun t => P.β ^ t * CB) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs]; exact htel t
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const CB
  have h := hasSum_of_telescope hg
    (fun t => mul_nonneg (pow_nonneg hβ0.le t)
      (E_nonneg 𝔼 (fun ω => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) 0 ω))
    (fun t => by rw [← mul_sub]; exact period_identity 𝔼 P hpo hβ0.ne' hz hzs hfoc hφa t ω)
    hlim
  convert h using 1
  unfold telTerm
  simp only [pow_zero, one_mul, lagged_zero, sub_self]
  have h0 : ∀ k, 𝔼.E 0 (φ 0 k * dotC (P.lagCoef k) (fun _ => (0 : Ω → ℝ))) ω = 0 := by
    intro k
    have : φ 0 k * dotC (P.lagCoef k) (fun _ => (0 : Ω → ℝ)) = 0 := by
      funext ω'; simp [dotC]
    rw [this, map_zero, Pi.zero_apply]
  simp only [h0, zero_sub, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-! ### Optimality -/

/-- **Woodford (2003), Ch. 7, pp. 472–475, 489 (Lagrangian sufficiency; survey §4.4)**: if `z*` is
feasible and satisfies the first-order conditions with bounded adapted multipliers, then in every
state `ω` its expected loss is no larger than that of any bounded adapted feasible plan `z` whose
initial-commitment term `∑_k E_0[φ_{−1,k} B_k·(z_0 − z*_0)]` vanishes at `ω`. -/
theorem expLoss_le_of_foc (hpo : 𝔼.PullOut) (hβ0 : 0 < P.β) (hβ1 : P.β < 1)
    (hw : ∀ i, 0 ≤ P.w i) (hT : ∃ T, ∀ t i ω, |P.target t i ω| ≤ T)
    {z zs : ℕ → ι → Ω → ℝ} {φm : K → Ω → ℝ} {φ : ℕ → K → Ω → ℝ} (hz : Plan 𝔼 P z)
    (hzs : Plan 𝔼 P zs) (hfoc : FOC 𝔼 P zs φm φ) (hφa : ∀ t k, 𝔼.E t (φ t k) = φ t k)
    (hφb : ∃ F, ∀ t k ω, |φ t k ω| ≤ F) (hφmb : ∃ F, ∀ k ω, |φm k ω| ≤ F) (ω : Ω)
    (hinit : ∑ k, 𝔼.E 0 (φm k * dotC (P.leadCoef k) (fun i => z 0 i - zs 0 i)) ω = 0) :
    expLoss 𝔼 P zs ω ≤ expLoss 𝔼 P z ω := by
  have h := expLoss_sub_hasSum 𝔼 P hpo hβ0 hβ1 hw hT hz hzs hfoc hφa hφb hφmb ω
  rw [hinit, mul_zero, add_zero] at h
  exact sub_nonneg.1 (h.nonneg fun t => mul_nonneg (pow_nonneg hβ0.le t)
    (E_nonneg 𝔼 (fun ω => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) 0 ω))

/-- **Woodford (2003), Ch. 7, pp. 472–475, 489 (uniqueness of the optimum; survey §4.4)**: under
the hypotheses of `expLoss_le_of_foc`, a plan with the same expected loss at `ω` agrees with `z*`
in conditional mean square, `E_0 (z_{t,i} − z*_{t,i})² = 0` at `ω`, on every coordinate with
`w_i > 0` (strict convexity in the target variables). -/
theorem eq_of_expLoss_eq (hpo : 𝔼.PullOut) (hβ0 : 0 < P.β) (hβ1 : P.β < 1)
    (hw : ∀ i, 0 ≤ P.w i) (hT : ∃ T, ∀ t i ω, |P.target t i ω| ≤ T)
    {z zs : ℕ → ι → Ω → ℝ} {φm : K → Ω → ℝ} {φ : ℕ → K → Ω → ℝ} (hz : Plan 𝔼 P z)
    (hzs : Plan 𝔼 P zs) (hfoc : FOC 𝔼 P zs φm φ) (hφa : ∀ t k, 𝔼.E t (φ t k) = φ t k)
    (hφb : ∃ F, ∀ t k ω, |φ t k ω| ≤ F) (hφmb : ∃ F, ∀ k ω, |φm k ω| ≤ F) (ω : Ω)
    (hinit : ∑ k, 𝔼.E 0 (φm k * dotC (P.leadCoef k) (fun i => z 0 i - zs 0 i)) ω = 0)
    (heq : expLoss 𝔼 P z ω = expLoss 𝔼 P zs ω) (t : ℕ) (i : ι) (hwi : 0 < P.w i) :
    𝔼.E 0 (fun ω => (z t i ω - zs t i ω) ^ 2) ω = 0 := by
  have h := expLoss_sub_hasSum 𝔼 P hpo hβ0 hβ1 hw hT hz hzs hfoc hφa hφb hφmb ω
  rw [hinit, mul_zero, add_zero, heq, sub_self] at h
  have hz0 := (hasSum_zero_iff_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ0.le t)
    (E_nonneg 𝔼 (fun ω => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))
      0 ω))).1 h
  have ht := congrFun hz0 t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at ht
  have hsplit : (fun ω => ∑ j, P.w j * (z t j ω - zs t j ω) ^ 2) =
      ∑ j, P.w j • (fun ω => (z t j ω - zs t j ω) ^ 2) := by
    funext ω'; simp [Finset.sum_apply]
  rw [hsplit, map_sum, Finset.sum_apply] at ht
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at ht
  have hnn : ∀ j, 0 ≤ P.w j * 𝔼.E 0 (fun ω => (z t j ω - zs t j ω) ^ 2) ω := fun j =>
    mul_nonneg (hw j) (E_nonneg 𝔼 (fun ω => sq_nonneg _) 0 ω)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).1 ht i (Finset.mem_univ i)
  rcases mul_eq_zero.1 hi with h | h
  · exact absurd h hwi.ne'
  · exact h

/-- Woodford (2003), Ch. 7, p. 474 (constraints on the initial outcomes): `z*` is optimal among
the admissible plans in the class `S`: it is an admissible plan in `S` and, state by state, no
admissible plan in `S` has a smaller expected loss. -/
def IsOptimalAmong (S : (ℕ → ι → Ω → ℝ) → Prop) (zs : ℕ → ι → Ω → ℝ) : Prop :=
  S zs ∧ Plan 𝔼 P zs ∧ ∀ z, S z → Plan 𝔼 P z → ∀ ω, expLoss 𝔼 P zs ω ≤ expLoss 𝔼 P z ω

/-- Woodford (2003), Ch. 7, p. 474 (**sufficiency with initial commitments**): if `z*` satisfies
the first-order conditions with bounded adapted multipliers, and every plan in the class `S`
fulfils the initial commitments `φ_{−1,k} B_k·(z_0 − z*_0) = 0`, then `z*` is optimal in `S`. -/
theorem isOptimalAmong_of_foc (hpo : 𝔼.PullOut) (hβ0 : 0 < P.β) (hβ1 : P.β < 1)
    (hw : ∀ i, 0 ≤ P.w i) (hT : ∃ T, ∀ t i ω, |P.target t i ω| ≤ T)
    {S : (ℕ → ι → Ω → ℝ) → Prop} {zs : ℕ → ι → Ω → ℝ} {φm : K → Ω → ℝ}
    {φ : ℕ → K → Ω → ℝ} (hSzs : S zs) (hzs : Plan 𝔼 P zs) (hfoc : FOC 𝔼 P zs φm φ)
    (hφa : ∀ t k, 𝔼.E t (φ t k) = φ t k) (hφb : ∃ F, ∀ t k ω, |φ t k ω| ≤ F)
    (hφmb : ∃ F, ∀ k ω, |φm k ω| ≤ F)
    (hS : ∀ z, S z → ∀ k ω, φm k ω * dotC (P.leadCoef k) (fun i => z 0 i - zs 0 i) ω = 0) :
    IsOptimalAmong 𝔼 P S zs := by
  refine ⟨hSzs, hzs, fun z hSz hz ω => ?_⟩
  refine expLoss_le_of_foc 𝔼 P hpo hβ0 hβ1 hw hT hz hzs hfoc hφa hφb hφmb ω ?_
  refine Finset.sum_eq_zero fun k _ => ?_
  have : φm k * dotC (P.leadCoef k) (fun i => z 0 i - zs 0 i) = 0 := funext (hS z hSz k)
  rw [this, map_zero, Pi.zero_apply]

/-- Woodford (2003), Ch. 7, pp. 472–473, (1.9) (**sufficiency without initial commitments**): if
`z*` satisfies the first-order conditions with `φ_{−1} = 0` and bounded adapted multipliers, it
minimises the expected loss, state by state, among all bounded adapted feasible plans. -/
theorem isOptimal_of_foc_noInit (hpo : 𝔼.PullOut) (hβ0 : 0 < P.β) (hβ1 : P.β < 1)
    (hw : ∀ i, 0 ≤ P.w i) (hT : ∃ T, ∀ t i ω, |P.target t i ω| ≤ T)
    {zs : ℕ → ι → Ω → ℝ} {φ : ℕ → K → Ω → ℝ} (hzs : Plan 𝔼 P zs) (hfoc : FOC 𝔼 P zs 0 φ)
    (hφa : ∀ t k, 𝔼.E t (φ t k) = φ t k) (hφb : ∃ F, ∀ t k ω, |φ t k ω| ≤ F) :
    IsOptimalAmong 𝔼 P (fun _ => True) zs :=
  isOptimalAmong_of_foc 𝔼 P hpo hβ0 hβ1 hw hT trivial hzs hfoc hφa hφb ⟨0, fun _ _ => by simp⟩
    fun _ _ k ω => by simp

/-! ### The deterministic case -/

omit [Fintype K] in
/-- Woodford (2003), eq. (1.2), p. 469 (perfect foresight): the expected loss is the discounted
sum `∑ βᵗ ∑_i w_i (z_{t,i} − z̄_{t,i})²`. -/
theorem expLoss_perfectForesight (P : LQProblem Unit ι K) (z : ℕ → ι → Unit → ℝ) :
    expLoss perfectForesight P z () = ∑' t, P.β ^ t * periodLoss P z t () := rfl

/-- **Woodford (2003), Ch. 7, pp. 472–475 (deterministic Lagrangian sufficiency)**: under perfect
foresight, a feasible bounded plan satisfying the first-order conditions with bounded
multipliers has a loss no larger than any bounded feasible plan fulfilling the initial
commitments; equality forces equality on every coordinate with positive weight. -/
theorem det_loss_le_of_foc (P : LQProblem Unit ι K) (hβ0 : 0 < P.β) (hβ1 : P.β < 1)
    (hw : ∀ i, 0 ≤ P.w i) (hT : ∃ T, ∀ t i ω, |P.target t i ω| ≤ T)
    {z zs : ℕ → ι → Unit → ℝ} {φm : K → Unit → ℝ} {φ : ℕ → K → Unit → ℝ}
    (hz : Plan perfectForesight P z) (hzs : Plan perfectForesight P zs)
    (hfoc : FOC perfectForesight P zs φm φ) (hφb : ∃ F, ∀ t k ω, |φ t k ω| ≤ F)
    (hinit : ∀ k, φm k () * dotC (P.leadCoef k) (fun i => z 0 i - zs 0 i) () = 0) :
    ∑' t, P.β ^ t * periodLoss P zs t () ≤ ∑' t, P.β ^ t * periodLoss P z t () ∧
      (∑' t, P.β ^ t * periodLoss P z t () = ∑' t, P.β ^ t * periodLoss P zs t () →
        ∀ t i, 0 < P.w i → z t i = zs t i) := by
  have hφmb : ∃ F, ∀ k ω, |φm k ω| ≤ F :=
    ⟨∑ k, |φm k ()|, fun k ω => by
      cases ω
      exact Finset.single_le_sum (f := fun k => |φm k ()|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ k)⟩
  have hφa : ∀ t k, perfectForesight.E t (φ t k) = φ t k := fun _ _ => rfl
  have hin : ∑ k, perfectForesight.E 0 (φm k * dotC (P.leadCoef k) (fun i => z 0 i - zs 0 i))
      () = 0 := Finset.sum_eq_zero fun k _ => hinit k
  refine ⟨expLoss_le_of_foc perfectForesight P perfectForesight_pullOut hβ0 hβ1 hw hT hz hzs
    hfoc hφa hφb hφmb () hin, fun heq t i hwi => ?_⟩
  have h := eq_of_expLoss_eq perfectForesight P perfectForesight_pullOut hβ0 hβ1 hw hT hz hzs
    hfoc hφa hφb hφmb () hin heq t i hwi
  funext ω
  cases ω
  have : (z t i () - zs t i ()) ^ 2 = 0 := h
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)

end Woodford.GainsFromCommitment.LQSufficiency
