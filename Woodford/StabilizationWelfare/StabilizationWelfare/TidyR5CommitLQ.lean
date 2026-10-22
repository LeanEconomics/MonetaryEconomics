/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.PriceStability
import StabilizationWelfare.CostPush

/-!
# The date-0 optimal commitment of p. 415 and the optimality claim of footnote 71

Woodford (2003), *Interest and Prices*, Chapter 6, §3.2, pp. 412–416 (the date-0 optimal
commitment with an inefficient natural rate, eq. (3.5)) and §4.5, footnote 71, p. 454 (the
efficient frontier of Figure 6.6 is complete stabilisation of `log P_t + φx_t` with
`λ = 16κφ`); the results anticipate Chapter 7, §1 (pp. 470–490) and §5.1 (p. 527).

PriceStability proved that a path satisfying the first-order conditions is the optimal
commitment (`PriceStability.commit_optimal`) and that IF it converges its limit has zero
inflation (`PriceStability.commit_limits`). Here the optimal path is constructed and its
convergence is proved.

## Main results

* The explicit path `muP`, `piP`, `xP` driven by a root `z` of the characteristic polynomial
  solves the AS relation and the first-order conditions (`path_AS`, `path_FOC`); the stable
  root `zRoot` of `βz² − (1+β+c)z + 1` satisfies `0 < z < 1` (`zRoot_props`).
* **`date0_exists`**, **`date0_optimal`**: for `0 < β < 1`, `κ, λ > 0`, the date-0 optimal
  commitment exists, is bounded and is the unique optimum among bounded feasible paths;
  `date0_formula` (`π_t = (λx*/κ)(1 − z)zᵗ`, `x_t = x*z^{t+1}`), `date0_positive` (inflation is
  positive at every date when `x* > 0`), **`date0_tendsto`** (it converges to the timeless plan
  `π = x = 0`, `μ = μ̄`), `date0_geometric` (at the rate `z`), **`longrun_zero`** (the
  long-run inflation of the optimal commitment is zero, unconditionally).
* The timeless perspective (p. 415, Ch. 7): `CommitFOCm` (initial multiplier `μ_{−1}`),
  `commit_gap_init` (the gap identity with the initial term `2(b/β)μ_{−1}(π'_0 − π_0)`),
  **`timeless_zero_optimal`** (`π_t = 0` at all times is optimal among bounded feasible paths
  that honour the timeless constraint `π'_0 = 0`).
* The "simplified" AS relation with a unit coefficient (p. 415): **`date0_one_exists`**,
  **`date0_one_tendsto`**, **`longrun_negative`**: the date-0 optimal commitment exists and its
  long-run inflation is `−(1 − β)λx*/(βκ) < 0`, unconditionally.
* Uncertainty (p. 414, "the optimal commitment from date zero onward involves a deterministic
  path for inflation"): `NKPCu` (with a cost-push term), the stochastic gap identity
  **`gap_stoch`** (for any `ExpectationSystem`, with a pull-out hypothesis for the multiplier),
  **`date0_optimal_stoch`**: the deterministic date-0 path minimises `E_0 ∑ βᵗ[π_t² +
  λ(x_t − x*)²]` among ALL bounded feasible processes, adapted or not.
* Footnote 71 (cost-push shocks, `x* = 0`): the plan `fnX`, `fnPi` with `x_t = z x_{t−1} + v_t`
  and `v` the forward series of the cost-push shock; **`fn71_AS`** (it is an equilibrium),
  **`fn71_targeting`** (it stabilises `p_t + φx_t` completely), **`fn71_optimal`** (with
  `x_{−1} = 0` it is the date-0 optimal policy for the weight `λ = κφ` among all bounded adapted
  feasible processes, for any expectation system with the pull-out property),
  **`fn71_timeless_optimal`** (any `x_{−1}`: optimal subject to the timeless constraint on
  `π_0`), **`fn71_annualized`** (in annualised units the weight is `16κφ`).
-/

namespace Woodford.StabilizationWelfare.TidyR5CommitLQ

open Filter Topology Sequences PriceStability

/-! ## The path driven by a root of the characteristic polynomial -/

/-- Woodford (2003), p. 414 and Ch. 7, §1: the multiplier path `μ_t = μ̄(1 − z^{t+1})` of the
date-0 commitment (`μ_{−1} = 0`). -/
noncomputable def muP (mb z : ℝ) (t : ℕ) : ℝ := mb * (1 - z ^ (t + 1))

/-- Woodford (2003), p. 414: inflation from the first-order condition,
`π_t = (b/β)μ_{t−1} − μ_t` with `μ_{−1} = 0`. -/
noncomputable def piP (b β mb z : ℝ) (t : ℕ) : ℝ := b / β * lagS 0 (muP mb z) t - muP mb z t

/-- Woodford (2003), p. 414: the output gap from the first-order condition,
`x_t = x* + (κ/λ)μ_t`. -/
noncomputable def xP (κ lam xs mb z : ℝ) (t : ℕ) : ℝ := xs + κ / lam * muP mb z t

/-- Woodford (2003), p. 414: the lagged multiplier of the date-0 path is
`μ_{t−1} = μ̄(1 − zᵗ)` (also at `t = 0`, where it is `0`). -/
theorem lag_muP (mb z : ℝ) (t : ℕ) : lagS 0 (muP mb z) t = mb * (1 - z ^ t) := by
  cases t with
  | zero => simp
  | succ t => simp [muP]

/-- Woodford (2003), (2.18) and (3.5), pp. 399, 413 (**the path solves the AS relation**): if
`z` is a root of `bz² − (1 + b²/β + c)z + b/β` with `c = κ²/λ` and `μ̄` solves the steady-state
relation `μ̄((b/β) − 1 − b²/β + b − c) = κx*`, then `π_t = κx_t + bπ_{t+1}`. -/
theorem path_AS {b β κ lam xs mb z : ℝ}
    (hz : b * z ^ 2 - (1 + b ^ 2 / β + κ ^ 2 / lam) * z + b / β = 0)
    (hmb : mb * (b / β - 1 - b ^ 2 / β + b - κ ^ 2 / lam) = κ * xs) :
    ASb κ b (piP b β mb z) (xP κ lam xs mb z) := by
  intro t
  simp only [piP, xP, lag_muP, muP]
  rw [show t + 1 + 1 = t + 2 by ring]
  linear_combination hmb - mb * z ^ t * hz

/-- Woodford (2003), p. 415 (**the path solves the first-order conditions**
`π_t + μ_t − (b/β)μ_{t−1} = 0`, `λ(x_t − x*) = κμ_t`, `μ_{−1} = 0`). -/
theorem path_FOC {b β κ lam xs mb z : ℝ} (hlam : lam ≠ 0) :
    CommitFOC b β κ lam xs (piP b β mb z) (xP κ lam xs mb z) (muP mb z) := by
  intro t
  refine ⟨by simp only [piP]; ring, ?_⟩
  simp only [xP]
  field_simp
  ring

/-- Woodford (2003), p. 414: for `|z| ≤ 1` the multiplier path is bounded. -/
theorem bdd_muP {mb z : ℝ} (hz : |z| ≤ 1) : Bdd (muP mb z) := by
  refine ⟨|mb| * 2, fun t => ?_⟩
  simp only [muP, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |1 - z ^ (t + 1)| ≤ |1| + |z ^ (t + 1)| := abs_sub _ _
    _ ≤ 1 + 1 := by
        rw [abs_one, abs_pow]
        gcongr
        exact pow_le_one₀ (abs_nonneg z) hz
    _ = 2 := by norm_num

/-- Woodford (2003), p. 414: the inflation path is bounded. -/
theorem bdd_piP {b β mb z : ℝ} (hz : |z| ≤ 1) : Bdd (piP b β mb z) :=
  ((Bdd.const (b / β)).mul ((bdd_muP hz).lagS 0)).sub (bdd_muP hz)

/-- Woodford (2003), p. 414: the output-gap path is bounded. -/
theorem bdd_xP {κ lam xs mb z : ℝ} (hz : |z| ≤ 1) : Bdd (xP κ lam xs mb z) :=
  (Bdd.const xs).add ((Bdd.const (κ / lam)).mul (bdd_muP hz))

/-! ## The stable root -/

/-- Woodford (2003), Ch. 7, (1.20): the smaller root of `βz² − (1 + β + c)z + 1`. -/
noncomputable def zRoot (β c : ℝ) : ℝ :=
  ((1 + β + c) - Real.sqrt ((1 + β + c) ^ 2 - 4 * β)) / (2 * β)

/-- Woodford (2003), Ch. 7, (1.20) (**the stable root**): for `0 < β < 1` and `c > 0`,
`0 < z < 1` and `βz² − (1 + β + c)z + 1 = 0`. -/
theorem zRoot_props {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    0 < zRoot β c ∧ zRoot β c < 1 ∧ β * zRoot β c ^ 2 - (1 + β + c) * zRoot β c + 1 = 0 := by
  unfold zRoot
  set A := 1 + β + c with hA
  set D := A ^ 2 - 4 * β with hD
  have hDpos : (1 - β + c) ^ 2 < D := by rw [hD, hA]; nlinarith
  have hD0 : 0 < D := lt_of_le_of_lt (sq_nonneg _) hDpos
  set q := Real.sqrt D with hq
  have hqq : q * q = D := Real.mul_self_sqrt hD0.le
  have hq1 : 1 - β + c < q := by rw [hq]; exact Real.lt_sqrt_of_sq_lt hDpos
  have hqA : q < A := by
    rw [hq, Real.sqrt_lt' (by linarith)]; rw [hD]; nlinarith
  refine ⟨by apply div_pos <;> linarith, by rw [div_lt_one (by linarith)]; linarith, ?_⟩
  field_simp
  rw [hD] at hqq
  nlinarith

/-! ## The date-0 optimal commitment with the AS relation (2.18) -/

/-- Woodford (2003), p. 415: the steady-state multiplier `μ̄ = −λx*/κ`. -/
noncomputable def muBar (κ lam xs : ℝ) : ℝ := -(lam * xs / κ)

/-- Woodford (2003), p. 414: the stable root for (2.18), `z` with `c = κ²/λ`. -/
noncomputable def zD (β κ lam : ℝ) : ℝ := zRoot β (κ ^ 2 / lam)

/-- Woodford (2003), pp. 413–415: the date-0 optimal multiplier path. -/
noncomputable def muD (β κ lam xs : ℝ) : ℕ → ℝ := muP (muBar κ lam xs) (zD β κ lam)

/-- Woodford (2003), pp. 413–415: the date-0 optimal inflation path. -/
noncomputable def piD (β κ lam xs : ℝ) : ℕ → ℝ := piP β β (muBar κ lam xs) (zD β κ lam)

/-- Woodford (2003), pp. 413–415: the date-0 optimal output-gap path. -/
noncomputable def xD (β κ lam xs : ℝ) : ℕ → ℝ := xP κ lam xs (muBar κ lam xs) (zD β κ lam)

/-- Woodford (2003), p. 414: properties of the root `z` of the date-0 problem. -/
theorem zD_props {β κ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    0 < zD β κ lam ∧ zD β κ lam < 1 ∧
      β * zD β κ lam ^ 2 - (1 + β + κ ^ 2 / lam) * zD β κ lam + 1 = 0 :=
  zRoot_props hβ0 hβ1 (by positivity)

/-- **Woodford (2003), pp. 413–415 (existence of the date-0 optimal commitment).** For
`0 < β < 1`, `κ, λ > 0` and any `x*`, the explicit path solves the AS relation (2.18), the
first-order conditions of the date-0 problem (`μ_{−1} = 0`) and is bounded. -/
theorem date0_exists {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) :
    ASb κ β (piD β κ lam xs) (xD β κ lam xs) ∧
      CommitFOC β β κ lam xs (piD β κ lam xs) (xD β κ lam xs) (muD β κ lam xs) ∧
      Bdd (piD β κ lam xs) ∧ Bdd (xD β κ lam xs) ∧ Bdd (muD β κ lam xs) := by
  obtain ⟨hz0, hz1, hz⟩ := zD_props (lam := lam) hβ0 hβ1 hκ hlam
  have hzabs : |zD β κ lam| ≤ 1 := by rw [abs_of_pos hz0]; exact hz1.le
  refine ⟨path_AS ?_ ?_, path_FOC hlam.ne', bdd_piP hzabs, bdd_xP hzabs, bdd_muP hzabs⟩
  · have hβ : β ≠ 0 := hβ0.ne'
    have e1 : β ^ 2 / β = β := by field_simp
    have e2 : β / β = 1 := div_self hβ
    rw [e1, e2]
    linear_combination hz
  · unfold muBar
    have hβ : β ≠ 0 := hβ0.ne'
    have e1 : β ^ 2 / β = β := by field_simp
    have e2 : β / β = 1 := div_self hβ
    rw [e1, e2]
    field_simp
    ring

/-- **Woodford (2003), pp. 413–415 and Ch. 7 (the date-0 optimal commitment is optimal and
unique).** Among all bounded paths satisfying (2.18), the date-0 path minimises the discounted
loss `∑ βᵗ[π_t² + λ(x_t − x*)²]`, and any bounded feasible path with the same loss is it. -/
theorem date0_optimal {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {π' x' : ℕ → ℝ} (hπ' : Bdd π') (hx' : Bdd x') (hAS' : ASb κ β π' x') :
    Jloss β lam xs (piD β κ lam xs) (xD β κ lam xs) ≤ Jloss β lam xs π' x' ∧
      (Jloss β lam xs π' x' = Jloss β lam xs (piD β κ lam xs) (xD β κ lam xs) →
        π' = piD β κ lam xs ∧ x' = xD β κ lam xs) := by
  obtain ⟨hAS, hF, hπ, hx, hμ⟩ := date0_exists (xs := xs) hβ0 hβ1 hκ hlam
  exact commit_optimal hβ0 hβ1 hlam hπ hx hμ hAS hF hπ' hx' hAS'

/-- Woodford (2003), p. 414 (**the date-0 path in closed form**):
`π_t = (λx*/κ)(1 − z)zᵗ`, `x_t = x*z^{t+1}`, `μ_t = μ̄(1 − z^{t+1})`. -/
theorem date0_formula {β κ lam xs : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (t : ℕ) :
    piD β κ lam xs t = lam * xs / κ * (1 - zD β κ lam) * zD β κ lam ^ t ∧
      xD β κ lam xs t = xs * zD β κ lam ^ (t + 1) ∧
      muD β κ lam xs t = muBar κ lam xs * (1 - zD β κ lam ^ (t + 1)) := by
  refine ⟨?_, ?_, rfl⟩
  · simp only [piD, piP, lag_muP, muP, muBar]
    rw [div_self hβ0.ne']
    ring
  · simp only [xD, xP, muP, muBar]
    field_simp
    ring

/-- **Woodford (2003), p. 414 ("it is optimal to arrange an initial inflation … the optimal
policy involves positive inflation in subsequent periods as well").** If `x* > 0`, inflation on
the date-0 optimal path is strictly positive at every date. -/
theorem date0_positive {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hxs : 0 < xs) (t : ℕ) : 0 < piD β κ lam xs t := by
  obtain ⟨hz0, hz1, -⟩ := zD_props (lam := lam) hβ0 hβ1 hκ hlam
  rw [(date0_formula (xs := xs) hβ0 hκ hlam t).1]
  have : 0 < 1 - zD β κ lam := by linarith
  positivity

/-- **Woodford (2003), pp. 414–415 (convergence): the date-0 optimal commitment converges to
the timeless plan** `π = 0`, `x = 0`, `μ = μ̄`: "the deterministic path for planned inflation
should converge asymptotically to zero". -/
theorem date0_tendsto {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) :
    Tendsto (piD β κ lam xs) atTop (𝓝 0) ∧ Tendsto (xD β κ lam xs) atTop (𝓝 0) ∧
      Tendsto (muD β κ lam xs) atTop (𝓝 (muBar κ lam xs)) := by
  obtain ⟨hz0, hz1, -⟩ := zD_props (lam := lam) hβ0 hβ1 hκ hlam
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hz0.le hz1
  have hp1 : Tendsto (fun t : ℕ => zD β κ lam ^ (t + 1)) atTop (𝓝 0) :=
    hp.comp (tendsto_add_atTop_nat 1)
  refine ⟨?_, ?_, ?_⟩
  · have h := hp.const_mul (lam * xs / κ * (1 - zD β κ lam))
    rw [mul_zero] at h
    exact h.congr fun t => (date0_formula hβ0 hκ hlam t).1.symm
  · have h := hp1.const_mul xs
    rw [mul_zero] at h
    exact h.congr fun t => (date0_formula hβ0 hκ hlam t).2.1.symm
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hp1 |>.const_mul (muBar κ lam xs)
    rw [sub_zero, mul_one] at h
    exact h.congr fun t => (date0_formula hβ0 hκ hlam t).2.2.symm

/-- Woodford (2003), p. 415 (**the rate of convergence**): the date-0 path approaches the
timeless plan geometrically at the rate of the stable root,
`|π_t| + |x_t| + |μ_t − μ̄| ≤ C zᵗ`. -/
theorem date0_geometric {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) :
    ∃ C, ∀ t, |piD β κ lam xs t| + |xD β κ lam xs t| + |muD β κ lam xs t - muBar κ lam xs| ≤
      C * zD β κ lam ^ t := by
  obtain ⟨hz0, hz1, -⟩ := zD_props (lam := lam) hβ0 hβ1 hκ hlam
  refine ⟨|lam * xs / κ * (1 - zD β κ lam)| + |xs| + |muBar κ lam xs|, fun t => ?_⟩
  obtain ⟨e1, e2, e3⟩ := date0_formula (xs := xs) hβ0 hκ hlam t
  have hzt : 0 ≤ zD β κ lam ^ t := pow_nonneg hz0.le t
  have hz' : zD β κ lam ^ (t + 1) ≤ zD β κ lam ^ t :=
    pow_le_pow_of_le_one hz0.le hz1.le (Nat.le_succ t)
  have hz'0 : 0 ≤ zD β κ lam ^ (t + 1) := pow_nonneg hz0.le _
  rw [e1, e2, e3]
  have a1 : |lam * xs / κ * (1 - zD β κ lam) * zD β κ lam ^ t| =
      |lam * xs / κ * (1 - zD β κ lam)| * zD β κ lam ^ t := by
    rw [abs_mul, abs_of_nonneg hzt]
  have a2 : |xs * zD β κ lam ^ (t + 1)| ≤ |xs| * zD β κ lam ^ t := by
    rw [abs_mul, abs_of_nonneg hz'0]
    exact mul_le_mul_of_nonneg_left hz' (abs_nonneg _)
  have a3 : |muBar κ lam xs * (1 - zD β κ lam ^ (t + 1)) - muBar κ lam xs| ≤
      |muBar κ lam xs| * zD β κ lam ^ t := by
    rw [show muBar κ lam xs * (1 - zD β κ lam ^ (t + 1)) - muBar κ lam xs =
      -(muBar κ lam xs * zD β κ lam ^ (t + 1)) by ring, abs_neg, abs_mul, abs_of_nonneg hz'0]
    exact mul_le_mul_of_nonneg_left hz' (abs_nonneg _)
  rw [a1]
  nlinarith [abs_nonneg (muBar κ lam xs)]

/-- **Woodford (2003), p. 415 (the long-run inflation rate of the optimal commitment is zero,
unconditionally).** For `0 < β < 1`, `κ, λ > 0` and any `x*` (in particular an inefficiently
low natural rate, `x* > 0`), the date-0 optimal commitment EXISTS, is the unique bounded optimum,
and its inflation rate converges to zero; the limit relations of
`PriceStability.longrun_inflation_zero` are therefore satisfied by an actual path. -/
theorem longrun_zero {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) :
    ∃ π x μ : ℕ → ℝ, ASb κ β π x ∧ CommitFOC β β κ lam xs π x μ ∧ Bdd π ∧ Bdd x ∧
      (∀ π' x' : ℕ → ℝ, Bdd π' → Bdd x' → ASb κ β π' x' →
        Jloss β lam xs π x ≤ Jloss β lam xs π' x') ∧
      Tendsto π atTop (𝓝 0) ∧ Tendsto x atTop (𝓝 0) ∧ Tendsto μ atTop (𝓝 (-(lam * xs / κ))) := by
  obtain ⟨hAS, hF, hπ, hx, -⟩ := date0_exists (xs := xs) hβ0 hβ1 hκ hlam
  obtain ⟨t1, t2, t3⟩ := date0_tendsto (xs := xs) hβ0 hβ1 hκ hlam
  exact ⟨_, _, _, hAS, hF, hπ, hx, fun π' x' h1 h2 h3 =>
    (date0_optimal hβ0 hβ1 hκ hlam h1 h2 h3).1, t1, t2, t3⟩

/-! ## The timeless perspective -/

/-- Woodford (2003), p. 415 and Ch. 7, §1 (**the first-order conditions with an initial
multiplier** `μ_{−1}`): `π_t + μ_t − (b/β)μ_{t−1} = 0`, `λ(x_t − x*) = κμ_t`. The date-0 problem
is `μ_{−1} = 0`; the timeless perspective takes `μ_{−1}` from the commitment "made far in the
past". -/
def CommitFOCm (b β κ lam xs μm1 : ℝ) (π x μ : ℕ → ℝ) : Prop :=
  ∀ t, π t + μ t - b / β * lagS μm1 μ t = 0 ∧ lam * (x t - xs) = κ * μ t

/-- **Woodford (2003), p. 415 and Ch. 7 (the gap identity with an initial multiplier).** For a
bounded path satisfying the AS relation and the first-order conditions with `μ_{−1}`, every
other bounded feasible path has
`J' = J + ∑ βᵗ[(π'_t − π_t)² + λ(x'_t − x_t)²] + 2(b/β)μ_{−1}(π'_0 − π_0)`. -/
theorem commit_gap_init {b β κ lam xs μm1 : ℝ} (h0 : 0 < β) (h1 : β < 1)
    {π x μ π' x' : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x) (hμ : Bdd μ) (hπ' : Bdd π') (hx' : Bdd x')
    (hAS : ASb κ b π x) (hFOC : CommitFOCm b β κ lam xs μm1 π x μ) (hAS' : ASb κ b π' x') :
    Jloss β lam xs π' x' = Jloss β lam xs π x +
      ∑' t, β ^ t * ((π' t - π t) ^ 2 + lam * (x' t - x t) ^ 2) +
        2 * (b / β * μm1 * (π' 0 - π 0)) := by
  have hL : Bdd (fun t => π t ^ 2 + lam * (x t - xs) ^ 2) :=
    (hπ.pow 2).add ((Bdd.const lam).mul ((hx.sub (Bdd.const xs)).pow 2))
  have hD : Bdd (fun t => (π' t - π t) ^ 2 + lam * (x' t - x t) ^ 2) :=
    ((hπ'.sub hπ).pow 2).add ((Bdd.const lam).mul ((hx'.sub hx).pow 2))
  have hK : Bdd (fun t => 2 * (b / β * lagS μm1 μ t * (π' t - π t))) :=
    (Bdd.const 2).mul (((Bdd.const _).mul (hμ.lagS μm1)).mul (hπ'.sub hπ))
  have hβ : β * (b / β) = b := mul_div_cancel₀ b h0.ne'
  unfold Jloss
  rw [tsum_telescope_add h0.le h1 (hL.add hD) hK (fun t => ?_)]
  · simp only [lagS_zero]
    rw [(hL.summable h0.le h1).tsum_add (hD.summable h0.le h1) |>.symm]
    congr 1
    exact tsum_congr fun t => by ring
  · obtain ⟨hf1, hf2⟩ := hFOC t
    have ha := hAS t
    have ha' := hAS' t
    simp only [lagS_succ]
    linear_combination (2 * (π' t - π t)) * hf1 + (2 * (x' t - x t)) * hf2 +
      (-2 * μ t) * (ha' - ha) + (2 * μ t * (π' (t + 1) - π (t + 1))) * hβ

/-- Woodford (2003), p. 415: the timeless plan `π_t = 0`, `x_t = 0`, `μ_t = μ̄ = −λx*/κ`
solves (2.18) and the first-order conditions with `μ_{−1} = μ̄`. -/
theorem timeless_plan {β κ lam xs : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) :
    ASb κ β (fun _ => 0) (fun _ => 0) ∧
      CommitFOCm β β κ lam xs (muBar κ lam xs) (fun _ => 0) (fun _ => 0)
        (fun _ => muBar κ lam xs) := by
  refine ⟨fun t => by ring, fun t => ⟨?_, ?_⟩⟩
  · cases t <;> simp [div_self hβ]
  · unfold muBar; field_simp; ring

/-- **Woodford (2003), p. 415 ("if one … should actually conduct policy as one would have
optimally committed to do far in the past … then it is optimal simply to choose `π_t = 0` at all
times").** For `0 < β < 1`, `κ ≠ 0`, `λ > 0`: among all bounded paths satisfying (2.18) and the
timeless constraint `π'_0 = 0`, the zero-inflation plan minimises the discounted loss, and it is
the only minimiser. -/
theorem timeless_zero_optimal {β κ lam xs : ℝ} (h0 : 0 < β) (h1 : β < 1) (hκ : κ ≠ 0)
    (hlam : 0 < lam) {π' x' : ℕ → ℝ} (hπ' : Bdd π') (hx' : Bdd x') (hAS' : ASb κ β π' x')
    (h0' : π' 0 = 0) :
    Jloss β lam xs (fun _ => 0) (fun _ => 0) ≤ Jloss β lam xs π' x' ∧
      (Jloss β lam xs π' x' = Jloss β lam xs (fun _ => 0) (fun _ => 0) →
        π' = (fun _ => 0) ∧ x' = (fun _ => 0)) := by
  obtain ⟨hAS, hF⟩ := timeless_plan (lam := lam) (xs := xs) h0.ne' hκ
  have hg := commit_gap_init h0 h1 (Bdd.const 0) (Bdd.const 0) (Bdd.const _) hπ' hx' hAS hF hAS'
  rw [h0', sub_zero, mul_zero, mul_zero, add_zero] at hg
  rw [hg]
  have hnn : 0 ≤ ∑' t, β ^ t * ((π' t - 0) ^ 2 + lam * (x' t - 0) ^ 2) :=
    tsum_nonneg fun t => mul_nonneg (pow_nonneg h0.le t) (by positivity)
  refine ⟨by linarith, fun h => ?_⟩
  have hz : ∑' t, β ^ t * ((π' t - 0) ^ 2 + lam * (x' t - 0) ^ 2) = 0 := by linarith
  have := (zero_loss_iff h0 h1 hlam (hπ'.sub (Bdd.const 0)) (hx'.sub (Bdd.const 0))).mp hz
  exact ⟨funext fun t => by linarith [(this t).1], funext fun t => by linarith [(this t).2]⟩

/-! ## The "simplified" AS relation with a unit coefficient (p. 415) -/

/-- Woodford (2003), p. 415: the stable root for the unit coefficient, the smaller root of
`βz² − (1 + β + βc)z + 1` (`c = κ²/λ`), equivalently of `z² − (1 + 1/β + c)z + 1/β`. -/
noncomputable def zOne (β κ lam : ℝ) : ℝ := zRoot β (β * (κ ^ 2 / lam))

/-- Woodford (2003), p. 415: the date-0 inflation path with the unit coefficient. -/
noncomputable def piOne (β κ lam xs : ℝ) : ℕ → ℝ := piP 1 β (muBar κ lam xs) (zOne β κ lam)

/-- Woodford (2003), p. 415: the date-0 output-gap path with the unit coefficient. -/
noncomputable def xOne (β κ lam xs : ℝ) : ℕ → ℝ := xP κ lam xs (muBar κ lam xs) (zOne β κ lam)

/-- Woodford (2003), p. 415: the date-0 multiplier path with the unit coefficient. -/
noncomputable def muOne (β κ lam xs : ℝ) : ℕ → ℝ := muP (muBar κ lam xs) (zOne β κ lam)

/-- **Woodford (2003), p. 415 (existence of the date-0 optimal commitment under the
"simplified" AS relation `π_t = κx_t + π_{t+1}`)**: the explicit path solves it, the first-order
conditions with `b = 1`, is bounded, and is the unique optimum among bounded feasible paths. -/
theorem date0_one_exists {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) :
    ASb κ 1 (piOne β κ lam xs) (xOne β κ lam xs) ∧
      CommitFOC 1 β κ lam xs (piOne β κ lam xs) (xOne β κ lam xs) (muOne β κ lam xs) ∧
      Bdd (piOne β κ lam xs) ∧ Bdd (xOne β κ lam xs) ∧
      ∀ π' x' : ℕ → ℝ, Bdd π' → Bdd x' → ASb κ 1 π' x' →
        Jloss β lam xs (piOne β κ lam xs) (xOne β κ lam xs) ≤ Jloss β lam xs π' x' := by
  obtain ⟨hz0, hz1, hz⟩ := zRoot_props hβ0 hβ1 (by positivity : 0 < β * (κ ^ 2 / lam))
  have hzabs : |zOne β κ lam| ≤ 1 := by
    unfold zOne; rw [abs_of_pos hz0]; exact hz1.le
  have hAS : ASb κ 1 (piOne β κ lam xs) (xOne β κ lam xs) := by
    refine path_AS ?_ ?_
    · have hβ : β ≠ 0 := hβ0.ne'
      set z := zRoot β (β * (κ ^ 2 / lam)) with hzd
      set c := κ ^ 2 / lam with hc
      have e : 1 * z ^ 2 - (1 + 1 ^ 2 / β + c) * z + 1 / β =
          (β * z ^ 2 - (1 + β + β * c) * z + 1) / β := by
        field_simp
        ring
      change 1 * z ^ 2 - (1 + 1 ^ 2 / β + c) * z + 1 / β = 0
      rw [e, hz, zero_div]
    · unfold muBar
      field_simp
      ring
  have hF : CommitFOC 1 β κ lam xs (piOne β κ lam xs) (xOne β κ lam xs) (muOne β κ lam xs) :=
    path_FOC hlam.ne'
  refine ⟨hAS, hF, bdd_piP hzabs, bdd_xP hzabs, fun π' x' h1 h2 h3 =>
    (commit_optimal hβ0 hβ1 hlam (bdd_piP hzabs) (bdd_xP hzabs) (bdd_muP hzabs) hAS hF h1 h2
      h3).1⟩

/-- **Woodford (2003), p. 415 (with a unit coefficient on expected inflation the optimal
long-run inflation rate is negative, unconditionally).** The date-0 optimal path converges, with
`π_t → −(1 − β)λx*/(βκ)` and `x_t → 0`. -/
theorem date0_one_tendsto {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) :
    Tendsto (piOne β κ lam xs) atTop (𝓝 (-((1 - β) * lam * xs / (β * κ)))) ∧
      Tendsto (xOne β κ lam xs) atTop (𝓝 0) := by
  obtain ⟨hz0, hz1, -⟩ := zRoot_props hβ0 hβ1 (by positivity : 0 < β * (κ ^ 2 / lam))
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hz0.le hz1
  have hp1 : Tendsto (fun t : ℕ => zRoot β (β * (κ ^ 2 / lam)) ^ (t + 1)) atTop (𝓝 0) :=
    hp.comp (tendsto_add_atTop_nat 1)
  constructor
  · have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul
      (1 / β * muBar κ lam xs)).sub (((tendsto_const_nhds (x := (1 : ℝ))).sub hp1).const_mul
        (muBar κ lam xs))
    have e : 1 / β * muBar κ lam xs * (1 - 0) - muBar κ lam xs * (1 - 0) =
        -((1 - β) * lam * xs / (β * κ)) := by
      unfold muBar; field_simp; ring
    rw [e] at h
    refine h.congr fun t => ?_
    simp only [piOne, piP, lag_muP, muP, zOne]
    ring
  · have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hp1).const_mul (κ / lam * muBar κ lam xs)
      |>.const_add xs
    have e : xs + κ / lam * muBar κ lam xs * (1 - 0) = 0 := by
      unfold muBar; field_simp; ring
    rw [e] at h
    refine h.congr fun t => ?_
    simp only [xOne, xP, muP, zOne]
    ring

/-- **Woodford (2003), p. 415, made unconditional**: with a unit coefficient on expected inflation
the optimal commitment EXISTS and its long-run inflation rate is strictly negative when `x* > 0`
(while the long-run output gap is zero). -/
theorem longrun_negative {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hxs : 0 < xs) :
    ∃ πbar, πbar < 0 ∧ Tendsto (piOne β κ lam xs) atTop (𝓝 πbar) ∧
      Tendsto (xOne β κ lam xs) atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := date0_one_tendsto (xs := xs) hβ0 hβ1 hκ hlam
  refine ⟨_, ?_, h1, h2⟩
  rw [neg_lt_zero]
  have : 0 < 1 - β := by linarith
  positivity

/-! ## Uncertainty: the stochastic gap identity -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (4.38), p. 451 (and (2.18) when `u = 0`): the AS relation with a cost-push
term, `π_t = κx_t + βE_tπ_{t+1} + u_t`. -/
def NKPCu (κ β : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • x t + β • 𝔼.E t (π (t + 1)) + u t

/-- Woodford (2003), (3.3) and (2.22): the expected discounted loss
`E_0 ∑ βᵗ[π_t² + λ(x_t − x*)²]` in state `ω`. -/
noncomputable def ELoss (β lam xs : ℝ) (π x : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  𝔼.E 0 (fun ω' => ∑' t, β ^ t * (π t ω' ^ 2 + lam * (x t ω' - xs) ^ 2)) ω

/-- Woodford (2003), (3.3): `E_0 ∑ βᵗ L_t = ∑ βᵗ E_0 L_t` for a bounded loss. -/
theorem E0_tsum_eq {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {L : ℕ → Ω → ℝ}
    (hL : ∀ t ω, |L t ω| ≤ M) (ω : Ω) :
    𝔼.E 0 (fun ω' => ∑' t, β ^ t * L t ω') ω = ∑' t, β ^ t * 𝔼.E 0 (L t) ω := by
  have hb : ∀ k ω', |β ^ k * L k ω'| ≤ β ^ k * M := fun k ω' => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    exact mul_le_mul_of_nonneg_left (hL k ω') (pow_nonneg h0 k)
  rw [𝔼.E_tsum h0 h1 hb 0 ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E 0 (β ^ k • L k) ω = _
  rw [map_smul]
  rfl

/-- `Eₜ` of a product with a function that is pointwise linear. -/
theorem E_lin_comb (t : ℕ) (a b : ℝ) (f g : Ω → ℝ) (ω : Ω) :
    𝔼.E t (fun ω' => a * f ω' + b * g ω') ω = a * 𝔼.E t f ω + b * 𝔼.E t g ω := by
  have e : (fun ω' => a * f ω' + b * g ω') = a • f + b • g := rfl
  rw [e, map_add, map_smul, map_smul]
  rfl

/-- Woodford (2003), p. 414: a deterministic factor pulls out of `Eₜ`. -/
theorem E_const_mul (t : ℕ) (c : ℝ) (f : Ω → ℝ) :
    𝔼.E t (fun ω => c * f ω) = fun ω => c * 𝔼.E t f ω := by
  have e : (fun ω => c * f ω) = c • f := rfl
  rw [e, map_smul]
  rfl

/-- Woodford (2003), Ch. 7, §1: with the pull-out property an adapted factor pulls out of
`Eₜ`. -/
theorem E_adapted_mul (hPO : 𝔼.PullOut) {μ : ℕ → Ω → ℝ} (hμ : 𝔼.Adapted μ) (t : ℕ)
    (f : Ω → ℝ) : 𝔼.E t (fun ω => μ t ω * f ω) = fun ω => μ t ω * 𝔼.E t f ω :=
  hPO t (μ t) f (hμ t)

/-- **Woodford (2003), p. 414 and Ch. 7, §1 (the stochastic gap identity).** Let `(π, x, μ)` be
bounded, satisfy the AS relation with cost-push `u` and the first-order conditions
`π_t + μ_t − μ_{t−1} = 0`, `λ(x_t − x*) = κμ_t` with initial multiplier `μ_{−1}` (a constant),
and let `E_t(μ_t f) = μ_t E_t f` (pull-out for the multiplier: automatic when `μ` is
deterministic, and implied by `ExpectationSystem.PullOut` when `μ` is adapted). Then for every
bounded process `(π', x')` satisfying the same AS relation,
`E_0 L' = E_0 L + E_0 ∑ βᵗ[(π'_t − π_t)² + λ(x'_t − x_t)²] + 2μ_{−1}E_0(π'_0 − π_0)`. -/
theorem gap_stoch {κ β lam xs μm1 M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1)
    {u π x μ π' x' : ℕ → Ω → ℝ} (hAS : NKPCu 𝔼 κ β u π x) (hAS' : NKPCu 𝔼 κ β u π' x')
    (hF1 : ∀ t ω, π t ω + μ t ω - lagP (fun _ => μm1) μ t ω = 0)
    (hF2 : ∀ t ω, lam * (x t ω - xs) = κ * μ t ω)
    (hPO : ∀ t (f : Ω → ℝ), 𝔼.E t (fun ω => μ t ω * f ω) = fun ω => μ t ω * 𝔼.E t f ω)
    (hπ : ∀ t ω, |π t ω| ≤ M) (hx : ∀ t ω, |x t ω| ≤ M) (hμ : ∀ t ω, |μ t ω| ≤ M)
    (hπ' : ∀ t ω, |π' t ω| ≤ M) (hx' : ∀ t ω, |x' t ω| ≤ M) (hm1 : |μm1| ≤ M) (ω : Ω) :
    ELoss 𝔼 β lam xs π' x' ω = ELoss 𝔼 β lam xs π x ω +
      𝔼.E 0 (fun ω' => ∑' t, β ^ t * ((π' t ω' - π t ω') ^ 2 + lam * (x' t ω' - x t ω') ^ 2))
        ω + 2 * (μm1 * 𝔼.E 0 (fun ω' => π' 0 ω' - π 0 ω') ω) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hm1
  -- notation for the differences
  set dπ : ℕ → Ω → ℝ := fun t ω' => π' t ω' - π t ω' with hdπ
  set lμ : ℕ → Ω → ℝ := lagP (fun _ => μm1) μ with hlμ
  have hlμb : ∀ t ω', |lμ t ω'| ≤ M := fun t ω' => by
    cases t with
    | zero => exact hm1
    | succ t => exact hμ t ω'
  have hdπb : ∀ t ω', |dπ t ω'| ≤ 2 * M := fun t ω' => by
    simp only [hdπ]
    calc _ ≤ |π' t ω'| + |π t ω'| := abs_sub _ _
      _ ≤ M + M := add_le_add (hπ' t ω') (hπ t ω')
      _ = 2 * M := by ring
  -- the AS relation in differences
  have hdAS : ∀ t ω', dπ t ω' = κ * (x' t ω' - x t ω') + β * 𝔼.E t (dπ (t + 1)) ω' := by
    intro t ω'
    have e1 := congrFun (hAS t) ω'
    have e2 := congrFun (hAS' t) ω'
    have hE : 𝔼.E t (dπ (t + 1)) ω' = 𝔼.E t (π' (t + 1)) ω' - 𝔼.E t (π (t + 1)) ω' := by
      have e : dπ (t + 1) = π' (t + 1) - π (t + 1) := rfl
      rw [e, map_sub]; rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    rw [hE]; simp only [hdπ]; linarith
  -- the period identity
  have hper : ∀ t ω', π' t ω' ^ 2 + lam * (x' t ω' - xs) ^ 2 =
      (π t ω' ^ 2 + lam * (x t ω' - xs) ^ 2) +
        ((π' t ω' - π t ω') ^ 2 + lam * (x' t ω' - x t ω') ^ 2) +
        (2 * (lμ t ω' * dπ t ω') - 2 * β * (μ t ω' * 𝔼.E t (dπ (t + 1)) ω')) := by
    intro t ω'
    have f1 := hF1 t ω'
    have f2 := hF2 t ω'
    have a := hdAS t ω'
    simp only [hdπ] at a ⊢
    linear_combination (2 * (π' t ω' - π t ω')) * f1 + (2 * (x' t ω' - x t ω')) * f2 -
      2 * μ t ω' * a
  -- bounds for the three pieces
  set BL := M ^ 2 + |lam| * (M + |xs|) ^ 2 with hBL
  have bL : ∀ (p y : ℕ → Ω → ℝ), (∀ t ω, |p t ω| ≤ M) → (∀ t ω, |y t ω| ≤ M) →
      ∀ t ω, |p t ω ^ 2 + lam * (y t ω - xs) ^ 2| ≤ BL := fun p y hp hy t ω' => by
    have hp2 : p t ω' ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hp t ω') 2
    have hy2 : (y t ω' - xs) ^ 2 ≤ (M + |xs|) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add (hy t ω') le_rfl)) 2
    calc _ ≤ |p t ω' ^ 2| + |lam * (y t ω' - xs) ^ 2| := abs_add_le _ _
      _ = p t ω' ^ 2 + |lam| * (y t ω' - xs) ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg (p t ω')), abs_mul,
            abs_of_nonneg (sq_nonneg (y t ω' - xs))]
      _ ≤ M ^ 2 + |lam| * (M + |xs|) ^ 2 := by gcongr
  set BD := (2 * M) ^ 2 + |lam| * (2 * M) ^ 2 with hBD
  have bD : ∀ t ω', |(π' t ω' - π t ω') ^ 2 + lam * (x' t ω' - x t ω') ^ 2| ≤ BD := by
    intro t ω'
    have hdx : |x' t ω' - x t ω'| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [hx' t ω', hx t ω'])
    have e1 : (π' t ω' - π t ω') ^ 2 ≤ (2 * M) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdπb t ω') 2
    have e2 : (x' t ω' - x t ω') ^ 2 ≤ (2 * M) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdx 2
    calc _ ≤ |(π' t ω' - π t ω') ^ 2| + |lam * (x' t ω' - x t ω') ^ 2| := abs_add_le _ _
      _ = (π' t ω' - π t ω') ^ 2 + |lam| * (x' t ω' - x t ω') ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg (π' t ω' - π t ω')), abs_mul,
            abs_of_nonneg (sq_nonneg (x' t ω' - x t ω'))]
      _ ≤ _ := by rw [hBD]; exact add_le_add e1 (mul_le_mul_of_nonneg_left e2 (abs_nonneg lam))
  -- expectations of the cross terms
  set K : ℕ → ℝ := fun t => 𝔼.E 0 (fun ω' => lμ t ω' * dπ t ω') ω with hK
  have hKb : Bdd K := ⟨M * (2 * M), fun t => 𝔼.abs_E_le (fun ω' => by
    rw [abs_mul]; exact mul_le_mul (hlμb t ω') (hdπb t ω') (abs_nonneg _) hM0) 0 ω⟩
  have hcross : ∀ t, 𝔼.E 0 (fun ω' => μ t ω' * 𝔼.E t (dπ (t + 1)) ω') ω = K (t + 1) := by
    intro t
    have e : (fun ω' => μ t ω' * 𝔼.E t (dπ (t + 1)) ω') =
        𝔼.E t (fun ω' => μ t ω' * dπ (t + 1) ω') := (hPO t (dπ (t + 1))).symm
    rw [e, 𝔼.tower (Nat.zero_le t)]
    rfl
  -- assemble
  have hsplitE : ∀ t, 𝔼.E 0 (fun ω' => π' t ω' ^ 2 + lam * (x' t ω' - xs) ^ 2) ω =
      (𝔼.E 0 (fun ω' => π t ω' ^ 2 + lam * (x t ω' - xs) ^ 2) ω +
        𝔼.E 0 (fun ω' => (π' t ω' - π t ω') ^ 2 + lam * (x' t ω' - x t ω') ^ 2) ω) +
        (2 * (K t - β * K (t + 1))) := by
    intro t
    have e : (fun ω' => π' t ω' ^ 2 + lam * (x' t ω' - xs) ^ 2) =
        (fun ω' => π t ω' ^ 2 + lam * (x t ω' - xs) ^ 2) +
        (fun ω' => (π' t ω' - π t ω') ^ 2 + lam * (x' t ω' - x t ω') ^ 2) +
        ((2 : ℝ) • (fun ω' => lμ t ω' * dπ t ω') -
          (2 * β) • (fun ω' => μ t ω' * 𝔼.E t (dπ (t + 1)) ω')) := by
      funext ω'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hper t ω']
    rw [e, map_add, map_add, map_sub, map_smul, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcross t]
    ring
  unfold ELoss
  rw [E0_tsum_eq 𝔼 h0 h1 (bL π' x' hπ' hx') ω, E0_tsum_eq 𝔼 h0 h1 (bL π x hπ hx) ω,
    E0_tsum_eq 𝔼 h0 h1 bD ω]
  have hG1 : Bdd (fun t => 𝔼.E 0 (fun ω' => π t ω' ^ 2 + lam * (x t ω' - xs) ^ 2) ω) :=
    ⟨BL, fun t => 𝔼.abs_E_le (bL π x hπ hx t) 0 ω⟩
  have hG2 : Bdd (fun t => 𝔼.E 0 (fun ω' => (π' t ω' - π t ω') ^ 2 +
      lam * (x' t ω' - x t ω') ^ 2) ω) := ⟨BD, fun t => 𝔼.abs_E_le (bD t) 0 ω⟩
  rw [tsum_telescope_add h0 h1 (hG1.add hG2) ((Bdd.const 2).mul hKb) (fun t => by
    rw [hsplitE t]; ring), ← (hG1.summable h0 h1).tsum_add (hG2.summable h0 h1)]
  have hK0 : K 0 = μm1 * 𝔼.E 0 (fun ω' => π' 0 ω' - π 0 ω') ω := by
    simp only [hK, hlμ, hdπ, lagP]
    have e : (fun ω' => μm1 * (π' 0 ω' - π 0 ω')) = μm1 • fun ω' => π' 0 ω' - π 0 ω' := rfl
    rw [e, map_smul]; rfl
  rw [hK0]
  congr 1
  exact tsum_congr fun t => by ring

/-- **Woodford (2003), p. 414 ("the optimal commitment from date zero onward involves a
deterministic path for inflation; it continues not to be optimal for the inflation rate to respond
at all to real disturbances").** For ANY expectation system, the deterministic date-0 path
minimises the expected discounted loss `E_0 ∑ βᵗ[π_t² + λ(x_t − x*)²]` among all bounded
processes satisfying (2.18) (adapted or not), and the gap equals `E₀` of the discounted squared
deviations. -/
theorem date0_optimal_stoch {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {π' x' : ℕ → Ω → ℝ} (hb' : BoundedProc π') (hbx' : BoundedProc x')
    (hAS' : NKPC 𝔼 κ β π' x') (ω : Ω) :
    ELoss 𝔼 β lam xs (fun t _ => piD β κ lam xs t) (fun t _ => xD β κ lam xs t) ω ≤
        ELoss 𝔼 β lam xs π' x' ω ∧
      ELoss 𝔼 β lam xs π' x' ω =
        ELoss 𝔼 β lam xs (fun t _ => piD β κ lam xs t) (fun t _ => xD β κ lam xs t) ω +
        𝔼.E 0 (fun ω' => ∑' t, β ^ t * ((π' t ω' - piD β κ lam xs t) ^ 2 +
          lam * (x' t ω' - xD β κ lam xs t) ^ 2)) ω := by
  obtain ⟨hAS, hF, ⟨Mπ, hMπ⟩, ⟨Mx, hMx⟩, ⟨Mμ, hMμ⟩⟩ := date0_exists (xs := xs) hβ0 hβ1 hκ hlam
  obtain ⟨Nπ, hNπ⟩ := hb'
  obtain ⟨Nx, hNx⟩ := hbx'
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |Mπ| + |Mx| + |Mμ| + |Nπ| + |Nx| := ⟨_, rfl⟩
  have h1 := abs_nonneg Mπ
  have h2 := abs_nonneg Mx
  have h3 := abs_nonneg Mμ
  have h4 := abs_nonneg Nπ
  have h5 := abs_nonneg Nx
  have b1 : Mπ ≤ M := by rw [hM]; linarith [le_abs_self Mπ]
  have b2 : Mx ≤ M := by rw [hM]; linarith [le_abs_self Mx]
  have b3 : Mμ ≤ M := by rw [hM]; linarith [le_abs_self Mμ]
  have b4 : Nπ ≤ M := by rw [hM]; linarith [le_abs_self Nπ]
  have b5 : Nx ≤ M := by rw [hM]; linarith [le_abs_self Nx]
  have hu : NKPCu 𝔼 κ β (fun _ _ => 0) (fun t _ => piD β κ lam xs t)
      (fun t _ => xD β κ lam xs t) := fun t => by
    funext ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, 𝔼.const, add_zero]
    exact hAS t
  have hu' : NKPCu 𝔼 κ β (fun _ _ => 0) π' x' := fun t => by
    rw [hAS' t]; funext ω'; simp
  have hg := gap_stoch 𝔼 (μm1 := 0) (M := M) hβ0.le hβ1 hu hu'
    (μ := fun t _ => muD β κ lam xs t)
    (fun t ω' => by
      have := (hF t).1
      cases t with
      | zero => simp only [lagP] at this ⊢; rw [div_self hβ0.ne'] at this; simpa using this
      | succ t => simp only [lagP] at this ⊢; rw [div_self hβ0.ne'] at this; simpa using this)
    (fun t ω' => (hF t).2)
    (fun t f => E_const_mul 𝔼 t (muD β κ lam xs t) f)
    (fun t _ => (hMπ t).trans b1) (fun t _ => (hMx t).trans b2) (fun t _ => (hMμ t).trans b3)
    (fun t ω' => (hNπ t ω').trans b4) (fun t ω' => (hNx t ω').trans b5)
    (by rw [abs_zero, hM]; positivity) ω
  rw [zero_mul, mul_zero, add_zero] at hg
  refine ⟨?_, hg⟩
  rw [hg]
  have hnn : (fun _ : Ω => (0 : ℝ)) ≤ fun ω' => ∑' t, β ^ t * ((π' t ω' - piD β κ lam xs t) ^ 2 +
      lam * (x' t ω' - xD β κ lam xs t) ^ 2) := fun ω' =>
    tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0.le t) (by positivity)
  have := 𝔼.mono 0 hnn ω
  rw [𝔼.const] at this
  linarith

/-! ## Footnote 71: complete stabilisation of `log P_t + φx_t` is optimal for `λ = κφ` -/

/-- Woodford (2003), footnote 71 and Ch. 7, (5.1): the forward component
`v_t = ∑ z₂⁻ᵏ E_t[−u_{t+k}/(βφz₂)]`, `z₂ = 1/(βz)` (`z` the stable root with `c = κ/φ`). -/
noncomputable def fnV (β κ φ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (β * zRoot β (κ / φ)) (fun t ω => -(zRoot β (κ / φ) * u t ω / φ))

/-- Woodford (2003), footnote 71: the output gap `x_t = z x_{t−1} + v_t` with given `x_{−1}`. -/
noncomputable def fnX (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => zRoot β (κ / φ) * xm1 + fnV 𝔼 β κ φ u 0 ω
  | t + 1 => fun ω => zRoot β (κ / φ) * fnX β κ φ u xm1 t ω + fnV 𝔼 β κ φ u (t + 1) ω

/-- Woodford (2003), footnote 71: inflation from the targeting rule,
`π_t = −φ(x_t − x_{t−1})`. -/
noncomputable def fnPi (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => -(φ * (fnX 𝔼 β κ φ u xm1 t ω - lagP (fun _ => xm1) (fnX 𝔼 β κ φ u xm1) t ω))

/-- Woodford (2003), footnote 71: `x_t = z x_{t−1} + v_t` at every date. -/
theorem fnX_rec (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 : ℝ) (t : ℕ) (ω : Ω) :
    fnX 𝔼 β κ φ u xm1 t ω = zRoot β (κ / φ) * lagP (fun _ => xm1) (fnX 𝔼 β κ φ u xm1) t ω +
      fnV 𝔼 β κ φ u t ω := by
  cases t <;> rfl

/-- Woodford (2003), footnote 71: for bounded adapted `u` the forward component is bounded,
adapted and solves `v_t = βz E_t v_{t+1} − zu_t/φ`. -/
theorem fnV_props {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    BoundedProc (fnV 𝔼 β κ φ u) ∧ 𝔼.Adapted (fnV 𝔼 β κ φ u) ∧
      ∀ t, fnV 𝔼 β κ φ u t = (β * zRoot β (κ / φ)) • 𝔼.E t (fnV 𝔼 β κ φ u (t + 1)) +
        fun ω => -(zRoot β (κ / φ) * u t ω / φ) := by
  obtain ⟨hz0, hz1, -⟩ := zRoot_props hβ0 hβ1 (div_pos hκ hφ)
  have ha0 : 0 ≤ β * zRoot β (κ / φ) := by positivity
  have ha1 : β * zRoot β (κ / φ) < 1 := by nlinarith
  have hw : ∀ t ω, |(fun t ω => -(zRoot β (κ / φ) * u t ω / φ)) t ω| ≤
      zRoot β (κ / φ) * |M| / φ := fun t ω => by
    simp only [abs_neg, abs_div, abs_mul, abs_of_pos hz0, abs_of_pos hφ]
    rw [div_le_div_iff_of_pos_right hφ]
    exact mul_le_mul_of_nonneg_left ((hu t ω).trans (le_abs_self M)) hz0.le
  have hwa : 𝔼.Adapted (fun t ω => -(zRoot β (κ / φ) * u t ω / φ)) := fun t => by
    change 𝔼.E t (fun ω => -(zRoot β (κ / φ) * u t ω / φ)) = fun ω => -(zRoot β (κ / φ) * u t ω / φ)
    have e : (fun ω => -(zRoot β (κ / φ) * u t ω / φ)) = (-(zRoot β (κ / φ) / φ)) • u t := by
      funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, map_smul, hua t]
  exact ⟨𝔼.forwardSeries_bounded ha0 ha1 hw, 𝔼.forwardSeries_adapted ha0 ha1 hw,
    𝔼.forwardSeries_solves ha0 ha1 hw hwa⟩

/-- Woodford (2003), footnote 71: the output gap of the plan is bounded and adapted. -/
theorem fnX_props {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (xm1 : ℝ) :
    BoundedProc (fnX 𝔼 β κ φ u xm1) ∧ 𝔼.Adapted (fnX 𝔼 β κ φ u xm1) := by
  obtain ⟨hz0, hz1, -⟩ := zRoot_props hβ0 hβ1 (div_pos hκ hφ)
  obtain ⟨⟨V, hV⟩, hVa, -⟩ := fnV_props 𝔼 hβ0 hβ1 hκ hφ hu hua
  set z := zRoot β (κ / φ)
  set B := |xm1| + |V| / (1 - z) with hB
  have h1z : 0 < 1 - z := by linarith
  have hbd : ∀ t ω, |fnX 𝔼 β κ φ u xm1 t ω| ≤ B := by
    have hVB : ∀ t ω, |fnV 𝔼 β κ φ u t ω| ≤ |V| := fun t ω => (hV t ω).trans (le_abs_self V)
    have key : |V| / (1 - z) = z * (|V| / (1 - z)) + |V| := by field_simp; ring
    intro t
    induction t with
    | zero =>
      intro ω
      change |z * xm1 + fnV 𝔼 β κ φ u 0 ω| ≤ B
      calc _ ≤ |z * xm1| + |fnV 𝔼 β κ φ u 0 ω| := abs_add_le _ _
        _ ≤ |xm1| + |V| := by
            rw [abs_mul, abs_of_pos hz0]
            exact add_le_add (by nlinarith [abs_nonneg xm1]) (hVB 0 ω)
        _ ≤ B := by
            simp only [hB]
            have : |V| ≤ |V| / (1 - z) := le_div_self (abs_nonneg _) h1z (by linarith)
            linarith
    | succ t ih =>
      intro ω
      change |z * fnX 𝔼 β κ φ u xm1 t ω + fnV 𝔼 β κ φ u (t + 1) ω| ≤ B
      calc _ ≤ |z * fnX 𝔼 β κ φ u xm1 t ω| + |fnV 𝔼 β κ φ u (t + 1) ω| := abs_add_le _ _
        _ ≤ z * B + |V| := by
            rw [abs_mul, abs_of_pos hz0]
            exact add_le_add (mul_le_mul_of_nonneg_left (ih ω) hz0.le) (hVB _ ω)
        _ ≤ B := by
            simp only [hB]
            nlinarith [abs_nonneg xm1]
  refine ⟨⟨B, hbd⟩, fun t => ?_⟩
  induction t with
  | zero =>
    have e : fnX 𝔼 β κ φ u xm1 0 = (fun _ => z * xm1) + fnV 𝔼 β κ φ u 0 := rfl
    rw [e, map_add, 𝔼.const, hVa 0]
  | succ t ih =>
    have e : fnX 𝔼 β κ φ u xm1 (t + 1) = z • fnX 𝔼 β κ φ u xm1 t + fnV 𝔼 β κ φ u (t + 1) := rfl
    rw [e, map_add, map_smul, hVa (t + 1),
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih]

/-- **Woodford (2003), footnote 71 and (4.38) (the plan is an equilibrium).** For
`0 < β < 1`, `κ, φ > 0` and a bounded adapted cost-push process `u`, the plan
`x_t = zx_{t−1} + v_t`, `π_t = −φ(x_t − x_{t−1})` satisfies `π_t = κx_t + βE_tπ_{t+1} + u_t`. -/
theorem fn71_AS {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (xm1 : ℝ) :
    NKPCu 𝔼 κ β u (fnPi 𝔼 β κ φ u xm1) (fnX 𝔼 β κ φ u xm1) := by
  obtain ⟨hz0, hz1, hz⟩ := zRoot_props hβ0 hβ1 (div_pos hκ hφ)
  obtain ⟨-, -, hVs⟩ := fnV_props 𝔼 hβ0 hβ1 hκ hφ hu hua
  obtain ⟨-, hXa⟩ := fnX_props 𝔼 hβ0 hβ1 hκ hφ hu hua xm1
  set z := zRoot β (κ / φ)
  intro t
  funext ω
  -- `E_t π_{t+1} = −φ(z x_t + E_t v_{t+1} − x_t)`
  have hX1 : fnX 𝔼 β κ φ u xm1 (t + 1) = z • fnX 𝔼 β κ φ u xm1 t + fnV 𝔼 β κ φ u (t + 1) :=
    rfl
  have hP1 : fnPi 𝔼 β κ φ u xm1 (t + 1) =
      (-φ) • fnX 𝔼 β κ φ u xm1 (t + 1) + φ • fnX 𝔼 β κ φ u xm1 t := by
    funext ω'; simp only [fnPi, lagP, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hEP : 𝔼.E t (fnPi 𝔼 β κ φ u xm1 (t + 1)) ω =
      -φ * (z * fnX 𝔼 β κ φ u xm1 t ω + 𝔼.E t (fnV 𝔼 β κ φ u (t + 1)) ω) +
        φ * fnX 𝔼 β κ φ u xm1 t ω := by
    rw [hP1, map_add, map_smul, map_smul, hX1, map_add, map_smul, hXa t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hv := congrFun (hVs t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv
  have hx := fnX_rec 𝔼 β κ φ u xm1 t ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hEP]
  simp only [fnPi]
  set X := fnX 𝔼 β κ φ u xm1 t ω
  set L := lagP (fun _ => xm1) (fnX 𝔼 β κ φ u xm1) t ω
  set V := fnV 𝔼 β κ φ u t ω
  set EV := 𝔼.E t (fnV 𝔼 β κ φ u (t + 1)) ω
  -- `X = zL + V`, `V = βz EV − zu/φ`, `βz² − (1+β+κ/φ)z + 1 = 0`
  have hzne : z ≠ 0 := hz0.ne'
  have hφne : φ ≠ 0 := hφ.ne'
  have hL : L = (X - V) / z := by rw [hx]; field_simp; ring
  have key : -(φ * (X - L)) - (κ * X + β * (-φ * (z * X + EV) + φ * X) + u t ω) =
      φ * X / z * (β * z ^ 2 - (1 + β + κ / φ) * z + 1) := by
    rw [hL, hv]; field_simp; ring
  rw [hz, mul_zero] at key
  linarith

/-- **Woodford (2003), footnote 71 (the plan stabilises `log P_t + φx_t` completely).** With the
price level `p_t = p_{−1} + ∑_{s ≤ t} π_s`, `p_t + φx_t = p_{−1} + φx_{−1}` at every date and in
every state. -/
theorem fn71_targeting (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 pm1 : ℝ) (t : ℕ) (ω : Ω) :
    pm1 + ∑ s ∈ Finset.range (t + 1), fnPi 𝔼 β κ φ u xm1 s ω + φ * fnX 𝔼 β κ φ u xm1 t ω =
      pm1 + φ * xm1 := by
  induction t with
  | zero => simp only [zero_add, Finset.sum_range_one, fnPi, lagP]; ring
  | succ t ih =>
    rw [Finset.sum_range_succ]
    simp only [fnPi, lagP] at ih ⊢
    linarith

/-- Woodford (2003), footnote 71: the multiplier of the plan, `μ_t = φx_t` (`λx_t = κμ_t` with
`λ = κφ`), and its first-order conditions `π_t + μ_t − μ_{t−1} = 0` with `μ_{−1} = φx_{−1}`. -/
theorem fn71_FOC (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 : ℝ) :
    (∀ t ω, fnPi 𝔼 β κ φ u xm1 t ω + φ * fnX 𝔼 β κ φ u xm1 t ω -
        lagP (fun _ => φ * xm1) (fun s ω' => φ * fnX 𝔼 β κ φ u xm1 s ω') t ω = 0) ∧
      ∀ t ω, κ * φ * (fnX 𝔼 β κ φ u xm1 t ω - 0) = κ * (φ * fnX 𝔼 β κ φ u xm1 t ω) := by
  refine ⟨fun t ω => ?_, fun t ω => by ring⟩
  cases t <;> simp only [fnPi, lagP] <;> ring

/-- Woodford (2003), footnote 71 and Ch. 7 (**the gap identity for the targeting-rule plan**):
for bounded `(π', x')` satisfying the AS relation with the same cost-push process,
`E_0 L' = E_0 L + E_0 ∑ βᵗ[(π'_t − π_t)² + κφ(x'_t − x_t)²] + 2φx_{−1}E_0(π'_0 − π_0)`. -/
theorem fn71_gap (hPO : 𝔼.PullOut) {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (xm1 : ℝ) {π' x' : ℕ → Ω → ℝ} (hb' : BoundedProc π') (hbx' : BoundedProc x')
    (hAS' : NKPCu 𝔼 κ β u π' x') (ω : Ω) :
    ELoss 𝔼 β (κ * φ) 0 π' x' ω = ELoss 𝔼 β (κ * φ) 0 (fnPi 𝔼 β κ φ u xm1) (fnX 𝔼 β κ φ u xm1) ω +
      𝔼.E 0 (fun ω' => ∑' t, β ^ t * ((π' t ω' - fnPi 𝔼 β κ φ u xm1 t ω') ^ 2 +
        κ * φ * (x' t ω' - fnX 𝔼 β κ φ u xm1 t ω') ^ 2)) ω +
      2 * (φ * xm1 * 𝔼.E 0 (fun ω' => π' 0 ω' - fnPi 𝔼 β κ φ u xm1 0 ω') ω) := by
  obtain ⟨⟨Bx, hBx⟩, hXa⟩ := fnX_props 𝔼 hβ0 hβ1 hκ hφ hu hua xm1
  obtain ⟨Nπ, hNπ⟩ := hb'
  obtain ⟨Nx, hNx⟩ := hbx'
  have hAS := fn71_AS 𝔼 hβ0 hβ1 hκ hφ hu hua xm1
  obtain ⟨hF1, hF2⟩ := fn71_FOC 𝔼 β κ φ u xm1
  set X := fnX 𝔼 β κ φ u xm1 with hXdef
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |Bx| + |xm1| := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |φ| * (2 * A) + |φ| * A + |Nπ| + |Nx| + A + |φ| * |xm1| :=
    ⟨_, rfl⟩
  have hφA : 0 ≤ |φ| * A := mul_nonneg (abs_nonneg _) hA0
  have hφx : 0 ≤ |φ| * |xm1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hXB : ∀ t ω', |X t ω'| ≤ A := fun t ω' =>
    (hBx t ω').trans ((le_abs_self _).trans (by rw [hA]; linarith [abs_nonneg xm1]))
  have hlagB : ∀ t ω', |lagP (fun _ => xm1) X t ω'| ≤ A := fun t ω' => by
    cases t with
    | zero => simp only [lagP]; rw [hA]; linarith [abs_nonneg Bx]
    | succ t => exact hXB t ω'
  have hPiB : ∀ t ω', |fnPi 𝔼 β κ φ u xm1 t ω'| ≤ B := fun t ω' => by
    simp only [fnPi, abs_neg, abs_mul]
    have := abs_sub (X t ω') (lagP (fun _ => xm1) X t ω')
    have h2 : |φ| * |X t ω' - lagP (fun _ => xm1) X t ω'| ≤ |φ| * (2 * A) :=
      mul_le_mul_of_nonneg_left (this.trans (by linarith [hXB t ω', hlagB t ω']))
        (abs_nonneg _)
    rw [hB]
    linarith [abs_nonneg Nπ, abs_nonneg Nx]
  have hμB : ∀ t ω', |φ * X t ω'| ≤ B := fun t ω' => by
    rw [abs_mul, hB]
    have := mul_le_mul_of_nonneg_left (hXB t ω') (abs_nonneg φ)
    linarith [abs_nonneg Nπ, abs_nonneg Nx]
  have hXB' : ∀ t ω', |X t ω'| ≤ B := fun t ω' => by
    rw [hB]; linarith [hXB t ω', abs_nonneg Nπ, abs_nonneg Nx]
  have hμa : 𝔼.Adapted (fun t ω' => φ * X t ω') := fun t => by
    rw [E_const_mul 𝔼 t φ (X t), hXa t]
  have hg := gap_stoch 𝔼 (μm1 := φ * xm1) (M := B) (lam := κ * φ) (xs := 0) hβ0.le hβ1 hAS hAS'
    (μ := fun t ω' => φ * X t ω') hF1 hF2 (E_adapted_mul 𝔼 hPO hμa)
    hPiB hXB' hμB
    (fun t ω' => (hNπ t ω').trans (by rw [hB]; linarith [le_abs_self Nπ, abs_nonneg Nx]))
    (fun t ω' => (hNx t ω').trans (by rw [hB]; linarith [le_abs_self Nx, abs_nonneg Nπ]))
    (by rw [abs_mul, hB]; linarith [abs_nonneg Nπ, abs_nonneg Nx]) ω
  rw [hg]

/-- **Woodford (2003), footnote 71 and Ch. 7, §5.1 (complete stabilisation of `log P_t + φx_t`
is the date-0 optimal policy for `λ = κφ`).** For an expectation system with the pull-out property,
`0 < β < 1`, `κ, φ > 0` and a bounded adapted cost-push process `u`, the plan with `x_{−1} = 0`
minimises `E_0 ∑ βᵗ[π_t² + κφ x_t²]` among ALL bounded processes satisfying
`π_t = κx_t + βE_tπ_{t+1} + u_t`; the loss gap is `E₀` of the discounted squared deviations. -/
theorem fn71_optimal (hPO : 𝔼.PullOut) {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    {π' x' : ℕ → Ω → ℝ} (hb' : BoundedProc π') (hbx' : BoundedProc x')
    (hAS' : NKPCu 𝔼 κ β u π' x') (ω : Ω) :
    ELoss 𝔼 β (κ * φ) 0 (fnPi 𝔼 β κ φ u 0) (fnX 𝔼 β κ φ u 0) ω ≤ ELoss 𝔼 β (κ * φ) 0 π' x' ω ∧
      ELoss 𝔼 β (κ * φ) 0 π' x' ω = ELoss 𝔼 β (κ * φ) 0 (fnPi 𝔼 β κ φ u 0) (fnX 𝔼 β κ φ u 0) ω +
        𝔼.E 0 (fun ω' => ∑' t, β ^ t * ((π' t ω' - fnPi 𝔼 β κ φ u 0 t ω') ^ 2 +
          κ * φ * (x' t ω' - fnX 𝔼 β κ φ u 0 t ω') ^ 2)) ω := by
  have hg := fn71_gap 𝔼 hPO hβ0 hβ1 hκ hφ hu hua 0 hb' hbx' hAS' ω
  rw [mul_zero, zero_mul, mul_zero, add_zero] at hg
  refine ⟨?_, hg⟩
  rw [hg]
  have hnn : (fun _ : Ω => (0 : ℝ)) ≤ fun ω' => ∑' t, β ^ t *
      ((π' t ω' - fnPi 𝔼 β κ φ u 0 t ω') ^ 2 + κ * φ * (x' t ω' - fnX 𝔼 β κ φ u 0 t ω') ^ 2) :=
    fun ω' => tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0.le t) (by positivity)
  have := 𝔼.mono 0 hnn ω
  rw [𝔼.const] at this
  linarith

/-- **Woodford (2003), footnote 71 and Ch. 7, §5.1 (the timeless perspective).** For any
`x_{−1}`, the plan stabilising `p_t + φx_t` at `p_{−1} + φx_{−1}` minimises
`E_0 ∑ βᵗ[π_t² + κφ x_t²]` among all bounded processes satisfying the AS relation and the
timeless constraint `π'_0 = π_0` (the initial inflation the rule commits to). -/
theorem fn71_timeless_optimal (hPO : 𝔼.PullOut) {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (xm1 : ℝ) {π' x' : ℕ → Ω → ℝ} (hb' : BoundedProc π') (hbx' : BoundedProc x')
    (hAS' : NKPCu 𝔼 κ β u π' x') (h0' : π' 0 = fnPi 𝔼 β κ φ u xm1 0) (ω : Ω) :
    ELoss 𝔼 β (κ * φ) 0 (fnPi 𝔼 β κ φ u xm1) (fnX 𝔼 β κ φ u xm1) ω ≤
      ELoss 𝔼 β (κ * φ) 0 π' x' ω := by
  have hg := fn71_gap 𝔼 hPO hβ0 hβ1 hκ hφ hu hua xm1 hb' hbx' hAS' ω
  have hz : (fun ω' => π' 0 ω' - fnPi 𝔼 β κ φ u xm1 0 ω') = fun _ => 0 := by
    funext ω'; rw [h0']; ring
  rw [hz, 𝔼.const, mul_zero, mul_zero, add_zero] at hg
  rw [hg]
  have hnn : (fun _ : Ω => (0 : ℝ)) ≤ fun ω' => ∑' t, β ^ t *
      ((π' t ω' - fnPi 𝔼 β κ φ u xm1 t ω') ^ 2 +
        κ * φ * (x' t ω' - fnX 𝔼 β κ φ u xm1 t ω') ^ 2) :=
    fun ω' => tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0.le t) (by positivity)
  have := 𝔼.mono 0 hnn ω
  rw [𝔼.const] at this
  linarith

/-- **Woodford (2003), footnote 71 (the weight in annualised units is `16κφ`).** With inflation
measured at annual rates, `(4π)² + λ_a x² = 16(π² + (λ_a/16)x²)`, so the plan stabilising
`log P_t + φx_t` is optimal exactly for the quarterly weight `κφ`, i.e. for
`λ_a = 16κφ = CostPush.lambdaOfPhi κ φ`. -/
theorem fn71_annualized (κ φ π x : ℝ) :
    (4 * π) ^ 2 + CostPush.lambdaOfPhi κ φ * x ^ 2 = 16 * (π ^ 2 + κ * φ * x ^ 2) := by
  unfold CostPush.lambdaOfPhi; ring

end Woodford.StabilizationWelfare.TidyR5CommitLQ
