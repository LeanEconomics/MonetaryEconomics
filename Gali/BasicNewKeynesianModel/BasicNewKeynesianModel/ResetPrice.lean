/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The reset-price problem

Galí (2015), Chapter 3, §3.2.2 (pp. 56–57) and Appendix 3.3 (pp. 84–85).

A firm that resets its price at `t` chooses `P*` to maximise the genuine infinite
discounted sum `∑ₖ θᵏ E_t[Q_{t,t+k}(P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))]` subject to
the demand schedule (9), `Y_{t+k|t} = (P*/P_{t+k})^{−ε} C_{t+k}`. Expectations are
an arbitrary `ExpectationSystem`, so every statement holds under perfect foresight
and under uncertainty.

## Main results

* `E_tsum`: `E_t` commutes with discounted sums of bounded random variables (a
  consequence of the expectation axioms alone).
* `forwardSum_rec`, `forwardSum_unique`, `normForward_rec`, `normForward_unique`:
  recursive forms of discounted forward sums and their uniqueness among bounded
  processes.
* `hasDerivAt_E`, `hasDerivAt_tsum_E`: differentiation under `E_t` and under the
  infinite sum, with explicit Lipschitz and domination hypotheses.
* `hasDerivAt_objective`: the derivative of the objective is
  `((1 − ε)/P*) ∑ₖ θᵏ E_t[Q Y (P* − M Ψ')]`; `foc_of_isLocalMax`: (10) is necessary.
* `isMaxOn_iff_foc`: with convex costs (10) characterises the optimum, and the
  optimum is unique.
* `flexible_foc_iff`, `flexible_price_optimum`: `θ = 0 ⇒ P* = M Ψ'_{t|t}`.
* `steadyState_foc_iff`: in the zero-inflation steady state `P = M Ψ`.
* `hasDerivAt_focLHS_path`, `eq11_iff`: the log-linear rule (11) is exactly the
  vanishing of the derivative of (10) at the steady state along any bounded
  perturbation.
* `resetPrice_recursive`: the recursive form of the pricing rule.
* `reset_prob_sum`, `firmValue_eq`, `isMaxOn_firmValue_iff`: Appendix 3.3, eq. (37).
-/

namespace Gali.BasicNewKeynesianModel.ResetPrice

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Conditional expectations of discounted sums -/

/-- A geometrically weighted series of uniformly bounded random variables
converges at every state (used throughout Galí (2015), ch. 3, e.g. eq. (11), p. 57). -/
theorem summable_geometric_bounded {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) : Summable fun k => a ^ k * y k ω := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)

/-- The bound of a geometrically weighted series of bounded random variables:
`|∑ aᵏ yₖ| ≤ M / (1 − |a|)` (Galí (2015), ch. 3, p. 57). -/
theorem abs_tsum_geometric_le {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) :
    |∑' k, a ^ k * y k ω| ≤ M / (1 - |a|) := by
  have hs := summable_geometric_bounded ha hy ω
  have hg : Summable fun k => |a| ^ k * M :=
    (summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M
  have h1 : |∑' k, a ^ k * y k ω| ≤ ∑' k, |a ^ k * y k ω| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k => a ^ k * y k ω)
        (by simpa only [Real.norm_eq_abs] using hs.abs)
  have h2 : ∑' k, |a ^ k * y k ω| ≤ ∑' k, |a| ^ k * M := by
    refine Summable.tsum_le_tsum (fun k => ?_) hs.abs hg
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)
  rw [tsum_mul_right, tsum_geometric_of_lt_one (abs_nonneg a) ha] at h2
  calc |∑' k, a ^ k * y k ω| ≤ (1 - |a|)⁻¹ * M := h1.trans h2
    _ = M / (1 - |a|) := by rw [div_eq_inv_mul]

/-- **Conditional expectations commute with discounted sums.** For uniformly
bounded random variables and `|a| < 1`,
`E_t[∑ₖ aᵏ yₖ] = ∑ₖ aᵏ E_t yₖ`. This is the interchange used whenever Galí (2015)
writes `E_t` inside an infinite discounted sum (eqs. (10), (11), (16), pp. 56–60).
It follows from the expectation axioms alone: `E_t` is monotone and preserves
constants, so it is continuous for the uniform norm. -/
theorem E_tsum {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (t : ℕ) :
    𝔼.E t (fun ω => ∑' k, a ^ k * y k ω) = fun ω => ∑' k, a ^ k * 𝔼.E t (y k) ω := by
  funext ω
  set F : Ω → ℝ := fun ω => ∑' k, a ^ k * y k ω with hF
  set Fn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, a ^ k • y k with hFn
  set T : ℕ → ℝ := fun n => ∑' k, |a| ^ (k + n) * M with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add fun k => |a| ^ k * M
  have htail : ∀ n ω', |F ω' - Fn n ω'| ≤ T n := by
    intro n ω'
    have hs := summable_geometric_bounded ha hy ω'
    have hsplit := hs.sum_add_tsum_nat_add n
    have hFn' : Fn n ω' = ∑ k ∈ Finset.range n, a ^ k * y k ω' := by
      simp [hFn, Finset.sum_apply]
    rw [hFn']
    change |∑' k, a ^ k * y k ω' - _| ≤ T n
    rw [← hsplit, add_sub_cancel_left]
    have hs' : Summable fun k => a ^ (k + n) * y (k + n) ω' :=
      (summable_nat_add_iff n).mpr hs
    have hg : Summable fun k => |a| ^ (k + n) * M :=
      (summable_nat_add_iff n).mpr
        ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    calc |∑' k, a ^ (k + n) * y (k + n) ω'| ≤ ∑' k, |a ^ (k + n) * y (k + n) ω'| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => a ^ (k + n) * y (k + n) ω')
              (by simpa only [Real.norm_eq_abs] using hs'.abs)
      _ ≤ T n := by
          refine Summable.tsum_le_tsum (fun k => ?_) hs'.abs hg
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (hy (k + n) ω') (pow_nonneg (abs_nonneg a) _)
  have hEFn : ∀ n, 𝔼.E t (Fn n) ω = ∑ k ∈ Finset.range n, a ^ k * 𝔼.E t (y k) ω := by
    intro n
    simp [hFn, map_sum, map_smul, Finset.sum_apply]
  have hlim1 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop (𝓝 (𝔼.E t F ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hTlim
    have h := 𝔼.abs_E_le (x := F - Fn n) (fun ω' => htail n ω') t ω
    rw [map_sub, Pi.sub_apply] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have hbE : ∀ k ω', |𝔼.E t (y k) ω'| ≤ M := fun k ω' => 𝔼.abs_E_le (hy k) t ω'
  have hlim2 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop
      (𝓝 (∑' k, a ^ k * 𝔼.E t (y k) ω)) := by
    simp_rw [hEFn]
    exact (summable_geometric_bounded ha hbE ω).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim1 hlim2

/-- The discounted forward sum `∑ₖ aᵏ E_t x_{t+k}` of a process (Galí (2015),
eqs. (11) and (16), pp. 57–60, and the forward solution of (17), p. 61). -/
noncomputable def forwardSum (a : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * 𝔼.E t (x (t + k)) ω

/-- The forward sum of a process bounded by `M` is bounded by `M / (1 − |a|)`
(Galí (2015), p. 60). -/
theorem abs_forwardSum_le {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |forwardSum 𝔼 a x t ω| ≤ M / (1 - |a|) :=
  abs_tsum_geometric_le ha (fun k ω' => 𝔼.bounded_E hx t (t + k) ω') ω

/-- The forward sum of a bounded process is a bounded process (Galí (2015), p. 60). -/
theorem forwardSum_bounded {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} (hx : BoundedProc x) :
    BoundedProc (forwardSum 𝔼 a x) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M / (1 - |a|), fun t ω => abs_forwardSum_le 𝔼 ha hM t ω⟩

/-- **Recursive form of a forward sum** (Galí (2015), the step from the series
for `p*` to eq. (16), p. 60): for a bounded adapted process `x`,
`S_t = x_t + a E_t S_{t+1}` where `S_t = ∑ₖ aᵏ E_t x_{t+k}`. -/
theorem forwardSum_rec {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) (t : ℕ) :
    forwardSum 𝔼 a x t = x t + a • 𝔼.E t (forwardSum 𝔼 a x (t + 1)) := by
  have hy : ∀ k ω, |𝔼.E (t + 1) (x (t + 1 + k)) ω| ≤ M :=
    fun k ω => 𝔼.bounded_E hx (t + 1) (t + 1 + k) ω
  have hE : 𝔼.E t (forwardSum 𝔼 a x (t + 1))
      = fun ω => ∑' k, a ^ k * 𝔼.E t (x (t + 1 + k)) ω := by
    unfold forwardSum
    rw [E_tsum 𝔼 ha hy t]
    funext ω
    congr 1
    funext k
    rw [𝔼.tower (Nat.le_succ t)]
  rw [hE]
  funext ω
  have hs := summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hx t (t + k) ω') ω
  simp only [forwardSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, hxa t, ← tsum_mul_left]
  congr 1
  congr 1
  funext k
  rw [pow_succ, show t + (k + 1) = t + 1 + k by omega]
  ring

/-- **Uniqueness of the forward sum** (Galí (2015), p. 60–61): with `|a| < 1`,
the forward sum is the only bounded process satisfying `S_t = x_t + a E_t S_{t+1}`. -/
theorem forwardSum_unique {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) {z : ℕ → Ω → ℝ} (hz : BoundedProc z)
    (hzrec : ∀ t, z t = x t + a • 𝔼.E t (z (t + 1))) : z = forwardSum 𝔼 a x := by
  refine 𝔼.forward_unique ha (u := x) (fun t => ?_) (fun t => ?_) hz
    (forwardSum_bounded 𝔼 ha ⟨M, hx⟩)
  · rw [add_comm]; exact hzrec t
  · rw [add_comm]; exact forwardSum_rec 𝔼 ha hx hxa t

/-! ### Differentiating under `E_t` -/

/-- **Differentiation under a conditional expectation.** If the second-order
remainder of `z ↦ g z` at `x` is bounded by `C h²` uniformly in the state, then
`z ↦ E_t[g z]` has derivative `E_t[g']` at `x`. Needed to differentiate the
reset-price objective of Galí (2015), p. 56, under `E_t`. -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- A Lipschitz bound on the derivative bounds the second-order remainder:
`|f(x+h) − f(x) − h f'(x)| ≤ L h²` (mean value theorem). -/
theorem remainder_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {x r L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ y ∈ Metric.ball x r, HasDerivAt f (f' y) y)
    (hL : ∀ y ∈ Metric.ball x r, |f' y - f' x| ≤ L * |y - x|) {h : ℝ} (hh : |h| < r) :
    |f (x + h) - f x - h * f' x| ≤ L * h ^ 2 := by
  have hsub : Metric.closedBall x |h| ⊆ Metric.ball x r :=
    Metric.closedBall_subset_ball hh
  have hd : ∀ y ∈ Metric.closedBall x |h|,
      HasDerivWithinAt (fun z => f z - z * f' x) (f' y - f' x) (Metric.closedBall x |h|) y := by
    intro y hy
    have h1 := hf y (hsub hy)
    have h2 : HasDerivAt (fun z : ℝ => z * f' x) (f' x) y := by
      simpa using (hasDerivAt_id y).mul_const (f' x)
    exact (HasDerivAt.sub h1 h2).hasDerivWithinAt
  have hb : ∀ y ∈ Metric.closedBall x |h|, ‖f' y - f' x‖ ≤ L * |h| := by
    intro y hy
    rw [Real.norm_eq_abs]
    refine (hL y (hsub hy)).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    simpa [Metric.mem_closedBall, Real.dist_eq] using hy
  have hx : x ∈ Metric.closedBall x |h| := Metric.mem_closedBall_self (abs_nonneg h)
  have hxh : x + h ∈ Metric.closedBall x |h| := by
    simp [Metric.mem_closedBall]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_closedBall x |h|) hx hxh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at this
  calc |f (x + h) - f x - h * f' x| = |f (x + h) - (x + h) * f' x - (f x - x * f' x)| := by
        ring_nf
    _ ≤ L * |h| * |h| := this
    _ = L * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Differentiation under `E_t`, Lipschitz form.** If `z ↦ g z ω` has derivative
`g' z ω` near `x` and the derivative is Lipschitz at `x` uniformly in the state,
then `z ↦ E_t[g z]` has derivative `E_t[g' x]` at `x` (Galí (2015), p. 56). -/
theorem hasDerivAt_E {g g' : ℝ → Ω → ℝ} {x r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hg : ∀ y ∈ Metric.ball x r, ∀ ω, HasDerivAt (fun z => g z ω) (g' y ω) y)
    (hL : ∀ y ∈ Metric.ball x r, ∀ ω, |g' y ω - g' x ω| ≤ L * |y - x|) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t (g' x) ω) x :=
  hasDerivAt_E_of_remainder 𝔼 hr (fun _ hh ω' => remainder_le_of_lipschitz_deriv hL0
    (fun y hy => hg y hy ω') (fun y hy => hL y hy ω') hh) t ω

/-- **Term-by-term differentiation of a discounted sum of conditional
expectations** (Galí (2015), eq. (10), p. 56): `z ↦ ∑ₖ θᵏ E_t[gₖ z]` has
derivative `∑ₖ θᵏ E_t[g'ₖ x]` on an open interval `U`, provided each `g'ₖ` is
locally Lipschitz uniformly in the state and dominated by `uₖ` with
`∑ |θ|ᵏ uₖ < ∞`, and the series converges at one point of `U`. -/
theorem hasDerivAt_tsum_E {θ : ℝ} {g g' : ℕ → ℝ → Ω → ℝ} {U : Set ℝ} {u : ℕ → ℝ}
    (hU : IsOpen U) (hU' : IsPreconnected U)
    (hg : ∀ k, ∀ y ∈ U, ∀ ω, HasDerivAt (fun z => g k z ω) (g' k y ω) y)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0,
      ∀ z ∈ Metric.ball y r, ∀ ω, |g' k z ω - g' k y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |g' k y ω| ≤ u k) (hu : Summable fun k => |θ| ^ k * u k)
    {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => θ ^ k * 𝔼.E t (g k y₀) ω) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => ∑' k, θ ^ k * 𝔼.E t (g k z) ω)
      (∑' k, θ ^ k * 𝔼.E t (g' k x) ω) x := by
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => |θ| ^ k * u k)
    (g := fun k z => θ ^ k * 𝔼.E t (g k z) ω) (g' := fun k z => θ ^ k * 𝔼.E t (g' k z) ω)
    hu hU hU' (fun k y hy => ?_) (fun k y hy => ?_) hy₀ hs hx
  · obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU y hy
    obtain ⟨L, hL0, r, hr, hL⟩ := hLip k y hy
    have hsub : Metric.ball y (min r r₁) ⊆ Metric.ball y r₁ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hsub' : Metric.ball y (min r r₁) ⊆ Metric.ball y r :=
      Metric.ball_subset_ball (min_le_left _ _)
    exact (hasDerivAt_E 𝔼 (lt_min hr hr₁) hL0 (fun z hz ω' => hg k z (hball (hsub hz)) ω')
      (fun z hz ω' => hL z (hsub' hz) ω') t ω).const_mul (θ ^ k)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k y hy) t ω)
      (pow_nonneg (abs_nonneg θ) k)

/-! ### The reset-price objective and the first-order condition (10) -/

/-- The desired (frictionless) gross markup `M = ε/(ε − 1)` (Galí (2015), p. 57). -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- The desired markup exceeds one: `M > 1` for `ε > 1` (Galí (2015), p. 57). -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  unfold markup
  rw [one_lt_div (by linarith)]
  linarith

/-- The desired markup is positive (Galí (2015), p. 57). -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  lt_trans one_pos (one_lt_markup hε)

/-- The demand constraint (9), Galí (2015), p. 56:
`Y_{t+k|t} = (P*_t / P_{t+k})^{−ε} C_{t+k}`, as a random variable. -/
noncomputable def demand (ε Pstar : ℝ) (P C : Ω → ℝ) : Ω → ℝ :=
  fun ω => (Pstar / P ω) ^ (-ε) * C ω

/-- Demand factorises as `P*^{−ε} · P^ε C` (Galí (2015), eq. (9), p. 56). -/
theorem demand_eq {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    demand ε x P C ω = x ^ (-ε) * (P ω ^ ε * C ω) := by
  unfold demand
  rw [Real.div_rpow hx.le (hP ω).le, Real.rpow_neg (hP ω).le ε, div_inv_eq_mul]
  ring

/-- Demand is positive (Galí (2015), eq. (9), p. 56). -/
theorem demand_pos {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) : 0 < demand ε x P C ω :=
  mul_pos (Real.rpow_pos_of_pos (div_pos hx (hP ω)) _) (hC ω)

/-- The price elasticity of demand (9) is `−ε`: `dY/dP* = −ε Y / P*`
(Galí (2015), p. 56). -/
theorem hasDerivAt_demand {ε x : ℝ} (hx : 0 < x) {P C : Ω → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    HasDerivAt (fun z => demand ε z P C ω) (-ε * demand ε x P C ω / x) x := by
  have hxP : x / P ω ≠ 0 := (div_pos hx (hP ω)).ne'
  have h1 : HasDerivAt (fun z => z / P ω) (1 / P ω) x := (hasDerivAt_id x).div_const (P ω)
  have h2 := (h1.rpow_const (p := -ε) (Or.inl hxP)).mul_const (C ω)
  refine h2.congr_deriv ?_
  unfold demand
  rw [Real.rpow_sub_one hxP]
  have := (hP ω).ne'
  field_simp

/-- Realised discounted nominal profits at horizon `k` of a firm that reset its
price to `P*` (Galí (2015), p. 56, and Appendix 3.3, p. 84):
`Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))`, where
`Q_{t,t+k} = Λ_{t,t+k}/P_{t+k}` converts nominal date-`t+k` profits into date-`t`
consumption and `Ψ_{t+k}` is the nominal cost function. -/
noncomputable def profit (ε : ℝ) (Q P C : Ω → ℝ) (Ψ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (Pstar * demand ε Pstar P C ω - Ψ ω (demand ε Pstar P C ω))

/-- **The reset-price objective** (Galí (2015), p. 56):
`∑ₖ θᵏ E_t[Q_{t,t+k} (P* Y_{t+k|t} − Ψ_{t+k}(Y_{t+k|t}))]`, a genuine infinite
discounted sum, evaluated at the state `ω`. -/
noncomputable def objective (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) Pstar) ω

/-- The summand of (10), Galí (2015), p. 56:
`Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})`, with `Ψ'_{t+k|t} = Ψ'_{t+k}(Y_{t+k|t})`
the nominal marginal cost. -/
noncomputable def focTerm (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * demand ε Pstar P C ω * (Pstar - markup ε * dΨ ω (demand ε Pstar P C ω))

/-- The left-hand side of the optimality condition (10), Galí (2015), p. 56:
`∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})]`. -/
noncomputable def focSum (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (focTerm ε (Q k) (P k) (C k) (dΨ k) Pstar) ω

/-- The derivative of horizon-`k` profits in `P*`:
`((1 − ε)/P*) Q Y (P* − M Ψ')` (Galí (2015), p. 56). -/
noncomputable def profitDeriv (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - ε) / Pstar * focTerm ε Q P C dΨ Pstar ω

/-- **Marginal profit at one horizon** (Galí (2015), p. 56):
`d/dP* [Q (P* Y − Ψ(Y))] = ((1 − ε)/P*) Q Y (P* − M Ψ'(Y))`. -/
theorem hasDerivAt_profit {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : Ω → ℝ}
    {Ψ dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ ω) (dΨ ω y) y) (ω : Ω) :
    HasDerivAt (fun z => profit ε Q P C Ψ z ω) (profitDeriv ε Q P C dΨ x ω) x := by
  have hY := hasDerivAt_demand (ε := ε) (C := C) hx hP ω
  have hΨY := (hΨ ω _ (demand_pos hx hP hC ω)).comp x hY
  have h := (((hasDerivAt_id x).mul hY).sub hΨY).const_mul (Q ω)
  refine h.congr_deriv ?_
  unfold profitDeriv focTerm markup
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : x ≠ 0 := hx.ne'
  simp only [id]
  field_simp
  ring

/-- `E_t` of marginal profit: the constant `(1 − ε)/P*` comes out of `E_t`
(Galí (2015), p. 56). -/
theorem E_profitDeriv (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (x : ℝ) (t : ℕ) (ω : Ω) :
    𝔼.E t (profitDeriv ε Q P C dΨ x) ω = (1 - ε) / x * 𝔼.E t (focTerm ε Q P C dΨ x) ω := by
  have : profitDeriv ε Q P C dΨ x = ((1 - ε) / x) • focTerm ε Q P C dΨ x := rfl
  rw [this, 𝔼.E_smul]
  rfl

/-- **The derivative of the reset-price objective** (Galí (2015), eq. (10), p. 56):
under explicit domination and local-Lipschitz hypotheses on marginal profits and
convergence of the objective at one price, the objective has derivative
`((1 − ε)/P*) ∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]` at every `P*` in
an open interval `U ⊆ (0, ∞)`. -/
theorem hasDerivAt_objective {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    {U : Set ℝ} (hU : IsOpen U) (hU' : IsPreconnected U) (hUpos : U ⊆ Set.Ioi 0)
    {u : ℕ → ℝ}
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (hu : Summable fun k => |θ| ^ k * u k) {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y₀) ω)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  have h := hasDerivAt_tsum_E 𝔼 (θ := θ)
    (g := fun k z => profit ε (Q k) (P k) (C k) (Ψ k) z)
    (g' := fun k z => profitDeriv ε (Q k) (P k) (C k) (dΨ k) z) hU hU'
    (fun k y hy ω' => hasDerivAt_profit hε (hUpos hy) (hP k) (hC k) (hΨ k) ω')
    hLip hdom hu hy₀ t ω hs hx
  refine h.congr_deriv ?_
  simp only [E_profitDeriv, focSum]
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- **The optimality condition (10) is necessary** (Galí (2015), eq. (10), p. 56):
if `P*` is a local maximum of the reset-price objective, then
`∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t} (P* − M Ψ'_{t+k|t})] = 0`. -/
theorem foc_of_isLocalMax {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} {t : ℕ} {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hder : HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x)
    (hmax : IsLocalMax (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) x) :
    focSum 𝔼 θ ε Q P C dΨ t x ω = 0 := by
  have h := hmax.hasDerivAt_eq_zero hder
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- The objective is differentiable at every positive price when marginal profits
are dominated on every bounded interval `(a, b)` with `a > 0` (Galí (2015), p. 56). -/
theorem hasDerivAt_objective_of_pos {θ ε : ℝ} (hε : 1 < ε) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hP : ∀ k ω, 0 < P k ω) (hC : ∀ k ω, 0 < C k ω)
    (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  obtain ⟨u, hu, hdom⟩ := hloc (x / 2) (x + 1) (by positivity)
  have hxU : x ∈ Set.Ioo (x / 2) (x + 1) := ⟨by linarith, by linarith⟩
  have hUpos : Set.Ioo (x / 2) (x + 1) ⊆ Set.Ioi 0 := fun y hy => by
    simp only [Set.mem_Ioi]; linarith [hy.1]
  exact hasDerivAt_objective 𝔼 hε hP hC hΨ isOpen_Ioo isPreconnected_Ioo hUpos
    (fun k y hy => hLip k y (hUpos hy)) hdom hu hxU t ω (hs x hx) hxU

/-! ### The first-order condition characterises the optimum (convex costs) -/

/-- The `P*`-dependent core of the summand of (10) once the factor `P*^{−ε}` of
demand is taken out: `Q P^ε C (P* − M Ψ'(Y))` (Galí (2015), p. 56). -/
noncomputable def focCore (ε : ℝ) (Q P C : Ω → ℝ) (dΨ : Ω → ℝ → ℝ) (Pstar : ℝ) : Ω → ℝ :=
  fun ω => Q ω * (P ω ^ ε * C ω) * (Pstar - markup ε * dΨ ω (demand ε Pstar P C ω))

/-- The summand of (10) is `P*^{−ε}` times its core (Galí (2015), p. 56). -/
theorem focTerm_eq {ε x : ℝ} (hx : 0 < x) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) : focTerm ε Q P C dΨ x = x ^ (-ε) • focCore ε Q P C dΨ x := by
  funext ω
  simp only [focTerm, focCore, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hP ω]
  ring

/-- With convex costs (nondecreasing marginal cost), the core of (10) increases in
`P*` at least at rate `Q P^ε C`: a higher price lowers demand and hence marginal
cost (Galí (2015), p. 56). -/
theorem focCore_sub_ge {ε : ℝ} (hε : 1 < ε) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (ω : Ω) :
    (y - x) * (Q ω * (P ω ^ ε * C ω)) ≤ focCore ε Q P C dΨ y ω - focCore ε Q P C dΨ x ω := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hK : 0 < P ω ^ ε * C ω := mul_pos (Real.rpow_pos_of_pos (hP ω) ε) (hC ω)
  have hdem : demand ε y P C ω ≤ demand ε x P C ω := by
    rw [demand_eq hx hP ω, demand_eq hy hP ω]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
      hK.le
  have hd : dΨ ω (demand ε y P C ω) ≤ dΨ ω (demand ε x P C ω) :=
    hconv ω (demand_pos hy hP hC ω) (demand_pos hx hP hC ω) hdem
  have key : focCore ε Q P C dΨ y ω - focCore ε Q P C dΨ x ω
        - (y - x) * (Q ω * (P ω ^ ε * C ω))
      = Q ω * (P ω ^ ε * C ω) *
        (markup ε * (dΨ ω (demand ε x P C ω) - dΨ ω (demand ε y P C ω))) := by
    unfold focCore; ring
  have h0 : 0 ≤ Q ω * (P ω ^ ε * C ω) *
      (markup ε * (dΨ ω (demand ε x P C ω) - dΨ ω (demand ε y P C ω))) :=
    mul_nonneg (mul_pos (hQ ω) hK).le
      (mul_nonneg (markup_pos hε).le (sub_nonneg.mpr hd))
  linarith

/-- `E_t` version of `focCore_sub_ge` (Galí (2015), p. 56). -/
theorem E_focCore_le {ε : ℝ} (hε : 1 < ε) {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ}
    (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hconv : ∀ ω, MonotoneOn (dΨ ω) (Set.Ioi 0)) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (t : ℕ) (ω : Ω) :
    (y - x) * 𝔼.E t (fun ω' => Q ω' * (P ω' ^ ε * C ω')) ω + 𝔼.E t (focCore ε Q P C dΨ x) ω
      ≤ 𝔼.E t (focCore ε Q P C dΨ y) ω := by
  have hle : (y - x) • (fun ω' => Q ω' * (P ω' ^ ε * C ω')) + focCore ε Q P C dΨ x
      ≤ focCore ε Q P C dΨ y := fun ω' => by
    have := focCore_sub_ge hε hQ hP hC hconv hx hxy ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have := 𝔼.mono t hle ω
  simpa [map_add, map_smul] using this

/-- The expected-revenue weight `E_t[Q P^ε C]` is nonnegative (Galí (2015), p. 56). -/
theorem E_weight_nonneg {ε : ℝ} {Q P C : Ω → ℝ} (hQ : ∀ ω, 0 < Q ω) (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (t : ℕ) (ω : Ω) :
    0 ≤ 𝔼.E t (fun ω' => Q ω' * (P ω' ^ ε * C ω')) ω := by
  have h0 : (0 : Ω → ℝ) ≤ fun ω' => Q ω' * (P ω' ^ ε * C ω') := fun ω' =>
    (mul_pos (hQ ω') (mul_pos (Real.rpow_pos_of_pos (hP ω') ε) (hC ω'))).le
  simpa using 𝔼.mono t h0 ω

/-- `E_t` of the summand of (10) in terms of marginal profit
(Galí (2015), p. 56). -/
theorem E_focCore_eq {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : Ω → ℝ}
    (dΨ : Ω → ℝ → ℝ) (hP : ∀ ω, 0 < P ω) (t : ℕ) (ω : Ω) :
    𝔼.E t (focCore ε Q P C dΨ x) ω
      = ((1 - ε) / x * x ^ (-ε))⁻¹ * 𝔼.E t (profitDeriv ε Q P C dΨ x) ω := by
  rw [E_profitDeriv, focTerm_eq hx dΨ hP, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h2 : x ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have h3 : 1 - ε ≠ 0 := by linarith
  field_simp

/-- **The optimality condition (10) characterises the optimal reset price**
(Galí (2015), eq. (10), p. 56). With convex costs (nondecreasing marginal cost),
positive discount factors, prices and demand, and a positive current-period
revenue weight, a positive price `P*` maximises the reset-price objective over
all positive prices if and only if it satisfies (10); such a maximiser is then
the strict, hence unique, maximiser. -/
theorem isMaxOn_iff_foc {θ ε : ℝ} (hε : 1 < ε) (hθ : 0 ≤ θ) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ k ω, 0 < Q k ω) (hP : ∀ k ω, 0 < P k ω)
    (hC : ∀ k ω, 0 < C k ω) (hΨ : ∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y)
    (hconv : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0))
    (hLip : ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y|)
    (hloc : ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k)
    (t : ℕ) (ω : Ω)
    (hs : ∀ y, 0 < y → Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω)
    (hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω)
    {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 θ ε Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 θ ε Q P C Ψ t y ω < objective 𝔼 θ ε Q P C Ψ t x ω) := by
  set V := fun z => objective 𝔼 θ ε Q P C Ψ t z ω with hV
  set H : ℝ → ℝ := fun z => ∑' k, θ ^ k * 𝔼.E t (focCore ε (Q k) (P k) (C k) (dΨ k) z) ω
    with hH
  have hder : ∀ z, 0 < z → HasDerivAt V ((1 - ε) / z * focSum 𝔼 θ ε Q P C dΨ t z ω) z :=
    fun z hz => hasDerivAt_objective_of_pos 𝔼 hε hP hC hΨ hLip hloc t ω hs hz
  -- summability of the core series
  have hsum : ∀ z, 0 < z →
      Summable fun k => θ ^ k * 𝔼.E t (focCore ε (Q k) (P k) (C k) (dΨ k) z) ω := by
    intro z hz
    obtain ⟨u, hu, hdom⟩ := hloc (z / 2) (z + 1) (by positivity)
    have hzU : z ∈ Set.Ioo (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
    have hs' : Summable fun k =>
        θ ^ k * 𝔼.E t (profitDeriv ε (Q k) (P k) (C k) (dΨ k) z) ω := by
      refine Summable.of_norm_bounded hu fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k z hzU) t ω)
        (pow_nonneg (abs_nonneg θ) k)
    refine (hs'.mul_left ((1 - ε) / z * z ^ (-ε))⁻¹).congr fun k => ?_
    rw [E_focCore_eq 𝔼 hε hz _ (hP k)]
    ring
  -- (10) in terms of the core series
  have hfocH : ∀ z, 0 < z → focSum 𝔼 θ ε Q P C dΨ t z ω = z ^ (-ε) * H z := by
    intro z hz
    simp only [focSum, hH, focTerm_eq hz _ (hP _), 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  -- the core series is strictly increasing
  have hHmono : ∀ z y, 0 < z → z < y → H z < H y := by
    intro z y hz hzy
    refine Summable.tsum_lt_tsum (i := 0) (fun k => ?_) ?_ (hsum z hz)
      (hsum y (hz.trans hzy))
    · have h1 := E_focCore_le 𝔼 hε (hQ k) (hP k) (hC k) (hconv k) hz hzy.le t ω
      have h2 := E_weight_nonneg 𝔼 (ε := ε) (hQ k) (hP k) (hC k) t ω
      have h3 : 0 ≤ (y - z) * 𝔼.E t (fun ω' => Q k ω' * (P k ω' ^ ε * C k ω')) ω :=
        mul_nonneg (by linarith) h2
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hθ k)
    · have h1 := E_focCore_le 𝔼 hε (hQ 0) (hP 0) (hC 0) (hconv 0) hz hzy.le t ω
      have h3 : 0 < (y - z) * 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω :=
        mul_pos (by linarith) hpos
      simp only [pow_zero, one_mul]
      linarith
  have hcoef : ∀ z, 0 < z → (1 - ε) / z < 0 := fun z hz => div_neg_of_neg_of_pos (by linarith) hz
  -- the strict-maximum part
  have hstrict : focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x → V y < V x := by
    intro hfoc
    have hHx : H x = 0 := by
      have := hfocH x hx
      rw [hfoc] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (Real.rpow_pos_of_pos hx _).ne'
    have hcont : ∀ z, 0 < z → ContinuousAt V z := fun z hz => (hder z hz).continuousAt
    have hinc : StrictMonoOn V (Set.Ioc 0 x) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 x)
        (fun z hz => (hcont z hz.1).continuousWithinAt) fun z hz => ?_
      rw [interior_Ioc] at hz
      rw [(hder z hz.1).deriv, hfocH z hz.1]
      have hHz : H z < 0 := hHx ▸ hHmono z x hz.1 hz.2
      have := mul_neg_of_neg_of_pos hHz (Real.rpow_pos_of_pos hz.1 (-ε))
      nlinarith [hcoef z hz.1]
    have hdec : StrictAntiOn V (Set.Ici x) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici x)
        (fun z hz => (hcont z (lt_of_lt_of_le hx hz)).continuousWithinAt) fun z hz => ?_
      rw [interior_Ici] at hz
      have hz0 : 0 < z := hx.trans hz
      rw [(hder z hz0).deriv, hfocH z hz0]
      have hHz : 0 < H z := hHx ▸ hHmono x z hx hz
      have := mul_pos (Real.rpow_pos_of_pos hz0 (-ε)) hHz
      nlinarith [hcoef z hz0]
    intro y hy hyx
    rcases lt_or_gt_of_ne hyx with h | h
    · exact hinc ⟨hy, h.le⟩ ⟨hx, le_rfl⟩ h
    · exact hdec (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h
  refine ⟨⟨fun hmax => ?_, fun hfoc => ?_⟩, hstrict⟩
  · exact foc_of_isLocalMax 𝔼 hε hx (hder x hx) (hmax.isLocalMax (Ioi_mem_nhds hx))
  · intro y hy
    rcases eq_or_ne y x with h | h
    · rw [h]; exact le_refl (V x)
    · exact (hstrict hfoc y hy h).le

/-! ### Flexible prices and the zero-inflation steady state -/

/-- With flexible prices (`θ = 0`) the objective reduces to current expected
profits (Galí (2015), p. 57). -/
theorem objective_flexible (ε : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    objective 𝔼 0 ε Q P C Ψ t z ω = 𝔼.E t (profit ε (Q 0) (P 0) (C 0) (Ψ 0) z) ω := by
  unfold objective
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- With flexible prices (`θ = 0`) condition (10) involves only the current period
(Galí (2015), p. 57). -/
theorem focSum_flexible (ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (z : ℝ) (ω : Ω) :
    focSum 𝔼 0 ε Q P C dΨ t z ω = 𝔼.E t (focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) z) ω := by
  unfold focSum
  rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- **Flexible-price pricing rule** (Galí (2015), p. 57): with `θ = 0` and the
current-period variables known at `t`, condition (10) holds if and only if
`P*_t = M Ψ'_{t|t}`, the frictionless markup over marginal cost. -/
theorem flexible_foc_iff {ε x : ℝ} (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    {t : ℕ} (hknown : 𝔼.E t (focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) x)
      = focTerm ε (Q 0) (P 0) (C 0) (dΨ 0) x) (ω : Ω) :
    focSum 𝔼 0 ε Q P C dΨ t x ω = 0 ↔ x = markup ε * dΨ 0 ω (demand ε x (P 0) (C 0) ω) := by
  rw [focSum_flexible, hknown]
  unfold focTerm
  have h := mul_pos (hQ ω) (demand_pos (ε := ε) hx hP hC ω)
  constructor
  · intro h0
    have := (mul_eq_zero.mp h0).resolve_left h.ne'
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero]

/-- **Flexible-price optimum** (Galí (2015), p. 57): with `θ = 0`, if the
current-period profit function is known at `t` and `P*` is a local maximum of
the objective, then `P* = M Ψ'_{t|t}`. -/
theorem flexible_price_optimum {ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ : ℕ → Ω → ℝ → ℝ} (hQ : ∀ ω, 0 < Q 0 ω) (hP : ∀ ω, 0 < P 0 ω) (hC : ∀ ω, 0 < C 0 ω)
    (hΨ : ∀ ω y, 0 < y → HasDerivAt (Ψ 0 ω) (dΨ 0 ω y) y) {t : ℕ}
    (hknown : ∀ z, 𝔼.E t (profit ε (Q 0) (P 0) (C 0) (Ψ 0) z)
      = profit ε (Q 0) (P 0) (C 0) (Ψ 0) z) {ω : Ω}
    (hmax : IsLocalMax (fun z => objective 𝔼 0 ε Q P C Ψ t z ω) x) :
    x = markup ε * dΨ 0 ω (demand ε x (P 0) (C 0) ω) := by
  have hfun : (fun z => objective 𝔼 0 ε Q P C Ψ t z ω)
      = fun z => profit ε (Q 0) (P 0) (C 0) (Ψ 0) z ω := by
    funext z; rw [objective_flexible, hknown]
  rw [hfun] at hmax
  have h0 := hmax.hasDerivAt_eq_zero (hasDerivAt_profit hε hx hP hC hΨ ω)
  unfold profitDeriv focTerm at h0
  have hc : (1 - ε) / x ≠ 0 := div_ne_zero (by linarith) hx.ne'
  have h := mul_pos (hQ ω) (demand_pos (ε := ε) hx hP hC ω)
  have h1 := (mul_eq_zero.mp h0).resolve_left hc
  have := (mul_eq_zero.mp h1).resolve_left h.ne'
  linarith

/-- **The zero-inflation steady state** (Galí (2015), p. 57): with constant price
level `P`, consumption `C`, discount factors `Λ_{t,t+k} = βᵏ` and marginal cost `Ψ`
at the steady-state output, condition (10) at `P* = P` holds if and only if
`P = M Ψ`: actual markups equal the frictionless markup. -/
theorem steadyState_foc_iff {β θ ε Pbar Cbar Ψbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hP : 0 < Pbar) (hC : 0 < Cbar) {dΨ : ℕ → Ω → ℝ → ℝ}
    (hdΨ : ∀ k ω, dΨ k ω Cbar = Ψbar) (t : ℕ) (ω : Ω) :
    focSum 𝔼 θ ε (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t Pbar ω = 0
      ↔ Pbar = markup ε * Ψbar := by
  have hY : ∀ ω' : Ω, demand ε Pbar (fun _ => Pbar) (fun _ => Cbar) ω' = Cbar := by
    intro ω'; simp [demand, div_self hP.ne']
  have hterm : ∀ k, focTerm ε (fun _ => β ^ k / Pbar) (fun _ => Pbar) (fun _ => Cbar) (dΨ k) Pbar
      = fun _ => β ^ k / Pbar * Cbar * (Pbar - markup ε * Ψbar) := by
    intro k; funext ω'
    simp only [focTerm, hY, hdΨ]
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  have hsum : focSum 𝔼 θ ε (fun k _ => β ^ k / Pbar) (fun _ _ => Pbar) (fun _ _ => Cbar) dΨ t
      Pbar ω = (1 - β * θ)⁻¹ * (Cbar / Pbar * (Pbar - markup ε * Ψbar)) := by
    simp only [focSum, hterm, 𝔼.const]
    rw [← tsum_geometric_of_lt_one hβθ0 hβθ1, ← tsum_mul_right]
    congr 1; funext k
    rw [mul_pow]; field_simp
  rw [hsum]
  have h1 : (1 - β * θ)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have h2 : Cbar / Pbar ≠ 0 := (div_pos hC hP).ne'
  constructor
  · intro h0
    have := (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h1)).resolve_left h2
    linarith
  · intro h0
    rw [← h0, sub_self, mul_zero, mul_zero]

/-! ### The log-linear pricing rule (11) as the exact linearisation of (10) -/

/-- The log desired markup `μ = log M` (Galí (2015), p. 57). -/
noncomputable def logMarkup (ε : ℝ) : ℝ := Real.log (markup ε)

/-- The left-hand side of (10) written in terms of the weights
`wₖ = Λ_{t,t+k} Y_{t+k|t} / P_{t+k}` and the nominal marginal costs
`Ψ_{t+k|t}` (Galí (2015), eq. (10), p. 56):
`∑ₖ θᵏ E_t[wₖ (P* − M Ψ_{t+k|t})]`. -/
noncomputable def focLHS (θ ε : ℝ) (w : ℕ → Ω → ℝ) (Pstar : ℝ) (Ψm : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ω => ∑' k, θ ^ k * 𝔼.E t (fun ω' => w k ω' * (Pstar - markup ε * Ψm k ω')) ω

/-- The reset-price condition `focSum` is (10) with weights `Q_{t,t+k} Y_{t+k|t}`
and marginal costs `Ψ'_{t+k}(Y_{t+k|t})` (Galí (2015), p. 56). -/
theorem focSum_eq_focLHS (θ ε : ℝ) (Q P C : ℕ → Ω → ℝ) (dΨ : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (x : ℝ) :
    focSum 𝔼 θ ε Q P C dΨ t x = focLHS 𝔼 θ ε (fun k ω => Q k ω * demand ε x (P k) (C k) ω) x
      (fun k ω => dΨ k ω (demand ε x (P k) (C k) ω)) t := rfl

/-- Differentiating `E_t[exp(s g)]` in `s` for a bounded random variable `g`:
the derivative is `E_t[g exp(s g)]`. -/
theorem hasDerivAt_E_exp {g : Ω → ℝ} {B : ℝ} (hg : ∀ ω, |g ω| ≤ B) (t : ℕ) (ω : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ω' => Real.exp (r * g ω')) ω)
      (𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω) s := by
  refine hasDerivAt_E_of_remainder 𝔼 (g := fun r ω' => Real.exp (r * g ω'))
    (δ := 1 / (|B| + 1)) (C := Real.exp (|s| * |B|) * B ^ 2) (by positivity)
    (fun h hh ω' => ?_) t ω
  have hgB : |g ω'| ≤ |B| := (hg ω').trans (le_abs_self B)
  have hhB : |h| * |B| ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hh
    nlinarith [abs_nonneg B, abs_nonneg h]
  have hhg : |h * g ω'| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hgB (abs_nonneg h)).trans hhB
  have hexp := Real.abs_exp_sub_one_sub_id_le hhg
  have key : Real.exp ((s + h) * g ω') - Real.exp (s * g ω') - h * (g ω' * Real.exp (s * g ω'))
      = Real.exp (s * g ω') * (Real.exp (h * g ω') - 1 - h * g ω') := by
    rw [add_mul, Real.exp_add]; ring
  rw [key, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : Real.exp (s * g ω') ≤ Real.exp (|s| * |B|) := by
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hgB (abs_nonneg s)
  have e2 : (h * g ω') ^ 2 ≤ B ^ 2 * h ^ 2 := by
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.mpr hgB) (sq_nonneg h)
  calc Real.exp (s * g ω') * |Real.exp (h * g ω') - 1 - h * g ω'|
      ≤ Real.exp (|s| * |B|) * (B ^ 2 * h ^ 2) :=
        mul_le_mul e1 (hexp.trans e2) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|s| * |B|) * B ^ 2 * h ^ 2 := by ring

/-- **Exact linearisation of (10) at the zero-inflation steady state**
(Galí (2015), p. 57). Perturb the steady state along an arbitrary bounded
direction: log weights `log wₖ = log(βᵏ w̄) + s ŵₖ` (stochastic discount factor,
demand and price level combined), log reset price `p* = p̄ + s x̂`, and log
marginal costs `ψ_{t+k|t} = ψ̄ + s ψ̂ₖ`, where the steady state satisfies
`p̄ = μ + ψ̄` (`P = M Ψ`). Then the left-hand side of (10) has derivative
`w̄ e^{p̄} ∑ₖ (βθ)ᵏ (x̂ − E_t ψ̂ₖ)` at `s = 0`. The weight deviations `ŵ` drop out:
to first order only prices and marginal costs matter. -/
theorem hasDerivAt_focLHS_path {θ β ε wbar pbar xhat B : ℝ} (hε : 1 < ε) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {what ψhat : ℕ → Ω → ℝ}
    (hw : ∀ k ω, |what k ω| ≤ B) (hψ : ∀ k ω, |ψhat k ω| ≤ B) (hxB : |xhat| ≤ B)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focLHS 𝔼 θ ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      (wbar * Real.exp pbar * ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω)) 0 := by
  set c := wbar * Real.exp pbar with hc
  set a : ℕ → Ω → ℝ := fun k ω' => what k ω' + xhat with ha
  set b : ℕ → Ω → ℝ := fun k ω' => what k ω' + ψhat k ω' with hb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hxB
  have haB : ∀ k ω', |a k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω'])
  have hbB : ∀ k ω', |b k ω'| ≤ 2 * B := fun k ω' =>
    (abs_add_le _ _).trans (by linarith [hw k ω', hψ k ω'])
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  -- rewrite the path of (10) through exponentials of `s a` and `s b`
  have hfun : (fun s => focLHS 𝔼 θ ε (fun k ω' => β ^ k * wbar * Real.exp (s * what k ω'))
        (Real.exp (pbar + s * xhat))
        (fun k ω' => Real.exp (pbar - logMarkup ε + s * ψhat k ω')) t ω)
      = fun s => ∑' k, (β * θ) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)) := by
    funext s
    unfold focLHS
    congr 1; funext k
    have hint : (fun ω' => β ^ k * wbar * Real.exp (s * what k ω') *
          (Real.exp (pbar + s * xhat)
            - markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')))
        = (β ^ k * c) • ((fun ω' => Real.exp (s * a k ω'))
            - fun ω' => Real.exp (s * b k ω')) := by
      funext ω'
      have hM : markup ε * Real.exp (pbar - logMarkup ε + s * ψhat k ω')
          = Real.exp (pbar + s * ψhat k ω') := by
        rw [logMarkup, show pbar - Real.log (markup ε) + s * ψhat k ω'
            = (pbar + s * ψhat k ω') + -Real.log (markup ε) by ring, Real.exp_add,
          Real.exp_neg, Real.exp_log (markup_pos hε)]
        have := (markup_pos hε).ne'
        field_simp
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hM]
      simp only [ha, hb, hc, mul_add, Real.exp_add]
      ring
    rw [hint, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_pow]
    ring
  rw [hfun]
  -- term-by-term differentiation on `(-1, 1)`
  have hbd : ∀ (g : Ω → ℝ), (∀ ω', |g ω'| ≤ 2 * B) → ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
      |𝔼.E t (fun ω' => g ω' * Real.exp (s * g ω')) ω| ≤ 2 * B * Real.exp (2 * B) := by
    intro g hg s hs
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hg ω') ?_ (Real.exp_pos _).le (by linarith)
    rw [Real.exp_le_exp]
    calc s * g ω' ≤ |s * g ω'| := le_abs_self _
      _ = |s| * |g ω'| := abs_mul _ _
      _ ≤ 1 * (2 * B) := mul_le_mul hs1 (hg ω') (abs_nonneg _) zero_le_one
      _ = 2 * B := one_mul _
  have hD := hasDerivAt_tsum_of_isPreconnected
    (u := fun k => (β * θ) ^ k * (|c| * (2 * (2 * B * Real.exp (2 * B)))))
    (g := fun k s => (β * θ) ^ k * (c * (𝔼.E t (fun ω' => Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => Real.exp (s * b k ω')) ω)))
    (g' := fun k s => (β * θ) ^ k * (c * (𝔼.E t (fun ω' => a k ω' * Real.exp (s * a k ω')) ω
          - 𝔼.E t (fun ω' => b k ω' * Real.exp (s * b k ω')) ω)))
    (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    ((summable_geometric_of_lt_one hβθ0 hβθ1).mul_right _) isOpen_Ioo isPreconnected_Ioo
    (fun k s _ => (((hasDerivAt_E_exp 𝔼 (haB k) t ω s).sub
      (hasDerivAt_E_exp 𝔼 (hbB k) t ω s)).const_mul c).const_mul _)
    (fun k s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβθ0 k), abs_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg c))
        (pow_nonneg hβθ0 k)
      refine (abs_sub _ _).trans ?_
      linarith [hbd _ (haB k) s hs, hbd _ (hbB k) s hs])
    ⟨by norm_num, by norm_num⟩
    (by simp)
    ⟨by norm_num, by norm_num⟩
  refine hD.congr_deriv ?_
  rw [← tsum_mul_left]
  congr 1; funext k
  have hab : (fun ω' => a k ω' * Real.exp (0 * a k ω'))
      - (fun ω' => b k ω' * Real.exp (0 * b k ω')) = (fun _ => xhat) - ψhat k := by
    funext ω'; simp [ha, hb]
  rw [← Pi.sub_apply (𝔼.E t _), ← map_sub, hab, map_sub, 𝔼.const]
  simp only [Pi.sub_apply]
  ring

/-- **The log-linear pricing rule (11)** (Galí (2015), eq. (11), p. 57). The
first-order term of (10) at the zero-inflation steady state vanishes if and only if
`p*_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k|t}`, where `p*_t = p̄ + x̂` and
`ψ_{t+k|t} = ψ̄ + ψ̂ₖ` with `ψ̄ = p̄ − μ`. -/
theorem eq11_iff {θ β ε wbar pbar xhat B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hwbar : 0 < wbar) {ψhat : ℕ → Ω → ℝ} (hψ : ∀ k ω, |ψhat k ω| ≤ B)
    (t : ℕ) (ω : Ω) :
    wbar * Real.exp pbar * ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = 0 ↔
      pbar + xhat = logMarkup ε + (1 - β * θ) *
        ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω := by
  have hβθ0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0
  have hβθ1 : β * θ < 1 := by nlinarith
  have hβθ : |β * θ| < 1 := by rwa [abs_of_nonneg hβθ0]
  have hg := summable_geometric_of_lt_one hβθ0 hβθ1
  have hT := summable_geometric_bounded hβθ (fun k ω' => 𝔼.abs_E_le (hψ k) t ω') ω
  set T := ∑' k, (β * θ) ^ k * 𝔼.E t (ψhat k) ω with hTdef
  have h1 : ∑' k, (β * θ) ^ k * (xhat - 𝔼.E t (ψhat k) ω) = xhat * (1 - β * θ)⁻¹ - T := by
    simp_rw [mul_sub]
    rw [Summable.tsum_sub (hg.mul_right xhat) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβθ0 hβθ1]
    ring
  have h2 : ∑' k, (β * θ) ^ k * 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
      = (pbar - logMarkup ε) * (1 - β * θ)⁻¹ + T := by
    have : ∀ k, 𝔼.E t (fun ω' => (pbar - logMarkup ε) + ψhat k ω') ω
        = (pbar - logMarkup ε) + 𝔼.E t (ψhat k) ω := by
      intro k
      have hf : (fun ω' => (pbar - logMarkup ε) + ψhat k ω')
          = (fun _ => pbar - logMarkup ε) + ψhat k := rfl
      rw [hf, map_add, 𝔼.const]; rfl
    simp_rw [this, mul_add]
    rw [Summable.tsum_add (hg.mul_right _) hT, tsum_mul_right,
      tsum_geometric_of_lt_one hβθ0 hβθ1, mul_comm]
  rw [h1, h2]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  have hd : 1 - β * θ ≠ 0 := by linarith
  constructor
  · intro h
    have h3 := (mul_eq_zero.mp h).resolve_left hc
    field_simp at h3 ⊢
    linarith
  · intro h
    have h3 : xhat * (1 - β * θ)⁻¹ - T = 0 := by
      field_simp at h ⊢
      linarith
    rw [h3, mul_zero]

/-- (11) in terms of real marginal cost `mc_{t+k|t} = ψ_{t+k|t} − p_{t+k}`
(Galí (2015), p. 57 and fn. 4, p. 61):
`μ + (1 − βθ)∑(βθ)ᵏ E_t ψ_{t+k|t} = μ + (1 − βθ)∑(βθ)ᵏ E_t[mc_{t+k|t} + p_{t+k}]`. -/
theorem eq11_real_marginal_cost (θ β ε : ℝ) (ψ mc p : ℕ → Ω → ℝ)
    (h : ∀ k, ψ k = mc k + p k) (t : ℕ) (ω : Ω) :
    logMarkup ε + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ k) ω
      = logMarkup ε + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (mc k + p k) ω := by
  simp_rw [h]

/-! ### Recursive form of the pricing rule -/

/-- The normalised forward sum `(1 − a) ∑ₖ aᵏ E_t x_{t+k}` satisfies
`S_t = a E_t S_{t+1} + (1 − a) x_t` (Galí (2015), eq. (16), p. 60). -/
theorem normForward_rec {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) (t : ℕ) :
    (1 - a) • forwardSum 𝔼 a x t
      = a • 𝔼.E t ((1 - a) • forwardSum 𝔼 a x (t + 1)) + (1 - a) • x t := by
  rw [forwardSum_rec 𝔼 ha hx hxa t, 𝔼.E_smul, smul_add, smul_smul, smul_smul,
    mul_comm (1 - a) a, add_comm]

/-- **Uniqueness of the recursive pricing rule** (Galí (2015), eq. (16), p. 60):
the normalised forward sum is the only bounded process with
`S_t = a E_t S_{t+1} + (1 − a) x_t`. -/
theorem normForward_unique {a : ℝ} (ha : |a| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (hxa : 𝔼.Adapted x) {S : ℕ → Ω → ℝ} (hS : BoundedProc S)
    (hrec : ∀ t, S t = a • 𝔼.E t (S (t + 1)) + (1 - a) • x t) :
    S = fun t => (1 - a) • forwardSum 𝔼 a x t := by
  refine 𝔼.forward_unique ha (u := fun t => (1 - a) • x t) hrec (fun t => ?_) hS ?_
  · exact normForward_rec 𝔼 ha hx hxa t
  · obtain ⟨B, hB⟩ := forwardSum_bounded 𝔼 ha ⟨M, hx⟩
    refine ⟨|1 - a| * B, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)

/-- A constant passes through the normalised forward sum:
`(1 − a) ∑ₖ aᵏ E_t[c + y_{t+k}] = c + (1 − a) ∑ₖ aᵏ E_t y_{t+k}`
(Galí (2015), eq. (11), p. 57: the markup `μ` in front of the sum). -/
theorem normForward_const_add {a : ℝ} (ha : |a| < 1) (c : ℝ) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ t ω, |y t ω| ≤ M) (t : ℕ) :
    (1 - a) • forwardSum 𝔼 a (fun s => (fun _ => c) + y s) t
      = (fun _ => c) + (1 - a) • forwardSum 𝔼 a y t := by
  funext ω
  have ha1 : a < 1 := (le_abs_self a).trans_lt ha
  have hd : 1 - a ≠ 0 := by linarith
  have hg : Summable fun k => a ^ k :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])
  have hT := summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hy t (t + k) ω') ω
  simp only [forwardSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, 𝔼.const]
  simp_rw [mul_add]
  rw [Summable.tsum_add (hg.mul_right c) hT, tsum_mul_right,
    tsum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs])]
  field_simp

/-- **Recursive form of the pricing rule under constant returns** (Galí (2015),
eqs. (11) and (16), pp. 57–60): when firm-specific marginal cost equals the
economy-wide `ψ_{t+k}` (`α = 0`), the reset price
`p*_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}` satisfies
`p*_t = βθ E_t p*_{t+1} + (1 − βθ)(μ + ψ_t)` and is its only bounded solution. -/
theorem resetPrice_recursive {a μ : ℝ} (ha : |a| < 1) {ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hψ : ∀ t ω, |ψ t ω| ≤ M) (hψa : 𝔼.Adapted ψ) :
    (∀ t, (fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ t
        = a • 𝔼.E t ((fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ (t + 1))
          + (1 - a) • ((fun _ => μ) + ψ t)) ∧
    ∀ S : ℕ → Ω → ℝ, BoundedProc S →
      (∀ t, S t = a • 𝔼.E t (S (t + 1)) + (1 - a) • ((fun _ => μ) + ψ t)) →
      S = fun t => (fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ t := by
  set x : ℕ → Ω → ℝ := fun s => (fun _ => μ) + ψ s with hx
  have hxb : ∀ t ω, |x t ω| ≤ |μ| + M := fun t ω =>
    (abs_add_le _ _).trans (by simp only [add_le_add_iff_left, hψ])
  have hxa : 𝔼.Adapted x := fun t => by
    simp only [hx, map_add, 𝔼.const, hψa t]
  have heq : ∀ t, (fun _ => μ) + (1 - a) • forwardSum 𝔼 a ψ t
      = (1 - a) • forwardSum 𝔼 a x t := fun t =>
    (normForward_const_add 𝔼 ha μ hψ t).symm
  refine ⟨fun t => ?_, fun S hS hrec => ?_⟩
  · rw [heq t, heq (t + 1)]
    exact normForward_rec 𝔼 ha hxb hxa t
  · rw [normForward_unique 𝔼 ha hxb hxa hS hrec]
    funext t
    exact (heq t).symm

/-! ### Appendix 3.3: the firm's objective function -/

/-- **Reset-history probabilities** (Galí (2015), Appendix 3.3, eq. (37), p. 84):
a price reset at `t` is still in force at `t + k` with probability `θᵏ`, and was
last reset at `t + h` (`1 ≤ h ≤ k`) with probability `(1 − θ) θ^{k−h}`; these
probabilities sum to one. -/
theorem reset_prob_sum (θ : ℝ) (k : ℕ) :
    θ ^ k + (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) = 1 := by
  have hr : ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) = ∑ h ∈ Finset.range k, θ ^ h := by
    rw [← Finset.sum_range_reflect (fun j => θ ^ j) k]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Nat.sub_sub, add_comm 1 h]
  rw [hr]
  linear_combination -(geom_sum_mul θ k)

/-- The value of a firm resetting its price at `t` (Galí (2015), Appendix 3.3,
eq. (37), pp. 84–85): at horizon `k` the expected real dividend is
`θᵏ E_t[Xₖ(P*)]` (price still `P*`) plus `(1 − θ) ∑_{h=1}^{k} θ^{k−h} E_t[Z_{k,h}]`
(price last reset at `t + h`), and the latter does not depend on `P*`. -/
noncomputable def firmValue (θ : ℝ) (X : ℕ → ℝ → Ω → ℝ) (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ)
    (Pstar : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, (θ ^ k * 𝔼.E t (X k Pstar) ω
    + (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω)

/-- The `P*`-independent term `Υ_t` of the firm's value (Galí (2015), p. 85). -/
noncomputable def resetValueRest (θ : ℝ) (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω

/-- **Decomposition of the firm's value** (Galí (2015), p. 85):
`V_{t|t}(P*) = ∑ₖ θᵏ E_t[Xₖ(P*)] + Υ_t`, with `Υ_t` independent of `P*`. -/
theorem firmValue_eq (θ : ℝ) (X : ℕ → ℝ → Ω → ℝ) (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ) (Pstar : ℝ)
    (ω : Ω) (hX : Summable fun k => θ ^ k * 𝔼.E t (X k Pstar) ω)
    (hZ : Summable fun k =>
      (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω) :
    firmValue 𝔼 θ X Z t Pstar ω
      = ∑' k, θ ^ k * 𝔼.E t (X k Pstar) ω + resetValueRest 𝔼 θ Z t ω :=
  hX.tsum_add hZ

/-- **The text's objective is the firm's value up to a constant** (Galí (2015),
p. 56 and Appendix 3.3, p. 85): with `Xₖ` the discounted profits of a firm still
charging `P*`, a price maximises the firm's value over a set of prices if and only
if it maximises the reset-price objective. -/
theorem isMaxOn_firmValue_iff {θ ε : ℝ} {Q P C : ℕ → Ω → ℝ} {Ψ : ℕ → Ω → ℝ → ℝ}
    (Z : ℕ → ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (S : Set ℝ) (x : ℝ) (hx : x ∈ S)
    (hX : ∀ z ∈ S, Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) z) ω)
    (hZ : Summable fun k =>
      (1 - θ) * ∑ h ∈ Finset.range k, θ ^ (k - (h + 1)) * 𝔼.E t (Z k (h + 1)) ω) :
    IsMaxOn (fun z => firmValue 𝔼 θ (fun k z => profit ε (Q k) (P k) (C k) (Ψ k) z) Z t z ω)
        S x ↔
      IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) S x := by
  simp only [isMaxOn_iff]
  refine forall₂_congr fun z hz => ?_
  rw [firmValue_eq 𝔼 θ _ Z t z ω (hX z hz) hZ, firmValue_eq 𝔼 θ _ Z t x ω (hX x hx) hZ,
    add_le_add_iff_right]
  rfl

/-! ### Regularity of the reset-price problem from model primitives -/

/-- **Primitive assumptions on the reset-price problem** (Galí (2015), p. 56): Calvo
`θ ≥ 0` and a discount bound `β ≥ 0` with `θβ < 1`; `ε > 1`; nominal discount factors
`0 < Q_{t,t+k} ≤ Q̄ βᵏ`; price levels and consumption in `[m, M̄]` with `m > 0`; a
nominal cost function `Ψ` twice differentiable at positive output, with `Ψ`, `Ψ'`,
`Ψ''` bounded, uniformly in the horizon and the state, on every compact range of
positive output. -/
def Primitives (θ β ε Qb m Mx : ℝ) (Q P C : ℕ → Ω → ℝ) (Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ) :
    Prop :=
  0 ≤ θ ∧ 0 ≤ β ∧ θ * β < 1 ∧ 1 < ε ∧ 0 < m ∧
  (∀ k ω, 0 < Q k ω ∧ Q k ω ≤ Qb * β ^ k) ∧
  (∀ k ω, m ≤ P k ω ∧ P k ω ≤ Mx) ∧ (∀ k ω, m ≤ C k ω ∧ C k ω ≤ Mx) ∧
  (∀ k ω y, 0 < y → HasDerivAt (Ψ k ω) (dΨ k ω y) y) ∧
  (∀ k ω y, 0 < y → HasDerivAt (dΨ k ω) (d2Ψ k ω y) y) ∧
  (∀ y₁ y₂, 0 < y₁ → ∃ K, ∀ k ω y, y₁ ≤ y → y ≤ y₂ →
    |Ψ k ω y| ≤ K ∧ |dΨ k ω y| ≤ K ∧ |d2Ψ k ω y| ≤ K)

/-- Bounds on the demand shifter `P^ε C ∈ [m^ε m, M̄^ε M̄]` (Galí (2015), eq. (9),
p. 56). -/
theorem weight_bounds {ε m Mx : ℝ} (hε : 0 ≤ ε) (hm : 0 < m) {P C : Ω → ℝ}
    (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx) (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    m ^ ε * m ≤ P ω ^ ε * C ω ∧ P ω ^ ε * C ω ≤ Mx ^ ε * Mx := by
  have hP0 : 0 ≤ P ω := hm.le.trans (hP ω).1
  have hC0 : 0 ≤ C ω := hm.le.trans (hC ω).1
  refine ⟨mul_le_mul (Real.rpow_le_rpow hm.le (hP ω).1 hε) (hC ω).1 hm.le
    (Real.rpow_nonneg hP0 _), mul_le_mul (Real.rpow_le_rpow hP0 (hP ω).2 hε) (hC ω).2 hC0
    (Real.rpow_nonneg (hP0.trans (hP ω).2) _)⟩

/-- **Demand stays in a compact range of positive output** when the reset price
ranges over `[lo, hi] ⊂ (0, ∞)` (Galí (2015), eq. (9), p. 56). -/
theorem demand_bounds {ε m Mx lo hi z : ℝ} (hε : 0 ≤ ε) (hm : 0 < m) (hlo : 0 < lo)
    (hz1 : lo ≤ z) (hz2 : z ≤ hi) {P C : Ω → ℝ} (hP : ∀ ω, m ≤ P ω ∧ P ω ≤ Mx)
    (hC : ∀ ω, m ≤ C ω ∧ C ω ≤ Mx) (ω : Ω) :
    hi ^ (-ε) * (m ^ ε * m) ≤ demand ε z P C ω ∧
      demand ε z P C ω ≤ lo ^ (-ε) * (Mx ^ ε * Mx) := by
  have hz : 0 < z := hlo.trans_le hz1
  have hPpos : ∀ ω, 0 < P ω := fun ω => hm.trans_le (hP ω).1
  obtain ⟨hw1, hw2⟩ := weight_bounds hε hm hP hC ω
  rw [demand_eq hz hPpos ω]
  have hm0 : 0 ≤ m ^ ε * m := by positivity
  exact ⟨mul_le_mul (Real.rpow_le_rpow_of_nonpos hz hz2 (by linarith)) hw1 hm0
      (Real.rpow_nonneg hz.le _),
    mul_le_mul (Real.rpow_le_rpow_of_nonpos hlo hz1 (by linarith)) hw2 (hm0.trans hw1)
      (Real.rpow_nonneg hlo.le _)⟩

/-- Marginal profit in factored form:
`((1 − ε)/P*) Q Y (P* − M Ψ') = (1 − ε) Q P^ε C (P*^{−ε} − M P*^{−ε−1} Ψ')`
(Galí (2015), p. 56). -/
theorem profitDeriv_eq {ε z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ} (dΨ : Ω → ℝ → ℝ)
    (hP : ∀ ω, 0 < P ω) (ω : Ω) :
    profitDeriv ε Q P C dΨ z ω = (1 - ε) * Q ω * (P ω ^ ε * C ω) *
      (z ^ (-ε) - markup ε * (z ^ (-ε - 1) * dΨ ω (demand ε z P C ω))) := by
  unfold profitDeriv focTerm
  rw [demand_eq hz hP ω, Real.rpow_sub_one hz.ne']
  field_simp

/-- The derivative of marginal profit in the reset price (Galí (2015), p. 56). -/
noncomputable def profitDeriv2 (ε : ℝ) (Q P C : Ω → ℝ) (dΨ d2Ψ : Ω → ℝ → ℝ) (z : ℝ) :
    Ω → ℝ :=
  fun ω => (1 - ε) * Q ω * (P ω ^ ε * C ω) * (-ε * z ^ (-ε - 1) - markup ε *
    ((-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)
      + z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z))))

/-- Marginal profit is differentiable in the reset price, with derivative
`profitDeriv2` (Galí (2015), p. 56). -/
theorem hasDerivAt_profitDeriv {ε z : ℝ} (hz : 0 < z) {Q P C : Ω → ℝ}
    {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (hC : ∀ ω, 0 < C ω)
    (hdΨ : ∀ ω y, 0 < y → HasDerivAt (dΨ ω) (d2Ψ ω y) y) (ω : Ω) :
    HasDerivAt (fun x => profitDeriv ε Q P C dΨ x ω) (profitDeriv2 ε Q P C dΨ d2Ψ z ω) z := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (-ε)) (-ε * z ^ (-ε - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h2 : HasDerivAt (fun x : ℝ => x ^ (-ε - 1)) ((-ε - 1) * z ^ (-ε - 1 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h3 : HasDerivAt (fun x => dΨ ω (demand ε x P C ω))
      (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z)) z :=
    (hdΨ ω _ (demand_pos hz hP hC ω)).comp z (hasDerivAt_demand hz hP ω)
  have hG := (HasDerivAt.sub h1 ((HasDerivAt.mul h2 h3).const_mul (markup ε))).const_mul
    ((1 - ε) * Q ω * (P ω ^ ε * C ω))
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hz] with x hx
  exact profitDeriv_eq hx dΨ hP ω

/-- A bound on marginal profit on prices `≥ lo > 0` (Galí (2015), p. 56). -/
theorem abs_profitDeriv_le {ε z lo Qm W K : ℝ} (hε : 1 < ε) (hlo : 0 < lo) (hz : lo ≤ z)
    {Q P C : Ω → ℝ} {dΨ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω) (ω : Ω) (hQ0 : 0 < Q ω)
    (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ ε * C ω) (hW : P ω ^ ε * C ω ≤ W)
    (hd : |dΨ ω (demand ε z P C ω)| ≤ K) :
    |profitDeriv ε Q P C dΨ z ω|
      ≤ (ε - 1) * Qm * W * (lo ^ (-ε) + markup ε * (lo ^ (-ε - 1) * K)) := by
  have hz0 : 0 < z := hlo.trans_le hz
  rw [profitDeriv_eq hz0 dΨ hP ω]
  have hM := markup_pos hε
  have a0 : 0 ≤ z ^ (-ε) := Real.rpow_nonneg hz0.le _
  have a1 : 0 ≤ z ^ (-ε - 1) := Real.rpow_nonneg hz0.le _
  have b0 : z ^ (-ε) ≤ lo ^ (-ε) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b1 : z ^ (-ε - 1) ≤ lo ^ (-ε - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have hc : |(1 - ε) * Q ω * (P ω ^ ε * C ω)| ≤ (ε - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - ε ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have hi : |z ^ (-ε) - markup ε * (z ^ (-ε - 1) * dΨ ω (demand ε z P C ω))|
      ≤ lo ^ (-ε) + markup ε * (lo ^ (-ε - 1) * K) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg a0, abs_mul, abs_of_pos hM, abs_mul, abs_of_nonneg a1]
    gcongr
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- A bound on the derivative of marginal profit on prices `≥ lo > 0`
(Galí (2015), p. 56). -/
theorem abs_profitDeriv2_le {ε z lo Qm W K Yh : ℝ} (hε : 1 < ε) (hlo : 0 < lo)
    (hz : lo ≤ z) {Q P C : Ω → ℝ} {dΨ d2Ψ : Ω → ℝ → ℝ} (hP : ∀ ω, 0 < P ω)
    (hC : ∀ ω, 0 < C ω) (ω : Ω) (hQ0 : 0 < Q ω) (hQ : Q ω ≤ Qm) (hW0 : 0 ≤ P ω ^ ε * C ω)
    (hW : P ω ^ ε * C ω ≤ W) (hd : |dΨ ω (demand ε z P C ω)| ≤ K)
    (hd2 : |d2Ψ ω (demand ε z P C ω)| ≤ K) (hY : demand ε z P C ω ≤ Yh) :
    |profitDeriv2 ε Q P C dΨ d2Ψ z ω| ≤ (ε - 1) * Qm * W * (ε * lo ^ (-ε - 1)
      + markup ε * ((ε + 1) * lo ^ (-ε - 1 - 1) * K + lo ^ (-ε - 1) * (K * (ε * (Yh / lo))))) := by
  have hz0 : 0 < z := hlo.trans_le hz
  have hM := markup_pos hε
  have hε0 : 0 < ε := by linarith
  have hY0 := demand_pos (ε := ε) hz0 hP hC ω
  have a1 : 0 ≤ z ^ (-ε - 1) := Real.rpow_nonneg hz0.le _
  have a2 : 0 ≤ z ^ (-ε - 1 - 1) := Real.rpow_nonneg hz0.le _
  have b1 : z ^ (-ε - 1) ≤ lo ^ (-ε - 1) := Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have b2 : z ^ (-ε - 1 - 1) ≤ lo ^ (-ε - 1 - 1) :=
    Real.rpow_le_rpow_of_nonpos hlo hz (by linarith)
  have bY : demand ε z P C ω / z ≤ Yh / lo := div_le_div₀ (hY0.le.trans hY) hY hlo hz
  have hK : 0 ≤ K := (abs_nonneg _).trans hd
  have hc : |(1 - ε) * Q ω * (P ω ^ ε * C ω)| ≤ (ε - 1) * Qm * W := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : 1 - ε ≤ 0), abs_of_pos hQ0,
      abs_of_nonneg hW0, neg_sub]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by linarith)) hW hW0
      (mul_nonneg (by linarith) (hQ0.le.trans hQ))
  have e1 : |-ε * z ^ (-ε - 1)| = ε * z ^ (-ε - 1) := by
    rw [abs_mul, abs_neg, abs_of_pos hε0, abs_of_nonneg a1]
  have e2 : |(-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)|
      = (ε + 1) * z ^ (-ε - 1 - 1) * |dΨ ω (demand ε z P C ω)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg a2, abs_of_nonpos (by linarith : -ε - 1 ≤ 0)]
    ring
  have e3 : |z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z))|
      = z ^ (-ε - 1) * (|d2Ψ ω (demand ε z P C ω)| * (ε * (demand ε z P C ω / z))) := by
    have hn : -ε * demand ε z P C ω / z ≤ 0 := by
      rw [neg_mul, neg_div]; exact neg_nonpos.mpr (by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg a1, abs_of_nonpos hn]
    ring
  have hi : |-ε * z ^ (-ε - 1) - markup ε *
      ((-ε - 1) * z ^ (-ε - 1 - 1) * dΨ ω (demand ε z P C ω)
        + z ^ (-ε - 1) * (d2Ψ ω (demand ε z P C ω) * (-ε * demand ε z P C ω / z)))|
      ≤ ε * lo ^ (-ε - 1)
        + markup ε * ((ε + 1) * lo ^ (-ε - 1 - 1) * K + lo ^ (-ε - 1) * (K * (ε * (Yh / lo)))) := by
    refine (abs_sub _ _).trans ?_
    rw [e1, abs_mul, abs_of_pos hM]
    refine add_le_add (by gcongr) (mul_le_mul_of_nonneg_left ?_ hM.le)
    refine (abs_add_le _ _).trans ?_
    rw [e2, e3]
    have hYz : 0 ≤ demand ε z P C ω / z := by positivity
    gcongr
  unfold profitDeriv2
  rw [abs_mul]
  exact mul_le_mul hc hi (abs_nonneg _)
    (mul_nonneg (mul_nonneg (by linarith) (hQ0.le.trans hQ)) (hW0.trans hW))

/-- **Local Lipschitz bounds on marginal profit from primitives** (Galí (2015),
p. 56): under `Primitives`, marginal profit is Lipschitz in the reset price near
every positive price, uniformly in the state. -/
theorem lipschitz_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ k, ∀ y, 0 < y → ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |profitDeriv ε (Q k) (P k) (C k) (dΨ k) z ω
        - profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ L * |z - y| := by
  obtain ⟨-, hβ, -, hε, hm, hQ, hP, hC, -, hdΨ, hΨb⟩ := hprim
  intro k y hy
  have hε0 : 0 ≤ ε := by linarith
  have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
  have hCpos : ∀ ω, 0 < C k ω := fun ω => hm.trans_le (hC k ω).1
  set lo := y / 2 with hlo_def
  set hi := 2 * y with hhi_def
  have hlo : 0 < lo := by positivity
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  set Yh := lo ^ (-ε) * Khi
  have hy1 : 0 < hi ^ (-ε) * Klo := by positivity
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-ε) * Klo) Yh hy1
  set L₀ := (ε - 1) * (|Qb| * β ^ k) * Khi * (ε * lo ^ (-ε - 1) + markup ε *
    ((ε + 1) * lo ^ (-ε - 1 - 1) * |K| + lo ^ (-ε - 1) * (|K| * (ε * (Yh / lo)))))
  refine ⟨max L₀ 0, le_max_right _ _, lo, hlo, fun z hz ω => ?_⟩
  have hball : ∀ x ∈ Metric.ball y lo, lo ≤ x ∧ x ≤ hi := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith
  have hd : ∀ x ∈ Metric.ball y lo, HasDerivWithinAt
      (fun x => profitDeriv ε (Q k) (P k) (C k) (dΨ k) x ω)
      (profitDeriv2 ε (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω) (Metric.ball y lo) x :=
    fun x hx => (hasDerivAt_profitDeriv (hlo.trans_le (hball x hx).1) hPpos hCpos (hdΨ k)
      ω).hasDerivWithinAt
  have hb : ∀ x ∈ Metric.ball y lo,
      ‖profitDeriv2 ε (Q k) (P k) (C k) (dΨ k) (d2Ψ k) x ω‖ ≤ max L₀ 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hball x hx
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm hlo hx1 hx2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hε0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, hK2⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    rw [Real.norm_eq_abs]
    exact (abs_profitDeriv2_le hε hlo hx1 hPpos hCpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ ε * m).trans hw1) hw2 (hK1.trans (le_abs_self _))
      (hK2.trans (le_abs_self _)) hY2).trans (le_max_left _ _)
  have hyb : y ∈ Metric.ball y lo := Metric.mem_ball_self hlo
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_ball y lo) hyb hz
  simpa only [Real.norm_eq_abs] using this

/-- **Domination of marginal profit from primitives** (Galí (2015), p. 56): under
`Primitives`, on every interval `(a, b)` with `a > 0`, marginal profit at horizon `k`
is bounded by `uₖ = c βᵏ`, and `∑ θᵏ uₖ < ∞` since `θβ < 1`. -/
theorem dominated_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) :
    ∀ a b, 0 < a → ∃ u : ℕ → ℝ, Summable (fun k => |θ| ^ k * u k) ∧
      ∀ k, ∀ y ∈ Set.Ioo a b, ∀ ω, |profitDeriv ε (Q k) (P k) (C k) (dΨ k) y ω| ≤ u k := by
  obtain ⟨hθ, hβ, hθβ, hε, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro a b ha
  have hε0 : 0 ≤ ε := by linarith
  set hi := max b a
  have hhi : 0 < hi := ha.trans_le (le_max_right _ _)
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  obtain ⟨K, hK⟩ := hΨb (hi ^ (-ε) * Klo) (a ^ (-ε) * Khi) (by positivity)
  set c := (ε - 1) * |Qb| * Khi * (a ^ (-ε) + markup ε * (a ^ (-ε - 1) * |K|))
  refine ⟨fun k => (ε - 1) * (|Qb| * β ^ k) * Khi * (a ^ (-ε) + markup ε * (a ^ (-ε - 1) * |K|)),
    ?_, fun k y hy ω => ?_⟩
  · refine ((summable_geometric_of_lt_one (mul_nonneg hθ hβ) hθβ).mul_left c).congr
      fun k => ?_
    rw [abs_of_nonneg hθ, mul_pow]
    ring
  · have hy1 : a ≤ y := hy.1.le
    have hy2 : y ≤ hi := hy.2.le.trans (le_max_left _ _)
    have hPpos : ∀ ω, 0 < P k ω := fun ω => hm.trans_le (hP k ω).1
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm ha hy1 hy2 (hP k) (hC k) ω
    obtain ⟨hw1, hw2⟩ := weight_bounds hε0 hm (hP k) (hC k) ω
    obtain ⟨-, hK1, -⟩ := hK k ω _ hY1 hY2
    have hQm : Q k ω ≤ |Qb| * β ^ k :=
      (hQ k ω).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    exact abs_profitDeriv_le hε ha hy1 hPpos ω (hQ k ω).1 hQm
      ((by positivity : (0 : ℝ) ≤ m ^ ε * m).trans hw1) hw2 (hK1.trans (le_abs_self _))

/-- **Convergence of the objective from primitives** (Galí (2015), p. 56): under
`Primitives`, the reset-price objective converges at every positive price. -/
theorem summable_profit_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) : ∀ y, 0 < y →
      Summable fun k => θ ^ k * 𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω := by
  obtain ⟨hθ, hβ, hθβ, hε, hm, hQ, hP, hC, -, -, hΨb⟩ := hprim
  intro y hy
  have hε0 : 0 ≤ ε := by linarith
  set Klo := m ^ ε * m
  set Khi := Mx ^ ε * Mx
  obtain ⟨K, hK⟩ := hΨb (y ^ (-ε) * Klo) (y ^ (-ε) * Khi) (by positivity)
  set c := |Qb| * (y * |y ^ (-ε) * Khi| + |K|)
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (mul_nonneg hθ hβ) hθβ).mul_left c) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hθ]
  have hb : ∀ ω', |profit ε (Q k) (P k) (C k) (Ψ k) y ω'| ≤ |Qb| * β ^ k *
      (y * |y ^ (-ε) * Khi| + |K|) := by
    intro ω'
    obtain ⟨hY1, hY2⟩ := demand_bounds hε0 hm hy le_rfl le_rfl (hP k) (hC k) ω'
    obtain ⟨hK0, -, -⟩ := hK k ω' _ hY1 hY2
    have hY0 : 0 < demand ε y (P k) (C k) ω' :=
      demand_pos hy (fun ω => hm.trans_le (hP k ω).1) (fun ω => hm.trans_le (hC k ω).1) ω'
    have hQm : Q k ω' ≤ |Qb| * β ^ k :=
      (hQ k ω').2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hβ k))
    unfold profit
    rw [abs_mul, abs_of_pos (hQ k ω').1]
    refine mul_le_mul hQm ((abs_sub _ _).trans (add_le_add ?_
      (hK0.trans (le_abs_self _)))) (abs_nonneg _) ((hQ k ω').1.le.trans hQm)
    rw [abs_mul, abs_of_pos hy, abs_of_pos hY0]
    exact mul_le_mul_of_nonneg_left (hY2.trans (le_abs_self _)) hy.le
  calc θ ^ k * |𝔼.E t (profit ε (Q k) (P k) (C k) (Ψ k) y) ω|
      ≤ θ ^ k * (|Qb| * β ^ k * (y * |y ^ (-ε) * Khi| + |K|)) :=
        mul_le_mul_of_nonneg_left (𝔼.abs_E_le hb t ω) (pow_nonneg hθ k)
    _ = c * (θ * β) ^ k := by rw [mul_pow]; ring

/-- **The derivative of the reset-price objective, from primitives only**
(Galí (2015), eq. (10), p. 56): under `Primitives`, at every positive price the
objective has derivative `((1 − ε)/P*) ∑ₖ θᵏ E_t[Q_{t,t+k} Y_{t+k|t}(P* − M Ψ'_{t+k|t})]`. -/
theorem hasDerivAt_objective_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => objective 𝔼 θ ε Q P C Ψ t z ω)
      ((1 - ε) / x * focSum 𝔼 θ ε Q P C dΨ t x ω) x := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨-, -, -, hε, hm, -, hP, hC, hΨ, -, -⟩ := hprim
  exact hasDerivAt_objective_of_pos 𝔼 hε (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hLip hloc t ω hs hx

/-- **(10) is necessary, from primitives only** (Galí (2015), eq. (10), p. 56): under
`Primitives`, a local maximum `P* > 0` of the reset-price objective satisfies (10). -/
theorem foc_of_isLocalMax_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ) {t : ℕ}
    {ω : Ω} {x : ℝ} (hx : 0 < x)
    (hmax : IsLocalMax (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) x) :
    focSum 𝔼 θ ε Q P C dΨ t x ω = 0 :=
  foc_of_isLocalMax 𝔼 hprim.2.2.2.1 hx (hasDerivAt_objective_of_primitives 𝔼 hprim t ω hx) hmax

/-- **(10) characterises the optimal reset price, from primitives only**
(Galí (2015), eq. (10), p. 56): under `Primitives`, convex costs (`Ψ'' ≥ 0`) and the
book's normalisation `Λ_{t,t} = 1` (so `Q_{t,t} = 1/P_t`), a positive price maximises
the objective over all positive prices if and only if it satisfies (10), and it is
then the unique maximiser. -/
theorem isMaxOn_iff_foc_of_primitives {θ β ε Qb m Mx : ℝ} {Q P C : ℕ → Ω → ℝ}
    {Ψ dΨ d2Ψ : ℕ → Ω → ℝ → ℝ} (hprim : Primitives θ β ε Qb m Mx Q P C Ψ dΨ d2Ψ)
    (hconv : ∀ k ω y, 0 < y → 0 ≤ d2Ψ k ω y) (hQ0 : ∀ ω, Q 0 ω = (P 0 ω)⁻¹) (t : ℕ)
    (ω : Ω) {x : ℝ} (hx : 0 < x) :
    (IsMaxOn (fun z => objective 𝔼 θ ε Q P C Ψ t z ω) (Set.Ioi 0) x ↔
        focSum 𝔼 θ ε Q P C dΨ t x ω = 0) ∧
      (focSum 𝔼 θ ε Q P C dΨ t x ω = 0 → ∀ y, 0 < y → y ≠ x →
        objective 𝔼 θ ε Q P C Ψ t y ω < objective 𝔼 θ ε Q P C Ψ t x ω) := by
  have hLip := lipschitz_of_primitives hprim
  have hloc := dominated_of_primitives hprim
  have hs := summable_profit_of_primitives 𝔼 hprim t ω
  obtain ⟨hθ, -, -, hε, hm, hQ, hP, hC, hΨ, hdΨ, -⟩ := hprim
  have hε0 : 0 ≤ ε := by linarith
  have hmono : ∀ k ω, MonotoneOn (dΨ k ω) (Set.Ioi 0) := by
    intro k ω
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun y hy => (hdΨ k ω y hy).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioi]
      exact fun y hy => (hdΨ k ω y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro y hy
      rw [(hdΨ k ω y hy).deriv]
      exact hconv k ω y hy
  have hpos : 0 < 𝔼.E t (fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω')) ω := by
    have hMx : 0 < Mx := hm.trans_le ((hP 0 ω).1.trans (hP 0 ω).2)
    have hc : 0 < Mx⁻¹ * (m ^ ε * m) := by positivity
    have hle : (fun _ : Ω => Mx⁻¹ * (m ^ ε * m))
        ≤ fun ω' => Q 0 ω' * (P 0 ω' ^ ε * C 0 ω') := fun ω' => by
      simp only
      rw [hQ0 ω']
      have hP0 : 0 < P 0 ω' := hm.trans_le (hP 0 ω').1
      exact mul_le_mul (inv_anti₀ hP0 (hP 0 ω').2)
        (weight_bounds hε0 hm (hP 0) (hC 0) ω').1 (by positivity) (inv_nonneg.mpr hP0.le)
    have := 𝔼.mono t hle ω
    rw [𝔼.const] at this
    exact hc.trans_le this
  exact isMaxOn_iff_foc 𝔼 hε hθ (fun k ω => (hQ k ω).1) (fun k ω => hm.trans_le (hP k ω).1)
    (fun k ω => hm.trans_le (hC k ω).1) hΨ hmono hLip hloc t ω hs hpos hx

end Gali.BasicNewKeynesianModel.ResetPrice
