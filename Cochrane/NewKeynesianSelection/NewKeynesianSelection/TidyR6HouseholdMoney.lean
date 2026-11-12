/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6ExpectationsMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Chapter 19 household problem on a genuine probability space

Restated from the Cochrane Monetarism project (its module HouseholdMeasure) with the namespace
renamed, for the household problem behind Cochrane (2023), eq. (16.31), p. 393 (module
TidyR6Household16_31).

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 439–441
(eqs. (19.9)–(19.12) and footnote 1) and §19.5.1, pp. 448–449 (eqs. (19.24)–(19.30)), in the
measure-theoretic setting of TidyR6ExpectationsMeasure: a probability space with a filtration,
`E_t = μ[· | 𝓕_t]`, information that may grow forever, and every budget constraint holding almost
surely. This module sets up the household problem common to the money-in-utility model and the
cash-in-advance model and proves the two general facts that both use: the first-order condition
along every bounded, measurable, budget-neutral deviation, and sufficiency under concavity and the
transversality condition.

## The household problem

"The household operates in complete contingent claim markets with state price `Λ_t`" (p. 439).
`Λ` is the real state-price density and `P` the price level, so the nominal state-price density is
`pk_t = Λ_t/P_t` and a nominal payoff `a_{t+1}` (measurable at `t + 1`) costs
`E_t[pk_{t+1} a_{t+1}]/pk_t` at `t` (`claimCost`). The one-period nominal bond price is
`Q_t = E_t[pk_{t+1}]/pk_t` (`bondPrice`) and `ι_t = 1 − Q_t = i_t/(1 + i_t)` (`iota`).

* `Flow`: the period budget constraint (19.10)/(19.27) with contingent claims,
  `a_t + M_{t−1} + P_t(y_t − c_t) = (cost of a_{t+1}) + M_t + P_ts_t`, almost surely at every
  date, where `a_t` is the nominal payoff of the claims maturing at `t` (the book's `B_{t−1}`),
  `M_t = P_tm_t` is money held overnight (real balances `m_t`) and `M_{−1} = N₀` (`moneyIn`).
* `Feasible`: adapted plans satisfying the flow constraint, the integrability that makes present
  values meaningful, and the no-Ponzi condition `liminf_T E[pk_T(a_T + M_{T−1})] ≥ 0`.
* `UAdmissible`, `expU`: expected discounted utility `E ∑ βᵗ u_t` as a genuine integral of an
  absolutely convergent series.
* `Optimal`: feasible, satisfying an extra constraint `Con` on `(c, m)` (none for money in the
  utility function; the cash-in-advance constraints in the Monetarism project), admissible, and
  unbeaten by any feasible admissible plan satisfying `Con`.

## Main results

* `pert_feasible`: for bounded `z₁, ζ₁` known at `t` and `z₂, ζ₂` known at `t + 1` with
  `Λ_t(z₁ + ι_tζ₁) + E_t[Λ_{t+1}(z₂ + ι_{t+1}ζ₂)] = 0` (the deviation costs nothing at date-`t`
  prices), changing `(c_t, m_t, c_{t+1}, m_{t+1})` by `ε(z₁, ζ₁, z₂, ζ₂)` and the claims maturing
  at `t + 1` and `t + 2` accordingly keeps every flow constraint almost surely.
* `pair_foc`: hence at an optimum `βᵗE[u_c z₁ + u_m ζ₁] + β^{t+1}E[u_c z₂ + u_m ζ₂] = 0`
  (differentiation of expected utility under the integral sign).
* `wealth_step`, `wealth_telescope`: the flow constraint integrates to
  `E[pk_t(a_t + M_{t−1})] = E[pk_{t+1}(a_{t+1} + M_t)] + E[Λ_t(c_t + ι_tm_t + s_t − y_t)]`, the
  unconditional form of the present-value budget (19.12)/(19.30).
* `pv_budget`: with the transversality condition `E[pk_T(a_T + M_{T−1})] → 0`, initial wealth
  equals the present value of the outlays.
* `optimal_of_supergradient`: a feasible admissible plan satisfying the transversality condition
  and the supergradient bound
  `βᵗ(u(c'_t, m'_t) − u(c_t, m_t)) ≤ λΛ_t((c'_t − c_t) + ι_t(m'_t − m_t))` against every
  competitor is optimal.
* `bundle_euler`, `bundle_multiplier_const`: for a consumption bundle carrying `θ` units of real
  balances per unit (cost `w_t = 1 + θι_t`, `wedge`), an optimum has
  `βᵗ(u_c + θu_m)(t) = λΛ_tw_t` almost surely with one multiplier `λ` known at date `0`.
* Tools: `hasDerivAt_integral_comp₂` (differentiation under the integral sign), `Smooth₂` and
  `smooth₂_sep`, `UAdmissible.hasSum` (Fubini for series), `UAdmissible.modify`,
  `UAdmissible.of_bdd`, essentially bounded variables `BddAt`, and the namespace TreeLink (a finite
  event tree
  as a probability space: almost sure statements hold at every node, measurability is
  constancy on information cells).
-/

namespace Cochrane.NewKeynesianSelection.TidyR6HouseholdMoney

open MeasureTheory ProbabilityTheory Filter Topology TidyR6ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Measure-theoretic tools -/

/-- Cochrane (2023), (19.9), p. 439 (expected discounted utility is an infinite sum; restated
from the Cochrane IntertemporalModel project): an almost surely convergent series of a.e.
strongly measurable variables is a.e. strongly measurable. -/
theorem aestronglyMeasurable_tsum {μ : Measure Ω} {f : ℕ → Ω → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (f n) μ) (hs : ∀ᵐ ω ∂μ, Summable fun n => f n ω) :
    AEStronglyMeasurable (fun ω => ∑' n, f n ω) μ :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ n ∈ Finset.range N, f n ω)
    (fun _ => Finset.aestronglyMeasurable_fun_sum _ fun n _ => hm n)
    (hs.mono fun _ h => h.hasSum.tendsto_sum_nat)

/-- Cochrane (2023), (19.9), p. 439: a continuous function of two real variables is bounded on
every square `[−R, R]²`. -/
theorem exists_abs_le_of_continuous₂ {v : ℝ → ℝ → ℝ}
    (hv : Continuous fun p : ℝ × ℝ => v p.1 p.2) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x y, |x| ≤ R → |y| ≤ R → |v x y| ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := -R) (b := R)).prod
    (isCompact_Icc (a := -R) (b := R))).exists_bound_of_continuousOn hv.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x y hx hy => ?_⟩
  have := hC (x, y) (Set.mk_mem_prod (Set.mem_Icc.2 (abs_le.1 hx)) (Set.mem_Icc.2 (abs_le.1 hy)))
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Cochrane (2023), (19.9), p. 439: a continuous function of two essentially bounded variables is
integrable on a probability space. -/
theorem integrable_comp₂_of_bdd {μ : Measure Ω} [IsFiniteMeasure μ] {v : ℝ → ℝ → ℝ}
    (hv : Continuous fun p : ℝ × ℝ => v p.1 p.2) {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {R : ℝ} (hfR : ∀ᵐ ω ∂μ, |f ω| ≤ R)
    (hgR : ∀ᵐ ω ∂μ, |g ω| ≤ R) : Integrable (fun ω => v (f ω) (g ω)) μ := by
  obtain ⟨C, -, hC⟩ := exists_abs_le_of_continuous₂ hv R
  refine Integrable.of_bound (hv.comp_aestronglyMeasurable (hf.prodMk hg)) C ?_
  filter_upwards [hfR, hgR] with ω h1 h2
  rw [Real.norm_eq_abs]
  exact hC _ _ h1 h2

/-- Cochrane (2023), (19.9), p. 439: the regularity of the period utility `u(c, m)` used for the
first-order conditions (19.13)–(19.14): `u` is differentiable on `ℝ²` with partial derivatives
`u_c`, `u_m`, both continuous. -/
def Smooth₂ (u uc um : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2)
      (uc x y • ContinuousLinearMap.fst ℝ ℝ ℝ + um x y • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y)) ∧
    (Continuous fun p : ℝ × ℝ => uc p.1 p.2) ∧ Continuous fun p : ℝ × ℝ => um p.1 p.2

/-- Cochrane (2023), (19.9), p. 439: a smooth period utility is continuous. -/
theorem Smooth₂.continuous {u uc um : ℝ → ℝ → ℝ} (h : Smooth₂ u uc um) :
    Continuous fun p : ℝ × ℝ => u p.1 p.2 :=
  continuous_iff_continuousAt.2 fun p => (h.1 p.1 p.2).continuousAt

/-- Cochrane (2023), (19.9), p. 439: along the line `ε ↦ (x + εg, y + εk)` a smooth period
utility has derivative `u_c g + u_m k`. -/
theorem Smooth₂.hasDerivAt_line {u uc um : ℝ → ℝ → ℝ} (h : Smooth₂ u uc um) (x y g k ε : ℝ) :
    HasDerivAt (fun e => u (x + e * g) (y + e * k))
      (uc (x + ε * g) (y + ε * k) * g + um (x + ε * g) (y + ε * k) * k) ε := by
  have hpath : HasDerivAt (fun e : ℝ => (x + e * g, y + e * k)) (g, k) ε := by
    have h1 : HasDerivAt (fun e : ℝ => x + e * g) g ε := by
      simpa using ((hasDerivAt_id ε).mul_const g).const_add x
    have h2 : HasDerivAt (fun e : ℝ => y + e * k) k ε := by
      simpa using ((hasDerivAt_id ε).mul_const k).const_add y
    exact h1.prodMk h2
  have := (h.1 (x + ε * g) (y + ε * k)).comp_hasDerivAt ε hpath
  have e : (uc (x + ε * g) (y + ε * k) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      um (x + ε * g) (y + ε * k) • ContinuousLinearMap.snd ℝ ℝ ℝ) (g, k) =
      uc (x + ε * g) (y + ε * k) * g + um (x + ε * g) (y + ε * k) * k := by
    simp [smul_eq_mul]
  rw [e] at this
  exact this

/-- Cochrane (2023), (19.13), p. 440: a smooth period utility has partial derivative `u_c` in
consumption. -/
theorem Smooth₂.hasDerivAt_fst {u uc um : ℝ → ℝ → ℝ} (h : Smooth₂ u uc um) (x y : ℝ) :
    HasDerivAt (fun x' => u x' y) (uc x y) x := by
  have hpath : HasDerivAt (fun x' : ℝ => (x', y)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have := (h.1 x y).comp_hasDerivAt x hpath
  have e : (uc x y • ContinuousLinearMap.fst ℝ ℝ ℝ + um x y • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((1 : ℝ), (0 : ℝ)) = uc x y := by simp
  rw [e] at this
  exact this

/-- Cochrane (2023), (19.14), p. 440: a smooth period utility has partial derivative `u_m` in
real balances. -/
theorem Smooth₂.hasDerivAt_snd {u uc um : ℝ → ℝ → ℝ} (h : Smooth₂ u uc um) (x y : ℝ) :
    HasDerivAt (fun y' => u x y') (um x y) y := by
  have hpath : HasDerivAt (fun y' : ℝ => (x, y')) ((0 : ℝ), (1 : ℝ)) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have := (h.1 x y).comp_hasDerivAt y hpath
  have e : (uc x y • ContinuousLinearMap.fst ℝ ℝ ℝ + um x y • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((0 : ℝ), (1 : ℝ)) = um x y := by simp
  rw [e] at this
  exact this

/-- Cochrane (2023), (19.17)–(19.18), p. 441 (separable utility `u(c) + v(m)`): a separable
period utility with continuously differentiable parts is smooth, with `u_c = u'(c)` and
`u_m = v'(m)`. -/
theorem smooth₂_sep {f f' g g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : Continuous g') :
    Smooth₂ (fun x y => f x + g y) (fun x _ => f' x) (fun _ y => g' y) := by
  refine ⟨fun x y => ?_, hf'.comp continuous_fst, hg'.comp continuous_snd⟩
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => f p.1) (f' x • ContinuousLinearMap.fst ℝ ℝ ℝ) (x, y) := by
    have := (hf x).hasFDerivAt.comp (x, y) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, y)))
    have e : (ContinuousLinearMap.toSpanSingleton ℝ (f' x)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ) = f' x • ContinuousLinearMap.fst ℝ ℝ ℝ := by
      ext <;> simp [mul_comm]
    rw [e] at this
    exact this
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => g p.2) (g' y • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) := by
    have := (hg y).hasFDerivAt.comp (x, y) (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y)))
    have e : (ContinuousLinearMap.toSpanSingleton ℝ (g' y)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ) = g' y • ContinuousLinearMap.snd ℝ ℝ ℝ := by
      ext <;> simp [mul_comm]
    rw [e] at this
    exact this
  exact h1.add h2

/-- Cochrane (2023), (19.13)–(19.14), p. 440 ("The first-order conditions"): differentiation of
expected utility under the integral sign. For a smooth `u` and essentially bounded `f, g, h, k`,
`ε ↦ E u(f + εg, h + εk)` has derivative `E[u_c(f, h) g + u_m(f, h) k]` at `0`. -/
theorem hasDerivAt_integral_comp₂ {μ : Measure Ω} [IsFiniteMeasure μ] {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um) {f g h k : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ)
    (hk : AEStronglyMeasurable k μ) {R : ℝ} (hfR : ∀ᵐ ω ∂μ, |f ω| ≤ R)
    (hgR : ∀ᵐ ω ∂μ, |g ω| ≤ R) (hhR : ∀ᵐ ω ∂μ, |h ω| ≤ R) (hkR : ∀ᵐ ω ∂μ, |k ω| ≤ R) :
    HasDerivAt (fun ε => ∫ ω, u (f ω + ε * g ω) (h ω + ε * k ω) ∂μ)
      (∫ ω, (uc (f ω) (h ω) * g ω + um (f ω) (h ω) * k ω) ∂μ) 0 := by
  have hvc := hu.continuous
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuous₂ hu.2.1 (2 * R)
  obtain ⟨D, hD0, hD⟩ := exists_abs_le_of_continuous₂ hu.2.2 (2 * R)
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun ω => u (f ω + ε * g ω) (h ω + ε * k ω)) μ := fun ε =>
    hvc.comp_aestronglyMeasurable ((hf.add (hg.const_mul ε)).prodMk (hh.add (hk.const_mul ε)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun ε ω => u (f ω + ε * g ω) (h ω + ε * k ω))
    (F' := fun ε ω => uc (f ω + ε * g ω) (h ω + ε * k ω) * g ω +
      um (f ω + ε * g ω) (h ω + ε * k ω) * k ω)
    (bound := fun _ => C * R + D * R) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall hmeas)
    (by simpa using integrable_comp₂_of_bdd hvc hf hh hfR hhR)
    (((hu.2.1.comp_aestronglyMeasurable ((hf.add (hg.const_mul 0)).prodMk
      (hh.add (hk.const_mul 0)))).mul hg).add
      ((hu.2.2.comp_aestronglyMeasurable ((hf.add (hg.const_mul 0)).prodMk
      (hh.add (hk.const_mul 0)))).mul hk)) ?_ (integrable_const _) ?_
  · simpa using key.2
  · filter_upwards [hfR, hgR, hhR, hkR] with ω h1 h2 h3 h4
    intro ε hε
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    have hR : 0 ≤ R := (abs_nonneg _).trans h1
    have hx : ∀ a b : ℝ, |a| ≤ R → |b| ≤ R → |a + ε * b| ≤ 2 * R := by
      intro a b ha hb
      calc |a + ε * b| ≤ |a| + |ε| * |b| := by rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ R + 1 * R := add_le_add ha (mul_le_mul hε.le hb (abs_nonneg _) zero_le_one)
        _ = 2 * R := by ring
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (hC _ _ (hx _ _ h1 h2) (hx _ _ h3 h4)) h2 (abs_nonneg _) hC0
    · rw [abs_mul]
      exact mul_le_mul (hD _ _ (hx _ _ h1 h2) (hx _ _ h3 h4)) h4 (abs_nonneg _) hD0
  · exact Eventually.of_forall fun ω ε _ =>
      hu.hasDerivAt_line (f ω) (h ω) (g ω) (k ω) ε

/-- Cochrane (2023), (19.13)–(19.14), p. 440: an essentially bounded variable whose integral
against itself vanishes is zero almost surely. -/
theorem ae_eq_zero_of_integral_mul_self {μ : Measure Ω} {G : Ω → ℝ}
    (hi : Integrable (fun ω => G ω * G ω) μ) (h0 : ∫ ω, G ω * G ω ∂μ = 0) : G =ᵐ[μ] 0 := by
  have hnn : 0 ≤ᵐ[μ] fun ω => G ω * G ω := Eventually.of_forall fun ω => mul_self_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h0] with ω hω
  exact mul_self_eq_zero.1 hω

/-- Cochrane (2023), (19.9), p. 439 (a summable sequence changed at finitely many dates): if `f`
agrees with the summable `g` off the finite set `F`, then
`∑ f = ∑ g + ∑_{n ∈ F} (f_n − g_n)`. -/
theorem hasSum_of_eq_off_finset {f g : ℕ → ℝ} (hg : Summable g) (F : Finset ℕ)
    (h : ∀ n ∉ F, f n = g n) : HasSum f (∑' n, g n + ∑ n ∈ F, (f n - g n)) := by
  have h1 : HasSum (fun n => f n - g n) (∑ n ∈ F, (f n - g n)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [h n hn, sub_self]
  have := hg.hasSum.add h1
  simpa using this

/-! ### Expected discounted utility -/

variable (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), (19.9), p. 439, "max `E ∑ βᵗ u(c_t, M_t/P_t)`": a process of period utilities
`f_n` has absolutely convergent expected discounted utility, `E ∑_n βⁿ|f_n| < ∞` (each `f_n` a.e.
measurable, the series almost surely convergent and its sum integrable). -/
def UAdmissible (β : ℝ) (f : ℕ → Ω → ℝ) : Prop :=
  (∀ n, AEStronglyMeasurable (f n) S.μ) ∧ (∀ᵐ ω ∂S.μ, Summable fun n => β ^ n * |f n ω|) ∧
    Integrable (fun ω => ∑' n, β ^ n * |f n ω|) S.μ

/-- Cochrane (2023), (19.9), p. 439: expected discounted utility `E ∑_t βᵗ f_t`, a genuine
integral of the realised discounted utility. -/
noncomputable def expU (β : ℝ) (f : ℕ → Ω → ℝ) : ℝ := ∫ ω, ∑' n, β ^ n * f n ω ∂S.μ

variable {S}

/-- Cochrane (2023), (19.9), p. 439: an admissible utility process has an almost surely
convergent discounted sum. -/
theorem UAdmissible.summable {β : ℝ} (hβ : 0 ≤ β) {f : ℕ → Ω → ℝ} (h : UAdmissible S β f) :
    ∀ᵐ ω ∂S.μ, Summable fun n => β ^ n * f n ω :=
  h.2.1.mono fun _ hs => Summable.of_norm_bounded hs fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]

/-- Cochrane (2023), (19.9), p. 439: in an admissible utility process each period's utility is
integrable. -/
theorem UAdmissible.integrable {β : ℝ} (hβ : 0 < β) {f : ℕ → Ω → ℝ} (h : UAdmissible S β f)
    (n : ℕ) : Integrable (f n) S.μ := by
  refine Integrable.mono' (h.2.2.const_mul (β ^ n)⁻¹) (h.1 n) ?_
  filter_upwards [h.2.1] with ω hs
  have hbn : 0 < β ^ n := pow_pos hβ n
  have hle : β ^ n * |f n ω| ≤ ∑' m, β ^ m * |f m ω| :=
    hs.le_tsum n fun m _ => mul_nonneg (pow_nonneg hβ.le m) (abs_nonneg _)
  rw [Real.norm_eq_abs, le_inv_mul_iff₀ hbn]
  exact hle

/-- Cochrane (2023), (19.9), p. 439: the realised discounted utility of an admissible process is
integrable, so `expU` is a genuine expectation. -/
theorem UAdmissible.integrable_sum {β : ℝ} (hβ : 0 ≤ β) {f : ℕ → Ω → ℝ}
    (h : UAdmissible S β f) : Integrable (fun ω => ∑' n, β ^ n * f n ω) S.μ := by
  refine Integrable.mono' h.2.2
    (aestronglyMeasurable_tsum (fun n => (h.1 n).const_mul _) (h.summable hβ)) ?_
  filter_upwards [h.2.1] with ω hs
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · refine hs.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]
  · refine tsum_congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ]

/-- Cochrane (2023), (19.9), p. 439: for an admissible process, expected discounted utility is
the discounted sum of expected period utilities, `E ∑ βⁿ f_n = ∑ βⁿ E f_n` (Fubini for series). -/
theorem UAdmissible.hasSum {β : ℝ} (hβ : 0 < β) {f : ℕ → Ω → ℝ} (h : UAdmissible S β f) :
    HasSum (fun n => β ^ n * ∫ ω, f n ω ∂S.μ) (expU S β f) := by
  have hint : ∀ n, Integrable (fun ω => β ^ n * f n ω) S.μ := fun n =>
    (h.integrable hβ n).const_mul _
  have hnorm : ∀ n, ∫ ω, ‖β ^ n * f n ω‖ ∂S.μ = ∫ ω, β ^ n * |f n ω| ∂S.μ := fun n =>
    integral_congr_ae (Eventually.of_forall fun ω => by
      change ‖β ^ n * f n ω‖ = β ^ n * |f n ω|
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.le])
  have hsum : Summable fun n => ∫ ω, ‖β ^ n * f n ω‖ ∂S.μ := by
    simp_rw [hnorm]
    refine summable_of_sum_range_le (c := ∫ ω, ∑' n, β ^ n * |f n ω| ∂S.μ)
      (fun n => integral_nonneg fun ω => mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _))
      fun N => ?_
    rw [← integral_finsetSum _ fun n _ => ((h.integrable hβ n).abs).const_mul _]
    refine integral_mono_ae (integrable_finsetSum _ fun n _ =>
      ((h.integrable hβ n).abs).const_mul _) h.2.2 ?_
    filter_upwards [h.2.1] with ω hs
    exact hs.sum_le_tsum _ fun n _ => mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _)
  have := hasSum_integral_of_summable_integral_norm hint hsum
  simpa [expU, integral_const_mul] using this

/-- Cochrane (2023), (19.9), p. 439: a uniformly bounded, measurable utility process is
admissible when `0 ≤ β < 1`. -/
theorem UAdmissible.of_bdd {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → Ω → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (f n) S.μ) {K : ℝ} (hK : ∀ n ω, |f n ω| ≤ K) :
    UAdmissible S β f := by
  have hgeo : Summable fun n : ℕ => β ^ n * K :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_right K
  have hs : ∀ ω, Summable fun n => β ^ n * |f n ω| := fun ω =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hβ0 n) (abs_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hK n ω) (pow_nonneg hβ0 n)) hgeo
  refine ⟨hm, Eventually.of_forall hs, ?_⟩
  refine Integrable.of_bound (aestronglyMeasurable_tsum (fun n => ((hm n).norm.const_mul _))
    (Eventually.of_forall fun ω => (hs ω).congr fun n => rfl))
    (∑' n : ℕ, β ^ n * K) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun n =>
    mul_nonneg (pow_nonneg hβ0 n) (abs_nonneg _))]
  exact (hs ω).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hK n ω) (pow_nonneg hβ0 n))
    hgeo

/-- Cochrane (2023), footnote 1, p. 440 (modifying a plan at finitely many dates): if `f'` agrees
with the admissible `f` off the finite set of dates `F` and `f'_n` is integrable for `n ∈ F`,
then `f'` is admissible and `E ∑ βⁿ f'_n = E ∑ βⁿ f_n + ∑_{n ∈ F} βⁿ (E f'_n − E f_n)`. -/
theorem UAdmissible.modify {β : ℝ} (hβ : 0 < β) {f f' : ℕ → Ω → ℝ} (hf : UAdmissible S β f)
    (F : Finset ℕ) (heq : ∀ n ∉ F, f' n = f n) (hi : ∀ n ∈ F, Integrable (f' n) S.μ) :
    UAdmissible S β f' ∧
      expU S β f' = expU S β f +
        ∑ n ∈ F, β ^ n * (∫ ω, f' n ω ∂S.μ - ∫ ω, f n ω ∂S.μ) := by
  have hfi := hf.integrable hβ
  have hm : ∀ n, AEStronglyMeasurable (f' n) S.μ := fun n => by
    by_cases hn : n ∈ F
    · exact (hi n hn).aestronglyMeasurable
    · rw [heq n hn]
      exact hf.1 n
  have habs : ∀ᵐ ω ∂S.μ, HasSum (fun n => β ^ n * |f' n ω|)
      (∑' n, β ^ n * |f n ω| + ∑ n ∈ F, (β ^ n * |f' n ω| - β ^ n * |f n ω|)) := by
    filter_upwards [hf.2.1] with ω hs
    exact hasSum_of_eq_off_finset hs F fun n hn => by rw [heq n hn]
  have hsgn : ∀ᵐ ω ∂S.μ, HasSum (fun n => β ^ n * f' n ω)
      (∑' n, β ^ n * f n ω + ∑ n ∈ F, (β ^ n * f' n ω - β ^ n * f n ω)) := by
    filter_upwards [hf.summable hβ.le] with ω hs
    exact hasSum_of_eq_off_finset hs F fun n hn => by rw [heq n hn]
  have hFi : Integrable (fun ω =>
      ∑ n ∈ F, (β ^ n * |f' n ω| - β ^ n * |f n ω|)) S.μ :=
    integrable_finsetSum F fun n hn =>
      (((hi n hn).abs).const_mul _).sub (((hfi n).abs).const_mul _)
  refine ⟨⟨hm, habs.mono fun _ h => h.summable, ?_⟩, ?_⟩
  · refine (hf.2.2.add hFi).congr ?_
    filter_upwards [habs] with ω h
    exact h.tsum_eq.symm
  · have hFi' : ∀ n ∈ F, Integrable (fun ω => β ^ n * f' n ω - β ^ n * f n ω) S.μ :=
      fun n hn => ((hi n hn).const_mul _).sub ((hfi n).const_mul _)
    unfold expU
    rw [integral_congr_ae (hsgn.mono fun _ h => h.tsum_eq), integral_add
      (hf.integrable_sum hβ.le) (integrable_finsetSum F hFi'), integral_finsetSum F hFi']
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [integral_sub ((hi n hn).const_mul _) ((hfi n).const_mul _), integral_const_mul,
      integral_const_mul, mul_sub]

/-! ### Essentially bounded variables -/

variable (S) in
/-- Cochrane (2023), (19.9), p. 439: an essentially bounded variable, `|f| ≤ M` almost surely. -/
def BddAt (f : Ω → ℝ) : Prop := ∃ M, ∀ᵐ ω ∂S.μ, |f ω| ≤ M

/-- Cochrane (2023), (19.9), p. 439: products of essentially bounded variables are essentially
bounded. -/
theorem BddAt.mul {f g : Ω → ℝ} (hf : BddAt S f) (hg : BddAt S g) :
    BddAt S (fun ω => f ω * g ω) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M * N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- Cochrane (2023), (19.9), p. 439: sums of essentially bounded variables are essentially
bounded. -/
theorem BddAt.add {f g : Ω → ℝ} (hf : BddAt S f) (hg : BddAt S g) :
    BddAt S (fun ω => f ω + g ω) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Cochrane (2023), (19.9), p. 439: negatives of essentially bounded variables are essentially
bounded. -/
theorem BddAt.neg {f : Ω → ℝ} (hf : BddAt S f) : BddAt S (fun ω => -f ω) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, hM.mono fun ω h => by rwa [abs_neg]⟩

/-- Cochrane (2023), (19.9), p. 439: differences of essentially bounded variables are
essentially bounded. -/
theorem BddAt.sub {f g : Ω → ℝ} (hf : BddAt S f) (hg : BddAt S g) :
    BddAt S (fun ω => f ω - g ω) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Cochrane (2023), (19.9), p. 439: constants are essentially bounded. -/
theorem BddAt.const (a : ℝ) : BddAt S (fun _ => a) :=
  ⟨|a|, Eventually.of_forall fun _ => le_rfl⟩

/-- Cochrane (2023), (19.9), p. 439: a variable a.e. equal to an essentially bounded one is
essentially bounded. -/
theorem BddAt.congr {f g : Ω → ℝ} (hf : BddAt S f) (h : f =ᵐ[S.μ] g) : BddAt S g := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, by filter_upwards [hM, h] with ω h1 h2; rwa [← h2]⟩

/-- Cochrane (2023), (19.9), p. 439: a continuous function of two essentially bounded variables
is essentially bounded. -/
theorem BddAt.comp₂ {v : ℝ → ℝ → ℝ} (hv : Continuous fun p : ℝ × ℝ => v p.1 p.2) {f g : Ω → ℝ}
    (hf : BddAt S f) (hg : BddAt S g) : BddAt S (fun ω => v (f ω) (g ω)) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  obtain ⟨C, -, hC⟩ := exists_abs_le_of_continuous₂ hv (max M N)
  refine ⟨C, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  exact hC _ _ (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _))

/-- Cochrane (2023), (19.15), p. 441: the reciprocal of a nowhere-zero continuous function of
two essentially bounded variables is essentially bounded (e.g. `1/u_c(c_t, m_t)` for `u_c > 0`).
-/
theorem BddAt.inv_comp₂ {v : ℝ → ℝ → ℝ} (hv : Continuous fun p : ℝ × ℝ => v p.1 p.2)
    (hne : ∀ x y, v x y ≠ 0) {f g : Ω → ℝ} (hf : BddAt S f) (hg : BddAt S g) :
    BddAt S (fun ω => (v (f ω) (g ω))⁻¹) :=
  BddAt.comp₂ (v := fun x y => (v x y)⁻¹) (hv.inv₀ fun p => hne p.1 p.2) hf hg

/-- Cochrane (2023), (19.9), p. 439: forecasts of essentially bounded variables are essentially
bounded. -/
theorem BddAt.E {f : Ω → ℝ} (hf : BddAt S f) (t : ℕ) : BddAt S (S.E t f) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, S.abs_E_le hM t⟩

/-- Cochrane (2023), (19.9), p. 439: an a.e. measurable, essentially bounded variable is
integrable. -/
theorem BddAt.integrable {f : Ω → ℝ} (hf : BddAt S f) (hm : AEStronglyMeasurable f S.μ) :
    Integrable f S.μ := by
  obtain ⟨M, hM⟩ := hf
  exact Integrable.of_bound hm M (hM.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), (19.9), p. 439: an essentially bounded variable has a positive bound. -/
theorem BddAt.exists_pos {f : Ω → ℝ} (hf : BddAt S f) :
    ∃ M, 0 < M ∧ ∀ᵐ ω ∂S.μ, |f ω| ≤ M := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨max M 1, by positivity, hM.mono fun ω h => h.trans (le_max_left _ _)⟩

/-- Cochrane (2023), (19.9), p. 439: an essentially bounded variable times an integrable one is
integrable. -/
theorem BddAt.integrable_mul {f g : Ω → ℝ} (hf : BddAt S f) (hm : AEStronglyMeasurable f S.μ)
    (hg : Integrable g S.μ) : Integrable (fun ω => f ω * g ω) S.μ := by
  obtain ⟨M, hM⟩ := hf
  exact hg.bdd_mul hm (hM.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), (19.15), p. 441 (iterated expectations with pull-out; restated from the
Cochrane IntertemporalModel project): `∫ z X = ∫ z E_t X` for a bounded `𝓕_t`-measurable `z`
and an integrable `X`. -/
theorem integral_mul_E {t : ℕ} {z X : Ω → ℝ} (hz : StronglyMeasurable[S.𝓕 t] z) {K : ℝ}
    (hzK : ∀ᵐ ω ∂S.μ, |z ω| ≤ K) (hX : Integrable X S.μ) :
    ∫ ω, z ω * X ω ∂S.μ = ∫ ω, z ω * S.E t X ω ∂S.μ := by
  rw [← S.integral_E t (fun ω => z ω * X ω)]
  exact integral_congr_ae (S.E_pullOut hz hzK hX)


/-! ### Prices -/

/-- Cochrane (2023), p. 439 and (19.29), p. 449: the nominal state-price density
`pk_t = Λ_t/P_t`; a nominal payoff `a_t` is worth `E[pk_t a_t]` in date-0 units. -/
noncomputable def pk (Λ P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := Λ t ω / P t ω

variable (S) in
/-- Cochrane (2023), (19.15), p. 441 and (19.32), p. 450: the nominal one-period bond price
implied by the state prices, `Q_t = E_t[pk_{t+1}]/pk_t` (`Λ_tQ_t/P_t = E_t[Λ_{t+1}/P_{t+1}]`). -/
noncomputable def bondPrice (Λ P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  S.E t (pk Λ P (t + 1)) ω / pk Λ P t ω

variable (S) in
/-- Cochrane (2023), (19.12), p. 439 and (19.30), p. 449: the interest cost of money,
`ι_t = 1 − Q_t = i_t/(1 + i_t)`. -/
noncomputable def iota (Λ P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := 1 - bondPrice S Λ P t ω

variable (S) in
/-- Cochrane (2023), p. 439: the regularity of the state prices and the price level used
throughout: both adapted and positive, and at every date essentially bounded and essentially
bounded away from zero. -/
def PriceRegular (Λ P : ℕ → Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 Λ ∧ StronglyAdapted S.𝓕 P ∧ (∀ t ω, 0 < Λ t ω) ∧ (∀ t ω, 0 < P t ω) ∧
    ∀ t, BddAt S (Λ t) ∧ BddAt S (fun ω => (Λ t ω)⁻¹) ∧ BddAt S (P t) ∧
      BddAt S (fun ω => (P t ω)⁻¹)

namespace PriceRegular

variable {Λ P : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 439: the nominal state-price density is positive. -/
theorem pk_pos (hp : PriceRegular S Λ P) (t : ℕ) (ω : Ω) : 0 < pk Λ P t ω :=
  div_pos (hp.2.2.1 t ω) (hp.2.2.2.1 t ω)

/-- Cochrane (2023), p. 439: `pk_t P_t = Λ_t`. -/
theorem pk_mul_P (hp : PriceRegular S Λ P) (t : ℕ) (ω : Ω) : pk Λ P t ω * P t ω = Λ t ω := by
  have := (hp.2.2.2.1 t ω).ne'
  simp only [pk]
  field_simp

/-- Cochrane (2023), p. 439: the nominal state-price density is known at `t`. -/
theorem stronglyMeasurable_pk (hp : PriceRegular S Λ P) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (pk Λ P t) :=
  ((hp.1 t).measurable.div (hp.2.1 t).measurable).stronglyMeasurable

/-- Cochrane (2023), p. 439: the nominal state-price density is essentially bounded. -/
theorem pk_bdd (hp : PriceRegular S Λ P) (t : ℕ) : BddAt S (pk Λ P t) := by
  have := (hp.2.2.2.2 t).1.mul (hp.2.2.2.2 t).2.2.2
  change BddAt S (fun ω => Λ t ω / P t ω)
  simpa [div_eq_mul_inv] using this

/-- Cochrane (2023), p. 439: the reciprocal of the nominal state-price density is essentially
bounded. -/
theorem pk_inv_bdd (hp : PriceRegular S Λ P) (t : ℕ) : BddAt S (fun ω => (pk Λ P t ω)⁻¹) := by
  have := (hp.2.2.2.2 t).2.2.1.mul (hp.2.2.2.2 t).2.1
  simpa [pk, div_eq_mul_inv, mul_comm] using this

/-- Cochrane (2023), p. 439: the nominal state-price density is integrable. -/
theorem integrable_pk (hp : PriceRegular S Λ P) (t : ℕ) : Integrable (pk Λ P t) S.μ :=
  (hp.pk_bdd t).integrable ((hp.stronglyMeasurable_pk t).mono (S.𝓕.le t)).aestronglyMeasurable

/-- Cochrane (2023), (19.15), p. 441: the bond price is known at `t`. -/
theorem stronglyMeasurable_bondPrice (hp : PriceRegular S Λ P) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (bondPrice S Λ P t) :=
  ((S.stronglyMeasurable_E t _).measurable.div
    (hp.stronglyMeasurable_pk t).measurable).stronglyMeasurable

/-- Cochrane (2023), (19.15), p. 441: the bond price is essentially bounded. -/
theorem bondPrice_bdd (hp : PriceRegular S Λ P) (t : ℕ) : BddAt S (bondPrice S Λ P t) := by
  have := ((hp.pk_bdd (t + 1)).E t).mul (hp.pk_inv_bdd t)
  change BddAt S (fun ω => S.E t (pk Λ P (t + 1)) ω / pk Λ P t ω)
  simpa [div_eq_mul_inv] using this

/-- Cochrane (2023), (19.12), p. 439: the interest cost `ι_t` is known at `t`. -/
theorem stronglyMeasurable_iota (hp : PriceRegular S Λ P) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (iota S Λ P t) :=
  (stronglyMeasurable_const.sub (hp.stronglyMeasurable_bondPrice t))

/-- Cochrane (2023), (19.12), p. 439: the interest cost `ι_t` is essentially bounded. -/
theorem iota_bdd (hp : PriceRegular S Λ P) (t : ℕ) : BddAt S (iota S Λ P t) :=
  (BddAt.const 1).sub (hp.bondPrice_bdd t)

/-- Cochrane (2023), (19.15), p. 441: `E_t[pk_{t+1}] = Q_t pk_t`. -/
theorem E_pk_eq (hp : PriceRegular S Λ P) (t : ℕ) (ω : Ω) :
    S.E t (pk Λ P (t + 1)) ω = bondPrice S Λ P t ω * pk Λ P t ω := by
  have := (hp.pk_pos t ω).ne'
  simp only [bondPrice]
  field_simp

/-- Cochrane (2023), (19.15), p. 441: the bond price is positive almost surely, `Q_t > 0`
(`i_t > −1`). -/
theorem bondPrice_pos (hp : PriceRegular S Λ P) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < bondPrice S Λ P t ω := by
  obtain ⟨K, hK0, hK⟩ := (hp.pk_inv_bdd (t + 1)).exists_pos
  have hlow : (fun _ => K⁻¹) ≤ᵐ[S.μ] pk Λ P (t + 1) := by
    filter_upwards [hK] with ω h
    have hp0 := hp.pk_pos (t + 1) ω
    rw [abs_of_pos (inv_pos.2 hp0)] at h
    exact (inv_le_comm₀ hp0 hK0).1 h
  filter_upwards [S.E_mono (integrable_const _) (hp.integrable_pk (t + 1)) hlow t] with ω h
  rw [S.E_const] at h
  exact div_pos (lt_of_lt_of_le (inv_pos.2 hK0) h) (hp.pk_pos t ω)

end PriceRegular

/-! ### The household problem -/

/-- Cochrane (2023), (19.10), p. 439 and (19.27), p. 449: the money brought into date `t`,
`M_{t−1}`: `N₀` at date `0` and `M_t = P_tm_t` thereafter (`m` is real balances held
overnight). -/
def moneyIn (N0 : Ω → ℝ) (P m : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => N0
  | t + 1 => fun ω => P t ω * m t ω

variable (S) in
/-- Cochrane (2023), p. 439 ("complete contingent claim markets with state price `Λ_t`"): the
date-`t` cost `E_t[pk_{t+1}a_{t+1}]/pk_t` of the claims paying the nominal amount `a_{t+1}` at
`t + 1`. With `a_{t+1} = B_t` known at `t` it is `Q_tB_t`. -/
noncomputable def claimCost (Λ P a : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  S.E t (fun ω => pk Λ P (t + 1) ω * a (t + 1) ω) ω / pk Λ P t ω

variable (S) in
/-- Cochrane (2023), eq. (19.10), p. 439 and eq. (19.27), p. 449, with complete markets: the
period budget constraint
`a_t + M_{t−1} + P_t(y_t − c_t) = (cost of a_{t+1}) + M_t + P_ts_t`
holds almost surely at every date. -/
def Flow (Λ P y s : ℕ → Ω → ℝ) (N0 : Ω → ℝ) (c m a : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, a t ω + moneyIn N0 P m t ω + P t ω * (y t ω - c t ω) =
    claimCost S Λ P a t ω + P t ω * m t ω + P t ω * s t ω

variable (S) in
/-- Cochrane (2023), (19.11)–(19.12), p. 439 and (19.28), p. 449: the date-0 value of the
household's nominal wealth at the start of date `t`, `E[pk_t(a_t + M_{t−1})]`. -/
noncomputable def wealthPV (Λ P : ℕ → Ω → ℝ) (N0 : Ω → ℝ) (m a : ℕ → Ω → ℝ) (t : ℕ) : ℝ :=
  ∫ ω, pk Λ P t ω * (a t ω + moneyIn N0 P m t ω) ∂S.μ

variable (S) in
/-- Cochrane (2023), (19.10)–(19.12), p. 439 and (19.26)–(19.28), p. 449: a feasible plan from
initial claims `a₀` and money `N₀`: consumption, real balances and claims are adapted (the claims
`a_{t+1}` maturing at `t + 1` may depend on date-`t + 1` news), the flow constraint holds almost
surely, the date-0 values `E[pk_ta_t]`, `E[pk_tM_{t−1}]`, `E[Λ_tm_t]`, `E[Λ_tc_t]` exist, and the
no-Ponzi condition `liminf_T E[pk_T(a_T + M_{T−1})] ≥ 0` holds (the household cannot roll over
debt forever; the book's lower bound `M_{t−1} + B_{t−1} > −B`). -/
def Feasible (Λ P y s : ℕ → Ω → ℝ) (N0 a0 : Ω → ℝ) (c m a : ℕ → Ω → ℝ) : Prop :=
  a 0 = a0 ∧ StronglyAdapted S.𝓕 c ∧ StronglyAdapted S.𝓕 m ∧ StronglyAdapted S.𝓕 a ∧
    Flow S Λ P y s N0 c m a ∧
    (∀ t, Integrable (fun ω => pk Λ P t ω * a t ω) S.μ) ∧
    (∀ t, Integrable (fun ω => pk Λ P t ω * moneyIn N0 P m t ω) S.μ) ∧
    (∀ t, Integrable (fun ω => Λ t ω * m t ω) S.μ) ∧
    (∀ t, Integrable (fun ω => Λ t ω * c t ω) S.μ) ∧
    ∀ δ, 0 < δ → ∀ᶠ T in atTop, -δ ≤ wealthPV S Λ P N0 m a T

variable (S) in
/-- Cochrane (2023), (19.9), p. 439 and §19.5.1, p. 449: an optimal plan maximises expected
discounted utility `E ∑ βᵗu(c_t, m_t)` over feasible plans satisfying the further constraint
`Con` on consumption and real balances (none in the money-in-utility model; the cash-in-advance
and no-printing constraints (19.24)–(19.26) in the cash-in-advance model). -/
def Optimal (β : ℝ) (u : ℝ → ℝ → ℝ) (Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    (Λ P y s : ℕ → Ω → ℝ) (N0 a0 : Ω → ℝ) (c m a : ℕ → Ω → ℝ) : Prop :=
  Feasible S Λ P y s N0 a0 c m a ∧ Con c m ∧ UAdmissible S β (fun n ω => u (c n ω) (m n ω)) ∧
    ∀ c' m' a', Feasible S Λ P y s N0 a0 c' m' a' → Con c' m' →
      UAdmissible S β (fun n ω => u (c' n ω) (m' n ω)) →
        expU S β (fun n ω => u (c' n ω) (m' n ω)) ≤ expU S β (fun n ω => u (c n ω) (m n ω))

/-! ### Budget-neutral deviations -/

/-- Cochrane (2023), footnote 1, p. 440 (perturbing a plan at two dates): `x` changed by `εd₁` at
date `t` and by `εd₂` at date `t + 1`. -/
noncomputable def bump (x : ℕ → Ω → ℝ) (t : ℕ) (d₁ d₂ : Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => x n ω + ε * (if n = t then d₁ ω else if n = t + 1 then d₂ ω else 0)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), footnote 1, p. 440: a bump leaves the other dates unchanged. -/
theorem bump_of_ne {x : ℕ → Ω → ℝ} {t n : ℕ} {d₁ d₂ : Ω → ℝ} {ε : ℝ} (h1 : n ≠ t)
    (h2 : n ≠ t + 1) : bump x t d₁ d₂ ε n = x n := by
  funext ω
  simp [bump, h1, h2]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), footnote 1, p. 440: the bump at its first date. -/
theorem bump_self {x : ℕ → Ω → ℝ} {t : ℕ} {d₁ d₂ : Ω → ℝ} {ε : ℝ} :
    bump x t d₁ d₂ ε t = fun ω => x t ω + ε * d₁ ω := by
  funext ω
  simp [bump]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), footnote 1, p. 440: the bump at its second date. -/
theorem bump_succ {x : ℕ → Ω → ℝ} {t : ℕ} {d₁ d₂ : Ω → ℝ} {ε : ℝ} :
    bump x t d₁ d₂ ε (t + 1) = fun ω => x (t + 1) ω + ε * d₂ ω := by
  funext ω
  simp [bump]

/-- Cochrane (2023), footnote 1, p. 440: a bump by variables known at the bumped dates keeps a
plan adapted. -/
theorem bump_adapted {x : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x) {t : ℕ} {d₁ d₂ : Ω → ℝ}
    (hd₁ : StronglyMeasurable[S.𝓕 t] d₁) (hd₂ : StronglyMeasurable[S.𝓕 (t + 1)] d₂) (ε : ℝ) :
    StronglyAdapted S.𝓕 (bump x t d₁ d₂ ε) := by
  intro n
  by_cases h1 : n = t
  · subst h1
    rw [bump_self]
    exact (hx n).add (hd₁.const_mul ε)
  · by_cases h2 : n = t + 1
    · subst h2
      rw [bump_succ]
      exact (hx (t + 1)).add (hd₂.const_mul ε)
    · rw [bump_of_ne h1 h2]
      exact hx n

/-- Cochrane (2023), footnote 1, p. 440: a bump keeps weighted integrability, if the weighted
changes are integrable. -/
theorem bump_integrable {w x : ℕ → Ω → ℝ} (hx : ∀ n, Integrable (fun ω => w n ω * x n ω) S.μ)
    {t : ℕ} {d₁ d₂ : Ω → ℝ} (hd₁ : Integrable (fun ω => w t ω * d₁ ω) S.μ)
    (hd₂ : Integrable (fun ω => w (t + 1) ω * d₂ ω) S.μ) (ε : ℝ) (n : ℕ) :
    Integrable (fun ω => w n ω * bump x t d₁ d₂ ε n ω) S.μ := by
  by_cases h1 : n = t
  · subst h1
    rw [bump_self]
    refine ((hx n).add (hd₁.const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  · by_cases h2 : n = t + 1
    · subst h2
      rw [bump_succ]
      refine ((hx (t + 1)).add (hd₂.const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply]
      ring
    · rw [bump_of_ne h1 h2]
      exact hx n

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), footnote 1, p. 440: money brought into a date unaffected by a bump of real
balances. -/
theorem moneyIn_bump_of_ne {N0 : Ω → ℝ} {P m : ℕ → Ω → ℝ} {t n : ℕ} {d₁ d₂ : Ω → ℝ} {ε : ℝ}
    (h1 : n ≠ t + 1) (h2 : n ≠ t + 2) : moneyIn N0 P (bump m t d₁ d₂ ε) n = moneyIn N0 P m n := by
  cases n with
  | zero => rfl
  | succ k =>
    funext ω
    simp only [moneyIn]
    rw [bump_of_ne (by omega) (by omega)]

variable (S) in
/-- Cochrane (2023), footnote 1, p. 440: the change in the claims maturing at `t + 1` that
finances the deviation `(ζ₁; z₂, ζ₂)`: `P_{t+1}(z₂ + ι_{t+1}ζ₂) − P_tζ₁` (the date-`t + 1`
spending on the deviation, net of the money `P_tζ₁` carried into `t + 1`). -/
noncomputable def claimDev (Λ P : ℕ → Ω → ℝ) (t : ℕ) (ζ₁ z₂ ζ₂ : Ω → ℝ) (ω : Ω) : ℝ :=
  P (t + 1) ω * (z₂ ω + iota S Λ P (t + 1) ω * ζ₂ ω) - P t ω * ζ₁ ω

variable (S) in
/-- Cochrane (2023), footnote 1, p. 440: the claims after the deviation: `a_{t+1}` changed by
`ε·claimDev` and `a_{t+2}` by `−εP_{t+1}ζ₂` (the extra money carried into `t + 2`). -/
noncomputable def pertA (Λ P a : ℕ → Ω → ℝ) (t : ℕ) (ζ₁ z₂ ζ₂ : Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ :=
  bump a (t + 1) (claimDev S Λ P t ζ₁ z₂ ζ₂) (fun ω => -(P (t + 1) ω * ζ₂ ω)) ε


/-- Cochrane (2023), (19.10), p. 439 and footnote 1, p. 440: **budget-neutral deviations are
feasible.** Let `z₁, ζ₁` be bounded and known at `t`, `z₂, ζ₂` bounded and known at `t + 1`, with
`Λ_t(z₁ + ι_tζ₁) + E_t[Λ_{t+1}(z₂ + ι_{t+1}ζ₂)] = 0` almost surely (consumption `z` and real
balances `ζ` cost `z + ιζ` in date-`t` goods, valued at the state prices). Then consuming `εz₁`,
`εz₂` and holding `εζ₁`, `εζ₂` more at `t`, `t + 1`, financed by the claims `pertA`, keeps every
flow constraint almost surely, adaptedness, integrability and the no-Ponzi condition. -/
theorem pert_feasible {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hf : Feasible S Λ P y s N0 a0 c m a) {t : ℕ}
    {z₁ ζ₁ z₂ ζ₂ : Ω → ℝ} (hz₁ : StronglyMeasurable[S.𝓕 t] z₁)
    (hζ₁ : StronglyMeasurable[S.𝓕 t] ζ₁) (hz₂ : StronglyMeasurable[S.𝓕 (t + 1)] z₂)
    (hζ₂ : StronglyMeasurable[S.𝓕 (t + 1)] ζ₂) (hbz₁ : BddAt S z₁) (hbζ₁ : BddAt S ζ₁)
    (hbz₂ : BddAt S z₂) (hbζ₂ : BddAt S ζ₂)
    (hfin : ∀ᵐ ω ∂S.μ, Λ t ω * (z₁ ω + iota S Λ P t ω * ζ₁ ω) +
      S.E t (fun ω => Λ (t + 1) ω * (z₂ ω + iota S Λ P (t + 1) ω * ζ₂ ω)) ω = 0) (ε : ℝ) :
    Feasible S Λ P y s N0 a0 (bump c t z₁ z₂ ε) (bump m t ζ₁ ζ₂ ε)
      (pertA S Λ P a t ζ₁ z₂ ζ₂ ε) := by
  obtain ⟨ha0, hca, hma, haa, hflow, hia, hiN, him, hic, hnp⟩ := hf
  have hle : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
  have ae : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → AEStronglyMeasurable f S.μ :=
    fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hPb := fun k => (hp.2.2.2.2 k).2.2.1
  have hΛb := fun k => (hp.2.2.2.2 k).1
  -- the financing claims
  have hd₁m : StronglyMeasurable[S.𝓕 (t + 1)] (claimDev S Λ P t ζ₁ z₂ ζ₂) :=
    ((hp.2.1 (t + 1)).mul (hz₂.add ((hp.stronglyMeasurable_iota (t + 1)).mul hζ₂))).sub
      (((hp.2.1 t).mul hζ₁).mono hle)
  have hd₁b : BddAt S (claimDev S Λ P t ζ₁ z₂ ζ₂) :=
    ((hPb (t + 1)).mul (hbz₂.add ((hp.iota_bdd (t + 1)).mul hbζ₂))).sub ((hPb t).mul hbζ₁)
  have hd₂m : StronglyMeasurable[S.𝓕 (t + 1 + 1)] (fun ω => -(P (t + 1) ω * ζ₂ ω)) :=
    (((hp.2.1 (t + 1)).mul hζ₂).neg).mono (S.𝓕.mono (Nat.le_succ _))
  have hd₂b : BddAt S (fun ω => -(P (t + 1) ω * ζ₂ ω)) := ((hPb (t + 1)).mul hbζ₂).neg
  -- integrability of the changes
  have hipk : ∀ (k : ℕ) {f : Ω → ℝ}, AEStronglyMeasurable f S.μ → BddAt S f →
      Integrable (fun ω => pk Λ P k ω * f ω) S.μ := fun k f hm hb =>
    ((hp.pk_bdd k).mul hb).integrable ((ae (hp.stronglyMeasurable_pk k)).mul hm)
  have hiΛ : ∀ (k : ℕ) {f : Ω → ℝ}, AEStronglyMeasurable f S.μ → BddAt S f →
      Integrable (fun ω => Λ k ω * f ω) S.μ := fun k f hm hb =>
    ((hΛb k).mul hb).integrable ((ae (hp.1 k)).mul hm)
  refine ⟨?_, bump_adapted hca hz₁ hz₂ ε, bump_adapted hma hζ₁ hζ₂ ε,
    bump_adapted haa hd₁m hd₂m ε, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change bump a (t + 1) _ _ ε 0 = a0
    rw [bump_of_ne (by omega) (by omega)]
    exact ha0
  · intro n
    by_cases h1 : n = t
    · subst h1
      have e1 : pertA S Λ P a n ζ₁ z₂ ζ₂ ε n = a n := bump_of_ne (by omega) (by omega)
      have e3 : bump c n z₁ z₂ ε n = fun ω => c n ω + ε * z₁ ω := bump_self
      have e4 : bump m n ζ₁ ζ₂ ε n = fun ω => m n ω + ε * ζ₁ ω := bump_self
      have e5 : moneyIn N0 P (bump m n ζ₁ ζ₂ ε) n = moneyIn N0 P m n :=
        moneyIn_bump_of_ne (by omega) (by omega)
      have hA : ∀ᵐ ω ∂S.μ,
          S.E n (fun ω => pk Λ P (n + 1) ω * pertA S Λ P a n ζ₁ z₂ ζ₂ ε (n + 1) ω) ω =
            S.E n (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) ω +
              ε * (S.E n (fun ω => Λ (n + 1) ω * (z₂ ω + iota S Λ P (n + 1) ω * ζ₂ ω)) ω -
                P n ω * ζ₁ ω * S.E n (pk Λ P (n + 1)) ω) := by
        have e2 : pertA S Λ P a n ζ₁ z₂ ζ₂ ε (n + 1) =
            fun ω => a (n + 1) ω + ε * claimDev S Λ P n ζ₁ z₂ ζ₂ ω := bump_self
        have f1 : (fun ω => pk Λ P (n + 1) ω * pertA S Λ P a n ζ₁ z₂ ζ₂ ε (n + 1) ω) =
            (fun ω => pk Λ P (n + 1) ω * a (n + 1) ω) +
              ε • ((fun ω => Λ (n + 1) ω * (z₂ ω + iota S Λ P (n + 1) ω * ζ₂ ω)) -
                (fun ω => P n ω * ζ₁ ω) * pk Λ P (n + 1)) := by
          funext ω
          rw [e2]
          simp only [claimDev, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply,
            smul_eq_mul]
          rw [← hp.pk_mul_P (n + 1) ω]
          ring
        have hX : Integrable (fun ω => Λ (n + 1) ω * (z₂ ω + iota S Λ P (n + 1) ω * ζ₂ ω)) S.μ :=
          hiΛ (n + 1) ((ae hz₂).add ((ae (hp.stronglyMeasurable_iota (n + 1))).mul (ae hζ₂)))
            (hbz₂.add ((hp.iota_bdd (n + 1)).mul hbζ₂))
        have hY : Integrable ((fun ω => P n ω * ζ₁ ω) * pk Λ P (n + 1)) S.μ := by
          have := hipk (n + 1) ((ae (hp.2.1 n)).mul (ae hζ₁)) ((hPb n).mul hbζ₁)
          refine this.congr (Eventually.of_forall fun ω => ?_)
          simp only [Pi.mul_apply]
          ring
        obtain ⟨K, hK⟩ := (hPb n).mul hbζ₁
        rw [f1]
        filter_upwards [S.E_add (hia (n + 1)) ((hX.sub hY).smul ε) n,
          S.E_smul ε ((fun ω => Λ (n + 1) ω * (z₂ ω + iota S Λ P (n + 1) ω * ζ₂ ω)) -
            (fun ω => P n ω * ζ₁ ω) * pk Λ P (n + 1)) n, S.E_sub hX hY n,
          S.E_pullOut (f := fun ω => P n ω * ζ₁ ω) ((hp.2.1 n).mul hζ₁) hK
            (hp.integrable_pk (n + 1))] with ω h1 h2 h3 h4
        rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, smul_eq_mul,
          Pi.mul_apply]
      filter_upwards [hflow n, hA, hfin] with ω hfl hAω hF
      simp only [claimCost, e1, e3, e4, e5] at hfl ⊢
      rw [hAω]
      have hk := (hp.pk_pos n ω).ne'
      have hΛ := (hp.pk_mul_P n ω).symm
      have hEp := hp.E_pk_eq n ω
      rw [show iota S Λ P n ω = 1 - bondPrice S Λ P n ω from rfl] at hF
      rw [hEp]
      rw [hΛ] at hF
      field_simp at hfl ⊢
      linear_combination hfl - ε * hF
    · by_cases h2 : n = t + 1
      · subst h2
        have e1 : pertA S Λ P a t ζ₁ z₂ ζ₂ ε (t + 1) =
            fun ω => a (t + 1) ω + ε * claimDev S Λ P t ζ₁ z₂ ζ₂ ω := bump_self
        have e3 : bump c t z₁ z₂ ε (t + 1) = fun ω => c (t + 1) ω + ε * z₂ ω := bump_succ
        have e4 : bump m t ζ₁ ζ₂ ε (t + 1) = fun ω => m (t + 1) ω + ε * ζ₂ ω := bump_succ
        have e4' : bump m t ζ₁ ζ₂ ε t = fun ω => m t ω + ε * ζ₁ ω := bump_self
        have e5 : moneyIn N0 P (bump m t ζ₁ ζ₂ ε) (t + 1) =
            fun ω => P t ω * (m t ω + ε * ζ₁ ω) := by
          funext ω
          simp only [moneyIn, e4']
        have hA : ∀ᵐ ω ∂S.μ,
            S.E (t + 1) (fun ω => pk Λ P (t + 1 + 1) ω *
              pertA S Λ P a t ζ₁ z₂ ζ₂ ε (t + 1 + 1) ω) ω =
              S.E (t + 1) (fun ω => pk Λ P (t + 1 + 1) ω * a (t + 1 + 1) ω) ω -
                ε * (P (t + 1) ω * ζ₂ ω * S.E (t + 1) (pk Λ P (t + 1 + 1)) ω) := by
          have e2 : pertA S Λ P a t ζ₁ z₂ ζ₂ ε (t + 1 + 1) =
              fun ω => a (t + 1 + 1) ω + ε * -(P (t + 1) ω * ζ₂ ω) := bump_succ
          have f1 : (fun ω => pk Λ P (t + 1 + 1) ω * pertA S Λ P a t ζ₁ z₂ ζ₂ ε (t + 1 + 1) ω) =
              (fun ω => pk Λ P (t + 1 + 1) ω * a (t + 1 + 1) ω) -
                ε • ((fun ω => P (t + 1) ω * ζ₂ ω) * pk Λ P (t + 1 + 1)) := by
            funext ω
            rw [e2]
            simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
            ring
          have hY : Integrable ((fun ω => P (t + 1) ω * ζ₂ ω) * pk Λ P (t + 1 + 1)) S.μ := by
            have := hipk (t + 1 + 1) ((ae (hp.2.1 (t + 1))).mul (ae hζ₂)) ((hPb (t + 1)).mul hbζ₂)
            refine this.congr (Eventually.of_forall fun ω => ?_)
            simp only [Pi.mul_apply]
            ring
          obtain ⟨K, hK⟩ := (hPb (t + 1)).mul hbζ₂
          rw [f1]
          filter_upwards [S.E_sub (hia (t + 1 + 1)) (hY.smul ε) (t + 1),
            S.E_smul ε ((fun ω => P (t + 1) ω * ζ₂ ω) * pk Λ P (t + 1 + 1)) (t + 1),
            S.E_pullOut (f := fun ω => P (t + 1) ω * ζ₂ ω) ((hp.2.1 (t + 1)).mul hζ₂) hK
              (hp.integrable_pk (t + 1 + 1))]
            with ω h1 h2 h3
          rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul, Pi.mul_apply]
        filter_upwards [hflow (t + 1), hA] with ω hfl hAω
        simp only [claimCost, e1, e3, e4, e5] at hfl ⊢
        rw [hAω]
        simp only [claimDev, iota, bondPrice]
        simp only [moneyIn] at hfl
        have hk := (hp.pk_pos (t + 1) ω).ne'
        field_simp at hfl ⊢
        linear_combination hfl
      · by_cases h3 : n = t + 1 + 1
        · subst h3
          have e1 : pertA S Λ P a t ζ₁ z₂ ζ₂ ε (t + 1 + 1) =
              fun ω => a (t + 1 + 1) ω + ε * -(P (t + 1) ω * ζ₂ ω) := bump_succ
          have e2 : pertA S Λ P a t ζ₁ z₂ ζ₂ ε (t + 1 + 1 + 1) = a (t + 1 + 1 + 1) :=
            bump_of_ne (by omega) (by omega)
          have e3 : bump c t z₁ z₂ ε (t + 1 + 1) = c (t + 1 + 1) :=
            bump_of_ne (by omega) (by omega)
          have e4 : bump m t ζ₁ ζ₂ ε (t + 1 + 1) = m (t + 1 + 1) :=
            bump_of_ne (by omega) (by omega)
          have e4' : bump m t ζ₁ ζ₂ ε (t + 1) = fun ω => m (t + 1) ω + ε * ζ₂ ω := bump_succ
          have e5 : moneyIn N0 P (bump m t ζ₁ ζ₂ ε) (t + 1 + 1) =
              fun ω => P (t + 1) ω * (m (t + 1) ω + ε * ζ₂ ω) := by
            funext ω
            simp only [moneyIn, e4']
          filter_upwards [hflow (t + 1 + 1)] with ω hfl
          simp only [claimCost, e1, e2, e3, e4, e5] at hfl ⊢
          simp only [moneyIn] at hfl
          linear_combination hfl
        · have e1 : pertA S Λ P a t ζ₁ z₂ ζ₂ ε n = a n := bump_of_ne h2 h3
          have e2 : pertA S Λ P a t ζ₁ z₂ ζ₂ ε (n + 1) = a (n + 1) :=
            bump_of_ne (by omega) (by omega)
          have e3 : bump c t z₁ z₂ ε n = c n := bump_of_ne h1 h2
          have e4 : bump m t ζ₁ ζ₂ ε n = m n := bump_of_ne h1 h2
          have e5 : moneyIn N0 P (bump m t ζ₁ ζ₂ ε) n = moneyIn N0 P m n :=
            moneyIn_bump_of_ne h2 h3
          filter_upwards [hflow n] with ω hfl
          simp only [claimCost, e1, e2, e3, e4, e5] at hfl ⊢
          exact hfl
  · exact bump_integrable hia (hipk (t + 1) (ae hd₁m) hd₁b) (hipk (t + 1 + 1) (ae hd₂m) hd₂b) ε
  · intro n
    cases n with
    | zero => exact hiN 0
    | succ k =>
      have hx : ∀ j, Integrable (fun ω => (pk Λ P (j + 1) ω * P j ω) * m j ω) S.μ := fun j =>
        (hiN (j + 1)).congr (Eventually.of_forall fun ω => by simp only [moneyIn]; ring)
      have hw : ∀ (j : ℕ) {f : Ω → ℝ}, AEStronglyMeasurable f S.μ → BddAt S f →
          Integrable (fun ω => (pk Λ P (j + 1) ω * P j ω) * f ω) S.μ := fun j f hm hb =>
        (((hp.pk_bdd (j + 1)).mul (hPb j)).mul hb).integrable
          (((ae (hp.stronglyMeasurable_pk (j + 1))).mul (ae (hp.2.1 j))).mul hm)
      have := bump_integrable (w := fun j ω => pk Λ P (j + 1) ω * P j ω) hx
        (hw t (ae hζ₁) hbζ₁) (hw (t + 1) (ae hζ₂) hbζ₂) ε k
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only [moneyIn]
      ring
  · exact bump_integrable him (hiΛ t (ae hζ₁) hbζ₁) (hiΛ (t + 1) (ae hζ₂) hbζ₂) ε
  · exact bump_integrable hic (hiΛ t (ae hz₁) hbz₁) (hiΛ (t + 1) (ae hz₂) hbz₂) ε
  · intro δ hδ
    filter_upwards [hnp δ hδ, eventually_ge_atTop (t + 3)] with T h1 hT
    have e1 : pertA S Λ P a t ζ₁ z₂ ζ₂ ε T = a T := bump_of_ne (by omega) (by omega)
    have e2 : moneyIn N0 P (bump m t ζ₁ ζ₂ ε) T = moneyIn N0 P m T :=
      moneyIn_bump_of_ne (by omega) (by omega)
    simp only [wealthPV, e1, e2] at h1 ⊢
    exact h1


/-! ### The first-order condition along budget-neutral deviations -/

/-- Cochrane (2023), (19.13)–(19.14), p. 440 and footnote 1 ("consider each item as a function of
state"), on a probability space: **the first-order condition of the household problem.** At an
optimal plan, with smooth utility, regular prices, consumption and real balances essentially
bounded at `t` and `t + 1`, and a budget-neutral deviation `(z₁, ζ₁; z₂, ζ₂)` (bounded, known at
`t` and `t + 1`, `Λ_t(z₁ + ι_tζ₁) + E_t[Λ_{t+1}(z₂ + ι_{t+1}ζ₂)] = 0`) that respects the extra
constraint `Con` for small steps,
`βᵗE[u_c(t)z₁ + u_m(t)ζ₁] + β^{t+1}E[u_c(t+1)z₂ + u_m(t+1)ζ₂] = 0`. -/
theorem pair_foc {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hopt : Optimal S β u Con Λ P y s N0 a0 c m a)
    (hp : PriceRegular S Λ P) {t : ℕ} (hct : BddAt S (c t)) (hct1 : BddAt S (c (t + 1)))
    (hmt : BddAt S (m t)) (hmt1 : BddAt S (m (t + 1))) {z₁ ζ₁ z₂ ζ₂ : Ω → ℝ}
    (hz₁ : StronglyMeasurable[S.𝓕 t] z₁) (hζ₁ : StronglyMeasurable[S.𝓕 t] ζ₁)
    (hz₂ : StronglyMeasurable[S.𝓕 (t + 1)] z₂) (hζ₂ : StronglyMeasurable[S.𝓕 (t + 1)] ζ₂)
    (hbz₁ : BddAt S z₁) (hbζ₁ : BddAt S ζ₁) (hbz₂ : BddAt S z₂) (hbζ₂ : BddAt S ζ₂)
    (hfin : ∀ᵐ ω ∂S.μ, Λ t ω * (z₁ ω + iota S Λ P t ω * ζ₁ ω) +
      S.E t (fun ω => Λ (t + 1) ω * (z₂ ω + iota S Λ P (t + 1) ω * ζ₂ ω)) ω = 0)
    (hcon : ∃ η, 0 < η ∧ ∀ ε, |ε| < η → Con (bump c t z₁ z₂ ε) (bump m t ζ₁ ζ₂ ε)) :
    β ^ t * ∫ ω, (uc (c t ω) (m t ω) * z₁ ω + um (c t ω) (m t ω) * ζ₁ ω) ∂S.μ +
      β ^ (t + 1) * ∫ ω, (uc (c (t + 1) ω) (m (t + 1) ω) * z₂ ω +
        um (c (t + 1) ω) (m (t + 1) ω) * ζ₂ ω) ∂S.μ = 0 := by
  obtain ⟨hfeas, -, hadm, hmax⟩ := hopt
  have ae : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → AEStronglyMeasurable f S.μ :=
    fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  -- integrability of perturbed period utilities
  have hint : ∀ {f g h k : Ω → ℝ}, AEStronglyMeasurable f S.μ → AEStronglyMeasurable g S.μ →
      AEStronglyMeasurable h S.μ → AEStronglyMeasurable k S.μ → BddAt S f → BddAt S g →
      BddAt S h → BddAt S k → ∀ ε : ℝ,
        Integrable (fun ω => u (f ω + ε * g ω) (h ω + ε * k ω)) S.μ := by
    intro f g h k hf hg hh hk hbf hbg hbh hbk ε
    exact (BddAt.comp₂ hu.continuous (hbf.add ((BddAt.const ε).mul hbg))
      (hbh.add ((BddAt.const ε).mul hbk))).integrable
      (hu.continuous.comp_aestronglyMeasurable ((hf.add (hg.const_mul ε)).prodMk
        (hh.add (hk.const_mul ε))))
  have hR : ∀ {f g h k : Ω → ℝ}, BddAt S f → BddAt S g → BddAt S h → BddAt S k →
      ∃ R, (∀ᵐ ω ∂S.μ, |f ω| ≤ R) ∧ (∀ᵐ ω ∂S.μ, |g ω| ≤ R) ∧ (∀ᵐ ω ∂S.μ, |h ω| ≤ R) ∧
        ∀ᵐ ω ∂S.μ, |k ω| ≤ R := by
    intro f g h k ⟨M1, h1⟩ ⟨M2, h2⟩ ⟨M3, h3⟩ ⟨M4, h4⟩
    refine ⟨max (max M1 M2) (max M3 M4), ?_, ?_, ?_, ?_⟩
    · exact h1.mono fun ω h => h.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h2.mono fun ω h => h.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact h3.mono fun ω h => h.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact h4.mono fun ω h => h.trans ((le_max_right _ _).trans (le_max_right _ _))
  have hc0 := ae (hca t)
  have hc1 := ae (hca (t + 1))
  have hm0 := ae (hma t)
  have hm1 := ae (hma (t + 1))
  set φ : ℝ → ℝ := fun ε =>
    β ^ t * (∫ ω, u (c t ω + ε * z₁ ω) (m t ω + ε * ζ₁ ω) ∂S.μ -
      ∫ ω, u (c t ω) (m t ω) ∂S.μ) +
    β ^ (t + 1) * (∫ ω, u (c (t + 1) ω + ε * z₂ ω) (m (t + 1) ω + ε * ζ₂ ω) ∂S.μ -
      ∫ ω, u (c (t + 1) ω) (m (t + 1) ω) ∂S.μ) with hφ
  have hval : ∀ ε, UAdmissible S β (fun n ω => u (bump c t z₁ z₂ ε n ω) (bump m t ζ₁ ζ₂ ε n ω)) ∧
      expU S β (fun n ω => u (bump c t z₁ z₂ ε n ω) (bump m t ζ₁ ζ₂ ε n ω)) =
        expU S β (fun n ω => u (c n ω) (m n ω)) + φ ε := by
    intro ε
    have h := hadm.modify hβ {t, t + 1}
      (f' := fun n ω => u (bump c t z₁ z₂ ε n ω) (bump m t ζ₁ ζ₂ ε n ω))
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        rw [bump_of_ne hn.1 hn.2, bump_of_ne hn.1 hn.2])
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · simp only [bump_self]
          exact hint hc0 (ae hz₁) hm0 (ae hζ₁) hct hbz₁ hmt hbζ₁ ε
        · simp only [bump_succ]
          exact hint hc1 (ae hz₂) hm1 (ae hζ₂) hct1 hbz₂ hmt1 hbζ₂ ε)
    refine ⟨h.1, h.2.trans ?_⟩
    rw [Finset.sum_pair (show t ≠ t + 1 by omega)]
    simp only [bump_self, bump_succ, hφ]
  obtain ⟨R0, hR1, hR2, hR3, hR4⟩ := hR hct hbz₁ hmt hbζ₁
  obtain ⟨R1, hS1, hS2, hS3, hS4⟩ := hR hct1 hbz₂ hmt1 hbζ₂
  have hd0 := hasDerivAt_integral_comp₂ hu hc0 (ae hz₁) hm0 (ae hζ₁) hR1 hR2 hR3 hR4
  have hd1 := hasDerivAt_integral_comp₂ hu hc1 (ae hz₂) hm1 (ae hζ₂) hS1 hS2 hS3 hS4
  have hD : HasDerivAt φ (β ^ t * ∫ ω, (uc (c t ω) (m t ω) * z₁ ω +
      um (c t ω) (m t ω) * ζ₁ ω) ∂S.μ + β ^ (t + 1) * ∫ ω, (uc (c (t + 1) ω) (m (t + 1) ω) *
        z₂ ω + um (c (t + 1) ω) (m (t + 1) ω) * ζ₂ ω) ∂S.μ) 0 :=
    ((hd0.sub_const _).const_mul (β ^ t)).add ((hd1.sub_const _).const_mul (β ^ (t + 1)))
  obtain ⟨η, hη, hcη⟩ := hcon
  have hlm : IsLocalMax φ 0 := by
    have h0 : φ 0 = 0 := by simp [hφ]
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hη) fun ε hε => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    have h1 := hmax _ _ _ (pert_feasible hp hfeas hz₁ hζ₁ hz₂ hζ₂ hbz₁ hbζ₁ hbz₂ hbζ₂ hfin ε)
      (hcη ε hε) (hval ε).1
    rw [(hval ε).2] at h1
    rw [h0]
    linarith
  exact hlm.hasDerivAt_eq_zero hD


/-! ### The present-value budget and sufficiency -/

variable (S) in
/-- Cochrane (2023), (19.12), p. 439 and (19.30), p. 449: the date-`t` term of the present-value
budget constraint in date-0 units, `Λ_t(c_t + ι_tm_t + s_t − y_t)` (consumption, the interest
cost of real balances, and taxes, net of the endowment). -/
noncomputable def outlay (Λ P y s c m : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Λ t ω * (c t ω + iota S Λ P t ω * m t ω + s t ω - y t ω)

/-- Cochrane (2023), (19.12), p. 439 and (19.30), p. 449 (iterating the flow constraint one
period): for a feasible plan the date-`t` outlay is integrable and
`E[pk_t(a_t + M_{t−1})] = E[pk_{t+1}(a_{t+1} + M_t)] + E[Λ_t(c_t + ι_tm_t + s_t − y_t)]`. -/
theorem wealth_step {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a) (t : ℕ) :
    Integrable (outlay S Λ P y s c m t) S.μ ∧
      wealthPV S Λ P N0 m a t = wealthPV S Λ P N0 m a (t + 1) +
        ∫ ω, outlay S Λ P y s c m t ω ∂S.μ := by
  obtain ⟨-, -, hma, -, hflow, hia, hiN, him, hic, -⟩ := hf
  -- the money carried into `t + 1`
  have hNm : StronglyMeasurable[S.𝓕 t] (fun ω => P t ω * m t ω) := (hp.2.1 t).mul (hma t)
  have hNi : Integrable ((fun ω => P t ω * m t ω) * pk Λ P (t + 1)) S.μ :=
    (hiN (t + 1)).congr (Eventually.of_forall fun ω => by
      simp only [moneyIn, Pi.mul_apply]
      ring)
  have hpull := condExp_mul_of_stronglyMeasurable_left hNm hNi (hp.integrable_pk (t + 1))
  have hQm : (fun ω => P t ω * m t ω) * S.E t (pk Λ P (t + 1)) =
      fun ω => bondPrice S Λ P t ω * (Λ t ω * m t ω) := by
    funext ω
    simp only [Pi.mul_apply]
    rw [hp.E_pk_eq t ω, ← hp.pk_mul_P t ω]
    ring
  rw [hQm] at hpull
  have hQi : Integrable (fun ω => bondPrice S Λ P t ω * (Λ t ω * m t ω)) S.μ :=
    integrable_condExp.congr hpull
  have hQint : ∫ ω, P t ω * m t ω * pk Λ P (t + 1) ω ∂S.μ =
      ∫ ω, bondPrice S Λ P t ω * (Λ t ω * m t ω) ∂S.μ := by
    rw [← integral_congr_ae hpull]
    exact (integral_condExp (S.𝓕.le t)).symm
  have hout : outlay S Λ P y s c m t = fun ω => Λ t ω * c t ω + (Λ t ω * m t ω -
      bondPrice S Λ P t ω * (Λ t ω * m t ω)) + Λ t ω * s t ω - Λ t ω * y t ω := by
    funext ω
    simp only [outlay, iota]
    ring
  have hoi : Integrable (outlay S Λ P y s c m t) S.μ := by
    rw [hout]
    exact (((hic t).add ((him t).sub hQi)).add (hs t)).sub (hy t)
  refine ⟨hoi, ?_⟩
  -- integrate the flow constraint multiplied by `pk_t`
  have hfl : ∀ᵐ ω ∂S.μ, pk Λ P t ω * a t ω + pk Λ P t ω * moneyIn N0 P m t ω +
      Λ t ω * y t ω - Λ t ω * c t ω = S.E t (fun ω => pk Λ P (t + 1) ω * a (t + 1) ω) ω +
        Λ t ω * m t ω + Λ t ω * s t ω := by
    filter_upwards [hflow t] with ω h
    have hk := (hp.pk_pos t ω).ne'
    have hΛ := (hp.pk_mul_P t ω).symm
    simp only [claimCost] at h
    rw [hΛ]
    have := congrArg (fun x => pk Λ P t ω * x) h
    field_simp at this
    linear_combination this
  have hI := integral_congr_ae hfl
  have i1 : Integrable (fun ω => pk Λ P t ω * a t ω + pk Λ P t ω * moneyIn N0 P m t ω) S.μ :=
    (hia t).add (hiN t)
  have i2 : Integrable (fun ω => pk Λ P t ω * a t ω + pk Λ P t ω * moneyIn N0 P m t ω +
      Λ t ω * y t ω) S.μ := i1.add (hy t)
  have j1 : Integrable (fun ω => S.E t (fun ω => pk Λ P (t + 1) ω * a (t + 1) ω) ω +
      Λ t ω * m t ω) S.μ := (S.integrable_E t _).add (him t)
  rw [integral_sub i2 (hic t), integral_add i1 (hy t), integral_add (hia t) (hiN t),
    integral_add j1 (hs t), integral_add (S.integrable_E t _) (him t), S.integral_E] at hI
  have hw1 : wealthPV S Λ P N0 m a t = ∫ ω, pk Λ P t ω * a t ω ∂S.μ +
      ∫ ω, pk Λ P t ω * moneyIn N0 P m t ω ∂S.μ := by
    rw [← integral_add (hia t) (hiN t)]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have hw2 : wealthPV S Λ P N0 m a (t + 1) = ∫ ω, pk Λ P (t + 1) ω * a (t + 1) ω ∂S.μ +
      ∫ ω, P t ω * m t ω * pk Λ P (t + 1) ω ∂S.μ := by
    have hNi' : Integrable (fun ω => P t ω * m t ω * pk Λ P (t + 1) ω) S.μ := hNi
    rw [← integral_add (hia (t + 1)) hNi']
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [moneyIn]; ring)
  have ho : ∫ ω, outlay S Λ P y s c m t ω ∂S.μ = ∫ ω, Λ t ω * c t ω ∂S.μ +
      (∫ ω, Λ t ω * m t ω ∂S.μ - ∫ ω, bondPrice S Λ P t ω * (Λ t ω * m t ω) ∂S.μ) +
      ∫ ω, Λ t ω * s t ω ∂S.μ - ∫ ω, Λ t ω * y t ω ∂S.μ := by
    have k1 : Integrable (fun ω => Λ t ω * m t ω -
        bondPrice S Λ P t ω * (Λ t ω * m t ω)) S.μ := (him t).sub hQi
    have k2 : Integrable (fun ω => Λ t ω * c t ω + (Λ t ω * m t ω -
        bondPrice S Λ P t ω * (Λ t ω * m t ω))) S.μ := (hic t).add k1
    have k3 : Integrable (fun ω => Λ t ω * c t ω + (Λ t ω * m t ω -
        bondPrice S Λ P t ω * (Λ t ω * m t ω)) + Λ t ω * s t ω) S.μ := k2.add (hs t)
    rw [hout, integral_sub k3 (hy t), integral_add k2 (hs t), integral_add (hic t) k1,
      integral_sub (him t) hQi]
  rw [hw1, hw2, ho, hQint]
  linarith

/-- Cochrane (2023), (19.12), p. 439 and (19.30), p. 449 (iterating the flow constraint
forward): `E[pk_0(a_0 + M_{−1})] = ∑_{t<T} E[Λ_t(c_t + ι_tm_t + s_t − y_t)] + E[pk_T(a_T +
M_{T−1})]`. -/
theorem wealth_telescope {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a) (T : ℕ) :
    wealthPV S Λ P N0 m a 0 = ∑ t ∈ Finset.range T, ∫ ω, outlay S Λ P y s c m t ω ∂S.μ +
      wealthPV S Λ P N0 m a T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, (wealth_step hp hy hs hf T).2]
    ring

/-- Cochrane (2023), (19.11)–(19.12), p. 439 and (19.28)–(19.30), p. 449: **the present-value
budget constraint.** For a feasible plan satisfying the transversality condition
`E[pk_T(a_T + M_{T−1})] → 0`, the date-0 value of initial wealth equals the present value of
the outlays, `E[pk_0(a_0 + M_{−1})] = ∑_{t=0}^∞ E[Λ_t(c_t + ι_tm_t + s_t − y_t)]` (the limit of
the partial sums). -/
theorem pv_budget {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hp : PriceRegular S Λ P) (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a)
    (htvc : Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ t ∈ Finset.range T, ∫ ω, outlay S Λ P y s c m t ω ∂S.μ) atTop
      (𝓝 (wealthPV S Λ P N0 m a 0)) := by
  have := (tendsto_const_nhds (x := wealthPV S Λ P N0 m a 0)).sub htvc
  rw [sub_zero] at this
  refine this.congr fun T => ?_
  rw [wealth_telescope hp hy hs hf T]
  ring


/-- Cochrane (2023), footnote 1, p. 440 and p. 453 ("first order conditions and transversality
conditions are necessary and sufficient"), on a probability space, **sufficiency**: a feasible,
admissible plan satisfying `Con` and the transversality condition `E[pk_T(a_T + M_{T−1})] → 0`
is optimal if, against every feasible competitor satisfying `Con`, almost surely at every date
`βᵗ(u(c'_t, m'_t) − u(c_t, m_t)) ≤ λΛ_t((c'_t − c_t) + ι_t(m'_t − m_t))` for a constant `λ ≥ 0`
(the supergradient form of the first-order conditions `βᵗu_c = λΛ_t`, `βᵗu_m = λΛ_tι_t`).
Competitors only need the no-Ponzi condition. -/
theorem optimal_of_supergradient {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ → ℝ}
    {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : Feasible S Λ P y s N0 a0 c m a) (hcon : Con c m)
    (hadm : UAdmissible S β (fun n ω => u (c n ω) (m n ω)))
    (htvc : Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0))
    (hsup : ∀ c' m' a', Feasible S Λ P y s N0 a0 c' m' a' → Con c' m' → ∀ t, ∀ᵐ ω ∂S.μ,
      β ^ t * (u (c' t ω) (m' t ω) - u (c t ω) (m t ω)) ≤
        lam * (Λ t ω * ((c' t ω - c t ω) + iota S Λ P t ω * (m' t ω - m t ω)))) :
    Optimal S β u Con Λ P y s N0 a0 c m a := by
  refine ⟨hf, hcon, hadm, fun c' m' a' hf' hc' hu' => ?_⟩
  set U := expU S β (fun n ω => u (c n ω) (m n ω)) with hU
  set U' := expU S β (fun n ω => u (c' n ω) (m' n ω)) with hU'
  set D : ℕ → ℝ := fun t => β ^ t * ∫ ω, u (c' t ω) (m' t ω) ∂S.μ -
    β ^ t * ∫ ω, u (c t ω) (m t ω) ∂S.μ with hD
  have hDs : HasSum D (U' - U) := (hu'.hasSum hβ).sub (hadm.hasSum hβ)
  -- date by date, the utility gain is bounded by the change in outlays
  have hle : ∀ t, D t ≤ lam * (∫ ω, outlay S Λ P y s c' m' t ω ∂S.μ -
      ∫ ω, outlay S Λ P y s c m t ω ∂S.μ) := by
    intro t
    have hi' := hu'.integrable hβ t
    have hi := hadm.integrable hβ t
    have ho' := (wealth_step hp hy hs hf' t).1
    have ho := (wealth_step hp hy hs hf t).1
    have hL : Integrable (fun ω => β ^ t * (u (c' t ω) (m' t ω) - u (c t ω) (m t ω))) S.μ :=
      (hi'.sub hi).const_mul _
    have hR : Integrable (fun ω => lam * (outlay S Λ P y s c' m' t ω -
        outlay S Λ P y s c m t ω)) S.μ := (ho'.sub ho).const_mul _
    have hmono := integral_mono_ae hL hR (by
      filter_upwards [hsup c' m' a' hf' hc' t] with ω h
      refine h.trans_eq ?_
      simp only [outlay]
      ring)
    rw [integral_const_mul, integral_const_mul, integral_sub hi' hi, integral_sub ho' ho]
      at hmono
    simp only [hD]
    linarith
  -- the outlays telescope to wealth
  have hW0 : wealthPV S Λ P N0 m' a' 0 = wealthPV S Λ P N0 m a 0 := by
    simp only [wealthPV, moneyIn, hf.1, hf'.1]
  have hpart : ∀ T, ∑ t ∈ Finset.range T, D t ≤
      lam * (wealthPV S Λ P N0 m a T - wealthPV S Λ P N0 m' a' T) := by
    intro T
    have h1 := wealth_telescope hp hy hs hf T
    have h2 := wealth_telescope hp hy hs hf' T
    calc ∑ t ∈ Finset.range T, D t
        ≤ ∑ t ∈ Finset.range T, lam * (∫ ω, outlay S Λ P y s c' m' t ω ∂S.μ -
          ∫ ω, outlay S Λ P y s c m t ω ∂S.μ) := Finset.sum_le_sum fun t _ => hle t
      _ = lam * (wealthPV S Λ P N0 m a T - wealthPV S Λ P N0 m' a' T) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
          congr 1
          linarith
  have hlimD : Tendsto (fun T => ∑ t ∈ Finset.range T, D t) atTop (𝓝 (U' - U)) :=
    hDs.tendsto_sum_nat
  by_contra hcon'
  push Not at hcon'
  set d := U' - U with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set δ := d / (2 * (lam + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hev : ∀ᶠ T in atTop, ∑ t ∈ Finset.range T, D t ≤
      lam * (wealthPV S Λ P N0 m a T + δ) := by
    filter_upwards [hf'.2.2.2.2.2.2.2.2.2 δ hδ0] with T hT
    refine (hpart T).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hlam
  have hlim2 : Tendsto (fun T => lam * (wealthPV S Λ P N0 m a T + δ)) atTop
      (𝓝 (lam * (0 + δ))) := (htvc.add_const δ).const_mul lam
  have := le_of_tendsto_of_tendsto hlimD hlim2 hev
  have hlt : lam * (0 + δ) < d := by
    rw [zero_add, hδ]
    have : lam * (d / (2 * (lam + 1))) = d * (lam / (2 * (lam + 1))) := by ring
    rw [this]
    have h1 : lam / (2 * (lam + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith
  linarith


/-! ### The consumption Euler equation for a bundle -/

variable (S) in
/-- Cochrane (2023), p. 450 (the binding cash-in-advance cost wedge of the Monetarism project): the
cost, per
unit of consumption, of the bundle "one unit of consumption with `θ` units of real balances",
`w_t = 1 + θι_t` (`θ = 0` in the money-in-utility Euler equation; `θ = 1/V − 1` in the
cash-in-advance model, where the overnight money moves one-for-`1/V − 1` with consumption). -/
noncomputable def wedge (θ : ℝ) (Λ P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  1 + θ * iota S Λ P t ω

/-- Cochrane (2023), (19.13), p. 440 and (19.31), p. 450, on a probability space: **the Euler
equation for a consumption bundle.** At an optimal plan, if `Con` allows small bounded deviations
of consumption by `z` together with real balances by `θz` at `t` and `t + 1`, and the bundle cost
`w = 1 + θι` is essentially bounded away from zero at `t`, then almost surely
`β^{t+1}V_{t+1} = κ_tΛ_{t+1}w_{t+1}` with `κ_t = βᵗV_t/(Λ_tw_t)`, where `V = u_c + θu_m` is the
marginal utility of the bundle. That is, `βᵗV_t/(Λ_tw_t)` is the same at `t` and `t + 1`. -/
theorem bundle_euler {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hopt : Optimal S β u Con Λ P y s N0 a0 c m a)
    (hp : PriceRegular S Λ P) (θ : ℝ) {t : ℕ} (hct : BddAt S (c t))
    (hct1 : BddAt S (c (t + 1))) (hmt : BddAt S (m t)) (hmt1 : BddAt S (m (t + 1)))
    (hw : ∀ᵐ ω ∂S.μ, wedge S θ Λ P t ω ≠ 0)
    (hwb : BddAt S (fun ω => (wedge S θ Λ P t ω)⁻¹))
    (hcon : ∀ z₁ z₂ : Ω → ℝ, BddAt S z₁ → BddAt S z₂ → ∃ η, 0 < η ∧ ∀ ε, |ε| < η →
      Con (bump c t z₁ z₂ ε) (bump m t (fun ω => θ * z₁ ω) (fun ω => θ * z₂ ω) ε)) :
    ∀ᵐ ω ∂S.μ, β ^ (t + 1) * (uc (c (t + 1) ω) (m (t + 1) ω) +
        θ * um (c (t + 1) ω) (m (t + 1) ω)) =
      β ^ t * (uc (c t ω) (m t ω) + θ * um (c t ω) (m t ω)) /
        (Λ t ω * wedge S θ Λ P t ω) * (Λ (t + 1) ω * wedge S θ Λ P (t + 1) ω) := by
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hle : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
  have ae : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → AEStronglyMeasurable f S.μ :=
    fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  set V : ℕ → Ω → ℝ := fun n ω => uc (c n ω) (m n ω) + θ * um (c n ω) (m n ω) with hV
  have hVc : Continuous fun p : ℝ × ℝ => uc p.1 p.2 + θ * um p.1 p.2 :=
    hu.2.1.add (continuous_const.mul hu.2.2)
  have hVm : ∀ n, StronglyMeasurable[S.𝓕 n] (V n) := fun n =>
    (hVc.measurable.comp ((hca n).measurable.prodMk (hma n).measurable)).stronglyMeasurable
  have hVb : ∀ n, BddAt S (c n) → BddAt S (m n) → BddAt S (V n) := fun n h1 h2 =>
    BddAt.comp₂ (v := fun x y => uc x y + θ * um x y) hVc h1 h2
  set w := wedge S θ Λ P with hwdef
  have hwm : ∀ n, StronglyMeasurable[S.𝓕 n] (w n) := fun n =>
    stronglyMeasurable_const.add ((hp.stronglyMeasurable_iota n).const_mul θ)
  have hwbd : ∀ n, BddAt S (w n) := fun n => (BddAt.const 1).add
    ((BddAt.const θ).mul (hp.iota_bdd n))
  -- the multiplier at `t`
  set κ : Ω → ℝ := fun ω => β ^ t * V t ω / (Λ t ω * w t ω) with hκ
  have hκm : StronglyMeasurable[S.𝓕 t] κ :=
    (((hVm t).const_mul (β ^ t)).measurable.div
      ((hp.1 t).measurable.mul (hwm t).measurable)).stronglyMeasurable
  have hκb : BddAt S κ := by
    have := (((BddAt.const (β ^ t)).mul (hVb t hct hmt)).mul (hp.2.2.2.2 t).2.1).mul hwb
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hκ]
    ring
  -- the test variable
  set G : Ω → ℝ := fun ω => β ^ (t + 1) * V (t + 1) ω - κ ω * (Λ (t + 1) ω * w (t + 1) ω)
    with hG
  have hGm : StronglyMeasurable[S.𝓕 (t + 1)] G :=
    ((hVm (t + 1)).const_mul _).sub ((hκm.mono hle).mul ((hp.1 (t + 1)).mul (hwm (t + 1))))
  have hGb : BddAt S G :=
    ((BddAt.const _).mul (hVb (t + 1) hct1 hmt1)).sub
      (hκb.mul ((hp.2.2.2.2 (t + 1)).1.mul (hwbd (t + 1))))
  set X : Ω → ℝ := fun ω => Λ (t + 1) ω * w (t + 1) ω * G ω with hX
  have hXm : StronglyMeasurable[S.𝓕 (t + 1)] X := ((hp.1 (t + 1)).mul (hwm (t + 1))).mul hGm
  have hXb : BddAt S X := ((hp.2.2.2.2 (t + 1)).1.mul (hwbd (t + 1))).mul hGb
  have hXi : Integrable X S.μ := hXb.integrable (ae hXm)
  set Y : Ω → ℝ := fun ω => S.E t X ω / (Λ t ω * w t ω) with hY
  have hYm : StronglyMeasurable[S.𝓕 t] Y :=
    ((S.stronglyMeasurable_E t X).measurable.div
      ((hp.1 t).measurable.mul (hwm t).measurable)).stronglyMeasurable
  have hYb : BddAt S Y := by
    have := ((hXb.E t).mul (hp.2.2.2.2 t).2.1).mul hwb
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hY]
    ring
  -- the deviation
  have hz₁ : StronglyMeasurable[S.𝓕 t] (fun ω => -Y ω) := hYm.neg
  have hζ₁ : StronglyMeasurable[S.𝓕 t] (fun ω => θ * -Y ω) := hYm.neg.const_mul θ
  have hζ₂ : StronglyMeasurable[S.𝓕 (t + 1)] (fun ω => θ * G ω) := hGm.const_mul θ
  have hfin : ∀ᵐ ω ∂S.μ, Λ t ω * (-Y ω + iota S Λ P t ω * (θ * -Y ω)) +
      S.E t (fun ω => Λ (t + 1) ω * (G ω + iota S Λ P (t + 1) ω * (θ * G ω))) ω = 0 := by
    have e : (fun ω => Λ (t + 1) ω * (G ω + iota S Λ P (t + 1) ω * (θ * G ω))) = X := by
      funext ω
      simp only [hX, hwdef, wedge]
      ring
    rw [e]
    filter_upwards [hw] with ω hω
    have hΛ := (hp.2.2.1 t ω).ne'
    simp only [hY]
    simp only [hwdef, wedge] at hω ⊢
    field_simp
    ring
  have key := pair_foc hβ hu hopt hp hct hct1 hmt hmt1 hz₁ hζ₁ hGm hζ₂ hYb.neg
    ((BddAt.const θ).mul hYb.neg) hGb ((BddAt.const θ).mul hGb) hfin
    (hcon _ _ hYb.neg hGb)
  -- rewrite the first-order condition as `E[G²] = 0`
  have hV0 := hVb t hct hmt
  have hV1 := hVb (t + 1) hct1 hmt1
  have i1 : Integrable (fun ω => V t ω * Y ω) S.μ :=
    (hV0.mul hYb).integrable ((ae (hVm t)).mul (ae hYm))
  have i2 : Integrable (fun ω => V (t + 1) ω * G ω) S.μ :=
    (hV1.mul hGb).integrable ((ae (hVm (t + 1))).mul (ae hGm))
  have e1 : ∫ ω, (uc (c t ω) (m t ω) * -Y ω + um (c t ω) (m t ω) * (θ * -Y ω)) ∂S.μ =
      -∫ ω, V t ω * Y ω ∂S.μ := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [hV]; ring)
  have e2 : ∫ ω, (uc (c (t + 1) ω) (m (t + 1) ω) * G ω + um (c (t + 1) ω) (m (t + 1) ω) *
      (θ * G ω)) ∂S.μ = ∫ ω, V (t + 1) ω * G ω ∂S.μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp only [hV]; ring)
  rw [e1, e2] at key
  have e3 : β ^ t * ∫ ω, V t ω * Y ω ∂S.μ = ∫ ω, κ ω * X ω ∂S.μ := by
    obtain ⟨K, hK⟩ := hκb
    rw [integral_mul_E hκm hK hXi, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [hY, hκ]; ring)
  have i3 : Integrable (fun ω => κ ω * X ω) S.μ :=
    (hκb.mul hXb).integrable ((ae hκm).mul (ae hXm))
  have hGG : ∫ ω, G ω * G ω ∂S.μ = 0 := by
    have e4 : ∫ ω, G ω * G ω ∂S.μ =
        β ^ (t + 1) * ∫ ω, V (t + 1) ω * G ω ∂S.μ - ∫ ω, κ ω * X ω ∂S.μ := by
      rw [← integral_const_mul, ← integral_sub (i2.const_mul _) i3]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [hG, hX]; ring)
    rw [e4, ← e3]
    linarith
  have hG0 := ae_eq_zero_of_integral_mul_self ((hGb.mul hGb).integrable
    ((ae hGm).mul (ae hGm))) hGG
  filter_upwards [hG0] with ω hω
  simp only [hG, Pi.zero_apply] at hω
  simp only [hκ, hV] at hω
  linarith


/-- Cochrane (2023), (19.13), p. 440 ("`βᵗu_c = Λ_t`") and (19.31), p. 450, on a probability
space: **the multiplier is constant over time.** At an optimal plan with consumption and real
balances essentially bounded at every date, bundle costs essentially bounded away from zero, and
`Con` stable under small bundle deviations, `βᵗV_t/(Λ_tw_t) = V_0/(Λ_0w_0)` almost surely at
every date, where `V = u_c + θu_m` and `w = 1 + θι`: `βᵗV_t = λΛ_tw_t` with the single
multiplier `λ = V_0/(Λ_0w_0)`, known at date `0`. -/
theorem bundle_multiplier_const {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um) {Con : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop} {Λ P y s : ℕ → Ω → ℝ}
    {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} (hopt : Optimal S β u Con Λ P y s N0 a0 c m a)
    (hp : PriceRegular S Λ P) (θ : ℝ) (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hw : ∀ n, ∀ᵐ ω ∂S.μ, wedge S θ Λ P n ω ≠ 0)
    (hwb : ∀ n, BddAt S (fun ω => (wedge S θ Λ P n ω)⁻¹))
    (hcon : ∀ n (z₁ z₂ : Ω → ℝ), BddAt S z₁ → BddAt S z₂ → ∃ η, 0 < η ∧ ∀ ε, |ε| < η →
      Con (bump c n z₁ z₂ ε) (bump m n (fun ω => θ * z₁ ω) (fun ω => θ * z₂ ω) ε)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ t * (uc (c t ω) (m t ω) + θ * um (c t ω) (m t ω)) /
        (Λ t ω * wedge S θ Λ P t ω) =
      (uc (c 0 ω) (m 0 ω) + θ * um (c 0 ω) (m 0 ω)) / (Λ 0 ω * wedge S θ Λ P 0 ω) := by
  induction t with
  | zero => exact Eventually.of_forall fun ω => by simp
  | succ t ih =>
    filter_upwards [ih, bundle_euler hβ hu hopt hp θ (hcb t) (hcb (t + 1)) (hmb t) (hmb (t + 1))
      (hw t) (hwb t) (hcon t), hw (t + 1)] with ω h1 h2 h3
    have hΛ := (hp.2.2.1 (t + 1) ω).ne'
    rw [h2, ← h1]
    field_simp

/-! ### Finite event trees as probability spaces -/

namespace TreeLink

open ExpectationsFiniteTree TreeBridge

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), footnote 1, p. 440 (every node has positive probability): on a finite event
tree a statement that holds almost surely holds in every state. -/
theorem forall_of_ae {p : Ω' → Prop} (h : ∀ᵐ ω ∂(treeSystem T).μ, p ω) (ω : Ω') : p ω := by
  by_contra hne
  have h0 : (treeSystem T).μ {ω' | ¬ p ω'} = 0 := ae_iff.mp h
  exact treeSystem_fullSupport T ω (measure_mono_null (fun ω' hω' => by
    rw [Set.mem_singleton_iff.mp hω']
    exact hne) h0)

/-- Cochrane (2023), footnote 1, p. 440 (`c_t(x^t)`): a variable constant on the date-`t`
information cells is `𝓕_t`-measurable for the tree's filtration. -/
theorem stronglyMeasurable_of_cell {t : ℕ} {x : Ω' → ℝ}
    (hx : ∀ ω ω', T.info t ω' ω → x ω' = x ω) :
    StronglyMeasurable[(treeSystem T).𝓕 t] x := by
  have e : T.condE t x = x := funext fun ω => T.condE_of_const_on_cell (hx ω)
  rw [← e]
  exact stronglyMeasurable_condE T t x

/-- Cochrane (2023), footnote 1, p. 440 (`c_t(x^t)`): a variable that is `𝓕_t`-measurable for
the tree's filtration is constant on the date-`t` information cells. -/
theorem cell_const {t : ℕ} {x : Ω' → ℝ} (hx : StronglyMeasurable[(treeSystem T).𝓕 t] x)
    {ω ω' : Ω'} (h : T.info t ω' ω) : x ω' = x ω := by
  have hm : MeasurableSet[treeFiltration T t] (x ⁻¹' {x ω}) :=
    hx.measurable (measurableSet_singleton _)
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 hm
  have hω : ω ∈ x ⁻¹' {x ω} := rfl
  rw [← hB] at hω
  have hω' : ω' ∈ Quotient.mk (T.info t) ⁻¹' B := by
    rw [Set.mem_preimage, Quotient.sound h]
    exact hω
  rw [hB] at hω'
  exact hω'

/-- Cochrane (2023), footnote 1, p. 440: on a finite state space every variable is bounded. -/
theorem bddAt_of_finite (f : Ω' → ℝ) : BddAt (treeSystem T) f :=
  ⟨∑ ω, |f ω|, Eventually.of_forall fun ω => Finset.single_le_sum (f := fun ω => |f ω|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ ω)⟩

/-- Cochrane (2023), p. 439: on a finite event tree, positive state prices and price levels that
are functions of the node are regular. -/
theorem priceRegular {Λ P : ℕ → Ω' → ℝ} (hΛa : ∀ t ω ω', T.info t ω' ω → Λ t ω' = Λ t ω)
    (hPa : ∀ t ω ω', T.info t ω' ω → P t ω' = P t ω) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hP : ∀ t ω, 0 < P t ω) : PriceRegular (treeSystem T) Λ P :=
  ⟨fun t => stronglyMeasurable_of_cell T (hΛa t), fun t => stronglyMeasurable_of_cell T (hPa t),
    hΛ, hP, fun _ => ⟨bddAt_of_finite T _, bddAt_of_finite T _, bddAt_of_finite T _,
      bddAt_of_finite T _⟩⟩

end TreeLink

end Cochrane.NewKeynesianSelection.TidyR6HouseholdMoney
