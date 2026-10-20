/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.ReturnDiscounting
import FiscalConstraints.ExpectationsFiniteTree
import FiscalConstraints.ForwardSolution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Aggregate uncertainty, `r < g` and present values

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.7, pp. 205–207,
equations (6.15)–(6.18).

Consumption `c_t = y_t > 0` grows by i.i.d. factors `G_{t+1} = c_{t+1}/c_t`; the
representative consumer has power utility, so the SDF is `β^j (c_{t+j}/c_t)^{−γ}`. In an
`ExpectationSystem` with the pull-out property, "i.i.d. growth" is the hypothesis
`E_t[G_{t+1}^a] = mom a` (a constant) for every real `a` (`IIDGrowth`), and "`c_t^a` is known at
`t`" is `KnownPowers`.

## Main results

* `E_ratio_pow_mul`: `E_t[(c_{t+j}/c_t)^a X] = (mom a)^j X` for `X` known at `t`.
* `correct_term` (6.15): the correct summands are `(β mom(1−γ))^j κ`;
  `incorrect_term` (6.16): the summands with the expectation inside are
  `(β mom(−γ) mom 1)^j κ = ((1+g)/(1+r))^j κ`.
* `correct_finite_incorrect_explodes`: the correct present value converges while the
  incorrect one diverges whenever `β mom(1−γ) < 1 ≤ β mom(−γ) mom 1`.
* Lognormal growth: `lognormalMoment_eq_integral` (Gaussian moment generating function),
  `lognormal_correct`, `lognormal_incorrect` (corrected exponent `(γ²+1)σ²/2`),
  `printed_incorrect_wrong`, `region_nonempty_iff` (non-empty iff `γ > 0`),
  `printed_region_iff` (`γ > 1/2` with the printed exponent), `log_riskFree_lognormal`,
  `printed_bohn_rate_wrong`, `riskFree_lt_growth_iff`, `bohn_region`.
* (6.17): `eq_6_17` for any debt rolled over at the risk-free rate, `terminal_c`, `pv_term_c`,
  `bohn_pv_hasSum_iff` (infinite horizon iff `β E[G^{1−γ}] < 1`), `terminal_tendsto_iff`.
* (6.18): `eq_6_18_pathwise`, `eq_6_18`, `eq_6_18_diverges`.
* The two-state witness: `bohnTree` (an i.i.d. coin tree of any horizon), `bohnSystem_iid`,
  `bohn_numbers` (`r_f ≈ 0.83% < E g = 5%`, `β E[G^{−1}] ≈ 0.968 < 1`), `bohn_witness_6_17`,
  `bohn_witness_6_18`.
-/

namespace Cochrane.FiscalConstraints.AggregateUncertainty

open Filter Topology

variable {Ω : Type*}

/-- Cochrane (2023), p. 205: every power `c_t^a` of consumption is known at date `t`. -/
def KnownPowers (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ℝ) : Prop :=
  ∀ t (a : ℝ), 𝔼.E t (fun ω => c t ω ^ a) = fun ω => c t ω ^ a

/-- Cochrane (2023), p. 205: consumption growth `G_{t+1} = c_{t+1}/c_t`. -/
noncomputable def growth (c : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := c (t + 1) ω / c t ω

/-- Cochrane (2023), p. 205 ("consumption and GDP growth are independent over time"): for
dates `t < H`, `E_t[G_{t+1}^a] = mom a`, the same constant at every date and state. -/
def IIDGrowth (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ℝ) (mom : ℝ → ℝ) (H : ℕ) : Prop :=
  ∀ t, t < H → ∀ a : ℝ, 𝔼.E t (fun ω => growth c t ω ^ a) = fun _ => mom a

/-- Cochrane (2023), (6.15) p. 205: the consumption ratio `c_{t+j}/c_t`. -/
noncomputable def ratio (c : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ := c (t + j) ω / c t ω

/-- Cochrane (2023), (6.17) p. 207: the stochastic discount factor
`β^j (c_{t+j}/c_t)^{−γ}`. -/
noncomputable def pvDisc (β γ : ℝ) (c : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  β ^ j * ratio c t j ω ^ (-γ)

/-- Cochrane (2023), p. 206: the gross risk-free rate `1 + r = 1/(β E[G^{−γ}])`. -/
noncomputable def riskFreeGross (β γ : ℝ) (mom : ℝ → ℝ) : ℝ := (β * mom (-γ))⁻¹

/-- Cochrane (2023), p. 205: with the pull-out property, products of known variables are
known. -/
theorem known_mul (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {t : ℕ} {x y : Ω → ℝ}
    (hx : 𝔼.E t x = x) (hy : 𝔼.E t y = y) :
    𝔼.E t (fun ω => x ω * y ω) = fun ω => x ω * y ω := by
  have h := hpo t x y hx
  rw [hy] at h
  exact h

/-- Cochrane (2023), (6.15) p. 205: `c_t/c_t = 1`. -/
theorem ratio_zero {c : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (h : c t ω ≠ 0) : ratio c t 0 ω = 1 := by
  simp [ratio, h]

/-- Cochrane (2023), (6.15) p. 205: `c_{t+j+1}/c_t = (c_{t+j}/c_t) G_{t+j+1}`. -/
theorem ratio_succ {c : ℕ → Ω → ℝ} {t j : ℕ} {ω : Ω} (h0 : c t ω ≠ 0) (h1 : c (t + j) ω ≠ 0) :
    ratio c t (j + 1) ω = ratio c t j ω * growth c (t + j) ω := by
  unfold ratio growth
  rw [← add_assoc]
  field_simp

/-- Cochrane (2023), (6.15) p. 205: consumption ratios are positive. -/
theorem ratio_pos {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (t j : ℕ) (ω : Ω) :
    0 < ratio c t j ω := div_pos (hpos _ _) (hpos _ _)

/-- Cochrane (2023), p. 205: consumption growth is positive. -/
theorem growth_pos {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (t : ℕ) (ω : Ω) :
    0 < growth c t ω := div_pos (hpos _ _) (hpos _ _)

/-- Cochrane (2023), (6.15) p. 205: powers of `c_{t+j}/c_t` are known at `t + j`. -/
theorem ratio_rpow_known (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) (t j : ℕ) (a : ℝ) :
    𝔼.E (t + j) (fun ω => ratio c t j ω ^ a) = fun ω => ratio c t j ω ^ a := by
  have h : (fun ω => ratio c t j ω ^ a) = fun ω => c (t + j) ω ^ a * c t ω ^ (-a) := by
    funext ω
    rw [ratio, Real.div_rpow (hpos _ _).le (hpos _ _).le, Real.rpow_neg (hpos _ _).le,
      div_eq_mul_inv]
  rw [h]
  exact known_mul 𝔼 hpo (hkp (t + j) a)
    (ForwardSolution.E_of_known 𝔼 (Nat.le_add_right t j) (hkp t (-a)))

/-- Cochrane (2023), p. 205: one period of i.i.d. growth, `E_s[Y G_{s+1}^a] = mom a · Y` for
`Y` known at `s < H`. -/
theorem E_growth_mul (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    {mom : ℝ → ℝ} {H : ℕ} (hiid : IIDGrowth 𝔼 c mom H) {s : ℕ} (hs : s < H) {Y : Ω → ℝ}
    (hY : 𝔼.E s Y = Y) (a : ℝ) :
    𝔼.E s (fun ω => Y ω * growth c s ω ^ a) = fun ω => mom a * Y ω := by
  have h := hpo s Y (fun ω => growth c s ω ^ a) hY
  rw [hiid s hs a] at h
  change 𝔼.E s (Y * fun ω => growth c s ω ^ a) = _
  rw [h]
  funext ω
  simp only [Pi.mul_apply]
  ring

/-- Cochrane (2023), (6.15) p. 205 (i.i.d. growth over `j` periods):
`E_t[(c_{t+j}/c_t)^a X] = (mom a)^j X` for `X` known at `t`, when `t + j ≤ H`. -/
theorem E_ratio_pow_mul (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {t : ℕ} {X : Ω → ℝ} (hX : 𝔼.E t X = X) (a : ℝ) :
    ∀ j, t + j ≤ H →
      𝔼.E t (fun ω => ratio c t j ω ^ a * X ω) = fun ω => mom a ^ j * X ω := by
  intro j
  induction j with
  | zero =>
    intro _
    have h : (fun ω => ratio c t 0 ω ^ a * X ω) = X := by
      funext ω; rw [ratio_zero (hpos t ω).ne', Real.one_rpow, one_mul]
    rw [h, hX]
    funext ω
    simp
  | succ j ih =>
    intro hj
    have hY : 𝔼.E (t + j) (fun ω => ratio c t j ω ^ a * X ω) =
        fun ω => ratio c t j ω ^ a * X ω :=
      known_mul 𝔼 hpo (ratio_rpow_known 𝔼 hpo hpos hkp t j a)
        (ForwardSolution.E_of_known 𝔼 (Nat.le_add_right t j) hX)
    have hfun : (fun ω => ratio c t (j + 1) ω ^ a * X ω) =
        fun ω => (ratio c t j ω ^ a * X ω) * growth c (t + j) ω ^ a := by
      funext ω
      rw [ratio_succ (hpos t ω).ne' (hpos (t + j) ω).ne',
        Real.mul_rpow (ratio_pos hpos t j ω).le (growth_pos hpos (t + j) ω).le]
      ring
    rw [hfun, ← 𝔼.tower (Nat.le_add_right t j), E_growth_mul 𝔼 hpo hiid (by omega) hY a]
    have hs : (fun ω => mom a * (ratio c t j ω ^ a * X ω)) =
        mom a • fun ω => ratio c t j ω ^ a * X ω := rfl
    rw [hs, 𝔼.E_smul, ih (by omega)]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- Cochrane (2023), p. 206: the risk-free rate prices the one-period riskless bond,
`E_s[β G_{s+1}^{−γ}] (1 + r) = 1`, for `s < H`. -/
theorem riskFree_prices (𝔼 : ExpectationSystem Ω) {c : ℕ → Ω → ℝ} {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ : ℝ} (hβm : β * mom (-γ) ≠ 0) {s : ℕ} (hs : s < H) :
    𝔼.E s (fun ω => β * growth c s ω ^ (-γ) * riskFreeGross β γ mom) = fun _ => 1 := by
  have h : (fun ω => β * growth c s ω ^ (-γ) * riskFreeGross β γ mom) =
      (β * riskFreeGross β γ mom) • fun ω => growth c s ω ^ (-γ) := by
    funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h, 𝔼.E_smul, hiid s hs]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, riskFreeGross]
  field_simp
  exact div_self hβm

/-! ### (6.15) and (6.16): the correct and the incorrect present value -/

/-- Cochrane (2023), (6.15) p. 205: the summand with `c = y` and a constant surplus ratio `κ`,
`β^j (u'(c_{t+j})/u'(c_t)) (y_{t+j}/y_t) κ`. -/
noncomputable def pvTerm (β γ κ : ℝ) (c : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  β ^ j * ratio c t j ω ^ (-γ) * ratio c t j ω * κ

/-- Cochrane (2023), (6.15) p. 205: the correct summands are `E_t[β^j (c_{t+j}/c_t)^{1−γ}] κ =
(β mom(1−γ))^j κ`. -/
theorem correct_term (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) (β γ κ : ℝ) {t j : ℕ} (hj : t + j ≤ H) :
    𝔼.E t (pvTerm β γ κ c t j) = fun _ => (β * mom (1 - γ)) ^ j * κ := by
  have h : pvTerm β γ κ c t j = (β ^ j * κ) • fun ω => ratio c t j ω ^ (1 - γ) * 1 := by
    funext ω
    simp only [pvTerm, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos hpos t j ω),
      Real.rpow_one]
    ring
  rw [h, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid (𝔼.const t 1) (1 - γ) j hj]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), (6.16) p. 205: the summands with the expectation moved inside,
`E_t[β^j (c_{t+j}/c_t)^{−γ}] E_t[c_{t+j}/c_t] κ = (β mom(−γ) mom 1)^j κ`. -/
theorem incorrect_term (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) (β γ κ : ℝ) {t j : ℕ} (hj : t + j ≤ H) (ω : Ω) :
    𝔼.E t (fun ω' => β ^ j * ratio c t j ω' ^ (-γ)) ω * 𝔼.E t (ratio c t j) ω * κ =
      (β * mom (-γ) * mom 1) ^ j * κ := by
  have h1 : (fun ω' => β ^ j * ratio c t j ω' ^ (-γ)) =
      β ^ j • fun ω' => ratio c t j ω' ^ (-γ) * 1 := by
    funext ω'; simp
  have h2 : ratio c t j = fun ω' => ratio c t j ω' ^ (1 : ℝ) * 1 := by
    funext ω'; simp
  rw [h1, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid (𝔼.const t 1) (-γ) j hj, h2,
    E_ratio_pow_mul 𝔼 hpo hpos hkp hiid (𝔼.const t 1) 1 j hj]
  simp only [Pi.smul_apply, smul_eq_mul, mul_one, mul_pow]

/-- Cochrane (2023), (6.16) p. 205: with `1 + g = E[G]` and `1 + r = 1/(β E[G^{−γ}])`, the
incorrect discount factor is `((1+g)/(1+r))^j`. -/
theorem incorrect_ratio_eq {β γ : ℝ} {mom : ℝ → ℝ} (j : ℕ) :
    (β * mom (-γ) * mom 1) ^ j = (mom 1 / riskFreeGross β γ mom) ^ j := by
  rw [riskFreeGross, div_inv_eq_mul]
  ring

/-- Cochrane (2023), pp. 205–206: a geometric series `Σ_{j≥1} q^j κ` with `κ ≠ 0` converges
iff `|q| < 1`. -/
theorem summable_geom_succ_iff {q κ : ℝ} (hκ : κ ≠ 0) :
    Summable (fun j : ℕ => q ^ (j + 1) * κ) ↔ |q| < 1 := by
  rw [summable_nat_add_iff 1 (f := fun j : ℕ => q ^ j * κ), summable_mul_right_iff hκ,
    summable_geometric_iff_norm_lt_one, Real.norm_eq_abs]

/-- Cochrane (2023), (6.15) p. 205: with i.i.d. growth at every date, the correct present
value `Σ_{j≥1} E_t[...]` converges iff `|β mom(1−γ)| < 1` (for `κ ≠ 0`). -/
theorem correct_pv_summable_iff (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) (ω : Ω) :
    Summable (fun j => 𝔼.E t (pvTerm β γ κ c t (j + 1)) ω) ↔ |β * mom (1 - γ)| < 1 := by
  have h : (fun j => 𝔼.E t (pvTerm β γ κ c t (j + 1)) ω) =
      fun j => (β * mom (1 - γ)) ^ (j + 1) * κ := by
    funext j
    rw [correct_term 𝔼 hpo hpos hkp (hiid (t + (j + 1))) β γ κ le_rfl]
  rw [h, summable_geom_succ_iff hκ]

/-- Cochrane (2023), (6.16) p. 205: the incorrect present value converges iff
`|β mom(−γ) mom 1| < 1`, i.e. iff `(1+g)/(1+r) < 1` (for `κ ≠ 0`). -/
theorem incorrect_pv_summable_iff (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) (ω : Ω) :
    Summable (fun j => 𝔼.E t (fun ω' => β ^ (j + 1) * ratio c t (j + 1) ω' ^ (-γ)) ω *
        𝔼.E t (ratio c t (j + 1)) ω * κ) ↔ |β * mom (-γ) * mom 1| < 1 := by
  have h : (fun j => 𝔼.E t (fun ω' => β ^ (j + 1) * ratio c t (j + 1) ω' ^ (-γ)) ω *
      𝔼.E t (ratio c t (j + 1)) ω * κ) = fun j => (β * mom (-γ) * mom 1) ^ (j + 1) * κ := by
    funext j
    exact incorrect_term 𝔼 hpo hpos hkp (hiid (t + (j + 1))) β γ κ le_rfl ω
  rw [h, summable_geom_succ_iff hκ]

/-- Cochrane (2023), p. 205 ("the true present value can converge while this mistaken one
explodes"): if `0 ≤ β mom(1−γ) < 1 ≤ β mom(−γ) mom 1` then the correct present value (6.15)
converges and the incorrect one (6.16) does not. -/
theorem correct_finite_incorrect_explodes (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {c : ℕ → Ω → ℝ} (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) {β γ κ : ℝ} (hκ : κ ≠ 0)
    (hq0 : 0 ≤ β * mom (1 - γ)) (hq1 : β * mom (1 - γ) < 1)
    (hρ : 1 ≤ β * mom (-γ) * mom 1) (t : ℕ) (ω : Ω) :
    Summable (fun j => 𝔼.E t (pvTerm β γ κ c t (j + 1)) ω) ∧
      ¬ Summable (fun j => 𝔼.E t (fun ω' => β ^ (j + 1) * ratio c t (j + 1) ω' ^ (-γ)) ω *
        𝔼.E t (ratio c t (j + 1)) ω * κ) := by
  rw [correct_pv_summable_iff 𝔼 hpo hpos hkp hiid β γ hκ t ω,
    incorrect_pv_summable_iff 𝔼 hpo hpos hkp hiid β γ hκ t ω, abs_of_nonneg hq0]
  refine ⟨hq1, fun h => ?_⟩
  have := le_abs_self (β * mom (-γ) * mom 1)
  linarith

/-! ### Lognormal growth -/

/-- Cochrane (2023), p. 205: the moment `E[G^a] = e^{a μ + v a²/2}` of lognormal growth with
`log G ~ N(μ, v)`. -/
noncomputable def lognormalMoment (μ v a : ℝ) : ℝ := Real.exp (a * μ + v * a ^ 2 / 2)

/-- Cochrane (2023), p. 205: the lognormal moment formula, proved from the Gaussian moment
generating function: `∫ (e^x)^a d N(μ, v) = e^{a μ + v a²/2}`. -/
theorem lognormalMoment_eq_integral (μ : ℝ) (v : NNReal) (a : ℝ) :
    ∫ x, Real.exp x ^ a ∂(ProbabilityTheory.gaussianReal μ v) = lognormalMoment μ v a := by
  have h : (fun x => Real.exp x ^ a) = fun x => Real.exp (a * x) := by
    funext x; rw [← Real.exp_mul, mul_comm]
  rw [h]
  have hm := congrFun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := μ) (v := v)) a
  rw [ProbabilityTheory.mgf] at hm
  rw [hm, lognormalMoment]
  ring_nf

/-- Cochrane (2023), p. 205: with `β = e^{−δ}`, the ratio of successive correct terms is
`β E[G^{1−γ}] = e^{−δ + (1−γ)μ + (1−γ)² v/2}`. -/
theorem lognormal_correct (δ γ μ v : ℝ) :
    Real.exp (-δ) * lognormalMoment μ v (1 - γ) =
      Real.exp (-δ + (1 - γ) * μ + (1 - γ) ^ 2 * v / 2) := by
  rw [lognormalMoment, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 206 (corrected): the ratio of successive incorrect terms is
`β E[G^{−γ}] E[G] = e^{−δ + (1−γ)μ + (γ²+1) v/2}`. -/
theorem lognormal_incorrect (δ γ μ v : ℝ) :
    Real.exp (-δ) * lognormalMoment μ v (-γ) * lognormalMoment μ v 1 =
      Real.exp (-δ + (1 - γ) * μ + (γ ^ 2 + 1) * v / 2) := by
  rw [lognormalMoment, lognormalMoment, ← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 206 (error in the book): the printed incorrect term
`e^{[(1−γ)g + γ²σ²/2] j}` drops the `σ²/2` of `E[c'/c]`; for `v = σ² ≠ 0` the true value
`E[G^{−γ}] E[G]` differs from the printed `e^{(1−γ)μ + γ² v/2}`. -/
theorem printed_incorrect_wrong (γ μ : ℝ) {v : ℝ} (hv : v ≠ 0) :
    lognormalMoment μ v (-γ) * lognormalMoment μ v 1 ≠
      Real.exp ((1 - γ) * μ + γ ^ 2 * v / 2) := by
  rw [lognormalMoment, lognormalMoment, ← Real.exp_add]
  intro h
  have := Real.exp_injective h
  apply hv
  linarith

/-- Cochrane (2023), p. 206: the log-ratio of the correct terms,
`A = −δ + (1−γ)μ + (1−γ)² v/2`. -/
noncomputable def correctExponent (δ γ μ v : ℝ) : ℝ := -δ + (1 - γ) * μ + (1 - γ) ^ 2 * v / 2

/-- Cochrane (2023), p. 206 (corrected): the log-ratio of the incorrect terms,
`B = −δ + (1−γ)μ + (γ²+1) v/2`. -/
noncomputable def incorrectExponent (δ γ μ v : ℝ) : ℝ := -δ + (1 - γ) * μ + (γ ^ 2 + 1) * v / 2

/-- Cochrane (2023), p. 206: the exponent printed in the book, `−δ + (1−γ)μ + γ² v/2`. -/
noncomputable def printedExponent (δ γ μ v : ℝ) : ℝ := -δ + (1 - γ) * μ + γ ^ 2 * v / 2

/-- Cochrane (2023), p. 206 (corrected; "it is entirely possible"): for `v = σ² > 0` there is a
`δ` with the correct present value finite (`A < 0`) and the incorrect one explosive (`B > 0`)
iff `γ > 0`; the book's sufficient condition `γ > 1` is not needed. -/
theorem region_nonempty_iff (γ μ : ℝ) {v : ℝ} (hv : 0 < v) :
    (∃ δ, correctExponent δ γ μ v < 0 ∧ 0 < incorrectExponent δ γ μ v) ↔ 0 < γ := by
  unfold correctExponent incorrectExponent
  constructor
  · rintro ⟨δ, h1, h2⟩
    by_contra hγ
    push Not at hγ
    nlinarith
  · intro hγ
    refine ⟨(1 - γ) * μ + ((1 - γ) ^ 2 + γ) * v / 2, ?_, ?_⟩ <;> nlinarith

/-- Cochrane (2023), p. 206: with the printed exponent the region is non-empty iff
`γ > 1/2` (for `v > 0`), so the printed formula would wrongly exclude `0 < γ ≤ 1/2`. -/
theorem printed_region_iff (γ μ : ℝ) {v : ℝ} (hv : 0 < v) :
    (∃ δ, correctExponent δ γ μ v < 0 ∧ 0 < printedExponent δ γ μ v) ↔ 1 / 2 < γ := by
  unfold correctExponent printedExponent
  constructor
  · rintro ⟨δ, h1, h2⟩
    by_contra hγ
    push Not at hγ
    nlinarith
  · intro hγ
    refine ⟨(1 - γ) * μ + ((1 - γ) ^ 2 + (γ - 1 / 2)) * v / 2, ?_, ?_⟩ <;> nlinarith

/-- Cochrane (2023), p. 206: for every `γ > 0` and `v > 0` there are a mean growth `μ` and a
discount rate `δ > 0` in the region. -/
theorem region_pos_delta {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v) :
    ∃ μ δ, 0 < δ ∧ correctExponent δ γ μ v < 0 ∧ 0 < incorrectExponent δ γ μ v := by
  refine ⟨0, ((1 - γ) ^ 2 + γ) * v / 2, by positivity, ?_, ?_⟩ <;>
    simp only [correctExponent, incorrectExponent] <;> nlinarith

/-- Cochrane (2023), p. 206 (Bohn's risk-free rate, corrected): with `β = e^{−δ}` and
lognormal growth, `log(1 + r_f) = δ + γ μ − γ² v/2`. -/
theorem log_riskFree_lognormal (δ γ μ v : ℝ) :
    Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) =
      δ + γ * μ - γ ^ 2 * v / 2 := by
  rw [riskFreeGross, lognormalMoment, ← Real.exp_add, ← Real.exp_neg, Real.log_exp]
  ring

/-- Cochrane (2023), p. 206: in terms of the log of mean gross growth `g_m = μ + v/2`,
`log(1 + r_f) = δ + γ g_m − γ(γ + 1) v/2`. -/
theorem log_riskFree_mean_growth (δ γ μ v : ℝ) :
    Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) =
      δ + γ * Real.log (lognormalMoment μ v 1) - γ * (γ + 1) * v / 2 := by
  rw [log_riskFree_lognormal, lognormalMoment, Real.log_exp]
  ring

/-- Cochrane (2023), p. 206 (error in the book): the printed `r = δ + γ g − γ(γ − 1)σ²/2`
matches neither convention when `γ σ² ≠ 0`: not `g = μ` (true `δ + γμ − γ²σ²/2`), nor
`g = g_m` (true `δ + γ g_m − γ(γ+1)σ²/2`). -/
theorem printed_bohn_rate_wrong (δ μ : ℝ) {γ v : ℝ} (hγ : γ ≠ 0) (hv : v ≠ 0) :
    δ + γ * μ - γ * (γ - 1) * v / 2 ≠
        Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) ∧
      δ + γ * Real.log (lognormalMoment μ v 1) - γ * (γ - 1) * v / 2 ≠
        Real.log (riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v)) := by
  rw [log_riskFree_lognormal, lognormalMoment, Real.log_exp]
  have hγv : γ * v ≠ 0 := mul_ne_zero hγ hv
  constructor
  · intro h; apply hγv; linarith
  · intro h; apply hγv; linarith

/-- Cochrane (2023), p. 206: the risk-free rate is below mean growth, `1 + r_f < E[G]`, iff
the incorrect present value explodes (`B > 0`): the two statements are the same. -/
theorem riskFree_lt_growth_iff (δ γ μ v : ℝ) :
    riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) < lognormalMoment μ v 1 ↔
      0 < incorrectExponent δ γ μ v := by
  have hR : riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) =
      Real.exp (δ + γ * μ - γ ^ 2 * v / 2) := by
    rw [← log_riskFree_lognormal δ γ μ v, Real.exp_log]
    rw [riskFreeGross]
    exact inv_pos.mpr (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  rw [hR, lognormalMoment, Real.exp_lt_exp, incorrectExponent]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), pp. 205–206 (Theorem B, lognormal form): for every `γ > 0` and `σ² > 0`
there are `μ` and `δ > 0` such that the correct present value converges
(`β E[G^{1−γ}] < 1`, `β = e^{−δ}`) while the risk-free rate is below mean growth. -/
theorem bohn_region {γ v : ℝ} (hγ : 0 < γ) (hv : 0 < v) :
    ∃ μ δ, 0 < δ ∧ Real.exp (-δ) * lognormalMoment μ v (1 - γ) < 1 ∧
      riskFreeGross (Real.exp (-δ)) γ (lognormalMoment μ v) < lognormalMoment μ v 1 := by
  obtain ⟨μ, δ, hδ, hA, hB⟩ := region_pos_delta hγ hv
  refine ⟨μ, δ, hδ, ?_, (riskFree_lt_growth_iff δ γ μ v).mpr hB⟩
  rw [lognormal_correct, Real.exp_lt_one_iff]
  exact hA

/-! ### (6.17): debt rolled over at the risk-free rate -/

/-- Cochrane (2023), (6.17) p. 207: rolling debt over at the risk-free rate: with
`β mom(−γ) R = 1` and `b` adapted, `E_t[D_{j+1} R b_{t+j}] = E_t[D_j b_{t+j}]` for
`t + j < H` ("the present value of borrowing and repaying `(1+r)` next period is zero"). -/
theorem rollover_step (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {b : ℕ → Ω → ℝ} (hb : 𝔼.Adapted b) {t j : ℕ} (hj : t + j < H) :
    𝔼.E t (fun ω => pvDisc β γ c t (j + 1) ω * (R * b (t + j) ω)) =
      𝔼.E t (fun ω => pvDisc β γ c t j ω * b (t + j) ω) := by
  have hY : 𝔼.E (t + j) (fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω) =
      fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω :=
    known_mul 𝔼 hpo (ratio_rpow_known 𝔼 hpo hpos hkp t j (-γ)) (hb (t + j))
  have hL : (fun ω => pvDisc β γ c t (j + 1) ω * (R * b (t + j) ω)) =
      (β ^ (j + 1) * R) •
        fun ω => (ratio c t j ω ^ (-γ) * b (t + j) ω) * growth c (t + j) ω ^ (-γ) := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, smul_eq_mul]
    rw [ratio_succ (hpos t ω).ne' (hpos (t + j) ω).ne',
      Real.mul_rpow (ratio_pos hpos t j ω).le (growth_pos hpos (t + j) ω).le]
    ring
  have hRt : (fun ω => pvDisc β γ c t j ω * b (t + j) ω) =
      β ^ j • fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω := by
    funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
  rw [hL, hRt, 𝔼.E_smul, 𝔼.E_smul, ← 𝔼.tower (Nat.le_add_right t j),
    E_growth_mul 𝔼 hpo hiid hj hY (-γ)]
  have hs : (fun ω => mom (-γ) * (ratio c t j ω ^ (-γ) * b (t + j) ω)) =
      mom (-γ) • fun ω => ratio c t j ω ^ (-γ) * b (t + j) ω := rfl
  rw [hs, 𝔼.E_smul, smul_smul]
  congr 1
  linear_combination β ^ j * hR

/-- **(6.17)**, Cochrane (2023), p. 207: if debt `b` (adapted) is rolled over at the risk-free
rate, `s_{u+1} = R b_u − b_{u+1}` with `β E[G^{−γ}] R = 1`, then for `t + T ≤ H`
`b_t = E_t Σ_{j=1}^T β^j (c_{t+j}/c_t)^{−γ} s_{t+j} + E_t[β^T (c_{t+T}/c_t)^{−γ} b_{t+T}]`. -/
theorem eq_6_17 (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {b s : ℕ → Ω → ℝ} (hb : 𝔼.Adapted b) (hs : ∀ u ω, s (u + 1) ω = R * b u ω - b (u + 1) ω)
    (t : ℕ) : ∀ T, t + T ≤ H →
      b t = 𝔼.E t (fun ω => ∑ j ∈ Finset.range T, pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω)
        + 𝔼.E t (fun ω => pvDisc β γ c t T ω * b (t + T) ω) := by
  intro T
  induction T with
  | zero =>
    intro _
    have h0 : (fun ω => ∑ j ∈ Finset.range 0, pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
        0 := by funext ω; simp
    have h1 : (fun ω => pvDisc β γ c t 0 ω * b (t + 0) ω) = b t := by
      funext ω; simp [pvDisc, ratio_zero (hpos t ω).ne']
    rw [h0, h1, map_zero, hb t, zero_add]
  | succ T ih =>
    intro hT
    rw [ih (by omega)]
    have hsplit : (fun ω => ∑ j ∈ Finset.range (T + 1),
        pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
        (fun ω => ∑ j ∈ Finset.range T, pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) +
          fun ω => pvDisc β γ c t (T + 1) ω * s (t + T + 1) ω := by
      funext ω; simp [Finset.sum_range_succ]
    have hcomb : (fun ω => pvDisc β γ c t (T + 1) ω * s (t + T + 1) ω) +
        (fun ω => pvDisc β γ c t (T + 1) ω * b (t + (T + 1)) ω) =
        fun ω => pvDisc β γ c t (T + 1) ω * (R * b (t + T) ω) := by
      funext ω
      simp only [Pi.add_apply]
      rw [hs (t + T) ω, ← add_assoc]
      ring
    have hstep := rollover_step 𝔼 hpo hpos hkp hiid hR hb (t := t) (j := T) (by omega)
    rw [hsplit, map_add, add_assoc, ← hstep, ← hcomb, map_add]

/-- Cochrane (2023), (6.17) p. 207: for the debt `b = c` (debt equal to GDP), the terminal
term is `E_t[β^T (c_{t+T}/c_t)^{−γ} c_{t+T}] = (β mom(1−γ))^T c_t`, for `t + T ≤ H`. -/
theorem terminal_c (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) (β γ : ℝ) {t T : ℕ} (hT : t + T ≤ H) :
    𝔼.E t (fun ω => pvDisc β γ c t T ω * c (t + T) ω) =
      fun ω => (β * mom (1 - γ)) ^ T * c t ω := by
  have hct : 𝔼.E t (c t) = c t := by
    have h := hkp t 1
    simp only [Real.rpow_one] at h
    exact h
  have h : (fun ω => pvDisc β γ c t T ω * c (t + T) ω) =
      β ^ T • fun ω => ratio c t T ω ^ (1 - γ) * c t ω := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, smul_eq_mul]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos hpos t T ω),
      Real.rpow_one, ratio]
    field_simp [(hpos t ω).ne']
  rw [h, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid hct (1 - γ) T hT]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), (6.17) p. 207: each term of the present value of the surpluses
`s_{t+j+1} = R c_{t+j} − c_{t+j+1}` is `E_t[β^{j+1} (c_{t+j+1}/c_t)^{−γ} s_{t+j+1}] =
q^j (1 − q) c_t`, `q = β mom(1−γ)`, for `t + j + 1 ≤ H`. -/
theorem pv_term_c (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {s : ℕ → Ω → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) {t j : ℕ}
    (hj : t + j + 1 ≤ H) :
    𝔼.E t (fun ω => pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
      fun ω => (β * mom (1 - γ)) ^ j * (1 - β * mom (1 - γ)) * c t ω := by
  have hca : 𝔼.Adapted c := fun u => by
    have h := hkp u 1
    simp only [Real.rpow_one] at h
    exact h
  have hfun : (fun ω => pvDisc β γ c t (j + 1) ω * s (t + j + 1) ω) =
      (fun ω => pvDisc β γ c t (j + 1) ω * (R * c (t + j) ω)) -
        fun ω => pvDisc β γ c t (j + 1) ω * c (t + (j + 1)) ω := by
    funext ω
    simp only [Pi.sub_apply]
    rw [hs (t + j) ω, ← add_assoc]
    ring
  rw [hfun, map_sub, rollover_step 𝔼 hpo hpos hkp hiid hR hca (by omega),
    terminal_c 𝔼 hpo hpos hkp hiid β γ (by omega),
    terminal_c 𝔼 hpo hpos hkp hiid β γ (by omega)]
  funext ω
  simp only [Pi.sub_apply, pow_succ]
  ring

/-- Cochrane (2023), (6.17) p. 207 ("the last term converges to zero, via the transversality
condition", made precise): the terminal term `(β mom(1−γ))^T c_t` tends to zero iff
`β mom(1−γ) < 1` (for `β mom(1−γ) ≥ 0` and `c_t > 0`). -/
theorem terminal_tendsto_iff {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) :
    Tendsto (fun T : ℕ => q ^ T * x) atTop (𝓝 0) ↔ q < 1 := by
  constructor
  · intro h
    have h2 : Tendsto (fun T : ℕ => q ^ T) atTop (𝓝 0) := by
      have := h.mul_const x⁻¹
      simp only [zero_mul] at this
      refine this.congr fun T => ?_
      field_simp
    rw [tendsto_pow_atTop_nhds_zero_iff, abs_of_nonneg hq] at h2
    exact h2
  · intro h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq h).mul_const x

/-- **(6.15) for Bohn's example**, Cochrane (2023), (6.17) p. 207, infinite horizon: with i.i.d.
growth at every date, debt equal to consumption, rolled over at the risk-free rate, equals the
infinite SDF present value of its surpluses, `Σ_{j≥1} E_t[β^j (c_{t+j}/c_t)^{−γ} s_{t+j}] = c_t`,
iff `β E[G^{1−γ}] < 1` (given `β E[G^{1−γ}] ≥ 0`). -/
theorem bohn_pv_hasSum_iff (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ}
    (hiid : ∀ H, IIDGrowth 𝔼 c mom H) {β γ R : ℝ} (hR : β * mom (-γ) * R = 1)
    {s : ℕ → Ω → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω)
    (hq0 : 0 ≤ β * mom (1 - γ)) (t : ℕ) (ω : Ω) :
    HasSum (fun j => 𝔼.E t (fun ω' => pvDisc β γ c t (j + 1) ω' * s (t + j + 1) ω') ω)
      (c t ω) ↔ β * mom (1 - γ) < 1 := by
  set q := β * mom (1 - γ) with hq
  have hterm : (fun j => 𝔼.E t (fun ω' => pvDisc β γ c t (j + 1) ω' * s (t + j + 1) ω') ω) =
      fun j => q ^ j * (1 - q) * c t ω := by
    funext j
    rw [pv_term_c 𝔼 hpo hpos hkp (hiid (t + j + 1)) hR hs le_rfl]
  have hc := hpos t ω
  rw [hterm]
  constructor
  · intro h
    by_contra hq1
    push Not at hq1
    rcases hq1.eq_or_lt with h1 | h1
    · have h0 : HasSum (fun j : ℕ => q ^ j * (1 - q) * c t ω) 0 := by
        rw [← h1]; simp
      have := h.unique h0
      linarith
    · have hlim := h.summable.tendsto_atTop_zero
      have hle : ∀ j : ℕ, q ^ j * (1 - q) * c t ω ≤ (1 - q) * c t ω := fun j => by
        have hp : 1 ≤ q ^ j := one_le_pow₀ h1.le
        have hneg : (1 - q) * c t ω < 0 := mul_neg_of_neg_of_pos (by linarith) hc
        nlinarith
      have := le_of_tendsto' hlim hle
      nlinarith
  · intro hq1
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_right ((1 - q) * c t ω)
    have hval : (1 - q)⁻¹ * ((1 - q) * c t ω) = c t ω := by
      field_simp [(by linarith : (1 - q) ≠ 0)]
    rw [hval] at hg
    refine hg.congr_fun ?_
    intro j
    ring

/-! ### (6.18): discounting at the risk-free rate -/

/-- Cochrane (2023), p. 207: for the rollover surpluses the ex-post return on debt is the
risk-free rate, `(c_{u+1} + s_{u+1})/c_u = R`. -/
theorem bohn_grossReturn {c s : ℕ → Ω → ℝ} {R : ℝ} (hpos : ∀ t ω, 0 < c t ω)
    (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) (u : ℕ) (ω : Ω) :
    ReturnDiscounting.grossReturn c s u ω = R := by
  rw [ReturnDiscounting.grossReturn, hs u ω]
  field_simp [(hpos u ω).ne']
  ring

/-- **(6.18), pathwise**, Cochrane (2023), p. 207: discounting at the risk-free rate,
`c_t = Σ_{j=1}^T R^{−j} s_{t+j} + R^{−T} c_{t+T}`, and the present-value term equals
`c_t − R^{−T} c_{t+T}`. -/
theorem eq_6_18_pathwise {c s : ℕ → Ω → ℝ} {R : ℝ} (hR : R ≠ 0) (hpos : ∀ t ω, 0 < c t ω)
    (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) (t T : ℕ) (ω : Ω) :
    c t ω = (∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) +
        (R⁻¹) ^ T * c (t + T) ω ∧
      (∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
        c t ω - (R⁻¹) ^ T * c (t + T) ω := by
  have hdisc : ∀ j, ReturnDiscounting.returnDiscount c s t j ω = (R⁻¹) ^ j := fun j => by
    unfold ReturnDiscounting.returnDiscount
    simp [bohn_grossReturn hpos hs]
  have hpd : ∀ u ω', c (u + 1) ω' + s (u + 1) ω' ≠ 0 := fun u ω' => by
    rw [hs u ω']
    have := mul_ne_zero hR (hpos u ω').ne'
    intro h; apply this; linarith
  have h := ReturnDiscounting.eq_6_14_pathwise hpd t ω T
  simp only [ReturnDiscounting.returnPV, hdisc] at h
  exact ⟨h, by linarith⟩

/-- **(6.18)**, Cochrane (2023), p. 207: taking expectations with i.i.d. growth, the
return-discounted present value is `E_t[PV_T] = c_t (1 − (E[G]/R)^T)` and the terminal term
is `E_t[R^{−T} c_{t+T}] = c_t (E[G]/R)^T`, for `t + T ≤ H`. -/
theorem eq_6_18 (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {c : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < c t ω) (hkp : KnownPowers 𝔼 c) {mom : ℝ → ℝ} {H : ℕ}
    (hiid : IIDGrowth 𝔼 c mom H) {R : ℝ} (hR : R ≠ 0) {s : ℕ → Ω → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * c u ω - c (u + 1) ω) {t T : ℕ} (hT : t + T ≤ H) :
    𝔼.E t (fun ω => (R⁻¹) ^ T * c (t + T) ω) = (fun ω => c t ω * (mom 1 / R) ^ T) ∧
      𝔼.E t (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
        fun ω => c t ω * (1 - (mom 1 / R) ^ T) := by
  have hct : 𝔼.E t (c t) = c t := by
    have h := hkp t 1
    simp only [Real.rpow_one] at h
    exact h
  have hterm : 𝔼.E t (fun ω => (R⁻¹) ^ T * c (t + T) ω) =
      fun ω => c t ω * (mom 1 / R) ^ T := by
    have h : (fun ω => (R⁻¹) ^ T * c (t + T) ω) =
        (R⁻¹) ^ T • fun ω => ratio c t T ω ^ (1 : ℝ) * c t ω := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, Real.rpow_one, ratio]
      field_simp [(hpos t ω).ne']
    rw [h, 𝔼.E_smul, E_ratio_pow_mul 𝔼 hpo hpos hkp hiid hct 1 T hT]
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, div_pow, inv_pow]
    field_simp
  refine ⟨hterm, ?_⟩
  have hfun : (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
      c t - fun ω => (R⁻¹) ^ T * c (t + T) ω := by
    funext ω
    rw [Pi.sub_apply, (eq_6_18_pathwise hR hpos hs t T ω).2]
  rw [hfun, map_sub, hct, hterm]
  funext ω
  simp only [Pi.sub_apply]
  ring

/-- Cochrane (2023), p. 207 ("with `r < g` the present value of cashflows term builds to
negative infinity, and the terminal value builds to positive infinity"): if
`0 < R < E[G]` and `c_t > 0` then `c_t (1 − (E[G]/R)^T) → −∞` and `c_t (E[G]/R)^T → +∞`. -/
theorem eq_6_18_diverges {R m x : ℝ} (hR : 0 < R) (hRm : R < m) (hx : 0 < x) :
    Tendsto (fun T : ℕ => x * (1 - (m / R) ^ T)) atTop atBot ∧
      Tendsto (fun T : ℕ => x * (m / R) ^ T) atTop atTop := by
  have h1 : 1 < m / R := by rw [lt_div_iff₀ hR]; linarith
  have hpow : Tendsto (fun T : ℕ => (m / R) ^ T) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h1
  have hterm : Tendsto (fun T : ℕ => x * (m / R) ^ T) atTop atTop :=
    hpow.const_mul_atTop hx
  refine ⟨?_, hterm⟩
  have heq : (fun T : ℕ => x * (1 - (m / R) ^ T)) = fun T => x - x * (m / R) ^ T := by
    funext T; ring
  rw [heq]
  exact tendsto_atBot_add_const_left _ x (tendsto_neg_atTop_atBot.comp hterm)

/-! ### The two-state witness -/

/-- Cochrane (2023), p. 206 (Bohn's example, two-state version): the date-`t` observation of a
sequence of `H` coin flips — the flips `0, …, t − 1` are revealed by date `t`. -/
def coinObsH (H t : ℕ) (ω : Fin H → Bool) : Fin H → Bool :=
  fun i => if (i : ℕ) < t then ω i else false

/-- Cochrane (2023), p. 206: two states `ω ~_t ω'` share the first `t` flips. -/
theorem coinObsH_eq_iff {H t : ℕ} {ω ω' : Fin H → Bool} :
    coinObsH H t ω = coinObsH H t ω' ↔ ∀ i : Fin H, (i : ℕ) < t → ω i = ω' i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [coinObsH, hi] using this
  · intro h
    funext i
    unfold coinObsH
    split_ifs with hi
    · exact h i hi
    · rfl

/-- Cochrane (2023), p. 206: the i.i.d. fair coin tree with horizon `H`: uniform probability on
`Fin H → Bool`, flip `i` revealed at date `i + 1`. -/
noncomputable def bohnTree (H : ℕ) : ExpectationsFiniteTree.FiniteTree (Fin H → Bool) where
  prob := fun _ => (1 / 2) ^ H
  prob_pos := fun _ => by positivity
  prob_sum := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]; norm_num
  info := fun t => Setoid.ker (coinObsH H t)
  refines := by
    intro s t hst a b h
    rw [Setoid.ker_def, coinObsH_eq_iff] at h ⊢
    exact fun i hi => h i (lt_of_lt_of_le hi hst)

/-- Cochrane (2023), p. 206: the expectation system of the coin tree. -/
noncomputable def bohnSystem (H : ℕ) : ExpectationSystem (Fin H → Bool) :=
  (bohnTree H).toExpectationSystem

/-- Cochrane (2023), p. 206: the coin tree has the pull-out property. -/
theorem bohnSystem_pullOut (H : ℕ) : (bohnSystem H).PullOut :=
  ExpectationsFiniteTree.finiteTree_pullOut (bohnTree H)

/-- Cochrane (2023), p. 206: flipping coin `i₀` (not yet revealed at `t`, since `t ≤ i₀`)
preserves the date-`t` information cell. -/
theorem info_flip {H t : ℕ} {i₀ : Fin H} (hi : t ≤ (i₀ : ℕ)) (ω ω' : Fin H → Bool) :
    (bohnTree H).info t (Function.update ω' i₀ (!ω' i₀)) ω ↔ (bohnTree H).info t ω' ω := by
  change Setoid.ker _ _ _ ↔ Setoid.ker _ _ _
  rw [Setoid.ker_def, Setoid.ker_def, coinObsH_eq_iff, coinObsH_eq_iff]
  have hu : ∀ i : Fin H, (i : ℕ) < t → Function.update ω' i₀ (!ω' i₀) i = ω' i := by
    intro i hit
    rw [Function.update_of_ne]
    intro h; rw [h] at hit; omega
  constructor
  · intro h i hit; rw [← hu i hit]; exact h i hit
  · intro h i hit; rw [hu i hit]; exact h i hit

/-- Cochrane (2023), p. 206: in the coin tree, a function of the not-yet-revealed coin
`i₀ ≥ t` has date-`t` expectation `(f true + f false)/2` — the coin is fair and independent
of the past. -/
theorem bohnTree_condE_coin {H t : ℕ} {i₀ : Fin H} (hi : t ≤ (i₀ : ℕ)) (f : Bool → ℝ)
    (ω : Fin H → Bool) :
    (bohnTree H).condE t (fun ω' => f (ω' i₀)) ω = (f true + f false) / 2 := by
  classical
  set T := bohnTree H with hT
  let flip : Equiv.Perm (Fin H → Bool) :=
    Function.Involutive.toPerm (fun ω' => Function.update ω' i₀ (!ω' i₀)) (fun ω' => by
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h])
  have hflip : ∀ ω', flip ω' = Function.update ω' i₀ (!ω' i₀) := fun _ => rfl
  have hprob : ∀ ω', T.prob ω' = (1 / 2) ^ H := fun _ => rfl
  have hnum : T.num t (fun ω' => f (ω' i₀)) ω =
      ∑ ω', if T.info t ω' ω then T.prob ω' * f (!ω' i₀) else 0 := by
    unfold ExpectationsFiniteTree.FiniteTree.num
    rw [← Equiv.sum_comp flip]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    rw [hflip, info_flip hi, hprob, hprob]
    simp
  have h2 : 2 * T.num t (fun ω' => f (ω' i₀)) ω = (f true + f false) * T.mass t ω := by
    have hn1 : T.num t (fun ω' => f (ω' i₀)) ω =
        ∑ ω', if T.info t ω' ω then T.prob ω' * f (ω' i₀) else 0 := rfl
    rw [two_mul]
    nth_rewrite 1 [hn1]
    rw [hnum, ← Finset.sum_add_distrib]
    unfold ExpectationsFiniteTree.FiniteTree.mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    by_cases h : T.info t ω' ω
    · simp only [h, ↓reduceIte]
      cases ω' i₀ <;> simp <;> ring
    · simp [h]
  unfold ExpectationsFiniteTree.FiniteTree.condE
  have hm := T.mass_pos t ω
  field_simp
  linarith

/-- Cochrane (2023), p. 206: the two growth states, `G = 5/4` (heads) or `G = 17/20`
(tails). -/
noncomputable def bohnGrowth (b : Bool) : ℝ := if b then 5 / 4 else 17 / 20

/-- Cochrane (2023), p. 206: two-state growth is positive. -/
theorem bohnGrowth_pos (b : Bool) : 0 < bohnGrowth b := by
  cases b <;> norm_num [bohnGrowth]

/-- Cochrane (2023), p. 206: consumption in the coin tree, `c_t = Π_{i < t} G(ω_i)` with
`c_0 = 1`. -/
noncomputable def bohnC (H t : ℕ) (ω : Fin H → Bool) : ℝ :=
  ∏ i : Fin H, if (i : ℕ) < t then bohnGrowth (ω i) else 1

/-- Cochrane (2023), p. 206: consumption is positive. -/
theorem bohnC_pos (H t : ℕ) (ω : Fin H → Bool) : 0 < bohnC H t ω := by
  unfold bohnC
  refine Finset.prod_pos fun i _ => ?_
  split_ifs
  · exact bohnGrowth_pos _
  · exact one_pos

/-- Cochrane (2023), p. 206: before the horizon, consumption growth is the coin's growth,
`c_{t+1}/c_t = G(ω_t)`. -/
theorem bohnC_growth {H t : ℕ} (ht : t < H) (ω : Fin H → Bool) :
    growth (bohnC H) t ω = bohnGrowth (ω ⟨t, ht⟩) := by
  unfold growth
  rw [div_eq_iff (bohnC_pos H t ω).ne']
  have hG : (∏ i : Fin H, if (⟨t, ht⟩ : Fin H) = i then bohnGrowth (ω i) else 1) =
      bohnGrowth (ω ⟨t, ht⟩) := by
    rw [Finset.prod_ite_eq]; simp
  unfold bohnC
  rw [mul_comm, ← hG, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h1 : (i : ℕ) < t
  · have hne : (⟨t, ht⟩ : Fin H) ≠ i := fun h => by rw [← h] at h1; exact lt_irrefl _ h1
    simp [h1, Nat.lt_succ_of_lt h1, hne]
  · by_cases h2 : (i : ℕ) = t
    · have heq : (⟨t, ht⟩ : Fin H) = i := Fin.ext h2.symm
      simp [h2, heq]
    · have h3 : ¬ (i : ℕ) < t + 1 := by omega
      have hne : (⟨t, ht⟩ : Fin H) ≠ i := fun h => h2 (by rw [← h])
      simp [h1, h3, hne]

/-- Cochrane (2023), p. 206: powers of consumption are known in the coin tree. -/
theorem bohnSystem_knownPowers (H : ℕ) : KnownPowers (bohnSystem H) (bohnC H) := by
  intro t a
  funext ω
  change (bohnTree H).condE t _ ω = _
  refine (bohnTree H).condE_of_const_on_cell fun ω' h => ?_
  change Setoid.ker _ _ _ at h
  rw [Setoid.ker_def, coinObsH_eq_iff] at h
  have : bohnC H t ω' = bohnC H t ω := by
    unfold bohnC
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [h i hi]
    · rfl
  rw [this]

/-- Cochrane (2023), p. 206: the moments of two-state growth,
`E[G^a] = ((5/4)^a + (17/20)^a)/2`. -/
noncomputable def bohnMom (a : ℝ) : ℝ := (bohnGrowth true ^ a + bohnGrowth false ^ a) / 2

/-- Cochrane (2023), p. 206: the coin tree has i.i.d. growth before its horizon, with moments
`bohnMom`. -/
theorem bohnSystem_iid (H : ℕ) : IIDGrowth (bohnSystem H) (bohnC H) bohnMom H := by
  intro t ht a
  funext ω
  have hfun : (fun ω' => growth (bohnC H) t ω' ^ a) =
      fun ω' => (fun b => bohnGrowth b ^ a) (ω' ⟨t, ht⟩) := by
    funext ω'; rw [bohnC_growth ht]
  change (bohnTree H).condE t _ ω = _
  rw [hfun]
  exact bohnTree_condE_coin (i₀ := ⟨t, ht⟩) (le_refl t) (fun b => bohnGrowth b ^ a) ω

/-- Cochrane (2023), p. 206: the two-state numbers (all exact): `E[G] = 21/20`,
`E[G^{−1}] = 84/85`, `E[G^{−2}] = 7312/7225`. -/
theorem bohnMom_values :
    bohnMom 1 = 21 / 20 ∧ bohnMom (-1) = 84 / 85 ∧ bohnMom (-2) = 7312 / 7225 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bohnMom, bohnGrowth]; norm_num
  · simp only [bohnMom, bohnGrowth, ↓reduceIte, Bool.false_eq_true, Real.rpow_neg_one]
    norm_num
  · simp only [bohnMom, bohnGrowth, ↓reduceIte, Bool.false_eq_true]
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_two,
      Real.rpow_two]
    norm_num

/-- Cochrane (2023), pp. 205–207 (Theorem B, two-state witness): with `β = 49/50`, `γ = 2`
and `G ∈ {17/20, 5/4}` equally likely, the risk-free rate `1 + r_f = 361250/358288 ≈ 1.0083`
is below mean growth `E[G] = 1.05` (`r_f < g`), while `β E[G^{1−γ}] = 4116/4250 ≈ 0.968 < 1`
(the correct present value converges), so the incorrect present value explodes:
`β E[G^{−γ}] E[G] > 1`. -/
theorem bohn_numbers :
    riskFreeGross (49 / 50) 2 bohnMom = 361250 / 358288 ∧
      riskFreeGross (49 / 50) 2 bohnMom < bohnMom 1 ∧
      (49 / 50 : ℝ) * bohnMom (1 - 2) = 4116 / 4250 ∧
      (49 / 50 : ℝ) * bohnMom (1 - 2) < 1 ∧
      1 < (49 / 50 : ℝ) * bohnMom (-2) * bohnMom 1 := by
  obtain ⟨h1, hm1, hm2⟩ := bohnMom_values
  have hR : riskFreeGross (49 / 50) 2 bohnMom = 361250 / 358288 := by
    rw [riskFreeGross, hm2]; norm_num
  have hq : (49 / 50 : ℝ) * bohnMom (1 - 2) = 4116 / 4250 := by
    rw [show (1 : ℝ) - 2 = -1 by norm_num, hm1]; norm_num
  refine ⟨hR, ?_, hq, ?_, ?_⟩
  · rw [hR, h1]; norm_num
  · rw [hq]; norm_num
  · rw [hm2, h1]; norm_num

/-- Cochrane (2023), (6.17) p. 207, two-state witness: in the coin tree of any horizon
`H ≥ T`, for debt `b = c` rolled over at the risk-free rate `R`, (6.17) holds at date 0
with genuine uncertainty, and the terminal term is `(4116/4250)^T` (`c_0 = 1`), which tends to
zero as `T → ∞`. -/
theorem bohn_witness_6_17 {H T : ℕ} (hT : T ≤ H) {s : ℕ → (Fin H → Bool) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * bohnC H u ω - bohnC H (u + 1) ω) :
    bohnC H 0 = (bohnSystem H).E 0 (fun ω => ∑ j ∈ Finset.range T,
        pvDisc (49 / 50) 2 (bohnC H) 0 (j + 1) ω * s (0 + j + 1) ω) +
      (bohnSystem H).E 0 (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 T ω * bohnC H (0 + T) ω) ∧
    (bohnSystem H).E 0 (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 T ω * bohnC H (0 + T) ω) =
      (fun _ => (4116 / 4250 : ℝ) ^ T) ∧
    Tendsto (fun T : ℕ => (4116 / 4250 : ℝ) ^ T) atTop (𝓝 0) := by
  have hR : (49 / 50 : ℝ) * bohnMom (-2) * riskFreeGross (49 / 50) 2 bohnMom = 1 := by
    rw [riskFreeGross, bohnMom_values.2.2]
    norm_num
  have hca : (bohnSystem H).Adapted (bohnC H) := fun u => by
    have h := bohnSystem_knownPowers H u 1
    simp only [Real.rpow_one] at h
    exact h
  have hc0 : ∀ ω, bohnC H 0 ω = 1 := fun ω => by simp [bohnC]
  refine ⟨eq_6_17 (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) hR hca hs 0 T (by omega), ?_, ?_⟩
  · rw [terminal_c (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) _ _ (by omega)]
    funext ω
    rw [hc0, mul_one, bohn_numbers.2.2.1]
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Cochrane (2023), (6.18) p. 207, two-state witness: in the coin tree of any horizon
`H ≥ T`, discounting at the risk-free rate `R = 361250/358288`, the expected present value of
the rollover surpluses is `1 − ((21/20)/R)^T` and the expected terminal term is
`((21/20)/R)^T`; since `R < 21/20` (`r_f < g`) these tend to `−∞` and `+∞`. -/
theorem bohn_witness_6_18 {H T : ℕ} (hT : T ≤ H) {s : ℕ → (Fin H → Bool) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * bohnC H u ω - bohnC H (u + 1) ω) :
    (bohnSystem H).E 0 (fun ω => ∑ j ∈ Finset.range T,
        (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ (j + 1) * s (0 + j + 1) ω) =
      (fun _ => 1 - ((21 / 20) / (361250 / 358288)) ^ T) ∧
    (bohnSystem H).E 0 (fun ω => (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ T * bohnC H (0 + T) ω) =
      (fun _ => ((21 / 20) / (361250 / 358288)) ^ T) ∧
    Tendsto (fun T : ℕ => 1 * (1 - ((21 / 20 : ℝ) / (361250 / 358288)) ^ T)) atTop atBot ∧
    Tendsto (fun T : ℕ => 1 * ((21 / 20 : ℝ) / (361250 / 358288)) ^ T) atTop atTop := by
  obtain ⟨hR, hRm, -, -, -⟩ := bohn_numbers
  have hR0 : riskFreeGross (49 / 50) 2 bohnMom ≠ 0 := by rw [hR]; norm_num
  have hc0 : ∀ ω, bohnC H 0 ω = 1 := fun ω => by simp [bohnC]
  obtain ⟨h1, h2⟩ := eq_6_18 (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
    (bohnSystem_knownPowers H) (bohnSystem_iid H) hR0 hs (t := 0) (T := T) (by omega)
  have hm1 : bohnMom 1 = 21 / 20 := bohnMom_values.1
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; funext ω; rw [hc0, hm1, hR, one_mul]
  · rw [h1]; funext ω; rw [hc0, hm1, hR, one_mul]
  · exact eq_6_18_diverges (by norm_num) (by norm_num) one_pos

/-- Cochrane (2023), (6.15)–(6.16) pp. 205–206, two-state witness: in the coin tree of any
horizon `H ≥ j`, the `j`-th correct summand (constant surplus ratio `κ`) is
`(4116/4250)^j κ`, while the `j`-th summand with the expectation inside is `ρ^j κ` with
`ρ = β E[G^{−2}] E[G] > 1`: the correct terms shrink geometrically, the incorrect ones grow. -/
theorem bohn_witness_terms {H j : ℕ} (hj : j ≤ H) (κ : ℝ) (ω : Fin H → Bool) :
    (bohnSystem H).E 0 (pvTerm (49 / 50) 2 κ (bohnC H) 0 j) ω = (4116 / 4250) ^ j * κ ∧
      (bohnSystem H).E 0 (fun ω' => (49 / 50) ^ j * ratio (bohnC H) 0 j ω' ^ (-2 : ℝ)) ω *
          (bohnSystem H).E 0 (ratio (bohnC H) 0 j) ω * κ =
        ((49 / 50) * (7312 / 7225) * (21 / 20)) ^ j * κ ∧
      1 < (49 / 50 : ℝ) * (7312 / 7225) * (21 / 20) := by
  obtain ⟨hm1, -, hm2⟩ := bohnMom_values
  refine ⟨?_, ?_, by norm_num⟩
  · rw [correct_term (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) _ _ κ (by omega), bohn_numbers.2.2.1]
  · rw [incorrect_term (bohnSystem H) (bohnSystem_pullOut H) (bohnC_pos H)
      (bohnSystem_knownPowers H) (bohnSystem_iid H) _ _ κ (by omega), hm1, hm2]

end Cochrane.FiscalConstraints.AggregateUncertainty
