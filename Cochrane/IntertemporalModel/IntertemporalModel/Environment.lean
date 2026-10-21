/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.ExpectationTools
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The intertemporal model: environment

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–23,
equations (2.1)–(2.5), and the proportional-tax remark on p. 23.

## Timing convention

The book's debt `B_t` is sold at the end of date `t` and matures at the start of `t + 1`; the
economy starts with `B_{−1}`. To index by natural numbers we write `Bm t` for the debt *maturing*
at date `t`, i.e. `Bm t = B_{t−1}` (so the book's `B_t` is `Bm (t + 1)`), and likewise
`Mm t = M_{t−1}` for money held overnight into date `t`. Random variables are `Ω → ℝ`, processes
`ℕ → Ω → ℝ`, and `E_t` is an arbitrary `ExpectationSystem`.

## Main results

* `GovFlow` (2.1), `HhFlow` (2.2); `hhFlow_iff_govFlow`: with goods-market clearing `c = y` the
  household flow constraint is exactly the government's (the "mirror image", p. 21).
* `HhOptimal`, `euler_of_optimal`: under perfect foresight an optimal household plan with
  positive bond holdings satisfies the nominal Euler equation (a variational proof);
  `bondPrice_of_optimal` gives (2.3) at `c = y`.
* `EulerNominal`, `EulerReal` (the first-order conditions behind (2.3)); `realBondPrice_of_euler`
  (`R = 1/β`), `bondPrice_of_euler` and `bondPrice_iff_euler` ((2.3), both directions, with
  constant marginal utility `u'(y)`), `bondPrice_eq_inv_one_add_rate` (`Q = 1/(1+i)`).
* Money demand (p. 22): `money_dominated` (with `i_t > 0` money held overnight is strictly
  dominated by bonds), `bonds_dominated_of_neg_rate` (with `i_t < 0` bonds are strictly dominated
  by money, so the government cannot sell debt: the rate cannot be negative),
  `perfect_substitutes` (with `i_t = 0` only `M + B` matters).
* `flow_of_govFlow` and `govFlow_merge`: eliminating money gives (2.4).
* `flow_real_25`, `flow_real_x`, `flow_iff_real_x`: (2.5), and its form
  `x_t = s_t + β E_t x_{t+1}` for real debt `x_t = B_{t−1}/P_t`.
* `propTax_real_surplus`, `propTax_surplus_indep_price`: proportional taxes keep the real
  surplus, hence the right-hand side of (2.7), free of the price level (p. 23).

The hypothesis `FunctionsKnown` (functions of known variables are known), used to show that the
equilibrium price level is adapted, lives in `ExpectationTools`.
-/

namespace Cochrane.IntertemporalModel.Environment

open Filter Topology

variable {Ω : Type*}

/-! ### Budget constraints (2.1), (2.2) -/

/-- Cochrane (2023), eq. (2.1), p. 21: the government flow budget constraint
`M_{t−1} + B_{t−1} = P_t s_t + M_t + Q_t B_t`, at every date and state, written with
`Mm t = M_{t−1}`, `Bm t = B_{t−1}`. -/
def GovFlow (Mm Bm P s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Mm t ω + Bm t ω = P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω

/-- Cochrane (2023), eq. (2.2), p. 21: the household flow budget constraint
`M_{t−1} + B_{t−1} + P_t y = P_t c_t + P_t s_t + M_t + Q_t B_t` with constant endowment `y`. -/
def HhFlow (y : ℝ) (Mm Bm P c s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Mm t ω + Bm t ω + P t ω * y =
    P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω

/-- Cochrane (2023), p. 21: with goods-market clearing `c_t = y` the household flow constraint
(2.2) is exactly the government flow constraint (2.1) ("almost the mirror of (2.1)"). -/
theorem hhFlow_iff_govFlow {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} (hc : ∀ t ω, c t ω = y) :
    HhFlow y Mm Bm P c s Q ↔ GovFlow Mm Bm P s Q := by
  constructor
  · intro h t ω
    have := h t ω
    rw [hc t ω] at this
    linarith
  · intro h t ω
    have := h t ω
    rw [hc t ω]
    linarith

/-- Cochrane (2023), pp. 21 and 23: the household and government flow constraints at the same
prices and policies differ exactly by the excess demand for goods,
`(2.2) − (2.1)`: household slack `= P_t (y − c_t) +` government slack. -/
theorem hhFlow_sub_govFlow (y : ℝ) (Mm Bm P c s Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (Mm t ω + Bm t ω + P t ω * y -
        (P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)) =
      P t ω * (y - c t ω) +
        (Mm t ω + Bm t ω - (P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)) := by
  ring

/-! ### Household optimisation under perfect foresight: the Euler equation -/

/-- Cochrane (2023), eq. (2.2), p. 21, under perfect foresight with no money held: a household
plan `(c, b)` (`b n = B_{n−1}`) is feasible from initial debt `b₀` if it satisfies the flow
constraint `b_n + P_n y = P_n c_n + P_n s_n + Q_n b_{n+1}` at every date and `B ≥ 0`. -/
def HhFeasible (y : ℝ) (P s Q : ℕ → ℝ) (b₀ : ℝ) (c b : ℕ → ℝ) : Prop :=
  b 0 = b₀ ∧ (∀ n, b n + P n * y = P n * c n + P n * s n + Q n * b (n + 1)) ∧ ∀ n, 0 ≤ b n

/-- Cochrane (2023), p. 21, "A representative household maximizes `∑ β^t u(c_t)`": a feasible
plan with summable discounted utility that no feasible plan with summable discounted utility
beats. -/
def HhOptimal (β y : ℝ) (u : ℝ → ℝ) (P s Q : ℕ → ℝ) (b₀ : ℝ) (c b : ℕ → ℝ) : Prop :=
  HhFeasible y P s Q b₀ c b ∧ Summable (fun n => β ^ n * u (c n)) ∧
    ∀ c' b', HhFeasible y P s Q b₀ c' b' → Summable (fun n => β ^ n * u (c' n)) →
      ∑' n, β ^ n * u (c' n) ≤ ∑' n, β ^ n * u (c n)

/-- Cochrane (2023), p. 21, "The consumer's first-order conditions", derived (perfect foresight):
if `(c, b)` is optimal, `u` is differentiable at `c_t` and `c_{t+1}` with derivatives `d₀, d₁`,
prices are positive, `Q_t > 0` and the household holds bonds `B_t > 0`, then shifting `ε` dollars
between consumption at `t` and bonds maturing at `t + 1` cannot raise utility, which gives the
nominal Euler equation `Q_t u'(c_t)/P_t = β u'(c_{t+1})/P_{t+1}`. -/
theorem euler_of_optimal {β y b₀ d₀ d₁ : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {P s Q c b : ℕ → ℝ}
    (hopt : HhOptimal β y u P s Q b₀ c b) {t : ℕ} (hPt : 0 < P t) (hPt1 : 0 < P (t + 1))
    (hQ : 0 < Q t) (hb : 0 < b (t + 1)) (hu0 : HasDerivAt u d₀ (c t))
    (hu1 : HasDerivAt u d₁ (c (t + 1))) :
    Q t * (d₀ / P t) = β * (d₁ / P (t + 1)) := by
  obtain ⟨⟨hb0, hflow, hbnn⟩, hsum, hbest⟩ := hopt
  -- the perturbed plans
  let cε : ℝ → ℕ → ℝ := fun ε n =>
    c n + (if n = t then ε / P t else if n = t + 1 then -(ε / (Q t * P (t + 1))) else 0)
  let bε : ℝ → ℕ → ℝ := fun ε n => b n - (if n = t + 1 then ε / Q t else 0)
  let φ : ℝ → ℝ := fun ε => β ^ t * (u (c t + ε / P t) - u (c t)) +
    β ^ (t + 1) * (u (c (t + 1) - ε / (Q t * P (t + 1))) - u (c (t + 1)))
  have hQ0 := hQ.ne'
  have hP0 := hPt.ne'
  have hP1 := hPt1.ne'
  have hfeas : ∀ ε, |ε| < Q t * b (t + 1) → HhFeasible y P s Q b₀ (cε ε) (bε ε) := by
    intro ε hε
    refine ⟨by simp [bε, hb0], fun n => ?_, fun n => ?_⟩
    · by_cases hn : n = t
      · subst hn
        simp only [cε, bε, ↓reduceIte, (show ¬ (n = n + 1) by omega)]
        have := hflow n
        field_simp
        linarith
      · by_cases hn1 : n = t + 1
        · subst hn1
          have := hflow (t + 1)
          simp only [cε, bε, ↓reduceIte, hn, (show ¬ (t + 1 + 1 = t + 1) by omega)]
          field_simp
          linear_combination (Q t) * this
        · have hn2 : n + 1 ≠ t + 1 := fun h => hn (by omega)
          simp only [cε, bε, hn, hn1, hn2, ↓reduceIte, add_zero, sub_zero]
          exact hflow n
    · simp only [bε]
      split_ifs with hn
      · subst hn
        have h1 : ε / Q t ≤ b (t + 1) := by
          rw [div_le_iff₀ hQ]
          linarith [le_abs_self ε, mul_comm (Q t) (b (t + 1))]
        linarith
      · simpa using hbnn n
  -- utility of the perturbed plan
  have hdiff : ∀ ε, HasSum (fun n => β ^ n * u (cε ε n)) (∑' n, β ^ n * u (c n) + φ ε) := by
    intro ε
    have hg : HasSum (fun n => β ^ n * u (cε ε n) - β ^ n * u (c n)) (φ ε) := by
      have h : HasSum (fun n => β ^ n * u (cε ε n) - β ^ n * u (c n))
          (∑ n ∈ ({t, t + 1} : Finset ℕ), (β ^ n * u (cε ε n) - β ^ n * u (c n))) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          simp [cε, hn.1, hn.2])
      convert h using 1
      rw [Finset.sum_pair (by omega)]
      simp only [cε, φ, ↓reduceIte, (show ¬ (t + 1 = t) by omega)]
      ring_nf
    convert hsum.hasSum.add hg using 1
    · funext n
      ring
  have hle : ∀ ε, |ε| < Q t * b (t + 1) → φ ε ≤ 0 := by
    intro ε hε
    have h1 := hbest (cε ε) (bε ε) (hfeas ε hε) (hdiff ε).summable
    rw [(hdiff ε).tsum_eq] at h1
    linarith
  -- φ has a local maximum at 0
  have hmax : IsLocalMax φ 0 := by
    have hpos : 0 < Q t * b (t + 1) := mul_pos hQ hb
    have hmem : Set.Ioo (-(Q t * b (t + 1))) (Q t * b (t + 1)) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) hpos
    filter_upwards [hmem] with ε hε
    have : φ 0 = 0 := by simp [φ]
    rw [this]
    exact hle ε (abs_lt.mpr hε)
  -- the derivative of φ at 0
  have hf0 : HasDerivAt (fun ε => c t + ε / P t) (1 / P t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const (P t)).const_add (c t)
  have hf1 : HasDerivAt (fun ε => c (t + 1) - ε / (Q t * P (t + 1)))
      (-(1 / (Q t * P (t + 1)))) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const (Q t * P (t + 1))).const_sub (c (t + 1))
  have hu0' : HasDerivAt u d₀ ((fun ε => c t + ε / P t) 0) := by simpa using hu0
  have hu1' : HasDerivAt u d₁ ((fun ε => c (t + 1) - ε / (Q t * P (t + 1))) 0) := by
    simpa using hu1
  have hφ : HasDerivAt φ (β ^ t * (d₀ * (1 / P t)) +
      β ^ (t + 1) * (d₁ * (-(1 / (Q t * P (t + 1)))))) 0 := by
    have a := ((hu0'.comp 0 hf0).sub_const (u (c t))).const_mul (β ^ t)
    have b' := ((hu1'.comp 0 hf1).sub_const (u (c (t + 1)))).const_mul (β ^ (t + 1))
    exact a.add b'
  have hzero := hmax.hasDerivAt_eq_zero hφ
  have hbt : β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
  rw [pow_succ] at hzero
  field_simp at hzero
  have : β ^ t * (Q t * d₀ * P (t + 1) - β * d₁ * P t) = 0 := by linear_combination hzero
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hbt
  · field_simp
    linarith

/-- Cochrane (2023), eq. (2.3), p. 22, derived from optimisation (perfect foresight): if the
endowment plan `c = y` with bond holdings `B_t > 0` is optimal and `u'(y) > 0`, then
`Q_t = β P_t/P_{t+1}`. -/
theorem bondPrice_of_optimal {β y b₀ uy : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {P s Q b : ℕ → ℝ}
    (hopt : HhOptimal β y u P s Q b₀ (fun _ => y) b) {t : ℕ} (hPt : 0 < P t)
    (hPt1 : 0 < P (t + 1)) (hQ : 0 < Q t) (hb : 0 < b (t + 1)) (huy : 0 < uy)
    (hu : HasDerivAt u uy y) : Q t = β * (P t / P (t + 1)) := by
  have h := euler_of_optimal hβ hopt hPt hPt1 hQ hb hu hu
  have := hPt.ne'
  have := hPt1.ne'
  have h2 : uy * (Q t * P (t + 1) - β * P t) = 0 := by
    field_simp at h
    linear_combination uy * h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 huy.ne'
  · field_simp
    linarith

/-! ### First-order conditions and the bond price (2.3) -/

/-- Cochrane (2023), p. 21 ("the consumer's first-order conditions"): the Euler equation for the
nominal one-period bond, `Q_t u'(c_t)/P_t = β E_t[u'(c_{t+1})/P_{t+1}]`, with `lam t = u'(c_t)`. -/
def EulerNominal (𝔼 : ExpectationSystem Ω) (β : ℝ) (lam P Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Q t * (fun ω => lam t ω / P t ω) = β • 𝔼.E t (fun ω => lam (t + 1) ω / P (t + 1) ω)

/-- Cochrane (2023), p. 21: the Euler equation for a one-period real (indexed) bond with price
`q_t`, `q_t u'(c_t) = β E_t u'(c_{t+1})`; the gross real rate is `R_t = 1/q_t`. -/
def EulerReal (𝔼 : ExpectationSystem Ω) (β : ℝ) (lam q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, q t * lam t = β • 𝔼.E t (lam (t + 1))

/-- Cochrane (2023), p. 21: "equilibrium `c_t = y` then impl[ies] that the gross real interest rate
is `R = 1/β`": with constant positive marginal utility `u'(y)` the real bond price is `β`. -/
theorem realBondPrice_of_euler (𝔼 : ExpectationSystem Ω) {β uy : ℝ} (huy : 0 < uy)
    {lam q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy) (heu : EulerReal 𝔼 β lam q) (t : ℕ) :
    q t = fun _ => β := by
  have h := heu t
  rw [hlam t, hlam (t + 1), 𝔼.const] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at hω
  have : (q t ω - β) * uy = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 huy.ne'

/-- Cochrane (2023), p. 21: the gross real rate `R = 1/q` equals `1/β`. -/
theorem realRate_eq_inv_beta (𝔼 : ExpectationSystem Ω) {β uy : ℝ} (huy : 0 < uy)
    {lam q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy) (heu : EulerReal 𝔼 β lam q) (t : ℕ)
    (ω : Ω) : (q t ω)⁻¹ = β⁻¹ := by
  rw [realBondPrice_of_euler 𝔼 huy hlam heu t]

/-- Cochrane (2023), eq. (2.3), p. 22: with constant positive marginal utility `u'(y)`, a
positive price level known at `t`, and the pull-out property, the nominal Euler equation gives
`Q_t = β E_t(P_t/P_{t+1})`. -/
theorem bondPrice_of_euler (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β uy : ℝ}
    (huy : 0 < uy) {lam P Q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy)
    (hPpos : ∀ t ω, 0 < P t ω) (hPad : 𝔼.Adapted P) (heu : EulerNominal 𝔼 β lam P Q) (t : ℕ) :
    Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω) := by
  have h := heu t
  have hsplit : (fun ω => lam (t + 1) ω / P (t + 1) ω) =
      (fun _ => uy) * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; rw [hlam (t + 1)]; simp [div_eq_mul_inv]
  have hsplit2 : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ (𝔼.const t uy)] at h
  rw [hsplit2, hPO t _ _ (hPad t)]
  funext ω
  have hω := congrFun h ω
  rw [hlam t] at hω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at hω ⊢
  have hP := (hPpos t ω).ne'
  set e := 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω
  have h2 : Q t ω * uy = (β * (P t ω * e)) * uy := by
    have h3 : Q t ω * uy = Q t ω * (uy / P t ω) * P t ω := by field_simp
    rw [h3, hω]
    ring
  exact mul_right_cancel₀ huy.ne' h2

/-- Cochrane (2023), eq. (2.3), p. 22, both directions: with constant positive marginal utility,
a positive adapted price level and the pull-out property, the nominal Euler equation holds iff
`Q_t = β E_t(P_t/P_{t+1})` at every date. -/
theorem bondPrice_iff_euler (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β uy : ℝ}
    (huy : 0 < uy) {lam P Q : ℕ → Ω → ℝ} (hlam : ∀ t, lam t = fun _ => uy)
    (hPpos : ∀ t ω, 0 < P t ω) (hPad : 𝔼.Adapted P) :
    EulerNominal 𝔼 β lam P Q ↔ ∀ t, Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω) := by
  refine ⟨fun h t => bondPrice_of_euler 𝔼 hPO huy hlam hPpos hPad h t, fun h t => ?_⟩
  have hsplit : (fun ω => lam (t + 1) ω / P (t + 1) ω) =
      (fun _ => uy) * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; rw [hlam (t + 1)]; simp [div_eq_mul_inv]
  have hsplit2 : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ (𝔼.const t uy), h t, hsplit2, hPO t _ _ (hPad t)]
  funext ω
  rw [hlam t]
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hP := (hPpos t ω).ne'
  field_simp

/-- Cochrane (2023), p. 21: the nominal interest rate implied by the bond price,
`i_t = 1/Q_t − 1`. -/
noncomputable def rate (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := (Q t ω)⁻¹ - 1

/-- Cochrane (2023), p. 21: `Q_t = 1/(1 + i_t)`. -/
theorem bondPrice_eq_inv_one_add_rate (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Q t ω = (1 + rate Q t ω)⁻¹ := by
  simp [rate]

/-- Cochrane (2023), eq. (2.3), p. 22: `1/(1+i_t) = (1/R) E_t(P_t/P_{t+1})` with `R = 1/β`. -/
theorem inv_one_add_rate_eq (𝔼 : ExpectationSystem Ω) {β : ℝ} {P Q : ℕ → Ω → ℝ}
    {t : ℕ} (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) (ω : Ω) :
    (1 + rate Q t ω)⁻¹ = (β⁻¹)⁻¹ * 𝔼.E t (fun ω => P t ω / P (t + 1) ω) ω := by
  rw [← bondPrice_eq_inv_one_add_rate, inv_inv, h23]
  simp

/-- Cochrane (2023), p. 22: the rate is positive iff the bond price is below one (for `Q > 0`). -/
theorem rate_pos_iff {Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hQ : 0 < Q t ω) :
    0 < rate Q t ω ↔ Q t ω < 1 := by
  simp only [rate, sub_pos]
  rw [one_lt_inv₀ hQ]

/-- Cochrane (2023), p. 22: the rate is negative iff the bond price exceeds one (for `Q > 0`). -/
theorem rate_neg_iff {Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hQ : 0 < Q t ω) :
    rate Q t ω < 0 ↔ 1 < Q t ω := by
  simp only [rate, sub_neg]
  rw [inv_lt_one₀ hQ]

/-! ### Money demand (p. 22) -/

/-- Cochrane (2023), p. 22, "When `i_t > 0` the household demands no money `M_t = 0`": take any
household plan satisfying (2.2) at dates `t` and `t + 1` in state `ω`. Replace the money held
overnight `M_t` by `M_t/Q_t` more bonds, and spend the extra payoff `i_t M_t` at `t + 1`. The new
plan satisfies (2.2) at both dates, keeps `B_t ≥ 0`, `M_t = 0`, and raises date-`t+1`
consumption by `i_t M_t / P_{t+1}`, strictly if `M_t > 0`. -/
theorem money_dominated {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hQ : 0 < Q t ω) (hP1 : 0 < P (t + 1) ω)
    (h0 : Mm t ω + Bm t ω + P t ω * y =
      P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)
    (h1 : Mm (t + 1) ω + Bm (t + 1) ω + P (t + 1) ω * y =
      P (t + 1) ω * c (t + 1) ω + P (t + 1) ω * s (t + 1) ω + Mm (t + 2) ω +
        Q (t + 1) ω * Bm (t + 2) ω) :
    let B' := Bm (t + 1) ω + Mm (t + 1) ω / Q t ω
    let c' := c (t + 1) ω + rate Q t ω * Mm (t + 1) ω / P (t + 1) ω
    (Mm t ω + Bm t ω + P t ω * y = P t ω * c t ω + P t ω * s t ω + 0 + Q t ω * B') ∧
      (0 + B' + P (t + 1) ω * y = P (t + 1) ω * c' + P (t + 1) ω * s (t + 1) ω +
        Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω) ∧
      (0 ≤ Bm (t + 1) ω → 0 ≤ Mm (t + 1) ω → 0 ≤ B') ∧
      (0 < rate Q t ω → 0 < Mm (t + 1) ω → c (t + 1) ω < c') := by
  intro B' c'
  have hQ0 := hQ.ne'
  have hP0 := hP1.ne'
  refine ⟨?_, ?_, fun hb hm => ?_, fun hi hm => ?_⟩
  · simp only [B']
    field_simp
    linarith
  · simp only [B', c', rate]
    field_simp
    linear_combination (Q t ω) * h1
  · exact add_nonneg hb (div_nonneg hm hQ.le)
  · simp only [c']
    have : 0 < rate Q t ω * Mm (t + 1) ω / P (t + 1) ω := by positivity
    linarith

/-- Cochrane (2023), p. 22, "The interest rate cannot be less than zero in this model": with
`i_t < 0` (`Q_t > 1`), any plan holding bonds `B_t > 0` is strictly dominated by holding their
cost `Q_t B_t` as money instead: (2.2) still holds at `t` and `t + 1`, money stays nonnegative,
`B_t = 0`, and date-`t+1` consumption rises by `(Q_t − 1) B_t / P_{t+1} > 0`. So no household
holds the government's debt at a negative rate. -/
theorem bonds_dominated_of_neg_rate {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hP1 : 0 < P (t + 1) ω)
    (h0 : Mm t ω + Bm t ω + P t ω * y =
      P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)
    (h1 : Mm (t + 1) ω + Bm (t + 1) ω + P (t + 1) ω * y =
      P (t + 1) ω * c (t + 1) ω + P (t + 1) ω * s (t + 1) ω + Mm (t + 2) ω +
        Q (t + 1) ω * Bm (t + 2) ω) :
    let M' := Mm (t + 1) ω + Q t ω * Bm (t + 1) ω
    let c' := c (t + 1) ω + (Q t ω - 1) * Bm (t + 1) ω / P (t + 1) ω
    (Mm t ω + Bm t ω + P t ω * y = P t ω * c t ω + P t ω * s t ω + M' + Q t ω * 0) ∧
      (M' + 0 + P (t + 1) ω * y = P (t + 1) ω * c' + P (t + 1) ω * s (t + 1) ω +
        Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω) ∧
      (0 ≤ Mm (t + 1) ω → 0 ≤ Q t ω → 0 ≤ Bm (t + 1) ω → 0 ≤ M') ∧
      (1 < Q t ω → 0 < Bm (t + 1) ω → c (t + 1) ω < c') := by
  intro M' c'
  have hP0 := hP1.ne'
  refine ⟨?_, ?_, fun hm hq hb => ?_, fun hq hb => ?_⟩
  · simp only [M']
    linarith
  · simp only [M', c']
    field_simp
    linarith
  · exact add_nonneg hm (mul_nonneg hq hb)
  · simp only [c']
    have : 0 < (Q t ω - 1) * Bm (t + 1) ω / P (t + 1) ω :=
      div_pos (mul_pos (by linarith) hb) hP1
    linarith

/-- Cochrane (2023), p. 22, "When `i_t = 0` money and bonds are perfect substitutes, so the
symbol `B_t` can stand for their sum": with `Q_t = 1`, any reallocation `(M', B')` of the
overnight portfolio with the same total `M' + B' = M_t + B_t` leaves (2.2) at `t` and `t + 1`
unchanged. -/
theorem perfect_substitutes {y : ℝ} {Mm Bm P c s Q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hQ : Q t ω = 1) {M' B' : ℝ} (hsum : M' + B' = Mm (t + 1) ω + Bm (t + 1) ω) :
    ((Mm t ω + Bm t ω + P t ω * y = P t ω * c t ω + P t ω * s t ω + M' + Q t ω * B') ↔
      (Mm t ω + Bm t ω + P t ω * y =
        P t ω * c t ω + P t ω * s t ω + Mm (t + 1) ω + Q t ω * Bm (t + 1) ω)) ∧
    ((M' + B' + P (t + 1) ω * y = P (t + 1) ω * c (t + 1) ω + P (t + 1) ω * s (t + 1) ω +
        Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω) ↔
      (Mm (t + 1) ω + Bm (t + 1) ω + P (t + 1) ω * y = P (t + 1) ω * c (t + 1) ω +
        P (t + 1) ω * s (t + 1) ω + Mm (t + 2) ω + Q (t + 1) ω * Bm (t + 2) ω)) := by
  simp only [hQ, one_mul]
  exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith,
    fun h => by linarith⟩⟩

/-! ### Eliminating money: (2.4) -/

/-- Cochrane (2023), eq. (2.4), p. 22: if no money is held overnight (`M_t = 0` for all `t`,
including `M_{−1}`), the government constraint (2.1) is `B_{t−1} = P_t s_t + Q_t B_t`. -/
theorem flow_of_govFlow {Mm Bm P s Q : ℕ → Ω → ℝ} (hM : ∀ t ω, Mm t ω = 0)
    (h21 : GovFlow Mm Bm P s Q) (t : ℕ) (ω : Ω) :
    Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω := by
  have := h21 t ω
  rw [hM t ω, hM (t + 1) ω] at this
  linarith

/-- Cochrane (2023), eq. (2.4), p. 22, the general elimination of money: if at every date either
no money is held overnight (`i_t > 0`) or `Q_t = 1` (`i_t = 0`, money and bonds perfect
substitutes), then with `B` standing for the sum of money and bonds, (2.1) becomes (2.4). -/
theorem govFlow_merge {Mm Bm P s Q : ℕ → Ω → ℝ}
    (hMQ : ∀ t ω, Mm (t + 1) ω = 0 ∨ Q t ω = 1) (h21 : GovFlow Mm Bm P s Q) (t : ℕ) (ω : Ω) :
    Mm t ω + Bm t ω = P t ω * s t ω + Q t ω * (Mm (t + 1) ω + Bm (t + 1) ω) := by
  have := h21 t ω
  rcases hMQ t ω with h | h
  · rw [h] at this ⊢
    linarith
  · rw [h] at this ⊢
    linarith

/-! ### The real flow condition (2.5) -/

/-- Cochrane (2023), eq. (2.5), p. 22: substituting the bond price (2.3) into (2.4) and dividing
by `P_t > 0` (with `P_t` and `B_t` known at `t`, and the pull-out property),
`B_{t−1}/P_t = s_t + β B_t E_t(1/P_{t+1})`. -/
theorem flow_real_25 (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω))
    (h24 : ∀ ω, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) (ω : Ω) :
    Bm t ω / P t ω = s t ω + β * Bm (t + 1) ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω := by
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ hPad] at h23
  have hQ := congrFun h23 ω
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hQ
  rw [h24 ω, hQ]
  have := (hPpos ω).ne'
  field_simp

/-- Cochrane (2023), eq. (2.5), p. 22, in terms of real debt `x_t = B_{t−1}/P_t`: with `B_t` known
at `t` and the pull-out property, `β B_t E_t(1/P_{t+1}) = β E_t x_{t+1}`, so (2.5) reads
`x_t = s_t + β E_t x_{t+1}`. -/
theorem flow_real_x (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm P : ℕ → Ω → ℝ} {t : ℕ} (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) :
    (fun ω => β * Bm (t + 1) ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) =
      β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  have hsplit : (fun ω => Bm (t + 1) ω / P (t + 1) ω) =
      Bm (t + 1) * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ hB]
  funext ω
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eqs. (2.4)–(2.5), p. 22, both directions: given (2.3), positive `P_t` known
at `t`, `B_t` known at `t` and pull-out, the nominal flow condition (2.4) at `t` holds iff the real
one `x_t = s_t + β E_t x_{t+1}` holds, `x_t = B_{t−1}/P_t`. -/
theorem flow_iff_real_x (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut) {β : ℝ}
    {Bm P s Q : ℕ → Ω → ℝ} {t : ℕ} (hPpos : ∀ ω, 0 < P t ω) (hPad : 𝔼.E t (P t) = P t)
    (hB : 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (h23 : Q t = β • 𝔼.E t (fun ω => P t ω / P (t + 1) ω)) :
    (∀ ω, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ↔
      (fun ω => Bm t ω / P t ω) =
        s t + β • 𝔼.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  have hx := flow_real_x 𝔼 hPO (β := β) (P := P) hB
  have hsplit : (fun ω => P t ω / P (t + 1) ω) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  have hQ : ∀ ω, Q t ω = β * (P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) := by
    intro ω
    rw [h23, hsplit, hPO t _ _ hPad]
    rfl
  constructor
  · intro h24
    rw [← hx]
    funext ω
    have := flow_real_25 𝔼 hPO hPpos hPad h23 h24 ω
    simpa using this
  · intro h ω
    have h1 := congrFun h ω
    rw [← hx] at h1
    simp only [Pi.add_apply] at h1
    have hP := (hPpos ω).ne'
    have hBP : Bm t ω = P t ω * (Bm t ω / P t ω) := by field_simp
    rw [hQ ω, hBP, h1]
    ring

/-! ### Proportional taxes (p. 23) -/

/-- Cochrane (2023), p. 23: with surpluses `P_t s_t = τ_t (P_t y) − P_t x_t` (a proportional
income tax less a real transfer) and `P_t ≠ 0`, the real surplus is `s_t = τ_t y − x_t`. -/
theorem propTax_real_surplus {y : ℝ} {P s τ xtr : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hP : P t ω ≠ 0) (h : P t ω * s t ω = τ t ω * (P t ω * y) - P t ω * xtr t ω) :
    s t ω = τ t ω * y - xtr t ω := by
  have : P t ω * (s t ω - (τ t ω * y - xtr t ω)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hP
  · linarith

/-- Cochrane (2023), p. 23: "This specification ensures that the price level is absent from the
right-hand side of (2.7)": two price paths (nonzero) with the same tax rates and real transfers
generate the same real surpluses. -/
theorem propTax_surplus_indep_price {y : ℝ} {P P' s s' τ xtr : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hP' : ∀ t ω, P' t ω ≠ 0)
    (h : ∀ t ω, P t ω * s t ω = τ t ω * (P t ω * y) - P t ω * xtr t ω)
    (h' : ∀ t ω, P' t ω * s' t ω = τ t ω * (P' t ω * y) - P' t ω * xtr t ω) : s = s' := by
  funext t ω
  rw [propTax_real_surplus (hP t ω) (h t ω), propTax_real_surplus (hP' t ω) (h' t ω)]

end Cochrane.IntertemporalModel.Environment
