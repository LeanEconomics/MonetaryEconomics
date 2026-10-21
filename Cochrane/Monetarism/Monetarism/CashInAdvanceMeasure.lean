/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.MoneyInUtilityMeasure
import Monetarism.CashInAdvance
import Monetarism.LinksTidy

/-!
# The cash-in-advance household on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.5.1–19.5.2,
pp. 447–451, eqs. (19.24)–(19.33), in the measure-theoretic setting of `ExpectationsMeasure` and
`HouseholdMeasure`: the household maximises expected utility `E ∑ βᵗu(c_t)` (a genuine integral)
subject to the budget constraint (19.27) with complete contingent claims holding almost surely,
the cash-in-advance constraint (19.24) `P_tc_t ≤ M^d_tV`, the overnight-money identity (19.25)
`M_t = M^d_t + P_t(y_t − c_t)` and no printing (19.26) `M_t ≥ 0`, on a probability space whose
information may grow forever. The finite-tree version is `CashInAdvance.TreeEuler` (with
`V = 1`); the general `ExpectationSystem` version `CashInAdvance.Stochastic.bond_price_19_32`
assumes `Λ_t = βᵗu'(y_t)`. Here it is derived, for every velocity `V`.

## The velocity wedge

Eliminating `M^d_t`, (19.24)–(19.26) say `m_t ≥ (1/V − 1)c_t + y_t` and `m_t ≥ 0` for real
overnight balances `m_t = M_t/P_t` (`cia_iff`, `CIACon`). One more unit of consumption therefore
needs `θ = 1/V − 1` more units of overnight money, which costs `ι_t = 1 − Q_t` in present value:
the effective price of consumption is `Λ_tw_t` with `w_t = 1 + θι_t`
(`HouseholdMeasure.wedge`; `CashInAdvance.MoneyDemand.binding_cost_wedge`).

## Main results

* `euler_step`, `multiplier_const`: at an optimal plan (regular prices, nonnegative nominal
  rates `Q_t ≤ 1`, consumption bounded, overnight money bounded away from zero),
  `βᵗu'(c_t) = λΛ_tw_t` almost surely at every date, with one multiplier `λ` known at date `0`.
* **(19.31) for every `V`** (`sdf_1931`): at an optimum consuming the endowment,
  `Λ_{t+j}w_{t+j}/(Λ_tw_t) = βʲu'(y_{t+j})/u'(y_t)`; with the normalisation `Λ_0w_0 = u'(y_0)`,
  `Λ_tw_t = βᵗu'(y_t)` (`lambda_derived`). **For `V = 1`**, `w = 1` and `Λ_t = βᵗu'(y_t)` is
  derived, not assumed (`lambda_derived_V1`, `sdf_1931_V1`).
* **(19.32) for every `V`** (`bond_1932`): `Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(w_t/w_{t+1})
  (P_t/P_{t+1})]`; for `V = 1` this is (19.32) as printed (`bond_1932_V1`). For `V ≠ 1`, the
  printed (19.32) holds at a state iff `E_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})(w_t/w_{t+1} − 1)]`
  vanishes there (`printed_1932_iff`), and it fails in general: `printed_1932_counterexample`
  gives, for every `V ≠ 1` and `0 < β < 1`, an economy on any probability space in which consuming
  the endowment is optimal while the printed (19.32) fails at date `0`.
* Sufficiency (`optimal_of_foc`): concave `u`, the first-order condition `βᵗu'(c_t) = λΛ_tw_t`,
  a binding cash constraint, `ι_t ≥ 0` and the transversality condition give optimality.
* Links to the finite tree (`Link`): with `V = 1`, on a finite event tree the derived
  `Λ_t = βᵗu'(y_t)` is the conclusion of `CashInAdvance.TreeEuler.sdf_eq` (`link_sdf_eq`), the
  derived (19.32) is `CashInAdvance.TreeEuler.bond_price_from_optimality`'s (`link_bond_price`,
  via `CashInAdvance.Stochastic.bond_price_19_32` for the tree's core system), and with one root
  node a measure-theoretic optimum is optimal in `TreeEuler.IsOptimal` and in the footnote-1
  problem `MoneyInUtility.FootnoteTree.TOptimal` through `LinksTidy.TreeBridge`
  (`link_isOptimal`), and conversely (`link_optimal_of_isOptimal`).
* The i.i.d. economy (`IID.iid_optimal`, `IID.iid_sdf`): with `V = 1`, inflation `P_t = 2ᵗ` and
  an i.i.d. endowment on `ExpectationsMeasureIID.iidSystem`, consuming the endowment is optimal
  and `Λ_t = βᵗu'(y_t)`, (19.32) hold there.
-/

namespace Cochrane.Monetarism.CashInAdvanceMeasure

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### The cash-in-advance constraints -/

/-- Cochrane (2023), eqs. (19.24)–(19.25), pp. 448–449: with `V > 0` and `P > 0`, the
cash-in-advance constraint `Pc ≤ M^dV` with `M^d = M − P(y − c)` (money taken shopping, given the
overnight money `M`) holds iff `(1/V − 1)c + y ≤ M/P`. -/
theorem cia_iff {P c y M V : ℝ} (hV : 0 < V) (hP : 0 < P) :
    P * c ≤ (M - P * (y - c)) * V ↔ (1 / V - 1) * c + y ≤ M / P := by
  have e : M / P - ((1 / V - 1) * c + y) = ((M - P * (y - c)) * V - P * c) / (V * P) := by
    field_simp
    ring
  rw [← sub_nonneg, ← sub_nonneg (a := M / P), e]
  constructor
  · intro h
    exact div_nonneg h (mul_pos hV hP).le
  · intro h
    have := mul_nonneg h (mul_pos hV hP).le
    rwa [div_mul_cancel₀ _ (mul_pos hV hP).ne'] at this

variable (S) in
/-- Cochrane (2023), eqs. (19.24)–(19.26), pp. 448–449: the cash-in-advance and no-printing
constraints in real overnight balances `m_t = M_t/P_t`: almost surely at every date
`(1/V − 1)c_t + y_t ≤ m_t` (`cia_iff`) and `0 ≤ m_t`. -/
def CIACon (V : ℝ) (y : ℕ → Ω → ℝ) (c m : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, (1 / V - 1) * c t ω + y t ω ≤ m t ω ∧ 0 ≤ m t ω

variable (S) in
/-- Cochrane (2023), §19.5.1, p. 449: an optimal plan of the cash-in-advance household
(utility `u(c_t)`, the budget (19.27)–(19.28) and the constraints (19.24)–(19.26)). -/
abbrev CIAOptimal (β : ℝ) (u : ℝ → ℝ) (V : ℝ) (Λ P y s : ℕ → Ω → ℝ) (N0 a0 : Ω → ℝ)
    (c m a : ℕ → Ω → ℝ) : Prop :=
  Optimal S β (fun x _ => u x) (CIACon S V y) Λ P y s N0 a0 c m a

/-- Cochrane (2023), §19.5.1, p. 448: a continuously differentiable utility of consumption alone
is a smooth period utility with `u_c = u'` and `u_m = 0`. -/
theorem smooth₂_of_deriv {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') :
    Smooth₂ (fun x _ => u x) (fun x _ => u' x) (fun _ _ => 0) := by
  refine ⟨fun x y => ?_, hu'.comp continuous_fst, continuous_const⟩
  have := (hu x).hasFDerivAt.comp (x, y) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, y)))
  have e : (ContinuousLinearMap.toSpanSingleton ℝ (u' x)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ) = u' x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    ext <;> simp [mul_comm]
  rw [e] at this
  exact this

/-- Cochrane (2023), (19.24)–(19.26), p. 449: if overnight money is bounded away from zero, then
consumption deviations `εz` accompanied by the overnight money `ε(1/V − 1)z` they require keep the
constraints `CIACon` for small steps. -/
theorem con_stable {V : ℝ} {y c m : ℕ → Ω → ℝ} (hcon : CIACon S V y c m) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω) (n : ℕ) (z₁ z₂ : Ω → ℝ) (hz₁ : BddAt S z₁)
    (hz₂ : BddAt S z₂) : ∃ η, 0 < η ∧ ∀ ε, |ε| < η → CIACon S V y (bump c n z₁ z₂ ε)
      (bump m n (fun ω => (1 / V - 1) * z₁ ω) (fun ω => (1 / V - 1) * z₂ ω) ε) := by
  obtain ⟨K1, hK1, hb1⟩ := hz₁.exists_pos
  obtain ⟨K2, hK2, hb2⟩ := hz₂.exists_pos
  set θ := 1 / V - 1 with hθ
  set C := (|θ| + 1) * (K1 + K2) with hC
  have hC0 : 0 < C := by positivity
  refine ⟨δ / C, div_pos hδ hC0, fun ε hε t => ?_⟩
  filter_upwards [hcon t, hmδ t, hb1, hb2] with ω h1 h2 h3 h4
  set d : ℝ := if t = n then z₁ ω else if t = n + 1 then z₂ ω else 0 with hd
  have hdb : |d| ≤ K1 + K2 := by
    simp only [hd]
    split_ifs
    · linarith
    · linarith
    · simp only [abs_zero]
      positivity
  have hcb : bump c n z₁ z₂ ε t ω = c t ω + ε * d := rfl
  have hmb : bump m n (fun ω => θ * z₁ ω) (fun ω => θ * z₂ ω) ε t ω = m t ω + ε * (θ * d) := by
    simp only [bump, hd]
    split_ifs <;> ring
  rw [hcb, hmb]
  have hsmall : |ε * (θ * d)| < δ := by
    rw [abs_mul, abs_mul]
    have h5 : |θ| * |d| ≤ C := by
      rw [hC]
      nlinarith [abs_nonneg θ, abs_nonneg d]
    calc |ε| * (|θ| * |d|) ≤ |ε| * C := mul_le_mul_of_nonneg_left h5 (abs_nonneg ε)
      _ < δ / C * C := mul_lt_mul_of_pos_right hε hC0
      _ = δ := div_mul_cancel₀ δ hC0.ne'
  constructor
  · have e : θ * (c t ω + ε * d) + y t ω - (m t ω + ε * (θ * d)) =
        θ * c t ω + y t ω - m t ω := by ring
    linarith [h1.1]
  · linarith [neg_abs_le (ε * (θ * d))]

/-- Cochrane (2023), p. 450 (`CashInAdvance.MoneyDemand.binding_cost_wedge`): with `V > 0` and
nonnegative nominal rates (`0 < Q_t ≤ 1`), the consumption wedge `w_t = 1 + (1/V − 1)ι_t` is at
least `min 1 (1/V) > 0`. -/
theorem wedge_lower {Λ P : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P) {V : ℝ} (hV : 0 < V) {t : ℕ}
    (hrate : ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) :
    ∀ᵐ ω ∂S.μ, min 1 (1 / V) ≤ wedge S (1 / V - 1) Λ P t ω := by
  filter_upwards [hrate, hp.bondPrice_pos t] with ω h1 h2
  simp only [wedge, iota]
  have hι0 : 0 ≤ 1 - bondPrice S Λ P t ω := by linarith
  have hι1 : 1 - bondPrice S Λ P t ω ≤ 1 := by linarith
  rcases le_or_gt V 1 with hV1 | hV1
  · have hθ : 0 ≤ 1 / V - 1 := by
      rw [sub_nonneg, le_div_iff₀ hV]
      linarith
    exact (min_le_left _ _).trans (by nlinarith)
  · have hθ : 1 / V - 1 < 0 := by
      rw [sub_neg, div_lt_one hV]
      exact hV1
    refine (min_le_right _ _).trans ?_
    nlinarith

/-- Cochrane (2023), p. 450: under `wedge_lower`, the wedge is almost surely nonzero and its
reciprocal is essentially bounded. -/
theorem wedge_regular {Λ P : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P) {V : ℝ} (hV : 0 < V) {t : ℕ}
    (hrate : ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) :
    (∀ᵐ ω ∂S.μ, wedge S (1 / V - 1) Λ P t ω ≠ 0) ∧
      BddAt S (fun ω => (wedge S (1 / V - 1) Λ P t ω)⁻¹) := by
  have hmin : 0 < min 1 (1 / V) := lt_min one_pos (one_div_pos.2 hV)
  have hl := wedge_lower hp hV hrate
  refine ⟨hl.mono fun ω h => (lt_of_lt_of_le hmin h).ne', ⟨(min 1 (1 / V))⁻¹, ?_⟩⟩
  filter_upwards [hl] with ω h
  have hw := lt_of_lt_of_le hmin h
  rw [abs_of_pos (inv_pos.2 hw)]
  exact inv_anti₀ hmin h

/-! ### The Euler equation and the state prices -/

/-- Cochrane (2023), (19.31), p. 450, on a probability space: **the cash-in-advance Euler
equation with the velocity wedge.** At an optimal plan (smooth `u`, `V > 0`, regular prices,
`Q_t ≤ 1`, consumption bounded, overnight money bounded away from zero and bounded),
`β^{t+1}u'(c_{t+1}) = (βᵗu'(c_t)/(Λ_tw_t)) Λ_{t+1}w_{t+1}` almost surely. -/
theorem euler_step {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hopt : CIAOptimal S β u V Λ P y s N0 a0 c m a)
    (hp : PriceRegular S Λ P) (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ}
    (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ (t + 1) * u' (c (t + 1) ω) =
      β ^ t * u' (c t ω) / (Λ t ω * wedge S (1 / V - 1) Λ P t ω) *
        (Λ (t + 1) ω * wedge S (1 / V - 1) Λ P (t + 1) ω) := by
  have h := bundle_euler hβ (smooth₂_of_deriv hu hu') hopt hp (1 / V - 1) (hcb t) (hcb (t + 1))
    (hmb t) (hmb (t + 1)) (wedge_regular hp hV (hrate t)).1 (wedge_regular hp hV (hrate t)).2
    (fun z₁ z₂ h1 h2 => con_stable hopt.2.1 hδ hmδ t z₁ z₂ h1 h2)
  filter_upwards [h] with ω hω
  simpa using hω

/-- Cochrane (2023), (19.31), p. 450, on a probability space: **one multiplier.** Under the
hypotheses of `euler_step`, `βᵗu'(c_t)/(Λ_tw_t) = u'(c_0)/(Λ_0w_0)` almost surely at every
date: `βᵗu'(c_t) = λΛ_tw_t` with `λ` known at date `0`. -/
theorem multiplier_const {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {c m a : ℕ → Ω → ℝ} (hopt : CIAOptimal S β u V Λ P y s N0 a0 c m a)
    (hp : PriceRegular S Λ P) (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ}
    (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ t * u' (c t ω) / (Λ t ω * wedge S (1 / V - 1) Λ P t ω) =
      u' (c 0 ω) / (Λ 0 ω * wedge S (1 / V - 1) Λ P 0 ω) := by
  have h := bundle_multiplier_const hβ (smooth₂_of_deriv hu hu') hopt hp (1 / V - 1) hcb hmb
    (fun n => (wedge_regular hp hV (hrate n)).1) (fun n => (wedge_regular hp hV (hrate n)).2)
    (fun n z₁ z₂ h1 h2 => con_stable hopt.2.1 hδ hmδ n z₁ z₂ h1 h2) t
  filter_upwards [h] with ω hω
  simpa using hω


/-- Cochrane (2023), eq. (19.31), p. 450, **for every velocity `V`**, on a probability space: at
an optimal plan consuming the endowment (hypotheses of `euler_step`, `u'(y_t) ≠ 0`),
`Λ_{t+j}w_{t+j}/(Λ_tw_t) = βʲu'(y_{t+j})/u'(y_t)` almost surely. The marginal rate of
substitution equals the ratio of the effective consumption prices `Λw`, not of `Λ` unless
`w_{t+j} = w_t` (`sdf_1931_V1`). -/
theorem sdf_1931 {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {m a : ℕ → Ω → ℝ} (hopt : CIAOptimal S β u V Λ P y s N0 a0 y m a)
    (hp : PriceRegular S Λ P) (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ}
    (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (hne : ∀ t ω, u' (y t ω) ≠ 0)
    (t j : ℕ) :
    ∀ᵐ ω ∂S.μ, Λ (t + j) ω * wedge S (1 / V - 1) Λ P (t + j) ω /
        (Λ t ω * wedge S (1 / V - 1) Λ P t ω) = β ^ j * u' (y (t + j) ω) / u' (y t ω) := by
  filter_upwards [multiplier_const hβ hu hu' hV hopt hp hyb hmb hδ hmδ hrate t,
    multiplier_const hβ hu hu' hV hopt hp hyb hmb hδ hmδ hrate (t + j),
    (wedge_regular hp hV (hrate t)).1, (wedge_regular hp hV (hrate (t + j))).1]
    with ω h1 h2 h3 h4
  have hA : Λ t ω * wedge S (1 / V - 1) Λ P t ω ≠ 0 := mul_ne_zero (hp.2.2.1 t ω).ne' h3
  have hB : Λ (t + j) ω * wedge S (1 / V - 1) Λ P (t + j) ω ≠ 0 :=
    mul_ne_zero (hp.2.2.1 (t + j) ω).ne' h4
  have h12 := h1.trans h2.symm
  rw [div_eq_div_iff hA hB] at h12
  rw [div_eq_div_iff hA (hne t ω)]
  have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
  refine mul_left_cancel₀ hb ?_
  rw [pow_add] at h12
  linear_combination h12

/-- Cochrane (2023), eq. (19.31), p. 450 ("`Λ_t`" as the stochastic discount factor), **for every
velocity `V`**, derived: at an optimum consuming the endowment, with the state prices normalised
by `Λ_0w_0 = u'(y_0)`, `Λ_tw_t = βᵗu'(y_t)` almost surely at every date. -/
theorem lambda_derived {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {m a : ℕ → Ω → ℝ} (hopt : CIAOptimal S β u V Λ P y s N0 a0 y m a)
    (hp : PriceRegular S Λ P) (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ}
    (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (hne : ∀ t ω, u' (y t ω) ≠ 0)
    (hnorm : ∀ ω, Λ 0 ω * wedge S (1 / V - 1) Λ P 0 ω = u' (y 0 ω)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Λ t ω * wedge S (1 / V - 1) Λ P t ω = β ^ t * u' (y t ω) := by
  filter_upwards [multiplier_const hβ hu hu' hV hopt hp hyb hmb hδ hmδ hrate t,
    (wedge_regular hp hV (hrate t)).1] with ω h1 h2
  rw [hnorm ω, div_self (hne 0 ω)] at h1
  have hA : Λ t ω * wedge S (1 / V - 1) Λ P t ω ≠ 0 := mul_ne_zero (hp.2.2.1 t ω).ne' h2
  rw [div_eq_one_iff_eq hA] at h1
  exact h1.symm

/-- Cochrane (2023), p. 450: with `V = 1` the consumption wedge is one. -/
theorem wedge_V1 (Λ P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : wedge S (1 / 1 - 1) Λ P t ω = 1 := by
  simp [wedge]

/-- Cochrane (2023), eq. (19.31), p. 450, **as printed (`V = 1`)**, on a probability space,
derived: at an optimum consuming the endowment, with `Λ_0 = u'(y_0)`, `Λ_t = βᵗu'(y_t)` almost
surely at every date. -/
theorem lambda_derived_V1 {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {m a : ℕ → Ω → ℝ}
    (hopt : CIAOptimal S β u 1 Λ P y s N0 a0 y m a) (hp : PriceRegular S Λ P)
    (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω) (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1)
    (hne : ∀ t ω, u' (y t ω) ≠ 0) (hnorm : ∀ ω, Λ 0 ω = u' (y 0 ω)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Λ t ω = β ^ t * u' (y t ω) := by
  filter_upwards [lambda_derived hβ hu hu' one_pos hopt hp hyb hmb hδ hmδ hrate hne
    (fun ω => by rw [wedge_V1, mul_one, hnorm]) t] with ω h
  rwa [wedge_V1, mul_one] at h

/-- Cochrane (2023), eq. (19.31), p. 450, **as printed (`V = 1`)**: at an optimum consuming the
endowment, `βʲu'(y_{t+j})/u'(y_t) = Λ_{t+j}/Λ_t` almost surely. -/
theorem sdf_1931_V1 {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {m a : ℕ → Ω → ℝ}
    (hopt : CIAOptimal S β u 1 Λ P y s N0 a0 y m a) (hp : PriceRegular S Λ P)
    (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω) (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1)
    (hne : ∀ t ω, u' (y t ω) ≠ 0) (t j : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ j * u' (y (t + j) ω) / u' (y t ω) = Λ (t + j) ω / Λ t ω := by
  filter_upwards [sdf_1931 hβ hu hu' one_pos hopt hp hyb hmb hδ hmδ hrate hne t j] with ω h
  rw [wedge_V1, wedge_V1, mul_one, mul_one] at h
  exact h.symm

/-- Cochrane (2023), eq. (19.32), p. 450, **for every velocity `V`**, on a probability space,
derived from optimality: at an optimum consuming the endowment (hypotheses of `euler_step`,
`u'(y_t) ≠ 0`), the nominal bond price is
`Q_t = βE_t[(u'(y_{t+1})/u'(y_t)) (w_t/w_{t+1}) (P_t/P_{t+1})]` almost surely. -/
theorem bond_1932 {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {m a : ℕ → Ω → ℝ} (hopt : CIAOptimal S β u V Λ P y s N0 a0 y m a)
    (hp : PriceRegular S Λ P) (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ}
    (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (hne : ∀ t ω, u' (y t ω) ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω = S.E t (fun ω => β * (u' (y (t + 1) ω) / u' (y t ω)) *
      (wedge S (1 / V - 1) Λ P t ω / wedge S (1 / V - 1) Λ P (t + 1) ω) *
        (P t ω / P (t + 1) ω)) ω := by
  set X : Ω → ℝ := fun ω => β * (u' (y (t + 1) ω) / u' (y t ω)) *
      (wedge S (1 / V - 1) Λ P t ω / wedge S (1 / V - 1) Λ P (t + 1) ω) *
        (P t ω / P (t + 1) ω) with hX
  have hae : pk Λ P (t + 1) =ᵐ[S.μ] pk Λ P t * X := by
    filter_upwards [euler_step hβ hu hu' hV hopt hp hyb hmb hδ hmδ hrate t,
      (wedge_regular hp hV (hrate t)).1, (wedge_regular hp hV (hrate (t + 1))).1]
      with ω h h3 h4
    have hb := (pow_pos hβ t).ne'
    have h1 := hne t ω
    have h2 := (hp.2.2.1 t ω).ne'
    have h5 := (hp.2.2.2.1 t ω).ne'
    have h6 := (hp.2.2.2.1 (t + 1) ω).ne'
    simp only [Pi.mul_apply, hX, pk]
    set w0 := wedge S (1 / V - 1) Λ P t ω with hw0
    set w1 := wedge S (1 / V - 1) Λ P (t + 1) ω with hw1
    have key : Λ (t + 1) ω = β * (u' (y (t + 1) ω) / u' (y t ω)) * (w0 / w1) * Λ t ω := by
      rw [pow_succ] at h
      field_simp at h ⊢
      linear_combination -h
    rw [key]
    field_simp
  have hXi : Integrable X S.μ := by
    have hb := (hp.pk_bdd (t + 1)).mul (hp.pk_inv_bdd t)
    have hm : AEStronglyMeasurable (fun ω => pk Λ P (t + 1) ω * (pk Λ P t ω)⁻¹) S.μ :=
      ((((hp.stronglyMeasurable_pk (t + 1)).measurable.mul
        ((hp.stronglyMeasurable_pk t).mono (S.𝓕.mono (Nat.le_succ t))).measurable.inv)
        ).stronglyMeasurable.mono (S.𝓕.le (t + 1))).aestronglyMeasurable
    refine (hb.integrable hm).congr ?_
    filter_upwards [hae] with ω h
    have := (hp.pk_pos t ω).ne'
    simp only [Pi.mul_apply] at h
    rw [h]
    field_simp
  obtain ⟨K, hK⟩ := hp.pk_bdd t
  filter_upwards [S.E_congr hae t, S.E_pullOut (hp.stronglyMeasurable_pk t) hK hXi] with ω h1 h2
  have := (hp.pk_pos t ω).ne'
  simp only [bondPrice]
  rw [h1, h2, Pi.mul_apply]
  field_simp

/-- Cochrane (2023), eq. (19.32), p. 450, **as printed (`V = 1`)**, on a probability space,
derived from optimality: `Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]` almost surely; the
hypothesis `Λ_t = βᵗu'(y_t)` of `CashInAdvance.Stochastic.bond_price_19_32` is not needed. -/
theorem bond_1932_V1 {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {m a : ℕ → Ω → ℝ}
    (hopt : CIAOptimal S β u 1 Λ P y s N0 a0 y m a) (hp : PriceRegular S Λ P)
    (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ} (hδ : 0 < δ)
    (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω) (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1)
    (hne : ∀ t ω, u' (y t ω) ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω =
      S.E t (fun ω => β * (u' (y (t + 1) ω) / u' (y t ω)) * (P t ω / P (t + 1) ω)) ω := by
  filter_upwards [bond_1932 hβ hu hu' one_pos hopt hp hyb hmb hδ hmδ hrate hne t] with ω h
  simpa only [div_one, sub_self, MoneyInUtilityMeasure.wedge_zero, mul_one] using h

/-- Cochrane (2023), eq. (19.32), p. 450, **what holds for `V ≠ 1`**: under the hypotheses of
`bond_1932` and `1/u'(y_t)` essentially bounded, the printed formula
`Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]` holds at almost every state exactly when the
wedge correction vanishes there,
`E_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})(w_t/w_{t+1} − 1)] = 0` (true for `V = 1`, where `w = 1`,
or when `w_{t+1} = w_t`, e.g. a constant nominal rate). -/
theorem printed_1932_iff {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {V : ℝ} (hV : 0 < V) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ}
    {m a : ℕ → Ω → ℝ} (hopt : CIAOptimal S β u V Λ P y s N0 a0 y m a)
    (hp : PriceRegular S Λ P) (hyb : ∀ n, BddAt S (y n)) (hmb : ∀ n, BddAt S (m n)) {δ : ℝ}
    (hδ : 0 < δ) (hmδ : ∀ t, ∀ᵐ ω ∂S.μ, δ ≤ m t ω)
    (hrate : ∀ t, ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω ≤ 1) (hne : ∀ t ω, u' (y t ω) ≠ 0)
    (hinv : ∀ t, BddAt S fun ω => (u' (y t ω))⁻¹) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (bondPrice S Λ P t ω =
        β * S.E t (fun ω => u' (y (t + 1) ω) / u' (y t ω) * (P t ω / P (t + 1) ω)) ω ↔
      S.E t (fun ω => u' (y (t + 1) ω) / u' (y t ω) * (P t ω / P (t + 1) ω) *
        (wedge S (1 / V - 1) Λ P t ω / wedge S (1 / V - 1) Λ P (t + 1) ω - 1)) ω = 0) := by
  have hya := hopt.1.2.1
  set A : Ω → ℝ := fun ω => u' (y (t + 1) ω) / u' (y t ω) * (P t ω / P (t + 1) ω) with hA
  set r : Ω → ℝ := fun ω => wedge S (1 / V - 1) Λ P t ω / wedge S (1 / V - 1) Λ P (t + 1) ω
    with hr
  have hAm : AEStronglyMeasurable A S.μ :=
    ((((hu'.measurable.comp (hya (t + 1)).measurable).div
      (hu'.measurable.comp ((hya t).mono (S.𝓕.mono (Nat.le_succ t))).measurable)).mul
      (((hp.2.1 t).mono (S.𝓕.mono (Nat.le_succ t))).measurable.div
        (hp.2.1 (t + 1)).measurable)).stronglyMeasurable.mono
      (S.𝓕.le (t + 1))).aestronglyMeasurable
  have hAb : BddAt S A := by
    have h1 : BddAt S (fun ω => u' (y (t + 1) ω)) := by
      obtain ⟨M, hM⟩ := hyb (t + 1)
      obtain ⟨C, -, hC⟩ := exists_abs_le_of_continuous₂ (v := fun x _ => u' x)
        (hu'.comp continuous_fst) M
      exact ⟨C, hM.mono fun ω h => hC _ 0 h (by
        rw [abs_zero]
        exact (abs_nonneg _).trans h)⟩
    have := ((h1.mul (hinv t)).mul (hp.2.2.2.2 t).2.2.1).mul (hp.2.2.2.2 (t + 1)).2.2.2
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hA]
    ring
  have hAi : Integrable A S.μ := hAb.integrable hAm
  -- `A r` is integrable, being `X/β`
  have hX := bond_1932 hβ hu hu' hV hopt hp hyb hmb hδ hmδ hrate hne t
  have hArX : (fun ω => A ω * r ω) = fun ω => β⁻¹ * (β * (u' (y (t + 1) ω) / u' (y t ω)) *
      (wedge S (1 / V - 1) Λ P t ω / wedge S (1 / V - 1) Λ P (t + 1) ω) *
        (P t ω / P (t + 1) ω)) := by
    funext ω
    have := hβ.ne'
    simp only [hA, hr]
    field_simp
  have hXi : Integrable (fun ω => β * (u' (y (t + 1) ω) / u' (y t ω)) *
      (wedge S (1 / V - 1) Λ P t ω / wedge S (1 / V - 1) Λ P (t + 1) ω) *
        (P t ω / P (t + 1) ω)) S.μ := by
    by_contra hni
    have h0 := condExp_of_not_integrable (μ := S.μ) (m := S.𝓕 t) hni
    have hQ := hp.bondPrice_pos t
    have : ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω = 0 := by
      filter_upwards [hX] with ω h
      rw [h]
      change (S.μ[_ | S.𝓕 t]) ω = 0
      rw [h0]
      rfl
    have hfalse : ∀ᵐ ω ∂S.μ, False := by
      filter_upwards [this, hQ] with ω h1 h2
      linarith
    exact absurd (ae_iff.1 hfalse) (by simp)
  have hAri : Integrable (fun ω => A ω * r ω) S.μ := by
    rw [hArX]
    exact hXi.const_mul _
  have e1 : (fun ω => A ω * (r ω - 1)) = (fun ω => A ω * r ω) - A := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  have e2 : (fun ω => β * (u' (y (t + 1) ω) / u' (y t ω)) *
      (wedge S (1 / V - 1) Λ P t ω / wedge S (1 / V - 1) Λ P (t + 1) ω) *
        (P t ω / P (t + 1) ω)) = β • fun ω => A ω * r ω := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, hA, hr]
    ring
  rw [e2] at hX
  change ∀ᵐ ω ∂S.μ, (bondPrice S Λ P t ω = β * S.E t A ω ↔
    S.E t (fun ω => A ω * (r ω - 1)) ω = 0)
  rw [e1]
  filter_upwards [hX, S.E_smul β (fun ω => A ω * r ω) t, S.E_sub hAri hAi t] with ω h1 h2 h3
  rw [h1, h2, h3, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  constructor
  · intro h
    have := mul_left_cancel₀ hβ.ne' h
    linarith
  · intro h
    have : S.E t (fun ω => A ω * r ω) ω = S.E t A ω := by linarith
    rw [this]


/-! ### Sufficiency -/

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are
necessary and sufficient"), on a probability space, **sufficiency for every velocity `V`**: for
concave `u` (`u(x') ≤ u(x) + u'(x)(x' − x)`), a feasible, admissible plan satisfying the
constraints (19.24)–(19.26) with the cash constraint binding (`m_t = (1/V − 1)c_t + y_t`),
nonnegative interest costs `ι_t ≥ 0`, the first-order condition `βᵗu'(c_t) = λΛ_tw_t` (`λ ≥ 0`)
and the transversality condition is optimal. -/
theorem optimal_of_foc {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hconc : ∀ x x', u x' ≤ u x + u' x * (x' - x)) {V : ℝ} {Λ P y s : ℕ → Ω → ℝ}
    {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : Feasible S Λ P y s N0 a0 c m a) (hcon : CIACon S V y c m)
    (hadm : UAdmissible S β (fun n ω => u (c n ω)))
    (hbind : ∀ t, ∀ᵐ ω ∂S.μ, m t ω = (1 / V - 1) * c t ω + y t ω)
    (hι : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ iota S Λ P t ω)
    (hfoc : ∀ t, ∀ᵐ ω ∂S.μ,
      β ^ t * u' (c t ω) = lam * (Λ t ω * wedge S (1 / V - 1) Λ P t ω))
    (htvc : Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0)) :
    CIAOptimal S β u V Λ P y s N0 a0 c m a := by
  refine optimal_of_supergradient hβ hp hy hs hlam hf hcon hadm htvc
    fun c' m' a' _ hc' t => ?_
  filter_upwards [hfoc t, hbind t, hι t, hc' t] with ω h1 h2 h3 h4
  set θ := 1 / V - 1 with hθ
  have hk := mul_le_mul_of_nonneg_left (show u (c' t ω) - u (c t ω) ≤ u' (c t ω) *
    (c' t ω - c t ω) by linarith [hconc (c t ω) (c' t ω)]) (pow_nonneg hβ.le t)
  have e1 : β ^ t * (u' (c t ω) * (c' t ω - c t ω)) = lam * (Λ t ω * (c' t ω - c t ω)) +
      lam * Λ t ω * iota S Λ P t ω * (θ * (c' t ω - c t ω)) := by
    rw [← mul_assoc, h1]
    simp only [wedge]
    ring
  have hpos : 0 ≤ lam * Λ t ω * iota S Λ P t ω :=
    mul_nonneg (mul_nonneg hlam (hp.2.2.1 t ω).le) h3
  have hm : θ * (c' t ω - c t ω) ≤ m' t ω - m t ω := by linarith [h4.1]
  have h5 := mul_le_mul_of_nonneg_left hm hpos
  calc β ^ t * (u (c' t ω) - u (c t ω)) ≤ β ^ t * (u' (c t ω) * (c' t ω - c t ω)) := hk
    _ ≤ lam * (Λ t ω * ((c' t ω - c t ω) + iota S Λ P t ω * (m' t ω - m t ω))) := by
        rw [e1]
        nlinarith [h5]

/-! ### The printed (19.32) fails for `V ≠ 1` -/

namespace Counterexample

/-- Cochrane (2023), p. 450: the overnight money needed per unit of consumption, `θ = 1/V − 1`. -/
noncomputable def theta (V : ℝ) : ℝ := 1 / V - 1

/-- Cochrane (2023), p. 450: the stationary consumption wedge `w̄ = 1 + θ(1 − β)` (when `Q = β`). -/
noncomputable def wbar (β V : ℝ) : ℝ := 1 + theta V * (1 - β)

/-- Cochrane (2023), p. 450: the date-0 consumption wedge `w_0 = 2(1 + θ)w̄/(2w̄ + θβ)`, the
fixed point of `w_0 = 1 + θ(1 − βw_0/(2w̄))` when the price level doubles at date `1`. -/
noncomputable def w0 (β V : ℝ) : ℝ :=
  (1 + theta V) * (2 * wbar β V) / (2 * wbar β V + theta V * β)

/-- Cochrane (2023), p. 450: the state prices `Λ_0 = 1/w_0`, `Λ_t = βᵗ/w̄` (deterministic). -/
noncomputable def cxΛ (β V : ℝ) (t : ℕ) (_ : Ω) : ℝ :=
  if t = 0 then 1 / w0 β V else β ^ t / wbar β V

/-- Cochrane (2023), p. 450: the price level `P_0 = 1`, `P_t = 2` for `t ≥ 1`. -/
noncomputable def cxP (t : ℕ) (_ : Ω) : ℝ := if t = 0 then 1 else 2

/-- Cochrane (2023), (19.33), p. 450: the binding overnight money `m_t = y/V = 1/V`. -/
noncomputable def cxm (V : ℝ) (_ : ℕ) (_ : Ω) : ℝ := 1 / V

/-- Cochrane (2023), (19.27), p. 449: the transfers that make the flow constraint hold with no
bonds, `s_t = (M_{t−1} − P_tm_t)/P_t`, with `M_{−1} = 1/V`. -/
noncomputable def cxs (V : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (moneyIn (fun _ => 1 / V) cxP (cxm V) t ω - cxP t ω * cxm V t ω) / cxP t ω

/-- Cochrane (2023), p. 450: `θ > −1` for `V > 0`. -/
theorem theta_gt {V : ℝ} (hV : 0 < V) : -1 < theta V := by
  simp only [theta]
  have := one_div_pos.2 hV
  linarith

/-- Cochrane (2023), p. 450: `w̄ > 0`. -/
theorem wbar_pos {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) : 0 < wbar β V := by
  have := theta_gt hV
  simp only [wbar]
  nlinarith

/-- Cochrane (2023), p. 450: `2w̄ + θβ > 0`. -/
theorem den_pos {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) :
    0 < 2 * wbar β V + theta V * β := by
  have := theta_gt hV
  simp only [wbar]
  nlinarith

/-- Cochrane (2023), p. 450: `w_0 > 0`. -/
theorem w0_pos {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) : 0 < w0 β V := by
  have := theta_gt hV
  have := wbar_pos hβ0 hβ1 hV
  have := den_pos hβ0 hβ1 hV
  simp only [w0]
  apply div_pos _ (by assumption)
  apply mul_pos (by linarith)
  linarith

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 450: the state prices are positive. -/
theorem cxΛ_pos {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) (t : ℕ) (ω : Ω) :
    0 < cxΛ β V t ω := by
  simp only [cxΛ]
  split_ifs
  · exact one_div_pos.2 (w0_pos hβ0 hβ1 hV)
  · exact div_pos (pow_pos hβ0 t) (wbar_pos hβ0 hβ1 hV)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 450: the price level is positive. -/
theorem cxP_pos (t : ℕ) (ω : Ω) : 0 < cxP t ω := by
  simp only [cxP]
  split_ifs <;> norm_num

/-- Cochrane (2023), p. 450: the deterministic prices are regular on any probability space. -/
theorem cx_priceRegular {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) :
    PriceRegular S (cxΛ β V) cxP := by
  refine ⟨fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    cxΛ_pos hβ0 hβ1 hV, cxP_pos, fun t =>
      ⟨⟨|if t = 0 then 1 / w0 β V else β ^ t / wbar β V|, ?_⟩,
      ⟨|(if t = 0 then 1 / w0 β V else β ^ t / wbar β V)⁻¹|, ?_⟩, ⟨2, ?_⟩, ⟨1, ?_⟩⟩⟩
  all_goals refine Eventually.of_forall fun ω => ?_
  · simp only [cxΛ]
    exact le_rfl
  · simp only [cxΛ]
    exact le_rfl
  · simp only [cxP]
    split_ifs <;> norm_num
  · simp only [cxP]
    split_ifs <;> norm_num

/-- Cochrane (2023), p. 450 (a deterministic variable is integrable): a function constant on
`Ω` is integrable for the probability measure. -/
theorem integrable_of_forall_eq {f : Ω → ℝ} (hf : ∀ x x', f x = f x') : Integrable f S.μ := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure S.μ
  have : f = fun _ => f ω₀ := funext fun x => hf x ω₀
  rw [this]
  exact integrable_const _

/-- Cochrane (2023), (19.32), p. 450: the bond prices of the example, `Q_0 = βw_0/(2w̄)` (the price
level doubles) and `Q_t = β` for `t ≥ 1`. -/
theorem cx_bondPrice {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) (t : ℕ) (ω : Ω) :
    bondPrice S (cxΛ β V) cxP t ω = if t = 0 then β * w0 β V / (2 * wbar β V) else β := by
  have hw := (w0_pos hβ0 hβ1 hV).ne'
  have hb := (wbar_pos hβ0 hβ1 hV).ne'
  have e : pk (cxΛ (Ω := Ω) β V) cxP (t + 1) = fun _ : Ω => β ^ (t + 1) / wbar β V / 2 := by
    funext ω
    simp [pk, cxΛ, cxP]
  simp only [bondPrice]
  rw [e, S.E_const]
  cases t with
  | zero =>
    simp only [pk, cxΛ, cxP, ↓reduceIte, zero_add, pow_one]
    field_simp
  | succ k =>
    simp only [pk, cxΛ, cxP, Nat.succ_ne_zero, ↓reduceIte]
    have := (pow_pos hβ0 (k + 1)).ne'
    field_simp
    ring

/-- Cochrane (2023), p. 450 (`CashInAdvance.MoneyDemand.binding_cost_wedge`): the consumption
wedges of the example are `w_0` at date `0` and `w̄` afterwards. -/
theorem cx_wedge {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V) (t : ℕ) (ω : Ω) :
    wedge S (1 / V - 1) (cxΛ β V) cxP t ω = if t = 0 then w0 β V else wbar β V := by
  have hb := (wbar_pos hβ0 hβ1 hV).ne'
  have hd := (den_pos hβ0 hβ1 hV).ne'
  simp only [wedge, iota, cx_bondPrice hβ0 hβ1 hV t ω]
  split_ifs
  · change 1 + theta V * (1 - β * ((1 + theta V) * (2 * wbar β V) /
      (2 * wbar β V + theta V * β)) / (2 * wbar β V)) = w0 β V
    simp only [w0]
    field_simp
    ring
  · simp only [wbar, theta]

end Counterexample

/-- Cochrane (2023), eq. (19.32), p. 450, **the printed formula is false for `V ≠ 1`**: for
every `0 < β < 1`, `V > 0` with `V ≠ 1`, and on every probability space, take linear utility
`u(c) = c`, the constant endowment `y = 1`, the price level `P_0 = 1`, `P_t = 2` (`t ≥ 1`), state
prices `Λ_0 = 1/w_0`, `Λ_t = βᵗ/w̄`, binding overnight money `m = 1/V`, no bonds and the
transfers `Counterexample.cxs`. Consuming the endowment is optimal for the cash-in-advance
household (`optimal_of_foc`), yet at date `0` the bond price
`Q_0 = βw_0/(2w̄) = β(1 + θ)/(2w̄ + θβ)` differs from the printed
`βE_0[(u'(y_1)/u'(y_0))(P_0/P_1)] = β/2` (the corrected `bond_1932` holds). -/
theorem printed_1932_counterexample {β V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hV : 0 < V)
    (hV1 : V ≠ 1) :
    CIAOptimal S β (fun x => x) V (Counterexample.cxΛ β V) Counterexample.cxP (fun _ _ => 1)
        (Counterexample.cxs V) (fun _ => 1 / V) (fun _ => 0) (fun _ _ => 1)
        (Counterexample.cxm V) (fun _ _ => 0) ∧
      ∀ ω, bondPrice S (Counterexample.cxΛ β V) Counterexample.cxP 0 ω ≠
        β * S.E 0 (fun ω => 1 / 1 * (Counterexample.cxP 0 ω / Counterexample.cxP 1 ω)) ω := by
  open Counterexample in
  have hθ := theta_gt hV
  have hwb := wbar_pos hβ0 hβ1 hV
  have hw0 := w0_pos hβ0 hβ1 hV
  have hden := den_pos hβ0 hβ1 hV
  have hp : PriceRegular S (cxΛ β V) cxP := cx_priceRegular hβ0 hβ1 hV
  have hconst : ∀ {f : Ω → ℝ}, (∀ x x', f x = f x') → Integrable f S.μ :=
    fun h => integrable_of_forall_eq h
  have hpkT : ∀ T (ω : Ω), pk (cxΛ β V) cxP T ω = if T = 0 then 1 / w0 β V else
      β ^ T / wbar β V / 2 := by
    intro T ω
    cases T with
    | zero => simp [pk, cxΛ, cxP]
    | succ k => simp [pk, cxΛ, cxP]
  have hmIn : ∀ T (ω : Ω), moneyIn (fun _ => 1 / V) cxP (cxm V) T ω =
      if T = 0 then 1 / V else cxP (T - 1) ω * (1 / V) := by
    intro T ω
    cases T with
    | zero => simp [moneyIn]
    | succ k => simp [moneyIn, cxm]
  have hmInpos : ∀ T (ω : Ω), 0 ≤ moneyIn (fun _ => 1 / V) cxP (cxm V) T ω := by
    intro T ω
    rw [hmIn]
    split_ifs
    · positivity
    · exact mul_nonneg (cxP_pos _ _).le (by positivity)
  -- feasibility
  have hflow : Flow S (cxΛ β V) cxP (fun _ _ => 1) (cxs V) (fun _ => 1 / V) (fun _ _ => 1)
      (cxm V) (fun _ _ => 0) := by
    intro t
    refine Eventually.of_forall fun ω => ?_
    have e0 : S.E t (fun _ => (0 : ℝ)) = 0 := S.E_zero t
    have hP := (cxP_pos t ω).ne'
    simp only [claimCost, mul_zero, e0, cxs, Pi.zero_apply, zero_div, sub_self, zero_add]
    field_simp
    ring
  have hfeas : Feasible S (cxΛ β V) cxP (fun _ _ => 1) (cxs V) (fun _ => 1 / V) (fun _ => 0)
      (fun _ _ => 1) (cxm V) (fun _ _ => 0) := by
    refine ⟨rfl, fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
      fun _ => stronglyMeasurable_const, hflow, fun t => ?_, fun t => ?_, fun t => ?_,
      fun t => ?_, fun δ hδ => Eventually.of_forall fun T => ?_⟩
    · exact hconst fun x x' => by simp
    · exact hconst fun x x' => by rw [hpkT, hpkT, hmIn, hmIn]; simp [cxP]
    · exact hconst fun x x' => by simp [cxΛ, cxm]
    · exact hconst fun x x' => by simp [cxΛ]
    · refine le_trans (by linarith) (integral_nonneg fun ω => ?_)
      simp only [zero_add]
      exact mul_nonneg (hp.pk_pos T ω).le (hmInpos T ω)
  have hadm : UAdmissible S β (fun n ω => (fun x : ℝ => x) ((fun _ _ => (1 : ℝ)) n ω)) :=
    UAdmissible.of_bdd hβ0.le hβ1 (fun _ => aestronglyMeasurable_const) (K := 1)
      fun _ _ => by norm_num
  -- the transversality condition
  have htvc : Tendsto (wealthPV S (cxΛ β V) cxP (fun _ => 1 / V) (cxm V) (fun _ _ => 0)) atTop
      (𝓝 0) := by
    set C := 1 / (V * wbar β V) + 1 / (w0 β V * V) with hC
    have hb : ∀ T, ‖wealthPV S (cxΛ β V) cxP (fun _ => 1 / V) (cxm V) (fun _ _ => 0) T‖ ≤
        C * β ^ T := by
      intro T
      have h := norm_integral_le_of_norm_le_const (μ := S.μ) (C := C * β ^ T)
        (f := fun ω => pk (cxΛ β V) cxP T ω * ((fun _ _ => (0 : ℝ)) T ω +
          moneyIn (fun _ => 1 / V) cxP (cxm V) T ω))
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, zero_add, hpkT, hmIn]
          cases T with
          | zero =>
            simp only [↓reduceIte, pow_zero, mul_one]
            rw [abs_of_pos (by positivity), hC]
            have : 0 ≤ 1 / (V * wbar β V) := by positivity
            have e : 1 / w0 β V * (1 / V) = 1 / (w0 β V * V) := by field_simp
            linarith
          | succ k =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            have hP2 : cxP k ω ≤ 2 := by simp only [cxP]; split_ifs <;> norm_num
            have hP0 := cxP_pos k ω
            have hβk := pow_pos hβ0 (k + 1)
            rw [abs_of_pos (by positivity), hC]
            have h1 : β ^ (k + 1) / wbar β V / 2 * (cxP k ω * (1 / V)) ≤
                1 / (V * wbar β V) * β ^ (k + 1) := by
              have e : 1 / (V * wbar β V) * β ^ (k + 1) =
                  β ^ (k + 1) / wbar β V / 2 * (2 * (1 / V)) := by field_simp
              rw [e]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP2 (by positivity))
                (by positivity)
            have h2 : 0 ≤ 1 / (w0 β V * V) * β ^ (k + 1) := by positivity
            nlinarith)
      rw [probReal_univ, mul_one] at h
      exact h
    have hlim : Tendsto (fun T : ℕ => C * β ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul C
    exact squeeze_zero_norm hb hlim
  refine ⟨optimal_of_foc (u' := fun _ => 1) hβ0 (fun x x' => by ring_nf; exact le_rfl) hp
    (fun t => hconst fun x x' => by simp [cxΛ]) (fun t => hconst fun x x' => ?_) zero_le_one
    hfeas ?_ hadm (fun t => Eventually.of_forall fun ω => ?_)
    (fun t => Eventually.of_forall fun ω => ?_) (fun t => Eventually.of_forall fun ω => ?_)
    htvc, fun ω => ?_⟩
  · simp only [cxs]
    rw [hmIn, hmIn]
    simp [cxΛ, cxP, cxm]
  · intro t
    exact Eventually.of_forall fun ω => ⟨by simp [cxm], by simp only [cxm]; positivity⟩
  · simp only [cxm]
    ring
  · rw [show iota S (cxΛ β V) cxP t ω = 1 - bondPrice S (cxΛ β V) cxP t ω from rfl,
      cx_bondPrice hβ0 hβ1 hV t ω]
    split_ifs
    · have key : β * (1 + theta V) ≤ 2 * wbar β V + theta V * β := by
        simp only [wbar]
        nlinarith [mul_pos (show 0 < theta V + 1 by linarith) (show 0 < 1 - β by linarith)]
      have : β * w0 β V / (2 * wbar β V) ≤ 1 := by
        rw [div_le_one (by positivity)]
        simp only [w0]
        rw [mul_div_assoc', div_le_iff₀ hden]
        nlinarith [mul_le_mul_of_nonneg_left key (show 0 ≤ 2 * wbar β V by positivity)]
      linarith
    · linarith
  · rw [cx_wedge hβ0 hβ1 hV t ω]
    simp only [cxΛ, one_mul, mul_one]
    split_ifs with h
    · subst h
      field_simp
    · field_simp
  · rw [cx_bondPrice hβ0 hβ1 hV 0 ω]
    have e : S.E 0 (fun ω => 1 / 1 * (cxP 0 ω / cxP 1 ω)) = fun _ => 1 / 2 := by
      have : (fun ω : Ω => 1 / 1 * (cxP 0 ω / cxP 1 ω)) = fun _ => 1 / 2 := by
        funext ω
        simp [cxP]
      rw [this, S.E_const]
    rw [e]
    simp only [↓reduceIte]
    intro h
    have h' : β * (w0 β V / (2 * wbar β V)) = β * (1 / 2) := by
      rw [← mul_div_assoc]
      exact h
    have h1 : w0 β V / (2 * wbar β V) = 1 / 2 := mul_left_cancel₀ hβ0.ne' h'
    rw [div_eq_iff (by positivity)] at h1
    have h2 : (1 + theta V) * (2 * wbar β V) = wbar β V * (2 * wbar β V + theta V * β) := by
      simp only [w0] at h1
      rw [div_eq_iff hden.ne'] at h1
      linarith
    have h3 : 2 * (1 + theta V) = 2 * wbar β V + theta V * β := by
      have := mul_left_cancel₀ hwb.ne' (show wbar β V * (2 * (1 + theta V)) =
        wbar β V * (2 * wbar β V + theta V * β) by linarith)
      exact this
    have h4 : theta V * β = 0 := by
      simp only [wbar] at h3
      linarith
    have h5 : theta V = 0 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact h
      · exact absurd h hβ0.ne'
    apply hV1
    simp only [theta] at h5
    have : 1 / V = 1 := by linarith
    rw [div_eq_one_iff_eq hV.ne'] at this
    exact this.symm

/-! ### Links to the finite-tree versions (`V = 1`) -/

namespace Link

open ExpectationsFiniteTree TreeBridge HouseholdMeasure.TreeLink

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), eq. (19.31), p. 450, **link to the finite tree**: on a finite event tree (as
a probability space through `ExpectationsMeasure.TreeBridge.treeSystem`), with `V = 1`, an
optimum of the measure-theoretic cash-in-advance problem consuming the endowment, with
`Λ_0 = u'(y_0)`, has `Λ_t = βᵗu'(y_t)` at every node: exactly the conclusion of
`CashInAdvance.TreeEuler.sdf_eq`. -/
theorem link_sdf_eq {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {Λ P y s : ℕ → Ω' → ℝ} {N0 a0 : Ω' → ℝ} {m a : ℕ → Ω' → ℝ}
    (hopt : CIAOptimal (treeSystem T) β u 1 Λ P y s N0 a0 y m a)
    (hΛa : ∀ t ω ω', T.info t ω' ω → Λ t ω' = Λ t ω)
    (hPa : ∀ t ω ω', T.info t ω' ω → P t ω' = P t ω) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hP : ∀ t ω, 0 < P t ω) {δ : ℝ} (hδ : 0 < δ) (hmδ : ∀ t ω, δ ≤ m t ω)
    (hrate : ∀ t ω, bondPrice (treeSystem T) Λ P t ω ≤ 1) (hne : ∀ t ω, u' (y t ω) ≠ 0)
    (hnorm : ∀ ω, Λ 0 ω = u' (y 0 ω)) (t : ℕ) :
    Λ t = β ^ t • fun ω => u' (y t ω) := by
  funext ω
  exact forall_of_ae T (lambda_derived_V1 hβ hu hu' hopt (priceRegular T hΛa hPa hΛ hP)
    (fun n => bddAt_of_finite T _) (fun n => bddAt_of_finite T _) hδ
    (fun t => Eventually.of_forall (hmδ t)) (fun t => Eventually.of_forall (hrate t)) hne hnorm
    t) ω

/-- Cochrane (2023), eq. (19.32), p. 450, **link to the core bond price**: under the hypotheses of
`link_sdf_eq` and `u' > 0` at the plan, the derived `Λ_t = βᵗu'(y_t)` feeds
`CashInAdvance.Stochastic.bond_price_19_32` for the tree's core `ExpectationSystem`, whose
conclusion (that of `CashInAdvance.TreeEuler.bond_price_from_optimality`) holds for the bond
price `Q_t = E_t[pk_{t+1}]/pk_t`: `Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]` at every
node. -/
theorem link_bond_price {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {Λ P y s : ℕ → Ω' → ℝ} {N0 a0 : Ω' → ℝ} {m a : ℕ → Ω' → ℝ}
    (hopt : CIAOptimal (treeSystem T) β u 1 Λ P y s N0 a0 y m a)
    (hΛa : ∀ t ω ω', T.info t ω' ω → Λ t ω' = Λ t ω)
    (hPa : ∀ t ω ω', T.info t ω' ω → P t ω' = P t ω) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hP : ∀ t ω, 0 < P t ω) {δ : ℝ} (hδ : 0 < δ) (hmδ : ∀ t ω, δ ≤ m t ω)
    (hrate : ∀ t ω, bondPrice (treeSystem T) Λ P t ω ≤ 1) (hpos : ∀ t ω, 0 < u' (y t ω))
    (hnorm : ∀ ω, Λ 0 ω = u' (y 0 ω)) (t : ℕ) :
    bondPrice (treeSystem T) Λ P t = β • T.toExpectationSystem.E t
      ((fun ω => u' (y (t + 1) ω)) / (fun ω => u' (y t ω)) * (P t / P (t + 1))) := by
  have hp := priceRegular T hΛa hPa hΛ hP
  have hya := hopt.1.2.1
  have hucA : T.toExpectationSystem.Adapted (fun t ω => u' (y t ω)) := by
    intro τ
    rw [FiniteTree.toExpectationSystem_E]
    funext ω
    exact T.condE_of_const_on_cell fun ω' h => by
      change u' (y τ ω') = u' (y τ ω)
      rw [cell_const T (hya τ) h]
  have hPA : T.toExpectationSystem.Adapted P := by
    intro τ
    rw [FiniteTree.toExpectationSystem_E]
    funext ω
    exact T.condE_of_const_on_cell fun ω' h => hPa τ ω ω' h
  have hQ : ∀ t, Λ t * bondPrice (treeSystem T) Λ P t / P t =
      T.toExpectationSystem.E t (Λ (t + 1) / P (t + 1)) := by
    intro t
    funext ω
    have h := hp.E_pk_eq t ω
    rw [treeSystem_E] at h
    have e : Λ (t + 1) / P (t + 1) = pk Λ P (t + 1) := rfl
    rw [e, FiniteTree.toExpectationSystem_E, h]
    have := (hP t ω).ne'
    simp only [Pi.div_apply, Pi.mul_apply, pk]
    field_simp
  exact CashInAdvance.Stochastic.bond_price_19_32 T.toExpectationSystem (Λ := Λ) (P := P)
    (Q := bondPrice (treeSystem T) Λ P) (finiteTree_pullOut T) hβ hpos hucA
    (link_sdf_eq T hβ hu hu' hopt hΛa hPa hΛ hP hδ hmδ hrate (fun t ω => (hpos t ω).ne') hnorm)
    hPA hP hQ t

/-- Cochrane (2023), §19.5.1, p. 449, and footnote 1, p. 440, **link to the finite tree
(optimality)**: on a finite event tree with one root node, for concave `u` with `u' > 0` at the
plan and `V = 1`, an optimum of the measure-theoretic cash-in-advance problem (flow budget almost
surely, cash-in-advance and no-Ponzi constraints) consuming the endowment is optimal in the
present-value tree problem `CashInAdvance.TreeEuler.IsOptimal` with wealth equal to its own
present-value cost (when summable), and hence, through `LinksTidy.TreeBridge`, in the footnote-1
time-0 problem `MoneyInUtility.FootnoteTree.TOptimal`. -/
theorem link_isOptimal {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') (hconc : ∀ x x', u x' ≤ u x + u' x * (x' - x))
    {Λ P y s : ℕ → Ω' → ℝ} {N0 a0 : Ω' → ℝ} {m a : ℕ → Ω' → ℝ}
    (hopt : CIAOptimal (treeSystem T) β u 1 Λ P y s N0 a0 y m a)
    (hΛa : ∀ t ω ω', T.info t ω' ω → Λ t ω' = Λ t ω)
    (hPa : ∀ t ω ω', T.info t ω' ω → P t ω' = P t ω) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hP : ∀ t ω, 0 < P t ω) {δ : ℝ} (hδ : 0 < δ) (hmδ : ∀ t ω, δ ≤ m t ω)
    (hrate : ∀ t ω, bondPrice (treeSystem T) Λ P t ω ≤ 1) (hpos : ∀ t ω, 0 < u' (y t ω))
    (htriv : ∀ a b, T.info 0 a b) (hcost : Summable (CashInAdvance.TreeEuler.pvCost T Λ y)) :
    CashInAdvance.TreeEuler.IsOptimal T β u Λ (∑' t, CashInAdvance.TreeEuler.pvCost T Λ y t) y ∧
      MoneyInUtility.FootnoteTree.TOptimal T β (fun x _ => u x) Λ (fun _ _ => 0)
        (∑' t, CashInAdvance.TreeEuler.pvCost T Λ y t) y (fun _ _ => 0) := by
  have hp := priceRegular T hΛa hPa hΛ hP
  have hya := hopt.1.2.1
  obtain ⟨ω₀⟩ : Nonempty Ω' := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := T.prob_sum
    simp at this
  set lam := u' (y 0 ω₀) / Λ 0 ω₀ with hlam
  have hfoc : ∀ τ ω, β ^ τ * u' (y τ ω) = lam * Λ τ ω := by
    intro τ ω
    have h := forall_of_ae T (multiplier_const hβ hu hu' one_pos hopt hp
      (fun n => bddAt_of_finite T _) (fun n => bddAt_of_finite T _) hδ
      (fun t => Eventually.of_forall (hmδ t)) (fun t => Eventually.of_forall (hrate t)) τ) ω
    simp only [wedge_V1, mul_one] at h
    have e1 : y 0 ω = y 0 ω₀ := cell_const T (hya 0) (htriv ω ω₀)
    have e2 : Λ 0 ω = Λ 0 ω₀ := hΛa 0 ω₀ ω (htriv ω ω₀)
    rw [e1, e2] at h
    have := (hΛ τ ω).ne'
    rw [hlam, ← h]
    field_simp
  have hadm := hopt.2.2.1
  have hus : Summable (fun t => β ^ t * ∑ ω, T.prob ω * u (y t ω)) := by
    have := (hadm.hasSum hβ).summable
    refine this.congr fun k => ?_
    change β ^ k * ∫ ω, u (y k ω) ∂(treeProb T : MeasureTheory.Measure Ω') = _
    rw [integral_treeProb]
  have hopt' := CashInAdvance.TreeEuler.euler_sufficient T hβ.le
    (div_nonneg (hpos 0 ω₀).le (hΛ 0 ω₀).le) (du := fun τ ω => u' (y τ ω))
    (fun τ ω x => hconc (y τ ω) x) hfoc
    ⟨fun t ω ω' h => cell_const T (hya t) h, hus, hcost, le_rfl⟩ rfl
  exact ⟨hopt', (LinksTidy.TreeBridge.isOptimal_iff_tOptimal T).mp hopt'⟩

/-- Cochrane (2023), §19.5.1, p. 449, and p. 453, **link from the finite tree (optimality)**: on
a finite event tree with one root node, for concave `u` with `u' > 0` at the plan and `V = 1`,
a plan consuming a nonnegative endowment that is optimal in the present-value tree problem
`CashInAdvance.TreeEuler.IsOptimal` (any wealth `W`) and, with the binding overnight money
`m = y`, feasible, admissible and transversal in the measure-theoretic problem, with
nonnegative nominal rates, is optimal in the measure-theoretic cash-in-advance problem. With
`link_isOptimal` the two optimality notions coincide on such trees. -/
theorem link_optimal_of_isOptimal {β : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hconc : ∀ x x', u x' ≤ u x + u' x * (x' - x))
    {Λ P y s : ℕ → Ω' → ℝ} {N0 a0 : Ω' → ℝ} {m a : ℕ → Ω' → ℝ} {W : ℝ}
    (htopt : CashInAdvance.TreeEuler.IsOptimal T β u Λ W y)
    (hΛa : ∀ t ω ω', T.info t ω' ω → Λ t ω' = Λ t ω)
    (hPa : ∀ t ω ω', T.info t ω' ω → P t ω' = P t ω) (hΛ : ∀ t ω, 0 < Λ t ω)
    (hP : ∀ t ω, 0 < P t ω) (htriv : ∀ a b, T.info 0 a b) (hpos : ∀ t ω, 0 < u' (y t ω))
    (hy0 : ∀ t ω, 0 ≤ y t ω) (hf : Feasible (treeSystem T) Λ P y s N0 a0 y m a)
    (hm : ∀ t ω, m t ω = y t ω) (hrate : ∀ t ω, bondPrice (treeSystem T) Λ P t ω ≤ 1)
    (hadm : UAdmissible (treeSystem T) β (fun n ω => u (y n ω)))
    (htvc : Tendsto (wealthPV (treeSystem T) Λ P N0 m a) atTop (𝓝 0)) :
    CIAOptimal (treeSystem T) β u 1 Λ P y s N0 a0 y m a := by
  have hp := priceRegular T hΛa hPa hΛ hP
  obtain ⟨ω₀⟩ : Nonempty Ω' := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := T.prob_sum
    simp at this
  have hya := hf.2.1
  have hΛm : CashInAdvance.TreeEuler.Meas T Λ := fun t ω ω' h => hΛa t ω' ω h
  refine optimal_of_foc (u' := u') hβ hconc hp (fun t => Integrable.of_finite)
    (fun t => Integrable.of_finite) (lam := u' (y 0 ω₀) / Λ 0 ω₀)
    (div_nonneg (hpos 0 ω₀).le (hΛ 0 ω₀).le) hf
    (fun t => Eventually.of_forall fun ω => ⟨by rw [hm]; norm_num, by rw [hm]; exact hy0 t ω⟩)
    hadm (fun t => Eventually.of_forall fun ω => by rw [hm]; norm_num)
    (fun t => Eventually.of_forall fun ω => by simp only [iota]; linarith [hrate t ω])
    (fun t => Eventually.of_forall fun ω => ?_) htvc
  have h := CashInAdvance.TreeEuler.sdf_19_31 T hβ htopt hΛm hΛ (fun t ω => hu (y t ω))
    (fun t ω => (hpos t ω).ne') 0 t ω
  rw [zero_add] at h
  have e1 : y 0 ω = y 0 ω₀ := cell_const T (hya 0) (htriv ω ω₀)
  have e2 : Λ 0 ω = Λ 0 ω₀ := hΛa 0 ω₀ ω (htriv ω ω₀)
  rw [e1, e2] at h
  rw [wedge_V1, mul_one]
  have h0 := (hΛ 0 ω₀).ne'
  have h1 := (hpos 0 ω₀).ne'
  rw [div_eq_div_iff h0 h1] at h
  field_simp
  linarith

end Link

/-! ### The i.i.d. economy (`V = 1`) -/

namespace IID

open ExpectationsMeasureIID MoneyInUtilityMeasure.IID

variable (ν : ProbabilityMeasure ℝ)

/-- Cochrane (2023), §19.5.2, p. 450: the price level `P_t = 2ᵗ` (inflation keeps nominal rates
positive). -/
def infl (t : ℕ) (_ : ℕ → ℝ) : ℝ := 2 ^ t

/-- Cochrane (2023), (19.27), p. 449: the transfers that make the endowment plan satisfy the flow
constraint with no bonds and binding overnight money `m = y` (`V = 1`), `M_{−1} = 0`. -/
noncomputable def ciaTaxes (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (moneyIn (fun _ => 0) infl endow t ω - infl t ω * endow t ω) / infl t ω

/-- Cochrane (2023), (19.31)–(19.32), p. 450: in the i.i.d. economy with `P_t = 2ᵗ`,
`E_t pk_{t+1} = β^{t+1}(4 − ȳ)/2^{t+1}`. -/
theorem E_pk_infl (β : ℝ) (t : ℕ) :
    (iidSystem ν).E t (pk (lam β) infl (t + 1)) =ᵐ[(iidSystem ν).μ]
      fun _ => β ^ (t + 1) * (4 - ybar ν) / 2 ^ (t + 1) := by
  set f : ℝ → ℝ := fun x => β ^ (t + 1) * (4 - (2 + clamp x / 2)) / 2 ^ (t + 1) with hf
  have hfm : Measurable f :=
    ((((continuous_clamp.measurable.div_const 2).const_add 2).const_sub 4).const_mul
      _).div_const _
  have e : pk (lam β) infl (t + 1) = fun ω => f (ω (t + 1)) := rfl
  rw [e]
  filter_upwards [E_shock_fun ν t hfm] with ω h
  rw [h]
  have hi : Integrable clamp (ν : Measure ℝ) :=
    Integrable.of_bound continuous_clamp.measurable.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_clamp_le x)
  have e2 : (fun x => f x) = fun x => (β ^ (t + 1) * 2 / 2 ^ (t + 1)) -
      (β ^ (t + 1) / 2 / 2 ^ (t + 1)) * clamp x := by
    funext x
    simp only [hf]
    ring
  simp only [e2]
  rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul,
    probReal_univ, one_smul, ybar]
  ring

/-- Cochrane (2023), p. 449: the i.i.d. state prices and the price level `2ᵗ` are regular. -/
theorem infl_priceRegular {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    PriceRegular (iidSystem ν) (lam β) infl := by
  have h := iid_priceRegular (ν := ν) hβ0 hβ1
  exact ⟨h.1, fun _ => stronglyMeasurable_const, h.2.2.1, fun t _ => pow_pos two_pos t,
    fun t => ⟨(h.2.2.2.2 t).1, (h.2.2.2.2 t).2.1, BddAt.const (2 ^ t),
      ⟨1, Eventually.of_forall fun _ => by
        simp only [infl]
        rw [abs_of_pos (by positivity)]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))⟩⟩⟩

/-- Cochrane (2023), §19.5.2, p. 450: in the i.i.d. economy with `P_t = 2ᵗ` nominal rates are
positive, `Q_t = β(4 − ȳ)/(2(4 − y_t)) ≤ 1`. -/
theorem infl_bondPrice_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, bondPrice (iidSystem ν) (lam β) infl t ω ≤ 1 := by
  have hyb := ybar_bounds ν
  filter_upwards [E_pk_infl ν β t] with ω h
  have hpk : pk (lam β) infl t ω = lam β t ω / 2 ^ t := rfl
  simp only [bondPrice, h, hpk, lam]
  have h1 := endow_bounds t ω
  have hb := pow_pos hβ0 t
  have h4 : 0 < 4 - endow t ω := by linarith
  rw [div_le_one (by positivity)]
  rw [pow_succ, pow_succ]
  have : (4 - ybar ν) ≤ 5 / 2 := by linarith [hyb.1]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have key : β * (4 - ybar ν) ≤ 2 * (4 - endow t ω) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left key (mul_pos hb (pow_pos (two_pos : (0 : ℝ) < 2) t)).le
  nlinarith [h2]

variable {ν}

/-- Cochrane (2023), §19.5.1–19.5.2, pp. 448–450, **the i.i.d. cash-in-advance economy** with
`V = 1`: on `ExpectationsMeasureIID.iidSystem ν`, with `0 < β < 1`, utility `u(c) = 4c − c²/2`,
the price level `P_t = 2ᵗ`, state prices `Λ_t = βᵗ(4 − y_t)` and transfers `ciaTaxes`,
consuming the endowment with the binding overnight money `m_t = y_t` and no bonds is optimal
(`optimal_of_foc`). -/
theorem iid_optimal {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    CIAOptimal (iidSystem ν) β (fun x => 4 * x - x ^ 2 / 2) 1 (lam β) infl endow ciaTaxes
      (fun _ => 0) (fun _ => 0) endow endow (fun _ _ => 0) := by
  set S := iidSystem ν with hS
  have hp := infl_priceRegular ν hβ0 hβ1
  have hyb := ybar_bounds ν
  have hlpos : ∀ t ω, 0 < lam β t ω := fun t ω => lam_pos hβ0 t ω
  have hlm : ∀ t, StronglyMeasurable[S.𝓕 t] (lam β t) := hp.1
  have hym : ∀ t, StronglyMeasurable[S.𝓕 t] (endow t) := fun t => measurable_endow ν t
  have ae : ∀ {k : ℕ} {f : (ℕ → ℝ) → ℝ}, StronglyMeasurable[S.𝓕 k] f →
      AEStronglyMeasurable f S.μ := fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hlb : ∀ t ω, |lam β t ω| ≤ 5 / 2 := fun t ω => by
    have h1 := endow_bounds t ω
    have hb : β ^ t ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    rw [abs_of_pos (hlpos t ω)]
    simp only [lam]
    nlinarith [pow_pos hβ0 t]
  have hyb' : ∀ t ω, |endow t ω| ≤ 5 / 2 := fun t ω => by
    have h1 := endow_bounds t ω
    rw [abs_le]
    constructor <;> linarith
  have hint : ∀ {k : ℕ} {f : (ℕ → ℝ) → ℝ} {K : ℝ}, StronglyMeasurable[S.𝓕 k] f →
      (∀ ω, |f ω| ≤ K) → Integrable f S.μ :=
    fun {k} {f} {K} hm h => (BddAt.integrable ⟨K, Eventually.of_forall h⟩ (ae hm))
  have hmIn : ∀ t ω, moneyIn (fun _ => (0 : ℝ)) infl endow t ω =
      if t = 0 then 0 else 2 ^ (t - 1) * endow (t - 1) ω := by
    intro t ω
    cases t with
    | zero => simp [moneyIn]
    | succ k => simp [moneyIn, infl]
  have hmInm : ∀ t, StronglyMeasurable[S.𝓕 t] (moneyIn (fun _ => (0 : ℝ)) infl endow t) := by
    intro t
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ k =>
      exact (stronglyMeasurable_const.mul (hym k)).mono (S.𝓕.mono (Nat.le_succ k))
  have hmInb : ∀ t ω, |moneyIn (fun _ => (0 : ℝ)) infl endow t ω| ≤ 2 ^ t * (5 / 2) := by
    intro t ω
    rw [hmIn]
    split_ifs with h
    · simp only [abs_zero]
      positivity
    · rw [abs_mul, abs_of_pos (by positivity)]
      have := hyb' (t - 1) ω
      have h2 : (2 : ℝ) ^ (t - 1) ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (Nat.sub_le t 1)
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (t - 1), abs_nonneg (endow (t - 1) ω)]
  have hpk : ∀ t ω, pk (lam β) infl t ω = lam β t ω / 2 ^ t := fun t ω => rfl
  -- feasibility
  have hflow : Flow S (lam β) infl endow ciaTaxes (fun _ => 0) endow endow
      (fun _ _ => 0) := by
    intro t
    refine Eventually.of_forall fun ω => ?_
    have e0 : S.E t (fun _ => (0 : ℝ)) = 0 := S.E_zero t
    have hP : infl t ω ≠ 0 := (pow_pos two_pos t).ne'
    simp only [claimCost, mul_zero, e0, ciaTaxes, Pi.zero_apply, zero_div, sub_self, zero_add]
    field_simp
    ring
  have hfeas : Feasible S (lam β) infl endow ciaTaxes (fun _ => 0) (fun _ => 0) endow endow
      (fun _ _ => 0) := by
    refine ⟨rfl, hym, hym, fun _ => stronglyMeasurable_const, hflow, fun t => by simp,
      fun t => ?_, fun t => ?_, fun t => ?_, fun δ hδ => Eventually.of_forall fun T => ?_⟩
    · refine hint (k := t) (K := 5 / 2 * (2 ^ t * (5 / 2)))
        ((hp.stronglyMeasurable_pk t).mul (hmInm t)) fun ω => ?_
      rw [abs_mul, hpk, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ t)]
      have h1 : |lam β t ω| / 2 ^ t ≤ 5 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hlb t ω, one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := t)]
      exact mul_le_mul h1 (hmInb t ω) (abs_nonneg _) (by norm_num)
    · refine hint (k := t) (K := 5 / 2 * (5 / 2)) ((hlm t).mul (hym t)) fun ω => ?_
      rw [abs_mul]
      exact mul_le_mul (hlb t ω) (hyb' t ω) (abs_nonneg _) (by norm_num)
    · refine hint (k := t) (K := 5 / 2 * (5 / 2)) ((hlm t).mul (hym t)) fun ω => ?_
      rw [abs_mul]
      exact mul_le_mul (hlb t ω) (hyb' t ω) (abs_nonneg _) (by norm_num)
    · refine le_trans (by linarith) (integral_nonneg fun ω => ?_)
      rw [zero_add]
      refine mul_nonneg (hp.pk_pos T ω).le ?_
      rw [hmIn]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (by positivity) (by linarith [(endow_bounds (T - 1) ω).1])
  -- admissibility
  have hadm : UAdmissible S β (fun n ω => 4 * endow n ω - endow n ω ^ 2 / 2) := by
    refine UAdmissible.of_bdd hβ0.le hβ1 (fun n => ae (k := n)
      ((measurable_const.mul (hym n).measurable).sub
        (((hym n).measurable.pow_const 2).div_const 2)).stronglyMeasurable)
      (K := 20) fun n ω => ?_
    have h1 := abs_le.1 (hyb' n ω)
    rw [abs_le]
    constructor <;> nlinarith
  -- transversality
  have htvc : Tendsto (wealthPV S (lam β) infl (fun _ => 0) endow (fun _ _ => 0)) atTop
      (𝓝 0) := by
    have hb : ∀ T, ‖wealthPV S (lam β) infl (fun _ => 0) endow (fun _ _ => 0) T‖ ≤
        7 * β ^ T := by
      intro T
      have h := norm_integral_le_of_norm_le_const (μ := S.μ) (C := 7 * β ^ T)
        (f := fun ω => pk (lam β) infl T ω * ((fun _ _ => (0 : ℝ)) T ω +
          moneyIn (fun _ => 0) infl endow T ω))
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, zero_add, hpk, hmIn]
          have h1 := endow_bounds T ω
          split_ifs with hT
          · simp only [mul_zero, abs_zero]
            positivity
          · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            have h2 := endow_bounds k ω
            have e : lam β (k + 1) ω / 2 ^ (k + 1) * (2 ^ k * endow k ω) =
                β ^ (k + 1) * (4 - endow (k + 1) ω) * endow k ω / 2 := by
              simp only [lam]
              field_simp
              ring
            rw [e, abs_of_pos (by
              have := pow_pos hβ0 (k + 1)
              apply div_pos _ two_pos
              apply mul_pos (mul_pos this (by linarith)) (by linarith))]
            have := pow_pos hβ0 (k + 1)
            rw [div_le_iff₀ two_pos]
            nlinarith [mul_le_mul (show 4 - endow (k + 1) ω ≤ 5 / 2 by linarith)
              (show endow k ω ≤ 5 / 2 by linarith) (by linarith) (by norm_num)])
      rw [probReal_univ, mul_one] at h
      exact h
    have hlim : Tendsto (fun T : ℕ => 7 * β ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul 7
    exact squeeze_zero_norm hb hlim
  refine optimal_of_foc (u' := fun x => 4 - x) hβ0 (fun x x' => by nlinarith [sq_nonneg (x' - x)])
    hp (fun t => ?_) (fun t => ?_) zero_le_one hfeas ?_ hadm
    (fun t => Eventually.of_forall fun ω => by ring) (fun t => ?_)
    (fun t => Eventually.of_forall fun ω => ?_) htvc
  · refine hint (k := t) (K := 5 / 2 * (5 / 2)) ((hlm t).mul (hym t)) fun ω => ?_
    rw [abs_mul]
    exact mul_le_mul (hlb t ω) (hyb' t ω) (abs_nonneg _) (by norm_num)
  · have hsm : StronglyMeasurable[S.𝓕 t] (ciaTaxes t) :=
      ((hmInm t).sub (stronglyMeasurable_const.mul (hym t))).div stronglyMeasurable_const
    refine hint (k := t) (K := 5 / 2 * (5 + 5 / 2)) ((hlm t).mul hsm) fun ω => ?_
    rw [abs_mul]
    refine mul_le_mul (hlb t ω) ?_ (abs_nonneg _) (by norm_num)
    have hP : (0 : ℝ) < 2 ^ t := by positivity
    simp only [ciaTaxes, infl]
    rw [abs_div, abs_of_pos hP, div_le_iff₀ hP]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hP]
    nlinarith [hmInb t ω, hyb' t ω]
  · intro t
    exact Eventually.of_forall fun ω => ⟨by norm_num, by linarith [(endow_bounds t ω).1]⟩
  · filter_upwards [infl_bondPrice_le ν hβ0 hβ1 t] with ω h
    simp only [iota]
    linarith
  · rw [wedge_V1]
    simp only [lam]
    ring

/-- Cochrane (2023), eqs. (19.31)–(19.32), p. 450, **derived on the i.i.d. economy** (`V = 1`):
the necessity theorems apply to the optimum of `iid_optimal`: the state prices are
`Λ_t = βᵗu'(y_t)` (derived, `lambda_derived_V1`) and
`Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]` (`bond_1932_V1`), almost surely. -/
theorem iid_sdf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) :
    (∀ᵐ ω ∂(iidSystem ν).μ, lam β t ω = β ^ t * (4 - endow t ω)) ∧
      ∀ᵐ ω ∂(iidSystem ν).μ, bondPrice (iidSystem ν) (lam β) infl t ω =
        (iidSystem ν).E t (fun ω => β * ((4 - endow (t + 1) ω) / (4 - endow t ω)) *
          (infl t ω / infl (t + 1) ω)) ω := by
  have hopt := iid_optimal (ν := ν) hβ0 hβ1
  have hp := infl_priceRegular ν hβ0 hβ1
  have hyb : ∀ n, BddAt (iidSystem ν) (endow n) := fun n => ⟨5 / 2, Eventually.of_forall
    fun ω => by have h1 := endow_bounds n ω; rw [abs_le]; constructor <;> linarith⟩
  have hne : ∀ t ω, (fun x : ℝ => 4 - x) (endow t ω) ≠ 0 := fun t ω => by
    have := (endow_bounds t ω).2
    simp only
    linarith
  have hδ : ∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, (3 / 2 : ℝ) ≤ endow t ω := fun t =>
    Eventually.of_forall fun ω => (endow_bounds t ω).1
  have hrate : ∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, bondPrice (iidSystem ν) (lam β) infl t ω ≤ 1 :=
    fun t => infl_bondPrice_le ν hβ0 hβ1 t
  refine ⟨lambda_derived_V1 hβ0 (u := fun x => 4 * x - x ^ 2 / 2) (fun x => ?_)
      (continuous_const.sub continuous_id) hopt hp hyb hyb (by norm_num) hδ hrate hne
      (fun ω => by simp [lam]) t,
    bond_1932_V1 hβ0 (u := fun x => 4 * x - x ^ 2 / 2) (fun x => ?_)
      (continuous_const.sub continuous_id) hopt hp hyb hyb (by norm_num) hδ hrate hne t⟩
  all_goals exact (((hasDerivAt_id' x).const_mul 4).sub ((hasDerivAt_pow 2 x).div_const
    2)).congr_deriv (by simp)

end IID

end Cochrane.Monetarism.CashInAdvanceMeasure
