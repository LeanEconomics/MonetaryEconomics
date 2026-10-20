/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.Regimes
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Monetarism.ExpectationsFiniteTree

/-!
# Money in the utility function

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 438–445,
eqs. (19.9)–(19.23) and Figure 19.1.

## Main results

* Budget constraints (19.10)–(19.12): `HHFlow`, `hhFlow_iff_flow`, `eq1911_iff_tvc` (the present
  value budget constraint (19.11) holds iff the transversality condition does), `eq1912_of_tvc`,
  `equilibrium_valuation` (with `c = y` the household's (19.12) is the government's (19.3)).
* First-order conditions (19.13)–(19.14), from the time-0 problem of footnote 1 (perfect
  foresight, genuine infinite horizon, no Lagrange-multiplier theorem assumed): `Feasible`,
  `Optimal`, `tsum_modify_two`, `perturb_le`, `foc_cc`, `foc_mc`, `foc_1913_1914` (with
  `λ = u_c(c_0, m_0)`, as in the footnote); sufficiency under concavity: `concave_le_tangent`,
  `supergradient_of_concave`, `optimal_of_foc`.
* Footnote 1 under uncertainty, on a finite event tree (genuine infinite horizon): `FootnoteTree`
  (`TAdapted`, `dateCost`, `dateUtil`, `TFeasible`, `TOptimal`, `cell`, `cell_adapted`,
  `sum_perturb_cell`, `perturb_adapted`, `tperturb_le`), node first-order conditions by
  cost-neutral perturbations at a node, `tree_foc_cc`, `tree_foc_mc`, `tree_foc_1913_1914`,
  `lambda_const`, and sufficiency under concavity `tree_optimal_of_foc`.
* Knownness of `Λ_t/P_t` and `P_t/u_c(t)`: `known_mul`, `known_inv`, `known_div` (with
  pull-out, products, reciprocals of nowhere-zero and quotients of known variables are known, on
  any state space), `known_prod`, `functionsKnown_of_fintype` (on a finite state space, every
  function of a known variable is known), `known_div_of_fintype` (no nonvanishing needed), and
  versions without the knownness hypotheses, on any state space: `eq1911_iff_tvc_adapted`,
  `eq1912_of_tvc_adapted`, `value_of_money_iterated_adapted`, `value_of_money_limit_adapted`.
* (19.15)–(19.16) and the value of money: `convenience_identity`
  (`1 = u_m/u_c + E_tβu_c'P/(u_cP')`), `value_recursion`, `value_of_money_iterated` (the iterated
  formula of p. 441), `value_of_money_limit`; money demand `lm_unique`, `lm_exists`.
* Separable perfect foresight (19.17)–(19.19): `price_ratio_eq`, `eq1918_iff`, `IsMIUPath`,
  `steady_state_path_iff`, `steady_state_inflation`, `steady_state_existsUnique`; the second
  (zero-rate) steady state `zero_rate_iff`, `deflation_approx`, satiation
  `satiation_absorbing`, `limit_rate_zero`, `money_demand_correspondence`.
* Power utility (19.20)–(19.23): `hasDerivAt_power`, `power_money_demand`, `power_um_ratio`,
  `IsPowerPath`, `eq1922`, `eq1922_exact`, `eq1922_partial_delta`, `eq1922_partial_mu`,
  `eq1922_approx`; calibration `calib_unit`, `calib_ten`, `calib_ten_gamma_one`,
  `calib_ten_gamma_two` (imprecision: `θ ≈ 0.01` needs `γ = 1`), `calib_interest_cost`;
  (19.23) `nextX`, `eq1923_iff`, `inflation_eq1923`.
* Figure 19.1 (`δ = µ = 0.2`, `γ = 2`, `θ = 0.01`): `fig191_steady`, `fig191_xbar_bounds`
  (`x̄ ≈ 5.53`), `nextX_hasDerivAt`, `slope_gt_one` (cuts from below), `fig191_slope`
  (`1.88`), `fig191_pole` (pole at `x = 10`), `deflation_limit` (`P_{t+1}/P_t → 1/(1 + δ)`).
* Survey error E13: `e13_corrected` (the deflationary steady state attracts, `x̄` exists and
  `x_{t+1}/x_t → β/(1 + µ) < 1`, iff `1 + µ > β`, not `1 + µ > 1/β`), `e13_printed_fails`.
* p. 445: `fiscal_determines_path` (active fiscal policy pins `P_0`, hence the whole path).
-/

namespace Cochrane.Monetarism.MoneyInUtility

open Filter Topology
open Cochrane.Monetarism.ForwardSolution (Solves iterate_A15)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (19.10)–(19.12): budget constraints -/

/-- Cochrane (2023), eq. (19.10), p. 439: the household's period budget constraint
`B_{t−1} + M_{t−1} + P_t(y_t − c_t) = Q_tB_t + M_t + P_ts_t` (`Bm t = B_{t−1}`,
`N t = M_{t−1}`). -/
def HHFlow (Bm N P y c s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Bm t + N t + P t * (y t - c t) = Q t * Bm (t + 1) + N (t + 1) + P t * s t

/-- Cochrane (2023), (19.10), p. 439: the household constraint is the government's flow
constraint with surplus replaced by `s + c − y`. -/
theorem hhFlow_iff_flow {Bm N P y c s Q : ℕ → Ω → ℝ} :
    HHFlow Bm N P y c s Q ↔ Regimes.Flow Bm N P (fun t => s t + c t - y t) Q := by
  constructor
  · intro h t
    rw [← sub_eq_zero]
    have := h t
    rw [← sub_eq_zero] at this
    rw [← this]
    ring
  · intro h t
    rw [← sub_eq_zero]
    have := h t
    rw [← sub_eq_zero] at this
    rw [← this]
    ring

/-- Cochrane (2023), eq. (19.11), p. 439 ("their optimal choices include transversality
conditions. Thereby the household must satisfy the present value budget constraints"): given
the period constraint (19.10) and bond pricing, (19.11) holds (as the limit of partial sums,
multiplied by `Λ_t`) if and only if the transversality condition
`E_t[Λ_{t+T}B_{t+T−1}/P_{t+T}] → 0` holds. -/
theorem eq1911_iff_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => Regimes.partial192 𝔼 Λ P N (fun k => s k + c k - y k) t T ω) atTop
        (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) :=
  Regimes.flow_pv_iff_tvc 𝔼 hPO hBP hφ hBa hB hQ hi hP (hhFlow_iff_flow.mp hflow) t ω

/-- Cochrane (2023), eq. (19.12), p. 439: with both transversality conditions the household's
present-value budget constraint holds in the form (19.12). -/
theorem eq1912_of_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) {t : ℕ} {ω : Ω}
    (hbond : Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0))
    (hmoney : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => Regimes.partial193 𝔼 Λ P N i (fun k => s k + c k - y k) t T ω) atTop
      (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) :=
  Regimes.flow_eq193_of_tvc 𝔼 hPO hBP hφ hBa hB hNa hN hQ hi hP (hhFlow_iff_flow.mp hflow)
    hbond hmoney

/-- Cochrane (2023), p. 440 ("The eventual government debt valuation equation results from the
consumer's budget constraint, and equilibrium `c_t = y_t`"): with `c = y` the household's
(19.12) is the government's valuation equation (19.3). -/
theorem equilibrium_valuation {Λ P N i y s : ℕ → Ω → ℝ} (t T : ℕ) :
    Regimes.partial193 𝔼 Λ P N i (fun k => s k + y k - y k) t T =
      Regimes.partial193 𝔼 Λ P N i s t T := by
  simp only [add_sub_cancel_right]

/-! ### (19.13)–(19.14): first-order conditions of the time-0 problem (footnote 1) -/

/-- Cochrane (2023), p. 440, footnote 1 (perfect foresight): a plan of consumption `c` and real
money `m = M/P` is feasible when its cost `∑ q_t(c_t + ι_tm_t)` converges and is at most wealth
`W`; `q_t = Λ_t/Λ_0` and `ι_t = i_t/(1 + i_t)`. -/
def Feasible (q ι : ℕ → ℝ) (W : ℝ) (c m : ℕ → ℝ) : Prop :=
  Summable (fun t => q t * (c t + ι t * m t)) ∧ ∑' t, q t * (c t + ι t * m t) ≤ W

/-- Cochrane (2023), (19.9), p. 439 and footnote 1, p. 440: an optimal plan maximises
`∑βᵗu(c_t, m_t)` over feasible plans with summable utility. -/
def Optimal (β : ℝ) (u : ℝ → ℝ → ℝ) (q ι : ℕ → ℝ) (W : ℝ) (c m : ℕ → ℝ) : Prop :=
  Feasible q ι W c m ∧ Summable (fun t => β ^ t * u (c t) (m t)) ∧
    ∀ c' m', Feasible q ι W c' m' → Summable (fun t => β ^ t * u (c' t) (m' t)) →
      ∑' t, β ^ t * u (c' t) (m' t) ≤ ∑' t, β ^ t * u (c t) (m t)

/-- Cochrane (2023), footnote 1, p. 440 (perturbation tool): changing a summable sequence at two
dates keeps it summable and changes its sum by the two changes. -/
theorem tsum_modify_two {f g : ℕ → ℝ} {t s : ℕ} (hts : t ≠ s)
    (hfg : ∀ k, k ≠ t → k ≠ s → g k = f k) (hf : Summable f) :
    Summable g ∧ ∑' k, g k = ∑' k, f k + (g t - f t) + (g s - f s) := by
  have hz : ∀ k ∉ ({t, s} : Finset ℕ), (g - f) k = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp [hfg k hk.1 hk.2]
  have hs : Summable (g - f) := summable_of_ne_finset_zero hz
  have hg : g = f + (g - f) := by abel
  refine ⟨hg ▸ hf.add hs, ?_⟩
  have e1 : ∑' k, (f + (g - f)) k = ∑' k, f k + ∑' k, (g - f) k :=
    (hf.hasSum.add hs.hasSum).tsum_eq
  rw [hg, e1, tsum_eq_sum hz, Finset.sum_pair hts]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Cochrane (2023), footnote 1, p. 440: a cost-neutral change of an optimal plan at two dates
`t ≠ s` cannot raise utility at those dates. -/
theorem perturb_le {β W : ℝ} {u : ℝ → ℝ → ℝ} {q ι c m c' m' : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m) {t s : ℕ} (hts : t ≠ s)
    (hc : ∀ k, k ≠ t → k ≠ s → c' k = c k) (hm : ∀ k, k ≠ t → k ≠ s → m' k = m k)
    (hcost : q t * (c' t + ι t * m' t) + q s * (c' s + ι s * m' s) =
      q t * (c t + ι t * m t) + q s * (c s + ι s * m s)) :
    β ^ t * u (c' t) (m' t) + β ^ s * u (c' s) (m' s) ≤
      β ^ t * u (c t) (m t) + β ^ s * u (c s) (m s) := by
  obtain ⟨⟨hfs, hfW⟩, hus, hmax⟩ := hopt
  have h1 := tsum_modify_two (f := fun k => q k * (c k + ι k * m k))
    (g := fun k => q k * (c' k + ι k * m' k)) hts
    (fun k hkt hks => by simp only [hc k hkt hks, hm k hkt hks]) hfs
  have h2 := tsum_modify_two (f := fun k => β ^ k * u (c k) (m k))
    (g := fun k => β ^ k * u (c' k) (m' k)) hts
    (fun k hkt hks => by simp only [hc k hkt hks, hm k hkt hks]) hus
  have hfeas : Feasible q ι W c' m' := ⟨h1.1, by rw [h1.2]; linarith⟩
  have := hmax c' m' hfeas h2.1
  rw [h2.2] at this
  linarith

/-- Cochrane (2023), eq. (19.13), p. 440 (cross-date form): at an optimum, for dates `t ≠ s`,
`βᵗu_c(t)q_s = βˢu_c(s)q_t` (shift consumption between `t` and `s` at constant cost). -/
theorem foc_cc {β W : ℝ} {u : ℝ → ℝ → ℝ} {uc : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m)
    (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k)) {t s : ℕ}
    (hts : t ≠ s) : β ^ t * uc (c t) (m t) * q s = β ^ s * uc (c s) (m s) * q t := by
  set D : ℝ → ℝ := fun ε => β ^ t * u (c t + ε * q s) (m t) + β ^ s * u (c s - ε * q t) (m s)
    with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    have := perturb_le (c' := Function.update (Function.update c t (c t + ε * q s)) s
      (c s - ε * q t)) (m' := m) hopt hts (fun k hkt hks => by
        simp [Function.update_of_ne hks, Function.update_of_ne hkt]) (fun _ _ _ => rfl)
      (by simp [Function.update_of_ne hts]; ring)
    simpa [hD, Function.update_of_ne hts, Function.update_of_ne hts.symm] using this
  have hd1 : HasDerivAt (fun ε => c t + ε * q s) (q s) 0 := by
    simpa using (hasDerivAt_mul_const (q s)).const_add (c t)
  have hd2 : HasDerivAt (fun ε => c s - ε * q t) (-q t) 0 := by
    simpa using (hasDerivAt_mul_const (q t)).const_sub (c s)
  have hu1 : HasDerivAt (fun ε => u (c t + ε * q s) (m t)) (uc (c t) (m t) * q s) 0 :=
    HasDerivAt.comp_of_eq 0 (huc t) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s - ε * q t) (m s)) (uc (c s) (m s) * -q t) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s) hd2 (by simp)
  have hDd : HasDerivAt D (β ^ t * (uc (c t) (m t) * q s) +
      β ^ s * (uc (c s) (m s) * -q t)) 0 :=
    (hu1.const_mul _).add (hu2.const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have := hmax.hasDerivAt_eq_zero hDd
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440 (cross-date form): at an optimum, for dates
`t ≠ s`, `βᵗu_m(t)q_s = βˢu_c(s)q_tι_t` (trade real money at `t` against consumption at `s`). -/
theorem foc_mc {β W : ℝ} {u : ℝ → ℝ → ℝ} {uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m)
    (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k))
    (hum : ∀ k, HasDerivAt (fun x => u (c k) x) (um (c k) (m k)) (m k)) {t s : ℕ}
    (hts : t ≠ s) : β ^ t * um (c t) (m t) * q s = β ^ s * uc (c s) (m s) * q t * ι t := by
  set D : ℝ → ℝ := fun ε =>
    β ^ t * u (c t) (m t + ε * q s) + β ^ s * u (c s - ε * (q t * ι t)) (m s) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    have := perturb_le (c' := Function.update c s (c s - ε * (q t * ι t)))
      (m' := Function.update m t (m t + ε * q s)) hopt hts
      (fun k _ hks => by simp [Function.update_of_ne hks])
      (fun k hkt _ => by simp [Function.update_of_ne hkt])
      (by simp [Function.update_of_ne hts, Function.update_of_ne hts.symm]; ring)
    simpa [hD, Function.update_of_ne hts, Function.update_of_ne hts.symm] using this
  have hd1 : HasDerivAt (fun ε => m t + ε * q s) (q s) 0 := by
    simpa using (hasDerivAt_mul_const (q s)).const_add (m t)
  have hd2 : HasDerivAt (fun ε => c s - ε * (q t * ι t)) (-(q t * ι t)) 0 := by
    simpa using (hasDerivAt_mul_const (q t * ι t)).const_sub (c s)
  have hu1 : HasDerivAt (fun ε => u (c t) (m t + ε * q s)) (um (c t) (m t) * q s) 0 :=
    HasDerivAt.comp_of_eq 0 (hum t) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s - ε * (q t * ι t)) (m s))
      (uc (c s) (m s) * -(q t * ι t)) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s) hd2 (by simp)
  have hDd : HasDerivAt D (β ^ t * (um (c t) (m t) * q s) +
      β ^ s * (uc (c s) (m s) * -(q t * ι t))) 0 :=
    (hu1.const_mul _).add (hu2.const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have := hmax.hasDerivAt_eq_zero hDd
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, and footnote 1: at an optimal plan of the
time-0 problem (with `q_0 = Λ_0/Λ_0 = 1`, `q_1 > 0`), with the multiplier
`λ = u_c(c_0, M_0/P_0)`, `βᵗu_c(c_t, M_t/P_t) = λΛ_t/Λ_0` and
`βᵗu_m(c_t, M_t/P_t) = λ(Λ_t/Λ_0) i_t/(1 + i_t)` at every date. -/
theorem foc_1913_1914 {β W : ℝ} {u : ℝ → ℝ → ℝ} {uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hopt : Optimal β u q ι W c m) (hq0 : q 0 = 1) (hq1 : 0 < q 1)
    (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k))
    (hum : ∀ k, HasDerivAt (fun x => u (c k) x) (um (c k) (m k)) (m k)) (t : ℕ) :
    β ^ t * uc (c t) (m t) = uc (c 0) (m 0) * q t ∧
      β ^ t * um (c t) (m t) = uc (c 0) (m 0) * q t * ι t := by
  have hc : ∀ k, β ^ k * uc (c k) (m k) = uc (c 0) (m 0) * q k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hq0]
    · have := foc_cc hopt huc (Nat.pos_iff_ne_zero.mp hk)
      rw [hq0] at this
      simpa using this
  refine ⟨hc t, ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h1 := foc_mc hopt huc hum (t := 0) (s := 1) zero_ne_one
    have h2 := hc 1
    simp only [pow_zero, one_mul, pow_one] at h1 h2 ⊢
    rw [h2] at h1
    have : um (c 0) (m 0) * q 1 = uc (c 0) (m 0) * q 0 * ι 0 * q 1 := by rw [hq0] at h1 ⊢; linarith
    rw [hq0] at this ⊢
    exact mul_right_cancel₀ hq1.ne' (by linarith)
  · have := foc_mc hopt huc hum (Nat.pos_iff_ne_zero.mp ht) (s := 0)
    rw [hq0] at this
    simpa using this

/-- Cochrane (2023), footnote 1, p. 440 (concave utility; restated from the Cochrane
IntertemporalModel project): for `g` concave on `ℝ` with derivative `d` at `x`, the tangent
line lies above the graph. -/
theorem concave_le_tangent {g : ℝ → ℝ} (hc : ConcaveOn ℝ Set.univ g) {x d : ℝ}
    (hg : HasDerivAt g d x) (y : ℝ) : g y ≤ g x + d * (y - x) := by
  rcases lt_trichotomy y x with h | h | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) h hg
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    nlinarith
  · subst h
    simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h hg
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- Cochrane (2023), footnote 1, p. 440 (concave utility): if `u(c, m)` is jointly concave and
differentiable at `(c₀, m₀)` with partial derivatives `u_c`, `u_m`, then
`u(c, m) ≤ u(c₀, m₀) + u_c(c − c₀) + u_m(m − m₀)`. -/
theorem supergradient_of_concave {u : ℝ → ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {c0 m0 : ℝ}
    (hconc : ConcaveOn ℝ Set.univ (fun z : ℝ × ℝ => u z.1 z.2))
    (hd : HasFDerivAt (fun z : ℝ × ℝ => u z.1 z.2) L (c0, m0)) (c m : ℝ) :
    u c m ≤ u c0 m0 + L (1, 0) * (c - c0) + L (0, 1) * (m - m0) := by
  set g : ℝ → ℝ := fun τ => u (c0 + τ * (c - c0)) (m0 + τ * (m - m0)) with hgdef
  have hgc : ConcaveOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := hconc.2 (Set.mem_univ (c0 + x * (c - c0), m0 + x * (m - m0)))
      (Set.mem_univ (c0 + y * (c - c0), m0 + y * (m - m0))) ha hb hab
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
    simp only [hgdef, smul_eq_mul]
    convert this using 2
    · linear_combination (-c0) * hab
    · linear_combination (-m0) * hab
  have hpath : HasDerivAt (fun τ : ℝ => (c0 + τ * (c - c0), m0 + τ * (m - m0)))
      (c - c0, m - m0) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => c0 + τ * (c - c0)) (c - c0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (c - c0)).const_add c0
    have h2 : HasDerivAt (fun τ : ℝ => m0 + τ * (m - m0)) (m - m0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (m - m0)).const_add m0
    exact h1.prodMk h2
  have hd' : HasFDerivAt (fun z : ℝ × ℝ => u z.1 z.2) L
      ((fun τ : ℝ => (c0 + τ * (c - c0), m0 + τ * (m - m0))) 0) := by simpa using hd
  have hg0 : HasDerivAt ((fun z : ℝ × ℝ => u z.1 z.2) ∘
      fun τ : ℝ => (c0 + τ * (c - c0), m0 + τ * (m - m0))) (L (c - c0, m - m0)) 0 :=
    hd'.comp_hasDerivAt (0 : ℝ) hpath
  have hg : HasDerivAt g (L (c - c0, m - m0)) 0 := hg0
  have h := concave_le_tangent hgc hg 1
  have hlin : L (c - c0, m - m0) = L (1, 0) * (c - c0) + L (0, 1) * (m - m0) := by
    have e : ((c - c0, m - m0) : ℝ × ℝ) = (c - c0) • ((1 : ℝ), (0 : ℝ)) +
        (m - m0) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  simp only [hgdef, one_mul, zero_mul, add_zero, add_sub_cancel] at h
  rw [hlin] at h
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440 (sufficiency): if utility is
concave in the sense of the supergradient inequality at the plan (`supergradient_of_concave`),
`β ≥ 0`, the first-order conditions `βᵗu_c = λq_t`, `βᵗu_m = λq_tι_t` hold with `λ ≥ 0`, and the
budget binds, then the plan is optimal. -/
theorem optimal_of_foc {β W lam : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ} (hβ : 0 ≤ β)
    (hlam : 0 ≤ lam)
    (hsup : ∀ k c' m', u c' m' ≤ u (c k) (m k) + uc (c k) (m k) * (c' - c k) +
      um (c k) (m k) * (m' - m k))
    (hfoc : ∀ k, β ^ k * uc (c k) (m k) = lam * q k ∧
      β ^ k * um (c k) (m k) = lam * q k * ι k)
    (hfeas : Feasible q ι W c m) (hbind : ∑' t, q t * (c t + ι t * m t) = W)
    (hus : Summable (fun t => β ^ t * u (c t) (m t))) : Optimal β u q ι W c m := by
  refine ⟨hfeas, hus, fun c' m' hf' hu' => ?_⟩
  have hpt : ∀ k, β ^ k * u (c' k) (m' k) ≤ β ^ k * u (c k) (m k) +
      lam * (q k * (c' k + ι k * m' k) - q k * (c k + ι k * m k)) := by
    intro k
    have h1 := mul_le_mul_of_nonneg_left (hsup k (c' k) (m' k)) (pow_nonneg hβ k)
    have h2 := hfoc k
    have e : β ^ k * (u (c k) (m k) + uc (c k) (m k) * (c' k - c k) +
        um (c k) (m k) * (m' k - m k)) = β ^ k * u (c k) (m k) +
        lam * (q k * (c' k + ι k * m' k) - q k * (c k + ι k * m k)) := by
      linear_combination (c' k - c k) * h2.1 + (m' k - m k) * h2.2
    linarith
  have hR : HasSum (fun k => β ^ k * u (c k) (m k) +
      lam * (q k * (c' k + ι k * m' k) - q k * (c k + ι k * m k)))
      (∑' k, β ^ k * u (c k) (m k) + lam * (∑' k, q k * (c' k + ι k * m' k) -
        ∑' k, q k * (c k + ι k * m k))) :=
    hus.hasSum.add ((hf'.1.hasSum.sub hfeas.1.hasSum).mul_left lam)
  have hle := hasSum_le hpt hu'.hasSum hR
  have : lam * (∑' k, q k * (c' k + ι k * m' k) - ∑' k, q k * (c k + ι k * m k)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hf'.2])
  linarith

/-! ### (19.15)–(19.16): bond prices, money demand and the value of money -/

/-- Cochrane (2023), p. 441: from (19.15) `1/(1 + i_t) = E_t[βu_c(t+1)P_t/(u_c(t)P_{t+1})]` and
(19.16) `u_m/u_c = i/(1 + i)`, `1 = u_m(t)/u_c(t) + E_t[βu_c(t+1)P_t/(u_c(t)P_{t+1})]`. -/
theorem convenience_identity {ratio i EQ : ℝ} (hi : 1 + i ≠ 0) (h1915 : EQ = 1 / (1 + i))
    (h1916 : ratio = i / (1 + i)) : 1 = ratio + EQ := by
  rw [h1915, h1916]
  field_simp
  ring

/-- Cochrane (2023), (19.15)–(19.16), p. 441: the value of a dollar `v_t = u_c(t)/P_t` satisfies
`v_t = u_m(t)/P_t + βE_tv_{t+1}`. -/
theorem value_recursion (hPO : 𝔼.PullOut) {β : ℝ} {uc um P i : ℕ → Ω → ℝ}
    (hk : ∀ t, 𝔼.E t (P t / uc t) = P t / uc t) (huc : ∀ t ω, uc t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) :
    Solves 𝔼 β (fun t => um t / P t) (fun t => uc t / P t) := by
  intro t
  have e : β • (uc (t + 1) / uc t * (P t / P (t + 1))) = (P t / uc t) * (β • (uc (t + 1) /
      P (t + 1))) := by
    funext ω
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.div_apply, smul_eq_mul]
    ring
  have h := h1915 t
  rw [e, hPO t _ _ (hk t), map_smul] at h
  funext ω
  have hω := congrFun h ω
  have h16 := h1916 t ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
    Pi.add_apply] at hω ⊢
  set X := 𝔼.E t (uc (t + 1) / P (t + 1)) ω with hXdef
  have h1 := huc t ω
  have h2 := hP t ω
  have h3 := hi t ω
  have hX : β * X = uc t ω / P t ω / (1 + i t ω) := by
    field_simp at hω ⊢
    linarith
  have hum : um t ω = uc t ω * (i t ω / (1 + i t ω)) := by
    field_simp at h16 ⊢
    linarith
  rw [hX, hum]
  field_simp

/-- Cochrane (2023), p. 441 ("Iterating, we can state an asset-pricing view of the value of
money"): `u_c(t)/P_t = E_t∑_{j≤T}βʲu_m(t+j)/P_{t+j} + β^{T+1}E_t[u_c(t+T+1)/P_{t+T+1}]`. -/
theorem value_of_money_iterated (hPO : 𝔼.PullOut) {β : ℝ} {uc um P i : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted (fun t => uc t / P t))
    (hk : ∀ t, 𝔼.E t (P t / uc t) = P t / uc t) (huc : ∀ t ω, uc t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t T : ℕ) :
    uc t / P t = ∑ j ∈ Finset.range (T + 1), β ^ j • 𝔼.E t (um (t + j) / P (t + j)) +
      β ^ (T + 1) • 𝔼.E t (uc (t + T + 1) / P (t + T + 1)) := by
  have hs := value_recursion 𝔼 hPO hk huc hP hi h1915 h1916
  have hwa : 𝔼.Adapted (fun t => um t / P t) := fun k => by
    have hsk := hs k
    simp only at hsk
    have e : um k / P k = uc k / P k - β • 𝔼.E k (uc (k + 1) / P (k + 1)) := by
      rw [hsk]; abel
    change 𝔼.E k (um k / P k) = um k / P k
    have hvk := hv k
    simp only at hvk
    rw [e, map_sub, map_smul, 𝔼.E_E_self, hvk]
  rw [iterate_A15 𝔼 hwa hs t (T + 1), add_comm, ← add_assoc]

/-- Cochrane (2023), p. 441 ("An additional dollar, held forever, costs `1/P_t`. It generates a
stream of benefits"): if `βᵀE_t[u_c(t+T)/P_{t+T}] → 0`, the value of a dollar is the present value
of its liquidity dividends, `u_c(t)/P_t = lim ∑_{j<T}βʲE_t[u_m(t+j)/P_{t+j}]`. -/
theorem value_of_money_limit (hPO : 𝔼.PullOut) {β : ℝ} {uc um P i : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted (fun t => uc t / P t))
    (hk : ∀ t, 𝔼.E t (P t / uc t) = P t / uc t) (huc : ∀ t ω, uc t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun T => β ^ T * 𝔼.E t (uc (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (um (t + j) / P (t + j)) ω) atTop
      (𝓝 (uc t ω / P t ω)) := by
  have hs := value_recursion 𝔼 hPO hk huc hP hi h1915 h1916
  have hwa : 𝔼.Adapted (fun t => um t / P t) := fun k => by
    have hsk := hs k
    simp only at hsk
    have e : um k / P k = uc k / P k - β • 𝔼.E k (uc (k + 1) / P (k + 1)) := by
      rw [hsk]; abel
    change 𝔼.E k (um k / P k) = um k / P k
    have hvk := hv k
    simp only at hvk
    rw [e, map_sub, map_smul, 𝔼.E_E_self, hvk]
  have hid : ∀ T, ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (um (t + j) / P (t + j)) ω =
      uc t ω / P t ω - β ^ T * 𝔼.E t (uc (t + T) / P (t + T)) ω := by
    intro T
    have h := congrFun (iterate_A15 𝔼 hwa hs t T) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.div_apply] at h
    linarith
  have h2 := (tendsto_const_nhds (x := uc t ω / P t ω)).sub htvc
  rw [sub_zero] at h2
  exact h2.congr fun T => (hid T).symm

/-- Cochrane (2023), (19.16), p. 441 (money demand `M_t = P_tL(y_t, i_t)`; restated from the
Woodford Chapter 2 project): if `u_m/u_c` is strictly decreasing in real balances, the
money-demand equation `u_m/u_c(y, m) = i/(1 + i)` has at most one positive solution. -/
theorem lm_unique {R : ℝ → ℝ} (hanti : StrictAntiOn R (Set.Ioi 0)) {Δ m₁ m₂ : ℝ}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (e₁ : R m₁ = Δ) (e₂ : R m₂ = Δ) : m₁ = m₂ :=
  hanti.injOn h₁ h₂ (e₁.trans e₂.symm)

/-- Cochrane (2023), (19.16), p. 441 (restated from the Woodford Chapter 2 project): if
`u_m/u_c` is continuous, unbounded as real balances vanish and tends to `0` for large balances,
money demand `u_m/u_c(y, m) = Δ` has a positive solution for every `Δ > 0`. -/
theorem lm_exists {R : ℝ → ℝ} (hcont : ContinuousOn R (Set.Ioi 0))
    (h0 : Tendsto R (𝓝[>] 0) atTop) (hinf : Tendsto R atTop (𝓝 0)) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ m, 0 < m ∧ R m = Δ := by
  have e₁ : ∀ᶠ m in 𝓝[>] (0 : ℝ), Δ < R m ∧ m ∈ Set.Ioi 0 :=
    (h0.eventually (eventually_gt_atTop Δ)).and self_mem_nhdsWithin
  have e₂ : ∀ᶠ m in atTop, R m < Δ ∧ 0 < m :=
    (hinf.eventually (gt_mem_nhds hΔ)).and (eventually_gt_atTop 0)
  obtain ⟨m₁, hR₁, hm₁⟩ := e₁.exists
  obtain ⟨m₂, hR₂, hm₂⟩ := e₂.exists
  have hsub : Set.uIcc m₁ m₂ ⊆ Set.Ioi 0 := fun x hx => by
    rcases Set.mem_uIcc.mp hx with h | h
    · exact lt_of_lt_of_le (Set.mem_Ioi.mp hm₁) h.1
    · exact lt_of_lt_of_le hm₂ h.1
  have hmem : Δ ∈ Set.uIcc (R m₁) (R m₂) := Set.mem_uIcc.mpr (Or.inr ⟨hR₂.le, hR₁.le⟩)
  obtain ⟨m, hm, hRm⟩ := intermediate_value_uIcc (hcont.mono hsub) hmem
  exact ⟨m, hsub hm, hRm⟩

/-! ### (19.17)–(19.19): separable utility, perfect foresight -/

/-- Cochrane (2023), eq. (19.18), p. 442: with real balances `m = M/P`,
`P_t/P_{t+1} = (m_{t+1}/m_t)(M_t/M_{t+1})`. -/
theorem price_ratio_eq {M M' P P' : ℝ} (hM : M ≠ 0) (hM' : M' ≠ 0) (hP : P ≠ 0)
    (hP' : P' ≠ 0) : P / P' = (M' / P') / (M / P) * (M / M') := by
  field_simp

/-- Cochrane (2023), eqs. (19.17)–(19.18), p. 442: with separable utility, constant consumption
`c = y` and perfect foresight, `1/(1 + i_t) = βP_t/P_{t+1}`, so (19.17)
`u_m(m_t)/u_c(y) = 1 − 1/(1 + i_t)` is the difference equation (19.18)
`u_m(m_t)/u_c(y) = 1 − β(m_{t+1}/m_t)(M_t/M_{t+1})`. -/
theorem eq1918_iff {β ucy umt i M M' P P' : ℝ} (hM : M ≠ 0) (hM' : M' ≠ 0) (hP : P ≠ 0)
    (hP' : P' ≠ 0) (h1915 : 1 / (1 + i) = β * (P / P')) :
    umt / ucy = 1 - 1 / (1 + i) ↔
      umt / ucy = 1 - β * ((M' / P') / (M / P)) * (M / M') := by
  rw [h1915, price_ratio_eq hM hM' hP hP', mul_assoc]

/-- Cochrane (2023), eq. (19.18), p. 442: a perfect-foresight path of positive real balances
`m_t = M_t/P_t` for separable utility, given the money path `M` and `u_c(y) = ucy`. -/
def IsMIUPath (β ucy : ℝ) (um : ℝ → ℝ) (M m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ um (m t) / ucy = 1 - β * (m (t + 1) / m t) * (M t / M (t + 1))

/-- Cochrane (2023), eq. (19.19), p. 442: with money growth `M_{t+1}/M_t = 1 + µ`, constant real
balances `m` form a path iff `u_m(m)/u_c(y) = 1 − β/(1 + µ)`. -/
theorem steady_state_path_iff {β ucy μg m : ℝ} {um : ℝ → ℝ} {M : ℕ → ℝ} (hm : 0 < m)
    (hM : ∀ t, 0 < M t) (hg : ∀ t, M (t + 1) = μg * M t) :
    IsMIUPath β ucy um M (fun _ => m) ↔ um m / ucy = 1 - β / μg := by
  have hμ : μg ≠ 0 := by
    intro h
    have := hg 0
    rw [h, zero_mul] at this
    exact (hM 1).ne' this
  constructor
  · intro h
    rw [(h 0).2, hg 0]
    field_simp [(hM 0).ne']
  · intro h t
    refine ⟨hm, ?_⟩
    rw [h, hg t]
    field_simp [(hM t).ne']

/-- Cochrane (2023), eq. (19.19), p. 442 ("prices are proportional to money over time, and
inflation equals the money growth rate"): with constant real balances `m = M_t/P_t`,
`P_{t+1}/P_t = M_{t+1}/M_t = 1 + µ`. -/
theorem steady_state_inflation {μg m Mt Pt Pt' : ℝ} (hm : 0 < m) (hMt : 0 < Mt)
    (h0 : m = Mt / Pt) (h1 : m = μg * Mt / Pt') : Pt' / Pt = μg := by
  have hμ : μg ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_div] at h1
    exact hm.ne' h1
  have hPt : Pt = Mt / m := by rw [h0]; field_simp [hMt.ne']
  have hPt' : Pt' = μg * Mt / m := by
    have hP' : Pt' ≠ 0 := by
      rintro rfl
      rw [div_zero] at h1
      exact hm.ne' h1
    rw [h1]
    field_simp
  rw [hPt, hPt']
  field_simp

/-- Cochrane (2023), eq. (19.19), p. 442: if `u_m` is continuous and strictly decreasing on
`(0, ∞)` and `u_m/u_c(y)` takes values on both sides of `1 − β/(1 + µ)`, the inflationary steady
state of real balances exists and is unique. -/
theorem steady_state_existsUnique {β ucy μg a b : ℝ} {um : ℝ → ℝ} (hucy : 0 < ucy)
    (hcont : ContinuousOn um (Set.Ioi 0)) (hanti : StrictAntiOn um (Set.Ioi 0)) (ha : 0 < a)
    (hab : a ≤ b) (hva : 1 - β / μg ≤ um a / ucy) (hvb : um b / ucy ≤ 1 - β / μg) :
    ∃! m, 0 < m ∧ um m / ucy = 1 - β / μg := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  have hc : ContinuousOn (fun z => um z / ucy) (Set.Icc a b) :=
    (hcont.mono hsub).div_const ucy
  obtain ⟨m, hm, hv⟩ := intermediate_value_Icc' hab hc ⟨hvb, hva⟩
  refine ⟨m, ⟨hsub hm, hv⟩, fun m' hm' => ?_⟩
  have e : um m' = um m := by
    have := hm'.2.trans hv.symm
    field_simp at this
    exact this
  exact hanti.injOn hm'.1 (hsub hm) e

/-- Cochrane (2023), p. 443 ("At zero nominal rates `i_t = 0`, we have `u_m = 0` … (19.18)
becomes `P_{t+1}/P_t = β`"): with `u_c > 0`, (19.16) and the bond price
`1/(1 + i) = βP_t/P_{t+1}`, `u_m = 0` iff `i = 0` iff `P_{t+1}/P_t = β`. -/
theorem zero_rate_iff {β ucy umt i P P' : ℝ} (hucy : 0 < ucy) (hi : 0 < 1 + i) (hP : 0 < P)
    (hP' : 0 < P') (h1916 : umt / ucy = i / (1 + i))
    (h1915 : 1 / (1 + i) = β * (P / P')) :
    (umt = 0 ↔ i = 0) ∧ (i = 0 ↔ P' / P = β) := by
  constructor
  · constructor
    · intro h
      rw [h, zero_div] at h1916
      rcases div_eq_zero_iff.mp h1916.symm with h | h
      · exact h
      · exact absurd h hi.ne'
    · intro h
      rw [h, zero_div, div_eq_zero_iff] at h1916
      exact h1916.resolve_right hucy.ne'
  · constructor
    · intro h
      rw [h, add_zero, div_one] at h1915
      field_simp at h1915 ⊢
      linarith
    · intro h
      have : β * (P / P') = 1 := by
        rw [← h]
        field_simp
      rw [this] at h1915
      have := (div_eq_one_iff_eq hi.ne').mp h1915
      linarith

/-- Cochrane (2023), p. 443 ("with `β = 1/(1 + δ)`, `π_{t+1} ≈ −δ`"): the deflation rate
`P_{t+1}/P_t − 1 = 1/(1 + δ) − 1` has derivative `−1` in `δ` at `δ = 0`, and equals
`−δ/(1 + δ)`. -/
theorem deflation_approx :
    HasDerivAt (fun δ : ℝ => 1 / (1 + δ) - 1) (-1) 0 ∧
      ∀ δ : ℝ, 1 + δ ≠ 0 → 1 / (1 + δ) - 1 = -δ / (1 + δ) := by
  refine ⟨?_, fun δ hδ => by field_simp; ring⟩
  have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
  simp only [id, add_zero] at h
  have h2 := h.sub_const 1
  simpa [one_div] using h2

/-- Cochrane (2023), p. 443 ("we arrive at zero interest rates in finite time and stay there"):
with satiation `u_m(m) = 0` for `m ≥ m_sat` and money growth `1 + µ ≥ β`, once a path of (19.18)
reaches `m_sat` it stays above it, real balances grow at `(1 + µ)/β` and `u_m = 0` (`i = 0`)
at every later date. -/
theorem satiation_absorbing {β ucy μg msat : ℝ} {um : ℝ → ℝ} {M m : ℕ → ℝ} (hβ : 0 < β)
    (hμβ : β ≤ μg) (hsat : ∀ x, msat ≤ x → um x = 0) (hM : ∀ t, 0 < M t)
    (hg : ∀ t, M (t + 1) = μg * M t) (hpath : IsMIUPath β ucy um M m) {t0 : ℕ}
    (ht0 : msat ≤ m t0) :
    ∀ n, msat ≤ m (t0 + n) ∧ um (m (t0 + n)) = 0 ∧
      m (t0 + n + 1) = μg / β * m (t0 + n) := by
  have hμ : 0 < μg := lt_of_lt_of_le hβ hμβ
  have step : ∀ k, msat ≤ m k → m (k + 1) = μg / β * m k ∧ msat ≤ m (k + 1) := by
    intro k hk
    have hp := hpath k
    rw [hsat _ hk, zero_div, hg k] at hp
    have hmk := hp.1
    have hMk := hM k
    have e : m (k + 1) = μg / β * m k := by
      have h2 : β * (m (k + 1) / m k) * (M k / (μg * M k)) = 1 := by linarith [hp.2]
      field_simp at h2
      field_simp
      linarith
    refine ⟨e, ?_⟩
    rw [e]
    have : 1 ≤ μg / β := (one_le_div hβ).mpr hμβ
    nlinarith
  intro n
  induction n with
  | zero => exact ⟨ht0, hsat _ ht0, (step t0 ht0).1⟩
  | succ n ih =>
    have h1 := (step (t0 + n) ih.1).2
    rw [show t0 + (n + 1) = t0 + n + 1 by ring]
    exact ⟨h1, hsat _ h1, (step _ h1).1⟩

/-- Cochrane (2023), p. 443 ("if `lim_{m→∞} u_m(m) = 0`, zero interest rates are a limiting
case, and the economy slowly drifts down to it"): along a path with `m_t → ∞` and (19.16),
`i_t → 0`. -/
theorem limit_rate_zero {ucy : ℝ} {um : ℝ → ℝ} {m i : ℕ → ℝ} (hum : Tendsto um atTop (𝓝 0))
    (hm : Tendsto m atTop atTop) (hi : ∀ t, 0 < 1 + i t)
    (h1916 : ∀ t, um (m t) / ucy = i t / (1 + i t)) : Tendsto i atTop (𝓝 0) := by
  set ι := fun t => um (m t) / ucy with hι
  have hιlim : Tendsto ι atTop (𝓝 0) := by
    have := (hum.comp hm).div_const ucy
    simpa [hι] using this
  have hfor : ∀ t, i t = ι t / (1 - ι t) := by
    intro t
    have h := h1916 t
    have h1 := hi t
    simp only [hι]
    rw [h]
    field_simp
    ring
  have hlim : Tendsto (fun t => ι t / (1 - ι t)) atTop (𝓝 (0 / (1 - 0))) :=
    hιlim.div (tendsto_const_nhds.sub hιlim) (by norm_num)
  rw [zero_div] at hlim
  exact hlim.congr fun t => (hfor t).symm

/-- Cochrane (2023), p. 443 ("The money demand curve becomes a correspondence `m ≥ m_sat`,
`i = 0`"): with satiation, at `i = 0` every `m ≥ m_sat` satisfies (19.16). -/
theorem money_demand_correspondence {ucy msat : ℝ} {um : ℝ → ℝ}
    (hsat : ∀ x, msat ≤ x → um x = 0) {m : ℝ} (hm : msat ≤ m) :
    um m / ucy = (0 : ℝ) / (1 + 0) := by
  rw [hsat m hm]
  simp

/-! ### (19.20)–(19.23): power utility -/

/-- Cochrane (2023), eq. (19.20), p. 443: for `γ ≠ 1` and `x > 0`, `x^{1−γ}/(1 − γ)` has
derivative `x^{−γ}`; hence `u_c = c^{−γ}` and `u_m = θm^{−γ}`. -/
theorem hasDerivAt_power {γ x : ℝ} (hγ : γ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => z ^ (1 - γ) / (1 - γ)) (x ^ (-γ)) x := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hx.ne')).div_const (1 - γ)
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  convert h using 1
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- Cochrane (2023), (19.20), p. 443: with power utility, `u_m/u_c = θm^{−γ}/y^{−γ} = θ(m/y)^{−γ}`
equals `θ(y/m)^γ = θ(Py/M)^γ`. -/
theorem power_um_ratio {θ γ m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    θ * m ^ (-γ) / y ^ (-γ) = θ * (y / m) ^ γ := by
  rw [mul_div_assoc, ← Real.div_rpow hm.le hy.le, Real.rpow_neg (by positivity),
    ← Real.inv_rpow (by positivity), inv_div]

/-- Cochrane (2023), (19.16) with (19.20), p. 443, and Online Appendix (3.4), p. 620 (the
inverse power money demand, a general lemma; formerly `PruningInflation.power_demand_iff`): for
`k, m > 0` and `γ ≠ 0`, `θm^{−γ} = k` iff `m = (k/θ)^{−1/γ}`. -/
theorem power_demand_iff {θ γ k m : ℝ} (hθ : 0 < θ) (hγ : γ ≠ 0) (hk : 0 < k) (hm : 0 < m) :
    θ * m ^ (-γ) = k ↔ m = (k / θ) ^ (-(1 / γ)) := by
  have hneg : -(1 / γ) = (-γ)⁻¹ := by field_simp
  constructor
  · intro h
    have h1 : m ^ (-γ) = k / θ := by rw [← h]; field_simp
    rw [hneg, ← h1, Real.rpow_rpow_inv hm.le (neg_ne_zero.mpr hγ)]
  · intro h
    rw [h, hneg, Real.rpow_inv_rpow (by positivity) (neg_ne_zero.mpr hγ)]
    field_simp

/-- Cochrane (2023), p. 443 ("Money demand is `M_t = P_ty_t(i_t/(θ(1 + i_t)))^{−1/γ}`"): for
`θ, γ, ι > 0`, `θ(m/y)^{−γ} = ι` iff `m = y(ι/θ)^{−1/γ}` (with `ι = i/(1 + i)`, `m = M/P`). -/
theorem power_money_demand {θ γ y m ι : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hy : 0 < y)
    (hm : 0 < m) (hι : 0 < ι) : θ * (m / y) ^ (-γ) = ι ↔ m = y * (ι / θ) ^ (-1 / γ) := by
  rw [power_demand_iff hθ hγ.ne' hι (div_pos hm hy), div_eq_iff hy.ne', neg_div]
  constructor <;> intro h <;> rw [h] <;> ring

/-- Cochrane (2023), eq. (19.21), p. 444, in terms of `x_t = P_ty/M_t` with money growth
`M_{t+1}/M_t = 1 + µ` (`μg = 1 + µ`): `θx_t^γ = 1 − β(x_t/x_{t+1})/(1 + µ)` (since
`m_{t+1}/m_t = x_t/x_{t+1}`). -/
def IsPowerPath (β θ γ μg : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ t, 0 < x t ∧ θ * x t ^ γ = 1 - β * (x t / x (t + 1)) / μg

/-- Cochrane (2023), eq. (19.22), p. 444: with `β = 1/(1 + δ)` the inflationary steady state of
(19.21) satisfies `θ(Py/M)^γ = 1 − 1/((1 + δ)(1 + µ))`. -/
theorem eq1922 {θ γ δ μ xb : ℝ} (hδ : 1 + δ ≠ 0) (hμ : 1 + μ ≠ 0) (hxb : 0 < xb) :
    IsPowerPath (1 / (1 + δ)) θ γ (1 + μ) (fun _ => xb) ↔
      θ * xb ^ γ = 1 - 1 / ((1 + δ) * (1 + μ)) := by
  constructor
  · intro h
    rw [(h 0).2]
    field_simp
  · intro h t
    refine ⟨hxb, ?_⟩
    rw [h]
    field_simp

/-- Cochrane (2023), (19.22), p. 444: exactly,
`1 − 1/((1 + δ)(1 + µ)) = (δ + µ + δµ)/((1 + δ)(1 + µ))`. -/
theorem eq1922_exact {δ μ : ℝ} (hδ : 1 + δ ≠ 0) (hμ : 1 + μ ≠ 0) :
    1 - 1 / ((1 + δ) * (1 + μ)) = (δ + μ + δ * μ) / ((1 + δ) * (1 + μ)) := by
  field_simp
  ring

/-- Cochrane (2023), (19.22), p. 444 ("`≈ δ + µ`"): the derivative in `δ` at `δ = µ = 0` is `1`. -/
theorem eq1922_partial_delta :
    HasDerivAt (fun δ : ℝ => 1 - 1 / ((1 + δ) * (1 + 0))) 1 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
  simp only [id, add_zero] at h
  have h2 := h.const_sub 1
  simpa [one_div] using h2

/-- Cochrane (2023), (19.22), p. 444 ("`≈ δ + µ`"): the derivative in `µ` at `δ = µ = 0` is `1`. -/
theorem eq1922_partial_mu :
    HasDerivAt (fun μ : ℝ => 1 - 1 / ((1 + 0) * (1 + μ))) 1 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by norm_num)
  simp only [id, add_zero] at h
  have h2 := h.const_sub 1
  simpa [one_div] using h2

/-- Cochrane (2023), (19.22), p. 444 ("`≈ δ + µ`"), quantitatively: for `δ, µ ≥ 0` with
`δ + µ ≤ 1`, `0 ≤ (δ + µ) − [1 − 1/((1 + δ)(1 + µ))] ≤ (δ + µ)²`. -/
theorem eq1922_approx {δ μ : ℝ} (hδ : 0 ≤ δ) (hμ : 0 ≤ μ) (h1 : δ + μ ≤ 1) :
    0 ≤ (δ + μ) - (1 - 1 / ((1 + δ) * (1 + μ))) ∧
      (δ + μ) - (1 - 1 / ((1 + δ) * (1 + μ))) ≤ (δ + μ) ^ 2 := by
  have hD : 0 < (1 + δ) * (1 + μ) := by positivity
  have e : (δ + μ) - (1 - 1 / ((1 + δ) * (1 + μ))) =
      ((δ + μ) * (δ + μ + δ * μ) - δ * μ) / ((1 + δ) * (1 + μ)) := by
    field_simp
    ring
  rw [e]
  have hdm : 0 ≤ δ * μ := mul_nonneg hδ hμ
  constructor
  · apply div_nonneg _ hD.le
    nlinarith [sq_nonneg (δ - μ)]
  · rw [div_le_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_right h1 hdm, sq_nonneg (δ + μ),
      mul_nonneg (sq_nonneg (δ + μ)) (add_nonneg (add_nonneg hδ hμ) hdm)]

/-- Cochrane (2023), p. 444 ("for `Py/M ≈ 1`, we need `θ ≈ δ + µ`"): at `x̄ = 1`, `θ` equals the
right-hand side of (19.22). -/
theorem calib_unit {θ γ f : ℝ} (h : θ * (1 : ℝ) ^ γ = f) : θ = f := by
  rwa [Real.one_rpow, mul_one] at h

/-- Cochrane (2023), p. 444 ("For a more realistic `Py/M ≈ 10`"): at `x̄ = 10`,
`θ = f·10^{−γ}`. -/
theorem calib_ten {θ γ f : ℝ} (h : θ * (10 : ℝ) ^ γ = f) : θ = f * (10 : ℝ) ^ (-γ) := by
  rw [← h, Real.rpow_neg (by norm_num), mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

/-- Cochrane (2023), p. 444 ("we need `θ` on the order of 0.01"): with `δ + µ ≈ 0.1` this holds
for `γ = 1`: `θ = 0.1/10 = 0.01`. -/
theorem calib_ten_gamma_one {θ : ℝ} (h : θ * (10 : ℝ) ^ (1 : ℝ) = 1 / 10) : θ = 1 / 100 := by
  rw [Real.rpow_one] at h
  linarith

/-- Cochrane (2023), p. 444, imprecision: with the figure's `γ = 2` and `δ + µ ≈ 0.1`,
`Py/M = 10` requires `θ = 0.001`, not `0.01`. -/
theorem calib_ten_gamma_two {θ : ℝ} (h : θ * (10 : ℝ) ^ (2 : ℝ) = 1 / 10) : θ = 1 / 1000 := by
  rw [Real.rpow_two] at h
  linarith

/-- Cochrane (2023), p. 444 ("If we hold one tenth of a year's income as money, even a 5%
nominal interest rate generates interests costs … equal to one two hundredth of a year's
income"). -/
theorem calib_interest_cost (y : ℝ) : (5 / 100) * (y / 10) = y / 200 := by ring

/-- Cochrane (2023), eq. (19.23), p. 444: the map
`x ↦ x(1 − θx̄^γ)/(1 − θx^γ)`, `x = P_ty/M_t`. -/
noncomputable def nextX (θ γ xb x : ℝ) : ℝ := x * (1 - θ * xb ^ γ) / (1 - θ * x ^ γ)

/-- Cochrane (2023), eq. (19.23), p. 444: given the steady state `θx̄^γ = 1 − β/(1 + µ)`, for
positive `x_t`, `x_{t+1}` the date-`t` equation of (19.21) holds iff `x_{t+1} = nextX x_t`
(positivity of `x_{t+1}` forces `1 − θx_t^γ ≠ 0`). -/
theorem eq1923_iff {β θ γ μg xb x x' : ℝ} (hβ : 0 < β) (hμ : 0 < μg) (hx : 0 < x)
    (hx' : 0 < x') (hxb : θ * xb ^ γ = 1 - β / μg) :
    θ * x ^ γ = 1 - β * (x / x') / μg ↔ x' = nextX θ γ xb x := by
  unfold nextX
  rw [hxb]
  constructor
  · intro h
    have h1 : 1 - θ * x ^ γ = β * x / (μg * x') := by rw [h]; field_simp; ring
    rw [h1]
    field_simp
    ring
  · intro h
    have := hβ.ne'
    rw [h]
    field_simp
    have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ this
    linear_combination (1 - θ * x ^ γ) * hb

/-- Cochrane (2023), p. 444 (`P_{t+1}/P_t = (1 + µ)(1 − θ(Py/M)^γ)/(1 − θ(P_ty/M_t)^γ)`): along
(19.23), `(x_{t+1}/x_t)(1 + µ) = (1 + µ)(1 − θx̄^γ)/(1 − θx_t^γ)`. -/
theorem inflation_eq1923 {θ γ μg xb x : ℝ} (hx : 0 < x) :
    nextX θ γ xb x / x * μg = μg * (1 - θ * xb ^ γ) / (1 - θ * x ^ γ) := by
  unfold nextX
  field_simp

/-! ### Figure 19.1 -/

/-- Cochrane (2023), Figure 19.1, p. 444: `x̄ = √(275/9)`, the steady state for
`δ = µ = 0.2`, `γ = 2`, `θ = 0.01`. -/
noncomputable def xbar191 : ℝ := Real.sqrt (275 / 9)

/-- Cochrane (2023), Figure 19.1, p. 444: `x̄` solves (19.22) with `δ = µ = 0.2`, `γ = 2`,
`θ = 0.01`, and `θx̄^γ = 11/36`. -/
theorem fig191_steady :
    (1 / 100 : ℝ) * xbar191 ^ (2 : ℝ) = 1 - 1 / ((1 + 1 / 5) * (1 + 1 / 5)) ∧
      (1 / 100 : ℝ) * xbar191 ^ (2 : ℝ) = 11 / 36 := by
  rw [Real.rpow_two, xbar191, Real.sq_sqrt (by norm_num)]
  constructor <;> norm_num

/-- Cochrane (2023), Figure 19.1, p. 444: `5.52 < x̄ < 5.53`. -/
theorem fig191_xbar_bounds : (552 / 100 : ℝ) < xbar191 ∧ xbar191 < 553 / 100 := by
  unfold xbar191
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- Cochrane (2023), p. 444 ("the derivative of (19.23) is positive at `Py/M`"): for `x̄ > 0`
with `1 − θx̄^γ ≠ 0`, the slope of (19.23) at `x̄` is `1 + γθx̄^γ/(1 − θx̄^γ)`. -/
theorem nextX_hasDerivAt {θ γ xb : ℝ} (hxb : 0 < xb) (hK : 1 - θ * xb ^ γ ≠ 0) :
    HasDerivAt (nextX θ γ xb) (1 + γ * θ * xb ^ γ / (1 - θ * xb ^ γ)) xb := by
  set K := 1 - θ * xb ^ γ with hKdef
  have hnum : HasDerivAt (fun x => x * K) K xb := by
    simpa using (hasDerivAt_id xb).mul_const K
  have hden : HasDerivAt (fun x => 1 - θ * x ^ γ) (-(θ * (γ * xb ^ (γ - 1)))) xb := by
    simpa using ((Real.hasDerivAt_rpow_const (p := γ) (Or.inl hxb.ne')).const_mul θ).const_sub 1
  have h := hnum.div hden hK
  have e : ((fun x => x * K) / fun x => 1 - θ * x ^ γ) = nextX θ γ xb := by
    funext x
    simp only [Pi.div_apply, nextX, hKdef]
  rw [e] at h
  convert h using 1
  rw [Real.rpow_sub_one hxb.ne', ← hKdef]
  field_simp
  ring

/-- Cochrane (2023), p. 444 ("The phase diagram cuts from below at the steady state … so
dynamics are unstable"): with `θ > 0`, `x̄ > 0` and `0 < 1 − θx̄^γ`, the slope exceeds one
for `γ > 0`. -/
theorem slope_gt_one {θ γ xb : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hxb : 0 < xb)
    (hK : 0 < 1 - θ * xb ^ γ) : 1 < 1 + γ * θ * xb ^ γ / (1 - θ * xb ^ γ) := by
  have : 0 < γ * θ * xb ^ γ / (1 - θ * xb ^ γ) := by
    have := Real.rpow_pos_of_pos hxb γ
    positivity
  linarith

/-- Cochrane (2023), Figure 19.1, p. 444 (survey: slope `1.88 > 1`): with the figure's numbers
the slope of (19.23) at `x̄` is exactly `47/25 = 1.88`. -/
theorem fig191_slope :
    HasDerivAt (nextX (1 / 100) 2 xbar191) (47 / 25) xbar191 := by
  have hpos : 0 < xbar191 := Real.sqrt_pos.mpr (by norm_num)
  have hs := fig191_steady.2
  have h := nextX_hasDerivAt (θ := 1 / 100) (γ := 2) hpos (by rw [hs]; norm_num)
  convert h using 1
  rw [mul_assoc, hs]
  norm_num

/-- Cochrane (2023), Figure 19.1, p. 444: the map (19.23) has its pole where `θx^γ = 1`; for
`θ = 0.01`, `γ = 2` at `x = 10`, and this is the only positive pole. -/
theorem fig191_pole : (1 / 100 : ℝ) * (10 : ℝ) ^ (2 : ℝ) = 1 ∧
    ∀ x : ℝ, 0 < x → (1 / 100 : ℝ) * x ^ (2 : ℝ) = 1 → x = 10 := by
  refine ⟨by rw [Real.rpow_two]; norm_num, fun x hx h => ?_⟩
  rw [Real.rpow_two] at h
  nlinarith

/-- Cochrane (2023), p. 444 ("in the limit `P_t/M_t → 0` … `lim P_{t+1}/P_t = 1/(1 + δ)`"): for
`γ > 0`, as `x → 0⁺` the gross inflation rate `(1 + µ)(1 − θx̄^γ)/(1 − θx^γ)` of (19.23) tends to
`(1 + µ)(1 − θx̄^γ)`, which equals `β = 1/(1 + δ)` at the steady state (19.22). -/
theorem deflation_limit {θ γ μg β xb : ℝ} (hγ : 0 < γ) (hxb : θ * xb ^ γ = 1 - β / μg)
    (hμ : μg ≠ 0) :
    Tendsto (fun x => μg * (1 - θ * xb ^ γ) / (1 - θ * x ^ γ)) (𝓝[>] 0) (𝓝 β) := by
  have hc : ContinuousAt (fun x : ℝ => x ^ γ) 0 :=
    Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)
  have h0 : (0 : ℝ) ^ γ = 0 := Real.zero_rpow hγ.ne'
  have hden : Tendsto (fun x : ℝ => 1 - θ * x ^ γ) (𝓝[>] 0) (𝓝 (1 - θ * 0)) := by
    have := (hc.tendsto.const_mul θ).const_sub 1
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := (tendsto_const_nhds (x := μg * (1 - θ * xb ^ γ))).div hden (by norm_num)
  have e : μg * (1 - θ * xb ^ γ) / (1 - θ * 0) = β := by
    rw [hxb, mul_zero, sub_zero, div_one]
    field_simp
    ring
  rw [e] at hlim
  exact hlim

/-- Cochrane (2023), pp. 444–445, survey error E13 (corrected): for `θ, γ > 0`, `β > 0`,
`1 + µ > 0`, the inflationary steady state `x̄ > 0` exists (`θx̄^γ = 1 − β/(1 + µ)`) iff
`1 + µ > β`, and then the ratio `x_{t+1}/x_t` near `x = 0` tends to `β/(1 + µ) < 1`, so the
deflationary steady state attracts; the condition is `1 + µ > β` (`µ > −δ/(1 + δ) ≈ −δ`),
not the printed `1 + µ > 1/β`. -/
theorem e13_corrected {θ γ β μg : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hμ : 0 < μg) :
    ((∃ xb, 0 < xb ∧ θ * xb ^ γ = 1 - β / μg) ↔ β < μg) ∧ (β / μg < 1 ↔ β < μg) := by
  refine ⟨⟨fun ⟨xb, hxb, h⟩ => ?_, fun h => ?_⟩, div_lt_one hμ⟩
  · have : 0 < θ * xb ^ γ := mul_pos hθ (Real.rpow_pos_of_pos hxb γ)
    have h2 : β / μg < 1 := by linarith
    exact (div_lt_one hμ).mp h2
  · have hpos : 0 < (1 - β / μg) / θ := by
      have : β / μg < 1 := (div_lt_one hμ).mpr h
      exact div_pos (by linarith) hθ
    refine ⟨((1 - β / μg) / θ) ^ γ⁻¹, Real.rpow_pos_of_pos hpos _, ?_⟩
    rw [Real.rpow_inv_rpow hpos.le hγ.ne']
    field_simp

/-- Cochrane (2023), p. 445, survey error E13: the printed condition `1 + µ > 1/β` is not
necessary: with `β = 5/6` (`δ = 0.2`) and zero money growth (`1 + µ = 1`) the corrected
condition `1 + µ > β` holds but the printed one fails. -/
theorem e13_printed_fails : (5 / 6 : ℝ) < 1 ∧ ¬ ((1 : ℝ) / (5 / 6) < 1) := by
  constructor <;> norm_num

/-- Cochrane (2023), p. 445 ("If we add back the government debt valuation equation … we obtain
a determinate price level"): with `B_{−1} + M_{−1} = D > 0` and real present value `S > 0`, the
valuation equation pins `P_0 = D/S`, hence `x_0 = P_0y/M_0`, and (19.23) then determines the
whole path: any two paths with the same valuation coincide. -/
theorem fiscal_determines_path {g : ℝ → ℝ} {D S y M0 : ℝ} (hS : 0 < S) {P0 P0' : ℝ}
    {x x' : ℕ → ℝ} (hv : D = P0 * S) (hv' : D = P0' * S) (hx0 : x 0 = P0 * y / M0)
    (hx0' : x' 0 = P0' * y / M0) (hx : ∀ t, x (t + 1) = g (x t))
    (hx' : ∀ t, x' (t + 1) = g (x' t)) : P0 = P0' ∧ x = x' := by
  have hP : P0 = P0' := mul_right_cancel₀ hS.ne' (hv.symm.trans hv')
  refine ⟨hP, funext fun t => ?_⟩
  induction t with
  | zero => rw [hx0, hx0', hP]
  | succ t ih => rw [hx t, hx' t, ih]

/-! ### Knownness of `Λ_t/P_t` and `P_t/u_c(t)` from adaptedness -/

/-- Cochrane (2023), §19.3, p. 441 (what "known at date `t`" allows): with the pull-out property,
the variables known at `t` are closed under products. -/
theorem known_mul (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [hPO t a b ha, hb]

/-- Cochrane (2023), §19.3, p. 441, and §19.5.1, p. 449 (measurability bookkeeping): with the
pull-out property, the reciprocal of a nowhere-zero random variable known at `t` is known at `t`
(on any state space: `a·E_t(a⁻¹) = E_t(a·a⁻¹) = 1`). -/
theorem known_inv (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (ha0 : ∀ ω, a ω ≠ 0) : 𝔼.E t a⁻¹ = a⁻¹ := by
  have h1 : a * a⁻¹ = fun _ => (1 : ℝ) := by
    funext ω
    simp [ha0 ω]
  have h := hPO t a a⁻¹ ha
  rw [h1, 𝔼.const] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.mul_apply, Pi.inv_apply] at hω ⊢
  have := ha0 ω
  field_simp
  linear_combination -hω

/-- Cochrane (2023), §19.3, p. 441 (`Λ_t/P_t` and `P_t/u_c(t)`), and §19.5.1, p. 449: a quotient
of random variables known at `t` with nowhere-zero denominator is known at `t`, on any state
space. -/
theorem known_div (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) (hb0 : ∀ ω, b ω ≠ 0) : 𝔼.E t (a / b) = a / b := by
  rw [div_eq_mul_inv, known_mul 𝔼 hPO ha (known_inv 𝔼 hPO hb hb0)]

/-- Cochrane (2023), §19.3, p. 441: with the pull-out property, finite products of variables
known at `t` are known at `t`. -/
theorem known_prod (hPO : 𝔼.PullOut) {t : ℕ} {κ : Type*} (S : Finset κ) {g : κ → Ω → ℝ}
    (hg : ∀ k ∈ S, 𝔼.E t (g k) = g k) : 𝔼.E t (∏ k ∈ S, g k) = ∏ k ∈ S, g k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact 𝔼.const t 1
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, hPO t _ _ (hg k (Finset.mem_insert_self k S)),
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)]

/-- Cochrane (2023), §19.3, p. 441: on a finite state space with the pull-out property, every
function `f(a)` of a variable `a` known at `t` is known at `t` (Lagrange interpolation: `f(a)` is
a polynomial in `a`, and known variables form a unital subalgebra by `known_mul`). This covers
perfect foresight and every finite event tree. (Quotients with nonvanishing denominators are
known on any state space, `known_div`: the pull-out property gives more than the subalgebra
structure.) -/
theorem functionsKnown_of_fintype [Finite Ω] (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ}
    (ha : 𝔼.E t a = a) (f : ℝ → ℝ) :
    𝔼.E t (fun ω => f (a ω)) = fun ω => f (a ω) := by
  classical
  have := Fintype.ofFinite Ω
  set S : Finset ℝ := Finset.univ.image a with hS
  have hfac : ∀ v w : ℝ, 𝔼.E t ((1 / (v - w)) • a - fun _ => w / (v - w)) =
      (1 / (v - w)) • a - fun _ => w / (v - w) := fun v w => by
    rw [map_sub, map_smul, ha, 𝔼.const]
  have key : (fun ω => f (a ω)) = ∑ v ∈ S, f v • ∏ w ∈ S.erase v,
      ((1 / (v - w)) • a - fun _ => w / (v - w)) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, Pi.sub_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single (a ω)]
    · rw [Finset.prod_eq_one, mul_one]
      intro w hw
      have hne : a ω - w ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm
      field_simp
    · intro v _ hv
      rw [Finset.prod_eq_zero (i := a ω)
        (Finset.mem_erase.mpr ⟨Ne.symm hv, Finset.mem_image_of_mem a (Finset.mem_univ ω)⟩),
        mul_zero]
      ring
    · intro h
      exact absurd (Finset.mem_image_of_mem a (Finset.mem_univ ω)) h
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, known_prod 𝔼 hPO _ fun w _ => hfac v w]

/-- Cochrane (2023), §19.1 and §19.3 (the value of a dollar `Λ_t/P_t` and `P_t/u_c(t)`): on a
finite state space with pull-out, the quotient of two variables known at `t` is known at `t`. -/
theorem known_div_of_fintype [Finite Ω] (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ}
    (ha : 𝔼.E t a = a) (hb : 𝔼.E t b = b) : 𝔼.E t (a / b) = a / b := by
  have e : a / b = a * fun ω => (b ω)⁻¹ := by
    funext ω
    simp [div_eq_mul_inv]
  rw [e, hPO t a _ ha, functionsKnown_of_fintype 𝔼 hPO hb (fun r => r⁻¹)]

/-- Cochrane (2023), eq. (19.11), p. 439, on any state space: `eq1911_iff_tvc` with the
knownness of `Λ_t/P_t` derived (`known_div`) from adapted `Λ` and `P`. -/
theorem eq1911_iff_tvc_adapted (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hΛa : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => Regimes.partial192 𝔼 Λ P N (fun k => s k + c k - y k) t T ω) atTop
        (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) :=
  eq1911_iff_tvc 𝔼 hPO hBP (fun k => known_div 𝔼 hPO (hΛa k) (hPa k) (hP k)) hBa hB hQ hi
    hP hflow t ω

/-- Cochrane (2023), eq. (19.12), p. 439, on any state space: `eq1912_of_tvc` with the
knownness of `Λ_t/P_t` derived (`known_div`) from adapted `Λ` and `P`. -/
theorem eq1912_of_tvc_adapted (hPO : 𝔼.PullOut) {Λ P N i Bm Q y c s : ℕ → Ω → ℝ}
    (hBP : Regimes.BondPricing 𝔼 Λ P i) (hΛa : 𝔼.Adapted Λ) (hPa : 𝔼.Adapted P)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : HHFlow Bm N P y c s Q) {t : ℕ} {ω : Ω}
    (hbond : Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0))
    (hmoney : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => Regimes.partial193 𝔼 Λ P N i (fun k => s k + c k - y k) t T ω) atTop
      (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) :=
  eq1912_of_tvc 𝔼 hPO hBP (fun k => known_div 𝔼 hPO (hΛa k) (hPa k) (hP k)) hBa hB hNa hN
    hQ hi hP hflow hbond hmoney

/-- Cochrane (2023), (19.15)–(19.16), p. 441, on any state space: the iterated value of
money with the knownness of `u_c(t)/P_t` and `P_t/u_c(t)` derived (`known_div`) from adapted
`u_c` and `P`. -/
theorem value_of_money_iterated_adapted (hPO : 𝔼.PullOut) {β : ℝ}
    {uc um P i : ℕ → Ω → ℝ} (huca : 𝔼.Adapted uc) (hPa : 𝔼.Adapted P)
    (huc : ∀ t ω, uc t ω ≠ 0) (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t T : ℕ) :
    uc t / P t = ∑ j ∈ Finset.range (T + 1), β ^ j • 𝔼.E t (um (t + j) / P (t + j)) +
      β ^ (T + 1) • 𝔼.E t (uc (t + T + 1) / P (t + T + 1)) :=
  value_of_money_iterated 𝔼 hPO (fun k => known_div 𝔼 hPO (huca k) (hPa k) (hP k))
    (fun k => known_div 𝔼 hPO (hPa k) (huca k) (huc k)) huc hP hi h1915 h1916 t T

/-- Cochrane (2023), p. 441, on any state space: `value_of_money_limit` with the knownness
hypotheses derived (`known_div`) from adapted `u_c` and `P`. -/
theorem value_of_money_limit_adapted (hPO : 𝔼.PullOut) {β : ℝ}
    {uc um P i : ℕ → Ω → ℝ} (huca : 𝔼.Adapted uc) (hPa : 𝔼.Adapted P)
    (huc : ∀ t ω, uc t ω ≠ 0) (hP : ∀ t ω, P t ω ≠ 0) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (h1915 : ∀ t, 𝔼.E t (β • (uc (t + 1) / uc t * (P t / P (t + 1)))) = 1 / (1 + i t))
    (h1916 : ∀ t ω, um t ω / uc t ω = i t ω / (1 + i t ω)) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun T => β ^ T * 𝔼.E t (uc (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (um (t + j) / P (t + j)) ω) atTop
      (𝓝 (uc t ω / P t ω)) :=
  value_of_money_limit 𝔼 hPO (fun k => known_div 𝔼 hPO (huca k) (hPa k) (hP k))
    (fun k => known_div 𝔼 hPO (hPa k) (huca k) (huc k)) huc hP hi h1915 h1916 t ω htvc

/-! ### Footnote 1 under uncertainty: the time-0 problem on a finite event tree -/

namespace FootnoteTree

open ExpectationsFiniteTree

variable {Ω' : Type*} [Fintype Ω'] (T : FiniteTree Ω')

/-- Cochrane (2023), footnote 1, p. 440 (`c_t(x^t)`): a process is a function of the date-`t`
node, i.e. constant on the date-`t` information cells of the tree. -/
def TAdapted (x : ℕ → Ω' → ℝ) : Prop := ∀ t ω ω', T.info t ω' ω → x t ω' = x t ω

/-- Cochrane (2023), footnote 1, p. 440: the date-`t` cost
`∑_{x^t} pr(x^t)(Λ_t/Λ_0)(c_t + ι_tm_t)` (`q = Λ_t/Λ_0`, `ι = i/(1 + i)`, `m = M/P`). -/
noncomputable def dateCost (q ι c m : ℕ → Ω' → ℝ) (k : ℕ) : ℝ :=
  ∑ ω, T.prob ω * (q k ω * (c k ω + ι k ω * m k ω))

/-- Cochrane (2023), footnote 1, p. 440: the date-`t` term `∑_{x^t} βᵗpr(x^t)u(c_t, m_t)`. -/
noncomputable def dateUtil (β : ℝ) (u : ℝ → ℝ → ℝ) (c m : ℕ → Ω' → ℝ) (k : ℕ) : ℝ :=
  ∑ ω, T.prob ω * (β ^ k * u (c k ω) (m k ω))

/-- Cochrane (2023), footnote 1, p. 440: a node-contingent plan is feasible when it is adapted
and its present-value cost converges and is at most wealth `W`. -/
def TFeasible (q ι : ℕ → Ω' → ℝ) (W : ℝ) (c m : ℕ → Ω' → ℝ) : Prop :=
  TAdapted T c ∧ TAdapted T m ∧ Summable (dateCost T q ι c m) ∧
    ∑' k, dateCost T q ι c m k ≤ W

/-- Cochrane (2023), (19.9), p. 439 and footnote 1, p. 440: an optimal plan of the time-0
problem on the tree maximises `∑_t ∑_{x^t} βᵗpr(x^t)u` over feasible plans. -/
def TOptimal (β : ℝ) (u : ℝ → ℝ → ℝ) (q ι : ℕ → Ω' → ℝ) (W : ℝ) (c m : ℕ → Ω' → ℝ) : Prop :=
  TFeasible T q ι W c m ∧ Summable (dateUtil T β u c m) ∧
    ∀ c' m', TFeasible T q ι W c' m' → Summable (dateUtil T β u c' m') →
      ∑' k, dateUtil T β u c' m' k ≤ ∑' k, dateUtil T β u c m k

open Classical in
/-- Cochrane (2023), footnote 1, p. 440: the indicator of the date-`t` node (information cell)
containing `ω₀`. -/
noncomputable def cell (t : ℕ) (ω0 ω : Ω') : ℝ := if T.info t ω ω0 then 1 else 0

/-- Cochrane (2023), footnote 1, p. 440: the node indicator is a date-`t` variable. -/
theorem cell_adapted {t : ℕ} {ω0 ω ω' : Ω'} (h : T.info t ω' ω) :
    cell T t ω0 ω' = cell T t ω0 ω := by
  unfold cell
  by_cases h1 : T.info t ω ω0
  · have h2 : T.info t ω' ω0 := (T.info t).iseqv.trans h h1
    simp only [h1, h2, ↓reduceIte]
  · have h2 : ¬ T.info t ω' ω0 := fun h2 => h1 ((T.info t).iseqv.trans
      ((T.info t).iseqv.symm h) h2)
    simp only [h1, h2, ↓reduceIte]

/-- Cochrane (2023), footnote 1, p. 440: changing a date-`t` variable at one node changes the
date-`t` expectation by the node's probability times the change. -/
theorem sum_perturb_cell {t : ℕ} {ω0 : Ω'} (F : Ω' → ℝ → ℝ) (x : Ω' → ℝ)
    (hx : ∀ ω, T.info t ω ω0 → x ω = x ω0) (hF : ∀ ω, T.info t ω ω0 → F ω = F ω0) (d : ℝ) :
    ∑ ω, T.prob ω * F ω (x ω + d * cell T t ω0 ω) =
      ∑ ω, T.prob ω * F ω (x ω) + T.mass t ω0 * (F ω0 (x ω0 + d) - F ω0 (x ω0)) := by
  classical
  unfold FiniteTree.mass
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  unfold cell
  by_cases h : T.info t ω ω0
  · simp only [h, ↓reduceIte, mul_one, hx ω h, hF ω h]
    ring
  · simp only [h, ↓reduceIte, mul_zero, add_zero, zero_mul]

/-- Cochrane (2023), footnote 1, p. 440: perturbing a plan at the date-`t` node of `ω₀` and the
date-`s` node of `ω₁` keeps it adapted. -/
theorem perturb_adapted {x : ℕ → Ω' → ℝ} (hx : TAdapted T x) (t s : ℕ) (ω0 ω1 : Ω')
    (d e : ℝ) : TAdapted T (fun k ω => x k ω + (if k = t then d * cell T t ω0 ω else 0) +
      (if k = s then e * cell T s ω1 ω else 0)) := by
  intro k ω ω' h
  have h1 : (if k = t then d * cell T t ω0 ω' else 0) =
      (if k = t then d * cell T t ω0 ω else 0) := by
    split_ifs with hk
    · subst hk; rw [cell_adapted T h]
    · rfl
  have h2 : (if k = s then e * cell T s ω1 ω' else 0) =
      (if k = s then e * cell T s ω1 ω else 0) := by
    split_ifs with hk
    · subst hk; rw [cell_adapted T h]
    · rfl
  simp only
  rw [hx k ω ω' h, h1, h2]

/-- Cochrane (2023), footnote 1, p. 440: a cost-neutral change of an optimal plan at two dates
`t ≠ s` cannot raise the expected utility of those dates. -/
theorem tperturb_le {β W : ℝ} {u : ℝ → ℝ → ℝ} {q ι c m c' m' : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) {t s : ℕ} (hts : t ≠ s) (hca : TAdapted T c')
    (hma : TAdapted T m') (hc : ∀ k, k ≠ t → k ≠ s → c' k = c k)
    (hm : ∀ k, k ≠ t → k ≠ s → m' k = m k)
    (hcost : dateCost T q ι c' m' t + dateCost T q ι c' m' s =
      dateCost T q ι c m t + dateCost T q ι c m s) :
    dateUtil T β u c' m' t + dateUtil T β u c' m' s ≤
      dateUtil T β u c m t + dateUtil T β u c m s := by
  obtain ⟨⟨-, -, hfs, hfW⟩, hus, hmax⟩ := hopt
  have h1 := tsum_modify_two (f := dateCost T q ι c m) (g := dateCost T q ι c' m') hts
    (fun k hkt hks => by simp only [dateCost, hc k hkt hks, hm k hkt hks]) hfs
  have h2 := tsum_modify_two (f := dateUtil T β u c m) (g := dateUtil T β u c' m') hts
    (fun k hkt hks => by simp only [dateUtil, hc k hkt hks, hm k hkt hks]) hus
  have hfeas : TFeasible T q ι W c' m' := ⟨hca, hma, h1.1, by rw [h1.2]; linarith⟩
  have := hmax c' m' hfeas h2.1
  rw [h2.2] at this
  linarith

/-- Cochrane (2023), eq. (19.13), p. 440, under uncertainty (node form): at an optimum on the
tree, for nodes `x^t ∋ ω₀` and `x^s ∋ ω₁` at dates `t ≠ s`,
`βᵗu_c(x^t)q(x^s) = βˢu_c(x^s)q(x^t)` (shift consumption between the two nodes at constant
cost). -/
theorem tree_foc_cc {β W : ℝ} {u uc : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) (hq : TAdapted T q) (hι : TAdapted T ι)
    (huc : ∀ k ω, HasDerivAt (fun x => u x (m k ω)) (uc (c k ω) (m k ω)) (c k ω)) {t s : ℕ}
    (hts : t ≠ s) (ω0 ω1 : Ω') :
    β ^ t * uc (c t ω0) (m t ω0) * q s ω1 = β ^ s * uc (c s ω1) (m s ω1) * q t ω0 := by
  have hca := hopt.1.1
  have hma := hopt.1.2.1
  set Mt := T.mass t ω0 with hMt
  set Ms := T.mass s ω1 with hMs
  have hMt0 : 0 < Mt := T.mass_pos t ω0
  have hMs0 : 0 < Ms := T.mass_pos s ω1
  set A := q s ω1 * Ms with hA
  set B := q t ω0 * Mt with hB
  set D : ℝ → ℝ := fun ε => Mt * (β ^ t * u (c t ω0 + ε * A) (m t ω0)) +
    Ms * (β ^ s * u (c s ω1 + -(ε * B)) (m s ω1)) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    set c' : ℕ → Ω' → ℝ := fun k ω => c k ω + (if k = t then ε * A * cell T t ω0 ω else 0) +
      (if k = s then -(ε * B) * cell T s ω1 ω else 0) with hc'
    have hut := sum_perturb_cell T (fun ω z => β ^ t * u z (m t ω)) (c t)
      (fun ω h => hca t ω0 ω h) (fun ω h => by funext z; rw [hma t ω0 ω h]) (ε * A)
    have hus := sum_perturb_cell T (fun ω z => β ^ s * u z (m s ω)) (c s)
      (fun ω h => hca s ω1 ω h) (fun ω h => by funext z; rw [hma s ω1 ω h]) (-(ε * B))
    have hkt := sum_perturb_cell T (fun ω z => q t ω * (z + ι t ω * m t ω)) (c t)
      (fun ω h => hca t ω0 ω h)
      (fun ω h => by funext z; rw [hq t ω0 ω h, hι t ω0 ω h, hma t ω0 ω h]) (ε * A)
    have hks := sum_perturb_cell T (fun ω z => q s ω * (z + ι s ω * m s ω)) (c s)
      (fun ω h => hca s ω1 ω h)
      (fun ω h => by funext z; rw [hq s ω1 ω h, hι s ω1 ω h, hma s ω1 ω h]) (-(ε * B))
    have h := tperturb_le T hopt hts (perturb_adapted T hca t s ω0 ω1 (ε * A) (-(ε * B)))
      hma (fun k hkt hks => by funext ω; simp [hkt, hks]) (fun _ _ _ => rfl) (by
        simp only [dateCost, hts, Ne.symm hts, ↓reduceIte, add_zero]
        rw [← hMt] at hkt
        rw [← hMs] at hks
        rw [hkt, hks]
        simp only [hA, hB]
        ring)
    simp only [dateUtil, hts, Ne.symm hts, ↓reduceIte, add_zero] at h
    rw [← hMt] at hut
    rw [← hMs] at hus
    rw [hut, hus] at h
    simp only [hD, zero_mul, add_zero, neg_zero]
    linarith
  have hd1 : HasDerivAt (fun ε => c t ω0 + ε * A) A 0 := by
    simpa using (hasDerivAt_mul_const A).const_add (c t ω0)
  have hd2 : HasDerivAt (fun ε => c s ω1 + -(ε * B)) (-B) 0 := by
    simpa using ((hasDerivAt_mul_const B).neg).const_add (c s ω1)
  have hu1 : HasDerivAt (fun ε => u (c t ω0 + ε * A) (m t ω0)) (uc (c t ω0) (m t ω0) * A) 0 :=
    HasDerivAt.comp_of_eq 0 (huc t ω0) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s ω1 + -(ε * B)) (m s ω1))
      (uc (c s ω1) (m s ω1) * -B) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s ω1) hd2 (by simp)
  have hDd : HasDerivAt D (Mt * (β ^ t * (uc (c t ω0) (m t ω0) * A)) +
      Ms * (β ^ s * (uc (c s ω1) (m s ω1) * -B))) 0 :=
    ((hu1.const_mul _).const_mul _).add ((hu2.const_mul _).const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have h0 := hmax.hasDerivAt_eq_zero hDd
  have hfac : Mt * Ms * (β ^ t * uc (c t ω0) (m t ω0) * q s ω1 -
      β ^ s * uc (c s ω1) (m s ω1) * q t ω0) = 0 := by
    rw [← h0, hA, hB]
    ring
  have := (mul_eq_zero.mp hfac).resolve_left (mul_pos hMt0 hMs0).ne'
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, under uncertainty (node form): at an optimum
on the tree, for nodes `x^t ∋ ω₀`, `x^s ∋ ω₁` at dates `t ≠ s`,
`βᵗu_m(x^t)q(x^s) = βˢu_c(x^s)q(x^t)ι(x^t)` (trade real money at one node against consumption at
the other). -/
theorem tree_foc_mc {β W : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) (hq : TAdapted T q) (hι : TAdapted T ι)
    (huc : ∀ k ω, HasDerivAt (fun x => u x (m k ω)) (uc (c k ω) (m k ω)) (c k ω))
    (hum : ∀ k ω, HasDerivAt (fun x => u (c k ω) x) (um (c k ω) (m k ω)) (m k ω)) {t s : ℕ}
    (hts : t ≠ s) (ω0 ω1 : Ω') :
    β ^ t * um (c t ω0) (m t ω0) * q s ω1 =
      β ^ s * uc (c s ω1) (m s ω1) * q t ω0 * ι t ω0 := by
  have hca := hopt.1.1
  have hma := hopt.1.2.1
  set Mt := T.mass t ω0 with hMt
  set Ms := T.mass s ω1 with hMs
  have hMt0 : 0 < Mt := T.mass_pos t ω0
  have hMs0 : 0 < Ms := T.mass_pos s ω1
  set A := q s ω1 * Ms with hA
  set B := q t ω0 * ι t ω0 * Mt with hB
  set D : ℝ → ℝ := fun ε => Mt * (β ^ t * u (c t ω0) (m t ω0 + ε * A)) +
    Ms * (β ^ s * u (c s ω1 + -(ε * B)) (m s ω1)) with hD
  have hle : ∀ ε, D ε ≤ D 0 := by
    intro ε
    set c' : ℕ → Ω' → ℝ := fun k ω => c k ω + (if k = t then 0 * cell T t ω0 ω else 0) +
      (if k = s then -(ε * B) * cell T s ω1 ω else 0) with hc'
    set m' : ℕ → Ω' → ℝ := fun k ω => m k ω + (if k = t then ε * A * cell T t ω0 ω else 0) +
      (if k = s then 0 * cell T s ω1 ω else 0) with hm'
    have hut := sum_perturb_cell T (fun ω z => β ^ t * u (c t ω) z) (m t)
      (fun ω h => hma t ω0 ω h) (fun ω h => by funext z; rw [hca t ω0 ω h]) (ε * A)
    have hus := sum_perturb_cell T (fun ω z => β ^ s * u z (m s ω)) (c s)
      (fun ω h => hca s ω1 ω h) (fun ω h => by funext z; rw [hma s ω1 ω h]) (-(ε * B))
    have hkt := sum_perturb_cell T (fun ω z => q t ω * (c t ω + ι t ω * z)) (m t)
      (fun ω h => hma t ω0 ω h)
      (fun ω h => by funext z; rw [hq t ω0 ω h, hι t ω0 ω h, hca t ω0 ω h]) (ε * A)
    have hks := sum_perturb_cell T (fun ω z => q s ω * (z + ι s ω * m s ω)) (c s)
      (fun ω h => hca s ω1 ω h)
      (fun ω h => by funext z; rw [hq s ω1 ω h, hι s ω1 ω h, hma s ω1 ω h]) (-(ε * B))
    have h := tperturb_le T hopt hts (perturb_adapted T hca t s ω0 ω1 0 (-(ε * B)))
      (perturb_adapted T hma t s ω0 ω1 (ε * A) 0)
      (fun k hkt hks => by funext ω; simp [hkt, hks])
      (fun k hkt hks => by funext ω; simp [hkt, hks]) (by
        simp only [dateCost, hts, Ne.symm hts, ↓reduceIte, add_zero, zero_mul]
        rw [← hMt] at hkt
        rw [← hMs] at hks
        rw [hkt, hks]
        simp only [hA, hB]
        ring)
    simp only [dateUtil, hts, Ne.symm hts, ↓reduceIte, add_zero, zero_mul] at h
    rw [← hMt] at hut
    rw [← hMs] at hus
    rw [hut, hus] at h
    simp only [hD, zero_mul, add_zero, neg_zero]
    linarith
  have hd1 : HasDerivAt (fun ε => m t ω0 + ε * A) A 0 := by
    simpa using (hasDerivAt_mul_const A).const_add (m t ω0)
  have hd2 : HasDerivAt (fun ε => c s ω1 + -(ε * B)) (-B) 0 := by
    simpa using ((hasDerivAt_mul_const B).neg).const_add (c s ω1)
  have hu1 : HasDerivAt (fun ε => u (c t ω0) (m t ω0 + ε * A)) (um (c t ω0) (m t ω0) * A) 0 :=
    HasDerivAt.comp_of_eq 0 (hum t ω0) hd1 (by simp)
  have hu2 : HasDerivAt (fun ε => u (c s ω1 + -(ε * B)) (m s ω1))
      (uc (c s ω1) (m s ω1) * -B) 0 :=
    HasDerivAt.comp_of_eq 0 (huc s ω1) hd2 (by simp)
  have hDd : HasDerivAt D (Mt * (β ^ t * (um (c t ω0) (m t ω0) * A)) +
      Ms * (β ^ s * (uc (c s ω1) (m s ω1) * -B))) 0 :=
    ((hu1.const_mul _).const_mul _).add ((hu2.const_mul _).const_mul _)
  have hmax : IsLocalMax D 0 := Filter.Eventually.of_forall hle
  have h0 := hmax.hasDerivAt_eq_zero hDd
  have hfac : Mt * Ms * (β ^ t * um (c t ω0) (m t ω0) * q s ω1 -
      β ^ s * uc (c s ω1) (m s ω1) * q t ω0 * ι t ω0) = 0 := by
    rw [← h0, hA, hB]
    ring
  have := (mul_eq_zero.mp hfac).resolve_left (mul_pos hMt0 hMs0).ne'
  linarith

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, and footnote 1, under uncertainty: at an
optimal plan of the time-0 problem on a finite event tree (with `q_0 = Λ_0/Λ_0 = 1` and
`q_1 > 0`), at every node `βᵗu_c(x^t) = λ(Λ_t/Λ_0)(x^t)` and
`βᵗu_m(x^t) = λ(Λ_t/Λ_0)(x^t) i_t/(1 + i_t)`, with `λ = u_c` at the date-0 node. -/
theorem tree_foc_1913_1914 {β W : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hopt : TOptimal T β u q ι W c m) (hq : TAdapted T q) (hι : TAdapted T ι)
    (hq0 : ∀ ω, q 0 ω = 1) (hq1 : ∀ ω, 0 < q 1 ω)
    (huc : ∀ k ω, HasDerivAt (fun x => u x (m k ω)) (uc (c k ω) (m k ω)) (c k ω))
    (hum : ∀ k ω, HasDerivAt (fun x => u (c k ω) x) (um (c k ω) (m k ω)) (m k ω)) (t : ℕ)
    (ω : Ω') :
    β ^ t * uc (c t ω) (m t ω) = uc (c 0 ω) (m 0 ω) * q t ω ∧
      β ^ t * um (c t ω) (m t ω) = uc (c 0 ω) (m 0 ω) * q t ω * ι t ω := by
  have hc : ∀ k, β ^ k * uc (c k ω) (m k ω) = uc (c 0 ω) (m 0 ω) * q k ω := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hq0]
    · have := tree_foc_cc T hopt hq hι huc (Nat.pos_iff_ne_zero.mp hk) ω ω
      rw [hq0] at this
      simpa using this
  refine ⟨hc t, ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have h1 := tree_foc_mc T hopt hq hι huc hum (t := 0) (s := 1) zero_ne_one ω ω
    have h2 := hc 1
    simp only [pow_zero, one_mul, pow_one] at h1 h2 ⊢
    rw [h2, hq0] at h1
    rw [hq0]
    exact mul_right_cancel₀ (hq1 ω).ne' (by linarith)
  · have := tree_foc_mc T hopt hq hι huc hum (Nat.pos_iff_ne_zero.mp ht) (s := 0) ω ω
    rw [hq0] at this
    simpa using this

/-- Cochrane (2023), footnote 1, p. 440: when the date-0 information is trivial (one root node),
the multiplier `λ = u_c(c_0, M_0/P_0)` is the same in every state. -/
theorem lambda_const {c m : ℕ → Ω' → ℝ} (uc : ℝ → ℝ → ℝ) (hca : TAdapted T c)
    (hma : TAdapted T m) (htriv : ∀ a b, T.info 0 a b) (ω ω' : Ω') :
    uc (c 0 ω) (m 0 ω) = uc (c 0 ω') (m 0 ω') := by
  rw [hca 0 ω' ω (htriv ω ω'), hma 0 ω' ω (htriv ω ω')]

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440, under uncertainty
(sufficiency): if utility satisfies the supergradient inequality at every node (joint concavity,
`supergradient_of_concave`), `β ≥ 0`, the node first-order conditions hold with `λ ≥ 0` and the
budget binds, then the adapted plan is optimal on the tree. -/
theorem tree_optimal_of_foc {β W lam : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → Ω' → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam)
    (hsup : ∀ k ω c' m', u c' m' ≤ u (c k ω) (m k ω) + uc (c k ω) (m k ω) * (c' - c k ω) +
      um (c k ω) (m k ω) * (m' - m k ω))
    (hfoc : ∀ k ω, β ^ k * uc (c k ω) (m k ω) = lam * q k ω ∧
      β ^ k * um (c k ω) (m k ω) = lam * q k ω * ι k ω)
    (hfeas : TFeasible T q ι W c m) (hbind : ∑' k, dateCost T q ι c m k = W)
    (hus : Summable (dateUtil T β u c m)) : TOptimal T β u q ι W c m := by
  refine ⟨hfeas, hus, fun c' m' hf' hu' => ?_⟩
  have hpt : ∀ k, dateUtil T β u c' m' k ≤ dateUtil T β u c m k +
      lam * (dateCost T q ι c' m' k - dateCost T q ι c m k) := by
    intro k
    unfold dateUtil dateCost
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hsup k ω (c' k ω) (m' k ω)) (pow_nonneg hβ k)
    have h2 := hfoc k ω
    have e : β ^ k * (u (c k ω) (m k ω) + uc (c k ω) (m k ω) * (c' k ω - c k ω) +
        um (c k ω) (m k ω) * (m' k ω - m k ω)) = β ^ k * u (c k ω) (m k ω) +
        lam * (q k ω * (c' k ω + ι k ω * m' k ω) - q k ω * (c k ω + ι k ω * m k ω)) := by
      linear_combination (c' k ω - c k ω) * h2.1 + (m' k ω - m k ω) * h2.2
    have hp := (T.prob_pos ω).le
    have h3 := mul_le_mul_of_nonneg_left (h1.trans_eq e) hp
    linarith
  have hR : HasSum (fun k => dateUtil T β u c m k +
      lam * (dateCost T q ι c' m' k - dateCost T q ι c m k))
      (∑' k, dateUtil T β u c m k + lam * (∑' k, dateCost T q ι c' m' k -
        ∑' k, dateCost T q ι c m k)) :=
    hus.hasSum.add ((hf'.2.2.1.hasSum.sub hfeas.2.2.1.hasSum).mul_left lam)
  have hle := hasSum_le hpt hu'.hasSum hR
  have : lam * (∑' k, dateCost T q ι c' m' k - ∑' k, dateCost T q ι c m k) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by rw [hbind]; linarith [hf'.2.2.2])
  linarith

end FootnoteTree

end Cochrane.Monetarism.MoneyInUtility
