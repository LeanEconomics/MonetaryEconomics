/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.ForwardSolution

/-!
# Equilibria and regimes: money demand and the government debt valuation equation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.1 (pp. 434–435), and the
precise claims of Chapter 11 (§11.1–11.3, pp. 314–319) and §14.1 (p. 342) on open-market
operations, elastic currency and helicopter drops.

Conventions. Processes are `ℕ → Ω → ℝ` for an arbitrary `ExpectationSystem` (so every result
holds under perfect foresight and under genuine uncertainty). `N t` is the money carried into
date `t`, the book's `M_{t−1}` (so the book's `M_{t+j}` is `N (t + j + 1)`), `Bm t` is the
book's `B_{t−1}`, `Λ` the (real) stochastic discount factor level and `P` the price level. The
infinite sums `E_t ∑_{j≥0} …` of (19.2)–(19.3) are stated as limits of the conditional
expectations of the partial sums, multiplied through by the known `Λ_t > 0`.

## Main results

* (19.1) `QuantityEq`. (19.2) ⇔ (19.3): the summation-by-parts identity `sum_by_parts` (any
  horizon `T`), `eq192_iff_eq193` (equivalence under the money transversality condition), and
  `tail_tendsto_zero_of_book_tvc` (the book's money TVC `E_tΛ_{t+T}M_{t+T}/P_{t+T} → 0` implies the
  one used, for `i ≥ 0`, `M ≥ 0`).
* The valuation equation from the flow constraint: `flow_value_recursion`,
  `flow_pv_iff_tvc` ((19.2) holds iff the bond transversality condition holds) and
  `flow_eq193_of_tvc`.
* §19.1 regimes (survey NI-7): `seigniorage_indep_price` (under (19.1) the seigniorage term of
  (19.3) does not involve `P`), `ni7` (monetary and fiscal regimes observationally equivalent:
  every equilibrium is the unique equilibrium of an active-money/passive-fiscal regime and of an
  active-fiscal/passive-money regime, with identical observables), `double_passive`
  (indeterminacy), `double_active_iff` (overdetermination), `passive_surplus_realises`
  (a passive surplus rule exists for every target value of debt).
* Ch11: V1 `spread_term_eq_zero_iff`, `partial111_of_no_spread`, `omo_irrelevant` (with
  `i = i^m` an open-market swap leaves the price level unchanged); V3 `spread_existsUnique`
  (money demand met by the spread); V4 `omo_equivalence` (both regimes describe the same fall in
  money, rise in bonds and rise in surpluses); V5 `elastic_currency`.
* §14.1, p. 342 (V11), helicopter magnitudes: `ftpl_price_ratio`, `quantity_price_ratio`,
  `helicopter_fiscal`, `helicopter_fiscal_approx`, `helicopter_monetarist`,
  `helicopter_cash_share`, `helicopter_bond_loss`.
-/

namespace Cochrane.Monetarism.Regimes

open Filter Topology
open Cochrane.Monetarism.ForwardSolution (Solves iterate_A15 tendsto_partial_A16)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (19.1) and the summation by parts (19.2) ⇔ (19.3) -/

/-- Cochrane (2023), eq. (19.1), p. 434 (and (11.2), p. 315, with `i = i^m`): money demand
`M_t V_t = P_t y_t` at every date and in every state. -/
def QuantityEq (M V P y : ℕ → Ω → ℝ) : Prop := ∀ t, M t * V t = P t * y t

/-- Cochrane (2023), §3.4 and eq. (19.3), p. 434 (`1/(1 + i_t) = E_t[Λ_{t+1}P_t/(Λ_tP_{t+1})]`):
the one-period nominal bond is priced by the stochastic discount factor, written for the value
of a dollar `Λ_t/P_t` as `E_t(Λ_{t+1}/P_{t+1}) = (Λ_t/P_t)/(1 + i_t)`. -/
def BondPricing (Λ P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (Λ (t + 1) / P (t + 1)) = Λ t / P t / (1 + i t)

/-- Cochrane (2023), eq. (19.2), p. 434, multiplied through by the known `Λ_t`: the date-`t`
partial sum `∑_{j<T} E_t[Λ_{t+j}((M_{t+j} − M_{t+j−1})/P_{t+j} + s_{t+j})]` (with
`M_{t+j} = N_{t+j+1}`). -/
noncomputable def partial192 (Λ P N s : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T,
    𝔼.E t (Λ (t + j) * ((N (t + j + 1) - N (t + j)) / P (t + j) + s (t + j)))

/-- Cochrane (2023), eq. (19.3), p. 434, multiplied through by the known `Λ_t`: the date-`t`
partial sum `∑_{j<T} E_t[Λ_{t+j}(i_{t+j}/(1 + i_{t+j}) · M_{t+j}/P_{t+j} + s_{t+j})]`. -/
noncomputable def partial193 (Λ P N i s : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T,
    𝔼.E t (Λ (t + j) * (i (t + j) / (1 + i (t + j)) * N (t + j + 1) / P (t + j) + s (t + j)))

/-- Cochrane (2023), eq. (19.3), p. 434 (the step behind the summation by parts): for `t ≤ k`,
`E_t[Λ_{k+1}M_k/P_{k+1}] = E_t[M_k(Λ_k/P_k)/(1 + i_k)]`, since `M_k` is known at `k`. -/
theorem E_next_value (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (hBP : BondPricing 𝔼 Λ P i)
    (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1)) {t k : ℕ} (htk : t ≤ k) :
    𝔼.E t (Λ (k + 1) * N (k + 1) / P (k + 1)) =
      𝔼.E t (N (k + 1) * (Λ k / P k / (1 + i k))) := by
  have h1 : Λ (k + 1) * N (k + 1) / P (k + 1) = N (k + 1) * (Λ (k + 1) / P (k + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring
  rw [h1, ← 𝔼.tower htk, hPO k _ _ (hN k), hBP k]

/-- Cochrane (2023), eq. (19.3), p. 434: the one-period form of the summation by parts,
`E_t[Λ_{k+1}M_k/P_{k+1}] = E_t[Λ_kM_k/P_k − Λ_k(i_k/(1 + i_k))M_k/P_k]`. -/
theorem step_identity (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (hBP : BondPricing 𝔼 Λ P i)
    (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1)) (hi : ∀ t ω, 1 + i t ω ≠ 0) {t k : ℕ}
    (htk : t ≤ k) :
    𝔼.E t (Λ (k + 1) * N (k + 1) / P (k + 1)) =
      𝔼.E t (Λ k * N (k + 1) / P k - Λ k * (i k / (1 + i k) * N (k + 1) / P k)) := by
  rw [E_next_value 𝔼 hPO hBP hN htk]
  congr 1
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.one_apply]
  have h := hi k ω
  have key : (1 + i k ω)⁻¹ + i k ω * (1 + i k ω)⁻¹ = 1 := by
    field_simp
  simp only [div_eq_mul_inv]
  linear_combination (Λ k ω * N (k + 1) ω * (P k ω)⁻¹) * key

/-- Cochrane (2023), (19.2)–(19.3), p. 434, the summation by parts at every horizon `T`:
`∑_{j<T} E_t[Λ(ΔM/P + s)] + Λ_tM_{t−1}/P_t = ∑_{j<T} E_t[Λ(iM/((1+i)P) + s)]
  + E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}]`. -/
theorem sum_by_parts (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (s : ℕ → Ω → ℝ)
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hi : ∀ t ω, 1 + i t ω ≠ 0) (t T : ℕ) :
    partial192 𝔼 Λ P N s t T + Λ t * N t / P t =
      partial193 𝔼 Λ P N i s t T + 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) := by
  induction T with
  | zero =>
    simp only [partial192, partial193, Finset.range_zero, Finset.sum_empty, zero_add, add_zero]
    have h1 : Λ t * N t / P t = N t * (Λ t / P t) := by
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO t _ _ (hNa t), hφ t]
  | succ T ih =>
    simp only [partial192, partial193, Finset.sum_range_succ] at ih ⊢
    rw [← add_assoc t T 1, step_identity 𝔼 hPO hBP hN hi (Nat.le_add_right t T)]
    have hDA : 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) +
        𝔼.E t (Λ (t + T) * ((N (t + T + 1) - N (t + T)) / P (t + T) + s (t + T))) =
        𝔼.E t (Λ (t + T) * (i (t + T) / (1 + i (t + T)) * N (t + T + 1) / P (t + T) +
          s (t + T))) +
        𝔼.E t (Λ (t + T) * N (t + T + 1) / P (t + T) -
          Λ (t + T) * (i (t + T) / (1 + i (t + T)) * N (t + T + 1) / P (t + T))) := by
      rw [← map_add, ← map_add]
      congr 1
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
      ring
    linear_combination ih + hDA

/-- Cochrane (2023), eqs. (19.2) and (19.3), p. 434: given the bond-pricing condition and the
money transversality condition `E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}] → 0`, the valuation equation in
the form (19.2) `B_{t−1}/P_t = E_t∑(Λ_{t+j}/Λ_t)(ΔM_{t+j}/P_{t+j} + s_{t+j})` holds if and only if
it holds in the form (19.3) `(B_{t−1} + M_{t−1})/P_t = E_t∑(Λ_{t+j}/Λ_t)(iM/((1+i)P) + s)`
(both multiplied through by `Λ_t`). -/
theorem eq192_iff_eq193 (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ} (s Bm : ℕ → Ω → ℝ)
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hi : ∀ t ω, 1 + i t ω ≠ 0) {t : ℕ} {ω : Ω}
    (hTVC : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => partial192 𝔼 Λ P N s t T ω) atTop (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => partial193 𝔼 Λ P N i s t T ω) atTop
        (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) := by
  have hid : ∀ T, partial193 𝔼 Λ P N i s t T ω = partial192 𝔼 Λ P N s t T ω +
      Λ t ω * N t ω / P t ω - 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω := by
    intro T
    have h := congrFun (sum_by_parts 𝔼 hPO s hBP hφ hNa hN hi t T) ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply] at h
    linarith
  have hval : Λ t ω * (Bm t ω + N t ω) / P t ω =
      Λ t ω * Bm t ω / P t ω + Λ t ω * N t ω / P t ω - 0 := by ring
  constructor
  · intro h
    rw [hval]
    exact ((h.add_const _).sub hTVC).congr fun T => (hid T).symm
  · intro h
    have h2 := (h.sub_const (Λ t ω * N t ω / P t ω)).add hTVC
    have hv : Λ t ω * (Bm t ω + N t ω) / P t ω - Λ t ω * N t ω / P t ω + 0 =
        Λ t ω * Bm t ω / P t ω := by ring
    rw [hv] at h2
    refine h2.congr fun T => ?_
    rw [hid T]
    ring

/-- Cochrane (2023), §19.1, p. 434 (the money transversality condition
`E_tΛ_{t+T}M_{t+T}/P_{t+T} → 0`): with `i ≥ 0` and nonnegative money and value of a dollar, the
book's form of the condition implies the form `E_t[Λ_{t+T}M_{t+T−1}/P_{t+T}] → 0` used in
`eq192_iff_eq193`, because `0 ≤ E_t[Λ_{k+1}M_k/P_{k+1}] ≤ E_t[Λ_kM_k/P_k]`. -/
theorem tail_tendsto_zero_of_book_tvc (hPO : 𝔼.PullOut) {Λ P N i : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hi0 : ∀ t ω, 0 ≤ i t ω) (hpos : ∀ t ω, 0 ≤ N (t + 1) ω * (Λ t ω / P t ω)) {t : ℕ}
    {ω : Ω}
    (hbook : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T + 1) / P (t + T)) ω) atTop
      (𝓝 0)) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0) := by
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  refine squeeze_zero (fun T => ?_) (fun T => ?_) hbook
  · rw [← add_assoc, E_next_value 𝔼 hPO hBP hN (Nat.le_add_right t T)]
    have h0 : (0 : Ω → ℝ) ≤ N (t + T + 1) * (Λ (t + T) / P (t + T) / (1 + i (t + T))) :=
      fun ω' => by
        simp only [Pi.zero_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.one_apply]
        have h1 : 0 < 1 + i (t + T) ω' := by linarith [hi0 (t + T) ω']
        have h2 := hpos (t + T) ω'
        have e : N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω' / (1 + i (t + T) ω')) =
            N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω') / (1 + i (t + T) ω') := by ring
        rw [e]
        exact div_nonneg h2 h1.le
    have := 𝔼.mono t h0 ω
    rwa [map_zero] at this
  · rw [← add_assoc, E_next_value 𝔼 hPO hBP hN (Nat.le_add_right t T)]
    have hle : N (t + T + 1) * (Λ (t + T) / P (t + T) / (1 + i (t + T))) ≤
        Λ (t + T) * N (t + T + 1) / P (t + T) := fun ω' => by
      simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.one_apply]
      have h1 : 1 ≤ 1 + i (t + T) ω' := by linarith [hi0 (t + T) ω']
      have h2 := hpos (t + T) ω'
      have e1 : N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω' / (1 + i (t + T) ω')) =
          N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω') / (1 + i (t + T) ω') := by ring
      have e2 : Λ (t + T) ω' * N (t + T + 1) ω' / P (t + T) ω' =
          N (t + T + 1) ω' * (Λ (t + T) ω' / P (t + T) ω') := by ring
      rw [e1, e2]
      exact div_le_self h2 h1
    exact 𝔼.mono t hle ω

/-! ### The valuation equation from the flow constraint -/

/-- Cochrane (2023), p. 439 (government flow constraint, and §3.4): with `Bm t = B_{t−1}` and
`N t = M_{t−1}`, `B_{t−1} + M_{t−1} = P_ts_t + Q_tB_t + M_t` at every date. (For the household of
§19.3, `s` is replaced by `s + c − y`.) -/
def Flow (Bm N P s Q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Bm t + N t = P t * s t + Q t * Bm (t + 1) + N (t + 1)

/-- Cochrane (2023), (19.2), p. 434, the one-period step: the flow constraint with
`Q_t = 1/(1 + i_t)` and the bond-pricing condition give
`Λ_tB_{t−1}/P_t = Λ_t(ΔM_t/P_t + s_t) + E_t[Λ_{t+1}B_t/P_{t+1}]`. -/
theorem flow_value_recursion (hPO : 𝔼.PullOut) {Λ P N i Bm Q s : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : Flow Bm N P s Q) (t : ℕ) :
    Λ t * Bm t / P t = Λ t * ((N (t + 1) - N t) / P t + s t) +
      𝔼.E t (Λ (t + 1) * Bm (t + 1) / P (t + 1)) := by
  have hE : 𝔼.E t (Λ (t + 1) * Bm (t + 1) / P (t + 1)) =
      Bm (t + 1) * (Λ t / P t / (1 + i t)) := by
    have h1 : Λ (t + 1) * Bm (t + 1) / P (t + 1) = Bm (t + 1) * (Λ (t + 1) / P (t + 1)) := by
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO t _ _ (hB t), hBP t]
  rw [hE]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  have hf := congrFun (hflow t) ω
  simp only [Pi.add_apply, Pi.mul_apply] at hf
  rw [hQ t ω] at hf
  have h1 := hi t ω
  have h2 := hP t ω
  have hb : Bm t ω = P t ω * s t ω + 1 / (1 + i t ω) * Bm (t + 1) ω + N (t + 1) ω - N t ω := by
    linarith
  rw [hb]
  field_simp
  ring

/-- Cochrane (2023), (19.2), p. 434 and §3.4: given the flow constraint, the bond-pricing
condition and adapted debt, the valuation equation (19.2) holds at `(t, ω)` (as the limit of
the partial sums, multiplied by `Λ_t`) if and only if the bond transversality condition
`E_t[Λ_{t+T}B_{t+T−1}/P_{t+T}] → 0` holds there. -/
theorem flow_pv_iff_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q s : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : Flow Bm N P s Q) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => partial192 𝔼 Λ P N s t T ω) atTop (𝓝 (Λ t ω * Bm t ω / P t ω)) ↔
      Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) := by
  set x : ℕ → Ω → ℝ := fun k => Λ k * Bm k / P k with hx
  set d : ℕ → Ω → ℝ := fun k => Λ k * ((N (k + 1) - N k) / P k + s k) with hd
  have hrec : ∀ k, x k = d k + 𝔼.E k (x (k + 1)) := fun k =>
    flow_value_recursion 𝔼 hPO hBP hB hQ hi hP hflow k
  have hxa : 𝔼.Adapted x := fun k => by
    have h1 : x k = Bm k * (Λ k / P k) := by
      funext ω'
      simp only [hx, Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO k _ _ (hBa k), hφ k]
  have hda : 𝔼.Adapted d := fun k => by
    have h1 : d k = x k - 𝔼.E k (x (k + 1)) := by rw [hrec k]; abel
    rw [h1, map_sub, hxa k, 𝔼.E_E_self]
  have hsol : Solves 𝔼 1 d x := fun k => by rw [one_smul, add_comm]; exact hrec k
  have hpart : ∀ T, partial192 𝔼 Λ P N s t T ω = x t ω - 𝔼.E t (x (t + T)) ω := by
    intro T
    have h := congrFun (iterate_A15 𝔼 hda hsol t T) ω
    simp only [one_pow, one_smul, Pi.add_apply, Finset.sum_apply] at h
    simp only [partial192, Finset.sum_apply]
    linarith
  have hxt : x t ω = Λ t ω * Bm t ω / P t ω := rfl
  constructor
  · intro h
    have h2 := (tendsto_const_nhds (x := x t ω)).sub h
    rw [hxt, sub_self] at h2
    refine h2.congr fun T => ?_
    rw [hpart T, hxt]
    simp only [hx]
    ring
  · intro h
    have h2 := (tendsto_const_nhds (x := x t ω)).sub h
    rw [sub_zero, hxt] at h2
    exact h2.congr fun T => (hpart T).symm

/-- Cochrane (2023), (19.3), p. 434: from the flow constraint, the bond-pricing condition, the
bond transversality condition and the money transversality condition, the valuation equation
holds in the form (19.3), `(B_{t−1} + M_{t−1})/P_t = E_t∑(Λ_{t+j}/Λ_t)(iM/((1+i)P) + s)`. -/
theorem flow_eq193_of_tvc (hPO : 𝔼.PullOut) {Λ P N i Bm Q s : ℕ → Ω → ℝ}
    (hBP : BondPricing 𝔼 Λ P i) (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t)
    (hBa : 𝔼.Adapted Bm) (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1))
    (hNa : 𝔼.Adapted N) (hN : ∀ t, 𝔼.E t (N (t + 1)) = N (t + 1))
    (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω)) (hi : ∀ t ω, 1 + i t ω ≠ 0)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : Flow Bm N P s Q) {t : ℕ} {ω : Ω}
    (hbond : Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0))
    (hmoney : Tendsto (fun T => 𝔼.E t (Λ (t + T) * N (t + T) / P (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => partial193 𝔼 Λ P N i s t T ω) atTop
      (𝓝 (Λ t ω * (Bm t ω + N t ω) / P t ω)) :=
  (eq192_iff_eq193 𝔼 hPO s Bm hBP hφ hNa hN hi hmoney).mp
    ((flow_pv_iff_tvc 𝔼 hPO hBP hφ hBa hB hQ hi hP hflow t ω).mpr hbond)

/-! ### §19.1: monetary and fiscal regimes (survey NI-7) -/

/-- Cochrane (2023), (19.1) and (19.3), p. 434: under money demand `MV = Py` the seigniorage flow
`(i/(1 + i))M/P` of (19.3) equals `(i/(1 + i))y/V`; it does not involve the price level, so the
right-hand side of (19.3) is a real present value `W_t` set by policy. -/
theorem seigniorage_indep_price {M V P y i : ℝ} (hP : P ≠ 0) (hV : V ≠ 0)
    (hq : M * V = P * y) : i / (1 + i) * M / P = i / (1 + i) * y / V := by
  rw [div_eq_div_iff hP hV, mul_assoc, hq]
  ring

/-- Cochrane (2023), §19.1, p. 435: the government debt valuation equation in the form
`B_{t−1} + M_{t−1} = P_tW_t`, with `D_t = B_{t−1} + M_{t−1}` the nominal liabilities and `W_t` the
real present value of surpluses and seigniorage on the right of (19.3). -/
def Valuation (D W P : ℕ → Ω → ℝ) : Prop := ∀ t, D t = P t * W t

/-- Cochrane (2023), §19.1, p. 435: a process is strictly positive at every date and state. -/
def Pos (x : ℕ → Ω → ℝ) : Prop := ∀ t ω, 0 < x t ω

/-- Cochrane (2023), §19.1, p. 435, the active-money, passive-fiscal regime: the money supply
`Ms` is set and the price level clears the money market (19.1); surpluses then adjust so that
the valuation equation holds for that price level (`W = D/P`). -/
def MonetaryEqm (Ms V y P : ℕ → Ω → ℝ) : Prop := Pos P ∧ QuantityEq Ms V P y

/-- Cochrane (2023), §19.1, p. 435, the active-fiscal, passive-money regime: nominal liabilities
`D` and the present value `W` are set and the price level satisfies the valuation equation;
money is then supplied passively (`M = Py/V`). -/
def FiscalEqm (D W P : ℕ → Ω → ℝ) : Prop := Pos P ∧ Valuation D W P

/-- Cochrane (2023), §19.1, p. 435 ("the fiscal and monetary regimes are observationally
equivalent", survey NI-7): if `(P, M, D, W)` satisfies both equilibrium conditions (19.1) and
the valuation equation, then `P` is the unique equilibrium of the active-money regime with money
supply `M` (whose passive surpluses reproduce `W = D/P`), and the unique equilibrium of the
active-fiscal regime with `(D, W)` (whose passive money reproduces `M = Py/V`). -/
theorem ni7 {P M D W V y : ℕ → Ω → ℝ} (hP : Pos P) (hV : Pos V) (hy : Pos y) (hW : Pos W)
    (hq : QuantityEq M V P y) (hv : Valuation D W P) :
    (∀ P', MonetaryEqm M V y P' ↔ P' = P) ∧ (fun t => D t / P t) = W ∧
      (∀ P', FiscalEqm D W P' ↔ P' = P) ∧ (fun t => P t * y t / V t) = M := by
  refine ⟨fun P' => ⟨fun h => ?_, fun h => h ▸ ⟨hP, hq⟩⟩, ?_,
    fun P' => ⟨fun h => ?_, fun h => h ▸ ⟨hP, hv⟩⟩, ?_⟩
  · funext t ω
    have h1 := congrFun (h.2 t) ω
    have h2 := congrFun (hq t) ω
    simp only [Pi.mul_apply] at h1 h2
    have := hy t ω
    exact mul_right_cancel₀ this.ne' (by linarith)
  · funext t ω
    have h1 := congrFun (hv t) ω
    simp only [Pi.mul_apply] at h1
    simp only [Pi.div_apply]
    rw [h1, mul_div_cancel_left₀ _ (hP t ω).ne']
  · funext t ω
    have h1 := congrFun (h.2 t) ω
    have h2 := congrFun (hv t) ω
    simp only [Pi.mul_apply] at h1 h2
    have := hW t ω
    exact mul_right_cancel₀ this.ne' (by linarith)
  · funext t ω
    have h1 := congrFun (hq t) ω
    simp only [Pi.mul_apply] at h1
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [← h1, mul_div_cancel_right₀ _ (hV t ω).ne']

/-- Cochrane (2023), §19.1, p. 435 ("if monetary and fiscal policy are both passive, then the
price level is undetermined"): with money supplied passively (`M = Py/V`) and surpluses adjusting
passively (`W = D/P`), every positive price-level process is an equilibrium. -/
theorem double_passive {D V y : ℕ → Ω → ℝ} (hV : Pos V) (P' : ℕ → Ω → ℝ) (hP' : Pos P') :
    QuantityEq (fun t => P' t * y t / V t) V P' y ∧ Valuation D (fun t => D t / P' t) P' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [div_mul_cancel₀ _ (hV t ω).ne']
  · funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [mul_div_cancel₀ _ (hP' t ω).ne']

/-- Cochrane (2023), §19.1, p. 435 (coordination): if money and fiscal policy are both active
(`M` and `(D, W)` both set), an equilibrium exists if and only if the two settings are
coordinated, `M_tV_tW_t = D_ty_t` at every date and state; otherwise the equations contradict. -/
theorem double_active_iff {Ms D W V y : ℕ → Ω → ℝ} (hD : Pos D) (hW : Pos W) :
    (∃ P, MonetaryEqm Ms V y P ∧ Valuation D W P) ↔ ∀ t ω, Ms t ω * V t ω * W t ω =
      D t ω * y t ω := by
  constructor
  · rintro ⟨P, ⟨-, hq⟩, hv⟩ t ω
    have h1 := congrFun (hq t) ω
    have h2 := congrFun (hv t) ω
    simp only [Pi.mul_apply] at h1 h2
    rw [h1, h2]
    ring
  · intro h
    refine ⟨fun t ω => D t ω / W t ω, ⟨fun t ω => div_pos (hD t ω) (hW t ω), fun t => ?_⟩,
      fun t => ?_⟩
    · funext ω
      simp only [Pi.mul_apply]
      have := hW t ω
      field_simp
      linarith [h t ω]
    · funext ω
      simp only [Pi.mul_apply]
      rw [div_mul_cancel₀ _ (hW t ω).ne']

/-- Cochrane (2023), §19.1, p. 435 ("the government must adjust surpluses ex-post so that the
government debt valuation equation holds"): the passive surplus rule
`s_t = W_t − βE_tW_{t+1}` that delivers a target real value `W` of the debt. -/
def passiveSurplus (β : ℝ) (W : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := W t - β • 𝔼.E t (W (t + 1))

/-- Cochrane (2023), §19.1, p. 435: a passive fiscal policy exists for every target. For any
bounded adapted `W` (e.g. `W = D/P` for whatever price level occurs) and `|β| < 1`, the surplus
rule `passiveSurplus` is adapted and its present value `E_t∑βʲs_{t+j}` (limit of the partial
sums) equals `W_t`, so the valuation equation holds for any price level. -/
theorem passive_surplus_realises {β : ℝ} (hβ : |β| < 1) {W : ℕ → Ω → ℝ} (hWa : 𝔼.Adapted W)
    (hWb : BoundedProc W) :
    𝔼.Adapted (passiveSurplus 𝔼 β W) ∧ ∀ t ω,
      Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (passiveSurplus 𝔼 β W (t + j)) ω)
        atTop (𝓝 (W t ω)) := by
  have hsa : 𝔼.Adapted (passiveSurplus 𝔼 β W) := fun t => by
    simp only [passiveSurplus]
    rw [map_sub, map_smul, 𝔼.E_E_self, hWa t]
  have hsol : Solves 𝔼 β (passiveSurplus 𝔼 β W) W := fun t => by
    simp only [passiveSurplus]
    abel
  exact ⟨hsa, fun t ω => tendsto_partial_A16 𝔼 hβ hsa hsol hWb t ω⟩

/-! ### Chapter 11: open-market operations, the spread, elastic currency -/

/-- Cochrane (2023), eq. (11.1), p. 315: the date-`t` partial sum of the valuation equation with
interest-paying money, `∑_{j<T} βʲE_t[s + (i − i^m)/((1 + i)(1 + i^m)) · M/P]`. -/
noncomputable def partial111 (β : ℝ) (s i im M P : ℕ → Ω → ℝ) (t T : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range T, β ^ j • 𝔼.E t (s (t + j) +
    (i (t + j) - im (t + j)) / ((1 + i (t + j)) * (1 + im (t + j))) * M (t + j) / P (t + j))

/-- Cochrane (2023), (11.1), p. 315, and V1 (pp. 316–317): with `1 + i > 0`, `1 + i^m > 0` and
positive real money, the seigniorage term `(i − i^m)/((1 + i)(1 + i^m)) · M/P` vanishes if and
only if money pays the market rate, `i = i^m`. -/
theorem spread_term_eq_zero_iff {i im M P : ℝ} (hi : 0 < 1 + i) (him : 0 < 1 + im)
    (hm : M / P ≠ 0) : (i - im) / ((1 + i) * (1 + im)) * M / P = 0 ↔ i = im := by
  rw [mul_div_assoc]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases div_eq_zero_iff.mp h1 with h2 | h2
      · linarith
      · exact absurd h2 (mul_pos hi him).ne'
    · exact absurd h1 hm
  · intro h
    rw [h, sub_self, zero_div, zero_mul]

/-- Cochrane (2023), (11.1), p. 315, V1: when money pays the market rate at every date
(`i = i^m`), the right-hand side of (11.1) is `∑ βʲE_ts_{t+j}`, whatever the money and price
paths. -/
theorem partial111_of_no_spread {β : ℝ} {s i im : ℕ → Ω → ℝ} (h : ∀ t, i t = im t)
    (M P : ℕ → Ω → ℝ) (t T : ℕ) :
    partial111 𝔼 β s i im M P t T = ∑ j ∈ Finset.range T, β ^ j • 𝔼.E t (s (t + j)) := by
  unfold partial111
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext ω
  simp [h]

/-- Cochrane (2023), §11.2, pp. 316–317, V1 ("an open-market operation swapping `M` for `B` has
no effect"): with `i = i^m` at every date, (11.1) depends on bonds and money only through
`B + M`. If `B_{t−1} + M_{t−1} = B'_{t−1} + M'_{t−1}` then, for any money paths, a price level
`P_t` satisfies (11.1) for `(B, M)` if and only if it does for `(B', M')`. -/
theorem omo_irrelevant {β : ℝ} {s i im : ℕ → Ω → ℝ} (h : ∀ t, i t = im t)
    (M M' P P' : ℕ → Ω → ℝ) {b m b' m' Pt : ℝ} (hsum : b + m = b' + m') (t : ℕ) (ω : Ω) :
    Tendsto (fun T => partial111 𝔼 β s i im M P t T ω) atTop (𝓝 ((b + m) / Pt)) ↔
      Tendsto (fun T => partial111 𝔼 β s i im M' P' t T ω) atTop (𝓝 ((b' + m') / Pt)) := by
  simp only [partial111_of_no_spread 𝔼 h, hsum]

/-- Cochrane (2023), §11.2, p. 317, V3 ("we can satisfy the money demand curve by letting the
interest-rate spread `i − i^m` vary … the price of money can be passive rather than the
quantity"): if velocity `V(i − i^m)` is strictly increasing in the spread and takes every
positive value, then for any money `M > 0` and nominal income `Py > 0` exactly one spread clears
the money market `M V(i − i^m) = Py`. -/
theorem spread_existsUnique {V : ℝ → ℝ} (hV : StrictMono V) (hsurj : ∀ v, 0 < v → ∃ x, V x = v)
    {M Py : ℝ} (hM : 0 < M) (hPy : 0 < Py) : ∃! x, M * V x = Py := by
  obtain ⟨x, hx⟩ := hsurj (Py / M) (div_pos hPy hM)
  refine ⟨x, show M * V x = Py by rw [hx]; field_simp, fun x' hx' => hV.injective ?_⟩
  rw [hx]
  field_simp
  linarith

/-- Cochrane (2023), §11.2, p. 318, V4 ("both theories describe an identical fall in money `M`,
rise in debt `B`, and a rise in surpluses `s`"): compare two equilibria `(P, M, D, W)` and
`(P', M', D, W')` with the same nominal liabilities `D = B + M` (a pure change of composition)
under rigid `M_tV = P_ty`. Money falls iff the price level falls iff the real value `W` of
surpluses rises; and bonds `B = D − M` rise iff money falls. The monetarist reading (less money,
passive fiscal tightening) and the fiscal reading (fiscal tightening, passive fall in money)
describe the same event. -/
theorem omo_equivalence {P M W P' M' W' D V y : ℕ → Ω → ℝ} (hP : Pos P) (hP' : Pos P')
    (hD : Pos D) (hV : Pos V) (hy : Pos y) (hq : QuantityEq M V P y)
    (hq' : QuantityEq M' V P' y) (hv : Valuation D W P) (hv' : Valuation D W' P') (t : ℕ)
    (ω : Ω) :
    (M' t ω < M t ω ↔ P' t ω < P t ω) ∧ (P' t ω < P t ω ↔ W t ω < W' t ω) ∧
      (D t ω - M t ω < D t ω - M' t ω ↔ M' t ω < M t ω) := by
  have h1 := congrFun (hq t) ω
  have h1' := congrFun (hq' t) ω
  have h2 := congrFun (hv t) ω
  have h2' := congrFun (hv' t) ω
  simp only [Pi.mul_apply] at h1 h1' h2 h2'
  have hVp := hV t ω
  have hyp := hy t ω
  have hPp := hP t ω
  have hPp' := hP' t ω
  have hDp := hD t ω
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => by linarith,
    fun h => by linarith⟩⟩
  · by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hyp.le]
  · by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hVp.le]
  · by_contra hc
    push Not at hc
    have hWp : 0 < W t ω := by
      by_contra h0
      push Not at h0
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hPp.le h0]
    nlinarith [mul_le_mul_of_nonneg_left hc hPp'.le, mul_lt_mul_of_pos_right h hWp]
  · by_contra hc
    push Not at hc
    have hWp : 0 < W t ω := by
      by_contra h0
      push Not at h0
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hPp.le h0]
    nlinarith [mul_le_mul_of_nonneg_left hc hPp.le, mul_lt_mul_of_pos_left h hPp']

/-- Cochrane (2023), §11.3, p. 318, V5 ("elastic currency": "any `P` is consistent with this
policy"): if the central bank issues `M_t = P_ty_t/V_t` for whatever price level occurs, the
money market clears for every positive price-level process; money demand then places no
restriction on `P`, which the valuation equation alone determines (`ni7`). -/
theorem elastic_currency {V y : ℕ → Ω → ℝ} (hV : Pos V) (P : ℕ → Ω → ℝ) :
    QuantityEq (fun t => P t * y t / V t) V P y := fun t => by
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply]
  rw [div_mul_cancel₀ _ (hV t ω).ne']

/-! ### §14.1, p. 342 (V11): helicopter magnitudes -/

/-- Cochrane (2023), §14.1, p. 342, the fiscal-theory answer: with the real value of surpluses
`W` unchanged, the valuation equation `D = PW` makes the price level proportional to nominal
liabilities, `P'/P = D'/D`. -/
theorem ftpl_price_ratio {D D' P P' W : ℝ} (hD : 0 < D) (hW : 0 < W) (hv : D = P * W)
    (hv' : D' = P' * W) : P' / P = D' / D := by
  have hP : P ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hv
    exact hD.ne' hv
  rw [hv, hv', mul_div_mul_right _ _ hW.ne']

/-- Cochrane (2023), §14.1, p. 342, the monetarist answer: with velocity and output unchanged,
`MV = Py` makes the price level proportional to money, `P'/P = M'/M`. -/
theorem quantity_price_ratio {M M' V y P P' : ℝ} (hM : 0 < M) (hV : 0 < V) (hy : 0 < y)
    (hq : M * V = P * y) (hq' : M' * V = P' * y) : P' / P = M' / M := by
  have hP : P ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hq
    exact (mul_pos hM hV).ne' hq
  rw [div_eq_div_iff hP hM.ne']
  have : P' * y * M = M' * V * M := by rw [hq']
  have h2 : M' * (P * y) = M' * (M * V) := by rw [hq]
  nlinarith

/-- Cochrane (2023), §14.1, p. 342 ("Overall treasury debt just got diluted 1%"): $100,000 of
bonds and $1,000 of cash per household plus a $1,000 drop raise nominal liabilities, hence the
price level, by the factor `1 + 1/101`. -/
theorem helicopter_fiscal : ((100000 + 1000 + 1000 : ℝ) / (100000 + 1000)) = 1 + 1 / 101 := by
  norm_num

/-- Cochrane (2023), §14.1, p. 342 ("a fiscal theory answer is, 1%"): the exact rise `1/101` is
within one hundredth of a percentage point of 1%. -/
theorem helicopter_fiscal_approx : |(1 : ℝ) / 101 - 1 / 100| < 1 / 10000 := by
  rw [abs_lt]
  constructor <;> norm_num

/-- Cochrane (2023), §14.1, p. 342 ("The monetarist answer is 100%. The money supply doubles, so
the price level must double"): cash goes from $1,000 to $2,000. -/
theorem helicopter_monetarist : ((1000 + 1000 : ℝ) / 1000) = 2 := by norm_num

/-- Cochrane (2023), §14.1, p. 342: after the doubling, $2,000 of cash is 1% of the now $200,000
nominal income per household. -/
theorem helicopter_cash_share : (2000 : ℝ) / (2 * 100000) = 1 / 100 := by norm_num

/-- Cochrane (2023), §14.1, p. 342 ("this doubling of the price level wipes out half of the real
value of $100,000 of treasury savings … the present value of taxes have declined $50,000"). -/
theorem helicopter_bond_loss : (100000 : ℝ) - 100000 / 2 = 50000 := by norm_num

end Cochrane.Monetarism.Regimes
