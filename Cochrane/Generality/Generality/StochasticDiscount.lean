/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.LongTermDebt

/-!
# Risk and discounting

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.3, pp. 55–57, eqs.
(3.5)–(3.8) and the unnumbered displays.

Discounting uses one-period factors `m t = Λ_{t+1}/Λ_t` (known at `t + 1`), and the
multi-period factor `sdf m t n = Λ_{t+n}/Λ_t` (`sdf_eq_ratio`); the machinery
(`pv`, `TVC`, `flow_tvc_iff_pv`) is in `LongTermDebt`. `D t` is `B_{t−1}`, the nominal
one-period debt outstanding at the start of `t`, and `x_t = B_{t−1}/P_t`.

## Main results

* `sdf_eq_ratio`, `sdf_marginal_utility`: `∏_{k<n} m_{t+k} = Λ_{t+n}/Λ_t`, and with
  `Λ_t = βᵗu'(c_t)` the factor `βⁿu'(c_{t+n})/u'(c_t)`.
* `flowOne_iff_rec` (p. 55): with `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]`, the flow
  `B_{t−1}/P_t = s_t + Q_tB_t/P_t` is `x_t = s_t + E_t[m_tx_{t+1}]`; `tvc_lambda_iff`: the TVC
  in the book's form `lim E_t[Λ_TB_{T−1}/(Λ_tP_T)] = 0`.
* `valuation_sdf_iff` (3.5): flow + TVC at every date ⟺ `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)
  s_{t+j}]` at every date (signed surpluses, absolutely summable); `pv_lambda` the printed
  form; `price_eq_of_valuation`, `price_unique`: the valuation equation determines `P_t`.
* `inv_return_sdf`, `inv_return_expost` (p. 56): `1 = E_t[R⁻¹_{t+1}R_{t+1}]` under every
  `ExpectationSystem` ("using any set of probabilities").
* `flow_expost` (p. 56): `B_{t−1}/P_t = s_t + R⁻¹_{t+1}B_t/P_{t+1}` with
  `R_{t+1} = (1/Q_t)P_t/P_{t+1}`, `expostReturn_rate`: `= (1+i_t)P_t/P_{t+1}`.
* `expost_iterate` (3.6), finite horizon, with the terminal product up to `T` (survey E12);
  `expost_tendsto_iff`, `expost_pv`: the infinite sum converges to `x_t` iff the terminal
  term vanishes; `expost_E_tendsto_iff`, `expost_pv_E`, `expost_flow_E`: the same after
  taking `E_t` under any expectation system.
* `pf_expost_inv_eq_sdf`: under perfect foresight the ex-post discount factor is `m`.
* `expost_may_diverge` (p. 56): an economy in which (3.5), the flow and the TVC hold at every
  date while along a realised path the ex-post present value (3.6) diverges to `−∞` and its
  terminal term to `+∞`.
* `finiteTree_expost_pv`: on every finite event tree, (3.5) with its flow and TVC force (3.6)
  to converge absolutely in every state (all states have positive probability), via
  `finiteTree_info_stable`, `finiteTree_eventually_known`; the explosion needs a
  zero-probability path.
* (3.7)–(3.8): `portfolioReturn`, `flowLT_iff_3_8`, and `expostLT_pv` (p. 57).
-/

namespace Cochrane.Generality.StochasticDiscount

open Filter Topology LongTermDebt

variable {Ω : Type*}

/-! ### The discount factor as a ratio of marginal utilities -/

/-- Cochrane (2023), §3.3, p. 55: if the one-period factors are `m_s = Λ_{s+1}/Λ_s` with
`Λ ≠ 0`, the multi-period factor is `Λ_{t+n}/Λ_t`. -/
theorem sdf_eq_ratio {Λ m : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0)
    (hm : ∀ s, m s = fun ξ => Λ (s + 1) ξ / Λ s ξ) (t n : ℕ) :
    sdf m t n = fun ξ => Λ (t + n) ξ / Λ t ξ := by
  induction n with
  | zero =>
    funext ξ
    simp [hΛ t ξ]
  | succ n ih =>
    rw [sdf_succ, ih, hm]
    funext ξ
    simp only [Pi.mul_apply]
    have := hΛ (t + n) ξ
    rw [show t + (n + 1) = t + n + 1 by omega]
    field_simp

/-- Cochrane (2023), §3.3, p. 55: with `Λ_t = βᵗu'(c_t)`, `β > 0`, positive marginal utility
`u'(c_t)`, the one-period factor is `β u'(c_{t+1})/u'(c_t)` and the multi-period factor is
`Λ_{t+n}/Λ_t = βⁿ u'(c_{t+n})/u'(c_t)`. -/
theorem sdf_marginal_utility {β : ℝ} (hβ : 0 < β) {up : ℕ → Ω → ℝ} (hup : ∀ s ξ, 0 < up s ξ)
    (t n : ℕ) :
    sdf (fun s ξ => β * up (s + 1) ξ / up s ξ) t n =
      fun ξ => β ^ n * up (t + n) ξ / up t ξ := by
  have h := sdf_eq_ratio (Λ := fun s ξ => β ^ s * up s ξ) (m := fun s ξ => β * up (s + 1) ξ /
    up s ξ) (fun s ξ => (mul_pos (pow_pos hβ s) (hup s ξ)).ne') (fun s => by
      funext ξ
      have := (hup s ξ).ne'
      have := hβ.ne'
      field_simp
      ring) t n
  rw [h]
  funext ξ
  have := (hup t ξ).ne'
  have := hβ.ne'
  rw [pow_add]
  field_simp

/-! ### One-period debt: the flow, the transversality condition and (3.5) -/

variable (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §3.3, p. 55: the one-period nominal bond price
`Q_t = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1})]`. -/
noncomputable def bondPrice (m P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (m t * fun ξ => P t ξ / P (t + 1) ξ)

/-- Cochrane (2023), §3.3, p. 55 (the flow condition (2.5) with a bond price `Q`):
`B_{t−1}/P_t = s_t + Q_tB_t/P_t`. -/
def FlowOne (Q P s D : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ξ, D t ξ / P t ξ = s t ξ + Q t ξ * D (t + 1) ξ / P t ξ

/-- Cochrane (2023), §3.3, p. 55: the real value `x_t = B_{t−1}/P_t` of the debt. -/
noncomputable def realDebt (D P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ξ => D t ξ / P t ξ

/-- Cochrane (2023), §3.3, p. 55: with the bond price `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]`,
`P_t` known at `t`, `B_t` known at `t` and `P ≠ 0`, the flow condition is
`x_t = s_t + E_t[(Λ_{t+1}/Λ_t)x_{t+1}]`. -/
theorem flowOne_iff_rec (hP : 𝔼.PullOut) {m P s D : ℕ → Ω → ℝ} {t : ℕ}
    (hPa : 𝔼.E t (P t) = P t) (hD1 : 𝔼.E t (D (t + 1)) = D (t + 1)) (hP0 : ∀ s ξ, P s ξ ≠ 0) :
    FlowOne (bondPrice 𝔼 m P) P s D t ↔
      realDebt D P t = s t + 𝔼.E t (m t * realDebt D P (t + 1)) := by
  have hQ : ∀ ξ, bondPrice 𝔼 m P t ξ * D (t + 1) ξ / P t ξ =
      𝔼.E t (m t * realDebt D P (t + 1)) ξ := by
    intro ξ
    have e1 : (m t * fun ξ' => P t ξ' / P (t + 1) ξ') =
        P t * (m t * fun ξ' => (P (t + 1) ξ')⁻¹) := by
      funext ξ'
      simp only [Pi.mul_apply, div_eq_mul_inv]
      ring
    have e2 : (m t * realDebt D P (t + 1)) = D (t + 1) * (m t * fun ξ' => (P (t + 1) ξ')⁻¹) := by
      funext ξ'
      simp only [Pi.mul_apply, realDebt, div_eq_mul_inv]
      ring
    rw [bondPrice, e1, hP t _ _ hPa, e2, hP t _ _ hD1]
    simp only [Pi.mul_apply]
    have := hP0 t ξ
    field_simp
  constructor
  · intro h
    funext ξ
    rw [Pi.add_apply, ← hQ ξ]
    exact h ξ
  · intro h ξ
    have := congrFun h ξ
    rw [Pi.add_apply, ← hQ ξ] at this
    exact this

/-- Cochrane (2023), §3.3, p. 55: the transversality condition in the book's form,
`lim_T E_t[Λ_T B_{T−1}/(Λ_t P_T)] = 0`, is `TVC` for the factors `m_s = Λ_{s+1}/Λ_s`. -/
theorem tvc_lambda_iff {Λ m D P : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0)
    (hm : ∀ s, m s = fun ξ => Λ (s + 1) ξ / Λ s ξ) (t : ℕ) :
    TVC 𝔼 m (realDebt D P) t ↔ ∀ ξ, Tendsto
      (fun N => 𝔼.E t (fun ξ' => Λ (t + N) ξ' * D (t + N) ξ' / (Λ t ξ' * P (t + N) ξ')) ξ)
      atTop (𝓝 0) := by
  refine forall_congr' fun ξ => ?_
  have h : ∀ N, (sdf m t N * realDebt D P (t + N)) =
      fun ξ' => Λ (t + N) ξ' * D (t + N) ξ' / (Λ t ξ' * P (t + N) ξ') := fun N => by
    rw [sdf_eq_ratio hΛ hm]
    funext ξ'
    simp only [Pi.mul_apply, realDebt]
    rw [div_mul_div_comm]
  simp_rw [h]

/-- Cochrane (2023), eq. (3.5), p. 55, printed form: the present value is
`∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]`. -/
theorem pv_lambda {Λ m s : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0)
    (hm : ∀ s, m s = fun ξ => Λ (s + 1) ξ / Λ s ξ) (t : ℕ) :
    pv 𝔼 m s t = fun ξ => ∑' j, 𝔼.E t (fun ξ' => Λ (t + j) ξ' / Λ t ξ' * s (t + j) ξ') ξ := by
  funext ξ
  simp only [pv, sdf_eq_ratio hΛ hm]
  rfl

/-- Cochrane (2023), eq. (3.5), p. 55: with the bond price `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]`,
nonnegative factors known one period ahead, adapted surpluses with absolutely summable present
values, an adapted price level `P ≠ 0`, debt `B_t` chosen at `t`, a real debt value known at
its date, and `E_t` with pull-out and conditional monotone convergence: the flow condition at
every date plus the transversality condition at every date hold iff the stochastically
discounted valuation formula `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` holds at every
date (signed surpluses). -/
theorem valuation_sdf_iff (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m P s D : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ)
    (hsa : 𝔼.Adapted s) (hs : SurplusSummable 𝔼 m s) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hD1 : ∀ t, 𝔼.E t (D (t + 1)) = D (t + 1))
    (hx : 𝔼.Adapted (realDebt D P)) :
    ((∀ t, FlowOne (bondPrice 𝔼 m P) P s D t) ∧ ∀ t, TVC 𝔼 m (realDebt D P) t) ↔
      ∀ t, realDebt D P t = pv 𝔼 m s t := by
  rw [← flow_tvc_iff_pv 𝔼 hMC hP hm hm0 hsa hs hx]
  have h : (∀ t, FlowOne (bondPrice 𝔼 m P) P s D t) ↔ FlowRec 𝔼 m s (realDebt D P) :=
    forall_congr' fun t => flowOne_iff_rec 𝔼 hP (hPa t) (hD1 t) hP0
  rw [h]

/-- Cochrane (2023), eq. (3.5), p. 55 (the price level is determined): if the valuation
formula holds and the present value is nonzero, `P_t = B_{t−1}/∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]`. -/
theorem price_eq_of_valuation {m s D P : ℕ → Ω → ℝ} {t : ℕ} {ξ : Ω} (hD : D t ξ ≠ 0)
    (hP0 : P t ξ ≠ 0) (hval : realDebt D P t ξ = pv 𝔼 m s t ξ) :
    P t ξ = D t ξ / pv 𝔼 m s t ξ := by
  rw [← hval, realDebt]
  field_simp

/-- Cochrane (2023), eq. (3.5), p. 55: given the debt `B_{t−1} ≠ 0`, the surpluses and the
discount factors, two nonzero price levels satisfying the valuation formula coincide. -/
theorem price_unique {m s D P P' : ℕ → Ω → ℝ} {t : ℕ} {ξ : Ω} (hD : D t ξ ≠ 0)
    (hP0 : P t ξ ≠ 0) (hP0' : P' t ξ ≠ 0) (hval : realDebt D P t ξ = pv 𝔼 m s t ξ)
    (hval' : realDebt D P' t ξ = pv 𝔼 m s t ξ) : P t ξ = P' t ξ := by
  rw [price_eq_of_valuation 𝔼 hD hP0 hval, price_eq_of_valuation 𝔼 hD hP0' hval']

/-! ### Ex-post returns as discount factors -/

/-- Cochrane (2023), §3.3, p. 56: `1 = R⁻¹_{t+1}R_{t+1}` state by state (the inverse return is
an ex-post discount factor). -/
theorem inv_return_expost {R : Ω → ℝ} (hR : ∀ ξ, R ξ ≠ 0) : (fun ξ => (R ξ)⁻¹ * R ξ) = 1 := by
  funext ξ
  simp [hR ξ]

/-- Cochrane (2023), §3.3, p. 56: `1 = E_t(R⁻¹_{t+1}R_{t+1})` for every `ExpectationSystem`
("using any set of probabilities"): the inverse return is an ex-ante discount factor. -/
theorem inv_return_sdf (t : ℕ) {R : Ω → ℝ} (hR : ∀ ξ, R ξ ≠ 0) :
    𝔼.E t (fun ξ => (R ξ)⁻¹ * R ξ) = 1 := by
  rw [inv_return_expost hR]
  exact 𝔼.const t 1

/-- Cochrane (2023), §3.3, p. 56: the ex-post real return from `t` to `t + 1` on one-period
debt, `R_{t+1} = (1/Q_t)(P_t/P_{t+1})`. -/
noncomputable def expostReturn (Q P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => (Q t ξ)⁻¹ * (P t ξ / P (t + 1) ξ)

/-- Cochrane (2023), §3.3, pp. 55–56: with `Q_t = 1/(1+i_t)`,
`R_{t+1} = (1+i_t)P_t/P_{t+1}`. -/
theorem expostReturn_rate {Q P i : ℕ → Ω → ℝ} {t : ℕ}
    (hQi : Q t = fun ξ => (1 + i t ξ)⁻¹) :
    expostReturn Q P t = fun ξ => (1 + i t ξ) * (P t ξ / P (t + 1) ξ) := by
  funext ξ
  simp [expostReturn, hQi]

/-- Cochrane (2023), §3.3, p. 56: the flow condition `B_{t−1}/P_t = s_t + Q_tB_t/P_t` (for any
bond price `Q ≠ 0`) is, state by state, `B_{t−1}/P_t = s_t + R⁻¹_{t+1}B_t/P_{t+1}`. -/
theorem flow_expost {Q P s D : ℕ → Ω → ℝ} {t : ℕ} (hQ0 : ∀ ξ, Q t ξ ≠ 0)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) :
    FlowOne Q P s D t ↔
      ∀ ξ, realDebt D P t ξ = s t ξ + (expostReturn Q P t ξ)⁻¹ * realDebt D P (t + 1) ξ := by
  refine forall_congr' fun ξ => ?_
  have h : (expostReturn Q P t ξ)⁻¹ * realDebt D P (t + 1) ξ = Q t ξ * D (t + 1) ξ / P t ξ := by
    have := hQ0 ξ
    have := hP0 t ξ
    have := hP0 (t + 1) ξ
    simp only [expostReturn, realDebt]
    field_simp
  rw [h, realDebt]

/-- Cochrane (2023), §3.3, p. 56: a process satisfying the ex-post flow
`x_t = s_t + g_t x_{t+1}` state by state, where `g_t = R⁻¹_{t+1}` is the realised one-period
discount factor. -/
def ExPostFlow (g s x : ℕ → Ω → ℝ) : Prop := ∀ t ξ, x t ξ = s t ξ + g t ξ * x (t + 1) ξ

/-- Cochrane (2023), eq. (3.6), p. 56, finite horizon (survey E12: the terminal product runs to
`T`, not `j`): `x_t = ∑_{j<T}(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j} + (∏_{k=1}^{T}R⁻¹_{t+k})x_{t+T}`
state by state. -/
theorem expost_iterate {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) (t T : ℕ) (ξ : Ω) :
    x t ξ = ∑ j ∈ Finset.range T, sdf g t j ξ * s (t + j) ξ + sdf g t T ξ * x (t + T) ξ := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, h (t + T) ξ, sdf_succ, Pi.mul_apply,
      show t + (T + 1) = t + T + 1 by omega]
    ring

/-- Cochrane (2023), eq. (3.6), p. 56: state by state, the ex-post present-value partial sums
converge to `x_t` iff the terminal term `(∏_{k=1}^{T}R⁻¹_{t+k})x_{t+T}` tends to zero. -/
theorem expost_tendsto_iff {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) (t : ℕ) (ξ : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, sdf g t j ξ * s (t + j) ξ) atTop (𝓝 (x t ξ)) ↔
      Tendsto (fun T => sdf g t T ξ * x (t + T) ξ) atTop (𝓝 0) := by
  have e : ∀ T, sdf g t T ξ * x (t + T) ξ =
      x t ξ - ∑ j ∈ Finset.range T, sdf g t j ξ * s (t + j) ξ := fun T => by
    rw [expost_iterate h t T ξ]
    ring
  simp_rw [e]
  constructor
  · intro hl
    simpa using (tendsto_const_nhds (x := x t ξ)).sub hl
  · intro hl
    have := (tendsto_const_nhds (x := x t ξ)).sub hl
    simp only [sub_sub_cancel, sub_zero] at this
    exact this

/-- Cochrane (2023), §3.3, p. 56 (the present value with ex-post returns): if in state `ξ` the
terminal term vanishes and the series converges (absolutely), then
`B_{t−1}/P_t = ∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}`. -/
theorem expost_pv {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) (t : ℕ) (ξ : Ω)
    (hsum : Summable fun j => sdf g t j ξ * s (t + j) ξ)
    (hterm : Tendsto (fun T => sdf g t T ξ * x (t + T) ξ) atTop (𝓝 0)) :
    x t ξ = ∑' j, sdf g t j ξ * s (t + j) ξ :=
  tendsto_nhds_unique ((expost_tendsto_iff h t ξ).mpr hterm) hsum.hasSum.tendsto_sum_nat

/-- Cochrane (2023), §3.3, p. 56 ("This equation holds ex-post, so it also holds ex-ante"):
for every `ExpectationSystem` and `x_t` known at `t`, the partial sums
`∑_{j<T}E_t[(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}]` converge to `x_t` iff the expected terminal term
`E_t[(∏_{k=1}^{T}R⁻¹_{t+k})x_{t+T}]` tends to zero. -/
theorem expost_E_tendsto_iff {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) {t : ℕ}
    (hx : 𝔼.E t (x t) = x t) (ξ : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, 𝔼.E t (sdf g t j * s (t + j)) ξ) atTop
        (𝓝 (x t ξ)) ↔
      Tendsto (fun T => 𝔼.E t (sdf g t T * x (t + T)) ξ) atTop (𝓝 0) := by
  have e : ∀ T, 𝔼.E t (sdf g t T * x (t + T)) ξ =
      x t ξ - ∑ j ∈ Finset.range T, 𝔼.E t (sdf g t j * s (t + j)) ξ := fun T => by
    have hfun : x t = ∑ j ∈ Finset.range T, sdf g t j * s (t + j) + sdf g t T * x (t + T) := by
      funext ξ'
      rw [expost_iterate h t T ξ', Pi.add_apply, Finset.sum_apply]
      rfl
    have := congrFun (congrArg (𝔼.E t) hfun) ξ
    rw [hx, map_add, map_sum, Pi.add_apply, Finset.sum_apply] at this
    linarith
  simp_rw [e]
  constructor
  · intro hl
    simpa using (tendsto_const_nhds (x := x t ξ)).sub hl
  · intro hl
    have := (tendsto_const_nhds (x := x t ξ)).sub hl
    simp only [sub_sub_cancel, sub_zero] at this
    exact this

/-- Cochrane (2023), §3.3, p. 56 (displayed present value with ex-post returns): if the
expected terminal term goes to zero and the series of expectations converges (absolutely), then
`B_{t−1}/P_t = ∑_j E_t[(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}]` under any `ExpectationSystem`; if
moreover the ex-post series converges absolutely in every state and `E_t` satisfies
conditional monotone convergence, this is `E_t[∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}]`. -/
theorem expost_pv_E {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) {t : ℕ}
    (hx : 𝔼.E t (x t) = x t) (ξ : Ω)
    (hsum : Summable fun j => 𝔼.E t (sdf g t j * s (t + j)) ξ)
    (hterm : Tendsto (fun T => 𝔼.E t (sdf g t T * x (t + T)) ξ) atTop (𝓝 0)) :
    x t ξ = ∑' j, 𝔼.E t (sdf g t j * s (t + j)) ξ ∧
      (MonotoneConvergence 𝔼 → (∀ ξ', Summable fun j => |sdf g t j ξ' * s (t + j) ξ'|) →
        x t ξ = 𝔼.E t (fun ξ' => ∑' j, sdf g t j ξ' * s (t + j) ξ') ξ) := by
  have h1 : x t ξ = ∑' j, 𝔼.E t (sdf g t j * s (t + j)) ξ :=
    tendsto_nhds_unique ((expost_E_tendsto_iff 𝔼 h hx ξ).mpr hterm)
      hsum.hasSum.tendsto_sum_nat
  refine ⟨h1, fun hMC habs => ?_⟩
  rw [h1]
  exact (E_tsum_abs 𝔼 hMC t (f := fun j => sdf g t j * s (t + j)) habs ξ).tsum_eq

/-- Cochrane (2023), §3.3, p. 56: taking `E_t` of the ex-post flow, `x_t = s_t + E_t[R⁻¹_{t+1}
x_{t+1}]` under any `ExpectationSystem` when `x_t` and `s_t` are known at `t`. -/
theorem expost_flow_E {g s x : ℕ → Ω → ℝ} (h : ExPostFlow g s x) {t : ℕ}
    (hx : 𝔼.E t (x t) = x t) (hs : 𝔼.E t (s t) = s t) :
    x t = s t + 𝔼.E t (g t * x (t + 1)) := by
  have hfun : x t = s t + g t * x (t + 1) := by
    funext ξ
    exact h t ξ
  conv_lhs => rw [← hx, hfun, map_add, hs]

/-- Cochrane (2023), §3.3, p. 56, under perfect foresight: with the bond price
`Q_t = (Λ_{t+1}/Λ_t)P_t/P_{t+1}`, `m ≠ 0`, `P ≠ 0`, the ex-post discount factor `R⁻¹_{t+1}`
is exactly `m_t`, so (3.6) and (3.5) coincide. -/
theorem pf_expost_inv_eq_sdf {m P : ℕ → Unit → ℝ} (hm : ∀ s ξ, m s ξ ≠ 0)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (t : ℕ) :
    (fun ξ => (expostReturn (bondPrice perfectForesight m P) P t ξ)⁻¹) = m t := by
  funext ξ
  have := hm t ξ
  have := hP0 t ξ
  have := hP0 (t + 1) ξ
  simp only [expostReturn, bondPrice, perfectForesight, LinearMap.id_apply, Pi.mul_apply]
  field_simp

/-! ### (3.6) may explode while (3.5) is well defined -/

/-- Cochrane (2023), §3.3, p. 56 (example): the belief map of the "peso" information set-up
on `Option ℕ` (state `some n`: a fiscal regime switch at date `n`; `none`: no switch ever).
At date `t` a switch at `n ≤ t` is known; otherwise agents are certain the switch comes at
`t + 1`. -/
def pesoPt (t : ℕ) : Option ℕ → Option ℕ
  | some n => if n ≤ t then some n else some (t + 1)
  | none => some (t + 1)

/-- Cochrane (2023), §3.3, p. 56 (example): a switch at `n ≤ t` is known at `t`. -/
theorem pesoPt_some_le {t n : ℕ} (h : n ≤ t) : pesoPt t (some n) = some n := by
  simp [pesoPt, h]

/-- Cochrane (2023), §3.3, p. 56 (example): before the switch, agents believe it comes at
`t + 1`. -/
theorem pesoPt_some_gt {t n : ℕ} (h : t < n) : pesoPt t (some n) = some (t + 1) := by
  simp [pesoPt, show ¬ n ≤ t by omega]

/-- Cochrane (2023), §3.3, p. 56 (example): on the never-switch path, agents believe the switch
comes at `t + 1`. -/
theorem pesoPt_none (t : ℕ) : pesoPt t none = some (t + 1) := rfl

/-- Cochrane (2023), §3.3, p. 56 (example): later beliefs do not change the believed state
of an earlier date's belief. -/
theorem pesoPt_pt {s t : ℕ} (h : s ≤ t) (ξ : Option ℕ) : pesoPt t (pesoPt s ξ) = pesoPt s ξ := by
  have key : pesoPt t (some (s + 1)) = some (s + 1) := by
    rcases Nat.lt_or_ge t (s + 1) with h1 | h1
    · rw [pesoPt_some_gt h1, show t = s by omega]
    · exact pesoPt_some_le h1
  cases ξ with
  | none => rw [pesoPt_none, key]
  | some n =>
    rcases Nat.lt_or_ge s n with h1 | h1
    · rw [pesoPt_some_gt h1, key]
    · rw [pesoPt_some_le h1, pesoPt_some_le (h1.trans h)]

/-- Cochrane (2023), §3.3, p. 56 (example): an earlier belief evaluated at a later belief is
the earlier belief. -/
theorem pesoPt_pt' {s t : ℕ} (h : s ≤ t) (ξ : Option ℕ) :
    pesoPt s (pesoPt t ξ) = pesoPt s ξ := by
  cases ξ with
  | none => rw [pesoPt_none, pesoPt_none, pesoPt_some_gt (by omega)]
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, pesoPt_some_gt (by omega), pesoPt_some_gt (by omega)]
    · rw [pesoPt_some_le h1]

/-- Cochrane (2023), §3.3, p. 56 ("using any set of probabilities"): the expectation system
`E_t x = x ∘ pesoPt t` of the peso example. -/
def pesoSystem : ExpectationSystem (Option ℕ) where
  E := fun t => LinearMap.funLeft ℝ ℝ (pesoPt t)
  const := fun _ _ => rfl
  mono := fun _ _ _ h ξ => h _
  tower := fun h x => by
    funext ξ
    simp only [LinearMap.funLeft_apply, pesoPt_pt h]
  known := fun h x => by
    funext ξ
    simp only [LinearMap.funLeft_apply, pesoPt_pt' h]

/-- Cochrane (2023), §3.3, p. 56 (example): `E_t x (ξ) = x (pesoPt t ξ)`. -/
theorem pesoSystem_E (t : ℕ) (x : Option ℕ → ℝ) (ξ : Option ℕ) :
    pesoSystem.E t x ξ = x (pesoPt t ξ) := rfl

/-- Cochrane (2023), §3.3, p. 56 (example): the peso system has the pull-out property. -/
theorem pesoSystem_pullOut : pesoSystem.PullOut := by
  intro t a y ha
  funext ξ
  have h := congrFun ha ξ
  simp only [pesoSystem_E] at h
  simp only [pesoSystem_E, Pi.mul_apply, h]

/-- Cochrane (2023), §3.3, p. 56 (example): the peso system satisfies conditional monotone
convergence. -/
theorem pesoSystem_monotoneConvergence : MonotoneConvergence pesoSystem := by
  intro t f _ hs ξ
  simp only [pesoSystem_E]
  exact (hs _).hasSum

/-- Cochrane (2023), §3.3, p. 56 (example): surpluses `−1` before the switch and `2` from the
switch date on. -/
def pesoS (t : ℕ) : Option ℕ → ℝ
  | some n => if n ≤ t then 2 else -1
  | none => -1

/-- Cochrane (2023), §3.3, p. 56 (example): the real debt value, `4` after the switch and `1`
before. -/
def pesoX (t : ℕ) : Option ℕ → ℝ
  | some n => if n ≤ t then 4 else 1
  | none => 1

/-- Cochrane (2023), §3.3, p. 56 (example): the values of `pesoX` and `pesoS` after and
before the switch. -/
theorem peso_values (t n : ℕ) :
    (n ≤ t → pesoX t (some n) = 4 ∧ pesoS t (some n) = 2) ∧
      (t < n → pesoX t (some n) = 1 ∧ pesoS t (some n) = -1) ∧
      pesoX t none = 1 ∧ pesoS t none = -1 := by
  refine ⟨fun h => ?_, fun h => ?_, rfl, rfl⟩
  · simp [pesoX, pesoS, h]
  · simp [pesoX, pesoS, show ¬ n ≤ t by omega]

/-- Cochrane (2023), §3.3, p. 56 (example): the real debt value is known at its date. -/
theorem pesoX_adapted : pesoSystem.Adapted pesoX := by
  intro t
  funext ξ
  rw [pesoSystem_E]
  cases ξ with
  | none => rw [pesoPt_none, (peso_values t (t + 1)).2.1 (by omega) |>.1, (peso_values t 0).2.2.1]
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, (peso_values t (t + 1)).2.1 (by omega) |>.1,
        (peso_values t n).2.1 h1 |>.1]
    · rw [pesoPt_some_le h1]

/-- Cochrane (2023), §3.3, p. 56 (example): surpluses are known at their date. -/
theorem pesoS_adapted : pesoSystem.Adapted pesoS := by
  intro t
  funext ξ
  rw [pesoSystem_E]
  cases ξ with
  | none => rw [pesoPt_none, (peso_values t (t + 1)).2.1 (by omega) |>.2, (peso_values t 0).2.2.2]
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, (peso_values t (t + 1)).2.1 (by omega) |>.2,
        (peso_values t n).2.1 h1 |>.2]
    · rw [pesoPt_some_le h1]

/-- Cochrane (2023), §3.3, p. 56 (example): the flow `x_t = s_t + ½E_t x_{t+1}` holds in every
state at every date. -/
theorem pesoX_flow (t : ℕ) (ξ : Option ℕ) :
    pesoX t ξ = pesoS t ξ + 1 / 2 * pesoX (t + 1) (pesoPt t ξ) := by
  have hsw : pesoX (t + 1) (some (t + 1)) = 4 := ((peso_values (t + 1) (t + 1)).1 le_rfl).1
  cases ξ with
  | none =>
    rw [pesoPt_none, hsw, (peso_values t 0).2.2.1, (peso_values t 0).2.2.2]
    norm_num
  | some n =>
    rcases Nat.lt_or_ge t n with h1 | h1
    · rw [pesoPt_some_gt h1, hsw, ((peso_values t n).2.1 h1).1, ((peso_values t n).2.1 h1).2]
      norm_num
    · rw [pesoPt_some_le h1, ((peso_values t n).1 h1).1, ((peso_values t n).1 h1).2,
        ((peso_values (t + 1) n).1 (by omega)).1]
      norm_num

/-- Cochrane (2023), §3.3, p. 56 (example): the real debt value lies in `[1, 4]`. -/
theorem pesoX_bounds (t : ℕ) (ξ : Option ℕ) : 1 ≤ pesoX t ξ ∧ pesoX t ξ ≤ 4 := by
  cases ξ with
  | none => simp [pesoX]
  | some n =>
    simp only [pesoX]
    split_ifs <;> norm_num

/-- Cochrane (2023), §3.3, p. 56 (example): `|s| ≤ 2`. -/
theorem pesoS_abs_le (t : ℕ) (ξ : Option ℕ) : |pesoS t ξ| ≤ 2 := by
  cases ξ with
  | none => norm_num [pesoS]
  | some n =>
    simp only [pesoS]
    split_ifs <;> norm_num

/-- Cochrane (2023), §3.3, p. 56 (example): the nominal price level `P_t = 1/x_t` with
one unit of nominal debt `B_{t−1} = 1` outstanding. -/
noncomputable def pesoP (t : ℕ) (ξ : Option ℕ) : ℝ := (pesoX t ξ)⁻¹

/-- Cochrane (2023), §3.3, p. 56 (example): along the never-switch path the realised ex-post
return on debt is `R_{t+1} = 1/2`. -/
theorem pesoReturn_none (t : ℕ) :
    expostReturn (bondPrice pesoSystem (fun _ _ => 1 / 2) pesoP) pesoP t none = 1 / 2 := by
  simp only [expostReturn, bondPrice, pesoSystem_E, Pi.mul_apply, pesoP, pesoPt, pesoX,
    show ¬ t + 1 ≤ t by omega, le_refl, ↓reduceIte]
  norm_num

/-- Cochrane (2023), §3.3, p. 56: "It is possible that the present value is well defined using
marginal utility or the discount factor as in (3.5), but the present value and terminal
condition using ex-post returns (3.6) explode." In the peso economy (risk-neutral discount
factor `1/2`, one unit of nominal one-period debt, `P_t = 1/x_t`, bond price
`Q_t = E_t[½P_t/P_{t+1}]`, expectations `pesoSystem` with pull-out and conditional monotone
convergence): the flow condition, the transversality condition and the valuation formula (3.5)
hold at every date in every state, surpluses have absolutely summable present values; but along
the realised never-switch path the ex-post flow holds with `R⁻¹_{t+1} = 2`, and the ex-post
present-value partial sums of (3.6) tend to `−∞` while the terminal term tends to `+∞`.
(Along that path, agents at every date assign probability one to a switch next period.) -/
theorem expost_may_diverge :
    let m : ℕ → Option ℕ → ℝ := fun _ _ => 1 / 2
    let D : ℕ → Option ℕ → ℝ := fun _ _ => 1
    let g : ℕ → Option ℕ → ℝ :=
      fun t ξ => (expostReturn (bondPrice pesoSystem m pesoP) pesoP t ξ)⁻¹
    (∀ t, FlowOne (bondPrice pesoSystem m pesoP) pesoP pesoS D t) ∧
      (∀ t, TVC pesoSystem m (realDebt D pesoP) t) ∧
      (∀ t, realDebt D pesoP t = pv pesoSystem m pesoS t) ∧
      SurplusSummable pesoSystem m pesoS ∧
      ExPostFlow g pesoS (realDebt D pesoP) ∧
      (∀ t, g t none = 2) ∧
      Tendsto (fun T => ∑ j ∈ Finset.range T, sdf g 0 j none * pesoS j none) atTop atBot ∧
      Tendsto (fun T => sdf g 0 T none * realDebt D pesoP T none) atTop atTop := by
  intro m D g
  have hxeq : realDebt D pesoP = pesoX := by
    funext t ξ
    simp [realDebt, D, pesoP]
  have hPpos : ∀ s ξ, 0 < pesoP s ξ := fun s ξ =>
    inv_pos.mpr (lt_of_lt_of_le one_pos (pesoX_bounds s ξ).1)
  have hP0 : ∀ s ξ, pesoP s ξ ≠ 0 := fun s ξ => (hPpos s ξ).ne'
  have hPa : pesoSystem.Adapted pesoP := by
    intro t
    funext ξ
    have h := congrFun (pesoX_adapted t) ξ
    simp only [pesoSystem_E] at h
    simp only [pesoSystem_E, pesoP, h]
  have hmE : ∀ s, pesoSystem.E (s + 1) (m s) = m s := fun s => pesoSystem.const (s + 1) (1 / 2)
  have hm0 : ∀ s ξ, 0 ≤ m s ξ := fun _ _ => by norm_num [m]
  have hsdf : ∀ t n, sdf m t n = fun _ => (1 / 2 : ℝ) ^ n := fun t n => sdf_const _ t n
  have hD1 : ∀ t, pesoSystem.E t (D (t + 1)) = D (t + 1) := fun t => pesoSystem.const t 1
  -- the flow condition
  have hflow : ∀ t, FlowOne (bondPrice pesoSystem m pesoP) pesoP pesoS D t := by
    intro t
    rw [flowOne_iff_rec pesoSystem pesoSystem_pullOut (hPa t) (hD1 t) hP0, hxeq]
    funext ξ
    rw [Pi.add_apply, pesoSystem_E, Pi.mul_apply]
    exact pesoX_flow t ξ
  -- surplus summability
  have hss : SurplusSummable pesoSystem m pesoS := by
    intro t ξ
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left 2)
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      exact mul_nonneg (by positivity) (abs_nonneg _)
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      have := pesoS_abs_le (t + n) (pesoPt t ξ)
      have hp : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      nlinarith
  -- the transversality condition
  have htvc : ∀ t, TVC pesoSystem m (realDebt D pesoP) t := by
    intro t ξ
    rw [hxeq]
    have hlim : Tendsto (fun N : ℕ => 4 * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 4
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hlim
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      exact mul_nonneg (by positivity) (by linarith [(pesoX_bounds (t + N) (pesoPt t ξ)).1])
    · rw [pesoSystem_E, hsdf, Pi.mul_apply]
      have := (pesoX_bounds (t + N) (pesoPt t ξ)).2
      have hp : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
      nlinarith
  -- the valuation formula (3.5)
  have hxa : pesoSystem.Adapted (realDebt D pesoP) := by rw [hxeq]; exact pesoX_adapted
  have hval := ((flow_tvc_iff_pv pesoSystem pesoSystem_monotoneConvergence pesoSystem_pullOut
    hmE hm0 pesoS_adapted hss hxa).mp ⟨fun t => (flowOne_iff_rec pesoSystem pesoSystem_pullOut
      (hPa t) (hD1 t) hP0).mp (hflow t), htvc⟩)
  -- the ex-post flow
  have hQ0 : ∀ t ξ, bondPrice pesoSystem m pesoP t ξ ≠ 0 := by
    intro t ξ
    simp only [bondPrice, pesoSystem_E, Pi.mul_apply, m]
    exact (mul_pos (by norm_num) (div_pos (hPpos _ _) (hPpos _ _))).ne'
  have hexp : ExPostFlow g pesoS (realDebt D pesoP) := fun t ξ =>
    (flow_expost (hQ0 t) hP0).mp (hflow t) ξ
  have hg : ∀ t, g t none = 2 := fun t => by
    simp only [g, m]
    rw [pesoReturn_none]
    norm_num
  have hsdfg : ∀ j, sdf g 0 j none = 2 ^ j := fun j => by
    simp only [sdf, Finset.prod_apply, zero_add, hg, Finset.prod_const, Finset.card_range]
  refine ⟨hflow, htvc, hval, hss, hexp, hg, ?_, ?_⟩
  · have e : ∀ T, ∑ j ∈ Finset.range T, sdf g 0 j none * pesoS j none =
        -(2 : ℝ) ^ T + 1 := fun T => by
      simp only [hsdfg, pesoS, mul_neg, mul_one, Finset.sum_neg_distrib]
      rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      ring
    simp_rw [e]
    exact (tendsto_neg_atTop_atBot.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).atBot_add
      tendsto_const_nhds
  · have e : ∀ T, sdf g 0 T none * realDebt D pesoP T none = (2 : ℝ) ^ T := fun T => by
      rw [hsdfg, hxeq]
      simp [pesoX]
    simp_rw [e]
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)

/-! ### On a finite event tree (3.6) cannot explode -/

/-- Cochrane (2023), §3.3, p. 56 (finite trees): on a finite event tree a variable is known at
`t` iff it is constant on the date-`t` information cells. -/
theorem finiteTree_known_iff {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    (t : ℕ) (y : Ω' → ℝ) :
    T.toExpectationSystem.E t y = y ↔ ∀ a b, T.info t a b → y a = y b := by
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  constructor
  · intro h a b hab
    rw [← h]
    exact T.condE_congr y hab
  · intro h
    funext ξ
    exact T.condE_of_const_on_cell fun ξ' h' => h ξ' ξ h'

/-- Cochrane (2023), §3.3, p. 56 (finite trees): information on a finite tree stops being
refined after some date `T₀` (the set of indistinguishable pairs is a decreasing sequence of
finite sets). -/
theorem finiteTree_info_stable {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') :
    ∃ T0, ∀ t, T0 ≤ t → ∀ a b, T.info t a b ↔ T.info T0 a b := by
  classical
  let F : ℕ → Finset (Ω' × Ω') := fun t => Finset.univ.filter fun p => T.info t p.1 p.2
  have hsub : ∀ {u v : ℕ}, u ≤ v → F v ⊆ F u := fun huv p hp => by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact T.refines huv _ _ hp
  have hex : ∃ k, ∃ t, (F t).card = k := ⟨(F 0).card, 0, rfl⟩
  obtain ⟨T0, hT0⟩ := Nat.find_spec hex
  refine ⟨T0, fun t ht a b => ⟨fun h => T.refines ht a b h, fun h => ?_⟩⟩
  have hmin : Nat.find hex ≤ (F t).card := Nat.find_min' hex ⟨t, rfl⟩
  have heq : F t = F T0 := Finset.eq_of_subset_of_card_le (hsub ht) (by omega)
  have hmem : (a, b) ∈ F T0 := by simp [F, h]
  rw [← heq] at hmem
  simpa [F] using hmem

/-- Cochrane (2023), §3.3, p. 56 (finite trees): after the date `T₀` at which information stops
being refined, whatever will be known is already known. -/
theorem finiteTree_eventually_known {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') :
    ∃ T0, ∀ t k, T0 ≤ t → t ≤ k → ∀ y, T.toExpectationSystem.E k y = y →
      T.toExpectationSystem.E t y = y := by
  obtain ⟨T0, hT0⟩ := finiteTree_info_stable T
  refine ⟨T0, fun t k ht htk y hy => ?_⟩
  rw [finiteTree_known_iff] at hy ⊢
  intro a b hab
  exact hy a b ((hT0 k (ht.trans htk) a b).mpr ((hT0 t ht a b).mp hab))

/-- Cochrane (2023), §3.3, p. 56: the flow condition `B_{t−1}/P_t = s_t + Q_tB_t/P_t` at every
date gives the ex-post flow with `R⁻¹_{t+1} = (expostReturn Q P t)⁻¹` in every state, also
where `Q_t = 0` (then both discount factors are zero). -/
theorem expostFlow_of_flowOne {Q P s D : ℕ → Ω → ℝ} (hflow : ∀ t, FlowOne Q P s D t)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) :
    ExPostFlow (fun t ξ => (expostReturn Q P t ξ)⁻¹) s (realDebt D P) := by
  intro t ξ
  have h := hflow t ξ
  by_cases hQ : Q t ξ = 0
  · simpa [expostReturn, realDebt, hQ] using h
  · simp only [expostReturn, realDebt]
    rw [h]
    have := hP0 t ξ
    have := hP0 (t + 1) ξ
    field_simp

/-- Cochrane (2023), §3.3, p. 56, the precise true statement behind "(3.6) may explode" on a
finite event tree (genuine uncertainty, every state of positive probability): if the flow
condition with SDF bond prices `Q_t = E_t[(Λ_{t+1}/Λ_t)P_t/P_{t+1}]` and the transversality
condition hold at every date (hence (3.5), `valuation_sdf_iff`), then in every state and at
every date the ex-post present value (3.6) with discount factors
`g_t = R⁻¹_{t+1}`, `R_{t+1} = (1/Q_t)P_t/P_{t+1}`, converges
absolutely, its terminal term tends to zero, and
`B_{t−1}/P_t = ∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}`. So the explosion of `expost_may_diverge`
can only happen along a path to which the expectation system gives zero probability. -/
theorem finiteTree_expost_pv {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    {m P s D : ℕ → Ω' → ℝ} (hm : ∀ k, T.toExpectationSystem.E (k + 1) (m k) = m k)
    (hm0 : ∀ k ξ, 0 ≤ m k ξ) (hsa : T.toExpectationSystem.Adapted s)
    (hs : SurplusSummable T.toExpectationSystem m s) (hPa : T.toExpectationSystem.Adapted P)
    (hP0 : ∀ k ξ, P k ξ ≠ 0)
    (hflow : ∀ t, FlowOne (bondPrice T.toExpectationSystem m P) P s D t)
    (htvc : ∀ t, TVC T.toExpectationSystem m (realDebt D P) t)
    (hx : T.toExpectationSystem.Adapted (realDebt D P)) {g : ℕ → Ω' → ℝ}
    (hgdef : g = fun k ξ' => (expostReturn (bondPrice T.toExpectationSystem m P) P k ξ')⁻¹)
    (t : ℕ) (ξ : Ω') :
    Summable (fun j => |sdf g t j ξ * s (t + j) ξ|) ∧
      Tendsto (fun N => sdf g t N ξ * realDebt D P (t + N) ξ) atTop (𝓝 0) ∧
      realDebt D P t ξ = ∑' j, sdf g t j ξ * s (t + j) ξ := by
  have hPO := ExpectationsFiniteTree.finiteTree_pullOut T
  obtain ⟨T0, hT0⟩ := finiteTree_eventually_known T
  -- after `T₀` the ex-post discount factor is the SDF
  have hg : ∀ k, T0 ≤ k → g k = m k := by
    intro k hk
    funext ξ'
    have hz : T.toExpectationSystem.E k (m k * fun ξ => P k ξ / P (k + 1) ξ) =
        m k * fun ξ => P k ξ / P (k + 1) ξ := by
      refine hT0 k (k + 1) hk (Nat.le_succ k) _ ?_
      rw [finiteTree_known_iff]
      intro a b hab
      have h1 := (finiteTree_known_iff T (k + 1) (m k)).mp (hm k) a b hab
      have h2 := (finiteTree_known_iff T k (P k)).mp (hPa k) a b
        (T.refines (Nat.le_succ k) a b hab)
      have h3 := (finiteTree_known_iff T (k + 1) (P (k + 1))).mp (hPa (k + 1)) a b hab
      simp only [Pi.mul_apply, h1, h2, h3]
    have hQ : bondPrice T.toExpectationSystem m P k ξ' = m k ξ' * (P k ξ' / P (k + 1) ξ') := by
      rw [bondPrice, hz]
      rfl
    have ha : P k ξ' / P (k + 1) ξ' ≠ 0 := div_ne_zero (hP0 _ _) (hP0 _ _)
    simp only [hgdef, expostReturn, hQ]
    by_cases hmz : m k ξ' = 0
    · simp [hmz]
    · have := hP0 k ξ'
      have := hP0 (k + 1) ξ'
      field_simp
  have hsdfg : ∀ k, T0 ≤ k → ∀ n, sdf g k n = sdf m k n := by
    intro k hk n
    simp only [sdf]
    exact Finset.prod_congr rfl fun j _ => hg (k + j) (by omega)
  -- after `T₀` conditional expectations of later-known variables are pathwise values
  have hE : ∀ k, T0 ≤ k → ∀ n (y : Ω' → ℝ), T.toExpectationSystem.E (k + n) y = y →
      T.toExpectationSystem.E k y = y := fun k hk n y hy =>
    hT0 k (k + n) hk (by omega) y hy
  have habs : ∀ k n, T.toExpectationSystem.E (k + n) (fun ξ => |s (k + n) ξ|) =
      fun ξ => |s (k + n) ξ| := by
    intro k n
    rw [finiteTree_known_iff]
    intro a b hab
    rw [(finiteTree_known_iff T _ _).mp (hsa (k + n)) a b hab]
  have hpath_s : ∀ k, T0 ≤ k → ∀ n, T.toExpectationSystem.E k
      (sdf m k n * fun ξ => |s (k + n) ξ|) ξ = sdf m k n ξ * |s (k + n) ξ| := by
    intro k hk n
    rw [hE k hk n _ (known_mul _ hPO (sdf_known _ hPO hm k n) (habs k n))]
    rfl
  have hpath_x : ∀ k, T0 ≤ k → ∀ N, T.toExpectationSystem.E k
      (sdf m k N * realDebt D P (k + N)) ξ = sdf m k N ξ * realDebt D P (k + N) ξ := by
    intro k hk N
    rw [hE k hk N _ (known_mul _ hPO (sdf_known _ hPO hm k N) (hx (k + N)))]
    rfl
  -- pass from `t` to `t₁ = max t T₀`
  obtain ⟨d, hd⟩ : ∃ d, t + d = max t T0 := ⟨max t T0 - t, by omega⟩
  have ht1 : T0 ≤ max t T0 := le_max_right _ _
  have hsum1 : Summable fun n => sdf m (max t T0) n ξ * |s (max t T0 + n) ξ| :=
    (hs (max t T0) ξ).congr fun n => hpath_s _ ht1 n
  have hterm1 : Tendsto (fun N => sdf m (max t T0) N ξ * realDebt D P (max t T0 + N) ξ) atTop
      (𝓝 0) := (htvc (max t T0) ξ).congr fun N => hpath_x _ ht1 N
  have hsplit : ∀ n, sdf g t (n + d) ξ = sdf g t d ξ * sdf m (max t T0) n ξ := by
    intro n
    rw [add_comm n d, sdf_add, hd, hsdfg _ ht1]
    rfl
  have hA : Summable fun n => |sdf g t (n + d) ξ * s (t + (n + d)) ξ| := by
    refine (hsum1.mul_left |sdf g t d ξ|).congr fun n => ?_
    have h0 : |sdf m (max t T0) n ξ| = sdf m (max t T0) n ξ :=
      abs_of_nonneg (sdf_nonneg hm0 (max t T0) n ξ)
    have e : sdf g t (n + d) ξ * s (t + (n + d)) ξ =
        sdf g t d ξ * (sdf m (max t T0) n ξ * s (max t T0 + n) ξ) := by
      rw [hsplit, show t + (n + d) = max t T0 + n by omega, mul_assoc]
    simp only [e, abs_mul, h0]
  have hsumA := (summable_nat_add_iff (f := fun j => |sdf g t j ξ * s (t + j) ξ|) d).mp hA
  have hB : Tendsto (fun N : ℕ => sdf g t (N + d) ξ * realDebt D P (t + (N + d)) ξ) atTop
      (𝓝 (0 : ℝ)) := by
    have h1 : (fun N => sdf g t (N + d) ξ * realDebt D P (t + (N + d)) ξ) =
        fun N => sdf g t d ξ * (sdf m (max t T0) N ξ * realDebt D P (max t T0 + N) ξ) := by
      funext N
      rw [hsplit, show t + (N + d) = max t T0 + N by omega, mul_assoc]
    rw [h1]
    have h2 := hterm1.const_mul (sdf g t d ξ)
    rwa [mul_zero] at h2
  have hterm := (tendsto_add_atTop_iff_nat
    (f := fun N => sdf g t N ξ * realDebt D P (t + N) ξ) d).mp hB
  have hflowg : ExPostFlow g s (realDebt D P) := by
    rw [hgdef]
    exact expostFlow_of_flowOne hflow hP0
  exact ⟨hsumA, hterm, expost_pv hflowg t ξ hsumA.of_abs hterm⟩

/-! ### Long-term debt: the portfolio return (3.7) and the flow identity (3.8) -/

/-- Cochrane (2023), eq. (3.7), p. 56: the ex-post real return on the whole debt portfolio,
`R_{t+1} = ∑_jQ_{t+1}^{(t+1+j)}B_t^{(t+1+j)} / ∑_jQ_t^{(t+1+j)}B_t^{(t+1+j)} · P_t/P_{t+1}`
(maximum maturity `K`). -/
noncomputable def portfolioReturn (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ξ => mktValue K Q B (t + 1) ξ / purchaseValue K Q B t ξ * (P t ξ / P (t + 1) ξ)

/-- Cochrane (2023), eqs. (3.2), (3.7)–(3.8), pp. 53, 56–57: with maximum maturity `K`,
maturing bonds worth face value, `P ≠ 0`, and a nonzero market value of the debt at `t + 1`,
the flow condition (3.2) holds iff the flow identity with the portfolio return (3.8)
`∑_jQ_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = s_t + R⁻¹_{t+1}∑_jQ_{t+1}^{(t+1+j)}B_t^{(t+1+j)}/P_{t+1}`
holds (exact, no pricing assumption). -/
theorem flowLT_iff_3_8 {K : ℕ} {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ}
    (hK : MaxMaturity K B) {t : ℕ} (hQ0 : Q t 0 = 1) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hV : ∀ ξ, mktValue K Q B (t + 1) ξ ≠ 0) :
    FlowLT K P s Q B t ↔ ∀ ξ, realValue K Q B P t ξ =
      s t ξ + (portfolioReturn K Q B P t ξ)⁻¹ * realValue K Q B P (t + 1) ξ := by
  rw [flowLT_iff_value hK hQ0 (hP0 t), funext_iff]
  refine forall_congr' fun ξ => ?_
  have h : (portfolioReturn K Q B P t ξ)⁻¹ * realValue K Q B P (t + 1) ξ =
      purchaseValue K Q B t ξ / P t ξ := by
    have := hV ξ
    have := hP0 t ξ
    have := hP0 (t + 1) ξ
    simp only [portfolioReturn, realValue]
    by_cases hp : purchaseValue K Q B t ξ = 0
    · simp [hp]
    · field_simp
  rw [Pi.add_apply, h]

/-- Cochrane (2023), p. 57 ("We iterate again"): with long-term debt, if (3.2) holds at every
date and the market value of the debt is never zero, then in every state where the terminal
term vanishes and the series converges absolutely,
`∑_jQ_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = ∑_j(∏_{k=1}^{j}R⁻¹_{t+k})s_{t+j}` with the portfolio
return (3.7). -/
theorem expostLT_pv {K : ℕ} {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ}
    (hK : MaxMaturity K B) (hQ0 : ∀ t, Q t 0 = 1) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hV : ∀ t ξ, mktValue K Q B t ξ ≠ 0) (hflow : ∀ t, FlowLT K P s Q B t) (t : ℕ) (ξ : Ω)
    (hsum : Summable fun j =>
      sdf (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) t j ξ * s (t + j) ξ)
    (hterm : Tendsto (fun T => sdf (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) t T ξ *
      realValue K Q B P (t + T) ξ) atTop (𝓝 0)) :
    realValue K Q B P t ξ =
      ∑' j, sdf (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) t j ξ * s (t + j) ξ := by
  have h : ExPostFlow (fun k ξ' => (portfolioReturn K Q B P k ξ')⁻¹) s (realValue K Q B P) :=
    fun k ξ' => (flowLT_iff_3_8 hK (hQ0 k) hP0 (hV (k + 1))).mp (hflow k) ξ'
  exact expost_pv h t ξ hsum hterm

end Cochrane.Generality.StochasticDiscount
