/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR5ActiveFiscal

/-!
# Active fiscal policy under uncertainty: uniqueness on event trees

Cochrane (2023), *The Fiscal Theory of the Price Level*, Ch. 19, §19.5, pp. 448–454:
"Active fiscal policy can rule out these multiple equilibria" (p. 454) and the valuation
equation (19.35), p. 450. `TidyR5ActiveFiscal` proved uniqueness across all paths under perfect
foresight, constant money growth and the constant surplus of the standard path. Here the
statement is generalised to genuine uncertainty (any `ExpectationSystem` with the pull-out
property and full support, in particular every finite event tree), money supplies that are an
arbitrary positive adapted process (time-varying, random money growth) and an arbitrary adapted
surplus process.

## Setting

Constant endowment `y > 0` and velocity `V > 0`, so the stochastic discount factor is
`Λ_{t+1}/Λ_t = β` and the nominal bond price is `Q_t = E_t[βP_t/P_{t+1}]` (`bondPriceS`,
(19.32)). Money `M_t = Min (t+1)` is chosen at `t`; bonds `B_t = Bin (t+1)` are chosen at `t`.
An equilibrium (`StochMonetaryEq`) has positive prices, known choices, the cash constraint and
optimal money holding at every state ((19.24)–(19.25), (19.33)), the flow budget (19.27) at
every state and the conditional transversality conditions (19.28) at every date and state.
The standard path is `P_t = M_tV/y` (`stdPrice`) with bond price
`q_t = E_t[βM_t/M_{t+1}]` (`stdBondPrice`).

## Main results

* `wealth_recursion`: in equilibrium `β^tx_t = E_t[β^{t+1}x_{t+1}] + β^t(s_t + (1 − Q_t)y/V)`,
  `x_t = (B_{t−1} + M_{t−1})/P_t`.
* `std_le_bondPrice`: `Q_t ≥ q_t` at every state (given `q_t ≤ 1`).
* `stoch_price_unique`: if `B_{−1} + M_{−1} ≥ 0`, the date-0 valuation of the standard path
  holds (`E_0Σβ^j(s_j + (1 − q_j)y/V) = (B_{−1} + M_{−1})/P^{std}_0`) and either initial
  liabilities are positive or `q_0 < 1`, then EVERY equilibrium has `P = M V/y` and `Q = q` at
  every date and state.
* `coord_of_standard`, `unique_of_standard`: the date-0 condition holds whenever the standard
  equilibrium exists; then it is the only equilibrium (prices and bonds).
* Corrected statement and counterexamples: `pf_two_equilibria` — the proviso
  `B_{−1} + M_{−1} ≥ 0` is still needed (the perfect-foresight counterexample of
  `TidyR5ActiveFiscal` is an instance); `coin_no_standard_equilibrium` — under uncertainty the
  standard equilibrium, hence the hypothesis of `unique_of_standard`, can fail to exist: on the
  coin-flip tree with constant money and a surplus shock revealed at date 1 there is no
  equilibrium with `P = MV/y` (one-period nominal debt chosen at date 0 cannot absorb the shock
  when the price level is pinned by money). So "active fiscal policy determines the price level"
  holds under uncertainty in the form: at most the standard equilibrium exists, and it exists
  only if surpluses are coordinated with money.
* `corner_equilibrium`, `pin_needed`: the pinning condition (`B_{−1} + M_{−1} > 0` or
  `q_0 < 1`) cannot be dropped: with zero liabilities and money shrinking at the rate `β` there
  is a continuum of equilibria.
* `finiteTree_fullSupport`: every finite event tree has full support; with
  `ExpectationsFiniteTree.finiteTree_pullOut` the theorems apply to every finite tree.
-/

namespace Cochrane.Monetarism.TidyR6ActiveFiscalTree

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), (19.32), p. 450, with a constant endowment: the nominal bond price
`Q_t = E_t[βP_t/P_{t+1}]`. -/
noncomputable def bondPriceS (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => β * P t ω / P (t + 1) ω)

/-- Cochrane (2023), p. 454: the bond price along the standard path `P_t = M_tV/y`,
`q_t = E_t[βM_t/M_{t+1}]` (`M_t = Min (t+1)`). -/
noncomputable def stdBondPrice (β : ℝ) (Min : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => β * Min (t + 1) ω / Min (t + 2) ω)

/-- Cochrane (2023), p. 454: the standard (quantity-theory) price level `P_t = M_tV/y`. -/
noncomputable def stdPrice (y V : ℝ) (Min : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => Min (t + 1) ω * V / y

/-- Cochrane (2023), (19.35), p. 450: real government liabilities `(B_{t−1} + M_{t−1})/P_t`. -/
noncomputable def wealth (P Bin Min : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (Bin t ω + Min t ω) / P t ω

/-- Cochrane (2023), (19.28), p. 449: discounted real liabilities `β^t(B_{t−1} + M_{t−1})/P_t`. -/
noncomputable def discWealth (β : ℝ) (P Bin Min : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β ^ t * wealth P Bin Min t ω

/-- Cochrane (2023), (19.35), p. 450: the discounted date-`t` flow
`β^t(s_t + (1 − Q_t)y/V)` (surplus plus seigniorage). -/
noncomputable def flowTerm (β y V : ℝ) (P s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β ^ t * (s t ω + (1 - bondPriceS 𝔼 β P t ω) * y / V)

/-- Cochrane (2023), (19.35), p. 450: the discounted date-`t` flow of the standard path,
`β^t(s_t + (1 − q_t)y/V)`. -/
noncomputable def stdFlow (β y V : ℝ) (Min s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β ^ t * (s t ω + (1 - stdBondPrice 𝔼 β Min t ω) * y / V)

/-- Cochrane (2023), (19.27), p. 449: the flow budget at every date and state,
`B_{t−1} + M_{t−1} = Q_tB_t + M_t + P_ts_t`. -/
def FlowHolds (β : ℝ) (P Bin Min s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Bin t ω + Min t ω =
    bondPriceS 𝔼 β P t ω * Bin (t + 1) ω + Min (t + 1) ω + P t ω * s t ω

/-- Cochrane (2023), (19.28), p. 449: the transversality condition at every date and state,
`E_t[β^{t+T}(B_{t+T−1} + M_{t+T−1})/P_{t+T}] → 0`. -/
def CondTVC (β : ℝ) (P Bin Min : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T => 𝔼.E t (discWealth β P Bin Min (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 450 (what a state of positive probability means): full support —
a nonnegative variable whose conditional expectation vanishes at `ω` vanishes at `ω`. -/
def FullSupport : Prop := ∀ t (X : Ω → ℝ) ω, 0 ≤ X → 𝔼.E t X ω = 0 → X ω = 0

variable (β y V : ℝ) (P Bin Min s : ℕ → Ω → ℝ)

/-- Cochrane (2023), §19.5, pp. 448–450: a stochastic equilibrium of the cash-in-advance model
with constant endowment: positive prices, the price level known at `t`, bonds `B_t` and money
`M_t` chosen at `t`, the cash constraint `M_t ≥ P_ty/V`, optimal money (`Q_t ≤ 1`, and
`Q_t < 1 ⇒ M_t = P_ty/V`), the flow budget and the conditional transversality conditions. -/
structure StochMonetaryEq where
  pos : ∀ t ω, 0 < P t ω
  knownP : ∀ t, 𝔼.E t (P t) = P t
  knownB : ∀ t, 𝔼.E t (Bin (t + 1)) = Bin (t + 1)
  knownM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)
  cia : ∀ t ω, P t ω * y / V ≤ Min (t + 1) ω
  rate_nonneg : ∀ t ω, bondPriceS 𝔼 β P t ω ≤ 1
  binds : ∀ t ω, bondPriceS 𝔼 β P t ω < 1 → Min (t + 1) ω = P t ω * y / V
  flow : FlowHolds 𝔼 β P Bin Min s
  tvc : CondTVC 𝔼 β P Bin Min

variable {𝔼 β y V P Bin Min s}

/-- Cochrane (2023), (19.32), p. 450: with the pull-out property,
`Q_t = P_t E_t[β/P_{t+1}]`. -/
theorem bondPriceS_eq (hPO : 𝔼.PullOut) (h : StochMonetaryEq 𝔼 β y V P Bin Min s) (t : ℕ) :
    bondPriceS 𝔼 β P t = P t * 𝔼.E t (fun ω => β / P (t + 1) ω) := by
  unfold bondPriceS
  have e : (fun ω => β * P t ω / P (t + 1) ω) = P t * (fun ω => β / P (t + 1) ω) := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  rw [e, hPO t _ _ (h.knownP t)]

/-- Cochrane (2023), p. 454: with the pull-out property and money known at `t`,
`q_t = M_t E_t[β/M_{t+1}]`. -/
theorem stdBondPrice_eq (hPO : 𝔼.PullOut) (hM : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1))
    (t : ℕ) : stdBondPrice 𝔼 β Min t = Min (t + 1) * 𝔼.E t (fun ω => β / Min (t + 2) ω) := by
  unfold stdBondPrice
  have e : (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) =
      Min (t + 1) * (fun ω => β / Min (t + 2) ω) := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  rw [e, hPO t _ _ (hM t)]

/-- Cochrane (2023), (19.24), p. 449: in equilibrium money is positive, `M_t ≥ P_ty/V > 0`. -/
theorem money_pos (hy : 0 < y) (hV : 0 < V) (h : StochMonetaryEq 𝔼 β y V P Bin Min s)
    (t : ℕ) (ω : Ω) : 0 < Min (t + 1) ω := by
  have := h.pos t ω
  have : 0 < P t ω * y / V := by positivity
  linarith [h.cia t ω]

/-- Cochrane (2023), (19.35), p. 450: the seigniorage term in equilibrium,
`(1 − Q_t)M_t = (1 − Q_t)P_ty/V` (the constraint binds or `Q_t = 1`). -/
theorem seigniorage_eq (h : StochMonetaryEq 𝔼 β y V P Bin Min s) (t : ℕ) (ω : Ω) :
    (1 - bondPriceS 𝔼 β P t ω) * Min (t + 1) ω = (1 - bondPriceS 𝔼 β P t ω) * (P t ω * y / V) := by
  rcases lt_or_eq_of_le (h.rate_nonneg t ω) with hQ | hQ
  · rw [h.binds t ω hQ]
  · rw [hQ, sub_self, zero_mul, zero_mul]

/-- **Cochrane (2023), (19.27)–(19.35), pp. 449–450: the stochastic wealth recursion.** In an
equilibrium (pull-out property, `y, V > 0`),
`β^tx_t = E_t[β^{t+1}x_{t+1}] + β^t(s_t + (1 − Q_t)y/V)` at every date and state.
Compare `CashInAdvance.Stochastic.flow_step_BM`. -/
theorem wealth_recursion (hPO : 𝔼.PullOut) (hV : 0 < V)
    (h : StochMonetaryEq 𝔼 β y V P Bin Min s) (t : ℕ) :
    discWealth β P Bin Min t =
      𝔼.E t (discWealth β P Bin Min (t + 1)) + flowTerm 𝔼 β y V P s t := by
  set K : Ω → ℝ := fun ω => β ^ t * (Bin (t + 1) ω + Min (t + 1) ω) with hK
  set R : Ω → ℝ := fun ω => β / P (t + 1) ω with hR
  have hKk : 𝔼.E t K = K := by
    have e : K = β ^ t • (Bin (t + 1) + Min (t + 1)) := by
      funext ω; simp [hK]
    rw [e, map_smul, map_add, h.knownB t, h.knownM t]
  have e1 : discWealth β P Bin Min (t + 1) = K * R := by
    funext ω
    have := (h.pos (t + 1) ω).ne'
    simp only [discWealth, wealth, hK, hR, Pi.mul_apply, pow_succ]
    field_simp
  have hQ := bondPriceS_eq hPO h t
  rw [e1, hPO t K R hKk]
  funext ω
  have hQω := congrFun hQ ω
  simp only [Pi.mul_apply] at hQω
  have hP := (h.pos t ω).ne'
  have hER : 𝔼.E t R ω = bondPriceS 𝔼 β P t ω / P t ω := by
    rw [hR, hQω]; field_simp
  have hsg := seigniorage_eq h t ω
  have hfl := h.flow t ω
  simp only [discWealth, wealth, flowTerm, Pi.add_apply, Pi.mul_apply, hK, hER]
  rw [hfl]
  have e2 : bondPriceS 𝔼 β P t ω * Bin (t + 1) ω + Min (t + 1) ω + P t ω * s t ω =
      (Bin (t + 1) ω + Min (t + 1) ω) * bondPriceS 𝔼 β P t ω +
        (1 - bondPriceS 𝔼 β P t ω) * Min (t + 1) ω + P t ω * s t ω := by ring
  rw [e2, hsg]
  have hV' := hV.ne'
  field_simp
  ring


/-- Cochrane (2023), (19.24), p. 449, one period ahead: the cash constraint at `t + 1` caps the
price level, so `β/P_{t+1} ≥ (y/V)·β/M_{t+1}` at every state (`β ≥ 0`). -/
theorem cash_bound (hy : 0 < y) (hV : 0 < V) (h : StochMonetaryEq 𝔼 β y V P Bin Min s)
    (hβ : 0 ≤ β) (t : ℕ) (ω : Ω) : (y / V) * (β / Min (t + 2) ω) ≤ β / P (t + 1) ω := by
  have hM2 := money_pos hy hV h (t + 1) ω
  have hP1 := h.pos (t + 1) ω
  have hc := h.cia (t + 1) ω
  rw [show (y / V) * (β / Min (t + 2) ω) = β / (Min (t + 1 + 1) ω * V / y) by
    field_simp]
  refine div_le_div_of_nonneg_left hβ hP1 ?_
  rw [le_div_iff₀ hy]
  calc P (t + 1) ω * y = P (t + 1) ω * y / V * V := by field_simp
    _ ≤ Min (t + 1 + 1) ω * V := mul_le_mul_of_nonneg_right hc hV.le

/-- Cochrane (2023), p. 454: **every equilibrium bond price is at least the standard one,**
`Q_t ≥ q_t`, at every state where `q_t ≤ 1` (the cash constraint caps `P_{t+1}` at
`M_{t+1}V/y`; if `Q_t < 1` the constraint binds at `t`).
Generalises `TidyR5ActiveFiscal.bondPrice_ge`. -/
theorem std_le_bondPrice (hPO : 𝔼.PullOut) (hy : 0 < y) (hV : 0 < V)
    (h : StochMonetaryEq 𝔼 β y V P Bin Min s) (hβ : 0 ≤ β) (t : ℕ) (ω : Ω)
    (hq1 : stdBondPrice 𝔼 β Min t ω ≤ 1) : stdBondPrice 𝔼 β Min t ω ≤ bondPriceS 𝔼 β P t ω := by
  rcases lt_or_eq_of_le (h.rate_nonneg t ω) with hlt | heq
  · have hb := h.binds t ω hlt
    have hR : (fun ω => (y / V) * (β / Min (t + 2) ω)) ≤ fun ω => β / P (t + 1) ω :=
      fun ω' => cash_bound hy hV h hβ t ω'
    have hmono := (𝔼.mono t hR) ω
    have e : (fun ω => (y / V) * (β / Min (t + 2) ω)) =
        (y / V) • (fun ω => β / Min (t + 2) ω) := by
      funext ω'; simp
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul] at hmono
    rw [stdBondPrice_eq hPO h.knownM t, bondPriceS_eq hPO h t]
    simp only [Pi.mul_apply]
    have hPt : P t ω = Min (t + 1) ω * V / y := by
      rw [hb]; field_simp
    rw [hPt]
    have hM1 := money_pos hy hV h t ω
    have hMV : 0 ≤ Min (t + 1) ω * V / y := by positivity
    calc Min (t + 1) ω * 𝔼.E t (fun ω => β / Min (t + 2) ω) ω
        = Min (t + 1) ω * V / y * (y / V * 𝔼.E t (fun ω => β / Min (t + 2) ω) ω) := by
          field_simp
      _ ≤ Min (t + 1) ω * V / y * 𝔼.E t (fun ω => β / P (t + 1) ω) ω :=
          mul_le_mul_of_nonneg_left hmono hMV
  · rw [heq]; exact hq1

/-- Cochrane (2023), (19.35), p. 450: the flow term is known at its date when `s_t` is:
`E_t[β^t(s_t + (1 − Q_t)y/V)] = β^t(s_t + (1 − Q_t)y/V)`. -/
theorem flowTerm_known (hs : ∀ t, 𝔼.E t (s t) = s t) (t : ℕ) :
    𝔼.E t (flowTerm 𝔼 β y V P s t) = flowTerm 𝔼 β y V P s t := by
  have e : flowTerm 𝔼 β y V P s t = (β ^ t) • s t + (β ^ t * y / V) • (fun _ => (1 : ℝ)) -
      (β ^ t * y / V) • bondPriceS 𝔼 β P t := by
    funext ω
    simp only [flowTerm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, map_sub, map_add, map_smul, map_smul, map_smul, hs t, 𝔼.const]
  unfold bondPriceS
  rw [𝔼.E_E_self]

/-- Cochrane (2023), (19.35), p. 450: **the date-0 valuation as a limit.** In equilibrium
(pull-out, surpluses known at their dates), the partial sums
`Σ_{j ≤ T} E_0[β^j(s_j + (1 − Q_j)y/V)]` converge to `x_0 = (B_{−1} + M_{−1})/P_0` at every
state. -/
theorem valuation_limit (hPO : 𝔼.PullOut) (hV : 0 < V)
    (h : StochMonetaryEq 𝔼 β y V P Bin Min s) (hs : ∀ t, 𝔼.E t (s t) = s t) (ω : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), 𝔼.E 0 (flowTerm 𝔼 β y V P s j) ω) atTop
      (𝓝 (wealth P Bin Min 0 ω)) := by
  have htel := CashInAdvance.Stochastic.telescope 𝔼 (wealth_recursion hPO hV h)
    (flowTerm_known hs) 0
  have hpart : ∀ T, ∑ j ∈ Finset.range (T + 1), 𝔼.E 0 (flowTerm 𝔼 β y V P s j) ω =
      wealth P Bin Min 0 ω - 𝔼.E 0 (discWealth β P Bin Min (0 + (T + 1))) ω := by
    intro T
    have h1 := congrFun (htel T) ω
    simp only [Pi.add_apply, Finset.sum_apply, zero_add] at h1
    simp only [zero_add]
    have h0 : discWealth β P Bin Min 0 ω = wealth P Bin Min 0 ω := by
      simp [discWealth]
    rw [← h0, h1]
    ring
  simp_rw [hpart]
  have htv := (tendsto_add_atTop_iff_nat 1).2 (h.tvc 0 ω)
  simpa using htv.const_sub (wealth P Bin Min 0 ω)

/-- **Cochrane (2023), pp. 453–454 under uncertainty: active fiscal policy determines the price
level.** Let `E` have the pull-out property and full support, `β > 0`, `y, V > 0`, surpluses
known at their dates, the standard bond price `q_t ≤ 1` everywhere, initial liabilities
`B_{−1} + M_{−1} ≥ 0`, and the date-0 valuation of the standard path
`E_0Σ_jβ^j(s_j + (1 − q_j)y/V) = (B_{−1} + M_{−1})y/(VM_0)` (as a limit of partial sums). If at
every state `B_{−1} + M_{−1} > 0` or `q_0 < 1`, EVERY equilibrium has the standard price level
`P_t = M_tV/y` and bond price `Q_t = q_t` at every date and state.
Generalises `TidyR5ActiveFiscal.active_fiscal_price_unique`. -/
theorem stoch_price_unique (hPO : 𝔼.PullOut) (hfull : FullSupport 𝔼) (hβ : 0 < β)
    (hy : 0 < y) (hV : 0 < V) (h : StochMonetaryEq 𝔼 β y V P Bin Min s)
    (hs : ∀ t, 𝔼.E t (s t) = s t) (hq1 : ∀ t ω, stdBondPrice 𝔼 β Min t ω ≤ 1)
    (hW : ∀ ω, 0 ≤ Bin 0 ω + Min 0 ω)
    (hcoord : ∀ ω, Tendsto (fun T => ∑ j ∈ Finset.range T, 𝔼.E 0 (stdFlow 𝔼 β y V Min s j) ω)
      atTop (𝓝 ((Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω))))
    (hpin : ∀ ω, 0 < Bin 0 ω + Min 0 ω ∨ stdBondPrice 𝔼 β Min 0 ω < 1) :
    P = stdPrice y V Min ∧ ∀ t, bondPriceS 𝔼 β P t = stdBondPrice 𝔼 β Min t := by
  -- flows of the candidate are below those of the standard path
  have hGH : ∀ j, flowTerm 𝔼 β y V P s j ≤ stdFlow 𝔼 β y V Min s j := by
    intro j ω
    have := std_le_bondPrice hPO hy hV h hβ.le j ω (hq1 j ω)
    simp only [flowTerm, stdFlow]
    have hyV : 0 ≤ y / V := by positivity
    have hk : (1 - bondPriceS 𝔼 β P j ω) * y / V ≤ (1 - stdBondPrice 𝔼 β Min j ω) * y / V := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hyV
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ.le j)
  -- at every state the expected flow gaps vanish and `x_0` is the standard value
  have hstate : ∀ ω, (∀ j, 𝔼.E 0 (stdFlow 𝔼 β y V Min s j - flowTerm 𝔼 β y V P s j) ω = 0) ∧
      wealth P Bin Min 0 ω = (Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω) := by
    intro ω
    set d : ℕ → ℝ := fun j =>
      𝔼.E 0 (stdFlow 𝔼 β y V Min s j - flowTerm 𝔼 β y V P s j) ω with hd
    have hdnn : ∀ j, 0 ≤ d j := by
      intro j
      have hm := 𝔼.mono 0 (sub_nonneg.mpr (hGH j))
      rw [map_zero] at hm
      exact hm ω
    have hdsum : ∀ T, ∑ j ∈ Finset.range T, d j =
        ∑ j ∈ Finset.range T, 𝔼.E 0 (stdFlow 𝔼 β y V Min s j) ω -
          ∑ j ∈ Finset.range T, 𝔼.E 0 (flowTerm 𝔼 β y V P s j) ω := by
      intro T
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hd, map_sub, Pi.sub_apply]
    have hval := (tendsto_add_atTop_iff_nat (f := fun T => ∑ j ∈ Finset.range T,
      𝔼.E 0 (flowTerm 𝔼 β y V P s j) ω) 1).1 (valuation_limit hPO hV h hs ω)
    have hlim : Tendsto (fun T => ∑ j ∈ Finset.range T, d j) atTop
        (𝓝 ((Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω) - wealth P Bin Min 0 ω)) := by
      simp_rw [hdsum]
      exact (hcoord ω).sub hval
    have hHS : HasSum d ((Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω) - wealth P Bin Min 0 ω) :=
      (hasSum_iff_tendsto_nat_of_nonneg hdnn _).2 hlim
    -- `x_0` is at least the standard value since `P_0 ≤ M_0V/y`
    have hx0 : (Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω) ≤ wealth P Bin Min 0 ω := by
      have hP0 := h.pos 0 ω
      have hM1 := money_pos hy hV h 0 ω
      have hc := h.cia 0 ω
      unfold wealth
      rw [div_le_div_iff₀ (by positivity) hP0]
      have : P 0 ω * y ≤ V * Min 1 ω := by
        have e : P 0 ω * y = P 0 ω * y / V * V := by field_simp
        rw [e, mul_comm V]
        exact mul_le_mul_of_nonneg_right hc hV.le
      nlinarith [hW ω]
    have hsum0 : 0 ≤ (Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω) - wealth P Bin Min 0 ω :=
      hHS.nonneg hdnn
    refine ⟨fun j => le_antisymm ?_ (hdnn j), by linarith⟩
    have := le_hasSum hHS j (fun i _ => hdnn i)
    linarith
  -- full support: the bond prices are the standard ones
  have hQq : ∀ t, bondPriceS 𝔼 β P t = stdBondPrice 𝔼 β Min t := by
    intro t
    funext ω
    have hz := hfull 0 (stdFlow 𝔼 β y V Min s t - flowTerm 𝔼 β y V P s t) ω
      (fun ω' => sub_nonneg.mpr (hGH t ω')) ((hstate ω).1 t)
    simp only [Pi.sub_apply, flowTerm, stdFlow] at hz
    have hk : β ^ t * (y / V) * (bondPriceS 𝔼 β P t ω - stdBondPrice 𝔼 β Min t ω) = 0 := by
      rw [← hz]; ring
    have hne : β ^ t * (y / V) ≠ 0 := by positivity
    have := (mul_eq_zero.mp hk).resolve_left hne
    linarith
  -- the initial price level
  have hP0 : ∀ ω, P 0 ω = stdPrice y V Min 0 ω := by
    intro ω
    have hM1 := money_pos hy hV h 0 ω
    have hP := h.pos 0 ω
    simp only [zero_add] at hM1
    simp only [stdPrice, zero_add]
    rcases hpin ω with hpos | hq
    · have hx := (hstate ω).2
      unfold wealth at hx
      rw [div_eq_div_iff hP.ne' (by positivity)] at hx
      have h2 : (Bin 0 ω + Min 0 ω) * (V * Min 1 ω) =
          (Bin 0 ω + Min 0 ω) * (y * P 0 ω) := by linarith
      have h3 := mul_left_cancel₀ hpos.ne' h2
      field_simp
      linarith
    · have hQ : bondPriceS 𝔼 β P 0 ω < 1 := by rw [hQq 0]; exact hq
      have hb := h.binds 0 ω hQ
      simp only [zero_add] at hb
      rw [hb]
      field_simp
  -- forward induction on the price level
  have hPt : ∀ t, P t = stdPrice y V Min t := by
    intro t
    induction t with
    | zero => funext ω; exact hP0 ω
    | succ t ih =>
      funext ω
      set R : Ω → ℝ := fun ω => β / P (t + 1) ω with hR
      set S : Ω → ℝ := fun ω => β / Min (t + 2) ω with hS
      have hZ : 0 ≤ R - (y / V) • S := fun ω' => by
        simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hR, hS]
        linarith [cash_bound hy hV h hβ.le t ω']
      have hE : 𝔼.E t (R - (y / V) • S) ω = 0 := by
        have e1 := congrFun (bondPriceS_eq hPO h t) ω
        have e2 := congrFun (stdBondPrice_eq (β := β) hPO h.knownM t) ω
        rw [hQq t] at e1
        simp only [Pi.mul_apply] at e1 e2
        have hPtω := congrFun ih ω
        simp only [stdPrice] at hPtω
        rw [hPtω] at e1
        have hM1 := money_pos hy hV h t ω
        rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have h4 : Min (t + 1) ω * (V / y * 𝔼.E t R ω - 𝔼.E t S ω) = 0 := by
          rw [hR, hS]
          linear_combination e2 - e1
        have h5 := (mul_eq_zero.mp h4).resolve_left hM1.ne'
        have : 𝔼.E t R ω = y / V * 𝔼.E t S ω := by
          field_simp at h5 ⊢
          linarith
        rw [this]
        ring
      have hz := hfull t _ ω hZ hE
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hR, hS] at hz
      have hP1 := h.pos (t + 1) ω
      have hM2 := money_pos hy hV h (t + 1) ω
      change P (t + 1) ω = Min (t + 1 + 1) ω * V / y
      have hz' : β / P (t + 1) ω = y / V * (β / Min (t + 1 + 1) ω) := by linarith
      field_simp at hz'
      rw [eq_div_iff hy.ne']
      linarith
  exact ⟨funext hPt, hQq⟩

/-- Cochrane (2023), p. 454: along the standard path `P_t = M_tV/y` the bond price
`E_t[βP_t/P_{t+1}]` is `q_t = E_t[βM_t/M_{t+1}]`. -/
theorem bondPriceS_std (hy : 0 < y) (hV : 0 < V) (hM : ∀ t ω, 0 < Min (t + 1) ω) (t : ℕ) :
    bondPriceS 𝔼 β (stdPrice y V Min) t = stdBondPrice 𝔼 β Min t := by
  unfold bondPriceS stdBondPrice
  congr 1
  funext ω
  have := (hM (t + 1) ω).ne'
  have := hy.ne'
  have := hV.ne'
  change β * (Min (t + 1) ω * V / y) / (Min (t + 2) ω * V / y) = β * Min (t + 1) ω / Min (t + 2) ω
  field_simp

/-- Cochrane (2023), (19.35), p. 450: **the date-0 coordination condition holds whenever the
standard equilibrium exists**: `E_0Σ_jβ^j(s_j + (1 − q_j)y/V)` converges to
`(B_{−1} + M_{−1})y/(VM_0)` at every state. -/
theorem coord_of_standard (hPO : 𝔼.PullOut) (hy : 0 < y) (hV : 0 < V) {Bs : ℕ → Ω → ℝ}
    (h : StochMonetaryEq 𝔼 β y V (stdPrice y V Min) Bs Min s) (hs : ∀ t, 𝔼.E t (s t) = s t)
    (ω : Ω) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, 𝔼.E 0 (stdFlow 𝔼 β y V Min s j) ω) atTop
      (𝓝 ((Bs 0 ω + Min 0 ω) * y / (V * Min 1 ω))) := by
  have hQ := bondPriceS_std (β := β) (𝔼 := 𝔼) hy hV (money_pos hy hV h)
  have hf : ∀ j, flowTerm 𝔼 β y V (stdPrice y V Min) s j = stdFlow 𝔼 β y V Min s j := by
    intro j
    funext ω'
    simp only [flowTerm, stdFlow, hQ j]
  have hval := (tendsto_add_atTop_iff_nat (f := fun T => ∑ j ∈ Finset.range T,
    𝔼.E 0 (flowTerm 𝔼 β y V (stdPrice y V Min) s j) ω) 1).1 (valuation_limit hPO hV h hs ω)
  simp_rw [hf] at hval
  have hM1 := money_pos hy hV h 0 ω
  simp only [zero_add] at hM1
  have e : wealth (stdPrice y V Min) Bs Min 0 ω = (Bs 0 ω + Min 0 ω) * y / (V * Min 1 ω) := by
    unfold wealth stdPrice
    have := hy.ne'
    have := hV.ne'
    field_simp
  rw [← e]
  exact hval

/-- **Cochrane (2023), pp. 453–454 under uncertainty, existence form: if the standard
equilibrium exists, it is the only equilibrium.** With the pull-out property, full support,
`β > 0`, `y, V > 0`, surpluses known at their dates, `B_{−1} + M_{−1} ≥ 0`, and at every state
`B_{−1} + M_{−1} > 0` or `q_0 < 1`: any equilibrium `(P, B)` with the same money, surpluses and
initial bonds as a standard equilibrium `(M V/y, B^s)` coincides with it (prices AND bonds).
Generalises `TidyR5ActiveFiscal.active_fiscal_price_unique`. -/
theorem unique_of_standard (hPO : 𝔼.PullOut) (hfull : FullSupport 𝔼) (hβ : 0 < β)
    (hy : 0 < y) (hV : 0 < V) {Bs : ℕ → Ω → ℝ}
    (h : StochMonetaryEq 𝔼 β y V P Bin Min s)
    (hstd : StochMonetaryEq 𝔼 β y V (stdPrice y V Min) Bs Min s)
    (hs : ∀ t, 𝔼.E t (s t) = s t) (hB0 : Bin 0 = Bs 0) (hW : ∀ ω, 0 ≤ Bin 0 ω + Min 0 ω)
    (hpin : ∀ ω, 0 < Bin 0 ω + Min 0 ω ∨ stdBondPrice 𝔼 β Min 0 ω < 1) :
    P = stdPrice y V Min ∧ Bin = Bs := by
  have hQs := bondPriceS_std (β := β) (𝔼 := 𝔼) hy hV (money_pos hy hV hstd)
  have hq1 : ∀ t ω, stdBondPrice 𝔼 β Min t ω ≤ 1 := fun t ω => by
    rw [← hQs t]; exact hstd.rate_nonneg t ω
  have hcoord : ∀ ω, Tendsto (fun T => ∑ j ∈ Finset.range T,
      𝔼.E 0 (stdFlow 𝔼 β y V Min s j) ω) atTop
      (𝓝 ((Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω))) := fun ω => by
    rw [hB0]; exact coord_of_standard hPO hy hV hstd hs ω
  obtain ⟨hP, hQ⟩ := stoch_price_unique hPO hfull hβ hy hV h hs hq1 hW hcoord hpin
  refine ⟨hP, ?_⟩
  funext t
  induction t with
  | zero => exact hB0
  | succ t ih =>
    funext ω
    have f1 := h.flow t ω
    have f2 := hstd.flow t ω
    rw [hQ t] at f1
    rw [hQs t] at f2
    rw [hP] at f1
    rw [ih] at f1
    have hqpos : stdBondPrice 𝔼 β Min t ω ≠ 0 := by
      intro h0
      have hX : 0 ≤ fun ω => β * Min (t + 1) ω / Min (t + 2) ω := fun ω' => by
        have := money_pos hy hV hstd t ω'
        have := money_pos hy hV hstd (t + 1) ω'
        simp only [Pi.zero_apply]
        positivity
      have hz := hfull t _ ω hX h0
      have := money_pos hy hV hstd t ω
      have := money_pos hy hV hstd (t + 1) ω
      have : 0 < β * Min (t + 1) ω / Min (t + 1 + 1) ω := by positivity
      linarith
    exact mul_left_cancel₀ hqpos (by linarith)

/-! ## Instances: perfect foresight and finite trees -/

/-- Cochrane (2023), p. 450: perfect foresight has full support. -/
theorem perfectForesight_fullSupport : FullSupport perfectForesight :=
  fun _ _ _ _ h => h

/-- Cochrane (2023), p. 450 (genuine uncertainty): every finite event tree with strictly positive
state probabilities has full support. -/
theorem finiteTree_fullSupport {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : FullSupport T.toExpectationSystem := by
  classical
  intro t X ω hX hE
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hE
  unfold ExpectationsFiniteTree.FiniteTree.condE at hE
  have hm := T.mass_pos t ω
  have hnum : T.num t X ω = 0 := by
    rcases div_eq_zero_iff.mp hE with h | h
    · exact h
    · exact absurd h hm.ne'
  unfold ExpectationsFiniteTree.FiniteTree.num at hnum
  have hnn : ∀ ω' ∈ Finset.univ,
      (0 : ℝ) ≤ if T.info t ω' ω then T.prob ω' * X ω' else 0 := fun ω' _ => by
    split_ifs
    · exact mul_nonneg (T.prob_pos ω').le (hX ω')
    · exact le_rfl
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnum ω (Finset.mem_univ _)
  simp only [(T.info t).refl' ω, ↓reduceIte] at hterm
  exact (mul_eq_zero.mp hterm).resolve_left (T.prob_pos ω).ne'

/-- Cochrane (2023), pp. 453–454 on a finite event tree: the standard equilibrium, when it
exists, is the only equilibrium (`unique_of_standard` with
`ExpectationsFiniteTree.finiteTree_pullOut` and `finiteTree_fullSupport`). -/
theorem finiteTree_unique_of_standard {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {P' Bin' Min' s' Bs : ℕ → Ω' → ℝ} (hβ : 0 < β)
    (hy : 0 < y) (hV : 0 < V) (h : StochMonetaryEq T.toExpectationSystem β y V P' Bin' Min' s')
    (hstd : StochMonetaryEq T.toExpectationSystem β y V (stdPrice y V Min') Bs Min' s')
    (hs : ∀ t, T.toExpectationSystem.E t (s' t) = s' t) (hB0 : Bin' 0 = Bs 0)
    (hW : ∀ ω, 0 ≤ Bin' 0 ω + Min' 0 ω)
    (hpin : ∀ ω, 0 < Bin' 0 ω + Min' 0 ω ∨ stdBondPrice T.toExpectationSystem β Min' 0 ω < 1) :
    P' = stdPrice y V Min' ∧ Bin' = Bs :=
  unique_of_standard (ExpectationsFiniteTree.finiteTree_pullOut T) (finiteTree_fullSupport T)
    hβ hy hV h hstd hs hB0 hW hpin

/-- Cochrane (2023), §19.5.5, pp. 449–454: a perfect-foresight monetary equilibrium
(`CashInAdvance.PF.MonetaryEq`) is a `StochMonetaryEq` of the perfect-foresight expectation
system. -/
theorem ofPF {P' Bin' Min' s' : ℕ → ℝ} (h : CashInAdvance.PF.MonetaryEq β y V P' Bin' Min' s') :
    StochMonetaryEq perfectForesight β y V (fun t _ => P' t) (fun t _ => Bin' t)
      (fun t _ => Min' t) (fun t _ => s' t) where
  pos := fun t _ => h.pos t
  knownP := fun _ => rfl
  knownB := fun _ => rfl
  knownM := fun _ => rfl
  cia := fun t _ => h.cia t
  rate_nonneg := fun t _ => h.rate_nonneg t
  binds := fun t _ hlt => h.binds t hlt
  flow := fun t _ => h.flow t
  tvc := fun t _ => by
    have := (tendsto_add_atTop_iff_nat t).2 h.tvc
    refine this.congr fun T => ?_
    change β ^ (T + t) * (Bin' (T + t) + Min' (T + t)) / P' (T + t) =
      β ^ (t + T) * ((Bin' (t + T) + Min' (t + T)) / P' (t + T))
    rw [add_comm T t]
    ring

/-- **Cochrane (2023), pp. 453–454: the proviso `B_{−1} + M_{−1} ≥ 0` cannot be dropped under
uncertainty either.** The perfect-foresight counterexample of
`TidyR5ActiveFiscal.active_fiscal_two_equilibria` gives, in this framework, two equilibria with
the same money, surplus and initial liabilities `M_{−1}(bV/y + 1) < 0`, one of them the standard
equilibrium, with different initial price levels. -/
theorem pf_two_equilibria (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) (hA0 : b * V + y < 0) :
    ∃ P1 B1 B2 : ℕ → Unit → ℝ,
      StochMonetaryEq perfectForesight β y V P1 B1 (fun t _ => Mm1 * (1 + μ) ^ t)
        (fun _ _ => (b * (1 - β) - μ * y / V) / (1 + μ)) ∧
      StochMonetaryEq perfectForesight β y V (stdPrice y V (fun t _ => Mm1 * (1 + μ) ^ t)) B2
        (fun t _ => Mm1 * (1 + μ) ^ t) (fun _ _ => (b * (1 - β) - μ * y / V) / (1 + μ)) ∧
      B1 0 = B2 0 ∧ P1 0 () < stdPrice y V (fun t _ => Mm1 * (1 + μ) ^ t) 0 () := by
  obtain ⟨P', Bin', h1, hA, hlt⟩ :=
    TidyR5ActiveFiscal.active_fiscal_two_equilibria hβ0 hβ1 hy hV hμ hM hA0
  have h2 := CashInAdvance.PF.usual_equilibrium (b := b) hβ0 hβ1 hy hV hμ.le hM
  have hstdP : stdPrice y V (fun t _ => Mm1 * (1 + μ) ^ t) =
      fun t (_ : Unit) => Mm1 * V / y * (1 + μ) ^ (t + 1) := by
    funext t _
    simp only [stdPrice]
    ring
  refine ⟨fun t _ => P' t, fun t _ => Bin' t, fun t _ => b * (Mm1 * (1 + μ) ^ t * V / y),
    ofPF h1, ?_, ?_, ?_⟩
  · rw [hstdP]; exact ofPF h2
  · funext _
    simp only [pow_zero, mul_one] at hA ⊢
    have := hy.ne'
    field_simp at hA ⊢
    linarith
  · rw [hstdP]; exact hlt

/-- Cochrane (2023), pp. 453–454 (the zero-liability corner): with money shrinking at the rate
`β` (`M_t = β^{t}M̄`, so the standard nominal rate is zero, `q_t = 1`), zero surpluses and zero
initial liabilities (`B_t = −M_{t−1}`), every price path `P_t = β^tp` with
`0 < p ≤ βM̄V/y` is a perfect-foresight equilibrium. -/
theorem corner_equilibrium (hβ0 : 0 < β) (hy : 0 < y) (hV : 0 < V) {Mbar p : ℝ}
    (hp : 0 < p) (hpb : p ≤ β * Mbar * V / y) :
    StochMonetaryEq perfectForesight β y V (fun t _ => β ^ t * p)
      (fun t _ => -(β ^ t * Mbar)) (fun t _ => β ^ t * Mbar) (fun _ _ => 0) := by
  have hQ : ∀ t, bondPriceS perfectForesight β (fun t _ => β ^ t * p) t = fun _ => 1 := by
    intro t
    funext ω
    change β * (β ^ t * p) / (β ^ (t + 1) * p) = 1
    rw [pow_succ]
    field_simp
  refine ⟨fun t _ => by positivity, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun t _ => ?_,
    fun t ω => by rw [hQ t], fun t ω h => by rw [hQ t] at h; exact absurd h (lt_irrefl _),
    fun t ω => by rw [hQ t]; ring, fun t ω => ?_⟩
  · have h1 : p * y / V ≤ β * Mbar := by
      rw [div_le_iff₀ hV]
      have := (le_div_iff₀ hy).1 hpb
      linarith
    have := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ0.le t)
    rw [pow_succ]
    calc β ^ t * p * y / V = β ^ t * (p * y / V) := by ring
      _ ≤ β ^ t * (β * Mbar) := this
      _ = β ^ t * β * Mbar := by ring
  · have : (fun T => perfectForesight.E t (discWealth β (fun t _ => β ^ t * p)
        (fun t _ => -(β ^ t * Mbar)) (fun t _ => β ^ t * Mbar) (t + T)) ω) = fun _ => 0 := by
      funext T
      change β ^ (t + T) * ((-(β ^ (t + T) * Mbar) + β ^ (t + T) * Mbar) / (β ^ (t + T) * p)) = 0
      simp
    rw [this]
    exact tendsto_const_nhds

/-- **Cochrane (2023), pp. 453–454: the condition "`B_{−1} + M_{−1} > 0` or `q_0 < 1`" of
`stoch_price_unique` cannot be dropped (counterexample).** With zero initial liabilities,
money shrinking at the rate `β` (so `q_t = 1`) and zero surpluses, the standard path and the
path with half its price level are both equilibria with the same money, surpluses and initial
bonds; since the standard path is an equilibrium, every hypothesis of `unique_of_standard` except
the pinning condition holds (`B_{−1} + M_{−1} = 0`, `q_0 = 1`). -/
theorem pin_needed (hβ0 : 0 < β) (hy : 0 < y) (hV : 0 < V) {Mbar : ℝ}
    (hM : 0 < Mbar) :
    StochMonetaryEq perfectForesight β y V (stdPrice y V fun t _ => β ^ t * Mbar)
        (fun t _ => -(β ^ t * Mbar)) (fun t _ => β ^ t * Mbar) (fun _ _ => 0) ∧
      StochMonetaryEq perfectForesight β y V (fun t _ => β ^ t * (β * Mbar * V / y / 2))
        (fun t _ => -(β ^ t * Mbar)) (fun t _ => β ^ t * Mbar) (fun _ _ => 0) ∧
      stdBondPrice perfectForesight β (fun t _ => β ^ t * Mbar) 0 () = 1 ∧
      β ^ 0 * (β * Mbar * V / y / 2) ≠ stdPrice y V (fun t _ => β ^ t * Mbar) 0 () := by
  have hb : β * Mbar * V / y > 0 := by positivity
  have hstd : stdPrice y V (fun t (_ : Unit) => β ^ t * Mbar) =
      fun t _ => β ^ t * (β * Mbar * V / y) := by
    funext t _
    simp only [stdPrice, pow_succ]
    ring
  refine ⟨?_, corner_equilibrium hβ0 hy hV (by positivity) (by linarith), ?_, ?_⟩
  · rw [hstd]; exact corner_equilibrium hβ0 hy hV hb le_rfl
  · change β * (β ^ (0 + 1) * Mbar) / (β ^ (0 + 2) * Mbar) = 1
    field_simp
    ring
  · rw [hstd]
    simp only [pow_zero, one_mul]
    linarith

/-! ## Under uncertainty the standard equilibrium can fail to exist -/

/-- Cochrane (2023), p. 454 (an uncoordinated active surplus): `s_0 = s̄` and
`s_t = s̄ + σ·1{first coin heads}` for `t ≥ 1`, a permanent surplus shock revealed at date 1. -/
noncomputable def shockSurplus (sbar σ : ℝ) (t : ℕ) (ω : Bool × Bool) : ℝ :=
  if t = 0 then sbar else sbar + σ * ExpectationsFiniteTree.firstHeads ω

/-- Cochrane (2023), p. 454 (coin-flip tree): the first flip is known from date 1 on. -/
theorem firstHeads_known {t : ℕ} (ht : 1 ≤ t) :
    ExpectationsFiniteTree.coinSystem.E t ExpectationsFiniteTree.firstHeads =
      ExpectationsFiniteTree.firstHeads := by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => ?_
  change Setoid.ker (ExpectationsFiniteTree.coinObs t) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [ExpectationsFiniteTree.coinObs, Prod.mk.injEq, ht, ↓reduceIte] at h
  simp [ExpectationsFiniteTree.firstHeads, h.1]

/-- Cochrane (2023), p. 454 (coin-flip tree): nothing is known at date 0, so a variable known at
date 0 takes the same value in every state. -/
theorem coin_known0_const {x : Bool × Bool → ℝ}
    (hx : ExpectationsFiniteTree.coinSystem.E 0 x = x) (ω ω' : Bool × Bool) : x ω = x ω' := by
  rw [← hx, ExpectationsFiniteTree.coinSystem,
    ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_congr x ?_
  change Setoid.ker (ExpectationsFiniteTree.coinObs 0) ω ω'
  rw [Setoid.ker_def]
  simp [ExpectationsFiniteTree.coinObs]

/-- **Cochrane (2023), p. 454 — under uncertainty the standard equilibrium need not exist
(counterexample).** On the coin-flip tree with constant money `M̄ > 0`, `0 < β < 1`, `y, V > 0`
and the surplus `shockSurplus s̄ σ` with `σ ≠ 0`, there is no equilibrium with the standard price
level `P_t = M̄V/y`: bonds `B_0` are chosen at date 0, so real liabilities at date 1 are the same
in every state, while the date-1 valuation equation makes them depend on the surplus shock. So
the hypothesis of `unique_of_standard` (equivalently the coordination condition) is a genuine
restriction linking surpluses and money. -/
theorem coin_no_standard_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {Mbar sbar σ : ℝ} (hM : 0 < Mbar) (hσ : σ ≠ 0) :
    ¬ ∃ Bs : ℕ → Bool × Bool → ℝ, StochMonetaryEq ExpectationsFiniteTree.coinSystem β y V
      (stdPrice y V (fun _ _ => Mbar)) Bs (fun _ _ => Mbar) (shockSurplus sbar σ) := by
  rintro ⟨Bs, h⟩
  set 𝔼c := ExpectationsFiniteTree.coinSystem with h𝔼c
  have hPO : 𝔼c.PullOut := ExpectationsFiniteTree.finiteTree_pullOut _
  have hs : ∀ t, 𝔼c.E t (shockSurplus sbar σ t) = shockSurplus sbar σ t := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have e : shockSurplus sbar σ 0 = fun _ => sbar := by
        funext ω; simp [shockSurplus]
      rw [e, 𝔼c.const]
    · have e : shockSurplus sbar σ t =
          (fun _ => sbar) + σ • ExpectationsFiniteTree.firstHeads := by
        funext ω; simp [shockSurplus, ht.ne']
      rw [e, map_add, map_smul, 𝔼c.const, firstHeads_known ht]
  -- the bond price is `β` at every date
  have hQ : ∀ t, bondPriceS 𝔼c β (stdPrice y V (fun _ _ => Mbar)) t = fun _ => β := by
    intro t
    rw [bondPriceS_std hy hV (fun _ _ => hM)]
    unfold stdBondPrice
    have e : (fun ω : Bool × Bool => β * Mbar / Mbar) = fun _ => β := by
      funext ω; field_simp
    rw [e, 𝔼c.const]
  -- the flows from date 1 on
  set c : Bool × Bool → ℝ := fun ω =>
    sbar + σ * ExpectationsFiniteTree.firstHeads ω + (1 - β) * y / V with hc
  have hflow1 : ∀ j, flowTerm 𝔼c β y V (stdPrice y V (fun _ _ => Mbar)) (shockSurplus sbar σ)
      (1 + j) = fun ω => β ^ (1 + j) * c ω := by
    intro j
    funext ω
    simp only [flowTerm, hQ, shockSurplus, hc, show 1 + j ≠ 0 by omega, ↓reduceIte]
  have hcknown : 𝔼c.E 1 c = c := by
    have e : c = (fun _ => sbar + (1 - β) * y / V) + σ • ExpectationsFiniteTree.firstHeads := by
      funext ω; simp only [hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, map_add, map_smul, 𝔼c.const, firstHeads_known le_rfl]
  have hE1 : ∀ j ω, 𝔼c.E 1 (flowTerm 𝔼c β y V (stdPrice y V (fun _ _ => Mbar))
      (shockSurplus sbar σ) (1 + j)) ω = β ^ (1 + j) * c ω := by
    intro j ω
    rw [hflow1 j]
    have e : (fun ω => β ^ (1 + j) * c ω) = β ^ (1 + j) • c := by
      funext ω; simp
    rw [e, map_smul, hcknown]
    simp
  -- the date-1 valuation equation
  have hval : ∀ ω, discWealth β (stdPrice y V (fun _ _ => Mbar)) Bs (fun _ _ => Mbar) 1 ω =
      β * c ω / (1 - β) := by
    intro ω
    have hgeo : Summable fun j : ℕ => β ^ (1 + j) * c ω :=
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left (β * c ω)).congr fun j => by
        rw [pow_add]; ring
    have key := (CashInAdvance.Stochastic.pv_iff_tvc 𝔼c (wealth_recursion hPO hV h)
      (flowTerm_known hs) 1 ω (by simp_rw [hE1]; exact hgeo)).1 (h.tvc 1 ω)
    simp_rw [hE1] at key
    rw [key]
    have e : (fun j : ℕ => β ^ (1 + j) * c ω) = fun j => β * c ω * β ^ j := by
      funext j; rw [pow_add]; ring
    rw [e, tsum_mul_left, tsum_geometric_of_lt_one hβ0.le hβ1]
    ring
  -- but real liabilities at date 1 are the same in every state
  have hB1 := coin_known0_const (h.knownB 0)
  have hv1 := hval (true, true)
  have hv2 := hval (false, true)
  have hsame : discWealth β (stdPrice y V (fun _ _ => Mbar)) Bs (fun _ _ => Mbar) 1 (true, true) =
      discWealth β (stdPrice y V (fun _ _ => Mbar)) Bs (fun _ _ => Mbar) 1 (false, true) := by
    simp only [discWealth, wealth, stdPrice, hB1 (true, true) (false, true)]
  rw [hv1, hv2] at hsame
  have h1β : (1 - β) ≠ 0 := by linarith
  have : σ * V = 0 := by
    simp only [hc, ExpectationsFiniteTree.firstHeads, ↓reduceIte, Bool.false_eq_true] at hsame
    field_simp at hsame
    linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hσ h0
  · exact hV.ne' h0

end Cochrane.Monetarism.TidyR6ActiveFiscalTree
