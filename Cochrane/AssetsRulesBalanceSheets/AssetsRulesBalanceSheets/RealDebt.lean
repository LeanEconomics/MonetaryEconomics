/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.PresentValue

/-!
# Indexed debt, foreign debt, pegs and the gold standard

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.1 (pp. 239–240) and §8.2
(pp. 241–245).

Timing convention used throughout this project: a debt process `b : ℕ → Ω → ℝ` is indexed by the
date at which it comes due, so `b t` is Cochrane's `b_{t−1}` (issued at `t − 1`, paid at `t`) and
`b (t + 1)` is Cochrane's `b_t`, chosen at date `t`. The same applies to nominal debt `B`.

## Main results

* The general valuation machinery (`epv`, `pv`, `TVC`, `flow_tvc_iff_pv`, `real_iterate`,
  `real_flow_tvc_iff`, ...) lives in `PresentValue`, shared with the Chapter 9 and 10 modules.
* §8.1 indexed debt: `indexedPrice_eq` (the bracket in the flow is `β P_t`),
  `indexed_real_value` (the real value at `t − 1` of `b_{t−1}` is `β b_{t−1}`),
  `indexedFlow_iff` (`b_{t−1} = s_t + β b_t` state by state), `indexed_valuation_iff` ((8.1),
  pathwise, with the TVC made explicit), `indexed_valuation_tsum`, `indexed_pv_news_zero` (the
  surplus present value is predetermined: (8.1) is a restriction on surpluses),
  `indexedFlow_price_free` and `cashFlow_iff` (with only real debt the price level is not
  determined), `surplus_rule_determines` (surpluses `s(P)` can determine `P`).
* p. 240 mixed timing: `nominalIssue_flow_iff`, `realOutstanding_price_free` (real debt
  outstanding, nominal issued: `P_t` undetermined), `nominalOutstanding_price_unique` (nominal
  outstanding, real issued: `P_t = B_{t−1}/(s_t + β b_t)`).
* (8.2) foreign-currency debt: `nominalFlow_iff_solves`, `nominal_valuation_iff`,
  `haircut_of_fixed_price` (with the price level fixed, `B D/P̄ = V` forces the haircut
  `D = P̄ V/B`), `foreign_default_required`.
* §8.2 reserves and pegs: `reserves_price_unique`, `reserves_through_sum`,
  `gold_deflation_raises_pv`, `gold_devaluation`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.RealDebt

open Filter Topology PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §8.1 Indexed debt -/

/-- Cochrane (2023), p. 239: the nominal price at `t` of a one-period indexed bond paying
`P_{t+1}` dollars, the bracket `E_t[β (P_t/P_{t+1}) × P_{t+1}]` of the indexed-debt flow. -/
noncomputable def indexedPrice (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => β * (P t ω / P (t + 1) ω) * P (t + 1) ω)

/-- Cochrane (2023), p. 239: with an adapted, nowhere-zero price level the nominal price of an
indexed bond is `β P_t`. -/
theorem indexedPrice_eq {β : ℝ} {P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) : indexedPrice 𝔼 β P t = β • P t := by
  have h : (fun ω => β * (P t ω / P (t + 1) ω) * P (t + 1) ω) = β • P t := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, div_mul_cancel₀ _ (hP (t + 1) ω)]
  rw [indexedPrice, h, map_smul, hPa t]

/-- Cochrane (2023), p. 239 (timing remark): the real price of the indexed bond is `β`, so the
real value at `t − 1` of `b_{t−1}` is `β b_{t−1}`. -/
theorem indexed_real_value {β : ℝ} {P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (b : Ω → ℝ) (t : ℕ) (ω : Ω) :
    indexedPrice 𝔼 β P t ω / P t ω * b ω = β * b ω := by
  rw [indexedPrice_eq 𝔼 hPa hP t, Pi.smul_apply, smul_eq_mul, mul_div_assoc,
    div_self (hP t ω), mul_one]

/-- Cochrane (2023), p. 239: the nominal flow condition with only indexed debt,
`b_{t−1} P_t = P_t s_t + E_t[β (P_t/P_{t+1}) P_{t+1}] b_t`. -/
def IndexedFlow (β : ℝ) (b s P : ℕ → Ω → ℝ) : Prop :=
  ∀ t, b t * P t = P t * s t + indexedPrice 𝔼 β P t * b (t + 1)

/-- Cochrane (2023), p. 239: the indexed-debt flow is equivalent, for any adapted nowhere-zero
price level, to the real flow `b_{t−1} = s_t + β b_t` state by state. -/
theorem indexedFlow_iff {β : ℝ} {b s P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) :
    IndexedFlow 𝔼 β b s P ↔ ∀ t ω, b t ω = s t ω + β * b (t + 1) ω := by
  simp only [IndexedFlow, indexedPrice_eq 𝔼 hPa hP, funext_iff, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h t ω
    have h1 : P t ω * b t ω = P t ω * (s t ω + β * b (t + 1) ω) := by
      linarith [h t ω]
    exact mul_left_cancel₀ (hP t ω) h1
  · intro h t ω
    rw [h t ω]
    ring

/-- Cochrane (2023), p. 239: with only real debt outstanding and surpluses independent of the
price level, the price level disappears: the flow holds for one adapted nowhere-zero price path
iff it holds for any other. -/
theorem indexedFlow_price_free {β : ℝ} {b s P P' : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hPa' : 𝔼.Adapted P') (hP' : ∀ t ω, P' t ω ≠ 0) :
    IndexedFlow 𝔼 β b s P ↔ IndexedFlow 𝔼 β b s P' := by
  rw [indexedFlow_iff 𝔼 hPa hP, indexedFlow_iff 𝔼 hPa' hP']

/-- Cochrane (2023), eq. (8.1), p. 239 (pathwise, TVC explicit): the indexed-debt flow plus
`βᵀ b_{t+T−1} → 0` in every state is equivalent to `b_{t−1} = ∑_{j ≥ 0} βʲ s_{t+j}` (as a
convergent series) in every state. -/
theorem indexed_valuation_iff {β : ℝ} {b s P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) :
    (IndexedFlow 𝔼 β b s P ∧
      ∀ t ω, Tendsto (fun T : ℕ => β ^ T * b (t + T) ω) atTop (𝓝 0)) ↔
    ∀ t ω, Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j) ω) atTop (𝓝 (b t ω)) := by
  rw [indexedFlow_iff 𝔼 hPa hP]
  constructor
  · rintro ⟨h, htvc⟩ t ω
    exact (real_flow_tvc_iff β (fun t => b t ω) (fun t => s t ω)).mp
      ⟨fun t => h t ω, fun t => htvc t ω⟩ t
  · intro h
    refine ⟨fun t ω => ?_, fun t ω => ?_⟩
    · exact ((real_flow_tvc_iff β (fun t => b t ω) (fun t => s t ω)).mpr
        (fun t => h t ω)).1 t
    · exact ((real_flow_tvc_iff β (fun t => b t ω) (fun t => s t ω)).mpr
        (fun t => h t ω)).2 t

/-- Cochrane (2023), eq. (8.1), p. 239: when the discounted surpluses are summable in every
state, the flow and the TVC give `b_{t−1} = ∑' βʲ s_{t+j}` (a genuine `tsum`). -/
theorem indexed_valuation_tsum {β : ℝ} {b s P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hflow : IndexedFlow 𝔼 β b s P)
    (htvc : ∀ t ω, Tendsto (fun T : ℕ => β ^ T * b (t + T) ω) atTop (𝓝 0))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * s (t + j) ω)) : ∀ t, b t = epv β s t := by
  intro t
  funext ω
  exact tendsto_nhds_unique ((indexed_valuation_iff 𝔼 hPa hP).mp ⟨hflow, htvc⟩ t ω)
    (hsum t ω).hasSum.tendsto_sum_nat

/-- Cochrane (2023), p. 239 ("a restriction on surpluses", `a(ρ) = 0`): if indexed debt is
valued by (8.1) and `b_t` is chosen at `t` (known at `t`), the ex post present value of
surpluses from `t + 1` on is already known at `t`: it has no news,
`E_{t+1} ∑ βʲ s_{t+1+j} − E_t ∑ βʲ s_{t+1+j} = 0`. -/
theorem indexed_pv_news_zero {β : ℝ} {b s : ℕ → Ω → ℝ} (hb : ∀ t, b t = epv β s t)
    (hpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) (t : ℕ) :
    𝔼.E (t + 1) (epv β s (t + 1)) - 𝔼.E t (epv β s (t + 1)) = 0 := by
  rw [← hb (t + 1), hpre t, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hpre t), sub_self]

/-- Cochrane (2023), p. 240: the cash version of the flow, `P_t b_{t−1} = P_t s_t + P_t β b_t`,
holds for a nowhere-zero price path iff the real flow holds — for any price level if surpluses
obey (8.1), for none otherwise. -/
theorem cashFlow_iff {β : ℝ} {b s P : ℕ → ℝ} (hP : ∀ t, P t ≠ 0) :
    (∀ t, P t * b t = P t * s t + P t * (β * b (t + 1))) ↔
      ∀ t, b t = s t + β * b (t + 1) := by
  constructor
  · intro h t
    exact mul_left_cancel₀ (hP t) (by rw [h t]; ring)
  · intro h t
    rw [h t]
    ring

/-- Cochrane (2023), p. 239: surpluses that respond to the price level, `s_t = σ(P_t)` with
`σ` injective, can determine the price level even with only real debt: given `b_{t−1}` and
`b_t` there is at most one price level. -/
theorem surplus_rule_determines {β : ℝ} {σ : ℝ → ℝ} (hσ : Function.Injective σ)
    {b b' p p' : ℝ} (hp : b = σ p + β * b') (hp' : b = σ p' + β * b') : p = p' :=
  hσ (by linarith)

/-! ### p. 240: which kind of debt comes due -/

/-- Cochrane (2023), p. 240: real debt `b` outstanding and nominal debt `B_t` issued at price
`Q_t = β E_t(P_t/P_{t+1})`. With the pull-out property and a nowhere-zero date-`t` price `p` known
at `t`, the flow `p b = p s + Q_t B_t` is equivalent to `b = s + β E_t(1/P_{t+1}) B_t`, which
does not involve `p`. -/
theorem nominalIssue_flow_iff (hPO : 𝔼.PullOut) {t : ℕ} {β : ℝ} {b s p Pn Bn : Ω → ℝ}
    (hp : 𝔼.E t p = p) (hp0 : ∀ ω, p ω ≠ 0) :
    p * b = p * s + 𝔼.E t (β • (p / Pn)) * Bn ↔ b = s + β • (𝔼.E t Pn⁻¹ * Bn) := by
  have hE : 𝔼.E t (β • (p / Pn)) = β • (p * 𝔼.E t Pn⁻¹) := by
    rw [map_smul, div_eq_mul_inv, hPO t p Pn⁻¹ hp]
  rw [hE]
  simp only [funext_iff, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h ω
    exact mul_left_cancel₀ (hp0 ω) (by rw [h ω]; ring)
  · intro h ω
    rw [h ω]
    ring

/-- Cochrane (2023), p. 240: if real debt is outstanding but the government issues nominal
debt, the date-`t` price level is still undetermined: the flow holds at one nowhere-zero known
price iff it holds at any other. -/
theorem realOutstanding_price_free (hPO : 𝔼.PullOut) {t : ℕ} {β : ℝ} {b s p p' Pn Bn : Ω → ℝ}
    (hp : 𝔼.E t p = p) (hp0 : ∀ ω, p ω ≠ 0) (hp' : 𝔼.E t p' = p') (hp0' : ∀ ω, p' ω ≠ 0) :
    p * b = p * s + 𝔼.E t (β • (p / Pn)) * Bn ↔
      p' * b = p' * s + 𝔼.E t (β • (p' / Pn)) * Bn := by
  rw [nominalIssue_flow_iff 𝔼 hPO hp hp0, nominalIssue_flow_iff 𝔼 hPO hp' hp0']

/-- Cochrane (2023), p. 240: if nominal debt `B_{t−1} > 0` is outstanding and the government
issues real debt `b_t` (nominal price `β P_t`), the flow `B_{t−1} = P_t s_t + β P_t b_t`
determines the price level uniquely, `P_t = B_{t−1}/(s_t + β b_t)`, when `s_t + β b_t > 0`. -/
theorem nominalOutstanding_price_unique {β B s b : ℝ} (hB : 0 < B) (hv : 0 < s + β * b) :
    ∃! P : ℝ, 0 < P ∧ B = P * s + β * P * b := by
  refine ⟨B / (s + β * b), ⟨div_pos hB hv, ?_⟩, ?_⟩
  · field_simp
  · rintro P ⟨_, hP⟩
    rw [eq_div_iff hv.ne']
    rw [hP]
    ring

/-! ### (8.2) Foreign-currency debt -/

/-- Cochrane (2023), eq. (8.2), p. 240: the flow condition for nominal debt (in domestic or, for
(8.2), foreign currency) at bond price `Q_t = β E_t(P_t/P_{t+1})`,
`B_{t−1} = P_t s_t + Q_t B_t`. -/
def NominalFlow (β : ℝ) (B P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, B t = P t * s t + 𝔼.E t (β • (P t / P (t + 1))) * B (t + 1)

/-- Cochrane (2023), eq. (8.2), p. 240: with the pull-out property, an adapted nowhere-zero
price level and debt `B_t` chosen at `t`, the nominal flow is the real recursion
`B_{t−1}/P_t = s_t + β E_t(B_t/P_{t+1})`. -/
theorem nominalFlow_iff_solves (hPO : 𝔼.PullOut) {β : ℝ} {B P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    NominalFlow 𝔼 β B P s ↔ ForwardSolution.Solves 𝔼 β s (fun t => B t / P t) := by
  have hE1 : ∀ t, 𝔼.E t (β • (P t / P (t + 1))) = β • (P t * 𝔼.E t (P (t + 1))⁻¹) := by
    intro t
    rw [map_smul, div_eq_mul_inv, hPO t (P t) (P (t + 1))⁻¹ (hPa t)]
  have hE2 : ∀ t, 𝔼.E t (B (t + 1) / P (t + 1)) = B (t + 1) * 𝔼.E t (P (t + 1))⁻¹ := by
    intro t
    rw [div_eq_mul_inv, hPO t (B (t + 1)) (P (t + 1))⁻¹ (hBpre t)]
  simp only [NominalFlow, ForwardSolution.Solves, hE1, hE2, funext_iff, Pi.add_apply,
    Pi.mul_apply, Pi.smul_apply, Pi.div_apply, smul_eq_mul]
  constructor
  · intro h t ω
    rw [div_eq_iff (hP t ω), h t ω]
    ring
  · intro h t ω
    have h1 := h t ω
    rw [div_eq_iff (hP t ω)] at h1
    rw [h1]
    ring

/-- Cochrane (2023), eq. (8.2), p. 240: for bounded adapted surpluses, `0 ≤ β < 1`, the
pull-out property, an adapted nowhere-zero price level `P` (for (8.2) the foreign price level
`P*`) and predetermined debt, the nominal flow plus the transversality condition on `B/P` is
equivalent to the valuation equation `B_{t−1}/P_t = E_t ∑ βʲ s_{t+j}` at every date. With `P*`
given from abroad this is a constraint on surpluses. -/
theorem nominal_valuation_iff (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {B P s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    (NominalFlow 𝔼 β B P s ∧ TVC 𝔼 β (fun t => B t / P t)) ↔
      ∀ t, B t / P t = pv 𝔼 β s t := by
  rw [nominalFlow_iff_solves 𝔼 hPO hPa hP hBpre, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs hsa, funext_iff]

/-- Cochrane (2023), p. 240 (foreign-currency debt) and §8.6, p. 257 (an independent central
bank): when the price level is fixed at `P̄ > 0` (from abroad, or by the central bank), the
valuation `B D/P̄ = V` with `B > 0` gives the haircut `D = P̄ V/B`, with `D = 1` iff `V = B/P̄`
and `D < 1` iff `V < B/P̄`. -/
theorem haircut_of_fixed_price {B Pbar V D : ℝ} (hB : 0 < B) (hP : 0 < Pbar)
    (hD : B * D / Pbar = V) :
    D = Pbar * V / B ∧ (D = 1 ↔ V = B / Pbar) ∧ (D < 1 ↔ V < B / Pbar) := by
  have hD' : D = Pbar * V / B := by
    rw [eq_div_iff hB.ne', ← hD]
    field_simp
  refine ⟨hD', ?_, ?_⟩
  · rw [hD', div_eq_one_iff_eq hB.ne', eq_div_iff hP.ne']
    constructor <;> intro h <;> linarith
  · rw [hD', div_lt_one hB, lt_div_iff₀ hP]
    constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 240 (Greece in the euro): with foreign-currency debt `B > 0` and the
foreign price level `P* > 0` given, the price level cannot adjust; if the present value of
surpluses `V` falls short of `B/P*`, the only way to satisfy `B D/P* = V` is an explicit
haircut, `D = P* V/B < 1`. -/
theorem foreign_default_required {B Pstar V D : ℝ} (hB : 0 < B) (hP : 0 < Pstar)
    (hshort : V < B / Pstar) (hD : B * D / Pstar = V) : D = Pstar * V / B ∧ D < 1 :=
  ⟨(haircut_of_fixed_price hB hP hD).1, (haircut_of_fixed_price hB hP hD).2.2.mpr hshort⟩

/-! ### §8.2 Reserves, pegs and the gold standard -/

/-- Cochrane (2023), p. 242: with reserves `G` the valuation equation is
`B_{t−1}/P_t = G_t + E_t ∑ βʲ s_{t+j}`; for `B > 0` and `G + V > 0` the price level is unique,
`P = B/(G + V)`. -/
theorem reserves_price_unique {B G V : ℝ} (hB : 0 < B) (hGV : 0 < G + V) :
    ∃! P : ℝ, 0 < P ∧ B / P = G + V :=
  valuation_price_unique hB hGV

/-- Cochrane (2023), p. 242: reserves "enter in parallel with the present value of surpluses":
the price level depends on reserves `G` and the surplus present value `V` only through
`G + V`. -/
theorem reserves_through_sum {B G V G' V' P : ℝ} (hsum : G + V = G' + V') :
    B / P = G + V ↔ B / P = G' + V' := by
  rw [hsum]

/-- Cochrane (2023), p. 243: the gold standard is passive with respect to the relative price of
goods and gold: a deflation (`q` falls) raises the surplus present value needed to pay the debt
at the peg. -/
theorem gold_deflation_raises_pv {B Pg q q' : ℝ} (hB : 0 < B) (hPg : 0 < Pg) (hq' : 0 < q')
    (hq : q' < q) : B / (Pg * q) < B / (Pg * q') := by
  apply div_lt_div_of_pos_left hB (mul_pos hPg hq') (mul_lt_mul_of_pos_left hq hPg)

/-- Cochrane (2023), pp. 242–243 ($20 to $32 per ounce): a devaluation from `P_g = 20` to
`P_g = 32` raises the price level by the factor `8/5` at a given relative price `q`, and cuts the
required present value of surpluses by the factor `5/8`. -/
theorem gold_devaluation {B q : ℝ} (hB : 0 < B) (hq : 0 < q) :
    (32 * q) / (20 * q) = 8 / 5 ∧ (B / (32 * q)) / (B / (20 * q)) = 5 / 8 := by
  constructor
  · field_simp
    norm_num
  · field_simp
    norm_num

end Cochrane.AssetsRulesBalanceSheets.RealDebt
