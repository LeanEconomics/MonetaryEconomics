/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.CPIStandard
import AssetsRulesBalanceSheets.CapitalStructure
import AssetsRulesBalanceSheets.MaturityBuffer
import AssetsRulesBalanceSheets.SharesAsMoney
import AssetsRulesBalanceSheets.Default

/-!
# Links between Chapters 8, 9 and 10

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapters 8 (pp. 239–258), 9
(pp. 259–286) and 10 (pp. 287–311). The chapters were formalised in two chains: Chapter 8 and
Chapter 10 (`RealDebt` … `BalanceSheets`) and Chapter 9 (`InflationTarget` … `CPIStandard`).
This module proves that the objects the two chains formalise separately are the same objects.

## Main results

* Valuation: `economy_nominalFlow`, `economy_valuation` — the §9.2 economy satisfies the §8.2
  nominal flow condition, so Theorem IT's real debt is the present value (8.2);
  `economy_tvc_iff`, `tvc_perfectForesight_iff` — the transversality conditions of the two
  chains are the same condition.
* Indexed debt: `ruleEquilibrium_iff_indexed` — the §9.3.2 rule equilibrium (ex post) is the
  §8.1 indexed-debt equilibrium under perfect foresight; `indexedFlow_eq_9_9` — under
  uncertainty, the §8.1 indexed flow with the §9.3.2 rule gives (9.9) state by state;
  `rule_97_determines` — (9.7) is an instance of the §8.1 "s(P) can determine P" claim.
* Indexed-debt pegs: `indexedPrice_eq_claimPrice`, `indexed_peg_iff`,
  `indexed_peg_foc_iff_market` — the §8.1 indexed-bond price is the §9.6 claim price, and the
  §9.5 peg holds iff the market price of indexed debt is `β P*_t`.
* Mixed debt: `mixed_existsUnique_iff`, `elasticities_reciprocal` — the §8.3 capital-structure
  price level and the §9.3.5 debt-value elasticity are reciprocal.
* Maturity: `valuation_922_of_short_debt`, `valuation_of_short_debt` — the §9.4.1 valuation
  equation (9.22) is the one-period-debt case (`ω = 0`) of the §8.4 identity.
* Bond prices: `bondPrice_no_haircut`, `revenue_eq_9_27` — the §8.5 bond price without a haircut
  is the §9.4.2 bond price of (9.27).
* Perpetuities: `pv_one_eq_one_add_perpetuity` — the §10.1.3 perpetuity value `1/(1 − β)` is the
  coupon plus the §9.6 ex-coupon value `1/r`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.Links

open Filter Topology PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §9.2 Theorem IT and the (8.2) valuation equation -/

/-- Cochrane (2023), §9.2, p. 263, and eq. (8.2), p. 240: the private-sector equilibrium of the
inflation-target model (`InflationTarget.Economy`: flow condition and bond pricing
`Q_t = β E_t(P_t/P_{t+1})`) satisfies the nominal flow condition `RealDebt.NominalFlow` of §8.2. -/
theorem economy_nominalFlow {β : ℝ} {B P Q s : ℕ → Ω → ℝ}
    (hE : InflationTarget.Economy 𝔼 β B P Q s) : RealDebt.NominalFlow 𝔼 β B P s := by
  intro t
  funext ω
  have h := congrFun (hE.flow t) ω
  have hq := congrFun (hE.pricing t) ω
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h hq
  have hP := (hE.pos_P t ω).ne'
  rw [map_smul]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hq]
  calc B t ω = B t ω / P t ω * P t ω := by field_simp
    _ = (s t ω + Q t ω * B (t + 1) ω / P t ω) * P t ω := by rw [h]
    _ = P t ω * s t ω + Q t ω * B (t + 1) ω := by rw [add_mul, div_mul_cancel₀ _ hP]; ring

/-- Cochrane (2023), §9.2, p. 264 ("the real value of nominal debt is also the present value of
surpluses") and eq. (8.2), p. 240: in the inflation-target economy with bounded adapted
surpluses, `0 ≤ β < 1` and the pull-out property, `B_t/P_t = E_t ∑ βʲ s_{t+j}` at every date —
the §8.2 valuation equation `RealDebt.nominal_valuation_iff`. -/
theorem economy_valuation (h𝔼 : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {B P Q s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hE : InflationTarget.Economy 𝔼 β B P Q s) : ∀ t, B t / P t = pv 𝔼 β s t :=
  (RealDebt.nominal_valuation_iff 𝔼 h𝔼 hβ0 hβ1 hs hsa hE.adapted_P
    (fun t ω => (hE.pos_P t ω).ne') hE.predetermined_B).mp ⟨economy_nominalFlow 𝔼 hE, hE.tvc⟩

/-- Cochrane (2023), §9.2, p. 263, and p. 239: the transversality field of
`InflationTarget.Economy` is the condition `TVC` of `PresentValue` for real debt `B/P`. -/
theorem economy_tvc_iff {β : ℝ} {B P : ℕ → Ω → ℝ} :
    (∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (B (t + T) / P (t + T)) ω) atTop (𝓝 0)) ↔
      TVC 𝔼 β (fun t => B t / P t) :=
  Iff.rfl

/-- Cochrane (2023), §9.3.2, p. 266, and p. 239: under perfect foresight the expected
transversality condition `TVC` is the ex post condition `βᵀ b_{t+T} → 0` used by
`FiscalRules.RuleEquilibrium`. -/
theorem tvc_perfectForesight_iff {β : ℝ} {x : ℕ → Unit → ℝ} :
    TVC perfectForesight β x ↔ ∀ t, Tendsto (fun T => β ^ T * x (t + T) ()) atTop (𝓝 0) :=
  ⟨fun h t => h t (), fun h t _ => h t⟩

/-! ### §8.1 indexed debt and §9.3 fiscal rules -/

/-- Cochrane (2023), §9.3.2, pp. 266–267, and §8.1, p. 239: an ex post equilibrium of the dynamic
fiscal rule with indexed debt (`FiscalRules.RuleEquilibrium`) is exactly a perfect-foresight
equilibrium of the §8.1 indexed-debt flow (`RealDebt.IndexedFlow`) with the rule
`s_t = s_{0,t} + θ (P_t − P*_t)`, positive prices and the transversality condition. -/
theorem ruleEquilibrium_iff_indexed {β θ : ℝ} {s0 Pstar P b : ℕ → ℝ} :
    FiscalRules.RuleEquilibrium β θ s0 Pstar P b ↔ (∀ t, 0 < P t) ∧
      RealDebt.IndexedFlow perfectForesight β (fun t _ => b t)
        (fun t _ => s0 t + θ * (P t - Pstar t)) (fun t _ => P t) ∧
      TVC perfectForesight β (fun t _ => b t) := by
  constructor
  · rintro ⟨hP, hflow, htvc⟩
    exact ⟨hP, (RealDebt.indexedFlow_iff perfectForesight (fun _ => rfl)
      (fun t _ => (hP t).ne')).mpr fun t _ => hflow t, fun t _ => htvc t⟩
  · rintro ⟨hP, hflow, htvc⟩
    exact ⟨hP, fun t => (RealDebt.indexedFlow_iff perfectForesight (fun _ => rfl)
      (fun t _ => (hP t).ne')).mp hflow t (), fun t => htvc t ()⟩

/-- Cochrane (2023), eq. (9.9), p. 266, and §8.1, p. 239: under any expectation system, the §8.1
indexed-debt flow with the surplus rule `s_t = s_{0,t} + θ (P_t − P*_t)` and the ex post
transversality condition give (9.9) in every state,
`b_{t−1} = ∑ βʲ s_{0,t+j} + θ ∑ βʲ (P_{t+j} − P*_{t+j})`. -/
theorem indexedFlow_eq_9_9 {β θ : ℝ} {b s0 P Pstar : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0)
    (hflow : RealDebt.IndexedFlow 𝔼 β b (fun t => s0 t + θ • (P t - Pstar t)) P) (t : ℕ)
    (ω : Ω) (htvc : Tendsto (fun T => β ^ T * b (t + T) ω) atTop (𝓝 0))
    (hs0 : Summable (fun j => β ^ j * s0 (t + j) ω))
    (hPs : Summable (fun j => β ^ j * (P (t + j) ω - Pstar (t + j) ω))) :
    b t ω = ∑' j, β ^ j * s0 (t + j) ω + θ * ∑' j, β ^ j * (P (t + j) ω - Pstar (t + j) ω) := by
  have h := (RealDebt.indexedFlow_iff 𝔼 hPa hP).mp hflow
  refine FiscalRules.eq_9_9 (b := fun t => b t ω) (s0 := fun t => s0 t ω)
    (P := fun t => P t ω) (Pstar := fun t => Pstar t ω) (fun t => ?_) t htvc hs0 hPs
  have := h t ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
  exact this

/-- Cochrane (2023), eq. (9.7), p. 265, and p. 239 ("surpluses that respond to the price level
can determine it"): for `θ ≠ 0` the rule `s(P) = b + θ (P − P*)` is injective, so the §8.1 claim
`RealDebt.surplus_rule_determines` applies and the one-period valuation `b = s(P)` gives
`P = P*`. -/
theorem rule_97_determines {θ : ℝ} (hθ : θ ≠ 0) {β b Pstar P : ℝ}
    (h : b = (b + θ * (P - Pstar)) + β * 0) : P = Pstar := by
  have hinj : Function.Injective (fun p : ℝ => b + θ * (p - Pstar)) := fun p q hpq => by
    have h1 : θ * (p - q) = 0 := by simp only at hpq; linarith
    rcases mul_eq_zero.mp h1 with h0 | h0
    · exact absurd h0 hθ
    · linarith
  exact RealDebt.surplus_rule_determines (σ := fun p : ℝ => b + θ * (p - Pstar)) hinj h
    (by ring)

/-! ### §8.1 indexed debt and the §9.5–§9.6 pegs -/

/-- Cochrane (2023), p. 239 and §9.6, p. 286: the §8.1 nominal price of a one-period indexed
bond, `E_t[β (P_t/P_{t+1}) P_{t+1}]`, is the §9.6 dollar price of a claim to next period's
basket, `P_t β E_t(P_{t+1}/P_{t+1})`; both are `β P_t`. -/
theorem indexedPrice_eq_claimPrice {β : ℝ} {P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, 0 < P t ω) (t : ℕ) :
    RealDebt.indexedPrice 𝔼 β P t = P t * β • 𝔼.E t (P (t + 1) / P (t + 1)) := by
  rw [RealDebt.indexedPrice_eq 𝔼 hPa (fun t ω => (hP t ω).ne') t,
    CPIStandard.indexed_claim_price 𝔼 hP t]

/-- Cochrane (2023), §9.5, p. 281, and §9.6, p. 286, with the §8.1 bond price of p. 239: a peg
that sells one-period indexed debt at the nominal price `β P*_t` clears the market at date `t`
(the market price `RealDebt.indexedPrice` equals the peg) if and only if `P_t = P*_t`. -/
theorem indexed_peg_iff {β : ℝ} (hβ : 0 < β) {P Pstar : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, 0 < P t ω) (t : ℕ) :
    RealDebt.indexedPrice 𝔼 β P t = β • Pstar t ↔ P t = Pstar t := by
  rw [indexedPrice_eq_claimPrice 𝔼 hPa hP t]
  constructor
  · exact CPIStandard.indexed_peg_pins_price 𝔼 hβ hP t
  · intro h
    rw [CPIStandard.indexed_claim_price 𝔼 hP t, h]

/-- Cochrane (2023), §9.5, pp. 281–282, and p. 239: in the endowment economy (`c = y`) the
consumer's first-order condition at the indexed-debt peg holds at every date iff the §8.1
market price of indexed debt equals the peg `β P*_t` at every date (both iff `P = P*`). -/
theorem indexed_peg_foc_iff_market {β y : ℝ} (hβ : 0 < β) {up : ℝ → ℝ} (hy : 0 < up y)
    {P Pstar : ℕ → Unit → ℝ} (hP : ∀ t ω, 0 < P t ω) :
    (∀ n, β * Pstar n () / P n () * up y = β * up y) ↔
      ∀ t, RealDebt.indexedPrice perfectForesight β P t = β • Pstar t := by
  have hfoc := IndexedDebtPeg.price_eq_target (P := fun n => P n ()) (Pstar := fun n => Pstar n ())
    hβ hy (fun n => hP n ())
  rw [hfoc]
  simp only [indexed_peg_iff perfectForesight hβ (fun _ => rfl) hP]
  constructor
  · intro h t
    funext ω
    exact congrFun h t
  · intro h
    funext n
    exact congrFun (h n) ()

/-! ### §8.3 capital structure and §9.3.5 mixed debt rules -/

/-- Cochrane (2023), eq. (8.3), p. 246, and §9.3.5, p. 271: with nominal debt `B > 0` and real
debt `b`, the one-period valuation `b + B/P = V` (a constant surplus in §9.3.5) has a unique
positive price level iff `b < V` (`CapitalStructure.mixed_price_unique`,
`CapitalStructure.mixed_no_price`; uniqueness alone is `MixedDebtRules.price_unique_const`). -/
theorem mixed_existsUnique_iff {b B V : ℝ} (hB : 0 < B) :
    (∃! P : ℝ, 0 < P ∧ b + B / P = V) ↔ b < V := by
  constructor
  · intro h
    by_contra hbV
    exact CapitalStructure.mixed_no_price hB (not_lt.mp hbV) h.exists
  · exact CapitalStructure.mixed_price_unique hB

/-- Cochrane (2023), p. 246 (§8.3: more real debt makes the price level more volatile) and
§9.3.5, p. 271 (the debt value has elasticity minus the nominal share): at
`V = b + B/P`, the elasticity of `P` with respect to `V` from (8.3), `−V/(V − b)`, and the
elasticity of the debt value with respect to `P`, `P v'(P)/v(P)`, are reciprocal. -/
theorem elasticities_reciprocal {b B P : ℝ} (hB : 0 < B) (hP : 0 < P) (hV : 0 < b + B / P) :
    HasDerivAt (fun u => Real.log (B / (Real.exp u - b)))
        (-((b + B / P) / (b + B / P - b))) (Real.log (b + B / P)) ∧
      HasDerivAt (fun P => b + B / P) (-(B / P ^ 2)) P ∧
      -((b + B / P) / (b + B / P - b)) * (P * (-(B / P ^ 2)) / (b + B / P)) = 1 := by
  have hBP : 0 < B / P := div_pos hB hP
  refine ⟨CapitalStructure.log_price_elasticity hB hV (by linarith),
    MixedDebtRules.hasDerivAt_value b B hP.ne', ?_⟩
  have hV0 := hV.ne'
  have hP0 := hP.ne'
  have hB0 := hB.ne'
  have hbp : b * P + B ≠ 0 := by
    rw [show b * P + B = (b + B / P) * P by rw [add_mul, div_mul_cancel₀ _ hP0]]
    exact mul_ne_zero hV0 hP0
  rw [show b + B / P - b = B / P by ring]
  field_simp

/-! ### §8.4 maturity and the §9.4.1 valuation equation -/

/-- Cochrane (2023), eq. (8.4), p. 250 (`ω = 0`, short-term debt) and eq. (9.22), p. 275: if the
news in inflation, surpluses and real returns at `(t, ω)` satisfy the identities (3.20)–(3.21)
of §8.4 with one-period debt, the surplus news `∑ ρʲ ΔE s` is the fiscal shock `ε_{t+1}` and the
real-return news is `ΔE(i_{t+j} − π_{t+1+j})`, then the §9.4.1 valuation equation (9.22) holds
at `(t, ω)`. -/
theorem valuation_922_of_short_debt {ρ rn : ℝ} {πN sN rN : ℕ → ℝ} {π i ε : ℕ → Ω → ℝ}
    {t : ℕ} {ω : Ω} (h320 : MaturityBuffer.Identity320 ρ πN sN rN rn)
    (h321 : MaturityBuffer.Identity321 0 πN rN rn)
    (hπ : πN 0 = SpreadTarget.innov 𝔼 t (π (t + 1)) ω) (hε : ∑' j, ρ ^ j * sN j = ε (t + 1) ω)
    (hr : ∀ j, rN (j + 1) = SpreadTarget.innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω) :
    SpreadTarget.innov 𝔼 t (π (t + 1)) ω = (-ε (t + 1) + fun ω =>
      ∑' j, ρ ^ (j + 1) * SpreadTarget.innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω) ω := by
  have h := MaturityBuffer.short_debt_identity h320 h321
  rw [hπ, hε] at h
  rw [h]
  simp only [Pi.add_apply, Pi.neg_apply]
  congr 1
  exact tsum_congr fun j => by rw [hr j]

/-- Cochrane (2023), eq. (8.4), p. 250, and eq. (9.22), p. 275: if at every date and state the
news satisfies the §8.4 identities with one-period debt (`ω = 0`) as in
`valuation_922_of_short_debt`, then `SpreadTarget.Valuation` holds: (9.22) is the short-debt
case of (8.4). -/
theorem valuation_of_short_debt {ρ : ℝ} {π i ε : ℕ → Ω → ℝ}
    (h : ∀ t ω, ∃ (πN sN rN : ℕ → ℝ) (rn : ℝ), MaturityBuffer.Identity320 ρ πN sN rN rn ∧
      MaturityBuffer.Identity321 0 πN rN rn ∧ πN 0 = SpreadTarget.innov 𝔼 t (π (t + 1)) ω ∧
      ∑' j, ρ ^ j * sN j = ε (t + 1) ω ∧
      ∀ j, rN (j + 1) = SpreadTarget.innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω) :
    SpreadTarget.Valuation 𝔼 ρ π i ε := by
  intro t
  funext ω
  obtain ⟨πN, sN, rN, rn, h320, h321, hπ, hε, hr⟩ := h t ω
  exact valuation_922_of_short_debt 𝔼 h320 h321 hπ hε hr

/-! ### §8.5 bond prices and (9.27) -/

/-- Cochrane (2023), eq. (8.7), p. 254, and eq. (9.27), p. 279: without a haircut (`D ≡ 1`) the
§8.5 bond price `Q_t = β E_t(P_t D_{t+1}/P_{t+1})` is the §9.4.2 bond price
`β E_t(P_t/P_{t+1})`. -/
theorem bondPrice_no_haircut (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) :
    Default.bondPrice 𝔼 β P (fun _ _ => 1) t = β • 𝔼.E t (P t / P (t + 1)) := by
  unfold Default.bondPrice
  congr 2
  funext ω
  simp only [Pi.div_apply, Pi.mul_apply, mul_one]

/-- Cochrane (2023), eq. (8.6), p. 254, and eq. (9.27), p. 279: with no haircut, the revenue
from selling `B_t` at the §8.5 bond price is the (9.27) expression `β B_t E_t(1/P_{t+1})`. -/
theorem revenue_eq_9_27 (h𝔼 : 𝔼.PullOut) {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P) (B : ℕ → Ω → ℝ) (t : ℕ) :
    Default.bondPrice 𝔼 β P (fun _ _ => 1) t * B t / P t =
      β • (B t * 𝔼.E t (fun ω => 1 / P (t + 1) ω)) :=
  SpreadSwap.eq_9_27 𝔼 h𝔼 (Q := fun t => Default.bondPrice 𝔼 β P (fun _ _ => 1) t) hP hPa
    (fun t => bondPrice_no_haircut 𝔼 β P t) t

/-! ### §10.1.3 perpetuities and §9.6 -/

/-- Cochrane (2023), eq. (10.7), p. 296, and §9.6, p. 285: with `β = 1/(1 + r)`, the §10.1.3
value of a perpetuity including today's coupon, `E_t ∑ βʲ = 1/(1 − β)`, is the coupon plus the
§9.6 ex-coupon value `∑_{j ≥ 1} (1 + r)^{−j} = 1/r`. -/
theorem pv_one_eq_one_add_perpetuity {r : ℝ} (hr : 0 < r) (t : ℕ) :
    pv 𝔼 (1 / (1 + r)) (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) t =
      fun _ => 1 + ∑' j : ℕ, (1 / (1 + r)) ^ (j + 1) := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  rw [SharesAsMoney.pv_one 𝔼 hq0 hq1 t, (CPIStandard.hasSum_perpetuity hr).tsum_eq,
    SharesAsMoney.one_sub_beta_inv hr]
  funext _
  field_simp
  ring

end Cochrane.AssetsRulesBalanceSheets.Links
