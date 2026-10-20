/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.RealDebt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Pots of assets: nominal liabilities backed by real assets

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 10, §10.1.1–10.1.2
(pp. 288–294), eqs. (10.1)–(10.6); and the real-bills doctrine of §11.5 (p. 322), which the
Chapters 11–19 survey assigns here.

A central bank issues nominal liabilities `B` and holds `b̂` shares of a real asset paying `ŝ`
per share, with ex-dividend price `q̂_t = E_t ∑ β^{j+1} ŝ_{t+1+j}` (10.1). Timing as in
`RealDebt`: `B t` is `B_{t−1}` and `bh t` is `b̂_{t−1}`, the holdings entering date `t`.

## Main results

* §10.1.1: `B_{t−1}/P_t = b_t` determines `P_t` (`PresentValue.valuation_price_unique`);
  `pot_unique_of_strictMono` and
  `pot_exists_of_continuous` (assets whose nominal value `P b(P)` is strictly increasing
  determine the price level), `pot_nominal_assets` (purely nominal assets cannot),
  `share_split` (varying `B_t` alone sets the future price level). The nominal flow on p. 290 is
  `RealDebt.nominalFlow_iff_solves`.
* (10.1)–(10.6): `qhat`, `qhat_recursion`, `pv_eq_sh_add_qhat`, `PotFlow` (10.2), `potX`,
  `potX_eq_pv_form`, `beta_E_potX`,
  `potFlow_iff_X` ((10.4)/(10.6): `X_t = β E_t X_{t+1}`), `PresentValue.eq_zero_of_tvc`
  ("both sides must be zero"), `pot_valuation_iff` ((10.3) ⇔ flow + transversality),
  `pot_valuation_pv` (the middle expression of (10.3)), `eq_10_5_eq_10_4` (survey E10.3:
  dropping `E_{t+1}` in (10.5) is harmless).
* Purchases at market prices: `purchases_irrelevant` (`P_t` does not depend on `b̂_t`) and
  `purchases_matched` (`β E_t(B_t/P_{t+1}) = q̂_t b̂_t`).
* §10.1.2: `sell_profit_pos_iff`, `buy_profit_pos_iff`, `no_arbitrage_iff` (a right to convert
  dollars and asset shares at `b̂_{t−1}/B_{t−1}` is arbitrage-free iff (10.3) holds);
  `discounted_wealth_const`, `wealth_tvc_iff`, `wealth_noPonzi_iff`, `wealth_explodes_pos`,
  `wealth_explodes_neg` (p. 294, the asymmetry of the transversality condition).
* §11.5 real bills: `real_bills_real_asset`, `real_bills_nominal_asset`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.PotOfAssets

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §10.1.1 Nominal debt and real assets -/

/-- Cochrane (2023), §10.1.1, p. 289: "It is enough that their value does not decline one-for-one
with the price level": if the nominal value of the assets `P ↦ P b(P)` is strictly increasing on
`P > 0`, then `B/P = b(P)` has at most one positive solution. -/
theorem pot_unique_of_strictMono {B : ℝ} {bf : ℝ → ℝ}
    (hN : StrictMonoOn (fun P => P * bf P) (Set.Ioi 0)) {P₁ P₂ : ℝ} (h1 : 0 < P₁)
    (h2 : 0 < P₂) (e1 : B / P₁ = bf P₁) (e2 : B / P₂ = bf P₂) : P₁ = P₂ := by
  have n1 : P₁ * bf P₁ = B := by rw [← e1]; field_simp
  have n2 : P₂ * bf P₂ = B := by rw [← e2]; field_simp
  exact price_unique_of_strictMonoOn hN h1 h2 n1.symm n2.symm

/-- Cochrane (2023), §10.1.1, p. 289: existence — if the nominal value `P ↦ P b(P)` is continuous
on `[p₁, p₂]` (`0 < p₁ ≤ p₂`) and the nominal liabilities `B` lie between its end values, some
price level in `[p₁, p₂]` solves `B/P = b(P)`. -/
theorem pot_exists_of_continuous {B p₁ p₂ : ℝ} {bf : ℝ → ℝ} (hp₁ : 0 < p₁) (hp : p₁ ≤ p₂)
    (hc : ContinuousOn (fun P => P * bf P) (Set.Icc p₁ p₂)) (hlo : p₁ * bf p₁ ≤ B)
    (hhi : B ≤ p₂ * bf p₂) : ∃ P ∈ Set.Icc p₁ p₂, B / P = bf P := by
  obtain ⟨P, hPmem, hPB⟩ := intermediate_value_Icc hp hc ⟨hlo, hhi⟩
  refine ⟨P, hPmem, ?_⟩
  have hP0 : P ≠ 0 := (lt_of_lt_of_le hp₁ hPmem.1).ne'
  rw [← hPB]
  field_simp

/-- Cochrane (2023), §10.1, p. 288: "nominal assets and nominal liabilities cannot define a
numeraire or determine the price level": if the assets are nominal, `b(P) = A/P`, then
`B/P = b(P)` holds at one nonzero price level iff it holds at every one (iff `B = A`). -/
theorem pot_nominal_assets {B A P : ℝ} (hP : P ≠ 0) : B / P = A / P ↔ B = A := by
  constructor
  · intro h
    field_simp at h
    exact h
  · intro h
    rw [h]

/-- Cochrane (2023), §10.1.1, p. 289: the bank "can set expected inflation ... by varying nominal
debt `B_t` without changing the amount of real securities, effectively by share splits":
multiplying the nominal debt by `k` multiplies the price level that solves `B/P = v` by `k`. -/
theorem share_split {B P v k P' : ℝ} (hP : P ≠ 0) (hv : v ≠ 0) (hP' : P' ≠ 0)
    (h : B / P = v) : k * B / P' = v ↔ P' = k * P := by
  have hB : B = v * P := by rw [← h]; field_simp
  rw [hB, div_eq_iff hP']
  constructor
  · intro h2
    have : v * (k * P) = v * P' := by rw [← h2]; ring
    exact (mul_left_cancel₀ hv this).symm
  · intro h2
    rw [h2]
    ring

/-! ### (10.1)–(10.6) A managed portfolio of real assets -/

/-- Cochrane (2023), eq. (10.1), p. 290: the real ex-dividend price per share,
`q̂_t = E_t ∑_{j ≥ 0} β^{j+1} ŝ_{t+1+j}`. -/
noncomputable def qhat (β : ℝ) (sh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + j) ω)

/-- Cochrane (2023), eq. (10.1), p. 290: the share price satisfies the pricing recursion
`q̂_t = β E_t(ŝ_{t+1} + q̂_{t+1})` whenever the discounted dividends are summable state by
state. -/
theorem qhat_recursion {β : ℝ} {sh : ℕ → Ω → ℝ}
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    qhat 𝔼 β sh t = β • 𝔼.E t (sh (t + 1) + qhat 𝔼 β sh (t + 1)) := by
  have hpath : (fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + j) ω) =
      β • (sh (t + 1) + fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + 1 + j) ω) := by
    funext ω
    have hs : Summable (fun j => β ^ (j + 1) * sh (t + 1 + j) ω) :=
      ((hsum (t + 1) ω).mul_left β).congr fun j => by ring
    rw [hs.tsum_eq_zero_add]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [mul_add, ← tsum_mul_left]
    congr 1
    · simp
    · exact tsum_congr fun j => by
        rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
        ring
  simp only [qhat]
  rw [hpath, map_smul, map_add, map_add, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), eq. (10.3), p. 291: the cum-dividend value of a share is
`E_t ∑_{j ≥ 0} βʲ ŝ_{t+j} = ŝ_t + q̂_t` for adapted summable dividends. -/
theorem pv_eq_sh_add_qhat {β : ℝ} {sh : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted sh)
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    pv 𝔼 β sh t = sh t + qhat 𝔼 β sh t := by
  have hpath : epv β sh t = sh t + fun ω => ∑' j, β ^ (j + 1) * sh (t + 1 + j) ω := by
    funext ω
    simp only [epv, Pi.add_apply]
    rw [(hsum t ω).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    exact tsum_congr fun j => by rw [show t + (j + 1) = t + 1 + j by omega]
  rw [pv, hpath, map_add, hsa t, qhat]

/-- Cochrane (2023), eq. (10.2), p. 290: the bank's flow condition with asset purchases,
`B_{t−1}/P_t = b̂_{t−1} ŝ_t + β E_t(B_t/P_{t+1}) − q̂_t (b̂_t − b̂_{t−1})`. -/
def PotFlow (β : ℝ) (B P bh sh : ℕ → Ω → ℝ) : Prop :=
  ∀ t, B t / P t = bh t * sh t + β • 𝔼.E t (B (t + 1) / P (t + 1)) -
    qhat 𝔼 β sh t * (bh (t + 1) - bh t)

/-- Cochrane (2023), eq. (10.6), p. 293: the net value
`X_t = B_{t−1}/P_t − b̂_{t−1}(ŝ_t + q̂_t)`. -/
noncomputable def potX (β : ℝ) (B P bh sh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  B t / P t - bh t * (sh t + qhat 𝔼 β sh t)

/-- Cochrane (2023), eqs. (10.4) and (10.6), pp. 291, 293: for adapted summable dividends the net
value in (10.6) is the left-hand side of (10.4),
`X_t = B_{t−1}/P_t − b̂_{t−1} E_t ∑ βʲ ŝ_{t+j}`. -/
theorem potX_eq_pv_form {β : ℝ} {B P bh sh : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted sh)
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    potX 𝔼 β B P bh sh t = B t / P t - bh t * pv 𝔼 β sh t := by
  rw [potX, pv_eq_sh_add_qhat 𝔼 hsa hsum t]

/-- Cochrane (2023), eq. (10.4), p. 291: with the pull-out property and holdings `b̂_t` chosen at
`t`, `β E_t X_{t+1} = β E_t(B_t/P_{t+1}) − b̂_t q̂_t`. -/
theorem beta_E_potX (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    β • 𝔼.E t (potX 𝔼 β B P bh sh (t + 1)) =
      β • 𝔼.E t (B (t + 1) / P (t + 1)) - bh (t + 1) * qhat 𝔼 β sh t := by
  rw [potX, map_sub, hPO t _ _ (hbpre t), qhat_recursion 𝔼 hsum t]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eqs. (10.4) and (10.6), pp. 291, 293: the flow condition (10.2) holds at
every date iff the net value satisfies `X_t = β E_t X_{t+1}`. -/
theorem potFlow_iff_X (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) :
    PotFlow 𝔼 β B P bh sh ↔
      ∀ t, potX 𝔼 β B P bh sh t = β • 𝔼.E t (potX 𝔼 β B P bh sh (t + 1)) := by
  simp only [PotFlow, beta_E_potX 𝔼 hPO hbpre hsum]
  simp only [potX, funext_iff, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
    smul_eq_mul]
  constructor
  · intro h t ω
    linarith [h t ω]
  · intro h t ω
    linarith [h t ω]

/-- Cochrane (2023), eq. (10.3), p. 291: the flow (10.2) at every date plus the transversality
condition on `X` is equivalent to `B_{t−1}/P_t = b̂_{t−1}(ŝ_t + q̂_t)` at every date: the value
of nominal debt equals the value of the bank's assets. -/
theorem pot_valuation_iff (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) :
    (PotFlow 𝔼 β B P bh sh ∧ TVC 𝔼 β (potX 𝔼 β B P bh sh)) ↔
      ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t) := by
  have hzero_iff : (∀ t, potX 𝔼 β B P bh sh t = 0) ↔
      ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t) := by
    simp only [potX, sub_eq_zero]
  rw [← hzero_iff, potFlow_iff_X 𝔼 hPO hbpre hsum]
  constructor
  · rintro ⟨hX, htvc⟩
    exact eq_zero_of_tvc 𝔼 hX htvc
  · intro h0
    refine ⟨fun t => ?_, fun t ω => ?_⟩
    · rw [h0 t, h0 (t + 1), map_zero, smul_zero]
    · simp only [h0, map_zero, Pi.zero_apply, mul_zero]
      exact tendsto_const_nhds

/-- Cochrane (2023), eq. (10.3), p. 291 (middle expression): for adapted summable dividends,
`B_{t−1}/P_t = b̂_{t−1} E_t ∑ βʲ ŝ_{t+j}` is the same condition as
`B_{t−1}/P_t = b̂_{t−1}(ŝ_t + q̂_t)`. -/
theorem pot_valuation_pv {β : ℝ} {B P bh sh : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted sh)
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω)) (t : ℕ) :
    B t / P t = bh t * pv 𝔼 β sh t ↔ B t / P t = bh t * (sh t + qhat 𝔼 β sh t) := by
  rw [pv_eq_sh_add_qhat 𝔼 hsa hsum t]

/-- Cochrane (2023), eqs. (10.4)–(10.5), pp. 291, 293 (survey E10.3): (10.5) drops the
`E_{t+1}` inside the second term of (10.4); with the pull-out property and `b̂_t` known at `t`
the two right-hand sides are equal, so the omission is harmless. -/
theorem eq_10_5_eq_10_4 (hPO : 𝔼.PullOut) {t : ℕ} {Bn Pn bn Y : Ω → ℝ}
    (hb : 𝔼.E t bn = bn) :
    𝔼.E t (Bn / Pn - bn * 𝔼.E (t + 1) Y) = 𝔼.E t (Bn / Pn - bn * Y) := by
  rw [map_sub, map_sub, hPO t _ _ hb, hPO t _ _ hb, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), p. 291: asset purchases at market prices do not affect the price level:
two equilibria with the same maturing nominal debt `B_{t−1}`, the same holdings `b̂_{t−1}` and
the same dividends have the same `P_t`, whatever the new purchases `b̂_t`. -/
theorem purchases_irrelevant {β : ℝ} {B P P' bh bh' sh : ℕ → Ω → ℝ}
    (hv : ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t))
    (hv' : ∀ t, B t / P' t = bh' t * (sh t + qhat 𝔼 β sh t)) {t : ℕ} {ω : Ω}
    (hbh : bh t ω = bh' t ω) (hB : B t ω ≠ 0) (hP : P t ω ≠ 0) (hP' : P' t ω ≠ 0) :
    P t ω = P' t ω := by
  have h1 := congrFun (hv t) ω
  have h2 := congrFun (hv' t) ω
  simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply] at h1 h2
  rw [← hbh, ← h1] at h2
  field_simp at h2
  exact mul_left_cancel₀ hB (by rw [mul_comm, h2, mul_comm])

/-- Cochrane (2023), p. 291: "Any increase in real assets ... is matched exactly by an increase in
the value of nominal liabilities": in an equilibrium, `β E_t(B_t/P_{t+1}) = b̂_t q̂_t`. -/
theorem purchases_matched (hPO : 𝔼.PullOut) {β : ℝ} {B P bh sh : ℕ → Ω → ℝ}
    (hbpre : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1))
    (hsum : ∀ t ω, Summable (fun j => β ^ j * sh (t + j) ω))
    (hv : ∀ t, B t / P t = bh t * (sh t + qhat 𝔼 β sh t)) (t : ℕ) :
    β • 𝔼.E t (B (t + 1) / P (t + 1)) = bh (t + 1) * qhat 𝔼 β sh t := by
  have h0 : potX 𝔼 β B P bh sh (t + 1) = 0 := by
    rw [potX, hv (t + 1), sub_self]
  have h := beta_E_potX 𝔼 hPO hbpre hsum (B := B) (P := P) t
  rw [h0, map_zero, smul_zero] at h
  exact (sub_eq_zero.mp h.symm)

/-! ### §10.1.2 A right to trade real assets -/

/-- Cochrane (2023), §10.1.2, p. 293: selling one share (cum-dividend value `v = ŝ_t + q̂_t`) to
the bank at `B_{t−1}/b̂_{t−1}` dollars per share is profitable iff the price level is too low,
`B_{t−1}/P_t > b̂_{t−1} v`. -/
theorem sell_profit_pos_iff {B P bh v : ℝ} (hbh : 0 < bh) (hP : 0 < P) :
    0 < B / (bh * P) - v ↔ bh * v < B / P := by
  rw [sub_pos, lt_div_iff₀ (mul_pos hbh hP), lt_div_iff₀ hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §10.1.2, p. 294: buying `b̂_{t−1}/B_{t−1}` shares from the bank with one
dollar is profitable iff the price level is too high, `B_{t−1}/P_t < b̂_{t−1} v`. -/
theorem buy_profit_pos_iff {B P bh v : ℝ} (hB : 0 < B) (hP : 0 < P) :
    0 < bh / B * v - 1 / P ↔ B / P < bh * v := by
  rw [sub_pos, div_lt_iff₀ hP, div_mul_eq_mul_div, div_mul_eq_mul_div, lt_div_iff₀ hB,
    div_lt_iff₀ hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §10.1.2, pp. 293–294: with the conversion right, there is no profitable
trade in either direction iff the value of the bank's liabilities equals the value of its
assets, `B_{t−1}/P_t = b̂_{t−1}(ŝ_t + q̂_t)`. -/
theorem no_arbitrage_iff {B P bh v : ℝ} (hbh : 0 < bh) (hB : 0 < B) (hP : 0 < P) :
    (¬ 0 < B / (bh * P) - v ∧ ¬ 0 < bh / B * v - 1 / P) ↔ B / P = bh * v := by
  rw [sell_profit_pos_iff hbh hP, buy_profit_pos_iff hB hP]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  · intro h
    rw [h]
    exact ⟨lt_irrefl _, lt_irrefl _⟩

/-- Cochrane (2023), p. 293: in perfect foresight, if `X_t = β X_{t+1}` then the discounted
net private wealth `βᵀ X_{t+T}` is constant, equal to `X_t`. -/
theorem discounted_wealth_const {β : ℝ} {X : ℕ → ℝ} (hX : ∀ t, X t = β * X (t + 1))
    (t T : ℕ) : β ^ T * X (t + T) = X t := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [← ih, hX (t + T), pow_succ, show t + (T + 1) = t + T + 1 by omega]
    ring

/-- Cochrane (2023), p. 294: the transversality condition `βᵀ X_{t+T} → 0` holds iff the
initial gap is zero, `X_t = 0`. -/
theorem wealth_tvc_iff {β : ℝ} {X : ℕ → ℝ} (hX : ∀ t, X t = β * X (t + 1)) (t : ℕ) :
    Tendsto (fun T : ℕ => β ^ T * X (t + T)) atTop (𝓝 0) ↔ X t = 0 := by
  simp_rw [discounted_wealth_const hX t]
  constructor
  · intro h
    exact tendsto_nhds_unique tendsto_const_nhds h
  · intro h
    rw [h]
    exact tendsto_const_nhds

/-- Cochrane (2023), p. 294 ("negative net wealth ... is eventually ruled out by a budget
constraint"): the no-Ponzi condition `βᵀ X_{t+T} ≥ 0` for all `T` holds iff `X_t ≥ 0`; positive
net wealth violates only optimality (the transversality condition), not the budget
constraint. -/
theorem wealth_noPonzi_iff {β : ℝ} {X : ℕ → ℝ} (hX : ∀ t, X t = β * X (t + 1)) (t : ℕ) :
    (∀ T, 0 ≤ β ^ T * X (t + T)) ↔ 0 ≤ X t := by
  simp_rw [discounted_wealth_const hX t]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- Cochrane (2023), p. 293: "If `P_t` is too low ... the net value grows at the real interest
rate": with `0 < β < 1` and `X_t > 0`, `X_{t+T} → +∞`. -/
theorem wealth_explodes_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℕ → ℝ}
    (hX : ∀ t, X t = β * X (t + 1)) {t : ℕ} (hpos : 0 < X t) :
    Tendsto (fun T => X (t + T)) atTop atTop := by
  have hgrow : ∀ T, X (t + T) = (β⁻¹) ^ T * X t := by
    intro T
    rw [← discounted_wealth_const hX t T, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hβ0.ne',
      one_pow, one_mul]
  simp_rw [hgrow]
  exact Tendsto.atTop_mul_const hpos
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hβ0 |>.mpr hβ1))

/-- Cochrane (2023), p. 294: with `0 < β < 1` and `X_t < 0`, `X_{t+T} → −∞` (ruled out by the
budget constraint). -/
theorem wealth_explodes_neg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {X : ℕ → ℝ}
    (hX : ∀ t, X t = β * X (t + 1)) {t : ℕ} (hneg : X t < 0) :
    Tendsto (fun T => X (t + T)) atTop atBot := by
  have hX' : ∀ t, (-X) t = β * (-X) (t + 1) := fun t => by
    simp only [Pi.neg_apply]
    rw [hX t]
    ring
  have h := wealth_explodes_pos hβ0 hβ1 hX' (t := t) (by simp only [Pi.neg_apply]; linarith)
  exact Tendsto.congr (fun T => by simp) (tendsto_neg_atTop_atBot.comp h)

/-! ### §11.5 Real bills (p. 322) -/

/-- Cochrane (2023), §11.5, p. 322 (Chapters 11–19 survey V7): issuing `ΔM` of money against a
real asset worth `ΔM/P` at the initial price level `P` (with `B/P = V`) adds equally to both sides
of the valuation equation; the new equation `(B + ΔM)/P' = V + ΔM/P` holds iff `P' = P`. -/
theorem real_bills_real_asset {B ΔM V P P' : ℝ} (hP : P ≠ 0) (hP' : P' ≠ 0)
    (hBM : B + ΔM ≠ 0) (h : B / P = V) : (B + ΔM) / P' = V + ΔM / P ↔ P' = P := by
  rw [← h, ← add_div]
  constructor
  · intro h2
    rw [div_eq_div_iff hP' hP] at h2
    exact (mul_left_cancel₀ hBM h2).symm
  · intro h2
    rw [h2]

/-- Cochrane (2023), §11.5, p. 322: if instead the bill is nominal (worth `ΔM/P'` at any price
level `P'`), the new valuation equation `(B + ΔM)/P' = V + ΔM/P'` has exactly the same solutions
as the old one, `B/P' = V`. -/
theorem real_bills_nominal_asset (B ΔM V P' : ℝ) :
    (B + ΔM) / P' = V + ΔM / P' ↔ B / P' = V := by
  rw [add_div]
  constructor <;> intro h <;> linarith

end Cochrane.AssetsRulesBalanceSheets.PotOfAssets
