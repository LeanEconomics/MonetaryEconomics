/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.RealDebt

/-!
# Default

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.5 (pp. 254–255),
eqs. (8.5)–(8.7).

A haircut `D_t` (each dollar of maturing debt pays `D_t` dollars) enters the valuation equation
`B_{t−1} D_t/P_t = E_t ∑ βʲ s_{t+j}` (8.5); an expected haircut `D_{t+1}` enters the bond price
`Q_t = β E_t(P_t D_{t+1}/P_{t+1})` (8.7) of the flow condition (8.6).

## Main results

* (8.5): `haircut_price_unique`, `haircut_offsets_shock` (an unexpected haircut `D = V'/V`
  absorbs a fall of the surplus present value from `V` to `V'` with no inflation).
* (8.6)–(8.7): `bondPrice`, `DefaultFlow`, `revenue_eq`, `defaultFlow_iff_solves`,
  `default_valuation_iff` ((8.5) at every date ⇔ flow + transversality), `default_flow_pv`
  ((8.6) in present-value form), `expected_default_no_effect` (an expected haircut with
  unchanged surpluses does not move `P_t`), `bondPrice_known_haircut`.
* p. 255: `bondPrice_scale`, `scaled_flow_iff` ("2 bonds at a 50% haircut = 1 bond at none":
  the equilibrium is invariant under `(B_t, D_t) ↦ (k B_t, D_t/k)`), `two_bonds_half_haircut`;
  `fixedQ_perfectForesight`, `fixedQ_next_price_mono` (with `Q_t` fixed, an expected haircut
  lowers `P_{t+1}`; it is equivalent to selling `D_{t+1} B_t` bonds with no haircut).
* p. 255, the 10% haircut example (survey E8.1): `haircut_ten_percent`,
  `haircut_factor_eq_iff`, `haircut_factor_lt`, `money_value_ten_percent_iff` — the price level
  rises by the exact factor `(s_t + V)/(s_t + 0.9 V)`, which is `10/9` (11.1%) only when
  `s_t = 0` and below `10/9` when `s_t > 0`; `rate_follows_premium` (if the interest rate
  follows the default premium, `P_{t+1}` rises by the same factor as `P_t`).
-/

namespace Cochrane.AssetsRulesBalanceSheets.Default

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (8.5): an unexpected haircut -/

/-- Cochrane (2023), eq. (8.5), p. 254: with a haircut `D_t`, `B_{t−1} D_t/P_t = V_t`; for
`B D > 0` and `V > 0` the price level is still determined, `P_t = B D/V`. -/
theorem haircut_price_unique {B D V : ℝ} (hBD : 0 < B * D) (hV : 0 < V) :
    ∃! P : ℝ, 0 < P ∧ B * D / P = V :=
  PresentValue.valuation_price_unique hBD hV

/-- Cochrane (2023), §8.5, p. 254: "An unexpected partial default allows the government to adapt
to a negative surplus shock with less or no inflation": if the price level `P` satisfied
`B/P = V` before the present value fell to `V'`, it still satisfies (8.5) with haircut `D` iff
`D = V'/V`. -/
theorem haircut_offsets_shock {B D V V' P : ℝ} (hV : V ≠ 0) (h0 : B / P = V) :
    B * D / P = V' ↔ D = V' / V := by
  have h1 : B * D / P = D * V := by rw [← h0]; ring
  rw [h1, eq_div_iff hV]

/-! ### (8.6)–(8.7): expected haircuts -/

/-- Cochrane (2023), eq. (8.7), p. 254: the nominal bond price with an expected haircut,
`Q_t = β E_t(P_t D_{t+1}/P_{t+1})`. -/
noncomputable def bondPrice (β : ℝ) (P D : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  β • 𝔼.E t (P t * D (t + 1) / P (t + 1))

/-- Cochrane (2023), eq. (8.6), p. 254, with a haircut at every date:
`B_{t−1} D_t/P_t = s_t + Q_t B_t/P_t` (the book's (8.6) is the case `D_t = 1`). -/
def DefaultFlow (β : ℝ) (B D P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, B t * D t / P t = s t + bondPrice 𝔼 β P D t * B (t + 1) / P t

/-- Cochrane (2023), eqs. (8.6)–(8.7), p. 254: with the pull-out property, an adapted nowhere-zero
price level and debt `B_t` chosen at `t`, the real revenue from bond sales is
`Q_t B_t/P_t = β E_t(B_t D_{t+1}/P_{t+1})`. -/
theorem revenue_eq (hPO : 𝔼.PullOut) {β : ℝ} {B D P : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) (t : ℕ) :
    bondPrice 𝔼 β P D t * B (t + 1) / P t =
      β • 𝔼.E t (B (t + 1) * D (t + 1) / P (t + 1)) := by
  have e1 : P t * D (t + 1) / P (t + 1) = P t * (D (t + 1) / P (t + 1)) := mul_div_assoc _ _ _
  have e2 : B (t + 1) * D (t + 1) / P (t + 1) = B (t + 1) * (D (t + 1) / P (t + 1)) :=
    mul_div_assoc _ _ _
  rw [bondPrice, e1, e2, hPO t (P t) _ (hPa t), hPO t (B (t + 1)) _ (hBpre t)]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hP t ω]

/-- Cochrane (2023), eq. (8.6), p. 254: the flow with haircuts is the real recursion
`v_t = s_t + β E_t v_{t+1}` for the post-haircut real value `v_t = B_{t−1} D_t/P_t`. -/
theorem defaultFlow_iff_solves (hPO : 𝔼.PullOut) {β : ℝ} {B D P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    DefaultFlow 𝔼 β B D P s ↔ ForwardSolution.Solves 𝔼 β s (fun t => B t * D t / P t) := by
  simp only [DefaultFlow, ForwardSolution.Solves, revenue_eq 𝔼 hPO hPa hP hBpre]
  constructor
  · intro h t
    rw [h t, add_comm]
  · intro h t
    rw [h t, add_comm]

/-- Cochrane (2023), eqs. (8.5)–(8.6), p. 254: for bounded adapted surpluses and `0 ≤ β < 1`,
the flow with haircuts plus the transversality condition is equivalent to the valuation
equation `B_{t−1} D_t/P_t = E_t ∑ βʲ s_{t+j}` at every date. -/
theorem default_valuation_iff (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {B D P s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    (DefaultFlow 𝔼 β B D P s ∧ TVC 𝔼 β (fun t => B t * D t / P t)) ↔
      ∀ t, B t * D t / P t = pv 𝔼 β s t := by
  rw [defaultFlow_iff_solves 𝔼 hPO hPa hP hBpre, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs hsa, funext_iff]

/-- Cochrane (2023), eq. (8.6), p. 254 (present-value form): in an equilibrium the real revenue
from new bonds is the present value of surpluses from `t + 1` on, whatever the expected haircut:
`B_{t−1} D_t/P_t = s_t + Q_t B_t/P_t = s_t + E_t ∑_{j ≥ 1} βʲ s_{t+j}`. -/
theorem default_flow_pv (hPO : 𝔼.PullOut) {β : ℝ} {B D P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1))
    (hflow : DefaultFlow 𝔼 β B D P s) (hval : ∀ t, B t * D t / P t = pv 𝔼 β s t) (t : ℕ) :
    B t * D t / P t = s t + 𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * s (t + 1 + j) ω) := by
  rw [hflow t, revenue_eq 𝔼 hPO hPa hP hBpre t, hval (t + 1), pv,
    𝔼.tower (Nat.le_succ t), ← map_smul]
  congr 2
  funext ω
  simp only [epv, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), §8.5, p. 254: "If at time `t` people expect a partial default `D_{t+1} < 1`,
with no change in surpluses, this change has no effect on the current price level": two
equilibria with the same surpluses and the same post-haircut maturing debt at `t` have the same
`P_t`, whatever the expected haircuts and new debt. -/
theorem expected_default_no_effect {β : ℝ} {s B D P B' D' P' : ℕ → Ω → ℝ}
    (hv : ∀ t, B t * D t / P t = pv 𝔼 β s t) (hv' : ∀ t, B' t * D' t / P' t = pv 𝔼 β s t)
    {t : ℕ} {ω : Ω} (hBD : B t ω * D t ω = B' t ω * D' t ω) (hpv : pv 𝔼 β s t ω ≠ 0)
    (hP : P t ω ≠ 0) (hP' : P' t ω ≠ 0) : P t ω = P' t ω := by
  have h1 := congrFun (hv t) ω
  have h2 := congrFun (hv' t) ω
  simp only [Pi.div_apply, Pi.mul_apply] at h1 h2
  have hnum : B t ω * D t ω ≠ 0 := by
    intro h0
    rw [h0, zero_div] at h1
    exact hpv h1.symm
  rw [div_eq_iff hP] at h1
  rw [div_eq_iff hP'] at h2
  rw [← hBD] at h2
  exact mul_left_cancel₀ hpv (h1.symm.trans h2)

/-- Cochrane (2023), eq. (8.7), p. 254: when the haircut `D_{t+1}` is announced at `t` (known at
`t`), the bond price is proportional to it, `Q_t = β P_t D_{t+1} E_t(1/P_{t+1})`: an expected
default lowers bond prices. -/
theorem bondPrice_known_haircut (hPO : 𝔼.PullOut) {β : ℝ} {P D : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) {t : ℕ} (hD : 𝔼.E t (D (t + 1)) = D (t + 1)) :
    bondPrice 𝔼 β P D t = β • (P t * D (t + 1) * 𝔼.E t (P (t + 1))⁻¹) := by
  have hPD : 𝔼.E t (P t * D (t + 1)) = P t * D (t + 1) := by
    rw [hPO t (P t) (D (t + 1)) (hPa t), hD]
  rw [bondPrice, div_eq_mul_inv, hPO t _ _ hPD]

/-! ### p. 255: the interest rate is free -/

/-- Cochrane (2023), §8.5, p. 255: scaling the expected haircut by `1/k` (a deterministic
`k ≠ 0`) scales the bond price by `1/k`. -/
theorem bondPrice_scale {β : ℝ} {P D : ℕ → Ω → ℝ} {k : ℕ → ℝ} (t : ℕ) :
    bondPrice 𝔼 β P (fun t => (k t)⁻¹ • D t) t = (k (t + 1))⁻¹ • bondPrice 𝔼 β P D t := by
  have e : P t * (k (t + 1))⁻¹ • D (t + 1) / P (t + 1) =
      (k (t + 1))⁻¹ • (P t * D (t + 1) / P (t + 1)) := by
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [bondPrice, bondPrice, e, map_smul, smul_comm]

/-- Cochrane (2023), §8.5, p. 255: "Selling 2 bonds when people expect a 50% haircut is exactly
the same as selling 1 bond when people expect no haircut, except nominal bond prices fall by
half": the flow with haircuts is invariant under `(B_t, D_t) ↦ (k_t B_t, D_t/k_t)` for any
deterministic `k_t ≠ 0`, with the same price level. -/
theorem scaled_flow_iff {β : ℝ} {B D P s : ℕ → Ω → ℝ} {k : ℕ → ℝ} (hk : ∀ t, k t ≠ 0) :
    DefaultFlow 𝔼 β (fun t => k t • B t) (fun t => (k t)⁻¹ • D t) P s ↔
      DefaultFlow 𝔼 β B D P s := by
  have h1 : ∀ t, k t • B t * (k t)⁻¹ • D t = B t * D t := by
    intro t
    funext ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hk t]
  have h2 : ∀ t, bondPrice 𝔼 β P (fun t => (k t)⁻¹ • D t) t * k (t + 1) • B (t + 1) =
      bondPrice 𝔼 β P D t * B (t + 1) := by
    intro t
    rw [bondPrice_scale]
    funext ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hk (t + 1)]
  simp only [DefaultFlow, h1, h2]

/-- Cochrane (2023), §8.5, p. 255 (the book's example): with a 50% expected haircut the bond price
is half the no-haircut price. -/
theorem two_bonds_half_haircut {β : ℝ} {P D : ℕ → Ω → ℝ} (t : ℕ) :
    bondPrice 𝔼 β P (fun t => (2 : ℝ)⁻¹ • D t) t = (2 : ℝ)⁻¹ • bondPrice 𝔼 β P D t :=
  bondPrice_scale 𝔼 (k := fun _ => 2) t

/-- Cochrane (2023), §8.5, p. 255 (perfect foresight): if the government holds `Q_t` fixed, the
real revenue condition `Q_t B_t/P_t = β V_{t+1}` and the valuation `B_t D_{t+1}/P_{t+1} = V_{t+1}`
give `B_t = β V_{t+1} P_t/Q_t`, independent of the haircut, and `P_{t+1} = β P_t D_{t+1}/Q_t`: the
same as selling `D_{t+1} B_t` bonds with no haircut. -/
theorem fixedQ_perfectForesight {β P Q B D P1 V1 : ℝ} (hP : P ≠ 0) (hQ : Q ≠ 0) (hV1 : V1 ≠ 0)
    (hP1 : P1 ≠ 0) (hrev : Q * B / P = β * V1) (hval : B * D / P1 = V1) :
    B = β * V1 * P / Q ∧ P1 = β * P * D / Q := by
  have hB : B = β * V1 * P / Q := by
    rw [eq_div_iff hQ, ← hrev]
    field_simp
  refine ⟨hB, ?_⟩
  rw [div_eq_iff hP1] at hval
  rw [eq_div_iff hQ]
  have : V1 * P1 * Q = V1 * (β * P * D) := by
    rw [← hval, hB]
    field_simp
  have := mul_left_cancel₀ hV1 (by rw [← this]; ring : V1 * (P1 * Q) = V1 * (β * P * D))
  linarith

/-- Cochrane (2023), §8.5, p. 255: "if the government sticks to the nominal interest-rate target
... the expected future price level `P_{t+1}` declines": `β P_t D/Q_t` is strictly increasing in
the haircut factor `D`. -/
theorem fixedQ_next_price_mono {β P Q D D' : ℝ} (hβ : 0 < β) (hP : 0 < P) (hQ : 0 < Q)
    (hD : D' < D) : β * P * D' / Q < β * P * D / Q := by
  apply div_lt_div_of_pos_right _ hQ
  exact mul_lt_mul_of_pos_left hD (mul_pos hβ hP)

/-! ### p. 255: the 10% haircut example (survey E8.1) -/

/-- Cochrane (2023), §8.5, p. 255: a 10% haircut at `t + 1` with surpluses from `t + 1` on 10%
lower (`V ↦ 0.9 V`, `s_t` unchanged) raises the price level by the exact factor
`(s_t + V)/(s_t + 0.9 V)`. -/
theorem haircut_ten_percent {B s V P P' : ℝ} (hB : B ≠ 0) (hsV : s + V ≠ 0)
    (hsV' : s + 9 / 10 * V ≠ 0) (hP : B / P = s + V) (hP' : B / P' = s + 9 / 10 * V) :
    P' / P = (s + V) / (s + 9 / 10 * V) := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, div_zero] at hP
    exact hsV hP.symm
  have hP0' : P' ≠ 0 := by
    intro h
    rw [h, div_zero] at hP'
    exact hsV' hP'.symm
  have e1 : P = B / (s + V) := by rw [eq_div_iff hsV, ← hP]; field_simp
  have e2 : P' = B / (s + 9 / 10 * V) := by rw [eq_div_iff hsV', ← hP']; field_simp
  rw [e1, e2]
  field_simp

/-- Cochrane (2023), §8.5, p. 255 (survey E8.1): the price-level factor is exactly `10/9` (an
11.1% rise) iff `s_t = 0`. -/
theorem haircut_factor_eq_iff {s V : ℝ} (hs' : 0 < s + 9 / 10 * V) :
    (s + V) / (s + 9 / 10 * V) = 10 / 9 ↔ s = 0 := by
  rw [div_eq_iff hs'.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.5, p. 255 (survey E8.1): with a positive current surplus `s_t > 0` the
price-level factor is strictly below `10/9`. -/
theorem haircut_factor_lt {s V : ℝ} (hV : 0 < V) (hs : 0 < s) :
    (s + V) / (s + 9 / 10 * V) < 10 / 9 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- Cochrane (2023), §8.5, p. 255 (survey E8.1): the value of money `1/P` falls by exactly 10%,
`(s + 0.9 V)/(s + V) = 9/10`, iff `s_t = 0` (for `s + V > 0`); the book's "raises the price level
today by 10%" is the first-order version of this. -/
theorem money_value_ten_percent_iff {s V : ℝ} (hsV : 0 < s + V) :
    (s + 9 / 10 * V) / (s + V) = 9 / 10 ↔ s = 0 := by
  rw [div_eq_iff hsV.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.5, p. 255 (perfect foresight): "If the government allows the interest
rate to rise, to follow the increased default premium, then by (8.7), the expected price level at
`t + 1` is also ... higher": with inflation `P_{t+1}/P_t` unchanged, `P_{t+1}` rises by the same
factor as `P_t`, and the bond price `Q_t = β P_t D_{t+1}/P_{t+1}` falls by the factor `D'/D`. -/
theorem rate_follows_premium {β P P1 P' P1' D D' : ℝ} (hP : P ≠ 0) (hP1 : P1 ≠ 0)
    (hP' : P' ≠ 0) (hD : D ≠ 0) (hinf : P1' / P' = P1 / P) :
    P1' / P1 = P' / P ∧ β * P' * D' / P1' = D' / D * (β * P * D / P1) := by
  have h : P1' = P1 * P' / P := by
    rw [div_eq_iff hP'] at hinf
    rw [hinf]
    field_simp
  constructor
  · rw [h]
    field_simp
  · rw [h]
    field_simp

end Cochrane.AssetsRulesBalanceSheets.Default
