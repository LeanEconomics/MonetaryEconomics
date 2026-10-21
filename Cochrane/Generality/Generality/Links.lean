/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.LogLinearIdentities
import Generality.StochasticDiscount
import Generality.Ratios
import Generality.ContinuousLong
import Generality.ContinuousMoney

/-!
# Links between the Chapter 3 developments

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, *Generality*, §§3.1–3.6
(pp. 53–80), and Online Appendix A1 (pp. 557–569). The chapter was formalised in four
independent chains (long-term debt and stochastic discounting; money and the log-linear
identities; continuous time with short and long debt; continuous linearised identities and
money). This module proves that their objects agree where the book talks about the same thing.

## Main results

* Discrete valuation machinery: the money chain's present-value relation and transversality
  condition (`Money.PVRel`, `Money.TVC`, levels of `Λ`) are the long-term-debt chain's
  `LongTermDebt.pv` and `LongTermDebt.TVC` with one-period factor `m_t = Λ_{t+1}/Λ_t`
  (`pvRel_iff_pv`, `tvc_money_iff_tvc`); the money chain's undiscounted recursion is
  `LongTermDebt.FlowRec` with `m ≡ 1` (`flowRec_one_iff`, `tvc_one_iff`).
* (3.5) with `Λ_t = βᵗ` is the constant-`β` valuation of (3.3) and Chapter 2 (`sdf_ratio_pow`,
  `pv_beta_pow`, `pv_lambda_beta`, `valuation_sdf_beta_iff`).
* Short-term debt as a special case: the geometric maturity structure with `ω = 0` is one-period
  debt, and `LongTermDebt.valuationGeom_iff` at `ω = 0` is exactly
  `StochasticDiscount.valuation_sdf_iff` (`annuity_zero`, `geomValue_zero`, `geomFlow_zero_iff`,
  `zeroPrice_one_eq_bondPrice`, `geomFlow_zero_iff_flowOne`, `valuationGeom_zero_iff`); in
  continuous time it is the limit `ϖ → ∞` (`short_debt_limits`), and the discrete jump ratio at
  `ω = e^{−ϖ}` has the same limit (`jumpRatio_tendsto_short`).
* Weights: the discrete (3.22) weights `ω̂ʲ`, `ρʲ` and the continuous (3.51) weights
  `e^{−(r+ϖ)τ}`, `e^{−rτ}` agree on the integer grid with `ω = e^{−ϖ}`, `1 + i = e^r`,
  `ρ = e^{−r}`, `ω̂ = ω/(1+i)` (`bond_coeff_exp`, `weights_322_351`, `omega_disc_endpoints`).
* Discretisation limits: with period length `h`, the discrete geometric annuity `h·(1+i)/(1+i−ω)`
  tends to the continuous bond price `1/(i+ϖ)` that solves `Q' = (i+ϖ)Q − 1`
  (`annuity_tendsto_bondPrice`), and the discrete jump ratio (1.16) tends to the continuous
  (1.18) `(r+ϖ)/(i+ϖ)` (`jumpRatio_tendsto_continuous`).
* E15 reconciled in one statement (`e15_reconciled`): exact proportional drop 3.41%, exact log
  drop in (3.46%, 3.48%), linear drop 4% with weight `ω`, 3.48% with the exact weight `ω/(1+i)`.
* Innovations: `Ratios.E_innov_zero` is `E_t ΔE_{t+1} = 0` for `LogLinearIdentities.innov`
  (`E_innov_eq_zero`); `LogLinearIdentities.geomQ` is `LongTermDebt.geom_value/(1+i)`
  (`geomQ_eq_geom_value_div`).
* Continuous engines: the general-discount-factor engine of `ContinuousLinear` applied to
  `Λ = ContinuousShort.disc r t` gives the valuation/TVC equivalence of `ContinuousShort` for
  every continuous rate (`hasDerivAt_disc_of_continuous`, `tvc_iff_pv_of_engine`); the constant-
  rate discount factors agree (`expDisc_ratio_eq_disc`).
* E13 in discrete and continuous time (`e13_discrete_and_continuous`).
* (3.26), p. 68, prints the scaled surplus `s̃` inside the nonlinear valuation equation; with
  `s̃ = κs` the printed equation is compatible with (3.3) only if `κ = 1` or the value of debt is
  zero (`eq_3_26_printed_iff`).
-/

namespace Cochrane.Generality.Links

open Filter Topology MeasureTheory

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Discrete valuation machinery: `Money` versus `LongTermDebt` -/

/-- Cochrane (2023), (3.5) and (3.10)–(3.12), pp. 55–59: the money chain's present-value
relation `X_t/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)d_{t+j}]` is the long-term-debt chain's present value
with one-period factor `m_s = Λ_{s+1}/Λ_s`. -/
theorem pvRel_iff_pv {Λ P X d : ℕ → Ω → ℝ} (hΛ : ∀ s ξ, Λ s ξ ≠ 0) (t : ℕ) (ω : Ω) :
    Money.PVRel 𝔼 Λ P X d t ω ↔
      X t ω / P t ω = LongTermDebt.pv 𝔼 (fun s ξ => Λ (s + 1) ξ / Λ s ξ) d t ω := by
  rw [StochasticDiscount.pv_lambda 𝔼 hΛ (fun _ => rfl) t]
  rfl

/-- Cochrane (2023), p. 55: under the money chain's standing assumptions, its transversality
condition `E_t[Λ_{t+T}X_{t+T}/P_{t+T}] → 0` (in every state) is the long-term-debt chain's
`E_t[(Λ_{t+T}/Λ_t)x_{t+T}] → 0` for the real value `x = X/P` and `m_s = Λ_{s+1}/Λ_s`. -/
theorem tvc_money_iff_tvc {Λ P i M B X : ℕ → Ω → ℝ} (hS : Money.Standing 𝔼 Λ P i M B)
    (t : ℕ) :
    (∀ ω, Money.TVC 𝔼 Λ P X t ω) ↔
      LongTermDebt.TVC 𝔼 (fun s ξ => Λ (s + 1) ξ / Λ s ξ) (fun s ξ => X s ξ / P s ξ) t := by
  have hΛ : ∀ s ξ, Λ s ξ ≠ 0 := fun s ξ => (hS.disc_pos s ξ).ne'
  have key : ∀ N ω, 𝔼.E t (LongTermDebt.sdf (fun s ξ => Λ (s + 1) ξ / Λ s ξ) t N *
      (fun s ξ => X s ξ / P s ξ) (t + N)) ω =
      (Λ t ω)⁻¹ * 𝔼.E t (fun ω' => Λ (t + N) ω' * (X (t + N) ω' / P (t + N) ω')) ω := by
    intro N ω
    rw [StochasticDiscount.sdf_eq_ratio hΛ (fun _ => rfl) t N]
    exact Money.E_ratio 𝔼 hS t N (fun s ξ => X s ξ / P s ξ) ω
  unfold LongTermDebt.TVC Money.TVC
  simp_rw [key]
  constructor
  · intro h ω
    simpa using (h ω).const_mul (Λ t ω)⁻¹
  · intro h ω
    simpa [mul_inv_cancel_left₀ (hΛ t ω)] using (h ω).const_mul (Λ t ω)

/-- Cochrane (2023), footnote 1, p. 58, and p. 55: the money chain's recursion
`Y_t = c_t + E_tY_{t+1}` (used in `Money.telescope`, `Money.pv_iff_tvc`) is the long-term-debt
flow condition `LongTermDebt.FlowRec` with the one-period factor `m ≡ 1`. -/
theorem flowRec_one_iff {Y c : ℕ → Ω → ℝ} :
    LongTermDebt.FlowRec 𝔼 (fun _ _ => 1) c Y ↔ ∀ t, Y t = c t + 𝔼.E t (Y (t + 1)) := by
  have h1 : ∀ x : Ω → ℝ, (fun _ : Ω => (1 : ℝ)) * x = x := fun x => funext fun _ => one_mul _
  simp only [LongTermDebt.FlowRec, h1]

/-- Cochrane (2023), p. 55 and footnote 1, p. 58: with `m ≡ 1` the long-term-debt
transversality condition is the money chain's `E_tY_{t+T} → 0` (`Money.pv_iff_tvc`). -/
theorem tvc_one_iff {Y : ℕ → Ω → ℝ} (t : ℕ) :
    LongTermDebt.TVC 𝔼 (fun _ _ => 1) Y t ↔
      ∀ ω, Tendsto (fun T => 𝔼.E t (Y (t + T)) ω) atTop (𝓝 0) := by
  have h2 : ∀ x : Ω → ℝ, (fun _ : Ω => (1 : ℝ)) * x = x := fun x => funext fun _ => one_mul _
  simp only [LongTermDebt.TVC, LongTermDebt.sdf_const, one_pow, h2]

/-! ### (3.5) with `Λ_t = βᵗ`: the constant-`β` valuation -/

/-- Cochrane (2023), p. 55: with `Λ_t = βᵗ`, `β ≠ 0`, the one-period factor `Λ_{t+1}/Λ_t` is the
constant `β`. -/
theorem sdf_ratio_pow {β : ℝ} (hβ : β ≠ 0) :
    (fun s (_ : Ω) => β ^ (s + 1) / β ^ s) = fun _ _ => β := by
  funext s _
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), (3.5), p. 55, with `Λ_t = βᵗ`: the present value is (3.3)'s
`∑_n βⁿE_ts_{t+n}`. -/
theorem pv_beta_pow {β : ℝ} (hβ : β ≠ 0) (s : ℕ → Ω → ℝ) (t : ℕ) :
    LongTermDebt.pv 𝔼 (fun s (_ : Ω) => β ^ (s + 1) / β ^ s) s t =
      fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  rw [sdf_ratio_pow hβ]
  exact LongTermDebt.pv_const 𝔼 β s t

/-- Cochrane (2023), (3.5), p. 55, as printed with `Λ_t = βᵗ`:
`∑_j E_t[(β^{t+j}/βᵗ)s_{t+j}] = ∑_j βʲE_ts_{t+j}`, the right-hand side of (3.3) and (2.7). -/
theorem pv_lambda_beta {β : ℝ} (hβ : β ≠ 0) (s : ℕ → Ω → ℝ) (t : ℕ) :
    (fun ξ => ∑' j, 𝔼.E t (fun ξ' => β ^ (t + j) / β ^ t * s (t + j) ξ') ξ) =
      fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  have h := StochasticDiscount.pv_lambda 𝔼 (Λ := fun s (_ : Ω) => β ^ s)
    (m := fun s (_ : Ω) => β ^ (s + 1) / β ^ s) (s := s) (fun s _ => pow_ne_zero s hβ)
    (fun _ => rfl) t
  rw [← h]
  exact pv_beta_pow 𝔼 hβ s t

/-- Cochrane (2023), (3.5), p. 55, specialised to `Λ_t = βᵗ` (`m ≡ β`, `0 ≤ β`): the flow with
the bond price `Q_t = E_t[βP_t/P_{t+1}]` and the transversality condition at every date hold iff
`B_{t−1}/P_t = ∑_n βⁿE_ts_{t+n}` at every date — the constant-`β` valuation of (3.3)
(`LongTermDebt.valuationLT_iff_const`) and of Chapter 2 for one-period debt. -/
theorem valuation_sdf_beta_iff (hMC : LongTermDebt.MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {β : ℝ} (hβ : 0 ≤ β) {P s D : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hs : LongTermDebt.SurplusSummable 𝔼 (fun _ _ => β) s) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hD1 : ∀ t, 𝔼.E t (D (t + 1)) = D (t + 1))
    (hx : 𝔼.Adapted (StochasticDiscount.realDebt D P)) :
    ((∀ t, StochasticDiscount.FlowOne (StochasticDiscount.bondPrice 𝔼 (fun _ _ => β) P) P s D t)
        ∧ ∀ t, LongTermDebt.TVC 𝔼 (fun _ _ => β) (StochasticDiscount.realDebt D P) t) ↔
      ∀ t, StochasticDiscount.realDebt D P t = fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  rw [StochasticDiscount.valuation_sdf_iff 𝔼 hMC hP (fun s => 𝔼.const (s + 1) β)
    (fun _ _ => hβ) hsa hs hPa hP0 hD1 hx]
  simp only [LongTermDebt.pv_const]

/-! ### Short-term debt as the `ω = 0` case of geometric debt -/

/-- Cochrane (2023), A1 (1.14), p. 559: with `ω = 0` the geometric portfolio is the maturing
bond only, `∑_j 0ʲQ_t^{(t+j)} = Q_t^{(t)}`. -/
theorem annuity_zero (Q : ℕ → ℕ → Ω → ℝ) (t : ℕ) : LongTermDebt.annuity 0 Q t = Q t 0 := by
  funext ξ
  simp only [LongTermDebt.annuity]
  rw [tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
  simp

/-- Cochrane (2023), A1 p. 559 and (3.1): with `ω = 0` and bonds priced by (3.1)
(`Q_t^{(t)} = 1`), the real value of geometric debt is `b_t/P_t`, the real value of one-period
debt of Chapter 2. -/
theorem geomValue_zero {m P b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : LongTermDebt.ZeroPrice 𝔼 m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0) (t : ℕ) :
    LongTermDebt.geomValue 0 Q b P t = StochasticDiscount.realDebt b P t := by
  funext ξ
  simp only [LongTermDebt.geomValue, annuity_zero, LongTermDebt.zeroPrice_zero 𝔼 hQ (hP0 t),
    StochasticDiscount.realDebt, Pi.one_apply, one_mul]

/-- Cochrane (2023), (3.2), p. 53, with the geometric structure at `ω = 0`: the flow is the
one-period flow `b_t = P_ts_t + Q_t^{(t+1)}b_{t+1}`. -/
theorem geomFlow_zero_iff {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (t : ℕ) :
    LongTermDebt.GeomFlow 0 P s b Q t ↔ ∀ ξ, b t ξ = P t ξ * s t ξ + Q t 1 ξ * b (t + 1) ξ := by
  have h : ∀ ξ, ∑' j, Q t (j + 1) ξ * ((0 : ℝ) ^ j * b (t + 1) ξ - 0 ^ (j + 1) * b t ξ) =
      Q t 1 ξ * b (t + 1) ξ := by
    intro ξ
    rw [tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
    simp
  simp only [LongTermDebt.GeomFlow, h]

/-- Cochrane (2023), (3.1) and p. 55: the price of the bond maturing next period is the
one-period bond price, `Q_t^{(t+1)} = E_t[m_tP_t/P_{t+1}]`. -/
theorem zeroPrice_one_eq_bondPrice {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : LongTermDebt.ZeroPrice 𝔼 m P Q) (t : ℕ) :
    Q t 1 = StochasticDiscount.bondPrice 𝔼 m P t := by
  rw [hQ t 1, LongTermDebt.sdf_one]
  rfl

/-- Cochrane (2023), (3.2), p. 53, and §3.3, p. 55: for `ω = 0`, the geometric flow is the
one-period flow `B_{t−1}/P_t = s_t + Q_tB_t/P_t` of `StochasticDiscount.FlowOne`. -/
theorem geomFlow_zero_iff_flowOne {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (t : ℕ) :
    LongTermDebt.GeomFlow 0 P s b Q t ↔ StochasticDiscount.FlowOne (fun t => Q t 1) P s b t := by
  rw [geomFlow_zero_iff]
  unfold StochasticDiscount.FlowOne
  refine forall_congr' fun ξ => ?_
  have hp := hP0 t ξ
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    field_simp at h
    linarith

/-- Cochrane (2023), (3.1)–(3.3), p. 53, and (3.5), p. 55: **short-term debt is the `ω = 0`
case.** The geometric-maturity valuation theorem `LongTermDebt.valuationGeom_iff` at `ω = 0` is
exactly the one-period stochastic-discount valuation theorem
`StochasticDiscount.valuation_sdf_iff`: flow with `Q_t = E_t[m_tP_t/P_{t+1}]` plus TVC at every
date iff `B_{t−1}/P_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` at every date. -/
theorem valuationGeom_zero_iff (hMC : LongTermDebt.MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hsa : 𝔼.Adapted s)
    (hs : LongTermDebt.SurplusSummable 𝔼 m s) (hQ : LongTermDebt.ZeroPrice 𝔼 m P Q)
    (hPa : 𝔼.Adapted P) (hPpos : ∀ s ξ, 0 < P s ξ)
    (hb : 𝔼.Adapted b) (hb1 : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) :
    ((∀ t, StochasticDiscount.FlowOne (StochasticDiscount.bondPrice 𝔼 m P) P s b t) ∧
        ∀ t, LongTermDebt.TVC 𝔼 m (StochasticDiscount.realDebt b P) t) ↔
      ∀ t, StochasticDiscount.realDebt b P t = LongTermDebt.pv 𝔼 m s t := by
  have hP0 : ∀ s ξ, P s ξ ≠ 0 := fun s ξ => (hPpos s ξ).ne'
  have hQs : ∀ t ξ, Summable fun j => (0 : ℝ) ^ j * Q t j ξ := fun t ξ =>
    (hasSum_single 0 fun j hj => by simp [zero_pow hj]).summable
  have h := LongTermDebt.valuationGeom_iff 𝔼 hMC hP le_rfl hm hm0 hsa hs hQ hPa hPpos hQs hb hb1
  have hv : LongTermDebt.geomValue 0 Q b P = StochasticDiscount.realDebt b P :=
    funext (geomValue_zero 𝔼 hQ hP0)
  have hQ1 : (fun t => Q t 1) = StochasticDiscount.bondPrice 𝔼 m P :=
    funext (zeroPrice_one_eq_bondPrice 𝔼 hQ)
  rw [hv] at h
  simp only [geomFlow_zero_iff_flowOne hP0, hQ1] at h
  exact h

/-- Cochrane (2023), A1 p. 560 ("`ϖ = ∞` is instantaneous debt") and E20, discrete and
continuous: with discrete geometric decay `ω = e^{−ϖ}`, the exact discrete jump ratio (1.16)
tends to `1` as `ϖ → ∞` (its value at `ω = 0`, `LongTermDebt.price_jump_omega_zero`). -/
theorem jumpRatio_tendsto_short {r i : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) :
    Tendsto (fun ϖ : ℝ => LongTermDebt.jumpRatio r i (Real.exp (-ϖ))) atTop (𝓝 1) := by
  have he : Tendsto (fun ϖ : ℝ => Real.exp (-ϖ)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hc : ContinuousAt (fun w => LongTermDebt.jumpRatio r i w) 0 := by
    unfold LongTermDebt.jumpRatio
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero hr.ne' (by rw [sub_zero]; exact hi.ne'))
  have h := hc.tendsto.comp he
  rwa [LongTermDebt.price_jump_omega_zero hr hi] at h

/-- Cochrane (2023), A1 pp. 559–560 and pp. 78–79 (E20): short-term debt is `ω = 0` in discrete
time and `ϖ → ∞` in continuous time. In continuous time the book-normalised bundle value
`ϖQ = ϖ/(i₀ + ϖ)` tends to `1` (`ContinuousLong.bondPrice`) and the jump ratio
`(r+ϖ)/(i+ϖ)` of (1.18) tends to `1`; the discrete decay `e^{−ϖ}` tends to `0` and the discrete
jump ratio is `1` at `ω = 0`. -/
theorem short_debt_limits {r i i₀ : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) (t : ℝ) :
    Tendsto (fun ϖ : ℝ => ϖ * ContinuousLong.bondPrice (fun _ => i₀) ϖ t) atTop (𝓝 1) ∧
      Tendsto (fun ϖ : ℝ => (r + ϖ) / (i + ϖ)) atTop (𝓝 1) ∧
      Tendsto (fun ϖ : ℝ => Real.exp (-ϖ)) atTop (𝓝 0) ∧
      LongTermDebt.jumpRatio r i 0 = 1 := by
  refine ⟨?_, ContinuousLong.price_jump_tendsto_one r i, Real.tendsto_exp_neg_atTop_nhds_zero,
    LongTermDebt.price_jump_omega_zero hr hi⟩
  refine (ContinuousLong.tendsto_book_bondValue i₀).congr' ?_
  filter_upwards [eventually_gt_atTop (-i₀)] with ϖ hϖ
  rw [ContinuousLong.bondPrice_const (by linarith) t]

/-! ### Discrete (3.22) and continuous (3.51) weights -/

/-- Cochrane (2023), A1 (1.22), p. 563, and (3.47), p. 77: with discrete decay `ω = e^{−ϖ}` and
a steady-state nominal rate `1 + i = e^r` (no inflation), the exact discrete coefficient
`ω̂ = ω/(1+i)` is the continuous `e^{−(r+ϖ)}`. -/
theorem bond_coeff_exp (r ϖ : ℝ) : Real.exp (-ϖ) / Real.exp r = Real.exp (-(r + ϖ)) := by
  rw [← Real.exp_sub]
  ring_nf

/-- Cochrane (2023), (3.22), p. 65, and (3.51), p. 78: on the integer grid the discrete weights
agree with the continuous ones under `ω̂ = e^{−ϖ}/e^r` and `ρ = e^{−r}` (the log-linear `ρ` of
`LogLinearIdentities.rho_eq` with no growth): the inflation weight `ω̂ʲ = e^{−(r+ϖ)j}`, the
surplus weight `ρʲ = e^{−rj}`, and the discount-rate weight
`ρ^{j+1} − ω̂^{j+1} = e^{−r(j+1)} − e^{−(r+ϖ)(j+1)}`. -/
theorem weights_322_351 (r ϖ : ℝ) (j : ℕ) :
    (Real.exp (-ϖ) / Real.exp r) ^ j = Real.exp (-((r + ϖ) * j)) ∧
      Real.exp (-r) ^ j = Real.exp (-(r * j)) ∧
      Real.exp (-r) ^ (j + 1) - (Real.exp (-ϖ) / Real.exp r) ^ (j + 1) =
        Real.exp (-(r * ((j + 1 : ℕ) : ℝ))) - Real.exp (-((r + ϖ) * ((j + 1 : ℕ) : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bond_coeff_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  · rw [← Real.exp_nat_mul]
    congr 1
    ring
  · rw [bond_coeff_exp, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 2 <;> ring

/-- Cochrane (2023), A1 p. 560 and E20: under `ω = e^{−ϖ}` the perpetuity `ϖ = 0` is `ω = 1`,
short-term debt `ϖ → ∞` is `ω → 0`, and `ω̂ = e^{−(r+ϖ)} → 0` as well. -/
theorem omega_disc_endpoints (r : ℝ) :
    Real.exp (-(0 : ℝ)) = 1 ∧ Tendsto (fun ϖ : ℝ => Real.exp (-ϖ)) atTop (𝓝 0) ∧
      Tendsto (fun ϖ : ℝ => Real.exp (-ϖ) / Real.exp r) atTop (𝓝 0) := by
  refine ⟨by simp, Real.tendsto_exp_neg_atTop_nhds_zero, ?_⟩
  simpa using Real.tendsto_exp_neg_atTop_nhds_zero.div_const (Real.exp r)

/-! ### Discretisation limits: annuity and jump ratio -/

/-- Cochrane (2023), §3.6.2 and A1.2.1 (auxiliary): `(e^{ah} − e^{bh})/h → a − b` as `h → 0`. -/
theorem tendsto_slope_exp_sub (a b : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (a * h) - Real.exp (b * h)) / h) (𝓝[≠] 0) (𝓝 (a - b)) := by
  have ha : HasDerivAt (fun h : ℝ => Real.exp (a * h)) a 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul a).exp).congr_deriv (by simp)
  have hb : HasDerivAt (fun h : ℝ => Real.exp (b * h)) b 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul b).exp).congr_deriv (by simp)
  have h := (HasDerivAt.sub ha hb).tendsto_slope_zero
  simpa [div_eq_inv_mul] using h

/-- Cochrane (2023), A1 (1.14), p. 559, and (3.47)/A1 (1.17), pp. 77, 560: **the discrete
geometric annuity converges to the continuous bond price.** With period length `h > 0`,
per-period gross rate `1 + i_h = e^{ih}` and decay `ω_h = e^{−ϖh}`, the value of the geometric
portfolio per unit of coupon flow, `h·∑_j ω_hʲ/(1+i_h)ʲ = h(1+i_h)/(1+i_h−ω_h)`
(`LongTermDebt.geom_value`), tends to `ContinuousLong.bondPrice = 1/(i+ϖ)`, the solution of
`Q' = (i+ϖ)Q − 1`, as `h → 0`. -/
theorem annuity_tendsto_bondPrice {i ϖ : ℝ} (hiϖ : 0 < i + ϖ) (t : ℝ) :
    Tendsto (fun h : ℝ => h * ∑' j : ℕ, Real.exp (-ϖ * h) ^ j / Real.exp (i * h) ^ j)
      (𝓝[>] 0) (𝓝 (ContinuousLong.bondPrice (fun _ => i) ϖ t)) := by
  rw [ContinuousLong.bondPrice_const hiϖ t]
  have hs := (tendsto_slope_exp_sub i (-ϖ)).mono_left
    (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.mp hx).ne')
  have hex : Tendsto (fun h : ℝ => Real.exp (i * h)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun h : ℝ => Real.exp (i * h) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := hex.div hs (by rw [sub_neg_eq_add]; exact hiϖ.ne')
  rw [sub_neg_eq_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  have hlt : Real.exp (-ϖ * h) < 1 + (Real.exp (i * h) - 1) := by
    rw [add_sub_cancel]
    exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos hiϖ hh'])
  have g := LongTermDebt.geom_value (Real.exp_pos (-ϖ * h)).le hlt
  rw [add_sub_cancel] at g
  rw [g.tsum_eq]
  change Real.exp (i * h) / ((Real.exp (i * h) - Real.exp (-ϖ * h)) / h) =
    h * (Real.exp (i * h) / (Real.exp (i * h) - Real.exp (-ϖ * h)))
  rw [div_div_eq_mul_div]
  ring

/-- Cochrane (2023), A1 (1.16), p. 559, and (1.18), p. 560: **the discrete jump ratio converges
to the continuous one.** With period length `h`, `1 + r_h = e^{rh}`, `1 + i_h = e^{ih}` and
`ω_h = e^{−ϖh}`, the exact discrete ratio `LongTermDebt.jumpRatio r_h i_h ω_h` tends to
`(r+ϖ)/(i+ϖ)`, the continuous ratio of `ContinuousLong.price_jump_permanent`, as `h → 0`. -/
theorem jumpRatio_tendsto_continuous {r i ϖ : ℝ} (hiϖ : i + ϖ ≠ 0) :
    Tendsto (fun h : ℝ => LongTermDebt.jumpRatio (Real.exp (r * h) - 1) (Real.exp (i * h) - 1)
      (Real.exp (-ϖ * h))) (𝓝[≠] 0) (𝓝 ((r + ϖ) / (i + ϖ))) := by
  have hexp : ∀ c : ℝ, Tendsto (fun h : ℝ => Real.exp (c * h)) (𝓝[≠] 0) (𝓝 1) := fun c => by
    have hc : Continuous fun h : ℝ => Real.exp (c * h) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hnum := (hexp i).mul (tendsto_slope_exp_sub r (-ϖ))
  have hden := (hexp r).mul (tendsto_slope_exp_sub i (-ϖ))
  have hlim := hnum.div hden (by rw [one_mul, sub_neg_eq_add]; exact hiϖ)
  rw [one_mul, one_mul, sub_neg_eq_add, sub_neg_eq_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : h ≠ 0 := hh
  have e1 : ∀ x : ℝ, 1 + (x - 1) = x := fun x => by ring
  simp only [Pi.div_apply, LongTermDebt.jumpRatio, e1]
  rw [mul_div_assoc', mul_div_assoc', div_div_div_cancel_right₀ hh']

/-! ### E15 reconciled -/

/-- Cochrane (2023), A1 p. 560 and Figure 3.1, p. 69 (survey E15), one consistent statement set
at the figure's `r = 2%`, `i = 3%`, `ω = 0.8`: the exact proportional drop `1 − P_0/P` is
`40/1173 ∈ (3.41%, 3.42%)`; the exact log drop `−log(P_0/P)` is in `(3.46%, 3.48%)` (the text's
"3.5%"); the linear drop is `ω/(1−ω) = 4` (percent, Figure 3.1) with the printed weight `ω` and
`ω̂/(1−ω̂) = 80/23 ∈ (3.47, 3.48)` with the exact first-order weight `ω̂ = ω/(1+i)`. -/
theorem e15_reconciled :
    1 - LongTermDebt.jumpRatio 0.02 0.03 0.8 = 40 / 1173 ∧ (0.0341 : ℝ) < 40 / 1173 ∧
      (40 / 1173 : ℝ) < 0.0342 ∧ 0.0346 < -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) ∧
      -Real.log (LongTermDebt.jumpRatio 0.02 0.03 0.8) < 0.0348 ∧ (0.8 : ℝ) / (1 - 0.8) = 4 ∧
      (0.8 / 1.03 : ℝ) / (1 - 0.8 / 1.03) = 80 / 23 ∧ (3.47 : ℝ) < 80 / 23 ∧
      (80 / 23 : ℝ) < 3.48 :=
  ⟨LongTermDebt.omega_08_example.2.1, LongTermDebt.omega_08_example.2.2.1,
    LongTermDebt.omega_08_example.2.2.2, LogLinearIdentities.fig31_log.1,
    LogLinearIdentities.fig31_log.2, LogLinearIdentities.fig31_linear_exact_coeff⟩

/-! ### Innovations and bond prices -/

/-- Cochrane (2023), p. 54 and p. 64: `E_t ΔE_{t+1}X = 0` for the innovation operator
`LogLinearIdentities.innov` (this is `Ratios.E_innov_zero`). -/
theorem E_innov_eq_zero (t : ℕ) (X : Ω → ℝ) : 𝔼.E t (LogLinearIdentities.innov 𝔼 t X) = 0 :=
  Ratios.E_innov_zero 𝔼 t X

/-- Cochrane (2023), A1 (1.14) and (1.23), pp. 559, 563: the bond price of the geometric
portfolio `Q = ∑_j ωʲ/(1+i)^{j+1}` (`LogLinearIdentities.geomQ`) is the value
`∑_j ωʲ/(1+i)ʲ` of `LongTermDebt.geom_value` divided by `1 + i`. -/
theorem geomQ_eq_geom_value_div {i w : ℝ} (hw : 0 ≤ w) (hwi : w < 1 + i) :
    ∑' j : ℕ, w ^ j / (1 + i) ^ (j + 1) = (∑' j : ℕ, w ^ j / (1 + i) ^ j) / (1 + i) := by
  have hi : 0 < 1 + i := by linarith
  have habs : |w| < |1 + i| := by rw [abs_of_nonneg hw, abs_of_pos hi]; exact hwi
  rw [(LongTermDebt.geom_value hw hwi).tsum_eq, LogLinearIdentities.geomQ habs]
  have h1 : 1 + i - w ≠ 0 := by linarith
  field_simp

/-! ### The two continuous-time valuation engines -/

/-- Cochrane (2023), §3.6.1, p. 74: for a rate continuous on all of `ℝ`, the discount function
`D(t,·) = exp(−∫_t^· r)` satisfies `D' = −rD` at every date (so it is a discount factor in the
sense of `ContinuousLinear.tvc_iff_valuation`). -/
theorem hasDerivAt_disc_of_continuous {r : ℝ → ℝ} (hr : Continuous r) (t τ : ℝ) :
    HasDerivAt (ContinuousShort.disc r t) (-(r τ) * ContinuousShort.disc r t τ) τ := by
  have h1 : HasDerivAt (fun u => ContinuousShort.cumRate r t u) (r τ) τ :=
    (hr.integral_hasStrictDerivAt t τ).hasDerivAt
  have h2 := h1.neg.exp
  have h3 : HasDerivAt (ContinuousShort.disc r t)
      (Real.exp (-ContinuousShort.cumRate r t τ) * -(r τ)) τ := h2
  exact h3.congr_deriv (by rw [mul_comm]; rfl)

/-- Cochrane (2023), (3.31), p. 73, and A1.4, pp. 564–565: **the two engines agree.** Applying
the general discount-factor engine `ContinuousLinear.tvc_iff_valuation` to `Λ = D(t,·)` gives
`ContinuousShort`'s statement: along `V' = rV − s` on `[t, ∞)` with a continuous rate and
integrable discounted surpluses, the TVC `D(t,T)V(T) → 0` holds iff
`V(t) = ContinuousShort.pv r s t` (cf. `ContinuousShort.valuation_iff_tvc`, which instead
assumes `s` continuous and allows `V` to be only right-continuous at `t`). -/
theorem tvc_iff_pv_of_engine {r s V : ℝ → ℝ} {t : ℝ} (hr : Continuous r)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - s τ) τ)
    (hI : ContinuousShort.PVIntegrable r s t) :
    ContinuousShort.TVC r V t ↔ V t = ContinuousShort.pv r s t := by
  have h := ContinuousLinear.tvc_iff_valuation (Λ := ContinuousShort.disc r t) (r := r)
    (fun τ _ => hasDerivAt_disc_of_continuous hr t τ) (ContinuousShort.disc_pos r t t) hV hI
  simp only [ContinuousShort.disc_self, div_one] at h
  exact h

/-- Cochrane (2023), p. 74: the constant-rate discount factors of the two continuous chains
agree, `e^{−cτ}/e^{−ct} = D(t,τ)` for the constant rate `c`. -/
theorem expDisc_ratio_eq_disc (c t τ : ℝ) :
    Real.exp (-(c * τ)) / Real.exp (-(c * t)) = ContinuousShort.disc (fun _ => c) t τ := by
  rw [ContinuousLinear.expDisc_ratio, ContinuousShort.disc_const]

/-! ### E13 in discrete and continuous time -/

/-- Cochrane (2023), p. 57 and §3.6.4/A1.6, pp. 79, 567–569 (survey E13, both time settings):
the "seigniorage" valuation with `ΔM/P` and the "interest-saving" valuation with `iM/P` are not
equivalent without the money transversality condition. Discrete time (`Money.money_bubble`): a
perfect-foresight economy satisfying the standing assumptions and (3.9) in which (3.11) holds and
(3.10) fails at every date. Continuous time (`ContinuousMoney.printing_without_interest_example`):
with `P ≡ 1`, `N = e^{−ιτ}`, `M = e^{ιτ}`, `s = −ιe^{ιτ}`, (3.53) holds and (3.54) fails. In both,
real money grows at the interest rate. -/
theorem e13_discrete_and_continuous {β : ℝ} (hβ0 : 0 < β) (ι t : ℝ) :
    (∃ Λ P i M B s : ℕ → Unit → ℝ, Money.Standing perfectForesight Λ P i M B ∧
      Money.Flow39 P s i M B ∧
      (∀ t, Money.PVRel perfectForesight Λ P B (Money.term11 P s M) t ()) ∧
      (∀ t, ¬ Money.PVRel perfectForesight Λ P (B + M) (Money.term10 P s i M) t ())) ∧
    ((0 : ℝ) / 1 = ∫ τ in Set.Ioi t, Real.exp (-(ι * τ)) * 1 / (Real.exp (-(ι * t)) * 1) *
        (-(ι * Real.exp (ι * τ)) + ι * Real.exp (ι * τ) / 1) ∧
      (Real.exp (ι * t) + 0) / 1 ≠ ∫ τ in Set.Ioi t, Real.exp (-(ι * τ)) * 1 /
        (Real.exp (-(ι * t)) * 1) *
          (-(ι * Real.exp (ι * τ)) + (ι - 0) * Real.exp (ι * τ) / 1)) := by
  obtain ⟨Λ, P, i, M, B, s, h1, h2, -, -, h5, h6, -⟩ := Money.money_bubble hβ0
  have hc := ContinuousMoney.printing_without_interest_example ι t
  exact ⟨⟨Λ, P, i, M, B, s, h1, h2, h5, h6⟩, hc.2.2.2.1, hc.2.2.2.2⟩

/-! ### The misprint in (3.26) -/

/-- Cochrane (2023), (3.26), p. 68: the book prints the nonlinear valuation equation with the
*scaled* surplus `s̃` (`s̃ = ρ/(V/(Py))·s/y`, p. 63) on the right; the nonlinear equation is (3.3)
with `s` (`LongTermDebt.valuationLT_iff_const`). If (3.3) holds and `s̃ = κs` with a constant
scale `κ`, the printed (3.26) holds iff `κ = 1` or the value of debt is zero. -/
theorem eq_3_26_printed_iff {β κ : ℝ} {s : ℕ → Ω → ℝ} {x : Ω → ℝ} (t : ℕ) (ξ : Ω)
    (h33 : x ξ = ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ) :
    x ξ = ∑' n, β ^ n * 𝔼.E t (fun ξ' => κ * s (t + n) ξ') ξ ↔ κ = 1 ∨ x ξ = 0 := by
  have e : ∀ n, 𝔼.E t (fun ξ' => κ * s (t + n) ξ') ξ = κ * 𝔼.E t (s (t + n)) ξ := fun n =>
    congrFun (map_smul (𝔼.E t) κ (s (t + n))) ξ
  have hsum : ∑' n, β ^ n * 𝔼.E t (fun ξ' => κ * s (t + n) ξ') ξ = κ * x ξ := by
    rw [h33, ← tsum_mul_left]
    exact tsum_congr fun n => by rw [e]; ring
  rw [hsum]
  constructor
  · intro h
    have h' : (κ - 1) * x ξ = 0 := by linarith
    rcases mul_eq_zero.mp h' with h0 | h0
    · left; linarith
    · right; exact h0
  · rintro (h0 | h0)
    · rw [h0, one_mul]
    · rw [h0, mul_zero]

end Cochrane.Generality.Links
