/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR6MoneyHousehold

/-!
# The money model's equilibrium conditions derived from optimisation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–496 (the
money model `M_tV_t = P_ty_t`, `(B_{t−1} + M_{t−1})/P_t = E_t∑βʲs_{t+j}`), Chapter 19, §19.1,
pp. 434–435, and Chapter 3, §3.4, pp. 57–59 (the flow condition with money, (3.9)–(3.10), and
"when money pays full interest … money and bonds become perfect substitutes", p. 57).

`TidyR6MoneyHousehold` solves the household problem. Here the household's optimal plan is made an
equilibrium: consumption equals the endowment, and the household holds the government's bonds
`B_t` and money `M_t` (`DerivedEqm`). The project's money modules impose instead the Fisher
equation `Q_t = βP_tE_t[1/P_{t+1}]`, the quantity equation `M_tV_t = P_ty_t` and the valuation
equation `W_t/P_t = E_t∑βʲs̄_{t+j}` (`TidyR5MoneyMeasure.EqmM`). The surplus in the valuation
equation is the seigniorage-inclusive surplus `s̄_t = τ_t + ι_tM_t/P_t` (`sbar`), the book's
"surpluses react one-for-one to seigniorage" (p. 495): the interest saved on money, `ι_tM_t`
with `ι_t = Q^m_t − Q_t`, counts as revenue, as in (3.10).

## Main results

* `derived_iff_imposed` (**the derived-model equilibria are exactly the imposed-equation
  equilibria**, with positive government debt): a price system supports `(c = y, B, M)` as the
  household's optimum iff the Fisher equation, `ι_t ≥ 0`, `M_tV_t ≥ P_ty_t` with equality where
  `ι_t > 0`, and the valuation equation hold. The flow condition `W_t = P_ts̄_t + Q_tW_{t+1}` is
  the household's budget at `c = y` (`flow_of_hhFlow`) and the valuation equation is that
  budget iterated with the transversality condition (`valuation_of_tvc`).
* `derived_iff_eqmM`: when money is costly to hold (`ι_t > 0`, e.g. cash with positive nominal
  rates), `DerivedEqm` is exactly the Fisher equation plus `TidyR5MoneyMeasure.EqmM`;
  `derived_of_eqmM`: in general the Fisher equation, `ι ≥ 0` and `EqmM` give a derived
  equilibrium.
* Corrections. `money_pays_interest`: when money pays the bond rate (`Q^m = Q`, the book's first
  simplification) optimisation implies only `M_tV_t ≥ P_ty_t`; on every probability space an
  open-market swap of bonds for money leaves a derived equilibrium in which `M_tV_t = 2P_ty_t`,
  so the quantity equation fails. `negative_spread_not_derived`: the imposed equations allow
  money that pays more than bonds (`ι < 0`); no optimising household holds it.
* `random_derived_eqm`, `coin_random_derived_eqm`: a derived equilibrium with a genuinely random
  price level, built from any bounded martingale-difference shock, and on the i.i.d. coin
  economy, where unexpected inflation is not zero.
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdEqm

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.TidyR6MoneyHousehold
open Cochrane.ObservationalEquivalence.TidyR5MoneyMeasure (EqmM pvM pvM_succ)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), §22.1, p. 495 ("surpluses react one-for-one to seigniorage"), and (3.10),
p. 58: the seigniorage-inclusive surplus `s̄_t = τ_t + ι_tM_t/P_t`. -/
noncomputable def sbar (e : Econ Ω) (M : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => e.τ t ω + iota e t ω * M t ω / e.P t ω

/-- Cochrane (2023), §22.1, p. 496: the household's plan in equilibrium — it consumes the
endowment and holds the government's bonds `B` and money `M`. -/
def hhPlan (e : Econ Ω) (B M : ℕ → Ω → ℝ) : Plan Ω := ⟨e.y, B, M⟩

/-- Cochrane (2023), §22.1, pp. 495–496: a **derived-model equilibrium** — at the prices of `e`
the plan `(c = y, B, M)` is optimal for the household. -/
def DerivedEqm (e : Econ Ω) (B M : ℕ → Ω → ℝ) : Prop := Optimal S e (hhPlan e B M)

/-- Cochrane (2023), eq. (2.3), p. 22, and (16.25), p. 377: the Fisher equation (bond pricing)
`Q_t = βP_tE_t[1/P_{t+1}]`, almost surely at every date. -/
def Fisher (e : Econ Ω) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, e.Q t ω = e.β * e.P t ω * S.E t (invP e (t + 1)) ω

/-- Cochrane (2023), §22.1, pp. 495–496: the **imposed equations** — the Fisher equation, money
not dominated (`ι_t ≥ 0`), the quantity relation `M_tV_t ≥ P_ty_t` with equality where
`ι_t > 0`, and the valuation equation `W_t/P_t = E_t∑βʲs̄_{t+j}`. -/
def Imposed (e : Econ Ω) (B M : ℕ → Ω → ℝ) : Prop :=
  Fisher S e ∧ (∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ iota e t ω) ∧ (∀ t, ∀ᵐ ω ∂S.μ, mmin e t ω ≤ M t ω) ∧
    (∀ t, ∀ᵐ ω ∂S.μ, 0 < iota e t ω → M t ω = mmin e t ω) ∧
    ∀ t, wealth e.W0 B M t / e.P t =ᵐ[S.μ] pvM S e.β (sbar e M) t

variable {S}

/-! ### The first-order conditions in prices -/

/-- Cochrane (2023), eq. (2.3), p. 22: the Euler gap vanishes iff the Fisher equation
`Q_t = βP_tE_t[1/P_{t+1}]` holds (almost surely). -/
theorem eulerGap_zero_iff {e : Econ Ω} (hreg : EconReg S e) (t : ℕ) :
    eulerGap S e t =ᵐ[S.μ] 0 ↔
      ∀ᵐ ω ∂S.μ, e.Q t ω = e.β * e.P t ω * S.E t (invP e (t + 1)) ω := by
  have hβ := hreg.1.1
  constructor
  · intro h
    filter_upwards [h, hreg.2.2.1 t] with ω h1 hP
    simp only [eulerGap, Pi.zero_apply] at h1
    have hP0 := hP.1.ne'
    have hb : e.β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
    field_simp at h1
    apply mul_left_cancel₀ hb
    linear_combination h1
  · intro h
    filter_upwards [h, hreg.2.2.1 t] with ω h1 hP
    simp only [eulerGap, Pi.zero_apply]
    rw [h1]
    field_simp [hP.1.ne']
    ring

omit mΩ in
/-- Cochrane (2023), §3.4, p. 58: the money gap exceeds the Euler gap by the discounted real
opportunity cost of money, `G_t − D_t = βᵗι_t/P_t`. -/
theorem moneyGap_sub_eulerGap {mΩ : MeasurableSpace Ω} (S : MeasExpectationSystem Ω)
    (e : Econ Ω) (t : ℕ) (ω : Ω) :
    moneyGap S e t ω - eulerGap S e t ω = e.β ^ t * iota e t ω / e.P t ω := by
  simp only [moneyGap, eulerGap, iota]
  ring

/-- Cochrane (2023), §22.1, p. 495: the seigniorage-inclusive surplus is adapted. -/
theorem sbar_adapted {e : Econ Ω} (hreg : EconReg S e) {M : ℕ → Ω → ℝ}
    (hMa : StronglyAdapted S.𝓕 M) : StronglyAdapted S.𝓕 (sbar e M) := fun t => by
  obtain ⟨-, ⟨hPa, hQa, hQma, -, -, hτa⟩, -⟩ := hreg
  exact (hτa t).add (sm_div (((hQma t).sub (hQa t)).mul (hMa t)) (hPa t))

/-- Cochrane (2023), eq. (2.3), p. 22: under the Fisher equation the bond price is nonnegative. -/
theorem Q_nonneg_of_fisher {e : Econ Ω} (hreg : EconReg S e) (hF : Fisher S e) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 ≤ e.Q t ω := by
  have hinv : 0 ≤ᵐ[S.μ] invP e (t + 1) := by
    filter_upwards [hreg.2.2.1 (t + 1)] with ω h
    exact inv_nonneg.2 h.1.le
  filter_upwards [hF t, condExp_nonneg hinv, hreg.2.2.1 t] with ω h1 h2 hP
  rw [h1]
  exact mul_nonneg (mul_nonneg hreg.1.1.le hP.1.le) h2

/-- Cochrane (2023), §22.1, p. 495: with the Fisher equation, `ι ≥ 0` and the complementary
slackness `ι_t > 0 ⇒ M_t = P_ty_t/V_t`, the seigniorage-inclusive surplus is bounded by `2K`. -/
theorem sbar_bdd {e : Econ Ω} (hreg : EconReg S e) {M : ℕ → Ω → ℝ} (hF : Fisher S e)
    (hι : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ iota e t ω)
    (hcs : ∀ t, ∀ᵐ ω ∂S.μ, 0 < iota e t ω → M t ω = mmin e t ω) :
    ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |sbar e M t ω| ≤ K + K := by
  obtain ⟨K, hK⟩ := hreg.2.2.2.2.2
  refine ⟨K, fun t => ?_⟩
  filter_upwards [hK t, hι t, hcs t, Q_nonneg_of_fisher hreg hF t, hreg.2.2.1 t]
    with ω hk hi hc hQ hP
  simp only [sbar]
  refine (abs_add_le _ _).trans (add_le_add hk.2.1 ?_)
  rcases hi.lt_or_eq with hlt | heq
  · rw [hc hlt]
    have e1 : iota e t ω * mmin e t ω / e.P t ω = iota e t ω * (e.y t ω / e.V t ω) := by
      simp only [mmin]; field_simp [hP.1.ne']
    have e2 : e.Qm t ω * e.y t ω / e.V t ω = e.Qm t ω * (e.y t ω / e.V t ω) := by ring
    have hyv : 0 < e.y t ω / e.V t ω := div_pos hP.2.2 hP.2.1
    rw [e1, abs_mul, abs_of_pos hyv, abs_of_pos hlt]
    rw [e2, abs_mul, abs_of_pos hyv] at hk
    have : iota e t ω ≤ |e.Qm t ω| := by
      simp only [iota]; linarith [le_abs_self (e.Qm t ω)]
    nlinarith [hk.2.2.1]
  · rw [← heq]
    simp only [zero_mul, zero_div, abs_zero]
    exact (abs_nonneg _).trans hk.1

/-! ### The flow condition and the valuation equation from the household's budget -/

/-- Cochrane (2023), eq. (3.9), p. 57, and §22.1, p. 496 (**the flow condition from the budget**):
at `c = y` the household's budget is the government flow condition
`W_t = P_ts̄_t + Q_tW_{t+1}`. -/
theorem flow_of_hhFlow {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hflow : Flow S e (hhPlan e B M)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, wealth e.W0 B M t ω =
      e.P t ω * sbar e M t ω + e.Q t ω * wealth e.W0 B M (t + 1) ω := by
  filter_upwards [hflow t, hreg.2.2.1 t] with ω h hP
  simp only [hhPlan, sbar, iota] at h ⊢
  rw [show wealth e.W0 B M (t + 1) ω = B t ω + M t ω from rfl]
  field_simp [hP.1.ne']
  linear_combination h

/-- Cochrane (2023), §22.1, p. 495 ("the government debt valuation formula results from
iterating … forward and imposing the transversality condition"), and (19.30), p. 449: if the
household's budget holds at `c = y`, the Fisher equation holds, the seigniorage-inclusive surplus
is bounded, real wealth is integrable and nonnegative from date `1` on, and
`βᵀE[W_T/P_T] → 0`, then `W_t/P_t = E_t∑βʲs̄_{t+j}` almost surely at every date. -/
theorem valuation_of_tvc {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hBa : StronglyAdapted S.𝓕 B) (hMa : StronglyAdapted S.𝓕 M)
    (hflow : Flow S e (hhPlan e B M)) (hF : Fisher S e) {K : ℝ}
    (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |sbar e M t ω| ≤ K)
    (hint : ∀ t, Integrable (wealth e.W0 B M (t + 1) / e.P (t + 1)) S.μ)
    (hnn : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ wealth e.W0 B M (t + 1) ω / e.P (t + 1) ω)
    (htvc : Tendsto (fun T => e.β ^ T * ∫ ω, wealth e.W0 B M T ω / e.P T ω ∂S.μ) atTop (𝓝 0))
    (t : ℕ) : wealth e.W0 B M t / e.P t =ᵐ[S.μ] pvM S e.β (sbar e M) t := by
  have hβ0 : 0 < e.β := hreg.1.1
  have hβ1 : e.β < 1 := hreg.1.2
  have hβ : |e.β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  set x : ℕ → Ω → ℝ := fun t => wealth e.W0 B M t / e.P t with hx
  have hxi : ∀ t, Integrable (x t) S.μ := fun t => by
    cases t with
    | zero => exact hreg.2.2.2.2.1
    | succ t => exact hint t
  -- `x` solves `x_t = βE_t x_{t+1} + s̄_t`
  have hsol : ∀ t, x t =ᵐ[S.μ] e.β • S.E t (x (t + 1)) + sbar e M t := fun t => by
    have hW' : StronglyMeasurable[S.𝓕 t] (wealth e.W0 B M (t + 1)) := (hBa t).add (hMa t)
    have e0 : wealth e.W0 B M (t + 1) * invP e (t + 1) = x (t + 1) := by
      funext ω; simp only [Pi.mul_apply, invP, hx, Pi.inv_apply, div_eq_mul_inv]
    have h := condExp_mul_of_stronglyMeasurable_left hW' (by rw [e0]; exact hxi (t + 1))
      (hreg.2.2.2.1 (t + 1)).1
    rw [← e0]
    filter_upwards [flow_of_hhFlow hreg hflow t, hF t, h, hreg.2.2.1 t] with ω h1 h2 h3 hP
    change wealth e.W0 B M t ω / e.P t ω =
      e.β * S.E t (wealth e.W0 B M (t + 1) * invP e (t + 1)) ω + sbar e M t ω
    have h3' : S.E t (wealth e.W0 B M (t + 1) * invP e (t + 1)) ω =
        wealth e.W0 B M (t + 1) ω * S.E t (invP e (t + 1)) ω := h3
    rw [h3', h1, h2]
    field_simp [hP.1.ne']
    ring
  have hpv := fun t => pvM_succ (S := S) hβ (sbar_adapted hreg hMa) hsb t
  obtain ⟨Kp, hKp⟩ := S.forwardSol_bdd hβ hsb
  have hpvi : ∀ t, Integrable (pvM S e.β (sbar e M) t) S.μ := fun t => S.integrable_E t _
  set d : ℕ → Ω → ℝ := fun t => x t - pvM S e.β (sbar e M) t with hd
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => (hxi t).sub (hpvi t)
  have hhom : ∀ t, d t =ᵐ[S.μ] e.β • S.E t (d (t + 1)) := fun t => by
    filter_upwards [hsol t, hpv t, S.E_sub (hxi (t + 1)) (hpvi (t + 1)) t] with ω h1 h2 h3
    simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h1 h2 h3 ⊢
    rw [h3, h1, h2]
    ring
  -- `E|d_t| ≤ β^{k+1}(E x_{t+k+1} + Kp)` for every `k`
  have hbd : ∀ k : ℕ, ∫ ω, |d t ω| ∂S.μ ≤
      e.β ^ (k + 1) * (∫ ω, x (t + (k + 1)) ω ∂S.μ + Kp) := fun k => by
    have h1 : ∫ ω, |d t ω| ∂S.μ = e.β ^ (k + 1) * ∫ ω, |S.E t (d (t + (k + 1))) ω| ∂S.μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [S.iterate_homog hhom t k] with ω h
      rw [h, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (pow_pos hβ0 _)]
    have h2 : ∫ ω, |S.E t (d (t + (k + 1))) ω| ∂S.μ ≤ ∫ ω, |d (t + (k + 1)) ω| ∂S.μ :=
      integral_abs_condExp_le _
    have h3 : ∫ ω, |d (t + (k + 1)) ω| ∂S.μ ≤ ∫ ω, x (t + (k + 1)) ω ∂S.μ + Kp := by
      have hle : ∫ ω, |d (t + (k + 1)) ω| ∂S.μ ≤
          ∫ ω, (x (t + (k + 1)) ω + |pvM S e.β (sbar e M) (t + (k + 1)) ω|) ∂S.μ := by
        refine integral_mono_ae (hdi _).abs ((hxi _).add (hpvi _).abs) ?_
        filter_upwards [hnn (t + k)] with ω h
        have h' : 0 ≤ x (t + (k + 1)) ω := h
        simp only [hd, Pi.sub_apply]
        calc |x (t + (k + 1)) ω - pvM S e.β (sbar e M) (t + (k + 1)) ω|
            ≤ |x (t + (k + 1)) ω| + |pvM S e.β (sbar e M) (t + (k + 1)) ω| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg h']
      rw [integral_add (hxi _) (hpvi _).abs] at hle
      have hK2 : ∫ ω, |pvM S e.β (sbar e M) (t + (k + 1)) ω| ∂S.μ ≤ Kp :=
        integral_abs_le_of_bdd (hKp (t + (k + 1)))
      linarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left (h2.trans h3) (pow_nonneg hβ0.le _)
  have hlim : Tendsto (fun k : ℕ => e.β ^ (k + 1) * (∫ ω, x (t + (k + 1)) ω ∂S.μ + Kp)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (e.β ^ t)⁻¹ *
        (e.β ^ (k + (t + 1)) * ∫ ω, x (k + (t + 1)) ω ∂S.μ)) atTop (𝓝 ((e.β ^ t)⁻¹ * 0)) :=
      (htvc.comp (tendsto_add_atTop_nat (t + 1))).const_mul _
    have h2 : Tendsto (fun k : ℕ => e.β ^ (k + 1) * Kp) atTop (𝓝 (0 * Kp)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
        (tendsto_add_atTop_nat 1)).mul_const Kp
    rw [mul_zero] at h1
    rw [zero_mul] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun k => ?_
    have hb : e.β ^ t ≠ 0 := pow_ne_zero t hβ0.ne'
    rw [show k + (t + 1) = t + (k + 1) by omega, pow_add, mul_add]
    field_simp
  have h0 : ∫ ω, |d t ω| ∂S.μ ≤ 0 := ge_of_tendsto' hlim hbd
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg (d t ω)) (hdi t).abs).1
    (le_antisymm h0 (integral_nonneg fun ω => abs_nonneg _))
  filter_upwards [hz] with ω h
  simp only [Pi.zero_apply, abs_eq_zero, hd, Pi.sub_apply, sub_eq_zero] at h
  exact h

/-! ### Derived equilibria are exactly the imposed-equation equilibria -/

/-- Cochrane (2023), §22.1, pp. 495–496 (**necessity**): with positive government debt, a
derived-model equilibrium satisfies the imposed equations — the Fisher equation, `ι_t ≥ 0`,
`M_tV_t ≥ P_ty_t` with equality where `ι_t > 0`, and the valuation equation. -/
theorem imposed_of_derived {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω) (h : DerivedEqm S e B M) : Imposed S e B M := by
  obtain ⟨hp, -, hD, hG0, hGM, htvc⟩ :=
    (optimal_iff_foc (p := hhPlan e B M) hreg hBpos).1 h
  have hF : Fisher S e := fun t => (eulerGap_zero_iff hreg t).1 (hD t)
  have hι : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ iota e t ω := fun t => by
    filter_upwards [hD t, hG0 t, hreg.2.2.1 t] with ω hd hg hP
    have e1 := moneyGap_sub_eulerGap S e t ω
    have hd' : eulerGap S e t ω = 0 := hd
    have hg' : 0 ≤ moneyGap S e t ω := hg
    rw [hd', sub_zero] at e1
    have h1 : 0 ≤ e.β ^ t * iota e t ω / e.P t ω := e1 ▸ hg'
    have h2 : 0 < e.β ^ t := pow_pos hreg.1.1 t
    rw [mul_div_assoc] at h1
    exact (div_nonneg_iff.1 (nonneg_of_mul_nonneg_right h1 h2)).elim (fun h => h.1)
      (fun h => absurd h.2 (not_le.2 hP.1))
  have hcs : ∀ t, ∀ᵐ ω ∂S.μ, 0 < iota e t ω → M t ω = mmin e t ω := fun t => by
    filter_upwards [hD t, hGM t, hp.2.2.1 t, hreg.2.2.1 t] with ω hd hg hc hP hpos
    by_contra hne
    have hlt : mmin e t ω < M t ω := lt_of_le_of_ne hc.2 (Ne.symm hne)
    have e1 := moneyGap_sub_eulerGap S e t ω
    have hd' : eulerGap S e t ω = 0 := hd
    rw [hd', hg hlt, sub_zero] at e1
    have : 0 < e.β ^ t * iota e t ω / e.P t ω :=
      div_pos (mul_pos (pow_pos hreg.1.1 t) hpos) hP.1
    linarith
  obtain ⟨K, hsb⟩ := sbar_bdd hreg hF hι hcs
  refine ⟨hF, hι, fun t => (hp.2.2.1 t).mono fun ω h => h.2, hcs, fun t => ?_⟩
  refine valuation_of_tvc hreg hp.1.2.1 hp.1.2.2 hp.2.1 hF hsb
    (fun t => realWealth_integrable hreg hp (t + 1)) (fun t => ?_) htvc t
  filter_upwards [hp.2.2.1 t, hreg.2.2.1 t, hreg.2.2.1 (t + 1)] with ω hc hT hT1
  have hmm : 0 < mmin e t ω := div_pos (mul_pos hT.1 hT.2.2) hT.2.1
  exact div_nonneg (by simp only [wealth, hhPlan, Pi.add_apply] at hc ⊢; linarith [hc.1, hc.2])
    hT1.1.le

/-- Cochrane (2023), §22.1, pp. 495–496 (**sufficiency**): with positive adapted government debt
and adapted money, the imposed equations make `(c = y, B, M)` the household's optimum. -/
theorem derived_of_imposed {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hBa : StronglyAdapted S.𝓕 B) (hMa : StronglyAdapted S.𝓕 M)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω) (h : Imposed S e B M) : DerivedEqm S e B M := by
  obtain ⟨hF, hι, hMm, hcs, hval⟩ := h
  have hβ0 : 0 < e.β := hreg.1.1
  have hβ1 : e.β < 1 := hreg.1.2
  have hβ : |e.β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  obtain ⟨K2, hsb⟩ := sbar_bdd hreg hF hι hcs
  obtain ⟨Kp, hKp⟩ := S.forwardSol_bdd hβ hsb
  have hreg0 := hreg
  obtain ⟨-, ⟨hPa, -, -, hya, -, hτa⟩, hpos, hint, -, K, hK⟩ := hreg0
  set x : ℕ → Ω → ℝ := fun t => wealth e.W0 B M t / e.P t with hx
  have hxb : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ Kp := fun t => by
    filter_upwards [hval t, hKp t] with ω h1 h2
    rw [show x t ω = _ from h1]
    exact h2
  have hxi : ∀ t, Integrable (x t) S.μ := fun t => (S.integrable_E t _).congr (hval t).symm
  have hsa := sbar_adapted hreg hMa
  have hsbi : ∀ t, Integrable (sbar e M t) S.μ := fun t => integrable_of_bdd (hsa t) (hsb t)
  have hpullB : ∀ t (X : ℕ → Ω → ℝ), StronglyAdapted S.𝓕 X →
      Integrable (fun ω => X t ω / e.P (t + 1) ω) S.μ →
      Integrable (fun ω => X t ω * S.E t (invP e (t + 1)) ω) S.μ ∧
        S.E t (X t * invP e (t + 1)) =ᵐ[S.μ] fun ω => X t ω * S.E t (invP e (t + 1)) ω :=
    fun t X hXa hXi => by
      have e0 : X t * invP e (t + 1) = fun ω => X t ω / e.P (t + 1) ω := by
        funext ω; simp only [Pi.mul_apply, invP, div_eq_mul_inv]
      have h := condExp_mul_of_stronglyMeasurable_left (hXa t) (by rw [e0]; exact hXi)
        (hint (t + 1)).1
      exact ⟨(S.integrable_E t _).congr h, h⟩
  -- the budget at `c = y`
  have hflow : Flow S e (hhPlan e B M) := fun t => by
    have hW' : StronglyMeasurable[S.𝓕 t] (wealth e.W0 B M (t + 1)) := (hBa t).add (hMa t)
    have e0 : wealth e.W0 B M (t + 1) * invP e (t + 1) = x (t + 1) := by
      funext ω; simp only [Pi.mul_apply, invP, hx, Pi.inv_apply, div_eq_mul_inv]
    have h3 := condExp_mul_of_stronglyMeasurable_left hW' (by rw [e0]; exact hxi (t + 1))
      (hint (t + 1)).1
    filter_upwards [hval t, pvM_succ (S := S) hβ hsa hsb t, S.E_congr (hval (t + 1)).symm t,
      h3, hF t, hpos t] with ω h1 h2 h4 h5 h6 hP
    have h5' : S.E t (wealth e.W0 B M (t + 1) * invP e (t + 1)) ω =
        wealth e.W0 B M (t + 1) ω * S.E t (invP e (t + 1)) ω := h5
    rw [e0] at h5'
    have h4' : S.E t (pvM S e.β (sbar e M) (t + 1)) ω = S.E t (x (t + 1)) ω := h4
    have h1' : x t ω = _ := h1
    rw [h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h4', h5'] at h1'
    simp only [hx, Pi.div_apply, sbar, iota] at h1'
    simp only [hhPlan]
    rw [show wealth e.W0 B M (t + 1) ω = B t ω + M t ω from rfl] at h1'
    field_simp [hP.1.ne'] at h1'
    rw [h6] at h1' ⊢
    linear_combination h1'
  have hint1 : ∀ t, Integrable (fun ω => B t ω / e.P (t + 1) ω) S.μ ∧
      Integrable (fun ω => M t ω / e.P (t + 1) ω) S.μ := fun t => by
    have hmB : AEStronglyMeasurable (fun ω => B t ω / e.P (t + 1) ω) S.μ :=
      ((sm_div ((hBa t).mono (S.𝓕.mono (Nat.le_succ t))) (hPa (t + 1))).mono
        (S.𝓕.le (t + 1))).aestronglyMeasurable
    have hmM : AEStronglyMeasurable (fun ω => M t ω / e.P (t + 1) ω) S.μ :=
      ((sm_div ((hMa t).mono (S.𝓕.mono (Nat.le_succ t))) (hPa (t + 1))).mono
        (S.𝓕.le (t + 1))).aestronglyMeasurable
    refine ⟨(hxi (t + 1)).mono' hmB ?_, (hxi (t + 1)).mono' hmM ?_⟩
    · filter_upwards [hBpos t, hMm t, hpos t, hpos (t + 1)] with ω hb hm hT hT1
      have hmm : 0 < mmin e t ω := div_pos (mul_pos hT.1 hT.2.2) hT.2.1
      simp only [Real.norm_eq_abs, hx, Pi.div_apply, wealth, Pi.add_apply]
      rw [abs_of_nonneg (div_nonneg hb.le hT1.1.le)]
      exact div_le_div_of_nonneg_right (by linarith) hT1.1.le
    · filter_upwards [hBpos t, hMm t, hpos t, hpos (t + 1)] with ω hb hm hT hT1
      have hmm : 0 < mmin e t ω := div_pos (mul_pos hT.1 hT.2.2) hT.2.1
      simp only [Real.norm_eq_abs, hx, Pi.div_apply, wealth, Pi.add_apply]
      rw [abs_of_nonneg (div_nonneg (by linarith) hT1.1.le)]
      exact div_le_div_of_nonneg_right (by linarith) hT1.1.le
  have hQX : ∀ t (X : ℕ → Ω → ℝ), StronglyAdapted S.𝓕 X →
      Integrable (fun ω => X t ω / e.P (t + 1) ω) S.μ →
      Integrable (fun ω => e.Q t ω * X t ω / e.P t ω) S.μ := fun t X hXa hXi => by
    obtain ⟨h1, -⟩ := hpullB t X hXa hXi
    refine (h1.const_mul e.β).congr ?_
    filter_upwards [hF t, hpos t] with ω hq hP
    rw [hq]
    field_simp [hP.1.ne']
  have hfeas : Feasible S e (hhPlan e B M) := by
    refine ⟨⟨hya, hBa, hMa⟩, hflow, fun t => ?_, fun t => ?_⟩
    · filter_upwards [hBpos t, hMm t] with ω hb hm
      exact ⟨hb.le, hm⟩
    · obtain ⟨hiB, hiM⟩ := hint1 t
      refine ⟨(exo_integrable hreg t).1, hiB, hiM, hQX t B hBa hiB, ?_⟩
      have e1 : (fun ω => e.Qm t ω * M t ω / e.P t ω) =
          fun ω => (sbar e M t ω - e.τ t ω) + e.Q t ω * M t ω / e.P t ω := by
        funext ω; simp only [sbar, iota]; ring
      change Integrable (fun ω => e.Qm t ω * M t ω / e.P t ω) S.μ
      rw [e1]
      exact ((hsbi t).sub (integrable_of_bdd (hτa t) ((hK t).mono fun ω h => h.2.1))).add
        (hQX t M hMa hiM)
  have hK0 : 0 ≤ K := by
    obtain ⟨ω, hω⟩ := (hK 0).exists
    exact (abs_nonneg _).trans hω.1
  have hadm : Admissible S e.β (hhPlan e B M).c := by
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0.le t)
      (integral_nonneg fun ω => abs_nonneg _)) (fun t => ?_)
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K)
    exact mul_le_mul_of_nonneg_left (integral_abs_le_of_bdd ((hK t).mono fun ω h => h.1))
      (pow_nonneg hβ0.le t)
  have hD : ∀ t, eulerGap S e t =ᵐ[S.μ] 0 := fun t => (eulerGap_zero_iff hreg t).2 (hF t)
  have hG0 : ∀ t, 0 ≤ᵐ[S.μ] moneyGap S e t := fun t => by
    filter_upwards [hD t, hι t, hpos t] with ω hd hi hP
    have e1 := moneyGap_sub_eulerGap S e t ω
    have hd' : eulerGap S e t ω = 0 := hd
    rw [hd', sub_zero] at e1
    change 0 ≤ moneyGap S e t ω
    rw [e1]
    exact div_nonneg (mul_nonneg (pow_nonneg hβ0.le t) hi) hP.1.le
  have hGM : ∀ t, ∀ᵐ ω ∂S.μ, mmin e t ω < (hhPlan e B M).M t ω → moneyGap S e t ω = 0 :=
    fun t => by
      filter_upwards [hD t, hι t, hcs t] with ω hd hi hc hlt
      have e1 := moneyGap_sub_eulerGap S e t ω
      have hd' : eulerGap S e t ω = 0 := hd
      rw [hd', sub_zero] at e1
      rcases hi.lt_or_eq with hpos' | heq
      · exact absurd (hc hpos') (ne_of_gt hlt)
      · rw [e1, ← heq, mul_zero, zero_div]
  have htvc : Tendsto (fun T => e.β ^ T * ∫ ω, realWealth e (hhPlan e B M) T ω ∂S.μ) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (a := fun T => e.β ^ T * Kp) (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 T)]
      refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans
        (integral_abs_le_of_bdd (hxb T))) (pow_nonneg hβ0.le T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const Kp
  exact (optimal_iff_foc (p := hhPlan e B M) hreg hBpos).2 ⟨hfeas, hadm, hD, hG0, hGM, htvc⟩

/-- Cochrane (2023), §22.1, pp. 495–496 (**the derived-model equilibria are exactly the
imposed-equation equilibria**): with positive adapted government debt and adapted money, a price
system supports `(c = y, B, M)` as the household's optimum iff the Fisher equation holds, money
is not dominated (`ι_t ≥ 0`), `M_tV_t ≥ P_ty_t` with equality where `ι_t > 0`, and
`W_t/P_t = E_t∑βʲs̄_{t+j}` (almost surely, at every date). -/
theorem derived_iff_imposed {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hBa : StronglyAdapted S.𝓕 B) (hMa : StronglyAdapted S.𝓕 M)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω) : DerivedEqm S e B M ↔ Imposed S e B M :=
  ⟨imposed_of_derived hreg hBpos, derived_of_imposed hreg hBa hMa hBpos⟩

/-! ### Links to the imposed-equation model `TidyR5MoneyMeasure.EqmM` -/

/-- Cochrane (2023), §19.5.2, (19.33), p. 450, and §22.1, p. 496: in a derived-model
equilibrium, `M_tV_t ≥ P_ty_t`, with equality `M_tV_t = P_ty_t` wherever money is costly to hold
(`ι_t > 0`). -/
theorem quantity_of_derived {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω) (h : DerivedEqm S e B M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, e.P t ω * e.y t ω ≤ M t ω * e.V t ω ∧
      (0 < iota e t ω → M t ω * e.V t ω = e.P t ω * e.y t ω) := by
  obtain ⟨-, -, hMm, hcs, -⟩ := imposed_of_derived hreg hBpos h
  filter_upwards [hMm t, hcs t, hreg.2.2.1 t] with ω hm hc hP
  have hV := hP.2.1
  refine ⟨?_, fun hi => ?_⟩
  · simp only [mmin] at hm
    rwa [div_le_iff₀ hV] at hm
  · rw [hc hi]
    simp only [mmin]
    field_simp [hV.ne']

/-- Cochrane (2023), §22.1, pp. 495–496 (**OE-2's equilibrium conditions derived**): when money
is costly to hold (`ι_t > 0` almost surely, as for cash at positive nominal rates), the derived
equilibria are exactly the price systems satisfying the Fisher equation and the imposed money
model `TidyR5MoneyMeasure.EqmM` with the seigniorage-inclusive surplus. -/
theorem derived_iff_eqmM {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hBa : StronglyAdapted S.𝓕 B) (hMa : StronglyAdapted S.𝓕 M)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω) (hspread : ∀ t, ∀ᵐ ω ∂S.μ, 0 < iota e t ω) :
    DerivedEqm S e B M ↔ Fisher S e ∧ EqmM S e.β e.V e.y e.P M (wealth e.W0 B M) (sbar e M) := by
  rw [derived_iff_imposed hreg hBa hMa hBpos]
  constructor
  · rintro ⟨hF, -, -, hcs, hval⟩
    refine ⟨hF, fun t => ⟨(hreg.2.2.1 t).mono fun ω h => h.1, ?_, hval t⟩⟩
    filter_upwards [hcs t, hspread t, hreg.2.2.1 t] with ω hc hs hP
    simp only [Pi.mul_apply]
    rw [hc hs]
    simp only [mmin]
    field_simp [hP.2.1.ne']
  · rintro ⟨hF, h⟩
    have hmm : ∀ t, ∀ᵐ ω ∂S.μ, M t ω = mmin e t ω := fun t => by
      filter_upwards [(h t).2.1, hreg.2.2.1 t] with ω hq hP
      simp only [Pi.mul_apply] at hq
      simp only [mmin]
      field_simp [hP.2.1.ne']
      linarith
    refine ⟨hF, fun t => (hspread t).mono fun ω h => h.le, fun t => (hmm t).mono fun ω h => h.ge,
      fun t => (hmm t).mono fun ω h _ => h, fun t => (h t).2.2⟩

/-- Cochrane (2023), §22.1, pp. 495–496: whatever the cost of money, the Fisher equation, money
not dominated (`ι ≥ 0`) and the imposed money model `TidyR5MoneyMeasure.EqmM` give a derived
equilibrium. -/
theorem derived_of_eqmM {e : Econ Ω} {B M : ℕ → Ω → ℝ} (hreg : EconReg S e)
    (hBa : StronglyAdapted S.𝓕 B) (hMa : StronglyAdapted S.𝓕 M)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω) (hF : Fisher S e)
    (hι : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ iota e t ω)
    (h : EqmM S e.β e.V e.y e.P M (wealth e.W0 B M) (sbar e M)) : DerivedEqm S e B M := by
  have hmm : ∀ t, ∀ᵐ ω ∂S.μ, M t ω = mmin e t ω := fun t => by
    filter_upwards [(h t).2.1, hreg.2.2.1 t] with ω hq hP
    simp only [Pi.mul_apply] at hq
    simp only [mmin]
    field_simp [hP.2.1.ne']
    linarith
  exact derived_of_imposed hreg hBa hMa hBpos ⟨hF, hι, fun t => (hmm t).mono fun ω h => h.ge,
    fun t => (hmm t).mono fun ω h _ => h, fun t => (h t).2.2⟩

/-! ### Corrections: interest-bearing money and a negative spread -/

/-- Cochrane (2023), §22.1, p. 495 (tool for the corrections): the constant economy —
`y = V = P = 1`, bond price `Q = β`, money price `Q^m = q`, taxes `τ` and initial wealth `w`. -/
noncomputable def constEcon (β q τ w : ℝ) : Econ Ω :=
  ⟨β, fun _ _ => 1, fun _ _ => 1, fun _ _ => τ, fun _ _ => 1, fun _ _ => β, fun _ _ => q,
    fun _ => w⟩

/-- Cochrane (2023), §22.1, p. 495: the constant economy satisfies the regularity conditions for
`0 < β < 1`. -/
theorem constEcon_reg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (q τ w : ℝ) :
    EconReg S (constEcon β q τ w) := by
  refine ⟨⟨hβ0, hβ1⟩, ⟨fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const⟩,
    fun t => Eventually.of_forall fun ω => ?_, fun t => ⟨?_, ?_, ?_⟩, ?_,
    |τ| + |q| + 1, fun t => Eventually.of_forall fun ω => ?_⟩
  · simp [constEcon]
  · unfold invP; simp only [constEcon, inv_one]; exact integrable_const _
  · simp only [constEcon, div_one]; exact integrable_const _
  · simp only [constEcon, div_one]; exact integrable_const _
  · simp only [constEcon, div_one]; exact integrable_const _
  · simp only [constEcon, mmin, mul_one, div_one, abs_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [abs_nonneg τ, abs_nonneg q]

/-- Cochrane (2023), §22.1, p. 496 (tool): the present value of a constant surplus `c` is
`c/(1 − β)`. -/
theorem pvM_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (c : ℝ) (t : ℕ) :
    pvM S β (fun _ _ => c) t = fun _ => c / (1 - β) := by
  have hd : MeasExpectationSystem.discSum β (fun (_ : ℕ) (_ : Ω) => c) t =
      fun _ => c / (1 - β) := by
    funext ω
    simp only [MeasExpectationSystem.discSum]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
    field_simp [(by linarith : (1 : ℝ) - β ≠ 0)]
  simp only [pvM, MeasExpectationSystem.forwardSol]
  rw [hd, S.E_const]

/-- Cochrane (2023), §22.1, p. 495 ("simplifying further to the case that money pays interest"),
and §3.4, p. 57 ("when money pays full interest … money and bonds become perfect substitutes";
**correction**): when money pays the bond rate (`Q^m = Q = β`), optimisation does not imply
`M_tV_t = P_ty_t`. In the constant economy with `W_0 = 3` and taxes `3(1 − β)`, every split
`B = 3 − m`, `M = m` with `1 ≤ m < 3` is a derived equilibrium at the same prices (open-market
operations are irrelevant), and at `m = 2` the imposed money model `EqmM` fails because
`M_tV_t = 2 ≠ 1 = P_ty_t`. Optimisation gives only `M_tV_t ≥ P_ty_t`. -/
theorem money_pays_interest {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ m : ℝ, 1 ≤ m → m < 3 →
      DerivedEqm S (constEcon β β (3 * (1 - β)) 3) (fun _ _ => 3 - m) (fun _ _ => m)) ∧
    ¬ EqmM S β (constEcon (Ω := Ω) β β (3 * (1 - β)) 3).V
      (constEcon (Ω := Ω) β β (3 * (1 - β)) 3).y (constEcon (Ω := Ω) β β (3 * (1 - β)) 3).P
      (fun _ _ => 2) (wealth 3 (fun _ _ => 1) (fun _ _ => 2))
      (sbar (constEcon β β (3 * (1 - β)) 3) (fun _ _ => 2)) := by
  have hreg := constEcon_reg (S := S) hβ0 hβ1 β (3 * (1 - β)) 3
  refine ⟨fun m hm1 hm3 => ?_, fun h => ?_⟩
  · refine derived_of_imposed hreg (fun _ => stronglyMeasurable_const)
      (fun _ => stronglyMeasurable_const) (fun t => Eventually.of_forall fun ω => by
        linarith) ⟨fun t => Eventually.of_forall fun ω => ?_,
        fun t => Eventually.of_forall fun ω => ?_, fun t => Eventually.of_forall fun ω => ?_,
        fun t => Eventually.of_forall fun ω h => ?_, fun t => ?_⟩
    · have hE : S.E t (invP (constEcon β β (3 * (1 - β)) 3) (t + 1)) = fun _ => 1 := by
        have : invP (constEcon (Ω := Ω) β β (3 * (1 - β)) 3) (t + 1) = fun _ => (1 : ℝ) := by
          funext ω; simp [invP, constEcon]
        rw [this, S.E_const]
      rw [hE]
      simp [constEcon]
    · simp [iota, constEcon]
    · simp [mmin, constEcon, hm1]
    · simp [iota, constEcon] at h
    · have hs : sbar (constEcon (Ω := Ω) β β (3 * (1 - β)) 3) (fun _ _ => m) =
          fun _ _ => 3 * (1 - β) := by
        funext t ω; simp [sbar, iota, constEcon]
      rw [hs]
      change _ =ᵐ[S.μ] pvM S β _ t
      rw [pvM_const hβ0.le hβ1]
      refine Eventually.of_forall fun ω => ?_
      have h1 : (1 : ℝ) - β ≠ 0 := by linarith
      cases t with
      | zero => simp [wealth, constEcon]; field_simp
      | succ t => simp [wealth, constEcon]; field_simp
  · obtain ⟨ω, hω⟩ := ((h 0).2.1).exists
    simp [constEcon] at hω

/-- Cochrane (2023), §22.1, pp. 495–496, and §3.4, p. 57 (**the sign restriction is derived,
not imposed**): the imposed equations allow money that pays more than bonds. In the constant
economy with `Q^m = β/2 < Q = β`, `B = M = 1`, `W_0 = 2` and taxes `2(1 − β) + β/2`, the Fisher
equation and the imposed money model `EqmM` hold, yet no optimising household holds this plan
(it would hoard money): `ι = −β/2 < 0` contradicts `ι_t ≥ 0`. -/
theorem negative_spread_not_derived {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Fisher S (constEcon β (β / 2) (2 * (1 - β) + β / 2) 2) ∧
    EqmM S β (constEcon (Ω := Ω) β (β / 2) (2 * (1 - β) + β / 2) 2).V
      (constEcon (Ω := Ω) β (β / 2) (2 * (1 - β) + β / 2) 2).y
      (constEcon (Ω := Ω) β (β / 2) (2 * (1 - β) + β / 2) 2).P
      (fun _ _ => 1) (wealth 2 (fun _ _ => 1) (fun _ _ => 1))
      (sbar (constEcon β (β / 2) (2 * (1 - β) + β / 2) 2) (fun _ _ => 1)) ∧
    ¬ DerivedEqm S (constEcon β (β / 2) (2 * (1 - β) + β / 2) 2) (fun _ _ => 1)
      (fun _ _ => 1) := by
  have hreg := constEcon_reg (S := S) hβ0 hβ1 (β / 2) (2 * (1 - β) + β / 2) 2
  refine ⟨fun t => Eventually.of_forall fun ω => ?_, fun t => ⟨Eventually.of_forall fun ω => ?_,
    Eventually.of_forall fun ω => ?_, ?_⟩, fun h => ?_⟩
  · have : invP (constEcon (Ω := Ω) β (β / 2) (2 * (1 - β) + β / 2) 2) (t + 1) =
        fun _ => (1 : ℝ) := by
      funext ω; simp [invP, constEcon]
    rw [this, S.E_const]
    simp [constEcon]
  · simp [constEcon]
  · simp [constEcon]
  · have hs : sbar (constEcon (Ω := Ω) β (β / 2) (2 * (1 - β) + β / 2) 2) (fun _ _ => 1) =
        fun _ _ => 2 * (1 - β) := by
      funext t ω; simp [sbar, iota, constEcon]; ring
    rw [hs]
    rw [pvM_const hβ0.le hβ1]
    refine Eventually.of_forall fun ω => ?_
    have h1 : (1 : ℝ) - β ≠ 0 := by linarith
    cases t with
    | zero => simp [wealth, constEcon]; field_simp
    | succ t => simp [wealth, constEcon]; field_simp; ring
  · obtain ⟨-, hι, -⟩ := imposed_of_derived hreg
      (fun t => Eventually.of_forall fun ω => by simp) h
    obtain ⟨ω, hω⟩ := (hι 0).exists
    simp only [iota, constEcon] at hω
    linarith

/-! ### A derived equilibrium with a random price level -/

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496 (the random economy): the price level `P_t = 1/(1 + bε_t)` with
`b = (1 − β)/2`, driven by a shock `ε`. -/
noncomputable def randP (β : ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (1 + (1 - β) / 2 * ε t ω)⁻¹

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496 (the random economy): real liabilities `W_t/P_t` with
`W_0 = 2`, one bond and money `M_t = P_t` (`W_{t+1} = 1 + P_t`). -/
noncomputable def randX (β : ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => wealth (fun _ => 2) (fun _ _ => 1) (randP β ε) t ω / randP β ε t ω

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496 (the random economy): cash (`Q^m = 1`), `y = V = 1`, the
price level `randP`, the Fisher bond price `Q_t = βP_t`, and the passive taxes
`τ_t = W_t/P_t − β(1 + P_t) − (1 − βP_t)` that make the surplus `s̄_t = x_t − βE_tx_{t+1}`. -/
noncomputable def randEcon (β : ℝ) (ε : ℕ → Ω → ℝ) : Econ Ω :=
  ⟨β, fun _ _ => 1, fun _ _ => 1,
    fun t ω => randX β ε t ω - β * (1 + randP β ε t ω) - (1 - β * randP β ε t ω),
    randP β ε, fun t ω => β * randP β ε t ω, fun _ _ => 1, fun _ => 2⟩

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496 (the random economy): the inverse price level is
`1/P_t = 1 + (1 − β)ε_t/2`. -/
theorem rand_invP (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) :
    invP (randEcon β ε) t = fun ω => 1 + (1 - β) / 2 * ε t ω := by
  funext ω; simp only [invP, randEcon, randP, inv_inv]

/-- Cochrane (2023), §22.1, p. 496 (the random economy): with `E_tε_{t+1} = 0`, the expected inverse
price level is one, `E_t[1/P_{t+1}] = 1`. -/
theorem rand_E_invP {β : ℝ} {ε : ℕ → Ω → ℝ} (hεa : StronglyAdapted S.𝓕 ε)
    (hεb : ∀ t ω, |ε t ω| ≤ 1) (hεm : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (t : ℕ) :
    S.E t (invP (randEcon β ε) (t + 1)) =ᵐ[S.μ] fun _ => 1 := by
  rw [rand_invP]
  have hεi : Integrable (ε (t + 1)) S.μ := integrable_of_bdd (hεa (t + 1))
    (Eventually.of_forall (hεb (t + 1)))
  have e1 : (fun ω => 1 + (1 - β) / 2 * ε (t + 1) ω) =
      (fun _ => (1 : ℝ)) + ((1 - β) / 2) • ε (t + 1) := by
    funext ω; simp [smul_eq_mul]
  rw [e1]
  filter_upwards [S.E_add (integrable_const 1) (hεi.smul ((1 - β) / 2)) t,
    S.E_smul ((1 - β) / 2) (ε (t + 1)) t, hεm t] with ω h1 h2 h3
  rw [h1, Pi.add_apply, S.E_const, h2, Pi.smul_apply, h3]
  simp

/-- Cochrane (2023), §22.1, p. 496 (**a derived equilibrium under genuine uncertainty**): for any
shock `ε` adapted, bounded by one and with `E_tε_{t+1} = 0`, and `0 < β < 1`, the price level
`P_t = 1/(1 + (1 − β)ε_t/2)`, bonds `B = 1`, money `M_t = P_t` (so `M_tV_t = P_ty_t`), cash
(`ι_t = 1 − βP_t > 0`) and the passive taxes of `randEcon` form a derived equilibrium; it is
also an equilibrium of the imposed money model `TidyR5MoneyMeasure.EqmM`. -/
theorem random_derived_eqm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {ε : ℕ → Ω → ℝ}
    (hεa : StronglyAdapted S.𝓕 ε) (hεb : ∀ t ω, |ε t ω| ≤ 1)
    (hεm : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) :
    DerivedEqm S (randEcon β ε) (fun _ _ => 1) (randP β ε) ∧ Fisher S (randEcon β ε) ∧
      EqmM S β (randEcon β ε).V (randEcon β ε).y (randP β ε)
        (randP β ε) (wealth (fun _ => 2) (fun _ _ => 1) (randP β ε))
        (sbar (randEcon β ε) (randP β ε)) := by
  set b : ℝ := (1 - β) / 2 with hb
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have hb1 : b ≤ 1 / 2 := by rw [hb]; linarith
  -- bounds on `u = 1 + bε` and `P = u⁻¹`
  have hu : ∀ t ω, (1 + β) / 2 ≤ 1 + b * ε t ω ∧ 1 + b * ε t ω ≤ 2 := fun t ω => by
    have h1 := abs_le.1 (hεb t ω)
    constructor <;> nlinarith [h1.1, h1.2]
  have hupos : ∀ t ω, 0 < 1 + b * ε t ω := fun t ω => by linarith [(hu t ω).1]
  have hPdef : ∀ t ω, randP β ε t ω = (1 + b * ε t ω)⁻¹ := fun t ω => rfl
  have hPpos : ∀ t ω, 0 < randP β ε t ω := fun t ω => by
    rw [hPdef]; exact inv_pos.2 (hupos t ω)
  have hPle : ∀ t ω, randP β ε t ω ≤ 2 / (1 + β) := fun t ω => by
    rw [hPdef, inv_eq_one_div, div_le_div_iff₀ (hupos t ω) (by linarith)]
    linarith [(hu t ω).1]
  have hP2 : ∀ t ω, randP β ε t ω ≤ 2 := fun t ω =>
    (hPle t ω).trans (by rw [div_le_iff₀ (by linarith)]; linarith)
  have hinvP : ∀ t, invP (randEcon β ε) t = fun ω => 1 + b * ε t ω := fun t => by
    funext ω; simp only [invP, randEcon, hPdef, inv_inv]
  have hx : ∀ t ω, randX β ε (t + 1) ω = (1 + randP β ε t ω) * (1 + b * ε (t + 1) ω) :=
    fun t ω => by
      simp only [randX, wealth]
      rw [hPdef (t + 1), div_inv_eq_mul]
      rfl
  have hx0 : ∀ ω, randX β ε 0 ω = 2 * (1 + b * ε 0 ω) := fun ω => by
    simp only [randX, wealth]
    rw [hPdef 0, div_inv_eq_mul]
  have hxb : ∀ t ω, 0 ≤ randX β ε t ω ∧ randX β ε t ω ≤ 6 := fun t ω => by
    cases t with
    | zero =>
      rw [hx0]
      constructor <;> nlinarith [hu 0 ω, hupos 0 ω]
    | succ t =>
      rw [hx]
      have := hu (t + 1) ω
      constructor <;> nlinarith [hPpos t ω, hP2 t ω, hupos (t + 1) ω]
  -- measurability
  have hum : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => 1 + b * ε t ω) := fun t =>
    (measurable_const.add (measurable_const.mul (hεa t).measurable)).stronglyMeasurable
  have hPa : StronglyAdapted S.𝓕 (randP β ε) := fun t =>
    (measurable_const.add (measurable_const.mul (hεa t).measurable)).inv.stronglyMeasurable
  have hxa : StronglyAdapted S.𝓕 (randX β ε) := fun t => by
    cases t with
    | zero => exact sm_div stronglyMeasurable_const (hPa 0)
    | succ t =>
      exact sm_div ((stronglyMeasurable_const.add (hPa t)).mono (S.𝓕.mono (Nat.le_succ t)))
        (hPa (t + 1))
  have hEu : ∀ t, S.E t (invP (randEcon β ε) (t + 1)) =ᵐ[S.μ] fun _ => 1 :=
    rand_E_invP hεa hεb hεm
  have hreg : EconReg S (randEcon β ε) := by
    refine ⟨⟨hβ0, hβ1⟩, ⟨hPa, fun t => (hPa t).const_mul β, fun _ => stronglyMeasurable_const,
      fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const, fun t => ?_⟩,
      fun t => Eventually.of_forall fun ω => ⟨hPpos t ω, one_pos, one_pos⟩,
      fun t => ⟨?_, ?_, ?_⟩, ?_, 12, fun t => Eventually.of_forall fun ω => ?_⟩
    · exact (((hxa t).sub (stronglyMeasurable_const.mul (stronglyMeasurable_const.add
        (hPa t)))).sub (stronglyMeasurable_const.sub (stronglyMeasurable_const.mul (hPa t))))
    · rw [hinvP]
      refine integrable_of_bdd (hum t) (K := 2) (Eventually.of_forall fun ω => ?_)
      rw [abs_of_pos (hupos t ω)]; exact (hu t ω).2
    · refine (integrable_const β).congr (Eventually.of_forall fun ω => ?_)
      simp only [randEcon]
      field_simp [(hPpos t ω).ne']
    · refine integrable_of_bdd (hum t) (K := 2) (Eventually.of_forall fun ω => ?_) |>.congr
        (Eventually.of_forall fun ω => ?_)
      · rw [abs_of_pos (hupos t ω)]; exact (hu t ω).2
      · simp only [randEcon, hPdef, one_div, inv_inv]
    · refine (integrable_of_bdd (hum 0) (K := 2) (Eventually.of_forall fun ω => ?_)).const_mul 2
        |>.congr (Eventually.of_forall fun ω => ?_)
      · rw [abs_of_pos (hupos 0 ω)]; exact (hu 0 ω).2
      · simp only [randEcon, hPdef, div_inv_eq_mul]
    · simp only [randEcon, mmin, abs_one, mul_one, div_one]
      have h1 := hxb t ω
      have h2 := hPpos t ω
      have h3 := hP2 t ω
      refine ⟨by norm_num, ?_, by norm_num, ?_⟩
      · rw [abs_le]; constructor <;> nlinarith
      · rw [hPdef (t + 1), div_inv_eq_mul, abs_of_nonneg (mul_nonneg h2.le (hupos (t + 1) ω).le)]
        nlinarith [hu (t + 1) ω]
  have hF : Fisher S (randEcon β ε) := fun t => by
    filter_upwards [hEu t] with ω h
    rw [h]
    simp [randEcon]
  have hιpos : ∀ t ω, 0 < iota (randEcon β ε) t ω := fun t ω => by
    simp only [iota, randEcon]
    have := hPle t ω
    have h2 : β * randP β ε t ω ≤ β * (2 / (1 + β)) := mul_le_mul_of_nonneg_left this hβ0.le
    have h3 : β * (2 / (1 + β)) < 1 := by rw [mul_div_assoc', div_lt_one (by linarith)]; linarith
    linarith
  have hmm : ∀ t ω, mmin (randEcon β ε) t ω = randP β ε t ω := fun t ω => by
    simp [mmin, randEcon]
  have hsbar : ∀ t ω, sbar (randEcon β ε) (randP β ε) t ω =
      randX β ε t ω - β * (1 + randP β ε t ω) := fun t ω => by
    simp only [sbar, iota, randEcon]
    field_simp [(hPpos t ω).ne']
    ring
  -- the valuation equation, by uniqueness of bounded forward solutions
  have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hsa := sbar_adapted hreg (M := randP β ε) hPa
  have hsb : ∀ t, ∀ᵐ ω ∂S.μ, |sbar (randEcon β ε) (randP β ε) t ω| ≤ 12 :=
    fun t => Eventually.of_forall fun ω => by
      rw [hsbar, abs_le]
      have := hxb t ω; have := hPpos t ω; have := hP2 t ω
      constructor <;> nlinarith
  have hxsol : S.Solves β (sbar (randEcon β ε) (randP β ε)) (randX β ε) := fun t => by
    have hpull := S.E_pullOut (f := fun ω => 1 + randP β ε t ω) (y := fun ω => 1 + b * ε (t + 1) ω)
      (stronglyMeasurable_const.add (hPa t)) (C := 3)
      (Eventually.of_forall fun ω => by
        rw [abs_le]; constructor <;> linarith [hPpos t ω, hP2 t ω])
      (integrable_of_bdd (hum (t + 1)) (K := 2) (Eventually.of_forall fun ω => by
        rw [abs_of_pos (hupos (t + 1) ω)]; exact (hu (t + 1) ω).2))
    have e1 : randX β ε (t + 1) =
        (fun ω => 1 + randP β ε t ω) * fun ω => 1 + b * ε (t + 1) ω := by
      funext ω; rw [hx]; rfl
    have hEu' := hEu t
    rw [hinvP] at hEu'
    filter_upwards [hpull, hEu'] with ω h1 h2
    rw [e1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, Pi.mul_apply, h2, hsbar]
    ring
  have hval : ∀ t, randX β ε t =ᵐ[S.μ] pvM S β (sbar (randEcon β ε) (randP β ε)) t :=
    S.forward_unique hβ hxsol (S.forwardSol_solves hβ hsa hsb)
      (fun t => ((hxa t).mono (S.𝓕.le t)).aestronglyMeasurable)
      (fun t => ((S.forwardSol_adapted β _ t).mono (S.𝓕.le t)).aestronglyMeasurable)
      ⟨6, fun t => Eventually.of_forall fun ω => by
        rw [abs_of_nonneg (hxb t ω).1]; exact (hxb t ω).2⟩
      (S.forwardSol_bdd hβ hsb)
  have heqm : EqmM S β (randEcon β ε).V (randEcon β ε).y (randP β ε)
      (randP β ε) (wealth (fun _ => 2) (fun _ _ => 1) (randP β ε))
      (sbar (randEcon β ε) (randP β ε)) := fun t =>
    ⟨Eventually.of_forall (hPpos t), Eventually.of_forall fun ω => by simp [randEcon],
      hval t⟩
  refine ⟨derived_of_eqmM hreg (fun _ => stronglyMeasurable_const) hPa
    (fun t => Eventually.of_forall fun ω => one_pos) hF
    (fun t => Eventually.of_forall fun ω => (hιpos t ω).le) heqm, hF, heqm⟩

/-- Cochrane (2023), §22.1, p. 496: the coin shock clamped to `[−1, 1]` (equal to the coin shock
almost surely). -/
noncomputable def coinClamp : ℕ → (ℕ → ℝ) → ℝ :=
  fun t ω => max (-1) (min 1 (ExpectationsMeasureIID.shock t ω))

/-- Cochrane (2023), §22.1, p. 496 ("fiscal surprises control unexpected inflation";
**a derived equilibrium on the i.i.d. coin economy**): with `0 < β < 1`, the economy
`randEcon β coinClamp` on `ExpectationsMeasureIID.iidSystem coin` (every history null) is a
derived equilibrium, and its date-1 inverse price level `1/P_1` is not almost surely equal to its
date-0 forecast — unexpected inflation is genuinely random. -/
theorem coin_random_derived_eqm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    DerivedEqm (ExpectationsMeasureIID.iidSystem ExpectationsMeasureIID.coin)
      (randEcon β coinClamp) (fun _ _ => 1) (randP β coinClamp) ∧
    ¬ invP (randEcon β coinClamp) 1 =ᵐ[(ExpectationsMeasureIID.iidSystem
      ExpectationsMeasureIID.coin).μ] (ExpectationsMeasureIID.iidSystem
        ExpectationsMeasureIID.coin).E 0 (invP (randEcon β coinClamp) 1) := by
  open ExpectationsMeasureIID in
  set S' := iidSystem coin with hS'
  have hεa : StronglyAdapted S'.𝓕 coinClamp := fun t =>
    (measurable_const.max (measurable_const.min
      (measurable_shock coin (le_refl t)))).stronglyMeasurable
  have hεb : ∀ t ω, |coinClamp t ω| ≤ 1 := fun t ω => by
    simp only [coinClamp]
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hεs : ∀ t, coinClamp t =ᵐ[S'.μ] shock t := fun t => by
    filter_upwards [shock_ae_bdd coin coin_bdd t] with ω h
    have h' := abs_le.1 h
    simp only [coinClamp]
    rw [min_eq_right h'.2, max_eq_right h'.1]
  have hεm : ∀ t, S'.E t (coinClamp (t + 1)) =ᵐ[S'.μ] 0 := fun t =>
    (S'.E_congr (hεs (t + 1)) t).trans (E_shock_zero (ν := coin) coin_mean t)
  refine ⟨(random_derived_eqm hβ0 hβ1 hεa hεb hεm).1, fun he => ?_⟩
  have h1 := he.trans (rand_E_invP (β := β) hεa hεb hεm 0)
  rw [rand_invP] at h1
  have hb : (1 - β) / 2 ≠ 0 := by intro h; linarith
  apply shock_not_ae_E (ν := coin) coin_mean coin_var one_pos 0
  have h2 : shock (0 + 1) =ᵐ[S'.μ] fun _ => (0 : ℝ) := by
    filter_upwards [h1, hεs 1] with ω h h'
    have h3 : (1 - β) / 2 * coinClamp 1 ω = 0 := by linarith
    rw [zero_add, ← h']
    exact (mul_eq_zero.1 h3).resolve_left hb
  exact h2.trans (E_shock_zero (ν := coin) coin_mean 0).symm

end Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdEqm
