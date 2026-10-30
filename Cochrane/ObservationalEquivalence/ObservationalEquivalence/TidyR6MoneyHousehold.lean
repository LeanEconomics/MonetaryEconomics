/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR5MoneyMeasure

/-!
# The household problem behind the money model of §22.1

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–496 (the
money model `M_tV_t = P_ty_t`, `(B_{t−1} + M_{t−1})/P_t = E_t∑βʲs_{t+j}`, "simplifying further to
the case that money pays interest, or that surpluses react one-for-one to seigniorage"), which is
the model of §19.1, pp. 434–435, built on §3.4, pp. 57–59 (the flow condition (3.9) with money
and the bond price `1/(1 + i_t)`), with the cash-in-advance logic of §19.5, pp. 447–451.

The project's money modules (`MoneyRegimes`, `TidyR5MoneyUncertainty`, `TidyR5MoneyMeasure`)
impose the three equations. Here they are derived from a household's optimisation problem on a
genuine probability space with any filtration (`ExpectationsMeasure.MeasExpectationSystem`,
information may grow forever, every constraint holds almost surely).

## The household problem

A risk-neutral household (the book's discounting `βʲ` of a random endowment `y_t` is exactly
risk neutrality) maximises `E∑βᵗc_t`, the genuine integral `∑βᵗE c_t` of an absolutely
convergent series (`expU`, `expU_eq_integral_tsum`). It enters date `t` with nominal wealth
`W_t = B_{t−1} + M_{t−1}` (`wealth`; `W_0` given) and faces, almost surely at every date,
* the flow constraint (3.9) `W_t + P_ty_t = P_tc_t + P_tτ_t + Q_tB_t + Q^m_tM_t` (`Flow`):
  one-period nominal bonds cost `Q_t = 1/(1 + i_t)`, money held overnight costs `Q^m_t`
  (`Q^m = 1` for cash, `Q^m = Q` for money that pays the bond rate, as in the book's discount
  notation of p. 58), and `τ_t` are lump-sum taxes, the primary surplus;
* the cash constraint `M_tV_t ≥ P_ty_t` (money demand: nominal income turns over at velocity
  `V_t`; it is the cash-in-advance constraint (19.24)–(19.26) of p. 448 at `V = 1`), and no
  borrowing `B_t ≥ 0` (`Constr`).
Plans are adapted and their holdings have finite expected real value (`Integ`). The opportunity
cost of money is `ι_t = Q^m_t − Q_t` (`iota`).

## Main results

* `dev_ineq`: at an optimum, every bounded `𝓕_t`-measurable reallocation `(b, m)` of bonds and
  money, financed by consumption at `t` and repaid at `t + 1`, satisfies
  `E[bD_t + mG_t] ≥ 0`, where `D_t = βᵗQ_t/P_t − β^{t+1}E_t[1/P_{t+1}]` (`eulerGap`) and
  `G_t = βᵗQ^m_t/P_t − β^{t+1}E_t[1/P_{t+1}]` (`moneyGap`).
* Necessity of the first-order conditions: `eulerGap_nonneg` and `eulerGap_eq_zero` (the bond
  price `Q_t ≥ βP_tE_t[1/P_{t+1}]`, with equality where bonds are held: the Fisher equation),
  `moneyGap_nonneg` and `moneyGap_eq_zero` (money is never dominated, and where the cash
  constraint is slack the marginal unit of money earns the bond return).
* `tvc_of_optimal`: the transversality condition `βᵀE[W_T/P_T] → 0` is necessary (the household
  could liquidate its bonds and excess money at `T`).
* `optimal_of_foc`: sufficiency — the first-order conditions and the transversality condition
  make a feasible admissible plan optimal against every feasible admissible plan;
  `optimal_iff_foc`: with bonds held at every date, the two together.
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MoneyHousehold

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure

variable (Ω : Type*)

/-- Cochrane (2023), §22.1, p. 496, §19.1, p. 434, and §3.4, pp. 57–58: what the household takes
as given — the discount factor, the endowment `y_t`, velocity `V_t`, lump-sum taxes `τ_t`, the
price level `P_t`, the bond price `Q_t = 1/(1 + i_t)`, the price of overnight money `Q^m_t` and
initial nominal wealth `W_0 = B_{−1} + M_{−1}`. -/
structure Econ where
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The endowment `y_t`. -/
  y : ℕ → Ω → ℝ
  /-- Velocity `V_t`. -/
  V : ℕ → Ω → ℝ
  /-- Lump-sum taxes, the primary surplus `τ_t`. -/
  τ : ℕ → Ω → ℝ
  /-- The price level `P_t`. -/
  P : ℕ → Ω → ℝ
  /-- The one-period nominal bond price `Q_t = 1/(1 + i_t)`. -/
  Q : ℕ → Ω → ℝ
  /-- The price of money held overnight, `Q^m_t = 1/(1 + i^m_t)`. -/
  Qm : ℕ → Ω → ℝ
  /-- Initial nominal wealth `W_0 = B_{−1} + M_{−1}`. -/
  W0 : Ω → ℝ

/-- Cochrane (2023), §19.5.1, p. 448, and §3.4, p. 57: a plan — consumption `c_t`, bonds `B_t`
and money `M_t` chosen at `t` and carried into `t + 1`. -/
structure Plan where
  /-- Consumption `c_t`. -/
  c : ℕ → Ω → ℝ
  /-- Nominal bonds bought at `t`, `B_t`. -/
  B : ℕ → Ω → ℝ
  /-- Nominal money held overnight from `t`, `M_t`. -/
  M : ℕ → Ω → ℝ

variable {Ω}

/-- Cochrane (2023), §22.1, p. 496: nominal wealth carried into date `t`,
`W_0` and `W_{t+1} = B_t + M_t`. -/
def wealth (W0 : Ω → ℝ) (B M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => W0
  | t + 1 => B t + M t

/-- Cochrane (2023), §19.1, p. 434 (eq. (19.1)): the least money the cash constraint allows,
`P_ty_t/V_t`. -/
noncomputable def mmin (e : Econ Ω) (t : ℕ) : Ω → ℝ := fun ω => e.P t ω * e.y t ω / e.V t ω

/-- Cochrane (2023), §3.4, p. 58: the opportunity cost of money in discount units,
`ι_t = Q^m_t − Q_t` (`= 1 − Q_t = i_t/(1 + i_t)` for cash). -/
def iota (e : Econ Ω) (t : ℕ) : Ω → ℝ := fun ω => e.Qm t ω - e.Q t ω

/-- Cochrane (2023), §22.1, p. 496: the reciprocal price level `1/P_t`. -/
noncomputable def invP (e : Econ Ω) (t : ℕ) : Ω → ℝ := fun ω => (e.P t ω)⁻¹

/-- Cochrane (2023), §22.1, p. 496: a plan changed at one date, `x` at `t` and `0` elsewhere. -/
def oneDate (t : ℕ) (x : Ω → ℝ) : ℕ → Ω → ℝ := fun s => if s = t then x else 0

/-- Cochrane (2023), §22.1, p. 496: a consumption change at two dates, `a` at `t`, `b` at `t + 1`
and `0` elsewhere. -/
def twoDate (t : ℕ) (a b : Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => if s = t then a else if s = t + 1 then b else 0

/-- Cochrane (2023), §22.1, p. 496: the sum of a plan and a change of plan. -/
def addPlan (p d : Plan Ω) : Plan Ω := ⟨p.c + d.c, p.B + d.B, p.M + d.M⟩

/-- Cochrane (2023), §22.1, p. 496 (tool): a one-date change at its date. -/
@[simp] theorem oneDate_self (t : ℕ) (x : Ω → ℝ) : oneDate t x t = x := by simp [oneDate]

/-- Cochrane (2023), §22.1, p. 496 (tool): a one-date change at another date. -/
theorem oneDate_ne {s t : ℕ} (h : s ≠ t) (x : Ω → ℝ) : oneDate t x s = 0 := by
  simp [oneDate, h]

/-- Cochrane (2023), §22.1, p. 496 (tool): a two-date change at its first date. -/
@[simp] theorem twoDate_self (t : ℕ) (a b : Ω → ℝ) : twoDate t a b t = a := by simp [twoDate]

/-- Cochrane (2023), §22.1, p. 496 (tool): a two-date change at its second date. -/
@[simp] theorem twoDate_succ (t : ℕ) (a b : Ω → ℝ) : twoDate t a b (t + 1) = b := by
  simp [twoDate]

/-- Cochrane (2023), §22.1, p. 496 (tool): a two-date change at any other date. -/
theorem twoDate_ne {s t : ℕ} (h1 : s ≠ t) (h2 : s ≠ t + 1) (a b : Ω → ℝ) :
    twoDate t a b s = 0 := by
  simp [twoDate, h1, h2]

variable [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), §2.1, p. 21, and §19.5.1, p. 448: a plan is chosen with the information of
each date (adapted consumption, bonds and money). -/
def AdaptedPlan (p : Plan Ω) : Prop :=
  StronglyAdapted S.𝓕 p.c ∧ StronglyAdapted S.𝓕 p.B ∧ StronglyAdapted S.𝓕 p.M

/-- Cochrane (2023), eq. (3.9), p. 57 (with the money price of p. 58): the flow constraint
`W_t + P_ty_t = P_tc_t + P_tτ_t + Q_tB_t + Q^m_tM_t`, almost surely at every date. -/
def Flow (e : Econ Ω) (p : Plan Ω) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, wealth e.W0 p.B p.M t ω + e.P t ω * e.y t ω =
    e.P t ω * p.c t ω + e.P t ω * e.τ t ω + e.Q t ω * p.B t ω + e.Qm t ω * p.M t ω

/-- Cochrane (2023), §19.5.1, p. 448 ((19.24)–(19.26) at `V = 1`) and §19.1, p. 434 (19.1): no
borrowing `B_t ≥ 0` and the cash constraint `M_t ≥ P_ty_t/V_t`, almost surely. -/
def Constr (e : Econ Ω) (p : Plan Ω) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ p.B t ω ∧ mmin e t ω ≤ p.M t ω

/-- Cochrane (2023), §19.3, p. 439 (present values must be meaningful): consumption and the real
values of the positions are integrable. -/
def Integ (e : Econ Ω) (p : Plan Ω) : Prop :=
  ∀ t, Integrable (p.c t) S.μ ∧ Integrable (fun ω => p.B t ω / e.P (t + 1) ω) S.μ ∧
    Integrable (fun ω => p.M t ω / e.P (t + 1) ω) S.μ ∧
    Integrable (fun ω => e.Q t ω * p.B t ω / e.P t ω) S.μ ∧
    Integrable (fun ω => e.Qm t ω * p.M t ω / e.P t ω) S.μ

/-- Cochrane (2023), §19.5.1, pp. 448–449: a feasible plan. -/
def Feasible (e : Econ Ω) (p : Plan Ω) : Prop :=
  AdaptedPlan S p ∧ Flow S e p ∧ Constr S e p ∧ Integ S e p

/-- Cochrane (2023), §2.1, p. 21: expected discounted utility converges absolutely,
`∑βᵗE|c_t| < ∞`. -/
def Admissible (β : ℝ) (c : ℕ → Ω → ℝ) : Prop :=
  Summable fun t => β ^ t * ∫ ω, |c t ω| ∂S.μ

/-- Cochrane (2023), §2.1, p. 21: expected discounted utility of the risk-neutral household,
`∑βᵗE c_t`. -/
noncomputable def expU (β : ℝ) (c : ℕ → Ω → ℝ) : ℝ := ∑' t, β ^ t * ∫ ω, c t ω ∂S.μ

/-- Cochrane (2023), §2.1, p. 21, and §19.5.1, p. 448: an optimal plan — feasible, admissible and
unbeaten by every feasible admissible plan. -/
def Optimal (e : Econ Ω) (p : Plan Ω) : Prop :=
  Feasible S e p ∧ Admissible S e.β p.c ∧
    ∀ p' : Plan Ω, Feasible S e p' → Admissible S e.β p'.c → expU S e.β p'.c ≤ expU S e.β p.c

/-- Cochrane (2023), §22.1, p. 496: the regularity the derivation uses — `0 < β < 1`; adapted
prices and exogenous processes; positive price level, velocity and endowment; integrable
`1/P_t`, `Q_t/P_t`, `Q^m_t/P_t` and `W_0/P_0`; and a uniform bound on the endowment, taxes,
the cost of minimal money `Q^m_ty_t/V_t` and its real value tomorrow `P_ty_t/(V_tP_{t+1})`. -/
def EconReg (e : Econ Ω) : Prop :=
  (0 < e.β ∧ e.β < 1) ∧
  (StronglyAdapted S.𝓕 e.P ∧ StronglyAdapted S.𝓕 e.Q ∧ StronglyAdapted S.𝓕 e.Qm ∧
    StronglyAdapted S.𝓕 e.y ∧ StronglyAdapted S.𝓕 e.V ∧ StronglyAdapted S.𝓕 e.τ) ∧
  (∀ t, ∀ᵐ ω ∂S.μ, 0 < e.P t ω ∧ 0 < e.V t ω ∧ 0 < e.y t ω) ∧
  (∀ t, Integrable (invP e t) S.μ ∧ Integrable (fun ω => e.Q t ω / e.P t ω) S.μ ∧
    Integrable (fun ω => e.Qm t ω / e.P t ω) S.μ) ∧
  Integrable (fun ω => e.W0 ω / e.P 0 ω) S.μ ∧
  ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |e.y t ω| ≤ K ∧ |e.τ t ω| ≤ K ∧ |e.Qm t ω * e.y t ω / e.V t ω| ≤ K ∧
    |mmin e t ω / e.P (t + 1) ω| ≤ K

/-- Cochrane (2023), §2.1, p. 22 (the bond first-order condition): the Euler gap
`D_t = βᵗQ_t/P_t − β^{t+1}E_t[1/P_{t+1}]`. -/
noncomputable def eulerGap (e : Econ Ω) (t : ℕ) : Ω → ℝ :=
  fun ω => e.β ^ t * (e.Q t ω / e.P t ω) - e.β ^ (t + 1) * S.E t (invP e (t + 1)) ω

/-- Cochrane (2023), §19.3, p. 440 (the money first-order condition): the money gap
`G_t = βᵗQ^m_t/P_t − β^{t+1}E_t[1/P_{t+1}]`. -/
noncomputable def moneyGap (e : Econ Ω) (t : ℕ) : Ω → ℝ :=
  fun ω => e.β ^ t * (e.Qm t ω / e.P t ω) - e.β ^ (t + 1) * S.E t (invP e (t + 1)) ω

/-- Cochrane (2023), §22.1, p. 496: the reallocation of `b` bonds and `m` money at date `t`,
paid for by consumption at `t` and repaid in consumption at `t + 1`. -/
noncomputable def dev (e : Econ Ω) (t : ℕ) (b m : Ω → ℝ) : Plan Ω :=
  ⟨twoDate t (fun ω => -(e.Q t ω * b ω + e.Qm t ω * m ω) / e.P t ω)
    (fun ω => (b ω + m ω) / e.P (t + 1) ω), oneDate t b, oneDate t m⟩

/-- Cochrane (2023), §22.1, p. 496: real wealth carried into date `t`, `W_t/P_t`. -/
noncomputable def realWealth (e : Econ Ω) (p : Plan Ω) (t : ℕ) : Ω → ℝ :=
  fun ω => wealth e.W0 p.B p.M t ω / e.P t ω

/-- Cochrane (2023), §19.5.1, p. 449 (the transversality argument): consumption at date `j + 1`
after liquidation — no bonds, minimal money, `M_jV_j = P_jy_j` carried in:
`P_jy_j/(V_jP_{j+1}) + y_{j+1} − τ_{j+1} − Q^m_{j+1}y_{j+1}/V_{j+1}`. -/
noncomputable def cref (e : Econ Ω) (j : ℕ) : Ω → ℝ :=
  fun ω => mmin e j ω / e.P (j + 1) ω + e.y (j + 1) ω - e.τ (j + 1) ω -
    e.Qm (j + 1) ω * e.y (j + 1) ω / e.V (j + 1) ω

/-- Cochrane (2023), §19.5.1, p. 449: the liquidation value consumed at `T`,
`Q_TB_T/P_T + Q^m_TM_T/P_T − Q^m_Ty_T/V_T` (bonds and money beyond the minimum, at date-`T`
prices). -/
noncomputable def liqValue (e : Econ Ω) (p : Plan Ω) (T : ℕ) : Ω → ℝ :=
  fun ω => e.Q T ω * p.B T ω / e.P T ω + e.Qm T ω * p.M T ω / e.P T ω -
    e.Qm T ω * e.y T ω / e.V T ω

/-- Cochrane (2023), §19.5.1, p. 449: the plan that follows `p` before `T`, consumes its
liquidation value at `T`, and from then on holds no bonds and the least money. -/
noncomputable def liq (e : Econ Ω) (p : Plan Ω) (T : ℕ) : Plan Ω :=
  ⟨fun s => if s < T then p.c s else if s = T then p.c T + liqValue e p T else cref e (s - 1),
    fun s => if s < T then p.B s else 0, fun s => if s < T then p.M s else mmin e s⟩

/-! ### Elementary facts -/

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496: wealth is additive in the positions. -/
theorem wealth_add (W0 : Ω → ℝ) (B M dB dM : ℕ → Ω → ℝ) (t : ℕ) :
    wealth W0 (B + dB) (M + dM) t = wealth W0 B M t + wealth 0 dB dM t := by
  cases t with
  | zero => simp [wealth]
  | succ t =>
    simp only [wealth, Pi.add_apply]
    abel

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496: the wealth change from a one-date reallocation arrives at
`t + 1`. -/
theorem wealth_oneDate (t : ℕ) (b m : Ω → ℝ) (s : ℕ) :
    wealth 0 (oneDate t b) (oneDate t m) s = if s = t + 1 then b + m else 0 := by
  cases s with
  | zero => simp [wealth]
  | succ s =>
    simp only [wealth, oneDate, add_left_inj]
    split_ifs <;> simp

/-- Cochrane (2023), §2.1, p. 21: an admissible consumption plan has a summable utility series. -/
theorem summable_of_admissible {β : ℝ} (hβ : 0 ≤ β) {c : ℕ → Ω → ℝ}
    (hc : Admissible S β c) : Summable fun t => β ^ t * ∫ ω, c t ω ∂S.μ := by
  refine Summable.of_norm_bounded hc fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ t)]
  exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (pow_nonneg hβ t)

/-- Cochrane (2023), §2.1, p. 21: expected discounted utility is the genuine integral of the
discounted consumption stream, `∑βᵗE c_t = E∑βᵗc_t` (Fubini for an absolutely convergent
series). -/
theorem expU_eq_integral_tsum {β : ℝ} (hβ : 0 ≤ β) {c : ℕ → Ω → ℝ}
    (hc : ∀ t, Integrable (c t) S.μ) (ha : Admissible S β c) :
    expU S β c = ∫ ω, ∑' t, β ^ t * c t ω ∂S.μ := by
  rw [← integral_tsum_of_summable_integral_norm (fun t => (hc t).const_mul (β ^ t))]
  · refine tsum_congr fun t => ?_
    rw [integral_const_mul]
  · refine ha.congr fun t => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ t)]

/-- Cochrane (2023), §2.1, p. 21: expected utility is additive in consumption changes (both
admissible, all dates integrable). -/
theorem expU_add {β : ℝ} (hβ : 0 ≤ β) {c d : ℕ → Ω → ℝ} (hc : ∀ t, Integrable (c t) S.μ)
    (hd : ∀ t, Integrable (d t) S.μ) (hca : Admissible S β c) (hda : Admissible S β d) :
    Admissible S β (c + d) ∧ expU S β (c + d) = expU S β c + expU S β d := by
  constructor
  · refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ t)
      (integral_nonneg fun ω => abs_nonneg _)) (fun t => ?_) (hca.add hda)
    rw [← mul_add, ← integral_add (hc t).abs (hd t).abs]
    refine mul_le_mul_of_nonneg_left (integral_mono ((hc t).add (hd t)).abs
      ((hc t).abs.add (hd t).abs) fun ω => ?_) (pow_nonneg hβ t)
    exact abs_add_le _ _
  · rw [expU, expU, expU, ← (summable_of_admissible S hβ hca).tsum_add
      (summable_of_admissible S hβ hda)]
    refine tsum_congr fun t => ?_
    rw [← mul_add, ← integral_add (hc t) (hd t)]
    rfl

/-- Cochrane (2023), §22.1, p. 496: a two-date consumption change is admissible and changes
expected utility by `βᵗE a + β^{t+1}E b`. -/
theorem expU_twoDate {β : ℝ} (t : ℕ) (a b : Ω → ℝ) :
    Admissible S β (twoDate t a b) ∧
      expU S β (twoDate t a b) = β ^ t * ∫ ω, a ω ∂S.μ + β ^ (t + 1) * ∫ ω, b ω ∂S.μ := by
  have hz : ∀ s ∉ ({t, t + 1} : Finset ℕ), twoDate t a b s = 0 := fun s hs => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    simp [twoDate, hs.1, hs.2]
  constructor
  · refine summable_of_ne_finset_zero (s := {t, t + 1}) fun s hs => ?_
    simp [hz s hs]
  · rw [expU, tsum_eq_sum (s := {t, t + 1}) fun s hs => by simp [hz s hs],
      Finset.sum_pair (by omega)]
    simp [twoDate]

/-! ### Measurability and integrability tools -/

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496 (tool): quotients of measurable real variables are strongly
measurable, for any σ-algebra. -/
theorem sm_div {m : MeasurableSpace Ω} {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) : StronglyMeasurable[m] (fun ω => f ω / g ω) :=
  (hf.measurable.div hg.measurable).stronglyMeasurable

/-- Cochrane (2023), §22.1, p. 496 (tool): a bounded variable known at `t` times an integrable one
is integrable. -/
theorem integrable_bdd_mul {t : ℕ} {f g : Ω → ℝ} (hg : Integrable g S.μ)
    (hf : StronglyMeasurable[S.𝓕 t] f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    Integrable (fun ω => f ω * g ω) S.μ :=
  hg.bdd_mul ((hf.mono (S.𝓕.le t)).aestronglyMeasurable)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

/-- Cochrane (2023), §22.1, p. 496 (tool): a nonnegative integrable variable with nonpositive
mean vanishes almost surely. -/
theorem ae_zero_of_nonneg_integral_nonpos {g : Ω → ℝ} (hg : 0 ≤ᵐ[S.μ] g)
    (hgi : Integrable g S.μ) (h : ∫ ω, g ω ∂S.μ ≤ 0) : g =ᵐ[S.μ] 0 :=
  (integral_eq_zero_iff_of_nonneg_ae hg hgi).1 (le_antisymm h (integral_nonneg_of_ae hg))

/-! ### Reallocations of bonds and money -/

variable {S}

/-- Cochrane (2023), §22.1, p. 496: the reallocation `dev` satisfies the flow constraint with zero
initial wealth (almost surely, where `P > 0`). -/
theorem flow_addPlan_dev {e : Econ Ω} {p : Plan Ω} (hpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < e.P t ω)
    (hp : Flow S e p) (t : ℕ) (b m : Ω → ℝ) : Flow S e (addPlan p (dev e t b m)) := by
  intro s
  filter_upwards [hp s, hpos s] with ω h hP
  simp only [addPlan, dev]
  rw [wealth_add, wealth_oneDate]
  simp only [Pi.add_apply]
  by_cases h1 : s = t
  · subst h1
    simp only [twoDate_self, oneDate_self, show ¬ s = s + 1 by omega, ↓reduceIte,
      Pi.zero_apply]
    field_simp
    linear_combination h
  · by_cases h2 : s = t + 1
    · subst h2
      simp only [twoDate_succ, oneDate_ne h1, ↓reduceIte, Pi.zero_apply, Pi.add_apply]
      field_simp
      linear_combination h
    · simp only [twoDate_ne h1 h2, oneDate_ne h1, h2, ↓reduceIte, Pi.zero_apply]
      linear_combination h

/-- Cochrane (2023), §22.1, p. 496: a bounded reallocation known at `t` that respects the no
borrowing and cash constraints keeps a feasible plan feasible. -/
theorem feasible_dev {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hp : Feasible S e p)
    {t : ℕ} {b m : Ω → ℝ} (hb : StronglyMeasurable[S.𝓕 t] b) (hm : StronglyMeasurable[S.𝓕 t] m)
    {C : ℝ} (hbC : ∀ ω, |b ω| ≤ C) (hmC : ∀ ω, |m ω| ≤ C)
    (hB : ∀ᵐ ω ∂S.μ, 0 ≤ p.B t ω + b ω) (hM : ∀ᵐ ω ∂S.μ, mmin e t ω ≤ p.M t ω + m ω) :
    Feasible S e (addPlan p (dev e t b m)) := by
  obtain ⟨-, ⟨hPa, hQa, hQma, -, -, -⟩, hpos, hint, -, -⟩ := hreg
  obtain ⟨⟨hca, hBa, hMa⟩, hflow, hcon, hI⟩ := hp
  have hb1 : StronglyMeasurable[S.𝓕 (t + 1)] b := hb.mono (S.𝓕.mono (Nat.le_succ t))
  have hm1 : StronglyMeasurable[S.𝓕 (t + 1)] m := hm.mono (S.𝓕.mono (Nat.le_succ t))
  have hbm : ∀ ω, |b ω + m ω| ≤ C + C := fun ω => (abs_add_le _ _).trans (add_le_add (hbC ω)
    (hmC ω))
  refine ⟨⟨fun s => ?_, fun s => ?_, fun s => ?_⟩, flow_addPlan_dev (fun s => ?_) hflow t b m,
    fun s => ?_, fun s => ?_⟩
  · simp only [addPlan, dev, Pi.add_apply]
    by_cases h1 : s = t
    · subst h1
      rw [twoDate_self]
      exact (hca s).add (sm_div ((((hQa s).mul hb).add ((hQma s).mul hm)).neg) (hPa s))
    · by_cases h2 : s = t + 1
      · subst h2
        rw [twoDate_succ]
        exact (hca (t + 1)).add (sm_div (hb1.add hm1) (hPa (t + 1)))
      · rw [twoDate_ne h1 h2, add_zero]
        exact hca s
  · simp only [addPlan, dev, Pi.add_apply]
    by_cases h1 : s = t
    · subst h1
      rw [oneDate_self]
      exact (hBa s).add hb
    · rw [oneDate_ne h1, add_zero]
      exact hBa s
  · simp only [addPlan, dev, Pi.add_apply]
    by_cases h1 : s = t
    · subst h1
      rw [oneDate_self]
      exact (hMa s).add hm
    · rw [oneDate_ne h1, add_zero]
      exact hMa s
  · filter_upwards [hpos s] with ω h
    exact h.1
  · simp only [addPlan, dev, Pi.add_apply]
    by_cases h1 : s = t
    · subst h1
      filter_upwards [hB, hM] with ω hb' hm'
      simp only [oneDate_self]
      exact ⟨hb', hm'⟩
    · filter_upwards [hcon s] with ω h
      simpa [oneDate_ne h1] using h
  · obtain ⟨hic, hiB, hiM, hiQ, hiQm⟩ := hI s
    obtain ⟨hinv, hQP, hQmP⟩ := hint s
    obtain ⟨hinv1, -, -⟩ := hint (s + 1)
    simp only [addPlan, dev, Pi.add_apply]
    by_cases h1 : s = t
    · subst h1
      simp only [twoDate_self, oneDate_self]
      have ea : (fun ω => -(e.Q s ω * b ω + e.Qm s ω * m ω) / e.P s ω) =
          fun ω => -(b ω * (e.Q s ω / e.P s ω) + m ω * (e.Qm s ω / e.P s ω)) := by
        funext ω; ring
      refine ⟨hic.add ?_, ?_, ?_, ?_, ?_⟩
      · rw [ea]
        exact ((integrable_bdd_mul S hQP hb hbC).add (integrable_bdd_mul S hQmP hm hmC)).neg
      · have e1 : (fun ω => (p.B s ω + b ω) / e.P (s + 1) ω) =
            fun ω => p.B s ω / e.P (s + 1) ω + b ω * invP e (s + 1) ω := by
          funext ω; simp only [invP]; ring
        rw [e1]
        exact hiB.add (integrable_bdd_mul S hinv1 hb hbC)
      · have e1 : (fun ω => (p.M s ω + m ω) / e.P (s + 1) ω) =
            fun ω => p.M s ω / e.P (s + 1) ω + m ω * invP e (s + 1) ω := by
          funext ω; simp only [invP]; ring
        rw [e1]
        exact hiM.add (integrable_bdd_mul S hinv1 hm hmC)
      · have e1 : (fun ω => e.Q s ω * (p.B s ω + b ω) / e.P s ω) =
            fun ω => e.Q s ω * p.B s ω / e.P s ω + b ω * (e.Q s ω / e.P s ω) := by
          funext ω; ring
        rw [e1]
        exact hiQ.add (integrable_bdd_mul S hQP hb hbC)
      · have e1 : (fun ω => e.Qm s ω * (p.M s ω + m ω) / e.P s ω) =
            fun ω => e.Qm s ω * p.M s ω / e.P s ω + m ω * (e.Qm s ω / e.P s ω) := by
          funext ω; ring
        rw [e1]
        exact hiQm.add (integrable_bdd_mul S hQmP hm hmC)
    · simp only [oneDate_ne h1, Pi.zero_apply, add_zero]
      refine ⟨?_, hiB, hiM, hiQ, hiQm⟩
      by_cases h2 : s = t + 1
      · subst h2
        rw [twoDate_succ]
        have e1 : (fun ω => (b ω + m ω) / e.P (t + 1) ω) =
            fun ω => (b ω + m ω) * invP e (t + 1) ω := by
          funext ω; simp only [invP]; ring
        refine hic.add ?_
        rw [e1]
        exact integrable_bdd_mul S hinv (hb.add hm) hbm
      · rw [twoDate_ne h1 h2, add_zero]
        exact hic

/-! ### The first-order conditions are necessary -/

/-- Cochrane (2023), §2.1, p. 22: the Euler gap is known at `t`. -/
theorem eulerGap_sm {e : Econ Ω} (hreg : EconReg S e) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (eulerGap S e t) := by
  obtain ⟨-, ⟨hPa, hQa, -, -, -, -⟩, -⟩ := hreg
  exact ((measurable_const.mul ((hQa t).measurable.div (hPa t).measurable)).sub
    (measurable_const.mul (S.stronglyMeasurable_E t _).measurable)).stronglyMeasurable

/-- Cochrane (2023), §19.3, p. 440: the money gap is known at `t`. -/
theorem moneyGap_sm {e : Econ Ω} (hreg : EconReg S e) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (moneyGap S e t) := by
  obtain ⟨-, ⟨hPa, -, hQma, -, -, -⟩, -⟩ := hreg
  exact ((measurable_const.mul ((hQma t).measurable.div (hPa t).measurable)).sub
    (measurable_const.mul (S.stronglyMeasurable_E t _).measurable)).stronglyMeasurable

/-- Cochrane (2023), §2.1, p. 22: the Euler gap is integrable. -/
theorem eulerGap_integrable {e : Econ Ω} (hreg : EconReg S e) (t : ℕ) :
    Integrable (eulerGap S e t) S.μ := by
  obtain ⟨-, -, -, hint, -⟩ := hreg
  exact ((hint t).2.1.const_mul _).sub ((S.integrable_E t _).const_mul _)

/-- Cochrane (2023), §19.3, p. 440: the money gap is integrable. -/
theorem moneyGap_integrable {e : Econ Ω} (hreg : EconReg S e) (t : ℕ) :
    Integrable (moneyGap S e t) S.μ := by
  obtain ⟨-, -, -, hint, -⟩ := hreg
  exact ((hint t).2.2.const_mul _).sub ((S.integrable_E t _).const_mul _)

/-- Cochrane (2023), §19.1, p. 434: the least money is known at `t`. -/
theorem mmin_sm {e : Econ Ω} (hreg : EconReg S e) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (mmin e t) := by
  obtain ⟨-, ⟨hPa, -, -, hya, hVa, -⟩, -⟩ := hreg
  exact sm_div ((hPa t).mul (hya t)) (hVa t)

/-- Cochrane (2023), §22.1, p. 496 (**the reallocation inequality**): at an optimal plan, every
bounded reallocation `(b, m)` known at `t` that respects the no-borrowing and cash constraints
satisfies `E[bD_t + mG_t] ≥ 0` — it cannot raise expected utility, whose change is
`−E[bD_t + mG_t]`. -/
theorem dev_ineq {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hopt : Optimal S e p)
    {t : ℕ} {b m : Ω → ℝ} (hb : StronglyMeasurable[S.𝓕 t] b) (hm : StronglyMeasurable[S.𝓕 t] m)
    {C : ℝ} (hbC : ∀ ω, |b ω| ≤ C) (hmC : ∀ ω, |m ω| ≤ C)
    (hB : ∀ᵐ ω ∂S.μ, 0 ≤ p.B t ω + b ω) (hM : ∀ᵐ ω ∂S.μ, mmin e t ω ≤ p.M t ω + m ω) :
    0 ≤ ∫ ω, (b ω * eulerGap S e t ω + m ω * moneyGap S e t ω) ∂S.μ := by
  have hβ0 : 0 ≤ e.β := hreg.1.1.le
  have hinv1 : Integrable (invP e (t + 1)) S.μ := (hreg.2.2.2.1 (t + 1)).1
  have hf := feasible_dev hreg hopt.1 hb hm hbC hmC hB hM
  set a : Ω → ℝ := fun ω => -(e.Q t ω * b ω + e.Qm t ω * m ω) / e.P t ω with ha
  set a' : Ω → ℝ := fun ω => (b ω + m ω) / e.P (t + 1) ω with ha'
  have hci : ∀ s, Integrable (p.c s) S.μ := fun s => (hopt.1.2.2.2 s).1
  have hdi : ∀ s, Integrable (twoDate t a a' s) S.μ := fun s => by
    have h1 := ((hf.2.2.2 s).1.sub (hci s))
    have e1 : (addPlan p (dev e t b m)).c s - p.c s = twoDate t a a' s := by
      funext ω
      simp only [addPlan, dev, Pi.sub_apply, Pi.add_apply, ha, ha']
      ring
    rwa [e1] at h1
  obtain ⟨hadm, heq⟩ := expU_add S hβ0 hci hdi hopt.2.1 (expU_twoDate S (β := e.β) t a a').1
  have hle := hopt.2.2 _ hf hadm
  change expU S e.β (p.c + twoDate t a a') ≤ expU S e.β p.c at hle
  rw [heq, (expU_twoDate S t a a').2] at hle
  have hai : Integrable a S.μ := by simpa using hdi t
  have hbm : ∀ ω, |b ω + m ω| ≤ C + C := fun ω =>
    (abs_add_le _ _).trans (add_le_add (hbC ω) (hmC ω))
  have hX : Integrable (fun ω => (b ω + m ω) * S.E t (invP e (t + 1)) ω) S.μ :=
    integrable_bdd_mul S (S.integrable_E t _) (hb.add hm) hbm
  have hpull : ∫ ω, (b ω + m ω) * S.E t (invP e (t + 1)) ω ∂S.μ = ∫ ω, a' ω ∂S.μ := by
    have h1 := S.E_pullOut (f := fun ω => b ω + m ω) (hb.add hm)
      (Eventually.of_forall hbm) hinv1
    have h2 : ∫ ω, (b ω + m ω) * S.E t (invP e (t + 1)) ω ∂S.μ =
        ∫ ω, S.E t ((fun ω => b ω + m ω) * invP e (t + 1)) ω ∂S.μ :=
      integral_congr_ae (h1.symm)
    rw [h2, S.integral_E]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply, invP, ha', div_eq_mul_inv]
  have hrw : (fun ω => b ω * eulerGap S e t ω + m ω * moneyGap S e t ω) =
      fun ω => e.β ^ t * (-a ω) - e.β ^ (t + 1) * ((b ω + m ω) * S.E t (invP e (t + 1)) ω) := by
    funext ω
    simp only [eulerGap, moneyGap, ha]
    ring
  have h1 : Integrable (fun ω => e.β ^ t * -a ω) S.μ := hai.neg.const_mul _
  rw [hrw, integral_sub h1 (hX.const_mul _), integral_const_mul,
    integral_const_mul, integral_neg, hpull]
  linarith

/-- Cochrane (2023), §22.1, p. 496 (tool): if `0 ≤ E[w f]` for the indicator `w` of `{f < 0}`
(an event known at `t`), then `f ≥ 0` almost surely. -/
theorem nonneg_of_indicator_ineq {t : ℕ} {f : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 t] f)
    (hfi : Integrable f S.μ)
    (h : 0 ≤ ∫ ω, {ω | f ω < 0}.indicator (fun _ => (1 : ℝ)) ω * f ω ∂S.μ) :
    0 ≤ᵐ[S.μ] f := by
  have hA : MeasurableSet[S.𝓕 t] {ω | f ω < 0} := measurableSet_lt hf.measurable measurable_const
  set w : Ω → ℝ := {ω | f ω < 0}.indicator (fun _ => (1 : ℝ)) with hw
  have hws : StronglyMeasurable[S.𝓕 t] w := stronglyMeasurable_const.indicator hA
  have hwC : ∀ ω, |w ω| ≤ 1 := fun ω => by
    simp only [hw, Set.indicator]
    split_ifs <;> norm_num
  have hg : 0 ≤ᵐ[S.μ] fun ω => -(w ω * f ω) := Eventually.of_forall fun ω => by
    simp only [hw, Set.indicator, Set.mem_ofPred_eq]
    split_ifs with h1
    · simp only [Pi.zero_apply, one_mul]; linarith
    · simp
  have hgi : Integrable (fun ω => -(w ω * f ω)) S.μ := (integrable_bdd_mul S hfi hws hwC).neg
  have h0 := ae_zero_of_nonneg_integral_nonpos S hg hgi (by rw [integral_neg]; linarith)
  filter_upwards [h0] with ω hω
  by_contra hneg
  push Not at hneg
  have hneg' : f ω < 0 := hneg
  have : w ω = 1 := by simp [hw, hneg']
  simp only [this, one_mul, Pi.zero_apply, neg_eq_zero] at hω
  linarith

/-- Cochrane (2023), eq. (2.3), p. 22, and §3.4, p. 57 (**the bond first-order condition,
inequality**): at an optimal plan `D_t ≥ 0`, i.e. `Q_t/P_t ≥ βE_t[1/P_{t+1}]` almost surely —
buying more bonds never pays. -/
theorem eulerGap_nonneg {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hopt : Optimal S e p)
    (t : ℕ) : 0 ≤ᵐ[S.μ] eulerGap S e t := by
  have hD := eulerGap_sm hreg t
  have hA : MeasurableSet[S.𝓕 t] {ω | eulerGap S e t ω < 0} :=
    measurableSet_lt hD.measurable measurable_const
  refine nonneg_of_indicator_ineq hD (eulerGap_integrable hreg t) ?_
  have h := dev_ineq hreg hopt (b := {ω | eulerGap S e t ω < 0}.indicator fun _ => (1 : ℝ))
    (m := 0) (stronglyMeasurable_const.indicator hA) stronglyMeasurable_const (C := 1)
    (fun ω => by simp only [Set.indicator]; split_ifs <;> norm_num) (fun ω => by simp)
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      have : 0 ≤ {ω | eulerGap S e t ω < 0}.indicator (fun _ => (1 : ℝ)) ω :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      linarith [h.1])
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      simpa using h.2)
  simpa using h

/-- Cochrane (2023), §19.3, p. 440 (**the money first-order condition, inequality**): at an
optimal plan `G_t ≥ 0`, i.e. `Q^m_t/P_t ≥ βE_t[1/P_{t+1}]` almost surely — holding more money
never pays. -/
theorem moneyGap_nonneg {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hopt : Optimal S e p)
    (t : ℕ) : 0 ≤ᵐ[S.μ] moneyGap S e t := by
  have hG := moneyGap_sm hreg t
  have hA : MeasurableSet[S.𝓕 t] {ω | moneyGap S e t ω < 0} :=
    measurableSet_lt hG.measurable measurable_const
  refine nonneg_of_indicator_ineq hG (moneyGap_integrable hreg t) ?_
  have h := dev_ineq hreg hopt (b := 0)
    (m := {ω | moneyGap S e t ω < 0}.indicator fun _ => (1 : ℝ))
    stronglyMeasurable_const (stronglyMeasurable_const.indicator hA) (C := 1) (fun ω => by simp)
    (fun ω => by simp only [Set.indicator]; split_ifs <;> norm_num)
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      simpa using h.1)
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      have : 0 ≤ {ω | moneyGap S e t ω < 0}.indicator (fun _ => (1 : ℝ)) ω :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      linarith [h.2])
  simpa using h

/-- Cochrane (2023), §22.1, p. 496 (tool): if `E[w f] ≤ 0` for the weight
`w = 1{f > 0}·max(0, min(x, 1))` (known at `t`), then almost surely `x > 0` forces `f ≤ 0`. -/
theorem nonpos_of_weight_ineq {t : ℕ} {f x : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 t] f)
    (hx : StronglyMeasurable[S.𝓕 t] x) (hfi : Integrable f S.μ)
    (h : ∫ ω, {ω | 0 < f ω}.indicator (fun _ => (1 : ℝ)) ω * max 0 (min (x ω) 1) * f ω ∂S.μ ≤ 0) :
    ∀ᵐ ω ∂S.μ, 0 < x ω → f ω ≤ 0 := by
  have hA : MeasurableSet[S.𝓕 t] {ω | 0 < f ω} := measurableSet_lt measurable_const hf.measurable
  set w : Ω → ℝ := fun ω => {ω | 0 < f ω}.indicator (fun _ => (1 : ℝ)) ω * max 0 (min (x ω) 1)
    with hw
  have hws : StronglyMeasurable[S.𝓕 t] w := (stronglyMeasurable_const.indicator hA).mul
    ((measurable_const.max (hx.measurable.min measurable_const)).stronglyMeasurable)
  have hwC : ∀ ω, |w ω| ≤ 1 := fun ω => by
    simp only [hw, Set.indicator]
    split_ifs
    · rw [one_mul, abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_right _ _)
    · simp
  have hg : 0 ≤ᵐ[S.μ] fun ω => w ω * f ω := Eventually.of_forall fun ω => by
    simp only [hw, Set.indicator, Set.mem_ofPred_eq]
    split_ifs with h1
    · exact mul_nonneg (by rw [one_mul]; exact le_max_left _ _) h1.le
    · simp
  have h0 := ae_zero_of_nonneg_integral_nonpos S hg (integrable_bdd_mul S hfi hws hwC) h
  filter_upwards [h0] with ω hω hxω
  by_contra hpos
  push Not at hpos
  have hw1 : w ω = max 0 (min (x ω) 1) := by simp [hw, hpos]
  have hm : 0 < max 0 (min (x ω) 1) := lt_max_of_lt_right (lt_min hxω one_pos)
  have : w ω * f ω = 0 := hω
  rw [hw1] at this
  exact (mul_pos hm hpos).ne' this

/-- Cochrane (2023), eq. (2.3), p. 22, and §16.8, p. 377 (**the Fisher equation from
optimisation**): at an optimal plan, almost surely, wherever the household holds bonds
(`B_t > 0`) the Euler gap vanishes, `Q_t/P_t = βE_t[1/P_{t+1}]`. -/
theorem eulerGap_eq_zero {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hopt : Optimal S e p)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, 0 < p.B t ω → eulerGap S e t ω = 0 := by
  have hD := eulerGap_sm hreg t
  have hBa : StronglyMeasurable[S.𝓕 t] (p.B t) := hopt.1.1.2.1 t
  have hA : MeasurableSet[S.𝓕 t] {ω | 0 < eulerGap S e t ω} :=
    measurableSet_lt measurable_const hD.measurable
  set w : Ω → ℝ := fun ω => {ω | 0 < eulerGap S e t ω}.indicator (fun _ => (1 : ℝ)) ω *
    max 0 (min (p.B t ω) 1) with hw
  have hws : StronglyMeasurable[S.𝓕 t] w := (stronglyMeasurable_const.indicator hA).mul
    ((measurable_const.max (hBa.measurable.min measurable_const)).stronglyMeasurable)
  have hw0 : ∀ ω, 0 ≤ w ω := fun ω => by
    simp only [hw, Set.indicator]
    split_ifs
    · rw [one_mul]; exact le_max_left _ _
    · simp
  have hwC : ∀ ω, |-w ω| ≤ 1 := fun ω => by
    rw [abs_neg, abs_of_nonneg (hw0 ω)]
    simp only [hw, Set.indicator]
    split_ifs
    · rw [one_mul]; exact max_le zero_le_one (min_le_right _ _)
    · simp
  have h := dev_ineq hreg hopt (b := fun ω => -w ω) (m := 0) hws.neg stronglyMeasurable_const
    (C := 1) hwC (fun ω => by simp)
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      have : w ω ≤ p.B t ω := by
        simp only [hw, Set.indicator]
        split_ifs
        · rw [one_mul]; exact max_le h.1 (min_le_left _ _)
        · simpa using h.1
      linarith)
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      simpa using h.2)
  have h' : ∫ ω, w ω * eulerGap S e t ω ∂S.μ ≤ 0 := by
    have e1 : (fun ω => -w ω * eulerGap S e t ω + (0 : Ω → ℝ) ω * moneyGap S e t ω) =
        fun ω => -(w ω * eulerGap S e t ω) := by
      funext ω; simp
    rw [e1, integral_neg] at h
    linarith
  filter_upwards [nonpos_of_weight_ineq hD hBa (eulerGap_integrable hreg t) h',
    eulerGap_nonneg hreg hopt t] with ω h1 h2 hB
  exact le_antisymm (h1 hB) h2

/-- Cochrane (2023), §19.3, p. 440, and §19.5.2, (19.33), p. 450 (**money demand from
optimisation**): at an optimal plan, almost surely, wherever the cash constraint is slack
(`M_t > P_ty_t/V_t`) the money gap vanishes, `Q^m_t/P_t = βE_t[1/P_{t+1}]`. -/
theorem moneyGap_eq_zero {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hopt : Optimal S e p)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, mmin e t ω < p.M t ω → moneyGap S e t ω = 0 := by
  have hG := moneyGap_sm hreg t
  have hx : StronglyMeasurable[S.𝓕 t] (fun ω => p.M t ω - mmin e t ω) :=
    (hopt.1.1.2.2 t).sub (mmin_sm hreg t)
  have hA : MeasurableSet[S.𝓕 t] {ω | 0 < moneyGap S e t ω} :=
    measurableSet_lt measurable_const hG.measurable
  set w : Ω → ℝ := fun ω => {ω | 0 < moneyGap S e t ω}.indicator (fun _ => (1 : ℝ)) ω *
    max 0 (min (p.M t ω - mmin e t ω) 1) with hw
  have hws : StronglyMeasurable[S.𝓕 t] w := (stronglyMeasurable_const.indicator hA).mul
    ((measurable_const.max (hx.measurable.min measurable_const)).stronglyMeasurable)
  have hw0 : ∀ ω, 0 ≤ w ω := fun ω => by
    simp only [hw, Set.indicator]
    split_ifs
    · rw [one_mul]; exact le_max_left _ _
    · simp
  have hwC : ∀ ω, |-w ω| ≤ 1 := fun ω => by
    rw [abs_neg, abs_of_nonneg (hw0 ω)]
    simp only [hw, Set.indicator]
    split_ifs
    · rw [one_mul]; exact max_le zero_le_one (min_le_right _ _)
    · simp
  have h := dev_ineq hreg hopt (b := 0) (m := fun ω => -w ω) stronglyMeasurable_const hws.neg
    (C := 1) (fun ω => by simp) hwC
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      simpa using h.1)
    (by
      filter_upwards [hopt.1.2.2.1 t] with ω h
      have : w ω ≤ p.M t ω - mmin e t ω := by
        simp only [hw, Set.indicator]
        split_ifs
        · rw [one_mul]; exact max_le (by linarith [h.2]) (min_le_left _ _)
        · simp only [zero_mul]; linarith [h.2]
      linarith)
  have h' : ∫ ω, w ω * moneyGap S e t ω ∂S.μ ≤ 0 := by
    have e1 : (fun ω => (0 : Ω → ℝ) ω * eulerGap S e t ω + -w ω * moneyGap S e t ω) =
        fun ω => -(w ω * moneyGap S e t ω) := by
      funext ω; simp
    rw [e1, integral_neg] at h
    linarith
  filter_upwards [nonpos_of_weight_ineq hG hx (moneyGap_integrable hreg t) h',
    moneyGap_nonneg hreg hopt t] with ω h1 h2 hM
  exact le_antisymm (h1 (by linarith)) h2

/-! ### Sufficiency -/

/-- Cochrane (2023), §2.1, p. 22 (tool: the bond-pricing step): for `X` known at `t` with
`X/P_{t+1}` and `R_tX/P_t` integrable, `X·(βᵗR_t/P_t − β^{t+1}E_t[1/P_{t+1}])` is integrable and
its mean is `βᵗE[R_tX/P_t] − β^{t+1}E[X/P_{t+1}]`. -/
theorem gap_split {e : Econ Ω} (hreg : EconReg S e) {t : ℕ} (R : Ω → ℝ) {X : Ω → ℝ}
    (hX : StronglyMeasurable[S.𝓕 t] X) (hXP : Integrable (fun ω => X ω / e.P (t + 1) ω) S.μ)
    (hRX : Integrable (fun ω => R ω * X ω / e.P t ω) S.μ) :
    Integrable (fun ω => X ω * (e.β ^ t * (R ω / e.P t ω) -
        e.β ^ (t + 1) * S.E t (invP e (t + 1)) ω)) S.μ ∧
      ∫ ω, X ω * (e.β ^ t * (R ω / e.P t ω) - e.β ^ (t + 1) * S.E t (invP e (t + 1)) ω) ∂S.μ =
        e.β ^ t * ∫ ω, R ω * X ω / e.P t ω ∂S.μ -
          e.β ^ (t + 1) * ∫ ω, X ω / e.P (t + 1) ω ∂S.μ := by
  have hinv1 : Integrable (invP e (t + 1)) S.μ := (hreg.2.2.2.1 (t + 1)).1
  have e0 : X * invP e (t + 1) = fun ω => X ω / e.P (t + 1) ω := by
    funext ω; simp only [Pi.mul_apply, invP, div_eq_mul_inv]
  have hfg : Integrable (X * invP e (t + 1)) S.μ := by rw [e0]; exact hXP
  have h := condExp_mul_of_stronglyMeasurable_left hX hfg hinv1
  have hXE : Integrable (fun ω => X ω * S.E t (invP e (t + 1)) ω) S.μ :=
    (S.integrable_E t _).congr h
  have hint : ∫ ω, X ω * S.E t (invP e (t + 1)) ω ∂S.μ = ∫ ω, X ω / e.P (t + 1) ω ∂S.μ := by
    have h2 : ∫ ω, X ω * S.E t (invP e (t + 1)) ω ∂S.μ =
        ∫ ω, S.E t (X * invP e (t + 1)) ω ∂S.μ := integral_congr_ae h.symm
    rw [h2, S.integral_E, e0]
  have e1 : (fun ω => X ω * (e.β ^ t * (R ω / e.P t ω) -
      e.β ^ (t + 1) * S.E t (invP e (t + 1)) ω)) = fun ω => e.β ^ t * (R ω * X ω / e.P t ω) -
        e.β ^ (t + 1) * (X ω * S.E t (invP e (t + 1)) ω) := by
    funext ω; ring
  have hi1 : Integrable (fun ω => e.β ^ t * (R ω * X ω / e.P t ω)) S.μ := hRX.const_mul _
  have hi2 : Integrable (fun ω => e.β ^ (t + 1) * (X ω * S.E t (invP e (t + 1)) ω)) S.μ :=
    hXE.const_mul _
  rw [e1]
  refine ⟨hi1.sub hi2, ?_⟩
  rw [integral_sub hi1 hi2, integral_const_mul, integral_const_mul, hint]

/-- Cochrane (2023), §19.3, p. 439 (tool): real wealth of a feasible plan is integrable. -/
theorem realWealth_integrable {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e)
    (hp : Feasible S e p) (t : ℕ) : Integrable (realWealth e p t) S.μ := by
  cases t with
  | zero => exact hreg.2.2.2.2.1
  | succ t =>
    have e1 : realWealth e p (t + 1) =
        fun ω => p.B t ω / e.P (t + 1) ω + p.M t ω / e.P (t + 1) ω := by
      funext ω; simp only [realWealth, wealth, Pi.add_apply]; ring
    rw [e1]
    exact (hp.2.2.2 t).2.1.add (hp.2.2.2 t).2.2.1

/-- Cochrane (2023), §19.3, p. 439 (tool): the endowment and taxes are integrable. -/
theorem exo_integrable {e : Econ Ω} (hreg : EconReg S e) (t : ℕ) :
    Integrable (e.y t) S.μ ∧ Integrable (e.τ t) S.μ := by
  obtain ⟨-, ⟨-, -, -, hya, -, hτa⟩, -, -, -, K, hK⟩ := hreg
  refine ⟨Integrable.of_bound (((hya t).mono (S.𝓕.le t)).aestronglyMeasurable) K ?_,
    Integrable.of_bound (((hτa t).mono (S.𝓕.le t)).aestronglyMeasurable) K ?_⟩
  · filter_upwards [hK t] with ω h
    rw [Real.norm_eq_abs]; exact h.1
  · filter_upwards [hK t] with ω h
    rw [Real.norm_eq_abs]; exact h.2.1

/-- Cochrane (2023), eqs. (19.11)–(19.12), p. 439, one period at a time (**the period identity**):
for every feasible plan,
`βᵗEc_t = βᵗE[W_t/P_t] − β^{t+1}E[W_{t+1}/P_{t+1}] + βᵗ(Ey_t − Eτ_t) − E[B_tD_t] − E[M_tG_t]`,
and the two gap terms are integrable. -/
theorem period_identity {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hp : Feasible S e p)
    (t : ℕ) :
    Integrable (fun ω => p.B t ω * eulerGap S e t ω) S.μ ∧
      Integrable (fun ω => p.M t ω * moneyGap S e t ω) S.μ ∧
      e.β ^ t * ∫ ω, p.c t ω ∂S.μ = e.β ^ t * ∫ ω, realWealth e p t ω ∂S.μ -
        e.β ^ (t + 1) * ∫ ω, realWealth e p (t + 1) ω ∂S.μ +
        e.β ^ t * (∫ ω, e.y t ω ∂S.μ - ∫ ω, e.τ t ω ∂S.μ) -
        ∫ ω, p.B t ω * eulerGap S e t ω ∂S.μ - ∫ ω, p.M t ω * moneyGap S e t ω ∂S.μ := by
  obtain ⟨hic, hiB, hiM, hiQ, hiQm⟩ := hp.2.2.2 t
  obtain ⟨hB1, hB2⟩ := gap_split hreg (e.Q t) (hp.1.2.1 t) hiB hiQ
  obtain ⟨hM1, hM2⟩ := gap_split hreg (e.Qm t) (hp.1.2.2 t) hiM hiQm
  obtain ⟨hyi, hτi⟩ := exo_integrable hreg t
  have hxi := realWealth_integrable hreg hp t
  refine ⟨hB1, hM1, ?_⟩
  have hc : p.c t =ᵐ[S.μ] fun ω => realWealth e p t ω + e.y t ω - e.τ t ω -
      e.Q t ω * p.B t ω / e.P t ω - e.Qm t ω * p.M t ω / e.P t ω := by
    filter_upwards [hp.2.1 t, hreg.2.2.1 t] with ω h hP
    simp only [realWealth]
    field_simp [hP.1.ne']
    linear_combination -h
  have hx1 : ∫ ω, realWealth e p (t + 1) ω ∂S.μ =
      ∫ ω, p.B t ω / e.P (t + 1) ω ∂S.μ + ∫ ω, p.M t ω / e.P (t + 1) ω ∂S.μ := by
    rw [← integral_add hiB hiM]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [realWealth, wealth, Pi.add_apply]; ring
  have i1 : Integrable (fun ω => realWealth e p t ω + e.y t ω) S.μ := hxi.add hyi
  have i2 : Integrable (fun ω => realWealth e p t ω + e.y t ω - e.τ t ω) S.μ := i1.sub hτi
  have i3 : Integrable (fun ω => realWealth e p t ω + e.y t ω - e.τ t ω -
      e.Q t ω * p.B t ω / e.P t ω) S.μ := i2.sub hiQ
  rw [integral_congr_ae hc, integral_sub i3 hiQm, integral_sub i2 hiQ, integral_sub i1 hτi,
    integral_add hxi hyi, hx1]
  change e.β ^ t * (_ + _ - _ - _ - _) = _
  have e2 : ∫ ω, p.B t ω * eulerGap S e t ω ∂S.μ = _ := hB2
  have e3 : ∫ ω, p.M t ω * moneyGap S e t ω ∂S.μ = _ := hM2
  rw [e2, e3, pow_succ]
  ring

/-- Cochrane (2023), §2.1, p. 22, §19.3, p. 440, and eq. (19.28), p. 449 (**sufficiency**): a
feasible admissible plan satisfying the first-order conditions — `D_t ≥ 0` with equality where
`B_t > 0`, `G_t ≥ 0` with equality where the cash constraint is slack — and the transversality
condition `βᵀE[W_T/P_T] → 0` is optimal. -/
theorem optimal_of_foc {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hp : Feasible S e p)
    (hadm : Admissible S e.β p.c) (hD0 : ∀ t, 0 ≤ᵐ[S.μ] eulerGap S e t)
    (hDB : ∀ t, ∀ᵐ ω ∂S.μ, 0 < p.B t ω → eulerGap S e t ω = 0)
    (hG0 : ∀ t, 0 ≤ᵐ[S.μ] moneyGap S e t)
    (hGM : ∀ t, ∀ᵐ ω ∂S.μ, mmin e t ω < p.M t ω → moneyGap S e t ω = 0)
    (htvc : Tendsto (fun T => e.β ^ T * ∫ ω, realWealth e p T ω ∂S.μ) atTop (𝓝 0)) :
    Optimal S e p := by
  have hβ0 : 0 ≤ e.β := hreg.1.1.le
  refine ⟨hp, hadm, fun p' hp' hadm' => ?_⟩
  set a : ℕ → ℝ := fun T => e.β ^ T * ∫ ω, realWealth e p T ω ∂S.μ with ha
  set a' : ℕ → ℝ := fun T => e.β ^ T * ∫ ω, realWealth e p' T ω ∂S.μ with ha'
  set d : ℕ → ℝ := fun t => e.β ^ t * ∫ ω, p'.c t ω ∂S.μ - e.β ^ t * ∫ ω, p.c t ω ∂S.μ
    with hd
  have hstep : ∀ t, d t ≤ (a' t - a' (t + 1)) - (a t - a (t + 1)) := fun t => by
    obtain ⟨hB1, hM1, h1⟩ := period_identity hreg hp t
    obtain ⟨hB1', hM1', h1'⟩ := period_identity hreg hp' t
    have hBD : ∫ ω, p.B t ω * eulerGap S e t ω ∂S.μ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hDB t, hp.2.2.1 t] with ω h hc
      rcases hc.1.lt_or_eq with hlt | heq
      · simp [h hlt]
      · simp [← heq]
    have hBD' : 0 ≤ ∫ ω, p'.B t ω * eulerGap S e t ω ∂S.μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hD0 t, hp'.2.2.1 t] with ω h hc
      exact mul_nonneg hc.1 h
    have hMG : ∫ ω, p.M t ω * moneyGap S e t ω ∂S.μ ≤
        ∫ ω, p'.M t ω * moneyGap S e t ω ∂S.μ := by
      refine integral_mono_ae hM1 hM1' ?_
      filter_upwards [hGM t, hG0 t, hp.2.2.1 t, hp'.2.2.1 t] with ω h hg hc hc'
      rcases hc.2.lt_or_eq with hlt | heq
      · simp [h hlt]
      · rw [← heq]
        exact mul_le_mul_of_nonneg_right hc'.2 hg
    simp only [hd, ha, ha']
    rw [h1, h1']
    linarith
  have hsum : ∀ T, ∑ t ∈ Finset.range T, d t ≤ (a' 0 - a' T) - (a 0 - a T) := fun T => by
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep T]
  have ha0 : a' 0 = a 0 := by simp [ha, ha', realWealth, wealth]
  have hpos : ∀ T, 0 ≤ a' (T + 1) := fun T => by
    refine mul_nonneg (pow_nonneg hβ0 _) (integral_nonneg_of_ae ?_)
    filter_upwards [hp'.2.2.1 T, hreg.2.2.1 T, hreg.2.2.1 (T + 1)] with ω hc hT hT1
    simp only [realWealth, wealth, Pi.add_apply]
    have hmm : 0 < mmin e T ω := div_pos (mul_pos hT.1 hT.2.2) hT.2.1
    exact div_nonneg (by linarith [hc.1, hc.2]) hT1.1.le
  have hds : HasSum d (expU S e.β p'.c - expU S e.β p.c) :=
    (summable_of_admissible S hβ0 hadm').hasSum.sub (summable_of_admissible S hβ0 hadm).hasSum
  have hle : expU S e.β p'.c - expU S e.β p.c ≤ 0 := by
    refine le_of_tendsto_of_tendsto hds.tendsto_sum_nat htvc ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    linarith [hsum (k + 1), hpos k]
  linarith

/-! ### The transversality condition is necessary -/

omit mΩ in
/-- Cochrane (2023), §19.5.1, p. 449: wealth under liquidation is the plan's wealth up to `T`
and minimal money afterwards. -/
theorem wealth_liq (e : Econ Ω) (p : Plan Ω) (T s : ℕ) :
    wealth e.W0 (liq e p T).B (liq e p T).M s =
      if s ≤ T then wealth e.W0 p.B p.M s else mmin e (s - 1) := by
  cases s with
  | zero => simp [wealth]
  | succ s =>
    simp only [wealth, liq, Nat.add_sub_cancel]
    by_cases h : s < T
    · simp [h, show s + 1 ≤ T by omega]
    · simp [h, show ¬ s + 1 ≤ T by omega]

/-- Cochrane (2023), §19.5.1, p. 449 (tool): bounded known variables are integrable. -/
theorem integrable_of_bdd {t : ℕ} {f : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 t] f) {K : ℝ}
    (hK : ∀ᵐ ω ∂S.μ, |f ω| ≤ K) : Integrable f S.μ :=
  Integrable.of_bound ((hf.mono (S.𝓕.le t)).aestronglyMeasurable) K
    (hK.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), §19.5.1, p. 449 (tool): `E|f| ≤ K` when `|f| ≤ K` almost surely. -/
theorem integral_abs_le_of_bdd {f : Ω → ℝ} {K : ℝ} (hK : ∀ᵐ ω ∂S.μ, |f ω| ≤ K) :
    ∫ ω, |f ω| ∂S.μ ≤ K := by
  have h := norm_integral_le_of_norm_le_const (μ := S.μ) (f := fun ω => |f ω|) (C := K)
    (hK.mono fun ω h => by rwa [Real.norm_eq_abs, abs_abs])
  rw [probReal_univ, mul_one] at h
  exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h)

/-- Cochrane (2023), §19.5.1, p. 449: the bounds on the liquidation plan's ingredients —
`|Q^m_ty_t/V_t|`, `|P_ty_t/(V_tP_{t+1})|` and `|cref_j| ≤ 4K` — and their measurability and
integrability. -/
theorem liq_parts {e : Econ Ω} (hreg : EconReg S e) :
    ∃ K, 0 ≤ K ∧ (∀ t, Integrable (fun ω => e.Qm t ω * e.y t ω / e.V t ω) S.μ) ∧
      (∀ t, Integrable (fun ω => mmin e t ω / e.P (t + 1) ω) S.μ) ∧
      (∀ t, ∀ᵐ ω ∂S.μ, |mmin e t ω / e.P (t + 1) ω| ≤ K) ∧
      (∀ j, StronglyMeasurable[S.𝓕 (j + 1)] (cref e j)) ∧
      (∀ j, ∀ᵐ ω ∂S.μ, |cref e j ω| ≤ 4 * K) := by
  obtain ⟨-, ⟨hPa, -, hQma, hya, hVa, hτa⟩, -, -, -, K, hK⟩ := hreg
  have hK0 : 0 ≤ K := by
    obtain ⟨ω, hω⟩ := (hK 0).exists
    exact (abs_nonneg _).trans hω.1
  have hmm : ∀ t, StronglyMeasurable[S.𝓕 t] (mmin e t) := fun t =>
    sm_div ((hPa t).mul (hya t)) (hVa t)
  have hqy : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => e.Qm t ω * e.y t ω / e.V t ω) :=
    fun t => sm_div ((hQma t).mul (hya t)) (hVa t)
  have hmP : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (fun ω => mmin e t ω / e.P (t + 1) ω) :=
    fun t => sm_div ((hmm t).mono (S.𝓕.mono (Nat.le_succ t))) (hPa (t + 1))
  refine ⟨K, hK0, fun t => integrable_of_bdd (hqy t) ((hK t).mono fun ω h => h.2.2.1),
    fun t => integrable_of_bdd (hmP t) ((hK t).mono fun ω h => h.2.2.2),
    fun t => (hK t).mono fun ω h => h.2.2.2, fun j => ?_, fun j => ?_⟩
  · exact (((hmP j).add (hya (j + 1))).sub (hτa (j + 1))).sub (hqy (j + 1))
  · filter_upwards [hK j, hK (j + 1)] with ω h0 h1
    simp only [cref]
    have := abs_sub (mmin e j ω / e.P (j + 1) ω + e.y (j + 1) ω - e.τ (j + 1) ω)
      (e.Qm (j + 1) ω * e.y (j + 1) ω / e.V (j + 1) ω)
    have := abs_sub (mmin e j ω / e.P (j + 1) ω + e.y (j + 1) ω) (e.τ (j + 1) ω)
    have := abs_add_le (mmin e j ω / e.P (j + 1) ω) (e.y (j + 1) ω)
    linarith [h0.2.2.2, h1.1, h1.2.1, h1.2.2.1]

/-- Cochrane (2023), §19.5.1, p. 449: the liquidation plan is feasible. -/
theorem feasible_liq {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hp : Feasible S e p)
    (T : ℕ) : Feasible S e (liq e p T) := by
  obtain ⟨K, -, hqyi, hmPi, -, hcrefm, hcrefb⟩ := liq_parts hreg
  have hreg' := hreg
  obtain ⟨-, ⟨hPa, hQa, hQma, hya, hVa, -⟩, hpos, -, -, -⟩ := hreg'
  obtain ⟨⟨hca, hBa, hMa⟩, hflow, hcon, hI⟩ := hp
  have hcref_i : ∀ j, Integrable (cref e j) S.μ := fun j => integrable_of_bdd (hcrefm j)
    (hcrefb j)
  have hqmm : ∀ t, Integrable (fun ω => e.Qm t ω * mmin e t ω / e.P t ω) S.μ := fun t => by
    refine (hqyi t).congr ?_
    filter_upwards [hpos t] with ω h
    simp only [mmin]
    field_simp [h.1.ne']
  refine ⟨⟨fun s => ?_, fun s => ?_, fun s => ?_⟩, fun s => ?_, fun s => ?_, fun s => ?_⟩
  · simp only [liq]
    split_ifs with h1 h2
    · exact hca s
    · subst h2
      exact (hca s).add ((((sm_div ((hQa s).mul (hBa s)) (hPa s)).add
        (sm_div ((hQma s).mul (hMa s)) (hPa s))).sub (sm_div ((hQma s).mul (hya s)) (hVa s))))
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      simpa using hcrefm j
  · simp only [liq]
    split_ifs
    · exact hBa s
    · exact stronglyMeasurable_const
  · simp only [liq]
    split_ifs
    · exact hMa s
    · exact mmin_sm hreg s
  · filter_upwards [hflow s, hpos s] with ω h hP
    rw [wealth_liq]
    simp only [liq]
    by_cases h1 : s < T
    · simp only [show s ≤ T by omega, h1, ↓reduceIte]
      exact h
    · by_cases h2 : s = T
      · subst h2
        simp only [le_refl, lt_irrefl, ↓reduceIte, liqValue, mmin, Pi.add_apply, Pi.zero_apply]
        field_simp [hP.1.ne', hP.2.1.ne']
        linear_combination (e.V s ω) * h
      · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
        simp only [show ¬ j + 1 ≤ T by omega, h1, h2, ↓reduceIte, Nat.add_sub_cancel, cref,
          mmin, Pi.zero_apply]
        field_simp [hP.1.ne', hP.2.1.ne']
        ring
  · filter_upwards [hcon s] with ω h
    simp only [liq]
    split_ifs
    · exact h
    · exact ⟨le_refl 0, le_refl _⟩
  · obtain ⟨hic, hiB, hiM, hiQ, hiQm⟩ := hI s
    simp only [liq]
    by_cases h1 : s < T
    · simp only [h1, ↓reduceIte]
      exact ⟨hic, hiB, hiM, hiQ, hiQm⟩
    · simp only [h1, ↓reduceIte, Pi.zero_apply, zero_div, mul_zero]
      refine ⟨?_, integrable_zero _ _ _, hmPi s, integrable_zero _ _ _, hqmm s⟩
      by_cases h2 : s = T
      · subst h2
        simp only [↓reduceIte]
        exact hic.add ((hiQ.add hiQm).sub (hqyi s))
      · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
        simp only [h2, ↓reduceIte, Nat.add_sub_cancel]
        exact hcref_i j

/-- Cochrane (2023), §19.5.1, p. 449: the liquidation plan is admissible. -/
theorem admissible_liq {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hp : Feasible S e p)
    (hadm : Admissible S e.β p.c) (T : ℕ) : Admissible S e.β (liq e p T).c := by
  have hβ0 : 0 ≤ e.β := hreg.1.1.le
  obtain ⟨K, hK0, -, -, -, -, hcrefb⟩ := liq_parts hreg
  set X : ℝ := e.β ^ T * ∫ ω, |liqValue e p T ω| ∂S.μ
  have hsum : Summable fun s => e.β ^ s * ∫ ω, |p.c s ω| ∂S.μ +
      (if s = T then X else 0) + e.β ^ s * (4 * K) :=
    (hadm.add (summable_of_ne_finset_zero (s := {T}) fun s hs => by
      simp only [Finset.mem_singleton] at hs; simp [hs])).add
      ((summable_geometric_of_lt_one hβ0 hreg.1.2).mul_right _)
  refine Summable.of_nonneg_of_le (fun s => mul_nonneg (pow_nonneg hβ0 s)
    (integral_nonneg fun ω => abs_nonneg _)) (fun s => ?_) hsum
  have hX0 : 0 ≤ X := mul_nonneg (pow_nonneg hβ0 T) (integral_nonneg fun ω => abs_nonneg _)
  have hc0 : 0 ≤ e.β ^ s * ∫ ω, |p.c s ω| ∂S.μ :=
    mul_nonneg (pow_nonneg hβ0 s) (integral_nonneg fun ω => abs_nonneg _)
  have hK4 : 0 ≤ e.β ^ s * (4 * K) := mul_nonneg (pow_nonneg hβ0 s) (by linarith)
  simp only [liq]
  by_cases h1 : s < T
  · simp only [h1, ↓reduceIte, show ¬ s = T by omega]
    linarith
  · by_cases h2 : s = T
    · subst h2
      simp only [lt_irrefl, ↓reduceIte]
      obtain ⟨hic, -, -, hiQ, hiQm⟩ := hp.2.2.2 s
      obtain ⟨K', -, hqyi, -⟩ := liq_parts hreg
      have hli : Integrable (liqValue e p s) S.μ := (hiQ.add hiQm).sub (hqyi s)
      have : ∫ ω, |(p.c s + liqValue e p s) ω| ∂S.μ ≤
          ∫ ω, |p.c s ω| ∂S.μ + ∫ ω, |liqValue e p s ω| ∂S.μ := by
        rw [← integral_add hic.abs hli.abs]
        exact integral_mono (hic.add hli).abs (hic.abs.add hli.abs) fun ω => abs_add_le _ _
      have := mul_le_mul_of_nonneg_left this (pow_nonneg hβ0 s)
      simp only [X, mul_add] at this ⊢
      linarith
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel, add_zero]
      have := mul_le_mul_of_nonneg_left (integral_abs_le_of_bdd (hcrefb j))
        (pow_nonneg hβ0 (j + 1))
      linarith

/-- Cochrane (2023), eq. (19.28), p. 449 ("their optimal choices include transversality
conditions"; **necessity of the transversality condition**): at an optimal plan,
`βᵀE[W_T/P_T] → 0`. Liquidating bonds and excess money at `T` and holding the least money from
then on cannot raise expected utility, so the liquidation value `βᵀE[Q_TB_T/P_T + …]` is bounded
by a tail of a convergent series; by the first-order inequalities it bounds `β^{T+1}E[W_{T+1}/
P_{T+1}]` up to `β^{T+1}K`. -/
theorem tvc_of_optimal {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e) (hopt : Optimal S e p) :
    Tendsto (fun T => e.β ^ T * ∫ ω, realWealth e p T ω ∂S.μ) atTop (𝓝 0) := by
  have hβ0 : 0 ≤ e.β := hreg.1.1.le
  have hβ1 : e.β < 1 := hreg.1.2
  obtain ⟨K, hK0, hqyi, hmPi, hmPb, hcrefm, hcrefb⟩ := liq_parts hreg
  have hcrefi : ∀ j, Integrable (cref e j) S.μ := fun j => integrable_of_bdd (hcrefm j)
    (hcrefb j)
  have hp := hopt.1
  set h : ℕ → ℝ := fun j => e.β ^ (j + 1) * (∫ ω, p.c (j + 1) ω ∂S.μ - ∫ ω, cref e j ω ∂S.μ)
    with hh
  have hcs := summable_of_admissible S hβ0 hopt.2.1
  have hcrs : Summable fun j => e.β ^ (j + 1) * ∫ ω, cref e j ω ∂S.μ := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right
      (e.β * (4 * K))) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 _), pow_succ]
    have h1 := (abs_integral_le_integral_abs (f := cref e j) (μ := S.μ)).trans
      (integral_abs_le_of_bdd (hcrefb j))
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (pow_nonneg hβ0 j) hβ0)
    linarith
  have hhs : Summable h := by
    have := ((summable_nat_add_iff 1).2 hcs).sub hcrs
    refine this.congr fun j => ?_
    simp only [hh]
    ring
  have hR := tendsto_sum_nat_add h
  -- the liquidation inequality
  have hliq : ∀ T, e.β ^ T * ∫ ω, liqValue e p T ω ∂S.μ ≤ ∑' i, h (i + T) := fun T => by
    have hfe := feasible_liq hreg hp T
    have hle := hopt.2.2 _ hfe (admissible_liq hreg hp hopt.2.1 T)
    set f : ℕ → ℝ := fun s => e.β ^ s * ∫ ω, (liq e p T).c s ω ∂S.μ -
      e.β ^ s * ∫ ω, p.c s ω ∂S.μ with hf
    have hfs : HasSum f (expU S e.β (liq e p T).c - expU S e.β p.c) :=
      (summable_of_admissible S hβ0 (admissible_liq hreg hp hopt.2.1 T)).hasSum.sub hcs.hasSum
    have hsplit := hfs.summable.sum_add_tsum_nat_add (T + 1)
    rw [hfs.tsum_eq] at hsplit
    have hhead : ∑ i ∈ Finset.range (T + 1), f i = e.β ^ T * ∫ ω, liqValue e p T ω ∂S.μ := by
      rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => ?_]
      · simp only [hf, liq, lt_irrefl, ↓reduceIte, zero_add]
        have hli : Integrable (liqValue e p T) S.μ :=
          ((hp.2.2.2 T).2.2.2.1.add (hp.2.2.2 T).2.2.2.2).sub (hqyi T)
        rw [show (∫ ω, (p.c T + liqValue e p T) ω ∂S.μ) = _ from
          integral_add (hp.2.2.2 T).1 hli]
        ring
      · have hi' : i < T := Finset.mem_range.1 hi
        simp [hf, liq, hi']
    have htail : ∑' i, f (i + (T + 1)) = -∑' i, h (i + T) := by
      rw [← tsum_neg]
      refine tsum_congr fun i => ?_
      simp only [hf, hh, liq, show ¬ i + (T + 1) < T by omega,
        show ¬ i + (T + 1) = T by omega, ↓reduceIte, show i + (T + 1) - 1 = i + T by omega,
        show i + T + 1 = i + (T + 1) by omega]
      ring
    rw [hhead, htail] at hsplit
    linarith
  -- the bound on next period's real wealth
  have hbound : ∀ T, e.β ^ (T + 1) * ∫ ω, realWealth e p (T + 1) ω ∂S.μ ≤
      e.β ^ T * ∫ ω, liqValue e p T ω ∂S.μ + e.β ^ (T + 1) * K := fun T => by
    obtain ⟨hic, hiB, hiM, hiQ, hiQm⟩ := hp.2.2.2 T
    have hpos := hreg.2.2.1 T
    have hqmm : Integrable (fun ω => e.Qm T ω * mmin e T ω / e.P T ω) S.μ := by
      refine (hqyi T).congr ?_
      filter_upwards [hpos] with ω h
      simp only [mmin]
      field_simp [h.1.ne']
    have hqmm_eq : ∫ ω, e.Qm T ω * mmin e T ω / e.P T ω ∂S.μ =
        ∫ ω, e.Qm T ω * e.y T ω / e.V T ω ∂S.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hpos] with ω h
      simp only [mmin]
      field_simp [h.1.ne']
    obtain ⟨hB1, hB2⟩ := gap_split hreg (e.Q T) (hp.1.2.1 T) hiB hiQ
    have hXm : StronglyMeasurable[S.𝓕 T] (fun ω => p.M T ω - mmin e T ω) :=
      (hp.1.2.2 T).sub (mmin_sm hreg T)
    have hXP : Integrable (fun ω => (p.M T ω - mmin e T ω) / e.P (T + 1) ω) S.μ := by
      have e1 : (fun ω => (p.M T ω - mmin e T ω) / e.P (T + 1) ω) =
          fun ω => p.M T ω / e.P (T + 1) ω - mmin e T ω / e.P (T + 1) ω := by
        funext ω; ring
      rw [e1]; exact hiM.sub (hmPi T)
    have hRX : Integrable (fun ω => e.Qm T ω * (p.M T ω - mmin e T ω) / e.P T ω) S.μ := by
      have e1 : (fun ω => e.Qm T ω * (p.M T ω - mmin e T ω) / e.P T ω) =
          fun ω => e.Qm T ω * p.M T ω / e.P T ω - e.Qm T ω * mmin e T ω / e.P T ω := by
        funext ω; ring
      rw [e1]; exact hiQm.sub hqmm
    obtain ⟨hM1, hM2⟩ := gap_split hreg (e.Qm T) hXm hXP hRX
    have hBD : 0 ≤ ∫ ω, p.B T ω * eulerGap S e T ω ∂S.μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [eulerGap_nonneg hreg hopt T, hp.2.2.1 T] with ω h hc
      exact mul_nonneg hc.1 h
    have hMG : 0 ≤ ∫ ω, (p.M T ω - mmin e T ω) * moneyGap S e T ω ∂S.μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [moneyGap_nonneg hreg hopt T, hp.2.2.1 T] with ω h hc
      exact mul_nonneg (by linarith [hc.2]) h
    have e2 : ∫ ω, p.B T ω * eulerGap S e T ω ∂S.μ = _ := hB2
    have e3 : ∫ ω, (p.M T ω - mmin e T ω) * moneyGap S e T ω ∂S.μ = _ := hM2
    have e4 : ∫ ω, e.Qm T ω * (p.M T ω - mmin e T ω) / e.P T ω ∂S.μ =
        ∫ ω, e.Qm T ω * p.M T ω / e.P T ω ∂S.μ - ∫ ω, e.Qm T ω * e.y T ω / e.V T ω ∂S.μ := by
      rw [← hqmm_eq, ← integral_sub hiQm hqmm]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only; ring
    have e5 : ∫ ω, (p.M T ω - mmin e T ω) / e.P (T + 1) ω ∂S.μ =
        ∫ ω, p.M T ω / e.P (T + 1) ω ∂S.μ - ∫ ω, mmin e T ω / e.P (T + 1) ω ∂S.μ := by
      rw [← integral_sub hiM (hmPi T)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only; ring
    have e6 : ∫ ω, liqValue e p T ω ∂S.μ = ∫ ω, e.Q T ω * p.B T ω / e.P T ω ∂S.μ +
        ∫ ω, e.Qm T ω * p.M T ω / e.P T ω ∂S.μ - ∫ ω, e.Qm T ω * e.y T ω / e.V T ω ∂S.μ := by
      have h1 := integral_sub (hiQ.add hiQm) (hqyi T)
      have h2 := integral_add hiQ hiQm
      simp only [Pi.add_apply] at h1
      rw [← h2]
      exact h1
    have e7 : ∫ ω, realWealth e p (T + 1) ω ∂S.μ =
        ∫ ω, p.B T ω / e.P (T + 1) ω ∂S.μ + ∫ ω, p.M T ω / e.P (T + 1) ω ∂S.μ := by
      rw [← integral_add hiB hiM]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [realWealth, wealth, Pi.add_apply]; ring
    have hmK : ∫ ω, mmin e T ω / e.P (T + 1) ω ∂S.μ ≤ K :=
      (le_abs_self _).trans ((abs_integral_le_integral_abs).trans
        (integral_abs_le_of_bdd (hmPb T)))
    have hmK' := mul_le_mul_of_nonneg_left hmK (pow_nonneg hβ0 (T + 1))
    rw [e7, e6]
    rw [e4, e5] at e3
    nlinarith
  have hlow : ∀ T, 0 ≤ e.β ^ (T + 1) * ∫ ω, realWealth e p (T + 1) ω ∂S.μ := fun T => by
    refine mul_nonneg (pow_nonneg hβ0 _) (integral_nonneg_of_ae ?_)
    filter_upwards [hp.2.2.1 T, hreg.2.2.1 T, hreg.2.2.1 (T + 1)] with ω hc hT hT1
    simp only [realWealth, wealth, Pi.add_apply]
    have hmm : 0 < mmin e T ω := div_pos (mul_pos hT.1 hT.2.2) hT.2.1
    exact div_nonneg (by linarith [hc.1, hc.2]) hT1.1.le
  have hup : Tendsto (fun T => ∑' i, h (i + T) + e.β ^ (T + 1) * K) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => e.β ^ (T + 1) * K) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).comp
        (tendsto_add_atTop_nat 1)).mul_const K
      simpa using this
    simpa using hR.add h1
  have hshift : Tendsto (fun T => e.β ^ (T + 1) * ∫ ω, realWealth e p (T + 1) ω ∂S.μ) atTop
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hlow fun T =>
      (hbound T).trans (by linarith [hliq T])
  exact (tendsto_add_atTop_iff_nat 1).1 hshift

/-- Cochrane (2023), §2.1, p. 22, §19.3, p. 440, and eq. (19.28), p. 449 (**the household problem
solved**): when the household holds bonds at every date (`B_t > 0` almost surely), a feasible
admissible plan is optimal **iff** the bond first-order condition holds with equality
(`D_t = 0`), money is never dominated (`G_t ≥ 0`), the marginal unit of money earns the bond
return where the cash constraint is slack (`G_t = 0` there), and the transversality condition
holds. -/
theorem optimal_iff_foc {e : Econ Ω} {p : Plan Ω} (hreg : EconReg S e)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < p.B t ω) :
    Optimal S e p ↔ Feasible S e p ∧ Admissible S e.β p.c ∧
      (∀ t, eulerGap S e t =ᵐ[S.μ] 0) ∧ (∀ t, 0 ≤ᵐ[S.μ] moneyGap S e t) ∧
      (∀ t, ∀ᵐ ω ∂S.μ, mmin e t ω < p.M t ω → moneyGap S e t ω = 0) ∧
      Tendsto (fun T => e.β ^ T * ∫ ω, realWealth e p T ω ∂S.μ) atTop (𝓝 0) := by
  constructor
  · intro hopt
    refine ⟨hopt.1, hopt.2.1, fun t => ?_, moneyGap_nonneg hreg hopt,
      moneyGap_eq_zero hreg hopt, tvc_of_optimal hreg hopt⟩
    filter_upwards [eulerGap_eq_zero hreg hopt t, hBpos t] with ω h hB
    exact h hB
  · rintro ⟨hp, hadm, hD, hG0, hGM, htvc⟩
    refine optimal_of_foc hreg hp hadm (fun t => (hD t).symm.le) (fun t => ?_) hG0 hGM htvc
    filter_upwards [hD t] with ω h _
    exact h

end Cochrane.ObservationalEquivalence.TidyR6MoneyHousehold
