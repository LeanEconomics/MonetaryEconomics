/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR5MoneyUncertainty
import ObservationalEquivalence.ExpectationsMeasureIID

/-!
# Money-supply regimes on a probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, pp. 495–496
(`M_t V_t = P_t y_t` and `(B_{t−1} + M_{t−1})/P_t = E_t ∑_{j ≥ 0} βʲ s_{t+j}`), and §22.7, p. 508.

`TidyR5MoneyUncertainty` states the model for an abstract `ExpectationSystem`. Here it lives on a
genuine probability space with any filtration (`MeasExpectationSystem`, Mathlib's `condExp`):
every equation holds almost surely, processes are adapted (`StronglyAdapted`) and bounded means
essentially bounded. `W_t = B_{t−1} + M_{t−1}`; the present value is the forward solution
`E_t ∑ βʲ s_{t+j}` (`ExpectationsMeasure.MeasExpectationSystem.forwardSol`), for `0 ≤ β < 1` and
bounded adapted surpluses.

## Main results

* `pvM_succ`, `pvM_hasSum`: `PV_t = s_t + β E_t PV_{t+1}` and `PV_t = ∑ βʲ E_t s_{t+j}` a.s.
* `flow_of_valuation`, `flow_bond_price`: `W_t = P_t s_t + Q_t W_{t+1}` a.s. with
  `Q_t = β P_t E_t[1/P_{t+1}]` when `W_{t+1}` is chosen at `t`.
* Active money: `activeMoney_price`, `activeMoney_exists`. Active fiscal: `activeFiscal_unique`,
  `activeFiscal_exists`, `activeFiscal_adapted`. OE-2: `oe2`.
* `unexpected_price_level`: the surprise in `1/P_{t+1}` equals the fiscal news
  `(PV_{t+1} − E_t PV_{t+1})/W_{t+1}` and the money news, a.s.
* `inconsistent_iff`, `halve_money_no_eqm`: §22.7 on a probability space.
* `coin_random_eqmM`: in the i.i.d. coin economy, an equilibrium whose date-1 price level is not
  a.s. equal to its date-0 forecast.
-/

namespace Cochrane.ObservationalEquivalence.TidyR5MoneyMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ObservationalEquivalence.ExpectationsMeasure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), §22.1, p. 496, on a probability space: the present value
`E_t ∑_{j ≥ 0} βʲ s_{t+j}` (Mathlib `condExp` of the realised discounted sum). -/
noncomputable def pvM (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := S.forwardSol β s t

/-- Cochrane (2023), §22.1, pp. 495–496, on a probability space: an equilibrium — a.s. a positive
price level, the quantity equation `M_t V_t = P_t y_t` and the valuation equation
`W_t / P_t = E_t ∑ βʲ s_{t+j}`, at every date. -/
def EqmM (β : ℝ) (V y P M W s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (∀ᵐ ω ∂S.μ, 0 < P t ω) ∧ M t * V t =ᵐ[S.μ] P t * y t ∧ W t / P t =ᵐ[S.μ] pvM S β s t

variable {S}

/-- Cochrane (2023), §22.1, p. 496: `PV_t = s_t + β E_t PV_{t+1}` a.s. (adapted, essentially
bounded surpluses, `|β| < 1`). -/
theorem pvM_succ {β K : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} (hsa : StronglyAdapted S.𝓕 s)
    (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ K) (t : ℕ) :
    pvM S β s t =ᵐ[S.μ] s t + β • S.E t (pvM S β s (t + 1)) := by
  filter_upwards [S.forwardSol_solves hβ hsa hsb t] with ω h
  rw [pvM, h, Pi.add_apply, Pi.add_apply, add_comm]
  rfl

/-- Cochrane (2023), §22.1, p. 496: `PV_t = ∑_j βʲ E_t s_{t+j}` a.s., a convergent series. -/
theorem pvM_hasSum {β K : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} (hsa : StronglyAdapted S.𝓕 s)
    (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t (s (t + j)) ω) (pvM S β s t ω) :=
  S.forwardSol_hasSum hβ (fun t => ((hsa t).mono (S.𝓕.le t)).aestronglyMeasurable) hsb t

/-- Cochrane (2023), §22.1, p. 496 (the valuation equation implies the flow constraint, a.s.):
`W_t = P_t s_t + β P_t E_t[W_{t+1}/P_{t+1}]`. -/
theorem flow_of_valuation {β K : ℝ} (hβ : |β| < 1) {V y P M W s : ℕ → Ω → ℝ}
    (hsa : StronglyAdapted S.𝓕 s) (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ K)
    (h : EqmM S β V y P M W s) (t : ℕ) :
    W t =ᵐ[S.μ] P t * s t + β • (P t * S.E t (W (t + 1) / P (t + 1))) := by
  filter_upwards [(h t).1, (h t).2.2, pvM_succ hβ hsa hsb t, S.E_congr (h (t + 1)).2.2 t]
    with ω hP hv hs hE
  simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at hv hs ⊢
  rw [hE]
  rw [hs] at hv
  field_simp at hv
  linear_combination hv

/-- Cochrane (2023), §22.1, p. 496 (the flow constraint with the bond price, a.s.): if `W_{t+1}`
is chosen at `t` and `1/P_{t+1}` is integrable, `W_t = P_t s_t + Q_t W_{t+1}` with
`Q_t = β P_t E_t[1/P_{t+1}]`. -/
theorem flow_bond_price {β K : ℝ} (hβ : |β| < 1) {V y P M W s : ℕ → Ω → ℝ}
    (hsa : StronglyAdapted S.𝓕 s) (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ K)
    (h : EqmM S β V y P M W s) (t : ℕ) (hW : StronglyMeasurable[S.𝓕 t] (W (t + 1)))
    (hPi : Integrable (fun ω => 1 / P (t + 1) ω) S.μ) :
    W t =ᵐ[S.μ] P t * s t + (β • (P t * S.E t (fun ω => 1 / P (t + 1) ω))) * W (t + 1) := by
  have e : W (t + 1) / P (t + 1) = W (t + 1) * fun ω => 1 / P (t + 1) ω := by
    funext ω; simp [div_eq_mul_inv]
  have hint : Integrable (W (t + 1) * fun ω => 1 / P (t + 1) ω) S.μ := by
    rw [← e]
    exact (S.integrable_E (t + 1) _).congr (h (t + 1)).2.2.symm
  filter_upwards [flow_of_valuation hβ hsa hsb h t,
    condExp_mul_of_stronglyMeasurable_left hW hint hPi] with ω h1 h2
  rw [h1, e]
  have h2' : S.E t (W (t + 1) * fun ω => 1 / P (t + 1) ω) ω =
      W (t + 1) ω * S.E t (fun ω => 1 / P (t + 1) ω) ω := h2
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [h2']
  ring

/-! ### Active money -/

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496 (active money, a.s.): `P_t = M_t V_t / y_t`. -/
theorem activeMoney_price {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {V y P M : ℕ → Ω → ℝ}
    (hy : ∀ t, ∀ᵐ ω ∂μ, 0 < y t ω) (h : ∀ t, M t * V t =ᵐ[μ] P t * y t) (t : ℕ) :
    P t =ᵐ[μ] M t * V t / y t := by
  filter_upwards [hy t, h t] with ω h1 h2
  simp only [Pi.mul_apply, Pi.div_apply] at h2 ⊢
  rw [h2, mul_div_cancel_right₀ _ h1.ne']

/-- Cochrane (2023), §22.1, p. 496 ("surpluses `s` follow", a.s.): for a positive money supply and
nominal liabilities whose real value `x_t = W_t y_t/(M_t V_t)` is adapted and essentially
bounded, the passive surpluses `s_t = x_t − β E_t x_{t+1}` complete an equilibrium with
`P = MV/y`. -/
theorem activeMoney_exists {β X : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V y M W : ℕ → Ω → ℝ}
    (hV : ∀ t, ∀ᵐ ω ∂S.μ, 0 < V t ω) (hy : ∀ t, ∀ᵐ ω ∂S.μ, 0 < y t ω)
    (hM : ∀ t, ∀ᵐ ω ∂S.μ, 0 < M t ω)
    (hxa : StronglyAdapted S.𝓕 fun t => W t / (M t * V t / y t))
    (hX : ∀ t, ∀ᵐ ω ∂S.μ, |(W t / (M t * V t / y t)) ω| ≤ X) :
    EqmM S β V y (fun t => M t * V t / y t) M W
      (fun t => W t / (M t * V t / y t) -
        β • S.E t (W (t + 1) / (M (t + 1) * V (t + 1) / y (t + 1)))) := by
  set x : ℕ → Ω → ℝ := fun t => W t / (M t * V t / y t) with hx
  set s : ℕ → Ω → ℝ := fun t => x t - β • S.E t (x (t + 1)) with hs
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have hsa : StronglyAdapted S.𝓕 s := fun t =>
    (hxa t).sub ((S.stronglyMeasurable_E t _).const_smul β)
  have hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ X + β * X := fun t => by
    filter_upwards [hX t, S.abs_E_le (hX (t + 1)) t] with ω h1 h2
    simp only [hs, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add h1 ?_)
    rw [abs_mul, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left h2 hβ0
  have hxs : S.Solves β s x := fun t =>
    Eventually.of_forall fun ω => by simp [hs]
  have hxm : ∀ t, AEStronglyMeasurable (x t) S.μ := fun t =>
    ((hxa t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hval := S.forward_unique hβ hxs (S.forwardSol_solves hβ hsa hsb) hxm
    (fun t => ((S.forwardSol_adapted β s t).mono (S.𝓕.le t)).aestronglyMeasurable) ⟨X, hX⟩
    (S.forwardSol_bdd hβ hsb)
  intro t
  refine ⟨?_, ?_, hval t⟩
  · filter_upwards [hV t, hy t, hM t] with ω h1 h2 h3
    exact div_pos (mul_pos h3 h1) h2
  · filter_upwards [hy t] with ω h1
    simp only [Pi.mul_apply, Pi.div_apply]
    field_simp [h1.ne']

/-! ### Active fiscal -/

omit mΩ in
/-- Cochrane (2023), §22.1, p. 496 (active fiscal, uniqueness, a.s.): given surpluses and nominal
liabilities with `W_t ≠ 0` a.s., the price level and money are unique (a.s., at every date). -/
theorem activeFiscal_unique {mΩ : MeasurableSpace Ω} {S : MeasExpectationSystem Ω} {β : ℝ}
    {V y P M P' M' W s : ℕ → Ω → ℝ} (hV : ∀ t, ∀ᵐ ω ∂S.μ, 0 < V t ω)
    (hW : ∀ t, ∀ᵐ ω ∂S.μ, W t ω ≠ 0) (h : EqmM S β V y P M W s) (h' : EqmM S β V y P' M' W s) :
    (∀ t, P t =ᵐ[S.μ] P' t) ∧ ∀ t, M t =ᵐ[S.μ] M' t := by
  have hP : ∀ t, P t =ᵐ[S.μ] P' t := fun t => by
    filter_upwards [(h t).1, (h' t).1, (h t).2.2, (h' t).2.2, hW t] with ω h1 h2 h3 h4 h5
    simp only [Pi.div_apply] at h3 h4
    have e := h3.trans h4.symm
    rw [div_eq_div_iff h1.ne' h2.ne'] at e
    exact (mul_left_cancel₀ h5 e).symm
  refine ⟨hP, fun t => ?_⟩
  filter_upwards [hP t, (h t).2.1, (h' t).2.1, hV t] with ω e0 e1 e2 hv
  simp only [Pi.mul_apply] at e1 e2
  rw [e0] at e1
  exact mul_right_cancel₀ hv.ne' (e1.trans e2.symm)

/-- Cochrane (2023), §22.1, p. 496 (active fiscal, existence, a.s.): if `W_t` and `E_t PV_t` are
a.s. positive, `P_t = W_t / E_t PV_t` and `M_t = P_t y_t / V_t` form an equilibrium. -/
theorem activeFiscal_exists {β : ℝ} {V y W s : ℕ → Ω → ℝ} (hV : ∀ t, ∀ᵐ ω ∂S.μ, 0 < V t ω)
    (hW : ∀ t, ∀ᵐ ω ∂S.μ, 0 < W t ω) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < pvM S β s t ω) :
    EqmM S β V y (fun t => W t / pvM S β s t) (fun t => W t / pvM S β s t * y t / V t) W s := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hW t, hpv t] with ω h1 h2
    exact div_pos h1 h2
  · filter_upwards [hV t] with ω h1
    simp only [Pi.mul_apply, Pi.div_apply]
    field_simp [h1.ne']
  · filter_upwards [hW t, hpv t] with ω h1 h2
    simp only [Pi.div_apply]
    field_simp [h1.ne', h2.ne']

/-- Cochrane (2023), §22.1, p. 496 (active fiscal: the price level is known at `t`): with adapted
nominal liabilities, `P_t = W_t / E_t PV_t` is adapted. -/
theorem activeFiscal_adapted {β : ℝ} {W s : ℕ → Ω → ℝ} (hWa : StronglyAdapted S.𝓕 W) :
    StronglyAdapted S.𝓕 fun t => W t / pvM S β s t := fun t =>
  ((hWa t).measurable.div (S.stronglyMeasurable_E t _).measurable).stronglyMeasurable

/-- Cochrane (2023), §22.1, p. 496 (OE-2 on a probability space): an equilibrium path is a.s. the
unique price path of the active-money regime given its `M`, and a.s. the unique `(P, M)` of the
active-fiscal regime given its `(W, s)`. -/
theorem oe2 {β : ℝ} {V y P M W s : ℕ → Ω → ℝ} (hV : ∀ t, ∀ᵐ ω ∂S.μ, 0 < V t ω)
    (hy : ∀ t, ∀ᵐ ω ∂S.μ, 0 < y t ω) (hW : ∀ t, ∀ᵐ ω ∂S.μ, W t ω ≠ 0)
    (h : EqmM S β V y P M W s) :
    (∀ P' : ℕ → Ω → ℝ, (∀ t, M t * V t =ᵐ[S.μ] P' t * y t) → ∀ t, P' t =ᵐ[S.μ] P t) ∧
      ∀ P' M' : ℕ → Ω → ℝ, EqmM S β V y P' M' W s →
        (∀ t, P' t =ᵐ[S.μ] P t) ∧ ∀ t, M' t =ᵐ[S.μ] M t := by
  refine ⟨fun P' hP' t => (activeMoney_price hy hP' t).trans
    (activeMoney_price hy (fun t => (h t).2.1) t).symm, fun P' M' h' => ?_⟩
  obtain ⟨e1, e2⟩ := activeFiscal_unique hV hW h h'
  exact ⟨fun t => (e1 t).symm, fun t => (e2 t).symm⟩

/-- Cochrane (2023), §22.1, p. 496 ("fiscal surprises control unexpected inflation", a.s.): if
`W_{t+1}` is chosen at `t`, nonzero a.s., and `1/P_{t+1}` is integrable, then in every equilibrium
the surprise in `1/P_{t+1}` equals the fiscal news `(PV_{t+1} − E_t PV_{t+1})/W_{t+1}` and the
money news `y_{t+1}/(M_{t+1}V_{t+1}) − E_t[y_{t+1}/(M_{t+1}V_{t+1})]`. -/
theorem unexpected_price_level {β : ℝ} {V y P M W s : ℕ → Ω → ℝ}
    (hy : ∀ t, ∀ᵐ ω ∂S.μ, 0 < y t ω) (h : EqmM S β V y P M W s) (t : ℕ)
    (hW : StronglyMeasurable[S.𝓕 t] (W (t + 1))) (hW0 : ∀ᵐ ω ∂S.μ, W (t + 1) ω ≠ 0)
    (hPi : Integrable (fun ω => 1 / P (t + 1) ω) S.μ) :
    ((fun ω => 1 / P (t + 1) ω) - S.E t (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ]
      fun ω => (pvM S β s (t + 1) ω - S.E t (pvM S β s (t + 1)) ω) / W (t + 1) ω) ∧
    ((fun ω => 1 / P (t + 1) ω) - S.E t (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ]
      (fun ω => y (t + 1) ω / (M (t + 1) ω * V (t + 1) ω)) -
        S.E t (fun ω => y (t + 1) ω / (M (t + 1) ω * V (t + 1) ω))) := by
  obtain ⟨hP, hq, hv⟩ := h (t + 1)
  have hinvP : (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ]
      (fun ω => (W (t + 1) ω)⁻¹) * pvM S β s (t + 1) := by
    filter_upwards [hP, hv, hW0] with ω h1 h2 h3
    simp only [Pi.div_apply] at h2
    simp only [Pi.mul_apply, ← h2]
    field_simp [h3, h1.ne']
  have hWi : StronglyMeasurable[S.𝓕 t] fun ω => (W (t + 1) ω)⁻¹ :=
    (hW.measurable.inv).stronglyMeasurable
  have hint : Integrable ((fun ω => (W (t + 1) ω)⁻¹) * pvM S β s (t + 1)) S.μ :=
    hPi.congr hinvP
  have hmon : (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ]
      fun ω => y (t + 1) ω / (M (t + 1) ω * V (t + 1) ω) := by
    filter_upwards [hP, hq, hy (t + 1)] with ω h1 h2 h3
    simp only [Pi.mul_apply] at h2
    rw [h2]
    field_simp [h3.ne', h1.ne']
  refine ⟨?_, ?_⟩
  · filter_upwards [hinvP, S.E_congr hinvP t,
      condExp_mul_of_stronglyMeasurable_left hWi hint (S.integrable_E (t + 1) _), hW0]
      with ω e1 e2 e3 e4
    have e3' : S.E t ((fun ω => (W (t + 1) ω)⁻¹) * pvM S β s (t + 1)) ω =
        (W (t + 1) ω)⁻¹ * S.E t (pvM S β s (t + 1)) ω := e3
    simp only [Pi.sub_apply, Pi.mul_apply] at e1 ⊢
    rw [e1, e2, e3']
    field_simp
  · filter_upwards [hmon, S.E_congr hmon t] with ω e1 e2
    simp only [Pi.sub_apply]
    rw [e1, e2]

/-! ### Inconsistent money and fiscal policy (§22.7) -/

omit mΩ in
/-- Cochrane (2023), §22.7, p. 508 ("no equilibrium can form", a.s.): with `M`, `s` and `W` all
fixed, an equilibrium exists iff `W_t y_t / (M_t V_t) = E_t PV_t` a.s. at every date. -/
theorem inconsistent_iff {mΩ : MeasurableSpace Ω} {S : MeasExpectationSystem Ω} {β : ℝ}
    {V y M W s : ℕ → Ω → ℝ} (hV : ∀ t, ∀ᵐ ω ∂S.μ, 0 < V t ω) (hy : ∀ t, ∀ᵐ ω ∂S.μ, 0 < y t ω)
    (hM : ∀ t, ∀ᵐ ω ∂S.μ, 0 < M t ω) :
    (∃ P, EqmM S β V y P M W s) ↔ ∀ t, W t / (M t * V t / y t) =ᵐ[S.μ] pvM S β s t := by
  constructor
  · rintro ⟨P, hP⟩ t
    filter_upwards [activeMoney_price hy (fun t => (hP t).2.1) t, (hP t).2.2] with ω e1 e2
    simp only [Pi.div_apply] at e1 e2 ⊢
    rw [← e2, e1]
  · intro h
    refine ⟨fun t => M t * V t / y t, fun t => ⟨?_, ?_, h t⟩⟩
    · filter_upwards [hV t, hy t, hM t] with ω h1 h2 h3
      exact div_pos (mul_pos h3 h1) h2
    · filter_upwards [hy t] with ω h1
      simp only [Pi.mul_apply, Pi.div_apply]
      field_simp [h1.ne']

omit mΩ in
/-- Cochrane (2023), §22.7, p. 508 ("suppose that the central bank cuts the money supply in half
and leaves it there", a.s.): if `(M, s, W)` admits an equilibrium and `W_0` is not a.s. zero,
then `(M/2, s, W)` — surpluses unchanged — admits none. -/
theorem halve_money_no_eqm {mΩ : MeasurableSpace Ω} {S : MeasExpectationSystem Ω} {β : ℝ}
    {V y M W s : ℕ → Ω → ℝ} (hV : ∀ t, ∀ᵐ ω ∂S.μ, 0 < V t ω) (hy : ∀ t, ∀ᵐ ω ∂S.μ, 0 < y t ω)
    (hM : ∀ t, ∀ᵐ ω ∂S.μ, 0 < M t ω) (hW : ¬ W 0 =ᵐ[S.μ] 0) (h : ∃ P, EqmM S β V y P M W s) :
    ¬ ∃ P, EqmM S β V y P (fun t => M t / 2) W s := by
  intro h2
  have hM2 : ∀ t, ∀ᵐ ω ∂S.μ, 0 < (fun t => M t / 2) t ω := fun t =>
    (hM t).mono fun ω h => by simp only [Pi.div_apply, Pi.ofNat_apply]; linarith
  apply hW
  filter_upwards [(inconsistent_iff hV hy hM).mp h 0, (inconsistent_iff hV hy hM2).mp h2 0,
    hV 0, hy 0, hM 0] with ω e1 e2 h1 h3 h4
  simp only [Pi.div_apply, Pi.mul_apply, Pi.ofNat_apply] at e1 e2 ⊢
  rw [← e1] at e2
  field_simp at e2
  nlinarith [mul_pos h4 h1]

/-! ### A genuinely random equilibrium -/

open ExpectationsMeasureIID (coin coin_mean coin_var coin_bdd iidSystem shock measurable_shock
  shock_ae_bdd E_shock_zero shock_not_ae_E)

/-- Cochrane (2023), §22.1, p. 496, in the i.i.d. coin economy: the money supply
`M_t = 2 + ε_t`, `V = y = 1`, `W = M` and the surplus `s_t = 1 − β` form an equilibrium (a.s.)
with `P = M`, and the date-1 price level is not a.s. equal to its date-0 forecast. -/
theorem coin_random_eqmM {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    EqmM (iidSystem coin) β 1 1 (fun t ω => 2 + shock t ω) (fun t ω => 2 + shock t ω)
      (fun t ω => 2 + shock t ω) (fun _ _ => 1 - β) ∧
    ¬ (fun ω => 2 + shock 1 ω) =ᵐ[(iidSystem coin).μ]
      (iidSystem coin).E 0 (fun ω => 2 + shock 1 ω) := by
  set S := iidSystem coin with hS
  set M : ℕ → (ℕ → ℝ) → ℝ := fun t ω => 2 + shock t ω with hMdef
  have hM : ∀ t, ∀ᵐ ω ∂S.μ, 0 < M t ω := fun t => by
    filter_upwards [shock_ae_bdd coin coin_bdd t] with ω h
    simp only [hMdef]
    linarith [(abs_le.1 h).1]
  have hpv : ∀ t, pvM S β (fun _ _ => 1 - β) t = fun _ => 1 := fun t => by
    have hd : MeasExpectationSystem.discSum β (fun (_ : ℕ) (_ : ℕ → ℝ) => 1 - β) t =
        fun _ => (1 : ℝ) := by
      funext ω
      simp only [MeasExpectationSystem.discSum]
      rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
      field_simp [(by linarith : (1 : ℝ) - β ≠ 0)]
    simp only [pvM, MeasExpectationSystem.forwardSol]
    rw [hd, S.E_const]
  refine ⟨fun t => ⟨hM t, Eventually.of_forall fun ω => rfl, ?_⟩, fun he => ?_⟩
  · rw [hpv t]
    filter_upwards [hM t] with ω h
    simp only [Pi.div_apply]
    exact div_self h.ne'
  · have hE : S.E 0 (fun ω => 2 + shock 1 ω) =ᵐ[S.μ] fun _ => 2 := by
      have e : (fun ω => 2 + shock 1 ω) = (fun _ => (2 : ℝ)) + shock (0 + 1) := by
        funext ω; simp
      rw [e]
      filter_upwards [S.E_add (x := fun _ => (2 : ℝ)) (y := shock (0 + 1)) (integrable_const 2)
        (Integrable.of_bound (measurable_pi_apply (0 + 1)).aestronglyMeasurable
          1 ((shock_ae_bdd coin coin_bdd (0 + 1)).mono fun ω h => by
            rwa [Real.norm_eq_abs])) 0, E_shock_zero (ν := coin) coin_mean 0] with ω h1 h2
      rw [h1, Pi.add_apply, S.E_const, h2]
      simp
    apply shock_not_ae_E (ν := coin) coin_mean coin_var one_pos 0
    have h1 := he.trans hE
    have h2 : shock (0 + 1) =ᵐ[S.μ] fun _ => (0 : ℝ) := by
      filter_upwards [h1] with ω h
      have h' : 2 + shock 1 ω = 2 := h
      simp only [zero_add]
      linarith
    exact h2.trans (E_shock_zero (ν := coin) coin_mean 0).symm

end Cochrane.ObservationalEquivalence.TidyR5MoneyMeasure
