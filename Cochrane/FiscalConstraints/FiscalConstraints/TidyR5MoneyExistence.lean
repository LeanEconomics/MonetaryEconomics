/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.MoneyLiquidity

/-!
# Existence of the money-and-debt solution with the forward value (6.9)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.5, pp. 201–203,
equation (6.9).

`MoneyLiquidity.eq_6_9` and `MoneyLiquidity.present_value_unique` show that a path of money and
debt solving the flow equation `d(M + B)/dt = i B − P s` and the transversality condition is
the forward present value (6.9), and that it is unique. This module proves the converse,
existence, under the weakest natural hypothesis, and the equivalences.

The liability ratio `w = (M + B)/(P y)` obeys `w' = a w − f` with `a = r^f − g` and the flow
`f = s/y + i M/(P y)`. The natural hypothesis is that the forward present value exists as an
improper integral: `∫₀^T e^{−aτ} f_τ dτ → L` (`ImproperPV`). No sign of `a` and no bound on `f`
is needed.

## Main results

* `fwdValue`: the forward value `ŵ_t = e^{at}(L − ∫₀^t e^{−aτ} f_τ dτ)`;
  `tendsto_finite_pv`: `ŵ_t = lim_T ∫_t^T e^{−a(τ−t)} f_τ dτ` at every date.
* `fwdValue_hasDerivAt`, `fwdValue_tvc`: it solves the flow equation and satisfies the
  transversality condition at every date (existence).
* `tvc_iff`: a solution satisfies the transversality condition iff it equals the forward value
  at that date; `eq_fwdValue_of_tvc`, `existsUnique_tvc` (uniqueness of the whole path).
* `exists_tvc_iff`: a solution with the transversality condition exists iff the improper
  present value converges.
* `fwdValue_eq_integral`: under Lebesgue integrability the forward value is the Bochner
  integral `∫_t^∞ e^{−a(τ−t)} f_τ dτ`; `integrable_of_bdd` (the setting of
  `MoneyLiquidity.eq_6_9`: `r^f > g`, bounded flows).
* For money and debt: `money_debt_exists` (debt `B = P y ŵ − M` solves the flow equation, has
  the value (6.9) and satisfies the transversality condition), `money_debt_unique`,
  `money_debt_tvc_iff`, `money_debt_exists_iff`, `eq_6_9_exists` (the bounded case of (6.9)).
-/

namespace Cochrane.FiscalConstraints.TidyR5MoneyExistence

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.LinearODE

/-- Cochrane (2023), (6.9) p. 201: the forward present value of the flow `f` discounted at `a`
converges as an improper integral to `L`: `∫₀^T e^{−aτ} f_τ dτ → L` as `T → ∞`. -/
def ImproperPV (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun T => ∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ) atTop (𝓝 L)

/-- Cochrane (2023), (6.9) p. 201: the forward value `ŵ_t = e^{at}(L − ∫₀^t e^{−aτ} f_τ dτ)`
(the variation-of-constants solution through `(0, L)`). -/
noncomputable def fwdValue (a : ℝ) (f : ℝ → ℝ) (L t : ℝ) : ℝ := vocFrom a f 0 L t

/-- Cochrane (2023), (6.9) p. 201: the forward value written out. -/
theorem fwdValue_eq (a : ℝ) (f : ℝ → ℝ) (L t : ℝ) :
    fwdValue a f L t = exp (a * t) * (L - ∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) := by
  unfold fwdValue vocFrom
  rw [mul_zero, exp_zero, one_mul]

variable {a L K : ℝ} {f w : ℝ → ℝ}

/-- Cochrane (2023), (6.13) p. 203: the finite-horizon present value from `t` to `T` is
`e^{at}(∫₀^T e^{−aτ} f − ∫₀^t e^{−aτ} f)`. -/
theorem finite_pv_eq (hf : Continuous f) (t T : ℝ) :
    ∫ τ in t..T, exp (-a * (τ - t)) * f τ =
      exp (a * t) * ((∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ) -
        ∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) := by
  have hc : Continuous fun τ => exp (-a * τ) * f τ := by fun_prop
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 T)
    (hc.intervalIntegrable 0 t), ← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), (6.9) p. 201: when the improper present value converges, the forward value
at every date `t` is the limit of the finite-horizon present values,
`ŵ_t = lim_{T→∞} ∫_t^T e^{−a(τ−t)} f_τ dτ`. -/
theorem tendsto_finite_pv (hf : Continuous f) (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => ∫ τ in t..T, exp (-a * (τ - t)) * f τ) atTop
      (𝓝 (fwdValue a f L t)) := by
  simp_rw [finite_pv_eq hf t, fwdValue_eq]
  exact (hL.sub_const _).const_mul _

/-- Cochrane (2023), (6.9) p. 201 (existence, the flow equation): the forward value solves
`w' = a w − f` at every date. -/
theorem fwdValue_hasDerivAt (hf : Continuous f) (L τ : ℝ) :
    HasDerivAt (fwdValue a f L) (a * fwdValue a f L τ - f τ) τ :=
  vocFrom_hasDerivAt a hf 0 L τ

/-- Cochrane (2023), (6.12)–(6.13) pp. 202–203: for any solution of `w' = a w − f`, the
discounted terminal value is `e^{−a(T−t)} w_T = w_t − ∫_t^T e^{−a(τ−t)} f_τ dτ`. -/
theorem terminal_eq (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (t T : ℝ) :
    exp (-a * (T - t)) * w T = w t - ∫ τ in t..T, exp (-a * (τ - t)) * f τ := by
  have := finite_horizon_identity hw hf t T
  linarith

/-- Cochrane (2023), (6.9) p. 201: for any solution, the discounted terminal value converges to
`w_t − ŵ_t`. -/
theorem tendsto_terminal (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f)
    (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 (w t - fwdValue a f L t)) := by
  simp_rw [terminal_eq hw hf t]
  exact (tendsto_finite_pv hf hL t).const_sub _

/-- Cochrane (2023), (6.9) p. 201 (**the iff**): a solution of the flow equation satisfies the
transversality condition `e^{−a(T−t)} w_T → 0` iff its value at `t` is the forward value (6.9). -/
theorem tvc_iff (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f)
    (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0) ↔ w t = fwdValue a f L t := by
  have h := tendsto_terminal hw hf hL t
  constructor
  · intro h0
    have := tendsto_nhds_unique h h0
    linarith
  · intro he
    rwa [he, sub_self] at h

/-- Cochrane (2023), (6.9) p. 201 (**existence**, the transversality condition): the forward
value satisfies the transversality condition at every date. -/
theorem fwdValue_tvc (hf : Continuous f) (hL : ImproperPV a f L) (t : ℝ) :
    Tendsto (fun T => exp (-a * (T - t)) * fwdValue a f L T) atTop (𝓝 0) :=
  (tvc_iff (fwdValue_hasDerivAt hf L) hf hL t).2 rfl

/-- Cochrane (2023), (6.9) p. 201 (uniqueness of the whole path): a solution satisfying the
transversality condition at one date `t` is the forward value at every date. -/
theorem eq_fwdValue_of_tvc (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f)
    (hL : ImproperPV a f L) {t : ℝ}
    (htvc : Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0)) :
    w = fwdValue a f L := by
  have ht := (tvc_iff hw hf hL t).1 htvc
  funext T
  rw [vocFrom_eq_of_global hw hf t T, vocFrom_eq_of_global (fwdValue_hasDerivAt hf L) hf t T,
    ht]

/-- Cochrane (2023), (6.9) p. 201 (**existence and uniqueness**): when the improper present
value converges, there is exactly one solution of the flow equation satisfying the
transversality condition at `t`, the forward value. -/
theorem existsUnique_tvc (hf : Continuous f) (hL : ImproperPV a f L) (t : ℝ) :
    ∃! w : ℝ → ℝ, (∀ τ, HasDerivAt w (a * w τ - f τ) τ) ∧
      Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0) :=
  ⟨fwdValue a f L, ⟨fwdValue_hasDerivAt hf L, fwdValue_tvc hf hL t⟩,
    fun _ hw => eq_fwdValue_of_tvc hw.1 hf hL hw.2⟩

/-- Cochrane (2023), (6.9) p. 201 (**the existence iff**): a solution of the flow equation
satisfying the transversality condition exists iff the forward present value converges as an
improper integral. -/
theorem exists_tvc_iff (hf : Continuous f) (t : ℝ) :
    (∃ w : ℝ → ℝ, (∀ τ, HasDerivAt w (a * w τ - f τ) τ) ∧
      Tendsto (fun T => exp (-a * (T - t)) * w T) atTop (𝓝 0)) ↔ ∃ L, ImproperPV a f L := by
  constructor
  · rintro ⟨w, hw, htvc⟩
    have hJ : Tendsto (fun T => ∫ τ in t..T, exp (-a * (τ - t)) * f τ) atTop (𝓝 (w t)) := by
      have h := htvc.const_sub (w t)
      rw [sub_zero] at h
      refine h.congr fun T => ?_
      rw [terminal_eq hw hf t T]
      ring
    refine ⟨(∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) + exp (-a * t) * w t, ?_⟩
    have he : ∀ T, ∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ = (∫ τ in (0 : ℝ)..t,
        exp (-a * τ) * f τ) + exp (-a * t) * ∫ τ in t..T, exp (-a * (τ - t)) * f τ := by
      intro T
      rw [finite_pv_eq hf t T]
      have e : exp (-a * t) * exp (a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
      generalize (∫ τ in (0 : ℝ)..T, exp (-a * τ) * f τ) = I1
      generalize (∫ τ in (0 : ℝ)..t, exp (-a * τ) * f τ) = I2
      linear_combination (-(I1 - I2)) * e
    exact ((hJ.const_mul _).const_add _).congr fun T => (he T).symm
  · rintro ⟨L, hL⟩
    exact ⟨fwdValue a f L, fwdValue_hasDerivAt hf L, fwdValue_tvc hf hL t⟩

/-- Cochrane (2023), (6.9) p. 201: a continuous flow whose discounted value is integrable on
`(0, ∞)` is integrable on every `(c, ∞)`. -/
theorem integrableOn_Ioi_of (hf : Continuous f)
    (hint : IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi 0)) (c : ℝ) :
    IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi c) := by
  have hc : Continuous fun τ => exp (-a * τ) * f τ := by fun_prop
  refine ((hc.integrableOn_Icc (a := min c 0) (b := 0)).union hint).mono_set fun τ hτ => ?_
  rcases le_or_gt τ 0 with h | h
  · exact Or.inl ⟨le_trans (min_le_left _ _) (le_of_lt hτ), h⟩
  · exact Or.inr h

/-- Cochrane (2023), (6.9) p. 201: under Lebesgue integrability of the discounted flow, the
improper present value converges to `∫₀^∞ e^{−aτ} f_τ dτ`, and the forward value at every date
is the Bochner integral `ŵ_t = ∫_t^∞ e^{−a(τ−t)} f_τ dτ`. -/
theorem fwdValue_eq_integral (hf : Continuous f)
    (hint : IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi 0)) :
    ImproperPV a f (∫ τ in Set.Ioi (0 : ℝ), exp (-a * τ) * f τ) ∧
      ∀ t, fwdValue a f (∫ τ in Set.Ioi (0 : ℝ), exp (-a * τ) * f τ) t =
        ∫ τ in Set.Ioi t, exp (-a * (τ - t)) * f τ := by
  refine ⟨intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id, fun t => ?_⟩
  rw [fwdValue_eq, ExpIntegrals.integral_Ioi_sub_interval (integrableOn_Ioi_of hf hint) t,
    ← integral_const_mul]
  congr 1
  funext τ
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), (6.9) p. 201 (the setting of `MoneyLiquidity.eq_6_9`): with `a = r^f − g > 0`
and a bounded continuous flow, the discounted flow is integrable on `(0, ∞)`. -/
theorem integrable_of_bdd (ha : 0 < a) (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K) :
    IntegrableOn (fun τ => exp (-a * τ) * f τ) (Set.Ioi 0) :=
  ExpIntegrals.integrableOn_exp_mul_bdd ha hf hK 0

/-! ### Money and debt -/

variable {M B P y s infl i : ℝ → ℝ} {g rf : ℝ}

/-- Cochrane (2023), (6.9) p. 201: for any money-and-debt path solving the flow equation
`d(M + B)/dt = i B − P s`, with `dP/dt = π P`, `dy/dt = g y` and `i = r^f + π`, the liability
ratio `w = (M + B)/(P y)` solves `w' = (r^f − g) w − (s/y + i M/(P y))`. -/
theorem ratio_hasDerivAt (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ) (τ : ℝ) :
    HasDerivAt (fun x => (M x + B x) / (P x * y x))
      ((rf - g) * ((M τ + B τ) / (P τ * y τ)) - (s τ / y τ + i τ * (M τ / (P τ * y τ)))) τ := by
  have h := MoneyLiquidity.hasDerivAt_liabilityRatio (g := fun _ => g) (hW τ) (hP τ) (hy τ)
    (hP0 τ) (hy0 τ)
  convert h using 1
  rw [hi τ]
  ring

/-- Cochrane (2023), (6.9) p. 201: with debt `B = P y W − M`, the liability ratio
`(M + B)/(P y)` is `W`. -/
theorem ratio_of_debt (W : ℝ → ℝ) {t : ℝ} (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    (M t + (P t * y t * W t - M t)) / (P t * y t) = W t := by
  have := mul_ne_zero hP0 hy0
  field_simp
  ring

/-- Cochrane (2023), (6.9) p. 201: if a ratio path `W` solves
`W' = (r^f − g) W − (s/y + i M/(P y))`, with `dP/dt = π P`, `dy/dt = g y` and `i = r^f + π`, then
debt `B = P y W − M` solves the flow equation `d(M + B)/dt = i B − P s`. -/
theorem flow_of_debt {W : ℝ → ℝ} {τ : ℝ} (hP : HasDerivAt P (infl τ * P τ) τ)
    (hy : HasDerivAt y (g * y τ) τ) (hP0 : P τ ≠ 0) (hy0 : y τ ≠ 0) (hi : i τ = rf + infl τ)
    (hW : HasDerivAt W ((rf - g) * W τ - (s τ / y τ + i τ * (M τ / (P τ * y τ)))) τ) :
    HasDerivAt (fun x => M x + (P x * y x * W x - M x))
      (i τ * (P τ * y τ * W τ - M τ) - P τ * s τ) τ := by
  have hMB : (fun x => M x + (P x * y x * W x - M x)) = fun x => P x * y x * W x := by
    funext x; ring
  rw [hMB]
  refine ((hP.mul hy).mul hW).congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [hi]
  field_simp
  ring

/-- Cochrane (2023), (6.9) p. 201 (**existence for money and debt**): given money `M`, the price
level, output and the surplus, with `i = r^f + π` and a convergent improper present value `L` of
`f = s/y + i M/(P y)` discounted at `r^f − g`, the debt path `B = P y ŵ − M` solves the flow
equation `d(M + B)/dt = i B − P s` at every date, its liability ratio is the forward value (6.9)
at every date, and it satisfies the transversality condition at every date. -/
theorem money_debt_exists (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hi : ∀ τ, i τ = rf + infl τ) (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hL : ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L) :
    let B := fun τ => P τ * y τ *
      fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L τ - M τ
    (∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ) ∧
      (∀ t, (M t + B t) / (P t * y t) =
        fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L t) ∧
      ∀ t, Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop
        (𝓝 0) := by
  intro B
  set F := fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)) with hF
  have hratio : ∀ t, (M t + B t) / (P t * y t) = fwdValue (rf - g) F L t := fun t =>
    ratio_of_debt (fwdValue (rf - g) F L) (hP0 t) (hy0 t)
  refine ⟨fun τ => flow_of_debt (hP τ) (hy τ) (hP0 τ) (hy0 τ) (hi τ)
    (fwdValue_hasDerivAt (a := rf - g) hf L τ), hratio, fun t => ?_⟩
  simp_rw [hratio]
  exact fwdValue_tvc hf hL t

/-- Cochrane (2023), (6.9) p. 201 (**the iff for money and debt**): for a money-and-debt path
solving the flow equation, the transversality condition at `t` holds iff the value of money and
debt at `t` is the forward value (6.9). -/
theorem money_debt_tvc_iff
    (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ)
    (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hL : ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L) (t : ℝ) :
    Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop (𝓝 0) ↔
      (M t + B t) / (P t * y t) =
        fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L t :=
  tvc_iff (w := fun x => (M x + B x) / (P x * y x))
    (ratio_hasDerivAt hW hP hy hP0 hy0 hi) hf hL t

/-- Cochrane (2023), (6.9) p. 201 (**uniqueness for money and debt**): any debt path solving the
flow equation and the transversality condition at one date is the debt of `money_debt_exists`,
`B = P y ŵ − M`, at every date. -/
theorem money_debt_unique
    (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ)
    (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hL : ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L) {t : ℝ}
    (htvc : Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop
      (𝓝 0)) :
    B = fun τ => P τ * y τ *
      fwdValue (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L τ - M τ := by
  have h := eq_fwdValue_of_tvc (w := fun x => (M x + B x) / (P x * y x))
    (ratio_hasDerivAt hW hP hy hP0 hy0 hi) hf hL htvc
  funext τ
  have hτ := congrFun h τ
  have h1 := hP0 τ
  have h2 := hy0 τ
  change (M τ + B τ) / (P τ * y τ) = _ at hτ
  rw [← hτ]
  field_simp
  ring

/-- Cochrane (2023), (6.9) p. 201 (**the existence iff for money and debt**): given money, prices,
output and surpluses, a debt path solving the flow equation and the transversality condition at
`t` exists iff the present value of `s/y + i M/(P y)` discounted at `r^f − g` converges as an
improper integral. -/
theorem money_debt_exists_iff (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hi : ∀ τ, i τ = rf + infl τ) (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (t : ℝ) :
    (∃ B : ℝ → ℝ, (∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ) ∧
      Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop (𝓝 0))
      ↔ ∃ L, ImproperPV (rf - g) (fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ))) L := by
  constructor
  · rintro ⟨B, hW, htvc⟩
    exact (exists_tvc_iff hf t).1 ⟨_, ratio_hasDerivAt hW hP hy hP0 hy0 hi, htvc⟩
  · rintro ⟨L, hL⟩
    obtain ⟨h1, -, h3⟩ := money_debt_exists hP hy hP0 hy0 hi hf hL
    exact ⟨_, h1, h3 t⟩

/-- Cochrane (2023), (6.9) p. 201 (**existence in the setting of `MoneyLiquidity.eq_6_9`**): with
`r^f > g`, `i = r^f + π` and a bounded continuous flow `s/y + i M/(P y)`, there is a debt path
solving the flow equation and the transversality condition at every date, whose value of money
and debt is the Bochner present value (6.9),
`(M_t + B_t)/(P_t y_t) = ∫_t^∞ e^{−(r^f−g)(τ−t)} (s_τ/y_τ + i_τ M_τ/(P_τ y_τ)) dτ`, at every
date. -/
theorem eq_6_9_exists (hrg : g < rf) (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hi : ∀ τ, i τ = rf + infl τ) (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hK : ∀ τ, |s τ / y τ + i τ * (M τ / (P τ * y τ))| ≤ K) :
    ∃ B : ℝ → ℝ, (∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ) ∧
      (∀ t, Tendsto (fun T => exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T))) atTop
        (𝓝 0)) ∧
      ∀ t, (M t + B t) / (P t * y t) = ∫ τ in Set.Ioi t, exp (-(rf - g) * (τ - t)) *
        (s τ / y τ + i τ * (M τ / (P τ * y τ))) := by
  have hint := integrable_of_bdd (sub_pos.2 hrg) hf hK
  obtain ⟨hL, hrep⟩ := fwdValue_eq_integral hf hint
  obtain ⟨h1, h2, h3⟩ := money_debt_exists hP hy hP0 hy0 hi hf hL
  exact ⟨_, h1, h3, fun t => (h2 t).trans (hrep t)⟩

end Cochrane.FiscalConstraints.TidyR5MoneyExistence
