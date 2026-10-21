/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Money in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 4, "Money in
continuous time", pp. 635–641, and Online Appendix A1, §1.6, pp. 567–569.

Deterministic paths `ℝ → ℝ` with `HasDerivAt`; present values are improper integrals over
`(t, ∞)` (`MeasureTheory.integral` on `Set.Ioi t` with `IntegrableOn`); transversality conditions
are explicit limits.

## Contents

* **Infrastructure**: forward integration in "iff" form (TVC ⇔ present value), the discount
  factor `Λ_t = e^{−∫_0^t r}` (`Λ' = −rΛ`), the nominal discount factor `Λ/P` (`(Λ/P)' = −iΛ/P`).
* **A1 §1.6, (1.31)–(1.37)** (restated from the Cochrane Generality project, Chapter 3 §3.6.4):
  money creation vs interest saving, the money TVC, ex-post discounting with `W` and `W^m`.
* **A4 p. 635, (4.5)**: the present-value budget with consumption, by integration plus TVC.
* **(4.1)–(4.4)**: the intertemporal and intratemporal first-order conditions, derived by
  differentiating the marginal-utility condition along the path (chain rule through `u_c(c, m)`).
* **CES utility (p. 636–637)**: special cases, exact derivatives `u_c`, `u_m`, `u_cc`, `u_cm`
  (`HasDerivAt`), (4.7), the elasticities.
* **CES limits (E20)**: `θ → 1` holds only for the normalised aggregator (the printed one diverges);
  `θ → ∞` with fixed `α` gives `min(c, m)` and `m/c → 1`; the printed `min(c, αm)`, `M/P = c/α`
  needs the coefficient `α^{−θ}`; and `M/P = c/α` means `V = α`, not `α = 1/V`.
* **(4.8)–(4.10)**, the interest cost `(m/c)(i − i^m) = α^ξ(i − i^m)^{1−ξ} → 0` iff `ξ < 1`.
* **IS curve with money (4.11)–(4.15), E21**: the exact equation
  `ẋ + (σ − ξ)(m/c)/(1 + A)·d(i − i^m)/dt = σ(i − π − δ)`, its first-order form at the steady state,
  the dropped `−δσ`, and the inconsistency of (4.15) with the discrete version of (4.13).
* **Hamiltonian (4.16)–(4.17)**: the constraint from `dM = (y − c − s)P dt`, the money-demand
  consequence `v'/u' = −µ̇/µ + δ + Ṗ/P = i`, and the TVC.
-/

namespace Cochrane.Monetarism.ContinuousTime

open Filter Topology MeasureTheory

/-! ## Forward integration -/

/-- Cochrane (2023), A1 (1.28), p. 566 (restated from the Cochrane Generality project): if
`G' = g` on `[t, ∞)` and `g` is integrable on `(t, ∞)`, then `G_T → G_t + ∫_t^∞ g`. -/
theorem tendsto_of_hasDerivAt {G g : ℝ → ℝ} {t : ℝ}
    (hG : ∀ τ, t ≤ τ → HasDerivAt G (g τ) τ) (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto G atTop (𝓝 (G t + ∫ τ in Set.Ioi t, g τ)) := by
  have hI := (intervalIntegral_tendsto_integral_Ioi t hg tendsto_id).const_add (G t)
  refine hI.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have hT' : t ≤ id T := hT
  have hint : IntervalIntegrable g volume t T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT').2 (hg.mono_set Set.Ioc_subset_Ioi_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hG x (by rw [Set.uIcc_of_le hT] at hx; exact hx.1)) hint
  simp only [id]
  rw [hftc]
  ring

/-- Cochrane (2023), A1 (1.33)–(1.34), p. 567 (restated from the Cochrane Generality project):
**forward integration, iff form.** If `G' = −h` on `[t, ∞)` and `h` is integrable on `(t, ∞)`,
then `G_T → 0` iff `G_t = ∫_t^∞ h`. -/
theorem forward_iff {G h : ℝ → ℝ} {t : ℝ} (hG : ∀ τ, t ≤ τ → HasDerivAt G (-h τ) τ)
    (hh : IntegrableOn h (Set.Ioi t)) :
    Tendsto G atTop (𝓝 0) ↔ G t = ∫ τ in Set.Ioi t, h τ := by
  have hlim := tendsto_of_hasDerivAt (g := fun τ => -h τ) hG hh.neg
  rw [integral_neg] at hlim
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro he
    have : G t + -∫ τ in Set.Ioi t, h τ = 0 := by rw [he]; ring
    rwa [this] at hlim

/-- Cochrane (2023), A1 p. 567 (restated from the Cochrane Generality project): pulling the
constant `1/Λ_t` out of the present-value integral. -/
theorem integral_ratio_eq {Λ f : ℝ → ℝ} (t : ℝ) :
    ∫ τ in Set.Ioi t, Λ τ / Λ t * f τ = (Λ t)⁻¹ * ∫ τ in Set.Ioi t, Λ τ * f τ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), A1 (1.33), p. 567 (restated from the Cochrane Generality project):
converting `N_tX = ∫_t^∞ NPf` (with `Λ = NP`) into `X/P_t = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`. -/
theorem real_form_iff {N P f : ℝ → ℝ} {X t : ℝ} (hN : 0 < N t) (hP : 0 < P t) :
    N t * X = ∫ τ in Set.Ioi t, N τ * P τ * f τ ↔
      X / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * f τ := by
  have h := integral_ratio_eq (Λ := fun τ => N τ * P τ) (f := f) t
  rw [h]
  have hNP : 0 < N t * P t := mul_pos hN hP
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hP.ne'] at e
    rw [e]
    field_simp

/-! ## Discount factors -/

/-- Cochrane (2023), A4 p. 635: **the discount factor `Λ_t = e^{−∫_0^t r_s ds}`** satisfies
`Λ' = −rΛ` when the real rate `r` is continuous. -/
theorem hasDerivAt_discount {r : ℝ → ℝ} (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun u => Real.exp (-∫ s in (0 : ℝ)..u, r s))
      (-r t * Real.exp (-∫ s in (0 : ℝ)..t, r s)) t := by
  have h := (hr.integral_hasStrictDerivAt 0 t).hasDerivAt
  exact (HasDerivAt.exp (HasDerivAt.neg h)).congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- Cochrane (2023), A4 p. 635 (`r_t = i_t − dP_t/P_t`): if `Λ' = −(i − Ṗ/P)Λ` and `P` is
differentiable and nonzero, the nominal discount factor obeys `(Λ/P)' = −i(Λ/P)`. -/
theorem hasDerivAt_nominal_discount {Λ P : ℝ → ℝ} {i dP τ : ℝ}
    (hΛ : HasDerivAt Λ (-(i - dP / P τ) * Λ τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => Λ x / P x) (-i * (Λ τ / P τ)) τ := by
  convert hΛ.div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), A1 (1.35), p. 568 (restated from the Cochrane Generality project): if
`X' = iX` (the nominal value of the short-bond portfolio `X = PW`), then `(1/X)' = −i(1/X)`. -/
theorem inv_nominal_value {X : ℝ → ℝ} {i τ : ℝ} (hX : HasDerivAt X (i * X τ) τ)
    (hXτ : X τ ≠ 0) : HasDerivAt (fun u => 1 / X u) (-i * (1 / X τ)) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div hX hXτ
  convert h using 1
  field_simp
  ring

/-- Cochrane (2023), A1 p. 568: with `Λ = NP` and `N = 1/(PW)`, `Λ_τ/Λ_t = W_t/W_τ`. -/
theorem lambda_ratio_eq_W {P W : ℝ → ℝ} {t τ : ℝ} (hPt : P t ≠ 0) (hPτ : P τ ≠ 0)
    (hWt : W t ≠ 0) (hWτ : W τ ≠ 0) :
    (1 / (P τ * W τ) * P τ) / (1 / (P t * W t) * P t) = W t / W τ := by
  field_simp

/-! ## A1 §1.6: the valuation equation with money -/

/-- Cochrane (2023), A1 (1.31), p. 567: the nominal flow `dM = iB + i^mM − Ps − dB` in real
terms, `(B/P)i + (M/P)i^m = s + dB/P + dM/P`. -/
theorem flow_real {B M P s i im dB dM : ℝ} (hP : P ≠ 0)
    (hflow : dM = i * B + im * M - P * s - dB) :
    B / P * i + M / P * im = s + dB / P + dM / P := by
  rw [hflow]
  field_simp
  ring

/-- Cochrane (2023), A1 (1.32), p. 567: with `i^m = 0`, along the flow the discounted debt obeys
`d(NB) = −NP(s + dM/P)` (`N = Λ/P`, `N' = −iN`). -/
theorem printing_hasDerivAt {N B P s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * B u) (-(N τ * P τ * (s τ + dM τ / P τ))) τ :=
  (hN.mul hB).congr_deriv (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), A1 (1.33), p. 567: **seigniorage as money creation.** With `i^m = 0`, the TVC
`Λ_TB_T/P_T → 0` holds iff `B_t/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + dM_τ/P_τ) dτ`. -/
theorem money_printing_iff {N B P s i dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + dM τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => N T * B T) atTop (𝓝 0) ↔
      B t / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ) := by
  rw [forward_iff (fun τ hτ => printing_hasDerivAt (hN τ hτ) (hB τ hτ) (hP τ hτ).ne'
    (hflow τ hτ)) hint]
  exact real_form_iff (f := fun τ => s τ + dM τ / P τ) hNt (hP t le_rfl)

/-- Cochrane (2023), A1 p. 567: with interest on money, along the flow
`d(N(M + B)) = −NP(s + (i − i^m)M/P)`. -/
theorem interest_hasDerivAt {N B M P s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ)
    (hM : HasDerivAt M (dM τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * (M u + B u))
      (-(N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  (hN.mul (HasDerivAt.add hM hB)).congr_deriv
    (by rw [hflow]; simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), A1 (1.34), p. 567: **seigniorage as interest saving.** The TVC
`Λ_T(M_T + B_T)/P_T → 0` holds iff
`(M_t + B_t)/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ`. -/
theorem money_interest_iff {N B M P s i im dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => N T * (M T + B T)) atTop (𝓝 0) ↔
      (M t + B t) / P t =
        ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - im τ) * M τ / P τ) := by
  rw [forward_iff (fun τ hτ => interest_hasDerivAt (hN τ hτ) (hB τ hτ) (hM τ hτ)
    (hP τ hτ).ne' (hflow τ hτ)) hint]
  exact real_form_iff (f := fun τ => s τ + (i τ - im τ) * M τ / P τ) hNt (hP t le_rfl)

/-- Cochrane (2023), A1 §1.6, p. 567: with `i^m = 0`, given (1.33), (1.34) holds **iff** the
money transversality condition `Λ_TM_T/P_T → 0` holds. -/
theorem printing_interest_iff_money_tvc {N B M P s i dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint1 : IntegrableOn (fun τ => N τ * P τ * (s τ + dM τ / P τ)) (Set.Ioi t))
    (hint2 : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - 0) * M τ / P τ)) (Set.Ioi t))
    (h133 : B t / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ)) :
    (M t + B t) / P t =
        ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - 0) * M τ / P τ) ↔
      Tendsto (fun T => N T * M T) atTop (𝓝 0) := by
  have hBtvc := (money_printing_iff hN hNt hB hP hflow hint1).2 h133
  rw [← money_interest_iff (im := fun _ => 0) hN hNt hB hM hP
    (fun τ hτ => by rw [hflow τ hτ]; ring) hint2]
  constructor
  · intro h
    have := h.sub hBtvc
    rw [sub_zero] at this
    exact this.congr fun T => by ring
  · intro h
    have := h.add hBtvc
    rw [add_zero] at this
    exact this.congr fun T => by ring

/-- Cochrane (2023), A1 (1.36), p. 568: with `i^m = 0` and `(PW)' = iPW`,
`d(B/(PW)) = −(1/W)(s + dM/P)`; the price level itself need not be differentiable. -/
theorem printing_W_hasDerivAt {P W B s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * B u) (-(1 / W τ * (s τ + dM τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul hB).congr_deriv
    (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), A1 (1.36), p. 568: **ex-post discounting, money creation.** The TVC
`B_T/(P_TW_T) → 0` holds iff `B_t/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + dM_τ/P_τ) dτ`. -/
theorem money_printing_W_iff {P W B s i dB dM : ℝ → ℝ} {t : ℝ}
    (hX : ∀ τ, t ≤ τ → HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ) (hW : ∀ τ, t ≤ τ → 0 < W τ)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => 1 / W τ * (s τ + dM τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => 1 / (P T * W T) * B T) atTop (𝓝 0) ↔
      B t / P t = ∫ τ in Set.Ioi t, W t / W τ * (s τ + dM τ / P τ) := by
  rw [forward_iff (fun τ hτ => printing_W_hasDerivAt (hX τ hτ) (hP τ hτ).ne' (hW τ hτ).ne'
    (hB τ hτ) (hflow τ hτ)) hint]
  have h := integral_ratio_eq (Λ := fun τ => 1 / W τ) (f := fun τ => s τ + dM τ / P τ) t
  have hc : ∫ τ in Set.Ioi t, W t / W τ * (s τ + dM τ / P τ) =
      ∫ τ in Set.Ioi t, 1 / W τ / (1 / W t) * (s τ + dM τ / P τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [one_div, one_div, inv_div_inv]
  have hWt := (hW t le_rfl).ne'
  have hPt := (hP t le_rfl).ne'
  rw [hc, h]
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hPt] at e
    rw [e]
    field_simp

/-- Cochrane (2023), A1 p. 568: with interest on money,
`d((B + M)/(PW)) = −(1/W)(s + (i − i^m)M/P)`. -/
theorem interest_W_hasDerivAt {P W B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * (B u + M u))
      (-(1 / W τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), A1 p. 568: **ex-post discounting, interest saving.** The TVC
`(B_T + M_T)/(P_TW_T) → 0` holds iff
`(B_t + M_t)/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` (the rate dated `τ`; the
book prints `(i_t − i^m_t)`, see `printed_index_counterexample`). -/
theorem money_interest_W_iff {P W B M s i im dB dM : ℝ → ℝ} {t : ℝ}
    (hX : ∀ τ, t ≤ τ → HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ) (hW : ∀ τ, t ≤ τ → 0 < W τ)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => 1 / W τ * (s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi t)) :
    Tendsto (fun T => 1 / (P T * W T) * (B T + M T)) atTop (𝓝 0) ↔
      (B t + M t) / P t = ∫ τ in Set.Ioi t, W t / W τ * (s τ + (i τ - im τ) * M τ / P τ) := by
  rw [forward_iff (fun τ hτ => interest_W_hasDerivAt (hX τ hτ) (hP τ hτ).ne' (hW τ hτ).ne'
    (hB τ hτ) (hM τ hτ) (hflow τ hτ)) hint]
  have h := integral_ratio_eq (Λ := fun τ => 1 / W τ)
    (f := fun τ => s τ + (i τ - im τ) * M τ / P τ) t
  have hc : ∫ τ in Set.Ioi t, W t / W τ * (s τ + (i τ - im τ) * M τ / P τ) =
      ∫ τ in Set.Ioi t, 1 / W τ / (1 / W t) * (s τ + (i τ - im τ) * M τ / P τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [one_div, one_div, inv_div_inv]
  have hWt := (hW t le_rfl).ne'
  have hPt := (hP t le_rfl).ne'
  rw [hc, h]
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hPt] at e
    rw [e]
    field_simp

/-- Cochrane (2023), A1 p. 568 (index typo): the printed integrand `(i_t − i^m_t)M_τ/P_τ` (rate
dated `t`) is wrong. With `P ≡ 1`, `i ≡ 1`, `W_τ = e^τ`, `B ≡ 0`, `M ≡ 1`, `i^m_τ = e^{−τ}` and
`s = i^m` the flow holds, the correctly dated integral equals `(B_0 + M_0)/P_0 = 1`, the printed
one equals `1/2`. -/
theorem printed_index_counterexample :
    let im : ℝ → ℝ := fun τ => Real.exp (-τ)
    (∀ τ : ℝ, (0 : ℝ) = 1 * 0 + im τ * 1 - 1 * im τ - 0) ∧
      ∫ τ in Set.Ioi (0 : ℝ), Real.exp 0 / Real.exp τ * (im τ + (1 - im τ) * 1 / 1) = 1 ∧
      ∫ τ in Set.Ioi (0 : ℝ), Real.exp 0 / Real.exp τ * (im τ + (1 - im 0) * 1 / 1) = 1 / 2 := by
  intro im
  refine ⟨fun τ => by ring, ?_, ?_⟩
  · have : ∀ τ : ℝ, Real.exp 0 / Real.exp τ * (im τ + (1 - im τ) * 1 / 1) =
        Real.exp (-1 * τ) := by
      intro τ
      rw [Real.exp_zero, neg_one_mul, Real.exp_neg]
      ring
    simp_rw [this]
    rw [integral_exp_mul_Ioi (by norm_num) 0]
    norm_num
  · have : ∀ τ : ℝ, Real.exp 0 / Real.exp τ * (im τ + (1 - im 0) * 1 / 1) =
        Real.exp (-2 * τ) := by
      intro τ
      simp only [im, neg_zero, Real.exp_zero, sub_self, zero_mul, zero_div, add_zero]
      rw [show -2 * τ = -τ + -τ by ring, Real.exp_add, Real.exp_neg]
      ring
    simp_rw [this]
    rw [integral_exp_mul_Ioi (by norm_num) 0]
    norm_num

/-- Cochrane (2023), A1 (1.37), p. 569: if `PW^m` grows at the mixed rate
`(Bi + Mi^m)/(B + M)`, then along the flow `d((B + M)/(PW^m)) = −(s/W^m)`. -/
theorem mixed_hasDerivAt {P Wm B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * Wm u)
      ((B τ * i τ + M τ * im τ) / (B τ + M τ) * (P τ * Wm τ)) τ)
    (hPτ : P τ ≠ 0) (hWτ : Wm τ ≠ 0) (hBM : B τ + M τ ≠ 0)
    (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * Wm u) * (B u + M u)) (-(1 / Wm τ * s τ)) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), A1 (1.37), p. 569: **valuation with the mixed portfolio return.** The TVC
`(B_T + M_T)/(P_TW^m_T) → 0` holds iff `(B_t + M_t)/P_t = ∫_t^∞ (W^m_t/W^m_τ) s_τ dτ`. -/
theorem money_mixed_iff {P Wm B M s i im dB dM : ℝ → ℝ} {t : ℝ}
    (hX : ∀ τ, t ≤ τ → HasDerivAt (fun u => P u * Wm u)
      ((B τ * i τ + M τ * im τ) / (B τ + M τ) * (P τ * Wm τ)) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ) (hW : ∀ τ, t ≤ τ → 0 < Wm τ)
    (hBM : ∀ τ, t ≤ τ → 0 < B τ + M τ)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ)
    (hint : IntegrableOn (fun τ => 1 / Wm τ * s τ) (Set.Ioi t)) :
    Tendsto (fun T => 1 / (P T * Wm T) * (B T + M T)) atTop (𝓝 0) ↔
      (B t + M t) / P t = ∫ τ in Set.Ioi t, Wm t / Wm τ * s τ := by
  rw [forward_iff (fun τ hτ => mixed_hasDerivAt (hX τ hτ) (hP τ hτ).ne' (hW τ hτ).ne'
    (hBM τ hτ).ne' (hB τ hτ) (hM τ hτ) (hflow τ hτ)) hint]
  have h := integral_ratio_eq (Λ := fun τ => 1 / Wm τ) (f := s) t
  have hc : ∫ τ in Set.Ioi t, Wm t / Wm τ * s τ =
      ∫ τ in Set.Ioi t, 1 / Wm τ / (1 / Wm t) * s τ := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [one_div, one_div, inv_div_inv]
  have hWt := (hW t le_rfl).ne'
  have hPt := (hP t le_rfl).ne'
  rw [hc, h]
  constructor
  · intro e; rw [← e]; field_simp
  · intro e
    rw [div_eq_iff hPt] at e
    rw [e]
    field_simp

/-- Cochrane (2023), A1 p. 569: the mixed nominal return `(Bi + Mi^m)/(B + M)` lies below `i`
when `i^m < i`, `M > 0`, `B ≥ 0`. -/
theorem mixed_rate_lt {B M i im : ℝ} (hB : 0 ≤ B) (hM : 0 < M) (him : im < i) :
    (B * i + M * im) / (B + M) < i := by
  have hpos : 0 < B + M := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

/-! ## A4 p. 635: the present-value budget constraint with consumption -/

/-- Cochrane (2023), A4 p. 635: along the flow `d(B + M) = iB + i^mM + P(y − c − s)` and
`N' = −iN` (`N = Λ/P`), `d(N(B + M)) = −NP(c − y + s + (i − i^m)M/P)`. -/
theorem budget_hasDerivAt {N B M P s c y i im : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ)
    (hBM : HasDerivAt (fun u => B u + M u)
      (i τ * B τ + im τ * M τ + P τ * (y τ - c τ - s τ)) τ) (hPτ : P τ ≠ 0) :
    HasDerivAt (fun u => N u * (B u + M u))
      (-(N τ * P τ * (c τ - y τ + s τ + (i τ - im τ) * M τ / P τ))) τ :=
  (hN.mul hBM).congr_deriv (by field_simp; ring)

/-- Cochrane (2023), A4 p. 635: **the present-value budget constraint is the present-value form of
the flow constraint.** Under `d(B + M) = iB + i^mM + P(y − c − s)` on `[0, ∞)`, `N' = −iN`,
`P > 0` and an integrable integrand, the TVC `Λ_T(B_T + M_T)/P_T → 0` holds iff
`(B_0 + M_0)/P_0 = ∫_0^∞ (Λ_t/Λ_0)(c_t − y_t + s_t + (i_t − i^m_t)M_t/P_t) dt`. -/
theorem pv_budget_iff {N B M P s c y i im : ℝ → ℝ}
    (hN : ∀ τ, 0 ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hN0 : 0 < N 0)
    (hBM : ∀ τ, 0 ≤ τ → HasDerivAt (fun u => B u + M u)
      (i τ * B τ + im τ * M τ + P τ * (y τ - c τ - s τ)) τ)
    (hP : ∀ τ, 0 ≤ τ → 0 < P τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (c τ - y τ + s τ + (i τ - im τ) * M τ / P τ))
      (Set.Ioi 0)) :
    Tendsto (fun T => N T * (B T + M T)) atTop (𝓝 0) ↔
      (B 0 + M 0) / P 0 = ∫ τ in Set.Ioi (0 : ℝ),
        N τ * P τ / (N 0 * P 0) * (c τ - y τ + s τ + (i τ - im τ) * M τ / P τ) := by
  rw [forward_iff (fun τ hτ => budget_hasDerivAt (hN τ hτ) (hBM τ hτ) (hP τ hτ).ne') hint]
  exact real_form_iff (f := fun τ => c τ - y τ + s τ + (i τ - im τ) * M τ / P τ) hN0
    (hP 0 le_rfl)

/-- Cochrane (2023), (4.5), p. 636: **the equilibrium valuation equation.** With `c = y`, the TVC
holds iff `(B_0 + M_0)/P_0 = ∫_0^∞ (Λ_t/Λ_0)(s_t + (i_t − i^m_t)M_t/P_t) dt`. -/
theorem valuation_4_5 {N B M P s y i im : ℝ → ℝ}
    (hN : ∀ τ, 0 ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hN0 : 0 < N 0)
    (hBM : ∀ τ, 0 ≤ τ → HasDerivAt (fun u => B u + M u)
      (i τ * B τ + im τ * M τ + P τ * (y τ - y τ - s τ)) τ)
    (hP : ∀ τ, 0 ≤ τ → 0 < P τ)
    (hint : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi 0)) :
    Tendsto (fun T => N T * (B T + M T)) atTop (𝓝 0) ↔
      (B 0 + M 0) / P 0 = ∫ τ in Set.Ioi (0 : ℝ),
        N τ * P τ / (N 0 * P 0) * (s τ + (i τ - im τ) * M τ / P τ) := by
  have hint' : IntegrableOn
      (fun τ => N τ * P τ * (y τ - y τ + s τ + (i τ - im τ) * M τ / P τ)) (Set.Ioi 0) :=
    hint.congr_fun (fun τ _ => by simp only; ring) measurableSet_Ioi
  rw [pv_budget_iff hN hN0 hBM hP hint']
  have : (fun τ => N τ * P τ / (N 0 * P 0) * (y τ - y τ + s τ + (i τ - im τ) * M τ / P τ)) =
      fun τ => N τ * P τ / (N 0 * P 0) * (s τ + (i τ - im τ) * M τ / P τ) := by
    funext τ
    ring
  rw [this]

/-! ## First-order conditions (4.1)–(4.4) -/

/-- Cochrane (2023), A4 p. 635: `d/dt e^{−δt} = −δe^{−δt}`. -/
theorem hasDerivAt_expDisc (δ t : ℝ) :
    HasDerivAt (fun u => Real.exp (-(δ * u))) (-δ * Real.exp (-(δ * t))) t := by
  have h1 : HasDerivAt (fun u => -(δ * u)) (-δ) t :=
    (HasDerivAt.neg ((hasDerivAt_id' t).const_mul δ)).congr_deriv (by ring)
  exact (HasDerivAt.exp h1).congr_deriv (by ring)

/-- Cochrane (2023), A4 p. 635 (chain rule): along a path `(c_t, m_t)` the marginal utility
`u_c(c_t, m_t)` has time derivative `u_cc ċ + u_cm ṁ`, where `u_cc = L(1, 0)`, `u_cm = L(0, 1)` are
the partial derivatives of `u_c` (its Fréchet derivative is `L`). -/
theorem hasDerivAt_marginal_utility {c m : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    {t dc dm : ℝ} (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t)
    (hU : HasFDerivAt Uc L (c t, m t)) :
    HasDerivAt (fun u => Uc (c u, m u)) (dc * L (1, 0) + dm * L (0, 1)) t := by
  have h := hU.comp_hasDerivAt t (hc.prodMk hm)
  have hL : L (dc, dm) = dc * L (1, 0) + dm * L (0, 1) := by
    have : ((dc, dm) : ℝ × ℝ) = dc • ((1 : ℝ), (0 : ℝ)) + dm • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [← hL]
  exact h

/-- Cochrane (2023), (4.1), p. 635: **the intertemporal first-order condition.** If the
consumption first-order condition `e^{−δt}u_c(c_t, m_t) = λΛ_t` holds along the path and
`Λ' = −rΛ`, then `−(c u_cc/u_c)(ċ/c) − (m u_cm/u_c)(ṁ/m) = r − δ`. -/
theorem foc_4_1 {c m Λ : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {δ lam t dc dm r : ℝ}
    (hfoc : ∀ u, Real.exp (-(δ * u)) * Uc (c u, m u) = lam * Λ u)
    (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t) (hU : HasFDerivAt Uc L (c t, m t))
    (hΛ : HasDerivAt Λ (-r * Λ t) t) (huc : Uc (c t, m t) ≠ 0) (hc0 : c t ≠ 0)
    (hm0 : m t ≠ 0) :
    -(c t * L (1, 0) / Uc (c t, m t)) * (dc / c t) -
        m t * L (0, 1) / Uc (c t, m t) * (dm / m t) = r - δ := by
  have hl : HasDerivAt (fun u => Real.exp (-(δ * u)) * Uc (c u, m u))
      (-δ * Real.exp (-(δ * t)) * Uc (c t, m t) +
        Real.exp (-(δ * t)) * (dc * L (1, 0) + dm * L (0, 1))) t :=
    HasDerivAt.mul (hasDerivAt_expDisc δ t) (hasDerivAt_marginal_utility hc hm hU)
  have heq : (fun u => Real.exp (-(δ * u)) * Uc (c u, m u)) = fun u => lam * Λ u :=
    funext hfoc
  rw [heq] at hl
  have hd := hl.unique (hΛ.const_mul lam)
  have hlam : lam * Λ t = Real.exp (-(δ * t)) * Uc (c t, m t) := (hfoc t).symm
  have he := (Real.exp_pos (-(δ * t))).ne'
  have key : dc * L (1, 0) + dm * L (0, 1) = (δ - r) * Uc (c t, m t) := by
    have h2 : Real.exp (-(δ * t)) * (dc * L (1, 0) + dm * L (0, 1)) =
        Real.exp (-(δ * t)) * ((δ - r) * Uc (c t, m t)) := by
      linear_combination hd - r * hlam
    exact mul_left_cancel₀ he h2
  field_simp
  linear_combination -key

/-- Cochrane (2023), (4.2) and (4.4), p. 636: **money demand.** From the consumption condition
`e^{−δt}u_c = λΛ_t` and the money condition `e^{−δt}u_m/P = λΛ_t(i − i^m)/P`,
`u_m/u_c = i − i^m`. -/
theorem foc_4_2 {e uc um lam Λ P i im : ℝ} (he : e ≠ 0) (huc : uc ≠ 0) (hP : P ≠ 0)
    (h1 : e * uc = lam * Λ) (h2 : e * um * (1 / P) = lam * Λ * (i - im) * (1 / P)) :
    um / uc = i - im := by
  rw [← h1] at h2
  field_simp at h2
  rw [h2]
  field_simp

/-- Cochrane (2023), (4.3), p. 636: **the equilibrium intertemporal condition**: with real rate
`r = i − π` (`π = Ṗ/P`) the condition (4.1) reads
`−(c u_cc/u_c)(ċ/c) − (m u_cm/u_c)(ṁ/m) = −δ + (i − π)`. -/
theorem foc_4_3 {c m Λ : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    {δ lam t dc dm i infl : ℝ}
    (hfoc : ∀ u, Real.exp (-(δ * u)) * Uc (c u, m u) = lam * Λ u)
    (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t) (hU : HasFDerivAt Uc L (c t, m t))
    (hΛ : HasDerivAt Λ (-(i - infl) * Λ t) t) (huc : Uc (c t, m t) ≠ 0) (hc0 : c t ≠ 0)
    (hm0 : m t ≠ 0) :
    -(c t * L (1, 0) / Uc (c t, m t)) * (dc / c t) -
        m t * L (0, 1) / Uc (c t, m t) * (dm / m t) = -δ + (i - infl) := by
  rw [foc_4_1 hfoc hc hm hU hΛ huc hc0 hm0]
  ring

/-! ## CES utility (pp. 636–637) -/

/-- Cochrane (2023), p. 636: the CES aggregator `c^{1−θ} + αm^{1−θ}`. -/
noncomputable def cesX (α θ c m : ℝ) : ℝ := c ^ (1 - θ) + α * m ^ (1 - θ)

/-- Cochrane (2023), p. 636: CES money-in-utility
`u(c, m) = [c^{1−θ} + αm^{1−θ}]^{(1−γ)/(1−θ)}/(1 − γ)`. -/
noncomputable def cesU (α θ γ c m : ℝ) : ℝ := cesX α θ c m ^ ((1 - γ) / (1 - θ)) / (1 - γ)

/-- Cochrane (2023), p. 636: the aggregator is positive for `c, m > 0`, `α ≥ 0`. -/
theorem cesX_pos {α θ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) : 0 < cesX α θ c m := by
  unfold cesX
  have := Real.rpow_pos_of_pos hc (1 - θ)
  have := Real.rpow_pos_of_pos hm (1 - θ)
  positivity

/-- Cochrane (2023), p. 636: **perfect substitutes**, `θ = 0`: `u = [c + αm]^{1−γ}/(1 − γ)`. -/
theorem ces_perfect_substitutes (α γ c m : ℝ) :
    cesU α 0 γ c m = (c + α * m) ^ (1 - γ) / (1 - γ) := by
  simp [cesU, cesX]

/-- Cochrane (2023), p. 636: **separable case**, `θ = γ ≠ 1`: `u = [c^{1−γ} + αm^{1−γ}]/(1 − γ)`. -/
theorem ces_separable {α γ c m : ℝ} (hγ : γ ≠ 1) :
    cesU α γ γ c m = (c ^ (1 - γ) + α * m ^ (1 - γ)) / (1 - γ) := by
  have : (1 - γ) / (1 - γ) = 1 := div_self (sub_ne_zero.2 (Ne.symm hγ))
  simp only [cesU, cesX, this, Real.rpow_one]

/-- Cochrane (2023), p. 637: `x^{1−θ} = x·x^{−θ}` for `x > 0`. -/
theorem rpow_one_sub {x : ℝ} (hx : 0 < x) (θ : ℝ) : x ^ (1 - θ) = x * x ^ (-θ) := by
  rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]

/-- Cochrane (2023), p. 637: **`u_c = [c^{1−θ} + αm^{1−θ}]^{(θ−γ)/(1−θ)} c^{−θ}`** (`c, m > 0`,
`α ≥ 0`, `θ, γ ≠ 1`). -/
theorem hasDerivAt_cesU_c {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1)
    (hγ : γ ≠ 1) :
    HasDerivAt (fun x => cesU α θ γ x m)
      (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) c := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * c ^ (1 - θ - 1)) c :=
    Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  have h2 := ((h1.add_const (α * m ^ (1 - θ))).rpow_const (p := (1 - γ) / (1 - θ))
    (Or.inl hX.ne')).div_const (1 - γ)
  refine h2.congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h1γ : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have e2 : (1 - γ) / (1 - θ) - 1 = (θ - γ) / (1 - θ) := by field_simp; ring
  rw [e1, e2]
  simp only [cesX]
  field_simp

/-- Cochrane (2023), p. 637: **`u_m = [c^{1−θ} + αm^{1−θ}]^{(θ−γ)/(1−θ)} αm^{−θ}`**. -/
theorem hasDerivAt_cesU_m {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1)
    (hγ : γ ≠ 1) :
    HasDerivAt (fun x => cesU α θ γ c x)
      (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * (α * m ^ (-θ))) m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * m ^ (1 - θ - 1)) m :=
    Real.hasDerivAt_rpow_const (Or.inl hm.ne')
  have h2 := (((h1.const_mul α).const_add (c ^ (1 - θ))).rpow_const (p := (1 - γ) / (1 - θ))
    (Or.inl hX.ne')).div_const (1 - γ)
  refine h2.congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have h1γ : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have e2 : (1 - γ) / (1 - θ) - 1 = (θ - γ) / (1 - θ) := by field_simp; ring
  rw [e1, e2]
  simp only [cesX]
  field_simp

/-- Cochrane (2023), (4.7), p. 637: **`u_m/u_c = α(m/c)^{−θ}`**. -/
theorem ces_mrs_4_7 {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    cesX α θ c m ^ ((θ - γ) / (1 - θ)) * (α * m ^ (-θ)) /
        (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) = α * (m / c) ^ (-θ) := by
  have hX := Real.rpow_pos_of_pos (cesX_pos (θ := θ) hα hc hm) ((θ - γ) / (1 - θ))
  have hcθ := Real.rpow_pos_of_pos hc (-θ)
  rw [Real.div_rpow hm.le hc.le]
  field_simp

/-- Cochrane (2023), p. 637: **`u_cc`**: the derivative of `u_c` in `c` is
`(θ − γ)X^{(θ−γ)/(1−θ) − 1}c^{−θ}c^{−θ} − θX^{(θ−γ)/(1−θ)}c^{−θ−1}` (`X = c^{1−θ} + αm^{1−θ}`). -/
theorem hasDerivAt_ucc {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1) :
    HasDerivAt (fun x => cesX α θ x m ^ ((θ - γ) / (1 - θ)) * x ^ (-θ))
      ((θ - γ) * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * c ^ (-θ) * c ^ (-θ) -
        θ * cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ - 1)) c := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * c ^ (1 - θ - 1)) c :=
    Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  have h2 := (h1.add_const (α * m ^ (1 - θ))).rpow_const (p := (θ - γ) / (1 - θ))
    (Or.inl hX.ne')
  have h3 : HasDerivAt (fun x : ℝ => x ^ (-θ)) (-θ * c ^ (-θ - 1)) c :=
    Real.hasDerivAt_rpow_const (Or.inl hc.ne')
  refine (h2.mul h3).congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  rw [e1]
  simp only [cesX]
  field_simp
  ring

/-- Cochrane (2023), p. 637: **`u_cm`**: the derivative of `u_c` in `m` is
`(θ − γ)αX^{(θ−γ)/(1−θ) − 1}m^{−θ}c^{−θ}`. -/
theorem hasDerivAt_ucm {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (hθ : θ ≠ 1) :
    HasDerivAt (fun x => cesX α θ c x ^ ((θ - γ) / (1 - θ)) * c ^ (-θ))
      ((θ - γ) * α * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * m ^ (-θ) * c ^ (-θ)) m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - θ)) ((1 - θ) * m ^ (1 - θ - 1)) m :=
    Real.hasDerivAt_rpow_const (Or.inl hm.ne')
  have h2 := (((h1.const_mul α).const_add (c ^ (1 - θ))).rpow_const (p := (θ - γ) / (1 - θ))
    (Or.inl hX.ne')).mul_const (c ^ (-θ))
  refine h2.congr_deriv ?_
  have e1 : (1 : ℝ) - θ - 1 = -θ := by ring
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  rw [e1]
  simp only [cesX]
  field_simp

/-- Cochrane (2023), p. 637: **`u_cc/u_c = (θ − γ)c^{−θ}/(c^{1−θ} + αm^{1−θ}) − θc^{−1}`**. -/
theorem ces_ucc_ratio {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    ((θ - γ) * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * c ^ (-θ) * c ^ (-θ) -
        θ * cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ - 1)) /
      (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) =
      (θ - γ) * c ^ (-θ) / cesX α θ c m - θ / c := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have hXk := Real.rpow_pos_of_pos hX ((θ - γ) / (1 - θ))
  have hcθ := Real.rpow_pos_of_pos hc (-θ)
  rw [Real.rpow_sub_one hX.ne', Real.rpow_sub_one hc.ne']
  field_simp

/-- Cochrane (2023), p. 637: **`−c u_cc/u_c = (γc^{1−θ} + θαm^{1−θ})/(c^{1−θ} + αm^{1−θ})`**. -/
theorem ces_ucc_elasticity {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    -(c * ((θ - γ) * c ^ (-θ) / cesX α θ c m - θ / c)) =
      (γ * c ^ (1 - θ) + θ * α * m ^ (1 - θ)) / cesX α θ c m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  rw [rpow_one_sub hc]
  unfold cesX
  rw [rpow_one_sub hc]
  field_simp
  ring

/-- Cochrane (2023), p. 637: in ratio form,
`−c u_cc/u_c = γ(1 + (θ/γ)α(m/c)^{1−θ})/(1 + α(m/c)^{1−θ})` (`γ ≠ 0`). -/
theorem ces_ucc_elasticity_ratio {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m)
    (hγ : γ ≠ 0) :
    (γ * c ^ (1 - θ) + θ * α * m ^ (1 - θ)) / cesX α θ c m =
      γ * (1 + θ / γ * (α * (m / c) ^ (1 - θ))) / (1 + α * (m / c) ^ (1 - θ)) := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have hcθ := Real.rpow_pos_of_pos hc (1 - θ)
  have hmθ := Real.rpow_pos_of_pos hm (1 - θ)
  rw [Real.div_rpow hm.le hc.le]
  unfold cesX at hX ⊢
  have h1 : 0 < 1 + α * (m ^ (1 - θ) / c ^ (1 - θ)) := by positivity
  field_simp

/-- Cochrane (2023), p. 637: **`m u_cm/u_c = (θ − γ)αm^{1−θ}/(c^{1−θ} + αm^{1−θ})`**. -/
theorem ces_ucm_elasticity {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    m * ((θ - γ) * α * cesX α θ c m ^ ((θ - γ) / (1 - θ) - 1) * m ^ (-θ) * c ^ (-θ)) /
        (cesX α θ c m ^ ((θ - γ) / (1 - θ)) * c ^ (-θ)) =
      (θ - γ) * α * m ^ (1 - θ) / cesX α θ c m := by
  have hX := cesX_pos (θ := θ) hα hc hm
  have hXk := Real.rpow_pos_of_pos hX ((θ - γ) / (1 - θ))
  have hcθ := Real.rpow_pos_of_pos hc (-θ)
  rw [Real.rpow_sub_one hX.ne', rpow_one_sub hm]
  field_simp

/-- Cochrane (2023), p. 637: in ratio form,
`m u_cm/u_c = (θ − γ)α(m/c)^{1−θ}/(1 + α(m/c)^{1−θ})`. -/
theorem ces_ucm_elasticity_ratio {α θ γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    (θ - γ) * α * m ^ (1 - θ) / cesX α θ c m =
      (θ - γ) * (α * (m / c) ^ (1 - θ)) / (1 + α * (m / c) ^ (1 - θ)) := by
  have hcθ := Real.rpow_pos_of_pos hc (1 - θ)
  have hmθ := Real.rpow_pos_of_pos hm (1 - θ)
  rw [Real.div_rpow hm.le hc.le]
  unfold cesX
  have h1 : 0 < 1 + α * (m ^ (1 - θ) / c ^ (1 - θ)) := by positivity
  have h2 : 0 < c ^ (1 - θ) + α * m ^ (1 - θ) := by positivity
  field_simp

/-- Cochrane (2023), p. 637 ("or, using (4.7)"): with money demand `α(m/c)^{−θ} = i − i^m`, the
interest cost satisfies `α(m/c)^{1−θ} = (m/c)(i − i^m)`; hence
`m u_cm/u_c = (θ − γ)(m/c)(i − i^m)/(1 + (m/c)(i − i^m))`. -/
theorem ces_A_eq {α θ c m ι : ℝ} (hc : 0 < c) (hm : 0 < m) (h47 : α * (m / c) ^ (-θ) = ι) :
    α * (m / c) ^ (1 - θ) = m / c * ι := by
  rw [rpow_one_sub (div_pos hm hc), ← h47]
  ring

/-! ## CES limits (E20) -/

/-- Cochrane (2023), (4.6), p. 636 (corrected): the **normalised** CES aggregator
`[(c^{1−θ} + αm^{1−θ})/(1 + α)]^{1/(1−θ)}` (a weighted power mean). -/
noncomputable def cesNorm (α θ c m : ℝ) : ℝ := (cesX α θ c m / (1 + α)) ^ (1 / (1 - θ))

/-- Cochrane (2023), (4.6), p. 636: `h ↦ log((c^h + αm^h)/(1 + α))` has derivative
`(log c + α log m)/(1 + α)` at `h = 0` (where it vanishes). -/
theorem log_mean_hasDerivAt {α c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    HasDerivAt (fun h : ℝ => Real.log ((c ^ h + α * m ^ h) / (1 + α)))
      ((Real.log c + α * Real.log m) / (1 + α)) 0 := by
  have h1 : HasDerivAt (fun h : ℝ => c ^ h) (c ^ (0 : ℝ) * Real.log c) 0 :=
    (Real.hasStrictDerivAt_const_rpow hc 0).hasDerivAt
  have h2 : HasDerivAt (fun h : ℝ => m ^ h) (m ^ (0 : ℝ) * Real.log m) 0 :=
    (Real.hasStrictDerivAt_const_rpow hm 0).hasDerivAt
  have hF : HasDerivAt (fun h : ℝ => (c ^ h + α * m ^ h) / (1 + α))
      ((c ^ (0 : ℝ) * Real.log c + α * (m ^ (0 : ℝ) * Real.log m)) / (1 + α)) 0 :=
    (HasDerivAt.add h1 (h2.const_mul α)).div_const (1 + α)
  have hα1 : (1 + α) ≠ 0 := by positivity
  have hF0 : (c ^ (0 : ℝ) + α * m ^ (0 : ℝ)) / (1 + α) = 1 := by
    simp only [Real.rpow_zero, mul_one]
    field_simp
  have hl := hF.log (by rw [hF0]; norm_num)
  refine hl.congr_deriv ?_
  rw [hF0]
  simp only [Real.rpow_zero]
  field_simp

/-- Cochrane (2023), (4.6), p. 636, **corrected (E20)**: as `θ → 1` the normalised aggregator
converges to the Cobb–Douglas index `c^{1/(1+α)} m^{α/(1+α)}` (`c, m > 0`, `α ≥ 0`). -/
theorem ces_norm_limit {α c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesNorm α θ c m) (𝓝[≠] 1)
      (𝓝 (c ^ (1 / (1 + α)) * m ^ (α / (1 + α)))) := by
  set D := (Real.log c + α * Real.log m) / (1 + α) with hD
  have hslope := (log_mean_hasDerivAt hα hc hm).tendsto_slope_zero
  have hmap : Tendsto (fun θ : ℝ => 1 - θ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
        ((continuous_const.sub continuous_id).tendsto 1)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_ne_zero.2 (Ne.symm hθ)
  have hexp := (Real.continuous_exp.tendsto D).comp (hslope.comp hmap)
  have hα1 : (1 + α) ≠ 0 := by positivity
  have hCD : c ^ (1 / (1 + α)) * m ^ (α / (1 + α)) = Real.exp D := by
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hm, ← Real.exp_add, hD]
    congr 1
    field_simp
  rw [hCD]
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have h1 : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hpos : 0 < (c ^ (1 - θ) + α * m ^ (1 - θ)) / (1 + α) := by
    have := Real.rpow_pos_of_pos hc (1 - θ)
    have := Real.rpow_pos_of_pos hm (1 - θ)
    positivity
  have hzero : Real.log ((c ^ (0 : ℝ) + α * m ^ (0 : ℝ)) / (1 + α)) = 0 := by
    simp only [Real.rpow_zero, mul_one]
    rw [div_self hα1, Real.log_one]
  simp only [Function.comp_apply, smul_eq_mul, zero_add, hzero, sub_zero]
  unfold cesNorm cesX
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  field_simp

/-- Cochrane (2023), (4.6), p. 636, **corrected (E20)**: utility built on the normalised
aggregator, `cesNorm^{1−γ}/(1 − γ)`, converges as `θ → 1` to the Cobb–Douglas utility
`[c^{1/(1+α)}m^{α/(1+α)}]^{1−γ}/(1 − γ)`. -/
theorem ces_norm_utility_limit {α γ c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesNorm α θ c m ^ (1 - γ) / (1 - γ)) (𝓝[≠] 1)
      (𝓝 ((c ^ (1 / (1 + α)) * m ^ (α / (1 + α))) ^ (1 - γ) / (1 - γ))) := by
  have hCD : 0 < c ^ (1 / (1 + α)) * m ^ (α / (1 + α)) := by
    have := Real.rpow_pos_of_pos hc (1 / (1 + α))
    have := Real.rpow_pos_of_pos hm (α / (1 + α))
    positivity
  exact ((Real.continuousAt_rpow_const _ (1 - γ) (Or.inl hCD.ne')).tendsto.comp
    (ces_norm_limit hα hc hm)).div_const _

/-- Cochrane (2023), (4.6), p. 636: the printed (un-normalised) aggregator is
`(1 + α)^{1/(1−θ)}` times the normalised one (same preferences, different cardinal scale). -/
theorem ces_unnorm_eq {α c m : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hm : 0 < m) (θ : ℝ) :
    cesX α θ c m ^ (1 / (1 - θ)) = (1 + α) ^ (1 / (1 - θ)) * cesNorm α θ c m := by
  unfold cesNorm
  have hX := cesX_pos (θ := θ) hα hc hm
  have hα1 : (0 : ℝ) < 1 + α := by positivity
  rw [← Real.mul_rpow hα1.le (div_nonneg hX.le hα1.le)]
  congr 1
  field_simp

/-- Cochrane (2023), (4.6), p. 636 (**E20**): with `α > 0` the printed aggregator
`(c^{1−θ} + αm^{1−θ})^{1/(1−θ)}` diverges to `+∞` as `θ → 1⁻`. -/
theorem ces_unnorm_diverges {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesX α θ c m ^ (1 / (1 - θ))) (𝓝[<] 1) atTop := by
  have hmap : Tendsto (fun θ : ℝ => 1 - θ) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
        ((continuous_const.sub continuous_id).tendsto 1)
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_pos.2 (Set.mem_Iio.1 hθ)
  have hinv : Tendsto (fun θ : ℝ => 1 / (1 - θ)) (𝓝[<] 1) atTop := by
    simp only [one_div]
    exact tendsto_inv_nhdsGT_zero.comp hmap
  have hpow := (tendsto_rpow_atTop_of_base_gt_one (1 + α) (by linarith)).comp hinv
  have hnorm := (ces_norm_limit hα.le hc hm).mono_left (nhdsLT_le_nhdsNE 1)
  have hCD : 0 < c ^ (1 / (1 + α)) * m ^ (α / (1 + α)) := by
    have := Real.rpow_pos_of_pos hc (1 / (1 + α))
    have := Real.rpow_pos_of_pos hm (α / (1 + α))
    positivity
  have := hpow.atTop_mul_pos hCD hnorm
  refine this.congr fun θ => ?_
  simp only [Function.comp_apply]
  exact (ces_unnorm_eq hα.le hc hm θ).symm

/-- Cochrane (2023), (4.6), p. 636 (**E20**): the printed aggregator has **no** finite limit as
`θ → 1` (`α > 0`), so the printed Cobb–Douglas limit holds only after normalising by `1 + α`. -/
theorem ces_unnorm_no_limit {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) (Lim : ℝ) :
    ¬ Tendsto (fun θ => cesX α θ c m ^ (1 / (1 - θ))) (𝓝[≠] 1) (𝓝 Lim) := by
  intro h
  exact not_tendsto_nhds_of_tendsto_atTop (ces_unnorm_diverges hα hc hm) Lim
    (h.mono_left (nhdsLT_le_nhdsNE 1))

/-- Cochrane (2023), p. 636 (**E20**): **the monetarist limit with fixed `α > 0` is `min(c, m)`**:
`(c^{1−θ} + αm^{1−θ})^{1/(1−θ)} → min(c, m)` as `θ → ∞`, not `min(c, αm)`. -/
theorem ces_limit_min {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ => cesX α θ c m ^ (1 / (1 - θ))) atTop (𝓝 (min c m)) := by
  set a := min c m with ha_def
  have ha : 0 < a := lt_min hc hm
  set k := min 1 α with hk_def
  have hk : 0 < k := lt_min one_pos hα
  have he : Tendsto (fun θ : ℝ => 1 / (1 - θ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun θ : ℝ => 1 - θ) atTop atBot :=
      (tendsto_atBot_add_const_left atTop 1
        (tendsto_neg_atTop_atBot : Tendsto (fun x : ℝ => -x) atTop atBot)).congr
        fun θ => by ring
    refine (tendsto_inv_atBot_zero.comp h1).congr fun θ => ?_
    simp only [Function.comp_apply, one_div]
  have hlim : ∀ b : ℝ, 0 < b → Tendsto (fun θ : ℝ => b ^ (1 / (1 - θ)) * a) atTop (𝓝 a) := by
    intro b hb
    have := ((Real.continuousAt_const_rpow hb.ne' (b := 0)).tendsto.comp he).mul_const a
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (1 + α) (by linarith)) (hlim k hk)
    ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with θ hθ
    have hq : 1 - θ < 0 := by linarith
    have he0 : 1 / (1 - θ) ≤ 0 := (one_div_neg.2 hq).le
    have hc' : c ^ (1 - θ) ≤ a ^ (1 - θ) := Real.rpow_le_rpow_of_nonpos ha (min_le_left c m) hq.le
    have hm' : m ^ (1 - θ) ≤ a ^ (1 - θ) := Real.rpow_le_rpow_of_nonpos ha (min_le_right c m) hq.le
    have hS : cesX α θ c m ≤ (1 + α) * a ^ (1 - θ) := by
      unfold cesX
      nlinarith
    have hX := cesX_pos (θ := θ) hα.le hc hm
    have h := Real.rpow_le_rpow_of_nonpos hX hS he0
    have hval : ((1 + α) * a ^ (1 - θ)) ^ (1 / (1 - θ)) = (1 + α) ^ (1 / (1 - θ)) * a := by
      rw [Real.mul_rpow (by linarith) (Real.rpow_pos_of_pos ha _).le, ← Real.rpow_mul ha.le,
        mul_one_div_cancel hq.ne, Real.rpow_one]
    rw [hval] at h
    exact h
  · filter_upwards [eventually_gt_atTop 1] with θ hθ
    have hq : 1 - θ < 0 := by linarith
    have he0 : 1 / (1 - θ) ≤ 0 := (one_div_neg.2 hq).le
    have haq := Real.rpow_pos_of_pos ha (1 - θ)
    have hS : k * a ^ (1 - θ) ≤ cesX α θ c m := by
      unfold cesX
      have hcq := Real.rpow_pos_of_pos hc (1 - θ)
      have hmq := Real.rpow_pos_of_pos hm (1 - θ)
      rcases le_total c m with hcm | hcm
      · have : a = c := min_eq_left hcm
        rw [this]
        have : k ≤ 1 := min_le_left 1 α
        nlinarith
      · have : a = m := min_eq_right hcm
        rw [this]
        have : k ≤ α := min_le_right 1 α
        nlinarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity) hS he0
    have hval : (k * a ^ (1 - θ)) ^ (1 / (1 - θ)) = k ^ (1 / (1 - θ)) * a := by
      rw [Real.mul_rpow hk.le haq.le, ← Real.rpow_mul ha.le, mul_one_div_cancel hq.ne,
        Real.rpow_one]
    rw [hval] at h
    exact h

/-- Cochrane (2023), p. 636: the coefficient `α^{−θ}` turns the aggregator into one with
coefficient `α^{−1}` on `(αm)^{1−θ}`: `α^{−θ}m^{1−θ} = α^{−1}(αm)^{1−θ}`. -/
theorem ces_coeff_rewrite {α m : ℝ} (hα : 0 < α) (hm : 0 < m) (θ : ℝ) :
    α ^ (-θ) * m ^ (1 - θ) = α⁻¹ * (α * m) ^ (1 - θ) := by
  rw [Real.mul_rpow hα.le hm.le, rpow_one_sub hα]
  field_simp

/-- Cochrane (2023), p. 636 (**E20**, corrected statement): to obtain the printed limit
`min(c, αm)` the coefficient on `m^{1−θ}` must be `α^{−θ}` (it must vary with `θ`):
`(c^{1−θ} + α^{−θ}m^{1−θ})^{1/(1−θ)} → min(c, αm)` as `θ → ∞`. -/
theorem ces_limit_min_corrected {α c m : ℝ} (hα : 0 < α) (hc : 0 < c) (hm : 0 < m) :
    Tendsto (fun θ : ℝ => (c ^ (1 - θ) + α ^ (-θ) * m ^ (1 - θ)) ^ (1 / (1 - θ))) atTop
      (𝓝 (min c (α * m))) := by
  have := ces_limit_min (α := α⁻¹) (inv_pos.2 hα) hc (mul_pos hα hm)
  refine this.congr fun θ => ?_
  unfold cesX
  rw [ces_coeff_rewrite hα hm]

/-- Cochrane (2023), (4.8), p. 637 (**E20**): with a fixed `α > 0` and interest differential
`i − i^m > 0`, money demand `m/c = α^{1/θ}(i − i^m)^{−1/θ}` tends to `1` as `θ → ∞`: the limit is
`M/P = c` (velocity one), not the printed `M/P = c/α`. -/
theorem demand_limit_fixed {α ι : ℝ} (hα : 0 < α) (hι : 0 < ι) :
    Tendsto (fun θ : ℝ => α ^ (1 / θ) * ι ^ (-(1 / θ))) atTop (𝓝 1) := by
  have h0 : Tendsto (fun θ : ℝ => 1 / θ) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have h0' : Tendsto (fun θ : ℝ => -(1 / θ)) atTop (𝓝 0) := by simpa using h0.neg
  have h1 := (Real.continuousAt_const_rpow hα.ne' (b := 0)).tendsto.comp h0
  have h2 := (Real.continuousAt_const_rpow hι.ne' (b := 0)).tendsto.comp h0'
  simpa using h1.mul h2

/-- Cochrane (2023), (4.7), p. 637, with the corrected coefficient `α^{−θ}` (**E20**): money
demand `α^{−θ}(m/c)^{−θ} = i − i^m` gives `m/c = α^{−1}(i − i^m)^{−1/θ}` (`θ > 0`). -/
theorem demand_corrected {α ι r θ : ℝ} (hα : 0 < α) (hr : 0 < r) (hθ : 0 < θ)
    (h : α ^ (-θ) * r ^ (-θ) = ι) : r = α⁻¹ * ι ^ (-(1 / θ)) := by
  rw [← Real.mul_rpow hα.le hr.le] at h
  have hθ0 := hθ.ne'
  have key : α * r = ι ^ (-(1 / θ)) := by
    rw [← h, ← Real.rpow_mul (by positivity)]
    have : -θ * -(1 / θ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [← key]
  field_simp

/-- Cochrane (2023), p. 636 (**E20**, corrected): with the coefficient `α^{−θ}`, money demand
`α^{−1}(i − i^m)^{−1/θ} → 1/α` as `θ → ∞`, i.e. `M/P = c/α`. -/
theorem demand_corrected_limit {α ι : ℝ} (hι : 0 < ι) :
    Tendsto (fun θ : ℝ => α⁻¹ * ι ^ (-(1 / θ))) atTop (𝓝 α⁻¹) := by
  have h00 : Tendsto (fun θ : ℝ => 1 / θ) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have h0 : Tendsto (fun θ : ℝ => -(1 / θ)) atTop (𝓝 0) := by simpa using h00.neg
  have h2 := (Real.continuousAt_const_rpow hι.ne' (b := 0)).tendsto.comp h0
  simpa using h2.const_mul α⁻¹

/-- Cochrane (2023), p. 636 ("`M_t/P_t = c_t/α`, i.e. `α = 1/V`", **E20**): with the quantity
equation `MV = Pc`, money demand `M/P = c/α` means velocity `V = α`. -/
theorem velocity_of_demand {α c M P V : ℝ} (hα : 0 < α) (hP : P ≠ 0) (hM : M ≠ 0)
    (hq : M * V = P * c) (hd : M / P = c / α) : V = α := by
  rw [div_eq_div_iff hP hα.ne'] at hd
  have : M * V = M * α := by rw [hq]; linarith
  exact mul_left_cancel₀ hM this

/-- Cochrane (2023), p. 636 (**E20**): given `V = α` (`velocity_of_demand`), the printed
`α = 1/V` holds only for `α = 1`. -/
theorem alpha_eq_inv_V_iff {α V : ℝ} (hα : 0 < α) (hV : V = α) : α = 1 / V ↔ α = 1 := by
  subst hV
  constructor
  · intro h
    field_simp at h
    nlinarith
  · intro h
    rw [h]
    norm_num

/-! ## Money demand (4.8)–(4.10) and the interest cost -/

/-- Cochrane (2023), (4.7)–(4.8), pp. 637–638: for `θ > 0`, `α, i − i^m, m/c > 0`,
`α(m/c)^{−θ} = i − i^m` iff `m/c = (1/α)^{−ξ}(i − i^m)^{−ξ}` with `ξ = 1/θ`. -/
theorem demand_4_8 {α ι r θ : ℝ} (hα : 0 < α) (hι : 0 < ι) (hr : 0 < r) (hθ : 0 < θ) :
    α * r ^ (-θ) = ι ↔ r = (1 / α) ^ (-(1 / θ)) * ι ^ (-(1 / θ)) := by
  have hθ0 := hθ.ne'
  have hinv : ∀ x : ℝ, 0 < x → (x ^ (-θ)) ^ (-(1 / θ)) = x := by
    intro x hx
    rw [← Real.rpow_mul hx.le]
    have : -θ * -(1 / θ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hinv' : ∀ x : ℝ, 0 < x → (x ^ (-(1 / θ))) ^ (-θ) = x := by
    intro x hx
    rw [← Real.rpow_mul hx.le]
    have : -(1 / θ) * -θ = 1 := by field_simp
    rw [this, Real.rpow_one]
  constructor
  · intro h
    have h1 : r ^ (-θ) = ι / α := by rw [← h]; field_simp
    have h2 := congrArg (fun x : ℝ => x ^ (-(1 / θ))) h1
    rw [hinv r hr, Real.div_rpow hι.le hα.le] at h2
    rw [h2, Real.div_rpow zero_le_one hα.le, Real.one_rpow]
    field_simp
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_pos_of_pos (by positivity) _).le
      (Real.rpow_pos_of_pos hι _).le, hinv' _ (by positivity), hinv' _ hι]
    field_simp

/-- Cochrane (2023), (4.9)–(4.10), p. 638: if `m_t/c_t = Kι_t^{−ξ}` and the steady state obeys
`m/c = Kι^{−ξ}` (`K > 0`, `ι_t, ι > 0`), then `m_t/c_t = (m/c)(ι_t/ι)^{−ξ}`, eliminating `α`. -/
theorem demand_4_10 {K ξ ιt ι rt rs : ℝ} (hι : 0 < ι) (hιt : 0 < ιt)
    (ht : rt = K * ιt ^ (-ξ)) (hs : rs = K * ι ^ (-ξ)) : rt = rs * (ιt / ι) ^ (-ξ) := by
  rw [ht, hs, Real.div_rpow hιt.le hι.le]
  have := (Real.rpow_pos_of_pos hι (-ξ)).ne'
  field_simp

/-- Cochrane (2023), p. 638: **the interest cost of holding money**: along (4.8),
`(m/c)(i − i^m) = α^ξ(i − i^m)^{1−ξ}`. -/
theorem interest_cost_formula {α ξ ι : ℝ} (hι : 0 < ι) :
    α ^ ξ * ι ^ (-ξ) * ι = α ^ ξ * ι ^ (1 - ξ) := by
  rw [rpow_one_sub hι]
  ring

/-- Cochrane (2023), p. 638: the interest cost `α^ξ(i − i^m)^{1−ξ}` (`α > 0`) tends to zero as
`i − i^m → 0⁺` **iff** `ξ < 1` (the book states the "if" direction). -/
theorem interest_cost_tendsto_iff {α ξ : ℝ} (hα : 0 < α) :
    Tendsto (fun ι : ℝ => α ^ ξ * ι ^ (1 - ξ)) (𝓝[>] 0) (𝓝 0) ↔ ξ < 1 := by
  constructor
  · intro h
    by_contra hξ
    push Not at hξ
    have hαξ := Real.rpow_pos_of_pos hα ξ
    have hev : ∀ᶠ ι in 𝓝[>] (0 : ℝ), α ^ ξ ≤ α ^ ξ * ι ^ (1 - ξ) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ι hι
      have : 1 ≤ ι ^ (1 - ξ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hι.1 hι.2.le (by linarith)
      nlinarith
    have := ge_of_tendsto h hev
    linarith
  · intro hξ
    have hc := (Real.continuousAt_rpow_const 0 (1 - ξ) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul (α ^ ξ)

/-! ## The IS curve with money (4.11)–(4.15), E21 -/

/-- Cochrane (2023), (4.11), pp. 638–639 ("prettier"): with `A = α(m/c)^{1−θ}`,
`γ(1 + (θ/γ)A)/(1 + A)·ĉ − (θ − γ)(A/(1 + A))·m̂ = γĉ + (θ − γ)(A/(1 + A))(ĉ − m̂)`. -/
theorem is_prettier {γ θ A ch mh : ℝ} (hγ : γ ≠ 0) (hA : 1 + A ≠ 0) :
    γ * (1 + θ / γ * A) / (1 + A) * ch - (θ - γ) * (A / (1 + A)) * mh =
      γ * ch + (θ - γ) * (A / (1 + A)) * (ch - mh) := by
  field_simp
  ring

/-- Cochrane (2023), (4.12), p. 639: dividing (4.11) by `γ` (`σ = 1/γ`, `ξ = 1/θ`):
`ĉ + ((σ − ξ)/ξ)(A/(1 + A))(ĉ − m̂) = −δσ + σ(i − π)`. -/
theorem is_4_12 {γ θ A ch mh δ i infl : ℝ} (hγ : γ ≠ 0) (hθ : θ ≠ 0) (hA : 1 + A ≠ 0)
    (h411 : γ * (1 + θ / γ * A) / (1 + A) * ch - (θ - γ) * (A / (1 + A)) * mh =
      -δ + (i - infl)) :
    ch + (1 / γ - 1 / θ) / (1 / θ) * (A / (1 + A)) * (ch - mh) =
      -δ * (1 / γ) + 1 / γ * (i - infl) := by
  rw [is_prettier hγ hA] at h411
  have key : ch + (1 / γ - 1 / θ) / (1 / θ) * (A / (1 + A)) * (ch - mh) -
      (-δ * (1 / γ) + 1 / γ * (i - infl)) =
      1 / γ * (γ * ch + (θ - γ) * (A / (1 + A)) * (ch - mh) - (-δ + (i - infl))) := by
    field_simp
  rw [h411, sub_self, mul_zero] at key
  linarith

/-- Cochrane (2023), p. 639 (differentiating the money-demand curve): along
`m_t/c_t = Kι_t^{−ξ}` (`ι = i − i^m`) with differentiable positive paths,
`ċ/c − ṁ/m = ξ ι̇/ι`. -/
theorem demand_log_deriv {m c ι : ℝ → ℝ} {K ξ t dm dc dι : ℝ}
    (hdem : ∀ u, m u / c u = K * ι u ^ (-ξ)) (hm : HasDerivAt m dm t) (hc : HasDerivAt c dc t)
    (hι : HasDerivAt ι dι t) (hm0 : 0 < m t) (hc0 : 0 < c t) (hι0 : 0 < ι t) :
    dc / c t - dm / m t = ξ * (dι / ι t) := by
  have h1 : HasDerivAt (fun u => m u / c u) ((dm * c t - m t * dc) / c t ^ 2) t :=
    hm.div hc hc0.ne'
  have h2 : HasDerivAt (fun u => K * ι u ^ (-ξ)) (K * (dι * (-ξ) * ι t ^ (-ξ - 1))) t :=
    (hι.rpow_const (Or.inl hι0.ne')).const_mul K
  have heq : (fun u => m u / c u) = fun u => K * ι u ^ (-ξ) := funext hdem
  rw [heq] at h1
  have hd := h1.unique h2
  have hK : m t / c t = K * ι t ^ (-ξ) := hdem t
  rw [Real.rpow_sub_one hι0.ne'] at hd
  have hr : K * (dι * -ξ * (ι t ^ (-ξ) / ι t)) = m t / c t * (dι * -ξ / ι t) := by
    rw [hK]
    ring
  rw [hr] at hd
  have hm1 := hm0.ne'
  have hc1 := hc0.ne'
  have hι1 := hι0.ne'
  have key : dc / c t - dm / m t - ξ * (dι / ι t) =
      -(c t / m t) * ((dm * c t - m t * dc) / c t ^ 2 - m t / c t * (dι * -ξ / ι t)) := by
    field_simp
    ring
  rw [hd, sub_self, mul_zero] at key
  linarith

/-- Cochrane (2023), p. 639, `x = log c`: `ẋ = ċ/c`. -/
theorem log_consumption_deriv {c : ℝ → ℝ} {t dc : ℝ} (hc : HasDerivAt c dc t) (hc0 : 0 < c t) :
    HasDerivAt (fun u => Real.log (c u)) (dc / c t) t :=
  hc.log hc0.ne'

/-- Cochrane (2023), p. 639, **the exact IS curve with money (E21)**: from (4.12), the
money-demand relation `ĉ − m̂ = ξι̇/ι` and `A = (m/c)ι`,
`ĉ + (σ − ξ)((m/c)/(1 + A))ι̇ = σ(i − π − δ)`; the book's last display and (4.13) drop `−δσ`. -/
theorem is_exact {σ ξ ch mh ι dι mc A δ i infl : ℝ} (hξ : ξ ≠ 0) (hι : ι ≠ 0)
    (hA : 1 + A ≠ 0) (hAdef : A = mc * ι)
    (h412 : ch + (σ - ξ) / ξ * (A / (1 + A)) * (ch - mh) = -δ * σ + σ * (i - infl))
    (hdem : ch - mh = ξ * (dι / ι)) :
    ch + (σ - ξ) * (mc / (1 + A)) * dι = σ * (i - infl - δ) := by
  rw [hdem] at h412
  have key : ch + (σ - ξ) * (mc / (1 + A)) * dι - σ * (i - infl - δ) =
      ch + (σ - ξ) / ξ * (A / (1 + A)) * (ξ * (dι / ι)) - (-δ * σ + σ * (i - infl)) := by
    rw [hAdef] at hA ⊢
    field_simp
    ring
  rw [h412, sub_self] at key
  linarith

/-- Cochrane (2023), (4.11)–(4.13), pp. 638–639: **the IS curve with money, exact form**,
assembled: from (4.11) (i.e. (4.3) with the CES elasticities `ces_ucc_elasticity_ratio`,
`ces_ucm_elasticity_ratio`) and the money-demand derivative,
`ĉ + (σ − ξ)((m/c)/(1 + (m/c)(i − i^m)))·d(i − i^m)/dt = σ(i − π − δ)` with `σ = 1/γ`,
`ξ = 1/θ`. -/
theorem is_curve_exact {γ θ ch mh mc ι dι δ i infl : ℝ} (hγ : γ ≠ 0) (hθ : θ ≠ 0)
    (hι : ι ≠ 0) (hA : 1 + mc * ι ≠ 0)
    (h411 : γ * (1 + θ / γ * (mc * ι)) / (1 + mc * ι) * ch -
      (θ - γ) * (mc * ι / (1 + mc * ι)) * mh = -δ + (i - infl))
    (hdem : ch - mh = 1 / θ * (dι / ι)) :
    ch + (1 / γ - 1 / θ) * (mc / (1 + mc * ι)) * dι = 1 / γ * (i - infl - δ) :=
  is_exact (by positivity) hι hA rfl (is_4_12 hγ hθ hA h411) hdem

/-- Cochrane (2023), (4.13), p. 639 (first-order approximation): for any `K` differentiable at
`ῑ`, the term `K(ι)ι̇` has derivative `(dι, dι̇) ↦ K(ῑ)dι̇` at the steady state `(ῑ, 0)`: to first
order the coefficient on `d(i − i^m)/dt` is its steady-state value
`K(ῑ) = (m/c)/(1 + (m/c)(i − i^m))`. -/
theorem first_order_term {K : ℝ → ℝ} {K' ι0 : ℝ} (hK : HasDerivAt K K' ι0) :
    HasFDerivAt (fun p : ℝ × ℝ => K p.1 * p.2) (K ι0 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (ι0, 0) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => K p.1) (K' • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (ι0, 0) := hK.comp_hasFDerivAt (ι0, 0) (hasFDerivAt_fst)
  have h2 := h1.mul (hasFDerivAt_snd (p := ((ι0, 0) : ℝ × ℝ)))
  convert h2 using 1
  ext <;> simp

/-- Cochrane (2023), (4.8), (4.13), p. 639: along money demand, the coefficient
`K(ι) = (m/c)(ι)/(1 + (m/c)(ι)ι)` with `(m/c)(ι) = α^ξι^{−ξ}` is differentiable at every
`ῑ > 0` (`α > 0`), so `first_order_term` applies. -/
theorem coefficient_differentiable {α ξ ι0 : ℝ} (hα : 0 < α) (hι : 0 < ι0) :
    DifferentiableAt ℝ (fun ι => α ^ ξ * ι ^ (-ξ) / (1 + α ^ ξ * ι ^ (-ξ) * ι)) ι0 := by
  have hr : DifferentiableAt ℝ (fun ι : ℝ => ι ^ (-ξ)) ι0 :=
    (Real.hasDerivAt_rpow_const (Or.inl hι.ne')).differentiableAt
  have hden : 1 + α ^ ξ * ι0 ^ (-ξ) * ι0 ≠ 0 := by
    have := Real.rpow_pos_of_pos hα ξ
    have := Real.rpow_pos_of_pos hι (-ξ)
    positivity
  exact (hr.const_mul _).div (((hr.const_mul _).mul differentiableAt_id).const_add 1) hden

/-- Cochrane (2023), (4.13), p. 639 ("approximating that the interest cost is small"): dropping
`1 + A` from the coefficient changes it by `(m/c)A/(1 + A) ∈ [0, (m/c)A]`, first order in the
interest cost `A = (m/c)(i − i^m)`. -/
theorem coefficient_gap {mc A : ℝ} (hmc : 0 ≤ mc) (hA : 0 ≤ A) :
    0 ≤ mc - mc / (1 + A) ∧ mc - mc / (1 + A) ≤ mc * A := by
  have h1 : (0 : ℝ) < 1 + A := by linarith
  have heq : mc - mc / (1 + A) = mc * A / (1 + A) := by field_simp; ring
  rw [heq]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h1]
  nlinarith [mul_nonneg hmc hA]

/-- Cochrane (2023), (4.13), p. 639 (**E21**): at a steady state of the exact IS curve
(`ẋ = 0`, `ι̇ = 0`) the real rate is `i − π = δ`, so the printed (4.13) `ẋ + … = σ(i − π)`, which
would force `i = π`, fails there whenever `σδ ≠ 0`. -/
theorem E21_steady_state {σ ξ mc A i infl δ : ℝ} (hσ : σ ≠ 0) (hδ : δ ≠ 0)
    (hexact : (0 : ℝ) + (σ - ξ) * (mc / (1 + A)) * 0 = σ * (i - infl - δ)) :
    ¬ ((0 : ℝ) + (σ - ξ) * mc * 0 = σ * (i - infl)) := by
  intro hp
  simp only [mul_zero, add_zero] at hexact hp
  have h1 : i - infl - δ = 0 := by
    rcases mul_eq_zero.1 hexact.symm with h | h
    · exact absurd h hσ
    · exact h
  have h2 : i - infl = 0 := by
    rcases mul_eq_zero.1 hp.symm with h | h
    · exact absurd h hσ
    · exact h
  exact hδ (by linarith)

/-- Cochrane (2023), (4.13), p. 639 (**E21**, the repair): measured as deviations from a steady
state with `ī − π̄ = δ`, `σ(i − π − δ) = σ((i − ī) − (π − π̄))`, so (4.13) is correct only for
`i, π` read as deviations. -/
theorem E21_deviations {σ i infl δ ib πb : ℝ} (hss : ib - πb = δ) :
    σ * (i - infl - δ) = σ * ((i - ib) - (infl - πb)) := by
  rw [← hss]
  ring

/-- Cochrane (2023), (4.14), p. 640 (**E21**): in terms of `x = log c` and `m̃ = log m`, (4.12)
reads exactly `ẋ + ((σ − ξ)/ξ)(A/(1 + A))(ẋ − dm̃/dt) = σ(i − π − δ)`; (4.14) replaces
`A/(1 + A)` by `A = (m/c)(i − i^m)` and drops `−δσ`. -/
theorem is_4_14_exact {c m : ℝ → ℝ} {t dc dm dx dmt σ ξ A δ i infl : ℝ}
    (hc : HasDerivAt c dc t) (hm : HasDerivAt m dm t) (hc0 : 0 < c t) (hm0 : 0 < m t)
    (hx : HasDerivAt (fun u => Real.log (c u)) dx t)
    (hmt : HasDerivAt (fun u => Real.log (m u)) dmt t)
    (h412 : dc / c t + (σ - ξ) / ξ * (A / (1 + A)) * (dc / c t - dm / m t) =
      -δ * σ + σ * (i - infl)) :
    dx + (σ - ξ) / ξ * (A / (1 + A)) * (dx - dmt) = σ * (i - infl - δ) := by
  rw [hx.unique (hc.log hc0.ne'), hmt.unique (hm.log hm0.ne'), h412]
  ring

/-- Cochrane (2023), (4.14), p. 640: replacing `A/(1 + A)` by `A` is a second-order change:
`0 ≤ A − A/(1 + A) ≤ A²` for `A ≥ 0`. -/
theorem A_ratio_gap {A : ℝ} (hA : 0 ≤ A) : 0 ≤ A - A / (1 + A) ∧ A - A / (1 + A) ≤ A ^ 2 := by
  have := coefficient_gap (mc := A) hA hA
  rw [sq]
  exact this

/-- Cochrane (2023), pp. 639–640 (**E21**, (4.15)): in the separable case `σ = ξ` the book's
discrete-time version of (4.13) reads `E_tx_{t+1} − x_t = σ(i_t − E_tπ_{t+1})` while (4.15) reads
`E_tx_{t+1} − x_t = σ(i_t − π_t)`; both hold only if `E_tπ_{t+1} = π_t`. So (4.15) should use
`E_tπ_{t+1}`. -/
theorem E21_discrete_inconsistent {σ ξ k k' Ex1 x dι dm i infl Einfl1 : ℝ} (hσξ : σ = ξ)
    (hσ : σ ≠ 0) (h413d : Ex1 - x + (σ - ξ) * k * dι = σ * (i - Einfl1))
    (h415 : Ex1 - x + (σ - ξ) / ξ * k' * ((Ex1 - x) - dm) = σ * (i - infl)) :
    Einfl1 = infl := by
  subst hσξ
  simp only [sub_self, zero_mul, zero_div, add_zero] at h413d h415
  rw [h413d] at h415
  have : σ * (infl - Einfl1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hσ
  · linarith

/-! ## The Hamiltonian approach (4.16)–(4.17) -/

/-- Cochrane (2023), (4.16), p. 640: from `dM = (y − c − s)P dt` and `m = M/P`,
`ṁ = (y − c − s) − mṖ/P`. -/
theorem constraint_4_16 {M P : ℝ → ℝ} {t dP y c s : ℝ}
    (hM : HasDerivAt M ((y - c - s) * P t) t) (hP : HasDerivAt P dP t) (hP0 : P t ≠ 0) :
    HasDerivAt (fun u => M u / P u) ((y - c - s) - M t / P t * (dP / P t)) t :=
  (hM.div hP hP0).congr_deriv (by field_simp)

/-- Cochrane (2023), p. 640: **money demand from the Hamiltonian first-order conditions**
`u'(c) = µ` and `µ̇ − δµ = −v'(m) + µṖ/P`: `v'(m)/u'(c) = −µ̇/µ + δ + Ṗ/P`. -/
theorem hamiltonian_money_demand {up vp μ dμ δ infl : ℝ} (h1 : up = μ)
    (h2 : dμ - δ * μ = -vp + μ * infl) (hμ : μ ≠ 0) :
    vp / up = -dμ / μ + δ + infl := by
  rw [h1]
  field_simp
  linarith

/-- Cochrane (2023), p. 640: with the real rate `r = δ − µ̇/µ` (consumption Euler equation) and
the Fisher relation `i = r + Ṗ/P`, the Hamiltonian money demand is `v'(m)/u'(c) = i`. -/
theorem hamiltonian_eq_i {up vp μ dμ δ infl r i : ℝ} (h1 : up = μ)
    (h2 : dμ - δ * μ = -vp + μ * infl) (hμ : μ ≠ 0) (hr : r = δ - dμ / μ) (hi : i = r + infl) :
    vp / up = i := by
  rw [hamiltonian_money_demand h1 h2 hμ, hi, hr]
  ring

/-- Cochrane (2023), p. 640: with constant consumption the costate `µ = u'(c̄)` is constant, so
`µ̇ = 0` and the real rate is `r = δ − µ̇/µ = δ`. -/
theorem constant_consumption_rate {μ : ℝ → ℝ} {up dμ t δ : ℝ} (hμ : ∀ u, μ u = up)
    (hd : HasDerivAt μ dμ t) : dμ = 0 ∧ δ - dμ / μ t = δ := by
  have hfun : μ = fun _ => up := funext hμ
  rw [hfun] at hd
  have h0 := hd.unique (hasDerivAt_const t up)
  refine ⟨h0, ?_⟩
  rw [h0, zero_div, sub_zero]

/-- Cochrane (2023), (4.17), pp. 640–641: with `µ_t = u'(c_t)` the Hamiltonian transversality
condition `e^{−δt}m_tµ_t → 0` is the condition `e^{−δt}u'(c_t)m_t → 0`. -/
theorem tvc_4_17_iff {m μ c up : ℝ → ℝ} {δ : ℝ} (hμ : ∀ t, μ t = up (c t)) :
    Tendsto (fun t => Real.exp (-(δ * t)) * m t * μ t) atTop (𝓝 0) ↔
      Tendsto (fun t => Real.exp (-(δ * t)) * up (c t) * m t) atTop (𝓝 0) := by
  have : (fun t => Real.exp (-(δ * t)) * m t * μ t) =
      fun t => Real.exp (-(δ * t)) * up (c t) * m t := by
    funext t
    rw [hμ t]
    ring
  rw [this]

end Cochrane.Monetarism.ContinuousTime
