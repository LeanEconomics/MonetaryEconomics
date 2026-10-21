/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.ContinuousLinear

/-!
# Money in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.4, pp. 79–80, and
Online Appendix A1.6, pp. 567–569.

Deterministic paths. Nominal debt `B` and money `M` are differentiable with derivatives `dB`,
`dM`; the nominal flow condition (3.52)/(1.31) is `dM = iB + i^m M − Ps − dB`. Discounting uses a
*nominal* discount factor `N = Λ/P` with `N' = −iN` (the definition of the nominal rate, A1
(1.26)); the real discount factor is `Λ = NP`. The price level need not be differentiable: only
`N` (or `PW`) is, as A1 p. 568 remarks.

* (3.52)/(1.31) in real terms.
* (1.32)–(1.33), (3.53): `B_t/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + dM_τ/P_τ) dτ` **iff** the TVC
  `Λ_T B_T/P_T → 0` (`i^m = 0`).
* (1.34), (3.54): `(M_t + B_t)/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` iff the TVC on
  `M + B`.
* The two are equivalent iff the money TVC `Λ_T M_T/P_T → 0` holds; an explicit path satisfies
  (3.53) but not (3.54).
* (1.35)–(1.36): ex-post discounting with the cumulative return `W` (`(PW)' = i PW`),
  `B/P = ∫ (W_t/W_τ)(s + dM/P)` and `(B+M)/P = ∫ (W_t/W_τ)(s + (i_τ − i^m_τ)M_τ/P_τ)`; with the
  printed index `(i_t − i^m_t)` (E21) the formula is false (explicit counterexample).
* (1.37), (3.55): with the mixed portfolio return `W^m`, `(B+M)/P = ∫ (W^m_t/W^m_τ) s dτ`.
-/

namespace Cochrane.Generality.ContinuousMoney

open Filter Topology MeasureTheory
open Cochrane.Generality.ContinuousLinear

/-! ## The flow condition and discount factors -/

/-- Cochrane (2023), (3.52), p. 79 and A1 (1.31), p. 567: the nominal flow condition
`dM = iB + i^m M − Ps − dB` in real terms:
`(B/P) i + (M/P) i^m = s + dB/P + dM/P`. -/
theorem flow_real {B M P s i im dB dM : ℝ} (hP : P ≠ 0)
    (hflow : dM = i * B + im * M - P * s - dB) :
    B / P * i + M / P * im = s + dB / P + dM / P := by
  rw [hflow]
  field_simp
  ring

/-- Cochrane (2023), A1 (1.26), p. 564: with a real discount factor `Λ' = −rΛ` and inflation
`P' = πP`, the nominal discount factor `Λ/P` obeys `(Λ/P)' = −(r + π)(Λ/P)`: the nominal rate is
`i = r + π`. (The constant-rate case of `ContinuousShort.hasDerivAt_nominal_discount`.) -/
theorem nominal_discount_of_real {Λ P : ℝ → ℝ} {r infl τ : ℝ}
    (hΛ : HasDerivAt Λ (-r * Λ τ) τ) (hP : HasDerivAt P (infl * P τ) τ) (hPτ : P τ ≠ 0) :
    HasDerivAt (fun u => Λ u / P u) (-(r + infl) * (Λ τ / P τ)) τ :=
  ContinuousShort.hasDerivAt_nominal_discount (i := fun _ => r + infl)
    (hΛ.congr_deriv (by field_simp; ring)) hP hPτ

/-- Cochrane (2023), A1 (1.35), p. 568: if the nominal value of the short-term bond portfolio
`X = PW` grows at `i` (`X' = iX`), then `1/(PW)` is a nominal discount factor:
`(1/X)' = −i (1/X)` (`ContinuousShort.hasDerivAt_inv_price` with `X' = iX`). -/
theorem inv_nominal_value {X : ℝ → ℝ} {i τ : ℝ} (hX : HasDerivAt X (i * X τ) τ) (hXτ : X τ ≠ 0) :
    HasDerivAt (fun u => 1 / X u) (-i * (1 / X τ)) τ :=
  (ContinuousShort.hasDerivAt_inv_price hX hXτ).congr_deriv (by field_simp)

/-- Cochrane (2023), A1 p. 568: with `Λ = NP` and `N = 1/(PW)`, `Λ_τ/Λ_t = W_t/W_τ`. -/
theorem lambda_ratio_eq_W {P W : ℝ → ℝ} {t τ : ℝ} (hPt : P t ≠ 0) (hPτ : P τ ≠ 0)
    (hWt : W t ≠ 0) (hWτ : W τ ≠ 0) :
    (1 / (P τ * W τ) * P τ) / (1 / (P t * W t) * P t) = W t / W τ := by
  field_simp

/-- Cochrane (2023), (3.31), A1.6, pp. 74, 567: the forward-integration step in "iff" form:
if `G' = −h` on `[t, ∞)` and `h` is integrable on `(t, ∞)`, then `G_T → 0` iff
`G_t = ∫_t^∞ h`. -/
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

/-- Cochrane (2023), (3.53), A1 (1.33): converting `N_t X_t = ∫_t^∞ Λ f` (with `Λ = NP`) into
`X_t/P_t = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`. -/
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

/-! ## (3.53): seigniorage as money creation -/

/-- Cochrane (2023), A1 (1.32), p. 567: with `i^m = 0`, along the flow condition the discounted
real debt obeys `d(N B) = −N P (s + dM/P) dt`. -/
theorem printing_hasDerivAt {N B P s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * B u) (-(N τ * P τ * (s τ + dM τ / P τ))) τ :=
  (hN.mul hB).congr_deriv (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), (3.53), p. 79 and A1 (1.33), p. 567: **seigniorage as money creation.**
With `i^m = 0`, nominal discount `N' = −iN` (`Λ = NP`), the flow (3.52) on `[t, ∞)` and
`Λ(s + dM/P)` integrable: the TVC `Λ_T B_T/P_T → 0` holds iff
`B_t/P_t = ∫_t^∞ (Λ_τ/Λ_t)(s_τ + dM_τ/P_τ) dτ`. -/
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

/-! ## (3.54): seigniorage as interest saving -/

/-- Cochrane (2023), A1 p. 567: along the flow (3.52) with interest on money,
`d(N(M + B)) = −N P (s + (i − i^m) M/P) dt`. -/
theorem interest_hasDerivAt {N B M P s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hN : HasDerivAt N (-(i τ) * N τ) τ) (hB : HasDerivAt B (dB τ) τ)
    (hM : HasDerivAt M (dM τ) τ) (hPτ : P τ ≠ 0)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => N u * (M u + B u))
      (-(N τ * P τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  (hN.mul (HasDerivAt.add hM hB)).congr_deriv
    (by rw [hflow]; try simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), (3.54), p. 79 and A1 (1.34), p. 567: **seigniorage as interest saving.**
With money paying `i^m`, the TVC `Λ_T(M_T + B_T)/P_T → 0` holds iff
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

/-- Cochrane (2023), §3.6.4 and A1.6 (continuous analogue of E13): with `i^m = 0`, if the
money-creation valuation (3.53) holds, then the interest-saving valuation (3.54) holds **iff**
the money transversality condition `Λ_T M_T/P_T → 0` holds. -/
theorem printing_interest_iff_money_tvc {N B M P s i dB dM : ℝ → ℝ} {t : ℝ}
    (hN : ∀ τ, t ≤ τ → HasDerivAt N (-(i τ) * N τ) τ) (hNt : 0 < N t)
    (hB : ∀ τ, t ≤ τ → HasDerivAt B (dB τ) τ) (hM : ∀ τ, t ≤ τ → HasDerivAt M (dM τ) τ)
    (hP : ∀ τ, t ≤ τ → 0 < P τ)
    (hflow : ∀ τ, t ≤ τ → dM τ = i τ * B τ - P τ * s τ - dB τ)
    (hint1 : IntegrableOn (fun τ => N τ * P τ * (s τ + dM τ / P τ)) (Set.Ioi t))
    (hint2 : IntegrableOn (fun τ => N τ * P τ * (s τ + (i τ - 0) * M τ / P τ)) (Set.Ioi t))
    (h353 : B t / P t = ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + dM τ / P τ)) :
    (M t + B t) / P t =
        ∫ τ in Set.Ioi t, N τ * P τ / (N t * P t) * (s τ + (i τ - 0) * M τ / P τ) ↔
      Tendsto (fun T => N T * M T) atTop (𝓝 0) := by
  have hBtvc := (money_printing_iff hN hNt hB hP hflow hint1).2 h353
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

/-- Cochrane (2023), §3.6.4 and A1.6 (E13 analogue): the two valuation equations are **not**
equivalent without the money TVC. With `P ≡ 1`, `i ≡ ι` (any `ι`, e.g. `ι > 0`), `i^m = 0`,
`N_τ = e^{−ιτ}`, no bonds, `M_τ = e^{ιτ}` and `s_τ = −ι e^{ιτ}` (money-financed deficits), the
flow (3.52) holds, the money-creation valuation (3.53) holds (`0 = 0`), but the interest-saving
valuation (3.54) fails (`e^{ιt} ≠ 0`). -/
theorem printing_without_interest_example (ι t : ℝ) :
    let N : ℝ → ℝ := fun τ => Real.exp (-(ι * τ))
    let M : ℝ → ℝ := fun τ => Real.exp (ι * τ)
    let s : ℝ → ℝ := fun τ => -(ι * Real.exp (ι * τ))
    (∀ τ, HasDerivAt N (-ι * N τ) τ) ∧ (∀ τ, HasDerivAt M (ι * M τ) τ) ∧
      (∀ τ, ι * M τ = ι * 0 + 0 * M τ - 1 * s τ - 0) ∧
      (0 : ℝ) / 1 = ∫ τ in Set.Ioi t, N τ * 1 / (N t * 1) * (s τ + ι * M τ / 1) ∧
      (M t + 0) / 1 ≠ ∫ τ in Set.Ioi t, N τ * 1 / (N t * 1) * (s τ + (ι - 0) * M τ / 1) := by
  intro N M s
  have hzero : ∀ τ, s τ + ι * M τ / 1 = 0 := fun τ => by simp only [s, M]; ring
  have hzero' : ∀ τ, s τ + (ι - 0) * M τ / 1 = 0 := fun τ => by simp only [s, M]; ring
  refine ⟨fun τ => hasDerivAt_expDisc ι τ, fun τ => ?_, fun τ => by simp only [s]; ring,
    ?_, ?_⟩
  · exact (HasDerivAt.exp ((hasDerivAt_id' τ).const_mul ι)).congr_deriv (by simp only [M]; ring)
  · simp only [hzero, mul_zero, integral_zero]
    norm_num
  · simp only [hzero', mul_zero, integral_zero]
    simp only [M, add_zero, div_one]
    exact (Real.exp_pos _).ne'

/-! ## (1.35)–(1.36): ex-post discounting with the cumulative return `W` -/

/-- Cochrane (2023), A1 (1.36), p. 568: with `i^m = 0`, if the nominal value `PW` of the
short-term bond portfolio grows at `i`, then `d(B/(PW)) = −(1/W)(s + dM/P) dt`; the price level
itself need not be differentiable. -/
theorem printing_W_hasDerivAt {P W B s i dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ)
    (hflow : dM τ = i τ * B τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * B u) (-(1 / W τ * (s τ + dM τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul hB).congr_deriv
    (by rw [hflow]; field_simp; ring)

/-- Cochrane (2023), §3.6.4, p. 79 and A1 (1.36), p. 568: **ex-post discounting, money
creation.** With `(PW)' = i PW`, `i^m = 0`, the flow (3.52) and `(s + dM/P)/W` integrable, the TVC
`B_T/(P_T W_T) → 0` holds iff `B_t/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + dM_τ/P_τ) dτ`. -/
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

/-- Cochrane (2023), A1 p. 568: along the flow with interest on money,
`d((B + M)/(PW)) = −(1/W)(s + (i − i^m)M/P) dt`. -/
theorem interest_W_hasDerivAt {P W B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * W u) (i τ * (P τ * W τ)) τ) (hPτ : P τ ≠ 0)
    (hWτ : W τ ≠ 0) (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * W u) * (B u + M u))
      (-(1 / W τ * (s τ + (i τ - im τ) * M τ / P τ))) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; try simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), §3.6.4, p. 79 and A1 p. 568: **ex-post discounting, interest saving.**
The TVC `(B_T + M_T)/(P_T W_T) → 0` holds iff
`(B_t + M_t)/P_t = ∫_t^∞ (W_t/W_τ)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` (integrand dated `τ`; the book
prints `(i_t − i^m_t)`, E21, see `printed_index_counterexample`). -/
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

/-- Cochrane (2023), p. 79 and A1 p. 568 (E21): the printed integrand `(i_t − i^m_t)M_τ/P_τ`
(rate dated `t`) is wrong. With `P ≡ 1`, `i ≡ 1`, `W_τ = e^τ`, `B ≡ 0`, `M ≡ 1`, `i^m_τ = e^{−τ}`
and `s = i^m` the flow (3.52) holds, `(B_0 + M_0)/P_0 = 1` equals the correctly dated integral,
while the printed one equals `1/2`. -/
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

/-! ## (1.37), (3.55): the mixed bond-and-money portfolio return -/

/-- Cochrane (2023), (3.55), p. 80 and A1 (1.37), p. 569: if the nominal value `PW^m` of the
whole government portfolio grows at the mixed rate `(Bi + Mi^m)/(B + M)`, then along the flow
`d((B + M)/(PW^m)) = −(s/W^m) dt`. -/
theorem mixed_hasDerivAt {P Wm B M s i im dB dM : ℝ → ℝ} {τ : ℝ}
    (hX : HasDerivAt (fun u => P u * Wm u)
      ((B τ * i τ + M τ * im τ) / (B τ + M τ) * (P τ * Wm τ)) τ)
    (hPτ : P τ ≠ 0) (hWτ : Wm τ ≠ 0) (hBM : B τ + M τ ≠ 0)
    (hB : HasDerivAt B (dB τ) τ) (hM : HasDerivAt M (dM τ) τ)
    (hflow : dM τ = i τ * B τ + im τ * M τ - P τ * s τ - dB τ) :
    HasDerivAt (fun u => 1 / (P u * Wm u) * (B u + M u)) (-(1 / Wm τ * s τ)) τ :=
  ((inv_nominal_value hX (mul_ne_zero hPτ hWτ)).mul (HasDerivAt.add hB hM)).congr_deriv
    (by rw [hflow]; try simp only [Pi.add_apply]; field_simp; ring)

/-- Cochrane (2023), (3.55), p. 80 and A1 (1.37), p. 569: **valuation with the mixed portfolio
return.** With `(PW^m)' = ((Bi + Mi^m)/(B + M)) PW^m`, `B + M > 0`, the flow (3.52) and `s/W^m`
integrable, the TVC `(B_T + M_T)/(P_T W^m_T) → 0` holds iff
`(B_t + M_t)/P_t = ∫_t^∞ (W^m_t/W^m_τ) s_τ dτ`: seigniorage is folded into the discount rate. -/
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

/-- Cochrane (2023), §3.6.4, p. 80: the mixed nominal return `(Bi + Mi^m)/(B + M)` lies below
the bond rate `i` when `i^m < i` and `M > 0`, `B ≥ 0`: money lets the government borrow at
lower rates. -/
theorem mixed_rate_lt {B M i im : ℝ} (hB : 0 ≤ B) (hM : 0 < M) (him : im < i) :
    (B * i + M * im) / (B + M) < i := by
  have hpos : 0 < B + M := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith

end Cochrane.Generality.ContinuousMoney
