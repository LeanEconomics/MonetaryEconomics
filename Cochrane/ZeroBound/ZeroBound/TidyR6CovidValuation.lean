/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.Covid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The nonlinear helicopter `P = B/S` and the linearised valuation equation

Cochrane (2023), Chapter 21, pp. 487–491 (the fiscal helicopter, partial backing and "bad fiscal
news can only affect unexpected inflation"), with the frictionless valuation equation of §2
(`B_{t}/P_{t+1} = E_{t+1}∑βʲs_{t+1+j}`, eq. (2.4)–(2.5), pp. 22–23) and its linearisation
`π_{t+1} − E_tπ_{t+1} = −ε_{t+1}` ((3.17)/(5.13); `Covid.fiscal_news_only_unexpected`).

`Covid` treats the helicopter in levels, `P = B/S` (`Covid.priceLevel`), and `Links` only the
frictionless limit of the sticky-price impact coefficient (`Links.fiscal_impact_frictionless`).
Here the nonlinear valuation equation itself is linearised, for an arbitrary `ExpectationSystem`.

## Main results

* `NonlinValuation`: `B_t/P_{t+1} = S_{t+1}` with `S_{t+1} = ∑βʲE_{t+1}s_{t+1+j}` a genuine sum.
* **Exact relation** (`unexpected_log_inflation`): unexpected log inflation is minus the news in
  the log present value of surpluses, `π_{t+1} − E_tπ_{t+1} = −(log S_{t+1} − E_t log S_{t+1})`,
  with no approximation.
* The linearised news `ε_{t+1} = (S_{t+1} − E_tS_{t+1})/E_tS_{t+1}` (`relNews`) is a news
  shock, `E_tε_{t+1} = 0` (`E_relNews`), and **the linearisation with explicit remainder**
  (`linearisation_remainder`): `π_{t+1} − E_tπ_{t+1} = −ε_{t+1} + R_{t+1}`, where
  `R = q(ε) − E_tq(ε)`, `q(x) = x − log(1 + x)`, and `0 ≤ q(x) ≤ x²/(1 + x)` (`q_bounds`), so
  `−E_t[ε²/(1 + ε)] ≤ R ≤ ε²/(1 + ε)` (`remainder_bounds`). The linear term is the exact
  derivative (`hasDerivAt_neg_log`), the remainder is second order (`q_isBigO`), and the linear
  valuation equation holds exactly for the corrected news `ε − R` (`linear_valuation_exact`).
* The hypotheses (pull-out, functions of known variables are known) hold under perfect foresight
  and on every finite event tree (`perfectForesight_knownFns`, `finiteTree_knownFns`); under
  perfect foresight the remainder vanishes (`perfectForesight_remainder_zero`).
* The helicopter (pp. 488, 490): debt `(1 + Δ)B`, surpluses `(1 + fΔ)S` are fiscal news
  `ε_h = −(1 − f)Δ/(1 + Δ)` per unit of debt (`helicopter_news`); the price ratio is exactly
  `1/(1 + ε_h)` (`priceRatio_eq_news`), its log is `−log(1 + ε_h)` (`log_priceRatio`), the
  linearised valuation equation predicts `−ε_h` with remainder `q(ε_h)` (`helicopter_remainder`),
  and to first order in `Δ` both agree with `(1 − f)Δ` (`hasDerivAt_neg_news`). At the book's
  numbers: linear `1/13`, exact log `log(13/12)`, level `1/12` (`helicopter_book_numbers`).
-/

namespace Cochrane.ZeroBound.TidyR6CovidValuation

open Filter Topology Asymptotics
open Cochrane.ZeroBound

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ## The nonlinear valuation equation -/

/-- Cochrane (2023), eqs. (2.4)–(2.5), pp. 22–23, as used on p. 487: the frictionless valuation
equation for one-period nominal debt `B_t` maturing at `t + 1`, `B_t/P_{t+1} = S_{t+1}`, where
`S_{t+1} = ∑_{j ≥ 0} βʲ E_{t+1}s_{t+1+j}` is the present value of real surpluses (a genuine
`HasSum`). -/
def NonlinValuation (β : ℝ) (B P S s : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, HasSum (fun j => β ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) ω) (S (t + 1) ω)) ∧
    ∀ t ω, B t ω / P (t + 1) ω = S (t + 1) ω

/-- Cochrane (2023), p. 487: log inflation `π_{t+1} = log P_{t+1} − log P_t`. -/
noncomputable def logInfl (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => Real.log (P (t + 1) ω) - Real.log (P t ω)

/-- Cochrane (2023), p. 487: the valuation equation in logs, `log P_{t+1} = log B_t − log S_{t+1}`
(positive debt and surpluses). -/
theorem log_price_eq {β : ℝ} {B P S s : ℕ → Ω → ℝ} (h : NonlinValuation 𝔼 β B P S s)
    (hB : ∀ t ω, 0 < B t ω) (hP : ∀ t ω, 0 < P t ω) (t : ℕ) (ω : Ω) :
    Real.log (P (t + 1) ω) = Real.log (B t ω) - Real.log (S (t + 1) ω) := by
  rw [← h.2 t ω, Real.log_div (hB t ω).ne' (hP (t + 1) ω).ne']
  ring

/-- Cochrane (2023), p. 491 ("bad fiscal news can only affect unexpected inflation"), exact
nonlinear form: if `log B_t` and `log P_t` are known at `t`, unexpected log inflation is minus
the news in the log present value of surpluses,
`π_{t+1} − E_tπ_{t+1} = −(log S_{t+1} − E_t log S_{t+1})`, for any `ExpectationSystem`. -/
theorem unexpected_log_inflation {β : ℝ} {B P S s : ℕ → Ω → ℝ}
    (h : NonlinValuation 𝔼 β B P S s) (hB : ∀ t ω, 0 < B t ω) (hP : ∀ t ω, 0 < P t ω) (t : ℕ)
    (hBk : 𝔼.E t (fun ω => Real.log (B t ω)) = fun ω => Real.log (B t ω))
    (hPk : 𝔼.E t (fun ω => Real.log (P t ω)) = fun ω => Real.log (P t ω)) :
    logInfl P t - 𝔼.E t (logInfl P t) =
      -((fun ω => Real.log (S (t + 1) ω)) - 𝔼.E t (fun ω => Real.log (S (t + 1) ω))) := by
  have e : logInfl P t = (fun ω => Real.log (B t ω)) - (fun ω => Real.log (S (t + 1) ω)) -
      (fun ω => Real.log (P t ω)) := by
    funext ω
    simp only [logInfl, Pi.sub_apply, log_price_eq 𝔼 h hB hP t ω]
  rw [e, map_sub, map_sub, hBk, hPk]
  abel

/-! ## Linearisation with an explicit remainder -/

/-- Cochrane (2023), p. 491: the property that a function of a variable known at `t` is known
at `t` (true for every `σ`-algebra; for the abstract `ExpectationSystem` it is an extra
hypothesis, like `ExpectationSystem.PullOut`). -/
def KnownFns : Prop :=
  ∀ t (a : Ω → ℝ) (g : ℝ → ℝ), 𝔼.E t a = a → 𝔼.E t (fun ω => g (a ω)) = fun ω => g (a ω)

/-- Cochrane (2023), p. 491: perfect foresight satisfies `KnownFns`. -/
theorem perfectForesight_knownFns : KnownFns perfectForesight := fun _ _ _ _ => rfl

/-- Cochrane (2023), p. 491: every finite event tree satisfies `KnownFns` (a variable known at
`t` is constant on date-`t` cells, so is any function of it). -/
theorem finiteTree_knownFns {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : KnownFns T.toExpectationSystem := by
  intro t a g ha
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at ha ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have : a ω' = a ω := by rw [← ha, T.condE_congr a h]
  rw [this]

/-- Cochrane (2023), (5.13) and p. 491: the linearised fiscal news, the surprise in the present
value of surpluses relative to its expected value, `ε_{t+1} = S_{t+1}/E_tS_{t+1} − 1`. -/
noncomputable def relNews (S : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => S (t + 1) ω / 𝔼.E t (S (t + 1)) ω - 1

/-- Cochrane (2023), p. 491: the linearised news is a news shock, `E_tε_{t+1} = 0` (pull-out of
the known `1/E_tS_{t+1}`, with `E_tS_{t+1} > 0`). -/
theorem E_relNews (hPO : 𝔼.PullOut) (hK : KnownFns 𝔼) {S : ℕ → Ω → ℝ} (t : ℕ)
    (hV : ∀ ω, 0 < 𝔼.E t (S (t + 1)) ω) : 𝔼.E t (relNews 𝔼 S t) = 0 := by
  set V := 𝔼.E t (S (t + 1))
  have hVk : 𝔼.E t V = V := 𝔼.E_E_self t _
  have hinv : 𝔼.E t (fun ω => (V ω)⁻¹) = fun ω => (V ω)⁻¹ := hK t V (fun x => x⁻¹) hVk
  have e : relNews 𝔼 S t = (fun ω => (V ω)⁻¹) * S (t + 1) - fun _ => 1 := by
    funext ω
    simp only [relNews, Pi.mul_apply, Pi.sub_apply, V]
    ring
  rw [e, map_sub, hPO t _ _ hinv, 𝔼.const]
  funext ω
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply]
  rw [inv_mul_cancel₀ (hV ω).ne', sub_self]

/-- Cochrane (2023), p. 491: the second-order term `q(x) = x − log(1 + x)` of the log
linearisation. -/
noncomputable def q (x : ℝ) : ℝ := x - Real.log (1 + x)

/-- Cochrane (2023), p. 491: for `x > −1`, `0 ≤ q(x) ≤ x²/(1 + x)` (from
`x/(1 + x) ≤ log(1 + x) ≤ x`). -/
theorem q_bounds {x : ℝ} (hx : -1 < x) : 0 ≤ q x ∧ q x ≤ x ^ 2 / (1 + x) := by
  have h1 : 0 < 1 + x := by linarith
  have hu := Real.log_le_sub_one_of_pos h1
  have hl := Real.one_sub_inv_le_log_of_pos h1
  unfold q
  refine ⟨by linarith, ?_⟩
  have e : x ^ 2 / (1 + x) = x - (1 - (1 + x)⁻¹) := by
    field_simp
    ring
  rw [e]
  linarith

/-- Cochrane (2023), p. 491: the linear term is the exact derivative of `−log(1 + ε)` at the
steady state `ε = 0`: `d/dε[−log(1 + ε)] = −1`. -/
theorem hasDerivAt_neg_log : HasDerivAt (fun ε : ℝ => -Real.log (1 + ε)) (-1) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => 1 + ε) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add 1
  have h3 : HasDerivAt (fun ε : ℝ => -Real.log (1 + ε)) (-(1 / (1 + 0))) 0 :=
    (h1.log (by norm_num)).neg
  simpa using h3

/-- Cochrane (2023), p. 491: the remainder is second order, `q(ε) = O(ε²)` as `ε → 0`. -/
theorem q_isBigO : q =O[𝓝 0] fun x : ℝ => x ^ 2 := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [Ioo_mem_nhds (show (-1 / 2 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
  obtain ⟨h0, h1⟩ := q_bounds (show -1 < x by linarith [hx.1])
  have hpos : 1 / 2 ≤ 1 + x := by linarith [hx.1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (sq_nonneg x)]
  calc q x ≤ x ^ 2 / (1 + x) := h1
    _ ≤ x ^ 2 / (1 / 2) := div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) hpos
    _ = 2 * x ^ 2 := by ring

/-- Cochrane (2023), p. 491: the remainder of the linearised valuation equation,
`R_{t+1} = q(ε_{t+1}) − E_tq(ε_{t+1})`. -/
noncomputable def remainder (S : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun ω => q (relNews 𝔼 S t ω)) - 𝔼.E t (fun ω => q (relNews 𝔼 S t ω))

/-- Cochrane (2023), p. 491 and (5.13): **the linearisation of the nonlinear valuation equation
with explicit remainder.** Under pull-out and `KnownFns`, with positive debt, prices and present
values, `log B_t`, `log P_t` known at `t` and `E_tS_{t+1} > 0`:
`π_{t+1} − E_tπ_{t+1} = −ε_{t+1} + R_{t+1}`. -/
theorem linearisation_remainder (hPO : 𝔼.PullOut) (hK : KnownFns 𝔼) {β : ℝ}
    {B P S s : ℕ → Ω → ℝ} (h : NonlinValuation 𝔼 β B P S s) (hB : ∀ t ω, 0 < B t ω)
    (hP : ∀ t ω, 0 < P t ω) (hS : ∀ t ω, 0 < S t ω) (t : ℕ)
    (hBk : 𝔼.E t (fun ω => Real.log (B t ω)) = fun ω => Real.log (B t ω))
    (hPk : 𝔼.E t (fun ω => Real.log (P t ω)) = fun ω => Real.log (P t ω))
    (hV : ∀ ω, 0 < 𝔼.E t (S (t + 1)) ω) :
    logInfl P t - 𝔼.E t (logInfl P t) = -relNews 𝔼 S t + remainder 𝔼 S t := by
  set V := 𝔼.E t (S (t + 1))
  have hVk : 𝔼.E t V = V := 𝔼.E_E_self t _
  have hlogV : 𝔼.E t (fun ω => Real.log (V ω)) = fun ω => Real.log (V ω) :=
    hK t V Real.log hVk
  have hε := E_relNews 𝔼 hPO hK t hV
  -- `log S = log V + ε − q(ε)`
  have hsplit : (fun ω => Real.log (S (t + 1) ω)) = (fun ω => Real.log (V ω)) +
      relNews 𝔼 S t - fun ω => q (relNews 𝔼 S t ω) := by
    funext ω
    have h1 : 1 + relNews 𝔼 S t ω = S (t + 1) ω / V ω := by
      simp only [relNews, V]; ring
    simp only [Pi.add_apply, Pi.sub_apply, q, h1]
    rw [Real.log_div (hS (t + 1) ω).ne' (hV ω).ne']
    ring
  rw [unexpected_log_inflation 𝔼 h hB hP t hBk hPk, hsplit, map_sub, map_add, hlogV, hε,
    remainder]
  abel

/-- Cochrane (2023), p. 491: explicit bounds on the remainder,
`−E_t[ε²/(1 + ε)] ≤ R_{t+1} ≤ ε²/(1 + ε)` (here `ε > −1` since `S, E_tS > 0`). -/
theorem remainder_bounds {S : ℕ → Ω → ℝ} (t : ℕ) (hS : ∀ t ω, 0 < S t ω)
    (hV : ∀ ω, 0 < 𝔼.E t (S (t + 1)) ω) (ω : Ω) :
    -𝔼.E t (fun ω => relNews 𝔼 S t ω ^ 2 / (1 + relNews 𝔼 S t ω)) ω ≤ remainder 𝔼 S t ω ∧
      remainder 𝔼 S t ω ≤ relNews 𝔼 S t ω ^ 2 / (1 + relNews 𝔼 S t ω) := by
  have hgt : ∀ ω, -1 < relNews 𝔼 S t ω := fun ω => by
    have : 0 < S (t + 1) ω / 𝔼.E t (S (t + 1)) ω := div_pos (hS _ ω) (hV ω)
    simp only [relNews]; linarith
  have hq0 : (0 : Ω → ℝ) ≤ fun ω => q (relNews 𝔼 S t ω) := fun ω => (q_bounds (hgt ω)).1
  have hq1 : (fun ω => q (relNews 𝔼 S t ω)) ≤
      fun ω => relNews 𝔼 S t ω ^ 2 / (1 + relNews 𝔼 S t ω) := fun ω => (q_bounds (hgt ω)).2
  have m0 := 𝔼.mono t hq0 ω
  have m1 := 𝔼.mono t hq1 ω
  rw [map_zero] at m0
  simp only [Pi.zero_apply] at m0
  simp only [remainder, Pi.sub_apply]
  constructor
  · linarith [(q_bounds (hgt ω)).1]
  · linarith [(q_bounds (hgt ω)).2]

/-- Cochrane (2023), p. 491 and `Covid.fiscal_news_only_unexpected`: the linear valuation
equation `π_{t+1} − E_tπ_{t+1} = −ε̃_{t+1}` holds exactly for the corrected news
`ε̃ = ε − R`, which is itself a news shock, `E_tε̃_{t+1} = 0`. -/
theorem linear_valuation_exact (hPO : 𝔼.PullOut) (hK : KnownFns 𝔼) {β : ℝ}
    {B P S s : ℕ → Ω → ℝ} (h : NonlinValuation 𝔼 β B P S s) (hB : ∀ t ω, 0 < B t ω)
    (hP : ∀ t ω, 0 < P t ω) (hS : ∀ t ω, 0 < S t ω) (t : ℕ)
    (hBk : 𝔼.E t (fun ω => Real.log (B t ω)) = fun ω => Real.log (B t ω))
    (hPk : 𝔼.E t (fun ω => Real.log (P t ω)) = fun ω => Real.log (P t ω))
    (hV : ∀ ω, 0 < 𝔼.E t (S (t + 1)) ω) :
    logInfl P t - 𝔼.E t (logInfl P t) = -(relNews 𝔼 S t - remainder 𝔼 S t) ∧
      𝔼.E t (relNews 𝔼 S t - remainder 𝔼 S t) = 0 := by
  refine ⟨by rw [linearisation_remainder 𝔼 hPO hK h hB hP hS t hBk hPk hV]; abel, ?_⟩
  rw [map_sub, E_relNews 𝔼 hPO hK t hV, remainder, map_sub, 𝔼.E_E_self, sub_self, sub_zero]

/-- Cochrane (2023), p. 491: under perfect foresight there is no news, so the remainder
vanishes. -/
theorem perfectForesight_remainder_zero {S : ℕ → Unit → ℝ} (t : ℕ) :
    remainder perfectForesight S t = 0 := by
  funext ω
  simp [remainder, perfectForesight]

/-! ## The helicopter drop (pp. 488, 490) -/

/-- Cochrane (2023), p. 488: the fiscal news of a helicopter with debt `(1 + Δ)B` and surpluses
`(1 + fΔ)S`, measured as the change in surplus backing per unit of nominal debt,
`ε_h = (1 + fΔ)/(1 + Δ) − 1`. -/
noncomputable def heliNews (f Δ : ℝ) : ℝ := (1 + f * Δ) / (1 + Δ) - 1

/-- Cochrane (2023), p. 488: `ε_h = −(1 − f)Δ/(1 + Δ)`. -/
theorem helicopter_news {f Δ : ℝ} (hΔ : 1 + Δ ≠ 0) : heliNews f Δ = -((1 - f) * Δ / (1 + Δ)) := by
  unfold heliNews
  field_simp
  ring

/-- Cochrane (2023), p. 488: the exact helicopter price ratio is `1/(1 + ε_h)`. -/
theorem priceRatio_eq_news {f Δ : ℝ} (hΔ : 1 + Δ ≠ 0) :
    Covid.priceRatio f Δ = 1 / (1 + heliNews f Δ) := by
  unfold Covid.priceRatio heliNews
  field_simp
  ring_nf

/-- Cochrane (2023), p. 488: exact log price change, `log(P′/P) = −log(1 + ε_h)`. -/
theorem log_priceRatio {f Δ : ℝ} (hΔ : 1 + Δ ≠ 0) :
    Real.log (Covid.priceRatio f Δ) = -Real.log (1 + heliNews f Δ) := by
  rw [priceRatio_eq_news hΔ, one_div, Real.log_inv]

/-- Cochrane (2023), p. 488: the linearised valuation equation predicts the log price change
`−ε_h`; the exact log change exceeds it by `q(ε_h) ∈ [0, ε_h²/(1 + ε_h)]`. -/
theorem helicopter_remainder {f Δ : ℝ} (hΔ : 0 < 1 + Δ) (hf : 0 < 1 + f * Δ) :
    Real.log (Covid.priceRatio f Δ) = -heliNews f Δ + q (heliNews f Δ) ∧
      0 ≤ q (heliNews f Δ) ∧
      q (heliNews f Δ) ≤ heliNews f Δ ^ 2 / (1 + heliNews f Δ) := by
  have hgt : -1 < heliNews f Δ := by
    unfold heliNews
    have : 0 < (1 + f * Δ) / (1 + Δ) := div_pos hf hΔ
    linarith
  refine ⟨?_, (q_bounds hgt).1, (q_bounds hgt).2⟩
  rw [log_priceRatio hΔ.ne', q]
  ring

/-- Cochrane (2023), p. 488: to first order in `Δ`, the linearised prediction `−ε_h` agrees with
the book's `(1 − f)Δ` (`Covid.hasDerivAt_priceRatio`): `d(−ε_h)/dΔ = 1 − f` at `Δ = 0`. -/
theorem hasDerivAt_neg_news (f : ℝ) : HasDerivAt (fun Δ => -heliNews f Δ) (1 - f) 0 := by
  have h1 : HasDerivAt (fun Δ : ℝ => 1 + f * Δ) f 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul f).const_add 1
  have h2 : HasDerivAt (fun Δ : ℝ => 1 + Δ) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add 1
  have h := ((h1.div h2 (by norm_num)).sub_const 1).neg
  unfold heliNews
  convert h using 1
  simp

/-- Cochrane (2023), p. 488 (survey error E10): at two-thirds backing of 30% new debt the news
is `ε_h = −1/13`; the linearised valuation equation gives `1/13` (7.7%), the exact price ratio
is `13/12` (8.33% in levels, `log(13/12)` in logs), and the first-order term in `Δ` is `1/10`. -/
theorem helicopter_book_numbers :
    heliNews (2 / 3) (3 / 10) = -1 / 13 ∧ Covid.priceRatio (2 / 3) (3 / 10) = 13 / 12 ∧
      Real.log (Covid.priceRatio (2 / 3) (3 / 10)) = Real.log (13 / 12) ∧
      -heliNews (2 / 3) (3 / 10) < Real.log (13 / 12) ∧
      Real.log (13 / 12) < 13 / 12 - 1 ∧ (13 / 12 : ℝ) - 1 < (1 - 2 / 3) * (3 / 10) := by
  have hn : heliNews (2 / 3) (3 / 10) = -1 / 13 := by unfold heliNews; norm_num
  have hp : Covid.priceRatio (2 / 3) (3 / 10) = 13 / 12 := by
    unfold Covid.priceRatio; norm_num
  have hr := helicopter_remainder (f := 2 / 3) (Δ := 3 / 10) (by norm_num) (by norm_num)
  have hq : 0 < q (-1 / 13) := by
    unfold q
    have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 + -1 / 13 by norm_num)
      (by norm_num)
    linarith
  have hlog : Real.log (13 / 12 : ℝ) < 13 / 12 - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  refine ⟨hn, hp, by rw [hp], ?_, hlog, by norm_num⟩
  rw [← hp, hr.1, hn]
  linarith

end Cochrane.ZeroBound.TidyR6CovidValuation
