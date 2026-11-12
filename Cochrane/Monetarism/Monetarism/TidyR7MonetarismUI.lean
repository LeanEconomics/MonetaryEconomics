/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismValuation
import Mathlib.Probability.Distributions.Geometric

/-!
# The domination hypothesis of `E_t∫_t^∞` cannot be dropped

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eq. (1.33).
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_dom` reads `∫_s^∞` as the pathwise
limit `G` of the flows `F_T = ∫_s^T Λs dr + ∫_s^T n dM` and assumes `|F_{T_k}| ≤ H` integrable;
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33` assumes
`F_T → G` in `L¹`. Without such a hypothesis the limit form
`lim E_s∫_s^T = n_sB_s` (`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq`) still holds,
but the literal `n_sB_s = E_s[∫_s^∞]` can fail.

## The model (`uiModel`)

`Ω = ℕ` with the geometric law `P(ω) = 2^{−(ω+1)}` (Mathlib `geometricMeasure`), all information
revealed just after time `0` (`uiFilt`). `Λ = P = 1`, `i = i^m = 0`, `M = 0`. With the hat function
`φ_ω` centred at `ω + 1` (`hat`, support `(ω, ω + 2)`, `Σ_ω φ_ω(T) = 1` for `T ≥ 1`, `tsum_hat`),
bonds are `B_u(ω) = 1 − 2^{ω+1}φ_ω(u)` (`uiB`) and the surplus is `s = −Ḃ` (`uiSur`): in state `ω`
the government runs a deficit and then a surplus of size `2^{ω+1}` around time `ω + 1`.

## Results

* `ui_flow`: `F_T(ω) = 2^{ω+1}φ_ω(T)`; `ui_EF`: `E_0[F_T] = Σ_ω φ_ω(T) = 1` for `T ≥ 1`.
* `ui_tvc`: `E_0[n_TB_T] = 0` for `T ≥ 1` (transversality holds); `ui_limit`: so
  `lim E_0[F_T] = 1 = n_0B_0` (the limit form of (1.33) holds).
* `ui_pathwise`: `F_T(ω) → 0` for every `ω`, so `G = ∫_0^∞ Λs = 0` path by path, and
  `ui_literal_fails`: `n_0B_0 = 1 ≠ 0 = E_0[G]`.
* `ui_dom`, `ui_integrable`: all other hypotheses of `MonetaryModel.valuation_1_33_dom` hold (the
product-step
  domination on every `[0, T]`, integrability of `n_TB_T`, measurability, pathwise convergence).
* `ui_not_dominated`: hence no integrable `H` dominates the flows (else
`MonetaryModel.valuation_1_33_dom` would
  give `n_0B_0 = E_0[G]`); `ui_not_L1`: the flows do not converge in `L¹`.
* `ui_headline`: all of the above together.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismUI

open MeasureTheory Filter Topology ProbabilityTheory
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation

/-! ## The probability space -/

/-- Cochrane (2023), A1 §1.6, p. 567 (counterexample): the parameter `1/2`. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Cochrane (2023), A1 §1.6, p. 567: `P(ω) = 2^{−(ω+1)}` on `ℕ`. -/
noncomputable abbrev uiMeasure : Measure ℕ := geometricMeasure half

/-- Cochrane (2023), A1 §1.6, p. 567: `1/2 ≠ 0`. -/
theorem half_ne_zero : half ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  norm_num [half] at this

/-- Cochrane (2023), A1 §1.6, p. 567: the state is revealed just after time `0`. -/
noncomputable def uiFilt : Filtration ℝ (inferInstance : MeasurableSpace ℕ) where
  seq u := if u ≤ 0 then ⊥ else inferInstance
  mono' i j hij := by
    by_cases hj : j ≤ 0
    · have hi : i ≤ 0 := hij.trans hj
      simp only [hi, hj, ↓reduceIte, le_refl]
    · by_cases hi : i ≤ 0
      · simp only [hi, hj, ↓reduceIte]
        exact bot_le
      · simp only [hi, hj, ↓reduceIte, le_refl]
  le' u := by
    by_cases hu : u ≤ 0
    · simp only [hu, ↓reduceIte]
      exact bot_le
    · simp only [hu, ↓reduceIte, le_refl]

/-- Cochrane (2023), A1 §1.6, p. 567: at time `0` the filtration is trivial. -/
theorem uiFilt_zero : uiFilt 0 = ⊥ := by
  change (if (0 : ℝ) ≤ 0 then ⊥ else (inferInstance : MeasurableSpace ℕ)) = _
  simp

/-- Cochrane (2023), A1 §1.6, p. 567: after time `0` the filtration is everything. -/
theorem uiFilt_pos {u : ℝ} (hu : ¬ u ≤ 0) : uiFilt u = (inferInstance : MeasurableSpace ℕ) := by
  change (if u ≤ 0 then ⊥ else (inferInstance : MeasurableSpace ℕ)) = _
  simp only [hu, ↓reduceIte]

/-- Cochrane (2023), A1 §1.6, p. 567: `E_0` is the expectation.
From Mathlib `condExp_bot`. -/
theorem condExp_ui_zero (f : ℕ → ℝ) : uiMeasure[f | uiFilt 0] = fun _ => ∫ ω, f ω ∂uiMeasure := by
  rw [uiFilt_zero, condExp_bot]

/-- Cochrane (2023), A1 §1.6, p. 567: a process that is non-random up to time `0` is adapted. -/
theorem ui_adapted {f : ℝ → ℕ → ℝ} (hf : ∀ u ≤ 0, ∀ ω, f u ω = f u 0) (u : ℝ) :
    StronglyMeasurable[uiFilt u] (f u) := by
  by_cases hu : u ≤ 0
  · have e : f u = fun _ => f u 0 := funext fun ω => hf u hu ω
    rw [e]
    exact stronglyMeasurable_const
  · rw [uiFilt_pos hu]
    exact (measurable_of_countable _).stronglyMeasurable

/-- Cochrane (2023), A1 §1.6, p. 567: the integral against `P(ω) = 2^{−(ω+1)}` of
`2^{ω+1}g(ω)` is `Σ g`. From Mathlib `integral_geometricMeasure`. -/
theorem integral_ui_wt (g : ℕ → ℝ) :
    ∫ ω, (2 : ℝ) ^ (ω + 1) * g ω ∂uiMeasure = ∑' ω, g ω := by
  rw [integral_geometricMeasure half_ne_zero]
  congr 1
  funext n
  have h : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  simp only [half, smul_eq_mul]
  rw [pow_succ]
  calc (1 - 1 / 2 : ℝ) ^ n * (1 / 2) * (2 ^ n * 2 * g n)
      = ((1 / 2 : ℝ) ^ n * 2 ^ n) * g n := by ring
    _ = g n := by rw [h, one_mul]

/-! ## Hat functions and steps -/

/-- Cochrane (2023), A1 §1.6, p. 567: the step `1{r > c}`.
Generalises `TidyR7MonetarismCoin.stepG`. -/
noncomputable def stepAt (c r : ℝ) : ℝ := if c < r then 1 else 0

/-- Cochrane (2023), A1 §1.6, p. 567: the step is monotone.
Generalises `TidyR7MonetarismCoin.monotone_stepG`. -/
theorem monotone_stepAt (c : ℝ) : Monotone (stepAt c) := by
  intro x y hxy
  simp only [stepAt]
  split_ifs with h1 h2 <;> (try simp only [not_lt] at *) <;> linarith

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_u^v 1{r > c} dr = (v − c)⁺ − (u − c)⁺`.
Generalises `TidyR7MonetarismCoin.integral_stepG`. -/
theorem integral_stepAt (c : ℝ) {u v : ℝ} (huv : u ≤ v) :
    ∫ r in u..v, stepAt c r = max (v - c) 0 - max (u - c) 0 := by
  have hii : ∀ a b, IntervalIntegrable (stepAt c) MeasureSpace.volume a b := fun _ _ =>
    (monotone_stepAt c).intervalIntegrable
  have h0 : ∀ a b : ℝ, a ≤ b → b ≤ c → ∫ r in a..b, stepAt c r = 0 := by
    intro a b hab hb
    have e : ∫ r in a..b, stepAt c r = ∫ _ in a..b, (0 : ℝ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        simp only [stepAt, not_lt.2 (hr.2.trans hb), ↓reduceIte])
    rw [e, intervalIntegral.integral_zero]
  have h1 : ∀ a b : ℝ, a ≤ b → c ≤ a → ∫ r in a..b, stepAt c r = b - a := by
    intro a b hab ha
    have e : ∫ r in a..b, stepAt c r = ∫ _ in a..b, (1 : ℝ) :=
      intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        simp only [stepAt, show c < r from lt_of_le_of_lt ha hr.1, ↓reduceIte])
    rw [e, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  rcases le_total v c with hv | hv
  · rw [h0 u v huv hv, max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · rcases le_total c u with hu | hu
    · rw [h1 u v huv hu, max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    · rw [← intervalIntegral.integral_add_adjacent_intervals (b := c) (hii u c) (hii c v),
        h0 u c hu le_rfl, h1 c v hv le_rfl, max_eq_left (by linarith), max_eq_right (by linarith)]
      ring

/-- Cochrane (2023), A1 §1.6, p. 567: the hat `φ_c(x) = (x − c)⁺ − 2(x − c − 1)⁺ + (x − c − 2)⁺`,
centred at `c + 1` with support `(c, c + 2)`. -/
noncomputable def hat (c x : ℝ) : ℝ :=
  max (x - c) 0 - 2 * max (x - (c + 1)) 0 + max (x - (c + 2)) 0

/-- Cochrane (2023), A1 §1.6, p. 567: the density of the hat. -/
noncomputable def hatD (c r : ℝ) : ℝ := stepAt c r - 2 * stepAt (c + 1) r + stepAt (c + 2) r

/-- Cochrane (2023), A1 §1.6, p. 567: `φ_c(x) = 0` for `x ≤ c`. -/
theorem hat_of_le {c x : ℝ} (h : x ≤ c) : hat c x = 0 := by
  simp only [hat]
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `φ_c(x) = x − c` on `[c, c + 1]`. -/
theorem hat_of_mid1 {c x : ℝ} (h1 : c ≤ x) (h2 : x ≤ c + 1) : hat c x = x - c := by
  simp only [hat]
  rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `φ_c(x) = c + 2 − x` on `[c + 1, c + 2]`. -/
theorem hat_of_mid2 {c x : ℝ} (h1 : c + 1 ≤ x) (h2 : x ≤ c + 2) : hat c x = c + 2 - x := by
  simp only [hat]
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `φ_c(x) = 0` for `x ≥ c + 2`. -/
theorem hat_of_ge {c x : ℝ} (h : c + 2 ≤ x) : hat c x = 0 := by
  simp only [hat]
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `0 ≤ φ_c ≤ 1`. -/
theorem hat_mem (c x : ℝ) : 0 ≤ hat c x ∧ hat c x ≤ 1 := by
  rcases le_total x c with h | h
  · rw [hat_of_le h]; norm_num
  rcases le_total x (c + 1) with h' | h'
  · rw [hat_of_mid1 h h']; constructor <;> linarith
  rcases le_total x (c + 2) with h'' | h''
  · rw [hat_of_mid2 h' h'']; constructor <;> linarith
  · rw [hat_of_ge h'']; norm_num

/-- Cochrane (2023), A1 §1.6, p. 567: the hat is continuous. -/
theorem continuous_hat (c : ℝ) : Continuous (hat c) := by
  unfold hat
  fun_prop

/-- Cochrane (2023), A1 §1.6, p. 567: `φ_c(v) − φ_c(u) = ∫_u^v φ_c'`. -/
theorem hat_incr (c : ℝ) {u v : ℝ} (huv : u ≤ v) :
    hat c v - hat c u = ∫ r in u..v, hatD c r := by
  have hi : ∀ d, IntervalIntegrable (stepAt d) MeasureSpace.volume u v := fun d =>
    (monotone_stepAt d).intervalIntegrable
  simp only [hatD]
  rw [intervalIntegral.integral_add ((hi c).sub ((hi (c + 1)).const_mul 2)) (hi (c + 2)),
    intervalIntegral.integral_sub (hi c) ((hi (c + 1)).const_mul 2),
    intervalIntegral.integral_const_mul, integral_stepAt c huv, integral_stepAt (c + 1) huv,
    integral_stepAt (c + 2) huv]
  simp only [hat]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: the density is integrable. -/
theorem intervalIntegrable_hatD (c u v : ℝ) :
    IntervalIntegrable (hatD c) MeasureSpace.volume u v :=
  (((monotone_stepAt c).intervalIntegrable).sub
    (((monotone_stepAt (c + 1)).intervalIntegrable).const_mul 2)).add
    (monotone_stepAt (c + 2)).intervalIntegrable

/-- Cochrane (2023), A1 §1.6, p. 567: `|φ_c'| ≤ 4`, and `φ_c' = 0` on `(−∞, c]`. -/
theorem abs_hatD_le (c r : ℝ) : |hatD c r| ≤ 4 ∧ (r ≤ c → hatD c r = 0) := by
  have hs : ∀ d, |stepAt d r| ≤ 1 := fun d => by
    simp only [stepAt]; split_ifs <;> norm_num
  refine ⟨?_, fun h => ?_⟩
  · simp only [hatD]
    have := hs c; have := hs (c + 1); have := hs (c + 2)
    rw [abs_le] at *
    constructor <;> linarith
  · simp only [hatD, stepAt, not_lt.2 h, not_lt.2 (h.trans (by linarith : c ≤ c + 1)),
      not_lt.2 (h.trans (by linarith : c ≤ c + 2)), ↓reduceIte]
    ring

/-- **Cochrane (2023), A1 §1.6, p. 567: the hats form a partition of unity on `[1, ∞)`:**
`Σ_ω φ_ω(T) = 1` for `T ≥ 1`. -/
theorem tsum_hat {T : ℝ} (hT : 1 ≤ T) : ∑' ω : ℕ, hat ω T = 1 := by
  set m := ⌊T⌋₊ with hm
  have hT0 : 0 ≤ T := by linarith
  have hmT : (m : ℝ) ≤ T := Nat.floor_le hT0
  have hTm : T < m + 1 := Nat.lt_floor_add_one T
  have hm1 : 1 ≤ m := Nat.le_floor (by simpa using hT)
  rw [tsum_eq_sum (s := {m - 1, m}) fun n hn => ?_]
  · rw [Finset.sum_pair (by omega)]
    have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1, Nat.cast_one]
    rw [hc, hat_of_mid2 (by linarith) (by linarith), hat_of_mid1 hmT hTm.le]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rcases lt_or_gt_of_ne hn.2 with h | h
    · have h2 : n + 2 ≤ m := by omega
      have h2' : (n : ℝ) + 2 ≤ m := by exact_mod_cast h2
      exact hat_of_ge (by linarith)
    · have h2 : m + 1 ≤ n := h
      have h2' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h2
      exact hat_of_le (by linarith)

/-! ## The model -/

/-- Cochrane (2023), A1 §1.6, p. 567: the unit process. -/
def uiOne (_ : ℝ) (_ : ℕ) : ℝ := 1

/-- Cochrane (2023), A1 §1.6, p. 567: the zero process. -/
def uiZero (_ : ℝ) (_ : ℕ) : ℝ := 0

/-- Cochrane (2023), A1 §1.6, p. 567: the weight `2^{ω+1}`. -/
def wt (ω : ℕ) : ℝ := (2 : ℝ) ^ (ω + 1)

/-- Cochrane (2023), A1 §1.6, p. 567: bonds `B_u(ω) = 1 − 2^{ω+1}φ_ω(u)`. -/
noncomputable def uiB (u : ℝ) (ω : ℕ) : ℝ := 1 - wt ω * hat ω u

/-- Cochrane (2023), A1 §1.6, p. 567: the surplus `s = −Ḃ = 2^{ω+1}φ_ω'`. -/
noncomputable def uiSur (u : ℝ) (ω : ℕ) : ℝ := wt ω * hatD ω u

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P = 1`. -/
theorem disc_ui (u : ℝ) (ω : ℕ) : disc uiOne uiOne u ω = 1 := by
  simp [disc, uiOne]

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: the flow density is `−s`. -/
theorem flowRate_ui (ω : ℕ) :
    (fun r => flowRate uiB uiZero uiOne uiZero uiZero uiSur r ω) =
      fun r => -(wt ω * hatD ω r) :=
  funext fun r => by simp only [flowRate, uiZero, uiOne, uiSur]; ring

/-- Cochrane (2023), A1 §1.6, p. 567: before the state is revealed, `B = 1`. -/
theorem uiB_of_le {u : ℝ} (hu : u ≤ 0) (ω : ℕ) : uiB u ω = 1 := by
  simp only [uiB, hat_of_le (hu.trans (Nat.cast_nonneg ω)), mul_zero, sub_zero]

/-- **Cochrane (2023), A1 §1.6, (1.31), p. 567: the counterexample satisfies
`TidyR7MonetarismModel.MonetaryModel`.** -/
theorem uiModel : MonetaryModel uiMeasure uiFilt uiOne uiOne uiB uiZero uiOne uiZero uiZero
    uiZero uiSur where
  P_pos _ _ := one_pos
  Λ_pos _ _ := one_pos
  Λ_adapted _ := stronglyMeasurable_const
  P_adapted _ := stronglyMeasurable_const
  dec u ω := by simp [disc, uiOne, uiZero]
  A_incr ω u v _ := by simp [uiOne, uiZero]
  A_int ω u v := by
    have e : (fun r => -(uiZero r ω * disc uiOne uiOne r ω)) = fun _ => (0 : ℝ) :=
      funext fun r => by simp [uiZero]
    rw [e]
    exact intervalIntegrable_const
  N_mart := martingale_const _ _ _
  N_cadlag _ := IsCadlag.const
  B_adapted := ui_adapted fun u hu ω => by rw [uiB_of_le hu, uiB_of_le hu]
  M_adapted _ := stronglyMeasurable_const
  M_cont _ := continuous_const
  M_bv _ a b := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  flow ω u v huv := by
    rw [flowRate_ui ω, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      ← hat_incr _ huv]
    simp only [addProc, uiB, uiZero]
    ring
  flow_int ω u v := by
    rw [flowRate_ui ω]
    exact ((intervalIntegrable_hatD _ u v).const_mul _).neg

/-! ## Flows, transversality and the two readings of `∫_0^∞` -/

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `F_T(ω) = 2^{ω+1}φ_ω(T)` for `T ≥ 0`. -/
theorem ui_flow {T : ℝ} (hT : 0 ≤ T) (ω : ℕ) :
    flow133 uiOne uiOne uiZero uiSur 0 T ω = wt ω * hat ω T := by
  have hrs := rsInt_eq_integral_of_incr (f := fun u => disc uiOne uiOne u ω)
    (g := fun u => uiZero u ω) (h := fun _ => (0 : ℝ))
    (uiModel.disc_cadlag ω) (fun _ _ => intervalIntegrable_const)
    (fun u v _ => by simp [uiZero]) hT
  have h0 : hat ω 0 = 0 := hat_of_le (Nat.cast_nonneg ω)
  have e : ∫ r in (0 : ℝ)..T, uiOne r ω * uiSur r ω = wt ω * (hat ω T - hat ω 0) := by
    rw [hat_incr _ hT, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun r _ => by simp only [uiOne, uiSur]; ring
  rw [flow133, hrs, e, h0]
  simp

/-- Cochrane (2023), A1 §1.6, p. 567: `|2^{ω+1}φ_ω(u)| ≤ 2^{⌈T⌉₊}` for `u ≤ T` (`φ_ω(u) ≠ 0`
only if `ω < u`). -/
theorem abs_wt_hat_le {T u : ℝ} (hu : u ≤ T) (ω : ℕ) :
    |wt ω * hat ω u| ≤ (2 : ℝ) ^ ⌈T⌉₊ := by
  obtain ⟨h0, h1⟩ := hat_mem ω u
  by_cases h : (ω : ℝ) < u
  · have hω : ω < ⌈T⌉₊ := Nat.lt_ceil.2 (lt_of_lt_of_le h hu)
    have hw : wt ω ≤ (2 : ℝ) ^ ⌈T⌉₊ := pow_le_pow_right₀ (by norm_num) hω
    have hw0 : 0 ≤ wt ω := by unfold wt; positivity
    rw [abs_of_nonneg (mul_nonneg hw0 h0)]
    nlinarith
  · rw [hat_of_le (not_lt.1 h), mul_zero, abs_zero]
    positivity

/-- Cochrane (2023), A1 §1.6, p. 567: `F_T` and `B_T` are integrable (bounded on a probability
space). -/
theorem ui_integrable (T : ℝ) :
    Integrable (fun ω => wt ω * hat ω T) uiMeasure ∧ Integrable (uiB T) uiMeasure := by
  have h1 : Integrable (fun ω => wt ω * hat ω T) uiMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((2 : ℝ) ^ ⌈T⌉₊)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_wt_hat_le le_rfl ω)
  refine ⟨h1, ?_⟩
  have e : uiB T = fun ω => 1 - wt ω * hat ω T := rfl
  rw [e]
  exact (integrable_const _).sub h1

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: `E_0[F_T] = Σ_ω φ_ω(T) = 1` for `T ≥ 1`.** -/
theorem ui_EF {T : ℝ} (hT : 1 ≤ T) :
    uiMeasure[flow133 uiOne uiOne uiZero uiSur 0 T | uiFilt 0] = fun _ => 1 := by
  have e : flow133 uiOne uiOne uiZero uiSur 0 T = fun ω => wt ω * hat ω T :=
    funext fun ω => ui_flow (by linarith) ω
  rw [condExp_ui_zero, e]
  funext _
  exact (integral_ui_wt (fun ω => hat ω T)).trans (tsum_hat hT)

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the transversality condition holds:**
`E_0[n_TB_T] = 1 − 1 = 0` for `T ≥ 1`. -/
theorem ui_tvc {T : ℝ} (hT : 1 ≤ T) :
    uiMeasure[fun ω => disc uiOne uiOne T ω * uiB T ω | uiFilt 0] = fun _ => 0 := by
  rw [condExp_ui_zero]
  funext _
  have e : (fun ω => disc uiOne uiOne T ω * uiB T ω) = fun ω => 1 - wt ω * hat ω T :=
    funext fun ω => by rw [disc_ui, one_mul]; rfl
  have h1 : ∫ ω, wt ω * hat ω T ∂uiMeasure = 1 :=
    (integral_ui_wt (fun ω => hat ω T)).trans (tsum_hat hT)
  rw [e, integral_sub (integrable_const _) (ui_integrable T).1, h1]
  simp

/-- Cochrane (2023), A1 §1.6, p. 567: `n_0B_0 = 1`. -/
theorem ui_Y0 (ω : ℕ) : disc uiOne uiOne 0 ω * uiB 0 ω = 1 := by
  rw [disc_ui, uiB_of_le le_rfl, one_mul]

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the limit form holds:**
`E_0[F_T] → 1 = n_0B_0`. -/
theorem ui_limit (ω : ℕ) :
    Tendsto (fun T => uiMeasure[flow133 uiOne uiOne uiZero uiSur 0 T | uiFilt 0] ω) atTop
      (𝓝 (disc uiOne uiOne 0 ω * uiB 0 ω)) := by
  rw [ui_Y0]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [ui_EF hT]

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the flows tend to `G = 0` path by path**
(`φ_ω(T) = 0` for `T ≥ ω + 2`). -/
theorem ui_pathwise (ω : ℕ) :
    Tendsto (fun T => flow133 uiOne uiOne uiZero uiSur 0 T ω) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ((ω : ℝ) + 2)] with T hT
  rw [ui_flow (by linarith [Nat.cast_nonneg (α := ℝ) ω]) ω, hat_of_ge hT, mul_zero]

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the literal form fails:**
`n_0B_0 = 1` but `E_0[G] = E_0[∫_0^∞ Λs] = 0`. -/
theorem ui_literal_fails :
    ¬ (fun ω => disc uiOne uiOne 0 ω * uiB 0 ω) =ᵐ[uiMeasure]
      uiMeasure[fun _ => (0 : ℝ) | uiFilt 0] := by
  intro h
  rw [condExp_ui_zero] at h
  obtain ⟨ω, hω⟩ := h.exists
  have h2 : disc uiOne uiOne 0 ω * uiB 0 ω = ∫ _, (0 : ℝ) ∂uiMeasure := hω
  rw [ui_Y0, integral_zero] at h2
  norm_num at h2

/-- Cochrane (2023), A1 §1.6, p. 567: `F_T ≥ 0`. -/
theorem ui_flow_nonneg {T : ℝ} (hT : 0 ≤ T) (ω : ℕ) :
    0 ≤ flow133 uiOne uiOne uiZero uiSur 0 T ω := by
  rw [ui_flow hT]
  exact mul_nonneg (by unfold wt; positivity) (hat_mem ω T).1

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: no `L¹` convergence:**
`∫|F_T − 0| = 1` for `T ≥ 1`. -/
theorem ui_not_L1 :
    ¬ Tendsto (fun T => ∫ ω, |flow133 uiOne uiOne uiZero uiSur 0 T ω - 0| ∂uiMeasure) atTop
      (𝓝 0) := by
  intro h
  have e : ∀ T : ℝ, 1 ≤ T →
      ∫ ω, |flow133 uiOne uiOne uiZero uiSur 0 T ω - 0| ∂uiMeasure = 1 := by
    intro T hT
    have h1 := congrFun (ui_EF hT) 0
    rw [condExp_ui_zero] at h1
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [sub_zero]
    exact abs_of_nonneg (ui_flow_nonneg (by linarith) ω)
  have h1 : Tendsto (fun T => ∫ ω, |flow133 uiOne uiOne uiZero uiSur 0 T ω - 0| ∂uiMeasure)
      atTop (𝓝 1) := tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 1] with T hT
        rw [e T hT])
  exact one_ne_zero (tendsto_nhds_unique h1 h)

/-- **Cochrane (2023), A1 §1.6, p. 567: the product-step domination holds on every `[0, T]`**
(`|B| ≤ 1 + 2^{⌈T⌉₊}`, `Var(B) ≤ ∫_0^T |s| ≤ 4·2^{⌈T⌉₊}T`, `Λ/P = 1`, `A = 1`). -/
theorem ui_dom {T : ℝ} (hT : 0 ≤ T) :
    Dominated uiMeasure uiOne uiZero 0 T uiB (disc uiOne uiOne) := by
  set K : ℝ := 1 + 4 * (2 : ℝ) ^ ⌈T⌉₊ * (T + 1) with hK
  have hpow : 0 ≤ (2 : ℝ) ^ ⌈T⌉₊ := by positivity
  have hK0 : 0 ≤ K := by positivity
  refine Dominated.of_bound (K := K) hK0 (fun _ => measurable_of_countable _)
    (fun _ => measurable_of_countable _) (fun _ => measurable_of_countable _)
    (fun ω => ?_) (fun _ => IsCadlag.const) (fun _ => integrable_zero _ _ _)
    (fun ω u _ => ?_) (fun ω u hu => ?_) (fun ω => ?_) (fun ω => ?_)
  · exact continuous_const.sub (continuous_const.mul (continuous_hat _))
  · rw [disc_ui, abs_one]
    nlinarith
  · have := abs_wt_hat_le hu.2 ω
    have e : uiB u ω = 1 - wt ω * hat ω u := rfl
    rw [e]
    calc |1 - wt ω * hat ω u| ≤ |(1 : ℝ)| + |wt ω * hat ω u| := abs_sub _ _
      _ ≤ K := by rw [abs_one]; nlinarith
  · -- the variation is at most `∫_0^T |s|`
    have hprim : ∀ x ∈ Set.Icc (0 : ℝ) T,
        uiB x ω = uiB 0 ω + ∫ y in (0 : ℝ)..x, -(wt ω * hatD ω y) := by
      intro x hx
      have := uiModel.flow ω 0 x hx.1
      rw [flowRate_ui ω] at this
      simp only [addProc, uiZero, add_zero] at this
      linarith
    have hv := eVariationOn_le_integral hT (((intervalIntegrable_hatD _ 0 T).const_mul _).neg)
      hprim
    simp only [Pi.neg_apply] at hv
    have hbound : ∫ y in (0 : ℝ)..T, |-(wt ω * hatD ω y)| ≤ 4 * (2 : ℝ) ^ ⌈T⌉₊ * T := by
      have hle : ∀ y ∈ Set.Icc (0 : ℝ) T, |-(wt ω * hatD ω y)| ≤ 4 * (2 : ℝ) ^ ⌈T⌉₊ := by
        intro y hy
        rw [abs_neg, abs_mul]
        obtain ⟨h4, h0⟩ := abs_hatD_le ω y
        have hw0 : 0 ≤ wt ω := by unfold wt; positivity
        by_cases h : (ω : ℝ) < y
        · have hω : ω < ⌈T⌉₊ := Nat.lt_ceil.2 (lt_of_lt_of_le h hy.2)
          have hw : wt ω ≤ (2 : ℝ) ^ ⌈T⌉₊ := pow_le_pow_right₀ (by norm_num) hω
          rw [abs_of_nonneg hw0]
          nlinarith [abs_nonneg (hatD ω y)]
        · rw [h0 (not_lt.1 h), abs_zero, mul_zero]
          positivity
      have hm := intervalIntegral.integral_mono_on hT
        (((intervalIntegrable_hatD _ 0 T).const_mul _).neg.abs) intervalIntegrable_const hle
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      simp only [Pi.neg_apply] at hm
      linarith
    have hint0 : 0 ≤ ∫ y in (0 : ℝ)..T, |-(wt ω * hatD ω y)| :=
      intervalIntegral.integral_nonneg hT fun _ _ => abs_nonneg _
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    rw [ENNReal.toReal_ofReal hint0] at this
    change (eVariationOn (fun u => uiB u ω) (Set.Icc 0 T)).toReal ≤ K
    nlinarith
  · have hc : eVariationOn (fun u => uiOne u ω) (Set.Icc 0 T) = 0 :=
      eVariationOn.constant_on (Set.subsingleton_of_forall_eq (1 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)
    change (eVariationOn (fun u => uiOne u ω) (Set.Icc 0 T)).toReal ≤ K
    rw [hc, ENNReal.toReal_zero]
    exact hK0

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: no integrable `H` dominates the flows.** Every
hypothesis of `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_dom` other than the
domination `|F_{T_k}| ≤ H` holds along `T_k = k + 1` (with `G = 0`), and so does the
transversality condition; if some integrable `H` dominated the flows,
`MonetaryModel.valuation_1_33_dom` would
give `n_0B_0 = E_0[G] = 0`, contradicting `n_0B_0 = 1`. -/
theorem ui_not_dominated : ¬ ∃ H : ℕ → ℝ, Integrable H uiMeasure ∧
    ∀ (k : ℕ) ω, |flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω| ≤ H ω := by
  rintro ⟨H, hH, hbd⟩
  have hk : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hseq : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := MonetaryModel.valuation_1_33_dom uiModel (fun _ _ => rfl) (s := 0)
    (fun T hT => ui_dom hT) (fun T _ => by
      have e : (fun ω => disc uiOne uiOne T ω * uiB T ω) = uiB T :=
        funext fun ω => by rw [disc_ui, one_mul]
      rw [e]; exact (ui_integrable T).2)
    (T := fun k : ℕ => (k : ℝ) + 1) (fun k => by linarith [hk k]) (G := fun _ => 0) hH hbd
    (fun ω => (ui_pathwise ω).comp hseq)
  refine ui_literal_fails (h.2 (Eventually.of_forall fun ω => ?_))
  refine tendsto_const_nhds.congr fun k => ?_
  rw [ui_tvc (hk k)]

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the domination (or `L¹`) hypothesis is needed for
the literal `n_sB_s = E_s[∫_s^∞ Λs dr + ∫_s^∞ n dM]`.** In `uiModel` at `s = 0`: the
transversality condition holds; the limit form `lim E_0[F_T] = n_0B_0` holds; the flows converge
path by path to `G = 0`; yet `n_0B_0 ≠ E_0[G]`; the flows are neither dominated nor `L¹`
convergent; and the product-step domination holds on every `[0, T]`. -/
theorem ui_headline :
    (∀ T : ℝ, 1 ≤ T →
      uiMeasure[fun ω => disc uiOne uiOne T ω * uiB T ω | uiFilt 0] = fun _ => 0) ∧
      (∀ ω, Tendsto (fun T => uiMeasure[flow133 uiOne uiOne uiZero uiSur 0 T | uiFilt 0] ω)
        atTop (𝓝 (disc uiOne uiOne 0 ω * uiB 0 ω))) ∧
      (∀ ω, Tendsto (fun T => flow133 uiOne uiOne uiZero uiSur 0 T ω) atTop (𝓝 0)) ∧
      ¬ (fun ω => disc uiOne uiOne 0 ω * uiB 0 ω) =ᵐ[uiMeasure]
        uiMeasure[fun _ => (0 : ℝ) | uiFilt 0] ∧
      (¬ ∃ H : ℕ → ℝ, Integrable H uiMeasure ∧
        ∀ (k : ℕ) ω, |flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω| ≤ H ω) ∧
      ¬ Tendsto (fun T => ∫ ω, |flow133 uiOne uiOne uiZero uiSur 0 T ω - 0| ∂uiMeasure) atTop
        (𝓝 0) ∧
      ∀ T : ℝ, 0 ≤ T → Dominated uiMeasure uiOne uiZero 0 T uiB (disc uiOne uiOne) :=
  ⟨fun _ hT => ui_tvc hT, ui_limit, ui_pathwise, ui_literal_fails, ui_not_dominated, ui_not_L1,
    fun _ hT => ui_dom hT⟩

end Cochrane.Monetarism.TidyR7MonetarismUI
