/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.HouseholdMeasure

/-!
# Transversality, sufficiency and the valuation equation on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, p. 22 ("Household
maximization, budget constraint, and equilibrium `c_t = y` also imply the household
transversality condition (2.6)"; iterating (2.5) gives (2.7)) and Online Appendix A1.1,
pp. 554–556, in the measure-theoretic setting of `ExpectationsMeasure` and `HouseholdMeasure`.
Information may grow forever: no `Valuation.InfoStable` hypothesis is used anywhere.

## Main results

* `tvc_end_of_optimal`, **necessity of the transversality condition** with information growing
  forever: in an optimal plan with concave increasing utility, if the after-tax endowment plan
  `c_n = y − s_n` is admissible, then `β^T E[u'(c_T) Q_T B_T/P_T] → 0`. The proof (Kamihigashi's
  scaling argument) compares the plan with the one that from date `T` on holds the fraction
  `1 − θ` of its bonds, consumes the proceeds `θ Q_T B_T/P_T` at `T` and the convex combination
  `(1 − θ) c_n + θ (y − s_n)` afterwards; this deviation satisfies every flow constraint
  exactly, whatever the information structure. `tvc_of_optimal` turns it into the
  marginal-utility-weighted transversality condition `β^N E[u'(c_N) B_{N−1}/P_N] → 0` through
  the Euler inequality.
* `optimal_of_euler_tvc`, **sufficiency**: a feasible admissible plan satisfying the Euler
  equation at every date and the transversality condition is optimal, for concave `u`. The
  comparison plan's bond positions need not be integrable a priori: integrability is proved
  date by date (`integrable_mul_of_E`).
* At the equilibrium `c = y`: `flowX_of_feasible` ((2.5) almost surely), `telescope_ae`,
  `tvc_valuation_of_unconditional`, and `valuation_of_optimal_eqm`: optimisation implies the book's
  transversality condition (2.6) `β^N E_t x_{t+N} → 0` almost surely **at every date**, and the
  valuation equation (2.7) `B_{t−1}/P_t = ∑_j β^j E_t s_{t+j}` almost surely, also in the form
  `E_t ∑_j β^j s_{t+j}` (part 4 of `valuation_of_optimal_eqm`).
* `IID.iid_equilibrium`: in the i.i.d. economy (`ExpectationsMeasureIID.iidSystem`, every
  history null, information growing forever) with surpluses `s_t = s̄ + σ ε_t`, the price level
  `P_t = B̄/(s̄/(1 − β) + σ ε_t)` and the bond price `Q_t = β E_t(P_t/P_{t+1})`, the endowment
  plan is optimal (by `optimal_of_euler_tvc`), the valuation equation holds (by
  `valuation_of_optimal_eqm`), `Q_t > 0`, and real debt carries genuine news.
* Links to the finite-state statements of `Valuation` through the bridge
  (`Link.feasible_iff`, `Link.optimal_of_core`, `Link.link_euler`, `Link.link_tvc_valuation`):
  on a finite event tree the core feasibility notion is the measure one, the core optimality
  notion implies the measure one, and the measure results give the core Euler equation and
  inequality, transversality condition and valuation equation in every state, without
  `Valuation.InfoStable`.
-/

namespace Cochrane.IntertemporalModel.HouseholdMeasureTVC

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Concave utility -/

/-- Cochrane (2023), Online Appendix A1.1, p. 556 (concave utility): the derivative of a
differentiable concave function is antitone. -/
theorem deriv_antitone {u u' : ℝ → ℝ} (hconc : ConcaveOn ℝ Set.univ u)
    (hu : ∀ x, HasDerivAt u (u' x) x) : Antitone u' := by
  intro a b hab
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · have h1 := Valuation.concave_le_tangent hconc (hu a) b
    have h2 := Valuation.concave_le_tangent hconc (hu b) a
    by_contra hlt
    push Not at hlt
    nlinarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556: for concave `u`,
`u(c + h) − u(c) ≥ h u'(c + h)`. -/
theorem sub_ge_mul_deriv {u u' : ℝ → ℝ} (hconc : ConcaveOn ℝ Set.univ u)
    (hu : ∀ x, HasDerivAt u (u' x) x) (c h : ℝ) : h * u' (c + h) ≤ u (c + h) - u c := by
  have := Valuation.concave_le_tangent hconc (hu (c + h)) c
  linarith

/-- Cochrane (2023), Online Appendix A1.1, p. 556: for increasing `u`, a value between
`u a` and `u b` (at a convex combination) is bounded by `|u a| + |u b|`. -/
theorem abs_comb_le {u : ℝ → ℝ} (hmono : Monotone u) {a e θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |u ((1 - θ) * a + θ * e)| ≤ |u a| + |u e| := by
  rcases le_total a e with hae | hae
  · have l : a ≤ (1 - θ) * a + θ * e := by nlinarith
    have r : (1 - θ) * a + θ * e ≤ e := by nlinarith
    have := hmono l
    have := hmono r
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (u a), le_abs_self (u e), abs_nonneg (u a),
      abs_nonneg (u e), neg_abs_le (u e), le_abs_self (u a)]
  · have l : e ≤ (1 - θ) * a + θ * e := by nlinarith
    have r : (1 - θ) * a + θ * e ≤ a := by nlinarith
    have := hmono l
    have := hmono r
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (u a), le_abs_self (u e), abs_nonneg (u a),
      abs_nonneg (u e), neg_abs_le (u e), le_abs_self (u a)]

/-! ### The scaling deviation (Kamihigashi) -/

/-- Cochrane (2023), p. 22 ("the consumer can raise consumption at time `t`, lower this terminal
value"), under uncertainty: from date `T` on, hold the fraction `1 − θ` of the bonds, consume the
proceeds `θ k` (`k = Q_T B_T/P_T`) at `T` and `(1 − θ) c_n + θ (y − s_n)` afterwards. -/
noncomputable def kamC (y : ℝ) (s c : ℕ → Ω → ℝ) (k : Ω → ℝ) (T : ℕ) (θ : ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => if n < T then c n ω else if n = T then c T ω + θ * k ω
    else (1 - θ) * c n ω + θ * (y - s n ω)

/-- Cochrane (2023), p. 22: the bond holdings of the scaling deviation, `(1 − θ) B_{n−1}` for
`n > T`. -/
noncomputable def kamB (b : ℕ → Ω → ℝ) (T : ℕ) (θ : ℝ) : ℕ → Ω → ℝ :=
  fun n ω => if n ≤ T then b n ω else (1 - θ) * b n ω

/-- Cochrane (2023), eq. (2.2), p. 21: the scaling deviation satisfies the flow constraint at
every date and state (exactly, under any information structure), is adapted, and keeps debt
nonnegative, for `θ ≤ 1`. -/
theorem kam_feasible {y : ℝ} {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hf : Feasible S y P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hQad : StronglyAdapted S.𝓕 Q) (hsad : StronglyAdapted S.𝓕 s)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) (T : ℕ) {θ : ℝ} (h1 : θ ≤ 1) :
    Feasible S y P s Q b₀
      (kamC y s c (fun ω => Q T ω * b (T + 1) ω / P T ω) T θ) (kamB b T θ) := by
  obtain ⟨hb0, hcad, hbad, hflow, hbnn⟩ := hf
  refine ⟨?_, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · funext ω
    simp only [kamB, zero_le, ↓reduceIte]
    rw [hb0]
  · rcases lt_trichotomy n T with hn | hn | hn
    · have e : kamC y s c (fun ω => Q T ω * b (T + 1) ω / P T ω) T θ n = c n := by
        funext ω
        simp [kamC, hn]
      rw [e]
      exact hcad n
    · subst hn
      have e : kamC y s c (fun ω => Q n ω * b (n + 1) ω / P n ω) n θ n =
          fun ω => c n ω + θ * (Q n ω * b (n + 1) ω / P n ω) := by
        funext ω
        simp [kamC]
      rw [e]
      exact (hcad n).add ((((hQad n).measurable.mul (hbad n).measurable).div
        (hPad n).measurable).stronglyMeasurable.const_mul θ)
    · have e : kamC y s c (fun ω => Q T ω * b (T + 1) ω / P T ω) T θ n =
          fun ω => (1 - θ) * c n ω + θ * (y - s n ω) := by
        funext ω
        simp [kamC, (show ¬ n < T by omega), (show n ≠ T by omega)]
      rw [e]
      exact ((hcad n).const_mul _).add
        ((stronglyMeasurable_const.sub (hsad n)).const_mul θ)
  · by_cases hn : n + 1 ≤ T
    · have e : kamB b T θ (n + 1) = b (n + 1) := by
        funext ω
        simp [kamB, hn]
      rw [e]
      exact hbad n
    · have e : kamB b T θ (n + 1) = fun ω => (1 - θ) * b (n + 1) ω := by
        funext ω
        simp [kamB, hn]
      rw [e]
      exact (hbad n).const_mul _
  · rcases lt_trichotomy n T with hn | hn | hn
    · filter_upwards [hflow n] with ω h
      simp only [kamC, kamB, hn, hn.le, (show n + 1 ≤ T by omega), ↓reduceIte]
      exact h
    · subst hn
      filter_upwards [hflow n, hP n] with ω h hp
      have := hp.ne'
      simp only [kamC, kamB, lt_irrefl, le_refl, (show ¬ n + 1 ≤ n by omega), ↓reduceIte]
      field_simp
      linear_combination h
    · filter_upwards [hflow n] with ω h
      simp only [kamC, kamB, (show ¬ n < T by omega), (show n ≠ T by omega),
        (show ¬ n ≤ T by omega), (show ¬ n + 1 ≤ T by omega), ↓reduceIte]
      linear_combination (1 - θ) * h
  · filter_upwards [hbnn n] with ω h
    simp only [kamB]
    split_ifs
    · exact h
    · exact mul_nonneg (by linarith) h

/-- Cochrane (2023), Online Appendix A1.1, p. 556: for increasing concave `u`, `k ≥ 0` and
`0 ≤ θ ≤ 1`, `|u(c + θk)| ≤ |u(c)| + u'(c) k`. -/
theorem abs_shift_le {u u' : ℝ → ℝ} (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    (hu : ∀ x, HasDerivAt u (u' x) x) {c k θ : ℝ} (hk : 0 ≤ k) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |u (c + θ * k)| ≤ |u c| + u' c * k := by
  have hd := Valuation.deriv_nonneg_of_monotone hmono (hu c)
  have l : u c ≤ u (c + θ * k) := hmono (by nlinarith)
  have r := Valuation.concave_le_tangent hconc (hu c) (c + θ * k)
  have r2 : u' c * (c + θ * k - c) ≤ u' c * k := by
    rw [add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hd
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (u c), le_abs_self (u c), mul_nonneg hd hk]

/-- Cochrane (2023), p. 22: the tail of the utility gain of the plan over the after-tax
endowment plan, `∑_{n > T} β^n (u(c_n) − u(y − s_n))`. -/
noncomputable def tail (β y : ℝ) (u : ℝ → ℝ) (s c : ℕ → Ω → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑' n, if T < n then β ^ n * (u (c n ω) - u (y - s n ω)) else 0

/-- Cochrane (2023), p. 22: the tail of a convergent series, `∑_{n > T} f_n`, is
`∑ f − ∑_{n ≤ T} f_n`. -/
theorem hasSum_ite_lt {f : ℕ → ℝ} (hf : Summable f) (T : ℕ) :
    HasSum (fun n => if T < n then f n else 0) (∑' n, f n - ∑ n ∈ Finset.range (T + 1), f n) := by
  have hfin : HasSum (fun n => if T < n then 0 else f n) (∑ n ∈ Finset.range (T + 1), f n) := by
    have h : HasSum (fun n => if T < n then 0 else f n)
        (∑ n ∈ Finset.range (T + 1), if T < n then 0 else f n) :=
      hasSum_sum_of_ne_finset_zero fun n hn => by
        simp only [Finset.mem_range, not_lt] at hn
        simp only [(show T < n by omega), ↓reduceIte]
    convert h using 1
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_range] at hn
    simp only [(show ¬ T < n by omega), ↓reduceIte]
  convert hf.hasSum.sub hfin using 1
  funext n
  split_ifs <;> ring

/-- Cochrane (2023), p. 22, "Household maximization ... also imply the household transversality
condition (2.6). If the term on the left is positive, then the consumer can raise consumption at
time `t`, lower this terminal value, and raise utility", on a genuine probability space with
information growing forever: if `(c, b)` is optimal, `u` is concave, increasing and
differentiable with continuous derivative, prices are positive, bond prices are nonnegative,
prices, bond prices and taxes are adapted, the after-tax endowment plan `c_n = y − s_n` is
admissible, and `u'(c_T) Q_T B_T/P_T` is integrable, then
`β^T E[u'(c_T) Q_T B_T/P_T] → 0`: the expected discounted marginal-utility value of the debt
carried out of date `T` vanishes. -/
theorem tvc_end_of_optimal {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hQad : StronglyAdapted S.𝓕 Q) (hsad : StronglyAdapted S.𝓕 s)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) (hQ : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ Q n ω)
    (he : Admissible S β u (fun n ω => y - s n ω))
    (hint : ∀ T, Integrable (fun ω => u' (c T ω) * (Q T ω * b (T + 1) ω / P T ω)) S.μ) :
    Tendsto (fun T => β ^ T * ∫ ω, u' (c T ω) * (Q T ω * b (T + 1) ω / P T ω) ∂S.μ)
      atTop (𝓝 0) := by
  obtain ⟨hfeas, hadm, hbest⟩ := hopt
  have hcad := hfeas.2.1
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  set k : ℕ → Ω → ℝ := fun T ω => Q T ω * b (T + 1) ω / P T ω with hk
  have hk0 : ∀ T, ∀ᵐ ω ∂S.μ, 0 ≤ k T ω := fun T => by
    filter_upwards [hQ T, hfeas.2.2.2.2 (T + 1), hP T] with ω h1 h2 h3
    exact div_nonneg (mul_nonneg h1 h2) h3.le
  have hkm : ∀ T, AEStronglyMeasurable (k T) S.μ := fun T =>
    ((((hQad T).measurable.mul (hfeas.2.2.1 T).measurable).div
      (hPad T).measurable).stronglyMeasurable.mono (S.𝓕.le T)).aestronglyMeasurable
  have hcm : ∀ T, AEStronglyMeasurable (c T) S.μ := fun T =>
    ((hcad T).mono (S.𝓕.le T)).aestronglyMeasurable
  have hu'0 : ∀ x, 0 ≤ u' x := fun x => Valuation.deriv_nonneg_of_monotone hmono (hu x)
  have hanti := deriv_antitone hconc hu
  set G : Ω → ℝ := fun ω => ∑' n, β ^ n * |u (c n ω)| + ∑' n, β ^ n * |u (y - s n ω)| with hG
  have hGi : Integrable G S.μ := hadm.2.2.add he.2.2
  have hsc := hadm.2.1
  have hse := he.2.1
  have hsc' := hadm.summable hβ.le
  have hse' := he.summable hβ.le
  -- the tail
  have htail_bd : ∀ T, ∀ᵐ ω ∂S.μ, |tail β y u s c T ω| ≤ G ω := fun T => by
    filter_upwards [hsc, hse] with ω h1 h2
    rw [← Real.norm_eq_abs]
    refine tsum_of_norm_bounded (h1.hasSum.add h2.hasSum) fun n => ?_
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.le, ← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (pow_nonneg hβ.le n)
    · rw [norm_zero]
      exact add_nonneg (mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _))
        (mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _))
  have htail_m : ∀ T, AEStronglyMeasurable (tail β y u s c T) S.μ := fun T => by
    refine aestronglyMeasurable_tsum (fun n => ?_) ?_
    · split_ifs
      · exact ((hadm.1 n).sub (he.1 n)).const_mul _
      · exact aestronglyMeasurable_const
    · filter_upwards [hsc', hse'] with ω h1 h2
      have hf : Summable fun n => β ^ n * (u (c n ω) - u (y - s n ω)) :=
        (h1.sub h2).congr fun n => by ring
      exact (hasSum_ite_lt hf T).summable
  have htail_i : ∀ T, Integrable (tail β y u s c T) S.μ := fun T =>
    Integrable.mono' hGi (htail_m T) (htail_bd T)
  -- the key inequality for each `T` and `θ ∈ (0, 1]`
  have key : ∀ T θ, 0 < θ → θ ≤ 1 →
      β ^ T * ∫ ω, k T ω * u' (c T ω + θ * k T ω) ∂S.μ ≤ ∫ ω, tail β y u s c T ω ∂S.μ := by
    intro T θ hθ0 hθ1
    have hfθ := kam_feasible hfeas hPad hQad hsad hP T hθ1
    set c' := kamC y s c (k T) T θ with hc'
    have hc'm : ∀ n, AEStronglyMeasurable (fun ω => u (c' n ω)) S.μ := fun n =>
      huc.comp_aestronglyMeasurable ((hfθ.2.1 n).mono (S.𝓕.le n)).aestronglyMeasurable
    have hbd : ∀ᵐ ω ∂S.μ, ∀ n, β ^ n * |u (c' n ω)| ≤
        β ^ n * |u (c n ω)| + β ^ n * |u (y - s n ω)| +
          (if n = T then β ^ T * (u' (c T ω) * k T ω) else 0) := by
      filter_upwards [hk0 T] with ω hkω n
      have hbn := pow_nonneg hβ.le n
      have hA := mul_nonneg hbn (abs_nonneg (u (y - s n ω)))
      rcases lt_trichotomy n T with hn | hn | hn
      · simp only [hc', kamC, hn, ↓reduceIte, hn.ne, add_zero]
        linarith
      · subst hn
        simp only [hc', kamC, lt_irrefl, ↓reduceIte]
        have := mul_le_mul_of_nonneg_left
          (abs_shift_le hconc hmono hu (c := c n ω) hkω hθ0.le hθ1) hbn
        nlinarith
      · simp only [hc', kamC, (show ¬ n < T by omega), (show n ≠ T by omega), ↓reduceIte,
          add_zero]
        have := mul_le_mul_of_nonneg_left
          (abs_comb_le hmono (a := c n ω) (e := y - s n ω) hθ0.le hθ1) hbn
        linarith
    have hg_sum : ∀ᵐ ω ∂S.μ, HasSum (fun n => β ^ n * |u (c n ω)| + β ^ n * |u (y - s n ω)| +
        (if n = T then β ^ T * (u' (c T ω) * k T ω) else 0))
        (G ω + β ^ T * (u' (c T ω) * k T ω)) := by
      filter_upwards [hsc, hse] with ω h1 h2
      exact (h1.hasSum.add h2.hasSum).add (hasSum_ite_eq T _)
    have hnn : ∀ ω n, 0 ≤ β ^ n * |u (c' n ω)| := fun ω n =>
      mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _)
    have hadm' : Admissible S β u c' := by
      refine ⟨hc'm, ?_, ?_⟩
      · filter_upwards [hbd, hg_sum] with ω h hs
        exact Summable.of_nonneg_of_le (hnn ω) h hs.summable
      · refine Integrable.mono' (hGi.add ((hint T).const_mul (β ^ T)))
          (aestronglyMeasurable_tsum (fun n => (hc'm n).norm.const_mul _) ?_) ?_
        · filter_upwards [hbd, hg_sum] with ω h hs
          exact Summable.of_nonneg_of_le (hnn ω) h hs.summable
        · filter_upwards [hbd, hg_sum] with ω h hs
          rw [Real.norm_of_nonneg (tsum_nonneg (hnn ω))]
          exact hasSum_le h (Summable.of_nonneg_of_le (hnn ω) h hs.summable).hasSum hs
    have hopt' := hbest c' (kamB b T θ) hfθ hadm'
    -- integrability of the shifted utility at `T`
    have hshift : Integrable (fun ω => u (c T ω + θ * k T ω)) S.μ := by
      refine Integrable.mono' ((hadm.integrable hβ T).abs.add (hint T))
        (huc.comp_aestronglyMeasurable ((hcm T).add ((hkm T).const_mul θ))) ?_
      filter_upwards [hk0 T] with ω hkω
      rw [Real.norm_eq_abs]
      exact abs_shift_le hconc hmono hu hkω hθ0.le hθ1
    -- the pointwise lower bound on the deviation's realised utility
    have hlow : ∀ᵐ ω ∂S.μ, ∑' n, β ^ n * u (c n ω) +
        β ^ T * (u (c T ω + θ * k T ω) - u (c T ω)) - θ * tail β y u s c T ω ≤
          ∑' n, β ^ n * u (c' n ω) := by
      filter_upwards [hsc', hse', hadm'.summable hβ.le] with ω h1 h2 h3
      have hf : Summable fun n => β ^ n * (u (c n ω) - u (y - s n ω)) :=
        (h1.sub h2).congr fun n => by ring
      have htl := hasSum_ite_lt hf T
      have htl' : HasSum (fun n => if T < n then β ^ n * (u (c n ω) - u (y - s n ω)) else 0)
          (tail β y u s c T ω) := htl.summable.hasSum
      have hh := (h1.hasSum.add (hasSum_ite_eq T (β ^ T * (u (c T ω + θ * k T ω) -
        u (c T ω))))).sub (htl'.mul_left θ)
      refine hasSum_le (fun n => ?_) hh h3.hasSum
      have hbn := pow_nonneg hβ.le n
      rcases lt_trichotomy n T with hn | hn | hn
      · simp only [hc', kamC, hn, ↓reduceIte, hn.ne, (show ¬ T < n by omega)]
        linarith
      · subst hn
        simp only [hc', kamC, lt_irrefl, ↓reduceIte]
        linarith
      · simp only [hc', kamC, (show ¬ n < T by omega), (show n ≠ T by omega), hn, ↓reduceIte]
        have hcv := hconc.2 (Set.mem_univ (c n ω)) (Set.mem_univ (y - s n ω))
          (show 0 ≤ 1 - θ by linarith) hθ0.le (by ring)
        simp only [smul_eq_mul] at hcv
        nlinarith [mul_le_mul_of_nonneg_left hcv hbn]
    have i4 : Integrable (fun ω => u (c T ω + θ * k T ω) - u (c T ω)) S.μ :=
      hshift.sub (hadm.integrable hβ T)
    have i3 : Integrable (fun ω => β ^ T * (u (c T ω + θ * k T ω) - u (c T ω))) S.μ :=
      i4.const_mul _
    have i1 : Integrable (fun ω => ∑' n, β ^ n * u (c n ω) +
        β ^ T * (u (c T ω + θ * k T ω) - u (c T ω))) S.μ :=
      (hadm.integrable_sum hβ.le).add i3
    have i2 : Integrable (fun ω => θ * tail β y u s c T ω) S.μ := (htail_i T).const_mul θ
    have hmono_int : ∫ ω, (∑' n, β ^ n * u (c n ω) +
        β ^ T * (u (c T ω + θ * k T ω) - u (c T ω)) - θ * tail β y u s c T ω) ∂S.μ ≤
          ∫ ω, ∑' n, β ^ n * u (c' n ω) ∂S.μ :=
      integral_mono_ae (i1.sub i2) (hadm'.integrable_sum hβ.le) hlow
    rw [integral_sub i1 i2, integral_add (hadm.integrable_sum hβ.le) i3, integral_const_mul,
      integral_const_mul, integral_sub hshift (hadm.integrable hβ T)] at hmono_int
    have hgain : β ^ T * (∫ ω, u (c T ω + θ * k T ω) ∂S.μ - ∫ ω, u (c T ω) ∂S.μ) ≤
        θ * ∫ ω, tail β y u s c T ω ∂S.μ := by
      unfold expUtil at hopt'
      linarith
    -- the tangent bound
    have hkd_i : Integrable (fun ω => k T ω * u' (c T ω + θ * k T ω)) S.μ := by
      refine Integrable.mono' (hint T) ((hkm T).mul (hu'.comp_aestronglyMeasurable
        ((hcm T).add ((hkm T).const_mul θ)))) ?_
      filter_upwards [hk0 T] with ω hkω
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hkω (hu'0 _)), mul_comm]
      exact mul_le_mul_of_nonneg_right (hanti (by nlinarith)) hkω
    have htan : θ * ∫ ω, k T ω * u' (c T ω + θ * k T ω) ∂S.μ ≤
        ∫ ω, u (c T ω + θ * k T ω) ∂S.μ - ∫ ω, u (c T ω) ∂S.μ := by
      rw [← integral_const_mul, ← integral_sub hshift (hadm.integrable hβ T)]
      refine integral_mono (hkd_i.const_mul θ) (hshift.sub (hadm.integrable hβ T)) fun ω => ?_
      have := sub_ge_mul_deriv hconc hu (c T ω) (θ * k T ω)
      simp only
      linarith
    have hbT := pow_pos hβ T
    have h3 : θ * (β ^ T * ∫ ω, k T ω * u' (c T ω + θ * k T ω) ∂S.μ) ≤
        θ * ∫ ω, tail β y u s c T ω ∂S.μ := by
      nlinarith [mul_le_mul_of_nonneg_left htan hbT.le]
    exact le_of_mul_le_mul_left h3 hθ0
  -- let `θ → 0` (dominated convergence)
  have key2 : ∀ T, β ^ T * ∫ ω, u' (c T ω) * k T ω ∂S.μ ≤ ∫ ω, tail β y u s c T ω ∂S.μ := by
    intro T
    have hlim : Tendsto (fun m : ℕ => ∫ ω, k T ω * u' (c T ω + 1 / ((m : ℝ) + 1) * k T ω) ∂S.μ)
        atTop (𝓝 (∫ ω, k T ω * u' (c T ω) ∂S.μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => u' (c T ω) * k T ω)
        (fun m => (hkm T).mul (hu'.comp_aestronglyMeasurable
          ((hcm T).add ((hkm T).const_mul _)))) (hint T) (fun m => ?_) ?_
      · filter_upwards [hk0 T] with ω hkω
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hkω (hu'0 _)), mul_comm]
        have : 0 ≤ 1 / ((m : ℝ) + 1) * k T ω := mul_nonneg (by positivity) hkω
        exact mul_le_mul_of_nonneg_right (hanti (by linarith)) hkω
      · refine Eventually.of_forall fun ω => ?_
        have h1 : Tendsto (fun m : ℕ => c T ω + 1 / ((m : ℝ) + 1) * k T ω) atTop
            (𝓝 (c T ω)) := by
          simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (k T ω)).const_add
            (c T ω)
        exact ((hu'.tendsto _).comp h1).const_mul (k T ω)
    have hle : ∀ m : ℕ, β ^ T * ∫ ω, k T ω * u' (c T ω + 1 / ((m : ℝ) + 1) * k T ω) ∂S.μ ≤
        ∫ ω, tail β y u s c T ω ∂S.μ := fun m =>
      key T _ (by positivity) (by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have := le_of_tendsto' (hlim.const_mul (β ^ T)) hle
    simpa only [mul_comm (k T _)] using this
  -- the tail of expected utility vanishes
  have hR : Tendsto (fun T => ∫ ω, tail β y u s c T ω ∂S.μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence G htail_m hGi
      (fun T => (htail_bd T).mono fun ω h => by rwa [Real.norm_eq_abs]) (f := fun _ => 0) ?_
    · simpa using h
    · filter_upwards [hsc', hse'] with ω h1 h2
      have hf : Summable fun n => β ^ n * (u (c n ω) - u (y - s n ω)) :=
        (h1.sub h2).congr fun n => by ring
      have e : ∀ T, tail β y u s c T ω = ∑' n, β ^ n * (u (c n ω) - u (y - s n ω)) -
          ∑ n ∈ Finset.range (T + 1), β ^ n * (u (c n ω) - u (y - s n ω)) :=
        fun T => (hasSum_ite_lt hf T).tsum_eq
      simp_rw [e]
      have := (tendsto_const_nhds (x := ∑' n, β ^ n * (u (c n ω) - u (y - s n ω)))).sub
        (hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
      simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR (fun T => ?_) key2
  exact mul_nonneg (pow_nonneg hβ.le T) (integral_nonneg_of_ae
    ((hk0 T).mono fun ω h => mul_nonneg (hu'0 _) h))

/-! ### From the end-of-period to the beginning-of-period transversality condition -/

/-- Cochrane (2023), p. 22 (`E_t` of a nonnegative payoff times a nonnegative position): if
`Z ≥ 0` is known at `t`, `X ≥ 0` is integrable and `Z E_t X` is integrable, then `Z X` is
integrable and `E[Z X] = E[Z E_t X]`. No bound on `Z` is assumed; the proof truncates `Z` and
uses monotone convergence. -/
theorem integrable_mul_of_E {t : ℕ} {Z X : Ω → ℝ} (hZ : StronglyMeasurable[S.𝓕 t] Z)
    (hZ0 : ∀ᵐ ω ∂S.μ, 0 ≤ Z ω) (hX : Integrable X S.μ) (hX0 : ∀ᵐ ω ∂S.μ, 0 ≤ X ω)
    (hZE : Integrable (fun ω => Z ω * S.E t X ω) S.μ) :
    Integrable (fun ω => Z ω * X ω) S.μ ∧
      ∫ ω, Z ω * X ω ∂S.μ = ∫ ω, Z ω * S.E t X ω ∂S.μ := by
  set Zm : ℕ → Ω → ℝ := fun m ω => min (Z ω) m with hZmdef
  have hZm : ∀ m, StronglyMeasurable[S.𝓕 t] (Zm m) := fun m =>
    (hZ.measurable.min measurable_const).stronglyMeasurable
  have hZmb : ∀ m : ℕ, ∀ᵐ ω ∂S.μ, |Zm m ω| ≤ m := fun m => hZ0.mono fun ω h => by
    rw [abs_of_nonneg (le_min h (Nat.cast_nonneg m))]
    exact min_le_right _ _
  have hEX0 : ∀ᵐ ω ∂S.μ, 0 ≤ S.E t X ω := condExp_nonneg (m := S.𝓕 t) hX0
  have hZa : AEStronglyMeasurable Z S.μ := (hZ.mono (S.𝓕.le t)).aestronglyMeasurable
  have hZma : ∀ m, AEStronglyMeasurable (Zm m) S.μ := fun m =>
    ((hZm m).mono (S.𝓕.le t)).aestronglyMeasurable
  have hi_m : ∀ m, Integrable (fun ω => Zm m ω * X ω) S.μ := fun m =>
    hX.bdd_mul (hZma m) ((hZmb m).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hiE_m : ∀ m, Integrable (fun ω => Zm m ω * S.E t X ω) S.μ := fun m =>
    (S.integrable_E t X).bdd_mul (hZma m) ((hZmb m).mono fun ω h => by rwa [Real.norm_eq_abs])
  have heq_m : ∀ m : ℕ, ∫ ω, Zm m ω * X ω ∂S.μ = ∫ ω, Zm m ω * S.E t X ω ∂S.μ := fun m =>
    integral_mul_E (hZm m) (hZmb m) hX
  have hpt : ∀ ω, Tendsto (fun m : ℕ => Zm m ω) atTop (𝓝 (Z ω)) := fun ω =>
    tendsto_const_nhds.congr' ((eventually_ge_atTop ⌈Z ω⌉₊).mono fun m hm =>
      (min_eq_left ((Nat.le_ceil (Z ω)).trans (Nat.cast_le.2 hm))).symm)
  have hle_m : ∀ (m : ℕ) (ω : Ω), 0 ≤ Z ω → 0 ≤ Zm m ω ∧ Zm m ω ≤ Z ω := fun m ω h =>
    ⟨le_min h (Nat.cast_nonneg m), min_le_left _ _⟩
  have hlimE : Tendsto (fun m : ℕ => ∫ ω, Zm m ω * S.E t X ω ∂S.μ) atTop
      (𝓝 (∫ ω, Z ω * S.E t X ω ∂S.μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => Z ω * S.E t X ω)
      (fun m => (hiE_m m).aestronglyMeasurable) hZE (fun m => ?_)
      (Eventually.of_forall fun ω => (hpt ω).mul_const _)
    filter_upwards [hZ0, hEX0] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hle_m m ω h1).1 h2)]
    exact mul_le_mul_of_nonneg_right (hle_m m ω h1).2 h2
  have hfin : ∫⁻ ω, ENNReal.ofReal (Z ω * X ω) ∂S.μ ≤
      ENNReal.ofReal (∫ ω, Z ω * S.E t X ω ∂S.μ) := by
    have hl := lintegral_tendsto_of_tendsto_of_monotone
      (f := fun m ω => ENNReal.ofReal (Zm m ω * X ω))
      (F := fun ω => ENNReal.ofReal (Z ω * X ω))
      (fun m => (hi_m m).aemeasurable.ennreal_ofReal)
      (by
        filter_upwards [hX0] with ω hx m₁ m₂ h
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (min_le_min_left _ (Nat.cast_le.2 h)) hx))
      (Eventually.of_forall fun ω =>
        (ENNReal.continuous_ofReal.tendsto _).comp ((hpt ω).mul_const _))
    refine le_of_tendsto' hl fun m => ?_
    have hnn : 0 ≤ᵐ[S.μ] fun ω => Zm m ω * X ω := by
      filter_upwards [hZ0, hX0] with ω h1 h2
      exact mul_nonneg (hle_m m ω h1).1 h2
    rw [← ofReal_integral_eq_lintegral_ofReal (hi_m m) hnn, heq_m m]
    refine ENNReal.ofReal_le_ofReal (integral_mono_ae (hiE_m m) hZE ?_)
    filter_upwards [hZ0, hEX0] with ω h1 h2
    exact mul_le_mul_of_nonneg_right (hle_m m ω h1).2 h2
  have hnnZX : 0 ≤ᵐ[S.μ] fun ω => Z ω * X ω := by
    filter_upwards [hZ0, hX0] with ω h1 h2
    exact mul_nonneg h1 h2
  have hZXi : Integrable (fun ω => Z ω * X ω) S.μ :=
    ⟨hZa.mul hX.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnnZX).2 (hfin.trans_lt ENNReal.ofReal_lt_top)⟩
  have hlimX : Tendsto (fun m : ℕ => ∫ ω, Zm m ω * X ω ∂S.μ) atTop
      (𝓝 (∫ ω, Z ω * X ω ∂S.μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => Z ω * X ω)
      (fun m => (hi_m m).aestronglyMeasurable) hZXi (fun m => ?_)
      (Eventually.of_forall fun ω => (hpt ω).mul_const _)
    filter_upwards [hZ0, hX0] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hle_m m ω h1).1 h2)]
    exact mul_le_mul_of_nonneg_right (hle_m m ω h1).2 h2
  refine ⟨hZXi, tendsto_nhds_unique hlimX ?_⟩
  simpa only [heq_m] using hlimE

/-- Cochrane (2023), p. 22, eq. (2.6) in marginal-utility form: given the Euler inequality
`β E_T[u'(c_{T+1})/P_{T+1}] ≤ Q_T u'(c_T)/P_T` at every date (`HouseholdMeasure.euler_kkt`),
nonnegative bonds known when bought, `u' ≥ 0`, positive prices and the integrability of the
quantities involved, the end-of-period condition `β^T E[u'(c_T) Q_T B_T/P_T] → 0` implies the
beginning-of-period transversality condition `β^N E[u'(c_N) B_{N−1}/P_N] → 0`. -/
theorem tvc_of_kkt {β : ℝ} (hβ : 0 < β) {u' : ℝ → ℝ} (hu'0 : ∀ x, 0 ≤ u' x)
    {P Q c b : ℕ → Ω → ℝ} (hbad : ∀ n, StronglyMeasurable[S.𝓕 n] (b (n + 1)))
    (hbnn : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ b n ω) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hX : ∀ T, Integrable (fun ω => u' (c (T + 1) ω) / P (T + 1) ω) S.μ)
    (hW : ∀ N, Integrable (fun ω => u' (c N ω) * b N ω / P N ω) S.μ)
    (hint : ∀ T, Integrable (fun ω => u' (c T ω) * (Q T ω * b (T + 1) ω / P T ω)) S.μ)
    (hkkt : ∀ T, ∀ᵐ ω ∂S.μ, β * S.E T (fun ω => u' (c (T + 1) ω) / P (T + 1) ω) ω ≤
      Q T ω * (u' (c T ω) / P T ω))
    (hend : Tendsto (fun T => β ^ T * ∫ ω, u' (c T ω) * (Q T ω * b (T + 1) ω / P T ω) ∂S.μ)
      atTop (𝓝 0)) :
    Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0) := by
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hend (fun T => ?_)
    (fun T => ?_)
  · refine mul_nonneg (pow_nonneg hβ.le _) (integral_nonneg_of_ae ?_)
    filter_upwards [hbnn (T + 1), hP (T + 1)] with ω h1 h2
    exact div_nonneg (mul_nonneg (hu'0 _) h1) h2.le
  · set X : Ω → ℝ := fun ω => u' (c (T + 1) ω) / P (T + 1) ω with hXdef
    have hbX : (fun ω => u' (c (T + 1) ω) * b (T + 1) ω / P (T + 1) ω) =
        b (T + 1) * X := by
      funext ω
      simp only [hXdef, Pi.mul_apply]
      ring
    have hpo := condExp_mul_of_stronglyMeasurable_left (hbad T) (hbX ▸ hW (T + 1)) (hX T)
    have h1 : ∫ ω, u' (c (T + 1) ω) * b (T + 1) ω / P (T + 1) ω ∂S.μ =
        ∫ ω, b (T + 1) ω * S.E T X ω ∂S.μ := by
      rw [hbX, ← S.integral_E T (b (T + 1) * X)]
      exact integral_congr_ae hpo
    have hi : Integrable (fun ω => b (T + 1) ω * S.E T X ω) S.μ :=
      (S.integrable_E T (b (T + 1) * X)).congr hpo
    have h2 : β * ∫ ω, b (T + 1) ω * S.E T X ω ∂S.μ ≤
        ∫ ω, u' (c T ω) * (Q T ω * b (T + 1) ω / P T ω) ∂S.μ := by
      rw [← integral_const_mul]
      refine integral_mono_ae (hi.const_mul β) (hint T) ?_
      filter_upwards [hkkt T, hbnn (T + 1)] with ω hk hb
      have := mul_le_mul_of_nonneg_left hk hb
      calc β * (b (T + 1) ω * S.E T X ω) = b (T + 1) ω * (β * S.E T X ω) := by ring
        _ ≤ b (T + 1) ω * (Q T ω * (u' (c T ω) / P T ω)) := this
        _ = u' (c T ω) * (Q T ω * b (T + 1) ω / P T ω) := by ring
    rw [h1, pow_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ.le T)

/-- Cochrane (2023), p. 22, "Household maximization ... also imply the household transversality
condition (2.6)", derived on a genuine probability space with information growing forever: in
an optimal plan with concave, increasing, differentiable `u` (continuous `u'`), positive prices,
nonnegative bond prices, adapted prices, bond prices and taxes, an admissible after-tax
endowment plan, `EulerRegular` at every date and the integrability of
`u'(c_N) B_{N−1}/P_N` and `u'(c_T) Q_T B_T/P_T`, the transversality condition
`lim_N β^N E[u'(c_N) B_{N−1}/P_N] = 0` holds. -/
theorem tvc_of_optimal {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ c b) (hPad : StronglyAdapted S.𝓕 P)
    (hQad : StronglyAdapted S.𝓕 Q) (hsad : StronglyAdapted S.𝓕 s)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) (hQ : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ Q n ω)
    (he : Admissible S β u (fun n ω => y - s n ω)) (hreg : ∀ T, EulerRegular S P Q c T)
    (hW : ∀ N, Integrable (fun ω => u' (c N ω) * b N ω / P N ω) S.μ)
    (hint : ∀ T, Integrable (fun ω => u' (c T ω) * (Q T ω * b (T + 1) ω / P T ω)) S.μ) :
    Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0) :=
  tvc_of_kkt hβ (fun x => Valuation.deriv_nonneg_of_monotone hmono (hu x)) hopt.1.2.2.1
    hopt.1.2.2.2.2 hP (fun T => margUtil_integrable hu' hopt.1.2.1 hPad (hreg T)) hW hint
    (fun T => euler_kkt hβ hu hu' hopt hPad hP (hQad T) (hreg T))
    (tvc_end_of_optimal hβ hu hu' hconc hmono hopt hPad hQad hsad hP hQ he hint)

/-! ### Sufficiency: concavity, Euler equation and transversality -/

/-- Cochrane (2023), p. 22: the partial sums of the utility difference of two admissible plans
converge in expectation, `∑_{n<N} β^n (E u(c'_n) − E u(c_n)) → E ∑ β^n u(c'_n) − E ∑ β^n u(c_n)`
(dominated convergence). -/
theorem tendsto_partial_utilDiff {β : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} {c c' : ℕ → Ω → ℝ}
    (hadm : Admissible S β u c) (hadm' : Admissible S β u c') :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
        β ^ n * (∫ ω, u (c' n ω) ∂S.μ - ∫ ω, u (c n ω) ∂S.μ)) atTop
      (𝓝 (expUtil S β u c' - expUtil S β u c)) := by
  have hci := hadm.integrable hβ
  have hc'i := hadm'.integrable hβ
  have hfi : ∀ n, Integrable (fun ω => β ^ n * u (c' n ω) - β ^ n * u (c n ω)) S.μ := fun n =>
    ((hc'i n).const_mul _).sub ((hci n).const_mul _)
  have e : ∀ N, ∑ n ∈ Finset.range N, β ^ n * (∫ ω, u (c' n ω) ∂S.μ - ∫ ω, u (c n ω) ∂S.μ) =
      ∫ ω, ∑ n ∈ Finset.range N, (β ^ n * u (c' n ω) - β ^ n * u (c n ω)) ∂S.μ := by
    intro N
    rw [integral_finsetSum _ fun n _ => hfi n]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_sub ((hc'i n).const_mul _) ((hci n).const_mul _), integral_const_mul,
      integral_const_mul, mul_sub]
  simp_rw [e]
  have he : expUtil S β u c' - expUtil S β u c =
      ∫ ω, (∑' n, β ^ n * u (c' n ω) - ∑' n, β ^ n * u (c n ω)) ∂S.μ := by
    unfold expUtil
    rw [integral_sub (hadm'.integrable_sum hβ.le) (hadm.integrable_sum hβ.le)]
  rw [he]
  refine tendsto_integral_of_dominated_convergence
    (fun ω => ∑' n, β ^ n * |u (c' n ω)| + ∑' n, β ^ n * |u (c n ω)|)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => (hfi n).aestronglyMeasurable)
    (hadm'.2.2.add hadm.2.2) (fun N => ?_) ?_
  · filter_upwards [hadm.2.1, hadm'.2.1] with ω h1 h2
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ n, |β ^ n * u (c' n ω) - β ^ n * u (c n ω)| ≤
        β ^ n * |u (c' n ω)| + β ^ n * |u (c n ω)| := fun n => by
      rw [← mul_sub, abs_mul, abs_pow, abs_of_nonneg hβ.le, ← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (pow_nonneg hβ.le n)
    refine (Finset.sum_le_sum fun n _ => hle n).trans ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add
      (h2.sum_le_tsum _ fun n _ => mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _))
      (h1.sum_le_tsum _ fun n _ => mul_nonneg (pow_nonneg hβ.le n) (abs_nonneg _))
  · filter_upwards [hadm.summable hβ.le, hadm'.summable hβ.le] with ω h1 h2
    have := (h2.sub h1).hasSum.tendsto_sum_nat
    rwa [h2.tsum_sub h1] at this

/-- Cochrane (2023), p. 21 and Online Appendix A1.1, p. 556, **sufficiency** on a genuine
probability space: a feasible admissible plan with concave, increasing, differentiable `u`,
positive prices, the Euler equation `Q_n u'(c_n)/P_n = β E_n[u'(c_{n+1})/P_{n+1}]` almost surely
at every date, integrable `u'(c_n)/P_n` and `u'(c_n) B_{n−1}/P_n`, and the transversality
condition `β^N E[u'(c_N) B_{N−1}/P_N] → 0`, is optimal. The comparison plans are arbitrary
feasible admissible plans: the integrability of their bond positions is proved date by date. -/
theorem optimal_of_euler_tvc {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    {P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ} (hfeas : Feasible S y P s Q b₀ c b)
    (hadm : Admissible S β u c) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hm : ∀ n, Integrable (fun ω => u' (c n ω) / P n ω) S.μ)
    (hW : ∀ n, Integrable (fun ω => u' (c n ω) * b n ω / P n ω) S.μ)
    (heul : ∀ n, ∀ᵐ ω ∂S.μ, Q n ω * (u' (c n ω) / P n ω) =
      β * S.E n (fun ω => u' (c (n + 1) ω) / P (n + 1) ω) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0)) :
    Optimal S β y u P s Q b₀ c b := by
  refine ⟨hfeas, hadm, fun c' b' hf' hadm' => ?_⟩
  obtain ⟨hb0, -, hbad, hflow, -⟩ := hfeas
  obtain ⟨hb0', -, hbad', hflow', hbnn'⟩ := hf'
  have hu'0 : ∀ x, 0 ≤ u' x := fun x => Valuation.deriv_nonneg_of_monotone hmono (hu x)
  have hci := hadm.integrable hβ
  have hc'i := hadm'.integrable hβ
  set m : ℕ → Ω → ℝ := fun n ω => u' (c n ω) / P n ω with hmdef
  set W : ℕ → Ω → ℝ := fun n ω => u' (c n ω) * b n ω / P n ω with hWdef
  set W' : ℕ → Ω → ℝ := fun n ω => u' (c n ω) * b' n ω / P n ω with hW'def
  set D : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N,
    β ^ n * (∫ ω, u (c' n ω) ∂S.μ - ∫ ω, u (c n ω) ∂S.μ) with hDdef
  have hm0 : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ m n ω := fun n =>
    (hP n).mono fun ω h => div_nonneg (hu'0 _) h.le
  -- the pointwise first-order bound at date `N`
  have hpt : ∀ N, ∀ᵐ ω ∂S.μ, u (c' N ω) - u (c N ω) ≤ W' N ω - W N ω -
      β * (b' (N + 1) ω * S.E N (m (N + 1)) ω) + β * (b (N + 1) ω * S.E N (m (N + 1)) ω) := by
    intro N
    filter_upwards [hflow N, hflow' N, hP N, heul N] with ω h1 h2 hp he
    have ht := Valuation.concave_le_tangent hconc (hu (c N ω)) (c' N ω)
    have hp0 := hp.ne'
    have hfd : b' N ω - b N ω - Q N ω * b' (N + 1) ω + Q N ω * b (N + 1) ω =
        P N ω * (c' N ω - c N ω) := by linarith
    have e : u' (c N ω) * (c' N ω - c N ω) = W' N ω - W N ω -
        Q N ω * (u' (c N ω) / P N ω) * b' (N + 1) ω +
          Q N ω * (u' (c N ω) / P N ω) * b (N + 1) ω := by
      calc u' (c N ω) * (c' N ω - c N ω) =
            u' (c N ω) / P N ω * (P N ω * (c' N ω - c N ω)) := by field_simp
        _ = u' (c N ω) / P N ω * (b' N ω - b N ω - Q N ω * b' (N + 1) ω +
            Q N ω * b (N + 1) ω) := by rw [hfd]
        _ = _ := by simp only [hW'def, hWdef]; ring
    rw [he] at e
    have : m (N + 1) = fun ω => u' (c (N + 1) ω) / P (N + 1) ω := rfl
    rw [this]
    linarith
  -- the induction
  have claim : ∀ N, Integrable (W' N) S.μ ∧
      D N ≤ β ^ N * (∫ ω, W N ω ∂S.μ - ∫ ω, W' N ω ∂S.μ) := by
    intro N
    induction N with
    | zero =>
      have e : W' 0 = W 0 := by
        funext ω
        simp only [hW'def, hWdef, hb0, hb0']
      refine ⟨e ▸ hW 0, ?_⟩
      simp [hDdef, e]
    | succ N ih =>
      obtain ⟨hiW', hD⟩ := ih
      have hbm : ∀ (bb : ℕ → Ω → ℝ), (fun ω => u' (c (N + 1) ω) * bb (N + 1) ω /
          P (N + 1) ω) = bb (N + 1) * m (N + 1) := fun bb => by
        funext ω
        simp only [hmdef, Pi.mul_apply]
        ring
      -- the candidate's term
      have hpoC := condExp_mul_of_stronglyMeasurable_left (hbad N)
        ((hbm b) ▸ hW (N + 1)) (hm (N + 1))
      have hVC_i : Integrable (fun ω => b (N + 1) ω * S.E N (m (N + 1)) ω) S.μ :=
        (S.integrable_E N _).congr hpoC
      have hVC_eq : ∫ ω, b (N + 1) ω * S.E N (m (N + 1)) ω ∂S.μ = ∫ ω, W (N + 1) ω ∂S.μ := by
        have : W (N + 1) = b (N + 1) * m (N + 1) := hbm b
        rw [this, ← S.integral_E N (b (N + 1) * m (N + 1))]
        exact (integral_congr_ae hpoC).symm
      -- the comparison plan's term
      have hEm0 : ∀ᵐ ω ∂S.μ, 0 ≤ S.E N (m (N + 1)) ω := condExp_nonneg (m := S.𝓕 N) (hm0 (N + 1))
      have hV0 : ∀ᵐ ω ∂S.μ, 0 ≤ b' (N + 1) ω * S.E N (m (N + 1)) ω := by
        filter_upwards [hbnn' (N + 1), hEm0] with ω h1 h2
        exact mul_nonneg h1 h2
      have hVm : AEStronglyMeasurable (fun ω => b' (N + 1) ω * S.E N (m (N + 1)) ω) S.μ :=
        ((hbad' N).mono (S.𝓕.le N)).aestronglyMeasurable.mul
          (S.integrable_E N _).aestronglyMeasurable
      have hbound_i : Integrable (fun ω => β⁻¹ * (W' N ω - W N ω +
          β * (b (N + 1) ω * S.E N (m (N + 1)) ω) - (u (c' N ω) - u (c N ω)))) S.μ :=
        ((((hiW'.sub (hW N)).add (hVC_i.const_mul β)).sub
          ((hc'i N).sub (hci N)))).const_mul _
      have hV_i : Integrable (fun ω => b' (N + 1) ω * S.E N (m (N + 1)) ω) S.μ := by
        refine Integrable.mono' hbound_i hVm ?_
        filter_upwards [hpt N, hV0] with ω h1 h2
        rw [Real.norm_eq_abs, abs_of_nonneg h2, le_inv_mul_iff₀ hβ]
        linarith
      obtain ⟨hiW'1, hW'eq⟩ := integrable_mul_of_E (hbad' N) (hbnn' (N + 1)) (hm (N + 1))
        (hm0 (N + 1)) hV_i
      have hW'1 : W' (N + 1) = fun ω => b' (N + 1) ω * m (N + 1) ω := hbm b'
      -- integrate the pointwise bound
      have hI : ∫ ω, u (c' N ω) ∂S.μ - ∫ ω, u (c N ω) ∂S.μ ≤
          ∫ ω, W' N ω ∂S.μ - ∫ ω, W N ω ∂S.μ -
            β * ∫ ω, b' (N + 1) ω * S.E N (m (N + 1)) ω ∂S.μ +
              β * ∫ ω, b (N + 1) ω * S.E N (m (N + 1)) ω ∂S.μ := by
        have iA : Integrable (fun ω => u (c' N ω) - u (c N ω)) S.μ := (hc'i N).sub (hci N)
        have iB : Integrable (fun ω => W' N ω - W N ω) S.μ := hiW'.sub (hW N)
        have iC : Integrable (fun ω => β * (b' (N + 1) ω * S.E N (m (N + 1)) ω)) S.μ :=
          hV_i.const_mul β
        have iD : Integrable (fun ω => β * (b (N + 1) ω * S.E N (m (N + 1)) ω)) S.μ :=
          hVC_i.const_mul β
        have iBC : Integrable (fun ω => W' N ω - W N ω -
            β * (b' (N + 1) ω * S.E N (m (N + 1)) ω)) S.μ := iB.sub iC
        have hmono : ∫ ω, (u (c' N ω) - u (c N ω)) ∂S.μ ≤
            ∫ ω, (W' N ω - W N ω - β * (b' (N + 1) ω * S.E N (m (N + 1)) ω) +
              β * (b (N + 1) ω * S.E N (m (N + 1)) ω)) ∂S.μ :=
          integral_mono_ae iA (iBC.add iD) (hpt N)
        rw [integral_sub (hc'i N) (hci N), integral_add iBC iD, integral_sub iB iC,
          integral_sub hiW' (hW N), integral_const_mul, integral_const_mul] at hmono
        exact hmono
      refine ⟨hW'1 ▸ hiW'1, ?_⟩
      have hDs : D (N + 1) = D N +
          β ^ N * (∫ ω, u (c' N ω) ∂S.μ - ∫ ω, u (c N ω) ∂S.μ) := by
        simp only [hDdef, Finset.sum_range_succ]
      rw [hDs, hW'1, hW'eq, ← hVC_eq, pow_succ]
      have hbN := pow_nonneg hβ.le N
      nlinarith [mul_le_mul_of_nonneg_left hI hbN]
  have hD_le : ∀ N, D N ≤ β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ := by
    intro N
    obtain ⟨-, hD⟩ := claim N
    have hW'0 : 0 ≤ ∫ ω, W' N ω ∂S.μ := integral_nonneg_of_ae (by
      filter_upwards [hbnn' N, hP N] with ω h1 h2
      exact div_nonneg (mul_nonneg (hu'0 _) h1) h2.le)
    have := mul_nonneg (pow_nonneg hβ.le N) hW'0
    have e : ∫ ω, W N ω ∂S.μ = ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ := rfl
    nlinarith
  have hlim := le_of_tendsto_of_tendsto' (tendsto_partial_utilDiff hβ hadm hadm') htvc hD_le
  linarith

/-! ### Equilibrium: the transversality condition (2.6) and the valuation equation (2.7) -/

/-- Cochrane (2023), p. 21: a plan with uniformly essentially bounded consumption has absolutely
convergent expected discounted utility (`0 ≤ β < 1`, `u` continuous). -/
theorem admissible_of_bdd {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℝ → ℝ} (huc : Continuous u)
    {c : ℕ → Ω → ℝ} (hcm : ∀ n, AEStronglyMeasurable (c n) S.μ) {M : ℝ}
    (hM : ∀ n, ∀ᵐ ω ∂S.μ, |c n ω| ≤ M) : Admissible S β u c := by
  obtain ⟨C, -, hC⟩ := exists_abs_le_of_continuous huc M
  have hall := ae_all_iff.2 hM
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right C
  have hle : ∀ ω, (∀ n, |c n ω| ≤ M) → ∀ n, β ^ n * |u (c n ω)| ≤ β ^ n * C := fun ω h n =>
    mul_le_mul_of_nonneg_left (hC _ (h n)) (pow_nonneg hβ0 n)
  have hnn : ∀ ω n, 0 ≤ β ^ n * |u (c n ω)| := fun ω n =>
    mul_nonneg (pow_nonneg hβ0 n) (abs_nonneg _)
  have hsum : ∀ᵐ ω ∂S.μ, Summable fun n => β ^ n * |u (c n ω)| := by
    filter_upwards [hall] with ω h
    exact Summable.of_nonneg_of_le (hnn ω) (hle ω h) hg.summable
  refine ⟨fun n => huc.comp_aestronglyMeasurable (hcm n), hsum, ?_⟩
  refine Integrable.of_bound (aestronglyMeasurable_tsum
    (fun n => (huc.comp_aestronglyMeasurable (hcm n)).norm.const_mul _) hsum)
    ((1 - β)⁻¹ * C) ?_
  filter_upwards [hall, hsum] with ω h hs
  rw [Real.norm_of_nonneg (tsum_nonneg (hnn ω))]
  exact hasSum_le (hle ω h) hs.hasSum hg

/-- Cochrane (2023), eqs. (2.3)–(2.4), p. 22, on a probability space: at the equilibrium `c = y`
with the bond price (2.3) `Q_n = β E_n(P_n/P_{n+1})`, the real value of the debt carried out of
date `n` is `Q_n B_n/P_n = β E_n x_{n+1}` almost surely (`x_n = B_{n−1}/P_n`). -/
theorem endDebt_ae {β y : ℝ} {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hf : Feasible S y P s Q b₀ (fun _ _ => y) b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hQ : ∀ n, Q n =ᵐ[S.μ] β • S.E n (fun ω => P n ω / P (n + 1) ω))
    (hPP : ∀ n, Integrable (fun ω => P n ω / P (n + 1) ω) S.μ)
    (hx : ∀ n, Integrable (fun ω => b n ω / P n ω) S.μ) (n : ℕ) :
    (fun ω => Q n ω * b (n + 1) ω / P n ω) =ᵐ[S.μ]
      β • S.E n (fun ω => b (n + 1) ω / P (n + 1) ω) := by
  set f : Ω → ℝ := fun ω => b (n + 1) ω / P n ω with hfdef
  set g : Ω → ℝ := fun ω => P n ω / P (n + 1) ω with hgdef
  have hfm : StronglyMeasurable[S.𝓕 n] f :=
    ((hf.2.2.1 n).measurable.div (hPad n).measurable).stronglyMeasurable
  have hfg : f * g =ᵐ[S.μ] fun ω => b (n + 1) ω / P (n + 1) ω := by
    filter_upwards [hP n] with ω hp
    have := hp.ne'
    simp only [hfdef, hgdef, Pi.mul_apply]
    field_simp
  have hpo := condExp_mul_of_stronglyMeasurable_left hfm ((hx (n + 1)).congr hfg.symm) (hPP n)
  filter_upwards [hQ n, hpo, S.E_congr hfg n] with ω hq h2 h3
  have h2' : S.E n (f * g) ω = f ω * S.E n g ω := h2
  rw [Pi.smul_apply, smul_eq_mul, ← h3, h2', hq, Pi.smul_apply, smul_eq_mul]
  simp only [hfdef]
  ring

/-- Cochrane (2023), eq. (2.5), p. 22, on a probability space: at the equilibrium `c = y` with the
bond price (2.3), the flow constraint (2.4) gives `x_n = s_n + β E_n x_{n+1}` almost surely at
every date, `x_n = B_{n−1}/P_n`. -/
theorem flowX_of_feasible {β y : ℝ} {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hf : Feasible S y P s Q b₀ (fun _ _ => y) b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hQ : ∀ n, Q n =ᵐ[S.μ] β • S.E n (fun ω => P n ω / P (n + 1) ω))
    (hPP : ∀ n, Integrable (fun ω => P n ω / P (n + 1) ω) S.μ)
    (hx : ∀ n, Integrable (fun ω => b n ω / P n ω) S.μ) (n : ℕ) :
    (fun ω => b n ω / P n ω) =ᵐ[S.μ]
      s n + β • S.E n (fun ω => b (n + 1) ω / P (n + 1) ω) := by
  filter_upwards [hf.2.2.2.1 n, hP n, endDebt_ae hf hPad hP hQ hPP hx n] with ω h1 hp h2
  rw [Pi.add_apply, ← h2]
  have := hp.ne'
  field_simp
  linarith

/-- Cochrane (2023), p. 22 ("iterate (2.5)") on a probability space: if
`x_n = s_n + β E_n x_{n+1}` almost surely at every date, with integrable adapted `s`, then
`x_t = ∑_{j ≤ N} β^j E_t s_{t+j} + β^{N+1} E_t x_{t+N+1}` almost surely. -/
theorem telescope_ae {β : ℝ} {x s : ℕ → Ω → ℝ}
    (hflow : ∀ n, x n =ᵐ[S.μ] s n + β • S.E n (x (n + 1))) (hsad : StronglyAdapted S.𝓕 s)
    (hsi : ∀ n, Integrable (s n) S.μ) (t N : ℕ) :
    x t =ᵐ[S.μ] fun ω => ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω +
      β ^ (N + 1) * S.E t (x (t + N + 1)) ω := by
  induction N with
  | zero =>
    filter_upwards [hflow t] with ω h
    rw [h]
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, add_zero, pow_one,
      S.E_of_stronglyMeasurable (hsad t) (hsi t), Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  | succ N ih =>
    have hEi : Integrable (β • S.E (t + N + 1) (x (t + N + 1 + 1))) S.μ :=
      (S.integrable_E _ _).smul β
    filter_upwards [ih, S.E_congr (hflow (t + N + 1)) t, S.E_add (hsi (t + N + 1)) hEi t,
      S.E_smul β (S.E (t + N + 1) (x (t + N + 1 + 1))) t,
      S.E_tower (show t ≤ t + N + 1 by omega) (x (t + N + 1 + 1))] with ω h0 h1 h2 h3 h4
    rw [h0, h1, h2, Pi.add_apply, h3, Pi.smul_apply, h4, smul_eq_mul,
      Finset.sum_range_succ (n := N + 1), show t + (N + 1) = t + N + 1 by omega,
      show t + N + 1 + 1 = t + (N + 1) + 1 by omega]
    ring

/-- Cochrane (2023), eqs. (2.6)–(2.7), p. 22, on a probability space with information growing
forever: if `x_n = s_n + β E_n x_{n+1}` almost surely at every date (`0 < β < 1`), surpluses are
adapted and uniformly essentially bounded, real debt is integrable and nonnegative, and the
unconditional transversality condition `β^N E x_N → 0` holds, then at every date `t`
almost surely the conditional transversality condition `β^N E_t x_{t+N} → 0` (2.6) holds and
`x_t = ∑_j β^j E_t s_{t+j}` (2.7). -/
theorem tvc_valuation_of_unconditional {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {x s : ℕ → Ω → ℝ}
    (hflow : ∀ n, x n =ᵐ[S.μ] s n + β • S.E n (x (n + 1))) (hsad : StronglyAdapted S.𝓕 s)
    {M : ℝ} (hsM : ∀ n, ∀ᵐ ω ∂S.μ, |s n ω| ≤ M) (hxi : ∀ n, Integrable (x n) S.μ)
    (hx0 : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ x n ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, x N ω ∂S.μ) atTop (𝓝 0)) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, Tendsto (fun N => β ^ N * S.E t (x (t + N)) ω) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t (s (t + j)) ω) (x t ω) := by
  have hsi : ∀ n, Integrable (s n) S.μ := fun n =>
    MeasExpectationSystem.BddRV.integrable
      ⟨((hsad n).mono (S.𝓕.le n)).aestronglyMeasurable, M, hsM n⟩
  have hEs : ∀ᵐ ω ∂S.μ, ∀ j, |S.E t (s (t + j)) ω| ≤ M :=
    ae_all_iff.2 fun j => S.abs_E_le (hsM (t + j)) t
  have hg := (hasSum_geometric_of_lt_one hβ.le hβ1).mul_right M
  have hsumm : ∀ᵐ ω ∂S.μ, Summable fun j => β ^ j * S.E t (s (t + j)) ω := by
    filter_upwards [hEs] with ω h
    refine Summable.of_norm_bounded hg.summable fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.le]
    exact mul_le_mul_of_nonneg_left (h j) (pow_nonneg hβ.le j)
  set pv : Ω → ℝ := fun ω => ∑' j, β ^ j * S.E t (s (t + j)) ω with hpv
  set F : ℕ → Ω → ℝ := fun N ω => β ^ (N + 1) * S.E t (x (t + N + 1)) ω with hF
  have htel := ae_all_iff.2 (telescope_ae hflow hsad hsi t)
  -- pointwise limit `x_t − pv_t`
  have hlimF : ∀ᵐ ω ∂S.μ, Tendsto (fun N => F N ω) atTop (𝓝 (x t ω - pv ω)) := by
    filter_upwards [htel, hsumm] with ω h1 h2
    have e : ∀ N, F N ω = x t ω - ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω :=
      fun N => by rw [h1 N]; simp only [hF]; ring
    simp_rw [e]
    exact tendsto_const_nhds.sub (h2.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  -- the bound
  have hpart : ∀ᵐ ω ∂S.μ, ∀ N, |∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω| ≤
      (1 - β)⁻¹ * M := by
    filter_upwards [hEs] with ω h N
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ j, |β ^ j * S.E t (s (t + j)) ω| ≤ β ^ j * M := fun j => by
      rw [abs_mul, abs_pow, abs_of_nonneg hβ.le]
      exact mul_le_mul_of_nonneg_left (h j) (pow_nonneg hβ.le j)
    refine (Finset.sum_le_sum fun j _ => hle j).trans ?_
    rw [← tsum_geometric_of_lt_one hβ.le hβ1, ← tsum_mul_right]
    exact hg.summable.sum_le_tsum _ fun j _ => mul_nonneg (pow_nonneg hβ.le j)
      ((abs_nonneg _).trans (h 0))
  have hFb : ∀ N, ∀ᵐ ω ∂S.μ, ‖F N ω‖ ≤ |x t ω| + (1 - β)⁻¹ * M := fun N => by
    filter_upwards [htel, hpart] with ω h1 h2
    have e : F N ω = x t ω - ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω := by
      rw [h1 N]; simp only [hF]; ring
    rw [Real.norm_eq_abs, e]
    exact (abs_sub _ _).trans (add_le_add le_rfl (h2 N))
  have hFm : ∀ N, AEStronglyMeasurable (F N) S.μ := fun N =>
    ((S.integrable_E t _).const_mul _).aestronglyMeasurable
  have hbi : Integrable (fun ω => |x t ω| + (1 - β)⁻¹ * M) S.μ :=
    (hxi t).abs.add (integrable_const _)
  -- the integral of the limit is zero
  have hintF : ∀ N, ∫ ω, F N ω ∂S.μ =
      (β ^ t)⁻¹ * (β ^ (t + N + 1) * ∫ ω, x (t + N + 1) ω ∂S.μ) :=
    fun N => by
      simp only [hF]
      rw [integral_const_mul, S.integral_E]
      have : β ^ t ≠ 0 := pow_ne_zero t hβ.ne'
      rw [show t + N + 1 = t + (N + 1) by omega, pow_add]
      field_simp
      ring
  have hF0 : Tendsto (fun N => ∫ ω, F N ω ∂S.μ) atTop (𝓝 0) := by
    have hmap : Tendsto (fun N : ℕ => t + N + 1) atTop atTop :=
      tendsto_atTop_mono (fun N => (by omega : N ≤ t + N + 1)) tendsto_id
    have h2 : Tendsto (fun N : ℕ => β ^ (t + N + 1) * ∫ ω, x (t + N + 1) ω ∂S.μ) atTop (𝓝 0) :=
      htvc.comp hmap
    rw [show (fun N => ∫ ω, F N ω ∂S.μ) = fun N =>
      (β ^ t)⁻¹ * (β ^ (t + N + 1) * ∫ ω, x (t + N + 1) ω ∂S.μ) from funext hintF]
    simpa using h2.const_mul (β ^ t)⁻¹
  have hFL := tendsto_integral_of_dominated_convergence _ hFm hbi hFb hlimF
  have hL0 : ∫ ω, (x t ω - pv ω) ∂S.μ = 0 := tendsto_nhds_unique hFL hF0
  have hLnn : 0 ≤ᵐ[S.μ] fun ω => x t ω - pv ω := by
    have hEx : ∀ N, ∀ᵐ ω ∂S.μ, 0 ≤ F N ω := fun N => by
      filter_upwards [condExp_nonneg (m := S.𝓕 t) (hx0 (t + N + 1))] with ω h
      exact mul_nonneg (pow_nonneg hβ.le _) h
    filter_upwards [hlimF, ae_all_iff.2 hEx] with ω h1 h2
    exact ge_of_tendsto' h1 h2
  have hLi : Integrable (fun ω => x t ω - pv ω) S.μ := by
    refine Integrable.mono' hbi (aestronglyMeasurable_of_tendsto_ae atTop hFm hlimF) ?_
    filter_upwards [hlimF, ae_all_iff.2 hFb] with ω h1 h2
    exact le_of_tendsto' h1.norm h2
  have hL := (integral_eq_zero_iff_of_nonneg_ae hLnn hLi).1 hL0
  refine ⟨?_, ?_⟩
  · filter_upwards [hlimF, hL] with ω h1 h2
    have h0 : x t ω - pv ω = 0 := h2
    rw [h0] at h1
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    refine h1.congr fun N => ?_
    simp only [hF, show t + N + 1 = t + (N + 1) by omega]
  · filter_upwards [hsumm, hL] with ω h1 h2
    have h0 : x t ω - pv ω = 0 := h2
    have : x t ω = pv ω := by linarith
    rw [this]
    exact h1.hasSum

/-- Cochrane (2023), p. 22, "Household maximization, budget constraint, and equilibrium `c_t = y`
also imply the household transversality condition (2.6) ... we can then iterate (2.5) to (2.7)",
derived on a genuine probability space with information growing forever (`0 < β < 1`). If the
endowment plan `c = y` with bonds `b` is optimal for concave, increasing, differentiable `u`
(continuous `u'`, `u'(y) > 0`), prices are positive, prices, bond prices and surpluses are
adapted, surpluses are uniformly essentially bounded, the bond price is (2.3)
`Q_n = β E_n(P_n/P_{n+1})`, and `P_n/P_{n+1}` and real debt `x_n = B_{n−1}/P_n` are
integrable, then:
* `β^N E x_N → 0` (unconditional transversality);
* (2.6) at every date `t`: almost surely `β^N E_t x_{t+N} → 0`;
* (2.7) at every date `t`: almost surely `x_t = ∑_j β^j E_t s_{t+j}`;
* `x_t = E_t ∑_j β^j s_{t+j}` almost surely (`forwardSol`). -/
theorem valuation_of_optimal_eqm {β y : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) (huy : 0 < u' y) {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S β y u P s Q b₀ (fun _ _ => y) b) (hPad : StronglyAdapted S.𝓕 P)
    (hQad : StronglyAdapted S.𝓕 Q) (hsad : StronglyAdapted S.𝓕 s)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {M : ℝ} (hsM : ∀ n, ∀ᵐ ω ∂S.μ, |s n ω| ≤ M)
    (hQ : ∀ n, Q n =ᵐ[S.μ] β • S.E n (fun ω => P n ω / P (n + 1) ω))
    (hPP : ∀ n, Integrable (fun ω => P n ω / P (n + 1) ω) S.μ)
    (hx : ∀ n, Integrable (fun ω => b n ω / P n ω) S.μ) (t : ℕ) :
    Tendsto (fun N => β ^ N * ∫ ω, b N ω / P N ω ∂S.μ) atTop (𝓝 0) ∧
      (∀ᵐ ω ∂S.μ, Tendsto (fun N => β ^ N * S.E t (fun ω => b (t + N) ω / P (t + N) ω) ω)
        atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t (s (t + j)) ω) (b t ω / P t ω)) ∧
      (fun ω => b t ω / P t ω) =ᵐ[S.μ] S.forwardSol β s t := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hsm : ∀ n, AEStronglyMeasurable (s n) S.μ := fun n =>
    ((hsad n).mono (S.𝓕.le n)).aestronglyMeasurable
  have he : Admissible S β u (fun n ω => y - s n ω) :=
    admissible_of_bdd hβ.le hβ1 huc (fun n => aestronglyMeasurable_const.sub (hsm n))
      (M := |y| + M) fun n => (hsM n).mono fun ω h => (abs_sub _ _).trans (add_le_add le_rfl h)
  have hQ0 : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ Q n ω := fun n => by
    have hnn : 0 ≤ᵐ[S.μ] fun ω => P n ω / P (n + 1) ω := by
      filter_upwards [hP n, hP (n + 1)] with ω h1 h2
      exact (div_pos h1 h2).le
    filter_upwards [hQ n, condExp_nonneg (m := S.𝓕 n) hnn] with ω h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hβ.le h2
  have hend := endDebt_ae hopt.1 hPad hP hQ hPP hx
  have hint : ∀ T, Integrable (fun ω => u' y * (Q T ω * b (T + 1) ω / P T ω)) S.μ := fun T =>
    (((S.integrable_E T _).smul β).congr (hend T).symm).const_mul (u' y)
  have htvcE := tvc_end_of_optimal hβ hu hu' hconc hmono hopt hPad hQad hsad hP hQ0 he hint
  have e : ∀ T, β ^ T * ∫ ω, u' y * (Q T ω * b (T + 1) ω / P T ω) ∂S.μ =
      u' y * (β ^ (T + 1) * ∫ ω, b (T + 1) ω / P (T + 1) ω ∂S.μ) := fun T => by
    rw [integral_const_mul, integral_congr_ae (hend T)]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, S.integral_E, pow_succ]
    ring
  have hunc : Tendsto (fun N => β ^ N * ∫ ω, b N ω / P N ω ∂S.μ) atTop (𝓝 0) := by
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    have := htvcE.const_mul (u' y)⁻¹
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    rw [e T, ← mul_assoc, inv_mul_cancel₀ huy.ne', one_mul]
  have hx0 : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ b n ω / P n ω := fun n => by
    filter_upwards [hopt.1.2.2.2.2 n, hP n] with ω h1 h2
    exact div_nonneg h1 h2.le
  obtain ⟨h26, h27⟩ := tvc_valuation_of_unconditional (x := fun n ω => b n ω / P n ω) hβ hβ1
    (flowX_of_feasible hopt.1 hPad hP hQ hPP hx) hsad hsM hx hx0 hunc t
  refine ⟨hunc, h26, h27, ?_⟩
  have hβa : |β| < 1 := by rwa [abs_of_pos hβ]
  filter_upwards [h27, S.forwardSol_hasSum hβa hsm hsM t] with ω h1 h2
  exact h1.unique h2

/-! ### The i.i.d. economy: a genuine infinite-state equilibrium -/

namespace IID

open ExpectationsMeasureIID

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), §2.7, p. 42 (surplus shocks), in the i.i.d. economy: surpluses
`s_t = s̄ + σ ε_t`. -/
def surplus (sbar σ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := sbar + σ * ω t

/-- Cochrane (2023), eq. (2.7), p. 22, in the i.i.d. economy: the price level
`P_t = B̄/(s̄/(1 − β) + σ ε_t)` that makes constant nominal debt `B̄` equal to the present value of
surpluses. -/
noncomputable def price (β sbar σ Bbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  Bbar / (sbar / (1 - β) + σ * ω t)

/-- Cochrane (2023), eq. (2.3), p. 22, in the i.i.d. economy: the bond price
`Q_t = β P_t s̄/((1 − β) B̄)`, which is `β E_t(P_t/P_{t+1})`. -/
noncomputable def bondPrice (β sbar σ Bbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  β * price β sbar σ Bbar t ω * (sbar / (1 - β) / Bbar)

/-- Cochrane (2023), Ch. 2, p. 29: in the i.i.d. economy, the forecast of an affine function of
the next shock is its mean, `E_t(p + q ε_{t+1}) = p` (mean-zero shocks). -/
theorem E_affine {B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t : ℕ) (p q : ℝ) :
    (iidSystem ν).E t (fun ω => p + q * ω (t + 1)) =ᵐ[(iidSystem ν).μ] fun _ => p := by
  have hxi : Integrable (fun x : ℝ => x) (ν : Measure ℝ) :=
    Integrable.of_bound aestronglyMeasurable_id B (hbdd.mono fun x h => by rwa [Real.norm_eq_abs])
  have h := E_shock_fun ν t (f := fun x => p + q * x) (by fun_prop)
  refine h.trans (Eventually.of_forall fun ω => ?_)
  simp only
  rw [integral_add (integrable_const p) (hxi.const_mul q), integral_const, integral_const_mul,
    hmean]
  simp

/-- Cochrane (2023), pp. 21–22 and §2.7, p. 42, **a genuine infinite-state equilibrium**: in the
i.i.d. economy (`ν` mean zero, variance `σ₂ > 0`, support in `[−B, B]`; every history has
probability zero and information grows forever) with `0 < β < 1`, surpluses
`s_t = s̄ + σ ε_t` (`σ ≠ 0`, `|σ| B < s̄/(1 − β)`), constant nominal debt `B̄ > 0`, the price level
`P_t = B̄/(s̄/(1 − β) + σ ε_t)` and the bond price `Q_t = β E_t(P_t/P_{t+1})`, and any concave,
increasing, differentiable utility with continuous `u'` and `u'(y) > 0`:
* the endowment plan `c = y` holding `B̄` is optimal (`optimal_of_euler_tvc`);
* hence (`valuation_of_optimal_eqm`) the valuation equation
  `B̄/P_t = ∑_j β^j E_t s_{t+j}` holds almost surely at every date;
* `Q_t > 0` and `i_t > −1` almost surely (`HouseholdMeasure.rate_gt_neg_one_of_formula`);
* real debt carries news: `B̄/P_{t+1}` is not almost surely equal to its date-`t` forecast;
* every single history has probability zero. -/
theorem iid_equilibrium {β y sbar σ Bbar B σ₂ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) (huy : 0 < u' y) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ₂) (hσ₂ : 0 < σ₂)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (hσ : σ ≠ 0) (hgap : |σ| * B < sbar / (1 - β))
    (hBbar : 0 < Bbar) :
    Optimal (iidSystem ν) β y u (price β sbar σ Bbar) (surplus sbar σ) (bondPrice β sbar σ Bbar)
        (fun _ => Bbar) (fun _ _ => y) (fun _ _ => Bbar) ∧
      (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, HasSum
        (fun j => β ^ j * (iidSystem ν).E t (surplus sbar σ (t + j)) ω)
        (Bbar / price β sbar σ Bbar t ω)) ∧
      (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, 0 < bondPrice β sbar σ Bbar t ω ∧
        -1 < Environment.rate (bondPrice β sbar σ Bbar) t ω) ∧
      (∀ t, ¬ (fun ω => Bbar / price β sbar σ Bbar (t + 1) ω) =ᵐ[(iidSystem ν).μ]
        (iidSystem ν).E t (fun ω => Bbar / price β sbar σ Bbar (t + 1) ω)) ∧
      ∀ ω, (iidSystem ν).μ {ω} = 0 := by
  set S := iidSystem ν with hS
  set a : ℝ := sbar / (1 - β) with ha
  have hB0 : 0 ≤ B := by
    obtain ⟨x, hx⟩ := hbdd.exists
    exact (abs_nonneg x).trans hx
  have ha0 : 0 < a := lt_of_le_of_lt (mul_nonneg (abs_nonneg σ) hB0) hgap
  have hsh : ∀ n, ∀ᵐ ω ∂S.μ, |ω n| ≤ B := fun n => shock_ae_bdd ν hbdd n
  -- the denominator is positive and bounded
  have hden : ∀ n, ∀ᵐ ω ∂S.μ, 0 < a + σ * ω n ∧ |a + σ * ω n| ≤ a + |σ| * B := fun n => by
    filter_upwards [hsh n] with ω h
    have h1 : |σ * ω n| ≤ |σ| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg σ)
    have h2 := abs_le.1 h1
    refine ⟨by linarith, ?_⟩
    rw [abs_le]
    constructor <;> linarith
  have hPpos : ∀ n, ∀ᵐ ω ∂S.μ, 0 < price β sbar σ Bbar n ω := fun n => by
    filter_upwards [hden n] with ω h
    exact div_pos hBbar h.1
  have hmeas : ∀ n, Measurable[S.𝓕 n] (fun ω : ℕ → ℝ => ω n) := fun n =>
    measurable_shock ν le_rfl
  have hPad : StronglyAdapted S.𝓕 (price β sbar σ Bbar) := fun n =>
    (measurable_const.div
      (measurable_const.add (measurable_const.mul (hmeas n)))).stronglyMeasurable
  have hQad : StronglyAdapted S.𝓕 (bondPrice β sbar σ Bbar) := fun n =>
    ((measurable_const.mul (hPad n).measurable).mul measurable_const).stronglyMeasurable
  have hsad : StronglyAdapted S.𝓕 (surplus sbar σ) := fun n =>
    (measurable_const.add (measurable_const.mul (hmeas n))).stronglyMeasurable
  have hm : ∀ n, AEStronglyMeasurable (fun ω : ℕ → ℝ => ω n) S.μ := fun n =>
    ((hmeas n).mono (S.𝓕.le n) le_rfl).aestronglyMeasurable
  -- real debt `B̄/P_n = a + σ ε_n`
  have hx : ∀ n ω, Bbar / price β sbar σ Bbar n ω = a + σ * ω n := fun n ω => by
    simp only [price, ← ha]
    rw [div_div_eq_mul_div]
    field_simp
  have hxi : ∀ n, Integrable (fun ω => Bbar / price β sbar σ Bbar n ω) S.μ := fun n => by
    simp_rw [hx n]
    exact (integrable_const a).add ((Integrable.of_bound (hm n) B ((hsh n).mono fun ω h => by
      rwa [Real.norm_eq_abs])).const_mul σ)
  have hint_x : ∀ n, ∫ ω, Bbar / price β sbar σ Bbar n ω ∂S.μ = a := fun n => by
    simp_rw [hx n]
    rw [integral_add (integrable_const a) ((Integrable.of_bound (hm n) B ((hsh n).mono
      fun ω h => by rwa [Real.norm_eq_abs])).const_mul σ), integral_const, integral_const_mul]
    have h : ∫ ω, ω n ∂S.μ = ∫ x, x ∂(ν : Measure ℝ) := integral_shock_fun ν n measurable_id
    rw [h, hmean]
    simp
  -- forecasts of real debt
  have hEx : ∀ n, S.E n (fun ω => Bbar / price β sbar σ Bbar (n + 1) ω) =ᵐ[S.μ] fun _ => a :=
    fun n => by
      have e : (fun ω => Bbar / price β sbar σ Bbar (n + 1) ω) = fun ω => a + σ * ω (n + 1) :=
        funext (hx (n + 1))
      rw [e]
      exact E_affine hmean hbdd n a σ
  -- the flow constraint
  have hflow : ∀ n, ∀ᵐ ω ∂S.μ, Bbar + price β sbar σ Bbar n ω * y =
      price β sbar σ Bbar n ω * y + price β sbar σ Bbar n ω * surplus sbar σ n ω +
        bondPrice β sbar σ Bbar n ω * Bbar := fun n => by
    filter_upwards [hPpos n] with ω hp
    have h1 : Bbar = price β sbar σ Bbar n ω * (a + σ * ω n) := by
      rw [← hx n ω]
      field_simp
    have h2 : sbar = a * (1 - β) := by
      rw [ha]
      field_simp [(show (1 - β) ≠ 0 by linarith)]
    simp only [bondPrice, surplus]
    rw [← ha]
    field_simp
    nlinarith [h1, h2]
  have hfeas : Feasible S y (price β sbar σ Bbar) (surplus sbar σ) (bondPrice β sbar σ Bbar)
      (fun _ => Bbar) (fun _ _ => y) (fun _ _ => Bbar) :=
    ⟨rfl, fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const, hflow,
      fun _ => Eventually.of_forall fun _ => hBbar.le⟩
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hadm : Admissible S β u (fun _ _ => y) :=
    admissible_of_bdd hβ.le hβ1 huc (fun _ => aestronglyMeasurable_const) (M := |y|)
      fun _ => Eventually.of_forall fun _ => le_rfl
  -- marginal utility per dollar: `u'(y)/P_n = (u'(y)/B̄)(B̄/P_n)`
  have hmu : ∀ n ω, u' y / price β sbar σ Bbar n ω =
      u' y / Bbar * (Bbar / price β sbar σ Bbar n ω) := fun n ω => by
    field_simp
  have hmI : ∀ n, Integrable (fun ω => u' y / price β sbar σ Bbar n ω) S.μ := fun n => by
    simp_rw [hmu n]
    exact (hxi n).const_mul _
  have hWI : ∀ n, Integrable (fun ω => u' y * Bbar / price β sbar σ Bbar n ω) S.μ := fun n => by
    have e : (fun ω => u' y * Bbar / price β sbar σ Bbar n ω) =
        fun ω => u' y * (Bbar / price β sbar σ Bbar n ω) := funext fun ω => by ring
    rw [e]
    exact (hxi n).const_mul _
  have heul : ∀ n, ∀ᵐ ω ∂S.μ, bondPrice β sbar σ Bbar n ω * (u' y / price β sbar σ Bbar n ω) =
      β * S.E n (fun ω => u' y / price β sbar σ Bbar (n + 1) ω) ω := fun n => by
    have e : (fun ω => u' y / price β sbar σ Bbar (n + 1) ω) =
        (u' y / Bbar) • fun ω => Bbar / price β sbar σ Bbar (n + 1) ω := funext fun ω => by
      rw [Pi.smul_apply, smul_eq_mul, hmu]
    filter_upwards [hPpos n, S.E_smul (u' y / Bbar)
      (fun ω => Bbar / price β sbar σ Bbar (n + 1) ω) n, hEx n] with ω hp h1 h2
    rw [e, h1, Pi.smul_apply, h2, smul_eq_mul]
    simp only [bondPrice, ← ha]
    have := hp.ne'
    field_simp
  have htvc : Tendsto (fun N => β ^ N * ∫ ω, u' y * Bbar / price β sbar σ Bbar N ω ∂S.μ)
      atTop (𝓝 0) := by
    have e : ∀ N, ∫ ω, u' y * Bbar / price β sbar σ Bbar N ω ∂S.μ = u' y * a := fun N => by
      rw [← hint_x N, ← integral_const_mul]
      congr 1
      funext ω
      ring
    simp_rw [e]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (u' y * a)
  have hopt : Optimal S β y u (price β sbar σ Bbar) (surplus sbar σ) (bondPrice β sbar σ Bbar)
      (fun _ => Bbar) (fun _ _ => y) (fun _ _ => Bbar) :=
    optimal_of_euler_tvc hβ hu hconc hmono hfeas hadm hPpos hmI hWI heul htvc
  -- the bond price formula (2.3)
  have hPPe : ∀ n ω, price β sbar σ Bbar n ω / price β sbar σ Bbar (n + 1) ω =
      price β sbar σ Bbar n ω * (Bbar / price β sbar σ Bbar (n + 1) ω / Bbar) := fun n ω => by
    field_simp
  have hPb : ∀ n, ∀ᵐ ω ∂S.μ, |price β sbar σ Bbar n ω| ≤ Bbar / (a - |σ| * B) := fun n => by
    filter_upwards [hsh n, hden n] with ω h1 h2
    simp only [price, ← ha]
    rw [abs_of_pos (div_pos hBbar h2.1)]
    have h3 : a - |σ| * B ≤ a + σ * ω n := by
      have := abs_le.1 (show |σ * ω n| ≤ |σ| * B by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg σ))
      linarith
    exact div_le_div_of_nonneg_left hBbar.le (by linarith) h3
  have hyI : ∀ n, Integrable (fun ω => Bbar / price β sbar σ Bbar (n + 1) ω / Bbar) S.μ :=
    fun n => (hxi (n + 1)).div_const _
  have hPP : ∀ n, Integrable (fun ω => price β sbar σ Bbar n ω /
      price β sbar σ Bbar (n + 1) ω) S.μ := fun n => by
    simp_rw [hPPe n]
    exact (hyI n).bdd_mul (hPad n |>.mono (S.𝓕.le n)).aestronglyMeasurable
      ((hPb n).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hQf : ∀ n, bondPrice β sbar σ Bbar n =ᵐ[S.μ]
      β • S.E n (fun ω => price β sbar σ Bbar n ω / price β sbar σ Bbar (n + 1) ω) := fun n => by
    have e : (fun ω => price β sbar σ Bbar n ω / price β sbar σ Bbar (n + 1) ω) =
        price β sbar σ Bbar n * fun ω => Bbar / price β sbar σ Bbar (n + 1) ω / Bbar :=
      funext fun ω => hPPe n ω
    have hEy : S.E n (fun ω => Bbar / price β sbar σ Bbar (n + 1) ω / Bbar) =ᵐ[S.μ]
        fun _ => a / Bbar := by
      have e2 : (fun ω => Bbar / price β sbar σ Bbar (n + 1) ω / Bbar) =
          Bbar⁻¹ • fun ω => Bbar / price β sbar σ Bbar (n + 1) ω := funext fun ω => by
        rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
      rw [e2]
      filter_upwards [S.E_smul Bbar⁻¹ (fun ω => Bbar / price β sbar σ Bbar (n + 1) ω) n,
        hEx n] with ω h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul, div_eq_inv_mul]
    rw [e]
    filter_upwards [S.E_pullOut (hPad n) (hPb n) (hyI n), hEy] with ω h1 h2
    rw [Pi.smul_apply, h1, Pi.mul_apply, h2, smul_eq_mul]
    simp only [bondPrice, ← ha]
    ring
  have hsM : ∀ n, ∀ᵐ ω ∂S.μ, |surplus sbar σ n ω| ≤ |sbar| + |σ| * B := fun n => by
    filter_upwards [hsh n] with ω h
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg σ)
  refine ⟨hopt, fun t => ?_, fun t => ?_, fun t => ?_, iid_singleton hmean hvar hσ₂⟩
  · exact (valuation_of_optimal_eqm hβ hβ1 hu hu' hconc hmono huy hopt hPad hQad hsad hPpos
      hsM hQf hPP hxi t).2.2.1
  · exact rate_gt_neg_one_of_formula hβ hPpos (hPP t) (hQf t)
  · intro hcon
    have h1 := hcon.trans (hEx t)
    have h2 : (fun ω : ℕ → ℝ => ω (t + 1)) =ᵐ[S.μ] fun _ => 0 := by
      filter_upwards [h1] with ω h
      rw [hx] at h
      have : σ * ω (t + 1) = 0 := by linarith
      simpa [hσ] using this
    refine shock_not_ae_E hmean hvar hσ₂ t ?_
    refine h2.trans ?_
    filter_upwards [E_shock_zero hmean t] with ω h
    rw [h]
    rfl

end IID

/-! ### Links to the finite-state statements of `Valuation` through the bridge -/

namespace Link

open ExpectationsFiniteTree TreeBridge

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), p. 21 (every state of a finite tree has positive probability): on the
tree's measure system an almost-sure statement holds in every state. -/
theorem forall_of_ae {p : Ω' → Prop} (h : ∀ᵐ ω ∂(treeSystem T).μ, p ω) : ∀ ω, p ω := by
  intro ω
  by_contra hω
  refine treeSystem_fullSupport T ω (measure_mono_null (fun ω' h' => ?_) (ae_iff.1 h))
  rw [Set.mem_singleton_iff.1 h']
  exact hω

/-- Cochrane (2023), p. 29: the tree's measure-theoretic `E_t` is its core `E_t`. -/
theorem treeE (t : ℕ) (x : Ω' → ℝ) :
    (treeSystem T).E t x = T.toExpectationSystem.E t x := by
  rw [treeSystem_E, FiniteTree.toExpectationSystem_E]

/-- Cochrane (2023), p. 21: on a finite tree, "known at `t`" in the measure sense
(`𝓕_t`-measurable) is "known at `t`" in the core sense (`E_t x = x`). -/
theorem sm_iff_known (t : ℕ) (x : Ω' → ℝ) :
    StronglyMeasurable[(treeSystem T).𝓕 t] x ↔ T.toExpectationSystem.E t x = x := by
  constructor
  · intro h
    rw [← treeE]
    exact (treeSystem T).E_of_stronglyMeasurable h Integrable.of_finite
  · intro h
    rw [← h, ← treeE]
    exact (treeSystem T).stronglyMeasurable_E t x

/-- Cochrane (2023), eq. (2.2), p. 21: on a finite tree the measure-theoretic feasibility of a
household plan is exactly the core one (`Valuation.SFeasible`). -/
theorem feasible_iff {y : ℝ} {P s Q c b : ℕ → Ω' → ℝ} {b₀ : Ω' → ℝ} :
    Valuation.SFeasible T.toExpectationSystem y P s Q b₀ c b ↔
      Feasible (treeSystem T) y P s Q b₀ c b := by
  constructor
  · rintro ⟨h0, hc, hb, hf, hn⟩
    exact ⟨h0, fun n => (sm_iff_known T n _).2 (hc n),
      fun n => (sm_iff_known T n _).2 (hb n), fun n => Eventually.of_forall (hf n),
      fun n => Eventually.of_forall (hn n)⟩
  · rintro ⟨h0, hc, hb, hf, hn⟩
    exact ⟨h0, fun n => (sm_iff_known T n _).1 (hc n), fun n => (sm_iff_known T n _).1 (hb n),
      fun n => forall_of_ae T (hf n), fun n => forall_of_ae T (hn n)⟩

/-- Cochrane (2023), p. 21: on a finite tree every variable is essentially bounded. -/
theorem bddAt_tree (f : Ω' → ℝ) : BddAt (treeSystem T) f :=
  ⟨∑ ω, |f ω|, Eventually.of_forall fun ω =>
    Finset.single_le_sum (f := fun ω => |f ω|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ω)⟩

/-- Cochrane (2023), p. 21: on a finite tree every plan satisfies `EulerRegular`. -/
theorem eulerRegular_tree (P Q c : ℕ → Ω' → ℝ) (t : ℕ) : EulerRegular (treeSystem T) P Q c t :=
  ⟨bddAt_tree T _, bddAt_tree T _, bddAt_tree T _, bddAt_tree T _, bddAt_tree T _⟩

/-- Cochrane (2023), p. 21: on a finite tree, integration commutes with a pointwise convergent
series. -/
theorem integral_tsum_tree {g : ℕ → Ω' → ℝ} (hs : ∀ ω, Summable fun n => g n ω) :
    ∫ ω, ∑' n, g n ω ∂(treeSystem T).μ = ∑' n, ∫ ω, g n ω ∂(treeSystem T).μ := by
  rw [integral_fintype Integrable.of_finite]
  simp_rw [integral_fintype Integrable.of_finite, smul_eq_mul, ← tsum_mul_left]
  exact (Summable.tsum_finsetSum fun ω _ => (hs ω).mul_left _).symm

omit [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω'] in
/-- Cochrane (2023), p. 21: on a finite tree, pathwise convergence of discounted utility gives
convergence of the core expected utility `∑_n β^n E_0 u(c_n)` in every state. -/
theorem core_summable {β : ℝ} {u : ℝ → ℝ} {c : ℕ → Ω' → ℝ}
    (hs : ∀ ω, Summable fun n => β ^ n * u (c n ω)) (ω : Ω') :
    Summable fun n => β ^ n * T.toExpectationSystem.E 0 (fun ω' => u (c n ω')) ω := by
  classical
  have e : ∀ n, β ^ n * T.toExpectationSystem.E 0 (fun ω' => u (c n ω')) ω =
      ∑ ω', β ^ n * u (c n ω') * T.toExpectationSystem.E 0 (Pi.single ω' 1) ω := fun n => by
    rw [Valuation.E_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω' _ => by ring
  simp_rw [e]
  exact summable_sum fun ω' _ => (hs ω').mul_right _

/-- Cochrane (2023), p. 21: on a finite tree, the expectation of the core expected utility
`∑_n β^n E_0 u(c_n)` is the measure-theoretic expected utility `E ∑_n β^n u(c_n)`. -/
theorem integral_core_expUtil {β : ℝ} {u : ℝ → ℝ} {c : ℕ → Ω' → ℝ}
    (hs : ∀ ω, Summable fun n => β ^ n * u (c n ω)) :
    ∫ ω, Valuation.expUtil T.toExpectationSystem β u c ω ∂(treeSystem T).μ =
      expUtil (treeSystem T) β u c := by
  unfold Valuation.expUtil expUtil
  rw [integral_tsum_tree T (core_summable T hs), integral_tsum_tree T hs]
  refine tsum_congr fun n => ?_
  rw [integral_const_mul, integral_const_mul, ← treeE, (treeSystem T).integral_E]

/-- Cochrane (2023), p. 21: on a finite tree, **the core optimality notion implies the
measure-theoretic one**: a core-optimal plan (`Valuation.SOptimal`, utility compared state by
state at date 0) whose discounted utility converges absolutely along every path is `Optimal` for
the tree's measure system. -/
theorem optimal_of_core {β y : ℝ} (hβ : 0 < β) {u : ℝ → ℝ} (huc : Continuous u)
    {P s Q c b : ℕ → Ω' → ℝ} {b₀ : Ω' → ℝ}
    (hopt : Valuation.SOptimal T.toExpectationSystem β y u P s Q b₀ c b)
    (hcabs : ∀ ω, Summable fun n => β ^ n * |u (c n ω)|) :
    Optimal (treeSystem T) β y u P s Q b₀ c b := by
  obtain ⟨hf, -, hbest⟩ := hopt
  have habs : ∀ {c' : ℕ → Ω' → ℝ}, (∀ ω, Summable fun n => β ^ n * |u (c' n ω)|) →
      ∀ ω, Summable fun n => β ^ n * u (c' n ω) := fun h ω =>
    Summable.of_norm_bounded (h ω) fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.le]
  refine ⟨(feasible_iff T).1 hf, ⟨fun n => (huc.measurable.comp
    (Measurable.of_discrete)).aestronglyMeasurable, Eventually.of_forall hcabs,
    Integrable.of_finite⟩, fun c' b' hf' hadm' => ?_⟩
  have hc'abs : ∀ ω, Summable fun n => β ^ n * |u (c' n ω)| := forall_of_ae T hadm'.2.1
  have h := hbest c' b' ((feasible_iff T).2 hf') (core_summable T (habs hc'abs))
  rw [← integral_core_expUtil T (habs hc'abs), ← integral_core_expUtil T (habs hcabs)]
  exact integral_mono Integrable.of_finite Integrable.of_finite h

/-- Cochrane (2023), p. 21, the Euler equation, **link to `Valuation.euler_of_optimal_stoch`**:
on a finite event tree, for a core-optimal plan with pathwise absolutely convergent utility,
differentiable `u` with continuous `u'`, positive adapted prices and a bond price known at `t`,
the measure-theoretic results (`euler_kkt`, `euler_interior`) give, in every state and for the
core `E_t`, the Euler inequality `β E_t[u'(c_{t+1})/P_{t+1}] ≤ Q_t u'(c_t)/P_t` and the Euler
equation wherever `B_t > 0` (the core theorem assumes `B_t > 0` in every state). -/
theorem link_euler {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {P s Q c b : ℕ → Ω' → ℝ} {b₀ : Ω' → ℝ}
    (hopt : Valuation.SOptimal T.toExpectationSystem β y u P s Q b₀ c b)
    (hcabs : ∀ ω, Summable fun n => β ^ n * |u (c n ω)|) (hP : ∀ n ω, 0 < P n ω)
    (hPad : T.toExpectationSystem.Adapted P) {t : ℕ}
    (hQt : T.toExpectationSystem.E t (Q t) = Q t) :
    (∀ ω, β * T.toExpectationSystem.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) ω ≤
      Q t ω * (u' (c t ω) / P t ω)) ∧
    ∀ ω, 0 < b (t + 1) ω → Q t ω * (u' (c t ω) / P t ω) =
      β * T.toExpectationSystem.E t (fun ω => u' (c (t + 1) ω) / P (t + 1) ω) ω := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hopt' := optimal_of_core T hβ huc hopt hcabs
  have hPad' : StronglyAdapted (treeSystem T).𝓕 P := fun n => (sm_iff_known T n _).2 (hPad n)
  have hP' : ∀ n, ∀ᵐ ω ∂(treeSystem T).μ, 0 < P n ω := fun n => Eventually.of_forall (hP n)
  have hQt' := (sm_iff_known T t _).2 hQt
  have h1 := forall_of_ae T (euler_kkt hβ hu hu' hopt' hPad' hP' hQt' (eulerRegular_tree T P Q c t))
  have h2 := forall_of_ae T
    (euler_interior hβ hu hu' hopt' hPad' hP' hQt' (eulerRegular_tree T P Q c t))
  rw [treeE] at h1 h2
  exact ⟨h1, h2⟩

/-- Cochrane (2023), eqs. (2.6)–(2.7), p. 22, **link to `Valuation.tvc_of_optimal_stoch` and
`Valuation.valuation_of_optimal_stoch`**: on a finite event tree, a core-optimal endowment plan
(`c = y`) gives the core transversality condition `Valuation.TVC` and the core valuation
equation `x_t = Valuation.pv` in every state, by way of the measure-theoretic theorem
`valuation_of_optimal_eqm` — with no `Valuation.InfoStable` hypothesis (here `u` is concave and
increasing with continuous `u'`, `u'(y) > 0`, `0 < β < 1`, surpluses uniformly bounded). -/
theorem link_tvc_valuation {β y : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) (huy : 0 < u' y) {P s Q b : ℕ → Ω' → ℝ} {b₀ : Ω' → ℝ}
    (hopt : Valuation.SOptimal T.toExpectationSystem β y u P s Q b₀ (fun _ _ => y) b)
    (hP : ∀ n ω, 0 < P n ω) (hPad : T.toExpectationSystem.Adapted P)
    (hQad : T.toExpectationSystem.Adapted Q) (hsad : T.toExpectationSystem.Adapted s)
    {M : ℝ} (hsM : ∀ n ω, |s n ω| ≤ M)
    (hQ : ∀ n, Q n = β • T.toExpectationSystem.E n (fun ω => P n ω / P (n + 1) ω)) (t : ℕ) :
    Valuation.TVC T.toExpectationSystem β (fun n ω => b n ω / P n ω) t ∧
      (fun ω => b t ω / P t ω) = Valuation.pv T.toExpectationSystem β s t := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hcabs : ∀ ω, Summable fun n => β ^ n * |u ((fun _ _ => y : ℕ → Ω' → ℝ) n ω)| :=
    fun ω => (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  have hopt' := optimal_of_core T hβ huc hopt hcabs
  have hQ' : ∀ n, Q n =ᵐ[(treeSystem T).μ]
      β • (treeSystem T).E n (fun ω => P n ω / P (n + 1) ω) := fun n => by
    rw [treeE, ← hQ n]
  obtain ⟨-, h26, h27, -⟩ := valuation_of_optimal_eqm hβ hβ1 hu hu' hconc hmono huy hopt'
    (fun n => (sm_iff_known T n _).2 (hPad n)) (fun n => (sm_iff_known T n _).2 (hQad n))
    (fun n => (sm_iff_known T n _).2 (hsad n)) (fun n => Eventually.of_forall (hP n))
    (fun n => Eventually.of_forall (hsM n)) hQ' (fun _ => Integrable.of_finite)
    (fun _ => Integrable.of_finite) t
  have h26' := forall_of_ae T h26
  have h27' := forall_of_ae T h27
  simp_rw [treeE] at h26' h27'
  refine ⟨fun ω => h26' ω, ?_⟩
  funext ω
  rw [Valuation.pv_apply]
  exact (h27' ω).tsum_eq.symm

end Link

end Cochrane.IntertemporalModel.HouseholdMeasureTVC
