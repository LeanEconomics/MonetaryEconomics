/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.DebtLimitStochastic
import FiscalConstraints.LognormalGrowthMeasure
import Mathlib.Probability.Independence.ZeroOne

/-!
# Debt limits with genuine i.i.d. surplus processes

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, pp. 196–197.

The surplus ratios are the coordinates `σ_t(ω) = ω_t` of the i.i.d. product space
`(ℕ → ℝ, ν^ℕ)` of `ExpectationsMeasureIID` (law `ν` at every date), with the natural filtration.
The debt ratio `x_{t+1} = γ x_t − σ_t` (`DebtLimitStochastic.debtPath`) is then an adapted
process on a genuine infinite-horizon probability space.

## Main results

* `debtPath_adapted`: the debt ratio `x_{t+1}` is known at `t`.
* `iid_frequently_exceeds`, `iid_not_sustainable` (**Theorem S on the i.i.d. process**, second
  Borel–Cantelli lemma): for any law `ν` bounded above with `ν(−∞, −c] > 0`.
* `iid_unbounded_core`: the core `DebtLimitStochastic.iid_unbounded` applied to the process.
* `coin_debt_dichotomy` (the bounded-support correction on a genuine process): with fair `±1`
  coin surpluses, debt a.s. never exceeds `max x₀ (1/(1 − γ))`, yet a.s. exceeds every
  `M < 1/(1 − γ)` infinitely often.
* `gaussian_not_ae_bounded_above`, `gaussian_iid_unbounded_vacuous` (**correction**): a
  non-degenerate Gaussian surplus is not a.s. bounded above, so the hypotheses of
  `DebtLimitStochastic.gaussian_iid_unbounded` can never hold; that theorem is vacuous.
* `iid_unbounded_of_integrable` (the corrected theorem, **no upper bound needed**): for i.i.d.
  integrable surpluses with deficits of every size, the debt ratio is a.s. unbounded above. The
  proof uses Markov's inequality, independence of `σ_{t+1}` from `𝓕_t`, and Kolmogorov's 0-1 law.
* `gaussian_process_unbounded`, `gaussian_process_not_sustainable`: **i.i.d. Gaussian surpluses
  as a process** make the debt ratio a.s. unbounded above, so no debt limit is sustainable.
* `managed_adapted`, `managedPath_le_process`: the managed surplus is an adapted process that
  keeps debt below the limit.
-/

namespace Cochrane.FiscalConstraints.DebtLimitStochasticMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic LognormalGrowthMeasure
open AggregateUncertaintyMeasure (integrable_coord_fun measurable_coord_future)

/-! ### General facts about the debt recursion -/

/-- Cochrane (2023), (6.4) p. 196: the debt ratio `x_t` is measurable for any σ-algebra for which
the surpluses `σ_0, …, σ_{t−1}` are measurable. -/
theorem measurable_debtPath {Ω : Type*} {m : MeasurableSpace Ω} (γ x₀ : ℝ) {σ : ℕ → Ω → ℝ} :
    ∀ t, (∀ s < t, Measurable[m] (σ s)) → Measurable[m] (debtPath γ x₀ σ t) := by
  intro t
  induction t with
  | zero => intro _; exact measurable_const
  | succ t ih =>
    intro h
    have h1 := ih fun s hs => h s (Nat.lt_succ_of_lt hs)
    have h2 := h t (Nat.lt_succ_self t)
    have hf : debtPath γ x₀ σ (t + 1) = fun ω => γ * debtPath γ x₀ σ t ω - σ t ω := by
      funext ω; exact debtPath_succ γ x₀ σ t ω
    rw [hf]
    exact (h1.const_mul γ).sub h2

/-- Cochrane (2023), (6.4) p. 196: restarting the recursion at date `N`,
`x_{N+k} = γ^k x_N + y_k` where `y` solves the same recursion from `y_0 = 0` driven by
`σ_N, σ_{N+1}, …`. -/
theorem debtPath_shift {Ω : Type*} (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    ∀ k, debtPath γ x₀ σ (N + k) ω =
      γ ^ k * debtPath γ x₀ σ N ω + debtPath γ 0 (fun s => σ (N + s)) k ω := by
  intro k
  induction k with
  | zero => change _ = _ * _ + 0; simp
  | succ k ih =>
    rw [← add_assoc, debtPath_succ, debtPath_succ, ih, pow_succ]
    ring

/-- Cochrane (2023), p. 197: a frequently-true property is shift invariant. -/
theorem frequently_shift_iff {p : ℕ → Prop} (N : ℕ) :
    (∃ᶠ t in atTop, p t) ↔ ∃ᶠ k in atTop, p (N + k) := by
  rw [frequently_atTop, frequently_atTop]
  constructor
  · intro h a
    obtain ⟨t, ht, hp⟩ := h (N + a)
    exact ⟨t - N, by omega, by rwa [show N + (t - N) = t by omega]⟩
  · intro h a
    obtain ⟨k, hk, hp⟩ := h a
    exact ⟨N + k, by omega, hp⟩

/-- Cochrane (2023), p. 197: "`z_t` gets within `1/(m+1)` of `a` from above infinitely often,
for every `m`" is unchanged by a perturbation that vanishes at infinity. -/
theorem frequently_near_of_tendsto {z z' : ℕ → ℝ} (hzz : Tendsto (fun t => z t - z' t) atTop (𝓝 0))
    {a : ℝ} (h : ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < z t) (m : ℕ) :
    ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < z' t := by
  have hpos : (0 : ℝ) < 1 / (2 * (m : ℝ) + 2) := by positivity
  have hev : ∀ᶠ t in atTop, |z t - z' t| < 1 / (2 * (m : ℝ) + 2) := by
    refine (hzz.eventually (Metric.ball_mem_nhds 0 hpos)).mono fun t ht => ?_
    rw [Real.dist_0_eq_abs] at ht
    exact ht
  have hf := h (2 * m + 1)
  refine (hf.and_eventually hev).mono fun t ht => ?_
  obtain ⟨h1, h2⟩ := ht
  rw [abs_lt] at h2
  have e1 : (1 : ℝ) / ((((2 * m + 1 : ℕ)) : ℝ) + 1) = 1 / (2 * (m : ℝ) + 2) := by
    push_cast; ring_nf
  rw [e1] at h1
  have e2 : 1 / (2 * (m : ℝ) + 2) + 1 / (2 * (m : ℝ) + 2) = 1 / ((m : ℝ) + 1) := by
    field_simp; ring
  linarith

/-- Cochrane (2023), p. 197: the event "frequently near or above `a`" for a sequence of
`m'`-measurable variables is `m'`-measurable. -/
theorem measurableSet_frequently_near {Ω : Type*} {m' : MeasurableSpace Ω} {y : ℕ → Ω → ℝ}
    (hy : ∀ k, Measurable[m'] (y k)) (a : ℝ) :
    MeasurableSet[m'] {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
  have h : {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} =
      ⋂ m : ℕ, ⋂ n : ℕ, ⋃ k : ℕ, ⋃ (_ : n ≤ k), {ω | a - 1 / ((m : ℝ) + 1) < y k ω} := by
    ext ω
    simp [frequently_atTop]
  rw [h]
  exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => MeasurableSet.iUnion
    fun k => MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const (hy k)

/-! ### The i.i.d. surplus process -/

variable {ν : ProbabilityMeasure ℝ}

variable (ν) in
/-- Cochrane (2023), (6.4) p. 196: on the i.i.d. process the debt ratio `x_{t+1}` is known at
date `t` (it depends on `σ_0, …, σ_t`), so `x` is adapted and predetermined. -/
theorem debtPath_adapted (γ x₀ : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (debtPath γ x₀ shock (t + 1)) :=
  measurable_debtPath γ x₀ (t + 1) fun _ hs => measurable_shock ν (by omega)

/-- Cochrane (2023), p. 197: the coordinate surpluses are independent under `ν^ℕ`. -/
theorem iIndepFun_shock : iIndepFun shock (iidSystem ν).μ :=
  iIndepFun_infinitePi (P := fun _ => (ν : Measure ℝ)) (X := fun _ => id)
    (fun _ => measurable_id)

/-- Cochrane (2023), p. 197: each surplus has law `ν`: `P(σ_t ∈ A) = ν(A)`. -/
theorem measure_shock_preimage (t : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    (iidSystem ν).μ (shock t ⁻¹' A) = (ν : Measure ℝ) A :=
  (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) t).measure_preimage
    hA.nullMeasurableSet

/-- **Theorem S on the i.i.d. process**, Cochrane (2023), §6.4.1, p. 197: if the surplus law
`ν` is a.s. bounded above by `K` and puts positive probability on deficits of size at least
`c`, then for `0 ≤ γ < 1` and every `M < c/(1 − γ)`, from every initial debt ratio, almost surely
the debt ratio exceeds `M` infinitely often. -/
theorem iid_frequently_exceeds {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) (hK : ∀ᵐ x ∂(ν : Measure ℝ), x ≤ K)
    (hp : (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  let _ : MeasureSpace (ℕ → ℝ) := @MeasureSpace.mk (ℕ → ℝ) MeasurableSpace.pi (iidSystem ν).μ
  exact frequently_exceeds hγ0 hγ1 hM (fun t => measurable_pi_apply t) iIndepFun_shock
    (fun t => (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) t
      ).quasiMeasurePreserving.ae hK) hp
    (fun t => (measure_shock_preimage t measurableSet_Iic).ge)

/-- Cochrane (2023), p. 197 ("no value of debt is sustainable"), on the i.i.d. process: under the
hypotheses of `iid_frequently_exceeds`, the event that debt stays at or below `M` forever has
probability zero. -/
theorem iid_not_sustainable {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) (hK : ∀ᵐ x ∂(ν : Measure ℝ), x ≤ K)
    (hp : (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) :
    (iidSystem ν).μ {ω | ∀ t, debtPath γ x₀ shock t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [iid_frequently_exceeds hγ0 hγ1 hM hK hp] with ω hω hall
  obtain ⟨t, ht⟩ := hω.exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197 (correction, **on a genuine process**): with i.i.d. fair `±1` coin
surpluses and `0 ≤ γ < 1`, almost surely the debt ratio never exceeds `max x₀ (1/(1 − γ))` (so
bounded support does not make debt exceed every bound), yet almost surely it exceeds every
`M < 1/(1 − γ)` infinitely often (Theorem S). -/
theorem coin_debt_dichotomy {γ x₀ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∀ᵐ ω ∂(iidSystem coin).μ, ∀ t, debtPath γ x₀ shock t ω ≤ max x₀ (1 / (1 - γ))) ∧
      ∀ M < 1 / (1 - γ), ∀ᵐ ω ∂(iidSystem coin).μ,
        ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  constructor
  · filter_upwards [ae_all_iff.2 (shock_ae_bdd coin coin_bdd)] with ω hω t
    exact debtPath_le_of_bounded_deficits hγ0 hγ1 (fun s => (abs_le.1 (hω s)).1) t
  · intro M hM
    have hK : ∀ᵐ x ∂(coin : Measure ℝ), x ≤ 1 :=
      coin_bdd.mono fun x h => (abs_le.1 h).2
    have hp : (coin : Measure ℝ) (Set.Iic (-1)) ≠ 0 := by
      change coinMeasure (Set.Iic (-1)) ≠ 0
      simp only [coinMeasure, Measure.smul_apply, Measure.add_apply,
        Measure.dirac_apply' _ measurableSet_Iic, Set.indicator, Set.mem_Iic, smul_eq_mul]
      norm_num
    exact iid_frequently_exceeds hγ0 hγ1 hM hK hp

/-- Cochrane (2023), p. 197 (**link**: the core `DebtLimitStochastic.iid_unbounded` on the
genuine process): if the surplus law `ν` is a.s. bounded above and puts positive mass on deficits
of every size, the core theorem applies to the coordinate surpluses of `ν^ℕ` and the debt ratio
is a.s. unbounded above. -/
theorem iid_unbounded_core {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hK : ∀ᵐ x ∂(ν : Measure ℝ), x ≤ K) (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  let _ : MeasureSpace (ℕ → ℝ) := @MeasureSpace.mk (ℕ → ℝ) MeasurableSpace.pi (iidSystem ν).μ
  have hmap : ∀ t, Measure.map (shock t) (iidSystem ν).μ = (ν : Measure ℝ) := fun t =>
    Measure.infinitePi_map_eval _ t
  refine DebtLimitStochastic.iid_unbounded hγ0 hγ1 (fun t => measurable_pi_apply t)
    iIndepFun_shock (fun t => ⟨(measurable_pi_apply t).aemeasurable,
      (measurable_pi_apply 0).aemeasurable, (hmap t).trans (hmap 0).symm⟩)
    (fun t => (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) t
      ).quasiMeasurePreserving.ae hK) fun c => ?_
  exact (measure_shock_preimage 0 measurableSet_Iic).trans_ne (hdef c)

/-! ### Gaussian surpluses: the correction -/

/-- Cochrane (2023), p. 197 (**correction**): a non-degenerate Gaussian surplus is not almost
surely bounded above: `P(σ > K) > 0` for every `K`. -/
theorem gaussian_not_ae_bounded_above {Ω : Type*} [MeasureSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    (hlaw : Measure.map X volume = gaussianReal m v) (K : ℝ) :
    ¬ ∀ᵐ ω, X ω ≤ K := by
  intro h
  have h0 : volume (X ⁻¹' Set.Ioi K) = 0 := by
    rw [ae_iff] at h
    have hs : {ω | ¬ X ω ≤ K} = X ⁻¹' Set.Ioi K := by ext ω; simp
    rwa [hs] at h
  rw [← Measure.map_apply hX measurableSet_Ioi, hlaw] at h0
  have h2 := gaussianReal_absolutelyContinuous' m hv h0
  rw [Real.volume_Ioi] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197 (**correction**: `DebtLimitStochastic.gaussian_iid_unbounded` is
vacuous): if `σ_0` is non-degenerate Gaussian, the hypothesis "`σ_t ≤ K` a.s. at every date" of
that theorem is false for every `K`. -/
theorem gaussian_iid_unbounded_vacuous {Ω : Type*} [MeasureSpace Ω] {σ : ℕ → Ω → ℝ}
    (hσ : Measurable (σ 0)) {m : ℝ} {v : NNReal} (hv : v ≠ 0)
    (hlaw : Measure.map (σ 0) volume = gaussianReal m v) (K : ℝ) :
    ¬ ∀ t, ∀ᵐ ω, σ t ω ≤ K :=
  fun h => gaussian_not_ae_bounded_above hσ hv hlaw K (h 0)

/-! ### The corrected theorem: i.i.d. surpluses unbounded below, no upper bound -/

/-- Cochrane (2023), p. 197: with integrable i.i.d. surpluses (`E|σ| = m₁`), every debt ratio
is integrable with `E|x_t| ≤ |x₀| + m₁/(1 − γ)`. -/
theorem integral_abs_debtPath_le (hint : Integrable id (ν : Measure ℝ)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (x₀ : ℝ) :
    ∀ t, Integrable (debtPath γ x₀ shock t) (iidSystem ν).μ ∧
      ∫ ω, |debtPath γ x₀ shock t ω| ∂(iidSystem ν).μ ≤
        |x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) := by
  have h1 : 0 < 1 - γ := by linarith
  have hm0 : 0 ≤ ∫ x, |x| ∂(ν : Measure ℝ) := integral_nonneg fun x => abs_nonneg x
  have hsh : ∀ s, Integrable (shock s) (iidSystem ν).μ := fun s =>
    integrable_coord_fun (f := id) hint s
  have hsa : ∀ s, ∫ ω, |shock s ω| ∂(iidSystem ν).μ = ∫ x, |x| ∂(ν : Measure ℝ) := fun s =>
    integral_shock_fun ν s (f := fun x => |x|) continuous_abs.measurable
  intro t
  induction t with
  | zero =>
    refine ⟨integrable_const x₀, ?_⟩
    change ∫ _, |x₀| ∂(iidSystem ν).μ ≤ _
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : 0 ≤ (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) := div_nonneg hm0 h1.le
    linarith
  | succ t ih =>
    have hf : debtPath γ x₀ shock (t + 1) = fun ω => γ * debtPath γ x₀ shock t ω - shock t ω := by
      funext ω; exact debtPath_succ γ x₀ shock t ω
    have hI : Integrable (debtPath γ x₀ shock (t + 1)) (iidSystem ν).μ := by
      rw [hf]; exact (ih.1.const_mul γ).sub (hsh t)
    refine ⟨hI, ?_⟩
    have hle : ∫ ω, |debtPath γ x₀ shock (t + 1) ω| ∂(iidSystem ν).μ ≤
        ∫ ω, (γ * |debtPath γ x₀ shock t ω| + |shock t ω|) ∂(iidSystem ν).μ := by
      refine integral_mono hI.abs ((ih.1.abs.const_mul γ).add (hsh t).abs) fun ω => ?_
      rw [hf]
      calc |γ * debtPath γ x₀ shock t ω - shock t ω|
          ≤ |γ * debtPath γ x₀ shock t ω| + |shock t ω| := abs_sub _ _
        _ = γ * |debtPath γ x₀ shock t ω| + |shock t ω| := by
          rw [abs_mul, abs_of_nonneg hγ0]
    rw [integral_add (ih.1.abs.const_mul γ) (hsh t).abs, integral_const_mul, hsa] at hle
    have key : γ * (|x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ)) + ∫ x, |x| ∂(ν : Measure ℝ)
        ≤ |x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) := by
      have e : (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) * (1 - γ) = ∫ x, |x| ∂(ν : Measure ℝ) :=
        div_mul_cancel₀ _ h1.ne'
      nlinarith [abs_nonneg x₀]
    nlinarith [mul_le_mul_of_nonneg_left ih.2 hγ0]

/-- Cochrane (2023), p. 197: with integrable i.i.d. surpluses and deficits of every size, the
probability that the debt ratio exceeds `M` at date `t + 2` is bounded below uniformly in `t`:
`P(x_{t+2} > M) ≥ ν(−∞, −L] / 2` for `L = M + γ D + 1`, `D = 2 C + 1`,
`C = |x₀| + E|σ|/(1 − γ)` (Markov's inequality and independence of `σ_{t+1}` from `𝓕_t`). -/
theorem prob_exceeds_ge (hint : Integrable id (ν : Measure ℝ)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (x₀ M : ℝ) (t : ℕ) :
    (ν : Measure ℝ) (Set.Iic (-(M + γ * (2 * (|x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ)) + 1)
        + 1))) * ENNReal.ofReal (1 / 2) ≤
      (iidSystem ν).μ {ω | M < debtPath γ x₀ shock (t + 2) ω} := by
  set C := |x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ) with hC
  set D := 2 * C + 1 with hD
  set L := M + γ * D + 1 with hL
  have h1 : 0 < 1 - γ := by linarith
  have hC0 : 0 ≤ C := add_nonneg (abs_nonneg _)
    (div_nonneg (integral_nonneg fun x => abs_nonneg x) h1.le)
  have hD0 : 0 < D := by linarith
  obtain ⟨hI, hbound⟩ := integral_abs_debtPath_le hint hγ0 hγ1 x₀ (t + 1)
  set A := {ω : ℕ → ℝ | -D < debtPath γ x₀ shock (t + 1) ω} with hA
  set B := {ω : ℕ → ℝ | ω (t + 1) ≤ -L} with hB
  have hAm : MeasurableSet[(iidSystem ν).𝓕 t] A :=
    measurableSet_lt measurable_const (debtPath_adapted ν γ x₀ t)
  have hBm : MeasurableSet[futureSigma t] B :=
    measurableSet_le (measurable_coord_future (by omega)) measurable_const
  have hind := (Indep_iff _ _ _).1 (indep_future ν t) B A hBm hAm
  have hsub : B ∩ A ⊆ {ω | M < debtPath γ x₀ shock (t + 2) ω} := by
    rintro ω ⟨hb, ha⟩
    simp only [Set.mem_ofPred_eq, hB, hA] at hb ha ⊢
    rw [show t + 2 = (t + 1) + 1 by rfl, debtPath_succ]
    change M < γ * debtPath γ x₀ shock (t + 1) ω - ω (t + 1)
    nlinarith [mul_le_mul_of_nonneg_left ha.le hγ0]
  have hBval : (iidSystem ν).μ B = (ν : Measure ℝ) (Set.Iic (-L)) :=
    measure_shock_preimage (t + 1) measurableSet_Iic
  have hAval : ENNReal.ofReal (1 / 2) ≤ (iidSystem ν).μ A := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := (iidSystem ν).μ)
      (Eventually.of_forall fun ω => abs_nonneg (debtPath γ x₀ shock (t + 1) ω)) hI.abs D
    have hreal : (iidSystem ν).μ.real {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|} ≤ 1 / 2 := by
      have : D * (iidSystem ν).μ.real {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|} ≤ C :=
        hmk.trans hbound
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hpr := measureReal_nonneg (μ := (iidSystem ν).μ)
        (s := {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|})
      nlinarith
    have hcompl : Aᶜ ⊆ {ω | D ≤ |debtPath γ x₀ shock (t + 1) ω|} := by
      intro ω hω
      simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
      rw [le_abs]; right; linarith
    have hAc : (iidSystem ν).μ.real Aᶜ ≤ 1 / 2 := (measureReal_mono hcompl).trans hreal
    have hAm' : MeasurableSet A := (iidSystem ν).𝓕.le t _ hAm
    rw [measureReal_compl hAm', probReal_univ] at hAc
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc (ν : Measure ℝ) (Set.Iic (-L)) * ENNReal.ofReal (1 / 2)
      ≤ (iidSystem ν).μ B * (iidSystem ν).μ A := by rw [hBval]; gcongr
    _ = (iidSystem ν).μ (B ∩ A) := hind.symm
    _ ≤ _ := measure_mono hsub

/-- Cochrane (2023), p. 197: if the events `A_{t+2}` all have probability at least `q`, then
"`A_t` infinitely often" has probability at least `q` (continuity from above). -/
theorem le_measure_frequently {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : ℕ → Set Ω} (hA : ∀ t, MeasurableSet (A t)) {q : ENNReal}
    (hq : ∀ t, q ≤ μ (A (t + 2))) : q ≤ μ {ω | ∃ᶠ t in atTop, ω ∈ A t} := by
  set B : ℕ → Set Ω := fun N => ⋃ t, ⋃ (_ : N ≤ t), A t with hBdef
  have hset : {ω | ∃ᶠ t in atTop, ω ∈ A t} = ⋂ N, B N := by
    ext ω
    simp [hBdef, frequently_atTop]
  have hanti : Antitone B := fun N N' h ω hω => by
    simp only [hBdef, Set.mem_iUnion] at hω ⊢
    obtain ⟨t, ht, h'⟩ := hω
    exact ⟨t, h.trans ht, h'⟩
  have hBm : ∀ N, NullMeasurableSet (B N) μ := fun N =>
    (MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ => hA t).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hBm hanti ⟨0, measure_ne_top μ _⟩
  rw [hset]
  refine ge_of_tendsto' hlim fun N => ?_
  calc q ≤ μ (A (N + 2)) := hq N
    _ ≤ μ (B N) := measure_mono (Set.subset_biUnion_of_mem (u := A) (by omega : N ≤ N + 2))

/-- **The debt ratio is a.s. unbounded above for i.i.d. surpluses that are integrable and
unbounded below** — no upper bound on surpluses is needed (Cochrane (2023), p. 197: "an AR(1)
ranges over the entire real line", corrected discrete i.i.d. version). For `0 ≤ γ < 1` and every
initial debt `x₀`, almost surely `x_t` exceeds every level infinitely often. Proof: the events
"`x_t` comes within `1/(m+1)` of `M` infinitely often" are tail events (`debtPath_shift`), have
probability at least `ν(−∞, −L]/2 > 0` (`prob_exceeds_ge`), hence probability one by
Kolmogorov's 0-1 law. -/
theorem iid_unbounded_of_integrable (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  set E : ℝ → Set (ℕ → ℝ) := fun a =>
    {ω | ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < debtPath γ x₀ shock t ω} with hE
  have hmeas : ∀ t, Measurable (debtPath γ x₀ shock t) := fun t =>
    measurable_debtPath γ x₀ t fun s _ => measurable_pi_apply s
  -- the events are tail events
  have htail : ∀ a, MeasurableSet[limsup coordSigma atTop] (E a) := by
    intro a
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    set y : ℕ → (ℕ → ℝ) → ℝ := fun k => debtPath γ 0 (fun s => shock (N + s)) k with hy
    have hym : ∀ k, Measurable[⨆ i ≥ N, coordSigma i] (y k) := fun k =>
      measurable_debtPath γ 0 k fun s _ => Measurable.of_comap_le
        (le_iSup₂ (f := fun i (_ : i ≥ N) => coordSigma i) (N + s) (by omega))
    have heq : E a = {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq]
      have hshift : ∀ m : ℕ, (∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < debtPath γ x₀ shock t ω) ↔
          ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < debtPath γ x₀ shock (N + k) ω :=
        fun m => frequently_shift_iff N
      simp only [hshift]
      have hdiff : Tendsto (fun k => debtPath γ x₀ shock (N + k) ω - y k ω) atTop (𝓝 0) := by
        have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const
          (debtPath γ x₀ shock N ω)
        rw [zero_mul] at h
        refine h.congr fun k => ?_
        rw [debtPath_shift]
        simp only [hy]
        ring
      have hdiff' : Tendsto (fun k => y k ω - debtPath γ x₀ shock (N + k) ω) atTop (𝓝 0) := by
        have := hdiff.neg
        rw [neg_zero] at this
        refine this.congr fun k => ?_
        ring
      exact ⟨fun h m => frequently_near_of_tendsto hdiff h m,
        fun h m => frequently_near_of_tendsto hdiff' h m⟩
    rw [heq]
    exact measurableSet_frequently_near hym a
  -- each event has positive probability
  have hpos : ∀ a, (iidSystem ν).μ (E a) ≠ 0 := by
    intro a
    set c := a + γ * (2 * (|x₀| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - γ)) + 1) + 1
    have hq := fun t => prob_exceeds_ge hint hγ0 hγ1 x₀ a t
    have hfreq := le_measure_frequently (μ := (iidSystem ν).μ)
      (A := fun t => {ω | a < debtPath γ x₀ shock t ω})
      (fun t => measurableSet_lt measurable_const (hmeas t)) hq
    have hsub : {ω | ∃ᶠ t in atTop, ω ∈ {ω' | a < debtPath γ x₀ shock t ω'}} ⊆ E a := by
      intro ω hω m
      refine hω.mono fun t ht => ?_
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      simp only [Set.mem_ofPred_eq] at ht
      linarith
    intro h0
    have := (hfreq.trans (measure_mono hsub)).trans_eq h0
    rw [nonpos_iff_eq_zero, mul_eq_zero] at this
    rcases this with h | h
    · exact hdef c h
    · rw [ENNReal.ofReal_eq_zero] at h
      norm_num at h
  -- Kolmogorov's 0-1 law
  have hone : ∀ n : ℕ, ∀ᵐ ω ∂(iidSystem ν).μ, ω ∈ E n := by
    intro n
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop coordSigma_le (iIndep_coord ν)
      (htail n) with h | h
    · exact absurd h (hpos n)
    · have hm : MeasurableSet (E n) :=
        (limsup_le_iSup.trans (iSup_le coordSigma_le)) _ (htail n)
      rw [ae_iff]
      have := (prob_compl_eq_zero_iff hm).2 h
      simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hone] with ω hω M
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  refine (hω n 0).mono fun t ht => ?_
  simp only [CharP.cast_eq_zero, zero_add, div_one] at ht
  linarith

/-! ### i.i.d. Gaussian surpluses as a process -/

/-- Cochrane (2023), p. 197: a non-degenerate Gaussian law puts positive mass on deficits of
every size. -/
theorem gaussian_Iic_ne_zero (m : ℝ) {v : NNReal} (hv : v ≠ 0) (c : ℝ) :
    gaussianReal m v (Set.Iic (-c)) ≠ 0 := by
  intro h
  have h2 := gaussianReal_absolutelyContinuous' m hv h
  rw [Real.volume_Iic] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197 (**i.i.d. Gaussian surpluses as a process**): with surpluses
`σ_t` i.i.d. `N(m, v)`, `v ≠ 0`, on `ℕ → ℝ`, and `0 ≤ γ < 1`, the debt ratio is almost surely
unbounded above: it exceeds every level infinitely often, from every initial debt. -/
theorem gaussian_process_unbounded (m : ℝ) {v : NNReal} (hv : v ≠ 0) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb m v)).μ, ∀ M : ℝ,
      ∃ᶠ t in atTop, M < debtPath γ x₀ shock t ω := by
  have hint : Integrable id (gaussianReal m v) := by
    have h := memLp_id_gaussianReal (μ := m) (v := v) 1
    rw [ENNReal.coe_one, memLp_one_iff_integrable] at h
    exact h
  exact iid_unbounded_of_integrable (ν := gaussianProb m v) hint (gaussian_Iic_ne_zero m hv)
    hγ0 hγ1 x₀

/-- Cochrane (2023), p. 197 ("no value of debt is sustainable", **Gaussian process**): with
i.i.d. non-degenerate Gaussian surpluses, for every debt limit `M` the event that debt stays
at or below `M` forever has probability zero. -/
theorem gaussian_process_not_sustainable (m : ℝ) {v : NNReal} (hv : v ≠ 0) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x₀ M : ℝ) :
    (iidSystem (gaussianProb m v)).μ {ω | ∀ t, debtPath γ x₀ shock t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [gaussian_process_unbounded m hv hγ0 hγ1 x₀] with ω hω hall
  obtain ⟨t, ht⟩ := (hω M).exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197: on the Gaussian process every surplus has the Gaussian law, so the
process satisfies the law hypothesis of `DebtLimitStochastic.gaussian_iid_unbounded` but, by
`gaussian_iid_unbounded_vacuous`, never its upper-bound hypothesis; `gaussian_process_unbounded`
is the theorem that actually applies. -/
theorem gaussian_process_law (m : ℝ) (v : NNReal) (t : ℕ) :
    Measure.map (shock t) (iidSystem (gaussianProb m v)).μ = gaussianReal m v :=
  Measure.infinitePi_map_eval _ t

/-! ### The managed surplus as an adapted process -/

/-- Cochrane (2023), p. 197: the managed surplus `σ_t = ε_t + max 0 (γ x_t − ε_t − x̄)`. -/
noncomputable def managedSurplus (γ x₀ xbar : ℝ) (ε : ℕ → (ℕ → ℝ) → ℝ) (t : ℕ)
    (ω : ℕ → ℝ) : ℝ :=
  ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)

variable (ν) in
/-- Cochrane (2023), p. 197 ("we must already imagine a managed surplus process"): with
i.i.d. shocks `ε_t = ω_t`, the managed debt ratio `x_t` and the managed surplus `σ_t` are known
at date `t`: the management rule is a genuine adapted policy. -/
theorem managed_adapted (γ x₀ xbar : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (managedPath γ x₀ xbar shock t) ∧
      Measurable[(iidSystem ν).𝓕 t] (managedSurplus γ x₀ xbar shock t) := by
  have hx : ∀ t, Measurable[(iidSystem ν).𝓕 t] (managedPath γ x₀ xbar shock t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      have ih' := ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hs := measurable_shock ν (Nat.le_succ t)
      have hf : managedPath γ x₀ xbar shock (t + 1) = fun ω =>
          γ * managedPath γ x₀ xbar shock t ω -
            (shock t ω + max 0 (γ * managedPath γ x₀ xbar shock t ω - shock t ω - xbar)) := rfl
      rw [hf]
      exact (ih'.const_mul γ).sub (hs.add (measurable_const.max
        (((ih'.const_mul γ).sub hs).sub measurable_const)))
  refine ⟨hx t, ?_⟩
  have hs := measurable_shock ν (le_refl t)
  exact hs.add (measurable_const.max (((hx t).const_mul γ).sub hs |>.sub measurable_const))

/-- Cochrane (2023), p. 197: on the i.i.d. process the managed surplus keeps the debt ratio at
or below the limit `x̄` from date 1 on, on every path. -/
theorem managedPath_le_process (γ x₀ xbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    managedPath γ x₀ xbar shock (t + 1) ω ≤ xbar :=
  managedPath_le γ x₀ xbar shock t ω

end Cochrane.FiscalConstraints.DebtLimitStochasticMeasure
