/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.TidyR6InertialMeasure
import PriceLevelDetermination.TidyR6InertialAnyExpectation
import PriceLevelDetermination.InertialBoundaryExist
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Existence on the boundary of Proposition 2.8 on a probability space

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 633–634, with the
conditional expectations `μ[· | 𝓕 t]` of a filtered probability space (`TidyR6InertialMeasure`).
For the rule `φ_π π + h(î_{−1})` this module constructs the equilibrium with small disturbances:
the backward solutions `V_{k+1}(t) = g⁻¹(μ[V_k(t + 1) | 𝓕 t] − f_t)` (clipped to their a.s. bounds
so that every bound holds in every state), their almost-sure uniform convergence, and the limit.

## Main results

* `bseq_props` and the a.s. Cauchy step inside its proof: the backward solutions of horizons
  `k` and `k + m` differ by at most `b_k` a.s., where `b_{k+1} + κ b_{k+1}³ = b_k` and `b_k → 0`.
* `exists_unique_affine_measure`: for `φ_π ≠ 0`, `h(0) = 0`, `h` continuous and the expanding
  diagonal, every initial rate and all disturbances with `(1 + |φ_π|) E₀ ≤ κR³` (a.s. bounds
  `|r̂_t|, |ν_t| ≤ E₀`), there is an equilibrium with `|î_t| ≤ R` a.s., and every equilibrium
  agrees with it a.s. at every date.
-/

namespace Woodford.PriceLevelDetermination.TidyR6InertialMeasureExist

open MeasureTheory Filter
open scoped Topology
open TidyR6InertialMeasure (lagI MeasEq integrable_of_known condExp_known_sub lagI_known
  lagI_bound unique_affine_measure)
open InertialBoundaryExist (phi_mono surjective_of_expanding)

/-! ### Clipping and the inverse of the diagonal -/

/-- Woodford (2003), App. A.3, p. 634 (tool): clipping to `[−C, C]`. -/
def clip (C y : ℝ) : ℝ := max (-C) (min C y)

/-- Woodford (2003), App. A.3, p. 634 (tool): properties of clipping: continuous, bounded by
`C`, the identity on `[−C, C]`, and `1`-Lipschitz. -/
theorem clip_props {C : ℝ} (hC : 0 ≤ C) :
    Continuous (clip C) ∧ (∀ y, |clip C y| ≤ C) ∧ (∀ y, |y| ≤ C → clip C y = y) ∧
      ∀ a b, |clip C a - clip C b| ≤ |a - b| := by
  refine ⟨(continuous_const.max (continuous_const.min continuous_id)), fun y => ?_,
    fun y hy => ?_, fun a b => ?_⟩
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · rw [abs_le] at hy
    simp only [clip, min_eq_right hy.2, max_eq_right hy.1]
  · simp only [clip]
    rw [max_comm (-C), max_comm (-C)]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rcases le_total C a with ha | ha <;> rcases le_total C b with hb | hb
    · rw [min_eq_left ha, min_eq_left hb, sub_self, abs_zero]
      exact abs_nonneg _
    · rw [min_eq_left ha, min_eq_right hb, abs_le]
      constructor <;> cases abs_cases (a - b) <;> linarith
    · rw [min_eq_right ha, min_eq_left hb, abs_le]
      constructor <;> cases abs_cases (a - b) <;> linarith
    · rw [min_eq_right ha, min_eq_right hb]

/-- Woodford (2003), App. A.3, p. 634 (tool): an inverse of a continuous expanding map `g`
(it is onto by `InertialBoundaryExist.surjective_of_expanding`). -/
noncomputable def ginv (g : ℝ → ℝ) (hs : Function.Surjective g) (y : ℝ) : ℝ :=
  Classical.choose (hs y)

/-- Woodford (2003), App. A.3, p. 634 (tool): `g(g⁻¹ y) = y`, and `g⁻¹` is measurable (it is
monotone, `g` being strictly monotone). -/
theorem ginv_props {g : ℝ → ℝ} {κ : ℝ} (hgc : Continuous g) (hκ : 0 < κ)
    (hexp : ∀ a b, |a - b| + κ * |a - b| ^ 3 ≤ |g a - g b|) (hs : Function.Surjective g) :
    (∀ y, g (ginv g hs y) = y) ∧ Measurable (ginv g hs) := by
  have hspec : ∀ y, g (ginv g hs y) = y := fun y => Classical.choose_spec (hs y)
  refine ⟨hspec, ?_⟩
  obtain ⟨τ, -, hτ⟩ := TidyR6InertialAnyExpectation.exists_sign_of_expanding hgc hκ hexp
  rcases le_or_gt 0 τ with hτ0 | hτ0
  · refine Monotone.measurable fun a b hab => ?_
    by_contra hlt
    push Not at hlt
    have := hτ _ _ hlt
    rw [hspec, hspec] at this
    rcases hτ0.lt_or_eq with h | h
    · nlinarith
    · rw [← h] at this
      simp at this
  · refine Antitone.measurable fun a b hab => ?_
    by_contra hlt
    push Not at hlt
    have := hτ _ _ hlt
    rw [hspec, hspec] at this
    nlinarith

/-! ### The bound sequence -/

/-- Woodford (2003), App. A.3, p. 634 (tool): the bound sequence `b_0 = B₀`,
`b_{k+1} + κ b_{k+1}³ = b_k`. -/
noncomputable def bseq (κ B0 : ℝ) : ℕ → ℝ
  | 0 => B0
  | k + 1 => Classical.epsilon fun x => 0 ≤ x ∧ x + κ * x ^ 3 = bseq κ B0 k

/-- Woodford (2003), App. A.3, p. 634 (tool): the bound sequence is nonnegative, satisfies
`b_{k+1} + κ b_{k+1}³ = b_k`, and tends to `0`. -/
theorem bseq_props {κ B0 : ℝ} (hκ : 0 < κ) (hB0 : 0 ≤ B0) :
    (∀ k, 0 ≤ bseq κ B0 k) ∧ (∀ k, bseq κ B0 (k + 1) + κ * bseq κ B0 (k + 1) ^ 3 = bseq κ B0 k) ∧
      Tendsto (bseq κ B0) atTop (𝓝 0) := by
  have hex : ∀ b : ℝ, 0 ≤ b → ∃ x, 0 ≤ x ∧ x + κ * x ^ 3 = b := by
    intro b hb
    have hc : ContinuousOn (fun x : ℝ => x + κ * x ^ 3) (Set.Icc 0 b) := by fun_prop
    have hmem : b ∈ Set.Icc ((fun x : ℝ => x + κ * x ^ 3) 0) ((fun x : ℝ => x + κ * x ^ 3) b) := by
      simp only [Set.mem_Icc]
      constructor
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
        exact hb
      · have : 0 ≤ κ * b ^ 3 := by positivity
        linarith
    obtain ⟨x, hx, hxb⟩ := intermediate_value_Icc hb hc hmem
    exact ⟨x, hx.1, hxb⟩
  have h0 : ∀ k, 0 ≤ bseq κ B0 k ∧
      (0 ≤ bseq κ B0 (k + 1) ∧ bseq κ B0 (k + 1) + κ * bseq κ B0 (k + 1) ^ 3 = bseq κ B0 k) := by
    intro k
    induction k with
    | zero =>
      exact ⟨hB0, Classical.epsilon_spec (hex _ hB0)⟩
    | succ k ih =>
      exact ⟨ih.2.1, Classical.epsilon_spec (hex _ ih.2.1)⟩
  refine ⟨fun k => (h0 k).1, fun k => (h0 k).2.2, ?_⟩
  have hanti : Antitone (bseq κ B0) := antitone_nat_of_succ_le fun k => by
    have := (h0 k).2.2
    have : 0 ≤ κ * bseq κ B0 (k + 1) ^ 3 := mul_nonneg hκ.le (pow_nonneg (h0 (k + 1)).1 3)
    linarith
  have hbb : BddBelow (Set.range (bseq κ B0)) := ⟨0, by rintro _ ⟨k, rfl⟩; exact (h0 k).1⟩
  have ht := tendsto_atTop_ciInf hanti hbb
  set L := ⨅ k, bseq κ B0 k with hL
  have hL0 : 0 ≤ L := le_ciInf fun k => (h0 k).1
  have ht1 : Tendsto (fun k => bseq κ B0 (k + 1) + κ * bseq κ B0 (k + 1) ^ 3) atTop
      (𝓝 (L + κ * L ^ 3)) := by
    have := ht.comp (tendsto_add_atTop_nat 1)
    exact this.add ((this.pow 3).const_mul κ)
  have heq : L + κ * L ^ 3 = L := by
    refine tendsto_nhds_unique ht1 ?_
    have : (fun k => bseq κ B0 (k + 1) + κ * bseq κ B0 (k + 1) ^ 3) = bseq κ B0 :=
      funext fun k => (h0 k).2.2
    rw [this]
    exact ht
  have hLz : L = 0 := by
    have : κ * L ^ 3 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hκ.ne'
    · exact pow_eq_zero_iff (by norm_num) |>.mp h
  rwa [hLz] at ht

/-! ### The backward solutions -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

variable (μ) in
/-- Woodford (2003), App. A.3, p. 634 (the construction): the backward solution with horizon
`t + k`, `V_0 = 0`, `V_{k+1}(t) = g⁻¹(clip_R(μ[V_k(t + 1) | 𝓕 t]) − f_t)`. -/
noncomputable def backM (𝓕 : Filtration ℕ mΩ) (gi : ℝ → ℝ) (R : ℝ) (fc : ℕ → Ω → ℝ) :
    ℕ → ℕ → Ω → ℝ
  | 0, _ => fun _ => 0
  | k + 1, t => fun ω => gi (clip R (μ[backM 𝓕 gi R fc k (t + 1) | 𝓕 t] ω) - fc t ω)

set_option maxHeartbeats 3200000 in
-- the construction, its almost-sure convergence and the verification of both conditions
/-- **Existence and uniqueness on the boundary `φ_π ≠ 0` on a probability space** (Woodford
(2003), Prop. 2.8, p. 96; App. A.3, pp. 632–634): with conditional expectations `μ[· | 𝓕 t]`, for
the rule `Ψ(π, i) = φ_π π + h(i)` with `φ_π ≠ 0`, `h` continuous, `h(0) = 0` and the expanding
diagonal `|g(i) − g(i')| ≥ |i − i'| + κ|i − i'|³`, for every initial rate and all integrable
disturbances with `|r̂_t|, |ν_t| ≤ E₀` a.s. and `(1 + |φ_π|)E₀ ≤ κR³`, there is an equilibrium
with `|î_t| ≤ R` a.s., and every equilibrium agrees with it a.s. at every date. -/
theorem exists_unique_affine_measure (𝓕 : Filtration ℕ mΩ) {Ψ : ℝ × ℝ → ℝ} {φ κ R E0 : ℝ}
    {h : ℝ → ℝ} (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) (hφ : φ ≠ 0) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hh : Continuous h) (hh0 : h 0 = 0)
    (hexp : ∀ i i', |i - i'| + κ * |i - i'| ^ 3 ≤ |(φ * i + h i) - (φ * i' + h i')|)
    (im1 : ℝ) {r ν : ℕ → Ω → ℝ} (hr : ∀ t, Integrable (r t) μ) (hν : ∀ t, Integrable (ν t) μ)
    (hrb : ∀ t, ∀ᵐ ω ∂μ, |r t ω| ≤ E0) (hνb : ∀ t, ∀ᵐ ω ∂μ, |ν t ω| ≤ E0)
    (hsmall : (1 + |φ|) * E0 ≤ κ * R ^ 3) :
    ∃ π i : ℕ → Ω → ℝ, MeasEq μ 𝓕 Ψ im1 r ν π i ∧ (∀ t, ∀ᵐ ω ∂μ, |i t ω| ≤ R) ∧
      ∀ π' i' : ℕ → Ω → ℝ, MeasEq μ 𝓕 Ψ im1 r ν π' i' →
        ∀ t, π' t =ᵐ[μ] π t ∧ i' t =ᵐ[μ] i t := by
  set g : ℝ → ℝ := fun z => φ * z + h z with hg
  have hgc : Continuous g := (continuous_const.mul continuous_id).add hh
  have hg0 : g 0 = 0 := by simp only [hg, mul_zero, hh0, add_zero]
  have hexp' : ∀ a b, |a - b| + κ * |a - b| ^ 3 ≤ |g a - g b| := hexp
  have hs := surjective_of_expanding hgc hκ hexp'
  obtain ⟨hgi, hgim⟩ := ginv_props hgc hκ hexp' hs
  set gi := ginv g hs with hgidef
  have hE0 : 0 ≤ E0 := by
    obtain ⟨ω, hω⟩ := (hrb 0).exists
    exact (abs_nonneg _).trans hω
  set F0 := (1 + |φ|) * E0 with hF0def
  have hF0 : 0 ≤ F0 := by positivity
  obtain ⟨hcR, hbR, hidR, hlipR⟩ := clip_props hR
  obtain ⟨hcF, hbF, hidF, -⟩ := clip_props hF0
  set f : ℕ → Ω → ℝ := fun t => μ[ν (t + 1) - φ • r t | 𝓕 t] with hf
  have hfb : ∀ t, ∀ᵐ ω ∂μ, |f t ω| ≤ F0 := by
    intro t
    refine ae_bdd_abs_condExp_of_ae_bdd_abs ?_
    filter_upwards [hνb (t + 1), hrb t] with ω h1 h2
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc |ν (t + 1) ω - φ * r t ω| ≤ |ν (t + 1) ω| + |φ| * |r t ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ E0 + |φ| * E0 := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg φ))
      _ = F0 := by rw [hF0def]; ring
  set fc : ℕ → Ω → ℝ := fun t ω => clip F0 (f t ω) with hfc
  set V := backM μ 𝓕 gi R fc with hV
  have hV0 : ∀ t, V 0 t = fun _ => 0 := fun _ => rfl
  have hVs : ∀ k t ω, g (V (k + 1) t ω) = clip R (μ[V k (t + 1) | 𝓕 t] ω) - fc t ω :=
    fun k t ω => hgi _
  have hVm : ∀ k t, StronglyMeasurable[𝓕 t] (V k t) := by
    intro k t
    cases k with
    | zero => exact stronglyMeasurable_const
    | succ k =>
      have h1 : Measurable[𝓕 t] (fun ω => clip R (μ[V k (t + 1) | 𝓕 t] ω) - fc t ω) :=
        (hcR.measurable.comp stronglyMeasurable_condExp.measurable).sub
          (hcF.measurable.comp stronglyMeasurable_condExp.measurable)
      exact (hgim.comp h1).stronglyMeasurable
  have hVb : ∀ k t ω, |V k t ω| ≤ R := by
    intro k t ω
    cases k with
    | zero => rw [hV0, abs_zero]; exact hR
    | succ k =>
      have he := hexp' (V (k + 1) t ω) 0
      rw [sub_zero, hg0, sub_zero, hVs] at he
      have h1 : |clip R (μ[V k (t + 1) | 𝓕 t] ω) - fc t ω| ≤ R + F0 :=
        (abs_sub _ _).trans (add_le_add (hbR _) (hbF _))
      by_contra hc
      push Not at hc
      have h3 : R ^ 3 < |V (k + 1) t ω| ^ 3 := pow_lt_pow_left₀ hc hR (by norm_num)
      have h4 := mul_lt_mul_of_pos_left h3 hκ
      linarith
  have hVI : ∀ k t, Integrable (V k t) μ := fun k t =>
    integrable_of_known (hVm k t) (Eventually.of_forall (hVb k t))
  -- almost-sure Cauchy property
  set b := bseq κ (2 * R) with hb
  obtain ⟨hb0, hbstep, hbto⟩ := bseq_props hκ (by positivity : (0 : ℝ) ≤ 2 * R)
  have hcau : ∀ k t m, ∀ᵐ ω ∂μ, |V k t ω - V (k + m) t ω| ≤ b k := by
    intro k
    induction k with
    | zero =>
      intro t m
      refine Eventually.of_forall fun ω => ?_
      rw [hV0, zero_add]
      change |0 - V m t ω| ≤ bseq κ (2 * R) 0
      simp only [bseq, zero_sub, abs_neg]
      linarith [hVb m t ω]
    | succ k ih =>
      intro t m
      have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := 𝓕 t) (ih (t + 1) m)
      filter_upwards [hc, condExp_sub (hVI k (t + 1)) (hVI (k + m) (t + 1)) (𝓕 t)] with ω h1 h2
      have h1' : |μ[V k (t + 1) | 𝓕 t] ω - μ[V (k + m) (t + 1) | 𝓕 t] ω| ≤ b k := by
        have e : (fun ω => V k (t + 1) ω - V (k + m) (t + 1) ω) = V k (t + 1) - V (k + m) (t + 1) :=
          rfl
        rw [e, h2] at h1
        exact h1
      have he := hexp' (V (k + 1) t ω) (V (k + m + 1) t ω)
      rw [hVs, hVs] at he
      have hl := hlipR (μ[V k (t + 1) | 𝓕 t] ω) (μ[V (k + m) (t + 1) | 𝓕 t] ω)
      have e2 : clip R (μ[V k (t + 1) | 𝓕 t] ω) - fc t ω -
          (clip R (μ[V (k + m) (t + 1) | 𝓕 t] ω) - fc t ω) =
          clip R (μ[V k (t + 1) | 𝓕 t] ω) - clip R (μ[V (k + m) (t + 1) | 𝓕 t] ω) := by ring
      rw [e2] at he
      have hΦ : |V (k + 1) t ω - V (k + m + 1) t ω| +
          κ * |V (k + 1) t ω - V (k + m + 1) t ω| ^ 3 ≤ b (k + 1) + κ * b (k + 1) ^ 3 := by
        rw [hbstep k]
        linarith
      rw [show k + 1 + m = k + m + 1 by omega]
      by_contra hcon
      push Not at hcon
      have h3 : b (k + 1) ^ 3 < |V (k + 1) t ω - V (k + m + 1) t ω| ^ 3 :=
        pow_lt_pow_left₀ hcon (hb0 _) (by norm_num)
      have h4 := mul_lt_mul_of_pos_left h3 hκ
      linarith
  have hcau' : ∀ t, ∀ᵐ ω ∂μ, ∀ k m, |V k t ω - V (k + m) t ω| ≤ b k := fun t =>
    ae_all_iff.mpr fun k => ae_all_iff.mpr fun m => hcau k t m
  -- the limit
  set i : ℕ → Ω → ℝ := fun t ω => limUnder atTop (fun k => V k t ω) with hi
  have him : ∀ t, StronglyMeasurable[𝓕 t] (i t) := fun t =>
    @StronglyMeasurable.limUnder ℕ Ω ℝ (𝓕 t) _ _ atTop _ (fun k => V k t) _ _
      (fun k => hVm k t)
  have hconv : ∀ t, ∀ᵐ ω ∂μ, ∀ k, |V k t ω - i t ω| ≤ b k := by
    intro t
    filter_upwards [hcau' t] with ω hω
    have hcs : CauchySeq fun k => V k t ω :=
      cauchySeq_of_le_tendsto_0 (fun N => 2 * b N) (fun n m N hn hm => by
        rw [Real.dist_eq]
        have h1 := hω N (n - N)
        have h2 := hω N (m - N)
        rw [show N + (n - N) = n by omega] at h1
        rw [show N + (m - N) = m by omega] at h2
        refine (abs_sub_le _ (V N t ω) _).trans ?_
        rw [abs_sub_comm (V n t ω)]
        linarith) (by simpa using hbto.const_mul 2)
    obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcs
    have hic : i t ω = c := hc.limUnder_eq
    intro k
    rw [hic]
    have ht : Tendsto (fun m => |V k t ω - V (m + k) t ω|) atTop (𝓝 |V k t ω - c|) :=
      (tendsto_const_nhds.sub (hc.comp (tendsto_add_atTop_nat k))).abs
    refine le_of_tendsto' ht fun m => ?_
    have := hω k m
    rwa [add_comm k m] at this
  have hib : ∀ t, ∀ᵐ ω ∂μ, |i t ω| ≤ R := by
    intro t
    filter_upwards [hconv t] with ω hω
    have ht : Tendsto (fun k => V k t ω) atTop (𝓝 (i t ω)) :=
      tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun k => dist_nonneg)
        (fun k => by rw [Real.dist_eq]; exact hω k) hbto)
    exact le_of_tendsto' ht.abs fun k => hVb k t ω
  have hiI : ∀ t, Integrable (i t) μ := fun t => integrable_of_known (him t) (hib t)
  -- the law of motion of the interest rate
  have heq : ∀ t, ∀ᵐ ω ∂μ, μ[i (t + 1) | 𝓕 t] ω = g (i t ω) + f t ω := by
    intro t
    have h1 : ∀ k, ∀ᵐ ω ∂μ, |μ[V k (t + 1) | 𝓕 t] ω - μ[i (t + 1) | 𝓕 t] ω| ≤ b k := by
      intro k
      have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := 𝓕 t)
        ((hconv (t + 1)).mono fun ω h => h k)
      filter_upwards [hc, condExp_sub (hVI k (t + 1)) (hiI (t + 1)) (𝓕 t)] with ω h2 h3
      have e : (fun ω => V k (t + 1) ω - i (t + 1) ω) = V k (t + 1) - i (t + 1) := rfl
      rw [e, h3] at h2
      exact h2
    have h2 : ∀ k, ∀ᵐ ω ∂μ, |μ[V k (t + 1) | 𝓕 t] ω| ≤ R := fun k =>
      ae_bdd_abs_condExp_of_ae_bdd_abs (Eventually.of_forall (hVb k (t + 1)))
    filter_upwards [ae_all_iff.mpr h1, ae_all_iff.mpr h2, hfb t, hconv t] with ω e1 e2 e3 e4
    have hk : ∀ k, g (V (k + 1) t ω) = μ[V k (t + 1) | 𝓕 t] ω - f t ω := fun k => by
      rw [hVs, hidR _ (e2 k), hfc]
      simp only [hidF _ e3]
    have hVt : Tendsto (fun k => V k t ω) atTop (𝓝 (i t ω)) :=
      tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun k => dist_nonneg)
        (fun k => by rw [Real.dist_eq]; exact e4 k) hbto)
    have hA : Tendsto (fun k => g (V (k + 1) t ω)) atTop (𝓝 (g (i t ω))) :=
      (hgc.tendsto _).comp (hVt.comp (tendsto_add_atTop_nat 1))
    have hB : Tendsto (fun k => μ[V k (t + 1) | 𝓕 t] ω - f t ω) atTop
        (𝓝 (μ[i (t + 1) | 𝓕 t] ω - f t ω)) := by
      refine Tendsto.sub_const ?_ _
      exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun k => dist_nonneg)
        (fun k => by rw [Real.dist_eq]; exact e1 k) hbto)
    have hfun : (fun k => g (V (k + 1) t ω)) = fun k => μ[V k (t + 1) | 𝓕 t] ω - f t ω :=
      funext hk
    rw [hfun] at hA
    have := tendsto_nhds_unique hB hA
    linarith
  -- inflation
  set L := max R |im1| with hL
  obtain ⟨Ch, hCh⟩ := (isCompact_Icc (a := -L) (b := L)).exists_bound_of_continuousOn
    hh.continuousOn
  set π : ℕ → Ω → ℝ := fun t ω => (i t ω - h (lagI im1 i t ω) - μ[ν t | 𝓕 t] ω) / φ with hπ
  have hhlm : ∀ t, StronglyMeasurable[𝓕 t] (fun ω => h (lagI im1 i t ω)) := fun t =>
    hh.comp_stronglyMeasurable (lagI_known him t)
  have hhlb : ∀ t, ∀ᵐ ω ∂μ, |h (lagI im1 i t ω)| ≤ Ch := by
    intro t
    filter_upwards [lagI_bound (im1 := im1) hib t] with ω hω
    have := hCh _ ⟨(abs_le.mp hω).1, (abs_le.mp hω).2⟩
    rwa [Real.norm_eq_abs] at this
  have hπm : ∀ t, StronglyMeasurable[𝓕 t] (π t) := fun t =>
    ((((him t).sub (hhlm t)).sub (stronglyMeasurable_condExp (μ := μ)
      (f := ν t))).measurable.div_const φ).stronglyMeasurable
  have hνc : ∀ t, ∀ᵐ ω ∂μ, |μ[ν t | 𝓕 t] ω| ≤ E0 := fun t =>
    ae_bdd_abs_condExp_of_ae_bdd_abs (hνb t)
  set Mπ := (R + Ch + E0) / |φ| with hMπ
  have hπb : ∀ t, ∀ᵐ ω ∂μ, |π t ω| ≤ Mπ := by
    intro t
    filter_upwards [hib t, hhlb t, hνc t] with ω h1 h2 h3
    simp only [hπ, abs_div]
    exact div_le_div_of_nonneg_right ((abs_sub _ _).trans
      (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3)) (abs_nonneg φ)
  have hπI : ∀ t, Integrable (π t) μ := fun t => integrable_of_known (hπm t) (hπb t)
  have hMeq : MeasEq μ 𝓕 Ψ im1 r ν π i := by
    refine ⟨fun t => ⟨hπm t, him t⟩, ⟨max Mπ R, fun t => ?_⟩, fun t => ?_, fun t => ?_⟩
    · filter_upwards [hπb t, hib t] with ω h1 h2
      exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_right _ _)⟩
    · -- the Fisher equation
      have hHm : StronglyMeasurable[𝓕 t] (fun ω => h (i t ω)) :=
        hh.comp_stronglyMeasurable (him t)
      have hHb : ∀ᵐ ω ∂μ, |h (i t ω)| ≤ Ch := hhlb (t + 1)
      have hHI : Integrable (fun ω => h (i t ω)) μ := integrable_of_known hHm hHb
      have hπe : π (t + 1) =
          φ⁻¹ • (i (t + 1) - (fun ω => h (i t ω)) - μ[ν (t + 1) | 𝓕 (t + 1)]) := by
        funext ω
        simp only [hπ, lagI, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [div_eq_inv_mul]
      have e1 := condExp_smul (m := 𝓕 t) (μ := μ) φ⁻¹
        (i (t + 1) - (fun ω => h (i t ω)) - μ[ν (t + 1) | 𝓕 (t + 1)])
      have e2 := condExp_sub ((hiI (t + 1)).sub hHI) (integrable_condExp (m := 𝓕 (t + 1))
        (f := ν (t + 1))) (𝓕 t)
      have e3 := condExp_sub (hiI (t + 1)) hHI (𝓕 t)
      have e4 : μ[fun ω => h (i t ω) | 𝓕 t] = fun ω => h (i t ω) :=
        condExp_of_stronglyMeasurable (𝓕.le t) hHm hHI
      have e5 : μ[μ[ν (t + 1) | 𝓕 (t + 1)] | 𝓕 t] =ᵐ[μ] μ[ν (t + 1) | 𝓕 t] :=
        condExp_condExp_of_le (𝓕.mono (Nat.le_succ t)) (𝓕.le (t + 1))
      have e6 := condExp_sub (hν (t + 1)) ((hr t).smul φ) (𝓕 t)
      have e7 := condExp_smul (m := 𝓕 t) (μ := μ) φ (r t)
      have hπμ : μ[π (t + 1) | 𝓕 t] =ᵐ[μ] fun ω => i t ω - μ[r t | 𝓕 t] ω := by
        rw [hπe]
        filter_upwards [e1, e2, e3, e5, e6, e7, heq t] with ω h1 h2 h3 h5 h6 h7 h9
        rw [h1]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h2]
        simp only [Pi.sub_apply]
        rw [h3]
        simp only [Pi.sub_apply]
        rw [e4, h5, h9]
        have hf' : f t ω = μ[ν (t + 1) | 𝓕 t] ω - φ * μ[r t | 𝓕 t] ω := by
          simp only [hf]
          rw [h6]
          simp only [Pi.sub_apply]
          rw [h7]
          simp only [Pi.smul_apply, smul_eq_mul]
        rw [hf']
        simp only [hg]
        field_simp
        ring
      have hk := condExp_known_sub (him t) (hib t) (hπI (t + 1))
      have hs := condExp_sub ((hiI t).sub (hπI (t + 1))) (hr t) (𝓕 t)
      filter_upwards [hs, hk, hπμ] with ω h1 h2 h3
      rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, Pi.zero_apply]
      ring
    · -- the rule
      have hfun : (i t - (fun ω => Ψ (π t ω, lagI im1 i t ω)) - ν t) = μ[ν t | 𝓕 t] - ν t := by
        funext ω
        simp only [Pi.sub_apply, hΨ, hπ]
        field_simp
        ring
      rw [hfun]
      have hcc : μ[μ[ν t | 𝓕 t] | 𝓕 t] = μ[ν t | 𝓕 t] :=
        condExp_of_stronglyMeasurable (𝓕.le t) stronglyMeasurable_condExp integrable_condExp
      filter_upwards [condExp_sub (integrable_condExp (m := 𝓕 t) (f := ν t)) (hν t) (𝓕 t)]
        with ω h1
      rw [h1, Pi.sub_apply, hcc, sub_self, Pi.zero_apply]
  exact ⟨π, i, hMeq, hib, fun π' i' he' t =>
    unique_affine_measure hΨ hφ hκ hh hexp hr hν he' hMeq t⟩

end Woodford.PriceLevelDetermination.TidyR6InertialMeasureExist
