/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEPicard

/-!
# Existence for stochastic differential equations: the Picard iterates converge

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B4). Continues
`TidyR12SDEPicard` (coefficients `SDECoeff`, Picard map `TidyR12SDEPicard.picard`, uniqueness
`TidyR12SDEPicard.sde_unique`) with existence.

## The construction

`picardSeq`: `X⁰ = ξ`, `Xⁿ⁺¹ = Φ(Xⁿ)`. With `c = 2L²(T − s + 1)(T − s)`, the Gronwall iteration
gives `E[(Xⁿ⁺¹_t − Xⁿ_t)²] ≤ M₀cⁿ/n!` uniformly on `[s, T]` (`picardSeq_diff_le`); Titu's
inequality with weights `2^{-j}` gives `E[(Xˡ⁺ᵐ_t − Xˡ_t)²] ≤ 2·2^{-l}S`, `S = M₀Σ(2c)ʲ/j!`
(`picardSeq_cauchy`). `sdeSol` is the adapted mean-square limit (completeness of `L²`,
`TidyR7ItoL2.exists_L2Tendsto`); the error is `≤ 4·2^{-l}S` uniformly (`sdeSol_err`), so the
limit is mean-square continuous (`sdeSol_ms`) and a fixed point of `Φ` (`sdeSol_fixed`).

## Main results

* **`sde_existsUnique`**: for `0 ≤ s ≤ T`, `ξ` square integrable and `𝓕_s`-measurable,
  `SDECoeff` coefficients `b, σ`: there is a mean-square continuous `X` on `[s, T]` with
  `X_s = ξ` a.s. and `X_t = ξ + ∫_s^t b(u, X_u) du + ∫_s^t σ(u, X_u) dW` a.s. for every
  `t ∈ [s, T]`, and every mean-square continuous solution agrees with it a.s. at every `t`.
* `sdeSol_itoProcessMS`: the solution is an `TidyR12SDEProcess.ItoProcessMS` with drift
  `b(u, X_u)` and diffusion `σ(u, X_u)`.
-/

namespace Cochrane.Monetarism.TidyR12SDEExist

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR10DoobFubini Cochrane.Monetarism.TidyR12SDETools
  Cochrane.Monetarism.TidyR12SDEProcess Cochrane.Monetarism.TidyR12SDEPicard
open scoped ENNReal NNReal Nat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Picard iterates** `X⁰ = ξ`,
`Xⁿ⁺¹ = Φ(Xⁿ)` of `dX = b(t, X)dt + σ(t, X)dW`, `X_s = ξ`. -/
noncomputable def picardSeq (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (b σ : ℝ → ℝ → ℝ) (ξ : Ω → ℝ) (s : ℝ) : ℕ → ℝ → Ω → ℝ
  | 0 => fun _ => ξ
  | n + 1 => picard P 𝓕 W b σ ξ s (picardSeq P 𝓕 W b σ ξ s n)

variable {P : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {b σ : ℝ → ℝ → ℝ}
  {ξ : Ω → ℝ} {s T L Kb Kσ : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: every Picard iterate starts at `ξ`. -/
theorem picardSeq_self (n : ℕ) : picardSeq P 𝓕 W b σ ξ s n s = ξ := by
  cases n with
  | zero => rfl
  | succ n => exact picard_self _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: every Picard iterate is mean-square continuous on
`[s, T]`, `0 ≤ s`. -/
theorem picardSeq_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∀ n, MSIntegrand P 𝓕 (picardSeq P 𝓕 W b σ ξ s n) s T := by
  intro n
  induction n with
  | zero => exact msIntegrand_const hξ hξ2
  | succ n ih => exact picard_ms hB hW h𝓕 hs hb hσ hξ2 hξ ih

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the successive differences decay factorially**:
for some `M₀ ≥ 0` and all `n`, `t ∈ [s, T]`,
`E[(Xⁿ⁺¹_t − Xⁿ_t)²] ≤ M₀(2L²(T − s + 1)(T − s))ⁿ/n!`. -/
theorem picardSeq_diff_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∃ M₀, 0 ≤ M₀ ∧ ∀ n, ∀ t ∈ Set.Icc s T,
      ∫ ω, (picardSeq P 𝓕 W b σ ξ s (n + 1) t ω - picardSeq P 𝓕 W b σ ξ s n t ω) ^ 2 ∂P
        ≤ M₀ * (2 * L ^ 2 * (T - s + 1) * (T - s)) ^ n / n ! := by
  have hms := picardSeq_ms hB hW h𝓕 hs hb hσ hξ2 hξ
  obtain ⟨M₀, hM₀, hM⟩ := exists_bound_integral_sq_ms (MSIntegrand.sub (hms 1) (hms 0))
  refine ⟨M₀, hM₀, fun n t ht => ?_⟩
  set K := 2 * L ^ 2 * (T - s + 1) with hKdef
  have hK : 0 ≤ K := by
    have : 0 ≤ T - s + 1 := by linarith
    positivity
  have h := iterate_bound (s := s) (T := T) (K := K) (M := M₀)
    (f := fun n t => ∫ ω, (picardSeq P 𝓕 W b σ ξ s (n + 1) t ω
      - picardSeq P 𝓕 W b σ ξ s n t ω) ^ 2 ∂P) hK
    (fun n => continuousOn_integral_sq_ms (MSIntegrand.sub (hms (n + 1)) (hms n)))
    (fun t ht => hM t ht)
    (fun n t ht => picard_sub_sq_le hB hW h𝓕 hs hb hσ (hms (n + 1)) (hms n) ht) n t ht
  refine h.trans ?_
  have h1 : K * (t - s) ≤ K * (T - s) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK
  have h2 : (K * (t - s)) ^ n ≤ (K * (T - s)) ^ n :=
    pow_le_pow_left₀ (mul_nonneg hK (sub_nonneg.2 ht.1)) h1 n
  have h3 : M₀ * (K * (t - s)) ^ n ≤ M₀ * (K * (T - s)) ^ n := mul_le_mul_of_nonneg_left h2 hM₀
  exact div_le_div_of_nonneg_right h3 (Nat.cast_nonneg _)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: Titu's inequality with weights `2^{-(l+j)}`:
`(Σ_{j<m} D_j)² ≤ 2·2^{-l} Σ_{j<m} D_j²·2^{l+j}`. -/
theorem sq_sum_le_geom (l m : ℕ) (D : ℕ → ℝ) :
    (∑ j ∈ Finset.range m, D j) ^ 2
      ≤ 2 * (1 / 2) ^ l * ∑ j ∈ Finset.range m, D j ^ 2 / (1 / 2) ^ (l + j) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  have hg : ∀ j ∈ Finset.range m, (0 : ℝ) < (1 / 2) ^ (l + j) := fun _ _ => by positivity
  have h := Finset.sq_sum_div_le_sum_sq_div (Finset.range m) D hg
  have hS : 0 < ∑ j ∈ Finset.range m, ((1 : ℝ) / 2) ^ (l + j) :=
    Finset.sum_pos hg ⟨0, Finset.mem_range.2 hm⟩
  have hS2 : ∑ j ∈ Finset.range m, ((1 : ℝ) / 2) ^ (l + j) ≤ 2 * (1 / 2) ^ l := by
    have e : ∑ j ∈ Finset.range m, ((1 : ℝ) / 2) ^ (l + j)
        = (1 / 2) ^ l * ∑ j ∈ Finset.range m, ((1 : ℝ) / 2) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => pow_add _ _ _
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le m) (by positivity)
  rw [div_le_iff₀ hS] at h
  have hR : 0 ≤ ∑ j ∈ Finset.range m, D j ^ 2 / (1 / 2) ^ (l + j) :=
    Finset.sum_nonneg fun j hj => div_nonneg (sq_nonneg _) (hg j hj).le
  calc (∑ j ∈ Finset.range m, D j) ^ 2
      ≤ (∑ j ∈ Finset.range m, D j ^ 2 / (1 / 2) ^ (l + j)) *
          ∑ j ∈ Finset.range m, ((1 : ℝ) / 2) ^ (l + j) := h
    _ ≤ (∑ j ∈ Finset.range m, D j ^ 2 / (1 / 2) ^ (l + j)) * (2 * (1 / 2) ^ l) :=
        mul_le_mul_of_nonneg_left hS2 hR
    _ = 2 * (1 / 2) ^ l * ∑ j ∈ Finset.range m, D j ^ 2 / (1 / 2) ^ (l + j) := by ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Picard iterates are uniformly mean-square
Cauchy**: there is `S ≥ 0` with `E[(Xˡ⁺ᵐ_t − Xˡ_t)²] ≤ 2·2^{-l}S` for all `l, m` and
`t ∈ [s, T]`. -/
theorem picardSeq_cauchy (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∃ S, 0 ≤ S ∧ ∀ l m, ∀ t ∈ Set.Icc s T,
      ∫ ω, (picardSeq P 𝓕 W b σ ξ s (l + m) t ω - picardSeq P 𝓕 W b σ ξ s l t ω) ^ 2 ∂P
        ≤ 2 * (1 / 2) ^ l * S := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hms := picardSeq_ms hB hW h𝓕 hs hb hσ hξ2 hξ
  obtain ⟨M₀, hM₀, hM⟩ := picardSeq_diff_le hB hW h𝓕 hs hsT hb hσ hξ2 hξ
  set c := 2 * L ^ 2 * (T - s + 1) * (T - s) with hc
  set e : ℕ → ℝ := fun i => M₀ * ((2 * c) ^ i / i !) with he
  have hsum : Summable e := (Real.summable_pow_div_factorial (2 * c)).mul_left M₀
  have he0 : ∀ i, 0 ≤ e i := fun i => by
    have hc0 : 0 ≤ c := by
      have : 0 ≤ T - s + 1 := by linarith
      have : 0 ≤ T - s := by linarith
      positivity
    positivity
  refine ⟨∑' i, e i, tsum_nonneg he0, fun l m t ht => ?_⟩
  set X := picardSeq P 𝓕 W b σ ξ s with hX
  set D : ℕ → Ω → ℝ := fun j ω => X (l + j + 1) t ω - X (l + j) t ω with hD
  have htel : ∀ ω, X (l + m) t ω - X l t ω = ∑ j ∈ Finset.range m, D j ω := fun ω => by
    have := Finset.sum_range_sub (fun j => X (l + j) t ω) m
    simp only [add_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by simp only [hD, add_assoc]
  have hDm : ∀ j, MemLp (D j) 2 P := fun j => ((hms _).memLp t ht).sub ((hms _).memLp t ht)
  have iR : Integrable (fun ω => 2 * (1 / 2) ^ l *
      ∑ j ∈ Finset.range m, D j ω ^ 2 / (1 / 2) ^ (l + j)) P :=
    (integrable_finsetSum _ fun j _ => (hDm j).integrable_sq.div_const _).const_mul _
  have hpt : ∀ ω, (X (l + m) t ω - X l t ω) ^ 2 ≤
      2 * (1 / 2) ^ l * ∑ j ∈ Finset.range m, D j ω ^ 2 / (1 / 2) ^ (l + j) := fun ω => by
    rw [htel]
    exact sq_sum_le_geom l m fun j => D j ω
  refine (integral_mono (((hms _).memLp t ht).sub ((hms _).memLp t ht)).integrable_sq iR
    hpt).trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hDm j).integrable_sq.div_const _]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hterm : ∀ j ∈ Finset.range m, ∫ ω, D j ω ^ 2 / (1 / 2) ^ (l + j) ∂P ≤ e (l + j) := by
    intro j _
    rw [integral_div]
    have h1 := hM (l + j) t ht
    have hpos : (0 : ℝ) < (1 / 2) ^ (l + j) := by positivity
    rw [div_le_iff₀ hpos]
    refine h1.trans_eq ?_
    simp only [he, mul_pow, one_div, inv_pow]
    field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  have e1 : ∑ j ∈ Finset.range m, e (l + j) = ∑ i ∈ Finset.Ico l (l + m), e i := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  rw [e1]
  exact hsum.sum_le_tsum _ fun i _ => he0 i

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `2·2^{-l}S → 0`. -/
theorem tendsto_geom_mul (S : ℝ) :
    Tendsto (fun l : ℕ => 2 * (1 / 2 : ℝ) ^ l * S) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)).const_mul 2 |>.mul_const S
  simpa using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the solution** of
`dX = b(t, X)dt + σ(t, X)dW`, `X_s = ξ`: at each `t`, a chosen `𝓕_t`-strongly measurable
mean-square limit of the Picard iterates if one exists, else `0` (hypothesis-free, like
`TidyR7ItoIntegral.itoInt`). -/
noncomputable def sdeSol (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (b σ : ℝ → ℝ → ℝ) (ξ : Ω → ℝ) (s : ℝ) (t : ℝ) : Ω → ℝ := by
  classical
  exact if h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧
      L2Tendsto P (fun n => picardSeq P 𝓕 W b σ ξ s n t) Y then h.choose else 0

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Picard iterates converge in mean square** at
every `t ∈ [s, T]`, to the `𝓕_t`-measurable `sdeSol … t`. -/
theorem sdeSol_spec (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) {t : ℝ}
    (ht : t ∈ Set.Icc s T) :
    StronglyMeasurable[𝓕 t] (sdeSol P 𝓕 W b σ ξ s t) ∧
      L2Tendsto P (fun n => picardSeq P 𝓕 W b σ ξ s n t) (sdeSol P 𝓕 W b σ ξ s t) := by
  classical
  have hms := picardSeq_ms hB hW h𝓕 hs hb hσ hξ2 hξ
  obtain ⟨S, -, hS⟩ := picardSeq_cauchy hB hW h𝓕 hs hsT hb hσ hξ2 hξ
  have hex : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧
      L2Tendsto P (fun n => picardSeq P 𝓕 W b σ ξ s n t) Y := by
    refine exists_L2Tendsto (𝓕.le t) (fun n => (hms n).adapted t ht)
      (fun n => (hms n).memLp t ht) fun ε hε => ?_
    obtain ⟨N, hN⟩ := (tendsto_geom_mul S).eventually (gt_mem_nhds hε) |>.exists_forall_of_atTop
    refine ⟨N, fun k hk l hl => ?_⟩
    have hmono : ∀ j ≥ N, 2 * (1 / 2 : ℝ) ^ j * S ≤ ε := fun j hj => (hN j hj).le
    rcases le_total l k with hlk | hkl
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlk
      exact (hS l m t ht).trans (hmono l hl)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have e : ∫ ω, (picardSeq P 𝓕 W b σ ξ s k t ω - picardSeq P 𝓕 W b σ ξ s (k + m) t ω) ^ 2 ∂P
          = ∫ ω, (picardSeq P 𝓕 W b σ ξ s (k + m) t ω - picardSeq P 𝓕 W b σ ξ s k t ω) ^ 2 ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => by ring)
      rw [e]
      exact (hS k m t ht).trans (hmono k hk)
  have e : sdeSol P 𝓕 W b σ ξ s t = hex.choose := by simp only [sdeSol, hex, ↓reduceDIte]
  rw [e]
  exact hex.choose_spec

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Picard error is uniformly small**:
`E[(X_t − Xˡ_t)²] ≤ 4·2^{-l}S` for all `l` and `t ∈ [s, T]`. -/
theorem sdeSol_err (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∃ S, 0 ≤ S ∧ ∀ l, ∀ t ∈ Set.Icc s T,
      ∫ ω, (sdeSol P 𝓕 W b σ ξ s t ω - picardSeq P 𝓕 W b σ ξ s l t ω) ^ 2 ∂P
        ≤ 4 * (1 / 2) ^ l * S := by
  obtain ⟨S, hS0, hS⟩ := picardSeq_cauchy hB hW h𝓕 hs hsT hb hσ hξ2 hξ
  refine ⟨S, hS0, fun l t ht => ?_⟩
  have hL := (sdeSol_spec hB hW h𝓕 hs hsT hb hσ hξ2 hξ ht).2
  set X := picardSeq P 𝓕 W b σ ξ s with hX
  set Y := sdeSol P 𝓕 W b σ ξ s t with hY
  have hlim : Tendsto (fun k => 2 * ∫ ω, (X k t ω - Y ω) ^ 2 ∂P + 2 * (2 * (1 / 2) ^ l * S))
      atTop (𝓝 (2 * 0 + 2 * (2 * (1 / 2) ^ l * S))) :=
    (hL.2.2.const_mul 2).add_const _
  have hb' : ∀ᶠ k in atTop, ∫ ω, (Y ω - X l t ω) ^ 2 ∂P
      ≤ 2 * ∫ ω, (X k t ω - Y ω) ^ 2 ∂P + 2 * (2 * (1 / 2) ^ l * S) := by
    filter_upwards [eventually_ge_atTop l] with k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine (integral_sq_sub_le (hL.1 (l + m)) hL.2.1 (hL.1 l)).trans ?_
    have := hS l m t ht
    linarith
  have h2 := ge_of_tendsto hlim hb'
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the solution is a mean-square continuous process**
on `[s, T]` (uniform mean-square limit of mean-square continuous iterates). -/
theorem sdeSol_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    MSIntegrand P 𝓕 (sdeSol P 𝓕 W b σ ξ s) s T where
  adapted _ ht := (sdeSol_spec hB hW h𝓕 hs hsT hb hσ hξ2 hξ ht).1
  memLp _ ht := (sdeSol_spec hB hW h𝓕 hs hsT hb hσ hξ2 hξ ht).2.2.1
  cont ε hε := by
    obtain ⟨S, -, hS⟩ := sdeSol_err hB hW h𝓕 hs hsT hb hσ hξ2 hξ
    have hms := picardSeq_ms hB hW h𝓕 hs hb hσ hξ2 hξ
    have h4 : Tendsto (fun l : ℕ => 2 * (2 * (1 / 2 : ℝ) ^ l * S)) atTop (𝓝 (2 * 0)) :=
      (tendsto_geom_mul S).const_mul 2
    rw [mul_zero] at h4
    obtain ⟨l, hl⟩ := (h4.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 12))).exists
    obtain ⟨δ, hδ, hδX⟩ := (hms l).cont (ε / 8) (by positivity)
    refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
    set X := picardSeq P 𝓕 W b σ ξ s l with hX
    set Y := sdeSol P 𝓕 W b σ ξ s with hY
    have mYu := (sdeSol_spec hB hW h𝓕 hs hsT hb hσ hξ2 hξ hu).2.2.1
    have mYv := (sdeSol_spec hB hW h𝓕 hs hsT hb hσ hξ2 hξ hv).2.2.1
    have mXu := (hms l).memLp u hu
    have mXv := (hms l).memLp v hv
    have e1 := hS l u hu
    have e2 := hS l v hv
    have sym : ∀ f g : Ω → ℝ, ∫ ω, (f ω - g ω) ^ 2 ∂P = ∫ ω, (g ω - f ω) ^ 2 ∂P :=
      fun f g => integral_congr_ae (ae_of_all _ fun ω => by ring)
    have a1 := integral_sq_sub_le mXu mYu mYv
    have a2 := integral_sq_sub_le mXv mXu mYv
    have a3 := hδX v hv u hu (by rw [abs_sub_comm]; exact huv)
    rw [sym (X u) (Y u)] at a1
    rw [sym (X v) (Y v)] at a2
    change ∫ ω, (Y u ω - Y v ω) ^ 2 ∂P ≤ ε
    have : 4 * (1 / 2 : ℝ) ^ l * S < ε / 12 := by linarith
    linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the solution starts at `ξ`**, `X_s = ξ` a.s. -/
theorem sdeSol_init (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    sdeSol P 𝓕 W b σ ξ s s =ᵐ[P] ξ := by
  have h := (sdeSol_spec hB hW h𝓕 hs hsT hb hσ hξ2 hξ ⟨le_rfl, hsT⟩).2
  have h' : L2Tendsto P (fun n => picardSeq P 𝓕 W b σ ξ s n s) ξ :=
    ⟨fun n => by simp only [picardSeq_self]; exact hξ2, hξ2, by simp [picardSeq_self]⟩
  exact ae_eq_of_L2Tendsto h h'

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the solution is a fixed point of the Picard map**:
for every `t ∈ [s, T]`, a.s. `X_t = ξ + ∫_s^t b(u, X_u) du + ∫_s^t σ(u, X_u) dW`. -/
theorem sdeSol_fixed (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∀ t ∈ Set.Icc s T, sdeSol P 𝓕 W b σ ξ s t =ᵐ[P]
      picard P 𝓕 W b σ ξ s (sdeSol P 𝓕 W b σ ξ s) t := by
  intro t ht
  obtain ⟨S, -, hS⟩ := sdeSol_err hB hW h𝓕 hs hsT hb hσ hξ2 hξ
  have hms := picardSeq_ms hB hW h𝓕 hs hb hσ hξ2 hξ
  have hY := sdeSol_ms hB hW h𝓕 hs hsT hb hσ hξ2 hξ
  have hΦ := picard_ms hB hW h𝓕 hs hb hσ hξ2 hξ hY
  set Y := sdeSol P 𝓕 W b σ ξ s with hYdef
  set X := picardSeq P 𝓕 W b σ ξ s with hX
  set K := 2 * L ^ 2 * (T - s + 1) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ T - s + 1 := by linarith
    positivity
  set r : ℕ → ℝ := fun n => 2 * (K * ((t - s) * (4 * (1 / 2) ^ n * S)))
    + 2 * (4 * (1 / 2) ^ (n + 1) * S) with hr
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h1 := ((((hg.const_mul 4).mul_const S).const_mul (t - s)).const_mul K).const_mul 2
    have h2 := (((hg.comp (tendsto_add_atTop_nat 1)).const_mul 4).mul_const S).const_mul 2
    simpa [hr, Function.comp_def] using h1.add h2
  have hbound : ∀ n, ∫ ω, (Y t ω - picard P 𝓕 W b σ ξ s Y t ω) ^ 2 ∂P ≤ r n := by
    intro n
    have mY := hY.memLp t ht
    have mΦ := hΦ.memLp t ht
    have mX := (hms (n + 1)).memLp t ht
    have a1 := integral_sq_sub_le mX mY mΦ
    have a2 := picard_sub_sq_le (ξ := ξ) hB hW h𝓕 hs hb hσ hY (hms n) ht
    have hD := MSIntegrand.sub hY (hms n)
    have a3 : ∫ u in s..t, ∫ ω, (Y u ω - X n u ω) ^ 2 ∂P ≤ (t - s) * (4 * (1 / 2) ^ n * S) :=
      intervalIntegral_integral_sq_le ht.1 (hD.mono le_rfl ht.2) fun u hu =>
        hS n u ⟨hu.1, hu.2.trans ht.2⟩
    have a4 := hS (n + 1) t ht
    have e1 : ∫ ω, (X (n + 1) t ω - picard P 𝓕 W b σ ξ s Y t ω) ^ 2 ∂P
        = ∫ ω, (picard P 𝓕 W b σ ξ s Y t ω - picard P 𝓕 W b σ ξ s (X n) t ω) ^ 2 ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => by simp only [hX, picardSeq]; ring)
    have e2 : ∫ ω, (X (n + 1) t ω - Y t ω) ^ 2 ∂P = ∫ ω, (Y t ω - X (n + 1) t ω) ^ 2 ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [e1] at a1
    rw [e2] at a1
    have a5 : K * ∫ u in s..t, ∫ ω, (Y u ω - X n u ω) ^ 2 ∂P
        ≤ K * ((t - s) * (4 * (1 / 2) ^ n * S)) := mul_le_mul_of_nonneg_left a3 hK0
    simp only [hr]
    linarith
  have h0 : ∫ ω, (Y t ω - picard P 𝓕 W b σ ξ s Y t ω) ^ 2 ∂P = 0 :=
    le_antisymm (ge_of_tendsto' hr0 hbound) (integral_nonneg fun _ => sq_nonneg _)
  exact ae_eq_of_integral_sq_sub_eq_zero (hY.memLp t ht) (hΦ.memLp t ht) h0

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: existence and uniqueness for
`dX = b(t, X)dt + σ(t, X)dW` on `[s, T]`, `X_s = ξ`.** For a Brownian motion with an admissible
filtration, `0 ≤ s ≤ T`, `ξ` square integrable and `𝓕_s`-measurable, and `SDECoeff`
coefficients (Lipschitz, linear growth, time-continuous): there is a mean-square continuous
`X` on `[s, T]` with `X_s = ξ` a.s. and, for every `t ∈ [s, T]`, a.s.
`X_t = ξ + ∫_s^t b(u, X_u) du + ∫_s^t σ(u, X_u) dW`; every mean-square continuous solution
agrees with it a.s. at every `t ∈ [s, T]`. -/
theorem sde_existsUnique (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∃ X : ℝ → Ω → ℝ, MSIntegrand P 𝓕 X s T ∧ X s =ᵐ[P] ξ ∧
      (∀ t ∈ Set.Icc s T, X t =ᵐ[P] fun ω => ξ ω + dtInt P 𝓕 (fun u ω => b u (X u ω)) s t ω
        + itoInt P 𝓕 W (fun u ω => σ u (X u ω)) s t ω) ∧
      ∀ Y : ℝ → Ω → ℝ, MSIntegrand P 𝓕 Y s T →
        (∀ t ∈ Set.Icc s T, Y t =ᵐ[P] fun ω => ξ ω + dtInt P 𝓕 (fun u ω => b u (Y u ω)) s t ω
          + itoInt P 𝓕 W (fun u ω => σ u (Y u ω)) s t ω) →
        ∀ t ∈ Set.Icc s T, Y t =ᵐ[P] X t :=
  ⟨sdeSol P 𝓕 W b σ ξ s, sdeSol_ms hB hW h𝓕 hs hsT hb hσ hξ2 hξ,
    sdeSol_init hB hW h𝓕 hs hsT hb hσ hξ2 hξ, sdeSol_fixed hB hW h𝓕 hs hsT hb hσ hξ2 hξ,
    fun _ hY hYe => sde_unique hB hW h𝓕 hs hsT hb hσ hY
      (sdeSol_ms hB hW h𝓕 hs hsT hb hσ hξ2 hξ) hYe
      (sdeSol_fixed hB hW h𝓕 hs hsT hb hσ hξ2 hξ)⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the SDE solution is an Itô process with
mean-square continuous coefficients** (`TidyR12SDEProcess.ItoProcessMS`) on `[s, T]`, with
drift `b(u, X_u)` and diffusion `σ(u, X_u)`. -/
theorem sdeSol_itoProcessMS (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L Kb)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ItoProcessMS P 𝓕 W (sdeSol P 𝓕 W b σ ξ s)
      (fun u ω => b u (sdeSol P 𝓕 W b σ ξ s u ω))
      (fun u ω => σ u (sdeSol P 𝓕 W b σ ξ s u ω)) s T := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hY := sdeSol_ms hB hW h𝓕 hs hsT hb hσ hξ2 hξ
  refine ⟨hY.adapted, hY.memLp s ⟨le_rfl, hsT⟩, hb.msIntegrand_comp hY,
    hσ.msIntegrand_comp hY, fun u hu => ?_⟩
  filter_upwards [sdeSol_fixed hB hW h𝓕 hs hsT hb hσ hξ2 hξ u hu,
    sdeSol_init hB hW h𝓕 hs hsT hb hσ hξ2 hξ] with ω h1 h2
  rw [h1, h2]
  rfl

end Cochrane.Monetarism.TidyR12SDEExist
