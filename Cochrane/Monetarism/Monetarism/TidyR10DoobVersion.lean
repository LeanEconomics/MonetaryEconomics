/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10DoobIto
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# An adapted continuous version of the Itô integral on `[s, ∞)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (Track 3, chunk B3, item 2). `TidyR7ItoContinuity.exists_continuous_modification` gives,
for each fixed `T`, a modification of `t ↦ ∫_s^t H dW` with a.s. continuous paths on `[s, T]`,
not shown adapted. Here one process works for all times and is adapted to `𝓕` itself.

## The construction (`exists_adapted_continuous_version`)

For an adapted `Y` with `Y_s = 0` that has, for every `N`, a modification with a.s. continuous
paths on `[s, s + N]`, put
`X_t(ω) = lim_L Y_{q_L(t)}(ω)`, `q_L(t) = s + ⌊(t − s)2^L⌋/2^L` (`dyadicFloor`),
the limit (limUnder) of `Y` along the dyadic points `q_L(t) ≤ t` approaching `t` from the
left. Each `Y_{q_L(t)}` is `𝓕_t`-measurable, so `X_t` is (Mathlib
`MeasureTheory.StronglyMeasurable.limUnder`) — no completion of `𝓕` is needed. On the full-measure
event where every modification `X^N` is continuous and agrees with `Y` at all dyadic points
(countably many), `X = X^N` on `[s, s + N]` for all `N`, so `X` is continuous on `ℝ` (it is `0`
for `t ≤ s`).

## Main results

* `exists_adapted_continuous_version`: the general construction.
* `exists_adapted_continuous_itoInt` (**item 2 for `𝓕`**): for `H` admissible on every
  `[s, T]` with a fixed bound and `W` with a.s. continuous paths, there is `X` with: `X_t`
  `𝓕_t`-strongly measurable for every `t`; `X_t = ∫_s^t H dW` a.s. for every `t`; `X_t = 0` for
  `t ≤ s` (every `ω`); a.s. every path continuous on `ℝ`; `X` a martingale for `𝓕`; and
  `E[sup_{[s,T]} X²] ≤ 4E[∫_s^T H²]` for every `T > s`.

What holds for `𝓕` itself is exactly this: adapted, with paths continuous outside a null set.
Continuity of EVERY path while staying adapted requires the null set to be in every `𝓕_t`; that is
done for the completed filtration in `TidyR10DoobAugment`.
-/

namespace Cochrane.Monetarism.TidyR10DoobVersion

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoContinuity Cochrane.Monetarism.TidyR7CondDominated
  Cochrane.Monetarism.TidyR10DoobIto
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ} {s : ℝ}

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): the dyadic point `s + ⌊(t − s)2^L⌋/2^L` of level
`L` at or below `t` (`= s` for `t ≤ s`). -/
noncomputable def dyadicFloor (s : ℝ) (L : ℕ) (t : ℝ) : ℝ :=
  s + (⌊(t - s) * 2 ^ L⌋₊ : ℝ) / 2 ^ L

/-- Cochrane (2023), A1 §1.6, p. 567: for `t ≤ s` the dyadic point is `s`. -/
theorem dyadicFloor_of_le (L : ℕ) {t : ℝ} (ht : t ≤ s) : dyadicFloor s L t = s := by
  have h : (t - s) * 2 ^ L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [dyadicFloor, Nat.floor_of_nonpos h]

/-- Cochrane (2023), A1 §1.6, p. 567: for `s ≤ t` the dyadic point lies in `[s, t]` and within
`2^{−L}` of `t`. -/
theorem dyadicFloor_mem (L : ℕ) {t : ℝ} (ht : s ≤ t) :
    dyadicFloor s L t ∈ Set.Icc s t ∧ t - dyadicFloor s L t ≤ 1 / 2 ^ L := by
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  have hy : 0 ≤ (t - s) * 2 ^ L := mul_nonneg (sub_nonneg.2 ht) h2.le
  have h1 : (⌊(t - s) * 2 ^ L⌋₊ : ℝ) ≤ (t - s) * 2 ^ L := Nat.floor_le hy
  have h3 : (t - s) * 2 ^ L < ⌊(t - s) * 2 ^ L⌋₊ + 1 := Nat.lt_floor_add_one _
  have e : t = s + (t - s) * 2 ^ L / 2 ^ L := by field_simp; ring
  refine ⟨⟨le_add_of_nonneg_right (by positivity), ?_⟩, ?_⟩
  · rw [dyadicFloor]
    nth_rewrite 2 [e]
    have := div_le_div_of_nonneg_right h1 h2.le
    linarith
  · rw [dyadicFloor]
    nth_rewrite 1 [e]
    have : ((t - s) * 2 ^ L - ⌊(t - s) * 2 ^ L⌋₊) / 2 ^ L ≤ 1 / 2 ^ L :=
      div_le_div_of_nonneg_right (by linarith) h2.le
    rw [sub_div] at this
    linarith

/-- Cochrane (2023), A1 §1.6, p. 567: for `s ≤ t` the dyadic points converge to `t` within
`[s, t]`. -/
theorem tendsto_dyadicFloor {t : ℝ} (ht : s ≤ t) :
    Tendsto (fun L => dyadicFloor s L t) atTop (𝓝[Set.Icc s t] t) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun L => (dyadicFloor_mem L ht).1⟩
  have h0 : Tendsto (fun L : ℕ => 1 / (2 : ℝ) ^ L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun L => ?_)
    h0)
  obtain ⟨h1, h2⟩ := dyadicFloor_mem L ht
  rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith [h1.2])]
  exact h2

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): the left dyadic limit
`lim_L Y_{q_L(t)}(ω)` (limUnder). -/
noncomputable def dyadicLim (s : ℝ) (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop fun L => Y (dyadicFloor s L t) ω

/-- Cochrane (2023), A1 §1.6, p. 567: if `Y_s = 0` then the left dyadic limit vanishes for
`t ≤ s`. -/
theorem dyadicLim_of_le {Y : ℝ → Ω → ℝ} (hYs : ∀ ω, Y s ω = 0) {t : ℝ} (ht : t ≤ s) (ω : Ω) :
    dyadicLim s Y t ω = 0 := by
  have e : (fun L => Y (dyadicFloor s L t) ω) = fun _ => 0 := funext fun L => by
    rw [dyadicFloor_of_le L ht, hYs]
  simp only [dyadicLim, e]
  exact tendsto_const_nhds.limUnder_eq

/-- Cochrane (2023), A1 §1.6, p. 567: **the left dyadic limit of an adapted process is
adapted**, if `Y_s = 0`. -/
theorem stronglyMeasurable_dyadicLim {Y : ℝ → Ω → ℝ} (hY : ∀ t, StronglyMeasurable[𝓕 t] (Y t))
    (hYs : ∀ ω, Y s ω = 0) (t : ℝ) : StronglyMeasurable[𝓕 t] (dyadicLim s Y t) := by
  have hL : ∀ L, StronglyMeasurable[𝓕 t] (Y (dyadicFloor s L t)) := by
    intro L
    rcases le_total s t with hst | hts
    · exact (hY _).mono (𝓕.mono (dyadicFloor_mem L hst).1.2)
    · have e : Y (dyadicFloor s L t) = fun _ => 0 := funext fun ω => by
        rw [dyadicFloor_of_le L hts, hYs]
      rw [e]
      exact stronglyMeasurable_const
  let := 𝓕 t
  exact StronglyMeasurable.limUnder hL

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 2): adapted continuous versions.**
Let `Y` be adapted with `Y_s = 0`, and suppose for every `N` some `X^N` has `X^N_t = Y_t` a.s.
for each `t ∈ [s, s + N]` and a.s. continuous paths on `[s, s + N]`. Then there is `X` with
`X_t` `𝓕_t`-strongly measurable for every `t`, `X_t = Y_t` a.s. for every `t ≥ s`, `X_t = 0`
for `t ≤ s` and every `ω`, and a.s. every path continuous on `ℝ`. -/
theorem exists_adapted_continuous_version {Y : ℝ → Ω → ℝ}
    (hY : ∀ t, StronglyMeasurable[𝓕 t] (Y t)) (hYs : ∀ ω, Y s ω = 0)
    (hmod : ∀ N : ℕ, ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s (s + N), X t =ᵐ[P] Y t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s (s + N))) :
    ∃ X : ℝ → Ω → ℝ, (∀ t, StronglyMeasurable[𝓕 t] (X t)) ∧
      (∀ t, s ≤ t → X t =ᵐ[P] Y t) ∧ (∀ t ≤ s, ∀ ω, X t ω = 0) ∧
      ∀ᵐ ω ∂P, Continuous fun t => X t ω := by
  choose Xn hXnY hXnc using hmod
  set r : ℕ → ℕ → ℝ := fun L k => s + (k : ℝ) / 2 ^ L with hr
  have hgrid : ∀ᵐ ω ∂P, ∀ N L k : ℕ, r L k ∈ Set.Icc s (s + N) → Xn N (r L k) ω = Y (r L k) ω := by
    rw [ae_all_iff]
    intro N
    rw [ae_all_iff]
    intro L
    rw [ae_all_iff]
    intro k
    by_cases h : r L k ∈ Set.Icc s (s + N)
    · filter_upwards [hXnY N _ h] with ω hω
      exact fun _ => hω
    · exact ae_of_all _ fun ω h' => absurd h' h
  have hcont : ∀ᵐ ω ∂P, ∀ N : ℕ, ContinuousOn (fun t => Xn N t ω) (Set.Icc s (s + N)) :=
    ae_all_iff.2 hXnc
  -- on the good event, `X = X^N` on `[s, s + N]`
  have hagree : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ t ∈ Set.Icc s (s + N), dyadicLim s Y t ω = Xn N t ω := by
    filter_upwards [hgrid, hcont] with ω hg hc N t ht
    have hq : ∀ L, Xn N (dyadicFloor s L t) ω = Y (dyadicFloor s L t) ω := fun L =>
      hg N L _ ⟨(dyadicFloor_mem L ht.1).1.1, (dyadicFloor_mem L ht.1).1.2.trans ht.2⟩
    have hlim : Tendsto (fun L => Xn N (dyadicFloor s L t) ω) atTop (𝓝 (Xn N t ω)) :=
      ((hc N t ht).mono (Set.Icc_subset_Icc_right ht.2)).tendsto.comp (tendsto_dyadicFloor ht.1)
    have hlim' : Tendsto (fun L => Y (dyadicFloor s L t) ω) atTop (𝓝 (Xn N t ω)) :=
      hlim.congr hq
    exact hlim'.limUnder_eq
  refine ⟨dyadicLim s Y, stronglyMeasurable_dyadicLim hY hYs, fun t ht => ?_,
    fun t ht ω => dyadicLim_of_le hYs ht ω, ?_⟩
  · obtain ⟨N, hN⟩ := exists_nat_ge (t - s)
    have htN : t ∈ Set.Icc s (s + N) := ⟨ht, by linarith⟩
    filter_upwards [hagree, hXnY N t htN] with ω h1 h2
    rw [h1 N t htN, h2]
  · filter_upwards [hagree, hcont] with ω h1 h2
    refine continuous_iff_continuousAt.2 fun t0 => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (t0 - s)
    have hsN : s ≤ s + N := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    -- `X = X^N ∘ max(·, s)` on `(−∞, s + N]`
    have heq : ∀ t ≤ s + N, dyadicLim s Y t ω = Xn N (max t s) ω := by
      intro t ht
      rcases le_total t s with hts | hst
      · rw [dyadicLim_of_le hYs hts, max_eq_right hts, ← h1 N s ⟨le_rfl, hsN⟩,
          dyadicLim_of_le hYs le_rfl]
      · rw [max_eq_left hst]
        exact h1 N t ⟨hst, ht⟩
    have hg : ContinuousOn (fun t => Xn N (max t s) ω) (Set.Iic (s + N)) :=
      (h2 N).comp (continuous_id.max continuous_const).continuousOn fun t ht =>
        ⟨le_max_right _ _, max_le ht hsN⟩
    have hnhds : Set.Iic (s + N) ∈ 𝓝 t0 := Iic_mem_nhds (by linarith)
    exact ((hg.continuousAt hnhds).congr
      (Filter.eventually_of_mem hnhds fun t ht => (heq t ht).symm))

/-! ## The Itô integral -/

variable {W : ℝ≥0 → Ω → ℝ} {H : ℝ → Ω → ℝ} {C : ℝ}

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 2): an adapted continuous version of
`t ↦ ∫_s^t H dW` on `[s, ∞)`, adapted to `𝓕` itself.** Let `W` be pre-Brownian with measurable
values and a.s. continuous paths, `𝓕` admissible, `0 ≤ s`, and `H` admissible on every `[s, T]`
with one bound `C`. There is `X` such that: `X_t` is `𝓕_t`-strongly measurable for every `t`;
`X_t = ∫_s^t H dW` a.s. for every `t`; `X_t = 0` for `t ≤ s` and every `ω`; almost every path is
continuous on `ℝ`; `X` is a martingale for `𝓕`; and for every `T > s`,
`E[(sup_{[s,T]}|X|)²] ≤ 4E[∫_s^T H_u² du]`. -/
theorem exists_adapted_continuous_itoInt (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hH : ∀ T, ItoIntegrand P 𝓕 H s T C) :
    ∃ X : ℝ → Ω → ℝ, (∀ t, StronglyMeasurable[𝓕 t] (X t)) ∧
      (∀ t, X t =ᵐ[P] itoInt P 𝓕 W H s t) ∧ (∀ t ≤ s, ∀ ω, X t ω = 0) ∧
      (∀ᵐ ω ∂P, Continuous fun t => X t ω) ∧ Martingale X 𝓕 P ∧
      ∀ T, s < T → Integrable (fun ω => pathSup s T X ω ^ 2) P ∧
        ∫ ω, pathSup s T X ω ^ 2 ∂P ≤ 4 * ∫ ω, (∫ u in s..T, H u ω ^ 2) ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hYs : ∀ ω, itoInt P 𝓕 W H s s ω = 0 := fun ω => by rw [itoInt_of_le le_rfl]; rfl
  have hmod : ∀ N : ℕ, ∃ X : ℝ → Ω → ℝ,
      (∀ t ∈ Set.Icc s (s + N), X t =ᵐ[P] itoInt P 𝓕 W H s t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s (s + N)) := by
    intro N
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).lt_or_eq with hN | hN
    · obtain ⟨X, hX1, hX2⟩ := exists_continuous_modification hB hW h𝓕 hcont hs
        (by linarith : s < s + N) (hH (s + N))
      exact ⟨X, hX1, hX2⟩
    · refine ⟨fun t => itoInt P 𝓕 W H s t, fun _ _ => ae_of_all _ fun _ => rfl,
        ae_of_all _ fun ω => ?_⟩
      rw [← hN, add_zero, Set.Icc_self]
      exact continuousOn_singleton _ _
  obtain ⟨X, hXm, hXY, hX0, hXc⟩ := exists_adapted_continuous_version
    (fun t => stronglyMeasurable_itoInt) hYs hmod
  have hXI : ∀ t, X t =ᵐ[P] itoInt P 𝓕 W H s t := by
    intro t
    rcases le_total s t with hst | hts
    · exact hXY t hst
    · exact ae_of_all _ fun ω => by rw [hX0 t hts ω, itoInt_of_le hts]; rfl
  have hmart := martingale_itoInt hB hW h𝓕 hs hH
  refine ⟨X, hXm, hXI, hX0, hXc, ⟨hXm, fun i j hij => ?_⟩, fun T hsT => ?_⟩
  · exact (condExp_congr_ae (hXI j)).trans ((hmart.2 i j hij).trans (hXI i).symm)
  · exact doob_sq_itoInt hB hW h𝓕 hs hsT (hH T) (fun t _ => hXI t)
      (hXc.mono fun ω hω x _ => hω.continuousWithinAt)

end Cochrane.Monetarism.TidyR10DoobVersion
