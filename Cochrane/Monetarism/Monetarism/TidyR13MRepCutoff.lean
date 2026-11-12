/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR13MRepIntegral

/-!
# Integrands switched on over a sub-interval

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B6, item 1). A mean-square
continuous integrand `G` on `[b, a] ⊆ [s, t]`, switched off outside `(b, a]`
(`mrepCut b a G = 1_{(b, a]}·G`), jumps at `a` when `G_a ≠ 0` (it is then not mean-square
continuous on `[s, t]`; no theorem here proves that).
It does lie in the extended class `TidyR13MRepIntegral.MRepIntegrand` on `[s, t]`, and its
extended integral is `∫_b^a G dW`. Proof: the continuous bumps `ψ_n` (`mrepBump`; `0` off
`(b, a)`, `→ 1` on `(b, a)`) give mean-square continuous `G·ψ_n` on `[s, t]` (glued from three
pieces, `mrep_ms_glue`) converging to `1_{(b, a]}G` in `L²(dt × dP)` by dominated convergence;
`∫_s^t Gψ_n dW = ∫_b^a Gψ_n dW → ∫_b^a G dW`.

## Main results

* `mrep_ms_glue`, `mrep_ms_congr`: gluing and congruence for mean-square continuous integrands.
* `mrep_itoInt_zero`: `∫_s^t 0 dW = 0` a.s.
* `mrepBump` and its properties; `mrep_bump_L2Tendsto` (dominated convergence).
* `mrep_cut` (**headline**): `1_{(b, a]}G` is in the class on `[s, t]` and
  `∫_s^t 1_{(b, a]}G dW = ∫_b^a G dW` a.s.
-/

namespace Cochrane.Monetarism.TidyR13MRepCutoff

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoIntegral Cochrane.Monetarism.TidyR7ItoUnbounded
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR9ItoFormulaVariants
  Cochrane.Monetarism.TidyR8MonetarismItoDom Cochrane.Monetarism.TidyR13MRepIntegral
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s t : ℝ}

/-! ## Gluing mean-square continuous integrands -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a mean-square continuous integrand may be changed
off `[s, t]`. -/
theorem mrep_ms_congr {G G' : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (h : ∀ u ∈ Set.Icc s t, ∀ ω, G u ω = G' u ω) : MSIntegrand P 𝓕 G' s t where
  adapted u hu := by
    have e : G' u = G u := funext fun ω => (h u hu ω).symm
    rw [e]; exact hG.adapted u hu
  memLp u hu := by
    have e : G' u = G u := funext fun ω => (h u hu ω).symm
    rw [e]; exact hG.memLp u hu
  cont ε hε := by
    obtain ⟨δ, hδ, h1⟩ := hG.cont ε hε
    refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
    have e : ∫ ω, (G' u ω - G' v ω) ^ 2 ∂P = ∫ ω, (G u ω - G v ω) ^ 2 ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => by
        change (G' u ω - G' v ω) ^ 2 = (G u ω - G v ω) ^ 2
        rw [h u hu ω, h v hv ω])
    rw [e]
    exact h1 u hu v hv huv

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: gluing.** Mean-square continuous on `[s, r]` and on
`[r, t]` implies mean-square continuous on `[s, t]`
(`E[(G_u − G_v)²] ≤ 2E[(G_r − G_u)²] + 2E[(G_r − G_v)²]` across `r`). -/
theorem mrep_ms_glue {G : ℝ → Ω → ℝ} {r : ℝ} (h1 : MSIntegrand P 𝓕 G s r)
    (h2 : MSIntegrand P 𝓕 G r t) : MSIntegrand P 𝓕 G s t where
  adapted u hu := by
    rcases le_total u r with hur | hru
    · exact h1.adapted u ⟨hu.1, hur⟩
    · exact h2.adapted u ⟨hru, hu.2⟩
  memLp u hu := by
    rcases le_total u r with hur | hru
    · exact h1.memLp u ⟨hu.1, hur⟩
    · exact h2.memLp u ⟨hru, hu.2⟩
  cont ε hε := by
    obtain ⟨δ1, hδ1, c1⟩ := h1.cont (ε / 4) (by positivity)
    obtain ⟨δ2, hδ2, c2⟩ := h2.cont (ε / 4) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun u hu v hv huv => ?_⟩
    have hd1 : |u - v| ≤ δ1 := huv.trans (min_le_left _ _)
    have hd2 : |u - v| ≤ δ2 := huv.trans (min_le_right _ _)
    rcases le_total u r with hur | hru <;> rcases le_total v r with hvr | hrv
    · exact (c1 u ⟨hu.1, hur⟩ v ⟨hv.1, hvr⟩ hd1).trans (by linarith)
    · have hsr : s ≤ r := hu.1.trans hur
      have hrt : r ≤ t := hrv.trans hv.2
      have a1 := c1 r ⟨hsr, le_rfl⟩ u ⟨hu.1, hur⟩ (by
        rw [abs_le] at hd1 ⊢; constructor <;> linarith)
      have a2 := c2 r ⟨le_rfl, hrt⟩ v ⟨hrv, hv.2⟩ (by
        rw [abs_le] at hd2 ⊢; constructor <;> linarith)
      have h := integral_sq_sub_le (h1.memLp r ⟨hsr, le_rfl⟩) (h1.memLp u ⟨hu.1, hur⟩)
        (h2.memLp v ⟨hrv, hv.2⟩)
      linarith
    · have hsr : s ≤ r := hv.1.trans hvr
      have hrt : r ≤ t := hru.trans hu.2
      have a1 := c2 r ⟨le_rfl, hrt⟩ u ⟨hru, hu.2⟩ (by
        rw [abs_le] at hd2 ⊢; constructor <;> linarith)
      have a2 := c1 r ⟨hsr, le_rfl⟩ v ⟨hv.1, hvr⟩ (by
        rw [abs_le] at hd1 ⊢; constructor <;> linarith)
      have h := integral_sq_sub_le (h1.memLp r ⟨hsr, le_rfl⟩) (h2.memLp u ⟨hru, hu.2⟩)
        (h1.memLp v ⟨hv.1, hvr⟩)
      linarith
    · exact (c2 u ⟨hru, hu.2⟩ v ⟨hrv, hv.2⟩ hd2).trans (by linarith)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the zero integrand is mean-square continuous. -/
theorem mrep_ms_zero [IsFiniteMeasure P] : MSIntegrand P 𝓕 (fun _ _ => (0 : ℝ)) s t :=
  msIntegrand_const (Z := fun _ => (0 : ℝ)) stronglyMeasurable_const (memLp_const 0)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫_s^t 0 dW = 0` a.s. -/
theorem mrep_itoInt_zero : itoInt P 𝓕 W (fun _ _ => (0 : ℝ)) s t =ᵐ[P] 0 := by
  rcases lt_or_ge s t with hst | hts
  · have hL : L2Tendsto P (fun k => itoSum W (fun _ _ => (0 : ℝ)) (dyadic hst k)) 0 := by
      have e : ∀ k, itoSum W (fun _ _ => (0 : ℝ)) (dyadic hst k) = 0 := fun k =>
        funext fun ω => by simp [itoSum]
      simp_rw [e]
      exact ⟨fun _ => MemLp.zero, MemLp.zero, by simp⟩
    exact ae_eq_of_L2Tendsto (itoInt_spec hst ⟨0, stronglyMeasurable_const, hL⟩).2 hL
  · rw [itoInt_of_le hts]

/-! ## The bump functions -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the continuous bump
`ψ_n(u) = min 1 ((n + 1)·max 0 (min (u − b) (a − u)))`: `0` off `(b, a)`, `1` once
`min(u − b, a − u) ≥ 1/(n + 1)`. -/
noncomputable def mrepBump (b a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  min 1 (((n : ℝ) + 1) * max 0 (min (u - b) (a - u)))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `0 ≤ ψ_n ≤ 1`. -/
theorem mrepBump_mem (b a : ℝ) (n : ℕ) (u : ℝ) :
    0 ≤ mrepBump b a n u ∧ mrepBump b a n u ≤ 1 :=
  ⟨le_min zero_le_one (mul_nonneg (by positivity) (le_max_left _ _)), min_le_left _ _⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `ψ_n` is continuous. -/
theorem continuous_mrepBump (b a : ℝ) (n : ℕ) : Continuous (mrepBump b a n) := by
  unfold mrepBump
  fun_prop

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `ψ_n(u) = 0` for `u ∉ (b, a)`. -/
theorem mrepBump_eq_zero {b a : ℝ} (n : ℕ) {u : ℝ} (hu : u ≤ b ∨ a ≤ u) :
    mrepBump b a n u = 0 := by
  have hm : min (u - b) (a - u) ≤ 0 := by
    rcases hu with h | h
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  simp [mrepBump, max_eq_left hm]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `ψ_n(u) → 1` for `u ∈ (b, a)`. -/
theorem tendsto_mrepBump {b a u : ℝ} (hu : u ∈ Set.Ioo b a) :
    Tendsto (fun n => mrepBump b a n u) atTop (𝓝 1) := by
  have hm : 0 < min (u - b) (a - u) := lt_min (by linarith [hu.1]) (by linarith [hu.2])
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / min (u - b) (a - u))
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have h1 : 1 ≤ ((n : ℝ) + 1) * min (u - b) (a - u) := by
    have : 1 / min (u - b) (a - u) ≤ (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rwa [div_le_iff₀ hm] at this
  simp [mrepBump, max_eq_right hm.le, min_eq_left h1]

/-! ## The cut-off integrand -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`G` switched on over `(b, a]`**,
`(1_{(b, a]}G)_u = 1_{(b, a]}(u)·G_u`. -/
noncomputable def mrepCut (b a : ℝ) (G : ℝ → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun u ω => G u ω * (Set.Ioc b a).indicator (fun _ => (1 : ℝ)) u

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the bump `ψ_n` as a bounded deterministic
integrand. -/
theorem itoIntegrand_mrepBump (b a : ℝ) (n : ℕ) :
    TidyR7ItoIntegral.ItoIntegrand P 𝓕 (fun u _ => mrepBump b a n u) s t 1 where
  adapted _ _ := stronglyMeasurable_const
  bound u _ _ := by
    rw [abs_of_nonneg (mrepBump_mem b a n u).1]; exact (mrepBump_mem b a n u).2
  cont := ae_of_all _ fun _ => (continuous_mrepBump b a n).continuousOn

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G·ψ_n` is mean-square continuous on `[s, t]` for
`G` mean-square continuous on `[b, a]` (zero on `[s, b]` and `[a, t]`; glued). -/
theorem mrep_ms_bump [IsFiniteMeasure P] {b a : ℝ} {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G b a)
    (n : ℕ) :
    MSIntegrand P 𝓕 (fun u ω => G u ω * mrepBump b a n u) s t := by
  have hmid : MSIntegrand P 𝓕 (fun u ω => G u ω * mrepBump b a n u) b a :=
    Cochrane.Monetarism.TidyR7ItoProducts.MSIntegrand.mul_itoIntegrand hG
      (itoIntegrand_mrepBump b a n)
  have hleft : MSIntegrand P 𝓕 (fun u ω => G u ω * mrepBump b a n u) s b :=
    mrep_ms_congr mrep_ms_zero fun u hu ω => by
      rw [mrepBump_eq_zero n (Or.inl hu.2), mul_zero]
  have hright : MSIntegrand P 𝓕 (fun u ω => G u ω * mrepBump b a n u) a t :=
    mrep_ms_congr mrep_ms_zero fun u hu ω => by
      rw [mrepBump_eq_zero n (Or.inr hu.1), mul_zero]
  exact mrep_ms_glue (mrep_ms_glue hleft hmid) hright

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G·ψ_n` is jointly measurable. -/
theorem measurable_mrep_bump {G : ℝ → Ω → ℝ} (hGm : Measurable (Function.uncurry G)) (b a : ℝ)
    (n : ℕ) : Measurable (Function.uncurry fun u ω => G u ω * mrepBump b a n u) :=
  hGm.mul ((continuous_mrepBump b a n).measurable.comp measurable_fst)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for every `u`, `μ_{s,t}`-a.e. point has first
coordinate `≠ u`. -/
theorem mrep_ae_ne [IsFiniteMeasure P] (u : ℝ) : ∀ᵐ x ∂mrepMeasure P s t, x.1 ≠ u := by
  rw [ae_iff]
  have e : {x : ℝ × Ω | ¬x.1 ≠ u} = {u} ×ˢ Set.univ := by
    ext x; simp
  rw [e, mrepMeasure, Measure.prod_prod]
  simp only [Measure.restrict_apply (measurableSet_singleton u), mul_eq_zero]
  exact Or.inl (measure_mono_null Set.inter_subset_left Real.volume_singleton)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: dominated convergence for the bumps.** If
`1_{[b,a]}G²` is `μ_{s',t'}`-integrable and `G` jointly measurable, `G·ψ_n → 1_{(b, a]}G` in
`L²(μ_{s',t'})` (given the `G·ψ_n` are in `L²`). -/
theorem mrep_bump_L2Tendsto [IsFiniteMeasure P] {s' t' b a : ℝ} {G : ℝ → Ω → ℝ}
    (hGm : Measurable (Function.uncurry G))
    (hI : Integrable ((Set.Icc b a ×ˢ (Set.univ : Set Ω)).indicator
      fun x => Function.uncurry G x ^ 2) (mrepMeasure P s' t'))
    (hmem : ∀ n, MemLp (Function.uncurry fun u ω => G u ω * mrepBump b a n u) 2
      (mrepMeasure P s' t')) :
    L2Tendsto (mrepMeasure P s' t') (fun n => Function.uncurry fun u ω => G u ω * mrepBump b a n u)
      (Function.uncurry (mrepCut b a G)) := by
  set S : Set (ℝ × Ω) := Set.Icc b a ×ˢ Set.univ with hS
  have hSm : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  have hcm : Measurable (Function.uncurry (mrepCut b a G)) :=
    hGm.mul ((measurable_const.indicator measurableSet_Ioc).comp measurable_fst)
  have hbd : ∀ x : ℝ × Ω, Function.uncurry (mrepCut b a G) x ^ 2
      ≤ S.indicator (fun x => Function.uncurry G x ^ 2) x := by
    intro x
    by_cases hx : x.1 ∈ Set.Ioc b a
    · have hxS : x ∈ S := ⟨Set.Ioc_subset_Icc_self hx, trivial⟩
      simp [mrepCut, Function.uncurry, Set.indicator_of_mem hx, Set.indicator_of_mem hxS]
    · simp only [mrepCut, Function.uncurry, Set.indicator_of_notMem hx, mul_zero]
      rw [zero_pow two_ne_zero]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hcmem : MemLp (Function.uncurry (mrepCut b a G)) 2 (mrepMeasure P s' t') := by
    rw [memLp_two_iff_integrable_sq hcm.aestronglyMeasurable]
    refine hI.mono' (hcm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbd x
  refine ⟨hmem, hcmem, ?_⟩
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := mrepMeasure P s' t')
    (F := fun n x => (Function.uncurry (fun u ω => G u ω * mrepBump b a n u) x
      - Function.uncurry (mrepCut b a G) x) ^ 2)
    (f := fun _ => 0) (fun x => S.indicator (fun x => Function.uncurry G x ^ 2) x)
    (fun n => (((measurable_mrep_bump hGm b a n).sub hcm).pow_const 2).aestronglyMeasurable)
    hI (fun n => ae_of_all _ fun x => ?_) ?_
  · simpa using hlim
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := mrepBump_mem b a n x.1
    by_cases hx : x.1 ∈ Set.Icc b a
    · have hxS : x ∈ S := ⟨hx, trivial⟩
      rw [Set.indicator_of_mem hxS]
      have hi : (Set.Ioc b a).indicator (fun _ => (1 : ℝ)) x.1 ∈ Set.Icc (0 : ℝ) 1 := by
        by_cases h : x.1 ∈ Set.Ioc b a <;> simp [h]
      have hd : (mrepBump b a n x.1 - (Set.Ioc b a).indicator (fun _ => (1 : ℝ)) x.1) ^ 2
          ≤ 1 := by
        rw [sq_le_one_iff_abs_le_one, abs_le]; constructor <;> linarith [hi.1, hi.2]
      have e : (Function.uncurry (fun u ω => G u ω * mrepBump b a n u) x
          - Function.uncurry (mrepCut b a G) x) ^ 2
          = (mrepBump b a n x.1 - (Set.Ioc b a).indicator (fun _ => (1 : ℝ)) x.1) ^ 2
            * Function.uncurry G x ^ 2 := by
        simp only [Function.uncurry, mrepCut]; ring
      rw [e]
      exact mul_le_of_le_one_left (sq_nonneg _) hd
    · have hxS : x ∉ S := fun h => hx h.1
      have hx' : x.1 ∉ Set.Ioc b a := fun h => hx (Set.Ioc_subset_Icc_self h)
      have h0 : mrepBump b a n x.1 = 0 := by
        rcases not_and_or.1 hx with h | h
        · exact mrepBump_eq_zero n (Or.inl (le_of_lt (not_le.1 h)))
        · exact mrepBump_eq_zero n (Or.inr (le_of_lt (not_le.1 h)))
      simp [Function.uncurry, mrepCut, h0, Set.indicator_of_notMem hx',
        Set.indicator_of_notMem hxS]
  · filter_upwards [mrep_ae_ne (P := P) (s := s') (t := t') a] with x hxa
    by_cases hx : x.1 ∈ Set.Ioo b a
    · have hx' : x.1 ∈ Set.Ioc b a := Set.Ioo_subset_Ioc_self hx
      have h := (((tendsto_mrepBump hx).const_mul (G x.1 x.2)).sub
        (tendsto_const_nhds (x := G x.1 x.2 * 1))).pow 2
      simpa [Function.uncurry, mrepCut, Set.indicator_of_mem hx'] using h
    · have hx' : x.1 ∉ Set.Ioc b a := by
        intro h
        exact hx ⟨h.1, lt_of_le_of_ne h.2 hxa⟩
      have h0 : ∀ n, mrepBump b a n x.1 = 0 := fun n => by
        rcases not_and_or.1 hx with h | h
        · exact mrepBump_eq_zero n (Or.inl (not_lt.1 h))
        · exact mrepBump_eq_zero n (Or.inr (not_lt.1 h))
      simp [Function.uncurry, mrepCut, h0, Set.indicator_of_notMem hx']

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `μ_{s,t}` restricted to `[b, a] × Ω` is at most
`μ_{b,a}`. -/
theorem mrepMeasure_restrict_le [SFinite P] (b a : ℝ) :
    (mrepMeasure P s t).restrict (Set.Icc b a ×ˢ Set.univ) ≤ mrepMeasure P b a := by
  rw [mrepMeasure, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict measurableSet_Icc]
  refine Measure.prod_mono ?_ le_rfl
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
  exact Measure.restrict_mono Set.inter_subset_left le_rfl

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the switched-on integrand is in the
extended integrand class.** For `0 ≤ s ≤ b ≤ a ≤ t` and `G` mean-square continuous on
`[b, a]` and jointly measurable, `1_{(b, a]}G` is in `TidyR13MRepIntegral.MRepIntegrand` on
`[s, t]` and `∫_s^t 1_{(b, a]}G dW = ∫_b^a G dW` a.s. -/
theorem mrep_cut (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {b a : ℝ} (hsb : s ≤ b) (hba : b ≤ a)
    (hat : a ≤ t) {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G b a)
    (hGm : Measurable (Function.uncurry G)) :
    MRepIntegrand P 𝓕 (mrepCut b a G) s t ∧
      mrepInt P 𝓕 W (mrepCut b a G) s t =ᵐ[P] itoInt P 𝓕 W G b a := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hb : 0 ≤ b := hs.trans hsb
  have hGba := mrep_memLp_uncurry hG hGm
  have hsq : Integrable (fun x => Function.uncurry G x ^ 2) (mrepMeasure P b a) :=
    hGba.integrable_sq
  have hSm : MeasurableSet (Set.Icc b a ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hIst : Integrable ((Set.Icc b a ×ˢ (Set.univ : Set Ω)).indicator
      fun x => Function.uncurry G x ^ 2) (mrepMeasure P s t) := by
    rw [integrable_indicator_iff hSm]
    exact hsq.mono_measure (mrepMeasure_restrict_le b a)
  have hIba : Integrable ((Set.Icc b a ×ˢ (Set.univ : Set Ω)).indicator
      fun x => Function.uncurry G x ^ 2) (mrepMeasure P b a) := hsq.indicator hSm
  have hms := fun n => mrep_ms_bump (s := s) (t := t) hG n
  have hmsba := fun n => mrep_ms_bump (s := b) (t := a) hG n
  have hAst : MRepApprox P 𝓕 (mrepCut b a G) s t
      (fun n u ω => G u ω * mrepBump b a n u) :=
    ⟨hms, fun n => measurable_mrep_bump hGm b a n, mrep_bump_L2Tendsto hGm hIst
      fun n => mrep_memLp_uncurry (hms n) (measurable_mrep_bump hGm b a n)⟩
  have hae : Function.uncurry (mrepCut b a G) =ᵐ[mrepMeasure P b a] Function.uncurry G := by
    have h1 : ∀ᵐ x ∂mrepMeasure P b a, x.1 ∈ Set.Ioc b a := by
      rw [ae_iff]
      have e : {x : ℝ × Ω | ¬x.1 ∈ Set.Ioc b a} = (Set.Ioc b a)ᶜ ×ˢ Set.univ := by
        ext x; simp
      rw [e, mrepMeasure, Measure.prod_prod]
      simp [Measure.restrict_apply measurableSet_Ioc.compl]
    filter_upwards [h1] with x hx
    simp [Function.uncurry, mrepCut, Set.indicator_of_mem hx]
  have hAba : MRepApprox P 𝓕 G b a (fun n u ω => G u ω * mrepBump b a n u) :=
    ⟨hmsba, fun n => measurable_mrep_bump hGm b a n, (mrep_bump_L2Tendsto hGm hIba
      fun n => mrep_memLp_uncurry (hmsba n) (measurable_mrep_bump hGm b a n)).congr_ae hae⟩
  refine ⟨⟨_, hAst⟩, ?_⟩
  have h1 := (mrep_spec hB hW h𝓕 hs hAst).2
  have h2 : L2Tendsto P (fun n => itoInt P 𝓕 W (fun u ω => G u ω * mrepBump b a n u) s t)
      (itoInt P 𝓕 W G b a) := by
    refine ((mrep_spec hB hW h𝓕 hb hAba).2.congr_ae (mrep_agree hB hW h𝓕 hb hG hGm).2).congr_seq
      fun n => ?_
    have c1 := itoInt_add_itoInt_ms hB hW h𝓕 hs hsb (hba.trans hat) (hms n)
    have c2 := itoInt_add_itoInt_ms hB hW h𝓕 hb hba hat ((hms n).mono hsb le_rfl)
    have z1 : itoInt P 𝓕 W (fun u ω => G u ω * mrepBump b a n u) s b
        = itoInt P 𝓕 W (fun _ _ => (0 : ℝ)) s b :=
      itoInt_congr_Icc fun u hu ω => by rw [mrepBump_eq_zero n (Or.inl hu.2), mul_zero]
    have z2 : itoInt P 𝓕 W (fun u ω => G u ω * mrepBump b a n u) a t
        = itoInt P 𝓕 W (fun _ _ => (0 : ℝ)) a t :=
      itoInt_congr_Icc fun u hu ω => by rw [mrepBump_eq_zero n (Or.inr hu.1), mul_zero]
    filter_upwards [c1, c2, mrep_itoInt_zero (P := P) (𝓕 := 𝓕) (W := W) (s := s) (t := b),
      mrep_itoInt_zero (P := P) (𝓕 := 𝓕) (W := W) (s := a) (t := t)] with ω e1 e2 e3 e4
    rw [e1, e2, z1, z2, e3, e4]
    simp
  exact ae_eq_of_L2Tendsto h1 h2

end Cochrane.Monetarism.TidyR13MRepCutoff
