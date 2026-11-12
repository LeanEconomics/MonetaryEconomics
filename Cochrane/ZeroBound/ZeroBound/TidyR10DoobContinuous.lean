/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR10DoobDiscrete
import ZeroBound.TidyR7CondDominated
import Mathlib.Probability.Martingale.Basic

/-!
# Doob's `L²` maximal inequality in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (Track 3, chunk B3, item 1): for a square-integrable martingale `M` on `[s, T]` with
right-continuous paths,
`E[sup_{u ∈ [s,T]} M_u²] ≤ 4E[M_T²]`.

The supremum is the measurable path supremum `TidyR7CondDominated.pathSup s T M` (over the
countable set `TidyR7StieltjesVariation.denseSet s T`); for paths continuous on `[s, T]` it is
the supremum of `|M_u|` over all of `[s, T]` (`TidyR7CondDominated.abs_le_pathSup_of_continuousOn`
and `pathSup_le_of_forall_abs_le`).

## Route

* On the `L`-th dyadic grid of `[s, T]` the discrete inequality
  `TidyR10DoobDiscrete.doob_sq_discrete` gives `E[(max_{i ≤ 2^L}|Y_{t_i}|)²] ≤ 4E[Y_T²]`
  (`doob_sq_dyadic`), for an adapted square-integrable `Y` whose increments `Y_T − Y_u` are
  orthogonal to the past.
* The grids are nested, so the grid maxima increase in `L` (`dyadicMax_mono`); by monotone
  convergence (`MeasureTheory.lintegral_iSup`) their limit `g` has `E[g] ≤ 4E[Y_T²]`, so it is
  finite a.s.
* For `M` a modification of `Y` (`M_u = Y_u` a.s. for each `u`) with right-continuous paths,
  every `u ∈ [s, T]` is a right limit of grid points (`tendsto_dyadic_ceil`), so
  `M_u² ≤ g` for all `u` a.s., hence `pathSup s T M ² ≤ g` a.s.

The modification form is what the Itô integral needs: `TidyR7ItoIntegral.itoInt` is adapted but
has no path regularity, and `TidyR7ItoContinuity.exists_continuous_modification` gives a
modification with continuous paths that is not shown adapted.

## Main results

* `doob_sq_pathSup` (**Doob's `L²` inequality, modification form**):
  `pathSup s T M ²` is integrable and `E[pathSup s T M ²] ≤ 4E[M_T²]`.
* `doob_sq_martingale`: the same for a Mathlib `MeasureTheory.Martingale` with square-integrable
  values and a.s. right-continuous paths; `memLp_pathSup_martingale`.
-/

namespace Cochrane.ZeroBound.TidyR10DoobContinuous

open MeasureTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7StieltjesVariation
  Cochrane.ZeroBound.TidyR7CondDominated Cochrane.ZeroBound.TidyR10DoobDiscrete
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {s T : ℝ}

/-! ## Path suprema -/

/-- Cochrane (2023), A1 §1.6, p. 567: `pathSup s T X ω ≤ c` whenever `|X_u(ω)| ≤ c` on
`[s, T]`, `s ≤ T`. With `TidyR7CondDominated.abs_le_pathSup_of_continuousOn`: for a path
continuous on `[s, T]`, the path supremum is the supremum of `|X_u|` over `[s, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.pathSup_le_of_forall_abs_le). -/
theorem pathSup_le_of_forall_abs_le {X : ℝ → Ω → ℝ} {ω : Ω} (hsT : s ≤ T) {c : ℝ}
    (h : ∀ u ∈ Set.Icc s T, |X u ω| ≤ c) : pathSup s T X ω ≤ c := by
  have : Nonempty (denseSet s T) := ⟨⟨T, ⟨hsT, le_rfl⟩, Or.inl rfl⟩⟩
  exact ciSup_le fun q => h q q.2.1

/-! ## Dyadic grids -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): the process `Y` read along the `L`-th dyadic grid
of `[s, T]`, `i ↦ Y_{t_{min(i, 2^L)}}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.gridSeq). -/
noncomputable def gridSeq (hsT : s < T) (Y : ℝ → Ω → ℝ) (L : ℕ) (i : ℕ) : Ω → ℝ :=
  Y ((dyadic hsT L).t (min i (2 ^ L)))

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): the maximum of `|Y|` over the `L`-th dyadic grid
of `[s, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.dyadicMax). -/
noncomputable def dyadicMax (hsT : s < T) (Y : ℝ → Ω → ℝ) (L : ℕ) (ω : Ω) : ℝ :=
  runMax (gridSeq hsT Y L) (2 ^ L) ω

/-- Cochrane (2023), A1 §1.6, p. 567: the grid points lie in `[s, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.dyadic_t_min_mem). -/
theorem dyadic_t_min_mem (hsT : s < T) (L i : ℕ) :
    (dyadic hsT L).t (min i (2 ^ L)) ∈ Set.Icc s T :=
  t_mem (dyadic hsT L) (min_le_right i (2 ^ L))

/-- Cochrane (2023), A1 §1.6, p. 567: the dyadic grids are nested, `t^L_i = t^{L+1}_{2i}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.dyadic_t_two_mul). -/
theorem dyadic_t_two_mul (hsT : s < T) (L i : ℕ) :
    (dyadic hsT (L + 1)).t (2 * i) = (dyadic hsT L).t i := by
  simp only [dyadic]
  push_cast
  rw [pow_succ]
  field_simp

/-- Cochrane (2023), A1 §1.6, p. 567: the grid maxima increase with the level.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.dyadicMax_mono). -/
theorem dyadicMax_mono (hsT : s < T) (Y : ℝ → Ω → ℝ) (ω : Ω) :
    Monotone fun L => dyadicMax hsT Y L ω := by
  refine monotone_nat_of_le_succ fun L => ?_
  change runMax _ _ ω ≤ runMax _ _ ω
  refine Finset.sup'_le Finset.nonempty_range_add_one _ fun k hk => ?_
  have hk' : k ≤ 2 ^ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have h2 : 2 * k ≤ 2 ^ (L + 1) := by rw [pow_succ]; omega
  have e : gridSeq hsT Y L k ω = gridSeq hsT Y (L + 1) (2 * k) ω := by
    simp only [gridSeq, min_eq_left hk', min_eq_left h2, dyadic_t_two_mul]
  change |gridSeq hsT Y L k ω| ≤ dyadicMax hsT Y (L + 1) ω
  rw [e]
  exact le_runMax _ h2 ω

/-- Cochrane (2023), A1 §1.6, p. 567: for `u ∈ [s, T]`, the grid point
`t^L_{⌈(u − s)2^L/(T − s)⌉}` lies in `[u, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.dyadic_ceil_mem). -/
theorem dyadic_ceil_mem (hsT : s < T) {u : ℝ} (hu : u ∈ Set.Icc s T) (L : ℕ) :
    ⌈(u - s) * 2 ^ L / (T - s)⌉₊ ≤ 2 ^ L ∧
      (dyadic hsT L).t ⌈(u - s) * 2 ^ L / (T - s)⌉₊ ∈ Set.Icc u T := by
  have hTs : 0 < T - s := sub_pos.2 hsT
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  set y := (u - s) * 2 ^ L / (T - s) with hy
  have hy0 : 0 ≤ y := div_nonneg (mul_nonneg (sub_nonneg.2 hu.1) h2.le) hTs.le
  have hyle : y ≤ 2 ^ L := by
    rw [hy, div_le_iff₀ hTs]
    nlinarith [hu.2]
  have hk : ⌈y⌉₊ ≤ 2 ^ L := Nat.ceil_le.2 (by exact_mod_cast hyle)
  refine ⟨hk, ?_, (t_mem (dyadic hsT L) hk).2⟩
  have h1 : y ≤ ⌈y⌉₊ := Nat.le_ceil y
  change u ≤ s + (T - s) * (⌈y⌉₊ : ℝ) / 2 ^ L
  have e : u = s + (T - s) * y / 2 ^ L := by
    rw [hy]
    field_simp
    ring
  rw [e]
  have : (T - s) * y ≤ (T - s) * ⌈y⌉₊ := mul_le_mul_of_nonneg_left h1 hTs.le
  have := div_le_div_of_nonneg_right this h2.le
  linarith

/-- Cochrane (2023), A1 §1.6, p. 567: every `u ∈ [s, T]` is the limit from the right, within
`[u, T]`, of the grid points `t^L_{⌈(u − s)2^L/(T − s)⌉}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.tendsto_dyadic_ceil). -/
theorem tendsto_dyadic_ceil (hsT : s < T) {u : ℝ} (hu : u ∈ Set.Icc s T) :
    Tendsto (fun L => (dyadic hsT L).t ⌈(u - s) * 2 ^ L / (T - s)⌉₊) atTop
      (𝓝[Set.Icc u T] u) := by
  have hTs : 0 < T - s := sub_pos.2 hsT
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun L => (dyadic_ceil_mem hsT hu L).2⟩
  have hb : ∀ L : ℕ, |(dyadic hsT L).t ⌈(u - s) * 2 ^ L / (T - s)⌉₊ - u| ≤ (T - s) / 2 ^ L := by
    intro L
    have h2 : (0 : ℝ) < 2 ^ L := by positivity
    set y := (u - s) * 2 ^ L / (T - s) with hy
    have hy0 : 0 ≤ y := div_nonneg (mul_nonneg (sub_nonneg.2 hu.1) h2.le) hTs.le
    have hc : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
    have h1 : y ≤ ⌈y⌉₊ := Nat.le_ceil y
    have e : (dyadic hsT L).t ⌈y⌉₊ - u = (T - s) / 2 ^ L * ((⌈y⌉₊ : ℝ) - y) := by
      change s + (T - s) * (⌈y⌉₊ : ℝ) / 2 ^ L - u = _
      rw [hy]
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity), abs_of_nonneg (by linarith)]
    have : (T - s) / 2 ^ L * ((⌈y⌉₊ : ℝ) - y) ≤ (T - s) / 2 ^ L * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have h0 : Tendsto (fun L : ℕ => (T - s) / 2 ^ L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun L => ?_)
    h0)
  rw [Real.norm_eq_abs]
  exact hb L

/-! ## The inequality -/

variable {Y : ℝ → Ω → ℝ}

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Doob's `L²` inequality on a dyadic grid.** For `Y`
adapted and square integrable on `[s, T]`, with `E[G(Y_T − Y_u)] = 0` for every `u ∈ [s, T]` and
every square-integrable `𝓕_u`-strongly measurable `G`,
`E[(max_{i ≤ 2^L}|Y_{t_i}|)²] ≤ 4E[Y_T²]` on the `L`-th dyadic grid.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.doob_sq_dyadic). -/
theorem doob_sq_dyadic (hsT : s < T) (hY : ∀ u ∈ Set.Icc s T, StronglyMeasurable[𝓕 u] (Y u))
    (hY2 : ∀ u ∈ Set.Icc s T, MemLp (Y u) 2 P)
    (horth : ∀ u ∈ Set.Icc s T, ∀ G : Ω → ℝ, StronglyMeasurable[𝓕 u] G → MemLp G 2 P →
      ∫ ω, G ω * (Y T ω - Y u ω) ∂P = 0) (L : ℕ) :
    ∫ ω, dyadicMax hsT Y L ω ^ 2 ∂P ≤ 4 * ∫ ω, Y T ω ^ 2 ∂P := by
  have hm : Monotone fun i => 𝓕 ((dyadic hsT L).t (min i (2 ^ L))) := fun i j hij =>
    𝓕.mono ((dyadic hsT L).strictMono.monotone (min_le_min_right _ hij))
  have hlast : gridSeq hsT Y L (2 ^ L) = Y T := by
    simp only [gridSeq, min_self]
    exact congrArg Y (dyadic hsT L).last
  have h := doob_sq_discrete (P := P) (Y := gridSeq hsT Y L) hm
    (fun i => 𝓕.le _) (fun i => hY _ (dyadic_t_min_mem hsT L i))
    (fun i => hY2 _ (dyadic_t_min_mem hsT L i)) (2 ^ L) (fun l _ G hG hG2 => by
      rw [hlast]
      exact horth _ (dyadic_t_min_mem hsT L l) G hG hG2)
  rw [hlast] at h
  exact h

/-- Cochrane (2023), A1 §1.6, p. 567: the grid maxima are measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.measurable_dyadicMax). -/
theorem measurable_dyadicMax (hsT : s < T)
    (hY : ∀ u ∈ Set.Icc s T, StronglyMeasurable[𝓕 u] (Y u)) (L : ℕ) :
    Measurable (dyadicMax hsT Y L) := by
  have hm : Monotone fun i => 𝓕 ((dyadic hsT L).t (min i (2 ^ L))) := fun i j hij =>
    𝓕.mono ((dyadic hsT L).strictMono.monotone (min_le_min_right _ hij))
  exact ((stronglyMeasurable_runMax hm (fun i => hY _ (dyadic_t_min_mem hsT L i)) (2 ^ L)).mono
    (𝓕.le _)).measurable

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 1): Doob's `L²` maximal inequality
in continuous time, modification form.** Let `s < T`, `Y` adapted and square integrable on
`[s, T]` with `E[G(Y_T − Y_u)] = 0` for every `u ∈ [s, T]` and every square-integrable
`𝓕_u`-strongly measurable `G` (a square-integrable martingale on `[s, T]`), and let `M` be a
modification of `Y` on `[s, T]` (`M_u = Y_u` a.s. for each `u`) whose paths are a.s.
right-continuous on `[s, T]`. Then `(sup_{[s,T]}|M|)²` is integrable and
`E[(sup_{[s,T]}|M|)²] ≤ 4E[M_T²]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.doob_sq_pathSup). -/
theorem doob_sq_pathSup (hsT : s < T) (hY : ∀ u ∈ Set.Icc s T, StronglyMeasurable[𝓕 u] (Y u))
    (hY2 : ∀ u ∈ Set.Icc s T, MemLp (Y u) 2 P)
    (horth : ∀ u ∈ Set.Icc s T, ∀ G : Ω → ℝ, StronglyMeasurable[𝓕 u] G → MemLp G 2 P →
      ∫ ω, G ω * (Y T ω - Y u ω) ∂P = 0)
    {M : ℝ → Ω → ℝ} (hMY : ∀ u ∈ Set.Icc s T, M u =ᵐ[P] Y u)
    (hMr : ∀ᵐ ω ∂P, ∀ x ∈ Set.Icc s T, ContinuousWithinAt (fun u => M u ω) (Set.Icc x T) x) :
    Integrable (fun ω => pathSup s T M ω ^ 2) P ∧
      ∫ ω, pathSup s T M ω ^ 2 ∂P ≤ 4 * ∫ ω, M T ω ^ 2 ∂P := by
  have hTmem : T ∈ Set.Icc s T := ⟨hsT.le, le_rfl⟩
  set a := ∫ ω, Y T ω ^ 2 ∂P with ha
  have ha0 : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  set f : ℕ → Ω → ℝ≥0∞ := fun L ω => ENNReal.ofReal (dyadicMax hsT Y L ω ^ 2) with hf
  have hfm : ∀ L, Measurable (f L) := fun L =>
    ENNReal.measurable_ofReal.comp ((measurable_dyadicMax hsT hY L).pow_const 2)
  have hfmono : Monotone f := fun L L' hLL' ω =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (runMax_nonneg _ _ _)
      (dyadicMax_mono hsT Y ω hLL') 2)
  set g : Ω → ℝ≥0∞ := fun ω => ⨆ L, f L ω with hg
  have hgm : Measurable g := Measurable.iSup hfm
  have hint : ∀ L, Integrable (fun ω => dyadicMax hsT Y L ω ^ 2) P := by
    intro L
    have hm : Monotone fun i => 𝓕 ((dyadic hsT L).t (min i (2 ^ L))) := fun i j hij =>
      𝓕.mono ((dyadic hsT L).strictMono.monotone (min_le_min_right _ hij))
    exact (memLp_runMax (fun i => 𝓕.le _) hm (fun i => hY _ (dyadic_t_min_mem hsT L i))
      (fun i => hY2 _ (dyadic_t_min_mem hsT L i)) (2 ^ L)).integrable_sq
  have hgle : ∫⁻ ω, g ω ∂P ≤ ENNReal.ofReal (4 * a) := by
    rw [hg, lintegral_iSup hfm hfmono]
    refine iSup_le fun L => ?_
    rw [hf, ← ofReal_integral_eq_lintegral_ofReal (hint L) (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (doob_sq_dyadic hsT hY hY2 horth L)
  have hgfin : ∫⁻ ω, g ω ∂P ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgle
  have hglt : ∀ᵐ ω ∂P, g ω < ∞ := ae_lt_top hgm hgfin
  -- the modification agrees with `Y` on every grid point and on `denseSet s T`
  have hgrid : ∀ᵐ ω ∂P, ∀ L i, M ((dyadic hsT L).t (min i (2 ^ L))) ω
      = Y ((dyadic hsT L).t (min i (2 ^ L))) ω := by
    rw [ae_all_iff]
    intro L
    rw [ae_all_iff]
    intro i
    exact hMY _ (dyadic_t_min_mem hsT L i)
  have hds : pathSup s T M =ᵐ[P] pathSup s T Y := by
    have := (countable_denseSet s T).to_subtype
    have h : ∀ᵐ ω ∂P, ∀ q : denseSet s T, M q ω = Y q ω := by
      rw [ae_all_iff]
      exact fun q => hMY q q.2.1
    filter_upwards [h] with ω hω
    simp only [pathSup, hω]
  have hYm : ∀ u ∈ Set.Icc s T, Measurable (Y u) := fun u hu =>
    ((hY u hu).mono (𝓕.le u)).measurable
  have hsm : AEStronglyMeasurable (fun ω => pathSup s T M ω ^ 2) P :=
    (((measurable_pathSup hYm).pow_const 2).aestronglyMeasurable).congr
      (hds.mono fun ω hω => by simp only [hω])
  -- the pointwise bound
  have hbound : ∀ᵐ ω ∂P, pathSup s T M ω ^ 2 ≤ (g ω).toReal := by
    filter_upwards [hglt, hgrid, hMr] with ω hgω hgridω hMrω
    have hL : ∀ L, dyadicMax hsT Y L ω ^ 2 ≤ (g ω).toReal := fun L =>
      (ENNReal.ofReal_le_iff_le_toReal hgω.ne).1 (le_iSup (fun L => f L ω) L)
    have hMu : ∀ u ∈ Set.Icc s T, M u ω ^ 2 ≤ (g ω).toReal := by
      intro u hu
      have ht := ((hMrω u hu).tendsto.comp (tendsto_dyadic_ceil hsT hu)).pow 2
      refine le_of_tendsto' ht fun L => ?_
      obtain ⟨hk, -⟩ := dyadic_ceil_mem hsT hu L
      set k := ⌈(u - s) * 2 ^ L / (T - s)⌉₊
      have e : M ((dyadic hsT L).t k) ω = gridSeq hsT Y L k ω := by
        have := hgridω L k
        rw [min_eq_left hk] at this
        rw [this, gridSeq, min_eq_left hk]
      change M ((dyadic hsT L).t k) ω ^ 2 ≤ _
      rw [e, ← sq_abs]
      exact (pow_le_pow_left₀ (abs_nonneg _) (le_runMax _ hk ω) 2).trans (hL L)
    have hs : pathSup s T M ω ≤ Real.sqrt (g ω).toReal :=
      pathSup_le_of_forall_abs_le hsT.le fun u hu => Real.abs_le_sqrt (hMu u hu)
    calc pathSup s T M ω ^ 2 ≤ Real.sqrt (g ω).toReal ^ 2 :=
          pow_le_pow_left₀ (pathSup_nonneg _ _ _ _) hs 2
      _ = (g ω).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hgi : Integrable (fun ω => (g ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hgm.aemeasurable hgfin
  have hMT : ∫ ω, M T ω ^ 2 ∂P = a := integral_congr_ae ((hMY T hTmem).mono fun ω hω => by
    simp only [hω])
  refine ⟨hgi.mono' hsm (hbound.mono fun ω hω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  · rw [hMT]
    calc ∫ ω, pathSup s T M ω ^ 2 ∂P ≤ ∫ ω, (g ω).toReal ∂P := integral_mono_ae
          (hgi.mono' hsm (hbound.mono fun ω hω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hω)) hgi hbound
      _ = (∫⁻ ω, g ω ∂P).toReal := integral_toReal hgm.aemeasurable hglt
      _ ≤ 4 * a := ENNReal.toReal_le_of_le_ofReal (by positivity) hgle

variable [IsFiniteMeasure P]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 1): Doob's `L²` inequality for a
right-continuous square-integrable martingale.** If `M` is a martingale for `𝓕` (Mathlib
`MeasureTheory.Martingale`), `M_u` is square integrable for `u ∈ [s, T]`, `s < T`, and the paths
are a.s. right-continuous on `[s, T]`, then `E[(sup_{[s,T]}|M|)²] ≤ 4E[M_T²]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.doob_sq_martingale). -/
theorem doob_sq_martingale (hsT : s < T) {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hM2 : ∀ u ∈ Set.Icc s T, MemLp (M u) 2 P)
    (hMr : ∀ᵐ ω ∂P, ∀ x ∈ Set.Icc s T, ContinuousWithinAt (fun u => M u ω) (Set.Icc x T) x) :
    Integrable (fun ω => pathSup s T M ω ^ 2) P ∧
      ∫ ω, pathSup s T M ω ^ 2 ∂P ≤ 4 * ∫ ω, M T ω ^ 2 ∂P :=
  doob_sq_pathSup hsT (fun u _ => hM.1 u) hM2
    (fun u hu _ hG hG2 => integral_mul_sub_eq_zero_of_condExp (𝓕.le u) (hM.2 u T hu.2)
      (hM2 T ⟨hsT.le, le_rfl⟩) (hM2 u hu) hG hG2)
    (fun _ _ => ae_of_all _ fun _ => rfl) hMr

/-- Cochrane (2023), A1 §1.6, pp. 567–568: under the hypotheses of `doob_sq_martingale`, the
path supremum `sup_{[s,T]}|M|` is square integrable (in particular integrable).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobContinuous.memLp_pathSup_martingale). -/
theorem memLp_pathSup_martingale (hsT : s < T) {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hM2 : ∀ u ∈ Set.Icc s T, MemLp (M u) 2 P)
    (hMr : ∀ᵐ ω ∂P, ∀ x ∈ Set.Icc s T, ContinuousWithinAt (fun u => M u ω) (Set.Icc x T) x) :
    MemLp (pathSup s T M) 2 P := by
  have hm : Measurable (pathSup s T M) := measurable_pathSup fun u _ =>
    ((hM.1 u).mono (𝓕.le u)).measurable
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
    (doob_sq_martingale hsT hM hM2 hMr).1

end Cochrane.ZeroBound.TidyR10DoobContinuous
