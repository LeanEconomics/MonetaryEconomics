/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR9ItoWeightedBracket
import ZeroBound.TidyR9ItoPathSums
import ZeroBound.TidyR7ItoBondStep

/-!
# Itô's formula `df(t, X) = f_t dt + f_x dX + ½f_xx d[X]`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Track 3, chunk B1. The book's (1.32)–(1.34)
work with the nominal discount factor `Λ/P`; a positive diffusive `Λ/P` (e.g. `2 + sin W`, or
`1/X`, or `exp` of an Itô process) is a function of an Itô process, and its drift and diffusion
come from Itô's formula. The product rule (`TidyR7ItoProductRule.product_rule`) is the case
`f(x, y) = xy`; this module proves the general one-dimensional formula, with time dependence.

## Setting

`X` an Itô process on `[s, t]`, `0 ≤ s < t` (`TidyR7ItoProcess.ItoProcess`: drift `a`, diffusion
`H` bounded, adapted, a.s. continuous), **with a.s. continuous paths on `[s, t]`** (the toolkit's
Itô process is specified at fixed times only, so path continuity is a hypothesis; Brownian
motion `bmPath` has it for every path). `f(u, x)` has partial derivatives `f_t = ∂_u f`,
`f_x = ∂_x f`, `f_xx = ∂_x f_x` everywhere, `f, f_t, f_x, f_xx` jointly continuous, `f_t` and `f_xx`
bounded on `[s, t] × ℝ`, and `u ↦ f_x(u, X_u)` mean-square continuous (automatic if `f_x` is
bounded, `msIntegrand_comp_of_bound`, or if `f` does not depend on time and `f''` is bounded,
`msIntegrand_comp_lipschitz`; so `f(x) = x²` is covered). No global uniform continuity of `f''`
is needed: the remainder is controlled by uniform continuity on the compact range of each path.

## Main results

* `ito_formula_time` (**Itô's formula with time dependence**): a.s.
  `f(t, X_t) − f(s, X_s) = ∫_s^t f_t(u, X_u) du + ∫_s^t f_x(u, X) dX + ½∫_s^t f_xx(u, X_u)H_u² du`,
  `∫ f_x dX = ∫ f_x a du + ∫ f_x H dW` (mean-square time integral `TidyR7ItoProducts.dtInt` plus
  Itô integral). Proof: the exact partition identity
  (`TidyR9ItoPathSums.itoTaylor_partition_identity`) along dyadic partitions, and four limits —
  the time sum (pathwise, then dominated convergence), `Σ f_x(X_i)ΔX_i` (`L²`,
  `TidyR7ItoCovariation.L2Tendsto_sumRS`), the weighted bracket `Σ f_xx(X_i)(ΔX_i)²`
  (`L¹`, `TidyR9ItoWeightedBracket.tendsto_integral_abs_wSumCross`), and the remainder
  (`L¹`: `|Σ R_i| = ρ_k Σ(ΔX_i)²` with `0 ≤ ρ_k ≤ 2L`, `ρ_k → 0` a.s. by
  `TidyR9ItoPathSums.eventually_abs_remSum_le`, and `Σ(ΔX_i)² → ∫H²` in `L¹`).
* `ito_formula` (**Itô's formula**, `f ∈ C²` with `f''` bounded and continuous): a.s.
  `f(X_t) − f(X_s) = ∫ f'(X)a du + ∫ f'(X)H dW + ½∫ f''(X)H² du`; `ito_formula_pathwise` (the
  time integrals pathwise).
* `itoProcess_comp` (**`f(X)` is again an Itô process** when `f'`, `f''` are bounded): drift
  `f'(X)a + ½f''(X)H²`, diffusion `f'(X)H` (the time-dependent and range-restricted versions,
  `1/X` and `exp X` are in `TidyR9ItoFormulaVariants`).
* `condExp_ito_formula` (**conditional form**):
  `E_s[f(X_t) − f(X_s)] = E_s[∫_s^t (f'(X)a + ½f''(X)H²) du]` a.s.
* `ito_formula_sq_recovers` (`f(x) = x²` gives back `TidyR7ItoProductRule.ito_formula_sq`).
* Non-vacuity on the constructed motion: `ito_formula_sin_bmPath`
  (`sin W_1 = ∫_0^1 cos W dW − ½∫_0^1 sin W du` a.s.), `itoProcess_sin_bm`.
-/

namespace Cochrane.ZeroBound.TidyR9ItoFormula

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoSums Cochrane.ZeroBound.TidyR7ItoIntegral
  Cochrane.ZeroBound.TidyR7ItoUnbounded Cochrane.ZeroBound.TidyR7ItoProducts
  Cochrane.ZeroBound.TidyR7ItoProcess Cochrane.ZeroBound.TidyR7ItoCovariation
  Cochrane.ZeroBound.TidyR7ItoProductRule Cochrane.ZeroBound.TidyR7ItoBondStep
  Cochrane.ZeroBound.TidyR9ItoTaylor Cochrane.ZeroBound.TidyR9ItoPathSums
  Cochrane.ZeroBound.TidyR9ItoWeightedBracket Cochrane.ZeroBound.TidyR7BrownianSchauder
  Cochrane.ZeroBound.TidyR7BrownianExist
open Cochrane.ZeroBound.TidyR7ProductStep (sumRS sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-! ## Admissibility of `g(u, X_u)` -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `g` jointly continuous and `X` adapted,
`g(u, X_u)` is `𝓕_u`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.stronglyMeasurable_comp). -/
theorem stronglyMeasurable_comp {X : ℝ → Ω → ℝ} {g : ℝ → ℝ → ℝ}
    (cg : Continuous (Function.uncurry g)) {u : ℝ} (hX : StronglyMeasurable[𝓕 u] (X u)) :
    StronglyMeasurable[𝓕 u] (fun ω => g u (X u ω)) :=
  (cg.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable hX

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`g(u, X_u)` is an admissible integrand** if `g` is
jointly continuous and bounded by `L` on `[s, t] × ℝ`, and `X` is adapted with a.s. continuous
paths on `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.itoIntegrand_comp). -/
theorem itoIntegrand_comp {X : ℝ → Ω → ℝ} (hXa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (X u))
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t)) {g : ℝ → ℝ → ℝ}
    (cg : Continuous (Function.uncurry g)) {L : ℝ} (hgb : ∀ u ∈ Set.Icc s t, ∀ x, |g u x| ≤ L) :
    ItoIntegrand P 𝓕 (fun u ω => g u (X u ω)) s t L where
  adapted u hu := stronglyMeasurable_comp cg (hXa u hu)
  bound u hu ω := hgb u hu _
  cont := by
    filter_upwards [hXc] with ω hω
    exact cg.comp_continuousOn (continuousOn_id.prodMk hω)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a Lipschitz function of a square-integrable
variable is square integrable (`|φ(Z)| ≤ |φ 0| + L|Z|`).
Generalises Mathlib `LipschitzWith.comp_memLp` (no `φ 0 = 0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.memLp_comp_lipschitz). -/
theorem memLp_comp_lipschitz [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|) : MemLp (fun ω => φ (Z ω)) 2 P := by
  have h1 : MemLp (fun _ : Ω => |φ 0|) 2 P := memLp_const _
  have h2 : MemLp (fun ω => L * ‖Z ω‖) 2 P := hZ.norm.const_mul L
  have hg : MemLp (fun ω => |φ 0| + L * ‖Z ω‖) 2 P := h1.add h2
  refine hg.of_le (hφc.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  have h := hφ (Z ω) 0
  rw [sub_zero] at h
  have h0 : 0 ≤ |φ 0| + L * |Z ω| := add_nonneg (abs_nonneg _) (mul_nonneg hL (abs_nonneg _))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
  have h2 := abs_sub_abs_le_abs_sub (φ (Z ω)) (φ 0)
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **a Lipschitz function of a mean-square continuous
integrand is one**: if `|φ x − φ y| ≤ L|x − y|`, `L ≥ 0`, and `G` is mean-square continuous, so is
`φ(G)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.msIntegrand_comp_lipschitz). -/
theorem msIntegrand_comp_lipschitz [IsFiniteMeasure P] {G : ℝ → Ω → ℝ}
    (hG : MSIntegrand P 𝓕 G s t) {φ : ℝ → ℝ} (hφc : Continuous φ) {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|) :
    MSIntegrand P 𝓕 (fun u ω => φ (G u ω)) s t where
  adapted u hu := hφc.comp_stronglyMeasurable (hG.adapted u hu)
  memLp u hu := memLp_comp_lipschitz (hG.memLp u hu) hφc hL hφ
  cont ε hε := by
    obtain ⟨δ, hδ, hδG⟩ := hG.cont (ε / (L ^ 2 + 1)) (by positivity)
    refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
    have hm : ∀ r ∈ Set.Icc s t, MemLp (fun ω => φ (G r ω)) 2 P := fun r hr =>
      memLp_comp_lipschitz (hG.memLp r hr) hφc hL hφ
    have h1 : ∫ ω, (φ (G u ω) - φ (G v ω)) ^ 2 ∂P ≤ ∫ ω, L ^ 2 * (G u ω - G v ω) ^ 2 ∂P := by
      refine integral_mono ((hm u hu).sub (hm v hv)).integrable_sq
        (((hG.memLp u hu).sub (hG.memLp v hv)).integrable_sq.const_mul _) fun ω => ?_
      have h := hφ (G u ω) (G v ω)
      have h' : (φ (G u ω) - φ (G v ω)) ^ 2 ≤ (L * |G u ω - G v ω|) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      calc (φ (G u ω) - φ (G v ω)) ^ 2 ≤ (L * |G u ω - G v ω|) ^ 2 := h'
        _ = L ^ 2 * (G u ω - G v ω) ^ 2 := by rw [mul_pow, sq_abs]
    rw [integral_const_mul] at h1
    have h2 := hδG u hu v hv huv
    have h3 : L ^ 2 * (ε / (L ^ 2 + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    calc ∫ ω, (φ (G u ω) - φ (G v ω)) ^ 2 ∂P ≤ L ^ 2 * ∫ ω, (G u ω - G v ω) ^ 2 ∂P := h1
      _ ≤ L ^ 2 * (ε / (L ^ 2 + 1)) := mul_le_mul_of_nonneg_left h2 (sq_nonneg L)
      _ ≤ ε := h3

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a bounded jointly continuous `g(u, X_u)` along an
adapted process with a.s. continuous paths is mean-square continuous
(`itoIntegrand_comp`, `TidyR7ItoUnbounded.ItoIntegrand.toMS`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.msIntegrand_comp_of_bound). -/
theorem msIntegrand_comp_of_bound [IsFiniteMeasure P] {X : ℝ → Ω → ℝ}
    (hXa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (X u))
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t)) {g : ℝ → ℝ → ℝ}
    (cg : Continuous (Function.uncurry g)) {L : ℝ} (hgb : ∀ u ∈ Set.Icc s t, ∀ x, |g u x| ≤ L) :
    MSIntegrand P 𝓕 (fun u ω => g u (X u ω)) s t :=
  ItoIntegrand.toMS (itoIntegrand_comp (P := P) hXa hXc cg hgb)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **an Itô process on `[s, t]` is one on `[s, u]`**,
`s ≤ u ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.itoProcess_restrict). -/
theorem itoProcess_restrict {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) {u : ℝ} (hu : u ≤ t) :
    ItoProcess P 𝓕 W X a H s u Ca CH where
  adapted r hr := hX.adapted r ⟨hr.1, hr.2.trans hu⟩
  init := hX.init
  drift := hX.drift.mono le_rfl hu
  diff := hX.diff.mono le_rfl hu
  eq r hr := hX.eq r ⟨hr.1, hr.2.trans hu⟩

/-! ## Itô's formula -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula with time dependence, for the
positive diffusive `Λ/P` of (1.32)–(1.34)).** For an Itô process `X` (drift `a`, diffusion `H`)
with a.s. continuous paths on `[s, t]`, `0 ≤ s < t`, and `f(u, x)` with partial derivatives
`f_t, f_x, f_xx` (jointly continuous, `f_t` and `f_xx` bounded on `[s, t] × ℝ`, `f_x(u, X_u)`
mean-square continuous), almost surely
`f(t, X_t) − f(s, X_s) = ∫_s^t f_t(u, X_u) du + (∫_s^t f_x(u, X_u)a_u du + ∫_s^t f_x(u, X)H dW)
  + ½∫_s^t f_xx(u, X_u)H_u² du`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.ito_formula_time). -/
theorem ito_formula_time (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f ft fx fxx : ℝ → ℝ → ℝ} (hft : ∀ u x, HasDerivAt (fun r => f r x) (ft u x) u)
    (hfx : ∀ u x, HasDerivAt (f u) (fx u x) x) (hfxx : ∀ u x, HasDerivAt (fx u) (fxx u x) x)
    (cf : Continuous (Function.uncurry f)) (cft : Continuous (Function.uncurry ft))
    (cfxx : Continuous (Function.uncurry fxx)) {Lt L2 : ℝ}
    (hftb : ∀ u ∈ Set.Icc s t, ∀ x, |ft u x| ≤ Lt)
    (hfxxb : ∀ u ∈ Set.Icc s t, ∀ x, |fxx u x| ≤ L2)
    (hG1 : MSIntegrand P 𝓕 (fun u ω => fx u (X u ω)) s t) :
    (fun ω => f t (X t ω) - f s (X s ω)) =ᵐ[P] fun ω =>
      (∫ u in s..t, ft u (X u ω))
      + (dtInt P 𝓕 (fun u ω => fx u (X u ω) * a u ω) s t ω
        + itoInt P 𝓕 W (fun u ω => fx u (X u ω) * H u ω) s t ω)
      + (∫ u in s..t, fxx u (X u ω) * (H u ω * H u ω)) / 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set ps : ℕ → Partition s t := fun k => dyadic hst k with hps_def
  have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := tendsto_mesh_dyadic hst
  have hL2 : 0 ≤ L2 := (abs_nonneg _).trans (hfxxb s ⟨le_rfl, hst.le⟩ 0)
  have hXm : ∀ v ∈ Set.Icc s t, Measurable (X v) := fun v hv =>
    ((hX.adapted v hv).mono (𝓕.le v)).measurable
  have hcm : ∀ g : ℝ → ℝ → ℝ, Continuous (Function.uncurry g) → ∀ r v, v ∈ Set.Icc s t →
      Measurable (fun ω => g r (X v ω)) := fun g cg r v hv =>
    (cg.comp (continuous_const.prodMk continuous_id)).measurable.comp (hXm v hv)
  set G1 : ℝ → Ω → ℝ := fun u ω => fx u (X u ω) with hG1_def
  set G2 : ℝ → Ω → ℝ := fun u ω => fxx u (X u ω) with hG2_def
  have hG2 : ItoIntegrand P 𝓕 G2 s t L2 := itoIntegrand_comp hX.adapted hXc cfxx hfxxb
  have hGt : ItoIntegrand P 𝓕 (fun u ω => ft u (X u ω)) s t Lt :=
    itoIntegrand_comp hX.adapted hXc cft hftb
  have hHH : ItoIntegrand P 𝓕 (fun u ω => H u ω * H u ω) s t (CH * CH) :=
    itoIntegrand_mul hX.diff hX.diff
  set LT : Ω → ℝ := fun ω => ∫ u in s..t, ft u (X u ω) with hLT
  set L1 : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => G1 u ω * a u ω) s t ω
    + itoInt P 𝓕 W (fun u ω => G1 u ω * H u ω) s t ω with hL1
  set L3 : Ω → ℝ := fun ω => ∫ u in s..t, G2 u ω * (H u ω * H u ω) with hL3
  set Q : Ω → ℝ := fun ω => ∫ u in s..t, H u ω * H u ω with hQ
  set Tk : ℕ → Ω → ℝ := fun k ω => timeSum (ps k) f (fun u => X u ω) with hTk
  set Rk : ℕ → Ω → ℝ := fun k ω => remSum (ps k) f fx fxx (fun u => X u ω) with hRk
  set D : Ω → ℝ := fun ω => f t (X t ω) - f s (X s ω) with hD
  -- the exact identity
  have hid : ∀ k ω, D ω = Tk k ω + sumRS (ps k) G1 X ω + wSumCross (ps k) G2 X X ω / 2
      + Rk k ω := fun k ω => itoTaylor_partition_identity (ps k) f fx fxx (fun u => X u ω)
  -- integrability of the limits
  have iLT : Integrable LT P :=
    (memLp_integral_drift hGt le_rfl hst.le le_rfl).integrable one_le_two
  have iL3 : Integrable L3 P :=
    (memLp_integral_drift (itoIntegrand_mul hG2 hHH) le_rfl hst.le le_rfl).integrable one_le_two
  have iQ : Integrable Q P :=
    (memLp_integral_drift hHH le_rfl hst.le le_rfl).integrable one_le_two
  -- (1) the time sum
  have mTk : ∀ k, Measurable (Tk k) := fun k => Finset.measurable_sum _ fun i hi =>
    (hcm f cf _ _ (t_mem _ (Finset.mem_range.1 hi))).sub
      (hcm f cf _ _ (t_mem _ (Finset.mem_range.1 hi)))
  have bTk : ∀ k ω, |Tk k ω - LT ω| ≤ 4 * Lt * (t - s) := fun k ω => by
    have h1 := abs_timeSum_le hft hftb (ps k) (fun u => X u ω)
    have h2 := abs_integral_drift_le hGt.bound le_rfl hst.le le_rfl ω
    calc |Tk k ω - LT ω| ≤ |Tk k ω| + |LT ω| := abs_sub _ _
      _ ≤ 4 * Lt * (t - s) := by
        simp only [hTk, hLT]
        linarith
  have hT : Tendsto (fun k => ∫ ω, |Tk k ω - LT ω| ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (F := fun k ω => |Tk k ω - LT ω|)
      (f := fun _ => (0 : ℝ)) (fun _ => 4 * Lt * (t - s))
      (fun k => (((mTk k).aestronglyMeasurable).sub iLT.1).norm) (integrable_const _)
      (fun k => ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_abs]; exact bTk k ω)
      (by
        filter_upwards [hXc] with ω hω
        have h := ((tendsto_timeSum hft hfx hfxx cft cfxx hω ps hps).sub_const (LT ω)).abs
        simpa [hTk, hLT] using h)
    simpa using h
  have iT : ∀ k, Integrable (fun ω => Tk k ω - LT ω) P := fun k =>
    Integrable.of_bound (((mTk k).aestronglyMeasurable).sub iLT.1) (4 * Lt * (t - s))
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact bTk k ω)
  -- (2) the first-order sum
  have h1 : L2Tendsto P (fun k => sumRS (ps k) G1 X) L1 :=
    L2Tendsto_sumRS hB hW h𝓕 hs hst hG1 hX ps hps
  have t1 := tendsto_integral_abs_of_L2Tendsto h1
  have iS1 : ∀ k, Integrable (fun ω => sumRS (ps k) G1 X ω - L1 ω) P := fun k =>
    ((h1.1 k).sub h1.2.1).integrable one_le_two
  -- (3) the weighted bracket
  have t3 := tendsto_integral_abs_wSumCross hB hW h𝓕 hs hst hX hX hG2 ps hps
  have iS2 : ∀ k, Integrable (fun ω => wSumCross (ps k) G2 X X ω - L3 ω) P := fun k =>
    (integrable_wSumCross hB hW h𝓕 hs hX hX hG2 (ps k)).sub iL3
  -- (4) the remainder
  set Qk : ℕ → Ω → ℝ := fun k => sumCross (ps k) X X with hQk
  have hQk0 : ∀ k ω, 0 ≤ Qk k ω := fun k ω => by
    simp only [hQk, sumCross, crossSum]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hZle : ∀ k ω, |Rk k ω| ≤ 2 * L2 * Qk k ω := fun k ω =>
    abs_remSum_le hfx hfxx hfxxb (ps k) (fun u => X u ω)
  have mRk : ∀ k, Measurable (Rk k) := fun k => Finset.measurable_sum _ fun i hi => by
    have hv := t_mem (ps k) (Finset.mem_range.1 hi)
    have hu := t_mem (ps k) (Finset.mem_range.1 hi).le
    exact (((hcm f cf _ _ hv).sub (hcm f cf _ _ hu)).sub ((hG1.measurable hu).mul
      ((hXm _ hv).sub (hXm _ hu)))).sub (((hcm fxx cfxx _ _ hu).div_const 2).mul
      (((hXm _ hv).sub (hXm _ hu)).pow_const 2))
  have mQk : ∀ k, Measurable (Qk k) := fun k => Finset.measurable_sum _ fun i hi =>
    ((hXm _ (t_mem _ (Finset.mem_range.1 hi))).sub (hXm _ (t_mem _ (Finset.mem_range.1 hi).le))).mul
      ((hXm _ (t_mem _ (Finset.mem_range.1 hi))).sub (hXm _ (t_mem _ (Finset.mem_range.1 hi).le)))
  set ρ : ℕ → Ω → ℝ := fun k ω => |Rk k ω| / Qk k ω with hρ
  have mρ : ∀ k, Measurable (ρ k) := fun k =>
    Measurable.div (continuous_abs.measurable.comp (mRk k)) (mQk k)
  have hρ0 : ∀ k ω, 0 ≤ ρ k ω := fun k ω => div_nonneg (abs_nonneg _) (hQk0 k ω)
  have hρb : ∀ k ω, ρ k ω ≤ 2 * L2 := fun k ω => by
    rcases (hQk0 k ω).eq_or_lt with h0 | h0
    · simp only [hρ, ← h0, div_zero]
      positivity
    · exact (div_le_iff₀ h0).2 (hZle k ω)
  have hZρ : ∀ k ω, |Rk k ω| = ρ k ω * Qk k ω := fun k ω => by
    rcases (hQk0 k ω).eq_or_lt with h0 | h0
    · have h := hZle k ω
      rw [← h0, mul_zero] at h
      rw [← h0, mul_zero]
      exact le_antisymm h (abs_nonneg _)
    · simp only [hρ]
      rw [div_mul_cancel₀ _ h0.ne']
  have hρlim : ∀ᵐ ω ∂P, Tendsto (fun k => ρ k ω) atTop (𝓝 0) := by
    filter_upwards [hXc] with ω hω
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => ha.trans_le (hρ0 k ω),
      fun ε hε => ?_⟩
    filter_upwards [eventually_abs_remSum_le hft hfx hfxx cft cfxx hω ps hps (half_pos hε)]
      with k hk
    rcases (hQk0 k ω).eq_or_lt with h0 | h0
    · simp only [hρ, ← h0, div_zero]
      exact hε
    · exact ((div_le_iff₀ h0).2 hk).trans_lt (half_lt_self hε)
  have hQ := tendsto_integral_abs_sumCross hB hW h𝓕 hs hst hX hX ps hps
  have iQk : ∀ k, Integrable (Qk k) P := fun k => integrable_sumCross hB hW h𝓕 hs hX hX (ps k)
  have iρQ : ∀ k, Integrable (fun ω => ρ k ω * Q ω) P := fun k =>
    iQ.bdd_mul (c := 2 * L2) (mρ k).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 k ω)]; exact hρb k ω)
  have iQd : ∀ k, Integrable (fun ω => |Qk k ω - Q ω|) P := fun k => ((iQk k).sub iQ).abs
  have iR : ∀ k, Integrable (Rk k) P := fun k =>
    ((iQk k).const_mul (2 * L2)).mono' (mRk k).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hZle k ω)
  have hρQ : Tendsto (fun k => ∫ ω, ρ k ω * Q ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (F := fun k ω => ρ k ω * Q ω)
      (f := fun _ => (0 : ℝ)) (fun ω => 2 * L2 * ‖Q ω‖) (fun k => (iρQ k).1)
      (iQ.norm.const_mul _) (fun k => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 k ω), ← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hρb k ω) (norm_nonneg _))
      (by
        filter_upwards [hρlim] with ω hω
        simpa using hω.mul_const (Q ω))
    simpa using h
  have hR : Tendsto (fun k => ∫ ω, |Rk k ω| ∂P) atTop (𝓝 0) := by
    have hlim := hρQ.add (hQ.const_mul (2 * L2))
    rw [mul_zero, add_zero] at hlim
    refine squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) hlim
    rw [← integral_const_mul, ← integral_add (iρQ k) ((iQd k).const_mul _)]
    refine integral_mono (iR k).abs ((iρQ k).add ((iQd k).const_mul _)) fun ω => ?_
    rw [hZρ k ω]
    have e : ρ k ω * Qk k ω = ρ k ω * Q ω + ρ k ω * (Qk k ω - Q ω) := by ring
    rw [e]
    have h1 : ρ k ω * (Qk k ω - Q ω) ≤ ρ k ω * |Qk k ω - Q ω| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (hρ0 k ω)
    have h2 : ρ k ω * |Qk k ω - Q ω| ≤ 2 * L2 * |Qk k ω - Q ω| :=
      mul_le_mul_of_nonneg_right (hρb k ω) (abs_nonneg _)
    simp only [hQk] at h1 h2 ⊢
    linarith
  -- combine
  set L : Ω → ℝ := fun ω => LT ω + L1 ω + L3 ω / 2 with hL
  have e : ∀ k ω, D ω - L ω = (Tk k ω - LT ω) + (sumRS (ps k) G1 X ω - L1 ω)
      + (wSumCross (ps k) G2 X X ω - L3 ω) / 2 + Rk k ω := fun k ω => by
    rw [hid k ω]
    simp only [hL]
    ring
  have iDL : Integrable (fun ω => D ω - L ω) P :=
    ((((iT 0).add (iS1 0)).add ((iS2 0).div_const 2)).add (iR 0)).congr
      (ae_of_all _ fun ω => (e 0 ω).symm)
  have hbound : ∀ k, ∫ ω, |D ω - L ω| ∂P
      ≤ ∫ ω, |Tk k ω - LT ω| ∂P + ∫ ω, |sumRS (ps k) G1 X ω - L1 ω| ∂P
        + ∫ ω, |wSumCross (ps k) G2 X X ω - L3 ω| ∂P + ∫ ω, |Rk k ω| ∂P := by
    intro k
    have j2 : Integrable (fun ω => |Tk k ω - LT ω| + |sumRS (ps k) G1 X ω - L1 ω|) P :=
      (iT k).abs.add (iS1 k).abs
    have j3 : Integrable (fun ω => |Tk k ω - LT ω| + |sumRS (ps k) G1 X ω - L1 ω|
        + |wSumCross (ps k) G2 X X ω - L3 ω|) P := j2.add (iS2 k).abs
    have j4 : Integrable (fun ω => |Tk k ω - LT ω| + |sumRS (ps k) G1 X ω - L1 ω|
        + |wSumCross (ps k) G2 X X ω - L3 ω| + |Rk k ω|) P := j3.add (iR k).abs
    rw [← integral_add (iT k).abs (iS1 k).abs, ← integral_add j2 (iS2 k).abs,
      ← integral_add j3 (iR k).abs]
    refine integral_mono iDL.abs j4 fun ω => ?_
    simp only
    rw [e k ω]
    have h2 : |(wSumCross (ps k) G2 X X ω - L3 ω) / 2| ≤ |wSumCross (ps k) G2 X X ω - L3 ω| := by
      rw [abs_div, abs_two]
      linarith [abs_nonneg (wSumCross (ps k) G2 X X ω - L3 ω)]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      (abs_add_le _ _) h2)) le_rfl)
  have hlim := ((hT.add t1).add t3).add hR
  simp only [add_zero] at hlim
  have h0 : ∫ ω, |D ω - L ω| ∂P ≤ 0 := ge_of_tendsto' hlim hbound
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) iDL.abs).1
    (le_antisymm h0 (integral_nonneg fun _ => abs_nonneg _))
  filter_upwards [hz] with ω hω
  simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hω
  exact hω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **Itô processes with pointwise-equal coefficients**:
an Itô process with drift `a` and diffusion `H` is one with any `a' = a`, `H' = H`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.itoProcess_of_coeff_eq). -/
theorem itoProcess_of_coeff_eq {X a H a' H' : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (ha : ∀ u ω, a u ω = a' u ω)
    (hH : ∀ u ω, H u ω = H' u ω) : ItoProcess P 𝓕 W X a' H' s t Ca CH := by
  have e1 : a = a' := funext fun u => funext (ha u)
  have e2 : H = H' := funext fun u => funext (hH u)
  subst e1 e2
  exact hX

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Itô's formula** for `f ∈ C²` with `f''` bounded
(`|f''| ≤ L`) and continuous, and an Itô process `X` (drift `a`, diffusion `H`) with a.s.
continuous paths on `[s, t]`, `0 ≤ s < t`: almost surely
`f(X_t) − f(X_s) = ∫_s^t f'(X)a du + ∫_s^t f'(X)H dW + ½∫_s^t f''(X_u)H_u² du`
(the `du` integral of `f'(X)a` in mean square, `TidyR7ItoProducts.dtInt`). `f'` need not be
bounded (`f(x) = x²` is covered). The time-independent case of `ito_formula_time`.
Generalises `TidyR7ItoProductRule.ito_formula_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.ito_formula). -/
theorem ito_formula (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (cf'' : Continuous f'') {L : ℝ} (hf''b : ∀ x, |f'' x| ≤ L) :
    (fun ω => f (X t ω) - f (X s ω)) =ᵐ[P] fun ω =>
      dtInt P 𝓕 (fun u ω => f' (X u ω) * a u ω) s t ω
        + itoInt P 𝓕 W (fun u ω => f' (X u ω) * H u ω) s t ω
      + (∫ u in s..t, f'' (X u ω) * (H u ω * H u ω)) / 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hL : 0 ≤ L := (abs_nonneg _).trans (hf''b 0)
  have cf : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have cf' : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
  have hG1 : MSIntegrand P 𝓕 (fun u ω => f' (X u ω)) s t :=
    msIntegrand_comp_lipschitz (hX.toMS hB hW h𝓕 hs) cf' hL
      (abs_sub_le_of_deriv_bound hf' hf''b)
  have h := ito_formula_time (f := fun _ x => f x) (ft := fun _ _ => 0) (fx := fun _ x => f' x)
    (fxx := fun _ x => f'' x) (Lt := 0) (L2 := L) hB hW h𝓕 hs hst hX hXc
    (fun u x => hasDerivAt_const u (f x)) (fun _ x => hf x) (fun _ x => hf' x)
    (cf.comp continuous_snd) continuous_const (cf''.comp continuous_snd)
    (fun _ _ _ => by simp) (fun _ _ x => hf''b x) hG1
  filter_upwards [h] with ω hω
  rw [hω]
  simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Itô's formula with pathwise time integrals.** Under
the hypotheses of `ito_formula`, a.s.
`f(X_t) − f(X_s) = ∫_s^t (f'(X_u)a_u + ½f''(X_u)H_u²) du + ∫_s^t f'(X)H dW`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.ito_formula_pathwise). -/
theorem ito_formula_pathwise (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (cf'' : Continuous f'') {L : ℝ} (hf''b : ∀ x, |f'' x| ≤ L) :
    (fun ω => f (X t ω) - f (X s ω)) =ᵐ[P] fun ω =>
      (∫ u in s..t, (f' (X u ω) * a u ω + f'' (X u ω) / 2 * (H u ω * H u ω)))
        + itoInt P 𝓕 W (fun u ω => f' (X u ω) * H u ω) s t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hL : 0 ≤ L := (abs_nonneg _).trans (hf''b 0)
  have cf' : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
  have hG1 : MSIntegrand P 𝓕 (fun u ω => f' (X u ω)) s t :=
    msIntegrand_comp_lipschitz (hX.toMS hB hW h𝓕 hs) cf' hL
      (abs_sub_le_of_deriv_bound hf' hf''b)
  have e1 := dtInt_ae_eq_integral hst.le (MSIntegrand.mul_itoIntegrand hG1 hX.drift) (by
    filter_upwards [hXc, hX.drift.cont] with ω h1 h2
    exact (cf'.comp_continuousOn h1).mul h2)
  filter_upwards [ito_formula hB hW h𝓕 hs hst hX hXc hf hf' cf'' hf''b, e1, hXc, hX.drift.cont,
    hX.diff.cont] with ω h0 h1 hc ha hH
  rw [h0, h1]
  have i1 : IntervalIntegrable (fun u => f' (X u ω) * a u ω) MeasureTheory.volume s t :=
    ((cf'.comp_continuousOn hc).mul ha).intervalIntegrable_of_Icc hst.le
  have i2 : IntervalIntegrable (fun u => f'' (X u ω) / 2 * (H u ω * H u ω))
      MeasureTheory.volume s t :=
    (((cf''.comp_continuousOn hc).div_const 2).mul (hH.mul hH)).intervalIntegrable_of_Icc hst.le
  rw [intervalIntegral.integral_add i1 i2]
  have e2 : (∫ u in s..t, f'' (X u ω) / 2 * (H u ω * H u ω))
      = (∫ u in s..t, f'' (X u ω) * (H u ω * H u ω)) / 2 := by
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun u _ => by ring
  rw [e2]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `f(X)` is an Itô process** when `f'` and `f''` are
bounded (`|f'| ≤ L₁`, `|f''| ≤ L₂`, `f''` continuous) and `X` is an Itô process with a.s.
continuous paths on `[s, t]`, `0 ≤ s ≤ t`: drift `f'(X)a + ½f''(X)H²` (bounded by
`L₁C_a + ½L₂C_H²`, a.s. continuous) and diffusion `f'(X)H` (bounded by `L₁C_H`). This is how a
positive diffusive `Λ/P` (e.g. `2 + sin W`) enters TidyR7MonetarismIto.ItoMonetaryModel.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.itoProcess_comp). -/
theorem itoProcess_comp (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (cf'' : Continuous f'') {L1 L2 : ℝ} (hf'b : ∀ x, |f' x| ≤ L1) (hf''b : ∀ x, |f'' x| ≤ L2) :
    ItoProcess P 𝓕 W (fun u ω => f (X u ω))
      (fun u ω => f' (X u ω) * a u ω + f'' (X u ω) / 2 * (H u ω * H u ω))
      (fun u ω => f' (X u ω) * H u ω) s t (L1 * Ca + L2 / 2 * (CH * CH)) (L1 * CH) where
  adapted u hu :=
    (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).comp_stronglyMeasurable
      (hX.adapted u hu)
  init := by
    have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    exact memLp_comp_lipschitz hX.init (continuous_iff_continuousAt.2 fun x =>
      (hf x).continuousAt) ((abs_nonneg _).trans (hf'b 0)) (abs_sub_le_of_deriv_bound hf hf'b)
  drift := by
    have cf' : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
    have h1 : ItoIntegrand P 𝓕 (fun u ω => f' (X u ω)) s t L1 :=
      itoIntegrand_comp (g := fun _ x => f' x) hX.adapted hXc (cf'.comp continuous_snd)
        fun _ _ x => hf'b x
    have h2 : ItoIntegrand P 𝓕 (fun u ω => f'' (X u ω) / 2) s t (L2 / 2) :=
      itoIntegrand_comp (g := fun _ x => f'' x / 2) hX.adapted hXc
        ((cf''.comp continuous_snd).div_const 2) fun _ _ x => by
          rw [abs_div, abs_two]
          linarith [hf''b x]
    exact (itoIntegrand_mul h1 hX.drift).add (itoIntegrand_mul h2
      (itoIntegrand_mul hX.diff hX.diff))
  diff := by
    have cf' : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
    exact itoIntegrand_mul (itoIntegrand_comp (g := fun _ x => f' x) hX.adapted hXc
      (cf'.comp continuous_snd) fun _ _ x => hf'b x) hX.diff
  eq u hu := by
    rcases hu.1.lt_or_eq with hsu | hsu
    · have h := ito_formula_pathwise hB hW h𝓕 hs hsu (itoProcess_restrict hX hu.2)
        (by filter_upwards [hXc] with ω hω; exact hω.mono (Set.Icc_subset_Icc le_rfl hu.2))
        hf hf' cf'' hf''b
      filter_upwards [h] with ω hω
      linarith
    · subst hsu
      refine ae_of_all _ fun ω => ?_
      simp [itoInt_of_le le_rfl]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the conditional form of Itô's formula**, the form
the expected-increment calculations of (1.32)–(1.34) use: under the hypotheses of
`itoProcess_comp` and `s < t`, a.s.
`E_s[f(X_t) − f(X_s)] = E_s[∫_s^t (f'(X_u)a_u + ½f''(X_u)H_u²) du]`
(the `dW` integral has conditional mean `0`, `TidyR7ItoUnbounded.condExp_itoInt_ms`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.condExp_ito_formula). -/
theorem condExp_ito_formula (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (cf'' : Continuous f'') {L1 L2 : ℝ} (hf'b : ∀ x, |f' x| ≤ L1) (hf''b : ∀ x, |f'' x| ≤ L2) :
    P[fun ω => f (X t ω) - f (X s ω) | 𝓕 s] =ᵐ[P]
      P[fun ω => ∫ u in s..t, (f' (X u ω) * a u ω + f'' (X u ω) / 2 * (H u ω * H u ω))
        | 𝓕 s] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hY := itoProcess_comp hB hW h𝓕 hs hX hXc hf hf' cf'' hf'b hf''b
  have hG := ItoIntegrand.toMS hY.diff
  refine condExp_eq_of_ae_eq_add (ito_formula_pathwise hB hW h𝓕 hs hst hX hXc hf hf' cf''
    hf''b) ((memLp_integral_drift hY.drift le_rfl hst.le le_rfl).integrable one_le_two)
    ((memLp_itoInt_ms hB hW h𝓕 hs hG).integrable one_le_two)
    (condExp_itoInt_ms hB hW h𝓕 hs hG)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫ cG dW = c∫G dW` a.s. for a mean-square
continuous `G` and a constant `c`, `0 ≤ s`.
The mean-square analogue of `TidyR7ItoIntegral.itoInt_const_mul`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.itoInt_const_mul_ms). -/
theorem itoInt_const_mul_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (c : ℝ) :
    itoInt P 𝓕 W (fun u ω => c * G u ω) s t =ᵐ[P] fun ω => c * itoInt P 𝓕 W G s t ω := by
  rcases lt_or_ge s t with hst | hts
  · have h2 : L2Tendsto P (fun k => itoSum W (fun u ω => c * G u ω) (dyadic hst k))
        (fun ω => c * itoInt P 𝓕 W G s t ω) :=
      ((L2Tendsto_dyadic_ms hB hW h𝓕 hs hst hG).const_mul c).congr_seq
        (fun k => ae_of_all _ fun ω => by rw [itoSum_const_mul])
    have h1 := (itoInt_spec hst ⟨_, stronglyMeasurable_itoInt.const_mul c, h2⟩).2
    exact ae_eq_of_L2Tendsto h1 h2
  · rw [itoInt_of_le hts, itoInt_of_le hts]
    exact ae_of_all _ fun ω => by simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `f(x) = x²` recovers the product-rule formula**
(`TidyR7ItoProductRule.ito_formula_sq`): for an Itô process with a.s. continuous paths,
the instance of `ito_formula` with `f' = 2x`, `f'' = 2` gives a.s.
`X_t² − X_s² = 2(∫X a du + ∫X H dW) + ∫_s^t H_u² du`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.ito_formula_sq_recovers). -/
theorem ito_formula_sq_recovers (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => X u ω) (Set.Icc s t)) :
    (fun ω => X t ω ^ 2 - X s ω ^ 2) =ᵐ[P] fun ω =>
      2 * (dtInt P 𝓕 (fun u ω => X u ω * a u ω) s t ω
        + itoInt P 𝓕 W (fun u ω => X u ω * H u ω) s t ω) + ∫ u in s..t, H u ω ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hf : ∀ x : ℝ, HasDerivAt (fun x => x ^ 2) (2 * x) x := fun x => by
    simpa using hasDerivAt_pow 2 x
  have hf' : ∀ x : ℝ, HasDerivAt (fun x => 2 * x) 2 x := fun x => by
    simpa using (hasDerivAt_id x).const_mul 2
  have h := ito_formula hB hW h𝓕 hs hst hX hXc (f := fun x => x ^ 2) hf hf' continuous_const
    (L := 2) (fun _ => by norm_num)
  have hXa := MSIntegrand.mul_itoIntegrand (hX.toMS hB hW h𝓕 hs) hX.drift
  have hXH := MSIntegrand.mul_itoIntegrand (hX.toMS hB hW h𝓕 hs) hX.diff
  have e1 : (fun u ω => 2 * X u ω * a u ω) = fun u ω => 2 * (X u ω * a u ω) :=
    funext fun u => funext fun ω => mul_assoc _ _ _
  have e2 : (fun u ω => 2 * X u ω * H u ω) = fun u ω => 2 * (X u ω * H u ω) :=
    funext fun u => funext fun ω => mul_assoc _ _ _
  have d1 := dtInt_const_mul hXa 2
  have d2 := itoInt_const_mul_ms hB hW h𝓕 hs hXH 2
  rw [← e1] at d1
  rw [← e2] at d2
  filter_upwards [h, d1, d2] with ω h0 h1 h2
  rw [h0, h1, h2]
  have e3 : (∫ u in s..t, 2 * (H u ω * H u ω)) / 2 = ∫ u in s..t, H u ω ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    have : (fun u => H u ω * H u ω) = fun u => H u ω ^ 2 := funext fun u => (sq _).symm
    rw [this]
    ring
  rw [e3]
  ring

/-! ## Non-vacuity: `sin W` -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity of Itô's formula): `sin W` is an Itô
process** for a Brownian motion with continuous paths, drift `−½ sin W`, diffusion `cos W`, on
every `[s, t]`, `0 ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.itoProcess_sin_bm). -/
theorem itoProcess_sin_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) (hs : 0 ≤ s) :
    ItoProcess P 𝓕 W (fun u ω => Real.sin (bmReal W u ω))
      (fun u ω => -(Real.sin (bmReal W u ω) / 2)) (fun u ω => Real.cos (bmReal W u ω)) s t
      (1 * 0 + 1 / 2 * (1 * 1)) (1 * 1) := by
  have h := itoProcess_comp (t := t) hB hW h𝓕 hs (itoProcess_bm hB hW h𝓕 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn) (f := Real.sin)
    (f' := Real.cos) (f'' := fun x => -Real.sin x) Real.hasDerivAt_sin
    (fun x => by simpa using Real.hasDerivAt_cos x) Real.continuous_sin.neg
    (L1 := 1) (L2 := 1) Real.abs_cos_le_one (fun x => by rw [abs_neg]; exact Real.abs_sin_le_one x)
  exact itoProcess_of_coeff_eq h (fun u ω => by ring) (fun u ω => by ring)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity on the constructed motion
`bmPath`): `sin W_1 = ∫_0^1 cos W dW − ½∫_0^1 sin W_u du`** a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoFormula.ito_formula_sin_bmPath). -/
theorem ito_formula_sin_bmPath :
    (fun ω => Real.sin (bmPath 1 ω)) =ᵐ[gaussSeq] fun ω =>
      itoInt gaussSeq (bmFiltrationReal bmPath
        measurable_bmPath) bmPath (fun u ω => Real.cos (bmReal bmPath u ω))
        0 1 ω - (∫ u in (0 : ℝ)..1, Real.sin (bmReal bmPath u ω)) / 2 := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have h := ito_formula_pathwise hB measurable_bmPath h𝓕 le_rfl zero_lt_one
    (itoProcess_bm (t := 1) hB measurable_bmPath h𝓕 le_rfl)
    (ae_of_all _ fun ω =>
      (continuous_bmReal (continuous_bmPath ω)).continuousOn)
    (f := Real.sin) (f' := Real.cos) (f'' := fun x => -Real.sin x) Real.hasDerivAt_sin
    (fun x => by simpa using Real.hasDerivAt_cos x) Real.continuous_sin.neg (L := 1)
    (fun x => by rw [abs_neg]; exact Real.abs_sin_le_one x)
  filter_upwards [h] with ω hω
  have w1 : bmReal bmPath 1 ω = bmPath 1 ω := by simp only [bmReal, Real.toNNReal_one]
  have w0 : bmReal bmPath 0 ω = 0 := by
    simp only [bmReal, Real.toNNReal_zero, bmPath_zero]
  simp only [w1, w0, Real.sin_zero, sub_zero, mul_zero, mul_one, zero_add] at hω
  rw [hω]
  have e : (∫ u in (0 : ℝ)..1, -Real.sin (bmReal bmPath u ω) / 2)
      = -((∫ u in (0 : ℝ)..1, Real.sin (bmReal bmPath u ω)) / 2) := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun u _ => by ring
  rw [e]
  ring

end Cochrane.ZeroBound.TidyR9ItoFormula
