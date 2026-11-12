/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR7ItoBridge
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Wiener integrals of `C¹` integrands are Gaussian

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197: the
continuous-time AR(1) surplus `ds = −η(s − s̄)dt + σ dz` is driven by Brownian motion through the
Wiener integral `∫_0^t e^{ηu} dW_u`. This module supplies the tools: for a deterministic `C¹`
integrand `h` and a pre-Brownian motion `W` with continuous paths,

* `itoInt_ae_eq_wienerBP`: the Itô integral `∫_s^t h dW` (`TidyR7ItoIntegral.itoInt`) equals,
  almost surely, the pathwise by-parts expression
  `wienerBP W h h' s t = h(t)W_t − h(s)W_s − ∫_s^t W_u h'(u) du`;
* `integral_wienerBP_sq`: `E[(∫_s^t h dW)²] = ∫_s^t h²` (Wiener isometry);
* `map_wienerBP`: `∫_s^t h dW ~ N(0, ∫_s^t h²)`;
* `exists_map_sum_wienerBP`: every finite linear combination of such integrals (over any
  intervals) is centred Gaussian — the joint Gaussianity used for independence;
* `integral_mul_wienerBP_eq_zero`: integrals over non-overlapping intervals are uncorrelated.

General tools: `exists_gaussianReal_of_tendsto` (an a.s. limit of centred Gaussians is centred
Gaussian, by characteristic functions), `tendsto_sum_mul_sub` (Riemann–Stieltjes sums against a
`C¹` integrator converge to `∫ f h'`), and `IsLinW` (finite linear combinations of values of `W`
are centred Gaussian, `IsLinW.exists_map_eq`).
-/

namespace Cochrane.FiscalConstraints.TidyR7WienerGaussian

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.TidyR7StieltjesSums Cochrane.FiscalConstraints.TidyR7BrownianTools
open Cochrane.FiscalConstraints.TidyR7BrownianQV Cochrane.FiscalConstraints.TidyR7ItoL2
open Cochrane.FiscalConstraints.TidyR7ItoSums Cochrane.FiscalConstraints.TidyR7ItoIntegral
open Cochrane.FiscalConstraints.TidyR7ItoBridge Cochrane.FiscalConstraints.TidyR7BrownianSchauder
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ### Limits of centred Gaussians -/

/-- Cochrane (2023), p. 197 (tool): the characteristic function of `N(0, v)` has modulus
`e^{−vu²/2}`.
The modulus of Mathlib `charFun_gaussianReal`. -/
theorem norm_charFun_gaussianReal (v : ℝ≥0) (u : ℝ) :
    ‖charFun (gaussianReal 0 v) u‖ = Real.exp (-((v : ℝ) * u ^ 2 / 2)) := by
  rw [charFun_gaussianReal, Complex.norm_exp]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Complex.neg_re]
  norm_cast

/-- **Cochrane (2023), p. 197 (tool): an almost-sure limit of centred Gaussians is centred
Gaussian.** No convergence of the variances is assumed: it follows from the convergence of the
characteristic functions near `0`. -/
theorem exists_gaussianReal_of_tendsto [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {v : ℕ → ℝ≥0} (hX : ∀ n, AEMeasurable (X n) P)
    (hlaw : ∀ n, P.map (X n) = gaussianReal 0 (v n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    ∃ w : ℝ≥0, P.map Y = gaussianReal 0 w := by
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae' hX hlim
  have : IsProbabilityMeasure (P.map Y) := inferInstance
  have hce : ∀ u : ℝ, Continuous fun x : ℝ => Complex.exp (u * x * Complex.I) := fun u => by
    fun_prop
  have h1 : ∀ u : ℝ,
      Tendsto (fun n => charFun (P.map (X n)) u) atTop (𝓝 (charFun (P.map Y) u)) := by
    intro u
    simp_rw [charFun_apply_real]
    rw [integral_map hY (by fun_prop)]
    simp_rw [fun n => integral_map (hX n) (f := fun x : ℝ => Complex.exp (u * x * Complex.I))
      (by fun_prop)]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
      (integrable_const _) (fun n => ?_) ?_
    · exact (hce u).comp_aestronglyMeasurable (hX n).aestronglyMeasurable
    · refine Eventually.of_forall fun ω => le_of_eq ?_
      rw [show (u : ℂ) * (X n ω : ℂ) * Complex.I = ((u * X n ω : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    · filter_upwards [hlim] with ω hω
      exact ((hce u).tendsto _).comp hω
  -- a point `u₀ ≠ 0` where the limit characteristic function is not small
  have hφ : Continuous fun u => ‖charFun (P.map Y) u‖ := continuous_charFun.norm
  have h0 : ‖charFun (P.map Y) 0‖ = 1 := by simp [charFun_zero]
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℝ), (1 / 2 : ℝ) < ‖charFun (P.map Y) u‖ ∧ u ≠ 0 := by
    refine (((hφ.tendsto 0).eventually (lt_mem_nhds (?_ : (1 / 2 : ℝ) <
      ‖charFun (P.map Y) 0‖))).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    rw [h0]
    norm_num
  obtain ⟨u0, hu0, hu0ne⟩ := hev.exists
  set c := ‖charFun (P.map Y) u0‖ with hc
  have hcpos : 0 < c := by linarith
  have hn : Tendsto (fun n => Real.exp (-((v n : ℝ) * u0 ^ 2 / 2))) atTop (𝓝 c) := by
    have := ((continuous_norm.tendsto _).comp (h1 u0))
    simp only [Function.comp_def, hlaw, norm_charFun_gaussianReal] at this
    exact this
  have hu2 : 0 < u0 ^ 2 := by positivity
  have hvr : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 (-2 * Real.log c / u0 ^ 2)) := by
    have hl := ((Real.continuousAt_log hcpos.ne').tendsto.comp hn).const_mul (-2) |>.div_const
      (u0 ^ 2)
    refine hl.congr fun n => ?_
    simp only [Function.comp_apply, Real.log_exp]
    field_simp
  refine ⟨(-2 * Real.log c / u0 ^ 2).toNNReal, map_eq_gaussianReal_of_tendsto hX hlaw hlim ?_⟩
  have := (continuous_real_toNNReal.tendsto _).comp hvr
  simpa [Function.comp_def] using this

/-! ### Riemann–Stieltjes sums against a `C¹` integrator -/

/-- **Cochrane (2023), p. 197 (tool): Riemann–Stieltjes sums against a `C¹` integrator.** For
continuous `f`, `h` with continuous derivative `h'`, and partitions of `[a, b]` with mesh `→ 0`,
`Σ f(t_{i+1})(h(t_{i+1}) − h(t_i)) → ∫_a^b f h'`.
A right-endpoint, C¹-integrator variant of `TidyR7StieltjesSums.tendsto_rsSum_of_continuousOn`. -/
theorem tendsto_sum_mul_sub {a b : ℝ} {f h h' : ℝ → ℝ} (hf : Continuous f)
    (hh : ∀ x, HasDerivAt h (h' x) x) (hh' : Continuous h') (ps : ℕ → Partition a b)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
      f ((ps k).t (i + 1)) * (h ((ps k).t (i + 1)) - h ((ps k).t i))) atTop
      (𝓝 (∫ x in a..b, f x * h' x)) := by
  have hab : a ≤ b := a_le_b (ps 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    hh'.continuousOn
  set C' := max C 0 + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  set L := b - a + 1 with hL
  have hLpos : 0 < L := by linarith
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) (ε / (2 * C' * L))
    (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun k hk => ?_⟩
  set p := ps k
  have hmesh : mesh p < δ := hN k hk
  have hcell : ∀ i ∈ Finset.range p.n, f (p.t (i + 1)) * (h (p.t (i + 1)) - h (p.t i))
      = ∫ x in p.t i..p.t (i + 1), f (p.t (i + 1)) * h' x := by
    intro i _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hh x) (hh'.intervalIntegrable _ _)]
  have hint : ∫ x in a..b, f x * h' x
      = ∑ i ∈ Finset.range p.n, ∫ x in p.t i..p.t (i + 1), f x * h' x := by
    have hs := intervalIntegral.sum_integral_adjacent_intervals (f := fun x => f x * h' x)
      (a := p.t) (n := p.n) (μ := volume) (fun _ _ => (hf.mul hh').intervalIntegrable _ _)
    rw [p.first, p.last] at hs
    exact hs.symm
  have hdiff : (∑ i ∈ Finset.range p.n, f (p.t (i + 1)) * (h (p.t (i + 1)) - h (p.t i)))
      - ∫ x in a..b, f x * h' x
      = ∑ i ∈ Finset.range p.n, ∫ x in p.t i..p.t (i + 1), (f (p.t (i + 1)) - f x) * h' x := by
    rw [Finset.sum_congr rfl hcell, hint, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← intervalIntegral.integral_sub (f := fun x => f (p.t (i + 1)) * h' x)
      (g := fun x => f x * h' x) ((continuous_const.mul hh').intervalIntegrable _ _)
      ((hf.mul hh').intervalIntegrable _ _)]
    congr 1
    funext x
    ring
  have hbound : ∀ i ∈ Finset.range p.n,
      ‖∫ x in p.t i..p.t (i + 1), (f (p.t (i + 1)) - f x) * h' x‖
        ≤ ε / (2 * C' * L) * C' * (p.t (i + 1) - p.t i) := by
    intro i hi
    have hi' : i < p.n := Finset.mem_range.1 hi
    have hlt : p.t i < p.t (i + 1) := p.strictMono (Nat.lt_succ_self i)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := p.t i) (b := p.t (i + 1)) (C := ε / (2 * C' * L) * C')
      (f := fun x => (f (p.t (i + 1)) - f x) * h' x) ?_
    · rwa [abs_of_pos (sub_pos.2 hlt)] at h
    intro x hx
    rw [Set.uIoc_of_le hlt.le] at hx
    have hxI : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self (Ioc_subset p hi' hx)
    have hyI : p.t (i + 1) ∈ Set.Icc a b := t_mem p hi'
    have hd : dist (p.t (i + 1)) x < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.2])]
      have := le_mesh p hi'
      linarith [hx.1]
    have h1 := hfδ _ hyI _ hxI hd
    rw [Real.dist_eq] at h1
    have h2 : ‖h' x‖ ≤ C' := (hC x hxI).trans (by rw [hC']; linarith [le_max_left C 0])
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul h1.le h2 (norm_nonneg _) (by positivity)
  have htel : ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) = b - a := by
    rw [Finset.sum_range_sub (fun i => p.t i), p.last, p.first]
  rw [Real.dist_eq, hdiff]
  calc |∑ i ∈ Finset.range p.n, ∫ x in p.t i..p.t (i + 1), (f (p.t (i + 1)) - f x) * h' x|
      ≤ ∑ i ∈ Finset.range p.n, ‖∫ x in p.t i..p.t (i + 1), (f (p.t (i + 1)) - f x) * h' x‖ :=
        by rw [← Real.norm_eq_abs]; exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range p.n, ε / (2 * C' * L) * C' * (p.t (i + 1) - p.t i) :=
        Finset.sum_le_sum hbound
    _ = ε / (2 * C' * L) * C' * (b - a) := by rw [← Finset.mul_sum, htel]
    _ < ε := by
        have e : ε / (2 * C' * L) * C' * (b - a) = ε * ((b - a) / (2 * L)) := by
          field_simp
        rw [e]
        have : (b - a) / (2 * L) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        nlinarith

/-! ### Finite linear combinations of `W` -/

/-- Cochrane (2023), p. 197 (tool): `X` is a finite linear combination of values `W_τ` of the
driving motion (an element of the linear span of `{W_τ}` in `Ω → ℝ`). -/
def IsLinW (W : ℝ≥0 → Ω → ℝ) (X : Ω → ℝ) : Prop := X ∈ Submodule.span ℝ (Set.range W)

/-- Cochrane (2023), p. 197 (tool): every value `W_τ` is a linear combination. -/
theorem isLinW_eval (τ : ℝ≥0) : IsLinW W (W τ) := Submodule.subset_span ⟨τ, rfl⟩

/-- **Cochrane (2023), p. 197 (tool): finite linear combinations of a pre-Brownian motion are
centred Gaussian.**
From Mathlib `IsPreBrownianReal.isGaussianProcess`. -/
theorem IsLinW.exists_map_eq (hB : IsPreBrownianReal W P) {X : Ω → ℝ} (hX : IsLinW W X) :
    ∃ v : ℝ≥0, P.map X = gaussianReal 0 v := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hX
  have hXe : X = fun ω => ∑ τ ∈ c.support, c τ • W τ ω := by
    rw [← hc]
    funext ω
    simp [Finsupp.sum, Finset.sum_apply]
  have hG : HasGaussianLaw X P := by
    rw [hXe]
    exact (hB.isGaussianProcess.smul fun τ => c τ).hasGaussianLaw_fun_sum
  have hmean : P[X] = 0 := by
    rw [hXe]
    change ∫ ω, ∑ τ ∈ c.support, c τ • W τ ω ∂P = 0
    rw [integral_finsetSum (f := fun τ ω => c τ • W τ ω) _
      fun τ _ => (hB.integrable_eval τ).smul (c τ)]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [integral_smul, hB.integral_eval τ, smul_zero]
  exact ⟨_, by rw [hG.map_eq_gaussianReal, hmean]⟩

/-- Cochrane (2023), p. 197 (tool): a deterministic left-point sum `Σ h(t_i)(W_{t_{i+1}} − W_{t_i})`
is a finite linear combination of values of `W`. -/
theorem isLinW_itoSum {s t : ℝ} (h : ℝ → ℝ) (p : Partition s t) :
    IsLinW W (itoSum W (fun u _ => h u) p) := by
  have e : itoSum W (fun u _ => h u) p = ∑ i ∈ Finset.range p.n,
      h (p.t i) • (W (p.t (i + 1)).toNNReal - W (p.t i).toNNReal) := by
    funext ω
    simp [itoSum, incr, bmReal, Finset.sum_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.sub_mem _ (isLinW_eval _) (isLinW_eval _))

/-! ### The Wiener integral by parts -/

/-- Cochrane (2023), p. 197: the pathwise by-parts form of the Wiener integral `∫_s^t h dW`,
`h(t)W_t − h(s)W_s − ∫_s^t W_u h'(u) du`. -/
noncomputable def wienerBP (W : ℝ≥0 → Ω → ℝ) (h h' : ℝ → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  h t * bmReal W t ω - h s * bmReal W s ω - ∫ u in s..t, bmReal W u ω * h' u

/-- Cochrane (2023), p. 197: on every continuous path the deterministic left-point sums
`Σ h(t_i)ΔW_i` along the dyadic partitions converge to `wienerBP`.
The deterministic C¹ form of `TidyR7ItoBridge.itoSum_eq_byParts`. -/
theorem tendsto_itoSum_wienerBP {h h' : ℝ → ℝ} (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh' : Continuous h') {s t : ℝ} (hst : s < t) {ω : Ω} (hω : Continuous fun u => W u ω) :
    Tendsto (fun k => itoSum W (fun u _ => h u) (dyadic hst k) ω) atTop
      (𝓝 (wienerBP W h h' s t ω)) := by
  have hT := tendsto_sum_mul_sub (continuous_bmReal hω) hh hh' (fun k => dyadic hst k)
    (tendsto_mesh_dyadic hst)
  have e : ∀ k, itoSum W (fun u _ => h u) (dyadic hst k) ω
      = h t * bmReal W t ω - h s * bmReal W s ω
        - ∑ i ∈ Finset.range (dyadic hst k).n, bmReal W ((dyadic hst k).t (i + 1)) ω
          * (h ((dyadic hst k).t (i + 1)) - h ((dyadic hst k).t i)) := by
    intro k
    rw [itoSum_eq_byParts, sub_sub]
    congr 1
    rw [rsSum, crossSum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  exact tendsto_const_nhds.sub hT

/-- **Cochrane (2023), p. 197: the Itô integral of a deterministic `C¹` integrand is the
by-parts Wiener integral**, `∫_s^t h dW = h(t)W_t − h(s)W_s − ∫_s^t W_u h'(u)du` a.s., for any
admissible filtration, `0 ≤ s < t`, and a pre-Brownian motion with continuous paths.
The C¹ case of `TidyR7ItoBridge.itoInt_deterministic`. -/
theorem itoInt_ae_eq_wienerBP (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {𝓕 : Filtration ℝ mΩ} (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    {h h' : ℝ → ℝ} (hh : ∀ x, HasDerivAt h (h' x) x) (hh' : Continuous h') {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) :
    itoInt P 𝓕 W (fun u _ => h u) s t =ᵐ[P] wienerBP W h h' s t := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc s t) hhc.continuousOn
  have hI : ItoIntegrand P 𝓕 (fun u _ => h u) s t C :=
    itoIntegrand_deterministic hhc.continuousOn fun u hu => by
      simpa [Real.norm_eq_abs] using hC u hu
  exact ae_eq_of_L2Tendsto_of_ae_tendsto (L2Tendsto_dyadic hB hW h𝓕 hs hst hI)
    (ae_of_all _ fun ω => tendsto_itoSum_wienerBP hh hh' hst (hcont ω))

/-- **Cochrane (2023), p. 197: the Wiener isometry** for the by-parts integral,
`E[(∫_s^t h dW)²] = ∫_s^t h²`.
Restates `TidyR7ItoBridge.integral_itoInt_deterministic_sq`. -/
theorem integral_wienerBP_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {h h' : ℝ → ℝ} (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh' : Continuous h') {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∫ ω, wienerBP W h h' s t ω ^ 2 ∂P = ∫ u in s..t, h u ^ 2 := by
  have h𝓕 := bmFiltrationReal_isBM hB hW
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc s t) hhc.continuousOn
  have hae := itoInt_ae_eq_wienerBP hB hW h𝓕 hcont hh hh' hs hst
  rw [← integral_itoInt_deterministic_sq hB hW h𝓕 hs hst.le hhc.continuousOn
    (fun u hu => by simpa [Real.norm_eq_abs] using hC u hu)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with ω hω
  rw [hω]

/-- Cochrane (2023), p. 197: the by-parts Wiener integral is square integrable. -/
theorem memLp_wienerBP (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {h h' : ℝ → ℝ} (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh' : Continuous h') {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    MemLp (wienerBP W h h' s t) 2 P := by
  have h𝓕 := bmFiltrationReal_isBM hB hW
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x => (hh x).continuousAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc s t) hhc.continuousOn
  have hI : ItoIntegrand P (bmFiltrationReal W hW) (fun u _ => h u) s t C :=
    itoIntegrand_deterministic hhc.continuousOn fun u hu => by
      simpa [Real.norm_eq_abs] using hC u hu
  exact (memLp_itoInt hB hW h𝓕 hs hI).ae_eq (itoInt_ae_eq_wienerBP hB hW h𝓕 hcont hh hh' hs hst)

/-- **Cochrane (2023), p. 197: finite linear combinations of Wiener integrals are jointly
centred Gaussian.** For any finite family of `C¹` integrands `h_i` on intervals
`[s_i, t_i]`, `s_i < t_i`, `Σ_i c_i ∫_{s_i}^{t_i} h_i dW` (by parts) is centred Gaussian. -/
theorem exists_map_sum_wienerBP (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {ι : Type*} (I : Finset ι) (c : ι → ℝ)
    {h h' : ι → ℝ → ℝ} (hh : ∀ i, ∀ x, HasDerivAt (h i) (h' i x) x)
    (hh' : ∀ i, Continuous (h' i)) {s t : ι → ℝ} (hst : ∀ i, s i < t i) :
    ∃ v : ℝ≥0, P.map (fun ω => ∑ i ∈ I, c i * wienerBP W (h i) (h' i) (s i) (t i) ω)
      = gaussianReal 0 v := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set X : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ I, c i * itoSum W (fun u _ => h i u) (dyadic (hst i) k) ω
  have hlin : ∀ k, IsLinW W (X k) := by
    intro k
    have e : X k = ∑ i ∈ I, c i • itoSum W (fun u _ => h i u) (dyadic (hst i) k) := by
      funext ω
      simp [X, Finset.sum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (isLinW_itoSum _ _)
  choose v hv using fun k => (hlin k).exists_map_eq hB
  have hmeas : ∀ k, AEMeasurable (X k) P := by
    intro k
    refine (Finset.measurable_sum _ fun i _ => ?_).aemeasurable
    refine (Finset.measurable_sum _ fun j _ => ?_).const_mul _
    exact measurable_const.mul ((hW _).sub (hW _))
  exact exists_gaussianReal_of_tendsto hmeas hv (ae_of_all _ fun ω =>
    tendsto_finsetSum _ fun i _ =>
      (tendsto_itoSum_wienerBP (hh i) (hh' i) (hst i) (hcont ω)).const_mul (c i))

/-- **Cochrane (2023), p. 197: the Wiener integral is Gaussian**,
`∫_s^t h dW ~ N(0, ∫_s^t h²)` for deterministic `C¹` `h`, `0 ≤ s < t`. -/
theorem map_wienerBP (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {h h' : ℝ → ℝ} (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh' : Continuous h') {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    P.map (wienerBP W h h' s t) = gaussianReal 0 (∫ u in s..t, h u ^ 2).toNNReal := by
  obtain ⟨v, hv⟩ := exists_map_sum_wienerBP (P := P) hB hW hcont {()} (fun _ => 1)
    (h := fun _ => h) (h' := fun _ => h') (fun _ => hh) (fun _ => hh') (s := fun _ => s)
    (t := fun _ => t) (fun _ => hst)
  simp only [Finset.sum_singleton, one_mul] at hv
  have hY : AEMeasurable (wienerBP W h h' s t) P :=
    (memLp_wienerBP hB hW hcont hh hh' hs hst).aestronglyMeasurable.aemeasurable
  have hsq : ∫ ω, wienerBP W h h' s t ω ^ 2 ∂P = v := by
    rw [← integral_sq_gaussianReal v, ← hv, integral_map hY (by fun_prop)]
  have e : (∫ u in s..t, h u ^ 2) = v := by
    rw [← integral_wienerBP_sq hB hW hcont hh hh' hs hst, hsq]
  rw [hv, e, Real.toNNReal_coe]

/-- **Cochrane (2023), p. 197: Wiener integrals over non-overlapping intervals are
uncorrelated**: for `0 ≤ s₁ < t₁ ≤ s₂ < t₂`, `E[∫_{s₁}^{t₁} h₁ dW · ∫_{s₂}^{t₂} h₂ dW] = 0`
(the second has conditional mean zero given `𝓕_{s₂}`). -/
theorem integral_mul_wienerBP_eq_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {h₁ h₁' h₂ h₂' : ℝ → ℝ}
    (hh₁ : ∀ x, HasDerivAt h₁ (h₁' x) x) (hh₁' : Continuous h₁')
    (hh₂ : ∀ x, HasDerivAt h₂ (h₂' x) x) (hh₂' : Continuous h₂') {s₁ t₁ s₂ t₂ : ℝ}
    (hs₁ : 0 ≤ s₁) (h₁₂ : s₁ < t₁) (h₂₃ : t₁ ≤ s₂) (h₃₄ : s₂ < t₂) :
    ∫ ω, wienerBP W h₁ h₁' s₁ t₁ ω * wienerBP W h₂ h₂' s₂ t₂ ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set 𝓕 := bmFiltrationReal W hW
  have h𝓕 : BMFiltration P W 𝓕 := bmFiltrationReal_isBM hB hW
  have hs₂ : 0 ≤ s₂ := by linarith
  have hc₁ : Continuous h₁ := continuous_iff_continuousAt.2 fun x => (hh₁ x).continuousAt
  have hc₂ : Continuous h₂ := continuous_iff_continuousAt.2 fun x => (hh₂ x).continuousAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc s₁ t₁)
    hc₁.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc s₂ t₂)
    hc₂.continuousOn
  have hI₁ : ItoIntegrand P 𝓕 (fun u _ => h₁ u) s₁ t₁ C₁ :=
    itoIntegrand_deterministic hc₁.continuousOn fun u hu => by
      simpa [Real.norm_eq_abs] using hC₁ u hu
  have hI₂ : ItoIntegrand P 𝓕 (fun u _ => h₂ u) s₂ t₂ C₂ :=
    itoIntegrand_deterministic hc₂.continuousOn fun u hu => by
      simpa [Real.norm_eq_abs] using hC₂ u hu
  set X := itoInt P 𝓕 W (fun u _ => h₁ u) s₁ t₁
  set Y := itoInt P 𝓕 W (fun u _ => h₂ u) s₂ t₂
  have hX2 : MemLp X 2 P := memLp_itoInt hB hW h𝓕 hs₁ hI₁
  have hY2 : MemLp Y 2 P := memLp_itoInt hB hW h𝓕 hs₂ hI₂
  have hXY : Integrable (X * Y) P := hX2.integrable_mul hY2
  have hXm : StronglyMeasurable[𝓕 s₂] X :=
    (stronglyMeasurable_itoInt (P := P) (W := W) (H := fun u _ => h₁ u) (s := s₁)).mono
      (𝓕.mono h₂₃)
  have hce : P[Y | 𝓕 s₂] =ᵐ[P] 0 := by
    have := condExp_itoInt hB hW h𝓕 hs₂ le_rfl h₃₄.le hI₂
    rwa [itoInt_of_le le_rfl] at this
  have hpull := condExp_mul_of_stronglyMeasurable_left hXm hXY (hY2.integrable one_le_two)
  have h0 : ∫ ω, (X * Y) ω ∂P = 0 := by
    rw [← integral_condExp (𝓕.le s₂)]
    refine (integral_congr_ae (hpull.trans ?_)).trans (integral_zero _ _)
    filter_upwards [hce] with ω hω
    simp [hω]
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [itoInt_ae_eq_wienerBP hB hW h𝓕 hcont hh₁ hh₁' hs₁ h₁₂,
    itoInt_ae_eq_wienerBP hB hW h𝓕 hcont hh₂ hh₂' hs₂ h₃₄] with ω e1 e2
  simp only [Pi.mul_apply, X, Y, e1, e2]

end Cochrane.FiscalConstraints.TidyR7WienerGaussian
