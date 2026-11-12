/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR7StochCTPath
import StickyPriceFiscal.TidyR7ItoBridge

/-!
# The continuous-time sticky-price model with Brownian shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7 and §5.7.1,
pp. 162–167, (5.85)–(5.96), and Online Appendix A1, §1.12–1.13, pp. 579–581.

The structural shocks are diffusions, `dε_m = σ_i dW`, `dε_s = σ_s dW`, for one pre-Brownian
motion `W` with continuous paths, `W_0 = 0`, and any admissible filtration `𝓕`
(`TidyR7BrownianQV.BMFiltration`). The model is solved path by path in `TidyR7StochCTPath`; here
each variable is a process `t ↦ (ω ↦ ...)` and the book's expectational statements are proved
with conditional expectations.

## Main results

* **`responses_ito`** (the solution is the deterministic responses with the shock replaced by
  a Wiener integral): for `T ≥ 0`, a.s.
  `π_T = ∫_0^T R_π(T − u) dW_u`, `x_T = ∫_0^T R_x(T − u) dW_u`, `v_T = ∫_0^T R_v(T − u) dW_u`
  (`TidyR7ItoIntegral.itoInt`), where `R` are the responses to a unit MIT shock
  (`TidyR7StochCTPath.resp_eq_ct_step`): the coefficient of `dW_u` in each variable at `T` is
  the book's impulse response at horizon `T − u`.
* **`ito_book_equations`** ((5.85)–(5.90) in the book's `E_t d` form): for `0 ≤ t ≤ T`, a.s.
  `E_t[x_T − x_t] = E_t[∫_t^T σ(i − π)]`, `E_t[π_T − π_t] = E_t[∫_t^T (ρπ − κx)]`,
  `E_t[i_T − i_t] = 0`, `E_t[s̃_T − s̃_t] = 0`, while `v_T − v_t = ∫_t^T (rv + i − π − s̃)` and
  `p_T − p_t = ∫_t^T π` hold on every path (no expectational error, `dv = E_t dv`,
  `dp = E_t dp`). The expectational errors are `dδx = R_x(0)dW`, `dδπ = R_π(0)dW`
  (`expectational_errors`).
* Forecasts and news: `condExp_responses` (`E_t X_T = ∫_0^t R_X(T − u) dW_u`, the moving-average
  form of A1 §1.13), `news_responses` (`E_{t'}X_T − E_tX_T = ∫_t^{t'} R_X(T − u)dW_u`: the
  innovation `Δ_t E X_T` is `R_X(T − t)dW_t`), `innovation_variance`.
* **Valuation under uncertainty** ((5.95) at every date): `pv_identity` (path by path,
  `∫_t^T e^{−r(τ−t)}[s̃ − (i − π)]dτ = v_t − e^{−r(T−t)}v_T`), `condExp_pv`,
  **`tvc_L1`** (`E_t[e^{−r(T−t)}v_T] → 0` in `L¹`) and **`valuation_L1`**
  (`E_t∫_t^T e^{−r(τ−t)}[s̃ − (i − π)]dτ → v_t` in `L¹` as `T → ∞`).
* No covariation correction (`crossSum_v_tendsto_zero`, `crossSum_p_tendsto_zero`): the value
  of debt and the price level are `C¹` on every path, so their bracket with `W` vanishes; the
  book's equations are linear with additive noise, so none of (5.85)–(5.96) needs an Itô term.
* Non-vacuity on the constructed motion `TidyR7BrownianExist.bmPath`: `bmPath_stoch_ct`,
  `bmPath_v_nondegenerate` (`E[v_T²] > 0` for `σ_s ≠ 0`, `T > 0`).

The Wiener-integral tools `tendsto_sum_mul_sub`, `wienerBP`, `tendsto_itoSum_wienerBP`,
`itoInt_ae_eq_wienerBP` are restated from the Cochrane FiscalConstraints project.
-/

namespace Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7StieltjesSums Cochrane.StickyPriceFiscal.TidyR7BrownianTools
open Cochrane.StickyPriceFiscal.TidyR7BrownianQV Cochrane.StickyPriceFiscal.TidyR7ItoL2
open Cochrane.StickyPriceFiscal.TidyR7ItoSums Cochrane.StickyPriceFiscal.TidyR7ItoIntegral
open Cochrane.StickyPriceFiscal.TidyR7ItoBridge Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open Cochrane.StickyPriceFiscal.TidyR7BrownianSchauder
open Cochrane.StickyPriceFiscal.TidyR7StieltjesCalculus
open Cochrane.StickyPriceFiscal.TidyR7StochCTPath Cochrane.StickyPriceFiscal.CTSimple
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ### Wiener integrals by parts (restated from the Cochrane FiscalConstraints project) -/

/-- **Cochrane (2023), §5.7, p. 164 (tool): Riemann–Stieltjes sums against a `C¹` integrator.**
For continuous `f`, `h` with continuous derivative `h'`, and partitions of `[a, b]` with
mesh `→ 0`, `Σ f(t_{i+1})(h(t_{i+1}) − h(t_i)) → ∫_a^b f h'`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7WienerGaussian.tendsto_sum_mul_sub). -/
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

/-- Cochrane (2023), §5.7, p. 164: the pathwise by-parts form of the Wiener integral
`∫_s^t h dW`, `h(t)W_t − h(s)W_s − ∫_s^t W_u h'(u) du`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7WienerGaussian.wienerBP). -/
noncomputable def wienerBP (W : ℝ≥0 → Ω → ℝ) (h h' : ℝ → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  h t * bmReal W t ω - h s * bmReal W s ω - ∫ u in s..t, bmReal W u ω * h' u

/-- Cochrane (2023), §5.7, p. 164: on every continuous path the deterministic left-point sums
`Σ h(t_i)ΔW_i` along the dyadic partitions converge to `wienerBP`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7WienerGaussian.tendsto_itoSum_wienerBP). -/
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

/-- **Cochrane (2023), §5.7, p. 164: the Itô integral of a deterministic `C¹` integrand is the
by-parts Wiener integral**, `∫_s^t h dW = h(t)W_t − h(s)W_s − ∫_s^t W_u h'(u)du` a.s., for any
admissible filtration, `0 ≤ s < t`, and a pre-Brownian motion with continuous paths.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7WienerGaussian.itoInt_ae_eq_wienerBP). -/
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

/-! ### Exponential response kernels -/

/-- Cochrane (2023), (5.96), p. 166: a response kernel `R(τ) = c + d e^{−ητ}` (each response of
the model has this form). -/
noncomputable def kerFn (c d η τ : ℝ) : ℝ := c + d * exp (-(η * τ))

/-- Cochrane (2023), §5.7, p. 164: the process `c W_T + d Y_T` driven by the Brownian path, with
`Y` the OU noise (`TidyR7StochCTPath.ouNoise`). -/
noncomputable def kerProc (W : ℝ≥0 → Ω → ℝ) (c d η T : ℝ) (ω : Ω) : ℝ :=
  c * bmReal W T ω + d * ouNoise η (fun u => bmReal W u ω) T

/-- Cochrane (2023), §5.7, p. 164: the kernel at horizon `T − u` has derivative
`dηe^{−η(T−x)}` in `x`. -/
theorem hasDerivAt_kerFn (c d η T x : ℝ) :
    HasDerivAt (fun u => kerFn c d η (T - u)) (d * η * exp (-(η * (T - x)))) x := by
  have h1 : HasDerivAt (fun u => -(η * (T - u))) η x := by
    have := (((hasDerivAt_id' x).const_sub T).const_mul η).neg
    exact this.congr_deriv (by ring)
  exact ((h1.exp.const_mul d).const_add c).congr_deriv (by ring)

/-- Cochrane (2023), §5.7, p. 164: the kernel is continuous in the integration variable. -/
theorem continuous_kerFn (c d η T : ℝ) : Continuous fun u => kerFn c d η (T - u) := by
  unfold kerFn
  fun_prop

/-- Cochrane (2023), §5.7, p. 164: the kernel integrand is admissible on every `[s, t]`. -/
theorem exists_itoIntegrand_kerFn (c d η T s t : ℝ) :
    ∃ C, ItoIntegrand P 𝓕 (fun u _ => kerFn c d η (T - u)) s t C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc s t)
    (continuous_kerFn c d η T).continuousOn
  exact ⟨C, itoIntegrand_deterministic (continuous_kerFn c d η T).continuousOn fun u hu => by
    simpa [Real.norm_eq_abs] using hC u hu⟩

/-- Cochrane (2023), §5.7, p. 164: path by path, `c W_T + d Y_T` is the by-parts Wiener integral
of the kernel `u ↦ c + d e^{−η(T−u)}` (when `W_0 = 0`).
Generalises the Cochrane FiscalConstraints project's TidyR7OrnsteinUhlenbeck.ouNoise_eq_wienerBP. -/
theorem kerProc_eq_wienerBP (hW0 : ∀ ω, W 0 ω = 0) (c d η T : ℝ) :
    kerProc W c d η T = wienerBP W (fun u => kerFn c d η (T - u))
      (fun u => d * η * exp (-(η * (T - u)))) 0 T := by
  funext ω
  have hb0 : bmReal W 0 ω = 0 := by simp [bmReal, hW0]
  have hfun : (fun u => bmReal W u ω * (d * η * exp (-(η * (T - u)))))
      = fun u => (d * η * exp (-η * T)) * (exp (η * u) * bmReal W u ω) := by
    funext u
    rw [show -(η * (T - u)) = -η * T + η * u by ring, exp_add]
    ring
  simp only [kerProc, wienerBP, kerFn, ouNoise, ouPrim, hb0, hfun,
    intervalIntegral.integral_const_mul, sub_self, mul_zero, neg_zero, exp_zero]
  ring

/-- Cochrane (2023), §5.7, p. 164: `c W_0 + d Y_0 = 0`. -/
theorem kerProc_zero (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) : kerProc W c d η 0 = 0 := by
  funext ω
  simp [kerProc, ouNoise_zero, bmReal, hW0]

/-- **Cochrane (2023), §5.7, p. 164: `c W_T + d Y_T` is the Wiener integral
`∫_0^T (c + d e^{−η(T−u)}) dW_u`** a.s., for every `T ≥ 0`.
Generalises the Cochrane FiscalConstraints project's TidyR7OrnsteinUhlenbeck.ouProc_ae_eq_itoInt. -/
theorem kerProc_ae_eq_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    kerProc W c d η T =ᵐ[P] itoInt P 𝓕 W (fun u _ => kerFn c d η (T - u)) 0 T := by
  rcases hT.lt_or_eq with hT | hT
  · rw [kerProc_eq_wienerBP hW0]
    exact (itoInt_ae_eq_wienerBP hB hW h𝓕 hcont (hasDerivAt_kerFn c d η T)
      (by fun_prop) le_rfl hT).symm
  · subst hT
    rw [kerProc_zero hW0, itoInt_of_le le_rfl]

/-- Cochrane (2023), §5.7, p. 164: `c W_T + d Y_T` is square integrable.
An instance of `TidyR7ItoIntegral.memLp_itoInt`. -/
theorem memLp_kerProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    MemLp (kerProc W c d η T) 2 P := by
  obtain ⟨C, hC⟩ := exists_itoIntegrand_kerFn (P := P) (𝓕 := 𝓕) c d η T 0 T
  exact (memLp_itoInt hB hW h𝓕 le_rfl hC).ae_eq
    (kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d η hT).symm

/-- Cochrane (2023), §5.7, p. 164: `c W_T + d Y_T` is integrable. -/
theorem integrable_kerProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (kerProc W c d η T) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact (memLp_kerProc hB hW h𝓕 hcont hW0 c d η hT).integrable one_le_two

/-- Cochrane (2023), §5.7, p. 164: `c W_T + d Y_T` is (a.e.) `𝓕_T`-measurable: the solution is
adapted. -/
theorem aesm_kerProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    AEStronglyMeasurable[𝓕 T] (kerProc W c d η T) P :=
  ⟨_, stronglyMeasurable_itoInt, kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d η hT⟩

/-- Cochrane (2023), §5.7, p. 164: the variance of `c W_T + d Y_T` is
`∫_0^T (c + d e^{−η(T−u)})² du` (the Wiener isometry).
An instance of `TidyR7ItoBridge.integral_itoInt_deterministic_sq`. -/
theorem integral_kerProc_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, kerProc W c d η T ω ^ 2 ∂P = ∫ u in (0 : ℝ)..T, kerFn c d η (T - u) ^ 2 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 T)
    (continuous_kerFn c d η T).continuousOn
  rw [← integral_itoInt_deterministic_sq hB hW h𝓕 le_rfl hT
    (continuous_kerFn c d η T).continuousOn (fun u hu => by
      simpa [Real.norm_eq_abs] using hC u hu)]
  refine integral_congr_ae ?_
  filter_upwards [kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d η hT] with ω hω
  simp only [hω]

/-- Cochrane (2023), §5.7, p. 164: the kernel at horizon `T − u` is the kernel at horizon
`t − u` with `d` replaced by `d e^{−η(T−t)}`. -/
theorem kerFn_shift (c d η T t : ℝ) :
    (fun u (_ : Ω) => kerFn c d η (T - u))
      = fun u _ => kerFn c (d * exp (-(η * (T - t)))) η (t - u) := by
  funext u _
  simp only [kerFn]
  rw [mul_assoc, ← exp_add]
  ring_nf

/-- **Cochrane (2023), A1 §1.13, p. 581 (moving-average form of forecasts)**: for
`0 ≤ t ≤ T`, `E_t[c W_T + d Y_T] = ∫_0^t (c + d e^{−η(T−u)}) dW_u` a.s.
An instance of `TidyR7ItoIntegral.condExp_itoInt`. -/
theorem condExp_kerProc_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[kerProc W c d η T | 𝓕 t] =ᵐ[P] itoInt P 𝓕 W (fun u _ => kerFn c d η (T - u)) 0 t := by
  obtain ⟨C, hC⟩ := exists_itoIntegrand_kerFn (P := P) (𝓕 := 𝓕) c d η T 0 T
  exact (condExp_congr_ae (kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d η (ht.trans htT))).trans
    (condExp_itoInt hB hW h𝓕 le_rfl ht htT hC)

/-- **Cochrane (2023), §5.7.1, p. 165 (forecasts)**: for `0 ≤ t ≤ T`,
`E_t[c W_T + d Y_T] = c W_t + d e^{−η(T−t)} Y_t` a.s.: the forecast of a response at horizon `T`
decays the transient part at the rate `η`. -/
theorem condExp_kerProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[kerProc W c d η T | 𝓕 t] =ᵐ[P] kerProc W c (d * exp (-(η * (T - t)))) η t := by
  refine (condExp_kerProc_itoInt hB hW h𝓕 hcont hW0 c d η ht htT).trans ?_
  rw [kerFn_shift c d η T t]
  exact (kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c _ η ht).symm

/-- **Cochrane (2023), §5.7, p. 168 (`Δ_t x_t = dx_t − E_t dx_t`, the news)**: for
`0 ≤ t ≤ t' ≤ T`, `E_{t'}[cW_T + dY_T] − E_t[cW_T + dY_T] = ∫_t^{t'} (c + de^{−η(T−u)}) dW_u`
a.s.: the revision of the forecast of the variable at `T` loads on `dW_u` with the
response at horizon `T − u`. -/
theorem news_kerProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {t t' T : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t')
    (ht'T : t' ≤ T) :
    (fun ω => P[kerProc W c d η T | 𝓕 t'] ω - P[kerProc W c d η T | 𝓕 t] ω)
      =ᵐ[P] itoInt P 𝓕 W (fun u _ => kerFn c d η (T - u)) t t' := by
  obtain ⟨C, hC⟩ := exists_itoIntegrand_kerFn (P := P) (𝓕 := 𝓕) c d η T 0 t'
  filter_upwards [condExp_kerProc_itoInt hB hW h𝓕 hcont hW0 c d η (ht.trans htt') ht'T,
    condExp_kerProc_itoInt hB hW h𝓕 hcont hW0 c d η ht (htt'.trans ht'T),
    itoInt_add_itoInt hB hW h𝓕 le_rfl ht htt' hC] with ω h1 h2 h3
  rw [h1, h2, h3]
  ring

/-- **Cochrane (2023), §5.7, p. 164: the innovation variance.** For `0 ≤ t ≤ T`,
`E[(X_T − E_tX_T)²] = ∫_t^T R(T − u)² du` for `X = cW + dY`, `R = c + de^{−η·}`.
An instance of `TidyR7ItoBridge.integral_itoInt_deterministic_sq`. -/
theorem innovation_variance (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (c d η : ℝ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ ω, (kerProc W c d η T ω - P[kerProc W c d η T | 𝓕 t] ω) ^ 2 ∂P
      = ∫ u in t..T, kerFn c d η (T - u) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_itoIntegrand_kerFn (P := P) (𝓕 := 𝓕) c d η T 0 T
  obtain ⟨C', hC'⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc t T)
    (continuous_kerFn c d η T).continuousOn
  rw [← integral_itoInt_deterministic_sq hB hW h𝓕 ht htT
    (continuous_kerFn c d η T).continuousOn (fun u hu => by
      simpa [Real.norm_eq_abs] using hC' u hu)]
  refine integral_congr_ae ?_
  filter_upwards [kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 c d η (ht.trans htT),
    condExp_kerProc_itoInt hB hW h𝓕 hcont hW0 c d η ht htT,
    itoInt_add_itoInt hB hW h𝓕 le_rfl ht htT hC] with ω h1 h2 h3
  rw [h1, h2, h3]
  ring

/-! ### The model's processes -/

/-- Cochrane (2023), (5.94), p. 164: inflation as a process, `π_t(ω)` on the Brownian path. -/
noncomputable def piProc (r σ κ ρ σi σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  piPath r σ κ ρ σi σs (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.92), p. 164: output as a process. -/
noncomputable def xProc (r σ κ ρ σi σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  xPath r σ κ ρ σi σs (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.93), p. 164: the real value of debt as a process. -/
noncomputable def vProc (r σ κ ρ σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  vPath r σ κ ρ σs (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.89), p. 162: the interest rate as a process, `i_t = σ_i W_t`. -/
def iProc (σi : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := iPath σi (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.90), p. 163: the surplus as a process, `s̃_t = σ_s W_t`. -/
def sProc (σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := sPath σs (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.87), p. 162: the price level as a process, `p_t = ∫_0^t π`. -/
noncomputable def pProc (r σ κ ρ σi σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  pPath r σ κ ρ σi σs (fun u => bmReal W u ω) t

variable {r σ κ ρ σi σs : ℝ}

/-- Cochrane (2023), (5.94), p. 164: inflation is `σ_i W + A Y`. -/
theorem piProc_eq_ker : piProc r σ κ ρ σi σs W
    = fun t => kerProc W σi (fiscalLoad r σ κ ρ σs) (lam2 ρ κ σ) t := rfl

/-- Cochrane (2023), (5.92), p. 164: output is `(ρσ_i/κ) W + (λ₁A/κ) Y`. -/
theorem xProc_eq_ker : xProc r σ κ ρ σi σs W = fun t =>
    kerProc W (ρ * σi / κ) (lam1 ρ κ σ * fiscalLoad r σ κ ρ σs / κ) (lam2 ρ κ σ) t := by
  funext t ω
  simp only [xProc, xPath, kerProc]
  ring

/-- Cochrane (2023), (5.93), p. 164: debt is `(σ_s/r) W − (σ_s/r) Y`. -/
theorem vProc_eq_ker : vProc r σ κ ρ σs W
    = fun t => kerProc W (σs / r) (-(σs / r)) (lam2 ρ κ σ) t := by
  funext t ω
  simp only [vProc, vPath, kerProc]
  ring

/-- Cochrane (2023), (5.96), p. 166: `R_π` is the kernel `(σ_i, A, λ₂)`. -/
theorem respPi_eq_ker (τ : ℝ) :
    respPi r σ κ ρ σi σs τ = kerFn σi (fiscalLoad r σ κ ρ σs) (lam2 ρ κ σ) τ := rfl

/-- Cochrane (2023), p. 166: `R_x` is the kernel `(ρσ_i/κ, λ₁A/κ, λ₂)`. -/
theorem respX_eq_ker (τ : ℝ) : respX r σ κ ρ σi σs τ
    = kerFn (ρ * σi / κ) (lam1 ρ κ σ * fiscalLoad r σ κ ρ σs / κ) (lam2 ρ κ σ) τ := by
  simp only [respX, kerFn]
  ring

/-- Cochrane (2023), p. 166: `R_v` is the kernel `(σ_s/r, −σ_s/r, λ₂)`. -/
theorem respV_eq_ker (τ : ℝ) :
    respV r σ κ ρ σs τ = kerFn (σs / r) (-(σs / r)) (lam2 ρ κ σ) τ := by
  simp only [respV, kerFn]
  ring

/-- **Cochrane (2023), §5.7, p. 164, and (5.96), p. 166: the responses to a `dW` shock are the
book's impulse responses.** For `T ≥ 0`, a.s.
`π_T = ∫_0^T R_π(T − u) dW_u`, `x_T = ∫_0^T R_x(T − u) dW_u`, `v_T = ∫_0^T R_v(T − u) dW_u`,
with `R` the deterministic responses to a unit MIT shock (`resp_eq_ct_step`). -/
theorem responses_ito (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {T : ℝ} (hT : 0 ≤ T) :
    piProc r σ κ ρ σi σs W T
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respPi r σ κ ρ σi σs (T - u)) 0 T ∧
      xProc r σ κ ρ σi σs W T
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respX r σ κ ρ σi σs (T - u)) 0 T ∧
      vProc r σ κ ρ σs W T =ᵐ[P] itoInt P 𝓕 W (fun u _ => respV r σ κ ρ σs (T - u)) 0 T := by
  simp only [respX_eq_ker, respV_eq_ker]
  rw [piProc_eq_ker, xProc_eq_ker, vProc_eq_ker]
  exact ⟨kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 _ _ _ hT,
    kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 _ _ _ hT,
    kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 _ _ _ hT⟩

/-- **Cochrane (2023), A1 §1.13, p. 581, and §5.7.1: forecasts are moving averages of past
shocks weighted by the responses.** For `0 ≤ t ≤ T`, a.s.
`E_tπ_T = ∫_0^t R_π(T − u) dW_u`, `E_tx_T = ∫_0^t R_x(T − u) dW_u`,
`E_tv_T = ∫_0^t R_v(T − u) dW_u`. -/
theorem condExp_responses (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[piProc r σ κ ρ σi σs W T | 𝓕 t]
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respPi r σ κ ρ σi σs (T - u)) 0 t ∧
      P[xProc r σ κ ρ σi σs W T | 𝓕 t]
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respX r σ κ ρ σi σs (T - u)) 0 t ∧
      P[vProc r σ κ ρ σs W T | 𝓕 t]
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respV r σ κ ρ σs (T - u)) 0 t := by
  simp only [respX_eq_ker, respV_eq_ker]
  rw [piProc_eq_ker, xProc_eq_ker, vProc_eq_ker]
  exact ⟨condExp_kerProc_itoInt hB hW h𝓕 hcont hW0 _ _ _ ht htT,
    condExp_kerProc_itoInt hB hW h𝓕 hcont hW0 _ _ _ ht htT,
    condExp_kerProc_itoInt hB hW h𝓕 hcont hW0 _ _ _ ht htT⟩

/-- **Cochrane (2023), §5.7, p. 168 (news): the response of the forecast to `dW`.** For
`0 ≤ t ≤ t' ≤ T`, a.s. `E_{t'}π_T − E_tπ_T = ∫_t^{t'} R_π(T − u) dW_u`, and likewise for `x`
and `v`. -/
theorem news_responses (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {t t' T : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') (ht'T : t' ≤ T) :
    (fun ω => P[piProc r σ κ ρ σi σs W T | 𝓕 t'] ω - P[piProc r σ κ ρ σi σs W T | 𝓕 t] ω)
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respPi r σ κ ρ σi σs (T - u)) t t' ∧
      (fun ω => P[xProc r σ κ ρ σi σs W T | 𝓕 t'] ω - P[xProc r σ κ ρ σi σs W T | 𝓕 t] ω)
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respX r σ κ ρ σi σs (T - u)) t t' ∧
      (fun ω => P[vProc r σ κ ρ σs W T | 𝓕 t'] ω - P[vProc r σ κ ρ σs W T | 𝓕 t] ω)
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => respV r σ κ ρ σs (T - u)) t t' := by
  simp only [respX_eq_ker, respV_eq_ker]
  rw [piProc_eq_ker, xProc_eq_ker, vProc_eq_ker]
  exact ⟨news_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht htt' ht'T,
    news_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht htt' ht'T,
    news_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht htt' ht'T⟩

/-! ### The book's `E_t d` equations -/

/-- Cochrane (2023), §5.7, p. 164 (`E_t dW = 0`): for `0 ≤ a ≤ b`, `E_a[W_b − W_a] = 0` a.s.
Generalises `TidyR7BrownianTools.condExp_increment` to any admissible filtration. -/
theorem condExp_incr (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P[incr W a b | 𝓕 a] =ᵐ[P] 0 := by
  have hI : ItoIntegrand P 𝓕 (fun _ _ => (1 : ℝ)) a b 1 :=
    itoIntegrand_deterministic continuousOn_const fun _ _ => by simp
  refine (condExp_congr_ae (itoInt_one hB hW h𝓕 ha hab).symm).trans ?_
  refine (condExp_itoInt hB hW h𝓕 ha le_rfl hab hI).trans ?_
  rw [itoInt_of_le le_rfl]

/-- Cochrane (2023), §5.7, p. 163 ("I add the expectational shock `dδx = dx − E_t dx`"): if
`X = D + c(W_b − W_a)` on every path and `X` is integrable, then `E_a X = E_a D` a.s. -/
theorem condExp_drift (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {X D : Ω → ℝ}
    (hX : Integrable X P) (h : ∀ ω, X ω = D ω + c * incr W a b ω) :
    P[X | 𝓕 a] =ᵐ[P] P[D | 𝓕 a] := by
  have hi : Integrable (fun ω => c * incr W a b ω) P := (integrable_incr hB a b).const_mul c
  have hD : Integrable D P := by
    have : D = fun ω => X ω - c * incr W a b ω := by
      funext ω
      rw [h ω]
      ring
    rw [this]
    exact hX.sub hi
  have hXD : X = D + fun ω => c * incr W a b ω := by
    funext ω
    exact h ω
  rw [hXD]
  have h2 : P[fun ω => c * incr W a b ω | 𝓕 a] =ᵐ[P] 0 := by
    have := condExp_smul (μ := P) c (incr W a b) (𝓕 a)
    filter_upwards [this, condExp_incr hB hW h𝓕 ha hab] with ω h1 h2
    have e : (fun ω => c * incr W a b ω) = c • incr W a b := rfl
    rw [e, h1]
    simp [h2]
  filter_upwards [condExp_add hD hi (𝓕 a), h2] with ω h1 h3
  rw [h1, Pi.add_apply, h3]
  simp

/-- Cochrane (2023), (5.85)–(5.86), p. 162, path by path in process form: the expectational
errors are `x_T − x_t − ∫_t^T σ(i − π) = R_x(0)(W_T − W_t)` and
`π_T − π_t − ∫_t^T (ρπ − κx) = R_π(0)(W_T − W_t)`, i.e. `dδx = R_x(0)dW`, `dδπ = R_π(0)dW`. -/
theorem expectational_errors (hκ : 0 < κ) (hσ : 0 < σ) (hcont : ∀ ω, Continuous fun t => W t ω)
    (t T : ℝ) (ω : Ω) :
    xProc r σ κ ρ σi σs W T ω - xProc r σ κ ρ σi σs W t ω
        - (∫ u in t..T, σ * (iProc σi W u ω - piProc r σ κ ρ σi σs W u ω))
        = respX r σ κ ρ σi σs 0 * incr W t T ω ∧
      piProc r σ κ ρ σi σs W T ω - piProc r σ κ ρ σi σs W t ω
        - (∫ u in t..T, (ρ * piProc r σ κ ρ σi σs W u ω - κ * xProc r σ κ ρ σi σs W u ω))
        = respPi r σ κ ρ σi σs 0 * incr W t T ω := by
  have hw := continuous_bmReal (hcont ω)
  constructor
  · have := x_incr (r := r) (ρ := ρ) (σi := σi) (σs := σs) hκ hσ hw t T
    simp only [xProc, iProc, piProc, incr]
    linarith
  · have := pi_incr (r := r) (σ := σ) (ρ := ρ) (σi := σi) (σs := σs) hκ hw t T
    simp only [xProc, piProc, incr]
    linarith

/-- **Cochrane (2023), (5.85)–(5.90), pp. 162–163: the book's equations in `E_t d` form.**
For `r ≠ 0`, `κ, σ > 0` and `0 ≤ t ≤ T`, almost surely
`E_t[x_T − x_t] = E_t[∫_t^T σ(i − π)]` (`E_t dx = σ(i − π)dt`),
`E_t[π_T − π_t] = E_t[∫_t^T (ρπ − κx)]` (`E_t dπ = (ρπ − κx)dt`),
`E_t[i_T − i_t] = 0`, `E_t[s̃_T − s̃_t] = 0` (`E_t dε = 0`); and on every path
`v_T − v_t = ∫_t^T (rv + i − π − s̃)` (debt has no expectational error) and
`p_T − p_t = ∫_t^T π` (`dp = π dt`: the price level is predictable). -/
theorem ito_book_equations (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : r ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) :
    P[fun ω => xProc r σ κ ρ σi σs W T ω - xProc r σ κ ρ σi σs W t ω | 𝓕 t]
        =ᵐ[P] P[fun ω => ∫ u in t..T, σ * (iProc σi W u ω - piProc r σ κ ρ σi σs W u ω) | 𝓕 t]
      ∧ P[fun ω => piProc r σ κ ρ σi σs W T ω - piProc r σ κ ρ σi σs W t ω | 𝓕 t]
        =ᵐ[P] P[fun ω => ∫ u in t..T,
          (ρ * piProc r σ κ ρ σi σs W u ω - κ * xProc r σ κ ρ σi σs W u ω) | 𝓕 t]
      ∧ P[fun ω => iProc σi W T ω - iProc σi W t ω | 𝓕 t] =ᵐ[P] 0
      ∧ P[fun ω => sProc σs W T ω - sProc σs W t ω | 𝓕 t] =ᵐ[P] 0
      ∧ (∀ ω, vProc r σ κ ρ σs W T ω - vProc r σ κ ρ σs W t ω
          = ∫ u in t..T, (r * vProc r σ κ ρ σs W u ω + iProc σi W u ω
            - piProc r σ κ ρ σi σs W u ω - sProc σs W u ω))
      ∧ (∀ ω, pProc r σ κ ρ σi σs W T ω - pProc r σ κ ρ σi σs W t ω
          = ∫ u in t..T, piProc r σ κ ρ σi σs W u ω) := by
  have hT : 0 ≤ T := ht.trans htT
  have hxi : ∀ τ, 0 ≤ τ → Integrable (xProc r σ κ ρ σi σs W τ) P := fun τ hτ => by
    rw [xProc_eq_ker]
    exact integrable_kerProc hB hW h𝓕 hcont hW0 _ _ _ hτ
  have hpii : ∀ τ, 0 ≤ τ → Integrable (piProc r σ κ ρ σi σs W τ) P := fun τ hτ => by
    rw [piProc_eq_ker]
    exact integrable_kerProc hB hW h𝓕 hcont hW0 _ _ _ hτ
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hshock : ∀ c : ℝ, P[fun ω => c * bmReal W T ω - c * bmReal W t ω | 𝓕 t] =ᵐ[P] 0 := by
    intro c
    have hX : Integrable (fun ω => c * bmReal W T ω - c * bmReal W t ω) P := by
      have e : (fun ω => c * bmReal W T ω - c * bmReal W t ω) = fun ω => c * incr W t T ω := by
        funext ω
        simp only [incr]
        ring
      rw [e]
      exact (integrable_incr hB t T).const_mul c
    have h := condExp_drift (c := c) (D := fun _ => 0) hB hW h𝓕 ht htT hX
      (fun ω => by simp only [incr]; ring)
    refine h.trans ?_
    rw [condExp_const (𝓕.le t)]
    rfl
  refine ⟨?_, ?_, hshock σi, hshock σs, fun ω => ?_, fun ω => ?_⟩
  · refine condExp_drift (c := respX r σ κ ρ σi σs 0) hB hW h𝓕 ht htT
      ((hxi T hT).sub (hxi t ht)) fun ω => ?_
    have := (expectational_errors (r := r) (ρ := ρ) (σi := σi) (σs := σs) hκ hσ hcont t T ω).1
    linarith
  · refine condExp_drift (c := respPi r σ κ ρ σi σs 0) hB hW h𝓕 ht htT
      ((hpii T hT).sub (hpii t ht)) fun ω => ?_
    have := (expectational_errors (r := r) (ρ := ρ) (σi := σi) (σs := σs) hκ hσ hcont t T ω).2
    linarith
  · exact v_incr hr (continuous_bmReal (hcont ω)) t T
  · have hc := continuous_piPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := σi) (σs := σs)
      (continuous_bmReal (hcont ω))
    simp only [pProc, pPath, piProc]
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 T)
      (hc.intervalIntegrable 0 t)]

/-! ### Valuation and transversality under uncertainty -/

/-- Cochrane (2023), (5.95), p. 165: the present value of surpluses and real-rate payments from
`t` to `T`, `∫_t^T e^{−r(τ−t)}[s̃_τ − (i_τ − π_τ)] dτ`, on the Brownian path. -/
noncomputable def pvProc (r σ κ ρ σi σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  ∫ τ in t..T, exp (-(r * (τ - t))) *
    (sProc σs W τ ω - (iProc σi W τ ω - piProc r σ κ ρ σi σs W τ ω))

/-- **Cochrane (2023), (5.95), p. 165, path by path and over a finite horizon**:
`∫_t^T e^{−r(τ−t)}[s̃ − (i − π)]dτ = v_t − e^{−r(T−t)}v_T` on every path. -/
theorem pv_identity (hr : r ≠ 0) (hcont : ∀ ω, Continuous fun t => W t ω) (t T : ℝ) (ω : Ω) :
    pvProc r σ κ ρ σi σs W t T ω
      = vProc r σ κ ρ σs W t ω - exp (-(r * (T - t))) * vProc r σ κ ρ σs W T ω := by
  have hw := continuous_bmReal (hcont ω)
  set w := fun u => bmReal W u ω
  have hF : ∀ τ, HasDerivAt (fun τ => -(exp (-(r * (τ - t))) * vPath r σ κ ρ σs w τ))
      (exp (-(r * (τ - t))) * (sPath σs w τ - (iPath σi w τ - piPath r σ κ ρ σi σs w τ))) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ => -(r * (τ - t))) (-r) τ := by
      have := (((hasDerivAt_id' τ).sub_const t).const_mul r).neg
      exact this.congr_deriv (by ring)
    have hE : HasDerivAt (fun τ => exp (-(r * (τ - t)))) (exp (-(r * (τ - t))) * -r) τ :=
      h1.exp
    have hv := v_hasDerivAt (σi := σi) (σ := σ) (κ := κ) (ρ := ρ) (σs := σs) hr hw τ
    exact (hE.mul hv).neg.congr_deriv (by ring)
  have hc : Continuous fun τ =>
      exp (-(r * (τ - t))) * (sPath σs w τ - (iPath σi w τ - piPath r σ κ ρ σi σs w τ)) := by
    have := continuous_piPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := σi) (σs := σs) hw
    simp only [sPath, iPath]
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
    (hc.intervalIntegrable t T)
  simp only [pvProc, sProc, iProc, piProc, vProc]
  rw [h]
  simp only [sub_self, mul_zero, neg_zero, exp_zero, one_mul]
  ring

/-- **Cochrane (2023), (5.95), p. 165, conditional on date-`t` information**: for
`0 ≤ t ≤ T`, `E_t∫_t^T e^{−r(τ−t)}[s̃ − (i − π)]dτ = v_t − e^{−r(T−t)}E_t v_T` a.s. (the value
of debt is known at `t`). -/
theorem condExp_pv (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : r ≠ 0) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[pvProc r σ κ ρ σi σs W t T | 𝓕 t] =ᵐ[P] fun ω => vProc r σ κ ρ σs W t ω
      - exp (-(r * (T - t))) * P[vProc r σ κ ρ σs W T | 𝓕 t] ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hvi : ∀ τ, 0 ≤ τ → Integrable (vProc r σ κ ρ σs W τ) P := fun τ hτ => by
    rw [vProc_eq_ker]
    exact integrable_kerProc hB hW h𝓕 hcont hW0 _ _ _ hτ
  have hvm : AEStronglyMeasurable[𝓕 t] (vProc r σ κ ρ σs W t) P := by
    rw [vProc_eq_ker]
    exact aesm_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht
  have he : pvProc r σ κ ρ σi σs W t T = vProc r σ κ ρ σs W t
      - (exp (-(r * (T - t)))) • vProc r σ κ ρ σs W T := by
    funext ω
    rw [pv_identity hr hcont t T ω]
    rfl
  rw [he]
  filter_upwards [condExp_sub (hvi t ht) ((hvi T (ht.trans htT)).smul (exp (-(r * (T - t)))))
    (𝓕 t), condExp_of_aestronglyMeasurable' (𝓕.le t) hvm (hvi t ht),
    condExp_smul (μ := P) (exp (-(r * (T - t)))) (vProc r σ κ ρ σs W T) (𝓕 t)]
    with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  rfl

/-- Cochrane (2023), §5.7.1, p. 165: the debt response is bounded, `R_v(τ)² ≤ (σ_s/r)²` for
`τ ≥ 0`. -/
theorem respV_sq_le (hκ : 0 < κ) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    respV r σ κ ρ σs τ ^ 2 ≤ (σs / r) ^ 2 := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have e1 : exp (-(lam2 ρ κ σ * τ)) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have e0 : 0 < exp (-(lam2 ρ κ σ * τ)) := exp_pos _
  rw [respV, mul_pow]
  have : (1 - exp (-(lam2 ρ κ σ * τ))) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (σs / r)]

/-- Cochrane (2023), (5.95), p. 165: `E|v_T| ≤ 1 + T(σ_s/r)²` for `T ≥ 0`. -/
theorem integral_abs_vProc_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, |vProc r σ κ ρ σs W T ω| ∂P ≤ 1 + T * (σs / r) ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : MemLp (vProc r σ κ ρ σs W T) 2 P := by
    rw [vProc_eq_ker]
    exact memLp_kerProc hB hW h𝓕 hcont hW0 _ _ _ hT
  have hsq : Integrable (fun ω => vProc r σ κ ρ σs W T ω ^ 2) P := hm.integrable_sq
  have h1 : ∫ ω, |vProc r σ κ ρ σs W T ω| ∂P ≤ ∫ ω, (1 + vProc r σ κ ρ σs W T ω ^ 2) ∂P :=
    integral_mono (hm.integrable one_le_two).abs ((integrable_const 1).add hsq) fun ω => by
      have := abs_nonneg (vProc r σ κ ρ σs W T ω)
      have := sq_abs (vProc r σ κ ρ σs W T ω)
      nlinarith
  have h2 : ∫ ω, vProc r σ κ ρ σs W T ω ^ 2 ∂P ≤ T * (σs / r) ^ 2 := by
    rw [vProc_eq_ker, integral_kerProc_sq hB hW h𝓕 hcont hW0 _ _ _ hT]
    have : ∫ u in (0 : ℝ)..T, kerFn (σs / r) (-(σs / r)) (lam2 ρ κ σ) (T - u) ^ 2
        ≤ ∫ u in (0 : ℝ)..T, (σs / r) ^ 2 := by
      refine intervalIntegral.integral_mono_on hT ?_ intervalIntegrable_const fun u hu => ?_
      · exact ((continuous_kerFn _ _ _ T).pow 2).intervalIntegrable 0 T
      · rw [← respV_eq_ker]
        exact respV_sq_le hκ hσ (by linarith [hu.2])
    simpa using this
  rw [integral_add (integrable_const 1) hsq] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  linarith

/-- Cochrane (2023), (5.95), p. 165: `e^{−r(T−t)}(1 + T K) → 0` as `T → ∞` for `r > 0`. -/
theorem tendsto_exp_mul_affine (hr : 0 < r) (t K : ℝ) :
    Tendsto (fun T => exp (-(r * (T - t))) * (1 + T * K)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T => exp (-(r * T))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
  have h2 : Tendsto (fun T => (r * T) ^ 1 * exp (-(r * T))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop hr)
  have h3 := (h1.add (h2.const_mul (K / r))).const_mul (exp (r * t))
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun T => ?_
  rw [show -(r * (T - t)) = r * t + -(r * T) by ring, exp_add]
  field_simp

/-- **Cochrane (2023), §5.7.1, p. 165: the transversality condition under uncertainty.** For
`r > 0` and `t ≥ 0`, `E_t[e^{−r(T−t)}v_T] → 0` in `L¹` as `T → ∞`.
The stochastic analogue of `CTSimple.tvc_of_bounded`. -/
theorem tvc_L1 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) (t : ℝ) :
    Tendsto (fun T => ∫ ω, |P[fun ω => exp (-(r * (T - t))) * vProc r σ κ ρ σs W T ω | 𝓕 t] ω|
      ∂P) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
    ?_ (tendsto_exp_mul_affine hr t ((σs / r) ^ 2))
  filter_upwards [eventually_ge_atTop 0] with T hT
  refine (integral_abs_condExp_le _).trans ?_
  have e : (fun ω => |exp (-(r * (T - t))) * vProc r σ κ ρ σs W T ω|)
      = fun ω => exp (-(r * (T - t))) * |vProc r σ κ ρ σs W T ω| := by
    funext ω
    rw [abs_mul, abs_of_pos (exp_pos _)]
  rw [e, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_abs_vProc_le hB hW h𝓕 hcont hW0 hκ hσ hT)
    (exp_pos _).le

/-- **Cochrane (2023), (5.95), p. 165, under uncertainty: the valuation equation at every
date.** For `r > 0` and `t ≥ 0`,
`E_t∫_t^T e^{−r(τ−t)}[s̃_τ − (i_τ − π_τ)]dτ → v_t` in `L¹` as `T → ∞`: the real value of debt is
the conditional present value of surpluses discounted at the real interest rate.
The stochastic analogue of `CTSimple.ct_value_at`. -/
theorem valuation_L1 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |P[pvProc r σ κ ρ σi σs W t T | 𝓕 t] ω - vProc r σ κ ρ σs W t ω|
      ∂P) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
    ?_ (tendsto_exp_mul_affine hr t ((σs / r) ^ 2))
  filter_upwards [eventually_ge_atTop t] with T hT
  have hcond := condExp_pv (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := σi) (σs := σs)
    hB hW h𝓕 hcont hW0 hr.ne' ht hT
  have e : ∫ ω, |P[pvProc r σ κ ρ σi σs W t T | 𝓕 t] ω - vProc r σ κ ρ σs W t ω| ∂P
      = exp (-(r * (T - t))) * ∫ ω, |P[vProc r σ κ ρ σs W T | 𝓕 t] ω| ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    rw [hω, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (exp_pos _)]
  rw [e]
  exact mul_le_mul_of_nonneg_left ((integral_abs_condExp_le _).trans
    (integral_abs_vProc_le hB hW h𝓕 hcont hW0 hκ hσ (ht.trans hT))) (exp_pos _).le

/-! ### No covariation correction -/

/-- Cochrane (2023), §5.7, p. 163 (tool): a `C¹` path is of bounded variation on `[a, b]`.
From Mathlib `LipschitzOnWith.locallyBoundedVariationOn`. -/
theorem bv_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    {a b : ℝ} (hab : a ≤ b) : BoundedVariationOn f (Set.Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    hf'.continuousOn
  have hL : LipschitzOnWith (Real.toNNReal C) f (Set.Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (hf x).hasDerivWithinAt) fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact (hC x hx).trans (Real.le_coe_toNNReal C)
  have := hL.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rwa [Set.inter_self] at this

/-- **Cochrane (2023), (5.88), p. 163 ("using the absence of price-level jumps or diffusion
terms"): the value of debt has zero covariation with `W`.** On every path and every `[a, b]`,
`Σ Δv_i ΔW_i → 0` along any partitions with mesh `→ 0`.
An instance of `TidyR7StieltjesCalculus.tendsto_crossSum_zero_of_continuousOn`. -/
theorem crossSum_v_tendsto_zero (hr : r ≠ 0) (hcont : ∀ ω, Continuous fun t => W t ω) (ω : Ω)
    {a b : ℝ} (ps : ℕ → Partition a b) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (ps k) (fun u => bmReal W u ω)
      (fun u => vProc r σ κ ρ σs W u ω)) atTop (𝓝 0) := by
  have hw := continuous_bmReal (hcont ω)
  have hd := fun x => v_hasDerivAt (σi := 0) (σ := σ) (κ := κ) (ρ := ρ) (σs := σs) hr hw x
  have hc : Continuous fun x => r * vPath r σ κ ρ σs (fun u => bmReal W u ω) x
      + iPath 0 (fun u => bmReal W u ω) x - piPath r σ κ ρ 0 σs (fun u => bmReal W u ω) x
      - sPath σs (fun u => bmReal W u ω) x := by
    have := continuous_vPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σs := σs) hw
    have := continuous_piPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := 0) (σs := σs) hw
    simp only [iPath, sPath]
    fun_prop
  exact tendsto_crossSum_zero_of_continuousOn hw.continuousOn
    (bv_of_hasDerivAt hd hc (a_le_b (ps 0))) ps hps

/-- **Cochrane (2023), (5.87), p. 163 ("the price level is continuous, differentiable, and hence
completely predictable"): the price level has zero covariation with `W`.**
An instance of `TidyR7StieltjesCalculus.tendsto_crossSum_zero_of_continuousOn`. -/
theorem crossSum_p_tendsto_zero (hcont : ∀ ω, Continuous fun t => W t ω) (ω : Ω)
    {a b : ℝ} (ps : ℕ → Partition a b) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (ps k) (fun u => bmReal W u ω)
      (fun u => pProc r σ κ ρ σi σs W u ω)) atTop (𝓝 0) := by
  have hw := continuous_bmReal (hcont ω)
  exact tendsto_crossSum_zero_of_continuousOn hw.continuousOn
    (bv_of_hasDerivAt (fun x => p_hasDerivAt hw x) (continuous_piPath hw) (a_le_b (ps 0)))
    ps hps

/-! ### Non-vacuity on the constructed Brownian motion -/

/-- **Cochrane (2023), §5.7, pp. 162–166 (non-vacuity)**: on the constructed motion
`bmPath` (on `gaussSeq`, natural filtration), the responses, the `E_t d` equations and the
transversality condition all hold. -/
theorem bmPath_stoch_ct (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) :
    (piProc r σ κ ρ σi σs bmPath T =ᵐ[gaussSeq] itoInt gaussSeq
      (bmFiltrationReal bmPath measurable_bmPath) bmPath
        (fun u _ => respPi r σ κ ρ σi σs (T - u)) 0 T) ∧
    (gaussSeq[fun ω => xProc r σ κ ρ σi σs bmPath T ω - xProc r σ κ ρ σi σs bmPath t ω
        | bmFiltrationReal bmPath measurable_bmPath t]
      =ᵐ[gaussSeq] gaussSeq[fun ω => ∫ u in t..T,
        σ * (iProc σi bmPath u ω - piProc r σ κ ρ σi σs bmPath u ω)
          | bmFiltrationReal bmPath measurable_bmPath t]) ∧
    Tendsto (fun T => ∫ ω, |gaussSeq[pvProc r σ κ ρ σi σs bmPath t T
        | bmFiltrationReal bmPath measurable_bmPath t] ω - vProc r σ κ ρ σs bmPath t ω|
      ∂gaussSeq) atTop (𝓝 0) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  exact ⟨(responses_ito hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero
      (ht.trans htT)).1,
    (ito_book_equations hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero hr.ne' hκ hσ ht
      htT).1,
    valuation_L1 hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero hr hκ hσ ht⟩

/-- **Cochrane (2023), §5.7.1, p. 166 (non-vacuity: the debt response is genuinely random)**:
on `bmPath`, for `σ_s ≠ 0`, `r ≠ 0` and `T > 0`, `E[v_T²] = ∫_0^T R_v(τ)² dτ > 0`. -/
theorem bmPath_v_nondegenerate (hr : r ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ) (hs : σs ≠ 0) {T : ℝ}
    (hT : 0 < T) : 0 < ∫ ω, vProc r σ κ ρ σs bmPath T ω ^ 2 ∂gaussSeq := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  rw [vProc_eq_ker, integral_kerProc_sq hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero
    _ _ _ hT.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuous_kerFn _ _ _ T).pow 2).intervalIntegrable 0 T) (fun u hu => ?_) hT
  rw [← respV_eq_ker, respV]
  have hlt : exp (-(lam2 ρ κ σ * (T - u))) < 1 :=
    Real.exp_lt_one_iff.2 (by nlinarith [hu.2])
  have : σs / r * (1 - exp (-(lam2 ρ κ σ * (T - u)))) ≠ 0 :=
    mul_ne_zero (div_ne_zero hs hr) (by linarith)
  positivity

end Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian
