/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR8StochKernel
import StickyPriceFiscal.CTSurplus

/-!
# S-shaped surpluses with a Brownian surplus shock

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7.2, pp. 167–169,
(5.97)–(5.104).

The surplus process (5.97)–(5.99), `s = αv* + u`, `dv* = (rv* − s)dt + β_s dε`,
`du = −ηu dt + dε` (the corrected (5.98)–(5.99), survey E45, E48, as in `CTSurplus`), is solved
here with a diffusive shock `dε = σ_s dW`. With `a = α − r` and the OU noises `Y^η`, `Y^a`
(`TidyR7StochCTPath.ouNoise`) the solution on every continuous path is

`u = σ_sY^η`, `v* = σ_s(β_sY^a − (Y^η − Y^a)/(a − η))`,
`s = σ_s((η+r)/(η+r−α) Y^η − (α/(η+r−α) − αβ_s) Y^a)` (5.101),

and the flexible-price (log) price level of p. 167 is `p* = −β_sσ_sW`.

## Main results

* `u_incr`, **`vstar_incr`** ((5.98)–(5.99) on every path: `dv* = (rv* − s)dt + β_sσ_s dW`),
  `surplus_5_101` ((5.101) on every path).
* **`responses_surplus`**: a.s. `s_T = ∫_0^T σ_s s^{IRF}(T − u) dW_u`,
  `v*_T = ∫_0^T σ_s v*^{IRF}(T − u) dW_u`, `u_T = ∫_0^T σ_s e^{−η(T−u)} dW_u`
  (`CTSurplus.surplusIRF`, `CTSurplus.vstarIRF`): the moving average (5.101) with past shocks
  `dε_{t−τ}` (E46), and the s-shape of `CTSurplus.ct_s_shape` is the shape of the `dW` loading.
* Hansen–Sargent under uncertainty: `pv_identity_surplus` (every path),
  `condExp_pv_surplus`, **`valuation_surplus_L1`** (`E_t∫_t^T e^{−r(τ−t)}s_τ dτ → v*_t` in `L¹`):
  `v*` is the present value of surpluses at every date.
* **The innovation in the present value is `L(r)σ_s dW = +β_sσ_s dW`**:
  `innovation_eq_L_r` (on every path) and `bracket_vstar_W` (`[v*, W]_t = β_sσ_s t` a.s.);
  `innovation_printed_iff` (the printed `L(r) = −β_s`, E47, would make it `−β_sσ_s`, which
  holds only if `β_sσ_s = 0`).
* **The price-level diffusion (p. 168)**: `pstar_debt` (`dv* = (rv* − s)dt − dp*`),
  `condExp_pstar_incr` (`E_t dp* = 0`), **`bracket_pstar_W`** (`[p*, W]_t = −β_sσ_s t` a.s.,
  i.e. `dP/P = −β_s dε` as on p. 167). The printed `−Δ(1/P)/(1/P) = β_s dε_s` has the wrong
  sign: `−Δ(1/P)/(1/P)` is the innovation of `log P`, which is `−β_s dε` (`pstar_loading`).
* No covariation correction in the linearised model (`bracket_vstar_pstar`: the bracket of
  the two diffusive states is the product of their loadings, `−(β_sσ_s)²t`, and enters nothing in
  (5.97)–(5.104)).
* Non-vacuity on `bmPath`: `bmPath_surplus`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR8StochCTSurplus

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7StieltjesSums Cochrane.StickyPriceFiscal.TidyR7BrownianTools
open Cochrane.StickyPriceFiscal.TidyR7BrownianQV Cochrane.StickyPriceFiscal.TidyR7ItoIntegral
open Cochrane.StickyPriceFiscal.TidyR7ItoBridge Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open Cochrane.StickyPriceFiscal.TidyR7StochCTPath Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian
open Cochrane.StickyPriceFiscal.TidyR8StochKernel Cochrane.StickyPriceFiscal.CTSurplus
open Cochrane.StickyPriceFiscal.TidyR7BrownianSchauder
open scoped ENNReal NNReal

/-! ### The solution on a path -/

/-- Cochrane (2023), (5.99), p. 167: the AR(1) surplus disturbance `u = σ_sY^η`
(`du = −ηu dt + σ_s dw`). -/
noncomputable def uPath (σs η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := σs * ouNoise η w t

/-- Cochrane (2023), (5.98), p. 167: the state variable
`v* = σ_s(β_sY^{α−r} − (Y^η − Y^{α−r})/(α − r − η))`. -/
noncomputable def vsPath (r α η βs σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  σs * (βs * ouNoise (α - r) w t - (ouNoise η w t - ouNoise (α - r) w t) / (α - r - η))

/-- Cochrane (2023), (5.97), p. 167: the surplus `s = αv* + u`. -/
noncomputable def ssPath (r α η βs σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  α * vsPath r α η βs σs w t + uPath σs η w t

/-- Cochrane (2023), p. 167: the flexible-price log price level `p* = −β_sσ_s w`
("allowing a price level diffusion or jump `dP/P = −β_s dε_s`"). -/
def pstarPath (βs σs : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := -(βs * σs * w t)

variable {r α η βs σs : ℝ} {w : ℝ → ℝ}

/-- **Cochrane (2023), (5.99), p. 167, on a path**: `u_b − u_a = σ_s(w_b − w_a) − η∫_a^b u`. -/
theorem u_incr (hw : Continuous w) (a b : ℝ) :
    uPath σs η w b - uPath σs η w a = σs * (w b - w a) - η * ∫ u in a..b, uPath σs η w u := by
  have h := ouNoise_incr η hw a b
  simp only [uPath]
  rw [intervalIntegral.integral_const_mul]
  linear_combination σs * h

/-- Cochrane (2023), (5.98), p. 167: the `C¹` part `v* − β_sσ_s w` has derivative `rv* − s`. -/
theorem vs_sub_hasDerivAt (h : η + r - α ≠ 0) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun u => vsPath r α η βs σs w u - βs * σs * w u)
      (r * vsPath r α η βs σs w t - ssPath r α η βs σs w t) t := by
  have hd : α - r - η ≠ 0 := fun h0 => h (by linarith)
  have h1 := hasDerivAt_sub_ouNoise (α - r) hw t
  have h2 := hasDerivAt_sub_ouNoise η hw t
  have hf : (fun u => vsPath r α η βs σs w u - βs * σs * w u) = fun u =>
      σs * (-βs * (w u - ouNoise (α - r) w u)
        - ((w u - ouNoise (α - r) w u) - (w u - ouNoise η w u)) / (α - r - η)) := by
    funext u
    simp only [vsPath]
    ring
  rw [hf]
  refine ((HasDerivAt.sub (h1.const_mul (-βs)) ((HasDerivAt.sub h1 h2).div_const
    (α - r - η))).const_mul σs).congr_deriv ?_
  simp only [ssPath, vsPath, uPath]
  field_simp
  ring

/-- Cochrane (2023), (5.97)–(5.98), p. 167: `v*` and `s` are continuous. -/
theorem continuous_vs_ss (hw : Continuous w) :
    Continuous (vsPath r α η βs σs w) ∧ Continuous (ssPath r α η βs σs w) := by
  have := continuous_ouNoise η hw
  have := continuous_ouNoise (α - r) hw
  refine ⟨?_, ?_⟩
  · unfold vsPath
    fun_prop
  · unfold ssPath vsPath uPath
    fun_prop

/-- **Cochrane (2023), (5.98), p. 167, on a path**: over every `[a, b]`,
`v*_b − v*_a = ∫_a^b (rv* − s) + β_sσ_s(w_b − w_a)`: the state variable is the value of debt of
the flexible-price model, with innovation `β_sσ_s dw`. -/
theorem vstar_incr (h : η + r - α ≠ 0) (hw : Continuous w) (a b : ℝ) :
    vsPath r α η βs σs w b - vsPath r α η βs σs w a
      = (∫ u in a..b, (r * vsPath r α η βs σs w u - ssPath r α η βs σs w u))
        + βs * σs * (w b - w a) := by
  obtain ⟨c1, c2⟩ := continuous_vs_ss (r := r) (α := α) (η := η) (βs := βs) (σs := σs) hw
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => vs_sub_hasDerivAt (βs := βs) (σs := σs) h hw x)
    (((c1.const_mul r).sub c2).intervalIntegrable a b)
  rw [hF]
  ring

/-- **Cochrane (2023), (5.101), p. 168, on a path**:
`s = σ_s((η+r)/(η+r−α) Y^η − (α/(η+r−α) − αβ_s) Y^{α−r})`. -/
theorem surplus_5_101 (h : η + r - α ≠ 0) (t : ℝ) :
    ssPath r α η βs σs w t = σs * ((η + r) / (η + r - α) * ouNoise η w t
      - (α / (η + r - α) - α * βs) * ouNoise (α - r) w t) := by
  have hd : α - r - η ≠ 0 := fun h0 => h (by linarith)
  simp only [ssPath, vsPath, uPath]
  field_simp
  ring

/-! ### Processes and Wiener integrals -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-- Cochrane (2023), (5.98), p. 167: `v*` as a process on the Brownian path. -/
noncomputable def vsProc (r α η βs σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  vsPath r α η βs σs (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.97), p. 167: the surplus as a process. -/
noncomputable def ssProc (r α η βs σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ssPath r α η βs σs (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.99), p. 167: the disturbance as a process. -/
noncomputable def uProc (σs η : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  uPath σs η (fun u => bmReal W u ω) t

/-- Cochrane (2023), p. 167: the flexible-price log price level as a process. -/
def pstarProc (βs σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  pstarPath βs σs (fun u => bmReal W u ω) t

/-- Cochrane (2023), (5.98), p. 167: `v*` is the two-mode process with loadings
`σ_s/(η+r−α)` on `Y^η` and `σ_s(β_s − 1/(η+r−α))` on `Y^{α−r}`. -/
theorem vsProc_eq_ker2 (h : η + r - α ≠ 0) : vsProc r α η βs σs W = fun t =>
    ker2Proc W 0 (σs / (η + r - α)) η (σs * (βs - 1 / (η + r - α))) (α - r) t := by
  have hd : α - r - η ≠ 0 := fun h0 => h (by linarith)
  funext t ω
  rw [ker2Proc_eq]
  simp only [vsProc, vsPath]
  field_simp
  ring

/-- Cochrane (2023), (5.101), p. 168: the surplus is the two-mode process with loadings
`σ_s(η+r)/(η+r−α)` on `Y^η` and `−σ_s(α/(η+r−α) − αβ_s)` on `Y^{α−r}`. -/
theorem ssProc_eq_ker2 (h : η + r - α ≠ 0) : ssProc r α η βs σs W = fun t =>
    ker2Proc W 0 (σs * ((η + r) / (η + r - α))) η (-(σs * (α / (η + r - α) - α * βs)))
      (α - r) t := by
  funext t ω
  rw [ker2Proc_eq]
  simp only [ssProc]
  rw [surplus_5_101 h]
  ring

/-- Cochrane (2023), (5.98), p. 167: the kernel of `v*` is `σ_s v*^{IRF}`. -/
theorem ker2_vstar (h : η + r - α ≠ 0) (τ : ℝ) :
    ker2Fn 0 (σs / (η + r - α)) η (σs * (βs - 1 / (η + r - α))) (α - r) τ
      = σs * vstarIRF r α η βs τ := by
  simp only [ker2Fn, vstarIRF]
  field_simp
  ring

/-- Cochrane (2023), (5.101), p. 168: the kernel of `s` is `σ_s s^{IRF}`. -/
theorem ker2_surplus (τ : ℝ) :
    ker2Fn 0 (σs * ((η + r) / (η + r - α))) η (-(σs * (α / (η + r - α) - α * βs))) (α - r) τ
      = σs * surplusIRF r α η βs τ := by
  simp only [ker2Fn, surplusIRF]
  ring

/-- **Cochrane (2023), (5.99)–(5.101), pp. 167–168: the responses to a diffusive surplus
shock.** For `η + r − α ≠ 0` and `T ≥ 0`, a.s.
`s_T = ∫_0^T σ_s s^{IRF}(T − u) dW_u`, `v*_T = ∫_0^T σ_s v*^{IRF}(T − u) dW_u` and
`u_T = ∫_0^T σ_s e^{−η(T−u)} dW_u` (`u_t = ∫ e^{−ητ} dε_{t−τ}`, past shocks). -/
theorem responses_surplus (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (h : η + r - α ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ssProc r α η βs σs W T
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => σs * surplusIRF r α η βs (T - u)) 0 T ∧
      vsProc r α η βs σs W T
        =ᵐ[P] itoInt P 𝓕 W (fun u _ => σs * vstarIRF r α η βs (T - u)) 0 T ∧
      uProc σs η W T =ᵐ[P] itoInt P 𝓕 W (fun u _ => σs * exp (-(η * (T - u)))) 0 T := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ssProc_eq_ker2 h]
    simp only [← ker2_surplus (r := r) (α := α) (η := η) (βs := βs) (σs := σs)]
    exact ker2Proc_ae_eq_itoInt hB hW h𝓕 hcont hW0 _ _ _ _ _ hT
  · rw [vsProc_eq_ker2 h]
    simp only [← ker2_vstar (r := r) (α := α) (η := η) (βs := βs) (σs := σs) h]
    exact ker2Proc_ae_eq_itoInt hB hW h𝓕 hcont hW0 _ _ _ _ _ hT
  · have e : uProc σs η W = fun t => kerProc W 0 σs η t := by
      funext t ω
      simp [uProc, uPath, kerProc]
    have ek : (fun u (_ : Ω) => σs * exp (-(η * (T - u)))) = fun u _ => kerFn 0 σs η (T - u) := by
      funext u _
      simp [kerFn]
    rw [e, ek]
    exact kerProc_ae_eq_itoInt hB hW h𝓕 hcont hW0 0 σs η hT

/-! ### Hansen–Sargent: the present value of surpluses -/

/-- Cochrane (2023), p. 168: the present value of surpluses from `t` to `T`,
`∫_t^T e^{−r(τ−t)} s_τ dτ`, on the Brownian path. -/
noncomputable def pvSurplus (r α η βs σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  ∫ τ in t..T, exp (-(r * (τ - t))) * ssProc r α η βs σs W τ ω

/-- **Cochrane (2023), p. 168, on every path**: `∫_t^T e^{−r(τ−t)}s_τ dτ
= v*_t − e^{−r(T−t)}v*_T + β_sσ_s∫_t^T e^{−r(τ−t)} dW_τ` (by parts, `TidyR8StochKernel.expWiener`).
The diffusion of `v*` leaves a martingale term.
Parallels `TidyR7StochCTBrownian.pv_identity`. -/
theorem pv_identity_surplus (h : η + r - α ≠ 0) (hcont : ∀ ω, Continuous fun t => W t ω)
    (t T : ℝ) (ω : Ω) :
    pvSurplus r α η βs σs W t T ω = vsProc r α η βs σs W t ω
      - exp (-(r * (T - t))) * vsProc r α η βs σs W T ω + βs * σs * expWiener r W t T ω := by
  have hw := continuous_bmReal (hcont ω)
  set w := fun u => bmReal W u ω
  obtain ⟨c1, c2⟩ := continuous_vs_ss (r := r) (α := α) (η := η) (βs := βs) (σs := σs) hw
  have hB := discounted_byParts (fun x => vs_sub_hasDerivAt (βs := βs) (σs := σs) h hw x)
    ((c1.const_mul r).sub c2) hw r (βs * σs) t T
  have e1 : ∀ τ, vsPath r α η βs σs w τ - βs * σs * w τ + βs * σs * w τ
      = vsPath r α η βs σs w τ := fun τ => by ring
  simp only [e1] at hB
  have e2 : (fun τ => exp (-(r * (τ - t))) * (r * vsPath r α η βs σs w τ
      - (r * vsPath r α η βs σs w τ - ssPath r α η βs σs w τ)))
      = fun τ => exp (-(r * (τ - t))) * ssPath r α η βs σs w τ := by
    funext τ
    ring
  rw [e2] at hB
  simp only [pvSurplus, ssProc, vsProc, expWiener]
  rw [hB]

/-- Cochrane (2023), p. 168: the finite-horizon present value is integrable. -/
theorem integrable_pvSurplus (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (h : η + r - α ≠ 0) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    Integrable (pvSurplus r α η βs σs W t T) P := by
  have iv : ∀ τ, 0 ≤ τ → Integrable (vsProc r α η βs σs W τ) P := fun τ hτ => by
    rw [vsProc_eq_ker2 h]
    exact integrable_ker2Proc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ _ _ _ hτ
  have e : pvSurplus r α η βs σs W t T = fun ω => vsProc r α η βs σs W t ω
      - exp (-(r * (T - t))) * vsProc r α η βs σs W T ω + βs * σs * expWiener r W t T ω := by
    funext ω
    exact pv_identity_surplus h hcont t T ω
  rw [e]
  exact ((iv t ht).sub ((iv T (ht.trans htT)).const_mul _)).add
    ((integrable_expWiener hB hW h𝓕 hcont r ht htT).const_mul _)

/-- **Cochrane (2023), p. 168, conditional on date-`t` information**: for `0 ≤ t ≤ T`,
`E_t∫_t^T e^{−r(τ−t)}s_τ dτ = v*_t − e^{−r(T−t)}E_t v*_T` a.s.
Parallels `TidyR7StochCTBrownian.condExp_pv`. -/
theorem condExp_pv_surplus (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (h : η + r - α ≠ 0) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[pvSurplus r α η βs σs W t T | 𝓕 t] =ᵐ[P] fun ω => vsProc r α η βs σs W t ω
      - exp (-(r * (T - t))) * P[vsProc r α η βs σs W T | 𝓕 t] ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have iv : ∀ τ, 0 ≤ τ → Integrable (vsProc r α η βs σs W τ) P := fun τ hτ => by
    rw [vsProc_eq_ker2 h]
    exact integrable_ker2Proc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ _ _ _ hτ
  have hvm : AEStronglyMeasurable[𝓕 t] (vsProc r α η βs σs W t) P := by
    rw [vsProc_eq_ker2 h]
    exact aesm_ker2Proc hB hW h𝓕 hcont hW0 _ _ _ _ _ ht
  have iE := integrable_expWiener hB hW h𝓕 hcont r ht htT
  have i1 := (iv t ht).sub ((iv T (ht.trans htT)).smul (exp (-(r * (T - t)))))
  have e : pvSurplus r α η βs σs W t T = (vsProc r α η βs σs W t
      - (exp (-(r * (T - t)))) • vsProc r α η βs σs W T) + (βs * σs) • expWiener r W t T := by
    funext ω
    rw [pv_identity_surplus h hcont t T ω]
    rfl
  rw [e]
  filter_upwards [condExp_add i1 (iE.smul (βs * σs)) (𝓕 t),
    condExp_sub (iv t ht) ((iv T (ht.trans htT)).smul (exp (-(r * (T - t))))) (𝓕 t),
    condExp_of_aestronglyMeasurable' (𝓕.le t) hvm (iv t ht),
    condExp_smul (μ := P) (exp (-(r * (T - t)))) (vsProc r α η βs σs W T) (𝓕 t),
    condExp_smul (μ := P) (βs * σs) (expWiener r W t T) (𝓕 t),
    condExp_expWiener hB hW h𝓕 hcont r ht htT] with ω h1 h2 h3 h4 h5 h6
  rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, h5]
  simp only [Pi.smul_apply, smul_eq_mul, h6, Pi.zero_apply, mul_zero, add_zero]

/-- **Cochrane (2023), p. 168 (Hansen–Sargent), under uncertainty: `v*` is the present value of
surpluses at every date.** For `r > 0`, `η ≥ 0`, `α ≥ r`, `η + r − α ≠ 0` and `t ≥ 0`,
`E_t∫_t^T e^{−r(τ−t)}s_τ dτ → v*_t` in `L¹` as `T → ∞`.
The stochastic version of `CTSurplus.ct_pv_eq_vstar`. -/
theorem valuation_surplus_L1 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hη : 0 ≤ η) (hα : r ≤ α) (h : η + r - α ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |P[pvSurplus r α η βs σs W t T | 𝓕 t] ω - vsProc r α η βs σs W t ω|
      ∂P) atTop (𝓝 0) := by
  set K := (|0| + |σs / (η + r - α)| + |σs * (βs - 1 / (η + r - α))|) ^ 2
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
    ?_ (tendsto_exp_mul_affine hr t K)
  filter_upwards [eventually_ge_atTop t] with T hT
  have hcond := condExp_pv_surplus (βs := βs) (σs := σs) hB hW h𝓕 hcont hW0 h ht hT
  have e : ∫ ω, |P[pvSurplus r α η βs σs W t T | 𝓕 t] ω - vsProc r α η βs σs W t ω| ∂P
      = exp (-(r * (T - t))) * ∫ ω, |P[vsProc r α η βs σs W T | 𝓕 t] ω| ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    rw [hω, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (exp_pos _)]
  rw [e]
  refine mul_le_mul_of_nonneg_left ((integral_abs_condExp_le _).trans ?_) (exp_pos _).le
  rw [vsProc_eq_ker2 h]
  exact integral_abs_ker2Proc_le hB hW h𝓕 hcont hW0 hη (by linarith) (ht.trans hT)

/-! ### The innovation of the present value and the price-level diffusion -/

/-- **Cochrane (2023), p. 168 ("the shock ... of the present value is `L(r)Dε_s`"), on every
path**: for `α ≠ 0`, `η + r ≠ 0`, `η + r − α ≠ 0`,
`v*_b − v*_a − ∫_a^b (rv* − s) = L(r)σ_s(w_b − w_a)` with `L(r) = β_s`
(`CTSurplus.surplus_L_r`). -/
theorem innovation_eq_L_r (hα : α ≠ 0) (h1 : η + r ≠ 0) (h : η + r - α ≠ 0)
    (hw : Continuous w) (a b : ℝ) :
    vsPath r α η βs σs w b - vsPath r α η βs σs w a
        - ∫ u in a..b, (r * vsPath r α η βs σs w u - ssPath r α η βs σs w u)
      = surplusL r α η βs r * σs * (w b - w a) := by
  rw [vstar_incr h hw a b, surplus_L_r hα h1 h]
  ring

/-- Cochrane (2023), p. 168 (survey E47 under diffusion): the loading of the present-value
innovation equals the printed `L(r)σ_s = −β_sσ_s` iff `β_sσ_s = 0`.
The diffusion version of `CTSurplus.printed_L_r_wrong`. -/
theorem innovation_printed_iff (hα : α ≠ 0) (h1 : η + r ≠ 0) (h : η + r - α ≠ 0) :
    surplusL r α η βs r * σs = -βs * σs ↔ βs * σs = 0 := by
  rw [surplus_L_r hα h1 h]
  constructor <;> intro h' <;> linarith

/-- **Cochrane (2023), p. 168: the bracket of `v*` with `W`.** For `η + r − α ≠ 0` and
`0 ≤ s < t`, a.s. along the dyadic partitions of `[s, t]`, `Σ Δv*ΔW → β_sσ_s(t − s)`.
An instance of `TidyR8StochKernel.tendsto_crossSum_affine`. -/
theorem bracket_vstar_W (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (h : η + r - α ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) :
    ∀ᵐ ω ∂P, Tendsto (fun k => crossSum (dyadic hst k) (fun u => vsProc r α η βs σs W u ω)
      (fun u => bmReal W u ω)) atTop (𝓝 (βs * σs * (t - s))) := by
  have hT := tendsto_crossSum_affine (P := P) hB hW hcont hs hst (βs * σs) 1
    (F := fun ω u => vsProc r α η βs σs W u ω - βs * σs * bmReal W u ω)
    (F' := fun ω u => r * vsProc r α η βs σs W u ω - ssProc r α η βs σs W u ω)
    (G := fun _ _ => 0) (G' := fun _ _ => 0)
    (fun ω x => vs_sub_hasDerivAt h (continuous_bmReal (hcont ω)) x)
    (fun ω => by
      obtain ⟨c1, c2⟩ := continuous_vs_ss (r := r) (α := α) (η := η) (βs := βs) (σs := σs)
        (continuous_bmReal (hcont ω))
      exact (c1.const_mul r).sub c2)
    (fun _ _ => hasDerivAt_const _ _) (fun _ => continuous_const)
  filter_upwards [hT] with ω hω
  simp only [mul_one, one_mul, add_zero] at hω
  refine hω.congr fun k => ?_
  congr 1
  funext u
  ring

/-- **Cochrane (2023), p. 167 and p. 168: the flexible-price debt equation with a diffusive
price level**, on every path: `v*_b − v*_a = ∫_a^b (rv* − s) − (p*_b − p*_a)` (the price-level
diffusion `dp* = −β_sσ_s dw` revalues the debt). -/
theorem pstar_debt (h : η + r - α ≠ 0) (hw : Continuous w) (a b : ℝ) :
    vsPath r α η βs σs w b - vsPath r α η βs σs w a
      = (∫ u in a..b, (r * vsPath r α η βs σs w u - ssPath r α η βs σs w u))
        - (pstarPath βs σs w b - pstarPath βs σs w a) := by
  rw [vstar_incr h hw a b]
  simp only [pstarPath]
  ring

/-- Cochrane (2023), p. 168: **`−Δ(1/P)/(1/P)` (the innovation of `log P`) is `−L(r)dε_s`**, and
with `L(r) = β_s` (E47) it is `−β_s dε_s`: the `dw` loading of `p*` is `−L(r)σ_s`. The printed
right-hand side `β_s dε_s` has the wrong sign (it contradicts `dP/P = −β_s dε_s` of p. 167). -/
theorem pstar_loading (hα : α ≠ 0) (h1 : η + r ≠ 0) (h : η + r - α ≠ 0) (a b : ℝ) :
    pstarPath βs σs w b - pstarPath βs σs w a = -(surplusL r α η βs r) * σs * (w b - w a) := by
  rw [surplus_L_r hα h1 h]
  simp only [pstarPath]
  ring

/-- Cochrane (2023), p. 167 (constant real rate, `E_t dP/P = 0` up to the linearisation): for
`0 ≤ t ≤ T`, `E_t[p*_T − p*_t] = 0` a.s.
An instance of `TidyR7StochCTBrownian.condExp_incr`. -/
theorem condExp_pstar_incr (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[fun ω => pstarProc βs σs W T ω - pstarProc βs σs W t ω | 𝓕 t] =ᵐ[P] 0 := by
  have e : (fun ω => pstarProc βs σs W T ω - pstarProc βs σs W t ω)
      = (-(βs * σs)) • incr W t T := by
    funext ω
    simp only [pstarProc, pstarPath, incr, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  filter_upwards [condExp_smul (μ := P) (-(βs * σs)) (incr W t T) (𝓕 t),
    condExp_incr hB hW h𝓕 ht htT] with ω h1 h2
  rw [h1, Pi.smul_apply, h2]
  simp

/-- **Cochrane (2023), p. 167 ("`dP/P = −β_s dε_s`") and p. 168: the price-level diffusion.**
For `0 ≤ s < t`, a.s. along the dyadic partitions, `Σ Δp*ΔW → −β_sσ_s(t − s)`.
An instance of `TidyR8StochKernel.tendsto_crossSum_affine`. -/
theorem bracket_pstar_W (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂P, Tendsto (fun k => crossSum (dyadic hst k) (fun u => pstarProc βs σs W u ω)
      (fun u => bmReal W u ω)) atTop (𝓝 (-(βs * σs) * (t - s))) := by
  have hT := tendsto_crossSum_affine (P := P) hB hW hcont hs hst (-(βs * σs)) 1
    (F := fun _ _ => 0) (F' := fun _ _ => 0) (G := fun _ _ => 0) (G' := fun _ _ => 0)
    (fun _ _ => hasDerivAt_const _ _) (fun _ => continuous_const)
    (fun _ _ => hasDerivAt_const _ _) (fun _ => continuous_const)
  filter_upwards [hT] with ω hω
  simp only [mul_one, one_mul, add_zero] at hω
  refine hω.congr fun k => ?_
  congr 1
  funext u
  simp only [pstarProc, pstarPath]
  ring

/-- Cochrane (2023), p. 168 (the covariation of the two diffusive states): for
`η + r − α ≠ 0`, `0 ≤ s < t`, a.s. `Σ Δv*Δp* → −(β_sσ_s)²(t − s)`. In the linearised model
of (5.97)–(5.104) no product of `v*` and `p*` appears, so this bracket corrects nothing.
An instance of `TidyR8StochKernel.tendsto_crossSum_affine`. -/
theorem bracket_vstar_pstar (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (h : η + r - α ≠ 0) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) :
    ∀ᵐ ω ∂P, Tendsto (fun k => crossSum (dyadic hst k) (fun u => vsProc r α η βs σs W u ω)
      (fun u => pstarProc βs σs W u ω)) atTop (𝓝 (-(βs * σs) ^ 2 * (t - s))) := by
  have hT := tendsto_crossSum_affine (P := P) hB hW hcont hs hst (βs * σs) (-(βs * σs))
    (F := fun ω u => vsProc r α η βs σs W u ω - βs * σs * bmReal W u ω)
    (F' := fun ω u => r * vsProc r α η βs σs W u ω - ssProc r α η βs σs W u ω)
    (G := fun _ _ => 0) (G' := fun _ _ => 0)
    (fun ω x => vs_sub_hasDerivAt h (continuous_bmReal (hcont ω)) x)
    (fun ω => by
      obtain ⟨c1, c2⟩ := continuous_vs_ss (r := r) (α := α) (η := η) (βs := βs) (σs := σs)
        (continuous_bmReal (hcont ω))
      exact (c1.const_mul r).sub c2)
    (fun _ _ => hasDerivAt_const _ _) (fun _ => continuous_const)
  filter_upwards [hT] with ω hω
  have e : βs * σs * -(βs * σs) * (t - s) = -(βs * σs) ^ 2 * (t - s) := by ring
  rw [e] at hω
  refine hω.congr fun k => ?_
  congr 1
  · funext u
    ring
  · funext u
    simp only [pstarProc, pstarPath]
    ring

/-! ### Non-vacuity -/

/-- **Cochrane (2023), §5.7.2, pp. 167–168 (non-vacuity on the constructed motion `bmPath`)**:
for `r > 0`, `η ≥ 0`, `α ≥ r`, `η + r − α ≠ 0`, `0 ≤ s < t`: the Hansen–Sargent valuation holds
in `L¹`, and a.s. `[p*, W]` over `[s, t]` is `−β_sσ_s(t − s)`. -/
theorem bmPath_surplus (hr : 0 < r) (hη : 0 ≤ η) (hα : r ≤ α) (h : η + r - α ≠ 0) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) :
    Tendsto (fun T => ∫ ω, |gaussSeq[pvSurplus r α η βs σs bmPath s T
        | bmFiltrationReal bmPath measurable_bmPath s] ω - vsProc r α η βs σs bmPath s ω|
      ∂gaussSeq) atTop (𝓝 0) ∧
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k => crossSum (dyadic hst k)
      (fun u => pstarProc βs σs bmPath u ω) (fun u => bmReal bmPath u ω)) atTop
      (𝓝 (-(βs * σs) * (t - s))) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  exact ⟨valuation_surplus_L1 hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero hr hη hα h
      hs,
    bracket_pstar_W hB measurable_bmPath continuous_bmPath hs hst⟩

end Cochrane.StickyPriceFiscal.TidyR8StochCTSurplus
