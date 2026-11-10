/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR8StochKernel

/-!
# The frictionless limit `κ → ∞` of the stochastic price level

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7.1, p. 163 ("as
`κ → ∞` ... `κ → ∞` is the frictionless limit") and p. 167 ("the frictionless limit is well
behaved ... the price level path smoothly approaches the jump of the truly frictionless
model"), and §5.7.4, pp. 172–174 (Fig. 5.10).

The deterministic results are `CTSimple.ct_frictionless_limit` (cumulative inflation tends to
the frictionless jump `v₀ − s̃₀/r`) and `CTSimple.ct_price_limit` (`p^κ_t → i₀t + v₀ − s̃₀/r`
for every `t > 0`). With Brownian shocks `dε_m = σ_i dW`, `dε_s = σ_s dW` (T8's solution,
`v₀ = 0`) the price level is `p^κ_T = σ_i∫_0^T W + A(W_T − Y^{λ₂}_T)/λ₂`, and the limit is
the frictionless price level

`p^∞_T = σ_i∫_0^T W_u du − (σ_s/r)W_T`, i.e. `dp^∞ = i dt − (σ_s/r) dW`,

a diffusion: the frictionless price level absorbs the present value `σ_s/r` of each surplus
innovation, exactly the jump of `CTSimple.ct_price_limit` arriving continuously.

## Main results

* `ouNoise_tendsto_zero`: on every continuous path with `w_0 = 0`, `Y^λ_T → 0` as `λ → ∞`
  (the exponential kernel is an approximate identity, `CTSimple.approx_identity`).
* `pPath_eq`, **`pPath_tendsto`**: on every continuous path, `p^κ_T → σ_i∫_0^T w − (σ_s/r)w_T`
  as `κ → ∞` (for `r ≠ 0`, `σ > 0`, `T ≥ 0`); `pProc_tendsto` (on every Brownian path).
* **`pProc_tendsto_L2`**: `E[(p^κ_T − p^∞_T)²] → 0` (in `L²` at each `T`), with the explicit
  bound `pProc_sub_sq_le`, `E[(p^κ_T − p^∞_T)²] ≤ 2(σ_s/λ₂)²T + ((r + λ₂)σ_s/(rλ₂))²/λ₂`.
* `inflation_variance_tendsto` (`E[(π^κ_T − i_T)²] → ∞` for `σ_s ≠ 0`, `T > 0`: "a larger and
  larger rise in inflation, but one that lasts a shorter and shorter time" — under diffusion
  inflation does not converge, only its integral does) and `output_tendsto_L2`
  (`E[x^κ_T²] → 0`: "output variation becomes smaller").
* Non-vacuity on `bmPath`: `bmPath_price_limit`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR8StochCTLimit

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7BrownianTools Cochrane.StickyPriceFiscal.TidyR7BrownianQV
open Cochrane.StickyPriceFiscal.TidyR7ItoIntegral Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open Cochrane.StickyPriceFiscal.TidyR7BrownianSchauder
open Cochrane.StickyPriceFiscal.TidyR7StochCTPath Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian
open Cochrane.StickyPriceFiscal.CTSimple
open scoped ENNReal NNReal

/-! ### The OU noise vanishes as the rate grows -/

/-- Cochrane (2023), p. 167 (tool): for `a > 0`, `T ≥ 0` and `w` continuous with `w_0 = 0`,
`∫_0^∞ e^{−aτ}w(clamp(T − τ))dτ = e^{−aT}∫_0^T e^{au}w_u du`, where the clamp to `[0, T]` makes
the integrand vanish beyond `T`. -/
theorem integral_clamp_eq {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {a T : ℝ}
    (hT : 0 ≤ T) :
    ∫ τ in Set.Ioi 0, exp (-(a * τ)) * w (max (min (T - τ) T) 0)
      = exp (-a * T) * ouPrim a w T := by
  set f : ℝ → ℝ := fun τ => exp (-(a * τ)) * w (max (min (T - τ) T) 0) with hf
  have hfc : Continuous f := by fun_prop
  have hz : ∀ τ ∈ Set.Ioi T, f τ = 0 := fun τ hτ => by
    have hτ' : T < τ := hτ
    have h1 : min (T - τ) T = T - τ := min_eq_left (by linarith)
    have h2 : max (T - τ) 0 = 0 := max_eq_right (by linarith)
    simp only [hf, h1, h2, hw0, mul_zero]
  have hI1 : IntegrableOn f (Set.Ioc 0 T) :=
    (hfc.integrableOn_Icc (a := 0) (b := T)).mono_set Set.Ioc_subset_Icc_self
  have hI2 : IntegrableOn f (Set.Ioi T) :=
    integrableOn_zero.congr_fun (fun τ hτ => (hz τ hτ).symm) measurableSet_Ioi
  have hsplit : ∫ τ in Set.Ioi 0, f τ = (∫ τ in Set.Ioc 0 T, f τ) + ∫ τ in Set.Ioi T, f τ := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hI1 hI2]
  have h0 : ∫ τ in Set.Ioi T, f τ = 0 := setIntegral_eq_zero_of_forall_eq_zero hz
  change ∫ τ in Set.Ioi 0, f τ = _
  rw [hsplit, h0, add_zero, ← intervalIntegral.integral_of_le hT]
  have hc : ∫ τ in (0 : ℝ)..T, f τ = ∫ τ in (0 : ℝ)..T, exp (-(a * τ)) * w (T - τ) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le hT] at hτ
    have h1 : min (T - τ) T = T - τ := min_eq_left (by linarith [hτ.1])
    have h2 : max (T - τ) 0 = T - τ := max_eq_left (by linarith [hτ.2])
    simp only [hf, h1, h2]
  rw [hc]
  have hs := intervalIntegral.integral_comp_sub_left
    (fun u => exp (-(a * (T - u))) * w u) (a := 0) (b := T) T
  simp only [sub_sub_cancel, sub_self, sub_zero] at hs
  rw [hs, ouPrim, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [show -(a * (T - u)) = -a * T + a * u by ring, exp_add]
  ring

/-- **Cochrane (2023), p. 167: on every continuous path with `w_0 = 0`, the OU noise `Y^λ_T`
tends to `0` as `λ → ∞`** (for each `T ≥ 0`).
An application of `CTSimple.approx_identity`. -/
theorem ouNoise_tendsto_zero {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) : Tendsto (fun a => ouNoise a w T) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun τ => w (max (min (T - τ) T) 0) with hg
  have hgc : Continuous g := by fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 T)
    hw.continuousOn
  have hM : ∀ τ, |g τ| ≤ C := fun τ => by
    have hm : max (min (T - τ) T) 0 ∈ Set.Icc 0 T :=
      ⟨le_max_right _ _, max_le (min_le_right _ _) hT⟩
    simpa [Real.norm_eq_abs] using hC _ hm
  have hg0 : Tendsto g (𝓝[>] 0) (𝓝 (w T)) := by
    have e : g 0 = w T := by simp [hg, max_eq_left hT]
    rw [← e]
    exact (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hA := approx_identity hgc.measurable hM hg0
  have hlim := hA.const_sub (w T)
  rw [sub_self] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a _
  rw [integral_clamp_eq hw hw0 hT, ouNoise]

/-! ### The price level -/

variable {r σ κ ρ σi σs : ℝ} {w : ℝ → ℝ}

/-- Cochrane (2023), p. 167 (tool): `∫_0^T Y^λ = (w_T − Y^λ_T)/λ` when `w_0 = 0`, `λ ≠ 0`. -/
theorem integral_ouNoise (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ} (hη : η ≠ 0) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, ouNoise η w u = (w T - ouNoise η w T) / η := by
  have h := ouNoise_incr η hw 0 T
  rw [ouNoise_zero, hw0] at h
  field_simp
  linarith

/-- **Cochrane (2023), p. 167: the price level on a path**,
`p_T = σ_i∫_0^T w + (A/λ₂)(w_T − Y^{λ₂}_T)` (`κ, σ > 0`, `w_0 = 0`). -/
theorem pPath_eq (hκ : 0 < κ) (hσ : 0 < σ) (hw : Continuous w) (hw0 : w 0 = 0) (T : ℝ) :
    pPath r σ κ ρ σi σs w T = σi * (∫ u in (0 : ℝ)..T, w u)
      + fiscalLoad r σ κ ρ σs / lam2 ρ κ σ * (w T - ouNoise (lam2 ρ κ σ) w T) := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  have hY := continuous_ouNoise (lam2 ρ κ σ) hw
  simp only [pPath, piPath]
  rw [intervalIntegral.integral_add ((hw.const_mul σi).intervalIntegrable 0 T)
    ((hY.const_mul _).intervalIntegrable 0 T), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_ouNoise hw hw0 h2]
  ring

/-- Cochrane (2023), p. 167: `A/λ₂ = −σ_s/r − σ_s/λ₂` (`r ≠ 0`, `λ₂ ≠ 0`). -/
theorem fiscalLoad_div (hr : r ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ) :
    fiscalLoad r σ κ ρ σs / lam2 ρ κ σ = -(σs / r) - σs / lam2 ρ κ σ := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  simp only [fiscalLoad]
  field_simp
  ring

/-- **Cochrane (2023), p. 167 ("the price level path smoothly approaches the jump of the truly
frictionless model"), with diffusive shocks, on every path.** For `r ≠ 0`, `σ > 0`, `T ≥ 0`
and a continuous path with `w_0 = 0`, as `κ → ∞`,
`p^κ_T → σ_i∫_0^T w − (σ_s/r)w_T`.
The stochastic version of `CTSimple.ct_price_limit`. -/
theorem pPath_tendsto (hr : r ≠ 0) (hσ : 0 < σ) (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) :
    Tendsto (fun κ => pPath r σ κ ρ σi σs w T) atTop
      (𝓝 (σi * (∫ u in (0 : ℝ)..T, w u) - σs / r * w T)) := by
  have hL := lam2_tendsto_atTop (ρ := ρ) hσ
  have hY := (ouNoise_tendsto_zero hw hw0 hT).comp hL
  have hc : Tendsto (fun κ => -(σs / r) - σs / lam2 ρ κ σ) atTop (𝓝 (-(σs / r))) := by
    have h0 : Tendsto (fun κ => σs / lam2 ρ κ σ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
    have := h0.const_sub (-(σs / r))
    simpa using this
  have := (hc.mul (hY.const_sub (w T))).const_add (σi * ∫ u in (0 : ℝ)..T, w u)
  rw [sub_zero] at this
  rw [show σi * (∫ u in (0 : ℝ)..T, w u) - σs / r * w T
    = σi * (∫ u in (0 : ℝ)..T, w u) + -(σs / r) * (w T) by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  rw [pPath_eq hκ hσ hw hw0, fiscalLoad_div hr hκ hσ]
  rfl

/-! ### With Brownian shocks -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-- Cochrane (2023), p. 167: the frictionless price level `p^∞_T = σ_i∫_0^T W − (σ_s/r)W_T`. -/
noncomputable def pLimProc (r σi σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  σi * (∫ u in (0 : ℝ)..T, bmReal W u ω) - σs / r * bmReal W T ω

/-- **Cochrane (2023), p. 167, on every Brownian path**: `p^κ_T → p^∞_T` as `κ → ∞` (for
`r ≠ 0`, `σ > 0`, `T ≥ 0`, continuous paths, `W_0 = 0`). -/
theorem pProc_tendsto (hr : r ≠ 0) (hσ : 0 < σ) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    Tendsto (fun κ => pProc r σ κ ρ σi σs W T ω) atTop (𝓝 (pLimProc r σi σs W T ω)) :=
  pPath_tendsto hr hσ (continuous_bmReal (hcont ω)) (by simp [bmReal, hW0]) hT

/-- Cochrane (2023), p. 167 (tool): `∫_0^T e^{−2λ(T−u)}du ≤ 1/(2λ)` for `λ > 0`, `T ≥ 0`. -/
theorem integral_exp_two_le {l T : ℝ} (hl : 0 < l) :
    ∫ u in (0 : ℝ)..T, exp (-(l * (T - u))) ^ 2 ≤ 1 / (2 * l) := by
  have hs := intervalIntegral.integral_comp_sub_left
    (fun s => exp (-(l * s)) ^ 2) (a := 0) (b := T) T
  simp only [sub_self, sub_zero] at hs
  rw [hs]
  have e : (fun s => exp (-(l * s)) ^ 2) = fun s => exp (-((2 * l) * s)) := by
    funext s
    rw [← exp_nat_mul]
    ring_nf
  rw [e, intervalIntegral_exp (by positivity) T]
  have : 0 < exp (-(2 * l * T)) := exp_pos _
  rw [div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- **Cochrane (2023), p. 167 (tool): the second moment of `aW_T + dY^λ_T`** is at most
`2a²T + d²/λ` for `λ > 0`, `T ≥ 0`. -/
theorem integral_kerProc_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (a d : ℝ) {l T : ℝ} (hl : 0 < l) (hT : 0 ≤ T) :
    ∫ ω, kerProc W a d l T ω ^ 2 ∂P ≤ 2 * a ^ 2 * T + d ^ 2 / l := by
  rw [integral_kerProc_sq (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 a d l hT]
  have hc : Continuous fun u => exp (-(l * (T - u))) ^ 2 := by fun_prop
  calc ∫ u in (0 : ℝ)..T, kerFn a d l (T - u) ^ 2
      ≤ ∫ u in (0 : ℝ)..T, (2 * a ^ 2 + 2 * d ^ 2 * exp (-(l * (T - u))) ^ 2) := by
        refine intervalIntegral.integral_mono_on hT
          (((continuous_kerFn a d l T).pow 2).intervalIntegrable 0 T)
          ((continuous_const.add (hc.const_mul _)).intervalIntegrable 0 T) fun u _ => ?_
        simp only [kerFn]
        nlinarith [sq_nonneg (a - d * exp (-(l * (T - u))))]
    _ = 2 * a ^ 2 * T + 2 * d ^ 2 * ∫ u in (0 : ℝ)..T, exp (-(l * (T - u))) ^ 2 := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          ((hc.const_mul _).intervalIntegrable 0 T), intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul]
        simp only [sub_zero, smul_eq_mul]
        ring
    _ ≤ 2 * a ^ 2 * T + 2 * d ^ 2 * (1 / (2 * l)) := by
        gcongr
        exact integral_exp_two_le hl
    _ = 2 * a ^ 2 * T + d ^ 2 / l := by
        field_simp

/-- Cochrane (2023), p. 167: on every path the gap to the frictionless price level is
`p^κ_T − p^∞_T = −(σ_s/λ₂)W_T + ((r + λ₂)σ_s/(rλ₂))Y^{λ₂}_T`. -/
theorem pProc_sub_eq (hr : r ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (T : ℝ) (ω : Ω) :
    pProc r σ κ ρ σi σs W T ω - pLimProc r σi σs W T ω
      = kerProc W (-(σs / lam2 ρ κ σ)) ((r + lam2 ρ κ σ) * σs / (r * lam2 ρ κ σ))
        (lam2 ρ κ σ) T ω := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  simp only [pProc, pLimProc, kerProc]
  rw [pPath_eq hκ hσ (continuous_bmReal (hcont ω)) (by simp [bmReal, hW0]),
    fiscalLoad_div hr hκ hσ]
  field_simp
  ring

/-- **Cochrane (2023), p. 167: the explicit `L²` bound.** For `r ≠ 0`, `κ, σ > 0`, `T ≥ 0`:
`E[(p^κ_T − p^∞_T)²] ≤ 2(σ_s/λ₂)²T + ((r + λ₂)σ_s/(rλ₂))²/λ₂`. -/
theorem pProc_sub_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : r ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, (pProc r σ κ ρ σi σs W T ω - pLimProc r σi σs W T ω) ^ 2 ∂P
      ≤ 2 * (-(σs / lam2 ρ κ σ)) ^ 2 * T
        + ((r + lam2 ρ κ σ) * σs / (r * lam2 ρ κ σ)) ^ 2 / lam2 ρ κ σ := by
  simp only [pProc_sub_eq hr hκ hσ hcont hW0 T]
  exact integral_kerProc_sq_le (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ (lam2_pos hκ hσ) hT

/-- **Cochrane (2023), p. 167: the frictionless limit of the stochastic price level, in `L²`.**
For `r ≠ 0`, `σ > 0`, `T ≥ 0`: `E[(p^κ_T − p^∞_T)²] → 0` as `κ → ∞`, where
`p^∞_T = σ_i∫_0^T W − (σ_s/r)W_T` (a diffusion with loading `−σ_s/r`).
The stochastic version of `CTSimple.ct_price_limit`. -/
theorem pProc_tendsto_L2 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : r ≠ 0) (hσ : 0 < σ) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun κ => ∫ ω, (pProc r σ κ ρ σi σs W T ω - pLimProc r σi σs W T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hL := lam2_tendsto_atTop (ρ := ρ) hσ
  have hinv : Tendsto (fun κ => (lam2 ρ κ σ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hL
  have hb : Tendsto (fun κ => 2 * (-(σs * (lam2 ρ κ σ)⁻¹)) ^ 2 * T
      + ((σs / r + σs * (lam2 ρ κ σ)⁻¹)) ^ 2 * (lam2 ρ κ σ)⁻¹) atTop (𝓝 0) := by
    have := ((((hinv.const_mul σs).neg).pow 2).const_mul 2).mul_const T |>.add
      ((((hinv.const_mul σs).const_add (σs / r)).pow 2).mul hinv)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
    ?_ hb
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  refine (pProc_sub_sq_le hB hW h𝓕 hcont hW0 hr hκ hσ hT).trans (le_of_eq ?_)
  field_simp
  ring

/-- **Cochrane (2023), p. 167 ("a larger and larger rise in inflation, but one that lasts a
shorter and shorter time"), with diffusive shocks**: for `r > 0`, `σ > 0`, `σ_s ≠ 0`, `T > 0`,
`E[(π^κ_T − i_T)²] = A²(1 − e^{−2λ₂T})/(2λ₂) → ∞` as `κ → ∞`: inflation itself has no limit
(it tends to white noise), only the price level does. -/
theorem inflation_variance_tendsto (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hσ : 0 < σ) (hs : σs ≠ 0) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun κ => ∫ ω, (piProc r σ κ ρ σi σs W T ω - iProc σi W T ω) ^ 2 ∂P) atTop
      atTop := by
  have hL := lam2_tendsto_atTop (ρ := ρ) hσ
  have hE : ∀ κ, 0 < κ → ∫ ω, (piProc r σ κ ρ σi σs W T ω - iProc σi W T ω) ^ 2 ∂P
      = fiscalLoad r σ κ ρ σs ^ 2 * ((1 - exp (-(2 * lam2 ρ κ σ * T))) / (2 * lam2 ρ κ σ)) := by
    intro κ hκ
    have h2 := lam2_pos (ρ := ρ) hκ hσ
    have e : (fun ω => (piProc r σ κ ρ σi σs W T ω - iProc σi W T ω) ^ 2)
        = fun ω => kerProc W 0 (fiscalLoad r σ κ ρ σs) (lam2 ρ κ σ) T ω ^ 2 := by
      funext ω
      simp only [piProc, piPath, iProc, iPath, kerProc]
      ring
    rw [e, integral_kerProc_sq (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ _ hT.le]
    have hs := intervalIntegral.integral_comp_sub_left
      (fun s => kerFn 0 (fiscalLoad r σ κ ρ σs) (lam2 ρ κ σ) s ^ 2) (a := 0) (b := T) T
    simp only [sub_self, sub_zero] at hs
    rw [hs]
    have e2 : (fun s => kerFn 0 (fiscalLoad r σ κ ρ σs) (lam2 ρ κ σ) s ^ 2)
        = fun s => fiscalLoad r σ κ ρ σs ^ 2 * exp (-((2 * lam2 ρ κ σ) * s)) := by
      funext s
      simp only [kerFn, zero_add, mul_pow]
      rw [← exp_nat_mul]
      ring_nf
    rw [e2, intervalIntegral.integral_const_mul, intervalIntegral_exp (by positivity) T]
  have hA : ∀ κ, 0 < κ → fiscalLoad r σ κ ρ σs ^ 2 / (2 * lam2 ρ κ σ)
      ≥ σs ^ 2 / (2 * r ^ 2) * lam2 ρ κ σ := by
    intro κ hκ
    have h2 := lam2_pos (ρ := ρ) hκ hσ
    have key : fiscalLoad r σ κ ρ σs ^ 2 / (2 * lam2 ρ κ σ)
        = σs ^ 2 * (r + lam2 ρ κ σ) ^ 2 / (2 * lam2 ρ κ σ * r ^ 2) := by
      simp only [fiscalLoad]
      field_simp
    rw [key, ge_iff_le, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : lam2 ρ κ σ ^ 2 ≤ (r + lam2 ρ κ σ) ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * r ^ 2 * σs ^ 2)
    nlinarith
  have hlow : Tendsto (fun κ => σs ^ 2 / (2 * r ^ 2) * lam2 ρ κ σ * (1 / 2)) atTop atTop := by
    have hc : 0 < σs ^ 2 / (2 * r ^ 2) * (1 / 2) := by positivity
    have := hL.const_mul_atTop hc
    refine this.congr fun κ => by ring
  refine tendsto_atTop_mono' _ ?_ hlow
  have hexp : ∀ᶠ κ in atTop, exp (-(2 * lam2 ρ κ σ * T)) ≤ 1 / 2 := by
    have : Tendsto (fun κ => exp (-(2 * lam2 ρ κ σ * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((hL.const_mul_atTop two_pos).atTop_mul_const hT)
    exact this.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_gt_atTop 0, hexp] with κ hκ he
  rw [hE κ hκ]
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have := hA κ hκ
  have hpos : 0 ≤ fiscalLoad r σ κ ρ σs ^ 2 / (2 * lam2 ρ κ σ) := by positivity
  calc σs ^ 2 / (2 * r ^ 2) * lam2 ρ κ σ * (1 / 2)
      ≤ fiscalLoad r σ κ ρ σs ^ 2 / (2 * lam2 ρ κ σ) * (1 / 2) := by
        exact mul_le_mul_of_nonneg_right this (by norm_num)
    _ ≤ fiscalLoad r σ κ ρ σs ^ 2 / (2 * lam2 ρ κ σ) * (1 - exp (-(2 * lam2 ρ κ σ * T))) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = fiscalLoad r σ κ ρ σs ^ 2 * ((1 - exp (-(2 * lam2 ρ κ σ * T))) / (2 * lam2 ρ κ σ)) := by
        ring

/-- **Cochrane (2023), p. 163 ("as `κ → ∞`, output variation becomes smaller")**: for
`r ≠ 0`, `σ > 0`, `T ≥ 0`, `E[x^κ_T²] → 0` as `κ → ∞`.
The stochastic version of `CTSimple.ct_flexible_limit`. -/
theorem output_tendsto_L2 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : r ≠ 0) (hσ : 0 < σ) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun κ => ∫ ω, xProc r σ κ ρ σi σs W T ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hL := lam2_tendsto_atTop (ρ := ρ) hσ
  have hinv : Tendsto (fun κ => (lam2 ρ κ σ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hL
  have hkinv : Tendsto (fun κ : ℝ => κ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hb : Tendsto (fun κ => 2 * (ρ * σi * κ⁻¹) ^ 2 * T
      + (σ * (σs / r + σs * (lam2 ρ κ σ)⁻¹)) ^ 2 * (lam2 ρ κ σ)⁻¹) atTop (𝓝 0) := by
    have := ((((hkinv.const_mul (ρ * σi)).pow 2).const_mul 2).mul_const T).add
      ((((((hinv.const_mul σs).const_add (σs / r))).const_mul σ).pow 2).mul hinv)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
    ?_ hb
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  have hm := lam_mul (ρ := ρ) hκ hσ
  rw [xProc_eq_ker]
  refine (integral_kerProc_sq_le (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ (lam2_pos hκ hσ) hT).trans
    (le_of_eq ?_)
  have hl1 : lam1 ρ κ σ / κ = σ / lam2 ρ κ σ := by
    field_simp
    linear_combination hm
  have e : lam1 ρ κ σ * fiscalLoad r σ κ ρ σs / κ
      = -(σ * (σs / r + σs * (lam2 ρ κ σ)⁻¹)) := by
    rw [mul_comm, mul_div_assoc, hl1]
    simp only [fiscalLoad]
    field_simp
    ring
  rw [e]
  field_simp

/-! ### Non-vacuity -/

/-- **Cochrane (2023), p. 167 (non-vacuity on the constructed motion `bmPath`)**: for `r ≠ 0`,
`σ > 0`, `T ≥ 0`, the price level converges on every path and in `L²` to
`σ_i∫_0^T W − (σ_s/r)W_T`. -/
theorem bmPath_price_limit (hr : r ≠ 0) (hσ : 0 < σ) {T : ℝ} (hT : 0 ≤ T) :
    (∀ ω, Tendsto (fun κ => pProc r σ κ ρ σi σs bmPath T ω) atTop
      (𝓝 (pLimProc r σi σs bmPath T ω))) ∧
    Tendsto (fun κ => ∫ ω, (pProc r σ κ ρ σi σs bmPath T ω - pLimProc r σi σs bmPath T ω) ^ 2
      ∂gaussSeq) atTop (𝓝 0) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  exact ⟨pProc_tendsto hr hσ continuous_bmPath bmPath_zero hT,
    pProc_tendsto_L2 hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero hr hσ hT⟩

end Cochrane.StickyPriceFiscal.TidyR8StochCTLimit
