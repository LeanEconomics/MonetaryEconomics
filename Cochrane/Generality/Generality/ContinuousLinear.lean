/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.ContinuousShort
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Linearised identities in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.3, pp. 76–79.

All paths are deterministic (`ℝ → ℝ`), differentiable where stated; infinite-horizon present
values are genuine improper integrals over `(t, ∞)` with integrability as an explicit hypothesis
(signed integrands: absolute integrability). The book's innovations `Δ_t` are formalised as the
difference between two perfect-foresight paths ("old" and "new") from the news date `t` on.

* A valuation engine: `G' = g` on `[t, ∞)` with `g` integrable gives `G(T) → G(t) + ∫_t^∞ g`;
  for `V' = rV − f` and a discount factor `Λ' = −rΛ`, the transversality condition
  `Λ(T)V(T) → 0` holds **iff** `V(t) = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`; uniqueness and existence.
* (3.39)–(3.40): steady state `s = rV`; the exact derivative of the flow map at the steady state.
* (3.41)–(3.43): the linearised value identity, iff the TVC, in the book's shifted form
  `∫_0^∞ e^{−rτ} x_{t+τ} dτ` (with the integrand index corrected, E21); the shift itself is
  `ContinuousShort.integral_Ioi_shift`.
* p. 76: `dR^n = dR + π dt` (nominal and real returns of a nominal asset).
* p. 77: AR(1) surpluses `ds = −ηs dt` (corrected, E18), present value `s/(r+η)`, news `σ/(r+η)`.
* (3.47): bond price `Q = 1/(ω+y)`, the holding return as the limit of the discrete return, and
  `dR^n = y dt + dQ/Q`.
* (3.48): exact derivative of the bond-return identity at the steady state; the book's
  intermediate line has the wrong sign (E19).
* (3.49): forward solution of (3.48), unique under the TVC (or boundedness).
* (3.46), (3.50), (3.51): news identities between two equilibria; the `ω → ∞` short-debt limit
  (the book says `ω = 0`, E20) and the `ω = 0` perpetuity counterexample.
-/

namespace Cochrane.Generality.ContinuousLinear

open Filter Topology MeasureTheory

/-! ## The valuation engine -/

/-- Cochrane (2023), §3.6, pp. 73–76 (integrating a flow forward): if `G' = g` on `[t, ∞)` and `g`
is integrable on `(t, ∞)`, then `G(T) → G(t) + ∫_t^∞ g`. -/
theorem tendsto_of_hasDerivAt {G g : ℝ → ℝ} {t : ℝ}
    (hG : ∀ τ, t ≤ τ → HasDerivAt G (g τ) τ) (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto G atTop (𝓝 (G t + ∫ τ in Set.Ioi t, g τ)) := by
  have hI := (intervalIntegral_tendsto_integral_Ioi t hg tendsto_id).const_add (G t)
  refine hI.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have hT' : t ≤ id T := hT
  have hint : IntervalIntegrable g volume t T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT').2 (hg.mono_set Set.Ioc_subset_Ioi_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hG x (by rw [Set.uIcc_of_le hT] at hx; exact hx.1)) hint
  simp only [id]
  rw [hftc]
  ring

/-- Cochrane (2023), §3.6, p. 74: the tail of a convergent improper integral vanishes,
`∫_T^∞ g → 0` as `T → ∞`. -/
theorem tendsto_integral_Ioi_zero {g : ℝ → ℝ} {t : ℝ} (hg : IntegrableOn g (Set.Ioi t)) :
    Tendsto (fun T => ∫ τ in Set.Ioi T, g τ) atTop (𝓝 0) := by
  have hI := (intervalIntegral_tendsto_integral_Ioi t hg tendsto_id)
  have h := (tendsto_const_nhds (x := ∫ τ in Set.Ioi t, g τ)).sub hI
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have := intervalIntegral.integral_interval_add_Ioi hg (hg.mono_set (Set.Ioi_subset_Ioi hT))
  simp only [id]
  linarith

/-- Cochrane (2023), (3.29)–(3.31), pp. 73–74: along `V' = rV − f` and `Λ' = −rΛ`, the
discounted value obeys `(ΛV)' = −Λf`. -/
theorem discounted_hasDerivAt {Λ V r f : ℝ → ℝ} {τ : ℝ}
    (hΛ : HasDerivAt Λ (-(r τ) * Λ τ) τ) (hV : HasDerivAt V (r τ * V τ - f τ) τ) :
    HasDerivAt (fun u => Λ u * V u) (-(Λ τ * f τ)) τ := by
  have h := hΛ.mul hV
  convert h using 1
  ring

/-- Cochrane (2023), (3.31), pp. 73–74: along `V' = rV − f` with discount factor `Λ' = −rΛ` and
`Λf` integrable, the discounted value converges: `Λ(T)V(T) → Λ(t)V(t) − ∫_t^∞ Λf`. -/
theorem discounted_tendsto {Λ V r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Λ T * V T) atTop (𝓝 (Λ t * V t - ∫ τ in Set.Ioi t, Λ τ * f τ)) := by
  have h := tendsto_of_hasDerivAt (G := fun u => Λ u * V u) (g := fun u => -(Λ u * f u))
    (fun τ hτ => discounted_hasDerivAt (hΛ τ hτ) (hV τ hτ)) hint.neg
  rw [integral_neg] at h
  simpa [sub_eq_add_neg] using h

/-- Cochrane (2023), (3.31), p. 74: `∫_t^∞ (Λ_τ/Λ_t) f_τ dτ = (1/Λ_t) ∫_t^∞ Λ_τ f_τ dτ`. -/
theorem integral_ratio_eq {Λ f : ℝ → ℝ} (t : ℝ) :
    ∫ τ in Set.Ioi t, Λ τ / Λ t * f τ = (Λ t)⁻¹ * ∫ τ in Set.Ioi t, Λ τ * f τ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), (3.31) and A1.4, pp. 74, 564–565: **valuation iff transversality.**
If `V' = rV − f` and `Λ' = −rΛ` on `[t, ∞)`, `Λ_t > 0` and `Λf` is integrable, then the TVC
`Λ(T)V(T) → 0` holds iff `V_t = ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ`. -/
theorem tvc_iff_valuation {Λ V r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛt : 0 < Λ t)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Λ T * V T) atTop (𝓝 0) ↔
      V t = ∫ τ in Set.Ioi t, Λ τ / Λ t * f τ := by
  have hlim := discounted_tendsto hΛ hV hint
  rw [integral_ratio_eq]
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    field_simp
    linarith
  · intro hv
    have : Λ t * V t - ∫ τ in Set.Ioi t, Λ τ * f τ = 0 := by
      rw [hv]; field_simp; ring
    rwa [this] at hlim

/-- Cochrane (2023), (3.31), p. 74: under the TVC the valuation equation holds at **every**
date `t' ≥ t`. -/
theorem valuation_every_date {Λ V r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛpos : ∀ τ, t ≤ τ → 0 < Λ τ)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t))
    (htvc : Tendsto (fun T => Λ T * V T) atTop (𝓝 0)) (t' : ℝ) (ht' : t ≤ t') :
    V t' = ∫ τ in Set.Ioi t', Λ τ / Λ t' * f τ :=
  (tvc_iff_valuation (fun τ hτ => hΛ τ (le_trans ht' hτ)) (hΛpos t' ht')
    (fun τ hτ => hV τ (le_trans ht' hτ)) (hint.mono_set (Set.Ioi_subset_Ioi ht'))).1 htvc

/-- Cochrane (2023), (3.31), p. 74: **uniqueness**: two solutions of `V' = rV − f` satisfying the
TVC coincide on `[t, ∞)`. -/
theorem valuation_unique {Λ V W r f : ℝ → ℝ} {t : ℝ}
    (hΛ : ∀ τ, t ≤ τ → HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛpos : ∀ τ, t ≤ τ → 0 < Λ τ)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r τ * V τ - f τ) τ)
    (hW : ∀ τ, t ≤ τ → HasDerivAt W (r τ * W τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi t))
    (hV0 : Tendsto (fun T => Λ T * V T) atTop (𝓝 0))
    (hW0 : Tendsto (fun T => Λ T * W T) atTop (𝓝 0)) (t' : ℝ) (ht' : t ≤ t') : V t' = W t' := by
  rw [valuation_every_date hΛ hΛpos hV hint hV0 t' ht',
    valuation_every_date hΛ hΛpos hW hint hW0 t' ht']

/-- Cochrane (2023), (3.31), p. 74: **existence**: if `Λ > 0`, `Λ' = −rΛ` everywhere, `Λf` is
continuous and integrable on every half-line, then `V_t := ∫_t^∞ (Λ_τ/Λ_t) f_τ dτ` solves
`V' = rV − f` and the TVC. -/
theorem valuation_exists {Λ r f : ℝ → ℝ}
    (hΛ : ∀ τ, HasDerivAt Λ (-(r τ) * Λ τ) τ) (hΛpos : ∀ τ, 0 < Λ τ)
    (hc : Continuous fun τ => Λ τ * f τ)
    (hint : ∀ a, IntegrableOn (fun τ => Λ τ * f τ) (Set.Ioi a)) :
    (∀ τ, HasDerivAt (fun u => ∫ x in Set.Ioi u, Λ x / Λ u * f x)
      (r τ * (∫ x in Set.Ioi τ, Λ x / Λ τ * f x) - f τ) τ) ∧
    Tendsto (fun T => Λ T * ∫ x in Set.Ioi T, Λ x / Λ T * f x) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun τ => Λ τ * f τ with hg
  have hF : ∀ u, ∫ x in Set.Ioi u, g x = (∫ x in Set.Ioi 0, g x) - ∫ x in (0 : ℝ)..u, g x := by
    intro u
    rw [← intervalIntegral.integral_interval_add_Ioi (hint 0) (hint u)]
    ring
  have hV : ∀ u, ∫ x in Set.Ioi u, Λ x / Λ u * f x =
      (Λ u)⁻¹ * ((∫ x in Set.Ioi 0, g x) - ∫ x in (0 : ℝ)..u, g x) := by
    intro u; rw [integral_ratio_eq, hF]
  refine ⟨fun τ => ?_, ?_⟩
  · have hP := HasDerivAt.sub (hasDerivAt_const τ (∫ x in Set.Ioi 0, g x))
      (hc.integral_hasStrictDerivAt 0 τ).hasDerivAt
    rw [zero_sub] at hP
    have hI : HasDerivAt (fun u => (Λ u)⁻¹) (-(-(r τ) * Λ τ) / (Λ τ) ^ 2) τ :=
      (hΛ τ).inv (hΛpos τ).ne'
    have h := hI.mul hP
    rw [show (fun u => ∫ x in Set.Ioi u, Λ x / Λ u * f x) =
      fun u => (Λ u)⁻¹ * ((∫ x in Set.Ioi 0, g x) - ∫ x in (0 : ℝ)..u, g x) from funext hV,
      hV τ]
    convert h using 1
    have hΛne := (hΛpos τ).ne'
    simp only [hg, Pi.sub_apply]
    field_simp
    ring
  · have h := tendsto_integral_Ioi_zero (hint 0)
    refine h.congr' ?_
    filter_upwards with T
    rw [integral_ratio_eq, ← mul_assoc, mul_inv_cancel₀ (hΛpos T).ne', one_mul]

/-! ## Exponential discounting and the book's shifted integrals -/

/-- Cochrane (2023), p. 74: the constant-rate discount factor `Λ_τ = e^{−rτ}` obeys
`Λ' = −rΛ`. -/
theorem hasDerivAt_expDisc (r τ : ℝ) :
    HasDerivAt (fun u => Real.exp (-(r * u))) (-r * Real.exp (-(r * τ))) τ := by
  have h1 : HasDerivAt (fun u => -(r * u)) (-r) τ :=
    (HasDerivAt.neg ((hasDerivAt_id' τ).const_mul r)).congr_deriv (by ring)
  exact (HasDerivAt.exp h1).congr_deriv (by ring)

/-- Cochrane (2023), p. 74: `Λ_τ/Λ_t = e^{−r(τ−t)}` for `Λ_τ = e^{−rτ}`. -/
theorem expDisc_ratio (r t τ : ℝ) :
    Real.exp (-(r * τ)) / Real.exp (-(r * t)) = Real.exp (-(r * (τ - t))) := by
  rw [← Real.exp_sub]; ring_nf

/-- Cochrane (2023), p. 74 (constant real rate): if `V' = rV − f` on `[t, ∞)` with `r`
constant and `e^{−rτ} f_τ` integrable, then the TVC `e^{−rT}V_T → 0` holds iff
`V_t = ∫_0^∞ e^{−rτ} f_{t+τ} dτ`. -/
theorem const_rate_tvc_iff {V f : ℝ → ℝ} {r t : ℝ}
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (r * V τ - f τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * f τ) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(r * T)) * V T) atTop (𝓝 0) ↔
      V t = ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * f (t + τ) := by
  have h := tvc_iff_valuation (Λ := fun u => Real.exp (-(r * u))) (r := fun _ => r)
    (fun τ _ => hasDerivAt_expDisc r τ) (Real.exp_pos _) hV hint
  rw [h]
  have : ∫ τ in Set.Ioi t, Real.exp (-(r * τ)) / Real.exp (-(r * t)) * f τ =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * f (t + τ) := by
    rw [← ContinuousShort.integral_Ioi_shift]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [expDisc_ratio, add_sub_cancel_left]
  rw [this]

/-- Cochrane (2023), (3.41)–(3.43), p. 76: shifting preserves integrability on half-lines:
`g` integrable on `(t, ∞)` gives `τ ↦ g(t+τ)` integrable on `(0, ∞)`. -/
theorem integrableOn_shift {g : ℝ → ℝ} {t : ℝ} (hg : IntegrableOn g (Set.Ioi t)) :
    IntegrableOn (fun τ => g (t + τ)) (Set.Ioi 0) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) t).integrableOn_comp_preimage
    (measurableEmbedding_addLeft t) (f := g) (s := Set.Ioi t)
  have hpre : (fun x => t + x) ⁻¹' Set.Ioi t = Set.Ioi 0 := by ext x; simp
  rw [hpre] at h
  exact h.2 hg

/-- Cochrane (2023), (3.43), p. 76: `e^{−aτ} g_τ` integrable on `(t, ∞)` gives
`τ ↦ e^{−aτ} g_{t+τ}` integrable on `(0, ∞)`. -/
theorem integrableOn_shift_weighted {g : ℝ → ℝ} {a t : ℝ}
    (hg : IntegrableOn (fun τ => Real.exp (-(a * τ)) * g τ) (Set.Ioi t)) :
    IntegrableOn (fun τ => Real.exp (-(a * τ)) * g (t + τ)) (Set.Ioi 0) := by
  have h := (integrableOn_shift hg).const_mul (Real.exp (a * t))
  refine IntegrableOn.congr_fun h (fun τ _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), (3.43), p. 76: `(Λ_t)⁻¹ ∫_t^∞ Λ_τ g_τ dτ = ∫_0^∞ e^{−aτ} g_{t+τ} dτ` for
`Λ_τ = e^{−aτ}`. -/
theorem shift_weighted (g : ℝ → ℝ) (a t : ℝ) :
    (Real.exp (-(a * t)))⁻¹ * ∫ τ in Set.Ioi t, Real.exp (-(a * τ)) * g τ =
      ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * g (t + τ) := by
  have h := integral_ratio_eq (Λ := fun τ => Real.exp (-(a * τ))) (f := g) t
  rw [← h, ← ContinuousShort.integral_Ioi_shift]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [expDisc_ratio, add_sub_cancel_left]

/-- Cochrane (2023), (3.43), p. 76: linearity of a weighted integral,
`∫ w(a − c) = ∫ wa − ∫ wc`, under integrability of both pieces. -/
theorem integral_weighted_sub {w a c : ℝ → ℝ} {S : Set ℝ}
    (ha : IntegrableOn (fun τ => w τ * a τ) S) (hc : IntegrableOn (fun τ => w τ * c τ) S) :
    ∫ τ in S, w τ * (a τ - c τ) = (∫ τ in S, w τ * a τ) - ∫ τ in S, w τ * c τ := by
  rw [← integral_sub ha hc]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-! ## (3.39)–(3.43): the linearised flow and value identities -/

/-- Cochrane (2023), (3.39)–(3.40), p. 76: a constant value `V̄` with constant return `r` and
constant surplus `s̄` solves the flow `V' = V·R' − s` (here `R'` is the instantaneous real return)
iff `s̄ = rV̄`. -/
theorem steady_state_iff (Vbar r sbar : ℝ) :
    (∀ τ : ℝ, HasDerivAt (fun _ : ℝ => Vbar) (Vbar * r - sbar) τ) ↔ sbar = r * Vbar := by
  constructor
  · intro h
    have := (hasDerivAt_const (0 : ℝ) Vbar).unique (h 0)
    linarith
  · intro h τ
    have : Vbar * r - sbar = 0 := by rw [h]; ring
    rw [this]
    exact hasDerivAt_const τ Vbar

/-- Cochrane (2023), (3.40), p. 76: the exact derivative of the flow map `(V, R', s) ↦ V R' − s`
of (3.39) at the steady state `(V̄, r, rV̄)` is `(dV, dR', ds) ↦ r dV + V̄ dR' − ds`. -/
theorem flow_hasFDerivAt (Vbar r : ℝ) :
    ∃ L : ℝ × ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1 * x.2.1 - x.2.2) L (Vbar, r, r * Vbar) ∧
        ∀ h : ℝ × ℝ × ℝ, L h = r * h.1 + Vbar * h.2.1 - h.2.2 := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      ((Vbar, r, r * Vbar) : ℝ × ℝ × ℝ) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((Vbar, r, r * Vbar) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((Vbar, r, r * Vbar) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.snd
  refine ⟨_, (h1.mul h2).sub h3, fun h => ?_⟩
  simp
  ring

/-- Cochrane (2023), (3.40), p. 76: the flow (3.39) equals its linearisation (3.40) plus the
second-order remainder `(V − V̄)(R' − r)`; exact identity, valid when `s̄ = rV̄`. -/
theorem flow_remainder (V Vbar ret r s : ℝ) :
    V * ret - s = (-s + Vbar * (ret - r) + r * V) + (V - Vbar) * (ret - r) := by ring

/-- Cochrane (2023), p. 76: the deviation form of (3.40): with `s̄ = rV̄`,
`−s + V̄(R' − r) + rV = −(s − s̄) + V̄(R' − r) + r(V − V̄)`. -/
theorem flow_deviation_form (V Vbar ret r s : ℝ) :
    -s + Vbar * (ret - r) + r * V = -(s - r * Vbar) + Vbar * (ret - r) + r * (V - Vbar) := by
  ring

/-- Cochrane (2023), (3.42), p. 76: dividing the linearised flow (3.40) by `V̄`, `v = V/V̄` and
`s̃ = s/V̄` obey `v' = rv + (R' − r) − s̃`. -/
theorem normalised_flow {V ret s : ℝ → ℝ} {Vbar r τ : ℝ} (hVbar : Vbar ≠ 0)
    (hV : HasDerivAt V (-s τ + Vbar * (ret τ - r) + r * V τ) τ) :
    HasDerivAt (fun u => V u / Vbar) (r * (V τ / Vbar) + (ret τ - r) - s τ / Vbar) τ :=
  (hV.div_const Vbar).congr_deriv (by field_simp; ring)

/-- Cochrane (2023), (3.43), p. 76: **the linearised value identity iff the TVC.** If
`v' = rv + (R' − r) − s̃` on `[t, ∞)` and `e^{−rτ}(s̃ − (R' − r))` is integrable, then
`e^{−rT}v_T → 0` iff `v_t = ∫_0^∞ e^{−rτ}(s̃_{t+τ} − (R'_{t+τ} − r)) dτ`. -/
theorem linear_value_iff {v ret s : ℝ → ℝ} {r t : ℝ}
    (hv : ∀ τ, t ≤ τ → HasDerivAt v (r * v τ + (ret τ - r) - s τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (ret τ - r))) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0) ↔
      v t = ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s (t + τ) - (ret (t + τ) - r)) :=
  const_rate_tvc_iff (f := fun τ => s τ - (ret τ - r))
    (fun τ hτ => (hv τ hτ).congr_deriv (by ring)) hint

/-- Cochrane (2023), (3.43), p. 76: under the TVC, with the two pieces separately integrable,
`v_t = ∫_0^∞ e^{−rτ} s̃_{t+τ} dτ − ∫_0^∞ e^{−rτ}(R'_{t+τ} − r) dτ` (the integrand index is
`t+τ`, cf. E21). -/
theorem linear_value_split {v ret s : ℝ → ℝ} {r t : ℝ}
    (hv : ∀ τ, t ≤ τ → HasDerivAt v (r * v τ + (ret τ - r) - s τ) τ)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi t))
    (hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (ret τ - r)) (Set.Ioi t))
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)) :
    v t = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s (t + τ)) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (ret (t + τ) - r) := by
  have hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (ret τ - r))) (Set.Ioi t) :=
    (hs.sub hR).congr_fun (fun τ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  rw [(linear_value_iff hv hint).1 htvc]
  exact integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => s (t + τ)) (c := fun τ => ret (t + τ) - r)
    (integrableOn_shift_weighted hs) (integrableOn_shift_weighted (g := fun τ => ret τ - r) hR)

/-- Cochrane (2023), (3.41), p. 76: the linearised value identity in levels: if `V` solves the
linearised flow (3.40) on `[t, ∞)` and `e^{−rT}V_T → 0`, then
`V_t/V̄ = ∫_0^∞ e^{−rτ} s_{t+τ}/V̄ dτ − ∫_0^∞ e^{−rτ}(R'_{t+τ} − r) dτ` (printed integrand index
`dR_t` corrected to `dR_{t+τ}`, E21). -/
theorem value_identity_341 {V ret s : ℝ → ℝ} {Vbar r t : ℝ} (hVbar : Vbar ≠ 0)
    (hV : ∀ τ, t ≤ τ → HasDerivAt V (-s τ + Vbar * (ret τ - r) + r * V τ) τ)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi t))
    (hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (ret τ - r)) (Set.Ioi t))
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * V T) atTop (𝓝 0)) :
    V t / Vbar = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s (t + τ) / Vbar)) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (ret (t + τ) - r) := by
  have hs' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ / Vbar)) (Set.Ioi t) :=
    IntegrableOn.congr_fun (hs.div_const Vbar) (fun τ _ => by ring) measurableSet_Ioi
  have htvc' : Tendsto (fun T => Real.exp (-(r * T)) * (V T / Vbar)) atTop (𝓝 0) := by
    have := htvc.div_const Vbar
    rw [zero_div] at this
    exact this.congr fun T => by ring
  exact linear_value_split (v := fun u => V u / Vbar) (s := fun u => s u / Vbar)
    (fun τ hτ => normalised_flow hVbar (hV τ hτ)) hs' hR htvc'

/-! ## p. 76: nominal and real returns -/

/-- Cochrane (2023), p. 76: `dR = dR^n − π dt`: if a nominal value `X` grows at the nominal return
`R^n` and the price level at the inflation rate `π`, the real value `X/P` grows at `R^n − π`. -/
theorem real_return_of_nominal {X P : ℝ → ℝ} {Rn infl τ : ℝ}
    (hX : HasDerivAt X (Rn * X τ) τ) (hP : HasDerivAt P (infl * P τ) τ) (hPτ : P τ ≠ 0) :
    HasDerivAt (fun u => X u / P u) ((Rn - infl) * (X τ / P τ)) τ :=
  (hX.div hP hPτ).congr_deriv (by field_simp)

/-- Cochrane (2023), p. 76: `d(1/P)/(1/P) = −dP/P` when the price level has no jumps. -/
theorem inv_price_growth {P : ℝ → ℝ} {infl τ : ℝ} (hP : HasDerivAt P (infl * P τ) τ)
    (hPτ : P τ ≠ 0) : HasDerivAt (fun u => 1 / P u) (-infl * (1 / P τ)) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div hP hPτ
  exact h.congr_deriv (by field_simp; ring)

/-! ## p. 77: AR(1) surpluses (E18) -/

/-- Cochrane (2023), p. 77 (corrected, E18): `s_τ = e^{−ητ}s_0` solves `ds = −ηs dt`. -/
theorem ar1_hasDerivAt (η s0 τ : ℝ) :
    HasDerivAt (fun u => Real.exp (-(η * u)) * s0) (-η * (Real.exp (-(η * τ)) * s0)) τ :=
  ((hasDerivAt_expDisc η τ).mul_const s0).congr_deriv (by ring)

/-- Cochrane (2023), p. 77: every solution of `s' = −ηs` is `s_τ = e^{−ητ}s_0` (so
`E_t s_{t+τ} = e^{−ητ}s_t` with no constant, E18). -/
theorem ar1_unique {s : ℝ → ℝ} {η : ℝ} (hs : ∀ τ, HasDerivAt s (-η * s τ) τ) (τ : ℝ) :
    s τ = Real.exp (-(η * τ)) * s 0 := by
  have hG : ∀ u, HasDerivAt (fun x => Real.exp (η * x) * s x) 0 u := by
    intro u
    have he : HasDerivAt (fun x => Real.exp (η * x)) (η * Real.exp (η * u)) u :=
      (HasDerivAt.exp ((hasDerivAt_id' u).const_mul η)).congr_deriv (by ring)
    exact (he.mul (hs u)).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun u => (hG u).differentiableAt)
    (fun u => (hG u).deriv) τ 0
  simp only [mul_zero, Real.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Real.exp_add]
  simp

/-- Cochrane (2023), p. 77 (E18): the printed `E_t s_{t+τ} = e^{−ητ}s_t + s̄` is inconsistent with
`ds = −ηs dt` unless `s̄ = 0`: for `η ≠ 0`, `s̄ ≠ 0` the path `e^{−ητ}s_0 + s̄` never satisfies the
AR(1) law of motion. -/
theorem ar1_printed_not_solution {η s0 c : ℝ} (hη : η ≠ 0) (hc : c ≠ 0) (τ : ℝ) :
    ¬ HasDerivAt (fun u => Real.exp (-(η * u)) * s0 + c)
      (-η * (Real.exp (-(η * τ)) * s0 + c)) τ := by
  intro h
  have h2 := (ar1_hasDerivAt η s0 τ).add_const c
  have := h.unique h2
  have : η * c = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact hη h
  · exact hc h

/-- Cochrane (2023), p. 77: the AR(1) present-value integrand `e^{−rτ}e^{−ητ}s_0` is integrable
on `(0, ∞)` when `r + η > 0`. -/
theorem ar1_integrable {r η s0 : ℝ} (h : 0 < r + η) :
    IntegrableOn (fun τ => Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * s0)) (Set.Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (a := -(r + η)) (by linarith) 0).mul_const s0
  refine IntegrableOn.congr_fun hi (fun τ _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 77: the AR(1) present value
`∫_0^∞ e^{−rτ} e^{−ητ} s_t dτ = s_t/(r + η)` (for `r + η > 0`). -/
theorem ar1_pv {r η s0 : ℝ} (h : 0 < r + η) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * s0) = s0 / (r + η) := by
  have hI := integral_exp_mul_Ioi (a := -(r + η)) (by linarith) 0
  have : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * s0) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r + η) * τ)) * s0 := by
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [this, hI]
  have hne : r + η ≠ 0 := h.ne'
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- Cochrane (2023), p. 77: **news about an AR(1) surplus.** If the surplus follows `ds = −ηs dt`
on the old and on the new perfect-foresight path, and the news raises `s_t` by `σ`, the present
value of surpluses rises by `σ/(r + η)`. -/
theorem ar1_news {r η σ : ℝ} {sOld sNew : ℝ → ℝ} (h : 0 < r + η)
    (hOld : ∀ τ, HasDerivAt sOld (-η * sOld τ) τ) (hNew : ∀ τ, HasDerivAt sNew (-η * sNew τ) τ)
    (hσ : sNew 0 - sOld 0 = σ) :
    (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * sNew τ) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * sOld τ = σ / (r + η) := by
  have e1 : (fun τ => Real.exp (-(r * τ)) * sNew τ) =
      fun τ => Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * sNew 0) :=
    funext fun τ => by rw [ar1_unique hNew τ]
  have e0 : (fun τ => Real.exp (-(r * τ)) * sOld τ) =
      fun τ => Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * sOld 0) :=
    funext fun τ => by rw [ar1_unique hOld τ]
  rw [e1, e0, ar1_pv h, ar1_pv h, ← hσ]
  ring

/-! ## (3.47): bond prices and returns with geometric maturity -/

/-- Cochrane (2023), p. 77: the price of a bond with coupons `e^{−ωτ}` at yield `y` is
`Q = ∫_0^∞ e^{−τy} e^{−ωτ} dτ = 1/(ω + y)` (for `ω + y > 0`). -/
theorem bond_price_yield {ω y : ℝ} (h : 0 < ω + y) :
    ∫ τ in Set.Ioi 0, Real.exp (-(τ * y)) * Real.exp (-(ω * τ)) = 1 / (ω + y) := by
  have hI := integral_exp_mul_Ioi (a := -(ω + y)) (by linarith) 0
  have : ∫ τ in Set.Ioi 0, Real.exp (-(τ * y)) * Real.exp (-(ω * τ)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(ω + y) * τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [← Real.exp_add]
    ring_nf
  rw [this, hI]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- Cochrane (2023), (3.47), pp. 77–78: the holding return over `[t, t+Δ]` of a geometric bond,
`(Δ + e^{−ωΔ} Q_{t+Δ} − Q_t)/(Q_t Δ)`, converges as `Δ → 0` to the instantaneous return
`(1 + Q')/Q − ω` (the first form of (3.47)). -/
theorem holding_return_tendsto {Q : ℝ → ℝ} {Q' ω t : ℝ} (hQ : HasDerivAt Q Q' t)
    (hQt : Q t ≠ 0) :
    Tendsto (fun Δ => (Δ + Real.exp (-(ω * Δ)) * Q (t + Δ) - Q t) / (Q t * Δ)) (𝓝[≠] 0)
      (𝓝 ((1 + Q') / Q t - ω)) := by
  have hQs : HasDerivAt (fun Δ => Q (t + Δ)) Q' 0 :=
    HasDerivAt.comp_const_add t 0 (by rwa [add_zero])
  have hφ : HasDerivAt (fun Δ => Δ + Real.exp (-(ω * Δ)) * Q (t + Δ))
      (1 + (-ω * Real.exp (-(ω * 0)) * Q (t + 0) + Real.exp (-(ω * 0)) * Q')) 0 :=
    HasDerivAt.add (hasDerivAt_id' 0) ((hasDerivAt_expDisc ω 0).mul hQs)
  have h := (hφ.tendsto_slope_zero).div_const (Q t)
  simp only [mul_zero, neg_zero, Real.exp_zero, add_zero, zero_add, one_mul, mul_one] at h
  have hlim : (1 + (-ω * Q t + Q')) / Q t = (1 + Q') / Q t - ω := by field_simp; ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  have hΔ' : Δ ≠ 0 := hΔ
  simp only [smul_eq_mul]
  field_simp

/-- Cochrane (2023), (3.47), p. 78: when `Q_t = 1/(ω + y_t)`, the instantaneous return is
`(1 + Q')/Q − ω = y + Q'/Q` (the second form of (3.47)). -/
theorem return_eq_yield {Q Q' ω y : ℝ} (hQ : Q = 1 / (ω + y)) :
    (1 + Q') / Q - ω = y + Q' / Q := by
  subst hQ
  field_simp
  ring

/-- Cochrane (2023), p. 78: the return definition (3.47) is equivalent to the identity
`Q dR^n = 1 dt + dQ − ωQ dt`. -/
theorem return_identity_iff {Q Q' ω Rn : ℝ} (hQ : Q ≠ 0) :
    Rn = (1 + Q') / Q - ω ↔ Q * Rn = 1 + Q' - ω * Q := by
  constructor
  · intro h; rw [h]; field_simp
  · intro h; field_simp; linarith

/-! ## (3.48)–(3.49): the linearised bond price (E19) -/

/-- Cochrane (2023), p. 78: the steady state `R^n = r`, `dQ = 0`, `Q̄ = 1/(r + ω)` satisfies the
bond-return identity `Q R^n − 1 − Q' + ωQ = 0`. -/
theorem bond_steady_state {r ω : ℝ} (h : r + ω ≠ 0) :
    1 / (r + ω) * r - 1 - 0 + ω * (1 / (r + ω)) = 0 := by
  field_simp; ring

/-- Cochrane (2023), p. 78: the exact derivative of the bond-return map
`(Q, Q', R^n) ↦ Q R^n − 1 − Q' + ωQ` at the steady state `(Q̄, 0, r)`, `Q̄ = 1/(r+ω)`, is
`(dQ, dQ', dR^n) ↦ (r + ω) dQ − dQ' + Q̄ dR^n`. -/
theorem bond_hasFDerivAt (r ω : ℝ) :
    ∃ L : ℝ × ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1 * x.2.2 - 1 - x.2.1 + ω * x.1) L
        (1 / (r + ω), 0, r) ∧
        ∀ h : ℝ × ℝ × ℝ, L h = (r + ω) * h.1 - h.2.1 + 1 / (r + ω) * h.2.2 := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      ((1 / (r + ω), 0, r) : ℝ × ℝ × ℝ) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((1 / (r + ω), 0, r) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      ((1 / (r + ω), 0, r) : ℝ × ℝ × ℝ) := hasFDerivAt_snd.snd
  refine ⟨_, (((h1.mul h3).sub_const 1).sub h2).add (h1.const_mul ω), fun h => ?_⟩
  simp
  ring

/-- Cochrane (2023), (3.48), p. 78: the linearised bond identity
`(r+ω)(Q − Q̄) − Q' + Q̄(R^n − r) = 0` is equivalent, with `q = Q/Q̄`, `q' = Q'/Q̄`, to
`q' = (R^n − r) + (ω + r)(q − 1)`. -/
theorem bond_linear_iff {r ω Q Q' Rn : ℝ} (h : 0 < r + ω) :
    (r + ω) * (Q - 1 / (r + ω)) - Q' + 1 / (r + ω) * (Rn - r) = 0 ↔
      Q' / (1 / (r + ω)) = (Rn - r) + (ω + r) * (Q / (1 / (r + ω)) - 1) := by
  have hne : r + ω ≠ 0 := h.ne'
  constructor
  · intro h0
    field_simp
    field_simp at h0
    linarith
  · intro h0
    field_simp at h0
    field_simp
    linarith

/-- Cochrane (2023), p. 78 (corrected, E19): (3.48) is equivalent to
`R^n − r = q' + (r + ω)(1 − q)`. -/
theorem bond_linear_corrected_line {r ω q q' Rn : ℝ} :
    q' = (Rn - r) + (ω + r) * (q - 1) ↔ Rn - r = q' + (r + ω) * (1 - q) := by
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 78 (E19): the printed intermediate line
`R^n − r = q' − (r + ω)(1 − q)` together with (3.48) forces `q = 1`, so it is not equivalent to
(3.48) off the steady state. -/
theorem printed_line_forces_steady {r ω q q' Rn : ℝ} (h : r + ω ≠ 0)
    (h348 : q' = (Rn - r) + (ω + r) * (q - 1)) (hprinted : Rn - r = q' - (r + ω) * (1 - q)) :
    q = 1 := by
  have : (r + ω) * (q - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 h
  · linarith

/-- Cochrane (2023), p. 78 (E19): a point satisfying (3.48) but violating the printed line:
`q = 2`, `R^n = r`, `q' = r + ω`. -/
theorem printed_line_counterexample {r ω : ℝ} (h : 0 < r + ω) :
    (r + ω) = (r - r) + (ω + r) * (2 - 1) ∧ ¬ (r - r = (r + ω) - (r + ω) * (1 - 2)) := by
  constructor
  · ring
  · intro h'; linarith

/-- Cochrane (2023), (3.49), p. 78: **the bond price forward solution iff the TVC.** If
`q' = (R^n − r) + (ω + r)(q − 1)` on `[t, ∞)` and `e^{−(r+ω)τ}(R^n_τ − r)` is integrable, then
`e^{−(r+ω)T}(q_T − 1) → 0` iff `q_t = 1 − ∫_0^∞ e^{−(r+ω)τ}(R^n_{t+τ} − r) dτ`. -/
theorem bond_price_forward_iff {q Rn : ℝ → ℝ} {r ω t : ℝ}
    (hq : ∀ τ, t ≤ τ → HasDerivAt q ((Rn τ - r) + (r + ω) * (q τ - 1)) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn τ - r)) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-((r + ω) * T)) * (q T - 1)) atTop (𝓝 0) ↔
      q t = 1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r) := by
  have hx : ∀ τ, t ≤ τ → HasDerivAt (fun u => q u - 1)
      ((r + ω) * (q τ - 1) - (-(Rn τ - r))) τ :=
    fun τ hτ => ((hq τ hτ).sub_const 1).congr_deriv (by ring)
  have hint' : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (-(Rn τ - r))) (Set.Ioi t) :=
    hint.neg.congr_fun (fun τ _ => by simp only [Pi.neg_apply]; ring) measurableSet_Ioi
  rw [const_rate_tvc_iff (V := fun u => q u - 1) (f := fun τ => -(Rn τ - r)) hx hint']
  have : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * -(Rn (t + τ) - r) =
      -∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r) := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [this]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 78: a path bounded on `[t, ∞)` satisfies the transversality condition
`e^{−aT}x_T → 0` for every `a > 0`. -/
theorem tvc_of_bounded {x : ℝ → ℝ} {a t K : ℝ} (ha : 0 < a) (hb : ∀ T, t ≤ T → |x T| ≤ K) :
    Tendsto (fun T => Real.exp (-(a * T)) * x T) atTop (𝓝 0) := by
  have he : Tendsto (fun T => Real.exp (-(a * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  have hK := he.mul_const K
  rw [zero_mul] at hK
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb T hT) (Real.exp_pos _).le

/-- Cochrane (2023), (3.49), p. 78: **uniqueness**: every solution of (3.48) that is bounded on
`[t, ∞)` is the forward solution (3.49), at every date `t' ≥ t` (`r + ω > 0`). -/
theorem bond_price_forward_bounded {q Rn : ℝ → ℝ} {r ω t K : ℝ} (h : 0 < r + ω)
    (hq : ∀ τ, t ≤ τ → HasDerivAt q ((Rn τ - r) + (r + ω) * (q τ - 1)) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn τ - r)) (Set.Ioi t))
    (hb : ∀ T, t ≤ T → |q T| ≤ K) (t' : ℝ) (ht' : t ≤ t') :
    q t' = 1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t' + τ) - r) := by
  refine (bond_price_forward_iff (fun τ hτ => hq τ (le_trans ht' hτ))
    (hint.mono_set (Set.Ioi_subset_Ioi ht'))).1 ?_
  refine tvc_of_bounded (t := t) (K := K + 1) h fun T hT => ?_
  have := hb T hT
  calc |q T - 1| ≤ |q T| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ K + 1 := by rw [abs_one]; linarith

/-- Cochrane (2023), (3.49), p. 78: the forward-solution bond price
`q^F_t = 1 − ∫_0^∞ e^{−(r+ω)τ}(R^n_{t+τ} − r) dτ`. -/
noncomputable def bondForward (r ω : ℝ) (Rn : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r)

/-- Cochrane (2023), (3.49), p. 78: **existence**: for a continuous return path with
`|R^n − r| ≤ K`, the forward solution solves (3.48) at every date and is bounded,
`|q^F − 1| ≤ K/(r + ω)`; with `bond_price_forward_bounded` it is the unique bounded solution. -/
theorem bondForward_spec {Rn : ℝ → ℝ} {r ω K : ℝ} (h : 0 < r + ω) (hc : Continuous Rn)
    (hb : ∀ τ, |Rn τ - r| ≤ K) :
    (∀ τ, HasDerivAt (bondForward r ω Rn)
      ((Rn τ - r) + (r + ω) * (bondForward r ω Rn τ - 1)) τ) ∧
    ∀ τ, |bondForward r ω Rn τ - 1| ≤ K / (r + ω) := by
  set a := r + ω with ha
  have hmeas : ∀ u : ℝ, AEStronglyMeasurable (fun τ => Real.exp (-(a * τ)) * (Rn τ - r))
      (volume.restrict (Set.Ioi u)) := fun u =>
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      (hc.sub continuous_const)).aestronglyMeasurable
  have hdom : ∀ u : ℝ, IntegrableOn (fun τ => Real.exp (-(a * τ)) * (Rn τ - r)) (Set.Ioi u) := by
    intro u
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -a) (by linarith) u).const_mul K)
      (hmeas u) (ae_of_all _ fun τ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm K, neg_mul]
    exact mul_le_mul_of_nonneg_left (hb τ) (Real.exp_pos _).le
  have hint : ∀ u : ℝ,
      IntegrableOn (fun τ => Real.exp (-(a * τ)) * (-(Rn τ - r))) (Set.Ioi u) := fun u =>
    (hdom u).neg.congr_fun (fun τ _ => by simp only [Pi.neg_apply]; ring) measurableSet_Ioi
  obtain ⟨hd, -⟩ := valuation_exists (Λ := fun u => Real.exp (-(a * u))) (r := fun _ => a)
    (f := fun τ => -(Rn τ - r)) (fun τ => hasDerivAt_expDisc a τ) (fun τ => Real.exp_pos _)
    (by fun_prop) hint
  have heq : ∀ u, bondForward r ω Rn u =
      1 + ∫ x in Set.Ioi u, Real.exp (-(a * x)) / Real.exp (-(a * u)) * -(Rn x - r) := by
    intro u
    rw [bondForward, integral_ratio_eq, shift_weighted (fun τ => -(Rn τ - r)) a u]
    rw [← ha]
    have : ∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * -(Rn (u + τ) - r) =
        -∫ τ in Set.Ioi 0, Real.exp (-(a * τ)) * (Rn (u + τ) - r) := by
      rw [← integral_neg]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      simp only
      ring
    rw [this]
    ring
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · rw [show bondForward r ω Rn = fun u =>
      1 + ∫ x in Set.Ioi u, Real.exp (-(a * x)) / Real.exp (-(a * u)) * -(Rn x - r) from
      funext heq]
    exact ((hd τ).const_add 1).congr_deriv (by beta_reduce; ring)
  · have hbound : ‖∫ x in Set.Ioi 0, Real.exp (-(a * x)) * (Rn (τ + x) - r)‖ ≤
        ∫ x in Set.Ioi 0, K * Real.exp (-a * x) := by
      refine norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).const_mul K)
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm K, neg_mul]
      exact mul_le_mul_of_nonneg_left (hb (τ + x)) (Real.exp_pos _).le
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hbound
    simp only [mul_zero, Real.exp_zero] at hbound
    have hval : K * (-1 / -a) = K / a := by field_simp
    rw [hval, Real.norm_eq_abs] at hbound
    rw [bondForward, ← ha]
    calc |1 - (∫ x in Set.Ioi 0, Real.exp (-(a * x)) * (Rn (τ + x) - r)) - 1|
        = |∫ x in Set.Ioi 0, Real.exp (-(a * x)) * (Rn (τ + x) - r)| := by
          rw [show ∀ z : ℝ, 1 - z - 1 = -z from fun z => by ring, abs_neg]
      _ ≤ K / a := hbound

/-! ## The value of debt at the news date and the unexpected bond return -/

/-- Cochrane (2023), (3.35), (3.46), pp. 75–77: the exact derivative of the value of debt
`V = Q·b` (bond price times real face value), normalised by `V̄ = Q̄ b̄`, at the steady state:
`(dQ, db) ↦ dQ/Q̄ + db/b̄`, i.e. `v − 1 = (q − 1) + (β − 1)` to first order. -/
theorem value_hasFDerivAt {Qbar bbar : ℝ} (hQ : Qbar ≠ 0) (hb : bbar ≠ 0) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun x : ℝ × ℝ => x.1 * x.2 * (1 / (Qbar * bbar))) L (Qbar, bbar) ∧
        ∀ h : ℝ × ℝ, L h = h.1 / Qbar + h.2 / bbar := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ)
      ((Qbar, bbar) : ℝ × ℝ) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((Qbar, bbar) : ℝ × ℝ) := hasFDerivAt_snd
  refine ⟨_, HasFDerivAt.mul_const (HasFDerivAt.mul h1 h2) (1 / (Qbar * bbar)), fun h => ?_⟩
  simp
  field_simp
  ring

/-- Cochrane (2023), pp. 75–77: the exact decomposition
`Qb/(Q̄b̄) − 1 = (q − 1) + (β − 1) + (q − 1)(β − 1)` with `q = Q/Q̄`, `β = b/b̄`; the last term is
the second-order remainder dropped by the linearisation. -/
theorem value_remainder {Q b Qbar bbar : ℝ} (hQ : Qbar ≠ 0) (hb : bbar ≠ 0) :
    Q * b / (Qbar * bbar) - 1 =
      (Q / Qbar - 1) + (b / bbar - 1) + (Q / Qbar - 1) * (b / bbar - 1) := by
  field_simp
  ring

/-- Cochrane (2023), pp. 77–78: **the unexpected bond return is the bond-price jump.** On the
combined path (old price `Q₀` before the news date `t`, new price `Q₁` from `t` on), the holding
return over `[t − h, t + h]`, `(2h + e^{−2ωh}Q₁(t+h) − Q₀(t−h))/Q₀(t−h)`, converges as `h → 0`
to `(Q₁(t) − Q₀(t))/Q₀(t)`: the coupon accrual vanishes and only the revaluation remains. -/
theorem news_return_tendsto {Q₀ Q₁ : ℝ → ℝ} {ω t : ℝ} (h₀ : ContinuousAt Q₀ t)
    (h₁ : ContinuousAt Q₁ t) (hpos : Q₀ t ≠ 0) :
    Tendsto (fun h => (2 * h + Real.exp (-(ω * (2 * h))) * Q₁ (t + h) - Q₀ (t - h)) / Q₀ (t - h))
      (𝓝 0) (𝓝 ((Q₁ t - Q₀ t) / Q₀ t)) := by
  have hp : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 t) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_add t
  have hm : Tendsto (fun h : ℝ => t - h) (𝓝 0) (𝓝 t) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_sub t
  have hQ1 := h₁.tendsto.comp hp
  have hQ0 := h₀.tendsto.comp hm
  have he : Tendsto (fun h : ℝ => Real.exp (-(ω * (2 * h)))) (𝓝 0) (𝓝 1) := by
    have : Continuous fun h : ℝ => Real.exp (-(ω * (2 * h))) := by fun_prop
    simpa using this.tendsto 0
  have h2 : Tendsto (fun h : ℝ => 2 * h) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2
  have hnum := (h2.add (he.mul hQ1)).sub hQ0
  have hlim := hnum.div hQ0 hpos
  rw [zero_add, one_mul] at hlim
  exact hlim

/-! ## News between two perfect-foresight equilibria: (3.46), (3.50), (3.51) -/

namespace Eqm

variable (r ω t : ℝ) (v q b Rn infl s : ℝ → ℝ)

/-- Cochrane (2023), (3.42)–(3.43), (3.47)–(3.49), pp. 76–78: a perfect-foresight path of the
linearised model from date `t` on: value `v`, bond price `q`, linearised real face value `b`
(predetermined: `B` is predetermined and `P` does not jump), nominal bond return `R^n`,
inflation `π` (`infl`), surplus `s̃`; real return `R' = R^n − π` (p. 76). Fields: the flow (3.42),
the bond identity (3.48), the value split `v = q + b − 1` at `t` (`value_hasFDerivAt`), the two
transversality conditions and integrability of the discounted pieces. -/
structure LinearEqm where
  flow : ∀ τ, t ≤ τ → HasDerivAt v (r * v τ + (Rn τ - infl τ - r) - s τ) τ
  bond : ∀ τ, t ≤ τ → HasDerivAt q ((Rn τ - r) + (r + ω) * (q τ - 1)) τ
  value : v t = q t + b t - 1
  tvcV : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)
  tvcQ : Tendsto (fun T => Real.exp (-((r + ω) * T)) * (q T - 1)) atTop (𝓝 0)
  intS : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi t)
  intR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (Rn τ - infl τ - r)) (Set.Ioi t)
  intN : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn τ - r)) (Set.Ioi t)

end Eqm

/-- Cochrane (2023), p. 76: the steady state `v = q = b = 1`, `R^n = r`, `π = 0`, `s̃ = r` is a
linearised equilibrium (for `r > 0`), so `Eqm.LinearEqm` is inhabited. -/
theorem steady_state_eqm {r ω t : ℝ} (hr : 0 < r) :
    Eqm.LinearEqm r ω t (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => r) (fun _ => 0)
      (fun _ => r) := by
  have hz : ∀ f : ℝ → ℝ, (∀ τ, f τ = 0) → IntegrableOn f (Set.Ioi t) := fun f hf =>
    IntegrableOn.congr_fun (integrableOn_zero (s := Set.Ioi t) (μ := volume))
      (fun τ _ => (hf τ).symm) measurableSet_Ioi
  refine ⟨fun τ _ => (hasDerivAt_const τ (1 : ℝ)).congr_deriv (by ring),
    fun τ _ => (hasDerivAt_const τ (1 : ℝ)).congr_deriv (by ring), by ring,
    tvc_of_bounded (t := t) (K := 1) hr (fun T _ => by simp), ?_, ?_,
    hz _ (fun τ => by ring), hz _ (fun τ => by ring)⟩
  · simp
  · refine IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Ioi (a := -r) (by linarith) t).mul_const r) (fun τ _ => ?_)
      measurableSet_Ioi
    simp only [neg_mul]

/-- Cochrane (2023), (3.43), p. 76: in a linearised equilibrium,
`v_t = ∫_0^∞ e^{−rτ}s̃_{t+τ}dτ − ∫_0^∞ e^{−rτ}(R'_{t+τ} − r)dτ`. -/
theorem eqm_value {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ}
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    v t = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s (t + τ)) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Rn (t + τ) - infl (t + τ) - r) :=
  linear_value_split (ret := fun τ => Rn τ - infl τ) E.flow E.intS E.intR E.tvcV

/-- Cochrane (2023), (3.49), p. 78: in a linearised equilibrium,
`q_t = 1 − ∫_0^∞ e^{−(r+ω)τ}(R^n_{t+τ} − r)dτ`. -/
theorem eqm_bond {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ}
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    q t = 1 - ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - r) :=
  (bond_price_forward_iff E.bond E.intN).1 E.tvcQ

/-- Cochrane (2023), (3.51), p. 78: with `ω ≥ 0`, the real-return term discounted at `r + ω`
is integrable (shifted form). -/
theorem eqm_int_real_bond {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ} (hω : 0 ≤ ω)
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * (Rn (t + τ) - infl (t + τ) - r))
      (Set.Ioi 0) := by
  have hR := integrableOn_shift_weighted (g := fun τ => Rn τ - infl τ - r) E.intR
  have hm : AEStronglyMeasurable (fun τ : ℝ => Real.exp (-(ω * τ)))
      (volume.restrict (Set.Ioi 0)) := by
    have : Continuous fun τ : ℝ => Real.exp (-(ω * τ)) := by fun_prop
    exact this.aestronglyMeasurable
  have hbd : ∀ᵐ τ ∂(volume.restrict (Set.Ioi (0 : ℝ))), ‖Real.exp (-(ω * τ))‖ ≤ 1 := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ hτ => ?_)
    have hτ' : (0 : ℝ) < τ := hτ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith
  refine IntegrableOn.congr_fun (Integrable.bdd_mul hR hm hbd) (fun τ _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), (3.50)–(3.51), p. 78: with `ω ≥ 0`, inflation discounted at `r + ω` is
integrable (shifted form): `π = (R^n − r) − (R^n − π − r)`. -/
theorem eqm_int_infl {r ω t : ℝ} {v q b Rn infl s : ℝ → ℝ} (hω : 0 ≤ ω)
    (E : Eqm.LinearEqm r ω t v q b Rn infl s) :
    IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * infl (t + τ)) (Set.Ioi 0) := by
  have hN := integrableOn_shift_weighted (g := fun τ => Rn τ - r) E.intN
  refine IntegrableOn.congr_fun (hN.sub (eqm_int_real_bond hω E)) (fun τ _ => ?_)
    measurableSet_Ioi
  simp only [Pi.sub_apply]
  ring

/-- Cochrane (2023), p. 77: `Δ_t dv_t = Δ_t dR^n_t`: with the real face value predetermined
(`B` predetermined, no price-level jump), the news-date jump in the value of debt equals the
jump in the bond price, i.e. the unexpected bond return (`news_return_tendsto`). -/
theorem news_value_eq_bond {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) :
    v₁ t - v₀ t = q₁ t - q₀ t := by
  rw [E₁.value, E₀.value, hb]; ring

/-- Cochrane (2023), (3.46), p. 77: **the value news identity.** Between an old and a new
equilibrium that share the predetermined face value at `t`, the unexpected bond return
`Δq_t` equals the news in discounted surpluses minus the news in discounted real returns:
`Δq_t = ∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ − ∫_0^∞ e^{−rτ}ΔR'_{t+τ}dτ`. -/
theorem news_value {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) :
    q₁ t - q₀ t =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ))) -
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
          ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
  rw [← news_value_eq_bond E₀ E₁ hb, eqm_value E₁, eqm_value E₀]
  have hS := integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => s₁ (t + τ)) (c := fun τ => s₀ (t + τ)) (S := Set.Ioi 0)
    (integrableOn_shift_weighted E₁.intS) (integrableOn_shift_weighted E₀.intS)
  have hR := integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => Rn₁ (t + τ) - infl₁ (t + τ) - r)
    (c := fun τ => Rn₀ (t + τ) - infl₀ (t + τ) - r) (S := Set.Ioi 0)
    (integrableOn_shift_weighted (g := fun τ => Rn₁ τ - infl₁ τ - r) E₁.intR)
    (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - infl₀ τ - r) E₀.intR)
  have hR' : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ) - r) - (Rn₀ (t + τ) - infl₀ (t + τ) - r)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  beta_reduce at hS hR
  linarith

/-- Cochrane (2023), (3.50), p. 78: **the bond-return news identity.**
`Δq_t = −∫_0^∞ e^{−(r+ω)τ}ΔR^n_{t+τ}dτ`. -/
theorem news_bond {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) :
    q₁ t - q₀ t =
      -∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn₁ (t + τ) - Rn₀ (t + τ)) := by
  rw [eqm_bond E₁, eqm_bond E₀]
  have hN := integral_weighted_sub (w := fun τ => Real.exp (-((r + ω) * τ)))
    (a := fun τ => Rn₁ (t + τ) - r) (c := fun τ => Rn₀ (t + τ) - r) (S := Set.Ioi 0)
    (integrableOn_shift_weighted (g := fun τ => Rn₁ τ - r) E₁.intN)
    (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - r) E₀.intN)
  have hN' : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
      ((Rn₁ (t + τ) - r) - (Rn₀ (t + τ) - r)) =
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (Rn₁ (t + τ) - Rn₀ (t + τ)) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  beta_reduce at hN
  linarith

/-- Cochrane (2023), (3.50), p. 78: the second form,
`Δq_t = −∫_0^∞ e^{−(r+ω)τ}(ΔR'_{t+τ} + Δπ_{t+τ})dτ` (`dR^n = dR + π dt`). -/
theorem news_bond_real {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) :
    q₁ t - q₀ t =
      -∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        (((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) +
          (infl₁ (t + τ) - infl₀ (t + τ))) := by
  rw [news_bond E₀ E₁]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), (3.51), p. 78: **the weighted-inflation identity.** For `ω ≥ 0`,
`∫_0^∞ e^{−(r+ω)τ}Δπ_{t+τ}dτ = −∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ
  + ∫_0^∞ (e^{−rτ} − e^{−(r+ω)τ})ΔR'_{t+τ}dτ`. -/
theorem news_weighted_inflation {r ω t : ℝ}
    {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ} (hω : 0 ≤ ω)
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (infl₁ (t + τ) - infl₀ (t + τ)) =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ))) +
        ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
          ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
  have hV := news_value E₀ E₁ hb
  have hB := news_bond_real E₀ E₁
  -- integrability of the shifted pieces
  have iR : IntegrableOn (fun τ => Real.exp (-(r * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_shift_weighted (g := fun τ => Rn₁ τ - infl₁ τ - r) E₁.intR).sub
        (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - infl₀ τ - r) E₀.intR))
      (fun τ _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have iM : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((eqm_int_real_bond hω E₁).sub (eqm_int_real_bond hω E₀)) (fun τ _ => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have iP : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) *
      (infl₁ (t + τ) - infl₀ (t + τ))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun ((eqm_int_infl hω E₁).sub (eqm_int_infl hω E₀))
      (fun τ _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hsplitB : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        (((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) +
          (infl₁ (t + τ) - infl₀ (t + τ))) =
      (∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) +
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (infl₁ (t + τ) - infl₀ (t + τ)) := by
    rw [← integral_add iM iP]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  have hsplitW : ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) -
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
    rw [← integral_sub iR iM]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [hsplitW]
  rw [hsplitB] at hB
  linarith

/-- Cochrane (2023), pp. 78–79: if the bond price does not move at the news date (`Δq_t = 0`, as
for instantaneous debt, whose value is pinned at par), any fiscal news is exactly matched by
news in discounted real returns:
`∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ = ∫_0^∞ e^{−rτ}ΔR'_{t+τ}dτ`. -/
theorem short_debt_news {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) (hb : b₁ t = b₀ t) (hq : q₁ t = q₀ t) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
  have := news_value E₀ E₁ hb
  rw [hq, sub_self] at this
  linarith

/-! ## Short-term debt is `ω → ∞`, not `ω = 0` (E20) -/

/-- Cochrane (2023), (3.51), p. 78: a measurable inflation news path bounded by `K` on `(0, ∞)`
gives a genuinely integrable left-hand side of (3.51) whenever `r + ω > 0`. -/
theorem short_limit_integrable {dπ : ℝ → ℝ} {r ω K : ℝ} (h : 0 < r + ω)
    (hm : AEStronglyMeasurable dπ (volume.restrict (Set.Ioi 0)))
    (hb : ∀ τ, 0 < τ → |dπ τ| ≤ K) :
    IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) * dπ τ) (Set.Ioi 0) := by
  have hint := (integrableOn_exp_mul_Ioi (a := -(r + ω)) (by linarith) 0).const_mul K
  have hc : Continuous fun τ : ℝ => Real.exp (-((r + ω) * τ)) := by fun_prop
  refine Integrable.mono' hint (hc.aestronglyMeasurable.mul hm)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hb τ hτ) (Real.exp_pos _).le

/-- Cochrane (2023), pp. 78–79 (E20): **the short-debt limit.** For a family of inflation news
paths uniformly bounded by `K` on `(0, ∞)`, the left-hand side of (3.51),
`∫_0^∞ e^{−(r+ω)τ}Δπ^ω_τ dτ`, tends to `0` as `ω → ∞` (instantaneous debt). -/
theorem short_limit {dπ : ℝ → ℝ → ℝ} {r K : ℝ}
    (hb : ∀ ω τ, 0 < τ → |dπ ω τ| ≤ K) :
    Tendsto (fun ω => ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ ω τ) atTop (𝓝 0) := by
  have hK : Tendsto (fun ω : ℝ => K / (r + ω)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ r tendsto_id)
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_gt_atTop (-r)] with ω hω
  have ha : 0 < r + ω := by linarith
  have hint := (integrableOn_exp_mul_Ioi (a := -(r + ω)) (by linarith) 0).const_mul K
  have hbound : ‖∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ ω τ‖ ≤
      ∫ τ in Set.Ioi 0, K * Real.exp (-(r + ω) * τ) := by
    refine norm_integral_le_of_norm_le hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm K]
    exact mul_le_mul_of_nonneg_left (hb ω τ hτ) (Real.exp_pos _).le
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hbound
  simp only [mul_zero, Real.exp_zero] at hbound
  have hval : K * (-1 / -(r + ω)) = K / (r + ω) := by field_simp
  rw [hval] at hbound
  exact hbound

/-- Cochrane (2023), pp. 78–79 (E20): the single-path version: for bounded measurable inflation
news, `∫_0^∞ e^{−(r+ω)τ}Δπ_τ dτ → 0` as `ω → ∞`. -/
theorem short_limit_single {dπ : ℝ → ℝ} {r K : ℝ} (hb : ∀ τ, 0 < τ → |dπ τ| ≤ K) :
    Tendsto (fun ω => ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ τ) atTop (𝓝 0) :=
  short_limit (dπ := fun _ => dπ) (fun _ => hb)

/-- Cochrane (2023), pp. 78–79 (E20): in the limit `ω → ∞` the weighted-inflation identity
(3.51) becomes `∫_0^∞ e^{−rτ}Δs̃_τ dτ = ∫_0^∞ e^{−rτ}ΔR'_τ dτ`: if (3.51) holds for all large `ω`
with inflation news uniformly bounded, the fiscal news equals the discount-rate news. -/
theorem short_debt_limit_identity {dπ : ℝ → ℝ → ℝ} {ds dR : ℝ → ℝ} {r K : ℝ}
    (hb : ∀ ω τ, 0 < τ → |dπ ω τ| ≤ K)
    (hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * dR τ) (Set.Ioi 0))
    (hid : ∀ᶠ ω in atTop, ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ ω τ =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ds τ) +
        ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) * dR τ) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ds τ =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * dR τ := by
  set A := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ds τ
  set B := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * dR τ
  have hL := short_limit (r := r) hb
  have hconv : ∀ ω τ, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) * dR τ =
      (1 - Real.exp (-(ω * τ))) * (Real.exp (-(r * τ)) * dR τ) := by
    intro ω τ
    have : Real.exp (-((r + ω) * τ)) = Real.exp (-(ω * τ)) * Real.exp (-(r * τ)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hD : Tendsto (fun ω => ∫ τ in Set.Ioi 0,
      (1 - Real.exp (-(ω * τ))) * (Real.exp (-(r * τ)) * dR τ)) atTop (𝓝 B) := by
    have hlim : ∀ᵐ τ ∂(volume.restrict (Set.Ioi (0 : ℝ))), Tendsto (fun ω =>
        (1 - Real.exp (-(ω * τ))) * (Real.exp (-(r * τ)) * dR τ)) atTop
        (𝓝 (Real.exp (-(r * τ)) * dR τ)) := by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_)
      have he : Tendsto (fun ω => Real.exp (-(ω * τ))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hτ)
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).mul_const
        (Real.exp (-(r * τ)) * dR τ)
      simpa using this
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => ‖Real.exp (-(r * τ)) * dR τ‖) ?_ ?_ hR.norm hlim
    · refine Eventually.of_forall fun ω => ?_
      have hc : Continuous fun τ : ℝ => 1 - Real.exp (-(ω * τ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hR.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 0] with ω hω
      refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : (0 : ℝ) < τ) => ?_)
      rw [norm_mul]
      have h1 : ‖1 - Real.exp (-(ω * τ))‖ ≤ 1 := by
        have hpos := Real.exp_pos (-(ω * τ))
        have hle : Real.exp (-(ω * τ)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      calc ‖1 - Real.exp (-(ω * τ))‖ * ‖Real.exp (-(r * τ)) * dR τ‖
          ≤ 1 * ‖Real.exp (-(r * τ)) * dR τ‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖Real.exp (-(r * τ)) * dR τ‖ := one_mul _
  have hR' : Tendsto (fun ω => -A + ∫ τ in Set.Ioi 0,
      (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) * dR τ) atTop (𝓝 (-A + B)) := by
    refine (hD.const_add (-A)).congr fun ω => ?_
    congr 1
    exact integral_congr_ae (ae_of_all _ fun τ => (hconv ω τ).symm)
  have hL' := hL.congr' (hid.mono fun ω h => h)
  have := tendsto_nhds_unique hL' hR'
  linarith

/-- Cochrane (2023), pp. 78–79 (E20): at `ω = 0` (a perpetuity, coupons `e^{−0·τ} = 1`, price
`1/y`) the left-hand side of (3.51) is **not** zero in general: for `Δπ ≡ 1` it equals
`1/r ≠ 0`. -/
theorem perpetuity_lhs_ne_zero {r : ℝ} (hr : 0 < r) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) = 1 / r ∧
      ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) ≠ 0 := by
  have hI := integral_exp_mul_Ioi (a := -r) (by linarith) 0
  have h : ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) = 1 / r := by
    have : ∫ τ in Set.Ioi 0, Real.exp (-((r + 0) * τ)) * (1 : ℝ) =
        ∫ τ in Set.Ioi 0, Real.exp (-r * τ) := by
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      simp only [add_zero, mul_one, neg_mul]
    rw [this, hI]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  refine ⟨h, ?_⟩
  rw [h]
  exact (one_div_pos.2 hr).ne'

/-- Cochrane (2023), p. 77 and A1 p. 560: `ω = 0` is the perpetuity: the bond price is `1/y`. -/
theorem perpetuity_price {y : ℝ} (hy : 0 < y) :
    ∫ τ in Set.Ioi 0, Real.exp (-(τ * y)) * Real.exp (-(0 * τ)) = 1 / y := by
  have := bond_price_yield (ω := 0) (y := y) (by linarith)
  rwa [zero_add] at this

/-- Cochrane (2023), p. 77 and A1 p. 560: `ω → ∞` is instantaneous debt: the bond price
`1/(ω + y) → 0` while the value of the coupon stream per unit of price, `ω/(ω + y)`, tends to `1`
(the bond matures instantly). -/
theorem instantaneous_limit (y : ℝ) :
    Tendsto (fun ω : ℝ => 1 / (ω + y)) atTop (𝓝 0) ∧
      Tendsto (fun ω : ℝ => ω / (ω + y)) atTop (𝓝 1) := by
  have hT : Tendsto (fun ω : ℝ => ω + y) atTop atTop := tendsto_atTop_add_const_right _ y tendsto_id
  have h1 : Tendsto (fun ω : ℝ => 1 / (ω + y)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hT
  refine ⟨h1, ?_⟩
  have h2 : Tendsto (fun ω : ℝ => 1 - y * (1 / (ω + y))) atTop (𝓝 1) := by
    simpa using (h1.const_mul y).const_sub 1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (-y)] with ω hω
  have : ω + y ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), p. 78: inflation news at the single instant `t` contributes nothing to the
left-hand side of (3.51): changing `Δπ` at one date leaves the integral unchanged. -/
theorem lhs_ignores_one_date {dπ dπ' : ℝ → ℝ} {r ω τ₀ : ℝ} (h : ∀ τ, τ ≠ τ₀ → dπ' τ = dπ τ) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ' τ =
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ τ := by
  have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ τ₀ := by
    rw [ae_iff]
    simp
  refine integral_congr_ae (ae_restrict_of_ae (hne.mono fun τ hτ => ?_))
  simp only [h τ hτ]

end Cochrane.Generality.ContinuousLinear
