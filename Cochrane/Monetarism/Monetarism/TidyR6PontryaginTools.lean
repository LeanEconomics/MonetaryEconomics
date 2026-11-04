/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Tools for Pontryagin necessity in the money-in-utility problem

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 4, §4.1.3,
"A Hamiltonian approach", pp. 640–641 (the problem of Obstfeld (1984)). The general lemmas
behind `TidyR6Pontryagin`; none of them is in Mathlib.

* `integral_dirDeriv_nonpos`: **the first-order condition of a concave program under an
  integral, by monotone convergence.** If `ε ↦ F(x, ε)` is concave on `[0, ε₀]` with right
  derivative `D(x)` at `0`, `F(·, 0)` and `F(·, ε₀)` are integrable, and no `ε ∈ (0, ε₀]` gives
  a well-defined improvement (`∫⁻(F_ε − F_0)⁺ ≤ ∫⁻(F_ε − F_0)⁻`), then `D` is integrable and
  `∫D ≤ 0`. Concavity makes the difference quotients monotone, so no domination hypothesis is
  needed; this is what makes the transversality argument work on an infinite horizon.
* `concave_tangent`: a concave function differentiable at `x > 0` lies below its tangent line
  on `(0, ∞)` (the supergradient inequality).
* `concaveOn_comp_affine`: `ε ↦ f(c + εa)` is concave on `[0, ε₀]` when `f` is concave on
  `(0, ∞)` and the arguments stay positive.
* `enorm_le_ofReal_add`: `‖r‖ₑ ≤ (r)⁺ + (−r)⁺` in `ℝ≥0∞`.
* The bump `bump τ w t = σ((t − τ)/w)` built from Mathlib's `Real.smoothTransition` `σ`, and its
  derivative `rho τ w t = σ'((t − τ)/w)/w`: `hasDerivAt_bump`, `continuous_rho`, `rho_nonneg`,
  `rho_eq_zero_of_lt`, `rho_eq_zero_of_gt`, `integral_rho`.
* `dubois_reymond`: **the du Bois-Reymond lemma** in the form used here: if `G` is continuous on
  `(0, ∞)` and `∫ G·(ρ_{t₁} − ρ_{t₂}) = 0` for all pairs of bumps, `G` is constant on `(0, ∞)`.
-/

namespace Cochrane.Monetarism.TidyR6PontryaginTools

open MeasureTheory Filter Topology

/-- Cochrane (2023), A4 p. 640 (bookkeeping for the Hamiltonian conditions): for a real `r`,
`‖r‖ₑ ≤ ofReal r + ofReal (−r)`. -/
theorem enorm_le_ofReal_add (r : ℝ) : ‖r‖ₑ ≤ ENNReal.ofReal r + ENNReal.ofReal (-r) := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -r ≤ 0), add_zero]
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]

/-- **Cochrane (2023), A4 (4.16)–(4.17), p. 640: the first-order condition of a concave program
under an integral.** Let `ε₀ > 0`; for almost every `x`, `ε ↦ F(x, ε)` is concave on `[0, ε₀]`
with right derivative `D(x)` at `0`; `F(·, ε)` is a.e. strongly measurable for `ε ∈ [0, ε₀]`;
`F(·, 0)` and `F(·, ε₀)` are integrable; and for every `ε ∈ (0, ε₀]` the gain `F(·, ε) − F(·, 0)`
does not have a larger positive than negative part (`∫⁻(·)⁺ ≤ ∫⁻(·)⁻`). Then `D` is integrable
and `∫D ≤ 0`. (Monotone convergence of the concave difference quotients.) -/
theorem integral_dirDeriv_nonpos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ → ℝ} {D : α → ℝ} {ε0 : ℝ} (hε0 : 0 < ε0)
    (hconc : ∀ᵐ x ∂μ, ConcaveOn ℝ (Set.Icc 0 ε0) (F x))
    (hder : ∀ᵐ x ∂μ, HasDerivWithinAt (F x) (D x) (Set.Ici 0) 0)
    (hmeas : ∀ ε ∈ Set.Icc 0 ε0, AEStronglyMeasurable (fun x => F x ε) μ)
    (hint0 : Integrable (fun x => F x 0) μ) (hint1 : Integrable (fun x => F x ε0) μ)
    (hopt : ∀ ε ∈ Set.Ioc 0 ε0,
      ∫⁻ x, ENNReal.ofReal (F x ε - F x 0) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (F x 0 - F x ε) ∂μ) :
    Integrable D μ ∧ ∫ x, D x ∂μ ≤ 0 := by
  set e : ℕ → ℝ := fun n => ε0 / (n + 1) with he
  have he_pos : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have he_le : ∀ n, e n ≤ ε0 := fun n => by
    simp only [he]
    exact div_le_self hε0.le (by have := n.cast_nonneg (α := ℝ); linarith)
  have he_anti : Antitone e := fun n m hnm => by
    simp only [he]
    exact div_le_div_of_nonneg_left hε0.le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have he_lim : Tendsto e atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat ε0)
    refine h.congr fun n => ?_
    simp [he]
  set q : ℕ → α → ℝ := fun n x => (F x (e n) - F x 0) / e n with hq
  have hmem : ∀ n, e n ∈ Set.Icc 0 ε0 := fun n => ⟨(he_pos n).le, he_le n⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 ε0 := ⟨le_rfl, hε0.le⟩
  -- the difference quotients increase as `ε ↓ 0`
  have hq_mono : ∀ᵐ x ∂μ, Monotone fun n => q n x := by
    filter_upwards [hconc] with x hx
    intro n m hnm
    have h := hx.neg.secant_mono h0mem (hmem m) (hmem n) (he_pos m).ne' (he_pos n).ne'
      (he_anti hnm)
    simp only [Pi.neg_apply, sub_zero] at h
    simp only [hq]
    have e1 : (-F x (e m) - -F x 0) / e m = -((F x (e m) - F x 0) / e m) := by ring
    have e2 : (-F x (e n) - -F x 0) / e n = -((F x (e n) - F x 0) / e n) := by ring
    linarith
  -- and converge to the derivative
  have hq_lim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 (D x)) := by
    filter_upwards [hder] with x hx
    have h1 := hasDerivWithinAt_iff_tendsto_slope.mp hx
    have h2 : Tendsto e atTop (𝓝[Set.Ici 0 \ {0}] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨he_lim, Eventually.of_forall fun n =>
        ⟨Set.mem_Ici.mpr (he_pos n).le, (he_pos n).ne'⟩⟩
    refine (h1.comp h2).congr fun n => ?_
    simp [hq, slope_def_field]
  have hq0 : Integrable (q 0) μ := by
    have e0 : q 0 = fun x => (F x ε0 - F x 0) / ε0 := by
      funext x; simp [hq, he]
    rw [e0]; exact (hint1.sub hint0).div_const ε0
  -- each gain is integrable with nonpositive integral
  have hgn : ∀ n, Integrable (fun x => F x (e n) - F x 0) μ ∧
      ∫ x, (F x (e n) - F x 0) ∂μ ≤ 0 := by
    intro n
    have hmeasg : AEStronglyMeasurable (fun x => F x (e n) - F x 0) μ :=
      (hmeas (e n) (hmem n)).sub hint0.1
    have hlow : ∀ᵐ x ∂μ, e n * q 0 x ≤ F x (e n) - F x 0 := by
      filter_upwards [hq_mono] with x hx
      have h1 := hx (Nat.zero_le n)
      have hqn : e n * q n x = F x (e n) - F x 0 := by
        simp only [hq]; field_simp [(he_pos n).ne']
      rw [← hqn]; exact mul_le_mul_of_nonneg_left h1 (he_pos n).le
    have hneg : ∫⁻ x, ENNReal.ofReal (F x 0 - F x (e n)) ∂μ < ⊤ := by
      calc ∫⁻ x, ENNReal.ofReal (F x 0 - F x (e n)) ∂μ ≤ ∫⁻ x, ‖e n * q 0 x‖ₑ ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hlow] with x hx
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (e n * q 0 x)])
        _ < ⊤ := (hq0.const_mul (e n)).hasFiniteIntegral
    have hpos : ∫⁻ x, ENNReal.ofReal (F x (e n) - F x 0) ∂μ < ⊤ :=
      lt_of_le_of_lt (hopt _ ⟨he_pos n, he_le n⟩) hneg
    have hint : Integrable (fun x => F x (e n) - F x 0) μ := by
      refine ⟨hmeasg, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ x, ‖F x (e n) - F x 0‖ₑ ∂μ ≤ ∫⁻ x, (ENNReal.ofReal (F x (e n) - F x 0) +
            ENNReal.ofReal (-(F x (e n) - F x 0))) ∂μ :=
            lintegral_mono fun x => enorm_le_ofReal_add _
        _ = ∫⁻ x, ENNReal.ofReal (F x (e n) - F x 0) ∂μ +
            ∫⁻ x, ENNReal.ofReal (-(F x (e n) - F x 0)) ∂μ :=
            lintegral_add_left' hmeasg.aemeasurable.ennreal_ofReal _
        _ < ⊤ := by
          refine ENNReal.add_lt_top.2 ⟨hpos, ?_⟩
          simpa only [neg_sub] using hneg
    refine ⟨hint, ?_⟩
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint, sub_nonpos]
    have h1 := hopt _ ⟨he_pos n, he_le n⟩
    simp only [neg_sub]
    exact ENNReal.toReal_mono hneg.ne h1
  have hqn_int : ∀ n, Integrable (q n) μ := fun n => (hgn n).1.div_const (e n)
  have hqn_le : ∀ n, ∫ x, q n x ∂μ ≤ 0 := fun n => by
    simp only [hq]
    rw [integral_div]
    exact div_nonpos_of_nonpos_of_nonneg (hgn n).2 (he_pos n).le
  -- the limit is integrable (monotone convergence for the nonnegative increments)
  have hDmeas : AEStronglyMeasurable D μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hqn_int n).1) hq_lim
  have hnn : ∀ n, 0 ≤ᵐ[μ] fun x => q n x - q 0 x := fun n => by
    filter_upwards [hq_mono] with x hx
    simp only [Pi.zero_apply, sub_nonneg]
    exact hx (Nat.zero_le n)
  have hDq0 : 0 ≤ᵐ[μ] fun x => D x - q 0 x := by
    filter_upwards [hq_mono, hq_lim] with x hx hl
    simp only [Pi.zero_apply, sub_nonneg]
    exact ge_of_tendsto' hl fun n => hx (Nat.zero_le n)
  have hlin : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (q n x - q 0 x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (D x - q 0 x) ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((hqn_int n).sub hq0).aemeasurable.ennreal_ofReal) ?_ ?_
    · filter_upwards [hq_mono] with x hx n m hnm
      exact ENNReal.ofReal_le_ofReal (by linarith [hx hnm])
    · filter_upwards [hq_lim] with x hx
      exact (ENNReal.continuous_ofReal.tendsto _).comp (hx.sub tendsto_const_nhds)
  have hbd : ∀ n, ∫⁻ x, ENNReal.ofReal (q n x - q 0 x) ∂μ ≤
      ENNReal.ofReal (-∫ x, q 0 x ∂μ) := by
    intro n
    have h := ofReal_integral_eq_lintegral_ofReal ((hqn_int n).sub hq0) (hnn n)
    simp only [Pi.sub_apply] at h
    rw [← h]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_sub (hqn_int n) hq0]
    linarith [hqn_le n]
  have hfin : ∫⁻ x, ENNReal.ofReal (D x - q 0 x) ∂μ < ⊤ :=
    lt_of_le_of_lt (le_of_tendsto' hlin hbd) ENNReal.ofReal_lt_top
  have hDq : Integrable (fun x => D x - q 0 x) μ := by
    refine ⟨hDmeas.sub hq0.1, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hDq0).2 hfin
  have hDint : Integrable D μ :=
    (hDq.add hq0).congr (ae_of_all _ fun x => by simp)
  refine ⟨hDint, ?_⟩
  exact le_of_tendsto' (integral_tendsto_of_tendsto_of_monotone hqn_int hDint hq_mono hq_lim)
    hqn_le

/-- Cochrane (2023), A4 p. 640 (the concavity behind the Hamiltonian sufficiency argument): a
function concave on `(0, ∞)` and differentiable at `x > 0` with derivative `d` lies below its
tangent line, `f(z) ≤ f(x) + d(z − x)` for `z > 0`.
The `(0, ∞)` form of `MoneyInUtility.concave_le_tangent`. -/
theorem concave_tangent {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ioi 0) f) {x z d : ℝ} (hx : 0 < x)
    (hz : 0 < z) (hd : HasDerivAt f d x) : f z ≤ f x + d * (z - x) := by
  rcases lt_trichotomy x z with hxz | hxz | hxz
  · have h := hf.slope_le_of_hasDerivAt hx hz hxz hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith
  · subst hxz; simp
  · have h := hf.le_slope_of_hasDerivAt hz hx hxz hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith

/-- Cochrane (2023), A4 p. 640 (concavity along a variation): if `f` is concave on `(0, ∞)` and
`c + εa > 0` for `ε ∈ [0, ε₀]`, then `ε ↦ f(c + εa)` is concave on `[0, ε₀]`. -/
theorem concaveOn_comp_affine {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ioi 0) f) {c a ε0 : ℝ}
    (hpos : ∀ ε ∈ Set.Icc 0 ε0, 0 < c + ε * a) :
    ConcaveOn ℝ (Set.Icc 0 ε0) (fun ε => f (c + ε * a)) := by
  refine ⟨convex_Icc 0 ε0, fun x hx z hz p r hp hr hpr => ?_⟩
  have h := hf.2 (Set.mem_Ioi.mpr (hpos x hx)) (Set.mem_Ioi.mpr (hpos z hz)) hp hr hpr
  simp only [smul_eq_mul] at h ⊢
  have e : p * (c + x * a) + r * (c + z * a) = c + (p * x + r * z) * a := by
    have : r = 1 - p := by linarith
    subst this; ring
  rw [e] at h
  exact h

/-! ## A smooth bump built from `Real.smoothTransition` -/

/-- Cochrane (2023), A4 p. 640 (test variations for the Hamiltonian conditions): the smooth
step `t ↦ σ((t − τ)/w)`, `σ = Real.smoothTransition` (`0` for `t ≤ τ`, `1` for `t ≥ τ + w`). -/
noncomputable def bump (τ w t : ℝ) : ℝ := Real.smoothTransition ((t - τ) / w)

/-- Cochrane (2023), A4 p. 640 (test variations): the derivative of `bump τ w`,
`ρ(t) = σ'((t − τ)/w)/w`. -/
noncomputable def rho (τ w t : ℝ) : ℝ := deriv Real.smoothTransition ((t - τ) / w) / w

/-- Cochrane (2023), A4 p. 640 (test variations): `σ` is differentiable with continuous
derivative. -/
theorem smoothTransition_C1 :
    Differentiable ℝ Real.smoothTransition ∧ Continuous (deriv Real.smoothTransition) :=
  contDiff_one_iff_deriv.mp Real.smoothTransition.contDiff

/-- Cochrane (2023), A4 p. 640 (test variations): `bump τ w` has derivative `rho τ w`. -/
theorem hasDerivAt_bump (τ w t : ℝ) : HasDerivAt (bump τ w) (rho τ w t) t := by
  have h1 : HasDerivAt (fun t => (t - τ) / w) (1 / w) t :=
    ((hasDerivAt_id t).sub_const τ).div_const w
  have h2 := (smoothTransition_C1.1 ((t - τ) / w)).hasDerivAt
  have h3 := h2.comp t h1
  unfold bump rho
  rw [div_eq_mul_one_div (deriv Real.smoothTransition ((t - τ) / w)) w]
  exact h3

/-- Cochrane (2023), A4 p. 640 (test variations): `rho τ w` is continuous. -/
theorem continuous_rho (τ w : ℝ) : Continuous (rho τ w) :=
  (smoothTransition_C1.2.comp ((continuous_id.sub continuous_const).div_const w)).div_const w

/-- Cochrane (2023), A4 p. 640 (test variations): `rho τ w ≥ 0` for `w > 0` (`σ` is
monotone). -/
theorem rho_nonneg (τ : ℝ) {w : ℝ} (hw : 0 < w) (t : ℝ) : 0 ≤ rho τ w t :=
  div_nonneg (Real.smoothTransition.monotone.deriv_nonneg) hw.le

/-- Cochrane (2023), A4 p. 640 (test variations): `σ' = 0` on `(−∞, 0)` and on `(1, ∞)`. -/
theorem deriv_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < 0 from hx)] with z hz
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
    rw [this.deriv_eq, deriv_const]
  · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds (show 1 < x from hx)] with z hz
      exact Real.smoothTransition.one_of_one_le (le_of_lt hz)
    rw [this.deriv_eq, deriv_const]

/-- Cochrane (2023), A4 p. 640 (test variations): `rho τ w t = 0` for `t < τ` (`w > 0`). -/
theorem rho_eq_zero_of_lt {τ w t : ℝ} (hw : 0 < w) (ht : t < τ) : rho τ w t = 0 := by
  unfold rho
  rw [deriv_smoothTransition_eq_zero (Or.inl (div_neg_of_neg_of_pos (by linarith) hw)),
    zero_div]

/-- Cochrane (2023), A4 p. 640 (test variations): `rho τ w t = 0` for `t > τ + w` (`w > 0`). -/
theorem rho_eq_zero_of_gt {τ w t : ℝ} (hw : 0 < w) (ht : τ + w < t) : rho τ w t = 0 := by
  unfold rho
  rw [deriv_smoothTransition_eq_zero (Or.inr ((one_lt_div hw).mpr (by linarith))), zero_div]

/-- Cochrane (2023), A4 p. 640 (test variations): `bump τ w t = 0` for `t ≤ τ` (`w > 0`). -/
theorem bump_eq_zero {τ w t : ℝ} (hw : 0 < w) (ht : t ≤ τ) : bump τ w t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)

/-- Cochrane (2023), A4 p. 640 (test variations): `bump τ w t = 1` for `t ≥ τ + w` (`w > 0`). -/
theorem bump_eq_one {τ w t : ℝ} (hw : 0 < w) (ht : τ + w ≤ t) : bump τ w t = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div hw).mpr (by linarith))

/-- Cochrane (2023), A4 p. 640 (test variations): over any `[a, b]` with `a ≤ τ` and
`τ + w ≤ b`, `∫_a^b ρ = 1`. -/
theorem integral_rho {τ w a b : ℝ} (hw : 0 < w) (ha : a ≤ τ) (hb : τ + w ≤ b) :
    ∫ t in a..b, rho τ w t = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_bump τ w t)
    ((continuous_rho τ w).intervalIntegrable a b), bump_eq_one hw hb, bump_eq_zero hw ha,
    sub_zero]

/-- **Cochrane (2023), A4 (4.17), p. 640: the du Bois-Reymond step, one direction.** If `G` is
continuous on `(0, ∞)`, `0 < t₁ < t₂`, `G(t₂) < G(t₁)`, there are `w > 0` with `t₁ + w < t₂`
and `∫_{t₁}^{t₂+w} G·(ρ_{t₁} − ρ_{t₂}) > 0`. -/
theorem dubois_reymond_aux {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Ioi 0)) {t1 t2 : ℝ}
    (h1 : 0 < t1) (h12 : t1 < t2) (hlt : G t2 < G t1) :
    ∃ w, 0 < w ∧ t1 + w < t2 ∧
      0 < ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) := by
  set ε := (G t1 - G t2) / 3 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hc1 := (hG.continuousAt (Ioi_mem_nhds h1))
  have hc2 := (hG.continuousAt (Ioi_mem_nhds (lt_trans h1 h12)))
  obtain ⟨η1, hη1, hb1⟩ := Metric.continuousAt_iff.mp hc1 ε hεpos
  obtain ⟨η2, hη2, hb2⟩ := Metric.continuousAt_iff.mp hc2 ε hεpos
  set w := min (min η1 η2 / 2) ((t2 - t1) / 2) with hw
  have hwpos : 0 < w := by
    rw [hw]; refine lt_min (by positivity) (by linarith)
  have hw1 : w < η1 := by
    have : w ≤ min η1 η2 / 2 := min_le_left _ _
    have : min η1 η2 ≤ η1 := min_le_left _ _
    linarith
  have hw2 : w < η2 := by
    have : w ≤ min η1 η2 / 2 := min_le_left _ _
    have : min η1 η2 ≤ η2 := min_le_right _ _
    linarith
  have hw12 : t1 + w < t2 := by
    have : w ≤ (t2 - t1) / 2 := min_le_right _ _
    linarith
  refine ⟨w, hwpos, hw12, ?_⟩
  have hab : t1 ≤ t2 + w := by linarith
  have hGc : ContinuousOn G (Set.uIcc t1 (t2 + w)) := hG.mono fun t ht => by
    rw [Set.uIcc_of_le hab] at ht; exact lt_of_lt_of_le h1 ht.1
  have hi1 : IntervalIntegrable (fun t => G t * rho t1 w t) volume t1 (t2 + w) :=
    (hGc.mul (continuous_rho t1 w).continuousOn).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => G t * rho t2 w t) volume t1 (t2 + w) :=
    (hGc.mul (continuous_rho t2 w).continuousOn).intervalIntegrable
  have hI1 : G t1 - ε ≤ ∫ t in t1..(t2 + w), G t * rho t1 w t := by
    have hmono := intervalIntegral.integral_mono_on hab
      (((continuous_rho t1 w).const_mul (G t1 - ε)).intervalIntegrable _ _) hi1
      (fun t ht => by
        rcases le_or_gt t (t1 + w) with hle | hgt
        · have hd : dist t t1 < η1 := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1]
          have := hb1 hd
          rw [Real.dist_eq, abs_lt] at this
          exact mul_le_mul_of_nonneg_right (by linarith [this.1]) (rho_nonneg t1 hwpos t)
        · rw [rho_eq_zero_of_gt hwpos hgt]; simp)
    beta_reduce at hmono
    rw [intervalIntegral.integral_const_mul, integral_rho hwpos le_rfl (by linarith),
      mul_one] at hmono
    exact hmono
  have hI2 : ∫ t in t1..(t2 + w), G t * rho t2 w t ≤ G t2 + ε := by
    have hmono := intervalIntegral.integral_mono_on hab hi2
      (((continuous_rho t2 w).const_mul (G t2 + ε)).intervalIntegrable _ _)
      (fun t ht => by
        rcases lt_or_ge t t2 with hlt' | hge
        · rw [rho_eq_zero_of_lt hwpos hlt']; simp
        · have hd : dist t t2 < η2 := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.2]
          have := hb2 hd
          rw [Real.dist_eq, abs_lt] at this
          exact mul_le_mul_of_nonneg_right (by linarith [this.2]) (rho_nonneg t2 hwpos t))
    beta_reduce at hmono
    rw [intervalIntegral.integral_const_mul, integral_rho hwpos (by linarith) le_rfl,
      mul_one] at hmono
    exact hmono
  have hsplit : ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) =
      (∫ t in t1..(t2 + w), G t * rho t1 w t) - ∫ t in t1..(t2 + w), G t * rho t2 w t := by
    have e : (fun t => G t * (rho t1 w t - rho t2 w t)) =
        fun t => G t * rho t1 w t - G t * rho t2 w t := by funext t; ring
    rw [e]
    exact intervalIntegral.integral_sub hi1 hi2
  rw [hsplit]
  linarith

/-- **Cochrane (2023), A4 (4.17), p. 640: the du Bois-Reymond lemma.** If `G` is continuous on
`(0, ∞)` and `∫_{t₁}^{t₂+w} G·(ρ_{t₁} − ρ_{t₂}) = 0` whenever `0 < t₁`, `0 < w` and
`t₁ + w < t₂`, then `G` is constant on `(0, ∞)`. -/
theorem dubois_reymond {G : ℝ → ℝ} (hG : ContinuousOn G (Set.Ioi 0))
    (hzero : ∀ t1 t2 w, 0 < t1 → 0 < w → t1 + w < t2 →
      ∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) = 0) :
    ∀ t1 t2, 0 < t1 → t1 < t2 → G t1 = G t2 := by
  intro t1 t2 h1 h12
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hG' : ContinuousOn (fun t => -G t) (Set.Ioi 0) := hG.neg
    obtain ⟨w, hw, hw12, hpos⟩ := dubois_reymond_aux hG' h1 h12 (by linarith)
    have := hzero t1 t2 w h1 hw hw12
    have e : ∫ t in t1..(t2 + w), -G t * (rho t1 w t - rho t2 w t) =
        -∫ t in t1..(t2 + w), G t * (rho t1 w t - rho t2 w t) := by
      rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
    rw [e, this] at hpos
    simp at hpos
  · obtain ⟨w, hw, hw12, hpos⟩ := dubois_reymond_aux hG h1 h12 hgt
    rw [hzero t1 t2 w h1 hw hw12] at hpos
    exact lt_irrefl _ hpos

end Cochrane.Monetarism.TidyR6PontryaginTools
