/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7BrownianQV
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Mean-square tools for the Itô integral

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5c): the `L²` analysis that turns the left-point sums `Σ H_{t_i}ΔW_i` into the
Itô integral `∫ H dW`. Nothing here is about Brownian motion.

* `L2Tendsto P X Y`: `X k → Y` in mean square (`X k`, `Y` square integrable and
  `E[(X k − Y)²] → 0`).
* `integral_sq_eq_toReal_eLpNorm_sq`, `eLpNorm_eq_ofReal_sqrt`: `E[f²] = ‖f‖²_{L²}`.
* `exists_L2Tendsto` (**completeness**): a mean-square Cauchy sequence of `m`-strongly
  measurable functions has an `m`-strongly measurable mean-square limit (through the complete
  space `Lp ℝ 2 (P.trim hm)`), so the limit can be chosen adapted without completing the
  filtration.
* `ae_eq_of_L2Tendsto` (uniqueness a.e.), `L2Tendsto.add`, `L2Tendsto.const_mul`,
  `ae_eq_of_L2Tendsto_of_ae_tendsto` (an `L²` limit and an a.s. limit agree a.e.).
* `sq_integral_mul_le` (Cauchy–Schwarz, by the discriminant), `tendsto_integral_mul_of_L2Tendsto`
  (`E[G X_k] → E[G Y]`) and `tendsto_integral_mul_sq_of_L2Tendsto` (`E[G X_k²] → E[G Y²]`) for
  bounded measurable `G`.
* `tendsto_riemannSum`: left-point Riemann sums of a function continuous on `[s, t]` converge to
  `∫_s^t f` along any partitions with mesh `→ 0`.
* `exists_delta_integral_sq_sub_le` (**mean-square uniform continuity**): a bounded process
  with a.s. continuous paths on `[s, t]` satisfies
  `∀ ε > 0, ∃ δ > 0, |u − v| ≤ δ ⇒ E[(H_u − H_v)²] ≤ ε` (Bolzano–Weierstrass and dominated
  convergence).
-/

namespace Cochrane.Monetarism.TidyR7ItoL2

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianQV
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the mean-square limit defining the Itô integral in
(1.32) with diffusive bonds): `X k → Y` in `L²(P)`: every `X k` and `Y` are square integrable
and `E[(X k − Y)²] → 0`. -/
def L2Tendsto (P : Measure Ω) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  (∀ k, MemLp (X k) 2 P) ∧ MemLp Y 2 P ∧
    Tendsto (fun k => ∫ ω, (X k ω - Y ω) ^ 2 ∂P) atTop (𝓝 0)

/-! ## `E[f²]` and the `L²` norm -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[f²] = ‖f‖²_{L²}` for square-integrable `f`. -/
theorem integral_sq_eq_toReal_eLpNorm_sq {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, f ω ^ 2 ∂P = (eLpNorm f 2 P).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have h0 : 0 ≤ ∫ ω, ‖f ω‖ ^ (2 : ℝ≥0∞).toReal ∂P := integral_nonneg fun _ => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  simp [Real.norm_eq_abs, sq_abs]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `‖f‖_{L²} = √E[f²]` for square-integrable `f`. -/
theorem eLpNorm_eq_ofReal_sqrt {f : Ω → ℝ} (hf : MemLp f 2 P) :
    eLpNorm f 2 P = ENNReal.ofReal (√(∫ ω, f ω ^ 2 ∂P)) := by
  rw [integral_sq_eq_toReal_eLpNorm_sq hf, Real.sqrt_sq ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hf.ne]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: mean-square convergence gives `‖X k − Y‖_{L²} → 0`.
Restates `TidyR7BrownianQV.tendsto_eLpNorm_of_integral_sq`. -/
theorem L2Tendsto.tendsto_eLpNorm {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (h : L2Tendsto P X Y) :
    Tendsto (fun k => eLpNorm (X k - Y) 2 P) atTop (𝓝 0) := by
  have e : ∀ k, eLpNorm (X k - Y) 2 P = ENNReal.ofReal (√(∫ ω, (X k ω - Y ω) ^ 2 ∂P)) :=
    fun k => eLpNorm_eq_ofReal_sqrt ((h.1 k).sub h.2.1)
  simp_rw [e]
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h.2.2
  rw [Real.sqrt_zero] at h2
  simpa using ENNReal.tendsto_ofReal h2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `(y − z)² ≤ 2(x − y)² + 2(x − z)²`. -/
lemma sq_sub_le_two_mul (x y z : ℝ) : (y - z) ^ 2 ≤ 2 * (x - y) ^ 2 + 2 * (x - z) ^ 2 := by
  nlinarith [sq_nonneg (2 * x - y - z)]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for square-integrable `f, g, h`,
`E[(g − h)²] ≤ 2E[(f − g)²] + 2E[(f − h)²]`. -/
theorem integral_sq_sub_le {f g h : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (hh : MemLp h 2 P) :
    ∫ ω, (g ω - h ω) ^ 2 ∂P
      ≤ 2 * ∫ ω, (f ω - g ω) ^ 2 ∂P + 2 * ∫ ω, (f ω - h ω) ^ 2 ∂P := by
  have i1 : Integrable (fun ω => (f ω - g ω) ^ 2) P := (hf.sub hg).integrable_sq
  have i2 : Integrable (fun ω => (f ω - h ω) ^ 2) P := (hf.sub hh).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
    (i2.const_mul _)]
  exact integral_mono (hg.sub hh).integrable_sq ((i1.const_mul _).add (i2.const_mul _))
    fun ω => sq_sub_le_two_mul (f ω) (g ω) (h ω)

/-! ## Completeness and uniqueness -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: completeness of `L²` with an adapted limit.** If
`X k` are `m`-strongly measurable, square integrable, and mean-square Cauchy, then they have a
mean-square limit `Y` that is itself `m`-strongly measurable. Proof: `Lp ℝ 2 (P.trim hm)` is
complete (`cauchySeq_tendsto_of_complete`); `Lp.stronglyMeasurable` gives the representative. -/
theorem exists_L2Tendsto {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : ℕ → Ω → ℝ}
    (hXm : ∀ k, StronglyMeasurable[m] (X k)) (hX : ∀ k, MemLp (X k) 2 P)
    (hC : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∫ ω, (X k ω - X l ω) ^ 2 ∂P ≤ ε) :
    ∃ Y, StronglyMeasurable[m] Y ∧ L2Tendsto P X Y := by
  have hXt : ∀ k, MemLp (X k) 2 (P.trim hm) := fun k =>
    by rw [memLp_iff, eLpNorm_trim hm (hXm k)]; exact hX k
  set F : ℕ → Lp ℝ 2 (P.trim hm) := fun k => (hXt k).toLp (X k) with hF
  have hdist : ∀ k l, dist (F k) (F l) = √(∫ ω, (X k ω - X l ω) ^ 2 ∂P) := by
    intro k l
    have key : ∫ ω, (X k ω - X l ω) ^ 2 ∂P = (eLpNorm (X k - X l) 2 P).toReal ^ 2 :=
      integral_sq_eq_toReal_eLpNorm_sq ((hX k).sub (hX l))
    rw [dist_eq_norm, hF, ← MemLp.toLp_sub, Lp.norm_toLp,
      eLpNorm_trim hm ((hXm k).sub (hXm l)), key, Real.sqrt_sq ENNReal.toReal_nonneg]
  have hcau : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC (ε ^ 2 / 4) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    rw [hdist]
    calc √(∫ ω, (X k ω - X l ω) ^ 2 ∂P) ≤ √(ε ^ 2 / 4) := Real.sqrt_le_sqrt (hN k hk l hl)
      _ = ε / 2 := by
        rw [show ε ^ 2 / 4 = (ε / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      _ < ε := by linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, Lp.stronglyMeasurable L, hX, memLp_of_memLp_trim hm (Lp.memLp L), ?_⟩
  have e : ∀ k, ∫ ω, (X k ω - L ω) ^ 2 ∂P = ‖F k - L‖ ^ 2 := by
    intro k
    have hae : ⇑(F k - L) =ᵐ[P.trim hm] fun ω => X k ω - L ω := by
      filter_upwards [Lp.coeFn_sub (F k) L, MemLp.coeFn_toLp (hXt k)] with ω h1 h2
      rw [h1, Pi.sub_apply, hF, h2]
    rw [Lp.norm_def, eLpNorm_congr_ae hae, eLpNorm_trim hm (f := fun ω => X k ω - L ω)
      ((hXm k).sub (Lp.stronglyMeasurable L))]
    exact integral_sq_eq_toReal_eLpNorm_sq ((hX k).sub (memLp_of_memLp_trim hm (Lp.memLp L)))
  simp_rw [e]
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 hL).pow 2
  simpa using h1

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **a mean-square limit is unique almost everywhere.**
Compare Mathlib `tendstoInMeasure_ae_unique`. -/
theorem ae_eq_of_L2Tendsto {X : ℕ → Ω → ℝ} {Y Z : Ω → ℝ} (hY : L2Tendsto P X Y)
    (hZ : L2Tendsto P X Z) : Y =ᵐ[P] Z := by
  have hle : ∀ k, ∫ ω, (Y ω - Z ω) ^ 2 ∂P
      ≤ 2 * ∫ ω, (X k ω - Y ω) ^ 2 ∂P + 2 * ∫ ω, (X k ω - Z ω) ^ 2 ∂P := fun k =>
    integral_sq_sub_le (hY.1 k) hY.2.1 hZ.2.1
  have hlim : Tendsto (fun k => 2 * ∫ ω, (X k ω - Y ω) ^ 2 ∂P
      + 2 * ∫ ω, (X k ω - Z ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa using (hY.2.2.const_mul 2).add (hZ.2.2.const_mul 2)
  have h0 : ∫ ω, (Y ω - Z ω) ^ 2 ∂P = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) (integral_nonneg fun _ => sq_nonneg _)
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (Y ω - Z ω))
    (hY.2.1.sub hZ.2.1).integrable_sq).1 h0
  filter_upwards [hz] with ω hω
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hω
  exact sub_eq_zero.1 hω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a mean-square limit can be replaced by an a.e. equal
square-integrable function. -/
theorem L2Tendsto.congr_ae {X : ℕ → Ω → ℝ} {Y Z : Ω → ℝ} (h : L2Tendsto P X Y) (hYZ : Y =ᵐ[P] Z) :
    L2Tendsto P X Z := by
  refine ⟨h.1, h.2.1.ae_eq hYZ, ?_⟩
  have e : ∀ k, ∫ ω, (X k ω - Z ω) ^ 2 ∂P = ∫ ω, (X k ω - Y ω) ^ 2 ∂P := fun k =>
    integral_congr_ae (by filter_upwards [hYZ] with ω hω; rw [hω])
  simp_rw [e]
  exact h.2.2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: mean-square limits do not see a.e. changes of the
sequence. -/
theorem L2Tendsto.congr_seq {X X' : ℕ → Ω → ℝ} {Y : Ω → ℝ} (h : L2Tendsto P X Y)
    (hXX : ∀ k, X k =ᵐ[P] X' k) : L2Tendsto P X' Y := by
  refine ⟨fun k => (h.1 k).ae_eq (hXX k), h.2.1, ?_⟩
  have e : ∀ k, ∫ ω, (X' k ω - Y ω) ^ 2 ∂P = ∫ ω, (X k ω - Y ω) ^ 2 ∂P := fun k =>
    integral_congr_ae (by filter_upwards [hXX k] with ω hω; rw [hω])
  simp_rw [e]
  exact h.2.2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: mean-square limits add (linearity of the Itô
integral). -/
theorem L2Tendsto.add {X X' : ℕ → Ω → ℝ} {Y Y' : Ω → ℝ} (h : L2Tendsto P X Y)
    (h' : L2Tendsto P X' Y') : L2Tendsto P (fun k => X k + X' k) (Y + Y') := by
  refine ⟨fun k => (h.1 k).add (h'.1 k), h.2.1.add h'.2.1, ?_⟩
  have hle : ∀ k, ∫ ω, ((X k + X' k) ω - (Y + Y') ω) ^ 2 ∂P
      ≤ 2 * ∫ ω, (X k ω - Y ω) ^ 2 ∂P + 2 * ∫ ω, (X' k ω - Y' ω) ^ 2 ∂P := by
    intro k
    have i1 : Integrable (fun ω => (X k ω - Y ω) ^ 2) P := ((h.1 k).sub h.2.1).integrable_sq
    have i2 : Integrable (fun ω => (X' k ω - Y' ω) ^ 2) P := ((h'.1 k).sub h'.2.1).integrable_sq
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _)
      (i2.const_mul _)]
    refine integral_mono (((h.1 k).add (h'.1 k)).sub (h.2.1.add h'.2.1)).integrable_sq
      ((i1.const_mul _).add (i2.const_mul _)) fun ω => ?_
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (X k ω - Y ω - (X' k ω - Y' ω))]
  have hlim : Tendsto (fun k => 2 * ∫ ω, (X k ω - Y ω) ^ 2 ∂P
      + 2 * ∫ ω, (X' k ω - Y' ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa using (h.2.2.const_mul 2).add (h'.2.2.const_mul 2)
  exact squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) hle hlim

/-- Cochrane (2023), A1 §1.6, pp. 567–568: mean-square limits scale (linearity of the Itô
integral). -/
theorem L2Tendsto.const_mul {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (h : L2Tendsto P X Y) (c : ℝ) :
    L2Tendsto P (fun k ω => c * X k ω) (fun ω => c * Y ω) := by
  refine ⟨fun k => (h.1 k).const_mul c, h.2.1.const_mul c, ?_⟩
  have e : ∀ k, ∫ ω, (c * X k ω - c * Y ω) ^ 2 ∂P = c ^ 2 * ∫ ω, (X k ω - Y ω) ^ 2 ∂P := by
    intro k
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  simp_rw [e]
  simpa using h.2.2.const_mul (c ^ 2)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **an `L²` limit and an almost-sure limit agree a.e.**
(a subsequence of an `L²`-convergent sequence converges a.s.,
`TendstoInMeasure.exists_seq_tendsto_ae`). -/
theorem ae_eq_of_L2Tendsto_of_ae_tendsto {X : ℕ → Ω → ℝ} {Y Z : Ω → ℝ} (hY : L2Tendsto P X Y)
    (hZ : ∀ᵐ ω ∂P, Tendsto (fun k => X k ω) atTop (𝓝 (Z ω))) : Y =ᵐ[P] Z := by
  have hm : TendstoInMeasure P X atTop Y :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hY.tendsto_eLpNorm
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hae, hZ] with ω h1 h2
  exact tendsto_nhds_unique h1 (h2.comp hns.tendsto_atTop)

/-! ## Cauchy–Schwarz and the convergence of moments -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **Cauchy–Schwarz**, `(E[ab])² ≤ E[a²]E[b²]` for
square-integrable `a, b` (the quadratic `x ↦ E[(xa + b)²] ≥ 0` has non-positive discriminant,
Mathlib `discrim_le_zero`).
Cauchy–Schwarz, the `p = q = 2` case of Mathlib `integral_mul_le_Lp_mul_Lq_of_nonneg`. -/
theorem sq_integral_mul_le {a b : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    (∫ ω, a ω * b ω ∂P) ^ 2 ≤ (∫ ω, a ω ^ 2 ∂P) * ∫ ω, b ω ^ 2 ∂P := by
  have iaa := ha.integrable_sq
  have ibb := hb.integrable_sq
  have iab : Integrable (fun ω => a ω * b ω) P := ha.integrable_mul hb
  have hq : ∀ x : ℝ, 0 ≤ (∫ ω, a ω ^ 2 ∂P) * (x * x) + (2 * ∫ ω, a ω * b ω ∂P) * x
      + ∫ ω, b ω ^ 2 ∂P := by
    intro x
    have e : ∫ ω, (x * a ω + b ω) ^ 2 ∂P = (∫ ω, a ω ^ 2 ∂P) * (x * x)
        + (2 * ∫ ω, a ω * b ω ∂P) * x + ∫ ω, b ω ^ 2 ∂P := by
      have e1 : (fun ω => (x * a ω + b ω) ^ 2)
          = fun ω => (x * x) * a ω ^ 2 + (2 * x) * (a ω * b ω) + b ω ^ 2 := by
        funext ω; ring
      rw [e1, integral_add (f := fun ω => x * x * a ω ^ 2 + 2 * x * (a ω * b ω))
        ((iaa.const_mul _).add (iab.const_mul _)) ibb,
        integral_add (iaa.const_mul _) (iab.const_mul _), integral_const_mul,
        integral_const_mul]
      ring
    rw [← e]
    exact integral_nonneg fun _ => sq_nonneg _
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: on a probability space, a bounded measurable `G`
with `|G| ≤ C` is square integrable with `E[G²] ≤ C²`.
Restates Mathlib `MemLp.of_bound`. -/
theorem memLp_of_bound [IsFiniteMeasure P] {G : Ω → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ ω, |G ω| ≤ C) : MemLp G 2 P :=
  MemLp.of_bound hG.aestronglyMeasurable C (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact hGb ω)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `a_k² ≤ c·b_k` and `b_k → 0` then `a_k → 0`. -/
lemma tendsto_zero_of_sq_le {a b : ℕ → ℝ} {c : ℝ} (hab : ∀ k, a k ^ 2 ≤ c * b k)
    (hb : Tendsto b atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => √(c * b k)) atTop (𝓝 0) := by
    have hb' : Tendsto (fun k => c * b k) atTop (𝓝 0) := by simpa using hb.const_mul c
    have := (Real.continuous_sqrt.tendsto 0).comp hb'
    rw [Real.sqrt_zero] at this
    exact this
  have h2 : Tendsto (fun k => |a k|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun k => by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (hab k)) h1
  exact tendsto_zero_iff_abs_tendsto_zero _ |>.2 h2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[G X_k] → E[G Y]`** for `X k → Y` in mean
square and `G` bounded measurable on a probability space. -/
theorem tendsto_integral_mul_of_L2Tendsto [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {Y : Ω → ℝ} (h : L2Tendsto P X Y) {G : Ω → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ ω, |G ω| ≤ C) :
    Tendsto (fun k => ∫ ω, G ω * X k ω ∂P) atTop (𝓝 (∫ ω, G ω * Y ω ∂P)) := by
  have hG2 := memLp_of_bound (P := P) hG hGb
  have hC2 : ∫ ω, G ω ^ 2 ∂P ≤ C ^ 2 := by
    have h := integral_mono_of_nonneg (μ := P) (ae_of_all _ fun ω => sq_nonneg (G ω))
      (integrable_const (C ^ 2)) (ae_of_all _ fun ω => sq_le_sq' (abs_le.1 (hGb ω)).1
        (abs_le.1 (hGb ω)).2)
    simpa using h
  have e : ∀ k, ∫ ω, G ω * X k ω ∂P - ∫ ω, G ω * Y ω ∂P
      = ∫ ω, G ω * (X k ω - Y ω) ∂P := by
    intro k
    rw [← integral_sub (f := fun ω => G ω * X k ω) (g := fun ω => G ω * Y ω)
      (hG2.integrable_mul (h.1 k)) (hG2.integrable_mul h.2.1)]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  refine tendsto_sub_nhds_zero_iff.1 ?_
  simp_rw [e]
  refine tendsto_zero_of_sq_le (c := C ^ 2) (fun k => ?_) h.2.2
  exact (sq_integral_mul_le hG2 ((h.1 k).sub h.2.1)).trans
    (mul_le_mul_of_nonneg_right hC2 (integral_nonneg fun _ => sq_nonneg _))

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[G X_k²] → E[G Y²]`** for `X k → Y` in mean
square and `G` bounded measurable on a probability space (`GX_k² − GY² = G(X_k − Y)² +
2GY(X_k − Y)`; Cauchy–Schwarz on the second term). -/
theorem tendsto_integral_mul_sq_of_L2Tendsto [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {Y : Ω → ℝ} (h : L2Tendsto P X Y) {G : Ω → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ ω, |G ω| ≤ C) :
    Tendsto (fun k => ∫ ω, G ω * X k ω ^ 2 ∂P) atTop (𝓝 (∫ ω, G ω * Y ω ^ 2 ∂P)) := by
  have hGY : MemLp (fun ω => G ω * Y ω) 2 P := by
    refine h.2.1.of_le_mul (c := C) (hG.aestronglyMeasurable.mul h.2.1.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hGb ω) (abs_nonneg _)
  have hD := fun k => (h.1 k).sub h.2.1
  have i1 : ∀ k, Integrable (fun ω => G ω * (X k ω - Y ω) ^ 2) P := fun k =>
    (hD k).integrable_sq.bdd_mul hG.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hGb ω)
  have i2 : ∀ k, Integrable (fun ω => G ω * Y ω * (X k ω - Y ω)) P := fun k =>
    hGY.integrable_mul (hD k)
  have e : ∀ k, ∫ ω, G ω * X k ω ^ 2 ∂P - ∫ ω, G ω * Y ω ^ 2 ∂P
      = ∫ ω, G ω * (X k ω - Y ω) ^ 2 ∂P + 2 * ∫ ω, G ω * Y ω * (X k ω - Y ω) ∂P := by
    intro k
    have j1 : Integrable (fun ω => G ω * X k ω ^ 2) P :=
      (h.1 k).integrable_sq.bdd_mul hG.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hGb ω)
    have j2 : Integrable (fun ω => G ω * Y ω ^ 2) P :=
      h.2.1.integrable_sq.bdd_mul hG.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hGb ω)
    rw [← integral_sub j1 j2, ← integral_const_mul, ← integral_add (i1 k) ((i2 k).const_mul _)]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  refine tendsto_sub_nhds_zero_iff.1 ?_
  simp_rw [e]
  have t1 : Tendsto (fun k => ∫ ω, G ω * (X k ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hb : ∀ k, |∫ ω, G ω * (X k ω - Y ω) ^ 2 ∂P| ≤ C * ∫ ω, (X k ω - Y ω) ^ 2 ∂P := by
      intro k
      refine (abs_integral_le_integral_abs).trans ?_
      rw [← integral_const_mul]
      refine integral_mono (i1 k).abs ((hD k).integrable_sq.const_mul C) fun ω => ?_
      rw [abs_mul, abs_of_nonneg (sq_nonneg (X k ω - Y ω))]
      exact mul_le_mul_of_nonneg_right (hGb ω) (sq_nonneg _)
    have hl : Tendsto (fun k => C * ∫ ω, (X k ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
      simpa using h.2.2.const_mul C
    exact (tendsto_zero_iff_abs_tendsto_zero _).2
      (squeeze_zero (fun _ => abs_nonneg _) hb hl)
  have t2 : Tendsto (fun k => ∫ ω, G ω * Y ω * (X k ω - Y ω) ∂P) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (fun k => sq_integral_mul_le hGY (hD k)) h.2.2
  simpa using t1.add (t2.const_mul 2)

/-! ## Riemann sums -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the `dt`-sums `Σ H_{t_i}²Δt_i` of the Itô isometry):
the left-point Riemann sum `Σ_{i<n} f(t_i)(t_{i+1} − t_i)` of `f` along a partition. -/
noncomputable def riemannSum {s t : ℝ} (p : Partition s t) (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.n, f (p.t i) * (p.t (i + 1) - p.t i)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `f` oscillates by at most `ε` over distances
`≤ mesh p` on `[s, t]`, then `|Σ f(t_i)Δt_i − ∫_s^t f| ≤ ε(t − s)`. -/
theorem abs_riemannSum_sub_le {s t : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc s t))
    (p : Partition s t) {ε : ℝ}
    (hfε : ∀ x ∈ Set.Icc s t, ∀ y ∈ Set.Icc s t, |x - y| ≤ mesh p → |f x - f y| ≤ ε) :
    |riemannSum p f - ∫ u in s..t, f u| ≤ ε * (t - s) := by
  have hint : ∀ k < p.n, IntervalIntegrable f MeasureSpace.volume (p.t k) (p.t (k + 1)) :=
    fun k hk => (hf.mono (Set.uIcc_subset_Icc (t_mem p hk.le) (t_mem p hk))).intervalIntegrable
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [p.first, p.last] at hsum
  rw [← hsum, riemannSum, ← Finset.sum_sub_distrib, ← sum_step_eq p, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  have hlt := p.strictMono (Nat.lt_succ_self i)
  have e : f (p.t i) * (p.t (i + 1) - p.t i) - ∫ u in p.t i..p.t (i + 1), f u
      = ∫ u in p.t i..p.t (i + 1), (f (p.t i) - f u) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint i hi'),
      intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [e, ← Real.norm_eq_abs, ← abs_of_pos (sub_pos.2 hlt)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hlt.le] at hx
  have hxm : x ∈ Set.Icc s t := ⟨(t_mem p hi'.le).1.trans hx.1.le, hx.2.trans (t_mem p hi').2⟩
  rw [Real.norm_eq_abs]
  refine hfε _ (t_mem p hi'.le) _ hxm ?_
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 hx.1)]
  exact (sub_le_sub_right hx.2 _).trans (le_mesh p hi')

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Riemann sums converge.** For `f` continuous on
`[s, t]` and any partitions with mesh `→ 0`, `Σ f(t_i)Δt_i → ∫_s^t f`.
The `g = id` case of `TidyR7StieltjesSums.tendsto_rsSum_of_continuousOn`. -/
theorem tendsto_riemannSum {s t : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc s t))
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => riemannSum (ps k) f) atTop (𝓝 (∫ u in s..t, f u)) := by
  have hst : 0 ≤ t - s := sub_nonneg.2 (a_le_b (ps 0))
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε := η / (2 * (t - s + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε0
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hps.eventually (gt_mem_nhds hδ)))
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  refine (abs_riemannSum_sub_le hf (ps k) (ε := ε) fun x hx y hy hxy => ?_).trans_lt ?_
  · have := hδf x hx y hy (by rw [Real.dist_eq]; exact hxy.trans_lt (hN k hk))
    rw [Real.dist_eq] at this
    exact this.le
  · calc ε * (t - s) ≤ ε * (t - s + 1) := by nlinarith
      _ = η / 2 := by rw [hε]; field_simp
      _ < η := by linarith

/-! ## Mean-square uniform continuity of a bounded continuous process -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: mean-square uniform continuity.** If `H` is
bounded by `C` on `[s, t]`, each `H u` measurable, and a.e. path `u ↦ H u ω` continuous on
`[s, t]`, then for every `ε > 0` there is `δ > 0` with `E[(H_u − H_v)²] ≤ ε` whenever
`u, v ∈ [s, t]`, `|u − v| ≤ δ`. Proof by contradiction: a bad sequence of pairs has a
convergent subsequence (`IsCompact.tendsto_subseq`), along which dominated convergence forces
`E[(H_u − H_v)²] → 0`. -/
theorem exists_delta_integral_sq_sub_le [IsFiniteMeasure P] {s t : ℝ} {H : ℝ → Ω → ℝ}
    (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C)
    (hHc : ∀ᵐ ω ∂P, ContinuousOn (fun u => H u ω) (Set.Icc s t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, |u - v| ≤ δ →
      ∫ ω, (H u ω - H v ω) ^ 2 ∂P ≤ ε := by
  by_contra hcon
  push Not at hcon
  choose u hu v hv huv hlt using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hu
  have hd : Tendsto (fun k => v (φ k) - u (φ k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs, abs_sub_comm]
    refine (huv (φ k)).trans ?_
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (hφ.id_le k) 1)
  have hlimv : Tendsto (fun k => v (φ k)) atTop (𝓝 a) := by
    have := hlim.add hd
    simp only [add_zero] at this
    exact this.congr fun k => by simp
  have hwin : ∀ w : ℕ → ℝ, (∀ k, w k ∈ Set.Icc s t) → Tendsto (fun k => w (φ k)) atTop (𝓝 a) →
      Tendsto (fun k => w (φ k)) atTop (𝓝[Set.Icc s t] a) := fun w hw hwl =>
    tendsto_nhdsWithin_iff.2 ⟨hwl, Eventually.of_forall fun k => hw (φ k)⟩
  have hF : Tendsto (fun k => ∫ ω, (H (u (φ k)) ω - H (v (φ k)) ω) ^ 2 ∂P) atTop
      (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2)
      (fun k => (((hHm _ (hu (φ k))).sub (hHm _ (hv (φ k)))).pow_const 2).aestronglyMeasurable)
      (integrable_const _) (fun k => ae_of_all _ fun ω => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hHb _ (hu (φ k)) ω
      have h2 := hHb _ (hv (φ k)) ω
      have h3 : |H (u (φ k)) ω - H (v (φ k)) ω| ≤ 2 * C := by
        rw [two_mul]; exact (abs_sub _ _).trans (add_le_add h1 h2)
      exact sq_le_sq' (abs_le.1 h3).1 (abs_le.1 h3).2
    · filter_upwards [hHc] with ω hω
      have t1 := ((hω a ha).tendsto).comp (hwin u hu hlim)
      have t2 := ((hω a ha).tendsto).comp (hwin v hv hlimv)
      have := (t1.sub t2).pow 2
      simpa using this
  rw [integral_zero] at hF
  have := ge_of_tendsto hF (Eventually.of_forall fun k => (hlt (φ k)).le)
  linarith

end Cochrane.Monetarism.TidyR7ItoL2
