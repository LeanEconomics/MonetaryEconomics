/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasureProps

/-!
# Proposition 6.15 with genuine conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (pp. 456–463), Proposition 6.15 and
(5.4)–(5.8), and Benigno–Woodford (2003).

The core `ExpectationSystem` cannot carry a probability measure with a continuum of values
(its linearity and monotonicity are required on all functions), so the derivation of (5.4),
Proposition 6.14 and Proposition 6.15 is redone here with Bochner integrals and Mathlib's
`condExp` for the recursions of `F` and `K`. Expected discounted sums are `Isum μ β X =
∑' t, βᵗ ∫ X_t dμ` over bounded, a.e.-strongly-measurable processes (`BM`); the conditional
expectations in the recursions integrate out (tower property).

## Main results

* `BM`, `Isum`, `hasSum_Isum`, `Isum_sub`, `RecEqM` (recursions a.s. with `condExp`).
* `second_order_AS_int`, `CalvoASM`, `remASm`, `eq54M`: (5.4) on a probability space.
* `prop614M`, `prop615M`: the Calvo identities behind Propositions 6.14 and 6.15.
* `remASm_o`, `tip615M`, `W0615M`, `prop615_layerBM`: Proposition 6.15 Layer B for families
  of economies with `O(ε)` first-order variables, `π̄ − π, D = O(ε²)`, `O(ε³)` remainder.
* `along`, `dispAlong`, `aesm_along`, `prop615_measure`: Proposition 6.15 ALONG THE
  PERTURBATION EQUILIBRIUM on `(ℕ → ℝ, ν^ℕ)`, with dispersion and `π̄ − π` of second order
  proved through the Calvo laws.
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaMeasure615

open MeasureTheory Filter Topology Asymptotics
open LargeDistortions (Vp restP nowA VA hA h3A restA)
open ExpLogCES (expRem rlog)
open LargeDistortions (YnA muY deltaA tipASA rho2A zA fhatIso quad51 loss614 lamYY gamT OmegaW
  OmegaTilde gbarC lamTilde loss615 YstarA Mden)
open Moments (calvoKappa calvoXi)

variable {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)

/-! ## Bounded measurable processes and their expected discounted sums -/

/-- Woodford (2003), (5.2): a bounded, almost-everywhere strongly measurable process. -/
def BM (X : ℕ → Ω → ℝ) : Prop := (∀ t, AEStronglyMeasurable (X t) μ) ∧ BoundedProc X

variable {μ}

/-- Woodford (2003), (5.2): bounded measurable processes are integrable at every date. -/
theorem BM.integrable [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} (h : BM μ X) (t : ℕ) :
    Integrable (X t) μ := by
  obtain ⟨M, hM⟩ := h.2
  exact Integrable.of_bound (h.1 t) M (Eventually.of_forall fun w => by
    rw [Real.norm_eq_abs]; exact hM t w)

/-- Woodford (2003), (5.2): congruence for bounded measurable processes. -/
theorem BM.congr {X Y : ℕ → Ω → ℝ} (hX : BM μ X) (h : ∀ t w, Y t w = X t w) : BM μ Y := by
  have hYX : Y = X := funext fun t => funext fun w => h t w
  rw [hYX]; exact hX

/-- Woodford (2003), (5.2): sums of bounded measurable processes. -/
theorem BM.add {X Y : ℕ → Ω → ℝ} (hX : BM μ X) (hY : BM μ Y) :
    BM μ (fun t w => X t w + Y t w) := by
  refine ⟨fun t => (hX.1 t).add (hY.1 t), ?_⟩
  obtain ⟨M, hM⟩ := hX.2
  obtain ⟨N, hN⟩ := hY.2
  exact ⟨M + N, fun t w => (abs_add_le _ _).trans (add_le_add (hM t w) (hN t w))⟩

/-- Woodford (2003), (5.2): constant multiples of bounded measurable processes. -/
theorem BM.cmul {X : ℕ → Ω → ℝ} (hX : BM μ X) (c : ℝ) : BM μ (fun t w => c * X t w) := by
  refine ⟨fun t => (hX.1 t).const_mul c, ?_⟩
  obtain ⟨M, hM⟩ := hX.2
  exact ⟨|c| * M, fun t w => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t w) (abs_nonneg c)⟩

/-- Woodford (2003), (5.2): differences of bounded measurable processes. -/
theorem BM.sub {X Y : ℕ → Ω → ℝ} (hX : BM μ X) (hY : BM μ Y) : BM μ (fun t w => X t w - Y t w) :=
  BM.congr (hX.add (hY.cmul (-1))) fun t w => by ring

/-- Woodford (2003), (5.2): products of bounded measurable processes. -/
theorem BM.mul {X Y : ℕ → Ω → ℝ} (hX : BM μ X) (hY : BM μ Y) : BM μ (fun t => X t * Y t) :=
  ⟨fun t => (hX.1 t).mul (hY.1 t), Sequences.bdd_mul hX.2 hY.2⟩

/-- Woodford (2003), (5.2): continuous functions of finitely many bounded measurable
processes. -/
theorem BM.of_continuous {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ)
    (X : Fin n → ℕ → Ω → ℝ) (hX : ∀ i, BM μ (X i)) :
    BM μ (fun t w => φ (fun i => X i t w)) := by
  refine ⟨fun t => ?_, Sequences.bdd_of_continuous φ hφ X fun i => (hX i).2⟩
  have : AEMeasurable (fun w => fun i => X i t w) μ :=
    aemeasurable_pi_iff.2 fun i => ((hX i).1 t).aemeasurable
  exact hφ.comp_aestronglyMeasurable this.aestronglyMeasurable

/-- Woodford (2003), (5.2): the expected discounted sum `∑ βᵗ ∫ X_t dμ`. -/
noncomputable def Isum (μ : Measure Ω) (β : ℝ) (X : ℕ → Ω → ℝ) : ℝ := ∑' t, β ^ t * ∫ w, X t w ∂μ

/-- Woodford (2003), (5.2): the expectation of a bounded process is bounded. -/
theorem abs_integral_le [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {M : ℝ}
    (hM : ∀ t w, |X t w| ≤ M) (t : ℕ) : |∫ w, X t w ∂μ| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := X t) (C := M)
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hM t w)
  simpa [Real.norm_eq_abs] using this

/-- Woodford (2003), (5.2): the expected discounted sum of a bounded process converges. -/
theorem hasSum_Isum [IsProbabilityMeasure μ] {β : ℝ} (hβ : |β| < 1) {X : ℕ → Ω → ℝ}
    (hX : BoundedProc X) : HasSum (fun t => β ^ t * ∫ w, X t w ∂μ) (Isum μ β X) := by
  obtain ⟨M, hM⟩ := hX
  exact (Sequences.summable_geom_bdd hβ (fun t => abs_integral_le hM t)).hasSum

/-! ## The recursions for `F` and `K` with conditional expectations -/

variable (μ) in
/-- Woodford (2003), §5 (Benigno–Woodford), with GENUINE conditional expectations: the
recursion `e^{F̂_t} − 1 = (1−αβ)(e^{f̂_t} − 1) + αβ E_t(e^{eπ_{t+1} + F̂_{t+1}} − 1)` almost
surely, `E_t = μ[· | m_t]`. -/
def RecEqM (m : ℕ → MeasurableSpace Ω) (α β e : ℝ) (infl F f : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun w => Real.exp (F t w) - 1) =ᵐ[μ] fun w =>
    (1 - α * β) * (Real.exp (f t w) - 1) +
      α * β * (μ[fun w => Real.exp (e * infl (t + 1) w + F (t + 1) w) - 1 | m t]) w

/-- Woodford (2003), (5.2): the expectation of a sum of five integrable terms. -/
theorem integral_add5 {a b c d e : Ω → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hd : Integrable d μ) (he : Integrable e μ) :
    ∫ w, (a w + b w + c w + d w + e w) ∂μ =
      ∫ w, a w ∂μ + ∫ w, b w ∂μ + ∫ w, c w ∂μ + ∫ w, d w ∂μ + ∫ w, e w ∂μ := by
  rw [integral_add (f := fun w => a w + b w + c w + d w) (g := e)
      (((ha.add hb).add hc).add hd) he,
    integral_add (f := fun w => a w + b w + c w) (g := d) ((ha.add hb).add hc) hd,
    integral_add (f := fun w => a w + b w) (g := c) (ha.add hb) hc,
    integral_add (f := a) (g := b) ha hb]

/-- Woodford (2003), (5.2): the expectation of a linear combination of five integrable terms. -/
theorem integral_lc5 {a b c d e : Ω → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hd : Integrable d μ) (he : Integrable e μ) (ca cb cc cd ce : ℝ) :
    ∫ w, (ca * a w + cb * b w + cc * c w + cd * d w + ce * e w) ∂μ =
      ca * ∫ w, a w ∂μ + cb * ∫ w, b w ∂μ + cc * ∫ w, c w ∂μ + cd * ∫ w, d w ∂μ +
        ce * ∫ w, e w ∂μ := by
  rw [integral_add5 (a := fun w => ca * a w) (b := fun w => cb * b w) (c := fun w => cc * c w)
    (d := fun w => cd * d w) (e := fun w => ce * e w) (ha.const_mul ca) (hb.const_mul cb)
    (hc.const_mul cc) (hd.const_mul cd) (he.const_mul ce), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- Woodford (2003), (5.2): the expectation of a linear combination of seven integrable terms. -/
theorem integral_lc7 {a b c d e f g : Ω → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hd : Integrable d μ) (he : Integrable e μ) (hf : Integrable f μ)
    (hg : Integrable g μ) (ca cb cc cd ce cf cg : ℝ) :
    ∫ w, (ca * a w + cb * b w + cc * c w + cd * d w + ce * e w + cf * f w + cg * g w) ∂μ =
      ca * ∫ w, a w ∂μ + cb * ∫ w, b w ∂μ + cc * ∫ w, c w ∂μ + cd * ∫ w, d w ∂μ +
        ce * ∫ w, e w ∂μ + cf * ∫ w, f w ∂μ + cg * ∫ w, g w ∂μ := by
  have i5 : Integrable (fun w => ca * a w + cb * b w + cc * c w + cd * d w + ce * e w) μ :=
    ((((ha.const_mul ca).add (hb.const_mul cb)).add (hc.const_mul cc)).add
      (hd.const_mul cd)).add (he.const_mul ce)
  rw [integral_add (f := fun w => ca * a w + cb * b w + cc * c w + cd * d w + ce * e w +
      cf * f w) (g := fun w => cg * g w) (i5.add (hf.const_mul cf)) (hg.const_mul cg),
    integral_add (f := fun w => ca * a w + cb * b w + cc * c w + cd * d w + ce * e w)
      (g := fun w => cf * f w) i5 (hf.const_mul cf), integral_lc5 ha hb hc hd he,
    integral_const_mul, integral_const_mul]

/-- Woodford (2003), (5.4): the date-`t` part `nowA` of the weight-three remainder of the
second-order AS relation, as a process. -/
noncomputable def nowP (α β θ ω : ℝ) (infl xr F K f k : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => nowA α β θ ω (infl t w) (xr t w) ((K t w + F t w) / 2) (expRem ((θ - 1) * infl t w))
    (expRem (-((θ - 1) * xr t w))) (expRem (K t w)) (expRem (F t w)) (expRem (k t w))
    (expRem (f t w))

/-- Woodford (2003), App. E, p. 693: the exponential atom is continuous. -/
theorem continuous_expRem : Continuous expRem := by
  unfold expRem; fun_prop

/-- Woodford (2003), §5, p. 457 ("a quadratic approximation to the aggregate supply
relation"), with GENUINE conditional expectations, integrated: under the exact price index and
reset-price conditions and the recursions for `F` and `K` almost surely,
`E V_t = κ̃ E[(k̂_t − f̂_t)(1 + (k̂_t + f̂_t)/2)] + (βθ(1+ω)/2) E π_{t+1}² + β E V_{t+1}
  + E nowA_t + β E rest_{t+1}` (the conditional expectations integrate out). -/
theorem second_order_AS_int [IsProbabilityMeasure μ] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ t, m t ≤ ‹MeasurableSpace Ω›) {α β θ ω : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : θ ≠ 1) (hν : 1 + ω * θ ≠ 0) {infl xr F K f k : ℕ → Ω → ℝ}
    (hP : LargeDistortions.PriceIndexEq α θ infl xr) (hR : LargeDistortions.ResetPriceEq ω θ xr F K)
    (hF : RecEqM μ m α β (θ - 1) infl F f) (hK : RecEqM μ m α β (θ * (1 + ω)) infl K k)
    (bi : BM μ infl) (bx : BM μ xr) (bF : BM μ F) (bK : BM μ K) (bf : BM μ f) (bk : BM μ k)
    (t : ℕ) :
    ∫ w, Vp α θ infl F K t w ∂μ =
      ∫ w, Moments.calvoXi α β ω θ * (k t w - f t w) * (1 + (k t w + f t w) / 2) ∂μ +
        β * (θ * (1 + ω)) / 2 * ∫ w, infl (t + 1) w ^ 2 ∂μ +
        β * ∫ w, Vp α θ infl F K (t + 1) w ∂μ + ∫ w, nowP α β θ ω infl xr F K f k t w ∂μ +
        β * ∫ w, restP α θ ω infl xr F K (t + 1) w ∂μ := by
  -- bounded measurable building blocks
  have X6 : ∀ i, BM μ (![infl, xr, F, K, f, k] i) := by
    intro i; fin_cases i <;> assumption
  have bV : BM μ (Vp α θ infl F K) := BM.congr (BM.of_continuous
    (fun v => VA α θ (v 0) ((v 3 + v 2) / 2)) (by unfold VA; fun_prop) _ X6)
    (fun t w => by simp [Vp])
  have bP2 : BM μ (fun t w => infl t w ^ 2) := BM.congr (BM.mul bi bi)
    (fun t w => by simp only [Pi.mul_apply]; ring)
  have bRest : BM μ (restP α θ ω infl xr F K) := BM.congr (BM.of_continuous
    (fun v => restA α θ ω (v 0) (v 1) ((v 3 + v 2) / 2) (expRem ((θ - 1) * v 0))
      (expRem (-((θ - 1) * v 1))) (expRem (θ * (1 + ω) * v 0 + v 3))
      (expRem ((θ - 1) * v 0 + v 2)))
    (by
      unfold restA h3A hA
      have := continuous_expRem
      fun_prop) _ X6) (fun t w => by simp [restP])
  have bNow : BM μ (nowP α β θ ω infl xr F K f k) := BM.congr (BM.of_continuous
    (fun v => nowA α β θ ω (v 0) (v 1) ((v 3 + v 2) / 2) (expRem ((θ - 1) * v 0))
      (expRem (-((θ - 1) * v 1))) (expRem (v 3)) (expRem (v 2)) (expRem (v 5)) (expRem (v 4)))
    (by
      unfold nowA h3A hA
      have := continuous_expRem
      fun_prop) _ X6) (fun t w => by simp [nowP])
  have bXF : BM μ (fun t w => Real.exp ((θ - 1) * infl t w + F t w) - 1) := BM.congr
    (BM.of_continuous (fun v => Real.exp ((θ - 1) * v 0 + v 2) - 1) (by fun_prop) _ X6)
    (fun t w => by simp)
  have bkf : BM μ (fun t w => Moments.calvoXi α β ω θ * (k t w - f t w) *
      (1 + (k t w + f t w) / 2)) := BM.congr (BM.of_continuous
    (fun v => Moments.calvoXi α β ω θ * (v 5 - v 4) * (1 + (v 5 + v 4) / 2)) (by fun_prop) _ X6)
    (fun t w => by simp)
  -- the date-`(t+1)` identity, pathwise
  set c : ℝ := (1 + ω * θ) / (1 - α) with hc
  set d : ℝ := θ * (1 + ω) / 2 with hd
  have hnext : (fun w => Real.exp (θ * (1 + ω) * infl (t + 1) w + K (t + 1) w) - 1) =
      (fun w => Real.exp ((θ - 1) * infl (t + 1) w + F (t + 1) w) - 1) +
        c • (Vp α θ infl F K (t + 1) + d • (fun w => infl (t + 1) w ^ 2) +
          restP α θ ω infl xr F K (t + 1)) := by
    funext w
    have E1 := LargeDistortions.xr_eq_of_priceIndex hα0 hα1 hθ (hP (t + 1) w)
    have h := LargeDistortions.next_identity hα0 hα1 hθ hν E1 (hR (t + 1) w)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Vp, restP, hc, hd]
    linear_combination h
  -- conditional expectations are linear almost surely
  have hE : μ[fun w => Real.exp (θ * (1 + ω) * infl (t + 1) w + K (t + 1) w) - 1 | m t]
      =ᵐ[μ] μ[fun w => Real.exp ((θ - 1) * infl (t + 1) w + F (t + 1) w) - 1 | m t] +
        c • (μ[Vp α θ infl F K (t + 1) | m t] + d • μ[fun w => infl (t + 1) w ^ 2 | m t] +
          μ[restP α θ ω infl xr F K (t + 1) | m t]) := by
    rw [hnext]
    have i1 := bXF.integrable (t + 1)
    have i2 := bV.integrable (t + 1)
    have i3 := bP2.integrable (t + 1)
    have i4 := bRest.integrable (t + 1)
    filter_upwards [condExp_add i1 (((i2.add (i3.smul d)).add i4).smul c) (m t),
      condExp_smul c (Vp α θ infl F K (t + 1) + d • (fun w => infl (t + 1) w ^ 2) +
        restP α θ ω infl xr F K (t + 1)) (m t),
      condExp_add (i2.add (i3.smul d)) i4 (m t), condExp_add i2 (i3.smul d) (m t),
      condExp_smul d (fun w => infl (t + 1) w ^ 2) (m t)] with w h1 h2 h3 h4 h5
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 h5 ⊢
    rw [h1, h2, h3, h4, h5]
  -- the pointwise identity, almost surely
  have hpt : (fun w => Vp α θ infl F K t w) =ᵐ[μ] fun w =>
      Moments.calvoXi α β ω θ * (k t w - f t w) * (1 + (k t w + f t w) / 2) +
        β * (θ * (1 + ω)) / 2 * (μ[fun w => infl (t + 1) w ^ 2 | m t]) w +
        β * (μ[Vp α θ infl F K (t + 1) | m t]) w + nowP α β θ ω infl xr F K f k t w +
        β * (μ[restP α θ ω infl xr F K (t + 1) | m t]) w := by
    filter_upwards [hF t, hK t, hE] with w hFw hKw hEw
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hEw
    have hstar : (Real.exp (K t w) - 1) - (Real.exp (F t w) - 1) =
        (1 - α * β) * ((Real.exp (k t w) - 1) - (Real.exp (f t w) - 1)) +
          α * β * ((1 + ω * θ) / (1 - α) * ((μ[Vp α θ infl F K (t + 1) | m t]) w +
            θ * (1 + ω) / 2 * (μ[fun w => infl (t + 1) w ^ 2 | m t]) w +
              (μ[restP α θ ω infl xr F K (t + 1) | m t]) w)) := by
      rw [hKw, hFw, hEw]; simp only [hc, hd]; ring
    have E1 := LargeDistortions.xr_eq_of_priceIndex hα0 hα1 hθ (hP t w)
    have key := LargeDistortions.now_identity (β := β) hα0 hα1 hθ hν E1 (hR t w) hstar
    simp only [Vp, nowP]
    rw [key]
    ring
  -- integrate
  have iC1 : Integrable (μ[fun w => infl (t + 1) w ^ 2 | m t]) μ := integrable_condExp
  have iC2 : Integrable (μ[Vp α θ infl F K (t + 1) | m t]) μ := integrable_condExp
  have iC3 : Integrable (μ[restP α θ ω infl xr F K (t + 1) | m t]) μ := integrable_condExp
  rw [integral_congr_ae hpt, integral_add5 (bkf.integrable t) (iC1.const_mul _)
    (iC2.const_mul _) (bNow.integrable t) (iC3.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_condExp (hm t), integral_condExp (hm t),
    integral_condExp (hm t)]

/-! ## The exact Calvo conditions with conditional expectations, and (5.4) integrated -/

variable (μ) (m : ℕ → MeasurableSpace Ω) (α β θ ω σ sC : ℝ)
  (infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ) in
/-- Woodford (2003), §5, pp. 457–458 (Benigno–Woodford 2003), with GENUINE conditional
expectations: the exact Calvo conditions under Assumption 6.2 (price index, reset price,
the recursions for `F` and `K` almost surely, isoelastic `k̂` and `f̂`). -/
structure CalvoASM where
  /-- Woodford (2003), §5 (Benigno–Woodford): the price index. -/
  priceIndex : LargeDistortions.PriceIndexEq α θ infl xr
  /-- Woodford (2003), §5 (Benigno–Woodford): the reset price. -/
  resetPrice : LargeDistortions.ResetPriceEq ω θ xr F K
  /-- Woodford (2003), §5, p. 457: the recursion for `F`, almost surely. -/
  recF : RecEqM μ m α β (θ - 1) infl F f
  /-- Woodford (2003), §5, p. 457: the recursion for `K`, almost surely. -/
  recK : RecEqM μ m α β (θ * (1 + ω)) infl K k
  /-- Woodford (2003), §5, p. 457: the isoelastic `k̂`. -/
  costK : ∀ t w, k t w = (1 + ω) * Y t w - ω * q t w + muw t w
  /-- Woodford (2003), §5, p. 457: the isoelastic `f̂`. -/
  revF : ∀ t w, f t w = fhatIso σ sC (Y t w) (G t w) (cb t w) (tau t w)

/-- Woodford (2003), (5.4), on a probability space: the weight-three remainder process, the
date-`t` atoms, `β` times the date-`(t+1)` atoms (no conditional expectation: it is integrated
out), and the AS-expansion remainder. -/
noncomputable def remASm (α β θ ω σ sC : ℝ) (infl xr F K f k Y G cb tau : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun w => nowP α β θ ω infl xr F K f k t w + β * restP α θ ω infl xr F K (t + 1) w +
    rho2A α β θ ω σ sC (Y t w) (G t w) (cb t w) (tau t w) (expRem (Y t w))
      (rlog (zA sC (Y t w) (G t w)))

/-- Woodford (2003), eq. (5.4), p. 458, DERIVED IN FULL from the exact Calvo model under
Assumption 6.2 with GENUINE conditional expectations (expectations are integrals; the
conditional expectations of the recursions integrate out): with bounded measurable processes,
`E[V_0 + (μ_π/2)π_0²] = κ∑βᵗE(Ŷ_t − Ŷⁿ_t) + (μ_y/2)∑βᵗEŶ_t² − ∑βᵗE δ_tŶ_t
  + (μ_π/2)∑βᵗEπ_t² + ∑βᵗE tipASA + ∑βᵗE remASm`. -/
theorem eq54M [IsProbabilityMeasure μ] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ t, m t ≤ ‹MeasurableSpace Ω›) {α β θ ω σ sC : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 1) (hν : 1 + ω * θ ≠ 0) (hs : sC ≠ 0)
    (hc : ω + σ ≠ 0) {infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ}
    (hM : CalvoASM μ m α β θ ω σ sC infl xr F K f k Y G cb q muw tau)
    (bi : BM μ infl) (bx : BM μ xr) (bF : BM μ F) (bK : BM μ K) (bf : BM μ f) (bk : BM μ k)
    (bY : BM μ Y) (bG : BM μ G) (bcb : BM μ cb) (bq : BM μ q) (bm : BM μ muw) (bt : BM μ tau) :
    ∫ w, (Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) ∂μ =
      calvoKappa α β ω θ σ * Isum μ β (fun t w => Y t w -
          YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w))
        + muY α β θ ω σ sC / 2 * Isum μ β (fun t w => Y t w ^ 2)
        - Isum μ β (fun t w => deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) *
            Y t w)
        + θ * (1 + ω) / 2 * Isum μ β (fun t w => infl t w ^ 2)
        + Isum μ β (fun t w => tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w))
        + Isum μ β (remASm α β θ ω σ sC infl xr F K f k Y G cb tau) := by
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  set b : ℝ := θ * (1 + ω) with hb
  set P1 : ℕ → Ω → ℝ := fun t w => Y t w - YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)
    with hP1
  set P2 : ℕ → Ω → ℝ := fun t w => Y t w ^ 2 with hP2
  set P3 : ℕ → Ω → ℝ := fun t w =>
    deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w with hP3
  set P4 : ℕ → Ω → ℝ := fun t w =>
    tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) with hP4
  set P5 : ℕ → Ω → ℝ := fun t w => infl t w ^ 2 with hP5
  set Rm := remASm α β θ ω σ sC infl xr F K f k Y G cb tau with hRm
  -- bounded measurable building blocks
  have bX : ∀ i, BM μ (![Y, G, cb, q, muw, tau] i) := by
    intro i; fin_cases i <;> assumption
  have b1 : BM μ P1 := BM.congr (BM.of_continuous
    (fun v => v 0 - YnA ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5)) (by unfold YnA; fun_prop) _ bX)
    (fun t w => by simp [P1])
  have b2 : BM μ P2 := BM.congr (BM.mul bY bY) (fun t w => by simp only [P2, Pi.mul_apply]; ring)
  have b3 : BM μ P3 := BM.congr (BM.of_continuous
    (fun v => deltaA α β θ ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5) * v 0)
    (by unfold deltaA; fun_prop) _ bX) (fun t w => by simp [P3])
  have b4 : BM μ P4 := BM.congr (BM.of_continuous
    (fun v => tipASA α β θ ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5))
    (by unfold tipASA; fun_prop) _ bX) (fun t w => by simp [P4])
  have b5 : BM μ P5 := BM.congr (BM.mul bi bi) (fun t w => by simp only [P5, Pi.mul_apply]; ring)
  have X6 : ∀ i, BM μ (![infl, xr, F, K, f, k] i) := by
    intro i; fin_cases i <;> assumption
  have bV : BM μ (Vp α θ infl F K) := BM.congr (BM.of_continuous
    (fun v => VA α θ (v 0) ((v 3 + v 2) / 2)) (by unfold VA; fun_prop) _ X6)
    (fun t w => by simp [Vp])
  have bRest : BM μ (restP α θ ω infl xr F K) := BM.congr (BM.of_continuous
    (fun v => restA α θ ω (v 0) (v 1) ((v 3 + v 2) / 2) (expRem ((θ - 1) * v 0))
      (expRem (-((θ - 1) * v 1))) (expRem (θ * (1 + ω) * v 0 + v 3))
      (expRem ((θ - 1) * v 0 + v 2)))
    (by
      unfold restA h3A hA
      have := continuous_expRem
      fun_prop) _ X6) (fun t w => by simp [restP])
  have bNow : BM μ (nowP α β θ ω infl xr F K f k) := BM.congr (BM.of_continuous
    (fun v => nowA α β θ ω (v 0) (v 1) ((v 3 + v 2) / 2) (expRem ((θ - 1) * v 0))
      (expRem (-((θ - 1) * v 1))) (expRem (v 3)) (expRem (v 2)) (expRem (v 5)) (expRem (v 4)))
    (by
      unfold nowA h3A hA
      have := continuous_expRem
      fun_prop) _ X6) (fun t w => by simp [nowP])
  have bkf : BM μ (fun t w => calvoXi α β ω θ * (k t w - f t w) *
      (1 + (k t w + f t w) / 2)) := BM.congr (BM.of_continuous
    (fun v => calvoXi α β ω θ * (v 5 - v 4) * (1 + (v 5 + v 4) / 2)) (by fun_prop) _ X6)
    (fun t w => by simp)
  -- the AS expansion, pathwise, and the remainder
  have hexp : ∀ t w, calvoXi α β ω θ * (k t w - f t w) * (1 + (k t w + f t w) / 2) =
      calvoKappa α β ω θ σ * P1 t w + muY α β θ ω σ sC / 2 * P2 t w - P3 t w + P4 t w +
        rho2A α β θ ω σ sC (Y t w) (G t w) (cb t w) (tau t w) (expRem (Y t w))
          (rlog (zA sC (Y t w) (G t w))) := fun t w => by
    rw [hM.costK t w, hM.revF t w]
    unfold fhatIso
    exact LargeDistortions.as_expand hs hc (Y t w) (G t w) (cb t w) (q t w) (muw t w) (tau t w)
  have bRho : BM μ (fun t w => rho2A α β θ ω σ sC (Y t w) (G t w) (cb t w) (tau t w)
      (expRem (Y t w)) (rlog (zA sC (Y t w) (G t w)))) :=
    BM.congr ((((bkf.sub (b1.cmul (calvoKappa α β ω θ σ))).sub
      (b2.cmul (muY α β θ ω σ sC / 2))).add b3).sub b4) fun t w => by
        have h := hexp t w
        linarith
  set ρ2 : ℕ → Ω → ℝ := fun t w => rho2A α β θ ω σ sC (Y t w) (G t w) (cb t w) (tau t w)
    (expRem (Y t w)) (rlog (zA sC (Y t w) (G t w))) with hρ2
  -- the integrated second-order AS relation
  have hstep : ∀ t, ∫ w, Vp α θ infl F K t w ∂μ - β * ∫ w, Vp α θ infl F K (t + 1) w ∂μ =
      calvoKappa α β ω θ σ * ∫ w, P1 t w ∂μ + muY α β θ ω σ sC / 2 * ∫ w, P2 t w ∂μ -
        ∫ w, P3 t w ∂μ + ∫ w, P4 t w ∂μ + β * b / 2 * ∫ w, P5 (t + 1) w ∂μ +
        ∫ w, Rm t w ∂μ := by
    intro t
    have h := second_order_AS_int hm hα0 hα1 hθ hν hM.priceIndex hM.resetPrice hM.recF hM.recK
      bi bx bF bK bf bk t
    have hkf : ∫ w, calvoXi α β ω θ * (k t w - f t w) * (1 + (k t w + f t w) / 2) ∂μ =
        calvoKappa α β ω θ σ * ∫ w, P1 t w ∂μ + muY α β θ ω σ sC / 2 * ∫ w, P2 t w ∂μ -
          ∫ w, P3 t w ∂μ + ∫ w, P4 t w ∂μ + ∫ w, ρ2 t w ∂μ := by
      have e : ∫ w, calvoXi α β ω θ * (k t w - f t w) * (1 + (k t w + f t w) / 2) ∂μ =
          ∫ w, (calvoKappa α β ω θ σ * P1 t w + muY α β θ ω σ sC / 2 * P2 t w +
            -P3 t w + P4 t w + ρ2 t w) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun w => by
          simp only [hρ2]; rw [hexp t w]; ring)
      rw [e, integral_add5 (a := fun w => calvoKappa α β ω θ σ * P1 t w)
        (b := fun w => muY α β θ ω σ sC / 2 * P2 t w) (c := fun w => -P3 t w) (d := P4 t)
        (e := ρ2 t) ((b1.integrable t).const_mul _) ((b2.integrable t).const_mul _)
        (b3.integrable t).neg (b4.integrable t) (bRho.integrable t), integral_const_mul,
        integral_const_mul, integral_neg]
      ring
    have hRm : ∫ w, Rm t w ∂μ = ∫ w, nowP α β θ ω infl xr F K f k t w ∂μ +
        β * ∫ w, restP α θ ω infl xr F K (t + 1) w ∂μ + ∫ w, ρ2 t w ∂μ := by
      have e : ∫ w, Rm t w ∂μ = ∫ w, (nowP α β θ ω infl xr F K f k t w +
          β * restP α θ ω infl xr F K (t + 1) w + ρ2 t w) ∂μ := rfl
      rw [e, integral_add (f := fun w => nowP α β θ ω infl xr F K f k t w +
          β * restP α θ ω infl xr F K (t + 1) w) (g := ρ2 t)
          ((bNow.integrable t).add ((bRest.integrable (t + 1)).const_mul β)) (bRho.integrable t),
        integral_add (f := nowP α β θ ω infl xr F K f k t)
          (g := fun w => β * restP α θ ω infl xr F K (t + 1) w)
          (bNow.integrable t) ((bRest.integrable (t + 1)).const_mul β),
        integral_const_mul]
    rw [h, hkf, hRm]
    simp only [hP5, hb]
    ring
  -- forward integration
  obtain ⟨MV, hMV⟩ := bV.2
  have hv : ∀ t, |∫ w, Vp α θ infl F K t w ∂μ| ≤ MV := fun t => abs_integral_le hMV t
  set d : ℕ → ℝ := fun t =>
    ∫ w, Vp α θ infl F K t w ∂μ - β * ∫ w, Vp α θ infl F K (t + 1) w ∂μ with hd
  have hfw := Sequences.forward_real hβ hv (d := d) (fun t => by simp only [d]; ring)
  have hdb : ∀ t, |d t| ≤ MV + |β| * MV := by
    intro t
    simp only [d]
    calc |∫ w, Vp α θ infl F K t w ∂μ - β * ∫ w, Vp α θ infl F K (t + 1) w ∂μ|
        ≤ |∫ w, Vp α θ infl F K t w ∂μ| + |β * ∫ w, Vp α θ infl F K (t + 1) w ∂μ| :=
          abs_sub _ _
      _ ≤ MV + |β| * MV := by
          rw [abs_mul]
          exact add_le_add (hv t) (mul_le_mul_of_nonneg_left (hv (t + 1)) (abs_nonneg β))
  have sd : HasSum (fun t => β ^ t * d t) (∫ w, Vp α θ infl F K 0 w ∂μ) := by
    rw [hfw]; exact (Sequences.summable_geom_bdd hβ hdb).hasSum
  have s1 := hasSum_Isum (μ := μ) hβ b1.2
  have s2 := hasSum_Isum (μ := μ) hβ b2.2
  have s3 := hasSum_Isum (μ := μ) hβ b3.2
  have s4 := hasSum_Isum (μ := μ) hβ b4.2
  obtain ⟨M5, hM5⟩ := b5.2
  have sum5 : Summable (fun t => β ^ t * ∫ w, P5 t w ∂μ) :=
    Sequences.summable_geom_bdd hβ (fun t => abs_integral_le hM5 t)
  have sum5s : Summable (fun t => β ^ t * ∫ w, P5 (t + 1) w ∂μ) :=
    Sequences.summable_geom_bdd hβ (fun t => abs_integral_le hM5 (t + 1))
  have hshift := Sequences.tsum_geom_shift sum5
  have s5s : HasSum (fun t => β ^ t * (β * b / 2 * ∫ w, P5 (t + 1) w ∂μ))
      (b / 2 * (Isum μ β P5 - ∫ w, P5 0 w ∂μ)) := by
    have := sum5s.hasSum.mul_left (β * b / 2)
    convert this using 1
    · funext t; ring
    · have e : Isum μ β P5 = ∫ w, P5 0 w ∂μ + β * ∑' t, β ^ t * ∫ w, P5 (t + 1) w ∂μ :=
        hshift
      rw [e]; ring
  have sR : HasSum (fun t => β ^ t * ∫ w, Rm t w ∂μ)
      (∫ w, Vp α θ infl F K 0 w ∂μ - (calvoKappa α β ω θ σ * Isum μ β P1 +
        muY α β θ ω σ sC / 2 * Isum μ β P2 - Isum μ β P3 + Isum μ β P4 +
        b / 2 * (Isum μ β P5 - ∫ w, P5 0 w ∂μ))) := by
    have := sd.sub (((((s1.mul_left (calvoKappa α β ω θ σ)).add
      (s2.mul_left (muY α β θ ω σ sC / 2))).sub s3).add s4).add s5s)
    convert this using 1
    funext t
    have := hstep t
    simp only [d]
    rw [this]
    ring
  have eR : Isum μ β Rm = _ := sR.tsum_eq
  -- assemble
  have hL : ∫ w, (Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) ∂μ =
      ∫ w, Vp α θ infl F K 0 w ∂μ + b / 2 * ∫ w, P5 0 w ∂μ := by
    rw [integral_add (bV.integrable 0) ((b5.integrable 0).const_mul _), integral_const_mul]
  rw [hL, eR]
  ring

/-! ## Proposition 6.14 with expectations as integrals -/

/-- Woodford (2003), **Proposition 6.14**, (5.2)–(5.3), p. 456, with expectations as integrals
on a probability space: for bounded measurable processes with the period utility (`h51`), the
dispersion as the variance of log prices (`hV`) and the Calvo law (`hD`),
`∑βᵗEU_t = −Ω∑βᵗEL_t + (∑βᵗE t.i.p._t − Ω(1−α)ED_0) + (∑βᵗER_t − Ω∑βᵗE(π̄_t² − π_t²))`. -/
theorem prop614M [IsProbabilityMeasure μ] {α β θ ω σ Φ Ybar uc : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ)
    (hΦ : Φ < 1) {U Y infl g q V D pib tipU R : ℕ → Ω → ℝ}
    (bY : BM μ Y) (bi : BM μ infl) (bg : BM μ g) (bq : BM μ q) (bD : BM μ D) (bp : BM μ pib)
    (bt : BM μ tipU) (bR : BM μ R)
    (h51 : ∀ t, U t = (fun w => -(Ybar * uc / 2) *
        quad51 σ ω θ Φ (g t w) (q t w) (Y t w) (V t w)) + tipU t + R t)
    (hV : ∀ t, V t = θ ^ 2 • D (t + 1))
    (hD : ∀ t, D (t + 1) = α • D t + (α / (1 - α)) • pib t ^ 2) :
    Isum μ β U =
      -OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ *
          Isum μ β (loss614 (calvoKappa α β ω θ σ) θ Φ ω σ infl Y g q) +
        (Isum μ β tipU -
          OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) * ∫ w, D 0 w ∂μ) +
        (Isum μ β R - OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ *
          (Isum μ β (fun t => pib t ^ 2) - Isum μ β (fun t => infl t ^ 2))) := by
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  -- bounded measurable building blocks
  have bY2 : BM μ (fun t => Y t ^ 2) := BM.congr (BM.mul bY bY) fun t w => by
    simp only [Pi.pow_apply, Pi.mul_apply]; ring
  have bgY : BM μ (fun t => g t * Y t) := BM.congr (BM.mul bg bY) fun t w => rfl
  have bqY : BM μ (fun t => q t * Y t) := BM.congr (BM.mul bq bY) fun t w => rfl
  have bpi2 : BM μ (fun t => infl t ^ 2) := BM.congr (BM.mul bi bi) fun t w => by
    simp only [Pi.pow_apply, Pi.mul_apply]; ring
  have bpib2 : BM μ (fun t => pib t ^ 2) := BM.congr (BM.mul bp bp) fun t w => by
    simp only [Pi.pow_apply, Pi.mul_apply]; ring
  -- sums
  have sY := hasSum_Isum (μ := μ) hβ bY.2
  have sY2 := hasSum_Isum (μ := μ) hβ bY2.2
  have sgY := hasSum_Isum (μ := μ) hβ bgY.2
  have sqY := hasSum_Isum (μ := μ) hβ bqY.2
  have spi2 := hasSum_Isum (μ := μ) hβ bpi2.2
  have stip := hasSum_Isum (μ := μ) hβ bt.2
  have sR := hasSum_Isum (μ := μ) hβ bR.2
  -- the dispersion sum
  obtain ⟨MD, hMD⟩ := bD.2
  obtain ⟨Mp, hMp⟩ := bpib2.2
  have hdrec : ∀ t, ∫ w, D (t + 1) w ∂μ =
      α * ∫ w, D t w ∂μ + α / (1 - α) * ∫ w, (pib t ^ 2) w ∂μ := by
    intro t
    have e : ∫ w, D (t + 1) w ∂μ = ∫ w, (α * D t w + α / (1 - α) * (pib t ^ 2) w) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun w => by
        rw [hD t]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul])
    rw [e, integral_add ((bD.integrable t).const_mul α) ((bpib2.integrable t).const_mul _),
      integral_const_mul, integral_const_mul]
  have hdisp := Sequences.dispersion_tsum hβ (fun t => abs_integral_le (μ := μ) hMD t)
    (fun t => abs_integral_le (μ := μ) hMp t) hdrec
  have sD : HasSum (fun t => β ^ t * ∫ w, D (t + 1) w ∂μ)
      (∑' t, β ^ t * ∫ w, D (t + 1) w ∂μ) :=
    (Sequences.summable_geom_bdd hβ (fun t => abs_integral_le (μ := μ) hMD (t + 1))).hasSum
  -- expectation of the period utility
  have hUt : ∀ t, ∫ w, U t w ∂μ =
      -(Ybar * uc / 2) * ((σ + ω - Φ * (1 + ω)) * ∫ w, (Y t ^ 2) w ∂μ
        - 2 * Φ * ∫ w, Y t w ∂μ - 2 * σ * ∫ w, (g t * Y t) w ∂μ
        - 2 * ((1 - Φ) * ω) * ∫ w, (q t * Y t) w ∂μ
        + (1 - Φ) * (θ⁻¹ + ω) * θ ^ 2 * ∫ w, D (t + 1) w ∂μ)
      + ∫ w, tipU t w ∂μ + ∫ w, R t w ∂μ := by
    intro t
    have e : ∫ w, U t w ∂μ = ∫ w, (-(Ybar * uc / 2) * (σ + ω - Φ * (1 + ω)) * (Y t ^ 2) w +
        -(Ybar * uc / 2) * (-(2 * Φ)) * Y t w + -(Ybar * uc / 2) * (-(2 * σ)) * (g t * Y t) w +
        -(Ybar * uc / 2) * (-(2 * ((1 - Φ) * ω))) * (q t * Y t) w +
        -(Ybar * uc / 2) * ((1 - Φ) * (θ⁻¹ + ω) * θ ^ 2) * D (t + 1) w + 1 * tipU t w +
        1 * R t w) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun w => by
        rw [h51 t]
        simp only [quad51, hV t, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply,
          smul_eq_mul]
        ring)
    rw [e, integral_lc7 (bY2.integrable t) (bY.integrable t) (bgY.integrable t)
      (bqY.integrable t) (bD.integrable (t + 1)) (bt.integrable t) (bR.integrable t)]
    ring
  have hLt : ∀ t, ∫ w, loss614 (calvoKappa α β ω θ σ) θ Φ ω σ infl Y g q t w ∂μ =
      ∫ w, (infl t ^ 2) w ∂μ + lamYY (calvoKappa α β ω θ σ) θ Φ ω σ * ∫ w, (Y t ^ 2) w ∂μ
        - 2 * (calvoKappa α β ω θ σ / θ / ((1 - Φ) * (ω + σ))) *
          (Φ * ∫ w, Y t w ∂μ + σ * ∫ w, (g t * Y t) w ∂μ +
            (1 - Φ) * ω * ∫ w, (q t * Y t) w ∂μ) := by
    intro t
    set c := calvoKappa α β ω θ σ / θ / ((1 - Φ) * (ω + σ)) with hc
    have e : ∫ w, loss614 (calvoKappa α β ω θ σ) θ Φ ω σ infl Y g q t w ∂μ =
        ∫ w, (1 * (infl t ^ 2) w + lamYY (calvoKappa α β ω θ σ) θ Φ ω σ * (Y t ^ 2) w +
          (-(2 * c * Φ)) * Y t w + (-(2 * c * σ)) * (g t * Y t) w +
          (-(2 * c * ((1 - Φ) * ω))) * (q t * Y t) w) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun w => by
        simp only [loss614, gamT, Pi.pow_apply, Pi.mul_apply, hc]
        ring)
    rw [e, integral_lc5 (bpi2.integrable t) (bY2.integrable t) (bY.integrable t)
      (bgY.integrable t) (bqY.integrable t)]
    ring
  -- assemble
  set κ := calvoKappa α β ω θ σ with hκ
  set Om := OmegaW Ybar uc κ θ Φ ω σ with hOm
  have hU : HasSum (fun t => β ^ t * ∫ w, U t w ∂μ)
      (-(Ybar * uc / 2) * ((σ + ω - Φ * (1 + ω)) * Isum μ β (fun t => Y t ^ 2)
        - 2 * Φ * Isum μ β Y - 2 * σ * Isum μ β (fun t => g t * Y t)
        - 2 * ((1 - Φ) * ω) * Isum μ β (fun t => q t * Y t)
        + (1 - Φ) * (θ⁻¹ + ω) * θ ^ 2 * ∑' t, β ^ t * ∫ w, D (t + 1) w ∂μ)
      + Isum μ β tipU + Isum μ β R) := by
    have := ((((((sY2.mul_left (σ + ω - Φ * (1 + ω))).sub (sY.mul_left (2 * Φ))).sub
      (sgY.mul_left (2 * σ))).sub (sqY.mul_left (2 * ((1 - Φ) * ω)))).add
      (sD.mul_left ((1 - Φ) * (θ⁻¹ + ω) * θ ^ 2))).mul_left (-(Ybar * uc / 2))).add stip
      |>.add sR
    convert this using 1
    funext t
    rw [hUt t]
    ring
  have hL : HasSum (fun t => β ^ t * ∫ w, loss614 κ θ Φ ω σ infl Y g q t w ∂μ)
      (Isum μ β (fun t => infl t ^ 2) + lamYY κ θ Φ ω σ * Isum μ β (fun t => Y t ^ 2)
        - 2 * (κ / θ / ((1 - Φ) * (ω + σ))) * (Φ * Isum μ β Y
          + σ * Isum μ β (fun t => g t * Y t)
          + (1 - Φ) * ω * Isum μ β (fun t => q t * Y t))) := by
    have := ((spi2.add (sY2.mul_left (lamYY κ θ Φ ω σ))).sub
      (((sY.mul_left Φ).add (sgY.mul_left σ)).add (sqY.mul_left ((1 - Φ) * ω))
        |>.mul_left (2 * (κ / θ / ((1 - Φ) * (ω + σ))))))
    convert this using 1
    funext t
    rw [hLt t]
    ring
  have eU : Isum μ β U = _ := hU.tsum_eq
  have eL : Isum μ β (loss614 κ θ Φ ω σ infl Y g q) = _ := hL.tsum_eq
  rw [eU, eL]
  have hab : 1 - α * β ≠ 0 := by nlinarith
  have h1a : 1 - α ≠ 0 := by linarith
  have hD' : ∑' t, β ^ t * ∫ w, D (t + 1) w ∂μ = (α * ∫ w, D 0 w ∂μ + α / (1 - α) *
      Isum μ β (fun t => pib t ^ 2)) / (1 - α * β) := by
    rw [eq_div_iff hab, mul_comm]; exact hdisp
  rw [hD']
  rw [hOm, hκ]
  unfold OmegaW lamYY calvoKappa
  have h1Φ : 1 - Φ ≠ 0 := by linarith
  have hωσ : ω + σ ≠ 0 := by linarith
  have h1ωθ : 1 + ω * θ ≠ 0 := by nlinarith
  field_simp
  ring

/-! ## Proposition 6.15 with expectations as integrals -/

/-- Woodford (2003), **Proposition 6.15**, eqs. (5.5)–(5.8), pp. 458–459, with GENUINE
conditional expectations: from (5.1) (`h51`), the Calvo dispersion law (`hV`, `hD`) and the
exact Calvo model with the recursions for `F` and `K` holding almost surely (`hM`, through the
derived (5.4), `eq54M`), for bounded measurable processes and any `Φ_y ∈ [0, 1)`,
`∑βᵗEU_t = W_0 − Ω̃∑βᵗEL̃_t + t.i.p. + R` with `W_0 = 2Ω(γ̄/κ)E[π_0 + Q_0]`, `R` of weight
three. -/
theorem prop615M [IsProbabilityMeasure μ] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ t, m t ≤ ‹MeasurableSpace Ω›) {α β θ ω σ sC Φ Ybar uc : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ)
    (hs : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) (hMd : Mden ω σ sC Φ ≠ 0)
    {U V D pib tipU R infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ}
    (hM : CalvoASM μ m α β θ ω σ sC infl xr F K f k Y G cb q muw tau)
    (bi : BM μ infl) (bx : BM μ xr) (bF : BM μ F) (bK : BM μ K) (bf : BM μ f) (bk : BM μ k)
    (bY : BM μ Y) (bG : BM μ G) (bcb : BM μ cb) (bq : BM μ q) (bm : BM μ muw) (bt : BM μ tau)
    (bD : BM μ D) (bp : BM μ pib) (bT : BM μ tipU) (bR : BM μ R)
    (h51 : ∀ t, U t = (fun w => -(Ybar * uc / 2) *
        quad51 σ ω θ Φ (G t w + sC * cb t w) (q t w) (Y t w) (V t w)) + tipU t + R t)
    (hV : ∀ t, V t = θ ^ 2 • D (t + 1))
    (hD : ∀ t, D (t + 1) = α • D t + (α / (1 - α)) • pib t ^ 2) :
    Isum μ β U =
      2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
          ∫ w, (Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) ∂μ
        - OmegaTilde Ybar uc α β θ ω σ Φ *
          Isum μ β (loss615 α β θ ω σ sC Φ infl Y G cb q muw tau)
        + (Isum μ β tipU
          - OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) * ∫ w, D 0 w ∂μ
          + OmegaTilde Ybar uc α β θ ω σ Φ * lamTilde α β θ ω σ sC Φ *
            Isum μ β (fun t w =>
              YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2)
          + 2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
            calvoKappa α β ω θ σ *
            Isum μ β (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w))
          - 2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
            Isum μ β (fun t w => tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w)
              (tau t w)))
        + (Isum μ β R - OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ *
            (Isum μ β (fun t => pib t ^ 2) - Isum μ β (fun t => infl t ^ 2))
          - 2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
            Isum μ β (remASm α β θ ω σ sC infl xr F K f k Y G cb tau)) := by
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hθ0 : 0 < θ := by linarith
  have hc : ω + σ ≠ 0 := by linarith
  have h1Φ : 1 - Φ ≠ 0 := by linarith
  have hν : 1 + ω * θ ≠ 0 := by nlinarith
  set κ := calvoKappa α β ω θ σ with hκ
  set Om := OmegaW Ybar uc κ θ Φ ω σ with hOm
  set gb := gbarC θ ω σ Φ with hgb
  set lt := lamTilde α β θ ω σ sC Φ with hlt
  set b : ℝ := θ * (1 + ω) with hb
  -- welfare side: Proposition 6.14
  have bg : BM μ (fun t w => G t w + sC * cb t w) := bG.add (bcb.cmul sC)
  have h614 := prop614M hα0 hα1 hβ0 hβ1 hθ0 hω hσ hΦ bY bi bg bq bD bp bT bR
    (g := fun t w => G t w + sC * cb t w) h51 hV hD
  rw [← hκ, ← hOm] at h614
  -- supply side: (5.4)
  have h54 := eq54M hm hα0 hα1 hβ0 hβ1 (by linarith : θ ≠ 1) hν hs.ne' hc hM bi bx bF bK bf bk
    bY bG bcb bq bm bt
  -- bounded building blocks
  have bX : ∀ i, BM μ (![Y, G, cb, q, muw, tau] i) := by
    intro i; fin_cases i <;> assumption
  have bY2 : BM μ (fun t => Y t ^ 2) := BM.congr (BM.mul bY bY) fun t w => by
    simp only [Pi.pow_apply, Pi.mul_apply]; ring
  have bpi2 : BM μ (fun t w => infl t w ^ 2) := BM.congr (BM.mul bi bi) fun t w => by
    simp only [Pi.mul_apply]; ring
  have bgY : BM μ (fun t => (fun t w => G t w + sC * cb t w) t * Y t) :=
    BM.congr (BM.mul bg bY) fun t w => rfl
  have bqY : BM μ (fun t => q t * Y t) := BM.congr (BM.mul bq bY) fun t w => rfl
  have bYn : BM μ (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) :=
    BM.congr (BM.of_continuous (fun v => YnA ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5))
      (by unfold YnA; fun_prop) _ bX) (fun t w => by simp)
  have bdY : BM μ (fun t w =>
      deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) :=
    BM.congr (BM.of_continuous (fun v => deltaA α β θ ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5) * v 0)
      (by unfold deltaA; fun_prop) _ bX) (fun t w => by simp)
  have bsY : BM μ (fun t w =>
      YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) :=
    BM.congr (BM.of_continuous
      (fun v => YstarA α β θ ω σ sC Φ (v 1) (v 2) (v 3) (v 4) (v 5) * v 0)
      (by unfold YstarA YnA; fun_prop) _ bX) (fun t w => by simp)
  have bs2 : BM μ (fun t w =>
      YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2) :=
    BM.congr (BM.of_continuous
      (fun v => YstarA α β θ ω σ sC Φ (v 1) (v 2) (v 3) (v 4) (v 5) ^ 2)
      (by unfold YstarA YnA; fun_prop) _ bX) (fun t w => by simp)
  have sY := hasSum_Isum (μ := μ) hβ bY.2
  have sY2 := hasSum_Isum (μ := μ) hβ bY2.2
  have spi2 := hasSum_Isum (μ := μ) hβ bpi2.2
  have sgY := hasSum_Isum (μ := μ) hβ bgY.2
  have sqY := hasSum_Isum (μ := μ) hβ bqY.2
  have sYn := hasSum_Isum (μ := μ) hβ bYn.2
  have sdY := hasSum_Isum (μ := μ) hβ bdY.2
  have ssY := hasSum_Isum (μ := μ) hβ bsY.2
  have ss2 := hasSum_Isum (μ := μ) hβ bs2.2
  -- the loss of Proposition 6.14 in terms of the sums
  have eL : Isum μ β (loss614 κ θ Φ ω σ infl Y (fun t w => G t w + sC * cb t w) q) =
      Isum μ β (fun t w => infl t w ^ 2) + lamYY κ θ Φ ω σ * Isum μ β (fun t => Y t ^ 2)
        - 2 * (κ / θ / ((1 - Φ) * (ω + σ))) * (Φ * Isum μ β Y
          + σ * Isum μ β (fun t => (fun t w => G t w + sC * cb t w) t * Y t)
          + (1 - Φ) * ω * Isum μ β (fun t => q t * Y t)) := by
    refine HasSum.tsum_eq ?_
    have := (spi2.add (sY2.mul_left (lamYY κ θ Φ ω σ))).sub
      ((((sY.mul_left Φ).add (sgY.mul_left σ)).add (sqY.mul_left ((1 - Φ) * ω))).mul_left
        (2 * (κ / θ / ((1 - Φ) * (ω + σ)))))
    convert this using 1
    funext t
    set c := κ / θ / ((1 - Φ) * (ω + σ)) with hcc
    have e : ∫ w, loss614 κ θ Φ ω σ infl Y (fun t w => G t w + sC * cb t w) q t w ∂μ =
        ∫ w, (1 * infl t w ^ 2 + lamYY κ θ Φ ω σ * (Y t ^ 2) w + (-(2 * c * Φ)) * Y t w +
          (-(2 * c * σ)) * ((fun t w => G t w + sC * cb t w) t * Y t) w +
          (-(2 * c * ((1 - Φ) * ω))) * (q t * Y t) w) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun w => by
        simp only [loss614, gamT, Pi.pow_apply, Pi.mul_apply, hcc]
        ring)
    rw [e, integral_lc5 (bpi2.integrable t) (bY2.integrable t) (bY.integrable t)
      (bgY.integrable t) (bqY.integrable t)]
    ring
  -- the first term of (5.4)
  have eP1 : Isum μ β (fun t w => Y t w -
      YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) =
      Isum μ β Y - Isum μ β (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w)
        (tau t w)) := by
    refine HasSum.tsum_eq ?_
    convert sY.sub sYn using 1
    funext t
    rw [integral_sub (bY.integrable t) (bYn.integrable t)]
    ring
  -- the new loss
  have eLt : Isum μ β (loss615 α β θ ω σ sC Φ infl Y G cb q muw tau) =
      Isum μ β (fun t w => infl t w ^ 2) + lt * (Isum μ β (fun t => Y t ^ 2)
        - 2 * Isum μ β (fun t w =>
          YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w)
        + Isum μ β (fun t w =>
          YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2)) := by
    refine HasSum.tsum_eq ?_
    have := spi2.add (((sY2.sub (ssY.mul_left 2)).add ss2).mul_left lt)
    convert this using 1
    funext t
    have e : ∫ w, loss615 α β θ ω σ sC Φ infl Y G cb q muw tau t w ∂μ =
        ∫ w, (1 * infl t w ^ 2 + lt * (Y t ^ 2) w + (-(lt * 2)) *
          (YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) +
          lt * YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2 +
          0 * infl t w ^ 2) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun w => by
        simp only [loss615, Pi.pow_apply, hlt]
        ring)
    rw [e, integral_lc5 (bpi2.integrable t) (bY2.integrable t) (bsY.integrable t)
      (bs2.integrable t) (bpi2.integrable t)]
    ring
  -- completing the square, summed
  have hE : (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) * Isum μ β (fun t w =>
        YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) =
      κ / θ / ((1 - Φ) * (ω + σ)) * (σ * Isum μ β (fun t =>
          (fun t w => G t w + sC * cb t w) t * Y t)
        + (1 - Φ) * ω * Isum μ β (fun t => q t * Y t))
      + gb * Isum μ β (fun t w =>
          deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) := by
    have h1 := ssY.mul_left (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC)
    have h2 := ((sgY.mul_left σ).add (sqY.mul_left ((1 - Φ) * ω))).mul_left
      (κ / θ / ((1 - Φ) * (ω + σ)))
    have h3 := sdY.mul_left gb
    refine h1.unique ?_
    convert h2.add h3 using 1
    funext t
    have e : (∫ w, YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) *
        Y t w ∂μ) * (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) =
        ∫ w, ((κ / θ / ((1 - Φ) * (ω + σ)) * σ) *
          ((fun t w => G t w + sC * cb t w) t * Y t) w +
          (κ / θ / ((1 - Φ) * (ω + σ)) * ((1 - Φ) * ω)) * (q t * Y t) w +
          gb * (deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) +
          0 * Y t w + 0 * Y t w) ∂μ := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      have hy := LargeDistortions.ystar_eq (β := β) hα0 hα1 hβ1 hθ0 hω hσ hs hΦ0 hΦ hMd (G t w)
        (cb t w) (q t w) (muw t w) (tau t w)
      simp only [Pi.mul_apply]
      rw [← hκ, ← hgb] at hy
      linear_combination (Y t w) * hy
    have e2 := integral_lc5 (μ := μ) (bgY.integrable t) (bqY.integrable t) (bdY.integrable t)
      (bY.integrable t) (bY.integrable t) (κ / θ / ((1 - Φ) * (ω + σ)) * σ)
      (κ / θ / ((1 - Φ) * (ω + σ)) * ((1 - Φ) * ω)) gb 0 0
    linear_combination (β ^ t) * (e.trans e2)
  -- the weight
  have hF := LargeDistortions.lamTilde_eq (β := β) (sC := sC) hα0 hα1 hθ0 hω hσ hs hΦ0 hΦ
  rw [← hlt, ← hgb, ← hκ] at hF
  -- assemble
  rw [h614, eL, h54, eP1, eLt]
  unfold OmegaTilde
  have e1 : Isum μ β (fun t => infl t ^ 2) = Isum μ β (fun t w => infl t w ^ 2) := rfl
  have e2 : Isum μ β (fun t w => Y t w ^ 2) = Isum μ β (fun t => Y t ^ 2) := rfl
  rw [e1, e2]
  have hgk : gb * κ = κ / θ / ((1 - Φ) * (ω + σ)) * Φ := by
    rw [hgb]; unfold gbarC; field_simp
  have hbg : 1 + Φ * (1 + ω) / ((1 - Φ) * (ω + σ)) = 1 + gb * (θ * (1 + ω)) := by
    rw [hgb]; unfold gbarC; field_simp
  rw [hbg]
  linear_combination (Om * (Isum μ β (fun t => Y t ^ 2) - 2 * Isum μ β (fun t w =>
      YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w))) * hF
    + (-2 * Om) * hE + (-2 * Om * Isum μ β Y) * hgk

/-! ## Proposition 6.15 in Layer B on a probability space -/

open BridgeExtensions (UProc)

/-- Woodford (2003), eq. (2.6), p. 393: the log output index is continuous (weights summing to
one). -/
theorem continuous_logYidx {ι : Type} [Fintype ι] {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (θ : ℝ) : Continuous (BridgeExtensions.logYidx w θ) := by
  have hpos : ∀ y : ι → ℝ, 0 < ∑ i, w i * Real.exp (y i) ^ (1 - θ⁻¹) := fun y => by
    obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
      by_contra h
      push Not at h
      have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    refine lt_of_lt_of_le (mul_pos hi (Real.rpow_pos_of_pos (Real.exp_pos _) _))
      (Finset.single_le_sum (f := fun i => w i * Real.exp (y i) ^ (1 - θ⁻¹))
        (fun j _ => mul_nonneg (hw0 j) (Real.rpow_nonneg (Real.exp_pos _).le _))
        (Finset.mem_univ i))
  unfold BridgeExtensions.logYidx ExpLogCES.cesIndex
  have hs : Continuous fun y : ι → ℝ => ∑ i, w i * Real.exp (y i) ^ (1 - θ⁻¹) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul
      ((Real.continuous_exp.comp (continuous_apply i)).rpow_const fun y =>
        Or.inl (Real.exp_pos _).ne')
  exact (hs.rpow_const fun y => Or.inl (hpos y).ne').log fun y =>
    (Real.rpow_pos_of_pos (hpos y) _).ne'

/-- Woodford (2003), (E.2): the policy-independent terms `tip51` are continuous in the shocks. -/
theorem continuous_tip51 {Ξ : Type} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (u v : ℝ × Ξ → ℝ) (Ybar : ℝ) :
    Continuous fun x : Ξ × Ξ => BridgeExtensions.tip51 u v Ybar x.1 x.2 := by
  have hc : Continuous fun ξ : Ξ => ((0 : ℝ), ξ) := continuous_const.prodMk continuous_id
  unfold BridgeExtensions.tip51 BridgeExtensions.dXi BridgeExtensions.dXiXi
  exact ((continuous_const.add (((fderiv ℝ u (Ybar, 0)).continuous.comp hc).comp
    continuous_fst)).add (((((fderiv ℝ (fderiv ℝ u) (Ybar, 0)).continuous.comp
      hc).clm_apply hc).comp continuous_fst).div_const 2)).sub
    ((continuous_const.add (((fderiv ℝ v (Ybar, 0)).continuous.comp hc).comp continuous_snd)).add
      (((((fderiv ℝ (fderiv ℝ v) (Ybar, 0)).continuous.comp hc).clm_apply hc).comp
        continuous_snd).div_const 2))

/-- Woodford (2003), (5.4): a uniformly small family stays uniformly small one date later. -/
theorem uproc_next {A Ω' : Type} {l : Filter A} {X : A → ℕ → Ω' → ℝ} {g : A → ℝ}
    (h : UProc l X g) : UProc l (fun a t z => X a (t + 1) z) g := by
  have ht : Tendsto (fun p : A × (ℕ × Ω') => (p.1, (p.2.1 + 1, p.2.2)))
      (l ×ˢ (⊤ : Filter (ℕ × Ω'))) (l ×ˢ (⊤ : Filter (ℕ × Ω'))) :=
    tendsto_fst.prodMk tendsto_top
  exact h.comp_tendsto ht

/-- Woodford (2003), eq. (5.4), p. 458, on a probability space: the remainder `remASm` of the
derived (5.4) is `O(ε³)` UNIFORMLY in the date and the state for any family in which
`π, x, F̂, K̂, f̂, k̂, Ŷ, Ĝ, ĉ, τ̂` are uniformly `O(ε)`. -/
theorem remASm_o {A Ω' : Type} {l : Filter A} {e : A → ℝ} (he : Tendsto e l (𝓝 0))
    (α β θ ω σ sC : ℝ) {infl xr F K f k Y G cb tau : A → ℕ → Ω' → ℝ}
    (hi : UProc l infl fun a => e a ^ 1) (hx : UProc l xr fun a => e a ^ 1)
    (hF : UProc l F fun a => e a ^ 1) (hK : UProc l K fun a => e a ^ 1)
    (hf : UProc l f fun a => e a ^ 1) (hk : UProc l k fun a => e a ^ 1)
    (hY : UProc l Y fun a => e a ^ 1) (hG : UProc l G fun a => e a ^ 1)
    (hcb : UProc l cb fun a => e a ^ 1) (htau : UProc l tau fun a => e a ^ 1) :
    UProc l (fun a => remASm α β θ ω σ sC (infl a) (xr a) (F a) (K a) (f a) (k a) (Y a) (G a)
      (cb a) (tau a)) fun a => e a ^ 3 := by
  have hs := BridgeExtensions.tendsto_amp (J := ℕ × Ω') he
  have hS : UProc l (fun a t z => (K a t z + F a t z) / 2) fun a => e a ^ 1 :=
    ((show (fun p : A × (ℕ × Ω') => K p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 from
      hK).add hF).const_mul_left (1 / 2) |>.congr_left fun p => by ring
  have ex : ∀ X : A → ℕ → Ω' → ℝ, UProc l X (fun a => e a ^ 1) →
      UProc l (fun a t z => expRem (X a t z)) fun a => e a ^ 3 := fun X hX =>
    BridgeExtensions.expRem_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω') => e p.1) hs hX
  have lin : ∀ (c : ℝ) (X Z : A → ℕ → Ω' → ℝ), UProc l X (fun a => e a ^ 1) →
      UProc l Z (fun a => e a ^ 1) → UProc l (fun a t z => c * X a t z + Z a t z)
        fun a => e a ^ 1 := fun c X Z hX hZ =>
    ((show (fun p : A × (ℕ × Ω') => X p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1
      from hX).const_mul_left c).add hZ
  have hneg : UProc l (fun a t z => -((θ - 1) * xr a t z)) fun a => e a ^ 1 :=
    ((show (fun p : A × (ℕ × Ω') => xr p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1
      from hx).const_mul_left (θ - 1)).neg_left
  have hpth : UProc l (fun a t z => (θ - 1) * infl a t z) fun a => e a ^ 1 :=
    (show (fun p : A × (ℕ × Ω') => infl p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1
      from hi).const_mul_left (θ - 1)
  have hnow := BridgeExtensions.nowA_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω') => e p.1) hs
    α β θ ω hi hx hS (ex _ hpth) (ex _ hneg) (ex _ hK) (ex _ hF) (ex _ hk) (ex _ hf)
  have hrest : UProc l (fun a => LargeDistortions.restP α θ ω (infl a) (xr a) (F a) (K a))
      fun a => e a ^ 3 :=
    BridgeExtensions.restA_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω') => e p.1) hs α θ ω hi hx
      hS (ex _ hpth) (ex _ hneg) (ex _ (lin (θ * (1 + ω)) infl K hi hK))
      (ex _ (lin (θ - 1) infl F hi hF))
  have hrest' := uproc_next hrest
  have hrho := BridgeExtensions.rho2A_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω') => e p.1) hs
    α β θ ω σ sC hY hG hcb htau (ex _ hY) (BridgeExtensions.rlog_o hs
      (BridgeExtensions.zA_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω') => e p.1) hs sC
        (Y := fun p => Y p.1 p.2.1 p.2.2) (G := fun p => G p.1 p.2.1 p.2.2) hY hG))
  refine ((hnow.add ((show (fun p : A × (ℕ × Ω') =>
      LargeDistortions.restP α θ ω (infl p.1) (xr p.1) (F p.1) (K p.1) (p.2.1 + 1) p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 from hrest').const_mul_left β)).add hrho).congr_left
        fun p => ?_
  simp only [remASm, nowP]

/-- Woodford (2003), (5.2): expected discounted sums are linear. -/
theorem Isum_sub [IsProbabilityMeasure μ] {β : ℝ} (hβ : |β| < 1) {X Z : ℕ → Ω → ℝ}
    (hX : BM μ X) (hZ : BM μ Z) :
    Isum μ β X - Isum μ β Z = Isum μ β (fun t w => X t w - Z t w) := by
  have h := (hasSum_Isum (μ := μ) hβ hX.2).sub (hasSum_Isum (μ := μ) hβ hZ.2)
  refine (h.congr_fun fun t => ?_).tsum_eq.symm
  rw [integral_sub (hX.integrable t) (hZ.integrable t)]
  ring

/-- Woodford (2003), (5.5), p. 458, on a probability space: the policy-independent terms of
Proposition 6.15 (functions of the disturbances and the initial dispersion only). -/
noncomputable def tip615M (μ : Measure Ω) (α β θ ω σ sC Φ Ybar uc : ℝ)
    (tipU D G cb q muw tau : ℕ → Ω → ℝ) : ℝ :=
  Isum μ β tipU -
    OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) * ∫ w, D 0 w ∂μ +
    OmegaTilde Ybar uc α β θ ω σ Φ * lamTilde α β θ ω σ sC Φ *
      Isum μ β (fun t w => YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2) +
    2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ * calvoKappa α β ω θ σ *
      Isum μ β (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) -
    2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
      Isum μ β (fun t w => tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w))

/-- Woodford (2003), (5.5), p. 458, on a probability space: the transitory term
`W_0 = 2Ω(γ̄/κ)E[π_0 + Q_0]`. -/
noncomputable def W0615M (μ : Measure Ω) (α β θ ω σ Φ Ybar uc : ℝ) (infl F K : ℕ → Ω → ℝ) :
    ℝ :=
  2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
    ∫ w, (Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) ∂μ

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), LAYER B ON A PROBABILITY SPACE with
GENUINE conditional expectations (`E_t = μ[· | m_t]` in the recursions for `F` and `K`, the
expectations of the welfare criterion as integrals): from the ACTUAL period utility, for a family
of economies satisfying, for small amplitudes, the exact Calvo conditions almost surely
(`hM`), the dispersion as the variance of log prices (`hV`) and the Calvo law (`hD`), with every
first-order variable uniformly `O(ε)`, `π̄ − π, D = O(ε²)` uniformly and measurable processes,
`∑βᵗEU_t = W_0 − Ω̃ ∑βᵗEL̃_t + t.i.p. + O(ε³)`. -/
theorem prop615_layerBM [IsProbabilityMeasure μ] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ t, m t ≤ ‹MeasurableSpace Ω›) {A : Type} {l : Filter A} {e : A → ℝ}
    {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ)
    (hΦ : Φ < 1) (hMd : Mden ω σ sC Φ ≠ 0)
    (he : Tendsto e l (𝓝 0)) {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ}
    {infl xr F K f k G cb q muw tau D pib : A → ℕ → Ω → ℝ}
    (hM : ∀ᶠ a in l, CalvoASM μ m α β θ ω σ sC (infl a) (xr a) (F a) (K a) (f a) (k a)
      (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a))
    (myh : ∀ a t, AEStronglyMeasurable (yh a t) μ) (mxu : ∀ a t, AEStronglyMeasurable (xu a t) μ)
    (mxv : ∀ a t, AEStronglyMeasurable (xv a t) μ)
    (mi : ∀ a t, AEStronglyMeasurable (infl a t) μ) (mx : ∀ a t, AEStronglyMeasurable (xr a t) μ)
    (mF : ∀ a t, AEStronglyMeasurable (F a t) μ) (mK : ∀ a t, AEStronglyMeasurable (K a t) μ)
    (mf : ∀ a t, AEStronglyMeasurable (f a t) μ) (mk : ∀ a t, AEStronglyMeasurable (k a t) μ)
    (mG : ∀ a t, AEStronglyMeasurable (G a t) μ) (mcb : ∀ a t, AEStronglyMeasurable (cb a t) μ)
    (mq : ∀ a t, AEStronglyMeasurable (q a t) μ) (mm : ∀ a t, AEStronglyMeasurable (muw a t) μ)
    (mt : ∀ a t, AEStronglyMeasurable (tau a t) μ) (mD : ∀ a t, AEStronglyMeasurable (D a t) μ)
    (mp : ∀ a t, AEStronglyMeasurable (pib a t) μ)
    (hyh : UProc l yh fun a => e a ^ 1) (hxu : UProc l xu fun a => e a ^ 1)
    (hxv : UProc l xv fun a => e a ^ 1) (hiO : UProc l infl fun a => e a ^ 1)
    (hxrO : UProc l xr fun a => e a ^ 1) (hFO : UProc l F fun a => e a ^ 1)
    (hKO : UProc l K fun a => e a ^ 1) (hfO : UProc l f fun a => e a ^ 1)
    (hkO : UProc l k fun a => e a ^ 1) (hGO : UProc l G fun a => e a ^ 1)
    (hcbO : UProc l cb fun a => e a ^ 1) (hqO : UProc l q fun a => e a ^ 1)
    (hmO : UProc l muw fun a => e a ^ 1) (htO : UProc l tau fun a => e a ^ 1)
    (hpO : UProc l (fun a t z => pib a t z - infl a t z) fun a => e a ^ 2)
    (hDO : UProc l D fun a => e a ^ 2)
    (hg : ∀ a t z, BridgeExtensions.dYXi u (Ybar, 0) (xu a t z) =
      σ * BridgeExtensions.dY u (Ybar, 0) * (G a t z + sC * cb a t z))
    (hq : ∀ a t z, BridgeExtensions.dYXi v (Ybar, 0) (xv a t z) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q a t z))
    (hV : ∀ᶠ a in l, ∀ t, (fun z => ExpLogCES.crossVar wt (yh a t z)) = θ ^ 2 • D a (t + 1))
    (hD : ∀ᶠ a in l, ∀ t, D a (t + 1) = α • D a t + (α / (1 - α)) • pib a t ^ 2) :
    (fun a => Isum μ β
        (fun t z => BridgeExtensions.periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) -
      (W0615M μ α β θ ω σ Φ Ybar (BridgeExtensions.dY u (Ybar, 0)) (infl a) (F a) (K a) -
        OmegaTilde Ybar (BridgeExtensions.dY u (Ybar, 0)) α β θ ω σ Φ *
          Isum μ β (loss615 α β θ ω σ sC Φ (infl a)
            (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a)
            (tau a)) +
        tip615M μ α β θ ω σ sC Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z)) (D a) (G a) (cb a)
          (q a) (muw a) (tau a)))
      =O[l] fun a => e a ^ 3 := by
  have hs := BridgeExtensions.tendsto_amp (J := ℕ × Ω) he
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hθ0 : 0 < θ := by linarith
  set Om := OmegaW Ybar (BridgeExtensions.dY u (Ybar, 0)) (calvoKappa α β ω θ σ) θ Φ ω σ
    with hOm
  set gb := gbarC θ ω σ Φ with hgb
  set R : A → ℕ → Ω → ℝ := fun a t z =>
    BridgeExtensions.periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z) -
      (-(Ybar * BridgeExtensions.dY u (Ybar, 0) / 2) * quad51 σ ω θ Φ
        (G a t z + sC * cb a t z) (q a t z)
        (BridgeExtensions.logYidx wt θ (yh a t z)) (ExpLogCES.crossVar wt (yh a t z)) +
          BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z)) with hR
  have hG' : (fun p : A × (ℕ × Ω) => G p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hGO
  have hcb' : (fun p : A × (ℕ × Ω) => cb p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    hcbO
  have hgO : UProc l (fun a t z => G a t z + sC * cb a t z) fun a => e a ^ 1 :=
    hG'.add (hcb'.const_mul_left sC)
  have hRO : UProc l R fun a => e a ^ 3 :=
    BridgeExtensions.eq51_actual (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs hw0 hw1
      hθ.ne' hu hv hucc hvy hvyy (yh := fun p => yh p.1 p.2.1 p.2.2)
      (xu := fun p => xu p.1 p.2.1 p.2.2) (xv := fun p => xv p.1 p.2.1 p.2.2)
      (g := fun p => G p.1 p.2.1 p.2.2 + sC * cb p.1 p.2.1 p.2.2)
      (q := fun p => q p.1 p.2.1 p.2.2) hyh hxu hxv hgO hqO (fun p => hg _ _ _)
      (fun p => hq _ _ _)
  have hpO' : (fun p : A × (ℕ × Ω) => pib p.1 p.2.1 p.2.2 - infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 := hpO
  have hiO' : (fun p : A × (ℕ × Ω) => infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hiO
  have hPO : UProc l (fun a t z => pib a t z ^ 2 - infl a t z ^ 2) fun a => e a ^ 3 := by
    have h1 := (BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2) hpO').add
      (hiO'.const_mul_left 2)
    refine (BridgeExtensions.o_mul hpO' h1 (by norm_num : 2 + 1 = 3)).congr_left fun p => ?_
    ring
  have hYO := BridgeExtensions.logYidx_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs
    hw0 hw1 hθ.ne' (yh := fun p => yh p.1 p.2.1 p.2.2) hyh
  have hAS := remASm_o he α β θ ω σ sC (Y := fun a t z => BridgeExtensions.logYidx wt θ
    (yh a t z)) hiO hxrO hFO hKO hfO hkO hYO hGO hcbO htO
  -- measurability of the composite processes
  have mY : ∀ a t, AEStronglyMeasurable
      (fun z => BridgeExtensions.logYidx wt θ (yh a t z)) μ := fun a t =>
    (continuous_logYidx hw0 hw1 θ).comp_aestronglyMeasurable (myh a t)
  have mT : ∀ a t, AEStronglyMeasurable
      (fun z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z)) μ := fun a t =>
    (continuous_tip51 u v Ybar).comp_aestronglyMeasurable ((mxu a t).prodMk (mxv a t))
  have mR : ∀ a t, AEStronglyMeasurable (R a t) μ := by
    intro a t
    have hU : Continuous fun x : (ι → ℝ) × Ξ × Ξ =>
        BridgeExtensions.periodU u v wt θ Ybar x.1 x.2.1 x.2.2 := by
      unfold BridgeExtensions.periodU
      have hL := continuous_logYidx hw0 hw1 θ
      exact (hu.continuous.comp ((continuous_const.mul (Real.continuous_exp.comp
        (hL.comp continuous_fst))).prodMk (continuous_fst.comp continuous_snd))).sub
        (continuous_finsetSum _ fun i _ => continuous_const.mul (hv.continuous.comp
          ((continuous_const.mul (Real.continuous_exp.comp ((continuous_apply i).comp
            continuous_fst))).prodMk (continuous_snd.comp continuous_snd))))
    have hCV : Continuous fun y : ι → ℝ => ExpLogCES.crossVar wt y := by
      unfold ExpLogCES.crossVar ExpLogCES.crossMean; fun_prop
    have m1 := hU.comp_aestronglyMeasurable ((myh a t).prodMk ((mxu a t).prodMk (mxv a t)))
    have m2 : AEStronglyMeasurable (fun z => -(Ybar * BridgeExtensions.dY u (Ybar, 0) / 2) *
        quad51 σ ω θ Φ (G a t z + sC * cb a t z) (q a t z)
          (BridgeExtensions.logYidx wt θ (yh a t z)) (ExpLogCES.crossVar wt (yh a t z))) μ := by
      unfold quad51
      exact aestronglyMeasurable_const.mul (((aestronglyMeasurable_const.mul ((mY a t).pow 2)).sub
        ((aestronglyMeasurable_const.mul ((aestronglyMeasurable_const.add
          (aestronglyMeasurable_const.mul ((mG a t).add (aestronglyMeasurable_const.mul
            (mcb a t))))).add (aestronglyMeasurable_const.mul (mq a t)))).mul (mY a t))).add
        (aestronglyMeasurable_const.mul (hCV.comp_aestronglyMeasurable (myh a t))))
    exact m1.sub (m2.add (mT a t))
  -- bounded measurable processes for amplitudes near `0`
  have bY := BridgeExtensions.bdd_of_o0 (X := fun a t z => BridgeExtensions.logYidx wt θ
    (yh a t z)) he hYO
  have bi := BridgeExtensions.bdd_of_o0 he hiO
  have bx := BridgeExtensions.bdd_of_o0 he hxrO
  have bF := BridgeExtensions.bdd_of_o0 he hFO
  have bK := BridgeExtensions.bdd_of_o0 he hKO
  have bf := BridgeExtensions.bdd_of_o0 he hfO
  have bk := BridgeExtensions.bdd_of_o0 he hkO
  have bG := BridgeExtensions.bdd_of_o0 he hGO
  have bcb := BridgeExtensions.bdd_of_o0 he hcbO
  have bq := BridgeExtensions.bdd_of_o0 he hqO
  have bm := BridgeExtensions.bdd_of_o0 he hmO
  have bt := BridgeExtensions.bdd_of_o0 he htO
  have bD := BridgeExtensions.bdd_of_o0 he hDO
  have bp := BridgeExtensions.bdd_of_o0 (X := pib) he
    (((BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2) hpO').add hiO').congr_left
      fun p => by ring)
  have bT := BridgeExtensions.bdd_of_o (X := fun a t z => BridgeExtensions.tip51 u v Ybar
    (xu a t z) (xv a t z)) he (BridgeExtensions.tip51 u v Ybar 0 0)
    (BridgeExtensions.tip51_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs u v Ybar
      (xu := fun p => xu p.1 p.2.1 p.2.2) (xv := fun p => xv p.1 p.2.1 p.2.2) hxu hxv)
  have bR := BridgeExtensions.bdd_of_o0 he hRO
  have hev : ∀ᶠ a in l, Isum μ β
        (fun t z => BridgeExtensions.periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) -
      (W0615M μ α β θ ω σ Φ Ybar (BridgeExtensions.dY u (Ybar, 0)) (infl a) (F a) (K a) -
        OmegaTilde Ybar (BridgeExtensions.dY u (Ybar, 0)) α β θ ω σ Φ *
          Isum μ β (loss615 α β θ ω σ sC Φ (infl a)
            (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a)
            (tau a)) +
        tip615M μ α β θ ω σ sC Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z)) (D a) (G a) (cb a)
          (q a) (muw a) (tau a)) =
      Isum μ β (R a) - Om * Isum μ β (fun t z => pib a t z ^ 2 - infl a t z ^ 2) -
        2 * Om * gb * Isum μ β (remASm α β θ ω σ sC (infl a) (xr a) (F a) (K a) (f a) (k a)
          (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (tau a)) := by
    filter_upwards [hM, hV, hD, bY, bi, bx, bF, bK, bf, bk, bG, bcb, bq, bm, bt, bD, bp, bT, bR]
      with a hMa hVa hDa hYb hib hxb hFb hKb hfb hkb hGb hcbb hqb hmb htb hDb hpb hTb hRb
    have h51 : ∀ t, (fun z => BridgeExtensions.periodU u v wt θ Ybar (yh a t z) (xu a t z)
        (xv a t z)) =
        (fun z => -(Ybar * BridgeExtensions.dY u (Ybar, 0) / 2) * quad51 σ ω θ Φ
          (G a t z + sC * cb a t z) (q a t z) (BridgeExtensions.logYidx wt θ (yh a t z))
          (ExpLogCES.crossVar wt (yh a t z))) +
          (fun z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z)) + R a t := by
      intro t
      funext z
      simp only [Pi.add_apply, hR]
      ring
    have h := prop615M hm hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd hMa
      ⟨mi a, hib⟩ ⟨mx a, hxb⟩ ⟨mF a, hFb⟩ ⟨mK a, hKb⟩ ⟨mf a, hfb⟩ ⟨mk a, hkb⟩ ⟨mY a, hYb⟩
      ⟨mG a, hGb⟩ ⟨mcb a, hcbb⟩ ⟨mq a, hqb⟩ ⟨mm a, hmb⟩ ⟨mt a, htb⟩ ⟨mD a, hDb⟩ ⟨mp a, hpb⟩
      ⟨mT a, hTb⟩ ⟨mR a, hRb⟩ h51 hVa hDa
    rw [h, Isum_sub hβ (BM.congr (BM.mul ⟨mp a, hpb⟩ ⟨mp a, hpb⟩) fun t w => by
        simp only [Pi.pow_apply, Pi.mul_apply]; ring)
      (BM.congr (BM.mul ⟨mi a, hib⟩ ⟨mi a, hib⟩) fun t w => by
        simp only [Pi.pow_apply, Pi.mul_apply]; ring)]
    unfold W0615M tip615M
    simp only [Pi.pow_apply]
    ring
  exact (((SmoothInSigmaMeasureWelfare.mdsum_o μ hβ0.le hβ1 hRO).sub
    ((SmoothInSigmaMeasureWelfare.mdsum_o μ hβ0.le hβ1 hPO).const_mul_left Om)).sub
    ((SmoothInSigmaMeasureWelfare.mdsum_o μ hβ0.le hβ1 hAS).const_mul_left (2 * Om * gb))).congr'
      (hev.mono fun a ha => ha.symm) (Eventually.of_forall fun _ => rfl)

/-! ## Proposition 6.15 along the perturbation equilibrium -/

open SmoothInSigmaMeasure (adSub)
open SmoothInSigma (pbar)
open SmoothInSigmaMeasureWelfare (ypath readout_first readout_second)
open SmoothInSigmaMeasureProps (discF dispersion_first_order_zero disc_second_order uproc_shift)

/-- Woodford (2003), §2, p. 394: a readout `R` along the equilibrium path of amplitude `ε`,
`R(y_t(ε, ω))`. -/
abbrev along {Y E : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) (R : Y → E) :
    ℝ → ℕ → (ℕ → ℝ) → E :=
  fun ε t z => R (ypath ψ ybar ε t z)

/-- Woodford (2003), (5.3), p. 457: the dispersion `Δ_{t−1}` along the equilibrium path, from
the readout `D` of the dispersion of the date (zero initial dispersion `Δ_{−1} = 0`). -/
abbrev dispAlong {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) (DR : Y → ℝ) :
    ℝ → ℕ → (ℕ → ℝ) → ℝ :=
  fun ε t z => match t with
    | 0 => 0
    | k + 1 => DR (ypath ψ ybar ε k z)

/-- Woodford (2003), App. E.2: a continuous readout along the equilibrium path is measurable
under the i.i.d. law (the path is adapted to the shock filtration). -/
theorem aesm_along {Y E : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace E]
    (ν0 : ProbabilityMeasure ℝ) (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) {R : Y → E}
    (hR : Continuous R) (ε : ℝ) (t : ℕ) :
    AEStronglyMeasurable (along ψ ybar R ε t) (ExpectationsMeasureIID.iidSystem ν0).μ :=
  (hR.comp_stronglyMeasurable ((SmoothInSigmaMeasurePath.yproc_adapted ν0 (ψ (ybar, 0, ε)).2
    t).mono ((ExpectationsMeasureIID.iidSystem ν0).𝓕.le t))).aestronglyMeasurable

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), p. 458, ALONG THE EQUILIBRIUM on the
i.i.d. probability space `(ℕ → ℝ, ν^ℕ)`, with GENUINE conditional expectations: let the decision
vector carry, through `C²` readouts vanishing at `ȳ`, log outputs `ŷ(i)`, relative prices, the
shocks `ξ_u, ξ_v`, inflation `π`, mean-price inflation `π̄`, the reset price, `F, K, f̂, k̂`, the
disturbances `G, c̄, q, μʷ, τ` and the dispersion `D` (as of the date). The model's equations are
the composites (`hg`, `hq`), the dispersion as the variance of log prices (`hV`), the Calvo law
of dispersion (`hlaw`), the mean-price/index discrepancy (`hdisc`) and the exact Calvo conditions
with `E_t = E[· | 𝓕_t]` (`hM`), along the equilibrium for small amplitudes. Then
`E∑βᵗU_t = W_0 − Ω̃ E∑βᵗL̃_t + t.i.p. + O(ε³)`: dispersion is `O(ε²)` because its first
derivative vanishes through the Calvo law, `π̄ − π = O(ε²)`, and `prop615_layerBM` applies. -/
theorem prop615_measure {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type} [Fintype ι]
    [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ)
    (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) (hMd : Mden ω σ sC Φ ≠ 0) {wt : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR rpR : Y → ι → ℝ} {xuR xvR : Y → Ξ}
    {inflR pibR xrR FR KR fR kR GR cbR qR muwR tauR DR : Y → ℝ}
    (cyh : ContDiff ℝ 2 yhR) (crp : ContDiff ℝ 2 rpR) (cxu : ContDiff ℝ 2 xuR)
    (cxv : ContDiff ℝ 2 xvR) (ci : ContDiff ℝ 2 inflR) (cp : ContDiff ℝ 2 pibR)
    (cxr : ContDiff ℝ 2 xrR) (cF : ContDiff ℝ 2 FR) (cK : ContDiff ℝ 2 KR)
    (cf : ContDiff ℝ 2 fR) (ck : ContDiff ℝ 2 kR) (cG : ContDiff ℝ 2 GR)
    (ccb : ContDiff ℝ 2 cbR) (cq : ContDiff ℝ 2 qR) (cmu : ContDiff ℝ 2 muwR)
    (ctau : ContDiff ℝ 2 tauR) (cD : ContDiff ℝ 2 DR)
    (zyh : yhR ybar = 0) (zrp : rpR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (zi : inflR ybar = 0) (zp : pibR ybar = 0) (zxr : xrR ybar = 0) (zF : FR ybar = 0)
    (zK : KR ybar = 0) (zf : fR ybar = 0) (zk : kR ybar = 0) (zG : GR ybar = 0)
    (zcb : cbR ybar = 0) (zq : qR ybar = 0) (zmu : muwR ybar = 0) (ztau : tauR ybar = 0)
    (zD : DR ybar = 0)
    (hg : ∀ y, BridgeExtensions.dYXi u (Ybar, 0) (xuR y) =
      σ * BridgeExtensions.dY u (Ybar, 0) * (GR y + sC * cbR y))
    (hq : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xvR y) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * qR y))
    (hV : ∀ y, ExpLogCES.crossVar wt (yhR y) = θ ^ 2 * DR y)
    (hlaw : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t z,
      DR (ypath ψ ybar ε t z) = α * DR (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k z) + α / (1 - α) * pibR (ypath ψ ybar ε t z) ^ 2)
    (hdisc : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t z,
      pibR (ypath ψ ybar ε t z) - inflR (ypath ψ ybar ε t z) =
        discF wt θ (fun i => rpR (ypath ψ ybar ε t z) i + inflR (ypath ψ ybar ε t z))
          (rpR (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k z)))
    (hM : ∀ᶠ ε in 𝓝 (0 : ℝ), CalvoASM (ExpectationsMeasureIID.iidSystem ν0).μ
      (fun t => (ExpectationsMeasureIID.iidSystem ν0).𝓕 t) α β θ ω σ sC
      (along ψ ybar inflR ε) (along ψ ybar xrR ε) (along ψ ybar FR ε) (along ψ ybar KR ε)
      (along ψ ybar fR ε) (along ψ ybar kR ε)
      (fun t z => BridgeExtensions.logYidx wt θ (along ψ ybar yhR ε t z))
      (along ψ ybar GR ε) (along ψ ybar cbR ε) (along ψ ybar qR ε) (along ψ ybar muwR ε)
      (along ψ ybar tauR ε)) :
    (fun ε => Isum (ExpectationsMeasureIID.iidSystem ν0).μ β
        (fun t z => BridgeExtensions.periodU u v wt θ Ybar (along ψ ybar yhR ε t z)
          (along ψ ybar xuR ε t z) (along ψ ybar xvR ε t z)) -
      (W0615M (ExpectationsMeasureIID.iidSystem ν0).μ α β θ ω σ Φ Ybar
          (BridgeExtensions.dY u (Ybar, 0)) (along ψ ybar inflR ε) (along ψ ybar FR ε)
          (along ψ ybar KR ε) -
        OmegaTilde Ybar (BridgeExtensions.dY u (Ybar, 0)) α β θ ω σ Φ *
          Isum (ExpectationsMeasureIID.iidSystem ν0).μ β (loss615 α β θ ω σ sC Φ
            (along ψ ybar inflR ε)
            (fun t z => BridgeExtensions.logYidx wt θ (along ψ ybar yhR ε t z))
            (along ψ ybar GR ε) (along ψ ybar cbR ε) (along ψ ybar qR ε)
            (along ψ ybar muwR ε) (along ψ ybar tauR ε)) +
        tip615M (ExpectationsMeasureIID.iidSystem ν0).μ α β θ ω σ sC Φ Ybar
          (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => BridgeExtensions.tip51 u v Ybar (along ψ ybar xuR ε t z)
            (along ψ ybar xvR ε t z)) (dispAlong ψ ybar DR ε) (along ψ ybar GR ε)
          (along ψ ybar cbR ε) (along ψ ybar qR ε) (along ψ ybar muwR ε)
          (along ψ ybar tauR ε)))
      =O[𝓝 0] fun ε => ε ^ 3 := by
  have hψ1 : DifferentiableAt ℝ ψ (pbar ybar) := hψ2.differentiableAt (by norm_num)
  -- the first derivative of the dispersion vanishes, so dispersion is of second order
  have hD1 := dispersion_first_order_zero hbase hψ1 (cD.contDiffAt.differentiableAt
    (by norm_num)) (cp.contDiffAt.differentiableAt (by norm_num)) zp hlaw
  have hDO : UProc (𝓝 0) (fun ε t z => DR (ypath ψ ybar ε t z)) fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cD.contDiffAt zD).congr_left fun b => ?_
    simp only [hD1, smul_zero, sub_zero]
  have hpO := disc_second_order hw0 hw1 (by linarith : θ ≠ 1) hbase hψ2 crp.contDiffAt
    ci.contDiffAt zrp zi hdisc
  have m1 : ∀ {E : Type} [TopologicalSpace E] {R : Y → E}, Continuous R → ∀ ε t,
      AEStronglyMeasurable (along ψ ybar R ε t) (ExpectationsMeasureIID.iidSystem ν0).μ :=
    fun {E} _ {R} hR ε t => aesm_along ν0 ψ ybar hR ε t
  have mD : ∀ ε t, AEStronglyMeasurable (dispAlong ψ ybar DR ε t)
      (ExpectationsMeasureIID.iidSystem ν0).μ := fun ε t => by
    cases t with
    | zero => exact aestronglyMeasurable_const
    | succ k => exact m1 cD.continuous ε k
  have hVm : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t, (fun z => ExpLogCES.crossVar wt (along ψ ybar yhR ε t z)) =
      θ ^ 2 • dispAlong ψ ybar DR ε (t + 1) :=
    Eventually.of_forall fun ε t => funext fun z => hV _
  have hDm : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t, dispAlong ψ ybar DR ε (t + 1) =
      α • dispAlong ψ ybar DR ε t + (α / (1 - α)) • along ψ ybar pibR ε t ^ 2 := by
    filter_upwards [hlaw] with ε hε t
    funext z
    have hl := hε t z
    cases t with
    | zero =>
      simp only [dispAlong, along, Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
      rw [hl, zD]
    | succ k =>
      simp only [dispAlong, along, Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
      exact hl
  exact prop615_layerBM (μ := (ExpectationsMeasureIID.iidSystem ν0).μ)
    (m := fun t => (ExpectationsMeasureIID.iidSystem ν0).𝓕 t)
    (fun t => (ExpectationsMeasureIID.iidSystem ν0).𝓕.le t) (l := 𝓝 (0 : ℝ))
    (e := fun ε => ε) hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd tendsto_id hw0 hw1 hu hv hucc
    hvy hvyy hM (m1 cyh.continuous) (m1 cxu.continuous) (m1 cxv.continuous)
    (m1 ci.continuous) (m1 cxr.continuous) (m1 cF.continuous) (m1 cK.continuous)
    (m1 cf.continuous) (m1 ck.continuous) (m1 cG.continuous) (m1 ccb.continuous)
    (m1 cq.continuous) (m1 cmu.continuous) (m1 ctau.continuous) mD (m1 cp.continuous)
    (readout_first hbase hψ2 cyh.contDiffAt zyh) (readout_first hbase hψ2 cxu.contDiffAt zxu)
    (readout_first hbase hψ2 cxv.contDiffAt zxv) (readout_first hbase hψ2 ci.contDiffAt zi)
    (readout_first hbase hψ2 cxr.contDiffAt zxr) (readout_first hbase hψ2 cF.contDiffAt zF)
    (readout_first hbase hψ2 cK.contDiffAt zK) (readout_first hbase hψ2 cf.contDiffAt zf)
    (readout_first hbase hψ2 ck.contDiffAt zk) (readout_first hbase hψ2 cG.contDiffAt zG)
    (readout_first hbase hψ2 ccb.contDiffAt zcb) (readout_first hbase hψ2 cq.contDiffAt zq)
    (readout_first hbase hψ2 cmu.contDiffAt zmu)
    (readout_first hbase hψ2 ctau.contDiffAt ztau) hpO (uproc_shift hDO)
    (fun ε t z => hg _) (fun ε t z => hq _) hVm hDm

end Woodford.StabilizationWelfare.SmoothInSigmaMeasure615
