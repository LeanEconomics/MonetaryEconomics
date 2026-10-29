/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bAlongModel

/-!
# Proposition 6.15 along the equilibrium with local `C²` readouts and derived Calvo conditions

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (pp. 456–463), Proposition 6.15 and
(5.4)–(5.8), and Appendix E.2 (the perturbation equilibrium).

`SmoothInSigmaMeasure615.prop615_measure` assumes globally `C²` readouts (used only for their
measurability along the path) and takes the Calvo law of dispersion, the mean-price discrepancy
and the exact Calvo conditions `hM` (with genuine conditional expectations) as hypotheses on the
path.

* `aesm_along_sm`: a strongly measurable readout along the path is a.e.-strongly measurable.
* **`prop615_local`**: Proposition 6.15 with readouts that are `C²` only NEAR `ȳ`, plus
  strong measurability (the measurability that is actually needed).
* **`prop615_model`**: Proposition 6.15 along the equilibrium OF A MODEL whose period conditions
  contain the Calvo equations: the dispersion law, the discrepancy, the price index, the reset
  price, `k̂`, `f̂` (static components, `TidyR6bAlongModel.static_on_path`) and the recursions
  for `F` and `K` (expectational components, `TidyR6bAlongModel.expect_on_path`): `hlaw`,
  `hdisc` and `hM` are DERIVED, with local `C²` readouts.
-/

namespace Woodford.StabilizationWelfare.TidyR6bAlong615

open MeasureTheory Filter Topology Asymptotics
open LargeDistortions (fhatIso OmegaTilde loss615 Mden)
open SmoothInSigmaMeasure615
open SmoothInSigmaMeasure (adSub MModel)
open SmoothInSigma (pbar)
open SmoothInSigmaMeasureWelfare (ypath readout_first readout_second)
open SmoothInSigmaMeasureProps (discF dispersion_first_order_zero disc_second_order uproc_shift)
open TidyR6bAlongModel
open BridgeExtensions (UProc)

/-- Woodford (2003), App. E.2: a strongly measurable readout along the equilibrium path is
a.e.-strongly measurable under the i.i.d. law (the path is adapted to the shock filtration). -/
theorem aesm_along_sm {Y E : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
    [BorelSpace Y] [TopologicalSpace E]
    (ν0 : ProbabilityMeasure ℝ) (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) {R : Y → E}
    (hR : StronglyMeasurable R) (ε : ℝ) (t : ℕ) :
    AEStronglyMeasurable (along ψ ybar R ε t) (ExpectationsMeasureIID.iidSystem ν0).μ :=
  (hR.comp_measurable (((SmoothInSigmaMeasurePath.yproc_adapted ν0 (ψ (ybar, 0, ε)).2
    t).mono ((ExpectationsMeasureIID.iidSystem ν0).𝓕.le t)).measurable)).aestronglyMeasurable

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), p. 458, ALONG THE EQUILIBRIUM on the
i.i.d. probability space `(ℕ → ℝ, ν^ℕ)`, with GENUINE conditional expectations, with LOCALLY `C²`
readouts (restated from `SmoothInSigmaMeasure615.prop615_measure`, which assumes them globally
`C²`): let the decision vector carry, through strongly measurable readouts that are `C²` NEAR
`ȳ` and vanish at `ȳ`, log outputs `ŷ(i)`, relative prices, the
shocks `ξ_u, ξ_v`, inflation `π`, mean-price inflation `π̄`, the reset price, `F, K, f̂, k̂`, the
disturbances `G, c̄, q, μʷ, τ` and the dispersion `D` (as of the date). The model's equations are
the composites (`hg`, `hq`), the dispersion as the variance of log prices (`hV`), the Calvo law
of dispersion (`hlaw`), the mean-price/index discrepancy (`hdisc`) and the exact Calvo conditions
with `E_t = E[· | 𝓕_t]` (`hM`), along the equilibrium for small amplitudes. Then
`E∑βᵗU_t = W_0 − Ω̃ E∑βᵗL̃_t + t.i.p. + O(ε³)`: dispersion is `O(ε²)` because its first
derivative vanishes through the Calvo law, `π̄ − π = O(ε²)`, and
`SmoothInSigmaMeasure615.prop615_layerBM` applies. -/
theorem prop615_local {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν0 : ProbabilityMeasure ℝ)
    {ι Ξ : Type} [Fintype ι]
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
    (cyh : ContDiffAt ℝ 2 yhR ybar) (syh : StronglyMeasurable yhR)
    (crp : ContDiffAt ℝ 2 rpR ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (sxu : StronglyMeasurable xuR)
    (cxv : ContDiffAt ℝ 2 xvR ybar) (sxv : StronglyMeasurable xvR)
    (ci : ContDiffAt ℝ 2 inflR ybar) (si : StronglyMeasurable inflR)
    (cp : ContDiffAt ℝ 2 pibR ybar) (sp : StronglyMeasurable pibR)
    (cxr : ContDiffAt ℝ 2 xrR ybar) (sxr : StronglyMeasurable xrR)
    (cF : ContDiffAt ℝ 2 FR ybar) (sF : StronglyMeasurable FR)
    (cK : ContDiffAt ℝ 2 KR ybar) (sK : StronglyMeasurable KR)
    (cf : ContDiffAt ℝ 2 fR ybar) (sf : StronglyMeasurable fR)
    (ck : ContDiffAt ℝ 2 kR ybar) (sk : StronglyMeasurable kR)
    (cG : ContDiffAt ℝ 2 GR ybar) (sG : StronglyMeasurable GR)
    (ccb : ContDiffAt ℝ 2 cbR ybar) (scb : StronglyMeasurable cbR)
    (cq : ContDiffAt ℝ 2 qR ybar) (sq : StronglyMeasurable qR)
    (cmu : ContDiffAt ℝ 2 muwR ybar) (smu : StronglyMeasurable muwR)
    (ctau : ContDiffAt ℝ 2 tauR ybar) (stau : StronglyMeasurable tauR)
    (cD : ContDiffAt ℝ 2 DR ybar) (sD : StronglyMeasurable DR)
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
  have hD1 := dispersion_first_order_zero hbase hψ1 (cD.differentiableAt
    (by norm_num)) (cp.differentiableAt (by norm_num)) zp hlaw
  have hDO : UProc (𝓝 0) (fun ε t z => DR (ypath ψ ybar ε t z)) fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cD zD).congr_left fun b => ?_
    simp only [hD1, smul_zero, sub_zero]
  have hpO := disc_second_order hw0 hw1 (by linarith : θ ≠ 1) hbase hψ2 crp
    ci zrp zi hdisc
  have m1 : ∀ {E : Type} [TopologicalSpace E] {R : Y → E}, StronglyMeasurable R → ∀ ε t,
      AEStronglyMeasurable (along ψ ybar R ε t) (ExpectationsMeasureIID.iidSystem ν0).μ :=
    fun {E} _ {R} hR ε t => aesm_along_sm ν0 ψ ybar hR ε t
  have mD : ∀ ε t, AEStronglyMeasurable (dispAlong ψ ybar DR ε t)
      (ExpectationsMeasureIID.iidSystem ν0).μ := fun ε t => by
    cases t with
    | zero => exact aestronglyMeasurable_const
    | succ k => exact m1 sD ε k
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
    hvy hvyy hM (m1 syh) (m1 sxu) (m1 sxv)
    (m1 si) (m1 sxr) (m1 sF) (m1 sK)
    (m1 sf) (m1 sk) (m1 sG) (m1 scb)
    (m1 sq) (m1 smu) (m1 stau) mD (m1 sp)
    (readout_first hbase hψ2 cyh zyh) (readout_first hbase hψ2 cxu zxu)
    (readout_first hbase hψ2 cxv zxv) (readout_first hbase hψ2 ci zi)
    (readout_first hbase hψ2 cxr zxr) (readout_first hbase hψ2 cF zF)
    (readout_first hbase hψ2 cK zK) (readout_first hbase hψ2 cf zf)
    (readout_first hbase hψ2 ck zk) (readout_first hbase hψ2 cG zG)
    (readout_first hbase hψ2 ccb zcb) (readout_first hbase hψ2 cq zq)
    (readout_first hbase hψ2 cmu zmu)
    (readout_first hbase hψ2 ctau ztau) hpO (uproc_shift hDO)
    (fun ε t z => hg _) (fun ε t z => hq _) hVm hDm

/-- **Woodford (2003), Proposition 6.15, (5.5)–(5.8), p. 458, along the equilibrium OF A MODEL,
with local `C²` readouts.** Let `ψ` be the local equilibrium of a model on `(ℕ → ℝ, ν^ℕ)` whose
period conditions contain, as components, the Calvo law of dispersion, the mean-price
discrepancy, the price index, the reset price, `k̂`, `f̂` (all static) and the recursions for
`F` and `K` (current part minus `αβ` times a lead). Then the conclusion of `prop615_local` holds:
the hypotheses `hlaw`, `hdisc` and `hM` of `SmoothInSigmaMeasure615.prop615_measure` are derived
(`TidyR6bAlongModel.static_on_path`, `TidyR6bAlongModel.expect_on_path`). -/
theorem prop615_model {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν0 : ProbabilityMeasure ℝ)
    {ι Ξ : Type} [Fintype ι]
    [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ)
    (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) (hMd : Mden ω σ sC Φ ≠ 0) {wt : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f) (hlawN : N.law () = ν0)
    (hψ : N.LocalSol ybar ψ)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR rpR : Y → ι → ℝ} {xuR xvR : Y → Ξ}
    {inflR pibR xrR FR KR fR kR GR cbR qR muwR tauR DR : Y → ℝ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (syh : StronglyMeasurable yhR)
    (crp : ContDiffAt ℝ 2 rpR ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (sxu : StronglyMeasurable xuR)
    (cxv : ContDiffAt ℝ 2 xvR ybar) (sxv : StronglyMeasurable xvR)
    (ci : ContDiffAt ℝ 2 inflR ybar) (si : StronglyMeasurable inflR)
    (cp : ContDiffAt ℝ 2 pibR ybar) (sp : StronglyMeasurable pibR)
    (cxr : ContDiffAt ℝ 2 xrR ybar) (sxr : StronglyMeasurable xrR)
    (cF : ContDiffAt ℝ 2 FR ybar) (sF : StronglyMeasurable FR)
    (cK : ContDiffAt ℝ 2 KR ybar) (sK : StronglyMeasurable KR)
    (cf : ContDiffAt ℝ 2 fR ybar) (sf : StronglyMeasurable fR)
    (ck : ContDiffAt ℝ 2 kR ybar) (sk : StronglyMeasurable kR)
    (cG : ContDiffAt ℝ 2 GR ybar) (sG : StronglyMeasurable GR)
    (ccb : ContDiffAt ℝ 2 cbR ybar) (scb : StronglyMeasurable cbR)
    (cq : ContDiffAt ℝ 2 qR ybar) (sq : StronglyMeasurable qR)
    (cmu : ContDiffAt ℝ 2 muwR ybar) (smu : StronglyMeasurable muwR)
    (ctau : ContDiffAt ℝ 2 tauR ybar) (stau : StronglyMeasurable tauR)
    (cD : ContDiffAt ℝ 2 DR ybar) (sD : StronglyMeasurable DR)
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
    (πD πP πI πR πk πf πF πK : Z →L[ℝ] ℝ)
    (hπD : ∀ a b c x e, πD (N.f (a, b, c, x, e)) =
      DR b - (α * DR c + α / (1 - α) * pibR b ^ 2))
    (hπP : ∀ a b c x e, πP (N.f (a, b, c, x, e)) =
      pibR b - inflR b - discF wt θ (fun i => rpR b i + inflR b) (rpR c))
    (hπI : ∀ a b c x e, πI (N.f (a, b, c, x, e)) =
      α * (Real.exp ((θ - 1) * inflR b) - 1) + (1 - α) * (Real.exp (-((θ - 1) * xrR b)) - 1))
    (hπR : ∀ a b c x e, πR (N.f (a, b, c, x, e)) = (1 + ω * θ) * xrR b - (KR b - FR b))
    (hπk : ∀ a b c x e, πk (N.f (a, b, c, x, e)) =
      kR b - ((1 + ω) * BridgeExtensions.logYidx wt θ (yhR b) - ω * qR b + muwR b))
    (hπf : ∀ a b c x e, πf (N.f (a, b, c, x, e)) =
      fR b - fhatIso σ sC (BridgeExtensions.logYidx wt θ (yhR b)) (GR b) (cbR b) (tauR b))
    (hπF : ∀ a b c x e, πF (N.f (a, b, c, x, e)) =
      (Real.exp (FR b) - 1 - (1 - α * β) * (Real.exp (fR b) - 1)) -
        α * β * (Real.exp ((θ - 1) * inflR a + FR a) - 1))
    (hπK : ∀ a b c x e, πK (N.f (a, b, c, x, e)) =
      (Real.exp (KR b) - 1 - (1 - α * β) * (Real.exp (kR b) - 1)) -
        α * β * (Real.exp (θ * (1 + ω) * inflR a + KR a) - 1)) :
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
      =O[𝓝 0] fun ε => ε ^ 3  := by
  set μ := (ExpectationsMeasureIID.iidSystem ν0).μ
  have hlaw := static_on_path hN hc hψ πD hπD
  have hdisc := static_on_path hN hc hψ πP hπP
  have hI := static_on_path hN hc hψ πI hπI
  have hR := static_on_path hN hc hψ πR hπR
  have hk := static_on_path hN hc hψ πk hπk
  have hf := static_on_path hN hc hψ πf hπf
  have hF := expect_on_path ν0 hN hc hlawN hψ πF (A := fun b =>
    Real.exp (FR b) - 1 - (1 - α * β) * (Real.exp (fR b) - 1))
    (B := fun a => α * β * (Real.exp ((θ - 1) * inflR a + FR a) - 1)) hπF
  have hK := expect_on_path ν0 hN hc hlawN hψ πK (A := fun b =>
    Real.exp (KR b) - 1 - (1 - α * β) * (Real.exp (kR b) - 1))
    (B := fun a => α * β * (Real.exp (θ * (1 + ω) * inflR a + KR a) - 1)) hπK
  refine prop615_local ν0 hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd hw0 hw1 hu hv hucc hvy hvyy
    hψ.base hψ2 cyh syh crp cxu sxu cxv sxv ci si cp sp cxr sxr cF sF cK sK cf sf ck sk cG sG
    ccb scb cq sq cmu smu ctau stau cD sD zyh zrp zxu zxv zi zp zxr zF zK zf zk zG zcb zq zmu
    ztau zD hg hq hV ?_ ?_ ?_
  · filter_upwards [hlaw] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)
  · filter_upwards [hdisc] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)
  · filter_upwards [hI, hR, hk, hf, hF, hK] with ε eI eR ek ef eF eK
    have hrec : ∀ (e : ℝ) (Fr fr : Y → ℝ),
        (∀ t, (fun ω => Real.exp (Fr (ypath ψ ybar ε t ω)) - 1 - (1 - α * β) *
          (Real.exp (fr (ypath ψ ybar ε t ω)) - 1)) =ᵐ[μ]
          μ[fun ω => α * β * (Real.exp (e * inflR (ypath ψ ybar ε (t + 1) ω) +
            Fr (ypath ψ ybar ε (t + 1) ω)) - 1) | (ExpectationsMeasureIID.iidSystem ν0).𝓕 t]) →
        RecEqM μ (fun t => (ExpectationsMeasureIID.iidSystem ν0).𝓕 t) α β e
          (along ψ ybar inflR ε) (along ψ ybar Fr ε) (along ψ ybar fr ε) := by
      intro e Fr fr h t
      have hs := condExp_smul (μ := μ) (α * β) (fun ω => Real.exp (e * inflR (ypath ψ ybar ε
        (t + 1) ω) + Fr (ypath ψ ybar ε (t + 1) ω)) - 1) ((ExpectationsMeasureIID.iidSystem ν0).𝓕 t)
      filter_upwards [h t, hs] with ω h1 h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      have e2 : (fun ω => α * β * (Real.exp (e * inflR (ypath ψ ybar ε (t + 1) ω) +
          Fr (ypath ψ ybar ε (t + 1) ω)) - 1)) = (α * β) • fun ω => Real.exp (e *
            inflR (ypath ψ ybar ε (t + 1) ω) + Fr (ypath ψ ybar ε (t + 1) ω)) - 1 := by
        funext ω; simp [smul_eq_mul]
      rw [e2] at h1
      simp only [along]
      linarith
    exact ⟨fun t ω => eI t ω, fun t ω => sub_eq_zero.mp (eR t ω),
      hrec (θ - 1) FR fR eF, hrec (θ * (1 + ω)) KR kR eK,
      fun t ω => sub_eq_zero.mp (ek t ω), fun t ω => sub_eq_zero.mp (ef t ω)⟩

end Woodford.StabilizationWelfare.TidyR6bAlong615
