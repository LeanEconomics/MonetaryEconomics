/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasurePath
import StabilizationWelfare.SmoothInSigmaWelfare
import StabilizationWelfare.BridgeExtensions

/-!
# Layer B along the perturbation equilibrium on the i.i.d. probability space

Woodford (2003), *Interest and Prices*, Chapter 6, §2 (p. 394, "bounded fluctuations"), §4.4
(pp. 443–448, Propositions 6.12–6.13) and Appendix E.2, E.8 (pp. 695, 706–708).

`BridgeExtensions` proves the Layer-B welfare expansions for any family whose first-order
variables are `O(ε)` and whose first-order decompositions have `O(ε²)` remainders UNIFORMLY in
the date and the state (`UProc`, along `l ×ˢ ⊤`). The core `ExpectationSystem` of those
discounted statements cannot carry an i.i.d. law with a continuum of values, so here the
state space is the genuine probability space `(ℕ → ℝ, ν^ℕ)` of `ExpectationsMeasureIID` and
expectations are Bochner integrals.

For the equilibrium `ψ` of `SmoothInSigmaMeasure` (single regime, any bounded-support law),
read along the path with amplitude `ε = σ` (`ypath`, the first-order solution `y1path`), every
`C²` readout `G` of the decision vector with `G(ȳ) = 0` satisfies the `UProc` hypotheses
(`readout_first`, `readout_bdd`, `readout_second`): this is the book's "bounded fluctuations",
PROVED. Proposition 6.12 (sticky prices and wages) then holds along the equilibrium: its
remaining hypotheses are the model's equations defining the composite disturbances.

## Main results

* `taylor_point_isBigO`: `G(y) − G(ȳ) − DG(ȳ)(y − ȳ) = O(‖y − ȳ‖²)` for `G` of class `C²`
  at `ȳ`.
* `ypath`, `y1path`, `path_taylor` (`y_t(ε, ω) = ȳ + εy¹_t(ω) + O(ε²)` with ONE constant for
  all dates and paths), `norm_y1path_le`.
* `readout_first`, `readout_bdd`, `readout_second`: the `UProc` hypotheses for a readout.
* `mdsum_o`: uniform orders survive expectation `∫ dν^ℕ` and discounted sums
  `∑ βᵗ ∫ X_t dν^ℕ`.
* `contDiffAt_logYidx`, `logYidx_zero`: the Dixit–Stiglitz output index of a `C²` readout.
* `rem612`, `prop612_measure` (Proposition 6.12 along the equilibrium, uniformly in the date
  and the path) and `prop612_measure_discounted` (expected discounted utility, `O(ε³)`).
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaMeasureWelfare

open MeasureTheory Filter Topology Asymptotics
open SmoothInSigmaMeasure (Hist adSub MModel)
open SmoothInSigmaMeasurePath (histOf)
open SmoothInSigma (Bd norm_apply_le pbar)
open BridgeExtensions (UProc)

/-! ## Second-order Taylor bound at a point -/

/-- Woodford (2003), (2.10), p. 394 (**a `C²` function is linear up to `O(‖y − ȳ‖²)`**): for
`G` of class `C²` at `ȳ`, `G(y) − G(ȳ) − DG(ȳ)(y − ȳ) = O(‖y − ȳ‖²)` near `ȳ`. -/
theorem taylor_point_isBigO {Y V : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {G : Y → V} {ybar : Y}
    (hG : ContDiffAt ℝ 2 G ybar) :
    (fun y => G y - G ybar - fderiv ℝ G ybar (y - ybar)) =O[𝓝 ybar]
      fun y => ‖y - ybar‖ ^ 2 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ G) ybar := hG.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hL⟩ := h1.exists_lipschitzOnWith
  have hd : ∀ᶠ z in 𝓝 ybar, DifferentiableAt ℝ G z :=
    (hG.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht hd)
  have h0t : ybar ∈ t := mem_of_mem_nhds ht
  refine IsBigO.of_bound K ?_
  filter_upwards [Metric.ball_mem_nhds ybar hδ] with y hy
  have hyδ : ‖y - ybar‖ < δ := by simpa [dist_eq_norm] using hy
  have hsub : Metric.closedBall ybar ‖y - ybar‖ ⊆ Metric.ball ybar δ :=
    Metric.closedBall_subset_ball hyδ
  have hymem : y ∈ Metric.closedBall ybar ‖y - ybar‖ := by simp [dist_eq_norm]
  have key := (convex_closedBall ybar ‖y - ybar‖).norm_image_sub_le_of_norm_fderiv_le'
    (f := G) (φ := fderiv ℝ G ybar) (C := K * ‖y - ybar‖) (fun z hz => (hball (hsub hz)).2)
    (fun z hz => by
      have hzt : z ∈ t := (hball (hsub hz)).1
      have := hL.dist_le_mul z hzt ybar h0t
      rw [dist_eq_norm] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
      simpa [dist_eq_norm] using hz)
    (Metric.mem_closedBall_self (norm_nonneg _)) hymem
  refine key.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  ring

/-! ## The equilibrium along the path -/

variable {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Woodford (2003), §2, p. 394 (**the equilibrium family along the path**): with amplitude
`ε = σ` (`y_{−1} = ȳ`, `s₀ = 0`), `y_t(ε, ω) = ψ(ȳ, 0, ε)(t, h_t(ω))`. -/
def ypath (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) (ε : ℝ) (t : ℕ) (ω : ℕ → ℝ) : Y :=
  (ψ (ybar, 0, ε) : Bd (ℕ × Hist Unit) Y) (t, histOf t ω)

/-- Woodford (2003), §2, p. 394: the first-order solution along the path,
`y¹_t(ω) = ∂_σψ(p̄)(t, h_t(ω))`. -/
noncomputable def y1path (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) (t : ℕ)
    (ω : ℕ → ℝ) : Y :=
  (fderiv ℝ ψ (pbar ybar) (0, 0, 1) : Bd (ℕ × Hist Unit) Y) (t, histOf t ω)

/-- Woodford (2003), §2, p. 394: the first-order solution is bounded uniformly in the date and
the path. -/
theorem norm_y1path_le (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) (t : ℕ)
    (ω : ℕ → ℝ) : ‖y1path ψ ybar t ω‖ ≤ ‖fderiv ℝ ψ (pbar ybar) (0, 0, 1)‖ :=
  norm_apply_le _ _

/-- Woodford (2003), (2.10), p. 394, and App. E.2 (**the equilibrium is `ȳ + εy¹ + O(ε²)`
uniformly**): if `ψ` is `C²` at `p̄` (`SmoothInSigmaMeasure.MModel.exists_smooth_solution`), then
`y_t(ε, ω) − ȳ − εy¹_t(ω) = O(ε²)` along `𝓝 0 ×ˢ ⊤`, i.e. with ONE constant for every date and
every path. -/
theorem path_taylor {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) :
    UProc (𝓝 0) (fun ε t ω => ypath ψ ybar ε t ω - ybar - ε • y1path ψ ybar t ω)
      fun ε => ε ^ 2 := by
  set γ : ℝ → Y × ℝ × ℝ := fun ε => (ybar, 0, ε) with hγ
  have hγd : ∀ ε, HasDerivAt γ ((0 : Y), (0 : ℝ), (1 : ℝ)) ε := fun ε =>
    (hasDerivAt_const ε ybar).prodMk ((hasDerivAt_const ε (0 : ℝ)).prodMk (hasDerivAt_id ε))
  have hγc : ContDiff ℝ 2 γ := contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  set φ : ℝ → adSub (R := Unit) Y := fun ε => ψ (γ ε) with hφ
  have hφc : ContDiffAt ℝ 2 φ 0 :=
    (show ContDiffAt ℝ 2 (ψ ∘ γ) 0 from ContDiffAt.comp (f := γ) 0 hψ2 hγc.contDiffAt)
  have hφd : deriv φ 0 = fderiv ℝ ψ (pbar ybar) (0, 0, 1) :=
    ((hψ2.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 (hγd 0)).deriv
  have hT := (SmoothInSigmaWelfare.taylor_one_isBigO hφc).comp_tendsto
    (tendsto_fst (f := 𝓝 (0 : ℝ)) (g := (⊤ : Filter (ℕ × (ℕ → ℝ)))))
  refine IsBigO.trans ?_ hT
  refine IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)
  rw [one_mul]
  have hφ0 : φ 0 = SmoothInSigmaMeasure.MModel.ubar ybar := hbase
  simp only [Function.comp_apply, hφd, hφ0]
  refine le_trans (le_of_eq ?_) (norm_apply_le _ (b.2.1, histOf b.2.1 b.2.2))
  rfl

/-! ## Readouts of the decision vector -/

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Woodford (2003), §2, p. 394 (**first-order values are bounded**): `DG(ȳ)y¹_t(ω) = O(1)`
uniformly in the date and the path. -/
theorem readout_bdd (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) (G : Y → V) :
    UProc (𝓝 0) (fun (_ : ℝ) t ω => fderiv ℝ G ybar (y1path ψ ybar t ω)) fun _ => (1 : ℝ) := by
  refine IsBigO.of_bound (‖fderiv ℝ G ybar‖ * ‖fderiv ℝ ψ (pbar ybar) (0, 0, 1)‖)
    (Eventually.of_forall fun b => ?_)
  rw [norm_one, mul_one]
  exact ((fderiv ℝ G ybar).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_y1path_le ψ ybar _ _) (norm_nonneg _))

/-- Woodford (2003), (2.10), p. 394 (**the second-order remainder of a readout**): for `G` of
class `C²` at `ȳ` with `G(ȳ) = 0`,
`G(y_t(ε, ω)) − ε DG(ȳ)y¹_t(ω) = O(ε²)` uniformly in the date and the path. -/
theorem readout_second {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) {G : Y → V} (hG : ContDiffAt ℝ 2 G ybar)
    (hG0 : G ybar = 0) :
    UProc (𝓝 0) (fun ε t ω => G (ypath ψ ybar ε t ω) - ε • fderiv ℝ G ybar (y1path ψ ybar t ω))
      fun ε => ε ^ 2 := by
  set L := (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ))) with hLd
  have hs : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1) L (𝓝 0) := tendsto_fst
  have hP : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => ypath ψ ybar b.1 b.2.1 b.2.2 - ybar -
      b.1 • y1path ψ ybar b.2.1 b.2.2) =O[L] fun b => b.1 ^ 2 := path_taylor hbase hψ2
  have hy1 : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => y1path ψ ybar b.2.1 b.2.2) =O[L]
      fun _ => (1 : ℝ) :=
    IsBigO.of_bound ‖fderiv ℝ ψ (pbar ybar) (0, 0, 1)‖ (Eventually.of_forall fun b => by
      rw [norm_one, mul_one]; exact norm_y1path_le ψ ybar _ _)
  have h21 : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1 ^ 2) =O[L] fun b => b.1 ^ 1 :=
    BridgeExtensions.o_weaken hs (by norm_num) (isBigO_refl _ _)
  have hD : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => ypath ψ ybar b.1 b.2.1 b.2.2 - ybar) =O[L]
      fun b => b.1 ^ 1 :=
    ((hP.trans h21).add (((isBigO_refl (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1) L).smul hy1).congr_right
      fun b => by ring)).congr_left fun b => by abel
  have hT : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => ypath ψ ybar b.1 b.2.1 b.2.2) L (𝓝 ybar) := by
    have := (BridgeExtensions.tendsto_of_o_one hs hD).add_const ybar
    simpa using this
  have hTay := (taylor_point_isBigO hG).comp_tendsto hT
  have hD2 : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => ‖ypath ψ ybar b.1 b.2.1 b.2.2 - ybar‖ ^ 2) =O[L]
      fun b => b.1 ^ 2 :=
    (hD.norm_left.pow 2).congr_right fun b => by ring
  have hlin := ((fderiv ℝ G ybar).isBigO_comp _ L).trans hP
  refine ((hTay.trans hD2).add hlin).congr_left fun b => ?_
  simp only [Function.comp_apply, hG0, sub_zero, map_sub, map_smul]
  abel

/-- Woodford (2003), §2, p. 394 (**bounded fluctuations, PROVED**): for `G` of class `C²` at
`ȳ` with `G(ȳ) = 0`, `G(y_t(ε, ω)) = O(ε)` uniformly in the date and the path. -/
theorem readout_first {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) {G : Y → V} (hG : ContDiffAt ℝ 2 G ybar)
    (hG0 : G ybar = 0) :
    UProc (𝓝 0) (fun ε t ω => G (ypath ψ ybar ε t ω)) fun ε => ε ^ 1 := by
  have hs : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1)
      ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ)))) (𝓝 0) := tendsto_fst
  have h2 : UProc (𝓝 0) (fun ε t ω => G (ypath ψ ybar ε t ω) -
      ε • fderiv ℝ G ybar (y1path ψ ybar t ω)) fun ε => ε ^ 1 :=
    IsBigO.trans (readout_second hbase hψ2 hG hG0)
      (BridgeExtensions.o_weaken hs (by norm_num) (isBigO_refl _ _))
  exact (h2.add (((isBigO_refl (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1) _).smul
    (readout_bdd ψ ybar G)).congr_right fun b => by ring)).congr_left fun b => sub_add_cancel _ _

/-! ## Expectations and discounted sums on the probability space -/

/-- Woodford (2003), (5.2), p. 456, on a genuine probability space (**uniform orders and
discounting with Bochner expectations**): if `X_t(ω) = O(g)` uniformly in `(t, ω)` and
`0 ≤ β < 1`, then `∑ βᵗ ∫ X_t dμ = O(g)` for any probability measure `μ`. -/
theorem mdsum_o {A Ω : Type} [MeasurableSpace Ω] {l : Filter A} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {X : A → ℕ → Ω → ℝ}
    {g : A → ℝ} (h : UProc l X g) :
    (fun a => ∑' t, β ^ t * ∫ ω, X a t ω ∂μ) =O[l] g := by
  obtain ⟨C, hC⟩ := BridgeExtensions.uniform_bound h
  refine IsBigO.of_bound (C / (1 - β)) ?_
  filter_upwards [hC] with a ha
  have hb : ∀ t, |∫ ω, X a t ω ∂μ| ≤ C * |g a| := fun t => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := X a t) (C := C * |g a|)
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using ha (t, ω))
    simpa [Real.norm_eq_abs] using this
  have h1 := Sequences.abs_tsum_le hb hβ0 hβ1
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc _ ≤ C * |g a| / (1 - β) := h1
    _ = C / (1 - β) * |g a| := by ring

/-! ## The Dixit–Stiglitz output index of a readout -/

omit [NormedSpace ℝ Y] in
/-- Woodford (2003), eq. (2.6), p. 393: the log output index vanishes at the steady state,
`log Y(0) = 0` (weights summing to one). -/
theorem logYidx_zero {ι : Type} [Fintype ι] {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (θ : ℝ) :
    BridgeExtensions.logYidx w θ 0 = 0 := by
  simp [BridgeExtensions.logYidx, ExpLogCES.cesIndex, hw1]

/-- Woodford (2003), eq. (2.6), p. 393 (**the output index is smooth**): if the cross-section
`ŷ(y)` of log outputs is `C²` at `ȳ` with `ŷ(ȳ) = 0`, so is `log Y(ŷ(y))`
(`Y = [∑ w_i (e^{ŷ_i})^{1−θ⁻¹}]^{1/(1−θ⁻¹)}`, weights summing to one). -/
theorem contDiffAt_logYidx {ι : Type} [Fintype ι] {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (θ : ℝ)
    {yh : Y → ι → ℝ} {ybar : Y} (hyh : ContDiffAt ℝ 2 yh ybar) (h0 : yh ybar = 0) :
    ContDiffAt ℝ 2 (fun y => BridgeExtensions.logYidx w θ (yh y)) ybar := by
  unfold BridgeExtensions.logYidx ExpLogCES.cesIndex
  have hi : ∀ i, ContDiffAt ℝ 2 (fun y => Real.exp (yh y i) ^ (1 - θ⁻¹)) ybar := fun i =>
    ((contDiffAt_pi.1 hyh i).exp).rpow_const_of_ne (Real.exp_pos _).ne'
  have hs : ContDiffAt ℝ 2 (fun y => ∑ i, w i * Real.exp (yh y i) ^ (1 - θ⁻¹)) ybar :=
    ContDiffAt.sum fun i _ => contDiffAt_const.mul (hi i)
  have hv : ∑ i, w i * Real.exp (yh ybar i) ^ (1 - θ⁻¹) = 1 := by simp [h0, hw1]
  refine (hs.rpow_const_of_ne (by rw [hv]; norm_num)).log ?_
  simp only [hv, Real.one_rpow]
  norm_num

/-! ## Proposition 6.12 along the equilibrium -/

open ExpLogCES (crossVar)

/-- Woodford (2003), **Proposition 6.12**, (4.28)/(E.33): the Layer-B remainder of the sticky
price and wage model, actual period utility minus
`t.i.p. − (ε²/2)·Ȳu_c·loss612(first-order solution)`. -/
noncomputable def rem612 {ι J Ξ : Type} [Fintype ι] [Fintype J] [NormedAddCommGroup Ξ]
    [NormedSpace ℝ Ξ] (u v : ℝ × Ξ → ℝ) (w : ι → ℝ) (ωt : J → ℝ)
    (θp θw Ybar Hbar σi ω ν ωp φh : ℝ) (G : ℝ → ℝ) (a : ℝ) (yh : ι → ℝ) (lw : J → ℝ)
    (xu xv : Ξ) (g hb af gf hbf Yf : ℝ) (y1 : ι → ℝ) (lw1 : J → ℝ) (s : ℝ) : ℝ :=
  BridgeExtensions.periodU12 u v w ωt θp θw Ybar Hbar G a yh lw xu xv -
    ((BridgeExtensions.tip12 u v Ybar Hbar xu xv + Ybar * BridgeExtensions.dY u (Ybar, 0) *
      StickyWageWelfare.tip612 σi ω ν 0 g a hb) -
      s ^ 2 / 2 * (Ybar * BridgeExtensions.dY u (Ybar, 0) *
        BridgeExtensions.loss612 σi ω ν θp ωp θw φh gf af hbf Yf (crossVar w y1 / θp ^ 2)
          (crossVar ωt lw1)))

/-- Woodford (2003), **Proposition 6.12**, (4.28)/(E.33), pp. 444, 706–708, ALONG THE
EQUILIBRIUM on the i.i.d. probability space: let the decision vector `y` carry, through `C²`
readouts vanishing at `ȳ`, the log outputs `ŷ(i)`, log wages `lw(j)`, the technology term `a`,
the composite disturbances `g, h̄` and the preference shocks `ξ_u, ξ_v` (the model's equations
`hg`, `hhb` define the composites). For the `C²` equilibrium `ψ` with amplitude `ε = σ`, the
actual period utility along every path is
`t.i.p. − (ε²/2)·Ȳu_c·loss612(first-order solution) + O(ε³)`, UNIFORMLY in the date and the
path. Every first-order hypothesis of `BridgeExtensions.prop612_layerB` is discharged. -/
theorem prop612_measure {ι J Ξ : Type} [Fintype ι] [Fintype J] [NormedAddCommGroup Ξ]
    [NormedSpace ℝ Ξ] {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {ωt : J → ℝ}
    (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1) {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1)
    (hθw1 : θw ≠ 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {σi ω ν ωp φh Ybar Hbar : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σi * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvhh : BridgeExtensions.dYY v (Hbar, 0) = ν * BridgeExtensions.dY v (Hbar, 0) / Hbar)
    (hss : Hbar * BridgeExtensions.dY v (Hbar, 0) * φh = Ybar * BridgeExtensions.dY u (Ybar, 0))
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR : Y → ι → ℝ} {lwR : Y → J → ℝ} {aR gR hbR : Y → ℝ} {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (clw : ContDiffAt ℝ 2 lwR ybar)
    (ca : ContDiffAt ℝ 2 aR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (chb : ContDiffAt ℝ 2 hbR ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zlw : lwR ybar = 0) (za : aR ybar = 0) (zg : gR ybar = 0)
    (zhb : hbR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (hg : ∀ y, BridgeExtensions.dYXi u (Ybar, 0) (xuR y) =
      σi * BridgeExtensions.dY u (Ybar, 0) * gR y)
    (hhb : ∀ y, BridgeExtensions.dYXi v (Hbar, 0) (xvR y) =
      -(ν * BridgeExtensions.dY v (Hbar, 0) * hbR y)) :
    UProc (𝓝 0) (fun ε t ω' => rem612 u v w ωt θp θw Ybar Hbar σi ω ν ωp φh G
      (aR (ypath ψ ybar ε t ω')) (yhR (ypath ψ ybar ε t ω')) (lwR (ypath ψ ybar ε t ω'))
      (xuR (ypath ψ ybar ε t ω')) (xvR (ypath ψ ybar ε t ω')) (gR (ypath ψ ybar ε t ω'))
      (hbR (ypath ψ ybar ε t ω')) (fderiv ℝ aR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ gR ybar (y1path ψ ybar t ω')) (fderiv ℝ hbR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ (fun y => BridgeExtensions.logYidx w θp (yhR y)) ybar (y1path ψ ybar t ω'))
      (fderiv ℝ yhR ybar (y1path ψ ybar t ω')) (fderiv ℝ lwR ybar (y1path ψ ybar t ω')) ε)
      fun ε => ε ^ 3 := by
  have hs : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1)
      ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ)))) (𝓝 0) := tendsto_fst
  have cY := contDiffAt_logYidx hw1 θp cyh zyh
  have zY : (fun y => BridgeExtensions.logYidx w θp (yhR y)) ybar = 0 := by
    simp only [zyh]; exact logYidx_zero hw1 θp
  exact BridgeExtensions.prop612_layerB hs hw0 hw1 hωt0 hωt1 hθp hθp1 hθw1 hu hv hG hG0 hG1
    hG2 hω hφ hσω hucc hvhh hss (fun b => hg _) (fun b => hhb _)
    (readout_first hbase hψ2 cyh zyh) (readout_first hbase hψ2 clw zlw)
    (readout_first hbase hψ2 cxu zxu) (readout_first hbase hψ2 cxv zxv)
    (readout_bdd ψ ybar yhR) (readout_bdd ψ ybar lwR) (readout_bdd ψ ybar aR)
    (readout_bdd ψ ybar gR) (readout_bdd ψ ybar hbR)
    (readout_bdd ψ ybar fun y => BridgeExtensions.logYidx w θp (yhR y))
    (readout_second hbase hψ2 cyh zyh) (readout_second hbase hψ2 clw zlw)
    (readout_second hbase hψ2 ca za) (readout_second hbase hψ2 cg zg)
    (readout_second hbase hψ2 chb zhb) (readout_second hbase hψ2 cY zY)

/-- Woodford (2003), **Proposition 6.12**, (4.28)/(E.33), and (5.2) (**expected discounted
utility along the equilibrium**): under the hypotheses of `prop612_measure`, on the i.i.d.
probability space `(ℕ → ℝ, ν^ℕ)` of any law `ν`,
`∑ βᵗ E[U_t] = ∑ βᵗ E[t.i.p._t − (ε²/2)·Ȳu_c·loss612_t(first-order solution)] + O(ε³)`
(the expectations are genuine Bochner integrals). -/
theorem prop612_measure_discounted (ν0 : ProbabilityMeasure ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ι J Ξ : Type} [Fintype ι] [Fintype J] [NormedAddCommGroup Ξ]
    [NormedSpace ℝ Ξ] {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {ωt : J → ℝ}
    (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1) {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1)
    (hθw1 : θw ≠ 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {σi ω ν ωp φh Ybar Hbar : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σi * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvhh : BridgeExtensions.dYY v (Hbar, 0) = ν * BridgeExtensions.dY v (Hbar, 0) / Hbar)
    (hss : Hbar * BridgeExtensions.dY v (Hbar, 0) * φh = Ybar * BridgeExtensions.dY u (Ybar, 0))
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR : Y → ι → ℝ} {lwR : Y → J → ℝ} {aR gR hbR : Y → ℝ} {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (clw : ContDiffAt ℝ 2 lwR ybar)
    (ca : ContDiffAt ℝ 2 aR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (chb : ContDiffAt ℝ 2 hbR ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zlw : lwR ybar = 0) (za : aR ybar = 0) (zg : gR ybar = 0)
    (zhb : hbR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (hg : ∀ y, BridgeExtensions.dYXi u (Ybar, 0) (xuR y) =
      σi * BridgeExtensions.dY u (Ybar, 0) * gR y)
    (hhb : ∀ y, BridgeExtensions.dYXi v (Hbar, 0) (xvR y) =
      -(ν * BridgeExtensions.dY v (Hbar, 0) * hbR y)) :
    (fun ε => ∑' t, β ^ t * ∫ ω', rem612 u v w ωt θp θw Ybar Hbar σi ω ν ωp φh G
      (aR (ypath ψ ybar ε t ω')) (yhR (ypath ψ ybar ε t ω')) (lwR (ypath ψ ybar ε t ω'))
      (xuR (ypath ψ ybar ε t ω')) (xvR (ypath ψ ybar ε t ω')) (gR (ypath ψ ybar ε t ω'))
      (hbR (ypath ψ ybar ε t ω')) (fderiv ℝ aR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ gR ybar (y1path ψ ybar t ω')) (fderiv ℝ hbR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ (fun y => BridgeExtensions.logYidx w θp (yhR y)) ybar (y1path ψ ybar t ω'))
      (fderiv ℝ yhR ybar (y1path ψ ybar t ω')) (fderiv ℝ lwR ybar (y1path ψ ybar t ω')) ε
      ∂(ExpectationsMeasureIID.iidSystem ν0).μ) =O[𝓝 0] fun ε => ε ^ 3 :=
  mdsum_o _ hβ0 hβ1 (prop612_measure hw0 hw1 hωt0 hωt1 hθp hθp1 hθw1 hu hv hG hG0 hG1 hG2 hω
    hφ hσω hucc hvhh hss hbase hψ2 cyh clw ca cg chb cxu cxv zyh zlw za zg zhb zxu zxv hg hhb)

/-! ## Proposition 6.10 along the equilibrium -/

/-- Woodford (2003), App. E.6, p. 703 (**the two-sector aggregate is smooth**): for `C²`
readouts `φ̂_1, φ̂_2, Ŷ_1, Ŷ_2` at `ȳ`, the log of the exact two-sector CES aggregate
`log(Y/Ȳ)` is `C²` at `ȳ` (by `TwoSectorWelfare.log_upperCES` it is
`r⁻¹ log(n₁e^{z₁} + n₂e^{z₂})` with `z_j` linear). -/
theorem contDiffAt_logY2 {n1 η Ybar : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η)
    (hη1 : η ≠ 1) (hY : 0 < Ybar) {f1 f2 Y1 Y2 : Y → ℝ} {ybar : Y}
    (c1 : ContDiffAt ℝ 2 f1 ybar) (c2 : ContDiffAt ℝ 2 f2 ybar) (c3 : ContDiffAt ℝ 2 Y1 ybar)
    (c4 : ContDiffAt ℝ 2 Y2 ybar) :
    ContDiffAt ℝ 2 (fun y => BridgeExtensions.logY2 n1 η Ybar (f1 y) (f2 y) (Y1 y) (Y2 y))
      ybar := by
  have hn2 : 0 < 1 - n1 := by linarith
  have he : (fun y => BridgeExtensions.logY2 n1 η Ybar (f1 y) (f2 y) (Y1 y) (Y2 y)) =
      fun y => ((η - 1) / η)⁻¹ * Real.log
        (n1 * Real.exp (1 * (η⁻¹ * f1 y + (η - 1) / η * Y1 y)) +
          (1 - n1) * Real.exp (1 * (η⁻¹ * f2 y + (η - 1) / η * Y2 y))) := by
    funext y
    rw [BridgeExtensions.logY2,
      TwoSectorWelfare.log_upperCES hn0 hn1 hη hη1 hY (f1 y) (f2 y) (Y1 y) (Y2 y) 1]
    simp [TwoSectorWelfare.lse, Fin.sum_univ_two]
  rw [he]
  refine contDiffAt_const.mul (ContDiffAt.log ?_ ?_)
  · exact (contDiffAt_const.mul (contDiffAt_const.mul ((contDiffAt_const.mul c1).add
      (contDiffAt_const.mul c3))).exp).add
      (contDiffAt_const.mul (contDiffAt_const.mul ((contDiffAt_const.mul c2).add
      (contDiffAt_const.mul c4))).exp)
  · positivity

omit [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.6, p. 703: the two-sector aggregate is `Ȳ` at the steady state,
`log(Y/Ȳ) = 0` when all log deviations vanish. -/
theorem logY2_zero {n1 η Ybar : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hY : 0 < Ybar) : BridgeExtensions.logY2 n1 η Ybar 0 0 0 0 = 0 := by
  rw [BridgeExtensions.logY2,
    TwoSectorWelfare.log_upperCES hn0 hn1 hη hη1 hY 0 0 0 0 1]
  simp [TwoSectorWelfare.lse, Fin.sum_univ_two]

/-- Woodford (2003), **Proposition 6.10**, (4.24)/(E.26): the Layer-B remainder of the
two-sector model, actual period utility minus
`t.i.p. − (ε²/2)·Ȳu_c·loss610(first-order solution)`. -/
noncomputable def rem610 {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (u v : ℝ × Ξ → ℝ) (n1 η θ Ybar σi ω : ℝ) (w1 w2 : ι → ℝ) (f1 f2 : ℝ) (yh1 yh2 : ι → ℝ)
    (xu xv1 xv2 : Ξ) (g q1 q2 gf q1f q2f df Yf Y1f Y2f : ℝ) (y1f y2f : ι → ℝ) (s : ℝ) : ℝ :=
  BridgeExtensions.periodU2 u v n1 η θ Ybar w1 w2 f1 f2 yh1 yh2 xu xv1 xv2 -
    ((BridgeExtensions.tip2 u v n1 Ybar xu xv1 xv2 + Ybar * BridgeExtensions.dY u (Ybar, 0) *
      TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 g q1 q2 (f2 - f1)
        (BridgeExtensions.tauAgg η⁻¹ n1 f1 f2)) -
      s ^ 2 / 2 * (Ybar * BridgeExtensions.dY u (Ybar, 0) *
        BridgeExtensions.loss610 σi ω θ⁻¹ η⁻¹ n1 gf q1f q2f df Yf Y1f Y2f (crossVar w1 y1f)
          (crossVar w2 y2f)))

/-- Woodford (2003), **Proposition 6.10**, (4.24)/(E.26), pp. 436, 703–705, ALONG THE
EQUILIBRIUM on the i.i.d. probability space: let the decision vector carry, through `C²`
readouts vanishing at `ȳ`, the sectoral log outputs `ŷ_j(i)`, the sectoral preference shocks
`φ̂_j` (normalised, `hnorm`, a model equation), the composite disturbances `g, q_j` (defined by
`hg`, `hq1`, `hq2`) and the shocks `ξ`. For the `C²` equilibrium with amplitude `ε = σ` the
actual period utility is `t.i.p. − (ε²/2)·Ȳu_c·loss610(first-order solution) + O(ε³)`,
UNIFORMLY in the date and the path; the aggregates' smoothness is proved
(`contDiffAt_logYidx`, `contDiffAt_logY2`). -/
theorem prop610_measure {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    {n1 η θ : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1) (hθ : θ ≠ 1)
    {w1 w2 : ι → ℝ} (hw10 : ∀ i, 0 ≤ w1 i) (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i)
    (hw21 : ∑ i, w2 i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {Ybar σi ω : ℝ} (hY : 0 < Ybar) (hσω : σi + ω ≠ 0) (hηω : η⁻¹ + ω ≠ 0)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σi * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yh1R yh2R : Y → ι → ℝ} {f1R f2R gR q1R q2R : Y → ℝ} {xuR xv1R xv2R : Y → Ξ}
    (cy1 : ContDiffAt ℝ 2 yh1R ybar) (cy2 : ContDiffAt ℝ 2 yh2R ybar)
    (cf1 : ContDiffAt ℝ 2 f1R ybar) (cf2 : ContDiffAt ℝ 2 f2R ybar)
    (cg : ContDiffAt ℝ 2 gR ybar) (cq1 : ContDiffAt ℝ 2 q1R ybar) (cq2 : ContDiffAt ℝ 2 q2R ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (cxv1 : ContDiffAt ℝ 2 xv1R ybar)
    (cxv2 : ContDiffAt ℝ 2 xv2R ybar)
    (zy1 : yh1R ybar = 0) (zy2 : yh2R ybar = 0) (zf1 : f1R ybar = 0) (zf2 : f2R ybar = 0)
    (zg : gR ybar = 0) (zq1 : q1R ybar = 0) (zq2 : q2R ybar = 0) (zxu : xuR ybar = 0)
    (zxv1 : xv1R ybar = 0) (zxv2 : xv2R ybar = 0)
    (hnorm : ∀ y, n1 * Real.exp (f1R y) + (1 - n1) * Real.exp (f2R y) = 1)
    (hg : ∀ y, BridgeExtensions.dYXi u (Ybar, 0) (xuR y) =
      σi * BridgeExtensions.dY u (Ybar, 0) * gR y)
    (hq1 : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xv1R y) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q1R y))
    (hq2 : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xv2R y) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q2R y)) :
    UProc (𝓝 0) (fun ε t ω' => rem610 u v n1 η θ Ybar σi ω w1 w2
      (f1R (ypath ψ ybar ε t ω')) (f2R (ypath ψ ybar ε t ω')) (yh1R (ypath ψ ybar ε t ω'))
      (yh2R (ypath ψ ybar ε t ω')) (xuR (ypath ψ ybar ε t ω')) (xv1R (ypath ψ ybar ε t ω'))
      (xv2R (ypath ψ ybar ε t ω')) (gR (ypath ψ ybar ε t ω')) (q1R (ypath ψ ybar ε t ω'))
      (q2R (ypath ψ ybar ε t ω')) (fderiv ℝ gR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ q1R ybar (y1path ψ ybar t ω')) (fderiv ℝ q2R ybar (y1path ψ ybar t ω'))
      (fderiv ℝ (fun y => f2R y - f1R y) ybar (y1path ψ ybar t ω'))
      (fderiv ℝ (fun y => BridgeExtensions.logY2 n1 η Ybar (f1R y) (f2R y)
        (BridgeExtensions.logYidx w1 θ (yh1R y)) (BridgeExtensions.logYidx w2 θ (yh2R y)))
        ybar (y1path ψ ybar t ω'))
      (fderiv ℝ (fun y => BridgeExtensions.logYidx w1 θ (yh1R y)) ybar (y1path ψ ybar t ω'))
      (fderiv ℝ (fun y => BridgeExtensions.logYidx w2 θ (yh2R y)) ybar (y1path ψ ybar t ω'))
      (fderiv ℝ yh1R ybar (y1path ψ ybar t ω')) (fderiv ℝ yh2R ybar (y1path ψ ybar t ω')) ε)
      fun ε => ε ^ 3 := by
  have hs : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1)
      ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ)))) (𝓝 0) := tendsto_fst
  have cY1 := contDiffAt_logYidx hw11 θ cy1 zy1
  have cY2 := contDiffAt_logYidx hw21 θ cy2 zy2
  have zY1 : (fun y => BridgeExtensions.logYidx w1 θ (yh1R y)) ybar = 0 := by
    simp only [zy1]; exact logYidx_zero hw11 θ
  have zY2 : (fun y => BridgeExtensions.logYidx w2 θ (yh2R y)) ybar = 0 := by
    simp only [zy2]; exact logYidx_zero hw21 θ
  have cY := contDiffAt_logY2 hn0 hn1 hη hη1 hY cf1 cf2 cY1 cY2
  have zY : (fun y => BridgeExtensions.logY2 n1 η Ybar (f1R y) (f2R y)
      (BridgeExtensions.logYidx w1 θ (yh1R y)) (BridgeExtensions.logYidx w2 θ (yh2R y)))
      ybar = 0 := by
    simp only [zf1, zf2]
    rw [show BridgeExtensions.logYidx w1 θ (yh1R ybar) = 0 from zY1,
      show BridgeExtensions.logYidx w2 θ (yh2R ybar) = 0 from zY2]
    exact logY2_zero hn0 hn1 hη hη1 hY
  have cd : ContDiffAt ℝ 2 (fun y => f2R y - f1R y) ybar := cf2.sub cf1
  have zd : (fun y => f2R y - f1R y) ybar = 0 := by simp [zf1, zf2]
  exact BridgeExtensions.prop610_layerB hs hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 hu hv hY hσω
    hηω hucc hvy hvyy (fun b => hnorm _) (fun b => hg _) (fun b => hq1 _) (fun b => hq2 _)
    (readout_first hbase hψ2 cy1 zy1) (readout_first hbase hψ2 cy2 zy2)
    (readout_first hbase hψ2 cf1 zf1) (readout_first hbase hψ2 cf2 zf2)
    (readout_first hbase hψ2 cxu zxu) (readout_first hbase hψ2 cxv1 zxv1)
    (readout_first hbase hψ2 cxv2 zxv2)
    (readout_bdd ψ ybar gR) (readout_bdd ψ ybar q1R) (readout_bdd ψ ybar q2R)
    (readout_bdd ψ ybar _) (readout_bdd ψ ybar _) (readout_bdd ψ ybar _)
    (readout_bdd ψ ybar _) (readout_bdd ψ ybar yh1R) (readout_bdd ψ ybar yh2R)
    (readout_second hbase hψ2 cg zg) (readout_second hbase hψ2 cq1 zq1)
    (readout_second hbase hψ2 cq2 zq2) (readout_second hbase hψ2 cd zd)
    (readout_second hbase hψ2 cY zY) (readout_second hbase hψ2 cY1 zY1)
    (readout_second hbase hψ2 cY2 zY2) (readout_second hbase hψ2 cy1 zy1)
    (readout_second hbase hψ2 cy2 zy2)

end Woodford.StabilizationWelfare.SmoothInSigmaMeasureWelfare
