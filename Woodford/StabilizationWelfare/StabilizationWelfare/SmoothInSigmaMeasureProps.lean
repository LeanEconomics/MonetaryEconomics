/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasureWelfare

/-!
# Propositions 6.7–6.15 along the perturbation equilibrium on the probability space

Woodford (2003), *Interest and Prices*, Chapter 6, §4–§5 (pp. 420–463) and Appendix E.4–E.8.

`SmoothInSigmaMeasureWelfare` gives the readout bounds (`readout_first`, `readout_second`) and
Proposition 6.10/6.12 along the perturbation equilibrium on `(ℕ → ℝ, ν^ℕ)`. Here the remaining
Layer-B propositions are transported to the equilibrium: the cores of `BridgeExtensions` are
applied path by path (perfect-foresight expectation system on `Unit`, amplitudes and paths as
the index), and uniform-in-path orders survive integration (`integral_isBigO`).

The second-order states are PROVED along the equilibrium, not assumed: price dispersion is
`O(ε²)` because its first derivative vanishes through the Calvo law
(`dispersion_first_order_zero`), and `π̄ − π = O(ε²)` because it is the price-index discrepancy
of two `O(ε)` cross-sections (`disc_second_order`). Propositions 6.7/6.8 use the one-sided
expansion at satiation (`hleft`) with money demand a `C¹` function of output, the interest rate
and the demand shock.

## Main results

* `prop610_measure_discounted`: Proposition 6.10 as expected discounted utility (`mdsum_o`).
* Tools: `uproc_lift`, `uproc_mask`, `uproc_shift`, `uproc_shiftV`, `uproc_lift2`,
  `isBigO_mask2`, `eventually_bdd_comp`, `integral_isBigO`, `ypath_zero`, `hasDerivAt_ypath`.
* `dispersion_first_order_zero`, `discF`, `disc_second_order`: the second-order states.
* `rem614`/`prop614_measure`, `rem613`/`prop613_measure`, `rem611`/`prop611_measure`,
  `rem67`/`prop67_measure`, `rem68`/`prop68_measure`: Propositions 6.14, 6.13, 6.11, 6.7 and
  6.8 along the equilibrium, `E[remainder] = O(ε³)`.
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaMeasureProps

open MeasureTheory Filter Topology Asymptotics
open SmoothInSigmaMeasure (Hist adSub)
open SmoothInSigma (Bd pbar norm_apply_le)
open SmoothInSigmaMeasurePath (histOf)
open SmoothInSigmaMeasureWelfare (ypath y1path rem610 mdsum_o prop610_measure readout_first
  readout_second readout_bdd)
open BridgeExtensions (UProc)

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Woodford (2003), **Proposition 6.10**, (4.24)/(E.26), and (5.2) (**expected discounted
utility along the equilibrium**): under the hypotheses of `prop610_measure`, on the i.i.d.
probability space `(ℕ → ℝ, ν^ℕ)` of any law `ν`,
`∑ βᵗ E[U_t] = ∑ βᵗ E[t.i.p._t − (ε²/2)·Ȳu_c·loss610_t(first-order solution)] + O(ε³)`. -/
theorem prop610_measure_discounted (ν0 : ProbabilityMeasure ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
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
    (fun ε => ∑' t, β ^ t * ∫ ω', rem610 u v n1 η θ Ybar σi ω w1 w2
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
      (fderiv ℝ yh1R ybar (y1path ψ ybar t ω')) (fderiv ℝ yh2R ybar (y1path ψ ybar t ω')) ε
      ∂(ExpectationsMeasureIID.iidSystem ν0).μ) =O[𝓝 0] fun ε => ε ^ 3 :=
  mdsum_o _ hβ0 hβ1 (prop610_measure hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 hu hv hY hσω hηω
    hucc hvy hvyy hbase hψ2 cy1 cy2 cf1 cf2 cg cq1 cq2 cxu cxv1 cxv2 zy1 zy2 zf1 zf2 zg zq1 zq2
    zxu zxv1 zxv2 hnorm hg hq1 hq2)

/-! ## Tools: orders along the path, lifted to the amplitude–path index -/

/-- Woodford (2003), §2, p. 394: a uniform order along the path lifts to the index
`(ε, ω)` with a trivial state space (each path a perfect-foresight economy). -/
theorem uproc_lift {Ω E : Type} [Norm E] {X : ℝ → ℕ → Ω → E} {g : ℝ → ℝ}
    (h : UProc (𝓝 0) X g) :
    UProc ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) (fun a t (_ : Unit) => X a.1 t a.2)
      (fun a => g a.1) := by
  have ht : Tendsto (fun p : (ℝ × Ω) × (ℕ × Unit) => (p.1.1, (p.2.1, p.1.2)))
      (((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) ×ˢ (⊤ : Filter (ℕ × Unit)))
      ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × Ω))) :=
    (tendsto_fst.comp tendsto_fst).prodMk tendsto_top
  exact h.comp_tendsto ht

/-- Woodford (2003), §2, p. 394: changing a family away from small amplitudes does not affect a
uniform order. -/
theorem uproc_mask {A' Ω E : Type} [NormedAddCommGroup E] {l : Filter A'} {X : A' → ℕ → Ω → E}
    {g : A' → ℝ} (h : UProc l X g) {P : A' → Prop} (hP : ∀ᶠ a in l, P a)
    [DecidablePred P] : UProc l (fun a t ω => if P a then X a t ω else 0) g := by
  refine IsBigO.congr' h ?_ (Eventually.of_forall fun _ => rfl)
  have : ∀ᶠ p in l ×ˢ (⊤ : Filter (ℕ × Ω)), P p.1 := tendsto_fst.eventually hP
  filter_upwards [this] with p hp
  simp [hp]

/-- Woodford (2003), §2, p. 394: the lag of a uniformly small family (zero at date `0`) is
uniformly small. -/
theorem uproc_shift {A' Ω : Type} {l : Filter A'} {X : A' → ℕ → Ω → ℝ} {g : A' → ℝ}
    (h : UProc l X g) :
    UProc l (fun a t ω => match t with
      | 0 => 0
      | k + 1 => X a k ω) g := by
  obtain ⟨C, hC⟩ := BridgeExtensions.uniform_bound h
  refine IsBigO.of_bound (max C 0) ?_
  rw [Filter.prod_top, Filter.eventually_comap]
  filter_upwards [hC] with a ha q hq
  rcases q with ⟨a', _ | k, ω⟩
  · simp only [Real.norm_eq_abs, abs_zero]
    exact mul_nonneg (le_max_right _ _) (abs_nonneg _)
  · simp only at hq
    subst hq
    simp only [Real.norm_eq_abs]
    exact (ha (k, ω)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-- Woodford (2003), (5.2), p. 456 (**expectations of uniformly small pathwise quantities**): if
`F(ε, ω) = O(εᵏ)` uniformly in the path, then `E F(ε, ·) = O(εᵏ)` under any probability law. -/
theorem integral_isBigO {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : ℝ → Ω → ℝ} {k : ℕ}
    (h : (fun a : ℝ × Ω => F a.1 a.2) =O[(𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)] fun a => a.1 ^ k) :
    (fun ε => ∫ ω, F ε ω ∂μ) =O[𝓝 0] fun ε => ε ^ k := by
  obtain ⟨C, hC⟩ := BridgeExtensions.uniform_bound (f := fun a : ℝ × Ω => F a.1 a.2)
    (g := fun ε => ε ^ k) h
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with ε hε
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F ε) (C := C * |ε ^ k|)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hε ω)
  simpa [Real.norm_eq_abs] using this

/-! ## The equilibrium path as a function of the amplitude -/

/-- Woodford (2003), App. E.2: at zero amplitude the equilibrium is the steady state. -/
theorem ypath_zero {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar) (t : ℕ) (ω : ℕ → ℝ) :
    ypath ψ ybar 0 t ω = ybar := by
  simp only [ypath]
  rw [show ((ybar, (0 : ℝ), (0 : ℝ)) : Y × ℝ × ℝ) = pbar ybar from rfl, hbase]
  rfl

/-- Woodford (2003), App. E.2 (**the first-order solution is the derivative in the amplitude**):
`d/dε y_t(ε, ω)|_{ε=0} = y¹_t(ω)`. -/
theorem hasDerivAt_ypath {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hψ1 : DifferentiableAt ℝ ψ (pbar ybar)) (t : ℕ) (ω : ℕ → ℝ) :
    HasDerivAt (fun ε => ypath ψ ybar ε t ω) (y1path ψ ybar t ω) 0 := by
  set ev : adSub (R := Unit) Y →L[ℝ] Y :=
    (SmoothInSigma.evalL Y (t, histOf t ω)).comp (adSub (R := Unit) Y).subtypeL with hev
  have hγ : HasDerivAt (fun ε : ℝ => ((ybar, 0, ε) : Y × ℝ × ℝ)) ((0, 0, 1) : Y × ℝ × ℝ) 0 :=
    (hasDerivAt_const 0 ybar).prodMk ((hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id 0))
  have hψ' : HasFDerivAt ψ (fderiv ℝ ψ (pbar ybar)) ((ybar, (0 : ℝ), (0 : ℝ)) : Y × ℝ × ℝ) :=
    hψ1.hasFDerivAt
  have h := ev.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hψ'.comp_hasDerivAt (0 : ℝ) hγ)
  exact h

/-- Woodford (2003), §5, pp. 456–458 (**dispersion is of second order, from the Calvo law**):
if the dispersion `D(y)` and mean-price inflation `π̄(y)` are `C¹` readouts vanishing at `ȳ`, and
along the equilibrium (for small amplitudes) the Calvo law
`D(y_t) = α D(y_{t−1}) + (α/(1−α)) π̄(y_t)²` holds (with `y_{−1} = ȳ`), then the first-order
dispersion vanishes: `DD(ȳ) y¹_t = 0` at every date and on every path. -/
theorem dispersion_first_order_zero {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ1 : DifferentiableAt ℝ ψ (pbar ybar)) {DR pibR : Y → ℝ} {α : ℝ}
    (hD1 : DifferentiableAt ℝ DR ybar) (hp1 : DifferentiableAt ℝ pibR ybar)
    (zp : pibR ybar = 0)
    (hlaw : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      DR (ypath ψ ybar ε t ω) = α * DR (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω) + α / (1 - α) * pibR (ypath ψ ybar ε t ω) ^ 2) :
    ∀ t ω, fderiv ℝ DR ybar (y1path ψ ybar t ω) = 0 := by
  have hD0 : ∀ t ω, HasDerivAt (fun ε => DR (ypath ψ ybar ε t ω))
      (fderiv ℝ DR ybar (y1path ψ ybar t ω)) 0 := fun t ω => by
    have hD' : HasFDerivAt DR (fderiv ℝ DR ybar) (ypath ψ ybar 0 t ω) := by
      rw [ypath_zero hbase t ω]; exact hD1.hasFDerivAt
    exact hD'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_ypath hψ1 t ω)
  have hp0 : ∀ t ω, HasDerivAt (fun ε => pibR (ypath ψ ybar ε t ω) ^ 2) 0 0 := fun t ω => by
    have hp' : HasFDerivAt pibR (fderiv ℝ pibR ybar) (ypath ψ ybar 0 t ω) := by
      rw [ypath_zero hbase t ω]; exact hp1.hasFDerivAt
    have h2 := (hp'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_ypath hψ1 t ω)).pow 2
    convert h2 using 1
    · funext ε
      rfl
    · simp [ypath_zero hbase t ω, zp]
  intro t
  induction t with
  | zero =>
    intro ω
    have hR : HasDerivAt (fun ε => α * DR (match 0 with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω) + α / (1 - α) * pibR (ypath ψ ybar ε 0 ω) ^ 2) 0 0 := by
      have h := (hasDerivAt_const (0 : ℝ) (α * DR ybar)).add ((hp0 0 ω).const_mul (α / (1 - α)))
      convert h using 1
      ring
    exact (hD0 0 ω).unique (hR.congr_of_eventuallyEq (hlaw.mono fun ε h => h 0 ω))
  | succ k ih =>
    intro ω
    have hR : HasDerivAt (fun ε => α * DR (match k + 1 with
        | 0 => ybar
        | j + 1 => ypath ψ ybar ε j ω) + α / (1 - α) * pibR (ypath ψ ybar ε (k + 1) ω) ^ 2)
        0 0 := by
      have h := ((hD0 k ω).const_mul α).add ((hp0 (k + 1) ω).const_mul (α / (1 - α)))
      convert h using 1
      rw [ih ω]
      ring
    exact (hD0 (k + 1) ω).unique (hR.congr_of_eventuallyEq (hlaw.mono fun ε h => h (k + 1) ω))

/-- Woodford (2003), §2, p. 394: the lag of a uniformly small vector family (zero at date `0`)
is uniformly small. -/
theorem uproc_shiftV {A' Ω E : Type} [NormedAddCommGroup E] {l : Filter A'}
    {X : A' → ℕ → Ω → E} {g : A' → ℝ} (h : UProc l X g) :
    UProc l (fun a t ω => match t with
      | 0 => 0
      | k + 1 => X a k ω) g := by
  obtain ⟨C, hC⟩ := h.bound
  rw [Filter.prod_top, Filter.eventually_comap] at hC
  refine IsBigO.of_bound (max C 0) ?_
  rw [Filter.prod_top, Filter.eventually_comap]
  filter_upwards [hC] with a ha q hq
  rcases q with ⟨a', _ | k, ω⟩
  · simp only [norm_zero]
    exact mul_nonneg (le_max_right _ _) (norm_nonneg _)
  · simp only at hq
    subst hq
    exact (ha (a', k, ω) rfl).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- Woodford (2003), Prop. 6.3 (App. E.2, p. 695): the discrepancy between mean-price and index
inflation, as a function of the log price cross-sections `z₁` (now) and `z₂` (before). -/
noncomputable def discF {ι : Type} [Fintype ι] (wt : ι → ℝ) (θ : ℝ) (z1 z2 : ι → ℝ) : ℝ :=
  (ExpLogCES.crossMean wt z1 - ExpLogCES.crossMean wt z2) -
    (Real.log (ExpLogCES.cesIndex wt (1 - θ) (fun i => Real.exp (z1 i))) -
      Real.log (ExpLogCES.cesIndex wt (1 - θ) (fun i => Real.exp (z2 i))))

/-- Woodford (2003), Prop. 6.3 and (5.2)–(5.3) (**`π̄ − π` is of second order along the
equilibrium**): if relative prices `rp(y)` and inflation `π(y)` are `C²` readouts vanishing at
`ȳ`, and along the equilibrium `π̄_t − π_t` is the price-index discrepancy of the log price
cross-sections `rp(y_t) + π(y_t)` and `rp(y_{t−1})` (`y_{−1} = ȳ`), then
`π̄ − π = O(ε²)` uniformly in the date and the path. -/
theorem disc_second_order {ι : Type} [Fintype ι] {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i)
    (hw1 : ∑ i, wt i = 1) {θ : ℝ} (hθ : θ ≠ 1) {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    {ybar : Y} (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) {rpR : Y → ι → ℝ} {inflR pibR : Y → ℝ}
    (crp : ContDiffAt ℝ 2 rpR ybar) (ci : ContDiffAt ℝ 2 inflR ybar) (zrp : rpR ybar = 0)
    (zi : inflR ybar = 0)
    (hdisc : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      pibR (ypath ψ ybar ε t ω) - inflR (ypath ψ ybar ε t ω) =
        discF wt θ (fun i => rpR (ypath ψ ybar ε t ω) i + inflR (ypath ψ ybar ε t ω))
          (rpR (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω))) :
    UProc (𝓝 0) (fun ε t ω => pibR (ypath ψ ybar ε t ω) - inflR (ypath ψ ybar ε t ω))
      fun ε => ε ^ 2 := by
  set L := (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ))) with hL
  have hs : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1) L (𝓝 0) := tendsto_fst
  have cz : ContDiffAt ℝ 2 (fun y => fun i => rpR y i + inflR y) ybar :=
    contDiffAt_pi.2 fun i => (contDiffAt_pi.1 crp i).add ci
  have zz : (fun y => fun i => rpR y i + inflR y) ybar = 0 := by
    funext i; simp [zrp, zi]
  have h1 : UProc (𝓝 0) (fun ε t ω => fun i => rpR (ypath ψ ybar ε t ω) i +
      inflR (ypath ψ ybar ε t ω)) fun ε => ε ^ 1 := readout_first hbase hψ2 cz zz
  have h2' : UProc (𝓝 0) (fun ε t ω => rpR (ypath ψ ybar ε t ω)) fun ε => ε ^ 1 :=
    readout_first hbase hψ2 crp zrp
  have h2 : UProc (𝓝 0) (fun ε t ω => rpR (match t with
      | 0 => ybar
      | k + 1 => ypath ψ ybar ε k ω)) fun ε => ε ^ 1 := by
    refine (uproc_shiftV h2').congr_left fun b => ?_
    rcases b with ⟨ε, _ | k, ω⟩
    · simp [zrp]
    · rfl
  have hz1 : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => fun i => rpR (ypath ψ ybar b.1 b.2.1 b.2.2) i +
      inflR (ypath ψ ybar b.1 b.2.1 b.2.2)) =O[L] fun b => b.1 ^ 1 := h1
  have hz2 : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => rpR (match b.2.1 with
      | 0 => ybar
      | k + 1 => ypath ψ ybar b.1 k b.2.2)) =O[L] fun b => b.1 ^ 1 := h2
  have hT : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) =>
      ((fun i => rpR (ypath ψ ybar b.1 b.2.1 b.2.2) i + inflR (ypath ψ ybar b.1 b.2.1 b.2.2)),
        rpR (match b.2.1 with
          | 0 => ybar
          | k + 1 => ypath ψ ybar b.1 k b.2.2))) L
      (𝓝 ((fun _ => (0 : ℝ)), (fun _ => (0 : ℝ)))) :=
    (BridgeExtensions.tendsto_of_o_one hs hz1).prodMk_nhds
      (BridgeExtensions.tendsto_of_o_one hs hz2)
  have hE := (Links.CES.eDisc_isBigO hw0 hw1 hθ 0).comp_tendsto hT
  have a1 : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => ‖(fun i => rpR (ypath ψ ybar b.1 b.2.1 b.2.2) i +
      inflR (ypath ψ ybar b.1 b.2.1 b.2.2))‖ ^ 2) =O[L] fun b => b.1 ^ 2 :=
    (hz1.norm_left.pow 2).congr_right fun b => by ring
  have a2 : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => ‖rpR (match b.2.1 with
      | 0 => ybar
      | k + 1 => ypath ψ ybar b.1 k b.2.2)‖ ^ 2) =O[L] fun b => b.1 ^ 2 :=
    (hz2.norm_left.pow 2).congr_right fun b => by ring
  have hsq := a1.add a2
  have hsq' : (fun b : ℝ × (ℕ × (ℕ → ℝ)) =>
      ‖(fun i => rpR (ypath ψ ybar b.1 b.2.1 b.2.2) i + inflR (ypath ψ ybar b.1 b.2.1 b.2.2)) -
        fun _ : ι => (0 : ℝ)‖ ^ 2 + ‖rpR (match b.2.1 with
          | 0 => ybar
          | k + 1 => ypath ψ ybar b.1 k b.2.2) - fun _ : ι => (0 : ℝ)‖ ^ 2) =O[L]
      fun b => b.1 ^ 2 := by
    refine hsq.congr_left fun b => ?_
    rw [show (fun _ : ι => (0 : ℝ)) = 0 from rfl, sub_zero, sub_zero]
  refine (hE.trans hsq').congr' ?_ (Eventually.of_forall fun _ => rfl)
  have : ∀ᶠ b in L, ∀ t ω, pibR (ypath ψ ybar b.1 t ω) - inflR (ypath ψ ybar b.1 t ω) =
      discF wt θ (fun i => rpR (ypath ψ ybar b.1 t ω) i + inflR (ypath ψ ybar b.1 t ω))
        (rpR (match t with
          | 0 => ybar
          | k + 1 => ypath ψ ybar b.1 k ω)) := tendsto_fst.eventually hdisc
  filter_upwards [this] with b hb
  rw [hb]
  rfl

/-! ## Proposition 6.14 along the equilibrium -/

open ExpLogCES (crossVar)

/-- Woodford (2003), **Proposition 6.14**, (5.2)–(5.3): the pathwise Layer-B remainder of the
large-distortion economy with readouts along a path (`yh` log outputs, `xu, xv` shocks,
`infl` inflation, `g, q` composite disturbances), zero initial dispersion:
`∑βᵗU_t − (−Ω ∑βᵗL_t + ∑βᵗ t.i.p._t)`. -/
noncomputable def rem614 {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (u v : ℝ × Ξ → ℝ) (wt : ι → ℝ) (α β θ ω σ Φ Ybar : ℝ) (yh : ℕ → ι → ℝ) (xu xv : ℕ → Ξ)
    (infl g q : ℕ → ℝ) : ℝ :=
  (∑' t, β ^ t * BridgeExtensions.periodU u v wt θ Ybar (yh t) (xu t) (xv t)) -
    (-LargeDistortions.OmegaW Ybar (BridgeExtensions.dY u (Ybar, 0))
        (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
      ∑' t, β ^ t * (infl t ^ 2 + LargeDistortions.lamYY (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
        BridgeExtensions.logYidx wt θ (yh t) ^ 2 -
        2 * LargeDistortions.gamT (Moments.calvoKappa α β ω θ σ) θ Φ ω σ (g t) (q t) *
          BridgeExtensions.logYidx wt θ (yh t)) +
      ∑' t, β ^ t * BridgeExtensions.tip51 u v Ybar (xu t) (xv t))

/-- Woodford (2003), **Proposition 6.14**, (5.2)–(5.3), p. 456, ALONG THE EQUILIBRIUM on the
i.i.d. probability space: let the decision vector carry, through `C²` readouts vanishing at `ȳ`,
log outputs `ŷ(i)`, the shocks `ξ_u, ξ_v`, inflation `π`, mean-price inflation `π̄`, relative
prices `rp(i)`, the composite disturbances `g, q`, and the dispersion `D` (as of the next date).
The model's equations are the composites (`hg`, `hq`), the dispersion as the variance of log
prices (`hV`), the Calvo law of dispersion (`hlaw`) and the mean-price/index discrepancy
(`hdisc`), along the equilibrium for small amplitudes. Then
`E[∑βᵗU_t] = E[−Ω∑βᵗL_t + ∑βᵗ t.i.p._t] + O(ε³)`: dispersion is `O(ε²)` because its first
derivative vanishes through the Calvo law (`dispersion_first_order_zero`), `π̄ − π = O(ε²)`
(`disc_second_order`), and `BridgeExtensions.prop614_layerB` applies to each path. -/
theorem prop614_measure [FiniteDimensional ℝ Y] (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type}
    [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {α β θ ω σ Φ Ybar : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1)
    (hω : 0 < ω) (hσ : 0 < σ) (hΦ : Φ < 1) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i)
    (hw1 : ∑ i, wt i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR rpR : Y → ι → ℝ} {xuR xvR : Y → Ξ} {gR qR inflR pibR DR : Y → ℝ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (crp : ContDiffAt ℝ 2 rpR ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (cxv : ContDiffAt ℝ 2 xvR ybar)
    (cg : ContDiffAt ℝ 2 gR ybar) (cq : ContDiffAt ℝ 2 qR ybar)
    (ci : ContDiffAt ℝ 2 inflR ybar) (cp : ContDiffAt ℝ 2 pibR ybar)
    (cD : ContDiffAt ℝ 2 DR ybar)
    (zyh : yhR ybar = 0) (zrp : rpR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (zg : gR ybar = 0) (zq : qR ybar = 0) (zi : inflR ybar = 0) (zp : pibR ybar = 0)
    (zD : DR ybar = 0)
    (hg : ∀ y, BridgeExtensions.dYXi u (Ybar, 0) (xuR y) =
      σ * BridgeExtensions.dY u (Ybar, 0) * gR y)
    (hq : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xvR y) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * qR y))
    (hV : ∀ y, crossVar wt (yhR y) = θ ^ 2 * DR y)
    (hlaw : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      DR (ypath ψ ybar ε t ω) = α * DR (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω) + α / (1 - α) * pibR (ypath ψ ybar ε t ω) ^ 2)
    (hdisc : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      pibR (ypath ψ ybar ε t ω) - inflR (ypath ψ ybar ε t ω) =
        discF wt θ (fun i => rpR (ypath ψ ybar ε t ω) i + inflR (ypath ψ ybar ε t ω))
          (rpR (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω))) :
    (fun ε => ∫ ω', rem614 u v wt α β θ ω σ Φ Ybar (fun t => yhR (ypath ψ ybar ε t ω'))
      (fun t => xuR (ypath ψ ybar ε t ω')) (fun t => xvR (ypath ψ ybar ε t ω'))
      (fun t => inflR (ypath ψ ybar ε t ω')) (fun t => gR (ypath ψ ybar ε t ω'))
      (fun t => qR (ypath ψ ybar ε t ω')) ∂(ExpectationsMeasureIID.iidSystem ν0).μ)
      =O[𝓝 0] fun ε => ε ^ 3 := by
  have hψ1 : DifferentiableAt ℝ ψ (pbar ybar) := hψ2.differentiableAt (by norm_num)
  -- the first derivative of the dispersion vanishes, so dispersion is of second order
  have hD1 := dispersion_first_order_zero hbase hψ1 (cD.differentiableAt (by norm_num))
    (cp.differentiableAt (by norm_num)) zp hlaw
  have hDO : UProc (𝓝 0) (fun ε t ω => DR (ypath ψ ybar ε t ω)) fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cD zD).congr_left fun b => ?_
    simp only [hD1, smul_zero, sub_zero]
  have hDO' := uproc_shift hDO
  have hpO := disc_second_order hw0 hw1 hθ1 hbase hψ2 crp ci zrp zi hdisc
  -- a small amplitude where the model equations hold
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 (hlaw.and hdisc)
  set P : ℝ × (ℕ → ℝ) → Prop := fun a => dist a.1 0 < ρ with hPd
  have hP : ∀ᶠ a in (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ)), P a :=
    tendsto_fst.eventually (Metric.ball_mem_nhds (0 : ℝ) hρ)
  set yh' : ℝ × (ℕ → ℝ) → ℕ → Unit → ι → ℝ := fun a t _ =>
    if P a then yhR (ypath ψ ybar a.1 t a.2) else 0 with hyh'
  set xu' : ℝ × (ℕ → ℝ) → ℕ → Unit → Ξ := fun a t _ =>
    if P a then xuR (ypath ψ ybar a.1 t a.2) else 0 with hxu'
  set xv' : ℝ × (ℕ → ℝ) → ℕ → Unit → Ξ := fun a t _ =>
    if P a then xvR (ypath ψ ybar a.1 t a.2) else 0 with hxv'
  set g' : ℝ × (ℕ → ℝ) → ℕ → Unit → ℝ := fun a t _ =>
    if P a then gR (ypath ψ ybar a.1 t a.2) else 0 with hg'
  set q' : ℝ × (ℕ → ℝ) → ℕ → Unit → ℝ := fun a t _ =>
    if P a then qR (ypath ψ ybar a.1 t a.2) else 0 with hq'
  set i' : ℝ × (ℕ → ℝ) → ℕ → Unit → ℝ := fun a t _ =>
    if P a then inflR (ypath ψ ybar a.1 t a.2) else 0 with hi'
  set p' : ℝ × (ℕ → ℝ) → ℕ → Unit → ℝ := fun a t _ =>
    if P a then pibR (ypath ψ ybar a.1 t a.2) else 0 with hp'
  set D' : ℝ × (ℕ → ℝ) → ℕ → Unit → ℝ := fun a t _ =>
    if P a then (match t with
      | 0 => 0
      | k + 1 => DR (ypath ψ ybar a.1 k a.2)) else 0 with hD'
  have lift1 : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : Y → E},
      ContDiffAt ℝ 2 R ybar → R ybar = 0 → UProc ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ)))
        (fun a t (_ : Unit) => if P a then R (ypath ψ ybar a.1 t a.2) else 0)
        fun a => a.1 ^ 1 := fun {E} _ _ {R} hR hR0 =>
    uproc_mask (uproc_lift (readout_first hbase hψ2 hR hR0)) hP
  have hpO' : UProc ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) (fun a t z => p' a t z - i' a t z)
      fun a => a.1 ^ 2 := by
    refine (uproc_mask (uproc_lift hpO) hP).congr_left fun b => ?_
    by_cases h : P b.1 <;> simp [hp', hi', h]
  have hDO'' : UProc ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) D' fun a => a.1 ^ 2 :=
    uproc_mask (uproc_lift hDO') hP
  have hgm : ∀ a t z, BridgeExtensions.dYXi u (Ybar, 0) (xu' a t z) =
      σ * BridgeExtensions.dY u (Ybar, 0) * g' a t z := fun a t z => by
    by_cases h : P a
    · simp only [hxu', hg', h, ↓reduceIte]; exact hg _
    · simp [hxu', hg', h, BridgeExtensions.dYXi, Prod.mk_zero_zero]
  have hqm : ∀ a t z, BridgeExtensions.dYXi v (Ybar, 0) (xv' a t z) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q' a t z) := fun a t z => by
    by_cases h : P a
    · simp only [hxv', hq', h, ↓reduceIte]; exact hq _
    · simp [hxv', hq', h, BridgeExtensions.dYXi, Prod.mk_zero_zero]
  have hVm : ∀ a t, (fun z => crossVar wt (yh' a t z)) = θ ^ 2 • D' a (t + 1) := fun a t => by
    funext z
    by_cases h : P a
    · simp only [hyh', hD', h, ↓reduceIte, Pi.smul_apply, smul_eq_mul]; exact hV _
    · simp [hyh', hD', h, crossVar, ExpLogCES.crossMean]
  have hDm : ∀ a t, D' a (t + 1) = α • D' a t + (α / (1 - α)) • p' a t ^ 2 := fun a t => by
    funext z
    by_cases h : P a
    · have hl := (hρs h).1 t a.2
      cases t with
      | zero =>
        simp only [hD', hp', h, ↓reduceIte, Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
        rw [hl, zD]
      | succ k =>
        simp only [hD', hp', h, ↓reduceIte, Pi.add_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
        exact hl
    · simp [hD', hp', h]
  have hcore := BridgeExtensions.prop614_layerB perfectForesight hα0 hα1 hβ0 hβ1 hθ hθ1 hω hσ hΦ
    (l := (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) (e := fun a => a.1) tendsto_fst hw0 hw1 hu hv
    hucc hvy hvyy (lift1 cyh zyh) (lift1 cxu zxu) (lift1 cxv zxv) (lift1 cg zg) (lift1 cq zq)
    (lift1 ci zi) hpO' hDO'' hgm hqm hVm hDm ()
  refine integral_isBigO _ (hcore.congr' ?_ (Eventually.of_forall fun _ => rfl))
  filter_upwards [hP] with a ha
  simp only [Sequences.dsum, perfectForesight, LinearMap.id_apply, hD', ha, ↓reduceIte,
    LargeDistortions.loss614, rem614, mul_zero, sub_zero]

/-! ## Tools for the pathwise sequence statements (Propositions 6.8, 6.11, 6.13) -/

/-- Woodford (2003), §2, p. 394: a uniform order along the path, re-indexed by
`((ε, ω), t)` for the sequence statements of Layer B. -/
theorem uproc_lift2 {Ω E : Type} [Norm E] {X : ℝ → ℕ → Ω → E} {g : ℝ → ℝ}
    (h : UProc (𝓝 0) X g) :
    (fun b : (ℝ × Ω) × ℕ => X b.1.1 b.2 b.1.2) =O[((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) ×ˢ
      (⊤ : Filter ℕ)] fun b => g b.1.1 := by
  have ht : Tendsto (fun b : (ℝ × Ω) × ℕ => (b.1.1, (b.2, b.1.2)))
      (((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) ×ˢ (⊤ : Filter ℕ))
      ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × Ω))) :=
    (tendsto_fst.comp tendsto_fst).prodMk tendsto_top
  exact h.comp_tendsto ht

/-- Woodford (2003), §2, p. 394: a masked family keeps a uniform order on `((ε, ω), t)`. -/
theorem isBigO_mask2 {Ω E : Type} [NormedAddCommGroup E] {X : (ℝ × Ω) × ℕ → E}
    {g : (ℝ × Ω) × ℕ → ℝ}
    (h : X =O[((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) ×ˢ (⊤ : Filter ℕ)] g) {P : ℝ × Ω → Prop}
    [DecidablePred P] (hP : ∀ᶠ a in (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω), P a) :
    (fun b => if P b.1 then X b else 0) =O[((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) ×ˢ
      (⊤ : Filter ℕ)] g := by
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [tendsto_fst.eventually hP] with b hb
  simp [hb]

/-- Woodford (2003), §2, p. 394 (**continuous functions of uniformly small readouts are uniformly
bounded**): if `X = O(ε)` uniformly in `(ω, t)` and `φ` is continuous at `0`, then
`|φ(X)| ≤ M` for all dates, for all small amplitudes and all paths. -/
theorem eventually_bdd_comp {Ω V : Type} [NormedAddCommGroup V] {X : (ℝ × Ω) × ℕ → V}
    (hX : X =O[((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) ×ˢ (⊤ : Filter ℕ)] fun b => b.1.1 ^ 1)
    {φ : V → ℝ} (hφ : ContinuousAt φ 0) :
    ∃ M, ∀ᶠ a in (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω), ∀ t, |φ (X (a, t))| ≤ M := by
  have hs : Tendsto (fun b : (ℝ × Ω) × ℕ => b.1.1)
      (((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter Ω)) ×ˢ (⊤ : Filter ℕ)) (𝓝 0) :=
    tendsto_fst.comp tendsto_fst
  have hT := hφ.tendsto.comp (BridgeExtensions.tendsto_of_o_one hs hX)
  have hev := hT.eventually (Metric.ball_mem_nhds (φ 0) one_pos)
  refine ⟨|φ 0| + 1, ?_⟩
  rw [Filter.prod_top, Filter.eventually_comap] at hev
  filter_upwards [hev] with a ha t
  have := ha (a, t) rfl
  simp only [Function.comp_apply, Real.dist_eq] at this
  have h2 := abs_sub_abs_le_abs_sub (φ (X (a, t))) (φ 0)
  linarith

/-- Woodford (2003), App. E, p. 693: the cross-sectional variance of a `C²` readout is `C²`. -/
theorem contDiffAt_crossVar {ι : Type} [Fintype ι] (w : ι → ℝ) {R : Y → ι → ℝ} {ybar : Y}
    (h : ContDiffAt ℝ 2 R ybar) : ContDiffAt ℝ 2 (fun y => crossVar w (R y)) ybar := by
  unfold crossVar ExpLogCES.crossMean
  exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (((contDiffAt_pi.1 h i).sub
    (ContDiffAt.sum fun j _ => contDiffAt_const.mul (contDiffAt_pi.1 h j))).pow 2)

omit [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E, p. 693: the cross-sectional variance vanishes at a zero
cross-section. -/
theorem crossVar_zero {ι : Type} [Fintype ι] (w : ι → ℝ) : crossVar w (0 : ι → ℝ) = 0 := by
  simp [crossVar, ExpLogCES.crossMean]

/-- Woodford (2003), (E.2), p. 692: the policy-independent terms `t.i.p.` of the expansion are
continuous in the shocks. -/
theorem continuous_tip12 {Ξ : Type} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (u v : ℝ × Ξ → ℝ) (Ybar Hbar : ℝ) :
    Continuous fun x : Ξ × Ξ => BridgeExtensions.tip12 u v Ybar Hbar x.1 x.2 := by
  have h0 : ∀ (z : ℝ × Ξ) (U : ℝ × Ξ → ℝ), Continuous fun ξ : Ξ =>
      BridgeExtensions.dXi U z ξ := fun z U =>
    (fderiv ℝ U z).continuous.comp (continuous_const.prodMk continuous_id)
  have h1 : ∀ (z : ℝ × Ξ) (U : ℝ × Ξ → ℝ), Continuous fun ξ : Ξ =>
      BridgeExtensions.dXiXi U z ξ := fun z U => by
    have hc : Continuous fun ξ : Ξ => ((0 : ℝ), ξ) := continuous_const.prodMk continuous_id
    exact ((fderiv ℝ (fderiv ℝ U) z).continuous.comp hc).clm_apply hc
  unfold BridgeExtensions.tip12
  exact ((continuous_const.add ((h0 _ u).comp continuous_fst)).add
    (((h1 _ u).comp continuous_fst).div_const 2)).sub
    ((continuous_const.add ((h0 _ v).comp continuous_snd)).add
    (((h1 _ v).comp continuous_snd).div_const 2))

/-! ## Proposition 6.13 along the equilibrium -/

/-- Woodford (2003), **Proposition 6.13**, (4.29): the pathwise remainder of the sticky price
and wage economy along a path of readouts, zero initial dispersions:
`∑βᵗU_t − (−(K/2)D ∑βᵗ L_t + ∑βᵗ t.i.p._t)` with `L` the loss (4.29). -/
noncomputable def rem613 {ι J Ξ : Type} [Fintype ι] [Fintype J] [NormedAddCommGroup Ξ]
    [NormedSpace ℝ Ξ] (u v : ℝ × Ξ → ℝ) (w : ι → ℝ) (ωt : J → ℝ) (θp θw Ybar Hbar σi ω ν ωp φh
    β αp αw : ℝ) (G : ℝ → ℝ) (a : ℕ → ℝ) (yh : ℕ → ι → ℝ) (lw : ℕ → J → ℝ) (xu xv : ℕ → Ξ)
    (g hb infl winfl : ℕ → ℝ) : ℝ :=
  (∑' t, β ^ t * BridgeExtensions.periodU12 u v w ωt θp θw Ybar Hbar G (a t) (yh t) (lw t)
      (xu t) (xv t)) -
    (-(Ybar * BridgeExtensions.dY u (Ybar, 0) / 2 * StickyWageWelfare.Dsum θp
        (Moments.calvoXi αp β ωp θp) θw φh (Moments.calvoXi αw β ν θw)) *
      ∑' t, β ^ t * StickyWageWelfare.loss429
        (StickyWageWelfare.lamP θp (Moments.calvoXi αp β ωp θp) θw φh (Moments.calvoXi αw β ν θw))
        (StickyWageWelfare.lamW θp (Moments.calvoXi αp β ωp θp) θw φh (Moments.calvoXi αw β ν θw))
        (StickyWageWelfare.lamX613 σi ω θp (Moments.calvoXi αp β ωp θp) θw φh
          (Moments.calvoXi αw β ν θw)) (infl t) (winfl t)
        (BridgeExtensions.logYidx w θp (yh t) - StickyWageWelfare.natY612 σi ω ν (g t) (a t) (hb t))
        0 +
      ∑' t, β ^ t * (BridgeExtensions.tip12 u v Ybar Hbar (xu t) (xv t) +
        Ybar * BridgeExtensions.dY u (Ybar, 0) * StickyWageWelfare.tip612 σi ω ν 0 (g t) (a t)
          (hb t)))

/-- Woodford (2003), **Proposition 6.13**, (4.29), p. 445, ALONG THE EQUILIBRIUM on the i.i.d.
probability space: under the hypotheses of `SmoothInSigmaMeasureWelfare.prop612_measure`, with
in addition price and wage inflation `π, π_w`, mean-price and mean-wage inflation `π̄, π̄_w`
and relative prices and wages as `C²` readouts vanishing at `ȳ`, and the model's equations along
the equilibrium (for small amplitudes): the exact Calvo laws of price and wage dispersion
(`Δ_p = var_i ŷ/θ_p²`, `Δ_w = var_j lw`) and the mean/index discrepancies of prices and wages,
`E[∑βᵗU_t] = E[−(K/2)D∑βᵗL_t + ∑βᵗ t.i.p._t] + O(ε³)` with `L` the loss (4.29) on the actual
path. Dispersions are `O(ε²)` (first derivative vanishes through the Calvo laws) and
`π̄ − π, π̄_w − π_w = O(ε²)` (Prop. 6.3). -/
theorem prop613_measure [FiniteDimensional ℝ Y] (ν0 : ProbabilityMeasure ℝ) {ι J Ξ : Type}
    [Fintype ι] [Fintype J] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j)
    (hωt1 : ∑ j, ωt j = 1) {θp θw : ℝ} (hθp : 0 < θp) (hθp1 : θp ≠ 1) (hθw : 0 < θw)
    (hθw1 : θw ≠ 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {σi ω ν ωp φh Ybar Hbar β αp αw : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : 0 < φh) (hσω : 0 < σi + ω) (hωθ : 0 < 1 + ωp * θp)
    (hνθ : 0 < 1 + ν * θw) (hap0 : 0 < αp) (hap1 : αp < 1) (haw0 : 0 < αw) (haw1 : αw < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σi * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvhh : BridgeExtensions.dYY v (Hbar, 0) = ν * BridgeExtensions.dY v (Hbar, 0) / Hbar)
    (hss : Hbar * BridgeExtensions.dY v (Hbar, 0) * φh = Ybar * BridgeExtensions.dY u (Ybar, 0))
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR rpR : Y → ι → ℝ} {lwR rwR : Y → J → ℝ} {aR gR hbR inflR winflR pbR wbR : Y → ℝ}
    {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (crp : ContDiffAt ℝ 2 rpR ybar)
    (clw : ContDiffAt ℝ 2 lwR ybar) (crw : ContDiffAt ℝ 2 rwR ybar)
    (ca : ContDiffAt ℝ 2 aR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (chb : ContDiffAt ℝ 2 hbR ybar)
    (ci : ContDiffAt ℝ 2 inflR ybar) (cwi : ContDiffAt ℝ 2 winflR ybar)
    (cpb : ContDiffAt ℝ 2 pbR ybar) (cwb : ContDiffAt ℝ 2 wbR ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zrp : rpR ybar = 0) (zlw : lwR ybar = 0) (zrw : rwR ybar = 0)
    (za : aR ybar = 0) (zg : gR ybar = 0) (zhb : hbR ybar = 0) (zi : inflR ybar = 0)
    (zwi : winflR ybar = 0) (zpb : pbR ybar = 0) (zwb : wbR ybar = 0) (zxu : xuR ybar = 0)
    (zxv : xvR ybar = 0)
    (hg : ∀ y, BridgeExtensions.dYXi u (Ybar, 0) (xuR y) =
      σi * BridgeExtensions.dY u (Ybar, 0) * gR y)
    (hhb : ∀ y, BridgeExtensions.dYXi v (Hbar, 0) (xvR y) =
      -(ν * BridgeExtensions.dY v (Hbar, 0) * hbR y))
    (hlawp : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      crossVar w (yhR (ypath ψ ybar ε t ω)) / θp ^ 2 = αp * (crossVar w (yhR (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω)) / θp ^ 2) + αp / (1 - αp) * pbR (ypath ψ ybar ε t ω) ^ 2)
    (hlaww : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      crossVar ωt (lwR (ypath ψ ybar ε t ω)) = αw * crossVar ωt (lwR (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω)) + αw / (1 - αw) * wbR (ypath ψ ybar ε t ω) ^ 2)
    (hdiscp : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      pbR (ypath ψ ybar ε t ω) - inflR (ypath ψ ybar ε t ω) =
        discF w θp (fun i => rpR (ypath ψ ybar ε t ω) i + inflR (ypath ψ ybar ε t ω))
          (rpR (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω)))
    (hdiscw : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω,
      wbR (ypath ψ ybar ε t ω) - winflR (ypath ψ ybar ε t ω) =
        discF ωt θw (fun j => rwR (ypath ψ ybar ε t ω) j + winflR (ypath ψ ybar ε t ω))
          (rwR (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω))) :
    (fun ε => ∫ ω', rem613 u v w ωt θp θw Ybar Hbar σi ω ν ωp φh β αp αw G
      (fun t => aR (ypath ψ ybar ε t ω')) (fun t => yhR (ypath ψ ybar ε t ω'))
      (fun t => lwR (ypath ψ ybar ε t ω')) (fun t => xuR (ypath ψ ybar ε t ω'))
      (fun t => xvR (ypath ψ ybar ε t ω')) (fun t => gR (ypath ψ ybar ε t ω'))
      (fun t => hbR (ypath ψ ybar ε t ω')) (fun t => inflR (ypath ψ ybar ε t ω'))
      (fun t => winflR (ypath ψ ybar ε t ω')) ∂(ExpectationsMeasureIID.iidSystem ν0).μ)
      =O[𝓝 0] fun ε => ε ^ 3 := by
  classical
  have hψ1 : DifferentiableAt ℝ ψ (pbar ybar) := hψ2.differentiableAt (by norm_num)
  set L2 := ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) ×ˢ (⊤ : Filter ℕ) with hL2
  set K := Ybar * BridgeExtensions.dY u (Ybar, 0) with hK
  -- second-order dispersions
  have cDp : ContDiffAt ℝ 2 (fun y => crossVar w (yhR y) / θp ^ 2) ybar :=
    (contDiffAt_crossVar w cyh).div_const _
  have zDp : (fun y => crossVar w (yhR y) / θp ^ 2) ybar = 0 := by
    simp only [zyh, crossVar_zero, zero_div]
  have cDw : ContDiffAt ℝ 2 (fun y => crossVar ωt (lwR y)) ybar := contDiffAt_crossVar ωt clw
  have zDw : (fun y => crossVar ωt (lwR y)) ybar = 0 := by simp only [zlw, crossVar_zero]
  have hDp1 := dispersion_first_order_zero hbase hψ1 (cDp.differentiableAt (by norm_num))
    (cpb.differentiableAt (by norm_num)) zpb hlawp
  have hDw1 := dispersion_first_order_zero hbase hψ1 (cDw.differentiableAt (by norm_num))
    (cwb.differentiableAt (by norm_num)) zwb hlaww
  have hDpO : UProc (𝓝 0) (fun ε t ω => crossVar w (yhR (ypath ψ ybar ε t ω)) / θp ^ 2)
      fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cDp zDp).congr_left fun b => ?_
    simp only [hDp1, smul_zero, sub_zero]
  have hDwO : UProc (𝓝 0) (fun ε t ω => crossVar ωt (lwR (ypath ψ ybar ε t ω)))
      fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cDw zDw).congr_left fun b => ?_
    simp only [hDw1, smul_zero, sub_zero]
  have hpO := disc_second_order hw0 hw1 hθp1 hbase hψ2 crp ci zrp zi hdiscp
  have hwO := disc_second_order hωt0 hωt1 hθw1 hbase hψ2 crw cwi zrw zwi hdiscw
  -- the output gap readout
  have cx : ContDiffAt ℝ 2 (fun y => BridgeExtensions.logYidx w θp (yhR y) -
      StickyWageWelfare.natY612 σi ω ν (gR y) (aR y) (hbR y)) ybar := by
    unfold StickyWageWelfare.natY612
    exact (SmoothInSigmaMeasureWelfare.contDiffAt_logYidx hw1 θp cyh zyh).sub
      (((((contDiffAt_const.mul cg).add (contDiffAt_const.mul ca)).add
        (contDiffAt_const.mul chb))).div_const _)
  have zx : (fun y => BridgeExtensions.logYidx w θp (yhR y) -
      StickyWageWelfare.natY612 σi ω ν (gR y) (aR y) (hbR y)) ybar = 0 := by
    simp only [zyh, za, zg, zhb, SmoothInSigmaMeasureWelfare.logYidx_zero hw1,
      StickyWageWelfare.natY612]
    ring
  -- the t.i.p. are uniformly bounded for small amplitudes
  have cτ : ContDiffAt ℝ 2 (fun y => (xuR y, xvR y, gR y, aR y, hbR y)) ybar :=
    cxu.prodMk (cxv.prodMk (cg.prodMk (ca.prodMk chb)))
  have zτ : (fun y => (xuR y, xvR y, gR y, aR y, hbR y)) ybar = 0 := by
    simp [zxu, zxv, zg, za, zhb]
  obtain ⟨Mτ, hMτ⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cτ zτ))
    (φ := fun x => BridgeExtensions.tip12 u v Ybar Hbar x.1 x.2.1 +
      K * StickyWageWelfare.tip612 σi ω ν 0 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
    (((continuous_tip12 u v Ybar Hbar).comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).add (continuous_const.mul
      (by unfold StickyWageWelfare.tip612; fun_prop))).continuousAt
  -- a small amplitude where the model equations hold
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 (hlawp.and hlaww)
  set P : ℝ × (ℕ → ℝ) → Prop := fun a => dist a.1 0 < ρ ∧ ∀ t,
    |BridgeExtensions.tip12 u v Ybar Hbar (xuR (ypath ψ ybar a.1 t a.2))
      (xvR (ypath ψ ybar a.1 t a.2)) + K * StickyWageWelfare.tip612 σi ω ν 0
      (gR (ypath ψ ybar a.1 t a.2)) (aR (ypath ψ ybar a.1 t a.2))
      (hbR (ypath ψ ybar a.1 t a.2))| ≤ Mτ with hPd
  have hP : ∀ᶠ a in (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ)), P a :=
    (tendsto_fst.eventually (Metric.ball_mem_nhds (0 : ℝ) hρ)).and hMτ
  -- the masked processes on `(ε, ω)` and dates
  set W : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then BridgeExtensions.periodU12 u v w ωt θp
    θw Ybar Hbar G (aR (ypath ψ ybar a.1 t a.2)) (yhR (ypath ψ ybar a.1 t a.2))
    (lwR (ypath ψ ybar a.1 t a.2)) (xuR (ypath ψ ybar a.1 t a.2))
    (xvR (ypath ψ ybar a.1 t a.2)) else 0 with hW
  set τ : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    BridgeExtensions.tip12 u v Ybar Hbar (xuR (ypath ψ ybar a.1 t a.2))
      (xvR (ypath ψ ybar a.1 t a.2)) + K * StickyWageWelfare.tip612 σi ω ν 0
      (gR (ypath ψ ybar a.1 t a.2)) (aR (ypath ψ ybar a.1 t a.2))
      (hbR (ypath ψ ybar a.1 t a.2)) else 0 with hτd
  set x : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    BridgeExtensions.logYidx w θp (yhR (ypath ψ ybar a.1 t a.2)) -
      StickyWageWelfare.natY612 σi ω ν (gR (ypath ψ ybar a.1 t a.2))
        (aR (ypath ψ ybar a.1 t a.2)) (hbR (ypath ψ ybar a.1 t a.2)) else 0 with hxd
  set π : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    inflR (ypath ψ ybar a.1 t a.2) else 0 with hπd
  set πw : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    winflR (ypath ψ ybar a.1 t a.2) else 0 with hπwd
  set pb : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    pbR (ypath ψ ybar a.1 t a.2) else 0 with hpbd
  set wb : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    wbR (ypath ψ ybar a.1 t a.2) else 0 with hwbd
  set Δp : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    crossVar w (yhR (ypath ψ ybar a.1 t a.2)) / θp ^ 2 else 0 with hΔpd
  set Δw : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    crossVar ωt (lwR (ypath ψ ybar a.1 t a.2)) else 0 with hΔwd
  have hτb : ∀ a, Sequences.Bdd (τ a) := fun a => ⟨max Mτ 0, fun t => by
    by_cases h : P a
    · simp only [hτd, h, ↓reduceIte]; exact (h.2 t).trans (le_max_left _ _)
    · simp [hτd, h]⟩
  have hs2 : Tendsto (fun b : (ℝ × (ℕ → ℝ)) × ℕ => b.1.1) L2 (𝓝 0) :=
    tendsto_fst.comp tendsto_fst
  have h612 := BridgeExtensions.prop612_actual (L := L2) (s := fun b => b.1.1) hs2 hw0 hw1
    hωt0 hωt1 hθp.ne' hθp1 hθw1 hu hv hG hG0 hG1 hG2 hω hφ.ne' hσω.ne' hucc hvhh hss
    (yh := fun b => yhR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (lw := fun b => lwR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (a := fun b => aR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (g := fun b => gR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (hb := fun b => hbR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xu := fun b => xuR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xv := fun b => xvR (ypath ψ ybar b.1.1 b.2 b.1.2)) (fun b => hg _) (fun b => hhb _)
    (uproc_lift2 (readout_first hbase hψ2 cyh zyh)) (uproc_lift2 (readout_first hbase hψ2 clw zlw))
    (uproc_lift2 (readout_first hbase hψ2 ca za)) (uproc_lift2 (readout_first hbase hψ2 cg zg))
    (uproc_lift2 (readout_first hbase hψ2 chb zhb))
    (uproc_lift2 (readout_first hbase hψ2 cxu zxu))
    (uproc_lift2 (readout_first hbase hψ2 cxv zxv))
  have hPc : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => W p.1 p.2 - (τ p.1 p.2 - K / 2 *
      ((σi + ω) * (x p.1 p.2 - 0) ^ 2 + θp * (1 + ωp * θp) * Δp p.1 p.2 +
        θw / φh * (1 + ν * θw) * Δw p.1 p.2))) =O[L2] fun p => p.1.1 ^ 3 := by
    refine h612.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [tendsto_fst.eventually hP] with b hb
    simp only [hW, hτd, hxd, hΔpd, hΔwd, hb, ↓reduceIte, BridgeExtensions.loss612]
    ring
  have m1 : ∀ {R : Y → ℝ}, ContDiffAt ℝ 2 R ybar → R ybar = 0 →
      (fun p : (ℝ × (ℕ → ℝ)) × ℕ => if P p.1 then R (ypath ψ ybar p.1.1 p.2 p.1.2) else 0)
        =O[L2] fun p => p.1.1 ^ 1 := fun {R} hR hR0 =>
    isBigO_mask2 (uproc_lift2 (readout_first hbase hψ2 hR hR0)) hP
  have hx : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => x p.1 p.2 - 0) =O[L2] fun p => p.1.1 ^ 1 :=
    (m1 cx zx).congr_left fun p => by simp only [hxd, sub_zero]
  have hDp : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => Δp p.1 p.2) =O[L2] fun p => p.1.1 ^ 2 :=
    isBigO_mask2 (uproc_lift2 hDpO) hP
  have hDw : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => Δw p.1 p.2) =O[L2] fun p => p.1.1 ^ 2 :=
    isBigO_mask2 (uproc_lift2 hDwO) hP
  have hpp : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => pb p.1 p.2 - π p.1 p.2) =O[L2]
      fun p => p.1.1 ^ 2 := by
    refine (isBigO_mask2 (uproc_lift2 hpO) hP).congr_left fun p => ?_
    by_cases h : P p.1 <;> simp [hpbd, hπd, h]
  have hww : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => wb p.1 p.2 - πw p.1 p.2) =O[L2]
      fun p => p.1.1 ^ 2 := by
    refine (isBigO_mask2 (uproc_lift2 hwO) hP).congr_left fun p => ?_
    by_cases h : P p.1 <;> simp [hwbd, hπwd, h]
  have hp0 : ∀ a, Δp a 0 = αp * (fun _ => (0 : ℝ)) a + αp / (1 - αp) * pb a 0 ^ 2 := fun a => by
    by_cases h : P a
    · have hl := (hρs h.1).1 0 a.2
      simp only [hΔpd, hpbd, h, ↓reduceIte]
      rw [hl, zyh, crossVar_zero]
      ring
    · simp [hΔpd, hpbd, h]
  have hps : ∀ a t, Δp a (t + 1) = αp * Δp a t + αp / (1 - αp) * pb a (t + 1) ^ 2 :=
    fun a t => by
    by_cases h : P a
    · have hl := (hρs h.1).1 (t + 1) a.2
      simp only [hΔpd, hpbd, h, ↓reduceIte]
      exact hl
    · simp [hΔpd, hpbd, h]
  have hw0' : ∀ a, Δw a 0 = αw * (fun _ => (0 : ℝ)) a + αw / (1 - αw) * wb a 0 ^ 2 :=
    fun a => by
    by_cases h : P a
    · have hl := (hρs h.1).2 0 a.2
      simp only [hΔwd, hwbd, h, ↓reduceIte]
      rw [hl, zlw, crossVar_zero]
    · simp [hΔwd, hwbd, h]
  have hws : ∀ a t, Δw a (t + 1) = αw * Δw a t + αw / (1 - αw) * wb a (t + 1) ^ 2 :=
    fun a t => by
    by_cases h : P a
    · have hl := (hρs h.1).2 (t + 1) a.2
      simp only [hΔwd, hwbd, h, ↓reduceIte]
      exact hl
    · simp [hΔwd, hwbd, h]
  have hcore := BridgeExtensions.prop613_layerB (K := K) (xs := 0)
    (l := (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) (e := fun a => a.1) hap0 hap1 haw0 haw1 hβ0
    hβ1 hθp hθw hφ hωθ hνθ hσω tendsto_fst hτb hPc hx (m1 ci zi) (m1 cwi zwi) hDp hDw hpp hww
    hp0 hps hw0' hws
  refine integral_isBigO _ (hcore.congr' ?_ (Eventually.of_forall fun _ => rfl))
  filter_upwards [hP] with a ha
  simp only [hW, hτd, hxd, hπd, hπwd, ha, ↓reduceIte, rem613, mul_zero, zero_div, add_zero,
    sub_zero, hK]

/-! ## Proposition 6.11 along the equilibrium -/

/-- Woodford (2003), (E.26), p. 703: the policy-independent terms of the two-sector expansion
are continuous in the shocks. -/
theorem continuous_tip2 {Ξ : Type} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (u v : ℝ × Ξ → ℝ) (n1 Ybar : ℝ) :
    Continuous fun x : Ξ × Ξ × Ξ => BridgeExtensions.tip2 u v n1 Ybar x.1 x.2.1 x.2.2 := by
  have h0 : ∀ (z : ℝ × Ξ) (U : ℝ × Ξ → ℝ), Continuous fun ξ : Ξ =>
      BridgeExtensions.dXi U z ξ := fun z U =>
    (fderiv ℝ U z).continuous.comp (continuous_const.prodMk continuous_id)
  have h1 : ∀ (z : ℝ × Ξ) (U : ℝ × Ξ → ℝ), Continuous fun ξ : Ξ =>
      BridgeExtensions.dXiXi U z ξ := fun z U => by
    have hc : Continuous fun ξ : Ξ => ((0 : ℝ), ξ) := continuous_const.prodMk continuous_id
    exact ((fderiv ℝ (fderiv ℝ U) z).continuous.comp hc).clm_apply hc
  have hv : ∀ (f : Ξ × Ξ × Ξ → Ξ), Continuous f → Continuous fun x =>
      v (Ybar, 0) + BridgeExtensions.dXi v (Ybar, 0) (f x) +
        BridgeExtensions.dXiXi v (Ybar, 0) (f x) / 2 := fun f hf =>
    (continuous_const.add ((h0 _ v).comp hf)).add (((h1 _ v).comp hf).div_const 2)
  unfold BridgeExtensions.tip2
  exact ((continuous_const.add ((h0 _ u).comp continuous_fst)).add
    (((h1 _ u).comp continuous_fst).div_const 2)).sub
    ((continuous_const.mul (hv _ (continuous_fst.comp continuous_snd))).add
      (continuous_const.mul (hv _ (continuous_snd.comp continuous_snd))))

/-- Woodford (2003), **Proposition 6.11**, (4.25): the pathwise remainder of the two-sector
economy along a path of readouts, zero initial dispersions. -/
noncomputable def rem611 {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (u v : ℝ × Ξ → ℝ) (w1 w2 : ι → ℝ) (n1 η θ Ybar σi ω β α1 α2 : ℝ) (f1 f2 : ℕ → ℝ)
    (yh1 yh2 : ℕ → ι → ℝ) (xu xv1 xv2 : ℕ → Ξ) (g q1 q2 π1 π2 : ℕ → ℝ) : ℝ :=
  (∑' t, β ^ t * BridgeExtensions.periodU2 u v n1 η θ Ybar w1 w2 (f1 t) (f2 t) (yh1 t) (yh2 t)
      (xu t) (xv1 t) (xv2 t)) -
    (-(Ybar * BridgeExtensions.dY u (Ybar, 0) / 2 * (θ * (σi + ω) /
        TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
          (Moments.calvoKappa α2 β ω θ σi))) *
      ∑' t, β ^ t * TwoSectorWelfare.loss425
        (TwoSectorWelfare.wJ n1 (Moments.calvoKappa α1 β ω θ σi)
          (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
            (Moments.calvoKappa α2 β ω θ σi)))
        (TwoSectorWelfare.wJ (1 - n1) (Moments.calvoKappa α2 β ω θ σi)
          (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
            (Moments.calvoKappa α2 β ω θ σi)))
        (TwoSectorWelfare.lamX (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
          (Moments.calvoKappa α2 β ω θ σi)) θ)
        (TwoSectorWelfare.lamR n1 η ω σi (TwoSectorWelfare.kappaH n1
          (Moments.calvoKappa α1 β ω θ σi) (Moments.calvoKappa α2 β ω θ σi)) θ)
        (π1 t) (π2 t)
        (BridgeExtensions.logY2 n1 η Ybar (f1 t) (f2 t) (BridgeExtensions.logYidx w1 θ (yh1 t))
          (BridgeExtensions.logYidx w2 θ (yh2 t)) - TwoSectorWelfare.natY σi ω n1 (g t) (q1 t)
            (q2 t)) 0
        (((BridgeExtensions.logYidx w2 θ (yh2 t) - BridgeExtensions.logYidx w1 θ (yh1 t)) -
          TwoSectorWelfare.natD η⁻¹ ω (f2 t - f1 t) (q1 t) (q2 t)) / η) +
      ∑' t, β ^ t * (BridgeExtensions.tip2 u v n1 Ybar (xu t) (xv1 t) (xv2 t) +
        Ybar * BridgeExtensions.dY u (Ybar, 0) * TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g t)
          (q1 t) (q2 t) (f2 t - f1 t) (BridgeExtensions.tauAgg η⁻¹ n1 (f1 t) (f2 t))))

/-- Woodford (2003), **Proposition 6.11**, (4.25), p. 437, ALONG THE EQUILIBRIUM on the i.i.d.
probability space: under the hypotheses of `SmoothInSigmaMeasureWelfare.prop610_measure`, with
in addition sectoral inflation `π_j`, sectoral mean-price inflation `π̄_j` and relative prices as
`C²` readouts vanishing at `ȳ`, and along the equilibrium (small amplitudes) the exact Calvo laws
of sectoral price dispersion (`Δ_j = var_i ŷ_j/θ²`) and the sectoral mean/index discrepancies,
`E[∑βᵗU_t] = E[−(K/2)(θ(σ⁻¹+ω)/κ)∑βᵗL_t + ∑βᵗ t.i.p._t] + O(ε³)` with `L` the loss (4.25) on
the actual path (`x = Ŷ − Ŷⁿ`, relative-price gap `g_R`). -/
theorem prop611_measure [FiniteDimensional ℝ Y] (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type}
    [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {n1 η θ : ℝ} (hn0 : 0 < n1)
    (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) {w1 w2 : ι → ℝ}
    (hw10 : ∀ i, 0 ≤ w1 i) (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i)
    (hw21 : ∑ i, w2 i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {Ybar σi ω β α1 α2 : ℝ} (hY : 0 < Ybar) (hσω : 0 < σi + ω) (hηω : η⁻¹ + ω ≠ 0)
    (hωθ : 0 < 1 + ω * θ) (ha10 : 0 < α1) (ha11 : α1 < 1) (ha20 : 0 < α2) (ha21 : α2 < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σi * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yh1R yh2R rp1R rp2R : Y → ι → ℝ} {f1R f2R gR q1R q2R π1R π2R pb1R pb2R : Y → ℝ}
    {xuR xv1R xv2R : Y → Ξ}
    (cy1 : ContDiffAt ℝ 2 yh1R ybar) (cy2 : ContDiffAt ℝ 2 yh2R ybar)
    (cr1 : ContDiffAt ℝ 2 rp1R ybar) (cr2 : ContDiffAt ℝ 2 rp2R ybar)
    (cf1 : ContDiffAt ℝ 2 f1R ybar) (cf2 : ContDiffAt ℝ 2 f2R ybar)
    (cg : ContDiffAt ℝ 2 gR ybar) (cq1 : ContDiffAt ℝ 2 q1R ybar) (cq2 : ContDiffAt ℝ 2 q2R ybar)
    (cπ1 : ContDiffAt ℝ 2 π1R ybar) (cπ2 : ContDiffAt ℝ 2 π2R ybar)
    (cp1 : ContDiffAt ℝ 2 pb1R ybar) (cp2 : ContDiffAt ℝ 2 pb2R ybar)
    (cxu : ContDiffAt ℝ 2 xuR ybar) (cxv1 : ContDiffAt ℝ 2 xv1R ybar)
    (cxv2 : ContDiffAt ℝ 2 xv2R ybar)
    (zy1 : yh1R ybar = 0) (zy2 : yh2R ybar = 0) (zr1 : rp1R ybar = 0) (zr2 : rp2R ybar = 0)
    (zf1 : f1R ybar = 0) (zf2 : f2R ybar = 0) (zg : gR ybar = 0) (zq1 : q1R ybar = 0)
    (zq2 : q2R ybar = 0) (zπ1 : π1R ybar = 0) (zπ2 : π2R ybar = 0) (zp1 : pb1R ybar = 0)
    (zp2 : pb2R ybar = 0) (zxu : xuR ybar = 0) (zxv1 : xv1R ybar = 0) (zxv2 : xv2R ybar = 0)
    (hnorm : ∀ y, n1 * Real.exp (f1R y) + (1 - n1) * Real.exp (f2R y) = 1)
    (hg : ∀ y, BridgeExtensions.dYXi u (Ybar, 0) (xuR y) =
      σi * BridgeExtensions.dY u (Ybar, 0) * gR y)
    (hq1 : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xv1R y) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q1R y))
    (hq2 : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xv2R y) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q2R y))
    (hlaw1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      crossVar w1 (yh1R (ypath ψ ybar ε t ω')) / θ ^ 2 = α1 * (crossVar w1 (yh1R (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω')) / θ ^ 2) +
          α1 / (1 - α1) * pb1R (ypath ψ ybar ε t ω') ^ 2)
    (hlaw2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      crossVar w2 (yh2R (ypath ψ ybar ε t ω')) / θ ^ 2 = α2 * (crossVar w2 (yh2R (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω')) / θ ^ 2) +
          α2 / (1 - α2) * pb2R (ypath ψ ybar ε t ω') ^ 2)
    (hdisc1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      pb1R (ypath ψ ybar ε t ω') - π1R (ypath ψ ybar ε t ω') =
        discF w1 θ (fun i => rp1R (ypath ψ ybar ε t ω') i + π1R (ypath ψ ybar ε t ω'))
          (rp1R (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω')))
    (hdisc2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      pb2R (ypath ψ ybar ε t ω') - π2R (ypath ψ ybar ε t ω') =
        discF w2 θ (fun i => rp2R (ypath ψ ybar ε t ω') i + π2R (ypath ψ ybar ε t ω'))
          (rp2R (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω'))) :
    (fun ε => ∫ ω', rem611 u v w1 w2 n1 η θ Ybar σi ω β α1 α2
      (fun t => f1R (ypath ψ ybar ε t ω')) (fun t => f2R (ypath ψ ybar ε t ω'))
      (fun t => yh1R (ypath ψ ybar ε t ω')) (fun t => yh2R (ypath ψ ybar ε t ω'))
      (fun t => xuR (ypath ψ ybar ε t ω')) (fun t => xv1R (ypath ψ ybar ε t ω'))
      (fun t => xv2R (ypath ψ ybar ε t ω')) (fun t => gR (ypath ψ ybar ε t ω'))
      (fun t => q1R (ypath ψ ybar ε t ω')) (fun t => q2R (ypath ψ ybar ε t ω'))
      (fun t => π1R (ypath ψ ybar ε t ω')) (fun t => π2R (ypath ψ ybar ε t ω'))
      ∂(ExpectationsMeasureIID.iidSystem ν0).μ) =O[𝓝 0] fun ε => ε ^ 3 := by
  classical
  have hψ1 : DifferentiableAt ℝ ψ (pbar ybar) := hψ2.differentiableAt (by norm_num)
  set L2 := ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) ×ˢ (⊤ : Filter ℕ) with hL2
  set K := Ybar * BridgeExtensions.dY u (Ybar, 0) with hK
  -- second-order dispersions and discrepancies
  have cD1 : ContDiffAt ℝ 2 (fun y => crossVar w1 (yh1R y) / θ ^ 2) ybar :=
    (contDiffAt_crossVar w1 cy1).div_const _
  have zD1 : (fun y => crossVar w1 (yh1R y) / θ ^ 2) ybar = 0 := by
    simp only [zy1, crossVar_zero, zero_div]
  have cD2 : ContDiffAt ℝ 2 (fun y => crossVar w2 (yh2R y) / θ ^ 2) ybar :=
    (contDiffAt_crossVar w2 cy2).div_const _
  have zD2 : (fun y => crossVar w2 (yh2R y) / θ ^ 2) ybar = 0 := by
    simp only [zy2, crossVar_zero, zero_div]
  have hD11 := dispersion_first_order_zero hbase hψ1 (cD1.differentiableAt (by norm_num))
    (cp1.differentiableAt (by norm_num)) zp1 hlaw1
  have hD21 := dispersion_first_order_zero hbase hψ1 (cD2.differentiableAt (by norm_num))
    (cp2.differentiableAt (by norm_num)) zp2 hlaw2
  have hD1O : UProc (𝓝 0) (fun ε t ω => crossVar w1 (yh1R (ypath ψ ybar ε t ω)) / θ ^ 2)
      fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cD1 zD1).congr_left fun b => ?_
    simp only [hD11, smul_zero, sub_zero]
  have hD2O : UProc (𝓝 0) (fun ε t ω => crossVar w2 (yh2R (ypath ψ ybar ε t ω)) / θ ^ 2)
      fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cD2 zD2).congr_left fun b => ?_
    simp only [hD21, smul_zero, sub_zero]
  have hp1O := disc_second_order hw10 hw11 hθ1 hbase hψ2 cr1 cπ1 zr1 zπ1 hdisc1
  have hp2O := disc_second_order hw20 hw21 hθ1 hbase hψ2 cr2 cπ2 zr2 zπ2 hdisc2
  -- composite readouts: the output gap and the relative-price gap
  have cY1 := SmoothInSigmaMeasureWelfare.contDiffAt_logYidx hw11 θ cy1 zy1
  have cY2 := SmoothInSigmaMeasureWelfare.contDiffAt_logYidx hw21 θ cy2 zy2
  have zY1 : BridgeExtensions.logYidx w1 θ (yh1R ybar) = 0 := by
    rw [zy1]; exact SmoothInSigmaMeasureWelfare.logYidx_zero hw11 θ
  have zY2 : BridgeExtensions.logYidx w2 θ (yh2R ybar) = 0 := by
    rw [zy2]; exact SmoothInSigmaMeasureWelfare.logYidx_zero hw21 θ
  have cx : ContDiffAt ℝ 2 (fun y => BridgeExtensions.logY2 n1 η Ybar (f1R y) (f2R y)
      (BridgeExtensions.logYidx w1 θ (yh1R y)) (BridgeExtensions.logYidx w2 θ (yh2R y)) -
      TwoSectorWelfare.natY σi ω n1 (gR y) (q1R y) (q2R y)) ybar := by
    unfold TwoSectorWelfare.natY
    exact (SmoothInSigmaMeasureWelfare.contDiffAt_logY2 hn0 hn1 hη hη1 hY cf1 cf2 cY1 cY2).sub
      (((contDiffAt_const.mul cg).add (contDiffAt_const.mul ((contDiffAt_const.mul cq1).add
        (contDiffAt_const.mul cq2)))).div_const _)
  have zx : (fun y => BridgeExtensions.logY2 n1 η Ybar (f1R y) (f2R y)
      (BridgeExtensions.logYidx w1 θ (yh1R y)) (BridgeExtensions.logYidx w2 θ (yh2R y)) -
      TwoSectorWelfare.natY σi ω n1 (gR y) (q1R y) (q2R y)) ybar = 0 := by
    simp only [zf1, zf2, zY1, zY2, zg, zq1, zq2, TwoSectorWelfare.natY,
      SmoothInSigmaMeasureWelfare.logY2_zero hn0 hn1 hη hη1 hY]
    ring
  have cgR : ContDiffAt ℝ 2 (fun y => ((BridgeExtensions.logYidx w2 θ (yh2R y) -
      BridgeExtensions.logYidx w1 θ (yh1R y)) -
      TwoSectorWelfare.natD η⁻¹ ω (f2R y - f1R y) (q1R y) (q2R y)) / η) ybar := by
    unfold TwoSectorWelfare.natD
    exact ((cY2.sub cY1).sub (((contDiffAt_const.mul (cf2.sub cf1)).add
      (contDiffAt_const.mul (cq2.sub cq1))).div_const _)).div_const _
  have zgR : (fun y => ((BridgeExtensions.logYidx w2 θ (yh2R y) -
      BridgeExtensions.logYidx w1 θ (yh1R y)) -
      TwoSectorWelfare.natD η⁻¹ ω (f2R y - f1R y) (q1R y) (q2R y)) / η) ybar = 0 := by
    simp only [zY1, zY2, zf1, zf2, zq1, zq2, TwoSectorWelfare.natD]
    ring
  -- the t.i.p. are uniformly bounded for small amplitudes
  have cτ : ContDiffAt ℝ 2 (fun y => (xuR y, xv1R y, xv2R y, gR y, q1R y, q2R y, f1R y, f2R y))
      ybar := cxu.prodMk (cxv1.prodMk (cxv2.prodMk (cg.prodMk (cq1.prodMk (cq2.prodMk
        (cf1.prodMk cf2))))))
  have zτ : (fun y => (xuR y, xv1R y, xv2R y, gR y, q1R y, q2R y, f1R y, f2R y)) ybar = 0 := by
    simp [zxu, zxv1, zxv2, zg, zq1, zq2, zf1, zf2]
  obtain ⟨Mτ, hMτ⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cτ zτ))
    (φ := fun x => BridgeExtensions.tip2 u v n1 Ybar x.1 x.2.1 x.2.2.1 +
      K * TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
        (x.2.2.2.2.2.2.2 - x.2.2.2.2.2.2.1)
        (BridgeExtensions.tauAgg η⁻¹ n1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2))
    (((continuous_tip2 u v n1 Ybar).comp (continuous_fst.prodMk ((continuous_fst.comp
      continuous_snd).prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd))))).add
      (continuous_const.mul (by
        unfold TwoSectorWelfare.tip610 BridgeExtensions.tauAgg; fun_prop))).continuousAt
  -- a small amplitude where the model equations hold
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 (hlaw1.and hlaw2)
  set P : ℝ × (ℕ → ℝ) → Prop := fun a => dist a.1 0 < ρ ∧ ∀ t,
    |BridgeExtensions.tip2 u v n1 Ybar (xuR (ypath ψ ybar a.1 t a.2)) (xv1R
        (ypath ψ ybar a.1 t a.2)) (xv2R (ypath ψ ybar a.1 t a.2)) +
      K * TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (gR (ypath ψ ybar a.1 t a.2)) (q1R
          (ypath ψ ybar a.1 t a.2)) (q2R (ypath ψ ybar a.1 t a.2))
        (f2R (ypath ψ ybar a.1 t a.2) - f1R (ypath ψ ybar a.1 t a.2))
            (BridgeExtensions.tauAgg η⁻¹ n1 (f1R (ypath ψ ybar a.1 t a.2)) (f2R
                (ypath ψ ybar a.1 t a.2)))| ≤ Mτ with hPd
  have hP : ∀ᶠ a in (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ)), P a :=
    (tendsto_fst.eventually (Metric.ball_mem_nhds (0 : ℝ) hρ)).and hMτ
  set W : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then BridgeExtensions.periodU2 u v n1 η θ
    Ybar w1 w2 (f1R (ypath ψ ybar a.1 t a.2)) (f2R (ypath ψ ybar a.1 t a.2)) (yh1R
        (ypath ψ ybar a.1 t a.2)) (yh2R (ypath ψ ybar a.1 t a.2)) (xuR (ypath ψ ybar a.1 t a.2))
            (xv1R (ypath ψ ybar a.1 t a.2)) (xv2R (ypath ψ ybar a.1 t a.2)) else 0 with hW
  set τ : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    BridgeExtensions.tip2 u v n1 Ybar (xuR (ypath ψ ybar a.1 t a.2)) (xv1R
        (ypath ψ ybar a.1 t a.2)) (xv2R (ypath ψ ybar a.1 t a.2)) +
      K * TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (gR (ypath ψ ybar a.1 t a.2)) (q1R
          (ypath ψ ybar a.1 t a.2)) (q2R (ypath ψ ybar a.1 t a.2))
        (f2R (ypath ψ ybar a.1 t a.2) - f1R (ypath ψ ybar a.1 t a.2))
            (BridgeExtensions.tauAgg η⁻¹ n1 (f1R (ypath ψ ybar a.1 t a.2)) (f2R
                (ypath ψ ybar a.1 t a.2))) else 0 with hτd
  set x : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    BridgeExtensions.logY2 n1 η Ybar (f1R (ypath ψ ybar a.1 t a.2)) (f2R (ypath ψ ybar a.1 t a.2))
      (BridgeExtensions.logYidx w1 θ (yh1R (ypath ψ ybar a.1 t a.2)))
          (BridgeExtensions.logYidx w2 θ (yh2R (ypath ψ ybar a.1 t a.2))) -
      TwoSectorWelfare.natY σi ω n1 (gR (ypath ψ ybar a.1 t a.2)) (q1R (ypath ψ ybar a.1 t a.2))
          (q2R (ypath ψ ybar a.1 t a.2)) else 0 with hxd
  set gRp : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    ((BridgeExtensions.logYidx w2 θ (yh2R
        (ypath ψ ybar a.1 t a.2)) - BridgeExtensions.logYidx w1 θ (yh1R (ypath ψ ybar a.1 t a.2))) -
      TwoSectorWelfare.natD η⁻¹ ω (f2R (ypath ψ ybar a.1 t a.2) - f1R (ypath ψ ybar a.1 t a.2))
          (q1R (ypath ψ ybar a.1 t a.2)) (q2R (ypath ψ ybar a.1 t a.2))) / η else 0 with hgRd
  set π1 : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then π1R
      (ypath ψ ybar a.1 t a.2) else 0 with hπ1d
  set π2 : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then π2R
      (ypath ψ ybar a.1 t a.2) else 0 with hπ2d
  set pb1 : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then pb1R
      (ypath ψ ybar a.1 t a.2) else 0 with hpb1d
  set pb2 : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then pb2R
      (ypath ψ ybar a.1 t a.2) else 0 with hpb2d
  set Δ1 : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    crossVar w1 (yh1R (ypath ψ ybar a.1 t a.2)) / θ ^ 2 else 0 with hΔ1d
  set Δ2 : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if P a then
    crossVar w2 (yh2R (ypath ψ ybar a.1 t a.2)) / θ ^ 2 else 0 with hΔ2d
  have hτb : ∀ a, Sequences.Bdd (τ a) := fun a => ⟨max Mτ 0, fun t => by
    by_cases h : P a
    · simp only [hτd, h, ↓reduceIte]; exact (h.2 t).trans (le_max_left _ _)
    · simp [hτd, h]⟩
  have hs2 : Tendsto (fun b : (ℝ × (ℕ → ℝ)) × ℕ => b.1.1) L2 (𝓝 0) :=
    tendsto_fst.comp tendsto_fst
  have h610 := BridgeExtensions.prop610_actual (L := L2) (s := fun b => b.1.1) hs2 hn0 hn1 hη
    hη1 hθ1 hw10 hw11 hw20 hw21 hu hv hY hσω.ne' hηω hucc hvy hvyy
    (yh1 := fun b => yh1R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (yh2 := fun b => yh2R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (f1 := fun b => f1R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (f2 := fun b => f2R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (g := fun b => gR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (q1 := fun b => q1R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (q2 := fun b => q2R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xu := fun b => xuR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xv1 := fun b => xv1R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xv2 := fun b => xv2R (ypath ψ ybar b.1.1 b.2 b.1.2))
    (fun b => hnorm _) (fun b => hg _) (fun b => hq1 _) (fun b => hq2 _)
    (uproc_lift2 (readout_first hbase hψ2 cy1 zy1)) (uproc_lift2 (readout_first hbase hψ2 cy2 zy2))
    (uproc_lift2 (readout_first hbase hψ2 cf1 zf1)) (uproc_lift2 (readout_first hbase hψ2 cf2 zf2))
    (uproc_lift2 (readout_first hbase hψ2 cg zg)) (uproc_lift2 (readout_first hbase hψ2 cq1 zq1))
    (uproc_lift2 (readout_first hbase hψ2 cq2 zq2))
    (uproc_lift2 (readout_first hbase hψ2 cxu zxu))
    (uproc_lift2 (readout_first hbase hψ2 cxv1 zxv1))
    (uproc_lift2 (readout_first hbase hψ2 cxv2 zxv2))
  have hPc : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => W p.1 p.2 - (τ p.1 p.2 - K / 2 *
      ((σi + ω) * (x p.1 p.2 - 0) ^ 2 + n1 * (1 - n1) * η * (1 + ω * η) * gRp p.1 p.2 ^ 2 +
        θ * (1 + ω * θ) * (n1 * Δ1 p.1 p.2 + (1 - n1) * Δ2 p.1 p.2)))) =O[L2]
      fun p => p.1.1 ^ 3 := by
    refine h610.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [tendsto_fst.eventually hP] with b hb
    simp only [hW, hτd, hxd, hgRd, hΔ1d, hΔ2d, hb, ↓reduceIte, BridgeExtensions.loss610]
    field_simp
    ring
  have m1 : ∀ {R : Y → ℝ}, ContDiffAt ℝ 2 R ybar → R ybar = 0 →
      (fun p : (ℝ × (ℕ → ℝ)) × ℕ => if P p.1 then R (ypath ψ ybar p.1.1 p.2 p.1.2) else 0)
        =O[L2] fun p => p.1.1 ^ 1 := fun {R} hR hR0 =>
    isBigO_mask2 (uproc_lift2 (readout_first hbase hψ2 hR hR0)) hP
  have hx : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => x p.1 p.2 - 0) =O[L2] fun p => p.1.1 ^ 1 :=
    (m1 cx zx).congr_left fun p => by simp only [hxd, sub_zero]
  have hD1 : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => Δ1 p.1 p.2) =O[L2] fun p => p.1.1 ^ 2 :=
    isBigO_mask2 (uproc_lift2 hD1O) hP
  have hD2 : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => Δ2 p.1 p.2) =O[L2] fun p => p.1.1 ^ 2 :=
    isBigO_mask2 (uproc_lift2 hD2O) hP
  have hpp1 : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => pb1 p.1 p.2 - π1 p.1 p.2) =O[L2]
      fun p => p.1.1 ^ 2 := by
    refine (isBigO_mask2 (uproc_lift2 hp1O) hP).congr_left fun p => ?_
    by_cases h : P p.1 <;> simp [hpb1d, hπ1d, h]
  have hpp2 : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => pb2 p.1 p.2 - π2 p.1 p.2) =O[L2]
      fun p => p.1.1 ^ 2 := by
    refine (isBigO_mask2 (uproc_lift2 hp2O) hP).congr_left fun p => ?_
    by_cases h : P p.1 <;> simp [hpb2d, hπ2d, h]
  have h10 : ∀ a, Δ1 a 0 = α1 * (fun _ => (0 : ℝ)) a + α1 / (1 - α1) * pb1 a 0 ^ 2 :=
    fun a => by
    by_cases h : P a
    · have hl := (hρs h.1).1 0 a.2
      simp only [hΔ1d, hpb1d, h, ↓reduceIte]
      rw [hl, zy1, crossVar_zero, zero_div, mul_zero]
    · simp [hΔ1d, hpb1d, h]
  have h1s : ∀ a t, Δ1 a (t + 1) = α1 * Δ1 a t + α1 / (1 - α1) * pb1 a (t + 1) ^ 2 :=
    fun a t => by
    by_cases h : P a
    · have hl := (hρs h.1).1 (t + 1) a.2
      simp only [hΔ1d, hpb1d, h, ↓reduceIte]
      exact hl
    · simp [hΔ1d, hpb1d, h]
  have h20 : ∀ a, Δ2 a 0 = α2 * (fun _ => (0 : ℝ)) a + α2 / (1 - α2) * pb2 a 0 ^ 2 :=
    fun a => by
    by_cases h : P a
    · have hl := (hρs h.1).2 0 a.2
      simp only [hΔ2d, hpb2d, h, ↓reduceIte]
      rw [hl, zy2, crossVar_zero, zero_div, mul_zero]
    · simp [hΔ2d, hpb2d, h]
  have h2s : ∀ a t, Δ2 a (t + 1) = α2 * Δ2 a t + α2 / (1 - α2) * pb2 a (t + 1) ^ 2 :=
    fun a t => by
    by_cases h : P a
    · have hl := (hρs h.1).2 (t + 1) a.2
      simp only [hΔ2d, hpb2d, h, ↓reduceIte]
      exact hl
    · simp [hΔ2d, hpb2d, h]
  have hcore := BridgeExtensions.prop611_layerB (K := K) (xs := 0)
    (l := (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) (e := fun a => a.1) ha10 ha11 ha20 ha21 hβ0
    hβ1 hn0 hn1 hθ hωθ hσω tendsto_fst hτb hPc hx (m1 cgR zgR) (m1 cπ1 zπ1) (m1 cπ2 zπ2) hD1
    hD2 hpp1 hpp2 h10 h1s h20 h2s
  refine integral_isBigO _ (hcore.congr' ?_ (Eventually.of_forall fun _ => rfl))
  filter_upwards [hP] with a ha
  simp only [hW, hτd, hxd, hgRd, hπ1d, hπ2d, ha, ↓reduceIte, rem611, mul_zero, zero_div,
    add_zero, sub_zero, hK]

/-! ## Proposition 6.7 along the equilibrium (one-sided expansion at satiation) -/

/-- Woodford (2003), **Proposition 6.7**, (4.9): the Layer-B remainder of the transactions
economy (actual utility minus `t.i.p. − (ε²/2)·Ȳu_c·loss49(first-order solution)`). -/
noncomputable def rem67 {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (U Ut : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (w : ι → ℝ) (θ Ybar mbar : ℝ)
    (P : Transactions.TxParams) (yh : ι → ℝ) (mh : ℝ) (xu xv : Ξ) (g q eps Y1 d1 g1 q1 eps1 : ℝ)
    (y1 : ι → ℝ) (s : ℝ) : ℝ :=
  BridgeExtensions.periodUT U v w θ Ybar mbar yh mh xu xv -
    ((BridgeExtensions.tipT Ut v Ybar mbar xu xv + Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
      Transactions.tip P g q eps 0 0) -
      s ^ 2 / 2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * Transactions.loss49 P
        (BridgeExtensions.txSat P Y1 d1 g1 q1 eps1 (crossVar w y1) 0)))

/-- Woodford (2003), App. E.4 (**the money-demand residual is of second order**): if real
balances obey `m̂ = M(Ŷ, î − îᵐ, εᵐ)` with `M` differentiable at `0`, `M(0) = 0` and
`DM(0)(a, b, c) = η_y a − η_i b + c` (eq. (4.1)), then the residual
`m̂ − (η_yŶ − η_i(î − îᵐ) + εᵐ)` has zero derivative at `ȳ`. -/
theorem fderiv_money_residual {ι : Type} [Fintype ι] {w : ι → ℝ} {θ ηY ηI : ℝ} {ybar : Y}
    {yhR : Y → ι → ℝ} {mhR dR epsR : Y → ℝ} {mdem : ℝ × ℝ × ℝ → ℝ}
    {Lmd : ℝ × ℝ × ℝ →L[ℝ] ℝ} (hLmd : ∀ a b c, Lmd (a, b, c) = ηY * a - ηI * b + c)
    (hmd : HasFDerivAt mdem Lmd 0)
    (hT : HasFDerivAt (fun y => (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
      (fderiv ℝ (fun y => (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y)) ybar) ybar)
    (hT0 : (BridgeExtensions.logYidx w θ (yhR ybar), dR ybar, epsR ybar) = 0)
    (hm : ∀ y, mhR y = mdem (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y)) :
    fderiv ℝ (fun y => mhR y - (ηY * BridgeExtensions.logYidx w θ (yhR y) - ηI * dR y +
      epsR y)) ybar = 0 := by
  set T := fun y => (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y) with hTd
  have hT0' : T ybar = 0 := hT0
  have hmd' : HasFDerivAt (fun x => mdem x - Lmd x) (Lmd - Lmd) (T ybar) := by
    rw [hT0']; exact hmd.sub Lmd.hasFDerivAt
  have hc := hmd'.comp ybar hT
  rw [sub_self, ContinuousLinearMap.zero_comp] at hc
  have he : (fun y => mhR y - (ηY * BridgeExtensions.logYidx w θ (yhR y) - ηI * dR y +
      epsR y)) = (fun x => mdem x - Lmd x) ∘ T := by
    funext y
    simp only [Function.comp_apply, hTd, hm, hLmd]
  rw [he]
  exact hc.fderiv

/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, ALONG THE EQUILIBRIUM on the i.i.d.
probability space, with the ONE-SIDED expansion at satiation: under the hypotheses of
`BridgeExtensions.prop67_layerB` on preferences, let the decision vector carry, through `C²`
readouts vanishing at `ȳ`, log outputs, real balances `m̂`, the interest differential, the
composite disturbances and the shocks. The model's equations are the composites (`hg`, `heps`,
`hq`), the money demand `m̂ = M(Ŷ, î − îᵐ, εᵐ)` (eq. (4.1)) and the satiation constraint
`m̂ ≤ 0` along the equilibrium. Then the actual period utility is
`t.i.p. − (ε²/2)·Ȳu_c·loss49(first-order solution) + O(ε³)` UNIFORMLY in the date and the path;
the money-demand residual is of second order (`fderiv_money_residual`). -/
theorem prop67_measure {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1)
    {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {mbar : ℝ} (hmbar : 0 < mbar)
    (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar}) {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = P.omega * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR : Y → ι → ℝ} {mhR dR gR qR epsR : Y → ℝ} {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (cmh : ContDiffAt ℝ 2 mhR ybar)
    (cd : ContDiffAt ℝ 2 dR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (cq : ContDiffAt ℝ 2 qR ybar)
    (ceps : ContDiffAt ℝ 2 epsR ybar) (cxu : ContDiffAt ℝ 2 xuR ybar)
    (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zmh : mhR ybar = 0) (zd : dR ybar = 0) (zg : gR ybar = 0)
    (zq : qR ybar = 0) (zeps : epsR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (hg : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * gR y))
    (heps : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * epsR y))
    (hq : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xvR y) =
      -(P.omega * BridgeExtensions.dY v (Ybar, 0) * qR y))
    {mdem : ℝ × ℝ × ℝ → ℝ} {Lmd : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hLmd : ∀ a b c, Lmd (a, b, c) = P.etaY * a - P.etaI * b + c)
    (hmd : HasFDerivAt mdem Lmd 0)
    (hm : ∀ y, mhR y = mdem (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
    (hleft : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω, mhR (ypath ψ ybar ε t ω) ≤ 0) :
    UProc (𝓝 0) (fun ε t ω' => rem67 U Ut v w θ Ybar mbar P (yhR (ypath ψ ybar ε t ω'))
      (mhR (ypath ψ ybar ε t ω')) (xuR (ypath ψ ybar ε t ω')) (xvR (ypath ψ ybar ε t ω'))
      (gR (ypath ψ ybar ε t ω')) (qR (ypath ψ ybar ε t ω')) (epsR (ypath ψ ybar ε t ω'))
      (fderiv ℝ (fun y => BridgeExtensions.logYidx w θ (yhR y)) ybar (y1path ψ ybar t ω'))
      (fderiv ℝ dR ybar (y1path ψ ybar t ω')) (fderiv ℝ gR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ qR ybar (y1path ψ ybar t ω')) (fderiv ℝ epsR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ yhR ybar (y1path ψ ybar t ω')) ε) fun ε => ε ^ 3 := by
  have hs : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1)
      ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ)))) (𝓝 0) := tendsto_fst
  have cY := SmoothInSigmaMeasureWelfare.contDiffAt_logYidx hw1 θ cyh zyh
  have zY : (fun y => BridgeExtensions.logYidx w θ (yhR y)) ybar = 0 := by
    simp only [zyh]; exact SmoothInSigmaMeasureWelfare.logYidx_zero hw1 θ
  have cT : ContDiffAt ℝ 2 (fun y => (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
      ybar := cY.prodMk (cd.prodMk ceps)
  have hres := fderiv_money_residual hLmd hmd ((cT.differentiableAt (by norm_num)).hasFDerivAt)
    (by simp only [zY, zd, zeps]; rfl) hm
  have cr : ContDiffAt ℝ 2 (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar :=
    cmh.sub (((contDiffAt_const.mul cY).sub (contDiffAt_const.mul cd)).add ceps)
  have zr : (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar = 0 := by
    simp only [zmh, zd, zeps]
    rw [show BridgeExtensions.logYidx w θ (yhR ybar) = 0 from zY]
    ring
  have hr : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => mhR (ypath ψ ybar b.1 b.2.1 b.2.2) -
      (P.etaY * BridgeExtensions.logYidx w θ (yhR (ypath ψ ybar b.1 b.2.1 b.2.2)) -
        P.etaI * dR (ypath ψ ybar b.1 b.2.1 b.2.2) + epsR (ypath ψ ybar b.1 b.2.1 b.2.2)))
      =O[(𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ)))] fun b => b.1 ^ 2 := by
    refine (readout_second hbase hψ2 cr zr).congr_left fun b => ?_
    simp only [hres, zero_apply, smul_zero, sub_zero]
  exact BridgeExtensions.prop67_layerB hs hw0 hw1 hθ hUt hmbar hEq hv P hθi hey hΩ hi hvb hsat
    h11 h12 h22 hvy hvyy (fun b => hg _) (fun b => heps _) (fun b => hq _)
    (readout_first hbase hψ2 cyh zyh) (readout_first hbase hψ2 cmh zmh)
    (readout_first hbase hψ2 cxu zxu) (readout_first hbase hψ2 cxv zxv) hr
    (tendsto_fst.eventually hleft |>.mono fun b hb => hb b.2.1 b.2.2)
    (readout_bdd ψ ybar yhR) (readout_bdd ψ ybar _) (readout_bdd ψ ybar dR)
    (readout_bdd ψ ybar gR) (readout_bdd ψ ybar qR) (readout_bdd ψ ybar epsR)
    (readout_second hbase hψ2 cyh zyh) (readout_second hbase hψ2 cY zY)
    (readout_second hbase hψ2 cd zd) (readout_second hbase hψ2 cg zg)
    (readout_second hbase hψ2 cq zq) (readout_second hbase hψ2 ceps zeps)

/-! ## Proposition 6.8 along the equilibrium -/

/-- Woodford (2003), (E.15): the policy-independent terms at satiation are continuous in the
shocks. -/
theorem continuous_tipT {Ξ : Type} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (Ut : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (Ybar mbar : ℝ) :
    Continuous fun x : Ξ × Ξ => BridgeExtensions.tipT Ut v Ybar mbar x.1 x.2 := by
  have hc : Continuous fun ξ : Ξ => ((0 : ℝ), (0 : ℝ), ξ) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hc' : Continuous fun ξ : Ξ => ((0 : ℝ), ξ) := continuous_const.prodMk continuous_id
  unfold BridgeExtensions.tipT BridgeExtensions.dXi BridgeExtensions.dXiXi
  exact ((continuous_const.add (((fderiv ℝ Ut (Ybar, mbar, 0)).continuous.comp hc).comp
    continuous_fst)).add (((((fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0)).continuous.comp
      hc).clm_apply hc).comp continuous_fst).div_const 2)).sub
    ((continuous_const.add (((fderiv ℝ v (Ybar, 0)).continuous.comp hc').comp continuous_snd)).add
      (((((fderiv ℝ (fderiv ℝ v) (Ybar, 0)).continuous.comp hc').clm_apply hc').comp
        continuous_snd).div_const 2))

/-- Woodford (2003), **Proposition 6.8**, (4.10): the pathwise remainder of the transactions
economy along a path of readouts, zero initial dispersion:
`∑βᵗU_t − (∑βᵗ t.i.p._t − (K/2)θ(1+ωθ)k ∑βᵗ L_t)` with `L` the loss (4.10). -/
noncomputable def rem68 {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    (U Ut : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (w : ι → ℝ) (α β θ Ybar mbar : ℝ)
    (P : Transactions.TxParams) (yh : ℕ → ι → ℝ) (mh : ℕ → ℝ) (xu xv : ℕ → Ξ)
    (d g q eps infl : ℕ → ℝ) : ℝ :=
  (∑' t, β ^ t * BridgeExtensions.periodUT U v w θ Ybar mbar (yh t) (mh t) (xu t) (xv t)) -
    (∑' t, β ^ t * (BridgeExtensions.tipT Ut v Ybar mbar (xu t) (xv t) +
      Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * Transactions.tip P (g t) (q t) (eps t) 0 0) -
      Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / 2 *
        (θ * (1 + P.omega * θ) * Moments.calvoK α β * ∑' t, β ^ t * Transactions.loss410 P α β θ
          (infl t) (BridgeExtensions.logYidx w θ (yh t) -
            Transactions.natRate P (g t) (q t) (eps t)) (d t)))

/-- Woodford (2003), **Proposition 6.8**, (4.10), p. 423, ALONG THE EQUILIBRIUM on the i.i.d.
probability space: under the hypotheses of `prop67_measure`, with in addition inflation `π`,
mean-price inflation `π̄` and relative prices as `C²` readouts vanishing at `ȳ`, and along the
equilibrium (small amplitudes) the exact Calvo law of price dispersion (`Δ = var_i ŷ/θ²`) and
the mean/index discrepancy, `E[∑βᵗU_t] = E[∑βᵗ t.i.p._t − (K/2)θ(1+ωθ)k∑βᵗL_t] + O(ε³)`, with
`L` the loss (4.10) on the actual path; the one-sided expansion at satiation is used at every
date. -/
theorem prop68_measure [FiniteDimensional ℝ Y] (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type}
    [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ α β : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {mbar : ℝ} (hmbar : 0 < mbar)
    (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar}) {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : 0 < Transactions.omegaMC P)
    (hωP : 0 ≤ P.omega) (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = P.omega * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR rpR : Y → ι → ℝ} {mhR dR gR qR epsR inflR pibR : Y → ℝ} {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (crp : ContDiffAt ℝ 2 rpR ybar)
    (cmh : ContDiffAt ℝ 2 mhR ybar)
    (cd : ContDiffAt ℝ 2 dR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (cq : ContDiffAt ℝ 2 qR ybar)
    (ceps : ContDiffAt ℝ 2 epsR ybar) (ci : ContDiffAt ℝ 2 inflR ybar)
    (cp : ContDiffAt ℝ 2 pibR ybar) (cxu : ContDiffAt ℝ 2 xuR ybar)
    (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zrp : rpR ybar = 0) (zmh : mhR ybar = 0) (zd : dR ybar = 0)
    (zg : gR ybar = 0) (zq : qR ybar = 0) (zeps : epsR ybar = 0) (zi : inflR ybar = 0)
    (zp : pibR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (hg : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * gR y))
    (heps : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * epsR y))
    (hq : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xvR y) =
      -(P.omega * BridgeExtensions.dY v (Ybar, 0) * qR y))
    {mdem : ℝ × ℝ × ℝ → ℝ} {Lmd : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hLmd : ∀ a b c, Lmd (a, b, c) = P.etaY * a - P.etaI * b + c)
    (hmd : HasFDerivAt mdem Lmd 0)
    (hm : ∀ y, mhR y = mdem (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
    (hleft : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω, mhR (ypath ψ ybar ε t ω) ≤ 0)
    (hlaw : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      crossVar w (yhR (ypath ψ ybar ε t ω')) / θ ^ 2 = α * (crossVar w (yhR (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω')) / θ ^ 2) + α / (1 - α) * pibR (ypath ψ ybar ε t ω') ^ 2)
    (hdisc : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      pibR (ypath ψ ybar ε t ω') - inflR (ypath ψ ybar ε t ω') =
        discF w θ (fun i => rpR (ypath ψ ybar ε t ω') i + inflR (ypath ψ ybar ε t ω'))
          (rpR (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω'))) :
    (fun ε => ∫ ω', rem68 U Ut v w α β θ Ybar mbar P (fun t => yhR (ypath ψ ybar ε t ω'))
      (fun t => mhR (ypath ψ ybar ε t ω')) (fun t => xuR (ypath ψ ybar ε t ω'))
      (fun t => xvR (ypath ψ ybar ε t ω')) (fun t => dR (ypath ψ ybar ε t ω'))
      (fun t => gR (ypath ψ ybar ε t ω')) (fun t => qR (ypath ψ ybar ε t ω'))
      (fun t => epsR (ypath ψ ybar ε t ω')) (fun t => inflR (ypath ψ ybar ε t ω'))
      ∂(ExpectationsMeasureIID.iidSystem ν0).μ) =O[𝓝 0] fun ε => ε ^ 3 := by
  classical
  set L2 := ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) ×ˢ (⊤ : Filter ℕ) with hL2
  set K := Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) with hK
  have hs2 : Tendsto (fun b : (ℝ × (ℕ → ℝ)) × ℕ => b.1.1) L2 (𝓝 0) :=
    tendsto_fst.comp tendsto_fst
  -- the period expansion along the path, from Proposition 6.7
  have cY := SmoothInSigmaMeasureWelfare.contDiffAt_logYidx hw1 θ cyh zyh
  have zY : (fun y => BridgeExtensions.logYidx w θ (yhR y)) ybar = 0 := by
    simp only [zyh]; exact SmoothInSigmaMeasureWelfare.logYidx_zero hw1 θ
  have cT : ContDiffAt ℝ 2 (fun y => (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
      ybar := cY.prodMk (cd.prodMk ceps)
  have hres := fderiv_money_residual hLmd hmd ((cT.differentiableAt (by norm_num)).hasFDerivAt)
    (by simp only [zY, zd, zeps]; rfl) hm
  have cr : ContDiffAt ℝ 2 (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar :=
    cmh.sub (((contDiffAt_const.mul cY).sub (contDiffAt_const.mul cd)).add ceps)
  have zr : (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar = 0 := by
    simp only [zmh, zd, zeps]
    rw [show BridgeExtensions.logYidx w θ (yhR ybar) = 0 from zY]
    ring
  have hr : UProc (𝓝 0) (fun ε t ω => mhR (ypath ψ ybar ε t ω) -
      (P.etaY * BridgeExtensions.logYidx w θ (yhR (ypath ψ ybar ε t ω)) -
        P.etaI * dR (ypath ψ ybar ε t ω) + epsR (ypath ψ ybar ε t ω))) fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cr zr).congr_left fun b => ?_
    simp only [hres, zero_apply, smul_zero, sub_zero]
  have h67 := BridgeExtensions.prop67_actual (L := L2) (s := fun b => b.1.1) hs2 hw0 hw1 hθ1
    hUt hmbar hEq hv P hθi hey hΩ.ne' hi hvb hsat h11 h12 h22 hvy hvyy
    (yh := fun b => yhR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (mh := fun b => mhR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (d := fun b => dR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (g := fun b => gR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (q := fun b => qR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (eps := fun b => epsR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xu := fun b => xuR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xv := fun b => xvR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (fun b => hg _) (fun b => heps _) (fun b => hq _)
    (uproc_lift2 (readout_first hbase hψ2 cyh zyh)) (uproc_lift2 (readout_first hbase hψ2 cmh zmh))
    (uproc_lift2 (readout_first hbase hψ2 cd zd)) (uproc_lift2 (readout_first hbase hψ2 cg zg))
    (uproc_lift2 (readout_first hbase hψ2 cq zq))
    (uproc_lift2 (readout_first hbase hψ2 ceps zeps))
    (uproc_lift2 (readout_first hbase hψ2 cxu zxu))
    (uproc_lift2 (readout_first hbase hψ2 cxv zxv)) (uproc_lift2 hr)
    ((tendsto_fst.comp tendsto_fst).eventually hleft |>.mono fun b hb => hb b.2 b.1.2)
  -- second-order dispersion and discrepancy
  have cD : ContDiffAt ℝ 2 (fun y => crossVar w (yhR y) / θ ^ 2) ybar :=
    (contDiffAt_crossVar w cyh).div_const _
  have hpO := disc_second_order hw0 hw1 hθ1 hbase hψ2 crp ci zrp zi hdisc
  -- uniform bounds for small amplitudes
  have cτ : ContDiffAt ℝ 2 (fun y => (xuR y, xvR y, gR y, qR y, epsR y)) ybar :=
    cxu.prodMk (cxv.prodMk (cg.prodMk (cq.prodMk ceps)))
  have zτ : (fun y => (xuR y, xvR y, gR y, qR y, epsR y)) ybar = 0 := by
    simp [zxu, zxv, zg, zq, zeps]
  obtain ⟨Mτ, hMτ⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cτ zτ))
    (φ := fun x => BridgeExtensions.tipT Ut v Ybar mbar x.1 x.2.1 +
      K * Transactions.tip P x.2.2.1 x.2.2.2.1 x.2.2.2.2 0 0)
    (((continuous_tipT Ut v Ybar mbar).comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).add (continuous_const.mul (by
        unfold Transactions.tip Transactions.natRate Transactions.xStar Transactions.sM
        fun_prop))).continuousAt
  obtain ⟨Mp, hMp⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cp zp))
    (φ := fun x => x) continuous_id.continuousAt
  obtain ⟨MV, hMV⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cyh zyh))
    (φ := fun x => crossVar w x) (by unfold crossVar ExpLogCES.crossMean; fun_prop)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hlaw
  set Pm : ℝ × (ℕ → ℝ) → Prop := fun a => dist a.1 0 < ρ ∧
    (∀ t, |BridgeExtensions.tipT Ut v Ybar mbar (xuR (ypath ψ ybar a.1 t a.2)) (xvR
        (ypath ψ ybar a.1 t a.2)) +
      K * Transactions.tip P (gR (ypath ψ ybar a.1 t a.2)) (qR (ypath ψ ybar a.1 t a.2)) (epsR
          (ypath ψ ybar a.1 t a.2)) 0 0| ≤ Mτ) ∧
    (∀ t, |pibR (ypath ψ ybar a.1 t a.2)| ≤ Mp) ∧ (∀ t, |crossVar w (yhR
        (ypath ψ ybar a.1 t a.2))| ≤ MV) with hPmd
  have hPm : ∀ᶠ a in (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ)), Pm a :=
    (tendsto_fst.eventually (Metric.ball_mem_nhds (0 : ℝ) hρ)).and (hMτ.and (hMp.and hMV))
  set W : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then BridgeExtensions.periodUT U v w θ
    Ybar mbar (yhR (ypath ψ ybar a.1 t a.2)) (mhR (ypath ψ ybar a.1 t a.2)) (xuR
        (ypath ψ ybar a.1 t a.2)) (xvR (ypath ψ ybar a.1 t a.2)) else 0 with hW
  set τ : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then
    BridgeExtensions.tipT Ut v Ybar mbar (xuR (ypath ψ ybar a.1 t a.2)) (xvR
        (ypath ψ ybar a.1 t a.2)) +
      K * Transactions.tip P (gR (ypath ψ ybar a.1 t a.2)) (qR (ypath ψ ybar a.1 t a.2)) (epsR
          (ypath ψ ybar a.1 t a.2)) 0 0 else 0 with hτd
  set Yv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then
    BridgeExtensions.logYidx w θ (yhR (ypath ψ ybar a.1 t a.2)) else 0 with hYv
  set dv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then dR
      (ypath ψ ybar a.1 t a.2) else 0 with hdv
  set gv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then gR
      (ypath ψ ybar a.1 t a.2) else 0 with hgv
  set qv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then qR
      (ypath ψ ybar a.1 t a.2) else 0 with hqv
  set ev : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then epsR
      (ypath ψ ybar a.1 t a.2) else 0 with hev
  set Vv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then crossVar w (yhR
      (ypath ψ ybar a.1 t a.2)) else 0 with hVv
  set pv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then pibR
      (ypath ψ ybar a.1 t a.2) else 0 with hpv
  set iv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then inflR
      (ypath ψ ybar a.1 t a.2) else 0 with hiv
  have hτb : ∀ a, Sequences.Bdd (τ a) := fun a => ⟨max Mτ 0, fun t => by
    by_cases h : Pm a
    · simp only [hτd, h, ↓reduceIte]; exact (h.2.1 t).trans (le_max_left _ _)
    · simp [hτd, h]⟩
  have hPc : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => W p.1 p.2 - (τ p.1 p.2 - K * Transactions.loss49 P
      (BridgeExtensions.txSat P (Yv p.1 p.2) (dv p.1 p.2) (gv p.1 p.2) (qv p.1 p.2)
        (ev p.1 p.2) (Vv p.1 p.2) 0) / 2)) =O[L2] fun p => p.1.1 ^ 3 := by
    refine h67.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [tendsto_fst.eventually hPm] with b hb
    simp only [hW, hτd, hYv, hdv, hgv, hqv, hev, hVv, hb, ↓reduceIte]
    simp only [Transactions.loss49, BridgeExtensions.txSat]
    ring
  have m1 : ∀ {R : Y → ℝ}, ContDiffAt ℝ 2 R ybar → R ybar = 0 →
      (fun p : (ℝ × (ℕ → ℝ)) × ℕ => if Pm p.1 then R (ypath ψ ybar p.1.1 p.2 p.1.2) else 0)
        =O[L2] fun p => p.1.1 ^ 1 := fun {R} hR hR0 =>
    isBigO_mask2 (uproc_lift2 (readout_first hbase hψ2 hR hR0)) hPm
  have hpp : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => pv p.1 p.2 - iv p.1 p.2) =O[L2]
      fun p => p.1.1 ^ 2 := by
    refine (isBigO_mask2 (uproc_lift2 hpO) hPm).congr_left fun p => ?_
    by_cases h : Pm p.1 <;> simp [hpv, hiv, h]
  have hθ' : P.thetaInv = 1 / θ := by rw [hθi, one_div]
  have hVs : ∀ a, HasSum (fun t => β ^ t * Vv a t)
      (θ ^ 2 * (Moments.calvoK α β * ∑' t, β ^ t * pv a t ^ 2 + (fun _ => (0 : ℝ)) a)) :=
    fun a => by
    by_cases h : Pm a
    · have hbdd : Sequences.Bdd (pv a) := ⟨Mp, fun t => by
        simp only [hpv, h, ↓reduceIte]; exact h.2.2.1 t⟩
      have hrec : ∀ t, Vv a t / θ ^ 2 = α * Sequences.lagS 0 (fun t => Vv a t / θ ^ 2) t +
          α / (1 - α) * pv a t ^ 2 := fun t => by
        have hl := (hρs h.1) t a.2
        cases t with
        | zero =>
          simp only [hVv, hpv, h, ↓reduceIte, Sequences.lagS_zero]
          rw [hl, zyh, crossVar_zero, zero_div, mul_zero]
        | succ k =>
          simp only [hVv, hpv, h, ↓reduceIte, Sequences.lagS_succ]
          exact hl
      have hd := Sequences.disp_discounted hβ0 hβ1 hα0.le hα1 hbdd hrec
      have hsum : Summable fun t => β ^ t * Vv a t := by
        refine Sequences.Bdd.summable (a := Vv a) ⟨MV, fun t => ?_⟩ hβ0 hβ1
        simp only [hVv, h, ↓reduceIte]; exact h.2.2.2 t
      convert hsum.hasSum using 1
      have hθ2 : θ ^ 2 ≠ 0 := by positivity
      have h2 : ∑' t, β ^ t * Vv a t = θ ^ 2 * ∑' t, β ^ t * (Vv a t / θ ^ 2) := by
        rw [← tsum_mul_left]
        congr 1
        funext t
        field_simp
      rw [h2, hd, Moments.calvoK]
      have hab : 1 - α * β ≠ 0 := by nlinarith
      have ha1 : 1 - α ≠ 0 := by linarith
      field_simp
      ring
    · have h0 : ∀ t, Vv a t = 0 := fun t => by simp [hVv, h]
      have h1 : ∀ t, pv a t = 0 := fun t => by simp [hpv, h]
      simp only [h0, h1, mul_zero]
      simp
  have hcore := BridgeExtensions.prop68_layerB (K := K) (T0 := fun _ => (0 : ℝ))
    (l := (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) (e := fun a => a.1) P hα0 hα1 hβ0 hβ1 hθ hθ'
    hωP hΩ hvb tendsto_fst hτb hPc
    ((m1 cY zY).congr_left fun p => rfl) (m1 cd zd) (m1 cg zg) (m1 cq zq) (m1 ceps zeps)
    (m1 ci zi) hpp hVs
  refine integral_isBigO _ (hcore.congr' ?_ (Eventually.of_forall fun _ => rfl))
  filter_upwards [hPm] with a ha
  simp only [hW, hτd, hYv, hdv, hgv, hqv, hev, hiv, ha, ↓reduceIte, rem68, mul_zero, add_zero, hK]

end Woodford.StabilizationWelfare.SmoothInSigmaMeasureProps
