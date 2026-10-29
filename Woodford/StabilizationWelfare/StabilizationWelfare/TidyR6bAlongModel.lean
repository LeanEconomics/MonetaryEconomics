/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasure615
import StabilizationWelfare.SmoothInSigmaMeasureProps

/-!
# The model equations along the perturbation equilibrium, derived from the model

Woodford (2003), *Interest and Prices*, Appendix E.2, p. 695 (the policy function of the model
`E_t f(y_{t+1}, y_t, y_{t−1}, e_t, e_{t+1}) = 0`), and Chapter 6, §5 (Propositions 6.14, 6.15).

`SmoothInSigmaMeasureProps.prop614_measure` and `SmoothInSigmaMeasure615.prop615_measure` take
the Calvo dispersion law, the mean-price discrepancy and (for 6.15) the Calvo conditions with
conditional expectations as HYPOTHESES on the path. Here they are DERIVED from the equilibrium
construction: if the period conditions `f` of the model contain these equations as components,
they hold along the equilibrium `ψ` of the model (`SmoothInSigmaMeasure.MModel.LocalSol`).

* **`solves_static`**: a component of `f` depending only on `(y_t, y_{t−1})` vanishes EXACTLY at
  every node of every solution on histories (the average over the next shock of a constant).
* **`static_on_path`**: hence along the equilibrium path, for small amplitudes, at every date
  and on EVERY path, with `y_{−1} = ȳ`.
* **`expect_on_path`**: a component `A(y_t) − B(y_{t+1})` gives `A(y_t) = E_t B(y_{t+1})`
  almost surely with Mathlib's conditional expectation, at every date.
* **`prop614_model`**, **`prop68_model`**: Propositions 6.14 and 6.8 along the equilibrium of any
  model whose conditions contain the Calvo law of dispersion and the mean-price/index discrepancy
  (`hlaw`, `hdisc` of
  `SmoothInSigmaMeasureProps.prop614_measure`/`SmoothInSigmaMeasureProps.prop68_measure` are now
  theorems).
* **`hleft_first_order_zero`**, **`TidyR6bAlongModel.hleft_money_demand`**: the one-sided
  hypothesis `hleft` of
  Propositions 6.7–6.8 holds along a perturbation equilibrium only if real balances do not move
  at first order (`η_yŶ¹ − η_i(î − îᵐ)¹ + εᵐ¹ ≡ 0`); otherwise it is FALSE, and the two-sided
  versions of `TidyR6bTwoSided67` apply.
-/

namespace Woodford.StabilizationWelfare.TidyR6bAlongModel

open MeasureTheory Filter Topology Asymptotics
open SmoothInSigmaMeasure (Hist consH tailH consH_zero tailH_consH adSub MModel measurable_consH)
open SmoothInSigmaMeasure.MModel (lagF)
open SmoothInSigma (Bd pbar norm_apply_le)
open SmoothInSigmaMeasurePath (histOf lagF_histOf)
open SmoothInSigmaMeasureWelfare (ypath)

variable {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] [CompleteSpace Z] [FiniteDimensional ℝ Y]

/-- **Woodford (2003), App. E.2, p. 695 (static model equations hold exactly).** If the
component `π ∘ f` of the period conditions depends only on `(y_t, y_{t−1})`,
`π(f(a, b, c, x, e)) = g(b, c)`, then every solution `u` of the model on histories satisfies
`g(u(t, s), u_{t−1}(s)) = 0` at EVERY node: the conditional expectation of a known quantity. -/
theorem solves_static {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f)
    (π : Z →L[ℝ] ℝ) {g : Y → Y → ℝ}
    (hπ : ∀ a b c x e, π (N.f (a, b, c, x, e)) = g b c) {p : Y × ℝ × ℝ}
    {u : adSub (R := Unit) Y} (hs : N.Solves (u : Bd (ℕ × Hist Unit) Y) p) (t : ℕ)
    (s : Hist Unit) : g ((u : Bd (ℕ × Hist Unit) Y) (t, s)) (lagF p u (t, s)) = 0 := by
  set G := N.NmS hc (N.WmapL (p, u)) with hG
  set F : ℝ → Z := fun e => ((G : adSub (R := Unit) Z) : Bd (ℕ × Hist Unit) Z)
    (t + 1, consH ((), e) s) with hF
  have hFm : StronglyMeasurable F :=
    (G.2.1 (t + 1)).comp_measurable (measurable_consH.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  have hFi : Integrable F (N.law () : Measure ℝ) :=
    Integrable.of_bound hFm.aestronglyMeasurable ‖(G : Bd (ℕ × Hist Unit) Z)‖
      (Eventually.of_forall fun e => norm_apply_le _ _)
  have hs' := hs t s
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
    SmoothInSigmaMeasure.MModel.trans_unit hN, one_smul] at hs'
  have hFe : ∀ e, F e = N.f ((u : Bd (ℕ × Hist Unit) Y) (t + 1, consH ((), e) s),
      (u : Bd (ℕ × Hist Unit) Y) (t, s), lagF p u (t, s), N.enowF p (t, s),
      p.2.2 * SmoothInSigmaMeasure.clipB N.bound e) := fun e => by
    change N.f (N.wfun p u (t + 1, consH ((), e) s)) = _
    simp only [MModel.wfun, tailH_consH, consH_zero]
  have h1 : ∫ e, F e ∂(N.law () : Measure ℝ) = 0 := by
    simp only [hFe]; exact hs'
  have h2 := π.integral_comp_comm hFi
  rw [h1, map_zero] at h2
  simp only [hFe, hπ, integral_const, probReal_univ, one_smul] at h2
  exact h2

omit [CompleteSpace Z] [FiniteDimensional ℝ Y] in
/-- Woodford (2003), App. E.2: the lagged value at the realised history, `ȳ` at date `0`. -/
theorem lagF_path (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (ybar : Y) (ε : ℝ) (t : ℕ)
    (ω : ℕ → ℝ) :
    lagF (ybar, 0, ε) (ψ (ybar, 0, ε) : Bd (ℕ × Hist Unit) Y) (t, histOf t ω) =
      match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω := by
  cases t with
  | zero => rfl
  | succ k => rw [lagF_histOf]; rfl

/-- **Woodford (2003), App. E.2 (static model equations along the equilibrium).** If `ψ` is a
local equilibrium of the model and `π(f(a, b, c, x, e)) = g(b, c)`, then for all small
amplitudes `ε`, at every date and on EVERY path, `g(y_t, y_{t−1}) = 0` with `y_{−1} = ȳ`. -/
theorem static_on_path {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f)
    {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} (hψ : N.LocalSol ybar ψ)
    (π : Z →L[ℝ] ℝ) {g : Y → Y → ℝ} (hπ : ∀ a b c x e, π (N.f (a, b, c, x, e)) = g b c) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω, g (ypath ψ ybar ε t ω) (match t with
      | 0 => ybar
      | k + 1 => ypath ψ ybar ε k ω) = 0 := by
  have hT : Tendsto (fun ε : ℝ => ((ybar, 0, ε) : Y × ℝ × ℝ)) (𝓝 0) (𝓝 (pbar ybar)) := by
    have : Continuous (fun ε : ℝ => ((ybar, 0, ε) : Y × ℝ × ℝ)) := by fun_prop
    simpa [pbar] using this.tendsto 0
  filter_upwards [hT.eventually hψ.solves] with ε hε t ω
  have h := solves_static hN hc π hπ hε t (histOf t ω)
  rwa [lagF_path] at h


/-- **Woodford (2003), App. E.2, p. 695 (expectational model equations along the
equilibrium).** If the model's shock law is `ν` and the component `π ∘ f` has the form
`π(f(a, b, c, x, e)) = A(b) − B(a)` (current part minus a lead), then for all small amplitudes,
at every date, `A(y_t) = E[B(y_{t+1}) | 𝓕_t]` almost surely on `(ℕ → ℝ, ν^ℕ)` (`A` and `B` are
continuous because `f` is). -/
theorem expect_on_path (ν : ProbabilityMeasure ℝ) {N : MModel Unit Y Z} (hN : N.Std)
    (hc : Continuous N.f) (hlawN : N.law () = ν) {ybar : Y}
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} (hψ : N.LocalSol ybar ψ) (π : Z →L[ℝ] ℝ)
    {A B : Y → ℝ} (hπ : ∀ a b c x e, π (N.f (a, b, c, x, e)) = A b - B a) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t, (fun ω => A (ypath ψ ybar ε t ω)) =ᵐ[(ExpectationsMeasureIID.iidSystem
      ν).μ] (ExpectationsMeasureIID.iidSystem ν).μ[fun ω => B (ypath ψ ybar ε (t + 1) ω) |
        (ExpectationsMeasureIID.iidSystem ν).𝓕 t] := by
  set E := ExpectationsMeasureIID.iidSystem ν with hE
  -- continuity of the two parts
  have hA : Continuous A := by
    have : A = fun b => π (N.f (ybar, b, ybar, 0, 0)) + B ybar := by
      funext b; rw [hπ]; ring
    rw [this]; fun_prop
  have hB : Continuous B := by
    have : B = fun a => A ybar - π (N.f (a, ybar, ybar, 0, 0)) := by
      funext a; rw [hπ]; ring
    rw [this]; fun_prop
  have hT : Tendsto (fun ε : ℝ => ((ybar, 0, ε) : Y × ℝ × ℝ)) (𝓝 0) (𝓝 (pbar ybar)) := by
    have : Continuous (fun ε : ℝ => ((ybar, 0, ε) : Y × ℝ × ℝ)) := by fun_prop
    simpa [pbar] using this.tendsto 0
  filter_upwards [hT.eventually hψ.solves] with ε hε t
  set p : Y × ℝ × ℝ := (ybar, 0, ε)
  set u := ψ p
  -- bounded continuous readouts of a bounded adapted family are integrable
  have hbdd : ∀ {C : Y → ℝ}, Continuous C → ∃ K, ∀ y, ‖y‖ ≤ ‖(u : Bd (ℕ × Hist Unit) Y)‖ →
      ‖C y‖ ≤ K := fun {C} hC => by
    obtain ⟨K, hK⟩ := IsCompact.exists_bound_of_continuousOn
      (isCompact_closedBall (0 : Y) ‖(u : Bd (ℕ × Hist Unit) Y)‖) hC.continuousOn
    exact ⟨K, fun y hy => hK y (by rwa [Metric.mem_closedBall, dist_zero_right])⟩
  have hyt : ∀ k, StronglyMeasurable[E.𝓕 k] (fun ω => ypath ψ ybar ε k ω) := fun k =>
    SmoothInSigmaMeasurePath.yproc_adapted ν u.2 k
  have hint : ∀ {C : Y → ℝ}, Continuous C → ∀ k,
      Integrable (fun ω => C (ypath ψ ybar ε k ω)) E.μ := fun {C} hC k => by
    obtain ⟨K, hK⟩ := hbdd hC
    refine Integrable.of_bound
      (hC.comp_stronglyMeasurable ((hyt k).mono (E.𝓕.le k))).aestronglyMeasurable K
      (Eventually.of_forall fun ω => hK _ ?_)
    exact SmoothInSigmaMeasurePath.norm_yproc_le _ k ω
  -- the model's conditions along the path
  set G := N.NmS hc (N.WmapL (p, u)) with hG
  set F : (ℕ → ℝ) → Z := fun ω => N.f (N.wfun p u (t + 1, histOf (t + 1) ω)) with hF
  have hFi : Integrable F E.μ := by
    have hm : StronglyMeasurable F :=
      ((G.2.1 (t + 1)).comp_measurable (SmoothInSigmaMeasurePath.measurable_histOf ν (t + 1))).mono
        (E.𝓕.le (t + 1))
    exact Integrable.of_bound hm.aestronglyMeasurable ‖(G : Bd (ℕ × Hist Unit) Z)‖
      (Eventually.of_forall fun ω => by
        have := norm_apply_le (G : Bd (ℕ × Hist Unit) Z) (t + 1, histOf (t + 1) ω)
        exact this)
  have h0 := SmoothInSigmaMeasurePath.solves_ae ν hN hc hlawN hε t
  have h1 := π.comp_condExp_comm (μ := E.μ) (m := E.𝓕 t) hFi
  have hπF : (π ∘ F) = fun ω => A (ypath ψ ybar ε t ω) - B (ypath ψ ybar ε (t + 1) ω) := by
    funext ω
    simp only [Function.comp_apply, hF, SmoothInSigmaMeasurePath.wfun_histOf, hπ]
    rfl
  rw [hπF] at h1
  have h2 := condExp_sub (m := E.𝓕 t) (μ := E.μ) (hint hA t) (hint hB (t + 1))
  have h3 : E.μ[fun ω => A (ypath ψ ybar ε t ω) | E.𝓕 t] = fun ω => A (ypath ψ ybar ε t ω) :=
    condExp_of_stronglyMeasurable (E.𝓕.le t) (hA.comp_stronglyMeasurable (hyt t)) (hint hA t)
  filter_upwards [h0, h1, h2] with ω e0 e1 e2
  have e1' : π (E.μ[F | E.𝓕 t] ω) = E.μ[(fun ω => A (ypath ψ ybar ε t ω)) -
      fun ω => B (ypath ψ ybar ε (t + 1) ω) | E.𝓕 t] ω := e1
  rw [e0, Pi.zero_apply, map_zero, e2, h3] at e1'
  simp only [Pi.sub_apply] at e1'
  linarith


open SmoothInSigmaMeasureProps (discF rem614 prop614_measure) in
open ExpLogCES (crossVar) in
/-- **Woodford (2003), Proposition 6.14, (5.2)–(5.3), p. 456, along the equilibrium OF A MODEL**
on the i.i.d. probability space: as `SmoothInSigmaMeasureProps.prop614_measure`, but the Calvo
law of dispersion and the mean-price/index discrepancy are no longer hypotheses on the path:
they are components of the model's period conditions (`hπD`, `hπP`), and `ψ` is the model's
local equilibrium, so they hold along the path by `static_on_path`. -/
theorem prop614_model (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type}
    [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {α β θ ω σ Φ Ybar : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1)
    (hω : 0 < ω) (hσ : 0 < σ) (hΦ : Φ < 1) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i)
    (hw1 : ∑ i, wt i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y} (hψ : N.LocalSol ybar ψ)
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
    (πD πP : Z →L[ℝ] ℝ)
    (hπD : ∀ a b c x e, πD (N.f (a, b, c, x, e)) =
      DR b - (α * DR c + α / (1 - α) * pibR b ^ 2))
    (hπP : ∀ a b c x e, πP (N.f (a, b, c, x, e)) =
      pibR b - inflR b - discF wt θ (fun i => rpR b i + inflR b) (rpR c)) :
    (fun ε => ∫ ω', rem614 u v wt α β θ ω σ Φ Ybar (fun t => yhR (ypath ψ ybar ε t ω'))
      (fun t => xuR (ypath ψ ybar ε t ω')) (fun t => xvR (ypath ψ ybar ε t ω'))
      (fun t => inflR (ypath ψ ybar ε t ω')) (fun t => gR (ypath ψ ybar ε t ω'))
      (fun t => qR (ypath ψ ybar ε t ω')) ∂(ExpectationsMeasureIID.iidSystem ν0).μ)
      =O[𝓝 0] fun ε => ε ^ 3 := by
  have hlaw := static_on_path hN hc hψ πD hπD
  have hdisc := static_on_path hN hc hψ πP hπP
  refine prop614_measure ν0 hα0 hα1 hβ0 hβ1 hθ hθ1 hω hσ hΦ hw0 hw1 hu hv hucc hvy hvyy
    hψ.base hψ2 cyh crp cxu cxv cg cq ci cp cD zyh zrp zxu zxv zg zq zi zp zD hg hq hV ?_ ?_
  · filter_upwards [hlaw] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)
  · filter_upwards [hdisc] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)


open SmoothInSigmaMeasureProps (discF rem68 prop68_measure) in
open ExpLogCES (crossVar) in
/-- **Woodford (2003), Proposition 6.8, (4.10), p. 423, along the equilibrium OF A MODEL**: as
`SmoothInSigmaMeasureProps.prop68_measure`, but the Calvo law of dispersion and the mean-price
discrepancy are components of the model's period conditions, so they hold along the model's
equilibrium (`static_on_path`) instead of being assumed. -/
theorem prop68_model (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type}
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
    {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f) (hψ : N.LocalSol ybar ψ)
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
    (πD πP : Z →L[ℝ] ℝ)
    (hπD : ∀ a b c x e, πD (N.f (a, b, c, x, e)) = crossVar w (yhR b) / θ ^ 2 -
      (α * (crossVar w (yhR c) / θ ^ 2) + α / (1 - α) * pibR b ^ 2))
    (hπP : ∀ a b c x e, πP (N.f (a, b, c, x, e)) =
      pibR b - inflR b - discF w θ (fun i => rpR b i + inflR b) (rpR c)) :
    (fun ε => ∫ ω', rem68 U Ut v w α β θ Ybar mbar P (fun t => yhR (ypath ψ ybar ε t ω'))
      (fun t => mhR (ypath ψ ybar ε t ω')) (fun t => xuR (ypath ψ ybar ε t ω'))
      (fun t => xvR (ypath ψ ybar ε t ω')) (fun t => dR (ypath ψ ybar ε t ω'))
      (fun t => gR (ypath ψ ybar ε t ω')) (fun t => qR (ypath ψ ybar ε t ω'))
      (fun t => epsR (ypath ψ ybar ε t ω')) (fun t => inflR (ypath ψ ybar ε t ω'))
      ∂(ExpectationsMeasureIID.iidSystem ν0).μ) =O[𝓝 0] fun ε => ε ^ 3  := by
  have hlaw := static_on_path hN hc hψ πD hπD
  have hdisc := static_on_path hN hc hψ πP hπP
  refine prop68_measure ν0 hw0 hw1 hθ hθ1 hα0 hα1 hβ0 hβ1 hUt hmbar hEq hv P hθi hey hΩ hωP hi
    hvb hsat h11 h12 h22 hvy hvyy hψ.base hψ2 cyh crp cmh cd cg cq ceps ci cp cxu cxv zyh zrp
    zmh zd zg zq zeps zi zp zxu zxv hg heps hq hLmd hmd hm hleft ?_ ?_
  · filter_upwards [hlaw] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)
  · filter_upwards [hdisc] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)

omit [CompleteSpace Z] [FiniteDimensional ℝ Y] in
/-- **Woodford (2003), Propositions 6.7–6.8 (when does the one-sided hypothesis `hleft` hold
along the equilibrium?).** If real balances (a readout `m̂` differentiable at `ȳ`, `m̂(ȳ) = 0`)
stay at or below satiation along the equilibrium for ALL small amplitudes `ε` (of either sign),
then their first-order response vanishes identically: `Dm̂(ȳ)(y¹_t(ω)) = 0` at every date and
on every path. So `hleft` of
`SmoothInSigmaMeasureProps.prop67_measure`/`SmoothInSigmaMeasureProps.prop68_measure` holds
only along equilibria in which real balances do not move at first order; whenever they do, it
FAILS (use the two-sided versions of `TidyR6bTwoSided67`). -/
theorem hleft_first_order_zero {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ1 : DifferentiableAt ℝ ψ (pbar ybar)) {mR : Y → ℝ} (hm1 : DifferentiableAt ℝ mR ybar)
    (hm0 : mR ybar = 0) (hleft : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω, mR (ypath ψ ybar ε t ω) ≤ 0)
    (t : ℕ) (ω : ℕ → ℝ) :
    fderiv ℝ mR ybar (SmoothInSigmaMeasureWelfare.y1path ψ ybar t ω) = 0 := by
  have hy := SmoothInSigmaMeasureProps.hasDerivAt_ypath hψ1 t ω
  have h0 : ypath ψ ybar 0 t ω = ybar := SmoothInSigmaMeasureProps.ypath_zero hbase t ω
  have hm : HasFDerivAt mR (fderiv ℝ mR ybar) (ypath ψ ybar 0 t ω) := by
    rw [h0]; exact hm1.hasFDerivAt
  have hg := hm.comp_hasDerivAt (0 : ℝ) hy
  have hmax : IsLocalMax (fun ε => mR (ypath ψ ybar ε t ω)) 0 := by
    filter_upwards [hleft] with ε hε
    simp only [h0, hm0]
    exact hε t ω
  exact hmax.hasDerivAt_eq_zero hg

omit [CompleteSpace Z] [FiniteDimensional ℝ Y] in
/-- Woodford (2003), (4.1) and Proposition 6.7 (**the one-sided hypothesis forces money demand
to be inactive at first order**): with money demand `m̂ = M(Ŷ, î − îᵐ, εᵐ)` and
`DM(0) = (η_y, −η_i, 1)`, `hleft` implies `η_yŶ¹ − η_i(î − îᵐ)¹ + εᵐ¹ = 0` at every date and on
every path. -/
theorem hleft_money_demand {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ1 : DifferentiableAt ℝ ψ (pbar ybar)) {mR YR dR epsR : Y → ℝ} {ηY ηI : ℝ}
    {mdem : ℝ × ℝ × ℝ → ℝ} {Lmd : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hLmd : ∀ a b c, Lmd (a, b, c) = ηY * a - ηI * b + c) (hmd : HasFDerivAt mdem Lmd 0)
    (hT : DifferentiableAt ℝ (fun y => (YR y, dR y, epsR y)) ybar)
    (hT0 : (YR ybar, dR ybar, epsR ybar) = 0) (hm : ∀ y, mR y = mdem (YR y, dR y, epsR y))
    (hm0 : mR ybar = 0) (hleft : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω, mR (ypath ψ ybar ε t ω) ≤ 0)
    (t : ℕ) (ω : ℕ → ℝ) :
    ηY * fderiv ℝ YR ybar (SmoothInSigmaMeasureWelfare.y1path ψ ybar t ω) -
      ηI * fderiv ℝ dR ybar (SmoothInSigmaMeasureWelfare.y1path ψ ybar t ω) +
        fderiv ℝ epsR ybar (SmoothInSigmaMeasureWelfare.y1path ψ ybar t ω) = 0 := by
  set T := fun y => (YR y, dR y, epsR y) with hTd
  have hmd' : HasFDerivAt mdem Lmd (T ybar) := by rw [show T ybar = 0 from hT0]; exact hmd
  have hc := hmd'.comp ybar hT.hasFDerivAt
  have he : mR = mdem ∘ T := funext fun y => hm y
  have hd : DifferentiableAt ℝ mR ybar := by rw [he]; exact hc.differentiableAt
  have h0 := hleft_first_order_zero hbase hψ1 hd hm0 hleft t ω
  rw [he, hc.fderiv] at h0
  have hY : DifferentiableAt ℝ YR ybar := hT.fst
  have hD : DifferentiableAt ℝ dR ybar := hT.snd.fst
  have hE : DifferentiableAt ℝ epsR ybar := hT.snd.snd
  have hTd' : fderiv ℝ T ybar = (fderiv ℝ YR ybar).prod ((fderiv ℝ dR ybar).prod
      (fderiv ℝ epsR ybar)) :=
    (hY.hasFDerivAt.prodMk (hD.hasFDerivAt.prodMk hE.hasFDerivAt)).fderiv
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hTd',
    ContinuousLinearMap.prod_apply, hLmd] at h0
  exact h0

end Woodford.StabilizationWelfare.TidyR6bAlongModel
