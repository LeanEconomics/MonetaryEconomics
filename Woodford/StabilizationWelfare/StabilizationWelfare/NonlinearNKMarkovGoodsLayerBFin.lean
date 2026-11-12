/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovGoodsLayerB

/-!
# The finite weighted cross-section as the special case of Proposition 6.15 over goods

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (Proposition 6.15) and App. E.2.

**`prop615_goods_layerB_of_M`** is `BridgeLinks.prop615_goods_layerB` VERBATIM (the same
statement, with its finite-style hypotheses: probability weights `wt`, sup-norm uniform orders
`UProc`, initial relative prices `cen wt`), DERIVED from
`NonlinearNKMarkovGoodsLayerB.prop615_goods_layerBM` at the goods probability space
`γ = BridgeLinks.wMeasure wt`, through `NonlinearNKMarkovGoodsLayerB.special_case`: every
function on a finite discrete space is measurable, the sup-norm order of the cross-section gives
the order uniformly in the goods, and the output index, price index, period utility and
variance over `wMeasure wt` are the finite weighted ones.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovGoodsLayerBFin

open MeasureTheory Filter Topology Asymptotics
open ExpLogCES (crossMean crossVar)
open BridgeLinks (wMeasure logP cen)
open NonlinearNKMarkovGoodsLayerB

variable {ι : Type*} [Fintype ι]
variable {Ξ' : Type*} [NormedAddCommGroup Ξ'] [NormedSpace ℝ Ξ']
variable {A : Type*} {l : Filter A} {e : A → ℝ}
variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), pp. 458–459, Layer B from the finite
goods population (the statement of `BridgeLinks.prop615_goods_layerB`), obtained as the special
case `γ = wMeasure wt` of the goods-probability-space theorem
`NonlinearNKMarkovGoodsLayerB.prop615_goods_layerBM`. -/
theorem prop615_goods_layerB_of_M [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1)
    (hMd : LargeDistortions.Mden ω σ sC Φ ≠ 0) (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1) {u v : ℝ × Ξ' → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 3 v)
    (hucc : BridgeExtensions.dYY u (Ybar, 0) = -(σ * BridgeExtensions.dY u (Ybar, 0) / Ybar))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = (1 - Φ) * BridgeExtensions.dY u (Ybar, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = ω * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ'}
    {xr F K f k G cb q muw tau : A → ℕ → Ω → ℝ} {X : A → ℕ → Ω → ι → ℝ}
    {Rs : A → Ω → ℕ → Set ι} {ps : A → Ω → ℕ → ℝ} {LY LP : A → ℕ → Ω → ℝ}
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC
      (fun t z => logP wt θ (X a (t + 1) z) - logP wt θ (X a t z)) (xr a) (F a) (K a) (f a)
      (k a) (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a)
      (tau a))
    (hyh : BridgeExtensions.UProc l yh fun a => e a ^ 1)
    (hxu : BridgeExtensions.UProc l xu fun a => e a ^ 1)
    (hxv : BridgeExtensions.UProc l xv fun a => e a ^ 1)
    (hiO : BridgeExtensions.UProc l (fun a t z => logP wt θ (X a (t + 1) z) -
      logP wt θ (X a t z)) fun a => e a ^ 1)
    (hxrO : BridgeExtensions.UProc l xr fun a => e a ^ 1)
    (hFO : BridgeExtensions.UProc l F fun a => e a ^ 1)
    (hKO : BridgeExtensions.UProc l K fun a => e a ^ 1)
    (hfO : BridgeExtensions.UProc l f fun a => e a ^ 1)
    (hkO : BridgeExtensions.UProc l k fun a => e a ^ 1)
    (hGO : BridgeExtensions.UProc l G fun a => e a ^ 1)
    (hcbO : BridgeExtensions.UProc l cb fun a => e a ^ 1)
    (hqO : BridgeExtensions.UProc l q fun a => e a ^ 1)
    (hmO : BridgeExtensions.UProc l muw fun a => e a ^ 1)
    (htO : BridgeExtensions.UProc l tau fun a => e a ^ 1)
    (hg : ∀ a t z, BridgeExtensions.dYXi u (Ybar, 0) (xu a t z) =
      σ * BridgeExtensions.dY u (Ybar, 0) * (G a t z + sC * cb a t z))
    (hq : ∀ a t z, BridgeExtensions.dYXi v (Ybar, 0) (xv a t z) =
      -(ω * BridgeExtensions.dY v (Ybar, 0) * q a t z))
    (hG : ∀ a z, Links.GoodsPop.Calvo (wMeasure wt) α (fun t => X a t z) (Rs a z) (ps a z)
      fun _ => 0)
    (hdem : ∀ a t z i, yh a t z i = LY a t z - θ * (X a (t + 1) z i - LP a t z))
    (hX0 : BridgeExtensions.UProc l (fun a (_ : ℕ) z => cen wt (X a 0 z)) fun a => e a ^ 1)
    (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => BridgeExtensions.periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (BridgeExtensions.W0615 𝔼 α β θ ω σ Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => logP wt θ (X a (t + 1) z) - logP wt θ (X a t z)) (F a) (K a) w0 -
        LargeDistortions.OmegaTilde Ybar (BridgeExtensions.dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ
            (fun t z => logP wt θ (X a (t + 1) z) - logP wt θ (X a t z))
            (fun t z => BridgeExtensions.logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a)
            (tau a)) w0 +
        BridgeExtensions.tip615 𝔼 α β θ ω σ sC Φ Ybar (BridgeExtensions.dY u (Ybar, 0))
          (fun t z => BridgeExtensions.tip51 u v Ybar (xu a t z) (xv a t z))
          (fun t z => crossVar wt (X a t z)) (G a) (cb a) (q a) (muw a) (tau a) w0))
      =O[l] fun a => e a ^ 3 := by
  have hP := BridgeLinks.isProbabilityMeasure_wMeasure hw0 hw1
  have hym : ∀ a t z, Measurable (yh a t z) := fun _ _ _ => measurable_of_finite _
  have hXm : ∀ a t z, Measurable (X a t z) := fun _ _ _ => measurable_of_finite _
  -- the order of the cross-section, uniformly in the goods
  have hyh' : (fun p : (A × (ℕ × Ω)) × ι => yh p.1.1 p.1.2.1 p.1.2.2 p.2) =O[(l ×ˢ ⊤) ×ˢ ⊤]
      fun p => e p.1.1 ^ 1 := by
    obtain ⟨C, hC⟩ := hyh.bound
    refine IsBigO.of_bound C ((tendsto_fst.eventually hC).mono fun p hp => ?_)
    exact (norm_le_pi_norm (yh p.1.1 p.1.2.1 p.1.2.2) p.2).trans hp
  -- the initial relative prices
  have hX0' : ∃ C0, ∀ᶠ a in l, ∀ z i,
      |X a 0 z i - CrossSection.crossMean (wMeasure wt) (X a 0 z)| ≤ C0 * |e a| := by
    obtain ⟨C, hC⟩ := hX0.bound
    refine ⟨C, (ev_prod_top hC).mono fun a ha z i => ?_⟩
    have h := (norm_le_pi_norm (cen wt (X a 0 z)) i).trans (ha (0, z))
    rw [BridgeLinks.crossMean_wMeasure hw0]
    simpa [cen, Real.norm_eq_abs] using h
  have hPe : ∀ q : ι → ℝ, logP wt θ q = logPM (wMeasure wt) θ q := fun q =>
    (logPM_wMeasure hw0 hw1 θ q).symm
  have hYe : ∀ q : ι → ℝ, BridgeExtensions.logYidx wt θ q = logYM (wMeasure wt) θ q := fun q =>
    (logYM_wMeasure hw0 hw1 θ q).symm
  simp only [hPe, hYe] at hM hiO
  have key := prop615_goods_layerBM (wMeasure wt) 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd he
    hu hv hucc hvy hvyy hM hym hXm hyh' hxu hxv hiO hxrO hFO hKO hfO hkO hGO hcbO hqO hmO htO hg hq
    hG hdem hX0' w0
  simp only [periodUM_wMeasure hw0 hw1, logPM_wMeasure hw0 hw1, logYM_wMeasure hw0 hw1,
    BridgeLinks.crossVar_wMeasure hw0] at key
  exact key

end Woodford.StabilizationWelfare.NonlinearNKMarkovGoodsLayerBFin
