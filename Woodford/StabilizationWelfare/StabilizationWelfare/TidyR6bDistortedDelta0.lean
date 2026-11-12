/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5DistortedBranch67

/-!
# Proposition 6.7 around a distorted steady state with `Δ̄ = 0`, for the ACTUAL utility

Woodford (2003), *Interest and Prices*, Chapter 6, §4.1, Proposition 6.7, (4.9), p. 422,
Assumption 6.1, p. 422, and Appendix E.4, (E.15)–(E.18), pp. 699–700.

`TidyR5DistortedBranch67.prop67_on_branch` expands the actual utility around the distorted
steady state `(Ȳ, m̄) = g₀(Φ, Δ̄)` selected by the smooth extension `Ũ`. When `Δ̄ = 0` the
actual utility (flat above satiation, Assumption 6.1) does not determine `m̄`: every `m̄ ≥ mˢ`
satisfies its money condition (`TidyR5DistortedBranch67.foc_actual_flat`). Here the correct
statement for the actual utility is proved.

* `crossVar_shift`: the cross-sectional variance is invariant to a common shift.
* **`prop67_actual_Delta0_any`**: for EVERY reference point `(Ȳ′_b, m̄′_b)` (in particular every
  admissible actual steady state, with any `m̄′ ≥ mˢ`), with deviations `ŷ′, m̂′` measured from
  it, the actual period utility is `t.i.p. − (Ȳu_c/2)·(4.9) + O(s³)`, where (4.9) is evaluated at
  `Ŷ′ + log(Ȳ′/Ȳ_Ũ)`. The hypotheses are on ACTUAL quantities: actual balances weakly below
  satiation, deviations `O(s)` and the money-demand relation (4.1) with balances measured from
  `Ũ`'s selection `m̄_Ũ = g₀(Φ, 0)₂`.
* **`prop67_actual_Delta0_admissible`**: in particular, for every admissible `m̄′ ≥ mˢ` and the
  output selection of `Ũ`, the expansion is EXACTLY that of
  `TidyR5DistortedBranch67.prop67_on_branch`: the choice of
  `m̄` is irrelevant (it cancels against `m̂′`), and the selection that matters is `Ũ`'s
  `m̄_Ũ`, only through the money-demand relation; a different output selection only re-centres
  the target `x*` of (4.9) by `log(Ȳ_Ũ/Ȳ′)` (`loss49_recentre`).
-/

namespace Woodford.StabilizationWelfare.TidyR6bDistortedDelta0

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610 TidyR5Distorted67
open TidyR5DistortedBranch67
open ExpLogCES (crossVar crossMean)

variable {B : Type*} {L : Filter B} {s : B → ℝ}
variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), App. E, p. 693: the cross-sectional variance is invariant to a common
shift of all log outputs. -/
theorem crossVar_shift {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw1 : ∑ i, w i = 1)
    (y : ι → ℝ) (c : ℝ) : crossVar w (fun i => y i + c) = crossVar w y := by
  have hm : crossMean w (fun i => y i + c) = crossMean w y + c := by
    simp only [crossMean, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
  simp only [crossVar, hm]
  congr 1
  funext i
  ring

/-- Woodford (2003), (4.9): shifting output by `c` re-centres the target `x*` of the loss
(the other terms are unchanged). -/
theorem loss49_recentre (P : Transactions.TxParams) (Y c d g q eps Phi Delta V m : ℝ) :
    Transactions.loss49 P (txDist P (Y + c) d g q eps Phi Delta V m) =
      Transactions.omegaMC P * (Y - Transactions.natRate P g q eps -
        (Transactions.xStar P Phi Delta - c)) ^ 2 + P.etaI / P.vbar * (d + Delta) ^ 2 +
        (P.thetaInv + P.omega) * V := by
  simp only [Transactions.loss49, txDist]
  ring

/-- **Woodford (2003), Proposition 6.7, (4.9), p. 422, with `Δ̄ = 0` for the ACTUAL utility,
around ANY reference point.** Let `g₀` be a branch of distorted steady states of `Ũ`
(`branch67`), `Φ_b = O(s)`, `Δ̄ = 0`, and let `(Ȳ′_b, m̄′_b)` be any positive reference point
(e.g. an admissible actual steady state with `m̄′ ≥ mˢ`). Write `Ȳ_Ũ, m̄_Ũ = g₀(Φ_b, 0)`. If the
log outputs relative to `Ȳ_Ũ`, `ŷ′ + log(Ȳ′/Ȳ_Ũ)`, the interest differential, the disturbances
and the shocks are `O(s)`, the money-demand relation (4.1) holds to `O(s²)` for balances measured
from `m̄_Ũ`, and actual balances are at or below satiation, then the actual period utility is
`t.i.p. + Ȳu_c[tip − ½(4.9)] + O(s³)` with (4.9) at `Ŷ′ + log(Ȳ′/Ȳ_Ũ)`. -/
theorem prop67_actual_Delta0_any (hs : Tendsto s L (𝓝 0)) {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ}
    (hUt : ContDiff ℝ 3 Ut) {ms : ℝ} (hms : 0 < ms) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ys : ℝ} (hYs : 0 < Ys)
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹) (hvel : P.vbar * ms = Ys)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0) (huc : fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) ≠ 0)
    (hsat : fderiv ℝ Ut (Ys, ms, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / Ys))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / ms))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 1, 0) =
      -(Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms ^ 2))
    (hvy : dY v (Ys, 0) = fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0))
    (hvyy : dYY v (Ys, 0) = P.omega * dY v (Ys, 0) / Ys)
    {g0 : ℝ × ℝ → ℝ × ℝ} (hg0 : g0 0 = (Ys, ms)) (hgT : Tendsto g0 (𝓝 0) (𝓝 (Ys, ms)))
    (hgS : ∀ᶠ q in 𝓝 0, dY v ((g0 q).1, 0) =
        (1 - q.1) * fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (1, 0, 0) ∧
      fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (0, 1, 0) =
        q.2 * fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (1, 0, 0))
    {Phi : B → ℝ} (hPhi : Phi =O[L] fun b => s b ^ 1)
    {Yp mp : B → ℝ} (hYp : ∀ b, 0 < Yp b) (hmp : ∀ b, 0 < mp b)
    {yd : B → ι → ℝ} {md d g q eps : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms * eps b))
    (hq : ∀ b, dYXi v (Ys, 0) (xv b) = -(P.omega * dY v (Ys, 0) * q b))
    (hyd : (fun b i => yd b i + Real.log (Yp b / (g0 (Phi b, 0)).1)) =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1) (hepsO : eps =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => (md b + Real.log (mp b / (g0 (Phi b, 0)).2)) -
      (P.etaY * (logYidx w θ (yd b) + Real.log (Yp b / (g0 (Phi b, 0)).1)) - P.etaI * d b +
        eps b)) =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, md b + Real.log (mp b / ms) ≤ 0) :
    (fun b => periodUT U v w θ (Yp b) (mp b) (yd b) (md b) (xu b) (xv b) -
      (tipT Ut v Ys ms (xu b) (xv b) + Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) *
        (Transactions.tip P (g b) (q b) (eps b) 0 0 - Transactions.loss49 P
          (txDist P (logYidx w θ (yd b) + Real.log (Yp b / (g0 (Phi b, 0)).1)) (d b) (g b)
            (q b) (eps b) (Phi b) 0 (crossVar w (yd b)) (md b)) / 2))) =O[L]
      fun b => s b ^ 3 := by
  set Yu : B → ℝ := fun b => (g0 (Phi b, 0)).1 with hYu
  set mu : B → ℝ := fun b => (g0 (Phi b, 0)).2 with hmu
  set ydU : B → ι → ℝ := fun b i => yd b i + Real.log (Yp b / Yu b) with hydU
  set mdU : B → ℝ := fun b => md b + Real.log (mp b / mu b) with hmdU
  -- the reference of `Ũ` converges and is eventually positive
  have hq0 : Tendsto (fun b => ((Phi b, 0) : ℝ × ℝ)) L (𝓝 0) :=
    (tendsto_of_o_one hs hPhi).prodMk_nhds tendsto_const_nhds
  have hGT : Tendsto (fun b => g0 (Phi b, 0)) L (𝓝 (Ys, ms)) := hgT.comp hq0
  have hpos : ∀ᶠ b in L, 0 < Yu b ∧ 0 < mu b :=
    ((continuous_fst.tendsto _).comp hGT |>.eventually (lt_mem_nhds hYs)).and
      ((continuous_snd.tendsto _).comp hGT |>.eventually (lt_mem_nhds hms))
  -- the money deviation from `Ũ`'s reference is `O(s)`
  have hYO : (fun b => logYidx w θ (ydU b)) =O[L] fun b => s b ^ 1 :=
    logYidx_o hs hw0 hw1 hθ hyd
  have hmdO : mdU =O[L] fun b => s b ^ 1 := by
    have hlin : (fun b => P.etaY * logYidx w θ (ydU b) - P.etaI * d b + eps b)
        =O[L] fun b => s b ^ 1 :=
      ((hYO.const_mul_left P.etaY).sub (hd.const_mul_left P.etaI)).add hepsO
    have hr' : (fun b => mdU b - (P.etaY * logYidx w θ (ydU b) - P.etaI * d b + eps b))
        =O[L] fun b => s b ^ 1 := by
      refine (o_weaken hs (by norm_num : 1 ≤ 2) hr).congr' ?_ EventuallyEq.rfl
      filter_upwards with b
      simp only [hmdU, hydU, logYidx_shift hw0 hw1 hθ]
      rfl
    exact (hr'.add hlin).congr_left fun b => by ring
  have hrU : (fun b => mdU b - (P.etaY * logYidx w θ (ydU b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2 := by
    refine hr.congr' ?_ EventuallyEq.rfl
    filter_upwards with b
    simp only [hmdU, hydU, logYidx_shift hw0 hw1 hθ]
    rfl
  have hleftU : ∀ᶠ b in L, mdU b + Real.log (mu b / ms) ≤ 0 := by
    filter_upwards [hleft, hpos] with b hb hp
    have : Real.log (mp b / mu b) + Real.log (mu b / ms) = Real.log (mp b / ms) := by
      rw [← Real.log_mul (div_pos (hmp b) hp.2).ne' (div_pos hp.2 hms).ne']
      congr 1; rw [div_mul_div_comm, mul_comm (mu b) ms, mul_div_mul_right _ _ hp.2.ne']
    simp only [hmdU]; linarith
  have hzero : (fun _ : B => (0 : ℝ)) =O[L] fun b => s b ^ 1 := isBigO_zero _ _
  have h := prop67_on_branch hs hw0 hw1 hθ hUt hms hEq hv hYs P hθi hvel hey hΩ hi hvb huc
    hsat h11 h12 h22 hvy hvyy hg0 hgT hgS hPhi hzero hg heps hq hyd hmdO hd hgO hqO hepsO
    hxu hxv hrU (by simpa [Real.exp_zero] using hleftU)
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hpos] with b hp
  have hshift := periodUT_shift hw0 hw1 hθ U v hp.1 hp.2 (hYp b) (hmp b) (yd b) (md b)
    (xu b) (xv b)
  simp only [neg_zero, Real.exp_zero, sub_self]
  rw [hshift, logYidx_shift hw0 hw1 hθ, crossVar_shift hw1, loss49_txDist P _ _ _ _ _ _ _ _
    (mdU b) (md b), loss49_txDist P _ _ _ _ _ _ _ _ (md b) (md b)]

/-- **Woodford (2003), Proposition 6.7 with `Δ̄ = 0`: EVERY admissible `m̄′ ≥ mˢ` gives the same
expansion.** With the output selection of `Ũ` and ANY real-balance reference `m̄′_b > 0` (in
particular every `m̄′ ≥ mˢ`, all of which satisfy the actual money condition,
`TidyR5DistortedBranch67.foc_actual_flat`), the actual period utility is exactly the expansion
of `TidyR5DistortedBranch67.prop67_on_branch`, with balances `m̄′e^{m̂′}`: the choice of `m̄`
cancels, and the selection
that matters is `Ũ`'s `m̄_Ũ`, through the money-demand relation only. -/
theorem prop67_actual_Delta0_admissible (hs : Tendsto s L (𝓝 0)) {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1)
    {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {ms : ℝ} (hms : 0 < ms)
    (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms}) {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ys : ℝ}
    (hYs : 0 < Ys) (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hvel : P.vbar * ms = Ys) (hey : P.etaY = P.chi * P.etaI * P.vbar)
    (hΩ : Transactions.omegaMC P ≠ 0) (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (huc : fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) ≠ 0) (hsat : fderiv ℝ Ut (Ys, ms, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / Ys))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / ms))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 1, 0) =
      -(Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms ^ 2))
    (hvy : dY v (Ys, 0) = fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0))
    (hvyy : dYY v (Ys, 0) = P.omega * dY v (Ys, 0) / Ys)
    {g0 : ℝ × ℝ → ℝ × ℝ} (hg0 : g0 0 = (Ys, ms)) (hgT : Tendsto g0 (𝓝 0) (𝓝 (Ys, ms)))
    (hgS : ∀ᶠ q in 𝓝 0, dY v ((g0 q).1, 0) =
        (1 - q.1) * fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (1, 0, 0) ∧
      fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (0, 1, 0) =
        q.2 * fderiv ℝ Ut ((g0 q).1, (g0 q).2, 0) (1, 0, 0))
    {Phi : B → ℝ} (hPhi : Phi =O[L] fun b => s b ^ 1)
    (hYp : ∀ b, 0 < (g0 (Phi b, 0)).1) {mp : B → ℝ} (hmp : ∀ b, 0 < mp b)
    {yd : B → ι → ℝ} {md d g q eps : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms * eps b))
    (hq : ∀ b, dYXi v (Ys, 0) (xv b) = -(P.omega * dY v (Ys, 0) * q b))
    (hyd : yd =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1) (hepsO : eps =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => (md b + Real.log (mp b / (g0 (Phi b, 0)).2)) -
      (P.etaY * logYidx w θ (yd b) - P.etaI * d b + eps b)) =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, md b + Real.log (mp b / ms) ≤ 0) :
    (fun b => periodUT U v w θ ((g0 (Phi b, 0)).1) (mp b) (yd b) (md b) (xu b) (xv b) -
      (tipT Ut v Ys ms (xu b) (xv b) + Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) *
        (Transactions.tip P (g b) (q b) (eps b) 0 0 - Transactions.loss49 P
          (txDist P (logYidx w θ (yd b)) (d b) (g b) (q b) (eps b) (Phi b) 0
            (crossVar w (yd b)) (md b)) / 2))) =O[L] fun b => s b ^ 3 := by
  have hself : ∀ b, Real.log ((g0 (Phi b, 0)).1 / (g0 (Phi b, 0)).1) = 0 := fun b => by
    rw [div_self (hYp b).ne', Real.log_one]
  have h := prop67_actual_Delta0_any hs hw0 hw1 hθ hUt hms hEq hv hYs P hθi hvel hey hΩ hi hvb
    huc hsat h11 h12 h22 hvy hvyy hg0 hgT hgS hPhi hYp hmp hg heps hq
    (by simpa only [hself, add_zero] using hyd) hd hgO hqO hepsO hxu hxv
    (by simpa only [hself, add_zero] using hr) hleft
  simpa only [hself, add_zero] using h

end Woodford.StabilizationWelfare.TidyR6bDistortedDelta0
