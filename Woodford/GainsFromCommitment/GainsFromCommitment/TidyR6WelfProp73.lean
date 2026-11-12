/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR6WelfFrictions
import GainsFromCommitment.TidyR6WelfCalvo
import GainsFromCommitment.MonetaryFrictions

/-!
# Proposition 7.3 as a statement about actual welfare

Woodford (2003), *Interest and Prices*, Chapter 7, §1.2, Proposition 7.3, pp. 478–479: with
transactions frictions "the quadratic approximation to welfare is given by (1.14)", and the
timelessly optimal policy has constant inflation (1.19) "up to an error of order
`O(‖Δ_{−1}^{1/2}, r̄ − iᵐ‖²)`"; the welfare approximation is Chapter 6, Propositions 6.7–6.8
(§4.1, pp. 420–426), restated in TidyR6WelfFrictions.

## Main results

* `frictions_bridge`: actual discounted utility with transactions frictions (expansion at the
  satiated efficient steady state, one-sided in real balances) along a family of Calvo economies
  equals `TIP − (ε²/2)·Ȳu_cΛ·∑βᵗL_t(first-order plan) + O(ε³)`, with L_t the loss (1.14) and
  weights `λ_x = κ/θ`, `λ_i = η_iλ_x/(v̄Ω_mc)` DERIVED (`κ` the Calvo slope with `Ω_mc`); it
  combines the Chapter 6 results `BridgeExtensions.prop67_actual`,
  `BridgeExtensions.prop68_layerB` and `BridgeExtensions.loss410_first_order`.
* `loss410_eq_basic`: the first-order loss is `MonetaryFrictions.loss` of the basic model (1.1),
  (1.14), (1.15) in Woodford's variables (`x = gap + x*`, `i = (i − iᵐ) + iᵐ`).
* `prop_7_3_welfare`: a policy whose first-order plan is the constant plan (1.19) is at least as
  good, up to `O(ε³)`, as every policy whose first-order plan satisfies (1.1), (1.15) and the
  timeless initial constraints, and strictly better if that plan differs.
* `prop_7_3_welfare_converse`: a constant first-order plan that is at least as good, up to
  `O(ε³)`, as the policies whose first-order plans are its perturbations along the feasible test
  deviation of p. 478 satisfies (1.19).
* `bdd_quad_terms`, `bdd_tipT` (restated from the Chapter 6 project's BridgeLinks).
-/

namespace Woodford.GainsFromCommitment.TidyR6WelfProp73

open Filter Topology Asymptotics
open Woodford.GainsFromCommitment.TidyR6WelfBase Woodford.GainsFromCommitment.TidyR6WelfBridge
  Woodford.GainsFromCommitment.TidyR6WelfFrictions Woodford.GainsFromCommitment.TidyR6WelfCalvo

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {ι : Type*} [Fintype ι]

/-- Woodford (2003), Ch. 6, (E.2)–(E.3), p. 692: the terms `c + Dξ + ½D²(ξ, ξ)` of an expansion
are a bounded sequence when the disturbances are bounded (restated from the Woodford Chapter 6
StabilizationWelfare project, BridgeLinks.bdd_quad_terms). -/
theorem bdd_quad_terms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (D1 : E →L[ℝ] ℝ) (D2 : E →L[ℝ] E →L[ℝ] ℝ) {u : ℕ → E} {M : ℝ} (hu : ∀ t, ‖u t‖ ≤ M) :
    SeqW.Bdd (fun t => c + D1 (u t) + D2 (u t) (u t) / 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hu 0)
  have b1 : SeqW.Bdd (fun t => D1 (u t)) := ⟨‖D1‖ * M, fun t => by
    rw [← Real.norm_eq_abs]
    exact (D1.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hu t) (norm_nonneg _))⟩
  have b2 : SeqW.Bdd (fun t => D2 (u t) (u t)) := ⟨‖D2‖ * M * M, fun t => by
    rw [← Real.norm_eq_abs]
    refine (D2.le_opNorm₂ _ _).trans ?_
    gcongr <;> exact hu t⟩
  exact ((SeqW.Bdd.const c).add b1).add (b2.div_const 2)

omit [NormedSpace ℝ Ξ] in
/-- Woodford (2003), Ch. 6, App. E.4: a disturbance in the last coordinate has the norm of the
disturbance (restated from the Chapter 6 project). -/
theorem norm_triple (x : Ξ) : ‖((0 : ℝ), (0 : ℝ), x)‖ = ‖x‖ := by
  simp [Prod.norm_def]

omit [NormedSpace ℝ Ξ] in
/-- Woodford (2003), Ch. 6, App. E.1: a disturbance in the second coordinate has the norm of the
disturbance (restated from the Chapter 6 project). -/
theorem norm_pair (x : Ξ) : ‖((0 : ℝ), x)‖ = ‖x‖ := by
  simp [Prod.norm_def]

/-- Woodford (2003), Ch. 6, (4.9) and (E.15), p. 699: the t.i.p. of the transactions model is a
bounded sequence when the disturbances are bounded (restated from the Woodford Chapter 6
StabilizationWelfare project, BridgeLinks.bdd_tipT). -/
theorem bdd_tipT (Ut : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (Ybar mbar K : ℝ)
    (P : Transactions.TxParams) {xu xv : ℕ → Ξ} {g q eps : ℕ → ℝ}
    (hxu : ∃ M, ∀ t, ‖xu t‖ ≤ M) (hxv : ∃ M, ∀ t, ‖xv t‖ ≤ M) (hg : SeqW.Bdd g)
    (hq : SeqW.Bdd q) (heps : SeqW.Bdd eps) :
    SeqW.Bdd (fun t => BridgeExtensions.tipT Ut v Ybar mbar (xu t) (xv t) +
      K * Transactions.tip P (g t) (q t) (eps t) 0 0) := by
  obtain ⟨M1, h1⟩ := hxu
  obtain ⟨M2, h2⟩ := hxv
  have b1 := bdd_quad_terms (Ut (Ybar, mbar, 0)) (fderiv ℝ Ut (Ybar, mbar, 0))
    (fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0)) (u := fun t => ((0 : ℝ), (0 : ℝ), xu t))
    (M := M1) fun t => by rw [norm_triple]; exact h1 t
  have b2 := bdd_quad_terms (v (Ybar, 0)) (fderiv ℝ v (Ybar, 0))
    (fderiv ℝ (fderiv ℝ v) (Ybar, 0)) (u := fun t => ((0 : ℝ), xv t))
    (M := M2) fun t => by rw [norm_pair]; exact h2 t
  have b3 : SeqW.Bdd (fun t => Transactions.tip P (g t) (q t) (eps t) 0 0) := by
    unfold Transactions.tip Transactions.natRate Transactions.xStar Transactions.sM
    aesop (add safe apply [SeqW.Bdd.add, SeqW.Bdd.sub, SeqW.Bdd.mul,
      SeqW.Bdd.neg, SeqW.Bdd.div_const, SeqW.Bdd.pow, SeqW.Bdd.const])
  exact (b1.sub b2).add ((SeqW.Bdd.const K).mul b3)

/-- Woodford (2003), Ch. 6, §4.1, (4.9)–(4.11), and Ch. 7, (1.14), p. 476 (**actual welfare with
transactions frictions to `O(ε³)`**). Along a one-parameter family of Calvo economies with
transactions frictions (output cross-section `ŷ`, real balances `m̂ ≤ 0` below satiation, the
interest differential `d = î − îᵐ` (total), disturbances x_u, x_v with composite shocks
`g`, `q`, `εᵐ`, index inflation `π` and mean-price inflation `π̄`, the Calvo dispersion law in
discounted form with initial term `T₀`), every order hypothesis uniform in the date, and
first-order solutions `(π₁, x₁, d₁)` of inflation, the gap from the natural rate and `d`:
`∑βᵗU_t = TIP(ε) − (ε²/2)·Ȳu_cΛ·∑βᵗL_t(π₁, x₁, d₁) + O(ε³)` with L_t the loss (4.10)/(1.14),
weights `λ_x = κ/θ` and `λ_i = η_iλ_x/(v̄Ω_mc)` (`Transactions.lambdaX`, `Transactions.lambdaI`,
derived), `Λ = θ(1 + ωθ)α/((1 − α)(1 − αβ))`, and TIP depending on the disturbances and `T₀`
only. -/
theorem frictions_bridge {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {mbar : ℝ}
    (hmbar : 0 < mbar) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar}) {v : ℝ × Ξ → ℝ}
    (hv : ContDiff ℝ 3 v) {Ybar : ℝ} (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : 0 < Transactions.omegaMC P)
    (hω : 0 ≤ P.omega) (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
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
    {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {yh : ℝ → ℕ → ι → ℝ} {mh d g q eps infl pib : ℝ → ℕ → ℝ} {xu xv : ℝ → ℕ → Ξ}
    {T0 : ℝ → ℝ}
    (hg : ∀ a t, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xu a t) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu a t) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * g a t))
    (heps : ∀ a t, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xu a t) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu a t) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar *
          eps a t))
    (hq : ∀ a t, BridgeExtensions.dYXi v (Ybar, 0) (xv a t) =
      -(P.omega * BridgeExtensions.dY v (Ybar, 0) * q a t))
    (hyh : (fun p : ℝ × ℕ => yh p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1)
    (hmh : (fun p : ℝ × ℕ => mh p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1)
    (hgO : (fun p : ℝ × ℕ => g p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1)
    (hqO : (fun p : ℝ × ℕ => q p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1)
    (hepsO : (fun p : ℝ × ℕ => eps p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1)
    (hxu : (fun p : ℝ × ℕ => xu p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1)
    (hxv : (fun p : ℝ × ℕ => xv p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1)
    (hr : (fun p : ℝ × ℕ => mh p.1 p.2 - (P.etaY * BridgeExtensions.logYidx w θ (yh p.1 p.2) -
      P.etaI * d p.1 p.2 + eps p.1 p.2)) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 2)
    (hleft : ∀ᶠ p in 𝓝 (0 : ℝ) ×ˢ (⊤ : Filter ℕ), mh p.1 p.2 ≤ 0)
    (hxuB : ∀ a, ∃ M, ∀ t, ‖xu a t‖ ≤ M) (hxvB : ∀ a, ∃ M, ∀ t, ‖xv a t‖ ≤ M)
    (hgB : ∀ a, SeqW.Bdd (g a)) (hqB : ∀ a, SeqW.Bdd (q a)) (hepsB : ∀ a, SeqW.Bdd (eps a))
    (hpO : (fun p : ℝ × ℕ => pib p.1 p.2 - infl p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 2)
    (hV : ∀ a, HasSum (fun t => β ^ t * ExpLogCES.crossVar w (yh a t))
      (θ ^ 2 * (Moments.calvoK α β * ∑' t, β ^ t * pib a t ^ 2 + T0 a)))
    {infl1 xg1 d1 : ℕ → ℝ} (hi1 : SeqW.Bdd infl1) (hx1 : SeqW.Bdd xg1) (hd1 : SeqW.Bdd d1)
    (hid : (fun p : ℝ × ℕ => infl p.1 p.2 - p.1 * infl1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 2)
    (hxd : (fun p : ℝ × ℕ => (BridgeExtensions.logYidx w θ (yh p.1 p.2) -
      Transactions.natRate P (g p.1 p.2) (q p.1 p.2) (eps p.1 p.2)) - p.1 * xg1 p.2)
      =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 2)
    (hdd : (fun p : ℝ × ℕ => d p.1 p.2 - p.1 * d1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 2) :
    (fun ε => ∑' t, β ^ t * BridgeExtensions.periodUT U v w θ Ybar mbar (yh ε t) (mh ε t)
        (xu ε t) (xv ε t) -
      ((∑' t, β ^ t * (BridgeExtensions.tipT Ut v Ybar mbar (xu ε t) (xv ε t) +
          Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
            Transactions.tip P (g ε t) (q ε t) (eps ε t) 0 0) -
        Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / 2 *
          ((P.thetaInv + P.omega) * θ ^ 2 * T0 ε)) -
        ε ^ 2 / 2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
          (θ * (1 + P.omega * θ) * Moments.calvoK α β) *
          ∑' t, β ^ t * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t))))
      =O[𝓝 0] fun ε => ε ^ 3 := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
  have hs := BridgeExtensions.tendsto_amp (J := ℕ) he
  have b1 : ∀ {u : ℕ → ℝ}, SeqW.Bdd u →
      (fun p : ℝ × ℕ => u p.2) =O[𝓝 0 ×ˢ ⊤] fun _ => (1 : ℝ) := fun {u} hu => by
    obtain ⟨M, hM⟩ := hu
    exact IsBigO.of_bound M (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, norm_one, mul_one]; exact hM _)
  have fo : ∀ {x : ℝ → ℕ → ℝ} {x1 : ℕ → ℝ}, SeqW.Bdd x1 →
      (fun p : ℝ × ℕ => x p.1 p.2 - p.1 * x1 p.2) =O[𝓝 0 ×ˢ ⊤] (fun p => p.1 ^ 2) →
      (fun p : ℝ × ℕ => x p.1 p.2) =O[𝓝 0 ×ˢ ⊤] fun p => p.1 ^ 1 := fun {x} {x1} h1 hd =>
    ((BridgeExtensions.o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl (fun p : ℝ × ℕ => p.1) _).mul (b1 h1)).congr_right fun p => by
        ring)).congr_left fun p => by ring
  have hdO := fo hd1 hdd
  have hiO := fo hi1 hid
  have hYO := BridgeExtensions.logYidx_o hs hw0 hw1 hθ hyh
  have hW := BridgeExtensions.prop67_actual hs hw0 hw1 hθ hUt hmbar hEq hv P hθi hey hΩ.ne' hi
    hvb hsat h11 h12 h22 hvy hvyy (fun p => hg p.1 p.2) (fun p => heps p.1 p.2)
    (fun p => hq p.1 p.2) hyh hmh hdO hgO hqO hepsO hxu hxv hr hleft
  have h68 := BridgeExtensions.prop68_layerB P hα0 hα1 hβ0 hβ1 hθ0 (by rw [hθi, one_div]) hω
    hΩ hvb he (K := Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (W := fun a t => BridgeExtensions.periodUT U v w θ Ybar mbar (yh a t) (mh a t) (xu a t)
      (xv a t))
    (τ := fun a t => BridgeExtensions.tipT Ut v Ybar mbar (xu a t) (xv a t) +
      Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
        Transactions.tip P (g a t) (q a t) (eps a t) 0 0)
    (Y := fun a t => BridgeExtensions.logYidx w θ (yh a t))
    (V := fun a t => ExpLogCES.crossVar w (yh a t)) (pib := pib) (infl := infl) (T0 := T0)
    (fun a => bdd_tipT Ut v Ybar mbar _ P (hxuB a) (hxvB a) (hgB a) (hqB a) (hepsB a))
    (hW.congr_left fun p => by
      simp only [Transactions.loss49, BridgeExtensions.txSat]; ring)
    hYO hdO hgO hqO hepsO hiO hpO hV
  have hL := BridgeExtensions.loss410_first_order P (α := α) (θ := θ) hβ0 hβ1 he
    (xg := fun a t => BridgeExtensions.logYidx w θ (yh a t) -
      Transactions.natRate P (g a t) (q a t) (eps a t)) hi1 hx1 hd1 hid hxd hdd
  refine (h68.sub (hL.const_mul_left (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / 2 *
    (θ * (1 + P.omega * θ) * Moments.calvoK α β)))).congr_left fun ε => ?_
  ring

/-- Woodford (2003), (1.14), p. 476: the discounted first-order loss of the bridge is the loss
`MonetaryFrictions.loss` of the basic model, with `λ_x = κ/θ`, `λ_i = η_iλ_x/(v̄Ω_mc)`, in
Woodford's variables `x = x₁ + x*` (gap from the natural rate) and `i = d₁ + iᵐ`. -/
theorem loss410_eq_basic (P : Transactions.TxParams) (α β θ σ rbar xs im : ℝ)
    (infl1 xg1 d1 : ℕ → ℝ) :
    ∑' t, β ^ t * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t) =
      MonetaryFrictions.loss (MonetaryFrictions.basic β (Transactions.kappaCalvo P α β θ) σ rbar
        (Transactions.lambdaX P α β θ) (Transactions.lambdaI P (Transactions.lambdaX P α β θ))
        xs im) infl1 (fun t => xg1 t + xs) (fun t => d1 t + im) := by
  unfold MonetaryFrictions.loss MonetaryFrictions.dsum MonetaryFrictions.periodLoss
  refine tsum_congr fun t => ?_
  simp only [MonetaryFrictions.basic, Transactions.loss410]
  ring

/-- Woodford (2003), (4.11), p. 423: `λ_x = κ/θ` with `κ` the Calvo slope (definitional;
`Transactions.lambdaX`). -/
theorem lambdaX_eq (P : Transactions.TxParams) (α β θ : ℝ) :
    Transactions.lambdaX P α β θ = Transactions.kappaCalvo P α β θ / θ := rfl

/-- **Woodford (2003), Proposition 7.3, pp. 478–479, as a statement about actual welfare.** Let
the actual welfare of two policies have the expansion of `frictions_bridge`,
`W_X = T − (ε²/2)K L_X + O(ε³)` with the same `T` and `K > 0`, where L_X is the loss (1.14) of
the first-order plan (`loss410_eq_basic`; `λ_x = κ/θ`, `λ_i > 0` derived). If the first-order plan
of `F` is the constant plan (1.19), `π̄ = −λ_i(r̄ − iᵐ)/(λ_i + β)`, `ı̄ = r̄ + π̄`,
`x̄ = (1 − β)π̄/κ`, and the first-order plan of `G` is bounded, satisfies (1.1) and (1.15) and the
timeless initial constraints `π_0 = π̄`, `x_0 = x̄`, then `F` is at least as good as `G` up to
`O(ε³)`, and strictly better for every small `ε ≠ 0` unless `G`'s plan is the constant plan. -/
theorem prop_7_3_welfare {β κ σ rbar lamx lami xs im : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lamx) (hli : 0 < lami) {WF WG T : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) {πb xb ib : ℝ} {π x i : ℕ → ℝ}
    (hF : (fun ε => WF ε - (T ε - ε ^ 2 / 2 * (K * MonetaryFrictions.loss
      (MonetaryFrictions.basic β κ σ rbar lamx lami xs im) (fun _ => πb) (fun _ => xb)
        (fun _ => ib)))) =O[𝓝 0] fun ε => ε ^ 3)
    (hG : (fun ε => WG ε - (T ε - ε ^ 2 / 2 * (K * MonetaryFrictions.loss
      (MonetaryFrictions.basic β κ σ rbar lamx lami xs im) π x i))) =O[𝓝 0] fun ε => ε ^ 3)
    (h119 : πb = -(lami / (lami + β)) * (rbar - im) ∧ ib = rbar + πb ∧ xb = (1 - β) * πb / κ)
    (hπ : Sequences.Bdd π) (hx : Sequences.Bdd x) (hi : Sequences.Bdd i)
    (hfeas : MonetaryFrictions.Feasible (MonetaryFrictions.basic β κ σ rbar lamx lami xs im)
      π x i) (h0 : π 0 = πb) (h0' : x 0 = xb) :
    WeaklyBetter WF WG ∧ (¬ (∀ t, π t = πb ∧ x t = xb ∧ i t = ib) →
      ∀ᶠ ε in 𝓝[≠] (0 : ℝ), WG ε < WF ε) := by
  have hopt := (MonetaryFrictions.prop_7_3 (xstar := xs) hβ0 hβ1 hκ hσ hlx.le hli.le πb xb
    ib).mpr h119
  have hle : MonetaryFrictions.loss (MonetaryFrictions.basic β κ σ rbar lamx lami xs im)
      (fun _ => πb) (fun _ => xb) (fun _ => ib) ≤
      MonetaryFrictions.loss (MonetaryFrictions.basic β κ σ rbar lamx lami xs im) π x i := by
    have := hopt.2 0 π x i hπ hx hi (fun t _ => hfeas t) h0 (by simp [MonetaryFrictions.basic, h0'])
    simpa using this
  refine ⟨weaklyBetter_of_loss_le hK.le hF hG hle, fun hne => ?_⟩
  refine eventually_lt_of_loss_lt hK hF hG (lt_of_le_of_ne hle fun heq => hne ?_)
  have h := MonetaryFrictions.prop_7_3_unique hβ0 hβ1 hκ hσ hlx hli hopt 0 hπ hx hi
    (fun t _ => hfeas t) h0 h0' (by simpa using heq.symm.le)
  intro t
  exact h t (Nat.zero_le t)

/-- **Woodford (2003), Proposition 7.3, pp. 478–479, as a statement about actual welfare
(necessity of (1.19) "up to an error of order `O(‖Δ_{−1}^{1/2}, r̄ − iᵐ‖²)`").** Let the first-order
plan of `F` be a feasible constant plan `(π̄, x̄, ı̄)`, and suppose that for every `s ∈ ℝ` there is
a policy G_s whose first-order plan is the constant plan perturbed by `s` times the feasible test
deviation of p. 478 (`MonetaryFrictions.pertPi`, pertX, pertI, which preserves the initial
constraints), with welfare expansion as in `frictions_bridge` (same `T`, `K > 0`). If `F` is at
least as good as every G_s up to `O(ε³)`, then the plan of `F` is (1.19):
`π̄ = −λ_i(r̄ − iᵐ)/(λ_i + β)`, `ı̄ = r̄ + π̄`, `x̄ = (1 − β)π̄/κ`. -/
theorem prop_7_3_welfare_converse {β κ σ rbar lamx lami xs im : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lamx) (hli : 0 ≤ lami) {WF T : ℝ → ℝ} {K : ℝ}
    (hK : 0 < K) {πb xb ib : ℝ}
    (hFfeas : MonetaryFrictions.Feasible (MonetaryFrictions.basic β κ σ rbar lamx lami xs im)
      (fun _ => πb) (fun _ => xb) (fun _ => ib))
    (hF : (fun ε => WF ε - (T ε - ε ^ 2 / 2 * (K * MonetaryFrictions.loss
      (MonetaryFrictions.basic β κ σ rbar lamx lami xs im) (fun _ => πb) (fun _ => xb)
        (fun _ => ib)))) =O[𝓝 0] fun ε => ε ^ 3)
    (hG : ∀ s : ℝ, ∃ WG : ℝ → ℝ, (fun ε => WG ε - (T ε - ε ^ 2 / 2 * (K *
      MonetaryFrictions.loss (MonetaryFrictions.basic β κ σ rbar lamx lami xs im)
        (fun t => πb + s * MonetaryFrictions.pertPi
          (MonetaryFrictions.basic β κ σ rbar lamx lami xs im) t)
        (fun t => xb + s * MonetaryFrictions.pertX
          (MonetaryFrictions.basic β κ σ rbar lamx lami xs im) t)
        (fun t => ib + s * MonetaryFrictions.pertI
          (MonetaryFrictions.basic β κ σ rbar lamx lami xs im) t)))) =O[𝓝 0] (fun ε => ε ^ 3) ∧
      WeaklyBetter WF WG) :
    πb = -(lami / (lami + β)) * (rbar - im) ∧ ib = rbar + πb ∧ xb = (1 - β) * πb / κ := by
  set Mb := MonetaryFrictions.basic β κ σ rbar lamx lami xs im with hMb
  have hβ0' : 0 < Mb.β := hβ0
  have hβ1' : Mb.β < 1 := hβ1
  have hb0 := MonetaryFrictions.pert_zero_from Mb
  have hbp : Sequences.Bdd (MonetaryFrictions.pertPi Mb) :=
    Sequences.bdd_of_zero_from 4 (fun t ht => (hb0 t ht).1)
  have hbx : Sequences.Bdd (MonetaryFrictions.pertX Mb) :=
    Sequences.bdd_of_zero_from 4 (fun t ht => (hb0 t ht).2.1)
  have hbi : Sequences.Bdd (MonetaryFrictions.pertI Mb) :=
    Sequences.bdd_of_zero_from 4 (fun t ht => (hb0 t ht).2.2)
  have hall : ∀ s : ℝ, 0 ≤ 2 * s * MonetaryFrictions.dsum Mb.β (fun t =>
      πb * MonetaryFrictions.pertPi Mb t +
        Mb.lamx * (xb - Mb.xstar) * MonetaryFrictions.pertX Mb t +
        Mb.lami * (ib - Mb.im) * MonetaryFrictions.pertI Mb t) +
      s ^ 2 * MonetaryFrictions.dsum Mb.β (MonetaryFrictions.quad Mb (MonetaryFrictions.pertPi Mb)
        (MonetaryFrictions.pertX Mb) (MonetaryFrictions.pertI Mb)) := by
    intro s
    obtain ⟨WG, hWG, hwb⟩ := hG s
    have hle := loss_le_of_weaklyBetter hK hF hWG hwb
    rw [MonetaryFrictions.loss_expand hβ0' hβ1' s (Sequences.bdd_const πb)
      (Sequences.bdd_const xb) (Sequences.bdd_const ib) hbp hbx hbi] at hle
    linarith
  have hGz := MonetaryFrictions.eq_zero_of_forall_nonneg hall
  rw [MonetaryFrictions.dsum_pert] at hGz
  have hne : Mb.β ^ 2 * Mb.κ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ0.ne') hκ.ne'
  have hc : MonetaryFrictions.TimelessCond Mb πb xb ib := by
    have := (mul_eq_zero.mp hGz).resolve_left hne
    unfold MonetaryFrictions.TimelessCond
    linarith
  have hopt := MonetaryFrictions.timelesslyOptimal_of_cond hβ0' hβ1' hlx hli hσ.ne' hκ.ne'
    hFfeas hc
  exact (MonetaryFrictions.prop_7_3 (xstar := xs) hβ0 hβ1 hκ hσ hlx hli πb xb ib).mp hopt

end Woodford.GainsFromCommitment.TidyR6WelfProp73
