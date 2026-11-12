/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR6WelfBase

/-!
# Chapter 6 welfare machinery for Chapter 7 (II): the Calvo bridge

Woodford (2003), *Interest and Prices*, Chapter 6, §§1–2 and §4.1 (pp. 383–405, 420–426) and
Appendix E.1–E.4 (pp. 692–699): the second-order welfare machinery that Chapter 7 uses
("the approximation to welfare of Chapter 6", Woodford (2003), p. 471, fn. 6), restated from
the Woodford Chapter 6 StabilizationWelfare project with the namespace renamed (the original
module names are kept as nested namespaces; that project's Sequences is SeqW here).
Only the declarations needed by the Chapter 7 welfare bridge are copied; proofs are verbatim.
-/

namespace Woodford.GainsFromCommitment.TidyR6WelfBridge

open Woodford.GainsFromCommitment.TidyR6WelfBase

namespace BridgeCore

open Filter Topology Asymptotics
open ExpLogCES (crossMean crossVar cumulant cesIndex expRem)
open Prop61 (Tu Tv Ru Rv natLin xStarLin tipA R3 lossQ sigmaInvEl omegaEl gShock qShock)
variable {α : Type*} {l : Filter α} {s : α → ℝ}

/-- Woodford (2003), (2.11), p. 395 (bookkeeping of orders): `sᵇ = O(sᵃ)` for `a ≤ b` when
`s → 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem pow_isBigO_pow (hs : Tendsto s l (𝓝 0)) {a b : ℕ} (hab : a ≤ b) :
    (fun x => s x ^ b) =O[l] (fun x => s x ^ a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : (fun x => s x ^ k) =O[l] (fun _ => (1 : ℝ)) := (hs.pow k).isBigO_one ℝ
  exact ((isBigO_refl (fun x => s x ^ a) l).mul h1).congr (fun x => by ring) (fun x => by ring)

/-- Woodford (2003), (2.11), p. 395: orders multiply, `O(sᵃ) · O(sᵇ) = O(sᶜ)` for
`a + b = c`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem isBigO_pow_mul {f g : α → ℝ} {a b c : ℕ} (hf : f =O[l] fun x => s x ^ a)
    (hg : g =O[l] fun x => s x ^ b) (habc : a + b = c) :
    (fun x => f x * g x) =O[l] fun x => s x ^ c :=
  (hf.mul hg).congr_right fun x => by rw [← habc, pow_add]

/-- Woodford (2003), App. E (`(a + O(2))² = a² + O(3)`, the lemma L-square of the survey): if
`f − s f₁ = O(s²)` with `f₁` bounded, then `f² − s² f₁² = O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem sq_sub_sq_isBigO (hs : Tendsto s l (𝓝 0)) {f f1 : α → ℝ}
    (h : (fun x => f x - s x * f1 x) =O[l] fun x => s x ^ 2)
    (h1 : f1 =O[l] fun _ => (1 : ℝ)) :
    (fun x => f x ^ 2 - s x ^ 2 * f1 x ^ 2) =O[l] fun x => s x ^ 3 := by
  have hs1 : (fun x => s x * f1 x) =O[l] fun x => s x ^ 1 :=
    ((isBigO_refl s l).mul h1).congr (fun x => rfl) (fun x => by ring)
  have hsum : (fun x => f x + s x * f1 x) =O[l] fun x => s x ^ 1 :=
    ((h.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))).add (hs1.const_mul_left 2)).congr_left
      fun x => by ring
  exact (isBigO_pow_mul h hsum (by norm_num : 2 + 1 = 3)).congr_left fun x => by ring

/-- Woodford (2003), App. E.1, p. 693 (T2): along any family with `Y = O(s)`, the remainder of
`e^Y = 1 + Y + Y²/2 + expRem Y` is `O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem expRem_isBigO (hs : Tendsto s l (𝓝 0)) {Y : α → ℝ} (hY : Y =O[l] s) :
    (fun x => expRem (Y x)) =O[l] fun x => s x ^ 3 := by
  have hYt : Tendsto Y l (𝓝 0) := hY.trans_tendsto hs
  have h := ExpLogCES.exp_taylor2_isBigO.comp_tendsto hYt
  refine (h.trans (hY.pow 3)).congr_left fun x => ?_
  simp only [Function.comp, expRem]
  ring

/-- Woodford (2003), App. E.1, p. 693: `e^Y − 1 = O(Y)`, so `Y = O(s)` gives `e^Y − 1 = O(s)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem exp_sub_one_isBigO (hs : Tendsto s l (𝓝 0)) {Y : α → ℝ} (hY : Y =O[l] s) :
    (fun x => Real.exp (Y x) - 1) =O[l] s := by
  have hYt : Tendsto Y l (𝓝 0) := hY.trans_tendsto hs
  have h := (Real.hasDerivAt_exp 0).isBigO_sub.comp_tendsto hYt
  refine (h.trans (hY.congr_left fun x => by simp)).congr_left fun x => ?_
  simp

/-- Woodford (2003), App. E.2, p. 695 (survey error 25): the filter "uniformly in the date `t`,
as the amplitude `ε → 0`", `⊤ ×ˢ 𝓝 0` on `ℕ × ℝ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
abbrev unif : Filter (ℕ × ℝ) := (⊤ : Filter ℕ) ×ˢ 𝓝 (0 : ℝ)

/-- Woodford (2003), App. E.2, p. 695: the amplitude tends to zero along `unif`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem tendsto_unif : Tendsto (fun p : ℕ × ℝ => p.2) unif (𝓝 0) := tendsto_snd

/-- Woodford (2003), App. E.2, p. 695 and survey error 25 (**what the uniformity hypothesis
says**): `f =O[unif] g` iff there is one constant `C` with `‖f t ε‖ ≤ C ‖g ε‖` for every date `t`
and every small `ε`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem isBigO_unif_iff {E : Type*} [Norm E] {f : ℕ → ℝ → E} {g : ℝ → ℝ} :
    (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => g p.2) ↔
      ∃ C, ∀ᶠ ε in 𝓝 0, ∀ t, ‖f t ε‖ ≤ C * ‖g ε‖ := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h.bound
    refine ⟨C, ?_⟩
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 hC
    rw [eventually_top] at hpa
    filter_upwards [hpb] with ε hε t
    exact hab (hpa t) hε
  · rintro ⟨C, hC⟩
    exact IsBigO.of_bound C ((hC.prod_inr _).mono fun p hp => hp p.1)

/-- Woodford (2003), App. E.2, p. 695: a bound uniform in `t` holds at each fixed date.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem isBigO_of_unif {E : Type*} [Norm E] {f : ℕ → ℝ → E} {g : ℝ → ℝ}
    (h : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => g p.2)) (t : ℕ) :
    (fun ε => f t ε) =O[𝓝 0] g := by
  obtain ⟨C, hC⟩ := isBigO_unif_iff.1 h
  exact IsBigO.of_bound C (hC.mono fun ε hε => hε t)

/-- Woodford (2003), App. E.3, p. 697: a sequence that is `O(g)` uniformly in `t` is a bounded
sequence for every small `ε`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem bdd_of_unif {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => g p.2)) :
    ∀ᶠ ε in 𝓝 0, SeqW.Bdd (fun t => f t ε) := by
  obtain ⟨C, hC⟩ := isBigO_unif_iff.1 h
  filter_upwards [hC] with ε hε
  exact ⟨C * ‖g ε‖, fun t => by simpa [Real.norm_eq_abs] using hε t⟩

/-- Woodford (2003), (2.21), p. 400, and survey error 25 (**discounted sums of uniformly small
remainders**): if `f t ε = O(εⁿ)` uniformly in `t` and `0 ≤ β < 1`, then
`∑ βᵗ f t ε = O(εⁿ)`, with constant `C/(1 − β)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem tsum_isBigO_of_unif {f : ℕ → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {n : ℕ}
    (hf : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => p.2 ^ n)) :
    (fun ε => ∑' t, β ^ t * f t ε) =O[𝓝 0] (fun ε => ε ^ n) := by
  obtain ⟨C, hC⟩ := (isBigO_unif_iff (g := fun ε => ε ^ n)).1 hf
  refine IsBigO.of_bound (C / (1 - β)) ?_
  filter_upwards [hC] with ε hε
  have h := SeqW.abs_tsum_le (f := fun t => f t ε) (B := C * ‖ε ^ n‖)
    (fun t => by simpa [Real.norm_eq_abs] using hε t) hβ0 hβ1
  rw [Real.norm_eq_abs]
  calc _ ≤ C * ‖ε ^ n‖ / (1 - β) := h
    _ = C / (1 - β) * ‖ε ^ n‖ := by ring

/-- Woodford (2003), §1, pp. 386–389 and §2 (the use of the quadratic losses): if welfare under
policies `A` and `B` satisfies `W_X ε = tip ε − (ε²/2) k L_X + O(ε³)` with the SAME
policy-independent part tip (any function of `ε`), `k > 0` and `L_A < L_B`, then `A` is
strictly better for all small `ε > 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem ranking_of_tip {WA WB tip : ℝ → ℝ} {k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun ε => WA ε - (tip ε + ε ^ 2 / 2 * (-(k * LA)))) =O[𝓝 0] (fun ε => ε ^ 3))
    (hB : (fun ε => WB ε - (tip ε + ε ^ 2 / 2 * (-(k * LB)))) =O[𝓝 0] (fun ε => ε ^ 3))
    (hL : LA < LB) : ∀ᶠ ε in 𝓝[>] 0, WB ε < WA ε := by
  have h := OneParamTaylor.welfare_ranking_of_loss (WA := fun ε => WA ε - tip ε)
    (WB := fun ε => WB ε - tip ε) (w0 := 0) (w1 := 0) hk
    (hA.congr_left fun ε => by ring) (hB.congr_left fun ε => by ring) hL
  filter_upwards [h] with ε hε
  linarith

/-- Woodford (2003), App. E.2 (matching Taylor coefficients): if `ε² c = O(ε³)` then `c = 0`;
the `ε²` coefficient of an expansion with cubic remainder is unique.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem coeff_two_unique {c : ℝ} (h : (fun ε : ℝ => ε ^ 2 * c) =O[𝓝 0] (fun ε => ε ^ 3)) :
    c = 0 := by
  by_contra hc
  apply OneParamTaylor.sq_not_isBigO_cube
  refine (h.const_mul_left c⁻¹).congr_left fun ε => ?_
  field_simp

/-- Woodford (2003), §1, p. 385 (expected welfare over a finite state space): if in every state
`ω` welfare is `W ω ε = T ω ε − (ε²/2) k L ω + O(ε³)`, then expected welfare is
`E W = E T − (ε²/2) k E L + O(ε³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem expect_bridge {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) {W T : Ω → ℝ → ℝ} {L : Ω → ℝ}
    {k : ℝ}
    (h : ∀ ω, (fun ε => W ω ε - (T ω ε + ε ^ 2 / 2 * (-(k * L ω)))) =O[𝓝 0]
      (fun ε => ε ^ 3)) :
    (fun ε => OneParamTaylor.expect p (fun ω => W ω ε) -
      (OneParamTaylor.expect p (fun ω => T ω ε) +
        ε ^ 2 / 2 * (-(k * OneParamTaylor.expect p L)))) =O[𝓝 0] (fun ε => ε ^ 3) := by
  refine (OneParamTaylor.isBigO_expect p h).congr_left fun ε => ?_
  have e : ∀ ω, p ω * (W ω ε - (T ω ε + ε ^ 2 / 2 * (-(k * L ω)))) =
      p ω * W ω ε - p ω * T ω ε + ε ^ 2 / 2 * k * (p ω * L ω) := fun ω => by ring
  simp only [OneParamTaylor.expect, smul_eq_mul, e, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.2), p. 692: the gradient `DU(ȳ, 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def D1 (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ × Ξ →L[ℝ] ℝ := fderiv ℝ U (yb, 0)

/-- Woodford (2003), (E.2), p. 692: the Hessian `D²U(ȳ, 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def D2 (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ × Ξ →L[ℝ] ℝ × Ξ →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ U) (yb, 0)

/-- Woodford (2003), (E.2), p. 692: `u_c = U_y(ȳ, 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def slope (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ := D1 U yb (1, 0)

/-- Woodford (2003), (E.2), p. 692: `u_cc = U_yy(ȳ, 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def curv (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ := D2 U yb (1, 0) (1, 0)

/-- Woodford (2003), (E.2), p. 692: `u_ξ ξ = U_ξ(ȳ, 0) ξ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def lin (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ := D1 U yb (0, ξ)

/-- Woodford (2003), (E.2), p. 692: `u_cξ ξ`, the (symmetrised) mixed second derivative.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def cross (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ :=
  (D2 U yb (1, 0) (0, ξ) + D2 U yb (0, ξ) (1, 0)) / 2

/-- Woodford (2003), (E.2), p. 692: `ξ′ u_ξξ ξ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def quad (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ := D2 U yb (0, ξ) (0, ξ)

/-- Woodford (2003), (E.2), p. 692: the terms of the expansion independent of policy,
`Ū + u_ξ ξ + ½ ξ′u_ξξ ξ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def tip0 (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ :=
  U (yb, 0) + lin U yb ξ + quad U yb ξ / 2

/-- Woodford (2003), eq. (1.2), p. 385 and (E.2), p. 692: the quadratic approximation of
`U` at `(ȳ, 0)` in the direction `(a, ξ)` is the polynomial `Prop61.uTaylor` of (E.2) with
coefficients `slope`, `curv`, `lin`, `cross`, `quad`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem quadApprox_pair (U : ℝ × Ξ → ℝ) (yb a : ℝ) (ξ : Ξ) :
    ApproxTheory.quadApprox (U (yb, 0)) (fderiv ℝ U (yb, 0)) (fderiv ℝ (fderiv ℝ U) (yb, 0))
        (a, ξ) =
      Prop61.uTaylor (U (yb, 0)) (slope U yb) (curv U yb) (lin U yb ξ) (cross U yb ξ)
        (quad U yb ξ) a := by
  have hz : ((a, ξ) : ℝ × Ξ) = a • ((1 : ℝ), (0 : Ξ)) + ((0 : ℝ), ξ) := by
    ext <;> simp
  rw [hz]
  unfold ApproxTheory.quadApprox Prop61.uTaylor slope curv lin cross quad D1 D2
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  ring

omit [NormedSpace ℝ Ξ] in
/-- Woodford (2003), App. E: `‖(0, ξ)‖ = ‖ξ‖`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem norm_inr (ξ : Ξ) : ‖((0 : ℝ), ξ)‖ = ‖ξ‖ := by
  rw [Prod.norm_def]
  simp

omit [NormedSpace ℝ Ξ] in
/-- Woodford (2003), App. E: `‖(1, 0)‖ = 1`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem norm_inl_one : ‖((1 : ℝ), (0 : Ξ))‖ = 1 := by
  rw [Prod.norm_def]
  simp

/-- Woodford (2003), (E.2): `|u_ξ ξ| ≤ ‖DU‖ ‖ξ‖`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_lin_le (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : |lin U yb ξ| ≤ ‖D1 U yb‖ * ‖ξ‖ := by
  have h := (D1 U yb).le_opNorm ((0 : ℝ), ξ)
  rwa [norm_inr, Real.norm_eq_abs] at h

/-- Woodford (2003), (E.2): `|u_cξ ξ| ≤ ‖D²U‖ ‖ξ‖`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_cross_le (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) :
    |cross U yb ξ| ≤ ‖D2 U yb‖ * ‖ξ‖ := by
  have h1 := (D2 U yb).le_opNorm₂ ((1 : ℝ), (0 : Ξ)) ((0 : ℝ), ξ)
  have h2 := (D2 U yb).le_opNorm₂ ((0 : ℝ), ξ) ((1 : ℝ), (0 : Ξ))
  rw [norm_inr, norm_inl_one, Real.norm_eq_abs] at h1 h2
  have h3 := abs_add_le (D2 U yb (1, 0) (0, ξ)) (D2 U yb (0, ξ) (1, 0))
  unfold cross
  rw [abs_div, abs_two]
  have e1 : ‖D2 U yb‖ * 1 * ‖ξ‖ = ‖D2 U yb‖ * ‖ξ‖ := by ring
  have e2 : ‖D2 U yb‖ * ‖ξ‖ * 1 = ‖D2 U yb‖ * ‖ξ‖ := by ring
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- Woodford (2003), (E.2): `|ξ′u_ξξ ξ| ≤ ‖D²U‖ ‖ξ‖²`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem abs_quad_le (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : |quad U yb ξ| ≤ ‖D2 U yb‖ * ‖ξ‖ ^ 2 := by
  have h := (D2 U yb).le_opNorm₂ ((0 : ℝ), ξ) ((0 : ℝ), ξ)
  rw [norm_inr, Real.norm_eq_abs] at h
  unfold quad
  calc _ ≤ _ := h
    _ = _ := by ring

/-- Woodford (2003), (E.2): `u_ξ (r ξ) = r u_ξ ξ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem lin_smul (U : ℝ × Ξ → ℝ) (yb r : ℝ) (ξ : Ξ) : lin U yb (r • ξ) = r * lin U yb ξ := by
  unfold lin
  rw [show ((0 : ℝ), r • ξ) = r • ((0 : ℝ), ξ) by simp, map_smul, smul_eq_mul]

/-- Woodford (2003), (E.2): `u_cξ (r ξ) = r u_cξ ξ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem cross_smul (U : ℝ × Ξ → ℝ) (yb r : ℝ) (ξ : Ξ) :
    cross U yb (r • ξ) = r * cross U yb ξ := by
  unfold cross
  rw [show ((0 : ℝ), r • ξ) = r • ((0 : ℝ), ξ) by simp]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.2): `(r ξ)′u_ξξ (r ξ) = r² ξ′u_ξξ ξ`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem quad_smul (U : ℝ × Ξ → ℝ) (yb r : ℝ) (ξ : Ξ) :
    quad U yb (r • ξ) = r ^ 2 * quad U yb ξ := by
  unfold quad
  rw [show ((0 : ℝ), r • ξ) = r • ((0 : ℝ), ξ) by simp]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.2): `u_ξ ξ = O(ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem lin_isBigO (U : ℝ × Ξ → ℝ) (yb : ℝ) {g : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] g) :
    (fun x => lin U yb (ξ x)) =O[l] g :=
  (IsBigO.of_bound ‖D1 U yb‖ (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact abs_lin_le U yb (ξ x))).trans hξ

/-- Woodford (2003), (E.2): `u_cξ ξ = O(ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem cross_isBigO (U : ℝ × Ξ → ℝ) (yb : ℝ) {g : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] g) :
    (fun x => cross U yb (ξ x)) =O[l] g :=
  (IsBigO.of_bound ‖D2 U yb‖ (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact abs_cross_le U yb (ξ x))).trans hξ

/-- Woodford (2003), (E.2): `ξ′u_ξξ ξ = O(ξ²)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem quad_isBigO (U : ℝ × Ξ → ℝ) (yb : ℝ) {g : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] g) :
    (fun x => quad U yb (ξ x)) =O[l] fun x => g x ^ 2 := by
  have h : (fun x => quad U yb (ξ x)) =O[l] fun x => ‖ξ x‖ ^ 2 :=
    IsBigO.of_bound ‖D2 U yb‖ (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
      exact abs_quad_le U yb (ξ x))
  exact h.trans (hξ.norm_left.pow 2)

/-- Woodford (2003), eq. (1.2), p. 385, and (E.2)–(E.3) (**the Taylor step along any family**):
for `C³` `U`, if the level deviation `c` and the disturbance `ξ` are `O(s)` with `s → 0`, then
`U(ȳ + c, ξ) = uTaylor(…)(c) + O(s³)`, the polynomial having the coefficients of (E.2).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem taylor_pair {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (yb : ℝ) (hs : Tendsto s l (𝓝 0))
    {c : α → ℝ} {ξ : α → Ξ} (hc : c =O[l] s) (hξ : ξ =O[l] s) :
    (fun x => U (yb + c x, ξ x) - Prop61.uTaylor (U (yb, 0)) (slope U yb) (curv U yb)
      (lin U yb (ξ x)) (cross U yb (ξ x)) (quad U yb (ξ x)) (c x)) =O[l] fun x => s x ^ 3 := by
  have hT := ApproxTheory.taylor2_multivar_isBigO_of_contDiff hU ((yb, 0) : ℝ × Ξ)
  have hz : (fun x => ((c x, ξ x) : ℝ × Ξ)) =O[l] s := hc.prod_left hξ
  have h1 := hT.comp_tendsto (hz.trans_tendsto hs)
  refine (h1.trans (hz.norm_left.pow 3)).congr_left fun _ => ?_
  simp only [Function.comp_apply, Prod.mk_add_mk, zero_add, quadApprox_pair]

/-- Woodford (2003), (E.2)–(E.3), p. 693 (**the Taylor step in log deviations**): with
`Y = ȳ e^{Ŷ}` and `Ŷ, ξ = O(s)`, `U(Y, ξ) = uTaylor(…)(Y − ȳ) + O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem level_taylor {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (yb : ℝ) (hs : Tendsto s l (𝓝 0))
    {Y : α → ℝ} {ξ : α → Ξ} (hY : Y =O[l] s) (hξ : ξ =O[l] s) :
    (fun x => U (yb * Real.exp (Y x), ξ x) - Prop61.uTaylor (U (yb, 0)) (slope U yb)
      (curv U yb) (lin U yb (ξ x)) (cross U yb (ξ x)) (quad U yb (ξ x))
      (yb * Real.exp (Y x) - yb)) =O[l] fun x => s x ^ 3 := by
  have hc : (fun x => yb * Real.exp (Y x) - yb) =O[l] s :=
    ((exp_sub_one_isBigO hs hY).const_mul_left yb).congr_left fun x => by ring
  refine (taylor_pair hU yb hs hc hξ).congr_left fun x => ?_
  rw [show yb + (yb * Real.exp (Y x) - yb) = yb * Real.exp (Y x) by ring]

/-- Woodford (2003), (2.11), p. 395 (bookkeeping): `f = O(s)` gives `f = O(s¹)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem isBigO_pow_one {f : α → ℝ} (h : f =O[l] s) : f =O[l] fun x => s x ^ 1 :=
  h.congr_right fun _ => (pow_one _).symm

/-- Woodford (2003), (E.2), p. 692 (**the remainder Ru is `O(s³)`**): with `g, Ŷ = O(s)` and
the exponential remainder `r = O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem Ru_isBigO (hs : Tendsto s l (𝓝 0)) (sinv : ℝ) {g Y r : α → ℝ} (hg : g =O[l] s)
    (hY : Y =O[l] s) (hr : r =O[l] fun x => s x ^ 3) :
    (fun x => Ru sinv (g x) (Y x) (r x)) =O[l] fun x => s x ^ 3 := by
  have hY1 := isBigO_pow_one hY
  have hW : (fun x => Y x ^ 2 / 2 + r x) =O[l] fun x => s x ^ 2 :=
    (((isBigO_pow_mul hY1 hY1 (by norm_num : 1 + 1 = 2)).const_mul_left (1 / 2)).add
      (hr.trans (pow_isBigO_pow hs (by norm_num : 2 ≤ 3)))).congr_left fun x => by ring
  have h2 : (fun x => 2 * Y x + (Y x ^ 2 / 2 + r x)) =O[l] fun x => s x ^ 1 :=
    (hY1.const_mul_left 2).add (hW.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2)))
  have t1 := isBigO_pow_mul hW h2 (by norm_num : 2 + 1 = 3)
  have t2 := isBigO_pow_mul (isBigO_pow_one hg) hW (by norm_num : 1 + 2 = 3)
  refine (hr.add ((t1.const_mul_left (-(sinv / 2))).add (t2.const_mul_left sinv))).congr_left
    fun x => ?_
  unfold Ru
  ring

/-- Woodford (2003), (E.3), p. 693 (**the remainder Rv at `Φ = 0` is `O(s³)`**): with
`q, ŷ = O(s)` and the exponential remainder `r = O(s³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem Rv_isBigO (hs : Tendsto s l (𝓝 0)) (omega : ℝ) {q y r : α → ℝ} (hq : q =O[l] s)
    (hy : y =O[l] s) (hr : r =O[l] fun x => s x ^ 3) :
    (fun x => Rv 0 omega (q x) (y x) (r x)) =O[l] fun x => s x ^ 3 := by
  have hy1 := isBigO_pow_one hy
  have hW : (fun x => y x ^ 2 / 2 + r x) =O[l] fun x => s x ^ 2 :=
    (((isBigO_pow_mul hy1 hy1 (by norm_num : 1 + 1 = 2)).const_mul_left (1 / 2)).add
      (hr.trans (pow_isBigO_pow hs (by norm_num : 2 ≤ 3)))).congr_left fun x => by ring
  have h2 : (fun x => 2 * y x + (y x ^ 2 / 2 + r x)) =O[l] fun x => s x ^ 1 :=
    (hy1.const_mul_left 2).add (hW.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2)))
  have t1 := isBigO_pow_mul hW h2 (by norm_num : 2 + 1 = 3)
  have t2 := isBigO_pow_mul (isBigO_pow_one hq) hW (by norm_num : 1 + 2 = 3)
  refine (hr.add ((t1.const_mul_left (omega / 2)).add
    (t2.const_mul_left (-omega)))).congr_left fun x => ?_
  unfold Rv
  ring

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), App. E, p. 693: one good's log output is bounded by the sup norm, so a
cross-section that is `O(s)` is `O(s)` good by good.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem coord_isBigO {g : α → ℝ} {yh : α → ι → ℝ} (hy : yh =O[l] g) (i : ι) :
    (fun x => yh x i) =O[l] g :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun x => by
    rw [one_mul]; exact norm_le_pi_norm (yh x) i)).trans hy

/-- Woodford (2003), App. E.1, eq. (E.5), p. 694 (**the orders of the CES objects**): if the
cross-section `ŷ` is `O(s)`, then `E_i ŷ = O(s)`, `var_i ŷ = O(s²)`, the (E.5) error
`Ŷ − E_i ŷ − (r/2) var_i ŷ = O(s³)` and `Ŷ = (1/r) log E_i e^{r ŷ} = O(s)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem ces_orders {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {r : ℝ} (hr : r ≠ 0)
    (hs : Tendsto s l (𝓝 0)) {yh : α → ι → ℝ} (hy : yh =O[l] s) :
    ((fun x => crossMean w (yh x)) =O[l] s) ∧
      ((fun x => crossVar w (yh x)) =O[l] fun x => s x ^ 2) ∧
      ((fun x => cumulant w r (yh x) - (crossMean w (yh x) + r / 2 * crossVar w (yh x)))
        =O[l] fun x => s x ^ 3) ∧
      ((fun x => cumulant w r (yh x)) =O[l] s) := by
  have hm : (fun x => crossMean w (yh x)) =O[l] s :=
    (IsBigO.of_bound 1 (Eventually.of_forall fun x => by
      rw [one_mul, Real.norm_eq_abs]; exact ExpLogCES.abs_crossMean_le hw hw1 (yh x))).trans hy
  have hV : (fun x => crossVar w (yh x)) =O[l] fun x => s x ^ 2 := by
    have h : (fun x => crossVar w (yh x)) =O[l] fun x => ‖yh x‖ ^ 2 :=
      IsBigO.of_bound 1 (Eventually.of_forall fun x => by
        have h := ExpLogCES.crossVar_le hw hw1 (yh x)
        rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1,
          abs_of_nonneg (by positivity)]
        exact h.2)
    exact h.trans (hy.norm_left.pow 2)
  have he := ((ExpLogCES.cumulant_expansion hw hw1 hr).comp_tendsto
    (hy.trans_tendsto hs)).trans (hy.norm_left.pow 3)
  refine ⟨hm, hV, he, ?_⟩
  have h3 := he.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 3))
  have h2 := hV.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))
  refine ((h3.add (isBigO_pow_one hm)).add (h2.const_mul_left (r / 2))).congr
    (fun x => ?_) (fun x => pow_one _)
  simp only [Function.comp_apply]
  ring

/-- Woodford (2003), App. E: E_i commutes with differences.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossMean_sub' (w a b : ι → ℝ) :
    crossMean w (a - b) = crossMean w a - crossMean w b := by
  simp [ExpLogCES.crossMean, mul_sub, Finset.sum_sub_distrib]

/-- Woodford (2003), (E.1), p. 692 (**the remainder R3 of Theorem A1 at `Φ = 0` is
`O(s³)`**), with the natural-rate and efficient-gap errors zero: if `q, Ŷ = O(s)`,
`var_i ŷ = O(s²)` and the (E.5) error `e = O(s³)` (no condition on `g`, which enters R3 only
through the vanishing error terms).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem R3_zero_isBigO (hs : Tendsto s l (𝓝 0)) (sinv omega θ : ℝ) {g q Y V e : α → ℝ}
    (hq : q =O[l] s) (hY : Y =O[l] s) (hV : V =O[l] fun x => s x ^ 2)
    (he : e =O[l] fun x => s x ^ 3) :
    (fun x => R3 sinv omega θ (g x) (q x) 0 (Y x) (V x) (e x) 0 0) =O[l] fun x => s x ^ 3 := by
  have hW : (fun x => (1 - θ⁻¹) / 2 * V x + e x) =O[l] fun x => s x ^ 2 :=
    (hV.const_mul_left _).add (he.trans (pow_isBigO_pow hs (by norm_num : 2 ≤ 3)))
  have h2 : (fun x => ((1 - θ⁻¹) / 2 * V x + e x) - 2 * Y x) =O[l] fun x => s x ^ 1 :=
    (hW.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))).sub
      ((isBigO_pow_one hY).const_mul_left 2)
  have t1 := isBigO_pow_mul hW h2 (by norm_num : 2 + 1 = 3)
  have t2 := isBigO_pow_mul (isBigO_pow_one hq) hW (by norm_num : 1 + 2 = 3)
  refine (he.add ((t1.const_mul_left (-((1 + omega) / 2))).add
    (t2.const_mul_left (-omega)))).congr_left fun x => ?_
  unfold R3
  ring

/-- Woodford (2003), (E.6), p. 694: the first-order natural rate
`Ŷⁿ = (σ⁻¹g + ωq)/(σ⁻¹ + ω)` is `O(s)` when `g, q` are.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem natLin_isBigO (sinv omega : ℝ) {g q : α → ℝ} {k : α → ℝ} (hg : g =O[l] k)
    (hq : q =O[l] k) : (fun x => natLin sinv omega (g x) (q x)) =O[l] k := by
  refine (((hg.const_mul_left sinv).add (hq.const_mul_left omega)).const_mul_left
    (sinv + omega)⁻¹).congr_left fun x => ?_
  unfold natLin
  ring

/-- Woodford (2003), (E.6), p. 694: `Ŷⁿ` is linear in the disturbances.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem natLin_smul (sinv omega r g q : ℝ) :
    natLin sinv omega (r * g) (r * q) = r * natLin sinv omega g q := by
  unfold natLin
  ring

/-- Woodford (2003), App. E (one-parameter families): if `ŷ − s y₁ = O(s²)` with `y₁` bounded
and `s → 0`, then `ŷ = O(s)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem family_isBigO {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hs : Tendsto s l (𝓝 0)) {yh y1 : α → F}
    (h : (fun x => yh x - s x • y1 x) =O[l] fun x => s x ^ 2)
    (h1 : y1 =O[l] fun _ => (1 : ℝ)) : yh =O[l] s := by
  have hsy : (fun x => s x • y1 x) =O[l] s :=
    ((isBigO_refl s l).smul h1).congr_right fun x => by ring
  have h2 : (fun x => yh x - s x • y1 x) =O[l] s :=
    (h.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))).congr_right fun x => pow_one _
  exact (h2.add hsy).congr_left fun x => by abel

/-- Woodford (2003), App. E (`(1/r) log E_i e^{r ŷ}` and the CES index): for probability weights,
`Ȳ · CES(e^{ŷ}) = Ȳ e^{Ŷ}` with `Ŷ = (1/r) log E_i e^{r ŷ}` (and the index is positive).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem cesIndex_exp_eq {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (r : ℝ)
    (yh : ι → ℝ) : cesIndex w r (fun i => Real.exp (yh i)) = Real.exp (cumulant w r yh) := by
  have hpos : 0 < cesIndex w r (fun i => Real.exp (yh i)) := by
    have e : ∑ i, w i * Real.exp (yh i) ^ r = ExpLogCES.cesMoment w r yh := by
      unfold ExpLogCES.cesMoment
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Real.exp_mul, mul_comm (yh i) r]
    unfold ExpLogCES.cesIndex
    rw [e]
    exact Real.rpow_pos_of_pos (ExpLogCES.cesMoment_pos hw hw1 r yh) _
  rw [← ExpLogCES.log_cesIndex_exp hw hw1, Real.exp_log hpos]

/-- Woodford (2003), (E.2), p. 692 (**the utility side**): for `C³` `U` with `U_y ≠ 0`,
`U_yy ≠ 0` at `(ȳ, 0)` and `Ŷ, ξ = O(s)`,
`U(ȳ e^{Ŷ}; ξ) = tip0 + ȳ U_y · Tu(σ⁻¹, g, Ŷ) + O(s³)` with `Tu = Ŷ + ½(1 − σ⁻¹)Ŷ² + σ⁻¹gŶ`,
`σ⁻¹ = −ȳ U_yy/U_y`, `g = −U_yξ ξ/(ȳ U_yy)` (via `Prop61.uTaylor_eq`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem uside_gen {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) {yb : ℝ} (hyb : yb ≠ 0)
    (huc : slope U yb ≠ 0) (hucc : curv U yb ≠ 0) (hs : Tendsto s l (𝓝 0)) {Y : α → ℝ}
    {ξ : α → Ξ} (hY : Y =O[l] s) (hξ : ξ =O[l] s) :
    (fun x => U (yb * Real.exp (Y x), ξ x) - (tip0 U yb (ξ x) + yb * slope U yb *
      Tu (sigmaInvEl yb (slope U yb) (curv U yb)) (gShock yb (curv U yb) (cross U yb (ξ x)))
        (Y x))) =O[l] fun x => s x ^ 3 := by
  have h1 := level_taylor hU yb hs hY hξ
  have hg : (fun x => gShock yb (curv U yb) (cross U yb (ξ x))) =O[l] s :=
    ((cross_isBigO U yb hξ).const_mul_left (-(yb * curv U yb)⁻¹)).congr_left fun x => by
      unfold gShock; ring
  have h2 := Ru_isBigO hs (sigmaInvEl yb (slope U yb) (curv U yb)) hg hY (expRem_isBigO hs hY)
  refine (h1.add (h2.const_mul_left (yb * slope U yb))).congr_left fun x => ?_
  rw [Prop61.levelDev_eq, Prop61.uTaylor_eq hyb huc hucc]
  unfold tip0
  ring

/-- Woodford (2003), (E.3)–(E.4), pp. 693–694 (**the disutility side, integrated over goods**):
for `C³` `V` with `V_y ≠ 0`, `V_yy ≠ 0` at `(ȳ, 0)`, probability weights and `ŷ, ξ = O(s)`,
`E_i V(ȳ e^{ŷ(i)}; ξ) = tip0 + ȳ V_y [E_i ŷ + ½(1 + ω)(var_i ŷ + (E_i ŷ)²) − ω q E_i ŷ] + O(s³)`,
`ω = ȳ V_yy/V_y`, `q = −V_yξ ξ/(ȳ V_yy)` (via `Prop61.vTaylor_eq` at `Φ = 0`, normalised by
`ȳ V_y`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem vside_gen {V : ℝ × Ξ → ℝ} (hV : ContDiff ℝ 3 V) {yb : ℝ} (hyb : yb ≠ 0)
    (hvy : slope V yb ≠ 0) (hvyy : curv V yb ≠ 0) {w : ι → ℝ} (hw1 : ∑ i, w i = 1)
    (hs : Tendsto s l (𝓝 0)) {yh : α → ι → ℝ} {ξ : α → Ξ} (hy : yh =O[l] s)
    (hξ : ξ =O[l] s) :
    (fun x => ∑ i, w i * V (yb * Real.exp (yh x i), ξ x) - (tip0 V yb (ξ x) + yb * slope V yb *
      (crossMean w (yh x) + (1 + omegaEl yb (slope V yb) (curv V yb)) / 2 *
        (crossVar w (yh x) + crossMean w (yh x) ^ 2) -
        omegaEl yb (slope V yb) (curv V yb) * qShock yb (curv V yb) (cross V yb (ξ x)) *
          crossMean w (yh x)))) =O[l] fun x => s x ^ 3 := by
  have hq : (fun x => qShock yb (curv V yb) (cross V yb (ξ x))) =O[l] s :=
    ((cross_isBigO V yb hξ).const_mul_left (-(yb * curv V yb)⁻¹)).congr_left fun x => by
      unfold qShock; ring
  have hi : ∀ i, (fun x => V (yb * Real.exp (yh x i), ξ x) - (tip0 V yb (ξ x) +
      yb * slope V yb * Tv 0 (omegaEl yb (slope V yb) (curv V yb))
        (qShock yb (curv V yb) (cross V yb (ξ x))) (yh x i))) =O[l] fun x => s x ^ 3 := by
    intro i
    have hyi := coord_isBigO hy i
    have h1 := level_taylor hV yb hs hyi hξ
    have h2 := Rv_isBigO hs (omegaEl yb (slope V yb) (curv V yb)) hq hyi (expRem_isBigO hs hyi)
    refine (h1.add (h2.const_mul_left (yb * slope V yb))).congr_left fun x => ?_
    have e := Prop61.vTaylor_eq (vbar := V (yb, 0)) (Lv := lin V yb (ξ x))
      (Cv := cross V yb (ξ x)) (Qv := quad V yb (ξ x)) (Φ := 0) (uc := slope V yb)
      (y := yh x i) (r := expRem (yh x i)) hyb (by ring) hvy hvyy
    have e2 : Prop61.uTaylor (V (yb, 0)) (slope V yb) (curv V yb) (lin V yb (ξ x))
        (cross V yb (ξ x)) (quad V yb (ξ x)) (yb * Real.exp (yh x i) - yb) =
        Prop61.vTaylor (V (yb, 0)) (slope V yb) (curv V yb) (lin V yb (ξ x))
        (cross V yb (ξ x)) (quad V yb (ξ x))
          (yb * (yh x i + yh x i ^ 2 / 2 + expRem (yh x i))) := by
      rw [Prop61.levelDev_eq]
      rfl
    rw [e2, e]
    unfold tip0
    ring
  have hsum := IsBigO.sum (s := Finset.univ) fun i _ => (hi i).const_mul_left (w i)
  refine hsum.congr_left fun x => ?_
  have e : ∀ i, w i * (V (yb * Real.exp (yh x i), ξ x) - (tip0 V yb (ξ x) +
      yb * slope V yb * Tv 0 (omegaEl yb (slope V yb) (curv V yb))
        (qShock yb (curv V yb) (cross V yb (ξ x))) (yh x i))) =
      w i * V (yb * Real.exp (yh x i), ξ x) - tip0 V yb (ξ x) * w i -
        yb * slope V yb * (1 - omegaEl yb (slope V yb) (curv V yb) *
          qShock yb (curv V yb) (cross V yb (ξ x))) * (w i * yh x i) -
        yb * slope V yb * ((1 + omegaEl yb (slope V yb) (curv V yb)) / 2) *
          (w i * yh x i ^ 2) := fun i => by
    unfold Tv
    ring
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun i _ => e i]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hw1]
  rw [Moments.sum_sq_eq hw1]
  unfold ExpLogCES.crossMean
  ring

/-- Woodford (2003), App. E: `E_i(r y) = r E_i y`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossMean_smul' (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) :
    crossMean w (r • y) = r * crossMean w y :=
  ExpLogCES.crossMean_mul w r y

/-- Woodford (2003), App. E: `E_i z = O(‖z‖)` along any family.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem crossMean_isBigO {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {g : α → ℝ}
    {z : α → ι → ℝ} (hz : z =O[l] g) : (fun x => crossMean w (z x)) =O[l] g :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun x => by
    rw [one_mul, Real.norm_eq_abs]; exact ExpLogCES.abs_crossMean_le hw hw1 (z x))).trans hz

/-- Woodford (2003), (2.10), p. 394 (C² families satisfy the first-order hypothesis): if every
good's log output `ε ↦ ŷ(ε)(i)` is `C²` with `ŷ(0) = 0`, then `ŷ(ε) − ε y₁ = O(ε²)` with the
first-order solution `y₁(i) = ŷ′(0)(i)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem family_of_contDiff {yh : ℝ → ι → ℝ} (hc : ∀ i, ContDiff ℝ 2 (fun ε => yh ε i))
    (h0 : yh 0 = 0) :
    (fun ε => yh ε - ε • (fun i => deriv (fun ε => yh ε i) 0)) =O[𝓝 0] fun ε => ε ^ 2 := by
  refine isBigO_pi.2 fun i => ?_
  refine (OneParamTaylor.taylor_one_bigO (hc i).contDiffAt).congr (fun ε => ?_) (fun ε => ?_)
  · simp [h0, mul_comm]
  · simp

/-- Woodford (2003), (2.9), p. 394 and (2.10) (**Woodford's gap versus the gap from the efficient
level**): with `Ȳ(Φ)` the distorted steady state, `x = log(Y/Ȳ) − Ŷⁿ` and
`x* = log(Y*/Ȳ)`, the welfare-relevant gap is `x − x* = log(Y/Y*) − Ŷⁿ`: expanding around the
efficient `Y*` measures exactly `x − x*`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem gap_eq_woodford {Y Ystar Ybar Yn : ℝ} (hY : 0 < Y) (hs : 0 < Ystar) (hb : 0 < Ybar) :
    Real.log (Y / Ystar) - Yn = (Real.log (Y / Ybar) - Yn) - Real.log (Ystar / Ybar) := by
  rw [Real.log_div hY.ne' hs.ne', Real.log_div hY.ne' hb.ne', Real.log_div hs.ne' hb.ne']
  ring

/-- Woodford (2003), (2.9)/(2.17), p. 394 (**the first-order efficient gap along `Φ = εΦ₁`**):
if `F(Φ) = log(Ȳ(Φ)/Y*)` has derivative `−1/(ω + σ⁻¹)` at `0` (Prop61.steadyState_family),
then `x*(ε) = log(Y*/Ȳ(εΦ₁)) = −F(εΦ₁)` has derivative `Φ₁/(σ⁻¹ + ω) = xStarLin σ⁻¹ ω Φ₁` at
`ε = 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem xstar_hasDerivAt {F : ℝ → ℝ} {sinv omega Φ1 : ℝ}
    (hF : HasDerivAt F (-(omega + sinv)⁻¹) 0) :
    HasDerivAt (fun ε => -F (ε * Φ1)) (xStarLin sinv omega Φ1) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => ε * Φ1) Φ1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const Φ1
  have h2 : HasDerivAt F (-(omega + sinv)⁻¹) ((0 : ℝ) * Φ1) := by simpa using hF
  have h3 : HasDerivAt (fun ε => -F (ε * Φ1)) (-(-(omega + sinv)⁻¹ * Φ1)) 0 :=
    (h2.comp (0 : ℝ) h1).neg
  unfold xStarLin
  convert h3 using 1
  rw [add_comm omega sinv]
  ring

/-- Woodford (2003), App. E.3, p. 697 (survey error 25): a sequence bounded by one constant for
all `t` is `O(1)` uniformly in `t`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem unif_of_bounded {E : Type*} [Norm E] {f : ℕ → E} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    (fun p : ℕ × ℝ => f p.1) =O[unif] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC⟩ := hf
  exact IsBigO.of_bound C (Eventually.of_forall fun p => by simpa using hC p.1)

variable (ι Ξ)

/-- Woodford (2003), (2.3)–(2.6), pp. 392–393: the primitives of the period utility
`U_t = ũ(Y_t; ξ_t) − ∫ ṽ(y_t(i); ξ_t) di` for a finite weighted cross-section of goods: the
utility `ũ` of aggregate output, the disutility `ṽ` of supplying one good, the steady state
`Ȳ` (the expansion point), the elasticity `θ` of the Dixit–Stiglitz aggregate and the weights.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
structure Econ where
  /-- `ũ(Y; ξ)`, (2.4): utility of output `Y` (consumption `Y − G`) given disturbances `ξ`. -/
  u : ℝ × Ξ → ℝ
  /-- `ṽ(y; ξ)`, (2.5): the disutility of supplying the quantity `y` of one good. -/
  v : ℝ × Ξ → ℝ
  /-- The steady-state output `Ȳ` (the expansion point). -/
  Yb : ℝ
  /-- The elasticity of substitution `θ` of the Dixit–Stiglitz aggregate (2.6). -/
  θ : ℝ
  /-- The weights of the goods (a probability vector). -/
  w : ι → ℝ

variable {ι Ξ}

namespace Econ

variable (M : Econ Ξ ι)

/-- Woodford (2003), App. E.1, p. 692: `u_c = ũ_Y(Ȳ; 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def uc : ℝ := slope M.u M.Yb

/-- Woodford (2003), App. E.1, p. 692: `u_cc = ũ_YY(Ȳ; 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def ucc : ℝ := curv M.u M.Yb

/-- Woodford (2003), App. E.1, p. 693: `ṽ_y(Ȳ; 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def vy : ℝ := slope M.v M.Yb

/-- Woodford (2003), App. E.1, p. 693: `ṽ_yy(Ȳ; 0)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def vyy : ℝ := curv M.v M.Yb

/-- Woodford (2003), p. 393: `σ⁻¹ = −Ȳ u_cc/u_c`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def sig : ℝ := sigmaInvEl M.Yb M.uc M.ucc

/-- Woodford (2003), p. 393: `ω = Ȳ ṽ_yy/ṽ_y`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def omg : ℝ := omegaEl M.Yb M.vy M.vyy

/-- Woodford (2003), App. E.1, p. 693: the demand disturbance `g = −u_cξ ξ/(Ȳ u_cc)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def gS (ξ : Ξ) : ℝ := gShock M.Yb M.ucc (cross M.u M.Yb ξ)

/-- Woodford (2003), App. E.1, p. 693: the supply disturbance `q = −ṽ_yξ ξ/(Ȳ ṽ_yy)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def qS (ξ : Ξ) : ℝ := qShock M.Yb M.vyy (cross M.v M.Yb ξ)

/-- Woodford (2003), eq. (2.6), p. 393: log aggregate output `Ŷ = log(Y/Ȳ)` of the cross-section
of log outputs `ŷ`, `Ŷ = (1/r) log E_i e^{r ŷ}` with `r = 1 − θ⁻¹`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def Yagg (yh : ι → ℝ) : ℝ := cumulant M.w (1 - M.θ⁻¹) yh

/-- Woodford (2003), eqs. (2.3)–(2.6), pp. 392–393 (**the actual period utility**): with
`y(i) = Ȳ e^{ŷ(i)}` and `Y` the Dixit–Stiglitz aggregate,
`U = ũ(Ȳ · CES(e^{ŷ}); ξ) − E_i ṽ(Ȳ e^{ŷ(i)}; ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def Ustate (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  M.u (M.Yb * cesIndex M.w (1 - M.θ⁻¹) (fun i => Real.exp (yh i)), ξ) -
    ∑ i, M.w i * M.v (M.Yb * Real.exp (yh i), ξ)

/-- Woodford (2003), (2.10)/(E.1), p. 394: the terms independent of policy,
`(ū + u_ξξ + ½ξ′u_ξξξ) − (v̄ + v_ξξ + ½ξ′v_ξξξ) + Ȳu_c · ½(σ⁻¹ + ω)(Ŷⁿ)²` (a function of the
disturbances only).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def tipState (ξ : Ξ) : ℝ :=
  tip0 M.u M.Yb ξ - tip0 M.v M.Yb ξ + M.Yb * M.uc * tipA M.sig M.omg (M.gS ξ) (M.qS ξ) 0

/-- Woodford (2003), eq. (2.10), p. 394 (**the loss in Woodford's variables**):
`(σ⁻¹ + ω)(Ŷ − Ŷⁿ)² + (θ⁻¹ + ω) var_i ŷ`, with `Ŷ` the CES aggregate.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def lossW (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  lossQ M.sig M.omg M.θ (M.Yagg yh - natLin M.sig M.omg (M.gS ξ) (M.qS ξ)) (crossVar M.w yh)

/-- Woodford (2003), eq. (2.10), p. 394 (**the loss as a quadratic form**): the same with `Ŷ`
replaced by `E_i ŷ` (equal to second order, (E.5)): a homogeneous quadratic in `(ŷ, ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def lossB (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  lossQ M.sig M.omg M.θ (crossMean M.w yh - natLin M.sig M.omg (M.gS ξ) (M.qS ξ))
    (crossVar M.w yh)

/-- Woodford (2003), §2.1, pp. 392–394 (**the maintained assumptions, made explicit**): `ũ`, `ṽ`
are `C³` (survey error 19), `Ȳ > 0`, probability weights, `θ ≠ 1`, `u_c > 0`, `u_cc ≠ 0`,
`ṽ_yy ≠ 0`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
structure Std where
  /-- `ũ` is `C³`. -/
  contDiff_u : ContDiff ℝ 3 M.u
  /-- `ṽ` is `C³`. -/
  contDiff_v : ContDiff ℝ 3 M.v
  /-- `Ȳ > 0`. -/
  Yb_pos : 0 < M.Yb
  /-- The weights are nonnegative. -/
  w_nonneg : ∀ i, 0 ≤ M.w i
  /-- The weights sum to one. -/
  w_sum : ∑ i, M.w i = 1
  /-- `θ ≠ 1`. -/
  θ_ne_one : M.θ ≠ 1
  /-- `u_c > 0`. -/
  uc_pos : 0 < M.uc
  /-- `u_cc ≠ 0`. -/
  ucc_ne : M.ucc ≠ 0
  /-- `ṽ_yy ≠ 0`. -/
  vyy_ne : M.vyy ≠ 0

variable {M}

/-- Woodford (2003), (2.6): `r = 1 − θ⁻¹ ≠ 0` for `θ ≠ 1`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem r_ne (hM : M.Std) : 1 - M.θ⁻¹ ≠ 0 := by
  intro h
  apply hM.θ_ne_one
  have : M.θ⁻¹ = 1 := by linarith
  simpa using congrArg (·⁻¹) this

/-- Woodford (2003), (2.6): the actual utility with the aggregate written as `Ȳ e^{Ŷ}`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem Ustate_eq (hM : M.Std) (yh : ι → ℝ) (ξ : Ξ) :
    M.Ustate yh ξ = M.u (M.Yb * Real.exp (M.Yagg yh), ξ) -
      ∑ i, M.w i * M.v (M.Yb * Real.exp (yh i), ξ) := by
  unfold Ustate Yagg
  rw [cesIndex_exp_eq hM.w_nonneg hM.w_sum]

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `g` is linear in the disturbances, `g(rξ) = r g(ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem gS_smul (r : ℝ) (ξ : Ξ) : M.gS (r • ξ) = r * M.gS ξ := by
  unfold gS gShock
  rw [cross_smul]
  ring

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `q` is linear in the disturbances, `q(rξ) = r q(ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem qS_smul (r : ℝ) (ξ : Ξ) : M.qS (r • ξ) = r * M.qS ξ := by
  unfold qS qShock
  rw [cross_smul]
  ring

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `g = O(ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem gS_isBigO {k : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] k) :
    (fun x => M.gS (ξ x)) =O[l] k :=
  ((cross_isBigO M.u M.Yb hξ).const_mul_left (-(M.Yb * M.ucc)⁻¹)).congr_left fun x => by
    unfold gS gShock
    ring

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `q = O(ξ)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem qS_isBigO {k : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] k) :
    (fun x => M.qS (ξ x)) =O[l] k :=
  ((cross_isBigO M.v M.Yb hξ).const_mul_left (-(M.Yb * M.vyy)⁻¹)).congr_left fun x => by
    unfold qS qShock
    ring

/-- Woodford (2003), **Proposition 6.1, eq. (2.10)/(E.1), p. 394 (Layer B, in the state
variables)**. Expand around the EFFICIENT steady state (`ṽ_y = u_c`, i.e. `Φ = 0`; the distortion
enters only through the allocation, see `gap_eq_woodford`). Along any family of states with the
cross-section `ŷ = O(s)` and the disturbances `ξ = O(s)`, `s → 0`, the actual utility satisfies
`U = t.i.p.(ξ) − (Ȳu_c/2)[(σ⁻¹ + ω)(Ŷ − Ŷⁿ)² + (θ⁻¹ + ω) var_i ŷ] + O(s³)`, with `Ŷ` the CES
aggregate and t.i.p. `tipState ξ`. The proof is the exact Layer-A identity `Prop61.thmA1`
(at `Φ = 0`) plus the Taylor remainders (`uside_gen`, `vside_gen`, `ces_orders`,
`R3_zero_isBigO`). With `l = 𝓝 0` on the state space and `s = ‖·‖` this is the book's
`O(‖ŷ, ξ‖³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop61_state (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hs : Tendsto s l (𝓝 0)) {yh : α → ι → ℝ} {ξ : α → Ξ} (hy : yh =O[l] s)
    (hξ : ξ =O[l] s) :
    (fun x => M.Ustate (yh x) (ξ x) -
      (M.tipState (ξ x) - M.Yb * M.uc / 2 * M.lossW (yh x) (ξ x))) =O[l] fun x => s x ^ 3 := by
  have hyb : M.Yb ≠ 0 := hM.Yb_pos.ne'
  have huc : slope M.u M.Yb ≠ 0 := hM.uc_pos.ne'
  have heff' : slope M.v M.Yb = slope M.u M.Yb := heff
  have hvy : slope M.v M.Yb ≠ 0 := by rw [heff']; exact huc
  obtain ⟨-, hV, he, hY⟩ := ces_orders hM.w_nonneg hM.w_sum (r_ne hM) hs hy
  have hu := uside_gen hM.contDiff_u hyb huc hM.ucc_ne hs hY hξ
  have hv := vside_gen hM.contDiff_v hyb hvy hM.vyy_ne hM.w_sum hs hy hξ
  have hR := R3_zero_isBigO hs M.sig M.omg M.θ (g := fun x => M.gS (ξ x)) (M.qS_isBigO hξ) hY
    hV he
  refine ((hu.sub hv).add (hR.const_mul_left (M.Yb * M.uc))).congr_left fun x => ?_
  have hA := Prop61.thmA1 (sinv := M.sig) (omega := M.omg) (θ := M.θ) (g := M.gS (ξ x))
    (q := M.qS (ξ x)) (Φ := 0) (Y := M.Yagg (yh x)) (V := crossVar M.w (yh x))
    (e := M.Yagg (yh x) - (crossMean M.w (yh x) + (1 - M.θ⁻¹) / 2 * crossVar M.w (yh x)))
    (n := 0) (k := 0) hden
  rw [Ustate_eq hM]
  simp only [tipState, lossW, lossQ, tipA, xStarLin, Yagg] at hA ⊢
  unfold sig omg gS qS uc ucc vy vyy at hA ⊢
  set σ := sigmaInvEl M.Yb (slope M.u M.Yb) (curv M.u M.Yb)
  set ω := omegaEl M.Yb (slope M.v M.Yb) (curv M.v M.Yb)
  rw [heff']
  linear_combination (-(M.Yb * slope M.u M.Yb)) * hA

/-- Woodford (2003), (E.5), p. 694: replacing the CES aggregate `Ŷ` by `E_i ŷ` in the gap changes
the loss by `O(s³)` (`Ŷ − E_i ŷ = O(s²)` multiplies a first-order term).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem lossW_sub_lossB (hM : M.Std) (hs : Tendsto s l (𝓝 0)) {yh : α → ι → ℝ}
    {ξ : α → Ξ} (hy : yh =O[l] s) (hξ : ξ =O[l] s) :
    (fun x => M.lossW (yh x) (ξ x) - M.lossB (yh x) (ξ x)) =O[l] fun x => s x ^ 3 := by
  obtain ⟨hm, hV, he, hY⟩ := ces_orders hM.w_nonneg hM.w_sum (r_ne hM) hs hy
  have hN := natLin_isBigO M.sig M.omg (M.gS_isBigO hξ) (M.qS_isBigO hξ)
  have hd : (fun x => cumulant M.w (1 - M.θ⁻¹) (yh x) - crossMean M.w (yh x)) =O[l]
      fun x => s x ^ 2 :=
    ((he.trans (pow_isBigO_pow hs (by norm_num : 2 ≤ 3))).add
      (hV.const_mul_left ((1 - M.θ⁻¹) / 2))).congr_left fun x => by ring
  have hsum : (fun x => (cumulant M.w (1 - M.θ⁻¹) (yh x) -
      natLin M.sig M.omg (M.gS (ξ x)) (M.qS (ξ x))) +
      (crossMean M.w (yh x) - natLin M.sig M.omg (M.gS (ξ x)) (M.qS (ξ x)))) =O[l]
      fun x => s x ^ 1 :=
    isBigO_pow_one (((hY.sub hN).add (hm.sub hN)))
  refine ((isBigO_pow_mul hd hsum (by norm_num : 2 + 1 = 3)).const_mul_left
    (M.sig + M.omg)).congr_left fun x => ?_
  unfold lossW lossB lossQ Yagg
  ring

/-- Woodford (2003), **Proposition 6.1, (2.10), p. 394 (Layer B, state variables, quadratic-form
version)**: as `prop61_state`, with the gap measured by `E_i ŷ` (the loss `lossB` is a
homogeneous quadratic form in `(ŷ, ξ)`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop61_state_poly (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hs : Tendsto s l (𝓝 0)) {yh : α → ι → ℝ} {ξ : α → Ξ} (hy : yh =O[l] s)
    (hξ : ξ =O[l] s) :
    (fun x => M.Ustate (yh x) (ξ x) -
      (M.tipState (ξ x) - M.Yb * M.uc / 2 * M.lossB (yh x) (ξ x))) =O[l] fun x => s x ^ 3 :=
  ((prop61_state hM heff hden hs hy hξ).sub
    ((lossW_sub_lossB hM hs hy hξ).const_mul_left (M.Yb * M.uc / 2))).congr_left fun x => by
      ring

omit [Fintype ι] in
/-- Woodford (2003), (2.10)/(E.1) (**the t.i.p. along `ε ξ₁` is an explicit polynomial in `ε`
whose coefficients depend on `ξ₁` only**). -/
theorem tipState_smul (r : ℝ) (ξ : Ξ) :
    M.tipState (r • ξ) = M.tipState 0 + r * (lin M.u M.Yb ξ - lin M.v M.Yb ξ) +
      r ^ 2 * (quad M.u M.Yb ξ / 2 - quad M.v M.Yb ξ / 2 +
        M.Yb * M.uc * tipA M.sig M.omg (M.gS ξ) (M.qS ξ) 0) := by
  have h0 : (0 : Ξ) = (0 : ℝ) • ξ := (zero_smul ℝ ξ).symm
  unfold tipState tip0
  rw [h0, lin_smul, lin_smul, quad_smul, quad_smul, M.gS_smul, M.qS_smul, lin_smul, lin_smul,
    quad_smul, quad_smul, M.gS_smul, M.qS_smul]
  unfold tipA natLin xStarLin
  ring

omit [Fintype ι] in
/-- Woodford (2003), (2.10)/(E.1): the t.i.p. along `ε ξ₁_t` is bounded uniformly in `t` (for
bounded `ξ₁_t`). -/
theorem tipState_unif {ξ1 : ℕ → Ξ} (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) :
    (fun p : ℕ × ℝ => M.tipState (p.2 • ξ1 p.1)) =O[unif] fun _ => (1 : ℝ) := by
  have hx := unif_of_bounded hξ1
  have he : (fun p : ℕ × ℝ => p.2) =O[unif] fun _ => (1 : ℝ) := tendsto_unif.isBigO_one ℝ
  have h1 : (fun p : ℕ × ℝ => lin M.u M.Yb (ξ1 p.1) - lin M.v M.Yb (ξ1 p.1)) =O[unif]
      fun _ => (1 : ℝ) := (lin_isBigO M.u M.Yb hx).sub (lin_isBigO M.v M.Yb hx)
  have hq1 := (quad_isBigO M.u M.Yb hx).congr_right fun _ => one_pow 2
  have hq2 := (quad_isBigO M.v M.Yb hx).congr_right fun _ => one_pow 2
  have hN := natLin_isBigO M.sig M.omg (M.gS_isBigO hx) (M.qS_isBigO hx)
  have hA : (fun p : ℕ × ℝ => tipA M.sig M.omg (M.gS (ξ1 p.1)) (M.qS (ξ1 p.1)) 0) =O[unif]
      fun _ => (1 : ℝ) :=
    (((hN.add (isBigO_const_const (xStarLin M.sig M.omg 0) one_ne_zero unif)).pow 2).const_mul_left
      ((M.sig + M.omg) / 2)).congr (fun p => by unfold tipA; ring) (fun p => one_pow 2)
  have h2 : (fun p : ℕ × ℝ => quad M.u M.Yb (ξ1 p.1) / 2 - quad M.v M.Yb (ξ1 p.1) / 2 +
      M.Yb * M.uc * tipA M.sig M.omg (M.gS (ξ1 p.1)) (M.qS (ξ1 p.1)) 0) =O[unif]
      fun _ => (1 : ℝ) :=
    (((hq1.const_mul_left (1 / 2)).sub (hq2.const_mul_left (1 / 2))).add
      (hA.const_mul_left (M.Yb * M.uc))).congr_left fun p => by ring
  have t1 : (fun p : ℕ × ℝ => p.2 * (lin M.u M.Yb (ξ1 p.1) - lin M.v M.Yb (ξ1 p.1))) =O[unif]
      fun _ => (1 : ℝ) := (he.mul h1).congr_right fun _ => mul_one 1
  have t2 : (fun p : ℕ × ℝ => p.2 ^ 2 * (quad M.u M.Yb (ξ1 p.1) / 2 - quad M.v M.Yb (ξ1 p.1) / 2 +
      M.Yb * M.uc * tipA M.sig M.omg (M.gS (ξ1 p.1)) (M.qS (ξ1 p.1)) 0)) =O[unif]
      fun _ => (1 : ℝ) := ((he.pow 2).mul h2).congr_right fun _ => by ring
  refine (((isBigO_const_const (M.tipState 0) one_ne_zero unif).add t1).add t2).congr_left
    fun p => ?_
  rw [tipState_smul]

end Econ

/-- Woodford (2003), App. E.3 (survey error 25): a `t`-sequence that is `O(1)` uniformly is
bounded by one constant.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem bounded_of_unif {f : ℕ → ℝ} (h : (fun p : ℕ × ℝ => f p.1) =O[unif] fun _ => (1 : ℝ)) :
    ∃ C, ∀ t, |f t| ≤ C := by
  obtain ⟨C, hC⟩ := (isBigO_unif_iff (f := fun t _ => f t) (g := fun _ => (1 : ℝ))).1 h
  obtain ⟨ε, hε⟩ := hC.exists
  exact ⟨C, fun t => by simpa using hε t⟩

/-- Woodford (2003), App. E.2 (dating conventions): a bound uniform in `t` survives the shift
`t ↦ t + 1`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem unif_shift {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] fun p => g p.2) :
    (fun p : ℕ × ℝ => f (p.1 + 1) p.2) =O[unif] fun p => g p.2 := by
  obtain ⟨C, hC⟩ := isBigO_unif_iff.1 h
  exact isBigO_unif_iff (f := fun t ε => f (t + 1) ε).2 ⟨C, hC.mono fun ε hε t => hε (t + 1)⟩

namespace Econ

variable (M : Econ Ξ ι)

/-- Woodford (2003), (2.10), p. 394: the output gap `x = E_i ŷ − Ŷⁿ` entering the loss
(`lossB yh ξ = (σ⁻¹ + ω) gap² + (θ⁻¹ + ω) var_i ŷ`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
noncomputable def gap (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  crossMean M.w yh - natLin M.sig M.omg (M.gS ξ) (M.qS ξ)

variable {M}

/-- Woodford (2003), (2.10): the gap along `(ŷ, r ξ₁)` minus `r` times the first-order gap is the
mean of `ŷ − r y₁`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem gap_smul_sub (yh y1 : ι → ℝ) (r : ℝ) (ξ1 : Ξ) :
    M.gap yh (r • ξ1) - r * M.gap y1 ξ1 = crossMean M.w (yh - r • y1) := by
  unfold gap
  rw [crossMean_sub', crossMean_smul', M.gS_smul, M.qS_smul, natLin_smul]
  ring

/-- Woodford (2003), **Propositions 6.4–6.5, (2.21)–(2.25), pp. 400–402 (Layer B, generic Calvo
form)**. Period utility is the actual `Ustate` of the cross-section `ŷ_t(ε)` with disturbances
`ε ξ₁_t`, and
* `ŷ_t(ε) − ε y₁_t = O(ε²)` UNIFORMLY in `t`, `y₁_t`, `ξ₁_t` bounded (survey error 25);
* (2.12): `var_i ŷ_t(ε) = θ² Δ_t(ε)` (Moments.crossVar_demand; `D ε (t+1) = Δ_t`,
  `D ε 0 = Δ_{−1}`);
* the exact dispersion recursion `Δ_t = α Δ_{t−1} + (α/(1−α)) q_t² + R_t` (Layer A:
  PriceDispersion.prop63_layerA with `q_t = π_t`, index_layerA with `q_t = π_t − γπ_{t−1}`),
  with `q_t(ε) − ε q₁_t = O(ε²)` and `R_t(ε) = O(ε³)` uniformly in `t`
  (PriceDispersion.prop63_uniform), `q₁_t` bounded.
Then, at the efficient steady state,
`∑ βᵗ U_t(ε) = TIP(ε) − (ε²/2) Ȳu_c · 2Θ ∑ βᵗ (q₁_t² + (κ/θ) x₁_t²) + O(ε³)`,
`TIP(ε) = ∑ βᵗ tipState(ε ξ₁_t) − Ȳu_c ½θ(1 + ωθ) α Δ_{−1}(ε)/(1 − αβ)` (exogenous terms and
the initial dispersion), `Θ = ThetaCalvo`, `κ` of (2.19), `x₁_t = gap(y₁_t, ξ₁_t)`. The
Layer-A identity used is `PriceDispersion.calvo_welfare_sum`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem calvo_bridge (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0) {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) {D qd R : ℝ → ℕ → ℝ}
    {q1 : ℕ → ℝ} (hdem : ∀ ε t, crossVar M.w (yh t ε) = M.θ ^ 2 * D ε (t + 1))
    (hrec : ∀ ε t, D ε (t + 1) = α * D ε t + α / (1 - α) * qd ε t ^ 2 + R ε t)
    (hq : (fun p : ℕ × ℝ => qd p.2 p.1 - p.2 * q1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hq1 : ∃ C, ∀ t, |q1 t| ≤ C)
    (hR : (fun p : ℕ × ℝ => R p.2 p.1) =O[unif] fun p => p.2 ^ 3) :
    (fun ε => ∑' t, β ^ t * M.Ustate (yh t ε) (ε • ξ1 t) -
      ((∑' t, β ^ t * M.tipState (ε • ξ1 t) -
          M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * D ε 0 / (1 - α * β)))) +
        ε ^ 2 / 2 * (-(M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) *
          ∑' t, β ^ t * (q1 t ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
            M.gap (y1 t) (ξ1 t) ^ 2))))) =O[𝓝 0] fun ε => ε ^ 3 := by
  have hYb0 : M.Yb ≠ 0 := hM.Yb_pos.ne'
  have huc0 : M.uc ≠ 0 := hM.uc_pos.ne'
  -- uniform orders
  have hyu : (fun p : ℕ × ℝ => yh p.1 p.2) =O[unif] fun p => p.2 :=
    family_isBigO (s := fun p : ℕ × ℝ => p.2) tendsto_unif h (unif_of_bounded hy1)
  have hx1 : (fun p : ℕ × ℝ => ξ1 p.1) =O[unif] fun _ => (1 : ℝ) := unif_of_bounded hξ1
  have hξu : (fun p : ℕ × ℝ => p.2 • ξ1 p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).smul hx1).congr_right fun _ => mul_one _
  have hρ := prop61_state_poly (l := unif) (s := fun p : ℕ × ℝ => p.2)
    (yh := fun p : ℕ × ℝ => yh p.1 p.2) (ξ := fun p : ℕ × ℝ => p.2 • ξ1 p.1) hM heff hden
    tendsto_unif hyu hξu
  have hX1 : (fun p : ℕ × ℝ => M.gap (y1 p.1) (ξ1 p.1)) =O[unif] fun _ => (1 : ℝ) :=
    (crossMean_isBigO hM.w_nonneg hM.w_sum (unif_of_bounded hy1)).sub
      (natLin_isBigO M.sig M.omg (M.gS_isBigO hx1) (M.qS_isBigO hx1))
  have hXd : (fun p : ℕ × ℝ => M.gap (yh p.1 p.2) (p.2 • ξ1 p.1) -
      p.2 * M.gap (y1 p.1) (ξ1 p.1)) =O[unif] fun p => p.2 ^ 2 :=
    (crossMean_isBigO hM.w_nonneg hM.w_sum h).congr_left fun p => (gap_smul_sub _ _ _ _).symm
  have hX2 := sq_sub_sq_isBigO tendsto_unif hXd hX1
  have hq1u : (fun p : ℕ × ℝ => q1 p.1) =O[unif] fun _ => (1 : ℝ) := unif_of_bounded
    (by obtain ⟨C, hC⟩ := hq1; exact ⟨C, fun t => by simpa using hC t⟩)
  have hq2 := sq_sub_sq_isBigO tendsto_unif hq hq1u
  -- the three remainders
  have S1 := tsum_isBigO_of_unif (f := fun t ε => (qd ε t ^ 2 - ε ^ 2 * q1 t ^ 2) +
    Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
      (M.gap (yh t ε) (ε • ξ1 t) ^ 2 - ε ^ 2 * M.gap (y1 t) (ξ1 t) ^ 2)) hβ0 hβ1
    (hq2.add (hX2.const_mul_left _))
  have S2 := tsum_isBigO_of_unif (f := fun t ε => M.Ustate (yh t ε) (ε • ξ1 t) -
    (M.tipState (ε • ξ1 t) - M.Yb * M.uc / 2 * M.lossB (yh t ε) (ε • ξ1 t))) hβ0 hβ1 hρ
  have S3 := tsum_isBigO_of_unif (f := fun t ε => R ε t) hβ0 hβ1 hR
  -- boundedness for each small `ε`
  have one : (fun p : ℕ × ℝ => p.2) =O[unif] fun _ => (1 : ℝ) := tendsto_unif.isBigO_one ℝ
  have b2 : ∀ {n : ℕ}, (fun p : ℕ × ℝ => p.2 ^ n) =O[unif] fun _ => (1 : ℝ) := fun {n} =>
    (one.pow n).congr_right fun _ => one_pow n
  have hqb : (fun p : ℕ × ℝ => qd p.2 p.1) =O[unif] fun _ => (1 : ℝ) :=
    ((hq.trans b2).add ((one.mul hq1u).congr_right fun _ => mul_one 1)).congr_left
      fun p => by ring
  have hXb : (fun p : ℕ × ℝ => M.gap (yh p.1 p.2) (p.2 • ξ1 p.1)) =O[unif]
      fun _ => (1 : ℝ) :=
    ((hXd.trans b2).add ((one.mul hX1).congr_right fun _ => mul_one 1)).congr_left
      fun p => by ring
  have hX1b := bounded_of_unif (f := fun t => M.gap (y1 t) (ξ1 t)) hX1
  obtain ⟨Cq, hCq⟩ := hq1
  have hq1b : SeqW.Bdd q1 := ⟨Cq, hCq⟩
  have hBb : SeqW.Bdd (fun t => q1 t ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
      M.gap (y1 t) (ξ1 t) ^ 2) :=
    (hq1b.pow 2).add ((SeqW.Bdd.const _).mul ((show SeqW.Bdd
      (fun t => M.gap (y1 t) (ξ1 t)) from hX1b).pow 2))
  have hcomb := ((S1.const_mul_left (-(M.Yb * M.uc * PriceDispersion.ThetaCalvo α β M.θ M.omg))).add
    S2).sub (S3.const_mul_left (M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 / (1 - α * β))))
  refine hcomb.congr' ?_ EventuallyEq.rfl
  filter_upwards [bdd_of_unif (f := fun t ε => qd ε t) (g := fun _ => (1 : ℝ)) hqb,
    bdd_of_unif (f := fun t ε => M.gap (yh t ε) (ε • ξ1 t)) (g := fun _ => (1 : ℝ)) hXb,
    bdd_of_unif (f := fun t ε => R ε t) (g := fun _ => (1 : ℝ)) (hR.trans b2),
    bdd_of_unif (f := fun t ε => M.tipState (ε • ξ1 t)) (g := fun _ => (1 : ℝ))
      (tipState_unif hξ1),
    bdd_of_unif (f := fun t ε => M.Ustate (yh t ε) (ε • ξ1 t) -
      (M.tipState (ε • ξ1 t) - M.Yb * M.uc / 2 * M.lossB (yh t ε) (ε • ξ1 t)))
      (g := fun _ => (1 : ℝ)) (hρ.trans b2)]
    with ε bq bX bR bT bρ
  obtain ⟨M1, hM1, hb1⟩ := bq.nonneg_bound
  obtain ⟨M2, hM2, hb2⟩ := bX.nonneg_bound
  obtain ⟨M3, hM3, hb3⟩ := bR.nonneg_bound
  obtain ⟨M4, hM4, hb4⟩ := (bT.div_const (M.Yb * M.uc)).nonneg_bound
  obtain ⟨M5, hM5, hb5⟩ := (bρ.div_const (M.Yb * M.uc)).nonneg_bound
  have hW : ∀ t, M.Ustate (yh t ε) (ε • ξ1 t) / (M.Yb * M.uc) = -(1 / 2) * ((M.sig + M.omg) *
      M.gap (yh t ε) (ε • ξ1 t) ^ 2 + M.θ * (1 + M.omg * M.θ) * D ε (t + 1)) +
      M.tipState (ε • ξ1 t) / (M.Yb * M.uc) + (M.Ustate (yh t ε) (ε • ξ1 t) -
        (M.tipState (ε • ξ1 t) - M.Yb * M.uc / 2 * M.lossB (yh t ε) (ε • ξ1 t))) /
          (M.Yb * M.uc) := fun t => by
    have hl : M.lossB (yh t ε) (ε • ξ1 t) = (M.sig + M.omg) * M.gap (yh t ε) (ε • ξ1 t) ^ 2 +
        M.θ * (1 + M.omg * M.θ) * D ε (t + 1) := by
      unfold lossB
      rw [hdem, Prop61.lossQ_disp hθ]
      rfl
    rw [hl]
    field_simp
    ring
  have hV := PriceDispersion.calvo_welfare_sum (M := M1 + M2 + M3 + M4 + M5) hα0 hα1 hβ0 hβ1
    hθ hd (hrec ε) hW (fun t => by linarith [hb1 t]) (fun t => by linarith [hb2 t])
    (fun t => by linarith [hb3 t]) (fun t => by linarith [hb4 t]) (fun t => by linarith [hb5 t])
  have e1 : ∑' t, β ^ t * M.Ustate (yh t ε) (ε • ξ1 t) =
      M.Yb * M.uc * ∑' t, β ^ t * (M.Ustate (yh t ε) (ε • ξ1 t) / (M.Yb * M.uc)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by field_simp
  have e2 : M.Yb * M.uc * ∑' t, β ^ t * (M.tipState (ε • ξ1 t) / (M.Yb * M.uc)) =
      ∑' t, β ^ t * M.tipState (ε • ξ1 t) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by field_simp
  have e3 : M.Yb * M.uc * ∑' t, β ^ t * ((M.Ustate (yh t ε) (ε • ξ1 t) -
      (M.tipState (ε • ξ1 t) - M.Yb * M.uc / 2 * M.lossB (yh t ε) (ε • ξ1 t))) /
        (M.Yb * M.uc)) =
      ∑' t, β ^ t * (M.Ustate (yh t ε) (ε • ξ1 t) -
        (M.tipState (ε • ξ1 t) - M.Yb * M.uc / 2 * M.lossB (yh t ε) (ε • ξ1 t))) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by field_simp
  have hAb : SeqW.Bdd (fun t => qd ε t ^ 2 +
      Moments.calvoKappa α β M.omg M.θ M.sig / M.θ * M.gap (yh t ε) (ε • ξ1 t) ^ 2) :=
    (bq.pow 2).add ((SeqW.Bdd.const _).mul (bX.pow 2))
  have e4 : ∑' t, β ^ t * ((qd ε t ^ 2 - ε ^ 2 * q1 t ^ 2) +
      Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
        (M.gap (yh t ε) (ε • ξ1 t) ^ 2 - ε ^ 2 * M.gap (y1 t) (ξ1 t) ^ 2)) =
      ∑' t, β ^ t * (qd ε t ^ 2 +
        Moments.calvoKappa α β M.omg M.θ M.sig / M.θ * M.gap (yh t ε) (ε • ξ1 t) ^ 2) -
        ε ^ 2 * ∑' t, β ^ t * (q1 t ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
          M.gap (y1 t) (ξ1 t) ^ 2) := by
    rw [← tsum_mul_left, ← (hAb.summable hβ0 hβ1).tsum_sub
      ((hBb.summable hβ0 hβ1).mul_left _)]
    exact tsum_congr fun t => by ring
  rw [e1, hV.tsum_eq, e4]
  linear_combination -(e2 + e3)

/-- Woodford (2003), **Proposition 6.4, eqs. (2.21)–(2.22), p. 400 (Layer B)**. Calvo pricing
without indexation (`infl ε (t+1) = π_t`, `infl ε 0 = π_{−1}`): under the hypotheses of
`calvo_bridge` with `q_t = π_t`, and `π_t(ε) − ε π₁_t = O(ε²)` uniformly in `t`,
`∑ βᵗ U_t(ε) = TIP(ε) − (ε²/2) Ȳu_c · 2Θ ∑ βᵗ (π₁_t² + λ x₁_t²) + O(ε³)`, `λ = κ/θ` with `κ`
of (2.19).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop64_bridge (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0) {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) {D infl R : ℝ → ℕ → ℝ}
    {π1 : ℕ → ℝ} (hdem : ∀ ε t, crossVar M.w (yh t ε) = M.θ ^ 2 * D ε (t + 1))
    (hrec : ∀ ε t, D ε (t + 1) = α * D ε t + α / (1 - α) * infl ε (t + 1) ^ 2 + R ε t)
    (hπ : (fun p : ℕ × ℝ => infl p.2 p.1 - p.2 * π1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hπ1 : ∃ C, ∀ t, |π1 t| ≤ C)
    (hR : (fun p : ℕ × ℝ => R p.2 p.1) =O[unif] fun p => p.2 ^ 3) :
    (fun ε => ∑' t, β ^ t * M.Ustate (yh t ε) (ε • ξ1 t) -
      ((∑' t, β ^ t * M.tipState (ε • ξ1 t) -
          M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * D ε 0 / (1 - α * β)))) +
        ε ^ 2 / 2 * (-(M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) *
          ∑' t, β ^ t * (π1 (t + 1) ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
            M.gap (y1 t) (ξ1 t) ^ 2))))) =O[𝓝 0] fun ε => ε ^ 3 := by
  obtain ⟨C, hC⟩ := hπ1
  exact calvo_bridge (qd := fun ε t => infl ε (t + 1)) (q1 := fun t => π1 (t + 1)) hM heff hden
    hθ hd hα0 hα1 hβ0 hβ1 h hy1 hξ1 hdem hrec
    (unif_shift (f := fun t ε => infl ε t - ε * π1 t) (g := fun ε => ε ^ 2) hπ)
    ⟨C, fun t => hC (t + 1)⟩ hR

/-- Woodford (2003), **Proposition 6.5, eq. (2.25), p. 402 (Layer B)**. Calvo pricing with
indexation to lagged inflation (`q_t = π_t − γπ_{t−1}`, (2.23)–(2.24),
PriceDispersion.index_layerA): with `π_t(ε) − ε π₁_t = O(ε²)` uniformly in `t` (all dates
including `π_{−1}`),
`∑ βᵗ U_t(ε) = TIP(ε) − (ε²/2) Ȳu_c · 2Θ ∑ βᵗ ((π₁_t − γπ₁_{t−1})² + λ x₁_t²) + O(ε³)`.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop65_bridge (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0) {α β γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) {D infl R : ℝ → ℕ → ℝ}
    {π1 : ℕ → ℝ} (hdem : ∀ ε t, crossVar M.w (yh t ε) = M.θ ^ 2 * D ε (t + 1))
    (hrec : ∀ ε t, D ε (t + 1) =
      α * D ε t + α / (1 - α) * (infl ε (t + 1) - γ * infl ε t) ^ 2 + R ε t)
    (hπ : (fun p : ℕ × ℝ => infl p.2 p.1 - p.2 * π1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hπ1 : ∃ C, ∀ t, |π1 t| ≤ C)
    (hR : (fun p : ℕ × ℝ => R p.2 p.1) =O[unif] fun p => p.2 ^ 3) :
    (fun ε => ∑' t, β ^ t * M.Ustate (yh t ε) (ε • ξ1 t) -
      ((∑' t, β ^ t * M.tipState (ε • ξ1 t) -
          M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * D ε 0 / (1 - α * β)))) +
        ε ^ 2 / 2 * (-(M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) *
          ∑' t, β ^ t * ((π1 (t + 1) - γ * π1 t) ^ 2 +
            Moments.calvoKappa α β M.omg M.θ M.sig / M.θ * M.gap (y1 t) (ξ1 t) ^ 2))))) =O[𝓝 0]
      fun ε => ε ^ 3 := by
  obtain ⟨C, hC⟩ := hπ1
  have hs := unif_shift (f := fun t ε => infl ε t - ε * π1 t) (g := fun ε => ε ^ 2) hπ
  have hq : (fun p : ℕ × ℝ => (infl p.2 (p.1 + 1) - γ * infl p.2 p.1) -
      p.2 * (π1 (p.1 + 1) - γ * π1 p.1)) =O[unif] fun p => p.2 ^ 2 :=
    (hs.sub (hπ.const_mul_left γ)).congr_left fun p => by ring
  refine calvo_bridge (qd := fun ε t => infl ε (t + 1) - γ * infl ε t)
    (q1 := fun t => π1 (t + 1) - γ * π1 t) hM heff hden hθ hd hα0 hα1 hβ0 hβ1 h hy1 hξ1 hdem
    hrec hq ⟨C + |γ| * C, fun t => ?_⟩ hR
  have h1 := hC (t + 1)
  have h2 := hC t
  calc |π1 (t + 1) - γ * π1 t| ≤ |π1 (t + 1)| + |γ * π1 t| := abs_sub _ _
    _ ≤ C + |γ| * C := by
      rw [abs_mul]
      gcongr

/-- Woodford (2003), §2.2, Prop. 6.4, p. 400 (**welfare ranking by the discounted Calvo loss**):
two policies `A`, `B` with the same disturbances `ε ξ₁_t` and the same initial dispersion
`Δ_{−1}(ε)`, each satisfying the hypotheses of `prop64_bridge`; if the discounted first-order loss
`∑ βᵗ (π₁_t² + λ x₁_t²)` of `A` is smaller, `A` is strictly better for all small `ε > 0`
(`θ > 0`, `1 + ωθ > 0`, `β < 1`).
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop64_ranking (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hθ : 0 < M.θ) (hd : 0 < 1 + M.omg * M.θ) {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ξ1 : ℕ → Ξ} (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    {yA yB : ℕ → ℝ → ι → ℝ} {yA1 yB1 : ℕ → ι → ℝ}
    (hA : (fun p : ℕ × ℝ => yA p.1 p.2 - p.2 • yA1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hB : (fun p : ℕ × ℝ => yB p.1 p.2 - p.2 • yB1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hyA : ∃ C, ∀ t, ‖yA1 t‖ ≤ C) (hyB : ∃ C, ∀ t, ‖yB1 t‖ ≤ C)
    {DA DB iA iB RA RB : ℝ → ℕ → ℝ} {πA πB : ℕ → ℝ}
    (hdA : ∀ ε t, crossVar M.w (yA t ε) = M.θ ^ 2 * DA ε (t + 1))
    (hdB : ∀ ε t, crossVar M.w (yB t ε) = M.θ ^ 2 * DB ε (t + 1))
    (hD0 : ∀ ε, DA ε 0 = DB ε 0)
    (hrA : ∀ ε t, DA ε (t + 1) = α * DA ε t + α / (1 - α) * iA ε (t + 1) ^ 2 + RA ε t)
    (hrB : ∀ ε t, DB ε (t + 1) = α * DB ε t + α / (1 - α) * iB ε (t + 1) ^ 2 + RB ε t)
    (hπA : (fun p : ℕ × ℝ => iA p.2 p.1 - p.2 * πA p.1) =O[unif] fun p => p.2 ^ 2)
    (hπB : (fun p : ℕ × ℝ => iB p.2 p.1 - p.2 * πB p.1) =O[unif] fun p => p.2 ^ 2)
    (hπA1 : ∃ C, ∀ t, |πA t| ≤ C) (hπB1 : ∃ C, ∀ t, |πB t| ≤ C)
    (hRA : (fun p : ℕ × ℝ => RA p.2 p.1) =O[unif] fun p => p.2 ^ 3)
    (hRB : (fun p : ℕ × ℝ => RB p.2 p.1) =O[unif] fun p => p.2 ^ 3)
    (hL : ∑' t, β ^ t * (πA (t + 1) ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
        M.gap (yA1 t) (ξ1 t) ^ 2) <
      ∑' t, β ^ t * (πB (t + 1) ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
        M.gap (yB1 t) (ξ1 t) ^ 2)) :
    ∀ᶠ ε in 𝓝[>] 0, ∑' t, β ^ t * M.Ustate (yB t ε) (ε • ξ1 t) <
      ∑' t, β ^ t * M.Ustate (yA t ε) (ε • ξ1 t) := by
  have hk : 0 < M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) :=
    mul_pos (mul_pos hM.Yb_pos hM.uc_pos)
      (mul_pos two_pos (PriceDispersion.ThetaCalvo_pos hα0 hα1 hβ1 hθ hd))
  have bA := prop64_bridge hM heff hden hθ.ne' hd.ne' hα0 hα1 hβ0 hβ1 hA hyA hξ1 hdA hrA hπA
    hπA1 hRA
  have bB := prop64_bridge hM heff hden hθ.ne' hd.ne' hα0 hα1 hβ0 hβ1 hB hyB hξ1 hdB hrB hπB
    hπB1 hRB
  simp only [hD0] at bA
  exact ranking_of_tip hk bA bB hL

/-- Woodford (2003), §2.2, Prop. 6.5, p. 402 (**welfare ranking with indexation**): as
`prop64_ranking`, with the quasi-differenced inflation `π₁_t − γπ₁_{t−1}` in the loss.
(Restated from the Woodford Chapter 6 StabilizationWelfare project.) -/
theorem prop65_ranking (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hθ : 0 < M.θ) (hd : 0 < 1 + M.omg * M.θ) {α β γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ξ1 : ℕ → Ξ} (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    {yA yB : ℕ → ℝ → ι → ℝ} {yA1 yB1 : ℕ → ι → ℝ}
    (hA : (fun p : ℕ × ℝ => yA p.1 p.2 - p.2 • yA1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hB : (fun p : ℕ × ℝ => yB p.1 p.2 - p.2 • yB1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hyA : ∃ C, ∀ t, ‖yA1 t‖ ≤ C) (hyB : ∃ C, ∀ t, ‖yB1 t‖ ≤ C)
    {DA DB iA iB RA RB : ℝ → ℕ → ℝ} {πA πB : ℕ → ℝ}
    (hdA : ∀ ε t, crossVar M.w (yA t ε) = M.θ ^ 2 * DA ε (t + 1))
    (hdB : ∀ ε t, crossVar M.w (yB t ε) = M.θ ^ 2 * DB ε (t + 1))
    (hD0 : ∀ ε, DA ε 0 = DB ε 0)
    (hrA : ∀ ε t, DA ε (t + 1) =
      α * DA ε t + α / (1 - α) * (iA ε (t + 1) - γ * iA ε t) ^ 2 + RA ε t)
    (hrB : ∀ ε t, DB ε (t + 1) =
      α * DB ε t + α / (1 - α) * (iB ε (t + 1) - γ * iB ε t) ^ 2 + RB ε t)
    (hπA : (fun p : ℕ × ℝ => iA p.2 p.1 - p.2 * πA p.1) =O[unif] fun p => p.2 ^ 2)
    (hπB : (fun p : ℕ × ℝ => iB p.2 p.1 - p.2 * πB p.1) =O[unif] fun p => p.2 ^ 2)
    (hπA1 : ∃ C, ∀ t, |πA t| ≤ C) (hπB1 : ∃ C, ∀ t, |πB t| ≤ C)
    (hRA : (fun p : ℕ × ℝ => RA p.2 p.1) =O[unif] fun p => p.2 ^ 3)
    (hRB : (fun p : ℕ × ℝ => RB p.2 p.1) =O[unif] fun p => p.2 ^ 3)
    (hL : ∑' t, β ^ t * ((πA (t + 1) - γ * πA t) ^ 2 +
        Moments.calvoKappa α β M.omg M.θ M.sig / M.θ * M.gap (yA1 t) (ξ1 t) ^ 2) <
      ∑' t, β ^ t * ((πB (t + 1) - γ * πB t) ^ 2 +
        Moments.calvoKappa α β M.omg M.θ M.sig / M.θ * M.gap (yB1 t) (ξ1 t) ^ 2)) :
    ∀ᶠ ε in 𝓝[>] 0, ∑' t, β ^ t * M.Ustate (yB t ε) (ε • ξ1 t) <
      ∑' t, β ^ t * M.Ustate (yA t ε) (ε • ξ1 t) := by
  have hk : 0 < M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) :=
    mul_pos (mul_pos hM.Yb_pos hM.uc_pos)
      (mul_pos two_pos (PriceDispersion.ThetaCalvo_pos hα0 hα1 hβ1 hθ hd))
  have bA := prop65_bridge hM heff hden hθ.ne' hd.ne' hα0 hα1 hβ0 hβ1 hA hyA hξ1 hdA hrA hπA
    hπA1 hRA
  have bB := prop65_bridge hM heff hden hθ.ne' hd.ne' hα0 hα1 hβ0 hβ1 hB hyB hξ1 hdB hrB hπB
    hπB1 hRB
  simp only [hD0] at bA
  exact ranking_of_tip hk bA bB hL

end Econ

end BridgeCore

end Woodford.GainsFromCommitment.TidyR6WelfBridge
