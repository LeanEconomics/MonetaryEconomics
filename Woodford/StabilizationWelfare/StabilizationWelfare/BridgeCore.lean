/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.ApproxTheory
import StabilizationWelfare.PriceDispersion
import StabilizationWelfare.HabitWelfare

/-!
# Layer B: from actual utility to the quadratic losses of Chapter 6

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392), §2 (pp. 392–405) and
Appendix E.1–E.3 (pp. 692–698).

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392), §2 (pp. 392–405) and
Appendix E.1–E.3 (pp. 692–698); survey §4, Layer B (option B1, one-parameter perturbation).

Layer A (`Prop61`, `PriceDispersion`, `HabitWelfare`) proves the exact polynomial identities
behind Propositions 6.1–6.6. This module connects them to the ACTUAL utility: along a family
with disturbances `ε ξ₁` and a cross-section `ŷ(ε)` with first-order solution `y₁`,
`W(ε) = t.i.p.(ε) − (ε²/2) Ȳ u_c L(first-order solution) + O(ε³)`, and the welfare ranking
follows (`ranking_of_tip`, from `OneParamTaylor.welfare_ranking_of_loss`).

## Setting and conventions

* `Econ`: `ũ, ṽ : ℝ × Ξ → ℝ` (`Ξ` the normed space of disturbances), the expansion point `Ȳ`,
  the elasticity `θ`, probability weights on a finite set of goods. `Econ.Std` lists the
  maintained assumptions; `C³` is required (survey error 19).
* The expansion is at the EFFICIENT steady state (`ṽ_y = u_c`; with habits
  `ṽ_y = (1 − βη)u_c`). A distortion `Φ = εΦ₁` then enters only through the allocation: the gap
  measured from `Y*` is exactly Woodford's `x − x*` (`gap_eq_woodford`) and `x*(ε)` has derivative
  `Φ₁/(σ⁻¹ + ω)` (`xstar_hasDerivAt`, from (2.9)). This settles survey imprecision 26 (`Ȳ` moving
  with `Φ`) without an expansion around a moving point.
* Families: `ŷ(ε) − ε y₁ = O(ε²)`, weaker than `C³` (a `C²` family qualifies,
  `family_of_contDiff`). The proofs run along an arbitrary filter with a rate `s → 0`
  (`taylor_pair`, `ces_orders`, `prop61_state`).
* Uniformity in `t` (survey error 25): the filter `unif = ⊤ ×ˢ 𝓝 0`; `isBigO_unif_iff` shows it
  means one constant for all dates; `tsum_isBigO_of_unif` (discounted sums) and
  `finsum_bound_of_unif` (finite horizons, bound uniform in the horizon) turn uniform period
  remainders into `O(ε³)` welfare remainders.

## Main results

* Proposition 6.1: `prop61_state`, `prop61_state_poly` (state variables, any filter),
  `prop61_family`, `prop61_bridge`, `prop61_expansion` (`W(0) + εW′(0) + (ε²/2)W″(0) + O(ε³)`),
  `prop61_ranking`, `prop61_discounted`, `prop61_discounted_ranking`, `prop61_expected`.
* Proposition 6.2: `lossB_NC`, `prop62_bridge`, `prop62_ranking`.
* Proposition 6.3: `prop63_first_order` (the first-order dispersion obeys (2.20) exactly).
* Propositions 6.4–6.5: `calvo_bridge` (via `PriceDispersion.calvo_welfare_sum`),
  `prop64_bridge`, `prop65_bridge`, `prop64_ranking`, `prop65_ranking`.
* Proposition 6.6 corrected (survey error 16): `habit_state`, `prop66_bridge` (via
  `HabitWelfare.prop66_corrected`), `prop66_ranking`, `habPar_spec`.

## Tools proved here

Order bookkeeping on a general filter (`pow_isBigO_pow`, `isBigO_pow_mul`, `sq_sub_sq_isBigO`,
`expRem_isBigO`), the Taylor step in `(level, ξ)` (`quadApprox_pair`, `taylor_pair`,
`level_taylor`, `uside_gen`, `vside_gen`), remainder orders (`Ru_isBigO`, `Rv_isBigO`,
`R3_zero_isBigO`, `E10rem_isBigO`, `vRem_isBigO`), the cross-sectional covariance
(`crossCov`, `crossVar_family`), two-point dispersion (`crossVar_twoPoint`), discounted bridges
(`discounted_bridge`, `discounted_ranking`), coefficient matching (`coeff_two_unique`) and
expectations over a finite state space (`expect_bridge`).
-/

namespace Woodford.StabilizationWelfare.BridgeCore

open Filter Topology Asymptotics
open ExpLogCES (crossMean crossVar cumulant cesIndex expRem)
open Prop61 (Tu Tv Ru Rv natLin xStarLin tipA R3 lossQ sigmaInvEl omegaEl gShock qShock)

/-! ## Orders of magnitude along a general filter

`f = O(sⁿ)` along a filter `l`, with `s → 0`. The filter is `𝓝 0` for a one-parameter family,
`𝓝 0` on a state space for a statement in the state variables, and `unif` (below) for a statement
uniform in the date `t`. -/

variable {α : Type*} {l : Filter α} {s : α → ℝ}

/-- Woodford (2003), (2.11), p. 395 (bookkeeping of orders): `sᵇ = O(sᵃ)` for `a ≤ b` when
`s → 0`. -/
theorem pow_isBigO_pow (hs : Tendsto s l (𝓝 0)) {a b : ℕ} (hab : a ≤ b) :
    (fun x => s x ^ b) =O[l] (fun x => s x ^ a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : (fun x => s x ^ k) =O[l] (fun _ => (1 : ℝ)) := (hs.pow k).isBigO_one ℝ
  exact ((isBigO_refl (fun x => s x ^ a) l).mul h1).congr (fun x => by ring) (fun x => by ring)

/-- Woodford (2003), (2.11), p. 395: orders multiply, `O(sᵃ) · O(sᵇ) = O(sᶜ)` for
`a + b = c`. -/
theorem isBigO_pow_mul {f g : α → ℝ} {a b c : ℕ} (hf : f =O[l] fun x => s x ^ a)
    (hg : g =O[l] fun x => s x ^ b) (habc : a + b = c) :
    (fun x => f x * g x) =O[l] fun x => s x ^ c :=
  (hf.mul hg).congr_right fun x => by rw [← habc, pow_add]

/-- Woodford (2003), (2.11), p. 395: a bounded factor does not change the order. -/
theorem isBigO_mul_bdd {f g : α → ℝ} {a : ℕ} (hf : f =O[l] fun x => s x ^ a)
    (hg : g =O[l] fun _ => (1 : ℝ)) : (fun x => f x * g x) =O[l] fun x => s x ^ a :=
  (hf.mul hg).congr_right fun x => by ring

/-- Woodford (2003), App. E (`(a + O(2))² = a² + O(3)`, the lemma L-square of the survey): if
`f − s f₁ = O(s²)` with `f₁` bounded, then `f² − s² f₁² = O(s³)`. -/
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
`e^Y = 1 + Y + Y²/2 + expRem Y` is `O(s³)`. -/
theorem expRem_isBigO (hs : Tendsto s l (𝓝 0)) {Y : α → ℝ} (hY : Y =O[l] s) :
    (fun x => expRem (Y x)) =O[l] fun x => s x ^ 3 := by
  have hYt : Tendsto Y l (𝓝 0) := hY.trans_tendsto hs
  have h := ExpLogCES.exp_taylor2_isBigO.comp_tendsto hYt
  refine (h.trans (hY.pow 3)).congr_left fun x => ?_
  simp only [Function.comp, expRem]
  ring

/-- Woodford (2003), App. E.1, p. 693: `e^Y − 1 = O(Y)`, so `Y = O(s)` gives `e^Y − 1 = O(s)`. -/
theorem exp_sub_one_isBigO (hs : Tendsto s l (𝓝 0)) {Y : α → ℝ} (hY : Y =O[l] s) :
    (fun x => Real.exp (Y x) - 1) =O[l] s := by
  have hYt : Tendsto Y l (𝓝 0) := hY.trans_tendsto hs
  have h := (Real.hasDerivAt_exp 0).isBigO_sub.comp_tendsto hYt
  refine (h.trans (hY.congr_left fun x => by simp)).congr_left fun x => ?_
  simp

/-! ## Uniformity in the date `t` (survey error 25)

Discounted sums of `O(ε³)` period remainders are `O(ε³)` only if the period bounds are uniform in
`t`. We encode "uniformly in `t` as `ε → 0`" by the product filter `unif = ⊤ ×ˢ 𝓝 0` on
`ℕ × ℝ`: `isBigO_unif_iff` shows that `f =O[unif] g` means exactly
`∃ C, ∀ᶠ ε in 𝓝 0, ∀ t, ‖f t ε‖ ≤ C ‖g ε‖`. -/

/-- Woodford (2003), App. E.2, p. 695 (survey error 25): the filter "uniformly in the date `t`,
as the amplitude `ε → 0`", `⊤ ×ˢ 𝓝 0` on `ℕ × ℝ`. -/
abbrev unif : Filter (ℕ × ℝ) := (⊤ : Filter ℕ) ×ˢ 𝓝 (0 : ℝ)

/-- Woodford (2003), App. E.2, p. 695: the amplitude tends to zero along `unif`. -/
theorem tendsto_unif : Tendsto (fun p : ℕ × ℝ => p.2) unif (𝓝 0) := tendsto_snd

/-- Woodford (2003), App. E.2, p. 695 and survey error 25 (**what the uniformity hypothesis
says**): `f =O[unif] g` iff there is one constant `C` with `‖f t ε‖ ≤ C ‖g ε‖` for every date `t`
and every small `ε`. -/
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

/-- Woodford (2003), App. E.2, p. 695: a bound uniform in `t` holds at each fixed date. -/
theorem isBigO_of_unif {E : Type*} [Norm E] {f : ℕ → ℝ → E} {g : ℝ → ℝ}
    (h : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => g p.2)) (t : ℕ) :
    (fun ε => f t ε) =O[𝓝 0] g := by
  obtain ⟨C, hC⟩ := isBigO_unif_iff.1 h
  exact IsBigO.of_bound C (hC.mono fun ε hε => hε t)

/-- Woodford (2003), App. E.3, p. 697: a sequence that is `O(g)` uniformly in `t` is a bounded
sequence for every small `ε`. -/
theorem bdd_of_unif {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => g p.2)) :
    ∀ᶠ ε in 𝓝 0, Sequences.Bdd (fun t => f t ε) := by
  obtain ⟨C, hC⟩ := isBigO_unif_iff.1 h
  filter_upwards [hC] with ε hε
  exact ⟨C * ‖g ε‖, fun t => by simpa [Real.norm_eq_abs] using hε t⟩

/-- Woodford (2003), (2.21), p. 400, and survey error 25 (**discounted sums of uniformly small
remainders**): if `f t ε = O(εⁿ)` uniformly in `t` and `0 ≤ β < 1`, then
`∑ βᵗ f t ε = O(εⁿ)`, with constant `C/(1 − β)`. -/
theorem tsum_isBigO_of_unif {f : ℕ → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {n : ℕ}
    (hf : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => p.2 ^ n)) :
    (fun ε => ∑' t, β ^ t * f t ε) =O[𝓝 0] (fun ε => ε ^ n) := by
  obtain ⟨C, hC⟩ := (isBigO_unif_iff (g := fun ε => ε ^ n)).1 hf
  refine IsBigO.of_bound (C / (1 - β)) ?_
  filter_upwards [hC] with ε hε
  have h := Sequences.abs_tsum_le (f := fun t => f t ε) (B := C * ‖ε ^ n‖)
    (fun t => by simpa [Real.norm_eq_abs] using hε t) hβ0 hβ1
  rw [Real.norm_eq_abs]
  calc _ ≤ C * ‖ε ^ n‖ / (1 - β) := h
    _ = C / (1 - β) * ‖ε ^ n‖ := by ring

/-- Woodford (2003), (2.21), p. 400, survey error 25 (**finite horizons, bound uniform in the
horizon**): if `f t ε = O(εⁿ)` uniformly in `t`, there is one `C` such that for all small `ε`
and EVERY horizon `T`, `|∑_{t<T} βᵗ f t ε| ≤ C |ε|ⁿ`. -/
theorem finsum_bound_of_unif {f : ℕ → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {n : ℕ}
    (hf : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] (fun p => p.2 ^ n)) :
    ∃ C, ∀ᶠ ε in 𝓝 0, ∀ T : ℕ, |∑ t ∈ Finset.range T, β ^ t * f t ε| ≤ C * |ε| ^ n := by
  obtain ⟨C, hC⟩ := (isBigO_unif_iff (g := fun ε => ε ^ n)).1 hf
  refine ⟨max C 0 / (1 - β), ?_⟩
  filter_upwards [hC] with ε hε T
  have h1β : 0 < 1 - β := by linarith
  have hgeom : ∑ t ∈ Finset.range T, β ^ t ≤ 1 / (1 - β) := by
    have hs := summable_geometric_of_lt_one hβ0 hβ1
    calc ∑ t ∈ Finset.range T, β ^ t ≤ ∑' t, β ^ t :=
          hs.sum_le_tsum _ (fun t _ => pow_nonneg hβ0 t)
      _ = 1 / (1 - β) := by rw [tsum_geometric_of_lt_one hβ0 hβ1, one_div]
  have hb : ∀ t, |β ^ t * f t ε| ≤ β ^ t * (max C 0 * |ε| ^ n) := fun t => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
    have := hε t
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  calc |∑ t ∈ Finset.range T, β ^ t * f t ε|
      ≤ ∑ t ∈ Finset.range T, |β ^ t * f t ε| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range T, β ^ t * (max C 0 * |ε| ^ n) := Finset.sum_le_sum fun t _ => hb t
    _ = (∑ t ∈ Finset.range T, β ^ t) * (max C 0 * |ε| ^ n) := by rw [Finset.sum_mul]
    _ ≤ 1 / (1 - β) * (max C 0 * |ε| ^ n) :=
        mul_le_mul_of_nonneg_right hgeom (by positivity)
    _ = max C 0 / (1 - β) * |ε| ^ n := by ring

/-! ## Welfare ranking with terms independent of policy -/

/-- Woodford (2003), §1, pp. 386–389 and §2 (the use of the quadratic losses): if welfare under
policies `A` and `B` satisfies `W_X ε = tip ε − (ε²/2) k L_X + O(ε³)` with the SAME
policy-independent part `tip` (any function of `ε`), `k > 0` and `L_A < L_B`, then `A` is
strictly better for all small `ε > 0`. -/
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
the `ε²` coefficient of an expansion with cubic remainder is unique. -/
theorem coeff_two_unique {c : ℝ} (h : (fun ε : ℝ => ε ^ 2 * c) =O[𝓝 0] (fun ε => ε ^ 3)) :
    c = 0 := by
  by_contra hc
  apply OneParamTaylor.sq_not_isBigO_cube
  refine (h.const_mul_left c⁻¹).congr_left fun ε => ?_
  field_simp

/-- Woodford (2003), §1, p. 385 (expected welfare over a finite state space): if in every state
`ω` welfare is `W ω ε = T ω ε − (ε²/2) k L ω + O(ε³)`, then expected welfare is
`E W = E T − (ε²/2) k E L + O(ε³)`. -/
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

/-! ## Taylor coefficients of a utility function `U(y; ξ)` at `(ȳ, 0)`

`U : ℝ × Ξ → ℝ` is `ũ(Y; ξ)` (or `u(c; ξ)`, or `ṽ(y; ξ)`), with `Ξ` the normed space of
disturbances `ξ`. Its first and second derivatives at `(ȳ, 0)` give the coefficients of (E.2)–(E.3):
`slope` (`u_c`, `ṽ_y`), `curv` (`u_cc`, `ṽ_yy`), `lin ξ` (`u_ξ ξ`), `cross ξ` (`u_cξ ξ`, the
symmetrised mixed derivative), `quad ξ` (`ξ′u_ξξ ξ`). -/

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.2), p. 692: the gradient `DU(ȳ, 0)`. -/
noncomputable def D1 (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ × Ξ →L[ℝ] ℝ := fderiv ℝ U (yb, 0)

/-- Woodford (2003), (E.2), p. 692: the Hessian `D²U(ȳ, 0)`. -/
noncomputable def D2 (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ × Ξ →L[ℝ] ℝ × Ξ →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ U) (yb, 0)

/-- Woodford (2003), (E.2), p. 692: `u_c = U_y(ȳ, 0)`. -/
noncomputable def slope (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ := D1 U yb (1, 0)

/-- Woodford (2003), (E.2), p. 692: `u_cc = U_yy(ȳ, 0)`. -/
noncomputable def curv (U : ℝ × Ξ → ℝ) (yb : ℝ) : ℝ := D2 U yb (1, 0) (1, 0)

/-- Woodford (2003), (E.2), p. 692: `u_ξ ξ = U_ξ(ȳ, 0) ξ`. -/
noncomputable def lin (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ := D1 U yb (0, ξ)

/-- Woodford (2003), (E.2), p. 692: `u_cξ ξ`, the (symmetrised) mixed second derivative. -/
noncomputable def cross (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ :=
  (D2 U yb (1, 0) (0, ξ) + D2 U yb (0, ξ) (1, 0)) / 2

/-- Woodford (2003), (E.2), p. 692: `ξ′ u_ξξ ξ`. -/
noncomputable def quad (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ := D2 U yb (0, ξ) (0, ξ)

/-- Woodford (2003), (E.2), p. 692: the terms of the expansion independent of policy,
`Ū + u_ξ ξ + ½ ξ′u_ξξ ξ`. -/
noncomputable def tip0 (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : ℝ :=
  U (yb, 0) + lin U yb ξ + quad U yb ξ / 2

/-- Woodford (2003), eq. (1.2), p. 385 and (E.2), p. 692: the quadratic approximation of
`U` at `(ȳ, 0)` in the direction `(a, ξ)` is the polynomial `Prop61.uTaylor` of (E.2) with
coefficients `slope`, `curv`, `lin`, `cross`, `quad`. -/
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
/-- Woodford (2003), App. E: `‖(0, ξ)‖ = ‖ξ‖`. -/
theorem norm_inr (ξ : Ξ) : ‖((0 : ℝ), ξ)‖ = ‖ξ‖ := by
  rw [Prod.norm_def]
  simp

omit [NormedSpace ℝ Ξ] in
/-- Woodford (2003), App. E: `‖(1, 0)‖ = 1`. -/
theorem norm_inl_one : ‖((1 : ℝ), (0 : Ξ))‖ = 1 := by
  rw [Prod.norm_def]
  simp

/-- Woodford (2003), (E.2): `|u_ξ ξ| ≤ ‖DU‖ ‖ξ‖`. -/
theorem abs_lin_le (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : |lin U yb ξ| ≤ ‖D1 U yb‖ * ‖ξ‖ := by
  have h := (D1 U yb).le_opNorm ((0 : ℝ), ξ)
  rwa [norm_inr, Real.norm_eq_abs] at h

/-- Woodford (2003), (E.2): `|u_cξ ξ| ≤ ‖D²U‖ ‖ξ‖`. -/
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

/-- Woodford (2003), (E.2): `|ξ′u_ξξ ξ| ≤ ‖D²U‖ ‖ξ‖²`. -/
theorem abs_quad_le (U : ℝ × Ξ → ℝ) (yb : ℝ) (ξ : Ξ) : |quad U yb ξ| ≤ ‖D2 U yb‖ * ‖ξ‖ ^ 2 := by
  have h := (D2 U yb).le_opNorm₂ ((0 : ℝ), ξ) ((0 : ℝ), ξ)
  rw [norm_inr, Real.norm_eq_abs] at h
  unfold quad
  calc _ ≤ _ := h
    _ = _ := by ring

/-- Woodford (2003), (E.2): `u_ξ (r ξ) = r u_ξ ξ`. -/
theorem lin_smul (U : ℝ × Ξ → ℝ) (yb r : ℝ) (ξ : Ξ) : lin U yb (r • ξ) = r * lin U yb ξ := by
  unfold lin
  rw [show ((0 : ℝ), r • ξ) = r • ((0 : ℝ), ξ) by simp, map_smul, smul_eq_mul]

/-- Woodford (2003), (E.2): `u_cξ (r ξ) = r u_cξ ξ`. -/
theorem cross_smul (U : ℝ × Ξ → ℝ) (yb r : ℝ) (ξ : Ξ) :
    cross U yb (r • ξ) = r * cross U yb ξ := by
  unfold cross
  rw [show ((0 : ℝ), r • ξ) = r • ((0 : ℝ), ξ) by simp]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.2): `(r ξ)′u_ξξ (r ξ) = r² ξ′u_ξξ ξ`. -/
theorem quad_smul (U : ℝ × Ξ → ℝ) (yb r : ℝ) (ξ : Ξ) :
    quad U yb (r • ξ) = r ^ 2 * quad U yb ξ := by
  unfold quad
  rw [show ((0 : ℝ), r • ξ) = r • ((0 : ℝ), ξ) by simp]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.2): `u_ξ ξ = O(ξ)`. -/
theorem lin_isBigO (U : ℝ × Ξ → ℝ) (yb : ℝ) {g : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] g) :
    (fun x => lin U yb (ξ x)) =O[l] g :=
  (IsBigO.of_bound ‖D1 U yb‖ (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact abs_lin_le U yb (ξ x))).trans hξ

/-- Woodford (2003), (E.2): `u_cξ ξ = O(ξ)`. -/
theorem cross_isBigO (U : ℝ × Ξ → ℝ) (yb : ℝ) {g : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] g) :
    (fun x => cross U yb (ξ x)) =O[l] g :=
  (IsBigO.of_bound ‖D2 U yb‖ (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact abs_cross_le U yb (ξ x))).trans hξ

/-- Woodford (2003), (E.2): `ξ′u_ξξ ξ = O(ξ²)`. -/
theorem quad_isBigO (U : ℝ × Ξ → ℝ) (yb : ℝ) {g : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] g) :
    (fun x => quad U yb (ξ x)) =O[l] fun x => g x ^ 2 := by
  have h : (fun x => quad U yb (ξ x)) =O[l] fun x => ‖ξ x‖ ^ 2 :=
    IsBigO.of_bound ‖D2 U yb‖ (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
      exact abs_quad_le U yb (ξ x))
  exact h.trans (hξ.norm_left.pow 2)

/-- Woodford (2003), eq. (1.2), p. 385, and (E.2)–(E.3) (**the Taylor step along any family**):
for `C³` `U`, if the level deviation `c` and the disturbance `ξ` are `O(s)` with `s → 0`, then
`U(ȳ + c, ξ) = uTaylor(…)(c) + O(s³)`, the polynomial having the coefficients of (E.2). -/
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
`Y = ȳ e^{Ŷ}` and `Ŷ, ξ = O(s)`, `U(Y, ξ) = uTaylor(…)(Y − ȳ) + O(s³)`. -/
theorem level_taylor {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (yb : ℝ) (hs : Tendsto s l (𝓝 0))
    {Y : α → ℝ} {ξ : α → Ξ} (hY : Y =O[l] s) (hξ : ξ =O[l] s) :
    (fun x => U (yb * Real.exp (Y x), ξ x) - Prop61.uTaylor (U (yb, 0)) (slope U yb)
      (curv U yb) (lin U yb (ξ x)) (cross U yb (ξ x)) (quad U yb (ξ x))
      (yb * Real.exp (Y x) - yb)) =O[l] fun x => s x ^ 3 := by
  have hc : (fun x => yb * Real.exp (Y x) - yb) =O[l] s :=
    ((exp_sub_one_isBigO hs hY).const_mul_left yb).congr_left fun x => by ring
  refine (taylor_pair hU yb hs hc hξ).congr_left fun x => ?_
  rw [show yb + (yb * Real.exp (Y x) - yb) = yb * Real.exp (Y x) by ring]

/-- Woodford (2003), (2.11), p. 395 (bookkeeping): `f = O(s)` gives `f = O(s¹)`. -/
theorem isBigO_pow_one {f : α → ℝ} (h : f =O[l] s) : f =O[l] fun x => s x ^ 1 :=
  h.congr_right fun _ => (pow_one _).symm

/-- Woodford (2003), (E.2), p. 692 (**the remainder `Ru` is `O(s³)`**): with `g, Ŷ = O(s)` and
the exponential remainder `r = O(s³)`. -/
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

/-- Woodford (2003), (E.3), p. 693 (**the remainder `Rv` at `Φ = 0` is `O(s³)`**): with
`q, ŷ = O(s)` and the exponential remainder `r = O(s³)`. -/
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

/-! ## The cross-section: CES orders and the cross-sectional covariance -/

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), App. E, p. 693: one good's log output is bounded by the sup norm, so a
cross-section that is `O(s)` is `O(s)` good by good. -/
theorem coord_isBigO {g : α → ℝ} {yh : α → ι → ℝ} (hy : yh =O[l] g) (i : ι) :
    (fun x => yh x i) =O[l] g :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun x => by
    rw [one_mul]; exact norm_le_pi_norm (yh x) i)).trans hy

/-- Woodford (2003), App. E.1, eq. (E.5), p. 694 (**the orders of the CES objects**): if the
cross-section `ŷ` is `O(s)`, then `E_i ŷ = O(s)`, `var_i ŷ = O(s²)`, the (E.5) error
`Ŷ − E_i ŷ − (r/2) var_i ŷ = O(s³)` and `Ŷ = (1/r) log E_i e^{r ŷ} = O(s)`. -/
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

/-- Woodford (2003), (2.12)–(2.13), p. 396: the cross-sectional covariance
`cov_i(a, b) = ∑ w_i (a_i − E_i a)(b_i − E_i b)`. -/
noncomputable def crossCov (w a b : ι → ℝ) : ℝ :=
  ∑ i, w i * ((a i - crossMean w a) * (b i - crossMean w b))

/-- Woodford (2003), App. E: `E_i` is additive. -/
theorem crossMean_add' (w a b : ι → ℝ) :
    crossMean w (a + b) = crossMean w a + crossMean w b := by
  simp [ExpLogCES.crossMean, mul_add, Finset.sum_add_distrib]

/-- Woodford (2003), App. E: `E_i` commutes with differences. -/
theorem crossMean_sub' (w a b : ι → ℝ) :
    crossMean w (a - b) = crossMean w a - crossMean w b := by
  simp [ExpLogCES.crossMean, mul_sub, Finset.sum_sub_distrib]

/-- Woodford (2003), App. E (difference of dispersions):
`var_i y − var_i y′ = cov_i(y − y′, y + y′)`. -/
theorem crossVar_sub_crossVar (w y y' : ι → ℝ) :
    crossVar w y - crossVar w y' = crossCov w (y - y') (y + y') := by
  unfold crossCov ExpLogCES.crossVar
  rw [crossMean_sub', crossMean_add', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- Woodford (2003), App. E: `|cov_i(a, b)| ≤ 4 ‖a‖∞ ‖b‖∞` for probability weights. -/
theorem abs_crossCov_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (a b : ι → ℝ) :
    |crossCov w a b| ≤ 4 * (‖a‖ * ‖b‖) := by
  have ha : ∀ i, |a i - crossMean w a| ≤ 2 * ‖a‖ := fun i => by
    have h1 := ExpLogCES.abs_crossMean_le hw hw1 a
    have h2 : |a i| ≤ ‖a‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i
    have := abs_sub (a i) (crossMean w a)
    linarith
  have hb : ∀ i, |b i - crossMean w b| ≤ 2 * ‖b‖ := fun i => by
    have h1 := ExpLogCES.abs_crossMean_le hw hw1 b
    have h2 : |b i| ≤ ‖b‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i
    have := abs_sub (b i) (crossMean w b)
    linarith
  unfold crossCov
  calc |∑ i, w i * ((a i - crossMean w a) * (b i - crossMean w b))|
      ≤ ∑ i, |w i * ((a i - crossMean w a) * (b i - crossMean w b))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * (4 * (‖a‖ * ‖b‖)) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_mul, abs_of_nonneg (hw i)]
        refine mul_le_mul_of_nonneg_left ?_ (hw i)
        have := mul_le_mul (ha i) (hb i) (abs_nonneg _) (by positivity)
        linarith
    _ = 4 * (‖a‖ * ‖b‖) := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Woodford (2003), App. E (**dispersion along a family is `s²` times the first-order
dispersion, up to `O(s³)`**): if `ŷ − s y₁ = O(s²)` with `y₁` bounded, then
`var_i ŷ − s² var_i y₁ = O(s³)`. -/
theorem crossVar_family {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hs : Tendsto s l (𝓝 0)) {yh y1 : α → ι → ℝ}
    (h : (fun x => yh x - s x • y1 x) =O[l] fun x => s x ^ 2)
    (h1 : y1 =O[l] fun _ => (1 : ℝ)) :
    (fun x => crossVar w (yh x) - s x ^ 2 * crossVar w (y1 x)) =O[l] fun x => s x ^ 3 := by
  have hsy : (fun x => s x • y1 x) =O[l] fun x => s x ^ 1 :=
    ((isBigO_refl s l).smul h1).congr (fun x => rfl) (fun x => by simp)
  have hsum : (fun x => yh x + s x • y1 x) =O[l] fun x => s x ^ 1 :=
    ((h.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))).add
      (hsy.const_smul_left (2 : ℝ))).congr_left fun x => by
        simp only [Pi.smul_apply]
        module
  have hcov : (fun x => crossCov w (yh x - s x • y1 x) (yh x + s x • y1 x)) =O[l]
      fun x => ‖yh x - s x • y1 x‖ * ‖yh x + s x • y1 x‖ :=
    IsBigO.of_bound 4 (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), Real.norm_eq_abs]
      exact abs_crossCov_le hw hw1 _ _)
  have hp := (h.norm_left.mul hsum.norm_left).congr_right fun x => by rw [← pow_add]
  refine (hcov.trans hp).congr_left fun x => ?_
  rw [← crossVar_sub_crossVar]
  have e : crossVar w (s x • y1 x) = s x ^ 2 * crossVar w (y1 x) := by
    have := ExpLogCES.crossVar_mul w (s x) (y1 x)
    rwa [show (fun i => s x * y1 x i) = s x • y1 x by ext i; simp] at this
  rw [e]

/-- Woodford (2003), (E.1), p. 692 (**the remainder `R3` of Theorem A1 at `Φ = 0` is
`O(s³)`**), with the natural-rate and efficient-gap errors zero: if `q, Ŷ = O(s)`,
`var_i ŷ = O(s²)` and the (E.5) error `e = O(s³)` (no condition on `g`, which enters `R3` only
through the vanishing error terms). -/
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
`Ŷⁿ = (σ⁻¹g + ωq)/(σ⁻¹ + ω)` is `O(s)` when `g, q` are. -/
theorem natLin_isBigO (sinv omega : ℝ) {g q : α → ℝ} {k : α → ℝ} (hg : g =O[l] k)
    (hq : q =O[l] k) : (fun x => natLin sinv omega (g x) (q x)) =O[l] k := by
  refine (((hg.const_mul_left sinv).add (hq.const_mul_left omega)).const_mul_left
    (sinv + omega)⁻¹).congr_left fun x => ?_
  unfold natLin
  ring

/-- Woodford (2003), (E.6), p. 694: `Ŷⁿ` is linear in the disturbances. -/
theorem natLin_smul (sinv omega r g q : ℝ) :
    natLin sinv omega (r * g) (r * q) = r * natLin sinv omega g q := by
  unfold natLin
  ring

/-- Woodford (2003), App. E (one-parameter families): if `ŷ − s y₁ = O(s²)` with `y₁` bounded
and `s → 0`, then `ŷ = O(s)`. -/
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
`Ȳ · CES(e^{ŷ}) = Ȳ e^{Ŷ}` with `Ŷ = (1/r) log E_i e^{r ŷ}` (and the index is positive). -/
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
`σ⁻¹ = −ȳ U_yy/U_y`, `g = −U_yξ ξ/(ȳ U_yy)` (via `Prop61.uTaylor_eq`). -/
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
`ȳ V_y`). -/
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

/-- Woodford (2003), App. E: `E_i(r y) = r E_i y`. -/
theorem crossMean_smul' (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) :
    crossMean w (r • y) = r * crossMean w y :=
  ExpLogCES.crossMean_mul w r y

/-- Woodford (2003), App. E: `E_i z = O(‖z‖)` along any family. -/
theorem crossMean_isBigO {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {g : α → ℝ}
    {z : α → ι → ℝ} (hz : z =O[l] g) : (fun x => crossMean w (z x)) =O[l] g :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun x => by
    rw [one_mul, Real.norm_eq_abs]; exact ExpLogCES.abs_crossMean_le hw hw1 (z x))).trans hz

/-- Woodford (2003), (2.10), p. 394 (C² families satisfy the first-order hypothesis): if every
good's log output `ε ↦ ŷ(ε)(i)` is `C²` with `ŷ(0) = 0`, then `ŷ(ε) − ε y₁ = O(ε²)` with the
first-order solution `y₁(i) = ŷ′(0)(i)`. -/
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
efficient `Y*` measures exactly `x − x*`. -/
theorem gap_eq_woodford {Y Ystar Ybar Yn : ℝ} (hY : 0 < Y) (hs : 0 < Ystar) (hb : 0 < Ybar) :
    Real.log (Y / Ystar) - Yn = (Real.log (Y / Ybar) - Yn) - Real.log (Ystar / Ybar) := by
  rw [Real.log_div hY.ne' hs.ne', Real.log_div hY.ne' hb.ne', Real.log_div hs.ne' hb.ne']
  ring

/-- Woodford (2003), (2.9)/(2.17), p. 394 (**the first-order efficient gap along `Φ = εΦ₁`**):
if `F(Φ) = log(Ȳ(Φ)/Y*)` has derivative `−1/(ω + σ⁻¹)` at `0` (`Prop61.steadyState_family`),
then `x*(ε) = log(Y*/Ȳ(εΦ₁)) = −F(εΦ₁)` has derivative `Φ₁/(σ⁻¹ + ω) = xStarLin σ⁻¹ ω Φ₁` at
`ε = 0`. -/
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
all `t` is `O(1)` uniformly in `t`. -/
theorem unif_of_bounded {E : Type*} [Norm E] {f : ℕ → E} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    (fun p : ℕ × ℝ => f p.1) =O[unif] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC⟩ := hf
  exact IsBigO.of_bound C (Eventually.of_forall fun p => by simpa using hC p.1)

/-- Woodford (2003), (2.21), p. 400: for bounded sequences the discounted sum is linear,
`∑ βᵗ (A_t − (B_t + c L_t)) = ∑ βᵗ A_t − (∑ βᵗ B_t + c ∑ βᵗ L_t)`. -/
theorem tsum_bridge_split {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {A B L : ℕ → ℝ} (c : ℝ)
    (hA : Sequences.Bdd A) (hB : Sequences.Bdd B) (hL : Sequences.Bdd L) :
    ∑' t, β ^ t * (A t - (B t + c * L t)) =
      ∑' t, β ^ t * A t - (∑' t, β ^ t * B t + c * ∑' t, β ^ t * L t) := by
  have sA := hA.summable hβ0 hβ1
  have sB := hB.summable hβ0 hβ1
  have sL := hL.summable hβ0 hβ1
  have e : (fun t => β ^ t * (A t - (B t + c * L t))) =
      fun t => β ^ t * A t - (β ^ t * B t + c * (β ^ t * L t)) := by
    funext t; ring
  rw [e, sA.tsum_sub (sB.add (sL.mul_left c)), sB.tsum_add (sL.mul_left c), tsum_mul_left]

/-- Woodford (2003), (2.21)–(2.22), p. 400, and survey error 25 (**the discounted bridge**): if
period welfare satisfies `U_t(ε) = T_t(ε) − (ε²/2) k L_t + O(ε³)` UNIFORMLY in `t`, the
policy-independent terms `T_t(ε)` are bounded uniformly in `t` (for small `ε`) and the
first-order losses `L_t` are bounded, then
`∑ βᵗ U_t(ε) = ∑ βᵗ T_t(ε) − (ε²/2) k ∑ βᵗ L_t + O(ε³)` (all sums genuine `tsum`s of bounded
sequences). -/
theorem discounted_bridge {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {U T : ℕ → ℝ → ℝ}
    {L : ℕ → ℝ} {k : ℝ}
    (h : (fun p : ℕ × ℝ => U p.1 p.2 - (T p.1 p.2 + p.2 ^ 2 / 2 * (-(k * L p.1)))) =O[unif]
      fun p => p.2 ^ 3)
    (hT : (fun p : ℕ × ℝ => T p.1 p.2) =O[unif] fun _ => (1 : ℝ))
    (hL : ∃ C, ∀ t, |L t| ≤ C) :
    (fun ε => ∑' t, β ^ t * U t ε - (∑' t, β ^ t * T t ε +
      ε ^ 2 / 2 * (-(k * ∑' t, β ^ t * L t)))) =O[𝓝 0] fun ε => ε ^ 3 := by
  have H := tsum_isBigO_of_unif
    (f := fun t ε => U t ε - (T t ε + ε ^ 2 / 2 * (-(k * L t)))) hβ0 hβ1 h
  have hLb : Sequences.Bdd L := hL
  refine H.congr' ?_ EventuallyEq.rfl
  filter_upwards [bdd_of_unif (f := fun t ε => U t ε - (T t ε + ε ^ 2 / 2 * (-(k * L t))))
    (g := fun ε => ε ^ 3) h, bdd_of_unif (f := T) (g := fun _ => (1 : ℝ)) hT] with ε hD hTε
  have hU : Sequences.Bdd (fun t => U t ε) := by
    obtain ⟨C, hC⟩ := (hD.add hTε).add ((Sequences.Bdd.const (ε ^ 2 / 2 * (-k))).mul hLb)
    exact ⟨C, fun t => by have := hC t; convert this using 2; ring⟩
  have e := tsum_bridge_split hβ0 hβ1 (ε ^ 2 / 2 * (-k)) hU hTε hLb
  rw [show (fun t => β ^ t * (U t ε - (T t ε + ε ^ 2 / 2 * (-(k * L t))))) =
      fun t => β ^ t * (U t ε - (T t ε + ε ^ 2 / 2 * (-k) * L t)) by funext t; ring, e]
  ring

/-- Woodford (2003), §2.2 (2.21) (**ranking by the discounted first-order loss**): two policies
whose discounted welfare satisfies the bridge with the same policy-independent part; the one
with the smaller discounted first-order loss is strictly better for all small `ε > 0`. -/
theorem discounted_ranking {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {UA UB T : ℕ → ℝ → ℝ}
    {LA LB : ℕ → ℝ} {k : ℝ} (hk : 0 < k)
    (hA : (fun p : ℕ × ℝ => UA p.1 p.2 - (T p.1 p.2 + p.2 ^ 2 / 2 * (-(k * LA p.1)))) =O[unif]
      fun p => p.2 ^ 3)
    (hB : (fun p : ℕ × ℝ => UB p.1 p.2 - (T p.1 p.2 + p.2 ^ 2 / 2 * (-(k * LB p.1)))) =O[unif]
      fun p => p.2 ^ 3)
    (hT : (fun p : ℕ × ℝ => T p.1 p.2) =O[unif] fun _ => (1 : ℝ))
    (hLA : ∃ C, ∀ t, |LA t| ≤ C) (hLB : ∃ C, ∀ t, |LB t| ≤ C)
    (hL : ∑' t, β ^ t * LA t < ∑' t, β ^ t * LB t) :
    ∀ᶠ ε in 𝓝[>] 0, ∑' t, β ^ t * UB t ε < ∑' t, β ^ t * UA t ε :=
  ranking_of_tip hk (discounted_bridge hβ0 hβ1 hA hT hLA) (discounted_bridge hβ0 hβ1 hB hT hLB) hL

/-- Woodford (2003), p. 397 (**two-point dispersion, finite weights**): if a fraction
`ι = ∑_{i ∈ F} w_i` of goods has log price `a` and the rest `b`, then
`var_i = ι(1 − ι)(a − b)²`. -/
theorem crossVar_twoPoint [DecidableEq ι] {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (F : Finset ι)
    (a b : ℝ) :
    crossVar w (fun i => if i ∈ F then a else b) =
      (∑ i ∈ F, w i) * (1 - ∑ i ∈ F, w i) * (a - b) ^ 2 := by
  set ind : ι → ℝ := fun i => if i ∈ F then 1 else 0 with hind
  have hp : (fun i => if i ∈ F then a else b) = fun i => b + (a - b) * ind i := by
    funext i
    by_cases h : i ∈ F <;> simp [hind, h]
  have hm : crossMean w ind = ∑ i ∈ F, w i := by
    unfold ExpLogCES.crossMean
    simp only [hind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : (fun i => ind i ^ 2) = ind := by
    funext i
    by_cases h : i ∈ F <;> simp [hind, h]
  rw [hp, ExpLogCES.crossVar_const_add hw1, ExpLogCES.crossVar_mul, ExpLogCES.crossVar_eq hw1,
    h2, hm]
  ring

/-! ## Proposition 6.1 (Layer B) -/

variable (ι Ξ)

/-- Woodford (2003), (2.3)–(2.6), pp. 392–393: the primitives of the period utility
`U_t = ũ(Y_t; ξ_t) − ∫ ṽ(y_t(i); ξ_t) di` for a finite weighted cross-section of goods: the
utility `ũ` of aggregate output, the disutility `ṽ` of supplying one good, the steady state
`Ȳ` (the expansion point), the elasticity `θ` of the Dixit–Stiglitz aggregate and the weights. -/
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

/-- Woodford (2003), App. E.1, p. 692: `u_c = ũ_Y(Ȳ; 0)`. -/
noncomputable def uc : ℝ := slope M.u M.Yb

/-- Woodford (2003), App. E.1, p. 692: `u_cc = ũ_YY(Ȳ; 0)`. -/
noncomputable def ucc : ℝ := curv M.u M.Yb

/-- Woodford (2003), App. E.1, p. 693: `ṽ_y(Ȳ; 0)`. -/
noncomputable def vy : ℝ := slope M.v M.Yb

/-- Woodford (2003), App. E.1, p. 693: `ṽ_yy(Ȳ; 0)`. -/
noncomputable def vyy : ℝ := curv M.v M.Yb

/-- Woodford (2003), p. 393: `σ⁻¹ = −Ȳ u_cc/u_c`. -/
noncomputable def sig : ℝ := sigmaInvEl M.Yb M.uc M.ucc

/-- Woodford (2003), p. 393: `ω = Ȳ ṽ_yy/ṽ_y`. -/
noncomputable def omg : ℝ := omegaEl M.Yb M.vy M.vyy

/-- Woodford (2003), App. E.1, p. 693: the demand disturbance `g = −u_cξ ξ/(Ȳ u_cc)`. -/
noncomputable def gS (ξ : Ξ) : ℝ := gShock M.Yb M.ucc (cross M.u M.Yb ξ)

/-- Woodford (2003), App. E.1, p. 693: the supply disturbance `q = −ṽ_yξ ξ/(Ȳ ṽ_yy)`. -/
noncomputable def qS (ξ : Ξ) : ℝ := qShock M.Yb M.vyy (cross M.v M.Yb ξ)

/-- Woodford (2003), eq. (2.6), p. 393: log aggregate output `Ŷ = log(Y/Ȳ)` of the cross-section
of log outputs `ŷ`, `Ŷ = (1/r) log E_i e^{r ŷ}` with `r = 1 − θ⁻¹`. -/
noncomputable def Yagg (yh : ι → ℝ) : ℝ := cumulant M.w (1 - M.θ⁻¹) yh

/-- Woodford (2003), eqs. (2.3)–(2.6), pp. 392–393 (**the actual period utility**): with
`y(i) = Ȳ e^{ŷ(i)}` and `Y` the Dixit–Stiglitz aggregate,
`U = ũ(Ȳ · CES(e^{ŷ}); ξ) − E_i ṽ(Ȳ e^{ŷ(i)}; ξ)`. -/
noncomputable def Ustate (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  M.u (M.Yb * cesIndex M.w (1 - M.θ⁻¹) (fun i => Real.exp (yh i)), ξ) -
    ∑ i, M.w i * M.v (M.Yb * Real.exp (yh i), ξ)

/-- Woodford (2003), (2.10)/(E.1), p. 394: the terms independent of policy,
`(ū + u_ξξ + ½ξ′u_ξξξ) − (v̄ + v_ξξ + ½ξ′v_ξξξ) + Ȳu_c · ½(σ⁻¹ + ω)(Ŷⁿ)²` (a function of the
disturbances only). -/
noncomputable def tipState (ξ : Ξ) : ℝ :=
  tip0 M.u M.Yb ξ - tip0 M.v M.Yb ξ + M.Yb * M.uc * tipA M.sig M.omg (M.gS ξ) (M.qS ξ) 0

/-- Woodford (2003), eq. (2.10), p. 394 (**the loss in Woodford's variables**):
`(σ⁻¹ + ω)(Ŷ − Ŷⁿ)² + (θ⁻¹ + ω) var_i ŷ`, with `Ŷ` the CES aggregate. -/
noncomputable def lossW (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  lossQ M.sig M.omg M.θ (M.Yagg yh - natLin M.sig M.omg (M.gS ξ) (M.qS ξ)) (crossVar M.w yh)

/-- Woodford (2003), eq. (2.10), p. 394 (**the loss as a quadratic form**): the same with `Ŷ`
replaced by `E_i ŷ` (equal to second order, (E.5)): a homogeneous quadratic in `(ŷ, ξ)`. -/
noncomputable def lossB (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  lossQ M.sig M.omg M.θ (crossMean M.w yh - natLin M.sig M.omg (M.gS ξ) (M.qS ξ))
    (crossVar M.w yh)

/-- Woodford (2003), §2.1, pp. 392–394 (**the maintained assumptions, made explicit**): `ũ`, `ṽ`
are `C³` (survey error 19), `Ȳ > 0`, probability weights, `θ ≠ 1`, `u_c > 0`, `u_cc ≠ 0`,
`ṽ_yy ≠ 0`. -/
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

/-- Woodford (2003), (2.6): `r = 1 − θ⁻¹ ≠ 0` for `θ ≠ 1`. -/
theorem r_ne (hM : M.Std) : 1 - M.θ⁻¹ ≠ 0 := by
  intro h
  apply hM.θ_ne_one
  have : M.θ⁻¹ = 1 := by linarith
  simpa using congrArg (·⁻¹) this

/-- Woodford (2003), (2.6): the actual utility with the aggregate written as `Ȳ e^{Ŷ}`. -/
theorem Ustate_eq (hM : M.Std) (yh : ι → ℝ) (ξ : Ξ) :
    M.Ustate yh ξ = M.u (M.Yb * Real.exp (M.Yagg yh), ξ) -
      ∑ i, M.w i * M.v (M.Yb * Real.exp (yh i), ξ) := by
  unfold Ustate Yagg
  rw [cesIndex_exp_eq hM.w_nonneg hM.w_sum]

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `g` is linear in the disturbances, `g(rξ) = r g(ξ)`. -/
theorem gS_smul (r : ℝ) (ξ : Ξ) : M.gS (r • ξ) = r * M.gS ξ := by
  unfold gS gShock
  rw [cross_smul]
  ring

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `q` is linear in the disturbances, `q(rξ) = r q(ξ)`. -/
theorem qS_smul (r : ℝ) (ξ : Ξ) : M.qS (r • ξ) = r * M.qS ξ := by
  unfold qS qShock
  rw [cross_smul]
  ring

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `g = O(ξ)`. -/
theorem gS_isBigO {k : α → ℝ} {ξ : α → Ξ} (hξ : ξ =O[l] k) :
    (fun x => M.gS (ξ x)) =O[l] k :=
  ((cross_isBigO M.u M.Yb hξ).const_mul_left (-(M.Yb * M.ucc)⁻¹)).congr_left fun x => by
    unfold gS gShock
    ring

omit [Fintype ι] in
/-- Woodford (2003), App. E.1: `q = O(ξ)`. -/
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
`O(‖ŷ, ξ‖³)`. -/
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
the loss by `O(s³)` (`Ŷ − E_i ŷ = O(s²)` multiplies a first-order term). -/
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
homogeneous quadratic form in `(ŷ, ξ)`). -/
theorem prop61_state_poly (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hs : Tendsto s l (𝓝 0)) {yh : α → ι → ℝ} {ξ : α → Ξ} (hy : yh =O[l] s)
    (hξ : ξ =O[l] s) :
    (fun x => M.Ustate (yh x) (ξ x) -
      (M.tipState (ξ x) - M.Yb * M.uc / 2 * M.lossB (yh x) (ξ x))) =O[l] fun x => s x ^ 3 :=
  ((prop61_state hM heff hden hs hy hξ).sub
    ((lossW_sub_lossB hM hs hy hξ).const_mul_left (M.Yb * M.uc / 2))).congr_left fun x => by
      ring

/-- Woodford (2003), (2.10)–(2.11), pp. 394–395 (**the loss at the first-order solution**): if
`ŷ − s y₁ = O(s²)`, `y₁` and `ξ₁` bounded, then the loss at `(ŷ, s ξ₁)` is `s²` times the loss at
the first-order solution `(y₁, ξ₁)`, up to `O(s³)`. -/
theorem lossB_family (hM : M.Std) (hs : Tendsto s l (𝓝 0)) {yh y1 : α → ι → ℝ}
    {ξ1 : α → Ξ} (h : (fun x => yh x - s x • y1 x) =O[l] fun x => s x ^ 2)
    (h1 : y1 =O[l] fun _ => (1 : ℝ)) (hξ1 : ξ1 =O[l] fun _ => (1 : ℝ)) :
    (fun x => M.lossB (yh x) (s x • ξ1 x) - s x ^ 2 * M.lossB (y1 x) (ξ1 x)) =O[l]
      fun x => s x ^ 3 := by
  have ha : (fun x => (crossMean M.w (yh x) -
      natLin M.sig M.omg (M.gS (s x • ξ1 x)) (M.qS (s x • ξ1 x))) -
      s x * (crossMean M.w (y1 x) - natLin M.sig M.omg (M.gS (ξ1 x)) (M.qS (ξ1 x)))) =O[l]
      fun x => s x ^ 2 :=
    (crossMean_isBigO hM.w_nonneg hM.w_sum h).congr_left fun x => by
      rw [crossMean_sub', crossMean_smul', M.gS_smul, M.qS_smul, natLin_smul]
      ring
  have ha1 : (fun x => crossMean M.w (y1 x) - natLin M.sig M.omg (M.gS (ξ1 x)) (M.qS (ξ1 x)))
      =O[l] fun _ => (1 : ℝ) :=
    (crossMean_isBigO hM.w_nonneg hM.w_sum h1).sub
      (natLin_isBigO M.sig M.omg (M.gS_isBigO hξ1) (M.qS_isBigO hξ1))
  have hsq := sq_sub_sq_isBigO hs ha ha1
  have hV := crossVar_family hM.w_nonneg hM.w_sum hs h h1
  refine ((hsq.const_mul_left (M.sig + M.omg)).add
    (hV.const_mul_left (M.θ⁻¹ + M.omg))).congr_left fun x => ?_
  unfold lossB lossQ
  ring

/-- Woodford (2003), **Proposition 6.1, eq. (2.10), p. 394 (Layer B along a family, any
filter)**. If the cross-section satisfies `ŷ − s y₁ = O(s²)` (first-order solution `y₁`), the
disturbances are `ξ = s ξ₁`, and `y₁`, `ξ₁` are bounded, then
`U = tipState(s ξ₁) − (s²/2) Ȳu_c L(y₁, ξ₁) + O(s³)` with
`L = (σ⁻¹ + ω)(E_i y₁ − Ŷⁿ₁)² + (θ⁻¹ + ω) var_i y₁` the loss of the first-order solution. -/
theorem prop61_family (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    (hs : Tendsto s l (𝓝 0)) {yh y1 : α → ι → ℝ} {ξ1 : α → Ξ}
    (h : (fun x => yh x - s x • y1 x) =O[l] fun x => s x ^ 2)
    (h1 : y1 =O[l] fun _ => (1 : ℝ)) (hξ1 : ξ1 =O[l] fun _ => (1 : ℝ)) :
    (fun x => M.Ustate (yh x) (s x • ξ1 x) - (M.tipState (s x • ξ1 x) +
      s x ^ 2 / 2 * (-(M.Yb * M.uc * M.lossB (y1 x) (ξ1 x))))) =O[l] fun x => s x ^ 3 := by
  have hy := family_isBigO hs h h1
  have hξ : (fun x => s x • ξ1 x) =O[l] s :=
    ((isBigO_refl s l).smul hξ1).congr_right fun x => mul_one _
  refine ((prop61_state_poly hM heff hden hs hy hξ).sub
    ((lossB_family hM hs h h1 hξ1).const_mul_left (M.Yb * M.uc / 2))).congr_left fun x => ?_
  ring

/-- Woodford (2003), **Proposition 6.1, eq. (2.10), p. 394 (Layer B, one-parameter form)**. Let
the disturbances be `ε ξ₁` and the cross-section of log outputs a family with
`ŷ(ε) − ε y₁ = O(ε²)` (e.g. `C²`, `family_of_contDiff`). At the efficient steady state
(`ṽ_y = u_c`) actual period utility satisfies
`U(ε) = tipState(ε ξ₁) − (ε²/2) Ȳ u_c L₁ + O(ε³)`, where
`L₁ = (σ⁻¹ + ω)(x₁)² + (θ⁻¹ + ω) var_i y₁` and `x₁ = E_i y₁ − Ŷⁿ₁` is the first-order gap
(`= x₁ − x₁*` in Woodford's notation, `gap_eq_woodford`, `xstar_hasDerivAt`). -/
theorem prop61_bridge (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    {yh : ℝ → ι → ℝ} {y1 : ι → ℝ} (ξ1 : Ξ)
    (h : (fun ε => yh ε - ε • y1) =O[𝓝 0] fun ε => ε ^ 2) :
    (fun ε => M.Ustate (yh ε) (ε • ξ1) - (M.tipState (ε • ξ1) +
      ε ^ 2 / 2 * (-(M.Yb * M.uc * M.lossB y1 ξ1)))) =O[𝓝 0] fun ε => ε ^ 3 :=
  prop61_family (s := fun ε => ε) (y1 := fun _ => y1) (ξ1 := fun _ => ξ1) hM heff hden
    tendsto_id h (isBigO_const_const _ one_ne_zero _) (isBigO_const_const _ one_ne_zero _)

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

/-- Woodford (2003), §2.1, p. 394: at `ε = 0` (no disturbances, the steady-state allocation)
actual utility is `ũ(Ȳ; 0) − ṽ(Ȳ; 0) = tipState 0`. -/
theorem Ustate_zero (hM : M.Std) : M.Ustate 0 0 = M.tipState 0 := by
  have h0 : (0 : Ξ) = (0 : ℝ) • (0 : Ξ) := (zero_smul ℝ _).symm
  have hc : cumulant M.w (1 - M.θ⁻¹) (0 : ι → ℝ) = 0 := by
    unfold ExpLogCES.cumulant ExpLogCES.cesMoment
    simp [hM.w_sum]
  rw [Ustate_eq hM]
  simp only [Yagg, hc, Pi.zero_apply, Real.exp_zero, mul_one]
  rw [← Finset.sum_mul, hM.w_sum, one_mul]
  unfold tipState tip0
  rw [h0, lin_smul, lin_smul, quad_smul, quad_smul, M.gS_smul, M.qS_smul]
  unfold tipA natLin xStarLin
  ring

/-- Woodford (2003), **Proposition 6.1 in the form `W(ε) = W(0) + εW′(0) + (ε²/2)W″(0) + O(ε³)`**
(survey §4, B1.1): `W(0) = ũ(Ȳ;0) − ṽ(Ȳ;0)`, the first-order term `ε(u_ξ − v_ξ)ξ₁` is
independent of policy (because `ṽ_y = u_c`, (1.5)), and
`W″(0) = 2T₂(ξ₁) − Ȳu_c L₁` with `T₂` depending on `ξ₁` only. -/
theorem prop61_expansion (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    {yh : ℝ → ι → ℝ} {y1 : ι → ℝ} (ξ1 : Ξ)
    (h : (fun ε => yh ε - ε • y1) =O[𝓝 0] fun ε => ε ^ 2) :
    (fun ε => M.Ustate (yh ε) (ε • ξ1) - (M.Ustate 0 0 +
      ε * (lin M.u M.Yb ξ1 - lin M.v M.Yb ξ1) +
      ε ^ 2 / 2 * (2 * (quad M.u M.Yb ξ1 / 2 - quad M.v M.Yb ξ1 / 2 +
        M.Yb * M.uc * tipA M.sig M.omg (M.gS ξ1) (M.qS ξ1) 0) -
        M.Yb * M.uc * M.lossB y1 ξ1))) =O[𝓝 0] fun ε => ε ^ 3 := by
  refine (prop61_bridge hM heff hden ξ1 h).congr_left fun ε => ?_
  rw [tipState_smul, Ustate_zero hM]
  ring

/-- Woodford (2003), §2.1, pp. 394–396 (**welfare ranking from Proposition 6.1**): two policies
with the same disturbances `ε ξ₁` and first-order solutions `y₁ᴬ`, `y₁ᴮ`; if
`L(y₁ᴬ, ξ₁) < L(y₁ᴮ, ξ₁)` then `A` gives strictly higher utility for all small `ε > 0`. -/
theorem prop61_ranking (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    {yA yB : ℝ → ι → ℝ} {yA1 yB1 : ι → ℝ} (ξ1 : Ξ)
    (hA : (fun ε => yA ε - ε • yA1) =O[𝓝 0] fun ε => ε ^ 2)
    (hB : (fun ε => yB ε - ε • yB1) =O[𝓝 0] fun ε => ε ^ 2)
    (hL : M.lossB yA1 ξ1 < M.lossB yB1 ξ1) :
    ∀ᶠ ε in 𝓝[>] 0, M.Ustate (yB ε) (ε • ξ1) < M.Ustate (yA ε) (ε • ξ1) :=
  ranking_of_tip (mul_pos hM.Yb_pos hM.uc_pos) (prop61_bridge hM heff hden ξ1 hA)
    (prop61_bridge hM heff hden ξ1 hB) hL

/-- Woodford (2003), (2.10), p. 394, uniformly in the date (survey error 25): the family form of
Proposition 6.1 with `t`-dependent first-order solutions `y₁_t` and disturbances `ε ξ₁_t`, the
cubic remainder bounded uniformly in `t`. -/
theorem prop61_unif (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) :
    (fun p : ℕ × ℝ => M.Ustate (yh p.1 p.2) (p.2 • ξ1 p.1) - (M.tipState (p.2 • ξ1 p.1) +
      p.2 ^ 2 / 2 * (-(M.Yb * M.uc * M.lossB (y1 p.1) (ξ1 p.1))))) =O[unif]
      fun p => p.2 ^ 3 := by
  have h1 : (fun p : ℕ × ℝ => y1 p.1) =O[unif] fun _ => (1 : ℝ) := unif_of_bounded hy1
  have h2 : (fun p : ℕ × ℝ => ξ1 p.1) =O[unif] fun _ => (1 : ℝ) := unif_of_bounded hξ1
  exact prop61_family (l := unif) (s := fun p : ℕ × ℝ => p.2)
    (yh := fun p : ℕ × ℝ => yh p.1 p.2) (y1 := fun p : ℕ × ℝ => y1 p.1)
    (ξ1 := fun p : ℕ × ℝ => ξ1 p.1) hM heff hden tendsto_unif h h1 h2

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

/-- Woodford (2003), (2.10): the first-order loss of bounded first-order solutions is bounded
uniformly in `t`. -/
theorem lossB_bounded (hM : M.Std) {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ} (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C)
    (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) : ∃ C, ∀ t, |M.lossB (y1 t) (ξ1 t)| ≤ C := by
  have hy := unif_of_bounded hy1
  have hx := unif_of_bounded hξ1
  have hX : (fun p : ℕ × ℝ => crossMean M.w (y1 p.1) -
      natLin M.sig M.omg (M.gS (ξ1 p.1)) (M.qS (ξ1 p.1))) =O[unif] fun _ => (1 : ℝ) :=
    (crossMean_isBigO hM.w_nonneg hM.w_sum hy).sub
      (natLin_isBigO M.sig M.omg (M.gS_isBigO hx) (M.qS_isBigO hx))
  have hV : (fun p : ℕ × ℝ => crossVar M.w (y1 p.1)) =O[unif] fun _ => (1 : ℝ) := by
    obtain ⟨C, hC⟩ := hy1
    refine IsBigO.of_bound (C ^ 2) (Eventually.of_forall fun p => ?_)
    have h := ExpLogCES.crossVar_le hM.w_nonneg hM.w_sum (y1 p.1)
    rw [Real.norm_eq_abs, abs_of_nonneg h.1, norm_one, mul_one]
    exact h.2.trans (pow_le_pow_left₀ (norm_nonneg _) (hC p.1) 2)
  have hL : (fun p : ℕ × ℝ => M.lossB (y1 p.1) (ξ1 p.1)) =O[unif] fun _ => (1 : ℝ) :=
    ((((hX.mul hX).congr_right fun _ => mul_one (1 : ℝ)).const_mul_left (M.sig + M.omg)).add
      (hV.const_mul_left (M.θ⁻¹ + M.omg))).congr_left fun p => by unfold lossB lossQ; ring
  obtain ⟨C, hC⟩ := (isBigO_unif_iff (f := fun t _ => M.lossB (y1 t) (ξ1 t))
    (g := fun _ => (1 : ℝ))).1 hL
  obtain ⟨ε, hε⟩ := hC.exists
  exact ⟨C, fun t => by simpa using hε t⟩

/-- Woodford (2003), **Proposition 6.1 for discounted welfare (Layer B)**, survey error 25 made
explicit: if `ŷ_t(ε) − ε y₁_t = O(ε²)` UNIFORMLY in `t` (`isBigO_unif_iff`: one constant `C`
for all dates and all small `ε`) and `y₁_t`, `ξ₁_t` are bounded sequences, then
`∑ βᵗ U_t(ε) = ∑ βᵗ tipState(ε ξ₁_t) − (ε²/2) Ȳu_c ∑ βᵗ L(y₁_t, ξ₁_t) + O(ε³)`. -/
theorem prop61_discounted (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ} {ξ1 : ℕ → Ξ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) :
    (fun ε => ∑' t, β ^ t * M.Ustate (yh t ε) (ε • ξ1 t) -
      (∑' t, β ^ t * M.tipState (ε • ξ1 t) +
        ε ^ 2 / 2 * (-(M.Yb * M.uc * ∑' t, β ^ t * M.lossB (y1 t) (ξ1 t))))) =O[𝓝 0]
      fun ε => ε ^ 3 :=
  discounted_bridge (U := fun t ε => M.Ustate (yh t ε) (ε • ξ1 t))
    (T := fun t ε => M.tipState (ε • ξ1 t)) (L := fun t => M.lossB (y1 t) (ξ1 t)) hβ0 hβ1
    (prop61_unif hM heff hden h hy1 hξ1) (tipState_unif hξ1) (lossB_bounded hM hy1 hξ1)

/-- Woodford (2003), §2.1 (**ranking of policies by the discounted first-order loss**): with
the same disturbances `ε ξ₁_t`, if `∑ βᵗ L(y₁ᴬ_t, ξ₁_t) < ∑ βᵗ L(y₁ᴮ_t, ξ₁_t)` then `A` gives
strictly higher discounted utility for all small `ε > 0`. -/
theorem prop61_discounted_ranking (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {yA yB : ℕ → ℝ → ι → ℝ} {yA1 yB1 : ℕ → ι → ℝ}
    {ξ1 : ℕ → Ξ}
    (hA : (fun p : ℕ × ℝ => yA p.1 p.2 - p.2 • yA1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hB : (fun p : ℕ × ℝ => yB p.1 p.2 - p.2 • yB1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hyA : ∃ C, ∀ t, ‖yA1 t‖ ≤ C) (hyB : ∃ C, ∀ t, ‖yB1 t‖ ≤ C) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (hL : ∑' t, β ^ t * M.lossB (yA1 t) (ξ1 t) < ∑' t, β ^ t * M.lossB (yB1 t) (ξ1 t)) :
    ∀ᶠ ε in 𝓝[>] 0, ∑' t, β ^ t * M.Ustate (yB t ε) (ε • ξ1 t) <
      ∑' t, β ^ t * M.Ustate (yA t ε) (ε • ξ1 t) :=
  ranking_of_tip (mul_pos hM.Yb_pos hM.uc_pos) (prop61_discounted hM heff hden hβ0 hβ1 hA hyA hξ1)
    (prop61_discounted hM heff hden hβ0 hβ1 hB hyB hξ1) hL

/-! ### Proposition 6.2: the New Classical model -/

/-- Woodford (2003), (2.12) and p. 397: the first-order cross-section of log output in the
two-price New Classical model, `y₁(i) = Y₁ − θ(p₁(i) − P₁)` with `p₁ = a` on the flexible-price
goods `F` and `b` on the others. -/
noncomputable def y1NC [DecidableEq ι] (F : Finset ι) (Y1 P1 a b : ℝ) : ι → ℝ :=
  fun i => Y1 - M.θ * ((if i ∈ F then a else b) - P1)

/-- Woodford (2003), eq. (2.16), p. 398: the New Classical loss
`(π − E_{t−1}π)² + (κ/θ)(x − x*)²` (first-order surprise `S₁`, gap `x₁`). -/
noncomputable def lossNC (ιF S1 x1 : ℝ) : ℝ :=
  S1 ^ 2 + PriceDispersion.kappaNC ιF M.sig M.omg M.θ / M.θ * x1 ^ 2

/-- Woodford (2003), **Proposition 6.2, (2.16)–(2.17), p. 398, at the first-order solution
(Layer A, exact)**: for the two-price cross-section with `ι = ∑_{i∈F} w_i`, the quadratic loss of
Proposition 6.1 equals `2Θ [S₁² + (κ/θ) x₁²]` with `S₁ = ι(a − b)` the first-order unexpected
inflation and `x₁ = E_i y₁ − Ŷⁿ₁` (via `Moments.crossVar_demand`, `crossVar_twoPoint`,
`Prop61.lossQ_disp`, `PriceDispersion.prop62`). -/
theorem lossB_NC [DecidableEq ι] (hM : M.Std) (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0)
    {F : Finset ι} {ιF : ℝ} (hF : ∑ i ∈ F, M.w i = ιF) (hι0 : ιF ≠ 0) (hι1 : 1 - ιF ≠ 0)
    (Y1 P1 a b : ℝ) (ξ1 : Ξ) :
    M.lossB (M.y1NC F Y1 P1 a b) ξ1 = 2 * PriceDispersion.ThetaNC M.θ M.omg ιF *
      M.lossNC ιF (ιF * (a - b))
        (crossMean M.w (M.y1NC F Y1 P1 a b) - natLin M.sig M.omg (M.gS ξ1) (M.qS ξ1)) := by
  have hV : crossVar M.w (M.y1NC F Y1 P1 a b) = M.θ ^ 2 * (ιF * (1 - ιF) * (a - b) ^ 2) := by
    unfold y1NC
    rw [Moments.crossVar_demand hM.w_sum, crossVar_twoPoint hM.w_sum, hF]
  have h62 := PriceDispersion.prop62 (sinv := M.sig) (dp := a - b) (e := 0)
    (S := ιF * (a - b))
    (X := crossMean M.w (M.y1NC F Y1 P1 a b) - natLin M.sig M.omg (M.gS ξ1) (M.qS ξ1))
    hθ hd hι0 hι1 (by ring)
  have hrem : CrossSection.twoPointRem ιF (a - b) 0 = 0 := by
    unfold CrossSection.twoPointRem; ring
  rw [hrem, mul_zero, sub_zero] at h62
  unfold lossB lossNC
  rw [hV, Prop61.lossQ_disp hθ]
  linarith

/-- Woodford (2003), **Proposition 6.2, eqs. (2.16)–(2.17), p. 398 (Layer B)**: in the New
Classical model with disturbances `ε ξ₁`, if the cross-section satisfies
`ŷ(ε) − ε y₁ = O(ε²)` with the two-price first-order solution `y₁ = y1NC F Y₁ P₁ a b`, then
`U(ε) = tipState(ε ξ₁) − (ε²/2) Ȳu_c · 2Θ [S₁² + (κ/θ) x₁²] + O(ε³)`, `S₁ = ι(a − b)`. -/
theorem prop62_bridge [DecidableEq ι] (hM : M.Std) (heff : M.vy = M.uc)
    (hden : M.sig + M.omg ≠ 0) (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0) {F : Finset ι}
    {ιF : ℝ} (hF : ∑ i ∈ F, M.w i = ιF) (hι0 : ιF ≠ 0) (hι1 : 1 - ιF ≠ 0) {Y1 P1 a b : ℝ}
    (ξ1 : Ξ) {yh : ℝ → ι → ℝ}
    (h : (fun ε => yh ε - ε • M.y1NC F Y1 P1 a b) =O[𝓝 0] fun ε => ε ^ 2) :
    (fun ε => M.Ustate (yh ε) (ε • ξ1) - (M.tipState (ε • ξ1) + ε ^ 2 / 2 *
      (-(M.Yb * M.uc * (2 * PriceDispersion.ThetaNC M.θ M.omg ιF) *
        M.lossNC ιF (ιF * (a - b)) (crossMean M.w (M.y1NC F Y1 P1 a b) -
          natLin M.sig M.omg (M.gS ξ1) (M.qS ξ1)))))) =O[𝓝 0] fun ε => ε ^ 3 := by
  refine (prop61_bridge hM heff hden ξ1 h).congr_left fun ε => ?_
  rw [lossB_NC hM hθ hd hF hι0 hι1]
  ring

/-- Woodford (2003), §2.2, p. 398 (**welfare ranking in the New Classical model**): with
`θ > 0`, `1 + ωθ > 0`, `0 < ι < 1`, the policy with the smaller first-order loss
`S₁² + (κ/θ) x₁²` gives strictly higher utility for all small `ε > 0`. -/
theorem prop62_ranking [DecidableEq ι] (hM : M.Std) (heff : M.vy = M.uc)
    (hden : M.sig + M.omg ≠ 0) (hθ : 0 < M.θ) (hd : 0 < 1 + M.omg * M.θ) {F : Finset ι}
    {ιF : ℝ} (hF : ∑ i ∈ F, M.w i = ιF) (hι0 : 0 < ιF) (hι1 : ιF < 1)
    {YA PA aA bA YB PB aB bB : ℝ} (ξ1 : Ξ) {yA yB : ℝ → ι → ℝ}
    (hA : (fun ε => yA ε - ε • M.y1NC F YA PA aA bA) =O[𝓝 0] fun ε => ε ^ 2)
    (hB : (fun ε => yB ε - ε • M.y1NC F YB PB aB bB) =O[𝓝 0] fun ε => ε ^ 2)
    (hL : M.lossNC ιF (ιF * (aA - bA)) (crossMean M.w (M.y1NC F YA PA aA bA) -
        natLin M.sig M.omg (M.gS ξ1) (M.qS ξ1)) <
      M.lossNC ιF (ιF * (aB - bB)) (crossMean M.w (M.y1NC F YB PB aB bB) -
        natLin M.sig M.omg (M.gS ξ1) (M.qS ξ1))) :
    ∀ᶠ ε in 𝓝[>] 0, M.Ustate (yB ε) (ε • ξ1) < M.Ustate (yA ε) (ε • ξ1) := by
  have hι1' : 1 - ιF ≠ 0 := by linarith
  have hk : 0 < M.Yb * M.uc * (2 * PriceDispersion.ThetaNC M.θ M.omg ιF) :=
    mul_pos (mul_pos hM.Yb_pos hM.uc_pos)
      (mul_pos two_pos (PriceDispersion.ThetaNC_pos hθ hd hι0 hι1))
  exact ranking_of_tip hk
    (prop62_bridge hM heff hden hθ.ne' hd.ne' hF hι0.ne' hι1' ξ1 hA)
    (prop62_bridge hM heff hden hθ.ne' hd.ne' hF hι0.ne' hι1' ξ1 hB) hL

end Econ

/-- Woodford (2003), App. E.3 (survey error 25): a `t`-sequence that is `O(1)` uniformly is
bounded by one constant. -/
theorem bounded_of_unif {f : ℕ → ℝ} (h : (fun p : ℕ × ℝ => f p.1) =O[unif] fun _ => (1 : ℝ)) :
    ∃ C, ∀ t, |f t| ≤ C := by
  obtain ⟨C, hC⟩ := (isBigO_unif_iff (f := fun t _ => f t) (g := fun _ => (1 : ℝ))).1 h
  obtain ⟨ε, hε⟩ := hC.exists
  exact ⟨C, fun t => by simpa using hε t⟩

/-- Woodford (2003), (2.20), p. 399 (**Proposition 6.3 at first order, Layer B**): if dispersion
is `Δ_t(ε) = ε² Δ₁_t + O(ε³)`, the inflation term `π_t(ε) = ε π₁_t + O(ε²)` and the recursion
`Δ_{t} = α Δ_{t−1} + (α/(1−α)) π_t² + R_t` holds exactly with `R_t = O(ε³)` (from
`PriceDispersion.prop63_layerA` and `prop63_uniform`), then the first-order objects satisfy the
recursion EXACTLY: `Δ₁_t = α Δ₁_{t−1} + (α/(1−α)) π₁_t²` (index `t + 1` is date `t`). -/
theorem prop63_first_order {α : ℝ} {D qd R : ℝ → ℕ → ℝ} {D1 π1 : ℕ → ℝ}
    (hrec : ∀ ε t, D ε (t + 1) = α * D ε t + α / (1 - α) * qd ε t ^ 2 + R ε t)
    (hD : ∀ t, (fun ε => D ε t - ε ^ 2 * D1 t) =O[𝓝 0] fun ε => ε ^ 3)
    (hq : ∀ t, (fun ε => qd ε t - ε * π1 t) =O[𝓝 0] fun ε => ε ^ 2)
    (hR : ∀ t, (fun ε => R ε t) =O[𝓝 0] fun ε => ε ^ 3) (t : ℕ) :
    D1 (t + 1) = α * D1 t + α / (1 - α) * π1 t ^ 2 := by
  have hq2 := sq_sub_sq_isBigO (s := fun ε : ℝ => ε) (f1 := fun _ => π1 t) tendsto_id (hq t)
    (isBigO_const_const _ one_ne_zero _)
  have h := ((((hD (t + 1)).neg_left.add ((hD t).const_mul_left α)).add
    (hq2.const_mul_left (α / (1 - α)))).add (hR t))
  refine sub_eq_zero.1 (coeff_two_unique (h.congr_left fun ε => ?_))
  rw [hrec ε t]
  ring

/-- Woodford (2003), App. E.2 (dating conventions): a bound uniform in `t` survives the shift
`t ↦ t + 1`. -/
theorem unif_shift {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : (fun p : ℕ × ℝ => f p.1 p.2) =O[unif] fun p => g p.2) :
    (fun p : ℕ × ℝ => f (p.1 + 1) p.2) =O[unif] fun p => g p.2 := by
  obtain ⟨C, hC⟩ := isBigO_unif_iff.1 h
  exact isBigO_unif_iff (f := fun t ε => f (t + 1) ε).2 ⟨C, hC.mono fun ε hε t => hε (t + 1)⟩

namespace Econ

variable (M : Econ Ξ ι)

/-- Woodford (2003), (2.10), p. 394: the output gap `x = E_i ŷ − Ŷⁿ` entering the loss
(`lossB yh ξ = (σ⁻¹ + ω) gap² + (θ⁻¹ + ω) var_i ŷ`). -/
noncomputable def gap (yh : ι → ℝ) (ξ : Ξ) : ℝ :=
  crossMean M.w yh - natLin M.sig M.omg (M.gS ξ) (M.qS ξ)

variable {M}

/-- Woodford (2003), (2.10): the gap along `(ŷ, r ξ₁)` minus `r` times the first-order gap is the
mean of `ŷ − r y₁`. -/
theorem gap_smul_sub (yh y1 : ι → ℝ) (r : ℝ) (ξ1 : Ξ) :
    M.gap yh (r • ξ1) - r * M.gap y1 ξ1 = crossMean M.w (yh - r • y1) := by
  unfold gap
  rw [crossMean_sub', crossMean_smul', M.gS_smul, M.qS_smul, natLin_smul]
  ring

/-- Woodford (2003), **Propositions 6.4–6.5, (2.21)–(2.25), pp. 400–402 (Layer B, generic Calvo
form)**. Period utility is the actual `Ustate` of the cross-section `ŷ_t(ε)` with disturbances
`ε ξ₁_t`, and
* `ŷ_t(ε) − ε y₁_t = O(ε²)` UNIFORMLY in `t`, `y₁_t`, `ξ₁_t` bounded (survey error 25);
* (2.12): `var_i ŷ_t(ε) = θ² Δ_t(ε)` (`Moments.crossVar_demand`; `D ε (t+1) = Δ_t`,
  `D ε 0 = Δ_{−1}`);
* the exact dispersion recursion `Δ_t = α Δ_{t−1} + (α/(1−α)) q_t² + R_t` (Layer A:
  `PriceDispersion.prop63_layerA` with `q_t = π_t`, `index_layerA` with `q_t = π_t − γπ_{t−1}`),
  with `q_t(ε) − ε q₁_t = O(ε²)` and `R_t(ε) = O(ε³)` uniformly in `t`
  (`PriceDispersion.prop63_uniform`), `q₁_t` bounded.
Then, at the efficient steady state,
`∑ βᵗ U_t(ε) = TIP(ε) − (ε²/2) Ȳu_c · 2Θ ∑ βᵗ (q₁_t² + (κ/θ) x₁_t²) + O(ε³)`,
`TIP(ε) = ∑ βᵗ tipState(ε ξ₁_t) − Ȳu_c ½θ(1 + ωθ) α Δ_{−1}(ε)/(1 − αβ)` (exogenous terms and
the initial dispersion), `Θ = ThetaCalvo`, `κ` of (2.19), `x₁_t = gap(y₁_t, ξ₁_t)`. The
Layer-A identity used is `PriceDispersion.calvo_welfare_sum`. -/
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
  have hq1b : Sequences.Bdd q1 := ⟨Cq, hCq⟩
  have hBb : Sequences.Bdd (fun t => q1 t ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
      M.gap (y1 t) (ξ1 t) ^ 2) :=
    (hq1b.pow 2).add ((Sequences.Bdd.const _).mul ((show Sequences.Bdd
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
  have hAb : Sequences.Bdd (fun t => qd ε t ^ 2 +
      Moments.calvoKappa α β M.omg M.θ M.sig / M.θ * M.gap (yh t ε) (ε • ξ1 t) ^ 2) :=
    (bq.pow 2).add ((Sequences.Bdd.const _).mul (bX.pow 2))
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
of (2.19). -/
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
`PriceDispersion.index_layerA`): with `π_t(ε) − ε π₁_t = O(ε²)` uniformly in `t` (all dates
including `π_{−1}`),
`∑ βᵗ U_t(ε) = TIP(ε) − (ε²/2) Ȳu_c · 2Θ ∑ βᵗ ((π₁_t − γπ₁_{t−1})² + λ x₁_t²) + O(ε³)`. -/
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
(`θ > 0`, `1 + ωθ > 0`, `β < 1`). -/
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
`prop64_ranking`, with the quasi-differenced inflation `π₁_t − γπ₁_{t−1}` in the loss. -/
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

/-! ## Proposition 6.6 (habit persistence, corrected): Layer B -/

/-- Woodford (2003), (E.10), p. 696 (**the remainder of the habit expansion is `O(s³)`**):
`E10remAt` with `Ŷ_t, Ŷ_{t−1}, Ĝ_t, Ĝ_{t−1}, gᵖ = O(s)`. -/
theorem E10rem_isBigO (hs : Tendsto s l (𝓝 0)) (sinv η : ℝ) {y ym G Gm gp : α → ℝ}
    (hy : y =O[l] s) (hym : ym =O[l] s) (hG : G =O[l] s) (hGm : Gm =O[l] s)
    (hgp : gp =O[l] s) :
    (fun x => HabitWelfare.E10remAt sinv η (y x) (ym x) (G x) (Gm x) (gp x)) =O[l]
      fun x => s x ^ 3 := by
  have hy1 := isBigO_pow_one hy
  have hym1 := isBigO_pow_one hym
  have hQ : (fun x => (y x ^ 2 - η * ym x ^ 2) / 2) =O[l] fun x => s x ^ 2 :=
    (((isBigO_pow_mul hy1 hy1 (by norm_num : 1 + 1 = 2)).sub
      ((isBigO_pow_mul hym1 hym1 (by norm_num : 1 + 1 = 2)).const_mul_left η)).const_mul_left
        (1 / 2)).congr_left fun x => by ring
  have hc : (fun x => (y x - η * ym x) - (G x - η * Gm x)) =O[l] fun x => s x ^ 1 :=
    isBigO_pow_one ((hy.sub (hym.const_mul_left η)).sub (hG.sub (hGm.const_mul_left η)))
  have t1 := isBigO_pow_mul hQ hc (by norm_num : 2 + 1 = 3)
  have t2 := (isBigO_pow_mul hQ hQ (by norm_num : 2 + 2 = 4)).trans
    (pow_isBigO_pow hs (by norm_num : 3 ≤ 4))
  have t3 := isBigO_pow_mul (isBigO_pow_one hgp) hQ (by norm_num : 1 + 2 = 3)
  refine (((t1.const_mul_left (-sinv)).sub (t2.const_mul_left (sinv / 2))).add
    (t3.const_mul_left sinv)).congr_left fun x => ?_
  unfold HabitWelfare.E10remAt
  ring

/-- Woodford (2003), (E.4), p. 694 (**the remainder of the integrated disutility at `Φ = 0` is
`O(s³)`**): `vRemAt` with `Ŷ, q = O(s)` and `var_i ŷ = O(s²)`. -/
theorem vRem_isBigO (hs : Tendsto s l (𝓝 0)) (θ ω : ℝ) {y q V : α → ℝ} (hy : y =O[l] s)
    (hq : q =O[l] s) (hV : V =O[l] fun x => s x ^ 2) :
    (fun x => HabitWelfare.vRemAt 0 θ ω (y x) (q x) (V x)) =O[l] fun x => s x ^ 3 := by
  have t1 := isBigO_pow_mul (isBigO_pow_one hy) hV (by norm_num : 1 + 2 = 3)
  have t2 := (isBigO_pow_mul hV hV (by norm_num : 2 + 2 = 4)).trans
    (pow_isBigO_pow hs (by norm_num : 3 ≤ 4))
  have t3 := isBigO_pow_mul (isBigO_pow_one hq) hV (by norm_num : 1 + 2 = 3)
  refine (((t1.const_mul_left (-((1 + ω) * ((1 - θ⁻¹) / 2)))).add
    (t2.const_mul_left ((1 + ω) / 2 * ((1 - θ⁻¹) / 2) ^ 2))).add
    (t3.const_mul_left (ω * ((1 - θ⁻¹) / 2)))).congr_left fun x => ?_
  unfold HabitWelfare.vRemAt
  ring

/-- Woodford (2003), (E.10), p. 696: the habit-adjusted expenditure deviation `cDevAt` is
`O(s)` when `Ŷ_t, Ŷ_{t−1}, Ĝ_t, Ĝ_{t−1}` are. -/
theorem cDev_isBigO (hs : Tendsto s l (𝓝 0)) (η : ℝ) {y ym G Gm : α → ℝ} (hy : y =O[l] s)
    (hym : ym =O[l] s) (hG : G =O[l] s) (hGm : Gm =O[l] s) :
    (fun x => HabitWelfare.cDevAt η (y x) (ym x) (G x) (Gm x)) =O[l] s := by
  have hy1 := isBigO_pow_one hy
  have hym1 := isBigO_pow_one hym
  have e1 : (fun x => y x ^ 2) =O[l] s :=
    (((isBigO_pow_mul hy1 hy1 (by norm_num : 1 + 1 = 2)).trans
      (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))).congr_right fun x => pow_one _).congr_left
        fun x => (sq (y x)).symm
  have e2 : (fun x => ym x ^ 2) =O[l] s :=
    (((isBigO_pow_mul hym1 hym1 (by norm_num : 1 + 1 = 2)).trans
      (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))).congr_right fun x => pow_one _).congr_left
        fun x => (sq (ym x)).symm
  refine ((((hy.add (e1.const_mul_left (1 / 2))).sub
    ((hym.add (e2.const_mul_left (1 / 2))).const_mul_left η))).sub
    (hG.sub (hGm.const_mul_left η))).congr_left fun x => ?_
  unfold HabitWelfare.cDevAt HabitWelfare.ePoly
  ring

/-- Woodford (2003), (E.10), p. 696 (Taylor polynomial of `u` in the habit deviation): with
`σ⁻¹ = −ȳ u_cc/u_c` and `gᵖ = −u_cξ ξ/(ȳ u_cc)`, the (E.2)-type polynomial at `ȳ z` equals
`ū + u_ξξ + ½ξ′u_ξξξ + ȳ u_c · HabitWelfare.uTaylor σ⁻¹ z gᵖ` exactly. -/
theorem uTaylor_habit_eq {ubar uc ucc Lu Cu Qu yb z : ℝ} (hyb : yb ≠ 0) (huc : uc ≠ 0)
    (hucc : ucc ≠ 0) :
    Prop61.uTaylor ubar uc ucc Lu Cu Qu (yb * z) = (ubar + Lu + Qu / 2) + yb * uc *
      HabitWelfare.uTaylor (sigmaInvEl yb uc ucc) z (gShock yb ucc Cu) := by
  unfold Prop61.uTaylor HabitWelfare.uTaylor sigmaInvEl gShock
  field_simp
  ring

/-- Woodford (2003), (E.3)–(E.5): replacing the exact `E_i ŷ = Ŷ − ½(1 − θ⁻¹)var_i ŷ − e` by
`m1Of θ Ŷ V` in the integrated disutility polynomial changes it by `O(s³)` when `e = O(s³)`. -/
theorem vTaylor_m1_isBigO (hs : Tendsto s l (𝓝 0)) (θ ω : ℝ) {Y V e q : α → ℝ}
    (hY : Y =O[l] s) (hV : V =O[l] fun x => s x ^ 2) (he : e =O[l] fun x => s x ^ 3)
    (hq : q =O[l] s) :
    (fun x => HabitWelfare.vTaylor 0 ω (HabitWelfare.m1Of θ (Y x) (V x) - e x)
        (V x + (HabitWelfare.m1Of θ (Y x) (V x) - e x) ^ 2) (q x) -
      HabitWelfare.vTaylor 0 ω (HabitWelfare.m1Of θ (Y x) (V x))
        (HabitWelfare.m2Of θ (Y x) (V x)) (q x)) =O[l] fun x => s x ^ 3 := by
  have hm : (fun x => HabitWelfare.m1Of θ (Y x) (V x)) =O[l] fun x => s x ^ 1 :=
    isBigO_pow_one ((hY.add ((hV.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 2))).congr_right
      (fun x => pow_one _) |>.const_mul_left (-((1 - θ⁻¹) / 2)))).congr_left fun x => by
        unfold HabitWelfare.m1Of; ring)
  have h2 : (fun x => 2 * HabitWelfare.m1Of θ (Y x) (V x) - e x) =O[l] fun x => s x ^ 1 :=
    (hm.const_mul_left 2).sub (he.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 3)))
  have t1 := isBigO_pow_mul he h2 (by norm_num : 3 + 1 = 4)
  have t2 := isBigO_pow_mul (isBigO_pow_one hq) he (by norm_num : 1 + 3 = 4)
  refine ((he.neg_left.sub ((t1.trans (pow_isBigO_pow hs (by norm_num : 3 ≤ 4))).const_mul_left
    ((1 + ω) / 2))).add ((t2.trans (pow_isBigO_pow hs (by norm_num : 3 ≤ 4))).const_mul_left
      ω)).congr_left fun x => ?_
  unfold HabitWelfare.vTaylor HabitWelfare.m2Of
  ring

/-- Woodford (2003), (2.26) and (E.10)–(E.12), pp. 403, 696–697: the period utility polynomial
`HabitWelfare.Useq` at one date, as a function of `Ŷ_t, Ŷ_{t−1}, Ĝ_t, Ĝ_{t−1}, gᵖ_t, q_t` and
`var_i ŷ_t`. -/
noncomputable def UseqAt (P : HabitWelfare.Par) (Y Ym G Gm gp q V : ℝ) : ℝ :=
  HabitWelfare.uTaylor P.sinv (HabitWelfare.cDevAt P.η Y Ym G Gm) gp -
    (1 - P.β * P.η) * HabitWelfare.vTaylor P.Φ P.ω (HabitWelfare.m1Of P.θ Y V)
      (HabitWelfare.m2Of P.θ Y V) q

/-- Woodford (2003), (2.26), p. 403: `Useq` is `UseqAt` at the date-`t` values. -/
theorem Useq_eq_at (P : HabitWelfare.Par) (e : HabitWelfare.Exo) (Ym1 : ℝ) (Y V : ℕ → ℝ)
    (t : ℕ) : HabitWelfare.Useq P e Ym1 Y V t = UseqAt P (Y t) (Sequences.lagS Ym1 Y t) (e.G t)
      (Sequences.lagS e.Gm1 e.G t) (e.gp t) (e.q t) (V t) := rfl

namespace Econ

variable (M : Econ Ξ ι)

/-- Woodford (2003), (2.26), p. 403: `u_c` at the steady-state habit-adjusted consumption `c̄`. -/
noncomputable def ucH (cbar : ℝ) : ℝ := slope M.u cbar

/-- Woodford (2003), (2.26), p. 403: `u_cc` at `c̄`. -/
noncomputable def uccH (cbar : ℝ) : ℝ := curv M.u cbar

/-- Woodford (2003), App. E.3, p. 696: `σ⁻¹ = −Ȳ u_cc/u_c` at `c̄`. -/
noncomputable def sigH (cbar : ℝ) : ℝ := sigmaInvEl M.Yb (M.ucH cbar) (M.uccH cbar)

/-- Woodford (2003), App. E.3, p. 696: the preference disturbance `gᵖ = −u_cξ ξ/(Ȳ u_cc)`. -/
noncomputable def gpH (cbar : ℝ) (ξ : Ξ) : ℝ := gShock M.Yb (M.uccH cbar) (cross M.u cbar ξ)

/-- Woodford (2003), (2.26), p. 403 (**the actual period utility with habits**):
`u((Y_t − G_t) − η(Y_{t−1} − G_{t−1}); ξ_t) − E_i ṽ(y_t(i); ξ_t)` with `Y_t = Ȳ · CES(e^{ŷ_t})`,
`Y_{t−1} = Ȳ e^{Ŷ_{t−1}}`, `G = Ḡ + Ȳ Ĝ`, `y_t(i) = Ȳ e^{ŷ_t(i)}`; here `u = M.u` is the utility
of habit-adjusted consumption. -/
noncomputable def Uhab (η Gbar : ℝ) (yh : ι → ℝ) (Ym G Gm : ℝ) (ξ : Ξ) : ℝ :=
  M.u ((M.Yb * cesIndex M.w (1 - M.θ⁻¹) (fun i => Real.exp (yh i)) - (Gbar + M.Yb * G)) -
      η * (M.Yb * Real.exp Ym - (Gbar + M.Yb * Gm)), ξ) -
    ∑ i, M.w i * M.v (M.Yb * Real.exp (yh i), ξ)

/-- Woodford (2003), Prop. 6.6, pp. 403–404: the habit parameters at the efficient steady state
(`Φ = 0`): `φ = σ⁻¹/(1 − βη)` (Ch. 5 (1.25)), `ω`, `θ` from the primitives. -/
noncomputable def habPar (β η cbar : ℝ) : HabitWelfare.Par :=
  ⟨β, η, M.sigH cbar / (1 - β * η), M.omg, M.θ, 0⟩

variable {M}

omit [Fintype ι] in
/-- Woodford (2003), p. 697: `(1 − βη)φ = σ⁻¹`. -/
theorem habPar_sinv {β η cbar : ℝ} (hβη : 1 - β * η ≠ 0) :
    (M.habPar β η cbar).sinv = M.sigH cbar := by
  unfold HabitWelfare.Par.sinv habPar
  field_simp

/-- Woodford (2003), (2.26) and (E.10)–(E.12), pp. 403, 696–697 (**Proposition 6.6, period by
period, Layer B in the state variables**): at the efficient steady state
(`ṽ_y = (1 − βη) u_c`, `Φ = 0`), for any family with `ŷ_t`, `Ŷ_{t−1}`, `Ĝ_t`, `Ĝ_{t−1}`, `ξ_t` all
`O(s)`, the actual habit utility is
`U_t = tip0_u(ξ_t) − tip0_v(ξ_t) + Ȳu_c · Useq_t + O(s³)`, `Useq_t` the exact second-order
polynomial of HabitWelfare (`UseqAt`). -/
theorem habit_state (hM : M.Std) {P : HabitWelfare.Par} {Gbar cbar : ℝ}
    (hPs : P.sinv = M.sigH cbar) (hPΦ : P.Φ = 0) (hPω : P.ω = M.omg) (hPθ : P.θ = M.θ)
    (hcbar : cbar = (1 - P.η) * (M.Yb - Gbar)) (hβη : 1 - P.β * P.η ≠ 0) (huc : 0 < M.ucH cbar)
    (hucc : M.uccH cbar ≠ 0) (heff : M.vy = (1 - P.β * P.η) * M.ucH cbar)
    (hs : Tendsto s l (𝓝 0)) {yh : α → ι → ℝ} {Ym G Gm : α → ℝ} {ξ : α → Ξ} (hy : yh =O[l] s)
    (hYm : Ym =O[l] s) (hG : G =O[l] s) (hGm : Gm =O[l] s) (hξ : ξ =O[l] s) :
    (fun x => M.Uhab P.η Gbar (yh x) (Ym x) (G x) (Gm x) (ξ x) -
      (tip0 M.u cbar (ξ x) - tip0 M.v M.Yb (ξ x) + M.Yb * M.ucH cbar *
        UseqAt P (M.Yagg (yh x)) (Ym x) (G x) (Gm x) (M.gpH cbar (ξ x))
          (M.qS (ξ x)) (crossVar M.w (yh x)))) =O[l] fun x => s x ^ 3 := by
  set η := P.η
  set β := P.β
  have hyb : M.Yb ≠ 0 := hM.Yb_pos.ne'
  have heff' : slope M.v M.Yb = (1 - β * η) * slope M.u cbar := heff
  have hvy : slope M.v M.Yb ≠ 0 := by
    rw [heff']; exact mul_ne_zero hβη huc.ne'
  obtain ⟨-, hV, he, hY⟩ := ces_orders hM.w_nonneg hM.w_sum (r_ne hM) hs hy
  -- the consumption side
  have hδ : (fun x => expRem (cumulant M.w (1 - M.θ⁻¹) (yh x)) - η * expRem (Ym x)) =O[l]
      fun x => s x ^ 3 :=
    (expRem_isBigO hs hY).sub ((expRem_isBigO hs hYm).const_mul_left η)
  have hcD := cDev_isBigO hs η hY hYm hG hGm
  have hc : (fun x => M.Yb * (HabitWelfare.cDevAt η (cumulant M.w (1 - M.θ⁻¹) (yh x)) (Ym x)
      (G x) (Gm x) + (expRem (cumulant M.w (1 - M.θ⁻¹) (yh x)) - η * expRem (Ym x)))) =O[l] s :=
    (hcD.add (hδ.trans (pow_isBigO_pow hs (by norm_num : 1 ≤ 3)) |>.congr_right
      fun x => pow_one _)).const_mul_left _
  have hA := taylor_pair hM.contDiff_u cbar hs hc hξ
  have hgp : (fun x => M.gpH cbar (ξ x)) =O[l] s :=
    ((cross_isBigO M.u cbar hξ).const_mul_left (-(M.Yb * M.uccH cbar)⁻¹)).congr_left fun x => by
      unfold gpH gShock; ring
  have hF : (fun x => 1 - M.sigH cbar * HabitWelfare.cDevAt η (cumulant M.w (1 - M.θ⁻¹) (yh x))
      (Ym x) (G x) (Gm x) - M.sigH cbar / 2 * (expRem (cumulant M.w (1 - M.θ⁻¹) (yh x)) -
        η * expRem (Ym x)) + M.sigH cbar * M.gpH cbar (ξ x)) =O[l] fun _ => (1 : ℝ) := by
    have o : s =O[l] fun _ => (1 : ℝ) := hs.isBigO_one ℝ
    exact (((isBigO_const_const (1 : ℝ) one_ne_zero l).sub
      ((hcD.trans o).const_mul_left _)).sub
      (((hδ.trans (pow_isBigO_pow hs (by norm_num : 0 ≤ 3))).congr_right
        fun x => pow_zero _).const_mul_left _)).add ((hgp.trans o).const_mul_left _)
  have hB := isBigO_mul_bdd hδ hF
  -- the disutility side
  have hv := vside_gen hM.contDiff_v hyb hvy hM.vyy_ne hM.w_sum hs hy hξ
  have hvm := vTaylor_m1_isBigO hs M.θ M.omg hY hV he (M.qS_isBigO hξ)
  refine (((hA.add (hB.const_mul_left (M.Yb * M.ucH cbar))).sub hv).sub
    (hvm.const_mul_left (M.Yb * slope M.v M.Yb))).congr_left fun x => ?_
  have harg : (M.Yb * cesIndex M.w (1 - M.θ⁻¹) (fun i => Real.exp (yh x i)) -
      (Gbar + M.Yb * G x)) - η * (M.Yb * Real.exp (Ym x) - (Gbar + M.Yb * Gm x)) =
      cbar + M.Yb * (HabitWelfare.cDevAt η (cumulant M.w (1 - M.θ⁻¹) (yh x)) (Ym x) (G x)
        (Gm x) + (expRem (cumulant M.w (1 - M.θ⁻¹) (yh x)) - η * expRem (Ym x))) := by
    rw [cesIndex_exp_eq hM.w_nonneg hM.w_sum]
    have h1 := ExpLogCES.exp_sub_one_eq (cumulant M.w (1 - M.θ⁻¹) (yh x))
    have h2 := ExpLogCES.exp_sub_one_eq (Ym x)
    unfold HabitWelfare.cDevAt HabitWelfare.ePoly
    rw [hcbar]
    linear_combination M.Yb * h1 - η * M.Yb * h2
  unfold Uhab
  rw [harg, uTaylor_habit_eq (uc := slope M.u cbar) (ucc := curv M.u cbar) hyb huc.ne' hucc]
  unfold UseqAt
  rw [hPs, hPΦ, hPω, hPθ]
  unfold HabitWelfare.uTaylor HabitWelfare.vTaylor HabitWelfare.m1Of HabitWelfare.m2Of tip0 Yagg
    sigH gpH ucH uccH omg qS vy vyy
  set ω := omegaEl M.Yb (slope M.v M.Yb) (curv M.v M.Yb)
  rw [heff']
  ring

end Econ

/-- Woodford (2003), (E.12), p. 697: the period-utility polynomial of bounded sequences is a
bounded sequence. -/
theorem bdd_UseqAt (P : HabitWelfare.Par) {Y Ym G Gm gp q V : ℕ → ℝ} (hY : Sequences.Bdd Y)
    (hYm : Sequences.Bdd Ym) (hG : Sequences.Bdd G) (hGm : Sequences.Bdd Gm)
    (hgp : Sequences.Bdd gp) (hq : Sequences.Bdd q) (hV : Sequences.Bdd V) :
    Sequences.Bdd (fun t => UseqAt P (Y t) (Ym t) (G t) (Gm t) (gp t) (q t) (V t)) := by
  have hc : Sequences.Bdd (fun t => HabitWelfare.cDevAt P.η (Y t) (Ym t) (G t) (Gm t)) := by
    unfold HabitWelfare.cDevAt HabitWelfare.ePoly
    exact ((hY.add ((hY.pow 2).div_const 2)).sub ((Sequences.Bdd.const _).mul
      (hYm.add ((hYm.pow 2).div_const 2)))).sub (hG.sub ((Sequences.Bdd.const _).mul hGm))
  have hm : Sequences.Bdd (fun t => HabitWelfare.m1Of P.θ (Y t) (V t)) := by
    unfold HabitWelfare.m1Of
    exact hY.sub ((Sequences.Bdd.const _).mul hV)
  unfold UseqAt HabitWelfare.uTaylor HabitWelfare.vTaylor HabitWelfare.m2Of
  exact ((hc.sub ((Sequences.Bdd.const _).mul (hc.pow 2))).add
    (((Sequences.Bdd.const _).mul hgp).mul hc)).sub ((Sequences.Bdd.const _).mul
      ((Sequences.Bdd.const _).mul ((hm.add ((Sequences.Bdd.const _).mul (hV.add (hm.pow 2)))).sub
        (((Sequences.Bdd.const _).mul hq).mul hm))))

/-- Woodford (2003), App. E.3 (survey error 25): a bounded sequence is `O(1)` uniformly. -/
theorem unif_of_bdd {f : ℕ → ℝ} (h : Sequences.Bdd f) :
    (fun p : ℕ × ℝ => f p.1) =O[unif] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC⟩ := h
  exact unif_of_bounded ⟨C, fun t => by simpa using hC t⟩

/-- Woodford (2003), App. E.3, p. 696: the lag of a scaled sequence is the scaled lag. -/
theorem lagS_smul (r a : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    Sequences.lagS (r * a) (fun s => r * x s) t = r * Sequences.lagS a x t := by
  cases t <;> rfl

/-- Woodford (2003), App. E.3, pp. 696–697 (the one-parameter family of exogenous data): all
disturbances, the natural rate and their initial values scaled by `ε`. -/
def exoSmul (r : ℝ) (e : HabitWelfare.Exo) : HabitWelfare.Exo :=
  ⟨fun t => r * e.G t, r * e.Gm1, fun t => r * e.gp t, fun t => r * e.q t, fun t => r * e.n t,
    r * e.nm1⟩

/-- Woodford (2003), p. 697: the flexible-price residual is linear in the exogenous data, so
`r_t(ε e₁) = ε r_t(e₁)`; if the first-order natural rate satisfies the (perfect-foresight)
flexible-price relation, so does its scaled version. -/
theorem rS_exoSmul (P : HabitWelfare.Par) (r : ℝ) (e : HabitWelfare.Exo) (t : ℕ) :
    HabitWelfare.rS P (exoSmul r e) t = r * HabitWelfare.rS P e t := by
  unfold HabitWelfare.rS HabitWelfare.gTil HabitWelfare.gS
  dsimp only [exoSmul]
  rw [lagS_smul, lagS_smul]
  ring

/-- Woodford (2003), App. E.3, p. 696 (survey error 25): the lag `x_{t−1}` (with initial value
`x_{−1}(ε)`) of a sequence that is `O(g)` uniformly in `t` is `O(g)` uniformly in `t`, provided
`x_{−1}(ε) = O(g)`. -/
theorem lag_unif {F : ℕ → ℝ → ℝ} {A g : ℝ → ℝ}
    (hF : (fun p : ℕ × ℝ => F p.1 p.2) =O[unif] fun p => g p.2) (hA : A =O[𝓝 0] g) :
    (fun p : ℕ × ℝ => Sequences.lagS (A p.2) (fun s => F s p.2) p.1) =O[unif]
      fun p => g p.2 := by
  obtain ⟨C1, h1⟩ := isBigO_unif_iff.1 hF
  obtain ⟨C2, h2⟩ := hA.bound
  refine (isBigO_unif_iff (f := fun t ε => Sequences.lagS (A ε) (fun s => F s ε) t)).2
    ⟨max C1 C2, ?_⟩
  filter_upwards [h1, h2] with ε e1 e2 t
  cases t with
  | zero => exact e2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  | succ t => exact (e1 t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- Woodford (2003), (E.2): `tip0` along `ε ξ₁_t` is bounded uniformly in `t` for bounded
`ξ₁_t`. -/
theorem tip0_unif (U : ℝ × Ξ → ℝ) (yb : ℝ) {ξ1 : ℕ → Ξ} (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) :
    (fun p : ℕ × ℝ => tip0 U yb (p.2 • ξ1 p.1)) =O[unif] fun _ => (1 : ℝ) := by
  have hx := unif_of_bounded hξ1
  have he : (fun p : ℕ × ℝ => p.2) =O[unif] fun _ => (1 : ℝ) := tendsto_unif.isBigO_one ℝ
  have t1 : (fun p : ℕ × ℝ => p.2 * lin U yb (ξ1 p.1)) =O[unif] fun _ => (1 : ℝ) :=
    (he.mul (lin_isBigO U yb hx)).congr_right fun _ => mul_one 1
  have t2 : (fun p : ℕ × ℝ => p.2 ^ 2 * quad U yb (ξ1 p.1)) =O[unif] fun _ => (1 : ℝ) :=
    ((he.pow 2).mul (quad_isBigO U yb hx)).congr_right fun _ => by ring
  refine (((isBigO_const_const (U (yb, 0)) one_ne_zero unif).add t1).add
    (t2.const_mul_left (1 / 2))).congr_left fun p => ?_
  unfold tip0
  rw [lin_smul, quad_smul]
  ring

namespace Econ

variable {M : Econ Ξ ι}

omit [Fintype ι] in
/-- Woodford (2003), App. E.3: `gᵖ` is linear in the disturbances. -/
theorem gpH_smul (cbar r : ℝ) (ξ : Ξ) : M.gpH cbar (r • ξ) = r * M.gpH cbar ξ := by
  unfold gpH gShock
  rw [cross_smul]
  ring

omit [Fintype ι] in
/-- Woodford (2003), Prop. 6.6, p. 403 (**the habit parameters built from the primitives satisfy
the maintained restrictions**): `habPar` has `σ⁻¹ = (1 − βη)φ`, `Φ = 0`, and is `Std` when
`0 ≤ β < 1`, `0 ≤ η ≤ 1`, `σ⁻¹ > 0`, `ω ≥ 0`. -/
theorem habPar_spec {β η cbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hσ : 0 < M.sigH cbar) (hω : 0 ≤ M.omg) :
    (M.habPar β η cbar).Std ∧ (M.habPar β η cbar).sinv = M.sigH cbar ∧
      (M.habPar β η cbar).Φ = 0 ∧ (M.habPar β η cbar).ω = M.omg ∧
      (M.habPar β η cbar).θ = M.θ := by
  have hβη : 0 < 1 - β * η := by nlinarith
  exact ⟨⟨hβ0, hβ1, hη0, hη1, div_pos hσ hβη, hω⟩, habPar_sinv hβη.ne', rfl, rfl, rfl⟩

/-- Woodford (2003), **Proposition 6.6 CORRECTED, eqs. (2.27)/(E.9), pp. 403–404, 696–698
(Layer B, discounted)**. Habit persistence, efficient steady state (`ṽ_y = (1 − βη)u_c`,
`Φ = 0`), habit parameters `P` matching the primitives (`habPar_spec`). The exogenous data are
`ε e₁` (`exoSmul`): government purchases `ε Ĝ₁_t`, disturbances `ε ξ₁_t` with
`gᵖ₁_t = gᵖ(ξ₁_t)`, `q₁_t = q(ξ₁_t)`, and the first-order natural rate `Ŷⁿ₁_t` satisfying the
perfect-foresight flexible-price relation (`rS P e₁ t = 0`). If `ŷ_t(ε) − ε y₁_t = O(ε²)` UNIFORMLY
in `t` (survey error 25), `y₁, ξ₁, Ĝ₁, Ŷⁿ₁` bounded and the initial lagged output
`Ŷ_{−1}(ε) − ε Ŷ₁_{−1} = O(ε²)`, then
`∑ βᵗ U_t(ε) = TIP(ε) − (ε²/2) Ȳu_c ∑ βᵗ [μ_x (x₁_t − δ x₁_{t−1})² + (1 − βη)(θ⁻¹ + ω) var_i y₁_t]
+ O(ε³)`
with `TIP(ε) = ∑ βᵗ (tip0_u − tip0_v)(ε ξ₁_t) + Ȳu_c · tipTotal(ε e₁, Ŷ_{−1}(ε))` and the CORRECTED
dispersion weight `(1 − βη)(θ⁻¹ + ω)` (survey error 16; the printed `θ⁻¹ + ω` is refuted by
`HabitWelfare.printed_E9_discounted_false`). The Layer-A identity is
`HabitWelfare.prop66_corrected`. -/
theorem prop66_bridge (hM : M.Std) {P : HabitWelfare.Par} (hP : P.Std) {Gbar cbar : ℝ}
    (hPs : P.sinv = M.sigH cbar) (hPΦ : P.Φ = 0) (hPω : P.ω = M.omg) (hPθ : P.θ = M.θ)
    (hcbar : cbar = (1 - P.η) * (M.Yb - Gbar)) (huc : 0 < M.ucH cbar)
    (hucc : M.uccH cbar ≠ 0) (heff : M.vy = (1 - P.β * P.η) * M.ucH cbar)
    {e1 : HabitWelfare.Exo} {ξ1 : ℕ → Ξ} (hgp : ∀ t, e1.gp t = M.gpH cbar (ξ1 t))
    (hq : ∀ t, e1.q t = M.qS (ξ1 t)) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (hG1 : Sequences.Bdd e1.G) (hn1 : Sequences.Bdd e1.n) (hflex : ∀ t, HabitWelfare.rS P e1 t = 0)
    {yh : ℕ → ℝ → ι → ℝ} {y1 : ℕ → ι → ℝ}
    (h : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ t, ‖y1 t‖ ≤ C) {Ym1 : ℝ → ℝ} {Y1m1 : ℝ}
    (hYm1 : (fun ε => Ym1 ε - ε * Y1m1) =O[𝓝 0] fun ε => ε ^ 2) :
    (fun ε => ∑' t, P.β ^ t * M.Uhab P.η Gbar (yh t ε)
        (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
        (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
      ((∑' t, P.β ^ t * (tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) +
          M.Yb * M.ucH cbar * HabitWelfare.tipTotal P (exoSmul ε e1) (Ym1 ε)) +
        ε ^ 2 / 2 * (-(M.Yb * M.ucH cbar * ∑' t, P.β ^ t *
          (P.muX * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (y1 s)) t +
            (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * crossVar M.w (y1 t)))))) =O[𝓝 0]
      fun ε => ε ^ 3 := by
  have hβ0 : 0 ≤ P.β := hP.1
  have hβ1 : P.β < 1 := hP.2.1
  have hβη : 0 < 1 - P.β * P.η := by
    have := hP.2.2.1; have := hP.2.2.2.1; nlinarith
  have hw := hM.w_nonneg
  have hw1 := hM.w_sum
  -- uniform orders of the state variables
  have hy1u := unif_of_bounded hy1
  have hx1 := unif_of_bounded hξ1
  have hyu : (fun p : ℕ × ℝ => yh p.1 p.2) =O[unif] fun p => p.2 :=
    family_isBigO (s := fun p : ℕ × ℝ => p.2) tendsto_unif h hy1u
  obtain ⟨-, hVu, heu, hYu⟩ := ces_orders hw hw1 (r_ne hM) tendsto_unif hyu
  have hYm1' : Ym1 =O[𝓝 0] fun ε => ε := by
    have h2 : (fun ε : ℝ => Ym1 ε - ε * Y1m1) =O[𝓝 0] fun ε => ε :=
      (hYm1.trans (pow_isBigO_pow (s := fun ε : ℝ => ε) tendsto_id
        (by norm_num : 1 ≤ 2))).congr_right fun ε => pow_one ε
    exact (h2.add ((isBigO_refl (fun ε : ℝ => ε) (𝓝 0)).const_mul_left Y1m1)).congr_left
      fun ε => by ring
  have hYlag := lag_unif (F := fun t ε => M.Yagg (yh t ε)) (A := Ym1) (g := fun ε => ε) hYu
    hYm1'
  obtain ⟨CG, hCG⟩ := hG1
  have hG1u : (fun p : ℕ × ℝ => e1.G p.1) =O[unif] fun _ => (1 : ℝ) :=
    unif_of_bounded ⟨CG, fun t => by simpa using hCG t⟩
  have hGu : (fun p : ℕ × ℝ => p.2 * e1.G p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul hG1u).congr_right fun _ => mul_one _
  have hGlb : Sequences.Bdd (Sequences.lagS e1.Gm1 e1.G) := Sequences.Bdd.lagS ⟨CG, hCG⟩ _
  obtain ⟨CGl, hCGl⟩ := hGlb
  have hGlag : (fun p : ℕ × ℝ => Sequences.lagS (p.2 * e1.Gm1) (fun s => p.2 * e1.G s) p.1)
      =O[unif] fun p => p.2 :=
    (((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul (unif_of_bounded (f := fun t =>
      Sequences.lagS e1.Gm1 e1.G t) ⟨CGl, fun t => by simpa using hCGl t⟩)).congr_right
        fun _ => mul_one _).congr_left fun p => (lagS_smul _ _ _ _).symm
  have hξu : (fun p : ℕ × ℝ => p.2 • ξ1 p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).smul hx1).congr_right fun _ => mul_one _
  -- the period bridge, uniformly in `t`
  have hρ0 := habit_state (l := unif) (s := fun p : ℕ × ℝ => p.2) hM hPs hPΦ hPω hPθ hcbar
    hβη.ne' huc hucc heff tendsto_unif hyu hYlag hGu hGlag hξu
  have hρ : (fun p : ℕ × ℝ => M.Uhab P.η Gbar (yh p.1 p.2)
      (Sequences.lagS (Ym1 p.2) (fun s => M.Yagg (yh s p.2)) p.1) (p.2 * e1.G p.1)
      (Sequences.lagS (p.2 * e1.Gm1) (fun s => p.2 * e1.G s) p.1) (p.2 • ξ1 p.1) -
      ((tip0 M.u cbar (p.2 • ξ1 p.1) - tip0 M.v M.Yb (p.2 • ξ1 p.1)) + M.Yb * M.ucH cbar *
        HabitWelfare.Useq P (exoSmul p.2 e1) (Ym1 p.2) (fun s => M.Yagg (yh s p.2))
          (fun s => crossVar M.w (yh s p.2)) p.1)) =O[unif] fun p => p.2 ^ 3 := by
    refine hρ0.congr_left fun p => ?_
    rw [Useq_eq_at]
    dsimp only [exoSmul]
    rw [hgp, hq, gpH_smul, M.qS_smul]
  -- the remainder of the Layer-A identity, uniformly in `t`
  have hgpb : (fun p : ℕ × ℝ => e1.gp p.1) =O[unif] fun _ => (1 : ℝ) :=
    ((cross_isBigO M.u cbar hx1).const_mul_left (-(M.Yb * M.uccH cbar)⁻¹)).congr_left
      fun p => by rw [hgp]; unfold gpH gShock; ring
  have hqb : (fun p : ℕ × ℝ => e1.q p.1) =O[unif] fun _ => (1 : ℝ) :=
    (M.qS_isBigO hx1).congr_left fun p => (hq p.1).symm
  have hgpu : (fun p : ℕ × ℝ => p.2 * e1.gp p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul hgpb).congr_right fun _ => mul_one _
  have hqu : (fun p : ℕ × ℝ => p.2 * e1.q p.1) =O[unif] fun p => p.2 :=
    ((isBigO_refl (fun p : ℕ × ℝ => p.2) unif).mul hqb).congr_right fun _ => mul_one _
  have hRU : (fun p : ℕ × ℝ => HabitWelfare.RUseq P (exoSmul p.2 e1) (Ym1 p.2)
      (fun s => M.Yagg (yh s p.2)) (fun s => crossVar M.w (yh s p.2)) p.1) =O[unif]
      fun p => p.2 ^ 3 := by
    refine ((E10rem_isBigO tendsto_unif P.sinv P.η hYu hYlag hGu hGlag hgpu).sub
      ((vRem_isBigO tendsto_unif P.θ P.ω hYu hqu hVu).const_mul_left
        (1 - P.β * P.η))).congr_left fun p => ?_
    unfold HabitWelfare.RUseq
    dsimp only [exoSmul]
    rw [hPΦ]
    rfl
  -- the gap, uniformly in `t`
  have hY1b : (fun p : ℕ × ℝ => crossMean M.w (y1 p.1)) =O[unif] fun _ => (1 : ℝ) :=
    crossMean_isBigO hw hw1 hy1u
  have hD0 : (fun p : ℕ × ℝ => M.Yagg (yh p.1 p.2) - p.2 * crossMean M.w (y1 p.1)) =O[unif]
      fun p => p.2 ^ 2 :=
    (((heu.trans (pow_isBigO_pow tendsto_unif (by norm_num : 2 ≤ 3))).add
      (hVu.const_mul_left ((1 - M.θ⁻¹) / 2))).add (crossMean_isBigO hw hw1 h)).congr_left
        fun p => by rw [crossMean_sub', crossMean_smul']; unfold Yagg; ring
  have hlagD := lag_unif (F := fun t ε => M.Yagg (yh t ε) - ε * crossMean M.w (y1 t))
    (A := fun ε => Ym1 ε - ε * Y1m1) (g := fun ε => ε ^ 2) hD0 hYm1
  have hxhat := HabitWelfare.xhat_of_Phi_zero hPΦ
  have ha : (fun p : ℕ × ℝ =>
      (HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2)) p.1 -
        P.δ * Sequences.lagS (Ym1 p.2 - (exoSmul p.2 e1).nm1)
          (HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2))) p.1 - P.xhat) -
      p.2 * (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) p.1 -
        P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
          p.1 - P.xhat)) =O[unif] fun p => p.2 ^ 2 := by
    refine (hD0.sub (hlagD.const_mul_left P.δ)).congr_left fun p => ?_
    obtain ⟨t, ε⟩ := p
    rw [hxhat]
    cases t <;> simp only [Sequences.lagS, HabitWelfare.xS, exoSmul] <;> ring
  have hx1b : Sequences.Bdd (fun t => HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) t -
      P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
        t - P.xhat) := by
    have hm : Sequences.Bdd (fun s => crossMean M.w (y1 s)) :=
      bounded_of_unif (f := fun s => crossMean M.w (y1 s)) hY1b
    have hxs : Sequences.Bdd (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s))) := hm.sub hn1
    exact (hxs.sub ((Sequences.Bdd.const _).mul (hxs.lagS _))).sub (Sequences.Bdd.const _)
  have ha1 : (fun p : ℕ × ℝ => HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) p.1 -
      P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
        p.1 - P.xhat) =O[unif] fun _ => (1 : ℝ) :=
    unif_of_bdd (f := fun t => HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)) t -
      P.δ * Sequences.lagS (Y1m1 - e1.nm1) (HabitWelfare.xS e1 (fun s => crossMean M.w (y1 s)))
        t - P.xhat) hx1b
  have hgap := sq_sub_sq_isBigO tendsto_unif ha ha1
  have hVd := crossVar_family hw hw1 tendsto_unif h hy1u
  -- discounted sums of the three uniform remainders
  have S1 := tsum_isBigO_of_unif (f := fun t ε => M.Uhab P.η Gbar (yh t ε)
      (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
      (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
      ((tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) + M.Yb * M.ucH cbar *
        HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε))
          (fun s => crossVar M.w (yh s ε)) t)) hβ0 hβ1 hρ
  have S2 := tsum_isBigO_of_unif (f := fun t ε => HabitWelfare.RUseq P (exoSmul ε e1) (Ym1 ε)
      (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) t) hβ0 hβ1 hRU
  have S3 := tsum_isBigO_of_unif (f := fun t ε =>
      P.muX * (HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε)) t -
        ε ^ 2 * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (y1 s)) t) +
      (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * (crossVar M.w (yh t ε) - ε ^ 2 * crossVar M.w (y1 t)))
      hβ0 hβ1 ((hgap.const_mul_left P.muX).add (hVd.const_mul_left _))
  have hcomb := (S1.add (S2.const_mul_left (M.Yb * M.ucH cbar))).sub
    (S3.const_mul_left (M.Yb * M.ucH cbar / 2))
  -- boundedness for each small `ε`
  have one : (fun p : ℕ × ℝ => p.2) =O[unif] fun _ => (1 : ℝ) := tendsto_unif.isBigO_one ℝ
  have b2 : ∀ {n : ℕ}, (fun p : ℕ × ℝ => p.2 ^ n) =O[unif] fun _ => (1 : ℝ) := fun {n} =>
    (one.pow n).congr_right fun _ => one_pow n
  have hab : (fun p : ℕ × ℝ =>
      HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2)) p.1 -
        P.δ * Sequences.lagS (Ym1 p.2 - (exoSmul p.2 e1).nm1)
          (HabitWelfare.xS (exoSmul p.2 e1) (fun s => M.Yagg (yh s p.2))) p.1 - P.xhat)
      =O[unif] fun _ => (1 : ℝ) :=
    ((ha.trans b2).add ((one.mul ha1).congr_right fun _ => mul_one 1)).congr_left
      fun p => by ring
  obtain ⟨Cy, hCy⟩ := hy1
  have bV1 : Sequences.Bdd (fun t => crossVar M.w (y1 t)) := ⟨Cy ^ 2, fun t => by
    have h := ExpLogCES.crossVar_le hw hw1 (y1 t)
    rw [abs_of_nonneg h.1]
    exact h.2.trans (pow_le_pow_left₀ (norm_nonneg _) (hCy t) 2)⟩
  have bB : Sequences.Bdd (fun t => P.muX * HabitWelfare.gapSq P e1 Y1m1
      (fun s => crossMean M.w (y1 s)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
        crossVar M.w (y1 t)) :=
    ((Sequences.Bdd.const _).mul (hx1b.pow 2)).add ((Sequences.Bdd.const _).mul bV1)
  have bgp1 : Sequences.Bdd e1.gp := bounded_of_unif (f := e1.gp) hgpb
  have bq1 : Sequences.Bdd e1.q := bounded_of_unif (f := e1.q) hqb
  have bG1 : Sequences.Bdd e1.G := ⟨CG, hCG⟩
  refine hcomb.congr' ?_ EventuallyEq.rfl
  filter_upwards [bdd_of_unif (f := fun t ε => M.Yagg (yh t ε)) (g := fun ε => ε) hYu,
    bdd_of_unif (f := fun t ε => crossVar M.w (yh t ε)) (g := fun ε => ε ^ 2) hVu,
    bdd_of_unif (f := fun t ε => tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t))
      (g := fun _ => (1 : ℝ)) ((tip0_unif M.u cbar hξ1).sub (tip0_unif M.v M.Yb hξ1)),
    bdd_of_unif (f := fun t ε => M.Uhab P.η Gbar (yh t ε)
      (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
      (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
      ((tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) + M.Yb * M.ucH cbar *
        HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε))
          (fun s => crossVar M.w (yh s ε)) t)) (g := fun ε => ε ^ 3) hρ,
    bdd_of_unif (f := fun t ε =>
      HabitWelfare.xS (exoSmul ε e1) (fun s => M.Yagg (yh s ε)) t -
        P.δ * Sequences.lagS (Ym1 ε - (exoSmul ε e1).nm1)
          (HabitWelfare.xS (exoSmul ε e1) (fun s => M.Yagg (yh s ε))) t - P.xhat)
      (g := fun _ => (1 : ℝ)) hab] with ε bY bV bT bρ bX
  have hb : (exoSmul ε e1).Bounded :=
    ⟨(Sequences.Bdd.const ε).mul bG1, (Sequences.Bdd.const ε).mul bgp1,
      (Sequences.Bdd.const ε).mul bq1, (Sequences.Bdd.const ε).mul hn1⟩
  have bUs : Sequences.Bdd (fun t => HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε)
      (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) t) := by
    have := bdd_UseqAt P bY (bY.lagS (Ym1 ε)) ((Sequences.Bdd.const ε).mul bG1)
      (((Sequences.Bdd.const ε).mul bG1).lagS (ε * e1.Gm1)) ((Sequences.Bdd.const ε).mul bgp1)
      ((Sequences.Bdd.const ε).mul bq1) bV
    exact this
  have bA : Sequences.Bdd (fun t => P.muX * HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε)
      (fun s => M.Yagg (yh s ε)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
        crossVar M.w (yh t ε)) :=
    ((Sequences.Bdd.const _).mul (bX.pow 2)).add ((Sequences.Bdd.const _).mul bV)
  have h66 := HabitWelfare.prop66_corrected hP (exoSmul ε e1) (Ym1 ε)
    (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) bY bV hb
  have e_r : ∑' t, P.β ^ t * (HabitWelfare.rS P (exoSmul ε e1) t *
      HabitWelfare.xS (exoSmul ε e1) (fun s => M.Yagg (yh s ε)) t) = 0 := by
    simp [rS_exoSmul, hflex]
  have sT := bT.summable hβ0 hβ1
  have sU := bUs.summable hβ0 hβ1
  have sρ := bρ.summable hβ0 hβ1
  have e_U : ∑' t, P.β ^ t * M.Uhab P.η Gbar (yh t ε)
        (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
        (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) =
      ∑' t, P.β ^ t * (tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) +
        M.Yb * M.ucH cbar * ∑' t, P.β ^ t * HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε)
          (fun s => M.Yagg (yh s ε)) (fun s => crossVar M.w (yh s ε)) t +
        ∑' t, P.β ^ t * (M.Uhab P.η Gbar (yh t ε)
          (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yh s ε)) t) (ε * e1.G t)
          (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) -
          ((tip0 M.u cbar (ε • ξ1 t) - tip0 M.v M.Yb (ε • ξ1 t)) + M.Yb * M.ucH cbar *
            HabitWelfare.Useq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε))
              (fun s => crossVar M.w (yh s ε)) t)) := by
    rw [← tsum_mul_left, ← sT.tsum_add (sU.mul_left _), ← (sT.add (sU.mul_left _)).tsum_add sρ]
    exact tsum_congr fun t => by ring
  have e_A : ∑' t, P.β ^ t *
      (P.muX * (HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε) (fun s => M.Yagg (yh s ε)) t -
        ε ^ 2 * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (y1 s)) t) +
      (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
        (crossVar M.w (yh t ε) - ε ^ 2 * crossVar M.w (y1 t))) =
      ∑' t, P.β ^ t * (P.muX * HabitWelfare.gapSq P (exoSmul ε e1) (Ym1 ε)
        (fun s => M.Yagg (yh s ε)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
          crossVar M.w (yh t ε)) -
      ε ^ 2 * ∑' t, P.β ^ t * (P.muX * HabitWelfare.gapSq P e1 Y1m1
        (fun s => crossMean M.w (y1 s)) t + (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) *
          crossVar M.w (y1 t)) := by
    rw [← tsum_mul_left, ← (bA.summable hβ0 hβ1).tsum_sub ((bB.summable hβ0 hβ1).mul_left _)]
    exact tsum_congr fun t => by ring
  rw [e_U, h66, e_r]
  linear_combination (-(M.Yb * M.ucH cbar / 2)) * e_A

/-- Woodford (2003), §2.2, p. 404 (**welfare ranking with habit persistence, corrected
weights**): two policies with the same exogenous data `ε e₁`, disturbances `ε ξ₁_t` and initial
lagged output `Ŷ_{−1}(ε)`, each satisfying the hypotheses of `prop66_bridge`; if the corrected
discounted first-order loss of `A`,
`∑ βᵗ [μ_x (x₁ᴬ_t − δ x₁ᴬ_{t−1})² + (1 − βη)(θ⁻¹ + ω) var_i y₁ᴬ_t]`, is smaller than that of `B`,
then `A` gives strictly higher discounted utility for all small `ε > 0`. -/
theorem prop66_ranking (hM : M.Std) {P : HabitWelfare.Par} (hP : P.Std) {Gbar cbar : ℝ}
    (hPs : P.sinv = M.sigH cbar) (hPΦ : P.Φ = 0) (hPω : P.ω = M.omg) (hPθ : P.θ = M.θ)
    (hcbar : cbar = (1 - P.η) * (M.Yb - Gbar)) (huc : 0 < M.ucH cbar)
    (hucc : M.uccH cbar ≠ 0) (heff : M.vy = (1 - P.β * P.η) * M.ucH cbar)
    {e1 : HabitWelfare.Exo} {ξ1 : ℕ → Ξ} (hgp : ∀ t, e1.gp t = M.gpH cbar (ξ1 t))
    (hq : ∀ t, e1.q t = M.qS (ξ1 t)) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (hG1 : Sequences.Bdd e1.G) (hn1 : Sequences.Bdd e1.n) (hflex : ∀ t, HabitWelfare.rS P e1 t = 0)
    {yA yB : ℕ → ℝ → ι → ℝ} {yA1 yB1 : ℕ → ι → ℝ}
    (hA : (fun p : ℕ × ℝ => yA p.1 p.2 - p.2 • yA1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hB : (fun p : ℕ × ℝ => yB p.1 p.2 - p.2 • yB1 p.1) =O[unif] fun p => p.2 ^ 2)
    (hyA : ∃ C, ∀ t, ‖yA1 t‖ ≤ C) (hyB : ∃ C, ∀ t, ‖yB1 t‖ ≤ C) {Ym1 : ℝ → ℝ} {Y1m1 : ℝ}
    (hYm1 : (fun ε => Ym1 ε - ε * Y1m1) =O[𝓝 0] fun ε => ε ^ 2)
    (hL : ∑' t, P.β ^ t * (P.muX * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (yA1 s)) t +
        (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * crossVar M.w (yA1 t)) <
      ∑' t, P.β ^ t * (P.muX * HabitWelfare.gapSq P e1 Y1m1 (fun s => crossMean M.w (yB1 s)) t +
        (1 - P.β * P.η) * (P.θ⁻¹ + P.ω) * crossVar M.w (yB1 t))) :
    ∀ᶠ ε in 𝓝[>] 0,
      ∑' t, P.β ^ t * M.Uhab P.η Gbar (yB t ε)
        (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yB s ε)) t) (ε * e1.G t)
        (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) <
      ∑' t, P.β ^ t * M.Uhab P.η Gbar (yA t ε)
        (Sequences.lagS (Ym1 ε) (fun s => M.Yagg (yA s ε)) t) (ε * e1.G t)
        (Sequences.lagS (ε * e1.Gm1) (fun s => ε * e1.G s) t) (ε • ξ1 t) :=
  ranking_of_tip (mul_pos hM.Yb_pos huc)
    (prop66_bridge hM hP hPs hPΦ hPω hPθ hcbar huc hucc heff hgp hq hξ1 hG1 hn1 hflex hA hyA
      hYm1)
    (prop66_bridge hM hP hPs hPΦ hPω hPθ hcbar huc hucc heff hgp hq hξ1 hG1 hn1 hflex hB hyB
      hYm1) hL

/-- Woodford (2003), §1, p. 385, and Prop. 6.1 (**expected utility over a finite state space**):
if in every state `ω` (probability `p ω`) the cross-section is a family with first-order solution
`y₁(ω)` and disturbances `ε ξ₁(ω)`, then
`E U(ε) = E tipState(ε ξ₁) − (ε²/2) Ȳu_c E L(y₁, ξ₁) + O(ε³)`; policies are ranked by the
expected first-order loss (`ranking_of_tip`). -/
theorem prop61_expected (hM : M.Std) (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0)
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) {yh : Ω → ℝ → ι → ℝ} {y1 : Ω → ι → ℝ} (ξ1 : Ω → Ξ)
    (h : ∀ ω, (fun ε => yh ω ε - ε • y1 ω) =O[𝓝 0] fun ε => ε ^ 2) :
    (fun ε => OneParamTaylor.expect p (fun ω => M.Ustate (yh ω ε) (ε • ξ1 ω)) -
      (OneParamTaylor.expect p (fun ω => M.tipState (ε • ξ1 ω)) + ε ^ 2 / 2 *
        (-(M.Yb * M.uc * OneParamTaylor.expect p (fun ω => M.lossB (y1 ω) (ξ1 ω))))))
      =O[𝓝 0] fun ε => ε ^ 3 :=
  expect_bridge p (W := fun ω ε => M.Ustate (yh ω ε) (ε • ξ1 ω))
    (T := fun ω ε => M.tipState (ε • ξ1 ω)) (L := fun ω => M.lossB (y1 ω) (ξ1 ω))
    fun ω => prop61_bridge hM heff hden (ξ1 ω) (h ω)

end Econ

end Woodford.StabilizationWelfare.BridgeCore
