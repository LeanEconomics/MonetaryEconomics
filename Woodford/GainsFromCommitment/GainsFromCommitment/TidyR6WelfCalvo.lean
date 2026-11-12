/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR6WelfBridge

/-!
# Welfare to `O(ε³)` for Chapter 7: the Calvo bridge uniform in the state

Woodford (2003), *Interest and Prices*, Chapter 7, §1.1, p. 471 (footnote 6: welfare is
decreasing in (1.2) "neglecting terms independent of policy and a residual of only third
order"), and the approximation qualifiers "up to an error of order `O(‖·‖²)`" of
Propositions 7.1–7.5 (pp. 471–487) and 7.15 (p. 523), which rest on the Chapter 6 welfare
approximation (Chapter 6, Propositions 6.4–6.5, pp. 400–402, and Appendix E.2–E.3).

This module supplies the tools that turn the Chapter 6 Layer-B bridge (restated in
TidyR6WelfBridge) into statements about the welfare rankings of Chapter 7.

## Main results

* **Ranking engine** (deterministic and uniform in a state space): `WeaklyBetter`
  (`W_B ≤ W_A + O(ε³)`), `weaklyBetter_of_loss_le`, `eventually_lt_of_loss_lt` (strictly
  better for every small `ε ≠ 0`), and the converse `loss_le_of_weaklyBetter`: a policy that is
  at least as good as another up to `O(ε³)` has a first-order loss no larger. The uniform
  versions `UWeaklyBetter`, `uweaklyBetter_of_loss_le`, `ueventually_lt_of_loss_lt`,
  `loss_le_of_uweaklyBetter` hold state by state with one constant for all states.
* **The Calvo bridge uniform in the state** (`calvo_bridge_unif`): Propositions 6.4–6.5 of
  Chapter 6 with every hypothesis uniform in the date AND the state, and the conclusion
  `∑βᵗU_t = TIP − (ε²/2)Ȳu_c·2Θ∑βᵗ(q₁_t² + (κ/θ)x₁_t²) + O(ε³)` with ONE constant for all
  states. `calvo_identity` is the exact identity along one path.
* **Expected welfare** (`SCalvoFamily.bridge`): for any `ExpectationSystem`, E_0 of the
  discounted utility of every path satisfies the same expansion uniformly in the date-`0` state.
* **`λ = κ/θ` derived** (`kap`, `lamW`, `lamW_eq`, `kap_pos`, `lamW_pos`): the weight on the
  output gap in the loss produced by the bridge is the Calvo slope `κ` of (2.19) divided by `θ`;
  it is not assumed.
-/

namespace Woodford.GainsFromCommitment.TidyR6WelfCalvo

open Filter Topology Asymptotics
open Woodford.GainsFromCommitment.TidyR6WelfBase Woodford.GainsFromCommitment.TidyR6WelfBridge

/-! ### The ranking engine -/

/-- Woodford (2003), p. 471, fn. 6 (**welfare ranking up to third order**): policy `A` is at
least as good as policy `B` up to `O(ε³)`, `W_B(ε) ≤ W_A(ε) + C|ε|³` for all small `ε`. -/
def WeaklyBetter (WA WB : ℝ → ℝ) : Prop := ∃ C, ∀ᶠ ε in 𝓝 (0 : ℝ), WB ε ≤ WA ε + C * |ε| ^ 3

/-- Woodford (2003), p. 471, fn. 6 (tool): unpacking a cubic remainder. -/
theorem cubic_bound {f : ℝ → ℝ} (h : f =O[𝓝 0] fun ε => ε ^ 3) :
    ∃ C, ∀ᶠ ε in 𝓝 (0 : ℝ), |f ε| ≤ C * |ε| ^ 3 := by
  obtain ⟨C, hC⟩ := h.bound
  exact ⟨C, hC.mono fun ε hε => by simpa [Real.norm_eq_abs, abs_pow] using hε⟩

/-- Woodford (2003), p. 471, fn. 6 and Ch. 6, §1, pp. 386–389: if `W_X = T − (ε²/2)k L_X + O(ε³)`
with the same policy-independent `T`, `k ≥ 0` and `L_A ≤ L_B`, then `A` is at least as good as
`B` up to `O(ε³)`. -/
theorem weaklyBetter_of_loss_le {WA WB T : ℝ → ℝ} {k LA LB : ℝ} (hk : 0 ≤ k)
    (hA : (fun ε => WA ε - (T ε - ε ^ 2 / 2 * (k * LA))) =O[𝓝 0] fun ε => ε ^ 3)
    (hB : (fun ε => WB ε - (T ε - ε ^ 2 / 2 * (k * LB))) =O[𝓝 0] fun ε => ε ^ 3)
    (hL : LA ≤ LB) : WeaklyBetter WA WB := by
  obtain ⟨C, hC⟩ := cubic_bound (hB.sub hA)
  refine ⟨C, hC.mono fun ε hε => ?_⟩
  have h1 := (abs_le.mp hε).2
  have h2 : 0 ≤ ε ^ 2 / 2 * k * (LB - LA) :=
    mul_nonneg (mul_nonneg (by positivity) hk) (by linarith)
  nlinarith

/-- Woodford (2003), Ch. 6, §1, pp. 386–389 (**strict ranking**): with `k > 0` and `L_A < L_B`,
`W_B(ε) < W_A(ε)` for every small `ε ≠ 0`. -/
theorem eventually_lt_of_loss_lt {WA WB T : ℝ → ℝ} {k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun ε => WA ε - (T ε - ε ^ 2 / 2 * (k * LA))) =O[𝓝 0] fun ε => ε ^ 3)
    (hB : (fun ε => WB ε - (T ε - ε ^ 2 / 2 * (k * LB))) =O[𝓝 0] fun ε => ε ^ 3)
    (hL : LA < LB) : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), WB ε < WA ε := by
  obtain ⟨C, hC⟩ := cubic_bound (hB.sub hA)
  set g := k * (LB - LA) / 2 with hg
  have hgpos : 0 < g := by rw [hg]; have := mul_pos hk (sub_pos.mpr hL); linarith
  have hball : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| * (|C| + 1) < g := by
    have hc : Tendsto (fun ε : ℝ => |ε| * (|C| + 1)) (𝓝 0) (𝓝 (|(0 : ℝ)| * (|C| + 1))) :=
      (continuous_abs.tendsto 0).mul_const _
    simp only [abs_zero, zero_mul] at hc
    exact hc.eventually (gt_mem_nhds hgpos)
  filter_upwards [nhdsWithin_le_nhds hC, nhdsWithin_le_nhds hball, self_mem_nhdsWithin]
    with ε hε hb hne
  have hε0 : 0 < |ε| := abs_pos.mpr hne
  have h1 := (abs_le.mp hε).2
  have hsq : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
  have hcube : C * |ε| ^ 3 < g * |ε| ^ 2 := by
    have : |ε| ^ 2 * (|ε| * (|C| + 1)) < |ε| ^ 2 * g :=
      mul_lt_mul_of_pos_left hb (by positivity)
    nlinarith [le_abs_self C, abs_nonneg C, sq_nonneg ε, pow_pos hε0 2, pow_pos hε0 3]
  have : WB ε - WA ε ≤ C * |ε| ^ 3 - g * ε ^ 2 := by rw [hg]; nlinarith
  rw [hsq] at this
  linarith

/-- Woodford (2003), Propositions 7.1–7.5 and 7.15 ("up to an error of order `O(‖·‖²)`", the
**converse**): if `A` is at least as good as `B` up to `O(ε³)` and both have Layer-B
expansions with the same `T` and `k > 0`, then `L_A ≤ L_B`. -/
theorem loss_le_of_weaklyBetter {WA WB T : ℝ → ℝ} {k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun ε => WA ε - (T ε - ε ^ 2 / 2 * (k * LA))) =O[𝓝 0] fun ε => ε ^ 3)
    (hB : (fun ε => WB ε - (T ε - ε ^ 2 / 2 * (k * LB))) =O[𝓝 0] fun ε => ε ^ 3)
    (h : WeaklyBetter WA WB) : LA ≤ LB := by
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hC⟩ := h
  obtain ⟨D, hD⟩ := cubic_bound (hA.sub hB)
  set g := k * (LA - LB) / 2 with hg
  have hgpos : 0 < g := by rw [hg]; have := mul_pos hk (sub_pos.mpr hlt); linarith
  have hball : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| * (|C| + |D| + 1) < g := by
    have hc : Tendsto (fun ε : ℝ => |ε| * (|C| + |D| + 1)) (𝓝 0)
        (𝓝 (|(0 : ℝ)| * (|C| + |D| + 1))) := (continuous_abs.tendsto 0).mul_const _
    simp only [abs_zero, zero_mul] at hc
    exact hc.eventually (gt_mem_nhds hgpos)
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), False := by
    filter_upwards [nhdsWithin_le_nhds hC, nhdsWithin_le_nhds hD, nhdsWithin_le_nhds hball,
      self_mem_nhdsWithin] with ε h1 h2 hb hne
    have hε0 : 0 < |ε| := abs_pos.mpr hne
    have h3 := (abs_le.mp h2).2
    have hsq : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
    have hkey : g * |ε| ^ 2 ≤ (C + D) * |ε| ^ 3 := by
      have : WA ε - WB ε - ε ^ 2 / 2 * (k * (LB - LA)) ≤ D * |ε| ^ 3 := by nlinarith
      rw [hg]; nlinarith
    have : |ε| ^ 2 * (|ε| * (|C| + |D| + 1)) < |ε| ^ 2 * g :=
      mul_lt_mul_of_pos_left hb (by positivity)
    nlinarith [le_abs_self C, le_abs_self D, abs_nonneg C, abs_nonneg D, pow_pos hε0 3]
  have hne : (𝓝[≠] (0 : ℝ)).NeBot := inferInstance
  exact (hev.exists).elim fun _ h => h

/-! ### The ranking engine uniformly in a state space -/

/-- Woodford (2003), p. 471, fn. 6, under uncertainty: `A` is at least as good as `B` up to
`O(ε³)` in every state `ω` (conditional on date-`t₀` information), with one constant `C` for all
states: `W_B(ε, ω) ≤ W_A(ε, ω) + C|ε|³`. -/
def UWeaklyBetter {Ω : Type*} (WA WB : ℝ → Ω → ℝ) : Prop :=
  ∃ C, ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ ω, WB ε ω ≤ WA ε ω + C * |ε| ^ 3

/-- Woodford (2003), App. E.2, p. 695 (uniformity in the state): a family of functions of `ε`
is `O(ε³)` with one constant for all states. -/
def UCubic {Ω : Type*} (f : ℝ → Ω → ℝ) : Prop :=
  ∃ C, ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ ω, |f ε ω| ≤ C * |ε| ^ 3

/-- Woodford (2003), p. 471, fn. 6, under uncertainty: the uniform version of
`weaklyBetter_of_loss_le`, state by state. -/
theorem uweaklyBetter_of_loss_le {Ω : Type*} {WA WB T : ℝ → Ω → ℝ} {k : ℝ} {LA LB : Ω → ℝ}
    (hk : 0 ≤ k) (hA : UCubic fun ε ω => WA ε ω - (T ε ω - ε ^ 2 / 2 * (k * LA ω)))
    (hB : UCubic fun ε ω => WB ε ω - (T ε ω - ε ^ 2 / 2 * (k * LB ω)))
    (hL : ∀ ω, LA ω ≤ LB ω) : UWeaklyBetter WA WB := by
  obtain ⟨C1, h1⟩ := hA
  obtain ⟨C2, h2⟩ := hB
  refine ⟨C1 + C2, (h1.and h2).mono fun ε ⟨e1, e2⟩ ω => ?_⟩
  have a1 := (abs_le.mp (e1 ω)).1
  have a2 := (abs_le.mp (e2 ω)).2
  have h3 : 0 ≤ ε ^ 2 / 2 * k * (LB ω - LA ω) :=
    mul_nonneg (mul_nonneg (by positivity) hk) (by linarith [hL ω])
  nlinarith

/-- Woodford (2003), Ch. 6, §1, under uncertainty (**strict ranking in a given state**): if
`L_A(ω) < L_B(ω)` then `W_B(ε, ω) < W_A(ε, ω)` for every small `ε ≠ 0`. -/
theorem ueventually_lt_of_loss_lt {Ω : Type*} {WA WB T : ℝ → Ω → ℝ} {k : ℝ} {LA LB : Ω → ℝ}
    (hk : 0 < k) (hA : UCubic fun ε ω => WA ε ω - (T ε ω - ε ^ 2 / 2 * (k * LA ω)))
    (hB : UCubic fun ε ω => WB ε ω - (T ε ω - ε ^ 2 / 2 * (k * LB ω))) (ω : Ω)
    (hL : LA ω < LB ω) : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), WB ε ω < WA ε ω := by
  obtain ⟨C1, h1⟩ := hA
  obtain ⟨C2, h2⟩ := hB
  have hA' : (fun ε => WA ε ω - (T ε ω - ε ^ 2 / 2 * (k * LA ω))) =O[𝓝 0] fun ε => ε ^ 3 :=
    IsBigO.of_bound C1 (h1.mono fun ε h => by simpa [Real.norm_eq_abs, abs_pow] using h ω)
  have hB' : (fun ε => WB ε ω - (T ε ω - ε ^ 2 / 2 * (k * LB ω))) =O[𝓝 0] fun ε => ε ^ 3 :=
    IsBigO.of_bound C2 (h2.mono fun ε h => by simpa [Real.norm_eq_abs, abs_pow] using h ω)
  exact eventually_lt_of_loss_lt (T := fun ε => T ε ω) hk hA' hB' hL

/-- Woodford (2003), Propositions 7.5 and 7.15 under uncertainty (the **converse**, state by
state): if `A` is at least as good as `B` up to `O(ε³)` uniformly in the state, then
`L_A ≤ L_B` in every state. -/
theorem loss_le_of_uweaklyBetter {Ω : Type*} {WA WB T : ℝ → Ω → ℝ} {k : ℝ} {LA LB : Ω → ℝ}
    (hk : 0 < k) (hA : UCubic fun ε ω => WA ε ω - (T ε ω - ε ^ 2 / 2 * (k * LA ω)))
    (hB : UCubic fun ε ω => WB ε ω - (T ε ω - ε ^ 2 / 2 * (k * LB ω)))
    (h : UWeaklyBetter WA WB) (ω : Ω) : LA ω ≤ LB ω := by
  obtain ⟨C1, h1⟩ := hA
  obtain ⟨C2, h2⟩ := hB
  obtain ⟨C, hC⟩ := h
  have hA' : (fun ε => WA ε ω - (T ε ω - ε ^ 2 / 2 * (k * LA ω))) =O[𝓝 0] fun ε => ε ^ 3 :=
    IsBigO.of_bound C1 (h1.mono fun ε h => by simpa [Real.norm_eq_abs, abs_pow] using h ω)
  have hB' : (fun ε => WB ε ω - (T ε ω - ε ^ 2 / 2 * (k * LB ω))) =O[𝓝 0] fun ε => ε ^ 3 :=
    IsBigO.of_bound C2 (h2.mono fun ε h => by simpa [Real.norm_eq_abs, abs_pow] using h ω)
  exact loss_le_of_weaklyBetter (T := fun ε => T ε ω) hk hA' hB' ⟨C, hC.mono fun ε h => h ω⟩

/-! ### The Calvo bridge uniformly in the date and the state -/

/-- Woodford (2003), App. E.2, p. 695, under uncertainty: the filter "uniformly in the state
`j` and the date `t`, as the amplitude `ε → 0`", `⊤ ×ˢ 𝓝 0` on `(J × ℕ) × ℝ`. -/
abbrev uF (J : Type*) : Filter ((J × ℕ) × ℝ) := (⊤ : Filter (J × ℕ)) ×ˢ 𝓝 (0 : ℝ)

/-- Woodford (2003), App. E.2, p. 695: the amplitude tends to zero along `uF J`. -/
theorem tendsto_uF (J : Type*) : Tendsto (fun p : (J × ℕ) × ℝ => p.2) (uF J) (𝓝 0) :=
  tendsto_snd

/-- Woodford (2003), App. E.2, p. 695 (**what uniformity in the state and the date says**):
`f =O[uF J] g` iff one constant `C` gives `‖f j t ε‖ ≤ C‖g ε‖` for all `j`, `t` and small `ε`. -/
theorem isBigO_uF_iff {J E : Type*} [Norm E] {f : J → ℕ → ℝ → E} {g : ℝ → ℝ} :
    (fun p : (J × ℕ) × ℝ => f p.1.1 p.1.2 p.2) =O[uF J] (fun p => g p.2) ↔
      ∃ C, ∀ᶠ ε in 𝓝 0, ∀ j t, ‖f j t ε‖ ≤ C * ‖g ε‖ := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h.bound
    refine ⟨C, ?_⟩
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 hC
    rw [eventually_top] at hpa
    filter_upwards [hpb] with ε hε j t
    exact hab (hpa (j, t)) hε
  · rintro ⟨C, hC⟩
    exact IsBigO.of_bound C ((hC.prod_inr _).mono fun p hp => hp p.1.1 p.1.2)

/-- Woodford (2003), App. E.3, p. 697, under uncertainty: a family bounded by one constant for
all states and dates is `O(1)` along `uF J`. -/
theorem uF_of_bounded {J E : Type*} [Norm E] {f : J → ℕ → E} (hf : ∃ C, ∀ j t, ‖f j t‖ ≤ C) :
    (fun p : (J × ℕ) × ℝ => f p.1.1 p.1.2) =O[uF J] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC⟩ := hf
  exact IsBigO.of_bound C (Eventually.of_forall fun p => by simpa using hC p.1.1 p.1.2)

/-- Woodford (2003), (2.21), p. 400, under uncertainty (**discounted sums of remainders uniform in
the state**): if `f j t ε = O(εⁿ)` uniformly in `j`, `t`, then for all small `ε` and every `j`,
`|∑ βᵗ f j t ε| ≤ C|ε|ⁿ`. -/
theorem tsum_bound_uF {J : Type*} {f : J → ℕ → ℝ → ℝ} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {n : ℕ} (hf : (fun p : (J × ℕ) × ℝ => f p.1.1 p.1.2 p.2) =O[uF J] (fun p => p.2 ^ n)) :
    ∃ C, ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ j, |∑' t, β ^ t * f j t ε| ≤ C * |ε| ^ n := by
  obtain ⟨C, hC⟩ := (isBigO_uF_iff (g := fun ε => ε ^ n)).1 hf
  refine ⟨C / (1 - β), hC.mono fun ε hε j => ?_⟩
  have h := SeqW.abs_tsum_le (f := fun t => f j t ε) (B := C * ‖ε ^ n‖)
    (fun t => by simpa [Real.norm_eq_abs] using hε j t) hβ0 hβ1
  rw [Real.norm_eq_abs, abs_pow] at h
  calc _ ≤ C * |ε| ^ n / (1 - β) := h
    _ = C / (1 - β) * |ε| ^ n := by ring

/-- Woodford (2003), App. E.3, p. 697, under uncertainty: a family that is `O(1)` uniformly in
`j`, `t` is, for all small `ε`, bounded by one constant for every `j` and `t`. -/
theorem bdd_uF {J : Type*} {f : J → ℕ → ℝ → ℝ}
    (hf : (fun p : (J × ℕ) × ℝ => f p.1.1 p.1.2 p.2) =O[uF J] (fun _ => (1 : ℝ))) :
    ∃ C, ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ j t, |f j t ε| ≤ C := by
  obtain ⟨C, hC⟩ := (isBigO_uF_iff (g := fun _ => (1 : ℝ))).1 hf
  exact ⟨C, hC.mono fun ε hε j t => by simpa using hε j t⟩

/-- Woodford (2003), App. E.2, p. 695: `εᵏ = O(1)` along `uF J`. -/
theorem pow_uF_one (J : Type*) (k : ℕ) :
    (fun p : (J × ℕ) × ℝ => p.2 ^ k) =O[uF J] fun _ => (1 : ℝ) :=
  (((tendsto_uF J).isBigO_one ℝ).pow k).congr_right fun _ => one_pow k

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Woodford (2003), (2.10)/(E.1), under uncertainty: the t.i.p. along `ε ξ₁` is bounded uniformly
in the state and the date for disturbances `ξ₁` bounded uniformly in both. -/
theorem tipState_uF (M : BridgeCore.Econ Ξ ι) {J : Type*} {ξ1 : J → ℕ → Ξ}
    (hξ1 : ∃ C, ∀ j t, ‖ξ1 j t‖ ≤ C) :
    (fun p : (J × ℕ) × ℝ => M.tipState (p.2 • ξ1 p.1.1 p.1.2)) =O[uF J]
      fun _ => (1 : ℝ) := by
  have hx := uF_of_bounded hξ1
  have he : (fun p : (J × ℕ) × ℝ => p.2) =O[uF J] fun _ => (1 : ℝ) :=
    (tendsto_uF J).isBigO_one ℝ
  have h1 : (fun p : (J × ℕ) × ℝ => BridgeCore.lin M.u M.Yb (ξ1 p.1.1 p.1.2) -
      BridgeCore.lin M.v M.Yb (ξ1 p.1.1 p.1.2)) =O[uF J] fun _ => (1 : ℝ) :=
    (BridgeCore.lin_isBigO M.u M.Yb hx).sub (BridgeCore.lin_isBigO M.v M.Yb hx)
  have hq1 := (BridgeCore.quad_isBigO M.u M.Yb hx).congr_right fun _ => one_pow 2
  have hq2 := (BridgeCore.quad_isBigO M.v M.Yb hx).congr_right fun _ => one_pow 2
  have hN := BridgeCore.natLin_isBigO M.sig M.omg (M.gS_isBigO hx) (M.qS_isBigO hx)
  have hA : (fun p : (J × ℕ) × ℝ => Prop61.tipA M.sig M.omg (M.gS (ξ1 p.1.1 p.1.2))
      (M.qS (ξ1 p.1.1 p.1.2)) 0) =O[uF J] fun _ => (1 : ℝ) :=
    (((hN.add (isBigO_const_const (Prop61.xStarLin M.sig M.omg 0) one_ne_zero
      (uF J))).pow 2).const_mul_left ((M.sig + M.omg) / 2)).congr
        (fun p => by unfold Prop61.tipA; ring) (fun p => one_pow 2)
  have h2 : (fun p : (J × ℕ) × ℝ => BridgeCore.quad M.u M.Yb (ξ1 p.1.1 p.1.2) / 2 -
      BridgeCore.quad M.v M.Yb (ξ1 p.1.1 p.1.2) / 2 + M.Yb * M.uc *
        Prop61.tipA M.sig M.omg (M.gS (ξ1 p.1.1 p.1.2)) (M.qS (ξ1 p.1.1 p.1.2)) 0) =O[uF J]
      fun _ => (1 : ℝ) :=
    (((hq1.const_mul_left (1 / 2)).sub (hq2.const_mul_left (1 / 2))).add
      (hA.const_mul_left (M.Yb * M.uc))).congr_left fun p => by ring
  have t1 : (fun p : (J × ℕ) × ℝ => p.2 * (BridgeCore.lin M.u M.Yb (ξ1 p.1.1 p.1.2) -
      BridgeCore.lin M.v M.Yb (ξ1 p.1.1 p.1.2))) =O[uF J] fun _ => (1 : ℝ) :=
    (he.mul h1).congr_right fun _ => mul_one 1
  have t2 : (fun p : (J × ℕ) × ℝ => p.2 ^ 2 * (BridgeCore.quad M.u M.Yb (ξ1 p.1.1 p.1.2) / 2 -
      BridgeCore.quad M.v M.Yb (ξ1 p.1.1 p.1.2) / 2 + M.Yb * M.uc *
        Prop61.tipA M.sig M.omg (M.gS (ξ1 p.1.1 p.1.2)) (M.qS (ξ1 p.1.1 p.1.2)) 0)) =O[uF J]
      fun _ => (1 : ℝ) := ((he.pow 2).mul h2).congr_right fun _ => by ring
  refine (((isBigO_const_const (M.tipState 0) one_ne_zero (uF J)).add t1).add t2).congr_left
    fun p => ?_
  rw [BridgeCore.Econ.tipState_smul]

/-- Woodford (2003), **Propositions 6.4–6.5, (2.21)–(2.25), pp. 400–402, along ONE path (the
exact identity)**: if `var_i ŷ_t = θ²Δ_t` and `Δ_t = αΔ_{t−1} + α/(1 − α)q_t² + R_t`, and the
sequences `q`, the gap, `R`, the t.i.p. and the remainder `ρ_t = U_t − (tip_t − (Ȳu_c/2)L_t)`
of Proposition 6.1 are bounded, then `∑βᵗU_t = ∑βᵗtip_t − Ȳu_c·θ(1 + ωθ)/2·αΔ_{−1}/(1 − αβ)
− Ȳu_cΘ∑βᵗ(q_t² + (κ/θ)x_t²) + ∑βᵗρ_t − Ȳu_c·θ(1 + ωθ)/(2(1 − αβ))∑βᵗR_t`, all sums genuine.
(The algebra of the Chapter 6 project's `BridgeCore.Econ.calvo_bridge`, isolated.) -/
theorem calvo_identity (M : BridgeCore.Econ Ξ ι) (hM : M.Std) (hθ : M.θ ≠ 0)
    (hd : 1 + M.omg * M.θ ≠ 0) {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {yh : ℕ → ι → ℝ} {ξ : ℕ → Ξ} {D qd R : ℕ → ℝ} {B : ℝ}
    (hdem : ∀ t, ExpLogCES.crossVar M.w (yh t) = M.θ ^ 2 * D (t + 1))
    (hrec : ∀ t, D (t + 1) = α * D t + α / (1 - α) * qd t ^ 2 + R t)
    (hqb : ∀ t, |qd t| ≤ B) (hXb : ∀ t, |M.gap (yh t) (ξ t)| ≤ B) (hRb : ∀ t, |R t| ≤ B)
    (hTb : ∀ t, |M.tipState (ξ t)| ≤ B)
    (hρb : ∀ t, |M.Ustate (yh t) (ξ t) -
      (M.tipState (ξ t) - M.Yb * M.uc / 2 * M.lossB (yh t) (ξ t))| ≤ B) :
    ∑' t, β ^ t * M.Ustate (yh t) (ξ t) =
      ∑' t, β ^ t * M.tipState (ξ t) -
        M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * D 0 / (1 - α * β))) -
        M.Yb * M.uc * PriceDispersion.ThetaCalvo α β M.θ M.omg *
          ∑' t, β ^ t * (qd t ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
            M.gap (yh t) (ξ t) ^ 2) +
        ∑' t, β ^ t * (M.Ustate (yh t) (ξ t) -
          (M.tipState (ξ t) - M.Yb * M.uc / 2 * M.lossB (yh t) (ξ t))) -
        M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 / (1 - α * β)) * ∑' t, β ^ t * R t := by
  have hYb0 : M.Yb ≠ 0 := hM.Yb_pos.ne'
  have huc0 : M.uc ≠ 0 := hM.uc_pos.ne'
  have hYb : 0 < M.Yb * M.uc := mul_pos hM.Yb_pos hM.uc_pos
  have hT' : ∀ t, |M.tipState (ξ t) / (M.Yb * M.uc)| ≤ B / (M.Yb * M.uc) := fun t => by
    rw [abs_div, abs_of_pos hYb]; exact div_le_div_of_nonneg_right (hTb t) hYb.le
  have hρ' : ∀ t, |(M.Ustate (yh t) (ξ t) - (M.tipState (ξ t) - M.Yb * M.uc / 2 *
      M.lossB (yh t) (ξ t))) / (M.Yb * M.uc)| ≤ B / (M.Yb * M.uc) := fun t => by
    rw [abs_div, abs_of_pos hYb]; exact div_le_div_of_nonneg_right (hρb t) hYb.le
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hqb 0)
  set B' := B + B / (M.Yb * M.uc) with hB'
  have hBB : B ≤ B' := by rw [hB']; have := div_nonneg hB0 hYb.le; linarith
  have hBB' : B / (M.Yb * M.uc) ≤ B' := by rw [hB']; linarith
  have hW : ∀ t, M.Ustate (yh t) (ξ t) / (M.Yb * M.uc) = -(1 / 2) * ((M.sig + M.omg) *
      M.gap (yh t) (ξ t) ^ 2 + M.θ * (1 + M.omg * M.θ) * D (t + 1)) +
      M.tipState (ξ t) / (M.Yb * M.uc) + (M.Ustate (yh t) (ξ t) -
        (M.tipState (ξ t) - M.Yb * M.uc / 2 * M.lossB (yh t) (ξ t))) / (M.Yb * M.uc) :=
    fun t => by
    have hl : M.lossB (yh t) (ξ t) = (M.sig + M.omg) * M.gap (yh t) (ξ t) ^ 2 +
        M.θ * (1 + M.omg * M.θ) * D (t + 1) := by
      unfold BridgeCore.Econ.lossB
      rw [hdem, Prop61.lossQ_disp hθ]
      rfl
    rw [hl]
    field_simp
    ring
  have hV := PriceDispersion.calvo_welfare_sum (M := B') hα0 hα1 hβ0 hβ1 hθ hd hrec hW
    (fun t => (hqb t).trans hBB) (fun t => (hXb t).trans hBB) (fun t => (hRb t).trans hBB)
    (fun t => (hT' t).trans hBB') (fun t => (hρ' t).trans hBB')
  have e1 : ∑' t, β ^ t * M.Ustate (yh t) (ξ t) =
      M.Yb * M.uc * ∑' t, β ^ t * (M.Ustate (yh t) (ξ t) / (M.Yb * M.uc)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by field_simp
  have e2 : M.Yb * M.uc * ∑' t, β ^ t * (M.tipState (ξ t) / (M.Yb * M.uc)) =
      ∑' t, β ^ t * M.tipState (ξ t) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by field_simp
  have e3 : M.Yb * M.uc * ∑' t, β ^ t * ((M.Ustate (yh t) (ξ t) -
      (M.tipState (ξ t) - M.Yb * M.uc / 2 * M.lossB (yh t) (ξ t))) / (M.Yb * M.uc)) =
      ∑' t, β ^ t * (M.Ustate (yh t) (ξ t) -
        (M.tipState (ξ t) - M.Yb * M.uc / 2 * M.lossB (yh t) (ξ t))) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun t => by field_simp
  rw [e1, hV.tsum_eq]
  linear_combination e2 + e3

set_option maxHeartbeats 1600000 in
-- many uniform `IsBigO` estimates are combined in one proof
/-- Woodford (2003), **Propositions 6.4–6.5, (2.21)–(2.25), pp. 400–402, uniformly in the
state** (the Layer-B bridge of Chapter 6 under uncertainty): for a family of paths indexed by
states `j` (the realised histories), with the cross-section `ŷ(ε)`, the disturbances `ε ξ₁` and
the dispersion recursion as in the Chapter 6 project's `BridgeCore.Econ.calvo_bridge` and every
order hypothesis UNIFORM in the state and the date, the discounted utility of every path
satisfies `∑βᵗU_t = TIP − (ε²/2)Ȳu_c·2Θ∑βᵗ(q₁_t² + (κ/θ)x₁_t²) + O(ε³)` with ONE constant for
all states (`UCubic`), `κ` the Calvo slope (2.19). -/
theorem calvo_bridge_unif (M : BridgeCore.Econ Ξ ι) (hM : M.Std) (heff : M.vy = M.uc)
    (hden : M.sig + M.omg ≠ 0) (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0) {α β : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {J : Type*}
    {yh : J → ℕ → ℝ → ι → ℝ} {y1 : J → ℕ → ι → ℝ} {ξ1 : J → ℕ → Ξ}
    (h : (fun p : (J × ℕ) × ℝ => yh p.1.1 p.1.2 p.2 - p.2 • y1 p.1.1 p.1.2) =O[uF J]
      fun p => p.2 ^ 2)
    (hy1 : ∃ C, ∀ j t, ‖y1 j t‖ ≤ C) (hξ1 : ∃ C, ∀ j t, ‖ξ1 j t‖ ≤ C)
    {D qd R : J → ℝ → ℕ → ℝ} {q1 : J → ℕ → ℝ}
    (hdem : ∀ j ε t, ExpLogCES.crossVar M.w (yh j t ε) = M.θ ^ 2 * D j ε (t + 1))
    (hrec : ∀ j ε t, D j ε (t + 1) = α * D j ε t + α / (1 - α) * qd j ε t ^ 2 + R j ε t)
    (hq : (fun p : (J × ℕ) × ℝ => qd p.1.1 p.2 p.1.2 - p.2 * q1 p.1.1 p.1.2) =O[uF J]
      fun p => p.2 ^ 2)
    (hq1 : ∃ C, ∀ j t, |q1 j t| ≤ C)
    (hR : (fun p : (J × ℕ) × ℝ => R p.1.1 p.2 p.1.2) =O[uF J] fun p => p.2 ^ 3) :
    UCubic fun ε j => ∑' t, β ^ t * M.Ustate (yh j t ε) (ε • ξ1 j t) -
      ((∑' t, β ^ t * M.tipState (ε • ξ1 j t) -
          M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * D j ε 0 / (1 - α * β)))) -
        ε ^ 2 / 2 * (M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg) *
          ∑' t, β ^ t * (q1 j t ^ 2 + Moments.calvoKappa α β M.omg M.θ M.sig / M.θ *
            M.gap (y1 j t) (ξ1 j t) ^ 2))) := by
  have hs := tendsto_uF J
  set kk := Moments.calvoKappa α β M.omg M.θ M.sig / M.θ with hkk
  set Th := PriceDispersion.ThetaCalvo α β M.θ M.omg with hTh
  set c3 := M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 / (1 - α * β)) with hc3
  have hyu : (fun p : (J × ℕ) × ℝ => yh p.1.1 p.1.2 p.2) =O[uF J] fun p => p.2 :=
    BridgeCore.family_isBigO (s := fun p : (J × ℕ) × ℝ => p.2) hs h (uF_of_bounded hy1)
  have hx1 : (fun p : (J × ℕ) × ℝ => ξ1 p.1.1 p.1.2) =O[uF J] fun _ => (1 : ℝ) :=
    uF_of_bounded hξ1
  have hξu : (fun p : (J × ℕ) × ℝ => p.2 • ξ1 p.1.1 p.1.2) =O[uF J] fun p => p.2 :=
    ((isBigO_refl (fun p : (J × ℕ) × ℝ => p.2) (uF J)).smul hx1).congr_right
      fun _ => mul_one _
  have hρ := BridgeCore.Econ.prop61_state_poly (l := uF J) (s := fun p : (J × ℕ) × ℝ => p.2)
    (yh := fun p : (J × ℕ) × ℝ => yh p.1.1 p.1.2 p.2)
    (ξ := fun p : (J × ℕ) × ℝ => p.2 • ξ1 p.1.1 p.1.2) hM heff hden hs hyu hξu
  have hX1 : (fun p : (J × ℕ) × ℝ => M.gap (y1 p.1.1 p.1.2) (ξ1 p.1.1 p.1.2)) =O[uF J]
      fun _ => (1 : ℝ) :=
    (BridgeCore.crossMean_isBigO hM.w_nonneg hM.w_sum (uF_of_bounded hy1)).sub
      (BridgeCore.natLin_isBigO M.sig M.omg (M.gS_isBigO hx1) (M.qS_isBigO hx1))
  have hXd : (fun p : (J × ℕ) × ℝ => M.gap (yh p.1.1 p.1.2 p.2) (p.2 • ξ1 p.1.1 p.1.2) -
      p.2 * M.gap (y1 p.1.1 p.1.2) (ξ1 p.1.1 p.1.2)) =O[uF J] fun p => p.2 ^ 2 :=
    (BridgeCore.crossMean_isBigO hM.w_nonneg hM.w_sum h).congr_left
      fun p => (BridgeCore.Econ.gap_smul_sub _ _ _ _).symm
  have hX2 := BridgeCore.sq_sub_sq_isBigO hs hXd hX1
  have hq1u : (fun p : (J × ℕ) × ℝ => q1 p.1.1 p.1.2) =O[uF J] fun _ => (1 : ℝ) := by
    obtain ⟨C, hC⟩ := hq1
    exact uF_of_bounded ⟨C, fun j t => by simpa using hC j t⟩
  have hq2 := BridgeCore.sq_sub_sq_isBigO hs hq hq1u
  have hcomb := hq2.add (hX2.const_mul_left kk)
  obtain ⟨C1, S1⟩ := tsum_bound_uF (f := fun j t ε => (qd j ε t ^ 2 - ε ^ 2 * q1 j t ^ 2) +
    kk * (M.gap (yh j t ε) (ε • ξ1 j t) ^ 2 - ε ^ 2 * M.gap (y1 j t) (ξ1 j t) ^ 2))
    hβ0 hβ1 hcomb
  obtain ⟨C2, S2⟩ := tsum_bound_uF (f := fun j t ε => M.Ustate (yh j t ε) (ε • ξ1 j t) -
    (M.tipState (ε • ξ1 j t) - M.Yb * M.uc / 2 * M.lossB (yh j t ε) (ε • ξ1 j t))) hβ0 hβ1 hρ
  obtain ⟨C3, S3⟩ := tsum_bound_uF (f := fun j t ε => R j ε t) hβ0 hβ1 hR
  -- boundedness for small `ε`, uniformly in the state
  have one : (fun p : (J × ℕ) × ℝ => p.2) =O[uF J] fun _ => (1 : ℝ) :=
    hs.isBigO_one ℝ
  obtain ⟨K1, bq⟩ := bdd_uF (f := fun j t ε => qd j ε t)
    (((hq.trans (pow_uF_one J 2)).add ((one.mul hq1u).congr_right fun _ => mul_one 1)).congr_left
      fun p => by ring)
  obtain ⟨K2, bX⟩ := bdd_uF (f := fun j t ε => M.gap (yh j t ε) (ε • ξ1 j t))
    (((hXd.trans (pow_uF_one J 2)).add ((one.mul hX1).congr_right fun _ => mul_one 1)).congr_left
      fun p => by ring)
  obtain ⟨K3, bR⟩ := bdd_uF (f := fun j t ε => R j ε t) (hR.trans (pow_uF_one J 3))
  obtain ⟨K4, bT⟩ := bdd_uF (f := fun j t ε => M.tipState (ε • ξ1 j t)) (tipState_uF M hξ1)
  obtain ⟨K5, bρ⟩ := bdd_uF (f := fun j t ε => M.Ustate (yh j t ε) (ε • ξ1 j t) -
    (M.tipState (ε • ξ1 j t) - M.Yb * M.uc / 2 * M.lossB (yh j t ε) (ε • ξ1 j t)))
    (hρ.trans (pow_uF_one J 3))
  obtain ⟨K6, hBq1⟩ := hq1
  obtain ⟨K7, bX1⟩ := bdd_uF (f := fun j t (_ : ℝ) => M.gap (y1 j t) (ξ1 j t)) hX1
  obtain ⟨ε0, hε0⟩ := bX1.exists
  refine ⟨C2 + |c3| * C3 + |M.Yb * M.uc * Th| * C1, ?_⟩
  filter_upwards [S1, S2, S3, bq, bX, bR, bT, bρ] with ε s1 s2 s3 hb1 hb2 hb3 hb4 hb5 j
  have n1 := abs_nonneg K1
  have n2 := abs_nonneg K2
  have n3 := abs_nonneg K3
  have n4 := abs_nonneg K4
  have n5 := abs_nonneg K5
  have l1 : K1 ≤ |K1| + |K2| + |K3| + |K4| + |K5| := by linarith [le_abs_self K1]
  have l2 : K2 ≤ |K1| + |K2| + |K3| + |K4| + |K5| := by linarith [le_abs_self K2]
  have l3 : K3 ≤ |K1| + |K2| + |K3| + |K4| + |K5| := by linarith [le_abs_self K3]
  have l4 : K4 ≤ |K1| + |K2| + |K3| + |K4| + |K5| := by linarith [le_abs_self K4]
  have l5 : K5 ≤ |K1| + |K2| + |K3| + |K4| + |K5| := by linarith [le_abs_self K5]
  have hid := calvo_identity M hM hθ hd hα0 hα1 hβ0 hβ1 (yh := fun t => yh j t ε)
    (ξ := fun t => ε • ξ1 j t) (D := D j ε) (qd := qd j ε) (R := R j ε)
    (B := |K1| + |K2| + |K3| + |K4| + |K5|) (fun t => hdem j ε t) (fun t => hrec j ε t)
    (fun t => (hb1 j t).trans l1) (fun t => (hb2 j t).trans l2) (fun t => (hb3 j t).trans l3)
    (fun t => (hb4 j t).trans l4) (fun t => (hb5 j t).trans l5)
  have hA : SeqW.Bdd (fun t => qd j ε t ^ 2 + kk * M.gap (yh j t ε) (ε • ξ1 j t) ^ 2) :=
    ⟨K1 ^ 2 + |kk| * K2 ^ 2, fun t => by
      have a1 : qd j ε t ^ 2 ≤ K1 ^ 2 := sq_le_sq' (abs_le.mp (hb1 j t)).1 (abs_le.mp (hb1 j t)).2
      have a2 : M.gap (yh j t ε) (ε • ξ1 j t) ^ 2 ≤ K2 ^ 2 :=
        sq_le_sq' (abs_le.mp (hb2 j t)).1 (abs_le.mp (hb2 j t)).2
      rw [abs_le]
      constructor <;> nlinarith [abs_nonneg kk, neg_abs_le kk, le_abs_self kk,
        sq_nonneg (qd j ε t), sq_nonneg (M.gap (yh j t ε) (ε • ξ1 j t))]⟩
  have hB : SeqW.Bdd (fun t => q1 j t ^ 2 + kk * M.gap (y1 j t) (ξ1 j t) ^ 2) :=
    ⟨K6 ^ 2 + |kk| * K7 ^ 2, fun t => by
      have a1 : q1 j t ^ 2 ≤ K6 ^ 2 := sq_le_sq' (abs_le.mp (hBq1 j t)).1 (abs_le.mp (hBq1 j t)).2
      have a2 : M.gap (y1 j t) (ξ1 j t) ^ 2 ≤ K7 ^ 2 :=
        sq_le_sq' (abs_le.mp (hε0 j t)).1 (abs_le.mp (hε0 j t)).2
      rw [abs_le]
      constructor <;> nlinarith [abs_nonneg kk, neg_abs_le kk, le_abs_self kk,
        sq_nonneg (q1 j t), sq_nonneg (M.gap (y1 j t) (ξ1 j t))]⟩
  have e4 : ∑' t, β ^ t * ((qd j ε t ^ 2 - ε ^ 2 * q1 j t ^ 2) +
      kk * (M.gap (yh j t ε) (ε • ξ1 j t) ^ 2 - ε ^ 2 * M.gap (y1 j t) (ξ1 j t) ^ 2)) =
      ∑' t, β ^ t * (qd j ε t ^ 2 + kk * M.gap (yh j t ε) (ε • ξ1 j t) ^ 2) -
        ε ^ 2 * ∑' t, β ^ t * (q1 j t ^ 2 + kk * M.gap (y1 j t) (ξ1 j t) ^ 2) := by
    rw [← tsum_mul_left, ← (hA.summable hβ0 hβ1).tsum_sub ((hB.summable hβ0 hβ1).mul_left _)]
    exact tsum_congr fun t => by ring
  have key : ∑' t, β ^ t * M.Ustate (yh j t ε) (ε • ξ1 j t) -
      ((∑' t, β ^ t * M.tipState (ε • ξ1 j t) -
          M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * D j ε 0 / (1 - α * β)))) -
        ε ^ 2 / 2 * (M.Yb * M.uc * (2 * Th) *
          ∑' t, β ^ t * (q1 j t ^ 2 + kk * M.gap (y1 j t) (ξ1 j t) ^ 2))) =
      ∑' t, β ^ t * (M.Ustate (yh j t ε) (ε • ξ1 j t) -
          (M.tipState (ε • ξ1 j t) - M.Yb * M.uc / 2 * M.lossB (yh j t ε) (ε • ξ1 j t))) -
        c3 * ∑' t, β ^ t * R j ε t -
        M.Yb * M.uc * Th * ∑' t, β ^ t * ((qd j ε t ^ 2 - ε ^ 2 * q1 j t ^ 2) +
          kk * (M.gap (yh j t ε) (ε • ξ1 j t) ^ 2 - ε ^ 2 * M.gap (y1 j t) (ξ1 j t) ^ 2)) := by
    rw [e4, hid]
    ring
  rw [key]
  have t1 := s2 j
  have t2 : |c3 * ∑' t, β ^ t * R j ε t| ≤ |c3| * (C3 * |ε| ^ 3) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (s3 j) (abs_nonneg _)
  have t3 : |M.Yb * M.uc * Th * ∑' t, β ^ t * ((qd j ε t ^ 2 - ε ^ 2 * q1 j t ^ 2) +
      kk * (M.gap (yh j t ε) (ε • ξ1 j t) ^ 2 - ε ^ 2 * M.gap (y1 j t) (ξ1 j t) ^ 2))| ≤
      |M.Yb * M.uc * Th| * (C1 * |ε| ^ 3) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (s1 j) (abs_nonneg _)
  have tri : ∀ a b c : ℝ, |a - b - c| ≤ |a| + |b| + |c| := fun a b c => by
    calc |a - b - c| ≤ |a - b| + |c| := abs_sub _ _
      _ ≤ |a| + |b| + |c| := by linarith [abs_sub a b]
  refine (tri _ _ _).trans ?_
  nlinarith [t1, t2, t3]

/-! ### Expected welfare -/

omit [NormedSpace ℝ Ξ] [Fintype ι] in
/-- Woodford (2003), §1, p. 385 (expected welfare `E_{t₀}`): a remainder that is `O(ε³)`
uniformly in the state stays `O(ε³)` uniformly after taking E_0 (for any expectation system,
by monotonicity and `E_0 c = c`). -/
theorem ucubic_E {Ω : Type} (𝔼 : ExpectationSystem Ω) {f : ℝ → Ω → ℝ} (h : UCubic f) :
    UCubic fun ε ω0 => 𝔼.E 0 (f ε) ω0 := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, hC.mono fun ε hε ω0 => 𝔼.abs_E_le (fun ω => hε ω) 0 ω0⟩

/-! ### `λ = κ/θ` derived -/

/-- Woodford (2003), Ch. 3, eq. (2.19), p. 187, restated in Ch. 6, p. 400: the slope of the
Calvo aggregate-supply relation, `κ = (1 − α)(1 − αβ)/α · (ω + σ⁻¹)/(1 + ωθ)`, computed from the
primitives of the economy `M` (`σ⁻¹ = M.sig`, `ω = M.omg`, `θ = M.θ`). -/
noncomputable def kap (M : BridgeCore.Econ Ξ ι) (α β : ℝ) : ℝ :=
  Moments.calvoKappa α β M.omg M.θ M.sig

/-- Woodford (2003), Ch. 6, eq. (2.22), p. 400, used in Ch. 7, (1.2), p. 469 (**the loss
weight produced by the welfare approximation**): `λ = κ/θ`. This is the weight on the squared
output gap in the second-order expansion of actual utility (`CalvoFamily.bridge`,
`SCalvoFamily.bridge`); it is derived, not assumed. -/
noncomputable def lamW (M : BridgeCore.Econ Ξ ι) (α β : ℝ) : ℝ := kap M α β / M.θ

omit [Fintype ι] in
/-- Woodford (2003), Ch. 6, (2.22), p. 400: `λ = κ/θ` (definitional). -/
theorem lamW_eq (M : BridgeCore.Econ Ξ ι) (α β : ℝ) : lamW M α β = kap M α β / M.θ := rfl

omit [Fintype ι] in
/-- Woodford (2003), Ch. 3, (2.19): `κ > 0` for `0 < α < 1`, `β < 1`, `σ⁻¹ + ω > 0`,
`1 + ωθ > 0`. -/
theorem kap_pos {M : BridgeCore.Econ Ξ ι} {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ1 : β < 1) (hs : 0 < M.sig + M.omg) (hd : 0 < 1 + M.omg * M.θ) : 0 < kap M α β := by
  unfold kap Moments.calvoKappa
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < 1 - α * β := by nlinarith
  have h3 : 0 < M.omg + M.sig := by linarith
  positivity

omit [Fintype ι] in
/-- Woodford (2003), Ch. 6, (2.22): `λ = κ/θ > 0` for `θ > 0`. -/
theorem lamW_pos {M : BridgeCore.Econ Ξ ι} {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ1 : β < 1) (hs : 0 < M.sig + M.omg) (hd : 0 < 1 + M.omg * M.θ)
    (hθ : 0 < M.θ) : 0 < lamW M α β :=
  div_pos (kap_pos hα0 hα1 hβ1 hs hd) hθ

/-- Woodford (2003), Ch. 6, (2.21), p. 400: the factor `Ȳu_c · 2Θ` multiplying `ε²/2` times
the loss in the welfare expansion, `Θ = ½θ(1 + ωθ)α/((1 − α)(1 − αβ))`. -/
noncomputable def bK (M : BridgeCore.Econ Ξ ι) (α β : ℝ) : ℝ :=
  M.Yb * M.uc * (2 * PriceDispersion.ThetaCalvo α β M.θ M.omg)

/-- Woodford (2003), Ch. 6, (2.21): `Ȳu_c · 2Θ > 0`. -/
theorem bK_pos {M : BridgeCore.Econ Ξ ι} (hM : M.Std) {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ1 : β < 1) (hθ : 0 < M.θ) (hd : 0 < 1 + M.omg * M.θ) : 0 < bK M α β :=
  mul_pos (mul_pos hM.Yb_pos hM.uc_pos)
    (mul_pos two_pos (PriceDispersion.ThetaCalvo_pos hα0 hα1 hβ1 hθ hd))

/-! ### Calvo families: deterministic -/

variable (M : BridgeCore.Econ Ξ ι) (α γ : ℝ) (ξ1 : ℕ → Ξ) (D0 : ℝ → ℝ)

/-- Woodford (2003), Ch. 7, §1, pp. 468–485, and Ch. 6, §2.2, pp. 399–402 (**a one-parameter
family of Calvo economies**, the object to which every `O(‖·‖²)` qualifier of Chapter 7
refers): the cross-section of log outputs `ŷ_t(ε)` with first-order solution `y₁_t`, the price
dispersion `D ε (t+1) = Δ_t` (`D ε 0 = Δ_{−1}(ε) = D0 ε`, common to all policies), index
inflation `fl ε (t+1) = π_t` (`fl ε 0 = π_{−1}`) with first-order solution `π₁`, satisfying
Dixit–Stiglitz demand (2.12) and the exact Calvo dispersion law with indexation `γ` (`γ = 0`:
none) with an `O(ε³)` remainder, all uniformly in the date; the disturbances are `ε ξ₁_t`. -/
structure CalvoFamily where
  /-- The cross-section of log outputs `ŷ_t(ε)(i)`. -/
  yh : ℕ → ℝ → ι → ℝ
  /-- Its first-order solution `y₁_t`. -/
  y1 : ℕ → ι → ℝ
  /-- Price dispersion: `D ε (t + 1) = Δ_t`, `D ε 0 = Δ_{−1}`. -/
  D : ℝ → ℕ → ℝ
  /-- Index inflation: `fl ε (t + 1) = π_t`, `fl ε 0 = π_{−1}`. -/
  fl : ℝ → ℕ → ℝ
  /-- The remainder of the dispersion law. -/
  R : ℝ → ℕ → ℝ
  /-- The first-order solution of inflation. -/
  π1 : ℕ → ℝ
  /-- `ŷ_t(ε) − εy₁_t = O(ε²)` uniformly in `t`. -/
  fam : (fun p : ℕ × ℝ => yh p.1 p.2 - p.2 • y1 p.1) =O[BridgeCore.unif] fun p => p.2 ^ 2
  /-- `y₁` is bounded. -/
  y1_bdd : ∃ C, ∀ t, ‖y1 t‖ ≤ C
  /-- Dixit–Stiglitz demand (2.12): `var_i ŷ_t = θ²Δ_t`. -/
  dem : ∀ ε t, ExpLogCES.crossVar M.w (yh t ε) = M.θ ^ 2 * D ε (t + 1)
  /-- The initial dispersion `Δ_{−1}(ε)` is the given `D0 ε`. -/
  init : ∀ ε, D ε 0 = D0 ε
  /-- The Calvo dispersion law (2.20)/(2.24) with remainder `R`. -/
  recur : ∀ ε t, D ε (t + 1) = α * D ε t + α / (1 - α) * (fl ε (t + 1) - γ * fl ε t) ^ 2 + R ε t
  /-- `π_t(ε) − επ₁_t = O(ε²)` uniformly in `t` (including `π_{−1}`). -/
  fl_fo : (fun p : ℕ × ℝ => fl p.2 p.1 - p.2 * π1 p.1) =O[BridgeCore.unif] fun p => p.2 ^ 2
  /-- `π₁` is bounded. -/
  π1_bdd : ∃ C, ∀ t, |π1 t| ≤ C
  /-- The remainder is `O(ε³)` uniformly in `t`. -/
  rem : (fun p : ℕ × ℝ => R p.2 p.1) =O[BridgeCore.unif] fun p => p.2 ^ 3

/-- Woodford (2003), Ch. 6, (2.21)–(2.25): the terms independent of policy, a function of the
disturbances `ξ₁` and the initial dispersion only. -/
noncomputable def tipC (β ε : ℝ) : ℝ :=
  ∑' t, β ^ t * M.tipState (ε • ξ1 t) -
    M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * D0 ε / (1 - α * β)))

namespace CalvoFamily

variable {M α γ D0}

/-- Woodford (2003), Ch. 7, (1.2), p. 469 (actual welfare): the discounted actual utility
`∑βᵗU_t(ε)` of the family. -/
noncomputable def W (F : CalvoFamily M α γ D0) (β ε : ℝ) : ℝ :=
  ∑' t, β ^ t * M.Ustate (F.yh t ε) (ε • ξ1 t)

/-- Woodford (2003), Ch. 7, (1.2) and (1.22), pp. 469 and 481: the discounted quadratic loss of
the first-order solution, `∑βᵗ[(π₁_t − γπ₁_{t−1})² + (κ/θ)(x₁_t)²]`, with the output gap measured
from the efficient level (Woodford's `x − x*`). -/
noncomputable def L (F : CalvoFamily M α γ D0) (β : ℝ) : ℝ :=
  ∑' t, β ^ t * ((F.π1 (t + 1) - γ * F.π1 t) ^ 2 + lamW M α β * M.gap (F.y1 t) (ξ1 t) ^ 2)

/-- Woodford (2003), Ch. 6, **Propositions 6.4–6.5** for the family (actual welfare to
`O(ε³)`): `∑βᵗU_t(ε) = TIP(ε) − (ε²/2)·Ȳu_c2Θ·L + O(ε³)` with `L` the loss of the first-order
solution with weight `λ = κ/θ` (`lamW`), from the Chapter 6 bridge
(`BridgeCore.Econ.prop65_bridge`). -/
theorem bridge (F : CalvoFamily M α γ D0) (hM : M.Std) (heff : M.vy = M.uc)
    (hden : M.sig + M.omg ≠ 0) (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0) {β : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) :
    (fun ε => F.W ξ1 β ε - (tipC M α ξ1 D0 β ε - ε ^ 2 / 2 * (bK M α β * F.L ξ1 β))) =O[𝓝 0]
      fun ε => ε ^ 3 := by
  have h := BridgeCore.Econ.prop65_bridge hM heff hden hθ hd hα0 hα1 hβ0 hβ1 F.fam F.y1_bdd hξ1
    F.dem F.recur F.fl_fo F.π1_bdd F.rem
  refine h.congr_left fun ε => ?_
  simp only [W, L, tipC, bK, lamW, kap, F.init]
  ring

end CalvoFamily

/-! ### Calvo families under uncertainty -/

variable {Ω : Type} (ξS : Ω → ℕ → Ξ) (DS0 : Ω → ℝ → ℝ)

/-- Woodford (2003), Ch. 7, §2, pp. 485–501, and Ch. 6, §2.2 (**a one-parameter family of Calvo
economies under uncertainty**): for every state `ω` (the realised history) a path as in
`CalvoFamily` (no indexation), with every order hypothesis uniform in the state AND the date
(the "bounded fluctuations" of Ch. 6, §2, p. 394). The disturbances along state `ω` are
`ε ξS ω t` and the initial dispersion `DS0 ω ε`. -/
structure SCalvoFamily where
  /-- The cross-section of log outputs in each state. -/
  yh : Ω → ℕ → ℝ → ι → ℝ
  /-- Its first-order solution. -/
  y1 : Ω → ℕ → ι → ℝ
  /-- Price dispersion in each state: `D ω ε (t + 1) = Δ_t`. -/
  D : Ω → ℝ → ℕ → ℝ
  /-- Index inflation in each state: `fl ω ε (t + 1) = π_t`. -/
  fl : Ω → ℝ → ℕ → ℝ
  /-- The remainder of the dispersion law. -/
  R : Ω → ℝ → ℕ → ℝ
  /-- The first-order solution of inflation in each state. -/
  π1 : Ω → ℕ → ℝ
  /-- `ŷ − εy₁ = O(ε²)` uniformly in the state and the date. -/
  fam : (fun p : (Ω × ℕ) × ℝ => yh p.1.1 p.1.2 p.2 - p.2 • y1 p.1.1 p.1.2) =O[uF Ω] fun p => p.2 ^ 2
  /-- `y₁` is bounded uniformly. -/
  y1_bdd : ∃ C, ∀ ω t, ‖y1 ω t‖ ≤ C
  /-- Dixit–Stiglitz demand (2.12) in each state. -/
  dem : ∀ ω ε t, ExpLogCES.crossVar M.w (yh ω t ε) = M.θ ^ 2 * D ω ε (t + 1)
  /-- The initial dispersion is the given DS0. -/
  init : ∀ ω ε, D ω ε 0 = DS0 ω ε
  /-- The Calvo dispersion law (2.20) with remainder `R`. -/
  recur : ∀ ω ε t, D ω ε (t + 1) = α * D ω ε t + α / (1 - α) * fl ω ε (t + 1) ^ 2 + R ω ε t
  /-- `π − επ₁ = O(ε²)` uniformly in the state and the date. -/
  fo : (fun p : (Ω × ℕ) × ℝ => fl p.1.1 p.2 p.1.2 - p.2 * π1 p.1.1 p.1.2) =O[uF Ω] fun p => p.2 ^ 2
  /-- `π₁` is bounded uniformly. -/
  π1_bdd : ∃ C, ∀ ω t, |π1 ω t| ≤ C
  /-- The remainder is `O(ε³)` uniformly in the state and the date. -/
  rem : (fun p : (Ω × ℕ) × ℝ => R p.1.1 p.2 p.1.2) =O[uF Ω] fun p => p.2 ^ 3

/-- Woodford (2003), Ch. 6, (2.21): the terms independent of policy along state `ω`. -/
noncomputable def tipS (β ε : ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * M.tipState (ε • ξS ω t) -
    M.Yb * M.uc * (M.θ * (1 + M.omg * M.θ) / 2 * (α * DS0 ω ε / (1 - α * β)))

/-- Woodford (2003), App. E.2, p. 695 (shifting the date): uniformity in the state and the date
is preserved by `t ↦ t + 1`. -/
theorem uF_shift {J : Type*} {f : J → ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : (fun p : (J × ℕ) × ℝ => f p.1.1 p.1.2 p.2) =O[uF J] fun p => g p.2) :
    (fun p : (J × ℕ) × ℝ => f p.1.1 (p.1.2 + 1) p.2) =O[uF J] fun p => g p.2 := by
  obtain ⟨C, hC⟩ := isBigO_uF_iff.1 h
  exact isBigO_uF_iff (f := fun j t ε => f j (t + 1) ε).2
    ⟨C, hC.mono fun ε hε j t => hε j (t + 1)⟩

namespace SCalvoFamily

variable {M α DS0}

/-- Woodford (2003), Ch. 7, (1.2), p. 469, along state `ω`: the discounted actual utility of the
realised path. -/
noncomputable def Wp (F : SCalvoFamily M α DS0) (β ε : ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * M.Ustate (F.yh ω t ε) (ε • ξS ω t)

/-- Woodford (2003), Ch. 7, (1.2), p. 469, along state `ω`: the discounted loss of the
first-order solution with `λ = κ/θ`. -/
noncomputable def Lp (F : SCalvoFamily M α DS0) (β : ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * (F.π1 ω (t + 1) ^ 2 + lamW M α β * M.gap (F.y1 ω t) (ξS ω t) ^ 2)

/-- Woodford (2003), Ch. 6, Proposition 6.4 along every state, uniformly (`calvo_bridge_unif`):
`∑βᵗU_t(ω, ε) = TIP(ω, ε) − (ε²/2)Ȳu_c2Θ L(ω) + O(ε³)`, one constant for all states. -/
theorem bridge_path (F : SCalvoFamily M α DS0) (hM : M.Std) (heff : M.vy = M.uc)
    (hden : M.sig + M.omg ≠ 0) (hθ : M.θ ≠ 0) (hd : 1 + M.omg * M.θ ≠ 0) {β : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C) :
    UCubic fun ε ω => F.Wp ξS β ε ω -
      (tipS M α ξS DS0 β ε ω - ε ^ 2 / 2 * (bK M α β * F.Lp ξS β ω)) := by
  obtain ⟨C, hC⟩ := F.π1_bdd
  have h := calvo_bridge_unif M hM heff hden hθ hd hα0 hα1 hβ0 hβ1 F.fam F.y1_bdd hξ
    (qd := fun ω ε t => F.fl ω ε (t + 1)) (q1 := fun ω t => F.π1 ω (t + 1)) F.dem F.recur
    (uF_shift (f := fun ω t ε => F.fl ω ε t - ε * F.π1 ω t) (g := fun ε => ε ^ 2) F.fo)
    ⟨C, fun ω t => hC ω (t + 1)⟩ F.rem
  obtain ⟨K, hK⟩ := h
  refine ⟨K, hK.mono fun ε hε ω => ?_⟩
  convert hε ω using 3
  simp only [Wp, Lp, tipS, bK, lamW, kap, F.init]

/-- Woodford (2003), Ch. 7, §2.1, p. 488 (**expected welfare** `E_{t₀}∑βᵗU_t`): the conditional
expectation at date `0` of the discounted actual utility. -/
noncomputable def EW (𝔼 : ExpectationSystem Ω) (F : SCalvoFamily M α DS0) (β ε : ℝ)
    (ω0 : Ω) : ℝ :=
  𝔼.E 0 (F.Wp ξS β ε) ω0

/-- Woodford (2003), Ch. 7, (1.2) and §2.1, p. 488: the conditional expectation at date `0` of
the discounted loss of the first-order solution. -/
noncomputable def EL (𝔼 : ExpectationSystem Ω) (F : SCalvoFamily M α DS0) (β : ℝ)
    (ω0 : Ω) : ℝ :=
  𝔼.E 0 (F.Lp ξS β) ω0

/-- Woodford (2003), Ch. 6, Proposition 6.4, and Ch. 7, §2.1 (**expected welfare to `O(ε³)`**):
for any expectation system, `E_0∑βᵗU_t = E_0 TIP − (ε²/2)Ȳu_c2Θ E_0 L + O(ε³)`, uniformly in the
date-`0` state. -/
theorem bridge (𝔼 : ExpectationSystem Ω) (F : SCalvoFamily M α DS0) (hM : M.Std)
    (heff : M.vy = M.uc) (hden : M.sig + M.omg ≠ 0) (hθ : M.θ ≠ 0)
    (hd : 1 + M.omg * M.θ ≠ 0) {β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C) :
    UCubic fun ε ω0 => EW ξS 𝔼 F β ε ω0 -
      (𝔼.E 0 (tipS M α ξS DS0 β ε) ω0 - ε ^ 2 / 2 * (bK M α β * EL ξS 𝔼 F β ω0)) := by
  have h := ucubic_E 𝔼 (F.bridge_path ξS hM heff hden hθ hd hα0 hα1 hβ0 hβ1 hξ)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, hK.mono fun ε hε ω0 => ?_⟩
  have e : (fun ω => F.Wp ξS β ε ω -
      (tipS M α ξS DS0 β ε ω - ε ^ 2 / 2 * (bK M α β * F.Lp ξS β ω))) =
      F.Wp ξS β ε - (tipS M α ξS DS0 β ε - (ε ^ 2 / 2 * bK M α β) • F.Lp ξS β) := by
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hε' := hε ω0
  beta_reduce at hε'
  rw [e, map_sub, map_sub, map_smul] at hε'
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hε'
  simp only [EW, EL]
  convert hε' using 2
  ring

end SCalvoFamily

end Woodford.GainsFromCommitment.TidyR6WelfCalvo
