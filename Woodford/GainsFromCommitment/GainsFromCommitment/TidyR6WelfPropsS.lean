/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR6WelfProps
import GainsFromCommitment.TargetingRule
import GainsFromCommitment.Discretion

/-!
# Propositions 7.5 and 7.15 as statements about actual expected welfare

Woodford (2003), *Interest and Prices*, Chapter 7, §2.1, Proposition 7.5 (p. 487: the
discretionary equilibrium "evolves according to (2.3), up to an error of order
`O(‖Δ_{−1}^{1/2}, Δ_y, ξ̃‖²)`") and §5.1, Proposition 7.15 (p. 523: commitment to (5.1) is optimal
from a timeless perspective), whose welfare criterion is the expected value of (1.2).

The welfare criterion here is ACTUAL expected utility `E_0∑βᵗU_t(ε)`, the conditional
expectation at date `0` (any `ExpectationSystem`) of the discounted utility of the realised path
of a one-parameter family of Calvo economies under uncertainty
(`TidyR6WelfCalvo.SCalvoFamily`), with the loss weight `λ = κ/θ` derived by the Chapter 6
expansion, uniformly in the date-`0` state.

## Main results

* `EL_eq_loss`: the expected first-order loss of a family is `TargetingRule.loss` of its plan.
* `prop_7_15_welfare`: a family whose first-order plan is the equilibrium of the target
  criterion (5.1) is at least as good, up to `O(ε³)` in every state, as every family whose
  first-order plan is feasible with the timeless initial constraint (2.11), and strictly better
  in every state where the losses differ; `prop_7_15_welfare_converse`: with a faithful E_0, a
  family at least as good as that one has the (5.1) equilibrium as its first-order plan.
* `prop_7_5_welfare` (with `DiscWelfareOptS`): the family whose first-order plan is (2.3) is a
  discretionary optimum of actual expected welfare against one-date deviations;
  `prop_7_5_welfare_converse`: with a faithful E_0, a family that is at least as good as a
  one-date static-optimum deviation at every date has (2.3) as its first-order plan.
-/

namespace Woodford.GainsFromCommitment.TidyR6WelfPropsS

open Filter Topology Asymptotics
open Woodford.GainsFromCommitment.TidyR6WelfBase Woodford.GainsFromCommitment.TidyR6WelfBridge
  Woodford.GainsFromCommitment.TidyR6WelfCalvo Woodford.GainsFromCommitment.TidyR6WelfProps

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {ι : Type*} [Fintype ι]
variable {M : BridgeCore.Econ Ξ ι} {α β : ℝ} {Ω : Type} {ξS : Ω → ℕ → Ξ} {DS0 : Ω → ℝ → ℝ}

/-- Woodford (2003), §2.1, p. 486: the first-order inflation process of a family,
`π_t(ω) = π₁(ω)_{t+1}`. -/
def πS (F : SCalvoFamily M α DS0) : ℕ → Ω → ℝ := fun t ω => F.π1 ω (t + 1)

/-- Woodford (2003), §2.1, p. 486: the first-order output gap of a family in Woodford's units
(measured from the natural level): `x_t(ω) = gap₁(ω)_t + x*`. -/
noncomputable def xS (ξS : Ω → ℕ → Ξ) (xs : ℝ) (F : SCalvoFamily M α DS0) : ℕ → Ω → ℝ :=
  fun t ω => M.gap (F.y1 ω t) (ξS ω t) + xs

/-- Woodford (2003), (2.10): the first-order output gap is bounded uniformly in the state and the
date. -/
theorem gapS_bdd (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C) (F : SCalvoFamily M α DS0) :
    ∃ C, ∀ ω t, |M.gap (F.y1 ω t) (ξS ω t)| ≤ C := by
  have hx := uF_of_bounded hξ
  have h := (BridgeCore.crossMean_isBigO A.std.w_nonneg A.std.w_sum
    (uF_of_bounded F.y1_bdd)).sub
    (BridgeCore.natLin_isBigO M.sig M.omg (M.gS_isBigO hx) (M.qS_isBigO hx))
  obtain ⟨C, hC⟩ := bdd_uF (f := fun ω t (_ : ℝ) => M.gap (F.y1 ω t) (ξS ω t)) h
  obtain ⟨ε, hε⟩ := hC.exists
  exact ⟨C, hε⟩

/-- Woodford (2003), (1.2): the period loss of the first-order plan is bounded uniformly. -/
theorem periodLoss_bdd (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C) (xs : ℝ)
    (F : SCalvoFamily M α DS0) :
    ∃ B, ∀ t ω, |TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t ω| ≤ B := by
  obtain ⟨C1, h1⟩ := F.π1_bdd
  obtain ⟨C2, h2⟩ := gapS_bdd A hξ F
  refine ⟨C1 ^ 2 + |lamW M α β| * C2 ^ 2, fun t ω => ?_⟩
  unfold TargetingRule.periodLoss πS xS
  have a1 : F.π1 ω (t + 1) ^ 2 ≤ C1 ^ 2 :=
    sq_le_sq' (abs_le.mp (h1 ω (t + 1))).1 (abs_le.mp (h1 ω (t + 1))).2
  have a2 : M.gap (F.y1 ω t) (ξS ω t) ^ 2 ≤ C2 ^ 2 :=
    sq_le_sq' (abs_le.mp (h2 ω t)).1 (abs_le.mp (h2 ω t)).2
  have e : M.gap (F.y1 ω t) (ξS ω t) + xs - xs = M.gap (F.y1 ω t) (ξS ω t) := by ring
  rw [e, abs_le]
  constructor <;> nlinarith [abs_nonneg (lamW M α β), neg_abs_le (lamW M α β),
    le_abs_self (lamW M α β), sq_nonneg (F.π1 ω (t + 1)), sq_nonneg (M.gap (F.y1 ω t) (ξS ω t))]

/-- Woodford (2003), §2.1, p. 488 (`E_{t₀}∑βᵗ = ∑βᵗE_{t₀}` for bounded plans): the expected
first-order loss of a family is the loss `TargetingRule.loss` (weight `λ = κ/θ`) of its plan. -/
theorem EL_eq_loss (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C) (𝔼 : ExpectationSystem Ω)
    (xs : ℝ) (F : SCalvoFamily M α DS0) (ω0 : Ω) :
    SCalvoFamily.EL ξS 𝔼 F β ω0 =
      TargetingRule.loss 𝔼 β (lamW M α β) xs (πS F) (xS ξS xs F) ω0 := by
  obtain ⟨B, hB⟩ := periodLoss_bdd A hξ xs F
  have hpl : ∀ ω, F.Lp ξS β ω = ∑' t, β ^ t *
      TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t ω := fun ω => by
    unfold SCalvoFamily.Lp TargetingRule.periodLoss πS xS
    exact tsum_congr fun t => by ring
  unfold SCalvoFamily.EL TargetingRule.loss
  have hfun : F.Lp ξS β = fun ω => ∑' t, β ^ t *
      TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t ω := funext hpl
  rw [hfun, 𝔼.E_tsum A.β_pos.le A.β_lt (M := B) (fun k ω => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg A.β_pos.le k)]
    exact mul_le_mul_of_nonneg_left (hB k ω) (pow_nonneg A.β_pos.le k)) 0 ω0]
  refine tsum_congr fun t => ?_
  have e : (fun ω => β ^ t * TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t ω) =
      β ^ t • TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t := by
    funext ω; simp [smul_eq_mul]
  rw [e, map_smul]
  rfl

/-! ### Rankings of expected welfare -/

/-- Woodford (2003), p. 471, fn. 6, under uncertainty: if the expected first-order loss of `F` is
no larger than that of `G` in every date-`0` state, `F` is at least as good as `G` up to `O(ε³)`
in every state. -/
theorem uweaklyBetter_of_EL_le (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (F G : SCalvoFamily M α DS0)
    (h : ∀ ω0, SCalvoFamily.EL ξS 𝔼 F β ω0 ≤ SCalvoFamily.EL ξS 𝔼 G β ω0) :
    UWeaklyBetter (SCalvoFamily.EW ξS 𝔼 F β) (SCalvoFamily.EW ξS 𝔼 G β) :=
  uweaklyBetter_of_loss_le (T := fun ε ω0 => 𝔼.E 0 (tipS M α ξS DS0 β ε) ω0) A.bK_pos.le
    (F.bridge ξS 𝔼 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt
      A.β_pos.le A.β_lt hξ)
    (G.bridge ξS 𝔼 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt
      A.β_pos.le A.β_lt hξ) h

/-- Woodford (2003), p. 471, fn. 6, under uncertainty (strict, in a given state). -/
theorem lt_of_EL_lt (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (F G : SCalvoFamily M α DS0) (ω0 : Ω)
    (h : SCalvoFamily.EL ξS 𝔼 F β ω0 < SCalvoFamily.EL ξS 𝔼 G β ω0) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), SCalvoFamily.EW ξS 𝔼 G β ε ω0 < SCalvoFamily.EW ξS 𝔼 F β ε ω0 :=
  ueventually_lt_of_loss_lt (T := fun ε ω0 => 𝔼.E 0 (tipS M α ξS DS0 β ε) ω0) A.bK_pos
    (F.bridge ξS 𝔼 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt
      A.β_pos.le A.β_lt hξ)
    (G.bridge ξS 𝔼 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt
      A.β_pos.le A.β_lt hξ) ω0 h

/-- Woodford (2003), Propositions 7.5 and 7.15 (the converse, under uncertainty): if `F` is at
least as good as `G` up to `O(ε³)` uniformly in the state, its expected first-order loss is no
larger in every state. -/
theorem EL_le_of_uweaklyBetter (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (F G : SCalvoFamily M α DS0)
    (h : UWeaklyBetter (SCalvoFamily.EW ξS 𝔼 F β) (SCalvoFamily.EW ξS 𝔼 G β)) (ω0 : Ω) :
    SCalvoFamily.EL ξS 𝔼 F β ω0 ≤ SCalvoFamily.EL ξS 𝔼 G β ω0 :=
  loss_le_of_uweaklyBetter (T := fun ε ω0 => 𝔼.E 0 (tipS M α ξS DS0 β ε) ω0) A.bK_pos
    (F.bridge ξS 𝔼 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt
      A.β_pos.le A.β_lt hξ)
    (G.bridge ξS 𝔼 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt
      A.β_pos.le A.β_lt hξ) h ω0

/-! ### Proposition 7.15 -/

/-- **Woodford (2003), Proposition 7.15, p. 523, as a statement about actual expected welfare.**
Let `u` be a bounded adapted cost-push process (otherwise unrestricted), `x_{t₀−1}` known at
`t₀`, and E_0 have the pull-out property. If the first-order plan of `F` is the equilibrium of
(2.1) and the target criterion (5.1) (`TargetingRule.piStar`, `TargetingRule.xStar`, with
`λ = κ/θ` and `κ` the Calvo slope), then for every family `G` whose first-order plan is feasible
— bounded, adapted, (2.1) — and satisfies the timeless initial constraint (2.11), `F` is at least
as good as `G` up to `O(ε³)` in every date-`0` state, and strictly better, for every small
`ε ≠ 0`, in every state where the expected losses differ. -/
theorem prop_7_15_welfare (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) (xs : ℝ) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hm0 : 𝔼.E 0 xm1 = xm1) (F G : SCalvoFamily M α DS0)
    (hF : πS F = TargetingRule.piStar 𝔼 β (kap M α β) (lamW M α β) xm1 u ∧
      xS ξS xs F = TargetingRule.xStar 𝔼 β (kap M α β) (lamW M α β) xm1 u)
    (hG : TargetingRule.Feasible 𝔼 β (kap M α β) u
      (TargetingRule.eq211 𝔼 β (kap M α β) (lamW M α β) u xm1) (πS G) (xS ξS xs G)) :
    UWeaklyBetter (SCalvoFamily.EW ξS 𝔼 F β) (SCalvoFamily.EW ξS 𝔼 G β) ∧
      ∀ ω0, SCalvoFamily.EL ξS 𝔼 F β ω0 < SCalvoFamily.EL ξS 𝔼 G β ω0 →
        ∀ᶠ ε in 𝓝[≠] (0 : ℝ), SCalvoFamily.EW ξS 𝔼 G β ε ω0 <
          SCalvoFamily.EW ξS 𝔼 F β ε ω0 := by
  obtain ⟨⟨hAS, hC, hpb, hxb, hpa, hxa⟩, -⟩ :=
    TargetingRule.prop_7_15 𝔼 A.β_pos A.kap_pos A.lam_pos hu hua hK hm0
  have hopt := TargetingRule.crit_isConstrainedOpt 𝔼 A.β_pos A.β_lt A.kap_pos A.lam_pos hpo xs
    hu hua hK hm0 hAS hC hpb hxb hpa hxa
  refine ⟨uweaklyBetter_of_EL_le A hξ 𝔼 F G fun ω0 => ?_, fun ω0 h => lt_of_EL_lt A hξ 𝔼 F G ω0 h⟩
  rw [EL_eq_loss A hξ 𝔼 xs F, EL_eq_loss A hξ 𝔼 xs G, hF.1, hF.2]
  exact hopt.2 _ _ hG ω0

/-- **Woodford (2003), Proposition 7.15, p. 523 (converse: "the equilibrium determined by this
policy commitment is the same as the one characterized in Proposition 7.7", up to `O(‖·‖²)`).**
With a faithful E_0 and the pull-out property: if `F`'s first-order plan is feasible with the
timeless constraint (2.11), and `F` is at least as good, up to `O(ε³)` in every state, as a family
`G` whose first-order plan is the (5.1) equilibrium, then `F`'s first-order plan IS the (5.1)
equilibrium: it satisfies the target criterion (5.1) at every date. -/
theorem prop_7_15_welfare_converse (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) (hf : TargetingRule.Faithful 𝔼) (xs : ℝ)
    {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (hua : 𝔼.Adapted u) {xm1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1) (F G : SCalvoFamily M α DS0)
    (hFfeas : TargetingRule.Feasible 𝔼 β (kap M α β) u
      (TargetingRule.eq211 𝔼 β (kap M α β) (lamW M α β) u xm1) (πS F) (xS ξS xs F))
    (hG : πS G = TargetingRule.piStar 𝔼 β (kap M α β) (lamW M α β) xm1 u ∧
      xS ξS xs G = TargetingRule.xStar 𝔼 β (kap M α β) (lamW M α β) xm1 u)
    (h : UWeaklyBetter (SCalvoFamily.EW ξS 𝔼 F β) (SCalvoFamily.EW ξS 𝔼 G β)) :
    πS F = TargetingRule.piStar 𝔼 β (kap M α β) (lamW M α β) xm1 u ∧
      xS ξS xs F = TargetingRule.xStar 𝔼 β (kap M α β) (lamW M α β) xm1 u ∧
      TargetingRule.Crit (lamW M α β) (kap M α β) xm1 (πS F) (xS ξS xs F) := by
  obtain ⟨⟨hAS, hC, hpb, hxb, hpa, hxa⟩, -⟩ :=
    TargetingRule.prop_7_15 𝔼 A.β_pos A.kap_pos A.lam_pos hu hua hK hm0
  have hopt := TargetingRule.crit_isConstrainedOpt 𝔼 A.β_pos A.β_lt A.kap_pos A.lam_pos hpo xs
    hu hua hK hm0 hAS hC hpb hxb hpa hxa
  have hle : ∀ ω0, TargetingRule.loss 𝔼 β (lamW M α β) xs (πS F) (xS ξS xs F) ω0 ≤
      TargetingRule.loss 𝔼 β (lamW M α β) xs (TargetingRule.piStar 𝔼 β (kap M α β) (lamW M α β)
        xm1 u) (TargetingRule.xStar 𝔼 β (kap M α β) (lamW M α β) xm1 u) ω0 := fun ω0 => by
    have := EL_le_of_uweaklyBetter A hξ 𝔼 F G h ω0
    rwa [EL_eq_loss A hξ 𝔼 xs F, EL_eq_loss A hξ 𝔼 xs G, hG.1, hG.2] at this
  have hFopt : TargetingRule.IsConstrainedOpt 𝔼 β (kap M α β) (lamW M α β) xs u
      (TargetingRule.eq211 𝔼 β (kap M α β) (lamW M α β) u xm1) (πS F) (xS ξS xs F) :=
    ⟨hFfeas, fun π' x' hF' ω => (hle ω).trans (hopt.2 π' x' hF' ω)⟩
  obtain ⟨e1, e2⟩ := TargetingRule.eq_star_of_isConstrainedOpt 𝔼 A.β_pos A.β_lt A.kap_pos
    A.lam_pos hpo hf hu hua hK hm0 hFopt
  exact ⟨e1, e2, by rw [e1, e2]; exact hC⟩

/-! ### Proposition 7.5 -/

/-- Woodford (2003), p. 487 (a deviation at one date): the first-order plans of `F` and `G`
coincide, in every state, at every date except `t`. -/
def SDev (ξS : Ω → ℕ → Ξ) (xs : ℝ) (F G : SCalvoFamily M α DS0) (t : ℕ) : Prop :=
  ∀ s, s ≠ t → πS G s = πS F s ∧ xS ξS xs G s = xS ξS xs F s

/-- Woodford (2003), p. 487: for a one-date deviation the difference of expected losses is the
discounted expected difference of the date-`t` period losses. -/
theorem loss_sub_of_sdev (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (xs : ℝ) (F G : SCalvoFamily M α DS0) (t : ℕ)
    (hdev : SDev ξS xs F G t) (ω0 : Ω) :
    TargetingRule.loss 𝔼 β (lamW M α β) xs (πS G) (xS ξS xs G) ω0 -
        TargetingRule.loss 𝔼 β (lamW M α β) xs (πS F) (xS ξS xs F) ω0 =
      β ^ t * 𝔼.E 0 (TargetingRule.periodLoss (lamW M α β) xs (πS G) (xS ξS xs G) t -
        TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t) ω0 := by
  obtain ⟨BG, hBG⟩ := periodLoss_bdd A hξ xs G
  obtain ⟨BF, hBF⟩ := periodLoss_bdd A hξ xs F
  have sG := Sequences.summable_disc A.β_pos.le A.β_lt
    (fun s => 𝔼.abs_E_le (fun ω => hBG s ω) 0 ω0)
  have sF := Sequences.summable_disc A.β_pos.le A.β_lt
    (fun s => 𝔼.abs_E_le (fun ω => hBF s ω) 0 ω0)
  unfold TargetingRule.loss
  rw [← sG.tsum_sub sF, tsum_eq_single t fun s hs => by
    obtain ⟨h1, h2⟩ := hdev s hs
    have e : TargetingRule.periodLoss (lamW M α β) xs (πS G) (xS ξS xs G) s =
        TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) s := by
      unfold TargetingRule.periodLoss; rw [h1, h2]
    rw [e, sub_self], map_sub]
  simp only [Pi.sub_apply]
  ring

/-- Woodford (2003), p. 487 (**discretion as optimisation of actual expected welfare**): the
family `F` is a discretionary optimum up to `O(ε³)` if, at every date `t`, it is at least as
good, up to `O(ε³)` uniformly in the state, as every family that deviates from it only at date
`t` and whose date-`t` first-order point lies, in every state, on the perceived trade-off (2.1)
with the private expectation `E_tπ_{t+1}` of `F` taken as given. -/
def DiscWelfareOptS (ξS : Ω → ℕ → Ξ) (𝔼 : ExpectationSystem Ω) (β xs : ℝ) (u : ℕ → Ω → ℝ)
    (F : SCalvoFamily M α DS0) : Prop :=
  ∀ (t : ℕ) (G : SCalvoFamily M α DS0), SDev ξS xs F G t →
    (∀ ω, (πS G t ω, xS ξS xs G t ω) ∈
      Discretion.staticSet β (kap M α β) (𝔼.E t (πS F (t + 1)) ω) (u t ω)) →
    UWeaklyBetter (SCalvoFamily.EW ξS 𝔼 F β) (SCalvoFamily.EW ξS 𝔼 G β)

/-- **Woodford (2003), Proposition 7.5, p. 487, as a statement about actual expected welfare
(existence).** For a bounded adapted cost-push process `u`, if the first-order plan of `F` is the
Markov process (2.3) with `x_t = x* − (κ/λ)π_t` (`λ = κ/θ`), then `F` is a discretionary optimum
of actual expected welfare up to `O(ε³)` (`DiscWelfareOptS`). -/
theorem prop_7_5_welfare (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (xs : ℝ) {u : ℕ → Ω → ℝ} {Mu : ℝ} (hu : ∀ t ω, |u t ω| ≤ Mu)
    (hua : 𝔼.Adapted u) (F : SCalvoFamily M α DS0)
    (hF : πS F = Discretion.infl23 𝔼 β (kap M α β) (lamW M α β) xs u ∧
      xS ξS xs F = Discretion.gap23 𝔼 β (kap M α β) (lamW M α β) xs u) :
    DiscWelfareOptS ξS 𝔼 β xs u F := by
  intro t G hdev hon
  have hD := Discretion.discretionEq_infl23 𝔼 (xs := xs) A.β_pos A.β_lt A.kap_pos A.lam_pos hu
    hua
  rw [← hF.1, ← hF.2] at hD
  refine uweaklyBetter_of_EL_le A hξ 𝔼 F G fun ω0 => ?_
  rw [EL_eq_loss A hξ 𝔼 xs F, EL_eq_loss A hξ 𝔼 xs G]
  have hsub := loss_sub_of_sdev A hξ 𝔼 xs F G t hdev ω0
  have hpt : (0 : Ω → ℝ) ≤
      TargetingRule.periodLoss (lamW M α β) xs (πS G) (xS ξS xs G) t -
        TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t := fun ω => by
    have hmin := (hD.2.2.2.2 t ω).2
    have := isMinOn_iff.mp hmin _ (hon ω)
    simp only [Pi.zero_apply, Pi.sub_apply, TargetingRule.periodLoss]
    simp only [Discretion.periodLoss] at this
    linarith
  have hE := 𝔼.mono 0 hpt ω0
  rw [map_zero] at hE
  have : 0 ≤ β ^ t * 𝔼.E 0 (TargetingRule.periodLoss (lamW M α β) xs (πS G) (xS ξS xs G) t -
      TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t) ω0 :=
    mul_nonneg (pow_nonneg A.β_pos.le t) hE
  linarith

/-- **Woodford (2003), Proposition 7.5, p. 487, as a statement about actual expected welfare
(uniqueness: "there is a unique Markov equilibrium ... inflation evolves according to (2.3), up
to an error of order `O(‖·‖²)`").** Let E_0 be faithful and `u` bounded and adapted. Let `F`
have an adapted first-order plan satisfying (2.1), and suppose that at every date `t` there is a
family deviating from `F` only at `t` whose date-`t` point is, in every state, the optimum of the
bank's static problem on the perceived trade-off, and that `F` is at least as good as it up to
`O(ε³)` uniformly in the state. Then `F`'s first-order plan is (2.3) with
`x_t = x* − (κ/λ)π_t`, `λ = κ/θ`. -/
theorem prop_7_5_welfare_converse (A : Assm M α β) (hξ : ∃ C, ∀ ω t, ‖ξS ω t‖ ≤ C)
    (𝔼 : ExpectationSystem Ω) (hf : TargetingRule.Faithful 𝔼) (xs : ℝ) {u : ℕ → Ω → ℝ}
    {Mu : ℝ} (hu : ∀ t ω, |u t ω| ≤ Mu) (hua : 𝔼.Adapted u) (F : SCalvoFamily M α DS0)
    (hFa : 𝔼.Adapted (πS F) ∧ 𝔼.Adapted (xS ξS xs F))
    (hFas : ∀ t ω, (πS F t ω, xS ξS xs F t ω) ∈
      Discretion.staticSet β (kap M α β) (𝔼.E t (πS F (t + 1)) ω) (u t ω))
    (hcomp : ∀ t, ∃ G : SCalvoFamily M α DS0, SDev ξS xs F G t ∧
      (∀ ω, (πS G t ω, xS ξS xs G t ω) ∈
          Discretion.staticSet β (kap M α β) (𝔼.E t (πS F (t + 1)) ω) (u t ω) ∧
        IsMinOn (fun r : ℝ × ℝ => Discretion.periodLoss (lamW M α β) xs r.1 r.2)
          (Discretion.staticSet β (kap M α β) (𝔼.E t (πS F (t + 1)) ω) (u t ω))
          (πS G t ω, xS ξS xs G t ω)) ∧
      UWeaklyBetter (SCalvoFamily.EW ξS 𝔼 F β) (SCalvoFamily.EW ξS 𝔼 G β)) :
    πS F = Discretion.infl23 𝔼 β (kap M α β) (lamW M α β) xs u ∧
      xS ξS xs F = Discretion.gap23 𝔼 β (kap M α β) (lamW M α β) xs u := by
  have hopt : ∀ t ω, IsMinOn (fun r : ℝ × ℝ => Discretion.periodLoss (lamW M α β) xs r.1 r.2)
      (Discretion.staticSet β (kap M α β) (𝔼.E t (πS F (t + 1)) ω) (u t ω))
      (πS F t ω, xS ξS xs F t ω) := by
    intro t
    obtain ⟨G, hdev, hG, hW⟩ := hcomp t
    set d := TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t -
      TargetingRule.periodLoss (lamW M α β) xs (πS G) (xS ξS xs G) t with hd
    have hnn : (0 : Ω → ℝ) ≤ d := fun ω => by
      have := isMinOn_iff.mp (hG ω).2 _ (hFas t ω)
      simp only [Pi.zero_apply, hd, Pi.sub_apply, TargetingRule.periodLoss]
      simp only [Discretion.periodLoss] at this
      linarith
    have hE0 : 𝔼.E 0 d = 0 := by
      funext ω0
      have h1 := EL_le_of_uweaklyBetter A hξ 𝔼 F G hW ω0
      rw [EL_eq_loss A hξ 𝔼 xs F, EL_eq_loss A hξ 𝔼 xs G] at h1
      have h2 := loss_sub_of_sdev A hξ 𝔼 xs F G t hdev ω0
      have hneg : d = -(TargetingRule.periodLoss (lamW M α β) xs (πS G) (xS ξS xs G) t -
          TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t) := by
        rw [hd]; abel
      have h3 : 𝔼.E 0 d ω0 = -𝔼.E 0 (TargetingRule.periodLoss (lamW M α β) xs (πS G)
          (xS ξS xs G) t - TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t)
          ω0 := by
        rw [hneg, map_neg]; rfl
      have h4 := 𝔼.mono 0 hnn ω0
      rw [map_zero] at h4
      have hβt := pow_pos A.β_pos t
      have h5 : 0 ≤ 𝔼.E 0 (TargetingRule.periodLoss (lamW M α β) xs (πS G) (xS ξS xs G) t -
          TargetingRule.periodLoss (lamW M α β) xs (πS F) (xS ξS xs F) t) ω0 := by
        by_contra hc
        push Not at hc
        nlinarith
      simp only [Pi.zero_apply] at h4 ⊢
      linarith
    have hz := hf d hnn hE0
    intro ω
    rw [isMinOn_iff]
    intro q hq
    have h1 := isMinOn_iff.mp (hG ω).2 q hq
    have h2 := congrFun hz ω
    simp only [hd, Pi.sub_apply, Pi.zero_apply, TargetingRule.periodLoss] at h2
    simp only [Discretion.periodLoss] at h1 ⊢
    linarith
  have hb1 : BoundedProc (πS F) := by
    obtain ⟨C, hC⟩ := F.π1_bdd
    exact ⟨C, fun t ω => hC ω (t + 1)⟩
  have hb2 : BoundedProc (xS ξS xs F) := by
    obtain ⟨C, hC⟩ := gapS_bdd A hξ F
    exact ⟨C + |xs|, fun t ω => (abs_add_le _ _).trans (by linarith [hC ω t])⟩
  have hD : Discretion.DiscretionEq 𝔼 β (kap M α β) (lamW M α β) xs u (πS F) (xS ξS xs F) :=
    ⟨hFa.1, hFa.2, hb1, hb2, fun t ω => ⟨hFas t ω, hopt t ω⟩⟩
  exact (Discretion.prop_7_5 𝔼 A.β_pos A.β_lt A.kap_pos A.lam_pos hu hua _ _).mp hD

end Woodford.GainsFromCommitment.TidyR6WelfPropsS
