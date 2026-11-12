/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6JointYeoman
import KeynesianStickyPrices.TidyR6RotembergLocal

/-!
# Decentralised optimum ⇒ joint optimum, over all uniformly bounded price plans

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118 ("a big point of
the new-Keynesian enterprise is that this structure has detailed micro-foundations"), and
Chapter 17, eqs. (17.15)–(17.17), p. 407.

TidyR6JointYeoman proves that the joint yeoman-farmer problem and the decentralised problems
coincide when the price plans are restricted to the concavity region of the decentralised
payoff. This module removes that restriction in the direction decentralised ⇒ joint and settles
the converse near the steady state.

## Main results

* `joint_of_decentral_class`: for **any** class `C` of price plans whose members are plans and
  admissible for the decentralised price setter, a household plan satisfying the Euler equation
  and the transversality condition together with a price plan **optimal** for the decentralised
  price setter in `C` is jointly optimal in `C`. No concavity of the price setter's payoff is
  used: the household's budget comparison bounds the utility gain of any joint deviation by the
  revenue gain valued at `u′(c_t)` (concavity of `u`), and the price setter's optimality bounds
  the latter.
* `joint_of_decentral_u`: the case `C = UPlan` (all uniformly bounded price plans), where
  admissibility is automatic.
* `joint_iff_decentral_near_ss`: in the symmetric equilibrium `q ≡ 0` with decentralised data
  within `ρ` of a zero-inflation steady state, joint optimality among uniformly bounded price
  plans **iff** household optimality and price-setter optimality among **all** plans
  (`TidyR6RotembergLocal.optimal_near_ss`).

## The decision

Decentralised ⇒ joint holds over all uniformly bounded price plans; it has no counter-model
(`TidyR6RotembergGlobal.cex_not_optimal` is a first-order-condition solution that is **not** a
decentralised optimum, so it does not bear on this direction). For merely date-wise bounded
competitors (`Plan`) the same proof works as soon as the competitor is admissible for the
decentralised price setter (`joint_of_decentral_class`); without it the revenue series of the
competitor need not converge and the comparison is not defined. The converse, joint ⇒ the price
setter's global optimality, is proved here near the steady state only: the joint deviation's
utility gain is bounded **above** by the linearly valued revenue gain, so joint optimality
controls the decentralised deviation only through the first-order condition.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6JointGlobal

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6HouseholdMeasureTVC TidyR6PriceSetting TidyR6Rotemberg
open TidyR6HouseholdPref TidyR6JointYeoman TidyR6RotembergPC TidyR6RotembergLocal

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 118: **a decentralised optimum is a joint optimum in any class of
admissible price plans**. Let the household plan `(c, b)` (income from `q`) satisfy the Euler
equation at every date and the transversality condition, with concave increasing differentiable
`u` and continuous `u′`; let `q` be optimal for the price setter that values revenue at
`u′(c_t)` (data `dataF`) within a class `C` of plans that are admissible for that price setter.
Then `(c, b, q)` is jointly optimal in `C`. -/
theorem joint_of_decentral_class {C : (ℕ → Ω → ℝ) → Prop} {β y : ℝ} (hβ : 0 < β)
    {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x) (hu'c : Continuous u')
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u) {ε η φ : ℝ}
    {P τ Y D π Q : ℕ → Ω → ℝ} {b₀ q0 : Ω → ℝ} {c b q : ℕ → Ω → ℝ}
    (hCP : ∀ q', C q' → Plan S q')
    (hCadm : ∀ q', C q' → TidyR6PriceSetting.Admissible S β (rotPay ε η φ) (dataF u' c Y D π)
      q0 q')
    (hfeas : Feasible S y P (sq τ Y ε q) Q b₀ c b)
    (hjadm : JointAdmissible S β u ε η φ D π q0 c q) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hm : ∀ n, Integrable (fun ω => u' (c n ω) / P n ω) S.μ)
    (hW : ∀ n, Integrable (fun ω => u' (c n ω) * b n ω / P n ω) S.μ)
    (heul : ∀ n, ∀ᵐ ω ∂S.μ, Q n ω * (u' (c n ω) / P n ω) =
      β * S.E n (fun ω => u' (c (n + 1) ω) / P (n + 1) ω) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0))
    (hF : OptimalIn S C β (rotPay ε η φ) (dataF u' c Y D π) q0 q)
    (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0) (hc : StronglyAdapted S.𝓕 c)
    (hY : StronglyAdapted S.𝓕 Y) (hD : StronglyAdapted S.𝓕 D) (hπ : StronglyAdapted S.𝓕 π)
    (hcb : ∀ t, BddAt S (c t)) (hYb : ∀ t, BddAt S (Y t)) (hDb : ∀ t, BddAt S (D t))
    (hπb : ∀ t, BddAt S (π t)) :
    JointOptimal S C β y u ε η φ P τ Y D π Q b₀ q0 c b q := by
  refine ⟨hfeas, hF.1, hjadm, fun c' b' q' hf' hq'C hjadm' => ?_⟩
  have hq := hCP q hF.1
  have hq' := hCP q' hq'C
  set e : (ℕ → Ω → ℝ) → ℕ → Ω → ℝ :=
    fun r n ω => u' (c n ω) * Y n ω * Real.exp ((1 - ε) * r n ω) with hedef
  have hei : ∀ (r : ℕ → Ω → ℝ), Plan S r → ∀ n, Integrable (e r n) S.μ := by
    intro r hr n
    have hb := ((BddAt.comp hu'c (hcb n)).mul (hYb n)).mul
      (BddAt.comp (v := fun z => Real.exp ((1 - ε) * z)) (by fun_prop) (hr.2 n))
    refine hb.integrable ?_
    have hm : Measurable[S.𝓕 n] (e r n) :=
      ((hu'c.measurable.comp (hc n).measurable).mul (hY n).measurable).mul
        (Real.continuous_exp.measurable.comp ((hr.1 n).measurable.const_mul (1 - ε)))
    exact (hm.stronglyMeasurable.mono (S.𝓕.le n)).aestronglyMeasurable
  -- the household's budget comparison
  have hhB : ∀ N, ∑ n ∈ Finset.range N, β ^ n * (∫ ω, u (c' n ω) ∂S.μ - ∫ ω, u (c n ω) ∂S.μ) ≤
      β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ +
        ∑ n ∈ Finset.range N, β ^ n * (∫ ω, e q' n ω ∂S.μ - ∫ ω, e q n ω ∂S.μ) := by
    intro N
    have h := partial_bound_w (w := fun _ _ => 1) hβ hu hconc hmono
      (fun _ => Eventually.of_forall fun _ => zero_le_one) hfeas hf'
      (fun n => (hjadm.1.integrable hβ n).congr (Eventually.of_forall fun ω => by simp [felic]))
      (fun n => (hjadm'.1.integrable hβ n).congr (Eventually.of_forall fun ω => by simp [felic]))
      hP
      (fun n => by simpa using hm n) (fun n => by simpa using hW n)
      (fun n => by
        have h2 := (hei q' hq' n).sub (hei q hq n)
        refine h2.congr (Eventually.of_forall fun ω => ?_)
        simp only [hedef, Pi.sub_apply, TidyR6JointYeoman.sq]
        ring)
      (fun n => by simpa using heul n) N
    have e2 : ∀ n, ∫ ω, u' (c n ω) * (sq τ Y ε q n ω - sq τ Y ε q' n ω) ∂S.μ =
        ∫ ω, e q' n ω ∂S.μ - ∫ ω, e q n ω ∂S.μ := by
      intro n
      rw [← integral_sub (hei q' hq' n) (hei q hq n)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hedef, TidyR6JointYeoman.sq]
      ring
    simp only [felic, one_mul] at h
    simp only [e2] at h
    simpa using h
  -- the decentralised payoff is the revenue plus the non-consumption payoff
  have hpF : ∀ (r : ℕ → Ω → ℝ), Plan S r → ∀ n,
      β ^ n * ∫ ω, e r n ω ∂S.μ =
        β ^ n * ∫ ω, pay (rotPay ε η φ) (dataF u' c Y D π) q0 r n ω ∂S.μ -
          β ^ n * ∫ ω, pay (rotPay ε η φ) (dataN D π) q0 r n ω ∂S.μ := by
    intro r hr n
    have hN := pay_integrable (rot_smooth ε η φ).2.2.1 (dataN_reg hD hπ hDb hπb) hq0 hq0b hr n
    rw [← mul_sub]
    congr 1
    rw [eq_sub_iff_add_eq, ← integral_add (hei r hr n) hN]
    exact integral_congr_ae (Eventually.of_forall fun ω =>
      (pay_split ε η φ u' c Y D π q0 r n ω).symm)
  have hsE : ∀ r, C r → TidyR6PriceSetting.Admissible S β (rotPay ε η φ) (dataN D π) q0 r →
      HasSum (fun n => β ^ n * ∫ ω, e r n ω ∂S.μ)
        (value S β (rotPay ε η φ) (dataF u' c Y D π) q0 r -
          value S β (rotPay ε η φ) (dataN D π) q0 r) := by
    intro r hrC hN
    have h := ((hCadm r hrC).summable hβ.le).hasSum.sub (hN.summable hβ.le).hasSum
    refine h.congr_fun fun n => ?_
    exact hpF r (hCP r hrC) n
  have hsq := hsE q hF.1 hjadm.2
  have hsq' := hsE q' hq'C hjadm'.2
  -- the limit of the household's comparison
  have hlimH := tendsto_partial_utilDiff hβ hjadm.1 hjadm'.1
  have hR := htvc.add (hsq'.sub hsq).tendsto_sum_nat
  have hle := le_of_tendsto_of_tendsto' hlimH hR fun N => by
    refine (hhB N).trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  have hFq := hF.2.2 q' hq'C (hCadm q' hq'C)
  unfold jointValue
  linarith

/-- Cochrane (2023), p. 118: **decentralised ⇒ joint over all uniformly bounded price plans**.
With `0 < β < 1` and uniformly bounded decentralised data, a household plan satisfying the Euler
equation and the transversality condition together with a price plan optimal for the
decentralised price setter among the uniformly bounded plans (`UPlan`) is jointly optimal among
the uniformly bounded plans. No concavity region is imposed. -/
theorem joint_of_decentral_u {β y : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu'c : Continuous u') (hconc : ConcaveOn ℝ Set.univ u)
    (hmono : Monotone u) {ε η φ : ℝ} {P τ Y D π Q : ℕ → Ω → ℝ} {b₀ q0 : Ω → ℝ}
    {c b q : ℕ → Ω → ℝ} (hfeas : Feasible S y P (sq τ Y ε q) Q b₀ c b)
    (hjadm : JointAdmissible S β u ε η φ D π q0 c q) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hm : ∀ n, Integrable (fun ω => u' (c n ω) / P n ω) S.μ)
    (hW : ∀ n, Integrable (fun ω => u' (c n ω) * b n ω / P n ω) S.μ)
    (heul : ∀ n, ∀ᵐ ω ∂S.μ, Q n ω * (u' (c n ω) / P n ω) =
      β * S.E n (fun ω => u' (c (n + 1) ω) / P (n + 1) ω) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0))
    (hF : OptimalIn S (UPlan S) β (rotPay ε η φ) (dataF u' c Y D π) q0 q)
    (hθ : DataReg S (dataF u' c Y D π)) (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖dataF u' c Y D π t ω‖ ≤ K)
    (hq0 : StronglyMeasurable[S.𝓕 0] q0) (hq0b : BddAt S q0) (hc : StronglyAdapted S.𝓕 c)
    (hY : StronglyAdapted S.𝓕 Y) (hD : StronglyAdapted S.𝓕 D) (hπ : StronglyAdapted S.𝓕 π)
    (hcb : ∀ t, BddAt S (c t)) (hYb : ∀ t, BddAt S (Y t)) (hDb : ∀ t, BddAt S (D t))
    (hπb : ∀ t, BddAt S (π t)) :
    JointOptimal S (UPlan S) β y u ε η φ P τ Y D π Q b₀ q0 c b q :=
  joint_of_decentral_class hβ hu hu'c hconc hmono (fun _ h => h.1)
    (fun _ h => admissible_of_uplan hβ.le hβ1 hθ hθu hq0 hq0b h) hfeas hjadm hP hm hW heul htvc
    hF hq0 hq0b hc hY hD hπ hcb hYb hDb hπb

/-- Cochrane (2023), p. 118 and eqs. (17.15)–(17.17), p. 407, **joint = decentralised near the
steady state, over all plans**. Let `0 < β < 1`, `ε > 1`, `η > ε − 1`, `φ > 0` and `(Ā, B̄, 0)` a
zero-inflation steady state (`Ā, B̄ > 0`, `(1 − ε)Ā + ηB̄ = 0`). There is `ρ > 0` such that, under
the regularity of `TidyR6JointYeoman.joint_iff_decentral` and with the decentralised data within
`ρ` of the steady state at every date almost surely, the symmetric plan `(c, b, q ≡ 0)` is jointly
optimal among uniformly bounded price plans **iff** `(c, b)` is optimal for the household and
`q ≡ 0` is optimal for the decentralised price setter among **all** plans. -/
theorem joint_iff_decentral_near_ss {β ε η φ A B : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hε : 1 < ε) (hη : ε - 1 < η) (hφ : 0 < φ) (hA : 0 < A) (hB : 0 < B)
    (hf : f1 ε η A B = 0) :
    ∃ ρ, 0 < ρ ∧ ∀ {y : ℝ} {u u' : ℝ → ℝ} {P τ Y D π Q : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
      {c b : ℕ → Ω → ℝ}, (∀ x, HasDerivAt u (u' x) x) → Continuous u' →
      ConcaveOn ℝ Set.univ u → Monotone u →
      Feasible S y P (sq τ Y ε zeroPlan) Q b₀ c b →
      JointAdmissible S β u ε η φ D π (fun _ => 0) c zeroPlan →
      StronglyAdapted S.𝓕 P → StronglyAdapted S.𝓕 Q → (∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) →
      (∀ t, EulerRegular S P Q c t) → (∀ t, ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) →
      (∀ n, Integrable (fun ω => u' (c n ω) * b n ω / P n ω) S.μ) →
      Tendsto (fun N => β ^ N * ∫ ω, u' (c N ω) * b N ω / P N ω ∂S.μ) atTop (𝓝 0) →
      StronglyAdapted S.𝓕 c → StronglyAdapted S.𝓕 Y → StronglyAdapted S.𝓕 D →
      StronglyAdapted S.𝓕 π → (∀ t, BddAt S (c t)) → (∀ t, BddAt S (Y t)) →
      (∀ t, BddAt S (D t)) → (∀ t, BddAt S (π t)) →
      (∀ t, ∀ᵐ ω ∂S.μ, dist (dataF u' c Y D π t ω) (A, B, 0) < ρ) →
      (JointOptimal S (UPlan S) β y u ε η φ P τ Y D π Q b₀ (fun _ => 0) c b zeroPlan ↔
        Optimal S β y u P (sq τ Y ε zeroPlan) Q b₀ c b ∧
          OptimalIn S (Plan S) β (rotPay ε η φ) (dataF u' c Y D π) (fun _ => 0) zeroPlan) := by
  obtain ⟨ρ, hρ, hopt⟩ := optimal_near_ss (S := S) hβ hβ1 hε hη hφ hA hB hf
  refine ⟨ρ, hρ, fun {y u u' P τ Y D π Q b₀ c b} hu hu'c hconc hmono hfeas hjadm hPad hQad hP
    hreg hb hW htvc hc hY hD hπ hcb hYb hDb hπb hnear => ?_⟩
  have hq0 : StronglyMeasurable[S.𝓕 0] (fun _ : Ω => (0 : ℝ)) := stronglyMeasurable_const
  have hq0b : BddAt S (fun _ : Ω => (0 : ℝ)) := BddAt.const 0
  have hθa : StronglyAdapted S.𝓕 (dataF u' c Y D π) := fun t =>
    ((((hu'c.measurable.comp (hc t).measurable).mul (hY t).measurable)).prodMk
      ((hD t).measurable.prodMk (hπ t).measurable)).stronglyMeasurable
  have hK : ∀ t, ∀ᵐ ω ∂S.μ, ‖dataF u' c Y D π t ω‖ ≤ ‖((A, B, 0) : ℝ × ℝ × ℝ)‖ + ρ :=
    fun t => by
      filter_upwards [hnear t] with ω h
      rw [dist_eq_norm] at h
      have := norm_le_insert' (dataF u' c Y D π t ω) ((A, B, 0) : ℝ × ℝ × ℝ)
      linarith
  constructor
  · intro hJ
    refine ⟨hh_of_joint hJ, hopt _ hθa hnear fun t => ?_⟩
    exact foc_of_joint hβ hu hu'c hJ (fun _ h => h.1) hq0 hq0b hc hY hD hπ hcb hYb hDb hπb
      fun z hz hzb => Eventually.of_forall fun s => uplan_perturb uplan_zero hz hzb s
  · rintro ⟨hH, hF⟩
    have hm' : ∀ n, Integrable (fun ω => u' (c n ω) / P n ω) S.μ := fun n => by
      have hbd := (BddAt.comp hu'c (hreg n).1).mul (hreg n).2.2.2.1
      refine (show BddAt S (fun ω => u' (c n ω) / P n ω) by
        simpa [div_eq_mul_inv] using hbd).integrable ?_
      have hmm : Measurable[S.𝓕 n] (fun ω => u' (c n ω) / P n ω) :=
        (hu'c.measurable.comp (hc n).measurable).div (hPad n).measurable
      exact (hmm.stronglyMeasurable.mono (S.𝓕.le n)).aestronglyMeasurable
    refine joint_of_decentral_u hβ hβ1 hu hu'c hconc hmono hfeas hjadm hP hm' hW (fun n => ?_)
      htvc ⟨uplan_zero, hF.2.1, fun q' h a => hF.2.2 q' h.1 a⟩
      ⟨hθa, fun t => ⟨_, hK t⟩⟩ ⟨_, hK⟩ hq0 hq0b hc hY hD hπ hcb hYb hDb hπb
    filter_upwards [euler_of_pos hβ hu hu'c hH hPad hP (hQad n) (hreg n) (hb n)] with ω hω
    simpa using hω

end Cochrane.KeynesianStickyPrices.TidyR6JointGlobal
