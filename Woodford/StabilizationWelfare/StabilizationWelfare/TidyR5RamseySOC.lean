/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5CommitLQ
import StabilizationWelfare.BridgeExtensions

/-!
# Second-order sufficiency of the commitment plan (Benigno–Woodford, any distortion)

Woodford (2003), *Interest and Prices*, Chapter 6, §5, Proposition 6.15, (5.5)–(5.8),
pp. 458–459, Chapter 7, §5.1, footnote 71, and pp. 414–415.

The first-order conditions of the date-0 Ramsey problem (TidyR5RamseyDate0) are necessary.
That their solution MAXIMISES welfare is a second-order statement. In the exact Calvo model with
an arbitrary distortion `Φ ∈ [0, 1)`, Proposition 6.15 (Layer B:
`BridgeExtensions.prop615_first_order`) expands welfare along ANY feasible family of plans as
`W(ε) = W₀ − ε²Ω̃·L(first-order component) + t.i.p. + O(ε³)` with `Ω̃ > 0`
(`LargeDistortions.OmegaTilde_pos`) and `L = E₀∑βᵗ[π² + λ̃(Ŷ − Ŷ*)²]`. The first-order
components of feasible plans satisfy the linear AS relation `π = κx + βE_tπ′ + u`
(`x = Ŷ − Ŷ*`, `u = κ(Ŷ* − Ŷⁿ)`), and for that LQ problem the footnote-71 plan with
`φ = λ̃/κ` is optimal (`TidyR5CommitLQ.fn71_optimal`). Here:

* `weak_ranking`: a family whose loss is not larger is not worse, up to `O(ε³)`.
* `loss615_eq_ELoss`: the discounted loss (5.6) is the expected loss `ELoss` of the LQ problem.
* **`lq_sufficiency615`**: for every `Φ ∈ [0, 1)` (with `λ̃ > 0`): the family whose first-order
  component is the footnote-71 commitment plan is optimal up to `O(ε³)` among all feasible
  families with the same transitory term `W₀` and terms independent of policy, and strictly
  better, for all small `ε ≠ 0`, than any family whose first-order component has a larger loss.
-/

namespace Woodford.StabilizationWelfare.TidyR5RamseySOC

open Filter Topology Asymptotics
open Sequences TidyR5CommitLQ BridgeExtensions

variable {A : Type*} {l : Filter A} {e : A → ℝ}

/-- Woodford (2003), §1, pp. 386–389 (the WEAK welfare ranking): if
`W_X = T − ε²kL_X + O(ε³)` for `X = A, B` (same `T`, `k > 0`) and `L_A ≤ L_B`, then
`W_B ≤ W_A + C|ε|³` for all small `ε`. -/
theorem weak_ranking {WA WB T : A → ℝ} {k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun a => WA a - (T a - e a ^ 2 * (k * LA))) =O[l] fun a => e a ^ 3)
    (hB : (fun a => WB a - (T a - e a ^ 2 * (k * LB))) =O[l] fun a => e a ^ 3)
    (hL : LA ≤ LB) : ∃ C, ∀ᶠ a in l, WB a - WA a ≤ C * |e a| ^ 3 := by
  obtain ⟨C1, h1⟩ := hA.bound
  obtain ⟨C2, h2⟩ := hB.bound
  refine ⟨C1 + C2, ?_⟩
  filter_upwards [h1, h2] with a b1 b2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at b1 b2
  have e1 := le_abs_self (WB a - (T a - e a ^ 2 * (k * LB)))
  have e2 := neg_abs_le (WA a - (T a - e a ^ 2 * (k * LA)))
  have hq : 0 ≤ e a ^ 2 * (k * (LB - LA)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hk.le (by linarith))
  nlinarith

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (5.6) and (3.3): for bounded first-order components the discounted loss
`∑βᵗE₀[π_t² + λ̃(Ŷ_t − Ŷ*_t)²]` of Proposition 6.15 is the expected loss `ELoss` of the LQ
problem in the output gap `x = Ŷ − Ŷ*`. -/
theorem loss615_eq_ELoss {α β θ ω σ sC Φ M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1)
    {infl Y G cb q muw tau : ℕ → Ω → ℝ}
    (hb : ∀ t w, |infl t w ^ 2 + LargeDistortions.lamTilde α β θ ω σ sC Φ *
      (Y t w - LargeDistortions.YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w)
        (tau t w) - 0) ^ 2| ≤ M) (w0 : Ω) :
    Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ infl Y G cb q muw tau) w0 =
      ELoss 𝔼 β (LargeDistortions.lamTilde α β θ ω σ sC Φ) 0 infl
        (fun t w => Y t w - LargeDistortions.YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w)
          (muw t w) (tau t w)) w0 := by
  unfold ELoss
  rw [E0_tsum_eq 𝔼 h0 h1 hb w0]
  unfold Sequences.dsum LargeDistortions.loss615
  simp only [sub_zero]

/-- **Woodford (2003), Proposition 6.15 with footnote 71 and pp. 414–415 (second-order
sufficiency of the commitment plan, for ANY distortion `Φ ∈ [0, 1)`).** Let `κ > 0`,
`λ̃ > 0`, `φ = λ̃/κ`, `u` a bounded adapted cost-push process, and let two families
of feasible plans have the welfare expansions of `BridgeExtensions.prop615_first_order` with the
same transitory term `W₀` and the same terms independent of policy: family `A` with first-order
component the footnote-71 plan (`π = fnPi`, `Ŷ = Ŷ* + fnX`, `x_{−1} = 0`), family `B` with any
bounded first-order component `(π′, Ŷ* + x′)` satisfying the linear AS relation
`π′ = κx′ + βE_tπ′_{t+1} + u`. Then `W_B ≤ W_A + C|ε|³` for all small `ε`, and if the loss of
`B`'s first-order component is strictly larger, `W_B < W_A` for all small `ε ≠ 0`. -/
theorem lq_sufficiency615 (hPO : 𝔼.PullOut) {α β θ ω σ sC Φ Ybar uc κ M : ℝ}
    (hY : 0 < Ybar) (huc : 0 < uc) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) (hκ : 0 < κ)
    (hlam : 0 < LargeDistortions.lamTilde α β θ ω σ sC Φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t w, |u t w| ≤ M) (hua : 𝔼.Adapted u)
    {G1 cb1 q1 muw1 tau1 π' x' : ℕ → Ω → ℝ}
    (hb' : BoundedProc π') (hbx' : BoundedProc x') (hAS' : NKPCu 𝔼 κ β u π' x')
    (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ a in l, e a ≠ 0) {WA WB W0 T : A → ℝ} (w0 : Ω)
    (hA : (fun a => WA a - (W0 a - e a ^ 2 * (LargeDistortions.OmegaTilde Ybar uc α β θ ω σ Φ *
      Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ
        (fnPi 𝔼 β κ (LargeDistortions.lamTilde α β θ ω σ sC Φ / κ) u 0)
        (fun t w => fnX 𝔼 β κ (LargeDistortions.lamTilde α β θ ω σ sC Φ / κ) u 0 t w +
          LargeDistortions.YstarA α β θ ω σ sC Φ (G1 t w) (cb1 t w) (q1 t w) (muw1 t w)
            (tau1 t w)) G1 cb1 q1 muw1 tau1) w0) + T a)) =O[l] fun a => e a ^ 3)
    (hB : (fun a => WB a - (W0 a - e a ^ 2 * (LargeDistortions.OmegaTilde Ybar uc α β θ ω σ Φ *
      Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ π'
        (fun t w => x' t w + LargeDistortions.YstarA α β θ ω σ sC Φ (G1 t w) (cb1 t w)
          (q1 t w) (muw1 t w) (tau1 t w)) G1 cb1 q1 muw1 tau1) w0) + T a)) =O[l]
      fun a => e a ^ 3) :
    (∃ C, ∀ᶠ a in l, WB a - WA a ≤ C * |e a| ^ 3) ∧
      (ELoss 𝔼 β (LargeDistortions.lamTilde α β θ ω σ sC Φ) 0
          (fnPi 𝔼 β κ (LargeDistortions.lamTilde α β θ ω σ sC Φ / κ) u 0)
          (fnX 𝔼 β κ (LargeDistortions.lamTilde α β θ ω σ sC Φ / κ) u 0) w0 <
        ELoss 𝔼 β (LargeDistortions.lamTilde α β θ ω σ sC Φ) 0 π' x' w0 →
        ∀ᶠ a in l, WB a < WA a) := by
  set lt := LargeDistortions.lamTilde α β θ ω σ sC Φ with hlt
  set φ := lt / κ with hφd
  have hφ : 0 < φ := div_pos hlam hκ
  have hκφ : κ * φ = lt := by rw [hφd]; field_simp
  set Ys := fun t w => LargeDistortions.YstarA α β θ ω σ sC Φ (G1 t w) (cb1 t w) (q1 t w)
    (muw1 t w) (tau1 t w) with hYsd
  obtain ⟨⟨Bx, hBx⟩, -⟩ := fnX_props 𝔼 hβ0 hβ1 hκ hφ hu hua 0
  obtain ⟨Np, hNp⟩ := hb'
  obtain ⟨Nx, hNx⟩ := hbx'
  -- the plan's inflation is bounded
  have hPb : ∀ t w, |fnPi 𝔼 β κ φ u 0 t w| ≤ |φ| * (2 * (|Bx| + 1)) := fun t w => by
    simp only [fnPi, abs_neg, abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (abs_nonneg _)
    have h1 : |fnX 𝔼 β κ φ u 0 t w| ≤ |Bx| + 1 := (hBx t w).trans (by linarith [le_abs_self Bx])
    have h2 : |lagP (fun _ => (0 : ℝ)) (fnX 𝔼 β κ φ u 0) t w| ≤ |Bx| + 1 := by
      rcases t with _ | t
      · simp only [lagP, abs_zero]; positivity
      · exact (hBx t w).trans (by linarith [le_abs_self Bx])
    linarith
  have bnd : ∀ (p x : ℕ → Ω → ℝ) (P X : ℝ), (∀ t w, |p t w| ≤ P) → (∀ t w, |x t w| ≤ X) →
      ∀ t w, |p t w ^ 2 + lt * (x t w - 0) ^ 2| ≤ P ^ 2 + |lt| * X ^ 2 := by
    intro p x P X hp hx t w
    have e1 : p t w ^ 2 ≤ P ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hp t w) 2
    have e2 : (x t w - 0) ^ 2 ≤ X ^ 2 := by
      rw [sub_zero, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx t w) 2
    calc _ ≤ |p t w ^ 2| + |lt * (x t w - 0) ^ 2| := abs_add_le _ _
      _ = p t w ^ 2 + |lt| * (x t w - 0) ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg (p t w)), abs_mul, abs_of_nonneg (sq_nonneg (x t w - 0))]
      _ ≤ _ := add_le_add e1 (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
  have hLA := loss615_eq_ELoss 𝔼 (α := α) (θ := θ) (ω := ω) (σ := σ) (sC := sC) (Φ := Φ)
    hβ0.le hβ1 (infl := fnPi 𝔼 β κ φ u 0) (Y := fun t w => fnX 𝔼 β κ φ u 0 t w + Ys t w)
    (G := G1) (cb := cb1) (q := q1) (muw := muw1) (tau := tau1)
    (fun t w => by
      have := bnd (fnPi 𝔼 β κ φ u 0) (fnX 𝔼 β κ φ u 0) _ _ hPb hBx t w
      simp only [hYsd, add_sub_cancel_right] at this ⊢
      exact this) w0
  have hLB := loss615_eq_ELoss 𝔼 (α := α) (θ := θ) (ω := ω) (σ := σ) (sC := sC) (Φ := Φ)
    hβ0.le hβ1 (infl := π') (Y := fun t w => x' t w + Ys t w)
    (G := G1) (cb := cb1) (q := q1) (muw := muw1) (tau := tau1)
    (fun t w => by
      have := bnd π' x' _ _ hNp hNx t w
      simp only [hYsd, add_sub_cancel_right] at this ⊢
      exact this) w0
  simp only [hYsd, add_sub_cancel_right] at hLA hLB
  have hopt := fn71_optimal 𝔼 hPO hβ0 hβ1 hκ hφ hu hua ⟨Np, hNp⟩ ⟨Nx, hNx⟩ hAS' w0
  rw [hκφ] at hopt
  have hOm := LargeDistortions.OmegaTilde_pos hY huc hα0 hα1 hβ1 hθ hω hσ hΦ0 hΦ (β := β)
  have hA' : (fun a => WA a - ((W0 a + T a) - e a ^ 2 *
      (LargeDistortions.OmegaTilde Ybar uc α β θ ω σ Φ *
        ELoss 𝔼 β lt 0 (fnPi 𝔼 β κ φ u 0) (fnX 𝔼 β κ φ u 0) w0))) =O[l] fun a => e a ^ 3 :=
    hA.congr_left fun a => by rw [hLA]; ring
  have hB' : (fun a => WB a - ((W0 a + T a) - e a ^ 2 *
      (LargeDistortions.OmegaTilde Ybar uc α β θ ω σ Φ * ELoss 𝔼 β lt 0 π' x' w0))) =O[l]
      fun a => e a ^ 3 :=
    hB.congr_left fun a => by rw [hLB]; ring
  exact ⟨weak_ranking hOm hA' hB' hopt.1, fun hlt' => ranking_of_common he hne hOm hA' hB' hlt'⟩

end Woodford.StabilizationWelfare.TidyR5RamseySOC
