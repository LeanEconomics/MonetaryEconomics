/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotemberg
import StabilizationWelfare.NonlinearNKMarkovRamseyIFT

/-!
# A quantitative implicit function theorem for forward-looking Markov systems

Woodford (2003), *Interest and Prices*, Appendix A.3 (pp. 631–635: local determinacy of the
nonlinear model by the implicit function theorem) and Chapter 6, §1 (pp. 383–392: the one-parameter
family of economies along which the welfare approximations are taken).

The Calvo modules (`NonlinearNKMarkovGeneral.general_existence`,
`NonlinearNKMarkovLinks.uniform_uniqueness`) prove existence and local uniqueness for the
particular Calvo maps. This module abstracts the argument from the model: for ANY pair of `C¹`
maps `Q, N : ℝᵐ × ℝⁿ → ℝⁿ` with `Q(0,0) + N(0,0) = 0`, the conditions
`Φ(z)(x) = Q(e(x), z(x)) + M[N(e, z)](x) = 0` (`PhiG`) on a state space `X` with a Markov operator
`M` and disturbances `e : X → ℝᵐ` are solved near the steady state by the Newton contraction
`z ↦ z − L⁻¹Φ(z)` whenever the linearised operator `L = LG` (`v ↦ DQ v + M[DN v]`) has an inverse
with a bound `K` (`newton_exist`), and two solutions near the steady state coincide whenever `L`
satisfies the a-priori bound `‖v‖ ≤ K‖Lv‖` (`newton_unique`). The radii depend ONLY on `Q, N`
and `K`, not on `X`, `M` or `e`.

Both theorems carry a class `S` of admissible policies (all functions; adapted processes;
measurable functions; policies with a pinned coordinate), closed under the Newton step and under
pointwise limits: the solution lies in `S`, and uniqueness holds within `S`. This is what makes
the theorem reusable for the Markov, sequence-space, adapted and indeterminate cases.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergNewton

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral NonlinearNKMarkovRamseyIFT

variable {m n : ℕ} {X : Type*}

/-- Woodford (2003), App. A.3 (**the residual of the equilibrium conditions**) for maps `Q, N`,
a Markov operator `M` and disturbances `e`: `Φ(z)(x) = Q(e(x), z(x)) + M[N(e, z)](x)`. -/
noncomputable def PhiG (Q N : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
    (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (e : X → Fin m → ℝ) (z : X → Fin n → ℝ) : X → Fin n → ℝ :=
  fun x => Q (e x, z x) + Mv M (fun x' => N (e x', z x')) x

/-- Woodford (2003), App. A.3, (A.12): the linearised operator
`(Lv)(x) = DQ(0,0)(0, v(x)) + M[DN(0,0)(0, v)](x)`. -/
noncomputable def LG (Q N : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ))
    (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v : X → Fin n → ℝ) : X → Fin n → ℝ :=
  fun x => fderiv ℝ Q (0, 0) (0, v x) + Mv M (fun x' => fderiv ℝ N (0, 0) (0, v x')) x

variable {Q N : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)}

/-- Woodford (2003), App. A.3: `L` is additive in differences. -/
theorem LG_sub (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v w : X → Fin n → ℝ) :
    LG Q N M (fun x => v x - w x) = fun x => LG Q N M v x - LG Q N M w x := by
  funext x
  have h0 : ∀ a b : Fin n → ℝ, ((0 : Fin m → ℝ), a - b) = ((0 : Fin m → ℝ), a) - (0, b) :=
    fun a b => by simp
  simp only [LG, h0, map_sub]
  have := congrFun (Mv_sub M (fun x' => fderiv ℝ N (0, 0) (0, v x'))
    (fun x' => fderiv ℝ N (0, 0) (0, w x'))) x
  rw [this]; abel

/-- `‖(0, w)‖ = ‖w‖`. -/
theorem norm_pair_zero' (w : Fin n → ℝ) : ‖((0 : Fin m → ℝ), w)‖ = ‖w‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

/-- Woodford (2003), App. A.3: `L` maps bounded functions to bounded functions. -/
theorem LG_bounded {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) {v : X → Fin n → ℝ} {V : ℝ}
    (hV : 0 ≤ V) (hv : ∀ x, ‖v x‖ ≤ V) (x : X) :
    ‖LG Q N M v x‖ ≤ (‖fderiv ℝ Q (0, 0)‖ + ‖fderiv ℝ N (0, 0)‖) * V := by
  have hq : ∀ w : Fin n → ℝ, ‖fderiv ℝ Q (0, 0) (0, w)‖ ≤ ‖fderiv ℝ Q (0, 0)‖ * ‖w‖ := fun w => by
    rw [← norm_pair_zero' (m := m) w]; exact ContinuousLinearMap.le_opNorm _ _
  have hn : ∀ w : Fin n → ℝ, ‖fderiv ℝ N (0, 0) (0, w)‖ ≤ ‖fderiv ℝ N (0, 0)‖ * ‖w‖ := fun w => by
    rw [← norm_pair_zero' (m := m) w]; exact ContinuousLinearMap.le_opNorm _ _
  have h2 := Mv_norm_le hM (mul_nonneg (norm_nonneg _) hV) (fun x' => (hn (v x')).trans
    (mul_le_mul_of_nonneg_left (hv x') (norm_nonneg _))) x
  calc ‖LG Q N M v x‖ ≤ ‖fderiv ℝ Q (0, 0) (0, v x)‖ +
        ‖Mv M (fun x' => fderiv ℝ N (0, 0) (0, v x')) x‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ Q (0, 0)‖ * V + ‖fderiv ℝ N (0, 0)‖ * V :=
        add_le_add ((hq _).trans (mul_le_mul_of_nonneg_left (hv x) (norm_nonneg _))) h2
    _ = _ := by ring

/-- Woodford (2003), App. A.3: the residual minus its linearisation is the sum of the pointwise
first-order remainders of `Q` and `N`. -/
theorem resid_split (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (e : X → Fin m → ℝ) (z z' : X → Fin n → ℝ)
    (x : X) : PhiG Q N M e z x - PhiG Q N M e z' x - LG Q N M (fun x => z x - z' x) x =
      (Q (e x, z x) - Q (e x, z' x) - fderiv ℝ Q (0, 0) (0, z x - z' x)) +
      Mv M (fun x' => N (e x', z x') - N (e x', z' x') - fderiv ℝ N (0, 0) (0, z x' - z' x')) x
      := by
  have m1 := congrFun (Mv_sub M (fun x' => N (e x', z x') - N (e x', z' x'))
    (fun x' => fderiv ℝ N (0, 0) (0, z x' - z' x'))) x
  have m2 := congrFun (Mv_sub M (fun x' => N (e x', z x')) (fun x' => N (e x', z' x'))) x
  rw [m1, m2]
  simp only [PhiG, LG]
  abel

/-- Woodford (2003), App. A.3: with the uniform first-order remainders of `Q` and `N` bounded
by `η` on a ball, `‖Φz − Φz′ − L(z − z′)‖ ≤ 2η sup‖z − z′‖`. -/
theorem resid_bound {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) {η ρ : ℝ} (hη0 : 0 ≤ η)
    (hQ : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖Q (e, w) - Q (e, w') - fderiv ℝ Q (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    (hN : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖N (e, w) - N (e, w') - fderiv ℝ N (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    {e : X → Fin m → ℝ} {z z' : X → Fin n → ℝ} (he : ∀ x, ‖e x‖ ≤ ρ) (hz : ∀ x, ‖z x‖ ≤ ρ)
    (hz' : ∀ x, ‖z' x‖ ≤ ρ) {D : ℝ} (hD : ∀ x, ‖z x - z' x‖ ≤ D) (x : X) :
    ‖PhiG Q N M e z x - PhiG Q N M e z' x - LG Q N M (fun x => z x - z' x) x‖ ≤ 2 * η * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
  have e2 : ∀ x', ‖N (e x', z x') - N (e x', z' x') -
      fderiv ℝ N (0, 0) (0, z x' - z' x')‖ ≤ η * D := fun x' =>
    (hN _ _ _ (he x') (hz x') (hz' x')).trans (mul_le_mul_of_nonneg_left (hD x') hη0)
  have e1 := (hQ (e x) (z x) (z' x) (he x) (hz x) (hz' x)).trans
    (mul_le_mul_of_nonneg_left (hD x) hη0)
  have e3 := Mv_norm_le hM (mul_nonneg hη0 hD0) e2 x
  rw [resid_split]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ η * D + η * D := add_le_add e1 e3
    _ = 2 * η * D := by ring

/-- Woodford (2003), App. A.3 (**local uniqueness, uniform over state spaces and Markov
operators**): if `Q, N` are `C¹` and `K > 0`, there is `ρ > 0` depending only on `Q, N, K` such
that on every state space with every Markov operator, within every class `S` on which the
a-priori bound `‖v − w‖ ≤ K sup‖L(v − w)‖` holds, two solutions of `Φ = 0` within `ρ` of the
steady state (with disturbances within `ρ`) coincide. -/
theorem newton_unique (hQ : ContDiff ℝ 1 Q) (hN : ContDiff ℝ 1 N) {K : ℝ} (hK : 0 < K) :
    ∃ ρ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (S : (X → Fin n → ℝ) → Prop),
      (∀ v w, S v → S w → ∀ D a, (∀ x, ‖v x - w x‖ ≤ D) →
        (∀ x, ‖LG Q N M (fun x => v x - w x) x‖ ≤ a) → ∀ x, ‖v x - w x‖ ≤ K * a) →
      ∀ (e : X → Fin m → ℝ) (z z' : X → Fin n → ℝ), (∀ x, ‖e x‖ ≤ ρ) → S z → S z' →
        (∀ x, ‖z x‖ ≤ ρ) → (∀ x, ‖z' x‖ ≤ ρ) → PhiG Q N M e z = 0 → PhiG Q N M e z' = 0 →
          z = z' := by
  set η := 1 / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQr⟩ := remainder_gen hQ hη0
  obtain ⟨ρN, hρN, hNr⟩ := remainder_gen hN hη0
  set ρ := min ρQ ρN with hρ
  have hQ' : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖Q (e, w) - Q (e, w') - fderiv ℝ Q (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hQr e w w' (he.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))
      (hw'.trans (min_le_left _ _))
  have hN' : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖N (e, w) - N (e, w') - fderiv ℝ N (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hNr e w w' (he.trans (min_le_right _ _))
      (hw.trans (min_le_right _ _)) (hw'.trans (min_le_right _ _))
  refine ⟨ρ, lt_min hρQ hρN, fun X M hM S hap e z z' he hSz hSz' hz hz' hE hE' => ?_⟩
  set d : X → Fin n → ℝ := fun x => z x - z' x with hd
  have hd0 : ∀ x, ‖d x‖ ≤ 2 * ρ := fun x => by
    calc ‖d x‖ ≤ ‖z x‖ + ‖z' x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hz x, hz' x]
  have himp : ∀ U, (∀ x, ‖d x‖ ≤ U) → ∀ x, ‖d x‖ ≤ 0 + 1 / 2 * U := by
    intro U hU x
    have hres := resid_bound hM hη0.le hQ' hN' he hz hz' hU
    have hL : ∀ x, ‖LG Q N M (fun x => z x - z' x) x‖ ≤ 2 * η * U := fun x => by
      have h := hres x
      rw [hE, hE'] at h
      simpa [norm_neg] using h
    calc ‖d x‖ ≤ K * (2 * η * U) := hap z z' hSz hSz' U _ hU hL x
      _ = 0 + 1 / 2 * U := by rw [hη]; field_simp; ring
  funext x
  have h := bound_of_improve (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hd0 himp x
  have : d x = 0 := norm_le_zero_iff.1 (by simpa using h)
  exact sub_eq_zero.1 this

/-- Woodford (2003), App. A.3 (**a quantitative implicit function theorem on bounded functions:
existence, with an invariant class**). If `Q, N` are `C¹`, `Q(0,0) + N(0,0) = 0` and `K > 0`,
there is `r₀ > 0` such that for every `0 < r ≤ r₀` there is `δ > 0`, depending only on `Q, N, K`,
with: on every state space `X` with every Markov operator `M`, if `Linv` is a right inverse of
`L` on bounded functions with `‖Linv ρ‖ ≤ K sup‖ρ‖`, additive, and a left inverse on differences
of members of a class `S` that contains `0`, is invariant under the Newton step
`z ↦ z − Linv Φ(z)` on the ball and is closed under pointwise limits, then for every
disturbance with `‖e(x)‖ ≤ δ` there is a solution `z ∈ S` of `Φ(z) = 0` with `‖z(x)‖ ≤ r`. -/
theorem newton_exist (hQ : ContDiff ℝ 1 Q) (hN : ContDiff ℝ 1 N)
    (hs : Q (0, 0) + N (0, 0) = 0) {K : ℝ} (hK : 0 < K) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)),
      IsMarkov M → ∀ (Linv : (X → Fin n → ℝ) → (X → Fin n → ℝ)),
      (∀ ρ a, 0 ≤ a → (∀ x, ‖ρ x‖ ≤ a) →
        (∀ x, ‖Linv ρ x‖ ≤ K * a) ∧ LG Q N M (Linv ρ) = ρ) →
      (∀ ρ ρ' a a', 0 ≤ a → 0 ≤ a' → (∀ x, ‖ρ x‖ ≤ a) → (∀ x, ‖ρ' x‖ ≤ a') →
        Linv (fun x => ρ x - ρ' x) = fun x => Linv ρ x - Linv ρ' x) →
      ∀ (S : (X → Fin n → ℝ) → Prop),
      (∀ v w, S v → S w → ∀ D, (∀ x, ‖v x - w x‖ ≤ D) →
        Linv (LG Q N M (fun x => v x - w x)) = fun x => v x - w x) →
      ∀ (e : X → Fin m → ℝ), (∀ x, ‖e x‖ ≤ δ) →
      S 0 → (∀ z, S z → (∀ x, ‖z x‖ ≤ r) → S (fun x => z x - Linv (PhiG Q N M e z) x)) →
      (∀ (zs : ℕ → X → Fin n → ℝ) (z : X → Fin n → ℝ), (∀ k, S (zs k)) →
        (∀ x, Tendsto (fun k => zs k x) atTop (𝓝 (z x))) → S z) →
      ∃ z, S z ∧ (∀ x, ‖z x‖ ≤ r) ∧ PhiG Q N M e z = 0 := by
  set η := 1 / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQr⟩ := remainder_gen hQ hη0
  obtain ⟨ρN, hρN, hNr⟩ := remainder_gen hN hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  have hQ' : ∀ e w w', ‖e‖ ≤ r0 → ‖w‖ ≤ r0 → ‖w'‖ ≤ r0 →
      ‖Q (e, w) - Q (e, w') - fderiv ℝ Q (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hQr e w w' (he.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))
      (hw'.trans (min_le_left _ _))
  have hN' : ∀ e w w', ‖e‖ ≤ r0 → ‖w‖ ≤ r0 → ‖w'‖ ≤ r0 →
      ‖N (e, w) - N (e, w') - fderiv ℝ N (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hNr e w w' (he.trans (min_le_right _ _))
      (hw.trans (min_le_right _ _)) (hw'.trans (min_le_right _ _))
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin m → ℝ) × (Fin n → ℝ))
    r0).exists_bound_of_continuousOn hQ.continuous.continuousOn
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin m → ℝ) × (Fin n → ℝ))
    r0).exists_bound_of_continuousOn hN.continuous.continuousOn
  have hin0 : ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈ Metric.closedBall 0 r0 :=
    Metric.mem_closedBall_self hr00.le
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ _ hin0)
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN _ hin0)
  refine ⟨r0, hr00, fun r hr hrr0 => ?_⟩
  set τ := r / (4 * K) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin m → ℝ => Q (e, 0)) 0 :=
    (hQ.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hcN : ContinuousAt (fun e : Fin m → ℝ => N (e, 0)) 0 :=
    (hN.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  refine ⟨min r (min (δQ / 2) (δN / 2)), lt_min hr (lt_min (by positivity) (by positivity)),
    fun X M hM Linv hL hadd S hleft e hξ hS0 hSinv hSlim => ?_⟩
  have hξr : ∀ x, ‖e x‖ ≤ r := fun x => (hξ x).trans (min_le_left _ _)
  have hξ0 : ∀ x, ‖e x‖ ≤ r0 := fun x => (hξr x).trans hrr0
  have hPhiB : ∀ z : X → Fin n → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖PhiG Q N M e z x‖ ≤ CQ + CN := by
    intro z hz x
    have hin : ∀ x', (e x', z x') ∈ Metric.closedBall (0 : (Fin m → ℝ) × (Fin n → ℝ)) r0 :=
      fun x' => by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        exact max_le (hξ0 x') ((hz x').trans hrr0)
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (hin x))
      (Mv_norm_le hM hCN0 (fun x' => hCN _ (hin x')) x))
  set T : (X → Fin n → ℝ) → (X → Fin n → ℝ) := fun z x => z x - Linv (PhiG Q N M e z) x
    with hT
  have hcontr : ∀ z z' : X → Fin n → ℝ, S z → S z' → (∀ x, ‖z x‖ ≤ r) →
      (∀ x, ‖z' x‖ ≤ r) → ∀ D, (∀ x, ‖z x - z' x‖ ≤ D) → ∀ x, ‖T z x - T z' x‖ ≤ D / 2 := by
    intro z z' hSz hSz' hz hz' D hD x
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
    have hz0 : ∀ x, ‖z x‖ ≤ r0 := fun x => (hz x).trans hrr0
    have hz'0 : ∀ x, ‖z' x‖ ≤ r0 := fun x => (hz' x).trans hrr0
    have hLd := LG_bounded (Q := Q) (N := N) hM hD0 hD
    set c := (‖fderiv ℝ Q (0, 0)‖ + ‖fderiv ℝ N (0, 0)‖) * D
    have hc0 : 0 ≤ c := mul_nonneg (by positivity) hD0
    have hres := resid_bound hM hη0.le hQ' hN' hξ0 hz0 hz'0 hD
    have hCC : 0 ≤ CQ + CN := add_nonneg hCQ0 hCN0
    have e1 := hadd _ _ _ _ hCC hCC (hPhiB z hz) (hPhiB z' hz')
    have e2 := hadd (fun x => PhiG Q N M e z x - PhiG Q N M e z' x)
      (LG Q N M (fun x => z x - z' x)) (CQ + CN + (CQ + CN)) c (by positivity) hc0
      (fun x => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz x) (hPhiB z' hz' x))) hLd
    have e3 := hleft z z' hSz hSz' D hD
    have key : T z x - T z' x = -Linv (fun x => PhiG Q N M e z x - PhiG Q N M e z' x -
        LG Q N M (fun x => z x - z' x) x) x := by
      rw [e2, e1, e3]
      simp only [hT]
      abel
    rw [key, norm_neg]
    have hr2 := (hL _ _ (by positivity) hres).1 x
    calc _ ≤ K * (2 * η * D) := hr2
      _ = D / 2 := by rw [hη]; field_simp; ring
  have hT0 : ∀ x, ‖T 0 x‖ ≤ r / 2 := by
    intro x
    have hb : ∀ x, ‖PhiG Q N M e 0 x‖ ≤ 2 * τ := fun x => by
      have hsplit : PhiG Q N M e 0 x = (Q (e x, 0) - Q (0, 0)) +
          Mv M (fun x' => N (e x', 0) - N (0, 0)) x := by
        have hm := congrFun (Mv_sub M (fun x' => N (e x', 0)) (fun _ => N (0, 0))) x
        have hc : Mv M (fun _ : X => N (0, 0)) x = N (0, 0) := Mv_const hM _ x
        simp only [PhiG, Pi.zero_apply]
        rw [hm, hc]
        linear_combination hs
      rw [hsplit]
      have hq : ∀ x', ‖Q (e x', 0) - Q (0, 0)‖ ≤ τ := fun x' => by
        have h := hQc (x := e x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have hn : ∀ x', ‖N (e x', 0) - N (0, 0)‖ ≤ τ := fun x' => by
        have h := hNc (x := e x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ τ + τ := add_le_add (hq x) (Mv_norm_le hM hτ0.le hn x)
        _ = 2 * τ := by ring
    have h := (hL _ _ (by positivity) hb).1 x
    simp only [hT, Pi.zero_apply, zero_sub, norm_neg]
    calc _ ≤ K * (2 * τ) := h
      _ = r / 2 := by rw [hτ]; field_simp; ring
  have hball : ∀ z : X → Fin n → ℝ, S z → (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖T z x‖ ≤ r := by
    intro z hSz hz x
    have h1 := hcontr z 0 hSz hS0 hz (fun x => by simp [hr.le]) r
      (fun x => by simpa using hz x) x
    calc ‖T z x‖ ≤ ‖T z x - T 0 x‖ + ‖T 0 x‖ := by
          have := norm_add_le (T z x - T 0 x) (T 0 x); simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add h1 (hT0 x)
      _ = r := by ring
  set zs : ℕ → X → Fin n → ℝ := fun k => T^[k] 0 with hzs
  have hzsBS : ∀ k, S (zs k) ∧ ∀ x, ‖zs k x‖ ≤ r := by
    intro k
    induction k with
    | zero => exact ⟨hS0, fun x => by simp [hzs, hr.le]⟩
    | succ k ih =>
      have e : zs (k + 1) = T (zs k) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]
      exact ⟨hSinv _ ih.1 ih.2, hball _ ih.1 ih.2⟩
  have hstep : ∀ k x, ‖zs k x - zs (k + 1) x‖ ≤ r / 2 / 2 ^ k := by
    intro k
    induction k with
    | zero =>
      intro x
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hT0 x
    | succ k ih =>
      intro x
      have h := hcontr (zs (k + 1)) (zs k) (hzsBS _).1 (hzsBS _).1 (hzsBS _).2 (hzsBS _).2
        (r / 2 / 2 ^ k) (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (k + 1 + 1) = T (zs (k + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (k + 1) = T (zs k) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (k + 1) x = T (zs k) x from congrFun e2 x]
      calc _ ≤ r / 2 / 2 ^ k / 2 := h
        _ = r / 2 / 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun k => zs k x := fun x =>
    cauchySeq_of_le_geometric_two (C := r) fun k => by rw [dist_eq_norm]; exact hstep k x
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzdist : ∀ k x, ‖zs k x - z x‖ ≤ r / 2 ^ k := fun k x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun k => zs k x)
      (fun k => by rw [dist_eq_norm]; exact hstep k x) (hz x) k
    rwa [dist_eq_norm] at this
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x =>
    le_of_tendsto' ((hz x).norm) fun k => (hzsBS k).2 x
  have hSz : S z := hSlim zs z (fun k => (hzsBS k).1) hz
  have hfix : T z = z := by
    funext x
    have hlim : Tendsto (fun k => zs (k + 1) x) atTop (𝓝 (T z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun k : ℕ => r / 2 ^ k / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun k => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hg
      have e : zs (k + 1) = T (zs k) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hcontr z (zs k) hSz (hzsBS k).1 hzB (hzsBS k).2 (r / 2 ^ k) (fun x => by
        rw [norm_sub_rev]; exact hzdist k x) x
    have hlim2 : Tendsto (fun k => zs (k + 1) x) atTop (𝓝 (z x)) :=
      (hz x).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hlim hlim2
  refine ⟨z, hSz, hzB, ?_⟩
  have hl : Linv (PhiG Q N M e z) = 0 := by
    funext x
    have := congrFun hfix x
    simp only [hT] at this
    have := congrArg (fun v => z x - v) this
    simp only [sub_sub_cancel, sub_self] at this
    exact this
  obtain ⟨-, hLz⟩ := hL _ _ (add_nonneg hCQ0 hCN0) (hPhiB z hzB)
  rw [← hLz, hl]
  funext x
  have := congrFun (LG_sub (Q := Q) (N := N) M (0 : X → Fin n → ℝ) 0) x
  simp only [Pi.zero_apply, sub_self] at this
  exact this

/-- Woodford (2003), App. A.3: a right inverse with a bound that is also a left inverse on
a class gives the a-priori bound `‖v − w‖ ≤ K sup‖L(v − w)‖` on that class. -/
theorem apriori_of_linv {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} {K : ℝ}
    {Linv : (X → Fin n → ℝ) → (X → Fin n → ℝ)}
    (hL : ∀ ρ a, 0 ≤ a → (∀ x, ‖ρ x‖ ≤ a) →
        (∀ x, ‖Linv ρ x‖ ≤ K * a) ∧ LG Q N M (Linv ρ) = ρ)
    {S : (X → Fin n → ℝ) → Prop}
    (hleft : ∀ v w, S v → S w → ∀ D, (∀ x, ‖v x - w x‖ ≤ D) →
        Linv (LG Q N M (fun x => v x - w x)) = fun x => v x - w x) :
    ∀ v w, S v → S w → ∀ D a, (∀ x, ‖v x - w x‖ ≤ D) →
      (∀ x, ‖LG Q N M (fun x => v x - w x) x‖ ≤ a) → ∀ x, ‖v x - w x‖ ≤ K * a := by
  intro v w hv hw D a hD ha x
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha x)
  have h := (hL _ a ha0 ha).1 x
  rwa [hleft v w hv hw D hD] at h

end Woodford.StabilizationWelfare.NonlinearRotembergNewton
