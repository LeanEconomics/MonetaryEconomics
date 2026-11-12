/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasSurplus
import StickyPriceFiscal.ExpectationsMeasureIID

/-!
# Equation (5.38) in a probability model: active iff `γ ≠ α` (E33)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.4.1, eq. (5.38), p. 139:
the surplus responds to the latent variable and to the gap,
`s̃_{t+1} = α v*_t + γ (v_t − v*_t) + u_{t+1}`. The book says fiscal policy is active iff
`γ = 0`; `ActivePassive.active_iff_538` proves (for the abstract `ExpectationSystem`) that it is
active iff `γ ≠ α` (survey E33). Here the same is proved in every probability model with genuine
news.

## Main results

* `MRule538`: the model, a.e.; `rule538_forecast`: for every date `t` and a.e. state the forecast
  paths satisfy the perfect-foresight model `ActivePassive.Rule538` with mean-zero future shocks.
* **`mtvc_v_iff_538`**: a.e., `ρᵀ E_t v_{t+T} → 0` iff `(α − γ)(v_t − v*_t) = 0`.
* `mactive_538` (`γ ≠ α`: the transversality condition selects `v = v*` and unexpected inflation
  `= ΔE π*`), `mpassive_538` (`γ = α`: it always holds).
* **`mactive_iff_538`**: in a probability model carrying a nondegenerate mean-zero shock, fiscal
  policy under (5.38) is active iff `γ ≠ α`; `mprinted_538_false`: in the i.i.d. economy the
  printed "active iff `γ = 0`" is false.
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasActive538

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRulesMeasure ActivePassive
  SurplusProcess

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eq. (5.38), p. 139, with (5.29), (5.31)–(5.34), in a probability model:
`i_t = E_t π_{t+1}`, `s̃_{t+1} = α v*_t + γ (v_t − v*_t) + u_{t+1}`, the flows of `v*` and `v`
with unexpected inflation, `ΔE π* = −β_s ε` and the AR(1) disturbance (a.e. where expectations
appear). -/
def MRule538 (ρ α γ βs η : ℝ) (ε i p ps s v vs u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t =ᵐ[S.μ] S.E t (p (t + 1)) ∧ s (t + 1) = α • vs t + γ • (v t - vs t) + u (t + 1) ∧
    ρ • vs (t + 1) =ᵐ[S.μ] vs t - (ps (t + 1) - S.E t (ps (t + 1))) - s (t + 1) ∧
    ρ • v (t + 1) =ᵐ[S.μ] v t - (p (t + 1) - S.E t (p (t + 1))) - s (t + 1) ∧
    ps (t + 1) - S.E t (ps (t + 1)) =ᵐ[S.μ] -(βs • ε (t + 1)) ∧ u (t + 1) = η • u t + ε (t + 1)

/-- Cochrane (2023) (tool): the forecast of a future surprise is zero,
`E_t (q_{r+1} − E_r q_{r+1}) = 0` a.e. for `t ≤ r`. -/
theorem E_surprise_zero {q : Ω → ℝ} (hq : Integrable q S.μ) {t r : ℕ} (htr : t ≤ r) :
    S.E t (q - S.E r q) =ᵐ[S.μ] 0 := by
  filter_upwards [S.E_sub hq (S.integrable_E r q) t, S.E_tower htr q] with ω e1 e2
  rw [e1, Pi.sub_apply, e2, sub_self, Pi.zero_apply]

/-- Cochrane (2023), (5.38), p. 139, **the forecast paths are a perfect-foresight (5.38) model**:
for every date `t` and a.e. state, `j ↦ E_t` of `(ε, i, π, π*, s̃, v, v*, u)_{t+j}` satisfies
`ActivePassive.Rule538` under perfect foresight, with mean-zero future shocks. -/
theorem rule538_forecast {ρ α γ βs η : ℝ} {ε i p ps s v vs u : ℕ → Ω → ℝ}
    (h : MRule538 S ρ α γ βs η ε i p ps s v vs u) (hpi : ∀ t, Integrable (p t) S.μ)
    (hpsi : ∀ t, Integrable (ps t) S.μ) (hsi : ∀ t, Integrable (s t) S.μ)
    (hvi : ∀ t, Integrable (v t) S.μ) (hvsi : ∀ t, Integrable (vs t) S.μ)
    (hui : ∀ t, Integrable (u t) S.μ) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Rule538 perfectForesight ρ α γ βs η (fun j _ => S.E t (ε (t + j)) ω)
        (fun j _ => S.E t (i (t + j)) ω) (fun j _ => S.E t (p (t + j)) ω)
        (fun j _ => S.E t (ps (t + j)) ω) (fun j _ => S.E t (s (t + j)) ω)
        (fun j _ => S.E t (v (t + j)) ω) (fun j _ => S.E t (vs (t + j)) ω)
        (fun j _ => S.E t (u (t + j)) ω) ∧
      MeanZero perfectForesight (fun j (_ : Unit) => S.E t (ε (t + j)) ω) := by
  have h1 : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (i (t + j)) ω = S.E t (p (t + j + 1)) ω := fun j => by
    filter_upwards [S.E_congr (h (t + j)).1 t, S.E_tower (Nat.le_add_right t j) (p (t + j + 1))]
      with ω e1 e2
    rw [e1, e2]
  have h2 : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (s (t + j + 1)) ω = α * S.E t (vs (t + j)) ω +
      γ * (S.E t (v (t + j)) ω - S.E t (vs (t + j)) ω) + S.E t (u (t + j + 1)) ω := fun j => by
    rw [(h (t + j)).2.1]
    filter_upwards [S.E_add (((hvsi (t + j)).smul α).add (((hvi (t + j)).sub
        (hvsi (t + j))).smul γ)) (hui (t + j + 1)) t,
      S.E_add ((hvsi (t + j)).smul α) (((hvi (t + j)).sub (hvsi (t + j))).smul γ) t,
      S.E_smul α (vs (t + j)) t, S.E_smul γ (v (t + j) - vs (t + j)) t,
      S.E_sub (hvi (t + j)) (hvsi (t + j)) t] with ω e1 e2 e3 e4 e5
    rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, e4, Pi.smul_apply, Pi.smul_apply, e5,
      Pi.sub_apply, smul_eq_mul, smul_eq_mul]
  have hflow : ∀ {w q : ℕ → Ω → ℝ}, (∀ r, Integrable (w r) S.μ) → (∀ r, Integrable (q r) S.μ) →
      (∀ r, ρ • w (r + 1) =ᵐ[S.μ] w r - (q (r + 1) - S.E r (q (r + 1))) - s (r + 1)) →
      ∀ j, ∀ᵐ ω ∂S.μ, ρ * S.E t (w (t + j + 1)) ω = S.E t (w (t + j)) ω -
        S.E t (s (t + j + 1)) ω := by
    intro w q hwi hqi hfl j
    have hqq := (hqi (t + j + 1)).sub (S.integrable_E (t + j) (q (t + j + 1)))
    filter_upwards [S.E_congr (hfl (t + j)) t, S.E_smul ρ (w (t + j + 1)) t,
      S.E_sub ((hwi (t + j)).sub hqq) (hsi (t + j + 1)) t, S.E_sub (hwi (t + j)) hqq t,
      E_surprise_zero S (hqi (t + j + 1)) (Nat.le_add_right t j)] with ω e1 e2 e3 e4 e5
    rw [e2] at e1
    simp only [Pi.smul_apply, smul_eq_mul] at e1
    rw [e1, e3, Pi.sub_apply, e4, Pi.sub_apply, e5, Pi.zero_apply, sub_zero]
  have h3 := hflow hvsi hpsi fun r => (h r).2.2.1
  have h4 := hflow hvi hpi fun r => (h r).2.2.2.1
  have h5 : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (ε (t + j + 1)) ω = 0 := fun j => by
    filter_upwards [(S.E_tower (Nat.le_add_right t j) (ε (t + j + 1))).symm,
      S.E_congr (hε (t + j)) t] with ω e1 e2
    rw [e1, e2, S.E_zero]
    rfl
  have h6 : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (u (t + j + 1)) ω =
      η * S.E t (u (t + j)) ω + S.E t (ε (t + j + 1)) ω := fun j => by
    rw [(h (t + j)).2.2.2.2.2]
    filter_upwards [E_add_smul S (hεi (t + j + 1)) (hui (t + j)) η t] with ω e
    rw [show η • u (t + j) + ε (t + j + 1) = ε (t + j + 1) + η • u (t + j) by abel, e]
    ring
  have hsz : ∀ (q : ℕ → Unit → ℝ) j, surprise perfectForesight q j = 0 := fun q j => by
    funext x
    simp [surprise, perfectForesight]
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2, ae_all_iff.2 h3, ae_all_iff.2 h4,
    ae_all_iff.2 h5, ae_all_iff.2 h6] with ω e1 e2 e3 e4 e5 e6
  refine ⟨fun j => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ?_⟩
  · funext x
    exact e1 j
  · funext x
    exact e2 j
  · rw [hsz]
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero]
    exact e3 j
  · rw [hsz]
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero]
    exact e4 j
  · rw [hsz]
    funext x
    simp only [Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    rw [show t + (j + 1) = t + j + 1 by ring, e5 j, mul_zero, neg_zero]
  · funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact e6 j
  · funext x
    exact e5 j

/-- Cochrane (2023), (5.38), p. 139, survey E33, **in a probability model**: with `0 < α < 2` and
`|ρη| < 1`, a.e. the discounted forecasts of debt `ρᵀ E_t v_{t+T}` tend to zero iff
`(α − γ)(v_t − v*_t) = 0`. -/
theorem mtvc_v_iff_538 {ρ α γ βs η : ℝ} (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε i p ps s v vs u : ℕ → Ω → ℝ} (h : MRule538 S ρ α γ βs η ε i p ps s v vs u)
    (hpi : ∀ t, Integrable (p t) S.μ) (hpsi : ∀ t, Integrable (ps t) S.μ)
    (hsi : ∀ t, Integrable (s t) S.μ) (hvi : ∀ t, Integrable (v t) S.μ)
    (hvsi : ∀ t, Integrable (vs t) S.μ) (hui : ∀ t, Integrable (u t) S.μ)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hva : StronglyAdapted S.𝓕 v) (hvsa : StronglyAdapted S.𝓕 vs) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (Tendsto (fun T => ρ ^ T * S.E t (v (t + T)) ω) atTop (𝓝 0) ↔
      (α - γ) * (v t ω - vs t ω) = 0) := by
  filter_upwards [rule538_forecast S h hpi hpsi hsi hvi hvsi hui hεi hε t] with ω ⟨hR, hm⟩
  have := tvc_v_iff_538 perfectForesight hα hη hR hm (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) 0 ()
  simp only [zero_add, add_zero, S.E_of_stronglyMeasurable (hva t) (hvi t),
    S.E_of_stronglyMeasurable (hvsa t) (hvsi t)] at this
  exact this

/-- Cochrane (2023), (5.38), p. 139, survey E33, **in a probability model**: for `γ ≠ α`, debt
satisfying the transversality condition has `v = v*` and unexpected inflation equal to the
target's, a.e. at every date. -/
theorem mactive_538 {ρ α γ βs η : ℝ} (hα : |1 - α| < 1) (hη : |ρ * η| < 1) (hγ : γ ≠ α)
    {ε i p ps s v vs u : ℕ → Ω → ℝ} (h : MRule538 S ρ α γ βs η ε i p ps s v vs u)
    (hpi : ∀ t, Integrable (p t) S.μ) (hpsi : ∀ t, Integrable (ps t) S.μ)
    (hsi : ∀ t, Integrable (s t) S.μ) (hvi : ∀ t, Integrable (v t) S.μ)
    (hvsi : ∀ t, Integrable (vs t) S.μ) (hui : ∀ t, Integrable (u t) S.μ)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hva : StronglyAdapted S.𝓕 v) (hvsa : StronglyAdapted S.𝓕 vs)
    (htv : TidyR6MeasFiscalNK.MTVC S ρ v) :
    ∀ t, v t =ᵐ[S.μ] vs t ∧
      p (t + 1) - S.E t (p (t + 1)) =ᵐ[S.μ] ps (t + 1) - S.E t (ps (t + 1)) := by
  have hvv : ∀ t, v t =ᵐ[S.μ] vs t := fun t => by
    filter_upwards [mtvc_v_iff_538 S hα hη h hpi hpsi hsi hvi hvsi hui hεi hε hva hvsa t,
      htv.2 t] with ω e1 e2
    have := (mul_eq_zero.mp (e1.1 e2)).resolve_left (sub_ne_zero.mpr (Ne.symm hγ))
    linarith
  intro t
  refine ⟨hvv t, ?_⟩
  filter_upwards [(h t).2.2.1, (h t).2.2.2.1, hvv t, hvv (t + 1)] with ω e1 e2 e3 e4
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2 ⊢
  rw [e3, e4] at e2
  linarith

/-- Cochrane (2023), (5.38), p. 139, survey E33, **in a probability model**: for `γ = α` the
transversality condition holds whatever unexpected inflation is. -/
theorem mpassive_538 {ρ α βs η : ℝ} (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε i p ps s v vs u : ℕ → Ω → ℝ} (h : MRule538 S ρ α α βs η ε i p ps s v vs u)
    (hpi : ∀ t, Integrable (p t) S.μ) (hpsi : ∀ t, Integrable (ps t) S.μ)
    (hsi : ∀ t, Integrable (s t) S.μ) (hvi : ∀ t, Integrable (v t) S.μ)
    (hvsi : ∀ t, Integrable (vs t) S.μ) (hui : ∀ t, Integrable (u t) S.μ)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hva : StronglyAdapted S.𝓕 v) (hvsa : StronglyAdapted S.𝓕 vs) :
    TidyR6MeasFiscalNK.MTVC S ρ v := by
  refine ⟨hvi, fun t => ?_⟩
  filter_upwards [mtvc_v_iff_538 S hα hη h hpi hpsi hsi hvi hvsi hui hεi hε hva hvsa t]
    with ω e
  exact e.2 (by rw [sub_self, zero_mul])

/-- Cochrane (2023), p. 139, in a probability model: fiscal policy under (5.38) is "active" if in
every solution (integrable, adapted, mean-zero shocks) whose debt satisfies the transversality
condition, unexpected inflation equals the target's a.e. -/
def MActive538 (ρ α γ βs η : ℝ) : Prop :=
  ∀ ε i p ps s v vs u : ℕ → Ω → ℝ, MRule538 S ρ α γ βs η ε i p ps s v vs u →
    (∀ t, Integrable (p t) S.μ) → (∀ t, Integrable (ps t) S.μ) → (∀ t, Integrable (s t) S.μ) →
    (∀ t, Integrable (v t) S.μ) → (∀ t, Integrable (vs t) S.μ) →
    (∀ t, Integrable (u t) S.μ) → (∀ t, Integrable (ε t) S.μ) →
    (∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) → StronglyAdapted S.𝓕 v → StronglyAdapted S.𝓕 vs →
    TidyR6MeasFiscalNK.MTVC S ρ v →
    ∀ t, p (t + 1) - S.E t (p (t + 1)) =ᵐ[S.μ] ps (t + 1) - S.E t (ps (t + 1))

/-- Cochrane (2023), (5.38), p. 139, survey E33 (the corrected statement), **in a probability
model**: if the model carries a nondegenerate shock — integrable `δ_t`, known at `t + 1`,
`E_t δ_t = 0` a.e., `δ_0` not a.e. zero — then fiscal policy under (5.38) is active iff
`γ ≠ α`. -/
theorem mactive_iff_538 {ρ α γ βs η : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {δ : ℕ → Ω → ℝ} (hδm : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (δ t))
    (hδi : ∀ t, Integrable (δ t) S.μ) (hδ : ∀ t, S.E t (δ t) =ᵐ[S.μ] 0)
    (hδ0 : ¬ δ 0 =ᵐ[S.μ] 0) :
    MActive538 S ρ α γ βs η ↔ γ ≠ α := by
  constructor
  · intro hA hγ
    subst hγ
    set v' := gammaPath ρ γ 0 δ 0
    set s' := succPath (fun t => γ • v' t)
    set vs' := latentPath ρ s'
    set π' := succPath δ
    have hv'k : ∀ t, StronglyMeasurable[S.𝓕 t] (v' t) ∧ Integrable (v' t) S.μ := by
      intro t
      induction t with
      | zero => exact ⟨stronglyMeasurable_zero, integrable_zero _ _ _⟩
      | succ t ih =>
        simp only [v', gammaPath]
        exact ⟨((((ih.1.mono (S.𝓕.mono (Nat.le_succ t))).const_smul _).sub (hδm t)).sub
          stronglyMeasurable_zero).const_smul _,
          (((ih.2.smul _).sub (hδi t)).sub (integrable_zero _ _ _)).smul _⟩
    have hs'i : ∀ t, StronglyMeasurable[S.𝓕 t] (s' t) ∧ Integrable (s' t) S.μ := by
      intro t
      cases t with
      | zero => exact ⟨stronglyMeasurable_zero, integrable_zero _ _ _⟩
      | succ t =>
        exact ⟨((hv'k t).1.mono (S.𝓕.mono (Nat.le_succ t))).const_smul _,
          (hv'k t).2.smul _⟩
    have hvs'k : ∀ t, StronglyMeasurable[S.𝓕 t] (vs' t) ∧ Integrable (vs' t) S.μ := by
      intro t
      induction t with
      | zero => exact ⟨stronglyMeasurable_zero, integrable_zero _ _ _⟩
      | succ t ih =>
        simp only [vs', latentPath]
        exact ⟨((ih.1.mono (S.𝓕.mono (Nat.le_succ t))).sub (hs'i (t + 1)).1).const_smul _,
          (ih.2.sub (hs'i (t + 1)).2).smul _⟩
    have hπ'i : ∀ t, Integrable (π' t) S.μ := fun t => by
      cases t with
      | zero => exact integrable_zero _ _ _
      | succ t => exact hδi t
    have hR : MRule538 S ρ γ γ βs η 0 0 π' 0 s' v' vs' 0 := by
      intro t
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · filter_upwards [hδ t] with ω e
        simp only [π', succPath]
        exact e.symm
      · simp only [s', succPath, Pi.zero_apply, add_zero, smul_sub]
        abel
      · refine Eventually.of_forall fun ω => ?_
        simp only [vs', latentPath, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
          S.E_zero, sub_zero]
        field_simp
      · filter_upwards [hδ t] with ω e
        simp only [v', gammaPath, π', succPath, s', Pi.smul_apply, Pi.sub_apply,
          Pi.zero_apply, smul_eq_mul, e, sub_zero]
        field_simp
        ring
      · refine Eventually.of_forall fun ω => ?_
        simp [S.E_zero]
      · simp
    have hint0 : ∀ t, Integrable ((0 : ℕ → Ω → ℝ) t) S.μ := fun t => integrable_zero _ _ _
    have hz : ∀ t, S.E t ((0 : ℕ → Ω → ℝ) (t + 1)) =ᵐ[S.μ] 0 := fun t =>
      Eventually.of_forall fun ω => by simp [S.E_zero]
    have htv := mpassive_538 S hα hη hR hπ'i hint0 (fun t => (hs'i t).2) (fun t => (hv'k t).2)
      (fun t => (hvs'k t).2) hint0 hint0 hz (fun t => (hv'k t).1) (fun t => (hvs'k t).1)
    have h0 := hA 0 0 π' 0 s' v' vs' 0 hR hπ'i hint0 (fun t => (hs'i t).2)
      (fun t => (hv'k t).2) (fun t => (hvs'k t).2) hint0 hint0 hz (fun t => (hv'k t).1)
      (fun t => (hvs'k t).1) htv 0
    refine hδ0 ?_
    filter_upwards [h0, hδ 0] with ω e1 e2
    simp only [π', succPath, Pi.sub_apply, Pi.zero_apply, S.E_zero] at e1
    rw [e2] at e1
    simpa using e1
  · intro hγ ε i p ps s v vs u h hpi hpsi hsi hvi hvsi hui hεi hε hva hvsa htv t
    exact (mactive_538 S hα hη hγ h hpi hpsi hsi hvi hvsi hui hεi hε hva hvsa htv t).2

open ExpectationsMeasureIID in
/-- Cochrane (2023), p. 139 ("The condition for active fiscal policy is γ = 0, not α = 0"),
survey E33, **in a genuine probability model**: in the i.i.d. economy with bounded mean-zero
shocks of positive variance, with `ρ = 1`, `η = 0`, `α = 1/10`, the rule with `γ = 1/5 ≠ 0` is
active, so the printed criterion "active iff `γ = 0`" is false. -/
theorem mprinted_538_false (ν : ProbabilityMeasure ℝ) {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (βs : ℝ) :
    MActive538 (iidSystem ν) 1 (1 / 10) (1 / 5) βs 0 ∧ (1 / 5 : ℝ) ≠ 0 := by
  set S := iidSystem ν
  have hm : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (shock (t + 1)) := fun t =>
    (measurable_shock ν le_rfl).stronglyMeasurable
  have hi : ∀ t, Integrable (shock (t + 1)) S.μ := fun t =>
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable (hm t)
      (shock_ae_bdd ν hbdd (t + 1))).integrable
  have hα : |1 - (1 / 10 : ℝ)| < 1 := by norm_num [abs_of_pos]
  have hne : ¬ shock (0 + 1) =ᵐ[S.μ] 0 := fun h =>
    shock_not_ae_E hmean hvar hσ 0 (h.trans (E_shock_zero hmean 0).symm)
  refine ⟨(mactive_iff_538 S one_ne_zero hα (by simp) (δ := fun t => shock (t + 1)) hm hi
    (fun t => E_shock_zero hmean t) hne).2 (by norm_num), by norm_num⟩

end Cochrane.StickyPriceFiscal.TidyR6MeasActive538
