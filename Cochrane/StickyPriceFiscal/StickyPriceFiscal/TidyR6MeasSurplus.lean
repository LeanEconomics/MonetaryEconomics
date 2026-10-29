/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasFiscalNK

/-!
# The surplus process, the selection of `v = v*` and alternative surpluses in a probability model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.4, eqs. (5.22)–(5.28),
pp. 134–137, §5.4.1, eqs. (5.29)–(5.35), pp. 137–138, §5.4.4, p. 146, and §5.6,
eqs. (5.82)–(5.84), pp. 160–162, restated with **measure-theoretic expectations**
(`ExpectationsMeasure.MeasExpectationSystem`, a.e. equations). The core modules
`SurplusProcess`, `ActivePassive` and `AltSurplus` prove these for the abstract
`ExpectationSystem` only.

The bridge (`surplus_forecast`): for every date `t` and almost every state, the forecast sequences
`j ↦ E_t ε_{t+j}`, `E_t s̃_{t+j}`, `E_t v*_{t+j}`, `E_t u_{t+j}` form a perfect-foresight surplus
process (`SurplusProcess.IsSurplusProc` under `perfectForesight`) with mean-zero future shocks, so
the core present-value results apply state by state.

## Main results

* `msurplus_adapted`: `u`, `v*`, `s̃` are adapted and integrable.
* **`mvstar_eq_pv`** (p. 136): `v*_t = ∑_j ρʲ E_t s̃_{t+1+j}` a.e., genuine series (`ρ ≠ 0`,
  `|1 − α| < 1`, `|ρη| < 1`); `msummable_pv`.
* **`minnov_pv`** ((5.28)): `∑_j ρʲ ΔE_{t+1} s̃_{t+1+j} = β_s ε_{t+1}` a.e.
* The frictionless model (5.27) / (5.29)–(5.34): `MFrictionless`, `mpv_of_tvc` (with the
  transversality condition, debt is the present value of surpluses);
  **`mselect`** (§5.4.1, p. 137): with the surplus process, `v = v*` and
  `ΔE_{t+1} π_{t+1} = −β_s ε_{t+1}` a.e. (survey E32's selection, by the transversality
  condition).
* §5.4.4, p. 146: **`mar1_surplus_inflation`**: AR(1) surpluses give
  `ΔE_{t+1} π_{t+1} = −ε_{t+1}/(1 − ρη)` a.e.
* §5.6, (5.82)–(5.84): **`malt_unexpected_inflation`**: backed `s*` (a surplus process with
  `β_s = 0`) plus unbacked AR(1) `ŝ` give `ΔE_{t+1} π_{t+1} = −ε̂_{t+1}/(1 − ρη̂)` a.e. and
  `v_t = v*_t + η̂ ŝ_t/(1 − ρη̂)`; `malt_v_closed_form`: `v ≠ v*` wherever `η̂ ŝ_t ≠ 0`.
* (5.36)–(5.37): **`mgamma_passive_iff`**: every debt path under the rule `s̃ = γv + u` satisfies
  the transversality condition, whatever the unexpected inflation, iff `0 < γ < 2` (E6).
* (5.42), observational equivalence: `MTarget`, `mmodelA_unique` (active fiscal policy reproduces
  the target), `MActiveMoney`, `mmodelB_unique` (active money `|φ| > 1` with passive fiscal policy
  reproduces it), **`mobservationally_equivalent`**. Tool: `msurprise_eq`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasSurplus

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRulesMeasure SurplusProcess

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), (5.22)–(5.24), p. 134 (tool): the processes of a surplus process are adapted
and integrable when the shocks are, and `v*₀`, `u₀` are integrable and known at date `0`. -/
theorem msurplus_adapted {ρ α βs η : ℝ} (hρ : ρ ≠ 0) {ε s vs u : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : StronglyAdapted S.𝓕 ε)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0))
    (hv0i : Integrable (vs 0) S.μ) (hu0 : StronglyMeasurable[S.𝓕 0] (u 0))
    (hu0i : Integrable (u 0) S.μ) :
    StronglyAdapted S.𝓕 u ∧ StronglyAdapted S.𝓕 vs ∧ (∀ t, Integrable (u t) S.μ) ∧
      (∀ t, Integrable (vs t) S.μ) ∧ (∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (s (t + 1))) ∧
      ∀ t, Integrable (s (t + 1)) S.μ := by
  have key : ∀ t, (StronglyMeasurable[S.𝓕 t] (u t) ∧ Integrable (u t) S.μ) ∧
      (StronglyMeasurable[S.𝓕 t] (vs t) ∧ Integrable (vs t) S.μ) := by
    intro t
    induction t with
    | zero => exact ⟨⟨hu0, hu0i⟩, ⟨hv0, hv0i⟩⟩
    | succ t ih =>
      obtain ⟨⟨hum, hui⟩, ⟨hvm, hvi⟩⟩ := ih
      have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
      obtain ⟨h1, h2, h3⟩ := h t
      have hu : StronglyMeasurable[S.𝓕 (t + 1)] (u (t + 1)) ∧ Integrable (u (t + 1)) S.μ := by
        rw [h3]
        exact ⟨((hum.mono hmono).const_smul η).add (hεa (t + 1)),
          (hui.smul η).add (hεi (t + 1))⟩
      have hs : s (t + 1) = α • vs t + u (t + 1) := h1
      have hv : vs (t + 1) = ρ⁻¹ • ((vs t + βs • ε (t + 1)) - (α • vs t + u (t + 1))) := by
        rw [← hs, ← h2, smul_smul, inv_mul_cancel₀ hρ, one_smul]
      refine ⟨hu, ?_⟩
      rw [hv]
      exact ⟨((((hvm.mono hmono).add ((hεa (t + 1)).const_smul βs)).sub
        (((hvm.mono hmono).const_smul α).add hu.1))).const_smul _,
        (((hvi.add ((hεi (t + 1)).smul βs)).sub ((hvi.smul α).add hu.2))).smul _⟩
  refine ⟨fun t => (key t).1.1, fun t => (key t).2.1, fun t => (key t).1.2, fun t => (key t).2.2,
    fun t => ?_, fun t => ?_⟩
  · rw [(h t).1]
    exact (((key t).2.1.mono (S.𝓕.mono (Nat.le_succ t))).const_smul α).add (key (t + 1)).1.1
  · rw [(h t).1]
    exact ((key t).2.2.smul α).add (key (t + 1)).1.2

/-- Cochrane (2023), (5.22)–(5.24), pp. 134–135, **the forecast paths are a perfect-foresight
surplus process**: for every date `t` and a.e. state, `j ↦ E_t` of `ε_{t+j}, s̃_{t+j}, v*_{t+j},
u_{t+j}` satisfies (5.22)–(5.24) for `j ≥ 0` with zero forecasts of the future shocks. -/
theorem surplus_forecast {ρ α βs η : ℝ} (hρ : ρ ≠ 0) {ε s vs u : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α βs η ε s vs u) (hεa : StronglyAdapted S.𝓕 ε)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0)) (hv0i : Integrable (vs 0) S.μ)
    (hu0 : StronglyMeasurable[S.𝓕 0] (u 0)) (hu0i : Integrable (u 0) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, IsSurplusProc ρ α βs η (fun j (_ : Unit) => S.E t (ε (t + j)) ω)
        (fun j _ => S.E t (s (t + j)) ω) (fun j _ => S.E t (vs (t + j)) ω)
        (fun j _ => S.E t (u (t + j)) ω) ∧
      MeanZero perfectForesight (fun j (_ : Unit) => S.E t (ε (t + j)) ω) := by
  obtain ⟨-, -, hui, hvi, -, hsi⟩ := msurplus_adapted S hρ h hεa hεi hv0 hv0i hu0 hu0i
  have h1 : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (s (t + j + 1)) ω =
      α * S.E t (vs (t + j)) ω + S.E t (u (t + j + 1)) ω := by
    intro j
    rw [(h (t + j)).1]
    filter_upwards [E_comb S (hvi (t + j)) (hui (t + j + 1)) α 1 t] with ω e
    have : α • vs (t + j) + u (t + j + 1) = α • vs (t + j) + (1 : ℝ) • u (t + j + 1) := by
      rw [one_smul]
    rw [this, e, one_mul]
  have h2 : ∀ j, ∀ᵐ ω ∂S.μ, ρ * S.E t (vs (t + j + 1)) ω =
      S.E t (vs (t + j)) ω + βs * S.E t (ε (t + j + 1)) ω - S.E t (s (t + j + 1)) ω := by
    intro j
    filter_upwards [S.E_congr (by rw [(h (t + j)).2.1] : ρ • vs (t + j + 1) =ᵐ[S.μ]
        vs (t + j) + βs • ε (t + j + 1) - s (t + j + 1)) t, S.E_smul ρ (vs (t + j + 1)) t,
      S.E_sub ((hvi (t + j)).add ((hεi (t + j + 1)).smul βs)) (hsi (t + j)) t,
      E_add_smul S (hvi (t + j)) (hεi (t + j + 1)) βs t] with ω e1 e2 e3 e4
    rw [e2] at e1
    simp only [Pi.smul_apply, smul_eq_mul] at e1
    rw [e1, e3, Pi.sub_apply, e4]
  have h3 : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (u (t + j + 1)) ω =
      η * S.E t (u (t + j)) ω + S.E t (ε (t + j + 1)) ω := by
    intro j
    rw [(h (t + j)).2.2]
    filter_upwards [E_comb S (hui (t + j)) (hεi (t + j + 1)) η 1 t] with ω e
    have : η • u (t + j) + ε (t + j + 1) = η • u (t + j) + (1 : ℝ) • ε (t + j + 1) := by
      rw [one_smul]
    rw [this, e, one_mul]
  have h4 : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (ε (t + j + 1)) ω = 0 := by
    intro j
    filter_upwards [(S.E_tower (Nat.le_add_right t j) (ε (t + j + 1))).symm,
      S.E_congr (hε (t + j)) t] with ω e1 e2
    rw [e1, e2, S.E_zero]
    rfl
  filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2, ae_all_iff.2 h3, ae_all_iff.2 h4]
    with ω e1 e2 e3 e4
  refine ⟨fun j => ⟨?_, ?_, ?_⟩, fun j => ?_⟩
  · funext x
    exact e1 j
  · funext x
    exact e2 j
  · funext x
    exact e3 j
  · funext x
    exact e4 j

/-- Cochrane (2023), p. 136 (`v*` is the present value of surpluses), **in a probability model**:
for `ρ ≠ 0`, `|1 − α| < 1`, `|ρη| < 1`, mean-zero integrable adapted shocks and integrable
`𝓕₀`-measurable `v*₀`, `u₀`, a.e. `v*_t = ∑_j ρʲ E_t s̃_{t+1+j}` (a genuine series). -/
theorem mvstar_eq_pv {ρ α βs η : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε s vs u : ℕ → Ω → ℝ} (h : IsSurplusProc ρ α βs η ε s vs u)
    (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0))
    (hv0i : Integrable (vs 0) S.μ) (hu0 : StronglyMeasurable[S.𝓕 0] (u 0))
    (hu0i : Integrable (u 0) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (s (t + 1 + j)) ω) (vs t ω) := by
  obtain ⟨-, hva, -, hvi, -, -⟩ := msurplus_adapted S hρ h hεa hεi hv0 hv0i hu0 hu0i
  filter_upwards [surplus_forecast S hρ h hεa hεi hε hv0 hv0i hu0 hu0i t] with ω ⟨hp, hm⟩
  have := vstar_eq_pv perfectForesight hρ hα hη hp (fun _ => rfl) hm rfl rfl 0 ()
  simp only [zero_add, add_zero, S.E_of_stronglyMeasurable (hva t) (hvi t)] at this
  convert this using 3 with j
  rw [add_assoc]
  rfl

/-- Cochrane (2023), p. 136 (tool): the discounted surplus forecasts are absolutely summable a.e. -/
theorem msummable_pv {ρ α βs η : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε s vs u : ℕ → Ω → ℝ} (h : IsSurplusProc ρ α βs η ε s vs u)
    (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0))
    (hv0i : Integrable (vs 0) S.μ) (hu0 : StronglyMeasurable[S.𝓕 0] (u 0))
    (hu0i : Integrable (u 0) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Summable (fun j => ρ ^ j * S.E t (s (t + 1 + j)) ω) := by
  filter_upwards [mvstar_eq_pv S hρ hα hη h hεa hεi hε hv0 hv0i hu0 hu0i t] with ω h
  exact h.summable

/-- Cochrane (2023), eq. (5.28), p. 135, **in a probability model**: the present value of the
surplus news is `β_s ε_{t+1}`: a.e.
`∑_j ρʲ (E_{t+1} s̃_{t+1+j} − E_t s̃_{t+1+j}) = β_s ε_{t+1}`. -/
theorem minnov_pv {ρ α βs η : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε s vs u : ℕ → Ω → ℝ} (h : IsSurplusProc ρ α βs η ε s vs u)
    (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0))
    (hv0i : Integrable (vs 0) S.μ) (hu0 : StronglyMeasurable[S.𝓕 0] (u 0))
    (hu0i : Integrable (u 0) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * (S.E (t + 1) (s (t + 1 + j)) ω -
      S.E t (s (t + 1 + j)) ω)) (βs * ε (t + 1) ω) := by
  obtain ⟨-, -, -, -, hsm, hsi⟩ := msurplus_adapted S hρ h hεa hεi hv0 hv0i hu0 hu0i
  filter_upwards [mvstar_eq_pv S hρ hα hη h hεa hεi hε hv0 hv0i hu0 hu0i t,
    mvstar_eq_pv S hρ hα hη h hεa hεi hε hv0 hv0i hu0 hu0i (t + 1)] with ω h0 h1
  have H1 : HasSum (fun j => ρ ^ j * S.E (t + 1) (s (t + 1 + j)) ω)
      (s (t + 1) ω + ρ * vs (t + 1) ω) := by
    rw [← hasSum_nat_add_iff' 1]
    convert h1.mul_left ρ using 1
    · funext j
      rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega, pow_succ]
      ring
    · simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero,
        S.E_of_stronglyMeasurable (hsm t) (hsi t)]
      ring
  have := H1.sub h0
  convert this using 1
  · funext j
    ring
  · have e := congrFun (h t).2.1 ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e
    linarith

/-! ### The frictionless model and the selection of `v = v*` -/

/-- Cochrane (2023), (5.27), p. 135 and (5.29), (5.32), p. 137, in a probability model: the
frictionless model, `i_t = E_t π_{t+1}` and `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (a.e.). -/
def MFrictionless (ρ : ℝ) (i p s v : ℕ → Ω → ℝ) : Prop :=
  (∀ t, i t =ᵐ[S.μ] S.E t (p (t + 1))) ∧
    ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + i t - p (t + 1) - s (t + 1)

/-- Cochrane (2023), pp. 135–136, **in a probability model**: in the frictionless model with
adapted integrable `π`, `s̃` and debt satisfying the transversality condition, if the surplus
forecasts are summable then `v_t = ∑_j ρʲ E_t s̃_{t+1+j}` a.e. -/
theorem mpv_of_tvc {ρ : ℝ} {i p s v : ℕ → Ω → ℝ} (hf : MFrictionless S ρ i p s v)
    (hva : StronglyAdapted S.𝓕 v) (htvc : TidyR6MeasFiscalNK.MTVC S ρ v)
    (hpi : ∀ t, Integrable (p t) S.μ)
    (hsi : ∀ t, Integrable (s (t + 1)) S.μ) (t : ℕ)
    (hsum : ∀ᵐ ω ∂S.μ, Summable (fun j => ρ ^ j * S.E t (s (t + 1 + j)) ω)) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (s (t + 1 + j)) ω) (v t ω) := by
  obtain ⟨hvi, hT⟩ := htvc
  -- `v_r = E_r s_{r+1} + ρ E_r v_{r+1}` a.e.
  have hrec : ∀ r, ∀ᵐ ω ∂S.μ, v r ω = S.E r (s (r + 1)) ω + ρ * S.E r (v (r + 1)) ω := by
    intro r
    have hv' : v r =ᵐ[S.μ] (s (r + 1) + ρ • v (r + 1)) + (p (r + 1) - S.E r (p (r + 1))) := by
      filter_upwards [hf.2 r, hf.1 r] with ω e1 e2
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e1 e2 ⊢
      rw [e2] at e1
      linarith
    have hn : S.E r (p (r + 1) - S.E r (p (r + 1))) =ᵐ[S.μ] 0 := by
      filter_upwards [S.E_sub (hpi (r + 1)) (S.integrable_E r (p (r + 1))) r] with ω e
      rw [e, Pi.sub_apply, S.E_E_self, sub_self, Pi.zero_apply]
    filter_upwards [S.E_congr hv' r, S.E_add ((hsi r).add ((hvi (r + 1)).smul ρ))
      ((hpi (r + 1)).sub (S.integrable_E r (p (r + 1)))) r, hn,
      E_add_smul S (hsi r) (hvi (r + 1)) ρ r] with ω e1 e2 e3 e4
    rw [← S.E_of_stronglyMeasurable (hva r) (hvi r), e1, e2, Pi.add_apply, e3, e4]
    simp
  -- iterate
  have hit : ∀ n, ∀ᵐ ω ∂S.μ, v t ω = ∑ j ∈ Finset.range n, ρ ^ j * S.E t (s (t + 1 + j)) ω +
      ρ ^ n * S.E t (v (t + n)) ω := by
    intro n
    induction n with
    | zero =>
      refine Eventually.of_forall fun ω => ?_
      simp [S.E_of_stronglyMeasurable (hva t) (hvi t)]
    | succ n ih =>
      have hr' := hrec (t + n)
      have hr'' : v (t + n) =ᵐ[S.μ] S.E (t + n) (s (t + n + 1)) + ρ • S.E (t + n) (v (t + n + 1)) :=
        hr'
      filter_upwards [ih, S.E_congr hr'' t, E_add_smul S (S.integrable_E (t + n) (s (t + n + 1)))
        (S.integrable_E (t + n) (v (t + n + 1))) ρ t,
        S.E_tower (Nat.le_add_right t n) (s (t + n + 1)),
        S.E_tower (Nat.le_add_right t n) (v (t + n + 1))] with ω e1 e2 e3 e4 e5
      rw [e1, e2, e3, e4, e5, Finset.sum_range_succ, show t + 1 + n = t + n + 1 by omega,
        show t + (n + 1) = t + n + 1 by omega, pow_succ]
      ring
  filter_upwards [ae_all_iff.2 hit, hT t, hsum] with ω e1 e2 e3
  have hlim : Tendsto (fun n => ∑ j ∈ Finset.range n, ρ ^ j * S.E t (s (t + 1 + j)) ω) atTop
      (𝓝 (v t ω)) := by
    have := (tendsto_const_nhds (x := v t ω)).sub e2
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    rw [e1 n]
    ring
  have heq := tendsto_nhds_unique e3.hasSum.tendsto_sum_nat hlim
  rw [← heq]
  exact e3.hasSum

/-- Cochrane (2023) (tool): in the frictionless model, unexpected inflation is
`π_{t+1} − E_t π_{t+1} = v_t − ρ v_{t+1} − s̃_{t+1}` a.e. -/
theorem msurprise_eq {ρ : ℝ} {i p s v : ℕ → Ω → ℝ} (hf : MFrictionless S ρ i p s v) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, p (t + 1) ω - S.E t (p (t + 1)) ω = v t ω - ρ * v (t + 1) ω - s (t + 1) ω := by
  filter_upwards [hf.1 t, hf.2 t] with ω e1 e2
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e1 e2
  rw [e1] at e2
  linarith

/-- Cochrane (2023), §5.4.1, p. 137 (debt that cannot explode means `v_t = v*_t`) and
(5.27)–(5.28),
**in a probability model**: in the frictionless model with the surplus process (5.22)–(5.24)
(`ρ ≠ 0`, `|1 − α| < 1`, `|ρη| < 1`), debt satisfying the transversality condition equals `v*`
a.e., and unexpected inflation is `ΔE_{t+1} π_{t+1} = −β_s ε_{t+1}` a.e. -/
theorem mselect {ρ α βs η : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε s vs u i p v : ℕ → Ω → ℝ} (h : IsSurplusProc ρ α βs η ε s vs u)
    (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0))
    (hv0i : Integrable (vs 0) S.μ) (hu0 : StronglyMeasurable[S.𝓕 0] (u 0))
    (hu0i : Integrable (u 0) S.μ) (hf : MFrictionless S ρ i p s v)
    (hva : StronglyAdapted S.𝓕 v) (htvc : TidyR6MeasFiscalNK.MTVC S ρ v)
    (hpi : ∀ t, Integrable (p t) S.μ) :
    ∀ t, v t =ᵐ[S.μ] vs t ∧
      (fun ω => p (t + 1) ω - S.E t (p (t + 1)) ω) =ᵐ[S.μ] -(βs • ε (t + 1)) := by
  obtain ⟨-, -, -, -, -, hsi⟩ := msurplus_adapted S hρ h hεa hεi hv0 hv0i hu0 hu0i
  have hvv : ∀ t, v t =ᵐ[S.μ] vs t := by
    intro t
    filter_upwards [mpv_of_tvc S hf hva htvc hpi hsi t
      (msummable_pv S hρ hα hη h hεa hεi hε hv0 hv0i hu0 hu0i t),
      mvstar_eq_pv S hρ hα hη h hεa hεi hε hv0 hv0i hu0 hu0i t] with ω e1 e2
    exact e1.unique e2
  intro t
  refine ⟨hvv t, ?_⟩
  filter_upwards [msurprise_eq S hf t, hvv t, hvv (t + 1)] with ω e1 e2 e3
  have e4 := congrFun (h t).2.1 ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e4
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, e3]
  linarith

/-- Cochrane (2023), §5.4.4, p. 146, **in a probability model**: with AR(1) surpluses
`s̃_{t+1} = η s̃_t + ε_{t+1}` (mean-zero integrable adapted shocks, `|ρη| < 1`), in the
frictionless model with debt satisfying the transversality condition,
`v_t = η s̃_t/(1 − ρη)` and `ΔE_{t+1} π_{t+1} = −ε_{t+1}/(1 − ρη)` a.e. -/
theorem mar1_surplus_inflation {ρ η : ℝ} (hη : |ρ * η| < 1) {ε s i p v : ℕ → Ω → ℝ}
    (hsr : ∀ t, s (t + 1) = η • s t + ε (t + 1)) (hεa : StronglyAdapted S.𝓕 ε)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hs0 : StronglyMeasurable[S.𝓕 0] (s 0)) (hs0i : Integrable (s 0) S.μ)
    (hf : MFrictionless S ρ i p s v) (hva : StronglyAdapted S.𝓕 v)
    (htvc : TidyR6MeasFiscalNK.MTVC S ρ v) (hpi : ∀ t, Integrable (p t) S.μ) :
    ∀ t, (∀ᵐ ω ∂S.μ, v t ω = η * s t ω / (1 - ρ * η)) ∧
      (fun ω => p (t + 1) ω - S.E t (p (t + 1)) ω) =ᵐ[S.μ]
        fun ω => -(ε (t + 1) ω / (1 - ρ * η)) := by
  have hρη : 1 - ρ * η ≠ 0 := by
    intro h0
    have : ρ * η = 1 := by linarith
    rw [this, abs_one] at hη
    exact lt_irrefl _ hη
  -- `s` is adapted and integrable
  have hsk : ∀ t, StronglyMeasurable[S.𝓕 t] (s t) ∧ Integrable (s t) S.μ := by
    intro t
    induction t with
    | zero => exact ⟨hs0, hs0i⟩
    | succ t ih =>
      rw [hsr t]
      exact ⟨((ih.1.mono (S.𝓕.mono (Nat.le_succ t))).const_smul η).add (hεa (t + 1)),
        (ih.2.smul η).add (hεi (t + 1))⟩
  have hsa : StronglyAdapted S.𝓕 s := fun t => (hsk t).1
  have hsi : ∀ t, Integrable (s t) S.μ := fun t => (hsk t).2
  -- AR(1) forecasts
  have hE1 : ∀ t, S.E t (s (t + 1)) =ᵐ[S.μ] η • s t := by
    intro t
    rw [hsr t]
    filter_upwards [E_add_smul S (hεi (t + 1)) (hsi t) η t, hε t] with ω e1 e2
    rw [show η • s t + ε (t + 1) = ε (t + 1) + η • s t by abel, e1, e2,
      S.E_of_stronglyMeasurable (hsa t) (hsi t)]
    simp
  have hEk := fun t => TidyR6MeasFiscalNK.E_iter S hsa hsi hE1 t
  have hpv : ∀ t, ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (s (t + 1 + j)) ω)
      (η * s t ω / (1 - ρ * η)) := by
    intro t
    filter_upwards [ae_all_iff.2 fun j => hEk t (1 + j)] with ω e
    have hg := (hasSum_geometric_of_abs_lt_one hη).mul_left (η * s t ω)
    convert hg using 1
    · funext j
      rw [show t + 1 + j = t + (1 + j) by omega, e j, Pi.smul_apply, smul_eq_mul, pow_add,
        mul_pow]
      ring
    · field_simp
  have hvv : ∀ t, ∀ᵐ ω ∂S.μ, v t ω = η * s t ω / (1 - ρ * η) := by
    intro t
    filter_upwards [mpv_of_tvc S hf hva htvc hpi (fun t => hsi (t + 1)) t
      (by filter_upwards [hpv t] with ω e; exact e.summable), hpv t] with ω e1 e2
    exact e1.unique e2
  intro t
  refine ⟨hvv t, ?_⟩
  filter_upwards [msurprise_eq S hf t, hvv t, hvv (t + 1)] with ω e1 e2 e3
  rw [e1, e2, e3]
  have e4 := congrFun (hsr t) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at e4
  rw [e4]
  have hDD : (1 - ρ * η) * (1 - ρ * η)⁻¹ = 1 := mul_inv_cancel₀ hρη
  simp only [div_eq_mul_inv]
  linear_combination (η * s t ω + ε (t + 1) ω) * hDD

/-- Cochrane (2023), §5.6, eqs. (5.82)–(5.84), pp. 160–162, **in a probability model**: a backed
component `s*` (a surplus process with `β_s = 0`, latent debt `v*`) plus an unbacked AR(1)
component `ŝ_{t+1} = η̂ ŝ_t + ε̂_{t+1}`, `s̃ = s* + ŝ`. In the frictionless model with debt
satisfying the transversality condition, a.e. `v_t = v*_t + η̂ ŝ_t/(1 − ρη̂)` and
`ΔE_{t+1} π_{t+1} = −ε̂_{t+1}/(1 − ρη̂)`. -/
theorem malt_unexpected_inflation {ρ α η ηh : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1)
    (hη : |ρ * η| < 1) (hηh : |ρ * ηh| < 1) {ε ss vs u εh sh s i p v : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α 0 η ε ss vs u) (hεa : StronglyAdapted S.𝓕 ε)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0)) (hv0i : Integrable (vs 0) S.μ)
    (hu0 : StronglyMeasurable[S.𝓕 0] (u 0)) (hu0i : Integrable (u 0) S.μ)
    (hshr : ∀ t, sh (t + 1) = ηh • sh t + εh (t + 1)) (hεha : StronglyAdapted S.𝓕 εh)
    (hεhi : ∀ t, Integrable (εh t) S.μ) (hεh : ∀ t, S.E t (εh (t + 1)) =ᵐ[S.μ] 0)
    (hsh0 : StronglyMeasurable[S.𝓕 0] (sh 0)) (hsh0i : Integrable (sh 0) S.μ)
    (hs : ∀ t, s (t + 1) = ss (t + 1) + sh (t + 1))
    (hf : MFrictionless S ρ i p s v) (hva : StronglyAdapted S.𝓕 v)
    (htvc : TidyR6MeasFiscalNK.MTVC S ρ v) (hpi : ∀ t, Integrable (p t) S.μ) :
    ∀ t, (∀ᵐ ω ∂S.μ, v t ω = vs t ω + ηh * sh t ω / (1 - ρ * ηh)) ∧
      (fun ω => p (t + 1) ω - S.E t (p (t + 1)) ω) =ᵐ[S.μ]
        fun ω => -(εh (t + 1) ω / (1 - ρ * ηh)) := by
  have hρη : 1 - ρ * ηh ≠ 0 := by
    intro h0
    have : ρ * ηh = 1 := by linarith
    rw [this, abs_one] at hηh
    exact lt_irrefl _ hηh
  obtain ⟨-, -, -, -, -, hssi⟩ := msurplus_adapted S hρ h hεa hεi hv0 hv0i hu0 hu0i
  have hsk : ∀ t, StronglyMeasurable[S.𝓕 t] (sh t) ∧ Integrable (sh t) S.μ := by
    intro t
    induction t with
    | zero => exact ⟨hsh0, hsh0i⟩
    | succ t ih =>
      rw [hshr t]
      exact ⟨((ih.1.mono (S.𝓕.mono (Nat.le_succ t))).const_smul ηh).add (hεha (t + 1)),
        (ih.2.smul ηh).add (hεhi (t + 1))⟩
  have hsha : StronglyAdapted S.𝓕 sh := fun t => (hsk t).1
  have hshi : ∀ t, Integrable (sh t) S.μ := fun t => (hsk t).2
  have hsi : ∀ t, Integrable (s (t + 1)) S.μ := fun t => by
    rw [hs t]
    exact (hssi t).add (hshi (t + 1))
  have hE1 : ∀ t, S.E t (sh (t + 1)) =ᵐ[S.μ] ηh • sh t := by
    intro t
    rw [hshr t]
    filter_upwards [E_add_smul S (hεhi (t + 1)) (hshi t) ηh t, hεh t] with ω e1 e2
    rw [show ηh • sh t + εh (t + 1) = εh (t + 1) + ηh • sh t by abel, e1, e2,
      S.E_of_stronglyMeasurable (hsha t) (hshi t)]
    simp
  have hEk := fun t => TidyR6MeasFiscalNK.E_iter S hsha hshi hE1 t
  have hpvh : ∀ t, ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (sh (t + 1 + j)) ω)
      (ηh * sh t ω / (1 - ρ * ηh)) := by
    intro t
    filter_upwards [ae_all_iff.2 fun j => hEk t (1 + j)] with ω e
    have hg := (hasSum_geometric_of_abs_lt_one hηh).mul_left (ηh * sh t ω)
    convert hg using 1
    · funext j
      rw [show t + 1 + j = t + (1 + j) by omega, e j, Pi.smul_apply, smul_eq_mul, pow_add,
        mul_pow]
      ring
    · field_simp
  have hpv : ∀ t, ∀ᵐ ω ∂S.μ, HasSum (fun j => ρ ^ j * S.E t (s (t + 1 + j)) ω)
      (vs t ω + ηh * sh t ω / (1 - ρ * ηh)) := by
    intro t
    have hadd : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (s (t + 1 + j)) ω =
        S.E t (ss (t + 1 + j)) ω + S.E t (sh (t + 1 + j)) ω := by
      intro j
      rw [show t + 1 + j = t + j + 1 by omega, hs (t + j)]
      exact S.E_add (hssi (t + j)) (hshi (t + j + 1)) t
    filter_upwards [mvstar_eq_pv S hρ hα hη h hεa hεi hε hv0 hv0i hu0 hu0i t, hpvh t,
      ae_all_iff.2 hadd] with ω e1 e2 e3
    convert e1.add e2 using 1
    funext j
    rw [e3 j]
    ring
  have hvv : ∀ t, ∀ᵐ ω ∂S.μ, v t ω = vs t ω + ηh * sh t ω / (1 - ρ * ηh) := by
    intro t
    filter_upwards [mpv_of_tvc S hf hva htvc hpi hsi t
      (by filter_upwards [hpv t] with ω e; exact e.summable), hpv t] with ω e1 e2
    exact e1.unique e2
  intro t
  refine ⟨hvv t, ?_⟩
  filter_upwards [msurprise_eq S hf t, hvv t, hvv (t + 1)] with ω e1 e2 e3
  rw [e1, e2, e3]
  have e4 := congrFun (h t).2.1 ω
  have e5 := congrFun (hshr t) ω
  have e6 := congrFun (hs t) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply, zero_mul, add_zero]
    at e4 e5 e6
  rw [e6, e5]
  have hDD : (1 - ρ * ηh) * (1 - ρ * ηh)⁻¹ = 1 := mul_inv_cancel₀ hρη
  simp only [div_eq_mul_inv]
  linear_combination (-1 : ℝ) * e4 + (ηh * sh t ω + εh (t + 1) ω) * hDD

/-- Cochrane (2023), §5.6, p. 161: `malt_unexpected_inflation`'s debt formula, the closed form
`v_t = v*_t + η̂ ŝ_t/(1 − ρη̂)` (a.e.); in particular `v ≠ v*` wherever `η̂ ŝ_t ≠ 0`. -/
theorem malt_v_closed_form {ρ α η ηh : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1)
    (hη : |ρ * η| < 1) (hηh : |ρ * ηh| < 1) {ε ss vs u εh sh s i p v : ℕ → Ω → ℝ}
    (h : IsSurplusProc ρ α 0 η ε ss vs u) (hεa : StronglyAdapted S.𝓕 ε)
    (hεi : ∀ t, Integrable (ε t) S.μ) (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0)) (hv0i : Integrable (vs 0) S.μ)
    (hu0 : StronglyMeasurable[S.𝓕 0] (u 0)) (hu0i : Integrable (u 0) S.μ)
    (hshr : ∀ t, sh (t + 1) = ηh • sh t + εh (t + 1)) (hεha : StronglyAdapted S.𝓕 εh)
    (hεhi : ∀ t, Integrable (εh t) S.μ) (hεh : ∀ t, S.E t (εh (t + 1)) =ᵐ[S.μ] 0)
    (hsh0 : StronglyMeasurable[S.𝓕 0] (sh 0)) (hsh0i : Integrable (sh 0) S.μ)
    (hs : ∀ t, s (t + 1) = ss (t + 1) + sh (t + 1))
    (hf : MFrictionless S ρ i p s v) (hva : StronglyAdapted S.𝓕 v)
    (htvc : TidyR6MeasFiscalNK.MTVC S ρ v) (hpi : ∀ t, Integrable (p t) S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ηh * sh t ω ≠ 0 → v t ω ≠ vs t ω := by
  filter_upwards [(malt_unexpected_inflation S hρ hα hη hηh h hεa hεi hε hv0 hv0i hu0 hu0i hshr
    hεha hεhi hεh hsh0 hsh0i hs hf hva htvc hpi t).1] with ω e hne
  rw [e]
  intro h'
  have hρη : 1 - ρ * ηh ≠ 0 := by
    intro h0
    have : ρ * ηh = 1 := by linarith
    rw [this, abs_one] at hηh
    exact lt_irrefl _ hηh
  have : ηh * sh t ω / (1 - ρ * ηh) = 0 := by linarith
  rcases div_eq_zero_iff.1 this with h1 | h1
  · exact hne h1
  · exact hρη h1

/-! ### §5.4.1, (5.36)–(5.37): passive surplus rules -/

/-- Cochrane (2023), (5.36)–(5.37), p. 138 ("for γ > 0 … the transversality condition holds. Any
unexpected inflation is an equilibrium"), corrected (survey of Ch. 11–19, E6), **in a probability
model**: for `ρ ≠ 0`, every adapted integrable debt path following
`ρ v_{t+1} = (1 − γ) v_t − ΔE_{t+1} π_{t+1}` (for any adapted integrable inflation) satisfies the
transversality condition **iff** `|1 − γ| < 1`, i.e. `0 < γ < 2`. -/
theorem mgamma_passive_iff {ρ γ : ℝ} (hρ : ρ ≠ 0) :
    (∀ p' v' : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 v' → (∀ t, Integrable (v' t) S.μ) →
      (∀ t, Integrable (p' t) S.μ) →
      (∀ t, ρ • v' (t + 1) =ᵐ[S.μ] (1 - γ) • v' t - (p' (t + 1) - S.E t (p' (t + 1)))) →
      TidyR6MeasFiscalNK.MTVC S ρ v') ↔ |1 - γ| < 1 := by
  constructor
  · intro H
    by_contra hc
    push Not at hc
    set c := (1 - γ) / ρ
    have hγ : 1 - γ ≠ 0 := fun h0 => by rw [h0, abs_zero] at hc; linarith
    have hc0 : c ≠ 0 := div_ne_zero hγ hρ
    have hrec : ∀ t, ρ • (fun (t : ℕ) (_ : Ω) => c ^ t) (t + 1) =ᵐ[S.μ]
        (1 - γ) • (fun (t : ℕ) (_ : Ω) => c ^ t) t -
          ((0 : ℕ → Ω → ℝ) (t + 1) - S.E t ((0 : ℕ → Ω → ℝ) (t + 1))) := fun t =>
      Eventually.of_forall fun ω => by
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul, S.E_zero, sub_zero,
          pow_succ]
        simp only [c]
        field_simp
    obtain ⟨-, hT⟩ := H 0 (fun t _ => c ^ t) (fun t => stronglyMeasurable_const)
      (fun t => integrable_const _) (fun t => integrable_const 0) hrec
    obtain ⟨ω, hω⟩ := (hT 0).exists
    simp only [zero_add, S.E_const] at hω
    have hbig : ∀ k : ℕ, 1 ≤ |ρ ^ k * c ^ k| := fun k => by
      rw [← mul_pow, show ρ * c = 1 - γ by simp only [c]; field_simp, abs_pow]
      exact one_le_pow₀ hc
    have := hω.abs
    rw [abs_zero] at this
    have hev := (this.eventually (gt_mem_nhds zero_lt_one))
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd (hbig k) (not_le.2 hk)
  · intro hγ p' v' hva hvi hpi hrec
    refine ⟨hvi, fun t => ?_⟩
    have hE1 : ∀ s, S.E s (v' (s + 1)) =ᵐ[S.μ] ((1 - γ) / ρ) • v' s := by
      intro s
      have hrec' : v' (s + 1) =ᵐ[S.μ] ρ⁻¹ • ((1 - γ) • v' s -
          (p' (s + 1) - S.E s (p' (s + 1)))) := by
        filter_upwards [hrec s] with ω e
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e ⊢
        rw [← e]
        field_simp
      have hn : S.E s (p' (s + 1) - S.E s (p' (s + 1))) =ᵐ[S.μ] 0 := by
        filter_upwards [S.E_sub (hpi (s + 1)) (S.integrable_E s (p' (s + 1))) s] with ω e
        rw [e, Pi.sub_apply, S.E_E_self, sub_self, Pi.zero_apply]
      filter_upwards [S.E_congr hrec' s, S.E_smul ρ⁻¹ ((1 - γ) • v' s -
          (p' (s + 1) - S.E s (p' (s + 1)))) s,
        S.E_sub ((hvi s).smul (1 - γ)) ((hpi (s + 1)).sub (S.integrable_E s (p' (s + 1)))) s,
        S.E_smul (1 - γ) (v' s) s, hn] with ω e1 e2 e3 e4 e5
      rw [e1, e2, Pi.smul_apply, e3, Pi.sub_apply, e4, e5, Pi.smul_apply,
        S.E_of_stronglyMeasurable (hva s) (hvi s)]
      simp only [Pi.zero_apply, sub_zero, smul_eq_mul, Pi.smul_apply]
      ring
    have hk := TidyR6MeasFiscalNK.E_iter S hva hvi hE1 t
    filter_upwards [ae_all_iff.2 hk] with ω e
    have hlim : Tendsto (fun k : ℕ => (1 - γ) ^ k * v' t ω) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hγ).mul_const (v' t ω)
      rwa [zero_mul] at this
    refine hlim.congr fun k => ?_
    rw [e k, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← mul_pow]
    congr 2
    field_simp

/-! ### (5.42): observational equivalence -/

/-- Cochrane (2023), pp. 139–140, in a probability model: a target `(π*, i*, v*, s̃, u)` with
`i*_t = E_t π*_{t+1}`, `ΔE_{t+1} π*_{t+1} = −β_s ε_{t+1}` (a.e.) and the surplus process
(5.22)–(5.24) with latent debt `v*`. -/
def MTarget (ρ α βs η : ℝ) (ε is ps s vs u : ℕ → Ω → ℝ) : Prop :=
  (∀ t, is t =ᵐ[S.μ] S.E t (ps (t + 1))) ∧
    (∀ t, (fun ω => ps (t + 1) ω - S.E t (ps (t + 1)) ω) =ᵐ[S.μ] -(βs • ε (t + 1))) ∧
    IsSurplusProc ρ α βs η ε s vs u

/-- Cochrane (2023), pp. 139–140 (model A: active fiscal, `i = i*`), **in a probability model**:
every equilibrium of the frictionless model with the surplus process and `i = i*`, whose debt
satisfies the transversality condition, is the target a.e.: `π_{t+1} = π*_{t+1}`, `v = v*`. -/
theorem mmodelA_unique {ρ α βs η : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * η| < 1)
    {ε is ps s vs u p v : ℕ → Ω → ℝ} (hT : MTarget S ρ α βs η ε is ps s vs u)
    (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0))
    (hv0i : Integrable (vs 0) S.μ) (hu0 : StronglyMeasurable[S.𝓕 0] (u 0))
    (hu0i : Integrable (u 0) S.μ) (hf : MFrictionless S ρ is p s v)
    (hva : StronglyAdapted S.𝓕 v) (htvc : TidyR6MeasFiscalNK.MTVC S ρ v)
    (hpi : ∀ t, Integrable (p t) S.μ) :
    ∀ t, p (t + 1) =ᵐ[S.μ] ps (t + 1) ∧ v t =ᵐ[S.μ] vs t := by
  obtain ⟨hTi, hTs, hTp⟩ := hT
  have hsel := mselect S hρ hα hη hTp hεa hεi hε hv0 hv0i hu0 hu0i hf hva htvc hpi
  intro t
  refine ⟨?_, (hsel t).1⟩
  filter_upwards [(hsel t).2, hTs t, hf.1 t, hTi t] with ω e1 e2 e3 e4
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
  rw [e3] at e4
  linarith

/-- Cochrane (2023), eq. (5.42), p. 140 (model B: active money, passive fiscal policy), in a
probability model: `i_t = E_t π_{t+1}`, `i_t = i*_t + φ(π_t − π*_t)`,
`s̃_{t+1} = α v_t + u_{t+1}`, `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (a.e.). -/
def MActiveMoney (ρ α φ : ℝ) (is ps i p s v u : ℕ → Ω → ℝ) : Prop :=
  (∀ t, i t =ᵐ[S.μ] S.E t (p (t + 1))) ∧ (∀ t, i t =ᵐ[S.μ] is t + φ • (p t - ps t)) ∧
    (∀ t, s (t + 1) = α • v t + u (t + 1)) ∧
    ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + i t - p (t + 1) - s (t + 1)

/-- Cochrane (2023), eq. (5.42), p. 140 ("`π_t ≠ π*_t` generates an explosion"), **in a
probability model**: for `|φ| > 1`, every equilibrium of the active-money model with bounded
adapted `π − π*` and `v_0 = v*_0` is the target a.e.:
`π = π*`, `v = v*`, `s̃ = s̃*`, `i = i*`. -/
theorem mmodelB_unique {ρ α βs η φ : ℝ} (hρ : ρ ≠ 0) (hφ : 1 < |φ|)
    {ε is ps s vs u i p sB v : ℕ → Ω → ℝ} (hT : MTarget S ρ α βs η ε is ps s vs u)
    (h : MActiveMoney S ρ α φ is ps i p sB v u) (hpa : StronglyAdapted S.𝓕 p)
    (hpsa : StronglyAdapted S.𝓕 ps) (hb : S.BddProc (fun t => p t - ps t))
    (hpi : ∀ t, Integrable (p t) S.μ) (hpsi : ∀ t, Integrable (ps t) S.μ)
    (hv0 : v 0 =ᵐ[S.μ] vs 0) :
    ∀ t, p t =ᵐ[S.μ] ps t ∧ v t =ᵐ[S.μ] vs t ∧ sB (t + 1) =ᵐ[S.μ] s (t + 1) ∧
      i t =ᵐ[S.μ] is t := by
  obtain ⟨hTi, hTs, hTp⟩ := hT
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hφ0 : φ ≠ 0 := fun h0 => by rw [h0, abs_zero] at hφ; linarith
  set d : ℕ → Ω → ℝ := fun t => p t - ps t
  have hda : StronglyAdapted S.𝓕 d := fun t => (hpa t).sub (hpsa t)
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => (hpi t).sub (hpsi t)
  -- `d_t = φ⁻¹ E_t d_{t+1}`
  have hsol : S.Solves φ⁻¹ 0 d := by
    intro t
    filter_upwards [h1 t, h2 t, hTi t, S.E_sub (hpi (t + 1)) (hpsi (t + 1)) t] with ω e1 e2 e3 e4
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, Pi.sub_apply]
      at e2 e4 ⊢
    change p t ω - ps t ω = φ⁻¹ * S.E t (fun ω => p (t + 1) ω - ps (t + 1) ω) ω
    have e4' : S.E t (fun ω => p (t + 1) ω - ps (t + 1) ω) ω =
        S.E t (p (t + 1)) ω - S.E t (ps (t + 1)) ω := e4
    rw [e4', ← e1, ← e3, e2]
    field_simp
    ring
  have hinv : |φ⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hφ
  have hz : S.Solves φ⁻¹ 0 (0 : ℕ → Ω → ℝ) := fun t => Eventually.of_forall fun ω => by
    simp [S.E_zero]
  have hd0 := S.forward_unique hinv hsol hz
    (fun t => ((hda t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => aestronglyMeasurable_const) hb (mbdd_zero S)
  have hpp : ∀ t, p t =ᵐ[S.μ] ps t := fun t => by
    filter_upwards [hd0 t] with ω e
    change p t ω - ps t ω = 0 at e
    linarith
  -- debt: `ρ (v − v*)_{t+1} = (1 − α)(v − v*)_t`, from `v_0 = v*_0`
  have hvv : ∀ t, v t =ᵐ[S.μ] vs t := by
    intro t
    induction t with
    | zero => exact hv0
    | succ t ih =>
      filter_upwards [ih, h4 t, h2 t, hpp t, hpp (t + 1), hTi t, hTs t, h1 t]
        with ω e1 e2 e3 e4 e5 e6 e7 e8
      have e9 := congrFun (hTp t).2.1 ω
      have e10 := congrFun (h3 t) ω
      have e11 := congrFun (hTp t).1 ω
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
        at e2 e3 e7 e9 e10 e11
      rw [e4, sub_self, mul_zero, add_zero] at e3
      have : ρ * (v (t + 1) ω - vs (t + 1) ω) = 0 := by
        rw [e10] at e2
        rw [e11] at e9
        rw [e1] at e2
        linarith
      have := (mul_eq_zero.mp this).resolve_left hρ
      linarith
  intro t
  refine ⟨hpp t, hvv t, ?_, ?_⟩
  · filter_upwards [hvv t] with ω e
    rw [congrFun (h3 t) ω, congrFun (hTp t).1 ω]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
  · filter_upwards [h2 t, hpp t] with ω e1 e2
    rw [e1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, e2, sub_self, mul_zero,
      add_zero]

/-- Cochrane (2023), eq. (5.42), pp. 139–140, **observational equivalence in a probability
model**: an equilibrium of model A (active fiscal, `i = i*`, transversality) and an equilibrium of
model B (active money `|φ| > 1`, passive fiscal, `π − π*` bounded, `v_0 = v*_0`) for the same
target produce the same inflation and value of debt a.e. at every date. -/
theorem mobservationally_equivalent {ρ α βs η φ : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1)
    (hη : |ρ * η| < 1) (hφ : 1 < |φ|) {ε is ps s vs u pA vA i pB sB vB : ℕ → Ω → ℝ}
    (hT : MTarget S ρ α βs η ε is ps s vs u)
    (hεa : StronglyAdapted S.𝓕 ε) (hεi : ∀ t, Integrable (ε t) S.μ)
    (hε : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (hv0 : StronglyMeasurable[S.𝓕 0] (vs 0))
    (hv0i : Integrable (vs 0) S.μ) (hu0 : StronglyMeasurable[S.𝓕 0] (u 0))
    (hu0i : Integrable (u 0) S.μ) (hA : MFrictionless S ρ is pA s vA)
    (hvAa : StronglyAdapted S.𝓕 vA) (htvc : TidyR6MeasFiscalNK.MTVC S ρ vA)
    (hpAi : ∀ t, Integrable (pA t) S.μ) (hB : MActiveMoney S ρ α φ is ps i pB sB vB u)
    (hpBa : StronglyAdapted S.𝓕 pB) (hpsa : StronglyAdapted S.𝓕 ps)
    (hbB : S.BddProc (fun t => pB t - ps t)) (hpBi : ∀ t, Integrable (pB t) S.μ)
    (hpsi : ∀ t, Integrable (ps t) S.μ) (hvB0 : vB 0 =ᵐ[S.μ] vs 0) :
    ∀ t, pA (t + 1) =ᵐ[S.μ] pB (t + 1) ∧ vA t =ᵐ[S.μ] vB t := by
  have hAu := mmodelA_unique S hρ hα hη hT hεa hεi hε hv0 hv0i hu0 hu0i hA hvAa htvc hpAi
  have hBu := mmodelB_unique S hρ hφ hT hB hpBa hpsa hbB hpBi hpsi hvB0
  intro t
  exact ⟨(hAu t).1.trans (hBu (t + 1)).1.symm, (hAu t).2.trans (hBu t).2.1.symm⟩

end Cochrane.StickyPriceFiscal.TidyR6MeasSurplus
