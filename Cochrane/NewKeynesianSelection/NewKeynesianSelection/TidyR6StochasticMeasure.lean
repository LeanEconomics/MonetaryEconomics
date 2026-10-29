/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6StochasticPatches
import NewKeynesianSelection.TidyR6ExpectationsMeasureIID

/-!
# The nonlinear model of §16.8 on a genuine probability space

Cochrane (2023), Chapter 16, §16.8, pp. 377–380 and §16.10, pp. 386–394. An abstract
`ExpectationSystem` on a countable state space has finitely supported forecasts, so the general
results of TidyR6StochasticLowerBound and TidyR6StochasticPatches cover finite event trees but no
infinite sequence of genuine shocks. Here the model is posed on a probability space with a
filtration (TidyR6ExpectationsMeasure, `E_t = μ[·|𝓕_t]`, every equation almost surely), and the
i.i.d. coin economy (TidyR6ExpectationsMeasureIID, every history null) supplies genuine sunspots.

## Main results

* `MeasStochEq`, `measStochEq_dyn` (the stochastic (16.29) almost surely), `const_measStochEq`
  (every perfect-foresight path is an equilibrium).
* `abs_E_le_E_abs_ae`, `growth_zero_ae`: the expectation-growth lemma almost surely.
* `target_unique_locally_bounded_ae` (p. 378): with `Φ′(Π*) > 1`, `Π*` is the unique
  equilibrium staying within `δ` of `Π*`, almost surely at every date.
* `stoch_bassetto_ae`, `stoch_v_rule_ae` (§§16.10.4–16.10.5): the Bassetto and V-shaped rules
  remove sunspot equilibria too.
* `lower_sunspot` (p. 379, "Many paths lead to `Π_L` and there are 'multiple local equilibria'
  near this point"): if `1/Φ(1/·)` contracts towards `1/Π_L` on a neighbourhood and the rule
  respects the zero bound, the i.i.d. coin economy has an equilibrium that stays near `Π_L`
  forever and is genuinely random (`Π_1` is not almost surely constant);
  `lower_contraction_of_deriv` derives the contraction from `|Φ′(Π_L)| < 1`, and
  `lower_sunspot_of_deriv` combines the two.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6StochasticMeasure

open MeasureTheory ProbabilityTheory Filter Topology TidyR6ExpectationsMeasure
open TidyR6ExpectationsMeasureIID TidyR6StochasticLowerBound TidyR6StochasticPatches

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (16.25), (16.27), p. 378, and the zero bound, p. 379, on a probability
space: positive adapted gross inflation, (16.25) almost surely at every date, the rule and
`i_t ≥ 0` in every state. -/
def MeasStochEq (r : ℝ) (Φ : ℝ → ℝ) (infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < infl t ω) ∧ StronglyAdapted S.𝓕 infl ∧
    (∀ t, (fun ω => 1 / (1 + i t ω)) =ᵐ[S.μ] (1 + r)⁻¹ • S.E t (fun ω => 1 / infl (t + 1) ω)) ∧
    (∀ t ω, 1 + i t ω = (1 + r) * Φ (infl t ω)) ∧ ∀ t ω, 0 ≤ i t ω

/-- Cochrane (2023), eq. (16.29), p. 378, on a probability space: in an equilibrium
`E_t(1/Π_{t+1}) = 1/Φ(Π_t)` almost surely. -/
theorem measStochEq_dyn {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {infl i : ℕ → Ω → ℝ}
    (h : MeasStochEq S r Φ infl i) (t : ℕ) :
    S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun ω => 1 / Φ (infl t ω) := by
  filter_upwards [h.2.2.1 t] with ω e
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rw [h.2.2.2.1 t ω, one_div, mul_inv] at e
  rw [one_div]
  exact (mul_left_cancel₀ (inv_ne_zero hr.ne') e).symm

/-- Cochrane (2023), p. 379, on a probability space: a perfect-foresight equilibrium path is an
equilibrium. -/
theorem const_measStochEq {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {p j : ℕ → ℝ}
    (hpos : ∀ t, 0 < p t) (hzb : ∀ t, 0 ≤ j t) (hfis : ∀ t, p (t + 1) = (1 + r)⁻¹ * (1 + j t))
    (hrule : ∀ t, 1 + j t = (1 + r) * Φ (p t)) :
    MeasStochEq S r Φ (fun t _ => p t) (fun t _ => j t) := by
  refine ⟨fun t _ => hpos t, fun t => stronglyMeasurable_const, fun t => ?_,
    fun t _ => hrule t, fun t _ => hzb t⟩
  refine Eventually.of_forall fun ω => ?_
  change 1 / (1 + j t) = (1 + r)⁻¹ * S.E t (fun _ => 1 / p (t + 1)) ω
  rw [S.E_const]
  have h1 : 0 < 1 + j t := by linarith [hzb t]
  rw [hfis t]
  field_simp

/-! ## The growth lemma almost surely -/

/-- Cochrane (2023), §16.1, p. 364: `|E_t f| ≤ E_t|f|` almost surely, for integrable `f`. -/
theorem abs_E_le_E_abs_ae {f : Ω → ℝ} (hf : Integrable f S.μ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |S.E t f ω| ≤ S.E t (fun ω' => |f ω'|) ω := by
  have h1 := S.E_mono hf hf.abs (Eventually.of_forall fun ω => le_abs_self (f ω)) t
  have h2 := S.E_mono hf.abs.neg hf (Eventually.of_forall fun ω => by
    simp only [Pi.neg_apply]; exact neg_abs_le (f ω)) t
  have h3 := S.E_smul (-1) (fun ω' => |f ω'|) t
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  have : S.E t (-fun ω' => |f ω'|) ω = -S.E t (fun ω' => |f ω'|) ω := by
    rw [show (-fun ω' => |f ω'|) = (-1 : ℝ) • fun ω' => |f ω'| by funext; simp, e3]
    simp
  rw [this] at e2
  exact abs_le.mpr ⟨by linarith, e1⟩

/-- Cochrane (2023), §16.1, p. 364 and §16.8, p. 378, almost surely: a process that is a.e.
nonnegative, bounded by `B`, a.e. strongly measurable at each date and satisfies
`cD_t ≤ E_tD_{t+1}` a.s. with `c > 1` is zero almost surely at every date. -/
theorem growth_zero_ae {D : ℕ → Ω → ℝ} {c B : ℝ} (hc : 1 < c)
    (hm : ∀ t, AEStronglyMeasurable (D t) S.μ) (hD0 : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ D t ω)
    (hDB : ∀ t, ∀ᵐ ω ∂S.μ, D t ω ≤ B)
    (hg : ∀ t, ∀ᵐ ω ∂S.μ, c * D t ω ≤ S.E t (D (t + 1)) ω) : ∀ t, D t =ᵐ[S.μ] 0 := by
  have hc0 : 0 < c := by linarith
  have hint : ∀ t, Integrable (D t) S.μ := fun t =>
    Integrable.of_bound (hm t) B (by
      filter_upwards [hD0 t, hDB t] with ω h0 h1
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have hk : ∀ k t, ∀ᵐ ω ∂S.μ, c ^ (k + 1) * D t ω ≤ S.E t (D (t + (k + 1))) ω := by
    intro k
    induction k with
    | zero => intro t; simpa using hg t
    | succ k ih =>
      intro t
      have h1 : c • D (t + (k + 1)) ≤ᵐ[S.μ] S.E (t + (k + 1)) (D (t + (k + 1) + 1)) := by
        filter_upwards [hg (t + (k + 1))] with ω h
        simpa [smul_eq_mul] using h
      have h2 := S.E_mono ((hint _).smul c) (S.integrable_E _ _) h1 t
      have h3 := S.E_smul c (D (t + (k + 1))) t
      have h4 := S.E_tower (Nat.le_add_right t (k + 1)) (D (t + (k + 1) + 1))
      filter_upwards [ih t, h2, h3, h4] with ω e1 e2 e3 e4
      rw [e3, e4] at e2
      simp only [Pi.smul_apply, smul_eq_mul] at e2
      calc c ^ (k + 1 + 1) * D t ω = c * (c ^ (k + 1) * D t ω) := by ring
        _ ≤ c * S.E t (D (t + (k + 1))) ω := mul_le_mul_of_nonneg_left e1 hc0.le
        _ ≤ S.E t (D (t + (k + 1) + 1)) ω := e2
        _ = S.E t (D (t + (k + 1 + 1))) ω := by rw [add_assoc]
  have hEB : ∀ t s, ∀ᵐ ω ∂S.μ, S.E t (D s) ω ≤ B := by
    intro t s
    have := S.E_mono (hint s) (integrable_const B) (hDB s) t
    rw [S.E_const] at this
    exact this
  intro t
  have hall : ∀ᵐ ω ∂S.μ, ∀ k, c ^ (k + 1) * D t ω ≤ B := by
    rw [ae_all_iff]
    intro k
    filter_upwards [hk k t, hEB t (t + (k + 1))] with ω e1 e2
    exact e1.trans e2
  filter_upwards [hall, hD0 t] with ω h h0
  by_contra hne
  have hpos : 0 < D t ω := lt_of_le_of_ne h0 (Ne.symm hne)
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (B / D t ω) hc
  have h2 : B < c ^ k * D t ω := by rwa [div_lt_iff₀ hpos] at hk'
  have h3 : c ^ k * D t ω ≤ c ^ (k + 1) * D t ω :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc.le (Nat.le_succ k)) hpos.le
  linarith [h k]

/-! ## Local uniqueness at the active steady state -/

/-- Cochrane (2023), p. 378, "the equilibrium `Π*` is a unique 'locally bounded' equilibrium",
on a probability space: if `Φ(Π*) = Π* > 0` and `Φ′(Π*) > 1`, there is `δ > 0` such that every
adapted process with `E_t(1/Π_{t+1}) = 1/Φ(Π_t)` almost surely that stays within `δ` of `Π*` is
`Π_t = Π*` almost surely at every date. -/
theorem target_unique_locally_bounded_ae {Φ : ℝ → ℝ} {Pis d : ℝ} (hPis : 0 < Pis)
    (hfix : Φ Pis = Pis) (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ δ > 0, ∀ infl : ℕ → Ω → ℝ, (∀ t, Measurable (infl t)) →
      (∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun ω => 1 / Φ (infl t ω)) →
      (∀ t ω, |infl t ω - Pis| < δ) → ∀ t, infl t =ᵐ[S.μ] fun _ => Pis := by
  obtain ⟨hh, hk⟩ := hasDerivAt_inv_pair hPis hfix hd
  set c := (1 + d) / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hP2 : 0 < Pis ^ 2 := by positivity
  have hab : c * |-1 / Pis ^ 2| < |-d / Pis ^ 2| := by
    rw [neg_div, neg_div, abs_neg, abs_neg, abs_of_pos (by positivity),
      abs_of_pos (div_pos (by linarith) hP2)]
    rw [← mul_div_assoc, mul_one]
    exact div_lt_div_of_pos_right (by rw [hc]; linarith) hP2
  obtain ⟨δ0, hδ0, hcmp⟩ := abs_sub_ge_of_hasDerivAt hh hk (by linarith) hab
  refine ⟨min δ0 (Pis / 2), lt_min hδ0 (by linarith), fun infl hmeas hdyn hnear => ?_⟩
  have hlow : ∀ t ω, Pis / 2 < infl t ω := fun t ω => by
    have := (abs_lt.mp ((hnear t ω).trans_le (min_le_right _ _))).1
    linarith
  set D : ℕ → Ω → ℝ := fun t ω => |1 / infl t ω - 1 / Pis| with hD
  have hDB : ∀ t ω, D t ω ≤ 2 / Pis + 1 / Pis := by
    intro t ω
    have hp := hlow t ω
    have h1 : 1 / infl t ω ≤ 2 / Pis := by
      rw [div_le_div_iff₀ (by linarith) hPis]; linarith
    have h2 : 0 < 1 / infl t ω := one_div_pos.mpr (by linarith)
    have h3 : 0 < 1 / Pis := one_div_pos.mpr hPis
    rw [abs_le]
    constructor <;> linarith
  have hfm : ∀ t, AEStronglyMeasurable (fun ω => 1 / infl t ω - 1 / Pis) S.μ := fun t =>
    ((hmeas t).const_div 1).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hfi : ∀ t, Integrable (fun ω => 1 / infl t ω - 1 / Pis) S.μ := fun t =>
    Integrable.of_bound (hfm t) (2 / Pis + 1 / Pis) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hDB t ω)
  have hg : ∀ t, ∀ᵐ ω ∂S.μ, c * D t ω ≤ S.E t (D (t + 1)) ω := by
    intro t
    have hgi : Integrable (fun ω => 1 / infl (t + 1) ω) S.μ := by
      have := (hfi (t + 1)).add (integrable_const (1 / Pis))
      refine this.congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply]
      ring
    have hsub := S.E_sub hgi (integrable_const (1 / Pis)) t
    filter_upwards [hdyn t, abs_E_le_E_abs_ae S (hfi (t + 1)) t, hsub] with ω e1 e2 e3
    have h1 := hcmp (infl t ω) ((hnear t ω).trans_le (min_le_left _ _))
    simp only [hfix] at h1
    have e5 : S.E t (fun ω => 1 / infl (t + 1) ω - 1 / Pis) ω =
        S.E t (fun ω => 1 / infl (t + 1) ω) ω - 1 / Pis := by
      calc S.E t (fun ω => 1 / infl (t + 1) ω - 1 / Pis) ω =
          S.E t ((fun ω => 1 / infl (t + 1) ω) - fun _ => 1 / Pis) ω := rfl
        _ = _ := by rw [e3, Pi.sub_apply, S.E_const]
    rw [e5, e1] at e2
    exact h1.trans e2
  have hz := growth_zero_ae S hc1 (fun t => (hfm t).norm)
    (fun t => Eventually.of_forall fun ω => abs_nonneg _)
    (fun t => Eventually.of_forall fun ω => hDB t ω) hg
  intro t
  filter_upwards [hz t] with ω h
  simp only [Pi.zero_apply, Real.norm_eq_abs, abs_eq_zero, sub_eq_zero] at h
  have hp := hlow t ω
  rw [div_eq_div_iff (by linarith) hPis.ne'] at h
  linarith

/-! ## Bassetto and V-shaped rules on a probability space -/

/-- Cochrane (2023), §16.10.4, pp. 391–392, on a probability space: with a rule satisfying
`TidyR6StochasticPatches.GapBelow` (`c > 1`) that respects the zero bound only above `lo > 0`,
every measurable process
with `E_t(1/Π_{t+1}) = 1/Φ(Π_t)` a.s. and `Φ(Π_t) ≥ β` in every state has `Π_t ≥ Π*` almost
surely at every date: Bassetto's rule removes sunspot deflations too. -/
theorem stoch_bassetto_ae {Φ : ℝ → ℝ} {β Pis c lo : ℝ} (hPis : 0 < Pis) (hlo : 0 < lo)
    (hc : 1 < c) (hgap : GapBelow Φ β Pis c) (hloB : ∀ x, 0 < x → β ≤ Φ x → lo ≤ x)
    {infl : ℕ → Ω → ℝ} (hmeas : ∀ t, Measurable (infl t)) (hpos : ∀ t ω, 0 < infl t ω)
    (hzb : ∀ t ω, β ≤ Φ (infl t ω))
    (hdyn : ∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun ω => 1 / Φ (infl t ω)) :
    ∀ t, ∀ᵐ ω ∂S.μ, Pis ≤ infl t ω := by
  set D : ℕ → Ω → ℝ := fun t ω => max (1 / infl t ω - 1 / Pis) 0 with hD
  have hinv : ∀ t ω, 1 / infl t ω ≤ 1 / lo := fun t ω =>
    one_div_le_one_div_of_le hlo (hloB _ (hpos t ω) (hzb t ω))
  have hDB : ∀ t ω, D t ω ≤ 1 / lo := fun t ω => by
    have := one_div_pos.mpr hPis
    exact max_le (by linarith [hinv t ω]) (one_div_pos.mpr hlo).le
  have hfm : ∀ t, Measurable (fun ω => 1 / infl t ω) := fun t => (hmeas t).const_div 1
  have hDm : ∀ t, AEStronglyMeasurable (D t) S.μ := fun t =>
    (((hfm t).sub measurable_const).max measurable_const).aestronglyMeasurable
  have hDi : ∀ t, Integrable (D t) S.μ := fun t =>
    Integrable.of_bound (hDm t) (1 / lo) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]; exact hDB t ω)
  have hgi : ∀ t, Integrable (fun ω => 1 / infl t ω) S.μ := fun t =>
    Integrable.of_bound (hfm t).aestronglyMeasurable (1 / lo) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hpos t ω))]; exact hinv t ω)
  have hg : ∀ t, ∀ᵐ ω ∂S.μ, c * D t ω ≤ S.E t (D (t + 1)) ω := by
    intro t
    have hnn := S.E_mono (integrable_const 0) (hDi (t + 1))
      (Eventually.of_forall fun ω => le_max_right _ _) t
    have hm := S.E_mono ((hgi (t + 1)).sub (integrable_const (1 / Pis))) (hDi (t + 1))
      (Eventually.of_forall fun ω => le_max_left _ _) t
    have hsub := S.E_sub (hgi (t + 1)) (integrable_const (1 / Pis)) t
    filter_upwards [hdyn t, hnn, hm, hsub] with ω e1 e2 e3 e4
    rw [S.E_const] at e2
    by_cases hx : Pis ≤ infl t ω
    · have : D t ω = 0 := by
        simp only [hD]
        apply max_eq_right
        rw [sub_nonpos]
        exact one_div_le_one_div_of_le hPis hx
      rw [this, mul_zero]
      exact e2
    · push Not at hx
      have hgp := hgap _ (hpos t ω) hx.le (hzb t ω)
      have hDt : D t ω = 1 / infl t ω - 1 / Pis := by
        simp only [hD]
        apply max_eq_left
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (hpos t ω) hx.le
      have e5 : S.E t ((fun ω => 1 / infl (t + 1) ω) - fun _ => 1 / Pis) ω =
          1 / Φ (infl t ω) - 1 / Pis := by rw [e4, Pi.sub_apply, e1, S.E_const]
      rw [e5] at e3
      rw [hDt]
      linarith
  have hz := growth_zero_ae S hc hDm (fun t => Eventually.of_forall fun ω => le_max_right _ _)
    (fun t => Eventually.of_forall fun ω => hDB t ω) hg
  intro t
  filter_upwards [hz t] with ω h0
  have h0' : max (1 / infl t ω - 1 / Pis) 0 = 0 := h0
  have hle : 1 / infl t ω - 1 / Pis ≤ 0 := by rw [← h0']; exact le_max_left _ _
  have := hpos t ω
  by_contra hcon
  push Not at hcon
  have : 1 / Pis < 1 / infl t ω := one_div_lt_one_div_of_lt this hcon
  linarith

/-- Cochrane (2023), §16.10.5, p. 392, on a probability space: with a rule satisfying
`TidyR6StochasticPatches.GapAbove` on `[Π*, Π_max]` (`c > 1`) that sends every `Π ≠ Π*` above `Π*`,
every measurable
process with values in `[lo, Π_max]` (`lo > 0`) and `E_t(1/Π_{t+1}) = 1/Φ(Π_t)` a.s. is `Π*`
almost surely at every date. -/
theorem stoch_v_rule_ae {Φ : ℝ → ℝ} {Pis Pmax c lo : ℝ} (hPis : 0 < Pis) (hlo : 0 < lo)
    (hc : 1 < c) (hgap : GapAbove Φ Pis Pmax c) (hjump : ∀ x, 0 < x → x ≠ Pis → Pis < Φ x)
    {infl : ℕ → Ω → ℝ} (hmeas : ∀ t, Measurable (infl t)) (hlow : ∀ t ω, lo ≤ infl t ω)
    (hbd : ∀ t ω, infl t ω ≤ Pmax)
    (hdyn : ∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun ω => 1 / Φ (infl t ω)) :
    ∀ t, infl t =ᵐ[S.μ] fun _ => Pis := by
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hlo (hlow t ω)
  set D : ℕ → Ω → ℝ := fun t ω => max (1 / Pis - 1 / infl t ω) 0 with hD
  have hDB : ∀ t ω, D t ω ≤ 1 / Pis := fun t ω => by
    have := one_div_pos.mpr (hpos t ω)
    exact max_le (by linarith) (one_div_pos.mpr hPis).le
  have hfm : ∀ t, Measurable (fun ω => 1 / infl t ω) := fun t => (hmeas t).const_div 1
  have hDm : ∀ t, AEStronglyMeasurable (D t) S.μ := fun t =>
    ((measurable_const.sub (hfm t)).max measurable_const).aestronglyMeasurable
  have hDi : ∀ t, Integrable (D t) S.μ := fun t =>
    Integrable.of_bound (hDm t) (1 / Pis) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]; exact hDB t ω)
  have hgi : ∀ t, Integrable (fun ω => 1 / infl t ω) S.μ := fun t =>
    Integrable.of_bound (hfm t).aestronglyMeasurable (1 / lo) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hpos t ω))]
      exact one_div_le_one_div_of_le hlo (hlow t ω))
  have hg : ∀ t, ∀ᵐ ω ∂S.μ, c * D t ω ≤ S.E t (D (t + 1)) ω := by
    intro t
    have hnn := S.E_mono (integrable_const 0) (hDi (t + 1))
      (Eventually.of_forall fun ω => le_max_right _ _) t
    have hm := S.E_mono ((integrable_const (1 / Pis)).sub (hgi (t + 1))) (hDi (t + 1))
      (Eventually.of_forall fun ω => le_max_left _ _) t
    have hsub := S.E_sub (integrable_const (1 / Pis)) (hgi (t + 1)) t
    filter_upwards [hdyn t, hnn, hm, hsub] with ω e1 e2 e3 e4
    rw [S.E_const] at e2
    by_cases hx : infl t ω ≤ Pis
    · have : D t ω = 0 := by
        simp only [hD]
        apply max_eq_right
        rw [sub_nonpos]
        exact one_div_le_one_div_of_le (hpos t ω) hx
      rw [this, mul_zero]
      exact e2
    · push Not at hx
      have hgp := hgap _ hx.le (hbd t ω)
      have hDt : D t ω = 1 / Pis - 1 / infl t ω := by
        simp only [hD]
        apply max_eq_left
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hPis hx.le
      have e5 : S.E t ((fun _ => 1 / Pis) - fun ω => 1 / infl (t + 1) ω) ω =
          1 / Pis - 1 / Φ (infl t ω) := by rw [e4, Pi.sub_apply, e1, S.E_const]
      rw [e5] at e3
      rw [hDt]
      linarith
  have hz := growth_zero_ae S hc hDm (fun t => Eventually.of_forall fun ω => le_max_right _ _)
    (fun t => Eventually.of_forall fun ω => hDB t ω) hg
  have hle : ∀ t, ∀ᵐ ω ∂S.μ, infl t ω ≤ Pis := by
    intro t
    filter_upwards [hz t] with ω h0
    have h0' : max (1 / Pis - 1 / infl t ω) 0 = 0 := h0
    have h1 : 1 / Pis - 1 / infl t ω ≤ 0 := by rw [← h0']; exact le_max_left _ _
    have := hpos t ω
    by_contra hcon
    push Not at hcon
    have : 1 / infl t ω < 1 / Pis := one_div_lt_one_div_of_lt hPis hcon
    linarith
  intro t
  have hm := S.E_mono (integrable_const (1 / Pis)) (hgi (t + 1)) (by
    filter_upwards [hle (t + 1)] with ω h
    exact one_div_le_one_div_of_le (hpos _ _) h) t
  rw [S.E_const] at hm
  filter_upwards [hm, hdyn t] with ω e1 e2
  rw [e2] at e1
  by_contra hne
  have hΦ := hjump _ (hpos t ω) hne
  have : 1 / Φ (infl t ω) < 1 / Pis := one_div_lt_one_div_of_lt hPis hΦ
  linarith

/-! ## Sunspot equilibria near `Π_L` in the i.i.d. coin economy -/

/-- Cochrane (2023), p. 379: the coin shock clipped to `[−1, 1]` (equal to the shock almost
surely). -/
noncomputable def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- Cochrane (2023), p. 379: the sunspot path of inverse inflation `Y_t = 1/Π_t`:
`Y_0 = 1/Π_L` and `Y_{t+1} = 1/Φ(1/Y_t) + η clip(ε_{t+1})`. -/
noncomputable def sunY (Φ : ℝ → ℝ) (XL η : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => XL
  | t + 1 => fun ω => 1 / Φ (1 / sunY Φ XL η t ω) + η * clip (ω (t + 1))

/-- Cochrane (2023), p. 379: `|clip x| ≤ 1`. -/
theorem abs_clip_le (x : ℝ) : |clip x| ≤ 1 := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- Cochrane (2023), p. 379: `clip x = x` on `[−1, 1]`. -/
theorem clip_of_abs_le {x : ℝ} (hx : |x| ≤ 1) : clip x = x := by
  unfold clip
  rw [min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

/-- Cochrane (2023), p. 379: `clip` is measurable. -/
theorem measurable_clip : Measurable clip :=
  (continuous_const.max (continuous_const.min continuous_id)).measurable

/-- Cochrane (2023), p. 379, "Many paths lead to `Π_L` and there are 'multiple local
equilibria' near this point", with genuine sunspots on a genuine probability space. Let
`Φ(Π_L) = Π_L > 0`, `Φ` measurable, and suppose that on the ball `|y − 1/Π_L| ≤ ρ` of inverse
inflation `y`, `y > 0`, the rule respects the zero bound (`Φ(1/y) ≥ β`) and contracts:
`|1/Φ(1/y) − 1/Π_L| ≤ λ|y − 1/Π_L|`, `0 ≤ λ < 1`. Then the i.i.d. fair-coin economy (every
history null) has an equilibrium that starts at `Π_L`, keeps `1/Π_t` within `ρ` of `1/Π_L`
forever, and is genuinely random: `Π_1` is not almost surely equal to `Π_L`. -/
theorem lower_sunspot {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} (hΦm : Measurable Φ) {PL ρ lam : ℝ}
    (hPL : 0 < PL) (hfix : Φ PL = PL) (hρ : 0 < ρ) (hlam0 : 0 ≤ lam) (hlam : lam < 1)
    (hball : ∀ y, |y - 1 / PL| ≤ ρ →
      0 < y ∧ (1 + r)⁻¹ ≤ Φ (1 / y) ∧ |1 / Φ (1 / y) - 1 / PL| ≤ lam * |y - 1 / PL|) :
    ∃ infl i : ℕ → (ℕ → ℝ) → ℝ, MeasStochEq (iidSystem coin) r Φ infl i ∧
      (∀ t ω, |1 / infl t ω - 1 / PL| ≤ ρ) ∧ infl 0 = (fun _ => PL) ∧
      ¬ infl 1 =ᵐ[(iidSystem coin).μ] fun _ => PL := by
  set S := iidSystem coin with hS
  set η := (1 - lam) * ρ with hη
  have hη0 : 0 < η := mul_pos (by linarith) hρ
  set Y := sunY Φ (1 / PL) η with hYdef
  have hYb : ∀ t ω, |Y t ω - 1 / PL| ≤ ρ := by
    intro t
    induction t with
    | zero => intro ω; simp [hYdef, sunY, hρ.le]
    | succ n ih =>
      intro ω
      have h1 := (hball _ (ih ω)).2.2
      change |1 / Φ (1 / Y n ω) + η * clip (ω (n + 1)) - 1 / PL| ≤ ρ
      have h2 : |η * clip (ω (n + 1))| ≤ η := by
        rw [abs_mul, abs_of_pos hη0]
        exact mul_le_of_le_one_right hη0.le (abs_clip_le _)
      calc |1 / Φ (1 / Y n ω) + η * clip (ω (n + 1)) - 1 / PL|
          = |(1 / Φ (1 / Y n ω) - 1 / PL) + η * clip (ω (n + 1))| := by ring_nf
        _ ≤ |1 / Φ (1 / Y n ω) - 1 / PL| + |η * clip (ω (n + 1))| := abs_add_le _ _
        _ ≤ lam * |Y n ω - 1 / PL| + η := add_le_add h1 h2
        _ ≤ lam * ρ + η := by nlinarith [ih ω]
        _ = ρ := by rw [hη]; ring
  have hYpos : ∀ t ω, 0 < Y t ω := fun t ω => (hball _ (hYb t ω)).1
  have hYzb : ∀ t ω, (1 + r)⁻¹ ≤ Φ (1 / Y t ω) := fun t ω => (hball _ (hYb t ω)).2.1
  have hΦpos : ∀ t ω, 0 < Φ (1 / Y t ω) := fun t ω =>
    lt_of_lt_of_le (inv_pos.mpr hr) (hYzb t ω)
  -- measurability: `Y_t` is known at `t`
  have hYm : ∀ t, Measurable[S.𝓕 t] (Y t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ n ih =>
      have h1 : Measurable[S.𝓕 n] (fun ω => 1 / Φ (1 / Y n ω)) :=
        (hΦm.comp (ih.const_div 1)).const_div 1
      have h2 : Measurable[S.𝓕 (n + 1)] (fun ω : ℕ → ℝ => clip (ω (n + 1))) :=
        measurable_clip.comp (measurable_shock coin (le_refl (n + 1)))
      exact (h1.mono (S.𝓕.mono (Nat.le_succ n)) le_rfl).add (h2.const_mul η)
  set infl : ℕ → (ℕ → ℝ) → ℝ := fun t ω => 1 / Y t ω with hinfl
  set i : ℕ → (ℕ → ℝ) → ℝ := fun t ω => (1 + r) * Φ (infl t ω) - 1 with hi
  have hYinfl : ∀ t ω, 1 / infl t ω = Y t ω := fun t ω => by simp [hinfl]
  refine ⟨infl, i, ⟨fun t ω => one_div_pos.mpr (hYpos t ω), fun t => ?_, fun t => ?_,
    fun t ω => by simp [hi], fun t ω => ?_⟩, fun t ω => by rw [hYinfl]; exact hYb t ω,
    by funext ω; simp [hinfl, hYdef, sunY], ?_⟩
  · exact ((hYm t).const_div 1).stronglyMeasurable
  · -- the bond-pricing equation almost surely
    have hgm : StronglyMeasurable[S.𝓕 t] (fun ω => 1 / Φ (1 / Y t ω)) :=
      ((hΦm.comp ((hYm t).const_div 1)).const_div 1).stronglyMeasurable
    have hgb : ∀ ω, |1 / Φ (1 / Y t ω)| ≤ 1 / PL + ρ := fun ω => by
      have h1 := (hball _ (hYb t ω)).2.2
      have h2 := hYb t ω
      have h3 : 0 < 1 / Φ (1 / Y t ω) := one_div_pos.mpr (hΦpos t ω)
      rw [abs_of_pos h3]
      have := abs_sub_abs_le_abs_sub (1 / Φ (1 / Y t ω)) (1 / PL)
      rw [abs_of_pos h3, abs_of_pos (one_div_pos.mpr hPL)] at this
      nlinarith [abs_nonneg (Y t ω - 1 / PL)]
    have hgi : Integrable (fun ω => 1 / Φ (1 / Y t ω)) S.μ :=
      Integrable.of_bound (hgm.mono (S.𝓕.le t)).aestronglyMeasurable (1 / PL + ρ)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
    have hci : Integrable (fun ω : ℕ → ℝ => η * clip (ω (t + 1))) S.μ :=
      Integrable.of_bound ((measurable_clip.comp (measurable_pi_apply (t + 1))).const_mul
        η).aestronglyMeasurable η (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hη0]
          exact mul_le_of_le_one_right hη0.le (abs_clip_le _))
    have hsplit : (fun ω => 1 / infl (t + 1) ω) =
        (fun ω => 1 / Φ (1 / Y t ω)) + fun ω : ℕ → ℝ => η * clip (ω (t + 1)) := by
      funext ω
      rw [hYinfl]
      rfl
    have hadd := S.E_add hgi hci t
    have hsm := S.E_smul η (fun ω : ℕ → ℝ => clip (ω (t + 1))) t
    have hsh := E_shock_fun coin t measurable_clip
    have hclip0 : ∫ x, clip x ∂(coin : Measure ℝ) = 0 := by
      rw [integral_coin]; norm_num [clip]
    filter_upwards [hadd, hsm, hsh] with ω e1 e2 e3
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsplit, e1, Pi.add_apply, S.E_of_stronglyMeasurable hgm hgi]
    have e4 : S.E t (fun ω : ℕ → ℝ => η * clip (ω (t + 1))) ω = 0 := by
      have : (fun ω : ℕ → ℝ => η * clip (ω (t + 1))) =
          η • fun ω : ℕ → ℝ => clip (ω (t + 1)) := rfl
      rw [this, e2, Pi.smul_apply, e3, hclip0, smul_zero]
    rw [e4, add_zero]
    change 1 / (1 + ((1 + r) * Φ (1 / Y t ω) - 1)) = (1 + r)⁻¹ * (1 / Φ (1 / Y t ω))
    rw [add_sub_cancel, one_div, mul_inv]
    simp only [one_div]
  · have h1 := mul_le_mul_of_nonneg_left (hYzb t ω) hr.le
    rw [mul_inv_cancel₀ hr.ne'] at h1
    simp only [hi, hinfl]
    linarith
  · -- genuine randomness
    intro hae
    have hY1 : ∀ ω, Y 1 ω = 1 / PL + η * clip (ω 1) := fun ω => by
      change 1 / Φ (1 / (1 / PL)) + η * clip (ω (0 + 1)) = _
      rw [one_div_one_div, hfix]
    have hshock0 : shock (0 + 1) =ᵐ[S.μ] 0 := by
      filter_upwards [hae, shock_ae_bdd coin coin_bdd 1] with ω h hb
      have h2 : Y 1 ω = 1 / PL := by
        rw [← hYinfl 1 ω]
        rw [h]
      rw [hY1] at h2
      have h3 : clip (ω 1) = 0 := by
        have : η * clip (ω 1) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hη0.ne'
      have hb' : |ω 1| ≤ 1 := hb
      rw [clip_of_abs_le hb'] at h3
      change ω 1 = 0
      exact h3
    exact shock_not_ae_E coin_mean coin_var one_pos 0
      (hshock0.trans (E_shock_zero coin_mean 0).symm)

/-- Cochrane (2023), p. 379 ("This stationary point must be stable … Many paths lead to
`Π_L`"): if `Φ(Π_L) = Π_L > 0`, `|Φ′(Π_L)| < 1` and the rule respects the zero bound on
`(0, ∞)`, then `1/Φ(1/·)` contracts towards `1/Π_L` on a ball of inverse inflation, with rate
`λ = (1 + |Φ′(Π_L)|)/2`, as `lower_sunspot` requires. -/
theorem lower_contraction_of_deriv {r : ℝ} {Φ : ℝ → ℝ} {PL d : ℝ} (hPL : 0 < PL)
    (hfix : Φ PL = PL) (hd : HasDerivAt Φ d PL) (hd1 : |d| < 1)
    (hbd : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) :
    ∃ ρ > 0, ∀ y, |y - 1 / PL| ≤ ρ →
      0 < y ∧ (1 + r)⁻¹ ≤ Φ (1 / y) ∧
        |1 / Φ (1 / y) - 1 / PL| ≤ (1 + |d|) / 2 * |y - 1 / PL| := by
  obtain ⟨hh, hk⟩ := hasDerivAt_inv_pair hPL hfix hd
  have hP2 : 0 < PL ^ 2 := by positivity
  have hab : |-d / PL ^ 2| < (1 + |d|) / 2 * |-1 / PL ^ 2| := by
    rw [neg_div, neg_div, abs_neg, abs_neg, abs_div, abs_div, abs_one, abs_of_pos hP2,
      ← mul_div_assoc, mul_one]
    exact div_lt_div_of_pos_right (by linarith) hP2
  obtain ⟨δ, hδ, hcmp⟩ := abs_sub_le_of_hasDerivAt hh hk (by positivity) hab
  refine ⟨min (1 / (2 * PL)) (δ / (4 * PL ^ 2)), lt_min (by positivity) (by positivity),
    fun y hy => ?_⟩
  have hy1 : |y - 1 / PL| ≤ 1 / (2 * PL) := hy.trans (min_le_left _ _)
  have hy2 : |y - 1 / PL| ≤ δ / (4 * PL ^ 2) := hy.trans (min_le_right _ _)
  have hylow : 1 / (2 * PL) ≤ y := by
    have := (abs_le.mp hy1).1
    have e : 1 / PL - 1 / (2 * PL) = 1 / (2 * PL) := by field_simp; ring
    linarith
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hylow
  have hnear : |1 / y - PL| < δ := by
    have e : 1 / y - PL = PL * (1 / PL - y) / y := by field_simp
    rw [e, abs_div, abs_mul, abs_of_pos hPL, abs_of_pos hy0, abs_sub_comm]
    rw [div_lt_iff₀ hy0]
    have h1 : PL * |y - 1 / PL| ≤ PL * (δ / (4 * PL ^ 2)) := mul_le_mul_of_nonneg_left hy2 hPL.le
    have h2 : PL * (δ / (4 * PL ^ 2)) = δ / (4 * PL) := by field_simp
    have h3 : δ / (4 * PL) < δ * y := by
      rw [div_lt_iff₀ (by positivity)]
      have : 1 / (2 * PL) * (4 * PL) = 2 := by field_simp; norm_num
      nlinarith [mul_le_mul_of_nonneg_right hylow (by positivity : (0 : ℝ) ≤ 4 * PL)]
    linarith
  have h := hcmp (1 / y) hnear
  simp only [hfix, one_div_one_div] at h
  exact ⟨hy0, hbd _ (one_div_pos.mpr hy0), h⟩

/-- Cochrane (2023), p. 379, "there are 'multiple local equilibria' near this point", from the
derivative: if `Φ` is measurable, `Φ(Π_L) = Π_L > 0`, `|Φ′(Π_L)| < 1` and the rule respects the
zero bound on `(0, ∞)`, the i.i.d. coin economy has a genuinely random equilibrium that starts at
`Π_L` and keeps inverse inflation near `1/Π_L` forever. -/
theorem lower_sunspot_of_deriv {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} (hΦm : Measurable Φ)
    {PL d : ℝ} (hPL : 0 < PL) (hfix : Φ PL = PL) (hd : HasDerivAt Φ d PL) (hd1 : |d| < 1)
    (hbd : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) :
    ∃ ρ > 0, ∃ infl i : ℕ → (ℕ → ℝ) → ℝ, MeasStochEq (iidSystem coin) r Φ infl i ∧
      (∀ t ω, |1 / infl t ω - 1 / PL| ≤ ρ) ∧ infl 0 = (fun _ => PL) ∧
      ¬ infl 1 =ᵐ[(iidSystem coin).μ] fun _ => PL := by
  obtain ⟨ρ, hρ, hball⟩ := lower_contraction_of_deriv (r := r) hPL hfix hd hd1 hbd
  exact ⟨ρ, hρ, lower_sunspot hr hΦm hPL hfix hρ (by positivity) (by linarith) hball⟩

end Cochrane.NewKeynesianSelection.TidyR6StochasticMeasure
