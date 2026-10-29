/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR6StrictSignRule
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The strict sign rule on a probability space

Cochrane (2023), Online Appendix §A1.14.2, p. 592 (last bullet), equations (1.65)–(1.66).

A genuine probability space `(Ω, μ)` with date-0 information `m ≤ mΩ`, and `E_0 = μ[· | m]`
(Mathlib's conditional expectation; every statement holds almost surely).

* `condExp_pos_iff_ae`: **the conditional expectation is strictly positive exactly on events of
  positive conditional probability.** If `f > 0` on a measurable `B` and `f = 0` off `B`, then
  almost surely `μ[f | m] > 0 ↔ μ[1_B | m] > 0`. `condExp_pos_ae`: `f > 0` everywhere gives
  `μ[f | m] > 0` almost surely. `condExp_bot_pos_iff`: with trivial date-0 information,
  `μ[f | ⊥] > 0` everywhere iff `μ B > 0`.
* `x0M`, `x0M66`, `x0M66_ae_eq`: the closed form (1.66) for `1/P_0` with `E_0 = μ[· | m]`, as
  printed (`x0M66`) and with the date-0 fraction `A₁` pulled out (`x0M`, the form of
  `TidyR5FutureSalesRandom.x0R_pull`); they agree almost surely.
* `x0M_strict_iff_ae`, `x0M66_strict_iff_ae`: **the strict sign rule under the book's sign
  conditions alone** (`A₁ > A₂`, `B_0^{(2)} > 0`, `s_2 > 0`, `B_{−1}^{(0)} > 0`, larger sales
  `G ≥ 0`, and only the integrability that makes (1.66) meaningful): almost surely, larger
  state-contingent future sales strictly lower `P_0` iff the larger sale has positive conditional
  probability `μ[1_{G>0} | m] > 0`. `x0M_mono_ae` is the weak rule.
  `x0M_strictMono_ae`: if `G > 0` everywhere, the rule is strict almost surely.
* `x0_ae_eq_x0M66`: in every equilibrium of the three-period economy (flow conditions (7.1) at
  dates 2, 1, 0 with `E_t = μ[· | 𝓕_t]`, almost surely), `1/P_0 = x0M66` almost surely.
  `eqm_strict_iff_ae`: the strict sign rule for equilibrium price levels.
* `x0M_bot_strict_iff`: with trivial date-0 information (the book's three-period economy has
  date-0 debt known at 0), larger sales strictly lower `P_0` iff `μ{G > 0} > 0`, in every state.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure

open MeasureTheory Filter TidyR5FutureSalesRandom TidyR6StrictSignRule

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Cochrane (2023), Online Appendix p. 592 (measure theory): a nonnegative integrable function
whose integral over a measurable set is nonpositive vanishes almost everywhere on that set. -/
theorem ae_zero_on_of_setIntegral_nonpos {h : Ω → ℝ} {Z : Set Ω} (hZ : MeasurableSet Z)
    (h0 : 0 ≤ᵐ[μ] h) (hi : Integrable h μ) (hle : ∫ x in Z, h x ∂μ ≤ 0) :
    ∀ᵐ ω ∂μ, ω ∈ Z → h ω = 0 := by
  have hnn : 0 ≤ ∫ x in Z, h x ∂μ := setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae h0)
  have heq : ∫ x in Z, h x ∂μ = 0 := le_antisymm hle hnn
  have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae h0) hi.integrableOn).1 heq
  exact (ae_restrict_iff' hZ).1 h1

/-- Cochrane (2023), Online Appendix p. 592 (on a probability space): **the conditional
expectation is strictly positive exactly where the event has positive conditional probability.**
If `f > 0` on a measurable set `B` and `f = 0` off `B`, then almost surely
`0 < μ[f | m] ↔ 0 < μ[1_B | m]`. -/
theorem condExp_pos_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → ℝ} {B : Set Ω}
    (hB : MeasurableSet B) (hfi : Integrable f μ) (hpos : ∀ ω ∈ B, 0 < f ω)
    (hzero : ∀ ω ∉ B, f ω = 0) :
    ∀ᵐ ω ∂μ, (0 < μ[f | m] ω ↔ 0 < μ[B.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  set ind : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hind
  have hii : Integrable ind μ := (integrable_const (1 : ℝ)).indicator hB
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by
    by_cases h : ω ∈ B
    · exact (hpos ω h).le
    · exact (hzero ω h).ge
  have hind0 : ∀ ω, 0 ≤ ind ω := fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hg0 : 0 ≤ᵐ[μ] μ[f | m] := condExp_nonneg (ae_of_all _ hf0)
  have hp0 : 0 ≤ᵐ[μ] μ[ind | m] := condExp_nonneg (ae_of_all _ hind0)
  -- Step 1: where `μ[f | m] ≤ 0`, the conditional probability of `B` vanishes.
  have hZm : MeasurableSet[m] (μ[f | m] ⁻¹' Set.Iic 0) :=
    stronglyMeasurable_condExp.measurable measurableSet_Iic
  have hZ := hm _ hZm
  have A1 : ∀ᵐ ω ∂μ, ω ∈ μ[f | m] ⁻¹' Set.Iic 0 → μ[ind | m] ω = 0 := by
    have hgZ : ∫ x in μ[f | m] ⁻¹' Set.Iic 0, (μ[f | m]) x ∂μ ≤ 0 :=
      setIntegral_nonpos hZ (fun x hx => hx)
    rw [setIntegral_condExp hm hfi hZm] at hgZ
    have hfZ := ae_zero_on_of_setIntegral_nonpos hZ (ae_of_all _ hf0) hfi hgZ
    have hindZ : ∫ x in μ[f | m] ⁻¹' Set.Iic 0, ind x ∂μ = 0 := by
      refine integral_eq_zero_of_ae ((ae_restrict_iff' hZ).2 ?_)
      filter_upwards [hfZ] with ω hω hωZ
      have h1 := hω hωZ
      have hnB : ω ∉ B := fun hb => (hpos ω hb).ne' h1
      simp [hind, hnB]
    rw [← setIntegral_condExp hm hii hZm] at hindZ
    exact ae_zero_on_of_setIntegral_nonpos hZ hp0 integrable_condExp hindZ.le
  -- Step 2: where `μ[1_B | m] ≤ 0`, the conditional expectation of `f` vanishes.
  have hZm' : MeasurableSet[m] (μ[ind | m] ⁻¹' Set.Iic 0) :=
    stronglyMeasurable_condExp.measurable measurableSet_Iic
  have hZ' := hm _ hZm'
  have A2 : ∀ᵐ ω ∂μ, ω ∈ μ[ind | m] ⁻¹' Set.Iic 0 → μ[f | m] ω = 0 := by
    have hpZ : ∫ x in μ[ind | m] ⁻¹' Set.Iic 0, (μ[ind | m]) x ∂μ ≤ 0 :=
      setIntegral_nonpos hZ' (fun x hx => hx)
    rw [setIntegral_condExp hm hii hZm'] at hpZ
    have hiZ := ae_zero_on_of_setIntegral_nonpos hZ' (ae_of_all _ hind0) hii hpZ
    have hfZ : ∫ x in μ[ind | m] ⁻¹' Set.Iic 0, f x ∂μ = 0 := by
      refine integral_eq_zero_of_ae ((ae_restrict_iff' hZ').2 ?_)
      filter_upwards [hiZ] with ω hω hωZ
      have h1 := hω hωZ
      have hnB : ω ∉ B := fun hb => by simp [hind, hb] at h1
      exact hzero ω hnB
    rw [← setIntegral_condExp hm hfi hZm'] at hfZ
    exact ae_zero_on_of_setIntegral_nonpos hZ' hg0 integrable_condExp hfZ.le
  filter_upwards [A1, A2, hg0, hp0] with ω h1 h2 hg hp
  constructor
  · intro hgpos
    by_contra hle
    push Not at hle
    have := h2 hle
    linarith
  · intro hppos
    by_contra hle
    push Not at hle
    have := h1 hle
    linarith

/-- Cochrane (2023), Online Appendix p. 592 (on a probability space): a strictly positive
integrable random variable has a strictly positive conditional expectation almost surely, with no
uniform lower bound. -/
theorem condExp_pos_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {f : Ω → ℝ} (hfi : Integrable f μ)
    (hpos : ∀ ω, 0 < f ω) : ∀ᵐ ω ∂μ, 0 < μ[f | m] ω := by
  have h := condExp_pos_iff_ae (m := m) hm MeasurableSet.univ hfi (fun ω _ => hpos ω)
    (fun ω h => absurd (Set.mem_univ ω) h)
  rw [Set.indicator_univ, condExp_const hm] at h
  filter_upwards [h] with ω hω
  exact hω.2 one_pos

/-- Cochrane (2023), Online Appendix p. 592 (on a probability space, trivial date-0
information): if `f > 0` on a measurable `B` and `f = 0` off `B`, then `μ[f | ⊥] > 0` in every
state iff `μ B > 0`. -/
theorem condExp_bot_pos_iff [IsProbabilityMeasure μ] {f : Ω → ℝ} {B : Set Ω}
    (hfi : Integrable f μ) (hpos : ∀ ω ∈ B, 0 < f ω) (hzero : ∀ ω ∉ B, f ω = 0) (ω : Ω) :
    0 < μ[f | ⊥] ω ↔ 0 < μ B := by
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => by
    by_cases h : ω ∈ B
    · exact (hpos ω h).le
    · exact (hzero ω h).ge
  have hsupp : Function.support f = B := by
    ext ω
    simp only [Function.mem_support]
    constructor
    · intro h; by_contra hb; exact h (hzero ω hb)
    · intro hb; exact (hpos ω hb).ne'
  rw [condExp_bot', probReal_univ, inv_one, one_smul, ← hsupp]
  exact integral_pos_iff_support_of_nonneg_ae (ae_of_all _ hf0) hfi

/-! ### The closed form (1.66) with `E_0 = μ[· | m]` -/

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, on a probability space, with the date-0
fraction pulled out (the form of `TidyR5FutureSalesRandom.x0R_pull`):
`1/P_0 = (s_0 + A₁ E_0(β s_1 + β² s_2) + E_0(kCoef/B_1^{(2)}(ε)))/B_{−1}^{(0)}`. -/
noncomputable def x0M (mi : MeasurableSpace Ω) (μ : @Measure Ω mΩ) (β : ℝ) (D : ℕ → ℕ → Ω → ℝ)
    (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) : Ω → ℝ :=
  (s 0 + fracA D 1 * μ[β • s 1 + β ^ 2 • s 2 | mi] +
    μ[kCoef β D s / (D 2 2 + ε • G) | mi]) / D 0 0

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, on a probability space, as printed:
`B_{−1}^{(0)}/P_0 = s_0 + A₁ E_0[β s_1 + β² ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) s_2]
+ E_0[β² ((B_0^{(2)} − B_{−1}^{(2)})/B_1^{(2)}) s_2]`, with `B_1^{(2)}(ε) = B_1^{(2)} + ε G`. -/
noncomputable def x0M66 (mi : MeasurableSpace Ω) (μ : @Measure Ω mΩ) (β : ℝ) (D : ℕ → ℕ → Ω → ℝ)
    (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) : Ω → ℝ :=
  (s 0 + fracA D 1 *
      μ[β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2) | mi] +
    μ[β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2) | mi]) / D 0 0

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, on a probability space: the printed
form and the pulled-out form agree almost surely, when `A₁` is known at date 0 and the
expectations in (1.66) exist. -/
theorem x0M66_ae_eq {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hA1 : StronglyMeasurable[m] (fracA D 1)) (hne : ∀ ω, D 2 2 ω + ε * G ω ≠ 0)
    (i1 : Integrable (β • s 1 + β ^ 2 • s 2) μ)
    (i2 : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) μ)
    (i3 : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)))) μ)
    (i4 : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) μ) :
    x0M66 m μ β D G s ε =ᵐ[μ] x0M m μ β D G s ε := by
  have hsplit : β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2) =
      (β • s 1 + β ^ 2 • s 2) - β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)) := by
    funext ω
    have := hne ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.sub_apply]
    field_simp
    ring
  have hk : β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2) -
      fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) = kCoef β D s / (D 2 2 + ε • G) := by
    funext ω
    have := hne ω
    simp only [kCoef, fracA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
      Pi.div_apply, Pi.add_apply]
    field_simp
  have e1 := condExp_sub (m := m) i1 i2
  have e2 := condExp_mul_of_stronglyMeasurable_left (μ := μ) hA1 i3 i2
  have e3 := condExp_sub (m := m) i4 i3
  rw [hk] at e3
  rw [← hsplit] at e1
  filter_upwards [e1, e2, e3] with ω h1 h2 h3
  simp only [x0M66, x0M, Pi.div_apply, Pi.add_apply, Pi.mul_apply]
  rw [h1, h3]
  simp only [Pi.sub_apply]
  rw [h2]
  simp only [Pi.mul_apply]
  ring

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space: **the weak
sign rule** under the book's sign conditions: almost surely `1/P_0` is larger with the larger
sale. -/
theorem x0M_mono_ae {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hG0 : ∀ ω, 0 ≤ G ω)
    (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω) (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω)
    (hD00 : ∀ ω, 0 < D 0 0 ω) (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) :
    ∀ᵐ ω ∂μ, x0M m μ β D G s ε ω ≤ x0M m μ β D G s ε' ω := by
  obtain ⟨hnn, -⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have e := condExp_sub (m := m) hi' hi
  have hc : 0 ≤ᵐ[μ] μ[dilDiff β D G s ε ε' | m] := condExp_nonneg (ae_of_all _ hnn)
  filter_upwards [e, hc] with ω he hc
  simp only [dilDiff] at hc
  rw [he] at hc
  simp only [x0M, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hc ⊢
  apply div_le_div_of_nonneg_right _ (hD00 ω).le
  linarith

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space: **the exact
strict sign rule under the book's sign conditions alone.** With `A₁ > A₂`, `B_0^{(2)} > 0`,
`s_2 > 0`, `β ≠ 0`, `B_{−1}^{(0)} > 0`, a measurable larger sale `G ≥ 0` and `ε < ε'`, and the
two dilution expectations of (1.66) defined (integrable), almost surely: larger
state-contingent future sales strictly lower `P_0` iff `μ[1_{G>0} | m] > 0`. -/
theorem x0M_strict_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hGm : Measurable G)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) :
    ∀ᵐ ω ∂μ, (x0M m μ β D G s ε ω < x0M m μ β D G s ε' ω ↔
      0 < μ[{ω | 0 < G ω}.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have hB : MeasurableSet {ω | 0 < G ω} := measurableSet_lt measurable_const hGm
  have hfpos : ∀ ω ∈ {ω | 0 < G ω}, 0 < dilDiff β D G s ε ε' ω := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq.mp hω, ↓reduceIte] at this
    by_contra h
    simp [h] at this
  have hfzero : ∀ ω ∉ {ω | 0 < G ω}, dilDiff β D G s ε ε' ω = 0 := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq] at this hω
    simp only [hω, ↓reduceIte] at this
    by_contra h
    have hp : 0 < dilDiff β D G s ε ε' ω := lt_of_le_of_ne (hnn ω) (Ne.symm h)
    simp [hp] at this
  have key := condExp_pos_iff_ae (m := m) hm hB (hi'.sub hi) hfpos hfzero
  have e := condExp_sub (m := m) hi' hi
  filter_upwards [key, e] with ω hk he
  rw [← hk, he]
  simp only [x0M, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  rw [← sub_pos, ← sub_div, div_pos_iff_of_pos_right (hD00 ω)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space: if the sale is
larger in every state (`G > 0`), larger future sales strictly lower `P_0` almost surely, with no
uniform bounds. -/
theorem x0M_strictMono_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hGm : Measurable G)
    (hG0 : ∀ ω, 0 < G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) :
    ∀ᵐ ω ∂μ, x0M m μ β D G s ε ω < x0M m μ β D G s ε' ω := by
  have h := x0M_strict_iff_ae hm hβ hGm (fun ω => (hG0 ω).le) hs2 h12 hA hD00 hpos hεε hi hi'
  have hset : {ω | 0 < G ω} = Set.univ := Set.eq_univ_of_forall hG0
  rw [hset, Set.indicator_univ, condExp_const hm] at h
  filter_upwards [h] with ω hω
  exact hω.2 one_pos

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space, as printed:
the exact strict sign rule for the printed closed form (1.66), almost surely, when `A₁` is known
at date 0 and the expectations in (1.66) exist at `ε` and `ε'`. -/
theorem x0M66_strict_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hGm : Measurable G)
    (hA1 : StronglyMeasurable[m] (fracA D 1))
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (i1 : Integrable (β • s 1 + β ^ 2 • s 2) μ)
    (i2 : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) μ)
    (i3 : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)))) μ)
    (i4 : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) μ)
    (i2' : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G))) μ)
    (i3' : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G)))) μ)
    (i4' : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε' • G) * s 2)) μ) :
    ∀ᵐ ω ∂μ, (x0M66 m μ β D G s ε ω < x0M66 m μ β D G s ε' ω ↔
      0 < μ[{ω | 0 < G ω}.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by nlinarith [hpos ω, hG0 ω]
  have hk : ∀ e : ℝ, (∀ ω, D 2 2 ω + e * G ω ≠ 0) →
      β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + e • G) * s 2) -
        fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + e • G))) =
        kCoef β D s / (D 2 2 + e • G) := fun e hne => by
    funext ω
    have := hne ω
    simp only [kCoef, fracA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
      Pi.div_apply, Pi.add_apply]
    field_simp
  have hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ := by
    rw [← hk ε (fun ω => (hpos ω).ne')]; exact i4.sub i3
  have hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ := by
    rw [← hk ε' (fun ω => (hpos' ω).ne')]; exact i4'.sub i3'
  have h := x0M_strict_iff_ae hm hβ hGm hG0 hs2 h12 hA hD00 hpos hεε hi hi'
  have q := x0M66_ae_eq hA1 (fun ω => (hpos ω).ne') i1 i2 i3 i4
  have q' := x0M66_ae_eq hA1 (fun ω => (hpos' ω).ne') i1 i2' i3' i4'
  filter_upwards [h, q, q'] with ω hω hq hq'
  rw [hq, hq']
  exact hω

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space with trivial
date-0 information (`m = ⊥`; date-0 quantities are numbers, as in the book): **in every state,
larger future sales strictly lower `P_0` iff the larger sale has positive probability,
`μ{G > 0} > 0`.** -/
theorem x0M_bot_strict_iff [IsProbabilityMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hi : Integrable (kCoef β D s / (D 2 2 + ε • G)) μ)
    (hi' : Integrable (kCoef β D s / (D 2 2 + ε' • G)) μ) (ω : Ω) :
    x0M ⊥ μ β D G s ε ω < x0M ⊥ μ β D G s ε' ω ↔ 0 < μ {ω | 0 < G ω} := by
  obtain ⟨hnn, hev⟩ := dilDiff_sign hβ hG0 hs2 h12 hA hpos hεε
  have hfpos : ∀ ω ∈ {ω | 0 < G ω}, 0 < dilDiff β D G s ε ε' ω := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq.mp hω, ↓reduceIte] at this
    by_contra h
    simp [h] at this
  have hfzero : ∀ ω ∉ {ω | 0 < G ω}, dilDiff β D G s ε ε' ω = 0 := fun ω hω => by
    have := congrFun hev ω
    simp only [posEvent, Set.mem_ofPred_eq] at this hω
    simp only [hω, ↓reduceIte] at this
    by_contra h
    have hp : 0 < dilDiff β D G s ε ε' ω := lt_of_le_of_ne (hnn ω) (Ne.symm h)
    simp [hp] at this
  rw [← condExp_bot_pos_iff (hi'.sub hi) hfpos hfzero ω]
  have e1 : ∫ x, (kCoef β D s / (D 2 2 + ε' • G) - kCoef β D s / (D 2 2 + ε • G)) x ∂μ =
      ∫ x, (kCoef β D s / (D 2 2 + ε' • G)) x ∂μ - ∫ x, (kCoef β D s / (D 2 2 + ε • G)) x ∂μ :=
    integral_sub hi' hi
  simp only [x0M, condExp_bot', probReal_univ, inv_one, one_smul]
  rw [e1]
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply]
  rw [← sub_pos, ← sub_div, div_pos_iff_of_pos_right (hD00 ω)]
  constructor <;> intro h <;> linarith

/-! ### From the flow conditions to (1.66) on a probability space -/

/-- Cochrane (2023), Online Appendix eqs. (1.63)–(1.66), pp. 589–591, on a probability space:
**in every equilibrium of the three-period economy, `1/P_0` is the printed closed form (1.66)
almost surely.** Date-0 information `m ≤ m1` (date-1 information), `E_t = μ[· | 𝓕_t]`; the flow
conditions (7.1) at dates 2, 1, 0 (as in `FutureSales.flows_of_realFlow`) hold, the first
everywhere and the others almost surely, with the date-1 sale `B_1^{(2)}(ε) = B_1^{(2)} + ε G`;
`B_0^{(1)}`, `B_0^{(2)} − B_{−1}^{(2)}` are known at 0 and `B_1^{(2)}(ε) − B_0^{(2)}` at 1; the
conditional expectations in the flow conditions exist (integrability). -/
theorem x0_ae_eq_x0M66 {m1 : MeasurableSpace Ω} (hm01 : m ≤ m1) (hm1 : m1 ≤ mΩ)
    [IsFiniteMeasure μ] {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hu : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (hD00 : ∀ ω, D 0 0 ω ≠ 0)
    (mu : StronglyMeasurable[m1] (D 2 2 + ε • G - D 1 2)) (m11 : StronglyMeasurable[m] (D 1 1))
    (m12 : StronglyMeasurable[m] (D 1 2 - D 0 2))
    (F2 : (D 2 2 + ε • G) * x 2 = s 2)
    (F1 : D 1 1 * x 1 =ᵐ[μ] s 1 + β • ((D 2 2 + ε • G - D 1 2) * μ[x 2 | m1]))
    (F0 : D 0 0 * x 0 =ᵐ[μ] s 0 + β • ((D 1 1 - D 0 1) * μ[x 1 | m]) +
      β ^ 2 • ((D 1 2 - D 0 2) * μ[x 2 | m]))
    (ix1 : Integrable (x 1) μ) (ix2 : Integrable (x 2) μ) (is1 : Integrable (s 1) μ)
    (ia : Integrable ((D 2 2 + ε • G - D 1 2) * x 2) μ) (ib : Integrable (D 1 1 * x 1) μ)
    (ic : Integrable ((D 1 2 - D 0 2) * x 2) μ) :
    x 0 =ᵐ[μ] x0M66 m μ β D G s ε := by
  set u := D 2 2 + ε • G with hu_def
  have hx2 : ∀ ω, x 2 ω = s 2 ω / u ω := fun ω => by
    have := congrFun F2 ω
    simp only [Pi.mul_apply] at this
    have hne : u ω ≠ 0 := by simpa [hu_def] using hu ω
    rw [eq_div_iff hne, ← this, mul_comm]
  have hf1 : β • s 1 + β ^ 2 • ((u - D 1 2) / u * s 2) =
      β • (s 1 + β • ((u - D 1 2) * x 2)) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.sub_apply, hx2 ω]
    ring
  have hf2 : β ^ 2 • ((D 1 2 - D 0 2) / u * s 2) = β ^ 2 • ((D 1 2 - D 0 2) * x 2) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, hx2 ω]
    ring
  have hx0M : x0M66 m μ β D G s ε = (s 0 + fracA D 1 * μ[β • (s 1 + β • ((u - D 1 2) * x 2)) | m]
      + μ[β ^ 2 • ((D 1 2 - D 0 2) * x 2) | m]) / D 0 0 := by
    unfold x0M66
    rw [← hf1, ← hf2]
  have eb := condExp_mul_of_stronglyMeasurable_left (μ := μ) mu ia ix2
  have iub : Integrable ((u - D 1 2) * μ[x 2 | m1]) μ := integrable_condExp.congr eb
  have a1 := condExp_smul (μ := μ) β (s 1 + β • ((u - D 1 2) * x 2)) m
  have a2 := condExp_add (m := m) is1 (ia.smul β)
  have a2' := condExp_smul (μ := μ) β ((u - D 1 2) * x 2) m
  have a3 := condExp_mul_of_stronglyMeasurable_left (μ := μ) m11 ib ix1
  have a4 := condExp_congr_ae (m := m) F1
  have a5 := condExp_add (m := m) is1 (iub.smul β)
  have a5' := condExp_smul (μ := μ) β ((u - D 1 2) * μ[x 2 | m1]) m
  have a6 := condExp_congr_ae (m := m) eb.symm
  have a7 := condExp_condExp_of_le (μ := μ) (f := (u - D 1 2) * x 2) hm01 hm1
  have a8 := condExp_smul (μ := μ) (β ^ 2) ((D 1 2 - D 0 2) * x 2) m
  have a9 := condExp_mul_of_stronglyMeasurable_left (μ := μ) m12 ic ix2
  rw [hx0M]
  filter_upwards [a1, a2, a2', a3, a4, a5, a5', a6, a7, a8, a9, F0] with ω h1 h2 h2' h3 h4 h5 h5'
    h6 h7 h8 h9 h0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h1 h2 h2' h5 h5' h8
  simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3 h9 h0
  simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply]
  rw [h1, h2, h2', h8, h9]
  rw [h3, h5, h5', h6, h7] at h4
  rw [eq_div_iff (hD00 ω), mul_comm, h0]
  simp only [fracA, Pi.sub_apply, Pi.div_apply] at h0 ⊢
  field_simp [hD11 ω]
  linear_combination (β * (D 1 1 ω - D 0 1 ω)) * h4

/-- Cochrane (2023), Online Appendix p. 592 (last bullet), on a probability space, **for
equilibrium prices**: if `x` is an equilibrium with the sale `B_1^{(2)} + ε G` and `x'` one with
`B_1^{(2)} + ε' G` (`x0_ae_eq_x0M66`), then under the book's sign conditions, almost surely,
`P'_0 < P_0` iff `μ[1_{G>0} | m] > 0`. -/
theorem eqm_strict_iff_ae (hm : m ≤ mΩ) [IsFiniteMeasure μ] {β ε ε' : ℝ} (hβ : β ≠ 0)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {x x' s : ℕ → Ω → ℝ} (hGm : Measurable G) (hA1 : StronglyMeasurable[m] (fracA D 1))
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 < s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω < fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε < ε')
    (hx : x 0 =ᵐ[μ] x0M66 m μ β D G s ε) (hx' : x' 0 =ᵐ[μ] x0M66 m μ β D G s ε')
    (i1 : Integrable (β • s 1 + β ^ 2 • s 2) μ)
    (i2 : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) μ)
    (i3 : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)))) μ)
    (i4 : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) μ)
    (i2' : Integrable (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G))) μ)
    (i3' : Integrable (fracA D 1 * (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε' • G)))) μ)
    (i4' : Integrable (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε' • G) * s 2)) μ) :
    ∀ᵐ ω ∂μ, (x 0 ω < x' 0 ω ↔ 0 < μ[{ω | 0 < G ω}.indicator (fun _ => (1 : ℝ)) | m] ω) := by
  have h := x0M66_strict_iff_ae hm hβ hGm hA1 hG0 hs2 h12 hA hD00 hpos hεε i1 i2 i3
    i4 i2' i3' i4'
  filter_upwards [h, hx, hx'] with ω hω e e'
  rw [e, e']
  exact hω

end Cochrane.LongTermDebtDynamics.TidyR6StrictSignMeasure
