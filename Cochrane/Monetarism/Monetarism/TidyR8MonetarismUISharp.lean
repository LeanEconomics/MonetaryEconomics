/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismUI
import Monetarism.TidyR7MonetarismCoinInf
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# The sharp condition for the printed `E_t∫_t^∞` forms of (1.33) and (1.34)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34).

`TidyR7MonetarismValuation` proves the printed `n_sB_s = E_s[∫_s^∞ …]` under domination
(`TidyR7MonetarismValuation.valuation_iff_tvc_dom`) or `L¹` convergence of the flows, and
`TidyR7MonetarismUI.ui_headline` shows that without such a hypothesis it can fail while the
transversality condition and the limit form hold. Here the condition is characterised.

## The characterisation

Let `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s` (the finite-horizon budgets), let the flows
`F_{T_k}` converge almost surely to `G` (the pathwise `∫_s^∞`) and be bounded below by `−h`,
`h` integrable (for instance nonnegative surpluses, or bounded flows).
* `valuation_iff_condL1_char`: under the almost-sure transversality condition,
  `Y_s = E_s[G]` a.s. **iff** `E_s|F_{T_k} − G| → 0` a.s. (conditional `L¹` convergence);
* `valuation_iff_L1_char`: under the `L¹` transversality condition, `Y_s = E_s[G]` a.s. **iff**
  `F_{T_k} → G` in `L¹`, **iff** the flows are uniformly integrable
  (`tendsto_integral_abs_iff_unifIntegrable`, Vitali);
* domination `|F_{T_k}| ≤ H` is one sufficient case; the reverse implications ("printed ⇒ `L¹`")
  are new and show the condition is necessary.
* The lower bound cannot be dropped from "printed ⇒ `L¹`": `sgn_headline` (signed flows with
  `E[F_{T_k}] = 0`, `F_{T_k} → 0` path by path, `E|F_{T_k}| = 2`; the printed form and the
  transversality condition hold, and no integrable lower bound exists, `sgn_no_lower_bound`).

Tools: `ae_tendsto_condExp_of_dominated_ae` (conditional dominated convergence with almost-sure
hypotheses), `tendsto_integral_abs_sub_of_nonneg` (Scheffé's lemma) and its conditional form
`ae_tendsto_condExp_abs_sub_of_nonneg`.

## In the economy

`valuation_1_33_char_L1`, `valuation_1_33_char_cond` ((1.33), `i^m = 0`) and
`valuation_1_34_char_L1`, `valuation_1_34_char_cond` ((1.34)) in
`TidyR7MonetarismModel.MonetaryModel`. Instances: `ui_char` (the counterexample of
`TidyR7MonetarismUI`: nonnegative flows, so the characterisation applies; the printed form
fails, hence the flows are not `L¹`, not conditionally `L¹` and not uniformly integrable) and
`inf_char` (the economy of `TidyR7MonetarismCoinInf`: bounded flows, `L¹`, printed form holds).
-/

namespace Cochrane.Monetarism.TidyR8MonetarismUISharp

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismValuation
open Cochrane.Monetarism.TidyR7ProductStep (addProc)

variable {Ω : Type*}

/-! ## Tools -/

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (tool): conditional dominated convergence with
almost-sure hypotheses.** If the `F_k` are a.e. strongly measurable, `|F_k| ≤ D` a.s. with `D`
integrable and `F_k → f` a.s., then `E[F_k | 𝓖] → E[f | 𝓖]` a.s.
Generalises `TidyR7CondDominated.ae_tendsto_condExp_of_dominated` (everywhere hypotheses,
measurable `F_k`), to which it reduces by modifying `F_k` on a null set. -/
theorem ae_tendsto_condExp_of_dominated_ae {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {F : ℕ → Ω → ℝ} {f D : Ω → ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ) (hD : Integrable D μ)
    (hbd : ∀ k, ∀ᵐ ω ∂μ, |F k ω| ≤ D ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => F k ω) atTop (𝓝 (f ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[F k | m] ω) atTop (𝓝 (μ[f | m] ω)) := by
  set F' : ℕ → Ω → ℝ := fun k => (hF k).mk (F k) with hF'
  have hgood : ∀ᵐ ω ∂μ, (∀ k, F k ω = F' k ω) ∧ (∀ k, |F k ω| ≤ D ω) ∧
      Tendsto (fun k => F k ω) atTop (𝓝 (f ω)) := by
    have h1 : ∀ᵐ ω ∂μ, ∀ k, F k ω = F' k ω := ae_all_iff.2 fun k => (hF k).ae_eq_mk
    filter_upwards [h1, ae_all_iff.2 hbd, hlim] with ω a b c
    exact ⟨a, b, c⟩
  set S : Set Ω := toMeasurable μ {ω | ¬ ((∀ k, F k ω = F' k ω) ∧ (∀ k, |F k ω| ≤ D ω) ∧
      Tendsto (fun k => F k ω) atTop (𝓝 (f ω)))} with hS
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hS0 : μ S = 0 := by rw [hS, measure_toMeasurable]; exact ae_iff.1 hgood
  have hgoodS : ∀ ω, ω ∉ S → (∀ k, F k ω = F' k ω) ∧ (∀ k, |F k ω| ≤ D ω) ∧
      Tendsto (fun k => F k ω) atTop (𝓝 (f ω)) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hnS : ∀ᵐ ω ∂μ, ω ∉ S := measure_eq_zero_iff_ae_notMem.1 hS0
  set G : ℕ → Ω → ℝ := fun k => Sᶜ.indicator (F' k) with hG
  set g : Ω → ℝ := Sᶜ.indicator f with hg
  have hGm : ∀ k, Measurable (G k) := fun k =>
    ((hF k).stronglyMeasurable_mk.measurable).indicator hSm.compl
  have hGb : ∀ k ω, |G k ω| ≤ |D ω| := by
    intro k ω
    by_cases hω : ω ∈ S
    · simp [hG, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω)]
    · have := hgoodS ω hω
      simp only [hG, Set.indicator_of_mem (Set.mem_compl hω)]
      rw [← this.1 k]
      exact (this.2.1 k).trans (le_abs_self _)
  have hGl : ∀ ω, Tendsto (fun k => G k ω) atTop (𝓝 (g ω)) := by
    intro ω
    by_cases hω : ω ∈ S
    · simp only [hG, hg, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω)]
      exact tendsto_const_nhds
    · have := hgoodS ω hω
      simp only [hG, hg, Set.indicator_of_mem (Set.mem_compl hω)]
      exact this.2.2.congr fun k => this.1 k
  have hc := ae_tendsto_condExp_of_dominated hm hGm hD.abs hGb hGl
  have hGF : ∀ k, μ[G k | m] =ᵐ[μ] μ[F k | m] := fun k => condExp_congr_ae (by
    filter_upwards [hnS] with ω hω
    simp only [hG, Set.indicator_of_mem (Set.mem_compl hω)]
    exact ((hgoodS ω hω).1 k).symm)
  have hgf : μ[g | m] =ᵐ[μ] μ[f | m] := condExp_congr_ae (by
    filter_upwards [hnS] with ω hω
    simp only [hg, Set.indicator_of_mem (Set.mem_compl hω)])
  filter_upwards [hc, ae_all_iff.2 hGF, hgf] with ω h1 h2 h3
  rw [← h3]
  exact h1.congr fun k => h2 k

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (tool): `|a − b| = (a − b) + 2(b − a)⁺`. -/
theorem abs_sub_eq_add_two_max (a b : ℝ) : |a - b| = (a - b) + 2 * max (b - a) 0 := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
    ring

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (tool): Scheffé's lemma.** If `f_k ≥ 0` a.s.,
`f_k → g` a.s., all integrable, and `∫ f_k → ∫ g`, then `∫|f_k − g| → 0`. -/
theorem tendsto_integral_abs_sub_of_nonneg {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ k, Integrable (f k) μ) (hg : Integrable g μ) (hf0 : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => f k ω) atTop (𝓝 (g ω)))
    (hint : Tendsto (fun k => ∫ ω, f k ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ))) :
    Tendsto (fun k => ∫ ω, |f k ω - g ω| ∂μ) atTop (𝓝 0) := by
  have hp : ∀ k, Integrable (fun ω => max (g ω - f k ω) 0) μ := fun k =>
    (hg.sub (hf k)).pos_part
  have hid : ∀ k, ∫ ω, |f k ω - g ω| ∂μ =
      (∫ ω, f k ω ∂μ - ∫ ω, g ω ∂μ) + 2 * ∫ ω, max (g ω - f k ω) 0 ∂μ := by
    intro k
    have e : (fun ω => |f k ω - g ω|) = fun ω => (f k ω - g ω) + 2 * max (g ω - f k ω) 0 :=
      funext fun ω => abs_sub_eq_add_two_max _ _
    have i1 : Integrable (fun ω => f k ω - g ω) μ := (hf k).sub hg
    rw [e, integral_add i1 ((hp k).const_mul 2), integral_sub (hf k) hg,
      integral_const_mul]
  have hD : Tendsto (fun k => ∫ ω, max (g ω - f k ω) 0 ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun ω => |g ω|)
      (fun k => (hp k).aestronglyMeasurable) hg.abs (fun k => by
        filter_upwards [hf0 k] with ω h
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [le_abs_self (g ω)]) (abs_nonneg _))
      (by
        filter_upwards [hlim] with ω h
        have := ((tendsto_const_nhds (x := g ω)).sub h).max (tendsto_const_nhds (x := (0 : ℝ)))
        simpa using this)
    simpa using this
  simp_rw [hid]
  have := (hint.sub_const (∫ ω, g ω ∂μ)).add (hD.const_mul 2)
  simpa using this

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (tool): conditional Scheffé lemma.** If
`f_k ≥ 0` a.s., `f_k → g` a.s., all integrable, and `E[f_k | 𝓖] → E[g | 𝓖]` a.s., then
`E[|f_k − g| | 𝓖] → 0` a.s. -/
theorem ae_tendsto_condExp_abs_sub_of_nonneg {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ k, Integrable (f k) μ) (hg : Integrable g μ) (hf0 : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ f k ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => f k ω) atTop (𝓝 (g ω)))
    (hce : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[f k | m] ω) atTop (𝓝 (μ[g | m] ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => |f k ω - g ω| | m] ω) atTop (𝓝 0) := by
  set p : ℕ → Ω → ℝ := fun k ω => max (g ω - f k ω) 0 with hp_def
  have hp : ∀ k, Integrable (p k) μ := fun k => (hg.sub (hf k)).pos_part
  have hD := ae_tendsto_condExp_of_dominated_ae hm (F := p) (f := 0)
    (fun k => (hp k).aestronglyMeasurable) hg.abs (fun k => by
      filter_upwards [hf0 k] with ω h
      simp only [hp_def]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self (g ω)]) (abs_nonneg _))
    (by
      filter_upwards [hlim] with ω h
      have := ((tendsto_const_nhds (x := g ω)).sub h).max (tendsto_const_nhds (x := (0 : ℝ)))
      simpa [hp_def] using this)
  rw [condExp_zero] at hD
  have hid : ∀ k, ∀ᵐ ω ∂μ, μ[fun ω => |f k ω - g ω| | m] ω =
      (μ[f k | m] ω - μ[g | m] ω) + 2 * μ[p k | m] ω := by
    intro k
    have e : (fun ω => |f k ω - g ω|) = (f k - g) + (2 : ℝ) • p k :=
      funext fun ω => by
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hp_def]
        exact abs_sub_eq_add_two_max _ _
    filter_upwards [condExp_add ((hf k).sub hg) ((hp k).smul (2 : ℝ)) m,
      condExp_sub (m := m) (hf k) hg, condExp_smul (μ := μ) (2 : ℝ) (p k) m] with ω h1 h2 h3
    rw [e, h1, Pi.add_apply, h2, h3]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  filter_upwards [ae_all_iff.2 hid, hce, hD] with ω h1 h2 h3
  simp_rw [h1]
  have := (h2.sub_const (μ[g | m] ω)).add (h3.const_mul 2)
  simpa using this

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (tool): `L¹` convergence is uniform
integrability** (Vitali, Mathlib `tendsto_Lp_finite_of_tendsto_ae`,
`unifIntegrable_of_tendsto_Lp`). For integrable `f_k → g` a.s. on a finite measure space,
`∫|f_k − g| → 0` iff `(f_k)` is uniformly integrable. -/
theorem tendsto_integral_abs_iff_unifIntegrable {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ k, Integrable (f k) μ)
    (hg : Integrable g μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => f k ω) atTop (𝓝 (g ω))) :
    Tendsto (fun k => ∫ ω, |f k ω - g ω| ∂μ) atTop (𝓝 0) ↔ UnifIntegrable f 1 μ := by
  have e : ∀ k, eLpNorm (f k - g) 1 μ = ENNReal.ofReal (∫ ω, |f k ω - g ω| ∂μ) := by
    intro k
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm
      ((hf k).sub hg)]
    · rfl
    · exact ((hf k).sub hg).aestronglyMeasurable
  constructor
  · intro h
    refine unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top
      (fun k => memLp_one_iff_integrable.2 (hf k)) (memLp_one_iff_integrable.2 hg) ?_
    simp_rw [e]
    simpa using ENNReal.tendsto_ofReal h
  · intro hui
    have h := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun k => (hf k).aestronglyMeasurable) (memLp_one_iff_integrable.2 hg) hui hlim
    simp_rw [e] at h
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    refine this.congr fun k => ?_
    simp only [Function.comp_apply]
    exact ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)

/-! ## The characterisation for a general flow -/

variable {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: the printed `E_s∫_s^∞` form iff `L¹`
convergence of the flows.** Let `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s`, times `T_k ≥ s`,
`F_{T_k}` integrable with `F_{T_k} → G` a.s. (`G` integrable) and `F_{T_k} ≥ −h` a.s. (`h`
integrable), and let the transversality condition hold in `L¹`,
`∫|E_s[Y_{T_k}]| → 0`. Then `Y_s = E_s[G]` a.s. **iff** `∫|F_{T_k} − G| → 0`.
The direction "⇐" needs neither the lower bound nor the a.s. limit.
Its "⇐" direction is `TidyR7MonetarismValuation.valuation_iff_tvc_flow` along a sequence `T_k`. -/
theorem valuation_iff_L1_char [IsFiniteMeasure μ] {Y F : ℝ → Ω → ℝ} {s : ℝ}
    (hrec : ∀ T, s ≤ T → Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[F T | 𝓕 s]) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) (hFi : ∀ k, Integrable (F (T k)) μ) {G h : Ω → ℝ}
    (hG : Integrable G μ) (hh : Integrable h μ) (hlow : ∀ k, ∀ᵐ ω ∂μ, -h ω ≤ F (T k) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => F (T k) ω) atTop (𝓝 (G ω)))
    (htvc : Tendsto (fun k => ∫ ω, |μ[Y (T k) | 𝓕 s] ω| ∂μ) atTop (𝓝 0)) :
    Y s =ᵐ[μ] μ[G | 𝓕 s] ↔ Tendsto (fun k => ∫ ω, |F (T k) ω - G ω| ∂μ) atTop (𝓝 0) := by
  constructor
  · intro hval
    have hYG : ∫ ω, Y s ω ∂μ = ∫ ω, G ω ∂μ := by
      rw [integral_congr_ae hval, integral_condExp (𝓕.le s)]
    have hFk : ∀ k, ∫ ω, F (T k) ω ∂μ =
        ∫ ω, Y s ω ∂μ - ∫ ω, μ[Y (T k) | 𝓕 s] ω ∂μ := by
      intro k
      rw [integral_congr_ae (hrec (T k) (hT k))]
      simp only [Pi.add_apply]
      rw [integral_add integrable_condExp integrable_condExp,
        integral_condExp (𝓕.le s) (f := F (T k))]
      ring
    have h0 : Tendsto (fun k => ∫ ω, μ[Y (T k) | 𝓕 s] ω ∂μ) atTop (𝓝 0) :=
      squeeze_zero_norm (fun k => by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ) (fun ω => μ[Y (T k) | 𝓕 s] ω)) htvc
    have hint : Tendsto (fun k => ∫ ω, F (T k) ω ∂μ) atTop (𝓝 (∫ ω, G ω ∂μ)) := by
      simp_rw [hFk]
      have := (tendsto_const_nhds (x := ∫ ω, Y s ω ∂μ)).sub h0
      rw [sub_zero] at this
      rw [← hYG]
      exact this
    have hS := tendsto_integral_abs_sub_of_nonneg (μ := μ) (f := fun k => F (T k) + h)
      (g := G + h) (fun k => (hFi k).add hh) (hG.add hh)
      (fun k => by
        filter_upwards [hlow k] with ω hω
        simp only [Pi.add_apply]
        linarith)
      (by
        filter_upwards [hlim] with ω hω
        exact hω.add_const (h ω))
      (by
        simp only [Pi.add_apply]
        rw [integral_add hG hh]
        simp_rw [integral_add (hFi _) hh]
        exact hint.add_const _)
    refine hS.congr fun k => ?_
    simp only [Pi.add_apply, add_sub_add_right_eq_sub]
  · intro hL
    set b : Ω → ℝ := fun ω => Y s ω - μ[G | 𝓕 s] ω with hb
    have hbk : ∀ k, b =ᵐ[μ] fun ω => μ[Y (T k) | 𝓕 s] ω + μ[F (T k) - G | 𝓕 s] ω := by
      intro k
      filter_upwards [hrec (T k) (hT k), condExp_sub (m := 𝓕 s) (hFi k) hG] with ω h1 h2
      simp only [hb, h1, Pi.add_apply, h2, Pi.sub_apply]
      ring
    have hbi : Integrable b μ :=
      (integrable_condExp.add integrable_condExp).congr (hbk 0).symm
    have hle : ∀ k, ∫ ω, |b ω| ∂μ ≤
        ∫ ω, |μ[Y (T k) | 𝓕 s] ω| ∂μ + ∫ ω, |F (T k) ω - G ω| ∂μ := by
      intro k
      have h1 := integral_abs_condExp_le (μ := μ) (m := 𝓕 s) (F (T k) - G)
      have h2 : ∫ ω, |b ω| ∂μ ≤
          ∫ ω, (|μ[Y (T k) | 𝓕 s] ω| + |μ[F (T k) - G | 𝓕 s] ω|) ∂μ := by
        refine integral_mono_ae hbi.abs
          (integrable_condExp.abs.add integrable_condExp.abs) ?_
        filter_upwards [hbk k] with ω hω
        rw [hω]
        exact abs_add_le _ _
      rw [integral_add integrable_condExp.abs integrable_condExp.abs] at h2
      have h1' : ∫ ω, |(F (T k) - G) ω| ∂μ = ∫ ω, |F (T k) ω - G ω| ∂μ := rfl
      linarith
    have hlim0 := htvc.add hL
    rw [add_zero] at hlim0
    have hb0 : ∫ ω, |b ω| ∂μ = 0 :=
      le_antisymm (ge_of_tendsto hlim0 (Eventually.of_forall hle))
        (integral_nonneg fun _ => abs_nonneg _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg (b ω)) hbi.abs).1 hb0
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply, abs_eq_zero, hb] at hω
    linarith

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: the printed `E_s∫_s^∞` form iff
conditional `L¹` convergence of the flows.** Under the hypotheses of `valuation_iff_L1_char`
but with the transversality condition almost surely, `E_s[Y_{T_k}] → 0` a.s.:
`Y_s = E_s[G]` a.s. **iff** `E_s[|F_{T_k} − G|] → 0` a.s.
The direction "⇐" needs neither the lower bound nor the a.s. limit.
Generalises the dominated case `TidyR7MonetarismValuation.valuation_iff_tvc_dom`. -/
theorem valuation_iff_condL1_char [IsFiniteMeasure μ] {Y F : ℝ → Ω → ℝ} {s : ℝ}
    (hrec : ∀ T, s ≤ T → Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[F T | 𝓕 s]) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) (hFi : ∀ k, Integrable (F (T k)) μ) {G h : Ω → ℝ}
    (hG : Integrable G μ) (hh : Integrable h μ) (hlow : ∀ k, ∀ᵐ ω ∂μ, -h ω ≤ F (T k) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => F (T k) ω) atTop (𝓝 (G ω)))
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[Y (T k) | 𝓕 s] ω) atTop (𝓝 0)) :
    Y s =ᵐ[μ] μ[G | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => |F (T k) ω - G ω| | 𝓕 s] ω) atTop (𝓝 0) := by
  have hlf := (valuation_iff_tvc_seq hrec hT).2 htvc
  constructor
  · intro hval
    have hce : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[F (T k) + h | 𝓕 s] ω) atTop
        (𝓝 (μ[G + h | 𝓕 s] ω)) := by
      have a1 : ∀ᵐ ω ∂μ, ∀ k, μ[F (T k) + h | 𝓕 s] ω = μ[F (T k) | 𝓕 s] ω + μ[h | 𝓕 s] ω :=
        ae_all_iff.2 fun k => by
          filter_upwards [condExp_add (hFi k) hh (𝓕 s)] with ω e
          rw [e, Pi.add_apply]
      filter_upwards [a1, condExp_add hG hh (𝓕 s), hlf, hval] with ω e1 e2 e3 e4
      simp_rw [e1]
      rw [e2, Pi.add_apply, ← e4]
      exact e3.add_const _
    have hS := ae_tendsto_condExp_abs_sub_of_nonneg (𝓕.le s) (μ := μ)
      (f := fun k => F (T k) + h) (g := G + h) (fun k => (hFi k).add hh) (hG.add hh)
      (fun k => by
        filter_upwards [hlow k] with ω hω
        simp only [Pi.add_apply]
        linarith)
      (by
        filter_upwards [hlim] with ω hω
        exact hω.add_const (h ω)) hce
    have e : ∀ k, (fun ω => |(F (T k) + h) ω - (G + h) ω|) = fun ω => |F (T k) ω - G ω| :=
      fun k => funext fun ω => by simp only [Pi.add_apply, add_sub_add_right_eq_sub]
    simp_rw [e] at hS
    exact hS
  · intro hc
    have h3 : ∀ᵐ ω ∂μ, ∀ k, |μ[F (T k) - G | 𝓕 s] ω| ≤
        μ[fun ω => |F (T k) ω - G ω| | 𝓕 s] ω :=
      ae_all_iff.2 fun k => by
        filter_upwards [abs_condExp_ae_le_condExp_abs (m := 𝓕 s) (μ := μ) (F (T k) - G)]
          with ω hω
        exact hω
    have h4 : ∀ᵐ ω ∂μ, ∀ k, μ[F (T k) - G | 𝓕 s] ω = μ[F (T k) | 𝓕 s] ω - μ[G | 𝓕 s] ω :=
      ae_all_iff.2 fun k => by
        filter_upwards [condExp_sub (m := 𝓕 s) (hFi k) hG] with ω hω
        rw [hω, Pi.sub_apply]
    filter_upwards [hc, hlf, h3, h4] with ω e1 e2 e3 e4
    have hconv : Tendsto (fun k => μ[F (T k) | 𝓕 s] ω) atTop (𝓝 (μ[G | 𝓕 s] ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) e1
      rw [Real.norm_eq_abs, ← e4 k]
      exact e3 k
    exact tendsto_nhds_unique e2 hconv

/-! ## In the economy: (1.33) and (1.34) -/

namespace MonetaryModel

variable {Λ P B M A N i im sp : ℝ → Ω → ℝ}

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the printed form of (1.33) holds iff the flows
converge in `L¹`.** With `i^m = 0`, the domination conditions of the product step on every
`[s, T]`, `n_TB_T` integrable, `F_{T_k} = ∫_s^{T_k} Λs dr + ∫_s^{T_k} n dM → G` a.s. with
`F_{T_k} ≥ −h` (`h` integrable), and the transversality condition in `L¹`:
`n_sB_s = E_s[G]` a.s. iff `∫|F_{T_k} − G| → 0`.
An instance of `valuation_iff_L1_char`.
Its "⇐" direction restates `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33`. -/
theorem valuation_1_33_char_L1 [IsFiniteMeasure μ] (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp)
    (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G h : Ω → ℝ} (hG : Integrable G μ) (hh : Integrable h μ)
    (hlow : ∀ k, ∀ᵐ ω ∂μ, -h ω ≤ flow133 Λ P M sp s (T k) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => flow133 Λ P M sp s (T k) ω) atTop (𝓝 (G ω)))
    (htvc : Tendsto (fun k => ∫ ω, |μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun k => ∫ ω, |flow133 Λ P M sp s (T k) ω - G ω| ∂μ) atTop (𝓝 0) :=
  valuation_iff_L1_char (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s)
    (fun T' hT' => (MonetaryModel.rec_1_33 hm him hT' (hd T' hT') (hYi s le_rfl)
      (hYi T' hT')).2) hT
    (fun k => (MonetaryModel.rec_1_33 hm him (hT k) (hd _ (hT k)) (hYi s le_rfl)
      (hYi _ (hT k))).1) hG hh hlow hlim htvc

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the printed form of (1.33) holds iff the flows
converge conditionally in `L¹`.** As `valuation_1_33_char_L1` with the almost-sure
transversality condition: `n_sB_s = E_s[G]` a.s. iff `E_s|F_{T_k} − G| → 0` a.s.
An instance of `valuation_iff_condL1_char`.
Generalises `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_dom` and
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_book`. -/
theorem valuation_1_33_char_cond [IsFiniteMeasure μ]
    (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp) (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G h : Ω → ℝ} (hG : Integrable G μ) (hh : Integrable h μ)
    (hlow : ∀ k, ∀ᵐ ω ∂μ, -h ω ≤ flow133 Λ P M sp s (T k) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => flow133 Λ P M sp s (T k) ω) atTop (𝓝 (G ω)))
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω)
      atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => |flow133 Λ P M sp s (T k) ω - G ω| | 𝓕 s] ω)
        atTop (𝓝 0) :=
  valuation_iff_condL1_char (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s)
    (fun T' hT' => (MonetaryModel.rec_1_33 hm him hT' (hd T' hT') (hYi s le_rfl)
      (hYi T' hT')).2) hT
    (fun k => (MonetaryModel.rec_1_33 hm him (hT k) (hd _ (hT k)) (hYi s le_rfl)
      (hYi _ (hT k))).1) hG hh hlow hlim htvc

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the finite-horizon budgets of (1.34),
`n_s(B + M)_s = E_s[n_T(B + M)_T] + E_s∫_s^T (Λs + (i − i^m)nM) dr` for every `T ≥ s` (as in
the proof of `TidyR7MonetarismValuation.MonetaryModel.valuation_1_34_book`). -/
theorem rec_1_34_char [IsFiniteMeasure μ] (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp) {s : ℝ}
    (hd : ∀ s t, s ≤ t → Dominated μ A N s t (addProc B M) (disc Λ P))
    (hYi : ∀ T, Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) :
    ∀ T', s ≤ T' → (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ]
      μ[fun ω => disc Λ P T' ω * addProc B M T' ω | 𝓕 s] +
        μ[flow134 Λ P M i im sp s T' | 𝓕 s] := fun T' hT' =>
  rec_of_incr (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (F := flow134 Λ P M i im sp s T') (hm.incr_1_34 hT' (hd s T' hT'))
    ((hm.disc_adapted s).mul (hm.W_adapted s)) (hYi s) (hYi T')

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the printed form of (1.34) holds iff the flows
converge in `L¹`.** With the domination conditions for `B + M`, `n_T(B + M)_T` integrable,
`F_{T_k} = ∫_s^{T_k} (Λs + (i − i^m)nM) dr → G` a.s. with `F_{T_k} ≥ −h`, and the
transversality condition in `L¹`: `n_s(B_s + M_s) = E_s[G]` a.s. iff `∫|F_{T_k} − G| → 0`.
An instance of `valuation_iff_L1_char`; its "⇐" direction restates
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_34`. -/
theorem valuation_1_34_char_L1 [IsFiniteMeasure μ] (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp)
    {s : ℝ} (hd : ∀ s t, s ≤ t → Dominated μ A N s t (addProc B M) (disc Λ P))
    (hYi : ∀ T, Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G h : Ω → ℝ} (hG : Integrable G μ) (hh : Integrable h μ)
    (hlow : ∀ k, ∀ᵐ ω ∂μ, -h ω ≤ flow134 Λ P M i im sp s (T k) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => flow134 Λ P M i im sp s (T k) ω) atTop (𝓝 (G ω)))
    (htvc : Tendsto (fun k => ∫ ω, |μ[fun ω => disc Λ P (T k) ω * addProc B M (T k) ω | 𝓕 s] ω|
      ∂μ) atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun k => ∫ ω, |flow134 Λ P M i im sp s (T k) ω - G ω| ∂μ) atTop (𝓝 0) :=
  valuation_iff_L1_char (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (F := flow134 Λ P M i im sp s) (rec_1_34_char hm hd hYi) hT
    (fun k => MonetaryModel.integrable_flow134 hm hd s (T k)) hG hh hlow hlim htvc

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the printed form of (1.34) holds iff the flows
converge conditionally in `L¹`** (almost-sure transversality condition).
An instance of `valuation_iff_condL1_char`; generalises
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_34_book`. -/
theorem valuation_1_34_char_cond [IsFiniteMeasure μ]
    (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp) {s : ℝ}
    (hd : ∀ s t, s ≤ t → Dominated μ A N s t (addProc B M) (disc Λ P))
    (hYi : ∀ T, Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G h : Ω → ℝ} (hG : Integrable G μ) (hh : Integrable h μ)
    (hlow : ∀ k, ∀ᵐ ω ∂μ, -h ω ≤ flow134 Λ P M i im sp s (T k) ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => flow134 Λ P M i im sp s (T k) ω) atTop (𝓝 (G ω)))
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * addProc B M (T k) ω |
      𝓕 s] ω) atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => |flow134 Λ P M i im sp s (T k) ω - G ω| | 𝓕 s] ω)
        atTop (𝓝 0) :=
  valuation_iff_condL1_char (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (F := flow134 Λ P M i im sp s) (rec_1_34_char hm hd hYi) hT
    (fun k => MonetaryModel.integrable_flow134 hm hd s (T k)) hG hh hlow hlim htvc

end MonetaryModel

/-! ## Instances -/

open Cochrane.Monetarism.TidyR7MonetarismUI Cochrane.Monetarism.TidyR7MonetarismCoinInf
  Cochrane.Monetarism.TidyR7MonetarismCoin Cochrane.Monetarism.TidyR7ProductStepCoin

/-- Cochrane (2023), A1 §1.6, p. 567: the times `T_k = k + 1` satisfy `T_k ≥ 1`. -/
theorem one_le_succ_cast (k : ℕ) : (1 : ℝ) ≤ (k : ℝ) + 1 := by
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

/-- Cochrane (2023), A1 §1.6, p. 567: `T_k = k + 1 → ∞`. -/
theorem tendsto_succ_cast : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the counterexample of `TidyR7MonetarismUI` is a
case of the characterisation.** In `TidyR7MonetarismUI.uiModel` at `s = 0`, along
`T_k = k + 1`, the flows are nonnegative and converge path by path to `G = 0`, and the
transversality condition holds (in `L¹` and a.s.), so `valuation_1_33_char_L1` and
`valuation_1_33_char_cond` apply; the printed form fails (`ui_literal_fails`), hence the flows
converge neither in `L¹` nor conditionally in `L¹`, and they are not uniformly integrable. -/
theorem ui_char :
    ((fun ω => disc uiOne uiOne 0 ω * uiB 0 ω) =ᵐ[uiMeasure]
        uiMeasure[fun _ => (0 : ℝ) | uiFilt 0] ↔
        Tendsto (fun k : ℕ => ∫ ω, |flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω - 0|
          ∂uiMeasure) atTop (𝓝 0)) ∧
      ¬ Tendsto (fun k : ℕ => ∫ ω, |flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω - 0|
          ∂uiMeasure) atTop (𝓝 0) ∧
      (¬ ∀ᵐ ω ∂uiMeasure, Tendsto (fun k : ℕ => uiMeasure[fun ω =>
          |flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω - 0| | uiFilt 0] ω) atTop (𝓝 0)) ∧
      ¬ UnifIntegrable (fun k : ℕ => flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1)) 1
          uiMeasure := by
  have hYi : ∀ T : ℝ, 0 ≤ T → Integrable (fun ω => disc uiOne uiOne T ω * uiB T ω) uiMeasure :=
    fun T _ => by
      have e : (fun ω => disc uiOne uiOne T ω * uiB T ω) = uiB T :=
        funext fun ω => by rw [disc_ui, one_mul]
      rw [e]
      exact (ui_integrable T).2
  have hT : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) + 1 := fun k => by linarith [one_le_succ_cast k]
  have hlow : ∀ k : ℕ, ∀ᵐ ω ∂uiMeasure,
      -(fun _ => (0 : ℝ)) ω ≤ flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω :=
    fun k => ae_of_all _ fun ω => by simpa using ui_flow_nonneg (hT k) ω
  have hlim : ∀ᵐ ω ∂uiMeasure, Tendsto (fun k : ℕ =>
      flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω) atTop (𝓝 ((fun _ => (0 : ℝ)) ω)) :=
    ae_of_all _ fun ω => (ui_pathwise ω).comp tendsto_succ_cast
  have htvc0 : ∀ k : ℕ, uiMeasure[fun ω => disc uiOne uiOne ((k : ℝ) + 1) ω *
      uiB ((k : ℝ) + 1) ω | uiFilt 0] = fun _ => 0 := fun k => ui_tvc (one_le_succ_cast k)
  have hL := MonetaryModel.valuation_1_33_char_L1 uiModel (fun _ _ => rfl) (s := 0)
    (fun T hT => ui_dom hT) hYi (T := fun k : ℕ => (k : ℝ) + 1) hT (G := fun _ => 0)
    (h := fun _ => 0) (integrable_const _) (integrable_const _) hlow hlim
    (by simp_rw [htvc0]; simp)
  have hC := MonetaryModel.valuation_1_33_char_cond uiModel (fun _ _ => rfl) (s := 0)
    (fun T hT => ui_dom hT) hYi (T := fun k : ℕ => (k : ℝ) + 1) hT (G := fun _ => 0)
    (h := fun _ => 0) (integrable_const _) (integrable_const _) hlow hlim
    (ae_of_all _ fun ω => by simp_rw [htvc0]; exact tendsto_const_nhds)
  have hnL : ¬ Tendsto (fun k : ℕ => ∫ ω, |flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1) ω
      - 0| ∂uiMeasure) atTop (𝓝 0) := fun h => ui_literal_fails (hL.2 h)
  have hFi : ∀ k : ℕ, Integrable (flow133 uiOne uiOne uiZero uiSur 0 ((k : ℝ) + 1)) uiMeasure :=
    fun k => (MonetaryModel.rec_1_33 uiModel (fun _ _ => rfl) (hT k) (ui_dom (hT k))
      (hYi 0 le_rfl) (hYi _ (hT k))).1
  refine ⟨hL, hnL, fun h => ui_literal_fails (hC.2 h), fun hui => hnL ?_⟩
  exact (tendsto_integral_abs_iff_unifIntegrable (g := fun _ => (0 : ℝ)) hFi
    (integrable_const _) hlim).2 hui

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: a positive instance of the characterisation.**
In `TidyR7MonetarismCoinInf.infModel` (news in `Λ/P`, positive nominal rate) at `s = 0`, along
`T_k = k + 1`, the flows are bounded below by `−5`, converge to `G = 2 + (ξ/4)e^{−1}` and the
transversality condition holds in `L¹`; `valuation_1_33_char_L1` applies, the flows converge in
`L¹`, so the printed form `n_0B_0 = E_0[G]` holds, and the flows are uniformly integrable. -/
theorem inf_char :
    ((fun ω => disc infLam coinP 0 ω * infB 0 ω) =ᵐ[coinMeasure]
        coinMeasure[infG | coinFiltration 0] ↔
        Tendsto (fun k : ℕ => ∫ ω, |flow133 infLam coinP zeroRate infSur 0 ((k : ℝ) + 1) ω -
          infG ω| ∂coinMeasure) atTop (𝓝 0)) ∧
      Tendsto (fun k : ℕ => ∫ ω, |flow133 infLam coinP zeroRate infSur 0 ((k : ℝ) + 1) ω -
          infG ω| ∂coinMeasure) atTop (𝓝 0) ∧
      (fun ω => disc infLam coinP 0 ω * infB 0 ω) =ᵐ[coinMeasure]
        coinMeasure[infG | coinFiltration 0] ∧
      UnifIntegrable (fun k : ℕ => flow133 infLam coinP zeroRate infSur 0 ((k : ℝ) + 1)) 1
        coinMeasure := by
  have hT : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) + 1 := fun k => by linarith [one_le_succ_cast k]
  have hlow : ∀ k : ℕ, ∀ᵐ ω ∂coinMeasure,
      -(fun _ => (5 : ℝ)) ω ≤ flow133 infLam coinP zeroRate infSur 0 ((k : ℝ) + 1) ω :=
    fun k => ae_of_all _ fun ω => (abs_le.1 (abs_inf_flow133_le (one_le_succ_cast k) ω)).1
  have hlim : ∀ᵐ ω ∂coinMeasure, Tendsto (fun k : ℕ =>
      flow133 infLam coinP zeroRate infSur 0 ((k : ℝ) + 1) ω) atTop (𝓝 (infG ω)) :=
    ae_of_all _ fun ω => (inf_tendsto ω).comp tendsto_succ_cast
  have htvc : Tendsto (fun k : ℕ => ∫ ω, |coinMeasure[fun ω => disc infLam coinP ((k : ℝ) + 1) ω
      * infB ((k : ℝ) + 1) ω | coinFiltration 0] ω| ∂coinMeasure) atTop (𝓝 0) := by
    have e : ∀ k : ℕ, ∫ ω, |coinMeasure[fun ω => disc infLam coinP ((k : ℝ) + 1) ω
        * infB ((k : ℝ) + 1) ω | coinFiltration 0] ω| ∂coinMeasure =
        (1 + Real.exp (-((k : ℝ) + 1))) * Real.exp (-((k : ℝ) + 1)) := fun k => by
      rw [inf_tvc_eq (one_le_succ_cast k), integral_coin]
      rw [abs_of_nonneg (by positivity)]
      ring
    simp_rw [e]
    exact tendsto_tvc_inf.comp tendsto_succ_cast
  have hL := MonetaryModel.valuation_1_33_char_L1 infModel (fun _ _ => rfl) (s := 0)
    (fun T _ => infDom 0 T) (fun _ _ => Integrable.of_finite) (T := fun k : ℕ => (k : ℝ) + 1)
    hT (G := infG) (h := fun _ => 5) Integrable.of_finite (integrable_const _) hlow hlim htvc
  have hconv : Tendsto (fun k : ℕ => ∫ ω, |flow133 infLam coinP zeroRate infSur 0 ((k : ℝ) + 1) ω
      - infG ω| ∂coinMeasure) atTop (𝓝 0) := inf_1_33.1.comp tendsto_succ_cast
  refine ⟨hL, hconv, hL.2 hconv, ?_⟩
  exact (tendsto_integral_abs_iff_unifIntegrable (fun _ => Integrable.of_finite)
    Integrable.of_finite hlim).1 hconv

/-! ## The lower bound cannot be dropped -/

/-- Cochrane (2023), A1 §1.6, p. 567 (counterexample): the signed flow
`Z_j(ω) = 2^{ω+1}(1{ω = j} − 1{ω = j + 1})` on `Ω = ℕ` with `P(ω) = 2^{−(ω+1)}`. -/
noncomputable def sgnZ (j ω : ℕ) : ℝ :=
  wt ω * ((if ω = j then 1 else 0) - (if ω = j + 1 then 1 else 0))

/-- Cochrane (2023), A1 §1.6, p. 567 (counterexample): the flows `F_T = Z_{⌊T⌋}` for `T ≥ 1`,
`0` before. -/
noncomputable def sgnF (T : ℝ) (ω : ℕ) : ℝ := if T < 1 then 0 else sgnZ ⌊T⌋₊ ω

/-- Cochrane (2023), A1 §1.6, p. 567 (counterexample): the discounted debt `Y_T = −F_T`. -/
noncomputable def sgnY (T : ℝ) (ω : ℕ) : ℝ := -sgnF T ω

/-- Cochrane (2023), A1 §1.6, p. 567: `F_{k+1} = Z_{k+1}`. -/
theorem sgnF_succ (k : ℕ) : sgnF ((k : ℝ) + 1) = sgnZ (k + 1) := by
  funext ω
  have h1 : ¬ ((k : ℝ) + 1 < 1) := not_lt.2 (one_le_succ_cast k)
  have h2 : ⌊(k : ℝ) + 1⌋₊ = k + 1 := by
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  simp only [sgnF, h1, ↓reduceIte, h2]

/-- Cochrane (2023), A1 §1.6, p. 567: `|Z_j(ω)| = 2^{ω+1}(1{ω = j} + 1{ω = j + 1})`. -/
theorem abs_sgnZ (j ω : ℕ) :
    |sgnZ j ω| = wt ω * ((if ω = j then 1 else 0) + (if ω = j + 1 then 1 else 0)) := by
  have hw : 0 < wt ω := by unfold wt; positivity
  by_cases h1 : ω = j
  · subst h1
    simp [sgnZ, abs_of_pos hw]
  · by_cases h2 : ω = j + 1
    · subst h2
      simp [sgnZ, abs_of_pos hw]
    · simp [sgnZ, h1, h2]

/-- Cochrane (2023), A1 §1.6, p. 567: `Z_j` is integrable (`|Z_j| ≤ 2^{j+1} + 2^{j+2}`). -/
theorem integrable_sgnZ (j : ℕ) : Integrable (sgnZ j) uiMeasure := by
  refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (wt j + wt (j + 1))
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_sgnZ]
  have h0 : 0 < wt j := by unfold wt; positivity
  have h0' : 0 < wt (j + 1) := by unfold wt; positivity
  by_cases h1 : ω = j
  · subst h1
    have h2 : ¬ (ω = ω + 1) := by omega
    simp only [h2, ↓reduceIte]
    linarith
  · by_cases h2 : ω = j + 1
    · subst h2
      have h3 : ¬ (j + 1 = j) := by omega
      simp only [h3, ↓reduceIte]
      linarith
    · simp only [h1, h2, ↓reduceIte, add_zero, mul_zero]
      linarith

/-- Cochrane (2023), A1 §1.6, p. 567: `E[Z_j] = 1 − 1 = 0`. -/
theorem integral_sgnZ (j : ℕ) : ∫ ω, sgnZ j ω ∂uiMeasure = 0 := by
  have e : (fun ω => sgnZ j ω) = fun ω : ℕ => (2 : ℝ) ^ (ω + 1) *
      ((if ω = j then 1 else 0) - (if ω = j + 1 then 1 else 0)) := funext fun ω => rfl
  rw [e, integral_ui_wt]
  have h := (hasSum_ite_eq j (1 : ℝ)).sub (hasSum_ite_eq (j + 1) (1 : ℝ))
  rw [h.tsum_eq, sub_self]

/-- Cochrane (2023), A1 §1.6, p. 567: `E|Z_j| = 1 + 1 = 2`. -/
theorem integral_abs_sgnZ (j : ℕ) : ∫ ω, |sgnZ j ω - 0| ∂uiMeasure = 2 := by
  have e : (fun ω => |sgnZ j ω - 0|) = fun ω : ℕ => (2 : ℝ) ^ (ω + 1) *
      ((if ω = j then 1 else 0) + (if ω = j + 1 then 1 else 0)) :=
    funext fun ω => by rw [sub_zero, abs_sgnZ]; rfl
  rw [e, integral_ui_wt]
  have h := (hasSum_ite_eq j (1 : ℝ)).add (hasSum_ite_eq (j + 1) (1 : ℝ))
  rw [h.tsum_eq]
  norm_num

/-- Cochrane (2023), A1 §1.6, p. 567: the finite-horizon budgets hold:
`Y_0 = 0 = E_0[Y_T] + E_0[F_T]` for every `T ≥ 0` (`E_0` is the expectation). -/
theorem sgn_rec : ∀ T : ℝ, 0 ≤ T →
    sgnY 0 =ᵐ[uiMeasure] uiMeasure[sgnY T | uiFilt 0] + uiMeasure[sgnF T | uiFilt 0] := by
  intro T _
  rw [condExp_ui_zero, condExp_ui_zero]
  refine ae_of_all _ fun ω => ?_
  simp only [Pi.add_apply, sgnY, integral_neg, neg_add_cancel]
  simp [sgnF]

/-- Cochrane (2023), A1 §1.6, p. 567: `F_{k+1}(ω) → 0` for every `ω` (`Z_j(ω) = 0` for
`j > ω`). -/
theorem sgn_pathwise (ω : ℕ) :
    Tendsto (fun k : ℕ => sgnF ((k : ℝ) + 1) ω) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ω] with k hk
  have h1 : ω ≠ k + 1 := by omega
  have h2 : ω ≠ k + 1 + 1 := by omega
  rw [sgnF_succ]
  simp [sgnZ, h1, h2]

/-- Cochrane (2023), A1 §1.6, p. 567: `E_0[Y_{k+1}] = −E[Z_{k+1}] = 0`. -/
theorem sgn_tvc (k : ℕ) : uiMeasure[sgnY ((k : ℝ) + 1) | uiFilt 0] = fun _ => 0 := by
  rw [condExp_ui_zero]
  funext _
  simp only [sgnY, integral_neg, sgnF_succ, integral_sgnZ, neg_zero]

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: without the lower bound, the printed form does
not imply `L¹` convergence.** For the signed flows `F_T` and `Y = −F` at `s = 0` along
`T_k = k + 1`: the finite-horizon budgets hold, the transversality condition holds (`E_0[Y_{T_k}]
= 0`), the flows converge path by path to `G = 0`, the printed form `Y_0 = 0 = E_0[G]` holds, but
`E|F_{T_k} − G| = 2` for every `k`: no `L¹` and (`𝓕_0` trivial) no conditional `L¹`
convergence. -/
theorem sgn_headline :
    (∀ T : ℝ, 0 ≤ T →
      sgnY 0 =ᵐ[uiMeasure] uiMeasure[sgnY T | uiFilt 0] + uiMeasure[sgnF T | uiFilt 0]) ∧
      (∀ k : ℕ, uiMeasure[sgnY ((k : ℝ) + 1) | uiFilt 0] = fun _ => 0) ∧
      (∀ ω, Tendsto (fun k : ℕ => sgnF ((k : ℝ) + 1) ω) atTop (𝓝 0)) ∧
      sgnY 0 =ᵐ[uiMeasure] uiMeasure[fun _ => (0 : ℝ) | uiFilt 0] ∧
      (∀ k : ℕ, ∫ ω, |sgnF ((k : ℝ) + 1) ω - 0| ∂uiMeasure = 2) ∧
      ¬ Tendsto (fun k : ℕ => ∫ ω, |sgnF ((k : ℝ) + 1) ω - 0| ∂uiMeasure) atTop (𝓝 0) ∧
      ¬ ∀ᵐ ω ∂uiMeasure, Tendsto (fun k : ℕ => uiMeasure[fun ω => |sgnF ((k : ℝ) + 1) ω - 0| |
        uiFilt 0] ω) atTop (𝓝 0) := by
  have h2 : ∀ k : ℕ, ∫ ω, |sgnF ((k : ℝ) + 1) ω - 0| ∂uiMeasure = 2 := fun k => by
    rw [sgnF_succ, integral_abs_sgnZ]
  have hnL : ¬ Tendsto (fun k : ℕ => ∫ ω, |sgnF ((k : ℝ) + 1) ω - 0| ∂uiMeasure) atTop
      (𝓝 0) := by
    intro h
    simp_rw [h2] at h
    exact two_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)
  refine ⟨sgn_rec, sgn_tvc, sgn_pathwise, ?_, h2, hnL, ?_⟩
  · rw [condExp_ui_zero]
    refine ae_of_all _ fun ω => ?_
    simp [sgnY, sgnF]
  · intro h
    obtain ⟨ω, hω⟩ := h.exists
    simp_rw [condExp_ui_zero, h2] at hω
    exact two_ne_zero (tendsto_nhds_unique tendsto_const_nhds hω)

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the lower bound in `valuation_iff_L1_char` is
necessary for "printed ⇒ `L¹`".** For the signed flows of `sgn_headline` no integrable `h`
satisfies `F_{T_k} ≥ −h` a.s. for all `k`: otherwise `valuation_iff_L1_char` would turn the
printed form into `L¹` convergence, which fails. -/
theorem sgn_no_lower_bound : ¬ ∃ h : ℕ → ℝ, Integrable h uiMeasure ∧
    ∀ k : ℕ, ∀ᵐ ω ∂uiMeasure, -h ω ≤ sgnF ((k : ℝ) + 1) ω := by
  rintro ⟨h, hh, hlow⟩
  obtain ⟨hrec, htvc, hpath, hval, -, hnL, -⟩ := sgn_headline
  have hT : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) + 1 := fun k => by linarith [one_le_succ_cast k]
  have hc := valuation_iff_L1_char (𝓕 := uiFilt) (Y := sgnY) (F := sgnF) (s := 0) hrec
    (T := fun k : ℕ => (k : ℝ) + 1) hT (fun k => by rw [sgnF_succ]; exact integrable_sgnZ _)
    (G := fun _ => 0) (integrable_const _) hh hlow (ae_of_all _ hpath)
    (by simp_rw [htvc]; simp)
  exact hnL (hc.1 hval)

end Cochrane.Monetarism.TidyR8MonetarismUISharp
