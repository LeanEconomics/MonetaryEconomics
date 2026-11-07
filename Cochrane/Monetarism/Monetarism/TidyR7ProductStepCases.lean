/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7ProductStep
import Monetarism.TidyR6StochasticDrift

/-!
# Special cases of the product step of (1.32)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Corollaries of the product step
`TidyR7ProductStep.ProductStepData.product_step`,
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB] + E_s[∫_s^t B dA]` (`X = A + M`).

## Main results

* `product_step_deterministic`: **deterministic bonds** `B_u = b(u)` (`b` continuous of bounded
  variation): the domination conditions reduce to integrability of `sup_{[s,t]}|X|` and of
  `Var_{[s,t]}(A)`.
* `product_step_fv`: **`X` of bounded variation** (`M = 0`): the headline, and its agreement with
  the conditional expectation of the pathwise integration by parts
  `TidyR7StieltjesCalculus.integration_by_parts_of_isCadlag`.
  `integration_by_parts_of_product_step`: conversely, the pathwise integration by parts (for `f`
  càdlàg of bounded variation, `g` continuous of bounded variation, `s ≤ t`) is RECOVERED from the
  headline on a one-point probability space with the constant filtration.
* `bv_of_hasDerivAt`, `rsInt_eq_integral_mul_deriv`: for a `C¹` integrator `g`,
  `∫_a^b f dg = ∫_a^b f g'` (Lebesgue), `f` continuous.
* `productStepData_C1`, `product_step_C1`: the **`C¹` case**: for `C¹` paths `n` (`X = n`, `M = 0`)
  and `B`, `E_s[B_tn_t − B_sn_s] = E_s∫_s^t nḂ + E_s∫_s^t Bṅ`, and `B·E_s dn = E_s∫_s^t Bṅ`.
* `product_step_1_32_C1`: with the hypotheses of `TidyR6StochasticDrift.drift_1_32_fv`
  (`ṅ = −in`, `Ḃ = iB − Ps − Ṁ`): `B·E_s d(Λ/P) = −E_s∫_s^t i(Λ/P)B` (the book's
  `E_t d(Λ/P) = −i(Λ/P)dt`) and `E_s[n_tB_t − n_sB_s] = −E_s∫_s^t n(Ps + Ṁ)`; `drift_1_32_link`:
  this gives exactly the martingale condition of `TidyR6StochasticDrift.HasDrift` that
  `TidyR6StochasticDrift.drift_1_32_fv` proves pathwise (which needs no integrability or
  adaptedness: in the `C¹` case the bracket vanishes identically).
-/

namespace Cochrane.Monetarism.TidyR7ProductStepCases

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7StieltjesCalculus Cochrane.Monetarism.TidyR7CondDominated
  Cochrane.Monetarism.TidyR7ProductStep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {s t : ℝ}

/-! ## Deterministic bonds -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, with deterministic bonds.** Let `B_u = b(u)`
with `b` continuous and of bounded variation on `[s, t]`, `A` measurable on `[s, t]`, càdlàg, of
bounded variation, `M` a càdlàg martingale, and `sup_{[s,t]}|A + M|`, `Var_{[s,t]}(A)` integrable.
Then `E_s[b_tX_t − b_sX_s] = E_s[∫_s^t X db] + E_s[∫_s^t b dA]` a.s. -/
theorem product_step_deterministic [IsFiniteMeasure μ] {b : ℝ → ℝ} {A M : ℝ → Ω → ℝ}
    (hst : s ≤ t) (hbc : ContinuousOn b (Set.Icc s t)) (hbv : BoundedVariationOn b (Set.Icc s t))
    (hAm : ∀ u ∈ Set.Icc s t, Measurable (A u)) (hAc : ∀ ω, IsCadlag fun u => A u ω)
    (hAv : ∀ ω, BoundedVariationOn (fun u => A u ω) (Set.Icc s t)) (hM : Martingale M 𝓕 μ)
    (hMc : ∀ ω, IsCadlag fun u => M u ω) (hXi : Integrable (pathSup s t (addProc A M)) μ)
    (hAi : Integrable (pathVar s t A) μ) :
    μ[fun ω => b t * addProc A M t ω - b s * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[intRS s t (addProc A M) (fun u _ => b u) | 𝓕 s] +
        μ[intRS s t (fun u _ => b u) A | 𝓕 s] := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hbc
  have hd : ProductStepData μ 𝓕 s t (fun u _ => b u) A M :=
    { le := hst
      B_adapted := fun _ _ => stronglyMeasurable_const
      B_cont := fun _ => hbc
      B_bv := fun _ => hbv
      A_meas := hAm
      A_cadlag := hAc
      A_bv := hAv
      M_mart := hM
      M_cadlag := hMc
      int_XB := hXi.mul_const _
      int_BA := hAi.const_mul _
      int_BM := integrable_mul_incr_of_bound (K := K)
        (fun u hu _ => by rw [← Real.norm_eq_abs]; exact hK u hu)
        (fun _ _ => measurable_const) hM.integrable }
  exact hd.product_step

/-! ## `X` of bounded variation (`M = 0`) -/

/-- Cochrane (2023), A1 §1.6, p. 567: `X = A + 0` is `A`. -/
theorem addProc_zero (A : ℝ → Ω → ℝ) : addProc A (fun _ _ => (0 : ℝ)) = A := by
  funext u ω
  simp [addProc]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, `X` of bounded variation.** With `M = 0`
(`X = A` càdlàg of bounded variation), the headline reads
`E_s[B_tA_t − B_sA_s] = E_s[∫_s^t A dB] + E_s[∫_s^t B dA]`, and for `s < t` this is the
conditional expectation of the pathwise integration by parts
`TidyR7StieltjesCalculus.integration_by_parts_of_isCadlag`. -/
theorem product_step_fv [IsFiniteMeasure μ] {B A : ℝ → Ω → ℝ}
    (hd : ProductStepData μ 𝓕 s t B A fun _ _ => 0) :
    μ[fun ω => B t ω * A t ω - B s ω * A s ω | 𝓕 s] =ᵐ[μ]
        μ[intRS s t A B | 𝓕 s] + μ[intRS s t B A | 𝓕 s] ∧
      (s < t → μ[fun ω => B t ω * A t ω - B s ω * A s ω | 𝓕 s] =
        μ[fun ω => intRS s t A B ω + intRS s t B A ω | 𝓕 s]) := by
  have h := hd.product_step
  rw [addProc_zero] at h
  refine ⟨h, fun hst => ?_⟩
  congr 1
  funext ω
  have := integration_by_parts_of_isCadlag hst (hd.A_cadlag ω) (hd.A_bv ω) (hd.B_cont ω)
    (hd.B_bv ω)
  simp only [intRS]
  linarith

/-- **Cochrane (2023), A1 §1.6, p. 567: pathwise integration by parts recovered from the product
step.** For `f` càdlàg of bounded variation on `[s, t]`, `g` continuous of bounded variation on
`[s, t]`, `s ≤ t`: `g(t)f(t) − g(s)f(s) = ∫_s^t f dg + ∫_s^t g df`. Proof: the headline on the
one-point space `Unit` with the Dirac measure and the constant filtration (`E_s` is then the
identity), `B = g`, `A = f`, `M = 0`. For `s < t` this is
`TidyR7StieltjesCalculus.integration_by_parts_of_isCadlag`; the case `s = t` is included. -/
theorem integration_by_parts_of_product_step {f g : ℝ → ℝ} (hst : s ≤ t) (hf : IsCadlag f)
    (hfv : BoundedVariationOn f (Set.Icc s t)) (hgc : ContinuousOn g (Set.Icc s t))
    (hgv : BoundedVariationOn g (Set.Icc s t)) :
    g t * f t - g s * f s = rsInt s t f g + rsInt s t g f := by
  let 𝓖 : Filtration ℝ (inferInstance : MeasurableSpace Unit) :=
    Filtration.const ℝ (inferInstance : MeasurableSpace Unit) le_rfl
  let ν : Measure Unit := Measure.dirac ()
  have hd : ProductStepData ν 𝓖 s t (fun u _ => g u) (fun u _ => f u) fun _ _ => 0 :=
    { le := hst
      B_adapted := fun _ _ => stronglyMeasurable_const
      B_cont := fun _ => hgc
      B_bv := fun _ => hgv
      A_meas := fun _ _ => measurable_const
      A_cadlag := fun _ => hf
      A_bv := fun _ => hfv
      M_mart := martingale_const 𝓖 ν 0
      M_cadlag := fun _ => IsCadlag.const
      int_XB := Integrable.of_finite
      int_BA := Integrable.of_finite
      int_BM := fun _ _ _ _ _ => Integrable.of_finite }
  have h := hd.product_step
  have e : ∀ F : Unit → ℝ, ν[F | 𝓖 s] = F := fun F =>
    condExp_of_stronglyMeasurable (𝓖.le s) StronglyMeasurable.of_subsingleton_dom
      Integrable.of_finite
  rw [e, e, e] at h
  obtain ⟨ω, hω⟩ := h.exists
  simp only [addProc, add_zero, Pi.add_apply, intRS] at hω
  exact hω

/-! ## The `C¹` case -/

/-- Cochrane (2023), A1 §1.6, p. 568: a `C¹` function (derivative continuous) has bounded
variation on every `[a, b]` (it is Lipschitz there, by the mean value theorem).
Compare Mathlib `LipschitzOnWith.comp_boundedVariationOn`. -/
theorem bv_of_hasDerivAt {a b : ℝ} {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Continuous g') : BoundedVariationOn g (Set.Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg'.continuousOn (s := Set.Icc a b))
  have hL : LipschitzOnWith C.toNNReal g (Set.Icc a b) :=
    Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc a b)
      (fun x _ => (hg x).hasDerivWithinAt) fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
        exact (hC x hx).trans (le_max_left _ _)
  exact hL.comp_boundedVariationOn (Set.mapsTo_id _) (BoundedVariationOn.id_Icc a b)

/-- **Cochrane (2023), A1 §1.6, p. 568: the Stieltjes integral against a `C¹` integrator.** For
`f` continuous on `[a, b]` and `g` with continuous derivative `g'`,
`∫_a^b f dg = ∫_a^b f(x)g'(x) dx`. Proof: each left-point sum is
`Σ ∫_{t_i}^{t_{i+1}} f(t_i)g'`, within `ε·sup|g'|·(b − a)` of `∫_a^b f g'` when `f` oscillates by
`≤ ε` over the mesh; the sums also converge to `∫ f dg`. -/
theorem rsInt_eq_integral_mul_deriv {a b : ℝ} {f g g' : ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    rsInt a b f g = ∫ x in a..b, f x * g' x := by
  rcases hab.lt_or_eq with hlt | rfl
  swap
  · rw [TidyR7StieltjesVariation.rsInt_self, intervalIntegral.integral_same]
  have hbv := bv_of_hasDerivAt (a := a) (b := b) hg hg'
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg'.continuousOn (s := Set.Icc a b))
  set G' := max G 0 with hG'def
  have hG' : ∀ x ∈ Set.Icc a b, |g' x| ≤ G' := fun x hx =>
    (by rw [← Real.norm_eq_abs]; exact hG x hx : |g' x| ≤ G).trans (le_max_left _ _)
  have hG0 : 0 ≤ G' := le_max_right _ _
  have hest : ∀ (P : Partition a b) (ε : ℝ), 0 ≤ ε →
      (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |x - y| ≤ mesh P → |f x - f y| ≤ ε) →
      |rsSum P f g - ∫ x in a..b, f x * g' x| ≤ ε * G' * (b - a) := by
    intro P ε hε hfε
    have hsub : ∀ i < P.n, Set.Icc (P.t i) (P.t (i + 1)) ⊆ Set.Icc a b := fun i hi =>
      Set.Icc_subset_Icc (t_mem P hi.le).1 (t_mem P hi).2
    have hlt : ∀ i, P.t i < P.t (i + 1) := fun i => P.strictMono (Nat.lt_succ_self i)
    have hint : ∀ i < P.n, IntervalIntegrable (fun x => f x * g' x) MeasureSpace.volume
        (P.t i) (P.t (i + 1)) := fun i hi =>
      ((hf.mono (hsub i hi)).mul hg'.continuousOn).intervalIntegrable_of_Icc (hlt i).le
    have e1 : rsSum P f g =
        ∑ i ∈ Finset.range P.n, ∫ x in P.t i..P.t (i + 1), f (P.t i) * g' x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x)
          (hg'.intervalIntegrable _ _)]
    have e2 : ∫ x in a..b, f x * g' x =
        ∑ i ∈ Finset.range P.n, ∫ x in P.t i..P.t (i + 1), f x * g' x := by
      rw [intervalIntegral.sum_integral_adjacent_intervals hint, P.first, P.last]
    rw [e1, e2, ← Finset.sum_sub_distrib]
    calc |∑ i ∈ Finset.range P.n, ((∫ x in P.t i..P.t (i + 1), f (P.t i) * g' x) -
          ∫ x in P.t i..P.t (i + 1), f x * g' x)|
        ≤ ∑ i ∈ Finset.range P.n, |(∫ x in P.t i..P.t (i + 1), f (P.t i) * g' x) -
          ∫ x in P.t i..P.t (i + 1), f x * g' x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range P.n, ε * G' * (P.t (i + 1) - P.t i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          rw [← intervalIntegral.integral_sub ((hg'.intervalIntegrable _ _).const_mul _)
            (hint i hi')]
          have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := P.t i)
            (b := P.t (i + 1)) (C := ε * G')
            (f := fun x => f (P.t i) * g' x - f x * g' x) fun x hx => by
              rw [Set.uIoc_of_le (hlt i).le] at hx
              have hx' : x ∈ Set.Icc a b := hsub i hi' ⟨hx.1.le, hx.2⟩
              rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
              have hm := le_mesh P hi'
              have h1 : |f (P.t i) - f x| ≤ ε := hfε _ (t_mem P hi'.le) _ hx' (by
                rw [abs_sub_comm, abs_of_nonneg (by linarith [hx.1])]
                linarith [hx.2])
              exact mul_le_mul h1 (hG' x hx') (abs_nonneg _) hε
          rw [Real.norm_eq_abs, abs_of_pos (sub_pos.2 (hlt i))] at hb
          exact hb
      _ = ε * G' * (b - a) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => P.t i), P.last, P.first]
  have hlim : Tendsto (fun k => rsSum (dyadic hlt k) f g) atTop
      (𝓝 (∫ x in a..b, f x * g' x)) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    have hden : 0 < G' * (b - a) + 1 := by nlinarith [mul_nonneg hG0 (sub_pos.2 hlt).le]
    set ε := η / (G' * (b - a) + 1) with hεdef
    have hε : 0 < ε := div_pos hη hden
    obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_mesh_dyadic hlt) δ hδ
    refine ⟨N, fun k hk => ?_⟩
    have hmk : mesh (dyadic hlt k) < δ := by
      have := hN k hk
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hest _ ε hε.le fun x hx y hy hxy =>
      (hδf x hx y hy (by rw [Real.dist_eq]; linarith)).le) ?_
    have : ε * (G' * (b - a)) < η := by
      rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    linarith [mul_assoc ε G' (b - a)]
  exact tendsto_nhds_unique (tendsto_rsSum_dyadic_of_continuousOn hlt hf hbv) hlim

/-- Cochrane (2023), A1 §1.6, p. 568: a path with a derivative everywhere is continuous.
From Mathlib `HasDerivAt.continuousAt`. -/
theorem continuous_of_hasDerivAt {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) :
    Continuous g :=
  continuous_iff_continuousAt.2 fun x => (hg x).continuousAt

/-- Cochrane (2023), A1 §1.6, (1.32), p. 568: **the data of the product step for `C¹` paths**
`n` (`X = n`, `A = n`, `M = 0`) and `B`: `B` adapted on `[s, t]`, `n` measurable on `[s, t]`, and
`sup|n|·Var(B)`, `sup|B|·Var(n)` integrable. -/
theorem productStepData_C1 {n n' B B' : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hn : ∀ ω r, HasDerivAt (fun u => n u ω) (n' r ω) r) (hn' : ∀ ω, Continuous fun r => n' r ω)
    (hB : ∀ ω r, HasDerivAt (fun u => B u ω) (B' r ω) r) (hB' : ∀ ω, Continuous fun r => B' r ω)
    (hBad : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u))
    (hnm : ∀ u ∈ Set.Icc s t, Measurable (n u))
    (hi1 : Integrable (fun ω => pathSup s t n ω * pathVar s t B ω) μ)
    (hi2 : Integrable (fun ω => pathSup s t B ω * pathVar s t n ω) μ) [IsFiniteMeasure μ] :
    ProductStepData μ 𝓕 s t B n fun _ _ => 0 where
  le := hst
  B_adapted := hBad
  B_cont := fun ω => (continuous_of_hasDerivAt (hB ω)).continuousOn
  B_bv := fun ω => bv_of_hasDerivAt (hB ω) (hB' ω)
  A_meas := hnm
  A_cadlag := fun ω => (continuous_of_hasDerivAt (hn ω)).isCadlag
  A_bv := fun ω => bv_of_hasDerivAt (hn ω) (hn' ω)
  M_mart := martingale_const 𝓕 μ 0
  M_cadlag := fun _ => IsCadlag.const
  int_XB := by rw [addProc_zero]; exact hi1
  int_BA := hi2
  int_BM := fun _ _ _ _ _ => by simp only [sub_self, mul_zero]; exact integrable_zero _ _ _

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 568, the `C¹` case.** For `C¹` paths `n` and `B` as in
`productStepData_C1`: a.s.
`E_s[B_tn_t − B_sn_s] = E_s[∫_s^t n Ḃ] + E_s[∫_s^t B ṅ]`, and the expected-increment integral
`B·E_s dn` (`TidyR7ProductStep.ExpIncrLimit`) is `E_s[∫_s^t B ṅ]`. -/
theorem product_step_C1 [IsFiniteMeasure μ] {n n' B B' : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hn : ∀ ω r, HasDerivAt (fun u => n u ω) (n' r ω) r) (hn' : ∀ ω, Continuous fun r => n' r ω)
    (hB : ∀ ω r, HasDerivAt (fun u => B u ω) (B' r ω) r) (hB' : ∀ ω, Continuous fun r => B' r ω)
    (hBad : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u))
    (hnm : ∀ u ∈ Set.Icc s t, Measurable (n u))
    (hi1 : Integrable (fun ω => pathSup s t n ω * pathVar s t B ω) μ)
    (hi2 : Integrable (fun ω => pathSup s t B ω * pathVar s t n ω) μ) :
    μ[fun ω => B t ω * n t ω - B s ω * n s ω | 𝓕 s] =ᵐ[μ]
        μ[fun ω => ∫ r in s..t, n r ω * B' r ω | 𝓕 s] +
          μ[fun ω => ∫ r in s..t, B r ω * n' r ω | 𝓕 s] ∧
      ExpIncrLimit μ 𝓕 s t B n (μ[fun ω => ∫ r in s..t, B r ω * n' r ω | 𝓕 s]) := by
  have hd := productStepData_C1 hst hn hn' hB hB' hBad hnm hi1 hi2 (μ := μ) (𝓕 := 𝓕)
  have e1 : intRS s t n B = fun ω => ∫ r in s..t, n r ω * B' r ω := funext fun ω =>
    rsInt_eq_integral_mul_deriv hst (continuous_of_hasDerivAt (hn ω)).continuousOn (hB ω) (hB' ω)
  have e2 : intRS s t B n = fun ω => ∫ r in s..t, B r ω * n' r ω := funext fun ω =>
    rsInt_eq_integral_mul_deriv hst (continuous_of_hasDerivAt (hB ω)).continuousOn (hn ω) (hn' ω)
  have h := hd.product_step
  have hL := expIncrLimit_condExp_rsInt hd
  rw [addProc_zero, e1, e2] at h
  rw [addProc_zero, e2] at hL
  exact ⟨h, hL⟩

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, the `C¹` case in the book's form.** Let
`n = Λ/P` and `B` have `C¹` paths with `ṅ = −in` (the nominal rate as the expected rate of decline
of `Λ/P`) and the flow (1.31) with `i^m = 0`, `Ḃ = iB − Ps − Ṁ`, all derivatives continuous, `B`
adapted, `n` measurable, with the domination of `productStepData_C1`. Then a.s.
(i) `B·E_s d(Λ/P) = −E_s∫_s^t i(Λ/P)B` (`E_t d(Λ/P) = −i(Λ/P) dt`), and
(ii) `E_s[n_tB_t − n_sB_s] = −E_s∫_s^t n(Ps + Ṁ)`, the integrated
`E_t d(ΛB/P) = −Λ(s + Ṁ/P) dt`. -/
theorem product_step_1_32_C1 [IsFiniteMeasure μ] {n B Pr sp i dM : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hn : ∀ ω r, HasDerivAt (fun u => n u ω) (-(i r ω * n r ω)) r)
    (hB : ∀ ω r, HasDerivAt (fun u => B u ω) (i r ω * B r ω - Pr r ω * sp r ω - dM r ω) r)
    (hic : ∀ ω, Continuous fun r => i r ω)
    (hfc : ∀ ω, Continuous fun r => Pr r ω * sp r ω + dM r ω)
    (hBad : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u))
    (hnm : ∀ u ∈ Set.Icc s t, Measurable (n u))
    (hi1 : Integrable (fun ω => pathSup s t n ω * pathVar s t B ω) μ)
    (hi2 : Integrable (fun ω => pathSup s t B ω * pathVar s t n ω) μ) :
    ExpIncrLimit μ 𝓕 s t B n (μ[fun ω => -∫ r in s..t, i r ω * n r ω * B r ω | 𝓕 s]) ∧
      μ[fun ω => n t ω * B t ω - n s ω * B s ω | 𝓕 s] =ᵐ[μ]
        μ[fun ω => ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω)) | 𝓕 s] := by
  have hnc : ∀ ω, Continuous fun r => n r ω := fun ω => continuous_of_hasDerivAt (hn ω)
  have hBc : ∀ ω, Continuous fun r => B r ω := fun ω => continuous_of_hasDerivAt (hB ω)
  have hn' : ∀ ω, Continuous fun r => -(i r ω * n r ω) := fun ω => ((hic ω).mul (hnc ω)).neg
  have hB' : ∀ ω, Continuous fun r => i r ω * B r ω - Pr r ω * sp r ω - dM r ω := fun ω => by
    have h1 : Continuous fun r => i r ω * B r ω - (Pr r ω * sp r ω + dM r ω) :=
      ((hic ω).mul (hBc ω)).sub (hfc ω)
    exact h1.congr fun r => by ring
  obtain ⟨h, hL⟩ := product_step_C1 (μ := μ) (𝓕 := 𝓕) hst hn hn' hB hB' hBad hnm hi1 hi2
  have eI : ∀ ω, ∫ r in s..t, B r ω * -(i r ω * n r ω) = -∫ r in s..t, i r ω * n r ω * B r ω :=
    fun ω => by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun r _ => by ring
  simp only [eI] at hL
  refine ⟨hL, ?_⟩
  have hd := productStepData_C1 hst hn hn' hB hB' hBad hnm hi1 hi2 (μ := μ) (𝓕 := 𝓕)
  have e1 : intRS s t n B = fun ω => ∫ r in s..t, n r ω * (i r ω * B r ω - Pr r ω * sp r ω -
      dM r ω) := funext fun ω =>
    rsInt_eq_integral_mul_deriv hst (hnc ω).continuousOn (hB ω) (hB' ω)
  have e2 : intRS s t B n = fun ω => ∫ r in s..t, B r ω * -(i r ω * n r ω) := funext fun ω =>
    rsInt_eq_integral_mul_deriv hst (hBc ω).continuousOn (hn ω) (hn' ω)
  have i1 := hd.integrable_intXB
  have i2 := hd.integrable_intBA
  rw [addProc_zero, e1] at i1
  rw [e2] at i2
  have hsum : (fun ω => ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω))) =
      (fun ω => ∫ r in s..t, n r ω * (i r ω * B r ω - Pr r ω * sp r ω - dM r ω)) +
        fun ω => ∫ r in s..t, B r ω * -(i r ω * n r ω) := by
    funext ω
    have c1 : Continuous fun r => n r ω * (i r ω * B r ω - Pr r ω * sp r ω - dM r ω) :=
      (hnc ω).mul (hB' ω)
    have c2 : Continuous fun r => B r ω * -(i r ω * n r ω) := (hBc ω).mul (hn' ω)
    rw [Pi.add_apply, ← intervalIntegral.integral_add (c1.intervalIntegrable _ _)
      (c2.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun r _ => by ring
  have eL : (fun ω => n t ω * B t ω - n s ω * B s ω) =
      fun ω => B t ω * n t ω - B s ω * n s ω := funext fun ω => by ring
  rw [eL, hsum]
  filter_upwards [h, condExp_add i1 i2 (𝓕 s)] with ω h1 h2
  rw [h1, h2]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: link with `TidyR6StochasticDrift.drift_1_32_fv`.**
Under the hypotheses of `product_step_1_32_C1`, the product step gives
`E_s[n_tB_t − n_sB_s − ∫_s^t (−n(Ps + Ṁ))] = 0` a.s., which is the martingale condition
`TidyR6StochasticDrift.HasDrift.mart` of `TidyR6StochasticDrift.drift_1_32_fv` at `s ≤ t` (the
latter proves it pathwise, with no integrability or adaptedness); both proofs are returned. -/
theorem drift_1_32_link [IsFiniteMeasure μ] {n B Pr sp i dM : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hn : ∀ ω r, HasDerivAt (fun u => n u ω) (-(i r ω * n r ω)) r)
    (hB : ∀ ω r, HasDerivAt (fun u => B u ω) (i r ω * B r ω - Pr r ω * sp r ω - dM r ω) r)
    (hic : ∀ ω, Continuous fun r => i r ω)
    (hfc : ∀ ω, Continuous fun r => Pr r ω * sp r ω + dM r ω)
    (hc : ∀ ω, Continuous fun r => n r ω * (Pr r ω * sp r ω + dM r ω))
    (hBad : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u))
    (hnm : ∀ u ∈ Set.Icc s t, Measurable (n u))
    (hi1 : Integrable (fun ω => pathSup s t n ω * pathVar s t B ω) μ)
    (hi2 : Integrable (fun ω => pathSup s t B ω * pathVar s t n ω) μ) :
    μ[fun ω => n t ω * B t ω - n s ω * B s ω -
        ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω)) | 𝓕 s] =ᵐ[μ] 0 ∧
      μ[fun ω => n t ω * B t ω - n s ω * B s ω -
        ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω)) | 𝓕 s] =ᵐ[μ] 0 := by
  refine ⟨?_, (TidyR6StochasticDrift.drift_1_32_fv (μ := μ) (𝓕 := 𝓕) hn hB hc).mart s t hst⟩
  have h := (product_step_1_32_C1 (μ := μ) (𝓕 := 𝓕) hst hn hB hic hfc hBad hnm hi1 hi2).2
  have hd := productStepData_C1 (μ := μ) (𝓕 := 𝓕) hst hn
    (fun ω => ((hic ω).mul (continuous_of_hasDerivAt (hn ω))).neg) hB
    (fun ω => by
      have h1 : Continuous fun r => i r ω * B r ω - (Pr r ω * sp r ω + dM r ω) :=
        ((hic ω).mul (continuous_of_hasDerivAt (hB ω))).sub (hfc ω)
      exact h1.congr fun r => by ring) hBad hnm hi1 hi2
  have iL := hd.integrable_lhs
  rw [addProc_zero] at iL
  have iL' : Integrable (fun ω => n t ω * B t ω - n s ω * B s ω) μ := by
    refine iL.congr (Eventually.of_forall fun ω => ?_)
    simp only
    ring
  have iG : Integrable (fun ω => ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω))) μ := by
    refine (iL'.congr (Eventually.of_forall fun ω => ?_))
    have hcn : Continuous fun r => -(n r ω * (Pr r ω * sp r ω + dM r ω)) := (hc ω).neg
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => n u ω * B u ω)
      (f' := fun r => -(n r ω * (Pr r ω * sp r ω + dM r ω)))
      (a := s) (b := t) (fun r _ => ((hn ω r).mul (hB ω r)).congr_deriv (by ring))
      (hcn.intervalIntegrable _ _)
    exact this.symm
  filter_upwards [condExp_sub iL' iG (𝓕 s), h] with ω h1 h2
  have h1' : μ[fun ω => n t ω * B t ω - n s ω * B s ω -
      ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω)) | 𝓕 s] ω =
      μ[fun ω => n t ω * B t ω - n s ω * B s ω | 𝓕 s] ω -
        μ[fun ω => ∫ r in s..t, -(n r ω * (Pr r ω * sp r ω + dM r ω)) | 𝓕 s] ω := h1
  rw [h1', h2, sub_self]
  rfl

end Cochrane.Monetarism.TidyR7ProductStepCases
