/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7CondDominated
import ZeroBound.TidyR7StieltjesCalculus
import Mathlib.Probability.Martingale.Basic

/-!
# The product step of (1.32) in expectation form, without a stochastic integral

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The middle step of (1.32) is
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`. It is proved here in integrated, expectation form,
with no stochastic integral: only conditional expectations, the pathwise Riemann–Stieltjes
calculus of `TidyR7StieltjesSums`/`TidyR7StieltjesCalculus`, and conditional dominated convergence
(`TidyR7CondDominated.ae_tendsto_condExp_of_dominated`).

## Setting (`ProductStepData`)

A finite measure `μ` on `Ω`, a filtration `𝓕` indexed by `ℝ` (as TidyR6StochasticDrift.HasDrift
and as the càdlàg notion `IsCadlag` on `ℝ` of `TidyR7StieltjesSums`; a filtration is only a
monotone family of sub-σ-algebras, so `ℝ` loses nothing against `ℝ≥0` and avoids coercions), times
`s ≤ t`, processes `B, A, M : ℝ → Ω → ℝ`, and `X = A + M` (`X` plays `Λ/P`, `B` plays bonds):
* `B` adapted on `[s, t]`, with paths continuous and of bounded variation on `[s, t]`;
* `A` measurable at each time of `[s, t]` (not necessarily adapted), càdlàg, of bounded variation
  on `[s, t]`;
* `M` a càdlàg martingale (Mathlib `MeasureTheory.Martingale`); `M`, hence `X`, need NOT have
  bounded variation;
* domination: `sup_{[s,t]}|X|·Var_{[s,t]}(B)` and `sup_{[s,t]}|B|·Var_{[s,t]}(A)` integrable
  (the suprema are the measurable `TidyR7CondDominated.pathSup`), and `B_u(M_v − M_u)` integrable
  for `s ≤ u ≤ v ≤ t` (it holds when `B` is bounded, `integrable_mul_incr_of_bound`).

## Main results

* `pathwise_identity`: for every partition of `[s, t]`, path by path,
  `B_tX_t − B_sX_s = Σ X_iΔB_i + Σ B_iΔA_i + Σ B_iΔM_i + Σ ΔX_iΔB_i`.
* `ProductStepData.condExp_mart_incr_zero`, `ProductStepData.condExp_sumBM_zero`:
  `E_s[B_uΔM] = 0` for `s ≤ u ≤ v ≤ t`, so `E_s[Σ B_iΔM_i] = Σ E_s[B_iΔM_i] = 0` exactly, at every
  partition (`ProductStepData.sum_condExp_mart_zero`).
* `ProductStepData.discrete_identity` (item 1): `E_s[B_tX_t − B_sX_s] = E_s[Σ X_iΔB_i] +
  E_s[Σ B_iΔA_i] + E_s[Σ ΔX_iΔB_i]` a.s. for every partition;
  `ProductStepData.condExp_sumBX_eq`: `E_s[Σ B_iΔX_i] = E_s[Σ B_iΔA_i]`.
* `ProductStepData.tendsto_condExp_sumXB`, `ProductStepData.tendsto_condExp_sumBA`,
  `ProductStepData.tendsto_condExp_cross`, `ProductStepData.tendsto_condExp_sumBX` (item 2): along
  ANY sequence of partitions with mesh `→ 0`, a.s.,
  `E_s[Σ X_iΔB_i] → E_s[∫X dB]`, `E_s[Σ B_iΔA_i] → E_s[∫B dA]`, `E_s[Σ ΔX_iΔB_i] → 0`,
  `E_s[Σ B_iΔX_i] → E_s[∫B dA]`; `ProductStepData.tendsto_condExp_dyadic` is the dyadic
  corollary.
* `ProductStepData.product_step` (item 3, the headline):
  `E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB] + E_s[∫_s^t B dA]`
  a.s. `ExpIncrLimit`: the expected-increment reading `B·E_s dX := lim E_s[Σ B_iΔX_i]`;
  `expIncrLimit_condExp_rsInt` (it exists and equals `E_s[∫B dA]`),
  `ExpIncrLimit.ae_eq` (it is unique), `product_step_expIncr`:
  `E_s[B_tX_t − B_sX_s] = E_s[∫X dB] + B·E_s dX`.
* `product_step_1_32`: the book's notation, `X = Λ/P`:
  `E_s[Λ_tB_t/P_t − Λ_sB_s/P_s] = E_s[∫_s^t (Λ/P) dB] + B·E_s d(Λ/P)` with
  `B·E_s d(Λ/P) = E_s[∫_s^t B dA]`.

## Where continuity of `B` is used (item 6)

Continuity of the paths of `B` on `[s, t]` is used in exactly three pathwise limits:
(i) the cross sum `Σ ΔX_iΔB_i → 0` (`TidyR7StieltjesSums.tendsto_crossSum_zero`, which fails
when `B` and `X` share a jump: `TidyR7StieltjesSums.not_tendsto_crossSum_heaviside`); this is
the step where a quadratic covariation `[X, B]` would otherwise appear in `E_s d(XB)`;
(ii) the left-point sums of the càdlàg `X` against `B` converge
(`TidyR7StieltjesSums.tendsto_rsSum_of_isCadlag`, case (b)); (iii) the left-point sums of `B`
against the jumping `A` converge (`TidyR7StieltjesSums.tendsto_rsSum_of_continuousOn`, case (a)).
The martingale step `E_s[Σ B_iΔM_i] = 0` uses only adaptedness of `B` and integrability.
-/

namespace Cochrane.ZeroBound.TidyR7ProductStep

open MeasureTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesIntegral Cochrane.ZeroBound.TidyR7StieltjesSums
  Cochrane.ZeroBound.TidyR7StieltjesCalculus Cochrane.ZeroBound.TidyR7CondDominated

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): the real variation
`Var_{[s,t]}(Y(ω, ·))` of a path.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.pathVar). -/
noncomputable def pathVar (s t : ℝ) (Y : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  (eVariationOn (fun u => Y u ω) (Set.Icc s t)).toReal

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the left-point sum `Σ Y_{t_i}(Z_{t_{i+1}} − Z_{t_i})`
of two processes along a partition, as a random variable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.sumRS). -/
def sumRS {s t : ℝ} (P : Partition s t) (Y Z : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  rsSum P (fun u => Y u ω) (fun u => Z u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the cross sum `Σ ΔY_iΔZ_i` of two processes along a
partition, as a random variable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.sumCross). -/
def sumCross {s t : ℝ} (P : Partition s t) (Y Z : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  crossSum P (fun u => Y u ω) (fun u => Z u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the pathwise integral `∫_s^t Y dZ`
(`TidyR7StieltjesIntegral.rsInt`), as a random variable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.intRS). -/
noncomputable def intRS (s t : ℝ) (Y Z : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  rsInt s t (fun u => Y u ω) (fun u => Z u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the sum of two processes, `X = A + M` (the
finite-variation part `A` and the martingale part `M` of `X = Λ/P`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.addProc). -/
def addProc (A M : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ := A u ω + M u ω

variable (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (s t : ℝ) (B A M : ℝ → Ω → ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the setting of the product step.** Times
`s ≤ t`; `B` adapted on `[s, t]` with continuous bounded-variation paths on `[s, t]`; `A`
measurable on `[s, t]`, càdlàg, of bounded variation on `[s, t]`; `M` a càdlàg martingale; the
domination and integrability conditions for conditional dominated convergence.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData). -/
structure ProductStepData where
  le : s ≤ t
  B_adapted : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u)
  B_cont : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t)
  B_bv : ∀ ω, BoundedVariationOn (fun u => B u ω) (Set.Icc s t)
  A_meas : ∀ u ∈ Set.Icc s t, Measurable (A u)
  A_cadlag : ∀ ω, IsCadlag fun u => A u ω
  A_bv : ∀ ω, BoundedVariationOn (fun u => A u ω) (Set.Icc s t)
  M_mart : Martingale M 𝓕 μ
  M_cadlag : ∀ ω, IsCadlag fun u => M u ω
  int_XB : Integrable (fun ω => pathSup s t (addProc A M) ω * pathVar s t B ω) μ
  int_BA : Integrable (fun ω => pathSup s t B ω * pathVar s t A ω) μ
  int_BM : ∀ u v, s ≤ u → u ≤ v → v ≤ t → Integrable (fun ω => B u ω * (M v ω - M u ω)) μ

variable {μ 𝓕 s t B A M}

/-! ## The pathwise identity -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the left-point sum is additive in the integrator,
`Σ B_iΔ(A + M)_i = Σ B_iΔA_i + Σ B_iΔM_i`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.sumRS_add_right). -/
theorem sumRS_add_right (P : Partition s t) (Y A M : ℝ → Ω → ℝ) (ω : Ω) :
    sumRS P Y (addProc A M) ω = sumRS P Y A ω + sumRS P Y M ω := by
  simp only [sumRS, rsSum, addProc, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the exact pathwise partition identity.** For
every partition of `[s, t]` and every `ω`,
`B_tX_t − B_sX_s = Σ X_iΔB_i + Σ B_iΔA_i + Σ B_iΔM_i + Σ ΔX_iΔB_i`, `X = A + M`.
Restates `TidyR7StieltjesCalculus.prod_partition_identity` with `X = A + M` split.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.pathwise_identity). -/
theorem pathwise_identity (P : Partition s t) (B A M : ℝ → Ω → ℝ) (ω : Ω) :
    B t ω * addProc A M t ω - B s ω * addProc A M s ω =
      sumRS P (addProc A M) B ω + sumRS P B A ω + sumRS P B M ω +
        sumCross P (addProc A M) B ω := by
  have h := prod_partition_identity P (fun u => addProc A M u ω) (fun u => B u ω)
  have e := sumRS_add_right P B A M ω
  simp only [sumRS, sumCross] at e ⊢
  linear_combination h + e

/-! ## Measurability, domination, integrability -/

/-- Cochrane (2023), A1 §1.6, p. 567: a left-point sum of processes measurable on `[s, t]` is
measurable.
Restates `TidyR7StieltjesCalculus.measurable_rsSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.measurable_sumRS). -/
theorem measurable_sumRS {Y Z : ℝ → Ω → ℝ} (hY : ∀ u ∈ Set.Icc s t, Measurable (Y u))
    (hZ : ∀ u ∈ Set.Icc s t, Measurable (Z u)) (P : Partition s t) :
    Measurable (sumRS P Y Z) := by
  change Measurable fun ω => ∑ i ∈ Finset.range P.n,
    Y (P.t i) ω * (Z (P.t (i + 1)) ω - Z (P.t i) ω)
  exact Finset.measurable_sum _ fun i hi =>
    (hY _ (t_mem P (Finset.mem_range.1 hi).le)).mul
      ((hZ _ (t_mem P (Finset.mem_range.1 hi))).sub (hZ _ (t_mem P (Finset.mem_range.1 hi).le)))

/-- Cochrane (2023), A1 §1.6, p. 567: a cross sum of processes measurable on `[s, t]` is
measurable.
Restates `TidyR7StieltjesCalculus.measurable_crossSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.measurable_sumCross). -/
theorem measurable_sumCross {Y Z : ℝ → Ω → ℝ} (hY : ∀ u ∈ Set.Icc s t, Measurable (Y u))
    (hZ : ∀ u ∈ Set.Icc s t, Measurable (Z u)) (P : Partition s t) :
    Measurable (sumCross P Y Z) := by
  change Measurable fun ω => ∑ i ∈ Finset.range P.n,
    (Y (P.t (i + 1)) ω - Y (P.t i) ω) * (Z (P.t (i + 1)) ω - Z (P.t i) ω)
  exact Finset.measurable_sum _ fun i hi =>
    ((hY _ (t_mem P (Finset.mem_range.1 hi))).sub (hY _ (t_mem P (Finset.mem_range.1 hi).le))).mul
      ((hZ _ (t_mem P (Finset.mem_range.1 hi))).sub (hZ _ (t_mem P (Finset.mem_range.1 hi).le)))

namespace ProductStepData

variable (hd : ProductStepData μ 𝓕 s t B A M)
include hd

/-- Cochrane (2023), A1 §1.6, p. 567: `B_u` is measurable for `u ∈ [s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.measurable_B). -/
theorem measurable_B : ∀ u ∈ Set.Icc s t, Measurable (B u) := fun u hu =>
  ((hd.B_adapted u hu).mono (𝓕.le u)).measurable

/-- Cochrane (2023), A1 §1.6, p. 567: `M_u` is measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.measurable_M). -/
theorem measurable_M : ∀ u, Measurable (M u) := fun u =>
  ((hd.M_mart.1 u).mono (𝓕.le u)).measurable

/-- Cochrane (2023), A1 §1.6, p. 567: `X_u = A_u + M_u` is measurable for `u ∈ [s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.measurable_X). -/
theorem measurable_X : ∀ u ∈ Set.Icc s t, Measurable (addProc A M u) := fun u hu =>
  (hd.A_meas u hu).add (hd.measurable_M u)

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `X = A + M` are càdlàg.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.X_cadlag). -/
theorem X_cadlag (ω : Ω) : IsCadlag fun u => addProc A M u ω :=
  (hd.A_cadlag ω).fun_add (hd.M_cadlag ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `|Σ X_iΔB_i| ≤ sup|X|·Var(B)` for every partition.
Restates `TidyR7StieltjesCalculus.abs_rsSum_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.abs_sumXB_le). -/
theorem abs_sumXB_le (P : Partition s t) (ω : Ω) :
    |sumRS P (addProc A M) B ω| ≤ pathSup s t (addProc A M) ω * pathVar s t B ω :=
  abs_rsSum_le (hd.B_bv ω) (fun _ hx => abs_le_pathSup_of_isCadlag (hd.X_cadlag ω) hx) P

/-- Cochrane (2023), A1 §1.6, p. 567: `|Σ B_iΔA_i| ≤ sup|B|·Var(A)` for every partition.
Restates `TidyR7StieltjesCalculus.abs_rsSum_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.abs_sumBA_le). -/
theorem abs_sumBA_le (P : Partition s t) (ω : Ω) :
    |sumRS P B A ω| ≤ pathSup s t B ω * pathVar s t A ω :=
  abs_rsSum_le (hd.A_bv ω) (fun _ hx => abs_le_pathSup_of_continuousOn (hd.B_cont ω) hx) P

/-- Cochrane (2023), A1 §1.6, p. 567: `|Σ ΔX_iΔB_i| ≤ 2 sup|X|·Var(B)` for every partition.
Restates `TidyR7StieltjesCalculus.abs_crossSum_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.abs_sumCross_le). -/
theorem abs_sumCross_le (P : Partition s t) (ω : Ω) :
    |sumCross P (addProc A M) B ω| ≤ 2 * (pathSup s t (addProc A M) ω * pathVar s t B ω) := by
  rw [← mul_assoc]
  exact abs_crossSum_le (hd.B_bv ω) (fun _ hx => abs_le_pathSup_of_isCadlag (hd.X_cadlag ω) hx) P

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ X_iΔB_i` is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_sumXB). -/
theorem integrable_sumXB (P : Partition s t) : Integrable (sumRS P (addProc A M) B) μ :=
  hd.int_XB.mono' (measurable_sumRS hd.measurable_X hd.measurable_B P).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hd.abs_sumXB_le P ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ B_iΔA_i` is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_sumBA). -/
theorem integrable_sumBA (P : Partition s t) : Integrable (sumRS P B A) μ :=
  hd.int_BA.mono' (measurable_sumRS hd.measurable_B hd.A_meas P).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hd.abs_sumBA_le P ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ ΔX_iΔB_i` is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_sumCross). -/
theorem integrable_sumCross (P : Partition s t) : Integrable (sumCross P (addProc A M) B) μ :=
  (hd.int_XB.const_mul 2).mono'
    (measurable_sumCross hd.measurable_X hd.measurable_B P).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hd.abs_sumCross_le P ω)

/-- Cochrane (2023), A1 §1.6, p. 567: each term `B_{t_i}ΔM_i` of a partition is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_term). -/
theorem integrable_term (P : Partition s t) {i : ℕ} (hi : i < P.n) :
    Integrable (fun ω => B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω)) μ :=
  hd.int_BM _ _ (t_mem P hi.le).1 (P.strictMono (Nat.lt_succ_self i)).le (t_mem P hi).2

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ B_iΔM_i` is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_sumBM). -/
theorem integrable_sumBM (P : Partition s t) : Integrable (sumRS P B M) μ := by
  have e : sumRS P B M = fun ω => ∑ i ∈ Finset.range P.n,
      B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω) := rfl
  rw [e]
  exact integrable_finsetSum _ fun i hi => hd.integrable_term P (Finset.mem_range.1 hi)

/-- Cochrane (2023), A1 §1.6, p. 567: `B_tX_t − B_sX_s` is integrable (it is the sum of the four
integrable partition sums of `pathwise_identity`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_lhs). -/
theorem integrable_lhs :
    Integrable (fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω) μ := by
  obtain ⟨P, -⟩ := exists_partition_seq hd.le
  have e : (fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω) =
      sumRS (P 0) (addProc A M) B + sumRS (P 0) B A + sumRS (P 0) B M +
        sumCross (P 0) (addProc A M) B :=
    funext fun ω => pathwise_identity (P 0) B A M ω
  rw [e]
  exact ((hd.integrable_sumXB _).add (hd.integrable_sumBA _)).add (hd.integrable_sumBM _) |>.add
    (hd.integrable_sumCross _)

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_s^t X dB` is integrable (measurable as the limit of
measurable sums, dominated by `sup|X|·Var(B)`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_intXB). -/
theorem integrable_intXB : Integrable (intRS s t (addProc A M) B) μ := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  have hm : Measurable (intRS s t (addProc A M) B) :=
    measurable_of_tendsto_metrizable
      (fun k => measurable_sumRS hd.measurable_X hd.measurable_B (P k))
      (tendsto_pi_nhds.2 fun ω =>
        tendsto_rsSum_of_isCadlag (hd.X_cadlag ω) (hd.B_bv ω) (hd.B_cont ω) P hP)
  exact hd.int_XB.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    exact abs_rsInt_le hd.le (hd.B_bv ω)
      (fun _ hx => abs_le_pathSup_of_isCadlag (hd.X_cadlag ω) hx))

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_s^t B dA` is integrable (measurable as the limit of
measurable sums, dominated by `sup|B|·Var(A)`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.integrable_intBA). -/
theorem integrable_intBA : Integrable (intRS s t B A) μ := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  have hm : Measurable (intRS s t B A) :=
    measurable_of_tendsto_metrizable (fun k => measurable_sumRS hd.measurable_B hd.A_meas (P k))
      (tendsto_pi_nhds.2 fun ω => tendsto_rsSum_of_continuousOn (hd.B_cont ω) (hd.A_bv ω) P hP)
  exact hd.int_BA.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    exact abs_rsInt_le hd.le (hd.A_bv ω)
      (fun _ hx => abs_le_pathSup_of_continuousOn (hd.B_cont ω) hx))

/-! ## The martingale terms vanish in conditional expectation -/

variable [IsFiniteMeasure μ]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: a martingale increment weighted by an earlier
`B` has zero conditional expectation.** For `s ≤ u ≤ v ≤ t`, `E_s[B_u(M_v − M_u)] = 0` a.s.
(`E_s = E_s E_u`, `B_u` pulls out of `E_u`, and `E_u[M_v − M_u] = 0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.condExp_mart_incr_zero). -/
theorem condExp_mart_incr_zero {u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    μ[fun ω => B u ω * (M v ω - M u ω) | 𝓕 s] =ᵐ[μ] 0 := by
  have hu : u ∈ Set.Icc s t := ⟨hsu, huv.trans hvt⟩
  have hMi := hd.M_mart.integrable
  have h1 : μ[fun ω => B u ω * (M v ω - M u ω) | 𝓕 u] =ᵐ[μ] 0 := by
    have e := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 u) (f := B u) (g := M v - M u)
      (hd.B_adapted u hu) (hd.int_BM u v hsu huv hvt) ((hMi v).sub (hMi u))
    have e2 := condExp_sub (m := 𝓕 u) (hMi v) (hMi u)
    have e3 := hd.M_mart.2 u v huv
    have e4 : μ[M u | 𝓕 u] = M u :=
      condExp_of_stronglyMeasurable (𝓕.le u) (hd.M_mart.1 u) (hMi u)
    filter_upwards [e, e2, e3] with ω h1 h2 h3
    have h1' : μ[fun ω => B u ω * (M v ω - M u ω) | 𝓕 u] ω =
        B u ω * μ[M v - M u | 𝓕 u] ω := h1
    rw [h1', h2, Pi.sub_apply, h3, e4]
    simp
  calc μ[fun ω => B u ω * (M v ω - M u ω) | 𝓕 s]
      =ᵐ[μ] μ[μ[fun ω => B u ω * (M v ω - M u ω) | 𝓕 u] | 𝓕 s] :=
        (condExp_condExp_of_le (𝓕.mono hsu) (𝓕.le u)).symm
    _ =ᵐ[μ] μ[(0 : Ω → ℝ) | 𝓕 s] := condExp_congr_ae h1
    _ = 0 := condExp_zero

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `Σ E_s[B_iΔM_i] = 0` exactly**, at every
partition: every term vanishes a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.sum_condExp_mart_zero). -/
theorem sum_condExp_mart_zero (P : Partition s t) :
    ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range P.n,
      μ[fun ω => B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω) | 𝓕 s] ω = 0 := by
  have h : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range P.n,
      μ[fun ω => B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω) | 𝓕 s] ω = 0 :=
    (eventually_all_finset _).2 fun i hi => by
      have hi' := Finset.mem_range.1 hi
      filter_upwards [hd.condExp_mart_incr_zero (t_mem P hi'.le).1
        (P.strictMono (Nat.lt_succ_self i)).le (t_mem P hi').2] with ω hω
      exact hω
  filter_upwards [h] with ω hω
  exact Finset.sum_eq_zero hω

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔM_i] = 0`** a.s., at every
partition.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.condExp_sumBM_zero). -/
theorem condExp_sumBM_zero (P : Partition s t) : μ[sumRS P B M | 𝓕 s] =ᵐ[μ] 0 := by
  have e : sumRS P B M = ∑ i ∈ Finset.range P.n,
      fun ω => B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω) := by
    funext ω
    simp only [sumRS, rsSum, Finset.sum_apply]
  rw [e]
  filter_upwards [condExp_finsetSum (fun i hi => hd.integrable_term P (Finset.mem_range.1 hi))
    (𝓕 s), hd.sum_condExp_mart_zero P] with ω h1 h2
  rw [h1, Finset.sum_apply, h2]
  rfl

/-! ## Item 1: the exact discrete identity under `E_s` -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the exact discrete identity in conditional
expectation.** For every partition of `[s, t]`, a.s.,
`E_s[B_tX_t − B_sX_s] = E_s[Σ X_iΔB_i] + E_s[Σ B_iΔA_i] + E_s[Σ ΔX_iΔB_i]`; the martingale
sum `Σ B_iΔM_i` has dropped out because `E_s[Σ B_iΔM_i] = 0` (`condExp_sumBM_zero`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.discrete_identity). -/
theorem discrete_identity (P : Partition s t) :
    μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[sumRS P (addProc A M) B | 𝓕 s] + μ[sumRS P B A | 𝓕 s] +
        μ[sumCross P (addProc A M) B | 𝓕 s] := by
  have e : (fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω) =
      sumRS P (addProc A M) B + sumRS P B A + sumRS P B M + sumCross P (addProc A M) B := by
    funext ω
    exact pathwise_identity P B A M ω
  rw [e]
  have i1 := hd.integrable_sumXB P
  have i2 := hd.integrable_sumBA P
  have i3 := hd.integrable_sumBM P
  have i4 := hd.integrable_sumCross P
  filter_upwards [condExp_add ((i1.add i2).add i3) i4 (𝓕 s), condExp_add (i1.add i2) i3 (𝓕 s),
    condExp_add i1 i2 (𝓕 s), hd.condExp_sumBM_zero P] with ω h1 h2 h3 h4
  simp only [Pi.add_apply] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4]
  simp

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔX_i] = E_s[Σ B_iΔA_i]`** a.s. at
every partition: the martingale part of `X` contributes nothing to the expected increment.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.condExp_sumBX_eq). -/
theorem condExp_sumBX_eq (P : Partition s t) :
    μ[sumRS P B (addProc A M) | 𝓕 s] =ᵐ[μ] μ[sumRS P B A | 𝓕 s] := by
  have e : sumRS P B (addProc A M) = sumRS P B A + sumRS P B M :=
    funext fun ω => sumRS_add_right P B A M ω
  rw [e]
  filter_upwards [condExp_add (hd.integrable_sumBA P) (hd.integrable_sumBM P) (𝓕 s),
    hd.condExp_sumBM_zero P] with ω h1 h2
  rw [h1, Pi.add_apply, h2]
  simp

/-! ## Item 2: the limits along partitions with mesh → 0 -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ X_iΔB_i] → E_s[∫_s^t X dB]`** a.s., along
any sequence of partitions with mesh `→ 0` (pathwise case (b) limit, dominated by
`sup|X|·Var(B)`).
Uses `TidyR7StieltjesSums.tendsto_rsSum_of_isCadlag`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.tendsto_condExp_sumXB). -/
theorem tendsto_condExp_sumXB (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (P k) (addProc A M) B | 𝓕 s] ω) atTop
      (𝓝 (μ[intRS s t (addProc A M) B | 𝓕 s] ω)) :=
  ae_tendsto_condExp_of_dominated (𝓕.le s)
    (fun k => measurable_sumRS hd.measurable_X hd.measurable_B (P k)) hd.int_XB
    (fun k ω => hd.abs_sumXB_le (P k) ω)
    (fun ω => tendsto_rsSum_of_isCadlag (hd.X_cadlag ω) (hd.B_bv ω) (hd.B_cont ω) P hP)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔA_i] → E_s[∫_s^t B dA]`** a.s., along
any sequence of partitions with mesh `→ 0` (pathwise case (a) limit, dominated by
`sup|B|·Var(A)`).
Uses `TidyR7StieltjesSums.tendsto_rsSum_of_continuousOn`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.tendsto_condExp_sumBA). -/
theorem tendsto_condExp_sumBA (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (P k) B A | 𝓕 s] ω) atTop
      (𝓝 (μ[intRS s t B A | 𝓕 s] ω)) :=
  ae_tendsto_condExp_of_dominated (𝓕.le s)
    (fun k => measurable_sumRS hd.measurable_B hd.A_meas (P k)) hd.int_BA
    (fun k ω => hd.abs_sumBA_le (P k) ω)
    (fun ω => tendsto_rsSum_of_continuousOn (hd.B_cont ω) (hd.A_bv ω) P hP)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ ΔX_iΔB_i] → 0`** a.s., along any sequence
of partitions with mesh `→ 0` (pathwise: `TidyR7StieltjesSums.tendsto_crossSum_zero`, which uses
the continuity of `B`; dominated by `2 sup|X|·Var(B)`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.tendsto_condExp_cross). -/
theorem tendsto_condExp_cross (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumCross (P k) (addProc A M) B | 𝓕 s] ω) atTop (𝓝 0) := by
  have h := ae_tendsto_condExp_of_dominated (𝓕.le s) (μ := μ) (f := fun _ => (0 : ℝ))
    (fun k => measurable_sumCross hd.measurable_X hd.measurable_B (P k)) (hd.int_XB.const_mul 2)
    (fun k ω => hd.abs_sumCross_le (P k) ω)
    (fun ω => tendsto_crossSum_zero (hd.X_cadlag ω) (hd.B_bv ω) (hd.B_cont ω) P hP)
  have e : μ[(fun _ => (0 : ℝ)) | 𝓕 s] = 0 := condExp_zero
  rw [e] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔX_i] → E_s[∫_s^t B dA]`** a.s., along
any sequence of partitions with mesh `→ 0`: the martingale part of `X` contributes `0` at every
partition (`condExp_sumBX_eq`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.tendsto_condExp_sumBX). -/
theorem tendsto_condExp_sumBX (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (P k) B (addProc A M) | 𝓕 s] ω) atTop
      (𝓝 (μ[intRS s t B A | 𝓕 s] ω)) := by
  have he : ∀ᵐ ω ∂μ, ∀ k, μ[sumRS (P k) B (addProc A M) | 𝓕 s] ω = μ[sumRS (P k) B A | 𝓕 s] ω :=
    ae_all_iff.2 fun k => hd.condExp_sumBX_eq (P k)
  filter_upwards [he, hd.tendsto_condExp_sumBA P hP] with ω h1 h2
  exact (tendsto_congr h1).2 h2

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the dyadic corollary**: for `s < t`, along the
dyadic partitions, a.s., `E_s[Σ X_iΔB_i] → E_s[∫X dB]`, `E_s[Σ B_iΔX_i] → E_s[∫B dA]` and
`E_s[Σ ΔX_iΔB_i] → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.tendsto_condExp_dyadic). -/
theorem tendsto_condExp_dyadic (hst : s < t) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (dyadic hst k) (addProc A M) B | 𝓕 s] ω) atTop
        (𝓝 (μ[intRS s t (addProc A M) B | 𝓕 s] ω)) ∧
      Tendsto (fun k => μ[sumRS (dyadic hst k) B (addProc A M) | 𝓕 s] ω) atTop
        (𝓝 (μ[intRS s t B A | 𝓕 s] ω)) ∧
      Tendsto (fun k => μ[sumCross (dyadic hst k) (addProc A M) B | 𝓕 s] ω) atTop (𝓝 0) := by
  filter_upwards [hd.tendsto_condExp_sumXB _ (tendsto_mesh_dyadic hst),
    hd.tendsto_condExp_sumBX _ (tendsto_mesh_dyadic hst),
    hd.tendsto_condExp_cross _ (tendsto_mesh_dyadic hst)] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-! ## Item 3: the headline -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the product step, in expectation form.**
Almost surely, `E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB] + E_s[∫_s^t B dA]`, `X = A + M`: the
increment of the product is the integral of `X` against `dB` plus the integral of `B` against
the expected increment of `X` (its finite-variation part `A`); no stochastic integral is used.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ProductStepData.product_step). -/
theorem product_step :
    μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[intRS s t (addProc A M) B | 𝓕 s] + μ[intRS s t B A | 𝓕 s] := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  have hid := ae_all_iff.2 fun k => hd.discrete_identity (P k)
  filter_upwards [hid, hd.tendsto_condExp_sumXB P hP, hd.tendsto_condExp_sumBA P hP,
    hd.tendsto_condExp_cross P hP] with ω h0 h1 h2 h3
  have hs := (h1.add h2).add h3
  rw [add_zero] at hs
  have hc : Tendsto (fun k => (μ[sumRS (P k) (addProc A M) B | 𝓕 s] +
      μ[sumRS (P k) B A | 𝓕 s] + μ[sumCross (P k) (addProc A M) B | 𝓕 s]) ω) atTop
      (𝓝 (μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] ω)) := by
    refine (tendsto_congr fun k => ?_).1 tendsto_const_nhds
    exact h0 k
  simp only [Pi.add_apply] at hc ⊢
  exact tendsto_nhds_unique hc hs

end ProductStepData

/-! ## The expected-increment reading `B·E_s dX` -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the expected-increment integral**
`B·E_s dX = L`: along every sequence of partitions of `[s, t]` with mesh `→ 0`,
`E_s[Σ B_iΔX_i] → L` almost surely.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ExpIncrLimit). -/
def ExpIncrLimit (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (s t : ℝ) (B X : ℝ → Ω → ℝ)
    (L : Ω → ℝ) : Prop :=
  ∀ P : ℕ → Partition s t, Tendsto (fun k => mesh (P k)) atTop (𝓝 0) →
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (P k) B X | 𝓕 s] ω) atTop (𝓝 (L ω))

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `B·E_s dX` is unique** (a.s.), for `s ≤ t`.
By Mathlib `tendsto_nhds_unique`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.ExpIncrLimit.ae_eq). -/
theorem ExpIncrLimit.ae_eq {X : ℝ → Ω → ℝ} {L L' : Ω → ℝ} (hst : s ≤ t)
    (h : ExpIncrLimit μ 𝓕 s t B X L) (h' : ExpIncrLimit μ 𝓕 s t B X L') : L =ᵐ[μ] L' := by
  obtain ⟨P, hP⟩ := exists_partition_seq hst
  filter_upwards [h P hP, h' P hP] with ω h1 h2
  exact tendsto_nhds_unique h1 h2

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `B·E_s dX` exists and equals `E_s[∫_s^t B dA]`**
(item 3).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.expIncrLimit_condExp_rsInt). -/
theorem expIncrLimit_condExp_rsInt [IsFiniteMeasure μ] (hd : ProductStepData μ 𝓕 s t B A M) :
    ExpIncrLimit μ 𝓕 s t B (addProc A M) (μ[intRS s t B A | 𝓕 s]) :=
  fun P hP => hd.tendsto_condExp_sumBX P hP

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the product step with the expected-increment
integral.** If `B·E_s dX = L` (`ExpIncrLimit`), then
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB] + L` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.product_step_expIncr). -/
theorem product_step_expIncr [IsFiniteMeasure μ] (hd : ProductStepData μ 𝓕 s t B A M)
    {L : Ω → ℝ} (hL : ExpIncrLimit μ 𝓕 s t B (addProc A M) L) :
    μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[intRS s t (addProc A M) B | 𝓕 s] + L := by
  filter_upwards [hd.product_step, (expIncrLimit_condExp_rsInt hd).ae_eq hd.le hL] with ω h1 h2
  rw [h1, Pi.add_apply, Pi.add_apply, h2]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, in the book's notation.** Let `X = Λ/P` have the
decomposition `Λ_u/P_u = A_u + M_u` (finite-variation part plus martingale) with the hypotheses of
`ProductStepData`. Then a.s.
`E_s[Λ_tB_t/P_t − Λ_sB_s/P_s] = E_s[∫_s^t (Λ/P) dB] + B·E_s d(Λ/P)`, where the expected-increment
integral `B·E_s d(Λ/P)` (`ExpIncrLimit`) exists and equals `E_s[∫_s^t B dA]`: integrated,
`Λ/P·dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.product_step_1_32). -/
theorem product_step_1_32 [IsFiniteMeasure μ] (hd : ProductStepData μ 𝓕 s t B A M)
    {Λ Pr : ℝ → Ω → ℝ} (hdec : ∀ u ω, Λ u ω / Pr u ω = A u ω + M u ω) :
    μ[fun ω => Λ t ω * B t ω / Pr t ω - Λ s ω * B s ω / Pr s ω | 𝓕 s] =ᵐ[μ]
        μ[intRS s t (fun u ω => Λ u ω / Pr u ω) B | 𝓕 s] + μ[intRS s t B A | 𝓕 s] ∧
      ExpIncrLimit μ 𝓕 s t B (fun u ω => Λ u ω / Pr u ω) (μ[intRS s t B A | 𝓕 s]) := by
  have eX : (fun u ω => Λ u ω / Pr u ω) = addProc A M := funext fun u => funext fun ω => hdec u ω
  have eL : (fun ω => Λ t ω * B t ω / Pr t ω - Λ s ω * B s ω / Pr s ω) =
      fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω := by
    funext ω
    simp only [addProc]
    rw [← hdec t ω, ← hdec s ω]
    ring
  rw [eX, eL]
  exact ⟨hd.product_step, expIncrLimit_condExp_rsInt hd⟩

/-- Cochrane (2023), A1 §1.6, p. 567: the integrability hypothesis `ProductStepData.int_BM` of
`ProductStepData` holds when `B` is bounded on `[s, t]` and measurable, `M` integrable.
An instance of Mathlib `Integrable.bdd_mul`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ProductStep.integrable_mul_incr_of_bound). -/
theorem integrable_mul_incr_of_bound {K : ℝ} (hK : ∀ u ∈ Set.Icc s t, ∀ ω, |B u ω| ≤ K)
    (hBm : ∀ u ∈ Set.Icc s t, Measurable (B u)) (hM : ∀ u, Integrable (M u) μ) :
    ∀ u v, s ≤ u → u ≤ v → v ≤ t → Integrable (fun ω => B u ω * (M v ω - M u ω)) μ := by
  intro u v hsu huv hvt
  have hu : u ∈ Set.Icc s t := ⟨hsu, huv.trans hvt⟩
  refine (((hM v).sub (hM u)).norm.const_mul K).mono'
    ((hBm u hu).aestronglyMeasurable.mul ((hM v).sub (hM u)).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, Pi.sub_apply]
  exact mul_le_mul_of_nonneg_right (hK u hu ω) (abs_nonneg _)

end Cochrane.ZeroBound.TidyR7ProductStep
