/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7JumpSums
import Monetarism.TidyR7ProductStep

/-!
# The corrected product step of (1.32) for bonds with jumps

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The middle step of (1.32),
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`, was proved in `TidyR7ProductStep` for bonds `B` with
continuous paths (`TidyR7ProductStep.ProductStepData.product_step`). For bonds that may jump
TOGETHER with `X = Λ/P` the step needs a third term, the jump covariation.

## Setting (`JumpStepData`)

As `TidyR7ProductStep.ProductStepData`, except that the paths of `B` are only càdlàg (on `ℝ`;
a path given on `[s, t]` can be frozen outside it) of bounded variation on `[s, t]`:
`B` adapted on `[s, t]`; `A` measurable on `[s, t]`, càdlàg, of bounded variation on `[s, t]`;
`M` a càdlàg martingale; `X = A + M`; the same domination conditions.

## Main results

* `JumpStepData.jump_step` (the corrected theorem): almost surely
  `E_s[B_tX_t − B_sX_s] = E_s[∫_{(s,t]} X_− dB] + E_s[∫_{(s,t]} B_− dA] + E_s[Σ_{s<u≤t} ΔB_uΔX_u]`,
  with `∫ X_− dB = rsInt s t (leftLim X) B` (`intLeft`) and the absolutely convergent countable
  jump sum `TidyR7JumpSums.jumpSum` (`jumpCov`). As in I2, the martingale terms vanish exactly at
  every partition (`JumpStepData.condExp_sumBM_zero`); the new ingredients are the pathwise limits
  `TidyR7JumpSums.tendsto_rsSum_leftLim` and `TidyR7JumpSums.tendsto_crossSum_jumpSum`.
* `JumpStepData.jump_step_ls`: the same in two terms with the Lebesgue–Stieltjes integral of the
  CURRENT `X`: `E_s[B_tX_t − B_sX_s] = E_s[∫ X dB] + E_s[∫ B_− dA]` (`∫ X dB = ∫ X_− dB + Σ ΔXΔB`).
* `JumpStepData.expIncrLimit_intLeft`, `JumpStepData.jump_step_expIncr`, `jump_step_1_32`: the
  expected-increment reading `B·E_s dX = E_s[∫ B_− dA]` and the book's notation.
* `JumpStepData.ofProductStepData`, `JumpStepData.toProductStepData`,
  `JumpStepData.rhs_eq_of_continuousOn`, `JumpStepData.jump_step_recovers_product_step`: for `B`
  continuous the jump term is `0`, `X_−` and `B_−` may be replaced by `X` and `B`, and the
  corrected result is exactly I2's `TidyR7ProductStep.ProductStepData.product_step`.
-/

namespace Cochrane.Monetarism.TidyR7ProductStepJump

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7StieltjesCalculus Cochrane.Monetarism.TidyR7CondDominated
  Cochrane.Monetarism.TidyR7ProductStep Cochrane.Monetarism.TidyR7JumpSums

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the pathwise integral of the LEFT LIMITS,
`∫_{(s,t]} Y_− dZ` (`rsInt s t (leftLim Y) Z`), as a random variable. -/
noncomputable def intLeft (s t : ℝ) (Y Z : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  rsInt s t (Function.leftLim fun u => Y u ω) (fun u => Z u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the jump covariation `Σ_{s<u≤t} ΔY_uΔZ_u`
(`TidyR7JumpSums.jumpSum`), as a random variable. -/
noncomputable def jumpCov (s t : ℝ) (Y Z : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  jumpSum s t (fun u => Y u ω) (fun u => Z u ω)

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): a pointwise limit of measurable functions dominated
by an integrable function is integrable. -/
theorem integrable_of_tendsto {μ : Measure Ω} {F : ℕ → Ω → ℝ} {f D : Ω → ℝ}
    (hF : ∀ k, Measurable (F k)) (hD : Integrable D μ) (hbd : ∀ k ω, |F k ω| ≤ D ω)
    (hlim : ∀ ω, Tendsto (fun k => F k ω) atTop (𝓝 (f ω))) : Integrable f μ := by
  have hfm : Measurable f := measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 hlim)
  refine hD.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact le_of_tendsto' (hlim ω).abs fun k => hbd k ω

variable (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (s t : ℝ) (B A M : ℝ → Ω → ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the setting of the product step with jumping
bonds.** As `TidyR7ProductStep.ProductStepData`, but the paths of `B` are càdlàg (not
necessarily continuous) of bounded variation on `[s, t]`. -/
structure JumpStepData where
  le : s ≤ t
  B_adapted : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u)
  B_cadlag : ∀ ω, IsCadlag fun u => B u ω
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

namespace JumpStepData

variable (hd : JumpStepData μ 𝓕 s t B A M)
include hd

/-- Cochrane (2023), A1 §1.6, p. 567: `B_u` is measurable for `u ∈ [s, t]`.
Restates `TidyR7ProductStep.ProductStepData.measurable_B` for càdlàg bonds. -/
theorem measurable_B : ∀ u ∈ Set.Icc s t, Measurable (B u) := fun u hu =>
  ((hd.B_adapted u hu).mono (𝓕.le u)).measurable

/-- Cochrane (2023), A1 §1.6, p. 567: `M_u` is measurable.
Restates `TidyR7ProductStep.ProductStepData.measurable_M` for càdlàg bonds. -/
theorem measurable_M : ∀ u, Measurable (M u) := fun u =>
  ((hd.M_mart.1 u).mono (𝓕.le u)).measurable

/-- Cochrane (2023), A1 §1.6, p. 567: `X_u = A_u + M_u` is measurable for `u ∈ [s, t]`.
Restates `TidyR7ProductStep.ProductStepData.measurable_X` for càdlàg bonds. -/
theorem measurable_X : ∀ u ∈ Set.Icc s t, Measurable (addProc A M u) := fun u hu =>
  (hd.A_meas u hu).add (hd.measurable_M u)

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `X = A + M` are càdlàg.
Restates `TidyR7ProductStep.ProductStepData.X_cadlag` for càdlàg bonds. -/
theorem X_cadlag (ω : Ω) : IsCadlag fun u => addProc A M u ω :=
  (hd.A_cadlag ω).fun_add (hd.M_cadlag ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `|Σ X_iΔB_i| ≤ sup|X|·Var(B)` for every partition.
Restates `TidyR7ProductStep.ProductStepData.abs_sumXB_le` for càdlàg bonds. -/
theorem abs_sumXB_le (P : Partition s t) (ω : Ω) :
    |sumRS P (addProc A M) B ω| ≤ pathSup s t (addProc A M) ω * pathVar s t B ω :=
  abs_rsSum_le (hd.B_bv ω) (fun _ hx => abs_le_pathSup_of_isCadlag (hd.X_cadlag ω) hx) P

/-- Cochrane (2023), A1 §1.6, p. 567: `|Σ B_iΔA_i| ≤ sup|B|·Var(A)` for every partition (`B`
càdlàg).
Restates `TidyR7ProductStep.ProductStepData.abs_sumBA_le` for càdlàg bonds. -/
theorem abs_sumBA_le (P : Partition s t) (ω : Ω) :
    |sumRS P B A ω| ≤ pathSup s t B ω * pathVar s t A ω :=
  abs_rsSum_le (hd.A_bv ω) (fun _ hx => abs_le_pathSup_of_isCadlag (hd.B_cadlag ω) hx) P

/-- Cochrane (2023), A1 §1.6, p. 567: `|Σ ΔX_iΔB_i| ≤ 2 sup|X|·Var(B)` for every partition.
Restates `TidyR7ProductStep.ProductStepData.abs_sumCross_le` for càdlàg bonds. -/
theorem abs_sumCross_le (P : Partition s t) (ω : Ω) :
    |sumCross P (addProc A M) B ω| ≤ 2 * (pathSup s t (addProc A M) ω * pathVar s t B ω) := by
  rw [← mul_assoc]
  exact abs_crossSum_le (hd.B_bv ω) (fun _ hx => abs_le_pathSup_of_isCadlag (hd.X_cadlag ω) hx) P

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ X_iΔB_i` is integrable.
Restates `TidyR7ProductStep.ProductStepData.integrable_sumXB` for càdlàg bonds. -/
theorem integrable_sumXB (P : Partition s t) : Integrable (sumRS P (addProc A M) B) μ :=
  hd.int_XB.mono' (measurable_sumRS hd.measurable_X hd.measurable_B P).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hd.abs_sumXB_le P ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ B_iΔA_i` is integrable.
Restates `TidyR7ProductStep.ProductStepData.integrable_sumBA` for càdlàg bonds. -/
theorem integrable_sumBA (P : Partition s t) : Integrable (sumRS P B A) μ :=
  hd.int_BA.mono' (measurable_sumRS hd.measurable_B hd.A_meas P).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hd.abs_sumBA_le P ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ ΔX_iΔB_i` is integrable.
Restates `TidyR7ProductStep.ProductStepData.integrable_sumCross` for càdlàg bonds. -/
theorem integrable_sumCross (P : Partition s t) : Integrable (sumCross P (addProc A M) B) μ :=
  (hd.int_XB.const_mul 2).mono'
    (measurable_sumCross hd.measurable_X hd.measurable_B P).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hd.abs_sumCross_le P ω)

/-- Cochrane (2023), A1 §1.6, p. 567: each term `B_{t_i}ΔM_i` of a partition is integrable.
Restates `TidyR7ProductStep.ProductStepData.integrable_term` for càdlàg bonds. -/
theorem integrable_term (P : Partition s t) {i : ℕ} (hi : i < P.n) :
    Integrable (fun ω => B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω)) μ :=
  hd.int_BM _ _ (t_mem P hi.le).1 (P.strictMono (Nat.lt_succ_self i)).le (t_mem P hi).2

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ B_iΔM_i` is integrable.
Restates `TidyR7ProductStep.ProductStepData.integrable_sumBM` for càdlàg bonds. -/
theorem integrable_sumBM (P : Partition s t) : Integrable (sumRS P B M) μ := by
  have e : sumRS P B M = fun ω => ∑ i ∈ Finset.range P.n,
      B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω) := rfl
  rw [e]
  exact integrable_finsetSum _ fun i hi => hd.integrable_term P (Finset.mem_range.1 hi)

/-- Cochrane (2023), A1 §1.6, p. 567: `B_tX_t − B_sX_s` is integrable (it is the sum of the four
integrable partition sums of `TidyR7ProductStep.pathwise_identity`).
Restates `TidyR7ProductStep.ProductStepData.integrable_lhs` for càdlàg bonds. -/
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

/-- Cochrane (2023), A1 §1.6, p. 567: path by path, `Σ X_iΔB_i → ∫ X_− dB` (extension (a)). -/
theorem tendsto_sumXB (P : ℕ → Partition s t) (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0))
    (ω : Ω) :
    Tendsto (fun k => sumRS (P k) (addProc A M) B ω) atTop (𝓝 (intLeft s t (addProc A M) B ω)) :=
  tendsto_rsSum_leftLim (hd.X_cadlag ω) (hd.B_bv ω) (hd.B_cadlag ω) P hP

/-- Cochrane (2023), A1 §1.6, p. 567: path by path, `Σ B_iΔA_i → ∫ B_− dA` (extension (a)). -/
theorem tendsto_sumBA (P : ℕ → Partition s t) (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0))
    (ω : Ω) : Tendsto (fun k => sumRS (P k) B A ω) atTop (𝓝 (intLeft s t B A ω)) :=
  tendsto_rsSum_leftLim (hd.B_cadlag ω) (hd.A_bv ω) (hd.A_cadlag ω) P hP

/-- Cochrane (2023), A1 §1.6, p. 567: path by path, `Σ ΔX_iΔB_i → Σ_{s<u≤t} ΔX_uΔB_u`
(extension (b)). -/
theorem tendsto_sumCross (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) (ω : Ω) :
    Tendsto (fun k => sumCross (P k) (addProc A M) B ω) atTop
      (𝓝 (jumpCov s t (addProc A M) B ω)) :=
  tendsto_crossSum_jumpSum (hd.X_cadlag ω) (hd.B_bv ω) (hd.B_cadlag ω) P hP

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_{(s,t]} X_− dB` is measurable (pointwise limit of
measurable partition sums). -/
theorem measurable_intLeftXB : Measurable (intLeft s t (addProc A M) B) := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  exact measurable_of_tendsto_metrizable
    (fun k => measurable_sumRS hd.measurable_X hd.measurable_B (P k))
    (tendsto_pi_nhds.2 (hd.tendsto_sumXB P hP))

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_{(s,t]} B_− dA` is measurable. -/
theorem measurable_intLeftBA : Measurable (intLeft s t B A) := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  exact measurable_of_tendsto_metrizable (fun k => measurable_sumRS hd.measurable_B hd.A_meas (P k))
    (tendsto_pi_nhds.2 (hd.tendsto_sumBA P hP))

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ Σ_{s<u≤t} ΔX_uΔB_u` is measurable. -/
theorem measurable_jumpCov : Measurable (jumpCov s t (addProc A M) B) := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  exact measurable_of_tendsto_metrizable
    (fun k => measurable_sumCross hd.measurable_X hd.measurable_B (P k))
    (tendsto_pi_nhds.2 (hd.tendsto_sumCross P hP))

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_{(s,t]} X_− dB` is integrable (limit of measurable
sums dominated by `sup|X|·Var(B)`). -/
theorem integrable_intLeftXB : Integrable (intLeft s t (addProc A M) B) μ := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  exact integrable_of_tendsto (fun k => measurable_sumRS hd.measurable_X hd.measurable_B (P k))
    hd.int_XB (fun k ω => hd.abs_sumXB_le (P k) ω) (hd.tendsto_sumXB P hP)

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_{(s,t]} B_− dA` is integrable. -/
theorem integrable_intLeftBA : Integrable (intLeft s t B A) μ := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  exact integrable_of_tendsto (fun k => measurable_sumRS hd.measurable_B hd.A_meas (P k))
    hd.int_BA (fun k ω => hd.abs_sumBA_le (P k) ω) (hd.tendsto_sumBA P hP)

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ Σ_{s<u≤t} ΔX_uΔB_u` is integrable. -/
theorem integrable_jumpCov : Integrable (jumpCov s t (addProc A M) B) μ := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  exact integrable_of_tendsto (fun k => measurable_sumCross hd.measurable_X hd.measurable_B (P k))
    (hd.int_XB.const_mul 2) (fun k ω => hd.abs_sumCross_le (P k) ω) (hd.tendsto_sumCross P hP)

/-- Cochrane (2023), A1 §1.6, p. 567: path by path,
`∫_s^t X dB = ∫_{(s,t]} X_− dB + Σ_{s<u≤t} ΔX_uΔB_u`
(`TidyR7JumpSums.rsInt_eq_leftLim_add_jumpSum`). -/
theorem intRS_eq (ω : Ω) :
    intRS s t (addProc A M) B ω = intLeft s t (addProc A M) B ω + jumpCov s t (addProc A M) B ω :=
  rsInt_eq_leftLim_add_jumpSum hd.le (hd.X_cadlag ω) (hd.B_bv ω) (hd.B_cadlag ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_s^t X dB` is integrable.
Restates `TidyR7ProductStep.ProductStepData.integrable_intXB` for càdlàg bonds. -/
theorem integrable_intXB : Integrable (intRS s t (addProc A M) B) μ := by
  have e : intRS s t (addProc A M) B = intLeft s t (addProc A M) B + jumpCov s t (addProc A M) B :=
    funext hd.intRS_eq
  rw [e]
  exact hd.integrable_intLeftXB.add hd.integrable_jumpCov

/-! ## The martingale terms vanish in conditional expectation (as in I2) -/

variable [IsFiniteMeasure μ]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: for `s ≤ u ≤ v ≤ t`, `E_s[B_u(M_v − M_u)] = 0`
a.s. (restated from `TidyR7ProductStep.ProductStepData.condExp_mart_incr_zero`; only adaptedness
of `B` and integrability are used). -/
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

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔM_i] = 0`** a.s., at every
partition, for jumping `B` as well.
Restates `TidyR7ProductStep.ProductStepData.condExp_sumBM_zero` for càdlàg bonds. -/
theorem condExp_sumBM_zero (P : Partition s t) : μ[sumRS P B M | 𝓕 s] =ᵐ[μ] 0 := by
  have e : sumRS P B M = ∑ i ∈ Finset.range P.n,
      fun ω => B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω) := by
    funext ω
    simp only [sumRS, rsSum, Finset.sum_apply]
  have h : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range P.n,
      μ[fun ω => B (P.t i) ω * (M (P.t (i + 1)) ω - M (P.t i) ω) | 𝓕 s] ω = 0 :=
    (eventually_all_finset _).2 fun i hi => by
      have hi' := Finset.mem_range.1 hi
      filter_upwards [hd.condExp_mart_incr_zero (t_mem P hi'.le).1
        (P.strictMono (Nat.lt_succ_self i)).le (t_mem P hi').2] with ω hω
      exact hω
  rw [e]
  filter_upwards [condExp_finsetSum (fun i hi => hd.integrable_term P (Finset.mem_range.1 hi))
    (𝓕 s), h] with ω h1 h2
  rw [h1, Finset.sum_apply, Finset.sum_eq_zero h2]
  rfl

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the exact discrete identity in conditional
expectation**, for jumping `B`: at every partition, a.s.,
`E_s[B_tX_t − B_sX_s] = E_s[Σ X_iΔB_i] + E_s[Σ B_iΔA_i] + E_s[Σ ΔX_iΔB_i]`.
Restates `TidyR7ProductStep.ProductStepData.discrete_identity` for càdlàg bonds. -/
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

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔX_i] = E_s[Σ B_iΔA_i]` a.s. at every
partition (the martingale part of `X` drops out).
Restates `TidyR7ProductStep.ProductStepData.condExp_sumBX_eq` for càdlàg bonds. -/
theorem condExp_sumBX_eq (P : Partition s t) :
    μ[sumRS P B (addProc A M) | 𝓕 s] =ᵐ[μ] μ[sumRS P B A | 𝓕 s] := by
  have e : sumRS P B (addProc A M) = sumRS P B A + sumRS P B M :=
    funext fun ω => sumRS_add_right P B A M ω
  rw [e]
  filter_upwards [condExp_add (hd.integrable_sumBA P) (hd.integrable_sumBM P) (𝓕 s),
    hd.condExp_sumBM_zero P] with ω h1 h2
  rw [h1, Pi.add_apply, h2]
  simp

/-! ## The conditional limits -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ X_iΔB_i] → E_s[∫ X_− dB]`** a.s., along
any sequence of partitions with mesh `→ 0`.
Restates `TidyR7ProductStep.ProductStepData.tendsto_condExp_sumXB` for càdlàg bonds. -/
theorem tendsto_condExp_sumXB (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (P k) (addProc A M) B | 𝓕 s] ω) atTop
      (𝓝 (μ[intLeft s t (addProc A M) B | 𝓕 s] ω)) :=
  ae_tendsto_condExp_of_dominated (𝓕.le s)
    (fun k => measurable_sumRS hd.measurable_X hd.measurable_B (P k)) hd.int_XB
    (fun k ω => hd.abs_sumXB_le (P k) ω) (hd.tendsto_sumXB P hP)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔA_i] → E_s[∫ B_− dA]`** a.s., along
any sequence of partitions with mesh `→ 0`.
Restates `TidyR7ProductStep.ProductStepData.tendsto_condExp_sumBA` for càdlàg bonds. -/
theorem tendsto_condExp_sumBA (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (P k) B A | 𝓕 s] ω) atTop
      (𝓝 (μ[intLeft s t B A | 𝓕 s] ω)) :=
  ae_tendsto_condExp_of_dominated (𝓕.le s)
    (fun k => measurable_sumRS hd.measurable_B hd.A_meas (P k)) hd.int_BA
    (fun k ω => hd.abs_sumBA_le (P k) ω) (hd.tendsto_sumBA P hP)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ ΔX_iΔB_i] → E_s[Σ_{s<u≤t} ΔX_uΔB_u]`**
a.s., along any sequence of partitions with mesh `→ 0`: the cross sum no longer vanishes
when `B` and `X` jump together.
Restates `TidyR7ProductStep.ProductStepData.tendsto_condExp_cross` for càdlàg bonds. -/
theorem tendsto_condExp_cross (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumCross (P k) (addProc A M) B | 𝓕 s] ω) atTop
      (𝓝 (μ[jumpCov s t (addProc A M) B | 𝓕 s] ω)) :=
  ae_tendsto_condExp_of_dominated (𝓕.le s)
    (fun k => measurable_sumCross hd.measurable_X hd.measurable_B (P k)) (hd.int_XB.const_mul 2)
    (fun k ω => hd.abs_sumCross_le (P k) ω) (hd.tendsto_sumCross P hP)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Σ B_iΔX_i] → E_s[∫ B_− dA]` a.s., along any
sequence of partitions with mesh `→ 0`.
Restates `TidyR7ProductStep.ProductStepData.tendsto_condExp_sumBX` for càdlàg bonds. -/
theorem tendsto_condExp_sumBX (P : ℕ → Partition s t)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[sumRS (P k) B (addProc A M) | 𝓕 s] ω) atTop
      (𝓝 (μ[intLeft s t B A | 𝓕 s] ω)) := by
  have he : ∀ᵐ ω ∂μ, ∀ k, μ[sumRS (P k) B (addProc A M) | 𝓕 s] ω = μ[sumRS (P k) B A | 𝓕 s] ω :=
    ae_all_iff.2 fun k => hd.condExp_sumBX_eq (P k)
  filter_upwards [he, hd.tendsto_condExp_sumBA P hP] with ω h1 h2
  exact (tendsto_congr h1).2 h2

/-! ## The corrected product step -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the product step for bonds with jumps (the
corrected (1.32) step).** Almost surely,
`E_s[B_tX_t − B_sX_s] = E_s[∫_{(s,t]} X_− dB] + E_s[∫_{(s,t]} B_− dA] + E_s[Σ_{s<u≤t} ΔX_uΔB_u]`,
`X = A + M`. The third term is the jump covariation of bonds and `X = Λ/P`; it vanishes when `B`
is continuous (`JumpStepData.rhs_eq_of_continuousOn`).
Generalises `TidyR7ProductStep.ProductStepData.product_step`. -/
theorem jump_step :
    μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A M) B | 𝓕 s] + μ[intLeft s t B A | 𝓕 s] +
        μ[jumpCov s t (addProc A M) B | 𝓕 s] := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.le
  have hid := ae_all_iff.2 fun k => hd.discrete_identity (P k)
  filter_upwards [hid, hd.tendsto_condExp_sumXB P hP, hd.tendsto_condExp_sumBA P hP,
    hd.tendsto_condExp_cross P hP] with ω h0 h1 h2 h3
  have hs := (h1.add h2).add h3
  have hc : Tendsto (fun k => (μ[sumRS (P k) (addProc A M) B | 𝓕 s] +
      μ[sumRS (P k) B A | 𝓕 s] + μ[sumCross (P k) (addProc A M) B | 𝓕 s]) ω) atTop
      (𝓝 (μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] ω)) := by
    refine (tendsto_congr fun k => ?_).1 tendsto_const_nhds
    exact h0 k
  simp only [Pi.add_apply] at hc ⊢
  exact tendsto_nhds_unique hc hs

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected step in two terms.** With the
Lebesgue–Stieltjes integral of the CURRENT `X` against `dB` (which charges `X(u)ΔB_u` at a jump),
a.s. `E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB] + E_s[∫_{(s,t]} B_− dA]`. -/
theorem jump_step_ls :
    μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[intRS s t (addProc A M) B | 𝓕 s] + μ[intLeft s t B A | 𝓕 s] := by
  have e : intRS s t (addProc A M) B = intLeft s t (addProc A M) B + jumpCov s t (addProc A M) B :=
    funext hd.intRS_eq
  filter_upwards [hd.jump_step, condExp_add hd.integrable_intLeftXB hd.integrable_jumpCov (𝓕 s)]
    with ω h1 h2
  rw [h1, e]
  simp only [Pi.add_apply] at h2 ⊢
  rw [h2]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `B·E_s dX` for jumping bonds.** The
expected-increment integral (`TidyR7ProductStep.ExpIncrLimit`) exists and equals
`E_s[∫_{(s,t]} B_− dA]`.
Generalises `TidyR7ProductStep.product_step_expIncr`. -/
theorem expIncrLimit_intLeft :
    ExpIncrLimit μ 𝓕 s t B (addProc A M) (μ[intLeft s t B A | 𝓕 s]) :=
  fun P hP => hd.tendsto_condExp_sumBX P hP

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected step with the expected-increment
integral.** If `B·E_s dX = L` then a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫ X_− dB] + L + E_s[Σ ΔX_uΔB_u]`: the book's two terms (read as limits
of left-point sums) miss the expected jump covariation.
Generalises `TidyR7ProductStep.product_step_expIncr`. -/
theorem jump_step_expIncr {L : Ω → ℝ} (hL : ExpIncrLimit μ 𝓕 s t B (addProc A M) L) :
    μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A M) B | 𝓕 s] + L + μ[jumpCov s t (addProc A M) B | 𝓕 s] := by
  filter_upwards [hd.jump_step, hd.expIncrLimit_intLeft.ae_eq hd.le hL] with ω h1 h2
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the left-point reading of the book's step
holds iff the expected jump covariation vanishes.** With `B·E_s dX = L`, a.s.
`E_s[B_tX_t − B_sX_s] = lim E_s[Σ X_iΔB_i] + L` holds exactly where
`E_s[Σ_{s<u≤t} ΔX_uΔB_u] = 0`. -/
theorem book_step_iff {L : Ω → ℝ} (hL : ExpIncrLimit μ 𝓕 s t B (addProc A M) L) :
    ∀ᵐ ω ∂μ, (μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] ω =
        μ[intLeft s t (addProc A M) B | 𝓕 s] ω + L ω ↔
      μ[jumpCov s t (addProc A M) B | 𝓕 s] ω = 0) := by
  filter_upwards [hd.jump_step_expIncr hL] with ω h
  rw [h]
  simp only [Pi.add_apply]
  constructor <;> intro h' <;> linarith

end JumpStepData

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, in the book's notation, for jumping bonds.**
With `Λ_u/P_u = A_u + M_u` and the hypotheses of `JumpStepData`, a.s.
`E_s[Λ_tB_t/P_t − Λ_sB_s/P_s] = E_s[∫ (Λ/P)_− dB] + B·E_s d(Λ/P) + E_s[Σ_{s<u≤t} Δ(Λ/P)_uΔB_u]`,
with `B·E_s d(Λ/P) = E_s[∫ B_− dA]` (`TidyR7ProductStep.ExpIncrLimit`).
Generalises `TidyR7ProductStep.product_step_1_32`. -/
theorem jump_step_1_32 [IsFiniteMeasure μ] (hd : JumpStepData μ 𝓕 s t B A M)
    {Λ Pr : ℝ → Ω → ℝ} (hdec : ∀ u ω, Λ u ω / Pr u ω = A u ω + M u ω) :
    μ[fun ω => Λ t ω * B t ω / Pr t ω - Λ s ω * B s ω / Pr s ω | 𝓕 s] =ᵐ[μ]
        μ[intLeft s t (fun u ω => Λ u ω / Pr u ω) B | 𝓕 s] + μ[intLeft s t B A | 𝓕 s] +
          μ[jumpCov s t (fun u ω => Λ u ω / Pr u ω) B | 𝓕 s] ∧
      ExpIncrLimit μ 𝓕 s t B (fun u ω => Λ u ω / Pr u ω) (μ[intLeft s t B A | 𝓕 s]) := by
  have eX : (fun u ω => Λ u ω / Pr u ω) = addProc A M := funext fun u => funext fun ω => hdec u ω
  have eL : (fun ω => Λ t ω * B t ω / Pr t ω - Λ s ω * B s ω / Pr s ω) =
      fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω := by
    funext ω
    simp only [addProc]
    rw [← hdec t ω, ← hdec s ω]
    ring
  rw [eX, eL]
  exact ⟨hd.jump_step, hd.expIncrLimit_intLeft⟩

/-! ## Reduction to I2 when the bonds are continuous -/

namespace JumpStepData

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: I2's data with bonds càdlàg on `ℝ` (e.g. frozen
outside `[s, t]`) are data of the jump step. -/
theorem ofProductStepData (hd : ProductStepData μ 𝓕 s t B A M)
    (hc : ∀ ω, IsCadlag fun u => B u ω) : JumpStepData μ 𝓕 s t B A M where
  le := hd.le
  B_adapted := hd.B_adapted
  B_cadlag := hc
  B_bv := hd.B_bv
  A_meas := hd.A_meas
  A_cadlag := hd.A_cadlag
  A_bv := hd.A_bv
  M_mart := hd.M_mart
  M_cadlag := hd.M_cadlag
  int_XB := hd.int_XB
  int_BA := hd.int_BA
  int_BM := hd.int_BM

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: data of the jump step with bonds continuous on
`[s, t]` are I2's data (`TidyR7ProductStep.ProductStepData`). -/
theorem toProductStepData (hd : JumpStepData μ 𝓕 s t B A M)
    (hc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t)) : ProductStepData μ 𝓕 s t B A M where
  le := hd.le
  B_adapted := hd.B_adapted
  B_cont := hc
  B_bv := hd.B_bv
  A_meas := hd.A_meas
  A_cadlag := hd.A_cadlag
  A_bv := hd.A_bv
  M_mart := hd.M_mart
  M_cadlag := hd.M_cadlag
  int_XB := hd.int_XB
  int_BA := hd.int_BA
  int_BM := hd.int_BM

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: for continuous bonds the corrected right-hand
side is I2's**: path by path `∫ X_− dB = ∫ X dB`, `∫ B_− dA = ∫ B dA` and the jump covariation is
`0`, so `E_s[∫X_− dB] + E_s[∫B_− dA] + E_s[ΣΔXΔB] = E_s[∫X dB] + E_s[∫B dA]` exactly. -/
theorem rhs_eq_of_continuousOn (hd : JumpStepData μ 𝓕 s t B A M)
    (hc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t)) :
    μ[intLeft s t (addProc A M) B | 𝓕 s] + μ[intLeft s t B A | 𝓕 s] +
        μ[jumpCov s t (addProc A M) B | 𝓕 s] =
      μ[intRS s t (addProc A M) B | 𝓕 s] + μ[intRS s t B A | 𝓕 s] := by
  have e1 : intLeft s t (addProc A M) B = intRS s t (addProc A M) B := funext fun ω =>
    (rsInt_eq_rsInt_leftLim hd.le (hd.X_cadlag ω) (hd.B_bv ω) (hc ω)).symm
  have e2 : intLeft s t B A = intRS s t B A := funext fun ω =>
    rsInt_leftLim_of_continuousOn hd.le (hd.A_bv ω) (hd.A_cadlag ω) (hc ω)
  have e3 : jumpCov s t (addProc A M) B = 0 := funext fun ω =>
    jumpSum_eq_zero_of_continuousOn hd.le (hd.X_cadlag ω) (hd.B_bv ω) (hd.B_cadlag ω) (hc ω)
  rw [e1, e2, e3, condExp_zero, add_zero]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected theorem recovers I2.** For bonds
continuous on `[s, t]`, `JumpStepData.jump_step` is exactly
`TidyR7ProductStep.ProductStepData.product_step`:
`E_s[B_tX_t − B_sX_s] = E_s[∫ X dB] + E_s[∫ B dA]`. -/
theorem jump_step_recovers_product_step [IsFiniteMeasure μ] (hd : JumpStepData μ 𝓕 s t B A M)
    (hc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t)) :
    μ[fun ω => B t ω * addProc A M t ω - B s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ]
      μ[intRS s t (addProc A M) B | 𝓕 s] + μ[intRS s t B A | 𝓕 s] := by
  rw [← hd.rhs_eq_of_continuousOn hc]
  exact hd.jump_step

end JumpStepData

end Cochrane.Monetarism.TidyR7ProductStepJump
