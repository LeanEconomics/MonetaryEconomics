/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7ProductStepJump
import Monetarism.TidyR7ItoProductRule
import Monetarism.TidyR7ProductStepCases

/-!
# The product step of (1.32) for jump-diffusion bonds and prices

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The middle step of (1.32),
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`, misses the covariation of bonds and `Λ/P`. Its jump part
was found in `TidyR7ProductStepJump` (bounded-variation bonds that jump with `Λ/P`), its
continuous part in `TidyR7ItoBondStep` (Itô bonds against an Itô `Λ/P`). Here both are present at
once: one product step for jumps and diffusion together.

## Setting (`JumpDiffData`)

`X = Λ/P = A + M_d + M_c` and `B = B_bv + B_c` on `[s, t]`, where
* `A` is adapted, càdlàg, of bounded variation (it may jump);
* `M_d` is a càdlàg martingale of bounded variation (a compensated jump martingale, e.g. a coin
  revealed at a fixed date);
* `B_bv` is adapted, càdlàg, of bounded variation (bonds may jump);
* `M_c = ∫K dW` and `B_c = ∫σ_B dW` are Itô processes without drift
  (`TidyR7ItoProcess.ItoProcess`) with every path continuous and martingales;
* the integrability conditions of `TidyR7ProductStepJump.JumpStepData` for the three
  bounded-variation factors (`B_bv` against `X`, `A` and `M_d` against `B_c`), and
  `B_c(u)(M_d(v) − M_d(u))` integrable.

## Main results

* `JumpDiffData.jump_diff_step` (**the unified corrected step**): almost surely
  `E_s[B_tX_t − B_sX_s] = E_s[∫_{(s,t]} X_− dB_bv] + E_s[∫_{(s,t]} B_− dA]`
  `+ E_s[∫_s^t σ_B K du] + E_s[Σ_{s<u≤t} ΔB_uΔX_u]`.
  The last two terms are the full covariation `E_s([B, X]_t − [B, X]_s)`: continuous part
  `σ_BK dt`, jump part `ΔBΔX`. The proof splits `BX = B_bv X + A B_c + M_d B_c + B_c M_c`:
  I4's jump step (`TidyR7ProductStepJump.JumpStepData.jump_step`) for the first three products,
  I5d's product rule (`TidyR7ItoProductRule.condExp_product_rule`) for the last; the martingale
  integrals `∫ B_c dM_d` (`JumpDiffData.condExp_intLeft_Bc_Md_zero`) and the diffusive integrals
  `∫ X K dW`, `∫ B σ_B dW` have zero conditional mean.
* `JumpDiffData.jump_diff_step_fullCov`, `JumpDiffData.jd_book_iff`: the book's two-term step holds
  iff `E_s` of the full covariation `∫σ_BK du + ΣΔBΔX` (`fullCov`) vanishes.
* Reductions: `JumpDiffData.jd_recovers_jump_step` (`σ_B = K = 0`, `B_c = M_c = 0`: I4's
  `TidyR7ProductStepJump.JumpStepData.jump_step`), `JumpDiffData.jd_continuous_step` and
  `JumpDiffData.jd_recovers_bond_step` (no jumps: the continuous Itô form of I5e's
  `TidyR7ItoBondStep.bond_step`, with `C¹` drifts `∫Xβ + ∫Bν + ∫σ_BK`),
  `JumpDiffData.jd_recovers_product_step` (both: I2's
  `TidyR7ProductStep.ProductStepData.product_step`).
* `jump_diff_step_1_32`: the step in the book's notation with `Λ/P = X`.
-/

namespace Cochrane.Monetarism.TidyR11JumpDiffStep

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7JumpSums Cochrane.Monetarism.TidyR7ProductStepJump
  Cochrane.Monetarism.TidyR7BrownianTools Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR7ItoIntegral Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7ProductStepCases
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Tools -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: left-point sums against a martingale have zero
conditional mean.** For `Y` adapted on `[s, t]`, `N` a martingale and `Y_u(N_v − N_u)` integrable,
`E_s[Σ Y_iΔN_i] = 0` a.s. at every partition. As
`TidyR7ProductStepJump.JumpStepData.condExp_sumBM_zero`, without bounded variation of `Y`. -/
theorem condExp_sumRS_martingale_zero {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℝ mΩ} {s t : ℝ} {Y N : ℝ → Ω → ℝ}
    (hY : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (Y u)) (hN : Martingale N 𝓕 μ)
    (hint : ∀ u v, s ≤ u → u ≤ v → v ≤ t → Integrable (fun ω => Y u ω * (N v ω - N u ω)) μ)
    (P : Partition s t) : μ[sumRS P Y N | 𝓕 s] =ᵐ[μ] 0 := by
  have hterm : ∀ u v, s ≤ u → u ≤ v → v ≤ t →
      μ[fun ω => Y u ω * (N v ω - N u ω) | 𝓕 s] =ᵐ[μ] 0 := by
    intro u v hsu huv hvt
    have hu : u ∈ Set.Icc s t := ⟨hsu, huv.trans hvt⟩
    have hNi := hN.integrable
    have h1 : μ[fun ω => Y u ω * (N v ω - N u ω) | 𝓕 u] =ᵐ[μ] 0 := by
      have e := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 u) (f := Y u) (g := N v - N u)
        (hY u hu) (hint u v hsu huv hvt) ((hNi v).sub (hNi u))
      have e2 := condExp_sub (m := 𝓕 u) (hNi v) (hNi u)
      have e3 := hN.2 u v huv
      have e4 : μ[N u | 𝓕 u] = N u :=
        condExp_of_stronglyMeasurable (𝓕.le u) (hN.1 u) (hNi u)
      filter_upwards [e, e2, e3] with ω h1 h2 h3
      have h1' : μ[fun ω => Y u ω * (N v ω - N u ω) | 𝓕 u] ω =
          Y u ω * μ[N v - N u | 𝓕 u] ω := h1
      rw [h1', h2, Pi.sub_apply, h3, e4]
      simp
    calc μ[fun ω => Y u ω * (N v ω - N u ω) | 𝓕 s]
        =ᵐ[μ] μ[μ[fun ω => Y u ω * (N v ω - N u ω) | 𝓕 u] | 𝓕 s] :=
          (condExp_condExp_of_le (𝓕.mono hsu) (𝓕.le u)).symm
      _ =ᵐ[μ] μ[(0 : Ω → ℝ) | 𝓕 s] := condExp_congr_ae h1
      _ = 0 := condExp_zero
  have e : sumRS P Y N = ∑ i ∈ Finset.range P.n,
      fun ω => Y (P.t i) ω * (N (P.t (i + 1)) ω - N (P.t i) ω) := by
    funext ω
    simp only [sumRS, rsSum, Finset.sum_apply]
  have h : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.range P.n,
      μ[fun ω => Y (P.t i) ω * (N (P.t (i + 1)) ω - N (P.t i) ω) | 𝓕 s] ω = 0 :=
    (eventually_all_finset _).2 fun i hi => by
      have hi' := Finset.mem_range.1 hi
      filter_upwards [hterm _ _ (t_mem P hi'.le).1
        (P.strictMono (Nat.lt_succ_self i)).le (t_mem P hi').2] with ω hω
      exact hω
  rw [e]
  filter_upwards [condExp_finsetSum (fun i hi => hint _ _ (t_mem P (Finset.mem_range.1 hi).le).1
    (P.strictMono (Nat.lt_succ_self i)).le (t_mem P (Finset.mem_range.1 hi)).2) (𝓕 s), h]
    with ω h1 h2
  rw [h1, Finset.sum_apply, Finset.sum_eq_zero h2]
  rfl

/-- Cochrane (2023), A1 §1.6, p. 567: `0 + Y = Y` for processes.
Restates `TidyR10DoobProductStep.addProc_zero_left`. -/
theorem jd_addProc_zero_left (Y : ℝ → Ω → ℝ) : addProc (fun _ _ => (0 : ℝ)) Y = Y := by
  funext u ω
  simp [addProc]

/-- Cochrane (2023), A1 §1.6, p. 567: `Y + 0 = Y` for processes.
Restates `TidyR7ProductStepCases.addProc_zero`. -/
theorem jd_addProc_zero_right (Y : ℝ → Ω → ℝ) : addProc Y (fun _ _ => (0 : ℝ)) = Y := by
  funext u ω
  simp [addProc]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **adding a continuous path does not change left
limits' defect**: for `f` càdlàg and `g` continuous, `(f + g)(x−) = f(x−) + g(x)`.
A continuous-summand analogue of `TidyR7StieltjesIntegral.leftLim_add_sub`. -/
theorem jd_leftLim_add_continuous {f g : ℝ → ℝ} (hf : IsCadlag f) (hg : Continuous g) (x : ℝ) :
    Function.leftLim (fun u => f u + g u) x = Function.leftLim f x + g x :=
  leftLim_eq_of_tendsto ((hf.tendsto_nhdsLT_leftLim x).add
    ((hg.tendsto x).mono_left nhdsWithin_le_nhds))

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **a continuous summand does not jump**:
`Δ(f + g)_x = Δf_x` for `f` càdlàg and `g` continuous. -/
theorem jd_jump_add_continuous {f g : ℝ → ℝ} (hf : IsCadlag f) (hg : Continuous g) (x : ℝ) :
    jump (fun u => f u + g u) x = jump f x := by
  simp only [jump, jd_leftLim_add_continuous hf hg x]
  ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the jump covariation ignores continuous summands
of the second factor: `Σ ΔY Δ(Z + G) = Σ ΔY ΔZ` for `Z` càdlàg and `G` continuous. -/
theorem jumpCov_add_continuous_right {s t : ℝ} {Y Z G : ℝ → Ω → ℝ} (ω : Ω)
    (hZ : IsCadlag fun u => Z u ω) (hG : Continuous fun u => G u ω) :
    jumpCov s t Y (addProc Z G) ω = jumpCov s t Y Z ω := by
  have h : ∀ u, jump (fun v => addProc Z G v ω) u = jump (fun v => Z v ω) u :=
    jd_jump_add_continuous hZ hG
  simp only [jumpCov, jumpSum, h]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the jump covariation ignores continuous summands
of the first factor: `Σ Δ(Y + G) ΔZ = Σ ΔY ΔZ` for `Y` càdlàg and `G` continuous. -/
theorem jumpCov_add_continuous_left {s t : ℝ} {Y Z G : ℝ → Ω → ℝ} (ω : Ω)
    (hY : IsCadlag fun u => Y u ω) (hG : Continuous fun u => G u ω) :
    jumpCov s t (addProc Y G) Z ω = jumpCov s t Y Z ω := by
  have h : ∀ u, jump (fun v => addProc Y G v ω) u = jump (fun v => Y v ω) u :=
    jd_jump_add_continuous hY hG
  simp only [jumpCov, jumpSum, h]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the full covariation** of `B` and `X = Λ/P` over
`(s, t]`: the continuous part `∫_s^t σ_B K du` plus the jump part `Σ_{s<u≤t} ΔB_uΔX_u`. -/
noncomputable def fullCov (s t : ℝ) (σB K X B : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  (∫ u in s..t, σB u ω * K u ω) + jumpCov s t X B ω

variable (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ) (s t : ℝ)
  (Bbv Bc A Md Mc σB K : ℝ → Ω → ℝ) (Cσ CK : ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the setting of the jump-diffusion product step.**
`X = Λ/P = A + M_d + M_c`, `B = B_bv + B_c` on `[s, t]`: the hypotheses of
`TidyR7ProductStepJump.JumpStepData` for `B_bv` against `X`, for `A` against `B_c` and for `M_d`
against `B_c`; `M_d` a martingale with `B_c(u)(M_d(v) − M_d(u))` integrable; `B_c = ∫σ_B dW` and
`M_c = ∫K dW` driftless Itô processes (`TidyR7ItoProcess.ItoProcess`) with every path
continuous. -/
structure JumpDiffData where
  bv : JumpStepData μ 𝓕 s t Bbv A (addProc Md Mc)
  cA : JumpStepData μ 𝓕 s t A (fun _ _ => 0) Bc
  cM : JumpStepData μ 𝓕 s t Md (fun _ _ => 0) Bc
  Md_mart : Martingale Md 𝓕 μ
  int_cM : ∀ u v, s ≤ u → u ≤ v → v ≤ t → Integrable (fun ω => Bc u ω * (Md v ω - Md u ω)) μ
  Bc_cont : ∀ ω, Continuous fun u => Bc u ω
  Mc_cont : ∀ ω, Continuous fun u => Mc u ω
  Bc_ito : ItoProcess μ 𝓕 W Bc (fun _ _ => 0) σB s t 0 Cσ
  Mc_ito : ItoProcess μ 𝓕 W Mc (fun _ _ => 0) K s t 0 CK

variable {μ 𝓕 W s t Bbv Bc A Md Mc σB K Cσ CK}

namespace JumpDiffData

variable (hd : JumpDiffData μ 𝓕 W s t Bbv Bc A Md Mc σB K Cσ CK)
include hd

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `ΔB = ΔB_bv` and `ΔX = Δ(A + M_d)`: the jump
covariation of `B` and `X` is that of their bounded-variation parts. -/
theorem jumpCov_eq_bv (ω : Ω) :
    jumpCov s t (addProc A (addProc Md Mc)) (addProc Bbv Bc) ω =
      jumpCov s t (addProc A Md) Bbv ω := by
  rw [jumpCov_add_continuous_right ω (hd.bv.B_cadlag ω) (hd.Bc_cont ω)]
  have e : addProc A (addProc Md Mc) = addProc (addProc A Md) Mc := by
    funext u ω
    simp only [addProc]
    ring
  rw [e]
  exact jumpCov_add_continuous_left ω ((hd.bv.A_cadlag ω).fun_add (hd.cM.B_cadlag ω))
    (hd.Mc_cont ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path,
`∫_{(s,t]} B_− dA = ∫_{(s,t]} (B_bv)_− dA + ∫_s^t B_c dA` (`B_c` is continuous). -/
theorem jd_intLeft_B_A (ω : Ω) :
    intLeft s t (addProc Bbv Bc) A ω = intLeft s t Bbv A ω + intRS s t Bc A ω := by
  have e : Function.leftLim (fun u => addProc Bbv Bc u ω) =
      fun x => Function.leftLim (fun u => Bbv u ω) x + Bc x ω :=
    funext (jd_leftLim_add_continuous (hd.bv.B_cadlag ω) (hd.Bc_cont ω))
  simp only [intLeft, intRS, e]
  exact rsInt_add_left (rsIntegrable_leftLim (hd.bv.B_cadlag ω))
    (rsIntegrable_of_continuousOn (hd.Bc_cont ω).continuousOn)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: path by path `∫_{(s,t]} (B_c)_− dA = ∫_s^t B_c dA`. -/
theorem jd_intLeft_Bc_A (ω : Ω) : intLeft s t Bc A ω = intRS s t Bc A ω :=
  rsInt_leftLim_of_continuousOn hd.bv.le (hd.cA.B_bv ω) (hd.cA.B_cadlag ω)
    (hd.Bc_cont ω).continuousOn

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_s^t B_c dA` is integrable. -/
theorem integrable_intRS_Bc_A : Integrable (intRS s t Bc A) μ := by
  have h := hd.cA.integrable_intLeftXB
  rw [jd_addProc_zero_left] at h
  exact h.congr (Eventually.of_forall hd.jd_intLeft_Bc_A)

variable [IsFiniteMeasure μ]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[∫ B_c dM_d] = 0`.** The integral of the
continuous Itô bond component against the jump martingale has zero conditional mean: it is the
limit of the left-point sums `Σ B_c(t_i)ΔM_d`, each of conditional mean zero
(`condExp_sumRS_martingale_zero`). -/
theorem condExp_intLeft_Bc_Md_zero : μ[intLeft s t Bc Md | 𝓕 s] =ᵐ[μ] 0 := by
  obtain ⟨P, hP⟩ := exists_partition_seq hd.bv.le
  have ht := hd.cM.tendsto_condExp_sumXB P hP
  rw [jd_addProc_zero_left] at ht
  have hBa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (Bc u) := fun u _ => hd.cA.M_mart.1 u
  have h0 := ae_all_iff.2 fun k =>
    condExp_sumRS_martingale_zero hBa hd.Md_mart hd.int_cM (P k)
  filter_upwards [ht, h0] with ω h1 h2
  have h3 : Tendsto (fun k => μ[sumRS (P k) Bc Md | 𝓕 s] ω) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun k => (h2 k).symm
  exact tendsto_nhds_unique h1 h3

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Δ(A B_c)] = E_s[∫ B_c dA]`** (I4's step for
the bounded-variation `A` against the martingale `B_c`; no jump term since `B_c` is
continuous). -/
theorem condExp_incr_A_Bc :
    μ[fun ω => A t ω * Bc t ω - A s ω * Bc s ω | 𝓕 s] =ᵐ[μ] μ[intRS s t Bc A | 𝓕 s] := by
  have h := hd.cA.jump_step
  rw [jd_addProc_zero_left] at h
  have e1 : intLeft s t A (fun _ _ => (0 : ℝ)) = 0 :=
    funext fun ω => rsInt_const_right hd.bv.le _ 0
  have e2 : jumpCov s t Bc A = 0 := funext fun ω =>
    jumpSum_eq_zero_of_continuousOn_left hd.bv.le (hd.cA.M_cadlag ω) (hd.cA.B_bv ω)
      (hd.cA.B_cadlag ω) (hd.Bc_cont ω).continuousOn
  have e3 : intLeft s t Bc A = intRS s t Bc A := funext hd.jd_intLeft_Bc_A
  rw [e1, e2, e3, condExp_zero, add_zero, add_zero] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Δ(M_d B_c)] = 0`**: the product of the jump
martingale and the continuous martingale has zero conditional drift (no common jumps, no
continuous covariation). -/
theorem condExp_incr_Md_Bc :
    μ[fun ω => Md t ω * Bc t ω - Md s ω * Bc s ω | 𝓕 s] =ᵐ[μ] 0 := by
  have h := hd.cM.jump_step
  rw [jd_addProc_zero_left] at h
  have e1 : intLeft s t Md (fun _ _ => (0 : ℝ)) = 0 :=
    funext fun ω => rsInt_const_right hd.bv.le _ 0
  have e2 : jumpCov s t Bc Md = 0 := funext fun ω =>
    jumpSum_eq_zero_of_continuousOn_left hd.bv.le (hd.cM.M_cadlag ω) (hd.cM.B_bv ω)
      (hd.cM.B_cadlag ω) (hd.Bc_cont ω).continuousOn
  rw [e1, e2, condExp_zero, add_zero, add_zero] at h
  filter_upwards [h, hd.condExp_intLeft_Bc_Md_zero] with ω h1 h2
  rw [h1, h2]

omit [IsFiniteMeasure μ] in
/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[Δ(B_c M_c)] = E_s[∫ σ_B K du]`** (I5d's
product rule `TidyR7ItoProductRule.condExp_product_rule` for two driftless Itô processes; the
diffusive integrals `∫ B_c K dW`, `∫ M_c σ_B dW` have zero conditional mean). -/
theorem condExp_incr_Bc_Mc (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => Bc t ω * Mc t ω - Bc s ω * Mc s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => ∫ u in s..t, σB u ω * K u ω | 𝓕 s] := by
  have h := condExp_product_rule hB hW h𝓕 hs hst hd.Bc_ito hd.Mc_ito
  refine h.trans (condExp_congr_ae ?_)
  have z1 := dtInt_of_eq_zero (P := μ) (𝓕 := 𝓕) (s := s) (t := t)
    (G := fun u ω => Bc u ω * 0) fun _ _ _ => mul_zero _
  have z2 := dtInt_of_eq_zero (P := μ) (𝓕 := 𝓕) (s := s) (t := t)
    (G := fun u ω => Mc u ω * 0) fun _ _ _ => mul_zero _
  filter_upwards [z1, z2] with ω h1 h2
  simp only [Pi.zero_apply] at h1 h2
  rw [h1, h2, zero_add, zero_add]

/-- Cochrane (2023), A1 §1.6, p. 567: `ω ↦ ∫_s^t σ_B K du` is integrable. -/
theorem jd_integrable_contCov (hst : s ≤ t) :
    Integrable (fun ω => ∫ u in s..t, σB u ω * K u ω) μ :=
  (memLp_integral_drift (itoIntegrand_mul hd.Bc_ito.diff hd.Mc_ito.diff) le_rfl hst
    le_rfl).integrable one_le_two

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the product step for jump-diffusion bonds and
prices (the unified corrected (1.32) step).** Almost surely,
`E_s[B_tX_t − B_sX_s] = E_s[∫_{(s,t]} X_− dB_bv] + E_s[∫_{(s,t]} B_− dA]`
`+ E_s[∫_s^t σ_B K du] + E_s[Σ_{s<u≤t} ΔB_uΔX_u]`,
with `X = A + M_d + M_c` and `B = B_bv + B_c`: the full covariation `E_s d[B, X]` (continuous
part `σ_BK dt`, jump part `ΔBΔX`) is the term the book's step omits. -/
theorem jump_diff_step (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
        addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A (addProc Md Mc)) Bbv | 𝓕 s]
        + μ[intLeft s t (addProc Bbv Bc) A | 𝓕 s]
        + μ[fun ω => ∫ u in s..t, σB u ω * K u ω | 𝓕 s]
        + μ[jumpCov s t (addProc A (addProc Md Mc)) (addProc Bbv Bc) | 𝓕 s] := by
  set X := addProc A (addProc Md Mc) with hX
  set f1 : Ω → ℝ := fun ω => Bbv t ω * X t ω - Bbv s ω * X s ω with hf1
  set f2 : Ω → ℝ := fun ω => A t ω * Bc t ω - A s ω * Bc s ω with hf2
  set f3 : Ω → ℝ := fun ω => Md t ω * Bc t ω - Md s ω * Bc s ω with hf3
  set f4 : Ω → ℝ := fun ω => Bc t ω * Mc t ω - Bc s ω * Mc s ω with hf4
  have hsplit : (fun ω => addProc Bbv Bc t ω * X t ω - addProc Bbv Bc s ω * X s ω) =
      f1 + f2 + f3 + f4 := by
    funext ω
    simp only [hf1, hf2, hf3, hf4, hX, addProc, Pi.add_apply]
    ring
  have i1 : Integrable f1 μ := hd.bv.integrable_lhs
  have i2 : Integrable f2 μ := by
    have h := hd.cA.integrable_lhs
    rw [jd_addProc_zero_left] at h
    exact h
  have i3 : Integrable f3 μ := by
    have h := hd.cM.integrable_lhs
    rw [jd_addProc_zero_left] at h
    exact h
  have i4 : Integrable f4 μ := by
    have mB := fun u (hu : u ∈ Set.Icc s t) => hd.Bc_ito.memLp hB hW h𝓕 hs hu
    have mM := fun u (hu : u ∈ Set.Icc s t) => hd.Mc_ito.memLp hB hW h𝓕 hs hu
    exact ((mB t ⟨hst.le, le_rfl⟩).integrable_mul (mM t ⟨hst.le, le_rfl⟩)).sub
      ((mB s ⟨le_rfl, hst.le⟩).integrable_mul (mM s ⟨le_rfl, hst.le⟩))
  have iL : Integrable (intLeft s t Bbv A) μ := hd.bv.integrable_intLeftBA
  have iR : Integrable (intRS s t Bc A) μ := hd.integrable_intRS_Bc_A
  have eBA : intLeft s t (addProc Bbv Bc) A = intLeft s t Bbv A + intRS s t Bc A :=
    funext hd.jd_intLeft_B_A
  have eJ : jumpCov s t X (addProc Bbv Bc) = jumpCov s t X Bbv :=
    funext fun ω => jumpCov_add_continuous_right ω (hd.bv.B_cadlag ω) (hd.Bc_cont ω)
  rw [hsplit, eBA, eJ]
  filter_upwards [condExp_add ((i1.add i2).add i3) i4 (𝓕 s), condExp_add (i1.add i2) i3 (𝓕 s),
    condExp_add i1 i2 (𝓕 s), condExp_add iL iR (𝓕 s), hd.bv.jump_step, hd.condExp_incr_A_Bc,
    hd.condExp_incr_Md_Bc, hd.condExp_incr_Bc_Mc hB hW h𝓕 hs hst]
    with ω h1 h2 h3 h4 h5 h6 h7 h8
  simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the unified step with the full covariation.**
Almost surely `E_s[B_tX_t − B_sX_s] = E_s[∫ X_− dB_bv] + E_s[∫ B_− dA] + E_s[[B, X]_t − [B, X]_s]`,
`[B, X]_t − [B, X]_s = ∫_s^t σ_BK du + Σ_{s<u≤t} ΔB_uΔX_u` (`fullCov`). -/
theorem jump_diff_step_fullCov (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
        addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A (addProc Md Mc)) Bbv | 𝓕 s]
        + μ[intLeft s t (addProc Bbv Bc) A | 𝓕 s]
        + μ[fullCov s t σB K (addProc A (addProc Md Mc)) (addProc Bbv Bc) | 𝓕 s] := by
  have iC := hd.jd_integrable_contCov hst.le
  have iJ : Integrable (jumpCov s t (addProc A (addProc Md Mc)) (addProc Bbv Bc)) μ := by
    have e : jumpCov s t (addProc A (addProc Md Mc)) (addProc Bbv Bc) =
        jumpCov s t (addProc A (addProc Md Mc)) Bbv :=
      funext fun ω => jumpCov_add_continuous_right ω (hd.bv.B_cadlag ω) (hd.Bc_cont ω)
    rw [e]
    exact hd.bv.integrable_jumpCov
  have e : fullCov s t σB K (addProc A (addProc Md Mc)) (addProc Bbv Bc) =
      (fun ω => ∫ u in s..t, σB u ω * K u ω) +
        jumpCov s t (addProc A (addProc Md Mc)) (addProc Bbv Bc) := rfl
  rw [e]
  filter_upwards [hd.jump_diff_step hB hW h𝓕 hs hst, condExp_add iC iJ (𝓕 s)] with ω h1 h2
  simp only [Pi.add_apply] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step holds iff the expected full
covariation vanishes.** The two-term form
`E_s[B_tX_t − B_sX_s] = E_s[∫ X_− dB_bv] + E_s[∫ B_− dA]` holds a.s. if and only if
`E_s[∫_s^t σ_BK du + Σ_{s<u≤t} ΔB_uΔX_u] = 0` a.s.: neither part need vanish on its own. -/
theorem jd_book_iff (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    (μ[fun ω => addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
        addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A (addProc Md Mc)) Bbv | 𝓕 s]
        + μ[intLeft s t (addProc Bbv Bc) A | 𝓕 s]) ↔
      μ[fullCov s t σB K (addProc A (addProc Md Mc)) (addProc Bbv Bc) | 𝓕 s] =ᵐ[μ] 0 := by
  have hmain := hd.jump_diff_step_fullCov hB hW h𝓕 hs hst
  constructor
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
    linarith
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
    linarith

/-! ## Reductions -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: with no diffusion (`σ_B = 0`, `B_c = M_c = 0`)
the unified step is I4's jump step** (`TidyR7ProductStepJump.JumpStepData.jump_step` for `B_bv`
against `X = A + M_d`): a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫ X_− dB] + E_s[∫ B_− dA] + E_s[Σ ΔBΔX]`, derived from
`JumpDiffData.jump_diff_step`. -/
theorem jd_recovers_jump_step (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hσ : ∀ u ω, σB u ω = 0)
    (hBc : ∀ u ω, Bc u ω = 0) (hMc : ∀ u ω, Mc u ω = 0) :
    μ[fun ω => Bbv t ω * addProc A Md t ω - Bbv s ω * addProc A Md s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A Md) Bbv | 𝓕 s] + μ[intLeft s t Bbv A | 𝓕 s]
        + μ[jumpCov s t (addProc A Md) Bbv | 𝓕 s] := by
  have h := hd.jump_diff_step hB hW h𝓕 hs hst
  have eB : Bc = fun _ _ => 0 := funext fun u => funext (hBc u)
  have eM : Mc = fun _ _ => 0 := funext fun u => funext (hMc u)
  have eσ : (fun ω => ∫ u in s..t, σB u ω * K u ω) = 0 := funext fun ω => by simp [hσ]
  rw [eB, eM, jd_addProc_zero_right, jd_addProc_zero_right, eσ, condExp_zero, add_zero] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: with no jumps the unified step is the continuous
Itô form.** If `B_bv`, `A` and `M_d` have paths continuous on `[s, t]`, left limits drop and the
jump term vanishes: a.s. `E_s[B_tX_t − B_sX_s] = E_s[∫ X dB_bv] + E_s[∫ B dA] + E_s[∫ σ_BK du]`
(the form of `TidyR7ItoBondStep.bond_step`, with pathwise Stieltjes integrals for the drifts). -/
theorem jd_continuous_step (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBc : ∀ ω, ContinuousOn (fun u => Bbv u ω) (Set.Icc s t))
    (hAc : ∀ ω, ContinuousOn (fun u => A u ω) (Set.Icc s t))
    (hMd : ∀ ω, ContinuousOn (fun u => Md u ω) (Set.Icc s t)) :
    μ[fun ω => addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
        addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω | 𝓕 s] =ᵐ[μ]
      μ[intRS s t (addProc A (addProc Md Mc)) Bbv | 𝓕 s]
        + μ[intRS s t (addProc Bbv Bc) A | 𝓕 s]
        + μ[fun ω => ∫ u in s..t, σB u ω * K u ω | 𝓕 s] := by
  have h := hd.jump_diff_step hB hW h𝓕 hs hst
  have hle := hst.le
  have e1 : intLeft s t (addProc A (addProc Md Mc)) Bbv =
      intRS s t (addProc A (addProc Md Mc)) Bbv := funext fun ω =>
    (rsInt_eq_rsInt_leftLim hle (hd.bv.X_cadlag ω) (hd.bv.B_bv ω) (hBc ω)).symm
  have e2 : intLeft s t (addProc Bbv Bc) A = intRS s t (addProc Bbv Bc) A := funext fun ω => by
    have hcont : ContinuousOn (fun u => addProc Bbv Bc u ω) (Set.Icc s t) :=
      (hBc ω).add (hd.Bc_cont ω).continuousOn
    exact rsInt_leftLim_of_continuousOn hle (hd.bv.A_bv ω) (hd.bv.A_cadlag ω) hcont
  have e3 : jumpCov s t (addProc A (addProc Md Mc)) (addProc Bbv Bc) = 0 := funext fun ω => by
    rw [hd.jumpCov_eq_bv ω]
    exact jumpSum_eq_zero_of_continuousOn_left hle
      ((hd.bv.A_cadlag ω).fun_add (hd.cM.B_cadlag ω)) (hd.bv.B_bv ω) (hd.bv.B_cadlag ω)
      ((hAc ω).add (hMd ω))
  rw [e1, e2, e3, condExp_zero, add_zero] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: with no jumps and `C¹` drifts the unified step is
I5e's bond step.** If moreover `B_bv(·, ω)` and `A(·, ω)` have continuous derivatives `β`, `ν`
(`dB_bv = β du`, `dA = ν du`), then a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X β du] + E_s[∫_s^t B ν du] + E_s[∫_s^t σ_BK du]`: the form of
`TidyR7ItoBondStep.bond_step` (drifts as pathwise time integrals,
`TidyR7ProductStepCases.rsInt_eq_integral_mul_deriv`). -/
theorem jd_recovers_bond_step (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) {β ν : ℝ → Ω → ℝ}
    (hβ : ∀ ω x, HasDerivAt (fun u => Bbv u ω) (β x ω) x) (hβc : ∀ ω, Continuous fun u => β u ω)
    (hν : ∀ ω x, HasDerivAt (fun u => A u ω) (ν x ω) x) (hνc : ∀ ω, Continuous fun u => ν u ω)
    (hMd : ∀ ω, ContinuousOn (fun u => Md u ω) (Set.Icc s t)) :
    μ[fun ω => addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
        addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => ∫ u in s..t, addProc A (addProc Md Mc) u ω * β u ω | 𝓕 s]
        + μ[fun ω => ∫ u in s..t, addProc Bbv Bc u ω * ν u ω | 𝓕 s]
        + μ[fun ω => ∫ u in s..t, σB u ω * K u ω | 𝓕 s] := by
  have hBcont : ∀ ω, ContinuousOn (fun u => Bbv u ω) (Set.Icc s t) := fun ω =>
    (continuous_iff_continuousAt.2 fun x => (hβ ω x).continuousAt).continuousOn
  have hAcont : ∀ ω, ContinuousOn (fun u => A u ω) (Set.Icc s t) := fun ω =>
    (continuous_iff_continuousAt.2 fun x => (hν ω x).continuousAt).continuousOn
  have h := hd.jd_continuous_step hB hW h𝓕 hs hst hBcont hAcont hMd
  have e1 : intRS s t (addProc A (addProc Md Mc)) Bbv =
      fun ω => ∫ u in s..t, addProc A (addProc Md Mc) u ω * β u ω := funext fun ω =>
    rsInt_eq_integral_mul_deriv hst.le
      ((hAcont ω).add ((hMd ω).add (hd.Mc_cont ω).continuousOn)) (hβ ω) (hβc ω)
  have e2 : intRS s t (addProc Bbv Bc) A = fun ω => ∫ u in s..t, addProc Bbv Bc u ω * ν u ω :=
    funext fun ω => rsInt_eq_integral_mul_deriv hst.le
      ((hBcont ω).add (hd.Bc_cont ω).continuousOn) (hν ω) (hνc ω)
  rw [e1, e2] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: with neither jumps nor diffusion the unified step
is I2's product step** (`TidyR7ProductStep.ProductStepData.product_step`): for `σ_B = 0`,
`B_c = M_c = 0` and `B_bv` continuous on `[s, t]`, a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫ X dB] + E_s[∫ B dA]`, `X = A + M_d`. -/
theorem jd_recovers_product_step (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hσ : ∀ u ω, σB u ω = 0)
    (hBc : ∀ u ω, Bc u ω = 0) (hMc : ∀ u ω, Mc u ω = 0)
    (hcont : ∀ ω, ContinuousOn (fun u => Bbv u ω) (Set.Icc s t)) :
    μ[fun ω => Bbv t ω * addProc A Md t ω - Bbv s ω * addProc A Md s ω | 𝓕 s] =ᵐ[μ]
      μ[intRS s t (addProc A Md) Bbv | 𝓕 s] + μ[intRS s t Bbv A | 𝓕 s] := by
  have h := hd.jd_recovers_jump_step hB hW h𝓕 hs hst hσ hBc hMc
  have eM : Mc = fun _ _ => 0 := funext fun u => funext (hMc u)
  have hj := hd.bv
  rw [eM, jd_addProc_zero_right] at hj
  rw [hj.rhs_eq_of_continuousOn hcont] at h
  exact h

end JumpDiffData

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, in the book's notation, for jump-diffusion bonds
and prices.** With `Λ_u/P_u = A_u + M_d(u) + M_c(u)` and bonds `B = B_bv + B_c` as in
`JumpDiffData`, a.s.
`E_s[Λ_tB_t/P_t − Λ_sB_s/P_s] = E_s[∫ (Λ/P)_− dB_bv] + E_s[∫ B_− dA] + E_s[[B, Λ/P]_t − [B, Λ/P]_s]`
with `E_t d[B, Λ/P] = σ_Bσ_X dt + ΔBΔ(Λ/P)` (`fullCov`); the book's two-term step holds iff the
last term vanishes (`JumpDiffData.jd_book_iff`). -/
theorem jump_diff_step_1_32 {Λ Pr : ℝ → Ω → ℝ}
    (hd : JumpDiffData μ 𝓕 W s t Bbv Bc A Md Mc σB K Cσ CK)
    (hΛ : ∀ u ω, Λ u ω / Pr u ω = addProc A (addProc Md Mc) u ω)
    (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => Λ t ω * addProc Bbv Bc t ω / Pr t ω - Λ s ω * addProc Bbv Bc s ω / Pr s ω
        | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (fun u ω => Λ u ω / Pr u ω) Bbv | 𝓕 s]
        + μ[intLeft s t (addProc Bbv Bc) A | 𝓕 s]
        + μ[fullCov s t σB K (fun u ω => Λ u ω / Pr u ω) (addProc Bbv Bc) | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have eX : (fun u ω => Λ u ω / Pr u ω) = addProc A (addProc Md Mc) :=
    funext fun u => funext (hΛ u)
  have eL : (fun ω => Λ t ω * addProc Bbv Bc t ω / Pr t ω -
      Λ s ω * addProc Bbv Bc s ω / Pr s ω) = fun ω =>
        addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
          addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω := funext fun ω => by
    rw [← hΛ t ω, ← hΛ s ω]
    ring
  rw [eL, eX]
  exact hd.jump_diff_step_fullCov hB hW h𝓕 hs hst

end Cochrane.Monetarism.TidyR11JumpDiffStep
