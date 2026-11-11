/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR11JumpDiffCoinBMStep

/-!
# The jump-diffusion step of (1.32) in terms of money

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.32). Under the flow (1.31)
`d(B + M) = (iB + i^mM − Ps) dt` total nominal government debt `B + M` has neither jumps nor a
diffusive part: an open-market operation swaps bonds for money, `ΔB = −ΔM`, and diffusive bond
issues are matched by money, `σ_B = −σ_M`. Then the covariation of bonds with `Λ/P` is minus that
of money: the omitted term in the book's (1.32) step is `−E_t d[M, Λ/P]`, with continuous part
`−σ_Mσ_X dt` (I5e, `TidyR7MonetarismIto`) and jump part `−ΔMΔ(Λ/P)` (I4,
`TidyR7MonetarismJump.JumpMonetaryModel.jumpCov_B`) at once.

## Main results

* `jump_neg_of_continuous_add`: if `f + g` is continuous and `g` càdlàg, `Δf = −Δg`.
* `jumpCov_neg_of_continuous_add`: then `Σ ΔY Δf = −Σ ΔY Δg`.
* `fullCov_bonds_eq_neg_money`: with `B_bv + M_bv` continuous, `σ_B = −σ_M` and money
  `M = M_bv + M_c` (`M_c` continuous), `[B, Λ/P]_t − [B, Λ/P]_s = −([M, Λ/P]_t − [M, Λ/P]_s)`
  path by path.
* `jump_diff_step_money` (**the corrected (1.32) step in terms of money**): a.s.
  `E_s[B_tX_t − B_sX_s] = E_s[∫X_− dB_bv] + E_s[∫B_− dA] − E_s[[M, Λ/P]_t − [M, Λ/P]_s]`; the
  book's step holds iff `E_s[[M, Λ/P]_t − [M, Λ/P]_s] = 0` (`jump_diff_book_iff_money`).
* `jdcb_money`: on the realisation of `TidyR11JumpDiffCoinBMStep` with money
  `M = −e·ξ·1{u ≥ 1} − c·W` (so `B + M = 0`), the money covariation is `−(2cd + e²)`.
-/

namespace Cochrane.Monetarism.TidyR11JumpDiffMoney

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7JumpSums Cochrane.Monetarism.TidyR7ProductStepJump
  Cochrane.Monetarism.TidyR7BrownianTools Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR11JumpDiffStep Cochrane.Monetarism.TidyR11JumpDiffCoinBM
  Cochrane.Monetarism.TidyR11JumpDiffCoinBMStep
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: **an open-market operation is a swap**: if
`f + g` is continuous and `g` is càdlàg then `Δf = −Δg` (here `f = B`, `g = M`).
Generalises `TidyR7MonetarismJump.JumpMonetaryModel.jump_B`. -/
theorem jump_neg_of_continuous_add {f g : ℝ → ℝ} (hg : IsCadlag g)
    (hfg : Continuous fun u => f u + g u) (x : ℝ) : jump f x = -jump g x := by
  have hl : Function.leftLim f x = (f x + g x) - Function.leftLim g x := by
    refine leftLim_eq_of_tendsto ?_
    have h := (((hfg.tendsto x).mono_left nhdsWithin_le_nhds)).sub
      (hg.tendsto_nhdsLT_leftLim x)
    exact h.congr fun u => by ring
  simp only [jump, hl]
  ring

/-- Cochrane (2023), A1 §1.6, (1.31)–(1.32), p. 567: if `f + g` is continuous and `g` càdlàg,
the jump covariation with `f` is minus that with `g`: `Σ ΔY Δf = −Σ ΔY Δg`.
Generalises `TidyR7MonetarismJump.JumpMonetaryModel.jumpCov_B`. -/
theorem jumpCov_neg_of_continuous_add {s t : ℝ} {Y F G : ℝ → Ω → ℝ} (ω : Ω)
    (hG : IsCadlag fun u => G u ω) (hFG : Continuous fun u => F u ω + G u ω) :
    jumpCov s t Y F ω = -jumpCov s t Y G ω := by
  have h : (fun u => (Set.Ioc s t).indicator
      (fun u => jump (fun v => Y v ω) u * jump (fun v => F v ω) u) u) =
      fun u => -(Set.Ioc s t).indicator
        (fun u => jump (fun v => Y v ω) u * jump (fun v => G v ω) u) u := by
    funext u
    by_cases hu : u ∈ Set.Ioc s t
    · simp only [Set.indicator_of_mem hu, jump_neg_of_continuous_add hG hFG u, mul_neg]
    · simp only [Set.indicator_of_notMem hu, neg_zero]
  simp only [jumpCov, jumpSum]
  rw [h, tsum_neg]

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.32), p. 567: the covariation of bonds with `Λ/P` is
minus that of money.** If `B_bv + M_bv` is continuous (no jumps in total nominal debt),
`σ_B = −σ_M` (no diffusion in total nominal debt) and money is `M = M_bv + M_c` with `M_bv` càdlàg
and `M_c` continuous, then path by path
`∫σ_BK du + Σ ΔB ΔX = −(∫σ_MK du + Σ ΔM ΔX)`, `B = B_bv + B_c`.
Combines and generalises `TidyR7MonetarismJump.JumpMonetaryModel.jumpCov_B` and
`TidyR7MonetarismIto.ItoMonetaryModel.money_diff`. -/
theorem fullCov_bonds_eq_neg_money {s t : ℝ} {Bbv Bc Mbv Mcm X σB σM K : ℝ → Ω → ℝ} (ω : Ω)
    (hBbv : IsCadlag fun u => Bbv u ω) (hBc : Continuous fun u => Bc u ω)
    (hMbv : IsCadlag fun u => Mbv u ω) (hMcm : Continuous fun u => Mcm u ω)
    (hwealth : Continuous fun u => Bbv u ω + Mbv u ω) (hσ : ∀ u, σB u ω = -σM u ω) :
    fullCov s t σB K X (addProc Bbv Bc) ω = -fullCov s t σM K X (addProc Mbv Mcm) ω := by
  simp only [fullCov]
  rw [jumpCov_add_continuous_right ω hBbv hBc, jumpCov_add_continuous_right ω hMbv hMcm,
    jumpCov_neg_of_continuous_add ω hMbv hwealth]
  have e : (∫ u in s..t, σB u ω * K u ω) = -∫ u in s..t, σM u ω * K u ω := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext u
    rw [hσ u]
    ring
  rw [e]
  ring

variable {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}
  {Bbv Bc A Md Mc σB K : ℝ → Ω → ℝ} {Cσ CK : ℝ}

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected step in terms of money.** In the
setting of `TidyR11JumpDiffStep.JumpDiffData`, with money `M = M_bv + M_c` (`M_bv` càdlàg,
`M_c` continuous) such that `B_bv + M_bv` is continuous and `σ_B = −σ_M` (the flow (1.31)), a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫ X_− dB_bv] + E_s[∫ B_− dA] − E_s[[M, X]_t − [M, X]_s]`,
`X = Λ/P`: the omitted term is `−E_t d[M, Λ/P] = −(σ_Mσ_X dt + ΔMΔ(Λ/P))`. -/
theorem jump_diff_step_money (hd : JumpDiffData μ 𝓕 W s t Bbv Bc A Md Mc σB K Cσ CK)
    {Mbv Mcm σM : ℝ → Ω → ℝ} (hMbv : ∀ ω, IsCadlag fun u => Mbv u ω)
    (hMcm : ∀ ω, Continuous fun u => Mcm u ω)
    (hwealth : ∀ ω, Continuous fun u => Bbv u ω + Mbv u ω) (hσ : ∀ u ω, σB u ω = -σM u ω)
    (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
        addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A (addProc Md Mc)) Bbv | 𝓕 s]
        + μ[intLeft s t (addProc Bbv Bc) A | 𝓕 s]
        - μ[fullCov s t σM K (addProc A (addProc Md Mc)) (addProc Mbv Mcm) | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have h := hd.jump_diff_step_fullCov hB hW h𝓕 hs hst
  have e : fullCov s t σB K (addProc A (addProc Md Mc)) (addProc Bbv Bc) =
      -fullCov s t σM K (addProc A (addProc Md Mc)) (addProc Mbv Mcm) :=
    funext fun ω => fullCov_bonds_eq_neg_money ω (hd.bv.B_cadlag ω) (hd.Bc_cont ω) (hMbv ω)
      (hMcm ω) (hwealth ω) fun u => hσ u ω
  rw [e] at h
  filter_upwards [h, condExp_neg (fullCov s t σM K (addProc A (addProc Md Mc)) (addProc Mbv Mcm))
    (𝓕 s)] with ω h1 h2
  rw [h1, Pi.add_apply, Pi.add_apply, h2, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step holds iff the expected
covariation of money with `Λ/P` vanishes** (continuous and jump parts together), under the
hypotheses of `jump_diff_step_money`. -/
theorem jump_diff_book_iff_money (hd : JumpDiffData μ 𝓕 W s t Bbv Bc A Md Mc σB K Cσ CK)
    {Mbv Mcm σM : ℝ → Ω → ℝ} (hMbv : ∀ ω, IsCadlag fun u => Mbv u ω)
    (hMcm : ∀ ω, Continuous fun u => Mcm u ω)
    (hwealth : ∀ ω, Continuous fun u => Bbv u ω + Mbv u ω) (hσ : ∀ u ω, σB u ω = -σM u ω)
    (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    (μ[fun ω => addProc Bbv Bc t ω * addProc A (addProc Md Mc) t ω -
        addProc Bbv Bc s ω * addProc A (addProc Md Mc) s ω | 𝓕 s] =ᵐ[μ]
      μ[intLeft s t (addProc A (addProc Md Mc)) Bbv | 𝓕 s]
        + μ[intLeft s t (addProc Bbv Bc) A | 𝓕 s]) ↔
      μ[fullCov s t σM K (addProc A (addProc Md Mc)) (addProc Mbv Mcm) | 𝓕 s] =ᵐ[μ] 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hmain := jump_diff_step_money hd hMbv hMcm hwealth hσ hB hW h𝓕 hs hst
  constructor
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h1 h2 ⊢
    linarith
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h1 h2 ⊢
    linarith

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.32), p. 567 (non-vacuity): money on the realisation.**
On `TidyR11JumpDiffCoinBMStep.jdcbData` take money `M = −e·ξ·1{u ≥ 1} − c·W` (`σ_M = −c`), so
that `B + M = 0` has neither jumps nor diffusion. Path by path the money covariation with `Λ/P`
is `−(2cd + e²)`, and a.s.
`E_0[B_2X_2 − B_0X_0] = E_0[∫X_− dB_bv] + E_0[∫B_− dA] − E_0[[M, X]_2 − [M, X]_0]`. -/
theorem jdcb_money (c d e : ℝ) :
    fullCov 0 2 (fun _ _ => -c) (fun _ _ => d)
        (addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)))
        (addProc (fun u ω => -cbJ e u ω) (jdBc (-c))) = (fun _ => -(2 * (c * d) + e ^ 2)) ∧
      cbMeasure[fun ω => addProc (cbJ e) (jdBc c) 2 ω *
          addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)) 2 ω -
          addProc (cbJ e) (jdBc c) 0 ω * addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)) 0 ω
          | cbF 0] =ᵐ[cbMeasure]
        cbMeasure[intLeft 0 2 (addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d))) (cbJ e)
          | cbF 0]
          + cbMeasure[intLeft 0 2 (addProc (cbJ e) (jdBc c)) (fun _ _ => 0) | cbF 0]
          - cbMeasure[fullCov 0 2 (fun _ _ => -c) (fun _ _ => d)
              (addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d)))
              (addProc (fun u ω => -cbJ e u ω) (jdBc (-c))) | cbF 0] := by
  have hd := jdcbData c d e
  have hMbv : ∀ ω, IsCadlag fun u => -cbJ e u ω := fun ω =>
    (cadlag_cbJ e ω).continuous_comp (g := fun y => -y) continuous_neg
  have hw : ∀ ω, Continuous fun u => cbJ e u ω + -cbJ e u ω := fun ω => by
    simp only [add_neg_cancel]
    exact continuous_const
  have hσ : ∀ (u : ℝ) (ω : (ℕ → ℝ) × Bool), (fun _ _ => c) u ω = -(fun _ _ => -c) u ω :=
    fun _ _ => (neg_neg c).symm
  refine ⟨?_, jump_diff_step_money hd hMbv (continuous_jdBc (-c)) hw hσ isPreBrownianReal_cbW
    measurable_cbW cbF_isBM le_rfl (by norm_num)⟩
  funext ω
  have h := fullCov_bonds_eq_neg_money (s := 0) (t := 2) (K := fun _ _ => d)
    (Bbv := cbJ e) (Bc := jdBc c) (Mbv := fun u ω => -cbJ e u ω) (Mcm := jdBc (-c))
    (σB := fun _ _ => c) (σM := fun _ _ => -c)
    (X := addProc (fun _ _ => 0) (addProc (cbJ e) (jdMc d))) ω (cadlag_cbJ e ω)
    (continuous_jdBc c ω) (hMbv ω) (continuous_jdBc (-c) ω) (hw ω) fun u => hσ u ω
  rw [jdcb_fullCov] at h
  linarith

end Cochrane.Monetarism.TidyR11JumpDiffMoney
