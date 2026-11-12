/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEBracket

/-!
# The conditional product rule for an Itô process with unbounded coefficients

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", eq. (1.32), p. 567 (Track 3, chunk B4). The step of (1.32) is a product rule
`E_t d(XY) = X E_t dY + Y E_t dX + E_t d[X, Y]` for `X = Λ/P` and `Y = B`. I5d proved it for two
Itô processes with bounded coefficients (`TidyR7ItoProductRule.condExp_product_rule`). Here
`X` is an Itô process with mean-square continuous coefficients (`TidyR12SDEProcess.ItoProcessMS`,
drift `a`, diffusion `H`; e.g. `Λ/P` geometric Brownian motion) and `Y` an Itô process with
bounded coefficients (drift `b`, diffusion `K`) whose values are bounded with a.s. continuous
paths (`Y` is itself an admissible integrand, `TidyR7ItoIntegral.ItoIntegrand`; e.g. bonds
`b₀ + c·arctan W`).

## The proof

Along the dyadic partitions, `X_tY_t − X_sY_s = ΣX_iΔY_i + ΣY_iΔX_i + ΣΔX_iΔY_i` exactly. With
`ΔX_i = A_i + I_i` (`A_i = ∫_{t_i}^{t_{i+1}} a`, `I_i = ∫_{t_i}^{t_{i+1}} H dW`):
`ΣX_iΔY_i → ∫Xb du + ∫XK dW` in `L²` (`TidyR7ItoCovariation.L2Tendsto_sumRS`, which needs only
`X` mean-square continuous); `ΣY_iA_i → ∫Y a du` in `L²` (`L2Tendsto_sumYA`, from
`E[(∫_{cell}(a − a_{t_i}))²] ≤ Δt²·ε`); `E_s[ΣY_iI_i] = 0` exactly (`condExp_sum_mul_itoInt_ms`:
`Y_i` is bounded and `𝓕_{t_i}`-measurable, `E_{t_i}[I_i] = 0`); and
`ΣΔX_iΔY_i → ∫HK du` in `L¹` (`TidyR12SDEBracket.tendsto_integral_abs_sumCross_ms`).
Conditional expectations are `L¹`-contractions (`tendsto_integral_abs_condExp_var`).

## Main results

* **`condExp_product_rule_ms`**: `E_s[X_tY_t − X_sY_s] = E_s[∫_s^t (Xb + Ya + HK) du]` a.s.
* `condExp_product_rule_ms_bookForm_iff`: the bracket-free form holds iff `E_s[∫_s^t HK du] = 0`.
-/

namespace Cochrane.Monetarism.TidyR12SDEProductRule

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoCovariation
  Cochrane.Monetarism.TidyR7ItoProductRule Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR7StieltjesCalculus
  Cochrane.Monetarism.TidyR12SDETools Cochrane.Monetarism.TidyR12SDEProcess
  Cochrane.Monetarism.TidyR12SDEBracket
open Cochrane.Monetarism.TidyR7ProductStep (sumRS sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s t : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `u ↦ Y_u a_u` is mean-square continuous for `Y`
bounded admissible and `a` mean-square continuous.
`TidyR7ItoProducts.MSIntegrand.mul_itoIntegrand` with the factors swapped. -/
theorem msIntegrand_itoIntegrand_mul [IsFiniteMeasure P] {Y a : ℝ → Ω → ℝ} {C : ℝ}
    (hY : ItoIntegrand P 𝓕 Y s t C) (ha : MSIntegrand P 𝓕 a s t) :
    MSIntegrand P 𝓕 (fun u ω => Y u ω * a u ω) s t := by
  have h := MSIntegrand.mul_itoIntegrand ha hY
  have e : (fun u ω => a u ω * Y u ω) = fun u ω => Y u ω * a u ω :=
    funext fun u => funext fun ω => mul_comm _ _
  rwa [e] at h

/-! ## `Σ Y_i A_i → ∫ Y a du` -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ Y_{t_i}∫_{t_i}^{t_{i+1}} a du → ∫_s^t Y a du` in
`L²`** along any partitions with mesh `→ 0`, for `Y` bounded admissible and `a` mean-square
continuous on `[s, t]`, `s < t` (the drift part of `Σ Y_iΔX_i`). -/
theorem L2Tendsto_sumYA [IsProbabilityMeasure P] (hst : s < t) {Y a : ℝ → Ω → ℝ} {C : ℝ}
    (hY : ItoIntegrand P 𝓕 Y s t C) (ha : MSIntegrand P 𝓕 a s t) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k ω => ∑ i ∈ Finset.range (ps k).n,
        Y ((ps k).t i) ω * dtInt P 𝓕 a ((ps k).t i) ((ps k).t (i + 1)) ω)
      (dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t) := by
  have hYa := msIntegrand_itoIntegrand_mul hY ha
  have h1 := L2Tendsto_dtSum hst hYa ps hps
  have hts : 0 < t - s := sub_pos.2 hst
  set E : ℕ → ℕ → Ω → ℝ := fun k i ω => dtInt P 𝓕 a ((ps k).t i) ((ps k).t (i + 1)) ω
    - a ((ps k).t i) ω * ((ps k).t (i + 1) - (ps k).t i) with hE
  set D : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (ps k).n, Y ((ps k).t i) ω * E k i ω
    with hD
  have mE : ∀ k, ∀ i < (ps k).n, MemLp (E k i) 2 P := fun k i hi =>
    (memLp_dtInt (ha.mono (t_mem _ hi.le).1 (t_mem _ hi).2)).sub
      ((ha.memLp _ (t_mem _ hi.le)).mul_const _)
  have mYE : ∀ k, ∀ i < (ps k).n, MemLp (fun ω => Y ((ps k).t i) ω * E k i ω) 2 P :=
    fun k i hi => (mE k i hi).of_le_mul (c := C)
      ((hY.measurable (t_mem _ hi.le)).aestronglyMeasurable.mul (mE k i hi).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hY.bound _ (t_mem _ hi.le) ω) (abs_nonneg _))
  have mD : ∀ k, MemLp (D k) 2 P := fun k =>
    memLp_finsetSum _ fun i hi => mYE k i (Finset.mem_range.1 hi)
  -- the cell error
  have hEbound : ∀ k i, i < (ps k).n → ∀ {ε : ℝ}, (∀ u ∈ Set.Icc ((ps k).t i) ((ps k).t (i + 1)),
      ∫ ω, (a u ω - a ((ps k).t i) ω) ^ 2 ∂P ≤ ε) →
      ∫ ω, E k i ω ^ 2 ∂P ≤ ((ps k).t (i + 1) - (ps k).t i) ^ 2 * ε := by
    intro k i hi ε hε
    set p := ps k
    have hai := ha.mono (t_mem p hi.le).1 (t_mem p hi).2
    have hci : MSIntegrand P 𝓕 (fun _ => a (p.t i)) (p.t i) (p.t (i + 1)) :=
      msIntegrand_const (hai.adapted _ ⟨le_rfl, t_le_succ p i⟩)
        (hai.memLp _ ⟨le_rfl, t_le_succ p i⟩)
    have h2 := integral_dtInt_sq_le_const (t_le_succ p i) (MSIntegrand.sub hai hci) hε
    have e : ∫ ω, E k i ω ^ 2 ∂P = ∫ ω, dtInt P 𝓕 (fun u ω => a u ω - a (p.t i) ω)
        (p.t i) (p.t (i + 1)) ω ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [dtInt_sub hai hci, dtInt_const (t_le_succ p i)
        (hai.adapted _ ⟨le_rfl, t_le_succ p i⟩) (hai.memLp _ ⟨le_rfl, t_le_succ p i⟩)] with
        ω h1 h3
      simp only [hE]
      rw [h1, h3]
      ring
    rw [e]
    exact h2
  have hD0 : Tendsto (fun k => ∫ ω, D k ω ^ 2 ∂P) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    set ε := η / (2 * ((t - s) ^ 2 * (C ^ 2 + 1))) with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨δ, hδ, hδa⟩ := ha.cont ε hε0
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
    refine ⟨N, fun k hk => ?_⟩
    set p := ps k with hp
    have hstep : ∀ i, 0 < p.t (i + 1) - p.t i := fun i => step_pos p i
    have hpt : ∀ ω, D k ω ^ 2 ≤ (t - s) * ∑ i ∈ Finset.range p.n,
        C ^ 2 * E k i ω ^ 2 / (p.t (i + 1) - p.t i) := by
      intro ω
      have hn : 0 < p.n := by
        rcases Nat.eq_zero_or_pos p.n with h | h
        · have h1 := p.first
          have h2 := p.last
          rw [h] at h2
          linarith
        · exact h
      have hT := Finset.sq_sum_div_le_sum_sq_div (Finset.range p.n)
        (fun i => Y (p.t i) ω * E k i ω) (fun i _ => hstep i)
      rw [sum_step_eq p, div_le_iff₀ hts] at hT
      refine hT.trans ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hts.le
      refine div_le_div_of_nonneg_right ?_ (hstep i).le
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have := hY.bound _ (t_mem p (Finset.mem_range.1 hi).le) ω
      exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2 |>.trans_eq rfl
    have iR : Integrable (fun ω => (t - s) * ∑ i ∈ Finset.range p.n,
        C ^ 2 * E k i ω ^ 2 / (p.t (i + 1) - p.t i)) P :=
      (integrable_finsetSum _ fun i hi =>
        (((mE k i (Finset.mem_range.1 hi)).integrable_sq).const_mul _).div_const _).const_mul _
    have hle := integral_mono (mD k).integrable_sq iR hpt
    rw [integral_const_mul, integral_finsetSum _ fun i hi =>
      (((mE k i (Finset.mem_range.1 hi)).integrable_sq).const_mul _).div_const _] at hle
    have hcell : ∀ i ∈ Finset.range p.n, ∫ ω, C ^ 2 * E k i ω ^ 2 / (p.t (i + 1) - p.t i) ∂P
        ≤ C ^ 2 * ε * (p.t (i + 1) - p.t i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [integral_div, integral_const_mul, div_le_iff₀ (hstep i)]
      have h1 := hEbound k i hi' (ε := ε) fun u hu => hδa u
        ⟨(t_mem p hi'.le).1.trans hu.1, hu.2.trans (t_mem p hi').2⟩ _ (t_mem p hi'.le) (by
          rw [abs_of_nonneg (sub_nonneg.2 hu.1)]
          exact ((sub_le_sub_right hu.2 _).trans (le_mesh p hi')).trans (hN k hk))
      calc C ^ 2 * ∫ ω, E k i ω ^ 2 ∂P ≤ C ^ 2 * ((p.t (i + 1) - p.t i) ^ 2 * ε) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = C ^ 2 * ε * (p.t (i + 1) - p.t i) * (p.t (i + 1) - p.t i) := by ring
    have hsum := Finset.sum_le_sum hcell
    rw [← Finset.mul_sum, sum_step_eq p] at hsum
    have h0 : 0 ≤ ∫ ω, D k ω ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    have h3 : (t - s) * (C ^ 2 * ε * (t - s)) < η := by
      have e : (t - s) * (C ^ 2 * ε * (t - s)) = η * (C ^ 2 / (2 * (C ^ 2 + 1))) := by
        rw [hε]
        field_simp
      rw [e]
      have : C ^ 2 / (2 * (C ^ 2 + 1)) < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith [sq_nonneg C]
      nlinarith
    calc ∫ ω, D k ω ^ 2 ∂P ≤ (t - s) * ∑ i ∈ Finset.range p.n,
          ∫ ω, C ^ 2 * E k i ω ^ 2 / (p.t (i + 1) - p.t i) ∂P := hle
      _ ≤ (t - s) * (C ^ 2 * ε * (t - s)) := mul_le_mul_of_nonneg_left hsum hts.le
      _ < η := h3
  have h2 : L2Tendsto P D 0 := ⟨mD, MemLp.zero, by simpa using hD0⟩
  have hseq : ∀ k, (fun ω => dtSum (fun u ω => Y u ω * a u ω) (ps k) ω + D k ω) =
      fun ω => ∑ i ∈ Finset.range (ps k).n,
        Y ((ps k).t i) ω * dtInt P 𝓕 a ((ps k).t i) ((ps k).t (i + 1)) ω := fun k => by
    funext ω
    simp only [hD, hE, dtSum, riemannSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h3 := (h1.add h2).congr_seq fun k => ae_of_all _ fun ω => congrFun (hseq k) ω
  exact h3.congr_ae (ae_of_all _ fun ω => by simp)

/-! ## `E_s[Σ Y_i I_i] = 0` -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E_s[Σ Y_{t_i}∫_{t_i}^{t_{i+1}} H dW] = 0`** for
`Y` bounded admissible and `H` mean-square continuous on `[s, t]`, `0 ≤ s`, along any partition
(tower property, pull out the bounded `𝓕_{t_i}`-measurable `Y_{t_i}`, `E_{t_i}[∫H dW] = 0`). -/
theorem condExp_sum_mul_itoInt_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H Y : ℝ → Ω → ℝ} {C : ℝ}
    (hH : MSIntegrand P 𝓕 H s t) (hY : ItoIntegrand P 𝓕 Y s t C) (p : Partition s t) :
    P[fun ω => ∑ i ∈ Finset.range p.n, Y (p.t i) ω * itoInt P 𝓕 W H (p.t i) (p.t (i + 1)) ω
      | 𝓕 s] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set f : ℕ → Ω → ℝ := fun i ω => Y (p.t i) ω * itoInt P 𝓕 W H (p.t i) (p.t (i + 1)) ω with hf
  have hI : ∀ i ∈ Finset.range p.n, Integrable (itoInt P 𝓕 W H (p.t i) (p.t (i + 1))) P :=
    fun i hi => (memLp_itoInt_ms hB hW h𝓕 (hs.trans (t_mem p (Finset.mem_range.1 hi).le).1)
      (hH.mono (t_mem p (Finset.mem_range.1 hi).le).1
        (t_mem p (Finset.mem_range.1 hi)).2)).integrable one_le_two
  have hfi : ∀ i ∈ Finset.range p.n, Integrable (f i) P := fun i hi =>
    (hI i hi).bdd_mul (hY.measurable (t_mem p (Finset.mem_range.1 hi).le)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact hY.bound _ (t_mem p (Finset.mem_range.1 hi).le) ω)
  have hterm : ∀ i ∈ Finset.range p.n, P[f i | 𝓕 s] =ᵐ[P] 0 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hm := t_mem p hi'.le
    have h1 := condExp_condExp_of_le (μ := P) (f := f i) (𝓕.mono hm.1) (𝓕.le (p.t i))
    have h2 := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := 𝓕 (p.t i))
      (hY.adapted _ hm) (hfi i hi) (hI i hi)
    have h3 := condExp_itoInt_ms hB hW h𝓕 (hs.trans hm.1) (hH.mono hm.1 (t_mem p hi').2)
    have h4 : P[f i | 𝓕 (p.t i)] =ᵐ[P] 0 := by
      filter_upwards [h2, h3] with ω h2 h3
      change P[(fun ω => Y (p.t i) ω) * itoInt P 𝓕 W H (p.t i) (p.t (i + 1)) | 𝓕 (p.t i)] ω = 0
      rw [h2, Pi.mul_apply, h3]
      simp
    refine h1.symm.trans ?_
    filter_upwards [condExp_congr_ae (m := 𝓕 s) h4] with ω h
    rw [h, condExp_zero]
  have e : (fun ω => ∑ i ∈ Finset.range p.n, Y (p.t i) ω *
      itoInt P 𝓕 W H (p.t i) (p.t (i + 1)) ω) = ∑ i ∈ Finset.range p.n, f i := by
    funext ω
    simp [hf, Finset.sum_apply]
  rw [e]
  refine (condExp_finsetSum hfi (𝓕 s)).trans ?_
  have hall : ∀ᵐ ω ∂P, ∀ i, i ∈ Finset.range p.n → P[f i | 𝓕 s] ω = 0 := by
    refine ae_all_iff.2 fun i => ?_
    by_cases hi : i ∈ Finset.range p.n
    · filter_upwards [hterm i hi] with ω h _
      exact h
    · exact ae_of_all _ fun ω h => absurd h hi
  filter_upwards [hall] with ω hω
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero hω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `Z_k − (L + V_k) → 0` in `L¹` and `E_s[V_k] = 0`
for every `k`, then `E_s[Z_k] → E_s[L]` in `L¹`.
Generalises `TidyR7ItoProductRule.tendsto_integral_abs_condExp` (one fixed `V`). -/
theorem tendsto_integral_abs_condExp_var [IsProbabilityMeasure P] {m : MeasurableSpace Ω}
    {Z V : ℕ → Ω → ℝ} {L : Ω → ℝ} (hZ : ∀ k, Integrable (Z k) P) (hL : Integrable L P)
    (hV : ∀ k, Integrable (V k) P) (hV0 : ∀ k, P[V k | m] =ᵐ[P] 0)
    (h : Tendsto (fun k => ∫ ω, |Z k ω - (L ω + V k ω)| ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |P[Z k | m] ω - P[L | m] ω| ∂P) atTop (𝓝 0) := by
  refine squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) h
  have e : (fun ω => |P[Z k | m] ω - P[L | m] ω|) =ᵐ[P]
      fun ω => |P[fun ω => Z k ω - (L ω + V k ω) | m] ω| := by
    have hsub := condExp_sub (m := m) (hZ k) (hL.add (hV k))
    have hadd := condExp_add (m := m) hL (hV k)
    filter_upwards [hsub, hadd, hV0 k] with ω h1 h2 h3
    change |P[Z k | m] ω - P[L | m] ω| = |P[Z k - (L + V k) | m] ω|
    rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3]
    simp
  rw [integral_congr_ae e]
  exact integral_abs_condExp_le _

/-! ## The conditional product rule -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the conditional product rule with an unbounded
`X`.** Let `X` be an Itô process with mean-square continuous coefficients (drift `a`, diffusion
`H`) and `Y` an Itô process with bounded coefficients (drift `b`, diffusion `K`) whose values are
bounded with a.s. continuous paths, on `[s, t]`, `0 ≤ s < t`. Then a.s.
`E_s[X_tY_t − X_sY_s] = E_s[∫_s^t X b du + ∫_s^t Y a du + ∫_s^t H K du]`:
`E_t d(XY) = X E_t dY + Y E_t dX + E_t d[X, Y]` with `d[X, Y] = HK dt`.
Generalises `TidyR7ItoProductRule.condExp_product_rule` (both bounded). -/
theorem condExp_product_rule_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X Y a b H K : ℝ → Ω → ℝ}
    {Cb CK CY : ℝ} (hX : ItoProcessMS P 𝓕 W X a H s t) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (hYb : ItoIntegrand P 𝓕 Y s t CY) :
    P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω
        + dtInt P 𝓕 (fun u ω => H u ω * K u ω) s t ω | 𝓕 s] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set ps : ℕ → Partition s t := fun k => dyadic hst k with hps_def
  have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := tendsto_mesh_dyadic hst
  have hXms := hX.toMS hB hW h𝓕 hs
  have G1 := MSIntegrand.mul_itoIntegrand hXms hY.drift
  have G2 := msIntegrand_itoIntegrand_mul hYb hX.drift
  have G3 := MSIntegrand.mul_itoIntegrand hX.diff hY.diff
  have G4 := MSIntegrand.mul_itoIntegrand hXms hY.diff
  set d1 := dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t with hd1
  set d2 := dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t with hd2
  set d3 := dtInt P 𝓕 (fun u ω => H u ω * K u ω) s t with hd3
  set I1 := itoInt P 𝓕 W (fun u ω => X u ω * K u ω) s t with hI1
  set Z : Ω → ℝ := fun ω => X t ω * Y t ω - X s ω * Y s ω with hZ
  set L : Ω → ℝ := fun ω => d1 ω + d2 ω + d3 ω with hL
  set SI : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (ps k).n,
    Y ((ps k).t i) ω * itoInt P 𝓕 W H ((ps k).t i) ((ps k).t (i + 1)) ω with hSI
  set SA : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (ps k).n,
    Y ((ps k).t i) ω * dtInt P 𝓕 a ((ps k).t i) ((ps k).t (i + 1)) ω with hSA
  set V : ℕ → Ω → ℝ := fun k ω => I1 ω + SI k ω with hV
  -- integrability
  have iZ : Integrable Z P :=
    ((hX.memLp hB hW h𝓕 hs ⟨hst.le, le_rfl⟩).integrable_mul (hY.memLp hB hW h𝓕 hs
      ⟨hst.le, le_rfl⟩)).sub ((hX.memLp hB hW h𝓕 hs ⟨le_rfl, hst.le⟩).integrable_mul
        (hY.memLp hB hW h𝓕 hs ⟨le_rfl, hst.le⟩))
  have iL : Integrable L P :=
    (((memLp_dtInt G1).integrable one_le_two).add ((memLp_dtInt G2).integrable one_le_two)).add
      ((memLp_dtInt G3).integrable one_le_two)
  have iI1 : Integrable I1 P := (memLp_itoInt_ms hB hW h𝓕 hs G4).integrable one_le_two
  have iSI : ∀ k, Integrable (SI k) P := fun k => integrable_finsetSum _ fun i hi =>
    ((memLp_itoInt_ms hB hW h𝓕 (hs.trans (t_mem _ (Finset.mem_range.1 hi).le).1)
      (hX.diff.mono (t_mem _ (Finset.mem_range.1 hi).le).1
        (t_mem _ (Finset.mem_range.1 hi)).2)).integrable one_le_two).bdd_mul
      (hYb.measurable (t_mem _ (Finset.mem_range.1 hi).le)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact hYb.bound _ (t_mem _ (Finset.mem_range.1 hi).le) ω)
  have iV : ∀ k, Integrable (V k) P := fun k => iI1.add (iSI k)
  have hV0 : ∀ k, P[V k | 𝓕 s] =ᵐ[P] 0 := by
    intro k
    filter_upwards [condExp_add (m := 𝓕 s) iI1 (iSI k), condExp_itoInt_ms hB hW h𝓕 hs G4,
      condExp_sum_mul_itoInt_ms hB hW h𝓕 hs hX.diff hYb (ps k)] with ω h1 h2 h3
    change P[I1 + SI k | 𝓕 s] ω = 0
    rw [h1, Pi.add_apply, h2]
    have h3' : P[SI k | 𝓕 s] ω = 0 := h3
    rw [h3']
    simp
  -- the decomposition
  have hdec : ∀ k, (fun ω => Z ω - (L ω + V k ω)) =ᵐ[P] fun ω =>
      (sumRS (ps k) X Y ω - (d1 ω + I1 ω)) + (SA k ω - d2 ω)
        + (sumCross (ps k) X Y ω - d3 ω) := by
    intro k
    set p := ps k
    have hall : ∀ᵐ ω ∂P, ∀ i, i < p.n → X (p.t (i + 1)) ω - X (p.t i) ω
        = dtInt P 𝓕 a (p.t i) (p.t (i + 1)) ω + itoInt P 𝓕 W H (p.t i) (p.t (i + 1)) ω := by
      refine ae_all_iff.2 fun i => ?_
      by_cases hi : i < p.n
      · filter_upwards [hX.incr_eq hB hW h𝓕 hs (t_mem p hi.le).1 (t_le_succ p i)
          (t_mem p hi).2] with ω h _
        exact h
      · exact ae_of_all _ fun ω h => absurd h hi
    filter_upwards [hall] with ω hω
    have hid := prod_partition_identity p (fun u => X u ω) (fun u => Y u ω)
    have hYX : sumRS p Y X ω = SA k ω + SI k ω := by
      simp only [sumRS, rsSum, hSA, hSI, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hω i (Finset.mem_range.1 hi)]
      ring
    have e1 : Z ω = sumRS p X Y ω + sumRS p Y X ω + sumCross p X Y ω := hid
    rw [e1, hYX]
    simp only [hL, hV]
    ring
  -- the three limits
  have T1 := tendsto_integral_abs_of_L2Tendsto (L2Tendsto_sumRS hB hW h𝓕 hs hst hXms hY ps hps)
  have T2 := tendsto_integral_abs_of_L2Tendsto (L2Tendsto_sumYA hst hYb hX.drift ps hps)
  have T3 := tendsto_integral_abs_sumCross_ms hB hW h𝓕 hs hst hX hY ps hps
  have m1 : ∀ k, Integrable (fun ω => sumRS (ps k) X Y ω - (d1 ω + I1 ω)) P := fun k =>
    (((L2Tendsto_sumRS hB hW h𝓕 hs hst hXms hY ps hps).1 k).sub
      (L2Tendsto_sumRS hB hW h𝓕 hs hst hXms hY ps hps).2.1).integrable one_le_two
  have m2 : ∀ k, Integrable (fun ω => SA k ω - d2 ω) P := fun k =>
    (((L2Tendsto_sumYA hst hYb hX.drift ps hps).1 k).sub
      (L2Tendsto_sumYA hst hYb hX.drift ps hps).2.1).integrable one_le_two
  have m3 : ∀ k, Integrable (fun ω => sumCross (ps k) X Y ω - d3 ω) P := fun k =>
    (integrable_finsetSum _ fun i hi =>
      ((hX.memLp hB hW h𝓕 hs (t_mem _ (Finset.mem_range.1 hi))).sub
        (hX.memLp hB hW h𝓕 hs (t_mem _ (Finset.mem_range.1 hi).le))).integrable_mul
      ((hY.memLp hB hW h𝓕 hs (t_mem _ (Finset.mem_range.1 hi))).sub
        (hY.memLp hB hW h𝓕 hs (t_mem _ (Finset.mem_range.1 hi).le)))).sub
      ((memLp_dtInt G3).integrable one_le_two)
  have hT : Tendsto (fun k => ∫ ω, |Z ω - (L ω + V k ω)| ∂P) atTop (𝓝 0) := by
    have hsum := (T1.add T2).add T3
    simp only [add_zero] at hsum
    refine squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) hsum
    have e : ∫ ω, |Z ω - (L ω + V k ω)| ∂P = ∫ ω, |(sumRS (ps k) X Y ω - (d1 ω + I1 ω))
        + (SA k ω - d2 ω) + (sumCross (ps k) X Y ω - d3 ω)| ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hdec k] with ω h
      rw [h]
    rw [e]
    have j1 : Integrable (fun ω => |sumRS (ps k) X Y ω - (d1 ω + I1 ω)|) P := (m1 k).abs
    have j2 : Integrable (fun ω => |SA k ω - d2 ω|) P := (m2 k).abs
    have j3 : Integrable (fun ω => |sumCross (ps k) X Y ω - d3 ω|) P := (m3 k).abs
    have hle : ∫ ω, |(sumRS (ps k) X Y ω - (d1 ω + I1 ω)) + (SA k ω - d2 ω)
        + (sumCross (ps k) X Y ω - d3 ω)| ∂P
        ≤ ∫ ω, |sumRS (ps k) X Y ω - (d1 ω + I1 ω)| ∂P + ∫ ω, |SA k ω - d2 ω| ∂P
          + ∫ ω, |sumCross (ps k) X Y ω - d3 ω| ∂P := by
      have j12 : Integrable (fun ω => |sumRS (ps k) X Y ω - (d1 ω + I1 ω)|
          + |SA k ω - d2 ω|) P := j1.add j2
      rw [← integral_add j1 j2, ← integral_add j12 j3]
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (j12.add j3)
        (ae_of_all _ fun ω => ?_)
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    exact hle
  have hc := tendsto_integral_abs_condExp_var (m := 𝓕 s) (Z := fun _ => Z) (fun _ => iZ) iL iV
    hV0 hT
  have h0 : ∫ ω, |P[Z | 𝓕 s] ω - P[L | 𝓕 s] ω| ∂P = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hc
  have hint : Integrable (fun ω => |P[Z | 𝓕 s] ω - P[L | 𝓕 s] ω|) P :=
    (integrable_condExp.sub integrable_condExp).abs
  have hz := (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hint).1 h0
  filter_upwards [hz] with ω hω
  have : |P[Z | 𝓕 s] ω - P[L | 𝓕 s] ω| = 0 := hω
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the bracket-free (book) form with an unbounded
`X`.** In the setting of `condExp_product_rule_ms`,
`E_s[X_tY_t − X_sY_s] = E_s[∫ X b du + ∫ Y a du]` a.s. **iff** `E_s[∫_s^t H K du] = 0` a.s.
Generalises `TidyR7ItoProductRule.condExp_product_rule_bookForm_iff`. -/
theorem condExp_product_rule_ms_bookForm_iff (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    {X Y a b H K : ℝ → Ω → ℝ} {Cb CK CY : ℝ} (hX : ItoProcessMS P 𝓕 W X a H s t)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (hYb : ItoIntegrand P 𝓕 Y s t CY) :
    (P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω | 𝓕 s]) ↔
      P[dtInt P 𝓕 (fun u ω => H u ω * K u ω) s t | 𝓕 s] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hXms := hX.toMS hB hW h𝓕 hs
  have iF : Integrable (fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
      + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω) P :=
    ((memLp_dtInt (MSIntegrand.mul_itoIntegrand hXms hY.drift)).integrable one_le_two).add
      ((memLp_dtInt (msIntegrand_itoIntegrand_mul hYb hX.drift)).integrable one_le_two)
  have iQ : Integrable (dtInt P 𝓕 (fun u ω => H u ω * K u ω) s t) P :=
    (memLp_dtInt (MSIntegrand.mul_itoIntegrand hX.diff hY.diff)).integrable one_le_two
  have hmain := (condExp_product_rule_ms hB hW h𝓕 hs hst hX hY hYb).trans
    (condExp_add iF iQ (𝓕 s))
  constructor
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    rw [h1, Pi.add_apply] at h2
    simp only [Pi.zero_apply]
    linarith
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    rw [h1, Pi.add_apply, h2]
    simp

end Cochrane.Monetarism.TidyR12SDEProductRule
