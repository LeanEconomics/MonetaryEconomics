/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEProcess
import Monetarism.TidyR12SDEGauss

/-!
# The bracket `d[X, Y] = HK dt` for an Itô process with unbounded coefficients

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eq. (1.32) (Track 3, chunk B4). I5d proved
`Σ ΔX_iΔY_i → ∫ H K du` in `L¹` for two Itô processes with bounded coefficients
(`TidyR7ItoCovariation.tendsto_integral_abs_sumCross`). Here `X` is an Itô process with
mean-square continuous coefficients (`TidyR12SDEProcess.ItoProcessMS`, drift `a`, diffusion `H`,
e.g. geometric Brownian motion `Λ/P`) and `Y` an Itô process with bounded coefficients (drift
`b`, diffusion `K`, e.g. bonds). The proof is I5d's: the cell split
`ΔXΔY = H_{t_i}K_{t_i}ΔW_i² + A_iΔY_i + (B_i + S_i)H_{t_i}ΔW_i + R_iΔY_i`, with the boundedness of
`a, H` replaced by the mean-square bounds `sup E[a²], sup E[H²] < ∞` and mean-square continuity
(I5d used the bounds only for integrability and these sums).

## Main results

* `itoInt_const_ms`, `dtInt_const`: `∫_a^b Z dW = Z(W_b − W_a)` and `∫_a^b Z du = (b − a)Z` for a
  square-integrable `𝓕_a`-measurable `Z`.
* `ItoProcessMS.incr_decomp`: `X_v − X_u = ∫_u^v a + H_u(W_v − W_u) + ∫_u^v (H − H_u) dW`.
* `tendsto_sum_integral_dtInt_sq`, `tendsto_sum_integral_itoInt_sub_sq_ms`,
  `sum_integral_mul_incr_sq_le_ms`, `tendsto_integral_wqvSum_sq_ms`: the four sums.
* **`tendsto_integral_abs_sumCross_ms`**: `Σ ΔX_iΔY_i → ∫_s^t H_uK_u du` (mean-square time
  integral) in `L¹`.
-/

namespace Cochrane.Monetarism.TidyR12SDEBracket

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoCovariation
  Cochrane.Monetarism.TidyR7ItoProductRule Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR12SDETools Cochrane.Monetarism.TidyR12SDEProcess
  Cochrane.Monetarism.TidyR12SDEGauss
open Cochrane.Monetarism.TidyR7ProductStep (sumRS sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s t : ℝ}

/-! ## Constant integrands -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`∫_a^b Z dW = Z(W_b − W_a)`** for a
square-integrable `𝓕_a`-measurable `Z`, `0 ≤ a ≤ b`.
Generalises `TidyR7ItoIntegral.itoInt_const` (bounded `Z`). -/
theorem itoInt_const_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 a] Z) (hZ2 : MemLp Z 2 P) :
    itoInt P 𝓕 W (fun _ => Z) a b =ᵐ[P] fun ω => Z ω * incr W a b ω := by
  rcases hab.lt_or_eq with hab | hab
  · have h1 := L2Tendsto_dyadic_ms hB hW h𝓕 ha hab (msIntegrand_const (t := b) hZ hZ2)
    have hm : MemLp (fun ω => Z ω * incr W a b ω) 2 P :=
      memLp_mul_incr_of_memLp hB hW h𝓕 hab.le hZ hZ2
    have h2 : L2Tendsto P (fun k => itoSum W (fun _ => Z) (dyadic hab k))
        (fun ω => Z ω * incr W a b ω) :=
      ⟨fun k => by
        have e : itoSum W (fun _ => Z) (dyadic hab k) = fun ω => Z ω * incr W a b ω :=
          funext fun ω => itoSum_const Z _ ω
        beta_reduce
        rw [e]
        exact hm, hm, by simp [itoSum_const]⟩
    exact ae_eq_of_L2Tendsto h1 h2
  · subst hab
    rw [itoInt_of_le le_rfl]
    exact ae_of_all _ fun ω => by simp [incr_self]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`∫_a^b Z du = (b − a)Z`** for a square-integrable
`𝓕_a`-measurable `Z`, `a ≤ b`. -/
theorem dtInt_const {a b : ℝ} (hab : a ≤ b) {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 a] Z)
    (hZ2 : MemLp Z 2 P) : dtInt P 𝓕 (fun _ => Z) a b =ᵐ[P] fun ω => (b - a) * Z ω := by
  rcases hab.lt_or_eq with hab | hab
  · have h1 := L2Tendsto_dyadic_dt hab (msIntegrand_const (P := P) (t := b) hZ hZ2)
    have hm : MemLp (fun ω => (b - a) * Z ω) 2 P := hZ2.const_mul _
    have e : ∀ k, dtSum (fun _ => Z) (dyadic hab k) = fun ω => (b - a) * Z ω := fun k =>
      funext fun ω => by
        simp only [dtSum, riemannSum, ← Finset.mul_sum, sum_step_eq]
        ring
    have h2 : L2Tendsto P (fun k => dtSum (fun _ => Z) (dyadic hab k))
        (fun ω => (b - a) * Z ω) := ⟨fun k => by beta_reduce; rw [e k]; exact hm, hm, by simp [e]⟩
    exact ae_eq_of_L2Tendsto h1 h2
  · subst hab
    rw [dtInt_of_le le_rfl]
    exact ae_of_all _ fun ω => by simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the cell decomposition of an `ItoProcessMS`**: for
`s ≤ u ≤ v ≤ t`, `0 ≤ s`, a.s.
`X_v − X_u = ∫_u^v a + (H_u(W_v − W_u) + ∫_u^v (H − H_u) dW)`.
The analogue of `TidyR7ItoProcess.ItoProcess.incr_decomp`. -/
theorem ItoProcessMS.incr_decomp {X a H : ℝ → Ω → ℝ} (hX : ItoProcessMS P 𝓕 W X a H s t)
    (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hs : 0 ≤ s) {u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    (fun ω => X v ω - X u ω) =ᵐ[P] fun ω => dtInt P 𝓕 a u v ω
      + (H u ω * incr W u v ω + itoInt P 𝓕 W (fun r ω => H r ω - H u ω) u v ω) := by
  have hHuv : MSIntegrand P 𝓕 H u v := hX.diff.mono hsu hvt
  have hHu := hHuv.adapted u ⟨le_rfl, huv⟩
  have hHu2 := hHuv.memLp u ⟨le_rfl, huv⟩
  have hc : MSIntegrand P 𝓕 (fun _ => H u) u v := msIntegrand_const hHu hHu2
  have hd : MSIntegrand P 𝓕 (fun r ω => H r ω - H u ω) u v := MSIntegrand.sub hHuv hc
  have hadd := itoInt_add_ms hB hW h𝓕 (hs.trans hsu) hc hd
  have e : (fun r ω => (fun _ => H u) r ω + (fun r ω => H r ω - H u ω) r ω) = H :=
    funext fun r => funext fun ω => by simp
  rw [e] at hadd
  filter_upwards [hX.incr_eq hB hW h𝓕 hs hsu huv hvt, hadd,
    itoInt_const_ms hB hW h𝓕 (hs.trans hsu) huv hHu hHu2] with ω h1 h2 h3
  rw [h1, h2, h3]

/-! ## The four sums -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ_i E[(∫_{t_i}^{t_{i+1}} a du)²] → 0` along
partitions with mesh `→ 0`, for `a` mean-square continuous on `[s, t]`. -/
theorem tendsto_sum_integral_dtInt_sq [IsProbabilityMeasure P] {a : ℝ → Ω → ℝ}
    (ha : MSIntegrand P 𝓕 a s t) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
      ∫ ω, dtInt P 𝓕 a ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_integral_sq_ms ha
  have hle : ∀ k, ∑ i ∈ Finset.range (ps k).n,
      ∫ ω, dtInt P 𝓕 a ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2 ∂P
        ≤ M * (mesh (ps k) * (t - s)) := by
    intro k
    set p := ps k
    refine (Finset.sum_le_sum (g := fun i => M * mesh p * (p.t (i + 1) - p.t i))
      fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p]; ring)
    have hi' := Finset.mem_range.1 hi
    have h1 := integral_dtInt_sq_le_const (t_le_succ p i)
      (ha.mono (t_mem p hi'.le).1 (t_mem p hi').2) (M := M)
      fun u hu => hM u ⟨(t_mem p hi'.le).1.trans hu.1, hu.2.trans (t_mem p hi').2⟩
    have h2 := le_mesh p hi'
    have h3 := step_pos p i
    have h6 : (p.t (i + 1) - p.t i) ^ 2 ≤ mesh p * (p.t (i + 1) - p.t i) := by nlinarith
    calc ∫ ω, dtInt P 𝓕 a (p.t i) (p.t (i + 1)) ω ^ 2 ∂P ≤ (p.t (i + 1) - p.t i) ^ 2 * M := h1
      _ ≤ (mesh p * (p.t (i + 1) - p.t i)) * M := mul_le_mul_of_nonneg_right h6 hM0
      _ = M * mesh p * (p.t (i + 1) - p.t i) := by ring
  have hts : 0 ≤ t - s := sub_nonneg.2 (a_le_b (ps 0))
  refine squeeze_zero (fun k => Finset.sum_nonneg fun i _ => integral_nonneg fun _ =>
    sq_nonneg _) hle ?_
  simpa using (hps.mul_const (t - s)).const_mul M

/-- Cochrane (2023), A1 §1.6, pp. 567–568: along partitions with mesh `→ 0`,
`Σ_i E[(∫_{t_i}^{t_{i+1}} (H − H_{t_i}) dW)²] → 0` for `H` mean-square continuous, `0 ≤ s`.
Generalises `TidyR7ItoCovariation.tendsto_sum_integral_itoInt_sub_sq` (bounded `H`). -/
theorem tendsto_sum_integral_itoInt_sub_sq_ms (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : MSIntegrand P 𝓕 H s t) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n, ∫ ω, itoInt P 𝓕 W
      (fun r ω => H r ω - H ((ps k).t i) ω) ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2 ∂P) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hts0 : 0 ≤ t - s := sub_nonneg.2 (a_le_b (ps 0))
  obtain ⟨δ, hδ, hδH⟩ := hH.cont (η / (2 * (t - s + 1))) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun k hk => ?_⟩
  set p := ps k with hp
  have hle : ∑ i ∈ Finset.range p.n, ∫ ω, itoInt P 𝓕 W (fun r ω => H r ω - H (p.t i) ω)
      (p.t i) (p.t (i + 1)) ω ^ 2 ∂P ≤ η / (2 * (t - s + 1)) * (t - s) := by
    refine (Finset.sum_le_sum (g := fun i => η / (2 * (t - s + 1)) * (p.t (i + 1) - p.t i))
      fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p])
    have hi' := Finset.mem_range.1 hi
    have hHi : MSIntegrand P 𝓕 H (p.t i) (p.t (i + 1)) :=
      hH.mono (t_mem p hi'.le).1 (t_mem p hi').2
    have hci : MSIntegrand P 𝓕 (fun _ => H (p.t i)) (p.t i) (p.t (i + 1)) :=
      msIntegrand_const (hHi.adapted _ ⟨le_rfl, t_le_succ p i⟩)
        (hHi.memLp _ ⟨le_rfl, t_le_succ p i⟩)
    refine integral_itoInt_sq_le_ms hB hW h𝓕 (hs.trans (t_mem p hi'.le).1) (t_le_succ p i)
      (MSIntegrand.sub hHi hci) fun r hr => ?_
    have hr' : r ∈ Set.Icc s t := ⟨(t_mem p hi'.le).1.trans hr.1, hr.2.trans (t_mem p hi').2⟩
    exact hδH r hr' _ (t_mem p hi'.le) (by
      rw [abs_of_nonneg (sub_nonneg.2 hr.1)]
      exact ((sub_le_sub_right hr.2 _).trans (le_mesh p hi')).trans (hN k hk))
  have h2 : η / (2 * (t - s + 1)) * (t - s) < η := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun i _ => integral_nonneg
    fun _ => sq_nonneg _)]
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ_i E[(H_{t_i}ΔW_i)²] ≤ M(t − s)` when `E[H_u²] ≤ M`
on `[s, t]`, `0 ≤ s`.
Generalises `TidyR7ItoCovariation.sum_integral_mul_incr_sq_le` (bounded `H`). -/
theorem sum_integral_mul_incr_sq_le_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} (hH : MSIntegrand P 𝓕 H s t)
    {M : ℝ} (hM : ∀ u ∈ Set.Icc s t, ∫ ω, H u ω ^ 2 ∂P ≤ M) (p : Partition s t) :
    ∑ i ∈ Finset.range p.n, ∫ ω, (H (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω) ^ 2 ∂P
      ≤ M * (t - s) := by
  refine (Finset.sum_le_sum (g := fun i => M * (p.t (i + 1) - p.t i))
    fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p])
  have hm := t_mem p (Finset.mem_range.1 hi).le
  have e : ∫ ω, (H (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω) ^ 2 ∂P
      = (p.t (i + 1) - p.t i) * ∫ ω, H (p.t i) ω ^ 2 ∂P := by
    have hY : StronglyMeasurable[𝓕 (p.t i)] (fun ω => H (p.t i) ω ^ 2) := (hH.adapted _ hm).pow 2
    rw [← integral_mul_incr_sq hB hW h𝓕 (hs.trans hm.1) (t_le_succ p i) hY]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  rw [e, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM _ hm) (step_pos p i).le

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the centred `(dW)²` sum vanishes in mean square
for a mean-square continuous weight**: `E[(Σ G_{t_i}((ΔW_i)² − Δt_i))²] → 0` along partitions
with mesh `→ 0`, `0 ≤ s` (orthogonal increments, `E[((ΔW)² − Δt)²] = 2Δt²`).
Generalises `TidyR7BrownianQV.tendsto_integral_wqvSum_sq` (bounded weight). -/
theorem tendsto_integral_wqvSum_sq_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, wqvSum W G (ps k) ω ^ 2 ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := exists_bound_integral_sq_ms hG
  have hle : ∀ k, ∫ ω, wqvSum W G (ps k) ω ^ 2 ∂P ≤ 2 * M * (mesh (ps k) * (t - s)) := by
    intro k
    set p := ps k
    have hV2 : ∀ i < p.n, MemLp (fun ω => G (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) 2 P :=
      fun i hi => memLp_mul_fun_incr hW h𝓕 (t_le_succ p i) (hG.adapted _ (t_mem p hi.le))
        (hG.memLp _ (t_mem p hi.le)) (φ := fun z => z ^ 2 - (p.t (i + 1) - p.t i))
        ((measurable_id.pow_const 2).sub_const _) (memLp_qvTerm hB hW _ _)
    have hVm : ∀ i < p.n, StronglyMeasurable[𝓕 (p.t (i + 1))]
        (fun ω => G (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) := fun i hi =>
      ((hG.adapted _ (t_mem p hi.le)).mono (𝓕.mono (t_le_succ p i))).mul
        (stronglyMeasurable_qvTerm h𝓕 (t_le_succ p i))
    have horth : ∀ i < p.n, ∀ Z : Ω → ℝ, StronglyMeasurable[𝓕 (p.t i)] Z → MemLp Z 2 P →
        ∫ ω, Z ω * (G (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) ∂P = 0 := by
      intro i hi Z hZ _
      have h := integral_mul_qvTerm hB hW h𝓕 (hs.trans (t_mem p hi.le).1) (t_le_succ p i)
        (hZ.mul (hG.adapted _ (t_mem p hi.le)))
      rw [← h]
      exact integral_congr_ae (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)
    have hsum := integral_sum_sq_of_orth (P := P) (𝓕 := 𝓕) p.strictMono.monotone p.n hV2 hVm
      horth
    have e : (fun ω => wqvSum W G p ω ^ 2) = fun ω => (∑ i ∈ Finset.range p.n,
        G (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) ^ 2 := rfl
    rw [e, hsum]
    refine (Finset.sum_le_sum (g := fun i => 2 * M * mesh p * (p.t (i + 1) - p.t i))
      fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p]; ring)
    have hi' := Finset.mem_range.1 hi
    have hY : StronglyMeasurable[𝓕 (p.t i)] (fun ω => G (p.t i) ω ^ 2) :=
      (hG.adapted _ (t_mem p hi'.le)).pow 2
    have h1 := integral_mul_qvTerm_sq hB hW h𝓕 (hs.trans (t_mem p hi'.le).1) (t_le_succ p i) hY
    have e2 : ∫ ω, (G (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) ^ 2 ∂P
        = 2 * (p.t (i + 1) - p.t i) ^ 2 * ∫ ω, G (p.t i) ω ^ 2 ∂P := by
      rw [← h1]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [e2]
    have h2 := le_mesh p hi'
    have h3 := step_pos p i
    have h4 := hM _ (t_mem p hi'.le)
    have h5 : 0 ≤ ∫ ω, G (p.t i) ω ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have h6 : (p.t (i + 1) - p.t i) ^ 2 ≤ mesh p * (p.t (i + 1) - p.t i) := by nlinarith
    calc 2 * (p.t (i + 1) - p.t i) ^ 2 * ∫ ω, G (p.t i) ω ^ 2 ∂P
        ≤ 2 * (mesh p * (p.t (i + 1) - p.t i)) * M :=
          mul_le_mul (by linarith) h4 h5 (mul_nonneg zero_le_two (mul_nonneg (mesh_nonneg p) h3.le))
      _ = 2 * M * mesh p * (p.t (i + 1) - p.t i) := by ring
  refine squeeze_zero (fun k => integral_nonneg fun _ => sq_nonneg _) hle ?_
  simpa using (hps.mul_const (t - s)).const_mul (2 * M)

/-! ## The bracket -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the bracket `d[X, Y] = HK dt` with unbounded
coefficients): `Σ (X_{t_{i+1}} − X_{t_i})(Y_{t_{i+1}} − Y_{t_i}) → ∫_s^t H_uK_u du` in `L¹`**
along any partitions with mesh `→ 0`, for `X` an Itô process with mean-square continuous
coefficients (drift `a`, diffusion `H`) and `Y` an Itô process with bounded coefficients (drift
`b`, diffusion `K`), `0 ≤ s < t`; the limit is the mean-square time integral.
Generalises `TidyR7ItoCovariation.tendsto_integral_abs_sumCross` (both bounded). -/
theorem tendsto_integral_abs_sumCross_ms (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    {X Y a b H K : ℝ → Ω → ℝ} {Cb CK : ℝ} (hX : ItoProcessMS P 𝓕 W X a H s t)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |sumCross (ps k) X Y ω
      - dtInt P 𝓕 (fun u ω => H u ω * K u ω) s t ω| ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set HK : ℝ → Ω → ℝ := fun u ω => H u ω * K u ω with hHK
  have hHKm : MSIntegrand P 𝓕 HK s t := MSIntegrand.mul_itoIntegrand hX.diff hY.diff
  obtain ⟨MH, hMH0, hMH⟩ := exists_bound_integral_sq_ms hX.diff
  -- the pieces
  set A : ℕ → ℕ → Ω → ℝ := fun k i => dtInt P 𝓕 a ((ps k).t i) ((ps k).t (i + 1)) with hA
  set Bt : ℕ → ℕ → Ω → ℝ := fun k i ω => ∫ r in (ps k).t i..(ps k).t (i + 1), b r ω with hBt
  set R : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W (fun r ω => H r ω - H ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hR
  set S : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W (fun r ω => K r ω - K ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hS
  set β : ℕ → ℕ → Ω → ℝ := fun k i ω => H ((ps k).t i) ω * incr W ((ps k).t i) ((ps k).t (i + 1)) ω
    with hβ
  set dY : ℕ → ℕ → Ω → ℝ := fun k i ω => Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω with hdY
  -- square integrability of the pieces
  have mA : ∀ k, ∀ i < (ps k).n, MemLp (A k i) 2 P := fun k i hi =>
    memLp_dtInt (hX.drift.mono (t_mem _ hi.le).1 (t_mem _ hi).2)
  have mB : ∀ k, ∀ i < (ps k).n, MemLp (Bt k i) 2 P := fun k i hi =>
    memLp_integral_drift hY.drift (t_mem _ hi.le).1 (t_le_succ _ i) (t_mem _ hi).2
  have mR : ∀ k, ∀ i < (ps k).n, MemLp (R k i) 2 P := fun k i hi => by
    have hHi := hX.diff.mono (t_mem (ps k) hi.le).1 (t_mem (ps k) hi).2
    exact memLp_itoInt_ms hB hW h𝓕 (hs.trans (t_mem _ hi.le).1) (MSIntegrand.sub hHi
      (msIntegrand_const (hHi.adapted _ ⟨le_rfl, t_le_succ _ i⟩)
        (hHi.memLp _ ⟨le_rfl, t_le_succ _ i⟩)))
  have mS : ∀ k, ∀ i < (ps k).n, MemLp (S k i) 2 P := fun k i hi =>
    memLp_itoInt hB hW h𝓕 (hs.trans (t_mem _ hi.le).1) (itoIntegrand_sub_left (t_le_succ _ i)
      (hY.diff.mono (t_mem _ hi.le).1 (t_mem _ hi).2))
  have mβ : ∀ k, ∀ i < (ps k).n, MemLp (β k i) 2 P := fun k i hi =>
    memLp_mul_incr_of_memLp hB hW h𝓕 (t_le_succ _ i) (hX.diff.adapted _ (t_mem _ hi.le))
      (hX.diff.memLp _ (t_mem _ hi.le))
  have mdY : ∀ k, ∀ i < (ps k).n, MemLp (dY k i) 2 P := fun k i hi =>
    (hY.memLp hB hW h𝓕 hs (t_mem _ hi)).sub (hY.memLp hB hW h𝓕 hs (t_mem _ hi.le))
  have mBS : ∀ k, ∀ i < (ps k).n, MemLp (fun ω => Bt k i ω + S k i ω) 2 P := fun k i hi =>
    (mB k i hi).add (mS k i hi)
  have mw : ∀ k, MemLp (wqvSum W HK (ps k)) 2 P := fun k =>
    memLp_finsetSum _ fun i hi => memLp_mul_fun_incr hW h𝓕 (t_le_succ _ i)
      (hHKm.adapted _ (t_mem _ (Finset.mem_range.1 hi).le))
      (hHKm.memLp _ (t_mem _ (Finset.mem_range.1 hi).le))
      (φ := fun z => z ^ 2 - ((ps k).t (i + 1) - (ps k).t i))
      ((measurable_id.pow_const 2).sub_const _) (memLp_qvTerm hB hW _ _)
  have mr : ∀ k, MemLp (fun ω => dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω) 2 P := fun k =>
    (memLp_dtSum hHKm.memLp _).sub (memLp_dtInt hHKm)
  -- the pathwise split
  have hsplit : ∀ k, (fun ω => sumCross (ps k) X Y ω - dtInt P 𝓕 HK s t ω) =ᵐ[P] fun ω =>
      wqvSum W HK (ps k) ω + (dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω)
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω := by
    intro k
    have hall : ∀ᵐ ω ∂P, ∀ i, i < (ps k).n →
        (X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) * dY k i ω
          = HK ((ps k).t i) ω * incr W ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2
            + A k i ω * dY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * dY k i ω := by
      refine ae_all_iff.2 fun i => ?_
      by_cases hi : i < (ps k).n
      · have hm := t_mem (ps k) hi.le
        have hm' := t_mem (ps k) hi
        filter_upwards [ItoProcessMS.incr_decomp hX hB hW h𝓕 hs hm.1 (t_le_succ _ i) hm'.2,
          hY.incr_decomp hB hW h𝓕 hs hm.1 (t_le_succ _ i) hm'.2] with ω h1 h2 _
        simp only [hdY, hA, hBt, hR, hS, hβ, hHK]
        rw [h1, h2]
        ring
      · exact ae_of_all _ fun ω h => absurd h hi
    filter_upwards [hall] with ω hω
    rw [wqvSum_eq]
    simp only [sumCross, crossSum, dtSum, riemannSum]
    have e : ∑ i ∈ Finset.range (ps k).n, (X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) *
        (Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω)
        = ∑ i ∈ Finset.range (ps k).n, (HK ((ps k).t i) ω *
          incr W ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2
          + A k i ω * dY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * dY k i ω) :=
      Finset.sum_congr rfl fun i hi => hω i (Finset.mem_range.1 hi)
    rw [e, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  -- the five limits
  have hw : Tendsto (fun k => ∫ ω, |wqvSum W HK (ps k) ω| ∂P) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (c := 1) (fun k => by rw [one_mul]; exact sq_integral_abs_le (mw k))
      (tendsto_integral_wqvSum_sq_ms hB hW h𝓕 hs hHKm ps hps)
  have hr : Tendsto (fun k => ∫ ω, |dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω| ∂P) atTop (𝓝 0) :=
    tendsto_integral_abs_of_L2Tendsto (L2Tendsto_dtSum hst hHKm ps hps)
  have hp1 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mA mdY
    (tendsto_sum_integral_dtInt_sq hX.drift ps hps)
    (fun k => sum_integral_incr_sq_le hB hW h𝓕 hs hY (ps k))
  have hBS0 : Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
      ∫ ω, (Bt k i ω + S k i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hl := ((tendsto_sum_integral_drift_sq (P := P) hY.drift.bound ps hps).const_mul 2).add
      ((tendsto_sum_integral_itoInt_sub_sq hB hW h𝓕 hs hY.diff ps hps).const_mul 2)
    rw [mul_zero, add_zero] at hl
    refine squeeze_zero (fun k => Finset.sum_nonneg fun i _ => integral_nonneg fun _ =>
      sq_nonneg _) (fun k => ?_) hl
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((mB k i hi').integrable_sq.const_mul _) ((mS k i hi').integrable_sq.const_mul _)]
    exact integral_mono ((mBS k i hi').integrable_sq) (((mB k i hi').integrable_sq.const_mul
      _).add ((mS k i hi').integrable_sq.const_mul _)) fun ω => add_sq_le_two _ _
  have hp2 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n)
    (f := fun k i ω => Bt k i ω + S k i ω) mBS mβ hBS0
    (fun k => sum_integral_mul_incr_sq_le_ms hB hW h𝓕 hs hX.diff hMH (ps k))
  have hp3 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mR mdY
    (tendsto_sum_integral_itoInt_sub_sq_ms hB hW h𝓕 hs hX.diff ps hps)
    (fun k => sum_integral_incr_sq_le hB hW h𝓕 hs hY (ps k))
  -- integrability of the pieces, and the triangle inequality
  have iw : ∀ k, Integrable (fun ω => |wqvSum W HK (ps k) ω|) P := fun k =>
    ((mw k).integrable one_le_two).abs
  have ir : ∀ k, Integrable (fun ω => |dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω|) P := fun k =>
    ((mr k).integrable one_le_two).abs
  have isum : ∀ (k : ℕ) (f g : ℕ → Ω → ℝ), (∀ i < (ps k).n, MemLp (f i) 2 P) →
      (∀ i < (ps k).n, MemLp (g i) 2 P) →
      Integrable (fun ω => |∑ i ∈ Finset.range (ps k).n, f i ω * g i ω|) P :=
    fun k f g hf hg => (integrable_finsetSum _ fun i hi =>
      (hf i (Finset.mem_range.1 hi)).integrable_mul (hg i (Finset.mem_range.1 hi))).abs
  have hbound : ∀ k, ∫ ω, |sumCross (ps k) X Y ω - dtInt P 𝓕 HK s t ω| ∂P
      ≤ ∫ ω, |wqvSum W HK (ps k) ω| ∂P
        + ∫ ω, |dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω| ∂P := by
    intro k
    have i1 := isum k (A k) (dY k) (mA k) (mdY k)
    have i2 := isum k (fun i ω => Bt k i ω + S k i ω) (β k) (mBS k) (mβ k)
    have i3 := isum k (R k) (dY k) (mR k) (mdY k)
    have j2 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω|) P := (iw k).add (ir k)
    have j3 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|) P := j2.add i1
    have j4 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|) P := j3.add i2
    have j5 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |dtSum HK (ps k) ω - dtInt P 𝓕 HK s t ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|
        + |∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω|) P := j4.add i3
    rw [← integral_add (iw k) (ir k), ← integral_add j2 i1, ← integral_add j3 i2,
      ← integral_add j4 i3]
    rw [integral_congr_ae (g := fun ω => |wqvSum W HK (ps k) ω + (dtSum HK (ps k) ω
        - dtInt P 𝓕 HK s t ω)
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω|)
      (by filter_upwards [hsplit k] with ω hω; rw [hω])]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) j5
      (ae_of_all _ fun ω => ?_)
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have hlim := (((hw.add hr).add hp1).add hp2).add hp3
  simp only [add_zero] at hlim
  exact squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) hbound hlim

end Cochrane.Monetarism.TidyR12SDEBracket
