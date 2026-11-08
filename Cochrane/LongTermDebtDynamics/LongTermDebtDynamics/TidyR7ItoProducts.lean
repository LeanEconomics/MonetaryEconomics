/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7ItoUnbounded

/-!
# Products of integrands, `∫ cK dW = c ∫ K dW`, and the mean-square time integral

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5d): the terms `∫ X K dW` and `∫ X b du` of the product rule
`d(XY) = X dY + Y dX + d[X, Y]` when `X` is an Itô process, hence unbounded and without path
regularity.

## Main results

* `tendsto_integral_sq_mul_sq` (**the uniform-integrability step**): if `u ↦ X_u` is
  square-integrable and uniformly mean-square continuous on `[s, t]`, `u_k → a` in `[s, t]`, and
  `Z_k` are uniformly bounded with `Z_k → 0` a.s., then `E[X_{u_k}² Z_k²] → 0`.
* `exists_delta_integral_sq_mul_sub_sq_le`: for a bounded a.s.-continuous `K`,
  `E[X_v²(K_u − K_v)²] ≤ ε` once `|u − v| ≤ δ`.
* `MSIntegrand.mul_itoIntegrand`: `X·K` is a mean-square continuous integrand (so `∫ X K dW`
  exists, TidyR7ItoUnbounded).
* `itoInt_mul_left` (**`∫_r^t Z K dW = Z ∫_r^t K dW`** for square-integrable
  `𝓕_r`-measurable `Z`; it closes the I5c item "`∫cH dW = c∫H dW` for random
  `𝓕_s`-measurable `c`", for square-integrable `c`).
* The time integral in mean square: `dtSum` (left-point Riemann sums `Σ G_{t_i}Δt_i` as random
  variables), `dtInt P 𝓕 G s t` (a chosen `𝓕_t`-strongly measurable mean-square limit of the
  dyadic ones, hypothesis-free like `TidyR7ItoIntegral.itoInt`), `L2Tendsto_dtSum` (convergence
  along any partitions for mean-square continuous `G`), `dtInt_ae_eq_integral` (it is the pathwise
  `∫_s^t G_u du` whenever the paths are a.s. continuous), `dtInt_of_eq_zero`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7ItoProducts

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7StieltjesSums
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoL2
  Cochrane.LongTermDebtDynamics.TidyR7ItoSums Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoUnbounded
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s t : ℝ}

/-! ## The uniform-integrability step -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `x²z² ≤ 2C²(x − y)² + 2y²z²` when `z² ≤ C²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.sq_mul_sq_le). -/
lemma sq_mul_sq_le (x y z C : ℝ) (hz : z ^ 2 ≤ C ^ 2) :
    x ^ 2 * z ^ 2 ≤ 2 * C ^ 2 * (x - y) ^ 2 + 2 * (y ^ 2 * z ^ 2) := by
  have h1 : x ^ 2 ≤ 2 * (x - y) ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - 2 * y)]
  have h2 : (x - y) ^ 2 * z ^ 2 ≤ (x - y) ^ 2 * C ^ 2 :=
    mul_le_mul_of_nonneg_left hz (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg z)]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the uniform-integrability step.** Let `u ↦ X_u` be
square integrable and uniformly continuous in mean square on `[s, t]`, `u_k ∈ [s, t]` with
`u_k → a ∈ [s, t]`, and `Z_k` a.e.-strongly measurable with `|Z_k| ≤ C` and `Z_k → 0` a.s.
Then `E[X_{u_k}² Z_k²] → 0` (split `X_{u_k} = (X_{u_k} − X_a) + X_a`; the first part is small
in `L²`, the second by dominated convergence).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.tendsto_integral_sq_mul_sq). -/
theorem tendsto_integral_sq_mul_sq {X : ℝ → Ω → ℝ} (hX2 : ∀ u ∈ Set.Icc s t, MemLp (X u) 2 P)
    (hXc : MSUnifCont P X s t) {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Set.Icc s t) {a : ℝ}
    (ha : a ∈ Set.Icc s t) (hua : Tendsto u atTop (𝓝 a)) {Z : ℕ → Ω → ℝ}
    (hZm : ∀ k, AEStronglyMeasurable (Z k) P) {C : ℝ} (hZb : ∀ k ω, |Z k ω| ≤ C)
    (hZ : ∀ᵐ ω ∂P, Tendsto (fun k => Z k ω) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, X (u k) ω ^ 2 * Z k ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hZ2 : ∀ k ω, Z k ω ^ 2 ≤ C ^ 2 := fun k ω =>
    sq_le_sq' (abs_le.1 (hZb k ω)).1 (abs_le.1 (hZb k ω)).2
  have hZn : ∀ k, ∀ᵐ ω ∂P, ‖Z k ω ^ 2‖ ≤ C ^ 2 := fun k => ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hZ2 k ω
  have i1 : ∀ k, Integrable (fun ω => X (u k) ω ^ 2 * Z k ω ^ 2) P := fun k =>
    ((hX2 _ (hu k)).integrable_sq.bdd_mul ((hZm k).pow 2) (hZn k)).congr
      (ae_of_all _ fun ω => mul_comm _ _)
  have i2 : ∀ k, Integrable (fun ω => (X (u k) ω - X a ω) ^ 2) P := fun k =>
    ((hX2 _ (hu k)).sub (hX2 a ha)).integrable_sq
  have i3 : ∀ k, Integrable (fun ω => X a ω ^ 2 * Z k ω ^ 2) P := fun k =>
    ((hX2 a ha).integrable_sq.bdd_mul ((hZm k).pow 2) (hZn k)).congr
      (ae_of_all _ fun ω => mul_comm _ _)
  have hle : ∀ k, ∫ ω, X (u k) ω ^ 2 * Z k ω ^ 2 ∂P
      ≤ 2 * C ^ 2 * ∫ ω, (X (u k) ω - X a ω) ^ 2 ∂P
        + 2 * ∫ ω, X a ω ^ 2 * Z k ω ^ 2 ∂P := by
    intro k
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i2 k).const_mul _)
      ((i3 k).const_mul _)]
    exact integral_mono (i1 k) (((i2 k).const_mul _).add ((i3 k).const_mul _))
      fun ω => sq_mul_sq_le _ _ _ C (hZ2 k ω)
  have T1 : Tendsto (fun k => ∫ ω, (X (u k) ω - X a ω) ^ 2 ∂P) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδX⟩ := hXc (ε / 2) (by positivity)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hua δ hδ
    refine ⟨N, fun k hk => ?_⟩
    have h := hδX _ (hu k) _ ha (by rw [← Real.dist_eq]; exact (hN k hk).le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    linarith
  have hb : ∀ k, ∀ᵐ ω ∂P, ‖X a ω ^ 2 * Z k ω ^ 2‖ ≤ X a ω ^ 2 * C ^ 2 := fun k =>
    ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hZ2 k ω) (sq_nonneg _)
  have hl : ∀ᵐ ω ∂P, Tendsto (fun k => X a ω ^ 2 * Z k ω ^ 2) atTop (𝓝 0) := by
    filter_upwards [hZ] with ω hω
    simpa using (hω.pow 2).const_mul (X a ω ^ 2)
  have T2 := tendsto_integral_of_dominated_convergence (F := fun k ω => X a ω ^ 2 * Z k ω ^ 2)
    (f := fun _ => (0 : ℝ)) (fun ω => X a ω ^ 2 * C ^ 2) (fun k => (i3 k).aestronglyMeasurable)
    ((hX2 a ha).integrable_sq.mul_const _) hb hl
  rw [integral_zero] at T2
  have hlim : Tendsto (fun k => 2 * C ^ 2 * ∫ ω, (X (u k) ω - X a ω) ^ 2 ∂P
      + 2 * ∫ ω, X a ω ^ 2 * Z k ω ^ 2 ∂P) atTop (𝓝 0) := by
    simpa using (T1.const_mul (2 * C ^ 2)).add (T2.const_mul 2)
  exact squeeze_zero (fun k => integral_nonneg fun ω => by positivity) hle hlim

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[X_v²(K_u − K_v)²]` is uniformly small.** For
`X` square integrable and uniformly mean-square continuous on `[s, t]` and `K` measurable, bounded
and a.s. continuous on `[s, t]`: `∀ ε > 0, ∃ δ > 0`, `|u − v| ≤ δ ⇒ E[X_v²(K_u − K_v)²] ≤ ε`
(a bad sequence has a convergent subsequence; `tendsto_integral_sq_mul_sq` along it).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.exists_delta_integral_sq_mul_sub_sq_le). -/
theorem exists_delta_integral_sq_mul_sub_sq_le {X K : ℝ → Ω → ℝ}
    (hX2 : ∀ u ∈ Set.Icc s t, MemLp (X u) 2 P) (hXc : MSUnifCont P X s t)
    (hKm : ∀ u ∈ Set.Icc s t, Measurable (K u)) {C : ℝ}
    (hKb : ∀ u ∈ Set.Icc s t, ∀ ω, |K u ω| ≤ C)
    (hKc : ∀ᵐ ω ∂P, ContinuousOn (fun u => K u ω) (Set.Icc s t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, |u - v| ≤ δ →
      ∫ ω, X v ω ^ 2 * (K u ω - K v ω) ^ 2 ∂P ≤ ε := by
  by_contra hcon
  push Not at hcon
  choose u hu v hv huv hlt using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hv
  have hd : Tendsto (fun k => u (φ k) - v (φ k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs]
    refine (huv (φ k)).trans ?_
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right (hφ.id_le k) 1)
  have hlimu : Tendsto (fun k => u (φ k)) atTop (𝓝 a) := by
    have := hlim.add hd
    simp only [add_zero] at this
    exact this.congr fun k => by simp
  have hwin : ∀ w : ℕ → ℝ, (∀ k, w k ∈ Set.Icc s t) → Tendsto (fun k => w (φ k)) atTop (𝓝 a) →
      Tendsto (fun k => w (φ k)) atTop (𝓝[Set.Icc s t] a) := fun w hw hwl =>
    tendsto_nhdsWithin_iff.2 ⟨hwl, Eventually.of_forall fun k => hw (φ k)⟩
  have hZ : ∀ᵐ ω ∂P, Tendsto (fun k => K (u (φ k)) ω - K (v (φ k)) ω) atTop (𝓝 0) := by
    filter_upwards [hKc] with ω hω
    have t1 := ((hω a ha).tendsto).comp (hwin u hu hlimu)
    have t2 := ((hω a ha).tendsto).comp (hwin v hv hlim)
    simpa using t1.sub t2
  have hT := tendsto_integral_sq_mul_sq hX2 hXc (fun k => hv (φ k)) ha hlim
    (Z := fun k ω => K (u (φ k)) ω - K (v (φ k)) ω)
    (fun k => ((hKm _ (hu _)).sub (hKm _ (hv _))).aestronglyMeasurable) (C := 2 * C)
    (fun k ω => by
      rw [two_mul]
      exact (abs_sub _ _).trans (add_le_add (hKb _ (hu _) ω) (hKb _ (hv _) ω))) hZ
  have := ge_of_tendsto hT (Eventually.of_forall fun k => (hlt (φ k)).le)
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: products with bounded integrands.** If `X` is a
mean-square continuous integrand and `K` a bounded admissible one on `[s, t]`, then `X·K` is a
mean-square continuous integrand: `∫ X K dW` exists.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.MSIntegrand.mul_itoIntegrand). -/
theorem MSIntegrand.mul_itoIntegrand [IsFiniteMeasure P] {X K : ℝ → Ω → ℝ} {C : ℝ}
    (hX : MSIntegrand P 𝓕 X s t) (hK : ItoIntegrand P 𝓕 K s t C) :
    MSIntegrand P 𝓕 (fun u ω => X u ω * K u ω) s t where
  adapted u hu := (hX.adapted u hu).mul (hK.adapted u hu)
  memLp u hu := (hX.memLp u hu).of_le_mul (c := C)
    ((hX.measurable hu).mul (hK.measurable hu)).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hK.bound u hu ω) (abs_nonneg _))
  cont ε hε := by
    obtain ⟨δ1, hδ1, h1⟩ := hX.cont (ε / (4 * (C ^ 2 + 1))) (by positivity)
    obtain ⟨δ2, hδ2, h2⟩ := exists_delta_integral_sq_mul_sub_sq_le hX.memLp hX.cont
      (fun u hu => hK.measurable hu) hK.bound hK.cont (ε := ε / 4) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun u hu v hv huv => ?_⟩
    have a1 := h1 u hu v hv (huv.trans (min_le_left _ _))
    have a2 := h2 u hu v hv (huv.trans (min_le_right _ _))
    have hK2 : ∀ w ∈ Set.Icc s t, ∀ ω, K w ω ^ 2 ≤ C ^ 2 := fun w hw ω =>
      sq_le_sq' (abs_le.1 (hK.bound w hw ω)).1 (abs_le.1 (hK.bound w hw ω)).2
    have hmem : ∀ w ∈ Set.Icc s t, MemLp (fun ω => X w ω * K w ω) 2 P := fun w hw =>
      (hX.memLp w hw).of_le_mul (c := C)
        ((hX.measurable hw).mul (hK.measurable hw)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm C]
          exact mul_le_mul_of_nonneg_left (hK.bound w hw ω) (abs_nonneg _))
    have iA : Integrable (fun ω => (X u ω - X v ω) ^ 2) P :=
      ((hX.memLp u hu).sub (hX.memLp v hv)).integrable_sq
    have iB : Integrable (fun ω => X v ω ^ 2 * (K u ω - K v ω) ^ 2) P := by
      refine ((hX.memLp v hv).integrable_sq.bdd_mul (c := (2 * C) ^ 2)
        (((hK.measurable hu).sub (hK.measurable hv)).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)).congr (ae_of_all _ fun ω => mul_comm _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h3 : |K u ω - K v ω| ≤ 2 * C := by
        rw [two_mul]
        exact (abs_sub _ _).trans (add_le_add (hK.bound u hu ω) (hK.bound v hv ω))
      exact sq_le_sq' (abs_le.1 h3).1 (abs_le.1 h3).2
    have iL : Integrable (fun ω => (X u ω * K u ω - X v ω * K v ω) ^ 2) P :=
      ((hmem u hu).sub (hmem v hv)).integrable_sq
    have hle : ∫ ω, (X u ω * K u ω - X v ω * K v ω) ^ 2 ∂P
        ≤ 2 * C ^ 2 * ∫ ω, (X u ω - X v ω) ^ 2 ∂P
          + 2 * ∫ ω, X v ω ^ 2 * (K u ω - K v ω) ^ 2 ∂P := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iA.const_mul _)
        (iB.const_mul _)]
      refine integral_mono iL ((iA.const_mul _).add (iB.const_mul _)) fun ω => ?_
      have e : X u ω * K u ω - X v ω * K v ω
          = (X u ω - X v ω) * K u ω + X v ω * (K u ω - K v ω) := by ring
      have h3 : ((X u ω - X v ω) * K u ω + X v ω * (K u ω - K v ω)) ^ 2
          ≤ 2 * ((X u ω - X v ω) * K u ω) ^ 2 + 2 * (X v ω * (K u ω - K v ω)) ^ 2 := by
        nlinarith [sq_nonneg ((X u ω - X v ω) * K u ω - X v ω * (K u ω - K v ω))]
      have h4 : ((X u ω - X v ω) * K u ω) ^ 2 ≤ C ^ 2 * (X u ω - X v ω) ^ 2 := by
        rw [mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (hK2 u hu ω) (sq_nonneg _)
      have h5 : (X v ω * (K u ω - K v ω)) ^ 2 = X v ω ^ 2 * (K u ω - K v ω) ^ 2 := mul_pow _ _ _
      simp only
      rw [e]
      linarith
    have key : 2 * C ^ 2 * (ε / (4 * (C ^ 2 + 1))) ≤ ε / 2 := by
      have hpos : 0 < 4 * (C ^ 2 + 1) := by positivity
      rw [mul_div_assoc', div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [sq_nonneg C]
    have hC2 : 0 ≤ 2 * C ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left a1 hC2]

/-! ## `∫ Z K dW = Z ∫ K dW` -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: a square-integrable `𝓕_r`-measurable factor comes
out of the Itô integral**: `∫_r^t Z K_u dW_u = Z ∫_r^t K dW` a.s., for `K` bounded admissible on
`[r, t]`, `0 ≤ r` (the left-point sums agree exactly; an `L²` limit along a subsequence on which
`Σ K_{t_i}ΔW_i` also converges a.s.).
Generalises `TidyR7ItoIntegral.itoInt_const_mul` and `TidyR7ItoIntegral.itoInt_const`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.itoInt_mul_left). -/
theorem itoInt_mul_left (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {r : ℝ} (hr : 0 ≤ r) {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 r] Z)
    (hZ2 : MemLp Z 2 P) {K : ℝ → Ω → ℝ} {C : ℝ} (hK : ItoIntegrand P 𝓕 K r t C) :
    itoInt P 𝓕 W (fun u ω => Z ω * K u ω) r t =ᵐ[P] fun ω => Z ω * itoInt P 𝓕 W K r t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rcases lt_or_ge r t with hrt | htr
  · have hZK : MSIntegrand P 𝓕 (fun u ω => Z ω * K u ω) r t :=
      MSIntegrand.mul_itoIntegrand (msIntegrand_const hZ hZ2) hK
    have hL := L2Tendsto_dyadic hB hW h𝓕 hr hrt hK
    have hm : TendstoInMeasure P (fun k => itoSum W K (dyadic hrt k)) atTop
        (itoInt P 𝓕 W K r t) :=
      tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hL.tendsto_eLpNorm
    obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
    have hL2 := L2Tendsto_itoSum_ms hB hW h𝓕 hr hrt hZK (fun k => dyadic hrt (ns k))
      ((tendsto_mesh_dyadic hrt).comp hns.tendsto_atTop)
    refine ae_eq_of_L2Tendsto_of_ae_tendsto hL2 ?_
    filter_upwards [hae] with ω hω
    have e : ∀ k, itoSum W (fun u ω => Z ω * K u ω) (dyadic hrt (ns k)) ω
        = Z ω * itoSum W K (dyadic hrt (ns k)) ω := fun k => by
      simp only [itoSum, Finset.mul_sum, mul_assoc]
    exact (tendsto_congr e).2 (hω.const_mul (Z ω))
  · rw [itoInt_of_le htr, itoInt_of_le htr]
    exact ae_of_all _ fun ω => by simp

/-! ## The time integral in mean square -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the `dt`-terms `∫ X b du` of (1.32) with diffusive
bonds): the left-point Riemann sum `Σ G_{t_i}(ω)Δt_i` of a process, as a random variable.
`TidyR7ItoL2.riemannSum` read pathwise.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.dtSum). -/
noncomputable def dtSum (G : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  riemannSum p (fun u => G u ω)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the time integral `∫_s^t G_u du` in mean square**
(the `dt`-terms of (1.32) with diffusive bonds, for integrands without path regularity). For
`s < t`: a chosen `𝓕_t`-strongly measurable mean-square limit of the dyadic Riemann sums if one
exists, else `0`; for `t ≤ s`: `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.dtInt). -/
noncomputable def dtInt (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (G : ℝ → Ω → ℝ) (s t : ℝ) :
    Ω → ℝ := by
  classical
  exact if hst : s < t then
    if h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P (fun k => dtSum G (dyadic hst k)) Y
    then h.choose else 0
  else 0

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `dtInt = 0` for `t ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.dtInt_of_le). -/
theorem dtInt_of_le {G : ℝ → Ω → ℝ} (hts : t ≤ s) : dtInt P 𝓕 G s t = 0 := by
  simp only [dtInt, not_lt.2 hts, ↓reduceDIte]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if the dyadic Riemann sums have an adapted
mean-square limit, `dtInt` is one.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.dtInt_spec). -/
theorem dtInt_spec {G : ℝ → Ω → ℝ} (hst : s < t)
    (h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P (fun k => dtSum G (dyadic hst k)) Y) :
    StronglyMeasurable[𝓕 t] (dtInt P 𝓕 G s t) ∧
      L2Tendsto P (fun k => dtSum G (dyadic hst k)) (dtInt P 𝓕 G s t) := by
  classical
  have e : dtInt P 𝓕 G s t = h.choose := by simp only [dtInt, hst, h, ↓reduceDIte]
  rw [e]
  exact h.choose_spec

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `dtInt` is `𝓕_t`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.stronglyMeasurable_dtInt). -/
theorem stronglyMeasurable_dtInt {G : ℝ → Ω → ℝ} : StronglyMeasurable[𝓕 t] (dtInt P 𝓕 G s t) := by
  classical
  by_cases hst : s < t
  · by_cases h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P (fun k => dtSum G (dyadic hst k)) Y
    · exact (dtInt_spec hst h).1
    · have e : dtInt P 𝓕 G s t = 0 := by simp only [dtInt, hst, h, ↓reduceDIte]
      rw [e]
      exact stronglyMeasurable_zero
  · rw [dtInt_of_le (not_lt.1 hst)]
    exact stronglyMeasurable_zero

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the Riemann sum of an adapted process is
`𝓕_t`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.stronglyMeasurable_dtSum). -/
theorem stronglyMeasurable_dtSum {G : ℝ → Ω → ℝ}
    (hG : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (G u)) (p : Partition s t) :
    StronglyMeasurable[𝓕 t] (dtSum G p) := by
  have e : dtSum G p = fun ω => ∑ i ∈ Finset.range p.n, G (p.t i) ω * (p.t (i + 1) - p.t i) :=
    rfl
  rw [e]
  exact Finset.stronglyMeasurable_fun_sum _ fun i hi =>
    ((hG _ (t_mem p (Finset.mem_range.1 hi).le)).mono
      (𝓕.mono (t_mem p (Finset.mem_range.1 hi).le).2)).mul_const _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the Riemann sum of a square-integrable process is
square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.memLp_dtSum). -/
theorem memLp_dtSum {G : ℝ → Ω → ℝ} (hG : ∀ u ∈ Set.Icc s t, MemLp (G u) 2 P)
    (p : Partition s t) : MemLp (dtSum G p) 2 P :=
  memLp_finsetSum _ fun _ hi => (hG _ (t_mem p (Finset.mem_range.1 hi).le)).mul_const _

/-- Cochrane (2023), A1 §1.6, p. 567: the difference of two Riemann sums is a sum over the cells
of the common refinement, `Σ_{i,j}(G_{p_i} − G_{q_j})·|cell_{ij}|`.
The Riemann-sum analogue of `TidyR7ItoSums.itoSum_sub_itoSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.dtSum_sub_dtSum). -/
theorem dtSum_sub_dtSum (G : ℝ → Ω → ℝ) (p q : Partition s t) (ω : Ω) :
    dtSum G p ω - dtSum G q ω = ∑ k ∈ Finset.range p.n ×ˢ Finset.range q.n,
      (G (p.t k.1) ω - G (q.t k.2) ω) * (cellB p q k.1 k.2 - cellA p q k.1 k.2) := by
  have hp : dtSum G p ω = ∑ i ∈ Finset.range p.n, ∑ j ∈ Finset.range q.n,
      G (p.t i) ω * (cellB p q i j - cellA p q i j) := by
    unfold dtSum riemannSum
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact sub_eq_sum_cells (fun u => u) p q (Finset.mem_range.1 hi)
  have hq : dtSum G q ω = ∑ j ∈ Finset.range q.n, ∑ i ∈ Finset.range p.n,
      G (q.t j) ω * (cellB p q i j - cellA p q i j) := by
    unfold dtSum riemannSum
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact sub_eq_sum_cells' (fun u => u) p q (Finset.mem_range.1 hj)
  rw [hp, hq, Finset.sum_comm (s := Finset.range q.n), Finset.sum_product,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Cauchy estimate for Riemann sums.** If
`E[(G_u − G_v)²] ≤ ε` whenever `|u − v| ≤ δ`, then `E[(R_p(G) − R_q(G))²] ≤ ε(t − s)²` for
partitions with meshes `≤ δ` (Cauchy–Schwarz over the cells).
The Riemann-sum analogue of `TidyR7ItoSums.integral_itoSum_sub_sq_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.integral_dtSum_sub_sq_le). -/
theorem integral_dtSum_sub_sq_le {G : ℝ → Ω → ℝ} (hG : ∀ u ∈ Set.Icc s t, MemLp (G u) 2 P)
    {ε δ : ℝ} (hδ : ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, |u - v| ≤ δ →
      ∫ ω, (G u ω - G v ω) ^ 2 ∂P ≤ ε)
    (p q : Partition s t) (hp : mesh p ≤ δ) (hq : mesh q ≤ δ) :
    ∫ ω, (dtSum G p ω - dtSum G q ω) ^ 2 ∂P ≤ ε * (t - s) ^ 2 := by
  classical
  set S := Finset.range p.n ×ˢ Finset.range q.n with hS
  set w : ℕ × ℕ → ℝ := fun k => cellB p q k.1 k.2 - cellA p q k.1 k.2 with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => sub_nonneg.2 (cellA_le_cellB p q k.1 k.2)
  have hsw : ∑ k ∈ S, w k = t - s := sum_cells_eq p q
  have hmem : ∀ k ∈ S, p.t k.1 ∈ Set.Icc s t ∧ q.t k.2 ∈ Set.Icc s t := by
    intro k hk
    rw [hS, Finset.mem_product] at hk
    exact ⟨t_mem p (Finset.mem_range.1 hk.1).le, t_mem q (Finset.mem_range.1 hk.2).le⟩
  have hc2 : ∀ k ∈ S, Integrable (fun ω => (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2) P :=
    fun k hk => ((hG _ (hmem k hk).1).sub (hG _ (hmem k hk).2)).integrable_sq
  have hpt : ∀ ω, (dtSum G p ω - dtSum G q ω) ^ 2
      ≤ (t - s) * ∑ k ∈ S, w k * (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2 := by
    intro ω
    rw [dtSum_sub_dtSum, ← hsw]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun k _ => hw0 k)
      (fun k _ => mul_nonneg (hw0 k) (sq_nonneg _)) fun k _ => le_of_eq ?_
    ring
  have iR : Integrable (fun ω => (t - s) * ∑ k ∈ S, w k *
      (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2) P :=
    (integrable_finsetSum _ fun k hk => (hc2 k hk).const_mul _).const_mul _
  have iL : Integrable (fun ω => (dtSum G p ω - dtSum G q ω) ^ 2) P :=
    ((memLp_dtSum hG p).sub (memLp_dtSum hG q)).integrable_sq
  have hts : 0 ≤ t - s := sub_nonneg.2 (a_le_b p)
  calc ∫ ω, (dtSum G p ω - dtSum G q ω) ^ 2 ∂P
      ≤ ∫ ω, (t - s) * ∑ k ∈ S, w k * (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2 ∂P :=
        integral_mono iL iR hpt
    _ = (t - s) * ∑ k ∈ S, w k * ∫ ω, (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun k hk => (hc2 k hk).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ (t - s) * ∑ k ∈ S, w k * ε := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) hts
        rw [hS, Finset.mem_product] at hk
        have hi := Finset.mem_range.1 hk.1
        have hj := Finset.mem_range.1 hk.2
        rcases (cellA_le_cellB p q k.1 k.2).lt_or_eq with hne | heq
        · refine mul_le_mul_of_nonneg_left ?_ (hw0 k)
          exact hδ _ (t_mem p hi.le) _ (t_mem q hj.le)
            ((abs_sub_le_of_cell p q hi hj hne).trans (max_le hp hq))
        · simp only [hw, heq, sub_self, zero_mul, le_refl]
    _ = ε * (t - s) ^ 2 := by rw [← Finset.sum_mul, hsw]; ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the Riemann sums of a mean-square continuous process
are mean-square Cauchy along any partitions with mesh `→ 0`, `s < t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.cauchy_dtSum). -/
theorem cauchy_dtSum {G : ℝ → Ω → ℝ} (hst : s < t) (hG : MSIntegrand P 𝓕 G s t)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ N, ∀ k ≥ N, ∀ l ≥ N,
      ∫ ω, (dtSum G (ps k) ω - dtSum G (ps l) ω) ^ 2 ∂P ≤ ε := by
  have hts : 0 < t - s := sub_pos.2 hst
  obtain ⟨δ, hδ, hδG⟩ := hG.cont (ε / (t - s) ^ 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun k hk l hl => ?_⟩
  have h := integral_dtSum_sub_sq_le hG.memLp hδG (ps k) (ps l) (hN k hk) (hN l hl)
  rwa [div_mul_cancel₀ _ (by positivity)] at h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: existence of the mean-square time integral.** For a
mean-square continuous process and `s < t`, the dyadic Riemann sums have an `𝓕_t`-strongly
measurable mean-square limit.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.exists_dyadic_limit_dt). -/
theorem exists_dyadic_limit_dt {G : ℝ → Ω → ℝ} (hst : s < t) (hG : MSIntegrand P 𝓕 G s t) :
    ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P (fun k => dtSum G (dyadic hst k)) Y :=
  exists_L2Tendsto (𝓕.le t) (fun _ => stronglyMeasurable_dtSum hG.adapted _)
    (fun _ => memLp_dtSum hG.memLp _)
    (fun _ hε => cauchy_dtSum hst hG _ (tendsto_mesh_dyadic hst) hε)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the dyadic Riemann sums converge in mean square to
`dtInt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.L2Tendsto_dyadic_dt). -/
theorem L2Tendsto_dyadic_dt {G : ℝ → Ω → ℝ} (hst : s < t) (hG : MSIntegrand P 𝓕 G s t) :
    L2Tendsto P (fun k => dtSum G (dyadic hst k)) (dtInt P 𝓕 G s t) :=
  (dtInt_spec hst (exists_dyadic_limit_dt hst hG)).2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square time integral of a mean-square
continuous process is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.memLp_dtInt). -/
theorem memLp_dtInt {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t) :
    MemLp (dtInt P 𝓕 G s t) 2 P := by
  rcases lt_or_ge s t with hst | hts
  · exact (L2Tendsto_dyadic_dt hst hG).2.1
  · rw [dtInt_of_le hts]
    exact MemLp.zero

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Riemann sums converge in mean square along ANY
partitions** with mesh `→ 0`, to `dtInt`, for a mean-square continuous process, `s < t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.L2Tendsto_dtSum). -/
theorem L2Tendsto_dtSum {G : ℝ → Ω → ℝ} (hst : s < t) (hG : MSIntegrand P 𝓕 G s t)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => dtSum G (ps k)) (dtInt P 𝓕 G s t) := by
  have hY := L2Tendsto_dyadic_dt hst hG
  have hmem : ∀ p : Partition s t, MemLp (dtSum G p) 2 P := fun p => memLp_dtSum hG.memLp p
  have hts : 0 < t - s := sub_pos.2 hst
  refine ⟨fun k => hmem _, hY.2.1, ?_⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδG⟩ := hG.cont (η / (4 * (t - s) ^ 2)) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  have hdy : ∀ᶠ m in atTop, mesh (dyadic hst m) ≤ δ :=
    (tendsto_mesh_dyadic hst).eventually (ge_mem_nhds hδ)
  refine ⟨N, fun k hk => ?_⟩
  have hev : ∀ᶠ m in atTop, ∫ ω, (dtSum G (ps k) ω - dtInt P 𝓕 G s t ω) ^ 2 ∂P
      ≤ 2 * (η / (4 * (t - s) ^ 2) * (t - s) ^ 2)
        + 2 * ∫ ω, (dtSum G (dyadic hst m) ω - dtInt P 𝓕 G s t ω) ^ 2 ∂P := by
    filter_upwards [hdy] with m hm
    refine (integral_sq_sub_le (hmem (dyadic hst m)) (hmem (ps k)) hY.2.1).trans ?_
    have h := integral_dtSum_sub_sq_le hG.memLp hδG (dyadic hst m) (ps k) hm (hN k hk)
    linarith
  have hlim : Tendsto (fun m => 2 * (η / (4 * (t - s) ^ 2) * (t - s) ^ 2)
      + 2 * ∫ ω, (dtSum G (dyadic hst m) ω - dtInt P 𝓕 G s t ω) ^ 2 ∂P) atTop
      (𝓝 (2 * (η / (4 * (t - s) ^ 2) * (t - s) ^ 2) + 2 * 0)) :=
    tendsto_const_nhds.add (hY.2.2.const_mul 2)
  have h2 := ge_of_tendsto hlim hev
  have e2 : 2 * (η / (4 * (t - s) ^ 2) * (t - s) ^ 2) + 2 * 0 = η / 2 := by field_simp; ring
  rw [e2] at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square time integral is the pathwise one**
whenever the paths are a.s. continuous on `[s, t]`: `dtInt G =ᵐ ∫_s^t G_u du` (an `L²` limit and
an a.s. limit of the same Riemann sums agree), `s ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.dtInt_ae_eq_integral). -/
theorem dtInt_ae_eq_integral {G : ℝ → Ω → ℝ} (hst : s ≤ t) (hG : MSIntegrand P 𝓕 G s t)
    (hGc : ∀ᵐ ω ∂P, ContinuousOn (fun u => G u ω) (Set.Icc s t)) :
    dtInt P 𝓕 G s t =ᵐ[P] fun ω => ∫ u in s..t, G u ω := by
  rcases hst.lt_or_eq with hst | hst
  · refine ae_eq_of_L2Tendsto_of_ae_tendsto (L2Tendsto_dyadic_dt hst hG) ?_
    filter_upwards [hGc] with ω hω
    exact tendsto_riemannSum hω _ (tendsto_mesh_dyadic hst)
  · rw [dtInt_of_le hst.ge, hst]
    exact ae_of_all _ fun ω => by simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square time integral of a process vanishing
on `[s, t]` is `0` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProducts.dtInt_of_eq_zero). -/
theorem dtInt_of_eq_zero {G : ℝ → Ω → ℝ} (hG0 : ∀ u ∈ Set.Icc s t, ∀ ω, G u ω = 0) :
    dtInt P 𝓕 G s t =ᵐ[P] 0 := by
  rcases lt_or_ge s t with hst | hts
  · have e : ∀ k, dtSum G (dyadic hst k) = 0 := fun k => funext fun ω => by
      unfold dtSum riemannSum
      exact Finset.sum_eq_zero fun i hi => by
        simp only [hG0 _ (t_mem _ (Finset.mem_range.1 hi).le) ω, zero_mul]
    have hL : L2Tendsto P (fun k => dtSum G (dyadic hst k)) 0 :=
      ⟨fun k => by change MemLp (dtSum G (dyadic hst k)) 2 P; rw [e k]; exact MemLp.zero,
        MemLp.zero, by simp [e]⟩
    exact ae_eq_of_L2Tendsto (dtInt_spec hst ⟨0, stronglyMeasurable_zero, hL⟩).2 hL
  · rw [dtInt_of_le hts]

end Cochrane.LongTermDebtDynamics.TidyR7ItoProducts
