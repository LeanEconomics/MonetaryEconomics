/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR13MRepDensity

/-!
# The martingale representation theorem on the Brownian filtration

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B6, item 3). Let `W` have
continuous paths, `𝓕` an admissible filtration (`TidyR7BrownianQV.BMFiltration`) with
`𝓕_T ⊆ 𝓖_T = σ(W_r : 0 ≤ r ≤ T)` (`TidyR13MRepDensity.mrepNat`; e.g. the natural filtration).

* `mrepSpace`: `{c + ∫_0^T H dW}` (`H` in the extended class `TidyR13MRepIntegral.MRepIntegrand`)
  as a subspace of `L²(P)`; `isClosed_mrepSpace`: it is closed (isometry + completeness of
  `L²(dt × dP)` + closedness of the class).
* **`mrep_representation`**: every `Y ∈ L²` that is `𝓖_T`-measurable is
  `Y = E[Y] + ∫_0^T H dW` a.s. (orthogonal projection onto the closed subspace; the residual is
  orthogonal to all `∫_b^a G dW` via `TidyR13MRepCutoff.mrep_cut`, hence `0` by
  `TidyR13MRepDensity.mrep_density`).
* **`mrep_unique`**: the constant and the integrand are unique (`H` up to `dt × dP`-null sets).
* **`mrep_martingale`**: every `𝓕`-martingale `M` with `M_T ∈ L²` has
  `M_t = E[M_T] + ∫_0^t H dW` a.s. for every `t ∈ [0, T]`, one `H` for all `t`;
  `mrep_martingale_zero`: `M_0 = E[M_T]` a.s.
-/

namespace Cochrane.ZeroBound.TidyR13MRepTheorem

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoIntegral Cochrane.ZeroBound.TidyR7ItoUnbounded
  Cochrane.ZeroBound.TidyR13MRepIntegral Cochrane.ZeroBound.TidyR13MRepCutoff
  Cochrane.ZeroBound.TidyR13MRepDensity
open scoped ENNReal NNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ## `L²` tools -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: convergence in the Hilbert space `L²(P)` is
mean-square convergence of representatives.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_L2Tendsto_of_tendsto_Lp). -/
theorem mrep_L2Tendsto_of_tendsto_Lp {f : ℕ → Lp ℝ 2 P} {g : Lp ℝ 2 P}
    (h : Tendsto f atTop (𝓝 g)) : L2Tendsto P (fun n => ⇑(f n)) ⇑g := by
  refine ⟨fun n => Lp.memLp _, Lp.memLp _, ?_⟩
  have e : ∀ n, ∫ ω, (f n ω - g ω) ^ 2 ∂P = ‖f n - g‖ ^ 2 := by
    intro n
    have h1 := integral_sq_eq_toReal_eLpNorm_sq ((Lp.memLp (f n)).sub (Lp.memLp g))
    simp only [Pi.sub_apply] at h1
    rw [h1, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub (f n) g)]
  simp_rw [e]
  have := (tendsto_iff_norm_sub_tendsto_zero.1 h).pow 2
  simpa using this

/-- Cochrane (2023), A1 §1.6, pp. 567–568: convergent constants converge in mean square.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_L2Tendsto_const). -/
theorem mrep_L2Tendsto_const [IsFiniteMeasure P] {a : ℕ → ℝ} {b : ℝ}
    (h : Tendsto a atTop (𝓝 b)) : L2Tendsto P (fun n _ => a n) (fun _ => b) := by
  refine ⟨fun n => memLp_const _, memLp_const _, ?_⟩
  simp only [integral_const, smul_eq_mul]
  have h2 : Tendsto (fun n => (a n - b) ^ 2) atTop (𝓝 0) := by
    have := (h.sub_const b).pow 2
    simpa using this
  simpa using h2.const_mul (P.real Set.univ)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[c + ∫_0^T H dW] = c`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_integral_const_add). -/
theorem mrep_integral_const_add (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {T c : ℝ} {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H 0 T) :
    ∫ ω, (c + mrepInt P 𝓕 W H 0 T ω) ∂P = c := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [integral_add (integrable_const c) ((memLp_mrepInt hB hW h𝓕 le_rfl hH).integrable
    one_le_two), mrepInt_integral_eq_zero hB hW h𝓕 le_rfl hH]
  simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the zero integrand is in the class and
`∫_s^t 0 dW = 0` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_zero). -/
theorem mrep_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) :
    MRepIntegrand P 𝓕 (fun _ _ => 0) s t ∧ mrepInt P 𝓕 W (fun _ _ => 0) s t =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := mrep_agree hB hW h𝓕 hs (mrep_ms_zero (P := P) (𝓕 := 𝓕) (s := s) (t := t))
    measurable_const
  exact ⟨h.1, h.2.trans mrep_itoInt_zero⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫_s^s H dW = 0` a.s. on the extended class.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrepInt_self). -/
theorem mrepInt_self (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : MRepIntegrand P 𝓕 H s s) : mrepInt P 𝓕 W H s s =ᵐ[P] 0 := by
  obtain ⟨G, hG⟩ := hH
  have h1 := (mrep_spec hB hW h𝓕 hs hG).2
  simp only [itoInt_of_le le_rfl] at h1
  exact ae_eq_of_L2Tendsto h1 ⟨fun _ => MemLp.zero, MemLp.zero, by simp⟩

/-! ## The closed subspace -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the subspace `{c + ∫_0^T H dW}` of `L²(P)`**,
`H` in the extended class `TidyR13MRepIntegral.MRepIntegrand` on `[0, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrepSpace). -/
def mrepSpace (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (T : ℝ) : Submodule ℝ (Lp ℝ 2 P) where
  carrier := {f | ∃ c : ℝ, ∃ H, MRepIntegrand P 𝓕 H 0 T ∧
    ⇑f =ᵐ[P] fun ω => c + mrepInt P 𝓕 W H 0 T ω}
  add_mem' := by
    rintro a b ⟨c, H, hH, ha⟩ ⟨c', H', hH', hb⟩
    refine ⟨c + c', _, mrep_add hH hH', ?_⟩
    filter_upwards [Lp.coeFn_add a b, ha, hb, mrepInt_add hB hW h𝓕 le_rfl hH hH'] with
      ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h3, h4]
    ring
  zero_mem' := by
    refine ⟨0, _, (mrep_zero hB hW h𝓕 le_rfl).1, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 P, (mrep_zero hB hW h𝓕 (t := T) le_rfl).2] with
      ω h1 h2
    rw [h1, h2]
    simp
  smul_mem' := by
    rintro k a ⟨c, H, hH, ha⟩
    refine ⟨k * c, _, mrep_const_mul hH k, ?_⟩
    filter_upwards [Lp.coeFn_smul k a, ha, mrepInt_const_mul hB hW h𝓕 le_rfl hH k] with
      ω h1 h2 h3
    rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul]
    ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `{c + ∫_0^T H dW}` is closed in `L²(P)`.** A limit
`c_n + ∫H_n dW → X`: `c_n = E[·] → E[X]`; `∫H_n dW` is Cauchy, so by the isometry `H_n` is Cauchy
in `L²(dt × dP)` and converges to some `H` in the (closed) class; `∫H_n dW → ∫H dW`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.isClosed_mrepSpace). -/
theorem isClosed_mrepSpace (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (T : ℝ) :
    IsClosed (mrepSpace hB hW h𝓕 T : Set (Lp ℝ 2 P)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨f, hfK, hf⟩ := mem_closure_iff_seq_limit.1 hx
  have hfK' : ∀ n, ∃ c : ℝ, ∃ H, MRepIntegrand P 𝓕 H 0 T ∧
      ⇑(f n) =ᵐ[P] fun ω => c + mrepInt P 𝓕 W H 0 T ω := hfK
  choose c H hH hfe using hfK'
  have hZ : L2Tendsto P (fun n ω => c n + mrepInt P 𝓕 W (H n) 0 T ω) ⇑x :=
    (mrep_L2Tendsto_of_tendsto_Lp hf).congr_seq hfe
  have hc : Tendsto c atTop (𝓝 (∫ ω, x ω ∂P)) := by
    have h := tendsto_integral_mul_of_L2Tendsto_memLp hZ (memLp_const 1)
    simp only [one_mul] at h
    simp_rw [mrep_integral_const_add hB hW h𝓕 (hH _)] at h
    exact h
  have hI : L2Tendsto P (fun n => mrepInt P 𝓕 W (H n) 0 T)
      (fun ω => x ω - ∫ ω, x ω ∂P) := by
    have h := hZ.add (mrep_L2Tendsto_const (P := P) hc.neg)
    refine (h.congr_seq fun n => ae_of_all _ fun ω => ?_).congr_ae (ae_of_all _ fun ω => ?_)
    · simp only [Pi.add_apply]; ring
    · simp only [Pi.add_apply]; ring
  have hmem := fun n => (hH n).memLp
  set F : ℕ → ℝ × Ω → ℝ := fun n => (hmem n).aestronglyMeasurable.mk _ with hF
  have hFH : ∀ n, Function.uncurry (H n) =ᵐ[mrepMeasure P 0 T] F n := fun n =>
    (hmem n).aestronglyMeasurable.ae_eq_mk
  have hcau := mrep_cauchy_of_L2Tendsto hI
  obtain ⟨Flim, -, hFlim⟩ := exists_L2Tendsto (P := mrepMeasure P 0 T) le_rfl
    (fun n => (hmem n).aestronglyMeasurable.stronglyMeasurable_mk) (fun n => (hmem n).ae_eq (hFH n))
    (fun ε hε => by
      obtain ⟨N, hN⟩ := hcau ε hε
      refine ⟨N, fun k hk l hl => ?_⟩
      have h := hN k hk l hl
      rw [mrepInt_isometry_sub hB hW h𝓕 le_rfl (hH k) (hH l)] at h
      refine le_of_eq_of_le ?_ h
      exact integral_congr_ae (by
        filter_upwards [hFH k, hFH l] with z e1 e2
        rw [e1, e2]))
  have hL : L2Tendsto (mrepMeasure P 0 T) (fun n => Function.uncurry (H n))
      (Function.uncurry (Function.curry Flim)) := by
    rw [Function.uncurry_curry]
    exact hFlim.congr_seq fun n => (hFH n).symm
  have hHlim := mrep_of_L2Tendsto hH hL
  have hconv := mrepInt_L2Tendsto hB hW h𝓕 le_rfl hH hHlim hL
  have heq := ae_eq_of_L2Tendsto hI hconv
  refine ⟨∫ ω, x ω ∂P, Function.curry Flim, hHlim, ?_⟩
  filter_upwards [heq] with ω hω
  rw [← hω]
  ring

/-! ## The representation theorem -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the inner product of `L²(P)` on representatives.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_inner_eq). -/
theorem mrep_inner_eq (f g : Lp ℝ 2 P) : ⟪f, g⟫_ℝ = ∫ ω, f ω * g ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  change ⟪f ω, g ω⟫_ℝ = f ω * g ω
  rw [RCLike.inner_apply, conj_trivial, mul_comm]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: THE MARTINGALE REPRESENTATION THEOREM (form for
a random variable).** Let `W` have continuous paths, `𝓕` be admissible with
`𝓕_T ⊆ 𝓖_T = σ(W_r : 0 ≤ r ≤ T)`. Every square-integrable `𝓖_T`-measurable `Y` is
`Y = E[Y] + ∫_0^T H dW` a.s. for some `H` in the extended class on `[0, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_representation). -/
theorem mrep_representation (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {T : ℝ}
    (h𝓕T : 𝓕 T ≤ mrepNat W T) {Y : Ω → ℝ} (hY2 : MemLp Y 2 P)
    (hYm : AEStronglyMeasurable[mrepNat W T] Y P) :
    ∃ H, MRepIntegrand P 𝓕 H 0 T ∧
      Y =ᵐ[P] fun ω => (∫ ω, Y ω ∂P) + mrepInt P 𝓕 W H 0 T ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set K := mrepSpace hB hW h𝓕 T with hK
  have : CompleteSpace K := (isClosed_mrepSpace hB hW h𝓕 T).completeSpace_coe
  obtain ⟨w, hwK, hwo⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := K)
    (hY2.toLp Y)
  obtain ⟨c, H, hH, hw⟩ := hwK
  set Y' : Ω → ℝ := fun ω => Y ω - (c + mrepInt P 𝓕 W H 0 T ω) with hY'def
  have hI2 := memLp_mrepInt hB hW h𝓕 le_rfl hH
  have hY'2 : MemLp Y' 2 P := hY2.sub ((memLp_const c).add hI2)
  have hD : ⇑(hY2.toLp Y - w) =ᵐ[P] Y' := by
    filter_upwards [Lp.coeFn_sub (hY2.toLp Y) w, hY2.coeFn_toLp, hw] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hinner : ∀ (Z : Ω → ℝ) (hZ : MemLp Z 2 P), hZ.toLp Z ∈ K →
      ∫ ω, Y' ω * Z ω ∂P = 0 := by
    intro Z hZ hZK
    have h := (Submodule.mem_orthogonal K _).1 hwo _ hZK
    rw [mrep_inner_eq] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [hD, hZ.coeFn_toLp] with ω h1 h2
    rw [h1, h2, mul_comm]
  have hY'0 : ∫ ω, Y' ω ∂P = 0 := by
    have hmem : (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P).toLp _ ∈ K := by
      refine ⟨1, _, (mrep_zero hB hW h𝓕 (t := T) le_rfl).1, ?_⟩
      filter_upwards [(memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P).coeFn_toLp,
        (mrep_zero hB hW h𝓕 (t := T) le_rfl).2] with ω h1 h2
      rw [h1, h2]
      simp
    simpa using hinner _ _ hmem
  have hY' : ∀ b a, 0 ≤ b → b ≤ a → a ≤ T → ∀ G : ℝ → Ω → ℝ, MSIntegrand P 𝓕 G b a →
      Measurable (Function.uncurry G) → ∫ ω, Y' ω * itoInt P 𝓕 W G b a ω ∂P = 0 := by
    intro b a hb hba haT G hG hGm
    have hc := mrep_cut hB hW h𝓕 le_rfl hb hba haT hG hGm
    have hG2 := memLp_itoInt_ms hB hW h𝓕 hb hG
    refine hinner _ hG2 ⟨0, _, hc.1, ?_⟩
    filter_upwards [hG2.coeFn_toLp, hc.2] with ω h1 h2
    rw [h1, h2]
    simp
  have hY'm : AEStronglyMeasurable[mrepNat W T] Y' P :=
    hYm.sub (stronglyMeasurable_const.add
      ((stronglyMeasurable_mrepInt hB hW h𝓕 le_rfl hH).mono h𝓕T)).aestronglyMeasurable
  have h0 := mrep_density hB hW h𝓕 hcont hY'2 hY'm hY'0 hY'
  have hYc : Y =ᵐ[P] fun ω => c + mrepInt P 𝓕 W H 0 T ω := by
    filter_upwards [h0] with ω hω
    simp only [hY'def, Pi.zero_apply] at hω
    linarith
  have hcY : ∫ ω, Y ω ∂P = c := by
    rw [integral_congr_ae hYc, mrep_integral_const_add hB hW h𝓕 hH]
  exact ⟨H, hH, by rw [hcY]; exact hYc⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: uniqueness of the representation.** If
`c + ∫_0^T H dW = c' + ∫_0^T H' dW` a.s., then `c = c'` and `H = H'` `dt × dP`-a.e. on
`(0, T] × Ω`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_unique). -/
theorem mrep_unique (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {T c c' : ℝ} {H H' : ℝ → Ω → ℝ}
    (hH : MRepIntegrand P 𝓕 H 0 T) (hH' : MRepIntegrand P 𝓕 H' 0 T)
    (h : (fun ω => c + mrepInt P 𝓕 W H 0 T ω) =ᵐ[P] fun ω => c' + mrepInt P 𝓕 W H' 0 T ω) :
    c = c' ∧ Function.uncurry H =ᵐ[mrepMeasure P 0 T] Function.uncurry H' := by
  have hc : c = c' := by
    rw [← mrep_integral_const_add hB hW h𝓕 (c := c) hH,
      ← mrep_integral_const_add hB hW h𝓕 (c := c') hH', integral_congr_ae h]
  refine ⟨hc, ?_⟩
  have hII : mrepInt P 𝓕 W H 0 T =ᵐ[P] mrepInt P 𝓕 W H' 0 T := by
    filter_upwards [h] with ω hω
    rw [hc] at hω
    linarith
  have h0 := mrepInt_isometry_sub hB hW h𝓕 le_rfl hH hH'
  have hz : ∫ ω, (mrepInt P 𝓕 W H 0 T ω - mrepInt P 𝓕 W H' 0 T ω) ^ 2 ∂P = 0 := by
    rw [← integral_zero Ω ℝ]
    refine integral_congr_ae ?_
    filter_upwards [hII] with ω hω
    simp [hω]
  rw [hz] at h0
  have hi := (hH.memLp.sub hH'.memLp).integrable_sq
  have h1 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).1 h0.symm
  filter_upwards [h1] with x hx
  simp only [Pi.sub_apply, Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hx
  exact hx

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: THE MARTINGALE REPRESENTATION THEOREM (process
form).** Under the hypotheses of `mrep_representation`, every `𝓕`-martingale `M` with `M_T`
square integrable is an Itô integral on `[0, T]`: there is ONE `H` in the extended class with
`M_t = E[M_T] + ∫_0^t H dW` a.s. for every `t ∈ [0, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_martingale). -/
theorem mrep_martingale (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {T : ℝ}
    (h𝓕T : 𝓕 T ≤ mrepNat W T) {M : ℝ → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hM2 : MemLp (M T) 2 P) :
    ∃ H, MRepIntegrand P 𝓕 H 0 T ∧ ∀ t ∈ Set.Icc 0 T,
      M t =ᵐ[P] fun ω => (∫ ω, M T ω ∂P) + mrepInt P 𝓕 W H 0 t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨H, hH, hrep⟩ := mrep_representation hB hW h𝓕 hcont h𝓕T hM2
    ((hM.1 T).mono h𝓕T).aestronglyMeasurable
  refine ⟨H, hH, fun t ht => ?_⟩
  have hIT := (memLp_mrepInt hB hW h𝓕 le_rfl hH).integrable one_le_two
  have h1 := hM.2 t T ht.2
  have h2 := condExp_congr_ae (m := 𝓕 t) hrep
  have h3 := condExp_add (integrable_const (∫ ω, M T ω ∂P)) hIT (𝓕 t)
  rw [condExp_const (𝓕.le t)] at h3
  have h4 := mrepInt_condExp hB hW h𝓕 le_rfl ht.1 ht.2 hH
  filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
  rw [← e1, e2]
  refine e3.trans ?_
  rw [Pi.add_apply, e4]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: in `mrep_martingale` the initial value is the
constant `M_0 = E[M_T]` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepTheorem.mrep_martingale_zero). -/
theorem mrep_martingale_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {T : ℝ} (hT : 0 ≤ T) {M : ℝ → Ω → ℝ} {H : ℝ → Ω → ℝ}
    (hH : MRepIntegrand P 𝓕 H 0 T)
    (hrep : ∀ t ∈ Set.Icc 0 T, M t =ᵐ[P] fun ω => (∫ ω, M T ω ∂P) + mrepInt P 𝓕 W H 0 t ω) :
    M 0 =ᵐ[P] fun _ => ∫ ω, M T ω ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  filter_upwards [hrep 0 ⟨le_rfl, hT⟩, mrepInt_self hB hW h𝓕 le_rfl (mrep_mono hH le_rfl hT)]
    with ω h1 h2
  rw [h1, h2]
  simp

end Cochrane.ZeroBound.TidyR13MRepTheorem
