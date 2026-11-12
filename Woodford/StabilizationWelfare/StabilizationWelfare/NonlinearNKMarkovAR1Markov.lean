/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovAE

/-!
# The Markov representation of the a.s. equilibrium with a general AR(1) innovation law

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392: the equilibrium as a
time-invariant function of the exogenous state) and Appendix A.3 (pp. 631–635).

`NonlinearNKMarkovAE.ar1_iid_equilibrium` gives the a.s. unique, a.s. measurable solution `z_t`
of the exact stochastic conditions on the i.i.d. product space of ANY bounded innovation law `ν`,
with disturbances `e_t = x_t c` driven by the AR(1) `x_t = ρx_{t−1} + ε_t`. This module proves it
has a MARKOV REPRESENTATION: there is one measurable, bounded `g : ℝ → ℝ⁴`, independent of `t`,
with `z_t = g(x_t)` almost surely at every date.

The route: build the Markov equilibrium directly on the bounded state interval and transfer it.

* `freeze` (the freezing lemma): if `W` is `m`-measurable and `Y` is independent of `m`,
  `E[F(W, Y) | m] = ∫ F(W, y) d(law Y)` a.s., for bounded measurable `F`.
* `hbExt`: integration against a probability measure on bounded measurable functions extends
  (Hahn–Banach, then a linear complement) to a linear functional on ALL functions that is
  bounded by the sup norm; hence the AR(1) transition integral is a Markov operator in the sense
  of `NonlinearNKMarkov.IsMarkov` (`arOp`, `arOp_isMarkov`, `arOp_eq`, `arOp_measPres`).
* `general_existence_inv_bd`: the Newton–Picard existence proof of
  `NonlinearNKMarkovGeneral.general_existence` with the invariant needed only on the ball.
* `bm_*`, `markov_existence_meas`: bounded measurability passes through the Markov operator, the
  forward series, the inverse `linSol` and the residual, so the Markov equilibrium is MEASURABLE
  whenever the Markov operator preserves bounded measurable functions.
* **`ar1_markov_representation`**: the measurable Markov equilibrium `g` on `|x| ≤ B/(1 − |ρ|)`,
  evaluated at `x_t`, solves the exact stochastic conditions a.s. (by `freeze`), and every
  a.s. measurable solution within `r` equals `g(x_t)` a.s. at every date.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovAR1Markov

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral ExpectationsMeasure
open NonlinearNKMarkovAE ExpectationsMeasureIID

/-! ## The freezing lemma and the Hahn–Banach extension of an integral -/

/-- Woodford (2003), App. A.3 (conditional expectations of a function of known and future
variables; **the freezing lemma**): if `W` is `m`-measurable and `Y` is independent of `m`, then
`E[F(W, Y) | m] = ∫ F(W, y) d(law Y)` a.s. for bounded measurable `F`. -/
theorem freeze {Ω α β : Type*} {m m0 : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure[m0] Ω} [IsProbabilityMeasure μ] (hm : m ≤ m0) {W : Ω → α} {Y : Ω → β}
    (hW : Measurable[m] W) (hY : Measurable Y)
    (hind : Indep (MeasurableSpace.comap Y inferInstance) m μ)
    {F : α × β → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ q, |F q| ≤ C) :
    μ[fun ω => F (W ω, Y ω) | m] =ᵐ[μ] fun ω => ∫ y, F (W ω, y) ∂(μ.map Y) := by
  have hW0 : Measurable W := hW.mono hm le_rfl
  set G : α → ℝ := fun a => ∫ y, F (a, y) ∂(μ.map Y) with hG
  have hGm : Measurable G := (hF.stronglyMeasurable.integral_prod_right').measurable
  have hGb : ∀ a, |G a| ≤ C := fun a => by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C) (Eventually.of_forall fun y => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hC _
    · rw [probReal_univ, mul_one]
  have hFi : Integrable (fun ω => F (W ω, Y ω)) μ :=
    Integrable.of_bound (hF.comp (hW0.prodMk hY)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (g := fun ω => G (W ω)) hm hFi
    (fun s _ _ => ?_) (fun s hs _ => ?_)
    (hGm.comp hW).aestronglyMeasurable).symm
  · exact (Integrable.of_bound (hGm.comp hW0).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _)).integrableOn
  · -- the pair `(1_s, W)` is independent of `Y`
    set V : Ω → ℝ × α := fun ω => (s.indicator (fun _ => (1 : ℝ)) ω, W ω) with hV
    have hVm : Measurable[m] V :=
      (measurable_const.indicator hs).prodMk hW
    have hV0 : Measurable V := hVm.mono hm le_rfl
    have hindV : IndepFun V Y μ := by
      rw [IndepFun_iff_Indep]
      exact (indep_of_indep_of_le_right hind hVm.comap_le).symm
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map hV0.aemeasurable hY.aemeasurable).1 hindV
    set H : (ℝ × α) × β → ℝ := fun q => max 0 (min 1 q.1.1) * F (q.1.2, q.2) with hH
    have hHm : Measurable H :=
      ((measurable_const.max (measurable_const.min (measurable_fst.comp measurable_fst))).mul
        (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hHb : ∀ q, |H q| ≤ C := fun q => by
      simp only [hH, abs_mul]
      have h1 : |max 0 (min 1 q.1.1)| ≤ 1 := by
        rw [abs_le]; constructor <;> [linarith [le_max_left 0 (min 1 q.1.1)];
          exact max_le zero_le_one (min_le_left _ _)]
      have := hC (q.1.2, q.2)
      nlinarith [abs_nonneg (max 0 (min 1 q.1.1)), abs_nonneg (F (q.1.2, q.2))]
    have hind01 : ∀ ω, max 0 (min 1 (s.indicator (fun _ => (1 : ℝ)) ω)) =
        s.indicator (fun _ => (1 : ℝ)) ω := fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    have hHi : Integrable H ((μ.map V).prod (μ.map Y)) :=
      Integrable.of_bound hHm.aestronglyMeasurable C
        (Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hHb q)
    have key : ∫ ω, H (V ω, Y ω) ∂μ = ∫ ω, ∫ y, H (V ω, y) ∂(μ.map Y) ∂μ := by
      rw [← integral_map (hV0.prodMk hY).aemeasurable hHm.aestronglyMeasurable, hmap,
        integral_prod _ hHi, integral_map hV0.aemeasurable]
      exact (hHm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    rw [← integral_indicator (hm _ hs), ← integral_indicator (hm _ hs)]
    have e1 : (fun ω => H (V ω, Y ω)) = s.indicator (fun ω => F (W ω, Y ω)) := funext fun ω => by
      simp only [hH, hV, hind01]
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : (fun ω => ∫ y, H (V ω, y) ∂(μ.map Y)) = s.indicator (fun ω => G (W ω)) :=
      funext fun ω => by
        simp only [hH, hV, hind01, hG]
        by_cases h : ω ∈ s <;> simp [h]
    rw [← e1, ← e2, key]

/-- Woodford (2003), Ch. 6, §1 (expectations as a linear operator on all functions): integration
against a probability measure on bounded measurable functions extends to a linear functional on
all functions, bounded by the sup norm (Hahn–Banach on bounded functions, then a linear
complement). -/
theorem hbExt {X : Type*} [MeasurableSpace X] [Nonempty X] (κ : Measure X)
    [IsProbabilityMeasure κ] :
    ∃ Λ : (X → ℝ) →ₗ[ℝ] ℝ, (∀ f : X → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      Λ f = ∫ x, f x ∂κ) ∧ ∀ (h : X → ℝ) (C : ℝ), (∀ x, |h x| ≤ C) → |Λ h| ≤ C := by
  let V : Submodule ℝ (X → ℝ) :=
    { carrier := {f | ∃ C, ∀ x, |f x| ≤ C}
      zero_mem' := ⟨0, fun x => by simp⟩
      add_mem' := by
        rintro f g ⟨C, hC⟩ ⟨D, hD⟩
        exact ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
      smul_mem' := by
        rintro c f ⟨C, hC⟩
        exact ⟨|c| * C, fun x => by
          simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)⟩ }
  have hint : ∀ f : V, Measurable (f : X → ℝ) → Integrable (f : X → ℝ) κ := fun f hf => by
    obtain ⟨C, hC⟩ := f.2
    exact Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  let D : Submodule ℝ V :=
    { carrier := {f | Measurable (f : X → ℝ)}
      zero_mem' := measurable_const
      add_mem' := fun hf hg => hf.add hg
      smul_mem' := fun c _ hf => hf.const_smul c }
  let ℓ : D →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ x, ((f : V) : X → ℝ) x ∂κ
      map_add' := fun f g => integral_add (hint _ f.2) (hint _ g.2)
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  set N : V → ℝ := fun f => ⨆ x, (f : X → ℝ) x with hN
  have hbdd : ∀ f : V, BddAbove (Set.range (f : X → ℝ)) := fun f => by
    obtain ⟨C, hC⟩ := f.2
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (hC x)⟩
  obtain ⟨g, hg, hgN⟩ := exists_extension_of_le_sublinear ⟨D, ℓ⟩ N
    (fun c hc f => by
      simp only [hN, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      exact (Real.mul_iSup_of_nonneg hc.le _).symm)
    (fun f f' => ciSup_le fun x => by
      simp only [Submodule.coe_add, Pi.add_apply]
      exact add_le_add (le_ciSup (hbdd f) x) (le_ciSup (hbdd f') x))
    (fun f => by
      change ∫ x, (((f : D) : V) : X → ℝ) x ∂κ ≤ ⨆ x, (((f : D) : V) : X → ℝ) x
      calc _ ≤ ∫ _x, (⨆ x, (((f : D) : V) : X → ℝ) x) ∂κ :=
            integral_mono (hint _ (f : D).2) (integrable_const _)
              fun x => le_ciSup (hbdd _) x
        _ = _ := by rw [integral_const, probReal_univ, one_smul])
  obtain ⟨G, hG⟩ := LinearMap.exists_extend g
  have hGV : ∀ f : V, G f = g f := fun f => by rw [← hG]; rfl
  refine ⟨G, fun f hf hb => ?_, fun h C hC => ?_⟩
  · have := hg ⟨⟨f, hb⟩, hf⟩
    rw [hGV ⟨f, hb⟩]
    exact this
  · have hle : ∀ f : V, (∀ x, (f : X → ℝ) x ≤ C) → G f ≤ C := fun f hf => by
      rw [hGV]; exact (hgN f).trans (ciSup_le hf)
    have h1 := hle ⟨h, C, hC⟩ fun x => (le_abs_self _).trans (hC x)
    have h2 := hle (-⟨h, C, hC⟩) fun x => by
      simp only [Submodule.coe_neg, Pi.neg_apply]
      exact (neg_le_abs _).trans (hC x)
    rw [abs_le]
    rw [Submodule.coe_neg, map_neg] at h2
    exact ⟨by linarith, h1⟩

/-! ## Measurability of the Markov equilibrium -/

variable {p : Par} {X : Type*}

/-- Woodford (2003), App. A.3: a Markov operator PRESERVES MEASURABILITY when it maps bounded
measurable functions to measurable functions. -/
def MeasPres [MeasurableSpace X] (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop :=
  ∀ f : X → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → Measurable (M f)

/-- Woodford (2003), App. A.3: a bounded measurable function of the state. -/
def BM {E : Type*} [MeasurableSpace X] [Norm E] [MeasurableSpace E] (f : X → E) : Prop :=
  Measurable f ∧ ∃ C, ∀ x, ‖f x‖ ≤ C

/-- A continuous function of a bounded measurable function is bounded measurable. -/
theorem bm_comp [MeasurableSpace X] {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [MeasurableSpace F]
    [BorelSpace F] {u : X → E} (hu : BM u) {Ψ : E → F} (hΨ : Continuous Ψ) :
    BM (fun x => Ψ (u x)) := by
  obtain ⟨C, hC⟩ := hu.2
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : E) C).exists_bound_of_continuousOn
    hΨ.continuousOn
  exact ⟨hΨ.measurable.comp hu.1, D, fun x => hD _ (by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hC x)⟩

/-- Pairs of bounded measurable functions are bounded measurable. -/
theorem bm_pair [MeasurableSpace X] {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [NormedAddCommGroup F] [MeasurableSpace F] {u : X → E} {v : X → F} (hu : BM u) (hv : BM v) :
    BM (fun x => (u x, v x)) := by
  obtain ⟨C, hC⟩ := hu.2
  obtain ⟨D, hD⟩ := hv.2
  exact ⟨hu.1.prodMk hv.1, max C D, fun x => by
    rw [Prod.norm_def]; exact max_le_max (hC x) (hD x)⟩

/-- A measurability-preserving Markov operator maps bounded measurable functions to bounded
measurable functions. -/
theorem bm_M [MeasurableSpace X] {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) (hMP : MeasPres M)
    {f : X → ℝ} (hf : BM f) : BM (M f) := by
  obtain ⟨C, hC⟩ := hf.2
  have hC' : ∀ x, |f x| ≤ C := fun x => by rw [← Real.norm_eq_abs]; exact hC x
  exact ⟨hMP f hf.1 ⟨C, hC'⟩, C, fun x => by rw [Real.norm_eq_abs]; exact hM.2 f C hC' x⟩

/-- The coordinatewise Markov operator preserves bounded measurability. -/
theorem bm_Mv [MeasurableSpace X] {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (hMP : MeasPres M) {n : ℕ} {h : X → Fin n → ℝ} (hh : BM h) : BM (Mv M h) := by
  obtain ⟨C, hC⟩ := hh.2
  have hC0 : ∀ x, ‖h x‖ ≤ max C 0 := fun x => (hC x).trans (le_max_left _ _)
  exact ⟨measurable_pi_iff.2 fun i =>
    (bm_M hM hMP (bm_comp hh (continuous_apply i))).1, max C 0,
    fun x => Mv_norm_le hM (le_max_right _ _) hC0 x⟩

/-- Iterates of the Markov operator preserve bounded measurability. -/
theorem bm_iter [MeasurableSpace X] {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (hMP : MeasPres M) {n : ℕ} {b : X → Fin n → ℝ} (hb : BM b) (k : ℕ) : BM ((Mv M)^[k] b) := by
  induction k with
  | zero => exact hb
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact bm_Mv hM hMP ih

/-- Woodford (2003), (A.13): the forward series of a bounded measurable function is bounded
measurable. -/
theorem bm_fwdSol [MeasurableSpace X] {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (hMP : MeasPres M) {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : Summable fun k => mnorm (B ^ k)) {b : X → Fin n → ℝ} (hb : BM b) :
    BM (fwdSol B M b) := by
  obtain ⟨C, hC⟩ := hb.2
  have hC0 : ∀ x, ‖b x‖ ≤ max C 0 := fun x => (hC x).trans (le_max_left _ _)
  refine ⟨?_, _, (fwdSol_spec hB hM (le_max_right _ _) hC0).1⟩
  refine measurable_of_tendsto_metrizable (f := fun N x => ∑ k ∈ Finset.range N,
    (B ^ k).mulVec ((Mv M)^[k] b x)) (fun N => Finset.measurable_fun_sum _ fun k _ =>
      (Matrix.mulVecLin (B ^ k)).continuous_of_finiteDimensional.measurable.comp
        (bm_iter hM hMP hb k).1) (tendsto_pi_nhds.2 fun x => ?_)
  exact (Summable.of_norm_bounded (hB.mul_right (max C 0)) fun k => (norm_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_left (iter_norm_le hM k (le_max_right _ _) hC0 x)
      (mnorm_nonneg _))).hasSum.tendsto_sum_nat

/-- Woodford (2003), App. A.3, (A.13): the inverse of the linearised operator maps bounded
measurable functions to bounded measurable functions. -/
theorem bm_linSol [MeasurableSpace X] (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (hMP : MeasPres M) {r : X → Fin 4 → ℝ} (hr : BM r) : BM (linSol p M r) := by
  have hs1 : BM (s1F p M r) := bm_comp (Ψ := fun q : (Fin 4 → ℝ) × ℝ =>
      (q.1 2 - q.1 1 + p.k3 * q.1 3 - p.α * p.β * p.k3 * q.2) / p.cR)
    (bm_pair hr (bm_M hM hMP (bm_comp hr (continuous_apply 3)))) (by fun_prop)
  have hb : BM (bF p M r) := bm_comp (Ψ := fun q : (Fin 4 → ℝ) × ℝ =>
      ![(q.1 0 - p.φ * q.2) / p.dd, (p.κ * q.1 0 + (p.σ + p.φy) * q.2) / p.dd])
    (bm_pair hr hs1) (continuous_pi fun i => by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one] <;> fun_prop)
  have hu : BM (uF p M r) := bm_fwdSol hM hMP (summable_mnorm_Amat hp) hb
  have hg : BM (fun x => ![gF p M r x]) := bm_comp (Ψ := fun q : ((Fin 4 → ℝ) × (Fin 2 → ℝ)) × ℝ =>
      ![q.1.1 1 + (1 - p.α * p.β) * (1 - p.σ) * q.1.2 0 + p.α * p.β * (p.θ - 1) * q.2])
    (bm_pair (bm_pair hr hu) (bm_M hM hMP (bm_comp hu (continuous_apply 1))))
    (continuous_pi fun i => by
      fin_cases i; simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]; fun_prop)
  have habs : mnorm !![p.α * p.β] < 1 := by
    rw [mnorm_ab, abs_of_pos hp.ab_pos]; exact hp.ab_lt_one
  have hF : BM (FF p M r) :=
    bm_comp (bm_fwdSol hM hMP (summable_mnorm_pow_of_lt habs) hg) (continuous_apply 0)
  exact bm_comp (Ψ := fun q : ((Fin 2 → ℝ) × ℝ) × (Fin 4 → ℝ) =>
      ![q.1.1 0, q.1.1 1, q.1.2, q.1.2 + p.cR * q.1.1 1 - p.k3 * q.2 3])
    (bm_pair (bm_pair hu hF) hr) (continuous_pi fun i => by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop)

/-- Woodford (2003), (A.11): the residual of a bounded measurable function with bounded
measurable disturbances is bounded measurable. -/
theorem bm_Phi [MeasurableSpace X] {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (hMP : MeasPres M) {ξ : X → Fin 5 → ℝ} {ε : ℝ} (hξ : BM fun x => ε • ξ x)
    {z : X → Fin 4 → ℝ} (hz : BM z) : BM (Phi p M ξ ε z) :=
  bm_comp (Ψ := fun q : ((Fin 5 → ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) => Qmap p q.1 + q.2)
    (bm_pair (bm_pair hξ hz) (bm_Mv hM hMP (bm_comp (bm_pair hξ hz)
      (contDiff_Nmap (p := p) (n := 0)).continuous)))
    (((contDiff_Qmap (p := p) (n := 0)).continuous.comp continuous_fst).add continuous_snd)

/-- Woodford (2003), App. A.3 (**existence with an invariant on the ball**): the Newton–Picard
fixed point of `NonlinearNKMarkovGeneral.general_existence` lies in every set containing `0`,
invariant under the Newton map on the ball of radius `r` and closed under pointwise limits of
sequences in that ball. -/
theorem general_existence_inv_bd (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)),
      IsMarkov M → ∀ (ξ : X → Fin 5 → ℝ) (ε : ℝ), (∀ x, ‖ε • ξ x‖ ≤ δ) →
        ∀ A : (X → Fin 4 → ℝ) → Prop, A 0 →
          (∀ z, (∀ x, ‖z x‖ ≤ r) → A z → A (fun x => z x - linSol p M (Phi p M ξ ε z) x)) →
          (∀ (zs : ℕ → X → Fin 4 → ℝ) (z : X → Fin 4 → ℝ), (∀ n, A (zs n)) →
            (∀ n x, ‖zs n x‖ ≤ r) → (∀ x, Tendsto (fun n => zs n x) atTop (𝓝 (z x))) → A z) →
        ∃ z : X → Fin 4 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ IsMarkovEqm p M ξ ε z) ∧ A z := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_small (contDiff_Qmap (p := p) (n := 1)) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_small (contDiff_Nmap (p := p) (n := 1)) hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  -- bounds of `Q`, `N` on the ball
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Qmap (p := p) (n := 0)).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  refine ⟨r0, hr00, fun r hr hrr0 => ?_⟩
  set τ := r / (4 * Kap p) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin 5 → ℝ => Qmap p (e, 0)) 0 :=
    ((contDiff_Qmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  have hcN : ContinuousAt (fun e : Fin 5 → ℝ => Nmap p (e, 0)) 0 :=
    ((contDiff_Nmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  refine ⟨min r (min (δQ / 2) (δN / 2)), lt_min hr (lt_min (by positivity) (by positivity)),
    fun X M hM ξ ε hξ A hA0 hAT hAlim => ?_⟩
  have hξr : ∀ x, ‖ε • ξ x‖ ≤ r := fun x => (hξ x).trans (min_le_left _ _)
  have hξ0 : ∀ x, ‖ε • ξ x‖ ≤ r0 := fun x => (hξr x).trans hrr0
  -- `Φ` is bounded on the ball
  have hPhiB : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖Phi p M ξ ε z x‖ ≤ CQ + CN := by
    intro z hz x
    have hin : ∀ x', (ε • ξ x', z x') ∈ Metric.closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ)) r0 :=
      fun x' => by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        exact max_le (hξ0 x') ((hz x').trans hrr0)
    have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN _ (hin x))
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (hin x))
      (Mv_norm_le hM hCN0 (fun x' => hCN _ (hin x')) x))
  -- the Newton map
  set T : (X → Fin 4 → ℝ) → (X → Fin 4 → ℝ) := fun z x => z x - linSol p M (Phi p M ξ ε z) x
    with hT
  have hCQN : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → 0 ≤ CQ + CN := fun z hz => by
    by_cases hX : Nonempty X
    · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hPhiB z hz x)
    · have hin : ((0 : Fin 5 → ℝ), (0 : Fin 4 → ℝ)) ∈ Metric.closedBall 0 r0 :=
        Metric.mem_closedBall_self hr00.le
      exact add_nonneg ((norm_nonneg _).trans (hCQ _ hin)) ((norm_nonneg _).trans (hCN _ hin))
  have hcontr : ∀ z z' : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → (∀ x, ‖z' x‖ ≤ r) → ∀ D,
      (∀ x, ‖z x - z' x‖ ≤ D) → ∀ x, ‖T z x - T z' x‖ ≤ D / 2 := by
    intro z z' hz hz' D hD x
    have hD0 : 0 ≤ D := by
      by_cases hX : Nonempty X
      · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hD x)
      · exact absurd ⟨x⟩ hX
    have hz0 : ∀ x, ‖z x‖ ≤ r0 := fun x => (hz x).trans hrr0
    have hz'0 : ∀ x, ‖z' x‖ ≤ r0 := fun x => (hz' x).trans hrr0
    have hC := hCQN z hz
    have hLd := Lop_bounded (p := p) hM hD0 hD
    set c := (‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖) * D
    have hc0 : 0 ≤ c := mul_nonneg (by positivity) hD0
    have hres := resid_diff_bound (p := p) hM hη0.le hQ hN hξ0 hz0 hz'0 hD
    -- `T z − T z′ = −L⁻¹(Φz − Φz′ − L(z − z′))`
    have e1 := linSol_sub hp hM hC hC (hPhiB z hz) (hPhiB z' hz')
    have e2 := linSol_sub hp hM (a := CQ + CN + (CQ + CN)) (a' := c) (by positivity) hc0
      (r := fun x => Phi p M ξ ε z x - Phi p M ξ ε z' x)
      (fun x => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz x) (hPhiB z' hz' x))) hLd
    have e3 := linSol_Lop hp hM hD0 hD
    have key : T z x - T z' x = -linSol p M (fun x => Phi p M ξ ε z x - Phi p M ξ ε z' x -
        Lop p M (fun x => z x - z' x) x) x := by
      rw [e2, e1, e3]
      simp only [hT]
      ring
    rw [key, norm_neg]
    have hr2 := norm_linSol_le hp hM (by positivity) hres x
    calc _ ≤ Kap p * (2 * η * D) := hr2
      _ = D / 2 := by rw [hη]; field_simp; ring
  -- `T 0` is small
  have hT0 : ∀ x, ‖T 0 x‖ ≤ r / 2 := by
    intro x
    have hb : ∀ x, ‖Phi p M ξ ε 0 x‖ ≤ 2 * τ := fun x => by
      rw [Phi_zero_eq hM]
      have hq : ∀ x', ‖Qmap p (ε • ξ x', 0) - Qmap p (0, 0)‖ ≤ τ := fun x' => by
        have h := hQc (x := ε • ξ x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have hn : ∀ x', ‖Nmap p (ε • ξ x', 0) - Nmap p (0, 0)‖ ≤ τ := fun x' => by
        have h := hNc (x := ε • ξ x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ τ + τ := add_le_add (hq x) (Mv_norm_le hM hτ0.le hn x)
        _ = 2 * τ := by ring
    have h := norm_linSol_le hp hM (by positivity) hb x
    simp only [hT, Pi.zero_apply, zero_sub, norm_neg]
    calc _ ≤ Kap p * (2 * τ) := h
      _ = r / 2 := by rw [hτ]; field_simp; ring
  have hball : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖T z x‖ ≤ r := by
    intro z hz x
    have h1 := hcontr z 0 hz (fun x => by simp [hr.le]) r (fun x => by simpa using hz x) x
    calc ‖T z x‖ ≤ ‖T z x - T 0 x‖ + ‖T 0 x‖ := by
          have := norm_add_le (T z x - T 0 x) (T 0 x); simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add h1 (hT0 x)
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → X → Fin 4 → ℝ := fun n => T^[n] 0 with hzs
  have hzsB : ∀ n x, ‖zs n x‖ ≤ r := by
    intro n
    induction n with
    | zero => intro x; simp [hzs, hr.le]
    | succ n ih =>
      intro x
      simp only [hzs, Function.iterate_succ_apply']
      exact hball _ ih x
  have hzsA : ∀ n, A (zs n) := by
    intro n
    induction n with
    | zero => simpa [hzs] using hA0
    | succ n ih =>
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]; exact hAT _ (hzsB n) ih
  have hstep : ∀ n x, ‖zs n x - zs (n + 1) x‖ ≤ r / 2 / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hT0 x
    | succ n ih =>
      intro x
      have h := hcontr (zs (n + 1)) (zs n) (hzsB _) (hzsB _) (r / 2 / 2 ^ n)
        (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (n + 1 + 1) = T (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) x = T (zs n) x from congrFun e2 x]
      calc _ ≤ r / 2 / 2 ^ n / 2 := h
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun n => zs n x := fun x =>
    cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hstep n x
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzdist : ∀ n x, ‖zs n x - z x‖ ≤ r / 2 ^ n := fun n x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n x)
      (fun n => by rw [dist_eq_norm]; exact hstep n x) (hz x) n
    rwa [dist_eq_norm] at this
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x =>
    le_of_tendsto' ((hz x).norm) fun n => hzsB n x
  -- `z` is a fixed point of `T`
  have hfix : T z = z := by
    funext x
    have hlim : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (T z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => r / 2 ^ n / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hcontr z (zs n) hzB (hzsB n) (r / 2 ^ n) (fun x => by
        rw [norm_sub_rev]; exact hzdist n x) x
    have hlim2 : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (z x)) :=
      (hz x).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hlim hlim2
  refine ⟨z, ⟨hzB, ?_⟩, hAlim zs z hzsA hzsB hz⟩
  -- the fixed point solves `Φ = 0`
  have hl : linSol p M (Phi p M ξ ε z) = 0 := by
    funext x
    have := congrFun hfix x
    simp only [hT] at this
    have h2 : linSol p M (Phi p M ξ ε z) x = 0 := by
      have := congrArg (fun v => z x - v) this
      simp only [sub_sub_cancel, sub_self] at this
      exact this
    exact h2
  obtain ⟨-, hL⟩ := linSol_spec hp hM (hCQN z hzB) (hPhiB z hzB)
  unfold IsMarkovEqm
  rw [← hL, hl]
  funext x
  have := congrFun (Lop_sub (p := p) M (0 : X → Fin 4 → ℝ) 0) x
  simp only [Pi.zero_apply, sub_self] at this
  exact this

/-- Woodford (2003), Ch. 6, §1 and App. A.3 (**the Markov equilibrium is measurable**): under the
Taylor principle there are radii such that for every measurable state space, every Markov
operator preserving bounded measurable functions and every measurable disturbance pattern with
`‖εξ‖ ≤ δ`, the Markov equilibrium within `r` is a measurable function of the state. -/
theorem markov_existence_meas (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (X : Type*) [MeasurableSpace X]
      (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M → MeasPres M → ∀ (ξ : X → Fin 5 → ℝ) (ε : ℝ),
        Measurable ξ → (∀ x, ‖ε • ξ x‖ ≤ δ) →
          ∃ z : X → Fin 4 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ IsMarkovEqm p M ξ ε z) ∧ Measurable z := by
  obtain ⟨r0, hr0, hex⟩ := general_existence_inv_bd hp
  refine ⟨r0, hr0, fun r hr hrr0 => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hex r hr hrr0
  refine ⟨δ, hδ, fun X _ M hM hMP ξ ε hξ hξδ => ?_⟩
  have hξB : BM fun x => ε • ξ x := ⟨hξ.const_smul ε, δ, hξδ⟩
  exact h X M hM ξ ε hξδ (fun z => Measurable z) measurable_zero
    (fun z hz hzm => hzm.sub (bm_linSol hp hM hMP (bm_Phi hM hMP hξB ⟨hzm, r, hz⟩)).1)
    (fun zs z hzs _ hlim => measurable_of_tendsto_metrizable hzs (tendsto_pi_nhds.2 hlim))

/-! ## The AR(1) transition as a Markov operator on the bounded state interval -/

/-- Woodford (2003), Ch. 6, §1: the projection of `ℝ` onto the state interval `|x| ≤ B`. -/
noncomputable def clampX (Bx : ℝ) (hB : 0 ≤ Bx) (y : ℝ) : ARState Bx :=
  ⟨max (-Bx) (min Bx y), abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩

/-- The projection onto the state interval is continuous. -/
theorem continuous_clampX (Bx : ℝ) (hB : 0 ≤ Bx) : Continuous (clampX Bx hB) :=
  (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

/-- The projection fixes the points of the interval. -/
theorem clampX_of {Bx : ℝ} (hB : 0 ≤ Bx) {y : ℝ} (hy : |y| ≤ Bx) : (clampX Bx hB y : ℝ) = y := by
  have := abs_le.1 hy
  simp only [clampX]
  rw [min_eq_right this.2, max_eq_right this.1]

/-- Woodford (2003), Ch. 6, §1: the AR(1) transition `x′ = ρx + e`, projected on the interval. -/
noncomputable def arSucc (ρ Bx : ℝ) (hB : 0 ≤ Bx) (x : ARState Bx) (e : ℝ) : ARState Bx :=
  clampX Bx hB (ρ * x + e)

/-- The AR(1) transition is jointly continuous. -/
theorem continuous_arSucc (ρ Bx : ℝ) (hB : 0 ≤ Bx) :
    Continuous fun q : ARState Bx × ℝ => arSucc ρ Bx hB q.1 q.2 :=
  (continuous_clampX Bx hB).comp ((continuous_const.mul
    (continuous_subtype_val.comp continuous_fst)).add continuous_snd)

/-- Woodford (2003), Ch. 6, §1: at each state, the transition integral extended to all functions
(`hbExt`). -/
noncomputable def arΛ (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx) (x : ARState Bx) :
    (ARState Bx → ℝ) →ₗ[ℝ] ℝ :=
  have : Nonempty (ARState Bx) := ⟨⟨0, by simpa using hB⟩⟩
  Classical.choose (hbExt ((ν : Measure ℝ).map (arSucc ρ Bx hB x)))

/-- The defining properties of `arΛ`. -/
theorem arΛ_spec (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx) (x : ARState Bx) :
    (∀ f : ARState Bx → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      arΛ ν ρ Bx hB x f = ∫ y, f y ∂((ν : Measure ℝ).map (arSucc ρ Bx hB x))) ∧
      ∀ (h : ARState Bx → ℝ) (C : ℝ), (∀ x, |h x| ≤ C) → |arΛ ν ρ Bx hB x h| ≤ C :=
  have : Nonempty (ARState Bx) := ⟨⟨0, by simpa using hB⟩⟩
  Classical.choose_spec (hbExt ((ν : Measure ℝ).map (arSucc ρ Bx hB x)))

/-- Woodford (2003), Ch. 6, §1 (**the AR(1) Markov operator for a GENERAL innovation law**):
`(Mf)(x) = ∫ f(ρx + e) dν(e)` on bounded measurable `f`, extended linearly to all functions. -/
noncomputable def arOp (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx) :
    (ARState Bx → ℝ) →ₗ[ℝ] (ARState Bx → ℝ) where
  toFun f x := arΛ ν ρ Bx hB x f
  map_add' f g := funext fun x => map_add (arΛ ν ρ Bx hB x) f g
  map_smul' c f := funext fun x => map_smul (arΛ ν ρ Bx hB x) c f

/-- Woodford (2003), Ch. 6, §1: on bounded measurable functions `arOp` is the transition
integral. -/
theorem arOp_eq (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx) {f : ARState Bx → ℝ}
    (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) (x : ARState Bx) :
    arOp ν ρ Bx hB f x = ∫ e, f (arSucc ρ Bx hB x e) ∂(ν : Measure ℝ) := by
  change arΛ ν ρ Bx hB x f = _
  have hm : Measurable (arSucc ρ Bx hB x) :=
    ((continuous_arSucc ρ Bx hB).comp (Continuous.prodMk_right x)).measurable
  rw [(arΛ_spec ν ρ Bx hB x).1 f hf hb, integral_map hm.aemeasurable hf.aestronglyMeasurable]

/-- Woodford (2003), Ch. 6, §1: `arOp` is a Markov operator. -/
theorem arOp_isMarkov (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx) :
    IsMarkov (arOp ν ρ Bx hB) := by
  refine ⟨funext fun x => ?_, fun h C hC x => (arΛ_spec ν ρ Bx hB x).2 h C hC⟩
  rw [arOp_eq ν ρ Bx hB measurable_const ⟨1, fun _ => by norm_num⟩ x, integral_const,
    probReal_univ, one_smul]

/-- Woodford (2003), Ch. 6, §1: `arOp` maps bounded measurable functions to measurable ones. -/
theorem arOp_measPres (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx) :
    MeasPres (arOp ν ρ Bx hB) := fun f hf hb => by
  have e : arOp ν ρ Bx hB f = fun x => ∫ e, f (arSucc ρ Bx hB x e) ∂(ν : Measure ℝ) :=
    funext (arOp_eq ν ρ Bx hB hf hb)
  rw [e]
  exact (hf.comp (continuous_arSucc ρ Bx hB).measurable).stronglyMeasurable
    |>.integral_prod_right'.measurable

/-! ## The Markov representation of the a.s. equilibrium -/

/-- Woodford (2003), Ch. 6, §1 and App. A.3 (**MARKOV REPRESENTATION with a GENERAL bounded
innovation law**): under the Taylor principle there are `r, δ > 0` such that on the i.i.d.
product space of any innovation law `ν` with `|ε| ≤ B` a.s., with the AR(1) state
`x_t = ρx_{t−1} + ε_t` (`|ρ| < 1`) and disturbances `e_t = x_t c` with `B‖c‖/(1 − |ρ|) ≤ δ`,
there is ONE measurable `g : ℝ → ℝ⁴` with `‖g‖ ≤ r`, independent of the date, such that
`z_t = g(x_t)` solves the exact stochastic conditions a.s., and every a.s. measurable solution
within `r` equals `g(x_t)` a.s. at every date. -/
theorem ar1_markov_representation (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (ν : ProbabilityMeasure ℝ) (B ρ : ℝ), |ρ| < 1 →
      (∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) → ∀ c : Fin 5 → ℝ, B / (1 - |ρ|) * ‖c‖ ≤ δ →
        ∃ g : ℝ → Fin 4 → ℝ, Measurable g ∧ (∀ y, ‖g y‖ ≤ r) ∧
          (Gd (iidSystem ν) (fun t ω => g (ar1 ρ t ω)) ∧
            Bd (iidSystem ν) (fun t ω => g (ar1 ρ t ω)) r ∧
            SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) (fun t ω => g (ar1 ρ t ω))) ∧
          ∀ z : ℕ → (ℕ → ℝ) → Fin 4 → ℝ, Gd (iidSystem ν) z → Bd (iidSystem ν) z r →
            SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) z →
              ∀ t, z t =ᵐ[(iidSystem ν).μ] fun ω => g (ar1 ρ t ω) := by
  obtain ⟨ρu, hρu, huniq⟩ := seq_uniqueness_ae hp
  obtain ⟨r0, hr0, hex⟩ := markov_existence_meas hp
  set r := min r0 ρu with hr
  have hr0' : 0 < r := lt_min hr0 hρu
  obtain ⟨δ1, hδ1, hM⟩ := hex r hr0' (min_le_left _ _)
  refine ⟨r, hr0', min δ1 ρu, lt_min hδ1 hρu, fun ν B ρ hρ hB c hc => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hB.exists
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hx₀
  have h1ρ : 0 < 1 - |ρ| := by linarith
  set Bx := B / (1 - |ρ|) with hBx
  have hBx0 : 0 ≤ Bx := div_nonneg hB0 h1ρ.le
  set M := arOp ν ρ Bx hBx0 with hMdef
  set ξ : ARState Bx → Fin 5 → ℝ := fun x => (x : ℝ) • c with hξ
  have hξm : Measurable ξ := (continuous_subtype_val.smul continuous_const).measurable
  have hξδ : ∀ x, ‖(1 : ℝ) • ξ x‖ ≤ δ1 := fun x => by
    rw [one_smul, hξ, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right x.2 (norm_nonneg c)).trans (hc.trans (min_le_left _ _))
  obtain ⟨gX, ⟨hgB, hgE⟩, hgm⟩ := hM (ARState Bx) M (arOp_isMarkov ν ρ Bx hBx0)
    (arOp_measPres ν ρ Bx hBx0) ξ 1 hξm hξδ
  set g : ℝ → Fin 4 → ℝ := fun y => gX (clampX Bx hBx0 y) with hg
  have hgm' : Measurable g := hgm.comp (continuous_clampX Bx hBx0).measurable
  have hgB' : ∀ y, ‖g y‖ ≤ r := fun y => hgB _
  set E := iidSystem ν with hE
  have har : ∀ t, Measurable[E.𝓕 t] (ar1 ρ t) := fun t => (ar1_adapted ν ρ t).measurable
  have har0 : ∀ t, Measurable (ar1 ρ t) := fun t => (har t).mono (E.𝓕.le t) le_rfl
  have hx : ∀ t, ∀ᵐ ω ∂E.μ, |ar1 ρ t ω| ≤ Bx := fun t => ar1_bdd (ν := ν) hρ hB t
  have heG : Gd E (fun t ω => ar1 ρ t ω • c) := fun t =>
    ((har0 t).smul_const c).aestronglyMeasurable
  have hzG : Gd E (fun t ω => g (ar1 ρ t ω)) := fun t => (hgm'.comp (har0 t)).aestronglyMeasurable
  have hzB : Bd E (fun t ω => g (ar1 ρ t ω)) r := fun t => Eventually.of_forall fun ω => hgB' _
  -- the transition integrand
  have hNB : BM (fun x : ARState Bx => Nmap p ((1 : ℝ) • ξ x, gX x)) :=
    bm_comp (bm_pair ⟨hξm.const_smul (1 : ℝ), δ1, hξδ⟩ ⟨hgm, r, hgB⟩)
      (contDiff_Nmap (p := p) (n := 0)).continuous
  have key : ∀ t (i : Fin 4), E.E t (fun ω' => Nmap p (ar1 ρ (t + 1) ω' • c,
      g (ar1 ρ (t + 1) ω')) i) =ᵐ[E.μ] fun ω =>
        M (fun x' => Nmap p ((1 : ℝ) • ξ x', gX x') i) (clampX Bx hBx0 (ar1 ρ t ω)) := by
    intro t i
    have hNi : BM (fun x : ARState Bx => Nmap p ((1 : ℝ) • ξ x, gX x) i) :=
      bm_comp hNB (continuous_apply i)
    obtain ⟨C, hC⟩ := hNi.2
    set F : ARState Bx × ℝ → ℝ := fun q => Nmap p ((1 : ℝ) • ξ (arSucc ρ Bx hBx0 q.1 q.2),
      gX (arSucc ρ Bx hBx0 q.1 q.2)) i with hF
    have hFm : Measurable F := hNi.1.comp (continuous_arSucc ρ Bx hBx0).measurable
    have hFb : ∀ q, |F q| ≤ C := fun q => by rw [← Real.norm_eq_abs]; exact hC _
    have hW : Measurable[E.𝓕 t] fun ω => clampX Bx hBx0 (ar1 ρ t ω) :=
      (continuous_clampX Bx hBx0).measurable.comp (har t)
    have hY : Measurable fun ω : ℕ → ℝ => ω (t + 1) := measurable_pi_apply (t + 1)
    have hind : Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ => ω (t + 1)) inferInstance)
        (E.𝓕 t) E.μ :=
      indep_of_indep_of_le_left (indep_future ν t)
        (measurable_future_fun t measurable_id).comap_le
    have hfr := freeze (μ := E.μ) (E.𝓕.le t) hW hY hind hFm hFb
    have hlaw : E.μ.map (fun ω : ℕ → ℝ => ω (t + 1)) = (ν : Measure ℝ) :=
      Measure.infinitePi_map_eval _ (t + 1)
    have hcongr : (fun ω' => Nmap p (ar1 ρ (t + 1) ω' • c, g (ar1 ρ (t + 1) ω')) i) =ᵐ[E.μ]
        fun ω' => F (clampX Bx hBx0 (ar1 ρ t ω'), ω' (t + 1)) := by
      filter_upwards [hx t, hx (t + 1)] with ω' ht ht1
      have e1 : arSucc ρ Bx hBx0 (clampX Bx hBx0 (ar1 ρ t ω')) (ω' (t + 1)) =
          clampX Bx hBx0 (ar1 ρ (t + 1) ω') := by
        simp only [arSucc, clampX_of hBx0 ht]
        rfl
      simp only [hF, e1, hg, hξ, one_smul, clampX_of hBx0 ht1]
    filter_upwards [E.E_congr hcongr t, hfr] with ω h1 h2
    rw [h1]
    refine h2.trans ?_
    rw [hlaw, hMdef, arOp_eq ν ρ Bx hBx0 hNi.1 ⟨C, fun x => by
      rw [← Real.norm_eq_abs]; exact hC x⟩]
  have hzE : SeqEqmAE E p (fun t ω => ar1 ρ t ω • c) (fun t ω => g (ar1 ρ t ω)) := fun t => by
    filter_upwards [hx t, ae_all_iff.2 (key t)] with ω h1 h2
    have e1 : MvA E (fun s ω' => Nmap p (ar1 ρ s ω' • c, g (ar1 ρ s ω'))) t ω =
        Mv M (fun x' => Nmap p ((1 : ℝ) • ξ x', gX x')) (clampX Bx hBx0 (ar1 ρ t ω)) :=
      funext fun i => h2 i
    have e2 : ar1 ρ t ω • c = (1 : ℝ) • ξ (clampX Bx hBx0 (ar1 ρ t ω)) := by
      rw [one_smul, hξ]; simp only [clampX_of hBx0 h1]
    change Qmap p (ar1 ρ t ω • c, g (ar1 ρ t ω)) + MvA E _ t ω = 0
    rw [e1, e2]
    exact congrFun hgE (clampX Bx hBx0 (ar1 ρ t ω))
  refine ⟨g, hgm', hgB', ⟨hzG, hzB, hzE⟩, fun z hzG' hzB' hz t => ?_⟩
  have heb : Bd E (fun t ω => ar1 ρ t ω • c) ρu := fun t => by
    filter_upwards [hx t] with ω hω
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hω (norm_nonneg c)).trans (hc.trans (min_le_right _ _))
  exact huniq (ℕ → ℝ) E _ z (fun t ω => g (ar1 ρ t ω)) heG hzG' hzG heb
    (fun t => by filter_upwards [hzB' t] with ω hω; exact hω.trans (min_le_right _ _))
    (fun t => Eventually.of_forall fun ω => (hgB' _).trans (min_le_right _ _)) hz hzE t

end Woodford.StabilizationWelfare.NonlinearNKMarkovAR1Markov
