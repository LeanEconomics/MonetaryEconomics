/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LinearSystemsStochastic
import PriceLevelDetermination.LocalIFTSystemsBar

/-!
# Local determinacy of `n`-dimensional systems with predetermined variables under uncertainty

Woodford (2003), *Interest and Prices*, Appendix A.3, eqs. (A.11)–(A.13), pp. 633–635. For `n`
equilibrium conditions in the book's stochastic form (A.11),
`E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0` (`x_t ∈ ℝⁿ` adapted, `x_{−1}` given, a bounded
disturbance process `e_t(ω)` in a finite-dimensional space that need not be adapted — date-`t+1`
shocks may sit inside `E_t`), the book asserts, citing Woodford (1986) and without proof, that
the implicit-function theorem applies on sequences of bounded functions with the `L∞` norm,
giving a locally unique bounded equilibrium approximated by the linear rational-expectations
solution. This module proves it for an arbitrary `ExpectationSystem` (core axioms only), with
predetermined variables, at any steady state, with the converse and the correct error bounds.

## Main results

* Nemytskii operators on bounded functions on any index set (`nemI`, `hasStrictFDerivAt_nemI`,
  `contDiff_nemI`).
* The equilibrium map `eqMapS` on `(ℝⁿ × ℓ∞(ℕ × Ω, E)) × ℓ∞(ℕ × Ω, ℝⁿ)`,
  `Φ(u, x)_t = E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] + (x_t − E_t x_t)`: its zeros are exactly the
  adapted solutions (`eqMapS_eq_zero_iff`), it is `C¹` (`contDiff_eqMapS`), and its derivative at
  the steady state is the operator (A.12) `LinearSystemsStochastic.opS` plus the parameter part
  (`eqDS_zero`).
* `local_determinacyS` (**the theorem**): `G` `C¹` near `0`, `G(0) = 0`, (A.12) invertible —
  equivalently the exact root condition of `LinearSystems.linDeterminate_iff` on
  `f_j = D_jG(0)`, for any nonempty `Ω` (`isUnit_linOpS_iff_roots`) — ⟹ for `‖(x_{−1}, e)‖ < δ`
  there is a unique bounded adapted equilibrium within `ε` of the steady state, `C¹` in
  `(x_{−1}, e)`, whose derivative at `0` is the linear RE solution `linSolS`
  (`linSolS_solves`, `eq_linSolS`).
* E18: `first_order_locS` (`o(‖u‖)` for `C¹`), `second_order_globalS`, `second_order_locS`
  (`O(‖u‖²)` for `C²`).
* The converse: `surjective_of_solution_mapS`, `not_locally_uniqueS`,
  `isUnit_of_local_determinacyS`, `isUnit_linOpS_iff_local_determinacyS` — local determinacy with a
  solution map differentiable at the steady state holds iff the root condition holds (when the
  disturbances move every equation).
* Perfect foresight inside uncertainty: `embG`, `embPar`, `solvesSV_embG_iff` (deterministic
  paths are stochastic equilibria iff they are perfect-foresight ones), `linSolS_embPar`;
  `pf_local_determinacy_recovered`: `LocalIFTSystems.local_determinacy` follows from
  `local_determinacyS` for the `perfectForesight` system.
* Any steady state `x̄`: `local_determinacyS_at`, `isUnit_iff_local_determinacyS_at`,
  `second_order_locS_at`.

Only the core `ExpectationSystem` axioms are used: no pull-out property and no informational
closure (the book form (A.11) needs neither).
-/

namespace Woodford.PriceLevelDetermination.LocalIFTSystemsStochastic

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic SystemsBK.GeneralBKForward
open LocalIFTSystems (Arg d1 d2 d3 dE M1 M2 M3 mulVec_M fderiv_zero_apply4 fderiv_close cutoff
  cutoff_eq contDiff_cutoff fderiv_cutoff exists_ball_contDiffAt norm_remainder_le
  lipschitz_fderiv)

/-! ### Nemytskii operators on bounded functions -/

variable {I Q V W : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Woodford (2003), App. A.3, eq. (A.11), p. 633: the Nemytskii (superposition) operator
`q ↦ (F(π_i q))_i` on bounded functions on an index set `I` (here dates and states), built from
coordinate maps `π_i` of norm at most one. -/
noncomputable def nemI (F : V → W) (hF : Continuous F) (pt : I → Q →L[ℝ] V)
    (hpt : ∀ i q, ‖pt i q‖ ≤ ‖q‖) (q : Q) : LocalIFTStochastic.BFun I W :=
  LocalIFTStochastic.mkB (fun i => F (pt i q)) (by
    obtain ⟨C, hC⟩ := LocalIFT.exists_bound_ball3 hF ‖q‖
    exact ⟨C, fun i => hC _ (hpt i q)⟩)

omit [NormedSpace ℝ W] in
/-- Woodford (2003), App. A.3, p. 634: values of the Nemytskii operator. -/
@[simp] theorem nemI_apply (F : V → W) (hF : Continuous F) (pt : I → Q →L[ℝ] V)
    (hpt : ∀ i q, ‖pt i q‖ ≤ ‖q‖) (q : Q) (i : I) : nemI F hF pt hpt q i = F (pt i q) := rfl

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the candidate derivative of the Nemytskii
operator, `dq ↦ (DF(π_i q)(π_i dq))_i`. -/
noncomputable def nemID (F : V → W) (hF : ContDiff ℝ 1 F) (pt : I → Q →L[ℝ] V)
    (hpt : ∀ i q, ‖pt i q‖ ≤ ‖q‖) (q : Q) : Q →L[ℝ] LocalIFTStochastic.BFun I W :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun dq => LocalIFTStochastic.mkB (fun i => fderiv ℝ F (pt i q) (pt i dq)) (by
        obtain ⟨C, hC⟩ := LocalIFT.exists_bound_ball3 (hF.continuous_fderiv one_ne_zero) ‖q‖
        exact ⟨C * ‖dq‖, fun i => ((fderiv ℝ F (pt i q)).le_opNorm _).trans
          (mul_le_mul (hC _ (hpt i q)) (hpt i dq) (norm_nonneg _)
            ((norm_nonneg _).trans (hC _ (hpt i q))))⟩)
      map_add' := fun dq dq' => lp.ext (funext fun i => by simp)
      map_smul' := fun c dq => lp.ext (funext fun i => by simp) }
    (by
      obtain ⟨C, hC⟩ := LocalIFT.exists_bound_ball3 (hF.continuous_fderiv one_ne_zero) ‖q‖
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp))
      refine ⟨C, fun dq => LocalIFTStochastic.norm_le_of_forall (by positivity) fun i => ?_⟩
      exact ((fderiv ℝ F (pt i q)).le_opNorm _).trans
        (mul_le_mul (hC _ (hpt i q)) (hpt i dq) (norm_nonneg _) hC0))

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: values of `nemID`. -/
@[simp] theorem nemID_apply (F : V → W) (hF : ContDiff ℝ 1 F) (pt : I → Q →L[ℝ] V)
    (hpt : ∀ i q, ‖pt i q‖ ≤ ‖q‖) (q dq : Q) (i : I) :
    nemID F hF pt hpt q dq i = fderiv ℝ F (pt i q) (pt i dq) := rfl

/-- Woodford (2003), App. A.3, p. 634: **the Nemytskii operator of a `C¹` map is strictly
Fréchet differentiable at every point** of the space of bounded functions (uniform continuity of
`DF` on bounded sets). -/
theorem hasStrictFDerivAt_nemI {F : V → W} (hF : ContDiff ℝ 1 F) (pt : I → Q →L[ℝ] V)
    (hpt : ∀ i q, ‖pt i q‖ ≤ ‖q‖) (q : Q) :
    HasStrictFDerivAt (nemI F hF.continuous pt hpt) (nemID F hF pt hpt q) q := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close hF ‖q‖ hc
  have hball : Metric.ball (q, q) (δ / 2) ∈ 𝓝 (q, q) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with p hp
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hp
  refine LocalIFTStochastic.norm_le_of_forall (by positivity) (fun i => ?_)
  have hmem : ∀ y : Q, ‖y - q‖ < δ / 2 → pt i y ∈ Metric.ball (pt i q) (δ / 2) := fun y hy => by
    rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
    exact (hpt i _).trans_lt hy
  have key := (convex_ball (pt i q) (δ / 2)).norm_image_sub_le_of_norm_fderiv_le' (f := F)
    (φ := fderiv ℝ F (pt i q)) (C := c) (fun w _ => (hF.differentiable one_ne_zero) w)
    (fun w hw => by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact (hclose (pt i q) w (hpt i q) (by linarith)).le)
    (hmem p.2 hp.2) (hmem p.1 hp.1)
  simp only [lp.coeFn_sub, Pi.sub_apply, nemI_apply, nemID_apply]
  rw [map_sub (pt i)]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
  rw [← map_sub]
  exact hpt i _

/-- Woodford (2003), App. A.3, p. 634: the derivative `q ↦ nemID q` is continuous in operator
norm. -/
theorem continuous_nemID {F : V → W} (hF : ContDiff ℝ 1 F) (pt : I → Q →L[ℝ] V)
    (hpt : ∀ i q, ‖pt i q‖ ≤ ‖q‖) : Continuous (nemID F hF pt hpt) := by
  rw [Metric.continuous_iff]
  intro q ε hε
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close hF ‖q‖ (half_pos hε)
  refine ⟨δ, hδ, fun q' hq' => ?_⟩
  rw [dist_eq_norm] at hq' ⊢
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    (fun dq => ?_)) (half_lt_self hε)
  refine LocalIFTStochastic.norm_le_of_forall (by positivity) (fun i => ?_)
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, nemID_apply]
  rw [← sub_apply]
  refine ((fderiv ℝ F (pt i q') - fderiv ℝ F (pt i q)).le_opNorm _).trans
    (mul_le_mul (hclose _ _ (hpt i q) ?_).le (hpt i dq) (norm_nonneg _) (half_pos hε).le)
  rw [← map_sub]
  exact (hpt i _).trans_lt hq'

/-- Woodford (2003), App. A.3, p. 634: the Nemytskii operator of a `C¹` map is `C¹`. -/
theorem contDiff_nemI {F : V → W} (hF : ContDiff ℝ 1 F) (pt : I → Q →L[ℝ] V)
    (hpt : ∀ i q, ‖pt i q‖ ≤ ‖q‖) : ContDiff ℝ 1 (nemI F hF.continuous pt hpt) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨nemID F hF pt hpt, continuous_nemID hF pt hpt,
      fun q => (hasStrictFDerivAt_nemI hF pt hpt q).hasFDerivAt⟩

/-! ### The stochastic `n`-dimensional class (A.11) -/

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Type*}

/-- Woodford (2003), App. A.3, p. 634: the "parameters" of the stochastic sequence-space
problem — the initial condition `x_{−1}` and the whole bounded disturbance process `e_t(ω)`
(not required to be adapted). -/
abbrev ParS (ι : Type*) [Fintype ι] (E Ω : Type*) [NormedAddCommGroup E] : Type _ :=
  (ι → ℝ) × LocalIFTStochastic.BFun (ℕ × Ω) E

/-- Woodford (2003), App. A.3, eq. (A.11), p. 633: the date-`t`, state-`ω` argument
`(x_{t−1}(ω), x_t(ω), x_{t+1}(ω), e_t(ω))` of the period conditions. -/
def ptS (q : ParS ι E Ω × SProcV ι Ω) (p : ℕ × Ω) : Arg ι E :=
  (lagV q.1.1 (fun s => q.2 (s, p.2)) p.1, q.2 p, q.2 (p.1 + 1, p.2), q.1.2 p)

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: every date-state argument is bounded by the norm of the
point. -/
theorem norm_ptS_le (q : ParS ι E Ω × SProcV ι Ω) (p : ℕ × Ω) : ‖ptS q p‖ ≤ ‖q‖ := by
  obtain ⟨t, ω⟩ := p
  have h1 : ‖lagV q.1.1 (fun s => q.2 (s, ω)) t‖ ≤ ‖q‖ := by
    cases t with
    | zero => exact (norm_fst_le q.1).trans (norm_fst_le q)
    | succ t => exact (LocalIFTStochastic.norm_apply_le q.2 _).trans (norm_snd_le q)
  have h2 : ‖q.2 (t, ω)‖ ≤ ‖q‖ := (LocalIFTStochastic.norm_apply_le q.2 _).trans (norm_snd_le q)
  have h3 : ‖q.2 (t + 1, ω)‖ ≤ ‖q‖ :=
    (LocalIFTStochastic.norm_apply_le q.2 _).trans (norm_snd_le q)
  have h4 : ‖q.1.2 (t, ω)‖ ≤ ‖q‖ :=
    (LocalIFTStochastic.norm_apply_le q.1.2 _).trans ((norm_snd_le q.1).trans (norm_fst_le q))
  rw [ptS, norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
  exact ⟨h1, h2, h3, h4⟩

/-- Woodford (2003), App. A.3, p. 634: the date-state argument as a continuous linear map of norm
at most one. -/
noncomputable def ptSL (p : ℕ × Ω) : ParS ι E Ω × SProcV ι Ω →L[ℝ] Arg ι E :=
  LinearMap.mkContinuous
    { toFun := fun q => ptS q p
      map_add' := fun q q' => by obtain ⟨t, ω⟩ := p; cases t <;> rfl
      map_smul' := fun c q => by obtain ⟨t, ω⟩ := p; cases t <;> rfl }
    1 (fun q => by rw [one_mul]; exact norm_ptS_le q p)

/-- Woodford (2003), App. A.3, p. 634: values of `ptSL`. -/
@[simp] theorem ptSL_apply (p : ℕ × Ω) (q : ParS ι E Ω × SProcV ι Ω) : ptSL p q = ptS q p :=
  rfl

/-- Woodford (2003), App. A.3, p. 634: `ptSL` has norm at most one. -/
theorem norm_ptSL_le (p : ℕ × Ω) (q : ParS ι E Ω × SProcV ι Ω) : ‖ptSL p q‖ ≤ ‖q‖ :=
  norm_ptS_le q p

/-- Woodford (2003), App. A.3, eq. (A.11), p. 633: `x` is an equilibrium of the stochastic
conditions given `u = (x_{−1}, e)`: `x` is adapted and `E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0`
for every date, coordinate and state. -/
def SolvesSV (𝔼 : ExpectationSystem Ω) (G : Arg ι E → (ι → ℝ)) (u : ParS ι E Ω)
    (x : SProcV ι Ω) : Prop :=
  AdaptedV 𝔼 (toP x) ∧ ∀ t i, 𝔼.E t (fun ω => G (ptS (u, x) (t, ω)) i) = 0

variable (𝔼 : ExpectationSystem Ω)
variable [FiniteDimensional ℝ E]

/-- Woodford (2003), App. A.3, eqs. (A.11)–(A.12), pp. 633–634: **the equilibrium map**
`Φ(u, x)_t = E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] + (x_t − E_t x_t)` on
`(ℝⁿ × ℓ∞(ℕ × Ω, E)) × ℓ∞(ℕ × Ω, ℝⁿ)`. -/
noncomputable def eqMapS (G : Arg ι E → (ι → ℝ)) (hG : Continuous G)
    (q : ParS ι E Ω × SProcV ι Ω) : SProcV ι Ω :=
  condEV 𝔼 (nemI G hG ptSL norm_ptSL_le q) + (q.2 - condEV 𝔼 q.2)

/-- Woodford (2003), App. A.3, p. 634: **zeros of the equilibrium map are exactly the adapted
solutions** of (A.11) (apply `E_t`: the adaptedness term has conditional mean zero). -/
theorem eqMapS_eq_zero_iff (G : Arg ι E → (ι → ℝ)) (hG : Continuous G) (u : ParS ι E Ω)
    (x : SProcV ι Ω) : eqMapS 𝔼 G hG (u, x) = 0 ↔ SolvesSV 𝔼 G u x := by
  have hP : ∀ t, toP (eqMapS 𝔼 G hG (u, x)) t =
      (fun i => 𝔼.E t (fun ω => G (ptS (u, x) (t, ω)) i)) +
        (toP x t - fun i => 𝔼.E t (toP x t i)) := fun t => rfl
  have hE : ∀ t i, 𝔼.E t (toP (eqMapS 𝔼 G hG (u, x)) t i) =
      𝔼.E t (fun ω => G (ptS (u, x) (t, ω)) i) := by
    intro t i
    rw [hP t]
    simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub, 𝔼.E_E_self, sub_self, add_zero]
  constructor
  · intro h
    have h0 : toP (eqMapS 𝔼 G hG (u, x)) = 0 := by rw [h]; rfl
    have hc : ∀ t i, 𝔼.E t (fun ω => G (ptS (u, x) (t, ω)) i) = 0 := by
      intro t i
      rw [← hE t i, h0]
      exact map_zero _
    refine ⟨fun t i => ?_, hc⟩
    have e := congrFun (hP t) i
    rw [h0] at e
    simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply, hc t i, zero_add] at e
    exact (sub_eq_zero.mp e.symm).symm
  · rintro ⟨ha, hc⟩
    apply toP_injective
    funext t i
    rw [hP t]
    simp only [Pi.add_apply, Pi.sub_apply, hc t i, ha t i, sub_self, add_zero]
    rfl

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the candidate derivative of the equilibrium
map at `q`. -/
noncomputable def eqDS (G : Arg ι E → (ι → ℝ)) (hG : ContDiff ℝ 1 G)
    (q : ParS ι E Ω × SProcV ι Ω) : ParS ι E Ω × SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  (condEV 𝔼).comp (nemID G hG ptSL norm_ptSL_le q) +
    (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω) -
      (condEV 𝔼).comp (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω)))

/-- Woodford (2003), App. A.3, p. 634: **the equilibrium map is strictly differentiable at
every point**. -/
theorem hasStrictFDerivAt_eqMapS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G)
    (q : ParS ι E Ω × SProcV ι Ω) :
    HasStrictFDerivAt (eqMapS 𝔼 G hG.continuous) (eqDS 𝔼 G hG q) q := by
  have h1 := (condEV 𝔼).hasStrictFDerivAt.comp q (hasStrictFDerivAt_nemI hG ptSL norm_ptSL_le q)
  have h2 := (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω)).hasStrictFDerivAt (x := q)
  have h3 := ((condEV 𝔼).comp
    (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω))).hasStrictFDerivAt (x := q)
  exact h1.add (h2.sub h3)

/-- Woodford (2003), App. A.3, p. 634: the equilibrium map is `C¹`. -/
theorem contDiff_eqMapS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (eqMapS 𝔼 G hG.continuous) :=
  ((condEV 𝔼).contDiff.comp (contDiff_nemI hG ptSL norm_ptSL_le)).add
    (contDiff_snd.sub ((condEV 𝔼).contDiff.comp contDiff_snd))

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the derivative of the conditions with respect
to the parameters `u = (x_{−1}, e)`, state by state: `(f₁ x_{−1} 1_{t=0} + D₄G e_t(ω))`. -/
noncomputable def bOpS (G : Arg ι E → (ι → ℝ)) : ParS ι E Ω →L[ℝ] SProcV ι Ω :=
  LinearMap.mkContinuous
    { toFun := fun u => LocalIFTStochastic.mkB
        (fun p => d1 G (lagV u.1 0 p.1) + dE G (u.2 p))
        ⟨(‖d1 G‖ + ‖dE G‖) * ‖u‖, fun p => by
          have hl : ‖lagV u.1 (0 : ℕ → ι → ℝ) p.1‖ ≤ ‖u‖ :=
            (LocalIFTSystems.norm_lagV_impulse u.1 p.1).trans (norm_fst_le u)
          have he : ‖u.2 p‖ ≤ ‖u‖ := (LocalIFTStochastic.norm_apply_le u.2 p).trans
            (norm_snd_le u)
          calc _ ≤ ‖d1 G (lagV u.1 0 p.1)‖ + ‖dE G (u.2 p)‖ := norm_add_le _ _
            _ ≤ ‖d1 G‖ * ‖u‖ + ‖dE G‖ * ‖u‖ := add_le_add
                (((d1 G).le_opNorm _).trans (mul_le_mul_of_nonneg_left hl (norm_nonneg _)))
                (((dE G).le_opNorm _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _)))
            _ = _ := by ring⟩
      map_add' := fun u v => lp.ext (funext fun p => by
        have hl : lagV (u + v).1 (0 : ℕ → ι → ℝ) p.1 = lagV u.1 0 p.1 + lagV v.1 0 p.1 := by
          cases p.1 <;> simp
        simp only [LocalIFTStochastic.mkB_apply, hl, map_add, Prod.snd_add, lp.coeFn_add,
          Pi.add_apply]
        abel)
      map_smul' := fun c u => lp.ext (funext fun p => by
        have hl : lagV (c • u).1 (0 : ℕ → ι → ℝ) p.1 = c • lagV u.1 0 p.1 := by
          cases p.1 <;> simp
        simp only [LocalIFTStochastic.mkB_apply, hl, map_smul, Prod.smul_snd, lp.coeFn_smul,
          Pi.smul_apply, smul_add, RingHom.id_apply]) }
    (‖d1 G‖ + ‖dE G‖) (fun u => LocalIFTStochastic.norm_le_of_forall (by positivity) fun p => by
      have hl : ‖lagV u.1 (0 : ℕ → ι → ℝ) p.1‖ ≤ ‖u‖ :=
        (LocalIFTSystems.norm_lagV_impulse u.1 p.1).trans (norm_fst_le u)
      have he : ‖u.2 p‖ ≤ ‖u‖ := (LocalIFTStochastic.norm_apply_le u.2 p).trans (norm_snd_le u)
      calc _ ≤ ‖d1 G (lagV u.1 0 p.1)‖ + ‖dE G (u.2 p)‖ := norm_add_le _ _
        _ ≤ ‖d1 G‖ * ‖u‖ + ‖dE G‖ * ‖u‖ := add_le_add
            (((d1 G).le_opNorm _).trans (mul_le_mul_of_nonneg_left hl (norm_nonneg _)))
            (((dE G).le_opNorm _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _)))
        _ = _ := by ring)

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: values of `bOpS`. -/
theorem bOpS_apply (G : Arg ι E → (ι → ℝ)) (u : ParS ι E Ω) (p : ℕ × Ω) :
    bOpS G u p = d1 G (lagV u.1 0 p.1) + dE G (u.2 p) := rfl

variable [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (tool): values of `linS`. -/
theorem linS_apply (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SProcV ι Ω) (p : ℕ × Ω) :
    linS f₁ f₂ f₃ x p =
      f₁ *ᵥ lagV 0 (fun s => x (s, p.2)) p.1 + f₂ *ᵥ x p + f₃ *ᵥ x (p.1 + 1, p.2) := rfl

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the linearised operator with `f_j = D_jG(0)`
(the matrices `LocalIFTSystems.M1`–`M3`) on `ℓ∞(ℕ × Ω, ℝⁿ)`. -/
noncomputable def linOpS (G : Arg ι E → (ι → ℝ)) : SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  opS 𝔼 (M1 G) (M2 G) (M3 G)

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the derivative of the equilibrium map at the
steady state, `(u, x̂) ↦ opS x̂ + E_t[B u]`. -/
noncomputable def eqD0S (G : Arg ι E → (ι → ℝ)) :
    ParS ι E Ω × SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  (linOpS 𝔼 G).comp (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω)) +
    (condEV 𝔼).comp ((bOpS G).comp (ContinuousLinearMap.fst ℝ (ParS ι E Ω) (SProcV ι Ω)))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632, state by state: at the steady state the
pointwise derivative is `f₁ x_{t−1} + f₂ x_t + f₃ x_{t+1} + D₄G e_t`. -/
theorem nemID_zero {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) :
    nemID G hG (ptSL (ι := ι) (E := E) (Ω := Ω)) norm_ptSL_le 0 =
      (linS (M1 G) (M2 G) (M3 G)).comp (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω)) +
        (bOpS G).comp (ContinuousLinearMap.fst ℝ (ParS ι E Ω) (SProcV ι Ω)) := by
  refine ContinuousLinearMap.ext fun q => lp.ext (funext fun p => ?_)
  obtain ⟨t, ω⟩ := p
  have e1 : nemID G hG ptSL norm_ptSL_le 0 q (t, ω) = fderiv ℝ G 0 (ptS q (t, ω)) := by
    rw [nemID_apply, ptSL_apply, ptSL_apply]
    congr 2
    cases t <;> rfl
  have e2 : ((linS (M1 G) (M2 G) (M3 G)).comp
      (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω)) +
      (bOpS G).comp (ContinuousLinearMap.fst ℝ (ParS ι E Ω) (SProcV ι Ω))) q (t, ω) =
      (M1 G *ᵥ lagV 0 (fun s => q.2 (s, ω)) t + M2 G *ᵥ q.2 (t, ω) +
        M3 G *ᵥ q.2 (t + 1, ω)) + (d1 G (lagV q.1.1 0 t) + dE G (q.1.2 (t, ω))) := by
    rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', lp.coeFn_add, Pi.add_apply,
      linS_apply, bOpS_apply]
  rw [e1, e2, ptS, fderiv_zero_apply4, (mulVec_M G _).1, (mulVec_M G _).2.1, (mulVec_M G _).2.2,
    LinearSystems.lagV_split q.1.1 (fun s => q.2 (s, ω)) t, map_add]
  abel

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: **at the steady state the derivative of the
equilibrium map is the operator (A.12)** (plus the parameter part). -/
theorem eqDS_zero {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) :
    eqDS 𝔼 G hG 0 = eqD0S 𝔼 G := by
  rw [eqDS, nemID_zero hG]
  refine ContinuousLinearMap.ext fun q => ?_
  simp only [eqD0S, linOpS, opS, add_apply, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    one_apply_eq_self, map_add]
  abel

/-! ### The linear rational-expectations solution -/

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): conditional expectations of bounded processes are
adapted. -/
theorem adaptedV_condEV (y : SProcV ι Ω) : AdaptedV 𝔼 (toP (condEV 𝔼 y)) := fun t i => by
  change 𝔼.E t (𝔼.E t (fun ω => y (t, ω) i)) = 𝔼.E t (fun ω => y (t, ω) i)
  exact 𝔼.E_E_self t _

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `‖E_t‖ ≤ 1` on vector processes. -/
theorem norm_condEV_le (y : SProcV ι Ω) : ‖condEV 𝔼 y‖ ≤ ‖y‖ :=
  LocalIFTStochastic.norm_le_of_forall (norm_nonneg y) fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i => by
      rw [Real.norm_eq_abs]
      exact 𝔼.abs_E_le (fun ω => abs_apply_le y p.1 ω i) p.1 p.2

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: `E_t` of the parameter part is
`f₁ x_{−1} 1_{t=0} + E_t[D₄G e_t]`. -/
theorem toP_condEV_bOpS (G : Arg ι E → (ι → ℝ)) (u : ParS ι E Ω) (t : ℕ) :
    toP (condEV 𝔼 (bOpS G u)) t =
      mv (M1 G) (lagP u.1 0 t) + fun i => 𝔼.E t (fun ω => dE G (u.2 (t, ω)) i) := by
  funext i ω
  have e : toP (bOpS G u) t i =
      (fun _ => d1 G (lagV u.1 0 t) i) + fun ω' => dE G (u.2 (t, ω')) i := by
    funext ω'
    rfl
  change 𝔼.E t (toP (bOpS G u) t i) ω = _
  rw [e, map_add, 𝔼.const]
  simp only [Pi.add_apply, mv_apply]
  congr 1
  rw [← (mulVec_M G _).1]
  congr 2
  funext j
  cases t <;> rfl

/-- Woodford (2003), App. A.3, p. 634: the inverse of the linearised operator (A.12), when it
exists. -/
noncomputable def linInvS (G : Arg ι E → (ι → ℝ)) : SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  Ring.inverse (linOpS 𝔼 G)

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: `linInvS` is a right inverse. -/
theorem linOpS_linInvS {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G)) (y : SProcV ι Ω) :
    linOpS 𝔼 G (linInvS 𝔼 G y) = y := by
  have h := Ring.mul_inverse_cancel _ hL
  unfold linInvS
  simpa using congrArg (fun T : SProcV ι Ω →L[ℝ] SProcV ι Ω => T y) h

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: `linInvS` is a left inverse. -/
theorem linInvS_linOpS {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G)) (x : SProcV ι Ω) :
    linInvS 𝔼 G (linOpS 𝔼 G x) = x := by
  have h := Ring.inverse_mul_cancel _ hL
  unfold linInvS
  simpa using congrArg (fun T : SProcV ι Ω →L[ℝ] SProcV ι Ω => T x) h

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: **the solution operator of the linear
rational-expectations system**, `u ↦ −(A.12)⁻¹ E_t[B u]`. -/
noncomputable def linSolS (G : Arg ι E → (ι → ℝ)) : ParS ι E Ω →L[ℝ] SProcV ι Ω :=
  -((linInvS 𝔼 G).comp ((condEV 𝔼).comp (bOpS G)))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: `(A.12) x̂ = −E_t[B u]` for `x̂ = linSolS u`. -/
theorem linOpS_linSolS {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G)) (u : ParS ι E Ω) :
    linOpS 𝔼 G (linSolS 𝔼 G u) = -condEV 𝔼 (bOpS G u) := by
  change linOpS 𝔼 G (-(linInvS 𝔼 G (condEV 𝔼 (bOpS G u)))) = _
  rw [map_neg, linOpS_linInvS 𝔼 hL]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.13), p. 634 (tool): `x̂` solves the linear RE system
`f₁ x̂_{t−1} + f₂ x̂_t + f₃ E_t x̂_{t+1} + E_t[D₄G e_t] = 0`, `x̂_{−1} = x_{−1}`, with `x̂` adapted,
iff `(A.12) x̂ = −E_t[B u]`. -/
theorem linOpS_eq_iff (G : Arg ι E → (ι → ℝ)) (u : ParS ι E Ω) (x : SProcV ι Ω) :
    linOpS 𝔼 G x = -condEV 𝔼 (bOpS G u) ↔ AdaptedV 𝔼 (toP x) ∧
      SolvesLinS 𝔼 (M1 G) (M2 G) (M3 G)
        (fun t => -fun i => 𝔼.E t (fun ω => dE G (u.2 (t, ω)) i)) u.1 (toP x) := by
  constructor
  · intro h
    have hp : toP (opS 𝔼 (M1 G) (M2 G) (M3 G) x) = -toP (condEV 𝔼 (bOpS G u)) := by
      change toP (linOpS 𝔼 G x) = _
      rw [h]
      rfl
    have ha : AdaptedV 𝔼 (toP x) := adapted_of_opS 𝔼 _ _ _ x (by
      rw [hp]
      exact SystemsBK.GeneralBK.adaptedV_neg 𝔼 (adaptedV_condEV 𝔼 _))
    refine ⟨ha, (solvesLinS_shift 𝔼 _ _ _ _ _ _).mpr fun t => ?_⟩
    rw [← toP_opS_of_adapted 𝔼 _ _ _ x ha t, hp, Pi.neg_apply, toP_condEV_bOpS]
    abel_nf
  · rintro ⟨ha, hs⟩
    apply toP_injective
    funext t
    have e := (solvesLinS_shift 𝔼 _ _ _ _ _ _).mp hs t
    change toP (opS 𝔼 (M1 G) (M2 G) (M3 G) x) t = -toP (condEV 𝔼 (bOpS G u)) t
    rw [toP_opS_of_adapted 𝔼 _ _ _ x ha t, e, toP_condEV_bOpS]
    abel_nf

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: `linSolS u` is a bounded adapted solution of
the linear RE system `f₁ x̂_{t−1} + f₂ x̂_t + f₃ E_t x̂_{t+1} + E_t[D₄G e_t] = 0`,
`x̂_{−1} = x_{−1}`. -/
theorem linSolS_solves {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G)) (u : ParS ι E Ω) :
    AdaptedV 𝔼 (toP (linSolS 𝔼 G u)) ∧
      SolvesLinS 𝔼 (M1 G) (M2 G) (M3 G)
        (fun t => -fun i => 𝔼.E t (fun ω => dE G (u.2 (t, ω)) i)) u.1 (toP (linSolS 𝔼 G u)) :=
  (linOpS_eq_iff 𝔼 G u _).mp (linOpS_linSolS 𝔼 hL u)

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: the linear RE system has exactly one bounded
adapted solution, `linSolS u`. -/
theorem eq_linSolS {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G)) {u : ParS ι E Ω}
    {x : SProcV ι Ω} (ha : AdaptedV 𝔼 (toP x))
    (hs : SolvesLinS 𝔼 (M1 G) (M2 G) (M3 G)
      (fun t => -fun i => 𝔼.E t (fun ω => dE G (u.2 (t, ω)) i)) u.1 (toP x)) :
    x = linSolS 𝔼 G u := by
  have h := (linOpS_eq_iff 𝔼 G u x).mpr ⟨ha, hs⟩
  rw [← linInvS_linOpS 𝔼 hL x, h, map_neg]
  rfl

/-! ### The implicit-function theorem on `ℓ∞(ℕ × Ω, ℝⁿ)` -/

/-- Woodford (2003), App. A.3, p. 634: the augmented map `(u, x) ↦ (u, Φ(u, x))`. -/
noncomputable def bigMapS (G : Arg ι E → (ι → ℝ)) (hG : Continuous G)
    (q : ParS ι E Ω × SProcV ι Ω) : ParS ι E Ω × SProcV ι Ω :=
  (q.1, eqMapS 𝔼 G hG q)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the augmented map is `C¹`. -/
theorem contDiff_bigMapS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (bigMapS 𝔼 G hG.continuous) :=
  contDiff_fst.prodMk (contDiff_eqMapS 𝔼 hG)

/-- Woodford (2003), App. A.3, p. 634: the derivative of the augmented map at the steady
state. -/
noncomputable def bigDS (G : Arg ι E → (ι → ℝ)) :
    ParS ι E Ω × SProcV ι Ω →L[ℝ] ParS ι E Ω × SProcV ι Ω :=
  (ContinuousLinearMap.fst ℝ (ParS ι E Ω) (SProcV ι Ω)).prod (eqD0S 𝔼 G)

/-- Woodford (2003), App. A.3, p. 634: the inverse of `bigDS`,
`(u, y) ↦ (u, (A.12)⁻¹(y − E_t[B u]))`. -/
noncomputable def bigDInvS (G : Arg ι E → (ι → ℝ)) :
    ParS ι E Ω × SProcV ι Ω →L[ℝ] ParS ι E Ω × SProcV ι Ω :=
  (ContinuousLinearMap.fst ℝ (ParS ι E Ω) (SProcV ι Ω)).prod
    ((linInvS 𝔼 G).comp (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω) -
      (condEV 𝔼).comp ((bOpS G).comp (ContinuousLinearMap.fst ℝ (ParS ι E Ω) (SProcV ι Ω)))))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: `bigDInvS` is a left inverse of `bigDS`. -/
theorem bigDInvS_bigDS {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G))
    (q : ParS ι E Ω × SProcV ι Ω) : bigDInvS 𝔼 G (bigDS 𝔼 G q) = q := by
  refine Prod.ext rfl ?_
  change linInvS 𝔼 G (linOpS 𝔼 G q.2 + condEV 𝔼 (bOpS G q.1) - condEV 𝔼 (bOpS G q.1)) = q.2
  rw [add_sub_cancel_right, linInvS_linOpS 𝔼 hL]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: `bigDInvS` is a right inverse of `bigDS`. -/
theorem bigDS_bigDInvS {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G))
    (q : ParS ι E Ω × SProcV ι Ω) : bigDS 𝔼 G (bigDInvS 𝔼 G q) = q := by
  refine Prod.ext rfl ?_
  change linOpS 𝔼 G (linInvS 𝔼 G (q.2 - condEV 𝔼 (bOpS G q.1))) + condEV 𝔼 (bOpS G q.1) = q.2
  rw [linOpS_linInvS 𝔼 hL, sub_add_cancel]

/-- Woodford (2003), App. A.3, p. 634: when (A.12) is invertible the derivative of the augmented
map is a continuous linear equivalence. -/
noncomputable def bigDEquivS (G : Arg ι E → (ι → ℝ)) (hL : IsUnit (linOpS 𝔼 G)) :
    (ParS ι E Ω × SProcV ι Ω) ≃L[ℝ] (ParS ι E Ω × SProcV ι Ω) :=
  ContinuousLinearEquiv.equivOfInverse (bigDS 𝔼 G) (bigDInvS 𝔼 G) (bigDInvS_bigDS 𝔼 hL)
    (bigDS_bigDInvS 𝔼 hL)

/-- Woodford (2003), App. A.3, p. 634: the derivative of the augmented map at the steady
state. -/
theorem hasFDerivAt_bigMapS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G)
    (hL : IsUnit (linOpS 𝔼 G)) :
    HasFDerivAt (bigMapS 𝔼 G hG.continuous) (bigDEquivS 𝔼 G hL : _ →L[ℝ] _) 0 := by
  have h := (hasStrictFDerivAt_eqMapS 𝔼 hG 0).hasFDerivAt
  rw [eqDS_zero 𝔼 hG] at h
  exact hasFDerivAt_fst.prodMk h

/-- Woodford (2003), App. A.3, pp. 633–634: the local homeomorphism given by the
inverse-function theorem on `L∞` (Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`). -/
noncomputable def homeoS (G : Arg ι E → (ι → ℝ)) (hG : ContDiff ℝ 1 G)
    (hL : IsUnit (linOpS 𝔼 G)) :
    OpenPartialHomeomorph (ParS ι E Ω × SProcV ι Ω) (ParS ι E Ω × SProcV ι Ω) :=
  ((contDiff_bigMapS 𝔼 hG).contDiffAt.hasStrictFDerivAt' (hasFDerivAt_bigMapS 𝔼 hG hL)
    one_ne_zero).toOpenPartialHomeomorph (bigMapS 𝔼 G hG.continuous)

/-- Woodford (2003), App. A.3, p. 634: the locally unique stochastic equilibrium
`x = X(x_{−1}, e)`. -/
noncomputable def implicitSolS (G : Arg ι E → (ι → ℝ)) (hG : ContDiff ℝ 1 G)
    (hL : IsUnit (linOpS 𝔼 G)) (u : ParS ι E Ω) : SProcV ι Ω :=
  ((homeoS 𝔼 G hG hL).symm (u, 0)).2

/-- Woodford (2003), App. A.3, p. 634: the local homeomorphism is the augmented map. -/
theorem homeoS_apply {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (hL : IsUnit (linOpS 𝔼 G))
    (q : ParS ι E Ω × SProcV ι Ω) : homeoS 𝔼 G hG hL q = bigMapS 𝔼 G hG.continuous q := rfl

/-- Woodford (2003), App. A.3, p. 634: the steady state lies in the source. -/
theorem zero_mem_homeoS_source {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G)
    (hL : IsUnit (linOpS 𝔼 G)) : (0 : ParS ι E Ω × SProcV ι Ω) ∈ (homeoS 𝔼 G hG hL).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

omit [DecidableEq ι] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: with `x_{−1} = x̄` and no disturbances the steady state
is an equilibrium. -/
theorem solvesSV_zero {G : Arg ι E → (ι → ℝ)} (h0 : G 0 = 0) :
    SolvesSV 𝔼 G (0 : ParS ι E Ω) (0 : SProcV ι Ω) := by
  refine ⟨fun t i => map_zero _, fun t i => ?_⟩
  have hz : (fun ω => G (ptS ((0 : ParS ι E Ω), (0 : SProcV ι Ω)) (t, ω)) i) = 0 := by
    funext ω
    have hp : ptS ((0 : ParS ι E Ω), (0 : SProcV ι Ω)) (t, ω) = 0 := by
      cases t <;> rfl
    rw [hp, h0]
    rfl
  rw [hz]
  exact map_zero _

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the augmented map fixes the steady state. -/
theorem bigMapS_zero {G : Arg ι E → (ι → ℝ)} (hG : Continuous G) (h0 : G 0 = 0) :
    bigMapS 𝔼 G hG 0 = 0 :=
  Prod.ext rfl ((eqMapS_eq_zero_iff 𝔼 G hG 0 0).mpr (solvesSV_zero 𝔼 h0))

/-- Woodford (2003), App. A.3, p. 634: the steady state lies in the target. -/
theorem zero_mem_homeoS_target {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) : (0 : ParS ι E Ω × SProcV ι Ω) ∈ (homeoS 𝔼 G hG hL).target := by
  have h := (homeoS 𝔼 G hG hL).map_source (zero_mem_homeoS_source 𝔼 hG hL)
  rwa [homeoS_apply, bigMapS_zero 𝔼 hG.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 634: the local inverse maps the steady state to itself. -/
theorem homeoS_symm_zero {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) : (homeoS 𝔼 G hG hL).symm 0 = 0 := by
  have h := (homeoS 𝔼 G hG hL).left_inv (zero_mem_homeoS_source 𝔼 hG hL)
  rwa [homeoS_apply, bigMapS_zero 𝔼 hG.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 634: the local inverse is `C¹` at the steady state. -/
theorem contDiffAt_homeoS_symm {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) : ContDiffAt ℝ 1 (homeoS 𝔼 G hG hL).symm 0 := by
  refine (homeoS 𝔼 G hG hL).contDiffAt_symm (f₀' := bigDEquivS 𝔼 G hL)
    (zero_mem_homeoS_target 𝔼 hG h0 hL) ?_ ?_
  · rw [homeoS_symm_zero 𝔼 hG h0 hL]
    exact hasFDerivAt_bigMapS 𝔼 hG hL
  · rw [homeoS_symm_zero 𝔼 hG h0 hL]
    exact (contDiff_bigMapS 𝔼 hG).contDiffAt

/-- Woodford (2003), App. A.3, p. 634: the derivative of the local inverse at the steady state
is the inverse of the derivative. -/
theorem hasFDerivAt_homeoS_symm {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) :
    HasFDerivAt (homeoS 𝔼 G hG hL).symm ((bigDEquivS 𝔼 G hL).symm : _ →L[ℝ] _) 0 := by
  refine (homeoS 𝔼 G hG hL).hasFDerivAt_symm (zero_mem_homeoS_target 𝔼 hG h0 hL) ?_
  rw [homeoS_symm_zero 𝔼 hG h0 hL]
  exact hasFDerivAt_bigMapS 𝔼 hG hL

/-- Woodford (2003), App. A.3, p. 634: with `x_{−1} = x̄` and no disturbances the equilibrium is
the steady state. -/
theorem implicitSolS_zero {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) : implicitSolS 𝔼 G hG hL 0 = 0 := by
  rw [implicitSolS, Prod.mk_zero_zero, homeoS_symm_zero 𝔼 hG h0 hL]
  rfl

/-- Woodford (2003), App. A.3, pp. 633–634: **the first-order term of the exact stochastic
equilibrium is the linear rational-expectations solution** (A.13). -/
theorem hasFDerivAt_implicitSolS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) : HasFDerivAt (implicitSolS 𝔼 G hG hL) (linSolS 𝔼 G) 0 := by
  have hin : HasFDerivAt (fun u : ParS ι E Ω => ((u, (0 : SProcV ι Ω)) : ParS ι E Ω × SProcV ι Ω))
      (ContinuousLinearMap.inl ℝ (ParS ι E Ω) (SProcV ι Ω)) 0 :=
    (ContinuousLinearMap.inl ℝ (ParS ι E Ω) (SProcV ι Ω)).hasFDerivAt
  have hs : HasFDerivAt (homeoS 𝔼 G hG hL).symm ((bigDEquivS 𝔼 G hL).symm : _ →L[ℝ] _)
      ((0 : ParS ι E Ω), (0 : SProcV ι Ω)) := by
    rw [Prod.mk_zero_zero]
    exact hasFDerivAt_homeoS_symm 𝔼 hG h0 hL
  have h := (ContinuousLinearMap.snd ℝ (ParS ι E Ω) (SProcV ι Ω)).hasFDerivAt.comp
    (0 : ParS ι E Ω) (hs.comp (0 : ParS ι E Ω) hin)
  refine h.congr_fderiv (ContinuousLinearMap.ext (fun u => ?_))
  change linInvS 𝔼 G ((0 : SProcV ι Ω) - condEV 𝔼 (bOpS G u)) =
    -(linInvS 𝔼 G (condEV 𝔼 (bOpS G u)))
  rw [zero_sub, map_neg]

/-- Woodford (2003), App. A.3, pp. 633–634, **global-`C¹` form**: if `G` is `C¹`, `G(0) = 0` and
(A.12) is invertible, there are `ε, δ > 0` such that for `‖(x_{−1}, e)‖ < δ`, `X(x_{−1}, e)` is a
bounded adapted equilibrium with `‖X‖ < ε/2`, `X` is `C¹` there, and every equilibrium with
`‖x‖ < ε` equals `X(x_{−1}, e)`. -/
theorem local_determinacy_globalS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) :
    ∃ ε > 0, ∃ δ > 0, δ ≤ ε ∧
      (∀ u : ParS ι E Ω, ‖u‖ < δ →
        ‖implicitSolS 𝔼 G hG hL u‖ < ε / 2 ∧ SolvesSV 𝔼 G u (implicitSolS 𝔼 G hG hL u) ∧
          ContDiffAt ℝ 1 (implicitSolS 𝔼 G hG hL) u) ∧
      (∀ u : ParS ι E Ω, ‖u‖ < δ → ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesSV 𝔼 G u x →
        x = implicitSolS 𝔼 G hG hL u) := by
  set H := homeoS 𝔼 G hG hL with hH
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (H.open_source.mem_nhds (zero_mem_homeoS_source 𝔼 hG hL))
  have hcd := contDiffAt_homeoS_symm 𝔼 hG h0 hL
  have hsym0 := homeoS_symm_zero 𝔼 hG h0 hL
  have hev1 : ∀ᶠ y in 𝓝 (0 : ParS ι E Ω × SProcV ι Ω), y ∈ H.target :=
    H.open_target.mem_nhds (zero_mem_homeoS_target 𝔼 hG h0 hL)
  have hev2 : ∀ᶠ y in 𝓝 (0 : ParS ι E Ω × SProcV ι Ω), ‖H.symm y‖ < ε / 2 := by
    have ht := hcd.continuousAt.tendsto
    rw [hsym0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds 0 (half_pos hε))).mono
      (fun y hy => by simpa using hy)
  have hev3 : ∀ᶠ y in 𝓝 (0 : ParS ι E Ω × SProcV ι Ω), ContDiffAt ℝ 1 H.symm y :=
    hcd.eventually (by simp)
  have hpull : Filter.Tendsto
      (fun u : ParS ι E Ω => ((u, (0 : SProcV ι Ω)) : ParS ι E Ω × SProcV ι Ω))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous
        (fun u : ParS ι E Ω => ((u, (0 : SProcV ι Ω)) : ParS ι E Ω × SProcV ι Ω)) :=
      continuous_id.prodMk continuous_const
    have h := hc.tendsto (0 : ParS ι E Ω)
    rwa [Prod.mk_zero_zero] at h
  obtain ⟨δ, hδ, hδP⟩ :=
    Metric.eventually_nhds_iff.mp (hpull.eventually (hev1.and (hev2.and hev3)))
  refine ⟨ε, hε, min δ ε, lt_min hδ hε, min_le_right _ _, fun u hu => ?_,
    fun u hu x hx hsol => ?_⟩
  · have huδ : dist u 0 < δ := by
      rw [dist_zero_right]
      exact lt_of_lt_of_le hu (min_le_left _ _)
    obtain ⟨htar, hnorm, hcds⟩ := hδP huδ
    have hright : H (H.symm (u, 0)) = (u, 0) := H.right_inv htar
    have hfst : (H.symm (u, 0)).1 = u := congrArg Prod.fst hright
    have hsnd : eqMapS 𝔼 G hG.continuous (H.symm (u, 0)) = 0 := congrArg Prod.snd hright
    refine ⟨lt_of_le_of_lt (norm_snd_le _) hnorm, ?_, ?_⟩
    · rw [← eqMapS_eq_zero_iff 𝔼 G hG.continuous]
      have hq : ((u, implicitSolS 𝔼 G hG hL u) : ParS ι E Ω × SProcV ι Ω) = H.symm (u, 0) :=
        Prod.ext hfst.symm rfl
      rw [hq]
      exact hsnd
    · exact contDiffAt_snd.comp u (hcds.comp u (contDiffAt_id.prodMk contDiffAt_const))
  · have hsrc : ((u, x) : ParS ι E Ω × SProcV ι Ω) ∈ H.source := by
      apply hεsub
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
      exact max_lt (lt_of_lt_of_le hu (min_le_right _ _)) hx
    have hHx : H (u, x) = (u, 0) :=
      Prod.ext rfl ((eqMapS_eq_zero_iff 𝔼 G hG.continuous u x).mpr hsol)
    have h := H.left_inv hsrc
    rw [hHx] at h
    exact (congrArg Prod.snd h).symm

/-! ### Only the behaviour near the steady state matters -/

/-- Woodford (2003), App. A.3, p. 634: the bump cut-off has the same linearisation. -/
theorem lin_cutoffS (G : Arg ι E → (ι → ℝ)) {r : ℝ} (hr : 0 < r) :
    linOpS 𝔼 (cutoff G r hr) = linOpS 𝔼 G ∧ bOpS (Ω := Ω) (cutoff G r hr) = bOpS G ∧
      linSolS 𝔼 (cutoff G r hr) = linSolS 𝔼 G ∧ dE (cutoff G r hr) = dE G := by
  have h := fderiv_cutoff G hr
  have h1 : linOpS 𝔼 (cutoff G r hr) = linOpS 𝔼 G := by
    simp only [linOpS, M1, M2, M3, d1, d2, d3, h]
  have hd1 : d1 (cutoff G r hr) = d1 G := by simp only [d1, h]
  have hdE : dE (cutoff G r hr) = dE G := by simp only [dE, h]
  have h2 : bOpS (Ω := Ω) (cutoff G r hr) = bOpS G :=
    ContinuousLinearMap.ext fun u => lp.ext (funext fun p => by
      rw [bOpS_apply, bOpS_apply, hd1, hdE])
  refine ⟨h1, h2, ?_, hdE⟩
  simp only [linSolS, linInvS, h1, h2]

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: near the steady state the cut-off conditions and the
original conditions have the same stochastic equilibria. -/
theorem solvesSV_cutoff_iff {G : Arg ι E → (ι → ℝ)} {r : ℝ} (hr : 0 < r) {u : ParS ι E Ω}
    {x : SProcV ι Ω} (hu : ‖u‖ ≤ r / 4) (hx : ‖x‖ ≤ r / 4) :
    SolvesSV 𝔼 (cutoff G r hr) u x ↔ SolvesSV 𝔼 G u x := by
  have hp : ∀ p, cutoff G r hr (ptS (u, x) p) = G (ptS (u, x) p) := fun p =>
    cutoff_eq hr ((norm_ptS_le _ p).trans (by rw [Prod.norm_mk]; exact max_le hu hx))
  unfold SolvesSV
  simp only [hp]

/-- **Woodford (2003), App. A.3, pp. 633–635: local determinacy of `n`-dimensional systems with
predetermined variables under uncertainty.** For any expectation system: if `G` is `C¹` near the
steady state, `G(0) = 0` and the operator (A.12) is invertible on `ℓ∞(ℕ × Ω, ℝⁿ)`
(equivalently, for nonempty `Ω`, the exact root condition: `isUnit_linOpS_iff_roots`), there are
`ε, δ > 0` (below any `η > 0`) and a map `X : (x_{−1}, e) ↦ x` with `X(0) = 0` whose derivative at
`0` is the linear rational-expectations solution (A.13), such that for every initial condition
and bounded disturbance process with `‖(x_{−1}, e)‖ < δ`: `X(x_{−1}, e)` is a bounded adapted
equilibrium of `E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0` within `ε/2` of the steady state, `X` is
`C¹` there, and every bounded adapted equilibrium within `ε` of the steady state equals it. -/
theorem local_determinacyS {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : ParS ι E Ω → SProcV ι Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 G) 0 ∧
      ∀ u : ParS ι E Ω, ‖u‖ < δ → ‖X u‖ < ε / 2 ∧ SolvesSV 𝔼 G u (X u) ∧
        ContDiffAt ℝ 1 X u ∧ ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesSV 𝔼 G u x → x = X u := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hG
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : Arg ι E, ‖p‖ < r → ContDiffAt ℝ 1 G p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set F := cutoff G r hr with hF
  have hF1 : ContDiff ℝ 1 F := contDiff_cutoff hr hball
  obtain ⟨hlo, -, hls, -⟩ := lin_cutoffS 𝔼 G hr
  have hL' : IsUnit (linOpS 𝔼 F) := by rw [hlo]; exact hL
  have hF0 : F 0 = 0 := by rw [hF, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, hex, huniq⟩ := local_determinacy_globalS 𝔼 hF1 hF0 hL'
  set X := implicitSolS 𝔼 F hF1 hL' with hX
  have hX0 : X 0 = 0 := implicitSolS_zero 𝔼 hF1 hF0 hL'
  have hcont : ContinuousAt X 0 := (hasFDerivAt_implicitSolS 𝔼 hF1 hF0 hL').continuousAt
  have hev : ∀ᶠ u in 𝓝 (0 : ParS ι E Ω), ‖X u‖ < r / 8 := by
    have ht := hcont.tendsto
    rw [hX0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds (0 : SProcV ι Ω)
      (by positivity : (0 : ℝ) < r / 8))).mono (fun u hu => by simpa using hu)
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₁) (r / 4), lt_min (lt_min hδ₀ hδ₁) (by positivity),
    (min_le_right _ _).trans hrη, X, hX0, ?_, fun u hu => ?_⟩
  · rw [← hls]
    exact hasFDerivAt_implicitSolS 𝔼 hF1 hF0 hL'
  have hu0 : ‖u‖ < δ₀ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_left _ _))
  have hu1 : dist u 0 < δ₁ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_right _ _))
  have hu4 : ‖u‖ ≤ r / 4 := (lt_of_lt_of_le hu (min_le_right _ _)).le
  obtain ⟨hXn, hXs, hXc⟩ := hex u hu0
  have hXr := hδ₁P hu1
  have hXr4 : ‖X u‖ ≤ r / 4 := by linarith
  refine ⟨by rw [lt_div_iff₀ two_pos]; exact lt_min (by linarith) (by linarith),
    (solvesSV_cutoff_iff 𝔼 hr hu4 hXr4).mp hXs, hXc, fun x hx hsol => ?_⟩
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  exact huniq u hu0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solvesSV_cutoff_iff 𝔼 hr hu4 hx4).mpr hsol)

omit [FiniteDimensional ℝ E] in
/-- **The invertibility condition under uncertainty is the exact root condition** (Woodford
(2003), App. A.3, eqs. (A.9), (A.12), pp. 632–634): for a nonempty state space, with
`f_j = D_jG(0)`, (A.12) is invertible iff `det(f₃λ² + f₂λ + f₁) ≢ 0`, no root lies on the unit
circle, exactly `n` lie inside, and genericity holds — the same condition as for the
perfect-foresight operator (A.8) (`isUnit_linOpS_iff_linOp`). -/
theorem isUnit_linOpS_iff_roots [Nonempty Ω] (G : Arg ι E → (ι → ℝ)) :
    IsUnit (linOpS 𝔼 G) ↔ quadPoly (M1 G) (M2 G) (M3 G) ≠ 0 ∧
      (∀ μ ∈ ((quadPoly (M1 G) (M2 G) (M3 G)).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly (M1 G) (M2 G) (M3 G)).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ HomInjective (M1 G) (M2 G) (M3 G) :=
  isUnit_opS_iff_roots 𝔼 _ _ _

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, pp. 632–634: the stochastic operator (A.12) is invertible iff
the perfect-foresight operator (A.8) of `LocalIFTSystems` is. -/
theorem isUnit_linOpS_iff_linOp [Nonempty Ω] (G : Arg ι E → (ι → ℝ)) :
    IsUnit (linOpS 𝔼 G) ↔ IsUnit (LocalIFTSystems.linOp G) :=
  isUnit_opS_iff_sysOp 𝔼 _ _ _

/-- **Woodford (2003), App. A.3, pp. 633–635, with the root condition made exact**: for a
nonempty state space, the conclusions of `local_determinacyS` hold whenever
`det(f₃λ² + f₂λ + f₁)` (`f_j = D_jG(0)`) is not identically zero, has no root on the unit circle
and exactly `n` roots inside it, and genericity holds. -/
theorem local_determinacyS_of_roots [Nonempty Ω] {G : Arg ι E → (ι → ℝ)}
    (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0) (hreg : quadPoly (M1 G) (M2 G) (M3 G) ≠ 0)
    (hnu : ∀ μ ∈ ((quadPoly (M1 G) (M2 G) (M3 G)).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1)
    (hcount : Multiset.card (((quadPoly (M1 G) (M2 G) (M3 G)).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι)
    (hgen : HomInjective (M1 G) (M2 G) (M3 G)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : ParS ι E Ω → SProcV ι Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 G) 0 ∧
      ∀ u : ParS ι E Ω, ‖u‖ < δ → ‖X u‖ < ε / 2 ∧ SolvesSV 𝔼 G u (X u) ∧
        ContDiffAt ℝ 1 X u ∧ ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesSV 𝔼 G u x → x = X u :=
  local_determinacyS 𝔼 hG h0 ((isUnit_linOpS_iff_roots 𝔼 G).mpr ⟨hreg, hnu, hcount, hgen⟩) hη

/-! ### Accuracy of the linear approximation (erratum E18) -/

/-- Woodford (2003), App. A.3, p. 634, E18 (**first order under `C¹`**): every stochastic
equilibrium near the steady state is within `c ‖(x_{−1}, e)‖` of the linear RE solution, for
every `c > 0` once the disturbances are small enough — an `o(‖u‖)` error. -/
theorem first_order_locS {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) :
    ∃ ε > 0, ∀ c > 0, ∃ δ > 0, ∀ u : ParS ι E Ω, ‖u‖ < δ → ∀ x : SProcV ι Ω, ‖x‖ < ε →
      SolvesSV 𝔼 G u x → ‖x - linSolS 𝔼 G u‖ ≤ c * ‖u‖ := by
  obtain ⟨ε, hε, -, δ₀, hδ₀, -, X, hX0, hXd, hX⟩ := local_determinacyS 𝔼 hG h0 hL one_pos
  refine ⟨ε, hε, fun c hc => ?_⟩
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := Metric.eventually_nhds_iff.mp (hXd.isLittleO.def hc)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun u hu x hx hsol => ?_⟩
  have h1 := hδ₁P (by rw [dist_zero_right]; exact lt_of_lt_of_le hu (min_le_right _ _))
  simp only [hX0, sub_zero] at h1
  rw [(hX u (lt_of_lt_of_le hu (min_le_left _ _))).2.2.2 x hx hsol]
  exact h1

/-- Woodford (2003), App. A.3, p. 634 (tool): for an equilibrium `x`,
`(A.12)(x − x̂) = −E_t[G(π_t) − DG(0) π_t]` — the linearisation error is the conditional
expectation of the pointwise Taylor remainder. -/
theorem linOpS_sub_linSolS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G)
    (hL : IsUnit (linOpS 𝔼 G)) {u : ParS ι E Ω} {x : SProcV ι Ω}
    (hsol : eqMapS 𝔼 G hG.continuous (u, x) = 0) :
    linOpS 𝔼 G (x - linSolS 𝔼 G u) = -condEV 𝔼 (nemI G hG.continuous ptSL norm_ptSL_le (u, x) -
      nemID G hG ptSL norm_ptSL_le 0 (u, x)) := by
  have hD : eqD0S 𝔼 G (u, x) = eqDS 𝔼 G hG 0 (u, x) := by rw [eqDS_zero 𝔼 hG]
  have e1 : linOpS 𝔼 G (x - linSolS 𝔼 G u) = eqD0S 𝔼 G (u, x) := by
    rw [map_sub, linOpS_linSolS 𝔼 hL, sub_neg_eq_add]
    rfl
  rw [e1, hD, ← sub_zero (eqDS 𝔼 G hG 0 (u, x)), ← hsol]
  change condEV 𝔼 (nemID G hG ptSL norm_ptSL_le 0 (u, x)) + (x - condEV 𝔼 x) -
    (condEV 𝔼 (nemI G hG.continuous ptSL norm_ptSL_le (u, x)) + (x - condEV 𝔼 x)) = _
  rw [map_sub]
  abel

/-- Woodford (2003), App. A.3, p. 634, corrected per E18 (**global form**): if `DG` is Lipschitz
near the steady state, the exact stochastic equilibrium differs from the linear RE solution by
at most `C ‖(x_{−1}, e)‖²`. -/
theorem second_order_globalS {G : Arg ι E → (ι → ℝ)} (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) {K r : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ z : Arg ι E, ‖z‖ ≤ r → ‖fderiv ℝ G z - fderiv ℝ G 0‖ ≤ K * ‖z‖) (hr : 0 < r) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ u : ParS ι E Ω, ‖u‖ < δ →
      ‖implicitSolS 𝔼 G hG hL u - linSolS 𝔼 G u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨ε, hε, δ₁, hδ₁, -, hex, -⟩ := local_determinacy_globalS 𝔼 hG h0 hL
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ :=
    Metric.eventually_nhds_iff.mp ((hasFDerivAt_implicitSolS 𝔼 hG h0 hL).isLittleO.def one_pos)
  set C1 := ‖linSolS 𝔼 G‖ + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  have hC1one : 1 ≤ C1 := le_add_of_nonneg_left (norm_nonneg _)
  refine ⟨‖linInvS 𝔼 G‖ * (K * C1 ^ 2), min (min δ₁ δ₂) (r / C1), by positivity,
    fun u hu => ?_⟩
  have hu1 : ‖u‖ < δ₁ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_left _ _))
  have hu2 : dist u 0 < δ₂ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_right _ _))
  have hu3 : C1 * ‖u‖ ≤ r := by
    have h : ‖u‖ < r / C1 := lt_of_lt_of_le hu (min_le_right _ _)
    rw [lt_div_iff₀ hC1pos] at h
    linarith
  obtain ⟨-, hsol, -⟩ := hex u hu1
  set x := implicitSolS 𝔼 G hG hL u with hx
  have hxb : ‖x‖ ≤ C1 * ‖u‖ := by
    have h := hδ₂P hu2
    rw [implicitSolS_zero 𝔼 hG h0 hL, sub_zero, sub_zero, one_mul] at h
    calc ‖x‖ = ‖(x - linSolS 𝔼 G u) + linSolS 𝔼 G u‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - linSolS 𝔼 G u‖ + ‖linSolS 𝔼 G u‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖linSolS 𝔼 G‖ * ‖u‖ := add_le_add h ((linSolS 𝔼 G).le_opNorm u)
      _ = C1 * ‖u‖ := by rw [hC1]; ring
  have hzero := (eqMapS_eq_zero_iff 𝔼 G hG.continuous u x).mpr hsol
  have hrem : ‖nemI G hG.continuous ptSL norm_ptSL_le (u, x) -
      nemID G hG ptSL norm_ptSL_le 0 (u, x)‖ ≤ K * (C1 * ‖u‖) ^ 2 := by
    refine LocalIFTStochastic.norm_le_of_forall (by positivity) fun p => ?_
    have hz : ‖ptS (u, x) p‖ ≤ C1 * ‖u‖ := by
      refine (norm_ptS_le _ p).trans ?_
      rw [Prod.norm_mk]
      exact max_le (le_mul_of_one_le_left (norm_nonneg _) hC1one) hxb
    have h := norm_remainder_le hG hK hLip _ (hz.trans hu3)
    rw [h0, sub_zero] at h
    have e : (nemI G hG.continuous ptSL norm_ptSL_le (u, x) -
        nemID G hG ptSL norm_ptSL_le 0 (u, x)) p =
        G (ptS (u, x) p) - fderiv ℝ G 0 (ptS (u, x) p) := by
      rw [lp.coeFn_sub, Pi.sub_apply, nemI_apply, nemID_apply, map_zero, ptSL_apply]
    rw [e]
    calc _ ≤ K * ‖ptS (u, x) p‖ ^ 2 := h
      _ ≤ K * (C1 * ‖u‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) hK
  have hlin : ‖linOpS 𝔼 G (x - linSolS 𝔼 G u)‖ ≤ K * (C1 * ‖u‖) ^ 2 := by
    rw [linOpS_sub_linSolS 𝔼 hG hL hzero, norm_neg]
    exact (norm_condEV_le 𝔼 _).trans hrem
  calc ‖x - linSolS 𝔼 G u‖ = ‖linInvS 𝔼 G (linOpS 𝔼 G (x - linSolS 𝔼 G u))‖ := by
        rw [linInvS_linOpS 𝔼 hL]
    _ ≤ ‖linInvS 𝔼 G‖ * ‖linOpS 𝔼 G (x - linSolS 𝔼 G u)‖ := (linInvS 𝔼 G).le_opNorm _
    _ ≤ ‖linInvS 𝔼 G‖ * (K * (C1 * ‖u‖) ^ 2) := mul_le_mul_of_nonneg_left hlin (norm_nonneg _)
    _ = ‖linInvS 𝔼 G‖ * (K * C1 ^ 2) * ‖u‖ ^ 2 := by ring

/-- Woodford (2003), App. A.3, p. 634 ("coincides with this solution … up to an error term of
order `O(‖u‖²)`"), **local form**, corrected per E18: if `G` is `C²` near the steady state, every
bounded adapted equilibrium within `ε` of the steady state satisfies
`‖x − x̂(x_{−1}, e)‖ ≤ C ‖(x_{−1}, e)‖²` for `‖(x_{−1}, e)‖ < δ`, `x̂` the linear RE solution. -/
theorem second_order_locS {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 2 G 0) (h0 : G 0 = 0)
    (hL : IsUnit (linOpS 𝔼 G)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ C : ℝ, ∀ u : ParS ι E Ω, ‖u‖ < δ →
      ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesSV 𝔼 G u x → ‖x - linSolS 𝔼 G u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hG
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : Arg ι E, ‖p‖ < r → ContDiffAt ℝ 2 G p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set F := cutoff G r hr with hF
  have hF2 : ContDiff ℝ 2 F := contDiff_cutoff hr hball
  have hF1 : ContDiff ℝ 1 F := hF2.of_le (by norm_num)
  obtain ⟨hlo, -, hls, -⟩ := lin_cutoffS 𝔼 G hr
  have hL' : IsUnit (linOpS 𝔼 F) := by rw [hlo]; exact hL
  have hF0 : F 0 = 0 := by rw [hF, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, -, huniq⟩ := local_determinacy_globalS 𝔼 hF1 hF0 hL'
  obtain ⟨K, r', hK, hr', hLip⟩ := lipschitz_fderiv hF2
  obtain ⟨C, δ₂, hδ₂, hC⟩ := second_order_globalS 𝔼 hF1 hF0 hL' hK hLip hr'
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₂) (r / 4), lt_min (lt_min hδ₀ hδ₂) (by positivity),
    (min_le_right _ _).trans hrη, C, fun u hu x hx hsol => ?_⟩
  have hu0 : ‖u‖ < δ₀ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_left _ _))
  have hu2 : ‖u‖ < δ₂ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_right _ _))
  have hu4 : ‖u‖ ≤ r / 4 := (lt_of_lt_of_le hu (min_le_right _ _)).le
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  have hxX := huniq u hu0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solvesSV_cutoff_iff 𝔼 hr hu4 hx4).mpr hsol)
  rw [← hls, hxX]
  exact hC u hu2

/-! ### Perfect foresight inside uncertainty: deterministic paths -/

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `E_t` applied twice, `E_t(y_t − E_t y_t) = 0`. -/
theorem condEV_sub_condEV (y : SProcV ι Ω) : condEV 𝔼 (y - condEV 𝔼 y) = 0 := by
  ext ⟨t, ω⟩ i
  change 𝔼.E t (toP y t i - 𝔼.E t (toP y t i)) ω = 0
  rw [map_sub, 𝔼.E_E_self, sub_self]
  rfl

/-- Woodford (2003), App. A.3, p. 634: a deterministic bounded sequence as a bounded process (the
same value in every state). -/
noncomputable def embG (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    LocalIFT.Seq V →L[ℝ] LocalIFTStochastic.BFun (ℕ × Ω) V :=
  LinearMap.mkContinuous
    { toFun := fun z => LocalIFTStochastic.mkB (fun p => z p.1)
        ⟨‖z‖, fun p => LocalIFT.norm_seq_apply_le z p.1⟩
      map_add' := fun z z' => lp.ext (funext fun p => rfl)
      map_smul' := fun c z => lp.ext (funext fun p => rfl) }
    1 (fun z => by
      rw [one_mul]
      exact LocalIFTStochastic.norm_le_of_forall (norm_nonneg _) fun p =>
        LocalIFT.norm_seq_apply_le z p.1)

/-- Woodford (2003), App. A.3, p. 634: values of the deterministic embedding. -/
@[simp] theorem embG_apply (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (z : LocalIFT.Seq V) (p : ℕ × Ω) : embG V z p = z p.1 := rfl

/-- Woodford (2003), App. A.3, p. 634: on a nonempty state space the deterministic embedding is
an isometry. -/
theorem norm_embG [Nonempty Ω] (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (z : LocalIFT.Seq V) : ‖embG (Ω := Ω) V z‖ = ‖z‖ := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  refine le_antisymm (LocalIFTStochastic.norm_le_of_forall (norm_nonneg _) fun p =>
    LocalIFT.norm_seq_apply_le z p.1) (LocalIFT.norm_seq_le (norm_nonneg _) fun t => ?_)
  have h := LocalIFTStochastic.norm_apply_le (embG (Ω := Ω) V z) (t, ω₀)
  rwa [embG_apply] at h

/-- Woodford (2003), App. A.3, p. 634: deterministic parameters `(x_{−1}, e)` as stochastic
ones. -/
noncomputable def embPar : LocalIFTSystems.Par ι E →L[ℝ] ParS ι E Ω :=
  (ContinuousLinearMap.fst ℝ (ι → ℝ) (LocalIFT.Seq E)).prod
    ((embG E).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (LocalIFT.Seq E)))

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: the embedding of parameters does not increase norms. -/
theorem norm_embPar_le (u : LocalIFTSystems.Par ι E) : ‖embPar (Ω := Ω) u‖ ≤ ‖u‖ := by
  change ‖((u.1, embG E u.2) : ParS ι E Ω)‖ ≤ ‖u‖
  rw [Prod.norm_mk, Prod.norm_def]
  refine max_le_max le_rfl (LocalIFTStochastic.norm_le_of_forall (norm_nonneg _) fun p =>
    LocalIFT.norm_seq_apply_le u.2 p.1)

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): the process of an embedded sequence. -/
theorem toP_embG (z : SeqV ι) : toP (embG (Ω := Ω) (ι → ℝ) z) = fun t i _ => z t i := rfl

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): embedded sequences are adapted. -/
theorem adaptedV_embG (z : SeqV ι) : AdaptedV 𝔼 (toP (embG (Ω := Ω) (ι → ℝ) z)) := by
  rw [toP_embG]
  exact fun t i => 𝔼.const t _

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, pp. 631–634: **a deterministic path is a stochastic equilibrium
with deterministic parameters iff it is a perfect-foresight equilibrium** (`LocalIFTSystems`),
for every expectation system on a nonempty state space. -/
theorem solvesSV_embG_iff [Nonempty Ω] (G : Arg ι E → (ι → ℝ)) (u : LocalIFTSystems.Par ι E)
    (z : SeqV ι) :
    SolvesSV 𝔼 G (embPar u) (embG (ι → ℝ) z) ↔ LocalIFTSystems.Solves G u z := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hp : ∀ t (ω : Ω), ptS (embPar u, embG (ι → ℝ) z) (t, ω) =
      (lagV u.1 (fun s => z s) t, z t, z (t + 1), u.2 t) := by
    intro t ω
    cases t <;> rfl
  constructor
  · rintro ⟨-, h⟩ t
    funext i
    have := congrFun (h t i) ω₀
    simp only [hp] at this
    rw [𝔼.const] at this
    exact this
  · intro h
    refine ⟨adaptedV_embG 𝔼 z, fun t i => ?_⟩
    simp only [hp, h t, Pi.zero_apply]
    exact 𝔼.const t 0

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, pp. 632–634: (A.12) onto implies (A.8) onto (a deterministic
forcing with no bounded perfect-foresight solution has no stochastic one). -/
theorem sysOp_surjective_of_opS [Nonempty Ω] {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (hs : Function.Surjective (opS 𝔼 f₁ f₂ f₃)) : Function.Surjective (sysOp f₁ f₂ f₃) := by
  by_contra hns
  obtain ⟨W, hWb, hno⟩ := (nonexistS_iff 𝔼 f₁ f₂ f₃).mpr hns
  obtain ⟨x, hx⟩ := hs (ofP (detP W) (boundedV_detP hWb))
  have hxp : toP (opS 𝔼 f₁ f₂ f₃ x) = detP W := by rw [hx]; rfl
  have ha := adapted_of_opS 𝔼 f₁ f₂ f₃ x (by rw [hxp]; exact adaptedV_detP 𝔼 W)
  exact hno (toP x) (boundedV_toP x) fun t => by
    rw [← toP_opS_of_adapted 𝔼 f₁ f₂ f₃ x ha t, hxp]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, pp. 632–634: (A.12) not one-to-one implies (A.8) not one-to-one
(a nonzero adapted solution of the homogeneous system projects to a perfect-foresight one). -/
theorem sysOp_not_injective_of_opS [Nonempty Ω] {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (h : ¬ Function.Injective (opS 𝔼 f₁ f₂ f₃)) : ¬ Function.Injective (sysOp f₁ f₂ f₃) := by
  rw [← nonuniqueS_iff 𝔼]
  simp only [Function.Injective, not_forall] at h
  obtain ⟨a, b, hab, hne⟩ := h
  have hd : opS 𝔼 f₁ f₂ f₃ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hdp : toP (opS 𝔼 f₁ f₂ f₃ (a - b)) = 0 := by rw [hd]; rfl
  have ha := adapted_of_opS 𝔼 f₁ f₂ f₃ (a - b) (by rw [hdp]; exact fun _ _ => map_zero _)
  refine ⟨toP (a - b), boundedV_toP _, ha, fun t => ?_, fun h0 => hne ?_⟩
  · rw [← toP_opS_of_adapted 𝔼 _ _ _ (a - b) ha t, hdp]
  · exact sub_eq_zero.mp (toP_injective (h0.trans toP_zero.symm))

/-! ### Necessity: what fails when the root condition fails -/

/-- Woodford (2003), App. A.3, p. 634 (**necessity, existence half**): if the disturbances can
move every equation independently (`D₄G(0)` onto) and there is a solution map `X` with
`X(0) = 0`, differentiable at the steady state, then the operator (A.12) is onto: differentiating
`Φ(u, X(u)) = 0` puts every `E_t y` in its range, and the adaptedness term covers the rest. -/
theorem surjective_of_solution_mapS {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (hE : Function.Surjective (dE G)) {X : ParS ι E Ω → SProcV ι Ω} {δ : ℝ}
    (hδ : 0 < δ) (hX0 : X 0 = 0) (hXd : DifferentiableAt ℝ X 0)
    (hX : ∀ u : ParS ι E Ω, ‖u‖ < δ → SolvesSV 𝔼 G u (X u)) :
    Function.Surjective (linOpS 𝔼 G) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt hG
  set F := cutoff G r hr with hF
  have hF1 : ContDiff ℝ 1 F := contDiff_cutoff hr hball
  obtain ⟨hlo, hbo, -, -⟩ := lin_cutoffS 𝔼 G hr
  have hev : (fun u => eqMapS 𝔼 F hF1.continuous (u, X u)) =ᶠ[𝓝 0] fun _ => 0 := by
    have h1 : ∀ᶠ u in 𝓝 (0 : ParS ι E Ω), ‖X u‖ < r / 4 := by
      have ht := hXd.continuousAt.tendsto
      rw [hX0] at ht
      exact (ht.eventually (Metric.ball_mem_nhds (0 : SProcV ι Ω)
        (by positivity : (0 : ℝ) < r / 4))).mono (fun u hu => by simpa using hu)
    have h2 : ∀ᶠ u in 𝓝 (0 : ParS ι E Ω), ‖u‖ < min δ (r / 4) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ParS ι E Ω)
        (lt_min hδ (by positivity : (0 : ℝ) < r / 4))] with u hu
      rwa [mem_ball_zero_iff] at hu
    filter_upwards [h1, h2] with u hu1 hu2
    rw [eqMapS_eq_zero_iff]
    exact (solvesSV_cutoff_iff 𝔼 hr (hu2.le.trans (min_le_right _ _)) hu1.le).mpr
      (hX u (hu2.trans_le (min_le_left _ _)))
  have hn := (hasStrictFDerivAt_eqMapS 𝔼 hF1 0).hasFDerivAt
  rw [eqDS_zero 𝔼 hF1] at hn
  have hp : HasFDerivAt (fun u : ParS ι E Ω => ((u, X u) : ParS ι E Ω × SProcV ι Ω))
      ((ContinuousLinearMap.id ℝ (ParS ι E Ω)).prod (fderiv ℝ X 0)) 0 :=
    (hasFDerivAt_id (0 : ParS ι E Ω)).prodMk hXd.hasFDerivAt
  have hp0 : ((0 : ParS ι E Ω), X 0) = (0 : ParS ι E Ω × SProcV ι Ω) := by rw [hX0]; rfl
  rw [← hp0] at hn
  have hD := hn.comp (0 : ParS ι E Ω) hp
  have hc : HasFDerivAt (fun u => eqMapS 𝔼 F hF1.continuous (u, X u))
      (0 : ParS ι E Ω →L[ℝ] SProcV ι Ω) 0 :=
    (hasFDerivAt_const (0 : SProcV ι Ω) (0 : ParS ι E Ω)).congr_of_eventuallyEq hev
  have hzero := hD.unique hc
  obtain ⟨g, hg⟩ := (dE G : E →ₗ[ℝ] (ι → ℝ)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hE)
  set R : (ι → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap g with hR
  have hRinv : ∀ v, dE G (R v) = v := fun v => by
    have := congrArg (fun φ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) => φ v) hg
    simpa [hR] using this
  have hrange : ∀ y : SProcV ι Ω, ∃ z, linOpS 𝔼 G z = condEV 𝔼 y := by
    intro y
    set e : LocalIFTStochastic.BFun (ℕ × Ω) E := LocalIFTStochastic.mkB (fun p => R (-y p))
      ⟨‖R‖ * ‖y‖, fun p => (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (by rw [norm_neg]; exact LocalIFTStochastic.norm_apply_le y p) (norm_nonneg _))⟩ with he
    set du : ParS ι E Ω := (0, e) with hdu
    refine ⟨fderiv ℝ X 0 du, ?_⟩
    have h1 := congrArg (fun T : ParS ι E Ω →L[ℝ] SProcV ι Ω => T du) hzero
    change linOpS 𝔼 F (fderiv ℝ X 0 du) + condEV 𝔼 (bOpS F du) = 0 at h1
    rw [hlo, hbo] at h1
    have hb : bOpS G du = -y := by
      refine lp.ext (funext fun p => ?_)
      rw [bOpS_apply]
      have hl : lagV (0 : ι → ℝ) (0 : ℕ → ι → ℝ) p.1 = 0 := by cases p.1 <;> rfl
      simp only [hdu, he, hl, map_zero, zero_add, LocalIFTStochastic.mkB_apply, hRinv,
        lp.coeFn_neg, Pi.neg_apply]
    rw [hb, map_neg] at h1
    exact add_neg_eq_zero.mp h1
  intro y
  obtain ⟨z₁, hz₁⟩ := hrange y
  have hPb : condEV 𝔼 (y - condEV 𝔼 y) = 0 := condEV_sub_condEV 𝔼 y
  obtain ⟨z₂, hz₂⟩ := hrange (linS (M1 G) (M2 G) (M3 G) (y - condEV 𝔼 y))
  refine ⟨z₁ + (y - condEV 𝔼 y) - z₂, ?_⟩
  have hb' : linOpS 𝔼 G (y - condEV 𝔼 y) =
      condEV 𝔼 (linS (M1 G) (M2 G) (M3 G) (y - condEV 𝔼 y)) + (y - condEV 𝔼 y) := by
    change condEV 𝔼 (linS (M1 G) (M2 G) (M3 G) (y - condEV 𝔼 y)) +
      ((y - condEV 𝔼 y) - condEV 𝔼 (y - condEV 𝔼 y)) = _
    rw [hPb, sub_zero]
  rw [map_sub, map_add, hz₁, hb', hz₂]
  abel

/-- Woodford (2003), App. A.3, pp. 633–634 (**necessity, uniqueness half**): on a nonempty
state space, if (A.12) is onto but not one-to-one, local uniqueness fails — there are bounded
adapted equilibria other than the steady state, with `x_{−1} = x̄` and no disturbances,
arbitrarily close to it (deterministic ones: the perfect-foresight manifold of
`LocalIFTSystems.not_locally_unique`, through `sysOp_surjective_of_opS` and
`sysOp_not_injective_of_opS`). -/
theorem not_locally_uniqueS [Nonempty Ω] {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (h0 : G 0 = 0) (hs : Function.Surjective (linOpS 𝔼 G))
    (hni : ¬ Function.Injective (linOpS 𝔼 G)) :
    ∀ ε > 0, ∃ x : SProcV ι Ω, x ≠ 0 ∧ ‖x‖ < ε ∧ SolvesSV 𝔼 G 0 x := by
  intro ε hε
  obtain ⟨z, hz0, hzε, hzs⟩ := LocalIFTSystems.not_locally_unique hG h0
    (sysOp_surjective_of_opS 𝔼 hs) (sysOp_not_injective_of_opS 𝔼 hni) ε hε
  refine ⟨embG (ι → ℝ) z, fun h => hz0 ?_, by rw [norm_embG]; exact hzε, ?_⟩
  · rw [← norm_eq_zero, ← norm_embG (Ω := Ω), h, norm_zero]
  · have e : (0 : ParS ι E Ω) = embPar 0 := (map_zero _).symm
    rw [e]
    exact (solvesSV_embG_iff 𝔼 G 0 z).mpr hzs

/-- **The converse of the stochastic local determinacy theorem** (Woodford (2003), App. A.3,
pp. 633–634): on a nonempty state space, if the disturbances move every equation independently
(`D₄G(0)` onto) and the exact model is locally determinate *with a solution map differentiable at
the steady state* — some `X` with `X(0) = 0`, differentiable at `0`, solving the conditions for
small `(x_{−1}, e)`, and the steady state the only equilibrium within `ε` when `x_{−1} = x̄`,
`e = 0` — then (A.12) is invertible, i.e. the root condition holds. -/
theorem isUnit_of_local_determinacyS [Nonempty Ω] {G : Arg ι E → (ι → ℝ)}
    (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0) (hE : Function.Surjective (dE G))
    {X : ParS ι E Ω → SProcV ι Ω} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hX0 : X 0 = 0)
    (hXd : DifferentiableAt ℝ X 0) (hX : ∀ u : ParS ι E Ω, ‖u‖ < δ → SolvesSV 𝔼 G u (X u))
    (huniq : ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesSV 𝔼 G 0 x → x = 0) : IsUnit (linOpS 𝔼 G) := by
  have hs := surjective_of_solution_mapS 𝔼 hG hE hδ hX0 hXd hX
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨?_, hs⟩
  by_contra hni
  obtain ⟨x, hx0, hxε, hxs⟩ := not_locally_uniqueS 𝔼 hG h0 hs hni ε hε
  exact hx0 (huniq x hxε hxs)

/-- **Stochastic local determinacy with a first-order approximation holds exactly under the
root condition** (Woodford (2003), App. A.3, pp. 633–634): on a nonempty state space, for `G`
`C¹` near the steady state with `G(0) = 0` and `D₄G(0)` onto, (A.12) is invertible —
equivalently the exact root condition (`isUnit_linOpS_iff_roots`) — iff there are `ε, δ > 0` and
a solution map `X` with `X(0) = 0`, differentiable at `0`, giving for every `‖(x_{−1}, e)‖ < δ`
a bounded adapted equilibrium which is the only one within `ε` of the steady state. -/
theorem isUnit_linOpS_iff_local_determinacyS [Nonempty Ω] {G : Arg ι E → (ι → ℝ)}
    (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0) (hE : Function.Surjective (dE G)) :
    IsUnit (linOpS 𝔼 G) ↔ ∃ ε > 0, ∃ δ > 0, ∃ X : ParS ι E Ω → SProcV ι Ω, X 0 = 0 ∧
      DifferentiableAt ℝ X 0 ∧ ∀ u : ParS ι E Ω, ‖u‖ < δ → SolvesSV 𝔼 G u (X u) ∧
        ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesSV 𝔼 G u x → x = X u := by
  constructor
  · intro hL
    obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ := local_determinacyS 𝔼 hG h0 hL one_pos
    exact ⟨ε, hε, δ, hδ, X, hX0, hXd.differentiableAt, fun u hu =>
      ⟨(hX u hu).2.1, (hX u hu).2.2.2⟩⟩
  · rintro ⟨ε, hε, δ, hδ, X, hX0, hXd, hX⟩
    refine isUnit_of_local_determinacyS 𝔼 hG h0 hE hε hδ hX0 hXd (fun u hu => (hX u hu).1)
      fun x hx hsol => ?_
    rw [(hX 0 (by rw [norm_zero]; exact hδ)).2 x hx hsol, hX0]

/-! ### Perfect foresight recovers `LocalIFTSystems` -/

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, pp. 632–634: with deterministic parameters the linear RE solution
is the deterministic solution of (A.10), `LocalIFTSystems.linSol`. -/
theorem linSolS_embPar [Nonempty Ω] {G : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOpS 𝔼 G))
    (u : LocalIFTSystems.Par ι E) :
    linSolS 𝔼 G (embPar u) = embG (ι → ℝ) (LocalIFTSystems.linSol G u) := by
  have hLP : IsUnit (LocalIFTSystems.linOp G) := (isUnit_linOpS_iff_linOp 𝔼 G).mp hL
  set z := LocalIFTSystems.linSol G u with hz
  symm
  refine eq_linSolS 𝔼 hL (adaptedV_embG 𝔼 z) fun t => ?_
  have hPF := LocalIFTSystems.linSol_solves hLP u t
  have hl : lagP (embPar (Ω := Ω) u).1 (toP (embG (ι → ℝ) z)) t =
      fun i (_ : Ω) => lagV u.1 (fun s => z s) t i := by
    cases t <;> rfl
  have hx : toP (embG (Ω := Ω) (ι → ℝ) z) t = fun i _ => z t i := rfl
  have hE1 : (fun i => 𝔼.E t (toP (embG (Ω := Ω) (ι → ℝ) z) (t + 1) i)) =
      fun i _ => z (t + 1) i := by
    rw [toP_embG]
    exact funext fun i => 𝔼.const t _
  have hE2 : (fun i => 𝔼.E t (fun ω => dE G ((embPar (Ω := Ω) u).2 (t, ω)) i)) =
      fun i _ => dE G (u.2 t) i := funext fun i => by
    change 𝔼.E t (fun _ => dE G (u.2 t) i) = _
    exact 𝔼.const t _
  rw [hl, hx, hE1]
  beta_reduce
  rw [hE2, mv_cst, mv_cst, mv_cst]
  funext i ω
  have h := congrFun hPF i
  simp only [Pi.add_apply, Pi.zero_apply] at h
  simp only [Pi.add_apply, Pi.neg_apply, (mulVec_M G _).1, (mulVec_M G _).2.1,
    (mulVec_M G _).2.2]
  linarith

/-- Woodford (2003), App. A.3, p. 634 (tool): a process on the one-state space as a sequence. -/
noncomputable def unembS : SProcV ι Unit →L[ℝ] SeqV ι :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFT.mkS (fun t => x (t, ()))
        ⟨‖x‖, fun t => LocalIFTStochastic.norm_apply_le x (t, ())⟩
      map_add' := fun x y => lp.ext (funext fun t => rfl)
      map_smul' := fun c x => lp.ext (funext fun t => rfl) }
    1 (fun x => by
      rw [one_mul]
      exact LocalIFT.norm_seq_le (norm_nonneg _) fun t => LocalIFTStochastic.norm_apply_le x _)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): under perfect foresight every process is
deterministic. -/
theorem embG_unembS (x : SProcV ι Unit) : embG (ι → ℝ) (unembS x) = x :=
  lp.ext (funext fun p => by obtain ⟨t, ⟨⟩⟩ := p; rfl)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `unembS` inverts the embedding. -/
theorem unembS_embG (z : SeqV ι) : unembS (embG (Ω := Unit) (ι → ℝ) z) = z :=
  lp.ext (funext fun _ => rfl)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `unembS` does not increase norms. -/
theorem norm_unembS_le (x : SProcV ι Unit) : ‖unembS x‖ ≤ ‖x‖ :=
  LocalIFT.norm_seq_le (norm_nonneg _) fun t => LocalIFTStochastic.norm_apply_le x (t, ())

/-- **Perfect foresight recovers `LocalIFTSystems`** (Woodford (2003), App. A.3, pp. 631–633):
the perfect-foresight local determinacy theorem `LocalIFTSystems.local_determinacy` follows from
the stochastic theorem `local_determinacyS` applied to the `perfectForesight` expectation
system. -/
theorem pf_local_determinacy_recovered {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (h0 : G 0 = 0) (hL : IsUnit (LocalIFTSystems.linOp G)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : LocalIFTSystems.Par ι E → SeqV ι, X 0 = 0 ∧
      HasFDerivAt X (LocalIFTSystems.linSol G) 0 ∧
      ∀ u : LocalIFTSystems.Par ι E, ‖u‖ < δ → ‖X u‖ < ε / 2 ∧ LocalIFTSystems.Solves G u (X u) ∧
        ContDiffAt ℝ 1 X u ∧
        ∀ x : SeqV ι, ‖x‖ < ε → LocalIFTSystems.Solves G u x → x = X u := by
  have hLS : IsUnit (linOpS perfectForesight G) :=
    (isUnit_linOpS_iff_linOp perfectForesight G).mpr hL
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, XS, hX0, hXd, hX⟩ :=
    local_determinacyS perfectForesight hG h0 hLS hη
  set P := embPar (ι := ι) (E := E) (Ω := Unit) with hP
  refine ⟨ε, hε, hεη, δ, hδ, hδη, fun u => unembS (XS (P u)), ?_, ?_, fun u hu => ?_⟩
  · simp only [map_zero, hX0]
  · have hd : HasFDerivAt XS (linSolS perfectForesight G) (P 0) := by rw [map_zero]; exact hXd
    have h := unembS.hasFDerivAt.comp (0 : LocalIFTSystems.Par ι E) (hd.comp 0 P.hasFDerivAt)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    change unembS (linSolS perfectForesight G (P v)) = _
    rw [linSolS_embPar perfectForesight hLS, unembS_embG]
  · have hPu : ‖P u‖ < δ := lt_of_le_of_lt (norm_embPar_le u) hu
    obtain ⟨hn, hs, hc, hun⟩ := hX (P u) hPu
    have hXe : XS (P u) = embG (ι → ℝ) (unembS (XS (P u))) := (embG_unembS _).symm
    refine ⟨lt_of_le_of_lt (norm_unembS_le _) hn, ?_, ?_, fun x hx hsol => ?_⟩
    · rw [hXe] at hs
      exact (solvesSV_embG_iff perfectForesight G u _).mp hs
    · exact unembS.contDiff.contDiffAt.comp u (hc.comp u P.contDiff.contDiffAt)
    · have hxs := (solvesSV_embG_iff perfectForesight G u x).mpr hsol
      have he := hun (embG (ι → ℝ) x) (by rw [norm_embG]; exact hx) hxs
      rw [← unembS_embG x, he]

/-! ### An arbitrary steady state `x̄` -/

/-- Woodford (2003), App. A.3, p. 634: the steady-state parameters `(x̄, 0)`. -/
noncomputable def ssParS (xbar : ι → ℝ) : ParS ι E Ω := (xbar, 0)

/-- Woodford (2003), App. A.3, p. 634: the steady-state path `x_t(ω) = x̄`. -/
noncomputable def constS (xbar : ι → ℝ) : SProcV ι Ω :=
  LocalIFTStochastic.mkB (fun _ => xbar) ⟨‖xbar‖, fun _ => le_rfl⟩

omit [DecidableEq ι] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: `x` is a stochastic equilibrium of the level conditions
with parameters `u` iff `x − x̄` is one of the deviation conditions `shiftF G x̄` with parameters
`u − (x̄, 0)`. -/
theorem solvesSV_shift_iff (G : Arg ι E → (ι → ℝ)) (xbar : ι → ℝ) (u : ParS ι E Ω)
    (x : SProcV ι Ω) :
    SolvesSV 𝔼 G u x ↔
      SolvesSV 𝔼 (LocalIFTSystemsBar.shiftF G xbar) (u - ssParS xbar) (x - constS xbar) := by
  have hp : ∀ p, LocalIFTSystemsBar.shiftF G xbar (ptS (u - ssParS xbar, x - constS xbar) p) =
      G (ptS (u, x) p) := by
    intro p
    obtain ⟨t, ω⟩ := p
    rw [LocalIFTSystemsBar.shiftF]
    congr 1
    cases t <;> simp [ptS, ssParS, constS, LocalIFTSystemsBar.ssArg]
  have hc : toP (constS (Ω := Ω) xbar) = fun _ i _ => xbar i := rfl
  have ha : AdaptedV 𝔼 (toP x) ↔ AdaptedV 𝔼 (toP (x - constS xbar)) := by
    rw [toP_sub, hc]
    constructor
    · intro h t i
      change 𝔼.E t (toP x t i - fun _ => xbar i) = toP x t i - fun _ => xbar i
      rw [map_sub, h t i, 𝔼.const]
    · intro h t i
      have e := h t i
      change 𝔼.E t (toP x t i - fun _ => xbar i) = toP x t i - fun _ => xbar i at e
      rw [map_sub, 𝔼.const] at e
      exact sub_left_injective e
  unfold SolvesSV
  simp only [hp]
  rw [ha]

/-- **Stochastic local determinacy at an arbitrary steady state** (Woodford (2003), App. A.3,
pp. 633–635): if `G` is `C¹` near `(x̄, x̄, x̄, 0)`, `G(x̄, x̄, x̄, 0) = 0` and the operator (A.12)
built from `f_j = D_jG(x̄, x̄, x̄, 0)` is invertible (for nonempty `Ω`: the exact root condition,
`isUnit_linOpS_iff_roots` applied to `shiftF G x̄`), then for every `(x_{−1}, e)` within `δ` of
`(x̄, 0)` there is a bounded adapted equilibrium `X(x_{−1}, e)` within `ε/2` of the steady-state
path, it is the only one within `ε` of that path, `X` is `C¹`, `X(x̄, 0) = x̄`, and its derivative
at `(x̄, 0)` is the linear RE solution. -/
theorem local_determinacyS_at {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ}
    (hG : ContDiffAt ℝ 1 G (LocalIFTSystemsBar.ssArg E xbar))
    (h0 : G (LocalIFTSystemsBar.ssArg E xbar) = 0)
    (hL : IsUnit (linOpS 𝔼 (LocalIFTSystemsBar.shiftF G xbar))) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : ParS ι E Ω → SProcV ι Ω, X (ssParS xbar) = constS xbar ∧
      HasFDerivAt X (linSolS 𝔼 (LocalIFTSystemsBar.shiftF G xbar)) (ssParS xbar) ∧
      ∀ u : ParS ι E Ω, ‖u - ssParS xbar‖ < δ → ‖X u - constS xbar‖ < ε / 2 ∧
        SolvesSV 𝔼 G u (X u) ∧ ContDiffAt ℝ 1 X u ∧
        ∀ x : SProcV ι Ω, ‖x - constS xbar‖ < ε → SolvesSV 𝔼 G u x → x = X u := by
  obtain ⟨ε, hε, -, δ, hδ, -, X0, hX00, hX0d, hX0⟩ := local_determinacyS 𝔼
    (LocalIFTSystemsBar.contDiffAt_shiftF hG) (LocalIFTSystemsBar.shiftF_zero h0) hL one_pos
  refine ⟨ε, hε, δ, hδ, fun u => constS xbar + X0 (u - ssParS xbar), ?_, ?_, fun u hu => ?_⟩
  · simp only [sub_self, hX00, add_zero]
  · have hd : HasFDerivAt X0 (linSolS 𝔼 (LocalIFTSystemsBar.shiftF G xbar))
        (ssParS (E := E) (Ω := Ω) xbar - ssParS xbar) := by rw [sub_self]; exact hX0d
    have hsub : HasFDerivAt (fun u : ParS ι E Ω => u - ssParS xbar)
        (ContinuousLinearMap.id ℝ (ParS ι E Ω)) (ssParS xbar) := (hasFDerivAt_id _).sub_const _
    have h2 := (HasFDerivAt.comp (f := fun u : ParS ι E Ω => u - ssParS xbar) (ssParS xbar) hd
      hsub).const_add (constS xbar)
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  obtain ⟨hn, hs, hc, hun⟩ := hX0 (u - ssParS xbar) hu
  refine ⟨by rw [add_sub_cancel_left]; exact hn, ?_, ?_, fun x hx hsol => ?_⟩
  · rw [solvesSV_shift_iff 𝔼 G xbar, add_sub_cancel_left]
    exact hs
  · exact contDiffAt_const.add (hc.comp u (contDiffAt_id.sub contDiffAt_const))
  · have h := hun (x - constS xbar) hx ((solvesSV_shift_iff 𝔼 G xbar u x).mp hsol)
    change x = constS xbar + X0 (u - ssParS xbar)
    rw [← h, add_sub_cancel]

/-- Woodford (2003), App. A.3, pp. 633–634 (**the converse at an arbitrary steady state**): on a
nonempty state space, with the disturbances moving every equation, (A.12) at `(x̄, x̄, x̄, 0)` is
invertible iff the level conditions are locally determinate around `x̄` with a solution map
differentiable at `(x̄, 0)`. -/
theorem isUnit_iff_local_determinacyS_at [Nonempty Ω] {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ}
    (hG : ContDiffAt ℝ 1 G (LocalIFTSystemsBar.ssArg E xbar))
    (h0 : G (LocalIFTSystemsBar.ssArg E xbar) = 0)
    (hE : Function.Surjective (dE (LocalIFTSystemsBar.shiftF G xbar))) :
    IsUnit (linOpS 𝔼 (LocalIFTSystemsBar.shiftF G xbar)) ↔ ∃ ε > 0, ∃ δ > 0,
      ∃ X : ParS ι E Ω → SProcV ι Ω, X (ssParS xbar) = constS xbar ∧
        DifferentiableAt ℝ X (ssParS xbar) ∧ ∀ u : ParS ι E Ω, ‖u - ssParS xbar‖ < δ →
          SolvesSV 𝔼 G u (X u) ∧
          ∀ x : SProcV ι Ω, ‖x - constS xbar‖ < ε → SolvesSV 𝔼 G u x → x = X u := by
  rw [isUnit_linOpS_iff_local_determinacyS 𝔼 (LocalIFTSystemsBar.contDiffAt_shiftF hG)
    (LocalIFTSystemsBar.shiftF_zero h0) hE]
  constructor
  · rintro ⟨ε, hε, δ, hδ, X0, hX00, hX0d, hX0⟩
    refine ⟨ε, hε, δ, hδ, fun u => constS xbar + X0 (u - ssParS xbar), ?_, ?_, fun u hu => ?_⟩
    · simp only [sub_self, hX00, add_zero]
    · have hd : DifferentiableAt ℝ X0 (ssParS (E := E) (Ω := Ω) xbar - ssParS xbar) := by
        rw [sub_self]; exact hX0d
      have hsub : DifferentiableAt ℝ (fun u : ParS ι E Ω => u - ssParS xbar) (ssParS xbar) :=
        differentiableAt_id.sub_const _
      exact (differentiableAt_const _).add
        (DifferentiableAt.comp (f := fun u : ParS ι E Ω => u - ssParS xbar) (ssParS xbar) hd hsub)
    · obtain ⟨hs, hun⟩ := hX0 (u - ssParS xbar) hu
      refine ⟨by rw [solvesSV_shift_iff 𝔼 G xbar, add_sub_cancel_left]; exact hs,
        fun x hx hsol => ?_⟩
      have h := hun (x - constS xbar) hx ((solvesSV_shift_iff 𝔼 G xbar u x).mp hsol)
      change x = constS xbar + X0 (u - ssParS xbar)
      rw [← h, add_sub_cancel]
  · rintro ⟨ε, hε, δ, hδ, X, hX0, hXd, hX⟩
    refine ⟨ε, hε, δ, hδ, fun v => X (v + ssParS xbar) - constS xbar, ?_, ?_, fun v hv => ?_⟩
    · simp only [zero_add, hX0, sub_self]
    · have hd : DifferentiableAt ℝ X (0 + ssParS (E := E) (Ω := Ω) xbar) := by
        rw [zero_add]; exact hXd
      have hadd : DifferentiableAt ℝ (fun v : ParS ι E Ω => v + ssParS xbar) 0 :=
        differentiableAt_id.add_const _
      exact (hd.comp (0 : ParS ι E Ω) hadd).sub_const _
    · have hv' : ‖v + ssParS xbar - ssParS xbar‖ < δ := by rwa [add_sub_cancel_right]
      obtain ⟨hs, hun⟩ := hX (v + ssParS xbar) hv'
      refine ⟨?_, fun x hx hsol => ?_⟩
      · have := (solvesSV_shift_iff 𝔼 G xbar _ _).mp hs
        rwa [add_sub_cancel_right] at this
      · have hsol' : SolvesSV 𝔼 G (v + ssParS xbar) (x + constS xbar) := by
          rw [solvesSV_shift_iff 𝔼 G xbar, add_sub_cancel_right, add_sub_cancel_right]
          exact hsol
        have h := hun (x + constS xbar) (by rwa [add_sub_cancel_right]) hsol'
        change x = X (v + ssParS xbar) - constS xbar
        rw [← h, add_sub_cancel_right]

/-- Woodford (2003), App. A.3, p. 634, E18 **at an arbitrary steady state**: if `G` is `C²` near
`(x̄, x̄, x̄, 0)` and (A.12) there is invertible, every bounded adapted equilibrium within `ε` of
the steady-state path satisfies `‖x − (x̄ + x̂(u − (x̄, 0)))‖ ≤ C ‖u − (x̄, 0)‖²` for
`‖u − (x̄, 0)‖ < δ`, `x̂` the linear RE solution. -/
theorem second_order_locS_at {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ}
    (hG : ContDiffAt ℝ 2 G (LocalIFTSystemsBar.ssArg E xbar))
    (h0 : G (LocalIFTSystemsBar.ssArg E xbar) = 0)
    (hL : IsUnit (linOpS 𝔼 (LocalIFTSystemsBar.shiftF G xbar))) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ u : ParS ι E Ω, ‖u - ssParS xbar‖ < δ →
      ∀ x : SProcV ι Ω, ‖x - constS xbar‖ < ε → SolvesSV 𝔼 G u x →
        ‖x - (constS xbar + linSolS 𝔼 (LocalIFTSystemsBar.shiftF G xbar) (u - ssParS xbar))‖ ≤
          C * ‖u - ssParS xbar‖ ^ 2 := by
  obtain ⟨ε, hε, -, δ, hδ, -, C, hC⟩ := second_order_locS 𝔼
    (LocalIFTSystemsBar.contDiffAt_shiftF hG) (LocalIFTSystemsBar.shiftF_zero h0) hL one_pos
  refine ⟨ε, hε, δ, hδ, C, fun u hu x hx hsol => ?_⟩
  have h := hC (u - ssParS xbar) hu (x - constS xbar) hx
    ((solvesSV_shift_iff 𝔼 G xbar u x).mp hsol)
  rwa [sub_sub] at h

end Woodford.PriceLevelDetermination.LocalIFTSystemsStochastic
