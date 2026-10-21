/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LinearSystems
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Local determinacy of `n`-dimensional perfect-foresight systems on `ℓ∞`

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 631–633: for `n` equations per period
`F(x_{t−1}, x_t, x_{t+1}, e_t) = 0` (A.7), `x_t ∈ ℝⁿ` (deviations from the steady state `x̄`, so
`F(0) = 0`), given initial condition `x_{−1}` and a bounded disturbance sequence `{e_t}` in a
finite-dimensional space, the book claims (citing Lang, without proof) that when the linearised
system (A.10) has a unique bounded solution, the exact system has, for `x_{−1}` near `x̄` and
small disturbances, a locally unique equilibrium approximated by the linear solution with error
`O(‖u‖²)`. This module proves the general `n`-dimensional statement with predetermined variables
(the scalar forward case is `LocalIFT`), its converse, and the correct form of the error bound
(E18). The invertibility condition is the exact root condition of `LinearSystems`.

## Main results

* Nemytskii operators on `ℓ∞` (`nem`, `hasStrictFDerivAt_nem`, `contDiff_nem`): the equilibrium
  map `eqMap` on `(ℝⁿ × ℓ∞(E)) × ℓ∞(ℕ, ℝⁿ)` is strictly differentiable everywhere and `C¹`;
  `nemD_zero`: its derivative at the steady state is (A.8), `linOp` (the operator
  `LinearSystems.sysOp` with `f_j = D_jF(0)`, `M1`–`M3`) plus the parameter part `bOp`.
* `local_determinacy` (**the theorem**): `F` `C¹` near `0`, `F(0) = 0`, (A.8) invertible ⟹ for
  `‖(x_{−1}, e)‖ < δ` there is a unique equilibrium within `ε` of the steady state, it depends
  `C¹` on `(x_{−1}, e)`, and its derivative at `0` is the solution operator `linSol` of (A.10)
  (`linSol_solves`, `eq_linSol`). `isUnit_linOp_iff`, `local_determinacy_of_roots`: the
  hypothesis is exactly the root condition (no root of `det(f₃λ² + f₂λ + f₁)` on the circle,
  `n` inside, not identically zero, genericity).
* E18: `first_order_loc` — for `C¹` the error is `o(‖(x_{−1}, e)‖)`; `second_order_loc`,
  `second_order_global` — for `C²` (or Lipschitz `DF`) it is `O(‖(x_{−1}, e)‖²)`.
* Necessity: `surjective_of_solution_map` — if the disturbances move every equation (`D₄F(0)`
  onto) and a solution map is differentiable at `0`, (A.8) is onto; `not_locally_unique` — if
  (A.8) is onto but not one-to-one, local uniqueness fails (nonzero equilibria arbitrarily close
  to the steady state, with no disturbances); `isUnit_of_local_determinacy`,
  `isUnit_linOp_iff_local_determinacy` — local determinacy with a solution map differentiable at
  the steady state holds **iff** the root condition holds.
* `cube_unique_without_root_condition`: the converse cannot be sharpened to "existence or
  uniqueness fails": for `x_t³ = e_t` the root condition fails, yet every disturbance sequence
  has exactly one bounded equilibrium; only the first-order approximation fails.
-/

namespace Woodford.PriceLevelDetermination.LocalIFTSystems

open scoped Topology Matrix
open LinearSystems

/-! ### Nemytskii operators on `ℓ∞` -/

/-- Woodford (2003), App. A.3, p. 632: the derivative of a `C¹` map on a finite-dimensional
space is uniformly continuous on bounded sets (Heine–Cantor); vector-valued version of
`LocalIFT.fderiv_close3`. -/
theorem fderiv_close {G W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [ProperSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : G → W} (hF : ContDiff ℝ 1 F) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : G, ‖p‖ ≤ R → ‖q - p‖ < δ → ‖fderiv ℝ F q - fderiv ℝ F p‖ < ε := by
  have hK := isCompact_closedBall (0 : G) (R + 1)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (hF.continuous_fderiv one_ne_zero).continuousOn) ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun p q hp hq => ?_⟩
  have hq1 : ‖q - p‖ < 1 := lt_of_lt_of_le hq (min_le_right _ _)
  have hpK : p ∈ Metric.closedBall (0 : G) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    linarith
  have hqK : q ∈ Metric.closedBall (0 : G) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have : ‖q‖ ≤ ‖p‖ + ‖q - p‖ := by
      calc ‖q‖ = ‖p + (q - p)‖ := by rw [add_sub_cancel]
        _ ≤ ‖p‖ + ‖q - p‖ := norm_add_le _ _
    linarith
  have := h q hqK p hpK (by rw [dist_eq_norm]; exact lt_of_lt_of_le hq (min_le_left _ _))
  rwa [dist_eq_norm] at this


variable {Q G W : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the equilibrium map `q ↦ (F(π_t q))_t` built
from date-`t` coordinate maps `π_t` of norm at most one (a Nemytskii operator). -/
noncomputable def nem (F : G → W) (hF : Continuous F) (pt : ℕ → Q →L[ℝ] G)
    (hpt : ∀ t q, ‖pt t q‖ ≤ ‖q‖) (q : Q) : LocalIFT.Seq W :=
  LocalIFT.mkS (fun t => F (pt t q)) (by
    obtain ⟨C, hC⟩ := LocalIFT.exists_bound_ball3 hF ‖q‖
    exact ⟨C, fun t => hC _ (hpt t q)⟩)

omit [NormedSpace ℝ W] in
/-- Woodford (2003), App. A.3, p. 631: coordinates of the equilibrium map. -/
@[simp] theorem nem_apply (F : G → W) (hF : Continuous F) (pt : ℕ → Q →L[ℝ] G)
    (hpt : ∀ t q, ‖pt t q‖ ≤ ‖q‖) (q : Q) (t : ℕ) : nem F hF pt hpt q t = F (pt t q) := rfl

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the candidate derivative of the equilibrium
map at `q`, `dq ↦ (DF(π_t q)(π_t dq))_t`. -/
noncomputable def nemD (F : G → W) (hF : ContDiff ℝ 1 F) (pt : ℕ → Q →L[ℝ] G)
    (hpt : ∀ t q, ‖pt t q‖ ≤ ‖q‖) (q : Q) : Q →L[ℝ] LocalIFT.Seq W :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun dq => LocalIFT.mkS (fun t => fderiv ℝ F (pt t q) (pt t dq)) (by
        obtain ⟨C, hC⟩ := LocalIFT.exists_bound_ball3 (hF.continuous_fderiv one_ne_zero) ‖q‖
        exact ⟨C * ‖dq‖, fun t => ((fderiv ℝ F (pt t q)).le_opNorm _).trans
          (mul_le_mul (hC _ (hpt t q)) (hpt t dq) (norm_nonneg _)
            ((norm_nonneg _).trans (hC _ (hpt t q))))⟩)
      map_add' := fun dq dq' => seq_ext fun t => by simp
      map_smul' := fun c dq => seq_ext fun t => by simp }
    (by
      obtain ⟨C, hC⟩ := LocalIFT.exists_bound_ball3 (hF.continuous_fderiv one_ne_zero) ‖q‖
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp))
      refine ⟨C, fun dq => LocalIFT.norm_seq_le (by positivity) fun t => ?_⟩
      exact ((fderiv ℝ F (pt t q)).le_opNorm _).trans
        (mul_le_mul (hC _ (hpt t q)) (hpt t dq) (norm_nonneg _) hC0))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of `nemD`. -/
@[simp] theorem nemD_apply (F : G → W) (hF : ContDiff ℝ 1 F) (pt : ℕ → Q →L[ℝ] G)
    (hpt : ∀ t q, ‖pt t q‖ ≤ ‖q‖) (q dq : Q) (t : ℕ) :
    nemD F hF pt hpt q dq t = fderiv ℝ F (pt t q) (pt t dq) := rfl

/-- Woodford (2003), App. A.3, p. 632: **the equilibrium map of a `C¹` period condition is
strictly Fréchet differentiable at every point**, with derivative `nemD` (vector-valued
version of `LocalIFT.hasStrictFDerivAt_eqMap`). -/
theorem hasStrictFDerivAt_nem {F : G → W} (hF : ContDiff ℝ 1 F) (pt : ℕ → Q →L[ℝ] G)
    (hpt : ∀ t q, ‖pt t q‖ ≤ ‖q‖) (q : Q) :
    HasStrictFDerivAt (nem F hF.continuous pt hpt) (nemD F hF pt hpt q) q := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close hF ‖q‖ hc
  have hball : Metric.ball (q, q) (δ / 2) ∈ 𝓝 (q, q) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with p hp
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hp
  refine LocalIFT.norm_seq_le (by positivity) (fun t => ?_)
  have hmem : ∀ y : Q, ‖y - q‖ < δ / 2 → pt t y ∈ Metric.ball (pt t q) (δ / 2) := fun y hy => by
    rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
    exact (hpt t _).trans_lt hy
  have key := (convex_ball (pt t q) (δ / 2)).norm_image_sub_le_of_norm_fderiv_le' (f := F)
    (φ := fderiv ℝ F (pt t q)) (C := c) (fun w _ => (hF.differentiable one_ne_zero) w)
    (fun w hw => by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact (hclose (pt t q) w (hpt t q) (by linarith)).le)
    (hmem p.2 hp.2) (hmem p.1 hp.1)
  simp only [lp.coeFn_sub, Pi.sub_apply, nem_apply, nemD_apply]
  rw [map_sub (pt t)]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
  rw [← map_sub]
  exact hpt t _

/-- Woodford (2003), App. A.3, p. 632: the derivative `q ↦ nemD q` is continuous in operator
norm. -/
theorem continuous_nemD {F : G → W} (hF : ContDiff ℝ 1 F) (pt : ℕ → Q →L[ℝ] G)
    (hpt : ∀ t q, ‖pt t q‖ ≤ ‖q‖) : Continuous (nemD F hF pt hpt) := by
  rw [Metric.continuous_iff]
  intro q ε hε
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close hF ‖q‖ (half_pos hε)
  refine ⟨δ, hδ, fun q' hq' => ?_⟩
  rw [dist_eq_norm] at hq' ⊢
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    (fun dq => ?_)) (half_lt_self hε)
  refine LocalIFT.norm_seq_le (by positivity) (fun t => ?_)
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, nemD_apply]
  rw [← sub_apply]
  refine ((fderiv ℝ F (pt t q') - fderiv ℝ F (pt t q)).le_opNorm _).trans
    (mul_le_mul (hclose _ _ (hpt t q) ?_).le (hpt t dq) (norm_nonneg _) (half_pos hε).le)
  rw [← map_sub]
  exact (hpt t _).trans_lt hq'

/-- Woodford (2003), App. A.3, p. 632: the equilibrium map is `C¹`. -/
theorem contDiff_nem {F : G → W} (hF : ContDiff ℝ 1 F) (pt : ℕ → Q →L[ℝ] G)
    (hpt : ∀ t q, ‖pt t q‖ ≤ ‖q‖) : ContDiff ℝ 1 (nem F hF.continuous pt hpt) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨nemD F hF pt hpt, continuous_nemD hF pt hpt,
      fun q => (hasStrictFDerivAt_nem hF pt hpt q).hasFDerivAt⟩


/-! ### The class `F(x_{t−1}, x_t, x_{t+1}, e_t) = 0` with `x_t ∈ ℝⁿ` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Woodford (2003), App. A.3, p. 631: the "parameters" `u` of the sequence-space problem — the
initial condition `x_{−1}` together with the whole disturbance sequence `{e_t}` (in `ℓ∞(E)`). -/
abbrev Par (ι : Type*) [Fintype ι] (E : Type*) [NormedAddCommGroup E] : Type _ :=
  (ι → ℝ) × LocalIFT.Seq E

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the argument `(x_{t−1}, x_t, x_{t+1}, e_t)` of
the period conditions. -/
abbrev Arg (ι : Type*) (E : Type*) : Type _ := (ι → ℝ) × (ι → ℝ) × (ι → ℝ) × E

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the date-`t` argument
`(x_{t−1}, x_t, x_{t+1}, e_t)` of a point `((x_{−1}, e), x)` of the sequence space. -/
def pt4 (q : Par ι E × SeqV ι) (t : ℕ) : Arg ι E :=
  (lagV q.1.1 (fun s => q.2 s) t, q.2 t, q.2 (t + 1), q.1.2 t)

omit [DecidableEq ι] [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: each date-`t` argument is bounded by the norm of the
point. -/
theorem norm_pt4_le (q : Par ι E × SeqV ι) (t : ℕ) : ‖pt4 q t‖ ≤ ‖q‖ := by
  have h1 : ‖lagV q.1.1 (fun s => q.2 s) t‖ ≤ ‖q‖ := by
    cases t with
    | zero => exact (norm_fst_le q.1).trans (norm_fst_le q)
    | succ t => exact (LocalIFT.norm_seq_apply_le q.2 t).trans (norm_snd_le q)
  have h2 : ‖q.2 t‖ ≤ ‖q‖ := (LocalIFT.norm_seq_apply_le q.2 t).trans (norm_snd_le q)
  have h3 : ‖q.2 (t + 1)‖ ≤ ‖q‖ := (LocalIFT.norm_seq_apply_le q.2 _).trans (norm_snd_le q)
  have h4 : ‖q.1.2 t‖ ≤ ‖q‖ :=
    (LocalIFT.norm_seq_apply_le q.1.2 t).trans ((norm_snd_le q.1).trans (norm_fst_le q))
  rw [pt4, norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
  exact ⟨h1, h2, h3, h4⟩

/-- Woodford (2003), App. A.3, p. 632: the date-`t` argument as a continuous linear map of norm
at most one. -/
noncomputable def ptL (t : ℕ) : Par ι E × SeqV ι →L[ℝ] Arg ι E :=
  LinearMap.mkContinuous
    { toFun := fun q => pt4 q t
      map_add' := fun q q' => by cases t <;> rfl
      map_smul' := fun c q => by cases t <;> rfl }
    1 (fun q => by rw [one_mul]; exact norm_pt4_le q t)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632: coordinates of `ptL`. -/
@[simp] theorem ptL_apply (t : ℕ) (q : Par ι E × SeqV ι) : ptL t q = pt4 q t := rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632: `ptL` has norm at most one. -/
theorem norm_ptL_le (t : ℕ) (q : Par ι E × SeqV ι) : ‖ptL t q‖ ≤ ‖q‖ := norm_pt4_le q t

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: `x` solves the exact perfect-foresight
conditions `F(x_{t−1}, x_t, x_{t+1}, e_t) = 0` for all `t ≥ 0`, given `u = (x_{−1}, e)`. -/
def Solves (F : Arg ι E → (ι → ℝ)) (u : Par ι E) (x : SeqV ι) : Prop :=
  ∀ t, F (lagV u.1 (fun s => x s) t, x t, x (t + 1), u.2 t) = 0

variable [FiniteDimensional ℝ E]

/-- Woodford (2003), App. A.3, eqs. (A.4)/(A.7), p. 631: the equilibrium map
`Φ(u, x)_t = F(x_{t−1}, x_t, x_{t+1}, e_t)` on `(ℝⁿ × ℓ∞(E)) × ℓ∞(ℕ, ℝⁿ)`. -/
noncomputable def eqMap (F : Arg ι E → (ι → ℝ)) (hF : Continuous F) :
    Par ι E × SeqV ι → SeqV ι :=
  nem F hF ptL norm_ptL_le

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, eq. (A.4), p. 630: zeros of the equilibrium map are exactly the
perfect-foresight equilibria. -/
theorem eqMap_eq_zero_iff (F : Arg ι E → (ι → ℝ)) (hF : Continuous F) (u : Par ι E)
    (x : SeqV ι) : eqMap F hF (u, x) = 0 ↔ Solves F u x := by
  constructor
  · intro h t
    exact congrArg (fun y : SeqV ι => y t) h
  · intro h
    exact seq_ext fun t => h t

/-! ### The derivative at the steady state: (A.8) -/

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `f₁ = D₁F`, the derivative with respect to
`x_{t−1}` at the steady state. -/
noncomputable def d1 (F : Arg ι E → (ι → ℝ)) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ F 0).comp (ContinuousLinearMap.inl ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `f₂ = D₂F`, with respect to `x_t`. -/
noncomputable def d2 (F : Arg ι E → (ι → ℝ)) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ F 0).comp ((ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E)).comp
    (ContinuousLinearMap.inl ℝ (ι → ℝ) ((ι → ℝ) × E)))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `f₃ = D₃F`, with respect to `x_{t+1}`. -/
noncomputable def d3 (F : Arg ι E → (ι → ℝ)) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ F 0).comp ((ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E)).comp
    ((ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × E)).comp
      (ContinuousLinearMap.inl ℝ (ι → ℝ) E)))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `D₄F`, the derivative with respect to the
disturbance `e_t`. -/
noncomputable def dE (F : Arg ι E → (ι → ℝ)) : E →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ F 0).comp ((ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E)).comp
    ((ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × E)).comp
      (ContinuousLinearMap.inr ℝ (ι → ℝ) E)))

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the derivative at the steady state in blocks,
`DF(0)(a, b, c, v) = f₁ a + f₂ b + f₃ c + D₄F v`. -/
theorem fderiv_zero_apply4 (F : Arg ι E → (ι → ℝ)) (a b c : ι → ℝ) (v : E) :
    fderiv ℝ F 0 (a, b, c, v) = d1 F a + d2 F b + d3 F c + dE F v := by
  have h : ((a, b, c, v) : Arg ι E) =
      ContinuousLinearMap.inl ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E) a +
        (ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E)
          (ContinuousLinearMap.inl ℝ (ι → ℝ) ((ι → ℝ) × E) b) +
        (ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E)
          (ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × E)
            (ContinuousLinearMap.inl ℝ (ι → ℝ) E c)) +
        ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × (ι → ℝ) × E)
          (ContinuousLinearMap.inr ℝ (ι → ℝ) ((ι → ℝ) × E)
            (ContinuousLinearMap.inr ℝ (ι → ℝ) E v)))) := by
    simp
  rw [h, map_add, map_add, map_add]
  simp only [d1, d2, d3, dE, ContinuousLinearMap.comp_apply]
  abel

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the coefficient matrix `f₁`. -/
noncomputable def M1 (F : Arg ι E → (ι → ℝ)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (d1 F : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the coefficient matrix `f₂`. -/
noncomputable def M2 (F : Arg ι E → (ι → ℝ)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (d2 F : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the coefficient matrix `f₃`. -/
noncomputable def M3 (F : Arg ι E → (ι → ℝ)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (d3 F : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the matrices act as the partial
derivatives. -/
theorem mulVec_M (F : Arg ι E → (ι → ℝ)) (v : ι → ℝ) :
    M1 F *ᵥ v = d1 F v ∧ M2 F *ᵥ v = d2 F v ∧ M3 F *ᵥ v = d3 F v :=
  ⟨LinearMap.toMatrix'_mulVec _ _, LinearMap.toMatrix'_mulVec _ _,
    LinearMap.toMatrix'_mulVec _ _⟩

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: **the linearised operator**
`x̂ ↦ (f₁ x̂_{t−1} + f₂ x̂_t + f₃ x̂_{t+1})_t` on `ℓ∞(ℕ, ℝⁿ)`, `x̂_{−1} = 0` (fn. 4). -/
noncomputable def linOp (F : Arg ι E → (ι → ℝ)) : SeqV ι →L[ℝ] SeqV ι :=
  sysOp (M1 F) (M2 F) (M3 F)

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of the linearised operator. -/
theorem linOp_apply (F : Arg ι E → (ι → ℝ)) (x : SeqV ι) (t : ℕ) :
    linOp F x t = d1 F (lagV 0 (fun s => x s) t) + d2 F (x t) + d3 F (x (t + 1)) := by
  rw [linOp, sysOp_apply, (mulVec_M F _).1, (mulVec_M F _).2.1, (mulVec_M F _).2.2]

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 633 (tool): the impulse sequence `(v, 0, 0, …)` has norm at
most `‖v‖`. -/
theorem norm_lagV_impulse (v : ι → ℝ) (t : ℕ) : ‖lagV v (0 : ℕ → ι → ℝ) t‖ ≤ ‖v‖ := by
  cases t with
  | zero => exact le_rfl
  | succ t => simp

/-- Woodford (2003), App. A.3, p. 633 and fn. 3: the initial condition enters the conditions as
the impulse `v ↦ (v, 0, 0, …)` (the `t = 0` lag), a bounded operator `ℝⁿ → ℓ∞(ℕ, ℝⁿ)`. -/
noncomputable def impOp (ι : Type*) [Fintype ι] : (ι → ℝ) →L[ℝ] SeqV ι :=
  LinearMap.mkContinuous
    { toFun := fun v => LocalIFT.mkS (lagV v 0) ⟨‖v‖, norm_lagV_impulse v⟩
      map_add' := fun v w => seq_ext fun t => by cases t <;> simp
      map_smul' := fun c v => seq_ext fun t => by cases t <;> simp }
    1 (fun v => by
      rw [one_mul]
      exact LocalIFT.norm_seq_le (norm_nonneg _) (norm_lagV_impulse v))

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 633: coordinates of the impulse operator. -/
@[simp] theorem impOp_apply (v : ι → ℝ) (t : ℕ) : impOp ι v t = lagV v 0 t := rfl

/-- Woodford (2003), App. A.3, eqs. (A.8)/(A.10), pp. 632–633: the derivative of the conditions
with respect to the parameters `u = (x_{−1}, e)`, `(f₁ x_{−1} 1_{t=0} + D₄F e_t)_t`. -/
noncomputable def bOp (F : Arg ι E → (ι → ℝ)) : Par ι E →L[ℝ] SeqV ι :=
  (pw (d1 F)).comp ((impOp ι).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (LocalIFT.Seq E))) +
    (pw (dE F)).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (LocalIFT.Seq E))

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 633: coordinates of `bOp`. -/
theorem bOp_apply (F : Arg ι E → (ι → ℝ)) (u : Par ι E) (t : ℕ) :
    bOp F u t = d1 F (lagV u.1 0 t) + dE F (u.2 t) := rfl

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the derivative of the equilibrium map at the
steady state, `(u, x̂) ↦ (f₁ L + f₂ + f₃ S) x̂ + B u`. -/
noncomputable def eqD0 (F : Arg ι E → (ι → ℝ)) : Par ι E × SeqV ι →L[ℝ] SeqV ι :=
  (linOp F).comp (ContinuousLinearMap.snd ℝ (Par ι E) (SeqV ι)) +
    (bOp F).comp (ContinuousLinearMap.fst ℝ (Par ι E) (SeqV ι))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: **at the steady state the derivative of the
equilibrium map is the operator (A.8)** (plus the parameter part). -/
theorem nemD_zero {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) :
    nemD F hF ptL norm_ptL_le 0 = eqD0 F := by
  refine ContinuousLinearMap.ext fun q => seq_ext fun t => ?_
  have e1 : nemD F hF ptL norm_ptL_le 0 q t = fderiv ℝ F 0 (pt4 q t) := by
    rw [nemD_apply, ptL_apply, ptL_apply]
    congr 2
    cases t <;> rfl
  have e2 : eqD0 F q t = linOp F q.2 t + bOp F q.1 t := rfl
  rw [e1, e2, pt4, fderiv_zero_apply4, linOp_apply, bOp_apply, lagV_split q.1.1, map_add]
  abel

/-! ### The implicit-function theorem on `ℓ∞(ℕ, ℝⁿ)` -/

/-- Woodford (2003), App. A.3, p. 633: the inverse of the linearised operator (the solution map
of (A.10) with `x̂_{−1} = 0`), when it exists. -/
noncomputable def linInv (F : Arg ι E → (ι → ℝ)) : SeqV ι →L[ℝ] SeqV ι := Ring.inverse (linOp F)

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 633: `linInv` is a right inverse. -/
theorem linOp_linInv {F : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOp F)) (y : SeqV ι) :
    linOp F (linInv F y) = y := by
  have h := Ring.mul_inverse_cancel _ hL
  unfold linInv
  simpa using congrArg (fun T : SeqV ι →L[ℝ] SeqV ι => T y) h

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 633: `linInv` is a left inverse. -/
theorem linInv_linOp {F : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOp F)) (x : SeqV ι) :
    linInv F (linOp F x) = x := by
  have h := Ring.inverse_mul_cancel _ hL
  unfold linInv
  simpa using congrArg (fun T : SeqV ι →L[ℝ] SeqV ι => T x) h

/-- Woodford (2003), App. A.3, p. 631: the augmented map `(u, x) ↦ (u, Φ(u, x))`. -/
noncomputable def bigMap (F : Arg ι E → (ι → ℝ)) (hF : Continuous F) (q : Par ι E × SeqV ι) :
    Par ι E × SeqV ι :=
  (q.1, eqMap F hF q)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632: the augmented map is `C¹`. -/
theorem contDiff_bigMap {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (bigMap F hF.continuous) :=
  contDiff_fst.prodMk (contDiff_nem hF ptL norm_ptL_le)

/-- Woodford (2003), App. A.3, p. 632: the derivative of the augmented map at the steady
state. -/
noncomputable def bigD (F : Arg ι E → (ι → ℝ)) : Par ι E × SeqV ι →L[ℝ] Par ι E × SeqV ι :=
  (ContinuousLinearMap.fst ℝ (Par ι E) (SeqV ι)).prod (eqD0 F)

/-- Woodford (2003), App. A.3, p. 632: the inverse of `bigD`,
`(u, y) ↦ (u, (f₁ L + f₂ + f₃ S)⁻¹(y − B u))`. -/
noncomputable def bigDInv (F : Arg ι E → (ι → ℝ)) : Par ι E × SeqV ι →L[ℝ] Par ι E × SeqV ι :=
  (ContinuousLinearMap.fst ℝ (Par ι E) (SeqV ι)).prod
    ((linInv F).comp (ContinuousLinearMap.snd ℝ (Par ι E) (SeqV ι) -
      (bOp F).comp (ContinuousLinearMap.fst ℝ (Par ι E) (SeqV ι))))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: `bigDInv` is a left inverse of `bigD`. -/
theorem bigDInv_bigD {F : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOp F)) (q : Par ι E × SeqV ι) :
    bigDInv F (bigD F q) = q := by
  refine Prod.ext rfl ?_
  change linInv F (linOp F q.2 + bOp F q.1 - bOp F q.1) = q.2
  rw [add_sub_cancel_right, linInv_linOp hL]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: `bigDInv` is a right inverse of `bigD`. -/
theorem bigD_bigDInv {F : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOp F)) (q : Par ι E × SeqV ι) :
    bigD F (bigDInv F q) = q := by
  refine Prod.ext rfl ?_
  change linOp F (linInv F (q.2 - bOp F q.1)) + bOp F q.1 = q.2
  rw [linOp_linInv hL, sub_add_cancel]

/-- Woodford (2003), App. A.3, p. 632: when (A.8) is invertible the derivative of the augmented
map is a continuous linear equivalence. -/
noncomputable def bigDEquiv (F : Arg ι E → (ι → ℝ)) (hL : IsUnit (linOp F)) :
    (Par ι E × SeqV ι) ≃L[ℝ] (Par ι E × SeqV ι) :=
  ContinuousLinearEquiv.equivOfInverse (bigD F) (bigDInv F) (bigDInv_bigD hL) (bigD_bigDInv hL)

/-- Woodford (2003), App. A.3, p. 632: the derivative of the augmented map at the steady
state. -/
theorem hasFDerivAt_bigMap {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F)
    (hL : IsUnit (linOp F)) :
    HasFDerivAt (bigMap F hF.continuous) (bigDEquiv F hL : _ →L[ℝ] _) 0 := by
  have h := (hasStrictFDerivAt_nem hF ptL norm_ptL_le 0).hasFDerivAt
  rw [nemD_zero hF] at h
  exact hasFDerivAt_fst.prodMk h

/-- Woodford (2003), App. A.3, pp. 632–633: the local homeomorphism given by the inverse-function
theorem (Lang 1983; Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`). -/
noncomputable def homeo (F : Arg ι E → (ι → ℝ)) (hF : ContDiff ℝ 1 F) (hL : IsUnit (linOp F)) :
    OpenPartialHomeomorph (Par ι E × SeqV ι) (Par ι E × SeqV ι) :=
  ((contDiff_bigMap hF).contDiffAt.hasStrictFDerivAt' (hasFDerivAt_bigMap hF hL)
    one_ne_zero).toOpenPartialHomeomorph (bigMap F hF.continuous)

/-- Woodford (2003), App. A.3, p. 633: the locally unique equilibrium `x = X(x_{−1}, e)`. -/
noncomputable def implicitSol (F : Arg ι E → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (hL : IsUnit (linOp F)) (u : Par ι E) : SeqV ι :=
  ((homeo F hF hL).symm (u, 0)).2

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the solution operator of the linearised
conditions, `u ↦ −(f₁ L + f₂ + f₃ S)⁻¹ B u`. -/
noncomputable def linSol (F : Arg ι E → (ι → ℝ)) : Par ι E →L[ℝ] SeqV ι :=
  -((linInv F).comp (bOp F))

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633 (tool): rearranging the five terms of a
linearised period condition. -/
theorem add5_eq_zero_iff {A : Type*} [AddCommGroup A] (a b c d e : A) :
    a + b + c + d + e = 0 ↔ a + c + d = -(b + e) := by
  rw [eq_neg_iff_add_eq_zero]
  constructor <;> intro h <;> rw [← h] <;> abel

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: `linSol u` solves the linearised conditions
`f₁ x̂_{t−1} + f₂ x̂_t + f₃ x̂_{t+1} + D₄F e_t = 0` with `x̂_{−1} = x_{−1}`. -/
theorem linSol_solves {F : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOp F)) (u : Par ι E) (t : ℕ) :
    d1 F (lagV u.1 (fun s => linSol F u s) t) + d2 F (linSol F u t) +
      d3 F (linSol F u (t + 1)) + dE F (u.2 t) = 0 := by
  have hT : linOp F (linSol F u) = -bOp F u := by
    change linOp F (-(linInv F (bOp F u))) = -bOp F u
    rw [map_neg, linOp_linInv hL]
  have h := congrArg (fun y : SeqV ι => y t) hT
  simp only [lp.coeFn_neg, Pi.neg_apply] at h
  rw [linOp_apply, bOp_apply] at h
  rw [lagV_split, map_add, add5_eq_zero_iff]
  exact h

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the linearised conditions have exactly one
bounded solution, `linSol u`. -/
theorem eq_linSol {F : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOp F)) {u : Par ι E} {x : SeqV ι}
    (h : ∀ t, d1 F (lagV u.1 (fun s => x s) t) + d2 F (x t) + d3 F (x (t + 1)) +
      dE F (u.2 t) = 0) : x = linSol F u := by
  have hT : linOp F x = -bOp F u := by
    refine seq_ext fun t => ?_
    have := h t
    rw [lagV_split, map_add, add5_eq_zero_iff] at this
    rw [linOp_apply, lp.coeFn_neg, Pi.neg_apply, bOp_apply]
    exact this
  rw [← linInv_linOp hL x, hT, map_neg]
  rfl

/-- Woodford (2003), App. A.3, p. 631: the local homeomorphism is the augmented map. -/
theorem homeo_apply {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (hL : IsUnit (linOp F))
    (q : Par ι E × SeqV ι) : homeo F hF hL q = bigMap F hF.continuous q := rfl

/-- Woodford (2003), App. A.3, p. 632: the steady state lies in the source. -/
theorem zero_mem_homeo_source {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F)
    (hL : IsUnit (linOp F)) : (0 : Par ι E × SeqV ι) ∈ (homeo F hF hL).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

omit [DecidableEq ι] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 631: with `x_{−1} = x̄` and no disturbances the steady state is
an equilibrium. -/
theorem solves_zero {F : Arg ι E → (ι → ℝ)} (h0 : F 0 = 0) : Solves F 0 0 := by
  intro t
  have hz : ((lagV (0 : Par ι E).1 (fun s => (0 : SeqV ι) s) t, (0 : SeqV ι) t,
      (0 : SeqV ι) (t + 1), (0 : Par ι E).2 t) : Arg ι E) = 0 := by
    cases t <;> rfl
  rw [hz]
  exact h0

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 631: the augmented map fixes the steady state. -/
theorem bigMap_zero {F : Arg ι E → (ι → ℝ)} (hF : Continuous F) (h0 : F 0 = 0) :
    bigMap F hF 0 = 0 :=
  Prod.ext rfl ((eqMap_eq_zero_iff F hF 0 0).mpr (solves_zero h0))

/-- Woodford (2003), App. A.3, p. 632: the steady state lies in the target. -/
theorem zero_mem_homeo_target {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) : (0 : Par ι E × SeqV ι) ∈ (homeo F hF hL).target := by
  have h := (homeo F hF hL).map_source (zero_mem_homeo_source hF hL)
  rwa [homeo_apply, bigMap_zero hF.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 632: the local inverse maps the steady state to itself. -/
theorem homeo_symm_zero {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) : (homeo F hF hL).symm 0 = 0 := by
  have h := (homeo F hF hL).left_inv (zero_mem_homeo_source hF hL)
  rwa [homeo_apply, bigMap_zero hF.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 633: the local inverse is `C¹` at the steady state. -/
theorem contDiffAt_homeo_symm {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) : ContDiffAt ℝ 1 (homeo F hF hL).symm 0 := by
  refine (homeo F hF hL).contDiffAt_symm (f₀' := bigDEquiv F hL)
    (zero_mem_homeo_target hF h0 hL) ?_ ?_
  · rw [homeo_symm_zero hF h0 hL]
    exact hasFDerivAt_bigMap hF hL
  · rw [homeo_symm_zero hF h0 hL]
    exact (contDiff_bigMap hF).contDiffAt

/-- Woodford (2003), App. A.3, (A.5), p. 630: the derivative of the local inverse at the steady
state is the inverse of the derivative. -/
theorem hasFDerivAt_homeo_symm {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) :
    HasFDerivAt (homeo F hF hL).symm ((bigDEquiv F hL).symm : _ →L[ℝ] _) 0 := by
  refine (homeo F hF hL).hasFDerivAt_symm (zero_mem_homeo_target hF h0 hL) ?_
  rw [homeo_symm_zero hF h0 hL]
  exact hasFDerivAt_bigMap hF hL

/-- Woodford (2003), App. A.3, p. 633: with `x_{−1} = x̄` and no disturbances the equilibrium is
the steady state. -/
theorem implicitSol_zero {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) : implicitSol F hF hL 0 = 0 := by
  rw [implicitSol, Prod.mk_zero_zero, homeo_symm_zero hF h0 hL]
  rfl

/-- Woodford (2003), App. A.3, p. 633 and (A.5), p. 630: **the first-order term of the exact
equilibrium is the solution of the linearised system (A.10)**. -/
theorem hasFDerivAt_implicitSol {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) : HasFDerivAt (implicitSol F hF hL) (linSol F) 0 := by
  have hin : HasFDerivAt (fun u : Par ι E => ((u, (0 : SeqV ι)) : Par ι E × SeqV ι))
      (ContinuousLinearMap.inl ℝ (Par ι E) (SeqV ι)) 0 :=
    (ContinuousLinearMap.inl ℝ (Par ι E) (SeqV ι)).hasFDerivAt
  have hs : HasFDerivAt (homeo F hF hL).symm ((bigDEquiv F hL).symm : _ →L[ℝ] _)
      ((0 : Par ι E), (0 : SeqV ι)) := by
    rw [Prod.mk_zero_zero]
    exact hasFDerivAt_homeo_symm hF h0 hL
  have h := (ContinuousLinearMap.snd ℝ (Par ι E) (SeqV ι)).hasFDerivAt.comp (0 : Par ι E)
    (hs.comp (0 : Par ι E) hin)
  refine h.congr_fderiv (ContinuousLinearMap.ext (fun u => ?_))
  change linInv F ((0 : SeqV ι) - bOp F u) = -(linInv F (bOp F u))
  rw [zero_sub, map_neg]

/-- Woodford (2003), App. A.3, pp. 632–633, **global-`C¹` form**: if `F` is `C¹`, `F(0) = 0` and
the operator (A.8) is invertible, there are `ε, δ > 0` such that for `‖(x_{−1}, e)‖ < δ`,
`X(x_{−1}, e)` is an equilibrium with `‖X‖ < ε/2`, `X` is `C¹` there, and every equilibrium with
`‖x‖ < ε` equals `X(x_{−1}, e)`. -/
theorem local_determinacy_global {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) :
    ∃ ε > 0, ∃ δ > 0, δ ≤ ε ∧
      (∀ u : Par ι E, ‖u‖ < δ →
        ‖implicitSol F hF hL u‖ < ε / 2 ∧ Solves F u (implicitSol F hF hL u) ∧
          ContDiffAt ℝ 1 (implicitSol F hF hL) u) ∧
      (∀ u : Par ι E, ‖u‖ < δ → ∀ x : SeqV ι, ‖x‖ < ε → Solves F u x →
        x = implicitSol F hF hL u) := by
  set H := homeo F hF hL with hH
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (H.open_source.mem_nhds (zero_mem_homeo_source hF hL))
  have hcd := contDiffAt_homeo_symm hF h0 hL
  have hsym0 := homeo_symm_zero hF h0 hL
  have hev1 : ∀ᶠ y in 𝓝 (0 : Par ι E × SeqV ι), y ∈ H.target :=
    H.open_target.mem_nhds (zero_mem_homeo_target hF h0 hL)
  have hev2 : ∀ᶠ y in 𝓝 (0 : Par ι E × SeqV ι), ‖H.symm y‖ < ε / 2 := by
    have ht := hcd.continuousAt.tendsto
    rw [hsym0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds 0 (half_pos hε))).mono
      (fun y hy => by simpa using hy)
  have hev3 : ∀ᶠ y in 𝓝 (0 : Par ι E × SeqV ι), ContDiffAt ℝ 1 H.symm y :=
    hcd.eventually (by simp)
  have hpull : Filter.Tendsto (fun u : Par ι E => ((u, (0 : SeqV ι)) : Par ι E × SeqV ι))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun u : Par ι E => ((u, (0 : SeqV ι)) : Par ι E × SeqV ι)) :=
      continuous_id.prodMk continuous_const
    have h := hc.tendsto (0 : Par ι E)
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
    have hsnd : eqMap F hF.continuous (H.symm (u, 0)) = 0 := congrArg Prod.snd hright
    refine ⟨lt_of_le_of_lt (norm_snd_le _) hnorm, ?_, ?_⟩
    · rw [← eqMap_eq_zero_iff F hF.continuous]
      have hq : ((u, implicitSol F hF hL u) : Par ι E × SeqV ι) = H.symm (u, 0) :=
        Prod.ext hfst.symm rfl
      rw [hq]
      exact hsnd
    · exact contDiffAt_snd.comp u (hcds.comp u (contDiffAt_id.prodMk contDiffAt_const))
  · have hsrc : ((u, x) : Par ι E × SeqV ι) ∈ H.source := by
      apply hεsub
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
      exact max_lt (lt_of_lt_of_le hu (min_le_right _ _)) hx
    have hHx : H (u, x) = (u, 0) :=
      Prod.ext rfl ((eqMap_eq_zero_iff F hF.continuous u x).mpr hsol)
    have h := H.left_inv hsrc
    rw [hHx] at h
    exact (congrArg Prod.snd h).symm

/-! ### Only the behaviour near the steady state matters (bump cut-off) -/

/-- Woodford (2003), App. A.3, p. 631: the bump-cut-off version `χ_r · F` of the period
conditions, equal to `F` on the ball of radius `r/4` and to `0` outside the ball of radius
`r/2`. -/
noncomputable def cutoff (F : Arg ι E → (ι → ℝ)) (r : ℝ) (hr : 0 < r) : Arg ι E → (ι → ℝ) :=
  fun p => (⟨r / 4, r / 2, by positivity, by linarith⟩ : ContDiffBump (0 : Arg ι E)) p • F p

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 631: the cut-off agrees with `F` near the steady state. -/
theorem cutoff_eq {F : Arg ι E → (ι → ℝ)} {r : ℝ} (hr : 0 < r) {p : Arg ι E}
    (hp : ‖p‖ ≤ r / 4) : cutoff F r hr p = F p := by
  rw [cutoff, ContDiffBump.one_of_mem_closedBall _ (mem_closedBall_zero_iff.mpr hp), one_smul]

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 631: the cut-off agrees with `F` on a neighbourhood of `0`. -/
theorem cutoff_eventuallyEq (F : Arg ι E → (ι → ℝ)) {r : ℝ} (hr : 0 < r) :
    cutoff F r hr =ᶠ[𝓝 0] F := by
  filter_upwards [Metric.ball_mem_nhds (0 : Arg ι E) (by positivity : 0 < r / 4)] with p hp
  rw [mem_ball_zero_iff] at hp
  exact cutoff_eq hr hp.le

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632: the cut-off has the same derivative at the steady state. -/
theorem fderiv_cutoff (F : Arg ι E → (ι → ℝ)) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (cutoff F r hr) 0 = fderiv ℝ F 0 :=
  (cutoff_eventuallyEq F hr).fderiv_eq

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632: if `F` is `Cᵏ` on the ball of radius `r`, the cut-off is
`Cᵏ` everywhere. -/
theorem contDiff_cutoff {F : Arg ι E → (ι → ℝ)} {r : ℝ} (hr : 0 < r) {k : ℕ}
    (hF : ∀ p : Arg ι E, ‖p‖ < r → ContDiffAt ℝ k F p) : ContDiff ℝ k (cutoff F r hr) := by
  set φ : ContDiffBump (0 : Arg ι E) := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hφ
  refine contDiff_iff_contDiffAt.mpr fun p => ?_
  by_cases hp : ‖p‖ < r
  · exact φ.contDiffAt.smul (hF p hp)
  · have hnot : p ∉ tsupport φ := by
      rw [φ.tsupport_eq, mem_closedBall_zero_iff]
      have : φ.rOut = r / 2 := rfl
      rw [this]
      push Not at hp ⊢
      linarith
    have hev : cutoff F r hr =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with q hq
      change φ q • F q = 0
      rw [hq, Pi.zero_apply, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: a function `Cᵏ` at the steady state is `Cᵏ` on a ball
around it. -/
theorem exists_ball_contDiffAt {F : Arg ι E → (ι → ℝ)} {k : ℕ} (hF : ContDiffAt ℝ k F 0) :
    ∃ r > 0, ∀ p : Arg ι E, ‖p‖ < r → ContDiffAt ℝ k F p := by
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hF.eventually (by simp))
  exact ⟨r, hr, fun p hp => h (by rwa [dist_zero_right])⟩

/-- Woodford (2003), App. A.3, p. 632: the cut-off has the same linearised operator, parameter
derivative and log-linear solution operator as `F`. -/
theorem lin_cutoff (F : Arg ι E → (ι → ℝ)) {r : ℝ} (hr : 0 < r) :
    linOp (cutoff F r hr) = linOp F ∧ bOp (cutoff F r hr) = bOp F ∧
      linSol (cutoff F r hr) = linSol F := by
  have h := fderiv_cutoff F hr
  have h1 : linOp (cutoff F r hr) = linOp F := by
    simp only [linOp, M1, M2, M3, d1, d2, d3, h]
  have h2 : bOp (cutoff F r hr) = bOp F := by
    simp only [bOp, d1, dE, h]
  refine ⟨h1, h2, ?_⟩
  simp only [linSol, linInv, h1, h2]

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 631: near the steady state the cut-off conditions and the
original conditions have the same solutions. -/
theorem solves_cutoff_iff {F : Arg ι E → (ι → ℝ)} {r : ℝ} (hr : 0 < r) {u : Par ι E}
    {x : SeqV ι} (hu : ‖u‖ ≤ r / 4) (hx : ‖x‖ ≤ r / 4) :
    Solves (cutoff F r hr) u x ↔ Solves F u x := by
  have hp : ∀ t, ‖pt4 (u, x) t‖ ≤ r / 4 := fun t =>
    (norm_pt4_le _ t).trans (by rw [Prod.norm_mk]; exact max_le hu hx)
  refine forall_congr' fun t => ?_
  have h : cutoff F r hr (pt4 (u, x) t) = F (pt4 (u, x) t) := cutoff_eq hr (hp t)
  exact ⟨fun h' => h ▸ h', fun h' => h.trans h'⟩

/-! ### The local determinacy theorem -/

/-- **Woodford (2003), App. A.3, pp. 632–633: local determinacy of `n`-dimensional
perfect-foresight systems with predetermined variables.** If `F` is `C¹` near the steady state,
`F(0) = 0` and the operator (A.8) is invertible on `ℓ∞(ℕ, ℝⁿ)` (equivalently, the root condition
of `isUnit_linOp_iff`), there are `ε, δ > 0` (below any `η > 0`) and a map
`X : (x_{−1}, e) ↦ x` with `X(0) = 0` whose derivative at `0` is the solution operator of the
linearised system (A.10), such that for every initial condition and disturbance sequence with
`‖(x_{−1}, e)‖ < δ`: `X(x_{−1}, e)` is an equilibrium, within `ε/2` of the steady state, `X` is
`C¹` there, and every equilibrium staying within `ε` of the steady state equals it. -/
theorem local_determinacy {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : Par ι E → SeqV ι, X 0 = 0 ∧
      HasFDerivAt X (linSol F) 0 ∧
      ∀ u : Par ι E, ‖u‖ < δ → ‖X u‖ < ε / 2 ∧ Solves F u (X u) ∧ ContDiffAt ℝ 1 X u ∧
        ∀ x : SeqV ι, ‖x‖ < ε → Solves F u x → x = X u := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hF
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : Arg ι E, ‖p‖ < r → ContDiffAt ℝ 1 F p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set G := cutoff F r hr with hG
  have hG1 : ContDiff ℝ 1 G := contDiff_cutoff hr hball
  obtain ⟨hlo, -, hls⟩ := lin_cutoff F hr
  have hL' : IsUnit (linOp G) := by rw [hlo]; exact hL
  have hG0 : G 0 = 0 := by rw [hG, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, hex, huniq⟩ := local_determinacy_global hG1 hG0 hL'
  set X := implicitSol G hG1 hL' with hX
  have hX0 : X 0 = 0 := implicitSol_zero hG1 hG0 hL'
  have hcont : ContinuousAt X 0 := (hasFDerivAt_implicitSol hG1 hG0 hL').continuousAt
  have hev : ∀ᶠ u in 𝓝 (0 : Par ι E), ‖X u‖ < r / 8 := by
    have ht := hcont.tendsto
    rw [hX0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds (0 : SeqV ι)
      (by positivity : (0 : ℝ) < r / 8))).mono (fun u hu => by simpa using hu)
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₁) (r / 4), lt_min (lt_min hδ₀ hδ₁) (by positivity),
    (min_le_right _ _).trans hrη, X, hX0, ?_, fun u hu => ?_⟩
  · rw [← hls]
    exact hasFDerivAt_implicitSol hG1 hG0 hL'
  have hu0 : ‖u‖ < δ₀ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_left _ _))
  have hu1 : dist u 0 < δ₁ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_right _ _))
  have hu4 : ‖u‖ ≤ r / 4 := (lt_of_lt_of_le hu (min_le_right _ _)).le
  obtain ⟨hXn, hXs, hXc⟩ := hex u hu0
  have hXr := hδ₁P hu1
  have hXr4 : ‖X u‖ ≤ r / 4 := by linarith
  refine ⟨by rw [lt_div_iff₀ two_pos]; exact lt_min (by linarith) (by linarith),
    (solves_cutoff_iff hr hu4 hXr4).mp hXs, hXc, fun x hx hsol => ?_⟩
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  exact huniq u hu0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solves_cutoff_iff hr hu4 hx4).mpr hsol)

omit [FiniteDimensional ℝ E] in
/-- **The invertibility condition is the root condition** (Woodford (2003), App. A.3, eq. (A.9),
p. 632, made exact in `LinearSystems.isUnit_sysOp_iff_roots`): with `f_j = D_jF(0)`, the
operator (A.8) is invertible iff `det(f₃λ² + f₂λ + f₁) ≢ 0`, no root lies on the unit circle,
exactly `n` lie inside, and the homogeneous linearised system with `x̂_{−1} = 0` has no nonzero
bounded solution. -/
theorem isUnit_linOp_iff (F : Arg ι E → (ι → ℝ)) :
    IsUnit (linOp F) ↔ quadPoly (M1 F) (M2 F) (M3 F) ≠ 0 ∧
      (∀ μ ∈ ((quadPoly (M1 F) (M2 F) (M3 F)).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly (M1 F) (M2 F) (M3 F)).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ HomInjective (M1 F) (M2 F) (M3 F) := by
  rw [linOp, isUnit_sysOp_iff, linDeterminate_iff]

/-- **Woodford (2003), App. A.3, pp. 632–633, with the root condition (A.9) made exact**: if `F`
is `C¹` near the steady state, `F(0) = 0`, `det(f₃λ² + f₂λ + f₁)` is not identically zero, has no
root on the unit circle and exactly `n` roots inside it, and the genericity condition holds,
then the conclusions of `local_determinacy` hold. For `det f₃ ≠ 0` the root conditions are the
book's "`n` inside and `n` outside" (`LinearSystems.linDeterminate_iff_of_det`). -/
theorem local_determinacy_of_roots {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0)
    (h0 : F 0 = 0) (hreg : quadPoly (M1 F) (M2 F) (M3 F) ≠ 0)
    (hnu : ∀ μ ∈ ((quadPoly (M1 F) (M2 F) (M3 F)).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1)
    (hcount : Multiset.card (((quadPoly (M1 F) (M2 F) (M3 F)).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι)
    (hgen : HomInjective (M1 F) (M2 F) (M3 F)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : Par ι E → SeqV ι, X 0 = 0 ∧
      HasFDerivAt X (linSol F) 0 ∧
      ∀ u : Par ι E, ‖u‖ < δ → ‖X u‖ < ε / 2 ∧ Solves F u (X u) ∧ ContDiffAt ℝ 1 X u ∧
        ∀ x : SeqV ι, ‖x‖ < ε → Solves F u x → x = X u :=
  local_determinacy hF h0 ((isUnit_linOp_iff F).mpr ⟨hreg, hnu, hcount, hgen⟩) hη

/-! ### Accuracy of the log-linear approximation (erratum E18) -/

/-- Woodford (2003), App. A.3, p. 633, E18 (**first order under `C¹`**): every equilibrium near
the steady state is within `c ‖(x_{−1}, e)‖` of the solution of the linearised system (A.10),
for every `c > 0` once the disturbances are small enough — an `o(‖u‖)` error. -/
theorem first_order_loc {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) :
    ∃ ε > 0, ∀ c > 0, ∃ δ > 0, ∀ u : Par ι E, ‖u‖ < δ → ∀ x : SeqV ι, ‖x‖ < ε →
      Solves F u x → ‖x - linSol F u‖ ≤ c * ‖u‖ := by
  obtain ⟨ε, hε, -, δ₀, hδ₀, -, X, hX0, hXd, hX⟩ := local_determinacy hF h0 hL one_pos
  refine ⟨ε, hε, fun c hc => ?_⟩
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := Metric.eventually_nhds_iff.mp (hXd.isLittleO.def hc)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun u hu x hx hsol => ?_⟩
  have h1 := hδ₁P (by rw [dist_zero_right]; exact lt_of_lt_of_le hu (min_le_right _ _))
  simp only [hX0, sub_zero] at h1
  rw [(hX u (lt_of_lt_of_le hu (min_le_left _ _))).2.2.2 x hx hsol]
  exact h1

/-- Woodford (2003), App. A.3, p. 630 ("Taylor's theorem"): if `DF` is Lipschitz at the steady
state on the ball of radius `r`, the first-order Taylor remainder is at most `K ‖z‖²`
(vector-valued version of `LocalIFT.abs_remainder_le3`). -/
theorem norm_remainder_le {G W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : G → W} (hF : ContDiff ℝ 1 F) {K r : ℝ}
    (hK : 0 ≤ K) (hL : ∀ z : G, ‖z‖ ≤ r → ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ K * ‖z‖)
    (z : G) (hz : ‖z‖ ≤ r) : ‖F z - F 0 - fderiv ℝ F 0 z‖ ≤ K * ‖z‖ ^ 2 := by
  have key := (convex_closedBall (0 : G) ‖z‖).norm_image_sub_le_of_norm_fderiv_le'
    (f := F) (φ := fderiv ℝ F 0) (C := K * ‖z‖) (fun w _ => (hF.differentiable one_ne_zero) w)
    (fun w hw => by
      rw [mem_closedBall_zero_iff] at hw
      exact (hL w (hw.trans hz)).trans (mul_le_mul_of_nonneg_left hw hK))
    (Metric.mem_closedBall_self (norm_nonneg z)) (mem_closedBall_zero_iff.mpr le_rfl)
  simp only [sub_zero] at key
  calc _ ≤ K * ‖z‖ * ‖z‖ := key
    _ = K * ‖z‖ ^ 2 := by ring

/-- Woodford (2003), App. A.3, p. 633, erratum E18: a `C²` map has a derivative that is
Lipschitz near the steady state (vector-valued version of `LocalIFT.lipschitz_fderiv3`). -/
theorem lipschitz_fderiv {G W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : G → W} (hF : ContDiff ℝ 2 F) :
    ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧
      ∀ z : G, ‖z‖ ≤ r → ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ K * ‖z‖ := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.contDiffAt.exists_lipschitzOnWith (x := 0)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, r / 2, K.coe_nonneg, half_pos hr, fun z hz => ?_⟩
  have hz' : z ∈ t := hrt (by rw [mem_ball_zero_iff]; linarith)
  have h0 : (0 : G) ∈ t := hrt (Metric.mem_ball_self hr)
  have h := hK.dist_le_mul z hz' 0 h0
  rwa [dist_eq_norm, dist_eq_norm, sub_zero] at h

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the linearised operator applied to the solution
of the linearised system is minus the parameter part. -/
theorem linOp_linSol {F : Arg ι E → (ι → ℝ)} (hL : IsUnit (linOp F)) (u : Par ι E) :
    linOp F (linSol F u) = -bOp F u := by
  change linOp F (-(linInv F (bOp F u))) = -bOp F u
  rw [map_neg, linOp_linInv hL]

/-- Woodford (2003), App. A.3, p. 633, corrected per E18 (**global form**): if `DF` is Lipschitz
near the steady state, the exact equilibrium differs from the solution of (A.10) by at most
`C ‖(x_{−1}, e)‖²`. -/
theorem second_order_global {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) {K r : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ z : Arg ι E, ‖z‖ ≤ r → ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ K * ‖z‖) (hr : 0 < r) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ u : Par ι E, ‖u‖ < δ →
      ‖implicitSol F hF hL u - linSol F u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨ε, hε, δ₁, hδ₁, -, hex, -⟩ := local_determinacy_global hF h0 hL
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ :=
    Metric.eventually_nhds_iff.mp ((hasFDerivAt_implicitSol hF h0 hL).isLittleO.def one_pos)
  set C1 := ‖linSol F‖ + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  have hC1one : 1 ≤ C1 := le_add_of_nonneg_left (norm_nonneg _)
  refine ⟨‖linInv F‖ * (K * C1 ^ 2), min (min δ₁ δ₂) (r / C1), by positivity,
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
  set x := implicitSol F hF hL u with hx
  have hxb : ‖x‖ ≤ C1 * ‖u‖ := by
    have h := hδ₂P hu2
    rw [implicitSol_zero hF h0 hL, sub_zero, sub_zero, one_mul] at h
    calc ‖x‖ = ‖(x - linSol F u) + linSol F u‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - linSol F u‖ + ‖linSol F u‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖linSol F‖ * ‖u‖ := add_le_add h ((linSol F).le_opNorm u)
      _ = C1 * ‖u‖ := by rw [hC1]; ring
  have hcoord : ∀ t, ‖linOp F (x - linSol F u) t‖ ≤ K * (C1 * ‖u‖) ^ 2 := by
    intro t
    have hz : ‖pt4 (u, x) t‖ ≤ C1 * ‖u‖ := by
      refine (norm_pt4_le _ t).trans ?_
      rw [Prod.norm_mk]
      exact max_le (le_mul_of_one_le_left (norm_nonneg _) hC1one) hxb
    have hrem := norm_remainder_le hF hK hLip _ (hz.trans hu3)
    have hst : F (pt4 (u, x) t) = 0 := hsol t
    have e1 : linOp F (x - linSol F u) t =
        -(F (pt4 (u, x) t) - F 0 - fderiv ℝ F 0 (pt4 (u, x) t)) := by
      rw [map_sub, linOp_linSol hL, sub_neg_eq_add, lp.coeFn_add, Pi.add_apply, linOp_apply,
        bOp_apply, hst, h0, pt4, fderiv_zero_apply4, lagV_split u.1 (fun s => x s) t, map_add]
      abel
    rw [e1, norm_neg]
    calc _ ≤ K * ‖pt4 (u, x) t‖ ^ 2 := hrem
      _ ≤ K * (C1 * ‖u‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) hK
  have hlin : ‖linOp F (x - linSol F u)‖ ≤ K * (C1 * ‖u‖) ^ 2 :=
    LocalIFT.norm_seq_le (by positivity) hcoord
  calc ‖x - linSol F u‖ = ‖linInv F (linOp F (x - linSol F u))‖ := by rw [linInv_linOp hL]
    _ ≤ ‖linInv F‖ * ‖linOp F (x - linSol F u)‖ := (linInv F).le_opNorm _
    _ ≤ ‖linInv F‖ * (K * (C1 * ‖u‖) ^ 2) := mul_le_mul_of_nonneg_left hlin (norm_nonneg _)
    _ = ‖linInv F‖ * (K * C1 ^ 2) * ‖u‖ ^ 2 := by ring

/-- Woodford (2003), App. A.3, p. 633 ("coincides with this solution … up to an error term of
order `O(‖u‖²)`"), **local form**, corrected per E18: if `F` is `C²` near the steady state, every
equilibrium within `ε` of the steady state satisfies `‖x − x̂(x_{−1}, e)‖ ≤ C ‖(x_{−1}, e)‖²`
for `‖(x_{−1}, e)‖ < δ`, `x̂` the solution of the linearised system (A.10). -/
theorem second_order_loc {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 2 F 0) (h0 : F 0 = 0)
    (hL : IsUnit (linOp F)) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ C : ℝ, ∀ u : Par ι E, ‖u‖ < δ → ∀ x : SeqV ι,
      ‖x‖ < ε → Solves F u x → ‖x - linSol F u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hF
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : Arg ι E, ‖p‖ < r → ContDiffAt ℝ 2 F p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set G := cutoff F r hr with hG
  have hG2 : ContDiff ℝ 2 G := contDiff_cutoff hr hball
  have hG1 : ContDiff ℝ 1 G := hG2.of_le (by norm_num)
  obtain ⟨hlo, -, hls⟩ := lin_cutoff F hr
  have hL' : IsUnit (linOp G) := by rw [hlo]; exact hL
  have hG0 : G 0 = 0 := by rw [hG, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, -, huniq⟩ := local_determinacy_global hG1 hG0 hL'
  obtain ⟨K, r', hK, hr', hLip⟩ := lipschitz_fderiv hG2
  obtain ⟨C, δ₂, hδ₂, hC⟩ := second_order_global hG1 hG0 hL' hK hLip hr'
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₂) (r / 4), lt_min (lt_min hδ₀ hδ₂) (by positivity),
    (min_le_right _ _).trans hrη, C, fun u hu x hx hsol => ?_⟩
  have hu0 : ‖u‖ < δ₀ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_left _ _))
  have hu2 : ‖u‖ < δ₂ := lt_of_lt_of_le hu ((min_le_left _ _).trans (min_le_right _ _))
  have hu4 : ‖u‖ ≤ r / 4 := (lt_of_lt_of_le hu (min_le_right _ _)).le
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  have hxX := huniq u hu0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solves_cutoff_iff hr hu4 hx4).mpr hsol)
  rw [← hls, hxX]
  exact hC u hu2

/-! ### Necessity: what fails when the root condition fails -/

/-- Woodford (2003), App. A.3, p. 633 (**necessity, existence half**): if the disturbances can
move every equation independently (`D₄F(0)` onto) and there is a solution map `X` with
`X(0) = 0` that is differentiable at the steady state, then the operator (A.8) is surjective:
differentiating `Φ(u, X(u)) = 0` gives `(f₁ L + f₂ + f₃ S) DX(0) = −B`. -/
theorem surjective_of_solution_map {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0)
    (hE : Function.Surjective (dE F)) {X : Par ι E → SeqV ι} {δ : ℝ}
    (hδ : 0 < δ) (hX0 : X 0 = 0) (hXd : DifferentiableAt ℝ X 0)
    (hX : ∀ u : Par ι E, ‖u‖ < δ → Solves F u (X u)) : Function.Surjective (linOp F) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt hF
  set G := cutoff F r hr with hG
  have hG1 : ContDiff ℝ 1 G := contDiff_cutoff hr hball
  obtain ⟨hlo, hbo, -⟩ := lin_cutoff F hr
  have hdE : dE G = dE F := by simp only [hG, dE, fderiv_cutoff]
  -- `u ↦ Φ_G(u, X u)` vanishes near `0`
  have hev : (fun u => eqMap G hG1.continuous (u, X u)) =ᶠ[𝓝 0] fun _ => 0 := by
    have h1 : ∀ᶠ u in 𝓝 (0 : Par ι E), ‖X u‖ < r / 4 := by
      have ht := hXd.continuousAt.tendsto
      rw [hX0] at ht
      exact (ht.eventually (Metric.ball_mem_nhds (0 : SeqV ι)
        (by positivity : (0 : ℝ) < r / 4))).mono (fun u hu => by simpa using hu)
    have h2 : ∀ᶠ u in 𝓝 (0 : Par ι E), ‖u‖ < min δ (r / 4) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Par ι E)
        (lt_min hδ (by positivity : (0 : ℝ) < r / 4))] with u hu
      rwa [mem_ball_zero_iff] at hu
    filter_upwards [h1, h2] with u hu1 hu2
    rw [eqMap_eq_zero_iff]
    exact (solves_cutoff_iff hr (hu2.le.trans (min_le_right _ _)) hu1.le).mpr
      (hX u (hu2.trans_le (min_le_left _ _)))
  -- its derivative at `0`
  have hn := (hasStrictFDerivAt_nem hG1 ptL norm_ptL_le 0).hasFDerivAt
  rw [nemD_zero hG1] at hn
  have hp : HasFDerivAt (fun u : Par ι E => ((u, X u) : Par ι E × SeqV ι))
      ((ContinuousLinearMap.id ℝ (Par ι E)).prod (fderiv ℝ X 0)) 0 :=
    (hasFDerivAt_id (0 : Par ι E)).prodMk hXd.hasFDerivAt
  have hp0 : ((0 : Par ι E), X 0) = (0 : Par ι E × SeqV ι) := by rw [hX0]; rfl
  rw [← hp0] at hn
  have hD := hn.comp (0 : Par ι E) hp
  have hc : HasFDerivAt (fun u => eqMap G hG1.continuous (u, X u))
      (0 : Par ι E →L[ℝ] SeqV ι) 0 :=
    (hasFDerivAt_const (0 : SeqV ι) (0 : Par ι E)).congr_of_eventuallyEq hev
  have hzero := hD.unique hc
  -- choose disturbances realising any forcing
  obtain ⟨g, hg⟩ := (dE F : E →ₗ[ℝ] (ι → ℝ)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hE)
  set R : (ι → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap g with hR
  have hRinv : ∀ v, dE F (R v) = v := fun v => by
    have := congrArg (fun φ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) => φ v) hg
    simpa [hR] using this
  intro y
  set du : Par ι E := (0, pw R (-y)) with hdu
  refine ⟨fderiv ℝ X 0 du, ?_⟩
  have h1 := congrArg (fun T : Par ι E →L[ℝ] SeqV ι => T du) hzero
  change linOp G (fderiv ℝ X 0 du) + bOp G du = 0 at h1
  rw [hlo, hbo] at h1
  have hb : bOp F du = -y := by
    refine seq_ext fun t => ?_
    rw [bOp_apply, hdu]
    have hl : lagV (0 : ι → ℝ) (0 : ℕ → ι → ℝ) t = 0 := by cases t <;> rfl
    simp only [hl, map_zero, zero_add, pw_apply, lp.coeFn_neg, Pi.neg_apply, map_neg, hRinv]
  rw [hb] at h1
  exact (add_neg_eq_zero.mp h1)

/-- Woodford (2003), App. A.3, pp. 632–633 (**necessity, uniqueness half**): if the operator
(A.8) is surjective but not injective, local uniqueness fails — there are equilibria other than
the steady state, with `x_{−1} = x̄` and no disturbances, arbitrarily close to the steady state.
(The kernel is finite-dimensional, `LinearSystems.eq_zero_of_regular`, so the
implicit-function theorem for a surjective derivative with complemented kernel applies.) -/
theorem not_locally_unique {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hs : Function.Surjective (linOp F)) (hni : ¬ Function.Injective (linOp F)) :
    ∀ ε > 0, ∃ x : SeqV ι, x ≠ 0 ∧ ‖x‖ < ε ∧ Solves F 0 x := by
  intro ε hε
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt hF
  set G := cutoff F r hr with hG
  have hG1 : ContDiff ℝ 1 G := contDiff_cutoff hr hball
  obtain ⟨hlo, -, -⟩ := lin_cutoff F hr
  have hG0 : G 0 = 0 := by rw [hG, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  set f : SeqV ι → SeqV ι := fun x => eqMap G hG1.continuous (0, x) with hfdef
  have hf : HasStrictFDerivAt f (linOp F) 0 := by
    have hn := hasStrictFDerivAt_nem hG1 ptL norm_ptL_le 0
    rw [nemD_zero hG1] at hn
    have hi : HasStrictFDerivAt (fun x : SeqV ι => ((0 : Par ι E), x))
        (ContinuousLinearMap.inr ℝ (Par ι E) (SeqV ι)) 0 :=
      (ContinuousLinearMap.inr ℝ (Par ι E) (SeqV ι)).hasStrictFDerivAt
    have h00 : ((0 : Par ι E), (0 : SeqV ι)) = (0 : Par ι E × SeqV ι) := rfl
    rw [← h00] at hn
    refine (hn.comp (0 : SeqV ι) hi).congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
    change linOp G x + bOp G 0 = linOp F x
    rw [map_zero, add_zero, hlo]
  have hrange : (linOp F).range = ⊤ := LinearMap.range_eq_top.mpr hs
  have hreg : quadPoly (M1 F) (M2 F) (M3 F) ≠ 0 := quadPoly_ne_zero_of_surjective hs
  have hfin : FiniteDimensional ℝ (linOp F).ker := by
    let ev : (linOp F).ker →ₗ[ℝ] (ι → ℝ) :=
      { toFun := fun x => (x : SeqV ι) 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective ev := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have hsol : SolvesLin (M1 F) (M2 F) (M3 F) 0 0 (fun t => (x : SeqV ι) t) := by
        intro t
        have := (sysOp_eq_iff _ _ _ _ _).mp (LinearMap.mem_ker.mp x.2) t
        simpa using this
      have := eq_zero_of_regular hreg (boundedSeq_coe _) hsol hx
      exact Subtype.ext (seq_ext fun t => congrFun this t)
    exact Module.Finite.of_injective ev hinj
  have hker : (linOp F).ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional _
  -- a nonzero kernel element
  obtain ⟨k, hk0, hk⟩ : ∃ k : SeqV ι, k ≠ 0 ∧ linOp F k = 0 := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact ⟨a - b, sub_ne_zero.mpr hne, by rw [map_sub, hab, sub_self]⟩
  set k' : (linOp F).ker := ⟨k, hk⟩ with hk'
  have hk'0 : k' ≠ 0 := fun h => hk0 (congrArg Subtype.val h)
  set H := hf.implicitToOpenPartialHomeomorphOfComplemented f (linOp F) hrange hker with hH
  have hf0 : f 0 = 0 := (eqMap_eq_zero_iff G hG1.continuous 0 0).mpr (solves_zero hG0)
  have hsrc : (0 : SeqV ι) ∈ H.source :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hrange hker
  have htar : (f 0, (0 : (linOp F).ker)) ∈ H.target :=
    hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hrange hker
  rw [hf0] at htar
  have hH0 : H 0 = (0, 0) := by
    rw [hH, HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_self, hf0]
  have hsymm0 : H.symm (0, 0) = 0 := by
    have := H.left_inv hsrc
    rwa [hH0] at this
  -- the curve `s ↦ H⁻¹(0, s k)` of zeros of `f`
  have hpath : Filter.Tendsto (fun s : ℝ => (((0 : SeqV ι), s • k') : SeqV ι × (linOp F).ker))
      (𝓝 0) (𝓝 (0, 0)) := by
    have hc : Continuous (fun s : ℝ => (((0 : SeqV ι), s • k') : SeqV ι × (linOp F).ker)) :=
      continuous_const.prodMk (continuous_id.smul continuous_const)
    have := hc.tendsto 0
    simpa using this
  have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ), (((0 : SeqV ι), s • k') : SeqV ι × (linOp F).ker) ∈ H.target :=
    hpath.eventually (H.open_target.mem_nhds htar)
  have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), ‖H.symm ((0 : SeqV ι), s • k')‖ < min ε (r / 4) := by
    have hcs : ContinuousAt H.symm (0, 0) := H.continuousAt_symm htar
    have ht := hcs.tendsto.comp hpath
    rw [hsymm0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds (0 : SeqV ι)
      (lt_min hε (by positivity : (0 : ℝ) < r / 4)))).mono
      fun s hs => by rwa [dist_zero_right] at hs
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
  set s : ℝ := ρ / 2 with hsdef
  have hs0 : s ≠ 0 := by positivity
  obtain ⟨hst, hsn⟩ := hρP (show dist s 0 < ρ by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  set x := H.symm ((0 : SeqV ι), s • k') with hx
  have hHx : H x = ((0 : SeqV ι), s • k') := H.right_inv hst
  have hHx' := hHx
  rw [hH, HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply] at hHx'
  have hfx : f x = 0 := congrArg Prod.fst hHx'
  refine ⟨x, fun hx0 => ?_, hsn.trans_le (min_le_left _ _), ?_⟩
  · have h2 := congrArg Prod.snd hHx'
    simp only [hx0, sub_zero, map_zero] at h2
    exact smul_ne_zero hs0 hk'0 h2.symm
  · have hx4 : ‖x‖ ≤ r / 4 := (hsn.trans_le (min_le_right _ _)).le
    exact (solves_cutoff_iff hr (by rw [norm_zero]; positivity) hx4).mp
      ((eqMap_eq_zero_iff G hG1.continuous 0 x).mp hfx)

/-- **The converse of the local determinacy theorem** (Woodford (2003), App. A.3, pp. 632–633):
if the disturbances move every equation independently (`D₄F(0)` onto) and the exact model is
locally determinate *with a solution map differentiable at the steady state* (the conclusion of
the implicit-function theorem) — some `X` with `X(0) = 0`, differentiable at `0`, solving the
conditions for small `(x_{−1}, e)`, and the steady state the only equilibrium within `ε` when
`x_{−1} = x̄`, `e = 0` — then (A.8) is invertible, i.e. the root condition holds. -/
theorem isUnit_of_local_determinacy {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0)
    (h0 : F 0 = 0) (hE : Function.Surjective (dE F)) {X : Par ι E → SeqV ι} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hX0 : X 0 = 0) (hXd : DifferentiableAt ℝ X 0)
    (hX : ∀ u : Par ι E, ‖u‖ < δ → Solves F u (X u))
    (huniq : ∀ x : SeqV ι, ‖x‖ < ε → Solves F 0 x → x = 0) : IsUnit (linOp F) := by
  have hs := surjective_of_solution_map hF hE hδ hX0 hXd hX
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨?_, hs⟩
  by_contra hni
  obtain ⟨x, hx0, hxε, hxs⟩ := not_locally_unique hF h0 hs hni ε hε
  exact hx0 (huniq x hxε hxs)

/-- **Local determinacy with a first-order approximation holds exactly under the root
condition** (Woodford (2003), App. A.3, pp. 632–633): for a period condition `C¹` near the steady
state with `F(0) = 0` and disturbances moving every equation (`D₄F(0)` onto), the following are
equivalent: (i) the operator (A.8) is invertible on `ℓ∞(ℕ, ℝⁿ)` — equivalently the exact root
condition of `isUnit_linOp_iff`; (ii) there are `ε, δ > 0` and a solution map `X` with `X(0) = 0`,
differentiable at `0`, giving for every `‖(x_{−1}, e)‖ < δ` an equilibrium, which is the only one
within `ε` of the steady state. -/
theorem isUnit_linOp_iff_local_determinacy {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0)
    (h0 : F 0 = 0) (hE : Function.Surjective (dE F)) :
    IsUnit (linOp F) ↔ ∃ ε > 0, ∃ δ > 0, ∃ X : Par ι E → SeqV ι, X 0 = 0 ∧
      DifferentiableAt ℝ X 0 ∧ ∀ u : Par ι E, ‖u‖ < δ → Solves F u (X u) ∧
        ∀ x : SeqV ι, ‖x‖ < ε → Solves F u x → x = X u := by
  constructor
  · intro hL
    obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ := local_determinacy hF h0 hL one_pos
    exact ⟨ε, hε, δ, hδ, X, hX0, hXd.differentiableAt, fun u hu =>
      ⟨(hX u hu).2.1, (hX u hu).2.2.2⟩⟩
  · rintro ⟨ε, hε, δ, hδ, X, hX0, hXd, hX⟩
    refine isUnit_of_local_determinacy hF h0 hE hε hδ hX0 hXd (fun u hu => (hX u hu).1)
      fun x hx hsol => ?_
    rw [(hX 0 (by rw [norm_zero]; exact hδ)).2 x hx hsol, hX0]

/-! ### Counterexample: the root condition can fail with existence and uniqueness intact -/

/-- Woodford (2003), App. A.3, p. 633 (counterexample data): `n = 1`, scalar disturbance, the
period condition `x_t³ − e_t = 0`. -/
def Fcube (p : Arg (Fin 1) ℝ) : Fin 1 → ℝ := fun _ => p.2.1 0 ^ 3 - p.2.2.2

/-- Woodford (2003), App. A.3, p. 633 (counterexample): the coordinate `x_t` of the argument. -/
noncomputable def projB : Arg (Fin 1) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp ((ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ)))

/-- Woodford (2003), App. A.3, p. 633 (counterexample): the coordinate `e_t` of the argument. -/
noncomputable def projE : Arg (Fin 1) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ℝ).comp
    ((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ)))

/-- Woodford (2003), App. A.3, p. 633 (counterexample): the derivative of `x_t³ − e_t` at the
steady state is `−e_t` (the cube has zero derivative). -/
theorem hasFDerivAt_Fcube :
    HasFDerivAt Fcube (ContinuousLinearMap.pi fun _ : Fin 1 => -projE) 0 := by
  refine hasFDerivAt_pi'' fun i => ?_
  have hb : HasFDerivAt (fun p : Arg (Fin 1) ℝ => projB p) projB 0 := projB.hasFDerivAt
  have he : HasFDerivAt (fun p : Arg (Fin 1) ℝ => projE p) projE 0 := projE.hasFDerivAt
  have h := (hb.pow 3).sub he
  refine h.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
  simp [projB]

/-- Woodford (2003), App. A.3, p. 633 (counterexample): the derivative applied. -/
theorem fderiv_Fcube_apply (p : Arg (Fin 1) ℝ) : fderiv ℝ Fcube 0 p = fun _ => -p.2.2.2 := by
  rw [hasFDerivAt_Fcube.fderiv]
  funext i
  simp [projE]

/-- Woodford (2003), App. A.3, p. 633 (counterexample): the linearised operator vanishes, so the
root condition fails (indeed `det(f₃λ² + f₂λ + f₁) ≡ 0`). -/
theorem linOp_Fcube (x : SeqV (Fin 1)) : linOp Fcube x = 0 := by
  refine seq_ext fun t => ?_
  rw [linOp_apply]
  simp only [d1, d2, d3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, fderiv_Fcube_apply]
  funext i
  simp

/-- Woodford (2003), App. A.3, p. 633 (counterexample): the disturbance moves the equation,
`D₄F(0) e = −e`, onto `ℝ`. -/
theorem dE_Fcube_surjective : Function.Surjective (dE Fcube) := by
  intro y
  refine ⟨-y 0, ?_⟩
  simp only [dE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    fderiv_Fcube_apply, neg_neg]
  funext i
  rw [Subsingleton.elim i 0]

/-- Woodford (2003), App. A.3, p. 633 (counterexample): `x` is an equilibrium iff `x_t³ = e_t`
for every `t`. -/
theorem solves_Fcube_iff (u : Par (Fin 1) ℝ) (x : SeqV (Fin 1)) :
    Solves Fcube u x ↔ ∀ t, x t 0 ^ 3 = u.2 t := by
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    have := congrFun h 0
    simp only [Fcube, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [Fcube, Pi.zero_apply]
    linarith [h]

/-- Woodford (2003), App. A.3, p. 633 (counterexample): the real cube root. -/
noncomputable def cbrt (y : ℝ) : ℝ :=
  if 0 ≤ y then y ^ ((3 : ℕ) : ℝ)⁻¹ else -((-y) ^ ((3 : ℕ) : ℝ)⁻¹)

/-- Woodford (2003), App. A.3, p. 633 (counterexample): `(∛y)³ = y`. -/
theorem cbrt_pow (y : ℝ) : cbrt y ^ 3 = y := by
  unfold cbrt
  split_ifs with hy
  · exact Real.rpow_inv_natCast_pow hy (by norm_num)
  · have h := Real.rpow_inv_natCast_pow (x := -y) (by linarith) (n := 3) (by norm_num)
    rw [neg_pow, h]
    norm_num

/-- Woodford (2003), App. A.3, p. 633 (counterexample): a real `c` with `c³ = y` satisfies
`|c| ≤ max 1 |y|`. -/
theorem abs_le_of_pow_three {c y : ℝ} (h : c ^ 3 = y) : |c| ≤ max 1 |y| := by
  by_cases hc : |c| ≤ 1
  · exact hc.trans (le_max_left _ _)
  · push Not at hc
    refine le_trans ?_ (le_max_right _ _)
    rw [← h, abs_pow]
    have h1 : 1 ≤ |c| ^ 2 := by nlinarith
    calc |c| = |c| * 1 := (mul_one _).symm
      _ ≤ |c| * |c| ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| ^ 3 := by ring

/-- **The nonlinear converse cannot be strengthened to "existence or uniqueness fails"**
(Woodford (2003), App. A.3, pp. 632–633): for the smooth scalar condition `x_t³ = e_t`
(`F(0) = 0`, disturbance derivative onto) the operator (A.8) is zero, so the root condition fails
(`isUnit_linOp_iff`); nevertheless for **every** disturbance sequence there is exactly one
bounded equilibrium (`x_t = ∛e_t`). What fails is the first-order approximation: no solution map
with `X(0) = 0` is differentiable at the steady state (`surjective_of_solution_map`). -/
theorem cube_unique_without_root_condition :
    (∀ k : ℕ, ContDiff ℝ k Fcube) ∧ Fcube 0 = 0 ∧ Function.Surjective (dE Fcube) ∧
      ¬ IsUnit (linOp Fcube) ∧ (∀ u : Par (Fin 1) ℝ, ∃! x : SeqV (Fin 1), Solves Fcube u x) ∧
      ¬ ∃ X : Par (Fin 1) ℝ → SeqV (Fin 1), X 0 = 0 ∧ DifferentiableAt ℝ X 0 ∧
        ∃ δ > 0, ∀ u : Par (Fin 1) ℝ, ‖u‖ < δ → Solves Fcube u (X u) := by
  have hns : ¬ Function.Surjective (linOp Fcube) := by
    intro hs
    obtain ⟨x, hx⟩ := hs (toSeqV (fun _ _ => 1) ⟨1, fun _ _ => by simp⟩)
    rw [linOp_Fcube] at hx
    have h1 : (0 : ℝ) = 1 := congrFun (congrArg (fun y : SeqV (Fin 1) => y 0) hx) 0
    norm_num at h1
  refine ⟨fun k => ?_, ?_, dE_Fcube_surjective, fun hu => hns ?_, fun u => ?_, ?_⟩
  · refine contDiff_pi.mpr fun _ => ?_
    exact (projB.contDiff.pow 3).sub projE.contDiff
  · funext i
    simp [Fcube]
  · exact (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2
  · have hb : LinearSystems.BoundedSeq (fun (t : ℕ) (_ : Fin 1) => cbrt (u.2 t)) :=
      ⟨max 1 ‖u.2‖, fun t _ => (abs_le_of_pow_three (cbrt_pow _)).trans
        (max_le_max_left 1 (by rw [← Real.norm_eq_abs]; exact LocalIFT.norm_seq_apply_le _ t))⟩
    refine ⟨toSeqV _ hb, (solves_Fcube_iff u _).mpr fun t => cbrt_pow _, fun y hy => ?_⟩
    have hy' := (solves_Fcube_iff u y).mp hy
    refine seq_ext fun t => funext fun i => ?_
    rw [Subsingleton.elim i 0]
    exact (Odd.pow_injective (by decide : Odd 3)) ((hy' t).trans (cbrt_pow _).symm)
  · rintro ⟨X, hX0, hXd, δ, hδ, hX⟩
    exact hns (surjective_of_solution_map ((contDiff_pi.mpr fun _ =>
      (projB.contDiff.pow 3).sub projE.contDiff).contDiffAt) dE_Fcube_surjective hδ hX0 hXd hX)

end Woodford.PriceLevelDetermination.LocalIFTSystems
