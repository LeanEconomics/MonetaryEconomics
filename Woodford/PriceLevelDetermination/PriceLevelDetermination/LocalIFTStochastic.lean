/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.Nonlinear
import PriceLevelDetermination.ExpectationsFiniteTree

/-!
# Stochastic local determinacy on `L∞` processes

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 633–635, eqs. (A.11)–(A.13) (A.3-c):
the book asserts, citing Woodford (1986) and without proof, that the inverse and implicit
function theorems apply on sequences of bounded measurable functions with the `L∞` norm, that the
linearised operator (A.12) is invertible iff (A.13) has a unique bounded solution, and that the
locally unique stochastic equilibrium is approximated by the linear RE solution. `LocalIFT`
proves the perfect-foresight version (A.3-b); this module proves the stochastic version for the
scalar forward-looking class, for an arbitrary `ExpectationSystem`.

## Setting and what is assumed about `E_t`

Processes are elements of `Proc Ω = ℓ∞(ℕ × Ω)` (sup over dates **and** states); adaptedness is
not built into the space. The only properties of `E_t` used are the `ExpectationSystem` axioms
(linearity, constants, monotonicity, tower and known-earlier); from monotonicity and constants
(`ExpectationSystem.abs_E_le`) the operators `x ↦ (E_t x_t)_t` (`Ops.condE`) and the expectational
lead `x ↦ (E_t x_{t+1})_t` (`Ops.lead`) are bounded linear operators of norm at most one
(`Ops.norm_condE_le`, `Ops.norm_lead_le`); `E_t` commutes with geometrically dominated series by
the core's `ExpectationSystem.E_tsum`. Nothing else (no `PullOut`) is assumed.

## Main results

* Nemytskii operators: `nem`, `hasStrictFDerivAt_nem`, `contDiff_nem` (any index set, `C¹` `F` on
  a finite-dimensional space).
* The linearised operator `a + b L`: `Ops.isUnit_TOpS_iff` (invertible on bounded processes iff
  `|b| < |a|`, any nonempty state space), `Ops.linearRE_unique_iff` ((A.13) has a unique bounded
  adapted solution for every bounded adapted forcing iff `|b| < |a|`), the stochastic forward
  solution `Ops.TInvS_apply_adapted`, `Ops.linSolS_apply` (the core's `forwardSeries`).
* The class `E_t[G(x_t, x_{t+1}, E_t x_{t+1}, e_t)] = 0` (`Ops.SolvesS`), containing (A.11) and
  `F(x_t, E_t x_{t+1}, e_t) = 0`: the equilibrium map `Ops.eqMapS` (zeros = adapted solutions,
  `Ops.eqMapS_eq_zero_iff`), `Ops.hasStrictFDerivAt_eqMapS`, `Ops.contDiff_eqMapS`,
  `Ops.eqDS_zero` (derivative (A.12)).
* Implicit-function theorem: `Ops.local_determinacyS`, `Ops.hasFDerivAt_implicitSolS`, local form
  `Ops.local_determinacyS_loc`; (A.11) form `Ops.local_determinacyII`, exponential form
  `Ops.local_determinacy_expII`; indeterminacy `Ops.local_indeterminacyII`.
* Erratum E18: `Ops.first_order_loc` (`C¹`: error `o(‖e‖)`), `Ops.second_orderS`,
  `Ops.second_orderS_loc` (`C^{1,1}`/`C²`: `O(‖e‖²)`), `Ops.not_second_order_of_C1S` (`C¹` does not
  give `O(‖e‖²)`).
* Form `F(x_t, E_t x_{t+1}, e_t) = 0`: `Ops.solvesS_liftI_iff` under informational closure
  (`Ops.InfoClosed`; `perfectForesight_infoClosed`, `finiteTree_infoClosed`), and
  `formI_needs_closure` / `skewSystem_not_infoClosed` (without it there may be no adapted
  solution at all).
* Applications (exact stochastic Euler equations): Props. 2.3 (`wicksell_local_determinacyS`),
  2.6 (`taylor_local_determinacyS`, `taylor_local_indeterminacyS`, `taylor_exp_identity`),
  2.7 (`smooth_local_determinacyS`, `smooth_local_indeterminacyS`), 2.8
  (`inertial_local_determinacyS`, `inertial_local_indeterminacyS`), 2.11
  (`mg_local_determinacyS`), 2.12 (`nsw_local_determinacyS`, `nsw_local_indeterminacyS`), 2.13
  (`nsi_local_determinacyS`, `nsi_local_indeterminacyS`).

Not covered: predetermined variables and systems (`n > 1`) under uncertainty.
-/

namespace Woodford.PriceLevelDetermination.LocalIFTStochastic

open scoped ENNReal Topology
open Woodford.PriceLevelDetermination.LocalIFT (exists_bound_ball3 fderiv_close3 slopeA slopeB
  slopeC fderiv_zero_apply3 ne_zero_of_abs_lt abs_ratio_lt cutoff cutoff_eq contDiff_cutoff
  fderiv_cutoff exists_ball_contDiffAt abs_remainder_le3 lipschitz_fderiv3 slopes_of_hasFDerivAt)

/-! ### Bounded functions on an index set and the Nemytskii operator -/

/-- Woodford (2003), App. A.3, p. 634: the Banach space of bounded functions on an index set
(for the index set `ℕ × Ω` of dates and states, the book's `L∞` processes) with the sup norm. -/
abbrev BFun (I G : Type*) [NormedAddCommGroup G] : Type _ := lp (fun _ : I => G) ∞

variable {I G : Type*} [NormedAddCommGroup G]

/-- Woodford (2003), App. A.3, p. 634: each value is bounded by the sup norm. -/
theorem norm_apply_le (p : BFun I G) (i : I) : ‖p i‖ ≤ ‖p‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero p i

/-- Woodford (2003), App. A.3, p. 634: a uniformly bounded function as an element of `BFun`. -/
noncomputable def mkB (f : I → G) (hf : ∃ C, ∀ i, ‖f i‖ ≤ C) : BFun I G :=
  ⟨f, memℓp_infty (by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩)⟩

/-- Woodford (2003), App. A.3, p. 634: values of `mkB`. -/
@[simp] theorem mkB_apply (f : I → G) (hf : ∃ C, ∀ i, ‖f i‖ ≤ C) (i : I) : mkB f hf i = f i :=
  rfl

/-- Woodford (2003), App. A.3, p. 634: the sup norm is at most any uniform bound. -/
theorem norm_le_of_forall {p : BFun I G} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖p i‖ ≤ C) :
    ‖p‖ ≤ C :=
  lp.norm_le_of_forall_le hC h

variable [NormedSpace ℝ G]

/-- Woodford (2003), App. A.3, p. 634: pointwise bound for a multiplication operator. -/
theorem norm_mulOp_le {L : I → (G →L[ℝ] ℝ)} {C : ℝ} (hC : ∀ i, ‖L i‖ ≤ C) (p : BFun I G)
    (i : I) : ‖L i (p i)‖ ≤ max C 0 * ‖p‖ :=
  ((L i).le_of_opNorm_le ((hC i).trans (le_max_left C 0)) _).trans
    (mul_le_mul_of_nonneg_left (norm_apply_le p i) (le_max_right C 0))

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the multiplication operator
`p ↦ (L_i(p_i))_i` with uniformly bounded coefficients. -/
noncomputable def mulOp (L : I → (G →L[ℝ] ℝ)) (hL : ∃ C, ∀ i, ‖L i‖ ≤ C) :
    BFun I G →L[ℝ] BFun I ℝ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun p => mkB (fun i => L i (p i)) (by
        obtain ⟨C, hC⟩ := hL
        exact ⟨max C 0 * ‖p‖, norm_mulOp_le hC p⟩)
      map_add' := fun p p' => by
        ext i
        simp
      map_smul' := fun c p => by
        ext i
        simp }
    (by
      obtain ⟨C, hC⟩ := hL
      exact ⟨max C 0, fun p => norm_le_of_forall (by positivity) (norm_mulOp_le hC p)⟩)

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: values of a multiplication operator. -/
@[simp] theorem mulOp_apply (L : I → (G →L[ℝ] ℝ)) (hL : ∃ C, ∀ i, ‖L i‖ ≤ C) (p : BFun I G)
    (i : I) : mulOp L hL p i = L i (p i) := rfl

variable [FiniteDimensional ℝ G]

/-- Woodford (2003), App. A.3, eq. (A.11), p. 633: the Nemytskii (superposition) operator
`p ↦ (F(p_i))_i` of a continuous `F` on a finite-dimensional space. -/
noncomputable def nem (F : G → ℝ) (hF : Continuous F) (p : BFun I G) : BFun I ℝ :=
  mkB (fun i => F (p i)) (by
    obtain ⟨C, hC⟩ := exists_bound_ball3 hF ‖p‖
    exact ⟨C, fun i => hC _ (norm_apply_le p i)⟩)

/-- Woodford (2003), App. A.3, p. 634: values of the Nemytskii operator. -/
@[simp] theorem nem_apply (F : G → ℝ) (hF : Continuous F) (p : BFun I G) (i : I) :
    nem F hF p i = F (p i) := rfl

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the candidate derivative of the Nemytskii
operator at `p`, `dp ↦ (DF(p_i) dp_i)_i`. -/
noncomputable def nemD (F : G → ℝ) (hF : ContDiff ℝ 1 F) (p : BFun I G) :
    BFun I G →L[ℝ] BFun I ℝ :=
  mulOp (fun i => fderiv ℝ F (p i)) (by
    obtain ⟨C, hC⟩ := exists_bound_ball3 (hF.continuous_fderiv one_ne_zero) ‖p‖
    exact ⟨C, fun i => hC _ (norm_apply_le p i)⟩)

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: values of `nemD`. -/
@[simp] theorem nemD_apply (F : G → ℝ) (hF : ContDiff ℝ 1 F) (p dp : BFun I G) (i : I) :
    nemD F hF p dp i = fderiv ℝ F (p i) (dp i) := rfl

/-- Woodford (2003), App. A.3, p. 634: **the Nemytskii operator of a `C¹` function on a
finite-dimensional space is strictly Fréchet differentiable on bounded functions, at every
point**, with derivative `nemD` (uniform continuity of `DF` on compact balls). -/
theorem hasStrictFDerivAt_nem {F : G → ℝ} (hF : ContDiff ℝ 1 F) (p : BFun I G) :
    HasStrictFDerivAt (nem F hF.continuous) (nemD F hF p) p := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close3 hF ‖p‖ hc
  have hball : Metric.ball (p, p) (δ / 2) ∈ 𝓝 (p, p) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with q hq
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hq
  refine norm_le_of_forall (by positivity) (fun i => ?_)
  have hmem : ∀ y : BFun I G, ‖y - p‖ < δ / 2 → y i ∈ Metric.ball (p i) (δ / 2) :=
    fun y hy => by
      rw [Metric.mem_ball, dist_eq_norm]
      have h := norm_apply_le (y - p) i
      rw [lp.coeFn_sub, Pi.sub_apply] at h
      exact h.trans_lt hy
  have key := (convex_ball (p i) (δ / 2)).norm_image_sub_le_of_norm_fderiv_le' (f := F)
    (φ := fderiv ℝ F (p i)) (C := c) (fun w _ => (hF.differentiable one_ne_zero) w)
    (fun w hw => by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact (hclose (p i) w (norm_apply_le p i) (by linarith)).le)
    (hmem q.2 hq.2) (hmem q.1 hq.1)
  have hsub : ‖q.1 i - q.2 i‖ ≤ ‖q.1 - q.2‖ := by
    have h := norm_apply_le (q.1 - q.2) i
    rwa [lp.coeFn_sub, Pi.sub_apply] at h
  simp only [lp.coeFn_sub, Pi.sub_apply, nem_apply, nemD_apply]
  exact key.trans (mul_le_mul_of_nonneg_left hsub hc.le)

/-- Woodford (2003), App. A.3, p. 634: the derivative `p ↦ nemD F p` is continuous in operator
norm. -/
theorem continuous_nemD {F : G → ℝ} (hF : ContDiff ℝ 1 F) :
    Continuous (nemD (I := I) F hF) := by
  rw [Metric.continuous_iff]
  intro p ε hε
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close3 hF ‖p‖ (half_pos hε)
  refine ⟨δ, hδ, fun p' hp' => ?_⟩
  rw [dist_eq_norm] at hp' ⊢
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    (fun dp => ?_)) (half_lt_self hε)
  refine norm_le_of_forall (by positivity) (fun i => ?_)
  have hpi : ‖p' i - p i‖ < δ := by
    have h := norm_apply_le (p' - p) i
    rw [lp.coeFn_sub, Pi.sub_apply] at h
    exact h.trans_lt hp'
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, nemD_apply]
  rw [← sub_apply]
  exact ((fderiv ℝ F (p' i) - fderiv ℝ F (p i)).le_opNorm _).trans
    (mul_le_mul (hclose _ _ (norm_apply_le p i) hpi).le (norm_apply_le dp i) (norm_nonneg _)
      (half_pos hε).le)

/-- Woodford (2003), App. A.3, p. 634: the Nemytskii operator of a `C¹` function is `C¹`. -/
theorem contDiff_nem {F : G → ℝ} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (nem (I := I) F hF.continuous) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨nemD F hF, continuous_nemD hF, fun p => (hasStrictFDerivAt_nem hF p).hasFDerivAt⟩

/-! ### Processes, conditional expectations and the lead operator -/

variable {Ω : Type*}

/-- Woodford (2003), App. A.3, p. 634: the Banach space of uniformly bounded real processes
`{p_t(s_t)}` (sup over dates and states), the book's sequences of bounded measurable functions
with the `L∞` norm. Adaptedness is **not** built in; it is a property (`SolvesS`). -/
abbrev Proc (Ω : Type*) : Type _ := BFun (ℕ × Ω) ℝ

/-- Woodford (2003), App. A.3, p. 634: uniformly bounded processes of disturbance vectors
`u_t(s_t) ∈ E`. -/
abbrev SProc (Ω E : Type*) [NormedAddCommGroup E] : Type _ := BFun (ℕ × Ω) E

/-- Woodford (2003), App. A.3, p. 633: the date-`t` random variable `ω ↦ x_t(ω)` of a process. -/
def slice (x : Proc Ω) (t : ℕ) : Ω → ℝ := fun ω => x (t, ω)

/-- Woodford (2003), App. A.3, p. 634: each value of a process is bounded by its norm. -/
theorem abs_slice_le (x : Proc Ω) (t : ℕ) (ω : Ω) : |slice x t ω| ≤ ‖x‖ := by
  have h := norm_apply_le x (t, ω)
  rwa [Real.norm_eq_abs] at h

/-- Woodford (2003), App. A.3, p. 634: slices are additive. -/
@[simp] theorem slice_add (x y : Proc Ω) (t : ℕ) : slice (x + y) t = slice x t + slice y t :=
  rfl

/-- Woodford (2003), App. A.3, p. 634: slices are homogeneous. -/
@[simp] theorem slice_smul (c : ℝ) (x : Proc Ω) (t : ℕ) : slice (c • x) t = c • slice x t :=
  rfl

/-- Woodford (2003), App. A.3, p. 634: slices commute with subtraction. -/
@[simp] theorem slice_sub (x y : Proc Ω) (t : ℕ) : slice (x - y) t = slice x t - slice y t :=
  rfl

/-- Woodford (2003), App. A.3, p. 634: the zero process has zero slices. -/
@[simp] theorem slice_zero (t : ℕ) : slice (0 : Proc Ω) t = 0 := rfl

namespace Ops

variable (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), App. A.3, p. 634: the conditional-expectation operator
`(x_t)_t ↦ (E_t x_t)_t` on bounded processes, as a linear map. -/
noncomputable def condELM : Proc Ω →ₗ[ℝ] Proc Ω where
  toFun x := mkB (fun q => 𝔼.E q.1 (slice x q.1) q.2)
    ⟨‖x‖, fun q => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (abs_slice_le x q.1) q.1 q.2⟩
  map_add' x y := by
    ext q
    simp only [mkB_apply, slice_add, map_add, Pi.add_apply, lp.coeFn_add]
  map_smul' c x := by
    ext q
    simp only [mkB_apply, slice_smul, map_smul, Pi.smul_apply, lp.coeFn_smul, smul_eq_mul,
      RingHom.id_apply]

/-- Woodford (2003), App. A.3, p. 634: the conditional-expectation operator
`(x_t)_t ↦ (E_t x_t)_t`, a bounded linear operator of norm at most one (monotonicity and
constants: `ExpectationSystem.abs_E_le`). -/
noncomputable def condE : Proc Ω →L[ℝ] Proc Ω :=
  (condELM 𝔼).mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_le_of_forall (norm_nonneg x) (fun q => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (abs_slice_le x q.1) q.1 q.2))

/-- Woodford (2003), App. A.3, p. 634: values of the conditional-expectation operator. -/
@[simp] theorem condE_apply (x : Proc Ω) (t : ℕ) (ω : Ω) :
    condE 𝔼 x (t, ω) = 𝔼.E t (slice x t) ω := rfl

/-- Woodford (2003), App. A.3, p. 634: slices of `condE x` are the conditional expectations. -/
@[simp] theorem slice_condE (x : Proc Ω) (t : ℕ) : slice (condE 𝔼 x) t = 𝔼.E t (slice x t) :=
  rfl

/-- Woodford (2003), App. A.3, p. 634: `‖E_t‖ ≤ 1`. -/
theorem norm_condE_le : ‖condE 𝔼‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the expectational lead
`(x_t)_t ↦ (E_t x_{t+1})_t`, as a linear map. -/
noncomputable def leadLM : Proc Ω →ₗ[ℝ] Proc Ω where
  toFun x := mkB (fun q => 𝔼.E q.1 (slice x (q.1 + 1)) q.2)
    ⟨‖x‖, fun q => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (abs_slice_le x (q.1 + 1)) q.1 q.2⟩
  map_add' x y := by
    ext q
    simp only [mkB_apply, slice_add, map_add, Pi.add_apply, lp.coeFn_add]
  map_smul' c x := by
    ext q
    simp only [mkB_apply, slice_smul, map_smul, Pi.smul_apply, lp.coeFn_smul, smul_eq_mul,
      RingHom.id_apply]

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the expectational lead operator
`L x = (E_t x_{t+1})_t`, of norm at most one — the stochastic counterpart of the lead `S`. -/
noncomputable def lead : Proc Ω →L[ℝ] Proc Ω :=
  (leadLM 𝔼).mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_le_of_forall (norm_nonneg x) (fun q => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (abs_slice_le x (q.1 + 1)) q.1 q.2))

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: values of the lead operator. -/
@[simp] theorem lead_apply (x : Proc Ω) (t : ℕ) (ω : Ω) :
    lead 𝔼 x (t, ω) = 𝔼.E t (slice x (t + 1)) ω := rfl

/-- Woodford (2003), App. A.3, p. 634: slices of `L x` are `E_t x_{t+1}`. -/
@[simp] theorem slice_lead (x : Proc Ω) (t : ℕ) :
    slice (lead 𝔼 x) t = 𝔼.E t (slice x (t + 1)) := rfl

/-- Woodford (2003), App. A.3, p. 634: `‖L‖ ≤ 1`. -/
theorem norm_lead_le : ‖lead 𝔼‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Woodford (2003), App. A.3, p. 634: `E_t E_t = E_t` on processes. -/
theorem condE_condE (x : Proc Ω) : condE 𝔼 (condE 𝔼 x) = condE 𝔼 x := by
  ext ⟨t, ω⟩
  simp only [condE_apply, slice_condE, 𝔼.E_E_self]

/-- Woodford (2003), App. A.3, p. 634: `E_t (E_t x_{t+1}) = E_t x_{t+1}`. -/
theorem condE_lead (x : Proc Ω) : condE 𝔼 (lead 𝔼 x) = lead 𝔼 x := by
  ext ⟨t, ω⟩
  simp only [condE_apply, slice_lead, 𝔼.E_E_self, lead_apply]

/-- Woodford (2003), App. A.3, p. 634 (law of iterated expectations):
`E_t (E_{t+1} x_{t+1}) = E_t x_{t+1}`. -/
theorem lead_condE (x : Proc Ω) : lead 𝔼 (condE 𝔼 x) = lead 𝔼 x := by
  ext ⟨t, ω⟩
  simp only [lead_apply, slice_condE, 𝔼.tower (Nat.le_succ t)]

/-- Woodford (2003), App. A.3, p. 634: a deterministic bounded sequence as a process. -/
noncomputable def detP (f : ℕ → ℝ) (hf : ∃ C, ∀ t, |f t| ≤ C) : Proc Ω :=
  mkB (fun q => f q.1) (by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun q => by rw [Real.norm_eq_abs]; exact hC q.1⟩)

/-- Woodford (2003), App. A.3, p. 634: values of a deterministic process. -/
@[simp] theorem detP_apply (f : ℕ → ℝ) (hf : ∃ C, ∀ t, |f t| ≤ C) (t : ℕ) (ω : Ω) :
    detP f hf (t, ω) = f t := rfl

/-- Woodford (2003), App. A.3, p. 634: on deterministic processes the lead is the shift. -/
theorem lead_detP (f : ℕ → ℝ) (hf : ∃ C, ∀ t, |f t| ≤ C) (t : ℕ) (ω : Ω) :
    lead 𝔼 (detP f hf) (t, ω) = f (t + 1) := by
  rw [lead_apply]
  exact congrFun (𝔼.const t (f (t + 1))) ω

/-! ### The linearised operator `a + b L` (A.12)-(A.13) -/

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634, scalar forward-looking case: the linearised
operator `x ↦ (a x_t + b E_t x_{t+1})_t` on bounded processes. -/
noncomputable def TOpS (a b : ℝ) : Proc Ω →L[ℝ] Proc Ω := a • (1 : Proc Ω →L[ℝ] Proc Ω) + b • lead 𝔼

/-- Woodford (2003), eq. (A.12), p. 634: values of `a + b L`. -/
@[simp] theorem TOpS_apply (a b : ℝ) (x : Proc Ω) (t : ℕ) (ω : Ω) :
    TOpS 𝔼 a b x (t, ω) = a * x (t, ω) + b * 𝔼.E t (slice x (t + 1)) ω := rfl

/-- Woodford (2003), App. A.3, p. 634: for `|ρ| < 1` the operator `ρ L` has norm below one. -/
theorem norm_smul_lead_lt {ρ : ℝ} (hρ : |ρ| < 1) : ‖ρ • lead 𝔼‖ < 1 := by
  refine (norm_smul_le ρ (lead 𝔼)).trans_lt ?_
  rw [Real.norm_eq_abs]
  calc |ρ| * ‖lead 𝔼‖ ≤ |ρ| * 1 := mul_le_mul_of_nonneg_left (norm_lead_le 𝔼) (abs_nonneg ρ)
    _ < 1 := by linarith

/-- Woodford (2003), App. A.3, p. 634: for `|b| < |a|` the operator `a + b L` is invertible
(Neumann series of `−(b/a) L`, `‖L‖ ≤ 1`). -/
theorem isUnit_TOpS {a b : ℝ} (h : |b| < |a|) : IsUnit (TOpS 𝔼 a b) := by
  have ha := ne_zero_of_abs_lt h
  set u := Units.oneSub ((-b / a) • lead 𝔼) (norm_smul_lead_lt 𝔼 (abs_ratio_lt h))
  have hval : (↑u : Proc Ω →L[ℝ] Proc Ω) = 1 - (-b / a) • lead 𝔼 := Units.val_oneSub _ _
  have heq : TOpS 𝔼 a b = a • (1 - (-b / a) • lead 𝔼) := by
    ext x ⟨t, ω⟩
    simp only [TOpS_apply, FunLike.coe_smul, FunLike.coe_sub, Pi.smul_apply, Pi.sub_apply,
      one_apply_eq_self, lp.coeFn_smul, lp.coeFn_sub, smul_eq_mul, lead_apply]
    field_simp
    ring
  have hr : ∀ y, (1 - (-b / a) • lead 𝔼) ((↑u⁻¹ : Proc Ω →L[ℝ] Proc Ω) y) = y := fun y => by
    rw [← hval]
    exact congrArg (fun T : Proc Ω →L[ℝ] Proc Ω => T y) u.mul_inv
  have hl : ∀ y, (↑u⁻¹ : Proc Ω →L[ℝ] Proc Ω) ((1 - (-b / a) • lead 𝔼) y) = y := fun y => by
    rw [← hval]
    exact congrArg (fun T : Proc Ω →L[ℝ] Proc Ω => T y) u.inv_mul
  rw [heq]
  refine ⟨⟨a • (1 - (-b / a) • lead 𝔼), a⁻¹ • (↑u⁻¹ : Proc Ω →L[ℝ] Proc Ω), ?_, ?_⟩, rfl⟩
  · ext y : 1
    change (a • (1 - (-b / a) • lead 𝔼)) ((a⁻¹ • (↑u⁻¹ : Proc Ω →L[ℝ] Proc Ω)) y) = y
    rw [smul_apply, smul_apply, map_smul, hr, smul_smul, mul_inv_cancel₀ ha, one_smul]
  · ext y : 1
    change (a⁻¹ • (↑u⁻¹ : Proc Ω →L[ℝ] Proc Ω)) ((a • (1 - (-b / a) • lead 𝔼)) y) = y
    rw [smul_apply, smul_apply, map_smul, hl, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Woodford (2003), App. A.3, pp. 634–635: **the linearised stochastic operator `a + b L` is
invertible on bounded processes if and only if `|b| < |a|`** — the same root condition as in the
perfect-foresight case (`LocalIFT.isUnit_TOp_iff`), with no "generically". -/
theorem isUnit_TOpS_iff [Nonempty Ω] (a b : ℝ) : IsUnit (TOpS 𝔼 a b) ↔ |b| < |a| := by
  refine ⟨fun h => ?_, isUnit_TOpS 𝔼⟩
  by_contra hc
  push Not at hc
  obtain ⟨u, hu⟩ := h
  have hinj : ∀ x, TOpS 𝔼 a b x = 0 → x = 0 := fun x hx => by
    have h1 : (↑u⁻¹ : Proc Ω →L[ℝ] Proc Ω) (TOpS 𝔼 a b x) = x := by
      rw [← hu]
      exact congrArg (fun T : Proc Ω →L[ℝ] Proc Ω => T x) u.inv_mul
    rw [hx, map_zero] at h1
    exact h1.symm
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  rcases eq_or_ne b 0 with hb | hb
  · have ha : a = 0 := by
      rw [hb, abs_zero] at hc
      exact abs_nonpos_iff.mp hc
    have h1 := hinj (detP (fun _ => 1) ⟨1, fun _ => by simp⟩) (by
      ext ⟨t, ω⟩
      simp [ha, hb])
    have := congrArg (fun y : Proc Ω => y (0, ω₀)) h1
    simp at this
  · set r := -a / b with hr
    have hr1 : |r| ≤ 1 := by
      rw [hr, abs_div, abs_neg, div_le_one (abs_pos.mpr hb)]
      exact hc
    have hbd : ∃ C, ∀ t, |r ^ t| ≤ C :=
      ⟨1, fun t => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg r) hr1⟩
    have h1 := hinj (detP (fun t => r ^ t) hbd) (by
      ext ⟨t, ω⟩
      rw [TOpS_apply]
      have hl := lead_detP 𝔼 (fun t => r ^ t) hbd t ω
      rw [lead_apply] at hl
      rw [hl, detP_apply, lp.coeFn_zero, Pi.zero_apply, hr, pow_succ]
      field_simp
      ring)
    have := congrArg (fun y : Proc Ω => y (0, ω₀)) h1
    simp at this

/-- Woodford (2003), App. A.3, p. 634: the inverse of `a + b L` (the unique bounded solution map of
the linearised conditions (A.13)). -/
noncomputable def TInvS (a b : ℝ) : Proc Ω →L[ℝ] Proc Ω := Ring.inverse (TOpS 𝔼 a b)

/-- Woodford (2003), App. A.3, p. 634: `TInvS` is a right inverse of `a + b L` (`|b| < |a|`). -/
theorem TOpS_TInvS {a b : ℝ} (h : |b| < |a|) (y : Proc Ω) : TOpS 𝔼 a b (TInvS 𝔼 a b y) = y := by
  have h' := Ring.mul_inverse_cancel _ (isUnit_TOpS 𝔼 h)
  unfold TInvS
  simpa using congrArg (fun T : Proc Ω →L[ℝ] Proc Ω => T y) h'

/-- Woodford (2003), App. A.3, p. 634: `TInvS` is a left inverse of `a + b L` (`|b| < |a|`). -/
theorem TInvS_TOpS {a b : ℝ} (h : |b| < |a|) (x : Proc Ω) : TInvS 𝔼 a b (TOpS 𝔼 a b x) = x := by
  have h' := Ring.inverse_mul_cancel _ (isUnit_TOpS 𝔼 h)
  unfold TInvS
  simpa using congrArg (fun T : Proc Ω →L[ℝ] Proc Ω => T x) h'

/-- Woodford (2003), App. A.3, p. 634: `a + b L` applied, as an operator identity. -/
theorem TOpS_eq (a b : ℝ) (x : Proc Ω) : TOpS 𝔼 a b x = a • x + b • lead 𝔼 x := rfl

/-- Woodford (2003), App. A.3, p. 634: **the bounded solution of the linearised conditions is
adapted when the forcing is**: if `E_t y_t = y_t` then `E_t x_t = x_t` for `x = (a + b L)⁻¹ y`. -/
theorem condE_TInvS {a b : ℝ} (h : |b| < |a|) {y : Proc Ω} (hy : condE 𝔼 y = y) :
    condE 𝔼 (TInvS 𝔼 a b y) = TInvS 𝔼 a b y := by
  have ha := ne_zero_of_abs_lt h
  set x := TInvS 𝔼 a b y with hx
  have h1 : a • x + b • lead 𝔼 x = y := TOpS_TInvS 𝔼 h y
  have h2 : a • condE 𝔼 x + b • lead 𝔼 x = y := by
    have := congrArg (condE 𝔼) h1
    rwa [map_add, map_smul, map_smul, condE_lead, hy] at this
  have h3 : a • (x - condE 𝔼 x) = 0 := by
    rw [smul_sub]
    have := h1.trans h2.symm
    rw [add_left_inj] at this
    rw [this, sub_self]
  rw [smul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact absurd h3 ha
  · exact (sub_eq_zero.mp h3).symm

/-- Woodford (2003), (A.16), p. 636, stochastic form: the forward sum
`∑_k ρᵏ E_t y_{t+k}` is summable for `|ρ| < 1`. -/
theorem summable_fwdS {ρ : ℝ} (hρ : |ρ| < 1) (y : Proc Ω) (t : ℕ) (ω : Ω) :
    Summable (fun k => ρ ^ k * 𝔼.E t (slice y (t + k)) ω) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right ‖y‖) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (abs_slice_le y (t + k)) t ω)
    (pow_nonneg (abs_nonneg ρ) k)

/-- Woodford (2003), (A.16), p. 636, stochastic form: the forward sum is bounded by
`‖y‖ / (1 − |ρ|)`. -/
theorem abs_fwdS_le {ρ : ℝ} (hρ : |ρ| < 1) (y : Proc Ω) (t : ℕ) (ω : Ω) :
    |∑' k, ρ ^ k * 𝔼.E t (slice y (t + k)) ω| ≤ ‖y‖ / (1 - |ρ|) := by
  have hs := summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  calc |∑' k, ρ ^ k * 𝔼.E t (slice y (t + k)) ω| ≤ ∑' k, ‖y‖ * |ρ| ^ k := by
        rw [← Real.norm_eq_abs]
        refine tsum_of_norm_bounded (hs.mul_left ‖y‖).hasSum (fun k => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (𝔼.abs_E_le (abs_slice_le y (t + k)) t ω)
          (pow_nonneg (abs_nonneg ρ) k)
    _ = ‖y‖ / (1 - |ρ|) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg ρ) hρ, div_eq_mul_inv]

/-- Woodford (2003), (A.16), p. 636, stochastic form: the forward solution
`x_t = ∑_{k ≥ 0} ρᵏ E_t y_{t+k}` as a bounded process. -/
noncomputable def fwdS {ρ : ℝ} (hρ : |ρ| < 1) (y : Proc Ω) : Proc Ω :=
  mkB (fun q => ∑' k, ρ ^ k * 𝔼.E q.1 (slice y (q.1 + k)) q.2)
    ⟨_, fun q => by rw [Real.norm_eq_abs]; exact abs_fwdS_le 𝔼 hρ y q.1 q.2⟩

/-- Woodford (2003), (A.15)–(A.16), p. 636: `E_t` of next period's forward sum,
`E_t x_{t+1} = ∑_k ρᵏ E_t y_{t+1+k}` (`E_t` commutes with the dominated series, tower
property). -/
theorem E_fwdS_succ {ρ : ℝ} (hρ : |ρ| < 1) (y : Proc Ω) (t : ℕ) (ω : Ω) :
    𝔼.E t (slice (fwdS 𝔼 hρ y) (t + 1)) ω = ∑' k, ρ ^ k * 𝔼.E t (slice y (t + 1 + k)) ω := by
  have hb : ∀ k ω', |ρ ^ k * 𝔼.E (t + 1) (slice y (t + 1 + k)) ω'| ≤ |ρ| ^ k * ‖y‖ :=
    fun k ω' => by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (abs_slice_le y (t + 1 + k)) (t + 1) ω')
        (pow_nonneg (abs_nonneg ρ) k)
  change 𝔼.E t (fun ω' => ∑' k, ρ ^ k * 𝔼.E (t + 1) (slice y (t + 1 + k)) ω') ω = _
  rw [𝔼.E_tsum (abs_nonneg ρ) hρ hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (ρ ^ k • 𝔼.E (t + 1) (slice y (t + 1 + k))) ω = _
  rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), (A.14)–(A.16), p. 636, stochastic form: for adapted forcing (`E_t y_t = y_t`)
the forward sum solves `x_t − ρ E_t x_{t+1} = y_t`. -/
theorem fwdS_solves {ρ : ℝ} (hρ : |ρ| < 1) {y : Proc Ω} (hy : condE 𝔼 y = y) (t : ℕ) (ω : Ω) :
    fwdS 𝔼 hρ y (t, ω) - ρ * 𝔼.E t (slice (fwdS 𝔼 hρ y) (t + 1)) ω = y (t, ω) := by
  rw [E_fwdS_succ]
  change ∑' k, ρ ^ k * 𝔼.E t (slice y (t + k)) ω - _ = _
  rw [(summable_fwdS 𝔼 hρ y t ω).tsum_eq_zero_add, pow_zero, one_mul, add_zero]
  have hyt : 𝔼.E t (slice y t) ω = y (t, ω) := by
    have := congrArg (fun z : Proc Ω => z (t, ω)) hy
    simpa using this
  rw [hyt, ← tsum_mul_left]
  have : ∀ k, ρ ^ (k + 1) * 𝔼.E t (slice y (t + (k + 1))) ω =
      ρ * (ρ ^ k * 𝔼.E t (slice y (t + 1 + k)) ω) := fun k => by
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  simp only [this]
  ring

/-- Woodford (2003), (1.37), p. 81 and (A.16), p. 636, stochastic form: for adapted forcing the
inverse of `a + b L` is the forward sum `y ↦ a⁻¹ ∑_k (−b/a)ᵏ E_t y_{t+k}`. -/
theorem TInvS_apply_adapted {a b : ℝ} (h : |b| < |a|) {y : Proc Ω} (hy : condE 𝔼 y = y)
    (t : ℕ) (ω : Ω) :
    TInvS 𝔼 a b y (t, ω) = a⁻¹ * ∑' k, (-b / a) ^ k * 𝔼.E t (slice y (t + k)) ω := by
  have ha := ne_zero_of_abs_lt h
  have hρ := abs_ratio_lt h
  have hsol : TOpS 𝔼 a b (a⁻¹ • fwdS 𝔼 hρ y) = y := by
    ext ⟨s, ω'⟩
    rw [TOpS_apply, slice_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    have hf := fwdS_solves 𝔼 hρ hy s ω'
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [← hf]
    field_simp
    ring
  have h2 := TInvS_TOpS 𝔼 h (a⁻¹ • fwdS 𝔼 hρ y)
  rw [hsol] at h2
  rw [h2]
  rfl

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the pointwise disturbance operator
`e ↦ (c(e_t))_t` for `c : E →L[ℝ] ℝ`. -/
noncomputable def ptc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E →L[ℝ] ℝ) :
    SProc Ω E →L[ℝ] Proc Ω :=
  mulOp (fun _ => c) ⟨‖c‖, fun _ => le_rfl⟩

/-- Woodford (2003), App. A.3, eq. (A.12)–(A.13), p. 634: the disturbance term of the linearised
conditions, `e ↦ (E_t c(e_t))_t` (disturbances need not be adapted: date-`t` conditions may
involve date-`t+1` shocks inside `E_t`). -/
noncomputable def cOpS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E →L[ℝ] ℝ) :
    SProc Ω E →L[ℝ] Proc Ω :=
  (condE 𝔼).comp (ptc c)

/-- Woodford (2003), (A.13), p. 634: the linear rational-expectations solution operator
`e ↦ −(a + b L)⁻¹ (E_t c(e_t))_t`. -/
noncomputable def linSolS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ)
    (c : E →L[ℝ] ℝ) : SProc Ω E →L[ℝ] Proc Ω :=
  -((TInvS 𝔼 a b).comp (cOpS 𝔼 c))

/-- Woodford (2003), (A.13), p. 634: the linear RE solution solves
`a x̂_t + b E_t x̂_{t+1} + E_t c(e_t) = 0`. -/
theorem linSolS_solves {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    (h : |b| < |a|) (c : E →L[ℝ] ℝ) (e : SProc Ω E) :
    TOpS 𝔼 a b (linSolS 𝔼 a b c e) + cOpS 𝔼 c e = 0 := by
  change TOpS 𝔼 a b (-(TInvS 𝔼 a b (cOpS 𝔼 c e))) + cOpS 𝔼 c e = 0
  rw [map_neg, TOpS_TInvS 𝔼 h, neg_add_cancel]

/-- Woodford (2003), (A.13), p. 634: the disturbance term `E_t c(e_t)` is adapted. -/
theorem condE_cOpS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E →L[ℝ] ℝ)
    (e : SProc Ω E) : condE 𝔼 (cOpS 𝔼 c e) = cOpS 𝔼 c e :=
  condE_condE 𝔼 (ptc c e)

/-- Woodford (2003), (A.13), p. 634: the linear RE solution is adapted. -/
theorem condE_linSolS {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    (h : |b| < |a|) (c : E →L[ℝ] ℝ) (e : SProc Ω E) :
    condE 𝔼 (linSolS 𝔼 a b c e) = linSolS 𝔼 a b c e := by
  change condE 𝔼 (-(TInvS 𝔼 a b (cOpS 𝔼 c e))) = -(TInvS 𝔼 a b (cOpS 𝔼 c e))
  rw [map_neg, condE_TInvS 𝔼 h (condE_cOpS 𝔼 c e)]

/-- Woodford (2003), eq. (1.37), p. 81, (A.13) p. 634 and (A.16) p. 636: **the linear RE
solution is the forward series of the core**:
`x̂_t = −a⁻¹ ∑_{k ≥ 0} (−b/a)ᵏ E_t c(e_{t+k})`, i.e. `−a⁻¹ · forwardSeries (−b/a) (c ∘ e)`. -/
theorem linSolS_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    (h : |b| < |a|) (c : E →L[ℝ] ℝ) (e : SProc Ω E) (t : ℕ) (ω : Ω) :
    linSolS 𝔼 a b c e (t, ω) =
      -(a⁻¹ * 𝔼.forwardSeries (-b / a) (fun s ω' => c (e (s, ω'))) t ω) := by
  change -(TInvS 𝔼 a b (cOpS 𝔼 c e) (t, ω)) = _
  rw [TInvS_apply_adapted 𝔼 h (condE_cOpS 𝔼 c e)]
  congr 2
  refine tsum_congr fun k => ?_
  change _ * 𝔼.E t (𝔼.E (t + k) (slice (ptc c e) (t + k))) ω = _
  rw [𝔼.tower (Nat.le_add_right t k)]
  rfl

/-! ### The general stochastic class `E_t[G(x_t, x_{t+1}, E_t x_{t+1}, e_t)] = 0`

Woodford's (A.11) is `E_t[f(p_{t−1}, p_t, p_{t+1}; u_t)] = 0`. We treat the scalar
forward-looking case (no predetermined variable) in a form that contains both

* (A.11) itself, `E_t[F(x_t, x_{t+1}, e_t)] = 0` (`G` ignoring its third argument), and
* `F(x_t, E_t x_{t+1}, e_t) = 0` (`G` ignoring its second argument; see `solvesS_liftI_iff`),

with a disturbance process `e_t ∈ E` that need **not** be adapted (date-`t` conditions such as
the Euler equation contain date-`t+1` shocks inside `E_t`). The unknown `x` is a bounded
process; the equilibrium conditions require it to be adapted. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Woodford (2003), App. A.3, p. 634: the date-`t` argument `(x_t, x_{t+1}, E_t x_{t+1}, e_t)` as
a function of the state. -/
noncomputable def argFun (q : SProc Ω E × Proc Ω) (i : ℕ × Ω) : ℝ × ℝ × ℝ × E :=
  (q.2 i, q.2 (i.1 + 1, i.2), lead 𝔼 q.2 i, q.1 i)

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: each date-`t` argument is bounded by the norm. -/
theorem norm_argFun_le (q : SProc Ω E × Proc Ω) (i : ℕ × Ω) : ‖argFun 𝔼 q i‖ ≤ ‖q‖ := by
  have h1 : ‖q.2 i‖ ≤ ‖q‖ := (norm_apply_le q.2 i).trans (norm_snd_le q)
  have h2 : ‖q.2 (i.1 + 1, i.2)‖ ≤ ‖q‖ := (norm_apply_le q.2 _).trans (norm_snd_le q)
  have h3 : ‖lead 𝔼 q.2 i‖ ≤ ‖q‖ := (norm_apply_le _ i).trans
    (((lead 𝔼).le_of_opNorm_le (norm_lead_le 𝔼) q.2).trans
      (by rw [one_mul]; exact norm_snd_le q))
  have h4 : ‖q.1 i‖ ≤ ‖q‖ := (norm_apply_le q.1 i).trans (norm_fst_le q)
  rw [argFun, norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
  exact ⟨h1, h2, h3, h4⟩

/-- Woodford (2003), App. A.3, p. 634: the argument map as a linear map. -/
noncomputable def argLM : SProc Ω E × Proc Ω →ₗ[ℝ] BFun (ℕ × Ω) (ℝ × ℝ × ℝ × E) where
  toFun q := mkB (argFun 𝔼 q) ⟨‖q‖, norm_argFun_le 𝔼 q⟩
  map_add' q q' := by
    refine lp.ext (funext fun i => ?_)
    simp only [mkB_apply, argFun, Prod.fst_add, Prod.snd_add, lp.coeFn_add, Pi.add_apply,
      map_add, Prod.mk_add_mk]
  map_smul' c q := by
    refine lp.ext (funext fun i => ?_)
    simp only [mkB_apply, argFun, Prod.smul_fst, Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply,
      map_smul, Prod.smul_mk, RingHom.id_apply]

/-- Woodford (2003), App. A.3, p. 634: the argument map `q ↦ (x_t, x_{t+1}, E_t x_{t+1}, e_t)_t`,
a bounded linear operator of norm at most one. -/
noncomputable def argL : SProc Ω E × Proc Ω →L[ℝ] BFun (ℕ × Ω) (ℝ × ℝ × ℝ × E) :=
  (argLM 𝔼).mkContinuous 1 (fun q => by
    rw [one_mul]
    exact norm_le_of_forall (norm_nonneg q) (norm_argFun_le 𝔼 q))

/-- Woodford (2003), App. A.3, p. 634: values of the argument map. -/
theorem argL_apply (q : SProc Ω E × Proc Ω) (i : ℕ × Ω) : argL 𝔼 q i = argFun 𝔼 q i := rfl

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: `∂G/∂(E_t x_{t+1})` at the steady state. -/
noncomputable def slopeD (G : ℝ × ℝ × ℝ × E → ℝ) : ℝ := fderiv ℝ G 0 (0, 0, (1, 0))

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the total coefficient on `E_t x̂_{t+1}` in the
linearised condition, `∂G/∂x_{t+1} + ∂G/∂(E_t x_{t+1})`. -/
noncomputable def sB (G : ℝ × ℝ × ℝ × E → ℝ) : ℝ := slopeB G + slopeD G

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: `∂G/∂e_t` at the steady state. -/
noncomputable def sC (G : ℝ × ℝ × ℝ × E → ℝ) : E →L[ℝ] ℝ :=
  (slopeC G).comp (ContinuousLinearMap.inr ℝ ℝ E)

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the derivative at the steady state in
coordinates, `DG(0)(x, y, z, v) = a x + b y + d z + c v`. -/
theorem fderiv_zero_apply4 [NormedSpace ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ) (x y z : ℝ) (v : E) :
    fderiv ℝ G 0 (x, y, z, v) = slopeA G * x + slopeB G * y + slopeD G * z + sC G v := by
  rw [fderiv_zero_apply3]
  have h : ((z, v) : ℝ × E) = z • ((1 : ℝ), (0 : E)) + ((0 : ℝ), v) := by ext <;> simp
  rw [h, map_add, map_smul, smul_eq_mul]
  simp only [slopeD, sC, slopeC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  ring

/-- Woodford (2003), App. A.3, eq. (A.11), p. 633: `x` is a stochastic equilibrium of
`E_t[G(x_t, x_{t+1}, E_t x_{t+1}, e_t)] = 0` given the disturbances `e`: `x` is adapted
(`E_t x_t = x_t`) and the conditions hold at every date and in every state. -/
def SolvesS (G : ℝ × ℝ × ℝ × E → ℝ) (e : SProc Ω E) (x : Proc Ω) : Prop :=
  (∀ t, 𝔼.E t (slice x t) = slice x t) ∧
    ∀ t, 𝔼.E t (fun ω => G (x (t, ω), x (t + 1, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω))) = 0

/-- Woodford (2003), App. A.3, eq. (A.4)/(A.11), pp. 630, 633–634: the stochastic equilibrium map
`Φ(e, x)_t = E_t[G(x_t, x_{t+1}, E_t x_{t+1}, e_t)] + a (x_t − E_t x_t)` with `a = ∂G/∂x_t(0)`
on all bounded (not necessarily adapted) processes. Its zeros are exactly the adapted solutions
(`eqMapS_eq_zero_iff`); the second term makes its derivative `a + b L` on the whole space. -/
noncomputable def eqMapS [FiniteDimensional ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ) (hG : Continuous G)
    (q : SProc Ω E × Proc Ω) : Proc Ω :=
  condE 𝔼 (nem G hG (argL 𝔼 q)) + slopeA G • (q.2 - condE 𝔼 q.2)

/-- Woodford (2003), App. A.3, p. 634: slices of the Nemytskii term are the date-`t`
conditions as functions of the state. -/
theorem slice_nem_argL [FiniteDimensional ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ) (hG : Continuous G)
    (e : SProc Ω E) (x : Proc Ω) (t : ℕ) :
    slice (nem G hG (argL 𝔼 (e, x))) t =
      fun ω => G (x (t, ω), x (t + 1, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω)) := rfl

/-- Woodford (2003), App. A.3, eq. (A.4), p. 630, stochastic form: **the zeros of `Φ` are exactly
the stochastic equilibria** (adaptedness included), provided `a ≠ 0`. -/
theorem eqMapS_eq_zero_iff [FiniteDimensional ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ) (hG : Continuous G)
    (ha : slopeA G ≠ 0) (e : SProc Ω E) (x : Proc Ω) :
    eqMapS 𝔼 G hG (e, x) = 0 ↔ SolvesS 𝔼 G e x := by
  have hsl : ∀ t, slice (eqMapS 𝔼 G hG (e, x)) t =
      𝔼.E t (fun ω => G (x (t, ω), x (t + 1, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω))) +
        slopeA G • (slice x t - 𝔼.E t (slice x t)) := fun t => rfl
  constructor
  · intro h
    have h0 : ∀ t, slice (eqMapS 𝔼 G hG (e, x)) t = 0 := fun t => by rw [h]; rfl
    have hE : ∀ t, 𝔼.E t
        (fun ω => G (x (t, ω), x (t + 1, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω))) = 0 := by
      intro t
      have h1 := congrArg (𝔼.E t) (h0 t)
      rw [hsl, map_add, map_smul, map_sub, 𝔼.E_E_self, 𝔼.E_E_self, sub_self, smul_zero,
        add_zero, map_zero] at h1
      exact h1
    refine ⟨fun t => ?_, hE⟩
    have h1 := h0 t
    rw [hsl, hE t, zero_add, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 ha
    · exact (sub_eq_zero.mp h1).symm
  · rintro ⟨had, hE⟩
    ext ⟨t, ω⟩
    have h1 := congrFun (hsl t) ω
    change eqMapS 𝔼 G hG (e, x) (t, ω) = _ at h1
    rw [h1, hE t, had t, sub_self, smul_zero, add_zero]
    rfl

/-- Woodford (2003), App. A.3, p. 634: the candidate derivative of `Φ` at `q`. -/
noncomputable def eqDS [FiniteDimensional ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ) (hG : ContDiff ℝ 1 G)
    (q : SProc Ω E × Proc Ω) : SProc Ω E × Proc Ω →L[ℝ] Proc Ω :=
  (condE 𝔼).comp ((nemD G hG (argL 𝔼 q)).comp (argL 𝔼)) +
    slopeA G • (ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω) -
      (condE 𝔼).comp (ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω)))

/-- Woodford (2003), App. A.3, p. 634: **the stochastic equilibrium map of a `C¹` condition is
strictly Fréchet differentiable on bounded processes at every point** (chain rule: bounded linear
argument map, Nemytskii operator, conditional expectation). -/
theorem hasStrictFDerivAt_eqMapS [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (q : SProc Ω E × Proc Ω) :
    HasStrictFDerivAt (eqMapS 𝔼 G hG.continuous) (eqDS 𝔼 G hG q) q := by
  have h1 := (condE 𝔼).hasStrictFDerivAt.comp q
    ((hasStrictFDerivAt_nem hG (argL 𝔼 q)).comp q (argL 𝔼).hasStrictFDerivAt)
  have h2 := ((ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω) -
      (condE 𝔼).comp (ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω))).hasStrictFDerivAt
      (x := q)).const_smul (slopeA G)
  exact h1.add h2

/-- Woodford (2003), App. A.3, p. 634: the stochastic equilibrium map is `C¹`. -/
theorem contDiff_eqMapS [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 (eqMapS 𝔼 G hG.continuous) := by
  have h1 := (condE 𝔼).contDiff.comp ((contDiff_nem hG).comp (argL 𝔼).contDiff)
  have h2 := ((ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω) -
      (condE 𝔼).comp (ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω))).contDiff
      (n := 1)).const_smul (slopeA G)
  exact h1.add h2

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: the derivative of `Φ` at the steady state,
`(de, dx) ↦ (a + b L) dx + (E_t c(de_t))_t` with `b = ∂G/∂x_{t+1} + ∂G/∂(E_t x_{t+1})`. -/
noncomputable def eqD0S (G : ℝ × ℝ × ℝ × E → ℝ) : SProc Ω E × Proc Ω →L[ℝ] Proc Ω :=
  (TOpS 𝔼 (slopeA G) (sB G)).comp (ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω)) +
    (cOpS 𝔼 (sC G)).comp (ContinuousLinearMap.fst ℝ (SProc Ω E) (Proc Ω))

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: at the steady state the derivative of the
stochastic equilibrium map is the linear operator (A.12). -/
theorem eqDS_zero [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ} (hG : ContDiff ℝ 1 G) :
    eqDS 𝔼 G hG 0 = eqD0S 𝔼 G := by
  refine ContinuousLinearMap.ext (fun q => ?_)
  ext ⟨t, ω⟩
  have hfun : slice ((nemD G hG (argL 𝔼 0)) (argL 𝔼 q)) t =
      slopeA G • slice q.2 t + (slopeB G • slice q.2 (t + 1) +
        (slopeD G • 𝔼.E t (slice q.2 (t + 1)) + slice (ptc (sC G) q.1) t)) := by
    funext ω'
    change fderiv ℝ G (argL 𝔼 0 (t, ω')) (argFun 𝔼 q (t, ω')) = _
    rw [map_zero]
    change fderiv ℝ G 0 (q.2 (t, ω'), q.2 (t + 1, ω'), 𝔼.E t (slice q.2 (t + 1)) ω',
      q.1 (t, ω')) = _
    rw [fderiv_zero_apply4]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change _ = _ + (_ + (_ + sC G (q.1 (t, ω'))))
    simp only [slice]
    ring
  have hL : eqDS 𝔼 G hG 0 q (t, ω) =
      𝔼.E t (slice ((nemD G hG (argL 𝔼 0)) (argL 𝔼 q)) t) ω +
        slopeA G * (q.2 (t, ω) - 𝔼.E t (slice q.2 t) ω) := rfl
  have hR : eqD0S 𝔼 G q (t, ω) = slopeA G * q.2 (t, ω) +
      sB G * 𝔼.E t (slice q.2 (t + 1)) ω + 𝔼.E t (slice (ptc (sC G) q.1) t) ω := rfl
  rw [hL, hR, hfun, map_add, map_add, map_add, map_smul, map_smul, map_smul, 𝔼.E_E_self]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sB]
  ring

/-! ### The implicit-function theorem on `L∞` processes -/

/-- Woodford (2003), App. A.3, p. 634: the augmented map `(e, x) ↦ (e, Φ(e, x))`. -/
noncomputable def bigMapS [FiniteDimensional ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ) (hG : Continuous G)
    (q : SProc Ω E × Proc Ω) : SProc Ω E × Proc Ω :=
  (q.1, eqMapS 𝔼 G hG q)

/-- Woodford (2003), App. A.3, p. 634: the augmented map is `C¹`. -/
theorem contDiff_bigMapS [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 (bigMapS 𝔼 G hG.continuous) :=
  contDiff_fst.prodMk (contDiff_eqMapS 𝔼 hG)

/-- Woodford (2003), App. A.3, p. 634: the derivative of the augmented map at the steady state. -/
noncomputable def bigD0S (G : ℝ × ℝ × ℝ × E → ℝ) :
    SProc Ω E × Proc Ω →L[ℝ] SProc Ω E × Proc Ω :=
  (ContinuousLinearMap.fst ℝ (SProc Ω E) (Proc Ω)).prod (eqD0S 𝔼 G)

/-- Woodford (2003), App. A.3, p. 634: the inverse of `bigD0S`,
`(de, dy) ↦ (de, (a + b L)⁻¹(dy − E_t c(de_t)))`. -/
noncomputable def bigDInvS (G : ℝ × ℝ × ℝ × E → ℝ) :
    SProc Ω E × Proc Ω →L[ℝ] SProc Ω E × Proc Ω :=
  (ContinuousLinearMap.fst ℝ (SProc Ω E) (Proc Ω)).prod
    ((TInvS 𝔼 (slopeA G) (sB G)).comp (ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω) -
      (cOpS 𝔼 (sC G)).comp (ContinuousLinearMap.fst ℝ (SProc Ω E) (Proc Ω))))

/-- Woodford (2003), App. A.3, p. 634: `bigDInvS` is a left inverse of `bigD0S`. -/
theorem bigDInvS_bigD0S {G : ℝ × ℝ × ℝ × E → ℝ} (hab : |sB G| < |slopeA G|)
    (q : SProc Ω E × Proc Ω) : bigDInvS 𝔼 G (bigD0S 𝔼 G q) = q := by
  refine Prod.ext rfl ?_
  change TInvS 𝔼 (slopeA G) (sB G) (TOpS 𝔼 (slopeA G) (sB G) q.2 + cOpS 𝔼 (sC G) q.1 -
    cOpS 𝔼 (sC G) q.1) = q.2
  rw [add_sub_cancel_right, TInvS_TOpS 𝔼 hab]

/-- Woodford (2003), App. A.3, p. 634: `bigDInvS` is a right inverse of `bigD0S`. -/
theorem bigD0S_bigDInvS {G : ℝ × ℝ × ℝ × E → ℝ} (hab : |sB G| < |slopeA G|)
    (q : SProc Ω E × Proc Ω) : bigD0S 𝔼 G (bigDInvS 𝔼 G q) = q := by
  refine Prod.ext rfl ?_
  change TOpS 𝔼 (slopeA G) (sB G) (TInvS 𝔼 (slopeA G) (sB G) (q.2 - cOpS 𝔼 (sC G) q.1)) +
    cOpS 𝔼 (sC G) q.1 = q.2
  rw [TOpS_TInvS 𝔼 hab, sub_add_cancel]

/-- Woodford (2003), App. A.3, p. 634: for `|b| < |a|` the derivative of the augmented map is a
continuous linear equivalence. -/
noncomputable def bigDEquivS (G : ℝ × ℝ × ℝ × E → ℝ) (hab : |sB G| < |slopeA G|) :
    (SProc Ω E × Proc Ω) ≃L[ℝ] (SProc Ω E × Proc Ω) :=
  ContinuousLinearEquiv.equivOfInverse (bigD0S 𝔼 G) (bigDInvS 𝔼 G) (bigDInvS_bigD0S 𝔼 hab)
    (bigD0S_bigDInvS 𝔼 hab)

/-- Woodford (2003), App. A.3, p. 634: the derivative of the augmented map at the steady state. -/
theorem hasFDerivAt_bigMapS [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (hab : |sB G| < |slopeA G|) :
    HasFDerivAt (bigMapS 𝔼 G hG.continuous) (bigDEquivS 𝔼 G hab : _ →L[ℝ] _) 0 := by
  have h := (hasStrictFDerivAt_eqMapS 𝔼 hG 0).hasFDerivAt
  rw [eqDS_zero 𝔼 hG] at h
  exact hasFDerivAt_fst.prodMk h

/-- Woodford (2003), App. A.3, pp. 633–634: the local homeomorphism given by the
inverse-function theorem on `L∞` processes (Mathlib's
`HasStrictFDerivAt.toOpenPartialHomeomorph`). -/
noncomputable def homeoS [FiniteDimensional ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ) (hG : ContDiff ℝ 1 G)
    (hab : |sB G| < |slopeA G|) :
    OpenPartialHomeomorph (SProc Ω E × Proc Ω) (SProc Ω E × Proc Ω) :=
  ((contDiff_bigMapS 𝔼 hG).contDiffAt.hasStrictFDerivAt' (hasFDerivAt_bigMapS 𝔼 hG hab)
    one_ne_zero).toOpenPartialHomeomorph (bigMapS 𝔼 G hG.continuous)

/-- Woodford (2003), App. A.3, p. 634: the locally unique stochastic equilibrium `x = X(e)`. -/
noncomputable def implicitSolS [FiniteDimensional ℝ E] (G : ℝ × ℝ × ℝ × E → ℝ)
    (hG : ContDiff ℝ 1 G) (hab : |sB G| < |slopeA G|) (e : SProc Ω E) : Proc Ω :=
  ((homeoS 𝔼 G hG hab).symm (e, 0)).2

/-- Woodford (2003), (A.13), p. 634: the linear RE solution operator of the class,
`e ↦ −(a + b L)⁻¹ (E_t c(e_t))_t`. -/
noncomputable def linSolG (G : ℝ × ℝ × ℝ × E → ℝ) : SProc Ω E →L[ℝ] Proc Ω :=
  linSolS 𝔼 (slopeA G) (sB G) (sC G)

/-- Woodford (2003), App. A.3, p. 634: the local homeomorphism is the augmented map. -/
theorem homeoS_apply [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ} (hG : ContDiff ℝ 1 G)
    (hab : |sB G| < |slopeA G|) (q : SProc Ω E × Proc Ω) :
    homeoS 𝔼 G hG hab q = bigMapS 𝔼 G hG.continuous q := rfl

/-- Woodford (2003), App. A.3, p. 634: the steady state lies in the source. -/
theorem zero_mem_homeoS_source [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (hab : |sB G| < |slopeA G|) :
    (0 : SProc Ω E × Proc Ω) ∈ (homeoS 𝔼 G hG hab).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

/-- Woodford (2003), App. A.3, p. 634: with no disturbances the steady state is an
equilibrium. -/
theorem bigMapS_zero [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ} (hG : Continuous G)
    (h0 : G 0 = 0) : bigMapS 𝔼 G hG 0 = 0 := by
  have h : eqMapS 𝔼 G hG 0 = 0 := by
    ext ⟨t, ω⟩
    have hn : nem G hG (argL 𝔼 0) = 0 := by
      ext i
      simp only [nem_apply, map_zero, lp.coeFn_zero, Pi.zero_apply, h0]
    change condE 𝔼 (nem G hG (argL 𝔼 0)) (t, ω) + _ = _
    rw [hn, map_zero]
    simp
  exact Prod.ext rfl h

/-- Woodford (2003), App. A.3, p. 634: the steady state lies in the target. -/
theorem zero_mem_homeoS_target [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    (0 : SProc Ω E × Proc Ω) ∈ (homeoS 𝔼 G hG hab).target := by
  have h := (homeoS 𝔼 G hG hab).map_source (zero_mem_homeoS_source 𝔼 hG hab)
  rwa [homeoS_apply, bigMapS_zero 𝔼 hG.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 634: the local inverse maps the steady state to itself. -/
theorem homeoS_symm_zero [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    (homeoS 𝔼 G hG hab).symm 0 = 0 := by
  have h := (homeoS 𝔼 G hG hab).left_inv (zero_mem_homeoS_source 𝔼 hG hab)
  rwa [homeoS_apply, bigMapS_zero 𝔼 hG.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 634: the local inverse is `C¹` at the steady state. -/
theorem contDiffAt_homeoS_symm [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    ContDiffAt ℝ 1 (homeoS 𝔼 G hG hab).symm 0 := by
  refine (homeoS 𝔼 G hG hab).contDiffAt_symm (f₀' := bigDEquivS 𝔼 G hab)
    (zero_mem_homeoS_target 𝔼 hG h0 hab) ?_ ?_
  · rw [homeoS_symm_zero 𝔼 hG h0 hab]
    exact hasFDerivAt_bigMapS 𝔼 hG hab
  · rw [homeoS_symm_zero 𝔼 hG h0 hab]
    exact (contDiff_bigMapS 𝔼 hG).contDiffAt

/-- Woodford (2003), App. A.3, (A.5), p. 630: the derivative of the local inverse at the steady
state is the inverse of the derivative. -/
theorem hasFDerivAt_homeoS_symm [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    HasFDerivAt (homeoS 𝔼 G hG hab).symm ((bigDEquivS 𝔼 G hab).symm : _ →L[ℝ] _) 0 := by
  refine (homeoS 𝔼 G hG hab).hasFDerivAt_symm (zero_mem_homeoS_target 𝔼 hG h0 hab) ?_
  rw [homeoS_symm_zero 𝔼 hG h0 hab]
  exact hasFDerivAt_bigMapS 𝔼 hG hab

/-- Woodford (2003), App. A.3, p. 634: with no disturbances the equilibrium is the steady
state. -/
theorem implicitSolS_zero [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    implicitSolS 𝔼 G hG hab 0 = 0 := by
  rw [implicitSolS, Prod.mk_zero_zero, homeoS_symm_zero 𝔼 hG h0 hab]
  rfl

/-- Woodford (2003), App. A.3, p. 634 ("approximated (to first order) by the unique bounded
solution to the linearized equilibrium conditions (A.13)"): **the first-order term of the exact
stochastic equilibrium is the linear RE solution**: `X` is Fréchet differentiable at `0` with
derivative `linSolG`. -/
theorem hasFDerivAt_implicitSolS [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    HasFDerivAt (implicitSolS 𝔼 G hG hab) (linSolG 𝔼 G) 0 := by
  have hin : HasFDerivAt (fun e : SProc Ω E => ((e, (0 : Proc Ω)) : SProc Ω E × Proc Ω))
      (ContinuousLinearMap.inl ℝ (SProc Ω E) (Proc Ω)) 0 :=
    (ContinuousLinearMap.inl ℝ (SProc Ω E) (Proc Ω)).hasFDerivAt
  have hs : HasFDerivAt (homeoS 𝔼 G hG hab).symm ((bigDEquivS 𝔼 G hab).symm : _ →L[ℝ] _)
      ((0 : SProc Ω E), (0 : Proc Ω)) := by
    rw [Prod.mk_zero_zero]
    exact hasFDerivAt_homeoS_symm 𝔼 hG h0 hab
  have h := (ContinuousLinearMap.snd ℝ (SProc Ω E) (Proc Ω)).hasFDerivAt.comp (0 : SProc Ω E)
    (hs.comp (0 : SProc Ω E) hin)
  refine h.congr_fderiv (ContinuousLinearMap.ext (fun e => ?_))
  change TInvS 𝔼 (slopeA G) (sB G) ((0 : Proc Ω) - cOpS 𝔼 (sC G) e) =
    -(TInvS 𝔼 (slopeA G) (sB G) (cOpS 𝔼 (sC G) e))
  rw [zero_sub, map_neg]

/-- Woodford (2003), App. A.3, pp. 633–634: **local existence and uniqueness of the stochastic
equilibrium** for `E_t[G(x_t, x_{t+1}, E_t x_{t+1}, e_t)] = 0` with `G` `C¹`, `G(0) = 0` and
`|b| < |a|`: there are `ε, δ > 0` such that for every disturbance process with `‖e‖∞ < δ`,
`X(e)` is a bounded **adapted** equilibrium with `‖X(e)‖∞ < ε/2`, `X` is `C¹` near `e`, and every
bounded adapted equilibrium with `‖x‖∞ < ε` equals `X(e)`. -/
theorem local_determinacyS [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiff ℝ 1 G) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    ∃ ε > 0, ∃ δ > 0, δ ≤ ε ∧
      (∀ e : SProc Ω E, ‖e‖ < δ →
        ‖implicitSolS 𝔼 G hG hab e‖ < ε / 2 ∧ SolvesS 𝔼 G e (implicitSolS 𝔼 G hG hab e) ∧
          ContDiffAt ℝ 1 (implicitSolS 𝔼 G hG hab) e) ∧
      (∀ e : SProc Ω E, ‖e‖ < δ → ∀ x : Proc Ω, ‖x‖ < ε → SolvesS 𝔼 G e x →
        x = implicitSolS 𝔼 G hG hab e) := by
  have ha : slopeA G ≠ 0 := ne_zero_of_abs_lt hab
  set H := homeoS 𝔼 G hG hab with hH
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (H.open_source.mem_nhds (zero_mem_homeoS_source 𝔼 hG hab))
  have hcd := contDiffAt_homeoS_symm 𝔼 hG h0 hab
  have hsym0 := homeoS_symm_zero 𝔼 hG h0 hab
  have hev1 : ∀ᶠ y in 𝓝 (0 : SProc Ω E × Proc Ω), y ∈ H.target :=
    H.open_target.mem_nhds (zero_mem_homeoS_target 𝔼 hG h0 hab)
  have hev2 : ∀ᶠ y in 𝓝 (0 : SProc Ω E × Proc Ω), ‖H.symm y‖ < ε / 2 := by
    have ht := hcd.continuousAt.tendsto
    rw [hsym0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds 0 (half_pos hε))).mono
      (fun y hy => by simpa using hy)
  have hev3 : ∀ᶠ y in 𝓝 (0 : SProc Ω E × Proc Ω), ContDiffAt ℝ 1 H.symm y :=
    hcd.eventually (by simp)
  have hpull : Filter.Tendsto (fun e : SProc Ω E => ((e, (0 : Proc Ω)) : SProc Ω E × Proc Ω))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun e : SProc Ω E => ((e, (0 : Proc Ω)) : SProc Ω E × Proc Ω)) :=
      continuous_id.prodMk continuous_const
    have h := hc.tendsto (0 : SProc Ω E)
    rwa [Prod.mk_zero_zero] at h
  obtain ⟨δ, hδ, hδP⟩ :=
    Metric.eventually_nhds_iff.mp (hpull.eventually (hev1.and (hev2.and hev3)))
  refine ⟨ε, hε, min δ ε, lt_min hδ hε, min_le_right _ _, fun e he => ?_,
    fun e he x hx hsol => ?_⟩
  · have heδ : dist e 0 < δ := by
      rw [dist_zero_right]
      exact lt_of_lt_of_le he (min_le_left _ _)
    obtain ⟨htar, hnorm, hcds⟩ := hδP heδ
    have hright : H (H.symm (e, 0)) = (e, 0) := H.right_inv htar
    have hfst : (H.symm (e, 0)).1 = e := congrArg Prod.fst hright
    have hsnd : eqMapS 𝔼 G hG.continuous (H.symm (e, 0)) = 0 := congrArg Prod.snd hright
    refine ⟨lt_of_le_of_lt (norm_snd_le _) hnorm, ?_, ?_⟩
    · rw [← eqMapS_eq_zero_iff 𝔼 G hG.continuous ha]
      have hq : ((e, implicitSolS 𝔼 G hG hab e) : SProc Ω E × Proc Ω) = H.symm (e, 0) :=
        Prod.ext hfst.symm rfl
      rw [hq]
      exact hsnd
    · exact contDiffAt_snd.comp e (hcds.comp e (contDiffAt_id.prodMk contDiffAt_const))
  · have hsrc : ((e, x) : SProc Ω E × Proc Ω) ∈ H.source := by
      apply hεsub
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
      exact max_lt (lt_of_lt_of_le he (min_le_right _ _)) hx
    have hHx : H (e, x) = (e, 0) :=
      Prod.ext rfl ((eqMapS_eq_zero_iff 𝔼 G hG.continuous ha e x).mpr hsol)
    have h := H.left_inv hsrc
    rw [hHx] at h
    exact (congrArg Prod.snd h).symm

/-! ### Accuracy of the linear RE solution (erratum E18) -/

/-- Woodford (2003), App. A.3, p. 634: the exact equilibrium map minus its linearisation at the
steady state is the conditional expectation of the pointwise Taylor remainder. -/
theorem eqMapS_sub_eqD0S [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ} (hG : ContDiff ℝ 1 G)
    (q : SProc Ω E × Proc Ω) :
    eqMapS 𝔼 G hG.continuous q - eqD0S 𝔼 G q =
      condE 𝔼 (nem G hG.continuous (argL 𝔼 q) - nemD G hG (argL 𝔼 0) (argL 𝔼 q)) := by
  rw [← eqDS_zero 𝔼 hG, map_sub]
  change condE 𝔼 (nem G hG.continuous (argL 𝔼 q)) + slopeA G • (q.2 - condE 𝔼 q.2) -
    (condE 𝔼 (nemD G hG (argL 𝔼 0) (argL 𝔼 q)) + slopeA G • (q.2 - condE 𝔼 q.2)) = _
  abel

/-- Woodford (2003), App. A.3, p. 634, corrected per E18: **if `DG` is Lipschitz near the steady
state (`C^{1,1}`, e.g. `G ∈ C²`), the exact stochastic equilibrium differs from the linear RE
solution by at most `C ‖e‖∞²`**. -/
theorem second_orderS [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ} (hG : ContDiff ℝ 1 G)
    (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) {K r : ℝ} (hK : 0 ≤ K)
    (hL : ∀ z : ℝ × ℝ × ℝ × E, ‖z‖ ≤ r → ‖fderiv ℝ G z - fderiv ℝ G 0‖ ≤ K * ‖z‖) (hr : 0 < r) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ e : SProc Ω E, ‖e‖ < δ →
      ‖implicitSolS 𝔼 G hG hab e - linSolG 𝔼 G e‖ ≤ C * ‖e‖ ^ 2 := by
  obtain ⟨ε, hε, δ₁, hδ₁, -, hex, -⟩ := local_determinacyS 𝔼 hG h0 hab
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ :=
    Metric.eventually_nhds_iff.mp ((hasFDerivAt_implicitSolS 𝔼 hG h0 hab).isLittleO.def one_pos)
  set C1 := ‖linSolG 𝔼 G‖ + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  have hC1one : 1 ≤ C1 := le_add_of_nonneg_left (norm_nonneg _)
  set Tinv := TInvS 𝔼 (slopeA G) (sB G) with hTinv
  refine ⟨‖Tinv‖ * (K * C1 ^ 2), min (min δ₁ δ₂) (r / C1), by positivity, fun e he => ?_⟩
  have he1 : ‖e‖ < δ₁ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_left _ _))
  have he2 : dist e 0 < δ₂ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_right _ _))
  have he3 : C1 * ‖e‖ ≤ r := by
    have h : ‖e‖ < r / C1 := lt_of_lt_of_le he (min_le_right _ _)
    rw [lt_div_iff₀ hC1pos] at h
    linarith
  obtain ⟨-, hsol, -⟩ := hex e he1
  set x := implicitSolS 𝔼 G hG hab e with hx
  set ℓ := linSolG 𝔼 G e with hℓ
  have hxb : ‖x‖ ≤ C1 * ‖e‖ := by
    have h := hδ₂P he2
    rw [implicitSolS_zero 𝔼 hG h0 hab, sub_zero, sub_zero, one_mul] at h
    calc ‖x‖ = ‖(x - ℓ) + ℓ‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - ℓ‖ + ‖ℓ‖ := norm_add_le _ _
      _ ≤ ‖e‖ + ‖linSolG 𝔼 G‖ * ‖e‖ := add_le_add h ((linSolG 𝔼 G).le_opNorm e)
      _ = C1 * ‖e‖ := by rw [hC1]; ring
  have hq : ‖((e, x) : SProc Ω E × Proc Ω)‖ ≤ C1 * ‖e‖ := by
    rw [Prod.norm_mk]
    exact max_le (le_mul_of_one_le_left (norm_nonneg _) hC1one) hxb
  -- the remainder
  set R := nem G hG.continuous (argL 𝔼 (e, x)) - nemD G hG (argL 𝔼 0) (argL 𝔼 (e, x)) with hR
  have hRb : ‖R‖ ≤ K * (C1 * ‖e‖) ^ 2 := by
    refine norm_le_of_forall (by positivity) (fun i => ?_)
    have hz : ‖argL 𝔼 (e, x) i‖ ≤ C1 * ‖e‖ :=
      (norm_argFun_le 𝔼 (e, x) i).trans hq
    have hrem := abs_remainder_le3 hG hK hL _ (hz.trans he3)
    have e1 : R i = G (argL 𝔼 (e, x) i) - G 0 - fderiv ℝ G 0 (argL 𝔼 (e, x) i) := by
      rw [hR, lp.coeFn_sub, Pi.sub_apply, nem_apply, nemD_apply, map_zero, h0, sub_zero]
      rfl
    rw [e1, Real.norm_eq_abs]
    exact hrem.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) hK)
  have hzero : eqMapS 𝔼 G hG.continuous (e, x) = 0 :=
    (eqMapS_eq_zero_iff 𝔼 G hG.continuous (ne_zero_of_abs_lt hab) e x).mpr hsol
  have hD : eqD0S 𝔼 G (e, x) = TOpS 𝔼 (slopeA G) (sB G) x + cOpS 𝔼 (sC G) e := rfl
  have hkey : TOpS 𝔼 (slopeA G) (sB G) (x - ℓ) = -condE 𝔼 R := by
    have h1 := eqMapS_sub_eqD0S 𝔼 hG (e, x)
    rw [hzero, zero_sub, hD] at h1
    have h1' : condE 𝔼 R = -(TOpS 𝔼 (slopeA G) (sB G) x + cOpS 𝔼 (sC G) e) := h1.symm
    have h3 : TOpS 𝔼 (slopeA G) (sB G) ℓ = -cOpS 𝔼 (sC G) e :=
      eq_neg_of_add_eq_zero_left (linSolS_solves 𝔼 hab (sC G) e)
    rw [map_sub, h3, h1', neg_neg]
    abel
  have hlin : ‖TOpS 𝔼 (slopeA G) (sB G) (x - ℓ)‖ ≤ K * (C1 * ‖e‖) ^ 2 := by
    rw [hkey, norm_neg]
    exact ((condE 𝔼).le_of_opNorm_le (norm_condE_le 𝔼) R).trans (by rw [one_mul]; exact hRb)
  calc ‖x - ℓ‖ = ‖Tinv (TOpS 𝔼 (slopeA G) (sB G) (x - ℓ))‖ := by
        rw [hTinv, TInvS_TOpS 𝔼 hab]
    _ ≤ ‖Tinv‖ * ‖TOpS 𝔼 (slopeA G) (sB G) (x - ℓ)‖ := Tinv.le_opNorm _
    _ ≤ ‖Tinv‖ * (K * (C1 * ‖e‖) ^ 2) := mul_le_mul_of_nonneg_left hlin (norm_nonneg _)
    _ = ‖Tinv‖ * (K * C1 ^ 2) * ‖e‖ ^ 2 := by ring

/-! ### Only the behaviour near the steady state matters (bump cut-off) -/

/-- Woodford (2003), App. A.3, p. 634: the cut-off (`LocalIFT.cutoff`) has the same slopes and the
same linear RE solution operator as `G`. -/
theorem slopes_cutoffS (G : ℝ × ℝ × ℝ × E → ℝ) [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) :
    slopeA (cutoff G r hr) = slopeA G ∧ sB (cutoff G r hr) = sB G ∧
      linSolG 𝔼 (cutoff G r hr) = linSolG 𝔼 G := by
  have h := fderiv_cutoff G hr
  refine ⟨by rw [slopeA, slopeA, h], by rw [sB, sB, slopeB, slopeB, slopeD, slopeD, h], ?_⟩
  simp only [linSolG, slopeA, sB, slopeB, slopeD, sC, slopeC, h]

/-- Woodford (2003), App. A.3, p. 634: near the steady state the cut-off conditions and the
original conditions have the same stochastic solutions. -/
theorem solvesS_cutoff_iff [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ} {r : ℝ}
    (hr : 0 < r) {e : SProc Ω E} {x : Proc Ω} (he : ‖e‖ ≤ r / 4) (hx : ‖x‖ ≤ r / 4) :
    SolvesS 𝔼 (cutoff G r hr) e x ↔ SolvesS 𝔼 G e x := by
  have hp : ∀ t ω, cutoff G r hr (x (t, ω), x (t + 1, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω)) =
      G (x (t, ω), x (t + 1, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω)) := fun t ω =>
    cutoff_eq hr ((norm_argFun_le 𝔼 (e, x) (t, ω)).trans
      (by rw [Prod.norm_mk]; exact max_le he hx))
  unfold SolvesS
  simp only [hp]

/-- Woodford (2003), App. A.3, pp. 633–634, **local form of the stochastic theorem**: if `G` is
`C¹` near the steady state, `G(0) = 0` and `|b| < |a|`, there are `ε, δ > 0` and a map
`X : L∞(E) → L∞` with `X(0) = 0` and derivative at `0` the linear RE solution operator, such that
for every disturbance process with `‖e‖∞ < δ`, `X(e)` is a bounded adapted equilibrium with
`‖X(e)‖∞ < ε/2`, `X` is `C¹` near `e`, and every bounded adapted equilibrium with `‖x‖∞ < ε`
equals `X(e)`. The radii can be taken below any prescribed `η > 0`. -/
theorem local_determinacyS_loc [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : SProc Ω E → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolG 𝔼 G) 0 ∧
      ∀ e : SProc Ω E, ‖e‖ < δ → ‖X e‖ < ε / 2 ∧ SolvesS 𝔼 G e (X e) ∧ ContDiffAt ℝ 1 X e ∧
        ∀ x : Proc Ω, ‖x‖ < ε → SolvesS 𝔼 G e x → x = X e := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hG
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : ℝ × ℝ × ℝ × E, ‖p‖ < r → ContDiffAt ℝ 1 G p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set K := cutoff G r hr with hK
  have hK1 : ContDiff ℝ 1 K := contDiff_cutoff hr hball
  obtain ⟨hsa, hsb, hls⟩ := slopes_cutoffS 𝔼 G hr
  have hab' : |sB K| < |slopeA K| := by rw [hsa, hsb]; exact hab
  have hK0 : K 0 = 0 := by rw [hK, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, hex, huniq⟩ := local_determinacyS 𝔼 hK1 hK0 hab'
  set X := implicitSolS 𝔼 K hK1 hab' with hX
  have hX0 : X 0 = 0 := implicitSolS_zero 𝔼 hK1 hK0 hab'
  have hcont : ContinuousAt X 0 := (hasFDerivAt_implicitSolS 𝔼 hK1 hK0 hab').continuousAt
  have hev : ∀ᶠ e in 𝓝 (0 : SProc Ω E), ‖X e‖ < r / 8 := by
    have ht := hcont.tendsto
    rw [hX0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds (0 : Proc Ω)
      (by positivity : (0 : ℝ) < r / 8))).mono (fun e he => by simpa using he)
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₁) (r / 4), lt_min (lt_min hδ₀ hδ₁) (by positivity),
    (min_le_right _ _).trans hrη, X, hX0, ?_, fun e he => ?_⟩
  · rw [← hls]
    exact hasFDerivAt_implicitSolS 𝔼 hK1 hK0 hab'
  have he0 : ‖e‖ < δ₀ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_left _ _))
  have he1 : dist e 0 < δ₁ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_right _ _))
  have he4 : ‖e‖ ≤ r / 4 := (lt_of_lt_of_le he (min_le_right _ _)).le
  obtain ⟨hXn, hXs, hXc⟩ := hex e he0
  have hXr := hδ₁P he1
  have hXr4 : ‖X e‖ ≤ r / 4 := by linarith
  refine ⟨by rw [lt_div_iff₀ two_pos]; exact lt_min (by linarith) (by linarith),
    (solvesS_cutoff_iff 𝔼 hr he4 hXr4).mp hXs, hXc, fun x hx hsol => ?_⟩
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  exact huniq e he0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solvesS_cutoff_iff 𝔼 hr he4 hx4).mpr hsol)

/-- Woodford (2003), App. A.3, p. 634, "approximated (to first order in a bound on the amplitude of
the disturbances)", **`C¹` case, precise form (E18)**: if `G` is only `C¹` near the steady state,
the error of the linear RE solution is `o(‖e‖∞)`: for every `c > 0` there is `δ_c > 0` such that
every bounded adapted equilibrium with `‖x‖∞ < ε` satisfies `‖x − x̂(e)‖∞ ≤ c ‖e‖∞` when
`‖e‖∞ < δ_c`. -/
theorem first_order_loc [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) :
    ∃ ε > 0, ∀ c > 0, ∃ δ > 0, ∀ e : SProc Ω E, ‖e‖ < δ → ∀ x : Proc Ω, ‖x‖ < ε →
      SolvesS 𝔼 G e x → ‖x - linSolG 𝔼 G e‖ ≤ c * ‖e‖ := by
  obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ := local_determinacyS_loc 𝔼 hG h0 hab one_pos
  refine ⟨ε, hε, fun c hc => ?_⟩
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ := Metric.eventually_nhds_iff.mp (hXd.isLittleO.def hc)
  refine ⟨min δ δ₂, lt_min hδ hδ₂, fun e he x hx hsol => ?_⟩
  have he1 : ‖e‖ < δ := lt_of_lt_of_le he (min_le_left _ _)
  have he2 : dist e 0 < δ₂ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le he (min_le_right _ _)
  rw [(hX e he1).2.2.2 x hx hsol]
  have h := hδ₂P he2
  rwa [hX0, sub_zero, sub_zero] at h

/-- Woodford (2003), App. A.3, p. 634 ("accurate up to … `O(‖u‖²)`"), **local form, corrected per
E18**: if `G` is `C²` near the steady state, every bounded adapted equilibrium with `‖x‖∞ < ε`
satisfies `‖x − x̂(e)‖∞ ≤ C ‖e‖∞²` for `‖e‖∞ < δ`, `x̂` the linear RE solution (radii below any
prescribed `η > 0`). -/
theorem second_orderS_loc [FiniteDimensional ℝ E] {G : ℝ × ℝ × ℝ × E → ℝ}
    (hG : ContDiffAt ℝ 2 G 0) (h0 : G 0 = 0) (hab : |sB G| < |slopeA G|) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ C : ℝ, ∀ e : SProc Ω E, ‖e‖ < δ → ∀ x : Proc Ω,
      ‖x‖ < ε → SolvesS 𝔼 G e x → ‖x - linSolG 𝔼 G e‖ ≤ C * ‖e‖ ^ 2 := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hG
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : ℝ × ℝ × ℝ × E, ‖p‖ < r → ContDiffAt ℝ 2 G p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set K := cutoff G r hr with hK
  have hK2 : ContDiff ℝ 2 K := contDiff_cutoff hr hball
  have hK1 : ContDiff ℝ 1 K := hK2.of_le (by norm_num)
  obtain ⟨hsa, hsb, hls⟩ := slopes_cutoffS 𝔼 G hr
  have hab' : |sB K| < |slopeA K| := by rw [hsa, hsb]; exact hab
  have hK0 : K 0 = 0 := by rw [hK, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, -, huniq⟩ := local_determinacyS 𝔼 hK1 hK0 hab'
  obtain ⟨Kl, r', hKl, hr', hL⟩ := lipschitz_fderiv3 hK2
  obtain ⟨C, δ₂, hδ₂, hC⟩ := second_orderS 𝔼 hK1 hK0 hab' hKl hL hr'
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₂) (r / 4), lt_min (lt_min hδ₀ hδ₂) (by positivity),
    (min_le_right _ _).trans hrη, C, fun e he x hx hsol => ?_⟩
  have he0 : ‖e‖ < δ₀ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_left _ _))
  have he2 : ‖e‖ < δ₂ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_right _ _))
  have he4 : ‖e‖ ≤ r / 4 := (lt_of_lt_of_le he (min_le_right _ _)).le
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  have hxX := huniq e he0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solvesS_cutoff_iff 𝔼 hr he4 hx4).mpr hsol)
  rw [← hls, hxX]
  exact hC e he2

/-! ### Erratum E18: `C¹` does not give `O(‖e‖²)` -/

/-- Woodford (2003), App. A.3, p. 633, erratum E18: the `C¹` (not `C^{1,1}`) condition
`G(x, y, z, v) = x − v − v^{3/2}` (real power; `v^{3/2} = 0` for `v ≤ 0` in Mathlib). -/
noncomputable def gC1 (p : ℝ × ℝ × ℝ × ℝ) : ℝ := p.1 - (p.2.2.2 + p.2.2.2 ^ (3 / 2 : ℝ))

/-- Woodford (2003), App. A.3, erratum E18: the projection `(x, y, z, v) ↦ v`. -/
noncomputable def proj4 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))

/-- Woodford (2003), App. A.3, erratum E18: the counterexample is `C¹`. -/
theorem contDiff_gC1 : ContDiff ℝ 1 gC1 := by
  have h : ContDiff ℝ 1 (fun y : ℝ => y ^ (3 / 2 : ℝ)) := by
    have h' := Real.contDiff_rpow_const_of_le (p := 3 / 2) (n := 1) (by norm_num)
    simpa using h'
  have h4 : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) := proj4.contDiff
  exact contDiff_fst.sub (h4.add (h.comp h4))

/-- Woodford (2003), App. A.3, erratum E18: the derivative of the counterexample at the steady
state, `(x, y, z, v) ↦ x − v`. -/
theorem hasFDerivAt_gC1 :
    HasFDerivAt gC1 (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ) - (proj4 + (0 : ℝ) • proj4)) 0 := by
  have hr : HasDerivAt (fun y : ℝ => y ^ (3 / 2 : ℝ)) 0 (proj4 0) := by
    have h' := Real.hasDerivAt_rpow_const (x := 0) (p := 3 / 2) (Or.inr (by norm_num))
    norm_num at h'
    rw [map_zero]
    simpa using h'
  exact hasFDerivAt_fst.sub ((proj4.hasFDerivAt (x := 0)).add
    (hr.comp_hasFDerivAt (0 : ℝ × ℝ × ℝ × ℝ) proj4.hasFDerivAt))

/-- Woodford (2003), App. A.3, erratum E18: the slopes of the counterexample, `a = 1`, `b = 0`,
`c = −1`. -/
theorem slopes_gC1 : slopeA gC1 = 1 ∧ sB gC1 = 0 ∧ ∀ v, sC gC1 v = -v := by
  have h := hasFDerivAt_gC1.fderiv
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [slopeA, h]
    simp [proj4]
  · rw [sB, slopeB, slopeD, h]
    simp [proj4]
  · simp only [sC, slopeC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, h]
    simp [proj4]

/-- Woodford (2003), App. A.3, erratum E18: the counterexample is determinate (`|0| < |1|`). -/
theorem abs_slopes_gC1 : |sB gC1| < |slopeA gC1| := by
  rw [slopes_gC1.1, slopes_gC1.2.1]
  norm_num

/-- Woodford (2003), App. A.3, p. 634, erratum E18, **counterexample to the printed `O(‖u‖²)`
claim for a `C¹` model under uncertainty**: for `G(x, y, z, v) = x − v − v^{3/2}` (`C¹`,
determinate) and any expectation system on a nonempty state space there are no `C, δ, ε` with
`‖x − x̂(e)‖∞ ≤ C ‖e‖∞²` for all equilibria `‖x‖∞ < ε` and disturbances `‖e‖∞ < δ` (along
`e ≡ η²` the error is exactly `η³`). So `second_orderS_loc` needs `C²`; for `C¹` only the
`o(‖e‖)` statement `first_order_loc` holds. -/
theorem not_second_order_of_C1S [Nonempty Ω] :
    ¬ ∃ C δ ε : ℝ, 0 < δ ∧ 0 < ε ∧ ∀ e : SProc Ω ℝ, ‖e‖ < δ → ∀ x : Proc Ω, ‖x‖ < ε →
      SolvesS 𝔼 gC1 e x → ‖x - linSolG 𝔼 gC1 e‖ ≤ C * ‖e‖ ^ 2 := by
  rintro ⟨C, δ, ε, hδ, hε, hC⟩
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  obtain ⟨hA, hB, hCc⟩ := slopes_gC1
  set m := min (min δ (min ε 1)) (1 / (|C| + 1)) with hm
  have hCpos : 0 < |C| + 1 := by positivity
  have hm0 : 0 < m := lt_min (lt_min hδ (lt_min hε one_pos)) (by positivity)
  set η := m / 2 with hη
  have hη0 : 0 < η := by positivity
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hmε : m ≤ ε := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm1 : m ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmC : m ≤ 1 / (|C| + 1) := min_le_right _ _
  have hη1 : η < 1 := by linarith
  have hηsq : η ^ 2 < η := by nlinarith
  have hηcube : η ^ 3 < η := by nlinarith
  have hCη : |C| * η < 1 := by
    have h1 : (|C| + 1) * m ≤ 1 := by
      rw [le_div_iff₀ hCpos] at hmC
      linarith
    nlinarith [abs_nonneg C]
  set e : SProc Ω ℝ := mkB (fun _ => η ^ 2) ⟨η ^ 2, fun _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)]⟩ with he
  have henorm : ‖e‖ ≤ η ^ 2 := norm_le_of_forall (sq_nonneg η) (fun i => by
    rw [he, mkB_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)])
  set x : Proc Ω := detP (fun _ => η ^ 2 + η ^ 3) ⟨|η ^ 2 + η ^ 3|, fun _ => le_rfl⟩ with hx
  have hxnorm : ‖x‖ < ε := by
    have h : ‖x‖ ≤ η ^ 2 + η ^ 3 := norm_le_of_forall (by positivity) (fun i => by
      rw [Real.norm_eq_abs]
      change |η ^ 2 + η ^ 3| ≤ _
      exact (abs_of_nonneg (by positivity)).le)
    linarith
  have hconst : ∀ t, slice x t = fun _ => η ^ 2 + η ^ 3 := fun t => rfl
  have hsol : SolvesS 𝔼 gC1 e x := by
    refine ⟨fun t => by rw [hconst, 𝔼.const], fun t => ?_⟩
    have hf : (fun ω => gC1 (x (t, ω), x (t + 1, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω))) =
        0 := by
      funext ω
      change (η ^ 2 + η ^ 3) - (η ^ 2 + (η ^ 2) ^ (3 / 2 : ℝ)) = 0
      rw [LocalIFT.sq_rpow_three_halves hη0.le]
      ring
    rw [hf, map_zero]
  set ℓ := linSolG 𝔼 gC1 e with hℓ
  have hlin : ∀ t ω, ℓ (t, ω) = η ^ 2 := by
    intro t ω
    have h2 := congrArg (fun y : Proc Ω => y (t, ω))
      (linSolS_solves 𝔼 abs_slopes_gC1 (sC gC1) e)
    change slopeA gC1 * ℓ (t, ω) + sB gC1 * 𝔼.E t (slice ℓ (t + 1)) ω +
      𝔼.E t (fun ω' => sC gC1 (e (t, ω'))) ω = 0 at h2
    have hc : (fun ω' => sC gC1 (e (t, ω'))) = fun _ => -(η ^ 2) := by
      funext ω'
      rw [hCc]
      rfl
    rw [hc, 𝔼.const, hA, hB] at h2
    linarith
  have herr := hC e (lt_of_le_of_lt henorm (by linarith)) x hxnorm hsol
  have hlow : η ^ 3 ≤ ‖x - ℓ‖ := by
    have h := norm_apply_le (x - ℓ) (0, ω₀)
    have e1 : (x - ℓ) (0, ω₀) = η ^ 3 := by
      rw [lp.coeFn_sub, Pi.sub_apply, hlin]
      change η ^ 2 + η ^ 3 - η ^ 2 = η ^ 3
      ring
    rw [e1, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h
  have hup : C * ‖e‖ ^ 2 ≤ |C| * (η ^ 2) ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) henorm 2) (abs_nonneg C))
  have hfin : η ^ 3 ≤ |C| * η ^ 4 := by nlinarith
  have hpos : 0 < η ^ 3 * (1 - |C| * η) := mul_pos (by positivity) (by linarith)
  nlinarith

/-! ### The two forms: (A.11) `E_t[F(x_t, x_{t+1}, e_t)] = 0` and `F(x_t, E_t x_{t+1}, e_t) = 0` -/

/-- Woodford (2003), (A.11), p. 633: the projection `(x, y, z, v) ↦ (x, y, v)`. -/
noncomputable def projII : ℝ × ℝ × ℝ × E →L[ℝ] ℝ × ℝ × E :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × E)).prod
    (((ContinuousLinearMap.fst ℝ ℝ (ℝ × E)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × E))).prod
      (((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × E))).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × E))))

/-- Woodford (2003), p. 634: the projection `(x, y, z, v) ↦ (x, z, v)`. -/
noncomputable def projI : ℝ × ℝ × ℝ × E →L[ℝ] ℝ × ℝ × E :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × E)).prod
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × E)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × E)))

/-- Woodford (2003), eq. (A.11), p. 633: a period condition `F(x_t, x_{t+1}, e_t)` of the
perfect-foresight class (`LocalIFT`) placed **inside** the conditional expectation,
`E_t[F(x_t, x_{t+1}, e_t)] = 0`. -/
noncomputable def liftII (F : ℝ × ℝ × E → ℝ) (p : ℝ × ℝ × ℝ × E) : ℝ := F (projII p)

/-- Woodford (2003), p. 634: a period condition evaluated at the forecast,
`F(x_t, E_t x_{t+1}, e_t) = 0`. -/
noncomputable def liftI (F : ℝ × ℝ × E → ℝ) (p : ℝ × ℝ × ℝ × E) : ℝ := F (projI p)

/-- Woodford (2003), (A.11), p. 633: the solutions of the lifted class are exactly the adapted
processes with `E_t[F(x_t, x_{t+1}, e_t)] = 0`. -/
theorem solvesS_liftII_iff (F : ℝ × ℝ × E → ℝ) (e : SProc Ω E) (x : Proc Ω) :
    SolvesS 𝔼 (liftII F) e x ↔ (∀ t, 𝔼.E t (slice x t) = slice x t) ∧
      ∀ t, 𝔼.E t (fun ω => F (x (t, ω), x (t + 1, ω), e (t, ω))) = 0 := Iff.rfl

/-- Woodford (2003), (A.11), p. 633: the lifted condition vanishes at the steady state. -/
theorem liftII_zero {F : ℝ × ℝ × E → ℝ} (h0 : F 0 = 0) : liftII F 0 = 0 := by
  rw [liftII, map_zero, h0]

/-- Woodford (2003), p. 634: the lifted condition vanishes at the steady state. -/
theorem liftI_zero {F : ℝ × ℝ × E → ℝ} (h0 : F 0 = 0) : liftI F 0 = 0 := by
  rw [liftI, map_zero, h0]

/-- Woodford (2003), (A.11), p. 633: lifting preserves `Cⁿ` at the steady state. -/
theorem contDiffAt_liftII {F : ℝ × ℝ × E → ℝ} {n : ℕ} (hF : ContDiffAt ℝ n F 0) :
    ContDiffAt ℝ n (liftII F) 0 := by
  have hF' : ContDiffAt ℝ n F (projII 0) := by rw [map_zero]; exact hF
  exact hF'.comp (0 : ℝ × ℝ × ℝ × E) (projII (E := E)).contDiff.contDiffAt

/-- Woodford (2003), p. 634: lifting preserves `Cⁿ` at the steady state. -/
theorem contDiffAt_liftI {F : ℝ × ℝ × E → ℝ} {n : ℕ} (hF : ContDiffAt ℝ n F 0) :
    ContDiffAt ℝ n (liftI F) 0 := by
  have hF' : ContDiffAt ℝ n F (projI 0) := by rw [map_zero]; exact hF
  exact hF'.comp (0 : ℝ × ℝ × ℝ × E) (projI (E := E)).contDiff.contDiffAt

/-- Woodford (2003), (A.11)–(A.12), pp. 633–634: **the linearisation of
`E_t[F(x_t, x_{t+1}, e_t)] = 0` has the perfect-foresight slopes**: `a = ∂F/∂x_t`,
`b = ∂F/∂x_{t+1}` (on `E_t x̂_{t+1}`), `c = ∂F/∂e_t`. -/
theorem slopes_liftII {F : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F 0) :
    slopeA (liftII F) = slopeA F ∧ sB (liftII F) = slopeB F ∧ sC (liftII F) = slopeC F := by
  have hF' : HasFDerivAt F (fderiv ℝ F 0) (projII 0) := by rw [map_zero]; exact hF.hasFDerivAt
  have hd : fderiv ℝ (liftII F) 0 = (fderiv ℝ F 0).comp projII :=
    (hF'.comp (0 : ℝ × ℝ × ℝ × E) (projII (E := E)).hasFDerivAt).fderiv
  refine ⟨?_, ?_, ?_⟩
  · rw [slopeA, hd, slopeA]
    rfl
  · rw [sB, slopeB, slopeD, hd, slopeB]
    change fderiv ℝ F 0 (0, 1, 0) + fderiv ℝ F 0 (0, 0, 0) = _
    rw [show ((0, 0, 0) : ℝ × ℝ × E) = 0 from rfl, map_zero, add_zero]
  · refine ContinuousLinearMap.ext fun v => ?_
    simp only [sC, slopeC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hd]
    rfl

/-- Woodford (2003), p. 634: the linearisation of `F(x_t, E_t x_{t+1}, e_t) = 0` has the
perfect-foresight slopes. -/
theorem slopes_liftI {F : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F 0) :
    slopeA (liftI F) = slopeA F ∧ sB (liftI F) = slopeB F ∧ sC (liftI F) = slopeC F := by
  have hF' : HasFDerivAt F (fderiv ℝ F 0) (projI 0) := by rw [map_zero]; exact hF.hasFDerivAt
  have hd : fderiv ℝ (liftI F) 0 = (fderiv ℝ F 0).comp projI :=
    (hF'.comp (0 : ℝ × ℝ × ℝ × E) (projI (E := E)).hasFDerivAt).fderiv
  refine ⟨?_, ?_, ?_⟩
  · rw [slopeA, hd, slopeA]
    rfl
  · rw [sB, slopeB, slopeD, hd, slopeB]
    change fderiv ℝ F 0 (0, 0, 0) + fderiv ℝ F 0 (0, 1, 0) = _
    rw [show ((0, 0, 0) : ℝ × ℝ × E) = 0 from rfl, map_zero, zero_add]
  · refine ContinuousLinearMap.ext fun v => ?_
    simp only [sC, slopeC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hd]
    rfl

/-! ### Information sets: when is a function of known variables known? -/

/-- Woodford (2003), p. 633 ("the state of the world `s_t`"): two states are indistinguishable at
date `t` when every conditional expectation takes the same value at both. -/
def Indist (t : ℕ) (ω ω' : Ω) : Prop := ∀ z : Ω → ℝ, 𝔼.E t z ω = 𝔼.E t z ω'

/-- Woodford (2003), p. 633: a function is constant on date-`t` information cells. -/
def CellConst {α : Type*} (t : ℕ) (f : Ω → α) : Prop := ∀ ω ω', Indist 𝔼 t ω ω' → f ω = f ω'

/-- Woodford (2003), p. 633 ("endogenous variables … functions of the state `s_t`"): the
expectation system is **informationally closed** when every variable constant on date-`t`
information cells is known at `t`. This holds for perfect foresight
(`perfectForesight_infoClosed`) and every finite event tree (`finiteTree_infoClosed`); it is not
implied by the `ExpectationSystem` axioms (`skewSystem_not_infoClosed`). -/
def InfoClosed : Prop := ∀ t (y : Ω → ℝ), CellConst 𝔼 t y → 𝔼.E t y = y

/-- Woodford (2003), p. 633: a known variable is constant on information cells. -/
theorem cellConst_of_known {t : ℕ} {y : Ω → ℝ} (hy : 𝔼.E t y = y) : CellConst 𝔼 t y :=
  fun ω ω' h => by rw [← hy]; exact h y

/-- Woodford (2003), p. 633: every forecast `E_t z` is constant on information cells. -/
theorem cellConst_E (t : ℕ) (z : Ω → ℝ) : CellConst 𝔼 t (𝔼.E t z) := fun _ _ h => h z

/-- Woodford (2003), p. 634: under informational closure, **`F(x_t, E_t x_{t+1}, e_t) = 0` (for
adapted `x` and cell-constant `e`) is the same as `E_t[F(x_t, E_t x_{t+1}, e_t)] = 0`**, so the
general theorem covers the form `F(x_t, E_t x_{t+1}, e_t) = 0`. -/
theorem solvesS_liftI_iff (hcl : InfoClosed 𝔼) (F : ℝ × ℝ × E → ℝ) {e : SProc Ω E}
    (he : ∀ t, CellConst 𝔼 t (fun ω => e (t, ω))) (x : Proc Ω) :
    SolvesS 𝔼 (liftI F) e x ↔ (∀ t, 𝔼.E t (slice x t) = slice x t) ∧
      ∀ t ω, F (x (t, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω)) = 0 := by
  have hknown : (∀ t, 𝔼.E t (slice x t) = slice x t) → ∀ t,
      𝔼.E t (fun ω => F (x (t, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω))) =
        fun ω => F (x (t, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω)) := by
    intro had t
    refine hcl t _ (fun ω ω' h => ?_)
    have h1 : x (t, ω) = x (t, ω') := cellConst_of_known 𝔼 (had t) ω ω' h
    have h2 := cellConst_E 𝔼 t (slice x (t + 1)) ω ω' h
    have h3 := he t ω ω' h
    simp only at h3
    rw [h1, h2, h3]
  constructor
  · rintro ⟨had, hE⟩
    refine ⟨had, fun t ω => ?_⟩
    have h := hE t
    change 𝔼.E t (fun ω => F (x (t, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω))) = 0 at h
    rw [hknown had t] at h
    exact congrFun h ω
  · rintro ⟨had, hF⟩
    refine ⟨had, fun t => ?_⟩
    change 𝔼.E t (fun ω => F (x (t, ω), 𝔼.E t (slice x (t + 1)) ω, e (t, ω))) = 0
    rw [hknown had t]
    funext ω
    exact hF t ω

end Ops

/-- Woodford (2003), p. 633: perfect foresight is informationally closed. -/
theorem perfectForesight_infoClosed : Ops.InfoClosed perfectForesight :=
  fun _ _ _ => rfl

/-- Woodford (2003), p. 633: **every finite event tree is informationally closed** (a variable
constant on the information cells is its own cell average). -/
theorem finiteTree_infoClosed {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : Ops.InfoClosed T.toExpectationSystem := by
  intro t y hy
  funext ω
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact T.condE_of_const_on_cell fun ω' h => hy ω' ω (fun z => T.condE_congr z h)

/-! ### Informational closure is needed for `F(x_t, E_t x_{t+1}, e_t) = 0` -/

/-- Woodford (2003), p. 634 (counterexample, not in the book): the positive unital idempotent
`P y = (y₀, y₁, (y₀ + y₁)/2)` on three states, as a linear map. -/
noncomputable def skewP : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun y i := if (i : ℕ) = 2 then (y 0 + y 1) / 2 else y i
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- Woodford (2003), p. 634 (counterexample): `P` applied. -/
theorem skewP_apply (y : Fin 3 → ℝ) (i : Fin 3) :
    skewP y i = if (i : ℕ) = 2 then (y 0 + y 1) / 2 else y i := rfl

/-- Woodford (2003), p. 634 (counterexample): `P` is idempotent. -/
theorem skewP_skewP (y : Fin 3 → ℝ) : skewP (skewP y) = skewP y := by
  funext i
  fin_cases i <;> simp [skewP_apply]

/-- Woodford (2003), p. 634 (counterexample): the expectation system with `E_t = P` at every
date; it satisfies all `ExpectationSystem` axioms (linearity, constants, monotonicity, tower). -/
noncomputable def skewSystem : ExpectationSystem (Fin 3) where
  E := fun _ => skewP
  const := fun _ c => by
    funext i
    fin_cases i <;> simp [skewP_apply]
  mono := fun _ x y h i => by
    fin_cases i <;> simp [skewP_apply] <;> linarith [h 0, h 1, h 2]
  tower := fun _ x => skewP_skewP x
  known := fun _ x => skewP_skewP x

/-- Woodford (2003), p. 634 (counterexample): the condition `F(x, y, v) = x − y/2 − v²`
(smooth, `a = 1`, `b = −1/2`, so determinate). -/
noncomputable def fSkew (p : ℝ × ℝ × ℝ) : ℝ := p.1 - p.2.1 / 2 - p.2.2 ^ 2

/-- Woodford (2003), p. 634 (counterexample): the known disturbance `(1, 0, 1/2)`. -/
noncomputable def eSkew (i : Fin 3) : ℝ :=
  if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then 0 else 1 / 2

/-- Woodford (2003), p. 634 (counterexample): the skew system is **not** informationally closed
(all states are distinguishable, yet `P ≠ id`). -/
theorem skewSystem_not_infoClosed : ¬ Ops.InfoClosed skewSystem := by
  intro h
  have hz : ∀ ω ω' : Fin 3, Ops.Indist skewSystem 0 ω ω' → ω = ω' := by
    intro ω ω' hi
    have := hi (fun i => ((i : ℕ) : ℝ))
    change skewP _ ω = skewP _ ω' at this
    fin_cases ω <;> fin_cases ω' <;> simp [skewP_apply] at this ⊢
  have h1 := congrFun (h 0 (fun i => if (i : ℕ) = 0 then 1 else 0)
    (fun ω ω' hi => by rw [hz ω ω' hi])) 2
  change skewP _ 2 = _ at h1
  simp [skewP_apply] at h1

/-- Woodford (2003), p. 634 (counterexample, not in the book): **without informational closure
the form `F(x_t, E_t x_{t+1}, e_t) = 0` can fail to have any adapted solution, however small the
(adapted) disturbance**: in the skew system, for every `s ≠ 0` the disturbance `s·(1, 0, 1/2)` is
adapted, `F = fSkew` is smooth with `|b| = 1/2 < 1 = |a|`, and yet there is no adapted
`x : ℕ → Fin 3 → ℝ` (bounded or not) with `F(x_t, E_t x_{t+1}, s e) = 0`. (The (A.11) form
`E_t[F(x_t, x_{t+1}, e_t)] = 0` has a locally unique solution by `local_determinacyS_loc`.) -/
theorem formI_needs_closure (s : ℝ) (hs : s ≠ 0) :
    skewSystem.E 0 (fun ω => s * eSkew ω) = (fun ω => s * eSkew ω) ∧
      ¬ ∃ x : ℕ → Fin 3 → ℝ, (∀ t, skewSystem.E t (x t) = x t) ∧
        ∀ t ω, fSkew (x t ω, skewSystem.E t (x (t + 1)) ω, s * eSkew ω) = 0 := by
  refine ⟨?_, ?_⟩
  · funext i
    change skewP _ i = _
    fin_cases i <;> simp [skewP_apply, eSkew]
    ring
  rintro ⟨x, hx, hF⟩
  have ha := congrFun (hx 0) 2
  change skewP (x 0) 2 = x 0 2 at ha
  have hb : skewSystem.E 0 (x 1) 2 = (skewSystem.E 0 (x 1) 0 + skewSystem.E 0 (x 1) 1) / 2 := by
    change skewP (x 1) 2 = (skewP (x 1) 0 + skewP (x 1) 1) / 2
    simp [skewP_apply]
  have h0 := hF 0 0
  have h1 := hF 0 1
  have h2 := hF 0 2
  simp only [fSkew, eSkew, skewP_apply] at h0 h1 h2 ha
  norm_num at h0 h1 h2 ha
  rw [hb] at h2
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith

namespace Ops

variable (𝔼 : ExpectationSystem Ω) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Determinacy of the linear RE system (A.13), stated for adapted processes -/

/-- Woodford (2003), (A.13), p. 634: if `|b| ≥ |a|` there is a nonzero bounded **adapted**
(indeed deterministic) solution of `a x_t + b E_t x_{t+1} = 0`. -/
theorem exists_adapted_ker [Nonempty Ω] {a b : ℝ} (hc : ¬ |b| < |a|) :
    ∃ x : Proc Ω, condE 𝔼 x = x ∧ TOpS 𝔼 a b x = 0 ∧ x ≠ 0 := by
  push Not at hc
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  have hdet : ∀ (f : ℕ → ℝ) (hf : ∃ C, ∀ t, |f t| ≤ C), condE 𝔼 (detP f hf) = detP f hf :=
    fun f hf => by
      ext ⟨t, ω⟩
      exact congrFun (𝔼.const t (f t)) ω
  rcases eq_or_ne b 0 with hb | hb
  · have ha : a = 0 := by
      rw [hb, abs_zero] at hc
      exact abs_nonpos_iff.mp hc
    refine ⟨detP (fun _ => 1) ⟨1, fun _ => by simp⟩, hdet _ _, ?_, fun h => ?_⟩
    · ext ⟨t, ω⟩
      simp [ha, hb]
    · have := congrArg (fun y : Proc Ω => y (0, ω₀)) h
      simp at this
  · set r := -a / b with hr
    have hr1 : |r| ≤ 1 := by
      rw [hr, abs_div, abs_neg, div_le_one (abs_pos.mpr hb)]
      exact hc
    have hbd : ∃ C, ∀ t, |r ^ t| ≤ C :=
      ⟨1, fun t => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg r) hr1⟩
    refine ⟨detP (fun t => r ^ t) hbd, hdet _ _, ?_, fun h => ?_⟩
    · ext ⟨t, ω⟩
      rw [TOpS_apply]
      have hl := lead_detP 𝔼 (fun t => r ^ t) hbd t ω
      rw [lead_apply] at hl
      rw [hl, detP_apply, lp.coeFn_zero, Pi.zero_apply, hr, pow_succ]
      field_simp
      ring
    · have := congrArg (fun y : Proc Ω => y (0, ω₀)) h
      simp at this

/-- Woodford (2003), (A.12)–(A.13), p. 634, **stated for adapted processes** (the book's
"`(A.12)` has a unique bounded solution in the case of any bounded process"): for every bounded
adapted forcing `y` the linear RE system `a x_t + b E_t x_{t+1} = y_t` has exactly one bounded
adapted solution **if and only if** `|b| < |a|` (on any nonempty state space; no
"generically"). -/
theorem linearRE_unique_iff [Nonempty Ω] (a b : ℝ) :
    (∀ y : Proc Ω, condE 𝔼 y = y → ∃! x : Proc Ω, condE 𝔼 x = x ∧ TOpS 𝔼 a b x = y) ↔
      |b| < |a| := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨k, hk, hk0, hkne⟩ := exists_adapted_ker 𝔼 hc
    obtain ⟨x, -, hx⟩ := h 0 (map_zero _)
    have h1 := hx k ⟨hk, hk0⟩
    have h2 := hx 0 ⟨map_zero _, map_zero _⟩
    exact hkne (h1.trans h2.symm)
  · intro h y hy
    refine ⟨TInvS 𝔼 a b y, ⟨condE_TInvS 𝔼 h hy, TOpS_TInvS 𝔼 h y⟩, fun x hx => ?_⟩
    rw [← hx.2, TInvS_TOpS 𝔼 h]

/-! ### Transformations of a period condition that keep its linearisation -/

/-- Woodford (2003), (1.21), p. 71, under uncertainty: the **exponential form**
`exp(F/κ) − 1` of a log-linear-in-the-future period condition `F` — the exact stochastic Euler
equation `E_t[exp(F(x_t, x_{t+1}, e_t)/κ)] = 1` is `E_t[expT κ F] = 0`. -/
noncomputable def expT (κ : ℝ) (F : ℝ × ℝ × E → ℝ) (p : ℝ × ℝ × E) : ℝ :=
  Real.exp (κ⁻¹ * F p) - 1

omit [NormedSpace ℝ E] in
/-- Woodford (2003), (1.21): the exponential form vanishes at the steady state. -/
theorem expT_zero (κ : ℝ) {F : ℝ × ℝ × E → ℝ} (h0 : F 0 = 0) : expT κ F 0 = 0 := by
  simp [expT, h0]

/-- Woodford (2003), (1.21): the exponential form is `Cⁿ` at the steady state when `F` is. -/
theorem contDiffAt_expT (κ : ℝ) {F : ℝ × ℝ × E → ℝ} {n : ℕ} (hF : ContDiffAt ℝ n F 0) :
    ContDiffAt ℝ n (expT κ F) 0 := by
  have h : ContDiffAt ℝ n (fun p => κ⁻¹ * F p) 0 := contDiffAt_const.mul hF
  exact (Real.contDiff_exp.contDiffAt.comp (0 : ℝ × ℝ × E) h).sub contDiffAt_const

/-- Woodford (2003), (1.21): the derivative of the exponential form at the steady state is
`κ⁻¹ DF(0)`. -/
theorem hasFDerivAt_expT (κ : ℝ) {F : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F 0)
    (h0 : F 0 = 0) : HasFDerivAt (expT κ F) (κ⁻¹ • fderiv ℝ F 0) 0 := by
  have h := ((hF.hasFDerivAt.const_mul κ⁻¹).exp).sub_const 1
  have he : Real.exp (κ⁻¹ * F 0) = 1 := by rw [h0, mul_zero, Real.exp_zero]
  rw [he, one_smul] at h
  exact h

/-- Woodford (2003), (1.21): the slopes of the exponential form are `κ⁻¹` times those of `F`. -/
theorem slopes_expT (κ : ℝ) {F : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F 0) (h0 : F 0 = 0) :
    slopeA (expT κ F) = κ⁻¹ * slopeA F ∧ slopeB (expT κ F) = κ⁻¹ * slopeB F ∧
      slopeC (expT κ F) = κ⁻¹ • slopeC F := by
  have hd := (hasFDerivAt_expT κ hF h0).fderiv
  refine ⟨?_, ?_, ?_⟩
  · rw [slopeA, hd, slopeA]
    rfl
  · rw [slopeB, hd, slopeB]
    rfl
  · rw [slopeC, hd, slopeC]
    rfl

/-- Woodford (2003), (3.3) and (1.21), p. 104, under uncertainty: multiplying a period condition
by a factor `m` with `m(0) = 1` does not change its derivative at the steady state. -/
theorem fderiv_mul_unit {F m : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F 0)
    (hm : DifferentiableAt ℝ m 0) (h0 : F 0 = 0) (hm0 : m 0 = 1) :
    fderiv ℝ (fun p => m p * F p) 0 = fderiv ℝ F 0 := by
  have h := hm.hasFDerivAt.mul hF.hasFDerivAt
  rw [hm0, h0, one_smul, zero_smul, add_zero] at h
  exact h.fderiv

/-- Woodford (2003), (A.13), p. 634: rescaling the linearised condition by `κ⁻¹` does not change
its linear RE solution. -/
theorem linSolS_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ a b : ℝ}
    (hκ : κ ≠ 0) (h : |b| < |a|) (c : E →L[ℝ] ℝ) :
    linSolS 𝔼 (κ⁻¹ * a) (κ⁻¹ * b) (κ⁻¹ • c) = linSolS 𝔼 a b c := by
  have h' : |κ⁻¹ * b| < |κ⁻¹ * a| := by
    rw [abs_mul, abs_mul]
    exact mul_lt_mul_of_pos_left h (abs_pos.mpr (inv_ne_zero hκ))
  refine ContinuousLinearMap.ext fun e => ?_
  set ℓ := linSolS 𝔼 (κ⁻¹ * a) (κ⁻¹ * b) (κ⁻¹ • c) e with hℓ
  have h1 := linSolS_solves 𝔼 h' (κ⁻¹ • c) e
  have h2 : TOpS 𝔼 a b ℓ = -cOpS 𝔼 c e := by
    ext ⟨t, ω⟩
    have h3 := congrArg (fun y : Proc Ω => y (t, ω)) h1
    have hf : (fun ω' => (κ⁻¹ • c) (e (t, ω'))) = κ⁻¹ • fun ω' => c (e (t, ω')) := by
      funext ω'
      rfl
    change κ⁻¹ * a * ℓ (t, ω) + κ⁻¹ * b * 𝔼.E t (slice ℓ (t + 1)) ω +
      𝔼.E t (fun ω' => (κ⁻¹ • c) (e (t, ω'))) ω = 0 at h3
    rw [hf, map_smul, Pi.smul_apply, smul_eq_mul] at h3
    change a * ℓ (t, ω) + b * 𝔼.E t (slice ℓ (t + 1)) ω = -𝔼.E t (fun ω' => c (e (t, ω'))) ω
    have h4 : κ⁻¹ * (a * ℓ (t, ω) + b * 𝔼.E t (slice ℓ (t + 1)) ω +
        𝔼.E t (fun ω' => c (e (t, ω'))) ω) = 0 := by
      rw [← h3]
      ring
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (inv_ne_zero hκ)
    · linarith
  have h6 := TInvS_TOpS 𝔼 h ℓ
  rw [h2] at h6
  rw [← h6]
  change TInvS 𝔼 a b (-cOpS 𝔼 c e) = -(TInvS 𝔼 a b (cOpS 𝔼 c e))
  rw [map_neg]

/-! ### The (A.11) form: local determinacy and indeterminacy -/

/-- Woodford (2003), App. A.3, pp. 633–635, **(A.11) form**: for a period condition `F` that is
`C¹` near the steady state with `F(0) = 0` and `|∂F/∂x_{t+1}| < |∂F/∂x_t|`, and any expectation
system, there are `ε, δ > 0` and a map `X` with `X(0) = 0` whose derivative at `0` is the linear
RE solution operator of (A.13), such that for every bounded disturbance process `‖e‖∞ < δ`
(adapted or not), `X(e)` is a bounded adapted solution of `E_t[F(x_t, x_{t+1}, e_t)] = 0`, it is
`C¹` in `e`, and it is the only one with `‖x‖∞ < ε`. -/
theorem local_determinacyII [FiniteDimensional ℝ E] {F : ℝ × ℝ × E → ℝ}
    (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0) (hab : |slopeB F| < |slopeA F|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω E → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA F) (slopeB F) (slopeC F)) 0 ∧
      ∀ e : SProc Ω E, ‖e‖ < δ → SolvesS 𝔼 (liftII F) e (X e) ∧ ‖X e‖ < ε ∧
        ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε → SolvesS 𝔼 (liftII F) e x → x = X e := by
  obtain ⟨ha, hb, hc⟩ := slopes_liftII (hF.differentiableAt (by norm_num))
  have hab' : |sB (liftII F)| < |slopeA (liftII F)| := by rw [ha, hb]; exact hab
  obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ :=
    local_determinacyS_loc 𝔼 (contDiffAt_liftII hF) (liftII_zero h0) hab' one_pos
  refine ⟨ε, hε, δ, hδ, X, hX0, ?_, fun e he => ?_⟩
  · have hl : linSolG 𝔼 (liftII F) = linSolS 𝔼 (slopeA F) (slopeB F) (slopeC F) := by
      rw [linSolG, ha, hb, hc]
    rw [← hl]
    exact hXd
  obtain ⟨h1, h2, h3, h4⟩ := hX e he
  exact ⟨h2, by linarith, h3, h4⟩

/-- Woodford (2003), App. A.3, pp. 633–635, **exponential (A.11) form**: the same conclusion for
the exact stochastic Euler form `E_t[exp(F(x_t, x_{t+1}, e_t)/κ)] = 1`, with derivative the
linear RE solution of `F`'s own linearisation (rescaling by `κ⁻¹` cancels). -/
theorem local_determinacy_expII [FiniteDimensional ℝ E] {κ : ℝ} (hκ : κ ≠ 0)
    {F : ℝ × ℝ × E → ℝ} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω E → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA F) (slopeB F) (slopeC F)) 0 ∧
      ∀ e : SProc Ω E, ‖e‖ < δ → SolvesS 𝔼 (liftII (expT κ F)) e (X e) ∧ ‖X e‖ < ε ∧
        ContDiffAt ℝ 1 X e ∧
        ∀ x : Proc Ω, ‖x‖ < ε → SolvesS 𝔼 (liftII (expT κ F)) e x → x = X e := by
  obtain ⟨ha, hb, hc⟩ := slopes_expT κ (hF.differentiableAt (by norm_num)) h0
  have hab' : |slopeB (expT κ F)| < |slopeA (expT κ F)| := by
    rw [ha, hb, abs_mul, abs_mul]
    exact mul_lt_mul_of_pos_left hab (abs_pos.mpr (inv_ne_zero hκ))
  obtain ⟨ε, hε, δ, hδ, X, hX0, hXd, hX⟩ :=
    local_determinacyII 𝔼 (contDiffAt_expT κ hF) (expT_zero κ h0) hab'
  refine ⟨ε, hε, δ, hδ, X, hX0, ?_, hX⟩
  rw [ha, hb, hc, linSolS_smul 𝔼 hκ hab] at hXd
  exact hXd

/-- Woodford (2003), App. A.3, p. 632 and the indeterminacy halves of Props. 2.6–2.8, 2.12–2.13,
**under uncertainty**: if `|∂F/∂x_t| < |∂F/∂x_{t+1}|`, every deterministic self-fulfilling path of
the perfect-foresight model (`LocalIFT.local_indeterminacy_loc`) is a bounded adapted solution of
`E_t[F(x_t, x_{t+1}, 0)] = 0`; so for every `ε > 0` there is `r > 0` such that every initial value
`|c| ≤ r` starts a stochastic equilibrium with no disturbances staying within `ε` of the steady
state — a continuum. -/
theorem local_indeterminacyII [FiniteDimensional ℝ E] {F : ℝ × ℝ × E → ℝ}
    (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0) (hab : |slopeA F| < |slopeB F|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r →
      ∃ x : Proc Ω, SolvesS 𝔼 (liftII F) 0 x ∧ ‖x‖ ≤ ε ∧ ∀ ω, x (0, ω) = c := by
  intro ε hε
  obtain ⟨r, hr, hrP⟩ := LocalIFT.local_indeterminacy_loc hF h0 hab ε hε
  refine ⟨r, hr, fun c hc => ?_⟩
  obtain ⟨y, hy, hyn, hy0⟩ := hrP c hc
  refine ⟨detP (fun t => y t) ⟨‖y‖, fun t => LocalIFT.abs_apply_le y t⟩, ⟨fun t => ?_,
    fun t => ?_⟩, ?_, fun ω => hy0⟩
  · exact 𝔼.const t (y t)
  · have hconst : 𝔼.E t (slice (detP (Ω := Ω) (fun t => y t)
        ⟨‖y‖, fun t => LocalIFT.abs_apply_le y t⟩) (t + 1)) = fun _ => y (t + 1) :=
      𝔼.const t (y (t + 1))
    change 𝔼.E t (fun ω => F (y t, y (t + 1), (0 : E))) = 0
    have h1 : F (y t, y (t + 1), (0 : E)) = 0 := by
      have := hy t
      simpa using this
    simp only [h1]
    exact (𝔼.const t 0)
  · exact norm_le_of_forall (hε.le) (fun i => by
      rw [Real.norm_eq_abs]
      exact (LocalIFT.abs_apply_le y i.1).trans hyn)

end Ops

/-! ### Stochastic versions of the local determinacy results of Chapter 2

Each exact period condition of `LocalIFT`/`Nonlinear` is log-linear in the date-`t+1` variables;
under uncertainty the exact Euler equation (1.21) holds in levels inside `E_t`, i.e.
`E_t[exp(F(x_t, x_{t+1}, e_t)/κ)] = 1` (with the date-`t+1` disturbances in `e_t`, which is
therefore not adapted). For the money-growth model the factor `e^{−w}` plays the same role. -/

namespace Models

open Ops

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (1.21) and (2.4), pp. 72, 90, **Taylor-rule Euler equation under
uncertainty**: with `x = log(Π_t/Π*_t)`, `x' = log(Π_{t+1}/Π*_{t+1})` and
`w = log(u_c(t)/u_c(t+1)) + log Π*_{t+1}`, the exponential of the period condition is the
integrand `β(1 + i_t) u_c(t+1)/(u_c(t) Π_{t+1})` of (1.21), `i_t = φ(Π_t/Π*_t; ν_t)`. -/
theorem taylor_exp_identity {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) {A ν Q S u0 u1 : ℝ}
    (hA : 0 < A) (hφ : 0 < 1 + φ (A, ν)) (hQ : 0 < Q) (hS : 0 < S) (hu0 : 0 < u0)
    (hu1 : 0 < u1) :
    expT 1 (LocalIFT.gF (LocalIFT.logRule β φ))
        (Real.log A, Real.log (Q / S), (ν, Real.log (u0 / u1) + Real.log S)) =
      β * (1 + φ (A, ν)) * u1 / (u0 * Q) - 1 := by
  have h : LocalIFT.gF (LocalIFT.logRule β φ)
      (Real.log A, Real.log (Q / S), (ν, Real.log (u0 / u1) + Real.log S)) =
      Real.log (β * (1 + φ (A, ν)) * u1 / (u0 * Q)) := by
    simp only [LocalIFT.gF, LocalIFT.projXN_apply, LocalIFT.leadL_apply, LocalIFT.logRule,
      Real.exp_log hA]
    have e : Real.log (β * (1 + φ (A, ν)) * u1 / (u0 * Q)) =
        Real.log β + Real.log (1 + φ (A, ν)) + Real.log u1 - (Real.log u0 + Real.log Q) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hu1.ne',
        Real.log_mul hβ.ne' hφ.ne', Real.log_mul hu0.ne' hQ.ne']
    rw [e, Real.log_div hQ.ne' hS.ne', Real.log_div hu0.ne' hu1.ne']
    ring
  rw [expT, inv_one, one_mul, h, Real.exp_log (by positivity)]

/-- Woodford (2003), **Proposition 2.6**, p. 91 (with A.3-c, pp. 633–635), **under uncertainty**:
for a Taylor rule `φ` that is `C¹` near the steady state with `1 + φ(1; 0) = β⁻¹` and
`|φ_π| > 1`, for every expectation system there are `ε, δ > 0` and a `C¹` map `X` (derivative at
`0` the linear RE solution, the forward sum (2.7)) such that for all bounded disturbances
`e_t = (ν_t, w_t)` with `‖e‖∞ < δ` (`w_t` may be date-`t+1` measurable), `X(e)` is the unique
bounded adapted solution with `‖x‖∞ < ε` of the exact stochastic Euler equation
`E_t[exp(log β(1 + φ(e^{x_t}; ν_t)) − x_{t+1} − w_t)] = 1` (`taylor_exp_identity`). -/
theorem taylor_local_determinacyS {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hφπ : 1 < |LocalIFT.elast β φ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω (ℝ × ℝ) → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA (LocalIFT.gF (LocalIFT.logRule β φ)))
        (slopeB (LocalIFT.gF (LocalIFT.logRule β φ)))
        (slopeC (LocalIFT.gF (LocalIFT.logRule β φ)))) 0 ∧
      ∀ e : SProc Ω (ℝ × ℝ), ‖e‖ < δ →
        SolvesS 𝔼 (liftII (expT 1 (LocalIFT.gF (LocalIFT.logRule β φ)))) e (X e) ∧
        ‖X e‖ < ε ∧ ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε →
          SolvesS 𝔼 (liftII (expT 1 (LocalIFT.gF (LocalIFT.logRule β φ)))) e x → x = X e := by
  have hg : ContDiffAt ℝ 1 (LocalIFT.logRule β φ) 0 := Nonlinear.contDiffAt_logRule hβ hss hφ
  have hgd : DifferentiableAt ℝ (LocalIFT.logRule β φ) 0 := hg.differentiableAt (by norm_num)
  obtain ⟨hx, -⟩ := LocalIFT.slopes_logRule hβ hss (hφ.differentiableAt (by norm_num))
  have hab := LocalIFT.abs_slopeB_gF_lt hgd (by rw [hx]; exact hφπ)
  exact local_determinacy_expII 𝔼 one_ne_zero (LocalIFT.contDiffAt_gF hg)
    (LocalIFT.gF_zero (LocalIFT.logRule_zero hss)) hab

/-- Woodford (2003), **Proposition 2.6**, p. 91, indeterminacy half, **under uncertainty**: if
`|φ_π| < 1`, the exact stochastic Euler equation has, with no disturbances, a continuum of bounded
adapted solutions arbitrarily close to the steady state. -/
theorem taylor_local_indeterminacyS {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hφπ : |LocalIFT.elast β φ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ x : Proc Ω,
      SolvesS 𝔼 (liftII (expT 1 (LocalIFT.gF (LocalIFT.logRule β φ)))) 0 x ∧ ‖x‖ ≤ ε ∧
        ∀ ω, x (0, ω) = c := by
  have hg : ContDiffAt ℝ 1 (LocalIFT.logRule β φ) 0 := Nonlinear.contDiffAt_logRule hβ hss hφ
  have hgd : DifferentiableAt ℝ (LocalIFT.logRule β φ) 0 := hg.differentiableAt (by norm_num)
  obtain ⟨hx, -⟩ := LocalIFT.slopes_logRule hβ hss (hφ.differentiableAt (by norm_num))
  obtain ⟨ha, hb, -⟩ := LocalIFT.slopes_gF hgd
  have hF := LocalIFT.contDiffAt_gF (n := 1) hg
  have h0 := LocalIFT.gF_zero (LocalIFT.logRule_zero hss (β := β))
  obtain ⟨ha', hb', -⟩ := slopes_expT 1 (hF.differentiableAt (by norm_num)) h0
  refine local_indeterminacyII 𝔼 (contDiffAt_expT 1 hF) (expT_zero 1 h0) ?_
  rw [ha', hb', ha, hb, hx]
  simpa using hφπ

/-- Woodford (2003), (1.36), p. 81: the Wicksellian `gW` is `C¹` at the steady state. -/
theorem contDiffAt_gW {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) : ContDiffAt ℝ 1 (LocalIFT.gW β φ) 0 :=
  (Nonlinear.contDiffAt_logRule hβ hss hφ).add contDiffAt_fst

/-- Woodford (2003), **Proposition 2.3**, p. 82 (proof A.4, pp. 635–637, which appeals to A.3),
**under uncertainty**: for a Wicksellian rule with `φ_p > 0` (`C¹` near the steady state),
the exact stochastic Euler equation `E_t[exp(gW(p_t, ν_t) − p_{t+1} − w_t)] = 1` in
`p_t = log(P_t/P*_t)` (`w_t = r̂_t + π*_{t+1}`) has, for all bounded disturbances `‖e‖∞ < δ`, a
unique bounded adapted solution with `‖p‖∞ < ε`, `C¹` in `e`, with first-order term the linear
RE solution (1.37). -/
theorem wicksell_local_determinacyS {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hφp : 0 < LocalIFT.elast β φ) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω (ℝ × ℝ) → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA (LocalIFT.gF (LocalIFT.gW β φ)))
        (slopeB (LocalIFT.gF (LocalIFT.gW β φ))) (slopeC (LocalIFT.gF (LocalIFT.gW β φ)))) 0 ∧
      ∀ e : SProc Ω (ℝ × ℝ), ‖e‖ < δ →
        SolvesS 𝔼 (liftII (expT 1 (LocalIFT.gF (LocalIFT.gW β φ)))) e (X e) ∧
        ‖X e‖ < ε ∧ ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε →
          SolvesS 𝔼 (liftII (expT 1 (LocalIFT.gF (LocalIFT.gW β φ)))) e x → x = X e := by
  have hg := contDiffAt_gW hβ hss hφ
  have hgd : DifferentiableAt ℝ (LocalIFT.gW β φ) 0 := hg.differentiableAt (by norm_num)
  obtain ⟨hx, -⟩ := LocalIFT.slopes_gW hβ hss (hφ.differentiableAt (by norm_num))
    ((Nonlinear.contDiffAt_logRule hβ hss hφ).differentiableAt (by norm_num))
  have hab := LocalIFT.abs_slopeB_gF_lt hgd (by
    rw [hx, abs_of_pos (by linarith)]
    linarith)
  exact local_determinacy_expII 𝔼 one_ne_zero (LocalIFT.contDiffAt_gF hg)
    (LocalIFT.gF_zero (LocalIFT.gW_zero hss)) hab

/-- Woodford (2003), **Proposition 2.7**, p. 95 (proof A.7, pp. 639–640), **under uncertainty**:
for a rule on smoothed inflation (`0 ≤ δ < 1`, `C¹` near the steady state) with
`|δ + (1 − δ)Φ_π| > 1` (for `0 ≤ δ`, `Φ_π ≥ 0` this is `Φ_π > 1`, `Nonlinear.prop_2_7_cond`), the
exact stochastic Euler equation `E_t[exp(F7(π̄_t, π̄_{t+1}, (ν_t, r̂_t))/(1 − δ))] = 1`
(`log Π_{t+1} = (π̄_{t+1} − δ π̄_t)/(1 − δ)`) has, for all bounded disturbances `‖e‖∞ < δ'`, a
unique bounded adapted solution with `‖π̄‖∞ < ε`, `C¹` in `e`, with first-order term the linear
RE solution (2.10). -/
theorem smooth_local_determinacyS {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hdet : 1 < |dl + (1 - dl) * LocalIFT.elast β φ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω (ℝ × ℝ) → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA (Nonlinear.F7 β dl φ)) (slopeB (Nonlinear.F7 β dl φ))
        (slopeC (Nonlinear.F7 β dl φ))) 0 ∧
      ∀ e : SProc Ω (ℝ × ℝ), ‖e‖ < δ →
        SolvesS 𝔼 (liftII (expT (1 - dl) (Nonlinear.F7 β dl φ))) e (X e) ∧ ‖X e‖ < ε ∧
        ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε →
          SolvesS 𝔼 (liftII (expT (1 - dl) (Nonlinear.F7 β dl φ))) e x → x = X e := by
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F7 (dl := dl) hβ hss hφ
  have hab : |slopeB (Nonlinear.F7 β dl φ)| < |slopeA (Nonlinear.F7 β dl φ)| := by
    rw [ha, hb, abs_neg, abs_one]
    exact hdet
  exact local_determinacy_expII 𝔼 (by linarith : (1 : ℝ) - dl ≠ 0)
    (Nonlinear.contDiffAt_F7 hβ hss hφ) (Nonlinear.F7_zero hss) hab

/-- Woodford (2003), **Proposition 2.7**, p. 95, indeterminacy half, **under uncertainty**: if
`|δ + (1 − δ)Φ_π| < 1` there is a continuum of bounded adapted stochastic equilibria near the
steady state. -/
theorem smooth_local_indeterminacyS {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hind : |dl + (1 - dl) * LocalIFT.elast β φ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ x : Proc Ω,
      SolvesS 𝔼 (liftII (expT (1 - dl) (Nonlinear.F7 β dl φ))) 0 x ∧ ‖x‖ ≤ ε ∧
        ∀ ω, x (0, ω) = c := by
  have hF := Nonlinear.contDiffAt_F7 (dl := dl) (n := 1) hβ hss hφ
  have h0 := Nonlinear.F7_zero (dl := dl) hss
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F7 (dl := dl) hβ hss hφ
  obtain ⟨ha', hb', -⟩ := slopes_expT (1 - dl) (hF.differentiableAt (by norm_num)) h0
  refine local_indeterminacyII 𝔼 (contDiffAt_expT (1 - dl) hF) (expT_zero (1 - dl) h0) ?_
  rw [ha', hb', ha, hb, abs_mul, abs_mul]
  refine mul_lt_mul_of_pos_left ?_ (abs_pos.mpr (inv_ne_zero (by linarith)))
  rw [abs_neg, abs_one]
  exact hind

/-- Woodford (2003), **Proposition 2.8**, p. 96 (proof A.8, pp. 640–641), **under uncertainty**:
for a nonlinear inertial rule `ĵ_t = ψ(π_t, ĵ_{t−1}, ν_t)` (`C¹`, `ψ(0) = 0`, `φ_π ≠ 0`) with
`|φ_π + ρ| > 1` (for `φ_π > 0`, `ρ ≥ 0`: `φ_π + ρ > 1`, (2.13), `Nonlinear.prop_2_8_cond`), the
exact stochastic Euler equation `E_t[exp(ĵ_t − r̂_t − Θ(ĵ_{t+1}, ĵ_t, ν_{t+1}))] = 1` has, for all
bounded disturbances `‖e‖∞ < δ`, a unique bounded adapted solution `ĵ` with `‖ĵ‖∞ < ε`, `C¹` in
`e`, with first-order term the linear RE solution (2.15). -/
theorem inertial_local_determinacyS {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hdet : 1 < |Nonlinear.phiPi ψ + Nonlinear.rhoR ψ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω (ℝ × ℝ) → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA (Nonlinear.F8 ψ hψ hφ)) (slopeB (Nonlinear.F8 ψ hψ hφ))
        (slopeC (Nonlinear.F8 ψ hψ hφ))) 0 ∧
      ∀ e : SProc Ω (ℝ × ℝ), ‖e‖ < δ →
        SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F8 ψ hψ hφ))) e (X e) ∧ ‖X e‖ < ε ∧
        ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε →
          SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F8 ψ hψ hφ))) e x → x = X e := by
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F8 hψ hφ h0
  have hab : |slopeB (Nonlinear.F8 ψ hψ hφ)| < |slopeA (Nonlinear.F8 ψ hψ hφ)| := by
    rw [ha, hb]
    exact (Nonlinear.inertial_slope_iff hφ).mpr hdet
  exact local_determinacy_expII 𝔼 one_ne_zero (Nonlinear.contDiffAt_F8 hψ hφ h0 hψ)
    (Nonlinear.F8_zero hψ hφ h0) hab

/-- Woodford (2003), **Proposition 2.8**, p. 96, indeterminacy half, **under uncertainty**: if
`|φ_π + ρ| < 1` there is a continuum of bounded adapted stochastic equilibria near the steady
state. -/
theorem inertial_local_indeterminacyS {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hind : |Nonlinear.phiPi ψ + Nonlinear.rhoR ψ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ x : Proc Ω,
      SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F8 ψ hψ hφ))) 0 x ∧ ‖x‖ ≤ ε ∧
        ∀ ω, x (0, ω) = c := by
  have hF := Nonlinear.contDiffAt_F8 hψ hφ h0 (n := 1) hψ
  have hz := Nonlinear.F8_zero hψ hφ h0
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F8 hψ hφ h0
  obtain ⟨ha', hb', -⟩ := slopes_expT 1 (hF.differentiableAt (by norm_num)) hz
  refine local_indeterminacyII 𝔼 (contDiffAt_expT 1 hF) (expT_zero 1 hz) ?_
  rw [ha', hb', ha, hb, inv_one, one_mul, one_mul]
  exact (Nonlinear.inertial_slope_iff' hφ).mpr hind

/-- Woodford (2003), (3.3) and (1.21), pp. 71, 104, A.11 p. 644, **money-growth Euler equation
under uncertainty**: `(1 − R_t) e^{x_t} − β(1 + īᵐ) e^{x_{t+1} − w_t}`, i.e. `e^{−w}` times
`Nonlinear.FMG`; `E_t[·] = 0` is `(1 − Δ_t) u_c(t)/P_t = β(1 + iᵐ_t) E_t[u_c(t+1)/P_{t+1}]` in
`x = log(M/(P m̄))`, `w_t = r̂_t + μ_{t+1} − îᵐ_t`. -/
noncomputable def FMGS (β ibm Ybar mbar : ℝ) (R : ℝ × ℝ × ℝ → ℝ)
    (p : ℝ × ℝ × (ℝ × ℝ × ℝ)) : ℝ :=
  Real.exp (-p.2.2.2.2) * Nonlinear.FMG β ibm Ybar mbar R p

/-- Woodford (2003), **Proposition 2.11**, p. 107 (proof A.11, pp. 644–645), **under
uncertainty**: under money-growth targeting with `∂(u_m/u_c)/∂m < 0` at the steady state
(`C¹` near it), the exact stochastic Euler equation `E_t[FMGS(x_t, x_{t+1}, e_t)] = 0` has, for all
bounded disturbances `‖e‖∞ < δ`, a unique bounded adapted solution with `‖x‖∞ < ε`, `C¹` in `e`,
with first-order term the linear RE solution (A.30). -/
theorem mg_local_determinacyS {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hibm : 0 < 1 + ibm) (hm : 0 < mbar) (hR : ContDiffAt ℝ 1 R (Ybar, mbar, 0))
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm))
    (hRm : fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) < 0) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω (ℝ × ℝ × ℝ) → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA (Nonlinear.FMG β ibm Ybar mbar R))
        (slopeB (Nonlinear.FMG β ibm Ybar mbar R)) (slopeC (Nonlinear.FMG β ibm Ybar mbar R))) 0 ∧
      ∀ e : SProc Ω (ℝ × ℝ × ℝ), ‖e‖ < δ →
        SolvesS 𝔼 (liftII (FMGS β ibm Ybar mbar R)) e (X e) ∧ ‖X e‖ < ε ∧
        ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε →
          SolvesS 𝔼 (liftII (FMGS β ibm Ybar mbar R)) e x → x = X e := by
  have hF : ContDiffAt ℝ 1 (Nonlinear.FMG β ibm Ybar mbar R) 0 := Nonlinear.contDiffAt_FMG hR
  have hz : Nonlinear.FMG β ibm Ybar mbar R 0 = 0 := Nonlinear.FMG_zero hss
  have hmc : ContDiffAt ℝ 1 (fun p : ℝ × ℝ × (ℝ × ℝ × ℝ) => Real.exp (-p.2.2.2.2)) 0 := by
    fun_prop
  have hG : ContDiffAt ℝ 1 (FMGS β ibm Ybar mbar R) 0 := hmc.mul hF
  have hG0 : FMGS β ibm Ybar mbar R 0 = 0 := by rw [FMGS, hz, mul_zero]
  have hd : fderiv ℝ (FMGS β ibm Ybar mbar R) 0 =
      fderiv ℝ (Nonlinear.FMG β ibm Ybar mbar R) 0 :=
    fderiv_mul_unit (hF.differentiableAt (by norm_num)) (hmc.differentiableAt (by norm_num)) hz
      (by simp)
  have hsa : slopeA (FMGS β ibm Ybar mbar R) = slopeA (Nonlinear.FMG β ibm Ybar mbar R) := by
    rw [slopeA, hd, slopeA]
  have hsb : slopeB (FMGS β ibm Ybar mbar R) = slopeB (Nonlinear.FMG β ibm Ybar mbar R) := by
    rw [slopeB, hd, slopeB]
  have hsc : slopeC (FMGS β ibm Ybar mbar R) = slopeC (Nonlinear.FMG β ibm Ybar mbar R) := by
    rw [slopeC, hd, slopeC]
  have hab := Nonlinear.mg_slope_cond hβ hibm hm (hR.differentiableAt (by norm_num)) hss hRm
  rw [← hsa, ← hsb] at hab
  obtain ⟨ε, hε, δ, hδ, X, hX0, hXd, hX⟩ := local_determinacyII 𝔼 hG hG0 hab
  refine ⟨ε, hε, δ, hδ, X, hX0, ?_, hX⟩
  rw [hsa, hsb, hsc] at hXd
  exact hXd

/-- Woodford (2003), **Proposition 2.12**, p. 115 (proof A.12, pp. 645–646), **under
uncertainty**: for a Wicksellian rule with non-separable utility, under the exact condition
`|B| < |A|` of (A.32) (implied by (3.16) and `φ_p > 0`, `NonSeparable.abs_B_lt_A`), the exact
stochastic Euler equation `E_t[exp(FW(p_t, p_{t+1}, e_t))] = 1`
(`E_t[β(1 + i_t) u_c(t+1) P_t/(u_c(t) P_{t+1})] = 1` with money demand (3.5)) has, for all bounded
disturbances `‖e‖∞ < δ`, a unique bounded adapted solution with `‖p‖∞ < ε`, `C¹` in `e`, with
first-order term the linear RE solution (3.17). -/
theorem nsw_local_determinacyS {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ}
    {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hAB : |NonSeparable.B212 (Nonlinear.etaNS β ibm mbar Ybar L) (Nonlinear.chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.A212 (Nonlinear.etaNS β ibm mbar Ybar L)
        (Nonlinear.chiNS Ybar mbar Uc) (LocalIFT.elast β φ)|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ) → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA (Nonlinear.FW β ibm Ybar φ L Uc))
        (slopeB (Nonlinear.FW β ibm Ybar φ L Uc)) (slopeC (Nonlinear.FW β ibm Ybar φ L Uc))) 0 ∧
      ∀ e : SProc Ω ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ), ‖e‖ < δ →
        SolvesS 𝔼 (liftII (expT 1 (Nonlinear.FW β ibm Ybar φ L Uc))) e (X e) ∧ ‖X e‖ < ε ∧
        ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε →
          SolvesS 𝔼 (liftII (expT 1 (Nonlinear.FW β ibm Ybar φ L Uc))) e x → x = X e := by
  obtain ⟨ha, hb⟩ := Nonlinear.slopes_FW hβ hm hss hφ hL hLss hU hUpos
  have hab : |slopeB (Nonlinear.FW β ibm Ybar φ L Uc)| <
      |slopeA (Nonlinear.FW β ibm Ybar φ L Uc)| := by
    rw [ha, hb, abs_neg]
    exact hAB
  exact local_determinacy_expII 𝔼 one_ne_zero
    (Nonlinear.contDiffAt_FW hβ hss hφ hL hLss hU hUpos) (Nonlinear.FW_zero hss) hab

/-- Woodford (2003), **Proposition 2.12**, p. 115, indeterminacy half, **under uncertainty**: if
`|A| < |B|` there is a continuum of bounded adapted stochastic equilibria near the steady
state. -/
theorem nsw_local_indeterminacyS {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ}
    {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hBA : |NonSeparable.A212 (Nonlinear.etaNS β ibm mbar Ybar L) (Nonlinear.chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.B212 (Nonlinear.etaNS β ibm mbar Ybar L)
        (Nonlinear.chiNS Ybar mbar Uc) (LocalIFT.elast β φ)|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ x : Proc Ω,
      SolvesS 𝔼 (liftII (expT 1 (Nonlinear.FW β ibm Ybar φ L Uc))) 0 x ∧ ‖x‖ ≤ ε ∧
        ∀ ω, x (0, ω) = c := by
  have hF := Nonlinear.contDiffAt_FW (n := 1) hβ hss hφ hL hLss hU hUpos
  have hz := Nonlinear.FW_zero (ibm := ibm) (Ybar := Ybar) (L := L) (Uc := Uc) hss
  obtain ⟨ha, hb⟩ := Nonlinear.slopes_FW hβ hm hss hφ hL hLss hU hUpos
  obtain ⟨ha', hb', -⟩ := slopes_expT 1 (hF.differentiableAt (by norm_num)) hz
  refine local_indeterminacyII 𝔼 (contDiffAt_expT 1 hF) (expT_zero 1 hz) ?_
  rw [ha', hb', ha, hb, inv_one, one_mul, one_mul, abs_neg]
  exact hBA

/-- Woodford (2003), **Proposition 2.13**, p. 116 (proof A.13, p. 646), **under uncertainty**:
for a nonlinear inertial rule with non-separable utility under `|γ₁| < |γ₀|` (implied by
(3.16), `φ_π > 0`, `ρ ≥ 0`, `φ_π + ρ > 1`: `Nonlinear.prop_2_13_cond`), the exact stochastic Euler
equation `E_t[exp(F13(ĵ_t, ĵ_{t+1}, e_t))] = 1` has, for all bounded disturbances `‖e‖∞ < δ`, a
unique bounded adapted solution with `‖ĵ‖∞ < ε`, `C¹` in `e`, with first-order term the linear RE
solution (3.20). -/
theorem nsi_local_determinacyS {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hm : 0 < mbar)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma1 (Nonlinear.etaNS β ibm mbar Ybar L)
      (Nonlinear.chiNS Ybar mbar Uc) (Nonlinear.phiPi ψ)| <
      |NonSeparable.gamma0 (Nonlinear.etaNS β ibm mbar Ybar L) (Nonlinear.chiNS Ybar mbar Uc)
        (Nonlinear.phiPi ψ) (Nonlinear.rhoR ψ)|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : SProc Ω ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) → Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (slopeA (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))
        (slopeB (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))
        (slopeC (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))) 0 ∧
      ∀ e : SProc Ω ((ℝ × ℝ) × (ℝ × ℝ) × ℝ), ‖e‖ < δ →
        SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))) e (X e) ∧
        ‖X e‖ < ε ∧ ContDiffAt ℝ 1 X e ∧ ∀ x : Proc Ω, ‖x‖ < ε →
          SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))) e x → x = X e := by
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F13 hψ hφ h0 hm hL hLss hU hUpos
  have hab : |slopeB (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ)| <
      |slopeA (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ)| :=
    (Nonlinear.gamma_slope_iff hφ ha hb).mpr hγ
  exact local_determinacy_expII 𝔼 one_ne_zero
    (Nonlinear.contDiffAt_F13 hψ hφ h0 hψ hL hLss hU hUpos) (Nonlinear.F13_zero hψ hφ h0) hab

/-- Woodford (2003), **Proposition 2.13**, p. 116, indeterminacy half, **under uncertainty**: if
`|γ₀| < |γ₁|` there is a continuum of bounded adapted stochastic equilibria near the steady
state. -/
theorem nsi_local_indeterminacyS {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hm : 0 < mbar)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma0 (Nonlinear.etaNS β ibm mbar Ybar L)
      (Nonlinear.chiNS Ybar mbar Uc) (Nonlinear.phiPi ψ) (Nonlinear.rhoR ψ)| <
      |NonSeparable.gamma1 (Nonlinear.etaNS β ibm mbar Ybar L) (Nonlinear.chiNS Ybar mbar Uc)
        (Nonlinear.phiPi ψ)|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ x : Proc Ω,
      SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))) 0 x ∧ ‖x‖ ≤ ε ∧
        ∀ ω, x (0, ω) = c := by
  have hF := Nonlinear.contDiffAt_F13 (n := 1) hψ hφ h0 hψ hL hLss hU hUpos
  have hz := Nonlinear.F13_zero (β := β) (ibm := ibm) (Ybar := Ybar) (L := L) (Uc := Uc) hψ hφ h0
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F13 hψ hφ h0 hm hL hLss hU hUpos
  obtain ⟨ha', hb', -⟩ := slopes_expT 1 (hF.differentiableAt (by norm_num)) hz
  refine local_indeterminacyII 𝔼 (contDiffAt_expT 1 hF) (expT_zero 1 hz) ?_
  rw [ha', hb', inv_one, one_mul, one_mul]
  have hpos : 0 < |Nonlinear.phiPi ψ| := abs_pos.mpr hφ
  rw [ha, hb, abs_neg, abs_div, abs_div]
  exact div_lt_div_of_pos_right hγ hpos

end Models


end Woodford.PriceLevelDetermination.LocalIFTStochastic
