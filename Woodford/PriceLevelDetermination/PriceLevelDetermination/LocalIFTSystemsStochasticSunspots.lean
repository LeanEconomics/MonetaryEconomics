/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFTSystemsStochastic
import PriceLevelDetermination.LocalIFTStochasticModels

/-!
# Random sunspot equilibria of nonlinear `n`-dimensional systems

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 632–634 (indeterminacy). When the
operator (A.8) of the linearisation of `E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0` is onto but not
one-to-one (too many stable roots, or genericity failure, without a unit root), the exact
nonlinear model has **genuinely random** bounded adapted equilibria on the core two-coin tree,
arbitrarily close to the steady state, with no fundamental shocks and `x_{−1} = x̄`. This
generalises `LocalIFTSystemsStochasticApps.inertial_random_sunspot` to any `C¹` condition.

## Construction

Look for equilibria of the form `x_0 = c` (deterministic) and, from date 1 on, one of two
perfect-foresight paths `y⁺`, `y⁻` according to the first coin flip. Such an `x` is an equilibrium
iff each branch solves the perfect-foresight conditions from the initial condition `c`, and the
date-0 condition holds on average:
`½ [G(0, c, y⁺_0, 0) + G(0, c, y⁻_0, 0)] = 0` (`branchMap`). Its derivative at `0` (`branchD`) is
onto when (A.8) is onto (`range_branchD`), and its kernel is finite-dimensional because the
pencil is regular (`finiteDimensional_ker_branchD`), hence complemented; the kernel contains the
antisymmetric direction `(0, k, −k)` for a nonzero kernel element `k` of (A.8). The implicit
function theorem with complemented kernel (Mathlib's `implicitFunctionOfComplemented`) gives a
curve of solutions tangent to `(0, k, −k)`, whose two branches differ at date 1.

## Main results

* `random_sunspot_nonlinear` (**the theorem**): `G` `C¹` near the steady state, `G(0) = 0`, (A.8)
  onto and not one-to-one ⟹ for every `ε > 0`, a bounded adapted equilibrium on the coin tree
  with `‖x‖ ≤ ε`, deterministic at date 0, whose date-1 value differs across the first flip.
* `random_sunspot_of_count_gt`: the same when more than `n` roots of `det(f₃λ² + f₂λ + f₁)` lie
  inside the unit circle and (A.8) is onto.
* `random_sunspot_of_opS`: the hypotheses stated for the stochastic operator (A.12) of any
  expectation system on a nonempty state space.

**On the extra hypothesis "(A.8) onto".** Non-injectivity alone does not suffice for this
argument: without surjectivity the linearised map has no right inverse and the implicit-function
theorem is unavailable (and existence can fail outright: a root on the unit circle destroys
existence, `LinearSystemsUnit.not_surjective_of_unit_root`). Surjectivity is the same hypothesis
as in the perfect-foresight non-uniqueness theorem `LocalIFTSystems.not_locally_unique`; it
excludes unit roots and singular pencils and gives the regularity used for the kernel. The
condition on `D₄G` is not needed (no disturbances are used).
-/

namespace Woodford.PriceLevelDetermination.LocalIFTSystemsStochasticSunspots

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic
open LocalIFTSystems (Arg Par Solves eqMap linOp bOp eqD0 d1 d2 d3 dE M1 M2 M3
  fderiv_zero_apply4 cutoff cutoff_eq contDiff_cutoff exists_ball_contDiffAt lin_cutoff
  solves_cutoff_iff eqMap_eq_zero_iff hasStrictFDerivAt_nem nemD_zero ptL norm_ptL_le linOp_apply
  bOp_apply impOp impOp_apply)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Woodford (2003), App. A.3, p. 634: the unknowns of the two-branch sunspot problem, the
date-0 value `c` and the two continuation paths `y⁺`, `y⁻`. -/
abbrev Br (ι : Type*) [Fintype ι] : Type _ := (ι → ℝ) × SeqV ι × SeqV ι

/-- Woodford (2003), App. A.3, p. 634 (tool): the date-0 value of a sequence as a continuous
linear map. -/
noncomputable def ev0 : SeqV ι →L[ℝ] (ι → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun y => y 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun y => by rw [one_mul]; exact LocalIFT.norm_seq_apply_le y 0)

/-- Woodford (2003), App. A.3, p. 634: the date-0 argument `(0, c, y_0, 0)` along branch `b`. -/
noncomputable def arg0 (b : Bool) : Br ι →L[ℝ] Arg ι E :=
  (0 : Br ι →L[ℝ] (ι → ℝ)).prod ((ContinuousLinearMap.fst ℝ (ι → ℝ) (SeqV ι × SeqV ι)).prod
    ((ev0.comp (if b then (ContinuousLinearMap.fst ℝ (SeqV ι) (SeqV ι)).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (SeqV ι × SeqV ι))
      else (ContinuousLinearMap.snd ℝ (SeqV ι) (SeqV ι)).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (SeqV ι × SeqV ι)))).prod (0 : Br ι →L[ℝ] E)))

/-- Woodford (2003), App. A.3, p. 634: the perfect-foresight problem of branch `b`,
`((c, 0), y^b)`. -/
noncomputable def parB (b : Bool) : Br ι →L[ℝ] Par ι E × SeqV ι :=
  ((ContinuousLinearMap.fst ℝ (ι → ℝ) (SeqV ι × SeqV ι)).prod
    (0 : Br ι →L[ℝ] LocalIFT.Seq E)).prod
    (if b then (ContinuousLinearMap.fst ℝ (SeqV ι) (SeqV ι)).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (SeqV ι × SeqV ι))
      else (ContinuousLinearMap.snd ℝ (SeqV ι) (SeqV ι)).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (SeqV ι × SeqV ι)))

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): values of `arg0`. -/
theorem arg0_apply (q : Br ι) :
    arg0 (E := E) true q = (0, q.1, q.2.1 0, 0) ∧ arg0 (E := E) false q = (0, q.1, q.2.2 0, 0) :=
  ⟨rfl, rfl⟩

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): values of `parB`. -/
theorem parB_apply (q : Br ι) :
    parB (E := E) true q = ((q.1, 0), q.2.1) ∧ parB (E := E) false q = ((q.1, 0), q.2.2) :=
  ⟨rfl, rfl⟩

/-- Woodford (2003), App. A.3, p. 634: **the two-branch sunspot map**: the averaged date-0
condition and the perfect-foresight conditions of both branches (`G` in the cut-off form). -/
noncomputable def branchMap (F : Arg ι E → (ι → ℝ)) (hF : Continuous F) (q : Br ι) : Br ι :=
  ((1 / 2 : ℝ) • (F (arg0 true q) + F (arg0 false q)),
    eqMap F hF (parB true q), eqMap F hF (parB false q))

/-- Woodford (2003), App. A.3, p. 634: the derivative of the two-branch map at `0`. -/
noncomputable def branchD (F : Arg ι E → (ι → ℝ)) : Br ι →L[ℝ] Br ι :=
  ((1 / 2 : ℝ) • ((fderiv ℝ F 0).comp (arg0 true) + (fderiv ℝ F 0).comp (arg0 false))).prod
    (((eqD0 F).comp (parB true)).prod ((eqD0 F).comp (parB false)))

/-- Woodford (2003), App. A.3, p. 634: the two-branch map is strictly differentiable at `0`. -/
theorem hasStrictFDerivAt_branchMap {F : Arg ι E → (ι → ℝ)} (hF : ContDiff ℝ 1 F) :
    HasStrictFDerivAt (branchMap F hF.continuous) (branchD F) 0 := by
  have h0 : ∀ b : Bool, HasStrictFDerivAt (fun q : Br ι => F (arg0 b q))
      ((fderiv ℝ F 0).comp (arg0 b)) 0 := by
    intro b
    have hs : HasStrictFDerivAt F (fderiv ℝ F 0) (arg0 (E := E) b (0 : Br ι)) := by
      rw [map_zero]
      exact hF.contDiffAt.hasStrictFDerivAt one_ne_zero
    exact hs.comp (0 : Br ι) ((arg0 (E := E) b).hasStrictFDerivAt (x := (0 : Br ι)))
  have hE : ∀ b : Bool, HasStrictFDerivAt (fun q : Br ι => eqMap F hF.continuous (parB b q))
      ((eqD0 F).comp (parB b)) 0 := by
    intro b
    have hn := hasStrictFDerivAt_nem hF ptL norm_ptL_le (0 : Par ι E × SeqV ι)
    rw [nemD_zero hF] at hn
    have hn' : HasStrictFDerivAt (eqMap F hF.continuous) (eqD0 F) (parB (E := E) b (0 : Br ι)) := by
      rw [map_zero]; exact hn
    exact hn'.comp (0 : Br ι) ((parB (E := E) b).hasStrictFDerivAt (x := (0 : Br ι)))
  exact (((h0 true).add (h0 false)).const_smul (1 / 2 : ℝ)).prodMk ((hE true).prodMk (hE false))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632 (tool): `eqD0` at `((v_0, 0), (v_{t+1})_t)` is the lead
of `(A.8) v`. -/
theorem eqD0_lead (F : Arg ι E → (ι → ℝ)) (v : SeqV ι) :
    eqD0 F ((v 0, 0), leadOp (ι → ℝ) v) = leadOp (ι → ℝ) (linOp F v) := by
  refine seq_ext fun t => ?_
  change linOp F (leadOp (ι → ℝ) v) t + bOp F (v 0, 0) t = linOp F v (t + 1)
  rw [linOp_apply, linOp_apply, bOp_apply]
  have h : lagV 0 (fun s => leadOp (ι → ℝ) v s) t + lagV (v 0) 0 t =
      lagV 0 (fun s => v s) (t + 1) := by
    cases t <;> simp
  rw [← h, map_add, show ((0 : LocalIFT.Seq E) t) = 0 from rfl, map_zero, add_zero]
  change d1 F _ + d2 F (v (t + 1)) + d3 F (v (t + 1 + 1)) + d1 F _ = _
  abel

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632 (tool): with `x_{−1} = 0` and no disturbances the
derivative is the operator (A.8). -/
theorem eqD0_zeroPar (F : Arg ι E → (ι → ℝ)) (y : SeqV ι) :
    eqD0 F ((0, 0), y) = linOp F y := by
  change linOp F y + bOp F 0 = linOp F y
  rw [map_zero, add_zero]

omit [DecidableEq ι] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632 (tool): the impulse has zero lead. -/
theorem leadOp_impOp (w : ι → ℝ) : leadOp (ι → ℝ) (impOp ι w) = 0 :=
  seq_ext fun t => by simp

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632 (tool): the derivative at the steady state on the date-0
argument `(0, c, y, 0)`. -/
theorem fderiv_arg0 (F : Arg ι E → (ι → ℝ)) (c y : ι → ℝ) :
    fderiv ℝ F 0 ((0, c, y, 0) : Arg ι E) = d2 F c + d3 F y := by
  rw [fderiv_zero_apply4, map_zero, map_zero, zero_add, add_zero]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: **the two-branch derivative is onto when (A.8) is onto**
(solve each branch with (A.8), then correct the averaged date-0 condition with the date-0 value
of a solution of (A.8) for an impulse forcing). -/
theorem range_branchD {F : Arg ι E → (ι → ℝ)} (hs : Function.Surjective (linOp F)) :
    (branchD F).range = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun target => ?_
  obtain ⟨r, a₁, a₂⟩ := target
  obtain ⟨q₁, hq₁⟩ := hs a₁
  obtain ⟨q₂, hq₂⟩ := hs a₂
  set r₀ : ι → ℝ := (1 / 2 : ℝ) • (d3 F (q₁ 0) + d3 F (q₂ 0)) with hr₀
  obtain ⟨v, hv⟩ := hs (impOp ι (r - r₀))
  have hv0 : d2 F (v 0) + d3 F (v 1) = r - r₀ := by
    have := congrArg (fun y : SeqV ι => y 0) hv
    simp only [linOp_apply, impOp_apply, lagV_zero] at this
    rw [map_zero, zero_add] at this
    exact this
  refine ⟨(v 0, q₁ + leadOp (ι → ℝ) v, q₂ + leadOp (ι → ℝ) v), ?_⟩
  have hb : ∀ (q a : SeqV ι), linOp F q = a →
      eqD0 F ((v 0, 0), q + leadOp (ι → ℝ) v) = a := by
    intro q a hq
    have e : (((v 0, 0), q + leadOp (ι → ℝ) v) : Par ι E × SeqV ι) =
        ((0, 0), q) + ((v 0, 0), leadOp (ι → ℝ) v) := by simp
    rw [e, map_add, eqD0_zeroPar, eqD0_lead, hv, leadOp_impOp, hq, add_zero]
  refine Prod.ext ?_ (Prod.ext (hb q₁ a₁ hq₁) (hb q₂ a₂ hq₂))
  change (1 / 2 : ℝ) • (fderiv ℝ F 0 ((0, v 0, (q₁ + leadOp (ι → ℝ) v) 0, 0) : Arg ι E) +
    fderiv ℝ F 0 ((0, v 0, (q₂ + leadOp (ι → ℝ) v) 0, 0) : Arg ι E)) = r
  rw [fderiv_arg0, fderiv_arg0]
  funext i
  have h1 := congrFun hv0 i
  simp only [hr₀, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lp.coeFn_add,
    leadOp_apply, map_add] at h1 ⊢
  linarith

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632 (tool): when (A.8) is onto, a nonzero element of its
kernel is nonzero at date 0 (the pencil is regular). -/
theorem kernel_ne_zero_at_zero {F : Arg ι E → (ι → ℝ)} (hs : Function.Surjective (linOp F))
    {k : SeqV ι} (hk : linOp F k = 0) (hk0 : k ≠ 0) : k 0 ≠ 0 := by
  intro h
  have hreg := quadPoly_ne_zero_of_surjective (f₁ := M1 F) (f₂ := M2 F) (f₃ := M3 F) hs
  have hsol : SolvesLin (M1 F) (M2 F) (M3 F) 0 0 (fun t => k t) := by
    intro t
    have := (sysOp_eq_iff _ _ _ _ _).mp hk t
    simpa using this
  exact hk0 (seq_ext fun t => congrFun (eq_zero_of_regular hreg (boundedSeq_coe k) hsol h) t)

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: when (A.8) is onto, **the kernel of the two-branch
derivative is finite-dimensional** (an element is determined by `(c, y⁺_0, y⁻_0)`, by
regularity of the pencil). -/
theorem finiteDimensional_ker_branchD {F : Arg ι E → (ι → ℝ)}
    (hs : Function.Surjective (linOp F)) : FiniteDimensional ℝ (branchD F).ker := by
  have hreg := quadPoly_ne_zero_of_surjective (f₁ := M1 F) (f₂ := M2 F) (f₃ := M3 F) hs
  let ev : (branchD F).ker →ₗ[ℝ] (ι → ℝ) × (ι → ℝ) × (ι → ℝ) :=
    { toFun := fun κ => ((κ : Br ι).1, (κ : Br ι).2.1 0, (κ : Br ι).2.2 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro κ hκ
    have h1 : (κ : Br ι).1 = 0 := congrArg Prod.fst hκ
    have h2 : (κ : Br ι).2.1 0 = 0 := congrArg (fun q => q.2.1) hκ
    have h3 : (κ : Br ι).2.2 0 = 0 := congrArg (fun q => q.2.2) hκ
    have hD : branchD F (κ : Br ι) = 0 := LinearMap.mem_ker.mp κ.2
    have hb : ∀ y : SeqV ι, eqD0 F (((κ : Br ι).1, 0), y) = 0 → y 0 = 0 → y = 0 := by
      intro y hy hy0
      rw [h1, eqD0_zeroPar] at hy
      have hsol : SolvesLin (M1 F) (M2 F) (M3 F) 0 0 (fun t => y t) := by
        intro t
        have := (sysOp_eq_iff _ _ _ _ _).mp hy t
        simpa using this
      exact seq_ext fun t => congrFun (eq_zero_of_regular hreg (boundedSeq_coe y) hsol hy0) t
    have hy1 := hb _ (congrArg (fun q => q.2.1) hD) h2
    have hy2 := hb _ (congrArg (fun q => q.2.2) hD) h3
    exact Subtype.ext (Prod.ext h1 (Prod.ext hy1 hy2))
  exact Module.Finite.of_injective ev hinj

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: **the antisymmetric direction `(0, k, −k)` lies in the
kernel** of the two-branch derivative for every `k` in the kernel of (A.8). -/
theorem branchD_anti {F : Arg ι E → (ι → ℝ)} {k : SeqV ι} (hk : linOp F k = 0) :
    branchD F ((0, k, -k) : Br ι) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (1 / 2 : ℝ) • (fderiv ℝ F 0 ((0, 0, k 0, 0) : Arg ι E) +
      fderiv ℝ F 0 ((0, 0, (-k) 0, 0) : Arg ι E)) = 0
    rw [fderiv_arg0, fderiv_arg0, lp.coeFn_neg, Pi.neg_apply, map_neg]
    simp
  · change eqD0 F ((0, 0), k) = 0
    rw [eqD0_zeroPar, hk]
  · change eqD0 F ((0, 0), -k) = 0
    rw [eqD0_zeroPar, map_neg, hk, neg_zero]

set_option maxHeartbeats 1600000 in
-- the proof unfolds the coin-tree processes and the cut-off conditions definitionally
/-- **Genuinely random sunspot equilibria of nonlinear `n`-dimensional systems** (Woodford
(2003), App. A.3, pp. 632–634, indeterminacy, under uncertainty): if `G` is `C¹` near the steady
state, `G(0) = 0`, and the operator (A.8) of its linearisation is onto but not one-to-one, then
on the core two-coin tree, for every `ε > 0`, the book-form conditions
`E_t[G(x_{t−1}, x_t, x_{t+1}, 0)] = 0` with `x_{−1} = x̄` have a bounded adapted solution with
`‖x‖ ≤ ε`, deterministic at date 0, whose date-1 value differs across the first coin flip. -/
theorem random_sunspot_nonlinear {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (h0 : G 0 = 0) (hs : Function.Surjective (linOp G)) (hni : ¬ Function.Injective (linOp G))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV ι (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem G 0 x ∧ ‖x‖ ≤ ε ∧
      (∀ ω ω', x (0, ω) = x (0, ω')) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt hG
  set F := cutoff G r hr with hFdef
  have hF1 : ContDiff ℝ 1 F := contDiff_cutoff hr hball
  obtain ⟨hlo, -, -⟩ := lin_cutoff G hr
  have hF0 : F 0 = 0 := by rw [hFdef, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  have hsF : Function.Surjective (linOp F) := by rw [hlo]; exact hs
  have hniF : ¬ Function.Injective (linOp F) := by rw [hlo]; exact hni
  obtain ⟨k, hk0, hk⟩ : ∃ k : SeqV ι, k ≠ 0 ∧ linOp F k = 0 := by
    simp only [Function.Injective, not_forall] at hniF
    obtain ⟨a, b, hab, hne⟩ := hniF
    exact ⟨a - b, sub_ne_zero.mpr hne, by rw [map_sub, hab, sub_self]⟩
  have hk00 : k 0 ≠ 0 := kernel_ne_zero_at_zero hsF hk hk0
  have hkn : 0 < ‖k 0‖ := norm_pos_iff.mpr hk00
  have hf := hasStrictFDerivAt_branchMap hF1
  have hrange := range_branchD hsF
  have := finiteDimensional_ker_branchD hsF
  have hker : (branchD F).ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional _
  set κ : (branchD F).ker := ⟨((0, k, -k) : Br ι), branchD_anti hk⟩ with hκ
  set g := hf.implicitFunctionOfComplemented (branchMap F hF1.continuous) (branchD F) hrange hker
    with hgdef
  set f0 := branchMap F hF1.continuous 0 with hf0def
  have hf0 : f0 = 0 := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change (1 / 2 : ℝ) • (F (arg0 true (0 : Br ι)) + F (arg0 false (0 : Br ι))) = 0
      rw [map_zero, map_zero, hF0, add_zero, smul_zero]
    · change eqMap F hF1.continuous (parB true (0 : Br ι)) = 0
      rw [map_zero, eqMap_eq_zero_iff]
      exact LocalIFTSystems.solves_zero hF0
    · change eqMap F hF1.continuous (parB false (0 : Br ι)) = 0
      rw [map_zero, eqMap_eq_zero_iff]
      exact LocalIFTSystems.solves_zero hF0
  set h : ℝ → Br ι := fun s => g f0 (s • κ) with hh
  have hg0 : g f0 0 = 0 := hf.implicitFunctionOfComplemented_apply_image hrange hker
  have hh0 : h 0 = 0 := by simp only [hh, zero_smul, hg0]
  have hderiv : HasDerivAt h (κ : Br ι) 0 := by
    have hs' := (hf.to_implicitFunctionOfComplemented hrange hker).hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => s • κ) κ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const κ
    have hs'' : HasFDerivAt (g f0) (branchD F).ker.subtypeL ((fun s : ℝ => s • κ) 0) := by
      simpa using hs'
    exact (hs''.comp_hasDerivAt (0 : ℝ) hline).congr_deriv rfl
  have hsol : ∀ᶠ s in 𝓝 (0 : ℝ), branchMap F hF1.continuous (h s) = 0 := by
    have hmap := hf.map_implicitFunctionOfComplemented_eq hrange hker
    have ht : Filter.Tendsto (fun s : ℝ => (f0, s • κ)) (𝓝 0) (𝓝 (f0, 0)) := by
      have hc : Continuous (fun s : ℝ => (f0, s • κ)) :=
        continuous_const.prodMk (continuous_id.smul continuous_const)
      simpa using hc.tendsto 0
    filter_upwards [ht.eventually hmap] with s hs
    rw [← hf0]
    exact hs
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), ‖h s‖ < min (r / 4) ε := by
    have ht := hderiv.continuousAt.tendsto
    rw [hh0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds (0 : Br ι)
      (lt_min (by positivity : (0 : ℝ) < r / 4) hε))).mono
        (fun s hs => by rwa [dist_zero_right] at hs)
  have hclose : ∀ᶠ s in 𝓝 (0 : ℝ), ‖h s - s • (κ : Br ι)‖ ≤ (‖k 0‖ / 2) * ‖s‖ := by
    have hl := (hasDerivAt_iff_isLittleO.mp hderiv).def (by positivity : (0 : ℝ) < ‖k 0‖ / 2)
    filter_upwards [hl] with s hs
    simp only [hh0, sub_zero] at hs
    exact hs
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp (hsol.and (hsmall.and hclose))
  set s : ℝ := ρ / 2 with hsdef
  have hs0 : 0 < s := by positivity
  obtain ⟨hs1, hs2, hs3⟩ := hρP (show dist s 0 < ρ by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hs0]
    linarith)
  set p := h s with hp
  set c := p.1 with hc
  set y₁ := p.2.1 with hy₁
  set y₂ := p.2.2 with hy₂
  have hpr : ‖p‖ ≤ r / 4 := hs2.le.trans (min_le_left _ _)
  have hpε : ‖p‖ ≤ ε := hs2.le.trans (min_le_right _ _)
  have hcn : ‖c‖ ≤ ‖p‖ := norm_fst_le p
  have hy₁n : ‖y₁‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
  have hy₂n : ‖y₂‖ ≤ ‖p‖ := (norm_snd_le p.2).trans (norm_snd_le p)
  -- the branches solve the exact conditions
  have hbr : ∀ y : SeqV ι, ‖y‖ ≤ ‖p‖ → eqMap F hF1.continuous ((c, 0), y) = 0 →
      Solves G (c, 0) y := by
    intro y hy hy0
    have hu : ‖((c, 0) : Par ι E)‖ ≤ r / 4 := by
      rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
      exact hcn.trans hpr
    exact (solves_cutoff_iff hr hu (hy.trans hpr)).mp ((eqMap_eq_zero_iff _ _ _ _).mp hy0)
  have hS₁ : Solves G (c, 0) y₁ := hbr y₁ hy₁n (congrArg (fun q => q.2.1) hs1)
  have hS₂ : Solves G (c, 0) y₂ := hbr y₂ hy₂n (congrArg (fun q => q.2.2) hs1)
  have harg : ∀ y : SeqV ι, ‖y‖ ≤ ‖p‖ → ‖((0, c, y 0, 0) : Arg ι E)‖ ≤ r / 4 := by
    intro y hy
    refine (norm_prod_le_iff.mpr ⟨by rw [norm_zero]; positivity, norm_prod_le_iff.mpr
      ⟨hcn.trans hpr, norm_prod_le_iff.mpr ⟨(LocalIFT.norm_seq_apply_le y 0).trans
        (hy.trans hpr), by rw [norm_zero]; positivity⟩⟩⟩)
  have hdate0 : (1 / 2 : ℝ) • (G ((0, c, y₁ 0, 0) : Arg ι E) + G ((0, c, y₂ 0, 0) : Arg ι E)) =
      0 := by
    have e := congrArg Prod.fst hs1
    change (1 / 2 : ℝ) • (F ((0, c, y₁ 0, 0) : Arg ι E) + F ((0, c, y₂ 0, 0) : Arg ι E)) = 0
      at e
    rwa [hFdef, cutoff_eq hr (harg y₁ hy₁n), cutoff_eq hr (harg y₂ hy₂n)] at e
  -- the stochastic sunspot process
  set x : SProcV ι (Bool × Bool) := LocalIFTStochastic.mkB
    (fun q => lagV c (fun t => if q.2.1 then y₁ t else y₂ t) q.1) ⟨‖p‖, fun q => by
      rcases q with ⟨t, b, b'⟩
      cases t with
      | zero => exact hcn
      | succ t =>
        cases b
        · exact (LocalIFT.norm_seq_apply_le y₂ t).trans hy₂n
        · exact (LocalIFT.norm_seq_apply_le y₁ t).trans hy₁n⟩ with hx
  have hxv : ∀ t ω, x (t, ω) = lagV c (fun t => if ω.1 then y₁ t else y₂ t) t :=
    fun _ _ => rfl
  refine ⟨x, ⟨fun t i => ?_, fun t i => ?_⟩, ?_, fun _ _ => rfl, ?_⟩
  · -- adaptedness
    cases t with
    | zero =>
      change ExpectationsFiniteTree.coinSystem.E 0 (fun _ => c i) = fun _ => c i
      exact ExpectationsFiniteTree.coinSystem.const 0 _
    | succ t =>
      change ExpectationsFiniteTree.coinSystem.E (t + 1)
        (fun ω => (fun b : Bool => (if b then y₁ t else y₂ t) i) ω.1) =
          fun ω => (fun b : Bool => (if b then y₁ t else y₂ t) i) ω.1
      exact LocalIFTStochasticModels.coin_known_fst t
        (fun b : Bool => (if b then y₁ t else y₂ t) i)
  · -- the book-form conditions
    cases t with
    | zero =>
      have hf : (fun ω => G (ptS ((0 : ParS ι E (Bool × Bool)), x) (0, ω)) i) =
          fun ω => (fun b : Bool => G ((0, c, (if b then y₁ 0 else y₂ 0), 0) : Arg ι E) i) ω.1 :=
        funext fun ω => rfl
      rw [hf]
      funext ω
      rw [LocalIFTStochasticModels.coin_E0]
      have hi := congrFun hdate0 i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.zero_apply] at hi
      simp only [↓reduceIte, Bool.false_eq_true, Pi.zero_apply]
      linarith
    | succ t =>
      have hf : (fun ω => G (ptS ((0 : ParS ι E (Bool × Bool)), x) (t + 1, ω)) i) = 0 := by
        funext ω
        rcases ω with ⟨b, b'⟩
        cases b
        · change G (lagV c (fun s => y₂ s) t, y₂ t, y₂ (t + 1), (0 : LocalIFT.Seq E) t) i = 0
          exact congrFun (hS₂ t) i
        · change G (lagV c (fun s => y₁ s) t, y₁ t, y₁ (t + 1), (0 : LocalIFT.Seq E) t) i = 0
          exact congrFun (hS₁ t) i
      rw [hf]
      exact map_zero _
  · -- the bound
    refine LocalIFTStochastic.norm_le_of_forall hε.le fun q => ?_
    rcases q with ⟨t, b, b'⟩
    cases t with
    | zero => exact hcn.trans hpε
    | succ t =>
      cases b
      · exact ((LocalIFT.norm_seq_apply_le y₂ t).trans hy₂n).trans hpε
      · exact ((LocalIFT.norm_seq_apply_le y₁ t).trans hy₁n).trans hpε
  · -- randomness
    change y₁ 0 ≠ y₂ 0
    intro hxy
    set err : Br ι := p - s • (κ : Br ι) with herr
    have hpe : p = s • (κ : Br ι) + err := by rw [herr]; abel
    have hy1 : y₁ = s • k + err.2.1 := by
      have := congrArg (fun q : Br ι => q.2.1) hpe
      simpa [hκ] using this
    have hy2 : y₂ = -(s • k) + err.2.2 := by
      have := congrArg (fun q : Br ι => q.2.2) hpe
      simpa [hκ] using this
    have e0 : (2 * s) • k 0 = err.2.2 0 - err.2.1 0 := by
      have h1 := congrArg (fun y : SeqV ι => y 0) hy1
      have h2 := congrArg (fun y : SeqV ι => y 0) hy2
      simp only [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_neg, Pi.add_apply, Pi.smul_apply,
        Pi.neg_apply] at h1 h2
      rw [hxy] at h1
      rw [h1] at h2
      rw [two_mul, add_smul]
      linear_combination h2
    have hen : ‖err‖ ≤ ‖k 0‖ / 2 * s := by
      have := hs3
      rwa [Real.norm_eq_abs, abs_of_pos hs0] at this
    have hb : ‖err.2.2 0 - err.2.1 0‖ ≤ ‖k 0‖ * s := by
      refine (norm_sub_le _ _).trans ?_
      have a1 : ‖err.2.2 0‖ ≤ ‖err‖ :=
        (LocalIFT.norm_seq_apply_le _ 0).trans ((norm_snd_le err.2).trans (norm_snd_le err))
      have a2 : ‖err.2.1 0‖ ≤ ‖err‖ :=
        (LocalIFT.norm_seq_apply_le _ 0).trans ((norm_fst_le err.2).trans (norm_snd_le err))
      linarith
    rw [← e0, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hb
    nlinarith

/-- Woodford (2003), App. A.3, pp. 632–634 (**too many stable roots**): if (A.8) is onto and more
than `n` roots of `det(f₃λ² + f₂λ + f₁)` lie inside the unit circle, the conclusion of
`random_sunspot_nonlinear` holds. -/
theorem random_sunspot_of_count_gt {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (h0 : G 0 = 0) (hs : Function.Surjective (linOp G))
    (hcount : Fintype.card ι < Multiset.card (((quadPoly (M1 G) (M2 G) (M3 G)).map
      Complex.ofRealHom).roots.filter (fun μ => ‖μ‖ < 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV ι (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem G 0 x ∧ ‖x‖ ≤ ε ∧
      (∀ ω ω', x (0, ω) = x (0, ω')) ∧ x (1, (true, true)) ≠ x (1, (false, true)) :=
  random_sunspot_nonlinear hG h0 hs (not_injective_of_count_gt hcount) hε

/-- Woodford (2003), App. A.3, pp. 632–634: the hypotheses of `random_sunspot_nonlinear` stated
for the stochastic operator (A.12) of any expectation system on a nonempty state space (onto and
not one-to-one there implies the same for (A.8)). -/
theorem random_sunspot_of_opS {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0) (h0 : G 0 = 0)
    (hs : Function.Surjective (linOpS 𝔼 G)) (hni : ¬ Function.Injective (linOpS 𝔼 G))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV ι (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem G 0 x ∧ ‖x‖ ≤ ε ∧
      (∀ ω ω', x (0, ω) = x (0, ω')) ∧ x (1, (true, true)) ≠ x (1, (false, true)) :=
  random_sunspot_nonlinear hG h0 (sysOp_surjective_of_opS 𝔼 hs)
    (sysOp_not_injective_of_opS 𝔼 hni) hε

end Woodford.PriceLevelDetermination.LocalIFTSystemsStochasticSunspots
