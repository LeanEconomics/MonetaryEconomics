/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaMeasurePath

/-!
# Nonlinear exogenous laws with Markov-switching shock laws

Woodford (2003), *Interest and Prices*, Appendix E.2, p. 695, and Ch. 6, §1 (the exogenous
disturbances follow a stationary law): an exogenous state obeying the NONLINEAR `Cᵏ` law
`x_t = h(x_{t−1}, σε_t)`, where the law of the innovation `ε_t` depends on a regime that
follows a Markov chain (node-dependent innovation probabilities), with arbitrary bounded-support
laws in each regime.

The law is the model `f(y⁺, y, y⁻, e, e⁺) = y − h(y⁻, e)` of `SmoothInSigmaMeasure`. If the
linearisation is stable, `‖h_x(x̄, 0)‖ < 1`, the linearised operator is `1 − h_x ∘ lag`, which
is invertible by the Neumann series (`linOp_exog`, `exog_isInvertible`); the general theorem
then gives a `Cᵏ` local solution, which satisfies the law EXACTLY at every node
(`exog_solves_iff`), and, on the i.i.d. probability space, surely along every path
(`exog_path`).

## Main results

* `lagOp` (the bounded operator `v ↦ C ∘ v_{t−1}` on adapted processes), `norm_lagOp_le`.
* `exogModel`, `exog_dA`, `exog_dB`, `exog_dC`, `linOp_exog`, `exog_isInvertible`.
* `exog_solves_iff` (the equilibrium conditions are the law itself, node by node),
  `exists_exog_solution` (existence, local uniqueness, `Cᵏ` in `(x_{−1}, s₀, σ)`, for any
  Markov chain of regimes and bounded-support laws), `exog_path` (the i.i.d. case along the
  path: `x_0 = h(x_{−1}, s₀)`, `x_{t+1} = h(x_t, σ clip(ε_{t+1}))` for every `ω`).
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaExog

open MeasureTheory Filter Topology
open SmoothInSigmaMeasure (Hist consH tailH consH_zero tailH_consH adSub MModel clipB
  measurable_tailH)
open SmoothInSigmaMeasure.MModel (lagF completeSpace_adSub)
open SmoothInSigma (Bd mkBd mkBd_apply norm_apply_le norm_le_of_forall pbar zbar)

variable {R Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace R]

/-! ## The lag operator on adapted processes -/

omit [NormedSpace ℝ Y] [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the predecessor of a bounded family (zero before date `0`) is
bounded by the family's sup norm. -/
theorem norm_lagF_le (v : Bd (ℕ × Hist R) Y) (n : ℕ × Hist R) :
    ‖lagF (0 : Y × ℝ × ℝ) (v : ℕ × Hist R → Y) n‖ ≤ ‖v‖ := by
  rcases n with ⟨_ | t, s⟩
  · simp [lagF]
  · exact norm_apply_le v _

/-- Woodford (2003), App. E.2: `C v_{t−1}` is adapted when `v` is. -/
theorem lag_mem (C : Y →L[ℝ] Y) {v : Bd (ℕ × Hist R) Y} (hv : v ∈ adSub (R := R) Y) :
    mkBd (fun n => C (lagF (0 : Y × ℝ × ℝ) (v : ℕ × Hist R → Y) n))
      ⟨‖C‖ * ‖v‖, fun n => (C.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_lagF_le v n) (norm_nonneg C))⟩ ∈ adSub (R := R) Y := by
  refine ⟨fun t => ?_, fun t s s' h1 h2 => ?_⟩
  · cases t with
    | zero =>
      simp only [mkBd_apply, lagF, Prod.fst_zero, map_zero]
      exact stronglyMeasurable_const
    | succ t =>
      simp only [mkBd_apply, lagF]
      exact C.continuous.comp_stronglyMeasurable ((hv.1 t).comp_measurable measurable_tailH)
  · cases t with
    | zero => rfl
    | succ t =>
      simp only [mkBd_apply, lagF]
      exact congrArg C (hv.2 t (tailH s) (tailH s') (fun i hi => h1 (i + 1) (by omega)) h2)

/-- Woodford (2003), App. E.2 (**the lag operator**): `v ↦ C v_{t−1}` (zero at date `0`) as a
bounded linear operator on the adapted processes. -/
noncomputable def lagOp (C : Y →L[ℝ] Y) : adSub (R := R) Y →L[ℝ] adSub (R := R) Y :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨_, lag_mem C v.2⟩
      map_add' := fun v w => by
        refine Subtype.ext (lp.ext (funext fun n => ?_))
        rcases n with ⟨_ | t, s⟩ <;> simp [lagF]
      map_smul' := fun c v => by
        refine Subtype.ext (lp.ext (funext fun n => ?_))
        rcases n with ⟨_ | t, s⟩ <;> simp [lagF] }
    ‖C‖ (fun v => norm_le_of_forall (by positivity) fun n => (C.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_lagF_le _ n) (norm_nonneg C)))

/-- Woodford (2003), App. E.2: members of the lag operator. -/
theorem lagOp_apply (C : Y →L[ℝ] Y) (v : adSub (R := R) Y) (n : ℕ × Hist R) :
    ((lagOp C v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) n =
      C (lagF (0 : Y × ℝ × ℝ) (v : Bd (ℕ × Hist R) Y) n) :=
  rfl

/-- Woodford (2003), App. E.2: `‖C ∘ lag‖ ≤ ‖C‖`. -/
theorem norm_lagOp_le (C : Y →L[ℝ] Y) : ‖lagOp (R := R) C‖ ≤ ‖C‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg C) _

/-! ## The nonlinear exogenous law -/

variable (R) in
/-- Woodford (2003), App. E.2, and Ch. 6, §1 (**a nonlinear exogenous law with Markov-switching
innovation laws**): `x_t = h(x_{t−1}, e_t)`, `e_t = σ clip(ε_t)`, where the next regime is
drawn from `trans` and the next innovation from `law` of the new regime. -/
def exogModel (h : Y × ℝ → Y) (trans : R → R → ℝ) (law : R → ProbabilityMeasure ℝ) (B : ℝ) :
    MModel R Y Y :=
  ⟨fun z => z.2.1 - h (z.2.2.1, z.2.2.2.1), trans, law, B⟩

variable {h : Y × ℝ → Y} {trans : R → R → ℝ} {law : R → ProbabilityMeasure ℝ} {B : ℝ}

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the derivative of the law's residual `y − h(y⁻, e)`. -/
theorem exog_hasFDerivAt {xbar : Y} (hh : DifferentiableAt ℝ h (xbar, 0)) :
    HasFDerivAt (exogModel R h trans law B).f
      ((ContinuousLinearMap.fst ℝ Y (Y × ℝ × ℝ)).comp
          (ContinuousLinearMap.snd ℝ Y (Y × Y × ℝ × ℝ)) -
        (fderiv ℝ h (xbar, 0)).comp
          (((ContinuousLinearMap.fst ℝ Y (ℝ × ℝ)).comp
            ((ContinuousLinearMap.snd ℝ Y (Y × ℝ × ℝ)).comp
              (ContinuousLinearMap.snd ℝ Y (Y × Y × ℝ × ℝ)))).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ Y (ℝ × ℝ)).comp
            ((ContinuousLinearMap.snd ℝ Y (Y × ℝ × ℝ)).comp
              (ContinuousLinearMap.snd ℝ Y (Y × Y × ℝ × ℝ)))))))
      (zbar xbar) := by
  set P : Y × Y × Y × ℝ × ℝ →L[ℝ] Y × ℝ :=
    ((ContinuousLinearMap.fst ℝ Y (ℝ × ℝ)).comp
      ((ContinuousLinearMap.snd ℝ Y (Y × ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ Y (Y × Y × ℝ × ℝ)))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ Y (ℝ × ℝ)).comp
      ((ContinuousLinearMap.snd ℝ Y (Y × ℝ × ℝ)).comp
        (ContinuousLinearMap.snd ℝ Y (Y × Y × ℝ × ℝ))))) with hP
  have hPz : P (zbar xbar) = (xbar, 0) := rfl
  have hh' : HasFDerivAt h (fderiv ℝ h (xbar, 0)) (P (zbar xbar)) := by
    rw [hPz]; exact hh.hasFDerivAt
  exact ((ContinuousLinearMap.fst ℝ Y (Y × ℝ × ℝ)).comp
    (ContinuousLinearMap.snd ℝ Y (Y × Y × ℝ × ℝ))).hasFDerivAt.sub
    (hh'.comp (zbar xbar) P.hasFDerivAt)

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the law does not involve `y_{t+1}`, `A = 0`. -/
theorem exog_dA {xbar : Y} (hh : DifferentiableAt ℝ h (xbar, 0)) (a : Y) :
    (exogModel R h trans law B).dA xbar a = 0 := by
  simp [MModel.dA, (exog_hasFDerivAt hh).fderiv, Prod.mk_zero_zero]

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `B = 1`. -/
theorem exog_dB {xbar : Y} (hh : DifferentiableAt ℝ h (xbar, 0)) (b : Y) :
    (exogModel R h trans law B).dB xbar b = b := by
  simp [MModel.dB, (exog_hasFDerivAt hh).fderiv, Prod.mk_zero_zero]

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `C = −h_x(x̄, 0)`. -/
theorem exog_dC {xbar : Y} (hh : DifferentiableAt ℝ h (xbar, 0)) (c : Y) :
    (exogModel R h trans law B).dC xbar c = -fderiv ℝ h (xbar, 0) (c, 0) := by
  simp [MModel.dC, (exog_hasFDerivAt hh).fderiv]

variable [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [CompleteSpace Y]

/-- Woodford (2003), App. E.2 (**the linearised exogenous law**): the linearised operator is
`1 − h_x ∘ lag`, `(L v)_t = v_t − h_x(x̄, 0) v_{t−1}`. -/
theorem linOp_exog (hM : (exogModel R h trans law B).Std) (hh : ContDiff ℝ 1 h) (xbar : Y) :
    (exogModel R h trans law B).linOp hM
        (show ContDiff ℝ 1 (exogModel R h trans law B).f from
          contDiff_snd.fst.sub (hh.comp (contDiff_snd.snd.fst.prodMk
            contDiff_snd.snd.snd.fst))).continuous xbar =
      1 - lagOp ((fderiv ℝ h (xbar, 0)).comp (ContinuousLinearMap.inl ℝ Y ℝ)) := by
  have hf : ContDiff ℝ 1 (exogModel R h trans law B).f :=
    contDiff_snd.fst.sub (hh.comp (contDiff_snd.snd.fst.prodMk contDiff_snd.snd.snd.fst))
  have hd : DifferentiableAt ℝ h (xbar, 0) := hh.differentiable (by norm_num) _
  refine ContinuousLinearMap.ext fun v => Subtype.ext (lp.ext (funext fun n => ?_))
  rcases n with ⟨t, s⟩
  rw [(exogModel R h trans law B).linOp_apply hM hf.continuous hf xbar v t s]
  simp only [exog_dA hd, exog_dB hd, exog_dC hd, zero_add, integral_const, probReal_univ,
    one_smul]
  rw [← Finset.sum_smul, hM.trans_sum, one_smul]
  change _ = (v : Bd (ℕ × Hist R) Y) (t, s) -
    ((lagOp ((fderiv ℝ h (xbar, 0)).comp (ContinuousLinearMap.inl ℝ Y ℝ)) v : adSub (R := R) Y) :
      Bd (ℕ × Hist R) Y) (t, s)
  rw [lagOp_apply, sub_eq_add_neg]
  rfl

/-- Woodford (2003), App. E.2, and Ch. 6, §1 (**a stable linearisation gives determinacy**): if
`‖h_x(x̄, 0)‖ < 1` the linearised operator of the exogenous law is invertible on the bounded
adapted processes (Neumann series). -/
theorem exog_isInvertible (hM : (exogModel R h trans law B).Std) (hh : ContDiff ℝ 1 h)
    (xbar : Y) (hstab : ‖(fderiv ℝ h (xbar, 0)).comp (ContinuousLinearMap.inl ℝ Y ℝ)‖ < 1) :
    ((exogModel R h trans law B).linOp hM
        (show ContDiff ℝ 1 (exogModel R h trans law B).f from
          contDiff_snd.fst.sub (hh.comp (contDiff_snd.snd.fst.prodMk
            contDiff_snd.snd.snd.fst))).continuous xbar).IsInvertible := by
  have := completeSpace_adSub (R := R) Y
  rw [linOp_exog hM hh xbar]
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one
    (R := adSub (R := R) Y →L[ℝ] adSub (R := R) Y)
    (x := lagOp ((fderiv ℝ h (xbar, 0)).comp (ContinuousLinearMap.inl ℝ Y ℝ)))
    (by exact (norm_lagOp_le (R := R) _).trans_lt hstab)
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ _ u, by ext1 v; simp [hu]⟩

omit [MeasurableSpace R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] in
/-- Woodford (2003), App. E.2 (**the equilibrium conditions are the law itself**): a family
solves the exogenous model iff `x(t, s) = h(x_{t−1}, e_t)` at EVERY node (the conditions do not
involve the future, so the expectation is trivial). -/
theorem exog_solves_iff (hM : (exogModel R h trans law B).Std) (u : ℕ × Hist R → Y)
    (p : Y × ℝ × ℝ) :
    (exogModel R h trans law B).Solves u p ↔
      ∀ t s, u (t, s) = h (lagF p u (t, s), (exogModel R h trans law B).enowF p (t, s)) := by
  unfold MModel.Solves
  simp only [exogModel, integral_const, probReal_univ, one_smul]
  refine forall_congr' fun t => forall_congr' fun s => ?_
  rw [← Finset.sum_smul, show ∑ i, trans (s 0).1 i = 1 from hM.trans_sum _, one_smul,
    sub_eq_zero]

/-- Woodford (2003), App. E.2, and Ch. 6, §1 (**existence and smoothness for a nonlinear
exogenous law with Markov-switching innovation laws**): if `h` is `Cᵏ` (`k ≥ 1`),
`h(x̄, 0) = x̄` and `‖h_x(x̄, 0)‖ < 1`, there is a local solution `ψ`, `Cᵏ` in
`(x_{−1}, s₀, σ)` at `p̄`, locally unique among bounded adapted processes, obeying the law
`x(t, s) = h(x_{t−1}, e_t)` at every node, for any regime chain and bounded-support laws. -/
theorem exists_exog_solution (hM : (exogModel R h trans law B).Std) {k : ℕ} (hk : 1 ≤ k)
    (hh : ContDiff ℝ k h) {xbar : Y} (hfix : h (xbar, 0) = xbar)
    (hstab : ‖(fderiv ℝ h (xbar, 0)).comp (ContinuousLinearMap.inl ℝ Y ℝ)‖ < 1) :
    ∃ ψ : Y × ℝ × ℝ → adSub (R := R) Y, (exogModel R h trans law B).LocalSol xbar ψ ∧
      ContDiffAt ℝ k ψ (pbar xbar) ∧ ∀ᶠ p in 𝓝 (pbar xbar : Y × ℝ × ℝ), ∀ t s,
        (ψ p : Bd (ℕ × Hist R) Y) (t, s) = h (lagF p (ψ p : Bd (ℕ × Hist R) Y) (t, s),
          (exogModel R h trans law B).enowF p (t, s)) := by
  have hf : ContDiff ℝ k (exogModel R h trans law B).f :=
    contDiff_snd.fst.sub (hh.comp (contDiff_snd.snd.fst.prodMk contDiff_snd.snd.snd.fst))
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast hk)
  have hss : (exogModel R h trans law B).f (zbar xbar) = 0 := by
    change xbar - h (xbar, 0) = 0
    rw [hfix, sub_self]
  have hdet := exog_isInvertible (trans := trans) (law := law) (B := B) hM hh1 xbar hstab
  obtain ⟨ψ, hψ, hψk⟩ := (exogModel R h trans law B).exists_smooth_solution hM hk hf hss hdet
  refine ⟨ψ, hψ, hψk, ?_⟩
  filter_upwards [hψ.solves] with p hp
  exact (exog_solves_iff hM _ p).1 hp

omit [NormedSpace ℝ Y] [Fintype R] [MeasurableSingletonClass R] [MeasurableSpace R]
  [FiniteDimensional ℝ Y] [CompleteSpace Y] in
/-- Woodford (2003), App. E.2, on the i.i.d. probability space (**the law holds surely along
every path**): for a single regime, a solution read along the path obeys
`x_0 = h(x_{−1}, s₀)` and `x_{t+1} = h(x_t, σ clip(ε_{t+1}))` for every `ω`. -/
theorem exog_path {h : Y × ℝ → Y} {trans : Unit → Unit → ℝ} {law : Unit → ProbabilityMeasure ℝ}
    {B : ℝ} {u : Bd (ℕ × Hist Unit) Y} {p : Y × ℝ × ℝ}
    (hu : ∀ t s, u (t, s) = h (lagF p (u : ℕ × Hist Unit → Y) (t, s),
      (exogModel Unit h trans law B).enowF p (t, s))) (ω : ℕ → ℝ) :
    SmoothInSigmaMeasurePath.yproc u 0 ω = h (p.1, p.2.1) ∧
      ∀ t, SmoothInSigmaMeasurePath.yproc u (t + 1) ω =
        h (SmoothInSigmaMeasurePath.yproc u t ω, p.2.2 * clipB B (ω (t + 1))) := by
  refine ⟨hu 0 _, fun t => ?_⟩
  have h1 := hu (t + 1) (SmoothInSigmaMeasurePath.histOf (t + 1) ω)
  rw [SmoothInSigmaMeasurePath.lagF_histOf, SmoothInSigmaMeasurePath.enowF_histOf] at h1
  exact h1

end Woodford.StabilizationWelfare.SmoothInSigmaExog
