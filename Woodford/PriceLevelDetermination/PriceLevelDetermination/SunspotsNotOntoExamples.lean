/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.SunspotsBoundedBelow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries

/-!
# Sunspots when (A.8) is not onto: examples

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 632–634. `SunspotsBoundedBelow` shows
that the linearisation decides whether random sunspot equilibria exist near the steady state
when the operator (A.8) is onto (they exist iff (A.8) is not one-to-one) or bounded below (they
never exist). This module gives explicit scalar (`n = 1`) examples for the other cases.

## Main results

* **Bounded below but not onto** (too few stable roots): `Glag`,
  `E_t[x_t + 2x_{t−1} + x_{t+1}² − e_t] = 0`. (A.8) is `v_t + 2v_{t−1}` (root `−2`, no stable
  root): `boundedBelow_linOp_Glag`, `not_surjective_linOp_Glag`. Hence `Glag_unique`: for every
  expectation system, local uniqueness for every small `(x_{−1}, e)`, and no sunspots.
* **A unit root: the linearisation does not decide.** `Gatt` (`E_t x_{t+1} = x_t − x_t³`) and
  `Grep` (`E_t x_{t+1} = x_t + x_t³`) have the **same** operator (A.8), `v_{t+1} − v_t`, with root
  `1` on the unit circle; it is neither one-to-one (`not_injective_linOp_unit`) nor onto
  (`not_surjective_linOp_unit`), and its range is **not closed** (`not_isClosed_range_unit`), so
  it is not Fredholm. Yet `Gatt_random_sunspot`: random sunspots at every scale on the coin tree;
  `Grep_unique`: under informational closure (perfect foresight, every finite tree) the steady
  state is the **only** bounded adapted equilibrium, for any `(x_{−1}, e)`.
* **A singular pencil with closed range: the linearisation does not decide.** `Gcub`
  (`E_t[x_{t+1}³ − x_t³] = 0`) and `Gsta` (`E_t[x_t³] = 0`) both have (A.8) `= 0` (closed range,
  `det(f₃λ² + f₂λ + f₁) ≡ 0`); `Gcub_random_sunspot` and `Gsta_unique`.

So outside "(A.8) onto" and "(A.8) bounded below" the existence of random sunspots near the
steady state is decided by higher-order terms, not by (A.8) (correction: a unit root does not
give a closed range of finite codimension).
-/

namespace Woodford.PriceLevelDetermination.SunspotsNotOntoExamples

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SunspotsBoundedBelow
open LocalIFTSystems (Arg linOp linOp_apply d1 d2 d3 projB projE)

/-! ### Tools -/

/-- Woodford (2003), App. A.3, p. 633 (tool): under informational closure a function of a variable
known at `t` is known at `t`. -/
theorem known_comp {Ω : Type*} {𝔼 : ExpectationSystem Ω} (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {t : ℕ} {y : Ω → ℝ} (hy : 𝔼.E t y = y) (f : ℝ → ℝ) :
    𝔼.E t (fun ω => f (y ω)) = fun ω => f (y ω) :=
  hcl t _ fun ω ω' h => by rw [LocalIFTStochastic.Ops.cellConst_of_known 𝔼 hy ω ω' h]

/-- Woodford (2003), App. A.3, p. 633 (tool): the coordinate `x_{t−1}` of the scalar argument. -/
noncomputable def pA : Arg (Fin 1) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ))

/-- Woodford (2003), App. A.3, p. 633 (tool): the coordinate `x_{t+1}` of the scalar argument. -/
noncomputable def pC : Arg (Fin 1) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp ((ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ℝ).comp
    ((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ))))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (tool): a scalar condition whose derivative at
the steady state is `a x_{t−1} + b x_t + c x_{t+1} + d e_t` has the operator (A.8)
`v ↦ a v_{t−1} + b v_t + c v_{t+1}`. -/
theorem linOp_of_fderiv {G : Arg (Fin 1) ℝ → (Fin 1 → ℝ)} {a b c d : ℝ}
    (hG : ∀ p : Arg (Fin 1) ℝ,
      fderiv ℝ G 0 p = fun _ => a * p.1 0 + b * p.2.1 0 + c * p.2.2.1 0 + d * p.2.2.2)
    (v : SeqV (Fin 1)) (t : ℕ) :
    linOp G v t = fun _ => a * lagV 0 (fun s => v s) t 0 + b * v t 0 + c * v (t + 1) 0 := by
  rw [linOp_apply]
  simp only [d1, d2, d3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, hG]
  funext i
  simp

/-- Woodford (2003), App. A.3, p. 634 (tool): the two-branch process on the coin tree,
`x_0 = 0` and `x_{t+1} = y_b(t)` after first flip `b`. -/
noncomputable def brProc (y : Bool → ℕ → ℝ) {M : ℝ} (hM : ∀ b t, |y b t| ≤ M) :
    SProcV (Fin 1) (Bool × Bool) :=
  LocalIFTStochastic.mkB (fun p _ => lagV 0 (y p.2.1) p.1) ⟨max M 0, fun p => by
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun _ => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨t, ω⟩ := p
    cases t with
    | zero => simp
    | succ t => exact (hM _ t).trans (le_max_left _ _)⟩

/-- Woodford (2003), App. A.3, p. 634 (tool): the two-branch process is within `M` of the
steady state. -/
theorem norm_brProc_le {y : Bool → ℕ → ℝ} {M : ℝ} (hM : ∀ b t, |y b t| ≤ M) (hM0 : 0 ≤ M) :
    ‖brProc y hM‖ ≤ M := by
  refine LocalIFTStochastic.norm_le_of_forall hM0 fun p => ?_
  refine (pi_norm_le_iff_of_nonneg hM0).mpr fun _ => ?_
  rw [Real.norm_eq_abs]
  obtain ⟨t, ω⟩ := p
  cases t with
  | zero =>
    change |lagV 0 (y ω.1) 0| ≤ M
    simpa using hM0
  | succ t => exact hM _ t

/-- Woodford (2003), App. A.3, p. 634 (tool): **the two-branch process is an equilibrium** of a
scalar condition `φ(x_t, x_{t+1})` on the coin tree if each branch solves it from date 1 on and
the date-0 condition holds on average over the first flip. -/
theorem solvesSV_brProc {G : Arg (Fin 1) ℝ → (Fin 1 → ℝ)} {φ : ℝ → ℝ → ℝ}
    (hG : ∀ p : Arg (Fin 1) ℝ, G p = fun _ => φ (p.2.1 0) (p.2.2.1 0))
    {y : Bool → ℕ → ℝ} {M : ℝ} (hM : ∀ b t, |y b t| ≤ M)
    (h0 : φ 0 (y true 0) + φ 0 (y false 0) = 0) (hstep : ∀ b t, φ (y b t) (y b (t + 1)) = 0) :
    SolvesSV ExpectationsFiniteTree.coinSystem G 0 (brProc y hM) := by
  refine ⟨fun t i => ?_, fun t i => ?_⟩
  · cases t with
    | zero =>
      change ExpectationsFiniteTree.coinSystem.E 0 (fun _ => 0) = fun _ => 0
      exact ExpectationsFiniteTree.coinSystem.const 0 0
    | succ t =>
      change ExpectationsFiniteTree.coinSystem.E (t + 1) (fun ω => y ω.1 t) = fun ω => y ω.1 t
      exact LocalIFTStochasticModels.coin_known_fst t (fun b => y b t)
  · cases t with
    | zero =>
      have hf : (fun ω => G (ptS ((0 : ParS (Fin 1) ℝ (Bool × Bool)), brProc y hM) (0, ω)) i) =
          fun ω => φ 0 (y ω.1 0) := by
        funext ω
        rw [hG]
        rfl
      rw [hf]
      funext ω
      rw [LocalIFTStochasticModels.coin_E0]
      simp only [Pi.zero_apply]
      linarith
    | succ t =>
      have hf : (fun ω => G (ptS ((0 : ParS (Fin 1) ℝ (Bool × Bool)), brProc y hM)
          (t + 1, ω)) i) = 0 := by
        funext ω
        rw [hG]
        exact hstep ω.1 t
      rw [hf]
      exact map_zero _

/-! ### Bounded below but not onto: too few stable roots -/

/-- Woodford (2003), App. A.3, p. 632 (example): the condition `x_t + 2x_{t−1} + x_{t+1}² − e_t`
(characteristic root `−2`: no stable root, one predetermined variable). -/
def Glag (p : Arg (Fin 1) ℝ) : Fin 1 → ℝ := fun _ => p.2.1 0 + 2 * p.1 0 + p.2.2.1 0 ^ 2 - p.2.2.2

/-- Woodford (2003), App. A.3, p. 632 (example): `Glag` is `C^∞`. -/
theorem contDiff_Glag (k : ℕ) : ContDiff ℝ k Glag :=
  contDiff_pi.mpr fun _ =>
    ((projB.contDiff.add (contDiff_const.mul pA.contDiff)).add (pC.contDiff.pow 2)).sub
      projE.contDiff

/-- Woodford (2003), App. A.3, p. 632 (example): the derivative of `Glag` at the steady state. -/
theorem fderiv_Glag (p : Arg (Fin 1) ℝ) :
    fderiv ℝ Glag 0 p = fun _ => 2 * p.1 0 + 1 * p.2.1 0 + 0 * p.2.2.1 0 + (-1) * p.2.2.2 := by
  have hA : HasFDerivAt (pA : Arg (Fin 1) ℝ → ℝ) pA 0 := pA.hasFDerivAt
  have hB : HasFDerivAt (projB : Arg (Fin 1) ℝ → ℝ) projB 0 := projB.hasFDerivAt
  have hC : HasFDerivAt (pC : Arg (Fin 1) ℝ → ℝ) pC 0 := pC.hasFDerivAt
  have hE : HasFDerivAt (projE : Arg (Fin 1) ℝ → ℝ) projE 0 := projE.hasFDerivAt
  have h : HasFDerivAt Glag (ContinuousLinearMap.pi fun _ : Fin 1 =>
      projB + (2 : ℝ) • pA - projE) 0 := by
    refine hasFDerivAt_pi'' fun _ => ?_
    have h1 := ((hB.add (hA.const_mul (2 : ℝ))).add (hC.pow 2)).sub hE
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [pC]
  rw [h.fderiv]
  funext i
  simp [projB, projE, pA]
  ring

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (example): the operator (A.8) of `Glag` is
`v ↦ v_t + 2v_{t−1}`. -/
theorem linOp_Glag (v : SeqV (Fin 1)) (t : ℕ) :
    linOp Glag v t = fun _ => 2 * lagV 0 (fun s => v s) t 0 + 1 * v t 0 + 0 * v (t + 1) 0 :=
  linOp_of_fderiv fderiv_Glag v t

/-- Woodford (2003), App. A.3, p. 632 (example): **the operator (A.8) of `Glag` is bounded below**,
`‖v‖ ≤ ‖(A.8) v‖` (from `v_t = ((A.8)v)_{t+1}/2 − v_{t+1}/2`). -/
theorem boundedBelow_linOp_Glag : BoundedBelow (linOp Glag) := by
  refine ⟨1, zero_le_one, fun v => ?_⟩
  rw [one_mul]
  have hc : ∀ t, |v t 0| ≤ (‖linOp Glag v‖ + ‖v‖) / 2 := by
    intro t
    have h := congrFun (linOp_Glag v (t + 1)) 0
    simp only [lagV_succ] at h
    have h1 : |linOp Glag v (t + 1) 0| ≤ ‖linOp Glag v‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ 0).trans (LocalIFT.norm_seq_apply_le _ _)
    have h2 : |v (t + 1) 0| ≤ ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ 0).trans (LocalIFT.norm_seq_apply_le _ _)
    rw [h] at h1
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  have hv : ‖v‖ ≤ (‖linOp Glag v‖ + ‖v‖) / 2 :=
    LocalIFT.norm_seq_le (by positivity) fun t =>
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
        rw [Real.norm_eq_abs, Subsingleton.elim i 0]
        exact hc t
  linarith

/-- Woodford (2003), App. A.3, p. 632 (example): **the operator (A.8) of `Glag` is not onto**:
the impulse `(1, 0, 0, …)` would need `v_t = (−2)ᵗ`. -/
theorem not_surjective_linOp_Glag : ¬ Function.Surjective (linOp Glag) := by
  intro hs
  have hb : LinearSystems.BoundedSeq (fun (t : ℕ) (_ : Fin 1) => if t = 0 then (1 : ℝ) else 0) :=
    ⟨1, fun t _ => by
      change |(if t = 0 then (1 : ℝ) else 0)| ≤ 1
      split_ifs <;> simp⟩
  obtain ⟨v, hv⟩ := hs (toSeqV _ hb)
  have hval : ∀ t, v t 0 = (-2) ^ t := by
    intro t
    induction t with
    | zero =>
      have h := congrFun (congrArg (fun w : SeqV (Fin 1) => w 0) hv) 0
      rw [linOp_Glag] at h
      simpa using h
    | succ t ih =>
      have h := congrFun (congrArg (fun w : SeqV (Fin 1) => w (t + 1)) hv) 0
      rw [linOp_Glag] at h
      simp only [lagV_succ, toSeqV_apply, Nat.add_one_ne_zero, ↓reduceIte] at h
      rw [pow_succ]
      linarith
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt ‖v‖ (by norm_num : (1 : ℝ) < 2)
  have h1 : |v t 0| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ 0).trans (LocalIFT.norm_seq_apply_le _ _)
  rw [hval, abs_pow, abs_neg, abs_two] at h1
  linarith

/-- **Bounded below, not onto: local uniqueness and no sunspots** (Woodford (2003), App. A.3,
pp. 632–634, example): the linearisation of `E_t[x_t + 2x_{t−1} + x_{t+1}² − e_t] = 0` has no
stable root, so (A.8) is not onto, but it is bounded below; hence for every expectation system
there is `ε > 0` with at most one bounded adapted equilibrium within `ε` of the steady state for
every `‖(x_{−1}, e)‖ < ε`, and the steady state is the only one when `x_{−1} = 0, e = 0`. -/
theorem Glag_unique {Ω : Type*} (𝔼 : ExpectationSystem Ω) :
    ¬ Function.Surjective (linOp Glag) ∧
      (∃ ε > 0, ∀ (u : ParS (Fin 1) ℝ Ω) (x y : SProcV (Fin 1) Ω), ‖u‖ < ε → ‖x‖ < ε →
        ‖y‖ < ε → SolvesSV 𝔼 Glag u x → SolvesSV 𝔼 Glag u y → x = y) ∧
      ∃ ε > 0, ∀ x : SProcV (Fin 1) Ω, ‖x‖ < ε → SolvesSV 𝔼 Glag 0 x → x = 0 := by
  have hc : ContDiffAt ℝ 1 Glag 0 := (contDiff_Glag 1).contDiffAt
  have h0 : Glag 0 = 0 := by
    funext i
    simp [Glag]
  exact ⟨not_surjective_linOp_Glag, unique_of_boundedBelow 𝔼 hc boundedBelow_linOp_Glag,
    no_sunspot_of_boundedBelow 𝔼 hc h0 boundedBelow_linOp_Glag⟩

/-! ### A unit root: the same linearisation, opposite answers -/

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t x_{t+1} = x_t − x_t³` (attracting cubic). -/
def Gatt (p : Arg (Fin 1) ℝ) : Fin 1 → ℝ := fun _ => p.2.2.1 0 - p.2.1 0 + p.2.1 0 ^ 3

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t x_{t+1} = x_t + x_t³` (repelling cubic). -/
def Grep (p : Arg (Fin 1) ℝ) : Fin 1 → ℝ := fun _ => p.2.2.1 0 - p.2.1 0 - p.2.1 0 ^ 3

/-- Woodford (2003), App. A.3, p. 632 (example): `Gatt` and `Grep` are `C^∞`. -/
theorem contDiff_Gatt_Grep (k : ℕ) : ContDiff ℝ k Gatt ∧ ContDiff ℝ k Grep :=
  ⟨contDiff_pi.mpr fun _ => (pC.contDiff.sub projB.contDiff).add (projB.contDiff.pow 3),
    contDiff_pi.mpr fun _ => (pC.contDiff.sub projB.contDiff).sub (projB.contDiff.pow 3)⟩

/-- Woodford (2003), App. A.3, p. 632 (example): **both have the derivative `x_{t+1} − x_t`** at
the steady state. -/
theorem fderiv_Gatt_Grep (p : Arg (Fin 1) ℝ) :
    fderiv ℝ Gatt 0 p = (fun _ => 0 * p.1 0 + (-1) * p.2.1 0 + 1 * p.2.2.1 0 + 0 * p.2.2.2) ∧
      fderiv ℝ Grep 0 p = (fun _ => 0 * p.1 0 + (-1) * p.2.1 0 + 1 * p.2.2.1 0 + 0 * p.2.2.2) := by
  have hA : HasFDerivAt (pA : Arg (Fin 1) ℝ → ℝ) pA 0 := pA.hasFDerivAt
  have hB : HasFDerivAt (projB : Arg (Fin 1) ℝ → ℝ) projB 0 := projB.hasFDerivAt
  have hC : HasFDerivAt (pC : Arg (Fin 1) ℝ → ℝ) pC 0 := pC.hasFDerivAt
  have hE : HasFDerivAt (projE : Arg (Fin 1) ℝ → ℝ) projE 0 := projE.hasFDerivAt
  have ha : HasFDerivAt Gatt (ContinuousLinearMap.pi fun _ : Fin 1 => pC - projB) 0 := by
    refine hasFDerivAt_pi'' fun _ => ?_
    have h1 := (hC.sub hB).add (hB.pow 3)
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [projB]
  have hr : HasFDerivAt Grep (ContinuousLinearMap.pi fun _ : Fin 1 => pC - projB) 0 := by
    refine hasFDerivAt_pi'' fun _ => ?_
    have h1 := (hC.sub hB).sub (hB.pow 3)
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [projB]
  rw [ha.fderiv, hr.fderiv]
  refine ⟨?_, ?_⟩ <;> funext i <;> simp [projB, pC] <;> ring

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (example): **`Gatt` and `Grep` have the same
operator (A.8)**, `v ↦ v_{t+1} − v_t` (characteristic root `1`, on the unit circle). -/
theorem linOp_Gatt_Grep : linOp Gatt = linOp Grep ∧ ∀ (v : SeqV (Fin 1)) (t : ℕ),
    linOp Gatt v t = fun _ => 0 * lagV 0 (fun s => v s) t 0 + (-1) * v t 0 + 1 * v (t + 1) 0 := by
  have hA := fun v t => linOp_of_fderiv (fun p => (fderiv_Gatt_Grep p).1) v t
  have hR := fun v t => linOp_of_fderiv (fun p => (fderiv_Gatt_Grep p).2) v t
  exact ⟨ContinuousLinearMap.ext fun v => seq_ext fun t => by rw [hA, hR], hA⟩

/-- Woodford (2003), App. A.3, p. 632 (example): the unit-root operator `v_{t+1} − v_t` is not
one-to-one (constants). -/
theorem not_injective_linOp_unit : ¬ Function.Injective (linOp Gatt) := by
  intro hinj
  have hb : LinearSystems.BoundedSeq (fun (_ : ℕ) (_ : Fin 1) => (1 : ℝ)) := ⟨1, fun _ _ => by simp⟩
  have h : linOp Gatt (toSeqV _ hb) = linOp Gatt 0 := by
    rw [map_zero]
    refine seq_ext fun t => ?_
    rw [linOp_Gatt_Grep.2]
    funext i
    simp
  have h1 := congrFun (congrArg (fun w : SeqV (Fin 1) => w 0) (hinj h)) 0
  simp at h1

/-- Woodford (2003), App. A.3, p. 632 (example): the unit-root operator is not onto (the constant
forcing `1` needs `v_t = v_0 + t`). -/
theorem not_surjective_linOp_unit : ¬ Function.Surjective (linOp Gatt) := by
  intro hs
  have hb : LinearSystems.BoundedSeq (fun (_ : ℕ) (_ : Fin 1) => (1 : ℝ)) := ⟨1, fun _ _ => by simp⟩
  obtain ⟨v, hv⟩ := hs (toSeqV _ hb)
  have hval : ∀ t : ℕ, v t 0 = v 0 0 + t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h := congrFun (congrArg (fun w : SeqV (Fin 1) => w t) hv) 0
      rw [linOp_Gatt_Grep.2] at h
      simp only [toSeqV_apply] at h
      push_cast
      linarith
  have hn : ∀ t, |v t 0| ≤ ‖v‖ := fun t => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ 0).trans (LocalIFT.norm_seq_apply_le _ _)
  obtain ⟨t, ht⟩ := exists_nat_gt (2 * ‖v‖)
  have h1 := hn t
  have h2 := hn 0
  rw [hval, abs_le] at h1
  rw [abs_le] at h2
  linarith [h1.2, h2.1]

/-- **A unit root does not give a closed range** (Woodford (2003), App. A.3, p. 632; correction):
the range of the unit-root operator `v ↦ v_{t+1} − v_t` on `ℓ∞` is not closed (`1/(t+1)` is a limit
of truncations in the range but is not in it, the harmonic series diverging), so (A.8) is not
Fredholm here. -/
theorem not_isClosed_range_unit : ¬ IsClosed (Set.range (linOp Gatt)) := by
  intro hcl
  have hwb : LinearSystems.BoundedSeq (fun (t : ℕ) (_ : Fin 1) => 1 / ((t : ℝ) + 1)) :=
    ⟨1, fun t _ => by
      rw [abs_of_pos (by positivity)]
      exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]) (by positivity)⟩
  set w := toSeqV _ hwb with hw
  have hmem : w ∈ closure (Set.range (linOp Gatt)) := by
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    have hvb : LinearSystems.BoundedSeq (fun (t : ℕ) (_ : Fin 1) =>
        ∑ s ∈ Finset.range (min t N), 1 / ((s : ℝ) + 1)) := ⟨N, fun t _ => by
      rw [abs_of_nonneg (Finset.sum_nonneg fun s _ => by positivity)]
      calc _ ≤ ∑ _s ∈ Finset.range (min t N), (1 : ℝ) := Finset.sum_le_sum fun s _ =>
            div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]) (by positivity)
        _ = (min t N : ℕ) := by simp
        _ ≤ N := by exact_mod_cast min_le_right t N⟩
    refine ⟨linOp Gatt (toSeqV _ hvb), ⟨_, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (LocalIFT.norm_seq_le (by positivity) fun t =>
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_) hN
    rw [Real.norm_eq_abs]
    change |(w - linOp Gatt (toSeqV _ hvb)) t i| ≤ 1 / ((N : ℝ) + 1)
    rw [lp.coeFn_sub, Pi.sub_apply, linOp_Gatt_Grep.2, hw, toSeqV_apply, Pi.sub_apply]
    simp only [toSeqV_apply]
    by_cases htN : t < N
    · rw [min_eq_left (by omega : t + 1 ≤ N), min_eq_left htN.le, Finset.sum_range_succ]
      simp only [one_div, zero_mul, neg_mul, one_mul, zero_add, neg_add_cancel_left, sub_self,
        abs_zero, inv_nonneg]
      positivity
    · push Not at htN
      rw [min_eq_right (by omega : N ≤ t + 1), min_eq_right htN]
      simp only [zero_mul, zero_add, neg_mul, one_mul, neg_add_cancel, sub_zero]
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ htN)
  rw [hcl.closure_eq] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hval : ∀ t : ℕ, v t 0 = v 0 0 + ∑ s ∈ Finset.range t, 1 / ((s : ℝ) + 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h := congrFun (congrArg (fun w' : SeqV (Fin 1) => w' t) hv) 0
      rw [linOp_Gatt_Grep.2, hw] at h
      simp only [toSeqV_apply] at h
      rw [Finset.sum_range_succ]
      linarith
  have hn : ∀ t, |v t 0| ≤ ‖v‖ := fun t => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ 0).trans (LocalIFT.norm_seq_apply_le _ _)
  obtain ⟨t, ht⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
    (2 * ‖v‖)).exists
  have h1 := hn t
  have h2 := hn 0
  rw [hval, abs_le] at h1
  rw [abs_le] at h2
  linarith [h1.2, h2.1]

/-- Woodford (2003), App. A.3, p. 632 (example): the attracting cubic `z ↦ z − z³` maps
`[−1, 1]` into itself and does not increase `|z|`. -/
theorem abs_att_le {z : ℝ} (hz : |z| ≤ 1) : |z - z ^ 3| ≤ |z| := by
  have h : z - z ^ 3 = z * (1 - z ^ 2) := by ring
  rw [h, abs_mul]
  have h2 : z ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg z]
  rw [abs_of_nonneg (a := 1 - z ^ 2) (by linarith)]
  calc |z| * (1 - z ^ 2) ≤ |z| * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z]) (abs_nonneg z)
    _ = |z| := mul_one _

/-- Woodford (2003), App. A.3, p. 634 (example): the deterministic path `x_{t+1} = x_t − x_t³`
from `x_0 = c`. -/
noncomputable def attPath (c : ℝ) : ℕ → ℝ
  | 0 => c
  | t + 1 => attPath c t - attPath c t ^ 3

/-- Woodford (2003), App. A.3, p. 634 (example): the attracting path stays within `|c| ≤ 1`. -/
theorem abs_attPath_le {c : ℝ} (hc : |c| ≤ 1) (t : ℕ) : |attPath c t| ≤ |c| := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (abs_att_le (ih.trans hc)).trans ih

/-- **Random sunspots at a unit root** (Woodford (2003), App. A.3, pp. 632–634, example): for
`E_t x_{t+1} = x_t − x_t³`, whose operator (A.8) has the unit root `1` (neither one-to-one nor
onto, range not closed), on the core coin tree and for every `ε > 0` there is a bounded adapted
equilibrium with `x_{−1} = 0`, no disturbances, `‖x‖ ≤ ε`, whose date-1 value differs across
the first flip (`x_1 = ±a`, then `x_{t+1} = x_t − x_t³` converges back). -/
theorem Gatt_random_sunspot {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV (Fin 1) (Bool × Bool), SolvesSV ExpectationsFiniteTree.coinSystem Gatt 0 x ∧
      ‖x‖ ≤ ε ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  set a := min ε 1 with ha
  have ha0 : 0 < a := lt_min hε one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  set y : Bool → ℕ → ℝ := fun b => attPath (if b then a else -a) with hy
  have habs : ∀ b : Bool, |(if b then a else -a)| = a := fun b => by
    cases b <;> simp [abs_of_pos ha0]
  have hM : ∀ b t, |y b t| ≤ a := fun b t =>
    (abs_attPath_le (by rw [habs]; exact ha1) t).trans_eq (habs b)
  refine ⟨brProc y hM, solvesSV_brProc (φ := fun z z' => z' - z + z ^ 3) (fun p => rfl) hM ?_
    (fun b t => ?_), (norm_brProc_le hM ha0.le).trans (min_le_left _ _), fun h => ?_⟩
  · simp [hy, attPath]
  · change attPath _ (t + 1) - attPath _ t + attPath _ t ^ 3 = 0
    simp only [attPath]
    ring
  · have := congrFun h 0
    change a = -a at this
    linarith

/-- Woodford (2003), App. A.3, p. 634 (example, tool): an equilibrium of `Grep` satisfies
`E_t x_{t+1} = x_t + x_t³` (informational closure makes `x_t³` known). -/
theorem Grep_E {Ω : Type*} {𝔼 : ExpectationSystem Ω} (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {u : ParS (Fin 1) ℝ Ω} {x : SProcV (Fin 1) Ω} (hx : SolvesSV 𝔼 Grep u x) (t : ℕ) :
    𝔼.E t (toP x (t + 1) 0) = fun ω => toP x t 0 ω + toP x t 0 ω ^ 3 := by
  have h := hx.2 t 0
  have hf : (fun ω => Grep (ptS (u, x) (t, ω)) 0) =
      toP x (t + 1) 0 - toP x t 0 - fun ω => toP x t 0 ω ^ 3 := rfl
  rw [hf, map_sub, map_sub, hx.1 t 0, known_comp hcl (hx.1 t 0) (fun z => z ^ 3)] at h
  funext ω
  have := congrFun h ω
  simp only [Pi.sub_apply, Pi.zero_apply] at this
  linarith

/-- **No sunspots at the same unit root** (Woodford (2003), App. A.3, pp. 632–634, example): for
`E_t x_{t+1} = x_t + x_t³` — the same operator (A.8) as `Gatt` — under informational closure
(perfect foresight, every finite event tree) **every** bounded adapted equilibrium, for any
`(x_{−1}, e)`, is the steady state: `|x_t| + |x_t|³ = |E_t x_{t+1}| ≤ sup |x|` forces `x = 0`. -/
theorem Grep_unique {Ω : Type*} {𝔼 : ExpectationSystem Ω}
    (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {u : ParS (Fin 1) ℝ Ω} {x : SProcV (Fin 1) Ω}
    (hx : SolvesSV 𝔼 Grep u x) : x = 0 := by
  have hz : ∀ p : ℕ × Ω, x p 0 = 0 := by
    refine eq_zero_of_push (fun p : ℕ × Ω => x p 0) ⟨‖x‖, fun p => abs_apply_le x p.1 p.2 0⟩
      one_pos fun B hB p => ?_
    obtain ⟨t, ω⟩ := p
    have hE := congrFun (Grep_E hcl hx t) ω
    have hb := 𝔼.abs_E_le (fun ω' => hB (t + 1, ω')) t ω
    change |𝔼.E t (toP x (t + 1) 0) ω| ≤ B at hb
    rw [hE] at hb
    change |x (t, ω) 0 + x (t, ω) 0 ^ 3| ≤ B at hb
    have e : |x (t, ω) 0 + x (t, ω) 0 ^ 3| = |x (t, ω) 0| + |x (t, ω) 0| ^ 3 := by
      rw [show x (t, ω) 0 + x (t, ω) 0 ^ 3 = x (t, ω) 0 * (1 + x (t, ω) 0 ^ 2) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 + x (t, ω) 0 ^ 2), ← sq_abs]
      ring
    change |x (t, ω) 0| ^ 3 ≤ 1 * (B - |x (t, ω) 0|)
    linarith
  ext p i
  rw [Subsingleton.elim i 0]
  exact hz p

/-- **The unit-root case is not decided by the linearisation** (Woodford (2003), App. A.3,
pp. 632–634, correction): `Gatt` and `Grep` have the same operator (A.8), which is neither onto
nor bounded below (not one-to-one, range not closed); the first has genuinely random sunspot
equilibria at every scale on the coin tree, the second has none (indeed a unique bounded
equilibrium, the steady state) on the coin tree. -/
theorem unit_root_undecided :
    linOp Gatt = linOp Grep ∧ ¬ Function.Surjective (linOp Gatt) ∧
      ¬ Function.Injective (linOp Gatt) ∧ ¬ IsClosed (Set.range (linOp Gatt)) ∧
      (∀ ε > 0, ∃ x : SProcV (Fin 1) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Gatt 0 x ∧ ‖x‖ ≤ ε ∧
          x (1, (true, true)) ≠ x (1, (false, true))) ∧
      ∀ x : SProcV (Fin 1) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Grep 0 x → x = 0 :=
  ⟨linOp_Gatt_Grep.1, not_surjective_linOp_unit, not_injective_linOp_unit,
    not_isClosed_range_unit, fun _ hε => Gatt_random_sunspot hε,
    fun _ hx => Grep_unique (LocalIFTStochastic.finiteTree_infoClosed _) hx⟩

/-! ### A singular pencil (closed range): the same linearisation, opposite answers -/

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t[x_{t+1}³ − x_t³] = 0`. -/
def Gcub (p : Arg (Fin 1) ℝ) : Fin 1 → ℝ := fun _ => p.2.2.1 0 ^ 3 - p.2.1 0 ^ 3

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t[x_t³] = 0`. -/
def Gsta (p : Arg (Fin 1) ℝ) : Fin 1 → ℝ := fun _ => p.2.1 0 ^ 3

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (example): **both `Gcub` and `Gsta` have
operator (A.8) equal to zero** (`det(f₃λ² + f₂λ + f₁) ≡ 0`; the range `{0}` is closed). -/
theorem linOp_Gcub_Gsta : linOp Gcub = 0 ∧ linOp Gsta = 0 := by
  have hA : HasFDerivAt (pA : Arg (Fin 1) ℝ → ℝ) pA 0 := pA.hasFDerivAt
  have hB : HasFDerivAt (projB : Arg (Fin 1) ℝ → ℝ) projB 0 := projB.hasFDerivAt
  have hC : HasFDerivAt (pC : Arg (Fin 1) ℝ → ℝ) pC 0 := pC.hasFDerivAt
  have hE : HasFDerivAt (projE : Arg (Fin 1) ℝ → ℝ) projE 0 := projE.hasFDerivAt
  have hc : HasFDerivAt Gcub (0 : Arg (Fin 1) ℝ →L[ℝ] (Fin 1 → ℝ)) 0 := by
    refine hasFDerivAt_pi'' fun _ => ?_
    have h1 := (hC.pow 3).sub (hB.pow 3)
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [projB, pC]
  have hs : HasFDerivAt Gsta (0 : Arg (Fin 1) ℝ →L[ℝ] (Fin 1 → ℝ)) 0 := by
    refine hasFDerivAt_pi'' fun _ => ?_
    have h1 := hB.pow 3
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [projB]
  have hz : ∀ G : Arg (Fin 1) ℝ → (Fin 1 → ℝ), fderiv ℝ G 0 = 0 → linOp G = 0 := by
    intro G hG
    refine ContinuousLinearMap.ext fun v => seq_ext fun t => ?_
    rw [linOp_of_fderiv (a := 0) (b := 0) (c := 0) (d := 0) (fun p => by
      rw [hG]; funext i; simp) v t]
    funext i
    simp
  exact ⟨hz _ hc.fderiv, hz _ hs.fderiv⟩

/-- **Random sunspots with a singular pencil** (Woodford (2003), App. A.3, p. 634, example): for
`E_t[x_{t+1}³ − x_t³] = 0` (operator (A.8) zero), on the coin tree, for every `ε > 0`, the path
`x_0 = 0`, `x_t = ±a` (`t ≥ 1`) is a bounded adapted equilibrium within `ε` whose date-1 value
differs across the first flip. -/
theorem Gcub_random_sunspot {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV (Fin 1) (Bool × Bool), SolvesSV ExpectationsFiniteTree.coinSystem Gcub 0 x ∧
      ‖x‖ ≤ ε ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  set y : Bool → ℕ → ℝ := fun b _ => if b then ε else -ε with hy
  have hM : ∀ b t, |y b t| ≤ ε := fun b t => by cases b <;> simp [hy, abs_of_pos hε]
  refine ⟨brProc y hM, solvesSV_brProc (φ := fun z z' => z' ^ 3 - z ^ 3) (fun p => rfl) hM ?_
    (fun b t => ?_), norm_brProc_le hM hε.le, fun h => ?_⟩
  · simp [hy]
    ring
  · simp [hy]
  · have := congrFun h 0
    change ε = -ε at this
    linarith

/-- **No sunspots with the same (zero) linearisation** (Woodford (2003), App. A.3, p. 634,
example): under informational closure, every equilibrium of `E_t[x_t³] = 0` is the steady
state. -/
theorem Gsta_unique {Ω : Type*} {𝔼 : ExpectationSystem Ω}
    (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {u : ParS (Fin 1) ℝ Ω} {x : SProcV (Fin 1) Ω}
    (hx : SolvesSV 𝔼 Gsta u x) : x = 0 := by
  ext ⟨t, ω⟩ i
  rw [Subsingleton.elim i 0]
  have h := hx.2 t 0
  have hf : (fun ω => Gsta (ptS (u, x) (t, ω)) 0) = fun ω => toP x t 0 ω ^ 3 := rfl
  rw [hf, known_comp hcl (hx.1 t 0) (fun z => z ^ 3)] at h
  have h1 := congrFun h ω
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h1

/-- **A closed range does not decide either** (Woodford (2003), App. A.3, pp. 632–634,
correction): `Gcub` and `Gsta` have the same operator (A.8), zero (closed range, neither onto nor
one-to-one, singular pencil); the first has random sunspots at every scale on the coin tree, the
second has the steady state as its only bounded equilibrium there. -/
theorem singular_pencil_undecided :
    linOp Gcub = 0 ∧ linOp Gsta = 0 ∧
      (∀ ε > 0, ∃ x : SProcV (Fin 1) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Gcub 0 x ∧ ‖x‖ ≤ ε ∧
          x (1, (true, true)) ≠ x (1, (false, true))) ∧
      ∀ x : SProcV (Fin 1) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Gsta 0 x → x = 0 :=
  ⟨linOp_Gcub_Gsta.1, linOp_Gcub_Gsta.2, fun _ hε => Gcub_random_sunspot hε,
    fun _ hx => Gsta_unique (LocalIFTStochastic.finiteTree_infoClosed _) hx⟩

end Woodford.PriceLevelDetermination.SunspotsNotOntoExamples
