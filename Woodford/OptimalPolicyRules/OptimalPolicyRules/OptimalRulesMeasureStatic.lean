/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureIID

/-!
# A static problem: Assumption 8.1 in the book's form on a genuine infinite sample space

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541) and Proposition 8.2
(p. 555), for the simplest problem of the general form (1.1)–(1.4): one forward-looking variable
that does not enter expectations (`Ẽ = 0`, so (1.1) reads `0 = z_t + i_t + c_t`), no
predetermined variable, and the loss `½ (z_t² + i_t²)`. The first-order conditions (1.9) are
`M_t + z_t = 0`, `M_t + i_t = 0`, so `z_t = i_t = −c_t / 2`, `M_t = c_t / 2`.

## Main results

* `static_assumption81MB`: the corrected Assumption 8.1 holds on **every** probability space and
  filtration, at every `t₀`, for every bounded adapted disturbance.
* `static_coin_assumption81`: hence **the book's Assumption 8.1 holds as stated on the fair-coin
  economy at `t₀ = 0`** (a genuine infinite sample space), while it fails there at every
  `t₀ ≥ 1` (`static_coin_not_assumption81`) — the dividing line of
  `OptimalRulesMeasure.assumption81_iff` is attained on both sides.
* `static_pf`: the perfect-foresight Assumption 8.1 (the core statement), from the one-point
  probability space; `static_Hn`: the endogenous state transition is `H_n = 0`, so the
  existence theorem `OptimalRulesMeasureMarkov.m_existsUnique_var` applies to every VAR economy
  (`static_var`): its hypotheses are satisfiable.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureStatic

open MeasureTheory ProbabilityTheory Filter Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure ExpectationsMeasureIID OptimalRulesMeasure OptimalRulesMeasureMarkov
  OptimalRulesMeasureIID

/-- Woodford (2003), eq. (1.1), p. 537: the static structure `0 = z_t + i_t + c_t` (no
predetermined variable, `A₂₂ = 1`, `B₂ = 1`, `Ẽ = 0`). -/
noncomputable def staticSys : LinearRESystem Empty Unit where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := 1
  Et := 0
  B2 := fun _ => 1
  A22_isUnit := by simp
  B2_ne_zero := fun h => one_ne_zero (congrFun h ())

/-- Woodford (2003), eqs. (1.2)–(1.4), p. 537: the static problem with targets `τ = (z, i)`,
`W = I`, `τ* = 0`, `β = 1/2`. -/
noncomputable def staticP : LQProblem Empty Unit (Fin 2) where
  sys := staticSys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := Matrix.of fun a _ => if a = 0 then 1 else 0
  Ti := ![0, 1]
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), (1.4): the targets of the static problem are `τ = (z, i)`. -/
theorem static_T (v : (Empty ⊕ Unit) ⊕ Unit → ℝ) :
    staticP.T *ᵥ v = ![v (Sum.inl (Sum.inr ())), v (Sum.inr ())] := by
  funext a
  fin_cases a <;>
    simp [LQProblem.T, staticP, mulVec, dotProduct, Fintype.sum_sum_type]

/-- Woodford (2003), eq. (1.9), p. 541, for the static problem: the first-order conditions are
`M_t + z_t = 0` and `M_t + i_t = 0` (`p` = `E_t φ_{t+1}`, whose `M`-block is `M_t`). -/
theorem static_foc_iff (p : Empty ⊕ Unit → ℝ) (v : (Empty ⊕ Unit) ⊕ Unit → ℝ)
    (q : Empty ⊕ Unit → ℝ) :
    staticP.sys.Atilᵀ *ᵥ p + staticP.Tᵀ *ᵥ (staticP.W *ᵥ (staticP.T *ᵥ v - staticP.τstar)) -
        staticP.β⁻¹ • (staticP.sys.Itilᵀ *ᵥ q) = 0 ↔
      p (Sum.inr ()) + v (Sum.inl (Sum.inr ())) = 0 ∧ p (Sum.inr ()) + v (Sum.inr ()) = 0 := by
  set F := staticP.sys.Atilᵀ *ᵥ p + staticP.Tᵀ *ᵥ (staticP.W *ᵥ (staticP.T *ᵥ v - staticP.τstar)) -
    staticP.β⁻¹ • (staticP.sys.Itilᵀ *ᵥ q) with hF
  have h1 : F (Sum.inl (Sum.inr ())) = p (Sum.inr ()) + v (Sum.inl (Sum.inr ())) := by
    simp [hF, LQProblem.T, staticP, staticSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type]
  have h2 : F (Sum.inr ()) = p (Sum.inr ()) + v (Sum.inr ()) := by
    simp [hF, LQProblem.T, staticP, staticSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two]
  constructor
  · intro h
    exact ⟨h1 ▸ congrFun h _, h2 ▸ congrFun h _⟩
  · rintro ⟨e1, e2⟩
    funext idx
    rcases idx with (e | u) | u
    · exact e.elim
    · rw [h1, e1]
      rfl
    · rw [h2, e2]
      rfl


/-- Woodford (2003), eq. (1.1), p. 537, for the static problem: the expectational row is
`0 = z_t + i_t + c_t` (whatever the forecast, since `Ẽ = 0`). -/
theorem static_struct_iff (w : Unit → ℝ) (Z : Empty → ℝ) (z : Unit → ℝ) (i : ℝ) (cc : Unit → ℝ) :
    staticP.sys.Et *ᵥ w = staticP.sys.A21 *ᵥ Z + staticP.sys.A22 *ᵥ z + i • staticP.sys.B2 + cc ↔
      z () + i + cc () = 0 := by
  have h : ∀ u : Unit, (staticP.sys.A21 *ᵥ Z + staticP.sys.A22 *ᵥ z + i • staticP.sys.B2 + cc) u =
      z () + i + cc () := by
    intro u
    simp [staticP, staticSys]
  have h0 : staticP.sys.Et *ᵥ w = 0 := by simp [staticP, staticSys]
  rw [h0]
  constructor
  · intro e
    have := congrFun e ()
    rw [h] at this
    simp only [Pi.zero_apply] at this
    linarith
  · intro e
    funext u
    rw [h]
    simp only [Pi.zero_apply]
    linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Woodford (2003), (1.5): the plan of the static problem, `z_t = i_t = −c_t / 2`. -/
noncomputable def staticY (c : ℕ → Ω → Unit → ℝ) : ℕ → Ω → (Empty ⊕ Unit) ⊕ Unit → ℝ :=
  fun t ω _ => -(c t ω ()) / 2

/-- Woodford (2003), (1.9): the multipliers of the static problem, `M_t = c_t / 2` for `t ≥ t₀`
and the given `M_{t₀−1}`. -/
noncomputable def staticΦ (c : ℕ → Ω → Unit → ℝ) (M0 : Ω → Unit → ℝ) (t0 : ℕ) :
    ℕ → Ω → Empty ⊕ Unit → ℝ :=
  fun t ω _ => if t0 < t then c (t - 1) ω () / 2 else if t = t0 then M0 ω () else 0

/-- Woodford (2003), Assumption 8.1 (existence), p. 541, for the static problem: on every
probability space, for every bounded adapted disturbance and every bounded `M_{t₀−1}` known at
`t₀ − 1`, `(staticY, staticΦ)` solves (1.1) + (1.9). -/
theorem static_solvable (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    MFOCSolvableMB S staticP t0 := by
  intro c Z0 M0 hcb hca _ _ hMb hMk
  obtain ⟨Kc, hKc⟩ := hcb
  obtain ⟨KM, hKM⟩ := hMb
  have hci : ∀ t, Integrable (fun ω => c t ω ()) S.μ := fun t =>
    integrable_of_bound ((hca t ()).mono (S.𝓕.le t)).aestronglyMeasurable
      ((hKc t).mono fun ω h => h ())
  refine ⟨staticY c, staticΦ c M0 t0, ⟨fun t _ => ⟨Eventually.of_forall fun ω =>
    funext fun e => e.elim, Eventually.of_forall fun ω => ?_⟩,
    Eventually.of_forall fun ω => funext fun e => e.elim, ⟨|Kc|, fun t => ?_⟩, fun t i => ?_⟩,
    ⟨max |Kc| |KM|, fun t => ?_⟩, fun t i => ?_, fun t r => ?_,
    Eventually.of_forall fun ω => ?_, fun t ht => ?_⟩
  · refine (static_struct_iff _ _ _ _ _).mpr ?_
    simp only [staticY, zpart, ipart]
    ring
  · filter_upwards [hKc t] with ω h i
    have := h ()
    simp only [staticY]
    rw [abs_div, abs_neg, abs_two]
    linarith [abs_nonneg (c t ω ()), le_abs_self Kc]
  · exact ((hca t ()).measurable.neg.div_const 2).stronglyMeasurable
  · filter_upwards [hKc (t - 1), hKM] with ω h1 h2 i
    have e1 := h1 ()
    have e2 := h2 ()
    simp only [staticΦ]
    split_ifs
    · rw [abs_div, abs_two]
      linarith [abs_nonneg (c (t - 1) ω ()), le_abs_self Kc, le_max_left |Kc| |KM|]
    · linarith [le_abs_self KM, le_max_right |Kc| |KM|]
    · simp
  · by_cases h1 : t0 < t
    · simp only [staticΦ, h1, ↓reduceIte]
      exact (((hca (t - 1) ()).mono (S.𝓕.le _)).measurable.div_const 2).aestronglyMeasurable
    · by_cases h2 : t = t0
      · simp only [staticΦ, h2, lt_irrefl, ↓reduceIte]
        exact ((hMk ()).mono (S.𝓕.le _)).aestronglyMeasurable
      · simp only [staticΦ, h1, h2, ↓reduceIte]
        exact aestronglyMeasurable_const
  · by_cases h1 : t0 < t + 1
    · simp only [staticΦ, h1, ↓reduceIte, Nat.add_sub_cancel]
      exact ((hca t ()).measurable.div_const 2).stronglyMeasurable
    · by_cases h2 : t + 1 = t0
      · simp only [staticΦ, h2, lt_irrefl, ↓reduceIte]
        have := hMk ()
        rwa [show t0 - 1 = t by omega] at this
      · simp only [staticΦ, h1, h2, ↓reduceIte]
        exact stronglyMeasurable_const
  · funext r
    simp [staticΦ, Mpart]
  · have hfun : (fun ω => staticΦ c M0 t0 (t + 1) ω (Sum.inr ())) = fun ω => c t ω () / 2 := by
      funext ω
      simp only [staticΦ, show t0 < t + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
    have hE : S.E t (fun ω => staticΦ c M0 t0 (t + 1) ω (Sum.inr ())) =
        fun ω => c t ω () / 2 := by
      rw [hfun]
      exact S.E_of_stronglyMeasurable ((hca t ()).measurable.div_const 2).stronglyMeasurable
        ((hci t).div_const 2)
    refine Eventually.of_forall fun ω => (static_foc_iff _ _ _).mpr ?_
    have hp : EVm S t (staticΦ c M0 t0 (t + 1)) ω (Sum.inr ()) = c t ω () / 2 :=
      congrFun hE ω
    rw [hp]
    simp only [staticY]
    constructor <;> ring

/-- Woodford (2003), pp. 541–542, for the static problem: every bounded solution of
(1.1) + (1.9) has `z_t = i_t = −c_t / 2` and `M_t = c_t / 2` a.s. for all `t ≥ t₀`. -/
theorem static_sol {S : MeasExpectationSystem Ω} {c : ℕ → Ω → Unit → ℝ} {t0 : ℕ}
    {Z0 : Ω → Empty → ℝ} {M0 : Ω → Unit → ℝ} {y : ℕ → Ω → (Empty ⊕ Unit) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → Empty ⊕ Unit → ℝ} (h : MFOCSystem S staticP c t0 Z0 M0 y φ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      y t ω = staticY c t ω ∧ φ (t + 1) ω (Sum.inr ()) = c t ω () / 2 := by
  intro t ht
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  have hE : S.E t (fun ω => φ (t + 1) ω (Sum.inr ())) = fun ω => φ (t + 1) ω (Sum.inr ()) :=
    S.E_of_stronglyMeasurable (h.2.2.2.1 t ()) (integrable_of_bound (h.2.2.1 (t + 1) _)
      ((hKφ (t + 1)).mono fun ω h => h _))
  filter_upwards [(h.1.1 t ht).2, h.2.2.2.2.2 t ht] with ω e1 e2
  have hs := (static_struct_iff _ _ _ _ _).mp e1
  obtain ⟨f1, f2⟩ := (static_foc_iff _ _ _).mp e2
  have hp : EVm S t (φ (t + 1)) ω (Sum.inr ()) = φ (t + 1) ω (Sum.inr ()) := congrFun hE ω
  rw [hp] at f1 f2
  simp only [zpart, ipart] at hs
  refine ⟨funext fun idx => ?_, by linarith⟩
  rcases idx with (e | u) | u
  · exact e.elim
  · simp only [staticY]
    linarith
  · simp only [staticY]
    linarith

/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541, for the static problem, on every
probability space. -/
theorem static_unique (S : MeasExpectationSystem Ω) (t0 : ℕ) : MFOCUnique S staticP t0 := by
  intro c Z0 M0 y y' φ φ' h h' t ht
  refine ⟨?_, ?_⟩
  · filter_upwards [static_sol h t ht, static_sol h' t ht] with ω e1 e2
    rw [e1.1, e2.1]
  · rcases Nat.eq_or_lt_of_le ht with h0 | h0
    · subst h0
      filter_upwards [h.2.2.2.2.1, h'.2.2.2.2.1] with ω e1 e2
      funext idx
      rcases idx with e | u
      · exact e.elim
      · exact (congrFun e1 u).trans (congrFun e2 u).symm
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
      filter_upwards [static_sol h k (by omega), static_sol h' k (by omega)] with ω e1 e2
      funext idx
      rcases idx with e | u
      · exact e.elim
      · exact e1.2.trans e2.2.symm

/-- Woodford (2003), **Assumption 8.1**, p. 541, for the static problem: the corrected form holds on
every probability space, at every `t₀`. -/
theorem static_assumption81MB (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    MAssumption81MB S staticP t0 :=
  ⟨static_solvable S t0, static_unique S t0⟩

/-- Woodford (2003), **Assumption 8.1 as stated in the book**, p. 541: for the static problem it
**holds on the fair-coin economy at `t₀ = 0`** — a genuine infinite sample space, every history
null — because there both information conditions of `OptimalRulesMeasure.assumption81_iff`
hold. -/
theorem static_coin_assumption81 : MAssumption81 (iidSystem coin) staticP 0 :=
  (coin_assumption81_zero_iff staticP).mpr (static_assumption81MB _ 0)

/-- Woodford (2003), Assumption 8.1 as stated in the book, p. 541: for the same problem on the same
economy it **fails at every `t₀ ≥ 1`** (genuine news at `t₀`). -/
theorem static_coin_not_assumption81 {t0 : ℕ} (ht0 : 1 ≤ t0) :
    ¬ MAssumption81 (iidSystem coin) staticP t0 :=
  coin_not_assumption81 staticP ht0

/-- Woodford (2003), Assumption 8.1, p. 541, under perfect foresight (the core statement
`GeneralFOC.LQ.Assumption81`), for the static problem: the measure-theoretic result on the
one-point probability space (`OptimalRulesMeasure.Bridge.unit_assumption81_iff`). -/
theorem static_pf : Assumption81 staticP perfectForesight 0 :=
  (Bridge.unit_assumption81_iff staticP 0).mp (assumption81_iff.mpr
    ⟨static_assumption81MB _ 0, Bridge.bddInfo_of_finite 0, predInfo_zero _⟩)

variable {ιs : Type*} [Fintype ιs] [DecidableEq ιs]

/-- Woodford (2003), (1.9) under perfect foresight: from any state `X`, the next lagged
multiplier of the static problem is `M_0 = c_0 / 2 = (C₂ s)/2`, whatever the endogenous state. -/
theorem static_nextN (A : Matrix ιs ιs ℝ) (C2 : Matrix Unit ιs ℝ) (hA : PowBdd A)
    (X : (Empty ⊕ Unit) ⊕ ιs → ℝ) :
    nextN staticP A C2 static_pf hA X (Sum.inr ()) = (C2 *ᵥ Xs X) () / 2 := by
  obtain ⟨⟨hst, -, -, -⟩, -, -, -, hfoc⟩ := pf_spec staticP A C2 static_pf hA X
  have hs := (static_struct_iff _ _ _ _ _).mp (hst 0 le_rfl ()).2
  obtain ⟨f1, f2⟩ := (static_foc_iff _ _ _).mp (hfoc 0 le_rfl ())
  simp only [zpart, ipart, cpf, pow_zero, one_mulVec] at hs
  change pfΦ staticP A C2 static_pf hA X 1 () (Sum.inr ()) + _ = 0 at f1
  change pfΦ staticP A C2 static_pf hA X 1 () (Sum.inr ()) + _ = 0 at f2
  change pfΦ staticP A C2 static_pf hA X 1 () (Sum.inr ()) = _
  linarith

/-- Woodford (2003), p. 539: for the static problem the endogenous state transition is
`H_n = 0`. -/
theorem static_Hn (A : Matrix ιs ιs ℝ) (C2 : Matrix Unit ιs ℝ) (hA : PowBdd A) :
    Hn staticP A C2 static_pf hA = 0 := by
  funext i j
  rw [Hn_apply]
  rcases i with e | u
  · exact e.elim
  · rw [static_nextN, static_nextN]
    have h1 : Xs (mkX (Pi.single j 1) (0 : ιs → ℝ)) = 0 := rfl
    have h2 : Xs (mkX (0 : Empty ⊕ Unit → ℝ) (0 : ιs → ℝ)) = 0 := rfl
    rw [h1, h2]
    simp

/-- Woodford (2003), App. G.1 (tool): the zero matrix has geometrically decaying powers. -/
theorem powDecay_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    PencilSplit.PowDecay (0 : Matrix ι ι ℝ) := by
  refine ⟨1, 0, le_rfl, zero_lt_one, fun k i j => ?_⟩
  rcases k with _ | k
  · rw [pow_zero, pow_zero, one_mul]
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.one_apply_ne h]
      simp
  · simp [zero_pow (Nat.succ_ne_zero k)]

/-- Woodford (2003), **Assumption 8.1 and Proposition 8.2 for the static problem on every VAR
economy**: the hypotheses of `OptimalRulesMeasureMarkov.m_existsUnique_var` hold (`static_pf`,
`static_Hn`), so on every probability space with a VAR(1) exogenous state there is an a.s.
unique bounded solution of (1.1) + (1.9), optimal from a timeless perspective with
`X̄_t = (M_{t−1}, s_t)`. -/
theorem static_var {Ω : Type*} [MeasurableSpace Ω] (A : Matrix ιs ιs ℝ) (C2 : Matrix Unit ιs ℝ)
    (hA : PowBdd A) {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {t0 : ℕ} {Z0 : Ω → Empty → ℝ} {M0 : Ω → Unit → ℝ} (hZk : MKnownV S t0 Z0)
    (hZb : MBoundedRV S Z0) (hMb : MBoundedRV S M0) (hMk : MKnownV S (t0 - 1) M0) :
    ∃ y φ, MFOCSystem S staticP (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ ∧
      (∀ y' φ', MFOCSystem S staticP (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y' φ' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t ∧ φ' t =ᵐ[S.μ] φ t) ∧
      MTimelesslyOptimalPlan S staticP (fun t ω => C2 *ᵥ s t ω) t0 Z0 (stateX y φ s)
        (zpart (fY staticP A C2 static_pf hA))
        ((FY staticP A C2 static_pf hA).submatrix (Sum.inl ∘ Sum.inr) id) y :=
  m_existsUnique_var staticP A C2 static_pf hA (by rw [static_Hn]; exact powDecay_zero) hs hZk
    hZb hMb hMk

end Woodford.OptimalPolicyRules.OptimalRulesMeasureStatic
