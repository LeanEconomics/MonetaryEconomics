/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bFOCMeanSq
import OptimalPolicyRules.ExpectationsMeasure

/-!
# Faithfulness is needed for the pointwise first-order conditions

Woodford (2003), *Interest and Prices*, Chapter 8, §1.1, p. 541: the first-order conditions
(1.9) are necessary for an optimal plan.

`TidyR5bFOCMeanSq.foc_necessary_meanSq` proves (1.9) in conditional mean square without any
faithfulness hypothesis, and `TidyR5bFOCMeanSq.foc_of_meanSq` recovers the pointwise form
when the expectations are faithful. This module settles whether faithfulness can be dropped.

* `faithful_needed` (**it cannot**): a two-state expectation system `nfSys` (`E₀` looks only at
  the state `true`; `E_t` for `t ≥ 1` is the identity) satisfies the pull-out property and
  `FOCSolvable` for the one-variable problem `nfProblem`, but is not faithful; the plan `yb`
  (zero, except `z_t = 1` from date `1` on in the null state `false`) is optimal, and no bounded
  multipliers with `M_t` known at `t` satisfy (1.9) at every state.
* `foc_ae_of_meanSq`: what survives — if the expectations are faithful **almost surely** for a
  measure `μ`, the optimum satisfies (1.9) `μ`-almost surely at every date.
* `condExp_aeFaithful`, `foc_ae_of_version`: Mathlib's conditional expectation on a filtered
  probability space is faithful almost surely, so on the conditional-expectation model the
  mean-square form is the almost-sure form.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bFaithNeeded

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ TidyR5bFOCMeanSq
open ExpectationTools (Faithful)

/-! ### A non-faithful expectation system -/

/-- Woodford (2003), p. 541 (tool): the operator `E_t` of `nfSys`: at `t = 0` the value at the
state `true`; at `t ≥ 1` the identity. -/
def nfE (t : ℕ) : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) where
  toFun x := fun ω => if t = 0 then x true else x ω
  map_add' x y := by
    funext ω
    by_cases h : t = 0 <;> simp [h]
  map_smul' c x := by
    funext ω
    by_cases h : t = 0 <;> simp [h]

/-- Woodford (2003), p. 541: a two-state expectation system in which the state `false` is null
at date `0` and revealed from date `1` on. -/
def nfSys : ExpectationSystem Bool where
  E := nfE
  const := fun t c => by
    funext ω
    by_cases h : t = 0 <;> simp [nfE, h]
  mono := fun t x y hxy ω => by
    by_cases h : t = 0 <;> simp [nfE, h, hxy true, hxy ω]
  tower := fun {s t} hst x => by
    funext ω
    by_cases hs : s = 0 <;> by_cases ht : t = 0 <;> simp [nfE, hs, ht]
    omega
  known := fun {s t} hst x => by
    funext ω
    by_cases hs : s = 0 <;> by_cases ht : t = 0 <;> simp [nfE, hs, ht]
    omega

/-- Woodford (2003), p. 541: the operators of `nfSys`. -/
theorem nf_E (t : ℕ) (x : Bool → ℝ) (ω : Bool) :
    nfSys.E t x ω = if t = 0 then x true else x ω := rfl

/-- Woodford (2003), p. 541: `nfSys` has the pull-out property. -/
theorem nf_pullOut : nfSys.PullOut := by
  intro t a y ha
  funext ω
  have hω := congrFun ha ω
  rw [nf_E] at hω
  by_cases h : t = 0
  · simp only [h, ↓reduceIte] at hω
    simp [nf_E, h, hω]
  · simp [nf_E, h]

/-- Woodford (2003), p. 541: `nfSys` is not faithful (`E₀` ignores the state `false`). -/
theorem nf_not_faithful : ¬ Faithful nfSys := by
  intro h
  have := congrFun (h 0 (fun ω => if ω then 0 else 1) (fun ω => by cases ω <;> simp)
    (by funext ω; simp [nf_E])) false
  simp at this

/-! ### A one-variable problem -/

/-- Woodford (2003), (1.1) (tool): one forward-looking variable, no predetermined one:
`E_t z_{t+1} = z_t + i_t + c_t`. -/
noncomputable def nfRE : LinearRESystem Empty Unit where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := 1
  Et := 1
  B2 := fun _ => 1
  A22_isUnit := by simp
  B2_ne_zero := fun h => by simpa using congrFun h ()

/-- Woodford (2003), (1.1)–(1.4) (tool): the problem `min E₀ ∑ βᵗ ½ z_t²` subject to `nfRE`,
`β = ½`. -/
noncomputable def nfProblem : LQProblem Empty Unit Unit where
  sys := nfRE
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := Matrix.of fun _ r => Sum.elim (fun _ => 0) (fun _ => 1) r
  Ti := 0
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), (1.9) (tool): the residual of (1.9) for `nfProblem`, componentwise: the
instrument row is `E_t M_t`, the `z` row is `E_t M_t + z_t − 2 M_{t−1}`. -/
theorem nf_foc_apply (p q : Empty ⊕ Unit → ℝ) (v : (Empty ⊕ Unit) ⊕ Unit → ℝ) :
    (nfProblem.sys.Atilᵀ *ᵥ p + nfProblem.Tᵀ *ᵥ (nfProblem.W *ᵥ (nfProblem.T *ᵥ v -
      nfProblem.τstar)) - nfProblem.β⁻¹ • (nfProblem.sys.Itilᵀ *ᵥ q)) (Sum.inr ()) =
        p (Sum.inr ()) ∧
    (nfProblem.sys.Atilᵀ *ᵥ p + nfProblem.Tᵀ *ᵥ (nfProblem.W *ᵥ (nfProblem.T *ᵥ v -
      nfProblem.τstar)) - nfProblem.β⁻¹ • (nfProblem.sys.Itilᵀ *ᵥ q)) (Sum.inl (Sum.inr ())) =
        p (Sum.inr ()) + v (Sum.inl (Sum.inr ())) - 2 * q (Sum.inr ()) := by
  constructor <;>
  simp [nfProblem, nfRE, LinearRESystem.Atil, LinearRESystem.Ahat, LinearRESystem.Itil,
    LinearRESystem.Ihat, LinearRESystem.Bvec, LQProblem.T, mulVec, dotProduct, fromCols,
    fromBlocks, Fintype.sum_sum_type, Matrix.mul_apply]

/-- Woodford (2003), (1.1) (tool): the structural equation of `nfProblem` at the `z` row. -/
theorem nf_struct_iff (c : ℕ → Bool → Unit → ℝ) (y : ℕ → Bool → (Empty ⊕ Unit) ⊕ Unit → ℝ)
    (t : ℕ) :
    nfProblem.sys.Structural nfSys c t y ↔ ∀ s, t ≤ s → ∀ ω,
      nfSys.E s (fun ω' => y (s + 1) ω' (Sum.inl (Sum.inr ()))) ω =
        y s ω (Sum.inl (Sum.inr ())) + y s ω (Sum.inr ()) + c s ω () := by
  constructor
  · intro h s hs ω
    have := congrFun (h s hs ω).2 ()
    simpa [nfProblem, nfRE, EV, zpart, Zpart, ipart, mulVec, dotProduct] using this
  · intro h s hs ω
    refine ⟨funext fun e => e.elim, funext fun _ => ?_⟩
    have := h s hs ω
    simpa [nfProblem, nfRE, EV, zpart, Zpart, ipart, mulVec, dotProduct] using this

/-! ### The plan and the failure of (1.9) -/

/-- Woodford (2003), p. 541 (tool): the plan `yb`: `z_t = 1` for `t ≥ 1` in the state `false`,
everything else zero. -/
noncomputable def yb : ℕ → Bool → (Empty ⊕ Unit) ⊕ Unit → ℝ :=
  fun t ω v => match v with
    | Sum.inl (Sum.inr _) => if 1 ≤ t ∧ ω = false then 1 else 0
    | _ => 0

/-- Woodford (2003), (1.3) (tool): the period loss of `nfProblem` is `½ z²`. -/
theorem nf_loss (v : (Empty ⊕ Unit) ⊕ Unit → ℝ) :
    nfProblem.loss v = (1 / 2) * v (Sum.inl (Sum.inr ())) ^ 2 := by
  simp [LQProblem.loss, nfProblem, LQProblem.T, mulVec, dotProduct, fromCols,
    Fintype.sum_sum_type]
  ring

/-- Woodford (2003), (1.1): `yb` is feasible (from `t₀ = 0`, with no disturbance). -/
theorem yb_feasible : nfProblem.Feasible nfSys (fun _ _ _ => 0) 0 (fun _ e => e.elim) yb := by
  refine ⟨(nf_struct_iff _ _ 0).mpr fun s _ ω => ?_, fun ω => funext fun e => e.elim,
    ⟨1, fun t ω v => ?_⟩, fun t i => ?_⟩
  · rw [nf_E]
    by_cases hs : s = 0
    · subst hs
      simp [yb]
    · simp only [hs, ↓reduceIte, yb]
      have h1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
      by_cases hω : ω = false <;> simp [hω, h1]
  · rcases v with (e | u) | u
    · exact e.elim
    · simp only [yb]
      split_ifs <;> norm_num
    · simp [yb]
  · funext ω
    rw [nf_E]
    by_cases ht : t = 0
    · subst ht
      rcases i with (e | u) | u
      · exact e.elim
      · simp [yb]
      · simp [yb]
    · simp [ht]

/-- Woodford (2003), (1.2): `yb` is optimal: its expected loss `E₀ ∑ βᵗ L` is `0` (the state
`false`, where `yb` is costly, is null at date `0`), and every expected loss is `≥ 0`. -/
theorem yb_optimal :
    nfProblem.OptimalSubjectTo nfSys (fun _ _ _ => 0) 0 (fun _ e => e.elim) 0 yb := by
  refine ⟨yb_feasible, fun ω => funext fun _ => ?_, fun y' _ _ ω => ?_⟩
  · simp [nfProblem, nfRE, zpart, yb, mulVec, dotProduct]
  · have h0 : nfProblem.J nfSys 0 yb ω = 0 := by
      simp only [LQProblem.J, nf_E, ↓reduceIte, nf_loss, zero_add]
      simp [yb]
    rw [h0, LQProblem.J, nf_E, ite_eq_left rfl]
    refine tsum_nonneg fun k => mul_nonneg (pow_nonneg (by norm_num [nfProblem]) _) ?_
    rw [nf_loss]
    positivity

/-- Woodford (2003), p. 541 (**the pointwise (1.9) fails**): no bounded multipliers with `M_t`
known at `t` satisfy (1.9) for `yb` at every state. -/
theorem yb_no_foc :
    ¬ ∃ φ : ℕ → Bool → Empty ⊕ Unit → ℝ, BoundedV φ ∧ MultiplierMeas nfSys φ ∧
      PFOC nfProblem nfSys 0 yb φ := by
  rintro ⟨φ, -, hm, hfoc⟩
  have row : ∀ t ω, nfSys.E t (fun ω' => φ (t + 1) ω' (Sum.inr ())) ω = 0 ∧
      nfSys.E t (fun ω' => φ (t + 1) ω' (Sum.inr ())) ω + yb t ω (Sum.inl (Sum.inr ())) -
        2 * φ t ω (Sum.inr ()) = 0 := by
    intro t ω
    have h := hfoc t (Nat.zero_le t) ω
    obtain ⟨e1, e2⟩ := nf_foc_apply (EV nfSys t (φ (t + 1)) ω) (φ t ω) (yb t ω)
    rw [h, Pi.zero_apply] at e1 e2
    exact ⟨e1.symm, e2.symm⟩
  have h10 : φ 1 true (Sum.inr ()) = 0 := by
    have := (row 0 true).1
    rwa [nf_E, ite_eq_left rfl] at this
  have h1f : φ 1 false (Sum.inr ()) = 0 := by
    have := congrFun (hm 0 ()) false
    rw [nf_E, ite_eq_left rfl] at this
    rw [← this, h10]
  have h2f : φ 2 false (Sum.inr ()) = 0 := by
    have := (row 1 false).1
    rwa [nf_E, ite_eq_right one_ne_zero] at this
  have := (row 1 false).2
  rw [nf_E, ite_eq_right one_ne_zero, h2f, h1f] at this
  simp [yb] at this

/-- Woodford (2003), p. 541: `FOCSolvable` holds for `nfProblem` under `nfSys` (so
`TidyR5bFOCMeanSq.foc_necessary_meanSq` applies): `M_{−1} = M₀`, `M_t = 0` afterwards,
`z₀ = 2M₀`, `z_t = 0` afterwards. -/
theorem nf_solvable : FOCSolvable nfProblem nfSys 0 := by
  intro c Z0 M0 hcb hca _ hM0
  have hM : ∀ ω, M0 ω () = M0 true () := fun ω => by
    have := congrFun (hM0 ()) ω
    rw [nf_E, ite_eq_left rfl] at this
    exact this.symm
  have hc0 : ∀ ω, c 0 ω () = c 0 true () := fun ω => by
    have := congrFun (hca 0 ()) ω
    rw [nf_E, ite_eq_left rfl] at this
    exact this.symm
  set z : ℕ → Bool → ℝ := fun t ω => if t = 0 then 2 * M0 ω () else 0 with hz
  set y : ℕ → Bool → (Empty ⊕ Unit) ⊕ Unit → ℝ := fun t ω v => match v with
    | Sum.inl (Sum.inr _) => z t ω
    | Sum.inr _ => -z t ω - c t ω ()
    | Sum.inl (Sum.inl e) => e.elim with hy
  set φ : ℕ → Bool → Empty ⊕ Unit → ℝ := fun t ω r => match r with
    | Sum.inr _ => if t = 0 then M0 ω () else 0
    | Sum.inl e => e.elim with hφ
  obtain ⟨Kc, hKc⟩ := hcb
  refine ⟨y, φ, ⟨(nf_struct_iff _ _ 0).mpr fun s _ ω => ?_, fun ω => funext fun e => e.elim,
    ⟨2 * |M0 true ()| + Kc + 1, fun t ω v => ?_⟩, fun t i => ?_⟩,
    ⟨|M0 true ()|, fun t ω r => ?_⟩, fun t r => ?_, fun ω => ?_, fun t _ ω => ?_⟩
  · rw [nf_E]
    simp only [hy, hz]
    split_ifs <;> (simp_all; try ring)
  · have hK0 : 0 ≤ Kc := (abs_nonneg _).trans (hKc 0 true ())
    rcases v with (e | u) | u
    · exact e.elim
    · simp only [hy, hz]
      split_ifs
      · rw [hM, abs_mul, abs_two]
        linarith [abs_nonneg (M0 true ())]
      · simp only [abs_zero]
        linarith [abs_nonneg (M0 true ())]
    · simp only [hy, hz]
      have := hKc t ω ()
      split_ifs
      · rw [hM]
        calc |-(2 * M0 true ()) - c t ω ()| ≤ |-(2 * M0 true ())| + |c t ω ()| := abs_sub _ _
          _ ≤ _ := by rw [abs_neg, abs_mul, abs_two]; linarith
      · rw [neg_zero, zero_sub, abs_neg]
        linarith [abs_nonneg (M0 true ())]
  · funext ω
    rw [nf_E]
    by_cases ht : t = 0
    · subst ht
      rcases i with (e | u) | u
      · exact e.elim
      · simp [hy, hz, hM ω]
      · simp [hy, hz, hM ω, hc0 ω]
    · simp [ht]
  · rcases r with e | u
    · exact e.elim
    · simp only [hφ]
      split_ifs
      · rw [hM]
      · simp
  · funext ω
    simp [nf_E, hφ]
  · funext r
    simp [hφ, Mpart]
  · funext v
    obtain ⟨e1, e2⟩ := nf_foc_apply (EV nfSys t (φ (t + 1)) ω) (φ t ω) (y t ω)
    rcases v with (e | u) | u
    · exact e.elim
    · rw [e2]
      simp [EV, nf_E, hφ, hy, hz]
    · rw [e1]
      simp [EV, nf_E, hφ]

/-- Woodford (2003), p. 541 (**faithfulness is needed for the pointwise first-order
conditions**): `nfSys` has the pull-out property and `FOCSolvable` holds for `nfProblem`
(the hypotheses of `TidyR5bFOCMeanSq.foc_necessary_meanSq`), `nfSys` is not faithful, `yb` is
optimal, and no bounded multipliers with `M_t` known at `t` satisfy (1.9) pointwise for `yb`. -/
theorem faithful_needed :
    nfSys.PullOut ∧ FOCSolvable nfProblem nfSys 0 ∧ ¬ Faithful nfSys ∧
      nfProblem.OptimalSubjectTo nfSys (fun _ _ _ => 0) 0 (fun _ e => e.elim) 0 yb ∧
      ¬ ∃ φ : ℕ → Bool → Empty ⊕ Unit → ℝ, BoundedV φ ∧ MultiplierMeas nfSys φ ∧
        PFOC nfProblem nfSys 0 yb φ :=
  ⟨nf_pullOut, nf_solvable, nf_not_faithful, yb_optimal, yb_no_foc⟩

/-! ### The almost-sure form -/

open MeasureTheory

/-- Woodford (2003), p. 541 (almost-sure faithfulness): a nonnegative variable with zero
conditional expectation vanishes `μ`-almost surely. -/
def AEFaithful {Ω : Type*} [MeasurableSpace Ω] (𝔼 : ExpectationSystem Ω) (μ : Measure Ω) :
    Prop :=
  ∀ t (x : Ω → ℝ), 0 ≤ x → 𝔼.E t x = 0 → x =ᵐ[μ] 0

/-- Woodford (2003), p. 541 (**(1.9) almost surely**): if the expectations are faithful
almost surely for `μ`, the conditional-mean-square form of
`TidyR5bFOCMeanSq.foc_necessary_meanSq` gives (1.9) `μ`-almost surely at every date `t ≥ t₀`. -/
theorem foc_ae_of_meanSq {Ω : Type*} [MeasurableSpace Ω] {ιZ ιz ιτ : Type*} [Fintype ιZ]
    [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {μ : Measure Ω} (hae : AEFaithful 𝔼 μ) {t0 : ℕ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : ∀ t, t0 ≤ t → ∀ ω i, 𝔼.E t0 (fun ω' => res P 𝔼 y φ t ω' i ^ 2) ω = 0) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂μ, res P 𝔼 y φ t ω = 0 := by
  intro t ht
  have hi : ∀ i, (fun ω => res P 𝔼 y φ t ω i ^ 2) =ᵐ[μ] 0 := fun i =>
    hae t0 _ (fun ω => sq_nonneg _) (funext fun ω => h t ht ω i)
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  funext i
  exact pow_eq_zero_iff two_ne_zero |>.mp (hω i)

/-- Woodford (2003), p. 541 (**the optimum satisfies (1.9) almost surely**): under the
hypotheses of `TidyR5bFOCMeanSq.foc_necessary_meanSq` and almost-sure faithfulness, an optimal
plan has bounded multipliers satisfying (1.9) `μ`-almost surely at every date. -/
theorem foc_necessary_ae {Ω : Type*} [MeasurableSpace Ω] {ιZ ιz ιτ : Type*} [Fintype ιZ]
    [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {μ : Measure Ω} (hae : AEFaithful 𝔼 μ) {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    {ebar : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.OptimalSubjectTo 𝔼 c t0 Z0 ebar y) :
    ∃ φ : ℕ → Ω → ιZ ⊕ ιz → ℝ, BoundedV φ ∧ MultiplierMeas 𝔼 φ ∧
      ∀ t, t0 ≤ t → ∀ᵐ ω ∂μ, res P 𝔼 y φ t ω = 0 := by
  obtain ⟨-, φ, -, -, -, hb, hm, -, h⟩ := foc_necessary_meanSq hsolv hpull hbc hac hy
  exact ⟨φ, hb, hm, foc_ae_of_meanSq hae h⟩

/-- Woodford (2003), p. 541, on a filtered probability space (module ExpectationsMeasure): Mathlib's
conditional expectation is faithful almost surely — an integrable `x ≥ 0` a.s. with
`E_t x = 0` a.s. vanishes a.s. (`∫ x = ∫ E_t x = 0`). -/
theorem condExp_aeFaithful {Ω : Type*} [MeasurableSpace Ω]
    (S : ExpectationsMeasure.MeasExpectationSystem Ω) (t : ℕ) {x : Ω → ℝ}
    (hx : Integrable x S.μ) (h0 : 0 ≤ᵐ[S.μ] x) (hE : S.E t x =ᵐ[S.μ] 0) : x =ᵐ[S.μ] 0 := by
  have hint : ∫ ω, x ω ∂S.μ = 0 := by
    rw [← S.integral_E t x, integral_congr_ae hE]
    simp
  exact (integral_eq_zero_iff_of_nonneg_ae h0 hx).mp hint

/-- Woodford (2003), p. 541, **on the conditional-expectation model**: if the exact operators
`𝔼.E t` are versions of Mathlib's conditional expectations of a filtered probability space
(`𝔼.E t x = E[x | 𝓕_t]` a.s. for integrable `x`), the conditional-mean-square form of (1.9) is
(1.9) almost surely at every date (for plans whose squared residuals are integrable, e.g.
measurable bounded ones). -/
theorem foc_ae_of_version {Ω : Type*} [MeasurableSpace Ω] {ιZ ιz ιτ : Type*} [Fintype ιZ]
    [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} (S : ExpectationsMeasure.MeasExpectationSystem Ω)
    (hver : ∀ t (x : Ω → ℝ), Integrable x S.μ → 𝔼.E t x =ᵐ[S.μ] S.E t x) {t0 : ℕ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hint : ∀ t i, Integrable (fun ω => res P 𝔼 y φ t ω i ^ 2) S.μ)
    (h : ∀ t, t0 ≤ t → ∀ ω i, 𝔼.E t0 (fun ω' => res P 𝔼 y φ t ω' i ^ 2) ω = 0) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, res P 𝔼 y φ t ω = 0 := by
  intro t ht
  have hi : ∀ i, (fun ω => res P 𝔼 y φ t ω i ^ 2) =ᵐ[S.μ] 0 := by
    intro i
    refine condExp_aeFaithful S t0 (hint t i) (Filter.Eventually.of_forall fun ω => sq_nonneg _) ?_
    filter_upwards [hver t0 _ (hint t i)] with ω hω
    rw [← hω]
    exact h t ht ω i
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  funext i
  exact pow_eq_zero_iff two_ne_zero |>.mp (hω i)

end Woodford.OptimalPolicyRules.TidyR5bFaithNeeded
