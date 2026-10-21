/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFTSystemsStochastic

/-!
# The form `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` for `n`-dimensional systems

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 633–634: besides the book form (A.11)
`E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0`, equilibrium conditions are often written with the
forecast as an argument, `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0`. This module reduces that form
to the book form of `LocalIFTSystemsStochastic` by adding the forecast as a new adapted variable
`z_t = E_t x_{t+1}`: the augmented `2n`-dimensional book-form system is
`E_t[(F(x_{t−1}, x_t, z_t, e_t), z_t − x_{t+1})] = 0` (`Gaug`). The reduction needs
**informational closure** (`LocalIFTStochastic.Ops.InfoClosed`, proved for perfect foresight and
every finite tree) and disturbances known at `t` (`EKnown`): then `F(…)` is known at `t`, so
`E_t[F(…)] = 0` iff `F(…) = 0`. Without closure the form can have no adapted solution at all
(`LocalIFTStochastic.formI_needs_closure`).

## Main results

* `solvesFS_iff`, `eq_augS_of_solvesSV`: under closure, equilibria of the form `F` are exactly
  the first blocks of book-form equilibria of `Gaug F`.
* `linDeterminateS_Gaug_iff`, `isUnit_linOpS_Gaug_iff`: the augmented linear system is
  determinate iff the `n`-dimensional linear RE system `f₁x_{t−1} + f₂x_t + f₃E_t x_{t+1} = w_t`
  (`f_j = D_jF(0)`) is — so the invertibility condition is the exact root condition on `F`
  (`isUnit_linOpS_Gaug_iff_roots`).
* `local_determinacyF` (**the theorem**), `linSolF_spec`, `first_order_locF`,
  `second_order_locF` (E18).
* The converse: `isUnit_of_local_determinacyF`, `isUnit_iff_local_determinacyF`.
-/

namespace Woodford.PriceLevelDetermination.LocalIFTSystemsStochasticFormI

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SystemsBK.GeneralBKForward
open SystemsBK.GeneralBK (boundedV_add boundedV_sub adaptedV_sub)
open LocalIFTSystems (Arg d1 d2 d3 dE M1 M2 M3 mulVec_M fderiv_zero_apply4 cutoff cutoff_eq
  contDiff_cutoff fderiv_cutoff exists_ball_contDiffAt)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The augmented book-form system -/

/-- Woodford (2003), App. A.3, p. 634: the arguments `(x_{t−1}, x_t, z_t, e_t)` of `F` read off
the augmented argument `((x_{t−1}, z_{t−1}), (x_t, z_t), (x_{t+1}, z_{t+1}), e_t)`. -/
noncomputable def projF : Arg (ι ⊕ ι) E →L[ℝ] Arg ι E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (fun i => p.1 (Sum.inl i), fun i => p.2.1 (Sum.inl i),
        fun i => p.2.1 (Sum.inr i), p.2.2.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Woodford (2003), App. A.3, p. 634: the forecast condition `z_t − x_{t+1}` (whose
conditional expectation vanishes iff `z_t = E_t x_{t+1}`). -/
noncomputable def lz : Arg (ι ⊕ ι) E →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => fun i => p.2.1 (Sum.inr i) - p.2.2.1 (Sum.inl i)
      map_add' := fun p q => by funext i; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
      map_smul' := fun c p => by
        funext i
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

/-- Woodford (2003), App. A.3, p. 634 (tool): two blocks of `n` equations as `2n` equations. -/
noncomputable def joinL : ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (ι ⊕ ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => Sum.elim q.1 q.2
      map_add' := fun p q => by funext k; cases k <;> rfl
      map_smul' := fun c p => by funext k; cases k <;> rfl }

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): values of `projF`. -/
theorem projF_apply (p : Arg (ι ⊕ ι) E) : projF p = (fun i => p.1 (Sum.inl i),
    fun i => p.2.1 (Sum.inl i), fun i => p.2.1 (Sum.inr i), p.2.2.2) := by
  rw [projF, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): values of `lz`. -/
theorem lz_apply (p : Arg (ι ⊕ ι) E) :
    lz p = fun i => p.2.1 (Sum.inr i) - p.2.2.1 (Sum.inl i) := by
  rw [lz, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): values of `joinL`. -/
theorem joinL_apply (q : (ι → ℝ) × (ι → ℝ)) : joinL q = Sum.elim q.1 q.2 := by
  rw [joinL, LinearMap.coe_toContinuousLinearMap']
  rfl

/-- Woodford (2003), App. A.3, p. 634: **the augmented book-form system**
`G̃((x, z)_{t−1}, (x, z)_t, (x, z)_{t+1}, e_t) = (F(x_{t−1}, x_t, z_t, e_t), z_t − x_{t+1})`;
`E_t[G̃] = 0` with `z` adapted means `F(x_{t−1}, x_t, z_t, e_t)` has conditional mean zero and
`z_t = E_t x_{t+1}`. -/
noncomputable def Gaug (F : Arg ι E → (ι → ℝ)) (p : Arg (ι ⊕ ι) E) : ι ⊕ ι → ℝ :=
  joinL (F (projF p), lz p)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the first block of `G̃` is `F`. -/
theorem Gaug_inl (F : Arg ι E → (ι → ℝ)) (p : Arg (ι ⊕ ι) E) (i : ι) :
    Gaug F p (Sum.inl i) = F (projF p) i := by
  rw [Gaug, joinL_apply]
  rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the second block of `G̃` is `z_t − x_{t+1}`. -/
theorem Gaug_inr (F : Arg ι E → (ι → ℝ)) (p : Arg (ι ⊕ ι) E) (i : ι) :
    Gaug F p (Sum.inr i) = p.2.1 (Sum.inr i) - p.2.2.1 (Sum.inl i) := by
  rw [Gaug, joinL_apply, lz_apply]
  rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: `G̃` vanishes at the steady state. -/
theorem Gaug_zero {F : Arg ι E → (ι → ℝ)} (h0 : F 0 = 0) : Gaug F 0 = 0 := by
  funext k
  cases k with
  | inl i => rw [Gaug_inl, map_zero, h0]; rfl
  | inr i => rw [Gaug_inr]; exact sub_self _

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: `G̃` is as smooth at the steady state as `F`. -/
theorem contDiffAt_Gaug {F : Arg ι E → (ι → ℝ)} {k : ℕ} (hF : ContDiffAt ℝ k F 0) :
    ContDiffAt ℝ k (Gaug F) 0 := by
  have hF' : ContDiffAt ℝ k F (projF (0 : Arg (ι ⊕ ι) E)) := by rw [map_zero]; exact hF
  exact joinL.contDiff.contDiffAt.comp 0
    ((hF'.comp 0 (projF (ι := ι) (E := E)).contDiff.contDiffAt).prodMk
      (lz (ι := ι) (E := E)).contDiff.contDiffAt)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the derivative of `G̃` at the steady state. -/
theorem fderiv_Gaug {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0)
    (p : Arg (ι ⊕ ι) E) :
    fderiv ℝ (Gaug F) 0 p = joinL (fderiv ℝ F 0 (projF p), lz p) := by
  have hF' : HasFDerivAt F (fderiv ℝ F 0) (projF (0 : Arg (ι ⊕ ι) E)) := by
    rw [map_zero]; exact hF.hasFDerivAt
  have h := joinL.hasFDerivAt.comp (0 : Arg (ι ⊕ ι) E)
    ((hF'.comp 0 (projF (ι := ι) (E := E)).hasFDerivAt).prodMk
      (lz (ι := ι) (E := E)).hasFDerivAt)
  rw [show Gaug F = ⇑joinL ∘ fun x => ((F ∘ ⇑projF) x, lz x) from rfl, h.fderiv]
  rfl

/-- Woodford (2003), App. A.3, p. 634: the coefficient matrices of the linearised augmented
system in blocks: `f̃₁ = [[f₁, 0], [0, 0]]`, `f̃₂ = [[f₂, f₃], [0, 1]]`, `f̃₃ = [[0, 0], [−1, 0]]`,
`D₄G̃ = (D₄F, 0)`. -/
theorem mulVec_M_Gaug {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0)
    (v : ι ⊕ ι → ℝ) :
    M1 (Gaug F) *ᵥ v = Sum.elim (M1 F *ᵥ fun i => v (Sum.inl i)) (0 : ι → ℝ) ∧
      M2 (Gaug F) *ᵥ v = Sum.elim ((M2 F *ᵥ fun i => v (Sum.inl i)) +
        M3 F *ᵥ fun i => v (Sum.inr i)) (fun i => v (Sum.inr i)) ∧
      M3 (Gaug F) *ᵥ v = Sum.elim (0 : ι → ℝ) (-fun i => v (Sum.inl i)) := by
  have e1 : ∀ w : ι → ℝ, M1 F *ᵥ w = fderiv ℝ F 0 (w, 0, 0, 0) := fun w => by
    rw [(mulVec_M F w).1]; rfl
  have e2 : ∀ w : ι → ℝ, M2 F *ᵥ w = fderiv ℝ F 0 (0, w, 0, 0) := fun w => by
    rw [(mulVec_M F w).2.1]; rfl
  have e3 : ∀ w : ι → ℝ, M3 F *ᵥ w = fderiv ℝ F 0 (0, 0, w, 0) := fun w => by
    rw [(mulVec_M F w).2.2]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [(mulVec_M _ v).1]
    change fderiv ℝ (Gaug F) 0 (v, 0, 0, 0) = _
    rw [fderiv_Gaug hF, e1, joinL_apply, projF_apply, lz_apply]
    funext k
    cases k with
    | inl i => rfl
    | inr i => exact sub_self _
  · rw [(mulVec_M _ v).2.1]
    change fderiv ℝ (Gaug F) 0 (0, v, 0, 0) = _
    rw [fderiv_Gaug hF, e2, e3, ← map_add, joinL_apply, projF_apply, lz_apply]
    have hs : ((0, fun i => v (Sum.inl i), 0, 0) : Arg ι E) + (0, 0, fun i => v (Sum.inr i), 0) =
        (0, fun i => v (Sum.inl i), fun i => v (Sum.inr i), 0) := by simp
    rw [hs]
    funext k
    cases k with
    | inl i => rfl
    | inr i => exact sub_zero _
  · rw [(mulVec_M _ v).2.2]
    change fderiv ℝ (Gaug F) 0 (0, 0, v, 0) = _
    rw [fderiv_Gaug hF, joinL_apply, projF_apply, lz_apply]
    funext k
    cases k with
    | inl i =>
      change fderiv ℝ F 0 (0, 0, 0, 0) i = 0
      rw [show ((0, 0, 0, 0) : Arg ι E) = 0 from rfl, map_zero]
      rfl
    | inr i => exact zero_sub _

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: `D₄G̃ = (D₄F, 0)`. -/
theorem dE_Gaug {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0) (w : E) :
    dE (Gaug F) w = Sum.elim (dE F w) (0 : ι → ℝ) := by
  change fderiv ℝ (Gaug F) 0 (0, 0, 0, w) = _
  rw [fderiv_Gaug hF, joinL_apply, projF_apply, lz_apply]
  funext k
  cases k with
  | inl i => rfl
  | inr i => exact sub_self _

/-- Woodford (2003), App. A.3, p. 634 (tool): the augmented matrices acting on vector
processes, in blocks. -/
theorem mv_Gaug {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0) (a : ι ⊕ ι → Ω → ℝ) :
    (∀ i, mv (M1 (Gaug F)) a (Sum.inl i) = mv (M1 F) (fun j => a (Sum.inl j)) i) ∧
      (∀ i, mv (M1 (Gaug F)) a (Sum.inr i) = 0) ∧
      (∀ i, mv (M2 (Gaug F)) a (Sum.inl i) =
        mv (M2 F) (fun j => a (Sum.inl j)) i + mv (M3 F) (fun j => a (Sum.inr j)) i) ∧
      (∀ i, mv (M2 (Gaug F)) a (Sum.inr i) = a (Sum.inr i)) ∧
      (∀ i, mv (M3 (Gaug F)) a (Sum.inl i) = 0) ∧
      (∀ i, mv (M3 (Gaug F)) a (Sum.inr i) = -a (Sum.inl i)) := by
  have h := fun ω => mulVec_M_Gaug hF (fun k => a k ω)
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
    funext ω <;> simp only [mv_apply, (h ω).1, (h ω).2.1, (h ω).2.2, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, Pi.zero_apply, Pi.neg_apply]

/-! ### The augmented linear system is the `n`-dimensional linear RE system -/

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): an equation between stacked vectors is the pair of
block equations. -/
theorem sumElim_eq_iff {α : Type*} (a b : ι → α) (W : ι ⊕ ι → α) :
    Sum.elim a b = W ↔ a = (fun i => W (Sum.inl i)) ∧ b = fun i => W (Sum.inr i) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    funext k
    cases k <;> rfl

/-- Woodford (2003), App. A.3, p. 634: **the linearised augmented system in blocks**:
`f₁ x_{t−1} + f₂ x_t + f₃ z_t = W¹_t` and `z_t − E_t x_{t+1} = W²_t`. -/
theorem solvesLinS_Gaug_iff {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0)
    (W : ℕ → ι ⊕ ι → Ω → ℝ) (ym : ι ⊕ ι → ℝ) (Y : ℕ → ι ⊕ ι → Ω → ℝ) :
    SolvesLinS 𝔼 (M1 (Gaug F)) (M2 (Gaug F)) (M3 (Gaug F)) W ym Y ↔
      (∀ t, mv (M1 F) (lagP (fun i => ym (Sum.inl i)) (fun s i => Y s (Sum.inl i)) t) +
          mv (M2 F) (fun i => Y t (Sum.inl i)) + mv (M3 F) (fun i => Y t (Sum.inr i)) =
            fun i => W t (Sum.inl i)) ∧
        ∀ t, (fun i => Y t (Sum.inr i) - 𝔼.E t (Y (t + 1) (Sum.inl i))) =
          fun i => W t (Sum.inr i) := by
  obtain h := fun a => mv_Gaug hF (Ω := Ω) a
  have key : ∀ t, mv (M1 (Gaug F)) (lagP ym Y t) + mv (M2 (Gaug F)) (Y t) +
      mv (M3 (Gaug F)) (fun k => 𝔼.E t (Y (t + 1) k)) =
      Sum.elim (mv (M1 F) (lagP (fun i => ym (Sum.inl i)) (fun s i => Y s (Sum.inl i)) t) +
          mv (M2 F) (fun i => Y t (Sum.inl i)) + mv (M3 F) (fun i => Y t (Sum.inr i)))
        (fun i => Y t (Sum.inr i) - 𝔼.E t (Y (t + 1) (Sum.inl i))) := by
    intro t
    have hl : (fun j => lagP ym Y t (Sum.inl j)) =
        lagP (fun i => ym (Sum.inl i)) (fun s i => Y s (Sum.inl i)) t := by
      cases t <;> rfl
    funext k
    cases k with
    | inl i =>
      simp only [Pi.add_apply, (h _).1, (h _).2.2.1, (h _).2.2.2.2.1, hl, Sum.elim_inl,
        add_zero]
      ring
    | inr i =>
      simp only [Pi.add_apply, (h _).2.1, (h _).2.2.2.1, (h _).2.2.2.2.2, Sum.elim_inr]
      ring
  unfold SolvesLinS
  simp only [key, sumElim_eq_iff]
  exact ⟨fun h => ⟨fun t => (h t).1, fun t => (h t).2⟩, fun h t => ⟨h.1 t, h.2 t⟩⟩

/-- **The augmented linear system is determinate iff the `n`-dimensional linear RE system is**
(Woodford (2003), App. A.3, pp. 633–634): for any expectation system, the linearisation of
`G̃ = Gaug F` is determinate iff `f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = w_t` with
`f_j = D_jF(0)` is (substitute `z_t = E_t x_{t+1} + w²_t`). -/
theorem linDeterminateS_Gaug_iff {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0) :
    LinDeterminateS 𝔼 (M1 (Gaug F)) (M2 (Gaug F)) (M3 (Gaug F)) ↔
      LinDeterminateS 𝔼 (M1 F) (M2 F) (M3 F) := by
  have hEb : ∀ {X : ℕ → ι → Ω → ℝ}, BoundedV X →
      BoundedV (fun t i => 𝔼.E t (X (t + 1) i)) := fun {X} hX => by
    obtain ⟨M, hM⟩ := hX
    exact ⟨M, fun t i ω => 𝔼.abs_E_le (hM (t + 1) i) t ω⟩
  have hblk : ∀ {a b : ℕ → ι → Ω → ℝ}, BoundedV a → BoundedV b →
      BoundedV (fun t => Sum.elim (a t) (b t)) := fun {a b} ha hb => by
    obtain ⟨A, hA⟩ := ha
    obtain ⟨B, hB⟩ := hb
    refine ⟨max A B, fun t k ω => ?_⟩
    cases k with
    | inl i => exact (hA t i ω).trans (le_max_left _ _)
    | inr i => exact (hB t i ω).trans (le_max_right _ _)
  have hinl : ∀ {Y : ℕ → ι ⊕ ι → Ω → ℝ}, BoundedV Y → BoundedV (fun t i => Y t (Sum.inl i)) :=
    fun {Y} hY => by obtain ⟨M, hM⟩ := hY; exact ⟨M, fun t i ω => hM t _ ω⟩
  have hinr : ∀ {Y : ℕ → ι ⊕ ι → Ω → ℝ}, BoundedV Y → BoundedV (fun t i => Y t (Sum.inr i)) :=
    fun {Y} hY => by obtain ⟨M, hM⟩ := hY; exact ⟨M, fun t i ω => hM t _ ω⟩
  constructor
  · intro hA w hwb hwa xm
    set W : ℕ → ι ⊕ ι → Ω → ℝ := fun t => Sum.elim (w t) 0 with hW
    have hWb : BoundedV W := hblk hwb ⟨0, fun _ _ _ => by simp⟩
    have hWa : AdaptedV 𝔼 W := fun t k => by
      cases k with
      | inl i => exact hwa t i
      | inr i => exact map_zero _
    obtain ⟨Y, ⟨hYb, hYa, hY⟩, hYu⟩ := hA W hWb hWa (Sum.elim xm 0)
    obtain ⟨h1, h2⟩ := (solvesLinS_Gaug_iff 𝔼 hF W _ Y).mp hY
    have hZ : ∀ t, (fun i => Y t (Sum.inr i)) = fun i => 𝔼.E t (Y (t + 1) (Sum.inl i)) := by
      intro t
      funext i
      have := congrFun (h2 t) i
      simp only [hW, Sum.elim_inr, Pi.zero_apply] at this
      exact sub_eq_zero.mp this
    refine ⟨fun t i => Y t (Sum.inl i), ⟨hinl hYb, fun t i => hYa t _, fun t => ?_⟩,
      fun X' ⟨hX'b, hX'a, hX'⟩ => ?_⟩
    · have := h1 t
      rw [hZ t] at this
      exact this
    · set Y' : ℕ → ι ⊕ ι → Ω → ℝ :=
        fun t => Sum.elim (X' t) (fun i => 𝔼.E t (X' (t + 1) i)) with hY'
      have hs : SolvesLinS 𝔼 (M1 (Gaug F)) (M2 (Gaug F)) (M3 (Gaug F)) W (Sum.elim xm 0) Y' := by
        refine (solvesLinS_Gaug_iff 𝔼 hF W _ Y').mpr ⟨fun t => ?_, fun t => ?_⟩
        · exact hX' t
        · funext i
          simp only [hY', hW, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, sub_self]
      have he := hYu Y' ⟨hblk hX'b (hEb hX'b), fun t k => by
        cases k with
        | inl i => exact hX'a t i
        | inr i => exact 𝔼.E_E_self t _, hs⟩
      funext t i
      rw [← he]
      rfl
  · intro hO W hWb hWa ym
    set w : ℕ → ι → Ω → ℝ := fun t => (fun i => W t (Sum.inl i)) -
      mv (M3 F) (fun i => W t (Sum.inr i)) with hw
    have hwb : BoundedV w := boundedV_sub (hinl hWb) (boundedV_mv _ (hinr hWb))
    have hwa : AdaptedV 𝔼 w :=
      adaptedV_sub 𝔼 (fun t i => hWa t _) (adaptedV_mv 𝔼 _ (fun t i => hWa t _))
    obtain ⟨X, ⟨hXb, hXa, hX⟩, hXu⟩ := hO w hwb hwa (fun i => ym (Sum.inl i))
    set Y : ℕ → ι ⊕ ι → Ω → ℝ := fun t => Sum.elim (X t)
      (fun i => 𝔼.E t (X (t + 1) i) + W t (Sum.inr i)) with hY
    have hsolve : ∀ X' : ℕ → ι → Ω → ℝ, SolvesLinS 𝔼 (M1 F) (M2 F) (M3 F) w
        (fun i => ym (Sum.inl i)) X' → SolvesLinS 𝔼 (M1 (Gaug F)) (M2 (Gaug F))
          (M3 (Gaug F)) W ym (fun t => Sum.elim (X' t)
            (fun i => 𝔼.E t (X' (t + 1) i) + W t (Sum.inr i))) := by
      intro X' hX'
      refine (solvesLinS_Gaug_iff 𝔼 hF W _ _).mpr ⟨fun t => ?_, fun t => ?_⟩
      · have e := hX' t
        have hz : (fun i => (fun t => Sum.elim (X' t)
            (fun i => 𝔼.E t (X' (t + 1) i) + W t (Sum.inr i))) t (Sum.inr i)) =
            (fun i => 𝔼.E t (X' (t + 1) i)) + fun i => W t (Sum.inr i) := rfl
        rw [hz, mv_add, ← add_assoc]
        change mv (M1 F) (lagP _ X' t) + mv (M2 F) (X' t) + _ + _ = _
        rw [e, hw]
        funext i
        simp
      · funext i
        simp
    refine ⟨Y, ⟨hblk hXb (boundedV_add (hEb hXb) (hinr hWb)), fun t k => ?_, hsolve X hX⟩,
      fun Y' ⟨hY'b, hY'a, hY'⟩ => ?_⟩
    · cases k with
      | inl i => exact hXa t i
      | inr i =>
        change 𝔼.E t (𝔼.E t (X (t + 1) i) + W t (Sum.inr i)) = _
        rw [map_add, 𝔼.E_E_self, hWa t]
        rfl
    · obtain ⟨h1, h2⟩ := (solvesLinS_Gaug_iff 𝔼 hF W _ Y').mp hY'
      have hZ : ∀ t, (fun i => Y' t (Sum.inr i)) =
          (fun i => 𝔼.E t (Y' (t + 1) (Sum.inl i))) + fun i => W t (Sum.inr i) := by
        intro t
        funext i
        have := congrFun (h2 t) i
        simp only [Pi.add_apply]
        rw [← this]
        abel
      have hX' : SolvesLinS 𝔼 (M1 F) (M2 F) (M3 F) w (fun i => ym (Sum.inl i))
          (fun t i => Y' t (Sum.inl i)) := by
        intro t
        have e := h1 t
        rw [hZ t, mv_add, ← add_assoc] at e
        exact eq_sub_of_add_eq e
      have he := hXu _ ⟨hinl hY'b, fun t i => hY'a t _, hX'⟩
      funext t k
      cases k with
      | inl i => exact congrFun (congrFun he t) i
      | inr i =>
        have := congrFun (hZ t) i
        simp only [Pi.add_apply] at this
        have h' : Y' (t + 1) (Sum.inl i) = X (t + 1) i := congrFun (congrFun he (t + 1)) i
        rw [this, h']
        rfl

/-- Woodford (2003), App. A.3, pp. 633–634: **the operator (A.12) of `G̃` is invertible iff the
operator (A.12) built from `f_j = D_jF(0)` is**, for any expectation system. -/
theorem isUnit_linOpS_Gaug_iff {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0) :
    IsUnit (linOpS 𝔼 (Gaug F)) ↔ IsUnit (opS 𝔼 (M1 F) (M2 F) (M3 F)) := by
  rw [linOpS, isUnit_opS_iff, isUnit_opS_iff, linDeterminateS_Gaug_iff 𝔼 hF]

/-- Woodford (2003), App. A.3, eqs. (A.9), (A.12), pp. 632–634: for a nonempty state space, the
invertibility condition for the form `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` is the exact root
condition on `f_j = D_jF(0)` (`f₃` the coefficient of the forecast). -/
theorem isUnit_linOpS_Gaug_iff_roots [Nonempty Ω] {F : Arg ι E → (ι → ℝ)}
    (hF : DifferentiableAt ℝ F 0) :
    IsUnit (linOpS 𝔼 (Gaug F)) ↔ quadPoly (M1 F) (M2 F) (M3 F) ≠ 0 ∧
      (∀ μ ∈ ((quadPoly (M1 F) (M2 F) (M3 F)).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly (M1 F) (M2 F) (M3 F)).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ HomInjective (M1 F) (M2 F) (M3 F) := by
  rw [isUnit_linOpS_Gaug_iff 𝔼 hF, isUnit_opS_iff_roots]

/-! ### Equilibria of the form `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` -/

/-- Woodford (2003), App. A.3, p. 634: the disturbances are known at each date (`e_t` constant on
date-`t` information cells). -/
def EKnown (e : LocalIFTStochastic.BFun (ℕ × Ω) E) : Prop :=
  ∀ t, LocalIFTStochastic.Ops.CellConst 𝔼 t (fun ω => e (t, ω))

/-- Woodford (2003), App. A.3, p. 634: `x` is an equilibrium of
`F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` given `u = (x_{−1}, e)`: `x` is adapted and the
conditions hold at every date and in every state. -/
def SolvesFS (F : Arg ι E → (ι → ℝ)) (u : ParS ι E Ω) (x : SProcV ι Ω) : Prop :=
  AdaptedV 𝔼 (toP x) ∧ ∀ t ω, F (lagV u.1 (fun s => x (s, ω)) t, x (t, ω),
    (fun i => 𝔼.E t (toP x (t + 1) i) ω), u.2 (t, ω)) = 0

/-- Woodford (2003), App. A.3, p. 634: the augmented process `(x_t, E_t x_{t+1})`. -/
noncomputable def augS : SProcV ι Ω →L[ℝ] SProcV (ι ⊕ ι) Ω :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFTStochastic.mkB
        (fun p => Sum.elim (x p) (fun i => 𝔼.E p.1 (toP x (p.1 + 1) i) p.2))
        ⟨‖x‖, fun p => (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun k => by
          rw [Real.norm_eq_abs]
          cases k with
          | inl i => exact abs_apply_le x p.1 p.2 i
          | inr i => exact 𝔼.abs_E_le (fun ω => abs_apply_le x (p.1 + 1) ω i) p.1 p.2⟩
      map_add' := fun x y => lp.ext (funext fun p => funext fun k => by
        cases k with
        | inl i => rfl
        | inr i =>
          change 𝔼.E p.1 (toP x (p.1 + 1) i + toP y (p.1 + 1) i) p.2 = _
          rw [map_add]
          rfl)
      map_smul' := fun c x => lp.ext (funext fun p => funext fun k => by
        cases k with
        | inl i => rfl
        | inr i =>
          change 𝔼.E p.1 (c • toP x (p.1 + 1) i) p.2 = _
          rw [map_smul]
          rfl) }
    1 (fun x => by
      rw [one_mul]
      exact LocalIFTStochastic.norm_le_of_forall (norm_nonneg x) fun p =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun k => by
          rw [Real.norm_eq_abs]
          cases k with
          | inl i => exact abs_apply_le x p.1 p.2 i
          | inr i => exact 𝔼.abs_E_le (fun ω => abs_apply_le x (p.1 + 1) ω i) p.1 p.2)

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: values of `augS`. -/
theorem augS_apply (x : SProcV ι Ω) (p : ℕ × Ω) :
    augS 𝔼 x p = Sum.elim (x p) (fun i => 𝔼.E p.1 (toP x (p.1 + 1) i) p.2) := rfl

/-- Woodford (2003), App. A.3, p. 634 (tool): the first block of a stacked process. -/
noncomputable def projS : SProcV (ι ⊕ ι) Ω →L[ℝ] SProcV ι Ω :=
  LinearMap.mkContinuous
    { toFun := fun y => LocalIFTStochastic.mkB (fun p i => y p (Sum.inl i))
        ⟨‖y‖, fun p => (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i =>
          (norm_le_pi_norm (y p) (Sum.inl i)).trans (LocalIFTStochastic.norm_apply_le y p)⟩
      map_add' := fun _ _ => lp.ext rfl
      map_smul' := fun _ _ => lp.ext rfl }
    1 (fun y => by
      rw [one_mul]
      exact LocalIFTStochastic.norm_le_of_forall (norm_nonneg y) fun p =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i =>
          (norm_le_pi_norm (y p) (Sum.inl i)).trans (LocalIFTStochastic.norm_apply_le y p))

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `projS ∘ augS = id`. -/
theorem projS_augS (x : SProcV ι Ω) : projS (augS 𝔼 x) = x := lp.ext rfl

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `‖augS x‖ ≤ ‖x‖` (`|E_t| ≤ 1`). -/
theorem norm_augS_le (x : SProcV ι Ω) : ‖augS 𝔼 x‖ ≤ ‖x‖ :=
  LocalIFTStochastic.norm_le_of_forall (norm_nonneg x) fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun k => by
      rw [Real.norm_eq_abs, augS_apply]
      cases k with
      | inl i => exact abs_apply_le x p.1 p.2 i
      | inr i => exact 𝔼.abs_E_le (fun ω => abs_apply_le x (p.1 + 1) ω i) p.1 p.2

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `‖projS y‖ ≤ ‖y‖`. -/
theorem norm_projS_le (y : SProcV (ι ⊕ ι) Ω) : ‖projS y‖ ≤ ‖y‖ :=
  LocalIFTStochastic.norm_le_of_forall (norm_nonneg y) fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i =>
      (norm_le_pi_norm (y p) (Sum.inl i)).trans (LocalIFTStochastic.norm_apply_le y p)

/-- Woodford (2003), App. A.3, p. 634: the parameters of the augmented system,
`((x_{−1}, 0), e)`. -/
noncomputable def augPar : ParS ι E Ω →L[ℝ] ParS (ι ⊕ ι) E Ω :=
  ((joinL.comp (ContinuousLinearMap.inl ℝ (ι → ℝ) (ι → ℝ))).comp
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (LocalIFTStochastic.BFun (ℕ × Ω) E))).prod
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (LocalIFTStochastic.BFun (ℕ × Ω) E))

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634: values of `augPar`. -/
theorem augPar_apply (u : ParS ι E Ω) : augPar u = (Sum.elim u.1 0, u.2) := by
  change (joinL (u.1, 0), u.2) = _
  rw [joinL_apply]

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `‖augPar u‖ ≤ ‖u‖`. -/
theorem norm_augPar_le (u : ParS ι E Ω) : ‖augPar u‖ ≤ ‖u‖ := by
  rw [augPar_apply, Prod.norm_mk, Prod.norm_def]
  refine max_le_max ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun k => ?_) le_rfl
  cases k with
  | inl i => exact norm_le_pi_norm u.1 i
  | inr i => simp

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the arguments of `F` inside the augmented system are
`(x_{t−1}, x_t, E_t x_{t+1}, e_t)`. -/
theorem projF_ptS_aug (u : ParS ι E Ω) (x : SProcV ι Ω) (t : ℕ) (ω : Ω) :
    projF (ptS (augPar u, augS 𝔼 x) (t, ω)) = (lagV u.1 (fun s => x (s, ω)) t, x (t, ω),
      (fun i => 𝔼.E t (toP x (t + 1) i) ω), u.2 (t, ω)) := by
  rw [projF_apply, augPar_apply]
  cases t <;> rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: **an equilibrium of the form `F` gives a book-form
equilibrium of the augmented system** (no closure needed). -/
theorem solvesSV_of_solvesFS {F : Arg ι E → (ι → ℝ)} {u : ParS ι E Ω} {x : SProcV ι Ω}
    (h : SolvesFS 𝔼 F u x) : SolvesSV 𝔼 (Gaug F) (augPar u) (augS 𝔼 x) := by
  obtain ⟨ha, hF⟩ := h
  refine ⟨fun t k => ?_, fun t k => ?_⟩
  · cases k with
    | inl i => exact ha t i
    | inr i =>
      change 𝔼.E t (𝔼.E t (toP x (t + 1) i)) = 𝔼.E t (toP x (t + 1) i)
      exact 𝔼.E_E_self t _
  · cases k with
    | inl i =>
      have hz : (fun ω => Gaug F (ptS (augPar u, augS 𝔼 x) (t, ω)) (Sum.inl i)) = 0 := by
        funext ω
        rw [Gaug_inl, projF_ptS_aug, hF t ω]
        rfl
      rw [hz]
      exact map_zero _
    | inr i =>
      have hz : (fun ω => Gaug F (ptS (augPar u, augS 𝔼 x) (t, ω)) (Sum.inr i)) =
          𝔼.E t (toP x (t + 1) i) - toP x (t + 1) i := by
        funext ω
        rw [Gaug_inr]
        rfl
      rw [hz, map_sub, 𝔼.E_E_self, sub_self]

omit [Fintype ι] [DecidableEq ι] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): a vector function with cell-constant coordinates
is cell-constant. -/
theorem cellConst_pi {t : ℕ} {v : Ω → ι → ℝ}
    (h : ∀ i, LocalIFTStochastic.Ops.CellConst 𝔼 t (fun ω => v ω i)) :
    LocalIFTStochastic.Ops.CellConst 𝔼 t v :=
  fun ω ω' hw => funext fun i => h i ω ω' hw

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: **under informational closure and known disturbances, a
book-form equilibrium of the augmented system is `(x, E_t x_{t+1})` for an equilibrium `x` of
the form `F`** (the second block forces `z_t = E_t x_{t+1}`; closure makes `F(…)` known). -/
theorem eq_augS_of_solvesSV (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {F : Arg ι E → (ι → ℝ)} {u : ParS ι E Ω} (he : EKnown 𝔼 u.2) {y : SProcV (ι ⊕ ι) Ω}
    (h : SolvesSV 𝔼 (Gaug F) (augPar u) y) :
    y = augS 𝔼 (projS y) ∧ SolvesFS 𝔼 F u (projS y) := by
  obtain ⟨ha, hb⟩ := h
  have hy : y = augS 𝔼 (projS y) := by
    apply toP_injective
    funext t k
    cases k with
    | inl i => rfl
    | inr i =>
      have h2 := hb t (Sum.inr i)
      have hz : (fun ω => Gaug F (ptS (augPar u, y) (t, ω)) (Sum.inr i)) =
          toP y t (Sum.inr i) - toP y (t + 1) (Sum.inl i) := by
        funext ω
        rw [Gaug_inr]
        rfl
      rw [hz, map_sub, ha t (Sum.inr i)] at h2
      rw [sub_eq_zero.mp h2]
      rfl
  refine ⟨hy, fun t i => ha t (Sum.inl i), fun t ω => ?_⟩
  set x := projS y with hx
  have hxa : AdaptedV 𝔼 (toP x) := fun t i => ha t (Sum.inl i)
  funext i
  have h1 := hb t (Sum.inl i)
  rw [hy] at h1
  have hf : (fun ω => Gaug F (ptS (augPar u, augS 𝔼 x) (t, ω)) (Sum.inl i)) =
      fun ω => F (lagV u.1 (fun s => x (s, ω)) t, x (t, ω),
        (fun i => 𝔼.E t (toP x (t + 1) i) ω), u.2 (t, ω)) i := by
    funext ω
    rw [Gaug_inl, projF_ptS_aug]
  rw [hf] at h1
  have hc : LocalIFTStochastic.Ops.CellConst 𝔼 t (fun ω => F (lagV u.1 (fun s => x (s, ω)) t,
      x (t, ω), (fun i => 𝔼.E t (toP x (t + 1) i) ω), u.2 (t, ω)) i) := by
    intro ω ω' hw
    have hl : lagV u.1 (fun s => x (s, ω)) t = lagV u.1 (fun s => x (s, ω')) t := by
      refine cellConst_pi 𝔼 (v := fun ω => lagV u.1 (fun s => x (s, ω)) t) (fun j => ?_) ω ω' hw
      have := LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (adaptedV_lagP 𝔼 u.1 hxa t j)
      cases t with
      | zero => exact fun _ _ _ => rfl
      | succ t => exact this
    have hxx : x (t, ω) = x (t, ω') :=
      cellConst_pi 𝔼 (v := fun ω => x (t, ω))
        (fun j => LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (hxa t j)) ω ω' hw
    have hz : (fun i => 𝔼.E t (toP x (t + 1) i) ω) = fun i => 𝔼.E t (toP x (t + 1) i) ω' :=
      funext fun j => LocalIFTStochastic.Ops.cellConst_E 𝔼 t _ ω ω' hw
    have hee := he t ω ω' hw
    simp only at hee
    simp only [hl, hxx, hz, hee]
  have := hcl t _ hc
  rw [this] at h1
  exact congrFun h1 ω

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: **under informational closure and known disturbances, `x`
solves `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` iff `(x, E_t x_{t+1})` solves the book form of the
augmented system** — the `n`-dimensional analogue of `LocalIFTStochastic.Ops.solvesS_liftI_iff`. -/
theorem solvesFS_iff (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {F : Arg ι E → (ι → ℝ)}
    {u : ParS ι E Ω} (he : EKnown 𝔼 u.2) (x : SProcV ι Ω) :
    SolvesFS 𝔼 F u x ↔ SolvesSV 𝔼 (Gaug F) (augPar u) (augS 𝔼 x) := by
  refine ⟨solvesSV_of_solvesFS 𝔼, fun h => ?_⟩
  have := (eq_augS_of_solvesSV 𝔼 hcl he h).2
  rwa [projS_augS] at this

/-! ### Local determinacy of the form `F` -/

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: the linear RE solution operator for the form
`F`: the first block of the augmented linear solution. -/
noncomputable def linSolF (F : Arg ι E → (ι → ℝ)) : ParS ι E Ω →L[ℝ] SProcV ι Ω :=
  projS.comp ((linSolS 𝔼 (Gaug F)).comp augPar)

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: **`linSolF u` is the bounded adapted
solution of the linear RE system `f₁ x̂_{t−1} + f₂ x̂_t + f₃ E_t x̂_{t+1} + E_t[D₄F e_t] = 0`,
`x̂_{−1} = x_{−1}`** (`f_j = D_jF(0)`), and it is the only one. -/
theorem linSolF_spec {F : Arg ι E → (ι → ℝ)}
    (hF : DifferentiableAt ℝ F 0) (hL : IsUnit (opS 𝔼 (M1 F) (M2 F) (M3 F))) (u : ParS ι E Ω) :
    (AdaptedV 𝔼 (toP (linSolF 𝔼 F u)) ∧
      SolvesLinS 𝔼 (M1 F) (M2 F) (M3 F)
        (fun t => -fun i => 𝔼.E t (fun ω => dE F (u.2 (t, ω)) i)) u.1 (toP (linSolF 𝔼 F u))) ∧
    ∀ x : SProcV ι Ω, AdaptedV 𝔼 (toP x) →
      SolvesLinS 𝔼 (M1 F) (M2 F) (M3 F)
        (fun t => -fun i => 𝔼.E t (fun ω => dE F (u.2 (t, ω)) i)) u.1 (toP x) →
      x = linSolF 𝔼 F u := by
  have hLG : IsUnit (linOpS 𝔼 (Gaug F)) := (isUnit_linOpS_Gaug_iff 𝔼 hF).mpr hL
  have hdE : ∀ t ω, dE (Gaug F) ((augPar u).2 (t, ω)) = Sum.elim (dE F (u.2 (t, ω))) 0 := by
    intro t ω
    rw [dE_Gaug hF, augPar_apply]
  have hR : ∀ t i,
      (-fun k => 𝔼.E t (fun ω => dE (Gaug F) ((augPar u).2 (t, ω)) k)) (Sum.inr i) = 0 := by
    intro t i
    rw [Pi.neg_apply]
    have : (fun ω => dE (Gaug F) ((augPar u).2 (t, ω)) (Sum.inr i)) = 0 :=
      funext fun ω => by rw [hdE]; rfl
    rw [this, map_zero, neg_zero]
  have hLl : ∀ t, (fun i => (-fun k => 𝔼.E t (fun ω => dE (Gaug F) ((augPar u).2 (t, ω)) k))
      (Sum.inl i)) = -fun i => 𝔼.E t (fun ω => dE F (u.2 (t, ω)) i) := by
    intro t
    funext i
    rw [Pi.neg_apply, Pi.neg_apply]
    congr 2
    funext ω
    rw [hdE]
    rfl
  have hym : (fun i => (augPar u).1 (Sum.inl i)) = u.1 := by rw [augPar_apply]; rfl
  obtain ⟨ha, hs⟩ := linSolS_solves 𝔼 hLG (augPar u)
  obtain ⟨h1, h2⟩ := (solvesLinS_Gaug_iff 𝔼 hF _ _ _).mp hs
  refine ⟨⟨fun t i => ha t (Sum.inl i), fun t => ?_⟩, fun x hxa hx => ?_⟩
  · have hz : (fun i => toP (linSolS 𝔼 (Gaug F) (augPar u)) t (Sum.inr i)) =
        fun i => 𝔼.E t (toP (linSolS 𝔼 (Gaug F) (augPar u)) (t + 1) (Sum.inl i)) := by
      funext i
      have := congrFun (h2 t) i
      beta_reduce at this
      rw [hR] at this
      exact sub_eq_zero.mp this
    have e := h1 t
    rw [hz, hym, hLl t] at e
    exact e
  · have hs' : SolvesLinS 𝔼 (M1 (Gaug F)) (M2 (Gaug F)) (M3 (Gaug F))
        (fun t => -fun k => 𝔼.E t (fun ω => dE (Gaug F) ((augPar u).2 (t, ω)) k))
        (augPar u).1 (toP (augS 𝔼 x)) := by
      refine (solvesLinS_Gaug_iff 𝔼 hF _ _ _).mpr ⟨fun t => ?_, fun t => ?_⟩
      · rw [hym, hLl t]
        exact hx t
      · funext i
        beta_reduce
        rw [hR]
        change 𝔼.E t (toP x (t + 1) i) - 𝔼.E t (toP x (t + 1) i) = 0
        exact sub_self _
    have hya : AdaptedV 𝔼 (toP (augS 𝔼 x)) := fun t k => by
      cases k with
      | inl i => exact hxa t i
      | inr i =>
        change 𝔼.E t (𝔼.E t (toP x (t + 1) i)) = 𝔼.E t (toP x (t + 1) i)
        exact 𝔼.E_E_self t _
    have he := eq_linSolS 𝔼 hLG hya hs'
    rw [← projS_augS 𝔼 x, he]
    rfl

/-- **Woodford (2003), App. A.3, pp. 633–635: local determinacy of `n`-dimensional systems
`F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` with predetermined variables under uncertainty.** For an
informationally closed expectation system (e.g. perfect foresight or any finite event tree): if
`F` is `C¹` near the steady state, `F(0) = 0` and the operator (A.12) built from `f_j = D_jF(0)`
is invertible (for nonempty `Ω`: the root condition, `isUnit_linOpS_Gaug_iff_roots`), there are
`ε, δ > 0` (below any `η > 0`) and a map `X : (x_{−1}, e) ↦ x` with `X(0) = 0`, whose derivative
at `0` is the linear RE solution `linSolF` (`linSolF_spec`), such that for every `x_{−1}` and
every bounded disturbance process known at each date with `‖(x_{−1}, e)‖ < δ`, `X(x_{−1}, e)` is
a bounded adapted equilibrium within `ε/2` of the steady state, `X` is `C¹` there, and every
bounded adapted equilibrium within `ε` of the steady state equals it. -/
theorem local_determinacyF (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hL : IsUnit (opS 𝔼 (M1 F) (M2 F) (M3 F))) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : ParS ι E Ω → SProcV ι Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolF 𝔼 F) 0 ∧
      ∀ u : ParS ι E Ω, ‖u‖ < δ → EKnown 𝔼 u.2 → ‖X u‖ < ε / 2 ∧ SolvesFS 𝔼 F u (X u) ∧
        ContDiffAt ℝ 1 X u ∧ ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesFS 𝔼 F u x → x = X u := by
  have hLG : IsUnit (linOpS 𝔼 (Gaug F)) :=
    (isUnit_linOpS_Gaug_iff 𝔼 (hF.differentiableAt one_ne_zero)).mpr hL
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, XS, hX0, hXd, hX⟩ :=
    local_determinacyS 𝔼 (contDiffAt_Gaug hF) (Gaug_zero h0) hLG hη
  refine ⟨ε, hε, hεη, δ, hδ, hδη, fun u => projS (XS (augPar u)), ?_, ?_, fun u hu he => ?_⟩
  · simp only [map_zero, hX0]
  · have hd : HasFDerivAt XS (linSolS 𝔼 (Gaug F)) (augPar (0 : ParS ι E Ω)) := by
      rw [map_zero]; exact hXd
    change HasFDerivAt _ ((projS (ι := ι) (Ω := Ω)).comp
      ((linSolS 𝔼 (Gaug F)).comp (augPar (ι := ι) (E := E) (Ω := Ω)))) 0
    exact (projS (ι := ι) (Ω := Ω)).hasFDerivAt.comp (0 : ParS ι E Ω)
      (hd.comp 0 (augPar (ι := ι) (E := E) (Ω := Ω)).hasFDerivAt)
  have hPu : ‖augPar u‖ < δ := lt_of_le_of_lt (norm_augPar_le u) hu
  obtain ⟨hn, hs, hc, hun⟩ := hX (augPar u) hPu
  refine ⟨lt_of_le_of_lt (norm_projS_le _) hn, (eq_augS_of_solvesSV 𝔼 hcl he hs).2,
    (projS (ι := ι) (Ω := Ω)).contDiff.contDiffAt.comp u
      (hc.comp u (augPar (ι := ι) (E := E) (Ω := Ω)).contDiff.contDiffAt),
    fun x hx hsol => ?_⟩
  have h := hun (augS 𝔼 x) (lt_of_le_of_lt (norm_augS_le 𝔼 x) hx) (solvesSV_of_solvesFS 𝔼 hsol)
  change x = projS (XS (augPar u))
  rw [← h, projS_augS]

/-- Woodford (2003), App. A.3, p. 634, E18 (**first order under `C¹`**), form `F`: every
equilibrium near the steady state is within `c ‖(x_{−1}, e)‖` of the linear RE solution, for
every `c > 0` once the disturbances are small. -/
theorem first_order_locF {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hL : IsUnit (opS 𝔼 (M1 F) (M2 F) (M3 F))) :
    ∃ ε > 0, ∀ c > 0, ∃ δ > 0, ∀ u : ParS ι E Ω, ‖u‖ < δ → ∀ x : SProcV ι Ω, ‖x‖ < ε →
      SolvesFS 𝔼 F u x → ‖x - linSolF 𝔼 F u‖ ≤ c * ‖u‖ := by
  have hLG : IsUnit (linOpS 𝔼 (Gaug F)) :=
    (isUnit_linOpS_Gaug_iff 𝔼 (hF.differentiableAt one_ne_zero)).mpr hL
  obtain ⟨ε, hε, hP⟩ := first_order_locS 𝔼 (contDiffAt_Gaug hF) (Gaug_zero h0) hLG
  refine ⟨ε, hε, fun c hc => ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hP c hc
  refine ⟨δ, hδ, fun u hu x hx hsol => ?_⟩
  have h := hb (augPar u) (lt_of_le_of_lt (norm_augPar_le u) hu) (augS 𝔼 x)
    (lt_of_le_of_lt (norm_augS_le 𝔼 x) hx) (solvesSV_of_solvesFS 𝔼 hsol)
  have e : x - linSolF 𝔼 F u = projS (augS 𝔼 x - linSolS 𝔼 (Gaug F) (augPar u)) := by
    rw [map_sub, projS_augS]
    rfl
  rw [e]
  exact (norm_projS_le _).trans (h.trans (mul_le_mul_of_nonneg_left (norm_augPar_le u) hc.le))

/-- Woodford (2003), App. A.3, p. 634, corrected per E18, form `F`: if `F` is `C²` near the
steady state, every equilibrium within `ε` of the steady state is within
`C ‖(x_{−1}, e)‖²` of the linear RE solution for `‖(x_{−1}, e)‖ < δ`. -/
theorem second_order_locF {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 2 F 0) (h0 : F 0 = 0)
    (hL : IsUnit (opS 𝔼 (M1 F) (M2 F) (M3 F))) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ C : ℝ, ∀ u : ParS ι E Ω, ‖u‖ < δ →
      ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesFS 𝔼 F u x → ‖x - linSolF 𝔼 F u‖ ≤ C * ‖u‖ ^ 2 := by
  have hLG : IsUnit (linOpS 𝔼 (Gaug F)) :=
    (isUnit_linOpS_Gaug_iff 𝔼 (hF.differentiableAt (by norm_num))).mpr hL
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, C, hC⟩ :=
    second_order_locS 𝔼 (contDiffAt_Gaug hF) (Gaug_zero h0) hLG hη
  refine ⟨ε, hε, hεη, δ, hδ, hδη, |C|, fun u hu x hx hsol => ?_⟩
  have h := hC (augPar u) (lt_of_le_of_lt (norm_augPar_le u) hu) (augS 𝔼 x)
    (lt_of_le_of_lt (norm_augS_le 𝔼 x) hx) (solvesSV_of_solvesFS 𝔼 hsol)
  have e : x - linSolF 𝔼 F u = projS (augS 𝔼 x - linSolS 𝔼 (Gaug F) (augPar u)) := by
    rw [map_sub, projS_augS]
    rfl
  rw [e]
  calc _ ≤ ‖augS 𝔼 x - linSolS 𝔼 (Gaug F) (augPar u)‖ := norm_projS_le _
    _ ≤ C * ‖augPar u‖ ^ 2 := h
    _ ≤ |C| * ‖augPar u‖ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_augPar_le u) 2)
          (abs_nonneg C)

/-! ### The converse for the form `F` -/

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, pp. 631–634: a perfect-foresight equilibrium of
`F(x_{t−1}, x_t, x_{t+1}, e_t) = 0` (`LocalIFTSystems.Solves`) is a deterministic equilibrium of
the form `F(x_{t−1}, x_t, E_t x_{t+1}, e_t) = 0` for every expectation system. -/
theorem solvesFS_embG {F : Arg ι E → (ι → ℝ)} {u : LocalIFTSystems.Par ι E} {z : SeqV ι}
    (h : LocalIFTSystems.Solves F u z) :
    SolvesFS 𝔼 F (embPar u) (embG (ι → ℝ) z) := by
  refine ⟨adaptedV_embG 𝔼 z, fun t ω => ?_⟩
  have hE : (fun i => 𝔼.E t (toP (embG (Ω := Ω) (ι → ℝ) z) (t + 1) i) ω) = z (t + 1) := by
    rw [toP_embG]
    funext i
    rw [𝔼.const]
  rw [hE]
  change F (lagV u.1 (fun s => z s) t, z t, z (t + 1), u.2 t) = 0
  exact h t

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `E_t E_t = E_t` on vector processes. -/
theorem condEV_condEV (y : SProcV ι Ω) : condEV 𝔼 (condEV 𝔼 y) = condEV 𝔼 y := by
  ext ⟨t, ω⟩ i
  change 𝔼.E t (𝔼.E t (toP y t i)) ω = 𝔼.E t (toP y t i) ω
  rw [𝔼.E_E_self]

/-- Woodford (2003), App. A.3, eq. (A.12), p. 634: **the first block of the augmented
derivative at `(x, E_t x_{t+1})` is the derivative (A.12) of the form `F`**,
`opS(f₁, f₂, f₃) x + E_t[B u]`. -/
theorem projS_eqD0S_Gaug {F : Arg ι E → (ι → ℝ)} (hF : DifferentiableAt ℝ F 0)
    (u : ParS ι E Ω) (x : SProcV ι Ω) :
    projS (eqD0S 𝔼 (Gaug F) (augPar u, augS 𝔼 x)) = eqD0S 𝔼 F (u, x) := by
  apply toP_injective
  funext t
  funext i
  have hm := mv_Gaug hF (Ω := Ω)
  have hy : ∀ s, toP (augS 𝔼 x) s =
      Sum.elim (toP x s) (fun j => 𝔼.E s (toP x (s + 1) j)) := fun s => by
    funext k
    cases k <;> rfl
  have L : toP (projS (eqD0S 𝔼 (Gaug F) (augPar u, augS 𝔼 x))) t i =
      toP (opS 𝔼 (M1 (Gaug F)) (M2 (Gaug F)) (M3 (Gaug F)) (augS 𝔼 x)) t (Sum.inl i) +
        toP (condEV 𝔼 (bOpS (Gaug F) (augPar u))) t (Sum.inl i) := rfl
  have R : toP (eqD0S 𝔼 F (u, x)) t i =
      toP (opS 𝔼 (M1 F) (M2 F) (M3 F) x) t i + toP (condEV 𝔼 (bOpS F u)) t i := rfl
  rw [L, R, toP_opS, toP_opS, toP_condEV_bOpS, toP_condEV_bOpS]
  have hl : (fun j => 𝔼.E t (lagP 0 (toP (augS 𝔼 x)) t (Sum.inl j))) =
      fun j => 𝔼.E t (lagP 0 (toP x) t j) := by
    funext j
    cases t <;> rfl
  have hl2 : (fun j => lagP (Ω := Ω) (augPar u).1 0 t (Sum.inl j)) = lagP u.1 0 t := by
    rw [augPar_apply]
    funext j
    cases t <;> rfl
  have h3 : (fun j => 𝔼.E t (toP (augS 𝔼 x) t (Sum.inr j))) =
      fun j => 𝔼.E t (toP x (t + 1) j) := by
    funext j
    rw [hy t]
    exact 𝔼.E_E_self t _
  have hdE : (fun ω => dE (Gaug F) ((augPar u).2 (t, ω)) (Sum.inl i)) =
      fun ω => dE F (u.2 (t, ω)) i := by
    funext ω
    rw [dE_Gaug hF, augPar_apply]
    rfl
  have hyl : ∀ s j, toP (augS 𝔼 x) s (Sum.inl j) = toP x s j := fun _ _ => rfl
  simp only [Pi.add_apply, Pi.sub_apply, (hm _).1, (hm _).2.2.1, (hm _).2.2.2.2.1, hl, hl2, h3,
    hdE, add_zero, hyl]
  ring

/-- Woodford (2003), App. A.3, p. 634 (**necessity, existence half**, form `F`): if the
disturbances move every equation (`D₄F(0)` onto) and a solution map `X`, differentiable at `0`
with `X(0) = 0`, gives equilibria for all small `(x_{−1}, e)` with `e` known at each date, then
(A.12) built from `f_j = D_jF(0)` is onto. (No closure is needed in this direction.) -/
theorem surjective_of_solution_mapF {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0)
    (hE : Function.Surjective (dE F)) {X : ParS ι E Ω → SProcV ι Ω} {δ : ℝ} (hδ : 0 < δ)
    (hX0 : X 0 = 0) (hXd : DifferentiableAt ℝ X 0)
    (hX : ∀ u : ParS ι E Ω, ‖u‖ < δ → EKnown 𝔼 u.2 → SolvesFS 𝔼 F u (X u)) :
    Function.Surjective (opS 𝔼 (M1 F) (M2 F) (M3 F)) := by
  have hFd : DifferentiableAt ℝ F 0 := hF.differentiableAt one_ne_zero
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt (contDiffAt_Gaug hF)
  set Gc := cutoff (Gaug F) r hr with hGc
  have hGc1 : ContDiff ℝ 1 Gc := contDiff_cutoff hr hball
  obtain ⟨hlo, hbo, -, -⟩ := lin_cutoffS 𝔼 (Gaug F) hr
  have key : ∀ du : ParS ι E Ω, EKnown 𝔼 du.2 →
      eqD0S 𝔼 (Gaug F) (augPar du, augS 𝔼 (fderiv ℝ X 0 du)) = 0 := by
    intro du hdu
    set ℓ := ContinuousLinearMap.toSpanSingleton ℝ du with hℓ
    set P := augPar (ι := ι) (E := E) (Ω := Ω) with hP
    set A := augS (ι := ι) 𝔼 with hA
    have hℓ0 : ℓ 0 = 0 := map_zero _
    have hXd' : HasFDerivAt X (fderiv ℝ X 0) (ℓ 0) := by rw [hℓ0]; exact hXd.hasFDerivAt
    have hpath : HasFDerivAt (fun s : ℝ => ((P (ℓ s), A (X (ℓ s))) :
        ParS (ι ⊕ ι) E Ω × SProcV (ι ⊕ ι) Ω))
        ((P.comp ℓ).prod (A.comp ((fderiv ℝ X 0).comp ℓ))) 0 :=
      (P.hasFDerivAt.comp 0 ℓ.hasFDerivAt).prodMk
        (A.hasFDerivAt.comp 0 (hXd'.comp 0 ℓ.hasFDerivAt))
    have hp0 : ((P (ℓ 0), A (X (ℓ 0))) : ParS (ι ⊕ ι) E Ω × SProcV (ι ⊕ ι) Ω) =
        0 := by
      rw [hℓ0, hX0, map_zero, map_zero]
      rfl
    have hn := (hasStrictFDerivAt_eqMapS 𝔼 hGc1 0).hasFDerivAt
    rw [eqDS_zero 𝔼 hGc1, ← hp0] at hn
    have hD := hn.comp (0 : ℝ) hpath
    have hev : (fun s : ℝ => eqMapS 𝔼 Gc hGc1.continuous (augPar (ℓ s), augS 𝔼 (X (ℓ s))))
        =ᶠ[𝓝 0] fun _ => 0 := by
      have hcℓ : Filter.Tendsto ℓ (𝓝 0) (𝓝 0) := by
        have := ℓ.continuous.tendsto 0
        rwa [hℓ0] at this
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), ‖X (ℓ s)‖ < r / 4 := by
        have ht := hXd.continuousAt.tendsto.comp hcℓ
        rw [Function.comp_def, hX0] at ht
        exact (ht.eventually (Metric.ball_mem_nhds (0 : SProcV ι Ω)
          (by positivity : (0 : ℝ) < r / 4))).mono (fun s hs => by simpa using hs)
      have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), ‖ℓ s‖ < min δ (r / 4) :=
        (hcℓ.eventually (Metric.ball_mem_nhds (0 : ParS ι E Ω)
          (lt_min hδ (by positivity : (0 : ℝ) < r / 4)))).mono (fun s hs => by simpa using hs)
      filter_upwards [h1, h2] with s hs1 hs2
      have hk : EKnown 𝔼 (ℓ s).2 := by
        intro t ω ω' hw
        change s • du.2 (t, ω) = s • du.2 (t, ω')
        have h := hdu t ω ω' hw
        simp only at h
        rw [h]
      have hsol := solvesSV_of_solvesFS 𝔼 (hX (ℓ s) (hs2.trans_le (min_le_left _ _)) hk)
      rw [eqMapS_eq_zero_iff]
      exact (solvesSV_cutoff_iff 𝔼 hr ((norm_augPar_le _).trans
        (hs2.le.trans (min_le_right _ _))) ((norm_augS_le 𝔼 _).trans hs1.le)).mpr hsol
    have hc : HasFDerivAt (fun s : ℝ => eqMapS 𝔼 Gc hGc1.continuous
        (augPar (ℓ s), augS 𝔼 (X (ℓ s)))) (0 : ℝ →L[ℝ] SProcV (ι ⊕ ι) Ω) 0 :=
      (hasFDerivAt_const (0 : SProcV (ι ⊕ ι) Ω) (0 : ℝ)).congr_of_eventuallyEq hev
    have hz := congrArg (fun T : ℝ →L[ℝ] SProcV (ι ⊕ ι) Ω => T 1) (hD.unique hc)
    change eqD0S 𝔼 Gc (augPar (ℓ 1), augS 𝔼 (fderiv ℝ X 0 (ℓ 1))) = 0 at hz
    have h1 : ℓ 1 = du := by rw [hℓ, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rw [h1] at hz
    have he : eqD0S 𝔼 Gc = eqD0S 𝔼 (Gaug F) := by
      simp only [eqD0S, hGc, hlo, hbo]
    rw [he] at hz
    exact hz
  obtain ⟨g, hg⟩ := (dE F : E →ₗ[ℝ] (ι → ℝ)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hE)
  set R : (ι → ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap g with hR
  have hRinv : ∀ v, dE F (R v) = v := fun v => by
    have := congrArg (fun φ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) => φ v) hg
    simpa [hR] using this
  have hrange : ∀ y : SProcV ι Ω, ∃ z, opS 𝔼 (M1 F) (M2 F) (M3 F) z = condEV 𝔼 y := by
    intro y
    set e : LocalIFTStochastic.BFun (ℕ × Ω) E :=
      LocalIFTStochastic.mkB (fun p => R (-(condEV 𝔼 y) p))
        ⟨‖R‖ * ‖y‖, fun p => (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (by
          rw [norm_neg]
          exact (LocalIFTStochastic.norm_apply_le _ p).trans (norm_condEV_le 𝔼 y))
          (norm_nonneg _))⟩ with he
    have hek : EKnown 𝔼 e := by
      intro t ω ω' hw
      have hc : (condEV 𝔼 y) (t, ω) = (condEV 𝔼 y) (t, ω') :=
        cellConst_pi 𝔼 (v := fun ω => (condEV 𝔼 y) (t, ω))
          (fun j => by
            change LocalIFTStochastic.Ops.CellConst 𝔼 t (𝔼.E t (toP y t j))
            exact LocalIFTStochastic.Ops.cellConst_E 𝔼 t _) ω ω' hw
      change R (-(condEV 𝔼 y) (t, ω)) = R (-(condEV 𝔼 y) (t, ω'))
      rw [hc]
    set du : ParS ι E Ω := (0, e) with hdu
    refine ⟨fderiv ℝ X 0 du, ?_⟩
    have hk := congrArg projS (key du hek)
    rw [projS_eqD0S_Gaug 𝔼 hFd, map_zero] at hk
    change opS 𝔼 (M1 F) (M2 F) (M3 F) (fderiv ℝ X 0 du) + condEV 𝔼 (bOpS F du) = 0 at hk
    have hb : bOpS F du = -condEV 𝔼 y := by
      refine lp.ext (funext fun p => ?_)
      rw [bOpS_apply]
      have hl : lagV (0 : ι → ℝ) (0 : ℕ → ι → ℝ) p.1 = 0 := by cases p.1 <;> rfl
      simp only [hdu, he, hl, map_zero, zero_add, LocalIFTStochastic.mkB_apply, hRinv,
        lp.coeFn_neg, Pi.neg_apply]
    rw [hb, map_neg, condEV_condEV] at hk
    exact add_neg_eq_zero.mp hk
  intro y
  obtain ⟨z₁, hz₁⟩ := hrange y
  have hPb : condEV 𝔼 (y - condEV 𝔼 y) = 0 := condEV_sub_condEV 𝔼 y
  obtain ⟨z₂, hz₂⟩ := hrange (linS (M1 F) (M2 F) (M3 F) (y - condEV 𝔼 y))
  refine ⟨z₁ + (y - condEV 𝔼 y) - z₂, ?_⟩
  have hb' : opS 𝔼 (M1 F) (M2 F) (M3 F) (y - condEV 𝔼 y) =
      condEV 𝔼 (linS (M1 F) (M2 F) (M3 F) (y - condEV 𝔼 y)) + (y - condEV 𝔼 y) := by
    change condEV 𝔼 (linS (M1 F) (M2 F) (M3 F) (y - condEV 𝔼 y)) +
      ((y - condEV 𝔼 y) - condEV 𝔼 (y - condEV 𝔼 y)) = _
    rw [hPb, sub_zero]
  rw [map_sub, map_add, hz₁, hb', hz₂]
  abel

/-- **The converse for the form `F`** (Woodford (2003), App. A.3, pp. 633–634): on a nonempty
state space, if `D₄F(0)` is onto and the form `F` is locally determinate with a solution map
differentiable at the steady state (for disturbances known at each date), then (A.12) built from
`f_j = D_jF(0)` is invertible. (No closure is needed in this direction; non-uniqueness comes from
the deterministic perfect-foresight manifold of `LocalIFTSystems.not_locally_unique`.) -/
theorem isUnit_of_local_determinacyF [Nonempty Ω] {F : Arg ι E → (ι → ℝ)}
    (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0) (hE : Function.Surjective (dE F))
    {X : ParS ι E Ω → SProcV ι Ω} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hX0 : X 0 = 0)
    (hXd : DifferentiableAt ℝ X 0)
    (hX : ∀ u : ParS ι E Ω, ‖u‖ < δ → EKnown 𝔼 u.2 → SolvesFS 𝔼 F u (X u))
    (huniq : ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesFS 𝔼 F 0 x → x = 0) :
    IsUnit (opS 𝔼 (M1 F) (M2 F) (M3 F)) := by
  have hs := surjective_of_solution_mapF 𝔼 hF hE hδ hX0 hXd hX
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨?_, hs⟩
  by_contra hni
  obtain ⟨z, hz0, hzε, hzs⟩ := LocalIFTSystems.not_locally_unique hF h0
    (sysOp_surjective_of_opS 𝔼 hs) (sysOp_not_injective_of_opS 𝔼 hni) ε hε
  have hxs := solvesFS_embG 𝔼 hzs
  rw [map_zero] at hxs
  have := huniq _ (by rw [norm_embG]; exact hzε) hxs
  apply hz0
  rw [← norm_eq_zero, ← norm_embG (Ω := Ω), this, norm_zero]

/-- **Local determinacy of the form `F` holds exactly under the root condition** (Woodford
(2003), App. A.3, pp. 633–634): for an informationally closed expectation system on a nonempty
state space, `F` `C¹` near the steady state with `F(0) = 0` and `D₄F(0)` onto, (A.12) built from
`f_j = D_jF(0)` is invertible (the exact root condition) iff there are `ε, δ > 0` and a solution
map `X` with `X(0) = 0`, differentiable at `0`, giving for every `‖(x_{−1}, e)‖ < δ` (with `e`
known at each date) a bounded adapted equilibrium which is the only one within `ε` of the steady
state. -/
theorem isUnit_iff_local_determinacyF [Nonempty Ω] (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {F : Arg ι E → (ι → ℝ)} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hE : Function.Surjective (dE F)) :
    IsUnit (opS 𝔼 (M1 F) (M2 F) (M3 F)) ↔ ∃ ε > 0, ∃ δ > 0, ∃ X : ParS ι E Ω → SProcV ι Ω,
      X 0 = 0 ∧ DifferentiableAt ℝ X 0 ∧ ∀ u : ParS ι E Ω, ‖u‖ < δ → EKnown 𝔼 u.2 →
        SolvesFS 𝔼 F u (X u) ∧ ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesFS 𝔼 F u x → x = X u := by
  constructor
  · intro hL
    obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ := local_determinacyF 𝔼 hcl hF h0 hL one_pos
    exact ⟨ε, hε, δ, hδ, X, hX0, hXd.differentiableAt, fun u hu he =>
      ⟨(hX u hu he).2.1, (hX u hu he).2.2.2⟩⟩
  · rintro ⟨ε, hε, δ, hδ, X, hX0, hXd, hX⟩
    have hk0 : EKnown 𝔼 (0 : ParS ι E Ω).2 := fun _ _ _ _ => rfl
    refine isUnit_of_local_determinacyF 𝔼 hF h0 hE hε hδ hX0 hXd
      (fun u hu he => (hX u hu he).1) fun x hx hsol => ?_
    rw [(hX 0 (by rw [norm_zero]; exact hδ) hk0).2 x hx hsol, hX0]

end Woodford.PriceLevelDetermination.LocalIFTSystemsStochasticFormI
