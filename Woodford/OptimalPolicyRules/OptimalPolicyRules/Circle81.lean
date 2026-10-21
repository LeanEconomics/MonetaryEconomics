/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Prop83
import OptimalPolicyRules.InflTargetInertia
import Mathlib.Algebra.Order.Star.Real

/-!
# Assumption 8.1 does not exclude roots of (1.15) on `|μ| = β⁻¹`

Woodford (2003), *Interest and Prices*, Chapter 8: Assumption 8.1 (p. 541) and the characteristic
polynomial (1.15) (p. 546); the circle `|μ| = β⁻¹` is the boundary of the root count of
Assumptions 8.2 and 8.7 (pp. 552, 556), and `Prop83.prop83` needs that no root lies on it.

The scalar problem `circProblem`: `E_t z_{t+1} = β⁻¹ z_t + i_t + c_t` (`n_Z = 0`, `n_z = 1`) with
loss `½(z_t² + i_t²)`. The root of (1.15) is `μ = β⁻¹`, on the circle. Yet the first-order
conditions reduce to the workhorse `βE_t M_{t+1} − (1 + β + β²) M_t + M_{t−1} = −β² c_t`
(Chapter 7's second-order equation, `InflTargetInertia.secondOrder_existsUnique`), which has a
unique bounded solution for every bounded disturbance and initial multiplier: Assumption 8.1
holds (`circ_assumption81`).

So the hypothesis "no root on `|μ| = β⁻¹`" of `Prop83.prop83` is not implied by Assumption 8.1
(`assumption81_not_exclude_circle`). (In this scalar problem Assumption 8.7 fails, `m = 0`; it
settles the question asked, not a counterexample to Proposition 8.3 itself.)
-/

namespace Woodford.OptimalPolicyRules.Circle81

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ
open InflTargetInertia (SecondOrder ysol secondOrder_existsUnique lagW)

/-- Woodford (2003), eq. (1.1), p. 537: `E_t z_{t+1} = β⁻¹ z_t + i_t + c_t`. -/
noncomputable def circSys (β : ℝ) (hβ : β ≠ 0) : LinearRESystem Empty Unit where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := Matrix.of fun _ _ => β⁻¹
  Et := 1
  B2 := fun _ => 1
  A22_isUnit := by
    rw [isUnit_iff_ne_zero, det_unique]
    exact inv_ne_zero hβ
  B2_ne_zero := by
    intro h
    have := congrFun h ()
    simp at this

/-- Woodford (2003), eqs. (1.2)–(1.4), p. 537: the loss `½(z_t² + i_t²)`, `τ = (z, i)`,
`W = I`. -/
noncomputable def circProblem (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    LQProblem Empty Unit (Fin 2) where
  sys := circSys β hβ0.ne'
  β := β
  β_pos := hβ0
  β_lt_one := hβ1
  Ttil := Matrix.of fun a col => Sum.elim (fun e => e.elim) (fun _ => if a = 0 then 1 else 0) col
  Ti := ![0, 1]
  W := 1
  τstar := 0
  W_posDef := PosDef.one

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)

/-- Woodford (2003), eq. (1.15), p. 546: `det(A − μÎ) = β⁻¹ − μ`; its root `β⁻¹` lies on the
circle `|μ| = β⁻¹`. -/
theorem circ_root : (β⁻¹ : ℂ) ∈ (circSys β hβ0.ne').pencilPoly.roots ∧
    ‖((β : ℂ))⁻¹‖ = β⁻¹ := by
  have hp : (circSys β hβ0.ne').pencilPoly = C ((β : ℂ)⁻¹) - X := by
    refine Polynomial.funext fun z => ?_
    rw [PencilSplit.pencilPoly_eval, Prop83.det_empty_sum, det_unique]
    simp [toBlocks₂₂, LinearRESystem.Ahat, LinearRESystem.Ihat, circSys,
      fromBlocks_apply₂₂]
  refine ⟨?_, ?_⟩
  · rw [hp, mem_roots]
    · simp
    · intro h
      have := congrArg natDegree h
      rw [natDegree_sub_eq_right_of_natDegree_lt (by simp)] at this
      simp at this
  · rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hβ0.le]

/-- Woodford (2003), (1.9) for `circProblem`, p. 541: with `M_t` known at `t`, the first-order
conditions at date `t` are `β⁻¹M_t + z_t − β⁻¹M_{t−1} = 0` and `M_t + i_t = 0`. -/
theorem circ_foc_at_iff (𝔼 : ExpectationSystem Unit)
    (y : ℕ → Unit → (Empty ⊕ Unit) ⊕ Unit → ℝ) {φ : ℕ → Unit → Empty ⊕ Unit → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) (t : ℕ) (ω : Unit) :
    ((circProblem β hβ0 hβ1).sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
      (circProblem β hβ0 hβ1).Tᵀ *ᵥ ((circProblem β hβ0 hβ1).W *ᵥ
        ((circProblem β hβ0 hβ1).T *ᵥ y t ω - (circProblem β hβ0 hβ1).τstar)) -
      (circProblem β hβ0 hβ1).β⁻¹ • ((circProblem β hβ0 hβ1).sys.Itilᵀ *ᵥ φ t ω) = 0) ↔
      (β⁻¹ * φ (t + 1) ω (Sum.inr ()) + y t ω (Sum.inl (Sum.inr ())) -
          β⁻¹ * φ t ω (Sum.inr ()) = 0 ∧
        φ (t + 1) ω (Sum.inr ()) + y t ω (Sum.inr ()) = 0) := by
  have hE : 𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inr ())) ω = φ (t + 1) ω (Sum.inr ()) :=
    congrFun (hmφ t ()) ω
  rw [foc_iff_split _ hmφ y t ω]
  have key : ∀ v : Empty ⊕ Unit → ℝ, v = 0 ↔ v (Sum.inr ()) = 0 := by
    intro v
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      funext r
      rcases r with e | u
      · exact e.elim
      · exact h
  rw [key]
  simp [circProblem, circSys, LinearRESystem.Ahat, LinearRESystem.Ihat, LQProblem.T, Mpart,
    EV, hE, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₂₂]

/-- Woodford (2003), (1.1) for `circProblem`: `E_t z_{t+1} = β⁻¹z_t + i_t + c_t`. -/
theorem circ_structural_iff (𝔼 : ExpectationSystem Unit) (c : ℕ → Unit → Unit → ℝ)
    (y : ℕ → Unit → (Empty ⊕ Unit) ⊕ Unit → ℝ) :
    (circSys β hβ0.ne').Structural 𝔼 c 0 y ↔
      ∀ t ω, 𝔼.E t (fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr ()))) ω =
        β⁻¹ * y t ω (Sum.inl (Sum.inr ())) + y t ω (Sum.inr ()) + c t ω () := by
  unfold LinearRESystem.Structural
  constructor
  · intro h t ω
    have := congrFun (h t (Nat.zero_le t) ω).2 ()
    simpa [circSys, EV, zpart, Zpart, ipart, mulVec, dotProduct] using this
  · intro h t _ ω
    refine ⟨funext fun e => e.elim, funext fun u => ?_⟩
    have := h t ω
    simpa [circSys, EV, zpart, Zpart, ipart, mulVec, dotProduct] using this

/-- **Woodford (2003), Assumption 8.1, p. 541, for `circProblem` (perfect foresight).** For every
bounded disturbance and initial multiplier, the system (1.1) + (1.9) has exactly one bounded
solution: the multiplier solves the workhorse second-order equation
`βM_{t+1} − (1 + β + β²)M_t + M_{t−1} = −β²c_t`, and `z_t = β⁻¹(M_{t−1} − M_t)`, `i_t = −M_t`. -/
theorem circ_assumption81 : Assumption81 (circProblem β hβ0 hβ1) perfectForesight 0 := by
  have hβ := hβ0.ne'
  have hc : (0 : ℝ) < β ^ 2 := by positivity
  -- the second-order equation of a solution
  have hsecond : ∀ {c : ℕ → Unit → Unit → ℝ} {Z0 : Unit → Empty → ℝ} {M0 : Unit → Unit → ℝ}
      {y : ℕ → Unit → (Empty ⊕ Unit) ⊕ Unit → ℝ} {φ : ℕ → Unit → Empty ⊕ Unit → ℝ},
      FOCSystem (circProblem β hβ0 hβ1) perfectForesight c 0 Z0 M0 y φ →
      SecondOrder perfectForesight β (β ^ 2) (fun ω => M0 ω ())
        (fun t ω => -β ^ 2 * c t ω ()) (fun t ω => φ (t + 1) ω (Sum.inr ())) := by
    intro c Z0 M0 y φ hsys t ω
    have hfoc := fun s => (circ_foc_at_iff hβ0 hβ1 perfectForesight y hsys.2.2.1 s ω).mp
      (hsys.2.2.2.2 s (Nat.zero_le s) ω)
    have hstr := (circ_structural_iff hβ0 perfectForesight c y).mp hsys.1.1 t ω
    have hlag : lagW (fun ω => M0 ω ()) (fun t ω => φ (t + 1) ω (Sum.inr ())) t ω =
        φ t ω (Sum.inr ()) := by
      cases t with
      | zero => exact (congrFun (hsys.2.2.2.1 ω) ()).symm
      | succ t => rfl
    rw [hlag]
    have h0 := (hfoc t).1
    have h1 := (hfoc (t + 1)).1
    have h2 := (hfoc t).2
    change y (t + 1) ω (Sum.inl (Sum.inr ())) =
      β⁻¹ * y t ω (Sum.inl (Sum.inr ())) + y t ω (Sum.inr ()) + c t ω () at hstr
    change β * φ (t + 1 + 1) ω (Sum.inr ()) - (1 + β + β ^ 2) * φ (t + 1) ω (Sum.inr ()) +
      φ t ω (Sum.inr ()) = -β ^ 2 * c t ω ()
    have hstr' : β * y (t + 1) ω (Sum.inl (Sum.inr ())) = y t ω (Sum.inl (Sum.inr ())) +
        β * y t ω (Sum.inr ()) + β * c t ω () := by
      rw [hstr]
      field_simp
    field_simp at h0 h1
    linear_combination β * h1 - β * hstr' - h0 - β ^ 2 * h2
  refine ⟨fun c Z0 M0 hcb _ _ _ => ?_, fun c Z0 M0 y y' φ φ' h h' t _ => ?_⟩
  · obtain ⟨Mc, hMc⟩ := hcb
    have hf : ∀ t ω, |(fun t ω => -β ^ 2 * c t ω ()) t ω| ≤ β ^ 2 * Mc := by
      intro t ω
      simp only [abs_mul, abs_neg, abs_pow, abs_of_pos hβ0]
      exact mul_le_mul_of_nonneg_left (hMc t ω ()) hc.le
    obtain ⟨⟨hsol, hsa, hsb⟩, -⟩ := secondOrder_existsUnique perfectForesight hβ0 hβ1 hc hf
      (fun _ => rfl) (y₀ := fun ω => M0 ω ()) (Y := |M0 () ()|) (fun ω => le_refl _) rfl
    set Ms := ysol perfectForesight β (β ^ 2) (fun ω => M0 ω ()) (fun t ω => -β ^ 2 * c t ω ())
      with hMs
    set Ml := lagW (fun ω => M0 ω ()) Ms with hMl
    set yP : ℕ → Unit → (Empty ⊕ Unit) ⊕ Unit → ℝ := fun t ω =>
      Sum.elim (Sum.elim (fun e => e.elim) (fun _ => β⁻¹ * (Ml t ω - Ms t ω)))
        (fun _ => -Ms t ω) with hyP
    set φP : ℕ → Unit → Empty ⊕ Unit → ℝ := fun t ω =>
      Sum.elim (fun e => e.elim) (fun _ => Ml t ω) with hφP
    obtain ⟨B, hB⟩ := hsb
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ())
    have hβi : 0 < β⁻¹ := inv_pos.mpr hβ0
    have hm : 0 ≤ max |M0 () ()| B := (abs_nonneg _).trans (le_max_left _ _)
    have hl : ∀ t ω, |Ml t ω| ≤ max |M0 () ()| B := fun t ω => InflTargetInertia.lagW_bounded
      (fun ω => le_refl |M0 ω ()|) hB t ω
    have hmult : MultiplierMeas perfectForesight φP := fun t r => rfl
    refine ⟨yP, φP, ⟨⟨?_, fun ω => funext fun e => e.elim, ?_, fun t i => rfl⟩, ?_, hmult,
        fun ω => funext fun u => rfl, fun t _ ω => ?_⟩⟩
    · change (circSys β hβ0.ne').Structural perfectForesight c 0 yP
      rw [circ_structural_iff hβ0]
      intro t ω
      have := hsol t ω
      change β * Ms (t + 1) ω - (1 + β + β ^ 2) * Ms t ω + Ml t ω = -β ^ 2 * c t ω () at this
      change β⁻¹ * (Ml (t + 1) ω - Ms (t + 1) ω) =
        β⁻¹ * (β⁻¹ * (Ml t ω - Ms t ω)) + -Ms t ω + c t ω ()
      have e : Ml (t + 1) ω = Ms t ω := rfl
      rw [e]
      field_simp
      linear_combination -this
    · refine ⟨β⁻¹ * (max |M0 () ()| B + B) + B + max |M0 () ()| B, fun t ω i => ?_⟩
      have hs := hB t ω
      have hp : 0 ≤ β⁻¹ * (max |M0 () ()| B + B) := by positivity
      rcases i with (e | u) | u
      · exact e.elim
      · change |β⁻¹ * (Ml t ω - Ms t ω)| ≤ _
        rw [abs_mul, abs_of_pos hβi]
        have := mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hl t ω) hs)) hβi.le
        linarith
      · change |-Ms t ω| ≤ _
        rw [abs_neg]
        linarith
    · refine ⟨max |M0 () ()| B, fun t ω i => ?_⟩
      rcases i with e | u
      · exact e.elim
      · exact hl t ω
    · refine (circ_foc_at_iff hβ0 hβ1 perfectForesight yP hmult t ω).mpr ⟨?_, ?_⟩
      · change β⁻¹ * Ml (t + 1) ω + β⁻¹ * (Ml t ω - Ms t ω) - β⁻¹ * Ml t ω = 0
        have e : Ml (t + 1) ω = Ms t ω := rfl
        rw [e]
        ring
      · change Ml (t + 1) ω + -Ms t ω = 0
        have e : Ml (t + 1) ω = Ms t ω := rfl
        rw [e]
        ring
  · -- uniqueness
    have hf : ∀ t ω, |(fun t ω => -β ^ 2 * c t ω ()) t ω| ≤ β ^ 2 * |c t ω ()| := by
      intro t ω
      simp only [abs_mul, abs_neg, abs_pow, abs_of_pos hβ0]
      exact le_refl _
    have hMb : ∀ {y : ℕ → Unit → (Empty ⊕ Unit) ⊕ Unit → ℝ} {φ : ℕ → Unit → Empty ⊕ Unit → ℝ},
        FOCSystem (circProblem β hβ0 hβ1) perfectForesight c 0 Z0 M0 y φ →
        BoundedProc (fun t ω => φ (t + 1) ω (Sum.inr ())) := by
      intro y φ hs
      obtain ⟨B, hB⟩ := hs.2.1
      exact ⟨B, fun t ω => hB (t + 1) ω (Sum.inr ())⟩
    obtain ⟨Bc, hBc⟩ : ∃ Bc, ∀ t ω, |c t ω ()| ≤ Bc := by
      -- `c` is bounded: it is determined by the bounded plan through (1.1)
      obtain ⟨By, hBy⟩ := h.1.2.2.1
      refine ⟨By + β⁻¹ * By + By, fun t ω => ?_⟩
      have hstr := (circ_structural_iff hβ0 perfectForesight c y).mp h.1.1 t ω
      change y (t + 1) ω (Sum.inl (Sum.inr ())) =
        β⁻¹ * y t ω (Sum.inl (Sum.inr ())) + y t ω (Sum.inr ()) + c t ω () at hstr
      have e : c t ω () = y (t + 1) ω (Sum.inl (Sum.inr ())) -
          β⁻¹ * y t ω (Sum.inl (Sum.inr ())) - y t ω (Sum.inr ()) := by linarith
      rw [e]
      have h1 := hBy (t + 1) ω (Sum.inl (Sum.inr ()))
      have h2 := hBy t ω (Sum.inl (Sum.inr ()))
      have h3 := hBy t ω (Sum.inr ())
      have hβi : 0 < β⁻¹ := inv_pos.mpr hβ0
      calc _ ≤ |y (t + 1) ω (Sum.inl (Sum.inr ()))| + |β⁻¹ * y t ω (Sum.inl (Sum.inr ()))| +
            |y t ω (Sum.inr ())| := by
            exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ _ := by
            rw [abs_mul, abs_of_pos hβi]
            nlinarith
    have hf' : ∀ t ω, |(fun t ω => -β ^ 2 * c t ω ()) t ω| ≤ β ^ 2 * Bc := fun t ω =>
      (hf t ω).trans (mul_le_mul_of_nonneg_left (hBc t ω) hc.le)
    have huniq := (secondOrder_existsUnique perfectForesight hβ0 hβ1 hc hf' (fun _ => rfl)
      (y₀ := fun ω => M0 ω ()) (Y := |M0 () ()|) (fun ω => le_refl _) rfl).2
    have e1 := huniq _ (hsecond h) (fun _ => rfl) (hMb h)
    have e2 := huniq _ (hsecond h') (fun _ => rfl) (hMb h')
    have hM : ∀ s ω, φ s ω (Sum.inr ()) = φ' s ω (Sum.inr ()) := by
      intro s ω
      cases s with
      | zero => exact (congrFun (h.2.2.2.1 ω) ()).trans (congrFun (h'.2.2.2.1 ω) ()).symm
      | succ s => exact (congrFun (congrFun e1 s) ω).trans (congrFun (congrFun e2 s) ω).symm
    have hfo := fun s ω => (circ_foc_at_iff hβ0 hβ1 perfectForesight y h.2.2.1 s ω).mp
      (h.2.2.2.2 s (Nat.zero_le s) ω)
    have hfo' := fun s ω => (circ_foc_at_iff hβ0 hβ1 perfectForesight y' h'.2.2.1 s ω).mp
      (h'.2.2.2.2 s (Nat.zero_le s) ω)
    refine ⟨funext fun ω => funext fun i => ?_, funext fun ω => funext fun i => ?_⟩
    · rcases i with (e | u) | u
      · exact e.elim
      · have a := (hfo t ω).1
        have b := (hfo' t ω).1
        rw [hM, hM] at a
        linarith
      · have a := (hfo t ω).2
        have b := (hfo' t ω).2
        rw [hM] at a
        linarith
    · rcases i with e | u
      · exact e.elim
      · exact hM t ω

/-- **Woodford (2003), Assumption 8.1 (p. 541) and (1.15) (p. 546): Assumption 8.1 does not
exclude roots on `|μ| = β⁻¹`.** For `0 < β < 1`, `circProblem` satisfies Assumption 8.1 (under
perfect foresight) and its characteristic polynomial (1.15) has the root `β⁻¹`, of modulus
exactly `β⁻¹`. -/
theorem assumption81_not_exclude_circle :
    Assumption81 (circProblem β hβ0 hβ1) perfectForesight 0 ∧
      ∃ l ∈ (circProblem β hβ0 hβ1).sys.pencilPoly.roots, ‖l‖ = (circProblem β hβ0 hβ1).β⁻¹ :=
  ⟨circ_assumption81 hβ0 hβ1, _, (circ_root hβ0).1, (circ_root hβ0).2⟩

end Woodford.OptimalPolicyRules.Circle81
