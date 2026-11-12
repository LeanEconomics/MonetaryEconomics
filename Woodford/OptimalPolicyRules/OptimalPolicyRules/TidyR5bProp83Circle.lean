/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bReRep
import OptimalPolicyRules.InflTargetInertia

/-!
# A counterexample to Proposition 8.3 that satisfies the full Assumption 8.1

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.3 (pp. 556–557), Assumption 8.1
(p. 541), Assumptions 8.3 (App. G.1, p. 716) and 8.7 (p. 556).

`Prop83.prop83` proves Proposition 8.3 for every representation of Proposition 8.1 under
Assumptions 8.1, 8.3, 8.7 and no root of (1.15) on `|μ| = β⁻¹`; `Prop83.circle_counterexample`
shows the circle hypothesis is needed, but only at the level of the homogeneous equivalence
`Prop83.HomEquiv`, and `Circle81.assumption81_not_exclude_circle` shows that Assumption 8.1
allows circle roots (with `m = 0`). Here everything is put together in one problem.

## The problem `p83Problem` (`n_Z = 0`, `n_z = 2`, `β = 1/2`)

`E_t z_{1,t+1} = ½ z_{1t} + c_{1t}` (no instrument) and `E_t z_{2,t+1} = 2 z_{2t} + i_t + c_{2t}`,
loss `½(z₁² + z₂² + i²)`. The roots of (1.15) are `½` (inside `|μ| < β⁻¹ = 2`) and `2` (ON the
circle `|μ| = β⁻¹`).

* `p83_assumption81`: **Assumption 8.1 holds** (perfect foresight): the first-order conditions
  decouple into two workhorse equations,
  `½ M_{1,t+1} − (9/4) M_{1t} + M_{1,t−1} = −c_{1t}` and
  `½ M_{2,t+1} − (7/4) M_{2t} + M_{2,t−1} = −c_{2t}/4`, each with a unique bounded solution
  (`InflTargetInertia.secondOrder_existsUnique`).
* `p83_assumption83`, `p83_stableCount`: Assumption 8.3 holds and Assumption 8.7 holds with `m = 1`.
* `p83Rep'`: a representation of Proposition 8.1 (perfect foresight, the original
  `Prop81Conclusion`) whose `Λ` is the Jordan block `[[1, 0], [1, 1]]`, obtained from the natural
  one (`Λ = diag(4, 1)`) by `TidyR5bReRep.reRep`.
* `prop83_fails_on_circle`: for it `α(L) = (1 − L)²` has **no** zero inside the unit circle,
  although `m = 1`: Proposition 8.3 (`TargetCriterion.Prop83Claim`) fails for a problem satisfying
  the full Assumption 8.1, Assumption 8.3 and Assumption 8.7.

The natural representation does satisfy the claim (`natural_zerosInside`): the failure is the
non-uniqueness of `Λ` when a root lies on the circle (`TidyR5bReRep.jordan_nonunique`).
-/

namespace Woodford.OptimalPolicyRules.TidyR5bProp83Circle

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ PencilSplit PencilEigen
open Prop81General TargetCriterion.Prop81 TidyR5bReRep Adjugate
open InflTargetInertia (SecondOrder ysol secondOrder_existsUnique lagW lagW_bounded)

/-! ### The problem -/

/-- Woodford (2003), eq. (1.1), p. 537 (the counterexample): `A₂₂ = diag(½, 2)`, `Ẽ = I`,
`B₂ = (0, 1)'` (the instrument enters only the second equation). -/
noncomputable def p83Sys : LinearRESystem Empty (Fin 2) where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := !![1 / 2, 0; 0, 2]
  Et := 1
  B2 := ![0, 1]
  A22_isUnit := by
    rw [isUnit_iff_ne_zero, det_fin_two_of]
    norm_num
  B2_ne_zero := by
    intro h
    have := congrFun h 1
    simp at this

/-- Woodford (2003), eqs. (1.2)–(1.4) (the counterexample): `β = 1/2`, targets
`τ = (z₁, z₂, i)`, `W = I`, `τ* = 0`. -/
noncomputable def p83Problem : LQProblem Empty (Fin 2) (Fin 3) where
  sys := p83Sys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := Matrix.of fun a col => Sum.elim (fun e => e.elim) (fun j => if a = j.castSucc then 1
    else 0) col
  Ti := ![0, 0, 1]
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), (1.9) for `p83Problem` (with `M_t` known at `t`): the first-order
conditions at date `t` are `½ M_{1t} + z_{1t} − 2 M_{1,t−1} = 0`,
`2 M_{2t} + z_{2t} − 2 M_{2,t−1} = 0` and `M_{2t} + i_t = 0`. -/
theorem p83_foc_at_iff (𝔼 : ExpectationSystem Unit)
    (y : ℕ → Unit → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) {φ : ℕ → Unit → Empty ⊕ Fin 2 → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) (t : ℕ) (ω : Unit) :
    (p83Problem.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
      p83Problem.Tᵀ *ᵥ (p83Problem.W *ᵥ (p83Problem.T *ᵥ y t ω - p83Problem.τstar)) -
      p83Problem.β⁻¹ • (p83Problem.sys.Itilᵀ *ᵥ φ t ω) = 0) ↔
      (1 / 2 * φ (t + 1) ω (Sum.inr 0) + y t ω (Sum.inl (Sum.inr 0)) -
          2 * φ t ω (Sum.inr 0) = 0 ∧
        2 * φ (t + 1) ω (Sum.inr 1) + y t ω (Sum.inl (Sum.inr 1)) -
          2 * φ t ω (Sum.inr 1) = 0 ∧
        φ (t + 1) ω (Sum.inr 1) + y t ω (Sum.inr ()) = 0) := by
  have hE : ∀ j, 𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inr j)) ω = φ (t + 1) ω (Sum.inr j) :=
    fun j => congrFun (hmφ t j) ω
  rw [foc_iff_split _ hmφ y t ω]
  have key : ∀ v : Empty ⊕ Fin 2 → ℝ, v = 0 ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
    intro v
    constructor
    · intro h
      rw [h]
      simp
    · rintro ⟨h0, h1⟩
      funext r
      rcases r with e | j
      · exact e.elim
      · fin_cases j
        · exact h0
        · exact h1
  rw [key, and_assoc]
  simp [p83Problem, p83Sys, LinearRESystem.Ahat, LinearRESystem.Ihat, LQProblem.T, Mpart, EV, hE,
    mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three]

/-- Woodford (2003), (1.1) for `p83Problem` (perfect foresight): `z_{1,t+1} = ½ z_{1t} + c_{1t}`
and `z_{2,t+1} = 2 z_{2t} + i_t + c_{2t}`. -/
theorem p83_structural_iff (c : ℕ → Unit → Fin 2 → ℝ)
    (y : ℕ → Unit → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) :
    p83Sys.Structural perfectForesight c 0 y ↔
      ∀ t, y (t + 1) () (Sum.inl (Sum.inr 0)) = 1 / 2 * y t () (Sum.inl (Sum.inr 0)) + c t () 0 ∧
        y (t + 1) () (Sum.inl (Sum.inr 1)) =
          2 * y t () (Sum.inl (Sum.inr 1)) + y t () (Sum.inr ()) + c t () 1 := by
  unfold LinearRESystem.Structural
  constructor
  · intro h t
    have h0 := congrFun (h t (Nat.zero_le t) ()).2 0
    have h1 := congrFun (h t (Nat.zero_le t) ()).2 1
    simp [p83Sys, EV, zpart, ipart, mulVec, dotProduct, Fin.sum_univ_two,
      perfectForesight] at h0 h1
    constructor <;> linarith
  · intro h t _ ω
    cases ω
    refine ⟨funext fun e => e.elim, funext fun j => ?_⟩
    have := h t
    fin_cases j <;>
      simp [p83Sys, EV, zpart, ipart, mulVec, dotProduct, Fin.sum_univ_two,
        perfectForesight] <;> linarith [this.1, this.2]

/-! ### Assumption 8.1 -/

/-- Woodford (2003), (1.1) + (1.9) for `p83Problem`: the multipliers of any solution satisfy the
two workhorse equations `½ M_{1,t+1} − (9/4) M_{1t} + M_{1,t−1} = −c_{1t}` and
`½ M_{2,t+1} − (7/4) M_{2t} + M_{2,t−1} = −c_{2t}/4`. -/
theorem p83_second {c : ℕ → Unit → Fin 2 → ℝ} {Z0 : Unit → Empty → ℝ} {M0 : Unit → Fin 2 → ℝ}
    {y : ℕ → Unit → (Empty ⊕ Fin 2) ⊕ Unit → ℝ} {φ : ℕ → Unit → Empty ⊕ Fin 2 → ℝ}
    (hsys : FOCSystem p83Problem perfectForesight c 0 Z0 M0 y φ) :
    SecondOrder perfectForesight (1 / 2) (3 / 4) (fun ω => M0 ω 0) (fun t ω => -c t ω 0)
        (fun t ω => φ (t + 1) ω (Sum.inr 0)) ∧
      SecondOrder perfectForesight (1 / 2) (1 / 4) (fun ω => M0 ω 1) (fun t ω => -c t ω 1 / 4)
        (fun t ω => φ (t + 1) ω (Sum.inr 1)) := by
  have hfoc := fun s ω => (p83_foc_at_iff perfectForesight y hsys.2.2.1 s ω).mp
    (hsys.2.2.2.2 s (Nat.zero_le s) ω)
  have hstr := (p83_structural_iff c y).mp hsys.1.1
  have hlag : ∀ j t ω, lagW (fun ω => M0 ω j) (fun t ω => φ (t + 1) ω (Sum.inr j)) t ω =
      φ t ω (Sum.inr j) := by
    intro j t ω
    cases t with
    | zero => exact (congrFun (hsys.2.2.2.1 ω) j).symm
    | succ t => rfl
  refine ⟨fun t ω => ?_, fun t ω => ?_⟩
  · cases ω
    rw [hlag]
    obtain ⟨f0, -, -⟩ := hfoc t ()
    obtain ⟨f1, -, -⟩ := hfoc (t + 1) ()
    obtain ⟨s0, -⟩ := hstr t
    change 1 / 2 * φ (t + 1 + 1) () (Sum.inr 0) - (1 + 1 / 2 + 3 / 4) * φ (t + 1) () (Sum.inr 0) +
      φ t () (Sum.inr 0) = -c t () 0
    linear_combination f1 - (1 / 2 : ℝ) * f0 - s0
  · cases ω
    rw [hlag]
    obtain ⟨-, g0, k0⟩ := hfoc t ()
    obtain ⟨-, g1, -⟩ := hfoc (t + 1) ()
    obtain ⟨-, s1⟩ := hstr t
    change 1 / 2 * φ (t + 1 + 1) () (Sum.inr 1) - (1 + 1 / 2 + 1 / 4) * φ (t + 1) () (Sum.inr 1) +
      φ t () (Sum.inr 1) = -c t () 1 / 4
    linear_combination (1 / 4 : ℝ) * g1 - (1 / 2 : ℝ) * g0 - (1 / 4 : ℝ) * k0 - (1 / 4 : ℝ) * s1

/-- **Woodford (2003), Assumption 8.1, p. 541, for `p83Problem` (perfect foresight)**: for every
bounded disturbance and initial multipliers, (1.1) + (1.9) has exactly one bounded solution. The
multipliers solve the two workhorse equations of `p83_second`
(`InflTargetInertia.secondOrder_existsUnique`, `c = 3/4` and `c = 1/4`), and
`z_{1t} = 2M_{1,t−1} − ½M_{1t}`, `z_{2t} = 2(M_{2,t−1} − M_{2t})`, `i_t = −M_{2t}`. -/
theorem p83_assumption81 : Assumption81 p83Problem perfectForesight 0 := by
  have hβ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hβ1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hpa : ∀ z : ℕ → Unit → ℝ, perfectForesight.Adapted z := fun _ _ => rfl
  refine ⟨fun c Z0 M0 hcb _ _ _ => ?_, fun c Z0 M0 y y' φ φ' h h' t _ => ?_⟩
  · obtain ⟨Mc, hMc⟩ := hcb
    have hf1 : ∀ t ω, |(fun t ω => -c t ω 0) t ω| ≤ Mc := fun t ω => by
      simp only [abs_neg]; exact hMc t ω 0
    have hf2 : ∀ t ω, |(fun t ω => -c t ω 1 / 4) t ω| ≤ Mc := fun t ω => by
      have := hMc t ω 1
      have h0 : 0 ≤ |c t ω 1| := abs_nonneg _
      simp only [abs_div, abs_neg]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith
    obtain ⟨⟨hs1, -, ⟨B1, hB1⟩⟩, -⟩ := secondOrder_existsUnique perfectForesight hβ0 hβ1
      (by norm_num : (0 : ℝ) < 3 / 4) hf1 (hpa _) (y₀ := fun ω => M0 ω 0) (Y := |M0 () 0|)
      (fun ω => by cases ω; exact le_rfl) rfl
    obtain ⟨⟨hs2, -, ⟨B2, hB2⟩⟩, -⟩ := secondOrder_existsUnique perfectForesight hβ0 hβ1
      (by norm_num : (0 : ℝ) < 1 / 4) hf2 (hpa _) (y₀ := fun ω => M0 ω 1) (Y := |M0 () 1|)
      (fun ω => by cases ω; exact le_rfl) rfl
    set A1 := ysol perfectForesight (1 / 2) (3 / 4) (fun ω => M0 ω 0) (fun t ω => -c t ω 0)
    set A2 := ysol perfectForesight (1 / 2) (1 / 4) (fun ω => M0 ω 1) (fun t ω => -c t ω 1 / 4)
    set L1 := lagW (fun ω => M0 ω 0) A1
    set L2 := lagW (fun ω => M0 ω 1) A2
    have hL1 : ∀ t ω, |L1 t ω| ≤ max |M0 () 0| B1 := fun t ω =>
      lagW_bounded (fun ω => by cases ω; exact le_rfl) hB1 t ω
    have hL2 : ∀ t ω, |L2 t ω| ≤ max |M0 () 1| B2 := fun t ω =>
      lagW_bounded (fun ω => by cases ω; exact le_rfl) hB2 t ω
    set yP : ℕ → Unit → (Empty ⊕ Fin 2) ⊕ Unit → ℝ := fun t ω =>
      Sum.elim (Sum.elim (fun e => e.elim) ![2 * L1 t ω - 1 / 2 * A1 t ω,
        2 * L2 t ω - 2 * A2 t ω]) (fun _ => -A2 t ω) with hyP
    set φP : ℕ → Unit → Empty ⊕ Fin 2 → ℝ := fun t ω =>
      Sum.elim (fun e => e.elim) ![L1 t ω, L2 t ω] with hφP
    have hmult : MultiplierMeas perfectForesight φP := fun t r => rfl
    have e1 : ∀ t ω, L1 (t + 1) ω = A1 t ω := fun t ω => rfl
    have e2 : ∀ t ω, L2 (t + 1) ω = A2 t ω := fun t ω => rfl
    set K := max |M0 () 0| B1 + max |M0 () 1| B2 + B1 + B2 with hK
    have hK1 := le_max_left |M0 () 0| B1
    have hK2 := le_max_left |M0 () 1| B2
    have hB1n : 0 ≤ B1 := (abs_nonneg _).trans (hB1 0 ())
    have hB2n : 0 ≤ B2 := (abs_nonneg _).trans (hB2 0 ())
    refine ⟨yP, φP, ⟨⟨?_, fun ω => funext fun e => e.elim, ⟨3 * K, fun t ω i => ?_⟩,
      fun t i => rfl⟩, ⟨K, fun t ω r => ?_⟩, hmult, fun ω => ?_, fun t _ ω => ?_⟩⟩
    · change p83Sys.Structural perfectForesight c 0 yP
      rw [p83_structural_iff]
      intro t
      have h1 := hs1 t ()
      have h2 := hs2 t ()
      change 1 / 2 * A1 (t + 1) () - (1 + 1 / 2 + 3 / 4) * A1 t () + L1 t () = -c t () 0 at h1
      change 1 / 2 * A2 (t + 1) () - (1 + 1 / 2 + 1 / 4) * A2 t () + L2 t () = -c t () 1 / 4 at h2
      constructor
      · change 2 * L1 (t + 1) () - 1 / 2 * A1 (t + 1) () =
          1 / 2 * (2 * L1 t () - 1 / 2 * A1 t ()) + c t () 0
        rw [e1]
        linarith
      · change 2 * L2 (t + 1) () - 2 * A2 (t + 1) () =
          2 * (2 * L2 t () - 2 * A2 t ()) + -A2 t () + c t () 1
        rw [e2]
        linarith
    · have a1 := hL1 t ω
      have a2 := hL2 t ω
      have b1 := hB1 t ω
      have b2 := hB2 t ω
      rcases i with (e | j) | u
      · exact e.elim
      · fin_cases j
        · change |2 * L1 t ω - 1 / 2 * A1 t ω| ≤ 3 * K
          have := abs_sub (2 * L1 t ω) (1 / 2 * A1 t ω)
          rw [abs_mul, abs_mul] at this
          norm_num at this
          nlinarith [abs_nonneg (L1 t ω), abs_nonneg (A1 t ω), abs_nonneg (M0 () 0),
            abs_nonneg (M0 () 1)]
        · change |2 * L2 t ω - 2 * A2 t ω| ≤ 3 * K
          have := abs_sub (2 * L2 t ω) (2 * A2 t ω)
          rw [abs_mul, abs_mul] at this
          norm_num at this
          nlinarith [abs_nonneg (L2 t ω), abs_nonneg (A2 t ω), abs_nonneg (M0 () 0),
            abs_nonneg (M0 () 1)]
      · change |-A2 t ω| ≤ 3 * K
        rw [abs_neg]
        nlinarith [abs_nonneg (M0 () 0), abs_nonneg (M0 () 1)]
    · rcases r with e | j
      · exact e.elim
      · fin_cases j
        · change |L1 t ω| ≤ K
          have := hL1 t ω
          nlinarith [abs_nonneg (M0 () 1), le_max_left |M0 () 1| B2]
        · change |L2 t ω| ≤ K
          have := hL2 t ω
          nlinarith [abs_nonneg (M0 () 0), le_max_left |M0 () 0| B1]
    · funext j
      fin_cases j <;> rfl
    · refine (p83_foc_at_iff perfectForesight yP hmult t ω).mpr ⟨?_, ?_, ?_⟩
      · change 1 / 2 * L1 (t + 1) ω + (2 * L1 t ω - 1 / 2 * A1 t ω) - 2 * L1 t ω = 0
        rw [e1]; ring
      · change 2 * L2 (t + 1) ω + (2 * L2 t ω - 2 * A2 t ω) - 2 * L2 t ω = 0
        rw [e2]; ring
      · change L2 (t + 1) ω + -A2 t ω = 0
        rw [e2]; ring
  · -- uniqueness
    obtain ⟨By, hBy⟩ := h.1.2.2.1
    have hstr := (p83_structural_iff c y).mp h.1.1
    have hcb : ∀ t ω j, |c t ω j| ≤ 4 * By := by
      intro t ω j
      cases ω
      obtain ⟨s0, s1⟩ := hstr t
      have b0 := hBy (t + 1) () (Sum.inl (Sum.inr 0))
      have b1 := hBy t () (Sum.inl (Sum.inr 0))
      have b2 := hBy (t + 1) () (Sum.inl (Sum.inr 1))
      have b3 := hBy t () (Sum.inl (Sum.inr 1))
      have b4 := hBy t () (Sum.inr ())
      fin_cases j
      · change |c t () 0| ≤ 4 * By
        rw [abs_le] at b0 b1 ⊢
        constructor <;> linarith [b0.1, b0.2, b1.1, b1.2]
      · change |c t () 1| ≤ 4 * By
        rw [abs_le] at b2 b3 b4 ⊢
        constructor <;> linarith [b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
    have hf1 : ∀ t ω, |(fun t ω => -c t ω 0) t ω| ≤ 4 * By := fun t ω => by
      simp only [abs_neg]; exact hcb t ω 0
    have hf2 : ∀ t ω, |(fun t ω => -c t ω 1 / 4) t ω| ≤ 4 * By := fun t ω => by
      have := hcb t ω 1
      have h0 : 0 ≤ |c t ω 1| := abs_nonneg _
      simp only [abs_div, abs_neg]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      linarith
    have u1 := (secondOrder_existsUnique perfectForesight hβ0 hβ1
      (by norm_num : (0 : ℝ) < 3 / 4) hf1 (hpa _) (y₀ := fun ω => M0 ω 0) (Y := |M0 () 0|)
      (fun ω => by cases ω; exact le_rfl) rfl).2
    have u2 := (secondOrder_existsUnique perfectForesight hβ0 hβ1
      (by norm_num : (0 : ℝ) < 1 / 4) hf2 (hpa _) (y₀ := fun ω => M0 ω 1) (Y := |M0 () 1|)
      (fun ω => by cases ω; exact le_rfl) rfl).2
    have hMb : ∀ {yy : ℕ → Unit → (Empty ⊕ Fin 2) ⊕ Unit → ℝ}
        {ψ : ℕ → Unit → Empty ⊕ Fin 2 → ℝ}, FOCSystem p83Problem perfectForesight c 0 Z0 M0 yy ψ →
        ∀ j, BoundedProc (fun t ω => ψ (t + 1) ω (Sum.inr j)) := by
      intro yy ψ hs j
      obtain ⟨B, hB⟩ := hs.2.1
      exact ⟨B, fun t ω => hB (t + 1) ω (Sum.inr j)⟩
    have m1 := (u1 _ (p83_second h).1 (hpa _) (hMb h 0)).trans
      (u1 _ (p83_second h').1 (hpa _) (hMb h' 0)).symm
    have m2 := (u2 _ (p83_second h).2 (hpa _) (hMb h 1)).trans
      (u2 _ (p83_second h').2 (hpa _) (hMb h' 1)).symm
    have hM : ∀ s ω j, φ s ω (Sum.inr j) = φ' s ω (Sum.inr j) := by
      intro s ω j
      cases s with
      | zero => exact (congrFun (h.2.2.2.1 ω) j).trans (congrFun (h'.2.2.2.1 ω) j).symm
      | succ s =>
        fin_cases j
        · exact congrFun (congrFun m1 s) ω
        · exact congrFun (congrFun m2 s) ω
    have hfo := fun s ω => (p83_foc_at_iff perfectForesight y h.2.2.1 s ω).mp
      (h.2.2.2.2 s (Nat.zero_le s) ω)
    have hfo' := fun s ω => (p83_foc_at_iff perfectForesight y' h'.2.2.1 s ω).mp
      (h'.2.2.2.2 s (Nat.zero_le s) ω)
    refine ⟨funext fun ω => funext fun i => ?_, funext fun ω => funext fun i => ?_⟩
    · obtain ⟨a1, a2, a3⟩ := hfo t ω
      obtain ⟨b1, b2, b3⟩ := hfo' t ω
      rw [hM, hM] at a1 a2
      rw [hM] at a3
      rcases i with (e | j) | u
      · exact e.elim
      · fin_cases j
        · change y t ω (Sum.inl (Sum.inr 0)) = y' t ω (Sum.inl (Sum.inr 0))
          linarith
        · change y t ω (Sum.inl (Sum.inr 1)) = y' t ω (Sum.inl (Sum.inr 1))
          linarith
      · linarith
    · rcases i with e | j
      · exact e.elim
      · exact hM t ω j

/-! ### Assumptions 8.3 and 8.7 and the circle root -/

/-- Woodford (2003), eq. (1.15) for `p83Problem`: `det(A − μÎ) = (μ − ½)(μ − 2)`. -/
theorem p83_pencilPoly : p83Sys.pencilPoly = (X - C (1 / 2)) * (X - C 2) := by
  refine Polynomial.funext fun μ => ?_
  rw [pencilPoly_eval, Prop83.det_empty_sum, det_fin_two]
  simp [toBlocks₂₂, LinearRESystem.Ahat, LinearRESystem.Ihat, p83Sys]
  ring

/-- Woodford (2003), (1.15) for `p83Problem`: the roots are `½` and `2`. -/
theorem p83_roots : p83Sys.pencilPoly.roots = {1 / 2, 2} := by
  rw [p83_pencilPoly, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

/-- Woodford (2003), p. 547: `A` is invertible, `rank A = 2`. -/
theorem p83_rankA : p83Sys.Ahat.rank = 2 := by
  have h : IsUnit p83Sys.Ahat.det := by
    rw [Prop83.det_empty_sum]
    exact p83Sys.A22_isUnit
  rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr h)]
  simp

/-- **Woodford (2003), Assumption 8.3, App. G.1, p. 716, for `p83Problem`**: (1.15) is nonzero,
its nonzero roots `½, 2` are distinct, and their number is `rank Ẽ + rank A − n_z = 2`. -/
theorem p83_assumption83 : Nonempty (Assumption83 p83Sys) := by
  have hne : (1 / 2 : ℂ) ≠ 2 := by norm_num
  have hnz : nonzeroRoots p83Sys = {1 / 2, 2} := by
    rw [nonzeroRoots, p83_roots]
    simp
  refine Assumption83.ofRoots _ ?_ ?_ ?_
  · rw [p83_pencilPoly]
    exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  · rw [hnz]
    simpa using hne
  · rw [hnz, p83_rankA]
    change 2 = (1 : Matrix (Fin 2) (Fin 2) ℝ).rank + 2 - 2
    rw [rank_one]
    simp

/-- **Woodford (2003), Assumption 8.7, p. 556, for `p83Problem`, with `m = 1`**, and the root `2`
of (1.15) lies on `|μ| = β⁻¹`. -/
theorem p83_stableCount : p83Sys.stableCount (1 / 2 : ℝ)⁻¹ = Fintype.card Empty + 1 ∧
    (2 : ℂ) ∈ p83Sys.pencilPoly.roots ∧ ‖(2 : ℂ)‖ = (1 / 2 : ℝ)⁻¹ := by
  refine ⟨?_, by rw [p83_roots]; simp, by norm_num⟩
  unfold LinearRESystem.stableCount
  rw [p83_rankA, p83_roots]
  norm_num [Multiset.filter_cons]

/-! ### Two representations of Proposition 8.1 -/

/-- Woodford (2003), Proposition 8.1 for `p83Problem` (perfect foresight): the representation from
the empty split, with `Λ = β⁻¹ (A₂₂')⁻¹ = diag(4, 1)`. -/
noncomputable def p83Rep : Prop81ConclusionM p83Problem perfectForesight 0 :=
  prop81 p83Problem (emptySplit' p83Sys (1 / 2)) perfectForesight 0

/-- Woodford (2003), (1.20) for `p83Problem`: `Λ = diag(4, 1)`. -/
theorem p83Rep_Λ : p83Rep.Λ = !![4, 0; 0, 1] := by
  change Λmat p83Sys (1 / 2) 0 = _
  rw [Λmat_empty]
  have hinv : (p83Sys.A22ᵀ)⁻¹ = !![2, 0; 0, 1 / 2] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [p83Sys, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [p83Sys]

/-- Woodford (2003), (1.20) homogeneous: for `ρ > 1` the bounded solutions of
`D_{t+1} = diag(ρ, 1) D_t` from `t₀` are exactly `D_{t,1} = 0`, `D_{t,2}` constant. -/
theorem diag_hom {ρ : ℝ} (hρ : 1 < ρ) (t0 : ℕ) {D : ℕ → Fin 2 → ℝ} (hD : BddS D) :
    (∀ t, t0 ≤ t → D (t + 1) = !![ρ, 0; 0, 1] *ᵥ D t) ↔
      ∀ t, t0 ≤ t → D t 0 = 0 ∧ D (t + 1) = D t := by
  have hmv : ∀ v : Fin 2 → ℝ, !![ρ, 0; 0, 1] *ᵥ v = ![ρ * v 0, v 1] := by
    intro v
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have h0 : ∀ n, D (t0 + n) 0 = ρ ^ n * D t0 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := congrFun (h (t0 + n) (by omega)) 0
        rw [hmv] at this
        simp only [Matrix.cons_val_zero] at this
        rw [← add_assoc, this, ih, pow_succ]
        ring
    have hc : D t0 0 = 0 := by
      obtain ⟨K, hK⟩ := hD
      by_contra hne
      have hpos : 0 < |D t0 0| := abs_pos.mpr hne
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K / |D t0 0|) hρ
      have := hK (t0 + n) 0
      rw [h0 n, abs_mul, abs_of_pos (pow_pos (by linarith) n)] at this
      have := (div_lt_iff₀ hpos).mp hn
      linarith
    intro t ht
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    refine ⟨by rw [h0 n, hc, mul_zero], ?_⟩
    rw [h (t0 + n) ht, hmv]
    funext i
    fin_cases i
    · simp [h0 n, hc]
    · simp
  · intro h t ht
    rw [hmv, (h t ht).2]
    funext i
    fin_cases i
    · simp [(h t ht).1]
    · simp

/-- Woodford (2003), Proposition 8.1 for `p83Problem`: the second representation, with the Jordan
block `Λ' = [[1, 0], [1, 1]]` (`TidyR5bReRep.reRep`): `diag(4, 1)` and `Λ'` have the same bounded
homogeneous solutions, and the forcing `(1, 0)` makes `M_{t+1} = Λ' M_t + (1, 0)` explode. -/
noncomputable def p83Rep' : Prop81ConclusionM p83Problem perfectForesight 0 :=
  reRep p83Rep (jΛ 1)
    (by
      rw [p83Rep_Λ]
      intro D hD
      rw [diag_hom (by norm_num) 0 hD, jΛ_hom one_ne_zero 0 hD])
    (fun _ _ => ![1, 0]) (fun _ _ _ => ⟨1, fun t i => by fin_cases i <;> simp⟩)
    (fun _ _ _ D hD => jΛ_blowUp 1 0 D hD)

/-- Woodford (2003), (1.22) for the natural representation: `α(L) = (1 − 4L)(1 − L)` has exactly
`m = 1` zero inside the unit circle (`1/4`), consistent with Proposition 8.3. -/
theorem natural_zerosInside : TargetCriterion.zerosInside (alpha p83Rep.Λ) = 1 := by
  rw [Prop83.zerosInside_alpha, p83Rep_Λ]
  have hcp : (Prop83.cmat (!![4, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)).charpoly =
      (X - C 4) * (X - C 1) := by
    rw [charpoly, det_fin_two]
    simp [Prop83.cmat]
  rw [hcp, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C]
  norm_num [Multiset.filter_singleton]

/-- **Woodford (2003), Proposition 8.3, pp. 556–557 — a counterexample satisfying the full
Assumption 8.1.** `p83Problem` satisfies Assumption 8.1 (existence and uniqueness of bounded
solutions of (1.1) + (1.9) for every bounded disturbance and initial multipliers, perfect
foresight), Assumption 8.3 and Assumption 8.7 with `m = 1`; the root `2` of (1.15) lies on
`|μ| = β⁻¹`. The representation `p83Rep'` of Proposition 8.1 (in the book's original form
`Prop81Conclusion`) has `α(L) = (1 − L)²`, with **no** zero inside the unit circle: the claim of
Proposition 8.3 (`TargetCriterion.Prop83Claim`) is false for it. So the hypothesis "no root on
`|μ| = β⁻¹`" of `Prop83.prop83` cannot be dropped even under the full Assumption 8.1. -/
theorem prop83_fails_on_circle :
    Assumption81 p83Problem perfectForesight 0 ∧ Nonempty (Assumption83 p83Sys) ∧
      p83Sys.stableCount (1 / 2 : ℝ)⁻¹ = Fintype.card Empty + 1 ∧
      (∃ l ∈ p83Sys.pencilPoly.roots, ‖l‖ = (1 / 2 : ℝ)⁻¹) ∧
      TargetCriterion.zerosInside (alpha (toPlain p83Rep').Λ) = 0 ∧
      ¬ TargetCriterion.Prop83Claim p83Problem perfectForesight 0 (toPlain p83Rep') := by
  obtain ⟨hc, hr, hn⟩ := p83_stableCount
  have hz : TargetCriterion.zerosInside (alpha (toPlain p83Rep').Λ) = 0 := by
    change TargetCriterion.zerosInside (alpha (jΛ 1)) = 0
    have : jΛ 1 = Prop83.jordanΛ := rfl
    rw [this]
    exact Prop83.jordanΛ_zeros.1
  refine ⟨p83_assumption81, p83_assumption83, hc, ⟨2, hr, hn⟩, hz, fun h => ?_⟩
  have := h 1 hc le_rfl
  rw [hz] at this
  exact zero_ne_one this

end Woodford.OptimalPolicyRules.TidyR5bProp83Circle
