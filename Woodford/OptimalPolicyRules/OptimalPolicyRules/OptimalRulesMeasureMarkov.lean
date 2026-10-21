/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasure

/-!
# Proposition 8.2: the optimal equilibrium has the linear form (1.5)

Woodford (2003), *Interest and Prices*, Chapter 8, Section 1.4, Proposition 8.2 (p. 555), with
the Definition of pp. 538–539 ((1.5)–(1.6)) and Assumption 8.1 (p. 541): "In this equilibrium,
`z_t` each period is given by a linear relation of the form (1.5), where `s̄_t = s_t` (the exogenous
state vector required to define the possible evolution of the target variables from date `t`
onward) and `Z̄_t` is given by (1.24)."

The claim needs a finite-dimensional exogenous state whose law of motion is time invariant. Here
the disturbance is `c_t = C₂ s_t` with `s_t ∈ ℝ^{ι_s}` a VAR(1) in the conditional-expectation
sense, `E_t s_{t+1} = A s_t` a.s. (`IsVAR`; e.g. `s_{t+1} = A s_t + b ε_{t+1}` with i.i.d.
shocks, `OptimalRulesMeasureIID`), on an arbitrary probability space with an arbitrary
filtration.

## The argument

* **Perfect foresight fixes the coefficients.** Under the deterministic Assumption 8.1
  (`GeneralFOC.LQ.Assumption81 P perfectForesight 0`, the core statement; it holds e.g. for the
  basic model, `NKAssumption81.NK.nk_assumption81_perfectForesight`), the bounded solution of
  (1.1) + (1.9) from the state `X = (Z, M, s)` with forcing `C₂ Aᵏ s` is unique (`pfY`, `pfΦ`). By
  uniqueness it is affine in `X` (`pf_affine`, from `GeneralFOC.LQ.affine_comb_focSystem`) and
  time invariant (`pf_shift`). An affine map on `ℝⁿ` is a vector plus a matrix
  (`exists_affine_matrix`), which gives the **time-invariant coefficient matrices** `fY`, `FY`.
* **Conditional forecasts of any solution are the perfect-foresight path.** For any bounded
  solution `(y, φ)` of the measure-theoretic system (1.1) + (1.9) and any `t ≥ t₀`, almost
  every `ω` gives a bounded deterministic solution `k ↦ E_t y_{t+k}(ω)` from the state
  `X_t(ω) = (Z_t, M_{t−1}, s_t)(ω)` (`forecast_focSystem`: linearity, the law of iterated
  expectations and `E_t s_{t+k} = Aᵏ s_t`). Uniqueness under perfect foresight gives
  `E_t y_{t+k} = pfY(X_t)_k` (`forecast_eq`), and at `k = 0`, **`y_t = fY + FY X_t` a.s.**
  (`linear_form`, `mult_form`, `state_transition`; `prop82_linear_form`: (1.5) with
  `Z̄_t = (Z_t, M_{t−1})`, `s̄_t = s_t`, the coefficients chosen before the probability space).
* Uniqueness (`m_focUnique_var`) and, under geometric stability of the endogenous state
  transition `Hn` (`Hn_apply`: an intrinsic perfect-foresight object), existence
  (`m_focSolvable_var`) of the bounded solution follow, so **Assumption 8.1 holds on every such
  VAR economy** (`m_existsUnique_var`).
* The solution is **optimal** a.s. subject to (1.27) (`OptimalRulesMeasure`'s Lagrangian
  sufficiency) and its target path is a.s. unique; it is **optimal from a timeless perspective**
  in the sense of the Definition with the substantive state `X̄_t = (Z_t, M_{t−1}, s_t)`
  (`timelesslyOptimal_var`).
* **(1.24).** With the deflating split of Proposition 8.1 (`PencilSplit.DeflatingSplit`) and
  Assumption 8.5, the multipliers satisfy (1.20) `M_t = Λ M_{t−1} + q_t` and (1.19)
  `B₂'M_t + v_t = 0` a.s., where `q_t = E_t Q(L⁻¹) T̃'W(τ_t − τ*)` is evaluated on the
  conditional forecasts (`qM`); hence the target criterion (1.23) holds (`criterion_var`) and
  `M_{t−1} = g(q_{t−1}, …, q_{t−D}, v_{t−1}, …, v_{t−D})` with one fixed linear `g`
  (`multiplier_rule_var`, `gRule_add`, `gRule_smul`), so that **`z_t` is a time-invariant linear
  function of `Z̄_t = (Z_t, q_{t−1..t−D}, v_{t−1..t−D})` of (1.24) and `s_t`**
  (`prop82_linear_form_124`).
* Links: the hypothesis `GeneralFOC.LQ.Assumption81 P perfectForesight 0` is the
  measure-theoretic Assumption 8.1 on the one-point probability space
  (`OptimalRulesMeasure.Bridge.unit_assumption81_iff`); (1.19)–(1.20) come from the core
  `Prop81General.prop81`, (1.23) from `TargetCriterion.Crit.eq123_of_eq119_eq120` and the rule `g`
  from `Prop82General.KrylovBound.multiplier_rule`, applied along the conditional forecasts.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureMarkov

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure

/-! ### Affine maps are matrices -/

/-- Woodford (2003), (1.5) and (1.10)–(1.12), pp. 538–542 (tool): a map `g : ℝ^κ → ℝ^ν` that
preserves affine combinations (weights summing to one) is `x ↦ f⁰ + F x` for a vector `f⁰` and a
matrix `F`. -/
theorem exists_affine_matrix {κ ν : Type*} [Fintype κ] (g : (κ → ℝ) → ν → ℝ)
    (hg : ∀ (w1 w2 w3 : ℝ) (x1 x2 x3 : κ → ℝ), w1 + w2 + w3 = 1 →
      g (w1 • x1 + w2 • x2 + w3 • x3) = w1 • g x1 + w2 • g x2 + w3 • g x3) :
    ∃ (f0 : ν → ℝ) (F : Matrix ν κ ℝ), ∀ x, g x = f0 + F *ᵥ x := by
  classical
  let L : (κ → ℝ) →ₗ[ℝ] (ν → ℝ) :=
    { toFun := fun x => g x - g 0
      map_add' := fun x1 x2 => by
        have h := hg 1 1 (-1) x1 x2 0 (by norm_num)
        simp only [one_smul, smul_zero, add_zero, neg_smul] at h
        change g (x1 + x2) - g 0 = (g x1 - g 0) + (g x2 - g 0)
        rw [h]
        abel
      map_smul' := fun a x => by
        have h := hg a (1 - a) 0 x 0 0 (by ring)
        simp only [smul_zero, add_zero, zero_smul] at h
        change g (a • x) - g 0 = a • (g x - g 0)
        rw [h, sub_smul, one_smul, smul_sub]
        abel }
  refine ⟨g 0, LinearMap.toMatrix' L, fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  change g x = g 0 + (g x - g 0)
  abel

/-! ### The perfect-foresight solution map -/

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ιZ ιz ιτ ιs : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs]
  [DecidableEq ιZ] [DecidableEq ιz] [DecidableEq ιs]

/-- Woodford (2003), p. 537 (the exogenous state is a finite VAR): the matrix `A` has bounded
powers, so `Aᵏ s` is a bounded forecast path. -/
def PowBdd (A : Matrix ιs ιs ℝ) : Prop := ∃ K, ∀ k i j, |(A ^ k) i j| ≤ K

/-- Woodford (2003), p. 537: the state vector `X = ((Z, M), s)` — predetermined variables, lagged
multipliers and the exogenous state. -/
def mkX (n : ιZ ⊕ ιz → ℝ) (σ : ιs → ℝ) : (ιZ ⊕ ιz) ⊕ ιs → ℝ := Sum.elim n σ

/-- Woodford (2003), p. 537: the predetermined block `Z` of a state vector. -/
def Xz (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) : ιZ → ℝ := fun j => X (Sum.inl (Sum.inl j))

/-- Woodford (2003), p. 540: the lagged-multiplier block `M` of a state vector. -/
def Xm (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) : ιz → ℝ := fun r => X (Sum.inl (Sum.inr r))

/-- Woodford (2003), p. 537: the exogenous block `s` of a state vector. -/
def Xs (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) : ιs → ℝ := fun i => X (Sum.inr i)

/-- Woodford (2003), p. 537, (1.1): the perfect-foresight forcing `c_k = C₂ Aᵏ s` of the VAR
started at `s`. -/
def cpf (A : Matrix ιs ιs ℝ) (C2 : Matrix ιz ιs ℝ) (σ : ιs → ℝ) : ℕ → Unit → ιz → ℝ :=
  fun k _ => C2 *ᵥ (A ^ k *ᵥ σ)

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 4, p. 537: the perfect-foresight forcing of a VAR with bounded powers is
bounded. -/
theorem cpf_bounded [Finite ιz] {A : Matrix ιs ιs ℝ} (hA : PowBdd A) (C2 : Matrix ιz ιs ℝ)
    (σ : ιs → ℝ) : BoundedV (cpf A C2 σ) := by
  obtain ⟨K, hK⟩ := hA
  obtain ⟨K2, hK2⟩ := exists_bound_mulVec C2 (∑ j, K * |σ j|)
  refine ⟨K2, fun k _ r => hK2 _ (fun i => ?_) r⟩
  calc |(A ^ k *ᵥ σ) i| = |∑ j, (A ^ k) i j * σ j| := rfl
    _ ≤ ∑ j, |(A ^ k) i j * σ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, K * |σ j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hK k i j) (abs_nonneg _)

variable (P : LQProblem ιZ ιz ιτ) (A : Matrix ιs ιs ℝ) (C2 : Matrix ιz ιs ℝ)

/-- Woodford (2003), Assumption 8.1, p. 541, under perfect foresight: from every state
`X = (Z, M, s)` the system (1.1) + (1.9) with forcing `C₂ Aᵏ s` has a bounded solution. -/
theorem pf_exists (hA81 : Assumption81 P perfectForesight 0) (hA : PowBdd A)
    (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) :
    ∃ y φ, FOCSystem P perfectForesight (cpf A C2 (Xs X)) 0 (fun _ => Xz X) (fun _ => Xm X) y φ :=
  hA81.solvable _ _ _ (cpf_bounded hA C2 (Xs X)) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- Woodford (2003), Assumption 8.1, p. 541: the bounded perfect-foresight plan from the state
`X` (unique, `pf_unique`). -/
noncomputable def pfY (hA81 : Assumption81 P perfectForesight 0) (hA : PowBdd A)
    (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ :=
  Classical.choose (pf_exists P A C2 hA81 hA X)

/-- Woodford (2003), Assumption 8.1, p. 541: the multipliers of the bounded perfect-foresight
plan from the state `X`. -/
noncomputable def pfΦ (hA81 : Assumption81 P perfectForesight 0) (hA : PowBdd A)
    (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) : ℕ → Unit → ιZ ⊕ ιz → ℝ :=
  Classical.choose (Classical.choose_spec (pf_exists P A C2 hA81 hA X))

variable (hA81 : Assumption81 P perfectForesight 0) (hA : PowBdd A)

/-- Woodford (2003), Assumption 8.1, p. 541: `(pfY, pfΦ)` solves (1.1) + (1.9) under perfect
foresight from the state `X`. -/
theorem pf_spec (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) :
    FOCSystem P perfectForesight (cpf A C2 (Xs X)) 0 (fun _ => Xz X) (fun _ => Xm X)
      (pfY P A C2 hA81 hA X) (pfΦ P A C2 hA81 hA X) :=
  Classical.choose_spec (Classical.choose_spec (pf_exists P A C2 hA81 hA X))

/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541, under perfect foresight: every bounded
solution from the state `X` is `(pfY X, pfΦ X)`. -/
theorem pf_unique (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) {y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Unit → ιZ ⊕ ιz → ℝ}
    (h : FOCSystem P perfectForesight (cpf A C2 (Xs X)) 0 (fun _ => Xz X) (fun _ => Xm X) y φ) :
    ∀ k, y k = pfY P A C2 hA81 hA X k ∧ φ k = pfΦ P A C2 hA81 hA X k := fun k =>
  hA81.unique _ _ _ _ _ _ _ h (pf_spec P A C2 hA81 hA X) k (Nat.zero_le k)

/-- Woodford (2003), p. 539 (time invariance): the state reached after one period of the
perfect-foresight plan from `X`, `(Z_1, M_0, A s)`. -/
noncomputable def nextX (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) : (ιZ ⊕ ιz) ⊕ ιs → ℝ :=
  mkX (Sum.elim (Zpart (pfY P A C2 hA81 hA X 1 ())) (Mpart (pfΦ P A C2 hA81 hA X 1 ())))
    (A *ᵥ Xs X)

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 537 (tool): `C₂ A^{k+1} s = C₂ Aᵏ (A s)`. -/
theorem cpf_succ (σ : ιs → ℝ) (k : ℕ) : cpf A C2 σ (k + 1) = cpf A C2 (A *ᵥ σ) k := by
  funext u
  simp only [cpf, pow_succ, mulVec_mulVec]

/-- Woodford (2003), p. 539: **time invariance of the perfect-foresight plan** — continuing the
plan from `X` one period later is the plan from the state it reaches, `nextX X`. -/
theorem pf_shift (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) (k : ℕ) :
    pfY P A C2 hA81 hA X (k + 1) = pfY P A C2 hA81 hA (nextX P A C2 hA81 hA X) k ∧
      pfΦ P A C2 hA81 hA X (k + 1) = pfΦ P A C2 hA81 hA (nextX P A C2 hA81 hA X) k := by
  obtain ⟨⟨hst, -, ⟨Ky, hKy⟩, -⟩, ⟨Kφ, hKφ⟩, -, -, hfoc⟩ := pf_spec P A C2 hA81 hA X
  refine pf_unique P A C2 hA81 hA (nextX P A C2 hA81 hA X)
    (y := fun j => pfY P A C2 hA81 hA X (j + 1)) (φ := fun j => pfΦ P A C2 hA81 hA X (j + 1))
    ⟨⟨fun t _ ω => ?_, fun ω => ?_, ⟨Ky, fun t ω => hKy _ ω⟩,
    fun _ _ => rfl⟩, ⟨Kφ, fun t ω => hKφ _ ω⟩, fun _ _ => rfl, fun ω => ?_,
    fun t _ ω => ?_⟩ k
  · obtain ⟨h1, h2⟩ := hst (t + 1) (Nat.zero_le _) ω
    refine ⟨h1, ?_⟩
    have hc : cpf A C2 (Xs (nextX P A C2 hA81 hA X)) t = cpf A C2 (Xs X) (t + 1) :=
      (cpf_succ A C2 (Xs X) t).symm
    rw [hc]
    exact h2
  · rfl
  · rfl
  · exact hfoc (t + 1) (Nat.zero_le _) ω

/-- Woodford (2003), (1.10), p. 542: **the perfect-foresight plan is affine in the state** (by
uniqueness, `GeneralFOC.LQ.affine_comb_focSystem`). -/
theorem pf_affine {w1 w2 w3 : ℝ} (hw : w1 + w2 + w3 = 1) (X1 X2 X3 : (ιZ ⊕ ιz) ⊕ ιs → ℝ)
    (k : ℕ) :
    pfY P A C2 hA81 hA (w1 • X1 + w2 • X2 + w3 • X3) k =
        comb3 w1 w2 w3 (pfY P A C2 hA81 hA X1) (pfY P A C2 hA81 hA X2)
          (pfY P A C2 hA81 hA X3) k ∧
      pfΦ P A C2 hA81 hA (w1 • X1 + w2 • X2 + w3 • X3) k =
        comb3 w1 w2 w3 (pfΦ P A C2 hA81 hA X1) (pfΦ P A C2 hA81 hA X2)
          (pfΦ P A C2 hA81 hA X3) k := by
  have hc := affine_comb_focSystem hw (pf_spec P A C2 hA81 hA X1) (pf_spec P A C2 hA81 hA X2)
    (pf_spec P A C2 hA81 hA X3)
  have e1 : comb3 w1 w2 w3 (cpf A C2 (Xs X1)) (cpf A C2 (Xs X2)) (cpf A C2 (Xs X3)) =
      cpf A C2 (Xs (w1 • X1 + w2 • X2 + w3 • X3)) := by
    funext t u
    have hs : Xs (w1 • X1 + w2 • X2 + w3 • X3) = w1 • Xs X1 + w2 • Xs X2 + w3 • Xs X3 := rfl
    simp only [comb3, cpf, hs, mulVec_add, mulVec_smul]
  have e2 : (fun (_ : Unit) => w1 • Xz X1 + w2 • Xz X2 + w3 • Xz X3) =
      fun _ => Xz (w1 • X1 + w2 • X2 + w3 • X3) := rfl
  have e3 : (fun (_ : Unit) => w1 • Xm X1 + w2 • Xm X2 + w3 • Xm X3) =
      fun _ => Xm (w1 • X1 + w2 • X2 + w3 • X3) := rfl
  rw [e1, e2, e3] at hc
  have := pf_unique P A C2 hA81 hA _ hc k
  exact ⟨this.1.symm, this.2.symm⟩

/-! ### The time-invariant coefficient matrices -/

/-- Woodford (2003), (1.5), p. 538: the date-0 plan `y_0 = pfY(X)_0` of the perfect-foresight
solution is an affine function of the state `X = (Z, M, s)`. -/
theorem pfY0_affine : ∃ (f0 : (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (F : Matrix ((ιZ ⊕ ιz) ⊕ Unit) ((ιZ ⊕ ιz) ⊕ ιs) ℝ),
    ∀ X, pfY P A C2 hA81 hA X 0 () = f0 + F *ᵥ X :=
  exists_affine_matrix (fun X => pfY P A C2 hA81 hA X 0 ()) fun _ _ _ X1 X2 X3 hw => by
    rw [(pf_affine P A C2 hA81 hA hw X1 X2 X3 0).1]
    rfl

/-- Woodford (2003), (1.17), p. 551: the date-0 multipliers of the perfect-foresight solution are
an affine function of the state. -/
theorem pfΦ0_affine : ∃ (g0 : ιZ ⊕ ιz → ℝ) (G : Matrix (ιZ ⊕ ιz) ((ιZ ⊕ ιz) ⊕ ιs) ℝ),
    ∀ X, pfΦ P A C2 hA81 hA X 0 () = g0 + G *ᵥ X :=
  exists_affine_matrix (fun X => pfΦ P A C2 hA81 hA X 0 ()) fun _ _ _ X1 X2 X3 hw => by
    rw [(pf_affine P A C2 hA81 hA hw X1 X2 X3 0).2]
    rfl

/-- Woodford (2003), p. 539: the next endogenous state `(Z_1, M_0)` of the perfect-foresight
solution from `X`. -/
noncomputable def nextN (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) : ιZ ⊕ ιz → ℝ :=
  Sum.elim (Zpart (pfY P A C2 hA81 hA X 1 ())) (Mpart (pfΦ P A C2 hA81 hA X 1 ()))

/-- Woodford (2003), p. 539: the endogenous state transition `(Z_{t+1}, M_t) = h⁰ + H X_t` is
affine in the state. -/
theorem nextN_affine : ∃ (h0 : ιZ ⊕ ιz → ℝ) (H : Matrix (ιZ ⊕ ιz) ((ιZ ⊕ ιz) ⊕ ιs) ℝ),
    ∀ X, nextN P A C2 hA81 hA X = h0 + H *ᵥ X :=
  exists_affine_matrix (nextN P A C2 hA81 hA) fun _ _ _ X1 X2 X3 hw => by
    have h1 := (pf_affine P A C2 hA81 hA hw X1 X2 X3 1).1
    have h2 := (pf_affine P A C2 hA81 hA hw X1 X2 X3 1).2
    funext i
    rcases i with i | i
    · simp only [nextN, h1, Sum.elim_inl, Pi.add_apply, Pi.smul_apply]
      rfl
    · simp only [nextN, h2, Sum.elim_inr, Pi.add_apply, Pi.smul_apply]
      rfl

/-- Woodford (2003), (1.5), p. 538: the **time-invariant intercept** `f⁰` of the plan. -/
noncomputable def fY : (ιZ ⊕ ιz) ⊕ Unit → ℝ := Classical.choose (pfY0_affine P A C2 hA81 hA)

/-- Woodford (2003), (1.5), p. 538: the **time-invariant coefficient matrix** `F = [f_Z f_s]`
of the plan on the state `(Z, M, s)`. -/
noncomputable def FY : Matrix ((ιZ ⊕ ιz) ⊕ Unit) ((ιZ ⊕ ιz) ⊕ ιs) ℝ :=
  Classical.choose (Classical.choose_spec (pfY0_affine P A C2 hA81 hA))

/-- Woodford (2003), (1.5): `pfY(X)_0 = f⁰ + F X`. -/
theorem fY_spec (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) :
    pfY P A C2 hA81 hA X 0 () = fY P A C2 hA81 hA + FY P A C2 hA81 hA *ᵥ X :=
  Classical.choose_spec (Classical.choose_spec (pfY0_affine P A C2 hA81 hA)) X

/-- Woodford (2003), (1.17): the intercept of the date-0 multipliers. -/
noncomputable def fΦ : ιZ ⊕ ιz → ℝ := Classical.choose (pfΦ0_affine P A C2 hA81 hA)

/-- Woodford (2003), (1.17): the coefficient matrix of the date-0 multipliers on the state. -/
noncomputable def FΦ : Matrix (ιZ ⊕ ιz) ((ιZ ⊕ ιz) ⊕ ιs) ℝ :=
  Classical.choose (Classical.choose_spec (pfΦ0_affine P A C2 hA81 hA))

/-- Woodford (2003), (1.17): `pfΦ(X)_0 = g⁰ + G X`. -/
theorem fΦ_spec (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) :
    pfΦ P A C2 hA81 hA X 0 () = fΦ P A C2 hA81 hA + FΦ P A C2 hA81 hA *ᵥ X :=
  Classical.choose_spec (Classical.choose_spec (pfΦ0_affine P A C2 hA81 hA)) X

/-- Woodford (2003), p. 539: the intercept `h⁰` of the endogenous state transition. -/
noncomputable def hN : ιZ ⊕ ιz → ℝ := Classical.choose (nextN_affine P A C2 hA81 hA)

/-- Woodford (2003), p. 539: the matrix `H` of the endogenous state transition. -/
noncomputable def HN : Matrix (ιZ ⊕ ιz) ((ιZ ⊕ ιz) ⊕ ιs) ℝ :=
  Classical.choose (Classical.choose_spec (nextN_affine P A C2 hA81 hA))

/-- Woodford (2003), p. 539: `(Z_1, M_0) = h⁰ + H X`. -/
theorem hN_spec (X : (ιZ ⊕ ιz) ⊕ ιs → ℝ) :
    nextN P A C2 hA81 hA X = hN P A C2 hA81 hA + HN P A C2 hA81 hA *ᵥ X :=
  Classical.choose_spec (Classical.choose_spec (nextN_affine P A C2 hA81 hA)) X

/-! ### Conditional expectations of random vectors -/

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): `E_t` respects a.s. equality of random vectors. -/
theorem EVm_congr (S : MeasExpectationSystem Ω) {ι : Type*} [Countable ι] (t : ℕ)
    {x x' : Ω → ι → ℝ} (h : ∀ᵐ ω ∂S.μ, x ω = x' ω) :
    ∀ᵐ ω ∂S.μ, EVm S t x ω = EVm S t x' ω := by
  have hc : ∀ i, S.E t (fun ω => x ω i) =ᵐ[S.μ] S.E t (fun ω => x' ω i) := fun i =>
    S.E_congr (h.mono fun ω e => congrFun e i) t
  filter_upwards [ae_all_iff.2 hc] with ω e
  exact funext e

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): `E_t` is additive on integrable random vectors (a.s.). -/
theorem EVm_add (S : MeasExpectationSystem Ω) {ι : Type*} [Countable ι] (t : ℕ)
    {x x' : Ω → ι → ℝ} (hx : ∀ i, Integrable (fun ω => x ω i) S.μ)
    (hx' : ∀ i, Integrable (fun ω => x' ω i) S.μ) :
    ∀ᵐ ω ∂S.μ, EVm S t (fun ω => x ω + x' ω) ω = EVm S t x ω + EVm S t x' ω := by
  have hc : ∀ i, S.E t (fun ω => x ω i + x' ω i) =ᵐ[S.μ]
      fun ω => S.E t (fun ω => x ω i) ω + S.E t (fun ω => x' ω i) ω := fun i =>
    S.E_add (hx i) (hx' i) t
  filter_upwards [ae_all_iff.2 hc] with ω e
  funext i
  exact e i

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): constants are their own forecast. -/
theorem EVm_const (S : MeasExpectationSystem Ω) {ι : Type*} (t : ℕ) (v : ι → ℝ) :
    EVm S t (fun _ => v) = fun _ => v := by
  funext ω i
  exact congrFun (S.E_const t (v i)) ω

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): the law of iterated expectations for random vectors,
`E_t E_s = E_t` for `t ≤ s` (a.s.). -/
theorem EVm_tower (S : MeasExpectationSystem Ω) {ι : Type*} [Countable ι] {t s : ℕ}
    (hts : t ≤ s) (x : Ω → ι → ℝ) :
    ∀ᵐ ω ∂S.μ, EVm S t (EVm S s x) ω = EVm S t x ω := by
  have hc : ∀ i, S.E t (S.E s (fun ω => x ω i)) =ᵐ[S.μ] S.E t (fun ω => x ω i) := fun i =>
    S.E_tower hts _
  filter_upwards [ae_all_iff.2 hc] with ω e
  funext i
  exact e i

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): a random vector known at `t` is its own forecast (exactly). -/
theorem EVm_of_known (S : MeasExpectationSystem Ω) {ι : Type*} {t : ℕ} {x : Ω → ι → ℝ}
    (hk : MKnownV S t x) (hi : ∀ i, Integrable (fun ω => x ω i) S.μ) : EVm S t x = x := by
  funext ω i
  exact congrFun (S.E_of_stronglyMeasurable (hk i) (hi i)) ω

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): matrices map integrable random vectors to integrable ones. -/
theorem integrable_mulVec {μ : Measure Ω} {ι κ : Type*} [Fintype ι] (B : Matrix κ ι ℝ)
    {x : Ω → ι → ℝ} (hx : ∀ i, Integrable (fun ω => x ω i) μ) (r : κ) :
    Integrable (fun ω => (B *ᵥ x ω) r) μ := by
  have : (fun ω => (B *ᵥ x ω) r) = fun ω => ∑ i, B r i * x ω i := rfl
  rw [this]
  exact integrable_finsetSum _ fun i _ => (hx i).const_mul _

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): `E_t` of an affine function of three random vectors,
`E_t (B₁ x₁ + B₂ x₂ + B₃ x₃ + b) = B₁ E_t x₁ + B₂ E_t x₂ + B₃ E_t x₃ + b` (a.s.). -/
theorem EVm_affine3 (S : MeasExpectationSystem Ω) {ι κ1 κ2 κ3 : Type*} [Finite ι]
    [Fintype κ1] [Fintype κ2] [Fintype κ3] (t : ℕ) (B1 : Matrix ι κ1 ℝ) (B2 : Matrix ι κ2 ℝ)
    (B3 : Matrix ι κ3 ℝ) (b : ι → ℝ) {x1 : Ω → κ1 → ℝ} {x2 : Ω → κ2 → ℝ} {x3 : Ω → κ3 → ℝ}
    (h1 : ∀ i, Integrable (fun ω => x1 ω i) S.μ) (h2 : ∀ i, Integrable (fun ω => x2 ω i) S.μ)
    (h3 : ∀ i, Integrable (fun ω => x3 ω i) S.μ) :
    ∀ᵐ ω ∂S.μ, EVm S t (fun ω => B1 *ᵥ x1 ω + B2 *ᵥ x2 ω + B3 *ᵥ x3 ω + b) ω =
      B1 *ᵥ EVm S t x1 ω + B2 *ᵥ EVm S t x2 ω + B3 *ᵥ EVm S t x3 ω + b := by
  have i1 := integrable_mulVec B1 h1
  have i2 := integrable_mulVec B2 h2
  have i3 := integrable_mulVec B3 h3
  have i12 : ∀ r, Integrable (fun ω => (B1 *ᵥ x1 ω + B2 *ᵥ x2 ω) r) S.μ := fun r =>
    (i1 r).add (i2 r)
  have i123 : ∀ r, Integrable (fun ω => (B1 *ᵥ x1 ω + B2 *ᵥ x2 ω + B3 *ᵥ x3 ω) r) S.μ :=
    fun r => (i12 r).add (i3 r)
  filter_upwards [EVm_add S t (x' := fun _ => b) i123 (fun i => integrable_const (b i)),
    EVm_add S t i12 i3,
    EVm_add S t i1 i2, EVm_mulVec S t B1 h1, EVm_mulVec S t B2 h2, EVm_mulVec S t B3 h3]
    with ω e1 e2 e3 e4 e5 e6
  rw [e1, e2, e3, e4, e5, e6, EVm_const]

/-! ### The exogenous VAR(1) state -/

/-- Woodford (2003), p. 537 ("`s_t` includes all of the exogenous states that contain information
about the possible future evolution"): a bounded adapted exogenous state with the time-invariant
conditional law of motion `E_t s_{t+1} = A s_t` a.s. (a VAR(1) with martingale-difference
innovations). -/
def IsVAR (S : MeasExpectationSystem Ω) (A : Matrix ιs ιs ℝ) (s : ℕ → Ω → ιs → ℝ) : Prop :=
  MBoundedV S s ∧ MAdaptedV S s ∧ ∀ t, ∀ᵐ ω ∂S.μ, EVm S t (s (t + 1)) ω = A *ᵥ s t ω

omit [Fintype ιs] [DecidableEq ιs] in
/-- Woodford (2003), fn 6, p. 539 (tool): the components of a bounded adapted process are
integrable. -/
theorem integrable_of_adapted {S : MeasExpectationSystem Ω} {ι : Type*} {x : ℕ → Ω → ι → ℝ}
    (hb : MBoundedV S x) (ha : MAdaptedV S x) (t : ℕ) (i : ι) :
    Integrable (fun ω => x t ω i) S.μ := by
  obtain ⟨K, hK⟩ := hb
  exact integrable_of_bound ((ha t i).mono (S.𝓕.le t)).aestronglyMeasurable
    ((hK t).mono fun ω h => h i)

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 537: **VAR forecasts**, `E_t s_{t+k} = Aᵏ s_t` a.s. -/
theorem var_forecast {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    (t k : ℕ) : ∀ᵐ ω ∂S.μ, EVm S t (s (t + k)) ω = A ^ k *ᵥ s t ω := by
  obtain ⟨hb, ha, hvar⟩ := hs
  have hi := integrable_of_adapted hb ha
  induction k with
  | zero =>
    refine Eventually.of_forall fun ω => ?_
    rw [Nat.add_zero, EVm_of_known S (ha t) (hi t), pow_zero, one_mulVec]
  | succ k ih =>
    filter_upwards [EVm_tower S (Nat.le_add_right t k) (s (t + k + 1)),
      EVm_congr S t (hvar (t + k)), EVm_mulVec S t A (hi (t + k)), ih] with ω e1 e2 e3 e4
    change EVm S t (s (t + k + 1)) ω = _
    rw [← e1, e2, e3, e4, mulVec_mulVec, ← pow_succ']

omit [Fintype ιτ] in
/-- Woodford (2003), eq. (1.1) and p. 540 (tool): in a feasible plan the constraints hold in the
abstract form `Ĩ E_t y_{t+1} = Ã y_t + c_t` (a.s.), the predetermined rows because `Z_{t+1}` is
known at `t`. -/
theorem m_constraints {S : MeasExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y)
    {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ EVm S t (y (t + 1)) ω = P.sys.Atil *ᵥ y t ω + liftDist c t ω := by
  obtain ⟨hst, -, hyb, hya⟩ := hy
  obtain ⟨hZ, hz⟩ := hst t ht
  have hi := integrable_of_adapted hyb hya
  set g : Ω → ιZ → ℝ := fun ω => P.sys.A11 *ᵥ Zpart (y t ω) + P.sys.A12 *ᵥ zpart (y t ω)
    with hg
  have hgk : MKnownV S t g := fun j =>
    sm_comp (hya t) (g := fun v => (P.sys.A11 *ᵥ Zpart v + P.sys.A12 *ᵥ zpart v) j)
      (by unfold Zpart zpart; fun_prop)
  have hgi : ∀ j, Integrable (fun ω => g ω j) S.μ := fun j =>
    (hi (t + 1) (Sum.inl (Sum.inl j))).congr (hZ.mono fun ω e => congrFun e j)
  have hgE : EVm S t g = g := EVm_of_known S hgk hgi
  filter_upwards [EVm_congr S t (x := fun ω => Zpart (y (t + 1) ω)) hZ, hz] with ω e1 e2
  funext i
  rcases i with j | r
  · rw [P.sys.Itil_mulVec, P.sys.Atil_mulVec]
    have h1 : Zpart (EVm S t (y (t + 1)) ω) = EVm S t (fun ω => Zpart (y (t + 1) ω)) ω := rfl
    have h2 : EVm S t (fun ω => Zpart (y (t + 1) ω)) ω = g ω := by
      rw [e1]
      exact congrFun hgE ω
    simp only [Sum.elim_inl, h1, h2, liftDist, Pi.add_apply, Pi.zero_apply, add_zero, hg]
  · rw [P.sys.Itil_mulVec, P.sys.Atil_mulVec]
    have h1 : zpart (EVm S t (y (t + 1)) ω) = EVm S t (fun ω => zpart (y (t + 1) ω)) ω := rfl
    simp only [Sum.elim_inr, h1, e2, liftDist, Pi.add_apply]

omit [MeasurableSpace Ω] [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz] [DecidableEq ιs] in
/-- Woodford (2003), p. 537 (tool): the disturbance `C s_t = [0; C₂ s_t]` as a matrix. -/
theorem liftDist_eq (s : ℕ → Ω → ιs → ℝ) (t : ℕ) (ω : Ω) :
    liftDist (ιZ := ιZ) (fun t ω => C2 *ᵥ s t ω) t ω = Matrix.fromRows 0 C2 *ᵥ s t ω := by
  rw [fromRows_mulVec, zero_mulVec]
  rfl

/-- Woodford (2003), eq. (1.9), p. 541 (tool): the left side of (1.9) as an affine function of
`(E_t φ_{t+1}, y_t, φ_t)`. -/
theorem foc_affine (p : ιZ ⊕ ιz → ℝ) (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) (q : ιZ ⊕ ιz → ℝ) :
    P.sys.Atilᵀ *ᵥ p + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ q) =
      P.sys.Atilᵀ *ᵥ p + (P.Tᵀ * P.W * P.T) *ᵥ v + (-(P.β⁻¹ • P.sys.Itilᵀ)) *ᵥ q +
        -(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) := by
  rw [mulVec_sub, mulVec_sub, ← mulVec_mulVec, ← mulVec_mulVec, neg_mulVec, smul_mulVec]
  abel

/-- Woodford (2003), p. 540: the state vector `X_t = (Z_t, M_{t−1}, s_t)` of a plan with
multipliers and exogenous state. -/
def stateX (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ)
    (s : ℕ → Ω → ιs → ℝ) (t : ℕ) (ω : Ω) : (ιZ ⊕ ιz) ⊕ ιs → ℝ :=
  mkX (Sum.elim (Zpart (y t ω)) (Mpart (φ t ω))) (s t ω)

/-! ### Conditional forecasts are the perfect-foresight path -/

/-- Woodford (2003), pp. 538–541: **the conditional forecast path of a solution is a
perfect-foresight solution.** If `(y, φ)` is a bounded solution of (1.1) + (1.9) on a probability
space with the VAR disturbance `c_t = C₂ s_t`, then for every `t ≥ t₀` and almost every `ω` the
deterministic paths `k ↦ E_t y_{t+k}(ω)`, `k ↦ E_t φ_{t+k}(ω)` solve (1.1) + (1.9) under perfect
foresight from the state `(Z_t(ω), M_{t−1}(ω))` with forcing `C₂ Aᵏ s_t(ω)` (linearity, the law
of iterated expectations, `E_t s_{t+k} = Aᵏ s_t`). -/
theorem forecast_focSystem {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ}
    (hs : IsVAR S A s) {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, FOCSystem P perfectForesight (cpf A C2 (s t ω)) 0 (fun _ => Zpart (y t ω))
      (fun _ => Mpart (φ t ω)) (fun k _ => EVm S t (y (t + k)) ω)
      (fun k _ => EVm S t (φ (t + k)) ω) := by
  have hy := h.1
  obtain ⟨⟨-, -, hyb, hya⟩, hφb, hφm, hMm, hM0e, hfoc⟩ := h
  have hsb := hs.1
  have hsa := hs.2.1
  have hyi := integrable_of_adapted hyb hya
  have hsi := integrable_of_adapted hsb hsa
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨Kφ, hKφ⟩ := hφb
  have hφi : ∀ t i, Integrable (fun ω => φ t ω i) S.μ := fun t i =>
    integrable_of_bound (hφm t i) ((hKφ t).mono fun ω h => h i)
  have hEyi : ∀ s' t' i, Integrable (fun ω => EVm S s' (y t') ω i) S.μ := fun _ _ _ =>
    S.integrable_E _ _
  have hEφi : ∀ s' t' i, Integrable (fun ω => EVm S s' (φ t') ω i) S.μ := fun _ _ _ =>
    S.integrable_E _ _
  -- (1.1) in abstract form along the forecasts
  have hcons : ∀ k, ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ EVm S t (y (t + k + 1)) ω =
      P.sys.Atil *ᵥ EVm S t (y (t + k)) ω + Matrix.fromRows 0 C2 *ᵥ (A ^ k *ᵥ s t ω) := by
    intro k
    have hc := m_constraints P hy (le_trans ht (Nat.le_add_right t k))
    have hz : ∀ᵐ ω ∂S.μ, P.sys.Itil *ᵥ EVm S (t + k) (y (t + k + 1)) ω +
        (-P.sys.Atil) *ᵥ y (t + k) ω + (-Matrix.fromRows 0 C2) *ᵥ s (t + k) ω + 0 = 0 := by
      filter_upwards [hc] with ω e
      rw [e, liftDist_eq, neg_mulVec, neg_mulVec]
      abel
    filter_upwards [EVm_congr S t hz, EVm_affine3 S t P.sys.Itil (-P.sys.Atil)
      (-Matrix.fromRows 0 C2) 0 (hEyi (t + k) (t + k + 1)) (hyi (t + k)) (hsi (t + k)),
      EVm_tower S (Nat.le_add_right t k) (y (t + k + 1)), var_forecast A hs t k]
      with ω e1 e2 e3 e4
    rw [EVm_const] at e1
    beta_reduce at e1
    have key := e2.symm.trans e1
    rw [e3, e4, neg_mulVec, neg_mulVec, add_zero] at key
    rw [← sub_eq_zero, ← key]
    abel
  -- (1.9) along the forecasts
  have hfocE : ∀ k, ∀ᵐ ω ∂S.μ, P.sys.Atilᵀ *ᵥ EVm S t (φ (t + k + 1)) ω +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + k)) ω - P.τstar)) -
        P.β⁻¹ • (P.sys.Itilᵀ *ᵥ EVm S t (φ (t + k)) ω) = 0 := by
    intro k
    have hz : ∀ᵐ ω ∂S.μ, P.sys.Atilᵀ *ᵥ EVm S (t + k) (φ (t + k + 1)) ω +
        (P.Tᵀ * P.W * P.T) *ᵥ y (t + k) ω + (-(P.β⁻¹ • P.sys.Itilᵀ)) *ᵥ φ (t + k) ω +
          -(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) = 0 := by
      filter_upwards [hfoc (t + k) (le_trans ht (Nat.le_add_right t k))] with ω e
      rw [← foc_affine]
      exact e
    filter_upwards [EVm_congr S t hz, EVm_affine3 S t P.sys.Atilᵀ (P.Tᵀ * P.W * P.T)
      (-(P.β⁻¹ • P.sys.Itilᵀ)) (-(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar))) (hEφi (t + k) (t + k + 1))
      (hyi (t + k)) (hφi (t + k)), EVm_tower S (Nat.le_add_right t k) (φ (t + k + 1))]
      with ω e1 e2 e3
    rw [EVm_const] at e1
    beta_reduce at e1
    have key := e2.symm.trans e1
    rw [e3, ← foc_affine] at key
    exact key
  -- initial conditions
  have hZi : EVm S t (y t) = y t := EVm_of_known S (hya t) (hyi t)
  have hMi : ∀ᵐ ω ∂S.μ, Mpart (EVm S t (φ t) ω) = Mpart (φ t ω) := by
    have hmeas : ∀ r, AEStronglyMeasurable[S.𝓕 t] (fun ω => φ t ω (Sum.inr r)) S.μ := by
      intro r
      rcases Nat.eq_or_lt_of_le ht with h0 | h0
      · subst h0
        exact (hM0 r).congr (hM0e.mono fun ω e => (congrFun e r).symm)
      · have hm := hMm (t - 1) r
        rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at hm
        exact (hm.mono (S.𝓕.mono (Nat.sub_le t 1))).aestronglyMeasurable
    have hc : ∀ r, S.E t (fun ω => φ t ω (Sum.inr r)) =ᵐ[S.μ] fun ω => φ t ω (Sum.inr r) :=
      fun r => S.E_of_aestronglyMeasurable (hmeas r) (hφi t _)
    filter_upwards [ae_all_iff.2 hc] with ω e
    funext r
    exact e r
  -- bounds
  have hyB : ∀ᵐ ω ∂S.μ, ∀ k i, |EVm S t (y (t + k)) ω i| ≤ Ky :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun i => S.abs_E_le ((hKy (t + k)).mono fun ω h => h i) t
  have hφB : ∀ᵐ ω ∂S.μ, ∀ k i, |EVm S t (φ (t + k)) ω i| ≤ Kφ :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun i => S.abs_E_le ((hKφ (t + k)).mono fun ω h => h i) t
  filter_upwards [ae_all_iff.2 hcons, ae_all_iff.2 hfocE, hMi, hyB, hφB] with ω e1 e2 e3 e4 e5
  have hL : ∀ k, Matrix.fromRows (0 : Matrix ιZ ιs ℝ) C2 *ᵥ (A ^ k *ᵥ s t ω) =
      liftDist (ιZ := ιZ) (cpf A C2 (s t ω)) k () := by
    intro k
    rw [fromRows_mulVec, zero_mulVec]
    rfl
  refine ⟨⟨(structural_iff P.sys perfectForesight _ 0 _).mpr
    fun k _ u => ⟨fun r => ?_, fun r => ?_⟩, fun u => ?_, ⟨Ky, fun k u i => e4 k i⟩,
    fun _ _ => rfl⟩, ⟨Kφ, fun k u i => e5 k i⟩, fun _ _ => rfl, fun u => ?_, fun k _ u => ?_⟩
  · have := congrFun (e1 k) (Sum.inl r)
    rw [hL k] at this
    exact this
  · have := congrFun (e1 k) (Sum.inr r)
    rw [hL k] at this
    exact this
  · change Zpart (EVm S t (y t) ω) = Zpart (y t ω)
    rw [hZi]
  · exact e3
  · exact e2 k

/-- Woodford (2003), pp. 538–541: **the conditional forecasts of any bounded solution are given by
the time-invariant perfect-foresight solution map of the current state**:
`E_t y_{t+k} = pfY(X_t)_k`, `E_t φ_{t+k} = pfΦ(X_t)_k` a.s., `X_t = (Z_t, M_{t−1}, s_t)`. -/
theorem forecast_eq {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, ∀ k, EVm S t (y (t + k)) ω = pfY P A C2 hA81 hA (stateX y φ s t ω) k () ∧
      EVm S t (φ (t + k)) ω = pfΦ P A C2 hA81 hA (stateX y φ s t ω) k () := by
  filter_upwards [forecast_focSystem P A C2 hs h hM0 ht] with ω hω k
  have := pf_unique P A C2 hA81 hA (stateX y φ s t ω) hω k
  exact ⟨congrFun this.1 (), congrFun this.2 ()⟩

/-- Woodford (2003), **Proposition 8.2 (the linear form (1.5))**, p. 555, for the whole plan: every
bounded solution of (1.1) + (1.9) satisfies `y_t = f⁰ + F X_t` a.s. at every `t ≥ t₀`, with the
time-invariant `f⁰ = fY`, `F = FY` (which depend only on the structural matrices, the loss and the
VAR matrix `A`, not on the probability space, the shock law, `t₀` or the initial conditions) and
the state `X_t = (Z_t, M_{t−1}, s_t)`. -/
theorem linear_form {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      y t ω = fY P A C2 hA81 hA + FY P A C2 hA81 hA *ᵥ stateX y φ s t ω := by
  intro t ht
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  filter_upwards [forecast_eq P A C2 hA81 hA hs h hM0 ht] with ω hω
  have h0 := (hω 0).1
  rw [Nat.add_zero, EVm_of_known S (h.1.2.2.2 t) (hyi t), fY_spec] at h0
  exact h0

omit [Fintype ιτ] in
/-- Woodford (2003), eqs. (1.18) and (1.9) (tool): `Ĩ' v` determines the `ξ`-block of `v`,
`(Ĩ' v)_Z = ξ`. -/
theorem Itil_transpose_inl (v : ιZ ⊕ ιz → ℝ) (j : ιZ) :
    (P.sys.Itilᵀ *ᵥ v) (Sum.inl (Sum.inl j)) = v (Sum.inl j) := by
  rw [Itil_transpose_mulVec, Sum.elim_inl, PencilSplit.Ihat_transpose_mulVec, Sum.elim_inl]
  rfl

/-- Woodford (2003), (1.17), p. 551: the multipliers of every bounded solution are also a
time-invariant affine function of the state, `φ_t = g⁰ + G X_t` a.s. (`ξ_t` from (1.9) at `t`,
`M_{t−1}` from the state itself). -/
theorem mult_form {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      φ t ω = fΦ P A C2 hA81 hA + FΦ P A C2 hA81 hA *ᵥ stateX y φ s t ω := by
  intro t ht
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  filter_upwards [forecast_eq P A C2 hA81 hA hs h hM0 ht, h.2.2.2.2.2 t ht] with ω hω hf
  set X := stateX y φ s t ω with hX
  obtain ⟨-, -, -, hM, hfoc⟩ := pf_spec P A C2 hA81 hA X
  have hp := hfoc 0 le_rfl ()
  have hy0 : pfY P A C2 hA81 hA X 0 () = y t ω := by
    rw [← (hω 0).1, Nat.add_zero, EVm_of_known S (h.1.2.2.2 t) (hyi t)]
  have hφ1 : pfΦ P A C2 hA81 hA X 1 () = EVm S t (φ (t + 1)) ω := (hω 1).2.symm
  change P.sys.Atilᵀ *ᵥ pfΦ P A C2 hA81 hA X (0 + 1) () + _ - _ = 0 at hp
  rw [Nat.zero_add, hφ1, hy0] at hp
  have hd : P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ t ω) = P.β⁻¹ • (P.sys.Itilᵀ *ᵥ pfΦ P A C2 hA81 hA X 0 ()) :=
    sub_right_inj.mp (hf.trans hp.symm)
  have hd' : P.sys.Itilᵀ *ᵥ φ t ω = P.sys.Itilᵀ *ᵥ pfΦ P A C2 hA81 hA X 0 () :=
    smul_right_injective _ (inv_ne_zero P.β_pos.ne') hd
  rw [← fΦ_spec]
  funext i
  rcases i with j | r
  · have := congrFun hd' (Sum.inl (Sum.inl j))
    rwa [Itil_transpose_inl, Itil_transpose_inl] at this
  · exact (congrFun (hM ()) r).symm

/-- Woodford (2003), p. 539: **the state evolves by a time-invariant affine law**: in every
bounded solution `(Z_{t+1}, M_t) = nextN(X_t) = h⁰ + H X_t` a.s. -/
theorem state_transition {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Sum.elim (Zpart (y (t + 1) ω)) (Mpart (φ (t + 1) ω)) =
      nextN P A C2 hA81 hA (stateX y φ s t ω) := by
  intro t ht
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  have hMk : ∀ r, S.E t (fun ω => φ (t + 1) ω (Sum.inr r)) = fun ω => φ (t + 1) ω (Sum.inr r) :=
    fun r => S.E_of_stronglyMeasurable (h.2.2.2.1 t r)
      (integrable_of_bound (h.2.2.1 (t + 1) _) ((hKφ (t + 1)).mono fun ω h => h _))
  filter_upwards [forecast_eq P A C2 hA81 hA hs h hM0 ht, (h.1.1 t ht).1] with ω hω hZ
  set X := stateX y φ s t ω with hX
  obtain ⟨⟨hst, -, -, -⟩, -⟩ := pf_spec P A C2 hA81 hA X
  have hy0 : pfY P A C2 hA81 hA X 0 () = y t ω := by
    rw [← (hω 0).1, Nat.add_zero, EVm_of_known S (h.1.2.2.2 t) (hyi t)]
  have hZ1 := (hst 0 le_rfl ()).1
  rw [hy0] at hZ1
  funext i
  rcases i with j | r
  · simp only [Sum.elim_inl, nextN]
    rw [hZ, ← hZ1]
  · simp only [Sum.elim_inr, nextN]
    rw [← (hω 1).2]
    exact (congrFun (hMk r) ω).symm

include hA81 hA in
/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541, **proved on every VAR economy from the
perfect-foresight Assumption 8.1**: two bounded solutions of (1.1) + (1.9) with the same data agree
a.s. at every date `t ≥ t₀` (the states agree by induction, `state_transition`, and the plans are
the same affine function of the state, `linear_form`, `mult_form`). -/
theorem m_focUnique_var {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ)
    {y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ φ' : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (h' : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y' φ') :
    ∀ t, t0 ≤ t → y t =ᵐ[S.μ] y' t ∧ φ t =ᵐ[S.μ] φ' t := by
  have hX : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, stateX y φ s t ω = stateX y' φ' s t ω := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      filter_upwards [h.1.2.1, h'.1.2.1, h.2.2.2.2.1, h'.2.2.2.2.1] with ω e1 e2 e3 e4
      simp only [stateX, e1, e2, e3, e4]
    | succ t ht ih =>
      filter_upwards [ih, state_transition P A C2 hA81 hA hs h hM0 t ht,
        state_transition P A C2 hA81 hA hs h' hM0 t ht] with ω e1 e2 e3
      simp only [stateX, mkX] at e1 e2 e3 ⊢
      rw [e2, e3, e1]
  intro t ht
  refine ⟨?_, ?_⟩
  · filter_upwards [hX t ht, linear_form P A C2 hA81 hA hs h hM0 t ht,
      linear_form P A C2 hA81 hA hs h' hM0 t ht] with ω e1 e2 e3
    rw [e2, e3, e1]
  · filter_upwards [hX t ht, mult_form P A C2 hA81 hA hs h hM0 t ht,
      mult_form P A C2 hA81 hA hs h' hM0 t ht] with ω e1 e2 e3
    rw [e2, e3, e1]

/-! ### Existence: the Markov solution -/

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), p. 539 (tool): `mkX` is continuous. -/
theorem continuous_mkX : Continuous (fun p : (ιZ ⊕ ιz → ℝ) × (ιs → ℝ) => mkX p.1 p.2) := by
  refine continuous_pi fun i => ?_
  rcases i with i | i
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply i).comp continuous_snd

omit [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] [DecidableEq ιs] in
/-- Woodford (2003), (1.5) (tool): a matrix acting on a state vector splits into its endogenous
and exogenous blocks. -/
theorem mulVec_mkX {ν : Type*} (F : Matrix ν ((ιZ ⊕ ιz) ⊕ ιs) ℝ) (n : ιZ ⊕ ιz → ℝ)
    (σ : ιs → ℝ) :
    F *ᵥ mkX n σ = F.submatrix id Sum.inl *ᵥ n + F.submatrix id Sum.inr *ᵥ σ := by
  funext i
  simp [mulVec, dotProduct, mkX, Fintype.sum_sum_type]

/-- Woodford (2003), p. 539: the matrix `H_n` of the endogenous block of the state transition,
`(Z_{t+1}, M_t) = h⁰ + H_n (Z_t, M_{t−1}) + H_s s_t`. -/
noncomputable def Hn : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ := (HN P A C2 hA81 hA).submatrix id Sum.inl

/-- Woodford (2003), p. 539: the matrix `H_s` of the exogenous block of the state transition. -/
noncomputable def Hs : Matrix (ιZ ⊕ ιz) ιs ℝ := (HN P A C2 hA81 hA).submatrix id Sum.inr

/-- Woodford (2003), p. 539: `H_n` is intrinsic — its `j`-th column is the response of the
perfect-foresight next state `(Z_1, M_0)` to a unit change in the `j`-th component of the
current endogenous state (with `s = 0`). -/
theorem Hn_apply (i j : ιZ ⊕ ιz) :
    Hn P A C2 hA81 hA i j = nextN P A C2 hA81 hA (mkX (Pi.single j 1) 0) i -
      nextN P A C2 hA81 hA (mkX 0 0) i := by
  rw [hN_spec, hN_spec, mulVec_mkX, mulVec_mkX]
  simp [Hn]

/-- Woodford (2003), p. 539: the endogenous state transition in block form. -/
theorem nextN_mkX (n : ιZ ⊕ ιz → ℝ) (σ : ιs → ℝ) :
    nextN P A C2 hA81 hA (mkX n σ) =
      Hn P A C2 hA81 hA *ᵥ n + (hN P A C2 hA81 hA + Hs P A C2 hA81 hA *ᵥ σ) := by
  rw [hN_spec, mulVec_mkX]
  simp only [Hn, Hs]
  abel

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), App. G.1, (G.5) (tool): a recursion `m_{k+1} = G m_k + b_k` with
geometrically decaying powers of `G` and bounded forcing stays bounded, with a bound that
depends only on the bounds of `m_0` and `b`. -/
theorem bounded_rec {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℝ}
    (hG : PencilSplit.PowDecay G) (K0 Kb : ℝ) :
    ∃ K, ∀ (m b : ℕ → ι → ℝ), (∀ i, |m 0 i| ≤ K0) → (∀ k i, |b k i| ≤ Kb) →
      (∀ k, m (k + 1) = G *ᵥ m k + b k) → ∀ k i, |m k i| ≤ K := by
  obtain ⟨C, r, hr0, hr1, hC⟩ := hG
  refine ⟨Fintype.card ι * (|C| * |K0|) + Fintype.card ι * (|C| * |Kb|) * (1 - r)⁻¹,
    fun m b hm0 hb hrec k i => ?_⟩
  have hit := Prop82General.KrylovBound.iterate_rec (Λ := G) (m := m) (q := fun j => b (j - 1))
    (t := 0) (n := k) (fun j hj _ => by
      obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [show 0 + (1 + j') - 1 = j' by omega, show 0 + (1 + j') = j' + 1 by omega]
      exact hrec j')
  rw [zero_add] at hit
  rw [hit, Pi.add_apply, Finset.sum_apply]
  have hrk : ∀ n, r ^ n ≤ 1 := fun n => pow_le_one₀ hr0 hr1.le
  have h1 : |(G ^ k *ᵥ m 0) i| ≤ Fintype.card ι * (|C| * |K0|) := by
    refine (PencilSplit.abs_mulVec_pow_le hC k (M := |K0|)
      (fun j => (hm0 j).trans (le_abs_self _)) i).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc C * r ^ k * |K0| ≤ |C| * 1 * |K0| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hr0 k)).trans
            (mul_le_mul_of_nonneg_left (hrk k) (abs_nonneg C))
      _ = |C| * |K0| := by ring
  have h2 : |∑ j ∈ Finset.range k, (G ^ (k - 1 - j) *ᵥ b (0 + 1 + j - 1)) i| ≤
      Fintype.card ι * (|C| * |Kb|) * (1 - r)⁻¹ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range k, |(G ^ (k - 1 - j) *ᵥ b (0 + 1 + j - 1)) i| ≤
        Fintype.card ι * (|C| * |Kb|) * r ^ (k - 1 - j) := by
      intro j _
      refine (PencilSplit.abs_mulVec_pow_le hC (k - 1 - j) (M := |Kb|)
        (fun l => (hb _ l).trans (le_abs_self _)) i).trans ?_
      have hc : C * r ^ (k - 1 - j) * |Kb| ≤ |C| * |Kb| * r ^ (k - 1 - j) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C)
          (pow_nonneg hr0 (k - 1 - j))) (abs_nonneg Kb)
        linarith [this, show |C| * r ^ (k - 1 - j) * |Kb| = |C| * |Kb| * r ^ (k - 1 - j) by ring]
      calc _ ≤ (Fintype.card ι : ℝ) * (|C| * |Kb| * r ^ (k - 1 - j)) :=
            mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hrefl : ∑ j ∈ Finset.range k, r ^ (k - 1 - j) = ∑ j ∈ Finset.range k, r ^ j :=
      Finset.sum_range_reflect (fun j => r ^ j) k
    rw [← Finset.mul_sum, hrefl]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun j _ => pow_nonneg hr0 j
  linarith [abs_add_le ((G ^ k *ᵥ m 0) i)
    (∑ j ∈ Finset.range k, (G ^ (k - 1 - j) *ᵥ b (0 + 1 + j - 1)) i)]

/-- Woodford (2003), p. 539: the endogenous state `(Z_t, M_{t−1})` of the Markov solution, `k`
periods after `t₀`, generated from `(Z_{t₀}, M_{t₀−1})` by the time-invariant transition
`nextN`. -/
noncomputable def candN (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (s : ℕ → Ω → ιs → ℝ) (t0 : ℕ) :
    ℕ → Ω → ιZ ⊕ ιz → ℝ
  | 0 => fun ω => Sum.elim (Z0 ω) (M0 ω)
  | k + 1 => fun ω => nextN P A C2 hA81 hA (mkX (candN Z0 M0 s t0 k ω) (s (t0 + k) ω))

/-- Woodford (2003), p. 539: the state `X_t = (Z_t, M_{t−1}, s_t)` of the Markov solution. -/
noncomputable def candX (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (s : ℕ → Ω → ιs → ℝ) (t0 t : ℕ)
    (ω : Ω) : (ιZ ⊕ ιz) ⊕ ιs → ℝ :=
  mkX (candN P A C2 hA81 hA Z0 M0 s t0 (t - t0) ω) (s t ω)

/-- Woodford (2003), (1.5): the plan of the Markov solution, `y_t = f⁰ + F X_t` for `t ≥ t₀`. -/
noncomputable def candY (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (s : ℕ → Ω → ιs → ℝ) (t0 : ℕ) :
    ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ :=
  fun t ω => if t0 ≤ t then fY P A C2 hA81 hA + FY P A C2 hA81 hA *ᵥ
    candX P A C2 hA81 hA Z0 M0 s t0 t ω else 0

/-- Woodford (2003), (1.17): the multipliers of the Markov solution, `φ_t = g⁰ + G X_t` for
`t ≥ t₀`. -/
noncomputable def candΦ (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (s : ℕ → Ω → ιs → ℝ) (t0 : ℕ) :
    ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun t ω => if t0 ≤ t then fΦ P A C2 hA81 hA + FΦ P A C2 hA81 hA *ᵥ
    candX P A C2 hA81 hA Z0 M0 s t0 t ω else 0

omit [MeasurableSpace Ω] in
/-- Woodford (2003), p. 539: one step of the Markov solution's state. -/
theorem candX_succ (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (s : ℕ → Ω → ιs → ℝ) {t0 t : ℕ}
    (ht : t0 ≤ t) (ω : Ω) :
    candX P A C2 hA81 hA Z0 M0 s t0 (t + 1) ω =
      mkX (nextN P A C2 hA81 hA (candX P A C2 hA81 hA Z0 M0 s t0 t ω)) (s (t + 1) ω) := by
  unfold candX
  rw [show t + 1 - t0 = (t - t0) + 1 by omega]
  simp only [candN]
  rw [show t0 + (t - t0) = t by omega]

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (1.5): the Markov plan is the perfect-foresight plan of the current state. -/
theorem candY_eq (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (s : ℕ → Ω → ιs → ℝ) {t0 t : ℕ}
    (ht : t0 ≤ t) (ω : Ω) :
    candY P A C2 hA81 hA Z0 M0 s t0 t ω =
      pfY P A C2 hA81 hA (candX P A C2 hA81 hA Z0 M0 s t0 t ω) 0 () := by
  simp only [candY, ht, ↓reduceIte]
  rw [fY_spec]

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (1.17): the Markov multipliers are the perfect-foresight multipliers of the
current state. -/
theorem candΦ_eq (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) (s : ℕ → Ω → ιs → ℝ) {t0 t : ℕ}
    (ht : t0 ≤ t) (ω : Ω) :
    candΦ P A C2 hA81 hA Z0 M0 s t0 t ω =
      pfΦ P A C2 hA81 hA (candX P A C2 hA81 hA Z0 M0 s t0 t ω) 0 () := by
  simp only [candΦ, ht, ↓reduceIte]
  rw [fΦ_spec]

omit [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] [DecidableEq ιs] in
/-- Woodford (2003), p. 540 (tool): `E_t` of an affine function of the state when the endogenous
block is known at `t`: `E_t (f⁰ + F (n, σ)) = f⁰ + F (n, E_t σ)` a.s. -/
theorem EVm_state (S : MeasExpectationSystem Ω) {ν : Type*} [Finite ν] (t : ℕ) (f0 : ν → ℝ)
    (F : Matrix ν ((ιZ ⊕ ιz) ⊕ ιs) ℝ) {n : Ω → ιZ ⊕ ιz → ℝ} {σ : Ω → ιs → ℝ}
    (hnk : MKnownV S t n) (hni : ∀ i, Integrable (fun ω => n ω i) S.μ)
    (hσi : ∀ i, Integrable (fun ω => σ ω i) S.μ) :
    ∀ᵐ ω ∂S.μ, EVm S t (fun ω => f0 + F *ᵥ mkX (n ω) (σ ω)) ω =
      f0 + F *ᵥ mkX (n ω) (EVm S t σ ω) := by
  have hf : (fun ω => f0 + F *ᵥ mkX (n ω) (σ ω)) = fun ω => F.submatrix id Sum.inl *ᵥ n ω +
      F.submatrix id Sum.inr *ᵥ σ ω + (0 : Matrix ν (ιZ ⊕ ιz) ℝ) *ᵥ n ω + f0 := by
    funext ω
    rw [mulVec_mkX, zero_mulVec]
    abel
  rw [hf]
  filter_upwards [EVm_affine3 S t (F.submatrix id Sum.inl) (F.submatrix id Sum.inr)
    (0 : Matrix ν (ιZ ⊕ ιz) ℝ) f0 hni hσi hni] with ω e
  rw [e, EVm_of_known S hnk hni, mulVec_mkX, zero_mulVec]
  abel

/-- Woodford (2003), p. 540: the endogenous state of the Markov solution is known at
`t₀ + k`. -/
theorem candN_known {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hsa : MAdaptedV S s)
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} (hZk : MKnownV S t0 Z0)
    (hMk : MKnownV S (t0 - 1) M0) :
    ∀ k, MKnownV S (t0 + k) (candN P A C2 hA81 hA Z0 M0 s t0 k) := by
  intro k
  induction k with
  | zero =>
    intro i
    rcases i with j | r
    · exact hZk j
    · exact (hMk r).mono (S.𝓕.mono (Nat.sub_le t0 1))
  | succ k ih =>
    intro i
    have hm : StronglyMeasurable[S.𝓕 (t0 + k)] (fun ω => (hN P A C2 hA81 hA +
        HN P A C2 hA81 hA *ᵥ mkX (candN P A C2 hA81 hA Z0 M0 s t0 k ω) (s (t0 + k) ω)) i) :=
      sm_comp₂ (g := fun p => (hN P A C2 hA81 hA + HN P A C2 hA81 hA *ᵥ mkX p.1 p.2) i) ih
        (hsa (t0 + k)) ((continuous_apply i).comp (continuous_const.add
          (continuous_const.matrix_mulVec continuous_mkX)))
    have heq : (fun ω => candN P A C2 hA81 hA Z0 M0 s t0 (k + 1) ω i) = fun ω =>
        (hN P A C2 hA81 hA + HN P A C2 hA81 hA *ᵥ
          mkX (candN P A C2 hA81 hA Z0 M0 s t0 k ω) (s (t0 + k) ω)) i := by
      funext ω
      simp only [candN]
      rw [hN_spec]
    rw [heq]
    exact hm.mono (S.𝓕.mono (Nat.le_succ _))

/-- Woodford (2003), Assumption 8.1 (existence), p. 541, **proved on every VAR economy** from the
perfect-foresight Assumption 8.1 and geometric stability of the endogenous state transition
`H_n` (`Hn_apply`): for every bounded `Z_{t₀}` known at `t₀` and bounded `M_{t₀−1}` known at
`t₀ − 1`, the Markov plan `y_t = f⁰ + F X_t`, `φ_t = g⁰ + G X_t`, with the state generated by
`(Z_{t+1}, M_t) = h⁰ + H X_t`, is a bounded solution of (1.1) + (1.9) with genuine conditional
expectations. -/
theorem m_focSolvable_var (hstab : PencilSplit.PowDecay (Hn P A C2 hA81 hA))
    {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s) {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0)
    (hMb : MBoundedRV S M0) (hMk : MKnownV S (t0 - 1) M0) :
    MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 (candY P A C2 hA81 hA Z0 M0 s t0)
      (candΦ P A C2 hA81 hA Z0 M0 s t0) := by
  obtain ⟨hsb, hsa, hvar⟩ := hs
  have hsi := integrable_of_adapted hsb hsa
  have hNk := candN_known P A C2 hA81 hA hsa hZk hMk
  set X := candX P A C2 hA81 hA Z0 M0 s t0 with hX
  -- the state is known
  have hXk : ∀ t, t0 ≤ t → MKnownV S t (X t) := by
    intro t ht i
    rcases i with i | i
    · have := hNk (t - t0) i
      rw [show t0 + (t - t0) = t by omega] at this
      exact this
    · exact hsa t i
  -- bounds
  obtain ⟨Ks, hKs⟩ := hsb
  obtain ⟨KZ, hKZ⟩ := hZb
  obtain ⟨KM, hKM⟩ := hMb
  obtain ⟨KHs, hKHs⟩ := exists_bound_mulVec (Hs P A C2 hA81 hA) Ks
  obtain ⟨Kn, hKn⟩ := bounded_rec hstab (max KZ KM) (∑ i, |hN P A C2 hA81 hA i| + KHs)
  have hNb : ∀ᵐ ω ∂S.μ, ∀ k i, |candN P A C2 hA81 hA Z0 M0 s t0 k ω i| ≤ Kn := by
    filter_upwards [hKZ, hKM, ae_all_iff.2 hKs] with ω h1 h2 h3
    refine hKn (fun k => candN P A C2 hA81 hA Z0 M0 s t0 k ω)
      (fun k => hN P A C2 hA81 hA + Hs P A C2 hA81 hA *ᵥ s (t0 + k) ω) ?_ ?_ ?_
    · intro i
      rcases i with j | r
      · exact (h1 j).trans (le_max_left _ _)
      · exact (h2 r).trans (le_max_right _ _)
    · intro k i
      refine (abs_add_le _ _).trans (add_le_add ?_ (hKHs _ (h3 (t0 + k)) i))
      exact Finset.single_le_sum (f := fun i => |hN P A C2 hA81 hA i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    · intro k
      exact nextN_mkX P A C2 hA81 hA _ _
  have hXb : ∀ᵐ ω ∂S.μ, ∀ t i, |X t ω i| ≤ max Kn Ks := by
    filter_upwards [hNb, ae_all_iff.2 hKs] with ω h1 h2 t i
    rcases i with i | i
    · exact (h1 _ i).trans (le_max_left _ _)
    · exact (h2 t i).trans (le_max_right _ _)
  -- the next endogenous state
  set n : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun t ω => nextN P A C2 hA81 hA (X t ω) with hn
  have hnk : ∀ t, t0 ≤ t → MKnownV S t (n t) := by
    intro t ht i
    have : (fun ω => n t ω i) =
        fun ω => (hN P A C2 hA81 hA + HN P A C2 hA81 hA *ᵥ X t ω) i := by
      funext ω
      simp only [hn]
      rw [hN_spec]
    rw [this]
    exact sm_comp (hXk t ht) (g := fun v => (hN P A C2 hA81 hA + HN P A C2 hA81 hA *ᵥ v) i)
      (by fun_prop)
  obtain ⟨KHN, hKHN⟩ := exists_bound_mulVec (HN P A C2 hA81 hA) (max Kn Ks)
  have hni : ∀ t, t0 ≤ t → ∀ i, Integrable (fun ω => n t ω i) S.μ := by
    intro t ht i
    refine integrable_of_bound (((hnk t ht) i).mono (S.𝓕.le t)).aestronglyMeasurable
      (K := ∑ i, |hN P A C2 hA81 hA i| + KHN) ?_
    filter_upwards [hXb] with ω h
    simp only [hn]
    rw [hN_spec, Pi.add_apply]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hKHN _ (h t) i))
    exact Finset.single_le_sum (f := fun i => |hN P A C2 hA81 hA i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  -- conditional expectations of next period's plan and multipliers
  have hshift : ∀ t ω, mkX (n t ω) (A *ᵥ s t ω) =
      nextX P A C2 hA81 hA (X t ω) := fun _ _ => rfl
  have hEY : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, EVm S t (candY P A C2 hA81 hA Z0 M0 s t0 (t + 1)) ω =
      pfY P A C2 hA81 hA (X t ω) 1 () := by
    intro t ht
    have hfun : candY P A C2 hA81 hA Z0 M0 s t0 (t + 1) = fun ω =>
        fY P A C2 hA81 hA + FY P A C2 hA81 hA *ᵥ mkX (n t ω) (s (t + 1) ω) := by
      funext ω
      simp only [candY, show t0 ≤ t + 1 by omega, ↓reduceIte, hn]
      rw [candX_succ P A C2 hA81 hA Z0 M0 s ht]
    rw [hfun]
    filter_upwards [EVm_state S t (fY P A C2 hA81 hA) (FY P A C2 hA81 hA) (hnk t ht) (hni t ht)
      (hsi (t + 1)), hvar t] with ω e1 e2
    rw [e1, e2, ← fY_spec, hshift, ← (pf_shift P A C2 hA81 hA (X t ω) 0).1]
  have hEΦ : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, EVm S t (candΦ P A C2 hA81 hA Z0 M0 s t0 (t + 1)) ω =
      pfΦ P A C2 hA81 hA (X t ω) 1 () := by
    intro t ht
    have hfun : candΦ P A C2 hA81 hA Z0 M0 s t0 (t + 1) = fun ω =>
        fΦ P A C2 hA81 hA + FΦ P A C2 hA81 hA *ᵥ mkX (n t ω) (s (t + 1) ω) := by
      funext ω
      simp only [candΦ, show t0 ≤ t + 1 by omega, ↓reduceIte, hn]
      rw [candX_succ P A C2 hA81 hA Z0 M0 s ht]
    rw [hfun]
    filter_upwards [EVm_state S t (fΦ P A C2 hA81 hA) (FΦ P A C2 hA81 hA) (hnk t ht) (hni t ht)
      (hsi (t + 1)), hvar t] with ω e1 e2
    rw [e1, e2, ← fΦ_spec, hshift, ← (pf_shift P A C2 hA81 hA (X t ω) 0).2]
  -- boundedness and adaptedness of the plan and the multipliers
  obtain ⟨KY, hKY⟩ := exists_bound_mulVec (FY P A C2 hA81 hA) (max Kn Ks)
  obtain ⟨KΦ, hKΦ⟩ := exists_bound_mulVec (FΦ P A C2 hA81 hA) (max Kn Ks)
  have hYb : MBoundedV S (candY P A C2 hA81 hA Z0 M0 s t0) := by
    refine ⟨max (∑ i, |fY P A C2 hA81 hA i| + KY) 0, fun t => ?_⟩
    filter_upwards [hXb] with ω h i
    by_cases ht : t0 ≤ t
    · simp only [candY, ht, ↓reduceIte, Pi.add_apply]
      refine ((abs_add_le _ _).trans (add_le_add ?_ (hKY _ (h t) i))).trans (le_max_left _ _)
      exact Finset.single_le_sum (f := fun i => |fY P A C2 hA81 hA i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    · simp only [candY, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact le_max_right _ _
  have hΦb : MBoundedV S (candΦ P A C2 hA81 hA Z0 M0 s t0) := by
    refine ⟨max (∑ i, |fΦ P A C2 hA81 hA i| + KΦ) 0, fun t => ?_⟩
    filter_upwards [hXb] with ω h i
    by_cases ht : t0 ≤ t
    · simp only [candΦ, ht, ↓reduceIte, Pi.add_apply]
      refine ((abs_add_le _ _).trans (add_le_add ?_ (hKΦ _ (h t) i))).trans (le_max_left _ _)
      exact Finset.single_le_sum (f := fun i => |fΦ P A C2 hA81 hA i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    · simp only [candΦ, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact le_max_right _ _
  have hYk : MAdaptedV S (candY P A C2 hA81 hA Z0 M0 s t0) := by
    intro t i
    by_cases ht : t0 ≤ t
    · have : (fun ω => candY P A C2 hA81 hA Z0 M0 s t0 t ω i) =
          fun ω => (fY P A C2 hA81 hA + FY P A C2 hA81 hA *ᵥ X t ω) i := by
        funext ω
        simp only [candY, ht, ↓reduceIte, hX]
      rw [this]
      exact sm_comp (hXk t ht) (g := fun v => (fY P A C2 hA81 hA + FY P A C2 hA81 hA *ᵥ v) i)
        (by fun_prop)
    · have : (fun ω => candY P A C2 hA81 hA Z0 M0 s t0 t ω i) = fun _ => 0 := by
        funext ω
        simp only [candY, ht, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact stronglyMeasurable_const
  have hΦk : MAdaptedV S (candΦ P A C2 hA81 hA Z0 M0 s t0) := by
    intro t i
    by_cases ht : t0 ≤ t
    · have : (fun ω => candΦ P A C2 hA81 hA Z0 M0 s t0 t ω i) =
          fun ω => (fΦ P A C2 hA81 hA + FΦ P A C2 hA81 hA *ᵥ X t ω) i := by
        funext ω
        simp only [candΦ, ht, ↓reduceIte, hX]
      rw [this]
      exact sm_comp (hXk t ht) (g := fun v => (fΦ P A C2 hA81 hA + FΦ P A C2 hA81 hA *ᵥ v) i)
        (by fun_prop)
    · have : (fun ω => candΦ P A C2 hA81 hA Z0 M0 s t0 t ω i) = fun _ => 0 := by
        funext ω
        simp only [candΦ, ht, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact stronglyMeasurable_const
  -- the lagged multipliers of the Markov solution
  have hMpart : ∀ t, t0 ≤ t → ∀ ω,
      Mpart (candΦ P A C2 hA81 hA Z0 M0 s t0 t ω) = Xm (X t ω) := by
    intro t ht ω
    rw [candΦ_eq P A C2 hA81 hA Z0 M0 s ht]
    exact (pf_spec P A C2 hA81 hA (X t ω)).2.2.2.1 ()
  have hZpart : ∀ t, t0 ≤ t → ∀ ω,
      Zpart (candY P A C2 hA81 hA Z0 M0 s t0 t ω) = Xz (X t ω) := by
    intro t ht ω
    rw [candY_eq P A C2 hA81 hA Z0 M0 s ht]
    exact (pf_spec P A C2 hA81 hA (X t ω)).1.2.1 ()
  refine ⟨⟨fun t ht => ⟨Eventually.of_forall fun ω => ?_, ?_⟩, Eventually.of_forall fun ω => ?_,
    hYb, hYk⟩, hΦb, fun t i => ((hΦk t i).mono (S.𝓕.le t)).aestronglyMeasurable,
    fun t r => ?_, Eventually.of_forall fun ω => ?_, fun t ht => ?_⟩
  · -- predetermined rows
    obtain ⟨⟨hst, -, -, -⟩, -⟩ := pf_spec P A C2 hA81 hA (X t ω)
    have hx : X (t + 1) ω = mkX (nextN P A C2 hA81 hA (X t ω)) (s (t + 1) ω) :=
      candX_succ P A C2 hA81 hA Z0 M0 s ht ω
    rw [hZpart (t + 1) (by omega), candY_eq P A C2 hA81 hA Z0 M0 s ht, hx]
    exact (hst 0 le_rfl ()).1
  · -- expectational rows
    filter_upwards [hEY t ht] with ω e
    obtain ⟨⟨hst, -, -, -⟩, -⟩ := pf_spec P A C2 hA81 hA (X t ω)
    have h2 := (hst 0 le_rfl ()).2
    have hz : EVm S t (fun ω' => zpart (candY P A C2 hA81 hA Z0 M0 s t0 (t + 1) ω')) ω =
        zpart (pfY P A C2 hA81 hA (X t ω) 1 ()) := by
      change zpart (EVm S t (candY P A C2 hA81 hA Z0 M0 s t0 (t + 1)) ω) = _
      rw [e]
    rw [hz, candY_eq P A C2 hA81 hA Z0 M0 s ht]
    change P.sys.Et *ᵥ zpart (pfY P A C2 hA81 hA (X t ω) 1 ()) = _ at h2
    rw [h2]
    simp only [cpf, pow_zero, one_mulVec]
    rfl
  · rw [hZpart t0 le_rfl ω]
    simp only [hX, candX, Nat.sub_self]
    rfl
  · -- `M_t` is known at `t`
    by_cases ht : t0 ≤ t
    · have : (fun ω => candΦ P A C2 hA81 hA Z0 M0 s t0 (t + 1) ω (Sum.inr r)) =
          fun ω => n t ω (Sum.inr r) := by
        funext ω
        have := congrFun (hMpart (t + 1) (by omega) ω) r
        have hx : X (t + 1) ω = mkX (nextN P A C2 hA81 hA (X t ω)) (s (t + 1) ω) :=
          candX_succ P A C2 hA81 hA Z0 M0 s ht ω
        rw [hx] at this
        exact this
      rw [this]
      exact hnk t ht _
    · by_cases ht' : t + 1 = t0
      · have : (fun ω => candΦ P A C2 hA81 hA Z0 M0 s t0 (t + 1) ω (Sum.inr r)) =
            fun ω => M0 ω r := by
          funext ω
          have := congrFun (hMpart (t + 1) (by omega) ω) r
          have hx : X (t + 1) ω = mkX (candN P A C2 hA81 hA Z0 M0 s t0 0 ω) (s (t + 1) ω) := by
            simp only [hX, candX, ht', Nat.sub_self]
          rw [hx] at this
          exact this
        rw [this]
        have := hMk r
        rwa [show t0 - 1 = t by omega] at this
      · have : (fun ω => candΦ P A C2 hA81 hA Z0 M0 s t0 (t + 1) ω (Sum.inr r)) =
            fun _ => 0 := by
          funext ω
          simp only [candΦ, show ¬ t0 ≤ t + 1 by omega, ↓reduceIte, Pi.zero_apply]
        rw [this]
        exact stronglyMeasurable_const
  · rw [hMpart t0 le_rfl ω]
    simp only [hX, candX, Nat.sub_self]
    rfl
  · -- (1.9)
    filter_upwards [hEΦ t ht] with ω e
    rw [e, candY_eq P A C2 hA81 hA Z0 M0 s ht, candΦ_eq P A C2 hA81 hA Z0 M0 s ht]
    exact (pf_spec P A C2 hA81 hA (X t ω)).2.2.2.2 0 le_rfl ()

/-! ### Proposition 8.2: the linear form (1.5) and optimality -/

include hA81 hA in
/-- Woodford (2003), **Proposition 8.2, the linear form (1.5)**, p. 555, with
`Z̄_t = (Z_t, M_{t−1})` (predetermined: `M_{t−1}` is known at `t − 1`) and `s̄_t = s_t`: there are
**time-invariant**
`f⁰`, `f_Z`, `f_s` — fixed by the structural matrices, the loss and the VAR matrix `A` alone —
such that on **every** probability space and filtration, for every VAR(1) exogenous state with
`E_t s_{t+1} = A s_t`, every `t₀` and all initial conditions, every bounded solution of
(1.1) + (1.9) has `z_t = f⁰ + f_Z Z̄_t + f_s s_t` a.s. at every `t ≥ t₀`. -/
theorem prop82_linear_form :
    ∃ (f0 : ιz → ℝ) (FZ : Matrix ιz (ιZ ⊕ ιz) ℝ) (Fs : Matrix ιz ιs ℝ),
      ∀ {Ω' : Type*} [MeasurableSpace Ω'] (S : MeasExpectationSystem Ω')
        (s : ℕ → Ω' → ιs → ℝ), IsVAR S A s → ∀ (t0 : ℕ) (Z0 : Ω' → ιZ → ℝ)
        (M0 : Ω' → ιz → ℝ) (y : ℕ → Ω' → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω' → ιZ ⊕ ιz → ℝ),
        MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ →
        (∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) →
        ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, zpart (y t ω) =
          f0 + FZ *ᵥ Sum.elim (Zpart (y t ω)) (Mpart (φ t ω)) + Fs *ᵥ s t ω := by
  refine ⟨zpart (fY P A C2 hA81 hA),
    (FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) Sum.inl,
    (FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) Sum.inr,
    fun S s hs t0 Z0 M0 y φ h hM0 t ht => ?_⟩
  filter_upwards [linear_form P A C2 hA81 hA hs h hM0 t ht] with ω e
  have hz := congrArg zpart e
  rw [hz, stateX, mulVec_mkX]
  funext j
  simp only [zpart, Pi.add_apply]
  rw [add_assoc]
  rfl

/-- Woodford (2003), **Definition, pp. 538–539, and Proposition 8.2 (second part)**, p. 555, on a
VAR economy: every bounded solution of (1.1) + (1.9) is **optimal from a timeless perspective**
in the sense of the Definition, with the substantive state `X̄_t = (Z_t, M_{t−1}, s_t)`:
(1) `z_t = f⁰ + F X̄_t` a.s. for all `t ≥ t₀` with time-invariant `f⁰`, `F`; (2) it minimises (1.2)
a.s. among all bounded feasible plans subject to `Ẽ z_{t₀} = Ẽ (f⁰ + F X̄_{t₀})` (Lagrangian
sufficiency with genuine conditional expectations). -/
theorem timelesslyOptimal_var {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ}
    (hs : IsVAR S A s) {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) :
    MTimelesslyOptimalPlan S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (stateX y φ s)
      (zpart (fY P A C2 hA81 hA)) ((FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) id) y := by
  have h1 : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, zpart (y t ω) = zpart (fY P A C2 hA81 hA) +
      (FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) id *ᵥ stateX y φ s t ω := by
    intro t ht
    filter_upwards [linear_form P A C2 hA81 hA hs h hM0 t ht] with ω e
    rw [e]
    rfl
  obtain ⟨hf, -, hopt⟩ := m_optimalSubjectTo_of_focSystem h
  have he : ∀ᵐ ω ∂S.μ, P.sys.Et *ᵥ zpart (y t0 ω) = P.sys.Et *ᵥ (zpart (fY P A C2 hA81 hA) +
      (FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) id *ᵥ stateX y φ s t0 ω) := by
    filter_upwards [h1 t0 le_rfl] with ω e
    rw [e]
  refine ⟨h1, hf, he, fun y' hy' he' => hopt y' hy' ?_⟩
  filter_upwards [he', he] with ω e1 e2
  rw [e1, e2]

/-- Woodford (2003), **Assumption 8.1 and Proposition 8.2 on every VAR economy**, p. 541 and
p. 555: under the perfect-foresight Assumption 8.1 and stability of `H_n`, for every probability
space and filtration, every VAR(1) exogenous state, every `t₀`, every bounded `Z_{t₀}` known at
`t₀` and every bounded `M_{t₀−1}` known at `t₀ − 1`, (1.1) + (1.9) has a bounded solution, it is
unique a.s., and it is optimal from a timeless perspective with `X̄_t = (Z_t, M_{t−1}, s_t)`. -/
theorem m_existsUnique_var (hstab : PencilSplit.PowDecay (Hn P A C2 hA81 hA))
    {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s) {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0)
    (hMb : MBoundedRV S M0) (hMk : MKnownV S (t0 - 1) M0) :
    ∃ y φ, MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ ∧
      (∀ y' φ', MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y' φ' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t ∧ φ' t =ᵐ[S.μ] φ t) ∧
      MTimelesslyOptimalPlan S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (stateX y φ s)
        (zpart (fY P A C2 hA81 hA)) ((FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) id) y := by
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ := fun r =>
    ((hMk r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  have h := m_focSolvable_var P A C2 hA81 hA hstab hs hZk hZb hMb hMk
  exact ⟨_, _, h, fun y' φ' h' t ht => m_focUnique_var P A C2 hA81 hA hs hM0 h' h t ht,
    timelesslyOptimal_var P A C2 hA81 hA hs h hM0⟩

/-! ### Proposition 8.1's split along the forecasts: (1.19), (1.20), (1.23) and (1.24) -/

/-- Woodford (2003), eq. (1.25), p. 554: `q_t = E_t Q(L⁻¹) T̃'W(τ_t − τ*)` — the operator `Q(L⁻¹)`
of Proposition 8.1 (`Prop81General.Qop`, built from a deflating pair) applied to the conditional
forecasts `k ↦ E_t T̃'W(τ_{t+k} − τ*)`, so that `q_t` involves only date-`t` conditional
expectations of future targets. -/
noncomputable def qM (Dsp : PencilSplit.DeflatingSplit P.sys P.β) (S : MeasExpectationSystem Ω)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) : ιz → ℝ :=
  Prop81General.Qop perfectForesight Dsp
    (TargetCriterion.Prop81.xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω)) 0 ()

omit [DecidableEq ιs] in
/-- Woodford (2003), **(1.20) and (1.19)**, p. 553, with genuine conditional expectations: along
every bounded solution of (1.1) + (1.9) on a VAR economy, a.s. for all `t ≥ t₀`,
`M_t = Λ M_{t−1} + q_t` with `Λ = β⁻¹K⁻¹Ẽ'` of Proposition 8.1 and `q_t` of (1.25), and
`B₂'M_t + v_t = 0` with `v_t = T_i'W(τ_t − τ*)` (1.26) (from the core Proposition 8.1,
`Prop81General.prop81`, applied to the conditional forecast path). -/
theorem eq119_120_var (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s) {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 M0 y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => M0 ω r) S.μ) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, Mpart (φ (t + 1) ω) =
        PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ Mpart (φ t ω) + qM P Dsp S y t ω ∧
      P.sys.B2 ⬝ᵥ Mpart (φ (t + 1) ω) + TargetCriterion.Prop81.vproc P y t ω = 0 := by
  classical
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  have hMk : ∀ ω, Mpart (EVm S t (φ (t + 1)) ω) = Mpart (φ (t + 1) ω) := by
    intro ω
    funext r
    exact congrFun (S.E_of_stronglyMeasurable (h.2.2.2.1 t r)
      (integrable_of_bound (h.2.2.1 (t + 1) _) ((hKφ (t + 1)).mono fun ω h => h _))) ω
  have hy0 : EVm S t (y t) = y t := EVm_of_known S (h.1.2.2.2 t) (hyi t)
  filter_upwards [forecast_focSystem P A C2 hs h hM0 ht] with ω hω
  obtain ⟨⟨-, -, hyb, -⟩, hφb, hmm, hM, hfoc⟩ := hω
  have h118 : TargetCriterion.Prop81.Eq118 P perfectForesight 0
      (fun k _ => EVm S t (y (t + k)) ω) (fun k _ => EVm S t (φ (t + k)) ω) := by
    intro k _ u
    have := hfoc k (Nat.zero_le k) u
    exact ((foc_iff_split P hmm (fun k _ => EVm S t (y (t + k)) ω) k u).mp this).1
  have h119 := ((foc_iff_split P hmm (fun k _ => EVm S t (y (t + k)) ω) 0 ()).mp
    (hfoc 0 le_rfl ())).2
  have heq := ((Prop81General.prop81 P Dsp perfectForesight 0).equiv _ _ hyb (fun _ _ => rfl)
    hφb (fun _ _ _ => rfl)).mp h118
  have h120 := heq.1 0 le_rfl ()
  change Mpart (EVm S t (φ (t + 1)) ω) = PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ
    Mpart (EVm S t (φ (t + 0)) ω) + qM P Dsp S y t ω at h120
  have hM' : Mpart (EVm S t (φ (t + 0)) ω) = Mpart (φ t ω) := hM ()
  rw [hMk, hM'] at h120
  refine ⟨h120, ?_⟩
  change P.sys.B2 ⬝ᵥ Mpart (EVm S t (φ (t + 1)) ω) +
    P.Ti ⬝ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 0)) ω - P.τstar)) = 0 at h119
  have hy0' : EVm S t (y (t + 0)) = y t := hy0
  rw [hMk, hy0'] at h119
  exact h119

/-- Woodford (2003), p. 555 (the history before `t₀`, a.s. version of
`TargetCriterion.Prop82.HistoryOK`): on the window `t₀ − D ≤ s < t₀` the historical multipliers
satisfy (1.20) and (1.19) a.s. with the historical `q`, `v`. -/
def HistoryOKm (S : MeasExpectationSystem Ω) (Λ : Matrix ιz ιz ℝ) (B2 : ιz → ℝ) (t0 D : ℕ)
    (Mh qh : ℕ → Ω → ιz → ℝ) (vh : ℕ → Ω → ℝ) : Prop :=
  (∀ s, t0 - D ≤ s → s < t0 → ∀ᵐ ω ∂S.μ, Mh s ω = Λ *ᵥ Mh (s - 1) ω + qh s ω) ∧
    ∀ s, t0 - D ≤ s → s < t0 → ∀ᵐ ω ∂S.μ, B2 ⬝ᵥ Mh s ω + vh s ω = 0

omit [DecidableEq ιs] in
/-- Woodford (2003), (1.20) and (1.19) for the spliced processes (history before `t₀`, the
solution from `t₀` on), a.s. for all dates `s ≥ t₀ − D`. -/
theorem spliced_119_120 (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s) {t0 D : ℕ}
    (ht0 : 1 ≤ t0)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (Mh (t0 - 1)) y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) :
    ∀ᵐ ω ∂S.μ, ∀ u, t0 - D ≤ u →
      TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω =
        PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ
          TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) (u - 1) ω +
          TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y) u ω ∧
      P.sys.B2 ⬝ᵥ TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω +
        TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y) u ω = 0 := by
  classical
  have hsol : ∀ u, ∀ᵐ ω ∂S.μ, t0 ≤ u → Mpart (φ (u + 1) ω) =
        PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ Mpart (φ u ω) + qM P Dsp S y u ω ∧
      P.sys.B2 ⬝ᵥ Mpart (φ (u + 1) ω) + TargetCriterion.Prop81.vproc P y u ω = 0 := by
    intro u
    by_cases hu : t0 ≤ u
    · filter_upwards [eq119_120_var P A C2 Dsp hs h hM0 hu] with ω e _
      exact e
    · exact Eventually.of_forall fun _ h' => absurd h' hu
  have hh1 : ∀ u, ∀ᵐ ω ∂S.μ, t0 - D ≤ u → u < t0 →
      Mh u ω = PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ Mh (u - 1) ω + qh u ω := by
    intro u
    by_cases hu : t0 - D ≤ u ∧ u < t0
    · filter_upwards [hhist.1 u hu.1 hu.2] with ω e _ _
      exact e
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hu
  have hh2 : ∀ u, ∀ᵐ ω ∂S.μ, t0 - D ≤ u → u < t0 → P.sys.B2 ⬝ᵥ Mh u ω + vh u ω = 0 := by
    intro u
    by_cases hu : t0 - D ≤ u ∧ u < t0
    · filter_upwards [hhist.2 u hu.1 hu.2] with ω e _ _
      exact e
    · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hu
  filter_upwards [ae_all_iff.2 hsol, ae_all_iff.2 hh1, ae_all_iff.2 hh2, h.2.2.2.2.1]
    with ω e1 e2 e3 e4 u hu
  unfold TargetCriterion.Recursion.splice
  by_cases hlt : u < t0
  · simp only [hlt, ↓reduceIte, show u - 1 < t0 by omega]
    exact ⟨e2 u hu hlt, e3 u hu hlt⟩
  · push Not at hlt
    simp only [show ¬ u < t0 by omega, ↓reduceIte]
    refine ⟨?_, (e1 u hlt).2⟩
    rw [(e1 u hlt).1]
    by_cases hu0 : u = t0
    · simp only [show u - 1 < t0 by omega, ↓reduceIte]
      rw [hu0, e4]
    · simp only [show ¬ u - 1 < t0 by omega, ↓reduceIte, show u - 1 + 1 = u by omega]

omit [DecidableEq ιs] in
/-- Woodford (2003), **(1.23)**, p. 554, and fn 14, with genuine conditional expectations: along
every bounded solution of (1.1) + (1.9) on a VAR economy whose initial multiplier comes from a
consistent history, the **target criterion** `α(L) v_t + B₂' B(L) q_t = 0` holds a.s. at every
`t ≥ t₀` (`α = det(I − ΛL)`, `B = adj(I − ΛL)`, `q_t` of (1.25), history before `t₀`): the
optimal equilibrium is the one that commitment to (1.23) brings about. -/
theorem criterion_var (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s) {t0 D : ℕ}
    (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (Mh (t0 - 1)) y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, TargetCriterion.Crit.crit
      (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J))
      (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J)) D P.sys.B2
      (TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y))
      (TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y)) t ω = 0 := by
  classical
  intro t ht
  filter_upwards [spliced_119_120 P A C2 Dsp hs (by omega) hhist h hM0] with ω e
  have := TargetCriterion.Crit.eq123_of_eq119_eq120 (Adjugate.eq122 _) hB hα P.sys.B2
    (M := fun u (_ : Unit) =>
      TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω)
    (q := fun u (_ : Unit) => TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y) u ω)
    (v := fun u (_ : Unit) =>
      TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y) u ω)
    (t0 := t0 - D) (fun u hu _ => (e u hu).2) (fun u hu _ => (e u hu).1) t (by omega) ()
  exact this

omit [DecidableEq ιs] in
/-- Woodford (2003), **(1.17) and (1.24)**, p. 554, with genuine conditional expectations: along
every bounded solution of (1.1) + (1.9) on a VAR economy with a consistent history, a.s. at every
`t ≥ t₀` the lagged multipliers are the **time-invariant linear rule** of Assumption 8.5
(`Prop82General.KrylovBound.gRule`, with the fixed matrix `C` of `krylov_factor`) applied to the
predetermined window `q_{t−D}, …, q_{t−1}`, `v_{t−D}, …, v_{t−1}` of (1.24):
`M_{t−1} = g(q_{t−1..t−D}, v_{t−1..t−D})`. -/
theorem multiplier_rule_var (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    {C : Matrix ιz (Fin (PencilSplit.Λmat P.sys P.β Dsp.J).rank) ℝ}
    (hC : ∀ w, PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ w =
      C *ᵥ fun j => (P.sys.B2 ᵥ* PencilSplit.Λmat P.sys P.β Dsp.J ^ (j.val + 1)) ⬝ᵥ w)
    {S : MeasExpectationSystem Ω} {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s) {t0 D : ℕ}
    (hD : D + 1 ≤ t0) (hD1 : 1 ≤ D) (hDk : (PencilSplit.Λmat P.sys P.β Dsp.J).rank ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (Mh (t0 - 1)) y φ)
    (hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Mpart (φ t ω) =
      Prop82General.KrylovBound.gRule (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 C D
        (fun i => TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y) (t - D + i) ω)
        (fun i => TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y)
          (t - D + i) ω) := by
  classical
  intro t ht
  filter_upwards [spliced_119_120 P A C2 Dsp hs (by omega) hhist h hM0, h.2.2.2.2.1] with ω e e0
  have hrule := Prop82General.KrylovBound.multiplier_rule hC hD1 hDk (s0 := t - 1 - D)
    (m := fun u => TargetCriterion.Recursion.splice t0 Mh (fun u ω => Mpart (φ (u + 1) ω)) u ω)
    (q := fun u => TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y) u ω)
    (v := fun u => TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y) u ω)
    (fun j _ _ => (e (t - 1 - D + j) (by omega)).1) (fun j _ _ => (e (t - 1 - D + j) (by omega)).2)
  rw [show t - 1 - D + D = t - 1 by omega] at hrule
  have hidx : ∀ i, t - 1 - D + 1 + i = t - D + i := fun i => by omega
  simp only [hidx] at hrule
  rw [← hrule]
  unfold TargetCriterion.Recursion.splice
  by_cases hlt : t - 1 < t0
  · have ht0 : t = t0 := by omega
    subst ht0
    simp only [hlt, ↓reduceIte]
    exact e0
  · simp only [hlt, ↓reduceIte, show t - 1 + 1 = t by omega]

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), (1.17) and (1.24): the initial-multiplier rule `g` is additive in the
predetermined window `(q, v)`. -/
theorem gRule_add {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ)
    (C : Matrix ι (Fin Λ.rank) ℝ) (K : ℕ) (qs1 qs2 : ℕ → ι → ℝ) (vs1 vs2 : ℕ → ℝ) :
    Prop82General.KrylovBound.gRule Λ B2 C K (qs1 + qs2) (vs1 + vs2) =
      Prop82General.KrylovBound.gRule Λ B2 C K qs1 vs1 +
        Prop82General.KrylovBound.gRule Λ B2 C K qs2 vs2 := by
  unfold Prop82General.KrylovBound.gRule
  have h : (fun j : Fin Λ.rank => -(vs1 + vs2) j.val - ∑ i ∈ Finset.range (j.val + 1),
      B2 ⬝ᵥ (Λ ^ (j.val - i) *ᵥ (qs1 + qs2) i)) =
      (fun j : Fin Λ.rank => -vs1 j.val - ∑ i ∈ Finset.range (j.val + 1),
        B2 ⬝ᵥ (Λ ^ (j.val - i) *ᵥ qs1 i)) +
      (fun j : Fin Λ.rank => -vs2 j.val - ∑ i ∈ Finset.range (j.val + 1),
        B2 ⬝ᵥ (Λ ^ (j.val - i) *ᵥ qs2 i)) := by
    funext j
    simp only [Pi.add_apply, mulVec_add, dotProduct_add, Finset.sum_add_distrib]
    ring
  rw [h, mulVec_add, mulVec_add]
  simp only [Pi.add_apply, mulVec_add, Finset.sum_add_distrib]
  abel

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [Fintype ιs] [DecidableEq ιZ] [DecidableEq ιz]
  [DecidableEq ιs] in
/-- Woodford (2003), (1.17) and (1.24): the initial-multiplier rule `g` is homogeneous in the
predetermined window `(q, v)`; with `gRule_add`, `g` is linear. -/
theorem gRule_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ)
    (C : Matrix ι (Fin Λ.rank) ℝ) (K : ℕ) (c : ℝ) (qs : ℕ → ι → ℝ) (vs : ℕ → ℝ) :
    Prop82General.KrylovBound.gRule Λ B2 C K (c • qs) (c • vs) =
      c • Prop82General.KrylovBound.gRule Λ B2 C K qs vs := by
  unfold Prop82General.KrylovBound.gRule
  have h : (fun j : Fin Λ.rank => -(c • vs) j.val - ∑ i ∈ Finset.range (j.val + 1),
      B2 ⬝ᵥ (Λ ^ (j.val - i) *ᵥ (c • qs) i)) =
      c • (fun j : Fin Λ.rank => -vs j.val - ∑ i ∈ Finset.range (j.val + 1),
        B2 ⬝ᵥ (Λ ^ (j.val - i) *ᵥ qs i)) := by
    funext j
    simp only [Pi.smul_apply, mulVec_smul, dotProduct_smul, smul_eq_mul, ← Finset.mul_sum]
    ring
  rw [h, mulVec_smul, mulVec_smul, smul_add]
  simp only [Pi.smul_apply, mulVec_smul, Finset.smul_sum]

omit [DecidableEq ιZ] [DecidableEq ιz] [DecidableEq ιs] in
/-- Woodford (2003), (1.5) (tool): the forward-looking block of `F X` for `X = (Z, M, s)`. -/
theorem zpart_mulVec_state (F : Matrix ((ιZ ⊕ ιz) ⊕ Unit) ((ιZ ⊕ ιz) ⊕ ιs) ℝ) (Z : ιZ → ℝ)
    (M : ιz → ℝ) (σ : ιs → ℝ) :
    zpart (F *ᵥ mkX (Sum.elim Z M) σ) =
      F.submatrix (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inl) *ᵥ Z +
        F.submatrix (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inr) *ᵥ M +
          F.submatrix (Sum.inl ∘ Sum.inr) Sum.inr *ᵥ σ := by
  funext j
  simp only [zpart, mulVec, dotProduct, Fintype.sum_sum_type, mkX, Sum.elim_inl, Sum.elim_inr,
    submatrix_apply, Function.comp_apply, Pi.add_apply]

include hA81 hA in
/-- Woodford (2003), **Proposition 8.2**, p. 555: **"In this equilibrium, `z_t` each period is
given by a linear relation of the form (1.5), where `s̄_t = s_t` … and `Z̄_t` is given by
(1.24)."** Under the perfect-foresight Assumption 8.1, the deflating split of Proposition 8.1
and Assumption 8.5, there are time-invariant `f⁰`, `f_Z`, `f_M`, `f_s` and the fixed matrix `C`
of the multiplier rule such that on every probability space and filtration, for every VAR(1)
exogenous state, every `t₀ ≥ D + 1`, every consistent history and every bounded solution of
(1.1) + (1.9) with that history, a.s. at every `t ≥ t₀`
`z_t = f⁰ + f_Z Z_t + f_M g(q_{t−1}, …, q_{t−D}, v_{t−1}, …, v_{t−D}) + f_s s_t`,
a time-invariant linear function (`gRule_add`, `gRule_smul`) of
`Z̄_t = (Z_t, q_{t−1}, …, q_{t−D}, v_{t−1}, …, v_{t−D})` (1.24) and `s_t`. -/
theorem prop82_linear_form_124 (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D : ℕ} (hD1 : 1 ≤ D) (hDk : (PencilSplit.Λmat P.sys P.β Dsp.J).rank ≤ D) :
    ∃ (f0 : ιz → ℝ) (FZ : Matrix ιz ιZ ℝ) (FM : Matrix ιz ιz ℝ) (Fs : Matrix ιz ιs ℝ)
      (C : Matrix ιz (Fin (PencilSplit.Λmat P.sys P.β Dsp.J).rank) ℝ),
      ∀ {Ω' : Type*} [MeasurableSpace Ω'] (S : MeasExpectationSystem Ω')
        (s : ℕ → Ω' → ιs → ℝ), IsVAR S A s → ∀ (t0 : ℕ), D + 1 ≤ t0 →
        ∀ (Mh qh : ℕ → Ω' → ιz → ℝ) (vh : ℕ → Ω' → ℝ),
        HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh →
        ∀ (Z0 : Ω' → ιZ → ℝ) (y : ℕ → Ω' → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω' → ιZ ⊕ ιz → ℝ),
        MFOCSystem S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (Mh (t0 - 1)) y φ →
        (∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ) →
        ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, zpart (y t ω) = f0 + FZ *ᵥ Zpart (y t ω) +
          FM *ᵥ Prop82General.KrylovBound.gRule (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 C D
            (fun i => TargetCriterion.Recursion.splice t0 qh (qM P Dsp S y) (t - D + i) ω)
            (fun i => TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y)
              (t - D + i) ω) + Fs *ᵥ s t ω := by
  obtain ⟨C, hC⟩ := Prop82General.KrylovBound.krylov_factor h85
  refine ⟨zpart (fY P A C2 hA81 hA),
    (FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inl),
    (FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inr),
    (FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) Sum.inr, C,
    fun S s hs t0 hD Mh qh vh hhist Z0 y φ h hM0 t ht => ?_⟩
  filter_upwards [linear_form P A C2 hA81 hA hs h hM0 t ht,
    multiplier_rule_var P A C2 Dsp hC hs hD hD1 hDk hhist h hM0 t ht] with ω e1 e2
  have hz := congrArg zpart e1
  have hza : ∀ a b : (ιZ ⊕ ιz) ⊕ Unit → ℝ, zpart (a + b) = zpart a + zpart b := fun _ _ => rfl
  rw [hz, stateX, hza, zpart_mulVec_state, ← e2]
  abel

end Woodford.OptimalPolicyRules.OptimalRulesMeasureMarkov
