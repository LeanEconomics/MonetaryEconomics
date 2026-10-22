/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.CaseIIInstance
import OptimalPolicyRules.InertiaAssumption81

/-!
# Proposition 8.2 for the case-(ii) example system: Assumption 8.5 holds, Assumption 8.1 fails

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541), Proposition 8.2
(p. 555), Assumption 8.5 (App. G.2, p. 719), for the concrete case-(ii) system
`CaseIIInstance.exProblem` (`A = [[1, 1], [−1, 1]]`, `Î = I`, `B₂ = 1`, `β = 1/4`), which
satisfies Assumption 8.2 (ii) (`CaseIIInstance.ex82`) and the corrected Assumption 8.4 (ii)
(`CaseIIInstance.ex84`), so that Proposition 8.1 holds for it (`CaseIIInstance.ex_prop81`).

Its loss is identically zero (`T̃ = 0`, `T_i = 0`): the problem has no target variables that
move.

## Main results

* `ex_assumption85`: **Assumption 8.5 holds** for the `Λ = β⁻¹K⁻¹Ẽ'` of every `J` with `K`
  invertible, in particular for the case-(ii) construction (`ex_assumption85_caseII`).
* `ex_foc_rows`: the first-order conditions (1.9) force `M_t = 0`, `E_tξ_{t+1} = M_t + 4ξ_t` and
  `E_tξ_{t+1} = 4M_{t−1} − M_t` from `t₀` on.
* `ex_not_focSolvableM`: **existence in Assumption 8.1 fails**: with `M_{t₀−1} = 1` (bounded,
  deterministic) the system (1.1) + (1.9) has no bounded solution, on any nonempty sample space
  and for any expectation system.
* `ex_not_focUnique`: **uniqueness in Assumption 8.1 fails**: the zero plan and a two-period
  bump `bumpPlan` both solve (1.1) + (1.9) with zero multipliers.
* `ex_not_assumption81`, `ex_not_assumption81M`, `ex_not_assumption81MB`: so Assumption 8.1 fails
  in every formalisation, and `CaseIIBasis.prop82_caseII` cannot be applied.
* `ex_not_robustlyOptimal_direct`, `ex_prop82_conclusion_fails`,
  `ex_prop82_conclusion_fails_B`: **the conclusion of Proposition 8.2 is false for this
  system**: no direct rule (a rule that depends on the plan only through its target variables,
  p. 547) — in particular the target criterion (1.23) of any representation of
  Proposition 8.1 — determines a unique bounded equilibrium, even with bounded initial
  conditions.

So `exProblem` satisfies Assumptions 8.2 (ii), 8.4 (ii) and 8.5 but not 8.1, and Proposition 8.2
fails for it: Assumption 8.1 cannot be dropped from Proposition 8.2. (A case-(ii) system where
every hypothesis holds and Proposition 8.2 is proved is the inflation-inertia model in the
complex case, `InertiaProp82Complex.in_prop82_complex_B`.)
-/

namespace Woodford.OptimalPolicyRules.TidyR5aCaseIIExample

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ PencilSplit Prop81General CaseIIInstance

variable {Ω : Type*}

/-! ### Assumption 8.5 -/

/-- Woodford (2003), Assumption 8.5, App. G.2, p. 719, for `1 × 1` systems: if `Λ ≠ 0` and
`B₂ ≠ 0` then `B₂'Λ⁰` and `B₂'Λ¹` (the families of `PencilAssumptions.Assumption85`, indexed by
`Fin (rank Λ) = Fin 1`) are linearly independent. -/
theorem assumption85_one {Λ : Matrix (Fin 1) (Fin 1) ℝ} {B2 : Fin 1 → ℝ} (hΛ : Λ 0 0 ≠ 0)
    (hB : B2 0 ≠ 0) : PencilAssumptions.Assumption85 Λ B2 := by
  have hdet : IsUnit Λ.det := by
    rw [isUnit_iff_ne_zero, det_unique]
    exact hΛ
  have hr : Λ.rank = 1 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr hdet)]
    simp
  have key : ∀ k : ℕ, (B2 ᵥ* Λ ^ k) 0 = B2 0 * Λ 0 0 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← vecMul_vecMul]
      simp only [vecMul, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
      rw [show (B2 ᵥ* Λ ^ k) = fun j => (B2 ᵥ* Λ ^ k) j from rfl] at ih
      simp only [vecMul, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
        Finset.sum_singleton] at ih
      rw [ih]
      ring
  have hne : ∀ k : ℕ, B2 ᵥ* Λ ^ k ≠ 0 := by
    intro k h0
    have := congrFun h0 0
    rw [key k, Pi.zero_apply] at this
    exact mul_ne_zero hB (pow_ne_zero _ hΛ) this
  constructor
  · generalize hk : Λ.rank = k at hr ⊢
    subst hr
    exact linearIndependent_unique_iff.mpr (by simpa using hne 0)
  · unfold TargetCriterion.Krylov.Assumption85b
    generalize hk : Λ.rank = k at hr ⊢
    subst hr
    exact linearIndependent_unique_iff.mpr (by simpa using hne 1)

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, holds for `exProblem`**, for the
`Λ = β⁻¹K⁻¹Ẽ'` of every `J` with `K = A₂₂' + A₁₂'Υ` invertible. -/
theorem ex_assumption85 (J : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ) (hK : (Kmat exSys J).det ≠ 0) :
    PencilAssumptions.Assumption85 (Λmat exSys exProblem.β J) exSys.B2 := by
  refine assumption85_one ?_ (by simp [exSys])
  have hK0 : Kmat exSys J 0 0 ≠ 0 := by rwa [det_unique] at hK
  have hinv : (Kmat exSys J)⁻¹ 0 0 = (Kmat exSys J 0 0)⁻¹ := by
    rw [inv_def, adjugate_fin_one, det_unique]
    simp [Ring.inverse_eq_inv']
  have hE : exSys.Et 0 0 = 1 := rfl
  have hb : exProblem.β = 1 / 4 := rfl
  have e : Λmat exSys exProblem.β J 0 0 = 4 * (Kmat exSys J 0 0)⁻¹ := by
    simp only [Λmat, Matrix.smul_apply, Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, hinv, smul_eq_mul, transpose_apply, hE, hb]
    norm_num
  rw [e]
  exact mul_ne_zero (by norm_num) (inv_ne_zero hK0)

/-- **Woodford (2003), Assumption 8.5, App. G.2, for the case-(ii) construction of
Proposition 8.1 for `exProblem`** (`CaseIIBasis.quasiSplitOfEx` with `CaseIIInstance.ex82`,
`CaseIIInstance.ex84`): the hypothesis `h85` of `CaseIIBasis.prop82_caseII` holds. -/
theorem ex_assumption85_caseII :
    PencilAssumptions.Assumption85 (Λmat exProblem.sys exProblem.β
      ((CaseIIBasis.quasiSplitOfEx exProblem ex82 (Multiset.mem_singleton_self μ0) ex84).Jp *
        (CaseIIBasis.quasiSplitOfEx exProblem ex82 (Multiset.mem_singleton_self μ0) ex84).P))
      exProblem.sys.B2 :=
  ex_assumption85 _
    (CaseIIBasis.quasiSplitOfEx exProblem ex82 (Multiset.mem_singleton_self μ0) ex84).K_det

/-! ### The first-order conditions -/

/-- Woodford (2003), (1.9), p. 541, for `exProblem` at `(t, ω)` (with `M_t` known at `t`): the
three rows (columns of `y = (Z, z, i)`) read `E_tξ_{t+1} − M_t − 4ξ_t = 0`,
`E_tξ_{t+1} + M_t − 4M_{t−1} = 0` and `M_t = 0` (`β⁻¹ = 4`, `T = 0`). -/
theorem ex_foc_rows {𝔼 : ExpectationSystem Ω} {φ : ℕ → Ω → Fin 1 ⊕ Fin 1 → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) (y : ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω)
    (h : exProblem.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
      exProblem.Tᵀ *ᵥ (exProblem.W *ᵥ (exProblem.T *ᵥ y t ω - exProblem.τstar)) -
        exProblem.β⁻¹ • (exProblem.sys.Itilᵀ *ᵥ φ t ω) = 0) :
    𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl 0)) ω - φ (t + 1) ω (Sum.inr 0) -
        4 * φ t ω (Sum.inl 0) = 0 ∧
      𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl 0)) ω + φ (t + 1) ω (Sum.inr 0) -
        4 * φ t ω (Sum.inr 0) = 0 ∧
      φ (t + 1) ω (Sum.inr 0) = 0 := by
  rw [foc_iff_split _ hmφ] at h
  obtain ⟨h1, h2⟩ := h
  have hE : EV 𝔼 t (φ (t + 1)) ω (Sum.inr 0) = φ (t + 1) ω (Sum.inr 0) :=
    congrFun (hmφ t 0) ω
  have r0 := congrFun h1 (Sum.inl 0)
  have r1 := congrFun h1 (Sum.inr 0)
  simp only [exProblem, exSys, LinearRESystem.Ahat, LinearRESystem.Ihat, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, mulVec, dotProduct, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, transpose_apply,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, add_zero, Matrix.one_apply_eq, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val'] at r0 r1
  simp only [exProblem, exSys, Mpart, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Matrix.cons_val_zero, Pi.zero_apply, zero_mul, add_zero,
    one_mul] at h2
  simp only [EV] at r0 r1 hE
  norm_num at r0 r1
  refine ⟨by linarith, by linarith, h2⟩

/-! ### Assumption 8.1 fails: existence -/

/-- **Woodford (2003), Assumption 8.1 (existence), p. 541, fails for `exProblem`**: on any
nonempty sample space and for any expectation system, with zero disturbance, `Z_{t₀} = 0` and the
bounded deterministic initial multiplier `M_{t₀−1} = 1`, the system (1.1) + (1.9) has no bounded
solution. (The `i`-row forces `M_t = 0` for `t ≥ t₀`; then `ξ_t = 0` for `t > t₀`, and the
`z`-row at `t₀` reads `E_{t₀}ξ_{t₀+1} = 4M_{t₀−1}`, i.e. `0 = 4`.) -/
theorem ex_not_focSolvableM [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ¬ Prop82General.FOCSolvableM exProblem 𝔼 t0 := by
  intro hS
  obtain ⟨y, φ, -, -, hmφ, hM0, hfoc⟩ := hS (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 1)
    ⟨0, fun _ _ _ => by simp⟩ (fun t i => 𝔼.const t 0) (fun i => 𝔼.const t0 0)
    ⟨1, fun _ _ => by simp⟩ (fun i => 𝔼.const (t0 - 1) 1)
  have rows := fun t ht ω => ex_foc_rows hmφ y t ω (hfoc t ht ω)
  -- `M_t = 0` from `t₀` on
  have hM : ∀ t, t0 ≤ t → ∀ ω, φ (t + 1) ω (Sum.inr 0) = 0 := fun t ht ω => (rows t ht ω).2.2
  -- `ξ_s = 0` for `s > t₀`
  have hξ : ∀ s, t0 + 1 ≤ s → ∀ ω, φ s ω (Sum.inl 0) = 0 := by
    intro s hs ω
    obtain ⟨r0, r1, r2⟩ := rows s (by omega) ω
    have hm1 : φ s ω (Sum.inr 0) = 0 := by
      have := hM (s - 1) (by omega) ω
      rwa [show s - 1 + 1 = s by omega] at this
    rw [r2] at r0 r1
    rw [hm1] at r1
    linarith
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  obtain ⟨-, r1, r2⟩ := rows t0 le_rfl ω
  have hz : (fun ω' => φ (t0 + 1) ω' (Sum.inl 0)) = fun _ => (0 : ℝ) :=
    funext fun ω' => hξ (t0 + 1) le_rfl ω'
  have hm : φ t0 ω (Sum.inr 0) = 1 := congrFun (hM0 ω) 0
  rw [hz, 𝔼.const, r2, hm] at r1
  norm_num at r1

/-! ### Assumption 8.1 fails: uniqueness -/

/-- Woodford (2003), (1.1) for `exProblem` (tool): the value of a two-period bump at date `t`
relative to `t₀`: `a` at `t₀`, `b` at `t₀ + 1`, `0` otherwise. -/
noncomputable def bump (t0 : ℕ) (a b : ℝ) (t : ℕ) : ℝ :=
  if t = t0 then a else if t = t0 + 1 then b else 0

/-- Woodford (2003), (1.1), p. 537, for `exProblem`: a deterministic two-period bump plan —
`z_{t₀} = 1`, `z_{t₀+1} = −1`, `Z_{t₀+1} = 1`, `i_{t₀} = −2`, `i_{t₀+1} = 2`, zero otherwise. -/
noncomputable def bumpPlan (t0 : ℕ) : ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ :=
  fun t _ => Sum.elim (Sum.elim (fun _ => bump t0 0 1 t) (fun _ => bump t0 1 (-1) t))
    (fun _ => bump t0 (-2) 2 t)

/-- Woodford (2003), (1.1), p. 537: the zero plan. -/
def zeroPlan : ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ := fun _ _ _ => 0

/-- Woodford (2003), (1.1) for `exProblem` (tool): the structural equations of a deterministic
plan `(Z_t, z_t, i_t)` with zero disturbance are `Z_{t+1} = Z_t + z_t` and
`z_{t+1} = −Z_t + z_t + i_t`. -/
theorem ex_structural_det (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (Zf zf iff : ℕ → ℝ)
    (h1 : ∀ t, t0 ≤ t → Zf (t + 1) = Zf t + zf t)
    (h2 : ∀ t, t0 ≤ t → zf (t + 1) = -Zf t + zf t + iff t) :
    exSys.Structural 𝔼 (fun _ _ _ => 0) t0
      (fun t _ => Sum.elim (Sum.elim (fun _ => Zf t) (fun _ => zf t)) (fun _ => iff t)) := by
  intro t ht ω
  refine ⟨funext fun j => ?_, ?_⟩
  · fin_cases j
    simp [Zpart, zpart, exSys, dotProduct, h1 t ht]
  · funext j
    fin_cases j
    simp only [mulVec, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [EV, zpart, Zpart, ipart, Sum.elim_inl, Sum.elim_inr, 𝔼.const]
    simp [exSys, h2 t ht]

/-- Woodford (2003), (1.1) (tool): a deterministic plan is adapted. -/
theorem adaptedV_det (𝔼 : ExpectationSystem Ω) (g : ℕ → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) :
    AdaptedV 𝔼 (fun t (_ : Ω) => g t) :=
  fun t i => 𝔼.const t (g t i)

/-- Woodford (2003), (1.1)–(1.4) (tool): the targets of `exProblem` vanish, `T = 0`. -/
theorem ex_T_mulVec (v : (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) : exProblem.T *ᵥ v = 0 := by
  funext a
  simp [exProblem, LQProblem.T, mulVec, dotProduct]

/-- Woodford (2003), (1.1), p. 537: the zero plan is feasible for `exProblem` with zero
disturbance and `Z_{t₀} = 0`. -/
theorem zeroPlan_feasible (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    exProblem.Feasible 𝔼 (fun _ _ _ => 0) t0 (fun _ _ => 0) zeroPlan := by
  have hs := ex_structural_det 𝔼 t0 (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ _ => by simp) (fun _ _ => by simp)
  have e : (zeroPlan : ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) = fun t _ =>
      Sum.elim (Sum.elim (fun _ => (0 : ℝ)) (fun _ => 0)) (fun _ => 0) := by
    funext t ω v
    rcases v with (v | v) | v <;> rfl
  refine ⟨?_, fun ω => funext fun j => rfl, ⟨0, fun _ _ _ => by simp [zeroPlan]⟩,
    fun t i => 𝔼.const t 0⟩
  rw [e]
  exact hs

/-- Woodford (2003), (1.1), p. 537: the bump plan is feasible for `exProblem` with zero
disturbance and `Z_{t₀} = 0`. -/
theorem bumpPlan_feasible (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    exProblem.Feasible 𝔼 (fun _ _ _ => 0) t0 (fun _ _ => 0) (bumpPlan t0) := by
  have hs := ex_structural_det 𝔼 t0 (bump t0 0 1) (bump t0 1 (-1)) (bump t0 (-2) 2)
    (fun t ht => by
      unfold bump
      rcases Nat.lt_or_ge t (t0 + 2) with h | h
      · rcases (show t = t0 ∨ t = t0 + 1 by omega) with rfl | rfl <;> simp
      · simp [show t + 1 ≠ t0 by omega, show t ≠ t0 by omega, show t ≠ t0 + 1 by omega])
    (fun t ht => by
      unfold bump
      rcases Nat.lt_or_ge t (t0 + 2) with h | h
      · rcases (show t = t0 ∨ t = t0 + 1 by omega) with rfl | rfl
        · norm_num
        · norm_num [show t0 + 1 + 1 ≠ t0 by omega]
      · simp [show t + 1 ≠ t0 by omega, show t ≠ t0 by omega, show t ≠ t0 + 1 by omega])
  refine ⟨hs, fun ω => funext fun j => by simp [bumpPlan, Zpart, bump], ⟨2, fun t ω v => ?_⟩,
    adaptedV_det 𝔼 _⟩
  rcases v with (v | v) | v <;> simp only [bumpPlan, bump, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;> norm_num

/-- Woodford (2003), (1.9) (tool): with zero multipliers the first-order conditions of
`exProblem` hold for every plan (the loss is zero). -/
theorem ex_pfoc_zero (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (y : ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) :
    PFOC exProblem 𝔼 t0 y (fun _ _ _ => 0) := by
  intro t _ ω
  have hEV : EV 𝔼 t (fun (_ : Ω) (_ : Fin 1 ⊕ Fin 1) => (0 : ℝ)) ω = 0 := by
    funext i
    simp only [EV, 𝔼.const, Pi.zero_apply]
  rw [hEV, ex_T_mulVec]
  ext a
  simp [exProblem, mulVec, dotProduct]

/-- Woodford (2003), (1.1) + (1.9) (tool): a feasible plan of `exProblem` with zero multipliers
solves the first-order system with `M_{t₀−1} = 0`. -/
theorem ex_focSystem_zero {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    {y : ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ}
    (hy : exProblem.Feasible 𝔼 (fun _ _ _ => 0) t0 (fun _ _ => 0) y) :
    FOCSystem exProblem 𝔼 (fun _ _ _ => 0) t0 (fun _ _ => 0) (fun _ _ => 0) y
      (fun _ _ _ => 0) :=
  ⟨hy, ⟨0, fun _ _ _ => by simp⟩, fun t r => 𝔼.const t 0, fun _ => rfl, ex_pfoc_zero 𝔼 t0 y⟩

/-- **Woodford (2003), Assumption 8.1 (uniqueness), p. 541, fails for `exProblem`**: on any
nonempty sample space the zero plan and `bumpPlan` are two different bounded solutions of
(1.1) + (1.9) with the same disturbance and initial conditions. -/
theorem ex_not_focUnique [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ¬ FOCUnique exProblem 𝔼 t0 := by
  intro hU
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have h := (hU _ _ _ _ _ _ _ (ex_focSystem_zero (zeroPlan_feasible 𝔼 t0))
    (ex_focSystem_zero (bumpPlan_feasible 𝔼 t0)) t0 le_rfl).1
  have := congrFun (congrFun h ω) (Sum.inl (Sum.inr 0))
  simp [zeroPlan, bumpPlan, bump] at this

/-- **Woodford (2003), Assumption 8.1, p. 541, fails for `exProblem`** in the original
formalisation `GeneralFOC.LQ.Assumption81` (nonempty sample space, any expectation system). -/
theorem ex_not_assumption81 [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ¬ Assumption81 exProblem 𝔼 t0 :=
  fun h => ex_not_focUnique 𝔼 t0 h.unique

/-- **Woodford (2003), Assumption 8.1, p. 541, fails for `exProblem`** in the corrected
formalisation `Prop82General.Assumption81M` (both halves fail). -/
theorem ex_not_assumption81M [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ¬ Prop82General.Assumption81M exProblem 𝔼 t0 :=
  fun h => ex_not_focSolvableM 𝔼 t0 h.solvable

/-- **Woodford (2003), Assumption 8.1, p. 541, fails for `exProblem`** with bounded initial
conditions (`InertiaAssumption81.Assumption81MB`). -/
theorem ex_not_assumption81MB [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ¬ InertiaAssumption81.Assumption81MB exProblem 𝔼 t0 :=
  fun h => ex_not_focUnique 𝔼 t0 h.unique

/-! ### The conclusion of Proposition 8.2 fails -/

/-- Woodford (2003), p. 547: a rule is **direct** when it involves the plan only through its
target variables `τ_t = T y_t` (1.4). -/
def DirectRule {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιz]
    (P : LQProblem ιZ ιz ιτ)
    (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop) : Prop :=
  ∀ c y y', (∀ t ω, P.T *ᵥ y t ω = P.T *ᵥ y' t ω) → (Rl c y ↔ Rl c y')

/-- Woodford (2003), (1.23)–(1.26), pp. 554–555: the target criterion (1.23) of any
representation of Proposition 8.1 is a direct rule: it involves the plan only through
`q_t = Q(T̃'W(τ_t − τ*))` and `v_t = T_i'W(τ_t − τ*)`. -/
theorem criterionM_direct {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ]
    [DecidableEq ιZ] [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81ConclusionM P 𝔼 t0) (D : ℕ) (qh : ℕ → Ω → ιz → ℝ)
    (vh : ℕ → Ω → ℝ) :
    DirectRule P (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y) := by
  intro _ y y' hT
  have hx : TargetCriterion.Prop81.xproc P y = TargetCriterion.Prop81.xproc P y' := by
    funext t ω
    simp only [TargetCriterion.Prop81.xproc, hT t ω]
  have hv : TargetCriterion.Prop81.vproc P y = TargetCriterion.Prop81.vproc P y' := by
    funext t ω
    simp only [TargetCriterion.Prop81.vproc, hT t ω]
  simp only [Prop82General.Prop82M.CriterionM, hx, hv]

/-- **Woodford (2003), Definition (1.16), pp. 549–550: no direct rule is robustly optimal for
`exProblem`, even with bounded initial conditions.** Every plan has the same (zero) targets, so a
direct rule satisfied by one feasible plan is satisfied by all of them, and the zero plan and
`bumpPlan` are two different bounded feasible plans (zero disturbance, `Z_{t₀} = 0`). -/
theorem ex_not_robustlyOptimalB_direct [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    {κ : Type*} [Fintype κ]
    {Rl : (ℕ → Ω → Fin 1 → ℝ) → (ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) → Prop}
    (hRl : DirectRule exProblem Rl)
    (Xbar : (ℕ → Ω → Fin 1 → ℝ) → (ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) :
    ¬ InertiaAssumption81.RobustlyOptimalB exProblem 𝔼 t0 Rl Xbar := by
  intro h
  obtain ⟨y, -, hR, hU, -⟩ := h (fun _ _ _ => 0) (fun _ _ => 0) ⟨0, fun _ _ _ => by simp⟩
    (fun t i => 𝔼.const t 0) (fun i => 𝔼.const t0 0) ⟨0, fun _ _ => by simp⟩
  have hT : ∀ y' : ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ, Rl (fun _ _ _ => 0) y' := fun y' =>
    (hRl _ y y' fun t ω => by rw [ex_T_mulVec, ex_T_mulVec]).mp hR
  have h0 := hU zeroPlan (zeroPlan_feasible 𝔼 t0) (hT _) t0 le_rfl
  have h1 := hU (bumpPlan t0) (bumpPlan_feasible 𝔼 t0) (hT _) t0 le_rfl
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun (h0.trans h1.symm) ω) (Sum.inl (Sum.inr 0))
  simp [zeroPlan, bumpPlan, bump] at this

/-- **Woodford (2003), Definition (1.16): no direct rule is robustly optimal for `exProblem`**
(every initial condition, `GeneralSetup.RobustlyOptimal`). -/
theorem ex_not_robustlyOptimal_direct [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    {κ : Type*} [Fintype κ]
    {Rl : (ℕ → Ω → Fin 1 → ℝ) → (ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) → Prop}
    (hRl : DirectRule exProblem Rl)
    (Xbar : (ℕ → Ω → Fin 1 → ℝ) → (ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) :
    ¬ RobustlyOptimal exProblem 𝔼 t0 Rl Xbar :=
  fun h => ex_not_robustlyOptimalB_direct 𝔼 t0 hRl Xbar (InertiaAssumption81.RobustlyOptimal.toB h)

/-- **Woodford (2003), Proposition 8.2, p. 555: its conclusion fails for `exProblem`.** For every
representation `H` of the corrected Proposition 8.1 (one exists, `CaseIIInstance.ex_prop81`),
every window `D` and history `(qh, vh)`, commitment to the target criterion (1.23) is not
robustly optimal: it does not determine a unique bounded equilibrium. Assumptions 8.2 (ii),
8.4 (ii) and 8.5 hold (`CaseIIInstance.ex82`, `CaseIIInstance.ex84`, `ex_assumption85_caseII`);
Assumption 8.1 fails (`ex_not_assumption81M`), and it cannot be dropped. -/
theorem ex_prop82_conclusion_fails [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (H : Prop81ConclusionM exProblem 𝔼 t0) (D : ℕ) (qh : ℕ → Ω → Fin 1 → ℝ)
    (vh : ℕ → Ω → ℝ) {κ : Type*} [Fintype κ]
    (Xbar : (ℕ → Ω → Fin 1 → ℝ) → (ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) :
    ¬ RobustlyOptimal exProblem 𝔼 t0 (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
      Xbar :=
  ex_not_robustlyOptimal_direct 𝔼 t0 (criterionM_direct H D qh vh) Xbar

/-- **Woodford (2003), Proposition 8.2, p. 555: its conclusion fails for `exProblem` even with
bounded initial conditions** (`InertiaAssumption81.RobustlyOptimalB`). -/
theorem ex_prop82_conclusion_fails_B [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (H : Prop81ConclusionM exProblem 𝔼 t0) (D : ℕ) (qh : ℕ → Ω → Fin 1 → ℝ)
    (vh : ℕ → Ω → ℝ) {κ : Type*} [Fintype κ]
    (Xbar : (ℕ → Ω → Fin 1 → ℝ) → (ℕ → Ω → (Fin 1 ⊕ Fin 1) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) :
    ¬ InertiaAssumption81.RobustlyOptimalB exProblem 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y) Xbar :=
  ex_not_robustlyOptimalB_direct 𝔼 t0 (criterionM_direct H D qh vh) Xbar

/-- **Woodford (2003), Proposition 8.2, p. 555, for the case-(ii) example, summarised**: under
perfect foresight, Proposition 8.1 holds (`CaseIIInstance.ex_prop81`), Assumption 8.5 holds for
its case-(ii) construction, Assumption 8.1 fails, and commitment to the resulting target criterion
(1.23) (any window, any history) is not robustly optimal. -/
theorem ex_prop82_summary (t0 D : ℕ) (qh : ℕ → Unit → Fin 1 → ℝ) (vh : ℕ → Unit → ℝ) :
    Nonempty (Prop81ConclusionM exProblem perfectForesight t0) ∧
      PencilAssumptions.Assumption85 (Λmat exProblem.sys exProblem.β
        ((CaseIIBasis.quasiSplitOfEx exProblem ex82 (Multiset.mem_singleton_self μ0) ex84).Jp *
          (CaseIIBasis.quasiSplitOfEx exProblem ex82 (Multiset.mem_singleton_self μ0) ex84).P))
        exProblem.sys.B2 ∧
      ¬ Assumption81 exProblem perfectForesight t0 ∧
      ¬ RobustlyOptimal (κ := Fin 1) exProblem perfectForesight t0
        (fun _ y => Prop82General.Prop82M.CriterionM
          (Prop81CaseII.prop81II exProblem
            (CaseIIBasis.quasiSplitOfEx exProblem ex82 (Multiset.mem_singleton_self μ0) ex84)
            perfectForesight t0) D qh vh y)
        (fun _ y t ω => zpart (y t ω)) :=
  ⟨ex_prop81 perfectForesight t0, ex_assumption85_caseII,
    ex_not_assumption81 perfectForesight t0, ex_prop82_conclusion_fails _ t0 _ D qh vh _⟩

end Woodford.OptimalPolicyRules.TidyR5aCaseIIExample
