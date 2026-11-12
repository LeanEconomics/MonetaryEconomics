/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.SimplestModel

/-!
# Sticky prices: `φ > 1` is neither necessary nor sufficient, and Friedman's spiral

Cochrane (2023), Chapter 16, p. 369 ("In more general models, the greater than one-for-one
reaction of interest rates to inflation is neither necessary nor sufficient to the essential
condition, which is one additional explosive eigenvalue in system dynamics"), Chapter 12, p. 328
(claim P8: "What matters, here, is the `φ` in `E_tπ_{t+1} = φπ_t`, not the `φ` in `i_t = φπ_t`")
and Chapter 12, pp. 324–325 (claim P1: Friedman's adaptive-expectations spiral under a peg).

The sticky-price models are those of Chapter 17. The three-equation deviation system, its
determinacy criterion and the witnesses are restated from the Cochrane KeynesianStickyPrices
project (modules SharedTools, TaylorDeterminacy and StaticIS), with the namespace renamed; the
results in the namespaces Fisherian and Friedman are new.

## Main results

* ThreeEq (restated): the three-equation model with `i = φπ + φ_x x`; `ThreeEq.determinate_iff`
  (both eigenvalues of the dynamics explosive), `ThreeEq.determinate_iff_BM`,
  `ThreeEq.not_necessary_witness`, `ThreeEq.not_necessary_phix`, `ThreeEq.not_necessary_negative`,
  `ThreeEq.not_sufficient_witness`, `ThreeEq.not_sufficient`.
* Fisherian (new): the Fisherian sticky-price model `x_t = −σ(i_t − E_tπ_{t+1})`,
  `π_t = βE_tπ_{t+1} + κx_t`. With the rule `i_t = φπ_t + u_t` it reduces exactly to
  `E_tπ_{t+1} = λπ_t + cu_t` with `λ = (1 + σκφ)/(β + σκ)` (`Fisherian.rule_iff`), and is
  determinate iff `|λ| > 1` (`Fisherian.rule_determinate_iff`): the eigenvalue, not `φ`, decides.
  For `β < 1`, `φ ∈ (1 − (1 − β)/(σκ), 1)` is determinate (`Fisherian.not_necessary`,
  `Fisherian.not_necessary_witness`). With the forecast rule `i_t = φE_tπ_{t+1} + u_t` the
  eigenvalue is `1/(β − σκ(φ − 1))` (`Fisherian.fwd_iff`, `Fisherian.fwd_determinate_iff`), and
  every `φ > 1 + (1 + β)/(σκ)` is indeterminate (`Fisherian.not_sufficient`,
  `Fisherian.not_sufficient_witness`). `Fisherian.p369`: both claims at once.
* Adaptive (restated): (17.6), `Adaptive.adaptive_peg`, `Adaptive.adaptive_peg_unbounded`;
  Friedman (new): `Friedman.spiral_up` (a peg below inflation, `ī < π_{−1}`: inflation rises
  every period without bound), `Friedman.spiral_down` (a peg above inflation, as at the zero
  bound: an unbounded deflation spiral), and the rational-expectations contrast
  `Friedman.re_peg_stable` (`E_0π_t → ī` geometrically): the spiral comes from adaptive
  expectations.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6StickyPrices

open Filter Topology

namespace ThreeEq

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 420: the matrix `A = P⁻¹ Q` of `x_t = A E_t x_{t+1}`, written with the
adjugate of `P`. -/
noncomputable def solvedA (P Q : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(P 1 1 * Q 0 0 - P 0 1 * Q 1 0) / det2 P, (P 1 1 * Q 0 1 - P 0 1 * Q 1 1) / det2 P;
    (P 0 0 * Q 1 0 - P 1 0 * Q 0 0) / det2 P, (P 0 0 * Q 1 1 - P 1 0 * Q 0 1) / det2 P]

/-- Cochrane (2023), p. 420: `tr A = (P₁₁Q₀₀ − P₀₁Q₁₀ − P₁₀Q₀₁ + P₀₀Q₁₁)/det P`. -/
theorem tr2_solvedA (P Q : Matrix (Fin 2) (Fin 2) ℝ) :
    tr2 (solvedA P Q) =
      (P 1 1 * Q 0 0 - P 0 1 * Q 1 0 - P 1 0 * Q 0 1 + P 0 0 * Q 1 1) / det2 P := by
  simp only [tr2, solvedA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Cochrane (2023), p. 420: `det A = det Q / det P`. -/
theorem det2_solvedA {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : det2 P ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : det2 (solvedA P Q) = det2 Q / det2 P := by
  have h : det2 (solvedA P Q) = solvedA P Q 0 0 * solvedA P Q 1 1 -
      solvedA P Q 0 1 * solvedA P Q 1 0 := rfl
  rw [h]
  simp only [solvedA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [div_mul_div_comm, div_mul_div_comm, div_sub_div_same,
    div_eq_div_iff (mul_ne_zero hP hP) hP]
  unfold det2
  ring

/-- Cochrane (2023), p. 420: the structural matrix `P = [[1 + σφ_x, σφ], [−κ, 1]]`. -/
def Pmat (σ κ φ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + σ * φx, σ * φ; -κ, 1]

/-- Cochrane (2023), p. 420: the structural matrix `Q = [[1, σ], [0, β]]`. -/
def Qmat (σ β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, σ; 0, β]

/-- Cochrane (2023), p. 420: `D = det P = 1 + σφ_x + σκφ`. -/
theorem det2_Pmat (σ κ φ φx : ℝ) : det2 (Pmat σ κ φ φx) = 1 + σ * φx + σ * κ * φ := by
  simp [det2, Pmat]; ring


/-! ### Generic structural systems `P x_t = Q E_t x_{t+1}` -/

/-- Cochrane (2023), p. 420 (the system behind (17.33)): `x` solves `P x_t = Q E_t x_{t+1}`. -/
def StructSolves (P Q : Matrix (Fin 2) (Fin 2) ℝ) (x : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, P i 0 • x t 0 + P i 1 • x t 1 =
    Q i 0 • 𝔼.E t (x (t + 1) 0) + Q i 1 • 𝔼.E t (x (t + 1) 1)

/-- Cochrane (2023), p. 420: determinacy — the only bounded adapted solution of
`P x_t = Q E_t x_{t+1}` is zero. -/
def StructDeterminate (P Q : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x, 𝔼.AdaptedVec x → BoundedVec x → StructSolves 𝔼 P Q x → x = 0

/-- Cochrane (2023), p. 420: solving two linear equations by Cramer's rule. -/
theorem solve2 {P00 P01 P10 P11 q0 q1 a b : ℝ} (hD : P00 * P11 - P01 * P10 ≠ 0) :
    (P00 * a + P01 * b = q0 ∧ P10 * a + P11 * b = q1) ↔
      (a = (P11 * q0 - P01 * q1) / (P00 * P11 - P01 * P10) ∧
        b = (P00 * q1 - P10 * q0) / (P00 * P11 - P01 * P10)) := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor <;> rw [eq_div_iff hD]
    · linear_combination P11 * h0 - P01 * h1
    · linear_combination P00 * h1 - P10 * h0
  · rintro ⟨ha, hb⟩
    have ka : a * (P00 * P11 - P01 * P10) = P11 * q0 - P01 * q1 := by
      rw [ha, div_mul_cancel₀ _ hD]
    have kb : b * (P00 * P11 - P01 * P10) = P00 * q1 - P10 * q0 := by
      rw [hb, div_mul_cancel₀ _ hD]
    constructor <;> apply mul_right_cancel₀ hD
    · linear_combination P00 * ka + P01 * kb
    · linear_combination P10 * ka + P11 * kb

/-- Cochrane (2023), p. 420: for `det P ≠ 0`, `P x_t = Q E_t x_{t+1}` iff
`x_t = A E_t x_{t+1}`, `A = P⁻¹ Q`. -/
theorem struct_iff_solves {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : det2 P ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (x : ℕ → Fin 2 → Ω → ℝ) :
    StructSolves 𝔼 P Q x ↔ 𝔼.Solves (solvedA P Q) 0 x := by
  have hP' : P 0 0 * P 1 1 - P 0 1 * P 1 0 ≠ 0 := hP
  have hd : det2 P = P 0 0 * P 1 1 - P 0 1 * P 1 0 := rfl
  constructor
  · intro h t i
    funext ω
    have e0 := congrFun (h t 0) ω
    have e1 := congrFun (h t 1) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
    obtain ⟨ha, hb⟩ := (solve2 hP').mp ⟨e0, e1⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    fin_cases i
    · simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [ha]; ring
    · simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
      rw [hb]; ring
  · intro h t i
    funext ω
    have e0 := congrFun (h t 0) ω
    have e1 := congrFun (h t 1) ω
    simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, add_zero] at e0 e1
    have hab := (solve2 hP' (a := x t 0 ω) (b := x t 1 ω)
      (q0 := Q 0 0 * 𝔼.E t (x (t + 1) 0) ω + Q 0 1 * 𝔼.E t (x (t + 1) 1) ω)
      (q1 := Q 1 0 * 𝔼.E t (x (t + 1) 0) ω + Q 1 1 * 𝔼.E t (x (t + 1) 1) ω)).mpr
      ⟨by rw [e0]; ring, by rw [e1]; ring⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · exact hab.1
    · exact hab.2

/-- Cochrane (2023), p. 420: if `det P = 0` the system is not determinate — a vector `v ≠ 0`
with `P v = 0` gives the bounded solution `x_0 = v`, `x_t = 0` for `t ≥ 1`. -/
theorem not_determinate_of_det_zero [Nonempty Ω] {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : det2 P = 0) (Q : Matrix (Fin 2) (Fin 2) ℝ) : ¬ StructDeterminate 𝔼 P Q := by
  have hP' : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 0 := hP
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, P i 0 * v 0 + P i 1 * v 1 = 0 := by
    by_cases h0 : P 0 0 = 0 ∧ P 0 1 = 0
    · by_cases h1 : P 1 0 = 0 ∧ P 1 1 = 0
      · refine ⟨![1, 0], fun h => by simpa using congrFun h 0, fun i => ?_⟩
        fin_cases i <;> simp [h0.1, h1.1]
      · refine ⟨![P 1 1, -P 1 0], fun h => h1 ⟨by simpa using congrFun h 1,
          by simpa using congrFun h 0⟩, fun i => ?_⟩
        fin_cases i
        · simp [h0.1, h0.2]
        · simp; ring
    · refine ⟨![P 0 1, -P 0 0], fun h => h0 ⟨by simpa using congrFun h 1,
        by simpa using congrFun h 0⟩, fun i => ?_⟩
      fin_cases i
      · simp; ring
      · simp; linear_combination -hP'
  intro hdet
  set x : ℕ → Fin 2 → Ω → ℝ := fun t j _ => if t = 0 then v j else 0 with hx
  have hsol : StructSolves 𝔼 P Q x := by
    intro t i
    funext ω
    simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_one_ne_zero, ↓reduceIte,
      𝔼.const, mul_zero, add_zero]
    split_ifs
    · exact hv i
    · simp
  have h := hdet x (fun t j => by simp only [hx]; exact 𝔼.const t _)
    ⟨|v 0| + |v 1|, fun t j ω => by
      simp only [hx]
      split_ifs
      · fin_cases j <;> simp
      · simp only [abs_zero]; positivity⟩ hsol
  apply hv0
  funext j
  have := congrFun (congrFun (congrFun h 0) j) (Classical.arbitrary Ω)
  simpa [hx] using this

/-- Cochrane (2023), p. 420, and A1 p. 587 (Blanchard–Kahn): `P x_t = Q E_t x_{t+1}` is
determinate iff `det P ≠ 0` and `A = P⁻¹Q` satisfies the Schur–Cohn condition. -/
theorem structDeterminate_iff [Nonempty Ω] (P Q : Matrix (Fin 2) (Fin 2) ℝ) :
    StructDeterminate 𝔼 P Q ↔
      det2 P ≠ 0 ∧ SchurStable (tr2 (solvedA P Q)) (det2 (solvedA P Q)) := by
  constructor
  · intro h
    have hP : det2 P ≠ 0 := fun h0 => not_determinate_of_det_zero 𝔼 h0 Q h
    refine ⟨hP, ?_⟩
    by_contra hA
    have hz : 𝔼.Solves (solvedA P Q) 0 0 := fun t i => by simp
    obtain ⟨y, hy, hay, hby, hne⟩ :=
      𝔼.system_not_unique hA hz (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    exact hne (h y hay hby ((struct_iff_solves 𝔼 hP Q y).mpr hy))
  · rintro ⟨hP, hA⟩ x hax hbx hx
    have hz : 𝔼.Solves (solvedA P Q) 0 0 := fun t i => by simp
    exact 𝔼.system_unique hA ((struct_iff_solves 𝔼 hP Q x).mp hx) hz hax
      (fun t i => by simp) hbx ⟨0, fun t i ω => by simp⟩

/-! ### The deviation system (17.29)–(17.32) -/

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, with an output response `φ_x` (eq. (18.1),
p. 427): `ĩ_t = r̃_t + E_t π̃_{t+1}`, `x̃_t = E_t x̃_{t+1} − σ r̃_t`,
`π̃_t = β E_t π̃_{t+1} + κ x̃_t`, `ĩ_t = φ π̃_t + φ_x x̃_t`. -/
def Deviation (σ β κ φ φx : ℝ) (i r x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + 𝔼.E t (π (t + 1)) ∧ x t = 𝔼.E t (x (t + 1)) - σ • r t ∧
    π t = β • 𝔼.E t (π (t + 1)) + κ • x t ∧ i t = φ • π t + φx • x t

/-- Cochrane (2023), p. 420: the stacked vector `(x̃_t, π̃_t)`. -/
def stack (x π : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, π t]

/-- Cochrane (2023), eqs. (17.29)–(17.32): eliminating `ĩ` and `r̃`, the deviation system is
`(1 + σφ_x) x̃_t + σφ π̃_t = E_t x̃_{t+1} + σ E_t π̃_{t+1}`, `−κ x̃_t + π̃_t = β E_t π̃_{t+1}`. -/
theorem deviation_iff_struct (σ β κ φ φx : ℝ) (i r x π : ℕ → Ω → ℝ) :
    Deviation 𝔼 σ β κ φ φx i r x π ↔
      (∀ t, i t = φ • π t + φx • x t) ∧ (∀ t, r t = i t - 𝔼.E t (π (t + 1))) ∧
        StructSolves 𝔼 (Pmat σ κ φ φx) (Qmat σ β) (stack x π) := by
  constructor
  · intro h
    refine ⟨fun t => (h t).2.2.2, fun t => by rw [(h t).1]; abel, fun t j => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    have e3 := congrFun h3 ω
    have e4 := congrFun h4 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
    fin_cases j
    · simp only [Pmat, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Qmat, one_smul]
      linear_combination e2 + σ * e1 - σ * e4
    · simp only [Pmat, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, stack, neg_smul,
        one_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Qmat, zero_smul,
        Pi.zero_apply, zero_add]
      linear_combination e3
  · rintro ⟨hi, hr, hs⟩ t
    have e0 := hs t 0
    have e1 := hs t 1
    simp only [Pmat, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Qmat, one_smul, neg_smul, zero_smul,
      zero_add] at e0 e1
    refine ⟨by rw [hr t]; abel, ?_, ?_, hi t⟩
    · funext ω
      have f0 := congrFun e0 ω
      have fi := congrFun (hi t) ω
      rw [hr t]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f0 fi ⊢
      rw [fi]
      linear_combination f0
    · funext ω
      have f1 := congrFun e1 ω
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at f1 ⊢
      linear_combination f1

/-- Cochrane (2023), p. 420: the deviation system is *determinate* when its only bounded
adapted solution has `x̃ = π̃ = 0` (and then `ĩ = r̃ = 0`). -/
def Determinate (σ β κ φ φx : ℝ) : Prop :=
  ∀ i r x π : ℕ → Ω → ℝ, 𝔼.Adapted x → 𝔼.Adapted π → BoundedProc x → BoundedProc π →
    Deviation 𝔼 σ β κ φ φx i r x π → x = 0 ∧ π = 0

/-- Cochrane (2023), p. 420: determinacy of the deviation system is determinacy of the
structural system. -/
theorem determinate_iff_struct (σ β κ φ φx : ℝ) :
    Determinate 𝔼 σ β κ φ φx ↔ StructDeterminate 𝔼 (Pmat σ κ φ φx) (Qmat σ β) := by
  constructor
  · intro h v hav hbv hv
    set x : ℕ → Ω → ℝ := fun t => v t 0
    set π : ℕ → Ω → ℝ := fun t => v t 1
    have hst : stack x π = v := by
      funext t j; fin_cases j <;> rfl
    have hd : Deviation 𝔼 σ β κ φ φx (fun t => φ • π t + φx • x t)
        (fun t => φ • π t + φx • x t - 𝔼.E t (π (t + 1))) x π :=
      (deviation_iff_struct 𝔼 σ β κ φ φx _ _ x π).mpr ⟨fun t => rfl, fun t => rfl, hst ▸ hv⟩
    obtain ⟨M, hM⟩ := hbv
    obtain ⟨h1, h2⟩ := h _ _ x π (fun t => hav t 0) (fun t => hav t 1)
      ⟨M, fun t ω => hM t 0 ω⟩ ⟨M, fun t ω => hM t 1 ω⟩ hd
    rw [← hst, h1, h2]
    funext t j
    fin_cases j <;> rfl
  · intro h i r x π hx hπ hbx hbπ hd
    have hs := ((deviation_iff_struct 𝔼 σ β κ φ φx i r x π).mp hd).2.2
    obtain ⟨M₁, h₁⟩ := hbx
    obtain ⟨M₂, h₂⟩ := hbπ
    have h0 := h (stack x π) (fun t j => by fin_cases j; exacts [hx t, hπ t])
      ⟨max M₁ M₂, fun t j ω => by
        fin_cases j
        · exact (h₁ t ω).trans (le_max_left _ _)
        · exact (h₂ t ω).trans (le_max_right _ _)⟩ hs
    exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun h0 t) 0,
      funext fun t => by simpa [stack] using congrFun (congrFun h0 t) 1⟩

/-- Cochrane (2023), p. 420 and A1 p. 587: the deviation system (with output response) is
determinate iff `D = 1 + σφ_x + σκφ ≠ 0` and `SchurStable (T/D) (β/D)`,
`T = 1 + β + σκ + βσφ_x`. -/
theorem determinate_iff [Nonempty Ω] (σ β κ φ φx : ℝ) :
    Determinate 𝔼 σ β κ φ φx ↔
      1 + σ * φx + σ * κ * φ ≠ 0 ∧
        SchurStable ((1 + β + σ * κ + β * σ * φx) / (1 + σ * φx + σ * κ * φ))
          (β / (1 + σ * φx + σ * κ * φ)) := by
  rw [determinate_iff_struct, structDeterminate_iff, det2_Pmat]
  refine and_congr_right fun hD => ?_
  have hD' : det2 (Pmat σ κ φ φx) ≠ 0 := by rwa [det2_Pmat]
  rw [tr2_solvedA, det2_solvedA hD', det2_Pmat]
  have hq : det2 (Qmat σ β) = β := by simp [det2, Qmat]
  rw [hq]
  have ht : Pmat σ κ φ φx 1 1 * Qmat σ β 0 0 - Pmat σ κ φ φx 0 1 * Qmat σ β 1 0 -
      Pmat σ κ φ φx 1 0 * Qmat σ β 0 1 + Pmat σ κ φ φx 0 0 * Qmat σ β 1 1 =
      1 + β + σ * κ + β * σ * φx := by
    simp [Pmat, Qmat]; ring
  rw [ht]

/-- Cochrane (2023), p. 420: Schur–Cohn for `(T/D, β/D)` with `D > 0`, `β > 0`:
`β < D ∧ |T| < D + β`. -/
theorem schur_div_pos {T D β : ℝ} (hD : 0 < D) (hβ : 0 < β) :
    SchurStable (T / D) (β / D) ↔ β < D ∧ |T| < D + β := by
  unfold SchurStable
  rw [abs_div, abs_div, abs_of_pos hD, abs_of_pos hβ, div_lt_one hD, one_add_div hD.ne',
    div_lt_div_iff_of_pos_right hD]

/-- Cochrane (2023), p. 420: Schur–Cohn for `(T/D, β/D)` with `D < 0`, `β > 0`:
`β < −D ∧ |T| < −D − β`. -/
theorem schur_div_neg {T D β : ℝ} (hD : D < 0) (hβ : 0 < β) :
    SchurStable (T / D) (β / D) ↔ β < -D ∧ |T| < -D - β := by
  unfold SchurStable
  have hD' : 0 < -D := by linarith
  have hD0 : D ≠ 0 := hD.ne
  rw [abs_div, abs_div, abs_of_neg hD, abs_of_pos hβ, div_lt_one hD',
    show 1 + β / D = (-D - β) / -D by field_simp; ring, div_lt_div_iff_of_pos_right hD']

/-- Cochrane (2023), p. 420 and A1 p. 587, explicit form: determinate iff
`(D > 0 ∧ β < D ∧ |T| < D + β) ∨ (D < 0 ∧ β < −D ∧ |T| < −D − β)`. -/
theorem determinate_iff_explicit [Nonempty Ω] {σ β κ φ φx : ℝ} (hβ : 0 < β) :
    Determinate 𝔼 σ β κ φ φx ↔
      (0 < 1 + σ * φx + σ * κ * φ ∧ β < 1 + σ * φx + σ * κ * φ ∧
          |1 + β + σ * κ + β * σ * φx| < 1 + σ * φx + σ * κ * φ + β) ∨
        (1 + σ * φx + σ * κ * φ < 0 ∧ β < -(1 + σ * φx + σ * κ * φ) ∧
          |1 + β + σ * κ + β * σ * φx| < -(1 + σ * φx + σ * κ * φ) - β) := by
  rw [determinate_iff]
  rcases lt_trichotomy (1 + σ * φx + σ * κ * φ) 0 with hD | hD | hD
  · rw [schur_div_neg hD hβ]
    constructor
    · rintro ⟨-, h⟩; exact Or.inr ⟨hD, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · linarith
      · exact ⟨hD.ne, h⟩
  · rw [hD]
    simp only [ne_eq, not_true_eq_false, false_and, lt_self_iff_false, false_or]
  · rw [schur_div_pos hD hβ]
    constructor
    · rintro ⟨-, h⟩; exact Or.inl ⟨hD, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ⟨hD.ne', h⟩
      · linarith

/-- Cochrane (2023), A1 p. 587 and eq. (1.58), with Ch17 p. 420: in the three-equation model
with `i = φπ` (`φ_x = 0`), `σ, κ > 0`, `0 < β < 1`, the equilibrium is determinate iff
`φ > 1` or `φ < −(1 + 2(1 + β)/(σκ))`. -/
theorem determinate_iff_phi [Nonempty Ω] {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) :
    Determinate 𝔼 σ β κ φ 0 ↔ 1 < φ ∨ φ < -(1 + 2 * (1 + β) / (σ * κ)) := by
  have ha := mul_pos hσ hκ
  rw [determinate_iff_explicit 𝔼 hβ]
  simp only [mul_zero, add_zero]
  have hT : 0 < 1 + β + σ * κ := by linarith
  rw [abs_of_pos hT]
  have hb : -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) = -(σ * κ) - 2 * (1 + β) := by
    field_simp
    ring
  constructor
  · rintro (⟨-, -, h⟩ | ⟨-, -, h⟩)
    · left
      nlinarith
    · right
      have : φ * (σ * κ) < -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) := by rw [hb]; nlinarith
      exact lt_of_mul_lt_mul_right this ha.le
  · rintro (h | h)
    · left
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · right
      have : φ * (σ * κ) < -(σ * κ) - 2 * (1 + β) := by
        rw [← hb]; exact mul_lt_mul_of_pos_right h ha
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Cochrane (2023), Ch16 p. 369 and A1 p. 587 (restated from Galí's Bullard–Mitra condition):
for `σ, κ > 0`, `0 < β < 1` and `φ, φ_x ≥ 0`, determinate iff `κ(φ − 1) + (1 − β)φ_x > 0`. -/
theorem determinate_iff_BM [Nonempty Ω] {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 0 ≤ φ) (hφx : 0 ≤ φx) :
    Determinate 𝔼 σ β κ φ φx ↔ 0 < κ * (φ - 1) + (1 - β) * φx := by
  rw [determinate_iff_explicit 𝔼 hβ]
  have h1 : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  have h2 : 0 ≤ σ * κ * φ := mul_nonneg (mul_pos hσ hκ).le hφ
  have hT : 0 < 1 + β + σ * κ + β * σ * φx := by
    have := mul_nonneg hβ.le h1
    nlinarith [mul_pos hσ hκ]
  rw [abs_of_pos hT]
  constructor
  · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
    · have : 0 < σ * (κ * (φ - 1) + (1 - β) * φx) := by nlinarith
      exact pos_of_mul_pos_right this hσ.le
    · linarith
  · intro h
    left
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith [mul_pos hσ h]


/-! ### φ > 1 is neither necessary nor sufficient -/

/-- Cochrane (2023), p. 420, A1 p. 587, Ch16 p. 369 and Ch12 p. 328 ("φ > 1 is neither
necessary …"): with `σ = κ = 1`, `β = 1/2`, the rule `i = 0.5 π + 2 x` (`φ < 1`) is
determinate. -/
theorem not_necessary_witness [Nonempty Ω] : Determinate 𝔼 1 (1 / 2) 1 (1 / 2) 2 :=
  (determinate_iff_BM 𝔼 one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).mpr (by norm_num)

/-- Cochrane (2023), p. 420 ("adding `φ_x x_t` responses widens the range"): for `σ, κ > 0`,
`0 < β < 1`, every `φ ∈ [0, 1)` is made determinate by a large enough output response. -/
theorem not_necessary_phix [Nonempty Ω] {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) :
    ∃ φx, 0 ≤ φx ∧ Determinate 𝔼 σ β κ φ φx := by
  have h1β : 0 < 1 - β := by linarith
  refine ⟨κ * (1 - φ) / (1 - β) + 1, by positivity, ?_⟩
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ0 (by positivity)]
  field_simp
  nlinarith

/-- Cochrane (2023), A1 p. 587, eq. (1.58): even with `φ_x = 0`, `φ > 1` is not necessary —
`σ = κ = 1`, `β = 1/2`, `φ = −5 < −(1 + 2(1 + β)/(σκ)) = −4` is determinate. -/
theorem not_necessary_negative [Nonempty Ω] : Determinate 𝔼 1 (1 / 2) 1 (-5) 0 :=
  (determinate_iff_phi 𝔼 one_pos one_pos (by norm_num) (by norm_num)).mpr (Or.inr (by norm_num))

/-- Cochrane (2023), p. 420, Ch16 p. 369, Ch12 P8 p. 328 ("… nor sufficient"; "the coefficient
can exceed 1 while the eigenvalue is stable"): with `σ = κ = 1`, `β = 1/2`, the rule
`i = 2π − 2x` (`φ = 2 > 1`) is not determinate. -/
theorem not_sufficient_witness [Nonempty Ω] : ¬ Determinate 𝔼 1 (1 / 2) 1 2 (-2) := by
  rw [determinate_iff_explicit 𝔼 (by norm_num)]
  norm_num

/-- Cochrane (2023), p. 420: for **every** `φ` (in particular every `φ > 1`) and `σ ≠ 0` there
is an output response `φ_x = −(1 + σκφ)/σ` that makes the system indeterminate. -/
theorem not_sufficient [Nonempty Ω] {σ β κ : ℝ} (hσ : σ ≠ 0) (φ : ℝ) :
    ∃ φx, ¬ Determinate 𝔼 σ β κ φ φx := by
  refine ⟨-(1 + σ * κ * φ) / σ, fun h => ((determinate_iff 𝔼 _ _ _ _ _).mp h).1 ?_⟩
  field_simp
  ring

/-- Cochrane (2023), p. 420: with a nonnegative output response, `φ > 1` is sufficient. -/
theorem sufficient_of_phix_nonneg [Nonempty Ω] {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 1 < φ) (hφx : 0 ≤ φx) : Determinate 𝔼 σ β κ φ φx :=
  (determinate_iff_BM 𝔼 hσ hκ hβ hβ1 (by linarith) hφx).mpr
    (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) hφx])

/-- Cochrane (2023), p. 420 ("adding `φ_x x_t` responses widens the range of parameters"):
for `φ ≥ 0`, raising a nonnegative output response preserves determinacy. -/
theorem widens_with_phix [Nonempty Ω] {σ β κ φ φx φx' : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 0 ≤ φ) (hφx : 0 ≤ φx) (hle : φx ≤ φx')
    (h : Determinate 𝔼 σ β κ φ φx) : Determinate 𝔼 σ β κ φ φx' := by
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ hφx] at h
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ (hφx.trans hle)]
  nlinarith

end ThreeEq

/-! ## Adaptive and rational expectations in the static model (restated) -/

namespace Adaptive

variable {Ω : Type*}

/-- Cochrane (2023), eqs. (17.3)–(17.4), p. 398: the static IS curve `x_t = −σ(i_t − πᵉ_t)` and
the Phillips curve `π_t = πᵉ_t + κ x_t`. -/
def StaticModel (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = -σ * (i t ω - πe t ω) ∧ π t ω = πe t ω + κ * x t ω

/-- Cochrane (2023), eq. (17.5), p. 398: eliminating `x_t` from (17.3)–(17.4), the static model
holds iff output is given by (17.3) and `π_t = −σκ i_t + (1 + σκ) πᵉ_t`. -/
theorem staticModel_iff (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) :
    StaticModel σ κ i πe x π ↔ (∀ t ω, x t ω = -σ * (i t ω - πe t ω)) ∧
      ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * πe t ω := by
  constructor
  · intro h
    refine ⟨fun t ω => (h t ω).1, fun t ω => ?_⟩
    obtain ⟨h1, h2⟩ := h t ω
    rw [h2, h1]; ring
  · rintro ⟨h1, h2⟩ t ω
    refine ⟨h1 t ω, ?_⟩
    rw [h2 t ω, h1 t ω]; ring

/-- Cochrane (2023), eq. (17.5), p. 398: an inflation process is part of an equilibrium of
(17.3)–(17.4) iff it satisfies the single equation (17.5). -/
theorem exists_static_iff_17_5 (σ κ : ℝ) (i πe π : ℕ → Ω → ℝ) :
    (∃ x, StaticModel σ κ i πe x π) ↔
      ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * πe t ω := by
  constructor
  · rintro ⟨x, hx⟩
    exact ((staticModel_iff σ κ i πe x π).mp hx).2
  · intro h
    exact ⟨fun t ω => -σ * (i t ω - πe t ω),
      (staticModel_iff σ κ i πe _ π).mpr ⟨fun _ _ => rfl, h⟩⟩

/-! ### Adaptive expectations (17.6) -/

/-- Cochrane (2023), p. 398: the lagged inflation process `π_{t−1}`, with initial value
`π_{−1}`; adaptive expectations set `πᵉ_t = π_{t−1}`. -/
def lagged (π0 : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => π t

/-- Cochrane (2023), eq. (17.6), p. 398: the adaptive-expectations equilibrium condition
`π_t = (1 + σκ) π_{t−1} − σκ i_t`, given `π_{−1}`. -/
def AdaptiveEq (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω = (1 + σ * κ) * lagged π0 π t ω - σ * κ * i t ω

/-- Cochrane (2023), eq. (17.6), p. 398: with `πᵉ_t = π_{t−1}` the static model (17.3)–(17.4)
reduces to (17.6). -/
theorem exists_static_adaptive_iff (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) :
    (∃ x, StaticModel σ κ i (lagged π0 π) x π) ↔ AdaptiveEq σ κ π0 i π := by
  rw [exists_static_iff_17_5]
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro h <;> rw [h] <;> ring

/-- Cochrane (2023), p. 398: (17.6) rearranged, `π_t − π_{t−1} = −σκ (i_t − π_{t−1})`: a higher
real rate brings inflation down. -/
theorem adaptive_change_iff (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) :
    AdaptiveEq σ κ π0 i π ↔ ∀ t ω,
      π t ω - lagged π0 π t ω = -(σ * κ) * (i t ω - lagged π0 π t ω) := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 399 (the old-Keynesian mechanism): with adaptive expectations a nominal
rate above lagged inflation (a high real rate) lowers output, and lower output lowers
inflation. -/
theorem adaptive_mechanism {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {π0 : Ω → ℝ}
    {i x π : ℕ → Ω → ℝ} (h : StaticModel σ κ i (lagged π0 π) x π) {t : ℕ} {ω : Ω}
    (hi : lagged π0 π t ω < i t ω) : x t ω < 0 ∧ π t ω < lagged π0 π t ω := by
  obtain ⟨h1, h2⟩ := h t ω
  have hx : x t ω < 0 := by rw [h1]; nlinarith
  exact ⟨hx, by rw [h2]; nlinarith⟩

/-- Cochrane (2023), eq. (17.6), p. 398: the solution of (17.6) built forward from `π_{−1}`. -/
def adaptivePath (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => (1 + σ * κ) * π0 ω - σ * κ * i 0 ω
  | t + 1 => fun ω => (1 + σ * κ) * adaptivePath σ κ π0 i t ω - σ * κ * i (t + 1) ω

/-- Cochrane (2023), eq. (17.6), p. 398: `adaptivePath` solves (17.6). -/
theorem adaptivePath_solves (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) :
    AdaptiveEq σ κ π0 i (adaptivePath σ κ π0 i) := by
  intro t ω
  cases t <;> rfl

/-- Cochrane (2023), p. 398, "There is only one equilibrium": two solutions of (17.6) with the
same `π_{−1}` coincide. -/
theorem adaptive_unique {σ κ : ℝ} {π0 : Ω → ℝ} {i π π' : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 i π) (h' : AdaptiveEq σ κ π0 i π') : π = π' := by
  funext t ω
  induction t with
  | zero => rw [h 0 ω, h' 0 ω]; rfl
  | succ t ih => rw [h (t + 1) ω, h' (t + 1) ω]; simp only [lagged]; rw [ih]

/-- Cochrane (2023), p. 398, "determinate": given `π_{−1}`, (17.6) has exactly one solution
(whatever the interest-rate path). -/
theorem adaptive_existsUnique (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) :
    ∃! π, AdaptiveEq σ κ π0 i π :=
  ⟨_, adaptivePath_solves σ κ π0 i, fun _ h => adaptive_unique h (adaptivePath_solves σ κ π0 i)⟩

/-- Cochrane (2023), eq. (17.6), p. 398: under an interest-rate peg `i_t = ī`,
`π_t − ī = (1 + σκ)^{t+1} (π_{−1} − ī)`. -/
theorem adaptive_peg {σ κ ib : ℝ} {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (t : ℕ) (ω : Ω) :
    π t ω = ib + (1 + σ * κ) ^ (t + 1) * (π0 ω - ib) := by
  induction t with
  | zero => rw [h 0 ω]; simp only [lagged]; ring
  | succ t ih => rw [h (t + 1) ω]; simp only [lagged]; rw [ih]; ring

/-- Cochrane (2023), p. 398, "unstable": under a peg, inflation spirals away from the peg,
`|π_t − ī| → ∞`, unless it starts exactly at the peg. -/
theorem adaptive_peg_unbounded {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) {ω : Ω} (hω : π0 ω ≠ ib) :
    Tendsto (fun t => |π t ω - ib|) atTop atTop := by
  have he : (fun t => |π t ω - ib|) = fun t => (1 + σ * κ) ^ (t + 1) * |π0 ω - ib| := by
    funext t
    rw [adaptive_peg h t ω, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]
  rw [he]
  have hpos : 0 < |π0 ω - ib| := abs_pos.mpr (sub_ne_zero.mpr hω)
  refine Tendsto.atTop_mul_const hpos ?_
  exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp (tendsto_add_atTop_nat 1)

/-- Cochrane (2023), p. 398: under a peg the adaptive solution is bounded iff inflation starts at
the peg, `π_{−1} = ī`. -/
theorem adaptive_peg_bounded_iff {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ}
    {π : ℕ → Ω → ℝ} (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (ω : Ω) :
    (∃ M, ∀ t, |π t ω| ≤ M) ↔ π0 ω = ib := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra hne
    obtain ⟨t, ht⟩ := ((adaptive_peg_unbounded hσκ h hne).eventually_gt_atTop
      (M + |ib|)).exists
    have := abs_sub (π t ω) ib
    linarith [hM t]
  · intro he
    exact ⟨|ib|, fun t => by rw [adaptive_peg h t ω, he, sub_self, mul_zero, add_zero]⟩

/-- Cochrane (2023), p. 398: `i = π` is a steady state of the adaptive model. -/
theorem adaptive_steady_state (σ κ c : ℝ) :
    AdaptiveEq σ κ (fun (_ : Ω) => c) (fun _ _ => c) (fun _ _ => c) := by
  intro t ω
  cases t <;> simp only [lagged] <;> ring

/-! ### Rational expectations (17.7) -/

/-- Cochrane (2023), eqs. (17.5) and (17.7), p. 398: the rational-expectations equilibrium
condition `π_t = −σκ i_t + (1 + σκ) E_t π_{t+1}`, with `π` adapted. -/
def REModel (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * 𝔼.E t (π (t + 1)) ω

/-- Cochrane (2023), p. 398: the rational-expectations model is (17.3)–(17.4) with
`πᵉ_t = E_t π_{t+1}`. -/
theorem reModel_iff_static (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i π : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ i π ↔
      𝔼.Adapted π ∧ ∃ x, StaticModel σ κ i (fun t => 𝔼.E t (π (t + 1))) x π := by
  rw [exists_static_iff_17_5]; rfl

/-- Cochrane (2023), eq. (17.7), p. 398:
`E_t π_{t+1} = π_t/(1 + σκ) + σκ/(1 + σκ) · i_t`. -/
theorem reModel_iff_17_7 (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    (i π : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ i π ↔ 𝔼.Adapted π ∧ ∀ t ω,
      𝔼.E t (π (t + 1)) ω = 1 / (1 + σ * κ) * π t ω + σ * κ / (1 + σ * κ) * i t ω := by
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun ω => ?_)
  constructor
  · intro e; rw [e]; field_simp; ring
  · intro e; rw [e]; field_simp; ring

/-- Cochrane (2023), p. 398: (17.7) rearranged, `E_t π_{t+1} − π_t = σκ (i_t − E_t π_{t+1})`:
a higher real rate raises subsequent expected inflation. -/
theorem re_change {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} {i π : ℕ → Ω → ℝ}
    (h : REModel 𝔼 σ κ i π) (t : ℕ) (ω : Ω) :
    𝔼.E t (π (t + 1)) ω - π t ω = σ * κ * (i t ω - 𝔼.E t (π (t + 1)) ω) := by
  rw [h.2 t ω]; ring

/-- Cochrane (2023), p. 398: with rational expectations a nominal rate above expected inflation
(a high real rate) raises expected inflation above current inflation. -/
theorem re_mechanism {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} (hσκ : 0 < σ * κ) {i π : ℕ → Ω → ℝ}
    (h : REModel 𝔼 σ κ i π) {t : ℕ} {ω : Ω} (hi : 𝔼.E t (π (t + 1)) ω < i t ω) :
    π t ω < 𝔼.E t (π (t + 1)) ω := by
  have := re_change h t ω
  nlinarith

/-- Cochrane (2023), p. 398, "The coefficient `1/(1 + σκ) < 1`": the coefficient of (17.7) lies
in `(0, 1)`, and the two coefficients sum to one. -/
theorem coeff_17_7 {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    0 < 1 / (1 + σ * κ) ∧ 1 / (1 + σ * κ) < 1 ∧ 0 < σ * κ / (1 + σ * κ) ∧
      1 / (1 + σ * κ) + σ * κ / (1 + σ * κ) = 1 := by
  have h1 : 0 < 1 + σ * κ := by linarith
  refine ⟨by positivity, by rw [div_lt_one h1]; linarith, by positivity, ?_⟩
  field_simp

end Adaptive

/-! ## The Fisherian sticky-price model: the eigenvalue, not `φ` (new) -/

namespace Fisherian

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Ch. 12, p. 328, and Ch. 17, (17.1)–(17.2) without the `E_tx_{t+1}` term:
the Fisherian sticky-price model `x_t = −σ(i_t − E_tπ_{t+1})`, `π_t = βE_tπ_{t+1} + κx_t` with
the rule `i_t = φπ_t + u_t`. -/
def RuleModel (σ β κ φ : ℝ) (u x i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = -σ • (i t - 𝔼.E t (π (t + 1))) ∧ π t = β • 𝔼.E t (π (t + 1)) + κ • x t ∧
    i t = φ • π t + u t

/-- Cochrane (2023), Ch. 12, p. 328: the eigenvalue `λ = (1 + σκφ)/(β + σκ)` of
`E_tπ_{t+1} = λπ_t + …` in the Fisherian sticky-price model with `i = φπ + u`. -/
noncomputable def lam (σ β κ φ : ℝ) : ℝ := (1 + σ * κ * φ) / (β + σ * κ)

/-- Cochrane (2023), Ch. 12, p. 328 ("what matters, here, is the `φ` in `E_tπ_{t+1} = φπ_t`"):
for `β + σκ ≠ 0`, inflation is part of an equilibrium of `Fisherian.RuleModel` iff
`E_tπ_{t+1} = λπ_t + (σκ/(β + σκ))u_t`, i.e. (16.4) with coefficient `λ`. -/
theorem rule_iff {σ β κ φ : ℝ} (h : β + σ * κ ≠ 0) (u π : ℕ → Ω → ℝ) :
    (∃ x i, RuleModel 𝔼 σ β κ φ u x i π) ↔
      SimplestModel.Eq164 𝔼 (lam σ β κ φ) ((σ * κ / (β + σ * κ)) • u) π := by
  constructor
  · rintro ⟨x, i, hm⟩ t
    obtain ⟨h1, h2, h3⟩ := hm t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    have e3 := congrFun h3 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
    simp only [lam]
    field_simp
    rw [e3] at e1
    rw [e1] at e2
    linear_combination (-1 : ℝ) * e2
  · intro he
    refine ⟨fun t => -σ • ((φ • π t + u t) - 𝔼.E t (π (t + 1))), fun t => φ • π t + u t,
      fun t => ⟨rfl, ?_, rfl⟩⟩
    funext ω
    have e := congrFun (he t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lam] at e ⊢
    rw [e]
    field_simp
    ring

/-- Cochrane (2023), §16.1, p. 364: scaling a bounded adapted disturbance by a constant keeps it
bounded and adapted. -/
theorem smul_bounded_adapted {u : ℕ → Ω → ℝ} (hb : BoundedProc u) (ha : 𝔼.Adapted u) (c : ℝ) :
    BoundedProc (c • u) ∧ 𝔼.Adapted (c • u) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨⟨|c| * M, fun t ω => ?_⟩, fun t => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)
  · simp only [Pi.smul_apply]
    rw [𝔼.E_smul, ha t]

/-- Cochrane (2023), §16.1, p. 364: if `c ≠ 0`, (16.4) with coefficient `λ` is determinate for
the disturbances `c u` iff it is determinate for the disturbances `u`, so iff `|λ| > 1`
(`SimplestModel.determinate_iff`). -/
theorem scaled_determinate_iff [Nonempty Ω] {c : ℝ} (hc : c ≠ 0) (lam : ℝ) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ SimplestModel.Eq164 𝔼 lam (c • u) π) ↔ 1 < |lam| := by
  rw [← SimplestModel.determinate_iff 𝔼 lam]
  constructor
  · intro h u hb ha
    obtain ⟨hb', ha'⟩ := smul_bounded_adapted 𝔼 hb ha c⁻¹
    have := h (c⁻¹ • u) hb' ha'
    rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at this
  · intro h u hb ha
    obtain ⟨hb', ha'⟩ := smul_bounded_adapted 𝔼 hb ha c
    exact h (c • u) hb' ha'

/-- Cochrane (2023), Ch. 16, p. 369, and Ch. 12, p. 328: for `σκ ≠ 0` and `β + σκ ≠ 0`, the
Fisherian sticky-price model with `i = φπ + u` has exactly one bounded equilibrium for every
bounded adapted disturbance iff `|λ| = |(1 + σκφ)/(β + σκ)| > 1`. -/
theorem rule_determinate_iff [Nonempty Ω] {σ β κ φ : ℝ} (hσκ : σ * κ ≠ 0)
    (h : β + σ * κ ≠ 0) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ ∃ x i, RuleModel 𝔼 σ β κ φ u x i π) ↔ 1 < |lam σ β κ φ| := by
  rw [← scaled_determinate_iff 𝔼 (div_ne_zero hσκ h) (lam σ β κ φ)]
  simp_rw [rule_iff 𝔼 h]

/-- Cochrane (2023), Ch. 16, p. 369: "`φ > 1` is not necessary": for `σκ > 0` and `0 < β < 1`,
every `φ > 1 − (1 − β)/(σκ)` gives an explosive eigenvalue `λ > 1`, including
`φ ∈ (1 − (1 − β)/(σκ), 1)`. -/
theorem not_necessary {σ β κ φ : ℝ} (hσκ : 0 < σ * κ) (hβ : 0 < β)
    (hφ : 1 - (1 - β) / (σ * κ) < φ) : 1 < |lam σ β κ φ| := by
  have hd : 0 < β + σ * κ := by linarith
  have h0 : (1 - β) / (σ * κ) * (σ * κ) = 1 - β := div_mul_cancel₀ _ hσκ.ne'
  have h1 : (1 - φ) * (σ * κ) < (1 - β) / (σ * κ) * (σ * κ) :=
    mul_lt_mul_of_pos_right (by linarith) hσκ
  have hl : 1 < lam σ β κ φ := by
    rw [lam, one_lt_div hd]
    nlinarith
  exact hl.trans_le (le_abs_self _)

/-- Cochrane (2023), Ch. 16, p. 369, witness: with `σ = κ = 1`, `β = 1/2`, the passive rule
`i = (3/4)π + u` is determinate (`λ = 7/6`). -/
theorem not_necessary_witness [Nonempty Ω] :
    ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ ∃ x i, RuleModel 𝔼 1 (1 / 2) 1 (3 / 4) u x i π :=
  (rule_determinate_iff 𝔼 (by norm_num) (by norm_num)).mpr (by norm_num [lam, abs_of_pos])

/-- Cochrane (2023), Ch. 16, p. 369: the Fisherian sticky-price model with the forecast rule
`i_t = φE_tπ_{t+1} + u_t`. -/
def FwdModel (σ β κ φ : ℝ) (u x i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = -σ • (i t - 𝔼.E t (π (t + 1))) ∧ π t = β • 𝔼.E t (π (t + 1)) + κ • x t ∧
    i t = φ • 𝔼.E t (π (t + 1)) + u t

/-- Cochrane (2023), Ch. 16, p. 369: `μ = β − σκ(φ − 1)`, so that `π_t = μE_tπ_{t+1} − σκu_t`
under the forecast rule. -/
def mu (σ β κ φ : ℝ) : ℝ := β - σ * κ * (φ - 1)

/-- Cochrane (2023), Ch. 16, p. 369: for `μ ≠ 0`, inflation is part of an equilibrium of the
forecast-rule model iff `E_tπ_{t+1} = μ⁻¹π_t + (σκ/μ)u_t`: the eigenvalue is `1/μ`. -/
theorem fwd_iff {σ β κ φ : ℝ} (h : mu σ β κ φ ≠ 0) (u π : ℕ → Ω → ℝ) :
    (∃ x i, FwdModel 𝔼 σ β κ φ u x i π) ↔
      SimplestModel.Eq164 𝔼 (mu σ β κ φ)⁻¹ ((σ * κ / mu σ β κ φ) • u) π := by
  have h' : β - σ * κ * (φ - 1) ≠ 0 := h
  constructor
  · rintro ⟨x, i, hm⟩ t
    obtain ⟨h1, h2, h3⟩ := hm t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    have e3 := congrFun h3 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
    rw [e3] at e1
    rw [e1] at e2
    have key : π t ω = (β - σ * κ * (φ - 1)) * 𝔼.E t (π (t + 1)) ω - σ * κ * u t ω := by
      rw [e2]; ring
    simp only [mu]
    rw [key]
    field_simp
    ring
  · intro he
    refine ⟨fun t => -σ • ((φ • 𝔼.E t (π (t + 1)) + u t) - 𝔼.E t (π (t + 1))),
      fun t => φ • 𝔼.E t (π (t + 1)) + u t, fun t => ⟨rfl, ?_, rfl⟩⟩
    funext ω
    have e := congrFun (he t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mu] at e ⊢
    rw [e]
    field_simp
    ring

/-- Cochrane (2023), Ch. 16, p. 369: for `σκ ≠ 0` and `μ ≠ 0`, the forecast-rule model is
determinate iff `|1/μ| > 1`. -/
theorem fwd_determinate_iff [Nonempty Ω] {σ β κ φ : ℝ} (hσκ : σ * κ ≠ 0)
    (h : mu σ β κ φ ≠ 0) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ ∃ x i, FwdModel 𝔼 σ β κ φ u x i π) ↔ 1 < |(mu σ β κ φ)⁻¹| := by
  rw [← scaled_determinate_iff 𝔼 (div_ne_zero hσκ h) (mu σ β κ φ)⁻¹]
  simp_rw [fwd_iff 𝔼 h]

/-- Cochrane (2023), Ch. 16, p. 369: "`φ > 1` is not sufficient": for `σκ > 0` and `β ≥ 0`,
every `φ > 1 + (1 + β)/(σκ)` (all of which exceed `1`) makes the forecast-rule model
indeterminate (`|1/μ| < 1`). -/
theorem not_sufficient [Nonempty Ω] {σ β κ φ : ℝ} (hσκ : 0 < σ * κ) (hβ : 0 ≤ β)
    (hφ : 1 + (1 + β) / (σ * κ) < φ) :
    1 < φ ∧ ¬ ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ ∃ x i, FwdModel 𝔼 σ β κ φ u x i π := by
  have hq : 0 < (1 + β) / (σ * κ) := by positivity
  have hm : mu σ β κ φ < -1 := by
    have := (div_lt_iff₀ hσκ).mp (by linarith : (1 + β) / (σ * κ) < φ - 1)
    simp only [mu]
    nlinarith
  refine ⟨by linarith, ?_⟩
  rw [fwd_determinate_iff 𝔼 hσκ.ne' (by linarith), not_lt, abs_inv,
    inv_le_one₀ (abs_pos.mpr (by linarith))]
  rw [abs_of_neg (by linarith)]
  linarith

/-- Cochrane (2023), Ch. 16, p. 369, witness: with `σ = κ = 1`, `β = 1/2`, the forecast rule
`i = 3E_tπ_{t+1} + u` (`φ = 3 > 1`) is indeterminate (`μ = −3/2`). -/
theorem not_sufficient_witness [Nonempty Ω] :
    ¬ ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ ∃ x i, FwdModel 𝔼 1 (1 / 2) 1 3 u x i π :=
  (not_sufficient 𝔼 (by norm_num) (by norm_num) (by norm_num)).2

/-- Cochrane (2023), Ch. 16, p. 369, and Ch. 12, p. 328 (P8), both halves at once in sticky-price
models: a reaction of interest rates to inflation below one-for-one can give the explosive
eigenvalue (determinacy) and one above one-for-one can fail to. -/
theorem p369 [Nonempty Ω] :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ ∃ x i, RuleModel 𝔼 1 (1 / 2) 1 (3 / 4) u x i π) ∧
    ¬ (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! π, BoundedProc π ∧ ∃ x i, FwdModel 𝔼 1 (1 / 2) 1 3 u x i π) :=
  ⟨not_necessary_witness 𝔼, not_sufficient_witness 𝔼⟩

end Fisherian

/-! ## Friedman's spiral (new) -/

namespace Friedman

open Adaptive

variable {Ω : Type*}

/-- Cochrane (2023), Ch. 12, pp. 324–325 (P1), Friedman's spiral: under adaptive expectations
(17.6) with `σκ > 0`, a peg below inflation (`ī < π_{−1}`, a too-low real rate) makes inflation
rise strictly every period and without bound. -/
theorem spiral_up {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) {ω : Ω} (hlow : ib < π0 ω) :
    StrictMono (fun t => π t ω) ∧ Tendsto (fun t => π t ω) atTop atTop := by
  have hd : 0 < π0 ω - ib := by linarith
  have hb : 1 < 1 + σ * κ := by linarith
  have e : (fun t => π t ω) = fun t => ib + (1 + σ * κ) ^ (t + 1) * (π0 ω - ib) :=
    funext fun t => adaptive_peg h t ω
  rw [e]
  refine ⟨fun s t hst => ?_, ?_⟩
  · have := mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hb (Nat.succ_lt_succ hst)) hd
    simp only [Nat.succ_eq_add_one] at this ⊢
    linarith
  · refine tendsto_atTop_add_const_left _ _ (Tendsto.atTop_mul_const hd ?_)
    exact (tendsto_pow_atTop_atTop_of_one_lt hb).comp (tendsto_add_atTop_nat 1)

/-- Cochrane (2023), Ch. 12, p. 325 ("These views predict an uncontrollable deflation spiral when
interest rates are effectively pegged by the zero bound"): under adaptive expectations a peg
above inflation (`ī > π_{−1}`) makes inflation fall strictly every period without bound. -/
theorem spiral_down {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) {ω : Ω} (hhigh : π0 ω < ib) :
    StrictAnti (fun t => π t ω) ∧ Tendsto (fun t => π t ω) atTop atBot := by
  have hd : 0 < ib - π0 ω := by linarith
  have hb : 1 < 1 + σ * κ := by linarith
  have e : (fun t => π t ω) = fun t => ib - (1 + σ * κ) ^ (t + 1) * (ib - π0 ω) :=
    funext fun t => by rw [adaptive_peg h t ω]; ring
  rw [e]
  refine ⟨fun s t hst => ?_, ?_⟩
  · have := mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hb (Nat.succ_lt_succ hst)) hd
    simp only [Nat.succ_eq_add_one] at this ⊢
    linarith
  · have := (tendsto_pow_atTop_atTop_of_one_lt hb).comp (tendsto_add_atTop_nat 1)
    have h2 := Tendsto.atTop_mul_const hd this
    exact tendsto_atBot_add_const_left _ ib (tendsto_neg_atTop_atBot.comp h2) |>.congr
      fun t => by simp only [Function.comp_apply]; ring

/-- Cochrane (2023), Ch. 12, p. 325 ("Under rational expectations … If the central bank pegs the
interest rate `i`, then `E_tπ_{t+1}` settles down to `i − r` all on its own"), in the same
sticky-price model (17.7) with `σκ > 0`: under a peg `ī`, expected inflation converges to the
peg, `E_0π_t = ī + (1 + σκ)^{−t}(π_0 − ī) → ī`. The spiral of `Friedman.spiral_up` comes from
adaptive
expectations. -/
theorem re_peg_stable (𝔼 : ExpectationSystem Ω) {σ κ ib : ℝ} (hσκ : 0 < σ * κ)
    {π : ℕ → Ω → ℝ} (h : REModel 𝔼 σ κ (fun _ _ => ib) π) (ω : Ω) :
    (∀ t, 𝔼.E 0 (π t) ω = ib + ((1 + σ * κ)⁻¹) ^ t * (π 0 ω - ib)) ∧
      Tendsto (fun t => 𝔼.E 0 (π t) ω) atTop (𝓝 ib) := by
  have hd : 0 < 1 + σ * κ := by linarith
  have h17 := ((reModel_iff_17_7 𝔼 hd.ne' (fun _ _ => ib) π).mp h).2
  have hstep : ∀ t, 𝔼.E 0 (π (t + 1)) ω =
      (1 + σ * κ)⁻¹ * 𝔼.E 0 (π t) ω + σ * κ / (1 + σ * κ) * ib := by
    intro t
    have hf : 𝔼.E t (π (t + 1)) =
        (1 / (1 + σ * κ)) • π t + (fun _ => σ * κ / (1 + σ * κ) * ib) := by
      funext ω'
      rw [h17 t ω']
      simp
    have := congrArg (fun f => 𝔼.E 0 f ω) hf
    simp only [𝔼.tower (Nat.zero_le t), map_add, map_smul, 𝔼.const, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    ring
  have hclosed : ∀ t, 𝔼.E 0 (π t) ω = ib + ((1 + σ * κ)⁻¹) ^ t * (π 0 ω - ib) := by
    intro t
    induction t with
    | zero =>
      rw [h.1 0]
      ring
    | succ n ih =>
      rw [hstep n, ih, pow_succ]
      field_simp
      ring
  refine ⟨hclosed, ?_⟩
  have hq : (1 + σ * κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hq0 : 0 ≤ (1 + σ * κ)⁻¹ := (inv_pos.mpr hd).le
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const (π 0 ω - ib)).const_add ib
  simp only [zero_mul, add_zero] at this
  exact this.congr fun t => (hclosed t).symm

end Friedman

end Cochrane.NewKeynesianSelection.TidyR6StickyPrices
