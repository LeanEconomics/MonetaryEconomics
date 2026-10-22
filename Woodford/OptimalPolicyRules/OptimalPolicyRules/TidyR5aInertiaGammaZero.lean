/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaProp82Complex
import OptimalPolicyRules.NKAssumption81

/-!
# The inflation-inertia model at `γ = 0`: Assumption 8.1 and Proposition 8.2

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541), Proposition 8.2
(p. 555), for the inflation-inertia model of §3.2 (pp. 592–604; `GeneralLinksInertia.inProblem`)
at the boundary `γ = 0` of the book's range `0 ≤ γ ≤ 1` (p. 592).

For `0 < γ ≤ 1` both are proved through the Blanchard–Kahn form of the first-order system
(`InertiaAssumption81.in_assumption81MB`, `InertiaProp82Complex.in_prop82_all_B`), whose lead
matrix has `det P = −β²γ/λₓ` (`InertiaFOCSystem.det_Pm`); at `γ = 0` it is singular
(`det_Pm_gamma_zero`), and that route is closed.

## The reduction

At `γ = 0` the predetermined variable `Z_t = π_{t−1}` enters neither the constraints' forward
block nor the loss. The row of (1.9) for `Z` gives `ξ_t = 0` from `t₀` on, so `E_tξ_{t+1} = 0`, and
the remaining rows of (1.1) + (1.9) are exactly those of the basic model
(`GeneralLinks.nkProblem`, `n_Z = 0`); `Z` is then read off `Z_{t₀} = Z₀`, `Z_{t+1} = π_t`.

* `focSystem0_iff`: **the reduction** — `(y, φ)` solves (1.1) + (1.9) for `inProblem` at `γ = 0`
  iff `ξ_t = 0` from `t₀` on, `Z` follows `Z_{t₀} = Z₀`, `Z_{t+1} = π_t`, and the projection
  `(toNK y, toNKφ φ)` solves (1.1) + (1.9) for the basic model.
* `in0_focUnique`, `in0_focSolvableMB`, `in0_assumption81MB`: **Assumption 8.1 holds at `γ = 0`**
  (bounded initial conditions, every expectation system, every `t₀`), from
  `NKAssumption81.NK.nk_focUnique` and `NKAssumption81.NK.nk_focSolvableM`;
  `in0_assumption81M_of_finite`, `in0_assumption81_perfectForesight`.
* `in0Split`: at `γ = 0` the zero root of (1.15) gives a deflating split with `J = (1, 0, 0)'`,
  `Ψ = [0]`, `K = A₂₂'` (`det K = 1`); `in0_assumption85`: Assumption 8.5 holds.
* `in0_prop82_B`, `in0_prop82_finite`: **Proposition 8.2 holds at `γ = 0`**.
* `in_assumption81MB_all`, `in_prop82_all_B'`, `in_prop82_all_finite'`: Assumption 8.1 and
  Proposition 8.2 for **every** `0 ≤ γ ≤ 1`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5aInertiaGammaZero

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ PencilSplit
open IRuleBasic (Calib)
open GeneralLinks (piOf xOf iOf nkSys nkProblem nkPhi1 nkPhi2)
open GeneralLinksInertia (inSys inProblem in_det_ne Zof Xi1 Xi2)
open InertiaAssumption81 (Assumption81MB FOCSolvableMB RobustlyOptimalB)

variable {Ω : Type*} (c : Calib)

/-- Woodford (2003), §3.2: at `γ = 0` the lead matrix of the second-order form of the first-order
system is singular, `det P = 0` (`InertiaFOCSystem.det_Pm`), so the Blanchard–Kahn route of
`InertiaAssumption81` does not apply. -/
theorem det_Pm_gamma_zero (hlx : c.lx ≠ 0) : (InertiaFOCSystem.Pm c 0).det = 0 := by
  rw [InertiaFOCSystem.det_Pm c 0 hlx]
  simp

/-! ### Projection to the basic model and back -/

/-- Woodford (2003), §3.1–3.2 (tool): the projection of a plan `y = (Z, π, x, i)` of the inertia
model onto the plan `(π, x, i)` of the basic model (`n_Z = 0`). -/
def toNK (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ :=
  fun t ω v => y t ω (Sum.map (Sum.map (fun e => e.elim) id) id v)

/-- Woodford (2003), §3.1–3.2 (tool): the projection of the multipliers `φ = (ξ, M)` onto the
multipliers `M` of the basic model. -/
def toNKφ (φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ) : ℕ → Ω → Empty ⊕ Fin 2 → ℝ :=
  fun t ω v => φ t ω (Sum.map (fun e => e.elim) id v)

/-- Woodford (2003), §3.2 (tool): a plan of the basic model extended by the predetermined
`Z_{t₀} = Z₀`, `Z_t = π_{t−1}` (`t ≠ t₀`). -/
def ofNK (t0 : ℕ) (Z0 : Ω → Unit → ℝ) (yN : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) :
    ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ :=
  fun t ω => Sum.elim (Sum.elim (fun _ => if t = t0 then Z0 ω () else yN (t - 1) ω
    (Sum.inl (Sum.inr 0))) (fun j => yN t ω (Sum.inl (Sum.inr j)))) (fun _ => yN t ω (Sum.inr ()))

/-- Woodford (2003), §3.2 (tool): multipliers of the basic model extended by `ξ = 0`. -/
def ofNKφ (φN : ℕ → Ω → Empty ⊕ Fin 2 → ℝ) : ℕ → Ω → Unit ⊕ Fin 2 → ℝ :=
  fun t ω => Sum.elim (fun _ => 0) (fun j => φN t ω (Sum.inr j))

/-- Woodford (2003), §3.2 (tool): projecting an extended plan gives the plan back. -/
theorem toNK_ofNK (t0 : ℕ) (Z0 : Ω → Unit → ℝ) (yN : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) :
    toNK (ofNK t0 Z0 yN) = yN := by
  funext t ω v
  rcases v with (e | j) | u
  · exact e.elim
  · rfl
  · rfl

/-- Woodford (2003), §3.2 (tool): projecting extended multipliers gives them back. -/
theorem toNKφ_ofNKφ (φN : ℕ → Ω → Empty ⊕ Fin 2 → ℝ) : toNKφ (ofNKφ φN) = φN := by
  funext t ω v
  rcases v with e | j
  · exact e.elim
  · rfl

/-! ### The structural equations -/

/-- Woodford (2003), (2.6) and (3.1) at `γ = 0` as (1.1), at one date: the rows of `inSys` are
`Z_{t+1} = π_t` together with the rows of the basic model's `nkSys`. -/
theorem struct0_at (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (cc : ℕ → Ω → Fin 2 → ℝ)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) :
    (Zpart (y (t + 1) ω) = (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).A11 *ᵥ
        Zpart (y t ω) + (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).A12 *ᵥ zpart (y t ω) ∧
      (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).Et *ᵥ
          EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω =
        (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).A21 *ᵥ Zpart (y t ω) +
          (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).A22 *ᵥ zpart (y t ω) +
          ipart (y t ω) • (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).B2 + cc t ω) ↔
    (Zof y (t + 1) ω = piOf y t ω ∧
      (Zpart (toNK y (t + 1) ω) = (nkSys c hc.2.2.1.ne').A11 *ᵥ Zpart (toNK y t ω) +
          (nkSys c hc.2.2.1.ne').A12 *ᵥ zpart (toNK y t ω) ∧
        (nkSys c hc.2.2.1.ne').Et *ᵥ EV 𝔼 t (fun ω' => zpart (toNK y (t + 1) ω')) ω =
          (nkSys c hc.2.2.1.ne').A21 *ᵥ Zpart (toNK y t ω) +
            (nkSys c hc.2.2.1.ne').A22 *ᵥ zpart (toNK y t ω) +
            ipart (toNK y t ω) • (nkSys c hc.2.2.1.ne').B2 + cc t ω)) := by
  have hZN : Zpart (toNK y (t + 1) ω) = (nkSys c hc.2.2.1.ne').A11 *ᵥ Zpart (toNK y t ω) +
      (nkSys c hc.2.2.1.ne').A12 *ᵥ zpart (toNK y t ω) := funext fun e => e.elim
  rw [NKAssumption81.NK.nk_struct_at c hc.2.2.1.ne' 𝔼 cc (toNK y) t ω]
  rw [funext_iff, funext_iff, Fin.forall_fin_two]
  simp only [inSys, mulVec, dotProduct, Fin.sum_univ_two, EV, zpart, Zpart, ipart, Zof, piOf,
    xOf, iOf, toNK, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.zero_apply, Fintype.univ_punit, Finset.sum_singleton,
    Fin.isValue, ↓reduceIte, one_ne_zero, Sum.map_inl, Sum.map_inr, id_eq,
    GeneralLinks.piOf_eq, GeneralLinks.xOf_eq, mul_zero, zero_mul, add_zero, zero_add, neg_zero,
    one_mul]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by linarith [h0 ()], hZN, by linarith, by linarith⟩
  · rintro ⟨h0, -, h1, h2⟩
    exact ⟨fun _ => by linarith, by linarith, by linarith⟩

/-! ### The first-order conditions -/

/-- Woodford (2003), (1.9) at `γ = 0`, at one date, pp. 541, 584 and 592: given
`E_tξ_{t+1} = 0`, the four rows of (1.9) for `inProblem` are `ξ_t = 0` together with the three
rows (3.3)–(3.5) of the basic model for the projected plan and multipliers. -/
theorem foc0_at (hc : c.Adm) (𝔼 : ExpectationSystem Ω)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) (t : ℕ) (ω : Ω)
    (hE : 𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω = 0) :
    ((inProblem c 0 hc le_rfl).sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
      (inProblem c 0 hc le_rfl).Tᵀ *ᵥ ((inProblem c 0 hc le_rfl).W *ᵥ
        ((inProblem c 0 hc le_rfl).T *ᵥ y t ω - (inProblem c 0 hc le_rfl).τstar)) -
      (inProblem c 0 hc le_rfl).β⁻¹ • ((inProblem c 0 hc le_rfl).sys.Itilᵀ *ᵥ φ t ω) = 0) ↔
    (φ t ω (Sum.inl ()) = 0 ∧
      (nkProblem c hc).sys.Atilᵀ *ᵥ EV 𝔼 t (toNKφ φ (t + 1)) ω +
        (nkProblem c hc).Tᵀ *ᵥ ((nkProblem c hc).W *ᵥ
          ((nkProblem c hc).T *ᵥ toNK y t ω - (nkProblem c hc).τstar)) -
        (nkProblem c hc).β⁻¹ • ((nkProblem c hc).sys.Itilᵀ *ᵥ toNKφ φ t ω) = 0) := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hmN : MultiplierMeas 𝔼 (toNKφ φ) := fun s r => hmφ s r
  rw [GeneralLinksInertia.in_foc_at_iff c 0 hc le_rfl 𝔼 y hmφ t ω,
    GeneralLinks.nk_foc_at_iff c hc 𝔼 (toNK y) hmN t ω, hE]
  simp only [Xi1, Xi2, nkPhi1, nkPhi2, piOf, xOf, iOf, toNK, toNKφ, Sum.map_inl, Sum.map_inr,
    id_eq, zero_mul, neg_zero, mul_zero, sub_zero, zero_sub, add_zero, zero_add]
  have e1 : ∀ a b : ℝ, c.β⁻¹ * (c.β * a + c.σ * b) = a + c.σ / c.β * b := by
    intro a b
    field_simp
  rw [e1]
  have hinv : c.β⁻¹ ≠ 0 := inv_ne_zero hβ
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨?_, by linarith, by linarith, by linarith⟩
    have : c.β⁻¹ * φ t ω (Sum.inl ()) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hinv
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨by rw [h0]; ring, by linarith, by linarith, by linarith⟩

/-- Woodford (2003), (1.9) at `γ = 0` (tool): along multipliers whose `ξ`-block vanishes from
`t₀ + 1` on, `E_tξ_{t+1} = 0` for `t ≥ t₀`. -/
theorem E_xi_zero (𝔼 : ExpectationSystem Ω) {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ} {t0 : ℕ}
    (hξ : ∀ s, t0 + 1 ≤ s → ∀ ω, φ s ω (Sum.inl ()) = 0) (t : ℕ) (ht : t0 ≤ t) (ω : Ω) :
    𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω = 0 := by
  have e : (fun ω' => φ (t + 1) ω' (Sum.inl ())) = fun _ => (0 : ℝ) :=
    funext fun ω' => hξ (t + 1) (by omega) ω'
  rw [e, 𝔼.const]

/-- **Woodford (2003), (1.9) at `γ = 0`, pp. 541 and 592.** Along multipliers with `M_t` known at
`t`, the first-order conditions (1.9) of `inProblem` from `t₀` on hold iff `ξ_t = 0` from `t₀` on
and the projected plan and multipliers satisfy the basic model's first-order conditions. -/
theorem pfoc0_iff (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) :
    PFOC (inProblem c 0 hc le_rfl) 𝔼 t0 y φ ↔
      (∀ t, t0 ≤ t → ∀ ω, φ t ω (Sum.inl ()) = 0) ∧
        PFOC (nkProblem c hc) 𝔼 t0 (toNK y) (toNKφ φ) := by
  constructor
  · intro h
    have hξ : ∀ t, t0 ≤ t → ∀ ω, φ t ω (Sum.inl ()) = 0 := by
      intro t ht ω
      have hξ' : ∀ s, t0 ≤ s → ∀ ω, φ s ω (Sum.inl ()) = 0 →
          φ s ω (Sum.inl ()) = 0 := fun _ _ _ h => h
      have key := GeneralLinksInertia.in_foc_at_iff c 0 hc le_rfl 𝔼 y hmφ t ω
      have h0 := (key.mp (h t ht ω)).1
      simp only [zero_mul, neg_zero, sub_zero, zero_sub, neg_eq_zero, mul_eq_zero,
        inv_eq_zero] at h0
      exact hξ' t ht ω (h0.resolve_left hc.1.ne')
    refine ⟨hξ, fun t ht ω => ?_⟩
    exact ((foc0_at c hc 𝔼 y hmφ t ω
      (E_xi_zero 𝔼 (fun s hs ω => hξ s (by omega) ω) t ht ω)).mp (h t ht ω)).2
  · rintro ⟨hξ, h⟩ t ht ω
    exact (foc0_at c hc 𝔼 y hmφ t ω
      (E_xi_zero 𝔼 (fun s hs ω => hξ s (by omega) ω) t ht ω)).mpr ⟨hξ t ht ω, h t ht ω⟩

/-! ### The reduction -/

/-- **Woodford (2003), (1.1) + (1.9) at `γ = 0`, pp. 537–541 and 592: the reduction to the basic
model.** `(y, φ)` solves the first-order system of `inProblem` at `γ = 0` with initial conditions
`Z₀`, `M₀` iff `Z` starts at `Z₀` and follows `Z_{t+1} = π_t`, `y` and `φ` are bounded and adapted,
`ξ_t = 0` from `t₀` on, and the projection `(toNK y, toNKφ φ)` solves the first-order system of
the basic model (`n_Z = 0`) with the same `M₀`. -/
theorem focSystem0_iff (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (cc : ℕ → Ω → Fin 2 → ℝ)
    (t0 : ℕ) (Z0 : Ω → Unit → ℝ) (M0 : Ω → Fin 2 → ℝ)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) (φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ) :
    FOCSystem (inProblem c 0 hc le_rfl) 𝔼 cc t0 Z0 M0 y φ ↔
      ((∀ ω, Zpart (y t0 ω) = Z0 ω) ∧ (∀ t, t0 ≤ t → ∀ ω, Zof y (t + 1) ω = piOf y t ω) ∧
        BoundedV y ∧ AdaptedV 𝔼 y ∧ BoundedV φ ∧ MultiplierMeas 𝔼 φ ∧
        (∀ t, t0 ≤ t → ∀ ω, φ t ω (Sum.inl ()) = 0)) ∧
      FOCSystem (nkProblem c hc) 𝔼 cc t0 (fun _ e => e.elim) M0 (toNK y) (toNKφ φ) := by
  have hstr : (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).Structural 𝔼 cc t0 y ↔
      (∀ t, t0 ≤ t → ∀ ω, Zof y (t + 1) ω = piOf y t ω) ∧
        (nkSys c hc.2.2.1.ne').Structural 𝔼 cc t0 (toNK y) := by
    constructor
    · intro h
      exact ⟨fun t ht ω => ((struct0_at c hc 𝔼 cc y t ω).mp (h t ht ω)).1,
        fun t ht ω => ((struct0_at c hc 𝔼 cc y t ω).mp (h t ht ω)).2⟩
    · rintro ⟨h1, h2⟩ t ht ω
      exact (struct0_at c hc 𝔼 cc y t ω).mpr ⟨h1 t ht ω, h2 t ht ω⟩
  have hbN : BoundedV y → BoundedV (toNK y) := by
    rintro ⟨K, hK⟩
    exact ⟨K, fun t ω v => hK t ω _⟩
  have haN : AdaptedV 𝔼 y → AdaptedV 𝔼 (toNK y) := fun h t v => h t _
  have hφN : BoundedV φ → BoundedV (toNKφ φ) := by
    rintro ⟨K, hK⟩
    exact ⟨K, fun t ω v => hK t ω _⟩
  constructor
  · rintro ⟨⟨hs, hZ0, hyb, hya⟩, hφb, hmφ, hM0, hfoc⟩
    obtain ⟨hZ, hsN⟩ := hstr.mp hs
    obtain ⟨hξ, hfocN⟩ := (pfoc0_iff c hc 𝔼 t0 y hmφ).mp hfoc
    exact ⟨⟨hZ0, hZ, hyb, hya, hφb, hmφ, hξ⟩,
      ⟨hsN, fun ω => funext fun e => e.elim, hbN hyb, haN hya⟩, hφN hφb, fun s r => hmφ s r,
      hM0, hfocN⟩
  · rintro ⟨⟨hZ0, hZ, hyb, hya, hφb, hmφ, hξ⟩, ⟨hsN, -, -, -⟩, -, -, hM0, hfocN⟩
    exact ⟨⟨hstr.mpr ⟨hZ, hsN⟩, hZ0, hyb, hya⟩, hφb, hmφ, hM0,
      (pfoc0_iff c hc 𝔼 t0 y hmφ).mpr ⟨hξ, hfocN⟩⟩

/-! ### Assumption 8.1 at `γ = 0` -/

/-- **Woodford (2003), Assumption 8.1 (uniqueness), p. 541, for the inflation-inertia model at
`γ = 0`**: two bounded solutions of (1.1) + (1.9) with the same disturbance and initial conditions
coincide from `t₀` on (any expectation system), by the reduction `focSystem0_iff` and the basic
model's uniqueness `NKAssumption81.NK.nk_focUnique`. -/
theorem in0_focUnique (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    FOCUnique (inProblem c 0 hc le_rfl) 𝔼 t0 := by
  intro cc Z0 M0 y y' φ φ' hs hs'
  obtain ⟨⟨hZ0, hZ, -, -, -, -, hξ⟩, hN⟩ := (focSystem0_iff c hc 𝔼 cc t0 Z0 M0 y φ).mp hs
  obtain ⟨⟨hZ0', hZ', -, -, -, -, hξ'⟩, hN'⟩ := (focSystem0_iff c hc 𝔼 cc t0 Z0 M0 y' φ').mp hs'
  have hU := NKAssumption81.NK.nk_focUnique c hc 𝔼 t0 cc _ M0 _ _ _ _ hN hN'
  intro t ht
  refine ⟨funext fun ω => funext fun v => ?_, funext fun ω => funext fun v => ?_⟩
  · rcases v with (u | j) | u
    · rcases Nat.lt_or_ge t0 t with h | h
      · have e1 := hZ (t - 1) (by omega) ω
        have e2 := hZ' (t - 1) (by omega) ω
        rw [show t - 1 + 1 = t by omega] at e1 e2
        have e3 := congrFun (congrFun (hU (t - 1) (by omega)).1 ω) (Sum.inl (Sum.inr 0))
        change Zof y t ω = Zof y' t ω
        rw [e1, e2]
        exact e3
      · obtain rfl : t = t0 := le_antisymm h ht
        rw [Subsingleton.elim u ()]
        exact (congrFun (hZ0 ω) ()).trans (congrFun (hZ0' ω) ()).symm
    · exact congrFun (congrFun (hU t ht).1 ω) (Sum.inl (Sum.inr j))
    · exact congrFun (congrFun (hU t ht).1 ω) (Sum.inr u)
  · rcases v with u | j
    · rw [Subsingleton.elim u ()]
      rw [hξ t ht ω, hξ' t ht ω]
    · exact congrFun (congrFun (hU t ht).2 ω) (Sum.inr j)

/-- **Woodford (2003), Assumption 8.1 (existence), p. 541, for the inflation-inertia model at
`γ = 0`** (bounded initial conditions, `InertiaAssumption81.FOCSolvableMB`): the basic model's
bounded solution (`NKAssumption81.NK.nk_focSolvableM`) extended by `Z_{t₀} = Z₀`, `Z_{t+1} = π_t`
and `ξ = 0` (any expectation system, any `t₀`). -/
theorem in0_focSolvableMB (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    FOCSolvableMB (inProblem c 0 hc le_rfl) 𝔼 t0 := by
  intro cc Z0 M0 hcb hca hZk hZb hMb hMk
  obtain ⟨yN, φN, hN⟩ := NKAssumption81.NK.nk_focSolvableM c hc 𝔼 t0 cc (fun _ e => e.elim) M0
    hcb hca (fun e => e.elim) hMb hMk
  obtain ⟨⟨-, -, ⟨Ky, hKy⟩, hya⟩, ⟨Kφ, hKφ⟩, hmN, -, -⟩ := id hN
  obtain ⟨KZ, hKZ⟩ := hZb
  refine ⟨ofNK t0 Z0 yN, ofNKφ φN, (focSystem0_iff c hc 𝔼 cc t0 Z0 M0 _ _).mpr
    ⟨⟨fun ω => funext fun u => ?_, fun t ht ω => ?_, ⟨max Ky KZ, fun t ω v => ?_⟩,
      fun t v => ?_, ⟨max Kφ 0, fun t ω v => ?_⟩, fun s r => hmN s r,
      fun t _ ω => rfl⟩, ?_⟩⟩
  · rw [Subsingleton.elim u ()]
    simp [ofNK, Zpart]
  · simp [ofNK, Zof, piOf, show t + 1 ≠ t0 by omega]
  · rcases v with (u | j) | u
    · simp only [ofNK, Sum.elim_inl]
      split_ifs
      · exact (hKZ ω ()).trans (le_max_right _ _)
      · exact (hKy _ ω _).trans (le_max_left _ _)
    · exact (hKy t ω _).trans (le_max_left _ _)
    · exact (hKy t ω _).trans (le_max_left _ _)
  · rcases v with (u | j) | u
    · simp only [ofNK, Sum.elim_inl]
      split_ifs with h
      · subst h
        exact hZk ()
      · have e := hya (t - 1) (Sum.inl (Sum.inr 0))
        rw [← e, 𝔼.known (Nat.sub_le t 1)]
    · exact hya t (Sum.inl (Sum.inr j))
    · exact hya t (Sum.inr u)
  · rcases v with u | j
    · simp [ofNKφ]
    · exact (hKφ t ω _).trans (le_max_left _ _)
  · rw [toNK_ofNK, toNKφ_ofNKφ]
    exact hN

/-- **Woodford (2003), Assumption 8.1, p. 541, holds for the inflation-inertia model at `γ = 0`**
(bounded initial conditions): for every expectation system and every `t₀`, (1.1) + (1.9) has
exactly one bounded solution. -/
theorem in0_assumption81MB (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Assumption81MB (inProblem c 0 hc le_rfl) 𝔼 t0 :=
  ⟨in0_focSolvableMB c hc 𝔼 t0, in0_focUnique c hc 𝔼 t0⟩

/-- **Woodford (2003), Assumption 8.1, p. 541, at `γ = 0` on a finite sample space**: the
corrected `Prop82General.Assumption81M` (every `Z_{t₀}` is bounded there). -/
theorem in0_assumption81M_of_finite [Finite Ω] (hc : c.Adm) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : Prop82General.Assumption81M (inProblem c 0 hc le_rfl) 𝔼 t0 := by
  have := Fintype.ofFinite Ω
  refine ⟨fun cc Z0 M0 hb ha hZ hMb hMk => in0_focSolvableMB c hc 𝔼 t0 cc Z0 M0 hb ha hZ
    ⟨∑ ω, |Z0 ω ()|, fun ω u => ?_⟩ hMb hMk, in0_focUnique c hc 𝔼 t0⟩
  rw [Subsingleton.elim u ()]
  exact Finset.single_le_sum (f := fun ω => |Z0 ω ()|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ ω)

/-- **Woodford (2003), Assumption 8.1, p. 541, at `γ = 0` under perfect foresight**, in the
original formalisation `GeneralFOC.LQ.Assumption81`. -/
theorem in0_assumption81_perfectForesight (hc : c.Adm) (t0 : ℕ) :
    Assumption81 (inProblem c 0 hc le_rfl) perfectForesight t0 := by
  have hA := in0_assumption81M_of_finite c hc perfectForesight t0
  refine ⟨fun cc Z0 M0 hcb hca hZ0 _ => ?_, hA.unique⟩
  exact hA.solvable cc Z0 M0 hcb hca hZ0
    ⟨|M0 () 0| + |M0 () 1|, fun ω r => by
      rcases ω
      fin_cases r
      · simp
      · simp⟩ (fun _ => rfl)

/-! ### Proposition 8.2 at `γ = 0` -/

/-- Woodford (2003), App. G.1, (G.4), p. 717, at `γ = 0`: the zero root of (1.15)
(`det A = γ = 0`, `InertiaSplit.pR_zero`) gives a deflating split with `J = (1, 0, 0)'` and
`Ψ = [0]`; `J₁ = 1` and `K = A₂₂'` with `det K = 1`. -/
noncomputable def in0Split (hc : c.Adm) :
    DeflatingSplit (inProblem c 0 hc le_rfl).sys (inProblem c 0 hc le_rfl).β where
  J := InertiaSplit.inJ c 0
  Ψ := InertiaSplit.inPsi 0
  deflate := InertiaSplit.in_deflate c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)
    (InertiaSplit.pR_zero c 0) (by norm_num)
  eig_lt := by
    intro μ hμ
    have hdet : (Matrix.scalar Unit μ - (InertiaSplit.inPsi 0).map Complex.ofReal).det = μ := by
      rw [det_unique]
      simp [InertiaSplit.inPsi]
    rw [hdet] at hμ
    rw [hμ, norm_zero]
    exact inv_pos.mpr hc.1
  J1_det := by
    rw [InertiaSplit.in_J1]
    simp
  K_det := by
    change (Kmat (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)) (InertiaSplit.inJ c 0)).det ≠ 0
    rw [InertiaSplit.in_Kmat, det_fin_two_of]
    norm_num

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, at `γ = 0`**, for the split `in0Split`
(`InertiaProp82Complex.in_assumption85_gen`). -/
theorem in0_assumption85 (hc : c.Adm) :
    PencilAssumptions.Assumption85 (Λmat (inProblem c 0 hc le_rfl).sys c.β (in0Split c hc).J)
      (inProblem c 0 hc le_rfl).sys.B2 :=
  InertiaProp82Complex.in_assumption85_gen c 0 hc le_rfl _ (in0Split c hc).K_det

/-- Woodford (2003), p. 555 (tool): `rank Ẽ = 2` at `γ = 0`, so `rank Λ = 2`. -/
theorem in0_rank_Λ (hc : c.Adm) :
    (Λmat (inProblem c 0 hc le_rfl).sys c.β (in0Split c hc).J).rank = 2 := by
  rw [Prop81General.rank_Λmat (inProblem c 0 hc le_rfl).sys hc.1.ne' (in0Split c hc).K_det]
  change (inSys c 0 hc.2.2.1.ne' (in_det_ne c 0 hc le_rfl)).Et.rank = 2
  rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
  · simp
  · rw [InertiaSplit.in_Et_det]
    exact isUnit_iff_ne_zero.mpr hc.1.ne'

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at `γ = 0`, with
bounded initial conditions**: for any expectation system with pull-out, commitment to the target
criterion (1.23) built from `in0Split` (a window of `D ≥ 2` lags, any consistent bounded
history) determines a unique bounded equilibrium, optimal from a timeless perspective, for every
bounded adapted disturbance and every bounded initial condition (Assumption 8.1:
`in0_assumption81MB`; Assumption 8.5: `in0_assumption85`). -/
theorem in0_prop82_B {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm) (hpull : 𝔼.PullOut)
    {D : ℕ} (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK
      (Λmat (inProblem c 0 hc le_rfl).sys c.β (in0Split c hc).J)
      (inProblem c 0 hc le_rfl).sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimalB (κ := Fin 2) (inProblem c 0 hc le_rfl) 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 _ (in0Split c hc) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  have hrk : (Λmat (inProblem c 0 hc le_rfl).sys c.β (in0Split c hc).J).rank ≤ D := by
    rw [in0_rank_Λ c hc]
    exact hD2
  exact InertiaAssumption81.prop82M_robustlyOptimalB hpull (in0_assumption81MB c hc 𝔼 t0)
    (Prop81General.prop81 _ (in0Split c hc) 𝔼 t0) (in0_assumption85 c hc).2 hD1
    (fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk)
    ((Adjugate.natDegree_alpha_le_rank _).trans hrk) hhist hMhb hMhk hqhb hvhb

/-- **Woodford (2003), Proposition 8.2, p. 555, at `γ = 0`, on a finite sample space, in the
original robust-optimality sense** (every initial condition). -/
theorem in0_prop82_finite [Finite Ω] {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm)
    (hpull : 𝔼.PullOut) {D : ℕ} (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK
      (Λmat (inProblem c 0 hc le_rfl).sys c.β (in0Split c hc).J)
      (inProblem c 0 hc le_rfl).sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := Fin 2) (inProblem c 0 hc le_rfl) 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 _ (in0Split c hc) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  refine Prop82General.prop82_of_split hpull (in0_assumption81M_of_finite c hc 𝔼 t0) _
    (in0_assumption85 c hc).2 hD1 ?_ hhist hMhb hMhk hqhb hvhb
  have := in0_rank_Λ c hc
  rw [Prop81General.rank_Λmat (inProblem c 0 hc le_rfl).sys hc.1.ne' (in0Split c hc).K_det]
    at this
  rw [this]
  exact hD2

/-! ### Every `0 ≤ γ ≤ 1` -/

/-- **Woodford (2003), Assumption 8.1, p. 541, for the inflation-inertia model at every
`0 ≤ γ ≤ 1`** (bounded initial conditions, every expectation system, every `t₀`):
`InertiaAssumption81.in_assumption81MB` for `γ > 0` and `in0_assumption81MB` for `γ = 0`. -/
theorem in_assumption81MB_all (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Assumption81MB (inProblem c γ hc hγ0) 𝔼 t0 := by
  rcases hγ0.lt_or_eq with h | h
  · exact InertiaAssumption81.in_assumption81MB c γ hc h hγ1 𝔼 t0
  · subst h
    exact in0_assumption81MB c hc 𝔼 t0

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at every
`0 ≤ γ ≤ 1`, with bounded initial conditions**: for any expectation system with pull-out there is
a matrix set of the corrected Proposition 8.1 such that, for every window of `D ≥ 2` lags and
every consistent bounded history, commitment to the target criterion (1.23) is robustly optimal
(`InertiaProp82Complex.in_prop82_all_B` for `γ > 0`, `in0_prop82_B` for `γ = 0`). -/
theorem in_prop82_all_B' (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (hpull : 𝔼.PullOut) :
    ∃ H : Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0) 𝔼 t0,
      ∀ D, D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        TargetCriterion.Prop82.HistoryOK H.Λ (inProblem c γ hc hγ0).sys.B2 t0 D Mh qh vh →
        BoundedV Mh → AdaptedV 𝔼 Mh → BoundedV qh → (∃ K, ∀ t ω, |vh t ω| ≤ K) →
        RobustlyOptimalB (κ := Fin 2) (inProblem c γ hc hγ0) 𝔼 t0
          (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
          (fun _ y t ω => zpart (y t ω)) := by
  rcases hγ0.lt_or_eq with h | h
  · exact InertiaProp82Complex.in_prop82_all_B c γ hc h hγ1 𝔼 t0 hpull
  · subst h
    exact ⟨_, fun D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb =>
      in0_prop82_B c hc hpull hD1 hD2 hhist hMhb hMhk hqhb hvhb⟩

/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model at every
`0 ≤ γ ≤ 1`, on a finite sample space, in the original robust-optimality sense.** -/
theorem in_prop82_all_finite' [Finite Ω] (hc : c.Adm) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (hpull : 𝔼.PullOut) :
    ∃ H : Prop81General.Prop81ConclusionM (inProblem c γ hc hγ0) 𝔼 t0,
      ∀ D, D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        TargetCriterion.Prop82.HistoryOK H.Λ (inProblem c γ hc hγ0).sys.B2 t0 D Mh qh vh →
        BoundedV Mh → AdaptedV 𝔼 Mh → BoundedV qh → (∃ K, ∀ t ω, |vh t ω| ≤ K) →
        RobustlyOptimal (κ := Fin 2) (inProblem c γ hc hγ0) 𝔼 t0
          (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
          (fun _ y t ω => zpart (y t ω)) := by
  rcases hγ0.lt_or_eq with h | h
  · exact InertiaProp82Complex.in_prop82_all_finite c γ hc h hγ1 𝔼 t0 hpull
  · subst h
    exact ⟨_, fun D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb =>
      in0_prop82_finite c hc hpull hD1 hD2 hhist hMhb hMhk hqhb hvhb⟩

end Woodford.OptimalPolicyRules.TidyR5aInertiaGammaZero
