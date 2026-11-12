/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyRuleSystem
import OptimalPolicyRules.InertiaFOCRoots
import OptimalPolicyRules.TidyR5aExogenousInstrument

/-!
# The rule system of p. 593 at `λₓ = 0`: existence

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, p. 593: the inflation-inertia model
(2.6), (3.1) under commitment to the implicit instrument rule (3.16), at the boundary `λₓ = 0` of
the loss (3.14) (no weight on output-gap stabilisation).

`TidyRuleSystem.rule_system_existsUnique` proves existence and uniqueness for `λₓ > 0`, through the
optimal plan of the problem with `λₓ > 0`; uniqueness (`InflationInertiaRules.rule_system_unique`)
holds for `λₓ ≥ 0`. At `λₓ = 0` the optimal-plan route fails (the loss is not strictly convex in
`x`, and the first-order system loses `x`). Here existence is proved **directly**, by writing the
rule system itself in Blanchard–Kahn form.

## The Blanchard–Kahn form of the rule system at `λₓ = 0`

* `0 < γ ≤ 1` (`Pos`): with `ı = i − i*`, the state is `(π_n, x_n, ı_n)` (non-predetermined) and
  `(π_{n−1}, ı_{n−1}, ı_{n−2})` (predetermined); (2.6), (3.1), (3.16) have the lead matrix
  `P = [[β, 0, 0], [σ, 1, 0], [−βγκσ/λᵢ, 0, βγ]]` (`det P = β²γ`). `Pos.eval_charpoly`: the
  characteristic polynomial of the `6 × 6` matrix is `D(z)/(−β²γ)`, `D` the determinant of the
  symbol of the rule system (`InflationInertiaRules.charD` at `λₓ = 0`), so
  (`InertiaFOCRoots.charD_inside_three`) it has no eigenvalue on the unit circle and exactly three
  inside (`Pos.bk_roots`).
* `γ = 0` (`Zero`): (3.16) has no lead, `ı_n = (κσ/λᵢ)π_n + A₂ı_{n−1} − β⁻¹ı_{n−2}`; the state is
  `(π_n, x_n)` and `(ı_{n−1}, ı_{n−2})`; `Zero.eval_charpoly`: the characteristic polynomial of
  the `4 × 4` matrix is the quartic `p` of App. G.4 at `λₓ = 0` (`IRuleBasic.pG`), with exactly
  two roots inside and none on the circle (`IRuleBasic.pG_insideCard_eq_two`).
* The genericity condition (`Pos.genericX`, `Zero.genericX`) follows from the **uniqueness**
  result `InflationInertiaRules.rule_system_unique` applied under perfect foresight: a bounded
  orbit with zero predetermined part is a solution of the homogeneous rule system with zero
  history, hence zero.

## Main results

* `Pos.exists_lx0`, `Zero.exists_lx0`: for every bounded adapted disturbance and every history
  `(π₁, x₁, i₁, i₀)` (bounded, known at the right dates) the rule system has a bounded adapted
  solution at `λₓ = 0` (any expectation system).
* **`rule_system_exists_lx0`, `rule_system_existsUnique_lx0`**: for every `0 ≤ γ ≤ 1`, existence
  (and, with faithful expectations and pull-out, uniqueness) at `λₓ = 0`; together with
  `TidyRuleSystem.rule_system_existsUnique` this covers every `λₓ ≥ 0`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5aLambdaXZero

open Matrix Polynomial
open CubicRoots CubicRoots.Assumptions
open InflationInertiaRules (charD recipC)
open BKInvariantSplit (eigs stableCount NoUnit GenericX boundedOrbits)

variable {Ω : Type*}

/-- Woodford (2003), p. 593 (tool): `E_t` of `a f + b₁g₁ + b₂g₂ + b₃g₃` with `g₁, g₂, g₃` known
at `t`. -/
theorem E_comb (𝔼 : ExpectationSystem Ω) (t : ℕ) (a b1 b2 b3 : ℝ) (f g1 g2 g3 : Ω → ℝ)
    (h1 : 𝔼.E t g1 = g1) (h2 : 𝔼.E t g2 = g2) (h3 : 𝔼.E t g3 = g3) :
    𝔼.E t (fun ω => a * f ω + b1 * g1 ω + b2 * g2 ω + b3 * g3 ω) =
      fun ω => a * 𝔼.E t f ω + b1 * g1 ω + b2 * g2 ω + b3 * g3 ω := by
  change 𝔼.E t (a • f + b1 • g1 + b2 • g2 + b3 • g3) = _
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2, h3]
  rfl

/-! ### `0 < γ ≤ 1` -/

namespace Pos

variable (β γ κ σ li : ℝ)

/-- Woodford (2003), (3.16), p. 593: the coefficient `κσ/λᵢ` of `q̃` at `λₓ = 0`. -/
noncomputable def c0 : ℝ := κ * σ / li

/-- Woodford (2003), (2.6), (3.1), (3.16) at `λₓ = 0`: the inverse of the lead matrix
`P = [[β, 0, 0], [σ, 1, 0], [−βγc₀, 0, βγ]]` (rows (2.6), (3.1), (3.16); columns `π, x, ı`). -/
noncomputable def Pinv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β⁻¹, 0, 0; -(σ * β⁻¹), 1, 0; c0 κ σ li * β⁻¹, 0, (β * γ)⁻¹]

/-- Woodford (2003), (2.6), (3.1), (3.16) at `λₓ = 0`: the matrix of `(π_n, x_n, ı_n)`. -/
noncomputable def A1 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + β * γ, -κ, 0; 0, 1, σ; -(c0 κ σ li * (1 + β * γ ^ 2)), 0, 1 + γ + β * γ]

/-- Woodford (2003), (2.6), (3.1), (3.16) at `λₓ = 0`: the matrix of the predetermined
`(π_{n−1}, ı_{n−1}, ı_{n−2})`. -/
noncomputable def A2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-γ, 0, 0; 0, 0, 0; c0 κ σ li * γ, -coefA2 β γ κ σ, β⁻¹]

/-- Woodford (2003), p. 593 (tool): the predetermined state next period,
`(π_n, ı_n, ı_{n−1})`: the part taken from `(π_n, x_n, ı_n)`. -/
def MXZ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 1; 0, 0, 0]

/-- Woodford (2003), p. 593 (tool): the part of `(π_n, ı_n, ı_{n−1})` taken from
`(π_{n−1}, ı_{n−1}, ı_{n−2})`. -/
def MXX : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 0; 0, 1, 0]

/-- **Woodford (2003), p. 593: the rule system (2.6), (3.1), (3.16) at `λₓ = 0` in
Blanchard–Kahn form** `E_ty_{t+1} = Ay_t + w_t`,
`y = (π_n, x_n, ı_n; π_{n−1}, ı_{n−1}, ı_{n−2})`. -/
noncomputable def Abk : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks (Pinv β γ κ σ li * A1 β γ κ σ li) (Pinv β γ κ σ li * A2 β γ κ σ li) MXZ MXX

/-- **Woodford (2003), p. 593 with App. C.1: the characteristic polynomial of the Blanchard–Kahn
matrix at `λₓ = 0` is `D(z)/(−β²γ)`** (for `z ≠ 0`), `D` the determinant of the symbol of the
rule system (`InflationInertiaRules.charD`). -/
theorem eval_charpoly (hβ : β ≠ 0) (hγ : γ ≠ 0) (hli : li ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    ((Abk β γ κ σ li).map Complex.ofReal).charpoly.eval z * (-(β ^ 2 * γ) : ℂ) =
      charD β γ κ σ 0 li z := by
  set B11 : Matrix (Fin 3) (Fin 3) ℂ := (Pinv β γ κ σ li * A1 β γ κ σ li).map Complex.ofReal
    with hB11
  set B12 : Matrix (Fin 3) (Fin 3) ℂ := (Pinv β γ κ σ li * A2 β γ κ σ li).map Complex.ofReal
    with hB12
  set B21 : Matrix (Fin 3) (Fin 3) ℂ := MXZ.map Complex.ofReal with hB21
  set B22 : Matrix (Fin 3) (Fin 3) ℂ := MXX.map Complex.ofReal with hB22
  have hmap : (Abk β γ κ σ li).map Complex.ofReal = fromBlocks B11 B12 B21 B22 := by
    rw [Abk, fromBlocks_map]
  have hN : Matrix.scalar (Fin 3 ⊕ Fin 3) z - fromBlocks B11 B12 B21 B22 =
      fromBlocks (Matrix.scalar (Fin 3) z - B11) (-B12) (-B21)
        (Matrix.scalar (Fin 3) z - B22) := by
    ext (i | i) (j | j) <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, fromBlocks]
  set Dz := Matrix.scalar (Fin 3) z - B22 with hDz
  set Dinv : Matrix (Fin 3) (Fin 3) ℂ := !![z⁻¹, 0, 0; 0, z⁻¹, 0; 0, z⁻¹ ^ 2, z⁻¹] with hDinv
  have hDD : Dz * Dinv = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hDz, hDinv, hB22, MXX, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
        Matrix.diagonal_apply, hz, pow_two]
  set Sz := (Matrix.scalar (Fin 3) z - B11) - (-B12) * Dinv * (-B21) with hSz
  have hE : fromBlocks (Matrix.scalar (Fin 3) z - B11) (-B12) (-B21) Dz *
      fromBlocks 1 0 (-(Dinv * (-B21))) 1 = fromBlocks Sz (-B12) 0 Dz := by
    rw [fromBlocks_multiply]
    congr 1
    · rw [hSz, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc]
      abel
    · simp
    · rw [Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
      abel
    · simp
  have hdet := congrArg Matrix.det hE
  rw [det_mul, det_fromBlocks_zero₁₂, det_one, mul_one, mul_one,
    det_fromBlocks_zero₂₁] at hdet
  rw [Matrix.eval_charpoly, hmap, hN, hdet]
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hlic : (li : ℂ) ≠ 0 := by exact_mod_cast hli
  rw [det_fin_three, det_fin_three]
  simp only [hSz, hDz, hDinv, hB11, hB12, hB21, hB22, Pinv, A1, A2, MXZ, MXX, c0,
    Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const, Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold charD recipC coefA0 coefA1 coefA2 coefA3
  simp
  field_simp
  ring

/-- **Woodford (2003), p. 593 with App. C.1, at `λₓ = 0`: the eigenvalues of the
Blanchard–Kahn matrix** are the six roots of `D`: none lies on the unit circle and exactly three
lie in the open unit disc (`InertiaFOCRoots.charD_inside_three`, which allows `λₓ = 0`). -/
theorem bk_roots (h : Standing β γ κ σ) (hli : 0 < li) :
    NoUnit (Abk β γ κ σ li) ∧ stableCount (Abk β γ κ σ li) = 3 := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  obtain ⟨s, -, hD, hin, hnu⟩ := InertiaFOCRoots.charD_inside_three h (le_refl 0) hli
  have hcp : ((Abk β γ κ σ li).map Complex.ofReal).charpoly = (s.map (fun m => X - C m)).prod := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (fun z (hz : z ∈ ({0}ᶜ : Set ℂ)) => ?_)
      (Set.finite_singleton (0 : ℂ)).infinite_compl
    have hz0 : z ≠ 0 := hz
    change Polynomial.eval z _ = Polynomial.eval z _
    have e := eval_charpoly β γ κ σ li hβ hγ hli.ne' hz0
    rw [hD z] at e
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    have he : ((fun p => Polynomial.eval z p) ∘ fun m => X - C m) = fun m => z - m := by
      funext m
      simp
    rw [he]
    have hc : (-(β ^ 2 * γ) : ℂ) ≠ 0 := by
      have : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
      have : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
      exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 ‹(β : ℂ) ≠ 0›) this)
    have e2 : ((-(β ^ 2 * γ) : ℝ) : ℂ) = (-(β ^ 2 * γ) : ℂ) := by push_cast; ring
    rw [e2, mul_comm] at e
    exact mul_left_cancel₀ hc e
  have heigs : eigs (Abk β γ κ σ li) = s := by
    rw [BKInvariantSplit.eigs, hcp, Polynomial.roots_multiset_prod_X_sub_C]
  refine ⟨fun μ hμ => hnu μ (heigs ▸ hμ), ?_⟩
  rw [stableCount, heigs, hin]

/-! #### The rule system from a Blanchard–Kahn path -/

/-- Woodford (2003), (2.6), (3.1), (3.16): the lead matrix `P` (rows (2.6), (3.1), (3.16);
columns `E_tπ_{t+1}, E_tx_{t+1}, E_tı_{t+1}`). -/
noncomputable def Pm : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β, 0, 0; σ, 1, 0; -(β * γ * c0 κ σ li), 0, β * γ]

/-- Woodford (2003), p. 593 (tool): `P P⁻¹ = I` (`det P = β²γ ≠ 0`). -/
theorem Pm_mul_Pinv (hβ : β ≠ 0) (hγ : γ ≠ 0) : Pm β γ κ σ li * Pinv β γ κ σ li = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Pinv, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp
  all_goals ring

/-- Woodford (2003), (2.6), (3.1) with `ı = i − i*`: the disturbance vector
`(−u_n, σ(i* − rⁿ_n), 0)` at date `n = s + 2`. -/
def Fvec (u rn : ℕ → Ω → ℝ) (istar : ℝ) (s : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![-u (s + 2) ω, σ * (istar - rn (s + 2) ω), 0]

/-- Woodford (2003), App. C.1 (tool): the forcing `(P⁻¹F_s, 0)` of the Blanchard–Kahn form. -/
noncomputable def wPos (u rn : ℕ → Ω → ℝ) (istar : ℝ) : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ :=
  fun s k ω => Sum.elim (fun j => (Pinv β γ κ σ li *ᵥ Fvec σ u rn istar s ω) j) (fun _ => 0) k

/-- Woodford (2003), p. 593: the initial predetermined state `(π₁, ı₁, ı₀)`. -/
def x0vec (p1 i1 i0 : Ω → ℝ) (istar : ℝ) : Fin 3 → Ω → ℝ :=
  ![p1, fun ω => i1 ω - istar, fun ω => i0 ω - istar]

/-- Woodford (2003), p. 593: inflation from a path, `π_0 = 0`, `π_1 = p₁`, `π_{s+2} = Y_s`. -/
def πB (p1 : Ω → ℝ) (Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => p1
  | s + 2 => Y s (Sum.inl 0)

/-- Woodford (2003), p. 593: the output gap from a path, `x_0 = 0`, `x_1 = x₁`. -/
def xB (x1 : Ω → ℝ) (Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => x1
  | s + 2 => Y s (Sum.inl 1)

/-- Woodford (2003), p. 593: the interest rate from a path, `i_0 = i₀`, `i_1 = i₁`,
`i_{s+2} = i* + ı_{s+2}`. -/
def iB (istar : ℝ) (i1 i0 : Ω → ℝ) (Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => i0
  | 1 => i1
  | s + 2 => fun ω => Y s (Sum.inl 2) ω + istar

variable {β γ κ σ li}

/-- Woodford (2003), p. 593 (tool): along an equilibrium path the predetermined block is the
lagged `(π_{n−1}, ı_{n−1}, ı_{n−2})`. -/
theorem lags {𝔼' : ExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ} {p1 i1 i0 : Ω → ℝ}
    {Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil 𝔼' (Abk β γ κ σ li) (wPos β γ κ σ li u rn istar)
      (x0vec p1 i1 i0 istar) Y) (s : ℕ) :
    Y s (Sum.inr 0) = πB p1 Y (s + 1) ∧
      Y s (Sum.inr 1) = (fun ω => iB istar i1 i0 Y (s + 1) ω - istar) ∧
      Y s (Sum.inr 2) = (fun ω => iB istar i1 i0 Y s ω - istar) := by
  obtain ⟨hS, -, hpk, h0, -⟩ := hY
  induction s with
  | zero => exact ⟨h0 0, h0 1, h0 2⟩
  | succ s ih =>
    have key : ∀ j, Y (s + 1) (Sum.inr j) = fun ω =>
        (MXZ *ᵥ fun i => Y s (Sum.inl i) ω) j + (MXX *ᵥ fun i => Y s (Sum.inr i) ω) j := by
      intro j
      rw [← hpk s j, hS s (Sum.inr j)]
      funext ω
      have hv : (fun k => Y s k ω) =
          Sum.elim (fun i => Y s (Sum.inl i) ω) (fun i => Y s (Sum.inr i) ω) := by
        funext k
        rcases k with i | i <;> rfl
      simp only [Pi.add_apply, BKForward.mv_apply, hv, Abk, fromBlocks_mulVec, Sum.elim_inr,
        Sum.elim_comp_inl, Sum.elim_comp_inr, wPos, add_zero, Pi.add_apply]
    refine ⟨?_, ?_, ?_⟩
    · rw [key 0]
      funext ω
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_three, πB]
    · rw [key 1]
      funext ω
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_three, iB]
    · rw [key 2]
      funext ω
      have := congrFun ih.2.1 ω
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_three, this]

/-- Woodford (2003), (2.6), (3.1), (3.16) at date `n = s + 2`, from a Blanchard–Kahn path:
`P E_n(π, x, ı)_{n+1} = A₁(π, x, ı)_n + A₂(π_{n−1}, ı_{n−1}, ı_{n−2}) + F_n`. -/
theorem rows (hβ : β ≠ 0) (hγ : γ ≠ 0) {𝔼' : ExpectationSystem Ω} {u rn : ℕ → Ω → ℝ}
    {istar : ℝ} {x0 : Fin 3 → Ω → ℝ} {Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil 𝔼' (Abk β γ κ σ li) (wPos β γ κ σ li u rn istar) x0 Y)
    (s : ℕ) (ω : Ω) :
    Pm β γ κ σ li *ᵥ (fun j => 𝔼'.E s (Y (s + 1) (Sum.inl j)) ω) =
      A1 β γ κ σ li *ᵥ (fun j => Y s (Sum.inl j) ω) + A2 β γ κ σ li *ᵥ
        (fun j => Y s (Sum.inr j) ω) + Fvec σ u rn istar s ω := by
  have hv : (fun k => Y s k ω) =
      Sum.elim (fun i => Y s (Sum.inl i) ω) (fun i => Y s (Sum.inr i) ω) := by
    funext k
    rcases k with i | i <;> rfl
  have hE : (fun j => 𝔼'.E s (Y (s + 1) (Sum.inl j)) ω) = Pinv β γ κ σ li *ᵥ
      (A1 β γ κ σ li *ᵥ (fun j => Y s (Sum.inl j) ω) + A2 β γ κ σ li *ᵥ
        (fun j => Y s (Sum.inr j) ω) + Fvec σ u rn istar s ω) := by
    funext j
    rw [hY.1 s (Sum.inl j)]
    simp only [Pi.add_apply, BKForward.mv_apply, hv, Abk, fromBlocks_mulVec, Sum.elim_inl,
      Sum.elim_comp_inl, Sum.elim_comp_inr, wPos, ← mulVec_mulVec]
    simp only [mulVec_add, Pi.add_apply]
  rw [hE, mulVec_mulVec, Pm_mul_Pinv β γ κ σ li hβ hγ, one_mulVec]

/-- **Woodford (2003), (2.6), (3.1), (3.16) at `λₓ = 0`, from a Blanchard–Kahn equilibrium**
(dates from `n = 2`, `Prop84General.shiftES`): the plan `(πB, xB, iB)` satisfies (2.6) and (3.1)
at every date `≥ 2` and the Euler equation (3.16) at every date `n = t + 2`. -/
theorem eqs_of_equil (hβ : β ≠ 0) (hγ : γ ≠ 0) {𝔼 : ExpectationSystem Ω} {u rn : ℕ → Ω → ℝ}
    {istar : ℝ} {p1 x1 i1 i0 : Ω → ℝ} {Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 2) (Abk β γ κ σ li)
      (wPos β γ κ σ li u rn istar) (x0vec p1 i1 i0 istar) Y) :
    (∀ k, 2 ≤ k → InflationInertiaRules.AS 𝔼 β γ κ u (πB p1 Y) (xB x1 Y) k) ∧
      (∀ k, 2 ≤ k → InflationInertiaRules.IS 𝔼 σ rn (πB p1 Y) (xB x1 Y) (iB istar i1 i0 Y) k) ∧
      ∀ t, InflationInertiaRules.Euler 𝔼 β γ κ σ (fun k ω => iB istar i1 i0 Y k ω - istar)
        (InflationInertiaRules.fbig 𝔼 β γ κ σ 0 li (πB p1 Y) (xB x1 Y)) t := by
  have hl := lags hY
  have hr := rows hβ hγ hY
  have ha : ∀ s k, 𝔼.E (s + 2) (Y s k) = Y s k := hY.2.1
  have hrow : ∀ s ω j, (Pm β γ κ σ li *ᵥ (fun j => 𝔼.E (s + 2) (Y (s + 1) (Sum.inl j)) ω)) j =
      (A1 β γ κ σ li *ᵥ (fun j => Y s (Sum.inl j) ω) + A2 β γ κ σ li *ᵥ
        (fun j => Y s (Sum.inr j) ω) + Fvec σ u rn istar s ω) j :=
    fun s ω j => congrFun (hr s ω) j
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun t => ?_⟩
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    intro ω
    have r0 : β * 𝔼.E (s + 2) (Y (s + 1) (Sum.inl 0)) ω = (1 + β * γ) * Y s (Sum.inl 0) ω +
        -(κ * Y s (Sum.inl 1) ω) + -(γ * Y s (Sum.inr 0) ω) + -u (s + 2) ω := by
      have h := hrow s ω 0
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_three] at h
      linear_combination h
    have hE := E_comb 𝔼 (s + 2) 1 (-γ) 0 0 (Y (s + 1) (Sum.inl 0)) (Y s (Sum.inl 0))
      (Y s (Sum.inl 0)) (Y s (Sum.inl 0)) (ha s _) (ha s _) (ha s _)
    have e1 : (fun ω' => πB p1 Y (s + 2 + 1) ω' - γ * πB p1 Y (s + 2) ω') =
        fun ω' => 1 * Y (s + 1) (Sum.inl 0) ω' + -γ * Y s (Sum.inl 0) ω' +
          0 * Y s (Sum.inl 0) ω' + 0 * Y s (Sum.inl 0) ω' := by
      funext ω'
      simp only [πB]
      ring
    have e2 : πB p1 Y (s + 2 - 1) = Y s (Sum.inr 0) := by
      rw [(hl s).1, show s + 2 - 1 = s + 1 by omega]
    rw [e1, hE, e2]
    simp only [πB, xB]
    linarith
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    intro ω
    have r1 := hrow s ω 1
    simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_three] at r1
    have e1 : 𝔼.E (s + 2) (xB x1 Y (s + 2 + 1)) ω = 𝔼.E (s + 2) (Y (s + 1) (Sum.inl 1)) ω := rfl
    have e2 : 𝔼.E (s + 2) (πB p1 Y (s + 2 + 1)) ω = 𝔼.E (s + 2) (Y (s + 1) (Sum.inl 0)) ω := rfl
    rw [e1, e2]
    simp only [xB, iB]
    linarith
  · intro ω
    have r2 : -(β * γ * (κ * σ / li)) * 𝔼.E (t + 2) (Y (t + 1) (Sum.inl 0)) ω +
        β * γ * 𝔼.E (t + 2) (Y (t + 1) (Sum.inl 2)) ω =
        -(κ * σ / li * (1 + β * γ ^ 2)) * Y t (Sum.inl 0) ω + (1 + γ + β * γ) * Y t (Sum.inl 2) ω +
          κ * σ / li * γ * Y t (Sum.inr 0) ω + -coefA2 β γ κ σ * Y t (Sum.inr 1) ω +
          β⁻¹ * Y t (Sum.inr 2) ω := by
      have h := hrow t ω 2
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_three, c0] at h
      linear_combination h
    have hALi : InflationInertiaRules.ALi β γ κ σ (fun k ω => iB istar i1 i0 Y k ω - istar) t =
        fun ω => β * γ * Y (t + 1) (Sum.inl 2) ω + -(1 + γ + β * γ) * Y t (Sum.inl 2) ω +
          coefA2 β γ κ σ * Y t (Sum.inr 1) ω + -β⁻¹ * Y t (Sum.inr 2) ω := by
      funext ω'
      have h1 := congrFun (hl t).2.1 ω'
      have h2 := congrFun (hl t).2.2 ω'
      simp only [InflationInertiaRules.ALi]
      rw [h1, h2]
      simp only [iB]
      ring
    have hq : InflationInertiaRules.qtil γ κ σ 0 li (πB p1 Y) (xB x1 Y) (t + 2 + 1) =
        fun ω => κ * σ / li * Y (t + 1) (Sum.inl 0) ω + -(κ * σ / li * γ) * Y t (Sum.inl 0) ω +
          0 * Y t (Sum.inl 0) ω + 0 * Y t (Sum.inl 0) ω := by
      funext ω'
      simp only [InflationInertiaRules.qtil, πB, zero_div, zero_mul, add_zero,
        show t + 2 + 1 - 1 = t + 2 by omega]
      ring
    have hq0 : InflationInertiaRules.qtil γ κ σ 0 li (πB p1 Y) (xB x1 Y) (t + 2) ω =
        κ * σ / li * (Y t (Sum.inl 0) ω - γ * Y t (Sum.inr 0) ω) := by
      have h1 := congrFun (hl t).1 ω
      simp only [InflationInertiaRules.qtil, zero_div, zero_mul, add_zero,
        show t + 2 - 1 = t + 1 by omega]
      rw [← h1]
      rfl
    unfold InflationInertiaRules.fbig
    rw [hALi, E_comb 𝔼 (t + 2) _ _ _ _ _ _ _ _ (ha t _) (ha t _) (ha t _), hq,
      E_comb 𝔼 (t + 2) _ _ _ _ _ _ _ _ (ha t _) (ha t _) (ha t _), hq0]
    linear_combination r2


variable (β γ κ σ li)

/-- Woodford (2003), p. 593 (tool): with no disturbance and `i* = 0` the forcing vanishes. -/
theorem wPos_zero :
    wPos β γ κ σ li (fun (_ : ℕ) (_ : Ω) => 0) (fun _ _ => 0) 0 = fun _ _ _ => 0 := by
  funext s k ω
  rcases k with j | j
  · simp [wPos, Fvec, mulVec, dotProduct, Fin.sum_univ_three]
  · rfl

/-- Woodford (2003), (3.16) (tool): the zero plan solves the homogeneous rule system under
perfect foresight (`u = rⁿ = 0`, `i* = 0`). -/
theorem zero_sol :
    (∀ k, 2 ≤ k → InflationInertiaRules.AS perfectForesight β γ κ (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => 0) k) ∧
    (∀ k, 2 ≤ k → InflationInertiaRules.IS perfectForesight σ (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => 0) k) ∧
    ∀ t, InflationInertiaRules.Euler perfectForesight β γ κ σ
      (fun k ω => (fun _ _ => (0 : ℝ)) k ω - 0)
      (InflationInertiaRules.fbig perfectForesight β γ κ σ 0 li (fun _ _ => 0) (fun _ _ => 0))
      t := by
  refine ⟨fun k _ ω => ?_, fun k _ ω => ?_, fun t ω => ?_⟩
  · change (0 : ℝ) - γ * 0 = κ * 0 + β * (0 - γ * 0) + 0
    ring
  · change (0 : ℝ) = 0 - σ * (0 - 0 - 0)
    ring
  · change InflationInertiaRules.ALi β γ κ σ (fun k ω => (fun _ _ => (0 : ℝ)) k ω - 0) t ω =
      -(InflationInertiaRules.qtil γ κ σ 0 li (fun _ _ => 0) (fun _ _ => 0) (t + 2) ω -
        β * γ * InflationInertiaRules.qtil γ κ σ 0 li (fun _ _ => 0) (fun _ _ => 0) (t + 2 + 1) ω)
    simp [InflationInertiaRules.ALi, InflationInertiaRules.qtil]

/-- **Woodford (2003), App. C.1, fn 2 (genericity) for the rule system at `λₓ = 0`, from the
uniqueness theorem.** A bounded orbit of the Blanchard–Kahn matrix with zero predetermined part is
(under perfect foresight) a solution of the homogeneous rule system with zero history, so it is
zero by `InflationInertiaRules.rule_system_unique`. -/
theorem genericX (h : Standing β γ κ σ) (hli : 0 < li) : GenericX (Abk β γ κ σ li) := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  intro v hv hx
  set 𝔼' := Prop84General.shiftES perfectForesight 2 with h𝔼'
  have hY : GeneralBKCopy.Equil 𝔼' (Abk β γ κ σ li)
      (wPos β γ κ σ li (fun (_ : ℕ) (_ : Unit) => 0) (fun _ _ => 0) 0)
      (x0vec (fun _ => 0) (fun _ => 0) (fun _ => 0) 0)
      (fun t k _ => ((Abk β γ κ σ li) ^ t *ᵥ v) k) := by
    rw [wPos_zero]
    have hx0 : x0vec (fun (_ : Unit) => (0 : ℝ)) (fun _ => 0) (fun _ => 0) 0 =
        fun j _ => v (Sum.inr j) := by
      funext j ω
      fin_cases j <;> simp [x0vec, hx]
    rw [hx0]
    exact TidyR5aExogenousInstrument.BK.orbit_equil _ hv
  obtain ⟨hAS, hIS, hEu⟩ := eqs_of_equil hβ hγ (x1 := fun _ => 0) hY
  obtain ⟨hAS0, hIS0, hEu0⟩ := zero_sol β γ κ σ li
  obtain ⟨C, hC⟩ := hv
  have hb : ∀ {g : ℕ → Unit → ℝ}, (∀ k ω, |g k ω| ≤ max C 0) →
      InflationInertiaRules.Bnd g := fun hg => ⟨max C 0, le_max_right _ _, hg⟩
  have hπb : InflationInertiaRules.Bnd (πB (fun _ => 0)
      (fun t k (_ : Unit) => ((Abk β γ κ σ li) ^ t *ᵥ v) k)) := by
    refine hb fun k ω => ?_
    rcases k with _ | _ | s
    · simp [πB]
    · simp [πB]
    · exact (hC s _).trans (le_max_left _ _)
  have hxb : InflationInertiaRules.Bnd (xB (fun _ => 0)
      (fun t k (_ : Unit) => ((Abk β γ κ σ li) ^ t *ᵥ v) k)) := by
    refine hb fun k ω => ?_
    rcases k with _ | _ | s
    · simp [xB]
    · simp [xB]
    · exact (hC s _).trans (le_max_left _ _)
  have hib : InflationInertiaRules.Bnd (iB 0 (fun _ => 0) (fun _ => 0)
      (fun t k (_ : Unit) => ((Abk β γ κ σ li) ^ t *ᵥ v) k)) := by
    refine hb fun k ω => ?_
    rcases k with _ | _ | s
    · simp [iB]
    · simp [iB]
    · change |((Abk β γ κ σ li) ^ s *ᵥ v) (Sum.inl 2) + 0| ≤ max C 0
      rw [add_zero]
      exact (hC s _).trans (le_max_left _ _)
  have h0b : InflationInertiaRules.Bnd (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) :=
    ⟨0, le_rfl, fun _ _ => by simp⟩
  have key := InflationInertiaRules.rule_system_unique perfectForesight perfectForesight_pullOut
    ExpectationTools.perfectForesight_faithful h.beta_pos h.beta_lt_one h.kappa_pos.ne'
    h.sigma_pos.ne' hli (le_refl 0) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hπb hxb hib h0b h0b h0b hAS hAS0 hIS hIS0 hEu
    hEu0 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  funext k
  rcases k with j | j
  · obtain ⟨e1, e2, e3⟩ := key 2 (by norm_num) ()
    fin_cases j
    · simpa [πB] using e1
    · simpa [xB] using e2
    · simpa [iB] using e3
  · exact hx j

/-- **Woodford (2003), p. 593: existence at `λₓ = 0` for `0 < γ ≤ 1`.** For every bounded adapted
disturbance `(u, rⁿ)` and every bounded history `(π₁, x₁, i₁, i₀)` (`π₁, x₁, i₁` known at 1, `i₀`
at 0), the rule system (2.6), (3.1), (3.16) with `λₓ = 0` has a bounded adapted solution with that
history (any expectation system): the Blanchard–Kahn equilibrium of `Abk` from date 2 on
(`GeneralBKCopy.determinate_of`), with the history glued in. -/
theorem exists_lx0 (c : IRuleBasic.Calib) (hlx : c.lx = 0) (h : Standing c.β γ c.κ c.σ)
    (hli : 0 < c.li) (𝔼 : ExpectationSystem Ω) {u rn : ℕ → Ω → ℝ}
    (hub : InflationInertiaRules.Bnd u) (hua : 𝔼.Adapted u) (hrb : InflationInertiaRules.Bnd rn)
    (hra : 𝔼.Adapted rn) {p1 x1 i1 i0 : Ω → ℝ} (hh : TidyRuleSystem.History 𝔼 p1 x1 i1 i0) :
    ∃ π x i, TidyRuleSystem.RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  obtain ⟨hnu, hcount⟩ := bk_roots c.β γ c.κ c.σ c.li h hli
  have hd : Module.finrank ℝ (boundedOrbits (Abk c.β γ c.κ c.σ c.li)) = Fintype.card (Fin 3) := by
    rw [BKInvariantSplit.finrank_eq_stableCount hnu, hcount, Fintype.card_fin]
  have hDet := GeneralBKCopy.determinate_of (Prop84General.shiftES 𝔼 2) hnu hd
    (genericX c.β γ c.κ c.σ c.li h hli)
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  obtain ⟨Cu, hCu0, hCu⟩ := hub
  obtain ⟨Cr, hCr0, hCr⟩ := hrb
  -- the forcing
  obtain ⟨Kw, hKw⟩ := GeneralFOC.exists_bound_mulVec (Pinv c.β γ c.κ c.σ c.li)
    (Cu + c.σ * (|c.istar| + Cr))
  have hwb : BKForward.BoundedV (wPos c.β γ c.κ c.σ c.li u rn c.istar) := by
    refine ⟨max Kw 0, fun s k ω => ?_⟩
    rcases k with j | j
    · refine (hKw _ (fun i => ?_) j).trans (le_max_left _ _)
      have hσ := h.sigma_pos
      fin_cases i
      · simp only [Fvec]
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, abs_neg]
        nlinarith [hCu (s + 2) ω, abs_nonneg c.istar]
      · simp only [Fvec]
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, abs_mul,
          abs_of_pos hσ]
        have := abs_sub c.istar (rn (s + 2) ω)
        nlinarith [hCr (s + 2) ω]
      · simp only [Fvec]
        simp only [Fin.reduceFinMk, Matrix.cons_val, abs_zero]
        nlinarith [abs_nonneg c.istar]
    · simp [wPos]
  have hwa : BKForward.AdaptedV (Prop84General.shiftES 𝔼 2)
      (wPos c.β γ c.κ c.σ c.li u rn c.istar) := by
    intro s k
    change 𝔼.E (s + 2) _ = _
    rcases k with j | j
    · have e : wPos c.β γ c.κ c.σ c.li u rn c.istar s (Sum.inl j) = fun ω =>
          (Pinv c.β γ c.κ c.σ c.li j 0) * (-u (s + 2) ω) +
            (Pinv c.β γ c.κ c.σ c.li j 1 * c.σ) * (-rn (s + 2) ω) +
            (Pinv c.β γ c.κ c.σ c.li j 2) * (0 : Ω → ℝ) ω +
            Pinv c.β γ c.κ c.σ c.li j 1 * c.σ * c.istar := by
        funext ω
        simp [wPos, Fvec, mulVec, dotProduct, Fin.sum_univ_three]
        ring
      have hu' : 𝔼.E (s + 2) (fun ω => -u (s + 2) ω) = fun ω => -u (s + 2) ω := by
        change 𝔼.E (s + 2) (-(u (s + 2))) = -(u (s + 2))
        rw [map_neg, hua]
      have hr' : 𝔼.E (s + 2) (fun ω => -rn (s + 2) ω) = fun ω => -rn (s + 2) ω := by
        change 𝔼.E (s + 2) (-(rn (s + 2))) = -(rn (s + 2))
        rw [map_neg, hra]
      rw [e]
      exact TidyRuleSystem.known_lin3 𝔼 hu' hr' (𝔼.const (s + 2) 0) _ _ _ _
    · exact 𝔼.const _ 0
  have hx0k : ∀ j, (Prop84General.shiftES 𝔼 2).E 0 (x0vec p1 i1 i0 c.istar j) =
      x0vec p1 i1 i0 c.istar j := by
    intro j
    change 𝔼.E (0 + 2) _ = _
    have k1 : ∀ f : Ω → ℝ, 𝔼.E 1 f = f → 𝔼.E 2 f = f := fun f hf => by
      rw [← hf, 𝔼.known (by norm_num : 1 ≤ 2)]
    have k0 : ∀ f : Ω → ℝ, 𝔼.E 0 f = f → 𝔼.E 2 f = f := fun f hf => by
      rw [← hf, 𝔼.known (by norm_num : 0 ≤ 2)]
    have hsub : ∀ f : Ω → ℝ, 𝔼.E 2 f = f → 𝔼.E 2 (fun ω => f ω - c.istar) =
        fun ω => f ω - c.istar := fun f hf => by
      change 𝔼.E 2 (f - fun _ => c.istar) = f - fun _ => c.istar
      rw [map_sub, hf, 𝔼.const]
    rw [zero_add]
    fin_cases j
    · exact k1 p1 hp1
    · exact hsub i1 (k1 i1 hi1)
    · exact hsub i0 (k0 i0 hi0)
  have hx0b : ∃ M, ∀ j ω, |x0vec p1 i1 i0 c.istar j ω| ≤ M := by
    refine ⟨K + |c.istar|, fun j ω => ?_⟩
    obtain ⟨k1, -, k3, k4⟩ := hK ω
    fin_cases j
    · simp only [x0vec]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [abs_nonneg c.istar]
    · simp only [x0vec]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [abs_sub (i1 ω) c.istar]
    · simp only [x0vec]
      simp only [Fin.reduceFinMk, Matrix.cons_val]
      linarith [abs_sub (i0 ω) c.istar]
  obtain ⟨Y, hY, -⟩ := hDet _ hwb hwa _ hx0k hx0b
  obtain ⟨hAS, hIS, hEu⟩ := eqs_of_equil hβ hγ (x1 := x1) hY
  have ha : ∀ s k, 𝔼.E (s + 2) (Y s k) = Y s k := hY.2.1
  obtain ⟨M, hM⟩ := hY.2.2.2.2
  refine ⟨πB p1 Y, xB x1 Y, iB c.istar i1 i0 Y, fun k => ?_, fun k => ?_, fun k => ?_,
    ⟨max (max M K) 0, le_max_right _ _, fun k ω => ?_⟩,
    ⟨max (max M K) 0, le_max_right _ _, fun k ω => ?_⟩,
    ⟨max (max M K) 0 + |c.istar|, by positivity, fun k ω => ?_⟩, hAS, hIS, ?_, rfl, rfl, rfl,
    rfl⟩
  · rcases k with _ | _ | s
    · exact 𝔼.const 0 0
    · exact hp1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact 𝔼.const 0 0
    · exact hx1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact hi0
    · exact hi1
    · change 𝔼.E (s + 2) (Y s (Sum.inl 2) + fun _ => c.istar) = Y s (Sum.inl 2) + fun _ => c.istar
      rw [map_add, ha, 𝔼.const]
  · rcases k with _ | _ | s
    · simp [πB]
    · exact (hK ω).1.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hM s _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rcases k with _ | _ | s
    · simp [xB]
    · exact (hK ω).2.1.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hM s _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h0 : 0 ≤ max (max M K) 0 := le_max_right _ _
    rcases k with _ | _ | s
    · have := (hK ω).2.2.2.trans ((le_max_right M K).trans (le_max_left _ 0))
      change |i0 ω| ≤ _
      linarith [abs_nonneg c.istar]
    · have := (hK ω).2.2.1.trans ((le_max_right M K).trans (le_max_left _ 0))
      change |i1 ω| ≤ _
      linarith [abs_nonneg c.istar]
    · change |Y s (Sum.inl 2) ω + c.istar| ≤ _
      have := (hM s (Sum.inl 2) ω).trans ((le_max_left M K).trans (le_max_left _ 0))
      linarith [abs_add_le (Y s (Sum.inl 2) ω) c.istar]
  · intro t
    rw [hlx]
    exact hEu t

end Pos

/-! ### `γ = 0` -/

namespace Zero

variable (β κ σ li : ℝ)

/-- Woodford (2003), (3.16) at `γ = 0`: the coefficient `A₂ = 1 + β⁻¹(1 + κσ)`. -/
noncomputable def A2c : ℝ := coefA2 β 0 κ σ

/-- Woodford (2003), (2.6), (3.1) at `γ = 0`: the inverse of the lead matrix
`P = [[β, 0], [σ, 1]]` (rows (2.6), (3.1); columns `π, x`). -/
noncomputable def Pinv : Matrix (Fin 2) (Fin 2) ℝ := !![β⁻¹, 0; -(σ * β⁻¹), 1]

/-- Woodford (2003), (2.6), (3.1) at `γ = 0`: the lead matrix `P`. -/
def Pm : Matrix (Fin 2) (Fin 2) ℝ := !![β, 0; σ, 1]

/-- Woodford (2003), (2.6), (3.1) at `γ = 0` with (3.16) substituted for `ı_n`: the matrix of
`(π_n, x_n)`. -/
noncomputable def A1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, -κ; σ * Pos.c0 κ σ li, 1]

/-- Woodford (2003), (2.6), (3.1) at `γ = 0` with (3.16) substituted for `ı_n`: the matrix of
the predetermined `(ı_{n−1}, ı_{n−2})`. -/
noncomputable def A2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; σ * A2c β κ σ, -(σ * β⁻¹)]

/-- Woodford (2003), (3.16) at `γ = 0`: `ı_n = (κσ/λᵢ)π_n + A₂ı_{n−1} − β⁻¹ı_{n−2}` — the part
from `(π_n, x_n)` of the next predetermined state `(ı_n, ı_{n−1})`. -/
noncomputable def MXZ : Matrix (Fin 2) (Fin 2) ℝ := !![Pos.c0 κ σ li, 0; 0, 0]

/-- Woodford (2003), (3.16) at `γ = 0`: the part from `(ı_{n−1}, ı_{n−2})` of `(ı_n, ı_{n−1})`. -/
noncomputable def MXX : Matrix (Fin 2) (Fin 2) ℝ := !![A2c β κ σ, -β⁻¹; 1, 0]

/-- **Woodford (2003), p. 593: the rule system at `γ = 0`, `λₓ = 0` in Blanchard–Kahn form**,
`y = (π_n, x_n; ı_{n−1}, ı_{n−2})`. -/
noncomputable def Abk : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  fromBlocks (Pinv β σ * A1 κ σ li) (Pinv β σ * A2 β κ σ) (MXZ κ σ li) (MXX β κ σ)

/-- **Woodford (2003), p. 593 with App. G.4: at `γ = 0`, `λₓ = 0`, the characteristic polynomial
of the Blanchard–Kahn matrix is the quartic `p` of (G.12)** (`IRuleBasic.pG` at `λₓ = 0`), at
every `z` with `z² − A₂z + β⁻¹ ≠ 0`. -/
theorem eval_charpoly (hβ : β ≠ 0) (hli : li ≠ 0) {z : ℂ}
    (hT : z ^ 2 - (A2c β κ σ : ℂ) * z + (β : ℂ)⁻¹ ≠ 0) :
    ((Abk β κ σ li).map Complex.ofReal).charpoly.eval z = IRuleBasic.pG β σ κ 0 li z := by
  set T : ℂ := z ^ 2 - (A2c β κ σ : ℂ) * z + (β : ℂ)⁻¹ with hTdef
  set B11 : Matrix (Fin 2) (Fin 2) ℂ := (Pinv β σ * A1 κ σ li).map Complex.ofReal with hB11
  set B12 : Matrix (Fin 2) (Fin 2) ℂ := (Pinv β σ * A2 β κ σ).map Complex.ofReal with hB12
  set B21 : Matrix (Fin 2) (Fin 2) ℂ := (MXZ κ σ li).map Complex.ofReal with hB21
  set B22 : Matrix (Fin 2) (Fin 2) ℂ := (MXX β κ σ).map Complex.ofReal with hB22
  have hmap : (Abk β κ σ li).map Complex.ofReal = fromBlocks B11 B12 B21 B22 := by
    rw [Abk, fromBlocks_map]
  have hN : Matrix.scalar (Fin 2 ⊕ Fin 2) z - fromBlocks B11 B12 B21 B22 =
      fromBlocks (Matrix.scalar (Fin 2) z - B11) (-B12) (-B21)
        (Matrix.scalar (Fin 2) z - B22) := by
    ext (i | i) (j | j) <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, fromBlocks]
  set Dz := Matrix.scalar (Fin 2) z - B22 with hDz
  set adjD : Matrix (Fin 2) (Fin 2) ℂ := !![z, -(β : ℂ)⁻¹; 1, z - (A2c β κ σ : ℂ)] with hadj
  have hDA : Dz * adjD = T • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hDz, hadj, hB22, MXX, hTdef, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply,
        Matrix.diagonal_apply] <;> ring
  set Cn := -B21 with hCn
  set TL := T • (Matrix.scalar (Fin 2) z - B11) - (-B12) * adjD * Cn with hTL
  have hE : fromBlocks (Matrix.scalar (Fin 2) z - B11) (-B12) Cn Dz *
      fromBlocks (T • 1) 0 (-(adjD * Cn)) 1 = fromBlocks TL (-B12) 0 Dz := by
    rw [fromBlocks_multiply]
    congr 1
    · rw [hTL, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc]
      abel
    · simp
    · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, hDA,
        Matrix.smul_mul, Matrix.one_mul]
      abel
    · simp
  have hdet := congrArg Matrix.det hE
  rw [det_mul, det_fromBlocks_zero₁₂, det_one, mul_one, det_smul, det_one, mul_one,
    det_fromBlocks_zero₂₁, Fintype.card_fin] at hdet
  have hdetD : Dz.det = T := by
    rw [det_fin_two]
    simp [hDz, hB22, MXX, hTdef, Matrix.scalar_apply]
    ring
  rw [hdetD] at hdet
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hlic : (li : ℂ) ≠ 0 := by exact_mod_cast hli
  have hTL : TL.det = T * IRuleBasic.pG β σ κ 0 li z := by
    rw [det_fin_two]
    simp only [hTL, hCn, hadj, hB11, hB12, hB21, Pinv, A1, A2, MXZ, A2c, Pos.c0, hTdef,
      Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
    unfold IRuleBasic.pG IRuleBasic.palin IRuleBasic.aG IRuleBasic.bG coefA2
    simp
    field_simp
    ring
  rw [hTL] at hdet
  rw [Matrix.eval_charpoly, hmap, hN]
  have hT' : T ≠ 0 := hT
  exact mul_right_cancel₀ (pow_ne_zero 2 hT') (by rw [hdet]; ring)

/-- **Woodford (2003), p. 593 with App. G.4, at `γ = 0`, `λₓ = 0`: the eigenvalues of the
Blanchard–Kahn matrix** are the roots of `p` (`IRuleBasic.pGPoly`): none on the unit circle and
exactly two in the open unit disc (`IRuleBasic.pG_insideCard_eq_two`, which allows `λₓ = 0`). -/
theorem bk_roots (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hli : 0 < li) :
    NoUnit (Abk β κ σ li) ∧ stableCount (Abk β κ σ li) = 2 := by
  set Tp : ℂ[X] := X ^ 2 - C (A2c β κ σ : ℂ) * X + C (β : ℂ)⁻¹ with hTp
  have hTp0 : Tp ≠ 0 := by
    intro h0
    have := congrArg (fun q : ℂ[X] => q.coeff 2) h0
    simp [hTp] at this
  have hcp : ((Abk β κ σ li).map Complex.ofReal).charpoly = IRuleBasic.pGPoly β σ κ 0 li := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (fun z (hz : z ∈ ((Tp.roots.toFinset : Set ℂ)ᶜ)) => ?_)
      (Tp.roots.toFinset.finite_toSet.infinite_compl)
    have hT : z ^ 2 - (A2c β κ σ : ℂ) * z + (β : ℂ)⁻¹ ≠ 0 := by
      intro h0
      apply hz
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hTp0]
      simpa [hTp] using h0
    change Polynomial.eval z _ = Polynomial.eval z _
    rw [eval_charpoly β κ σ li hβ0.ne' hli.ne' hT, IRuleBasic.pGPoly, IRuleBasic.eval_palinPoly]
    rfl
  have heigs : eigs (Abk β κ σ li) = (IRuleBasic.pGPoly β σ κ 0 li).roots := by
    rw [BKInvariantSplit.eigs, hcp]
  have hp0 : IRuleBasic.pGPoly β σ κ 0 li ≠ 0 := by
    intro h0
    have := congrArg (fun q : ℂ[X] => q.coeff 4) h0
    simp [IRuleBasic.pGPoly, IRuleBasic.palinPoly] at this
  refine ⟨fun μ hμ h1 => ?_, ?_⟩
  · rw [heigs, mem_roots hp0, IsRoot.def, IRuleBasic.pGPoly, IRuleBasic.eval_palinPoly] at hμ
    have ha : IRuleBasic.Annulus β μ := ⟨h1.ge, by
      rw [h1, le_div_iff₀ hβ0]
      linarith⟩
    exact IRuleBasic.pG_ne_zero_of_annulus hβ0 hσ hκ (le_refl 0) hli ha hμ
  · rw [stableCount, heigs]
    exact IRuleBasic.pG_insideCard_eq_two hβ0 hβ1 hσ hκ (le_refl 0) hli

/-- Woodford (2003), (2.6), (3.1) at `γ = 0` (tool): `P P⁻¹ = I`. -/
theorem Pm_mul_Pinv (hβ : β ≠ 0) : Pm β σ * Pinv β σ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pm, Pinv, Matrix.mul_apply, Fin.sum_univ_two, hβ]

/-- Woodford (2003), (2.6), (3.1) with `ı = i − i*`: the disturbance vector
`(−u_n, σ(i* − rⁿ_n))` at date `n = s + 2`. -/
def Fvec (u rn : ℕ → Ω → ℝ) (istar : ℝ) (s : ℕ) (ω : Ω) : Fin 2 → ℝ :=
  ![-u (s + 2) ω, σ * (istar - rn (s + 2) ω)]

/-- Woodford (2003), App. C.1 (tool): the forcing `(P⁻¹F_s, 0)` at `γ = 0`. -/
noncomputable def wZ (u rn : ℕ → Ω → ℝ) (istar : ℝ) : ℕ → Fin 2 ⊕ Fin 2 → Ω → ℝ :=
  fun s k ω => Sum.elim (fun j => (Pinv β σ *ᵥ Fvec σ u rn istar s ω) j) (fun _ => 0) k

/-- Woodford (2003), p. 593: the initial predetermined state `(ı₁, ı₀)` at `γ = 0`. -/
def x0vec (i1 i0 : Ω → ℝ) (istar : ℝ) : Fin 2 → Ω → ℝ :=
  ![fun ω => i1 ω - istar, fun ω => i0 ω - istar]

/-- Woodford (2003), p. 593: inflation from a path at `γ = 0`. -/
def πB (p1 : Ω → ℝ) (Y : ℕ → Fin 2 ⊕ Fin 2 → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => p1
  | s + 2 => Y s (Sum.inl 0)

/-- Woodford (2003), p. 593: the output gap from a path at `γ = 0`. -/
def xB (x1 : Ω → ℝ) (Y : ℕ → Fin 2 ⊕ Fin 2 → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => x1
  | s + 2 => Y s (Sum.inl 1)

/-- Woodford (2003), (3.16) at `γ = 0`: the interest rate from a path,
`i_{s+2} = i* + (κσ/λᵢ)π_{s+2} + A₂ı_{s+1} − β⁻¹ı_s`. -/
noncomputable def iB (istar : ℝ) (i1 i0 : Ω → ℝ) (Y : ℕ → Fin 2 ⊕ Fin 2 → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => i0
  | 1 => i1
  | s + 2 => fun ω => Pos.c0 κ σ li * Y s (Sum.inl 0) ω + A2c β κ σ * Y s (Sum.inr 0) ω -
      β⁻¹ * Y s (Sum.inr 1) ω + istar

variable {β κ σ li}

/-- Woodford (2003), p. 593 (tool), at `γ = 0`: along an equilibrium path the predetermined block
is `(ı_{n−1}, ı_{n−2})`. -/
theorem lags {𝔼' : ExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ} {i1 i0 : Ω → ℝ}
    {Y : ℕ → Fin 2 ⊕ Fin 2 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil 𝔼' (Abk β κ σ li) (wZ β σ u rn istar) (x0vec i1 i0 istar) Y)
    (s : ℕ) :
    Y s (Sum.inr 0) = (fun ω => iB β κ σ li istar i1 i0 Y (s + 1) ω - istar) ∧
      Y s (Sum.inr 1) = (fun ω => iB β κ σ li istar i1 i0 Y s ω - istar) := by
  obtain ⟨hS, -, hpk, h0, -⟩ := hY
  induction s with
  | zero => exact ⟨h0 0, h0 1⟩
  | succ s ih =>
    have key : ∀ j, Y (s + 1) (Sum.inr j) = fun ω =>
        (MXZ κ σ li *ᵥ fun i => Y s (Sum.inl i) ω) j +
          (MXX β κ σ *ᵥ fun i => Y s (Sum.inr i) ω) j := by
      intro j
      rw [← hpk s j, hS s (Sum.inr j)]
      funext ω
      have hv : (fun k => Y s k ω) =
          Sum.elim (fun i => Y s (Sum.inl i) ω) (fun i => Y s (Sum.inr i) ω) := by
        funext k
        rcases k with i | i <;> rfl
      simp only [Pi.add_apply, BKForward.mv_apply, hv, Abk, fromBlocks_mulVec, Sum.elim_inr,
        Sum.elim_comp_inl, Sum.elim_comp_inr, wZ, add_zero, Pi.add_apply]
    refine ⟨?_, ?_⟩
    · rw [key 0]
      funext ω
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_two, iB]
      ring
    · rw [key 1]
      funext ω
      have := congrFun ih.1 ω
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_two, this]

/-- Woodford (2003), (2.6), (3.1) at `γ = 0`, date `n = s + 2`, from a Blanchard–Kahn path. -/
theorem rows (hβ : β ≠ 0) {𝔼' : ExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ}
    {x0 : Fin 2 → Ω → ℝ} {Y : ℕ → Fin 2 ⊕ Fin 2 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil 𝔼' (Abk β κ σ li) (wZ β σ u rn istar) x0 Y) (s : ℕ) (ω : Ω) :
    Pm β σ *ᵥ (fun j => 𝔼'.E s (Y (s + 1) (Sum.inl j)) ω) =
      A1 κ σ li *ᵥ (fun j => Y s (Sum.inl j) ω) + A2 β κ σ *ᵥ (fun j => Y s (Sum.inr j) ω) +
        Fvec σ u rn istar s ω := by
  have hv : (fun k => Y s k ω) =
      Sum.elim (fun i => Y s (Sum.inl i) ω) (fun i => Y s (Sum.inr i) ω) := by
    funext k
    rcases k with i | i <;> rfl
  have hE : (fun j => 𝔼'.E s (Y (s + 1) (Sum.inl j)) ω) = Pinv β σ *ᵥ
      (A1 κ σ li *ᵥ (fun j => Y s (Sum.inl j) ω) + A2 β κ σ *ᵥ (fun j => Y s (Sum.inr j) ω) +
        Fvec σ u rn istar s ω) := by
    funext j
    rw [hY.1 s (Sum.inl j)]
    simp only [Pi.add_apply, BKForward.mv_apply, hv, Abk, fromBlocks_mulVec, Sum.elim_inl,
      Sum.elim_comp_inl, Sum.elim_comp_inr, wZ, ← mulVec_mulVec]
    simp only [mulVec_add, Pi.add_apply]
  rw [hE, mulVec_mulVec, Pm_mul_Pinv β σ hβ, one_mulVec]

/-- **Woodford (2003), (2.6), (3.1), (3.16) at `γ = 0`, `λₓ = 0`, from a Blanchard–Kahn
equilibrium** (dates from `n = 2`): the plan `(πB, xB, iB)` satisfies (2.6) and (3.1) at every
date `≥ 2` and (3.16) at every date `n = t + 2`. -/
theorem eqs_of_equil (hβ : β ≠ 0) {𝔼 : ExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ}
    {p1 x1 i1 i0 : Ω → ℝ} {Y : ℕ → Fin 2 ⊕ Fin 2 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 2) (Abk β κ σ li) (wZ β σ u rn istar)
      (x0vec i1 i0 istar) Y) :
    (∀ k, 2 ≤ k → InflationInertiaRules.AS 𝔼 β 0 κ u (πB p1 Y) (xB x1 Y) k) ∧
      (∀ k, 2 ≤ k → InflationInertiaRules.IS 𝔼 σ rn (πB p1 Y) (xB x1 Y)
        (iB β κ σ li istar i1 i0 Y) k) ∧
      ∀ t, InflationInertiaRules.Euler 𝔼 β 0 κ σ
        (fun k ω => iB β κ σ li istar i1 i0 Y k ω - istar)
        (InflationInertiaRules.fbig 𝔼 β 0 κ σ 0 li (πB p1 Y) (xB x1 Y)) t := by
  have hl := lags hY
  have hr := rows hβ hY
  have ha : ∀ s k, 𝔼.E (s + 2) (Y s k) = Y s k := hY.2.1
  have hrow : ∀ s ω j, (Pm β σ *ᵥ (fun j => 𝔼.E (s + 2) (Y (s + 1) (Sum.inl j)) ω)) j =
      (A1 κ σ li *ᵥ (fun j => Y s (Sum.inl j) ω) + A2 β κ σ *ᵥ (fun j => Y s (Sum.inr j) ω) +
        Fvec σ u rn istar s ω) j :=
    fun s ω j => congrFun (hr s ω) j
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun t => ?_⟩
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    intro ω
    have r0 : β * 𝔼.E (s + 2) (Y (s + 1) (Sum.inl 0)) ω =
        Y s (Sum.inl 0) ω + -(κ * Y s (Sum.inl 1) ω) + -u (s + 2) ω := by
      have h := hrow s ω 0
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_two] at h
      linear_combination h
    have hE := E_comb 𝔼 (s + 2) 1 (-0) 0 0 (Y (s + 1) (Sum.inl 0)) (Y s (Sum.inl 0))
      (Y s (Sum.inl 0)) (Y s (Sum.inl 0)) (ha s _) (ha s _) (ha s _)
    have e1 : (fun ω' => πB p1 Y (s + 2 + 1) ω' - 0 * πB p1 Y (s + 2) ω') =
        fun ω' => 1 * Y (s + 1) (Sum.inl 0) ω' + -0 * Y s (Sum.inl 0) ω' +
          0 * Y s (Sum.inl 0) ω' + 0 * Y s (Sum.inl 0) ω' := by
      funext ω'
      simp only [πB]
      ring
    rw [e1, hE]
    simp only [πB, xB]
    linarith
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    intro ω
    have r1 := hrow s ω 1
    simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_two, Pos.c0] at r1
    have e1 : 𝔼.E (s + 2) (xB x1 Y (s + 2 + 1)) ω = 𝔼.E (s + 2) (Y (s + 1) (Sum.inl 1)) ω := rfl
    have e2 : 𝔼.E (s + 2) (πB p1 Y (s + 2 + 1)) ω = 𝔼.E (s + 2) (Y (s + 1) (Sum.inl 0)) ω := rfl
    rw [e1, e2]
    simp only [xB, iB, Pos.c0]
    linarith
  · intro ω
    have hALi : InflationInertiaRules.ALi β 0 κ σ
        (fun k ω => iB β κ σ li istar i1 i0 Y k ω - istar) t =
        fun ω => β * 0 * (iB β κ σ li istar i1 i0 Y (t + 3) ω - istar) +
          -Pos.c0 κ σ li * Y t (Sum.inl 0) ω + 0 * Y t (Sum.inl 0) ω +
          0 * Y t (Sum.inl 0) ω := by
      funext ω'
      have h1 := congrFun (hl t).1 ω'
      have h2 := congrFun (hl t).2 ω'
      simp only [InflationInertiaRules.ALi]
      rw [← h1, ← h2]
      simp only [iB, A2c]
      ring
    have hq0 : InflationInertiaRules.qtil 0 κ σ 0 li (πB p1 Y) (xB x1 Y) (t + 2) ω =
        κ * σ / li * Y t (Sum.inl 0) ω := by
      simp only [InflationInertiaRules.qtil, zero_div, zero_mul, add_zero, sub_zero]
      rfl
    unfold InflationInertiaRules.fbig
    rw [hALi, E_comb 𝔼 (t + 2) _ _ _ _ _ _ _ _ (ha t _) (ha t _) (ha t _), hq0]
    simp only [Pos.c0]
    ring

variable (β κ σ li)

/-- Woodford (2003), p. 593 (tool), at `γ = 0`: with no disturbance and `i* = 0` the forcing
vanishes. -/
theorem wZ_zero : wZ β σ (fun (_ : ℕ) (_ : Ω) => 0) (fun _ _ => 0) 0 = fun _ _ _ => 0 := by
  funext s k ω
  rcases k with j | j
  · simp [wZ, Fvec, mulVec, dotProduct, Fin.sum_univ_two]
  · rfl

/-- **Woodford (2003), App. C.1, fn 2 (genericity) for the rule system at `γ = 0`, `λₓ = 0`, from
the uniqueness theorem** `InflationInertiaRules.rule_system_unique` (perfect foresight). -/
theorem genericX (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hli : 0 < li) :
    GenericX (Abk β κ σ li) := by
  intro v hv hx
  have hY : GeneralBKCopy.Equil (Prop84General.shiftES perfectForesight 2) (Abk β κ σ li)
      (wZ β σ (fun (_ : ℕ) (_ : Unit) => 0) (fun _ _ => 0) 0)
      (x0vec (fun _ => 0) (fun _ => 0) 0) (fun t k _ => ((Abk β κ σ li) ^ t *ᵥ v) k) := by
    rw [wZ_zero]
    have hx0 : x0vec (fun (_ : Unit) => (0 : ℝ)) (fun _ => 0) 0 = fun j _ => v (Sum.inr j) := by
      funext j ω
      fin_cases j <;> simp [x0vec, hx]
    rw [hx0]
    exact TidyR5aExogenousInstrument.BK.orbit_equil _ hv
  obtain ⟨hAS, hIS, hEu⟩ := eqs_of_equil hβ0.ne' (p1 := fun _ => 0) (x1 := fun _ => 0) hY
  obtain ⟨hAS0, hIS0, hEu0⟩ := Pos.zero_sol β 0 κ σ li
  obtain ⟨C, hC⟩ := hv
  set B := (|Pos.c0 κ σ li| + |A2c β κ σ| + |β⁻¹|) * max C 0 + max C 0 with hB
  have hB0 : 0 ≤ max C 0 := le_max_right _ _
  have hBC : max C 0 ≤ B := by
    rw [hB]
    have : 0 ≤ (|Pos.c0 κ σ li| + |A2c β κ σ| + |β⁻¹|) * max C 0 := by positivity
    linarith
  have hb : ∀ {g : ℕ → Unit → ℝ}, (∀ k ω, |g k ω| ≤ B) → InflationInertiaRules.Bnd g :=
    fun hg => ⟨B, hB0.trans hBC, hg⟩
  have hπb : InflationInertiaRules.Bnd (πB (fun _ => 0)
      (fun t k (_ : Unit) => ((Abk β κ σ li) ^ t *ᵥ v) k)) := by
    refine hb fun k ω => ?_
    rcases k with _ | _ | s
    · simp only [πB, abs_zero]
      exact hB0.trans hBC
    · simp only [πB, abs_zero]
      exact hB0.trans hBC
    · exact ((hC s _).trans (le_max_left _ _)).trans hBC
  have hxb : InflationInertiaRules.Bnd (xB (fun _ => 0)
      (fun t k (_ : Unit) => ((Abk β κ σ li) ^ t *ᵥ v) k)) := by
    refine hb fun k ω => ?_
    rcases k with _ | _ | s
    · simp only [xB, abs_zero]
      exact hB0.trans hBC
    · simp only [xB, abs_zero]
      exact hB0.trans hBC
    · exact ((hC s _).trans (le_max_left _ _)).trans hBC
  have hib : InflationInertiaRules.Bnd (iB β κ σ li 0 (fun _ => 0) (fun _ => 0)
      (fun t k (_ : Unit) => ((Abk β κ σ li) ^ t *ᵥ v) k)) := by
    refine hb fun k ω => ?_
    rcases k with _ | _ | s
    · simp only [iB, abs_zero]
      exact hB0.trans hBC
    · simp only [iB, abs_zero]
      exact hB0.trans hBC
    · simp only [iB, add_zero]
      have h1 := (hC s (Sum.inl 0)).trans (le_max_left C 0)
      have h2 := (hC s (Sum.inr 0)).trans (le_max_left C 0)
      have h3 := (hC s (Sum.inr 1)).trans (le_max_left C 0)
      calc |Pos.c0 κ σ li * ((Abk β κ σ li) ^ s *ᵥ v) (Sum.inl 0) +
            A2c β κ σ * ((Abk β κ σ li) ^ s *ᵥ v) (Sum.inr 0) -
            β⁻¹ * ((Abk β κ σ li) ^ s *ᵥ v) (Sum.inr 1)|
          ≤ |Pos.c0 κ σ li| * max C 0 + |A2c β κ σ| * max C 0 + |β⁻¹| * max C 0 := by
            refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
              (add_le_add ?_ ?_)) ?_) <;> rw [abs_mul] <;>
              exact mul_le_mul_of_nonneg_left ‹_› (abs_nonneg _)
        _ ≤ B := by rw [hB]; nlinarith
  have h0b : InflationInertiaRules.Bnd (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) :=
    ⟨0, le_rfl, fun _ _ => by simp⟩
  have key := InflationInertiaRules.rule_system_unique perfectForesight perfectForesight_pullOut
    ExpectationTools.perfectForesight_faithful hβ0 hβ1 hκ.ne' hσ.ne' hli (le_refl 0)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    hπb hxb hib h0b h0b h0b hAS hAS0 hIS hIS0 hEu hEu0 (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
  funext k
  rcases k with j | j
  · obtain ⟨e1, e2, -⟩ := key 2 (by norm_num) ()
    fin_cases j
    · simpa [πB] using e1
    · simpa [xB] using e2
  · exact hx j

/-- **Woodford (2003), p. 593: existence at `λₓ = 0` for `γ = 0`.** For every bounded adapted
disturbance and every bounded history known at the right dates, the rule system (2.6), (3.1),
(3.16) with `γ = 0`, `λₓ = 0` has a bounded adapted solution with that history (any expectation
system): the Blanchard–Kahn equilibrium of `Abk` from date 2 on, with the history glued in. -/
theorem exists_lx0 (c : IRuleBasic.Calib) (hlx : c.lx = 0) (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hσ : 0 < c.σ) (hκ : 0 < c.κ) (hli : 0 < c.li) (𝔼 : ExpectationSystem Ω) {u rn : ℕ → Ω → ℝ}
    (hub : InflationInertiaRules.Bnd u) (hua : 𝔼.Adapted u) (hrb : InflationInertiaRules.Bnd rn)
    (hra : 𝔼.Adapted rn) {p1 x1 i1 i0 : Ω → ℝ} (hh : TidyRuleSystem.History 𝔼 p1 x1 i1 i0) :
    ∃ π x i, TidyRuleSystem.RuleSol 𝔼 c 0 u rn p1 x1 i1 i0 π x i := by
  have hβ := hβ0.ne'
  obtain ⟨hnu, hcount⟩ := bk_roots c.β c.κ c.σ c.li hβ0 hβ1 hσ hκ hli
  have hd : Module.finrank ℝ (boundedOrbits (Abk c.β c.κ c.σ c.li)) = Fintype.card (Fin 2) := by
    rw [BKInvariantSplit.finrank_eq_stableCount hnu, hcount, Fintype.card_fin]
  have hDet := GeneralBKCopy.determinate_of (Prop84General.shiftES 𝔼 2) hnu hd
    (genericX c.β c.κ c.σ c.li hβ0 hβ1 hσ hκ hli)
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  obtain ⟨Cu, hCu0, hCu⟩ := hub
  obtain ⟨Cr, hCr0, hCr⟩ := hrb
  -- the forcing
  obtain ⟨Kw, hKw⟩ := GeneralFOC.exists_bound_mulVec (Pinv c.β c.σ)
    (Cu + c.σ * (|c.istar| + Cr))
  have hwb : BKForward.BoundedV (wZ c.β c.σ u rn c.istar) := by
    refine ⟨max Kw 0, fun s k ω => ?_⟩
    rcases k with j | j
    · refine (hKw _ (fun i => ?_) j).trans (le_max_left _ _)
      fin_cases i
      · simp only [Fvec]
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, abs_neg]
        nlinarith [hCu (s + 2) ω, abs_nonneg c.istar]
      · simp only [Fvec]
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, abs_mul,
          abs_of_pos hσ]
        have := abs_sub c.istar (rn (s + 2) ω)
        nlinarith [hCr (s + 2) ω]
    · simp [wZ]
  have hwa : BKForward.AdaptedV (Prop84General.shiftES 𝔼 2) (wZ c.β c.σ u rn c.istar) := by
    intro s k
    change 𝔼.E (s + 2) _ = _
    rcases k with j | j
    · have e : wZ c.β c.σ u rn c.istar s (Sum.inl j) = fun ω =>
          (Pinv c.β c.σ j 0) * (-u (s + 2) ω) + (Pinv c.β c.σ j 1 * c.σ) * (-rn (s + 2) ω) +
            0 * (0 : Ω → ℝ) ω + Pinv c.β c.σ j 1 * c.σ * c.istar := by
        funext ω
        simp [wZ, Fvec, mulVec, dotProduct, Fin.sum_univ_two]
        ring
      have hu' : 𝔼.E (s + 2) (fun ω => -u (s + 2) ω) = fun ω => -u (s + 2) ω := by
        change 𝔼.E (s + 2) (-(u (s + 2))) = -(u (s + 2))
        rw [map_neg, hua]
      have hr' : 𝔼.E (s + 2) (fun ω => -rn (s + 2) ω) = fun ω => -rn (s + 2) ω := by
        change 𝔼.E (s + 2) (-(rn (s + 2))) = -(rn (s + 2))
        rw [map_neg, hra]
      rw [e]
      exact TidyRuleSystem.known_lin3 𝔼 hu' hr' (𝔼.const (s + 2) 0) _ _ _ _
    · exact 𝔼.const _ 0
  have hx0k : ∀ j, (Prop84General.shiftES 𝔼 2).E 0 (x0vec i1 i0 c.istar j) =
      x0vec i1 i0 c.istar j := by
    intro j
    change 𝔼.E (0 + 2) _ = _
    have k1 : ∀ f : Ω → ℝ, 𝔼.E 1 f = f → 𝔼.E 2 f = f := fun f hf => by
      rw [← hf, 𝔼.known (by norm_num : 1 ≤ 2)]
    have k0 : ∀ f : Ω → ℝ, 𝔼.E 0 f = f → 𝔼.E 2 f = f := fun f hf => by
      rw [← hf, 𝔼.known (by norm_num : 0 ≤ 2)]
    have hsub : ∀ f : Ω → ℝ, 𝔼.E 2 f = f → 𝔼.E 2 (fun ω => f ω - c.istar) =
        fun ω => f ω - c.istar := fun f hf => by
      change 𝔼.E 2 (f - fun _ => c.istar) = f - fun _ => c.istar
      rw [map_sub, hf, 𝔼.const]
    rw [zero_add]
    fin_cases j
    · exact hsub i1 (k1 i1 hi1)
    · exact hsub i0 (k0 i0 hi0)
  have hx0b : ∃ M, ∀ j ω, |x0vec i1 i0 c.istar j ω| ≤ M := by
    refine ⟨K + |c.istar|, fun j ω => ?_⟩
    obtain ⟨-, -, k3, k4⟩ := hK ω
    fin_cases j
    · simp only [x0vec]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [abs_sub (i1 ω) c.istar]
    · simp only [x0vec]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [abs_sub (i0 ω) c.istar]
  obtain ⟨Y, hY, -⟩ := hDet _ hwb hwa _ hx0k hx0b
  obtain ⟨hAS, hIS, hEu⟩ := eqs_of_equil hβ (p1 := p1) (x1 := x1) hY
  have ha : ∀ s k, 𝔼.E (s + 2) (Y s k) = Y s k := hY.2.1
  obtain ⟨M, hM⟩ := hY.2.2.2.2
  set L := |Pos.c0 c.κ c.σ c.li| + |A2c c.β c.κ c.σ| + |c.β⁻¹| with hL
  refine ⟨πB p1 Y, xB x1 Y, iB c.β c.κ c.σ c.li c.istar i1 i0 Y, fun k => ?_, fun k => ?_,
    fun k => ?_, ⟨max (max M K) 0, le_max_right _ _, fun k ω => ?_⟩,
    ⟨max (max M K) 0, le_max_right _ _, fun k ω => ?_⟩,
    ⟨(L + 1) * max (max M K) 0 + |c.istar|, by positivity, fun k ω => ?_⟩, hAS, hIS, ?_, rfl,
    rfl, rfl, rfl⟩
  · rcases k with _ | _ | s
    · exact 𝔼.const 0 0
    · exact hp1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact 𝔼.const 0 0
    · exact hx1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact hi0
    · exact hi1
    · have e : iB c.β c.κ c.σ c.li c.istar i1 i0 Y (s + 2) = fun ω =>
          Pos.c0 c.κ c.σ c.li * Y s (Sum.inl 0) ω + A2c c.β c.κ c.σ * Y s (Sum.inr 0) ω +
            -c.β⁻¹ * Y s (Sum.inr 1) ω + c.istar := by
        funext ω
        simp only [iB]
        ring
      rw [e]
      exact TidyRuleSystem.known_lin3 𝔼 (ha s _) (ha s _) (ha s _) _ _ _ _
  · rcases k with _ | _ | s
    · simp [πB]
    · exact (hK ω).1.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hM s _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rcases k with _ | _ | s
    · simp [xB]
    · exact (hK ω).2.1.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hM s _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h0 : 0 ≤ max (max M K) 0 := le_max_right _ _
    have hL0 : 0 ≤ L := by positivity
    have hLm : 0 ≤ L * max (max M K) 0 := mul_nonneg hL0 h0
    rcases k with _ | _ | s
    · have := (hK ω).2.2.2.trans ((le_max_right M K).trans (le_max_left _ 0))
      change |i0 ω| ≤ _
      nlinarith [abs_nonneg c.istar]
    · have := (hK ω).2.2.1.trans ((le_max_right M K).trans (le_max_left _ 0))
      change |i1 ω| ≤ _
      nlinarith [abs_nonneg c.istar]
    · have h1 := (hM s (Sum.inl 0) ω).trans ((le_max_left M K).trans (le_max_left _ 0))
      have h2 := (hM s (Sum.inr 0) ω).trans ((le_max_left M K).trans (le_max_left _ 0))
      have h3 := (hM s (Sum.inr 1) ω).trans ((le_max_left M K).trans (le_max_left _ 0))
      change |Pos.c0 c.κ c.σ c.li * Y s (Sum.inl 0) ω + A2c c.β c.κ c.σ * Y s (Sum.inr 0) ω -
        c.β⁻¹ * Y s (Sum.inr 1) ω + c.istar| ≤ _
      have hb : |Pos.c0 c.κ c.σ c.li * Y s (Sum.inl 0) ω + A2c c.β c.κ c.σ * Y s (Sum.inr 0) ω -
          c.β⁻¹ * Y s (Sum.inr 1) ω| ≤ L * max (max M K) 0 := by
        calc _ ≤ |Pos.c0 c.κ c.σ c.li| * max (max M K) 0 +
              |A2c c.β c.κ c.σ| * max (max M K) 0 + |c.β⁻¹| * max (max M K) 0 := by
              refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
                (add_le_add ?_ ?_)) ?_) <;> rw [abs_mul] <;>
                exact mul_le_mul_of_nonneg_left ‹_› (abs_nonneg _)
          _ = L * max (max M K) 0 := by rw [hL]; ring
      have := abs_add_le (Pos.c0 c.κ c.σ c.li * Y s (Sum.inl 0) ω +
        A2c c.β c.κ c.σ * Y s (Sum.inr 0) ω - c.β⁻¹ * Y s (Sum.inr 1) ω) c.istar
      nlinarith
  · intro t
    rw [hlx]
    exact hEu t

end Zero

/-! ### Every `0 ≤ γ ≤ 1` -/

/-- **Woodford (2003), p. 593: existence for the rule system at `λₓ = 0`, every `0 ≤ γ ≤ 1`.**
For every bounded adapted disturbance and every bounded history `(π₁, x₁, i₁, i₀)` known at the
right dates, (2.6), (3.1), (3.16) with `λₓ = 0` has a bounded adapted solution with that history
(any expectation system). -/
theorem rule_system_exists_lx0 (c : IRuleBasic.Calib) (hlx : c.lx = 0) (hβ0 : 0 < c.β)
    (hβ1 : c.β < 1) (hσ : 0 < c.σ) (hκ : 0 < c.κ) (hli : 0 < c.li) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω) {u rn : ℕ → Ω → ℝ}
    (hub : InflationInertiaRules.Bnd u) (hua : 𝔼.Adapted u) (hrb : InflationInertiaRules.Bnd rn)
    (hra : 𝔼.Adapted rn) {p1 x1 i1 i0 : Ω → ℝ} (hh : TidyRuleSystem.History 𝔼 p1 x1 i1 i0) :
    ∃ π x i, TidyRuleSystem.RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i := by
  rcases hγ0.lt_or_eq with h | h
  · exact Pos.exists_lx0 (γ := γ) c hlx ⟨hσ, hκ, hβ0, hβ1, h, hγ1⟩ hli 𝔼 hub hua hrb hra hh
  · subst h
    exact Zero.exists_lx0 c hlx hβ0 hβ1 hσ hκ hli 𝔼 hub hua hrb hra hh

/-- **Woodford (2003), p. 593: the rule system (3.16) is determinate at `λₓ = 0` for every
`γ ∈ [0, 1]`.** With faithful expectations and the pull-out property, for every bounded adapted
disturbance and every bounded history known at the right dates, (2.6), (3.1), (3.16) with
`λₓ = 0` has a bounded adapted solution with that history, and every bounded adapted solution with
that history coincides with it at every date `≥ 1` (`InflationInertiaRules.rule_system_unique`). -/
theorem rule_system_existsUnique_lx0 (c : IRuleBasic.Calib) (hlx : c.lx = 0) (hβ0 : 0 < c.β)
    (hβ1 : c.β < 1) (hσ : 0 < c.σ) (hκ : 0 < c.κ) (hli : 0 < c.li) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω) (hpull : 𝔼.PullOut)
    (hfaith : ExpectationTools.Faithful 𝔼) {u rn : ℕ → Ω → ℝ}
    (hub : InflationInertiaRules.Bnd u) (hua : 𝔼.Adapted u) (hrb : InflationInertiaRules.Bnd rn)
    (hra : 𝔼.Adapted rn) {p1 x1 i1 i0 : Ω → ℝ} (hh : TidyRuleSystem.History 𝔼 p1 x1 i1 i0) :
    ∃ π x i, TidyRuleSystem.RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i ∧
      ∀ π' x' i', TidyRuleSystem.RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π' x' i' →
        ∀ k, 1 ≤ k → π' k = π k ∧ x' k = x k ∧ i' k = i k := by
  obtain ⟨π, x, i, hsol⟩ :=
    rule_system_exists_lx0 c hlx hβ0 hβ1 hσ hκ hli hγ0 hγ1 𝔼 hub hua hrb hra hh
  refine ⟨π, x, i, hsol, fun π' x' i' hsol' k hk => ?_⟩
  obtain ⟨ha, hb, hc3, b1, b2, b3, hAS, hIS, hE, e1, e2, e3, e4⟩ := hsol
  obtain ⟨ha', hb', hc3', b1', b2', b3', hAS', hIS', hE', e1', e2', e3', e4'⟩ := hsol'
  have key := InflationInertiaRules.rule_system_unique 𝔼 hpull hfaith hβ0 hβ1 hκ.ne' hσ.ne'
    hli (le_of_eq hlx.symm) ha' hb' hc3' ha hb hc3 b1' b2' b3' b1 b2 b3 hAS' hAS hIS' hIS hE' hE
    (fun ω => by rw [e1, e1']) (fun ω => by rw [e2, e2']) (fun ω => by rw [e3, e3'])
    (fun ω => by rw [e4, e4']) k hk
  exact ⟨funext fun ω => (key ω).1, funext fun ω => (key ω).2.1, funext fun ω => (key ω).2.2⟩

/-- **Woodford (2003), p. 593: the rule system (3.16) is determinate for every `λₓ ≥ 0` and every
`γ ∈ [0, 1]`** (`TidyRuleSystem.rule_system_existsUnique` for `λₓ > 0`,
`rule_system_existsUnique_lx0` for `λₓ = 0`). -/
theorem rule_system_existsUnique_nonneg (c : IRuleBasic.Calib) (hlx : 0 ≤ c.lx) (hβ0 : 0 < c.β)
    (hβ1 : c.β < 1) (hσ : 0 < c.σ) (hκ : 0 < c.κ) (hli : 0 < c.li) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω) (hpull : 𝔼.PullOut)
    (hfaith : ExpectationTools.Faithful 𝔼) {u rn : ℕ → Ω → ℝ}
    (hub : InflationInertiaRules.Bnd u) (hua : 𝔼.Adapted u) (hrb : InflationInertiaRules.Bnd rn)
    (hra : 𝔼.Adapted rn) {p1 x1 i1 i0 : Ω → ℝ} (hh : TidyRuleSystem.History 𝔼 p1 x1 i1 i0) :
    ∃ π x i, TidyRuleSystem.RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π x i ∧
      ∀ π' x' i', TidyRuleSystem.RuleSol 𝔼 c γ u rn p1 x1 i1 i0 π' x' i' →
        ∀ k, 1 ≤ k → π' k = π k ∧ x' k = x k ∧ i' k = i k := by
  rcases hlx.lt_or_eq with h | h
  · exact TidyRuleSystem.rule_system_existsUnique c ⟨hβ0, hβ1, hσ, hκ, h, hli⟩ hγ0 hγ1 𝔼 hpull
      hfaith hub hua hrb hra hh
  · exact rule_system_existsUnique_lx0 c h.symm hβ0 hβ1 hσ hκ hli hγ0 hγ1 𝔼 hpull hfaith hub
      hua hrb hra hh

end Woodford.OptimalPolicyRules.TidyR5aLambdaXZero
