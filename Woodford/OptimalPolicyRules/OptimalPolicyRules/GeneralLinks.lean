/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Prop84General
import OptimalPolicyRules.IRuleForwardIntegrated
import OptimalPolicyRules.QuadraticRoots
import Mathlib.Algebra.Order.Star.Real

/-!
# The general target-criterion machinery specialised to the basic model

Woodford (2003), *Interest and Prices*, Chapter 8: the general framework of §1 (pp. 536–559)
applied to the basic neo-Wicksellian model of §3.1 (pp. 582–591), as the book says it can be
("the examples considered here belong" to the general class, p. 560).

## Main results

* **The model as a general problem.** `nkSys`, `nkProblem`: the aggregate-supply relation (2.1)
  and the IS relation (3.1) are the structural equations (1.1) with `n_Z = 0`,
  `z = (π, x)`, `A₂₂ = [1 −κ; 0 1]` (invertible), `Ẽ = [β 0; σ 1]`, `B₂ = (0, σ)`; the loss (3.2)
  is (1.3) with `τ = (π, x, i)` and `W = diag(1, λₓ, λᵢ) ≻ 0`. `nk_structural_iff`: (1.1) in
  block form is exactly (2.1) and (3.1). `nk_foc_iff`: the general first-order conditions (1.9)
  are exactly (3.3)–(3.5), the multiplier on (2.1) being `φ₂` and the one on (3.1) `φ₁`.
* **Proposition 8.1 for the model.** `nkΛ = [1 σ/β; κ (1+κσ)/β]`, `nkQ = −(A₂₂')⁻¹`:
  `nk_eq120_of_foc` ((1.18) gives (1.20) with these), `nk_homEquiv` (the homogeneous (1.18) and
  (1.20) agree).
* **The criterion (1.23) is the rule (3.7).** `nk_alpha`: `α(L) = det(I − ΛL) =
  1 − (ρ₁ + ρ₂)L + ρ₂L²` with (3.8)'s `ρ₁ = 1 + κσ/β`, `ρ₂ = β⁻¹`; `nk_crit_iff_rule`: the
  general target criterion (1.23) with `α`, `B(L) = adj(I − ΛL)`, `q = Q T̃'W(τ − τ*)` and
  `v = λᵢ(i − i*)` holds at a date `t ≥ 2` iff the instrument rule (3.7) with the coefficients
  (3.8)–(3.9) does; `nk_rule_of_foc`: the general derivation (1.19)–(1.20) ⇒ (1.23) yields (3.7)
  for every solution of the first-order conditions.
* **Proposition 8.3 for the model (Proposition 8.5's superinertia).** `nk_pencilPoly`,
  `nk_assumption83`, `nk_stableCount` (`m = 1`), `nk_no_circle` and `nk_zerosInside`: the general
  Proposition 8.3 gives exactly one zero of `α(L)` inside the unit circle — the root `λ₂ > 1` of
  footnote 35 (`IRuleBasic.fn35_one_root_gt_one`).
* **Proposition 8.4 for the model (Proposition 8.6).** `prop_8_6_from_general`: the general
  Proposition 8.4 (`Prop84General.prop84_from`) with `α₁ = L − λ₂⁻¹`, `α₂ = −λ₂(1 − λ₁L)` gives
  the equivalence of (3.10) and the forward-integrated rule (3.12) from any date `T ≥ 2` on
  (`IRuleForwardIntegrated.G14`, `G15`; the chain-specific `prop_8_6` also covers the initial
  dates with pre-sample values).
* `prop83Claim_false_empty`: the statement `TargetCriterion.Prop83Claim` fails for the basic
  model on the empty sample space (so `Prop83.prop83` needs `Nonempty Ω`).
-/

namespace Woodford.OptimalPolicyRules.GeneralLinks

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ Adjugate
open TargetCriterion (zerosInside fwdOp lagOp)
open TargetCriterion.Prop81
open IRuleBasic (Calib rho1 rho2 phiPi phiX)

variable {Ω : Type*}

/-! ### The basic model as a general linear-quadratic problem -/

/-- Woodford (2003), (2.1) and (3.1) as (1.1), p. 537: `n_Z = 0`, `z = (π, x)`; row `0` is
`β E_tπ_{t+1} = π_t − κx_t − u_t`, row `1` is `σE_tπ_{t+1} + E_tx_{t+1} = x_t + σi_t − σrⁿ_t`. -/
noncomputable def nkSys (c : Calib) (hσ : c.σ ≠ 0) : LinearRESystem Empty (Fin 2) where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := !![1, -c.κ; 0, 1]
  Et := !![c.β, 0; c.σ, 1]
  B2 := ![0, c.σ]
  A22_isUnit := by simp [det_fin_two]
  B2_ne_zero := by
    intro h
    have := congrFun h 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at this
    exact hσ this

/-- Woodford (2003), (3.2) as (1.3)–(1.4), p. 537: the targets `τ = (π, x, i)`. -/
def nkTtil : Matrix (Fin 3) (Empty ⊕ Fin 2) ℝ :=
  Matrix.of fun a col => Sum.elim (fun e => e.elim) (fun j : Fin 2 => if (a : ℕ) = j then 1 else 0)
    col

/-- Woodford (2003), (3.2) as (1.2)–(1.4), p. 537: the basic model's linear-quadratic problem,
`W = diag(1, λₓ, λᵢ) ≻ 0`, `τ* = (0, x*, i*)`. -/
noncomputable def nkProblem (c : Calib) (hc : c.Adm) : LQProblem Empty (Fin 2) (Fin 3) where
  sys := nkSys c hc.2.2.1.ne'
  β := c.β
  β_pos := hc.1
  β_lt_one := hc.2.1
  Ttil := nkTtil
  Ti := ![0, 0, 1]
  W := diagonal ![1, c.lx, c.li]
  τstar := ![0, c.xstar, c.istar]
  W_posDef := PosDef.diagonal fun i => by
    fin_cases i
    · simp
    · simpa using hc.2.2.2.2.1
    · simpa using hc.2.2.2.2.2

/-- Woodford (2003), p. 538: inflation in a plan `y = (Z, z, i)` with `z = (π, x)` (any
predetermined block `Z`: `n_Z = 0` here, `Z = π_{t−1}` in `GeneralLinksInertia`). -/
def piOf {ιZ : Type*} (y : ℕ → Ω → (ιZ ⊕ Fin 2) ⊕ Unit → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => y t ω (Sum.inl (Sum.inr 0))

/-- Woodford (2003), p. 538: the output gap in a plan. -/
def xOf {ιZ : Type*} (y : ℕ → Ω → (ιZ ⊕ Fin 2) ⊕ Unit → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => y t ω (Sum.inl (Sum.inr 1))

/-- Woodford (2003), p. 538: the interest rate in a plan. -/
def iOf {ιZ : Type*} (y : ℕ → Ω → (ιZ ⊕ Fin 2) ⊕ Unit → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => y t ω (Sum.inr ())

/-- Woodford (2003), p. 538: inflation at date `t` as a random variable. -/
theorem piOf_eq {ιZ : Type*} (y : ℕ → Ω → (ιZ ⊕ Fin 2) ⊕ Unit → ℝ) (t : ℕ) :
    piOf y t = fun ω => y t ω (Sum.inl (Sum.inr 0)) := rfl

/-- Woodford (2003), p. 538: the output gap at date `t` as a random variable. -/
theorem xOf_eq {ιZ : Type*} (y : ℕ → Ω → (ιZ ⊕ Fin 2) ⊕ Unit → ℝ) (t : ℕ) :
    xOf y t = fun ω => y t ω (Sum.inl (Sum.inr 1)) := rfl

/-- Woodford (2003), p. 537: the disturbance `c_t = C₂s_t = (−u_t, −σrⁿ_t)` of the basic model. -/
def cNK (c : Calib) (u rn : ℕ → Ω → ℝ) : ℕ → Ω → Fin 2 → ℝ :=
  fun t ω => ![-u t ω, -(c.σ * rn t ω)]

/-- **Woodford (2003), (1.1) for the basic model, p. 537.** The structural equations (1.1) of
`nkSys` are exactly the aggregate-supply relation (2.1) and the IS relation (3.1). -/
theorem nk_structural_iff (c : Calib) (hσ : c.σ ≠ 0) (𝔼 : ExpectationSystem Ω)
    (u rn : ℕ → Ω → ℝ) (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) :
    (nkSys c hσ).Structural 𝔼 (cNK c u rn) 0 y ↔
      ∀ t, IRuleBasic.AS 𝔼 c u (piOf y) (xOf y) t ∧
        IRuleBasic.IS 𝔼 c rn (piOf y) (xOf y) (iOf y) t := by
  have key : ∀ t ω, ((nkSys c hσ).Et *ᵥ EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω =
      (nkSys c hσ).A21 *ᵥ Zpart (y t ω) + (nkSys c hσ).A22 *ᵥ zpart (y t ω) +
        ipart (y t ω) • (nkSys c hσ).B2 + cNK c u rn t ω) ↔
      (piOf y t ω = c.κ * xOf y t ω + c.β * 𝔼.E t (piOf y (t + 1)) ω + u t ω ∧
        xOf y t ω = 𝔼.E t (xOf y (t + 1)) ω -
          c.σ * (iOf y t ω - 𝔼.E t (piOf y (t + 1)) ω - rn t ω)) := by
    intro t ω
    rw [funext_iff, Fin.forall_fin_two]
    simp only [nkSys, cNK, mulVec, dotProduct, Fin.sum_univ_two, EV, zpart, Zpart, ipart,
      piOf_eq, xOf_eq, piOf, xOf, iOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Finset.univ_eq_empty, Finset.sum_empty,
      Matrix.zero_apply]
    constructor
    · rintro ⟨h0, h1⟩
      constructor <;> linarith
    · rintro ⟨h0, h1⟩
      constructor <;> linarith
  constructor
  · intro h t
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have := ((key t ω).mp (h t (Nat.zero_le t) ω).2).1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact this
    · have := ((key t ω).mp (h t (Nat.zero_le t) ω).2).2
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact this
  · intro h t _ ω
    refine ⟨funext fun e => e.elim, (key t ω).mpr ⟨?_, ?_⟩⟩
    · have := congrFun (h t).1 ω
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    · have := congrFun (h t).2 ω
      simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this

/-! ### The first-order conditions (1.9) are (3.3)–(3.5) -/

variable (c : Calib) (hc : c.Adm)

/-- Woodford (2003), p. 552: `A'` for the basic model, by blocks. -/
theorem nk_Ahat_transpose_mulVec (hσ : c.σ ≠ 0) (v : Empty ⊕ Fin 2 → ℝ) :
    (nkSys c hσ).Ahatᵀ *ᵥ v =
      Sum.elim (fun e => e.elim) ![v (Sum.inr 0), -c.κ * v (Sum.inr 0) + v (Sum.inr 1)] := by
  funext r
  rcases r with e | j
  · exact e.elim
  · fin_cases j <;>
      simp [nkSys, LinearRESystem.Ahat, mulVec, dotProduct, Fin.sum_univ_two]

/-- Woodford (2003), p. 552: `Î'` for the basic model, by blocks. -/
theorem nk_Ihat_transpose_mulVec (hσ : c.σ ≠ 0) (v : Empty ⊕ Fin 2 → ℝ) :
    (nkSys c hσ).Ihatᵀ *ᵥ v =
      Sum.elim (fun e => e.elim) ![c.β * v (Sum.inr 0) + c.σ * v (Sum.inr 1), v (Sum.inr 1)] := by
  funext r
  rcases r with e | j
  · exact e.elim
  · fin_cases j <;>
      simp [nkSys, LinearRESystem.Ihat, mulVec, dotProduct, Fin.sum_univ_two]

/-- Woodford (2003), p. 553: `T̃'W(τ − τ*) = (π, λₓ(x − x*))` for the basic model. -/
theorem nk_xvec (v : (Empty ⊕ Fin 2) ⊕ Unit → ℝ) :
    (nkProblem c hc).Ttilᵀ *ᵥ ((nkProblem c hc).W *ᵥ ((nkProblem c hc).T *ᵥ v -
      (nkProblem c hc).τstar)) =
      Sum.elim (fun e => e.elim)
        ![v (Sum.inl (Sum.inr 0)), c.lx * (v (Sum.inl (Sum.inr 1)) - c.xstar)] := by
  funext r
  rcases r with e | j
  · exact e.elim
  · fin_cases j <;>
      simp [nkProblem, nkTtil, LQProblem.T, mulVec, dotProduct, Fin.sum_univ_three,
        Fintype.sum_sum_type, diagonal_apply]

/-- Woodford (2003), p. 553: `T_i'W(τ − τ*) = λᵢ(i − i*)` for the basic model. -/
theorem nk_vvec (v : (Empty ⊕ Fin 2) ⊕ Unit → ℝ) :
    (nkProblem c hc).Ti ⬝ᵥ ((nkProblem c hc).W *ᵥ ((nkProblem c hc).T *ᵥ v -
      (nkProblem c hc).τstar)) = c.li * (v (Sum.inr ()) - c.istar) := by
  simp [nkProblem, nkTtil, LQProblem.T, mulVec, dotProduct, Fin.sum_univ_three,
    Fintype.sum_sum_type, diagonal_apply]

/-- Woodford (2003), p. 584: the multiplier `φ₁` on the IS relation (3.1), `M_t`'s second entry. -/
def nkPhi1 (φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ) : ℕ → Ω → ℝ := fun t ω => φ (t + 1) ω (Sum.inr 1)

/-- Woodford (2003), p. 584: the multiplier `φ₂` on the AS relation (2.1), `M_t`'s first
entry. -/
def nkPhi2 (φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ) : ℕ → Ω → ℝ := fun t ω => φ (t + 1) ω (Sum.inr 0)

/-- Woodford (2003), p. 584 (tool): with the pre-sample multipliers `φ_{t₀−1}` given, the lagged
multiplier is the `M_{t−1}`-block of `φ_t`. -/
theorem lag_nkPhi {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} {j : Fin 2} {h : ℝ}
    (hinit : ∀ ω, φ 0 ω (Sum.inr j) = h) (t : ℕ) (ω : Ω) :
    IRuleBasic.lag h (fun s ω => φ (s + 1) ω (Sum.inr j)) t ω = φ t ω (Sum.inr j) := by
  cases t with
  | zero => exact (hinit ω).symm
  | succ t => rfl

/-- Woodford (2003), p. 584 (tool): `φ₁_{t−1}` is the second entry of `M_{t−1}`. -/
theorem lag_nkPhi1 {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} {h : ℝ}
    (hinit : ∀ ω, φ 0 ω (Sum.inr 1) = h) (t : ℕ) (ω : Ω) :
    IRuleBasic.lag h (nkPhi1 φ) t ω = φ t ω (Sum.inr 1) :=
  lag_nkPhi hinit t ω

/-- Woodford (2003), p. 584 (tool): `φ₂_{t−1}` is the first entry of `M_{t−1}`. -/
theorem lag_nkPhi2 {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} {h : ℝ}
    (hinit : ∀ ω, φ 0 ω (Sum.inr 0) = h) (t : ℕ) (ω : Ω) :
    IRuleBasic.lag h (nkPhi2 φ) t ω = φ t ω (Sum.inr 0) :=
  lag_nkPhi hinit t ω

/-- Woodford (2003), (1.9) at one date for the basic model, pp. 541, 552 and 584: with `M_t`
known at `t`, the general first-order conditions at `(t, ω)` are the three scalar equations
(3.3)–(3.5) in `φ_t = M_{t−1}` and `φ_{t+1} = M_t`. -/
theorem nk_foc_at_iff (𝔼 : ExpectationSystem Ω) (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ)
    {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} (hmφ : MultiplierMeas 𝔼 φ) (t : ℕ) (ω : Ω) :
    ((nkProblem c hc).sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
      (nkProblem c hc).Tᵀ *ᵥ ((nkProblem c hc).W *ᵥ ((nkProblem c hc).T *ᵥ y t ω -
        (nkProblem c hc).τstar)) - (nkProblem c hc).β⁻¹ •
          ((nkProblem c hc).sys.Itilᵀ *ᵥ φ t ω) = 0) ↔
      (piOf y t ω - c.σ / c.β * φ t ω (Sum.inr 1) + nkPhi2 φ t ω - φ t ω (Sum.inr 0) = 0 ∧
        c.lx * (xOf y t ω - c.xstar) + nkPhi1 φ t ω - c.β⁻¹ * φ t ω (Sum.inr 1) -
          c.κ * nkPhi2 φ t ω = 0 ∧
        c.li * (iOf y t ω - c.istar) + c.σ * nkPhi1 φ t ω = 0) := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hE : ∀ t j ω, EV 𝔼 t (φ (t + 1)) ω (Sum.inr j) = φ (t + 1) ω (Sum.inr j) :=
    fun t j ω => congrFun (hmφ t j) ω
  rw [foc_iff_split _ hmφ y t ω, funext_iff, Sum.forall, Fin.forall_fin_two]
  have hA := nk_Ahat_transpose_mulVec c hc.2.2.1.ne' (EV 𝔼 t (φ (t + 1)) ω)
  have hI := nk_Ihat_transpose_mulVec c hc.2.2.1.ne' (φ t ω)
  have hx := nk_xvec c hc (y t ω)
  have hv := nk_vvec c hc (y t ω)
  simp only [nkProblem] at hA hI hx hv ⊢
  rw [hA, hI, hx, hv]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, hE, nkPhi1, nkPhi2, piOf, xOf,
    iOf, Mpart, nkSys, dotProduct, Fin.sum_univ_two, Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨⟨-, h0, h1⟩, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · field_simp at h0 ⊢
      linarith
    · linarith
    · linarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨fun e => e.elim, ?_, ?_⟩, ?_⟩
    · field_simp at h0 ⊢
      linarith
    · linarith
    · linarith

/-- **Woodford (2003), (1.9) for the basic model, p. 541 and p. 584.** For multipliers with
`M_t` known at `t` and given pre-sample multipliers, the general first-order conditions (1.9) of
`nkProblem` hold at every date iff (3.3), (3.4) and (3.5) do, with `φ₁` the multiplier on (3.1)
and `φ₂` the one on (2.1). -/
theorem nk_foc_iff (𝔼 : ExpectationSystem Ω) (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ)
    {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} (hmφ : MultiplierMeas 𝔼 φ) {φ1h φ2h : ℝ}
    (h1 : ∀ ω, φ 0 ω (Sum.inr 1) = φ1h) (h2 : ∀ ω, φ 0 ω (Sum.inr 0) = φ2h) :
    PFOC (nkProblem c hc) 𝔼 0 y φ ↔
      ∀ t, IRuleBasic.FOC3 c (piOf y) (nkPhi1 φ) (nkPhi2 φ) φ1h φ2h t ∧
        IRuleBasic.FOC4 c (xOf y) (nkPhi1 φ) (nkPhi2 φ) φ1h t ∧
        IRuleBasic.FOC5 c (iOf y) (nkPhi1 φ) t := by
  have key := nk_foc_at_iff c hc 𝔼 y hmφ
  constructor
  · intro H t
    have hk := fun ω => (key t ω).mp (H t (Nat.zero_le t) ω)
    refine ⟨funext fun ω => ?_, funext fun ω => ?_, funext fun ω => ?_⟩
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [lag_nkPhi1 h1, lag_nkPhi2 h2]
      exact (hk ω).1
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [lag_nkPhi1 h1]
      exact (hk ω).2.1
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact (hk ω).2.2
  · intro H t _ ω
    refine (key t ω).mpr ⟨?_, ?_, ?_⟩
    · have := congrFun (H t).1 ω
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [lag_nkPhi1 h1, lag_nkPhi2 h2] at this
      exact this
    · have := congrFun (H t).2.1 ω
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [lag_nkPhi1 h1] at this
      exact this
    · have := congrFun (H t).2.2 ω
      simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] using this

/-! ### Proposition 8.1 for the basic model -/

/-- Woodford (2003), (1.20), p. 553, for the basic model: `Λ = β⁻¹(A₂₂')⁻¹Ẽ' =
[1 σ/β; κ (1+κσ)/β]` (multipliers ordered `(φ₂, φ₁)`: AS, IS). -/
noncomputable def nkΛ : Matrix (Fin 2) (Fin 2) ℝ := !![1, c.σ / c.β; c.κ, (1 + c.κ * c.σ) / c.β]

/-- Woodford (2003), (1.20), p. 553, for the basic model: `Q(L⁻¹) = −(A₂₂')⁻¹` (no leads). -/
def nkQ : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; -c.κ, -1]

/-- Woodford (2003), p. 553: the forcing `T̃'W(τ_t − τ*) = (π_t, λₓ(x_t − x*))` of the basic
model. -/
def nkX (π x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 2 → ℝ := ![π t ω, c.lx * (x t ω - c.xstar)]

/-- Woodford (2003), p. 553: `Q = −(A₂₂')⁻¹` for the basic model. -/
theorem nkQ_eq (hσ : c.σ ≠ 0) : nkQ c = -((nkSys c hσ).A22ᵀ)⁻¹ := by
  rw [eq_comm, neg_eq_iff_eq_neg, inv_eq_left_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nkQ, nkSys, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Woodford (2003), (1.18) ⟹ (1.20), p. 553, for the basic model.** Along any solution of the
first-order conditions (with `M_t` known at `t`) the multipliers obey
`M_t = Λ M_{t−1} + Q T̃'W(τ_t − τ*)` with `Λ = nkΛ`, `Q = nkQ`. -/
theorem nk_eq120_of_foc (𝔼 : ExpectationSystem Ω) (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ)
    {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} (hmφ : MultiplierMeas 𝔼 φ)
    (H : PFOC (nkProblem c hc) 𝔼 0 y φ) (t : ℕ) (ω : Ω) :
    Mpart (φ (t + 1) ω) = nkΛ c *ᵥ Mpart (φ t ω) + nkQ c *ᵥ nkX c (piOf y) (xOf y) t ω := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  obtain ⟨h0, h1, -⟩ := (nk_foc_at_iff c hc 𝔼 y hmφ t ω).mp (H t (Nat.zero_le t) ω)
  simp only [nkPhi1, nkPhi2] at h0 h1
  funext r
  fin_cases r
  · simp [Mpart, nkΛ, nkQ, nkX, dotProduct, Fin.sum_univ_two]
    field_simp at h0 ⊢
    linarith
  · simp [Mpart, nkΛ, nkQ, nkX, dotProduct, Fin.sum_univ_two]
    field_simp at h0 h1 ⊢
    linear_combination h1 + c.κ * h0

/-- **Woodford (2003), Proposition 8.1 for the basic model (homogeneous part).** A sequence solves
the homogeneous (1.18) of `nkSys` iff it solves the homogeneous (1.20) with `Λ = nkΛ` (there is no
predetermined block, so (1.21) is empty). -/
theorem nk_homEquiv (hσ : c.σ ≠ 0) (hβ : c.β ≠ 0) :
    Prop83.HomEquiv (nkSys c hσ) c.β (nkΛ c) 0 := by
  intro h _
  refine forall_congr' fun t => ?_
  rw [nk_Ahat_transpose_mulVec, nk_Ihat_transpose_mulVec, funext_iff, Sum.forall,
    Fin.forall_fin_two, funext_iff, Fin.forall_fin_two]
  simp only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Mpart, nkΛ, mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val']
  constructor
  · rintro ⟨-, h0, h1⟩
    refine ⟨⟨?_, ?_⟩, funext fun e => e.elim⟩
    · field_simp at h0 ⊢
      linarith
    · field_simp at h0 h1 ⊢
      linear_combination h1 + c.κ * h0
  · rintro ⟨⟨h0, h1⟩, -⟩
    refine ⟨fun e => e.elim, ?_, ?_⟩
    · field_simp at h0 ⊢
      linarith
    · field_simp at h0 h1 ⊢
      linear_combination h1 - c.κ * h0
/-! ### The target criterion (1.23) is the instrument rule (3.7) -/

/-- **Woodford (2003), p. 553 and (3.8), p. 584: `α(L) = det(I − ΛL) = 1 − (ρ₁ + ρ₂)L + ρ₂L²`**
for the basic model, with `ρ₁ = 1 + κσ/β`, `ρ₂ = β⁻¹`. -/
theorem nk_alpha (hβ : c.β ≠ 0) :
    alpha (nkΛ c) = 1 - C (rho1 c.β c.σ c.κ + rho2 c.β) * X + C (rho2 c.β) * X ^ 2 := by
  have e1 : rho1 c.β c.σ c.κ + rho2 c.β = 1 + (1 + c.κ * c.σ) / c.β := by
    unfold rho1 rho2
    field_simp
    ring
  have e2 : rho2 c.β = 1 * ((1 + c.κ * c.σ) / c.β) - c.σ / c.β * c.κ := by
    unfold rho2
    field_simp
    ring
  rw [e1, e2, alpha, lagMat, det_fin_two]
  simp only [nkΛ, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  simp only [Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, one_ne_zero,
    C_sub, C_mul, C_add, map_one]
  norm_num
  ring

/-- Woodford (2003), p. 553 and fn 16, p. 555: the coefficient matrices of
`B(L) = adj(I − ΛL)` for the basic model: `B₀ = I`, `B₁ = [−(1+κσ)/β σ/β; κ −1]`, `B₂ = 0`. -/
theorem nk_Bc :
    TargetCriterion.Lag.Bc (Bpoly (nkΛ c)) 0 = 1 ∧
      TargetCriterion.Lag.Bc (Bpoly (nkΛ c)) 1 =
        !![-((1 + c.κ * c.σ) / c.β), c.σ / c.β; c.κ, -1] ∧
      TargetCriterion.Lag.Bc (Bpoly (nkΛ c)) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [TargetCriterion.Lag.Bc, Bpoly, adjugate_fin_two, lagMat, nkΛ, coeff_one, coeff_X,
        coeff_C]

/-- Woodford (2003), p. 553 (tool): a `2 × 2` matrix times a vector. -/
theorem mulVec_two (a b d e : ℝ) (v : Fin 2 → ℝ) :
    !![a, b; d, e] *ᵥ v = ![a * v 0 + b * v 1, d * v 0 + e * v 1] := by
  funext r
  fin_cases r <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- Woodford (2003), p. 553 (tool): `Q v = (−v₀, −κv₀ − v₁)`. -/
theorem nkQ_mulVec (v : Fin 2 → ℝ) : nkQ c *ᵥ v = ![-v 0, -c.κ * v 0 - v 1] := by
  rw [nkQ, mulVec_two]
  congr 1
  · ring
  · congr 1
    ring

/-- Woodford (2003), (1.23), p. 554, for the basic model at a date `t` (with `t − j` truncated
at `0`, as in `TargetCriterion.Crit.crit`): with
`v_t = λᵢ(i_t − i*)` and `q_t = Q T̃'W(τ_t − τ*)`, the criterion is
`λᵢ[(i_t − i*) − (ρ₁+ρ₂)(i_{t−1} − i*) + ρ₂(i_{t−2} − i*)] − κσπ_t − σλₓ(x_t − x_{t−1})`. -/
theorem nk_crit_eq (hσ : c.σ ≠ 0) (hβ : c.β ≠ 0) (π x i : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    TargetCriterion.Crit.crit (alpha (nkΛ c)) (Bpoly (nkΛ c)) 2 (nkSys c hσ).B2
        (fun s ω => c.li * (i s ω - c.istar)) (fun s ω => nkQ c *ᵥ nkX c π x s ω) t ω =
      c.li * ((i t ω - c.istar) - (rho1 c.β c.σ c.κ + rho2 c.β) * (i (t - 1) ω - c.istar) +
        rho2 c.β * (i (t - 2) ω - c.istar)) - c.κ * c.σ * π t ω -
        c.σ * c.lx * (x t ω - x (t - 1) ω) := by
  obtain ⟨hB0, hB1, hB2⟩ := nk_Bc c
  unfold TargetCriterion.Crit.crit
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, hB0, hB1, hB2, nk_alpha c hβ]
  simp only [coeff_add, coeff_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.sub_zero, nkQ_mulVec, mulVec_two]
  simp [nkSys, nkX, dotProduct, Fin.sum_univ_two]
  ring

/-- Woodford (2003), (3.6)–(3.7), p. 584 (tool): after the first date the lag is the previous
value. -/
theorem lag_of_pos {z0 : ℝ} {z : ℕ → Ω → ℝ} {t : ℕ} (ht : 1 ≤ t) :
    IRuleBasic.lag z0 z t = z (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rfl

/-- **Woodford (2003), (1.23) ⟺ (3.7), pp. 554 and 584: the general target criterion is the
optimal instrument rule of the basic model.** At every date `t ≥ 2` (so that no pre-sample value
enters), the criterion (1.23) built from `Λ = nkΛ` (`α = det(I − ΛL)`, `B = adj(I − ΛL)`), the
forcing `q_t = Q T̃'W(τ_t − τ*)` and `v_t = λᵢ(i_t − i*)` holds iff the instrument rule (3.7)
holds with the coefficients (3.8)–(3.9). -/
theorem nk_crit_iff_rule (hc : c.Adm) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ) {t : ℕ}
    (ht : 2 ≤ t) :
    (∀ ω, TargetCriterion.Crit.crit (alpha (nkΛ c)) (Bpoly (nkΛ c)) 2 (nkSys c hc.2.2.1.ne').B2
        (fun s ω => c.li * (i s ω - c.istar)) (fun s ω => nkQ c *ᵥ nkX c π x s ω) t ω = 0) ↔
      IRuleBasic.Rule c xm1 im1 im2 π x i t := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  unfold IRuleBasic.Rule
  rw [funext_iff]
  refine forall_congr' fun ω => ?_
  rw [nk_crit_eq c hc.2.2.1.ne' hβ π x i t ω]
  have h1 : IRuleBasic.lag im1 i t = i (t - 1) := lag_of_pos (by omega)
  have h2 : IRuleBasic.lag im2 (IRuleBasic.lag im1 i) t = i (t - 2) := by
    rw [lag_of_pos (by omega), lag_of_pos (by omega), show t - 1 - 1 = t - 2 by omega]
  have h3 : IRuleBasic.lag xm1 x t = x (t - 1) := lag_of_pos (by omega)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2, h3]
  have key : c.li * ((i t ω - c.istar) - (rho1 c.β c.σ c.κ + rho2 c.β) * (i (t - 1) ω - c.istar)
      + rho2 c.β * (i (t - 2) ω - c.istar)) - c.κ * c.σ * π t ω -
      c.σ * c.lx * (x t ω - x (t - 1) ω) =
      c.li * (i t ω - ((1 - rho1 c.β c.σ c.κ) * c.istar + rho1 c.β c.σ c.κ * i (t - 1) ω +
        rho2 c.β * (i (t - 1) ω - i (t - 2) ω) + phiPi c.σ c.κ c.li * π t ω +
        phiX c.σ c.lx c.li / 4 * (x t ω - x (t - 1) ω))) := by
    unfold phiPi phiX
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_left hli
    linarith
  · intro h
    rw [h]
    ring

/-- **Woodford (2003), pp. 553–554 and 584: the general derivation yields (3.7).** Along every
solution of the general first-order conditions (1.9) of `nkProblem` (with `M_t` known at `t`),
the general argument — (1.19), (1.20) with `Λ = nkΛ`, and premultiplication by `B₂'adj(I − ΛL)`
(`TargetCriterion.Crit.eq123_of_eq119_eq120`) — gives the instrument rule (3.7) at every date
`t ≥ 3`, whatever the pre-sample history. -/
theorem nk_rule_of_foc (𝔼 : ExpectationSystem Ω) (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ)
    {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} (hmφ : MultiplierMeas 𝔼 φ)
    (H : PFOC (nkProblem c hc) 𝔼 0 y φ) (xm1 im1 im2 : ℝ) {t : ℕ} (ht : 3 ≤ t) :
    IRuleBasic.Rule c xm1 im1 im2 (piOf y) (xOf y) (iOf y) t := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  set M : ℕ → Ω → Fin 2 → ℝ := fun s ω => Mpart (φ (s + 1) ω) with hM
  have h119 : ∀ s, 1 ≤ s → ∀ ω, (nkSys c hc.2.2.1.ne').B2 ⬝ᵥ M s ω +
      c.li * (iOf y s ω - c.istar) = 0 := by
    intro s _ ω
    obtain ⟨-, -, h5⟩ := (nk_foc_at_iff c hc 𝔼 y hmφ s ω).mp (H s (Nat.zero_le s) ω)
    simp only [nkPhi1] at h5
    simp [hM, Mpart, nkSys, dotProduct, Fin.sum_univ_two]
    linarith
  have h120 : ∀ s, 1 ≤ s → ∀ ω, M s ω = nkΛ c *ᵥ M (s - 1) ω +
      nkQ c *ᵥ nkX c (piOf y) (xOf y) s ω := by
    intro s hs ω
    have := nk_eq120_of_foc c hc 𝔼 y hmφ H s ω
    simp only [hM]
    rw [show s - 1 + 1 = s by omega]
    exact this
  have hcrit := TargetCriterion.Crit.eq123_of_eq119_eq120 (D := 2) (eq122 (nkΛ c))
    (fun i j => (natDegree_Bpoly_le_card_sub_one (nkΛ c) i j).trans (by simp))
    ((natDegree_alpha_le_rank _).trans ((rank_le_card_width _).trans (by simp)))
    (nkSys c hc.2.2.1.ne').B2 h119 h120
  exact (nk_crit_iff_rule c hc xm1 im1 im2 (piOf y) (xOf y) (iOf y) (by omega)).mp
    fun ω => hcrit t (by omega) ω

/-! ### Proposition 8.3 for the basic model: Proposition 8.5's superinertia -/

/-- Woodford (2003), (1.15), p. 546, for the basic model:
`det(A − μÎ) = (1 − βμ)(1 − μ) − κσμ = β(μ − λ₁)(μ − λ₂)`, with `λ₁ < 1 < β⁻¹ < λ₂` the roots of
Chapter 3's `βμ² − (1 + β + κσ)μ + 1` (`QuadraticRoots.lam1`, `lam2`). -/
theorem nk_pencilPoly (hc : c.Adm) :
    (nkSys c hc.2.2.1.ne').pencilPoly =
      C (c.β : ℂ) * (X - C (QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℂ)) *
        (X - C (QuadraticRoots.lam2 c.β (c.κ * c.σ) : ℂ)) := by
  have hβ := hc.1
  have hκσ : 0 < c.κ * c.σ := mul_pos hc.2.2.2.1 hc.2.2.1
  have hs : (c.β : ℂ) * ((QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℂ) +
      QuadraticRoots.lam2 c.β (c.κ * c.σ)) = 1 + c.β + c.κ * c.σ := by
    exact_mod_cast QuadraticRoots.beta_mul_sum hβ
  have hp : (c.β : ℂ) * ((QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℂ) *
      QuadraticRoots.lam2 c.β (c.κ * c.σ)) = 1 := by
    exact_mod_cast QuadraticRoots.beta_mul_prod hβ hκσ
  refine Polynomial.funext fun z => ?_
  rw [PencilSplit.pencilPoly_eval, Prop83.det_empty_sum, det_fin_two]
  simp [toBlocks₂₂, LinearRESystem.Ahat, LinearRESystem.Ihat, nkSys]
  linear_combination z * hs - hp

/-- Woodford (2003), App. G.1, p. 716 (Assumption 8.3) for the basic model: (1.15) is a nonzero
polynomial with the two distinct nonzero roots `λ₁, λ₂`, and
`2 = rank Ẽ + rank A − n_z`. -/
theorem nk_assumption83 (hc : c.Adm) : PencilEigen.Assumption83 (nkSys c hc.2.2.1.ne') := by
  have hβ := hc.1
  have hκσ : 0 < c.κ * c.σ := mul_pos hc.2.2.2.1 hc.2.2.1
  have h1 := QuadraticRoots.lam1_pos hβ hκσ
  have h12 := QuadraticRoots.lam1_lt_lam2 hβ hκσ
  have hroots : (nkSys c hc.2.2.1.ne').pencilPoly.roots =
      {(QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℂ), (QuadraticRoots.lam2 c.β (c.κ * c.σ) : ℂ)} := by
    rw [nk_pencilPoly c hc, mul_assoc, roots_C_mul _ (by exact_mod_cast hβ.ne'),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
      roots_X_sub_C]
    rfl
  have hnz : PencilEigen.nonzeroRoots (nkSys c hc.2.2.1.ne') =
      {(QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℂ), (QuadraticRoots.lam2 c.β (c.κ * c.σ) : ℂ)} := by
    rw [PencilEigen.nonzeroRoots, hroots]
    simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
    simp [h1.ne', (h1.trans h12).ne']
  refine (PencilEigen.Assumption83.ofRoots _ ?_ ?_ ?_).elim id
  · rw [nk_pencilPoly c hc]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast hβ.ne'))
      (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  · rw [hnz]
    simpa using h12.ne
  · rw [hnz]
    have hE : (nkSys c hc.2.2.1.ne').Et.rank = 2 := by
      rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
      · simp
      · simp [nkSys, det_fin_two, hβ.ne']
    have hA : (nkSys c hc.2.2.1.ne').Ahat.rank = 2 := by
      rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
      · simp
      · rw [Prop83.det_empty_sum]
        exact (nkSys c hc.2.2.1.ne').A22_isUnit
    rw [hE, hA]
    simp

/-- Woodford (2003), Assumption 8.7, p. 556, for the basic model: exactly `n_Z + 1 = 1` root of
(1.15) has `|μ| < β⁻¹` (the zero root does not occur, `A` is invertible): `m = 1`. -/
theorem nk_stableCount (hc : c.Adm) :
    (nkSys c hc.2.2.1.ne').stableCount c.β⁻¹ = Fintype.card Empty + 1 := by
  have hβ := hc.1
  have hκσ : 0 < c.κ * c.σ := mul_pos hc.2.2.2.1 hc.2.2.1
  have h1 := QuadraticRoots.lam1_pos hβ hκσ
  have hl1 := QuadraticRoots.lam1_lt_one hβ hκσ
  have hb1 : 1 < c.β⁻¹ := one_lt_inv₀ hβ |>.mpr hc.2.1
  have hl2 : c.β⁻¹ < QuadraticRoots.lam2 c.β (c.κ * c.σ) := by
    refine (QuadraticRoots.between_roots_of_neg hβ hκσ ?_).2
    unfold QuadraticRoots.charPoly
    field_simp
    nlinarith
  have hA : (nkSys c hc.2.2.1.ne').Ahat.rank = 2 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
    · simp
    · rw [Prop83.det_empty_sum]
      exact (nkSys c hc.2.2.1.ne').A22_isUnit
  unfold LinearRESystem.stableCount
  rw [nk_pencilPoly c hc, mul_assoc, roots_C_mul _ (by exact_mod_cast hβ.ne'),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C, hA]
  have n1 : ‖((QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℝ) : ℂ)‖ < c.β⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg h1.le]
    linarith
  have n2 : ¬ ‖((QuadraticRoots.lam2 c.β (c.κ * c.σ) : ℝ) : ℂ)‖ < c.β⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have hne1 : ((QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have c1 : ¬ ((QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℝ) : ℂ) = 0 ∧
      ‖((QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℝ) : ℂ)‖ < c.β⁻¹ := ⟨hne1, n1⟩
  have c2 : ¬ (¬ ((QuadraticRoots.lam2 c.β (c.κ * c.σ) : ℝ) : ℂ) = 0 ∧
      ‖((QuadraticRoots.lam2 c.β (c.κ * c.σ) : ℝ) : ℂ)‖ < c.β⁻¹) := fun h => n2 h.2
  rw [Multiset.filter_add]
  simp only [Multiset.filter_singleton, c1, c2, ↓reduceIte]
  simp [hne1]

/-- Woodford (2003), pp. 556–558, for the basic model: no root of (1.15) lies on
`|μ| = β⁻¹`. -/
theorem nk_no_circle (hc : c.Adm) :
    ∀ l ∈ (nkSys c hc.2.2.1.ne').pencilPoly.roots, ‖l‖ ≠ c.β⁻¹ := by
  have hβ := hc.1
  have hκσ : 0 < c.κ * c.σ := mul_pos hc.2.2.2.1 hc.2.2.1
  have h1 := QuadraticRoots.lam1_pos hβ hκσ
  have hl1 := QuadraticRoots.lam1_lt_one hβ hκσ
  have hb1 : 1 < c.β⁻¹ := one_lt_inv₀ hβ |>.mpr hc.2.1
  have hl2 : c.β⁻¹ < QuadraticRoots.lam2 c.β (c.κ * c.σ) := by
    refine (QuadraticRoots.between_roots_of_neg hβ hκσ ?_).2
    unfold QuadraticRoots.charPoly
    field_simp
    nlinarith
  intro l hl
  rw [nk_pencilPoly c hc, mul_assoc, roots_C_mul _ (by exact_mod_cast hβ.ne'),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C] at hl
  rcases Multiset.mem_add.mp hl with h | h <;> rw [Multiset.mem_singleton] at h <;> subst h <;>
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] <;> intro h <;> linarith

/-- Woodford (2003), fn 35, p. 586: the characteristic polynomial of `Λ` is
`z² − (ρ₁ + ρ₂)z + ρ₂`, the polynomial of footnote 35. -/
theorem nk_charpoly (hβ : c.β ≠ 0) :
    (nkΛ c).charpoly = X ^ 2 - C (rho1 c.β c.σ c.κ + rho2 c.β) * X + C (rho2 c.β) := by
  rw [charpoly_fin_two]
  congr 3
  · simp only [trace, Fin.sum_univ_two, diag, nkΛ, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    unfold rho1 rho2
    field_simp
    ring_nf
  · rw [det_fin_two]
    simp only [nkΛ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    unfold rho2
    field_simp
    ring

/-- **Woodford (2003), Proposition 8.3 specialised: Proposition 8.5's superinertia.** For the
basic model the general Proposition 8.3 (with `Λ = nkΛ`, the representation of Proposition 8.1,
`m = 1`) gives exactly one zero of the lag polynomial `α(L) = 1 − (ρ₁+ρ₂)L + ρ₂L²` of the rule
(3.7) inside the unit circle: the reciprocal of the root `λ₂ > 1` of footnote 35's
`z² − (ρ₁+ρ₂)z + ρ₂` (`IRuleBasic.fn35_one_root_gt_one`), which is `(nkΛ c).charpoly`. -/
theorem nk_zerosInside (hc : c.Adm) :
    zerosInside (alpha (nkΛ c)) = 1 ∧
      (nkΛ c).charpoly = X ^ 2 - C (rho1 c.β c.σ c.κ + rho2 c.β) * X + C (rho2 c.β) :=
  ⟨Prop83.eq_of_homEquiv (nk_homEquiv c hc.2.2.1.ne' hc.1.ne') hc.1 (nk_assumption83 c hc)
    (nk_stableCount c hc) (nk_no_circle c hc), nk_charpoly c hc.1.ne'⟩

/-! ### Proposition 8.4 for the basic model: Proposition 8.6 -/

omit c in
/-- **Woodford (2003), Proposition 8.6, p. 588, from the general Proposition 8.4.** With
`α(L) = (1 − λ₁L)(1 − λ₂L) = α₁(L)α₂(L)`, `α₁ = L − λ₂⁻¹` (its zero `λ₂⁻¹` inside the unit
circle), `α₂ = −λ₂(1 − λ₁L)`, `w = −q̂` and `g = α̃₁(L⁻¹)⁻¹ w = −∑ λ₂^{−j}E_t q̂_{t+j}`, the general
`Prop84General.prop84_from` says that (3.10) holds at all dates `t ≥ T` iff the forward-integrated
rule (3.12) does, for every `T ≥ 2` and all bounded adapted `î, q̂` (`λ₂ > 1`). -/
theorem prop_8_6_from_general (𝔼 : ExpectationSystem Ω) {l1 l2 : ℝ} (hl2 : 1 < l2)
    {ih q : ℕ → Ω → ℝ} {h1 h2 : ℝ} (hib : BoundedProc ih) (hia : 𝔼.Adapted ih)
    (hqb : BoundedProc q) (hqa : 𝔼.Adapted q) {T : ℕ} (hT : 2 ≤ T) :
    (∀ t, T ≤ t → IRuleForwardIntegrated.G14 l1 l2 ih q h1 h2 t) ↔
      (∀ t, T ≤ t → IRuleForwardIntegrated.G15 𝔼 l1 l2 ih q h1 h2 t) := by
  have hl0 : l2 ≠ 0 := by linarith
  have ha0 : 0 ≤ l2⁻¹ := inv_nonneg.mpr (by linarith)
  have ha1 : l2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl2
  obtain ⟨Mq, hMq⟩ := hqb
  set α1 : ℝ[X] := X - C l2⁻¹ with hα1
  set α2 : ℝ[X] := C (-l2) * (1 - C l1 * X) with hα2
  have hm : α1.natDegree = 1 := natDegree_X_sub_C _
  have hα10 : α1 ≠ 0 := X_sub_C_ne_zero _
  have hroots : ∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖ := by
    intro z hz
    rw [hα1, Prop83.reverse_X_sub_C, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
      map_C, map_X, Complex.ofRealHom_eq_coe, Prop83.roots_one_sub_C_mul_X] at hz
    have hne : ((l2⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero hl0
    simp only [hne, ↓reduceIte, Multiset.mem_singleton] at hz
    rw [hz, ← Complex.ofReal_inv, inv_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact hl2
  set g : ℕ → Ω → ℝ := -(𝔼.forwardSeries l2⁻¹ q) with hg
  have hgb : BoundedProc g := by
    obtain ⟨K, hK⟩ := 𝔼.forwardSeries_bounded ha0 ha1 hMq
    exact ⟨K, fun t ω => by simp only [hg, Pi.neg_apply, abs_neg]; exact hK t ω⟩
  have hga : 𝔼.Adapted g := fun t => by
    simp only [hg, Pi.neg_apply]
    rw [map_neg, 𝔼.forwardSeries_adapted ha0 ha1 hMq t]
  have hgsol : (aeval (fwdOp 𝔼) α1.reverse) g = -q := by
    rw [hα1, Prop83.reverse_X_sub_C]
    funext t
    have hs := 𝔼.forwardSeries_solves ha0 ha1 hMq hqa t
    simp only [map_sub, map_one, map_mul, aeval_C, aeval_X, LinearMap.sub_apply,
      Module.End.one_apply, Module.End.mul_apply, Module.algebraMap_end_apply]
    change g t - l2⁻¹ • 𝔼.E t (g (t + 1)) = -q t
    simp only [hg, Pi.neg_apply, map_neg]
    rw [hs]
    module
  have key := Prop84General.prop84_from (α2 := α2) (lam := 1) (istar := 0) hm hα10 hroots hib
    hia hgb hga hgsol T
  have hprod : α1 * α2 = C 1 - C (l1 + l2) * X + C (l1 * l2) * X ^ 2 := by
    refine Polynomial.funext fun x => ?_
    simp only [hα1, hα2, eval_mul, eval_sub, eval_X, eval_C, eval_one, eval_add, eval_pow]
    field_simp
    ring
  rw [hprod] at key
  have hα2deg : α2.natDegree ≤ 1 := by
    rw [hα2]
    compute_degree!
  have hpdeg : (C 1 - C (l1 + l2) * X + C (l1 * l2) * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
    compute_degree!
  refine (forall_congr' fun t => imp_congr_right fun ht => ?_).trans
    (key.trans (forall_congr' fun t => imp_congr_right fun ht => ?_))
  · have hlag1 : IRuleBasic.lag h1 ih t = ih (t - 1) := lag_of_pos (by omega)
    have hlag2 : IRuleBasic.lag h2 (IRuleBasic.lag h1 ih) t = ih (t - 2) := by
      rw [lag_of_pos (by omega), lag_of_pos (by omega), show t - 1 - 1 = t - 2 by omega]
    unfold IRuleForwardIntegrated.G14
    rw [hlag1, hlag2, funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply,
      one_smul, smul_eq_mul, sub_zero]
    rw [Prop84General.aeval_lagOp_apply_of_le _ hpdeg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_add, coeff_sub,
      coeff_C, coeff_C_mul, coeff_X, coeff_X_pow, Nat.sub_zero]
    norm_num
    constructor <;> intro h <;> linarith
  · have hlag1 : IRuleBasic.lag h1 ih t = ih (t - 1) := lag_of_pos (by omega)
    have hlag2 : IRuleBasic.lag h2 (IRuleBasic.lag h1 ih) t = ih (t - 2) := by
      rw [lag_of_pos (by omega), lag_of_pos (by omega), show t - 1 - 1 = t - 2 by omega]
    unfold IRuleForwardIntegrated.G15 IRuleForwardIntegrated.wLag
    rw [hlag1, hlag2, funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply,
      one_smul, smul_eq_mul, sub_zero, hg]
    rw [Prop84General.lagOp_pow_apply (by omega),
      Prop84General.aeval_lagOp_apply_of_le _ hα2deg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hα2, coeff_C_mul,
      coeff_sub, coeff_one, Nat.sub_zero, show t - 1 - 1 = t - 2 by omega]
    norm_num
    have hinv : l2 * l2⁻¹ = 1 := mul_inv_cancel₀ hl0
    constructor
    · intro h
      linear_combination (-l2⁻¹) * h - (ih (t - 1) ω - l1 * ih (t - 2) ω) * hinv
    · intro h
      linear_combination (-l2) * h + 𝔼.forwardSeries l2⁻¹ q t ω * hinv

/-! ### `Prop83Claim` needs a nonempty sample space -/

/-- Woodford (2003), p. 540 (tool): the (trivial) expectation system on the empty sample
space. -/
def emptyES : ExpectationSystem Empty where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- **Woodford (2003), Proposition 8.3 — the statement `TargetCriterion.Prop83Claim` is false in
general.** For the basic model (`m = 1`, `nk_stableCount`) on the empty sample space, Assumption
8.1 holds and Proposition 8.1 is satisfied by `Λ = 0`, whose `α(L) = 1` has no zero inside the
unit circle; so the claim needs `Nonempty Ω` (as in `Prop83.prop83`). -/
theorem prop83Claim_false_empty (hc : c.Adm) (t0 : ℕ) :
    Assumption81 (nkProblem c hc) emptyES t0 ∧
      ∃ H : Prop81Conclusion (nkProblem c hc) emptyES t0,
        ¬ TargetCriterion.Prop83Claim (nkProblem c hc) emptyES t0 H := by
  obtain ⟨hA, H, hH⟩ := Prop83.prop83_needs_nonempty (nkProblem c hc) emptyES t0
  refine ⟨hA, H, fun hcl => ?_⟩
  have := hcl 1 (nk_stableCount c hc) le_rfl
  omega

end Woodford.OptimalPolicyRules.GeneralLinks
