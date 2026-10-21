/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralBKCopy
import OptimalPolicyRules.InertiaFOCRoots
import OptimalPolicyRules.GeneralLinksInertia
import OptimalPolicyRules.Prop84General

/-!
# The first-order system of the inflation-inertia model as a Blanchard–Kahn system

Woodford (2003), *Interest and Prices*, Chapter 8, §1.3 (the system (1.1) + (1.9), pp. 540–541)
for the inflation-inertia model of §3.2 (pp. 592–604, `GeneralLinksInertia.inProblem`), with
the general Blanchard–Kahn theorem of Appendix C.1 (`GeneralBKCopy`).

## The system

With the multipliers `M_t = (Ξ₂ₜ, Ξ₁ₜ)` on (2.6) and (3.1) and the multiplier `ξ_t` on the
predetermined block `Z_{t+1} = π_t`, the first-order conditions give `ξ_t`, `x_t` and `i_t` in
terms of `w_t = (π_t, Ξ₂ₜ, Ξ₁ₜ)` and `w_{t−1}` (with `w_{t₀−1} = (Z_{t₀}, M_{t₀−1})`), and the
remaining equations — (2.6), (3.1) and the `π`-row of (1.9) — are the second-order system
`P E_t w_{t+1} = A₁ w_t + A₂ w_{t−1} + F_t` (`row_iff`), with `P` invertible (`det P = −β²γ/λₓ`).
In the state `(w_t, w_{t−1})` (`w_{t−1}` predetermined) it is the Blanchard–Kahn system
`E_t y_{t+1} = A y_t + f_t` with `A = [P⁻¹A₁ P⁻¹A₂; I 0]` (`Abk`).

## Main results

* `det_pencil`: `det(z²P − zA₁ − A₂) = D(z)/λₓ`, the polynomial `D` of p. 593
  (`InflationInertiaRules.charD`); `charpoly_Abk`: the characteristic polynomial of `A` is
  `∏ (X − m)` over the six roots of `D`.
* `noUnit_Abk`, `stableCount_Abk`, `finrank_Abk`: no eigenvalue on the unit circle and exactly
  three (= the number of predetermined variables) in the open disc (`InertiaFOCRoots`).
* `row_iff`: (2.6), (3.1) and the `π`-row of (1.9) at one date are the three rows of the
  second-order system.
-/

namespace Woodford.OptimalPolicyRules.InertiaFOCSystem

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ
open IRuleBasic (Calib)
open CubicRoots CubicRoots.Assumptions
open InflationInertiaRules (charD recipC)
open BKInvariantSplit (eigs stableCount NoUnit boundedOrbits GenericX)
open BKForward (mv mv_apply)
open GeneralLinks (piOf xOf iOf piOf_eq xOf_eq)
open GeneralLinksInertia (inSys inProblem in_det_ne Zof Xi1 Xi2 in_foc_at_iff)

variable (c : Calib) (γ : ℝ)

/-! ### The matrices -/

/-- Woodford (2003), (2.6), (3.1) and (1.9), §3.2: the lead matrix `P` of the second-order
system in `w = (π, Ξ₂, Ξ₁)` (rows: (2.6), (3.1), the `π`-row of (1.9)). -/
noncomputable def Pm : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c.β, 0, 0; c.σ, c.κ / c.lx, -(1 / c.lx); -(c.β * γ), -(c.β * γ), 0]

/-- Woodford (2003), (2.6), (3.1) and (1.9), §3.2: the matrix `A₁` multiplying `w_t`. -/
noncomputable def A1m : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + c.β * γ, -(c.κ ^ 2 / c.lx), c.κ / c.lx;
    0, c.κ / c.lx, -((1 + c.β⁻¹) / c.lx) - c.σ ^ 2 / c.li;
    -(1 + c.β * γ ^ 2), -(1 + c.β * γ), 0]

/-- Woodford (2003), (2.6), (3.1) and (1.9), §3.2: the matrix `A₂` multiplying `w_{t−1}`. -/
noncomputable def A2m : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-γ, 0, -(c.κ / (c.β * c.lx)); 0, 0, 1 / (c.β * c.lx); γ, 1, c.σ / c.β]

/-- Woodford (2003), App. C.1 with §3.2: the Blanchard–Kahn matrix `A = [P⁻¹A₁ P⁻¹A₂; I 0]` of
the state `(w_t, w_{t−1})`. -/
noncomputable def Abk : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks ((Pm c γ)⁻¹ * A1m c γ) ((Pm c γ)⁻¹ * A2m c γ) 1 0

/-- Woodford (2003), §3.2: `det P = −β²γ/λₓ`. -/
theorem det_Pm (hlx : c.lx ≠ 0) : (Pm c γ).det = -(c.β ^ 2 * γ) / c.lx := by
  rw [det_fin_three]
  simp only [Pm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  field_simp
  ring

/-- Woodford (2003), p. 593: `det(z²P − zA₁ − A₂) = D(z)/λₓ` (complexified), the characteristic
polynomial `D` of the optimal-plan system. -/
theorem det_pencil (hβ : c.β ≠ 0) (hlx : c.lx ≠ 0) (hli : c.li ≠ 0) (z : ℂ) :
    (z ^ 2 • (Pm c γ).map Complex.ofReal - z • (A1m c γ).map Complex.ofReal -
      (A2m c γ).map Complex.ofReal).det = charD c.β γ c.κ c.σ c.lx c.li z / c.lx := by
  have hβc : (c.β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hlxc : (c.lx : ℂ) ≠ 0 := by exact_mod_cast hlx
  have hlic : (c.li : ℂ) ≠ 0 := by exact_mod_cast hli
  rw [det_fin_three]
  simp only [Pm, A1m, A2m, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  unfold charD recipC coefA0 coefA1 coefA2 coefA3
  push_cast
  field_simp
  ring

/-- Woodford (2003), App. C.1 (tool): `det(zI − [M₁ M₂; I 0]) = det(z²I − zM₁ − M₂)` for `z ≠ 0`
(multiply on the right by `[zI 0; I I]`). -/
theorem det_companion {n : Type*} [Fintype n] [DecidableEq n] (M1 M2 : Matrix n n ℂ) {z : ℂ}
    (hz : z ≠ 0) :
    (Matrix.scalar (n ⊕ n) z - fromBlocks M1 M2 1 0).det = (z ^ 2 • 1 - z • M1 - M2).det := by
  set S : Matrix n n ℂ := z • 1 with hS
  have hN : Matrix.scalar (n ⊕ n) z - fromBlocks M1 M2 1 0 = fromBlocks (S - M1) (-M2) (-1) S := by
    ext (i | i) (j | j) <;>
      simp [hS, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, fromBlocks]
  have hE : (fromBlocks S 0 1 1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).det = z ^ Fintype.card n := by
    rw [det_fromBlocks_zero₁₂, det_one, mul_one, hS, det_smul, det_one, mul_one]
  have hNE : fromBlocks (S - M1) (-M2) (-1) S * fromBlocks S 0 1 1 =
      fromBlocks (z ^ 2 • 1 - z • M1 - M2) (-M2) 0 S := by
    rw [fromBlocks_multiply]
    congr 1
    · rw [hS, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_one]
      module
    · simp
    · simp
    · simp
  have hdet := congrArg Matrix.det hNE
  rw [det_mul, hE, det_fromBlocks_zero₂₁, hS, det_smul, det_one, mul_one] at hdet
  rw [hN]
  exact mul_right_cancel₀ (pow_ne_zero _ hz) hdet

/-- Woodford (2003), App. C.1 with p. 593: for `z ≠ 0`, the characteristic polynomial of the
Blanchard–Kahn matrix is `D(z)/(λₓ det P)`. -/
theorem eval_charpoly_Abk (hβ : c.β ≠ 0) (hγ : γ ≠ 0) (hlx : c.lx ≠ 0) (hli : c.li ≠ 0) {z : ℂ}
    (hz : z ≠ 0) :
    ((Abk c γ).map Complex.ofReal).charpoly.eval z =
      charD c.β γ c.κ c.σ c.lx c.li z / (c.lx * (Pm c γ).det) := by
  have hPd : (Pm c γ).det ≠ 0 := by
    rw [det_Pm c γ hlx]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hβ) hγ)) hlx
  have hPu : IsUnit (Pm c γ).det := isUnit_iff_ne_zero.mpr hPd
  set Pc : Matrix (Fin 3) (Fin 3) ℂ := (Pm c γ).map Complex.ofReal with hPc
  set M1 : Matrix (Fin 3) (Fin 3) ℂ := ((Pm c γ)⁻¹ * A1m c γ).map Complex.ofReal with hM1
  set M2 : Matrix (Fin 3) (Fin 3) ℂ := ((Pm c γ)⁻¹ * A2m c γ).map Complex.ofReal with hM2
  have hmap : (Abk c γ).map Complex.ofReal = fromBlocks M1 M2 1 0 := by
    rw [Abk, fromBlocks_map, Matrix.map_one _ (by simp) (by simp), Matrix.map_zero _ (by simp)]
  have hPM1 : Pc * M1 = (A1m c γ).map Complex.ofReal := by
    have e : (Pm c γ * ((Pm c γ)⁻¹ * A1m c γ)).map Complex.ofReal = Pc * M1 :=
      Matrix.map_mul (f := Complex.ofRealHom)
    rw [← e, Matrix.mul_nonsing_inv_cancel_left _ _ hPu]
  have hPM2 : Pc * M2 = (A2m c γ).map Complex.ofReal := by
    have e : (Pm c γ * ((Pm c γ)⁻¹ * A2m c γ)).map Complex.ofReal = Pc * M2 :=
      Matrix.map_mul (f := Complex.ofRealHom)
    rw [← e, Matrix.mul_nonsing_inv_cancel_left _ _ hPu]
  have hdetPc : Pc.det = ((Pm c γ).det : ℂ) := by
    rw [hPc]
    exact (RingHom.map_det Complex.ofRealHom (Pm c γ)).symm
  have hkey : Pc * (z ^ 2 • 1 - z • M1 - M2) =
      z ^ 2 • Pc - z • (A1m c γ).map Complex.ofReal - (A2m c γ).map Complex.ofReal := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, hPM1,
      hPM2]
  have hd := congrArg Matrix.det hkey
  rw [det_mul, det_pencil c γ hβ hlx hli, hdetPc] at hd
  have hPdc : ((Pm c γ).det : ℂ) ≠ 0 := by exact_mod_cast hPd
  have hlxc : (c.lx : ℂ) ≠ 0 := by exact_mod_cast hlx
  rw [Matrix.eval_charpoly, hmap, det_companion M1 M2 hz, eq_div_iff (mul_ne_zero hlxc hPdc)]
  rw [eq_div_iff hlxc] at hd
  linear_combination hd

/-- Woodford (2003), §3.2 (tool): the calibration and `0 < γ ≤ 1` give the standing assumptions of
Proposition 8.7. -/
theorem standing_of (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) : Standing c.β γ c.κ c.σ :=
  ⟨hc.2.2.1, hc.2.2.2.1, hc.1, hc.2.1, hγ0, hγ1⟩

/-- **Woodford (2003), App. C.1 with p. 593: the eigenvalues of the Blanchard–Kahn matrix of the
inflation-inertia first-order system** are the six roots of `D`: the characteristic polynomial
of `A` is `∏ (X − m)` over them; none lies on the unit circle and exactly three lie in the open
unit disc. -/
theorem bk_roots (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    NoUnit (Abk c γ) ∧ stableCount (Abk c γ) = 3 := by
  have h := standing_of c γ hc hγ0 hγ1
  have hβ := hc.1.ne'
  have hlx := hc.2.2.2.2.1.ne'
  have hli := hc.2.2.2.2.2.ne'
  obtain ⟨s, -, hD, hin, hnu⟩ := InertiaFOCRoots.charD_inside_three h hc.2.2.2.2.1.le hc.2.2.2.2.2
  have hcp : ((Abk c γ).map Complex.ofReal).charpoly = (s.map (fun m => X - C m)).prod := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (fun z (hz : z ∈ ({0}ᶜ : Set ℂ)) => ?_)
      (Set.finite_singleton (0 : ℂ)).infinite_compl
    have hz0 : z ≠ 0 := hz
    change Polynomial.eval z _ = Polynomial.eval z _
    rw [eval_charpoly_Abk c γ hβ hγ0.ne' hlx hli hz0, hD z, det_Pm c γ hlx,
      Polynomial.eval_multiset_prod, Multiset.map_map]
    have he : ((fun p => Polynomial.eval z p) ∘ fun m => X - C m) = fun m => z - m := by
      funext m
      simp
    rw [he]
    have hβc : (c.β : ℂ) ≠ 0 := by exact_mod_cast hβ
    have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ0.ne'
    have hlxc : (c.lx : ℂ) ≠ 0 := by exact_mod_cast hlx
    push_cast
    field_simp
  have heigs : eigs (Abk c γ) = s := by
    rw [BKInvariantSplit.eigs, hcp, Polynomial.roots_multiset_prod_X_sub_C]
  refine ⟨fun μ hμ => hnu μ (heigs ▸ hμ), ?_⟩
  rw [stableCount, heigs, hin]

/-- **Woodford (2003), App. C.1 (Blanchard–Kahn condition (ii)) for the inflation-inertia
first-order system**: the bounded-orbit (stable) subspace of `A` has dimension `3`, the number
of predetermined variables `(π_{t−1}, Ξ₂,ₜ₋₁, Ξ₁,ₜ₋₁)`. -/
theorem finrank_Abk (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    Module.finrank ℝ (boundedOrbits (Abk c γ)) = Fintype.card (Fin 3) := by
  obtain ⟨hnu, hcount⟩ := bk_roots c γ hc hγ0 hγ1
  rw [BKInvariantSplit.finrank_eq_stableCount hnu, hcount, Fintype.card_fin]

/-! ### The rows of the second-order system -/

/-- **Woodford (2003), (2.6), (3.1) and the `π`-row of (1.9), §3.2, at one date: they are the
three rows of `P E_t w_{t+1} = A₁ w_t + A₂ w_{t−1} + F_t`.** Here `w_t = (π_t, Ξ₂ₜ, Ξ₁ₜ)`, the
lagged `w_{t−1} = (Z_t, Ξ₂,ₜ₋₁, Ξ₁,ₜ₋₁)`, the leads are expectations, `x_t, i_t` come from (3.4),
(3.5) and `E_tξ_{t+1}` from the `Z`-row of (1.9) at `t + 1`; `F_t = (c₀ − κx*, σi* + c₁, 0)`. -/
theorem rows_iff (hβ : c.β ≠ 0) (hlx : c.lx ≠ 0) (hli : c.li ≠ 0)
    {p pE Zt a aE b bE am bm x xE i ξE c0 c1 : ℝ}
    (hx : x = c.xstar + c.lx⁻¹ * (c.κ * a - b + c.β⁻¹ * bm))
    (hxE : xE = c.xstar + c.lx⁻¹ * (c.κ * aE - bE + c.β⁻¹ * b))
    (hi : i = c.istar - c.σ / c.li * b) (hξ : ξE = -(c.β * γ) * (aE + (pE - γ * p))) :
    ((c.β * pE = -γ * Zt + (1 + c.β * γ) * p - c.κ * x + c0) ∧
        (c.σ * pE + xE = x + c.σ * i + c1) ∧
        (ξE + (1 + c.β * γ) * a + (p - γ * Zt) - c.β⁻¹ * (c.β * am + c.σ * bm) = 0)) ↔
      ∀ j, (Pm c γ *ᵥ ![pE, aE, bE]) j =
        (A1m c γ *ᵥ ![p, a, b]) j + (A2m c γ *ᵥ ![Zt, am, bm]) j +
          ![c0 - c.κ * c.xstar, c.σ * c.istar + c1, 0] j := by
  subst hx hxE hi hξ
  have e : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  constructor
  · rintro ⟨h0, h1, h2⟩ j
    rcases e j with rfl | rfl | rfl <;>
      simp only [Pm, A1m, A2m, mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
        Matrix.head_fin_const]
    · field_simp
      field_simp at h0
      linear_combination h0
    · field_simp
      field_simp at h1
      linear_combination h1
    · field_simp
      field_simp at h2
      linear_combination h2
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Pm, A1m, A2m, mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩
    · field_simp
      field_simp at h0
      linear_combination h0
    · field_simp
      field_simp at h1
      linear_combination h1
    · field_simp
      field_simp at h2
      linear_combination h2

/-! ### The structural equations at one date -/

variable {Ω : Type*}

/-- Woodford (2003), (1.1) for the inflation-inertia model at one date, with any disturbance
`c_t`: `Z_{t+1} = π_t`, `βE_tπ_{t+1} = −γZ_t + (1 + βγ)π_t − κx_t + c₀` ((2.6) corrected) and
`σE_tπ_{t+1} + E_tx_{t+1} = x_t + σi_t + c₁` ((3.1)). -/
theorem in_struct_at (hc : c.Adm) (hγ : 0 ≤ γ) (𝔼 : ExpectationSystem Ω)
    (cc : ℕ → Ω → Fin 2 → ℝ) (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) :
    (Zpart (y (t + 1) ω) = (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A11 *ᵥ Zpart (y t ω) +
        (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A12 *ᵥ zpart (y t ω) ∧
      (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).Et *ᵥ
          EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω =
        (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A21 *ᵥ Zpart (y t ω) +
          (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A22 *ᵥ zpart (y t ω) +
          ipart (y t ω) • (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).B2 + cc t ω) ↔
      (Zof y (t + 1) ω = piOf y t ω ∧
        c.β * 𝔼.E t (piOf y (t + 1)) ω =
          -γ * Zof y t ω + (1 + c.β * γ) * piOf y t ω - c.κ * xOf y t ω + cc t ω 0 ∧
        c.σ * 𝔼.E t (piOf y (t + 1)) ω + 𝔼.E t (xOf y (t + 1)) ω =
          xOf y t ω + c.σ * iOf y t ω + cc t ω 1) := by
  rw [funext_iff, funext_iff, Fin.forall_fin_two]
  simp only [inSys, mulVec, dotProduct, Fin.sum_univ_two, EV, zpart, Zpart, ipart,
    piOf_eq, xOf_eq, Zof, piOf, xOf, iOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply, Fintype.univ_punit,
    Finset.sum_singleton, Fin.isValue, ↓reduceIte, one_ne_zero]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h0' := h0 ()
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun _ => by linarith, by linarith, by linarith⟩

/-! ### The state `(w_t, w_{t−1})` -/

/-- Woodford (2003), §3.2: `w_s = (π_{t₀+s}, Ξ₂,t₀+s, Ξ₁,t₀+s)` of a plan and its multipliers
(`M_t` is the `inr` block of `φ_{t+1}`), dates counted from `t₀`. -/
def wOf (t0 : ℕ) (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) (φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ) :
    ℕ → Fin 3 → Ω → ℝ :=
  fun s => ![fun ω => y (s + t0) ω (Sum.inl (Sum.inr 0)), fun ω => φ (s + t0 + 1) ω (Sum.inr 0),
    fun ω => φ (s + t0 + 1) ω (Sum.inr 1)]

/-- Woodford (2003), §3.2: the initial predetermined vector `w_{t₀−1} = (Z_{t₀}, M_{t₀−1})`. -/
def x0Of (Z0 : Ω → Unit → ℝ) (M0 : Ω → Fin 2 → ℝ) : Fin 3 → Ω → ℝ :=
  ![fun ω => Z0 ω (), fun ω => M0 ω 0, fun ω => M0 ω 1]

/-- Woodford (2003), App. C.1: the lagged vector `w_{s−1}`, with `w_{−1} = x₀`. -/
def lagW (x0 : Fin 3 → Ω → ℝ) (w : ℕ → Fin 3 → Ω → ℝ) : ℕ → Fin 3 → Ω → ℝ
  | 0 => x0
  | s + 1 => w s

/-- Woodford (2003), App. C.1: the Blanchard–Kahn state `y_s = (w_s, w_{s−1})`. -/
def bkState (x0 : Fin 3 → Ω → ℝ) (w : ℕ → Fin 3 → Ω → ℝ) : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ :=
  fun s => Sum.elim (w s) (lagW x0 w s)

/-- Woodford (2003), (2.6), (3.1): the forcing `F_s = (c₀ − κx*, σi* + c₁, 0)` of the second-order
system at date `t₀ + s`. -/
def Fvec (cc : ℕ → Ω → Fin 2 → ℝ) (t0 : ℕ) : ℕ → Fin 3 → Ω → ℝ :=
  fun s => ![fun ω => cc (s + t0) ω 0 - c.κ * c.xstar,
    fun ω => c.σ * c.istar + cc (s + t0) ω 1, fun _ => 0]

/-- Woodford (2003), App. C.1: the forcing `(P⁻¹F_s, 0)` of the Blanchard–Kahn system. -/
noncomputable def forcing (cc : ℕ → Ω → Fin 2 → ℝ) (t0 : ℕ) : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ :=
  fun s => Sum.elim (mv (Pm c γ)⁻¹ (Fvec c cc t0 s)) 0

/-- Woodford (2003), App. C.1 (tool): a vector `![f₀, f₁, f₂]` of random variables at `ω`. -/
theorem vec3_eval (f0 f1 f2 : Ω → ℝ) (ω : Ω) :
    (fun k => (![f0, f1, f2] : Fin 3 → Ω → ℝ) k ω) = ![f0 ω, f1 ω, f2 ω] := by
  funext k
  fin_cases k <;> rfl

/-- Woodford (2003), (3.4)–(3.5) (tool): solving `ℓ(x − x*) = r` for `x`. -/
theorem lin_solve {l x xs r : ℝ} (hl : l ≠ 0) (h : l * (x - xs) = r) : x = xs + l⁻¹ * r := by
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hl, one_mul]
  ring

/-! ### From the first-order conditions to the second-order system -/

/-- **Woodford (2003), (1.1) + (1.9), §3.2: along a solution of the first-order system the
vector `w` solves the second-order system** `P E_s w_{s+1} = A₁ w_s + A₂ w_{s−1} + F_s` at every
date `s ≥ 0` (dates from `t₀`), with `w_{−1} = (Z_{t₀}, M_{t₀−1})`. -/
theorem rows_of_foc (hc : c.Adm) (hγ0 : 0 < γ) {𝔼 : ExpectationSystem Ω}
    {cc : ℕ → Ω → Fin 2 → ℝ} {t0 : ℕ} {Z0 : Ω → Unit → ℝ} {M0 : Ω → Fin 2 → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (hs : FOCSystem (inProblem c γ hc hγ0.le) 𝔼 cc t0 Z0 M0 y φ) (s : ℕ) (ω : Ω) :
    ∀ j, (Pm c γ *ᵥ ![𝔼.E (s + t0) (fun ω' => y (s + t0 + 1) ω' (Sum.inl (Sum.inr 0))) ω,
        𝔼.E (s + t0) (fun ω' => φ (s + t0 + 1 + 1) ω' (Sum.inr 0)) ω,
        𝔼.E (s + t0) (fun ω' => φ (s + t0 + 1 + 1) ω' (Sum.inr 1)) ω]) j =
      (A1m c γ *ᵥ fun k => wOf t0 y φ s k ω) j +
        (A2m c γ *ᵥ fun k => lagW (x0Of Z0 M0) (wOf t0 y φ) s k ω) j +
        ![cc (s + t0) ω 0 - c.κ * c.xstar, c.σ * c.istar + cc (s + t0) ω 1, 0] j := by
  obtain ⟨⟨hstr, hZ0, -, hya⟩, -, hmφ, hM, hfoc⟩ := hs
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hlx : c.lx ≠ 0 := hc.2.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  set t := s + t0 with ht
  have hF : ∀ u, t0 ≤ u → ∀ ω', _ := fun u hu ω' =>
    (in_foc_at_iff c γ hc hγ0.le 𝔼 y hmφ u ω').mp (hfoc u hu ω')
  have hS : ∀ u, t0 ≤ u → ∀ ω', _ := fun u hu ω' =>
    (in_struct_at c γ hc hγ0.le 𝔼 cc y u ω').mp (hstr u hu ω')
  -- the lagged vector
  have hlag : lagW (x0Of Z0 M0) (wOf t0 y φ) s =
      ![Zof y t, fun ω' => φ t ω' (Sum.inr 0), fun ω' => φ t ω' (Sum.inr 1)] := by
    cases s with
    | zero =>
      have e : t = t0 := by omega
      funext k ω'
      fin_cases k
      · change Z0 ω' () = y t ω' (Sum.inl (Sum.inl ()))
        rw [e]
        exact (congrFun (hZ0 ω') ()).symm
      · change M0 ω' 0 = φ t ω' (Sum.inr 0)
        rw [e]
        exact (congrFun (hM ω') 0).symm
      · change M0 ω' 1 = φ t ω' (Sum.inr 1)
        rw [e]
        exact (congrFun (hM ω') 1).symm
    | succ s' =>
      have e : s' + t0 + 1 = t := by omega
      funext k ω'
      fin_cases k
      · change y (s' + t0) ω' (Sum.inl (Sum.inr 0)) = Zof y t ω'
        rw [← e]
        exact ((hS (s' + t0) (by omega) ω').1).symm
      · change φ (s' + t0 + 1) ω' (Sum.inr 0) = φ t ω' (Sum.inr 0)
        rw [e]
      · change φ (s' + t0 + 1) ω' (Sum.inr 1) = φ t ω' (Sum.inr 1)
        rw [e]
  rw [hlag]
  -- the first-order conditions at `t` and `t + 1`
  obtain ⟨-, f1, f2, f3⟩ := hF t (by omega) ω
  obtain ⟨hZt1, s0, s1⟩ := hS t (by omega) ω
  -- `E_t x_{t+1}` and `E_t ξ_{t+1}`
  have hxf : xOf y (t + 1) = fun ω' => c.xstar + c.lx⁻¹ * (c.κ * φ (t + 1 + 1) ω' (Sum.inr 0) -
      φ (t + 1 + 1) ω' (Sum.inr 1) + c.β⁻¹ * φ (t + 1) ω' (Sum.inr 1)) := by
    funext ω'
    have h2 := (hF (t + 1) (by omega) ω').2.2.1
    simp only [Xi1, Xi2] at h2
    exact lin_solve hlx (by linarith)
  have hξf : (fun ω' => φ (t + 1) ω' (Sum.inl ())) = fun ω' => -(c.β * γ) *
      (φ (t + 1 + 1) ω' (Sum.inr 0) + (y (t + 1) ω' (Sum.inl (Sum.inr 0)) - γ * piOf y t ω')) := by
    funext ω'
    have h0 := (hF (t + 1) (by omega) ω').1
    have hz := (hS t (by omega) ω').1
    simp only [Xi2] at h0
    rw [hz] at h0
    simp only [piOf] at h0 ⊢
    field_simp at h0
    linear_combination -h0
  have hk1 := congrFun (hmφ t 1) ω
  have hπk : 𝔼.E t (piOf y t) = piOf y t := hya t (Sum.inl (Sum.inr 0))
  have hEx : 𝔼.E t (xOf y (t + 1)) ω = c.xstar + c.lx⁻¹ * (c.κ *
      𝔼.E t (fun ω' => φ (t + 1 + 1) ω' (Sum.inr 0)) ω -
      𝔼.E t (fun ω' => φ (t + 1 + 1) ω' (Sum.inr 1)) ω + c.β⁻¹ * φ (t + 1) ω (Sum.inr 1)) := by
    rw [hxf, ExpectationTools.E_fun_add, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add,
      ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_mul,
      𝔼.const]
    simp only
    rw [hk1]
  have hEξ : 𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω = -(c.β * γ) *
      (𝔼.E t (fun ω' => φ (t + 1 + 1) ω' (Sum.inr 0)) ω +
        (𝔼.E t (fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr 0))) ω - γ * piOf y t ω)) := by
    rw [hξf, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add, ExpectationTools.E_fun_sub,
      ExpectationTools.E_fun_mul]
    rw [hπk]
  have hrows := (rows_iff c γ hβ hlx hli (p := piOf y t ω) (Zt := Zof y t ω)
    (a := φ (t + 1) ω (Sum.inr 0)) (b := φ (t + 1) ω (Sum.inr 1))
    (am := φ t ω (Sum.inr 0)) (bm := φ t ω (Sum.inr 1)) (x := xOf y t ω)
    (xE := 𝔼.E t (xOf y (t + 1)) ω) (i := iOf y t ω)
    (c0 := cc t ω 0) (c1 := cc t ω 1)
    (by simp only [Xi1, Xi2] at f2; exact lin_solve hlx (by linarith)) hEx
    (by
      simp only [Xi1] at f3
      have := lin_solve hli (show c.li * (iOf y t ω - c.istar) = -(c.σ * φ (t + 1) ω (Sum.inr 1))
        by linarith)
      rw [this]
      ring) hEξ).mp
    ⟨s0, s1, by simpa [Xi2] using f1⟩
  intro j
  have hw : (fun k => wOf t0 y φ s k ω) =
      ![y t ω (Sum.inl (Sum.inr 0)), φ (t + 1) ω (Sum.inr 0), φ (t + 1) ω (Sum.inr 1)] :=
    vec3_eval _ _ _ ω
  rw [hw, vec3_eval]
  exact hrows j

/-! ### The second-order system as the Blanchard–Kahn system -/

/-- Woodford (2003), App. C.1 with §3.2: for `w` adapted, `y = (w_s, w_{s−1})` solves
`E_s y_{s+1} = A y_s + (P⁻¹F_s, 0)` iff `P E_s w_{s+1} = A₁ w_s + A₂ w_{s−1} + F_s` at every date
and outcome (`P` invertible). -/
theorem solves_bk_iff (hc : c.Adm) (hγ0 : 0 < γ) (𝔼' : ExpectationSystem Ω)
    (x0 : Fin 3 → Ω → ℝ) (w F : ℕ → Fin 3 → Ω → ℝ) (hwa : ∀ s k, 𝔼'.E s (w s k) = w s k) :
    GeneralBKCopy.Solves 𝔼' (Abk c γ) (fun s => Sum.elim (mv (Pm c γ)⁻¹ (F s)) 0)
        (bkState x0 w) ↔
      ∀ s ω, Pm c γ *ᵥ (fun k => 𝔼'.E s (w (s + 1) k) ω) =
        A1m c γ *ᵥ (fun k => w s k ω) + A2m c γ *ᵥ (fun k => lagW x0 w s k ω) +
          fun k => F s k ω := by
  have hPd : (Pm c γ).det ≠ 0 := by
    rw [det_Pm c γ hc.2.2.2.2.1.ne']
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hc.1.ne') hγ0.ne'))
      hc.2.2.2.2.1.ne'
  have hPu : IsUnit (Pm c γ).det := isUnit_iff_ne_zero.mpr hPd
  have hinl : ∀ s ω, (fun i => mv (Abk c γ) (bkState x0 w s) (Sum.inl i) ω) =
      ((Pm c γ)⁻¹ * A1m c γ) *ᵥ (fun k => w s k ω) +
        ((Pm c γ)⁻¹ * A2m c γ) *ᵥ (fun k => lagW x0 w s k ω) := by
    intro s ω
    funext i
    rw [mv_apply, Abk, fromBlocks_mulVec]
    rfl
  have hinr : ∀ s ω, (fun i => mv (Abk c γ) (bkState x0 w s) (Sum.inr i) ω) =
      fun k => w s k ω := by
    intro s ω
    funext i
    rw [mv_apply, Abk, fromBlocks_mulVec]
    simp [bkState]
  constructor
  · intro h s ω
    have hv : (fun k => 𝔼'.E s (w (s + 1) k) ω) =
        ((Pm c γ)⁻¹ * A1m c γ) *ᵥ (fun k => w s k ω) +
          ((Pm c γ)⁻¹ * A2m c γ) *ᵥ (fun k => lagW x0 w s k ω) +
            (Pm c γ)⁻¹ *ᵥ (fun k => F s k ω) := by
      funext k
      have := congrFun (h s (Sum.inl k)) ω
      rw [Pi.add_apply] at this
      have e2 := congrFun (hinl s ω) k
      rw [show bkState x0 w (s + 1) (Sum.inl k) = w (s + 1) k from rfl, e2] at this
      rw [this]
      simp only [Sum.elim_inl, Pi.add_apply, mv_apply]
    rw [hv, mulVec_add, mulVec_add, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
      mul_nonsing_inv_cancel_left _ _ hPu, mul_nonsing_inv_cancel_left _ _ hPu,
      mul_nonsing_inv _ hPu, one_mulVec]
  · intro h s k
    funext ω
    rcases k with k | k
    · have hv : (fun k => 𝔼'.E s (w (s + 1) k) ω) =
          (Pm c γ)⁻¹ *ᵥ (A1m c γ *ᵥ (fun k => w s k ω) + A2m c γ *ᵥ
            (fun k => lagW x0 w s k ω) + fun k => F s k ω) := by
        rw [← h s ω, mulVec_mulVec, nonsing_inv_mul _ hPu, one_mulVec]
      have e1 := congrFun hv k
      have e2 := congrFun (hinl s ω) k
      change 𝔼'.E s (w (s + 1) k) ω = mv (Abk c γ) (bkState x0 w s) (Sum.inl k) ω +
        mv (Pm c γ)⁻¹ (F s) k ω
      rw [e1, e2, mv_apply, mulVec_add, mulVec_add, mulVec_mulVec, mulVec_mulVec]
      simp only [Pi.add_apply]
    · have e2 := congrFun (hinr s ω) k
      change 𝔼'.E s (w s k) ω = mv (Abk c γ) (bkState x0 w s) (Sum.inr k) ω + 0
      rw [e2, hwa s k, add_zero]

/-! ### From the second-order system back to the first-order conditions -/

/-- Woodford (2003), (3.4)–(3.5) and §3.2: the plan determined by `w` and `w_{−1} = x₀` from `t₀`
on: `Z_t = π_{t−1}` (`Z_{t₀}` from `x₀`), `π_t`, `x_t = x* + λₓ⁻¹(κΞ₂ₜ − Ξ₁ₜ + β⁻¹Ξ₁,ₜ₋₁)`,
`i_t = i* − (σ/λᵢ)Ξ₁ₜ`; `0` before `t₀`. -/
noncomputable def yC (t0 : ℕ) (x0 : Fin 3 → Ω → ℝ) (w : ℕ → Fin 3 → Ω → ℝ) :
    ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ :=
  fun t ω => if t0 ≤ t then
    Sum.elim (Sum.elim (fun _ => lagW x0 w (t - t0) 0 ω)
      ![w (t - t0) 0 ω, c.xstar + c.lx⁻¹ * (c.κ * w (t - t0) 1 ω - w (t - t0) 2 ω +
        c.β⁻¹ * lagW x0 w (t - t0) 2 ω)])
      (fun _ => c.istar - c.σ / c.li * w (t - t0) 2 ω)
  else 0

/-- Woodford (2003), (1.9) and §3.2: the multipliers determined by `w` and `x₀`:
`φ_t = (ξ_t, M_{t−1})` with `ξ_t = −βγ(Ξ₂ₜ + π_t − γZ_t)` and `M_{t−1} = (Ξ₂,ₜ₋₁, Ξ₁,ₜ₋₁)`;
`0` before `t₀`. -/
noncomputable def φC (t0 : ℕ) (x0 : Fin 3 → Ω → ℝ) (w : ℕ → Fin 3 → Ω → ℝ) :
    ℕ → Ω → Unit ⊕ Fin 2 → ℝ :=
  fun t ω => if t0 ≤ t then
    Sum.elim (fun _ => -(c.β * γ) * (w (t - t0) 1 ω + (w (t - t0) 0 ω -
      γ * lagW x0 w (t - t0) 0 ω)))
      ![lagW x0 w (t - t0) 1 ω, lagW x0 w (t - t0) 2 ω]
  else 0


/-- Woodford (2003), §3.2 (tool): the constructed plan at date `t₀ + s`. -/
theorem yC_at (t0 : ℕ) (x0 : Fin 3 → Ω → ℝ) (w : ℕ → Fin 3 → Ω → ℝ) (s : ℕ) (ω : Ω) :
    piOf (yC c t0 x0 w) (s + t0) ω = w s 0 ω ∧ Zof (yC c t0 x0 w) (s + t0) ω = lagW x0 w s 0 ω ∧
      xOf (yC c t0 x0 w) (s + t0) ω = c.xstar + c.lx⁻¹ * (c.κ * w s 1 ω - w s 2 ω +
        c.β⁻¹ * lagW x0 w s 2 ω) ∧
      iOf (yC c t0 x0 w) (s + t0) ω = c.istar - c.σ / c.li * w s 2 ω := by
  have h1 : t0 ≤ s + t0 := by omega
  have h2 : s + t0 - t0 = s := by omega
  simp only [piOf, Zof, xOf, iOf, yC, h1, ↓reduceIte, h2, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, and_self]

/-- Woodford (2003), §3.2 (tool): the constructed multipliers at date `t₀ + s`. -/
theorem φC_at (t0 : ℕ) (x0 : Fin 3 → Ω → ℝ) (w : ℕ → Fin 3 → Ω → ℝ) (s : ℕ) (ω : Ω) :
    φC c γ t0 x0 w (s + t0) ω (Sum.inl ()) =
        -(c.β * γ) * (w s 1 ω + (w s 0 ω - γ * lagW x0 w s 0 ω)) ∧
      φC c γ t0 x0 w (s + t0) ω (Sum.inr 0) = lagW x0 w s 1 ω ∧
      φC c γ t0 x0 w (s + t0) ω (Sum.inr 1) = lagW x0 w s 2 ω := by
  have h1 : t0 ≤ s + t0 := by omega
  have h2 : s + t0 - t0 = s := by omega
  simp only [φC, h1, ↓reduceIte, h2, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, and_self]

/-- Woodford (2003), §3.2 (tool): `M_{t₀+s} = (Ξ₂, Ξ₁)` of the constructed multipliers is `w_s`. -/
theorem φC_succ (t0 : ℕ) (x0 : Fin 3 → Ω → ℝ) (w : ℕ → Fin 3 → Ω → ℝ) (s : ℕ) (ω : Ω) :
    φC c γ t0 x0 w (s + t0 + 1) ω (Sum.inr 0) = w s 1 ω ∧
      φC c γ t0 x0 w (s + t0 + 1) ω (Sum.inr 1) = w s 2 ω := by
  have h := φC_at c γ t0 x0 w (s + 1) ω
  rw [show s + 1 + t0 = s + t0 + 1 by omega] at h
  exact ⟨h.2.1, h.2.2⟩

/-- Woodford (2003), (3.4) (tool): `|x* + ℓ(κa − b + mz)| ≤ |x*| + |ℓ|((|κ| + 1 + |m|)K)` for
`|a|, |b|, |z| ≤ K`. -/
theorem abs_affine3 {a b z K : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K) (hz : |z| ≤ K) (x0 l k m : ℝ) :
    |x0 + l * (k * a - b + m * z)| ≤ |x0| + |l| * ((|k| + 1 + |m|) * K) := by
  have h1 : |k * a - b + m * z| ≤ (|k| + 1 + |m|) * K := by
    have e1 := abs_add_le (k * a - b) (m * z)
    have e2 := abs_sub (k * a) b
    have e3 : |k * a| ≤ |k| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ha (abs_nonneg k)
    have e4 : |m * z| ≤ |m| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hz (abs_nonneg m)
    nlinarith
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg l)

/-- Woodford (2003), App. C.1 (tool): a vector of three reals read off a function on `Fin 3`. -/
theorem fun_fin3 (f : Fin 3 → ℝ) : f = ![f 0, f 1, f 2] := by
  funext k
  fin_cases k <;> rfl

/-- **Woodford (2003), (1.1) + (1.9), §3.2: a solution `w` of the second-order system gives a
solution of the first-order system.** If `w` is adapted (`w_s` known at `t₀ + s`), bounded
together with its lags, starts from `w_{−1} = (Z_{t₀}, M_{t₀−1})` with `Z_{t₀}` known at `t₀` and
`M_{t₀−1}` known at `t₀ − 1`, and solves `P E w_{s+1} = A₁ w_s + A₂ w_{s−1} + F_s`, then the plan
`yC` and the multipliers `φC` solve (1.1) + (1.9) with these initial conditions. -/
theorem foc_of_rows (hc : c.Adm) (hγ0 : 0 < γ) {𝔼 : ExpectationSystem Ω}
    {cc : ℕ → Ω → Fin 2 → ℝ} {t0 : ℕ} {Z0 : Ω → Unit → ℝ} {M0 : Ω → Fin 2 → ℝ}
    (hM0k : KnownV 𝔼 (t0 - 1) M0) {w : ℕ → Fin 3 → Ω → ℝ}
    (hwa : ∀ s k, 𝔼.E (s + t0) (w s k) = w s k)
    (hx0k : ∀ k, 𝔼.E t0 (x0Of Z0 M0 k) = x0Of Z0 M0 k)
    (hb : ∃ B, ∀ s k ω, |w s k ω| ≤ B ∧ |lagW (x0Of Z0 M0) w s k ω| ≤ B)
    (hrows : ∀ s ω, Pm c γ *ᵥ (fun k => 𝔼.E (s + t0) (w (s + 1) k) ω) =
      A1m c γ *ᵥ (fun k => w s k ω) + A2m c γ *ᵥ (fun k => lagW (x0Of Z0 M0) w s k ω) +
        fun k => Fvec c cc t0 s k ω) :
    FOCSystem (inProblem c γ hc hγ0.le) 𝔼 cc t0 Z0 M0 (yC c t0 (x0Of Z0 M0) w)
      (φC c γ t0 (x0Of Z0 M0) w) := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hlx : c.lx ≠ 0 := hc.2.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  set x0 := x0Of Z0 M0 with hx0
  set y := yC c t0 x0 w with hy
  set φ := φC c γ t0 x0 w with hφ
  -- the lags are known
  have hlagk : ∀ s k, 𝔼.E (s + t0) (lagW x0 w s k) = lagW x0 w s k := by
    intro s k
    cases s with
    | zero => rw [zero_add]; exact hx0k k
    | succ s => exact ForwardSolution.E_of_known 𝔼 (by omega) (hwa s k)
  -- the function forms at `t₀ + s + 1`
  have hπf : ∀ s, piOf y (s + t0 + 1) = w (s + 1) 0 := by
    intro s
    funext ω'
    have := (yC_at c t0 x0 w (s + 1) ω').1
    rwa [show s + 1 + t0 = s + t0 + 1 by omega] at this
  have hxf : ∀ s, xOf y (s + t0 + 1) = fun ω' => c.xstar + c.lx⁻¹ * (c.κ * w (s + 1) 1 ω' -
      w (s + 1) 2 ω' + c.β⁻¹ * w s 2 ω') := by
    intro s
    funext ω'
    have := (yC_at c t0 x0 w (s + 1) ω').2.2.1
    rwa [show s + 1 + t0 = s + t0 + 1 by omega] at this
  have hξf : ∀ s, (fun ω' => φ (s + t0 + 1) ω' (Sum.inl ())) = fun ω' => -(c.β * γ) *
      (w (s + 1) 1 ω' + (w (s + 1) 0 ω' - γ * w s 0 ω')) := by
    intro s
    funext ω'
    have := (φC_at c γ t0 x0 w (s + 1) ω').1
    rwa [show s + 1 + t0 = s + t0 + 1 by omega] at this
  have hEx : ∀ s ω, 𝔼.E (s + t0) (xOf y (s + t0 + 1)) ω = c.xstar + c.lx⁻¹ * (c.κ *
      𝔼.E (s + t0) (w (s + 1) 1) ω - 𝔼.E (s + t0) (w (s + 1) 2) ω + c.β⁻¹ * w s 2 ω) := by
    intro s ω
    rw [hxf, ExpectationTools.E_fun_add, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add,
      ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_mul,
      𝔼.const]
    rw [hwa s 2]
  have hEξ : ∀ s ω, 𝔼.E (s + t0) (fun ω' => φ (s + t0 + 1) ω' (Sum.inl ())) ω = -(c.β * γ) *
      (𝔼.E (s + t0) (w (s + 1) 1) ω + (𝔼.E (s + t0) (w (s + 1) 0) ω - γ * w s 0 ω)) := by
    intro s ω
    rw [hξf, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add, ExpectationTools.E_fun_sub,
      ExpectationTools.E_fun_mul]
    rw [hwa s 0]
  -- the structural rows and the `π`-row of (1.9) at every date
  have hR : ∀ s ω, _ := fun s ω => (rows_iff c γ hβ hlx hli (p := w s 0 ω)
    (pE := 𝔼.E (s + t0) (w (s + 1) 0) ω) (Zt := lagW x0 w s 0 ω) (a := w s 1 ω)
    (aE := 𝔼.E (s + t0) (w (s + 1) 1) ω) (b := w s 2 ω) (bE := 𝔼.E (s + t0) (w (s + 1) 2) ω)
    (am := lagW x0 w s 1 ω) (bm := lagW x0 w s 2 ω)
    (x := c.xstar + c.lx⁻¹ * (c.κ * w s 1 ω - w s 2 ω + c.β⁻¹ * lagW x0 w s 2 ω))
    (c0 := cc (s + t0) ω 0) (c1 := cc (s + t0) ω 1) rfl rfl rfl rfl).mpr (by
      intro j
      have h := congrFun (hrows s ω) j
      rw [fun_fin3 (fun k => 𝔼.E (s + t0) (w (s + 1) k) ω), fun_fin3 (fun k => w s k ω),
        fun_fin3 (fun k => lagW x0 w s k ω)] at h
      rw [h]
      fin_cases j <;> rfl)
  -- multipliers known one period ahead
  have hmφ : MultiplierMeas 𝔼 φ := by
    intro t r
    rcases lt_trichotomy (t + 1) t0 with h | h | h
    · have e : (fun ω => φ (t + 1) ω (Sum.inr r)) = fun _ => 0 := by
        funext ω
        simp [hφ, φC, show ¬ t0 ≤ t + 1 by omega]
      rw [e, 𝔼.const]
    · have e : (fun ω => φ (t + 1) ω (Sum.inr r)) = fun ω => M0 ω r := by
        funext ω
        have := φC_at c γ t0 x0 w 0 ω
        rw [zero_add] at this
        rw [h]
        fin_cases r
        · exact this.2.1
        · exact this.2.2
      rw [e]
      have := hM0k r
      rwa [show t0 - 1 = t by omega] at this
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
      fin_cases r
      · have e : (fun ω => φ (s + t0 + 1) ω (Sum.inr 0)) = w s 1 :=
          funext fun ω => (φC_succ c γ t0 x0 w s ω).1
        change 𝔼.E (s + t0) (fun ω => φ (s + t0 + 1) ω (Sum.inr 0)) =
          fun ω => φ (s + t0 + 1) ω (Sum.inr 0)
        rw [e, hwa]
      · have e : (fun ω => φ (s + t0 + 1) ω (Sum.inr 1)) = w s 2 :=
          funext fun ω => (φC_succ c γ t0 x0 w s ω).2
        change 𝔼.E (s + t0) (fun ω => φ (s + t0 + 1) ω (Sum.inr 1)) =
          fun ω => φ (s + t0 + 1) ω (Sum.inr 1)
        rw [e, hwa]
  obtain ⟨B, hB⟩ := hb
  set K := max B 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hw : ∀ s k ω, |w s k ω| ≤ K := fun s k ω => (hB s k ω).1.trans (le_max_left _ _)
  have hl : ∀ s k ω, |lagW x0 w s k ω| ≤ K := fun s k ω => (hB s k ω).2.trans (le_max_left _ _)
  refine ⟨⟨fun t ht ω => ?_, fun ω => ?_, ?_, fun t i => ?_⟩, ?_, hmφ, fun ω => ?_,
    fun t ht ω => ?_⟩
  · -- (1.1)
    obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
    obtain ⟨y1, y2, y3, -⟩ := yC_at c t0 x0 w s ω
    have hZ1 := (yC_at c t0 x0 w (s + 1) ω).2.1
    rw [show s + 1 + t0 = s + t0 + 1 by omega] at hZ1
    refine (in_struct_at c γ hc hγ0.le 𝔼 cc y (s + t0) ω).mpr ⟨?_, ?_, ?_⟩
    · rw [hZ1, y1]
      rfl
    · rw [hπf s, y1, y2, y3]
      exact (hR s ω).1
    · rw [hπf s, hEx s ω, y3, (yC_at c t0 x0 w s ω).2.2.2]
      exact (hR s ω).2.1
  · -- the initial condition
    funext u
    have := (yC_at c t0 x0 w 0 ω).2.1
    rw [zero_add] at this
    exact this
  · -- bounded
    refine ⟨K + (|c.xstar| + |c.lx⁻¹| * ((|c.κ| + 1 + |c.β⁻¹|) * K)) +
      (|c.istar| + |c.σ / c.li| * K), fun t ω i => ?_⟩
    have p1 : 0 ≤ |c.xstar| + |c.lx⁻¹| * ((|c.κ| + 1 + |c.β⁻¹|) * K) := by positivity
    have p2 : 0 ≤ |c.istar| + |c.σ / c.li| * K := by positivity
    by_cases ht : t0 ≤ t
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
      obtain ⟨y1, y2, y3, y4⟩ := yC_at c t0 x0 w s ω
      rcases i with (u | j) | u
      · change |Zof y (s + t0) ω| ≤ _
        rw [y2]
        linarith [hl s 0 ω]
      · fin_cases j
        · change |piOf y (s + t0) ω| ≤ _
          rw [y1]
          linarith [hw s 0 ω]
        · change |xOf y (s + t0) ω| ≤ _
          rw [y3]
          have hb3 := abs_affine3 (hw s 1 ω) (hw s 2 ω) (hl s 2 ω) c.xstar c.lx⁻¹ c.κ c.β⁻¹
          linarith
      · change |iOf y (s + t0) ω| ≤ _
        rw [y4]
        have : |c.istar - c.σ / c.li * w s 2 ω| ≤ |c.istar| + |c.σ / c.li| * K := by
          refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hw s 2 ω) (abs_nonneg _)
        linarith
    · simp only [hy, yC, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      linarith
  · -- adapted
    by_cases ht : t0 ≤ t
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
      rcases i with (u | j) | u
      · have e : (fun ω => y (s + t0) ω (Sum.inl (Sum.inl u))) = lagW x0 w s 0 :=
          funext fun ω => (yC_at c t0 x0 w s ω).2.1
        change 𝔼.E (s + t0) (fun ω => y (s + t0) ω (Sum.inl (Sum.inl u))) = _
        rw [e, hlagk]
      · fin_cases j
        · have e : (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 0))) = w s 0 :=
            funext fun ω => (yC_at c t0 x0 w s ω).1
          change 𝔼.E (s + t0) (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 0))) =
            fun ω => y (s + t0) ω (Sum.inl (Sum.inr 0))
          rw [e, hwa]
        · have e : (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 1))) = fun ω => c.xstar +
              c.lx⁻¹ * (c.κ * w s 1 ω - w s 2 ω + c.β⁻¹ * lagW x0 w s 2 ω) :=
            funext fun ω => (yC_at c t0 x0 w s ω).2.2.1
          change 𝔼.E (s + t0) (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 1))) =
            fun ω => y (s + t0) ω (Sum.inl (Sum.inr 1))
          rw [e, ExpectationTools.E_fun_add, ExpectationTools.E_fun_mul,
            ExpectationTools.E_fun_add, ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul,
            ExpectationTools.E_fun_mul, 𝔼.const, hwa s 1, hwa s 2, hlagk s 2]
      · have e : (fun ω => y (s + t0) ω (Sum.inr u)) = fun ω =>
            c.istar - c.σ / c.li * w s 2 ω :=
          funext fun ω => (yC_at c t0 x0 w s ω).2.2.2
        change 𝔼.E (s + t0) (fun ω => y (s + t0) ω (Sum.inr u)) = _
        rw [e, ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul, 𝔼.const, hwa s 2]
    · have e : (fun ω => y t ω i) = fun _ => 0 := by
        funext ω
        simp [hy, yC, ht]
      change 𝔼.E t (fun ω => y t ω i) = _
      rw [e, 𝔼.const]
  · -- the multipliers are bounded
    refine ⟨|c.β * γ| * (K + (K + |γ| * K)) + K, fun t ω i => ?_⟩
    have p1 : 0 ≤ |c.β * γ| * (K + (K + |γ| * K)) := by positivity
    by_cases ht : t0 ≤ t
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
      obtain ⟨f1, f2, f3⟩ := φC_at c γ t0 x0 w s ω
      rcases i with u | j
      · rw [hφ, f1, abs_mul]
        have h1 : |w s 1 ω + (w s 0 ω - γ * lagW x0 w s 0 ω)| ≤ K + (K + |γ| * K) := by
          refine (abs_add_le _ _).trans (add_le_add (hw s 1 ω) ((abs_sub _ _).trans
            (add_le_add (hw s 0 ω) ?_)))
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hl s 0 ω) (abs_nonneg _)
        rw [abs_neg]
        nlinarith [abs_nonneg (c.β * γ)]
      · fin_cases j
        · change |φ (s + t0) ω (Sum.inr 0)| ≤ _
          rw [hφ, f2]
          linarith [hl s 1 ω]
        · change |φ (s + t0) ω (Sum.inr 1)| ≤ _
          rw [hφ, f3]
          linarith [hl s 2 ω]
    · simp only [hφ, φC, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      linarith
  · -- `M_{t₀−1}`
    funext r
    have := φC_at c γ t0 x0 w 0 ω
    rw [zero_add] at this
    fin_cases r
    · exact this.2.1
    · exact this.2.2
  · -- (1.9)
    obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
    obtain ⟨y1, y2, y3, y4⟩ := yC_at c t0 x0 w s ω
    obtain ⟨f1, f2, f3⟩ := φC_at c γ t0 x0 w s ω
    obtain ⟨g1, g2⟩ := φC_succ c γ t0 x0 w s ω
    refine (in_foc_at_iff c γ hc hγ0.le 𝔼 y hmφ (s + t0) ω).mpr ⟨?_, ?_, ?_, ?_⟩
    · simp only [Xi2]
      rw [hφ, g1, f1, y1, y2]
      field_simp
      ring
    · simp only [Xi2]
      rw [hEξ s ω, hφ, g1, f2, f3, y1, y2]
      exact (hR s ω).2.2
    · simp only [Xi1, Xi2]
      rw [hφ, g1, g2, f3, y3]
      field_simp
      ring
    · simp only [Xi1]
      rw [hφ, g2, y4]
      field_simp
      ring

end Woodford.OptimalPolicyRules.InertiaFOCSystem
