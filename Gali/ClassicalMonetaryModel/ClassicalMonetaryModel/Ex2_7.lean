/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exercise 2.7: a shopping-time model

Galí (2015), Chapter 2, Exercise 2.7, p. 50. Consuming `C` takes shopping time `S(C, M/P)` with
`S_c > 0`, `S_m ≤ 0`; period utility is `V(C, L)` with leisure `L = 1 − N − S(C, M/P)`. Write
`m = M/P`.

## (a) The implied utility `U(C, m, N) = V(C, 1 − N − S(C, m))` (`shoppingU`)

* `hasDerivAt_curve`: the chain rule along a curve, for differentiable `V : ℝ × ℝ → ℝ`.
* `hasDerivAt_U_c`, `hasDerivAt_U_m`, `hasDerivAt_U_n`: `U_c = V_C − V_L S_c`,
  `U_m = −V_L S_m`, `U_n = −V_L`.
* `U_m_nonneg`, `U_n_neg`, `U_c_lt_V_C`: `U_m ≥ 0`, `U_n < 0`, and `U_c < V_C` (the sign of
  `U_c` is ambiguous, `U_c_sign_ambiguous`).
* Second derivatives along sections (`C` fixed, `v = V(C, ·)`, `s = S(C, ·)`):
  `U_mm = v'' s'² − v' s''` (`hasDerivAt_U_mm`, `U_mm_nonpos`), `U_nn = v''`
  (`hasDerivAt_U_nn`), `U_nm = v'' s'` (`hasDerivAt_U_nm`, `U_nm_nonneg`).

## (b) Optimality and `(W/P)(−S_m) ≃ i`

* `labour_foc`, `money_foc` (**necessity**, under the budget constraint (31)): along
  `P dC = W dN`, `(W/P) U_c + U_n = 0` (eq. (4)); along the portfolio line
  `P dC = −(1 − Q) P dm`, `U_m = (1 − Q) U_c` (eq. (33)).
* `shopping_rate_eq`: hence `(W/P)(−S_m) = 1 − Q = 1 − e^{−i}` **exactly**; and
  `shopping_rate_approx`: `|(W/P)(−S_m) − i| ≤ i²` for `|i| ≤ 1`, with
  `hasDerivAt_one_sub_exp_neg` (value `0` and slope `1` at `i = 0`).

## (c) Money demand with `V = log C + χ log L`, `S = A v + B/v − 2√(AB)`, `v = C/m`

* `hasDerivAt_S_m`: `S_m = −A C/m² + B/C`; `S_nonneg`, `S_eq_zero_iff` (minimum at
  `v = √(B/A)`); `S_m_nonpos_iff` (`S_m ≤ 0 ⟺ v² ≥ B/A`).
* `money_demand`: `v² = B/A + (1 − Q) C/(A w)`, i.e. `m = C/√(B/A + (1 − Q) C/(A w))`,
  `w = W/P`; `money_demand_of_hasFDerivAt` derives it from (b).
* `money_demand_strictAnti`: real balances fall as `1 − Q` (the nominal rate) rises;
  `money_demand_satiation`: at `i = 0`, `v = √(B/A)` (finite satiation).
-/

namespace Gali.ClassicalMonetaryModel.Ex2_7

open Filter Topology

/-- Galí (2015), Ex. 2.7(a), p. 50: the implied utility `U(C, m, N) = V(C, 1 − N − S(C, m))`. -/
def shoppingU (V S : ℝ × ℝ → ℝ) (C m N : ℝ) : ℝ := V (C, 1 - N - S (C, m))

/-- Galí (2015), Ex. 2.7(a), p. 50: the chain rule along a curve,
`d/dt V(f t, g t) = f' V_1 + g' V_2`, where `V_1 = V'(1,0)`, `V_2 = V'(0,1)`. -/
theorem hasDerivAt_curve {V : ℝ × ℝ → ℝ} {V' : ℝ × ℝ →L[ℝ] ℝ} {f g : ℝ → ℝ} {a b t : ℝ}
    (hV : HasFDerivAt V V' (f t, g t)) (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => V (f s, g s)) (a * V' (1, 0) + b * V' (0, 1)) t := by
  have h := hV.comp_hasDerivAt (f := fun s => (f s, g s)) t (hf.prodMk hg)
  have hv : ((a, b) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact h

/-- Galí (2015), Ex. 2.7(a): partial derivatives of a differentiable `S : ℝ × ℝ → ℝ` along the
coordinate sections. -/
theorem hasDerivAt_sections {S : ℝ × ℝ → ℝ} {S' : ℝ × ℝ →L[ℝ] ℝ} {C m : ℝ}
    (hS : HasFDerivAt S S' (C, m)) :
    HasDerivAt (fun C' => S (C', m)) (S' (1, 0)) C ∧
      HasDerivAt (fun m' => S (C, m')) (S' (0, 1)) m := by
  constructor
  · have := hasDerivAt_curve (f := fun x => x) (g := fun _ => m) hS (hasDerivAt_id' C)
      (hasDerivAt_const C m)
    simpa using this
  · have := hasDerivAt_curve (f := fun _ => C) (g := fun x => x) hS (hasDerivAt_const m C)
      (hasDerivAt_id' m)
    simpa using this

variable {V S : ℝ × ℝ → ℝ} {V' S' : ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_c = V_C − V_L S_c`. -/
theorem hasDerivAt_U_c (hV : HasFDerivAt V V' (C, 1 - N - S (C, m)))
    (hS : HasFDerivAt S S' (C, m)) :
    HasDerivAt (fun C' => shoppingU V S C' m N) (V' (1, 0) - V' (0, 1) * S' (1, 0)) C := by
  have hL : HasDerivAt (fun C' => 1 - N - S (C', m)) (-S' (1, 0)) C := by
    have := ((hasDerivAt_sections hS).1).const_sub (1 - N)
    simpa using this
  have := hasDerivAt_curve (f := fun x => x) (g := fun C' => 1 - N - S (C', m)) (t := C) hV
    (hasDerivAt_id' C) hL
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_m = −V_L S_m`. -/
theorem hasDerivAt_U_m (hV : HasFDerivAt V V' (C, 1 - N - S (C, m)))
    (hS : HasFDerivAt S S' (C, m)) :
    HasDerivAt (fun m' => shoppingU V S C m' N) (-(V' (0, 1) * S' (0, 1))) m := by
  have hL : HasDerivAt (fun m' => 1 - N - S (C, m')) (-S' (0, 1)) m := by
    have := ((hasDerivAt_sections hS).2).const_sub (1 - N)
    simpa using this
  have := hasDerivAt_curve (f := fun _ => C) (g := fun m' => 1 - N - S (C, m')) (t := m) hV
    (hasDerivAt_const m C) hL
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_n = −V_L`. -/
theorem hasDerivAt_U_n (hV : HasFDerivAt V V' (C, 1 - N - S (C, m))) :
    HasDerivAt (fun N' => shoppingU V S C m N') (-V' (0, 1)) N := by
  have hL : HasDerivAt (fun N' => 1 - N' - S (C, m)) (-1) N :=
    ((hasDerivAt_id' N).const_sub 1).sub_const (S (C, m))
  have := hasDerivAt_curve (f := fun _ => C) (g := fun N' => 1 - N' - S (C, m)) (t := N) hV
    (hasDerivAt_const N C) hL
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: with `V_L > 0` and `S_m ≤ 0`, `U_m = −V_L S_m ≥ 0`. -/
theorem U_m_nonneg {VL Sm : ℝ} (hVL : 0 < VL) (hSm : Sm ≤ 0) : 0 ≤ -(VL * Sm) := by
  nlinarith

/-- Galí (2015), Ex. 2.7(a), p. 50: with `V_L > 0`, `U_n = −V_L < 0`. -/
theorem U_n_neg {VL : ℝ} (hVL : 0 < VL) : -VL < 0 := by linarith

/-- Galí (2015), Ex. 2.7(a), p. 50: with `V_L > 0` and `S_c > 0`, `U_c = V_C − V_L S_c < V_C`:
shopping time lowers the marginal utility of consumption. -/
theorem U_c_lt_V_C {VC VL Sc : ℝ} (hVL : 0 < VL) (hSc : 0 < Sc) : VC - VL * Sc < VC := by
  nlinarith

/-- Galí (2015), Ex. 2.7(a), p. 50: the sign of `U_c = V_C − V_L S_c` is not determined by the
signs of `V_C, V_L, S_c > 0` alone. -/
theorem U_c_sign_ambiguous :
    (0 : ℝ) < 1 - 1 * (1 / 2) ∧ (1 : ℝ) - 1 * 2 < 0 := by norm_num

/-- Galí (2015), Ex. 2.7(a), p. 50: along the section `m ↦ U(C, m, N)` with `v = V(C, ·)`,
`s = S(C, ·)`: `U_m = −v'(L) s'(m)`. -/
theorem hasDerivAt_section_m {v v' s s' : ℝ → ℝ} {N m : ℝ}
    (hv : ∀ L, HasDerivAt v (v' L) L) (hs : HasDerivAt s (s' m) m) :
    HasDerivAt (fun m' => v (1 - N - s m')) (-(v' (1 - N - s m) * s' m)) m := by
  have := (hv (1 - N - s m)).comp m (hs.const_sub (1 - N))
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_mm = v''(L) s'(m)² − v'(L) s''(m)`. -/
theorem hasDerivAt_U_mm {v' v'' s s' s'' : ℝ → ℝ} {N m : ℝ}
    (hv' : ∀ L, HasDerivAt v' (v'' L) L) (hs : HasDerivAt s (s' m) m)
    (hs' : HasDerivAt s' (s'' m) m) :
    HasDerivAt (fun m' => -(v' (1 - N - s m') * s' m'))
      (v'' (1 - N - s m) * s' m ^ 2 - v' (1 - N - s m) * s'' m) m := by
  have h1 := (hv' (1 - N - s m)).comp m (hs.const_sub (1 - N))
  have := (h1.mul hs').neg
  exact this.congr_deriv (by simp only [Function.comp_def]; ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_mm ≤ 0` when `V` is concave in leisure (`v'' ≤ 0`),
`V_L ≥ 0`, and shopping time is convex in real balances (`s'' ≥ 0`). -/
theorem U_mm_nonpos {vpp vp sp spp : ℝ} (hvpp : vpp ≤ 0) (hvp : 0 ≤ vp) (hspp : 0 ≤ spp) :
    vpp * sp ^ 2 - vp * spp ≤ 0 := by
  nlinarith [sq_nonneg sp, mul_nonneg hvp hspp]

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_n = −v'(L)` along `N`, and `U_nn = v''(L) ≤ 0` when `V`
is concave in leisure. -/
theorem hasDerivAt_U_nn {v v' v'' : ℝ → ℝ} {N sm : ℝ} (hv : ∀ L, HasDerivAt v (v' L) L)
    (hv' : ∀ L, HasDerivAt v' (v'' L) L) :
    HasDerivAt (fun N' => v (1 - N' - sm)) (-v' (1 - N - sm)) N ∧
      HasDerivAt (fun N' => -v' (1 - N' - sm)) (v'' (1 - N - sm)) N := by
  have hL : HasDerivAt (fun N' : ℝ => 1 - N' - sm) (-1) N :=
    ((hasDerivAt_id' N).const_sub 1).sub_const sm
  constructor
  · have := (hv (1 - N - sm)).comp N hL
    exact this.congr_deriv (by ring)
  · have := ((hv' (1 - N - sm)).comp N hL).neg
    exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: the cross derivative `U_nm = v''(L) s'(m)`
(differentiating `U_n = −v'(1 − N − s(m))` in `m`). -/
theorem hasDerivAt_U_nm {v' v'' s s' : ℝ → ℝ} {N m : ℝ}
    (hv' : ∀ L, HasDerivAt v' (v'' L) L) (hs : HasDerivAt s (s' m) m) :
    HasDerivAt (fun m' => -v' (1 - N - s m')) (v'' (1 - N - s m) * s' m) m := by
  have := ((hv' (1 - N - s m)).comp m (hs.const_sub (1 - N))).neg
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.7(a), p. 50: `U_nm = v'' s' ≥ 0` when `v'' ≤ 0` and `S_m ≤ 0`: more real
balances save shopping time and so raise the marginal disutility-of-work term. -/
theorem U_nm_nonneg {vpp sp : ℝ} (hvpp : vpp ≤ 0) (hsp : sp ≤ 0) : 0 ≤ vpp * sp :=
  mul_nonneg_of_nonpos_of_nonpos hvpp hsp

/-! ### (b) Optimality conditions -/

/-- Galí (2015), Ex. 2.7(b), with eq. (4), p. 19 (**necessity**): if hours `N` are a local
optimum along the budget line `P C = W N + X` (from (31), everything else fixed), then
`(W/P) U_c + U_n = 0`. -/
theorem labour_foc {P W X L : ℝ} (hP : 0 < P) (hbud : P * C = W * N + X)
    (hL : L = 1 - N - S (C, m)) (hV : HasFDerivAt V V' (C, L)) (hS : HasFDerivAt S S' (C, m))
    (hloc : IsLocalMax (fun N' => shoppingU V S ((W * N' + X) / P) m N') N) :
    W / P * (V' (1, 0) - V' (0, 1) * S' (1, 0)) + -V' (0, 1) = 0 := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hc : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id' N).const_mul W).add_const X).div_const P
    simpa using this
  have hSc : HasDerivAt (fun N' => S ((W * N' + X) / P, m)) (W / P * S' (1, 0)) N := by
    have := hasDerivAt_curve (f := fun N' => (W * N' + X) / P) (g := fun _ => m)
      (by rw [hCeq]; exact hS) hc (hasDerivAt_const N m)
    simpa using this
  have hl : HasDerivAt (fun N' => 1 - N' - S ((W * N' + X) / P, m)) (-1 - W / P * S' (1, 0))
      N := by
    have := ((hasDerivAt_id' N).const_sub 1).sub hSc
    convert this using 1
  have hg := hasDerivAt_curve (f := fun N' => (W * N' + X) / P)
    (g := fun N' => 1 - N' - S ((W * N' + X) / P, m)) (by rw [hCeq, ← hL]; exact hV) hc hl
  have h0 := hloc.hasDerivAt_eq_zero hg
  linear_combination h0

/-- Galí (2015), Ex. 2.7(b), with eq. (33), p. 32 (**necessity**): along the portfolio line
`P C + (1 − Q) P m = X` (budget (32), total wealth fixed), a local optimum `m` satisfies
`U_m = (1 − Q) U_c`. -/
theorem money_foc {P Q X L : ℝ} (hP : 0 < P) (hbud : P * C + (1 - Q) * P * m = X)
    (hL : L = 1 - N - S (C, m)) (hV : HasFDerivAt V V' (C, L)) (hS : HasFDerivAt S S' (C, m))
    (hloc : IsLocalMax (fun m' => shoppingU V S ((X - (1 - Q) * P * m') / P) m' N) m) :
    -(V' (0, 1) * S' (0, 1)) = (1 - Q) * (V' (1, 0) - V' (0, 1) * S' (1, 0)) := by
  have hCeq : (X - (1 - Q) * P * m) / P = C := by rw [← hbud]; field_simp; ring
  have hc : HasDerivAt (fun m' : ℝ => (X - (1 - Q) * P * m') / P) (-(1 - Q)) m := by
    have := (((hasDerivAt_id' m).const_mul ((1 - Q) * P)).const_sub X).div_const P
    convert this using 1
    field_simp
  have hSm : HasDerivAt (fun m' => S ((X - (1 - Q) * P * m') / P, m'))
      (-(1 - Q) * S' (1, 0) + 1 * S' (0, 1)) m :=
    hasDerivAt_curve (f := fun m' => (X - (1 - Q) * P * m') / P) (g := fun m' => m')
      (by rw [hCeq]; exact hS) hc (hasDerivAt_id' m)
  have hl : HasDerivAt (fun m' => 1 - N - S ((X - (1 - Q) * P * m') / P, m'))
      (-(-(1 - Q) * S' (1, 0) + 1 * S' (0, 1))) m := by
    have := hSm.const_sub (1 - N)
    convert this using 1
  have hg := hasDerivAt_curve (f := fun m' => (X - (1 - Q) * P * m') / P)
    (g := fun m' => 1 - N - S ((X - (1 - Q) * P * m') / P, m')) (by rw [hCeq, ← hL]; exact hV)
    hc hl
  have h0 := hloc.hasDerivAt_eq_zero hg
  linear_combination h0

/-- Galí (2015), Ex. 2.7(b), p. 50: combining (4) and (33) (with `V_L ≠ 0`):
`(W/P)(−S_m) = 1 − Q` **exactly**. -/
theorem shopping_rate_eq {w Q VC VL Sc Sm : ℝ} (hVL : VL ≠ 0)
    (hlab : w * (VC - VL * Sc) + -VL = 0) (hmon : -(VL * Sm) = (1 - Q) * (VC - VL * Sc)) :
    w * -Sm = 1 - Q := by
  have hUc : VC - VL * Sc ≠ 0 := by
    intro h0; rw [h0, mul_zero, zero_add, neg_eq_zero] at hlab; exact hVL hlab
  have h1 : w * (VC - VL * Sc) = VL := by linarith
  have h2 : (w * -Sm) * (VC - VL * Sc) = (1 - Q) * (VC - VL * Sc) := by
    rw [← hmon]; linear_combination (-Sm) * h1
  exact mul_right_cancel₀ hUc h2

/-- Galí (2015), p. 32: `i ↦ 1 − e^{−i}` vanishes at `0` with slope `1`, so `1 − e^{−i} ≃ i`. -/
theorem hasDerivAt_one_sub_exp_neg :
    HasDerivAt (fun i : ℝ => 1 - Real.exp (-i)) 1 0 ∧ 1 - Real.exp (-(0 : ℝ)) = 0 := by
  refine ⟨?_, by simp⟩
  have := ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)).const_sub 1
  simpa using this

/-- Galí (2015), Ex. 2.7(b), p. 50 (**precise first-order statement**): under the optimal plan
`(W/P)(−S_m) = 1 − e^{−i}`, and `|(W/P)(−S_m) − i| ≤ i²` for `|i| ≤ 1`. -/
theorem shopping_rate_approx {w Sm i : ℝ} (h : w * -Sm = 1 - Real.exp (-i)) (hi : |i| ≤ 1) :
    |w * -Sm - i| ≤ i ^ 2 := by
  have hb := Real.abs_exp_sub_one_sub_id_le (x := -i) (by rwa [abs_neg])
  rw [h, show 1 - Real.exp (-i) - i = -(Real.exp (-i) - 1 - -i) by ring, abs_neg]
  simpa using hb

/-! ### (c) Money demand -/

/-- Galí (2015), Ex. 2.7(c), p. 50 (Schmitt-Grohé and Uribe 2011): shopping time
`S(C, m) = A v + B/v − 2√(AB)` with velocity `v = C/m` (`v = P C/M`). -/
noncomputable def sguS (A B C m : ℝ) : ℝ := A * (C / m) + B / (C / m) - 2 * Real.sqrt (A * B)

/-- Galí (2015), Ex. 2.7(c): `S_m = −A C/m² + B/C`. -/
theorem hasDerivAt_S_m {A B C m : ℝ} (hC : C ≠ 0) (hm : m ≠ 0) :
    HasDerivAt (fun m' => sguS A B C m') (-(A * C / m ^ 2) + B / C) m := by
  have hfun : (fun m' => sguS A B C m') = fun m' => A * C * m'⁻¹ + B / C * m' -
      2 * Real.sqrt (A * B) := by
    funext m'
    rw [sguS]
    by_cases h0 : m' = 0
    · simp [h0]
    · field_simp
  rw [hfun]
  have := ((((hasDerivAt_inv hm).const_mul (A * C)).add
    ((hasDerivAt_id' m).const_mul (B / C))).sub_const (2 * Real.sqrt (A * B)))
  convert this using 1
  field_simp

/-- Galí (2015), Ex. 2.7(c): `S · v = (√A v − √B)²` for `A, B ≥ 0` and `v = C/m ≠ 0`. -/
theorem S_mul_v {A B C m : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hv : C / m ≠ 0) :
    sguS A B C m * (C / m) = (Real.sqrt A * (C / m) - Real.sqrt B) ^ 2 := by
  have hsq : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  have hBv : B / (C / m) * (C / m) = B := div_mul_cancel₀ B hv
  rw [sguS, hsq]
  linear_combination (-(C / m) ^ 2) * h1 + hBv - h2

/-- Galí (2015), Ex. 2.7(c): shopping time is nonnegative, `S ≥ 0` (for `A, B ≥ 0`, `v > 0`). -/
theorem S_nonneg {A B C m : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hv : 0 < C / m) :
    0 ≤ sguS A B C m := by
  have h := S_mul_v hA hB hv.ne'
  have : 0 ≤ sguS A B C m * (C / m) := by rw [h]; exact sq_nonneg _
  exact nonneg_of_mul_nonneg_left this hv

/-- Galí (2015), Ex. 2.7(c): for `A > 0`, `B ≥ 0` shopping time is zero exactly at
`v² = B/A`. -/
theorem S_eq_zero_iff {A B C m : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hv : 0 < C / m) :
    sguS A B C m = 0 ↔ (C / m) ^ 2 = B / A := by
  have h1 := Real.sq_sqrt hA.le
  have h2 := Real.sq_sqrt hB
  have hval := S_mul_v hA.le hB hv.ne'
  have hnn : 0 ≤ Real.sqrt A * (C / m) := mul_nonneg (Real.sqrt_nonneg A) hv.le
  constructor
  · intro h
    rw [h, zero_mul] at hval
    have : Real.sqrt A * (C / m) = Real.sqrt B := by
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 hval.symm
      linarith
    rw [eq_div_iff hA.ne', ← h1, ← h2, ← this]
    ring
  · intro h
    have hB' : Real.sqrt A * (C / m) = Real.sqrt B := by
      have : (Real.sqrt A * (C / m)) ^ 2 = Real.sqrt B ^ 2 := by
        rw [mul_pow, h, h1, h2]; field_simp
      exact (pow_left_inj₀ hnn (Real.sqrt_nonneg B) two_ne_zero).1 this
    rw [hB', sub_self, zero_pow two_ne_zero] at hval
    exact (mul_eq_zero.1 hval).resolve_right hv.ne'

/-- Galí (2015), Ex. 2.7(c): `S_m ≤ 0` (the book's assumption) iff `v² ≥ B/A`. -/
theorem S_m_nonpos_iff {A B C m : ℝ} (hA : 0 < A) (hC : 0 < C) (hm : 0 < m) :
    -(A * C / m ^ 2) + B / C ≤ 0 ↔ B / A ≤ (C / m) ^ 2 := by
  rw [div_le_iff₀ hA]
  constructor
  · intro h
    have : B / C ≤ A * C / m ^ 2 := by linarith
    rw [div_le_div_iff₀ hC (by positivity)] at this
    rw [div_pow]
    rw [mul_comm, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith
  · intro h
    rw [div_pow, mul_comm, ← mul_div_assoc, le_div_iff₀ (by positivity)] at h
    have : B / C ≤ A * C / m ^ 2 := by
      rw [div_le_div_iff₀ hC (by positivity)]
      nlinarith
    linarith

/-- Galí (2015), Ex. 2.7(c), p. 50 (**money demand**): if `w (−S_m) = 1 − Q` (part (b)) with
`w = W/P > 0`, `A > 0`, `C, m > 0`, then `v² = B/A + (1 − Q) C/(A w)` and
`m = C/√(B/A + (1 − Q) C/(A w))`. -/
theorem money_demand {A B C m w Q : ℝ} (hA : 0 < A) (hC : 0 < C) (hm : 0 < m) (hw : 0 < w)
    (h : w * -(-(A * C / m ^ 2) + B / C) = 1 - Q) :
    (C / m) ^ 2 = B / A + (1 - Q) * C / (A * w) ∧
      m = C / Real.sqrt (B / A + (1 - Q) * C / (A * w)) := by
  have hv : (C / m) ^ 2 = B / A + (1 - Q) * C / (A * w) := by
    rw [← h]
    field_simp
    ring
  refine ⟨hv, ?_⟩
  rw [← hv, Real.sqrt_sq (div_pos hC hm).le]
  field_simp

/-- Galí (2015), Ex. 2.7(c), p. 50: the money demand derived from part (b): if `S = sguS A B`
has derivative `S'` at `(C, m)` and `w (−S_m) = 1 − Q` with `S_m = S'(0,1)`, then
`m = C/√(B/A + (1 − Q) C/(A w))`. -/
theorem money_demand_of_hasFDerivAt {A B C m w Q : ℝ} {S' : ℝ × ℝ →L[ℝ] ℝ} (hA : 0 < A)
    (hC : 0 < C) (hm : 0 < m) (hw : 0 < w)
    (hS : HasFDerivAt (fun p : ℝ × ℝ => sguS A B p.1 p.2) S' (C, m))
    (h : w * -S' (0, 1) = 1 - Q) :
    m = C / Real.sqrt (B / A + (1 - Q) * C / (A * w)) := by
  have h1 := (hasDerivAt_sections hS).2
  have h2 := hasDerivAt_S_m (A := A) (B := B) hC.ne' hm.ne'
  rw [h1.unique h2] at h
  exact (money_demand hA hC hm hw h).2

/-- Galí (2015), Ex. 2.7(c), p. 50: money demand is strictly decreasing in the opportunity cost
`1 − Q = 1 − e^{−i}` (for `A, B, C, w > 0`, nonnegative rates). -/
theorem money_demand_strictAnti {A B C w : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hw : 0 < w) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    C / Real.sqrt (B / A + y * C / (A * w)) < C / Real.sqrt (B / A + x * C / (A * w)) := by
  have hAw : 0 < A * w := mul_pos hA hw
  have h0 : 0 < B / A + x * C / (A * w) := by positivity
  have hlt : B / A + x * C / (A * w) < B / A + y * C / (A * w) := by
    have : x * C / (A * w) < y * C / (A * w) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hxy hC) hAw
    linarith
  exact div_lt_div_of_pos_left hC (Real.sqrt_pos.2 h0) (Real.sqrt_lt_sqrt h0.le hlt)

/-- Galí (2015), Ex. 2.7(c), p. 50: at the Friedman rule (`Q = 1`, `i = 0`) velocity is
`v = √(B/A)`, the shopping-time minimum: real balances satiate at a finite level. -/
theorem money_demand_satiation {A B C m w : ℝ} (hA : 0 < A) (hC : 0 < C) (hm : 0 < m)
    (hw : 0 < w) (h : w * -(-(A * C / m ^ 2) + B / C) = 1 - 1) :
    C / m = Real.sqrt (B / A) := by
  have hv := (money_demand hA hC hm hw h).1
  rw [sub_self, zero_mul, zero_div, add_zero] at hv
  rw [← hv, Real.sqrt_sq (div_pos hC hm).le]

end Gali.ClassicalMonetaryModel.Ex2_7
