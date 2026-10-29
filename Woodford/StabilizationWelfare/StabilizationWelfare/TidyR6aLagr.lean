/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aTreeSum
import StabilizationWelfare.TidyR5RamseyDate0

/-!
# The Lagrangian of the exact date-0 Ramsey problem on an event tree

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (Benigno–Woodford: welfare
`E_0 ∑βᵗ[u(Y_t) − v(Y_t)Δ_t]` subject to the exact Calvo constraints) and Chapter 7, §1 (the
Lagrangian of the Ramsey problem, the date-0 problem with no lagged multipliers).

In the efficient frame (`A_u = A_v = A`; a distortion is a constant disturbance,
`TidyR5RamseyDate0.absorb`) the planner's objective is `W(r) = S[U(r)]`
(`TidyR6aTreeSum.S` the expected discounted sum), with the period utility `Uw` (equal to
`u(Y) − v(Y)Δ` up to a term that depends only on the disturbances), over plans `r` that satisfy
the four exact constraints at every node (`Feas`: the `F` and `K` recursions, the price index,
the dispersion law with the given `Δ_{−1}`). For a plan `w` solving the exact first-order
conditions (`TidyR5RamseyDate0.RamseyL` with the date-0 root lag) and any feasible `r = w + h`:

* `Lnode`: the Lagrangian density at a node, with the multipliers of `w` and the LAGGED
  multipliers of the `F`, `K` recursions (the law of iterated expectations moves `βλE_t[·]` to the
  next node); `lnode_expand`: the EXACT identity
  `Lnode(w + h) − Lnode(w) = ∑ᵢ Qᵢ hᵢ + P h_{Δ,−1} + R2`, with `Qᵢ` the first-order conditions
  (`NonlinearNKMarkovRamsey.ramseyQ`), `P = −αλ₄e^{aπ}` and the second-order remainder `R2`
  written with the atoms `E2(z) = eᶻ − 1 − z` and `Gx(c, h) − h`.
* **`welfare_lagrangian`**: for feasible bounded `r`, `W(r) = S[Lnode(r)]` at every root
  (the constraint terms vanish; the lagged-multiplier terms cancel the expectation terms by
  regrouping, `TidyR6aTreeSum.S_lag`, and the date-0 lagged multipliers are zero).
* **`foc_kill`**: the first-order terms vanish in `S` at every root.
* **`welfare_diff`**: `W(r) − W(w) = S[R2]` at every root, exactly.
-/

namespace Woodford.StabilizationWelfare.TidyR6aLagr

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyTree
open TidyR6aTreeSum TidyR5RamseyDate0

/-- Woodford (2003), §5: the utility kernel `Gx(c, t) = (e^{ct} − 1)/c` (`= t` for `c = 0`), with
`d/dt Gx(c, t) = e^{ct}`; `A e^{σĉ} Gx(1 − σ, ŷ)` is `u(Y)` up to a constant. -/
noncomputable def Gx (c t : ℝ) : ℝ := if c = 0 then t else (Real.exp (c * t) - 1) / c

/-- Woodford (2003), §5: the second-order atom `E2(z) = eᶻ − 1 − z`. -/
noncomputable def E2 (z : ℝ) : ℝ := Real.exp z - 1 - z

/-- The exponential splits along increments: `e^{u+v} = eᵘ(1 + v + E2(v))`. -/
theorem exp_split (u v : ℝ) : Real.exp (u + v) = Real.exp u * (1 + v + E2 v) := by
  unfold E2; rw [Real.exp_add]; ring

/-- Woodford (2003), §5: `Gx(c, t + h) = Gx(c, t) + e^{ct}h + e^{ct}(Gx(c, h) − h)`. -/
theorem Gx_split (c t h : ℝ) :
    Gx c (t + h) = Gx c t + Real.exp (c * t) * h + Real.exp (c * t) * (Gx c h - h) := by
  unfold Gx
  split_ifs with hc
  · subst hc; simp
  · rw [show c * (t + h) = c * t + c * h by ring, Real.exp_add]
    field_simp
    ring

/-- Woodford (2003), §5: `Gx(c, ·)` has derivative `e^{ct}` (so `A e^{σĉ}Gx(1 − σ, ŷ)` has
marginal utility `A e^{(1−σ)ŷ + σĉ}`, the first term of the output condition in
`NonlinearNKMarkovRamsey.ramseyQ`). -/
theorem hasDerivAt_Gx (c t : ℝ) : HasDerivAt (Gx c) (Real.exp (c * t)) t := by
  unfold Gx
  by_cases hc : c = 0
  · subst hc; simp only [↓reduceIte, zero_mul, Real.exp_zero]; exact hasDerivAt_id' t
  · simp only [hc, ↓reduceIte]
    have h1 : HasDerivAt (fun x => Real.exp (c * x)) (Real.exp (c * t) * c) t := by
      simpa using ((hasDerivAt_id t).const_mul c).exp
    have h2 := (h1.sub_const 1).div_const c
    convert h2 using 1
    field_simp

/-- Woodford (2003), §5 (**the period utility in the efficient frame**):
`A e^{σĉ}Gx(1 − σ, ŷ) − AΔ e^{(1+ω)ŷ − ωq}/(1+ω)`, i.e. `u(Y) − v(Y)Δ` up to a function of
the disturbances, for `v = (ŷ, π, F̂, K̂, Δ, …)`. -/
noncomputable def Uw (p : Par) (A : ℝ) (e : Fin 5 → ℝ) (v : Fin 9 → ℝ) : ℝ :=
  A * Real.exp (p.σ * e 1) * Gx (1 - p.σ) (v 0) -
    A * v 4 * Real.exp ((1 + p.ω) * v 0 - p.ω * e 3) / (1 + p.ω)

/-- Woodford (2003), Ch. 7: the reset-price gap `x̂ = (K̂ − F̂)/(1+ωθ)`. -/
noncomputable def xr (p : Par) (v : Fin 9 → ℝ) : ℝ := (v 3 - v 2) / p.c0

/-- Woodford (2003), Ch. 7: the lagged dispersion of a plan, `Δ_{−1}` at the roots. -/
def lagDv {Y : Type*} (T : LagTree Y) (Dm1 : ℝ) (r : Y → Fin 9 → ℝ) (x : Y) : ℝ :=
  if T.depth x = 0 then Dm1 else r (T.par x) 4

/-- Woodford (2003), §5 and Ch. 3 (**a feasible plan**): at every node the exact `F` and `K`
recursions, the price index and the dispersion law (with initial dispersion `Δ_{−1}`) hold. -/
def Feas {Y : Type*} (T : LagTree Y) (p : Par) (e : Y → Fin 5 → ℝ) (Dm1 : ℝ)
    (r : Y → Fin 9 → ℝ) : Prop :=
  ∀ x, (Real.exp (r x 2) - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * r x 0 + p.σ * e x 1 + e x 2) -
      p.α * p.β * T.M (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2)) x = 0) ∧
    (Real.exp (r x 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * r x 0 - p.ω * e x 3 + e x 4) -
      p.α * p.β * T.M (fun y => Real.exp (aE p * r y 1 + r y 3)) x = 0) ∧
    (p.α * (Real.exp ((p.θ - 1) * r x 1) - 1) +
      (1 - p.α) * (Real.exp (-((p.θ - 1) * xr p (r x))) - 1) = 0) ∧
    (r x 4 - p.α * lagDv T Dm1 r x * Real.exp (aE p * r x 1) -
      (1 - p.α) * Real.exp (-(aE p * xr p (r x))) = 0)

/-- Woodford (2003), Ch. 7: a solution of the exact Ramsey conditions with root lag `Δ_{−1}` is
feasible. -/
theorem feas_of_ramsey {Y : Type*} (T : LagTree Y) (p : Par) (R : RPar) (e : Y → Fin 5 → ℝ)
    (lag : Fin 9 → ℝ) (w : Y → Fin 9 → ℝ) (hw : RamseyL T p R e lag w) :
    Feas T p e (lag 4) w := by
  intro x
  have h5 := congrFun (hw x) 5
  have h6 := congrFun (hw x) 6
  have h7 := congrFun (hw x) 7
  have h8 := congrFun (hw x) 8
  have hM : ∀ i, Mv T.M (fun y => ramseyN p (w y)) x i = T.M (fun y => ramseyN p (w y) i) x :=
    fun i => rfl
  have hM5 : T.M (fun y => ramseyN p (w y) 5) x =
      -(p.α * p.β) * T.M (fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2)) x := by
    have e0 : (fun y => ramseyN p (w y) 5) =
        (-(p.α * p.β)) • fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2) := by
      funext y; simp only [ramseyN, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]; ring
    rw [e0, map_smul]; rfl
  have hM6 : T.M (fun y => ramseyN p (w y) 6) x =
      -(p.α * p.β) * T.M (fun y => Real.exp (aE p * w y 1 + w y 3)) x := by
    have e0 : (fun y => ramseyN p (w y) 6) =
        (-(p.α * p.β)) • fun y => Real.exp (aE p * w y 1 + w y 3) := by
      funext y; simp only [ramseyN, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]; ring
    rw [e0, map_smul]; rfl
  have hM78 : ∀ i, i = 7 ∨ i = 8 → T.M (fun y => ramseyN p (w y) i) x = 0 := by
    intro i hi
    have e0 : (fun y => ramseyN p (w y) i) = fun _ => (0 : ℝ) := by
      funext y; rcases hi with h | h <;> subst h <;> simp [ramseyN]
    rw [e0, M_const T]
  simp only [Pi.add_apply, Pi.zero_apply, hM, hM5, hM6, hM78 7 (by simp), hM78 8 (by simp),
    ramseyQ, Matrix.cons_val, add_zero] at h5 h6 h7 h8
  refine ⟨by linear_combination h5, by linear_combination h6, ?_, ?_⟩
  · simp only [xr]; linear_combination h7
  · simp only [xr, lagDv]
    split_ifs with hx <;> simp only [hx, ↓reduceIte] at h8 <;> linear_combination h8

/-- Woodford (2003), §5 and Ch. 7 (**the Lagrangian density at a node**), with the multipliers
lw of the plan at the node, the lagged multipliers `m₅, m₆` of the `F`, `K` recursions, the
lagged dispersion Dp and the real variables `v`. -/
noncomputable def Lnode (p : Par) (A : ℝ) (e : Fin 5 → ℝ) (m5 m6 : ℝ) (lw : Fin 9 → ℝ) (Dp : ℝ)
    (v : Fin 9 → ℝ) : ℝ :=
  Uw p A e v +
    lw 5 * (Real.exp (v 2) - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * v 0 + p.σ * e 1 + e 2)) +
    lw 6 * (Real.exp (v 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * v 0 - p.ω * e 3 + e 4)) +
    lw 7 * (p.α * (Real.exp ((p.θ - 1) * v 1) - 1) +
      (1 - p.α) * (Real.exp (-((p.θ - 1) * xr p v)) - 1)) +
    lw 8 * (v 4 - p.α * Dp * Real.exp (aE p * v 1) - (1 - p.α) * Real.exp (-(aE p * xr p v))) -
    p.α * m5 * Real.exp ((p.θ - 1) * v 1 + v 2) - p.α * m6 * Real.exp (aE p * v 1 + v 3)

/-- Woodford (2003), §5 and Ch. 7 (**the exact second-order remainder of the Lagrangian
density**) at the plan `w` (lagged dispersion Dp) in the direction `h` (lagged `h_Δ = hDp`). -/
noncomputable def R2 (p : Par) (A : ℝ) (e : Fin 5 → ℝ) (m5 m6 : ℝ) (w : Fin 9 → ℝ) (Dp : ℝ)
    (h : Fin 9 → ℝ) (hDp : ℝ) : ℝ :=
  A * Real.exp (p.σ * e 1) * Real.exp ((1 - p.σ) * w 0) * (Gx (1 - p.σ) (h 0) - h 0) -
    A * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω) *
      (w 4 * E2 ((1 + p.ω) * h 0) + h 4 * (Real.exp ((1 + p.ω) * h 0) - 1)) +
    w 5 * Real.exp (w 2) * E2 (h 2) -
    w 5 * (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w 0 + p.σ * e 1 + e 2) *
      E2 ((1 - p.σ) * h 0) +
    w 6 * Real.exp (w 3) * E2 (h 3) -
    w 6 * (1 - p.α * p.β) * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3 + e 4) *
      E2 ((1 + p.ω) * h 0) +
    w 7 * (p.α * Real.exp ((p.θ - 1) * w 1) * E2 ((p.θ - 1) * h 1) +
      (1 - p.α) * Real.exp (-((p.θ - 1) * xr p w)) * E2 (-((p.θ - 1) * xr p h))) -
    w 8 * (p.α * Real.exp (aE p * w 1) *
        (Dp * E2 (aE p * h 1) + hDp * (Real.exp (aE p * h 1) - 1)) +
      (1 - p.α) * Real.exp (-(aE p * xr p w)) * E2 (-(aE p * xr p h))) -
    p.α * m5 * Real.exp ((p.θ - 1) * w 1 + w 2) * E2 ((p.θ - 1) * h 1 + h 2) -
    p.α * m6 * Real.exp (aE p * w 1 + w 3) * E2 (aE p * h 1 + h 3)

/-- **Woodford (2003), §5 and Ch. 7 (the exact second-order expansion of the Lagrangian
density).** For the efficient-frame economy `R0 A`,
`Lnode(w + h) − Lnode(w) = ∑_{i ≤ 4} Qᵢ hᵢ − αλ₄e^{aπ}h_{Δ,−1} + R2`, where `Qᵢ` are the
first-order conditions `ramseyQ` at `w` with lagged `(Δ, λ₁, λ₂) = (Dp, m₅, m₆)`. -/
theorem lnode_expand {p : Par} (hω : 1 + p.ω ≠ 0) (A : ℝ) (e : Fin 5 → ℝ) (m5 m6 : ℝ)
    (w : Fin 9 → ℝ) (Dp : ℝ) (h : Fin 9 → ℝ) (hDp : ℝ) :
    Lnode p A e m5 m6 w (Dp + hDp) (w + h) - Lnode p A e m5 m6 w Dp w =
      ramseyQ p (R0 A) e ![0, 0, 0, 0, Dp, m5, m6, 0, 0] w 0 * h 0 +
      ramseyQ p (R0 A) e ![0, 0, 0, 0, Dp, m5, m6, 0, 0] w 1 * h 1 +
      ramseyQ p (R0 A) e ![0, 0, 0, 0, Dp, m5, m6, 0, 0] w 2 * h 2 +
      ramseyQ p (R0 A) e ![0, 0, 0, 0, Dp, m5, m6, 0, 0] w 3 * h 3 +
      ramseyQ p (R0 A) e ![0, 0, 0, 0, Dp, m5, m6, 0, 0] w 4 * h 4 +
      (-(p.α * w 8 * Real.exp (aE p * w 1))) * hDp + R2 p A e m5 m6 w Dp h hDp := by
  have hxr : xr p (w + h) = xr p w + xr p h := by simp only [xr, Pi.add_apply]; ring
  have X0 : Real.exp ((1 - p.σ) * w 0 + p.σ * e 1) =
      Real.exp (p.σ * e 1) * Real.exp ((1 - p.σ) * w 0) := by rw [← Real.exp_add]; ring_nf
  have X1 : Real.exp ((1 + p.ω) * (w 0 + h 0) - p.ω * e 3) =
      Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) * (1 + (1 + p.ω) * h 0 + E2 ((1 + p.ω) * h 0)) := by
    rw [← exp_split]; ring_nf
  have X1' : Real.exp ((1 + p.ω) * h 0) = 1 + (1 + p.ω) * h 0 + E2 ((1 + p.ω) * h 0) := by
    unfold E2; ring
  have X2 : Real.exp ((1 - p.σ) * (w 0 + h 0) + p.σ * e 1 + e 2) =
      Real.exp ((1 - p.σ) * w 0 + p.σ * e 1 + e 2) *
        (1 + (1 - p.σ) * h 0 + E2 ((1 - p.σ) * h 0)) := by
    rw [← exp_split]; ring_nf
  have X3 : Real.exp ((1 + p.ω) * (w 0 + h 0) - p.ω * e 3 + e 4) =
      Real.exp ((1 + p.ω) * w 0 - p.ω * e 3 + e 4) *
        (1 + (1 + p.ω) * h 0 + E2 ((1 + p.ω) * h 0)) := by
    rw [← exp_split]; ring_nf
  have X4 : Real.exp (w 2 + h 2) = Real.exp (w 2) * (1 + h 2 + E2 (h 2)) := exp_split _ _
  have X5 : Real.exp (w 3 + h 3) = Real.exp (w 3) * (1 + h 3 + E2 (h 3)) := exp_split _ _
  have X6 : Real.exp ((p.θ - 1) * (w 1 + h 1)) =
      Real.exp ((p.θ - 1) * w 1) * (1 + (p.θ - 1) * h 1 + E2 ((p.θ - 1) * h 1)) := by
    rw [← exp_split]; ring_nf
  have X7 : Real.exp (-((p.θ - 1) * (xr p w + xr p h))) =
      Real.exp (-((p.θ - 1) * xr p w)) *
        (1 + -((p.θ - 1) * xr p h) + E2 (-((p.θ - 1) * xr p h))) := by
    rw [← exp_split]; ring_nf
  have X8 : Real.exp (aE p * (w 1 + h 1)) =
      Real.exp (aE p * w 1) * (1 + aE p * h 1 + E2 (aE p * h 1)) := by
    rw [← exp_split]; ring_nf
  have X8' : Real.exp (aE p * h 1) = 1 + aE p * h 1 + E2 (aE p * h 1) := by unfold E2; ring
  have X9 : Real.exp (-(aE p * (xr p w + xr p h))) =
      Real.exp (-(aE p * xr p w)) * (1 + -(aE p * xr p h) + E2 (-(aE p * xr p h))) := by
    rw [← exp_split]; ring_nf
  have X10 : Real.exp ((p.θ - 1) * (w 1 + h 1) + (w 2 + h 2)) =
      Real.exp ((p.θ - 1) * w 1 + w 2) *
        (1 + ((p.θ - 1) * h 1 + h 2) + E2 ((p.θ - 1) * h 1 + h 2)) := by
    rw [← exp_split]; ring_nf
  have X11 : Real.exp (aE p * (w 1 + h 1) + (w 3 + h 3)) =
      Real.exp (aE p * w 1 + w 3) * (1 + (aE p * h 1 + h 3) + E2 (aE p * h 1 + h 3)) := by
    rw [← exp_split]; ring_nf
  have XG := Gx_split (1 - p.σ) (w 0) (h 0)
  simp only [Lnode, Uw, R2, Pi.add_apply, hxr]
  rw [X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, XG, X1', X8']
  simp only [ramseyQ, R0, Matrix.cons_val, sub_zero, one_mul, X0, xr]
  field_simp
  ring

/-! ## Welfare and the Lagrangian on an event tree -/

variable {Y : Type*} (T : LagTree Y)

/-- Woodford (2003), §1 and §5 (**welfare of a plan**): `W(r)(x) = S[Uw(r)](x)`, the expected
discounted utility from node `x`. -/
noncomputable def W (p : Par) (A : ℝ) (e : Y → Fin 5 → ℝ) (r : Y → Fin 9 → ℝ) (x : Y) : ℝ :=
  S T p.β (fun y => Uw p A (e y) (r y)) x

/-- Woodford (2003), Ch. 7: the Lagrangian density along a plan `r`, with the multipliers of `w`
and their lags (zero at the roots: the date-0 problem). -/
noncomputable def LN (p : Par) (A : ℝ) (e : Y → Fin 5 → ℝ) (w : Y → Fin 9 → ℝ) (Dm1 : ℝ)
    (r : Y → Fin 9 → ℝ) (y : Y) : ℝ :=
  Lnode p A (e y) (lag0 T (fun z => w z 5) y) (lag0 T (fun z => w z 6) y) (w y)
    (lagDv T Dm1 r y) (r y)

/-- A node function bounded in every coordinate. -/
def VBdd {n : ℕ} (v : Y → Fin n → ℝ) : Prop := ∃ B, ∀ y i, |v y i| ≤ B

omit T in
/-- Coordinates of a bounded vector function are bounded. -/
theorem VBdd.coord {n : ℕ} {v : Y → Fin n → ℝ} (hv : VBdd v) (i : Fin n) :
    Bdd (fun y => v y i) := by
  obtain ⟨B, hB⟩ := hv
  exact ⟨B, fun y => hB y i⟩

omit T in
/-- Constants are bounded. -/
theorem bdd_const (c : ℝ) : Bdd (fun _ : Y => c) := ⟨|c|, fun _ => le_rfl⟩

omit T in
/-- The exponential of a bounded function is bounded. -/
theorem bdd_exp {g : Y → ℝ} (hg : Bdd g) : Bdd (fun y => Real.exp (g y)) := by
  obtain ⟨B, hB⟩ := hg
  refine ⟨Real.exp B, fun y => ?_⟩
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (hB y))

omit T in
/-- `Gx(c, ·)` of a bounded function is bounded. -/
theorem bdd_gx (c : ℝ) {g : Y → ℝ} (hg : Bdd g) : Bdd (fun y => Gx c (g y)) := by
  by_cases hc : c = 0
  · simpa [Gx, hc] using hg
  · have h := (bdd_exp (hg.lin hg c 0)).lin (bdd_const (Y := Y) 1) (1 / c) (-(1 / c))
    refine h.congr fun y => ?_
    simp only [Gx, hc, ↓reduceIte]
    ring_nf

/-- Woodford (2003), Ch. 7 (**regrouping at a root**): for bounded `a, h` and a root `x₀`,
`S[β h·Ma − a·lag h](x₀) = 0`. -/
theorem S_reg_zero {β : ℝ} (hβ : |β| < 1) {a h : Y → ℝ} (ha : Bdd a) (hh : Bdd h) {x : Y}
    (hx : T.depth x = 0) :
    S T β (fun y => β * (h y * T.M a y) - a y * lag0 T h y) x = 0 := by
  have h1 : Bdd (fun y => h y * T.M a y) := hh.mul (ha.M T)
  have h2 : Bdd (fun y => a y * lag0 T h y) := ha.mul (hh.lag T)
  have e : (fun y => β * (h y * T.M a y) - a y * lag0 T h y) =
      fun y => β * (h y * T.M a y) + (-1) * (a y * lag0 T h y) := by funext y; ring
  rw [e, S_lin T hβ h1 h2]
  simp only
  rw [S_lag T hβ ha hh]
  simp only [lag0, hx, ↓reduceIte, mul_zero, zero_add]
  have e2 : (fun z => T.M a z * h z) = fun y => h y * T.M a y := by funext z; ring
  rw [e2]
  ring

omit T in
/-- Woodford (2003), §5: the period utility of a bounded plan is bounded. -/
theorem bdd_Uw (p : Par) (A : ℝ) {e : Y → Fin 5 → ℝ} (he : VBdd e) {r : Y → Fin 9 → ℝ}
    (hr : VBdd r) : Bdd (fun y => Uw p A (e y) (r y)) := by
  have h1 := ((bdd_const (Y := Y) A).mul (bdd_exp ((he.coord 1).lin (he.coord 1) p.σ 0))).mul
    (bdd_gx (1 - p.σ) (hr.coord 0))
  have h2 := ((bdd_const (Y := Y) A).mul (hr.coord 4)).mul
    (bdd_exp ((hr.coord 0).lin (he.coord 3) (1 + p.ω) (-p.ω)))
  refine (h1.lin h2 1 (-(1 / (1 + p.ω)))).congr fun y => ?_
  simp only [Uw]
  ring_nf

/-- Woodford (2003), Ch. 7: the lagged dispersion of a bounded plan is bounded. -/
theorem bdd_lagDv (Dm1 : ℝ) {r : Y → Fin 9 → ℝ} (hr : VBdd r) : Bdd (lagDv T Dm1 r) := by
  obtain ⟨B, hB⟩ := hr
  refine ⟨|Dm1| + |B|, fun y => ?_⟩
  unfold lagDv
  split_ifs
  · have := abs_nonneg B; linarith
  · rename_i hy
    have := (hB (T.par y) 4).trans (le_abs_self B); have := abs_nonneg Dm1; linarith

/-- Woodford (2003), Ch. 7: the Lagrangian density along a bounded plan is bounded. -/
theorem bdd_LN (p : Par) (A : ℝ) {e : Y → Fin 5 → ℝ} (he : VBdd e) {w r : Y → Fin 9 → ℝ}
    (hw : VBdd w) (hr : VBdd r) (Dm1 : ℝ) : Bdd (LN T p A e w Dm1 r) := by
  have c := fun i => hr.coord i
  have cw := fun i => hw.coord i
  have ce := fun i => he.coord i
  have b5 := (cw 5).mul ((bdd_exp (c 2)).lin (bdd_exp (((c 0).lin (ce 1) (1 - p.σ) p.σ).lin
    (ce 2) 1 1)) 1 (-(1 - p.α * p.β)))
  have b6 := (cw 6).mul ((bdd_exp (c 3)).lin (bdd_exp (((c 0).lin (ce 3) (1 + p.ω) (-p.ω)).lin
    (ce 4) 1 1)) 1 (-(1 - p.α * p.β)))
  have hx : Bdd (fun y => xr p (r y)) := ((c 3).lin (c 2) (1 / p.c0) (-(1 / p.c0))).congr
    fun y => by simp only [xr]; ring
  have b7 := (cw 7).mul (((bdd_exp ((c 1).lin (c 1) (p.θ - 1) 0)).lin
    (bdd_const (Y := Y) 1) p.α (-p.α)).lin ((bdd_exp (hx.lin hx (-(p.θ - 1)) 0)).lin
    (bdd_const (Y := Y) 1) (1 - p.α) (-(1 - p.α))) 1 1)
  have b8 := (cw 8).mul (((c 4).lin ((bdd_lagDv T Dm1 hr).mul
    (bdd_exp ((c 1).lin (c 1) (aE p) 0))) 1 (-p.α)).lin
    (bdd_exp (hx.lin hx (-(aE p)) 0)) 1 (-(1 - p.α)))
  have b9 := ((cw 5).lag T).mul (bdd_exp ((c 1).lin (c 2) (p.θ - 1) 1))
  have b10 := ((cw 6).lag T).mul (bdd_exp ((c 1).lin (c 3) (aE p) 1))
  have hU := bdd_Uw p A he hr
  have hs := ((((((hU.lin b5 1 1).lin b6 1 1).lin b7 1 1).lin b8 1 1).lin b9 1 (-p.α)).lin
    b10 1 (-p.α))
  refine hs.congr fun y => ?_
  simp only [LN, Lnode]
  ring_nf

/-- **Woodford (2003), Ch. 7 (welfare is the Lagrangian on the feasible set, date-0 problem).**
For a bounded feasible plan `r`, bounded multipliers `w` and bounded disturbances, at every root
`x₀`: `W(r)(x₀) = S[Lnode(r)](x₀)`. The constraint terms vanish by feasibility and the
expectation terms `βλ_tE_t[⋯]` cancel the lagged-multiplier terms by regrouping
(`S_reg_zero`), the lagged multipliers being zero at the root. -/
theorem welfare_lagrangian (p : Par) (A : ℝ) {e : Y → Fin 5 → ℝ} (he : VBdd e)
    {w r : Y → Fin 9 → ℝ} (hw : VBdd w) (hr : VBdd r) {Dm1 : ℝ} (hF : Feas T p e Dm1 r)
    (hβ : |p.β| < 1) {x : Y} (hx : T.depth x = 0) :
    W T p A e r x = S T p.β (LN T p A e w Dm1 r) x := by
  set g1 : Y → ℝ := fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2) with hg1
  set g2 : Y → ℝ := fun y => Real.exp (aE p * r y 1 + r y 3) with hg2
  have hb1 : Bdd g1 := bdd_exp (((hr.coord 1).lin (hr.coord 2) (p.θ - 1) 1).congr
    fun y => by ring)
  have hb2 : Bdd g2 := bdd_exp (((hr.coord 1).lin (hr.coord 3) (aE p) 1).congr fun y => by ring)
  set D1 : Y → ℝ := fun y => p.β * ((fun z => w z 5) y * T.M g1 y) -
    g1 y * lag0 T (fun z => w z 5) y with hD1
  set D2 : Y → ℝ := fun y => p.β * ((fun z => w z 6) y * T.M g2 y) -
    g2 y * lag0 T (fun z => w z 6) y with hD2
  have hbD1 : Bdd D1 := (((hw.coord 5).mul (hb1.M T)).lin (hb1.mul ((hw.coord 5).lag T)) p.β
    (-1)).congr fun y => by simp only [hD1]; ring
  have hbD2 : Bdd D2 := (((hw.coord 6).mul (hb2.M T)).lin (hb2.mul ((hw.coord 6).lag T)) p.β
    (-1)).congr fun y => by simp only [hD2]; ring
  have hpt : LN T p A e w Dm1 r = fun y => 1 * (fun y => 1 * Uw p A (e y) (r y) + p.α * D1 y) y +
      p.α * D2 y := by
    funext y
    obtain ⟨h5, h6, h7, h8⟩ := hF y
    simp only [LN, Lnode, hD1, hD2, hg1, hg2]
    have e5 : Real.exp (r y 2) - (1 - p.α * p.β) *
        Real.exp ((1 - p.σ) * r y 0 + p.σ * e y 1 + e y 2) =
        p.α * p.β * T.M (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2)) y := by linarith
    have e6 : Real.exp (r y 3) - (1 - p.α * p.β) *
        Real.exp ((1 + p.ω) * r y 0 - p.ω * e y 3 + e y 4) =
        p.α * p.β * T.M (fun y => Real.exp (aE p * r y 1 + r y 3)) y := by linarith
    rw [e5, e6, h7]
    have e8 : r y 4 - p.α * lagDv T Dm1 r y * Real.exp (aE p * r y 1) -
        (1 - p.α) * Real.exp (-(aE p * xr p (r y))) = 0 := h8
    rw [e8]
    ring
  rw [hpt, S_lin T hβ ((bdd_Uw p A he hr).lin hbD1 1 p.α) hbD2]
  simp only
  rw [S_lin T hβ (bdd_Uw p A he hr) hbD1]
  simp only
  rw [hD1, S_reg_zero T hβ hb1 (hw.coord 5) hx, hD2, S_reg_zero T hβ hb2 (hw.coord 6) hx]
  simp only [W]
  ring

/-- **Woodford (2003), Ch. 7 (the first-order terms vanish).** If `w` (bounded, with bounded
disturbances) solves the exact date-0 Ramsey conditions of the efficient-frame economy, then for
every bounded direction `h` and every root `x₀`,
`S[∑ᵢ Qᵢhᵢ − αλ₄e^{aπ}·lag h_Δ](x₀) = 0`, `Qᵢ` the first-order conditions at `w`. -/
theorem foc_kill {p : Par} (A : ℝ) {e : Y → Fin 5 → ℝ} (he : VBdd e) {w : Y → Fin 9 → ℝ}
    (hw : VBdd w) {Dm1 : ℝ} (hR : RamseyL T p (R0 A) e (lagD0 Dm1) w)
    (hβ : |p.β| < 1) (hω : 1 + p.ω ≠ 0) {h : Y → Fin 9 → ℝ} (hh : VBdd h) {x : Y}
    (hx : T.depth x = 0) :
    S T p.β (fun y =>
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 0 * h y 0 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 1 * h y 1 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 2 * h y 2 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 3 * h y 3 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 4 * h y 4 +
      (-(p.α * w y 8 * Real.exp (aE p * w y 1))) * lag0 T (fun z => h z 4) y) x = 0 := by
  -- the conditions at every node
  have hQ : ∀ y, ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
      lag0 T (fun z => w z 6) y, 0, 0] (w y) = ramseyQ p (R0 A) (e y)
        (if T.depth y = 0 then lagD0 Dm1 else w (T.par y)) (w y) := fun y => by
    refine ramseyQ_congr p (R0 A) (e y) (w y) ?_ ?_ ?_ <;>
      by_cases hy : T.depth y = 0 <;> simp [lagDv, lag0, hy, lagD0]
  set P : Y → ℝ := fun y => -(p.α * w y 8 * Real.exp (aE p * w y 1)) with hP
  have hN : ∀ y, Mv T.M (fun z => ramseyN p (w z)) y 4 = p.β * T.M P y := fun y => by
    change T.M (fun z => ramseyN p (w z) 4) y = _
    have e0 : (fun z => ramseyN p (w z) 4) = p.β • P := by
      funext z; simp only [ramseyN, Matrix.cons_val, hP, Pi.smul_apply, smul_eq_mul]; ring
    rw [e0, map_smul]; rfl
  have hN0 : ∀ y (i : Fin 9), i.val < 4 → Mv T.M (fun z => ramseyN p (w z)) y i = 0 :=
    fun y i hi => by
      change T.M (fun z => ramseyN p (w z) i) y = 0
      have e0 : (fun z => ramseyN p (w z) i) = fun _ => (0 : ℝ) := by
        funext z; fin_cases i <;> simp_all [ramseyN]
      rw [e0, M_const T]
  have hc : ∀ y (i : Fin 9), (ramseyQ p (R0 A) (e y)
      (if T.depth y = 0 then lagD0 Dm1 else w (T.par y)) (w y) i) +
        Mv T.M (fun z => ramseyN p (w z)) y i = 0 := fun y i => congrFun (hR y) i
  set Q4 : Y → ℝ := fun y => ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y,
    lag0 T (fun z => w z 5) y, lag0 T (fun z => w z 6) y, 0, 0] (w y) 4 with hQ4
  have hQ4b : Bdd Q4 := by
    have := ((bdd_exp ((hw.coord 0).lin (he.coord 3) (1 + p.ω) (-p.ω))).lin (hw.coord 8)
      (-(A / (1 + p.ω))) 1)
    refine this.congr fun y => ?_
    simp only [hQ4, ramseyQ, Matrix.cons_val, R0]
    field_simp
    ring_nf
  have hPb : Bdd P := ((hw.coord 8).mul (bdd_exp ((hw.coord 1).lin (hw.coord 1) (aE p) 0))).lin
    (bdd_const (Y := Y) 0) (-p.α) 0 |>.congr fun y => by simp only [hP]; ring_nf
  have hfun : (fun y =>
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 0 * h y 0 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 1 * h y 1 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 2 * h y 2 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 3 * h y 3 +
      ramseyQ p (R0 A) (e y) ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
          lag0 T (fun z => w z 6) y, 0, 0] (w y) 4 * h y 4 +
      (-(p.α * w y 8 * Real.exp (aE p * w y 1))) * lag0 T (fun z => h z 4) y) =
      fun y => 1 * (Q4 y * h y 4) + 1 * (P y * lag0 T (fun z => h z 4) y) := by
    funext y
    have z0 := hc y 0
    have z1 := hc y 1
    have z2 := hc y 2
    have z3 := hc y 3
    rw [hN0 y 0 (by decide), add_zero] at z0
    rw [hN0 y 1 (by decide), add_zero] at z1
    rw [hN0 y 2 (by decide), add_zero] at z2
    rw [hN0 y 3 (by decide), add_zero] at z3
    rw [hQ y, z0, z1, z2, z3]
    simp only [hQ4, hP, hQ y]
    ring
  rw [hfun, S_lin T hβ (hQ4b.mul (hh.coord 4)) (hPb.mul ((hh.coord 4).lag T))]
  simp only
  rw [S_lag T hβ hPb (hh.coord 4)]
  simp only [lag0, hx, ↓reduceIte, mul_zero, zero_add, one_mul]
  have hz : (fun y => Q4 y * h y 4) = fun y => -(p.β * (T.M P y * h y 4)) := by
    funext y
    have z4 := hc y 4
    rw [← hQ y, hN y] at z4
    simp only [hQ4]
    linear_combination (h y 4) * z4
  rw [hz]
  have hb : Bdd (fun y => T.M P y * h y 4) := (hPb.M T).mul (hh.coord 4)
  have e1 := S_lin T hβ hb hb (-p.β) 0
  have e2 : (fun y => -p.β * (T.M P y * h y 4) + 0 * (T.M P y * h y 4)) =
      fun y => -(p.β * (T.M P y * h y 4)) := by funext y; ring
  rw [e2] at e1
  rw [e1]
  simp only
  ring

omit T in
/-- Woodford (2003), §5: every component of the exact Ramsey conditions is continuous in the
disturbances, the lag and the current values. -/
theorem continuous_ramseyQ (p : Par) (R : RPar) (i : Fin 9) :
    Continuous (fun q : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
      ramseyQ p R q.1 q.2.1 q.2.2 i) := by
  fin_cases i <;> simp only [ramseyQ, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop

omit T in
/-- A continuous function of bounded node data is bounded. -/
theorem bdd_of_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : E → ℝ} (hF : Continuous F) {g : Y → E} {B : ℝ} (hg : ∀ y, ‖g y‖ ≤ B) :
    Bdd (fun y => F (g y)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) B).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun y => by
    have := hC (g y) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hg y)
    rwa [Real.norm_eq_abs] at this⟩

omit T in
/-- The sup norm of a coordinatewise bounded vector. -/
theorem norm_le_of_vbdd {n : ℕ} {v : Y → Fin n → ℝ} {B : ℝ} (hB : ∀ y i, |v y i| ≤ B) (y : Y) :
    ‖v y‖ ≤ |B| :=
  (pi_norm_le_iff_of_nonneg (abs_nonneg B)).2 fun i => by
    rw [Real.norm_eq_abs]; exact (hB y i).trans (le_abs_self B)

/-- **Woodford (2003), Ch. 6, §5 and Ch. 7 (the welfare difference is EXACTLY the discounted
second-order remainder).** If `w` (bounded) solves the exact date-0 Ramsey conditions of the
efficient-frame economy with bounded disturbances, then for every bounded feasible plan `r` and
every root `x₀`, `W(r)(x₀) − W(w)(x₀) = S[R2](x₀)`, with the node remainder `R2` at `w` in the
direction `r − w` (lagged dispersion difference `lag(r_Δ − w_Δ)`). -/
theorem welfare_diff {p : Par} (hp : p.Std) (A : ℝ) {e : Y → Fin 5 → ℝ} (he : VBdd e)
    {w r : Y → Fin 9 → ℝ} (hw : VBdd w) (hr : VBdd r) {Dm1 : ℝ}
    (hR : RamseyL T p (R0 A) e (lagD0 Dm1) w) (hF : Feas T p e Dm1 r) {x : Y}
    (hx : T.depth x = 0) :
    W T p A e r x - W T p A e w x = S T p.β (fun y => R2 p A (e y) (lag0 T (fun z => w z 5) y)
      (lag0 T (fun z => w z 6) y) (w y) (lagDv T Dm1 w y) (r y - w y)
      (lag0 T (fun z => r z 4 - w z 4) y)) x := by
  have hβ : |p.β| < 1 := by rw [abs_of_pos hp.β_pos]; exact hp.β_lt_one
  have hω : 1 + p.ω ≠ 0 := by linarith [hp.ω_nonneg]
  have hFw : Feas T p e Dm1 w := by
    have := feas_of_ramsey T p (R0 A) e (lagD0 Dm1) w hR
    simpa [lagD0] using this
  set h : Y → Fin 9 → ℝ := fun y => r y - w y with hh
  have hhb : VBdd h := by
    obtain ⟨B1, hB1⟩ := hr
    obtain ⟨B2, hB2⟩ := hw
    exact ⟨B1 + B2, fun y i => (abs_sub _ _).trans (add_le_add (hB1 y i) (hB2 y i))⟩
  set wm : Y → Fin 9 → ℝ := fun y => ![0, 0, 0, 0, lagDv T Dm1 w y, lag0 T (fun z => w z 5) y,
    lag0 T (fun z => w z 6) y, 0, 0] with hwm
  have hwmb : VBdd wm := by
    obtain ⟨B1, hB1⟩ := bdd_lagDv T Dm1 hw
    obtain ⟨B2, hB2⟩ := (hw.coord 5).lag T
    obtain ⟨B3, hB3⟩ := (hw.coord 6).lag T
    refine ⟨|B1| + |B2| + |B3|, fun y i => ?_⟩
    have a1 := (hB1 y).trans (le_abs_self B1)
    have a2 := (hB2 y).trans (le_abs_self B2)
    have a3 := (hB3 y).trans (le_abs_self B3)
    have := abs_nonneg B1; have := abs_nonneg B2; have := abs_nonneg B3
    fin_cases i <;> simp [hwm] <;> linarith
  obtain ⟨Be, hBe⟩ := he
  obtain ⟨Bm, hBm⟩ := hwmb
  obtain ⟨Bw, hBw⟩ := hw
  have hQb : ∀ i, Bdd (fun y => ramseyQ p (R0 A) (e y) (wm y) (w y) i) := fun i =>
    bdd_of_cont (continuous_ramseyQ p (R0 A) i) (g := fun y => (e y, wm y, w y))
      (B := |Be| + |Bm| + |Bw|) fun y => by
        rw [Prod.norm_def, Prod.norm_def]
        have := norm_le_of_vbdd hBe y; have := norm_le_of_vbdd hBm y
        have := norm_le_of_vbdd hBw y
        have := abs_nonneg Be; have := abs_nonneg Bm; have := abs_nonneg Bw
        exact max_le (by linarith) (max_le (by linarith) (by linarith))
  have hwb : VBdd w := ⟨Bw, hBw⟩
  have heb : VBdd e := ⟨Be, hBe⟩
  have hPb : Bdd (fun y => -(p.α * w y 8 * Real.exp (aE p * w y 1))) :=
    ((hwb.coord 8).mul (bdd_exp ((hwb.coord 1).lin (hwb.coord 1) (aE p) 0))).lin
      (bdd_const (Y := Y) 0) (-p.α) 0 |>.congr fun y => by ring_nf
  set Lf : Y → ℝ := fun y =>
    ramseyQ p (R0 A) (e y) (wm y) (w y) 0 * h y 0 + ramseyQ p (R0 A) (e y) (wm y) (w y) 1 * h y 1 +
      ramseyQ p (R0 A) (e y) (wm y) (w y) 2 * h y 2 +
      ramseyQ p (R0 A) (e y) (wm y) (w y) 3 * h y 3 +
      ramseyQ p (R0 A) (e y) (wm y) (w y) 4 * h y 4 +
      (-(p.α * w y 8 * Real.exp (aE p * w y 1))) * lag0 T (fun z => h z 4) y with hLf
  have hLb : Bdd Lf := by
    have t := fun i => (hQb i).mul (hhb.coord i)
    refine (((((t 0).lin (t 1) 1 1).lin (t 2) 1 1).lin (t 3) 1 1).lin (t 4) 1 1 |>.lin
      (hPb.mul ((hhb.coord 4).lag T)) 1 1).congr fun y => ?_
    simp only [hLf]
    ring
  have hL0 : S T p.β Lf x = 0 := foc_kill T A heb hwb hR hβ hω hhb hx
  have hpt : ∀ y, LN T p A e w Dm1 r y - LN T p A e w Dm1 w y = Lf y +
      R2 p A (e y) (lag0 T (fun z => w z 5) y) (lag0 T (fun z => w z 6) y) (w y)
        (lagDv T Dm1 w y) (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y) := by
    intro y
    have hl : lag0 T (fun z => r z 4 - w z 4) y = lagDv T Dm1 r y - lagDv T Dm1 w y := by
      simp only [lag0, lagDv]; split_ifs <;> ring
    have e1 : r y = w y + h y := by funext i; simp [hh]
    have e2 : lagDv T Dm1 r y = lagDv T Dm1 w y + lag0 T (fun z => r z 4 - w z 4) y := by
      rw [hl]; ring
    have key := lnode_expand hω A (e y) (lag0 T (fun z => w z 5) y)
      (lag0 T (fun z => w z 6) y) (w y) (lagDv T Dm1 w y) (h y)
      (lag0 T (fun z => r z 4 - w z 4) y)
    simp only [LN]
    rw [e2]
    conv_lhs => rw [e1]
    rw [key]
    simp only [hLf, hwm, hh]
    have e3 : (fun z => h z 4) = fun z => r z 4 - w z 4 := by funext z; simp [hh]
    rw [e3]
  have hbr := bdd_LN T p A heb hwb hr Dm1
  have hbw := bdd_LN T p A heb hwb hwb Dm1
  have hR2b : Bdd (fun y => R2 p A (e y) (lag0 T (fun z => w z 5) y) (lag0 T (fun z => w z 6) y)
      (w y) (lagDv T Dm1 w y) (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y)) :=
    ((hbr.lin hbw 1 (-1)).lin hLb 1 (-1)).congr fun y => by linear_combination hpt y
  rw [welfare_lagrangian T p A heb hwb hr hF hβ hx, welfare_lagrangian T p A heb hwb hwb hFw hβ hx]
  have e1 := congrFun (S_lin T hβ hbr hbw 1 (-1)) x
  have e2 := congrFun (S_lin T hβ hLb hR2b 1 1) x
  have e3 : (fun y => 1 * LN T p A e w Dm1 r y + -1 * LN T p A e w Dm1 w y) =
      fun y => 1 * Lf y + 1 * R2 p A (e y) (lag0 T (fun z => w z 5) y)
        (lag0 T (fun z => w z 6) y) (w y) (lagDv T Dm1 w y) (r y - w y)
        (lag0 T (fun z => r z 4 - w z 4) y) := by
    funext y; linear_combination hpt y
  rw [e3, e2] at e1
  rw [hL0] at e1
  linarith

end Woodford.StabilizationWelfare.TidyR6aLagr

