/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyTree

/-!
# The linearised Ramsey system with disturbances: the Benigno–Woodford target and cost push

Woodford (2003), *Interest and Prices*, Chapter 6, §5, eqs. (5.6)–(5.11), pp. 458–461
(Benigno–Woodford: the welfare-relevant target `Ŷ*`, the cost-push term `u`), Chapter 7, §1
(the optimal commitment `π_t + (λ_x/κ)(x_t − x_{t−1}) = 0`) and §5.1, footnote 71.

NonlinearNKMarkovRamseyLin linearised the exact Ramsey conditions in the lagged, current and
expected variables (`DQr`, `DNr`) but not in the disturbances. Here the derivative in the
disturbances `e = (·, ĉ, τ̂, q, μ̂ʷ)` is computed (`DQs`, `fderiv_Qd_full`), and the linear
system with disturbances is reduced, for EVERY distortion `Φ` (with `s_C = 1`, as in the Ramsey
model), to the two relations of the linear-quadratic problem of §5:

* **`shock_pc`**: the aggregate-supply relation `π = κ(ŷ − Ŷⁿ) + βE π′`, with Woodford's natural
  rate `Ŷⁿ = LargeDistortions.YnA` (`G = 0`, `s_C = 1`);
* **`DQs0_eq`**: the disturbance part of the output condition is `A_uG Ŷ*` with exactly the
  Benigno–Woodford target `Ŷ* = LargeDistortions.YstarA` of (5.8) (generalised for a revenue
  wedge), `G = σ + ω + Φ(1 − σ) = Mden` (`Mden_one`);
* **`first_order_tree`**: on every event tree, a bounded solution of the linear system
  `L v = −DQs(ê)` (zero initial lag) has `Δ̂ = 0`, `λ̂₁ + λ̂₂ = 0`, satisfies the AS relation
  with the natural rate, and the targeting rule
  `(ŷ − Ŷ*) − (ŷ − Ŷ*)₋ + θπ = 0` with zero initial gap: the footnote-71 commitment with
  `φ = 1/θ`;
* **`lamTilde_one`**: `λ̃ = κ/θ` at `s_C = 1` for every `Φ` (so `φ = λ̃/κ = 1/θ`: the weight of
  the linearised Ramsey conditions, `NonlinearNKMarkovRamseyLin.key_theta`, IS the
  Benigno–Woodford weight (5.7)); **`costPush_one`**: the cost-push term is `κ(Ŷ* − Ŷⁿ)`
  (`LargeDistortions.costPush511`).
-/

namespace Woodford.StabilizationWelfare.TidyR6aShock

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree

/-! ## The derivative in the disturbances -/

/-- Woodford (2003), §5 (**the linearised conditions in the disturbances**) at the steady state:
the derivative of the current part of the exact Ramsey conditions in the direction `e` of the
disturbances `(·, ĉ, τ̂, q, μ̂ʷ)` (`s = 1 − αβ`, `L = ramseyLam`). -/
noncomputable def DQs (p : Par) (R : RPar) (e : Fin 5 → ℝ) : Fin 9 → ℝ :=
  let s := 1 - p.α * p.β
  let L := ramseyLam p R
  ![R.Au * p.σ * e 1 + (1 - R.Φ) * R.Au * p.ω * e 3
      - s * (1 - p.σ) * L 0 * (p.σ * e 1 + e 2) - s * (1 + p.ω) * L 1 * (-(p.ω * e 3) + e 4),
    0, 0, 0, (1 - R.Φ) * R.Au * p.ω * e 3 / (1 + p.ω),
    -(s * (p.σ * e 1 + e 2)), -(s * (-(p.ω * e 3) + e 4)), 0, 0]

/-- Woodford (2003), §5: the components of the current part that do not involve the
disturbances (`∂π`, `∂F̂`, `∂K̂`, price index, dispersion) vanish along `t ↦ (t·e, 0, 0)`. -/
theorem const_case {p : Par} (R : RPar) (hp : p.Std) (e : Fin 5 → ℝ) (i : Fin 9)
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 7 ∨ i = 8) (hD : DQs p R e i = 0) :
    HasDerivAt (fun t : ℝ => Qd p R (t • e, 0, 0) i) (DQs p R e i) 0 := by
  have hss := congrFun (Qd_Nd_zero R hp) i
  have hN : Nd p R 0 i = 0 := by
    rcases hi with h | h | h | h | h <;> subst h <;> simp [Nd, ramseyN]
  have hz : ∀ t : ℝ, Qd p R (t • e, 0, 0) i = Qd p R (0, 0, 0) i := fun t => by
    rcases hi with h | h | h | h | h <;> subst h <;> simp [Qd, ramseyQ]
  rw [hD]
  refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => ?_)
  change Qd p R (t • e, 0, 0) i = 0
  rw [hz t]
  simp only [Pi.add_apply, Pi.zero_apply, hN, add_zero] at hss
  exact hss

/-- Woodford (2003), §5: the derivative of the current part along `t ↦ (t·e, 0, 0)` at the
steady state is `DQs e`. -/
theorem hasDerivAt_Qd_shock {p : Par} (R : RPar) (hp : p.Std) (e : Fin 5 → ℝ) (i : Fin 9) :
    HasDerivAt (fun t : ℝ => Qd p R (t • e, 0, 0) i) (DQs p R e i) 0 := by
  have hω : 1 + p.ω ≠ 0 := by linarith [hp.ω_nonneg]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := ((((hd3 1 0 1 0 (p.σ * e 1)).const_mul R.Au).sub
      ((hd3 1 0 1 0 (-(p.ω * e 3))).const_mul ((1 - R.Φ) * R.Au))).sub
      ((hd3 1 0 1 0 (p.σ * e 1 + e 2)).const_mul
        (ramseyLam p R 0 * (1 - p.α * p.β) * (1 - p.σ)))).sub
      ((hd3 1 0 1 0 (-(p.ω * e 3) + e 4)).const_mul
        (ramseyLam p R 1 * (1 - p.α * p.β) * (1 + p.ω)))
    refine (h.congr_deriv (by simp only [DQs, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, add_zero, mul_zero]
    simp only [Pi.sub_apply]
    ring_nf
  · exact const_case R hp e 1 (by decide) (by simp [DQs])
  · exact const_case R hp e 2 (by decide) (by simp [DQs])
  · exact const_case R hp e 3 (by decide) (by simp [DQs])
  · have h := ((hd3 1 0 1 0 (-(p.ω * e 3))).const_mul
      (-((1 - R.Φ) * R.Au / (1 + p.ω)))).add_const (ramseyLam p R 3)
    refine (h.congr_deriv (by simp only [DQs, Matrix.cons_val]; field_simp; ring))
      |>.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, add_zero, mul_zero]
    ring_nf
  · have h := ((hd3 1 0 1 0 (p.σ * e 1 + e 2)).const_mul (-(1 - p.α * p.β))).const_add 1
    refine (h.congr_deriv (by simp only [DQs, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, add_zero, mul_zero, Real.exp_zero]
    ring_nf
  · have h := ((hd3 1 0 1 0 (-(p.ω * e 3) + e 4)).const_mul (-(1 - p.α * p.β))).const_add 1
    refine (h.congr_deriv (by simp only [DQs, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, add_zero, mul_zero, Real.exp_zero]
    ring_nf
  · exact const_case R hp e 7 (by decide) (by simp [DQs])
  · exact const_case R hp e 8 (by decide) (by simp [DQs])

/-- Woodford (2003), §5 (**the full linearisation**): the derivative of the current part at the
steady state in the direction `(e, um, u)` is `DQs e + DQr um u`. -/
theorem fderiv_Qd_full {p : Par} (R : RPar) (hp : p.Std) (e : Fin 5 → ℝ) (um u : Fin 9 → ℝ) :
    fderiv ℝ (Qd p R) 0 (e, um, u) = DQs p R e + DQr p R um u := by
  have hd : HasFDerivAt (Qd p R) (fderiv ℝ (Qd p R) 0) 0 :=
    ((contDiff_Qd (n := 1) p R).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => (t • e, (0 : Fin 9 → ℝ), (0 : Fin 9 → ℝ)))
      (e, (0 : Fin 9 → ℝ), (0 : Fin 9 → ℝ)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).prodMk
      ((hasDerivAt_const (0 : ℝ) (0 : Fin 9 → ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : Fin 9 → ℝ)))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp; rfl)
  have he : fderiv ℝ (Qd p R) 0 (e, 0, 0) = DQs p R e :=
    hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Qd_shock R hp e i)
  have hs : ((e, um, u) : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)) = (e, 0, 0) + (0, um, u) := by
    simp
  rw [hs, map_add, he, fderiv_Qd R hp]

/-! ## The natural rate, the target and the cost push at `s_C = 1` -/

/-- Woodford (2003), (5.4) at `s_C = 1`, `G = 0`: the natural rate
`Ŷⁿ = (ωq + σ⁻¹ĉ − μ̂ʷ + τ̂)/(ω + σ⁻¹)` of the disturbances `e = (·, ĉ, τ̂, q, μ̂ʷ)`. -/
noncomputable def Yn1 (p : Par) (e : Fin 5 → ℝ) : ℝ :=
  LargeDistortions.YnA p.ω p.σ 1 0 (e 1) (e 3) (e 4) (e 2)

/-- Woodford (2003), (5.8) at `s_C = 1`, `G = 0`: the Benigno–Woodford target `Ŷ*`. -/
noncomputable def Ys1 (p : Par) (R : RPar) (e : Fin 5 → ℝ) : ℝ :=
  LargeDistortions.YstarA p.α p.β p.θ p.ω p.σ 1 R.Φ 0 (e 1) (e 3) (e 4) (e 2)

/-- Woodford (2003), (5.11) at `s_C = 1`, `G = 0`: the cost-push term `κ(Ŷ* − Ŷⁿ)`. -/
noncomputable def u1 (p : Par) (R : RPar) (e : Fin 5 → ℝ) : ℝ :=
  LargeDistortions.costPush511 p.α p.β p.θ p.ω p.σ 1 R.Φ 0 (e 1) (e 3) (e 4) (e 2)

/-- Woodford (2003), (5.11): the cost-push term is `κ(Ŷ* − Ŷⁿ)`. -/
theorem costPush_one (p : Par) (R : RPar) (e : Fin 5 → ℝ) :
    u1 p R e = p.κ * (Ys1 p R e - Yn1 p e) := rfl

/-- Woodford (2003), p. 459: at `s_C = 1` the denominator `M` of `ω₂, ω₃` is
`G = σ + ω + Φ(1 − σ)`, the weight of the linearised targeting rule. -/
theorem Mden_one (p : Par) (R : RPar) : LargeDistortions.Mden p.ω p.σ 1 R.Φ = Gw p R := by
  unfold LargeDistortions.Mden Gw
  ring

/-- Woodford (2003), (5.7) at `s_C = 1` (**`λ̃ = κ/θ` for every distortion**): the
Benigno–Woodford weight equals the weight `λ_x = κ/θ` of the linearised Ramsey conditions
(`NonlinearNKMarkovRamseyLin.key_theta`), so the footnote-71 rule has `φ = λ̃/κ = 1/θ`. -/
theorem lamTilde_one (p : Par) (R : RPar) (hp : p.Std) :
    LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 R.Φ = p.κ / p.θ ∧
      LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 R.Φ / p.κ = 1 / p.θ := by
  have hκ := hp.κ_pos.ne'
  have h1 : LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 R.Φ = p.κ / p.θ := by
    unfold LargeDistortions.lamTilde
    simp only [div_one, sub_self, mul_zero, zero_div, zero_mul, sub_zero, mul_one]
    rfl
  refine ⟨h1, ?_⟩
  rw [h1]
  field_simp

/-- Woodford (2003), §5 and (5.8) (**the disturbance part of the output condition is
`A_uG Ŷ*`**): with `G = σ + ω + Φ(1 − σ) ≠ 0`, `DQs₀(e) = A_uG Ŷ*(e)`, `Ŷ*` exactly the
Benigno–Woodford target. -/
theorem DQs0_eq {p : Par} (R : RPar) (hp : p.Std) (hGw : Gw p R ≠ 0) (e : Fin 5 → ℝ) :
    DQs p R e 0 = R.Au * Gw p R * Ys1 p R e := by
  have hκ := hp.κ_pos.ne'
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hσω : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hl : LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 R.Φ = p.κ / p.θ :=
    (lamTilde_one p R hp).1
  have hM := Mden_one p R
  have h1 : LargeDistortions.omega1 p.α p.β p.θ p.ω p.σ 1 R.Φ = 1 := by
    unfold LargeDistortions.omega1
    rw [hl]
    change p.κ / (p.κ / p.θ * p.θ) = 1
    field_simp
  have h3 : LargeDistortions.omega3 p.ω p.σ 1 R.Φ = (1 - R.Φ) / Gw p R := by
    rw [LargeDistortions.omega3_eq, hM]
  unfold Ys1 LargeDistortions.YstarA
  rw [h1, h3, hM]
  simp only [DQs, Matrix.cons_val_zero, ramseyLam, Matrix.cons_val_one, LargeDistortions.YnA]
  unfold Gw at hGw ⊢
  field_simp
  ring

/-! ## Reduction of the linear system with disturbances -/

/-- Woodford (2003), (5.4) linearised at `s_C = 1` (**the AS relation with the natural rate**):
if the linear conditions hold with the disturbance forcing, `DQr vm v + DNr vn = −DQs e`, and
the expected price-index residual vanishes, then `π = κ(ŷ − Ŷⁿ) + βE π′`. -/
theorem shock_pc {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) (e : Fin 5 → ℝ)
    (h : DQr p R vm v + DNr p R vn = -DQs p R e)
    (h7n : p.α * (p.θ - 1) * vn 1 - (1 - p.α) * (p.θ - 1) * ((vn 3 - vn 2) / p.c0) = 0) :
    v 1 = p.κ * (v 0 - Yn1 p e) + p.β * vn 1 := by
  have hpc := red_pc R hp vm v vn
  rw [h, h7n] at hpc
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  rw [hpc]
  simp only [Pi.neg_apply, DQs, Matrix.cons_val, Yn1, LargeDistortions.YnA, Par.κ,
    Moments.calvoKappa]
  unfold Par.c0
  field_simp
  ring

/-- Woodford (2003), §5 (**the output condition with disturbances**): `s(σ+ω)λ̂₁ = A_uG(ŷ − Ŷ*)
+ A_vΔ̂ + s(1+ω)μ` with `μ = λ̂₁ + λ̂₂`, `s = 1 − αβ`. -/
theorem shock_l1 {p : Par} (R : RPar) (hp : p.Std) (hGw : Gw p R ≠ 0) (vm v vn : Fin 9 → ℝ)
    (e : Fin 5 → ℝ) (h : DQr p R vm v + DNr p R vn = -DQs p R e) :
    (1 - p.α * p.β) * (p.σ + p.ω) * v 5 = R.Au * Gw p R * (v 0 - Ys1 p R e) +
      (1 - R.Φ) * R.Au * v 4 + (1 - p.α * p.β) * (1 + p.ω) * (v 5 + v 6) := by
  have h0 := red_l1 R hp vm v vn
  rw [h] at h0
  simp only [Pi.neg_apply] at h0
  rw [DQs0_eq R hp hGw] at h0
  linarith

/-- Woodford (2003), Ch. 7, (1.17) (**the multiplier recursion with disturbances**): when the
lagged and current predetermined blocks vanish, `s(σ+ω)(λ̂₁ − λ̂₁₋) = −A_uGθπ`. -/
theorem shock_l1_lag {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) (e : Fin 5 → ℝ)
    (h : DQr p R vm v + DNr p R vn = -DQs p R e) (hm4 : vm 4 = 0) (hm56 : vm 5 + vm 6 = 0) :
    (1 - p.α * p.β) * (p.σ + p.ω) * (v 5 - vm 5) = -(R.Au * Gw p R * p.θ * v 1) := by
  have hl := red_l1_lag R hp vm v vn
  rw [h] at hl
  simp only [Pi.neg_apply, DQs, Matrix.cons_val, neg_zero, mul_zero, sub_zero, hm4, hm56,
    add_zero] at hl
  have key := key_theta R hp
  rw [hl]
  linear_combination (-(v 1)) * key

/-! ## The first-order system on an event tree -/

variable {X : Type*} (T : LagTree X)

/-- **Woodford (2003), §5, (5.4)–(5.11), Ch. 7, (1.17), and footnote 71 (the linearised Ramsey
system with disturbances IS the linear-quadratic commitment problem, for every `Φ`).** On every
event tree, if `v` solves the linear system `L v = −DQs(ê)` with zero initial lag
(`ê` the disturbance pattern, `A_uG ≠ 0`, `G ≠ 0`), then:
* `Δ̂ = 0` and `λ̂₁ + λ̂₂ = 0` at every node;
* the AS relation `π = κ(ŷ − Ŷⁿ(ê)) + βE π′` holds at every node;
* the targeting rule `x − lag x + θπ = 0` holds with the gap `x = ŷ − Ŷ*(ê)` and zero initial
  gap (`lag0`), i.e. `π = −(1/θ)(x − x₋)`, the footnote-71 rule with `φ = λ̃/κ = 1/θ`;
* `s(σ+ω)λ̂₁ = A_uG x`. -/
theorem first_order_tree {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    (ê : X → Fin 5 → ℝ) (v : X → Fin 9 → ℝ)
    (hL : LR T p R v = fun y => -DQs p R (ê y)) :
    (∀ y, v y 4 = 0) ∧ (∀ y, v y 5 + v y 6 = 0) ∧
      (∀ y, v y 1 = p.κ * (v y 0 - Yn1 p (ê y)) + p.β * T.M (fun y' => v y' 1) y) ∧
      (∀ y, (v y 0 - Ys1 p R (ê y)) - lag0 T (fun y' => v y' 0 - Ys1 p R (ê y')) y +
        p.θ * v y 1 = 0) ∧
      ∀ y, (1 - p.α * p.β) * (p.σ + p.ω) * v y 5 = R.Au * Gw p R * (v y 0 - Ys1 p R (ê y)) := by
  have hGw : Gw p R ≠ 0 := fun h => hG (by rw [h, mul_zero])
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hσω : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hR : ∀ y, DQr p R (lagv T v y) (v y) + DNr p R (Mv T.M v y) = -DQs p R (ê y) :=
    fun y => congrFun hL y
  -- the dispersion block
  have hD : ∀ y, v y 4 = 0 := by
    have hrec : ∀ y, v y 4 = p.α * lag0 T (fun y' => v y' 4) y := fun y => by
      have h := red_D R hp (lagv T v y) (v y) (Mv T.M v y)
      rw [hR y] at h
      simpa [DQs, lagv] using h
    exact fun y => zero_of_eq_lag T hrec y
  -- the summed multiplier
  have hμ : ∀ y, v y 5 + v y 6 = 0 := by
    have hrec : ∀ y, v y 5 + v y 6 = p.α * lag0 T (fun y' => v y' 5 + v y' 6) y := fun y => by
      have h := red_mu R hp (lagv T v y) (v y) (Mv T.M v y)
      rw [hR y] at h
      have e : lag0 T (fun y' => v y' 5 + v y' 6) y = lagv T v y 5 + lagv T v y 6 := by
        have := lag0_lin T 1 1 (fun y' => v y' 5) (fun y' => v y' 6) y
        simp only [one_mul] at this
        rw [this]; rfl
      rw [e]
      simpa [DQs] using h
    exact fun y => zero_of_eq_lag T hrec y
  -- the price index holds at every node
  have h7 : ∀ y, p.α * (p.θ - 1) * v y 1 - (1 - p.α) * (p.θ - 1) * ((v y 3 - v y 2) / p.c0) =
      0 := fun y => by
    have h := red_x (p := p) R (lagv T v y) (v y) (Mv T.M v y)
    rw [hR y] at h
    simp only [Pi.neg_apply, DQs, Matrix.cons_val, neg_zero] at h
    linarith
  have h7n : ∀ y, p.α * (p.θ - 1) * Mv T.M v y 1 -
      (1 - p.α) * (p.θ - 1) * ((Mv T.M v y 3 - Mv T.M v y 2) / p.c0) = 0 := fun y => by
    have hz : (fun y' => p.α * (p.θ - 1) * v y' 1 -
        (1 - p.α) * (p.θ - 1) * ((v y' 3 - v y' 2) / p.c0)) = fun _ => 0 := funext h7
    have e : (fun y' => p.α * (p.θ - 1) * v y' 1 -
        (1 - p.α) * (p.θ - 1) * ((v y' 3 - v y' 2) / p.c0)) =
        (p.α * (p.θ - 1)) • (fun y' => v y' 1) -
          ((1 - p.α) * (p.θ - 1) / p.c0) • ((fun y' => v y' 3) - fun y' => v y' 2) := by
      funext y'; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hM := congrArg (fun f => T.M f y) hz
    rw [e, map_sub, map_smul, map_smul, map_sub, M_const T 0] at hM
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hM
    change p.α * (p.θ - 1) * T.M (fun y' => v y' 1) y - (1 - p.α) * (p.θ - 1) *
      ((T.M (fun y' => v y' 3) y - T.M (fun y' => v y' 2) y) / p.c0) = 0
    rw [← hM]
    ring
  refine ⟨hD, hμ, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · have h := shock_pc R hp (lagv T v y) (v y) (Mv T.M v y) (ê y) (hR y) (h7n y)
    rw [h]; rfl
  · have hl1 : ∀ y, (1 - p.α * p.β) * (p.σ + p.ω) * v y 5 =
        R.Au * Gw p R * (v y 0 - Ys1 p R (ê y)) := fun y => by
      have h := shock_l1 R hp hGw (lagv T v y) (v y) (Mv T.M v y) (ê y) (hR y)
      rw [hD y, hμ y] at h
      linarith
    have hm4 : lagv T v y 4 = 0 := by
      simp only [lagv, lag0]; split_ifs
      · rfl
      · exact hD _
    have hm56 : lagv T v y 5 + lagv T v y 6 = 0 := by
      simp only [lagv, lag0]; split_ifs
      · simp
      · exact hμ _
    have hlag := shock_l1_lag R hp (lagv T v y) (v y) (Mv T.M v y) (ê y) (hR y) hm4 hm56
    have hlag5 : (1 - p.α * p.β) * (p.σ + p.ω) * lagv T v y 5 =
        R.Au * Gw p R * lag0 T (fun y' => v y' 0 - Ys1 p R (ê y')) y := by
      simp only [lagv, lag0]; split_ifs
      · simp
      · exact hl1 _
    have key : R.Au * Gw p R * ((v y 0 - Ys1 p R (ê y)) -
        lag0 T (fun y' => v y' 0 - Ys1 p R (ê y')) y + p.θ * v y 1) = 0 := by
      linear_combination -(hl1 y) + hlag5 + hlag
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h hG
    · exact h
  · have h := shock_l1 R hp hGw (lagv T v y) (v y) (Mv T.M v y) (ê y) (hR y)
    rw [hD y, hμ y] at h
    linarith

end Woodford.StabilizationWelfare.TidyR6aShock
