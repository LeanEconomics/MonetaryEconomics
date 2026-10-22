/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyRootsInv

/-!
# The linearised Rotemberg Ramsey operator when `G = 0`

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2, and Appendix A.3. When
`G = 1 + ω − m(1 − σ) = 0` the combined consumption–output condition pins the multiplier
statically, `θm(σ+ω)λ̂ = κ_4 r_4 − r_0 − r_2` (no recursion), inflation follows from the inflation
condition, output from the NKPC and `γ̂` from the consumption condition. The inverse `LinvZ` is
explicit and bounded on every event tree.

* **`LR_LinvZ`**, **`LR_injZ`**, **`LinvZ_bound`**: right inverse (for every forcing),
  injectivity (for every process, bounded or not), and a uniform bound.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyZeroInv

open NonlinearNKMarkov (Mv IsMarkov)
open NonlinearNKMarkovRamseyTree (LagTree lag0 M_lag0 abs_lag0_le M_lin M_const lagv lb2 lbM
  lbLag lag0_zero)
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyTree (LR cR4)
open NonlinearRotembergRamseyAE (gamb_pos)

variable {p : Par} {X : Type*} (T : LagTree X)

/-- Woodford (2003), Ch. 7 with `G = 0`: the multiplier, `(κ₄r₄ − r₀ − r₂)/(θm(σ+ω))`. -/
noncomputable def lz (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (cR4 p * r x 4 - r x 0 - r x 2) / (p.θ * p.m * (p.σ + p.ω))

/-- Woodford (2003), Ch. 7 with `G = 0`: inflation from the inflation condition. -/
noncomputable def pz (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (lz p r x - lag0 T (lz p r) x) / gamb p - r x 1 / (gamb p * p.ψ)

/-- Woodford (2003), Ch. 7 with `G = 0`: output from the NKPC. -/
noncomputable def yz (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (p.ψ * pz T p r x - p.β * p.ψ * T.M (pz T p r) x - r x 3 + p.θ * p.m * p.σ * r x 4) /
    (p.θ * p.m * (p.σ + p.ω))

/-- Woodford (2003), Ch. 7 with `G = 0`: consumption from the resource constraint. -/
noncomputable def cz (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ := yz T p r x - r x 4

/-- Woodford (2003), Ch. 7 with `G = 0`: the resource multiplier. -/
noncomputable def gz (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (1 - p.σ) * cz T p r x - lz p r x * (p.θ * p.m * p.σ) -
    lamb p * (p.θ * p.m * p.σ * (yz T p r x - p.σ * cz T p r x)) - gamb p * cz T p r x - r x 2

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse when `G = 0`**). -/
noncomputable def LinvZ (p : Par) (r : X → Fin 5 → ℝ) (x : X) : Fin 5 → ℝ :=
  ![yz T p r x, pz T p r x, cz T p r x, lz p r x, gz T p r x]

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r` when `G = 0`**), for every forcing. -/
theorem LR_LinvZ (hp : p.Basic) (hG : Gw p = 0) (r : X → Fin 5 → ℝ) :
    LR T p (LinvZ T p r) = r := by
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hK : p.θ * p.m * (p.σ + p.ω) ≠ 0 := by positivity
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm0 : p.m ≠ 0 := hp.m_pos.ne'
  have hs0 : p.σ + p.ω ≠ 0 := hs.ne'
  set v := LinvZ T p r
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  have f1 : (fun z => v z 1) = pz T p r := rfl
  have f3 : (fun z => v z 3) = lz p r := rfl
  funext x i
  fin_cases i
  · have h02 := red_lam hp (lagv T v x) (v x)
    have hc2 : DQr p (lagv T v x) (v x) 2 = r x 2 := by
      simp only [DQr, v, LinvZ, Matrix.cons_val, gz]; ring
    rw [hc2, hG] at h02
    simp only [LR, Fin.zero_eta, Pi.add_apply, DNr, Matrix.cons_val_zero, add_zero]
    have e0 : v x 0 - v x 2 = r x 4 := by simp [v, LinvZ, cz]
    have e3 : v x 3 = lz p r x := rfl
    rw [e0, e3] at h02
    have : p.θ * p.m * (p.σ + p.ω) * lz p r x = cR4 p * r x 4 - r x 0 - r x 2 := by
      unfold lz; field_simp
    unfold cR4 at this
    linarith
  · simp only [LR, Fin.mk_one, Pi.add_apply, DNr, DQr, Matrix.cons_val_one,
      Matrix.cons_val_zero, add_zero]
    rw [hl x 3, f3]
    simp only [v, LinvZ, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val, pz]
    field_simp
    ring
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero]
    simp only [v, LinvZ, Matrix.cons_val, gz]; ring
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val]
    rw [hm x 1, f1]
    simp only [v, LinvZ, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, cz, yz]
    field_simp
    ring
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero]
    simp only [v, LinvZ, Matrix.cons_val, cz]; ring

/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity when `G = 0`**): every solution of the
homogeneous linearised system with zero initial lag is zero (no boundedness needed). -/
theorem LR_injZ (hp : p.Basic) (hG : Gw p = 0) (v : X → Fin 5 → ℝ) (h0 : LR T p v = 0) :
    v = 0 := by
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hRk : ∀ x k, (DQr p (lagv T v x) (v x) + DNr p (Mv T.M v x)) k = 0 := fun x k => by
    have := congrFun (congrFun h0 x) k; exact this
  have e4 : ∀ x, v x 0 = v x 2 := fun x => by
    have := hRk x 4
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val, add_zero] at this
    linarith
  have h3 : ∀ x, v x 3 = 0 := fun x => by
    have h02 := red_lam hp (lagv T v x) (v x)
    have c0 := hRk x 0
    have c2 := hRk x 2
    simp only [Pi.add_apply, DNr, Matrix.cons_val_zero, Matrix.cons_val, add_zero] at c0 c2
    rw [c0, c2, e4 x, sub_self, mul_zero, add_zero, hG] at h02
    have : p.θ * p.m * (p.σ + p.ω) * v x 3 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by positivity)
  have hlag3 : ∀ x, lag0 T (fun z => v z 3) x = 0 := fun x => by
    have : (fun z => v z 3) = fun _ => 0 := funext h3
    rw [this, lag0_zero]
  have h1 : ∀ x, v x 1 = 0 := fun x => by
    have := hRk x 1
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val_one, Matrix.cons_val_zero,
      add_zero] at this
    have hl : lagv T v x 3 = 0 := hlag3 x
    rw [hl, h3 x] at this
    have : p.ψ * (gamb p * v x 1) = 0 := by linarith
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hψ.ne')).resolve_left hgb.ne'
  have hM1 : ∀ x, T.M (fun z => v z 1) x = 0 := fun x => by
    have : (fun z => v z 1) = fun _ => 0 := funext h1
    rw [this, M_const T]
  have h0' : ∀ x, v x 0 = 0 := fun x => by
    have := hRk x 3
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val] at this
    have hm : Mv T.M v x 1 = 0 := hM1 x
    rw [hm, h1 x, ← e4 x] at this
    have : p.θ * p.m * (p.σ + p.ω) * v x 0 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by positivity)
  have h2 : ∀ x, v x 2 = 0 := fun x => by rw [← e4 x, h0' x]
  have h4 : ∀ x, v x 4 = 0 := fun x => by
    have c2 := hRk x 2
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val, add_zero] at c2
    rw [h0' x, h2 x, h3 x] at c2
    linarith
  funext x k
  fin_cases k
  exacts [h0' x, h1 x, h2 x, h3 x, h4 x]

/-- Woodford (2003), App. A.3 (**the uniform bound on the inverse when `G = 0`**). -/
theorem LinvZ_bound (hp : p.Basic) : ∃ K, 0 ≤ K ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y, ‖r y‖ ≤ A) → ∀ y, ‖LinvZ T p r y‖ ≤ K * A := by
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm0 : p.m ≠ 0 := hp.m_pos.ne'
  have hs0 : p.σ + p.ω ≠ 0 := hs.ne'
  set D := p.θ * p.m * (p.σ + p.ω)
  set cl := |cR4 p / D| * 1 + |-(1 / D)| * 1 + |-(1 / D)| * 1
  set cp := |1 / gamb p| * (|1| * cl + |-1| * cl) + |-(1 / (gamb p * p.ψ))| * 1
  set cy := |p.ψ / D| * cp + |-(p.β * p.ψ / D)| * cp + (|-(1 / D)| * 1 + |p.θ * p.m * p.σ / D| * 1)
  set cc := |1| * cy + |-1| * 1
  set k1 := 1 - p.σ - gamb p + lamb p * (p.θ * p.m * p.σ) * p.σ
  set k2 := -(p.θ * p.m * p.σ)
  set k3 := -(lamb p * (p.θ * p.m * p.σ))
  set cg := |1| * (|k1| * cc + |k2| * cl) + |1| * (|k3| * cy + |-1| * 1)
  refine ⟨cl + cc + cy + cp + cg, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ k y, |r y k| ≤ 1 * A := fun k y => by
    have := (norm_le_pi_norm (r y) k).trans (hr y); rw [Real.norm_eq_abs] at this; linarith
  have hL : ∀ y, |lz p r y| ≤ cl * A := fun y => by
    have := lb2 (lb2 (hr' 4) (hr' 0) (cR4 p / D) (-(1 / D))) (hr' 2) 1 (-(1 / D)) y
    convert this using 2
    · simp only [lz, D]; field_simp; ring
    · simp only [cl]; ring
  have hP : ∀ y, |pz T p r y| ≤ cp * A := fun y => by
    have := lb2 (lb2 hL (lbLag T (by positivity) hL) 1 (-1)) (hr' 1) (1 / gamb p)
      (-(1 / (gamb p * p.ψ))) y
    convert this using 2; simp only [pz]; field_simp; ring
  have hY : ∀ y, |yz T p r y| ≤ cy * A := fun y => by
    have e := lb2 (lb2 hP (lbM T hP) (p.ψ / D) (-(p.β * p.ψ / D)))
      (lb2 (hr' 3) (hr' 4) (-(1 / D)) (p.θ * p.m * p.σ / D)) 1 1 y
    convert e using 2
    · simp only [yz, D]; field_simp; ring
    · simp only [cy]; ring
  have hC : ∀ y, |cz T p r y| ≤ cc * A := fun y => by
    have := lb2 hY (hr' 4) 1 (-1) y
    convert this using 2; simp only [cz]; ring
  have hGv : ∀ y, |gz T p r y| ≤ cg * A := fun y => by
    have := lb2 (lb2 hC hL k1 k2) (lb2 hY (hr' 2) k3 (-1)) 1 1 y
    convert this using 2; simp only [gz, k1, k2, k3]; ring
  have hcc : 0 ≤ cc := by positivity
  have hcy : 0 ≤ cy := by positivity
  have hcp : 0 ≤ cp := by positivity
  have hcg : 0 ≤ cg := by positivity
  have hcl : 0 ≤ cl := by positivity
  have hA' : ∀ c, c ≤ cl + cc + cy + cp + cg → c * A ≤ (cl + cc + cy + cp + cg) * A :=
    fun c hc => mul_le_mul_of_nonneg_right hc hA
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (hY y).trans (hA' _ (by linarith))
  · exact (hP y).trans (hA' _ (by linarith))
  · exact (hC y).trans (hA' _ (by linarith))
  · exact (hL y).trans (hA' _ (by linarith))
  · exact (hGv y).trans (hA' _ (by linarith))

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyZeroInv
