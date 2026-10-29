/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyIFT

/-!
# The Calvo timeless Ramsey problem when `A_uG = 0`

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 ((1.17), (1.20), pp. 475–476: the
targeting rule and the root condition of the optimal commitment system), Chapter 6, §5
(Benigno–Woodford), and Appendix A.3.

The Calvo Ramsey results (`NonlinearNKMarkovRamseyIFT`, `…AEIFT`, `…AR1`, `…Markov`,
`…NonAdapted`) assume `A_uG ≠ 0`, `G = σ + ω + Φ(1 − σ)`. Here the remaining case `A_uG = 0` is
characterised.

* **`Gw_zero_outside`**, `Gw_zero_occurs`: with `A_u ≠ 0`, `A_uG = 0` iff `σ ≠ 1` and
  `Φ = −(σ+ω)/(1−σ)`, which is `< 0` (an overshooting subsidy) for `σ < 1` and `> 1` for
  `σ > 1`; both occur. So `A_uG > 0` on `0 ≤ Φ ≤ 1` (`NonlinearNKMarkovRamseyLin.AuGw_pos`), and
  the degenerate case lies outside that range.
* **The degenerate reduction** (`lam_eq_of_AuGw_zero`, `ell`, `kappaD`, **`ell_DQr`**): when
  `A_uG = 0`, `λ̄₁ = λ̄₄`, so BOTH the output weight and the inflation weight of the targeting
  rule vanish; the combination `ℓ(r)` of the output condition, the multiplier recursion, the
  dispersion and the summed-multiplier blocks then involves the LAGGED variables only:
  `ℓ(DQr(v₋, v) + DNr(vₙ)) = κ_D(v₋)` for every current `v` and lead `vₙ`.
* **Linear indeterminacy** (`kerV`, **`LR_kerV`**, **`LR_not_injective`**): the linearised
  operator has the nonzero CONSTANT bounded solution `kerV` (`ŷ ≡ 1`, `π ≡ κ/(1−β)`,
  `Δ̂ = λ̂₁ = λ̂₂ ≡ 0`) on every event tree, so every `a·kerV` solves the homogeneous system:
  there is a continuum of bounded linearised equilibria and no inverse with the properties used
  by the Newton contraction exists (`LR_not_injective`).
* **Linear non-existence** (**`LR_not_surjective`**): on every event tree with a root, the
  constant bounded forcing `r = (1, 0, …, 0)` has NO solution at all.
* **Exact conditions** (**`root_constraint`**, **`no_small_solution`**): for the exact Ramsey
  conditions, at every root `|ℓ_e(e) + κ_D(d)| ≤ M‖(e, d, z)‖²`; hence if `κ_D(d₀) ≠ 0` (true
  for `d₀ = e₆`, `kappaD_e6`) then for every `K` there is `ε₀ > 0` such that for `0 < ε < ε₀`
  NO exact solution with initial lag `εd₀`, no disturbances and `‖z‖ ≤ Kε` exists on any tree
  with a root: equilibria, if any, are not `O(‖d‖)`, so the conclusion of the sequence-space
  implicit function theorem (an equilibrium Lipschitz in the predetermined state) FAILS.
-/

namespace Woodford.StabilizationWelfare.TidyR6bCalvoDegenerate

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT

/-! ## When does `A_uG` vanish? -/

/-- Woodford (2003), Ch. 7: with `σ > 0`, `ω ≥ 0`, `G = 0` forces `σ ≠ 1` and `Φ < 0` (for
`σ < 1`) or `Φ > 1` (for `σ > 1`): the degenerate case lies outside `0 ≤ Φ ≤ 1`. -/
theorem Gw_zero_outside {p : Par} (R : RPar) (hp : p.Std) (hG : Gw p R = 0) :
    p.σ ≠ 1 ∧ (p.σ < 1 → R.Φ < 0) ∧ (1 < p.σ → 1 < R.Φ) := by
  unfold Gw at hG
  have hσ := hp.σ_pos
  have hω := hp.ω_nonneg
  refine ⟨fun h => by rw [h] at hG; linarith, fun h => ?_, fun h => ?_⟩
  · by_contra hc; push Not at hc; nlinarith
  · by_contra hc; push Not at hc; nlinarith

/-- Woodford (2003), Ch. 7: both degenerate cases occur: `σ = 1/2`, `ω = 0`, `Φ = −1`, and
`σ = 2`, `ω = 0`, `Φ = 2`. -/
theorem Gw_zero_occurs (α β θ φ φy Au : ℝ) :
    Gw ⟨α, β, θ, 0, 1 / 2, φ, φy⟩ ⟨Au, -1⟩ = 0 ∧ Gw ⟨α, β, θ, 0, 2, φ, φy⟩ ⟨Au, 2⟩ = 0 := by
  constructor <;> (unfold Gw; norm_num)

/-- Woodford (2003), Ch. 7: `A_uG = 0` iff `A_u = 0` or `G = 0`. -/
theorem AuGw_zero_iff {p : Par} (R : RPar) : R.Au * Gw p R = 0 ↔ R.Au = 0 ∨ Gw p R = 0 :=
  mul_eq_zero

/-! ## The degenerate reduction -/

/-- Woodford (2003), Ch. 7, p. 476 (**`λ̄₁ = λ̄₄` when `A_uG = 0`**): by
`NonlinearNKMarkovRamseyLin.key_theta`, the inflation
weight `a(λ̄₁ − λ̄₄)` of the targeting rule vanishes together with the output weight. -/
theorem lam_eq_of_AuGw_zero {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0) :
    ramseyLam p R 3 = ramseyLam p R 0 := by
  have key := key_theta R hp
  rw [h0, zero_mul] at key
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have ha : aE p ≠ 0 := by
    unfold aE; have := hp.one_lt_θ; have := hp.ω_nonneg; positivity
  have := (mul_eq_zero.1 key).resolve_left (mul_ne_zero (mul_ne_zero hab hωσ) ha)
  linarith

/-- Woodford (2003), Ch. 7: the combination `ℓ` of the residuals of the output condition (0),
the multiplier recursion (1, 2), the summed-multiplier block (2, 3) and the dispersion block
(7, 8) in which, when `A_uG = 0`, all current variables cancel. -/
noncomputable def ell (p : Par) (R : RPar) (r : Fin 9 → ℝ) : ℝ :=
  r 0 + (1 - R.Φ) * R.Au * (aE p / (p.θ - 1) * r 7 + r 8) +
    (1 - p.α * p.β) * (1 + p.ω) * (r 2 + r 3 - ramseyLam p R 0 * p.c0 / (p.θ - 1) * r 7) -
    (1 - p.α * p.β) * (p.σ + p.ω) * (-((p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) /
      (p.θ - 1) * r 7) + r 2 - (1 - p.α) / (p.α * p.c0) * r 1)

/-- Woodford (2003), Ch. 7: the value of `ℓ` on the linearised conditions, a linear function of
the lagged predetermined variables `(Δ̂₋, λ̂₁₋, λ̂₂₋)` only. -/
noncomputable def kappaD (p : Par) (R : RPar) (d : Fin 9 → ℝ) : ℝ :=
  (1 - p.α * p.β) * (p.σ + p.ω) * d 5 - p.α * ((1 - R.Φ) * R.Au) * d 4 -
    p.α * ((1 - p.α * p.β) * (1 + p.ω)) * (d 5 + d 6) -
    (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) * aE p / p.c0) *
      ((d 5 + d 6) + ramseyLam p R 3 * d 4)

/-- **Woodford (2003), Ch. 7, §1–2 (the degenerate reduction).** If `A_uG = 0`, then for all
lagged, current and lead vectors `ℓ(DQr(v₋, v) + DNr(vₙ)) = κ_D(v₋)`: the current variables
drop out of this combination of the linearised conditions. -/
theorem ell_DQr {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0)
    (vm v vn : Fin 9 → ℝ) : ell p R (DQr p R vm v + DNr p R vn) = kappaD p R vm := by
  have e0 := red_l1 R hp vm v vn
  have e1 := red_l1_lag R hp vm v vn
  have eD := red_D R hp vm v vn
  have eM := red_mu R hp vm v vn
  have hL := lam_eq_of_AuGw_zero R hp h0
  rw [h0, zero_mul, neg_zero, zero_sub] at e0
  simp only [ell, kappaD]
  rw [hL, sub_self, mul_zero, zero_mul, zero_sub] at e1
  rw [hL]
  linear_combination (-1 : ℝ) * e0 - (1 - R.Φ) * R.Au * eD -
    (1 - p.α * p.β) * (1 + p.ω) * eM + (1 - p.α * p.β) * (p.σ + p.ω) * e1

/-- Woodford (2003), Ch. 7: `κ_D` is not identically zero: its value on the inherited
`λ̂₂₋ = 1` is strictly negative. -/
theorem kappaD_e6 {p : Par} (R : RPar) (hp : p.Std) :
    kappaD p R (Pi.single 6 1) < 0 := by
  have hab : 0 < 1 - p.α * p.β := by linarith [hp.ab_lt_one]
  have hωσ : 0 < p.σ + p.ω := by linarith [hp.ω_nonneg, hp.σ_pos]
  have ha : 0 < aE p := by unfold aE; have := hp.one_lt_θ; have := hp.ω_nonneg; positivity
  have h1 : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  have hc0 := hp.c0_pos
  have hα := hp.α_pos
  have hω := hp.ω_nonneg
  simp only [kappaD, Pi.single_apply, show (4 : Fin 9) ≠ 6 by decide,
    show (5 : Fin 9) ≠ 6 by decide, ↓reduceIte, mul_zero, sub_zero, zero_add, add_zero, mul_one]
  have : 0 < p.α * ((1 - p.α * p.β) * (1 + p.ω)) := by positivity
  have : 0 < (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) * aE p / p.c0) := by positivity
  linarith

/-! ## Linear indeterminacy -/

/-- Woodford (2003), Ch. 7: the steady-state inflation of the kernel, `π* = κ/(1 − β)`. -/
noncomputable def piK (p : Par) : ℝ :=
  (1 - p.α * p.β) * (p.σ + p.ω) * (1 - p.α) / (p.c0 * p.α * (1 - p.β))

/-- Woodford (2003), Ch. 7: the `F̂` of the kernel. -/
noncomputable def FK (p : Par) : ℝ :=
  ((1 - p.α * p.β) * (1 - p.σ) + p.α * p.β * (p.θ - 1) * piK p) / (1 - p.α * p.β)

/-- Woodford (2003), Ch. 7: the `λ̂₄` of the kernel. -/
noncomputable def l4K (p : Par) (R : RPar) : ℝ :=
  ((1 - R.Φ) * R.Au + p.α * p.β * ramseyLam p R 3 * aE p * piK p) / (1 - p.α * p.β)

/-- Woodford (2003), Ch. 7: the `λ̂₃` of the kernel (from the inflation condition). -/
noncomputable def l3K (p : Par) (R : RPar) : ℝ :=
  (p.α * (p.θ - 1) * (ramseyLam p R 0 * ((p.θ - 1) * piK p + FK p)) +
    p.α * aE p * (ramseyLam p R 1 * (aE p * piK p + (FK p + p.c0 * p.α * piK p / (1 - p.α)))) -
    p.α * (p.θ - 1) * (ramseyLam p R 2 * (p.θ - 1) * piK p) +
    p.α * aE p * (l4K p R + ramseyLam p R 3 * aE p * piK p)) / (p.α * (p.θ - 1))

/-- Woodford (2003), Ch. 7 (**a constant solution of the homogeneous linearised system**):
`ŷ = 1`, `π = κ/(1 − β)`, `Δ̂ = λ̂₁ = λ̂₂ = 0`. -/
noncomputable def kerV (p : Par) (R : RPar) : Fin 9 → ℝ :=
  ![1, piK p, FK p, FK p + p.c0 * p.α * piK p / (1 - p.α), 0, 0, 0, l3K p R, l4K p R]

/-- Woodford (2003), §5: the linearised conditions depend on the lag only through components
4, 5, 6. -/
theorem DQr_lag_congr (p : Par) (R : RPar) {um um' : Fin 9 → ℝ} (u : Fin 9 → ℝ)
    (h4 : um 4 = um' 4) (h5 : um 5 = um' 5) (h6 : um 6 = um' 6) :
    DQr p R um u = DQr p R um' u := by
  simp only [DQr, h4, h5, h6]

/-- **Woodford (2003), Ch. 7 (the constant kernel).** If `A_uG = 0`, the constant vector `kerV`
solves the linearised Ramsey conditions with any lag whose predetermined components vanish:
`DQr(v₋, kerV) + DNr(kerV) = 0`. -/
theorem DQr_kerV {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0) (vm : Fin 9 → ℝ)
    (h4 : vm 4 = 0) (h5 : vm 5 = 0) (h6 : vm 6 = 0) :
    DQr p R vm (kerV p R) + DNr p R (kerV p R) = 0 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have h1β : 1 - p.β ≠ 0 := by linarith [hp.β_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hL := lam_eq_of_AuGw_zero R hp h0
  have hL1 : ramseyLam p R 1 = -ramseyLam p R 0 := by simp [ramseyLam]
  set r := DQr p R vm (kerV p R) + DNr p R (kerV p R) with hr
  have hv4 : kerV p R 4 = 0 := rfl
  have hv5 : kerV p R 5 = 0 := rfl
  have hv6 : kerV p R 6 = 0 := rfl
  -- the components fixed by construction
  have r7 : r 7 = 0 := by
    rw [hr, red_x]; simp only [kerV, Matrix.cons_val]; field_simp; ring
  have r8 : r 8 = 0 := by
    simp only [hr, DQr, DNr, Pi.add_apply, Matrix.cons_val, h4, kerV]; field_simp; ring
  have r5 : r 5 = 0 := by
    simp only [hr, DQr, DNr, Pi.add_apply, Matrix.cons_val, kerV, FK]; field_simp; ring
  have r6 : r 6 = 0 := by
    have ha : aE p = p.θ - 1 + p.c0 := by unfold aE Par.c0; ring
    simp only [hr, DQr, DNr, Pi.add_apply, Matrix.cons_val, kerV, FK, piK, ha]
    field_simp; ring
  have r4 : r 4 = 0 := by
    simp only [hr, DQr, DNr, Pi.add_apply, Matrix.cons_val, kerV, l4K]; field_simp; ring
  have r1 : r 1 = 0 := by
    simp only [hr, DQr, DNr, Pi.add_apply, Matrix.cons_val, kerV, l3K, h4, h5, h6]
    field_simp; ring
  have r0 : r 0 = 0 := by
    rw [hr, ← red_l1 R hp, h0]; simp [kerV]
  -- the remaining two from the reduction
  have eM := red_mu R hp vm (kerV p R) (kerV p R)
  have e1 := red_l1_lag R hp vm (kerV p R) (kerV p R)
  rw [← hr] at eM e1
  rw [hv5, hv6, h5, h6, r7] at eM
  rw [hv5, h5, h6, h4, r7, r1, hL] at e1
  have r2 : r 2 = 0 := by linarith
  have r3 : r 3 = 0 := by linarith
  funext i
  fin_cases i
  exacts [r0, r1, r2, r3, r4, r5, r6, r7, r8]

variable {X : Type*} (T : LagTree X)

/-- **Woodford (2003), Ch. 7 (linear indeterminacy when `A_uG = 0`).** On every event tree the
constant process `kerV` solves the homogeneous linearised Ramsey system with zero initial lag. -/
theorem LR_kerV {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0) :
    LR T p R (fun _ => kerV p R) = 0 := by
  funext x
  simp only [LR, Pi.zero_apply]
  have hM : Mv T.M (fun _ => kerV p R) x = kerV p R := Mv_const T.markov _ x
  rw [hM]
  exact DQr_kerV R hp h0 _ (by simp [lagv, lag0, kerV]) (by simp [lagv, lag0, kerV])
    (by simp [lagv, lag0, kerV])

/-- **Woodford (2003), Ch. 7 (a continuum of bounded linearised equilibria when `A_uG = 0`).**
On every event tree, for every `a ∈ ℝ` the constant process `a·kerV` is a bounded solution of the
homogeneous linearised system with zero initial lag. -/
theorem LR_smul_kerV {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0) (a : ℝ) :
    LR T p R (fun _ => a • kerV p R) = 0 ∧ ∀ (_ : X) k, |(a • kerV p R) k| ≤ |a| * ‖kerV p R‖ := by
  refine ⟨?_, fun _ k => ?_⟩
  · funext x
    simp only [LR, Pi.zero_apply]
    have hM : Mv T.M (fun _ => a • kerV p R) x = a • kerV p R := Mv_const T.markov _ x
    have hl : lagv T (fun _ => a • kerV p R) x = a • lagv T (fun _ => kerV p R) x := by
      funext i; simp only [lagv, lag0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    have hlin := (DLin p R).map_smul a (lagv T (fun _ => kerV p R) x, kerV p R, kerV p R)
    simp only [DLin, LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_mk] at hlin
    rw [hM, hl, hlin]
    have := congrFun (LR_kerV T R hp h0) x
    simp only [LR, Mv_const T.markov, Pi.zero_apply] at this
    rw [this, smul_zero]
  · rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (by
      have := norm_le_pi_norm (kerV p R) k; rwa [Real.norm_eq_abs] at this) (abs_nonneg a)

/-- **Woodford (2003), Ch. 7 (no inverse when `A_uG = 0`).** On every nonempty event tree, the
linearised operator is NOT injective on bounded processes: so no inverse with the properties
used by the Newton contraction (`TidyR6bRamseyNewton.InvBound`) exists. -/
theorem LR_not_injective {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0) (x0 : X) :
    ¬ ∀ (v : X → Fin 9 → ℝ) (B : ℝ), (∀ x k, |v x k| ≤ B) → LR T p R v = 0 → v = 0 := by
  intro h
  obtain ⟨hL, hB⟩ := LR_smul_kerV T R hp h0 1
  have := congrFun (congrFun (h _ _ hB hL) x0) 0
  simp [kerV] at this

/-! ## Linear non-existence -/

/-- **Woodford (2003), Ch. 7 (linear non-existence when `A_uG = 0`).** On every event tree with a
root `x₀`, the linearised Ramsey system with the constant bounded forcing `r = (1, 0, …, 0)` (a
unit shock to the output condition) has NO solution `v`, bounded or not. -/
theorem LR_not_surjective {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0) {x0 : X}
    (hx0 : T.depth x0 = 0) (v : X → Fin 9 → ℝ) :
    LR T p R v ≠ fun _ => ![1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  intro h
  have hr := congrFun h x0
  have hlag : lagv T v x0 = 0 := by funext i; simp [lagv, lag0, hx0]
  have key := ell_DQr R hp h0 (lagv T v x0) (v x0) (Mv T.M v x0)
  have hk : kappaD p R (lagv T v x0) = 0 := by rw [hlag]; simp [kappaD]
  have hl : ell p R (DQr p R (lagv T v x0) (v x0) + DNr p R (Mv T.M v x0)) = 1 := by
    change ell p R (LR T p R v x0) = 1
    rw [hr]; simp [ell]
  rw [hl, hk] at key
  exact one_ne_zero key

/-! ## The exact conditions: no equilibrium of the size of the shock -/

/-- Woodford (2003), App. A.3 (tool): a `C²` function has a quadratic Taylor remainder near `0`:
`|g(q) − g(0) − Dg(0)q| ≤ M‖q‖²` for `‖q‖ ≤ ρ`. -/
theorem taylor2_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}
    (hg : ContDiff ℝ 2 g) : ∃ M, 0 ≤ M ∧ ∃ ρ > 0, ∀ q : E, ‖q‖ ≤ ρ →
      |g q - g 0 - fderiv ℝ g 0 q| ≤ M * ‖q‖ ^ 2 := by
  have hd : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := (hd.contDiffAt (x := 0)).exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨K, K.2, ρ / 2, by positivity, fun q hq => ?_⟩
  set S := Metric.closedBall (0 : E) ‖q‖
  have hS : S ⊆ t := fun y hy => hball (by
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith)
  set A := fderiv ℝ g 0
  have hdiff : ∀ y ∈ S, HasFDerivWithinAt (fun y => g y - A y) (fderiv ℝ g y - A) S y :=
    fun y _ => ((hg.differentiable (by norm_num) y).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ y ∈ S, ‖fderiv ℝ g y - A‖ ≤ K * ‖q‖ := fun y hy => by
    have h1 := hK.dist_le_mul y (hS hy) 0 (hS (Metric.mem_closedBall_self (norm_nonneg q)))
    rw [dist_eq_norm, dist_zero_right] at h1
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact h1.trans (mul_le_mul_of_nonneg_left hy K.2)
  have hq' : q ∈ S := by rw [Metric.mem_closedBall, dist_zero_right]
  have h := (convex_closedBall (0 : E) ‖q‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff
    hbound (Metric.mem_closedBall_self (norm_nonneg q)) hq'
  have e1 : (g q - A q) - (g 0 - A 0) = g q - g 0 - A q := by rw [map_zero]; ring
  rw [e1, sub_zero, Real.norm_eq_abs] at h
  calc |g q - g 0 - A q| ≤ K * ‖q‖ * ‖q‖ := h
    _ = K * ‖q‖ ^ 2 := by ring

/-- Woodford (2003), Ch. 7: the combination `ℓ` as a linear map. -/
noncomputable def ellL (p : Par) (R : RPar) : (Fin 9 → ℝ) →ₗ[ℝ] ℝ where
  toFun := ell p R
  map_add' r r' := by simp only [ell, Pi.add_apply]; ring
  map_smul' c r := by simp only [ell, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Woodford (2003), Ch. 7: the disturbance part `ℓ_e(e) = ℓ(DQ(0)(e, 0, 0))` of the combination. -/
noncomputable def ellE (p : Par) (R : RPar) (e : Fin 5 → ℝ) : ℝ :=
  ell p R (fderiv ℝ (Qd p R) 0 (e, 0, 0))

/-- Woodford (2003), §5: the part inside `E_t` never enters the components used by `ℓ`. -/
theorem ell_N (p : Par) (R : RPar) (n : Fin 9 → ℝ) : ell p R (Nd p R n) = 0 := by
  simp [ell, Nd, ramseyN]

/-- **Woodford (2003), Ch. 7 and App. A.3 (the root constraint of the exact conditions when
`A_uG = 0`).** There are `M ≥ 0`, `ρ > 0` such that on every event tree, at every root `x` of a
solution of the EXACT Ramsey conditions with `‖(e(x), d(x), z(x))‖ ≤ ρ`,
`|ℓ_e(e(x)) + κ_D(d(x))| ≤ M‖(e(x), d(x), z(x))‖²`: the current variables enter only at second
order. -/
theorem root_constraint {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0) :
    ∃ M, 0 ≤ M ∧ ∃ ρ > 0, ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 5 → ℝ)
      (d z : Y → Fin 9 → ℝ), PhiR T p R e d z = 0 → ∀ x, T.depth x = 0 →
        ‖((e x, d x, z x) : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))‖ ≤ ρ →
          |ellE p R (e x) + kappaD p R (d x)| ≤
            M * ‖((e x, d x, z x) : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))‖ ^ 2 := by
  set L := LinearMap.toContinuousLinearMap (ellL p R)
  have hg : ContDiff ℝ 2 (fun q => L (Qd p R q)) := L.contDiff.comp (contDiff_Qd p R)
  obtain ⟨M, hM, ρ, hρ, hT⟩ := taylor2_bound hg
  refine ⟨M, hM, ρ, hρ, fun {Y} T e d z hz x hx hq => ?_⟩
  have hL : ∀ r, L r = ell p R r := fun r => rfl
  -- the value at the steady state
  have h00 : L (Qd p R 0) = 0 := by
    have hss := Qd_Nd_zero R hp
    have : Qd p R 0 = -Nd p R 0 := eq_neg_of_add_eq_zero_left hss
    rw [this, map_neg, hL, ell_N, neg_zero]
  -- the derivative
  have hD : fderiv ℝ (fun q => L (Qd p R q)) 0 (e x, d x, z x) =
      ellE p R (e x) + kappaD p R (d x) := by
    have hQd : HasFDerivAt (Qd p R) (fderiv ℝ (Qd p R) 0) 0 :=
      ((contDiff_Qd (n := 1) p R).differentiable one_ne_zero 0).hasFDerivAt
    rw [show (fun q => L (Qd p R q)) = ⇑L ∘ Qd p R from rfl,
      (L.hasFDerivAt.comp 0 hQd).fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    have hsplit : ((e x, d x, z x) : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)) =
        (e x, 0, 0) + (0, d x, z x) := by simp
    rw [hsplit, map_add, map_add, hL, hL, fderiv_Qd R hp]
    have := ell_DQr R hp h0 (d x) (z x) 0
    simp only [DNr, ramseyLam, Pi.zero_apply, mul_zero, zero_add, neg_zero] at this
    have e2 : DQr p R (d x) (z x) + ![0, 0, 0, 0, 0, 0, 0, 0, 0] = DQr p R (d x) (z x) := by
      funext i; fin_cases i <;> simp
    rw [ellE]
    congr 1
    rw [← this]
    congr 1
    rw [e2]
  -- the residual at the root
  have hres : L (Qd p R (e x, d x, z x)) = 0 := by
    have hz' := congrFun hz x
    simp only [PhiR, lagI, hx, ↓reduceIte, Pi.zero_apply] at hz'
    have h1 := congrArg L hz'
    rw [map_add, map_zero, hL (Mv T.M _ x)] at h1
    have h2 : ell p R (Mv T.M (fun y => Nd p R (z y)) x) = 0 := by
      simp [ell, Mv, Nd, ramseyN]
      have hz0 : ∀ i : Fin 9, i ≠ 4 → i ≠ 5 → i ≠ 6 → (T.M fun _ => (0 : ℝ)) x = 0 := by
        intro _ _ _ _
        have : (fun _ : Y => (0 : ℝ)) = (0 : ℝ) • fun _ => (1 : ℝ) := by funext; simp
        rw [this, map_smul]; simp
      simp only [hz0 0 (by decide) (by decide) (by decide)]
      ring
    rw [h2, add_zero] at h1
    exact h1
  have h := hT (e x, d x, z x) hq
  rw [hres, h00, hD, sub_zero, zero_sub, abs_neg] at h
  exact h

/-- **Woodford (2003), Ch. 7 and App. A.3 (no equilibrium of the size of the inherited
multipliers when `A_uG = 0`).** If `κ_D(d₀) ≠ 0`, then for every `K ≥ 0` there is `ε₀ > 0` such
that for `0 < ε < ε₀`, on every event tree with a root, there is NO solution `z` of the exact
Ramsey conditions without disturbances, with initial lag `εd₀` at the roots, and `‖z‖ ≤ Kε`. -/
theorem no_small_solution {p : Par} (R : RPar) (hp : p.Std) (h0 : R.Au * Gw p R = 0)
    {d0 : Fin 9 → ℝ} (hd0 : kappaD p R d0 ≠ 0) (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε0 > 0, ∀ ε, 0 < ε → ε < ε0 → ∀ {Y : Type*} (T : LagTree Y) (x0 : Y), T.depth x0 = 0 →
      ∀ z : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ K * ε) →
        PhiR T p R (fun _ => 0) (fun _ => ε • d0) z ≠ 0 := by
  obtain ⟨M, hM, ρ, hρ, hc⟩ := root_constraint R hp h0
  set C := ‖d0‖ + K with hC
  have hC0 : 0 ≤ C := by positivity
  have hk : 0 < |kappaD p R d0| := abs_pos.2 hd0
  refine ⟨min (ρ / (C + 1)) (|kappaD p R d0| / (M * C ^ 2 + 1)), lt_min (by positivity)
    (by positivity), fun ε hε hε0 Y T x0 hx0 z hz hPhi => ?_⟩
  have hε1 : ε < ρ / (C + 1) := hε0.trans_le (min_le_left _ _)
  have hε2 : ε < |kappaD p R d0| / (M * C ^ 2 + 1) := hε0.trans_le (min_le_right _ _)
  have hnorm : ‖(((fun _ => (0 : Fin 5 → ℝ)) x0, (fun _ => ε • d0) x0, z x0) :
      (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))‖ ≤ C * ε := by
    simp only [Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    refine max_le (by positivity) (max_le ?_ ((hz x0).trans ?_))
    · rw [hC]; nlinarith [norm_nonneg d0]
    · rw [hC]; nlinarith [norm_nonneg d0]
  have hρ' : C * ε ≤ ρ := by
    have : ε * (C + 1) < ρ := by rwa [lt_div_iff₀ (by positivity)] at hε1
    nlinarith
  have h := hc T _ _ z hPhi x0 hx0 (hnorm.trans hρ')
  have hE : ellE p R 0 = 0 := by
    simp only [ellE]
    rw [show (((0 : Fin 5 → ℝ), (0 : Fin 9 → ℝ), (0 : Fin 9 → ℝ)) :
      (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)) = 0 from rfl, map_zero]
    simp [ell]
  have hkap : kappaD p R (ε • d0) = ε * kappaD p R d0 := by
    simp only [kappaD, Pi.smul_apply, smul_eq_mul]; ring
  rw [hE, zero_add, hkap, abs_mul, abs_of_pos hε] at h
  have h2 : ε * |kappaD p R d0| ≤ M * (C * ε) ^ 2 :=
    h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hM)
  have h3 : |kappaD p R d0| ≤ M * C ^ 2 * ε := by
    have : ε * |kappaD p R d0| ≤ ε * (M * C ^ 2 * ε) := by nlinarith
    exact le_of_mul_le_mul_left this hε
  have h4 : ε * (M * C ^ 2 + 1) < |kappaD p R d0| := by
    rwa [lt_div_iff₀ (by positivity)] at hε2
  nlinarith

end Woodford.StabilizationWelfare.TidyR6bCalvoDegenerate
