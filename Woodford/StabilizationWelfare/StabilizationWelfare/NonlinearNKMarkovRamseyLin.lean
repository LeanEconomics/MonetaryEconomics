/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamsey

/-!
# The linearised Ramsey system reduces to the commitment system; the root condition

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (pp. 470–490: the optimal commitment
`π_t + (λ_x/κ)(x_t − x_{t−1}) = 0` with `λ_x = κ/θ`, and its characteristic polynomial
`βz² − (1 + β + κ²/λ_x)z + 1`), and Chapter 6, §5 (Benigno–Woodford, the distorted steady state).

`NonlinearNKMarkovRamsey` gives the nine exact Ramsey conditions
`Q(e_t, w_{t−1}, w_t) + E_t N(w_{t+1}) = 0` and their zero-inflation steady state `w̄`. Here:

* **`commit_roots`**, **`ramsey_root_condition`**: for every `0 < β < 1` and `c > 0`,
  `βz² − (1+β+c)z + 1` has exactly two real roots `0 < z₁ < 1 < z₂` (`βz₁z₂ = 1`); with
  `c = κ²/λ_x = κθ` this holds for every admissible calibration (`p.Std`).
* `Qd`, `Nd`: the conditions in deviations from `w̄`; `contDiff_Qd`, `contDiff_Nd`.
* `DQr`, `DNr`: the explicit linearisation, and **`fderiv_Qd`**, **`fderiv_Nd`**: they ARE the
  Fréchet derivatives at the steady state (line derivatives `hasDerivAt_Qd_line`,
  `hasDerivAt_Nd_line`).
* The reduction of the 9×9 linear system (`v = (ŷ, π, F̂, K̂, Δ̂, λ̂₁, λ̂₂, λ̂₃, λ̂₄)`, lag `vm`,
  expected lead `vn`, forcing `r = DQr vm v + DNr vn`): `red_x` (price index), `red_D`
  (`Δ̂ = αΔ̂₋ + ⋯`), `red_mu` (`λ̂₁ + λ̂₂ = α(λ̂₁ + λ̂₂)₋ + ⋯`), `red_pc` (the NKPC
  `π = κŷ + βE π′ + ⋯`), `red_l1`, `red_l1_lag`, and **`red_target`**: the targeting rule
  `Γ(ŷ − ŷ₋) + Γθπ = ⋯` with `Γ = A_u((σ+ω) + Φ(1−σ))`, i.e. `λ_x = κ/θ` for EVERY distortion
  `Φ` (`key_theta`). **`commitment_system`** collects the homogeneous case: the exact
  linearisation is the commitment system driven by the decaying predetermined block.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyLin

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovRamsey

/-! ## The root condition -/

/-- Woodford (2003), Ch. 7, (1.20) (**the root condition of the commitment system**): for
`0 < β < 1` and `c > 0` the polynomial `βz² − (1+β+c)z + 1` has two real roots
`0 < z₁ < 1 < z₂` with `βz₁z₂ = 1`, `β(z₁ + z₂) = 1 + β + c`, and no other real roots. -/
theorem commit_roots {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    ∃ z1 z2 : ℝ, 0 < z1 ∧ z1 < 1 ∧ 1 < z2 ∧ β * z1 * z2 = 1 ∧ β * (z1 + z2) = 1 + β + c ∧
      (∀ z : ℝ, β * z ^ 2 - (1 + β + c) * z + 1 = 0 ↔ z = z1 ∨ z = z2) := by
  set A := 1 + β + c with hA
  set D := A ^ 2 - 4 * β with hD
  have hDpos : (1 - β + c) ^ 2 < D := by rw [hD, hA]; nlinarith
  have hD0 : 0 < D := lt_of_le_of_lt (sq_nonneg _) hDpos
  set q := Real.sqrt D with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg D
  have hqq : q * q = D := Real.mul_self_sqrt hD0.le
  have hq1 : 1 - β + c < q := by
    rw [hq]; exact Real.lt_sqrt_of_sq_lt hDpos
  have hqA : q < A := by
    rw [hq, Real.sqrt_lt' (by linarith)]; rw [hD]; nlinarith
  refine ⟨(A - q) / (2 * β), (A + q) / (2 * β), by apply div_pos <;> linarith,
    by rw [div_lt_one (by linarith)]; linarith, by rw [one_lt_div (by linarith)]; linarith,
    by field_simp; nlinarith, by field_simp; ring, fun z => ?_⟩
  have hfac : β * z ^ 2 - A * z + 1 = β * (z - (A - q) / (2 * β)) * (z - (A + q) / (2 * β)) := by
    field_simp; rw [hD] at hqq; nlinarith
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hβ0.ne'
      · left; linarith
    · right; linarith
  · rintro (h | h) <;> rw [h] <;> ring

/-- Woodford (2003), Ch. 7, pp. 475–476 (**the root condition for every admissible
calibration**): with the optimal weight `λ_x = κ/θ` (so `κ²/λ_x = κθ > 0`), the commitment
polynomial `βz² − (1 + β + κ²/λ_x)z + 1` has exactly one root inside and one outside the unit
circle. -/
theorem ramsey_root_condition {p : Par} (hp : p.Std) :
    ∃ z1 z2 : ℝ, 0 < z1 ∧ z1 < 1 ∧ 1 < z2 ∧ p.β * z1 * z2 = 1 ∧
      p.β * (z1 + z2) = 1 + p.β + p.κ ^ 2 / (p.κ / p.θ) ∧
      (∀ z : ℝ, p.β * z ^ 2 - (1 + p.β + p.κ ^ 2 / (p.κ / p.θ)) * z + 1 = 0 ↔ z = z1 ∨ z = z2) := by
  have hk := hp.κ_pos
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have e : p.κ ^ 2 / (p.κ / p.θ) = p.κ * p.θ := by field_simp
  rw [e]
  exact commit_roots hp.β_pos hp.β_lt_one (mul_pos hk hθ)

/-! ## The conditions in deviations and their linearisation -/

/-- Woodford (2003), §5: the current part of the exact Ramsey conditions as a function of the
disturbances and the DEVIATIONS `(w₋ − w̄, w − w̄)` from the steady state. -/
noncomputable def Qd (p : Par) (R : RPar) (q : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)) :
    Fin 9 → ℝ :=
  ramseyQ p R q.1 (ramseySS p R + q.2.1) (ramseySS p R + q.2.2)

/-- Woodford (2003), §5: the part of the exact Ramsey conditions inside `E_t`, in deviations. -/
noncomputable def Nd (p : Par) (R : RPar) (n : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ramseyN p (ramseySS p R + n)

/-- Woodford (2003), §5: the current part is `C^∞`. -/
theorem contDiff_Qd {n : WithTop ℕ∞} (p : Par) (R : RPar) : ContDiff ℝ n (Qd p R) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Qd, ramseyQ, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Pi.add_apply] <;>
    fun_prop

/-- Woodford (2003), §5: the part inside `E_t` is `C^∞`. -/
theorem contDiff_Nd {n : WithTop ℕ∞} (p : Par) (R : RPar) : ContDiff ℝ n (Nd p R) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Nd, ramseyN, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Pi.add_apply] <;>
    fun_prop

/-- Woodford (2003), §5: the steady state in deviation form, `Q(0, 0, 0) + N(0) = 0`. -/
theorem Qd_Nd_zero {p : Par} (R : RPar) (hp : p.Std) : Qd p R (0, 0, 0) + Nd p R 0 = 0 := by
  simpa [Qd, Nd] using ramsey_steadyState p R hp

/-- Woodford (2003), §5 (**the linearised current part**) at the steady state, for the lag
direction `um` and the current direction `u` (`L_i = ramseyLam`, `s = 1 − αβ`, `b = θ − 1`,
`a = θ(1+ω)`, `x̂ = (u₃ − u₂)/(1+ωθ)`). -/
noncomputable def DQr (p : Par) (R : RPar) (um u : Fin 9 → ℝ) : Fin 9 → ℝ :=
  let s := 1 - p.α * p.β
  let b := p.θ - 1
  let a := aE p
  let x := (u 3 - u 2) / p.c0
  let L := ramseyLam p R
  ![R.Au * (1 - p.σ) * u 0 - (1 - R.Φ) * R.Au * (u 4 + (1 + p.ω) * u 0)
      - s * (1 - p.σ) * (u 5 + L 0 * (1 - p.σ) * u 0)
      - s * (1 + p.ω) * (u 6 + L 1 * (1 + p.ω) * u 0),
    -(p.α * b * (um 5 + L 0 * (b * u 1 + u 2))) - p.α * a * (um 6 + L 1 * (a * u 1 + u 3))
      + p.α * b * (u 7 + L 2 * b * u 1) - p.α * a * (u 8 + L 3 * um 4 + L 3 * a * u 1),
    u 5 + L 0 * u 2 - p.α * (um 5 + L 0 * (b * u 1 + u 2))
      + (1 - p.α) * (b / p.c0) * (u 7 - L 2 * b * x) - (1 - p.α) * (a / p.c0) * (u 8 - L 3 * a * x),
    u 6 + L 1 * u 3 - p.α * (um 6 + L 1 * (a * u 1 + u 3))
      - (1 - p.α) * (b / p.c0) * (u 7 - L 2 * b * x) + (1 - p.α) * (a / p.c0) * (u 8 - L 3 * a * x),
    -((1 - R.Φ) * R.Au * u 0) + u 8,
    u 2 - s * (1 - p.σ) * u 0,
    u 3 - s * (1 + p.ω) * u 0,
    p.α * b * u 1 - (1 - p.α) * b * x,
    u 4 - p.α * (um 4 + a * u 1) + (1 - p.α) * a * x]

/-- Woodford (2003), §5 (**the linearised part inside `E_t`**) at the steady state. -/
noncomputable def DNr (p : Par) (R : RPar) (n : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![0, 0, 0, 0, -(p.β * p.α * (n 8 + ramseyLam p R 3 * aE p * n 1)),
    -(p.α * p.β * ((p.θ - 1) * n 1 + n 2)), -(p.α * p.β * (aE p * n 1 + n 3)), 0, 0]

/-- `t ↦ (a + tb)(a′ + tb′)e^{tc}` has derivative `ba′ + ab′ + aa′c` at `0`. -/
theorem hd3 (a b a' b' c : ℝ) :
    HasDerivAt (fun t : ℝ => (a + t * b) * (a' + t * b') * Real.exp (t * c))
      (b * a' + a * b' + a * a' * c) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
  have h2 : HasDerivAt (fun t : ℝ => a' + t * b') b' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b').const_add a'
  have h3 : HasDerivAt (fun t : ℝ => Real.exp (t * c)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).exp
  convert (h1.mul h2).mul h3 using 1
  simp only [Pi.mul_apply, zero_mul, add_zero, Real.exp_zero, mul_one]

/-- `t ↦ a + tb` has derivative `b` at `0`. -/
theorem hdlin (a b : ℝ) : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- Woodford (2003), §5: the derivative of the current part along `t ↦ (0, t·um, t·u)` at the
steady state is `DQr um u`. -/
theorem hasDerivAt_Qd_line {p : Par} (R : RPar) (hp : p.Std) (um u : Fin 9 → ℝ) (i : Fin 9) :
    HasDerivAt (fun t : ℝ => Qd p R (0, t • um, t • u) i) (DQr p R um u i) 0 := by
  have hω : 1 + p.ω ≠ 0 := by linarith [hp.ω_nonneg]
  set L := ramseyLam p R with hL
  set b := p.θ - 1 with hb
  set a := aE p with ha
  set c0 := p.c0 with hc0
  set s := 1 - p.α * p.β with hs
  set xc := (u 3 - u 2) / c0 with hxc
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := (((((hd3 1 0 1 0 ((1 - p.σ) * u 0)).const_mul R.Au).sub
      ((hd3 1 (u 4) 1 0 ((1 + p.ω) * u 0)).const_mul ((1 - R.Φ) * R.Au))).sub
      ((hd3 (ramseyLam p R 0) (u 5) 1 0 ((1 - p.σ) * u 0)).const_mul
        ((1 - p.α * p.β) * (1 - p.σ)))).sub
      ((hd3 (ramseyLam p R 1) (u 6) 1 0 ((1 + p.ω) * u 0)).const_mul ((1 - p.α * p.β) * (1 + p.ω))))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := ((((hd3 (ramseyLam p R 0) (um 5) 1 0 ((p.θ - 1) * u 1 + u 2)).const_mul
      (-(p.α * (p.θ - 1)))).sub
      ((hd3 (ramseyLam p R 1) (um 6) 1 0 (aE p * u 1 + u 3)).const_mul (p.α * aE p))).add
      ((hd3 (ramseyLam p R 2) (u 7) 1 0 ((p.θ - 1) * u 1)).const_mul (p.α * (p.θ - 1)))).sub
      ((hd3 (ramseyLam p R 3) (u 8) 1 (um 4) (aE p * u 1)).const_mul (p.α * aE p))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := (((hd3 (ramseyLam p R 0) (u 5) 1 0 (u 2)).sub
      ((hd3 (ramseyLam p R 0) (um 5) 1 0 ((p.θ - 1) * u 1 + u 2)).const_mul p.α)).add
      ((hd3 (ramseyLam p R 2) (u 7) 1 0 (-((p.θ - 1) * ((u 3 - u 2) / p.c0)))).const_mul
        ((1 - p.α) * ((p.θ - 1) / p.c0)))).sub
      ((hd3 (ramseyLam p R 3) (u 8) 1 0 (-(aE p * ((u 3 - u 2) / p.c0)))).const_mul
        ((1 - p.α) * (aE p / p.c0)))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := (((hd3 (ramseyLam p R 1) (u 6) 1 0 (u 3)).sub
      ((hd3 (ramseyLam p R 1) (um 6) 1 0 (aE p * u 1 + u 3)).const_mul p.α)).sub
      ((hd3 (ramseyLam p R 2) (u 7) 1 0 (-((p.θ - 1) * ((u 3 - u 2) / p.c0)))).const_mul
        ((1 - p.α) * ((p.θ - 1) / p.c0)))).add
      ((hd3 (ramseyLam p R 3) (u 8) 1 0 (-(aE p * ((u 3 - u 2) / p.c0)))).const_mul
        ((1 - p.α) * (aE p / p.c0)))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := ((hd3 1 0 1 0 ((1 + p.ω) * u 0)).const_mul (-((1 - R.Φ) * R.Au / (1 + p.ω)))).add
      (hdlin (ramseyLam p R 3) (u 8))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; field_simp; ring))
      |>.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    ring_nf
  · have h := (hd3 1 0 1 0 (u 2)).sub ((hd3 1 0 1 0 ((1 - p.σ) * u 0)).const_mul (1 - p.α * p.β))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := (hd3 1 0 1 0 (u 3)).sub ((hd3 1 0 1 0 ((1 + p.ω) * u 0)).const_mul (1 - p.α * p.β))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := (((hd3 1 0 1 0 ((p.θ - 1) * u 1)).sub_const 1).const_mul p.α).add
      (((hd3 1 0 1 0 (-((p.θ - 1) * ((u 3 - u 2) / p.c0)))).sub_const 1).const_mul (1 - p.α))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    ring_nf
  · have h := ((hdlin 1 (u 4)).sub ((hd3 1 (um 4) 1 0 (aE p * u 1)).const_mul p.α)).sub
      ((hd3 1 0 1 0 (-(aE p * ((u 3 - u 2) / p.c0)))).const_mul (1 - p.α))
    refine (h.congr_deriv (by simp only [DQr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qd, ramseyQ, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Pi.sub_apply]
    ring_nf

/-- Woodford (2003), §5: the derivative of the part inside `E_t` along `t ↦ t·n` at the steady
state is `DNr n`. -/
theorem hasDerivAt_Nd_line {p : Par} (R : RPar) (n : Fin 9 → ℝ) (i : Fin 9) :
    HasDerivAt (fun t : ℝ => Nd p R (t • n) i) (DNr p R n i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  all_goals first
    | (simp only [Nd, ramseyN, DNr, Matrix.cons_val]; exact hasDerivAt_const _ _)
    | skip
  · have h := (hd3 (ramseyLam p R 3) (n 8) 1 0 (aE p * n 1)).const_mul (-(p.β * p.α))
    refine (h.congr_deriv (by simp only [DNr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nd, ramseyN, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · have h := (hd3 1 0 1 0 ((p.θ - 1) * n 1 + n 2)).const_mul (-(p.α * p.β))
    refine (h.congr_deriv (by simp only [DNr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nd, ramseyN, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · have h := (hd3 1 0 1 0 (aE p * n 1 + n 3)).const_mul (-(p.α * p.β))
    refine (h.congr_deriv (by simp only [DNr, Matrix.cons_val]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nd, ramseyN, ramseySS, Matrix.cons_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf

/-- Woodford (2003), §5 (**the explicit linearisation is the Fréchet derivative**): the partial
derivative of the current part at the steady state in the direction `(0, um, u)` is
`DQr um u`. -/
theorem fderiv_Qd {p : Par} (R : RPar) (hp : p.Std) (um u : Fin 9 → ℝ) :
    fderiv ℝ (Qd p R) 0 (0, um, u) = DQr p R um u := by
  have hd : HasFDerivAt (Qd p R) (fderiv ℝ (Qd p R) 0) 0 :=
    ((contDiff_Qd (n := 1) p R).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 5 → ℝ), t • um, t • u))
      ((0 : Fin 5 → ℝ), um, u) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : Fin 5 → ℝ)).prodMk
      (((hasDerivAt_id (0 : ℝ)).smul_const um).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const u))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp; rfl)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Qd_line R hp um u i)

/-- Woodford (2003), §5: the derivative of the part inside `E_t` at the steady state is
`DNr`. -/
theorem fderiv_Nd {p : Par} (R : RPar) (n : Fin 9 → ℝ) : fderiv ℝ (Nd p R) 0 n = DNr p R n := by
  have hd : HasFDerivAt (Nd p R) (fderiv ℝ (Nd p R) 0) 0 :=
    ((contDiff_Nd (n := 1) p R).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • n) n 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const n
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Nd_line R n i)

/-! ## Reduction of the linearised system to the commitment system -/

/-- Woodford (2003), Ch. 6, §5 and Ch. 7: the welfare-weighted slope `G = (σ+ω) + Φ(1−σ)`. -/
def Gw (p : Par) (R : RPar) : ℝ := p.σ + p.ω + R.Φ * (1 - p.σ)

/-- Woodford (2003), Ch. 6, §5 (**admissible distortions**): for `A_u > 0` and `0 ≤ Φ ≤ 1` the
weight `A_uG` of the targeting rule is positive, so the reduction never degenerates. -/
theorem AuGw_pos {p : Par} (R : RPar) (hp : p.Std) (hAu : 0 < R.Au) (hΦ0 : 0 ≤ R.Φ)
    (hΦ1 : R.Φ ≤ 1) : 0 < R.Au * Gw p R := by
  have hσ := hp.σ_pos
  have hω := hp.ω_nonneg
  have : 0 < Gw p R := by
    unfold Gw
    rcases eq_or_lt_of_le hΦ0 with h | h
    · rw [← h]; linarith
    · nlinarith [mul_nonneg hσ.le (sub_nonneg.2 hΦ1)]
  positivity

/-- Woodford (2003), Ch. 7, p. 476 (**`λ_x/κ = 1/θ` for every distortion**): the coefficients of
the linearised first-order conditions satisfy `(1−αβ)(σ+ω)a(λ̄₄ − λ̄₁) = A_u G θ`. -/
theorem key_theta {p : Par} (R : RPar) (hp : p.Std) :
    (1 - p.α * p.β) * (p.σ + p.ω) * aE p * (ramseyLam p R 3 - ramseyLam p R 0) =
      R.Au * Gw p R * p.θ := by
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hω : 1 + p.ω ≠ 0 := by linarith [hp.ω_nonneg]
  simp only [ramseyLam, Matrix.cons_val, aE, Gw]
  field_simp
  ring

/-- Woodford (2003), (2.20) of Ch. 3 linearised: the price index `αbπ − (1−α)bx̂ = r₇`. -/
theorem red_x {p : Par} (R : RPar) (vm v vn : Fin 9 → ℝ) :
    (DQr p R vm v + DNr p R vn) 7 = p.α * (p.θ - 1) * v 1 - (1 - p.α) * (p.θ - 1) *
      ((v 3 - v 2) / p.c0) := by
  simp [DQr, DNr]

/-- Woodford (2003), (2.20) linearised (**the dispersion block**):
`Δ̂ = αΔ̂₋ + (a/b)r₇ + r₈`. -/
theorem red_D {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) :
    v 4 = p.α * vm 4 + aE p / (p.θ - 1) * (DQr p R vm v + DNr p R vn) 7 +
      (DQr p R vm v + DNr p R vn) 8 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val]
  field_simp
  ring

/-- Woodford (2003), §5 and Ch. 7 (**the summed-multiplier block**):
`μ = αμ₋ + r₂ + r₃ − (λ̄₁c₀/b)r₇`, `μ = λ̂₁ + λ̂₂`. -/
theorem red_mu {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) :
    v 5 + v 6 = p.α * (vm 5 + vm 6) + (DQr p R vm v + DNr p R vn) 2 +
      (DQr p R vm v + DNr p R vn) 3 -
        ramseyLam p R 0 * p.c0 / (p.θ - 1) * (DQr p R vm v + DNr p R vn) 7 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hL : ramseyLam p R 1 = -ramseyLam p R 0 := by simp [ramseyLam]
  simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val]
  rw [hL]
  field_simp
  unfold aE Par.c0
  ring

/-- Woodford (2003), (2.19) of Ch. 3 linearised (**the NKPC**): with `m₇` the expected price-index
residual, `π = κŷ + βE π′ + ((1−α)/(c₀α))(r₆ − r₅) + (r₇ − αβm₇)/(αb)`. -/
theorem red_pc {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) :
    v 1 = p.κ * v 0 + p.β * vn 1 + (1 - p.α) / (p.c0 * p.α) *
      ((DQr p R vm v + DNr p R vn) 6 - (DQr p R vm v + DNr p R vn) 5) +
        ((DQr p R vm v + DNr p R vn) 7 - p.α * p.β * (p.α * (p.θ - 1) * vn 1 -
          (1 - p.α) * (p.θ - 1) * ((vn 3 - vn 2) / p.c0))) / (p.α * (p.θ - 1)) := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have hc0' : 1 + p.ω * p.θ ≠ 0 := hc0
  simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, Par.κ, Moments.calvoKappa]
  unfold aE Par.c0
  field_simp
  ring

/-- Woodford (2003), §5: the output condition (component 0) in terms of `λ̂₁` and
`μ = λ̂₁ + λ̂₂`: `−A_u G ŷ − A_v Δ̂ + (1−αβ)(σ+ω)λ̂₁ − (1−αβ)(1+ω)μ = r₀`. -/
theorem red_l1 {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) :
    -(R.Au * Gw p R * v 0) - (1 - R.Φ) * R.Au * v 4 + (1 - p.α * p.β) * (p.σ + p.ω) * v 5 -
      (1 - p.α * p.β) * (1 + p.ω) * (v 5 + v 6) = (DQr p R vm v + DNr p R vn) 0 := by
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, ramseyLam, Gw]
  field_simp
  ring

/-- Woodford (2003), §5 and Ch. 7 (**the multiplier recursion**): components 1 and 2 give
`λ̂₁ − λ̂₁₋ = a(λ̄₁ − λ̄₄)π − ((1−α)a/c₀)(μ₋ + λ̄₄Δ̂₋) − ((c₀λ̄₁ − aλ̄₄)/b)r₇ + r₂
 − (1−α)r₁/(αc₀)`. -/
theorem red_l1_lag {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) :
    v 5 - vm 5 = aE p * (ramseyLam p R 0 - ramseyLam p R 3) * v 1 -
      (1 - p.α) * aE p / p.c0 * ((vm 5 + vm 6) + ramseyLam p R 3 * vm 4) -
      (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1) *
        (DQr p R vm v + DNr p R vn) 7 + (DQr p R vm v + DNr p R vn) 2 -
      (1 - p.α) / (p.α * p.c0) * (DQr p R vm v + DNr p R vn) 1 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have hL : ramseyLam p R 1 = -ramseyLam p R 0 := by simp [ramseyLam]
  have hL3 : ramseyLam p R 2 = (aE p * ramseyLam p R 3 - p.c0 * ramseyLam p R 0) / (p.θ - 1) := by
    simp [ramseyLam]
  simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val]
  rw [hL, hL3]
  field_simp
  unfold aE Par.c0
  ring

/-- Woodford (2003), Ch. 7, (1.17) (**the targeting rule of the exact linearisation**): with the
output condition `r₀₋` at the previous node, `A_uG(ŷ − ŷ₋) + A_uGθπ` equals the forcing from
`r₀, r₀₋, r₁, r₂, r₇` and the predetermined block (`Δ̂, μ` and their lags): the optimal
commitment `π + (λ_x/κ)(ŷ − ŷ₋) = ⋯` with `λ_x = κ/θ`, for every distortion `Φ`. -/
theorem red_target {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ) (r0m : ℝ)
    (h0m : -(R.Au * Gw p R * vm 0) - (1 - R.Φ) * R.Au * vm 4 +
      (1 - p.α * p.β) * (p.σ + p.ω) * vm 5 - (1 - p.α * p.β) * (1 + p.ω) * (vm 5 + vm 6) = r0m) :
    R.Au * Gw p R * (v 0 - vm 0) + R.Au * Gw p R * p.θ * v 1 =
      (1 - p.α * p.β) * (p.σ + p.ω) * (-((1 - p.α) * aE p / p.c0 *
        ((vm 5 + vm 6) + ramseyLam p R 3 * vm 4)) -
        (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1) *
          (DQr p R vm v + DNr p R vn) 7 + (DQr p R vm v + DNr p R vn) 2 -
        (1 - p.α) / (p.α * p.c0) * (DQr p R vm v + DNr p R vn) 1) -
      ((DQr p R vm v + DNr p R vn) 0 - r0m) - (1 - R.Φ) * R.Au * (v 4 - vm 4) -
      (1 - p.α * p.β) * (1 + p.ω) * ((v 5 + v 6) - (vm 5 + vm 6)) := by
  have e := red_l1 R hp vm v vn
  have lag := red_l1_lag R hp vm v vn
  have key := key_theta R hp
  linear_combination (-1 : ℝ) * e + h0m + (1 - p.α * p.β) * (p.σ + p.ω) * lag - v 1 * key

/-- Woodford (2003), Ch. 7, §1–2 (**the exact linearisation IS the commitment system**): at a
node where all nine linearised conditions hold with zero forcing, the previous node's output
condition holds, and the expected price-index residual vanishes, the 9×9 system reduces to
`Δ̂ = αΔ̂₋`, `μ = αμ₋` (the predetermined block), the NKPC `π = κŷ + βπⁿ` and the targeting
rule `A_uG(ŷ − ŷ₋ + θπ) = (1−α)[A_v Δ̂₋ + (1−αβ)(1+ω)μ₋ − (1−αβ)(σ+ω)(a/c₀)(μ₋ + λ̄₄Δ̂₋)]`,
whose characteristic polynomial is `βz² − (1+β+κθ)z + 1` (`ramsey_root_condition`). -/
theorem commitment_system {p : Par} (R : RPar) (hp : p.Std) (vm v vn : Fin 9 → ℝ)
    (h : DQr p R vm v + DNr p R vn = 0)
    (h0m : -(R.Au * Gw p R * vm 0) - (1 - R.Φ) * R.Au * vm 4 +
      (1 - p.α * p.β) * (p.σ + p.ω) * vm 5 - (1 - p.α * p.β) * (1 + p.ω) * (vm 5 + vm 6) = 0)
    (h7n : p.α * (p.θ - 1) * vn 1 - (1 - p.α) * (p.θ - 1) * ((vn 3 - vn 2) / p.c0) = 0) :
    v 4 = p.α * vm 4 ∧ v 5 + v 6 = p.α * (vm 5 + vm 6) ∧ v 1 = p.κ * v 0 + p.β * vn 1 ∧
      R.Au * Gw p R * (v 0 - vm 0 + p.θ * v 1) = (1 - p.α) * ((1 - R.Φ) * R.Au * vm 4 +
        (1 - p.α * p.β) * (1 + p.ω) * (vm 5 + vm 6) - (1 - p.α * p.β) * (p.σ + p.ω) *
          (aE p / p.c0) * ((vm 5 + vm 6) + ramseyLam p R 3 * vm 4)) := by
  have hr : ∀ i, (DQr p R vm v + DNr p R vn) i = 0 := fun i => congrFun h i
  have hD := red_D R hp vm v vn
  have hμ := red_mu R hp vm v vn
  have hpc := red_pc R hp vm v vn
  have ht := red_target R hp vm v vn 0 h0m
  simp only [hr, h7n, mul_zero, add_zero, sub_zero, zero_div, sub_self] at hD hμ hpc ht
  refine ⟨hD, hμ, hpc, ?_⟩
  rw [hD, hμ] at ht
  linear_combination ht

end Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyLin
