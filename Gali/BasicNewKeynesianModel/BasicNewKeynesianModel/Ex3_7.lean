/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Exercise 3.7: technology shocks and the Taylor rule

Galí (2015), Chapter 3, Exercise 3.7, pp. 95–96. Log utility (`σ = 1`),
technology `Y = A N`, constant desired markups, Calvo pricing.

* (a) `natural_output_levels`, `natural_output`: `yⁿ_t = a_t − μ/(1 + φ)`.
* The dynamic IS equation in gaps (`gap_dis`), with the natural rate
  `rⁿ_t = ρ + E_t a_{t+1} − a_t`; under a random walk `rⁿ = ρ`
  (`naturalRate_randomWalk`), under an AR(1) `rⁿ = ρ − (1 − ρₐ) a`
  (`naturalRate_ar1`). The DIS (41) as printed (with `ρ`) is valid only in
  the random-walk case.
* `solves_of_model`, `schurStable_iff`, `determinate_iff_taylor`: with the rule
  (43), the system `x_t = A E_t x_{t+1} + w_t` is determinate iff `φ_π > 1`.
* (b) `randomWalk_equilibrium`: with a random-walk technology and `φ_π > 1`,
  `ỹ = π = 0` is the unique bounded equilibrium, so `y = yⁿ` and `i = ρ`.
* (c) `ar1_equilibrium`, `ar1_signs`: with `a` an AR(1), `ρₐ < 1`, the
  unique bounded equilibrium is the minimum-state-variable solution
  `ỹ = −(1 − ρₐ)(1 − βρₐ) Λ a`, `π = −(1 − ρₐ) κ Λ a`,
  `Λ = 1/((1 − βρₐ)(1 − ρₐ) + κ(φ_π − ρₐ)) > 0`: a positive technology shock
  opens a negative gap and lowers inflation, and output rises by less than
  natural output.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_7

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) Natural output -/

/-- **Natural output in levels** (Galí (2015), Ex. 3.7(a), p. 96): with flexible
prices `P = M W/A` (`M > 0` the desired gross markup), labour supply
`W/P = C N^φ` (log utility), `C = Y` and `Y = A N`, employment is
`N = M^{−1/(1+φ)}` and `log Y = log A − log M/(1 + φ)` exactly. -/
theorem natural_output_levels {φ M P W A C Y Nl : ℝ} (hφ : 0 ≤ φ) (hM : 0 < M) (hP : 0 < P)
    (hA : 0 < A) (hN : 0 < Nl) (hflex : P = M * (W / A)) (hls : W / P = C * Nl ^ φ)
    (hc : C = Y) (hy : Y = A * Nl) :
    Real.log Y = Real.log A - Real.log M / (1 + φ) := by
  have hWA : 0 < W / A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hA
    rwa [div_mul_cancel₀ W hA.ne'] at this
  have hW : W / P = A / M := by
    rw [hflex]; field_simp
  rw [hW, hc, hy] at hls
  have h1 := congrArg Real.log hls
  rw [Real.log_div hA.ne' hM.ne', Real.log_mul (mul_pos hA hN).ne'
    (Real.rpow_pos_of_pos hN φ).ne', Real.log_rpow hN, Real.log_mul hA.ne' hN.ne'] at h1
  rw [hy, Real.log_mul hA.ne' hN.ne', eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff
    (by linarith)]
  linear_combination -h1

/-- **Natural output in logs** (Galí (2015), Ex. 3.7(a), p. 96): flexible prices
`p = μ + w − a`, labour supply `w − p = c + φ n`, `c = y`, `n = y − a` give
`yⁿ = a − μ/(1 + φ)`: natural output moves one-for-one with technology. -/
theorem natural_output {φ μ p w a y n c : ℝ} (hφ : 0 ≤ φ) (hflex : p = μ + (w - a))
    (hls : w - p = c + φ * n) (hc : c = y) (hn : n = y - a) : y = a - μ / (1 + φ) := by
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff h1]
  subst hc hn
  linear_combination -hls - hflex

/-! ### The dynamic IS equation in gaps and the natural rate -/

/-- The natural rate of interest with log utility, `rⁿ_t = ρ + E_t a_{t+1} − a_t`
(Galí (2015), eq. (24), p. 63, with `σ = 1`, `ψ_ya = 1`). -/
noncomputable def naturalRate (ρ : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + 𝔼.E t (a (t + 1)) - a t

/-- **The DIS in gaps** (Galí (2015), Ex. 3.7, eq. (41), p. 95, and eq. (23)): the
consumption Euler equation `y_t = E_t y_{t+1} − (i_t − E_t π_{t+1} − ρ)` with
`y = ỹ + yⁿ` and `yⁿ = a − const` gives
`ỹ_t = E_t ỹ_{t+1} − (i_t − E_t π_{t+1} − rⁿ_t)`. -/
theorem gap_dis {ρ c0 : ℝ} {y ytil yn a i infl : ℕ → Ω → ℝ}
    (heuler : ∀ t, y t = 𝔼.E t (y (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ))
    (hy : ∀ t, y t = ytil t + yn t) (hyn : ∀ t, yn t = a t - fun _ => c0) (t : ℕ) :
    ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - naturalRate 𝔼 ρ a t) := by
  have h := heuler t
  rw [hy, hy, hyn, hyn, map_add, map_sub, 𝔼.const] at h
  unfold naturalRate
  funext ω
  have h' := congrFun h ω
  simp only [Pi.add_apply, Pi.sub_apply] at h' ⊢
  linarith

/-- **Random-walk technology: a constant natural rate** (Galí (2015),
Ex. 3.7(b), p. 96): if `E_t a_{t+1} = a_t` then `rⁿ_t = ρ`. -/
theorem naturalRate_randomWalk {ρ : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 1 a) (t : ℕ) :
    naturalRate 𝔼 ρ a t = fun _ => ρ := by
  unfold naturalRate
  rw [ha.2 t, one_smul, add_sub_cancel_right]

/-- **AR(1) technology: a moving natural rate** (Galí (2015), Ex. 3.7(c),
p. 96): if `E_t a_{t+1} = ρₐ a_t` then `rⁿ_t = ρ − (1 − ρₐ) a_t`. -/
theorem naturalRate_ar1 {ρ ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    naturalRate 𝔼 ρ a t = (fun _ => ρ) - (1 - ρa) • a t := by
  unfold naturalRate
  rw [ha.2 t, sub_smul, one_smul]
  abel

/-! ### The system under the rule (43) -/

/-- `Ω = 1/(1 + κ φ_π)` (Galí (2015), eq. (27), p. 65, with `σ = 1`, `φ_y = 0`). -/
noncomputable def coefOmega (κ φπ : ℝ) : ℝ := 1 / (1 + κ * φπ)

/-- The matrix `A_T` of (27) with `σ = 1`, `φ_y = 0` (Galí (2015), p. 65):
`Ω [[1, 1 − βφ_π], [κ, κ + β]]`. -/
noncomputable def AT (β κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![coefOmega κ φπ, coefOmega κ φπ * (1 - β * φπ);
    coefOmega κ φπ * κ, coefOmega κ φπ * (κ + β)]

/-- The forcing term `B_T u_t = Ω [1, κ] u_t` (Galí (2015), eq. (27), p. 65). -/
noncomputable def forcing (κ φπ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![coefOmega κ φπ • u t, (coefOmega κ φπ * κ) • u t]

/-- The state vector `x_t = (ỹ_t, π_t)` (Galí (2015), eq. (27)). -/
def stack (ytil infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ytil t, infl t]

/-- **The model as a two-variable system** (Galí (2015), eq. (27), p. 65). If
`ỹ_t = E_t ỹ_{t+1} − (φ_π π_t − E_t π_{t+1}) + u_t` (the DIS with the rule (43)
substituted, `u = rⁿ − ρ`) and `π_t = β E_t π_{t+1} + κ ỹ_t` (42), then
`x_t = A_T E_t x_{t+1} + B_T u_t`. -/
theorem solves_of_model {β κ φπ : ℝ} (hΩ : 1 + κ * φπ ≠ 0) {ytil infl u : ℕ → Ω → ℝ}
    (hdis : ∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (φπ • infl t - 𝔼.E t (infl (t + 1))) + u t)
    (hpc : ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) :
    𝔼.Solves (AT β κ φπ) (forcing κ φπ u) (stack ytil infl) := by
  intro t i
  fin_cases i
  · funext ω
    have h1 := congrFun (hdis t) ω
    have h2 := congrFun (hpc t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    simp only [stack, forcing, AT, coefOmega, Fin.zero_eta, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h1 - φπ * h2
  · funext ω
    have h1 := congrFun (hdis t) ω
    have h2 := congrFun (hpc t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    simp only [stack, forcing, AT, coefOmega, Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination κ * h1 + h2

/-- The trace of `A_T`: `Ω(1 + κ + β)` (Galí (2015), p. 65). -/
theorem tr2_AT (β κ φπ : ℝ) : tr2 (AT β κ φπ) = coefOmega κ φπ * (1 + κ + β) := by
  simp [tr2, AT]
  ring

/-- The determinant of `A_T`: `β Ω` (Galí (2015), p. 65). -/
theorem det2_AT {β κ φπ : ℝ} (hΩ : 1 + κ * φπ ≠ 0) :
    det2 (AT β κ φπ) = β * coefOmega κ φπ := by
  simp [det2, AT, coefOmega]
  field_simp
  ring

/-- **Determinacy condition for the rule (43)** (Galí (2015), Ex. 3.7(b), p. 96;
eq. (28) with `φ_y = 0`): for `0 < β < 1`, `κ > 0` and `φ_π ≥ 0`, `A_T`
satisfies the Schur–Cohn condition if and only if `φ_π > 1`. -/
theorem schurStable_iff {β κ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 ≤ φπ) : SchurStable (tr2 (AT β κ φπ)) (det2 (AT β κ φπ)) ↔ 1 < φπ := by
  have hD : 0 < 1 + κ * φπ := by positivity
  rw [tr2_AT, det2_AT hD.ne']
  have hΩ : 0 < coefOmega κ φπ := by unfold coefOmega; positivity
  have hΩ1 : coefOmega κ φπ ≤ 1 := by
    unfold coefOmega; rw [div_le_one hD]; nlinarith
  have hΩe : coefOmega κ φπ * (1 + κ * φπ) = 1 := by unfold coefOmega; field_simp
  unfold SchurStable
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  constructor
  · rintro ⟨-, h⟩
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    exact ⟨by nlinarith, by nlinarith⟩

/-- **Determinacy iff `φ_π > 1`** (Galí (2015), Ex. 3.7(b), p. 96): bounded
adapted solutions of the system are unique exactly when `φ_π > 1`. -/
theorem determinate_iff_taylor [Nonempty Ω] {β κ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hφ : 0 ≤ φπ) : 𝔼.Determinate (AT β κ φπ) ↔ 1 < φπ := by
  rw [𝔼.determinate_iff, schurStable_iff hβ0 hβ1 hκ hφ]

/-- The DIS with the rule (43) substituted (Galí (2015), Ex. 3.7(b)):
`i = ρ + φ_π π` turns (41) into `ỹ_t = E_t ỹ_{t+1} − (φ_π π_t − E_t π_{t+1}) + (rⁿ_t − ρ)`. -/
theorem dis_with_rule {ρ φπ : ℝ} {ytil infl i rn : ℕ → Ω → ℝ}
    (hdis : ∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - rn t))
    (hrule : ∀ t, i t = (fun _ => ρ) + φπ • infl t) (t : ℕ) :
    ytil t = 𝔼.E t (ytil (t + 1)) - (φπ • infl t - 𝔼.E t (infl (t + 1)))
      + (rn t - fun _ => ρ) := by
  rw [hdis t, hrule t]
  abel

/-! ### (b) Random-walk technology -/

/-- **The equilibrium under a random walk** (Galí (2015), Ex. 3.7(b), p. 96).
With `rⁿ = ρ` (random-walk technology), the rule `i = ρ + φ_π π` with
`φ_π > 1`, the DIS (41) and the NKPC (42): (i) `ỹ = π = 0`, `i = ρ` is an
equilibrium; (ii) every bounded adapted equilibrium has `ỹ = π = 0`, hence
output equals natural output, `y = yⁿ = a − μ/(1 + φ)`, and `i = ρ`. -/
theorem randomWalk_equilibrium {ρ β κ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 1 < φπ) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 1 a) :
    ((∀ t, (0 : Ω → ℝ) = 𝔼.E t 0 - ((fun _ => ρ) - 𝔼.E t 0 - naturalRate 𝔼 ρ a t)) ∧
      ∀ t, (0 : Ω → ℝ) = β • 𝔼.E t 0 + κ • (0 : Ω → ℝ)) ∧
    ∀ ytil infl i : ℕ → Ω → ℝ,
      (∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - naturalRate 𝔼 ρ a t)) →
      (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) →
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) →
      𝔼.Adapted ytil → 𝔼.Adapted infl → BoundedProc ytil → BoundedProc infl →
      ∀ t, ytil t = 0 ∧ infl t = 0 ∧ i t = fun _ => ρ := by
  have hrn := naturalRate_randomWalk 𝔼 (ρ := ρ) ha
  refine ⟨⟨fun t => ?_, fun t => by simp⟩, ?_⟩
  · rw [hrn t, map_zero]; funext ω; simp
  intro ytil infl i hdis hpc hrule hya hia ⟨M₁, hM₁⟩ ⟨M₂, hM₂⟩ t
  have hD : 1 + κ * φπ ≠ 0 := by nlinarith
  have hsys := solves_of_model 𝔼 hD (u := fun t => naturalRate 𝔼 ρ a t - fun _ => ρ)
    (fun t => dis_with_rule 𝔼 hdis hrule t) hpc
  have hw : forcing κ φπ (fun t => naturalRate 𝔼 ρ a t - fun _ => ρ) = 0 := by
    funext s j
    simp only [forcing, hrn s, sub_self, smul_zero]
    fin_cases j <;> rfl
  rw [hw] at hsys
  have hz : 𝔼.Solves (AT β κ φπ) 0 (stack 0 0) := fun s j => by
    fin_cases j <;> simp [stack]
  have hS := (schurStable_iff hβ0 hβ1 hκ (by linarith)).mpr hφ
  have heq := 𝔼.system_unique hS hsys hz
    (fun s j => by fin_cases j <;> simp [stack, hya s, hia s])
    (fun s j => by fin_cases j <;> simp [stack])
    ⟨max M₁ M₂, fun s j ω => by
      fin_cases j
      · exact (hM₁ s ω).trans (le_max_left _ _)
      · exact (hM₂ s ω).trans (le_max_right _ _)⟩
    ⟨0, fun s j ω => by fin_cases j <;> simp [stack]⟩
  have hy : ytil t = 0 := congrFun (congrFun heq t) 0
  have hi : infl t = 0 := congrFun (congrFun heq t) 1
  refine ⟨hy, hi, ?_⟩
  rw [hrule t, hi, smul_zero, add_zero]

/-! ### (c) AR(1) technology -/

/-- `Λ = 1/((1 − βρₐ)(1 − ρₐ) + κ(φ_π − ρₐ))` (Galí (2015), eq. (29)–(30), p. 66,
with `σ = 1`, `φ_y = 0`). -/
noncomputable def lam (β κ φπ ρa : ℝ) : ℝ := 1 / ((1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa))

/-- `Λ > 0` when `φ_π > 1 > ρₐ` (Galí (2015), Ex. 3.7(c)). -/
theorem lam_pos {β κ φπ ρa : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 1 < φπ)
    (hρ1 : ρa < 1) : 0 < lam β κ φπ ρa := by
  unfold lam
  have : 0 < 1 - β * ρa := by nlinarith
  have : 0 < 1 - ρa := by linarith
  have : 0 < φπ - ρa := by linarith
  positivity

/-- **The equilibrium under AR(1) technology** (Galí (2015), Ex. 3.7(c), p. 96).
With `E_t a_{t+1} = ρₐ a_t`, `ρₐ < 1` (the book has `ρₐ ∈ (0,1)`), `a` bounded, and `φ_π > 1`:
(i) `ỹ = −(1 − ρₐ)(1 − βρₐ) Λ a`, `π = −(1 − ρₐ) κ Λ a`, `i = ρ + φ_π π` is an
equilibrium; (ii) it is the only bounded adapted one. -/
theorem ar1_equilibrium {ρ β κ φπ ρa : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 1 < φπ) (hρ1 : ρa < 1) {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hab : BoundedProc a) :
    let ys : ℕ → Ω → ℝ := fun t => (-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa) • a t
    let ps : ℕ → Ω → ℝ := fun t => (-(1 - ρa) * κ * lam β κ φπ ρa) • a t
    ((∀ t, ys t = 𝔼.E t (ys (t + 1))
        - (((fun _ => ρ) + φπ • ps t) - 𝔼.E t (ps (t + 1)) - naturalRate 𝔼 ρ a t)) ∧
      ∀ t, ps t = β • 𝔼.E t (ps (t + 1)) + κ • ys t) ∧
    ∀ ytil infl i : ℕ → Ω → ℝ,
      (∀ t, ytil t = 𝔼.E t (ytil (t + 1)) - (i t - 𝔼.E t (infl (t + 1)) - naturalRate 𝔼 ρ a t)) →
      (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) →
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) →
      𝔼.Adapted ytil → 𝔼.Adapted infl → BoundedProc ytil → BoundedProc infl →
      ytil = ys ∧ infl = ps := by
  intro ys ps
  have hrn := naturalRate_ar1 𝔼 (ρ := ρ) ha
  have hL := lam_pos hβ0 hβ1 hκ hφ hρ1
  have hLe : lam β κ φπ ρa * ((1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa)) = 1 := by
    have : 0 < 1 - β * ρa := by nlinarith
    have : 0 < 1 - ρa := by linarith
    have : 0 < φπ - ρa := by linarith
    have hX : 0 < (1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa) := by positivity
    unfold lam
    rw [one_div, inv_mul_cancel₀ hX.ne']
  have hEys : ∀ t, 𝔼.E t (ys (t + 1)) = ρa • ys t := fun t => by
    simp only [ys, map_smul, ha.2 t, smul_smul, mul_comm]
  have hEps : ∀ t, 𝔼.E t (ps (t + 1)) = ρa • ps t := fun t => by
    simp only [ps, map_smul, ha.2 t, smul_smul, mul_comm]
  have hmsv1 : ∀ t, ys t = 𝔼.E t (ys (t + 1))
      - (((fun _ => ρ) + φπ • ps t) - 𝔼.E t (ps (t + 1)) - naturalRate 𝔼 ρ a t) := by
    intro t
    rw [hEys, hEps, hrn]
    funext ω
    simp only [ys, ps, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(1 - ρa) * a t ω) * hLe
  have hmsv2 : ∀ t, ps t = β • 𝔼.E t (ps (t + 1)) + κ • ys t := by
    intro t
    rw [hEps]
    funext ω
    simp only [ys, ps, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨⟨hmsv1, hmsv2⟩, ?_⟩
  intro ytil infl i hdis hpc hrule hya hia ⟨M₁, hM₁⟩ ⟨M₂, hM₂⟩
  obtain ⟨Ma, hMa⟩ := hab
  have hD : 1 + κ * φπ ≠ 0 := by nlinarith
  set u : ℕ → Ω → ℝ := fun t => naturalRate 𝔼 ρ a t - fun _ => ρ with hu
  have hsys := solves_of_model 𝔼 hD (u := u) (fun t => dis_with_rule 𝔼 hdis hrule t) hpc
  have hsys' := solves_of_model 𝔼 hD (u := u) (ytil := ys) (infl := ps)
    (fun t => by
      have := hmsv1 t
      rw [this]
      funext ω
      simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring) hmsv2
  have hS := (schurStable_iff hβ0 hβ1 hκ (by linarith)).mpr hφ
  have hya' : 𝔼.Adapted ys := fun t => by simp only [ys, map_smul, ha.1 t]
  have hpa' : 𝔼.Adapted ps := fun t => by simp only [ps, map_smul, ha.1 t]
  have heq := 𝔼.system_unique hS hsys hsys'
    (fun s j => by fin_cases j <;> simp [stack, hya s, hia s])
    (fun s j => by fin_cases j <;> simp [stack, hya' s, hpa' s])
    ⟨max M₁ M₂, fun s j ω => by
      fin_cases j
      · exact (hM₁ s ω).trans (le_max_left _ _)
      · exact (hM₂ s ω).trans (le_max_right _ _)⟩
    ⟨(|-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa| + |-(1 - ρa) * κ * lam β κ φπ ρa|) * Ma,
      fun s j ω => by
        have h1 := abs_nonneg (-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa)
        have h2 := abs_nonneg (-(1 - ρa) * κ * lam β κ φπ ρa)
        have hMa0 : 0 ≤ Ma := (abs_nonneg _).trans (hMa 0 ω)
        fin_cases j
        · change |(-(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa) * a s ω| ≤ _
          rw [abs_mul]
          nlinarith [hMa s ω, abs_nonneg (a s ω)]
        · change |(-(1 - ρa) * κ * lam β κ φπ ρa) * a s ω| ≤ _
          rw [abs_mul]
          nlinarith [hMa s ω, abs_nonneg (a s ω)]⟩
  exact ⟨funext fun t => congrFun (congrFun heq t) 0, funext fun t => congrFun (congrFun heq t) 1⟩

/-- **Signs of the responses** (Galí (2015), Ex. 3.7(c), p. 96): the output-gap
and inflation coefficients on `a` are negative, and the output coefficient
`1 − (1 − ρₐ)(1 − βρₐ)Λ = κ(φ_π − ρₐ)Λ` lies in `(0, 1)`: output rises by less
than its natural level after a positive technology shock, unlike in (b). -/
theorem ar1_signs {β κ φπ ρa : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 1 < φπ)
    (hρ1 : ρa < 1) :
    -(1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa < 0 ∧ -(1 - ρa) * κ * lam β κ φπ ρa < 0 ∧
      1 - (1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa = κ * (φπ - ρa) * lam β κ φπ ρa ∧
      0 < κ * (φπ - ρa) * lam β κ φπ ρa ∧ κ * (φπ - ρa) * lam β κ φπ ρa < 1 := by
  have hL := lam_pos hβ0 hβ1 hκ hφ hρ1
  have h1 : 0 < 1 - β * ρa := by nlinarith
  have h2 : 0 < 1 - ρa := by linarith
  have h3 : 0 < φπ - ρa := by linarith
  have hLe : lam β κ φπ ρa * ((1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa)) = 1 := by
    have hX : 0 < (1 - β * ρa) * (1 - ρa) + κ * (φπ - ρa) := by positivity
    unfold lam
    rw [one_div, inv_mul_cancel₀ hX.ne']
  refine ⟨?_, ?_, ?_, by positivity, ?_⟩
  · have : 0 < (1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa := by positivity
    linarith
  · have : 0 < (1 - ρa) * κ * lam β κ φπ ρa := by positivity
    linarith
  · linear_combination -hLe
  · have : 0 < (1 - ρa) * (1 - β * ρa) * lam β κ φπ ρa := by positivity
    nlinarith

end Gali.BasicNewKeynesianModel.Ex3_7
