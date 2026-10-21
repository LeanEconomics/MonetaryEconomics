/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.Habit
import PolicyResponseDynamics.ExpectationsFiniteTree

/-!
# Necessity of the Blanchard–Kahn condition in the habit model

Woodford (2003), *Interest and Prices*, Chapter 5, §1.2, pp. 334–336 ((1.25), (1.26), (1.30) and
the solution form (1.31)–(1.33): "whenever the response coefficients of the monetary policy rule
are in the range that implies determinacy"), with Appendix D, §D.1. The module `Habit` proves
that the exact Blanchard–Kahn condition `BKCondition` is sufficient (`habit_existsUnique`); this
module proves that it is necessary, states it in the structural parameters, and so identifies
the range the book leaves implicit. All results hold for an arbitrary `ExpectationSystem`.

## Main results

* The characteristic quartic `Q(μ) = (1 − βμ) X_IS(μ) − (φ_π − μ) X_AS(μ)` (`habQ`,
  `habCoef`, `habQ_structural`); `Q(1)` is the Taylor-principle expression (`habQ_one`, and
  `habQ_one_kappa` with the book's `κ`, `δ` of (1.28)–(1.29)).
* The condition in the structural parameters (`HabitRootCond`): `Q` has exactly one root in the
  closed unit disc, counted with multiplicity, and it lies inside (a real root `λ`, `|λ| < 1`,
  with the cubic quotient `R_λ = Q/(μ − λ)` (`synth`) nonvanishing on the closed disc).
* `bk_of_rootCond`: `HabitRootCond` gives `BKCondition` (`decomp_of_root`, `bkOmega`, and
  `resM_det`: `φ det(M − μN) = R_λ(μ)`); `habit_bk_iff`: the two are equivalent.
* **The exact theorem** `habit_determinate_iff` / `habit_determinate_iff_bk` (and
  `habit_determinate_iff_sigma` with `φ = [(1 − βη)σ]⁻¹`): for `0 < β < 1`, `φ ≠ 0`, any `η`
  (including the Ch. 4 limit `η = 0`), `x̄` consistent with `π̄`, and any expectation system on a
  nonempty state space, there is a unique bounded equilibrium for every bounded disturbance and
  every bounded `x_{−1}` (`HabitDeterminate`) iff `HabitRootCond` iff `BKCondition`.
* Necessity in detail (`habit_failure`): if the condition fails, either
  - a root `±1` (`η ≠ 0`) gives non-existence for `r̂ⁿ_t = (±1)ᵗ − π̄` by resonance through the
    left eigenvector of the state-space matrix `A` (`nonexist_unitRoot`, `habA`, `habA_charpoly`:
    `det(μI − A) = −Q(μ)/(β²ηφ)`, `expSys_of_predSys`, `no_bounded_resonance`), or
  - no root in the closed disc gives non-existence for `x_{−1} ≠ x̄` (`nonexist_noRoot`), or
  - a real quadratic factor `μ² − Tμ + D` of `Q` with bounded mode gives a continuum of bounded
    equilibria (`habit_continuum`, `not_determinate_of_factor`, from the second-order modes
    `ar2_predSys`, `habit_add_mode`, `chSeq_bounded_of_distinct`, `chSeq_bounded_of_schur`).
* Too many stable roots (`HabitTwoStable`) ⇒ sunspot equilibria next to every equilibrium, for
  every disturbance and every expectation system (`habit_sunspots_of_twoStable`, `habit_sunspot`,
  `sunX`), genuinely stochastic on the coin-flip tree (`coin_sunspot`).
* The calibration of `bkCondition_calibration` satisfies the condition (`rootCond_calibration`,
  `determinate_calibration`); the passive rule `φ_π ≈ 0.70`, `φ_x ≈ 0.03` has the two stable roots
  `9/10`, `2/5` (`twoStable_passive`, `not_rootCond_passive`, `not_determinate_passive`) and an
  explicit coin-flip sunspot equilibrium (`sunspot_passive`); on the Taylor-principle boundary
  `φ_π = 1`, `φ_x = 0` a permanent unit natural-rate shock has no bounded equilibrium
  (`nonexist_boundary`, `not_rootCond_boundary`).
-/

namespace Woodford.PolicyResponseDynamics.HabitNecessity

open ForwardSystems Habit ComplexConjugate

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Real quartics: synthetic division and quadratic factors -/

/-- Woodford (2003), p. 335 (the characteristic polynomial of (1.30)–(1.33) is a quartic):
`c₄μ⁴ + c₃μ³ + c₂μ² + c₁μ + c₀` with real coefficients, evaluated at a complex `μ`. -/
noncomputable def quart (c : Fin 5 → ℝ) (μ : ℂ) : ℂ :=
  c 4 * μ ^ 4 + c 3 * μ ^ 3 + c 2 * μ ^ 2 + c 1 * μ + c 0

/-- Woodford (2003), p. 335 (tool): the cubic quotient of the quartic by `μ − λ` (synthetic
division). -/
noncomputable def synth (c : Fin 5 → ℝ) (lam μ : ℂ) : ℂ :=
  c 4 * μ ^ 3 + (c 3 + lam * c 4) * μ ^ 2 + (c 2 + lam * c 3 + lam ^ 2 * c 4) * μ +
    (c 1 + lam * c 2 + lam ^ 2 * c 3 + lam ^ 3 * c 4)

/-- Woodford (2003), p. 335 (tool): `Q(μ) = (μ − λ) R_λ(μ) + Q(λ)`. -/
theorem quart_eq_synth (c : Fin 5 → ℝ) (lam μ : ℂ) :
    quart c μ = (μ - lam) * synth c lam μ + quart c lam := by
  unfold quart synth
  ring

/-- Woodford (2003), p. 335 (tool): the linear coefficient of the remainder of the quartic on
division by `μ² − Tμ + D`. -/
def rem1 (c : Fin 5 → ℝ) (T D : ℝ) : ℝ :=
  c 1 + c 2 * T + c 3 * (T ^ 2 - D) + c 4 * (T ^ 3 - 2 * T * D)

/-- Woodford (2003), p. 335 (tool): the constant coefficient of the remainder of the quartic on
division by `μ² − Tμ + D`. -/
def rem0 (c : Fin 5 → ℝ) (T D : ℝ) : ℝ :=
  c 0 - c 2 * D - c 3 * T * D - c 4 * (T ^ 2 - D) * D

/-- Woodford (2003), p. 335 (tool): division of the quartic by `μ² − Tμ + D`. -/
theorem quart_eq_quadratic (c : Fin 5 → ℝ) (T D : ℝ) (μ : ℂ) :
    quart c μ = (μ ^ 2 - T * μ + D) * (c 4 * μ ^ 2 + (c 3 + c 4 * T) * μ +
      (c 2 + c 3 * T + c 4 * (T ^ 2 - D))) + rem1 c T D * μ + rem0 c T D := by
  unfold quart rem1 rem0
  push_cast
  ring

/-- Woodford (2003), p. 335 (tool): for `T = λ₁ + λ₂`, `D = λ₁λ₂` the remainder is
`R_{λ₁}(λ₂) μ + Q(λ₁) − λ₁ R_{λ₁}(λ₂)`. -/
theorem rem_of_roots (c : Fin 5 → ℝ) {T D : ℝ} {l1 l2 : ℂ} (hT : (T : ℂ) = l1 + l2)
    (hD : (D : ℂ) = l1 * l2) :
    (rem1 c T D : ℂ) = synth c l1 l2 ∧ (rem0 c T D : ℂ) = quart c l1 - l1 * synth c l1 l2 := by
  unfold rem1 rem0 synth quart
  push_cast
  rw [hT, hD]
  constructor <;> ring

/-- Woodford (2003), p. 335 (tool): if `λ₁` is a root and `R_{λ₁}(λ₂) = 0` (so `λ₂` is a further
root, counted with multiplicity), then `μ² − (λ₁ + λ₂)μ + λ₁λ₂` divides the quartic. -/
theorem rem_zero_of_roots (c : Fin 5 → ℝ) {T D : ℝ} {l1 l2 : ℂ} (hT : (T : ℂ) = l1 + l2)
    (hD : (D : ℂ) = l1 * l2) (h1 : quart c l1 = 0) (h2 : synth c l1 l2 = 0) :
    rem1 c T D = 0 ∧ rem0 c T D = 0 := by
  obtain ⟨e1, e0⟩ := rem_of_roots c hT hD
  rw [h1, h2] at e0
  rw [h2] at e1
  exact ⟨by exact_mod_cast e1, by exact_mod_cast (show (rem0 c T D : ℂ) = 0 by simpa using e0)⟩

/-- Woodford (2003), p. 335 (tool): a real quartic commutes with complex conjugation. -/
theorem quart_conj (c : Fin 5 → ℝ) (μ : ℂ) : quart c (conj μ) = conj (quart c μ) := by
  simp [quart, map_add, map_mul, map_pow, Complex.conj_ofReal]

/-! ### The characteristic quartic of the habit model -/

/-- **Woodford (2003), (1.25), (1.26), (1.30), p. 335: the characteristic quartic of the habit
model**, `Q(μ) = (1 − βμ) X_IS(μ) − (φ_π − μ) X_AS(μ)` (`habQ_structural`), with coefficients
`c₀, …, c₄` in the structural parameters `ξ_p, ω, φ, β, η, φ_π, φ_x`
(`φ = [(1 − βη)σ]⁻¹`, `vphiOf`). -/
noncomputable def habCoef (ξp ω vphi β η φπ φx : ℝ) : Fin 5 → ℝ :=
  ![-(η * vphi * (1 + ξp * φπ)),
    vphi * (1 + η + β * η + β * η ^ 2 + η * ξp) + ξp * φπ * (vphi + β * η ^ 2 * vphi + ω) + φx,
    -(vphi * (1 + β + 2 * β * η + β * η ^ 2 + β ^ 2 * η ^ 2)) -
      ξp * (vphi + ω + β * η ^ 2 * vphi + β * η * vphi * φπ) - β * φx,
    β * η * vphi * ξp + β * vphi * (1 + η + β * η + β * η ^ 2),
    -(β ^ 2 * η * vphi)]

/-- Woodford (2003), p. 335: `Q(μ)`, the characteristic quartic of the habit model. -/
noncomputable def habQ (ξp ω vphi β η φπ φx : ℝ) (μ : ℂ) : ℂ :=
  quart (habCoef ξp ω vphi β η φπ φx) μ

/-- **Woodford (2003), p. 335: the structural form of the characteristic quartic.**
`Q(μ) = (1 − βμ)[φβημ³ − φ(1 + βη + βη²)μ² + (φ(1 + η + βη²) + φ_x)μ − φη]
− (φ_π − μ) ξ_p[φβημ² − (ω + φ(1 + βη²))μ + φη]`: the determinant of the IS and AS rows on
`(π, x) = (A, B) μᵗ`, multiplied by `μ`. -/
theorem habQ_structural (ξp ω vphi β η φπ φx : ℝ) (μ : ℂ) :
    habQ ξp ω vphi β η φπ φx μ =
      (1 - β * μ) * (vphi * β * η * μ ^ 3 - vphi * (1 + β * η + β * η ^ 2) * μ ^ 2 +
        (vphi * (1 + η + β * η ^ 2) + φx) * μ - vphi * η) -
      (φπ - μ) * (ξp * (vphi * β * η * μ ^ 2 - (ω + vphi * (1 + β * η ^ 2)) * μ + vphi * η)) := by
  simp only [habQ, quart, habCoef, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

/-- **Woodford (2003), p. 335 (the root `μ = 1` and the Taylor principle).**
`Q(1) = (1 − β)φ_x + (φ_π − 1) ξ_p(ω + φ(1 − η)(1 − βη))`; `ξ_p(ω + φ(1 − η)(1 − βη))` is the
long-run slope of (1.26) (`XbarConsistent`), so `Q(1) = 0` exactly on the boundary
`φ_π + (1 − β)φ_x / [ξ_p(ω + φ(1 − η)(1 − βη))] = 1` of the Taylor principle. -/
theorem habQ_one (ξp ω vphi β η φπ φx : ℝ) :
    habQ ξp ω vphi β η φπ φx 1 =
      ((1 - β) * φx + (φπ - 1) * (ξp * (ω + vphi * (1 - η) * (1 - β * η))) : ℝ) := by
  rw [habQ_structural]
  push_cast
  ring

omit 𝔼 in
/-- **Woodford (2003), (1.27)–(1.29), p. 335: `Q(1)` in terms of the book's `κ` and `δ`.** With
`κ`, `δ` of (1.29), (1.28) (`habKappa`, `habDelta`; `β ≥ 0`, `ω ≥ 0`, `φ > 0`),
`Q(1) = (1 − β)φ_x + (φ_π − 1) κ(1 − δ)(1 − βδ)`; so the root `μ = 1` sits exactly on the
Taylor-principle boundary `φ_π + (1 − β)φ_x/[κ(1 − δ)(1 − βδ)] = 1`. -/
theorem habQ_one_kappa {ξp ω vphi β η φπ φx : ℝ} (hβ : 0 ≤ β) (hω : 0 ≤ ω) (hφ : 0 < vphi) :
    habQ ξp ω vphi β η φπ φx 1 =
      ((1 - β) * φx + (φπ - 1) * (habKappa ξp β ω vphi η * (1 - habDelta β ω vphi η) *
        (1 - β * habDelta β ω vphi η)) : ℝ) := by
  rw [habQ_one]
  congr 1
  have h1 := habKappa_mul_delta (ξp := ξp) (η := η) hβ hω hφ
  have h2 := habKappa_mul (ξp := ξp) (η := η) hβ hω hφ
  linear_combination (φπ - 1) * ((1 + β) * h1 - h2)

/-! ### Second-order modes `E_t X_{t+1} = T X_t − D X_{t−1}` -/

/-- Woodford (2003), p. 335 (tool): `1 − βT + β²D = (1 − βλ₁)(1 − βλ₂)`. -/
noncomputable def arDen (β T D : ℝ) : ℝ := 1 - β * T + β ^ 2 * D

/-- Woodford (2003), (1.26), p. 334 (tool): along a mode `X`, inflation
`π_t = p X_t + q X_{t−1}` solves the AS relation; this is `p`. -/
noncomputable def arP (ξp ω vphi β η T D : ℝ) : ℝ :=
  (ξp * (ω + vphi * (1 + β * η ^ 2)) - ξp * vphi * β * η * T + β * (ξp * vphi * β * η) * D -
    β * (ξp * vphi * η)) / arDen β T D

/-- Woodford (2003), (1.26), p. 334 (tool): the coefficient `q` of `X_{t−1}` in the inflation
response to a mode. -/
noncomputable def arQ (ξp ω vphi β η T D : ℝ) : ℝ :=
  ξp * vphi * β * η * D - ξp * vphi * η - β * D * arP ξp ω vphi β η T D

/-- Woodford (2003), (1.26), p. 334 (tool): the `X_t` coefficient of the AS relation along a
mode vanishes. -/
theorem ar_row0_X {ξp ω vphi β η T D : ℝ} (hden : arDen β T D ≠ 0) :
    arP ξp ω vphi β η T D - ξp * (ω + vphi * (1 + β * η ^ 2)) + ξp * vphi * β * η * T -
      β * (arP ξp ω vphi β η T D * T + arQ ξp ω vphi β η T D) = 0 := by
  unfold arQ arP
  unfold arDen at hden ⊢
  field_simp
  ring

/-- Woodford (2003), (1.25), p. 333 (tool): the `X_t` coefficient of the IS relation along a mode,
times `1 − βT + β²D`, is `r₁ + β r₀`, the remainder of `Q` on division by `μ² − Tμ + D`. -/
theorem ar_row1_X {ξp ω vphi β η φπ φx T D : ℝ} (hden : arDen β T D ≠ 0) :
    (φπ * arP ξp ω vphi β η T D + (vphi * (1 + β * η ^ 2 + η) + φx) - vphi * β * η * T -
      (arP ξp ω vphi β η T D * T + arQ ξp ω vphi β η T D) - vphi * (1 + β * η ^ 2) * T +
      vphi * β * η * (T ^ 2 - D)) * arDen β T D =
      rem1 (habCoef ξp ω vphi β η φπ φx) T D + β * rem0 (habCoef ξp ω vphi β η φπ φx) T D := by
  unfold arQ arP rem1 rem0
  simp only [habCoef, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold arDen at hden ⊢
  field_simp
  ring

/-- Woodford (2003), (1.25), p. 333 (tool): the `X_{t−1}` coefficient of the IS relation along a
mode is `r₀ − βD` times the `X_t` coefficient. -/
theorem ar_row1_L {ξp ω vphi β η φπ φx T D : ℝ} (hden : arDen β T D ≠ 0) :
    φπ * arQ ξp ω vphi β η T D + vphi * β * η * D + arP ξp ω vphi β η T D * D +
      vphi * (1 + β * η ^ 2) * D - vphi * β * η * T * D - vphi * η =
      rem0 (habCoef ξp ω vphi β η φπ φx) T D - β * D *
        (φπ * arP ξp ω vphi β η T D + (vphi * (1 + β * η ^ 2 + η) + φx) - vphi * β * η * T -
          (arP ξp ω vphi β η T D * T + arQ ξp ω vphi β η T D) - vphi * (1 + β * η ^ 2) * T +
          vphi * β * η * (T ^ 2 - D)) := by
  unfold arQ arP rem0
  simp only [habCoef, Matrix.cons_val, Matrix.cons_val_zero]
  unfold arDen at hden ⊢
  field_simp
  ring


/-- Woodford (2003), p. 335 (tool): the vector `z_t = (p X_t + q X_{t−1}, X_t, E_t X_{t+1})` of a
mode `X` (with `X_{−1} = 0`). -/
def modeZ (p q : ℝ) (X : ℕ → Ω → ℝ) : ℕ → Fin 3 → Ω → ℝ :=
  fun t => ![p • X t + q • lag 0 X t, X t, 𝔼.E t (X (t + 1))]

/-- **Woodford (2003), (1.25)–(1.26), p. 335: quadratic factors of `Q` give modes.** If
`μ² − Tμ + D` divides the characteristic quartic (`r₁ = r₀ = 0`) and `1 − βT + β²D ≠ 0`, then
for every adapted `X` with `X_{−1} = 0` and `E_t X_{t+1} = T X_t − D X_{t−1}` (deterministic or
driven by sunspot innovations), `x̂ = X`, `π̂ = p X_t + q X_{t−1}` solves the homogeneous
system (1.25), (1.26), (1.30): `P z_t = N E_t z_{t+1} + h s_t`, `s_{t+1} = x̂_t`. -/
theorem ar2_predSys {ξp ω vphi β η φπ φx T D : ℝ} (hφ : vphi ≠ 0) (hden : arDen β T D ≠ 0)
    (hr1 : rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    (hr0 : rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    {X : ℕ → Ω → ℝ} (hX : 𝔼.Adapted X)
    (hrec : ∀ t, 𝔼.E t (X (t + 1)) = T • X t - D • lag 0 X t) :
    PredSysN 𝔼 (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) (habBv vphi) habSel 0
      (fun _ => 0) (modeZ 𝔼 (arP ξp ω vphi β η T D) (arQ ξp ω vphi β η T D) X) (lag 0 X) := by
  set p := arP ξp ω vphi β η T D with hp
  set q := arQ ξp ω vphi β η T D with hq
  have hX2 : ∀ t, 𝔼.E t (X (t + 2)) = T • (T • X t - D • lag 0 X t) - D • X t := by
    intro t
    rw [← 𝔼.tower (Nat.le_succ t), hrec (t + 1), map_sub, map_smul, map_smul, hrec t]
    simp only [lag, hX t]
  have z0 : ∀ t y, modeZ 𝔼 p q X t 0 y = p * X t y + q * lag 0 X t y := fun t y => rfl
  have z1 : ∀ t y, modeZ 𝔼 p q X t 1 y = X t y := fun t y => rfl
  have z2 : ∀ t y, modeZ 𝔼 p q X t 2 y = T * X t y - D * lag 0 X t y := by
    intro t y
    change 𝔼.E t (X (t + 1)) y = _
    rw [hrec t]
    rfl
  have e0 : ∀ t y, 𝔼.E t (modeZ 𝔼 p q X (t + 1) 0) y =
      p * (T * X t y - D * lag 0 X t y) + q * X t y := by
    intro t y
    change 𝔼.E t (p • X (t + 1) + q • X t) y = _
    rw [map_add, map_smul, map_smul, hrec t, hX t]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have e1 : ∀ t y, 𝔼.E t (modeZ 𝔼 p q X (t + 1) 1) y = T * X t y - D * lag 0 X t y := by
    intro t y
    change 𝔼.E t (X (t + 1)) y = _
    rw [hrec t]
    rfl
  have e2 : ∀ t y, 𝔼.E t (modeZ 𝔼 p q X (t + 1) 2) y =
      T * (T * X t y - D * lag 0 X t y) - D * X t y := by
    intro t y
    change 𝔼.E t (𝔼.E (t + 1) (X (t + 1 + 1))) y = _
    rw [𝔼.tower (Nat.le_succ t), hX2 t]
    rfl
  have hA : p - ξp * (ω + vphi * (1 + β * η ^ 2)) + ξp * vphi * β * η * T - β * (p * T + q) = 0 :=
    ar_row0_X hden
  have hB : q - ξp * vphi * β * η * D + β * p * D + ξp * vphi * η = 0 := by
    rw [hq, arQ]
    ring
  have hE1 : φπ * p + (vphi * (1 + β * η ^ 2 + η) + φx) - vphi * β * η * T - (p * T + q) -
      vphi * (1 + β * η ^ 2) * T + vphi * β * η * (T ^ 2 - D) = 0 := by
    have h := ar_row1_X (φπ := φπ) (φx := φx) (ξp := ξp) (ω := ω) (vphi := vphi) (η := η) hden
    rw [hr1, hr0, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hden
  have hE2 : φπ * q + vphi * β * η * D + p * D + vphi * (1 + β * η ^ 2) * D -
      vphi * β * η * T * D - vphi * η = 0 := by
    have h := ar_row1_L (φπ := φπ) (φx := φx) (ξp := ξp) (ω := ω) (vphi := vphi) (η := η) hden
    rw [hr0, hE1] at h
    simpa using h
  refine ⟨fun t => ?_, fun t => ?_⟩
  · funext i y
    fin_cases i
    · simp only [Fin.zero_eta, Pi.add_apply, habP_row0, habN_row0, z0, z1, z2, e0, habH, habBv,
        Matrix.cons_val_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, add_zero]
      linear_combination X t y * hA + lag 0 X t y * hB
    · simp only [Fin.mk_one, Pi.add_apply, habP_row1, habN_row1, z0, z1, z2, e0, e1, e2, habH,
        habBv, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        mul_zero, add_zero]
      linear_combination (norm := skip) (vphi⁻¹ * X t y) * hE1 + (vphi⁻¹ * lag 0 X t y) * hE2
      field_simp
      ring
    · simp only [Fin.reduceFinMk, Pi.add_apply, habP_row2, habN_row2, habH, habBv,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, mul_zero, zero_mul, add_zero]
      rfl
  · funext y
    simp [habSel, Fin.sum_univ_three, lag, modeZ]

/-- Woodford (2003), (1.30)–(1.33), p. 335 (linearity): a solution plus a solution of the
homogeneous system (`g = 0`) is a solution. -/
theorem predSysN_add {n : ℕ} {P N : Matrix (Fin n) (Fin n) ℝ} {h b φ : Fin n → ℝ} {ρ : ℝ}
    {g : ℕ → Ω → ℝ} {z z' : ℕ → Fin n → Ω → ℝ} {s s' : ℕ → Ω → ℝ}
    (h1 : PredSysN 𝔼 P N h b φ ρ g z s) (h2 : PredSysN 𝔼 P N h b φ ρ (fun _ => 0) z' s') :
    PredSysN 𝔼 P N h b φ ρ g (fun t => z t + z' t) (fun t => s t + s' t) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · funext i y
    have a1 := congrFun (congrFun (h1.1 t) i) y
    have a2 := congrFun (congrFun (h2.1 t) i) y
    simp only [rvMul_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero,
      add_zero, map_add] at a1 a2 ⊢
    simp only [mul_add, Finset.sum_add_distrib]
    linear_combination a1 + a2
  · funext y
    have a1 := congrFun (h1.2 t) y
    have a2 := congrFun (h2.2 t) y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at a1 a2 ⊢
    simp only [mul_add, Finset.sum_add_distrib]
    linear_combination a1 + a2


/-- **Woodford (2003), (1.25), (1.26), (1.30), p. 335: equilibrium plus mode is an equilibrium.**
If `μ² − Tμ + D` divides the characteristic quartic and `1 − βT + β²D ≠ 0`, then adding to any
equilibrium `(π, x, î)` a mode `X` (adapted, `X_{−1} = 0`, `E_t X_{t+1} = T X_t − D X_{t−1}`)
with `π̂ = p X_t + q X_{t−1}` and the Taylor-rule response of `î` gives another equilibrium for the
same disturbances and the same `x_{−1}`. -/
theorem habit_add_mode {ξp ω vphi β η φπ φx πbar xbar T D : ℝ} (hφ : vphi ≠ 0)
    (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) (hden : arDen β T D ≠ 0)
    (hr1 : rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    (hr0 : rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    {xm1 : Ω → ℝ} {π x i ibar rn : ℕ → Ω → ℝ}
    (hmod : HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 π x i ibar rn) (hx : 𝔼.Adapted x)
    {X : ℕ → Ω → ℝ} (hX : 𝔼.Adapted X)
    (hrec : ∀ t, 𝔼.E t (X (t + 1)) = T • X t - D • lag 0 X t) :
    HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1
      (fun t => π t + (arP ξp ω vphi β η T D • X t + arQ ξp ω vphi β η T D • lag 0 X t))
      (fun t => x t + X t)
      (fun t => i t + (φπ • (arP ξp ω vphi β η T D • X t + arQ ξp ω vphi β η T D • lag 0 X t) +
        φx • X t)) ibar rn := by
  obtain ⟨hIS, hAS, hT⟩ := hmod
  set p := arP ξp ω vphi β η T D with hp
  set q := arQ ξp ω vphi β η T D with hq
  have h1 := (habit_iff_predSys 𝔼 hφ hxbar hx hT).mp ⟨hIS, hAS⟩
  have h2 := ar2_predSys 𝔼 (φπ := φπ) (φx := φx) hφ hden hr1 hr0 hX hrec
  have h3 := predSysN_add 𝔼 h1 h2
  have hT' : Taylor130 φπ φx πbar xbar (fun t => π t + (p • X t + q • lag 0 X t))
      (fun t => x t + X t) (fun t => i t + (φπ • (p • X t + q • lag 0 X t) + φx • X t)) ibar := by
    intro t
    dsimp only
    rw [hT t]
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hx' : 𝔼.Adapted (fun t => x t + X t) := fun t => by rw [map_add, hx t, hX t]
  have hV : habVec 𝔼 πbar xbar (fun t => π t + (p • X t + q • lag 0 X t)) (fun t => x t + X t) =
      fun t => habVec 𝔼 πbar xbar π x t + modeZ 𝔼 p q X t := by
    funext t j y
    fin_cases j
    · simp only [habVec, modeZ, Fin.zero_eta, Matrix.cons_val_zero, Pi.add_apply, Pi.sub_apply]
      ring
    · simp only [habVec, modeZ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.add_apply, Pi.sub_apply]
      ring
    · simp only [habVec, modeZ, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Pi.add_apply, Pi.sub_apply, map_add]
      ring
  have hS : habS xbar xm1 (fun t => x t + X t) = fun t => habS xbar xm1 x t + lag 0 X t := by
    funext t y
    cases t with
    | zero => simp [habS, lag]
    | succ t => simp only [habS, lag, Pi.add_apply, Pi.sub_apply]; ring
  have := (habit_iff_predSys 𝔼 hφ hxbar hx' hT').mpr (by rw [hV, hS]; exact h3)
  exact ⟨this.1, this.2, hT'⟩

/-! ### Bounded modes -/

omit 𝔼 in
/-- Woodford (2003), p. 335 (tool): `(r₁ − r₂) p_k = r₁^{k+1} − r₂^{k+1}` for the
Cayley–Hamilton sequence `p_k` of `z² − Tz + D` with roots `r₁, r₂`. -/
theorem chSeq_mul_sub {T D : ℝ} {r1 r2 : ℂ} (hT : (T : ℂ) = r1 + r2) (hD : (D : ℂ) = r1 * r2)
    (k : ℕ) : (r1 - r2) * (chSeq T D k : ℂ) = r1 ^ (k + 1) - r2 ^ (k + 1) := by
  have key : ∀ k, (r1 - r2) * (chSeq T D k : ℂ) = r1 ^ (k + 1) - r2 ^ (k + 1) ∧
      (r1 - r2) * (chSeq T D (k + 1) : ℂ) = r1 ^ (k + 2) - r2 ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
      simp only [chSeq, Complex.ofReal_one, hT]
      constructor <;> ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e : (chSeq T D (k + 1 + 1) : ℂ) = T * chSeq T D (k + 1) - D * chSeq T D k := by
        simp only [chSeq]
        push_cast
        ring
      rw [e, hT, hD]
      linear_combination (r1 + r2) * ih.2 - r1 * r2 * ih.1
  exact (key k).1

omit 𝔼 in
/-- Woodford (2003), p. 335 (tool): if the roots of `z² − Tz + D` are distinct and lie in the
closed unit disc, the sequence `p_0 = 1`, `p_{k+2} = T p_{k+1} − D p_k` is bounded by
`2/|r₁ − r₂|`. -/
theorem chSeq_bounded_of_distinct {T D : ℝ} {r1 r2 : ℂ} (hT : (T : ℂ) = r1 + r2)
    (hD : (D : ℂ) = r1 * r2) (hne : r1 ≠ r2) (h1 : ‖r1‖ ≤ 1) (h2 : ‖r2‖ ≤ 1) (k : ℕ) :
    |chSeq T D k| ≤ 2 / ‖r1 - r2‖ := by
  have hpos : 0 < ‖r1 - r2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have e := chSeq_mul_sub hT hD k
  have hn : ‖r1 - r2‖ * |chSeq T D k| = ‖r1 ^ (k + 1) - r2 ^ (k + 1)‖ := by
    rw [← e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [le_div_iff₀ hpos, mul_comm, hn]
  calc ‖r1 ^ (k + 1) - r2 ^ (k + 1)‖ ≤ ‖r1‖ ^ (k + 1) + ‖r2‖ ^ (k + 1) := by
        rw [← norm_pow, ← norm_pow]; exact norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (pow_le_one₀ (norm_nonneg _) h1) (pow_le_one₀ (norm_nonneg _) h2)
    _ = 2 := by norm_num

omit 𝔼 in
/-- Woodford (2003), p. 335 (tool): under the Schur–Cohn condition the Cayley–Hamilton sequence
is absolutely summable, with `|p_k| ≤ (k + 1)ρᵏ`, `ρ < 1`. -/
theorem chSeq_summable {T D : ℝ} (hS : SchurStable T D) : Summable fun k => |chSeq T D k| := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots T D).mp hS
  set ρ := max ‖root₁ T D‖ ‖root₂ T D‖
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt h1 h2
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have hsum : Summable fun k : ℕ => ((k : ℝ) + 1) * ρ ^ k := by
    have a := summable_pow_mul_geometric_of_norm_lt_one 1 hn
    have b := summable_geometric_of_lt_one hρ0 hρ1
    simpa [add_mul] using a.add b
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => abs_chSeq_le T D k) hsum

omit 𝔼 in
/-- Woodford (2003), p. 335 (tool): under the Schur–Cohn condition the Cayley–Hamilton sequence
is bounded. -/
theorem chSeq_bounded_of_schur {T D : ℝ} (hS : SchurStable T D) :
    ∃ M, ∀ k, |chSeq T D k| ≤ M :=
  ⟨∑' k, |chSeq T D k|, fun k => (chSeq_summable hS).le_tsum k (fun _ _ => abs_nonneg _)⟩

/-- Woodford (2003), p. 335: the deterministic mode `X_t = p_t` (`X_{−1} = 0`, `X_0 = 1`) solves
`E_t X_{t+1} = T X_t − D X_{t−1}` under every expectation system. -/
theorem chSeq_mode (T D : ℝ) (t : ℕ) :
    𝔼.E t ((fun s _ => chSeq T D s : ℕ → Ω → ℝ) (t + 1)) =
      T • (fun s _ => chSeq T D s : ℕ → Ω → ℝ) t - D • lag 0 (fun s _ => chSeq T D s) t := by
  rw [𝔼.const]
  funext y
  cases t with
  | zero => simp [chSeq, lag]
  | succ t => simp [chSeq, lag]

/-- Woodford (2003), p. 335 (sunspot modes): `X_t = ∑_{k ≤ t} p_{t−k} ε_k`, the solution of
`X_{t+1} = T X_t − D X_{t−1} + ε_{t+1}`, `X_0 = ε_0`, `X_{−1} = 0`, driven by sunspot
innovations `ε`. -/
noncomputable def sunX (T D : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range (t + 1), chSeq T D (t - k) • ε k

omit 𝔼 in
/-- Woodford (2003), p. 335: the sunspot mode obeys `X_{t+1} = T X_t − D X_{t−1} + ε_{t+1}`. -/
theorem sunX_succ (T D : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) :
    sunX T D ε (t + 1) = T • sunX T D ε t - D • lag 0 (sunX T D ε) t + ε (t + 1) := by
  cases t with
  | zero =>
    simp only [sunX, lag, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp [chSeq]
  | succ t =>
    simp only [sunX, lag]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1)]
    have hterm : ∑ k ∈ Finset.range (t + 1), chSeq T D (t + 1 + 1 - k) • ε k =
        T • ∑ k ∈ Finset.range (t + 1), chSeq T D (t + 1 - k) • ε k -
          D • ∑ k ∈ Finset.range (t + 1), chSeq T D (t - k) • ε k := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have e1 : t + 1 + 1 - k = (t - k) + 2 := by omega
      have e2 : t + 1 - k = (t - k) + 1 := by omega
      rw [e1, e2, smul_smul, smul_smul, ← sub_smul]
      congr 1
    rw [hterm]
    have e3 : t + 1 + 1 - (t + 1) = 1 := by omega
    rw [e3, Nat.sub_self, Nat.sub_self]
    simp only [chSeq, one_smul, smul_add]
    abel

/-- Woodford (2003), p. 335: the sunspot mode is adapted. -/
theorem sunX_adapted {T D : ℝ} {ε : ℕ → Ω → ℝ} (hε : 𝔼.Adapted ε) : 𝔼.Adapted (sunX T D ε) := by
  intro t
  simp only [sunX, map_sum, map_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [ForwardSolution.E_of_known 𝔼 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (hε k)]

/-- Woodford (2003), p. 335: with mean-zero innovations `E_t ε_{t+1} = 0`, the sunspot mode
satisfies `E_t X_{t+1} = T X_t − D X_{t−1}`. -/
theorem sunX_rec {T D : ℝ} {ε : ℕ → Ω → ℝ} (hε : 𝔼.Adapted ε)
    (hmz : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (t : ℕ) :
    𝔼.E t (sunX T D ε (t + 1)) = T • sunX T D ε t - D • lag 0 (sunX T D ε) t := by
  rw [sunX_succ, map_add, map_sub, map_smul, map_smul, hmz t, add_zero,
    sunX_adapted 𝔼 hε t, lag_known 𝔼 (map_zero _) (sunX_adapted 𝔼 hε) t]

omit 𝔼 in
/-- Woodford (2003), p. 335: under the Schur–Cohn condition the sunspot mode driven by bounded
innovations is bounded. -/
theorem sunX_bounded {T D : ℝ} (hS : SchurStable T D) {ε : ℕ → Ω → ℝ} (hε : BoundedProc ε) :
    BoundedProc (sunX T D ε) := by
  obtain ⟨M, hM⟩ := hε
  refine ⟨(∑' k, |chSeq T D k|) * M, fun t y => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 y)
  simp only [sunX, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc |∑ k ∈ Finset.range (t + 1), chSeq T D (t - k) * ε k y|
      ≤ ∑ k ∈ Finset.range (t + 1), |chSeq T D (t - k)| * M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM k y) (abs_nonneg _)
    _ = (∑ k ∈ Finset.range (t + 1), |chSeq T D k|) * M := by
        rw [← Finset.sum_mul]
        congr 1
        exact Finset.sum_range_reflect (fun k => |chSeq T D k|) (t + 1)
    _ ≤ (∑' k, |chSeq T D k|) * M := by
        gcongr
        exact (chSeq_summable hS).sum_le_tsum _ (fun _ _ => abs_nonneg _)


/-! ### The state-space form `E_t y_{t+1} = A y_t + w_t` -/

/-- **Woodford (2003), (1.30)–(1.33), p. 335: the state-space matrix of the habit model.** With
`y_t = (π̂_t, x̂_t, E_t x̂_{t+1}, x̂_{t−1})` (three non-predetermined variables and one
predetermined one), the system is `E_t y_{t+1} = A y_t + w_t` (`expSys_of_predSys`); `A` exists
because `det N = β²η ≠ 0`. -/
noncomputable def habA (ξp ω vphi β η φπ φx : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / β, -(ξp * (ω + vphi * (1 + β * η ^ 2))) / β, ξp * vphi * β * η / β, ξp * vphi * η / β;
    0, 0, 1, 0;
    (1 - β * φπ) / (β ^ 2 * η * vphi),
      (-(ξp * (ω + vphi * (1 + β * η ^ 2))) - β * (vphi * (1 + β * η ^ 2 + η) + φx)) /
        (β ^ 2 * η * vphi),
      (ξp * vphi * β * η + β * vphi * (1 + β * η ^ 2) + β ^ 2 * vphi * η) / (β ^ 2 * η * vphi),
      (ξp * vphi * η + β * vphi * η) / (β ^ 2 * η * vphi);
    0, 1, 0, 0]

/-- **Woodford (2003), p. 335: the eigenvalues of `A` are the roots of the quartic.**
`det(μI − A) = −Q(μ)/(β²ηφ)`. -/
theorem habA_charpoly {ξp ω vphi β η φπ φx : ℝ} (hβ : β ≠ 0) (hη : η ≠ 0) (hφ : vphi ≠ 0)
    (μ : ℂ) :
    (Matrix.scalar (Fin 4) μ - (habA ξp ω vphi β η φπ φx).map Complex.ofReal).det =
      -habQ ξp ω vphi β η φπ φx μ / (β ^ 2 * η * vphi) := by
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  have hφ' : (vphi : ℂ) ≠ 0 := by exact_mod_cast hφ
  rw [habQ_structural]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, habA, Matrix.scalar_apply]
  field_simp
  ring


/-- Woodford (2003), p. 335: the state vector `y_t = (z_{t,0}, z_{t,1}, z_{t,2}, s_t)`. -/
def habY (z : ℕ → Fin 3 → Ω → ℝ) (s : ℕ → Ω → ℝ) : ℕ → Fin 4 → Ω → ℝ :=
  fun t => ![z t 0, z t 1, z t 2, s t]

/-- Woodford (2003), p. 335: row 0 of `A y_t` (the AS relation solved for `E_t π_{t+1}`). -/
theorem habA_row0 (ξp ω vphi β η φπ φx : ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ)
    (y : Ω) : rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 0 y =
      (z t 0 y - ξp * (ω + vphi * (1 + β * η ^ 2)) * z t 1 y + ξp * vphi * β * η * z t 2 y +
        ξp * vphi * η * s t y) / β := by
  simp [rvMul_apply, habA, habY, Fin.sum_univ_four]
  ring

/-- Woodford (2003), p. 335: row 1 of `A y_t` (`E_t x_{t+1}` is the third variable). -/
theorem habA_row1 (ξp ω vphi β η φπ φx : ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ)
    (y : Ω) : rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 1 y = z t 2 y := by
  simp [rvMul_apply, habA, habY, Fin.sum_univ_four]

/-- Woodford (2003), p. 335: row 2 of `A y_t` (the IS relation solved for `E_t x_{t+2}`). -/
theorem habA_row2 (ξp ω vphi β η φπ φx : ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ)
    (y : Ω) : rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 2 y =
      ((1 - β * φπ) * z t 0 y +
        (-(ξp * (ω + vphi * (1 + β * η ^ 2))) - β * (vphi * (1 + β * η ^ 2 + η) + φx)) * z t 1 y +
        (ξp * vphi * β * η + β * vphi * (1 + β * η ^ 2) + β ^ 2 * vphi * η) * z t 2 y +
        (ξp * vphi * η + β * vphi * η) * s t y) / (β ^ 2 * η * vphi) := by
  simp [rvMul_apply, habA, habY, Fin.sum_univ_four]
  ring

/-- Woodford (2003), p. 335: row 3 of `A y_t` (`s_{t+1} = x̂_t`). -/
theorem habA_row3 (ξp ω vphi β η φπ φx : ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ)
    (y : Ω) : rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 3 y = z t 1 y := by
  simp [rvMul_apply, habA, habY, Fin.sum_univ_four]

/-- **Woodford (2003), (1.30)–(1.33), p. 335: the state-space form.** Every adapted solution of
the habit system `P z_t = N E_t z_{t+1} + h s_t + b g_t`, `s_{t+1} = z_{t,1}` satisfies
`E_t y_{t+1} = A y_t + w_t` with `w_t = (0, 0, g_t/(βηφ), 0)`. -/
theorem expSys_of_predSys {ξp ω vphi β η φπ φx : ℝ} (hβ : β ≠ 0) (hη : η ≠ 0) (hφ : vphi ≠ 0)
    {g : ℕ → Ω → ℝ} {z : ℕ → Fin 3 → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hsys : PredSysN 𝔼 (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) (habBv vphi)
      habSel 0 g z s) (hza : VAdapted 𝔼 z) :
    ExpSys 𝔼 (habA ξp ω vphi β η φπ φx) (fun t => ![0, 0, (β * η * vphi)⁻¹ • g t, 0])
      (habY z s) := by
  intro t i
  funext y
  have R0 := congrFun (congrFun (hsys.1 t) 0) y
  have R1 := congrFun (congrFun (hsys.1 t) 1) y
  have R2 := congrFun (congrFun (hsys.1 t) 2) y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, habP_row0, habN_row0, habP_row1, habN_row1,
    habP_row2, habN_row2, habH, habBv, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at R0 R1 R2
  have hrec : s (t + 1) = z t 1 := by
    rw [hsys.2 t]
    funext y
    simp [habSel, Fin.sum_univ_three]
  fin_cases i
  · change 𝔼.E t (z (t + 1) 0) y = rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 0 y + 0
    rw [habA_row0]
    field_simp
    linear_combination -R0
  · change 𝔼.E t (z (t + 1) 1) y = rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 1 y + 0
    rw [habA_row1]
    linear_combination -R2
  · change 𝔼.E t (z (t + 1) 2) y =
      rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 2 y + (β * η * vphi)⁻¹ * g t y
    rw [habA_row2]
    linear_combination (norm := skip) (1 / (β * η)) * R1 -
      (1 / (vphi * β ^ 2 * η)) * R0 - ((1 + β * η ^ 2) / (β * η)) * R2
    field_simp
    ring
  · change 𝔼.E t (s (t + 1)) y = rvMul (habA ξp ω vphi β η φπ φx) (habY z s t) 3 y + 0
    rw [habA_row3, hrec, hza t 1, add_zero]


/-! ### Non-existence: a unit root, or no stable root -/

/-- **Woodford (2003), App. C.1, fn. 1 (resonance), for a real unit root.** If `μ₀² = 1`, `c ≠ 0`
and `E_t u_{t+1} = μ₀ u_t + c μ₀ᵗ`, then `u` is unbounded (`E_0[μ₀ᵗ u_t] = u_0 + t c μ₀`). -/
theorem no_bounded_resonance [Nonempty Ω] {u : ℕ → Ω → ℝ} {μ0 c : ℝ} (hμ : μ0 ^ 2 = 1)
    (hc : c ≠ 0) (hu0 : 𝔼.E 0 (u 0) = u 0)
    (hu : ∀ t, 𝔼.E t (u (t + 1)) = μ0 • u t + fun _ => c * μ0 ^ t) (hb : BoundedProc u) :
    False := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨y⟩ := ‹Nonempty Ω›
  have habs : |μ0| = 1 := by
    have h := congrArg Real.sqrt hμ
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_one] at h
  have key : ∀ t : ℕ, μ0 ^ t * 𝔼.E 0 (u t) y = u 0 y + t * (c * μ0) := by
    intro t
    induction t with
    | zero => simp [hu0]
    | succ t ih =>
      have h1 : 𝔼.E 0 (u (t + 1)) y = μ0 * 𝔼.E 0 (u t) y + c * μ0 ^ t := by
        rw [← 𝔼.tower (Nat.zero_le t), hu t, map_add, map_smul, 𝔼.const]
        rfl
      rw [h1]
      have e1 : μ0 ^ (t + 1) * (μ0 * 𝔼.E 0 (u t) y + c * μ0 ^ t) =
          (μ0 ^ 2) * (μ0 ^ t * 𝔼.E 0 (u t) y) + c * μ0 * (μ0 ^ 2) ^ t := by ring
      rw [e1, hμ, ih]
      push_cast
      ring
  have hb : ∀ t : ℕ, (t : ℝ) * |c| ≤ 2 * M := by
    intro t
    have k := key t
    have hE : |𝔼.E 0 (u t) y| ≤ M := 𝔼.abs_E_le (hM t) 0 y
    have h0 : |u 0 y| ≤ M := hM 0 y
    have e : |μ0 ^ t * 𝔼.E 0 (u t) y| = |𝔼.E 0 (u t) y| := by
      rw [abs_mul, abs_pow, habs, one_pow, one_mul]
    have : |(t : ℝ) * (c * μ0)| ≤ 2 * M := by
      have : (t : ℝ) * (c * μ0) = μ0 ^ t * 𝔼.E 0 (u t) y - u 0 y := by linarith
      rw [this]
      calc |μ0 ^ t * 𝔼.E 0 (u t) y - u 0 y| ≤ |μ0 ^ t * 𝔼.E 0 (u t) y| + |u 0 y| :=
            abs_sub _ _
        _ ≤ 2 * M := by rw [e]; linarith
    rwa [abs_mul, abs_mul, habs, mul_one, abs_of_nonneg (Nat.cast_nonneg t)] at this
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * M / |c|)
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have := hb n
  rw [div_lt_iff₀ hcpos] at hn
  linarith


/-- Woodford (2003), p. 335: the state vector of an adapted bounded solution is adapted and
bounded. -/
theorem habY_props {z : ℕ → Fin 3 → Ω → ℝ} {s : ℕ → Ω → ℝ} (hza : VAdapted 𝔼 z)
    (hsa : 𝔼.Adapted s) (hzb : VBounded z) (hsb : BoundedProc s) :
    VAdapted 𝔼 (habY z s) ∧ VBounded (habY z s) := by
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Ms, hMs⟩ := hsb
  refine ⟨fun t i => ?_, ⟨max Mz Ms, fun t i y => ?_⟩⟩
  · fin_cases i
    · exact hza t 0
    · exact hza t 1
    · exact hza t 2
    · exact hsa t
  · fin_cases i
    · exact (hMz t 0 y).trans (le_max_left _ _)
    · exact (hMz t 1 y).trans (le_max_left _ _)
    · exact (hMz t 2 y).trans (le_max_left _ _)
    · exact (hMs t y).trans (le_max_right _ _)

omit 𝔼 in
/-- Woodford (2003), p. 335: a real root `μ₀` of `Q` is a real eigenvalue of `A`:
`det(μ₀ I − A) = 0`. -/
theorem habA_det_real {ξp ω vphi β η φπ φx μ0 : ℝ} (hβ : β ≠ 0) (hη : η ≠ 0) (hφ : vphi ≠ 0)
    (hQ : habQ ξp ω vphi β η φπ φx μ0 = 0) :
    (Matrix.scalar (Fin 4) μ0 - habA ξp ω vphi β η φπ φx).det = 0 := by
  have hdetC := habA_charpoly (ξp := ξp) (ω := ω) (φπ := φπ) (φx := φx) hβ hη hφ (μ0 : ℂ)
  rw [hQ, neg_zero, zero_div] at hdetC
  have hmap : Complex.ofRealHom.mapMatrix (Matrix.scalar (Fin 4) μ0 - habA ξp ω vphi β η φπ φx) =
      Matrix.scalar (Fin 4) (μ0 : ℂ) - (habA ξp ω vphi β η φπ φx).map Complex.ofReal := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  have := RingHom.map_det Complex.ofRealHom (Matrix.scalar (Fin 4) μ0 - habA ξp ω vphi β η φπ φx)
  rw [hmap, hdetC] at this
  simpa using this

omit 𝔼 in
/-- Woodford (2003), p. 335: column 0 of `vᵀ A`. -/
theorem habA_col0 (ξp ω vphi β η φπ φx : ℝ) (v : Fin 4 → ℝ) :
    ∑ k, v k * habA ξp ω vphi β η φπ φx k 0 =
      v 0 / β + v 2 * ((1 - β * φπ) / (β ^ 2 * η * vphi)) := by
  simp [Fin.sum_univ_four, habA]
  ring

omit 𝔼 in
/-- Woodford (2003), p. 335: column 1 of `vᵀ A`. -/
theorem habA_col1 (ξp ω vphi β η φπ φx : ℝ) (v : Fin 4 → ℝ) :
    ∑ k, v k * habA ξp ω vphi β η φπ φx k 1 =
      v 0 * (-(ξp * (ω + vphi * (1 + β * η ^ 2))) / β) +
      v 2 * ((-(ξp * (ω + vphi * (1 + β * η ^ 2))) - β * (vphi * (1 + β * η ^ 2 + η) + φx)) /
        (β ^ 2 * η * vphi)) + v 3 := by
  simp [Fin.sum_univ_four, habA]

omit 𝔼 in
/-- Woodford (2003), p. 335: column 2 of `vᵀ A`. -/
theorem habA_col2 (ξp ω vphi β η φπ φx : ℝ) (v : Fin 4 → ℝ) :
    ∑ k, v k * habA ξp ω vphi β η φπ φx k 2 =
      v 0 * (ξp * vphi * β * η / β) + v 1 +
      v 2 * ((ξp * vphi * β * η + β * vphi * (1 + β * η ^ 2) + β ^ 2 * vphi * η) /
        (β ^ 2 * η * vphi)) := by
  simp [Fin.sum_univ_four, habA]

/-- **Woodford (2003), (1.30)–(1.33), p. 335: a root `μ₀ = ±1` rules out existence.** If the
characteristic quartic has the root `1` (the Taylor-principle boundary, `habQ_one`) or `−1`, then
for the bounded deterministic disturbance `r̂ⁿ_t = μ₀ᵗ − π̄`, `ī_t = 0` and any bounded `x_{−1}`
known at date 0 there is no bounded adapted equilibrium of (1.25), (1.26), (1.30): the
left eigenvector `v` of `A` for `μ₀` loads on the IS disturbance (`v₂ ≠ 0`), so `u_t = v · y_t`
satisfies `E_t u_{t+1} = μ₀ u_t + c μ₀ᵗ` with `c ≠ 0` (resonance). -/
theorem nonexist_unitRoot [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar μ0 : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hη : η ≠ 0) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (hμ : μ0 ^ 2 = 1) (hQ : habQ ξp ω vphi β η φπ φx μ0 = 0) {xm1 : Ω → ℝ} {B : ℝ}
    (hm0 : 𝔼.E 0 xm1 = xm1) (hmb : ∀ y, |xm1 y| ≤ B) :
    ¬∃ p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 p.1 p.2.1 p.2.2 (fun _ _ => 0)
        (fun t _ => μ0 ^ t - πbar) ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧
      BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2 := by
  rintro ⟨⟨π, x, i⟩, ⟨hIS, hAS, hT⟩, hπa, hxa, -, ⟨Mπ, hMπ⟩, ⟨Mx, hMx⟩, -⟩
  dsimp only at hIS hAS hT hπa hxa hMπ hMx
  have hsys := (habit_iff_predSys 𝔼 hφ hxbar hxa hT).mp ⟨hIS, hAS⟩
  obtain ⟨hva, hsa, hvb, hsb⟩ := habVec_props 𝔼 (πbar := πbar) (xbar := xbar) hm0 hmb hπa hxa
    hMπ hMx
  have hE := expSys_of_predSys 𝔼 hβ0.ne' hη hφ hsys hva
  obtain ⟨hya, ⟨My, hMy⟩⟩ := habY_props 𝔼 hva hsa hvb hsb
  set y := habY (habVec 𝔼 πbar xbar π x) (habS xbar xm1 x) with hydef
  set A := habA ξp ω vphi β η φπ φx with hAdef
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr (habA_det_real hβ0.ne' hη hφ hQ)
  have hvA : ∀ j, ∑ i, v i * A i j = v j * μ0 := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul_sub, Pi.sub_apply, Matrix.scalar_apply, Matrix.vecMul_diagonal,
      Pi.zero_apply] at this
    have e : Matrix.vecMul v A j = ∑ i, v i * A i j := rfl
    linarith
  have hμβ : μ0 * β ≠ 1 := by
    have habs : |μ0| = 1 := by
      have h := congrArg Real.sqrt hμ
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_one] at h
    intro h
    have : |μ0 * β| = β := by rw [abs_mul, habs, one_mul, abs_of_pos hβ0]
    rw [h, abs_one] at this
    linarith
  have hv2 : v 2 ≠ 0 := by
    intro h2
    have c0 := hvA 0
    have c1 := hvA 1
    have c2 := hvA 2
    rw [hAdef, habA_col0, h2] at c0
    rw [hAdef, habA_col1, h2] at c1
    rw [hAdef, habA_col2, h2] at c2
    have hv0' : v 0 = 0 := by
      have : v 0 * (1 - μ0 * β) = 0 := by
        have e : v 0 / β = v 0 * μ0 := by rw [zero_mul, add_zero] at c0; exact c0
        rw [div_eq_iff hβ0.ne'] at e
        linear_combination e
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hμβ))
    rw [hv0'] at c1 c2
    have hv1' : v 1 = 0 := by linarith
    rw [hv1'] at c1
    have hv3' : v 3 = 0 := by linarith
    apply hv0
    funext k
    fin_cases k
    · exact hv0'
    · exact hv1'
    · exact h2
    · exact hv3'
  set u : ℕ → Ω → ℝ := fun t => ∑ k, v k • y t k with hudef
  have hg : ∀ t, habG πbar (fun t (_ : Ω) => μ0 ^ t - πbar) (fun _ (_ : Ω) => (0 : ℝ)) t =
      fun _ => μ0 ^ t := by
    intro t
    funext w
    simp [habG]
  have hrec : ∀ t, 𝔼.E t (u (t + 1)) = μ0 • u t +
      fun _ => (v 2 * (β * η * vphi)⁻¹) * μ0 ^ t := by
    intro t
    funext w
    have hEk : ∀ k, 𝔼.E t (y (t + 1) k) w = ∑ j, A k j * y t j w +
        (![0, 0, (β * η * vphi)⁻¹ • habG πbar (fun t (_ : Ω) => μ0 ^ t - πbar)
          (fun _ (_ : Ω) => (0 : ℝ)) t, 0] : Fin 4 → Ω → ℝ) k w := by
      intro k
      have := congrFun (hE t k) w
      rw [this, Pi.add_apply, rvMul_apply]
    simp only [hudef, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hEk,
      Pi.add_apply]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hsum : ∀ j, ∑ k, v k * (A k j * y t j w) = v j * μ0 * y t j w := by
      intro j
      rw [← hvA j, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hsum, Fin.sum_univ_four, hg]
    simp
    ring
  have hu0 : 𝔼.E 0 (u 0) = u 0 := by
    simp only [hudef, map_sum, map_smul, hya 0]
  have hub : BoundedProc u := by
    refine ⟨(∑ k, |v k|) * My, fun t w => ?_⟩
    simp only [hudef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMy t k w) (abs_nonneg _)
  exact no_bounded_resonance 𝔼 hμ (mul_ne_zero hv2 (inv_ne_zero (by positivity))) hu0 hrec hub


/-- **Woodford (2003), (1.30)–(1.33), p. 335: no stable root rules out existence.** If no root
of the characteristic quartic lies in the closed unit disc, then with no disturbance
(`r̂ⁿ_t = −π̄`, `ī_t = 0`, so `g = 0`) and an initial gap `x_{−1} = x̄ + 1` there is no bounded
adapted equilibrium: all four eigenvalues of `A` lie outside the unit circle, so the only bounded
solution of `E_t y_{t+1} = A y_t` is `y = 0`, contradicting `y_{0,3} = x_{−1} − x̄ = 1`. -/
theorem nonexist_noRoot [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hβ : β ≠ 0)
    (hη : η ≠ 0) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (hno : ∀ μ : ℂ, ‖μ‖ ≤ 1 → habQ ξp ω vphi β η φπ φx μ ≠ 0) :
    ¬∃ p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar (fun _ => xbar + 1) p.1 p.2.1 p.2.2
        (fun _ _ => 0) (fun _ _ => -πbar) ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧
      BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2 := by
  rintro ⟨⟨π, x, i⟩, ⟨hIS, hAS, hT⟩, hπa, hxa, -, ⟨Mπ, hMπ⟩, ⟨Mx, hMx⟩, -⟩
  dsimp only at hIS hAS hT hπa hxa hMπ hMx
  have hsys := (habit_iff_predSys 𝔼 hφ hxbar hxa hT).mp ⟨hIS, hAS⟩
  obtain ⟨hva, hsa, hvb, hsb⟩ := habVec_props 𝔼 (πbar := πbar) (xbar := xbar)
    (𝔼.const 0 (xbar + 1)) (fun _ => le_refl |xbar + 1|) hπa hxa hMπ hMx
  have hE := expSys_of_predSys 𝔼 hβ hη hφ hsys hva
  obtain ⟨hya, hyb⟩ := habY_props 𝔼 hva hsa hvb hsb
  set y := habY (habVec 𝔼 πbar xbar π x) (habS xbar (fun _ => xbar + 1) x) with hydef
  have hw : (fun t => (![0, 0, (β * η * vphi)⁻¹ • habG πbar (fun _ (_ : Ω) => -πbar)
      (fun _ (_ : Ω) => (0 : ℝ)) t, 0] : Fin 4 → Ω → ℝ)) = 0 := by
    funext t k w
    fin_cases k <;> simp [habG]
  rw [hw] at hE
  have hA : EigenOut (habA ξp ω vphi β η φπ φx) := by
    intro μ hμ
    rw [habA_charpoly hβ hη hφ] at hμ
    have hK : ((β : ℂ) ^ 2 * η * vphi) ≠ 0 := by
      have : (β ^ 2 * η * vphi : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    have hQ : habQ ξp ω vphi β η φπ φx μ = 0 := by
      rw [div_eq_zero_iff, neg_eq_zero] at hμ
      exact hμ.resolve_right hK
    by_contra hle
    push Not at hle
    exact hno μ hle hQ
  obtain ⟨-, -, -, huniq⟩ := existsUnique_of_eigenOut 𝔼 hA (w := 0) (Mw := 0)
    (fun t i ω => by simp) (fun t i => by simp)
  have h1 := huniq y hE hya hyb
  have h0 := huniq 0 (fun t i => by simp [rvMul_zero]) (fun t i => by simp)
    ⟨0, fun t i ω => by simp⟩
  have hy0 : y = 0 := h1.trans h0.symm
  obtain ⟨w⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun (congrFun hy0 0) 3) w
  simp [hydef, habY, habS, lag] at this


/-! ### Non-uniqueness: a continuum of equilibria and sunspots -/

/-- **Woodford (2003), (1.30)–(1.33), p. 335: determinacy, the property characterised.** For every
bounded adapted disturbance (`r̂ⁿ`, `ī`) and every bounded `x_{−1}` known at date 0 there is exactly
one bounded adapted equilibrium `(π, x, î)` of (1.25), (1.26), (1.30). -/
def HabitDeterminate (ξp ω vphi β η φπ φx πbar xbar : ℝ) : Prop :=
  ∀ rn ibar : ℕ → Ω → ℝ, BoundedProc rn → BoundedProc ibar → 𝔼.Adapted rn → 𝔼.Adapted ibar →
    ∀ (xm1 : Ω → ℝ) (B : ℝ), 𝔼.E 0 xm1 = xm1 → (∀ y, |xm1 y| ≤ B) →
      ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
        HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 p.1 p.2.1 p.2.2 ibar rn ∧
        𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧
        BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2

/-- Woodford (2003), p. 335: the steady state `π = π̄`, `x = x̄`, `î = 0` is an equilibrium when
there is no disturbance (`r̂ⁿ = −π̄`, `ī = 0`) and `x_{−1} = x̄`. -/
theorem steady_habit {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hφ : vphi ≠ 0)
    (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) :
    HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar (fun _ => xbar) (fun _ _ => πbar) (fun _ _ => xbar)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -πbar) := by
  have hT : Taylor130 φπ φx πbar xbar (fun _ (_ : Ω) => πbar) (fun _ (_ : Ω) => xbar)
      (fun _ (_ : Ω) => (0 : ℝ)) (fun _ (_ : Ω) => (0 : ℝ)) := by
    intro t
    funext y
    simp
  have hx : 𝔼.Adapted (fun _ (_ : Ω) => xbar) := fun t => 𝔼.const t xbar
  have h := (habit_iff_predSys 𝔼 hφ hxbar (xm1 := fun _ => xbar) (rn := fun _ _ => -πbar) hx
    hT).mpr (by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext k y
      cases t <;>
        fin_cases k <;> simp [rvMul_apply, habVec, habS, habG, lag, 𝔼.const, Fin.sum_univ_three]
    · funext y
      simp [habVec, habS, habSel, lag, Fin.sum_univ_three])
  exact ⟨h.1, h.2, hT⟩

omit 𝔼 in
/-- Woodford (2003), p. 335 (tool): if `T = r₁ + r₂`, `D = r₁r₂` with `|r₁|, |r₂| ≤ 1` and
`0 < β < 1`, then `1 − βT + β²D = (1 − βr₁)(1 − βr₂) ≠ 0`. -/
theorem arDen_ne_zero {β T D : ℝ} {r1 r2 : ℂ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hT : (T : ℂ) = r1 + r2) (hD : (D : ℂ) = r1 * r2) (h1 : ‖r1‖ ≤ 1) (h2 : ‖r2‖ ≤ 1) :
    arDen β T D ≠ 0 := by
  have e : (arDen β T D : ℂ) = (1 - β * r1) * (1 - β * r2) := by
    unfold arDen
    push_cast
    rw [hT, hD]
    ring
  have f : ∀ r : ℂ, ‖r‖ ≤ 1 → (1 : ℂ) - β * r ≠ 0 := by
    intro r hr h
    have h' : (β : ℂ) * r = 1 := by linear_combination -h
    have := congrArg norm h'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0, norm_one] at this
    nlinarith [norm_nonneg r]
  intro h0
  have : ((arDen β T D : ℝ) : ℂ) = 0 := by rw [h0]; simp
  rw [e] at this
  rcases mul_eq_zero.mp this with h | h
  · exact f r1 h1 h
  · exact f r2 h2 h

/-- **Woodford (2003), (1.25), (1.26), (1.30): equilibrium plus a bounded mode, in full.** Under
the hypotheses of `habit_add_mode`, if the original equilibrium is bounded and adapted (with
`x_{−1}` known at date 0) and the mode `X` is bounded, the new equilibrium is bounded and
adapted. -/
theorem habit_add_mode_full {ξp ω vphi β η φπ φx πbar xbar T D : ℝ} (hφ : vphi ≠ 0)
    (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) (hden : arDen β T D ≠ 0)
    (hr1 : rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    (hr0 : rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    {xm1 : Ω → ℝ} {π x i ibar rn : ℕ → Ω → ℝ}
    (hmod : HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 π x i ibar rn)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    {X : ℕ → Ω → ℝ} (hX : 𝔼.Adapted X) (hXb : BoundedProc X)
    (hrec : ∀ t, 𝔼.E t (X (t + 1)) = T • X t - D • lag 0 X t) :
    HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1
      (fun t => π t + (arP ξp ω vphi β η T D • X t + arQ ξp ω vphi β η T D • lag 0 X t))
      (fun t => x t + X t)
      (fun t => i t + (φπ • (arP ξp ω vphi β η T D • X t + arQ ξp ω vphi β η T D • lag 0 X t) +
        φx • X t)) ibar rn ∧
    𝔼.Adapted (fun t => π t + (arP ξp ω vphi β η T D • X t +
      arQ ξp ω vphi β η T D • lag 0 X t)) ∧
    𝔼.Adapted (fun t => x t + X t) ∧
    𝔼.Adapted (fun t => i t + (φπ • (arP ξp ω vphi β η T D • X t +
      arQ ξp ω vphi β η T D • lag 0 X t) + φx • X t)) ∧
    BoundedProc (fun t => π t + (arP ξp ω vphi β η T D • X t +
      arQ ξp ω vphi β η T D • lag 0 X t)) ∧
    BoundedProc (fun t => x t + X t) ∧
    BoundedProc (fun t => i t + (φπ • (arP ξp ω vphi β η T D • X t +
      arQ ξp ω vphi β η T D • lag 0 X t) + φx • X t)) := by
  set p := arP ξp ω vphi β η T D
  set q := arQ ξp ω vphi β η T D
  have hL := lag_known 𝔼 (map_zero (𝔼.E 0)) hX
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨MX, hMX⟩ := hXb
  set K := max MX 0
  have hXK : ∀ t y, |X t y| ≤ K := fun t y => (hMX t y).trans (le_max_left _ _)
  have hLK : ∀ t y, |lag 0 X t y| ≤ K := by
    intro t y
    cases t with
    | zero => simp [lag, K]
    | succ t => exact hXK t y
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨habit_add_mode 𝔼 hφ hxbar hden hr1 hr0 hmod hxa hX hrec, fun t => ?_, fun t => ?_,
    fun t => ?_, ⟨Mπ + (|p| * K + |q| * K), fun t y => ?_⟩, ⟨Mx + K, fun t y => ?_⟩,
    ⟨Mi + (|φπ| * (|p| * K + |q| * K) + |φx| * K), fun t y => ?_⟩⟩
  · simp only [map_add, map_smul, hπa t, hX t, hL t]
  · simp only [map_add, hxa t, hX t]
  · simp only [map_add, map_smul, hia t, hX t, hL t]
  · have hpq : |p * X t y + q * lag 0 X t y| ≤ |p| * K + |q| * K := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul_of_nonneg_left (hXK t y) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left (hLK t y) (abs_nonneg _)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (abs_add_le _ _).trans (add_le_add (hMπ t y) hpq)
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hMx t y) (hXK t y))
  · have hpq : |p * X t y + q * lag 0 X t y| ≤ |p| * K + |q| * K := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul_of_nonneg_left (hXK t y) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left (hLK t y) (abs_nonneg _)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hMi t y) ?_)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left hpq (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hXK t y) (abs_nonneg _)


/-- Woodford (2003), p. 335: the deterministic mode `X_t = c p_t` of size `c`. -/
def detMode (c T D : ℝ) : ℕ → Ω → ℝ := fun t _ => c * chSeq T D t

/-- Woodford (2003), p. 335: the deterministic mode solves `E_t X_{t+1} = T X_t − D X_{t−1}`. -/
theorem detMode_rec (c T D : ℝ) (t : ℕ) :
    𝔼.E t (detMode c T D (t + 1)) = T • detMode c T D t - D • lag 0 (detMode c T D) t := by
  change 𝔼.E t (fun _ => c * chSeq T D (t + 1)) = _
  rw [𝔼.const]
  funext y
  cases t with
  | zero => simp [chSeq, lag, detMode]; ring
  | succ t => simp [chSeq, lag, detMode]; ring

/-- **Woodford (2003), (1.30)–(1.33), p. 335: a continuum of bounded equilibria.** If
`μ² − Tμ + D` divides the characteristic quartic, `1 − βT + β²D ≠ 0` and `p_t` is bounded (both
roots of the factor in the closed unit disc, distinct or both strictly inside:
`chSeq_bounded_of_distinct`, `chSeq_bounded_of_schur`), then with no disturbance
(`r̂ⁿ = −π̄`, `ī = 0`) and `x_{−1} = x̄`, for every `c ∈ ℝ` the steady state plus `c` times the
mode is a bounded adapted equilibrium; its output gap at date 0 is `x̄ + c`
(`habit_continuum_x0`), so the equilibria are pairwise distinct. -/
theorem habit_continuum {ξp ω vphi β η φπ φx πbar xbar T D : ℝ} (hφ : vphi ≠ 0)
    (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) (hden : arDen β T D ≠ 0)
    (hr1 : rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    (hr0 : rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0) (hM : ∃ M, ∀ k, |chSeq T D k| ≤ M)
    (c : ℝ) :
    HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar (fun _ : Ω => xbar)
      (fun t => (fun _ : Ω => πbar) + (arP ξp ω vphi β η T D • detMode c T D t +
        arQ ξp ω vphi β η T D • lag 0 (detMode c T D) t))
      (fun t => (fun _ : Ω => xbar) + detMode c T D t)
      (fun t => (fun _ : Ω => (0 : ℝ)) + (φπ • (arP ξp ω vphi β η T D • detMode c T D t +
        arQ ξp ω vphi β η T D • lag 0 (detMode c T D) t) + φx • detMode c T D t))
      (fun _ (_ : Ω) => (0 : ℝ)) (fun _ (_ : Ω) => -πbar) ∧
    𝔼.Adapted (fun t => (fun _ : Ω => πbar) + (arP ξp ω vphi β η T D • detMode c T D t +
        arQ ξp ω vphi β η T D • lag 0 (detMode c T D) t)) ∧
    𝔼.Adapted (fun t => (fun _ : Ω => xbar) + detMode c T D t) ∧
    𝔼.Adapted (fun t => (fun _ : Ω => (0 : ℝ)) + (φπ • (arP ξp ω vphi β η T D • detMode c T D t +
        arQ ξp ω vphi β η T D • lag 0 (detMode c T D) t) + φx • detMode c T D t)) ∧
    BoundedProc (fun t => (fun _ : Ω => πbar) + (arP ξp ω vphi β η T D • detMode c T D t +
        arQ ξp ω vphi β η T D • lag 0 (detMode c T D) t)) ∧
    BoundedProc (fun t => (fun _ : Ω => xbar) + detMode c T D t) ∧
    BoundedProc (fun t => (fun _ : Ω => (0 : ℝ)) + (φπ • (arP ξp ω vphi β η T D • detMode c T D t +
        arQ ξp ω vphi β η T D • lag 0 (detMode c T D) t) + φx • detMode c T D t)) := by
  obtain ⟨M, hM⟩ := hM
  have hXb : BoundedProc (detMode (Ω := Ω) c T D) :=
    ⟨|c| * M, fun t y => by
      simp only [detMode, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)⟩
  exact habit_add_mode_full 𝔼 hφ hxbar hden hr1 hr0 (steady_habit 𝔼 hφ hxbar)
    (fun t => 𝔼.const t _) (fun t => 𝔼.const t _) (fun t => 𝔼.const t _)
    ⟨|πbar|, fun _ _ => le_rfl⟩ ⟨|xbar|, fun _ _ => le_rfl⟩ ⟨0, fun _ _ => by simp⟩
    (fun t => 𝔼.const t _) hXb (detMode_rec 𝔼 c T D)

omit 𝔼 in
/-- Woodford (2003), p. 335: the member `c` of the continuum has date-0 output gap `x̄ + c`. -/
theorem habit_continuum_x0 (xbar c T D : ℝ) (y : Ω) :
    (((fun _ : Ω => xbar) + detMode c T D 0 : Ω → ℝ)) y = xbar + c := by
  simp [detMode, chSeq]

/-- **Woodford (2003), (1.30)–(1.33), p. 335: a quadratic factor with bounded modes rules out
determinacy.** Under the hypotheses of `habit_continuum` (and a nonempty state space), the habit
model is not determinate: the no-disturbance data with `x_{−1} = x̄` have the distinct bounded
equilibria `c = 0` and `c = 1`. -/
theorem not_determinate_of_factor [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar T D : ℝ}
    (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) (hden : arDen β T D ≠ 0)
    (hr1 : rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    (hr0 : rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0) (hM : ∃ M, ∀ k, |chSeq T D k| ≤ M) :
    ¬HabitDeterminate 𝔼 ξp ω vphi β η φπ φx πbar xbar := by
  intro hD
  obtain ⟨p, -, huniq⟩ := hD (fun _ _ => -πbar) (fun _ _ => 0) ⟨|πbar|, fun _ _ => by simp⟩
    ⟨0, fun _ _ => by simp⟩ (fun t => 𝔼.const t _) (fun t => 𝔼.const t _) (fun _ => xbar) |xbar|
    (𝔼.const 0 xbar) (fun _ => le_rfl)
  have e0 := huniq (_, _, _) (habit_continuum 𝔼 hφ hxbar hden hr1 hr0 hM 0)
  have e1 := huniq (_, _, _) (habit_continuum 𝔼 hφ hxbar hden hr1 hr0 hM 1)
  have e := e0.trans e1.symm
  simp only [Prod.mk.injEq] at e
  obtain ⟨y⟩ := ‹Nonempty Ω›
  have h := congrFun (congrFun e.2.1 0) y
  rw [habit_continuum_x0, habit_continuum_x0] at h
  norm_num at h

omit 𝔼 in
/-- Woodford (2003), p. 335 (tool): under the Schur–Cohn condition `1 − βT + β²D ≠ 0`
(`0 < β < 1`). -/
theorem arDen_ne_zero_of_schur {β T D : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hS : SchurStable T D) :
    arDen β T D ≠ 0 := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots T D).mp hS
  exact arDen_ne_zero hβ0 hβ1 (root_sum T D).symm (root_prod T D).symm h1.le h2.le

/-- **Woodford (2003), (1.30)–(1.33), p. 335: sunspot equilibria.** If the characteristic
quartic has a factor `μ² − Tμ + D` with both roots strictly inside the unit circle (two stable
roots, counted with multiplicity: one too many), then next to every bounded adapted equilibrium,
for any disturbance, there is a bounded adapted equilibrium driven by any bounded sunspot
innovation `ε` with `E_t ε_{t+1} = 0`: add the mode `X_t = ∑_{k ≤ t} p_{t−k} ε_k`. -/
theorem habit_sunspot {ξp ω vphi β η φπ φx πbar xbar T D : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) (hS : SchurStable T D)
    (hr1 : rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    (hr0 : rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    {xm1 : Ω → ℝ} {π x i ibar rn : ℕ → Ω → ℝ}
    (hmod : HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 π x i ibar rn)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hεb : BoundedProc ε)
    (hmz : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1
      (fun t => π t + (arP ξp ω vphi β η T D • sunX T D ε t +
        arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t))
      (fun t => x t + sunX T D ε t)
      (fun t => i t + (φπ • (arP ξp ω vphi β η T D • sunX T D ε t +
        arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t) + φx • sunX T D ε t)) ibar rn ∧
    𝔼.Adapted (fun t => π t + (arP ξp ω vphi β η T D • sunX T D ε t +
      arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t)) ∧
    𝔼.Adapted (fun t => x t + sunX T D ε t) ∧
    𝔼.Adapted (fun t => i t + (φπ • (arP ξp ω vphi β η T D • sunX T D ε t +
      arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t) + φx • sunX T D ε t)) ∧
    BoundedProc (fun t => π t + (arP ξp ω vphi β η T D • sunX T D ε t +
      arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t)) ∧
    BoundedProc (fun t => x t + sunX T D ε t) ∧
    BoundedProc (fun t => i t + (φπ • (arP ξp ω vphi β η T D • sunX T D ε t +
      arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t) + φx • sunX T D ε t)) :=
  habit_add_mode_full 𝔼 hφ hxbar (arDen_ne_zero_of_schur hβ0 hβ1 hS) hr1 hr0 hmod hπa hxa hia
    hπb hxb hib (sunX_adapted 𝔼 hεa) (sunX_bounded hS hεb) (sunX_rec 𝔼 hεa hmz)


/-! #### Genuinely stochastic sunspot equilibria on the coin-flip tree -/

open ExpectationsFiniteTree in
/-- Woodford (2003), p. 335 (sunspots on the core finite tree): the coin-flip innovation is
adapted. -/
theorem coinShock_adapted : coinSystem.Adapted coinShock := by
  intro t
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun ω' h => coinShock_measurable t h

open ExpectationsFiniteTree in
/-- Woodford (2003), p. 335 (sunspots on the core finite tree): the coin-flip innovation is
bounded by one. -/
theorem coinShock_bounded : BoundedProc coinShock :=
  ⟨1, fun t ω => by unfold coinShock; split_ifs <;> simp⟩

open ExpectationsFiniteTree in
/-- **Woodford (2003), (1.30)–(1.33), p. 335: genuinely stochastic sunspot equilibria.** With two
stable roots (a Schur-stable factor `μ² − Tμ + D` of the characteristic quartic), on the coin-flip
tree, with no fundamental disturbance (`r̂ⁿ = −π̄`, `ī = 0`, `x_{−1} = x̄`), besides the steady
state there is a bounded adapted equilibrium driven by the coin flips alone: its output gap at
date 1 is `x̄ + 1` or `x̄ − 1` according to the first flip, while its date-0 forecast is `x̄`. -/
theorem coin_sunspot {ξp ω vphi β η φπ φx πbar xbar T D : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) (hS : SchurStable T D)
    (hr1 : rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0)
    (hr0 : rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0) :
    ∃ π x i : ℕ → Bool × Bool → ℝ,
      HabitModel coinSystem ξp ω vphi β η φπ φx πbar xbar (fun _ => xbar) π x i
        (fun _ _ => 0) (fun _ _ => -πbar) ∧
      coinSystem.Adapted π ∧ coinSystem.Adapted x ∧ coinSystem.Adapted i ∧
      BoundedProc π ∧ BoundedProc x ∧ BoundedProc i ∧
      x 1 (true, true) = xbar + 1 ∧ x 1 (false, true) = xbar - 1 ∧
      coinSystem.E 0 (x 1) = fun _ => xbar := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := habit_sunspot coinSystem hβ0 hβ1 hφ hxbar hS hr1 hr0
    (steady_habit coinSystem (φπ := φπ) (φx := φx) hφ hxbar) (fun t => coinSystem.const t _)
    (fun t => coinSystem.const t _) (fun t => coinSystem.const t _) ⟨|πbar|, fun _ _ => le_rfl⟩
    ⟨|xbar|, fun _ _ => le_rfl⟩ ⟨0, fun _ _ => by simp⟩ coinShock_adapted coinShock_bounded
    coinShock_mean_zero
  have hX1 : sunX T D coinShock 1 = coinShock 1 := by
    funext ω
    simp [sunX, Finset.sum_range_succ, chSeq, coinShock]
  refine ⟨_, _, _, h1, h2, h3, h4, h5, h6, h7, ?_, ?_, ?_⟩
  · simp only [hX1]
    simp [coinShock]
  · simp only [hX1]
    simp [coinShock]
    ring
  · have hE := sunX_rec coinSystem (T := T) (D := D) coinShock_adapted coinShock_mean_zero 0
    have h0 : sunX T D coinShock 0 = 0 := by
      funext ω
      simp [sunX, coinShock]
    rw [map_add, coinSystem.const, hE, h0]
    funext ω
    simp [lag]


/-! ### The root condition and the Blanchard–Kahn decomposition -/

/-- **Woodford (2003), (1.30)–(1.33), p. 335: the Blanchard–Kahn condition in the structural
parameters.** The characteristic quartic `Q` (`habQ`, `habQ_structural`) has a real root `λ`
with `|λ| < 1` and no further root in the closed unit disc, counted with multiplicity: the cubic
quotient `R_λ(μ) = Q(μ)/(μ − λ)` (`synth`, `quart_eq_synth`) has no root with `|μ| ≤ 1`.
Equivalently: exactly one root of `Q` in the closed unit disc, and it lies inside. -/
def HabitRootCond (ξp ω vphi β η φπ φx : ℝ) : Prop :=
  ∃ lam : ℝ, |lam| < 1 ∧ habQ ξp ω vphi β η φπ φx lam = 0 ∧
    ∀ μ : ℂ, ‖μ‖ ≤ 1 → synth (habCoef ξp ω vphi β η φπ φx) lam μ ≠ 0

/-- Woodford (2003), (1.31)–(1.33), p. 335: the coefficients `ω = (ω_π, λ, λ²)` of the
predetermined `x_{t−1} − x̄` in `(π̂_t, x̂_t, E_t x̂_{t+1})` for the stable root `λ`, with
`ω_π = [ξ_p(ω + φ(1 + βη²))λ − ξ_p φβηλ² − ξ_p φη]/(1 − βλ)` from the AS relation. -/
noncomputable def bkOmega (ξp ω vphi β η lam : ℝ) : Fin 3 → ℝ :=
  ![(ξp * (ω + vphi * (1 + β * η ^ 2)) * lam - ξp * vphi * β * η * lam ^ 2 - ξp * vphi * η) /
    (1 - β * lam), lam, lam ^ 2]

omit 𝔼 in
/-- Woodford (2003), p. 335: the quartic at a real point, in structural form. -/
theorem habQ_real (ξp ω vphi β η φπ φx lam : ℝ) :
    habQ ξp ω vphi β η φπ φx lam =
      (((1 - β * lam) * (vphi * β * η * lam ^ 3 - vphi * (1 + β * η + β * η ^ 2) * lam ^ 2 +
        (vphi * (1 + η + β * η ^ 2) + φx) * lam - vphi * η) -
      (φπ - lam) * (ξp * (vphi * β * η * lam ^ 2 - (ω + vphi * (1 + β * η ^ 2)) * lam +
        vphi * η)) : ℝ) : ℂ) := by
  rw [habQ_structural]
  push_cast
  ring

omit 𝔼 in
/-- **Woodford (2003), (1.31)–(1.33), p. 335: every root gives a decomposition.** If `Q(λ) = 0`
and `βλ ≠ 1`, then `(λ, ω)` with `ω = bkOmega` solves `Pω = λNω + h`, `λ = (0, 1, 0)·ω`. -/
theorem decomp_of_root {ξp ω vphi β η φπ φx lam : ℝ} (hb : 1 - β * lam ≠ 0) (hφ : vphi ≠ 0)
    (hQ : habQ ξp ω vphi β η φπ φx lam = 0) :
    DecompN (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) habSel 0 lam
      (bkOmega ξp ω vphi β η lam) := by
  rw [habQ_real] at hQ
  have hQr := Complex.ofReal_eq_zero.mp hQ
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · simp [habP, habN, habH, bkOmega, Fin.sum_univ_three]
      field_simp
      ring
    · simp [habP, habN, habH, bkOmega, Fin.sum_univ_three]
      linear_combination (norm := skip) (1 / (vphi * (1 - β * lam))) * hQr
      field_simp
      ring
    · simp [habP, habN, habH, bkOmega, Fin.sum_univ_three]
      ring
  · simp [habSel, bkOmega, Fin.sum_univ_three]


omit 𝔼 in
/-- **Woodford (2003), p. 335: the forward block carries the remaining roots.** If `Q(λ) = 0` and
`βλ ≠ 1`, then with `M = P − (Nω)φᵀ` (`resMN`), `φ det(M − μN) = R_λ(μ)`, the cubic quotient
`Q(μ)/(μ − λ)`. -/
theorem resM_det {ξp ω vphi β η φπ φx lam : ℝ} (hb : 1 - β * lam ≠ 0) (hφ : vphi ≠ 0)
    (hQ : habQ ξp ω vphi β η φπ φx lam = 0) (μ : ℂ) :
    (vphi : ℂ) * ((resMN (habP ξp ω vphi β η φπ φx) (habN vphi β η) habSel
      (bkOmega ξp ω vphi β η lam)).map Complex.ofReal -
        μ • (habN vphi β η).map Complex.ofReal).det =
      synth (habCoef ξp ω vphi β η φπ φx) lam μ := by
  have hb' : (1 : ℂ) - β * lam ≠ 0 := by exact_mod_cast hb
  have hφ' : (vphi : ℂ) ≠ 0 := by exact_mod_cast hφ
  rw [habQ, quart] at hQ
  rw [Matrix.det_fin_three]
  simp [resMN, habP, habN, habSel, bkOmega, Fin.sum_univ_three, synth, habCoef] at hQ ⊢
  linear_combination (norm := skip) ((β : ℂ) / (1 - β * lam)) * hQ
  field_simp
  ring


omit 𝔼 in
/-- **Woodford (2003), (1.30)–(1.33), p. 335: the root condition gives the Blanchard–Kahn
condition.** For `0 < β < 1`, `φ ≠ 0` (any `η`, including the Ch. 4 limit `η = 0`): if
`HabitRootCond` holds with root `λ`, then `BKCondition` holds with `(λ, bkOmega λ)`: the
decomposition (`decomp_of_root`), `|λ| < 1`, `det M ≠ 0` (`R_λ(0) ≠ 0`), and every eigenvalue
`w ≠ 0` of `G = M⁻¹N` has `|w| < 1` (`R_λ(1/w) = 0` forces `|1/w| > 1`). -/
theorem bk_of_rootCond {ξp ω vphi β η φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : vphi ≠ 0) (h : HabitRootCond ξp ω vphi β η φπ φx) :
    ∃ lam ωv, BKCondition (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) habSel 0
      lam ωv := by
  obtain ⟨lam, hl, hQ, hR⟩ := h
  have hb : 1 - β * lam ≠ 0 := by
    have h1 : |β * lam| < 1 := by
      rw [abs_mul, abs_of_pos hβ0]
      nlinarith [abs_nonneg lam]
    intro h0
    have h2 : β * lam = 1 := by linarith
    rw [h2, abs_one] at h1
    exact lt_irrefl _ h1
  set M := resMN (habP ξp ω vphi β η φπ φx) (habN vphi β η) habSel (bkOmega ξp ω vphi β η lam)
    with hMdef
  set N := habN vphi β η with hNdef
  have hdet := resM_det (φπ := φπ) (φx := φx) (ξp := ξp) (ω := ω) hb hφ hQ
  have hφ' : (vphi : ℂ) ≠ 0 := by exact_mod_cast hφ
  have hmapdet : ∀ A : Matrix (Fin 3) (Fin 3) ℝ, (A.map Complex.ofReal).det = (A.det : ℂ) := by
    intro A
    exact (RingHom.map_det Complex.ofRealHom A).symm
  have hM : M.det ≠ 0 := by
    intro h0
    have h1 := hdet 0
    rw [zero_smul, sub_zero, hmapdet, h0, Complex.ofReal_zero, mul_zero] at h1
    exact hR 0 (by simp) h1.symm
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  refine ⟨lam, bkOmega ξp ω vphi β η lam, decomp_of_root hb hφ hQ, hl, hMu, fun w hw => ?_⟩
  have hreal : M * predG (habP ξp ω vphi β η φπ φx) N habSel (bkOmega ξp ω vphi β η lam) = N := by
    change M * (M⁻¹ * N) = N
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M hMu, Matrix.one_mul]
  set G := predG (habP ξp ω vphi β η φπ φx) N habSel (bkOmega ξp ω vphi β η lam)
  have hMG : M.map Complex.ofReal * G.map Complex.ofReal = N.map Complex.ofReal := by
    rw [← hreal]
    ext i j
    simp [Matrix.mul_apply]
  have hs : (Matrix.scalar (Fin 3) w : Matrix (Fin 3) (Fin 3) ℂ) = w • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hprod : M.map Complex.ofReal * (Matrix.scalar (Fin 3) w - G.map Complex.ofReal) =
      w • M.map Complex.ofReal - N.map Complex.ofReal := by
    rw [Matrix.mul_sub, hMG, hs, Matrix.mul_smul, Matrix.mul_one]
  have hz : (w • M.map Complex.ofReal - N.map Complex.ofReal).det = 0 := by
    rw [← hprod, Matrix.det_mul, hw, mul_zero]
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]
    exact one_pos
  · have hsplit : w • M.map Complex.ofReal - N.map Complex.ofReal =
        w • (M.map Complex.ofReal - w⁻¹ • N.map Complex.ofReal) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hw0, one_smul]
    rw [hsplit, Matrix.det_smul, Fintype.card_fin] at hz
    have hz' : (M.map Complex.ofReal - w⁻¹ • N.map Complex.ofReal).det = 0 :=
      (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hw0)
    have hsyn : synth (habCoef ξp ω vphi β η φπ φx) lam w⁻¹ = 0 := by
      rw [← hdet, hz', mul_zero]
    by_contra hge
    push Not at hge
    have hinv : ‖w⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hge
    exact hR _ hinv hsyn


/-! ### Necessity, and the exact characterisation -/

omit 𝔼 in
/-- Woodford (2003), p. 335 (tool): a nonreal root `μ` of `Q` gives the real quadratic factor
`μ² − 2Re(μ) μ + |μ|²` (roots `μ`, `μ̄`). -/
theorem factor_of_nonreal {c : Fin 5 → ℝ} {μ : ℂ} (hq : quart c μ = 0) (him : μ.im ≠ 0) :
    rem1 c (2 * μ.re) (μ.re ^ 2 + μ.im ^ 2) = 0 ∧ rem0 c (2 * μ.re) (μ.re ^ 2 + μ.im ^ 2) = 0 ∧
      ((2 * μ.re : ℝ) : ℂ) = μ + conj μ ∧ ((μ.re ^ 2 + μ.im ^ 2 : ℝ) : ℂ) = μ * conj μ ∧
      μ ≠ conj μ := by
  have hT : ((2 * μ.re : ℝ) : ℂ) = μ + conj μ := by
    apply Complex.ext <;> simp; ring
  have hD : ((μ.re ^ 2 + μ.im ^ 2 : ℝ) : ℂ) = μ * conj μ := by
    apply Complex.ext
    · simp [sq]
    · simp [sq]
      ring
  have hne : μ ≠ conj μ := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    exact him (by linarith)
  have hs : synth c μ (conj μ) = 0 := by
    have e := quart_eq_synth c μ (conj μ)
    rw [quart_conj, hq, map_zero, add_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨h1, h0⟩ := rem_zero_of_roots c hT hD hq hs
  exact ⟨h1, h0, hT, hD, hne⟩

/-- Woodford (2003), (1.30)–(1.33), p. 335: non-existence for some disturbance — some bounded
adapted `r̂ⁿ`, `ī` and bounded `x_{−1}` known at date 0 have no bounded adapted equilibrium. -/
def HabitNonexist (ξp ω vphi β η φπ φx πbar xbar : ℝ) : Prop :=
  ∃ (rn ibar : ℕ → Ω → ℝ) (xm1 : Ω → ℝ) (B : ℝ), BoundedProc rn ∧ BoundedProc ibar ∧
    𝔼.Adapted rn ∧ 𝔼.Adapted ibar ∧ 𝔼.E 0 xm1 = xm1 ∧ (∀ y, |xm1 y| ≤ B) ∧
    ¬∃ p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 p.1 p.2.1 p.2.2 ibar rn ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧
      BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2

/-- Woodford (2003), p. 335: non-existence for some disturbance contradicts determinacy. -/
theorem not_determinate_of_nonexist {ξp ω vphi β η φπ φx πbar xbar : ℝ}
    (h : HabitNonexist 𝔼 ξp ω vphi β η φπ φx πbar xbar) :
    ¬HabitDeterminate 𝔼 ξp ω vphi β η φπ φx πbar xbar := by
  intro hD
  obtain ⟨rn, ibar, xm1, B, hrn, hib, hrna, hiba, hm0, hmb, hno⟩ := h
  obtain ⟨p, hp, -⟩ := hD rn ibar hrn hib hrna hiba xm1 B hm0 hmb
  exact hno ⟨p, hp⟩

/-- Woodford (2003), p. 335: a root `μ₀ = ±1` of the quartic gives non-existence for the
disturbance `r̂ⁿ_t = μ₀ᵗ − π̄`, `ī = 0`, `x_{−1} = x̄` (`nonexist_unitRoot`). -/
theorem nonexist_of_unit [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar μ0 : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hη : η ≠ 0) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (hμ : μ0 ^ 2 = 1) (hQ : habQ ξp ω vphi β η φπ φx μ0 = 0) :
    HabitNonexist 𝔼 ξp ω vphi β η φπ φx πbar xbar :=
  ⟨fun t _ => μ0 ^ t - πbar, fun _ _ => 0, fun _ => xbar, |xbar|,
    ⟨1 + |πbar|, fun t _ => by
      have hp : |μ0 ^ t| = 1 := by
        rw [abs_pow]
        have h := congrArg Real.sqrt hμ
        rw [Real.sqrt_sq_eq_abs, Real.sqrt_one] at h
        rw [h, one_pow]
      exact (abs_sub _ _).trans (by rw [hp])⟩,
    ⟨0, fun _ _ => by simp⟩, fun t => 𝔼.const t _, fun t => 𝔼.const t _, 𝔼.const 0 xbar,
    fun _ => le_rfl, nonexist_unitRoot 𝔼 hβ0 hβ1 hη hφ hxbar hμ hQ (𝔼.const 0 xbar)
      (fun _ => le_refl |xbar|)⟩

omit 𝔼 in
/-- Woodford (2003), p. 335 (`η = 0`, the Ch. 4 limit): `μ = 0` is a root of the quartic. -/
theorem habQ_zero_eta (ξp ω vphi β φπ φx : ℝ) : habQ ξp ω vphi β 0 φπ φx 0 = 0 := by
  simp [habQ, quart, habCoef]

omit 𝔼 in
/-- Woodford (2003), p. 335 (`η = 0`): a root `μ₀ = ±1` together with the root `0` gives the
factor `μ² − μ₀μ`, with distinct roots in the closed unit disc. -/
theorem factor_of_unit_eta_zero {ξp ω vphi β φπ φx μ0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hμ : μ0 ^ 2 = 1) (hQ : habQ ξp ω vphi β 0 φπ φx μ0 = 0) :
    rem1 (habCoef ξp ω vphi β 0 φπ φx) μ0 0 = 0 ∧ rem0 (habCoef ξp ω vphi β 0 φπ φx) μ0 0 = 0 ∧
      arDen β μ0 0 ≠ 0 ∧ ∃ M, ∀ k, |chSeq μ0 0 k| ≤ M := by
  have hμ0 : (μ0 : ℂ) ≠ 0 := by
    intro h
    have : μ0 = 0 := by exact_mod_cast h
    rw [this] at hμ
    norm_num at hμ
  have hn : ‖(μ0 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h := congrArg Real.sqrt hμ
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_one] at h
    rw [h]
  have hs : synth (habCoef ξp ω vphi β 0 φπ φx) μ0 0 = 0 := by
    have e := quart_eq_synth (habCoef ξp ω vphi β 0 φπ φx) μ0 0
    have h0 := habQ_zero_eta ξp ω vphi β φπ φx
    rw [habQ] at hQ h0
    rw [h0, hQ, add_zero, zero_sub] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (neg_ne_zero.mpr hμ0)
  have hT : ((μ0 : ℝ) : ℂ) = (μ0 : ℂ) + 0 := by simp
  have hD : ((0 : ℝ) : ℂ) = (μ0 : ℂ) * 0 := by simp
  obtain ⟨r1, r0⟩ := rem_zero_of_roots _ hT hD hQ hs
  have h0n : ‖(0 : ℂ)‖ ≤ 1 := by simp
  exact ⟨r1, r0, arDen_ne_zero hβ0 hβ1 hT hD hn h0n,
    ⟨_, chSeq_bounded_of_distinct hT hD hμ0 hn h0n⟩⟩

/-- **Woodford (2003), (1.30)–(1.33), p. 335: necessity of the Blanchard–Kahn condition.** For
`0 < β < 1`, `φ ≠ 0`, `x̄` consistent with `π̄` (any `η`, including the Ch. 4 limit `η = 0`), and
any expectation system on a nonempty state space: if `HabitRootCond` fails then either some
bounded adapted disturbance and bounded `x_{−1}` known at 0 have no bounded adapted equilibrium
(for `η ≠ 0`: a root `±1` of the quartic, `nonexist_unitRoot`, or no root in the closed unit
disc, `nonexist_noRoot`), or the quartic has a real quadratic factor `μ² − Tμ + D` whose mode
`p_t` is bounded, so that the no-disturbance data have the continuum of equilibria of
`habit_continuum` (two distinct roots in the closed disc, or a repeated root inside it). -/
theorem habit_failure [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (h : ¬HabitRootCond ξp ω vphi β η φπ φx) :
    HabitNonexist 𝔼 ξp ω vphi β η φπ φx πbar xbar ∨
    (∃ T D : ℝ, rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0 ∧
      rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0 ∧ arDen β T D ≠ 0 ∧
      ∃ M, ∀ k, |chSeq T D k| ≤ M) := by
  -- a root `±1`: resonance (`η ≠ 0`), or a factor with the root `0` (`η = 0`)
  have unit : ∀ μ0 : ℝ, μ0 ^ 2 = 1 → habQ ξp ω vphi β η φπ φx μ0 = 0 →
      HabitNonexist 𝔼 ξp ω vphi β η φπ φx πbar xbar ∨
      (∃ T D : ℝ, rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0 ∧
        rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0 ∧ arDen β T D ≠ 0 ∧
        ∃ M, ∀ k, |chSeq T D k| ≤ M) := by
    intro μ0 hμ hQ
    by_cases hη : η = 0
    · subst hη
      exact Or.inr ⟨μ0, 0, factor_of_unit_eta_zero hβ0 hβ1 hμ hQ⟩
    · exact Or.inl (nonexist_of_unit 𝔼 hβ0 hβ1 hη hφ hxbar hμ hQ)
  by_cases h1 : habQ ξp ω vphi β η φπ φx ((1 : ℝ) : ℂ) = 0
  · exact unit 1 (by norm_num) h1
  by_cases hm1 : habQ ξp ω vphi β η φπ φx ((-1 : ℝ) : ℂ) = 0
  · exact unit (-1) (by norm_num) hm1
  -- a nonreal root in the closed disc: the conjugate pair
  by_cases hc : ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ habQ ξp ω vphi β η φπ φx μ = 0 ∧ μ.im ≠ 0
  · obtain ⟨μ, hμ1, hμQ, hμim⟩ := hc
    obtain ⟨r1, r0, hT, hD, hne⟩ := factor_of_nonreal hμQ hμim
    have hcn : ‖conj μ‖ ≤ 1 := by rw [Complex.norm_conj]; exact hμ1
    exact Or.inr ⟨_, _, r1, r0, arDen_ne_zero hβ0 hβ1 hT hD hμ1 hcn,
      ⟨_, chSeq_bounded_of_distinct hT hD hne hμ1 hcn⟩⟩
  push Not at hc
  -- every root in the closed disc is real and lies strictly inside
  have hreal : ∀ μ : ℂ, ‖μ‖ ≤ 1 → habQ ξp ω vphi β η φπ φx μ = 0 →
      μ = (μ.re : ℂ) ∧ |μ.re| < 1 := by
    intro μ hμ hQ
    have him := hc μ hμ hQ
    have he : μ = (μ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    refine ⟨he, ?_⟩
    have hle : |μ.re| ≤ 1 := by
      have : ‖(μ.re : ℂ)‖ ≤ 1 := by rw [← he]; exact hμ
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      rcases abs_eq (zero_le_one) |>.mp heq with h' | h'
      · exact h1 (by rw [← h', ← he]; exact hQ)
      · exact hm1 (by rw [← h', ← he]; exact hQ)
  by_cases hr : ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ habQ ξp ω vphi β η φπ φx μ = 0
  · -- a stable real root `λ₁` and, by failure of the root condition, a second one `λ₂`
    obtain ⟨μ1, hn1, hq1⟩ := hr
    obtain ⟨he1, hl1⟩ := hreal μ1 hn1 hq1
    set l1 := μ1.re
    have hq1' : habQ ξp ω vphi β η φπ φx l1 = 0 := by rw [← he1]; exact hq1
    unfold HabitRootCond at h
    push Not at h
    obtain ⟨μ2, hn2, hs2⟩ := h l1 hl1 hq1'
    have hq2 : habQ ξp ω vphi β η φπ φx μ2 = 0 := by
      rw [habQ, quart_eq_synth _ l1 μ2, hs2]
      simp only [mul_zero, zero_add]
      exact hq1'
    obtain ⟨he2, hl2⟩ := hreal μ2 hn2 hq2
    set l2 := μ2.re
    have hT : ((l1 + l2 : ℝ) : ℂ) = (l1 : ℂ) + μ2 := by rw [he2]; push_cast; ring
    have hD : ((l1 * l2 : ℝ) : ℂ) = (l1 : ℂ) * μ2 := by rw [he2]; push_cast; ring
    obtain ⟨r1, r0⟩ := rem_zero_of_roots _ hT hD hq1' hs2
    have hS : SchurStable (l1 + l2) (l1 * l2) := by
      obtain ⟨a1, b1⟩ := abs_lt.mp hl1
      obtain ⟨a2, b2⟩ := abs_lt.mp hl2
      refine ⟨abs_lt.mpr ⟨by nlinarith, by nlinarith⟩, abs_lt.mpr ⟨by nlinarith, by nlinarith⟩⟩
    exact Or.inr ⟨_, _, r1, r0, arDen_ne_zero_of_schur hβ0 hβ1 hS, chSeq_bounded_of_schur hS⟩
  · -- no root in the closed disc (impossible for `η = 0`, where `0` is a root)
    push Not at hr
    have hη : η ≠ 0 := by
      rintro rfl
      exact hr 0 (by simp) (by exact_mod_cast habQ_zero_eta ξp ω vphi β φπ φx)
    exact Or.inl ⟨fun _ _ => -πbar, fun _ _ => 0, fun _ => xbar + 1, |xbar + 1|,
      ⟨|πbar|, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩, fun t => 𝔼.const t _,
      fun t => 𝔼.const t _, 𝔼.const 0 _, fun _ => le_rfl,
      nonexist_noRoot 𝔼 hβ0.ne' hη hφ hxbar hr⟩


/-- Woodford (2003), (1.30)–(1.33), p. 335 (sufficiency, `habit_existsUnique` restated in terms of
`HabitDeterminate`): the Blanchard–Kahn condition implies determinacy. -/
theorem determinate_of_bk {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hφ : vphi ≠ 0)
    (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (h : ∃ lam ωv, BKCondition (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η)
      habSel 0 lam ωv) :
    HabitDeterminate 𝔼 ξp ω vphi β η φπ φx πbar xbar := by
  obtain ⟨lam, ωv, hBK⟩ := h
  intro rn ibar hrn hib hrna hiba xm1 B hm0 hmb
  exact habit_existsUnique 𝔼 hφ hxbar hBK hrn hib hrna hiba hm0 hmb

/-- **Woodford (2003), (1.30)–(1.33), p. 335: determinacy implies the root condition** (any
expectation system on a nonempty state space; `habit_failure`). -/
theorem rootCond_of_determinate [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (hD : HabitDeterminate 𝔼 ξp ω vphi β η φπ φx πbar xbar) :
    HabitRootCond ξp ω vphi β η φπ φx := by
  by_contra h
  rcases habit_failure 𝔼 hβ0 hβ1 hφ hxbar h with hn | ⟨T, D, r1, r0, hden, hM⟩
  · exact not_determinate_of_nonexist 𝔼 hn hD
  · exact not_determinate_of_factor 𝔼 hφ hxbar hden r1 r0 hM hD

/-- **Woodford (2003), (1.30)–(1.33), p. 335: the exact determinacy condition for the habit
model.** For `0 < β < 1`, every `η`, `φ ≠ 0` and `x̄` consistent with `π̄`, and any expectation
system on a nonempty state space: the habit model (1.25), (1.26), (1.30) has a unique bounded
equilibrium for every bounded disturbance and every bounded `x_{−1}` iff the characteristic
quartic has exactly one root in the closed unit disc, lying inside it (`HabitRootCond`). -/
theorem habit_determinate_iff [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) :
    HabitDeterminate 𝔼 ξp ω vphi β η φπ φx πbar xbar ↔ HabitRootCond ξp ω vphi β η φπ φx :=
  ⟨rootCond_of_determinate 𝔼 hβ0 hβ1 hφ hxbar,
    fun h => determinate_of_bk 𝔼 hφ hxbar (bk_of_rootCond hβ0 hβ1 hφ h)⟩

omit 𝔼 in
/-- **Woodford (2003), (1.30)–(1.33), p. 335: the Blanchard–Kahn condition of `Habit` in the
structural parameters.** `BKCondition` holds for some `(λ, ω)` iff `HabitRootCond`
(`0 < β < 1`, every `η`, `φ ≠ 0`). -/
theorem habit_bk_iff {ξp ω vphi β η φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : vphi ≠ 0) :
    (∃ lam ωv, BKCondition (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) habSel 0
      lam ωv) ↔ HabitRootCond ξp ω vphi β η φπ φx := by
  have hx0 : XbarConsistent ξp ω vphi β η 0 0 := by simp [XbarConsistent]
  exact ⟨fun h => rootCond_of_determinate perfectForesight hβ0 hβ1 hφ hx0
    (determinate_of_bk perfectForesight hφ hx0 h), bk_of_rootCond hβ0 hβ1 hφ⟩

/-- **Woodford (2003), (1.30)–(1.33), p. 335: necessity and sufficiency of the Blanchard–Kahn
condition.** Under the hypotheses of `habit_determinate_iff`: unique bounded equilibrium for every
bounded disturbance ⇔ `BKCondition` (sufficiency: `habit_existsUnique`; necessity: this module). -/
theorem habit_determinate_iff_bk [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar) :
    HabitDeterminate 𝔼 ξp ω vphi β η φπ φx πbar xbar ↔
      ∃ lam ωv, BKCondition (habP ξp ω vphi β η φπ φx) (habN vphi β η) (habH ξp vphi η) habSel 0
        lam ωv :=
  (habit_determinate_iff 𝔼 hβ0 hβ1 hφ hxbar).trans (habit_bk_iff hβ0 hβ1 hφ).symm

/-- **Woodford (2003), (1.30)–(1.33), p. 335, with `φ = [(1 − βη)σ]⁻¹`: the condition in
`(σ, η, β, ξ_p, ω, φ_π, φ_x)`.** For `σ > 0`, `0 < β < 1`, `βη < 1` and `x̄` consistent with `π̄`,
on any nonempty state space: determinacy ⇔ `HabitRootCond ξ_p ω φ(η) β η φ_π φ_x`
⇔ `BKCondition`. -/
theorem habit_determinate_iff_sigma [Nonempty Ω] {ξp ω σ β η φπ φx πbar xbar : ℝ} (hσ : 0 < σ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβη : β * η < 1)
    (hxbar : XbarConsistent ξp ω (vphiOf β σ η) β η πbar xbar) :
    (HabitDeterminate 𝔼 ξp ω (vphiOf β σ η) β η φπ φx πbar xbar ↔
      HabitRootCond ξp ω (vphiOf β σ η) β η φπ φx) ∧
    (HabitRootCond ξp ω (vphiOf β σ η) β η φπ φx ↔
      ∃ lam ωv, BKCondition (habP ξp ω (vphiOf β σ η) β η φπ φx) (habN (vphiOf β σ η) β η)
        (habH ξp (vphiOf β σ η) η) habSel 0 lam ωv) :=
  ⟨habit_determinate_iff 𝔼 hβ0 hβ1 (vphiOf_pos hσ hβη).ne' hxbar,
    (habit_bk_iff hβ0 hβ1 (vphiOf_pos hσ hβη).ne').symm⟩

/-! ### Too many stable roots: sunspots -/

/-- Woodford (2003), p. 335: at least two roots of the characteristic quartic strictly inside the
unit circle, counted with multiplicity (a nonreal root, which brings its conjugate, or two real
roots `λ₁`, `λ₂` with `R_{λ₁}(λ₂) = 0`, possibly `λ₁ = λ₂`). -/
def HabitTwoStable (ξp ω vphi β η φπ φx : ℝ) : Prop :=
  (∃ μ : ℂ, ‖μ‖ < 1 ∧ habQ ξp ω vphi β η φπ φx μ = 0 ∧ μ.im ≠ 0) ∨
    ∃ l1 l2 : ℝ, |l1| < 1 ∧ |l2| < 1 ∧ habQ ξp ω vphi β η φπ φx l1 = 0 ∧
      synth (habCoef ξp ω vphi β η φπ φx) l1 l2 = 0

omit 𝔼 in
/-- Woodford (2003), p. 335: two stable roots give a Schur-stable real quadratic factor. -/
theorem schur_factor_of_twoStable {ξp ω vphi β η φπ φx : ℝ}
    (h : HabitTwoStable ξp ω vphi β η φπ φx) :
    ∃ T D, SchurStable T D ∧ rem1 (habCoef ξp ω vphi β η φπ φx) T D = 0 ∧
      rem0 (habCoef ξp ω vphi β η φπ φx) T D = 0 := by
  rcases h with ⟨μ, hμ, hQ, him⟩ | ⟨l1, l2, hl1, hl2, hQ, hs⟩
  · obtain ⟨r1, r0, -, -, -⟩ := factor_of_nonreal hQ him
    refine ⟨_, _, ?_, r1, r0⟩
    have hn : μ.re ^ 2 + μ.im ^ 2 < 1 := by
      have h1 : ‖μ‖ ^ 2 < 1 := by nlinarith [norm_nonneg μ]
      rwa [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← sq, ← sq] at h1
    have hi : 0 < μ.im ^ 2 := by positivity
    refine ⟨abs_lt.mpr ⟨by nlinarith, by nlinarith⟩, abs_lt.mpr ⟨?_, ?_⟩⟩
    · nlinarith [sq_nonneg (μ.re + 1)]
    · nlinarith [sq_nonneg (μ.re - 1)]
  · have hT : ((l1 + l2 : ℝ) : ℂ) = (l1 : ℂ) + l2 := by push_cast; ring
    have hD : ((l1 * l2 : ℝ) : ℂ) = (l1 : ℂ) * l2 := by push_cast; ring
    obtain ⟨r1, r0⟩ := rem_zero_of_roots _ hT hD hQ hs
    obtain ⟨a1, b1⟩ := abs_lt.mp hl1
    obtain ⟨a2, b2⟩ := abs_lt.mp hl2
    exact ⟨_, _, ⟨abs_lt.mpr ⟨by nlinarith, by nlinarith⟩, abs_lt.mpr ⟨by nlinarith,
      by nlinarith⟩⟩, r1, r0⟩

/-- **Woodford (2003), (1.30)–(1.33), p. 335: too many stable roots ⇒ sunspot equilibria.** With
two stable roots (`HabitTwoStable`), `0 < β < 1` and `φ ≠ 0`, there is a Schur-stable quadratic
factor `μ² − Tμ + D` such that next to every bounded adapted equilibrium (any disturbance, any
expectation system) every bounded sunspot innovation `ε` with `E_t ε_{t+1} = 0` gives another
bounded adapted equilibrium (`habit_sunspot`); in particular the model is not determinate on any
nonempty state space (`not_determinate_of_twoStable`). -/
theorem habit_sunspots_of_twoStable {ξp ω vphi β η φπ φx πbar xbar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (h : HabitTwoStable ξp ω vphi β η φπ φx) :
    ∃ T D, SchurStable T D ∧ ∀ {xm1 : Ω → ℝ} {π x i ibar rn : ℕ → Ω → ℝ},
      HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1 π x i ibar rn →
      𝔼.Adapted π → 𝔼.Adapted x → 𝔼.Adapted i → BoundedProc π → BoundedProc x →
      BoundedProc i → ∀ {ε : ℕ → Ω → ℝ}, 𝔼.Adapted ε → BoundedProc ε →
      (∀ t, 𝔼.E t (ε (t + 1)) = 0) →
      HabitModel 𝔼 ξp ω vphi β η φπ φx πbar xbar xm1
        (fun t => π t + (arP ξp ω vphi β η T D • sunX T D ε t +
          arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t))
        (fun t => x t + sunX T D ε t)
        (fun t => i t + (φπ • (arP ξp ω vphi β η T D • sunX T D ε t +
          arQ ξp ω vphi β η T D • lag 0 (sunX T D ε) t) + φx • sunX T D ε t)) ibar rn := by
  obtain ⟨T, D, hS, r1, r0⟩ := schur_factor_of_twoStable h
  exact ⟨T, D, hS, fun hmod hπa hxa hia hπb hxb hib _ hεa hεb hmz =>
    (habit_sunspot 𝔼 hβ0 hβ1 hφ hxbar hS r1 r0 hmod hπa hxa hia hπb hxb hib hεa hεb hmz).1⟩

/-- Woodford (2003), p. 335: two stable roots rule out determinacy. -/
theorem not_determinate_of_twoStable [Nonempty Ω] {ξp ω vphi β η φπ φx πbar xbar : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : vphi ≠ 0) (hxbar : XbarConsistent ξp ω vphi β η πbar xbar)
    (h : HabitTwoStable ξp ω vphi β η φπ φx) :
    ¬HabitDeterminate 𝔼 ξp ω vphi β η φπ φx πbar xbar := by
  obtain ⟨T, D, hS, r1, r0⟩ := schur_factor_of_twoStable h
  exact not_determinate_of_factor 𝔼 hφ hxbar (arDen_ne_zero_of_schur hβ0 hβ1 hS) r1 r0
    (chSeq_bounded_of_schur hS)


/-! ### The calibration, and parameter points where the condition fails -/

omit 𝔼 in
/-- **Woodford (2003), Table 5.1, p. 341, with `η = 1/2`: the root condition holds at the
calibration of `bkCondition_calibration`** (`φ_π ≈ 1.49`, `φ_x ≈ 0.49`): the stable root is
`λ = 1/6`, the other three roots lie outside the unit circle. -/
theorem rootCond_calibration :
    HabitRootCond (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) calPhiPi calPhiX :=
  (habit_bk_iff (by norm_num) (by norm_num) (by norm_num)).mp
    ⟨1 / 6, calOmega, bkCondition_calibration⟩

/-- **Woodford (2003), Table 5.1 calibration with `η = 1/2`: determinacy at the calibration**, for
any expectation system on a nonempty state space (`habit_determinate_iff`). -/
theorem determinate_calibration [Nonempty Ω] :
    HabitDeterminate 𝔼 (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) calPhiPi calPhiX 0 0 :=
  (habit_determinate_iff 𝔼 (by norm_num) (by norm_num) (by norm_num)
    (by simp [XbarConsistent])).mpr rootCond_calibration

/-- Woodford (2003), p. 335 (a passive rule): `φ_π ≈ 0.70`, chosen so that `9/10` and `2/5` are
roots of the quartic at the Table 5.1 calibration with `η = 1/2`. -/
noncomputable def indPhiPi : ℝ := 2282167749 / 3258030625

/-- Woodford (2003), p. 335 (a passive rule): `φ_x ≈ 0.030`, chosen with `indPhiPi`. -/
noncomputable def indPhiX : ℝ := 1050762843824 / 34551414778125

omit 𝔼 in
/-- **Woodford (2003), p. 335: a passive rule with two stable roots.** At the Table 5.1
calibration with `η = 1/2` and the rule `φ_π ≈ 0.70 < 1`, `φ_x ≈ 0.030`, the quartic has the two
stable roots `9/10` and `2/5`; it factors through `μ² − (13/10)μ + 9/25`. -/
theorem twoStable_passive :
    HabitTwoStable (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) indPhiPi indPhiX ∧
      rem1 (habCoef (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) indPhiPi indPhiX)
        (13 / 10) (9 / 25) = 0 ∧
      rem0 (habCoef (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) indPhiPi indPhiX)
        (13 / 10) (9 / 25) = 0 ∧ SchurStable (13 / 10) (9 / 25) := by
  refine ⟨Or.inr ⟨9 / 10, 2 / 5, by norm_num [abs_of_pos], by norm_num [abs_of_pos], ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [habQ_real]
    norm_num [indPhiPi, indPhiX]
  · simp only [synth, habCoef, indPhiPi, indPhiX, Matrix.cons_val]
    push_cast
    norm_num
  · norm_num [rem1, habCoef, indPhiPi, indPhiX]
  · norm_num [rem0, habCoef, indPhiPi, indPhiX]
  · norm_num [SchurStable, abs_of_pos]

omit 𝔼 in
/-- Woodford (2003), p. 335: the root condition fails for the passive rule. -/
theorem not_rootCond_passive :
    ¬HabitRootCond (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) indPhiPi indPhiX := by
  rw [← habit_determinate_iff perfectForesight (by norm_num) (by norm_num) (by norm_num)
    (show XbarConsistent (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) 0 0 by
      simp [XbarConsistent])]
  exact not_determinate_of_twoStable perfectForesight (by norm_num) (by norm_num) (by norm_num)
    (by simp [XbarConsistent]) twoStable_passive.1

open ExpectationsFiniteTree in
/-- **Woodford (2003), p. 335: an explicit sunspot equilibrium under the passive rule.** On the
coin-flip tree, with no fundamental disturbance and `x_{−1} = 0`, the passive rule has, besides
the zero steady state, a bounded adapted equilibrium driven by the coin flips alone
(`x_t = ∑_{k ≤ t} p_{t−k} ε_k`, `p` the sequence of `μ² − (13/10)μ + 9/25`): the output gap at
date 1 is `+1` or `−1` according to the first flip, while its date-0 forecast is `0`. -/
theorem sunspot_passive :
    ∃ π x i : ℕ → Bool × Bool → ℝ,
      HabitModel coinSystem (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) indPhiPi indPhiX 0 0
        (fun _ => 0) π x i (fun _ _ => 0) (fun _ _ => -0) ∧
      coinSystem.Adapted π ∧ coinSystem.Adapted x ∧ coinSystem.Adapted i ∧
      BoundedProc π ∧ BoundedProc x ∧ BoundedProc i ∧
      x 1 (true, true) = 0 + 1 ∧ x 1 (false, true) = 0 - 1 ∧
      coinSystem.E 0 (x 1) = fun _ => 0 := by
  obtain ⟨-, r1, r0, hS⟩ := twoStable_passive
  exact coin_sunspot (by norm_num) (by norm_num) (by norm_num) (by simp [XbarConsistent]) hS r1 r0

/-- **Woodford (2003), p. 335: the passive rule — a continuum of deterministic equilibria.** With
no disturbance and `x_{−1} = 0`, every `c ∈ ℝ` gives a bounded equilibrium with date-0 output gap
`c` (`habit_continuum`, `habit_continuum_x0`); hence the passive rule is not determinate on any
nonempty state space. -/
theorem not_determinate_passive [Nonempty Ω] :
    ¬HabitDeterminate 𝔼 (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) indPhiPi indPhiX 0 0 :=
  not_determinate_of_twoStable 𝔼 (by norm_num) (by norm_num) (by norm_num)
    (by simp [XbarConsistent]) twoStable_passive.1

/-- **Woodford (2003), p. 335 (the Taylor-principle boundary): explicit non-existence.** At the
Table 5.1 calibration with `η = 1/2` and the rule `φ_π = 1`, `φ_x = 0`, `μ = 1` is a root of the
quartic (`habQ_one`), and a permanent unit shock to the natural rate (`r̂ⁿ_t = 1`, `ī = 0`,
`π̄ = x̄ = 0`) has no bounded adapted equilibrium, whatever the bounded `x_{−1}` known at 0. -/
theorem nonexist_boundary [Nonempty Ω] {xm1 : Ω → ℝ} {B : ℝ} (hm0 : 𝔼.E 0 xm1 = xm1)
    (hmb : ∀ y, |xm1 y| ≤ B) :
    ¬∃ p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      HabitModel 𝔼 (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) 1 0 0 0 xm1 p.1 p.2.1 p.2.2
        (fun _ _ => 0) (fun _ _ => 1) ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧
      BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2 := by
  have hQ : habQ (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) 1 0 ((1 : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_one, habQ_one]
    norm_num
  have h := nonexist_unitRoot 𝔼 (πbar := 0) (xbar := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simp [XbarConsistent]) (by norm_num) hQ hm0 hmb
  have e : (fun t (_ : Ω) => (1 : ℝ) ^ t - 0) = fun _ _ => 1 := by
    funext t y
    simp
  rwa [e] at h

omit 𝔼 in
/-- Woodford (2003), p. 335: the root condition fails on the Taylor-principle boundary. -/
theorem not_rootCond_boundary :
    ¬HabitRootCond (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) 1 0 := by
  rw [← habit_determinate_iff perfectForesight (by norm_num) (by norm_num) (by norm_num)
    (show XbarConsistent (4 / 105) (47 / 100) (32 / 101) (99 / 100) (1 / 2) 0 0 by
      simp [XbarConsistent])]
  refine not_determinate_of_nonexist perfectForesight
    (nonexist_of_unit perfectForesight (μ0 := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by simp [XbarConsistent]) (by norm_num) ?_)
  rw [Complex.ofReal_one, habQ_one]
  norm_num

end Woodford.PolicyResponseDynamics.HabitNecessity
