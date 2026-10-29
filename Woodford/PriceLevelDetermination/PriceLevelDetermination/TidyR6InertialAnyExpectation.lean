/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.TidyR6ForwardSunspots
import PriceLevelDetermination.InertialBoundaryExistCube

/-!
# The boundary of Proposition 2.8 beyond informational closure

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 633–634.
`InertialBoundary.unique_affine` and `InertialBoundary.unique_cube` assume informational closure
(every variable constant on information cells is known). That closure is what makes
`E_t h(î_{t−1}) = h(î_{t−1})` and `E_t π_t³ = π_t³`. This module removes it.

## Main results

* `conc_lower`, `conc_upper`: **concentration of a forecast near the supremum.** If `D ≤ B`
  everywhere and `E_t D` is close to `B` in state `ω`, then `E_t` puts little weight on
  `{D < c}`: `(B − c)·E_t 1_{D<c} ≤ B − E_t D`. Only linearity, constants and monotonicity of
  `E_t` are used.
* `unique_affine_any`: **for every expectation system** (no informational closure, no pull-out
  property), the rule `φ_π π + h(î_{−1})` with `φ_π ≠ 0`, `h` continuous and the expanding
  diagonal of `InertialBoundary.unique_affine` has at most one bounded equilibrium for every
  initial rate and disturbance process. Continuity of `h` replaces closure: it makes the
  diagonal monotone, so
  the sign of `g(î_t) − g(î'_t)` is that of `î_t − î'_t` in every state that `E_t` weighs.
* `boundary_affine_any`: hence the rule `ruleCubI φ ρ (φ + ρ)` of
  `InertialBoundary.boundary_unit_circle` (c) has **exactly one** bounded equilibrium for every
  initial rate, without shocks, under every expectation system.
* `unique_affine_skew`: the extension is genuine: it applies to `skewSystem`, which is not
  informationally closed (`LocalIFTStochastic.skewSystem_not_infoClosed`).
* `unique_cube_of_cube_known`: the rule `ρ î_{−1} + σπ³` (`σ² = 1`, `σρ ≥ 1`) has at most one
  bounded equilibrium under every expectation system in which **cubes of known variables are
  known**; `cube_known_of_pullOut`: this holds whenever `E_t` has the pull-out property
  (`ExpectationSystem.PullOut`). Closure is no longer used for the forecast of the bound
  `∛(4 max(B − τ D_t, 0))` (concentration replaces it).
-/

namespace Woodford.PriceLevelDetermination.TidyR6InertialAnyExpectation

open scoped Topology
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic
open TidyR6ForwardSunspots (eq_zero_of_annulus)
open LocalIFTSystems (cbrt cbrt_pow)
open LocalIFTSystemsApps (Finert)
open InertialBoundary (eq0_of_solves eq1_of_solves lag_known sub_le_cbrt pow_le_of_le_cbrt
  cbrt_nonneg)

variable {Ω : Type*}

/-! ### Concentration near the supremum -/

/-- Woodford (2003), App. A.3, p. 634 (tool): **a lower bound for a forecast from a bound on the
event `{D ≥ c}`.** If `D ≤ B`, `Z ≥ αD` where `D ≥ c` and `Z ≥ −L` where `D < c`
(`0 ≤ c < B`, `α, L ≥ 0`), then
`E_t Z ≥ α E_t D − (αc + L)(B − E_t D)/(B − c)` in every state. -/
theorem conc_lower (𝔼 : ExpectationSystem Ω) (t : ℕ) (ω : Ω) {D Z : Ω → ℝ} {B c α L : ℝ}
    (hcB : c < B) (hα : 0 ≤ α) (hL : 0 ≤ L) (hc : 0 ≤ c) (hD : ∀ w, D w ≤ B)
    (hZ1 : ∀ w, c ≤ D w → α * D w ≤ Z w) (hZ2 : ∀ w, D w < c → -L ≤ Z w) :
    α * 𝔼.E t D ω - (α * c + L) * ((B - 𝔼.E t D ω) / (B - c)) ≤ 𝔼.E t Z ω := by
  classical
  set χ : Ω → ℝ := fun w => if D w < c then 1 else 0 with hχ
  have h1 : α • D - (α * c + L) • χ ≤ Z := by
    intro w
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hχ]
    by_cases hw : D w < c
    · simp only [hw, ↓reduceIte, mul_one]
      have := hZ2 w hw
      nlinarith
    · simp only [hw, ↓reduceIte, mul_zero, sub_zero]
      exact hZ1 w (not_lt.mp hw)
  have h2 : (B - c) • χ ≤ (fun _ => B) - D := by
    intro w
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hχ]
    by_cases hw : D w < c
    · simp only [hw, ↓reduceIte, mul_one]
      linarith
    · simp only [hw, ↓reduceIte, mul_zero]
      linarith [hD w]
  have h0 : (0 : Ω → ℝ) ≤ χ := by
    intro w
    simp only [Pi.zero_apply, hχ]
    split_ifs <;> norm_num
  have e1 := 𝔼.mono t h1 ω
  have e2 := 𝔼.mono t h2 ω
  have e0 := 𝔼.mono t h0 ω
  simp only [map_sub, map_smul, 𝔼.const, map_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at e1 e2 e0
  have hBc : 0 < B - c := by linarith
  have hq : 𝔼.E t χ ω ≤ (B - 𝔼.E t D ω) / (B - c) := by
    rw [le_div_iff₀ hBc]
    linarith
  have hk : 0 ≤ α * c + L := by positivity
  nlinarith

/-- Woodford (2003), App. A.3, p. 634 (tool): **an upper bound for a forecast from a bound on the
event `{D ≥ c}`.** If `D ≤ B`, `P ≤ A` where `D ≥ c` and `P ≤ F` where `D < c` (`c < B`,
`A, F ≥ 0`), then `E_t P ≤ A + F(B − E_t D)/(B − c)`. -/
theorem conc_upper (𝔼 : ExpectationSystem Ω) (t : ℕ) (ω : Ω) {D P : Ω → ℝ} {B c A F : ℝ}
    (hcB : c < B) (hA : 0 ≤ A) (hF : 0 ≤ F) (hD : ∀ w, D w ≤ B)
    (hP1 : ∀ w, c ≤ D w → P w ≤ A) (hP2 : ∀ w, D w < c → P w ≤ F) :
    𝔼.E t P ω ≤ A + F * ((B - 𝔼.E t D ω) / (B - c)) := by
  classical
  set χ : Ω → ℝ := fun w => if D w < c then 1 else 0 with hχ
  have h1 : P ≤ (fun _ => A) + F • χ := by
    intro w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]
    by_cases hw : D w < c
    · simp only [hw, ↓reduceIte, mul_one]
      linarith [hP2 w hw]
    · simp only [hw, ↓reduceIte, mul_zero, add_zero]
      exact hP1 w (not_lt.mp hw)
  have h2 : (B - c) • χ ≤ (fun _ => B) - D := by
    intro w
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hχ]
    by_cases hw : D w < c
    · simp only [hw, ↓reduceIte, mul_one]
      linarith
    · simp only [hw, ↓reduceIte, mul_zero]
      linarith [hD w]
  have e1 := 𝔼.mono t h1 ω
  have e2 := 𝔼.mono t h2 ω
  simp only [map_add, map_sub, map_smul, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at e1 e2
  have hBc : 0 < B - c := by linarith
  have hq : 𝔼.E t χ ω ≤ (B - 𝔼.E t D ω) / (B - c) := by
    rw [le_div_iff₀ hBc]
    linarith
  nlinarith

/-! ### The affine rule under every expectation system -/

/-- Woodford (2003), App. A.3, p. 634 (tool): a continuous map with an expanding difference
`|g a − g b| ≥ |a − b| + κ|a − b|³` is strictly monotone: there is a sign `τ` with
`τ(g a − g b) > 0` whenever `a > b`. -/
theorem exists_sign_of_expanding {g : ℝ → ℝ} {κ : ℝ} (hgc : Continuous g) (hκ : 0 < κ)
    (hexp : ∀ a b, |a - b| + κ * |a - b| ^ 3 ≤ |g a - g b|) :
    ∃ τ : ℝ, |τ| = 1 ∧ ∀ a b, b < a → 0 < τ * (g a - g b) := by
  have hinj : Function.Injective g := by
    intro a b hab
    have h := hexp a b
    rw [hab, sub_self, abs_zero] at h
    have h3 : 0 ≤ κ * |a - b| ^ 3 := by positivity
    have : |a - b| ≤ 0 := by linarith
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  rcases hgc.strictMono_of_inj hinj with hm | ha
  · exact ⟨1, abs_one, fun a b hab => by rw [one_mul]; exact sub_pos.mpr (hm hab)⟩
  · exact ⟨-1, by norm_num, fun a b hab => by have := ha hab; linarith⟩

set_option maxHeartbeats 1600000 in
-- the push argument combines the concentration bound with explicit constants
/-- **Uniqueness on the boundary `φ_π ≠ 0` under every expectation system** (Woodford (2003),
Prop. 2.8, p. 96; App. A.3, p. 634): for the rule `Ψ(π, i) = φ_π π + h(i)` with `φ_π ≠ 0`, `h`
continuous, and the expanding diagonal `|g(i) − g(i')| ≥ |i − i'| + κ|i − i'|³`
(`g(i) = φ_π i + h(i)`, `κ > 0`), any two bounded adapted equilibria with the same initial rate
and disturbances coincide, **for every expectation system** (no informational closure, no
pull-out property). The gap `D_t = î_t − î'_t` satisfies `E_t D_{t+1} = E_t[g(î_t) − g(î'_t)]`;
at a state where `|D_t|` is near its supremum, `E_t` concentrates on states where `D_t` is large
(`conc_lower`), and there `g` has pushed the gap beyond the supremum. -/
theorem unique_affine_any (𝔼 : ExpectationSystem Ω) {Ψ : ℝ × ℝ → ℝ} {φ κ : ℝ} {h : ℝ → ℝ}
    (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) (hφ : φ ≠ 0) (hκ : 0 < κ) (hh : Continuous h)
    (hexp : ∀ i i', |i - i'| + κ * |i - i'| ^ 3 ≤ |(φ * i + h i) - (φ * i' + h i')|)
    {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x y : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (hy : SolvesSV 𝔼 (Finert Ψ) u y) : x = y := by
  set g : ℝ → ℝ := fun i => φ * i + h i with hg
  have hgc : Continuous g := (continuous_const.mul continuous_id).add hh
  obtain ⟨τ, hτ1, hτ⟩ := exists_sign_of_expanding hgc hκ hexp
  -- the rule without closure
  have hrule : ∀ z : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) u z → ∀ t,
      toP z t 1 = φ • toP z t 0 + 𝔼.E t (fun ω => h (lagV u.1 (fun s => z (s, ω)) t 1)) +
        𝔼.E t (fun ω => u.2 (t, ω) 1) := by
    intro z hz t
    rw [eq1_of_solves hz t]
    have e : (fun ω => Ψ (z (t, ω) 0, lagV u.1 (fun s => z (s, ω)) t 1)) =
        φ • toP z t 0 + fun ω => h (lagV u.1 (fun s => z (s, ω)) t 1) := by
      funext ω
      simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [e, map_add, map_smul, hz.1 t 0]
  set D : ℕ → Ω → ℝ := fun t => toP x t 1 - toP y t 1 with hD
  have hDk : ∀ t, 𝔼.E t (D t) = D t := fun t => by
    simp only [hD, map_sub, hx.1 t 1, hy.1 t 1]
  have hED : ∀ t, 𝔼.E t (D (t + 1)) =
      𝔼.E t (fun ω => g (x (t, ω) 1) - g (y (t, ω) 1)) := by
    intro t
    have hdiff : D (t + 1) = φ • (toP x (t + 1) 0 - toP y (t + 1) 0) +
        (𝔼.E (t + 1) (fun ω => h (x (t, ω) 1)) - 𝔼.E (t + 1) (fun ω => h (y (t, ω) 1))) := by
      change toP x (t + 1) 1 - toP y (t + 1) 1 = _
      rw [hrule x hx (t + 1), hrule y hy (t + 1)]
      simp only [lagV_succ, smul_sub]
      abel
    have htw : ∀ f : Ω → ℝ, 𝔼.E t (𝔼.E (t + 1) f) = 𝔼.E t f := fun f =>
      𝔼.tower (Nat.le_succ t) f
    have hrhs : (fun ω => g (x (t, ω) 1) - g (y (t, ω) 1)) =
        φ • D t + ((fun ω => h (x (t, ω) 1)) - fun ω => h (y (t, ω) 1)) := by
      funext ω
      simp only [hg, hD, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      change _ = φ * (x (t, ω) 1 - y (t, ω) 1) + _
      ring
    have hDk' : 𝔼.E t (toP x t 1 - toP y t 1) = toP x t 1 - toP y t 1 := hDk t
    rw [hdiff, hrhs]
    simp only [map_add, map_smul, map_sub, htw, eq0_of_solves hx t, eq0_of_solves hy t]
    funext ω
    simp only [hDk', hD, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- bounds
  set M := ‖x‖ + ‖y‖ with hMdef
  have hxM : ∀ t ω, |x (t, ω) 1| ≤ M := fun t ω =>
    (abs_apply_le x t ω 1).trans (le_add_of_nonneg_right (norm_nonneg y))
  have hyM : ∀ t ω, |y (t, ω) 1| ≤ M := fun t ω =>
    (abs_apply_le y t ω 1).trans (le_add_of_nonneg_left (norm_nonneg x))
  obtain ⟨L0, hL0⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    hgc.continuousOn
  set L := 2 * max L0 0 with hLdef
  have hL : 0 ≤ L := by positivity
  have hgM : ∀ z, |z| ≤ M → |g z| ≤ max L0 0 := fun z hz => by
    have := hL0 z ⟨(abs_le.mp hz).1, (abs_le.mp hz).2⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hZb : ∀ t ω, |g (x (t, ω) 1) - g (y (t, ω) 1)| ≤ L := fun t ω => by
    have h1 := hgM _ (hxM t ω)
    have h2 := hgM _ (hyM t ω)
    calc |g (x (t, ω) 1) - g (y (t, ω) 1)| ≤ |g (x (t, ω) 1)| + |g (y (t, ω) 1)| := abs_sub _ _
      _ ≤ L := by rw [hLdef]; linarith
  have hDM : ∀ p : ℕ × Ω, |D p.1 p.2| ≤ M := fun p => by
    have h1 := abs_le.mp (abs_apply_le x p.1 p.2 1)
    have h2 := abs_le.mp (abs_apply_le y p.1 p.2 1)
    change |x p 1 - y p 1| ≤ _
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  -- the gap of interest rates vanishes
  have hD0 : ∀ p : ℕ × Ω, D p.1 p.2 = 0 := by
    refine eq_zero_of_annulus (fun p : ℕ × Ω => D p.1 p.2) hDM (fun B hB _ hall => ?_)
    set c := B / 2 with hc
    set α := 1 + κ * c ^ 2 with hα
    have hcpos : 0 < c := by rw [hc]; positivity
    have hα1 : 0 < α - 1 := by
      have := mul_pos hκ (pow_pos hcpos 2)
      rw [hα]
      linarith
    set k := 2 * α + 2 * L / B with hk
    have hα0 : 0 < α := by linarith
    have hk0 : 0 ≤ k := by rw [hk]; positivity
    refine ⟨(α - 1) * B / (k + 1), div_pos (mul_pos hα1 hB) (by positivity), fun q _ => ?_⟩
    obtain ⟨t, ω⟩ := q
    by_contra hcon
    push Not at hcon
    set d := D t ω with hd
    obtain ⟨σ, hσ1, hσd⟩ : ∃ σ : ℝ, |σ| = 1 ∧ σ * d = |d| := by
      rcases le_or_gt 0 d with h0 | h0
      · exact ⟨1, abs_one, by rw [one_mul, abs_of_nonneg h0]⟩
      · exact ⟨-1, by norm_num, by rw [abs_of_neg h0]; ring⟩
    have hD'B : ∀ w, σ * D t w ≤ B := fun w =>
      (le_abs_self _).trans (by rw [abs_mul, hσ1, one_mul]; exact hall (t, w))
    have hZ1 : ∀ w, c ≤ σ * D t w →
        α * (σ * D t w) ≤ σ * τ * (g (x (t, w) 1) - g (y (t, w) 1)) := by
      intro w hw
      have hc0 : 0 < c := by positivity
      have hpos : 0 < σ * D t w := lt_of_lt_of_le hc0 hw
      have hDw : D t w = x (t, w) 1 - y (t, w) 1 := rfl
      have hD0w : D t w ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hpos
        exact lt_irrefl _ hpos
      have hsgn : 0 < σ * τ * (g (x (t, w) 1) - g (y (t, w) 1)) := by
        rcases lt_or_gt_of_ne hD0w with hneg | hpos'
        · have hs : σ < 0 := by
            by_contra hs
            push Not at hs
            nlinarith
          have h1 := hτ (y (t, w) 1) (x (t, w) 1) (by rw [hDw] at hneg; linarith)
          nlinarith
        · have hs : 0 < σ := by
            by_contra hs
            push Not at hs
            nlinarith
          have h1 := hτ (x (t, w) 1) (y (t, w) 1) (by rw [hDw] at hpos'; linarith)
          nlinarith
      have habs : σ * τ * (g (x (t, w) 1) - g (y (t, w) 1)) =
          |g (x (t, w) 1) - g (y (t, w) 1)| := by
        rw [← abs_of_pos hsgn, abs_mul, abs_mul, hσ1, hτ1, one_mul, one_mul]
      have he := hexp (x (t, w) 1) (y (t, w) 1)
      have hDa : |x (t, w) 1 - y (t, w) 1| = σ * D t w := by
        rw [← hDw, ← abs_of_pos hpos, abs_mul, hσ1, one_mul]
      rw [habs]
      rw [hDa] at he
      have hc2 : c ^ 2 ≤ (σ * D t w) ^ 2 := pow_le_pow_left₀ hc0.le hw 2
      change |g (x (t, w) 1) - g (y (t, w) 1)| ≥ _ at he
      rw [hα]
      nlinarith [mul_nonneg (mul_nonneg hκ.le hpos.le) (sub_nonneg.mpr hc2)]
    have hZ2 : ∀ w, σ * D t w < c → -L ≤ σ * τ * (g (x (t, w) 1) - g (y (t, w) 1)) := by
      intro w _
      have h1 : |σ * τ * (g (x (t, w) 1) - g (y (t, w) 1))| ≤ L := by
        rw [abs_mul, abs_mul, hσ1, hτ1, one_mul, one_mul]
        exact hZb t w
      exact (abs_le.mp h1).1
    have hcl := conc_lower 𝔼 t ω (D := fun w => σ * D t w)
      (Z := fun w => σ * τ * (g (x (t, w) 1) - g (y (t, w) 1))) (by rw [hc]; linarith)
      (by positivity) hL (by positivity) hD'B hZ1 hZ2
    have hED' : 𝔼.E t (fun w => σ * D t w) ω = |d| := by
      have e : (fun w => σ * D t w) = σ • D t := rfl
      rw [e, map_smul, hDk]
      exact hσd
    have hEZ' : 𝔼.E t (fun w => σ * τ * (g (x (t, w) 1) - g (y (t, w) 1))) ω ≤ B := by
      have e : (fun w => σ * τ * (g (x (t, w) 1) - g (y (t, w) 1))) =
          (σ * τ) • fun w => g (x (t, w) 1) - g (y (t, w) 1) := rfl
      rw [e, map_smul, ← hED t]
      have hb := 𝔼.abs_E_le (fun w => hall (t + 1, w)) t ω
      simp only [Pi.smul_apply, smul_eq_mul]
      calc σ * τ * 𝔼.E t (D (t + 1)) ω ≤ |σ * τ * 𝔼.E t (D (t + 1)) ω| := le_abs_self _
        _ = |𝔼.E t (D (t + 1)) ω| := by rw [abs_mul, abs_mul, hσ1, hτ1, one_mul, one_mul]
        _ ≤ B := hb
    rw [hED'] at hcl
    have hdB : |d| ≤ B := hall (t, ω)
    set η := B - |d| with hη
    have hη0 : 0 ≤ η := by linarith
    have hηδ : η < (α - 1) * B / (k + 1) := by linarith
    have hfrac : (α * c + L) * ((B - |d|) / (B - c)) = α * η + 2 * L / B * η := by
      rw [hc, ← hη]
      field_simp
      ring
    rw [hfrac] at hcl
    have h1 : (α - 1) * B ≤ η * k := by rw [hk]; nlinarith
    have h2 : η * (k + 1) < (α - 1) * B := by
      rwa [lt_div_iff₀ (by positivity)] at hηδ
    nlinarith
  have hI : ∀ t, toP x t 1 = toP y t 1 := fun t => funext fun ω => sub_eq_zero.mp (hD0 (t, ω))
  have hlag : ∀ t ω, lagV u.1 (fun s => x (s, ω)) t 1 = lagV u.1 (fun s => y (s, ω)) t 1 := by
    intro t ω
    cases t with
    | zero => rfl
    | succ s => exact congrFun (hI s) ω
  have hπ : ∀ t, toP x t 0 = toP y t 0 := by
    intro t
    have e1 := hrule x hx t
    have e2 := hrule y hy t
    rw [hI t] at e1
    have hl : (fun ω => h (lagV u.1 (fun s => x (s, ω)) t 1)) =
        fun ω => h (lagV u.1 (fun s => y (s, ω)) t 1) := funext fun ω => by rw [hlag t ω]
    rw [hl] at e1
    have hs : φ • toP x t 0 = φ • toP y t 0 :=
      add_right_cancel (add_right_cancel (e1.symm.trans e2))
    exact smul_right_injective _ hφ hs
  ext ⟨t, ω⟩ i
  fin_cases i
  · exact congrFun (hπ t) ω
  · exact congrFun (hI t) ω

/-- **The boundary rule `φ_π π + ρî + (φ_π + ρ)î³` under every expectation system** (Woodford
(2003), Prop. 2.8, p. 96): for `φ_π ≠ 0`, `|φ_π + ρ| = 1`, without shocks, the exact model has
**exactly one** bounded equilibrium for every initial rate, under every expectation system
(`InertialBoundary.boundary_unit_circle` (c) assumed informational closure). -/
theorem boundary_affine_any {φ ρ : ℝ} (hσ : (φ + ρ) * (φ + ρ) = 1) (hφ : φ ≠ 0)
    (𝔼 : ExpectationSystem Ω) (xm : Fin 2 → ℝ) :
    ∃! x : SProcV (Fin 2) Ω,
      SolvesSV 𝔼 (Finert (InertialBoundary.ruleCubI φ ρ (φ + ρ))) (xm, 0) x := by
  have hΨ : ∀ π i, InertialBoundary.ruleCubI φ ρ (φ + ρ) (π, i) =
      φ * π + (ρ * i + (φ + ρ) * i ^ 3) := fun π i => by
    simp only [InertialBoundary.ruleCubI]
    ring
  have hexp : ∀ i i', |i - i'| + 1 / 4 * |i - i'| ^ 3 ≤
      |(φ * i + (ρ * i + (φ + ρ) * i ^ 3)) - (φ * i' + (ρ * i' + (φ + ρ) * i' ^ 3))| := by
    intro i i'
    have := InertialBoundary.expand_cubic hσ i i'
    convert this using 2
    ring
  have hc : Continuous fun i : ℝ => ρ * i + (φ + ρ) * i ^ 3 := by fun_prop
  have h00 : InertialBoundary.ruleCubI φ ρ (φ + ρ) (0, 0) = 0 := by
    simp [InertialBoundary.ruleCubI]
  have hroot : InertialBoundary.ruleCubI φ ρ (φ + ρ)
      (-(ρ * xm 1 + (φ + ρ) * xm 1 ^ 3) / φ, xm 1) = 0 := by
    rw [hΨ]
    field_simp
    ring
  refine ⟨InertialBoundary.jumpP (-(ρ * xm 1 + (φ + ρ) * xm 1 ^ 3) / φ),
    InertialBoundary.solvesSV_jump h00 hroot, fun y hy => ?_⟩
  exact unique_affine_any 𝔼 hΨ hφ (by norm_num) hc hexp hy
    (InertialBoundary.solvesSV_jump h00 hroot)

/-- **The extension is genuine** (Woodford (2003), Prop. 2.8, p. 96, and p. 633): the skew
expectation system `LocalIFTStochastic.skewSystem` is not informationally closed, yet the
boundary rule `φ_π π + ρî + (φ_π + ρ)î³` has at most one bounded equilibrium for every initial
rate and disturbance process under it (and exactly one without shocks). -/
theorem unique_affine_skew {φ ρ : ℝ} (hσ : (φ + ρ) * (φ + ρ) = 1) (hφ : φ ≠ 0) :
    ¬ LocalIFTStochastic.Ops.InfoClosed LocalIFTStochastic.skewSystem ∧
    (∀ (u : ParS (Fin 2) (Fin 2 → ℝ) (Fin 3)) (x y : SProcV (Fin 2) (Fin 3)),
      SolvesSV LocalIFTStochastic.skewSystem (Finert (InertialBoundary.ruleCubI φ ρ (φ + ρ))) u x →
      SolvesSV LocalIFTStochastic.skewSystem (Finert (InertialBoundary.ruleCubI φ ρ (φ + ρ))) u y →
        x = y) ∧
    ∀ xm : Fin 2 → ℝ, ∃! x : SProcV (Fin 2) (Fin 3),
      SolvesSV LocalIFTStochastic.skewSystem (Finert (InertialBoundary.ruleCubI φ ρ (φ + ρ)))
        (xm, 0) x := by
  have hΨ : ∀ π i, InertialBoundary.ruleCubI φ ρ (φ + ρ) (π, i) =
      φ * π + (ρ * i + (φ + ρ) * i ^ 3) := fun π i => by
    simp only [InertialBoundary.ruleCubI]
    ring
  have hexp : ∀ i i', |i - i'| + 1 / 4 * |i - i'| ^ 3 ≤
      |(φ * i + (ρ * i + (φ + ρ) * i ^ 3)) - (φ * i' + (ρ * i' + (φ + ρ) * i' ^ 3))| := by
    intro i i'
    have := InertialBoundary.expand_cubic hσ i i'
    convert this using 2
    ring
  have hc : Continuous fun i : ℝ => ρ * i + (φ + ρ) * i ^ 3 := by fun_prop
  exact ⟨LocalIFTStochastic.skewSystem_not_infoClosed,
    fun u x y hx hy => unique_affine_any _ hΨ hφ (by norm_num) hc hexp hx hy,
    boundary_affine_any hσ hφ _⟩

/-! ### The cubic rule `ρ î_{−1} + σπ³` -/

/-- Woodford (2003), App. A.3, p. 633 (tool): **with the pull-out property, cubes of known
variables are known** (`E_t(z·z·z) = z·z·E_t z`). -/
theorem cube_known_of_pullOut (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {t : ℕ}
    {z : Ω → ℝ} (hz : 𝔼.E t z = z) : 𝔼.E t (fun ω => z ω ^ 3) = fun ω => z ω ^ 3 := by
  have e : (fun ω => z ω ^ 3) = z * (z * z) := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  rw [e, hpo t z (z * z) hz, hpo t z z hz, hz]

set_option maxHeartbeats 1600000 in
-- the proof reruns `InertialBoundary.unique_cube` with the concentration bound at the end
/-- **Uniqueness on the boundary `φ_π = 0` without informational closure** (Woodford (2003),
Prop. 2.8, p. 96; App. A.3, p. 634): for the rule `Ψ(π, i) = ρ i + σπ³` with `σ² = 1`, `σρ ≥ 1`,
any two bounded adapted equilibria with the same initial rate and disturbances coincide under
**every expectation system in which cubes of known variables are known** (in particular every
system with the pull-out property, `cube_known_of_pullOut`, and every informationally closed
one). The forecast of the bound `∛(4 max(B − σρ D_t, 0))` no longer needs closure: `conc_upper`
bounds it near the supremum of the gap. -/
theorem unique_cube_of_cube_known (𝔼 : ExpectationSystem Ω)
    (hcube : ∀ t (z : Ω → ℝ), 𝔼.E t z = z → 𝔼.E t (fun ω => z ω ^ 3) = fun ω => z ω ^ 3)
    {Ψ : ℝ × ℝ → ℝ} {ρ σ : ℝ} (hΨ : ∀ π i, Ψ (π, i) = ρ * i + σ * π ^ 3) (hσ : σ * σ = 1)
    (hτ : 1 ≤ σ * ρ) {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x y : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (hy : SolvesSV 𝔼 (Finert Ψ) u y) : x = y := by
  have hrule : ∀ z : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) u z → ∀ t,
      toP z t 1 = ρ • (fun ω => lagV u.1 (fun s => z (s, ω)) t 1) +
        σ • (fun ω => toP z t 0 ω ^ 3) + 𝔼.E t (fun ω => u.2 (t, ω) 1) := by
    intro z hz t
    rw [eq1_of_solves hz t]
    have e : (fun ω => Ψ (z (t, ω) 0, lagV u.1 (fun s => z (s, ω)) t 1)) =
        ρ • (fun ω => lagV u.1 (fun s => z (s, ω)) t 1) + σ • (fun ω => toP z t 0 ω ^ 3) := by
      funext ω
      simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [e, map_add, map_smul, map_smul, lag_known hz t, hcube t _ (hz.1 t 0)]
  set D : ℕ → Ω → ℝ := fun t => toP x t 1 - toP y t 1 with hD
  set τ := σ * ρ with hτdef
  have hgap : ∀ t ω, toP x (t + 1) 0 ω ^ 3 - toP y (t + 1) 0 ω ^ 3 =
      σ * D (t + 1) ω - τ * D t ω := by
    intro t ω
    have e1 := congrFun (hrule x hx (t + 1)) ω
    have e2 := congrFun (hrule y hy (t + 1)) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lagV_succ] at e1 e2
    change σ * σ = 1 at hσ
    change _ = σ * (toP x (t + 1) 1 ω - toP y (t + 1) 1 ω) -
      σ * ρ * (toP x t 1 ω - toP y t 1 ω)
    change toP x (t + 1) 1 ω = ρ * toP x t 1 ω + σ * toP x (t + 1) 0 ω ^ 3 + _ at e1
    change toP y (t + 1) 1 ω = ρ * toP y t 1 ω + σ * toP y (t + 1) 0 ω ^ 3 + _ at e2
    rw [e1, e2]
    linear_combination (toP y (t + 1) 0 ω ^ 3 - toP x (t + 1) 0 ω ^ 3) * hσ
  have hEπ : ∀ t, 𝔼.E t (toP x (t + 1) 0 - toP y (t + 1) 0) = D t := by
    intro t
    rw [map_sub, eq0_of_solves hx t, eq0_of_solves hy t]
    change _ = toP x t 1 - toP y t 1
    abel
  have hDk : ∀ t, 𝔼.E t (D t) = D t := fun t => by
    change 𝔼.E t (toP x t 1 - toP y t 1) = toP x t 1 - toP y t 1
    rw [map_sub, hx.1 t 1, hy.1 t 1]
  have hsa : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have hDM : ∀ p : ℕ × Ω, |D p.1 p.2| ≤ ‖x‖ + ‖y‖ := fun p => by
    have h1 := abs_le.mp (abs_apply_le x p.1 p.2 1)
    have h2 := abs_le.mp (abs_apply_le y p.1 p.2 1)
    change |x p 1 - y p 1| ≤ _
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  have hcm := InertialBoundaryExistCube.cbrt_strictMono.monotone
  have hD0 : ∀ p : ℕ × Ω, D p.1 p.2 = 0 := by
    refine eq_zero_of_annulus (fun p : ℕ × Ω => D p.1 p.2) hDM (fun B hB _ hall => ?_)
    set lam := min B (B ^ 3 / 64) with hlam
    have hlam0 : 0 < lam := lt_min hB (by positivity)
    have hlamB : lam ≤ B := min_le_left _ _
    have hlam3 : lam ≤ B ^ 3 / 64 := min_le_right _ _
    set F := cbrt (4 * ((1 + τ) * B)) with hF
    have hF0 : 0 ≤ F := cbrt_nonneg (by nlinarith)
    set δ := B / 2 / (1 + F / lam) / 2 with hδ
    have hq0 : 0 < 1 + F / lam := by positivity
    have hδ0 : 0 < δ := by positivity
    refine ⟨δ, hδ0, fun q _ => ?_⟩
    obtain ⟨t, ω⟩ := q
    by_contra hcon
    push Not at hcon
    set d := D t ω with hd
    have hBn : ∀ ω', |σ * D (t + 1) ω'| ≤ B := fun ω' => by
      rw [abs_mul, hsa, one_mul]
      exact hall (t + 1, ω')
    -- the value of the bound on `{|D_t| ≥ B − λ}`
    have hA : cbrt (4 * max (B - τ * (B - lam)) 0) ≤ B / 2 := by
      refine InertialBoundaryExistCube.cbrt_le_of_le_pow ?_
      have h1 : B - τ * (B - lam) ≤ lam := by nlinarith
      have h2 : max (B - τ * (B - lam)) 0 ≤ lam := max_le h1 hlam0.le
      nlinarith
    have hA0 : 0 ≤ cbrt (4 * max (B - τ * (B - lam)) 0) := cbrt_nonneg (by positivity)
    have hFbig : ∀ w : ℝ, -B ≤ w → cbrt (4 * max (B - τ * w) 0) ≤ F := by
      intro w hw
      refine hcm ?_
      have : max (B - τ * w) 0 ≤ (1 + τ) * B := max_le (by nlinarith) (by nlinarith)
      linarith
    have hkey : ∀ (Dv P : Ω → ℝ), (∀ w, Dv w ≤ B) → (∀ w, -B ≤ Dv w) →
        (∀ w, P w ≤ cbrt (4 * max (B - τ * Dv w) 0)) → 𝔼.E t P ω = 𝔼.E t Dv ω →
        𝔼.E t Dv ω ≤ B - δ := by
      intro Dv P hDB hDl hP hEP
      by_contra hc
      push Not at hc
      have hc' := conc_upper 𝔼 t ω (c := B - lam) (A := cbrt (4 * max (B - τ * (B - lam)) 0))
        (F := F) (by linarith) hA0 hF0 hDB
        (fun w hw => (hP w).trans (hcm (by
          have : B - τ * Dv w ≤ B - τ * (B - lam) := by nlinarith
          have := max_le_max this (le_refl (0 : ℝ))
          linarith)))
        (fun w _ => (hP w).trans (hFbig _ (hDl w)))
      rw [hEP] at hc'
      set η := B - 𝔼.E t Dv ω with hη
      have hη0 : η < δ := by linarith
      have hfr : (B - 𝔼.E t Dv ω) / (B - (B - lam)) = η / lam := by
        rw [hη]
        congr 1
        ring
      rw [hfr] at hc'
      have h1 : B / 2 ≤ η * (1 + F / lam) := by
        have : F * (η / lam) = η * (F / lam) := by ring
        nlinarith
      have h2 : δ * (1 + F / lam) = B / 4 := by
        rw [hδ]
        field_simp
        ring
      have h3 : η * (1 + F / lam) < δ * (1 + F / lam) := mul_lt_mul_of_pos_right hη0 hq0
      linarith
    have hdB : |d| ≤ B := hall (t, ω)
    rcases le_or_gt 0 d with h0 | h0
    · have hup : ∀ ω', (toP x (t + 1) 0 - toP y (t + 1) 0) ω' ≤
          cbrt (4 * max (B - τ * D t ω') 0) := fun ω' => by
        refine sub_le_cbrt ?_
        rw [hgap t ω']
        linarith [(abs_le.mp (hBn ω')).2]
      have := hkey (D t) (toP x (t + 1) 0 - toP y (t + 1) 0)
        (fun w => (le_abs_self _).trans (hall (t, w)))
        (fun w => (neg_abs_le _).trans' (by linarith [hall (t, w)])) hup
        (by rw [hEπ, hDk])
      rw [hDk] at this
      rw [abs_of_nonneg h0] at hcon
      linarith
    · have hlo : ∀ ω', (toP y (t + 1) 0 - toP x (t + 1) 0) ω' ≤
          cbrt (4 * max (B - τ * (-D t ω')) 0) := fun ω' => by
        refine sub_le_cbrt ?_
        have := hgap t ω'
        have h2 := (abs_le.mp (hBn ω')).1
        linarith
      have hneg : (fun w => -D t w) = -D t := rfl
      have := hkey (fun w => -D t w) (toP y (t + 1) 0 - toP x (t + 1) 0)
        (fun w => (neg_le_abs _).trans (hall (t, w)))
        (fun w => by have := le_abs_self (D t w); linarith [hall (t, w)]) hlo
        (by
          rw [hneg, map_neg, show toP y (t + 1) 0 - toP x (t + 1) 0 =
            -(toP x (t + 1) 0 - toP y (t + 1) 0) by abel, map_neg, hEπ, hDk])
      rw [hneg, map_neg, hDk] at this
      simp only [Pi.neg_apply] at this
      rw [abs_of_neg h0] at hcon
      linarith
  have hI : ∀ t, toP x t 1 = toP y t 1 := fun t => funext fun ω => sub_eq_zero.mp (hD0 (t, ω))
  have hπ : ∀ t, toP x t 0 = toP y t 0 := by
    intro t
    funext ω
    have e1 := congrFun (hrule x hx t) ω
    have e2 := congrFun (hrule y hy t) ω
    have hl : lagV u.1 (fun s => x (s, ω)) t 1 = lagV u.1 (fun s => y (s, ω)) t 1 := by
      cases t with
      | zero => rfl
      | succ s => exact congrFun (hI s) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    rw [congrFun (hI t) ω, hl] at e1
    have hcube' : toP x t 0 ω ^ 3 = toP y t 0 ω ^ 3 := by
      have h3 : σ * toP x t 0 ω ^ 3 = σ * toP y t 0 ω ^ 3 := by linarith
      have := congrArg (fun w => σ * w) h3
      rw [← mul_assoc, ← mul_assoc, hσ, one_mul, one_mul] at this
      exact this
    exact (Odd.pow_injective (by decide : Odd 3)) hcube'
  ext ⟨t, ω⟩ i
  fin_cases i
  · exact congrFun (hπ t) ω
  · exact congrFun (hI t) ω

/-- **The cubic rule under every expectation system with the pull-out property** (Woodford
(2003), Prop. 2.8, p. 96): `unique_cube_of_cube_known` with `cube_known_of_pullOut`. -/
theorem unique_cube_pullOut (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {Ψ : ℝ × ℝ → ℝ}
    {ρ σ : ℝ} (hΨ : ∀ π i, Ψ (π, i) = ρ * i + σ * π ^ 3) (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ)
    {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x y : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (hy : SolvesSV 𝔼 (Finert Ψ) u y) : x = y :=
  unique_cube_of_cube_known 𝔼 (fun _ _ hz => cube_known_of_pullOut 𝔼 hpo hz) hΨ hσ hτ hx hy

end Woodford.PriceLevelDetermination.TidyR6InertialAnyExpectation
