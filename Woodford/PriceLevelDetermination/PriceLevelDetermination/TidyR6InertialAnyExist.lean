/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.TidyR6InertialAnyExpectation
import PriceLevelDetermination.InertialBoundaryExist

/-!
# Existence on the boundary of Proposition 2.8 under every expectation system

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 633–634.
`InertialBoundaryExist.exists_unique_affine` constructs the unique equilibrium of the rule
`φ_π π + h(î_{−1})` with small disturbances under informational closure: the backward step
`î_t = g⁻¹(E_t î_{t+1} − f_t)` is computed state by state, and closure makes it known at `t`.
Without closure the step must solve `E_t g(y) = w` for a variable `y` known at `t`; this module
solves it and redoes the construction for **every** expectation system.

## Main results

* `step_solve`: for `w` known at `t`, the equation `E_t g(y) = w` has a solution `y` known at
  `t` (a contraction `y ↦ E_t[y − (τ/Λ) g(y)] + (τ/Λ) w` on the variables known at `t`, using
  that `g` is strictly monotone with slopes in `[1, Λ]` near `0`).
* `step_contract`: two such solutions satisfy `|y − y'| + (κ/4)|y − y'|³ ≤ sup |w − w'|`
  (concentration of `E_t` near the supremum, `TidyR6InertialAnyExpectation.conc_lower`).
* `exists_expanding_any`: a bounded process known at every date with
  `E_t î_{t+1} = E_t g(î_t) + f_t`, as the uniform limit of backward solutions.
* `exists_unique_affine_any`: for every expectation system, the rule `φ_π π + h(î_{−1})` with
  `φ_π ≠ 0`, `h(0) = 0`, `h` locally Lipschitz and the expanding diagonal has **exactly one**
  bounded equilibrium for every initial rate and every disturbance process with
  `(1 + |φ_π|)‖e‖ ≤ (κ/4)R³`, and its interest rate stays within `R`.
* `boundary_affine_any_shocks`: the boundary rule `φ_π π + ρ î + (φ_π + ρ) î³` of
  `InertialBoundary.boundary_unit_circle` (c).
-/

namespace Woodford.PriceLevelDetermination.TidyR6InertialAnyExist

open scoped Topology
open Filter
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic
open TidyR6InertialAnyExpectation (conc_lower exists_sign_of_expanding unique_affine_any)
open LocalIFTSystemsApps (Finert)
open InertialBoundary (eq0_of_solves eq1_of_solves lag_known)
open InertialBoundaryExist (forceA forceA_known abs_forceA_le phi_mono)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Solving `E_t g(y) = w` on the variables known at `t` -/

/-- Woodford (2003), App. A.3, p. 634 (tool): the damped map `m(z) = z − (τ/Λ) g(z)` is a
contraction with factor `1 − 1/Λ` on `[−R, R]` when `τ g` has slopes in `[1, Λ]` there. -/
theorem damp_lip {g : ℝ → ℝ} {τ Λ Rb : ℝ} (hΛ : 1 ≤ Λ)
    (hslope : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → b ≤ a →
      a - b ≤ τ * (g a - g b) ∧ τ * (g a - g b) ≤ Λ * (a - b))
    {a b : ℝ} (ha : |a| ≤ Rb) (hb : |b| ≤ Rb) :
    |(a - τ / Λ * g a) - (b - τ / Λ * g b)| ≤ (1 - 1 / Λ) * |a - b| := by
  have hΛ0 : 0 < Λ := by linarith
  have key : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → b ≤ a →
      |(a - τ / Λ * g a) - (b - τ / Λ * g b)| ≤ (1 - 1 / Λ) * |a - b| := by
    intro a b ha hb hab
    obtain ⟨h1, h2⟩ := hslope a b ha hb hab
    have e : (a - τ / Λ * g a) - (b - τ / Λ * g b) = (a - b) - (τ * (g a - g b)) / Λ := by
      field_simp
      ring
    rw [e, abs_of_nonneg (sub_nonneg.mpr hab)]
    have h3 : (a - b) / Λ ≤ (τ * (g a - g b)) / Λ := div_le_div_of_nonneg_right h1 hΛ0.le
    have h4 : (τ * (g a - g b)) / Λ ≤ a - b := by
      rw [div_le_iff₀ hΛ0]
      linarith
    rw [abs_le]
    constructor
    · have : 0 ≤ (1 - 1 / Λ) * (a - b) := mul_nonneg (by
        rw [sub_nonneg, div_le_one hΛ0]
        exact hΛ) (sub_nonneg.mpr hab)
      linarith
    · have : (1 - 1 / Λ) * (a - b) = (a - b) - (a - b) / Λ := by ring
      linarith
  rcases le_total b a with hab | hab
  · exact key a b ha hb hab
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact key b a hb ha hab

/-- Woodford (2003), App. A.3, p. 634 (tool): a number bounded by `C qⁿ` for every `n`, with
`0 ≤ q < 1`, is zero. -/
theorem eq_zero_of_le_geom {x C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ∀ n : ℕ, |x| ≤ C * q ^ n) :
    x = 0 := by
  have ht : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have := ge_of_tendsto' ht h
  exact abs_nonpos_iff.mp this

/-- Woodford (2003), App. A.3, p. 634 (tool): the iteration `y_{n+1} = E_t m(y_n) + c w` from
`y_0 = 0` for the step equation. -/
noncomputable def stepIter (t : ℕ) (m : ℝ → ℝ) (c : ℝ) (w : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => 𝔼.E t (fun ω' => m (stepIter t m c w n ω')) ω + c * w ω

set_option maxHeartbeats 1600000 in
-- the proof runs the contraction and passes three identities to the limit
/-- **The backward step without informational closure** (Woodford (2003), App. A.3, p. 634): if
`τ g` has slopes in `[1, Λ]` on `[−R_b, R_b]` (`|τ| = 1`, `Λ ≥ 1`) and `w` is known at `t` with
`|w| + |g(0)| ≤ R_b`, there is `y` **known at `t`**, `|y| ≤ R_b`, with `E_t g(y) = w`. -/
theorem step_solve {g : ℝ → ℝ} {τ Λ Rb : ℝ} (hΛ : 1 ≤ Λ) (hτ1 : |τ| = 1) (hRb : 0 ≤ Rb)
    (hslope : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → b ≤ a →
      a - b ≤ τ * (g a - g b) ∧ τ * (g a - g b) ≤ Λ * (a - b))
    (t : ℕ) {w : Ω → ℝ} (hw : 𝔼.E t w = w) (hwb : ∀ ω, |w ω| + |g 0| ≤ Rb) :
    ∃ y : Ω → ℝ, 𝔼.E t y = y ∧ (∀ ω, |y ω| ≤ Rb) ∧ 𝔼.E t (fun ω => g (y ω)) = w := by
  have hΛ0 : 0 < Λ := by linarith
  set m : ℝ → ℝ := fun z => z - τ / Λ * g z with hm
  set c := τ / Λ with hc
  set q := 1 - 1 / Λ with hq
  have hq0 : 0 ≤ q := by rw [hq, sub_nonneg, div_le_one hΛ0]; exact hΛ
  have hq1 : q < 1 := by
    have : 0 < 1 / Λ := by positivity
    rw [hq]
    linarith
  have hca : |c| = 1 / Λ := by rw [hc, abs_div, hτ1, abs_of_pos hΛ0]
  have hmlip : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → |m a - m b| ≤ q * |a - b| :=
    fun a b ha hb => damp_lip hΛ hslope ha hb
  have hglip : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → |g a - g b| ≤ Λ * |a - b| := by
    intro a b ha hb
    have key : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → b ≤ a → |g a - g b| ≤ Λ * |a - b| := by
      intro a b ha hb hab
      obtain ⟨h1, h2⟩ := hslope a b ha hb hab
      have e : |g a - g b| = |τ * (g a - g b)| := by rw [abs_mul, hτ1, one_mul]
      rw [e, abs_of_nonneg (by linarith), abs_of_nonneg (sub_nonneg.mpr hab)]
      exact h2
    rcases le_total b a with hab | hab
    · exact key a b ha hb hab
    · rw [abs_sub_comm, abs_sub_comm a b]
      exact key b a hb ha hab
  have hm0 : |m 0| = |g 0| / Λ := by
    simp only [hm, zero_sub, abs_neg, abs_mul, hca]
    ring
  set y := stepIter 𝔼 t m c w with hy
  have hy0 : ∀ ω, y 0 ω = 0 := fun _ => rfl
  have hysucc : ∀ n ω, y (n + 1) ω = 𝔼.E t (fun ω' => m (y n ω')) ω + c * w ω := fun _ _ => rfl
  have hyfun : ∀ n, y (n + 1) = 𝔼.E t (fun ω' => m (y n ω')) + c • w := fun n => by
    funext ω
    rw [hysucc]
    rfl
  -- the iterates stay in the ball
  have hbd : ∀ n ω, |y n ω| ≤ Rb := by
    intro n
    induction n with
    | zero => intro ω; rw [hy0, abs_zero]; exact hRb
    | succ n ih =>
      intro ω
      have hmb : ∀ ω', |m (y n ω')| ≤ q * Rb + |g 0| / Λ := by
        intro ω'
        have h1 := hmlip (y n ω') 0 (ih ω') (by rw [abs_zero]; exact hRb)
        rw [sub_zero] at h1
        have h2 := abs_sub_abs_le_abs_sub (m (y n ω')) (m 0)
        have h3 : q * |y n ω'| ≤ q * Rb := mul_le_mul_of_nonneg_left (ih ω') hq0
        linarith
      have hE := 𝔼.abs_E_le hmb t ω
      rw [hysucc]
      have hcw : |c * w ω| = |w ω| / Λ := by rw [abs_mul, hca]; ring
      have hw' := hwb ω
      calc |𝔼.E t (fun ω' => m (y n ω')) ω + c * w ω|
          ≤ |𝔼.E t (fun ω' => m (y n ω')) ω| + |c * w ω| := abs_add_le _ _
        _ ≤ q * Rb + |g 0| / Λ + |w ω| / Λ := by rw [hcw]; linarith
        _ = q * Rb + (|w ω| + |g 0|) / Λ := by ring
        _ ≤ q * Rb + Rb / Λ := by
            have := div_le_div_of_nonneg_right hw' hΛ0.le
            linarith
        _ = Rb := by rw [hq]; field_simp; ring
  -- the iterates are known at `t`
  have hkn : ∀ n, 𝔼.E t (y n) = y n := by
    intro n
    cases n with
    | zero =>
      have : y 0 = fun _ => 0 := funext hy0
      rw [this]
      exact 𝔼.const t 0
    | succ n => rw [hyfun, map_add, map_smul, 𝔼.E_E_self, hw]
  -- geometric decay of the steps
  have hdiff : ∀ n ω, |y (n + 1) ω - y n ω| ≤ Rb * q ^ n := by
    intro n
    induction n with
    | zero => intro ω; rw [hy0, sub_zero, pow_zero, mul_one]; exact hbd 1 ω
    | succ n ih =>
      intro ω
      have hpt : ∀ ω', |m (y (n + 1) ω') - m (y n ω')| ≤ q * (Rb * q ^ n) := fun ω' =>
        (hmlip _ _ (hbd _ ω') (hbd _ ω')).trans (mul_le_mul_of_nonneg_left (ih ω') hq0)
      have hE := 𝔼.abs_E_le hpt t ω
      have e : y (n + 1 + 1) ω - y (n + 1) ω =
          𝔼.E t (fun ω' => m (y (n + 1) ω') - m (y n ω')) ω := by
        rw [hysucc, hysucc, show (fun ω' => m (y (n + 1) ω') - m (y n ω')) =
          (fun ω' => m (y (n + 1) ω')) - fun ω' => m (y n ω') from rfl, map_sub]
        simp only [Pi.sub_apply]
        ring
      rw [e, pow_succ]
      calc _ ≤ q * (Rb * q ^ n) := hE
        _ = Rb * (q ^ n * q) := by ring
  -- the limit
  have hcs : ∀ ω, CauchySeq fun n => y n ω := fun ω =>
    cauchySeq_of_le_geometric q Rb hq1 fun n => by
      rw [Real.dist_eq, abs_sub_comm]
      exact hdiff n ω
  choose Y hY using fun ω => cauchySeq_tendsto_of_complete (hcs ω)
  have hYn : ∀ n ω, |y n ω - Y ω| ≤ Rb * q ^ n / (1 - q) := fun n ω => by
    have := dist_le_of_le_geometric_of_tendsto q Rb hq1 (fun n => by
      rw [Real.dist_eq, abs_sub_comm]
      exact hdiff n ω) (hY ω) n
    rwa [Real.dist_eq] at this
  have hq1' : 0 < 1 - q := by linarith
  have hYb : ∀ ω, |Y ω| ≤ Rb := fun ω =>
    le_of_tendsto' ((hY ω).abs) fun n => hbd n ω
  have hYk : 𝔼.E t Y = Y := by
    funext ω
    refine sub_eq_zero.mp (eq_zero_of_le_geom (C := 2 * Rb / (1 - q)) hq0 hq1 fun n => ?_)
    have h1 := 𝔼.abs_E_le (x := Y - y n) (M := Rb * q ^ n / (1 - q)) (fun ω' => by
      change |Y ω' - y n ω'| ≤ _
      rw [abs_sub_comm]
      exact hYn n ω') t ω
    have e : 𝔼.E t Y ω - Y ω = 𝔼.E t (Y - y n) ω + (y n ω - Y ω) := by
      rw [map_sub, hkn n]
      simp only [Pi.sub_apply]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h2 := hYn n ω
    have e3 : 2 * Rb / (1 - q) * q ^ n = Rb * q ^ n / (1 - q) + Rb * q ^ n / (1 - q) := by ring
    rw [e3]
    exact add_le_add h1 h2
  have hYg : 𝔼.E t (fun ω => g (Y ω)) = w := by
    funext ω
    refine sub_eq_zero.mp (eq_zero_of_le_geom
      (C := Λ * Rb / (1 - q) + Λ * Rb) hq0 hq1 fun n => ?_)
    -- the step identity `c (E_t g(y_n) − w) = y_n − y_{n+1}`
    have hst : c * (𝔼.E t (fun ω' => g (y n ω')) ω - w ω) = y n ω - y (n + 1) ω := by
      rw [hysucc]
      have e : (fun ω' => m (y n ω')) = y n - c • fun ω' => g (y n ω') := by
        funext ω'
        simp only [hm, hc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e, map_sub, map_smul, hkn n]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hst' : |𝔼.E t (fun ω' => g (y n ω')) ω - w ω| ≤ Λ * (Rb * q ^ n) := by
      have h1 : |c| * |𝔼.E t (fun ω' => g (y n ω')) ω - w ω| ≤ Rb * q ^ n := by
        rw [← abs_mul, hst, abs_sub_comm]
        exact hdiff n ω
      rw [hca] at h1
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hΛ0] at h1
      linarith
    have hgl : ∀ ω', |g (Y ω') - g (y n ω')| ≤ Λ * (Rb * q ^ n / (1 - q)) := fun ω' =>
      (hglip _ _ (hYb ω') (hbd n ω')).trans (mul_le_mul_of_nonneg_left (by
        rw [abs_sub_comm]
        exact hYn n ω') hΛ0.le)
    have hE := 𝔼.abs_E_le hgl t ω
    have e : 𝔼.E t (fun ω => g (Y ω)) ω - w ω =
        𝔼.E t (fun ω' => g (Y ω') - g (y n ω')) ω +
          (𝔼.E t (fun ω' => g (y n ω')) ω - w ω) := by
      rw [show (fun ω' => g (Y ω') - g (y n ω')) =
        (fun ω' => g (Y ω')) - fun ω' => g (y n ω') from rfl, map_sub]
      simp only [Pi.sub_apply]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have e3 : (Λ * Rb / (1 - q) + Λ * Rb) * q ^ n =
        Λ * (Rb * q ^ n / (1 - q)) + Λ * (Rb * q ^ n) := by ring
    rw [e3]
    exact add_le_add hE hst'
  exact ⟨Y, hYk, hYb, hYg⟩

/-! ### Two step solutions are close when their targets are close -/

set_option maxHeartbeats 1600000 in
-- the concentration bound is applied at a state near the supremum of the gap
/-- **The backward step is a weak contraction without informational closure** (Woodford (2003),
App. A.3, p. 634): let `τ(g(a) − g(b)) ≥ (a − b) + κ(a − b)³` for `a ≥ b`, and let `y, y'` be
known at `t` with bounded gap, `|g(y) − g(y')| ≤ L`, and `|E_t[g(y) − g(y')]| ≤ d`. Then
`|y − y'| + (κ/4)|y − y'|³ ≤ d` in every state. -/
theorem step_contract [Nonempty Ω] {g : ℝ → ℝ} {τ κ L : ℝ} (hτ1 : |τ| = 1) (hκ : 0 < κ)
    (hL : 0 ≤ L) (hexpτ : ∀ a b, b ≤ a → (a - b) + κ * (a - b) ^ 3 ≤ τ * (g a - g b))
    {t : ℕ} {y y' : Ω → ℝ} (hy : 𝔼.E t y = y) (hy' : 𝔼.E t y' = y')
    (hbd : BddAbove (Set.range fun ω => |y ω - y' ω|))
    (hgL : ∀ ω, |g (y ω) - g (y' ω)| ≤ L) {d : ℝ}
    (hd : ∀ ω, |𝔼.E t (fun ω' => g (y ω') - g (y' ω')) ω| ≤ d) (ω : Ω) :
    |y ω - y' ω| + κ / 4 * |y ω - y' ω| ^ 3 ≤ d := by
  set e := ⨆ ω, |y ω - y' ω| with he
  have hle : ∀ ω, |y ω - y' ω| ≤ e := fun ω => le_ciSup hbd ω
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have he0 : 0 ≤ e := (abs_nonneg _).trans (hle ω₀)
  have hd0 : 0 ≤ d := (abs_nonneg _).trans (hd ω₀)
  have hmain : e + κ / 4 * e ^ 3 ≤ d := by
    by_contra hc
    push Not at hc
    have hepos : 0 < e := by
      rcases he0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hc
        simp at hc
        linarith
    set c := e / 2 with hcdef
    have hc0 : 0 < c := by positivity
    set α := 1 + κ * c ^ 2 with hα
    have hα0 : 0 ≤ α := by positivity
    have hαe : α * e = e + κ / 4 * e ^ 3 := by rw [hα, hcdef]; ring
    set gap := α * e - d with hgap
    have hgap0 : 0 < gap := by rw [hgap, hαe]; linarith
    set K := α + 2 * (α * c + L) / e with hK
    have hK0 : 0 ≤ K := by positivity
    set η := gap / (K + 1) with hη
    have hη0 : 0 < η := by positivity
    have hηK : η * (K + 1) = gap := by rw [hη]; field_simp
    obtain ⟨ω₁, hω₁⟩ := exists_lt_of_lt_ciSup (show e - η < e by linarith)
    change e - η < |y ω₁ - y' ω₁| at hω₁
    obtain ⟨σ, hσ1, hσd, hσc⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        σ * (y ω₁ - y' ω₁) = |y ω₁ - y' ω₁| ∧ |σ| = 1 := by
      rcases le_or_gt 0 (y ω₁ - y' ω₁) with h0 | h0
      · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h0], abs_one⟩
      · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h0]; ring, by norm_num⟩
    have hD' : ∀ w, σ * (y w - y' w) ≤ e := fun w =>
      (le_abs_self _).trans (by rw [abs_mul, hσc, one_mul]; exact hle w)
    have hZ1 : ∀ w, c ≤ σ * (y w - y' w) →
        α * (σ * (y w - y' w)) ≤ σ * τ * (g (y w) - g (y' w)) := by
      intro w hw
      have hpos : 0 < σ * (y w - y' w) := lt_of_lt_of_le hc0 hw
      have hc2 : c ^ 2 ≤ (σ * (y w - y' w)) ^ 2 := pow_le_pow_left₀ hc0.le hw 2
      have hk : 0 ≤ κ * (σ * (y w - y' w)) * ((σ * (y w - y' w)) ^ 2 - c ^ 2) :=
        mul_nonneg (mul_nonneg hκ.le hpos.le) (sub_nonneg.mpr hc2)
      rcases hσ1 with h1 | h1
      · rw [h1] at hpos hk ⊢
        have := hexpτ (y w) (y' w) (by linarith)
        rw [hα]
        nlinarith
      · rw [h1] at hpos hk ⊢
        have := hexpτ (y' w) (y w) (by linarith)
        rw [hα]
        nlinarith
    have hZ2 : ∀ w, σ * (y w - y' w) < c → -L ≤ σ * τ * (g (y w) - g (y' w)) := by
      intro w _
      have h1 : |σ * τ * (g (y w) - g (y' w))| ≤ L := by
        rw [abs_mul, abs_mul, hσc, hτ1, one_mul, one_mul]
        exact hgL w
      exact (abs_le.mp h1).1
    have hcl := conc_lower 𝔼 t ω₁ (D := fun w => σ * (y w - y' w))
      (Z := fun w => σ * τ * (g (y w) - g (y' w))) (by rw [hcdef]; linarith) hα0 hL hc0.le hD'
      hZ1 hZ2
    have hED : 𝔼.E t (fun w => σ * (y w - y' w)) ω₁ = |y ω₁ - y' ω₁| := by
      have e1 : (fun w => σ * (y w - y' w)) = σ • (y - y') := rfl
      rw [e1, map_smul, map_sub, hy, hy']
      exact hσd
    have hEZ : 𝔼.E t (fun w => σ * τ * (g (y w) - g (y' w))) ω₁ ≤ d := by
      have e1 : (fun w => σ * τ * (g (y w) - g (y' w))) =
          (σ * τ) • fun w => g (y w) - g (y' w) := rfl
      rw [e1, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      calc σ * τ * 𝔼.E t (fun w => g (y w) - g (y' w)) ω₁
          ≤ |σ * τ * 𝔼.E t (fun w => g (y w) - g (y' w)) ω₁| := le_abs_self _
        _ = |𝔼.E t (fun w => g (y w) - g (y' w)) ω₁| := by
            rw [abs_mul, abs_mul, hσc, hτ1, one_mul, one_mul]
        _ ≤ d := hd ω₁
    rw [hED] at hcl
    set s := |y ω₁ - y' ω₁| with hs
    have hse : s ≤ e := hle ω₁
    have hfrac : (α * c + L) * ((e - s) / (e - c)) ≤ (α * c + L) * (2 * η / e) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hcdef, show e - e / 2 = e / 2 by ring, div_le_div_iff₀ (by positivity) hepos]
      nlinarith
    have h2 : (α * c + L) * (2 * η / e) = η * (K - α) := by
      rw [hK]
      field_simp
      ring
    have h3 : α * (e - η) ≤ α * s := mul_le_mul_of_nonneg_left (by linarith) hα0
    nlinarith
  have hΦ := phi_mono (κ := κ / 4) (by positivity) (hle ω)
  have hΦ' : |y ω - y' ω| + κ / 4 * |y ω - y' ω| ^ 3 ≤ e + κ / 4 * e ^ 3 := hΦ
  linarith

/-! ### The backward construction -/

/-- Woodford (2003), App. A.3, p. 634 (the construction): a solution `y`, known at `t` and
within `R_b`, of `E_t g(y) = w` (chosen by `Classical.epsilon`; it exists by `step_solve`). -/
noncomputable def stepMap (g : ℝ → ℝ) (Rb : ℝ) (t : ℕ) (w : Ω → ℝ) : Ω → ℝ :=
  Classical.epsilon fun y : Ω → ℝ =>
    𝔼.E t y = y ∧ (∀ ω, |y ω| ≤ Rb) ∧ 𝔼.E t (fun ω => g (y ω)) = w

/-- Woodford (2003), App. A.3, p. 634 (the construction): the backward solution with horizon
`t + k`, `V_0 = 0`, `E_t g(V_{k+1}(t)) = E_t V_k(t + 1) − f_t`. -/
noncomputable def backV (g : ℝ → ℝ) (Rb : ℝ) (f : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0, _ => fun _ => 0
  | k + 1, t => stepMap 𝔼 g Rb t (𝔼.E t (backV g Rb f k (t + 1)) - f t)

set_option maxHeartbeats 3200000 in
-- the proof follows `InertialBoundaryExist.exists_expanding` with the closure-free step
/-- **Existence for expanding forward recursions under every expectation system** (Woodford
(2003), App. A.3, p. 634): let `g` be continuous with `g(0) = 0`, uniformly expanding
(`|g(a) − g(b)| ≥ |a − b| + κ|a − b|³`) and Lipschitz on `[−(R + F₀), R + F₀]`, and let `f_t` be
known at `t` with `|f_t| ≤ F₀ ≤ (κ/4)R³`. Then on any nonempty state space, for **every**
expectation system there is a process `î`, known at every date, with `|î_t| ≤ R` and
`E_t î_{t+1} = E_t g(î_t) + f_t`. -/
theorem exists_expanding_any [Nonempty Ω] {g : ℝ → ℝ} {κ R F0 : ℝ} (hgc : Continuous g)
    (hκ : 0 < κ) (hR : 0 ≤ R) (hg0 : g 0 = 0)
    (hexp : ∀ a b, |a - b| + κ * |a - b| ^ 3 ≤ |g a - g b|)
    (hlip : ∃ Λ, ∀ a b, |a| ≤ R + F0 → |b| ≤ R + F0 → |g a - g b| ≤ Λ * |a - b|)
    (hF0 : 0 ≤ F0) (hsmall : F0 ≤ κ / 4 * R ^ 3)
    {f : ℕ → Ω → ℝ} (hfk : ∀ t, 𝔼.E t (f t) = f t) (hfb : ∀ t ω, |f t ω| ≤ F0) :
    ∃ i : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (i t) = i t) ∧ (∀ t ω, |i t ω| ≤ R) ∧
      ∀ t, 𝔼.E t (i (t + 1)) = 𝔼.E t (fun ω => g (i t ω)) + f t := by
  obtain ⟨τ, hτ1, hτ⟩ := exists_sign_of_expanding hgc hκ hexp
  obtain ⟨Λ0, hΛ0⟩ := hlip
  set Rb := R + F0 with hRb
  have hRb0 : 0 ≤ Rb := by positivity
  set Λ := max Λ0 1 with hΛ
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hexpτ : ∀ a b, b ≤ a → (a - b) + κ * (a - b) ^ 3 ≤ τ * (g a - g b) := by
    intro a b hab
    rcases hab.lt_or_eq with h | h
    · have hp := hτ a b h
      have e : τ * (g a - g b) = |g a - g b| := by
        rw [← abs_of_pos hp, abs_mul, hτ1, one_mul]
      rw [e]
      have := hexp a b
      rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at this
    · rw [h, sub_self]
      simp
  have hslope : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → b ≤ a →
      a - b ≤ τ * (g a - g b) ∧ τ * (g a - g b) ≤ Λ * (a - b) := by
    intro a b ha hb hab
    have h1 := hexpτ a b hab
    have h3 : 0 ≤ κ * (a - b) ^ 3 := mul_nonneg hκ.le (pow_nonneg (sub_nonneg.mpr hab) 3)
    refine ⟨by linarith, ?_⟩
    have h4 : τ * (g a - g b) ≤ |g a - g b| := by
      calc τ * (g a - g b) ≤ |τ * (g a - g b)| := le_abs_self _
        _ = |g a - g b| := by rw [abs_mul, hτ1, one_mul]
    have h5 := hΛ0 a b ha hb
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h5
    have h6 : Λ0 * (a - b) ≤ Λ * (a - b) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_nonneg.mpr hab)
    linarith
  have hglip : ∀ a b, |a| ≤ Rb → |b| ≤ Rb → |g a - g b| ≤ Λ * |a - b| := fun a b ha hb =>
    (hΛ0 a b ha hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  set V := backV 𝔼 g Rb f with hV
  have hV0 : ∀ t, V 0 t = fun _ => 0 := fun _ => rfl
  have hVs : ∀ k t, V (k + 1) t = stepMap 𝔼 g Rb t (𝔼.E t (V k (t + 1)) - f t) :=
    fun _ _ => rfl
  -- the invariant: known, within `R`, and the step equation
  have hinv : ∀ k t, 𝔼.E t (V k t) = V k t ∧ (∀ ω, |V k t ω| ≤ R) := by
    intro k
    induction k with
    | zero =>
      intro t
      rw [hV0]
      exact ⟨𝔼.const t 0, fun _ => by rw [abs_zero]; exact hR⟩
    | succ k ih =>
      intro t
      set w := 𝔼.E t (V k (t + 1)) - f t with hw
      have hwk : 𝔼.E t w = w := by rw [hw, map_sub, 𝔼.E_E_self, hfk]
      have hwb : ∀ ω, |w ω| ≤ R + F0 := fun ω => by
        have h1 := 𝔼.abs_E_le (fun ω' => (ih (t + 1)).2 ω') t ω
        simp only [hw, Pi.sub_apply]
        exact (abs_sub _ _).trans (add_le_add h1 (hfb t ω))
      have hex := step_solve 𝔼 hΛ1 hτ1 hRb0 hslope t hwk (fun ω => by
        rw [hg0, abs_zero, add_zero]
        exact hwb ω)
      have hspec : 𝔼.E t (stepMap 𝔼 g Rb t w) = stepMap 𝔼 g Rb t w ∧
          (∀ ω, |stepMap 𝔼 g Rb t w ω| ≤ Rb) ∧
          𝔼.E t (fun ω => g (stepMap 𝔼 g Rb t w ω)) = w := Classical.epsilon_spec hex
      rw [hVs]
      obtain ⟨hk, hb, he⟩ := hspec
      refine ⟨hk, fun ω => ?_⟩
      -- compare with the solution `0` of `E_t g(0) = 0`
      have hc := step_contract 𝔼 (y' := fun _ => 0) (L := Λ * Rb) hτ1 hκ (by positivity)
        hexpτ hk (𝔼.const t 0)
        ⟨Rb, by rintro _ ⟨ω', rfl⟩; simp only [sub_zero]; exact hb ω'⟩
        (fun ω' => by
          have := hglip _ _ (hb ω') (by rw [abs_zero]; exact hRb0)
          rw [sub_zero] at this
          exact this.trans (mul_le_mul_of_nonneg_left (hb ω') (by linarith)))
        (d := R + F0) (fun ω' => by
          have e : (fun ω'' => g (stepMap 𝔼 g Rb t w ω'') - g ((fun _ => (0 : ℝ)) ω'')) =
              fun ω'' => g (stepMap 𝔼 g Rb t w ω'') := by
            funext ω''
            simp only [hg0, sub_zero]
          rw [e, he]
          exact hwb ω') ω
      simp only [sub_zero] at hc
      by_contra hcon
      push Not at hcon
      have h3 : R ^ 3 < |stepMap 𝔼 g Rb t w ω| ^ 3 := pow_lt_pow_left₀ hcon hR (by norm_num)
      have h4 := mul_lt_mul_of_pos_left h3 (by positivity : (0 : ℝ) < κ / 4)
      linarith
  have hstepeq : ∀ k t, 𝔼.E t (fun ω => g (V (k + 1) t ω)) = 𝔼.E t (V k (t + 1)) - f t := by
    intro k t
    set w := 𝔼.E t (V k (t + 1)) - f t with hw
    have hwk : 𝔼.E t w = w := by rw [hw, map_sub, 𝔼.E_E_self, hfk]
    have hwb : ∀ ω, |w ω| ≤ R + F0 := fun ω => by
      have h1 := 𝔼.abs_E_le (fun ω' => (hinv k (t + 1)).2 ω') t ω
      simp only [hw, Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add h1 (hfb t ω))
    have hex := step_solve 𝔼 hΛ1 hτ1 hRb0 hslope t hwk (fun ω => by
      rw [hg0, abs_zero, add_zero]
      exact hwb ω)
    exact (Classical.epsilon_spec hex).2.2
  -- the Cauchy property
  set dk : ℕ → ℝ := fun k => ⨆ p : ℕ × Ω × ℕ, |V k p.1 p.2.1 - V (k + p.2.2) p.1 p.2.1| with hdk
  have hbdd : ∀ k, BddAbove (Set.range fun p : ℕ × Ω × ℕ =>
      |V k p.1 p.2.1 - V (k + p.2.2) p.1 p.2.1|) := fun k =>
    ⟨2 * R, by
      rintro _ ⟨p, rfl⟩
      exact (abs_sub _ _).trans
        (by linarith [(hinv k p.1).2 p.2.1, (hinv (k + p.2.2) p.1).2 p.2.1])⟩
  have hle : ∀ k t ω m, |V k t ω - V (k + m) t ω| ≤ dk k :=
    fun k t ω m => le_ciSup (hbdd k) (t, ω, m)
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hd0 : ∀ k, 0 ≤ dk k := fun k => (abs_nonneg _).trans (hle k 0 ω₀ 0)
  set Φ : ℝ → ℝ := fun x => x + κ / 4 * x ^ 3 with hΦ
  have hΦm : Monotone Φ := phi_mono (by positivity)
  have hΦc : Continuous Φ := by fun_prop
  have hstep : ∀ k, Φ (dk (k + 1)) ≤ dk k := by
    intro k
    rw [hdk, hΦm.map_ciSup_of_continuousAt hΦc.continuousAt (hbdd (k + 1))]
    refine ciSup_le fun p => ?_
    obtain ⟨t, ω, m⟩ := p
    have hk1 := hinv (k + 1) t
    have hk2 := hinv (k + m + 1) t
    have hc := step_contract 𝔼 (y := V (k + 1) t) (y' := V (k + m + 1) t) (L := Λ * (2 * R))
      hτ1 hκ (by positivity) hexpτ hk1.1 hk2.1
      ⟨2 * R, by
        rintro _ ⟨ω', rfl⟩
        exact (abs_sub _ _).trans (by linarith [hk1.2 ω', hk2.2 ω'])⟩
      (fun ω' => (hglip _ _ ((hk1.2 ω').trans (by linarith)) ((hk2.2 ω').trans (by linarith))).trans
        (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hk1.2 ω', hk2.2 ω']))
          (by linarith)))
      (d := dk k) (fun ω' => by
        have e : (fun ω'' => g (V (k + 1) t ω'') - g (V (k + m + 1) t ω'')) =
            (fun ω'' => g (V (k + 1) t ω'')) - fun ω'' => g (V (k + m + 1) t ω'') := rfl
        rw [e, map_sub, hstepeq, hstepeq]
        have e2 : (𝔼.E t (V k (t + 1)) - f t - (𝔼.E t (V (k + m) (t + 1)) - f t)) ω' =
            𝔼.E t (V k (t + 1) - V (k + m) (t + 1)) ω' := by
          rw [map_sub]
          simp only [Pi.sub_apply]
          ring
        rw [e2]
        exact 𝔼.abs_E_le (fun ω'' => hle k (t + 1) ω'' m) t ω') ω
    change Φ |V (k + 1) t ω - V (k + 1 + m) t ω| ≤ _
    rw [show k + 1 + m = k + m + 1 by omega]
    exact hc
  have hanti : Antitone dk := antitone_nat_of_succ_le fun k => by
    have := hstep k
    have : 0 ≤ κ / 4 * dk (k + 1) ^ 3 := mul_nonneg (by positivity) (pow_nonneg (hd0 _) 3)
    simp only [hΦ] at *
    linarith
  have hbb : BddBelow (Set.range dk) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hd0 k⟩
  set Lm := ⨅ k, dk k with hLm
  have hL0 : 0 ≤ Lm := le_ciInf hd0
  have hΦL : Φ Lm ≤ Lm := le_ciInf fun k =>
    (hΦm (ciInf_le hbb (k + 1))).trans (hstep k)
  have hLz : Lm = 0 := by
    simp only [hΦ] at hΦL
    have : κ / 4 * Lm ^ 3 ≤ 0 := by linarith
    rcases hL0.lt_or_eq with h | h
    · have : 0 < κ / 4 * Lm ^ 3 := by positivity
      linarith
    · exact h.symm
  have hd : Tendsto dk atTop (𝓝 0) := by
    rw [← hLz]
    exact tendsto_atTop_ciInf hanti hbb
  -- the limit
  have hcs : ∀ t ω, CauchySeq fun k => V k t ω := fun t ω =>
    cauchySeq_of_le_tendsto_0 (fun N => 2 * dk N) (fun n m N hn hm => by
      rw [Real.dist_eq]
      have h1 := hle N t ω (n - N)
      have h2 := hle N t ω (m - N)
      rw [show N + (n - N) = n by omega] at h1
      rw [show N + (m - N) = m by omega] at h2
      refine (abs_sub_le _ (V N t ω) _).trans ?_
      rw [abs_sub_comm (V n t ω)]
      linarith) (by simpa using hd.const_mul 2)
  choose lim hlim using fun t ω => cauchySeq_tendsto_of_complete (hcs t ω)
  have hunif : ∀ k t ω, |V k t ω - lim t ω| ≤ dk k := by
    intro k t ω
    have ht : Tendsto (fun m => |V k t ω - V (m + k) t ω|) atTop (𝓝 |V k t ω - lim t ω|) :=
      (tendsto_const_nhds.sub ((hlim t ω).comp (tendsto_add_atTop_nat k))).abs
    refine le_of_tendsto' ht fun m => ?_
    have := hle k t ω m
    rwa [add_comm k m] at this
  have hlimb : ∀ t ω, |lim t ω| ≤ R := fun t ω =>
    le_of_tendsto' (hlim t ω).abs fun k => (hinv k t).2 ω
  refine ⟨lim, fun t => ?_, hlimb, fun t => ?_⟩
  · funext ω
    have hb : ∀ k, |𝔼.E t (lim t) ω - lim t ω| ≤ 2 * dk k := by
      intro k
      have h1 : |𝔼.E t (lim t - V k t) ω| ≤ dk k :=
        𝔼.abs_E_le (fun ω' => by
          simp only [Pi.sub_apply]
          rw [abs_sub_comm]
          exact hunif k t ω') t ω
      have e : 𝔼.E t (lim t) ω - lim t ω =
          𝔼.E t (lim t - V k t) ω + (V k t ω - lim t ω) := by
        rw [map_sub, (hinv k t).1]
        simp only [Pi.sub_apply]
        ring
      rw [e]
      exact (abs_add_le _ _).trans (by linarith [hunif k t ω])
    have h0 := ge_of_tendsto' (hd.const_mul 2) hb
    rw [mul_zero] at h0
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)
  · funext ω
    have ha : Tendsto (fun k => 𝔼.E t (fun ω' => g (V (k + 1) t ω')) ω) atTop
        (𝓝 (𝔼.E t (fun ω' => g (lim t ω')) ω)) := by
      have hd1 : Tendsto (fun k => Λ * dk (k + 1)) atTop (𝓝 0) := by
        have := (hd.comp (tendsto_add_atTop_nat 1)).const_mul Λ
        simpa using this
      refine tendsto_iff_dist_tendsto_zero.mpr
        (squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hd1)
      rw [Real.dist_eq]
      have e : 𝔼.E t (fun ω' => g (V (k + 1) t ω')) ω - 𝔼.E t (fun ω' => g (lim t ω')) ω =
          𝔼.E t (fun ω' => g (V (k + 1) t ω') - g (lim t ω')) ω := by
        rw [show (fun ω' => g (V (k + 1) t ω') - g (lim t ω')) =
          (fun ω' => g (V (k + 1) t ω')) - fun ω' => g (lim t ω') from rfl, map_sub]
        rfl
      rw [e]
      refine 𝔼.abs_E_le (fun ω' => ?_) t ω
      refine (hglip _ _ (((hinv (k + 1) t).2 ω').trans (by linarith))
        ((hlimb t ω').trans (by linarith))).trans ?_
      exact mul_le_mul_of_nonneg_left (hunif (k + 1) t ω') (by linarith)
    have hb : Tendsto (fun k => 𝔼.E t (V k (t + 1)) ω - f t ω) atTop
        (𝓝 (𝔼.E t (lim (t + 1)) ω - f t ω)) := by
      refine Tendsto.sub_const ?_ _
      refine tendsto_iff_dist_tendsto_zero.mpr
        (squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hd)
      rw [Real.dist_eq]
      have e : 𝔼.E t (V k (t + 1)) ω - 𝔼.E t (lim (t + 1)) ω =
          𝔼.E t (V k (t + 1) - lim (t + 1)) ω := by
        rw [map_sub]
        rfl
      rw [e]
      exact 𝔼.abs_E_le (fun ω' => hunif k (t + 1) ω') t ω
    have hab : (fun k => 𝔼.E t (fun ω' => g (V (k + 1) t ω')) ω) =
        fun k => 𝔼.E t (V k (t + 1)) ω - f t ω := funext fun k => by
      rw [hstepeq]
      rfl
    rw [hab] at ha
    have := tendsto_nhds_unique hb ha
    simp only [Pi.add_apply]
    linarith

/-! ### The affine-in-inflation rule under every expectation system -/

set_option maxHeartbeats 1600000 in
-- the verification of the two conditions unfolds the constructed process
/-- **Existence and uniqueness on the boundary `φ_π ≠ 0` with small disturbances, under every
expectation system** (Woodford (2003), Prop. 2.8, p. 96; App. A.3, pp. 632–634): on any nonempty
state space and for **every** expectation system (no informational closure, no pull-out
property), for the rule `Ψ(π, i) = φ_π π + h(i)` with `φ_π ≠ 0`, `h(0) = 0`, `h` Lipschitz on
bounded intervals, and the expanding diagonal `|g(i) − g(i')| ≥ |i − i'| + κ|i − i'|³`, for every
initial rate and every disturbance process with `(1 + |φ_π|)‖e‖ ≤ (κ/4)R³` there is **exactly
one** bounded adapted equilibrium, and its interest rate stays within `R` of the steady state.
Inflation is `π_t = (î_t − E_t h(î_{t−1}) − E_t ν_t)/φ_π`; without closure `E_t h(î_{t−1})` need
not equal `h(î_{t−1})`, and the interest rate solves `E_t î_{t+1} = E_t g(î_t) + f_t`
(`exists_expanding_any`). -/
theorem exists_unique_affine_any [Nonempty Ω] {Ψ : ℝ × ℝ → ℝ} {φ κ R : ℝ} {h : ℝ → ℝ}
    (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) (hφ : φ ≠ 0) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hhc : Continuous h) (hh0 : h 0 = 0)
    (hlip : ∀ B, ∃ Λ, ∀ a b, |a| ≤ B → |b| ≤ B → |h a - h b| ≤ Λ * |a - b|)
    (hexp : ∀ i i', |i - i'| + κ * |i - i'| ^ 3 ≤ |(φ * i + h i) - (φ * i' + h i')|)
    (xm : Fin 2 → ℝ) (e : LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ))
    (he : (1 + |φ|) * ‖e‖ ≤ κ / 4 * R ^ 3) :
    ∃ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) (xm, e) x ∧ (∀ t ω, |x (t, ω) 1| ≤ R) ∧
      ∀ y : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) (xm, e) y → y = x := by
  set g : ℝ → ℝ := fun z => φ * z + h z with hg
  have hgc : Continuous g := (continuous_const.mul continuous_id).add hhc
  have hg0 : g 0 = 0 := by simp only [hg, mul_zero, hh0, add_zero]
  set F0 := (1 + |φ|) * ‖e‖ with hF0
  have hF00 : 0 ≤ F0 := by positivity
  have hglip : ∃ Λ, ∀ a b, |a| ≤ R + F0 → |b| ≤ R + F0 → |g a - g b| ≤ Λ * |a - b| := by
    obtain ⟨Λ, hΛ⟩ := hlip (R + F0)
    refine ⟨|φ| + Λ, fun a b ha hb => ?_⟩
    have e1 : g a - g b = φ * (a - b) + (h a - h b) := by simp only [hg]; ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, add_mul]
    linarith [hΛ a b ha hb]
  obtain ⟨i, hik, hib, hirec⟩ := exists_expanding_any 𝔼 hgc hκ hR hg0 hexp hglip hF00 he
    (forceA_known 𝔼 φ e) (abs_forceA_le 𝔼 φ e)
  set lagI : ℕ → Ω → ℝ := fun t ω => lagV (xm 1) (fun s => i s ω) t with hlagI
  set ν : ℕ → Ω → ℝ := fun t ω => e (t, ω) 1 with hν
  set pz : ℕ → Ω → ℝ :=
    fun t ω => (i t ω - 𝔼.E t (fun ω' => h (lagI t ω')) ω - 𝔼.E t (ν t) ω) / φ with hpz
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hhc.continuousOn
  have hhl : ∀ t ω, |h (lagI t ω)| ≤ max C |h (xm 1)| := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t =>
      have := hC (i t ω) (abs_le.mp (hib t ω) |> fun h' => ⟨h'.1, h'.2⟩)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
  have habs : ∀ p j, |e p j| ≤ ‖e‖ := fun p j => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ j).trans (LocalIFTStochastic.norm_apply_le e p)
  set Bp := (R + max C |h (xm 1)| + ‖e‖) / |φ| with hBp
  have hpzb : ∀ t ω, |pz t ω| ≤ Bp := by
    intro t ω
    have h3 := 𝔼.abs_E_le (fun ω' => habs (t, ω') 1) t ω
    have h4 := 𝔼.abs_E_le (fun ω' => hhl t ω') t ω
    simp only [hpz, abs_div]
    rw [hBp]
    refine div_le_div_of_nonneg_right ((abs_sub _ _).trans ?_) (abs_nonneg φ)
    exact add_le_add ((abs_sub _ _).trans (add_le_add (hib t ω) h4)) h3
  set x : SProcV (Fin 2) Ω := LocalIFTStochastic.mkB (fun p => ![pz p.1 p.2, i p.1 p.2])
    ⟨max Bp R, fun p => (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans
      ((hib p.1 p.2).trans (le_max_right _ _)))).mpr fun j => by
        rw [Real.norm_eq_abs]
        fin_cases j
        · exact (hpzb p.1 p.2).trans (le_max_left _ _)
        · exact (hib p.1 p.2).trans (le_max_right _ _)⟩ with hx
  have hpzf : ∀ t, pz t = φ⁻¹ • (i t - 𝔼.E t (fun ω => h (lagI t ω)) - 𝔼.E t (ν t)) := by
    intro t
    funext ω
    simp only [hpz, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
  have hpzk : ∀ t, 𝔼.E t (pz t) = pz t := by
    intro t
    rw [hpzf, map_smul, map_sub, map_sub, hik, 𝔼.E_E_self, 𝔼.E_E_self]
  have hsol : SolvesSV 𝔼 (Finert Ψ) (xm, e) x := by
    refine ⟨fun t j => ?_, fun t j => ?_⟩
    · fin_cases j
      · exact hpzk t
      · exact hik t
    · fin_cases j
      · -- the Fisher equation
        have hf : (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 0) =
            i t - pz (t + 1) - fun ω => e (t, ω) 0 := rfl
        change 𝔼.E t (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x)
          (t, ω)) 0) = 0
        have hlag1 : (fun ω => h (lagI (t + 1) ω)) = fun ω => h (i t ω) := rfl
        have hEg : 𝔼.E t (fun ω => g (i t ω)) = φ • i t + 𝔼.E t (fun ω => h (i t ω)) := by
          have e1 : (fun ω => g (i t ω)) = φ • i t + fun ω => h (i t ω) := by
            funext ω
            simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [e1, map_add, map_smul, hik]
        have hEpz : 𝔼.E t (pz (t + 1)) = i t - 𝔼.E t (fun ω => e (t, ω) 0) := by
          rw [hpzf, map_smul, map_sub, map_sub, hirec, hlag1, 𝔼.tower (Nat.le_succ t),
            𝔼.tower (Nat.le_succ t), hEg]
          funext ω
          simp only [forceA, hν, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
          field_simp
          ring
        rw [hf, map_sub, map_sub, hik, hEpz]
        funext ω
        simp
      · -- the rule
        have hf : (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x) (t, ω)) 1) =
            i t - (φ • pz t + fun ω => h (lagI t ω)) - ν t := by
          funext ω
          have hl : lagV xm (fun s => x (s, ω)) t 1 = lagI t ω := by
            cases t <;> rfl
          simp only [Finert, ptS, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hl, hΨ]
          rfl
        change 𝔼.E t (fun ω => Finert Ψ (ptS (((xm, e) : ParS (Fin 2) (Fin 2 → ℝ) Ω), x)
          (t, ω)) 1) = 0
        rw [hf, map_sub, map_sub, map_add, map_smul, hik, hpzk]
        funext ω
        simp only [hpz, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        field_simp
        ring
  exact ⟨x, hsol, fun t ω => hib t ω,
    fun y hy => unique_affine_any 𝔼 hΨ hφ hκ hhc hexp hy hsol⟩

/-- **The boundary rule `φ_π π + ρî + (φ_π + ρ)î³` with small disturbances, under every
expectation system** (Woodford (2003), Prop. 2.8, p. 96): for `φ_π ≠ 0`, `|φ_π + ρ| = 1`, on
any nonempty state space, every initial rate and every disturbance process with
`(1 + |φ_π|)‖e‖ ≤ R³/16`: exactly one bounded equilibrium, with `|î_t| ≤ R`. -/
theorem boundary_affine_any_shocks [Nonempty Ω] {φ ρ R : ℝ} (hσ : (φ + ρ) * (φ + ρ) = 1)
    (hφ : φ ≠ 0) (hR : 0 ≤ R) (xm : Fin 2 → ℝ) (e : LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ))
    (he : (1 + |φ|) * ‖e‖ ≤ 1 / 16 * R ^ 3) :
    ∃ x : SProcV (Fin 2) Ω,
      SolvesSV 𝔼 (Finert (InertialBoundary.ruleCubI φ ρ (φ + ρ))) (xm, e) x ∧
      (∀ t ω, |x (t, ω) 1| ≤ R) ∧
      ∀ y : SProcV (Fin 2) Ω,
        SolvesSV 𝔼 (Finert (InertialBoundary.ruleCubI φ ρ (φ + ρ))) (xm, e) y → y = x := by
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
  have hs : |φ + ρ| = 1 := by nlinarith [abs_mul_abs_self (φ + ρ), abs_nonneg (φ + ρ)]
  have hlip : ∀ B, ∃ Λ, ∀ a b, |a| ≤ B → |b| ≤ B →
      |(ρ * a + (φ + ρ) * a ^ 3) - (ρ * b + (φ + ρ) * b ^ 3)| ≤ Λ * |a - b| := by
    intro B
    refine ⟨|ρ| + 3 * B ^ 2, fun a b ha hb => ?_⟩
    have e1 : (ρ * a + (φ + ρ) * a ^ 3) - (ρ * b + (φ + ρ) * b ^ 3) =
        (a - b) * (ρ + (φ + ρ) * (a ^ 2 + a * b + b ^ 2)) := by ring
    rw [e1, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, hs, one_mul]
    have h1 : |a ^ 2 + a * b + b ^ 2| ≤ |a| ^ 2 + |a| * |b| + |b| ^ 2 := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
      · rw [abs_pow, abs_mul]
      · rw [abs_pow]
    have h2 : |a| ^ 2 + |a| * |b| + |b| ^ 2 ≤ 3 * B ^ 2 := by
      have := abs_nonneg a
      have := abs_nonneg b
      nlinarith
    linarith
  exact exists_unique_affine_any 𝔼 hΨ hφ (by norm_num) hR hc (by ring) hlip hexp xm e
    (by linarith)

end Woodford.PriceLevelDetermination.TidyR6InertialAnyExist
