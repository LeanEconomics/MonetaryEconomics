/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.LowerBound

/-!
# A tiny bit of fiscal theory (Sims 2013)

Cochrane (2023), Chapter 16, §16.10.8, pp. 395–396. The simple environment `i_t = E_tπ_{t+1}`,
`i_t = φπ_t` under perfect foresight, so `π_t = φᵗπ₀`; real debt `b_t` with the surplus rule
(16.33) `s_t = γb_t + θπ_t` and accumulation (16.34) `b_{t+1} = Rb_t − s_t`.

## Main results

* `infl_path`: `π_t = φᵗπ₀`; `eq1634`: `b_{t+1} = (R − γ)b_t − θφᵗπ₀`.
* The closed form: `closed_form` (`φ ≠ R − γ`), `closed_form_book` (the printed form, `φ ≠ 0`),
  `closed_form_eq` (`φ = R − γ`).
* `debt_explodes`: for `|R − γ| < 1 < φ` and `θπ₀ ≠ 0`, `|b_t| → ∞` (as printed).
* Error E1: `tvc_iff` (`R^{−t}b_t → 0` iff `θπ₀ = 0` or `φ < R`), `e1_tvc_violated_iff`
  (TVC fails for every `π₀ ≠ 0` iff `φ ≥ R`), `e1_counterexample` (`φ = 1.02`, `R = 1.05`: debt
  explodes but the TVC holds), `active_iff` (determinacy `π₀ = 0` exactly when `φ ≥ R`).
* (16.26)-type valuation: `valuation_iff_tvc`, `valuation_fails`.
* Stationarity: `stationary_iff` (`(R − γ)ᵗb₀ → 0` for all `b₀` iff `R − 1 < γ < R + 1`),
  `stationary_counterexample` (`γ > R − 1` alone is not enough); `passive_of_bounded` (with a
  bounded external surplus component, debt is bounded and the TVC holds for every initial
  value: passive policy).
* `selected_path_indep_theta`: on the selected path `π ≡ 0`, the surplus is `γb_t` whatever `θ`
  ("its presence would have no effect … except for its elimination of the unstable solutions").
-/

namespace Cochrane.NewKeynesianSelection.SimsTinyFiscal

open Filter Topology
open Cochrane.NewKeynesianSelection.LowerBound

/-- Cochrane (2023), §16.10.8, p. 395: in the simple environment `i_t = E_tπ_{t+1}`,
`i_t = φπ_t` under perfect foresight, `π_{t+1} = φπ_t`, so `π_t = φᵗπ₀`. -/
theorem infl_path {φ : ℝ} {infl i : ℕ → ℝ} (hfis : ∀ t, i t = infl (t + 1))
    (hrule : ∀ t, i t = φ * infl t) (t : ℕ) : infl t = φ ^ t * infl 0 := by
  induction t with
  | zero => simp
  | succ n ih => rw [← hfis, hrule, ih, pow_succ]; ring

/-- Cochrane (2023), eqs. (16.33)–(16.34), p. 395: with `s_t = γb_t + θπ_t`,
`b_{t+1} = Rb_t − s_t` and `π_t = φᵗπ₀`, debt follows `b_{t+1} = (R − γ)b_t − θφᵗπ₀`. -/
theorem eq1634 {R γ θ φ π0 : ℝ} {b s infl : ℕ → ℝ} (hs : ∀ t, s t = γ * b t + θ * infl t)
    (hb : ∀ t, b (t + 1) = R * b t - s t) (hπ : ∀ t, infl t = φ ^ t * π0) (t : ℕ) :
    b (t + 1) = (R - γ) * b t - θ * (φ ^ t * π0) := by
  rw [hb, hs, hπ]; ring

/-- Cochrane (2023), p. 396, the solution of (16.34) for `φ ≠ R − γ`:
`b_t = (R − γ)ᵗb₀ − θπ₀(φᵗ − (R − γ)ᵗ)/(φ − (R − γ))`. -/
theorem closed_form {a θ φ π0 : ℝ} {b : ℕ → ℝ} (hφa : φ ≠ a)
    (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) (t : ℕ) :
    b t = a ^ t * b 0 - θ * π0 * ((φ ^ t - a ^ t) / (φ - a)) := by
  have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hb, ih]
    field_simp
    ring

/-- Cochrane (2023), p. 396, the printed form of the solution:
`b_t = (R − γ)ᵗb₀ − θ [1 − (R − γ)ᵗφ^{−t}]/[1 − (R − γ)φ^{−1}] φ^{t−1}π₀` (for `φ ≠ 0`,
`φ ≠ R − γ`; at `t = 0` read `φ^{−1}·(1 − 1) = 0`). -/
theorem closed_form_book {a θ φ π0 : ℝ} {b : ℕ → ℝ} (hφ : φ ≠ 0) (hφa : φ ≠ a)
    (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) (t : ℕ) :
    b t = a ^ t * b 0 - θ * ((1 - a ^ t * (φ ^ t)⁻¹) / (1 - a * φ⁻¹)) * (φ ^ t * φ⁻¹) * π0 := by
  rw [closed_form hφa hb t]
  have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
  have hne' : 1 - a * φ⁻¹ ≠ 0 := by
    rw [show 1 - a * φ⁻¹ = (φ - a) / φ by field_simp]
    exact div_ne_zero hne hφ
  have hpt : φ ^ t ≠ 0 := pow_ne_zero t hφ
  rw [show 1 - a * φ⁻¹ = (φ - a) / φ by field_simp]
  field_simp

/-- Cochrane (2023), p. 396, the borderline case `φ = R − γ`: `b_t = aᵗb₀ − θπ₀ t a^{t−1}`
(written `t·a^{t−1}` as `t * a^(t-1)` with natural subtraction). -/
theorem closed_form_eq {a θ π0 : ℝ} {b : ℕ → ℝ}
    (hb : ∀ t, b (t + 1) = a * b t - θ * (a ^ t * π0)) (t : ℕ) :
    b t = a ^ t * b 0 - θ * π0 * (t * a ^ (t - 1)) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hb, ih]
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

/-- Cochrane (2023), p. 396, "for any `π₀ ≠ 0`, debt explodes": with `|R − γ| < 1 < φ` and
`θπ₀ ≠ 0`, `|b_t| → ∞`. -/
theorem debt_explodes {a θ φ π0 : ℝ} {b : ℕ → ℝ} (ha : |a| < 1) (hφ : 1 < φ) (hθπ : θ * π0 ≠ 0)
    (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) :
    Tendsto (fun t => |b t|) atTop atTop := by
  have hφa : φ ≠ a := by
    intro h; rw [h] at hφ; linarith [le_abs_self a]
  have hpos : 0 < φ - a := by linarith [le_abs_self a]
  set c := θ * π0 / (φ - a) with hc
  have hc0 : 0 < |c| := abs_pos.mpr (div_ne_zero hθπ hpos.ne')
  have hlow : ∀ t, |c| * φ ^ t - (|b 0| + |c|) ≤ |b t| := by
    intro t
    have hform := closed_form hφa hb t
    have hat : |a ^ t| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) ha.le
    have e : b t = a ^ t * b 0 + c * a ^ t - c * φ ^ t := by rw [hform, hc]; field_simp; ring
    have h1 : |c * φ ^ t| ≤ |b t| + |a ^ t * b 0| + |c * a ^ t| := by
      have : c * φ ^ t = a ^ t * b 0 + c * a ^ t - b t := by linarith
      rw [this]
      calc |a ^ t * b 0 + c * a ^ t - b t| ≤ |a ^ t * b 0 + c * a ^ t| + |b t| := abs_sub _ _
        _ ≤ |a ^ t * b 0| + |c * a ^ t| + |b t| := by gcongr; exact abs_add_le _ _
        _ = |b t| + |a ^ t * b 0| + |c * a ^ t| := by ring
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < φ) t)] at h1
    have h2 : |a ^ t| * |b 0| ≤ |b 0| := by nlinarith [abs_nonneg (b 0)]
    have h3 : |c| * |a ^ t| ≤ |c| := by nlinarith [abs_nonneg c]
    linarith
  refine tendsto_atTop_mono hlow ?_
  exact tendsto_atTop_add_const_right _ _
    ((tendsto_pow_atTop_atTop_of_one_lt hφ).const_mul_atTop hc0)

/-- Cochrane (2023), p. 396, error E1: the transversality condition `R^{−t}b_t → 0` holds if and
only if `θπ₀ = 0` or `φ < R` (for `R > 0`, `|R − γ| < R`, `φ > 0`, `φ ≠ R − γ`). -/
theorem tvc_iff {R a θ φ π0 : ℝ} {b : ℕ → ℝ} (hR : 0 < R) (ha : |a| < R) (hφ : 0 < φ)
    (hφa : φ ≠ a) (hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) :
    Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0) ↔ θ * π0 = 0 ∨ φ < R := by
  have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
  set c := θ * π0 / (φ - a) with hc
  have hform : ∀ t, R⁻¹ ^ t * b t = (a / R) ^ t * (b 0 + c) - c * (φ / R) ^ t := fun t => by
    rw [closed_form hφa hb t, hc, div_pow, div_pow, inv_pow]
    have : R ^ t ≠ 0 := pow_ne_zero t hR.ne'
    field_simp
    ring
  have haR : |a / R| < 1 := by rw [abs_div, abs_of_pos hR, div_lt_one hR]; exact ha
  have hA : Tendsto (fun t => (a / R) ^ t * (b 0 + c)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one haR).mul_const (b 0 + c)
  simp only [hform]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hθπ, hφR⟩ := hcon
    have hc0 : c ≠ 0 := div_ne_zero hθπ hne
    have h2 : Tendsto (fun t => c * (φ / R) ^ t) atTop (𝓝 0) := by
      have := hA.sub h
      simpa using this
    have h3 : Tendsto (fun t => (φ / R) ^ t) atTop (𝓝 0) := by
      have := h2.const_mul c⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hc0] using this
    have hge : ∀ t : ℕ, 1 ≤ (φ / R) ^ t := fun t => one_le_pow₀ ((one_le_div hR).mpr hφR)
    have := ge_of_tendsto' h3 hge
    linarith
  · rintro (h | h)
    · have hc0 : c = 0 := by rw [hc, h, zero_div]
      simpa [hc0] using hA
    · have h1 : Tendsto (fun t => (φ / R) ^ t) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hφ hR).le ((div_lt_one hR).mpr h)
      simpa using hA.sub (h1.const_mul c)

/-- Cochrane (2023), p. 396, error E1 (corrected statement): with `|R − γ| < 1 < R`, `φ > 1` and
`θ ≠ 0`, "for any `π₀ ≠ 0` debt … violat[es] the transversality condition" holds if and only if
`φ ≥ R`. For `1 < φ < R` every `π₀` satisfies the transversality condition and fiscal policy stays
passive. -/
theorem e1_tvc_violated_iff {R a θ φ : ℝ} (hR : 1 < R) (ha : |a| < 1) (hφ : 1 < φ)
    (hθ : θ ≠ 0) :
    (∀ π0 : ℝ, π0 ≠ 0 → ∀ b : ℕ → ℝ, (∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) →
      ¬ Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0)) ↔ R ≤ φ := by
  have hφa : φ ≠ a := by intro h; rw [h] at hφ; linarith [le_abs_self a]
  have haR : |a| < R := by linarith
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    -- the path from `π₀ = 1`, `b₀ = 0`
    set b : ℕ → ℝ := fun t => -θ * ((φ ^ t - a ^ t) / (φ - a)) with hbdef
    have hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * 1) := fun t => by
      have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
      simp only [hbdef]
      field_simp
      ring
    exact h 1 one_ne_zero b hb ((tvc_iff (by linarith) haR (by linarith) hφa hb).mpr
      (Or.inr hlt))
  · intro hRφ π0 hπ0 b hb htvc
    rcases (tvc_iff (by linarith) haR (by linarith) hφa hb).mp htvc with h | h
    · exact mul_ne_zero hθ hπ0 h
    · linarith

/-- Cochrane (2023), p. 396, error E1 counterexample: `R = 1.05`, `γ = 0.5` (so `R − γ = 0.55`),
`φ = 1.02`, `θ = 1`, `π₀ = 1`, `b₀ = 0`. Debt explodes, yet `R^{−t}b_t → 0`: the transversality
condition holds and the inflationary path is not ruled out. -/
theorem e1_counterexample :
    let b : ℕ → ℝ := fun t => -((102 / 100) ^ t - (55 / 100) ^ t) / (102 / 100 - 55 / 100)
    (∀ t, b (t + 1) = 55 / 100 * b t - 1 * ((102 / 100) ^ t * 1)) ∧
      Tendsto (fun t => |b t|) atTop atTop ∧
      Tendsto (fun t => (105 / 100 : ℝ)⁻¹ ^ t * b t) atTop (𝓝 0) := by
  intro b
  have hb : ∀ t, b (t + 1) = 55 / 100 * b t - 1 * ((102 / 100) ^ t * 1) := fun t => by
    simp only [b, pow_succ]
    ring
  refine ⟨hb, debt_explodes (by norm_num [abs_of_pos]) (by norm_num) (by norm_num) hb, ?_⟩
  exact (tvc_iff (by norm_num) (by norm_num [abs_of_pos]) (by norm_num) (by norm_num) hb).mpr
    (Or.inr (by norm_num))

/-- Cochrane (2023), p. 396, "we now have a real reason to rule out the nominally explosive
equilibria": with `|R − γ| < 1 < R`, `φ > 1`, `θ ≠ 0`, the transversality condition selects
`π₀ = 0` (fiscal policy active, a unique equilibrium) if and only if `φ ≥ R`. -/
theorem active_iff {R a θ φ : ℝ} (hR : 1 < R) (ha : |a| < 1) (hφ : 1 < φ) (hθ : θ ≠ 0)
    (b0 : ℝ) :
    (∀ π0 : ℝ, ∀ b : ℕ → ℝ, b 0 = b0 → (∀ t, b (t + 1) = a * b t - θ * (φ ^ t * π0)) →
      Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0) → π0 = 0) ↔ R ≤ φ := by
  have hφa : φ ≠ a := by intro h; rw [h] at hφ; linarith [le_abs_self a]
  have haR : |a| < R := by linarith
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    set b : ℕ → ℝ := fun t => a ^ t * b0 - θ * ((φ ^ t - a ^ t) / (φ - a)) with hbdef
    have hb : ∀ t, b (t + 1) = a * b t - θ * (φ ^ t * 1) := fun t => by
      have hne : φ - a ≠ 0 := sub_ne_zero.mpr hφa
      simp only [hbdef]
      field_simp
      ring
    have := h 1 b (by simp [hbdef]) hb ((tvc_iff (by linarith) haR (by linarith) hφa hb).mpr
      (Or.inr hlt))
    exact one_ne_zero this
  · intro hRφ π0 b _ hb htvc
    by_contra hπ0
    exact (e1_tvc_violated_iff hR ha hφ hθ).mpr hRφ π0 hπ0 b hb htvc

/-- Cochrane (2023), p. 395, the valuation equation behind the transversality condition: with
`b_{t+1} = Rb_t − s_t`, `R > 0`, and absolutely summable discounted surpluses,
`b_t = Σ R^{−(j+1)} s_{t+j}` holds iff `R^{−T}b_{t+T} → 0`. -/
theorem valuation_iff_tvc {R : ℝ} {b s : ℕ → ℝ} (hR : 0 < R)
    (hb : ∀ t, b (t + 1) = R * b t - s t) (t : ℕ)
    (hsum : Summable fun j => R⁻¹ ^ (j + 1) * s (t + j)) :
    HasSum (fun j => R⁻¹ ^ (j + 1) * s (t + j)) (b t) ↔
      Tendsto (fun T => R⁻¹ ^ T * b (t + T)) atTop (𝓝 0) := by
  have hR1 : 0 < 1 + (R - 1) := by linarith
  have hflow : ∀ u, b (u + 1) = (1 + (R - 1)) * (b u - s u / R) := fun u => by
    rw [hb]; field_simp; ring
  have heq : (fun j => R⁻¹ ^ (j + 1) * s (t + j)) =
      fun j => (1 + (R - 1))⁻¹ ^ j * (s (t + j) / R) := by
    funext j; rw [pow_succ]; field_simp; ring
  rw [heq] at hsum ⊢
  have := LowerBound.valuation_iff_tvc (b := b) (s := fun u => s u / R) hR1 hflow t hsum
  simpa using this

/-- Cochrane (2023), p. 396: when the transversality condition fails, the valuation equation
`b₀ = Σ R^{−(j+1)}s_j` cannot hold (as a genuine sum). -/
theorem valuation_fails {R : ℝ} {b s : ℕ → ℝ} (hR : 0 < R) (hb : ∀ t, b (t + 1) = R * b t - s t)
    (htvc : ¬ Tendsto (fun T => R⁻¹ ^ T * b T) atTop (𝓝 0)) :
    ¬ HasSum (fun j => R⁻¹ ^ (j + 1) * s j) (b 0) := by
  intro h
  have hsum : Summable fun j => R⁻¹ ^ (j + 1) * s (0 + j) := by simpa using h.summable
  have := (valuation_iff_tvc hR hb 0 hsum).mp (by simpa using h)
  exact htvc (by simpa using this)

/-- Cochrane (2023), p. 395, "specialize to `γ > R − 1` so debt is stationary", corrected: with
no inflation term, `b_t = (R − γ)ᵗb₀` converges to zero for every `b₀` iff `|R − γ| < 1`, i.e.
`R − 1 < γ < R + 1`. -/
theorem stationary_iff {R γ : ℝ} :
    (∀ b0 : ℝ, Tendsto (fun t : ℕ => (R - γ) ^ t * b0) atTop (𝓝 0)) ↔
      R - 1 < γ ∧ γ < R + 1 := by
  have habs : |R - γ| < 1 ↔ R - 1 < γ ∧ γ < R + 1 := by
    rw [abs_lt]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← habs]
  constructor
  · intro h
    have h1 := h 1
    simp only [mul_one] at h1
    by_contra hcon
    push Not at hcon
    have hge : ∀ t : ℕ, 1 ≤ |(R - γ) ^ t| := fun t => by
      rw [abs_pow]; exact one_le_pow₀ hcon
    have h2 := h1.abs
    rw [abs_zero] at h2
    have := ge_of_tendsto' h2 hge
    linarith
  · intro h b0
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const b0

/-- Cochrane (2023), p. 395, error E1 (second part): `γ > R − 1` alone does not make debt
stationary. With `R = 1.05` and `γ = 3.05 > R − 1`, `R − γ = −2` and `b_t = (−2)ᵗ` does not
converge. -/
theorem stationary_counterexample :
    ((105 / 100 : ℝ) - 1 < 305 / 100) ∧
      ¬ Tendsto (fun t : ℕ => ((105 / 100 : ℝ) - 305 / 100) ^ t * 1) atTop (𝓝 0) := by
  refine ⟨by norm_num, fun h => ?_⟩
  have := (stationary_iff (R := 105 / 100) (γ := 305 / 100)).mp (fun b0 => by
    have := h.mul_const b0
    simpa [mul_comm, mul_assoc] using this)
  norm_num at this

/-- Cochrane (2023), p. 396, "the result that `γ > R − 1` leads to passive policy needs a bounded
external component of the surplus": if `b_{t+1} = (R − γ)b_t − x_t` with `|R − γ| < 1` and
`|x_t| ≤ X`, debt is bounded by `|b₀| + X/(1 − |R − γ|)`, and for `R > 1` the transversality
condition `R^{−t}b_t → 0` holds for every initial value: fiscal policy is passive. -/
theorem passive_of_bounded {R a X : ℝ} {b x : ℕ → ℝ} (ha : |a| < 1) (hR : 1 < R)
    (hx : ∀ t, |x t| ≤ X) (hb : ∀ t, b (t + 1) = a * b t - x t) :
    (∀ t, |b t| ≤ |b 0| + X / (1 - |a|)) ∧ Tendsto (fun t => R⁻¹ ^ t * b t) atTop (𝓝 0) := by
  have h1a : 0 < 1 - |a| := by linarith
  have hX : 0 ≤ X := le_trans (abs_nonneg _) (hx 0)
  set B := |b 0| + X / (1 - |a|) with hB
  have hbd : ∀ t, |b t| ≤ B := by
    intro t
    induction t with
    | zero => rw [hB]; have : 0 ≤ X / (1 - |a|) := div_nonneg hX h1a.le; linarith
    | succ n ih =>
      rw [hb]
      have hkey : |a| * B + X ≤ B := by
        have : X = (1 - |a|) * (X / (1 - |a|)) := by field_simp
        rw [hB]
        nlinarith [abs_nonneg (b 0), abs_nonneg a, div_nonneg hX h1a.le]
      calc |a * b n - x n| ≤ |a * b n| + |x n| := abs_sub _ _
        _ = |a| * |b n| + |x n| := by rw [abs_mul]
        _ ≤ |a| * B + X := by gcongr; exact hx n
        _ ≤ B := hkey
  refine ⟨hbd, ?_⟩
  have hR0 : 0 ≤ R⁻¹ := (inv_pos.mpr (by linarith)).le
  have hR1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hlim : Tendsto (fun t => R⁻¹ ^ t * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1).mul_const B
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun t => abs_nonneg _) (fun t => ?_) hlim
  change |R⁻¹ ^ t * b t| ≤ R⁻¹ ^ t * B
  rw [abs_mul, abs_pow, abs_of_nonneg hR0]
  exact mul_le_mul_of_nonneg_left (hbd t) (pow_nonneg hR0 t)

/-- Cochrane (2023), p. 396, quoting Sims: "its [`θ`] presence would have no effect on the first
two equations of the system or on the equilibrium time path of prices and interest rates, except
for its elimination of the unstable solutions": on the selected path `π₀ = 0`, inflation is zero,
the surplus is `γb_t` and debt is `(R − γ)ᵗb₀`, whatever `θ`. -/
theorem selected_path_indep_theta {R γ θ φ : ℝ} {b s infl : ℕ → ℝ}
    (hs : ∀ t, s t = γ * b t + θ * infl t) (hb : ∀ t, b (t + 1) = R * b t - s t)
    (hπ : ∀ t, infl t = φ ^ t * 0) :
    (∀ t, infl t = 0) ∧ (∀ t, s t = γ * b t) ∧ ∀ t, b t = (R - γ) ^ t * b 0 := by
  have h0 : ∀ t, infl t = 0 := fun t => by rw [hπ, mul_zero]
  have hs' : ∀ t, s t = γ * b t := fun t => by rw [hs, h0, mul_zero, add_zero]
  refine ⟨h0, hs', fun t => ?_⟩
  induction t with
  | zero => simp
  | succ n ih => rw [hb, hs', ih, pow_succ]; ring

end Cochrane.NewKeynesianSelection.SimsTinyFiscal
