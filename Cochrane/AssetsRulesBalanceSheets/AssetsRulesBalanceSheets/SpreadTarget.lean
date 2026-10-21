/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.MixedDebtRules

/-!
# Targeting the spread

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.4
"Targeting the spread" and §9.4.1 "Fiscal theory with a spread target", eqs. (9.17)–(9.26),
pp. 271–278.

## Main results

* §9.4: `taylor_spread_equiv` (a Taylor rule with a real rate that tracks it is a spread target,
  p. 273); `swap_rate`: the zero-cost inflation-swap rate is `β/Q_t`, the expected gross inflation
  under the nominal risk-neutral weights `m = β P_t/P_{t+1}` (p. 273).
* The simple model (9.17)–(9.20) (`SimpleModel`): `eq_9_21_mul`, `eq_9_21` (valid for every
  `θ ∈ [0, 1]`, including the spread target `θ = 1`), `lam_bounds`;
`indeterminate_without_valuation`:
  without (9.22) any initial inflation gives a bounded equilibrium.
* **Theorem ST** (`unexpected_inflation_iff`, `eq_9_23`): given (9.17)–(9.21), the linearised
  valuation equation (9.22) holds iff
  `ΔE_{t+1} π_{t+1} = −((1 − ρ)(1 − θ) + σκ)/((1 − ρ)(1 − θ) + σκ + ρ) · ε^{Σs}_{t+1}`;
  `exists_solution`, `solution_bounded`, `unique_solution`: existence, boundedness and uniqueness
  (given `π_0`) of the solution of (9.17)–(9.22), for every `θ ∈ [0, 1]`.
* `theta_zero`, `theta_one`, `tendsto_coef_theta_one`: the cases `θ = 0`, `θ = 1` (proved directly;
  the footnote's formula `r_t = (π^{e*} − E_t π_{t+1})/(1 − θ)` is undefined at `θ = 1`, error E9.5,
  see `footnote_r` and `r_eq`) and the limit `θ → 1`; `theta_one_paths`: the paths of `x`, `r`, `i`
  on p. 277.
* The full new-Keynesian model (9.24)–(9.25) with a spread target (`FullNK`): `x_formula`
  ((9.26) first line), `r_formula` (**(9.26) corrected**, error E9.4),
  `printed_9_26_fails_perfectForesight` (the printed `u_π` terms lack `1/κ`) and
  `printed_9_26_fails_coin` (the printed sign of `ΔE_t π_t` is wrong).
* `holden_unique`: the rule `i_t = r_t + π* + φ (π_t − π*)` with `|φ| > 1` has the unique bounded
  solution `π ≡ π*` (Holden 2020, p. 278).
-/

namespace Cochrane.AssetsRulesBalanceSheets.SpreadTarget

open Filter Topology

/-! ### §9.4: spreads, Taylor rules and inflation swaps -/

/-- Cochrane (2023), §9.4, p. 273: if the central bank follows `i = (r̄ + π*) + θ_π π + θ_x x` and
the
real rate tracks the same variables, `r = r̄ + θ_π π + θ_x x`, the spread `i − r` equals `π*`: the
Taylor rule is a spread target. -/
theorem taylor_spread_equiv {i r rbar πs θπ θx π x : ℝ} (hi : i = (rbar + πs) + θπ * π + θx * x)
    (hr : r = rbar + θπ * π + θx * x) : i - r = πs := by
  rw [hi, hr]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.4, p. 273 (inflation swaps): with a constant real rate, the dollar price of
a claim to `Π_{t+1} = P_{t+1}/P_t` dollars is `β`, the nominal bond costs `Q_t = β
E_t(P_t/P_{t+1})`,
so the swap paying `Π_{t+1} − Π*` costs `β − Π* Q_t`; it is zero iff `Π* = β/Q_t`, which equals the
expectation of `Π_{t+1}` under the nominal risk-neutral weights `m = β P_t/P_{t+1}`. -/
theorem swap_rate {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (t : ℕ) (ω : Ω)
    (hQ : 0 < β * 𝔼.E t (P t / P (t + 1)) ω) (Pis : ℝ) :
    (β - Pis * (β * 𝔼.E t (P t / P (t + 1)) ω) = 0 ↔
        Pis = β / (β * 𝔼.E t (P t / P (t + 1)) ω)) ∧
      β / (β * 𝔼.E t (P t / P (t + 1)) ω) =
        𝔼.E t ((β • (P t / P (t + 1))) * (P (t + 1) / P t)) ω /
          𝔼.E t (β • (P t / P (t + 1))) ω := by
  have hmPi : (β • (P t / P (t + 1))) * (P (t + 1) / P t) = fun _ => β := by
    funext ω'
    simp only [Pi.mul_apply, Pi.smul_apply, Pi.div_apply, smul_eq_mul]
    field_simp [(hP t ω').ne', (hP (t + 1) ω').ne']
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · rw [eq_div_iff hQ.ne']
    linarith
  · rw [h, div_mul_cancel₀ _ hQ.ne', sub_self]
  · rw [hmPi, 𝔼.const, map_smul]
    rfl

/-! ### The simple model (9.17)–(9.20) -/

variable (σ κ θ πs : ℝ) (π x i r : ℕ → Ω → ℝ)

/-- Cochrane (2023), eqs. (9.17)–(9.20), p. 275: the static IS curve `x_t = −σ(i_t − E_t π_{t+1})`,
the Phillips curve `π_t = E_t π_{t+1} + κ x_t`, the real rate `r_t = i_t − E_t π_{t+1}`, and the
rule
`i_t = θ r_t + π^{e*}` (the spread target is `θ = 1`), with inflation adapted. -/
structure SimpleModel where
  adapted_pi : 𝔼.Adapted π
  is_9_17 : ∀ t, x t = (-σ) • (i t - 𝔼.E t (π (t + 1)))
  is_9_18 : ∀ t, π t = 𝔼.E t (π (t + 1)) + κ • x t
  is_9_19 : ∀ t, r t = i t - 𝔼.E t (π (t + 1))
  is_9_20 : ∀ t, i t = θ • r t + fun _ => πs

variable {𝔼 σ κ θ πs π x i r}

/-- Cochrane (2023), §9.4.1, p. 275 (footnote 1): the IS and Phillips curves give
`σκ r_t = E_t π_{t+1} − π_t` for every `θ` (this, not the footnote's division by `1 − θ`, pins
`r`). -/
theorem r_eq (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    (σ * κ) • r t = 𝔼.E t (π (t + 1)) - π t := by
  have h17 := hM.is_9_17 t
  have h18 := hM.is_9_18 t
  have h19 := hM.is_9_19 t
  funext ω
  have a := congrFun h17 ω
  have b := congrFun h18 ω
  have c := congrFun h19 ω
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at a b c ⊢
  rw [b, a, ← c]
  ring

/-- Cochrane (2023), eq. (9.21), p. 275, multiplied out:
`(1 − θ + σκ)(E_t π_{t+1} − π^{e*}) = (1 − θ)(π_t − π^{e*})`, valid for every `θ`. -/
theorem eq_9_21_mul (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    (1 - θ + σ * κ) • (𝔼.E t (π (t + 1)) - fun _ => πs) = (1 - θ) • (π t - fun _ => πs) := by
  have hr := r_eq hM t
  have h19 := hM.is_9_19 t
  have h20 := hM.is_9_20 t
  funext ω
  have a := congrFun hr ω
  have c := congrFun h19 ω
  have d := congrFun h20 ω
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at a c d ⊢
  have e : (1 - θ) * r t ω = πs - 𝔼.E t (π (t + 1)) ω := by linarith
  linear_combination (σ * κ) * e - (1 - θ) * a

/-- Cochrane (2023), eq. (9.21), p. 275: the persistence `λ = (1 − θ)/(1 − θ + σκ)`. -/
noncomputable def lam (σ κ θ : ℝ) : ℝ := (1 - θ) / (1 - θ + σ * κ)

/-- Cochrane (2023), eq. (9.21), p. 275: `E_t(π_{t+1} − π^{e*}) = (1 − θ)/(1 − θ + σκ) · (π_t −
π^{e*})`. -/
theorem eq_9_21 (hD : 1 - θ + σ * κ ≠ 0) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    𝔼.E t (π (t + 1)) - (fun _ => πs) = lam σ κ θ • (π t - fun _ => πs) := by
  have h := eq_9_21_mul hM t
  funext ω
  have a := congrFun h ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a ⊢
  unfold lam
  field_simp
  linarith

/-- Cochrane (2023), §9.4.1, p. 275 ("when the coefficient on the right-hand side is less than
one"): for `θ ∈ [0, 1]` and `σκ > 0`, `0 ≤ λ < 1`. -/
theorem lam_bounds {σ κ θ : ℝ} (hθ1 : θ ≤ 1) (hσκ : 0 < σ * κ) :
    0 ≤ lam σ κ θ ∧ lam σ κ θ < 1 := by
  unfold lam
  have h : 0 < 1 - θ + σ * κ := by linarith
  exact ⟨div_nonneg (by linarith) h.le, (div_lt_one h).mpr (by linarith)⟩

/-- Cochrane (2023), §9.4.1, p. 275 (footnote 1): `λ − 1 = −σκ/(1 − θ + σκ)`. -/
theorem lam_sub_one {σ κ θ : ℝ} (hD : 1 - θ + σ * κ ≠ 0) :
    lam σ κ θ - 1 = -(σ * κ) / (1 - θ + σ * κ) := by
  unfold lam
  field_simp
  ring

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): iterating (9.21),
`E_s π_{s+j} − π^{e*} = λʲ (π_s − π^{e*})`. -/
theorem E_pi_iter (hD : 1 - θ + σ * κ ≠ 0) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (s j : ℕ) :
    𝔼.E s (π (s + j)) - (fun _ => πs) = lam σ κ θ ^ j • (π s - fun _ => πs) := by
  induction j with
  | zero => simp [hM.adapted_pi s]
  | succ j ih =>
    have h := congrArg (𝔼.E s) (eq_9_21 hD hM (s + j))
    rw [map_sub, map_smul, map_sub, 𝔼.tower (Nat.le_add_right s j), 𝔼.const] at h
    have ih' : 𝔼.E s (π (s + j)) = (fun _ => πs) + lam σ κ θ ^ j • (π s - fun _ => πs) := by
      rw [← ih]
      abel
    rw [ih'] at h
    rw [← add_assoc, h, pow_succ]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), §9.4.1, p. 275 ("inflation is stable but indeterminate, as `ΔE_{t+1} π_{t+1}`
can be anything"): without the valuation equation (9.22), under perfect foresight, every initial
inflation `π_0 = π^{e*} + a` starts a bounded equilibrium of (9.17)–(9.20) (`θ ∈ [0, 1]`,
`σκ > 0`). -/
theorem indeterminate_without_valuation {σ κ θ πs : ℝ} (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (a : ℝ) :
    ∃ π x i r : ℕ → Unit → ℝ, SimpleModel perfectForesight σ κ θ πs π x i r ∧ BoundedProc π ∧
      π 0 () = πs + a := by
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have hσκ0 : σ * κ ≠ 0 := hσκ.ne'
  have hσ : σ ≠ 0 := left_ne_zero_of_mul hσκ0
  have hκ : κ ≠ 0 := right_ne_zero_of_mul hσκ0
  have hl := lam_bounds hθ1 hσκ
  set l := lam σ κ θ with hl_def
  set π : ℕ → Unit → ℝ := fun t _ => πs + l ^ t * a with hπ
  set r : ℕ → Unit → ℝ := fun t _ => (π (t + 1) () - π t ()) / (σ * κ) with hr
  refine ⟨π, fun t _ => -σ * r t (), fun t _ => r t () + π (t + 1) (), r, ⟨fun _ => rfl,
    fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩, ⟨|πs| + |a|, fun t ω => ?_⟩, by simp [hπ]⟩
  · funext ω
    change -σ * r t () = -σ * (r t () + π (t + 1) () - π (t + 1) ())
    ring
  · funext ω
    change π t () = π (t + 1) () + κ * (-σ * r t ())
    simp only [hr]
    field_simp
    ring
  · funext ω
    change r t () = r t () + π (t + 1) () - π (t + 1) ()
    ring
  · funext ω
    change r t () + π (t + 1) () = θ * r t () + πs
    have hls := lam_sub_one (σ := σ) (κ := κ) (θ := θ) hD
    rw [← hl_def] at hls
    simp only [hr, hπ]
    have e : (πs + l ^ (t + 1) * a - (πs + l ^ t * a)) / (σ * κ) =
        l ^ t * a * ((l - 1) / (σ * κ)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [e, show (l - 1) / (σ * κ) = -1 / (1 - θ + σ * κ) by
      rw [hls]
      field_simp, pow_succ, hl_def]
    unfold lam
    field_simp
    ring
  · simp only [hπ]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_pow, abs_of_nonneg hl.1]
    exact mul_le_of_le_one_left (abs_nonneg a) (pow_le_one₀ hl.1 hl.2.le)

/-! ### The valuation equation (9.22) and Theorem ST -/

/-- Cochrane (2023), eq. (9.22), p. 275: the innovation operator
`ΔE_{t+1} y = E_{t+1} y − E_t y`. -/
def innov (𝔼 : ExpectationSystem Ω) (t : ℕ) (y : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) y - 𝔼.E t y

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): `ΔE_{t+1} π_{t+1+j} = λʲ ΔE_{t+1} π_{t+1}`. -/
theorem innov_pi_iter (hD : 1 - θ + σ * κ ≠ 0) (hM : SimpleModel 𝔼 σ κ θ πs π x i r)
    (t j : ℕ) : innov 𝔼 t (π (t + 1 + j)) = lam σ κ θ ^ j • innov 𝔼 t (π (t + 1)) := by
  have h1 := E_pi_iter hD hM (t + 1) j
  have h2 := congrArg (𝔼.E t) h1
  rw [map_sub, 𝔼.tower (by omega : t ≤ t + 1), 𝔼.const, map_smul, map_sub, 𝔼.const] at h2
  · unfold innov
    rw [hM.adapted_pi (t + 1)]
    have e1 : 𝔼.E (t + 1) (π (t + 1 + j)) =
        (fun _ => πs) + lam σ κ θ ^ j • (π (t + 1) - fun _ => πs) := by
      rw [← h1]
      abel
    have e2 : 𝔼.E t (π (t + 1 + j)) =
        (fun _ => πs) + lam σ κ θ ^ j • (𝔼.E t (π (t + 1)) - fun _ => πs) := by
      rw [← h2]
      abel
    rw [e1, e2]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): the innovation in the ex-post real return,
`ΔE_{t+1}(i_{t+1+j} − π_{t+2+j}) = −λʲ/(1 − θ + σκ) · ΔE_{t+1} π_{t+1}`. -/
theorem innov_return (hD : 1 - θ + σ * κ ≠ 0) (hσκ : σ * κ ≠ 0)
    (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t j : ℕ) :
    innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) =
      (-(lam σ κ θ ^ j / (1 - θ + σ * κ))) • innov 𝔼 t (π (t + 1)) := by
  set s := t + 1 + j with hs
  have hs2 : t + 2 + j = s + 1 := by omega
  rw [hs2]
  -- the real rate in terms of inflation
  have hr : r s = (-(1 / (1 - θ + σ * κ))) • (π s - fun _ => πs) := by
    have h1 := r_eq hM s
    have h2 := eq_9_21 hD hM s
    have hls := lam_sub_one (σ := σ) (κ := κ) (θ := θ) hD
    funext ω
    have a := congrFun h1 ω
    have b := congrFun h2 ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a b ⊢
    have hE : 𝔼.E s (π (s + 1)) ω = πs + lam σ κ θ * (π s ω - πs) := by linarith
    have e : σ * κ * r s ω = σ * κ * (-(1 / (1 - θ + σ * κ)) * (π s ω - πs)) := by
      rw [a, hE]
      unfold lam
      field_simp
      ring
    exact mul_left_cancel₀ hσκ e
  have hdecomp : i s - π (s + 1) =
      r s + (𝔼.E s (π (s + 1)) - π (s + 1)) := by
    rw [hM.is_9_19 s]
    abel
  have hts : t + 1 ≤ s := by omega
  have hz : innov 𝔼 t (𝔼.E s (π (s + 1)) - π (s + 1)) = 0 := by
    unfold innov
    rw [map_sub, map_sub, 𝔼.tower hts, 𝔼.tower (by omega : t ≤ s)]
    abel
  have hc : innov 𝔼 t (fun _ => πs) = 0 := by
    unfold innov
    rw [𝔼.const, 𝔼.const, sub_self]
  have hlin : ∀ y z : Ω → ℝ, innov 𝔼 t (y + z) = innov 𝔼 t y + innov 𝔼 t z := fun y z => by
    unfold innov
    rw [map_add, map_add]
    abel
  have hsm : ∀ (c : ℝ) (y : Ω → ℝ), innov 𝔼 t (c • y) = c • innov 𝔼 t y := fun c y => by
    unfold innov
    rw [map_smul, map_smul, smul_sub]
  have hsub : ∀ y z : Ω → ℝ, innov 𝔼 t (y - z) = innov 𝔼 t y - innov 𝔼 t z := fun y z => by
    unfold innov
    rw [map_sub, map_sub]
    abel
  rw [hdecomp, hlin, hz, add_zero, hr, hsm, hsub, hc, sub_zero, hs, innov_pi_iter hD hM t j,
    smul_smul]
  congr 1
  ring

/-- Cochrane (2023), eq. (9.22), p. 275: the linearised government debt valuation equation,
`ΔE_{t+1} π_{t+1} = −ε^{Σs}_{t+1} + ∑_{j≥1} ρʲ ΔE_{t+1}(i_{t+j} − π_{t+1+j})`, where
`ε^{Σs}_{t+1} = ΔE_{t+1} ∑ⱼ ρʲ s̃_{t+1+j}` is the surplus (fiscal) shock. -/
def Valuation (𝔼 : ExpectationSystem Ω) (ρ : ℝ) (π i ε : ℕ → Ω → ℝ) : Prop :=
  ∀ t, innov 𝔼 t (π (t + 1)) = -ε (t + 1) + fun ω =>
    ∑' j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω

/-- Cochrane (2023), eq. (9.23), p. 276: `D = (1 − ρ)(1 − θ) + σκ`. -/
noncomputable def coefD (σ κ θ ρ : ℝ) : ℝ := (1 - ρ) * (1 - θ) + σ * κ

/-- Cochrane (2023), §9.4.1, p. 276 (footnote 1): the discount-rate term of (9.22) equals
`−(ρ/D) ΔE_{t+1} π_{t+1}`. -/
theorem valuation_sum {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) (ω : Ω) :
    ∑' j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω =
      -(ρ / coefD σ κ θ ρ) * innov 𝔼 t (π (t + 1)) ω := by
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have hl := lam_bounds hθ1 hσκ
  have hρl : |ρ * lam σ κ θ| < 1 := by
    rw [abs_of_nonneg (mul_nonneg hρ0 hl.1)]
    calc ρ * lam σ κ θ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hl.2.le hρ0
      _ < 1 := by linarith
  have hterm : ∀ j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω =
      (-(ρ * innov 𝔼 t (π (t + 1)) ω / (1 - θ + σ * κ))) * (ρ * lam σ κ θ) ^ j := by
    intro j
    rw [innov_return hD hσκ.ne' hM t j]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, pow_succ]
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_abs_lt_one hρl]
  have hDpos : 0 < coefD σ κ θ ρ := by
    unfold coefD
    have : 0 ≤ (1 - ρ) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h1 : 1 - ρ * lam σ κ θ ≠ 0 := by
    have := (abs_lt.mp hρl).2
    linarith
  have hkey : (1 - θ + σ * κ) * (1 - ρ * lam σ κ θ) = coefD σ κ θ ρ := by
    unfold lam coefD
    field_simp
    ring
  rw [← hkey]
  field_simp

/-- Cochrane (2023), eq. (9.23), p. 276 (**Theorem ST**): given (9.17)–(9.20) with `θ ∈ [0, 1]`,
`σκ > 0` and `0 ≤ ρ < 1`, the valuation equation (9.22) holds if and only if
`ΔE_{t+1} π_{t+1} = −D/(D + ρ) · ε^{Σs}_{t+1}` with `D = (1 − ρ)(1 − θ) + σκ`. -/
theorem unexpected_inflation_iff {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) {ε : ℕ → Ω → ℝ} :
    Valuation 𝔼 ρ π i ε ↔ ∀ t, innov 𝔼 t (π (t + 1)) =
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1) := by
  have hDpos : 0 < coefD σ κ θ ρ := by
    unfold coefD
    have : 0 ≤ (1 - ρ) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hDρ : 0 < coefD σ κ θ ρ + ρ := by linarith
  constructor
  · intro hV t
    funext ω
    have h := congrFun (hV t) ω
    simp only [Pi.add_apply, Pi.neg_apply] at h
    rw [valuation_sum hρ0 hρ1 hθ1 hσκ hM t ω] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp at h ⊢
    linarith
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [valuation_sum hρ0 hρ1 hθ1 hσκ hM t ω, h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- Cochrane (2023), eq. (9.23), p. 276: in any solution of (9.17)–(9.22),
`ΔE_{t+1} π_{t+1} = −((1 − ρ)(1 − θ) + σκ)/((1 − ρ)(1 − θ) + σκ + ρ) · ε^{Σs}_{t+1}`. -/
theorem eq_9_23 {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) {ε : ℕ → Ω → ℝ}
    (hV : Valuation 𝔼 ρ π i ε) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = (-(((1 - ρ) * (1 - θ) + σ * κ) /
      ((1 - ρ) * (1 - θ) + σ * κ + ρ))) • ε (t + 1) :=
  (unexpected_inflation_iff hρ0 hρ1 hθ1 hσκ hM).mp hV t

/-- Cochrane (2023), §9.4.1, p. 276: the solution path. In any solution of (9.17)–(9.22) with
inflation adapted, `π_{t+1} = π^{e*} + λ(π_t − π^{e*}) − D/(D + ρ) · ε^{Σs}_{t+1}`. -/
theorem pi_succ {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) {ε : ℕ → Ω → ℝ}
    (hV : Valuation 𝔼 ρ π i ε) (t : ℕ) :
    π (t + 1) = (fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1) := by
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have h1 := (unexpected_inflation_iff hρ0 hρ1 hθ1 hσκ hM).mp hV t
  have h2 := eq_9_21 hD hM t
  unfold innov at h1
  rw [hM.adapted_pi (t + 1)] at h1
  rw [← h1, ← h2]
  abel

/-- Cochrane (2023), §9.4.1, pp. 275–276 (uniqueness): two solutions of (9.17)–(9.22) with the same
fiscal shocks and the same initial inflation coincide (inflation, output, and both rates). -/
theorem unique_solution {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) {ε : ℕ → Ω → ℝ} {π' x' i' r' : ℕ → Ω → ℝ}
    (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (hM' : SimpleModel 𝔼 σ κ θ πs π' x' i' r')
    (hV : Valuation 𝔼 ρ π i ε) (hV' : Valuation 𝔼 ρ π' i' ε) (h0 : π 0 = π' 0) :
    π = π' ∧ r = r' ∧ i = i' ∧ x = x' := by
  have hπ : π = π' := by
    funext t
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [pi_succ hρ0 hρ1 hθ1 hσκ hM hV t, pi_succ hρ0 hρ1 hθ1 hσκ hM' hV' t, ih]
  have hσκ0 : σ * κ ≠ 0 := hσκ.ne'
  have hr : r = r' := by
    funext t
    have a := r_eq hM t
    have b := r_eq hM' t
    rw [← hπ] at b
    rw [← b] at a
    funext ω
    have := congrFun a ω
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hσκ0 this
  have hi : i = i' := by
    funext t
    rw [hM.is_9_20 t, hM'.is_9_20 t, hr]
  refine ⟨hπ, hr, hi, ?_⟩
  funext t
  rw [hM.is_9_17 t, hM'.is_9_17 t, hi, hπ]

/-- Cochrane (2023), §9.4.1, p. 276: the solution path `π_0`, `π_{t+1} = π^{e*} + λ(π_t − π^{e*}) −
k ε_{t+1}`. -/
noncomputable def solPi (lamv k πs : ℝ) (π0 : Ω → ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => (fun _ => πs) + lamv • (solPi lamv k πs π0 ε t - fun _ => πs) + (-k) • ε (t + 1)

/-- Cochrane (2023), §9.4.1, pp. 275–276 (**existence**): for any adapted fiscal shocks with
`E_t ε_{t+1} = 0` and any initial inflation known at date 0, the path `solPi` together with
`r_t = (E_t π_{t+1} − π_t)/(σκ)`, `x_t = −σ r_t`, `i_t = r_t + E_t π_{t+1}` solves (9.17)–(9.22). -/
theorem exists_solution {σ κ θ πs ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hθ1 : θ ≤ 1)
    (hσκ : 0 < σ * κ) {ε : ℕ → Ω → ℝ} (hεa : 𝔼.Adapted ε) (hε0 : ∀ t, 𝔼.E t (ε (t + 1)) = 0)
    {π0 : Ω → ℝ} (hπ0 : 𝔼.E 0 π0 = π0) :
    let π := solPi (lam σ κ θ) (coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ)) πs π0 ε
    let r := fun t => (1 / (σ * κ)) • (𝔼.E t (π (t + 1)) - π t)
    SimpleModel 𝔼 σ κ θ πs π (fun t => (-σ) • r t) (fun t => r t + 𝔼.E t (π (t + 1))) r ∧
      Valuation 𝔼 ρ π (fun t => r t + 𝔼.E t (π (t + 1))) ε := by
  intro π r
  have hD : 1 - θ + σ * κ ≠ 0 := by linarith
  have hσκ0 : σ * κ ≠ 0 := hσκ.ne'
  have hσ : σ ≠ 0 := left_ne_zero_of_mul hσκ0
  have hκ : κ ≠ 0 := right_ne_zero_of_mul hσκ0
  have hadapt : 𝔼.Adapted π := by
    intro t
    induction t with
    | zero => exact hπ0
    | succ t ih =>
      change 𝔼.E (t + 1) ((fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
        (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1)) = _
      rw [map_add, map_add, map_smul, map_smul, map_sub, 𝔼.const,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih, hεa (t + 1)]
      rfl
  have hEπ : ∀ t, 𝔼.E t (π (t + 1)) = (fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) := by
    intro t
    change 𝔼.E t ((fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1)) = _
    rw [map_add, map_add, map_smul, map_smul, map_sub, 𝔼.const, hadapt t, hε0 t, smul_zero,
      add_zero]
  have hM : SimpleModel 𝔼 σ κ θ πs π (fun t => (-σ) • r t)
      (fun t => r t + 𝔼.E t (π (t + 1))) r := by
    refine ⟨hadapt, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · simp only [add_sub_cancel_right]
    · funext ω
      simp only [r, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    · simp only [add_sub_cancel_right]
    · rw [hEπ t]
      funext ω
      simp only [r, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hEπ t]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have hls := lam_sub_one (σ := σ) (κ := κ) (θ := θ) hD
      have e : πs + lam σ κ θ * (π t ω - πs) - π t ω = (lam σ κ θ - 1) * (π t ω - πs) := by ring
      rw [e, hls]
      unfold lam
      field_simp
      ring
  refine ⟨hM, (unexpected_inflation_iff hρ0 hρ1 hθ1 hσκ hM).mpr fun t => ?_⟩
  unfold innov
  rw [hadapt (t + 1)]
  change ((fun _ => πs) + lam σ κ θ • (π t - fun _ => πs) +
      (-(coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ))) • ε (t + 1)) - 𝔼.E t (π (t + 1)) = _
  rw [hEπ t]
  abel

/-- Cochrane (2023), §9.4.1, p. 276: with bounded fiscal shocks the solution is bounded,
`|π_t − π^{e*}| ≤ |π_0 − π^{e*}| + k M/(1 − λ)` (`0 ≤ λ < 1`, `0 ≤ k`). -/
theorem solution_bounded {lamv k πs M : ℝ} (hl0 : 0 ≤ lamv) (hl1 : lamv < 1) (hk : 0 ≤ k)
    {π0 : Ω → ℝ} {B0 : ℝ} (hπ0 : ∀ ω, |π0 ω - πs| ≤ B0) {ε : ℕ → Ω → ℝ}
    (hε : ∀ t ω, |ε t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |solPi lamv k πs π0 ε t ω - πs| ≤ B0 + k * M / (1 - lamv) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hε 0 ω)
  have hB0 : 0 ≤ B0 := (abs_nonneg _).trans (hπ0 ω)
  have h1 : 0 < 1 - lamv := by linarith
  induction t with
  | zero =>
    have : 0 ≤ k * M / (1 - lamv) := by positivity
    exact (hπ0 ω).trans (by linarith)
  | succ t ih =>
    simp only [solPi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [show πs + lamv * (solPi lamv k πs π0 ε t ω - πs) + -k * ε (t + 1) ω - πs =
      lamv * (solPi lamv k πs π0 ε t ω - πs) + -k * ε (t + 1) ω by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hl0, abs_neg, abs_of_nonneg hk]
    have h2 : lamv * |solPi lamv k πs π0 ε t ω - πs| ≤ lamv * (B0 + k * M / (1 - lamv)) :=
      mul_le_mul_of_nonneg_left ih hl0
    have h3 : k * |ε (t + 1) ω| ≤ k * M := mul_le_mul_of_nonneg_left (hε (t + 1) ω) hk
    have h4 : lamv * (B0 + k * M / (1 - lamv)) + k * M ≤ B0 + k * M / (1 - lamv) := by
      have e : lamv * (B0 + k * M / (1 - lamv)) + k * M =
          lamv * B0 + k * M / (1 - lamv) := by
        field_simp
        ring
      rw [e]
      nlinarith
    linarith

/-! ### The cases `θ = 0` and `θ = 1` -/

/-- Cochrane (2023), §9.4.1, p. 276: at `θ = 0` (interest-rate peg) the coefficients are
`1/(1 + σκ)` and `(1 − ρ + σκ)/(1 + σκ)`. -/
theorem theta_zero (σ κ ρ : ℝ) :
    lam σ κ 0 = 1 / (1 + σ * κ) ∧
      coefD σ κ 0 ρ / (coefD σ κ 0 ρ + ρ) = (1 - ρ + σ * κ) / (1 + σ * κ) := by
  unfold lam coefD
  constructor
  · ring_nf
  · ring_nf

/-- Cochrane (2023), §9.4.1, p. 276 (`θ = 1`, the spread target, proved directly — error E9.5):
`λ = 0`, `D/(D + ρ) = σκ/(σκ + ρ)`, so in any solution `E_t π_{t+1} = π^{e*}` and
`π_{t+1} = π^{e*} − σκ/(σκ + ρ) ε^{Σs}_{t+1}`: inflation is serially uncorrelated around the
target. -/
theorem theta_one {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hσκ : 0 < σ * κ)
    (hM : SimpleModel 𝔼 σ κ 1 πs π x i r) {ε : ℕ → Ω → ℝ} (hV : Valuation 𝔼 ρ π i ε) (t : ℕ) :
    𝔼.E t (π (t + 1)) = (fun _ => πs) ∧
      π (t + 1) = (fun _ => πs) + (-(σ * κ / (σ * κ + ρ))) • ε (t + 1) := by
  have hl : lam σ κ 1 = 0 := by simp [lam]
  have hD : coefD σ κ 1 ρ = σ * κ := by simp [coefD]
  have h1 : (1 : ℝ) - 1 + σ * κ ≠ 0 := by linarith
  constructor
  · have := eq_9_21 h1 hM t
    rw [hl, zero_smul] at this
    exact sub_eq_zero.mp this
  · have := pi_succ hρ0 hρ1 le_rfl hσκ hM hV t
    rw [hl, hD, zero_smul, add_zero] at this
    exact this

/-- Cochrane (2023), p. 277 (`θ = 1`): output and the real and nominal rates follow inflation,
`x_t = (π_t − π^{e*})/κ`, `r_t = −(π_t − π^{e*})/(σκ)`, `i_t = π^{e*} − (π_t − π^{e*})/(σκ)`. -/
theorem theta_one_paths (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hM : SimpleModel 𝔼 σ κ 1 πs π x i r)
    (t : ℕ) : x t = (1 / κ) • (π t - fun _ => πs) ∧
      r t = (-(1 / (σ * κ))) • (π t - fun _ => πs) ∧
      i t = (fun _ => πs) + (-(1 / (σ * κ))) • (π t - fun _ => πs) := by
  have h21 := eq_9_21_mul hM t
  have hE : 𝔼.E t (π (t + 1)) = fun _ => πs := by
    have hσκ : σ * κ ≠ 0 := mul_ne_zero hσ hκ
    funext ω
    have a := congrFun h21 ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_self, zero_mul, zero_add] at a
    have := (mul_eq_zero.mp a).resolve_left hσκ
    linarith
  have hr := r_eq hM t
  have h18 := hM.is_9_18 t
  have h19 := hM.is_9_19 t
  refine ⟨?_, ?_, ?_⟩
  · funext ω
    have b := congrFun h18 ω
    rw [hE] at b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at b
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linarith
  · funext ω
    have a := congrFun hr ω
    rw [hE] at a
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a ⊢
    field_simp
    linarith
  · funext ω
    have a := congrFun hr ω
    have c := congrFun h19 ω
    rw [hE] at a c
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.add_apply] at a c ⊢
    have hσκ : σ * κ ≠ 0 := mul_ne_zero hσ hκ
    have hr' : r t ω = (πs - π t ω) / (σ * κ) := by
      rw [eq_div_iff hσκ]
      linarith
    rw [show i t ω = r t ω + πs by linarith, hr']
    field_simp
    ring

/-- Cochrane (2023), p. 276, footnote 1 (error E9.5): for `θ ≠ 1` the rule gives
`r_t = (π^{e*} − E_t π_{t+1})/(1 − θ)`; this formula is undefined at `θ = 1`, where `r` is instead
pinned down by `σκ r_t = E_t π_{t+1} − π_t` (`r_eq`). -/
theorem footnote_r (hθ : θ ≠ 1) (hM : SimpleModel 𝔼 σ κ θ πs π x i r) (t : ℕ) :
    r t = (1 / (1 - θ)) • ((fun _ => πs) - 𝔼.E t (π (t + 1))) := by
  have h1 : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  funext ω
  have c := congrFun (hM.is_9_19 t) ω
  have d := congrFun (hM.is_9_20 t) ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.add_apply] at c d ⊢
  field_simp
  linarith

/-- Cochrane (2023), §9.4.1, p. 276 ("at `θ = 1` … equals the `θ → 1` limit"): the coefficient of
(9.23) is continuous in `θ` and tends to `σκ/(σκ + ρ)`, and `λ → 0`. -/
theorem tendsto_coef_theta_one {σ κ ρ : ℝ} (hσκ : 0 < σ * κ) (hρ0 : 0 ≤ ρ) :
    Tendsto (fun θ => coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ)) (𝓝 1) (𝓝 (σ * κ / (σ * κ + ρ))) ∧
      Tendsto (fun θ => lam σ κ θ) (𝓝 1) (𝓝 0) := by
  constructor
  · have h : ContinuousAt (fun θ => coefD σ κ θ ρ / (coefD σ κ θ ρ + ρ)) 1 := by
      unfold coefD
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simp only [sub_self, mul_zero, zero_add]
      linarith
    have := h.tendsto
    simpa [coefD] using this
  · have h : ContinuousAt (fun θ => lam σ κ θ) 1 := by
      unfold lam
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simp only [sub_self, zero_add]
      exact hσκ.ne'
    have := h.tendsto
    simpa [lam] using this

/-! ### The full new-Keynesian model (9.24)–(9.26) -/

variable (𝔼 σ κ πs π x i)
variable (β : ℝ) (ux upi : ℕ → Ω → ℝ)

/-- Cochrane (2023), eqs. (9.24)–(9.25), p. 277: the IS curve `x_t = E_t x_{t+1} − σ(i_t − E_t
π_{t+1}) + u_{x,t}`,
the Phillips curve `π_t = β E_t π_{t+1} + κ x_t + u_{π,t}`, and the spread target `E_t π_{t+1} =
π^{e*}`. -/
structure FullNK where
  is_9_24 : ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1))) + ux t
  is_9_25 : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + upi t
  spread : ∀ t, 𝔼.E t (π (t + 1)) = fun _ => πs

variable {𝔼 σ κ πs π x i β ux upi}

/-- Cochrane (2023), (9.26) first line, p. 277: `κ x_t = π_t − β π^{e*} − u_{π,t}`, i.e.
`x_t = [(1 − β)π^{e*} + ΔE_t π_t − u_{π,t}]/κ` with `ΔE_t π_t = π_t − π^{e*}`. The IS shock `u_x`
does not
appear (given inflation; survey E9.7). -/
theorem x_formula (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (t : ℕ) :
    κ • x t = (fun _ => (1 - β) * πs) + (π t - fun _ => πs) - upi t := by
  have h := hN.is_9_25 t
  rw [hN.spread t] at h
  funext ω
  have a := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at a ⊢
  linarith

/-- Cochrane (2023), §9.4.1, p. 277: with the spread target, the inflation innovation is
`ΔE_{t+1} π_{t+1} = π_{t+1} − π^{e*}` (for adapted inflation). -/
theorem innov_eq (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (hπ : 𝔼.Adapted π) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = π (t + 1) - fun _ => πs := by
  unfold innov
  rw [hπ (t + 1), hN.spread t]

/-- Cochrane (2023), eq. (9.26), p. 277, **corrected** (error E9.4): the real rate
`r_t = i_t − E_t π_{t+1}` obeys
`σ r_t = −ΔE_t π_t/κ + u_{x,t} + (u_{π,t} − E_t u_{π,t+1})/κ` (with `ΔE_t π_t = π_t − π^{e*}`); the
book prints `+ΔE_t π_t/κ` and omits the `1/κ` on the `u_π` terms. -/
theorem r_formula (hκ : κ ≠ 0) (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (t : ℕ) :
    σ • (i t - 𝔼.E t (π (t + 1))) =
      (1 / κ) • (-(π t - fun _ => πs) + (upi t - 𝔼.E t (upi (t + 1)))) + ux t := by
  have h24 := hN.is_9_24 t
  have hx := x_formula hN t
  have hx1 := congrArg (𝔼.E t) (x_formula hN (t + 1))
  rw [map_smul, map_sub, map_add, 𝔼.const, map_sub, hN.spread t, 𝔼.const] at hx1
  funext ω
  have a := congrFun h24 ω
  have b := congrFun hx ω
  have c := congrFun hx1 ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply] at a b c ⊢
  field_simp
  linear_combination κ * a - b + c

/-- Cochrane (2023), eq. (9.26), p. 277 (error E9.4): the printed formula minus the correct one is
`(1/σ)[2 ΔE_t π_t/κ + (1 − 1/κ)(u_{π,t} − E_t u_{π,t+1})]`. -/
theorem printed_minus_corrected (σ κ D ux upi Eupi : ℝ) (hσ : σ ≠ 0) :
    (1 / σ) * (D / κ + ux + upi - Eupi) - (1 / σ) * (-D / κ + ux + (upi - Eupi) / κ) =
      (1 / σ) * (2 * D / κ + (1 - 1 / κ) * (upi - Eupi)) := by
  field_simp
  ring

/-- Cochrane (2023), eq. (9.26), p. 277 (error E9.4, the `1/κ`): a perfect-foresight solution of
(9.24)–(9.25) with the spread target (`β = 1/2`, `σ = 1`, `κ = 2`, `π^{e*} = 0`, `π ≡ 0`, `u_x ≡ 0`,
`u_{π,0} = 1`, `u_{π,t} = 0` for `t ≥ 1`) where the printed formula gives `σ r_0 = 1` but `σ r_0 =
1/2`. -/
theorem printed_9_26_fails_perfectForesight :
    ∃ π x i ux upi : ℕ → Unit → ℝ, FullNK perfectForesight 1 2 0 π x i (1 / 2) ux upi ∧
      1 * (i 0 () - π 1 ()) = 1 / 2 ∧
      (0 - 0) / 2 + ux 0 () + upi 0 () - upi 1 () = 1 := by
  set upi : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 0 with hu
  set x : ℕ → Unit → ℝ := fun t _ => -upi t () / 2 with hx
  refine ⟨fun _ _ => 0, x, fun t _ => x (t + 1) () - x t (), fun _ _ => 0, upi,
    ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · funext ω
    change x t () = x (t + 1) () - 1 * (x (t + 1) () - x t () - 0) + 0
    ring
  · funext ω
    change (0 : ℝ) = 1 / 2 * 0 + 2 * x t () + upi t ()
    simp only [hx]
    ring
  · rfl
  · simp [hx, hu]
    norm_num
  · simp [hu]

/-- Cochrane (2023), §9.4.1, p. 277: the coin-flip inflation used in `printed_9_26_fails_coin`,
`π_t = ε_t` (the mean-zero coin shock). -/
noncomputable def coinPi (t : ℕ) (ω : Bool × Bool) : ℝ := ExpectationsFiniteTree.coinShock t ω

/-- Cochrane (2023), eq. (9.26), p. 277 (error E9.4, the sign): under genuine uncertainty (the
two-coin tree), with `β = 1/2`, `σ = κ = 1`, `π^{e*} = 0`, no shocks `u_x = u_π = 0`, and inflation
equal to a mean-zero coin innovation, (9.24)–(9.25) and the spread target hold, and
`σ r_1 = −ΔE_1 π_1/κ`; at a state with `ΔE_1 π_1 = 1` this is `−1`, while the printed (9.26) gives
`+1`. -/
theorem printed_9_26_fails_coin :
    FullNK ExpectationsFiniteTree.coinSystem 1 1 0 coinPi coinPi
      (fun t => -(ExpectationsFiniteTree.coinSystem.E t (coinPi (t + 1))) + (-1 : ℝ) • coinPi t +
        ExpectationsFiniteTree.coinSystem.E t (coinPi (t + 1))) (1 / 2) 0 0 ∧
      innov ExpectationsFiniteTree.coinSystem 0 (coinPi 1) (true, true) = 1 ∧
      1 * ((-(ExpectationsFiniteTree.coinSystem.E 1 (coinPi 2)) + (-1 : ℝ) • coinPi 1 +
        ExpectationsFiniteTree.coinSystem.E 1 (coinPi 2)) - ExpectationsFiniteTree.coinSystem.E 1
          (coinPi 2)) (true, true) = -1 := by
  have hmean : ∀ t, ExpectationsFiniteTree.coinSystem.E t (coinPi (t + 1)) = 0 := fun t =>
    ExpectationsFiniteTree.coinShock_mean_zero t
  have hadapt : ExpectationsFiniteTree.coinSystem.Adapted coinPi := fun t => by
    funext ω
    rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
      ExpectationsFiniteTree.coinShock_measurable t h
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · simp only [hmean t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    ring
  · simp only [hmean t]
    funext ω
    simp
  · exact (hmean t).trans rfl
  · unfold innov
    rw [hadapt 1, hmean 0]
    simp [coinPi, ExpectationsFiniteTree.coinShock]
  · rw [hmean 1]
    simp [coinPi, ExpectationsFiniteTree.coinShock]

/-! ### Holden's rule -/

/-- Cochrane (2023), §9.4.1, p. 278 (Holden 2020): with the spread rule `i_t = r_t + π* + φ(π_t −
π*)`
and `r_t = i_t − E_t π_{t+1}`, i.e. `E_t π_{t+1} − π* = φ(π_t − π*)`, and `|φ| > 1`, the unique
bounded
inflation process is `π ≡ π*` (new-Keynesian equilibrium selection). -/
theorem holden_unique {φ πs : ℝ} (hφ : 1 < |φ|) {π i r : ℕ → Ω → ℝ}
    (hr : ∀ t, r t = i t - 𝔼.E t (π (t + 1)))
    (hrule : ∀ t, i t = r t + (fun _ => πs) + φ • (π t - fun _ => πs)) (hb : BoundedProc π) :
    π = fun _ _ => πs := by
  have hφ0 : φ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hφ
    linarith
  have hE : ∀ t, 𝔼.E t (π (t + 1)) = (fun _ => πs) + φ • (π t - fun _ => πs) := by
    intro t
    have h1 := hr t
    rw [hrule t] at h1
    funext ω
    have := congrFun h1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  set d : ℕ → Ω → ℝ := fun t => π t - fun _ => πs with hd
  have hdsol : ∀ t, d t = φ⁻¹ • 𝔼.E t (d (t + 1)) + 0 := by
    intro t
    simp only [hd, map_sub, hE t, 𝔼.const, add_zero]
    funext ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  have h0sol : ∀ t, (0 : Ω → ℝ) = φ⁻¹ • 𝔼.E t (0 : Ω → ℝ) + 0 := fun t => by simp
  have hinv : |φ⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hφ
  obtain ⟨M, hM⟩ := hb
  have hdb : BoundedProc d := ⟨M + |πs|, fun t ω => by
    simp only [hd, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)⟩
  have h := 𝔼.forward_unique hinv (u := fun _ => 0) (z₂ := fun _ => 0) hdsol h0sol hdb
    ⟨0, fun _ _ => by simp⟩
  funext t ω
  have := congrFun (congrFun h t) ω
  simp only [hd, Pi.sub_apply, Pi.zero_apply] at this
  linarith

end Cochrane.AssetsRulesBalanceSheets.SpreadTarget
