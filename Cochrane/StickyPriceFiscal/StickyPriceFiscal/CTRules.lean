/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.CTSimple
import StickyPriceFiscal.Expectations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Matrix.Mul

/-!
# Long-term debt and policy rules in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7.3–§5.7.5, pp. 169–179,
(5.105)–(5.117).

Paths are deterministic after the time-`0` news (MIT shocks); the `dδ` and `dε` terms of
(5.105)–(5.113) are the jumps at date `0`.

## Main results

* (5.105): `bond_deviation` (the deviation form of the linearised bond-pricing equation),
  `ct_bond_price` / `ct_bond_price_exists` (the unique bounded bond price is
  `q_t = −∫_0^∞ e^{−(r+ω)τ} i_{t+τ} dτ`), `bond_price_falls`.
* p. 171, partial adjustment: `ct_partial_adj` (`π_t = π₀e^{−ψ(1−θ)t}`), `ct_static_rule`
  (`i = θπ` with `i = π` forces `π = 0`), and in discrete time `discrete_degenerate`
  (`i_t = θE_tπ_{t+1}` with `i_t = E_tπ_{t+1}` forces `E_tπ_{t+1} = 0`), `discrete_dynamics`.
* (5.115), survey E51: `rule_5_115_correct` (the coefficient on `i_{t−1}` is `1/(1+ζ)`),
  `rule_5_115_printed_iff_lagged`, `rule_5_115_counterexample`.
* p. 172, the `v − v*` elimination: `ct_elim` (with the transversality conditions and the
  unstated `v*₀ = v₀`, E49, it gives `v = v*`, `π = π*`), `ct_elim_pi0` (then
  `π₀ = −β_sε_s − β_iε_i`), `ct_elim_needs_initial`.
* (5.116): `ct_nonlinear_pv`, the nonlinear present value iff the transversality condition.
* (5.117): `ct_weighted_identity`; `ct_short_debt_limit` (its left side vanishes as `ω → ∞`),
  `ct_short_debt_identity`, `ct_rules_identity`.
* §5.7.5: `ct_rules_pinned` (with a given interest-rate path, fiscal policy only selects `π₀`),
  the Laplace identities `laplace_deriv`, `laplace_P`, the closed form `ct_pi0_laplace` /
  `ct_pi0_laplace_div` for `π₀` with a surplus rule and `α = 0` (Fig. 5.11; it reproduces
  `π₀ = −0.80`), the constant-rate case `ct_fiscal_rule_step`, `ct_fiscal_rule_negative_iff`
  (a rate rise lowers inflation iff `θ_{sπ}λ₂ > r`, with short-term debt) and
  `ct_fiscal_rule_exists`; backed vs unbacked: `ct_same_weighted_sum`,
  `ct_zero_weighted_sum_iff` (the `β_i` of Fig. 5.13, E52) and
  `ct_zero_weighted_sum_iff_fisherian`.
* A1 §1.13 (real diagonalisable case): `modes_hasDerivAt`, `matrix_solution`
  (`z_t = Qe^{Λt}Q⁻¹z_0`), `matrix_bounded_iff` (bounded iff the explosive modes vanish),
  `matrix_errors`, `matrix_errors_unique` (the expectational errors from the explosive rows),
  `matrix_pv` (`∫ e^{−rt}z = Q diag(1/(r − d))Q⁻¹z_0`); scalar modes `mode_stable_bounded`,
  `mode_zero_unbounded` (E25: zero real part is not stable).
-/

namespace Cochrane.StickyPriceFiscal.CTRules

open Filter Topology MeasureTheory Cochrane.StickyPriceFiscal.CTSimple

/-! ## The bond price (5.105) -/

/-- Cochrane (2023), (5.105) and p. 170: the linearised bond-pricing equation in levels,
`dQ/dt = (R^n − r) + (ω + r)(Q − 1)` with the expectations hypothesis `R^n = i` after the news,
is in deviations `q = Q − 1`, `ĩ = i − r` exactly `dq/dt = (r + ω)q + ĩ`. -/
theorem bond_deviation {Q i : ℝ → ℝ} {r ω t : ℝ}
    (h : HasDerivAt Q ((i t - r) + (ω + r) * (Q t - 1)) t) :
    HasDerivAt (fun u => Q u - 1) ((r + ω) * (Q t - 1) + (i t - r)) t :=
  (h.sub_const 1).congr_deriv (by ring)

/-- Cochrane (2023), (5.105), p. 169: **the bond price is the forward solution**: for `r + ω > 0`
and an interest-rate path continuous and bounded on `[0, ∞)`, every bond-price path continuous
and bounded on `[0, ∞)` with `dq/dt = (r + ω)q + i` on `(0, ∞)` is
`q_t = −∫_0^∞ e^{−(r+ω)τ} i_{t+τ} dτ`. -/
theorem ct_bond_price {r ω M K : ℝ} {i q : ℝ → ℝ} (h : 0 < r + ω)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ s, 0 ≤ s → |i s| ≤ M)
    (hc : ContinuousOn q (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt q ((r + ω) * q t + i t) t)
    (hb : ∀ t, 0 ≤ t → |q t| ≤ K) (t : ℝ) (ht : 0 ≤ t) : q t = -fwdInt (r + ω) i t := by
  rw [ode_forward_bounded h (ext0_continuous hi) (ext0_abs_le hM) hc
    (fun τ hτ => by rw [ext0_eq hτ.le]; exact hd τ hτ) hb t ht,
    fwdInt_congr ht fun s hs => ext0_eq hs]

/-- Cochrane (2023), (5.105), p. 169: **existence**: `q = −∫_0^∞ e^{−(r+ω)τ} i_{t+τ} dτ` is a
bounded solution of the bond-price equation. -/
theorem ct_bond_price_exists {r ω M : ℝ} {i : ℝ → ℝ} (h : 0 < r + ω)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ s, 0 ≤ s → |i s| ≤ M) :
    ContinuousOn (fun t => -fwdInt (r + ω) i t) (Set.Ici 0) ∧
      (∀ t, 0 < t → HasDerivAt (fun t => -fwdInt (r + ω) (ext0 i) t)
        ((r + ω) * (-fwdInt (r + ω) i t) + i t) t) ∧
      ∀ t, 0 ≤ t → |-fwdInt (r + ω) i t| ≤ M / (r + ω) := by
  have hie := ext0_continuous hi
  have hieb := ext0_abs_le hM
  refine ⟨(fwdInt_continuousOn h hi hM).neg, fun t ht => ?_, fun t ht => ?_⟩
  · rw [fwdInt_congr ht.le fun s hs => (ext0_eq hs).symm, ← ext0_eq (f := i) ht.le]
    exact (fwdInt_hasDerivAt h hie hieb t).neg.congr_deriv (by ring)
  · rw [abs_neg]
    exact fwdInt_abs_le h fun s hs => hM s (le_trans ht hs)

/-- Cochrane (2023), p. 174: **higher interest rates give a downward bond-price jump**: for
`r + ω > 0` and a nonnegative interest-rate rise, `q₀ ≤ 0`; for a permanent rise `i₀ > 0`,
`q₀ = −i₀/(r + ω) < 0`. -/
theorem bond_price_falls {r ω : ℝ} {i : ℝ → ℝ} (h : 0 < r + ω) (hi : ∀ s, 0 ≤ s → 0 ≤ i s) :
    -fwdInt (r + ω) i 0 ≤ 0 ∧ ∀ i0, 0 < i0 → -fwdInt (r + ω) (fun _ => i0) 0 < 0 := by
  refine ⟨?_, fun i0 hi0 => ?_⟩
  · rw [neg_nonpos]
    refine setIntegral_nonneg measurableSet_Ioi fun τ (hτ : (0 : ℝ) < τ) => ?_
    exact mul_nonneg (Real.exp_pos _).le (hi _ (by linarith))
  · rw [fwdInt_const h, neg_neg_iff_pos]
    positivity

/-! ## Partial adjustment (p. 171) -/

/-- Cochrane (2023), p. 171: **partial adjustment in continuous time**: with differentiable
prices the Fisher relation is `i = π`; with `di = −ψ(i − θπ)dt`, inflation follows
`dπ = −ψ(1 − θ)π dt`, so `π_t = π₀ e^{−ψ(1−θ)t}`. -/
theorem ct_partial_adj {ψ θ : ℝ} {i π : ℝ → ℝ} (hc : ContinuousOn i (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt i (-ψ * (i t - θ * π t)) t)
    (hf : ∀ t, 0 ≤ t → i t = π t) (t : ℝ) (ht : 0 ≤ t) :
    π t = π 0 * Real.exp (-(ψ * (1 - θ) * t)) := by
  have h := decay_unique (b := ψ * (1 - θ)) hc
    (fun τ hτ => (hd τ hτ).congr_deriv (by rw [← hf τ hτ.le]; ring)) t ht
  rw [← hf t ht, h, hf 0 le_rfl]
  ring

/-- Cochrane (2023), p. 171: a static rule `i = θπ` together with `i = π` and `θ ≠ 1` forces
`π = 0` ("instant dynamics"). -/
theorem ct_static_rule {θ i π : ℝ} (hθ : θ ≠ 1) (h1 : i = θ * π) (h2 : i = π) : π = 0 := by
  have : (1 - θ) * π = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (by linarith : θ = 1) hθ
  · exact h

/-- Cochrane (2023), p. 171: **the discrete-time trap**: a rule responding to expected
inflation, `i_t = θE_tπ_{t+1}`, with the flexible-price Fisher equation `i_t = E_tπ_{t+1}` and
`θ ≠ 1`, forces `E_tπ_{t+1} = 0` (for any expectation system). -/
theorem discrete_degenerate {Ω : Type*} (𝔼 : ExpectationSystem Ω) {θ : ℝ} (hθ : θ ≠ 1)
    {i : ℕ → Ω → ℝ} {π : ℕ → Ω → ℝ} {t : ℕ} (h1 : i t = θ • 𝔼.E t (π (t + 1)))
    (h2 : i t = 𝔼.E t (π (t + 1))) : 𝔼.E t (π (t + 1)) = 0 := by
  funext ω
  have a := congrFun h1 ω
  have b := congrFun h2 ω
  simp only [Pi.smul_apply, smul_eq_mul] at a
  exact ct_static_rule hθ a b

/-- Cochrane (2023), p. 171: the discrete-time rule `i_t = θπ_t` with `i_t = E_tπ_{t+1}` gives
the dynamics `E_tπ_{t+1} = θπ_t` (the lag is built in by the timing convention). -/
theorem discrete_dynamics {Ω : Type*} (𝔼 : ExpectationSystem Ω) {θ : ℝ}
    {i : ℕ → Ω → ℝ} {π : ℕ → Ω → ℝ} {t : ℕ} (h1 : i t = θ • π t)
    (h2 : i t = 𝔼.E t (π (t + 1))) : 𝔼.E t (π (t + 1)) = θ • π t := by
  rw [← h2, h1]

/-! ## (5.115) and survey E51 -/

/-- Cochrane (2023), (5.115), p. 170 (corrected, E51): the discrete partial-adjustment rule
`i_t − i_{t−1} = −ζ[i_t − m_t] + θ_ε ε_t` (with `m_t = θ_π π_t + θ_x x_t + u_t`) is equivalent
to `i_t = i_{t−1}/(1+ζ) + ζ m_t/(1+ζ) + θ_ε ε_t/(1+ζ)` (for `1 + ζ ≠ 0`): the coefficient on
`i_{t−1}` is `1/(1+ζ)`, not the printed `1 − ζ`. -/
theorem rule_5_115_correct {ζ θε it itm1 m ε : ℝ} (hζ : 1 + ζ ≠ 0) :
    it - itm1 = -ζ * (it - m) + θε * ε ↔
      it = itm1 / (1 + ζ) + ζ * m / (1 + ζ) + θε * ε / (1 + ζ) := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), (5.115), p. 170 (E51): the printed form
`i_t = (1 − ζ)i_{t−1} + ζ m_t + θ_ε ε_t` is equivalent to the *lagged* rule
`i_t − i_{t−1} = −ζ[i_{t−1} − m_t] + θ_ε ε_t`. -/
theorem rule_5_115_printed_iff_lagged {ζ θε it itm1 m ε : ℝ} :
    it = (1 - ζ) * itm1 + ζ * m + θε * ε ↔ it - itm1 = -ζ * (itm1 - m) + θε * ε := by
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), (5.115), p. 170 (E51): the printed (5.115) is **not** equivalent to the
displayed rule: with `ζ = 1`, `i_{t−1} = 1`, `m = 0`, `ε = 0`, the rule gives `i_t = 1/2` while
(5.115) gives `i_t = 0`. -/
theorem rule_5_115_counterexample :
    ((1 : ℝ) / 2 - 1 = -1 * ((1 : ℝ) / 2 - 0) + 0 * 0) ∧
      ¬ ((1 : ℝ) / 2 = (1 - 1) * 1 + 1 * 0 + 0 * 0) := by
  norm_num

/-- Cochrane (2023), (5.112) and (5.115), p. 170: the disturbance `u_{t+1} − u_t = −η u_t + ε_t`
is `u_{t+1} = (1 − η)u_t + ε_t` (this part of (5.115) is right). -/
theorem disturbance_ar1 {η u u' ε : ℝ} : u' - u = -η * u + ε ↔ u' = (1 - η) * u + ε := by
  constructor <;> intro h <;> linarith

/-! ## The `v − v*` elimination (p. 172) -/

/-- Cochrane (2023), (5.106), (5.109)–(5.110), p. 172: **eliminating the starred variables.**
After the news, `dv/dt = rv + i − π − s̃` and `dv*/dt = rv* + i − π* − s̃` on `(0, ∞)`;
(5.110) under perfect foresight says `dπ*/dt = dπ/dt` on `(0, ∞)`. If both values of debt
satisfy the transversality condition and **start from the same value** `v*₀ = v₀` (identical
jump terms, survey E49), then `π* = π` and `v* = v` on `[0, ∞)` (`r > 0`). -/
theorem ct_elim {r : ℝ} {i s π πs v vs p : ℝ → ℝ} (hr : 0 < r)
    (hπc : ContinuousOn π (Set.Ici 0)) (hπsc : ContinuousOn πs (Set.Ici 0))
    (hπd : ∀ t, 0 < t → HasDerivAt π (p t) t) (hπsd : ∀ t, 0 < t → HasDerivAt πs (p t) t)
    (hvc : ContinuousOn v (Set.Ici 0)) (hvsc : ContinuousOn vs (Set.Ici 0))
    (hvd : ∀ t, 0 < t → HasDerivAt v (r * v t + i t - π t - s t) t)
    (hvsd : ∀ t, 0 < t → HasDerivAt vs (r * vs t + i t - πs t - s t) t)
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0))
    (htvcs : Tendsto (fun T => Real.exp (-(r * T)) * vs T) atTop (𝓝 0))
    (h0 : vs 0 = v 0) (t : ℝ) (ht : 0 ≤ t) : πs t = π t ∧ vs t = v t := by
  -- `π* − π` is constant
  have hc : ∀ u, 0 ≤ u → πs u - π u = πs 0 - π 0 := fun u hu => by
    have := decay_unique (b := 0) (w := fun x => πs x - π x) (hπsc.sub hπc)
      (fun x hx => ((hπsd x hx).sub (hπd x hx)).congr_deriv (by ring)) u hu
    simpa using this
  set c := πs 0 - π 0
  -- `w = v* − v − c/r` grows at rate `r`
  have hw := decay_unique (b := -r) (w := fun x => vs x - v x - c / r)
    ((hvsc.sub hvc).sub continuousOn_const)
    (fun x hx => (((hvsd x hx).sub (hvd x hx)).sub_const (c / r)).congr_deriv (by
      have := hc x hx.le
      field_simp
      linarith))
  simp only [h0, sub_self, zero_sub] at hw
  -- the transversality conditions force `c = 0`
  have hlim : Tendsto (fun T => Real.exp (-(r * T)) * (vs T - v T)) atTop (𝓝 0) := by
    have := htvcs.sub htvc
    rw [sub_zero] at this
    exact this.congr fun T => by ring
  have hlim2 : Tendsto (fun T => Real.exp (-(r * T)) * (vs T - v T)) atTop (𝓝 (-(c / r))) := by
    have he : Tendsto (fun T => Real.exp (-(r * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
    have := (he.mul_const (c / r)).add_const (-(c / r))
    rw [zero_mul, zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    have hT := hw T hT
    have : vs T - v T = c / r + Real.exp (-(-r * T)) * -(c / r) := by linarith
    rw [this, mul_add, ← mul_assoc, ← Real.exp_add]
    simp
  have hcr : c / r = 0 := by
    have := tendsto_nhds_unique hlim hlim2
    linarith
  have hc0 : c = 0 := by
    rcases div_eq_zero_iff.1 hcr with h | h
    · exact h
    · exact absurd h hr.ne'
  refine ⟨by linarith [hc t ht], ?_⟩
  have := hw t ht
  rw [hcr, neg_zero, mul_zero] at this
  linarith

/-- Cochrane (2023), (5.111) and p. 172: after the elimination, **unexpected inflation is set by
the fiscal innovation**: if in addition the target's time-`0` innovation is
`π*₀ = −β_s ε_s − β_i ε_i` (5.111), then `π₀ = −β_s ε_s − β_i ε_i` (the book's
`dδ_{π} = −β_s dε_s − β_i dε_i`). -/
theorem ct_elim_pi0 {r βs βi es ei : ℝ} {i s π πs v vs p : ℝ → ℝ} (hr : 0 < r)
    (hπc : ContinuousOn π (Set.Ici 0)) (hπsc : ContinuousOn πs (Set.Ici 0))
    (hπd : ∀ t, 0 < t → HasDerivAt π (p t) t) (hπsd : ∀ t, 0 < t → HasDerivAt πs (p t) t)
    (hvc : ContinuousOn v (Set.Ici 0)) (hvsc : ContinuousOn vs (Set.Ici 0))
    (hvd : ∀ t, 0 < t → HasDerivAt v (r * v t + i t - π t - s t) t)
    (hvsd : ∀ t, 0 < t → HasDerivAt vs (r * vs t + i t - πs t - s t) t)
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0))
    (htvcs : Tendsto (fun T => Real.exp (-(r * T)) * vs T) atTop (𝓝 0))
    (h0 : vs 0 = v 0) (hinn : πs 0 = -βs * es - βi * ei) : π 0 = -βs * es - βi * ei := by
  rw [← hinn, (ct_elim hr hπc hπsc hπd hπsd hvc hvsc hvd hvsd htvc htvcs h0 0 le_rfl).1]

/-- Cochrane (2023), p. 172 (E49): **the initial condition `v*₀ = v₀` is needed**: for any
`c ≠ 0`, `π* = π + c` and `v* = v + c/r` satisfy (5.109)–(5.110) and the transversality
condition whenever `(π, v)` satisfy (5.106) and theirs, yet `π* ≠ π`. -/
theorem ct_elim_needs_initial {r c : ℝ} {i s π v : ℝ → ℝ} (hr : 0 < r) (hcne : c ≠ 0)
    (hvd : ∀ t, 0 < t → HasDerivAt v (r * v t + i t - π t - s t) t)
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)) :
    (∀ t, 0 < t → HasDerivAt (fun u => v u + c / r)
      (r * (v t + c / r) + i t - (π t + c) - s t) t) ∧
      Tendsto (fun T => Real.exp (-(r * T)) * (v T + c / r)) atTop (𝓝 0) ∧
      ∀ t, π t + c ≠ π t := by
  refine ⟨fun t ht => ((hvd t ht).add_const (c / r)).congr_deriv (by field_simp; ring), ?_,
    fun t h => hcne (by linarith)⟩
  have he : Tendsto (fun T => Real.exp (-(r * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
  have := htvc.add (he.mul_const (c / r))
  rw [zero_mul, add_zero] at this
  exact this.congr fun T => by ring

/-! ## (5.116): the nonlinear present value -/

/-- Cochrane (2023), (5.116), p. 174: **the nonlinear valuation equation.** Under perfect
foresight the real value of debt obeys `dV/dt = (i − π)V − s` on `(t, ∞)`; with `i − π`
continuous on `[t, ∞)` and the discounted surplus stream integrable, the transversality
condition `e^{−∫_t^T (i−π)} V_T → 0` holds iff
`V_t = ∫_t^∞ e^{−∫_t^τ (i_w − π_w) dw} s_τ dτ`. -/
theorem ct_nonlinear_pv {V i π s : ℝ → ℝ} {t : ℝ}
    (hg : ContinuousOn (fun w => i w - π w) (Set.Ici t)) (hVc : ContinuousOn V (Set.Ici t))
    (hV : ∀ τ, t < τ → HasDerivAt V ((i τ - π τ) * V τ - s τ) τ)
    (hint : IntegrableOn (fun τ => Real.exp (-∫ w in t..τ, (i w - π w)) * s τ) (Set.Ioi t)) :
    Tendsto (fun T => Real.exp (-∫ w in t..T, (i w - π w)) * V T) atTop (𝓝 0) ↔
      V t = ∫ τ in Set.Ioi t, Real.exp (-∫ w in t..τ, (i w - π w)) * s τ := by
  set g : ℝ → ℝ := fun w => i w - π w
  set ge : ℝ → ℝ := fun w => g (max w t) with hge
  have hgec : Continuous ge := hg.comp_continuous (continuous_id.max continuous_const)
    fun w => Set.mem_Ici.2 (le_max_right w t)
  have hint_eq : ∀ τ, t ≤ τ → ∫ w in t..τ, g w = ∫ w in t..τ, ge w := fun τ hτ =>
    intervalIntegral.integral_congr fun w hw => by
      rw [Set.uIcc_of_le hτ] at hw
      simp only [hge, max_eq_left hw.1]
  set Λ : ℝ → ℝ := fun τ => Real.exp (-∫ w in t..τ, ge w) with hΛ
  have hΛd : ∀ τ, HasDerivAt Λ (-(ge τ) * Λ τ) τ := fun τ =>
    ((hgec.integral_hasStrictDerivAt t τ).hasDerivAt.neg.exp).congr_deriv (by simp [hΛ]; ring)
  have hΛc : Continuous Λ := continuous_iff_continuousAt.2 fun τ => (hΛd τ).continuousAt
  have hGd : ∀ τ, t < τ → HasDerivAt (fun u => Λ u * V u) (-(Λ τ * s τ)) τ := fun τ hτ => by
    refine ((hΛd τ).mul (hV τ hτ)).congr_deriv ?_
    simp only [hge, g, max_eq_left hτ.le]
    ring
  have hint' : IntegrableOn (fun τ => Λ τ * s τ) (Set.Ioi t) :=
    hint.congr_fun (fun τ hτ => by simp only [hΛ, hint_eq τ (le_of_lt hτ)]) measurableSet_Ioi
  have hlim := tendsto_of_deriv_Ioi (G := fun u => Λ u * V u) (hΛc.continuousOn.mul hVc) hGd
    hint'.neg
  have hΛt : Λ t = 1 := by simp [hΛ]
  rw [integral_neg, hΛt, one_mul] at hlim
  have hT : (fun T => Real.exp (-∫ w in t..T, g w) * V T) =ᶠ[atTop] fun T => Λ T * V T := by
    filter_upwards [eventually_ge_atTop t] with T hT
    simp only [hΛ, hint_eq T hT]
  have hI : ∫ τ in Set.Ioi t, Real.exp (-∫ w in t..τ, g w) * s τ =
      ∫ τ in Set.Ioi t, Λ τ * s τ :=
    setIntegral_congr_fun measurableSet_Ioi fun τ hτ => by
      simp only [hΛ, hint_eq τ (le_of_lt hτ)]
  change Tendsto (fun T => Real.exp (-∫ w in t..T, g w) * V T) atTop (𝓝 0) ↔
    V t = ∫ τ in Set.Ioi t, Real.exp (-∫ w in t..τ, g w) * s τ
  rw [tendsto_congr' hT, hI]
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro hv
    rw [hv, add_neg_cancel] at hlim
    exact hlim

/-! ## (5.117): the weighted inflation identity -/

/-- Cochrane (2023), (5.117), p. 176: **the weighted inflation identity.** For a response
function with long-term debt (`r > 0`, `ω ≥ 0`): the bond price solves (5.105) and is bounded,
the value of debt solves (5.106) after the news with the transversality condition, and the
value of debt jumps with the bond price (`v₀ = q₀`: face value predetermined, no price-level
jump). Then, with all paths continuous and bounded on `[0, ∞)`,
`∫_0^∞ e^{−(r+ω)τ}π_τ dτ = −∫_0^∞ e^{−rτ}s̃_τ dτ + ∫_0^∞ (e^{−rτ} − e^{−(r+ω)τ})(i_τ − π_τ) dτ`. -/
theorem ct_weighted_identity {r ω Mi Mπ Ms Kq : ℝ} {i π s q v : ℝ → ℝ} (hr : 0 < r)
    (hω : 0 ≤ ω) (hi : ContinuousOn i (Set.Ici 0)) (hMi : ∀ t, 0 ≤ t → |i t| ≤ Mi)
    (hπ : ContinuousOn π (Set.Ici 0)) (hMπ : ∀ t, 0 ≤ t → |π t| ≤ Mπ)
    (hs : ContinuousOn s (Set.Ici 0)) (hMs : ∀ t, 0 ≤ t → |s t| ≤ Ms)
    (hqc : ContinuousOn q (Set.Ici 0))
    (hqd : ∀ t, 0 < t → HasDerivAt q ((r + ω) * q t + i t) t) (hqb : ∀ t, 0 ≤ t → |q t| ≤ Kq)
    (hvc : ContinuousOn v (Set.Ici 0))
    (hvd : ∀ t, 0 < t → HasDerivAt v (r * v t + i t - π t - s t) t)
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)) (h0 : v 0 = q 0) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * π τ =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ) +
        ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) * (i τ - π τ) := by
  have hrw : 0 < r + ω := by linarith
  have hipb : ∀ t, 0 ≤ t → |i t - π t| ≤ Mi + Mπ := fun t ht =>
    (abs_sub _ _).trans (add_le_add (hMi t ht) (hMπ t ht))
  have hfb : ∀ t, 0 ≤ t → |s t - (i t - π t)| ≤ Ms + (Mi + Mπ) := fun t ht =>
    (abs_sub _ _).trans (add_le_add (hMs t ht) (hipb t ht))
  have A1 := integrableOn_of_contOn_bdd hrw le_rfl hi hMi
  have A2 := integrableOn_of_contOn_bdd (g := fun t => i t - π t) hrw le_rfl (hi.sub hπ) hipb
  have A3 := integrableOn_of_contOn_bdd hr le_rfl hs hMs
  have A4 := integrableOn_of_contOn_bdd (g := fun t => i t - π t) hr le_rfl (hi.sub hπ) hipb
  have A5 := integrableOn_of_contOn_bdd (g := fun t => s t - (i t - π t)) hr le_rfl
    (hs.sub (hi.sub hπ)) hfb
  have hq0 := ct_bond_price hrw hi hMi hqc hqd hqb 0 le_rfl
  have hv0 := (ct_value hvc hvd A5).1 htvc
  rw [h0, hq0, fwdInt] at hv0
  simp only [zero_add] at hv0
  have e1 : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * π τ =
      (∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * i τ) -
        ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (i τ - π τ) := by
    rw [← integral_sub A1 A2]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  have e2 : ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
        (i τ - π τ) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (i τ - π τ)) -
        ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (i τ - π τ) := by
    rw [← integral_sub A4 A2]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  have e3 : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - (i τ - π τ)) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ) -
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (i τ - π τ) := by
    rw [← integral_sub A3 A4]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [e1, e2]
  rw [e3] at hv0
  linarith

/-- Cochrane (2023), p. 176: **with short-term debt the left side of (5.117) vanishes**: for any
family of inflation responses uniformly bounded by `K` on `(0, ∞)`,
`∫_0^∞ e^{−(r+ω)τ}π^ω_τ dτ → 0` as `ω → ∞` (short-term debt is `ω = ∞`). -/
theorem ct_short_debt_limit {dπ : ℝ → ℝ → ℝ} {r K : ℝ} (hb : ∀ ω τ, 0 < τ → |dπ ω τ| ≤ K) :
    Tendsto (fun ω => ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * dπ ω τ) atTop (𝓝 0) := by
  have hK : Tendsto (fun ω : ℝ => K / (r + ω)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ r tendsto_id)
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_gt_atTop (-r)] with ω hω
  have ha : 0 < r + ω := by linarith
  have := abs_integral_exp_le (z := dπ ω) ha fun τ hτ => hb ω τ hτ
  rwa [Real.norm_eq_abs]

/-- Cochrane (2023), p. 176: **short-term debt**: if instantaneous debt does not jump at the news
date (`v₀ = 0`) and satisfies the transversality condition, the weighted sum of surpluses equals
the weighted sum of real interest rates, `∫_0^∞ e^{−rτ}s̃_τ dτ = ∫_0^∞ e^{−rτ}(i_τ − π_τ) dτ`. -/
theorem ct_short_debt_identity {r : ℝ} {i π s v : ℝ → ℝ} (hvc : ContinuousOn v (Set.Ici 0))
    (hvd : ∀ t, 0 < t → HasDerivAt v (r * v t + i t - π t - s t) t)
    (hS : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0))
    (hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (i τ - π τ)) (Set.Ioi 0))
    (htvc : Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)) (h0 : v 0 = 0) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (i τ - π τ) := by
  have hint : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - π τ))) (Set.Ioi 0) :=
    (hS.sub hR).congr_fun (fun τ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hv := (ct_value hvc hvd hint).1 htvc
  rw [h0] at hv
  have e : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - (i τ - π τ)) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ) -
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (i τ - π τ) := by
    rw [← integral_sub hS hR]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  linarith

/-! ## §5.7.5: monetary–fiscal coordination with short-term debt -/

/-- Cochrane (2023), (5.105)–(5.113) after the `v = v*` elimination, §5.7.5, pp. 174–178, with
short-term debt (`ω = ∞`, Figs. 5.11–5.13) and an interest-rate path `i` given after the news
(`θ_{iπ} = θ_{ix} = 0`): `(x, π)` is a bounded solution of the IS and Phillips curves, the
surplus follows the rule `s̃ = θ_{sπ}π + θ_{sx}x + αv + u_s`, the value of debt `v` (continuous,
not revalued at `0`: `v₀ = 0`) follows (5.106) and the transversality condition. -/
def IsRulesEq (r σ κ ρ θsπ θsx α : ℝ) (i us x π v s : ℝ → ℝ) : Prop :=
  (IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π) ∧
    (∀ t, 0 ≤ t → s t = θsπ * π t + θsx * x t + α * v t + us t) ∧
      ContinuousOn v (Set.Ici 0) ∧
        (∀ t, 0 < t → HasDerivAt v (r * v t + i t - π t - s t) t) ∧ v 0 = 0 ∧
          Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)

/-- Cochrane (2023), p. 177: **"the interest-rate path sets the family of solutions; fiscal
policy chooses only unexpected inflation at time zero"**: two equilibria with the same
interest-rate path, possibly different fiscal rules (`θ_s`, `α`, `u_s`), and the same `π₀` have
the same inflation and output paths. -/
theorem ct_rules_pinned {r σ κ ρ θsπ θsx α θsπ' θsx' α' M : ℝ}
    {i us x π v s us' x' π' v' s' : ℝ → ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s)
    (h' : IsRulesEq r σ κ ρ θsπ' θsx' α' i us' x' π' v' s') (h0 : π 0 = π' 0) :
    ∀ t, 0 ≤ t → π t = π' t ∧ x t = x' t :=
  ct_family_pinned_by_pi0 hκ hσ hi hM h.1 h'.1 h0

/-- Cochrane (2023), survey item 9 (Laplace identity): for `a > 0` and `f` continuous and
bounded on `[0, ∞)` with `f' = g` on `(0, ∞)`, `g` continuous and bounded on `[0, ∞)`,
`∫_0^∞ e^{−aτ} g_τ dτ = a ∫_0^∞ e^{−aτ} f_τ dτ − f_0`. -/
theorem laplace_deriv {f g : ℝ → ℝ} {a K Kg : ℝ} (ha : 0 < a) (hc : ContinuousOn f (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt f (g t) t) (hb : ∀ t, 0 ≤ t → |f t| ≤ K)
    (hgc : ContinuousOn g (Set.Ici 0)) (hgb : ∀ t, 0 ≤ t → |g t| ≤ Kg) :
    ∫ t in Set.Ioi 0, Real.exp (-(a * t)) * g t =
      a * (∫ t in Set.Ioi 0, Real.exp (-(a * t)) * f t) - f 0 := by
  have If := integrableOn_of_contOn_bdd ha le_rfl hc hb
  have Ig := integrableOn_of_contOn_bdd ha le_rfl hgc hgb
  have hG : ∀ t, 0 < t → HasDerivAt (fun u => Real.exp (-(a * u)) * f u)
      (Real.exp (-(a * t)) * g t - a * (Real.exp (-(a * t)) * f t)) t := fun t ht =>
    ((hasDerivAt_expNeg a t).mul (hd t ht)).congr_deriv (by ring)
  have hGc : ContinuousOn (fun u => Real.exp (-(a * u)) * f u) (Set.Ici 0) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(a * u))).continuousOn.mul hc
  have hlim := tendsto_of_deriv_Ioi hGc hG (Ig.sub (If.const_mul a))
  have h0 := tvc_of_bounded (t := 0) ha fun T hT => hb T hT
  have hu := tendsto_nhds_unique hlim h0
  rw [integral_sub Ig (If.const_mul a), integral_const_mul] at hu
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at hu
  linarith

/-- Cochrane (2023), §5.7.5 and survey item 9: **the Laplace transforms of a bounded solution.**
With `P = ∫_0^∞ e^{−rτ}π`, `X = ∫_0^∞ e^{−rτ}x`, `I = ∫_0^∞ e^{−rτ}i`, `J = ∫_0^∞ e^{−λ₁τ}i`:
`κX = π₀ − (r − ρ)P` and `(λ₁ − r)(r + λ₂) P = κσ(I − J) + (λ₁ − r)π₀`. -/
theorem laplace_P {r σ κ ρ M : ℝ} {i x π : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (h : IsCTSolution σ κ ρ i x π ∧ BddOnIci x ∧ BddOnIci π) :
    κ * (∫ t in Set.Ioi 0, Real.exp (-(r * t)) * x t) =
        π 0 - (r - ρ) * ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * π t ∧
      (lam1 ρ κ σ - r) * (r + lam2 ρ κ σ) * (∫ t in Set.Ioi 0, Real.exp (-(r * t)) * π t) =
        κ * σ * ((∫ t in Set.Ioi 0, Real.exp (-(r * t)) * i t) -
          ∫ t in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * t)) * i t) + (lam1 ρ κ σ - r) * π 0 := by
  obtain ⟨⟨hxc, hπc, hd⟩, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩ := h
  obtain ⟨C, hC⟩ := (ct_family hκ hσ hi hM).1 ⟨⟨hxc, hπc, hd⟩, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩
  set P := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * π t
  set X := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * x t
  set I := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * i t
  set J := ∫ t in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * t)) * i t
  have IP := integrableOn_of_contOn_bdd hr le_rfl hπc hKπ
  have IX := integrableOn_of_contOn_bdd hr le_rfl hxc hKx
  have II := integrableOn_of_contOn_bdd hr le_rfl hi hM
  -- the Phillips curve
  have L1 := laplace_deriv (g := fun t => ρ * π t - κ * x t) (Kg := |ρ| * Kπ + |κ| * Kx) hr hπc
    (fun t ht => (hd t ht).2) hKπ ((continuousOn_const.mul hπc).sub (continuousOn_const.mul hxc))
    (fun t ht => (abs_sub _ _).trans (by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hKπ t ht) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hKx t ht) (abs_nonneg _))))
  have e1 : ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * (ρ * π t - κ * x t) = ρ * P - κ * X := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (IP.const_mul ρ)
      (IX.const_mul κ)]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [e1] at L1
  -- the IS curve
  have L2 := laplace_deriv (g := fun t => σ * (i t - π t)) (Kg := σ * (M + Kπ)) hr hxc
    (fun t ht => (hd t ht).1) hKx (continuousOn_const.mul (hi.sub hπc))
    (fun t ht => by
      rw [abs_mul, abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM t ht) (hKπ t ht)))
        hσ.le)
  have e2 : ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * (σ * (i t - π t)) = σ * (I - P) := by
    rw [← integral_sub II IP, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [e2] at L2
  -- the initial output gap from (5.94)
  have hx0 := (hC 0 le_rfl).2
  have hF0 : fwdInt (lam1 ρ κ σ) i 0 = J := by
    simp only [fwdInt, zero_add, J]
  rw [hF0] at hx0
  have E3 : κ * x 0 = lam1 ρ κ σ * π 0 - κ * σ * J := by
    rw [hx0]
    field_simp
  refine ⟨by linarith, ?_⟩
  linear_combination r * L1 - κ * L2 + E3 + P * lam_mul (ρ := ρ) hκ hσ +
    r * P * lam_sub ρ κ σ

/-- Cochrane (2023), §5.7.5, Fig. 5.11 and Table 5.2: **the Laplace closed form for `π₀` with
`α = 0`.** In any short-term-debt equilibrium with the surplus rule `s̃ = θ_{sπ}π + θ_{sx}x + u_s`
(`α = 0`), with `D = (λ₁ − r)(r + λ₂)`, `Φκ = κ(1 + θ_{sπ}) − θ_{sx}(r − ρ)`,
`I = ∫_0^∞ e^{−rτ}i`, `J = ∫_0^∞ e^{−λ₁τ}i`, `U = ∫_0^∞ e^{−rτ}u_s`:
`π₀(θ_{sx}D + Φκ(λ₁ − r)) = κ(I − U)D − Φκ κσ(I − J)`. (With the Fig. 5.11 parameters this gives
`π₀ = −0.803`.) -/
theorem ct_pi0_laplace {r σ κ ρ θsπ θsx M Mu : ℝ} {i us x π v s : ℝ → ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hu : ContinuousOn us (Set.Ici 0)) (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu)
    (h : IsRulesEq r σ κ ρ θsπ θsx 0 i us x π v s) :
    π 0 * (θsx * ((lam1 ρ κ σ - r) * (r + lam2 ρ κ σ)) +
        (κ * (1 + θsπ) - θsx * (r - ρ)) * (lam1 ρ κ σ - r)) =
      κ * ((∫ t in Set.Ioi 0, Real.exp (-(r * t)) * i t) -
          ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * us t) *
          ((lam1 ρ κ σ - r) * (r + lam2 ρ κ σ)) -
        (κ * (1 + θsπ) - θsx * (r - ρ)) * (κ * σ) *
          ((∫ t in Set.Ioi 0, Real.exp (-(r * t)) * i t) -
            ∫ t in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * t)) * i t) := by
  obtain ⟨hsol, hs, hvc, hvd, hv0, htvc⟩ := h
  obtain ⟨hX, hP⟩ := laplace_P hr hκ hσ hi hM hsol
  obtain ⟨⟨hxc, hπc, -⟩, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩ := hsol
  set P := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * π t
  set X := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * x t
  set I := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * i t
  set U := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * us t
  have IP := integrableOn_of_contOn_bdd hr le_rfl hπc hKπ
  have IX := integrableOn_of_contOn_bdd hr le_rfl hxc hKx
  have II := integrableOn_of_contOn_bdd hr le_rfl hi hM
  have IU := integrableOn_of_contOn_bdd hr le_rfl hu hMu
  have J1 : IntegrableOn (fun τ => (1 + θsπ) * (Real.exp (-(r * τ)) * π τ)) (Set.Ioi 0) :=
    IP.const_mul _
  have J2 : IntegrableOn (fun τ => θsx * (Real.exp (-(r * τ)) * x τ)) (Set.Ioi 0) :=
    IX.const_mul _
  have J12 : IntegrableOn (fun τ => (1 + θsπ) * (Real.exp (-(r * τ)) * π τ) +
      θsx * (Real.exp (-(r * τ)) * x τ)) (Set.Ioi 0) := J1.add J2
  have J123 : IntegrableOn (fun τ => (1 + θsπ) * (Real.exp (-(r * τ)) * π τ) +
      θsx * (Real.exp (-(r * τ)) * x τ) + Real.exp (-(r * τ)) * us τ) (Set.Ioi 0) := J12.add IU
  have J : IntegrableOn (fun τ => (1 + θsπ) * (Real.exp (-(r * τ)) * π τ) +
      θsx * (Real.exp (-(r * τ)) * x τ) + Real.exp (-(r * τ)) * us τ -
        Real.exp (-(r * τ)) * i τ) (Set.Ioi 0) := J123.sub II
  have heq : Set.EqOn (fun τ => (1 + θsπ) * (Real.exp (-(r * τ)) * π τ) +
      θsx * (Real.exp (-(r * τ)) * x τ) + Real.exp (-(r * τ)) * us τ -
        Real.exp (-(r * τ)) * i τ)
      (fun τ => Real.exp (-(r * τ)) * (s τ - (i τ - π τ))) (Set.Ioi 0) := fun τ hτ => by
    simp only [hs τ (le_of_lt hτ)]
    ring
  have hint := IntegrableOn.congr_fun J heq measurableSet_Ioi
  have hval := (ct_value hvc hvd hint).1 htvc
  rw [hv0] at hval
  have hsplit : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s τ - (i τ - π τ)) =
      (1 + θsπ) * P + θsx * X + U - I := by
    rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_sub J123 II,
      integral_add J12 IU, integral_add J1 J2, integral_const_mul, integral_const_mul]
  rw [hsplit] at hval
  linear_combination (-(κ * (1 + θsπ) - θsx * (r - ρ))) * hP +
    (-((lam1 ρ κ σ - r) * (r + lam2 ρ κ σ) * θsx)) * hX +
    (-((lam1 ρ κ σ - r) * (r + lam2 ρ κ σ) * κ)) * hval

/-- Cochrane (2023), §5.7.5, Fig. 5.11: **the closed form for `π₀`** (divided form of
`ct_pi0_laplace`): if `λ₁ ≠ r` and `θ_{sx}/κ + Φ/(r + λ₂) ≠ 0` with
`Φ = 1 + θ_{sπ} − θ_{sx}(r − ρ)/κ`, then
`π₀ = [(I − U) − Φκσ(I − J)/((λ₁ − r)(r + λ₂))] / (θ_{sx}/κ + Φ/(r + λ₂))`. -/
theorem ct_pi0_laplace_div {r σ κ ρ θsπ θsx M Mu : ℝ} {i us x π v s : ℝ → ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hu : ContinuousOn us (Set.Ici 0)) (hMu : ∀ t, 0 ≤ t → |us t| ≤ Mu)
    (h : IsRulesEq r σ κ ρ θsπ θsx 0 i us x π v s) (hne : lam1 ρ κ σ ≠ r)
    (hden : θsx / κ + (1 + θsπ - θsx * (r - ρ) / κ) / (r + lam2 ρ κ σ) ≠ 0) :
    π 0 = (((∫ t in Set.Ioi 0, Real.exp (-(r * t)) * i t) -
        ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * us t) -
        (1 + θsπ - θsx * (r - ρ) / κ) * (κ * σ) *
          ((∫ t in Set.Ioi 0, Real.exp (-(r * t)) * i t) -
            ∫ t in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * t)) * i t) /
          ((lam1 ρ κ σ - r) * (r + lam2 ρ κ σ))) /
      (θsx / κ + (1 + θsπ - θsx * (r - ρ) / κ) / (r + lam2 ρ κ σ)) := by
  have hm := ct_pi0_laplace hr hκ hσ hi hM hu hMu h
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have h1r : lam1 ρ κ σ - r ≠ 0 := sub_ne_zero.2 hne
  have h2r : r + lam2 ρ κ σ ≠ 0 := by linarith
  rw [eq_div_iff hden]
  field_simp
  linear_combination hm

/-- Cochrane (2023), §5.7.5, p. 174: **a permanent interest-rate rise with a surplus rule**
(short-term debt, `α = 0`, `u_s = 0`, constant `i₀`): in any equilibrium
`(π₀ − i₀)(1 + θ_{sπ} + θ_{sx}λ₁/κ) r = −(r + λ₂) i₀ (θ_{sπ} + θ_{sx}ρ/κ)`. -/
theorem ct_fiscal_rule_step {r σ κ ρ θsπ θsx i0 : ℝ} {x π v s : ℝ → ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hσ : 0 < σ)
    (h : IsRulesEq r σ κ ρ θsπ θsx 0 (fun _ => i0) (fun _ => 0) x π v s) :
    (π 0 - i0) * (1 + θsπ + θsx * lam1 ρ κ σ / κ) * r =
      -(r + lam2 ρ κ σ) * i0 * (θsπ + θsx * ρ / κ) := by
  obtain ⟨hsol, hs, hvc, hvd, hv0, htvc⟩ := h
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set D := π 0 - i0
  set c := θsπ * i0 + θsx * ρ * i0 / κ
  set D' := (1 + θsπ) * D + θsx * lam1 ρ κ σ * D / κ
  obtain ⟨hI, hval⟩ := integral_exp_two (c := c) (D := D') hr h2
  have heq : Set.EqOn (fun τ => Real.exp (-(r * τ)) * (c + D' * Real.exp (-(lam2 ρ κ σ * τ))))
      (fun τ => Real.exp (-(r * τ)) * (s τ - (i0 - π τ))) (Set.Ioi 0) := fun τ hτ => by
    obtain ⟨e1, e2⟩ := ct_step_family hκ hσ hsol τ (le_of_lt hτ)
    simp only [hs τ (le_of_lt hτ), e1, e2, c, D', D]
    field_simp
    ring
  have hv := (ct_value (i := fun _ => i0) hvc hvd (hI.congr_fun heq measurableSet_Ioi)).1 htvc
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, hval, hv0] at hv
  have hrl : r + lam2 ρ κ σ ≠ 0 := by linarith
  field_simp at hv
  simp only [c, D'] at hv
  field_simp at hv ⊢
  linear_combination -hv

/-- Cochrane (2023), §5.7.5, p. 175 and Fig. 5.11: **a surplus rule reacting to inflation can make
inflation fall after a rate rise, even with short-term debt.** With `s̃ = θπ` (`θ_{sx} = 0`,
`1 + θ > 0`) and a permanent rise `i₀ > 0`, every equilibrium has
`π₀ = i₀(r − θλ₂)/(r(1 + θ))`, so `π₀ < 0` iff `θλ₂ > r` (`θ = 0` is the Fisherian `π₀ = i₀`). -/
theorem ct_fiscal_rule_negative_iff {r σ κ ρ θ i0 : ℝ} {x π v s : ℝ → ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hσ : 0 < σ) (hθ : 0 < 1 + θ) (hi0 : 0 < i0)
    (h : IsRulesEq r σ κ ρ θ 0 0 (fun _ => i0) (fun _ => 0) x π v s) :
    π 0 = i0 * (r - θ * lam2 ρ κ σ) / (r * (1 + θ)) ∧ (π 0 < 0 ↔ r < θ * lam2 ρ κ σ) := by
  have hf := ct_fiscal_rule_step hr hκ hσ h
  simp only [zero_mul, zero_div, add_zero] at hf
  have hπ0 : π 0 = i0 * (r - θ * lam2 ρ κ σ) / (r * (1 + θ)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hf
  refine ⟨hπ0, ?_⟩
  rw [hπ0, div_neg_iff]
  constructor
  · rintro (⟨-, hb⟩ | ⟨hn, -⟩)
    · exact absurd hb (not_lt.2 (by positivity))
    · by_contra hc
      push Not at hc
      have : 0 ≤ i0 * (r - θ * lam2 ρ κ σ) := mul_nonneg hi0.le (by linarith)
      linarith
  · intro hlt
    right
    exact ⟨mul_neg_of_pos_of_neg hi0 (by linarith), by positivity⟩

/-- Cochrane (2023), §5.7.5, Fig. 5.11: **existence**: with `s̃ = θπ`, `1 + θ > 0`, short-term debt
and a permanent rise `i₀`, an equilibrium exists (with `π₀ = i₀(r − θλ₂)/(r(1 + θ))`); hence for
`θλ₂ > r` and `i₀ > 0` there is an equilibrium in which inflation falls on impact. -/
theorem ct_fiscal_rule_exists {r σ κ ρ θ i0 : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ)
    (hθ : 0 < 1 + θ) :
    ∃ x π v s : ℝ → ℝ, IsRulesEq r σ κ ρ θ 0 0 (fun _ => i0) (fun _ => 0) x π v s ∧
      π 0 = i0 * (r - θ * lam2 ρ κ σ) / (r * (1 + θ)) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set π0 := i0 * (r - θ * lam2 ρ κ σ) / (r * (1 + θ))
  obtain ⟨x, π, hsol, hπ0⟩ := ct_family_exists (ρ := ρ) (M := |i0|) hκ hσ
    (i := fun _ => i0) continuousOn_const (fun _ _ => le_refl _) π0
  obtain ⟨Kπ, hKπ⟩ := hsol.2.2
  set f : ℝ → ℝ := fun t => θ * π t - (i0 - π t) with hfdef
  have hfc : ContinuousOn f (Set.Ici 0) :=
    (continuousOn_const.mul hsol.1.2.1).sub (continuousOn_const.sub hsol.1.2.1)
  have hfb : ∀ t, 0 ≤ t → |f t| ≤ |θ| * Kπ + (|i0| + Kπ) := fun t ht => by
    calc |θ * π t - (i0 - π t)| ≤ |θ * π t| + (|i0| + |π t|) :=
          (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ |θ| * Kπ + (|i0| + Kπ) := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hKπ t ht) (abs_nonneg θ))
            (add_le_add le_rfl (hKπ t ht))
  have hfe := ext0_continuous hfc
  have hfeb := ext0_abs_le hfb
  refine ⟨x, π, fwdInt r (ext0 f), fun t => θ * π t, ⟨hsol, fun t _ => by ring,
    (fwdInt_continuous hr hfe hfeb).continuousOn,
    fun t ht => (fwdInt_hasDerivAt hr hfe hfeb t).congr_deriv ?_, ?_,
    tvc_of_bounded (t := 0) hr fun T _ => fwdInt_abs_le hr fun u _ => hfeb u⟩, hπ0⟩
  · rw [ext0_eq ht.le, hfdef]
    ring
  · -- the valuation equation holds with `v₀ = 0` at this `π₀`
    obtain ⟨-, hval⟩ := integral_exp_two (c := θ * i0) (D := (1 + θ) * (π0 - i0)) hr h2
    have hv : fwdInt r (ext0 f) 0 =
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
          (θ * i0 + (1 + θ) * (π0 - i0) * Real.exp (-(lam2 ρ κ σ * τ))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : (0 : ℝ) < τ) => ?_
      simp only [zero_add, ext0_eq hτ.le, hfdef, (ct_step_family hκ hσ hsol τ hτ.le).1, hπ0]
      ring
    rw [hv, hval]
    have hrl : r + lam2 ρ κ σ ≠ 0 := by linarith
    simp only [π0]
    field_simp
    ring

/-- Cochrane (2023), §5.7.5, p. 176 and Table 5.2: in any short-term-debt equilibrium whose
weighted sum of surpluses exists, `∫_0^∞ e^{−rτ}s̃_τ dτ = I − P` with `I = ∫ e^{−rτ}i` and
`P = ∫ e^{−rτ}π` ((5.117) at `ω = ∞`). -/
theorem ct_rules_identity {r σ κ ρ θsπ θsx α M : ℝ} {i us x π v s : ℝ → ℝ} (hr : 0 < r)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s)
    (hS : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0)) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * i τ) -
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * π τ := by
  obtain ⟨hsol, -, hvc, hvd, hv0, htvc⟩ := h
  obtain ⟨Kπ, hKπ⟩ := hsol.2.2
  have II := integrableOn_of_contOn_bdd hr le_rfl hi hM
  have IP := integrableOn_of_contOn_bdd hr le_rfl hsol.1.2.1 hKπ
  have hR : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (i τ - π τ)) (Set.Ioi 0) :=
    (II.sub IP).congr_fun (fun τ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  rw [ct_short_debt_identity hvc hvd hS hR htvc hv0, ← integral_sub II IP]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  ring

/-- Cochrane (2023), §5.7.5, p. 178, Fig. 5.13 and Table 5.2 (survey E52, E53): **zero weighted
sum of surpluses** (`L(r) = 0`, printed "`L(D) = 0`"). In any short-term-debt equilibrium (any
fiscal rule) with `λ₁ ≠ r`, `∫_0^∞ e^{−rτ}s̃_τ dτ = 0` iff
`π₀ = (r + λ₂)I − κσ(I − J)/(λ₁ − r)`. (With the Fig. 5.13 parameters this is `π₀ = 0.5085`,
i.e. `β_i = −0.5085` as in the text and caption, not the `−0.91` of Table 5.2.) -/
theorem ct_zero_weighted_sum_iff {r σ κ ρ θsπ θsx α M : ℝ} {i us x π v s : ℝ → ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hσ : 0 < σ) (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M)
    (hne : lam1 ρ κ σ ≠ r) (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s)
    (hS : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0)) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ = 0 ↔
      π 0 = (r + lam2 ρ κ σ) * (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * i τ) -
        κ * σ * ((∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * i τ) -
          ∫ τ in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * τ)) * i τ) / (lam1 ρ κ σ - r) := by
  have hid := ct_rules_identity hr hi hM h hS
  have hP := (laplace_P hr hκ hσ hi hM h.1).2
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have h1r : lam1 ρ κ σ - r ≠ 0 := sub_ne_zero.2 hne
  set I := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * i τ
  set J := ∫ τ in Set.Ioi 0, Real.exp (-(lam1 ρ κ σ * τ)) * i τ
  set P := ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * π τ
  rw [hid, sub_eq_zero]
  constructor
  · intro hIP
    have key : (lam1 ρ κ σ - r) * π 0 =
        (lam1 ρ κ σ - r) * (r + lam2 ρ κ σ) * I - κ * σ * (I - J) := by
      rw [← hIP] at hP
      linarith
    field_simp
    linear_combination key
  · intro h0
    have hD : (lam1 ρ κ σ - r) * (r + lam2 ρ κ σ) ≠ 0 := mul_ne_zero h1r (by linarith)
    refine mul_left_cancel₀ hD ?_
    rw [hP, h0]
    field_simp
    ring

/-- Cochrane (2023), §5.7.5, pp. 177–178: **backed vs unbacked**: two short-term-debt equilibria
with the same interest-rate path (and `λ₁ ≠ r`), under possibly different fiscal rules, have the
same weighted sum of surpluses iff they have the same `π₀`, and then identical inflation and
output paths. -/
theorem ct_same_weighted_sum {r σ κ ρ θsπ θsx α θsπ' θsx' α' M : ℝ}
    {i us x π v s us' x' π' v' s' : ℝ → ℝ} (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ)
    (hi : ContinuousOn i (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → |i t| ≤ M) (hne : lam1 ρ κ σ ≠ r)
    (h : IsRulesEq r σ κ ρ θsπ θsx α i us x π v s)
    (h' : IsRulesEq r σ κ ρ θsπ' θsx' α' i us' x' π' v' s')
    (hS : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0))
    (hS' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s' τ) (Set.Ioi 0)) :
    (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ =
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ ↔ π 0 = π' 0) ∧
      (π 0 = π' 0 → ∀ t, 0 ≤ t → π t = π' t ∧ x t = x' t) := by
  refine ⟨?_, fun h0 => ct_rules_pinned hκ hσ hi hM h h' h0⟩
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have h1r : lam1 ρ κ σ - r ≠ 0 := sub_ne_zero.2 hne
  have hD : (lam1 ρ κ σ - r) * (r + lam2 ρ κ σ) ≠ 0 := mul_ne_zero h1r (by linarith)
  have hP := (laplace_P hr hκ hσ hi hM h.1).2
  have hP' := (laplace_P hr hκ hσ hi hM h'.1).2
  rw [ct_rules_identity hr hi hM h hS, ct_rules_identity hr hi hM h' hS', sub_right_inj]
  constructor
  · intro hPP
    have : (lam1 ρ κ σ - r) * π 0 = (lam1 ρ κ σ - r) * π' 0 := by
      rw [hPP] at hP
      linarith
    exact mul_left_cancel₀ h1r this
  · intro h0
    refine mul_left_cancel₀ hD ?_
    rw [hP, hP', h0]

/-- Cochrane (2023), p. 178: **"the parameter configuration that produces no weighted sum of
surpluses is essentially Fisherian"** — exactly so for a permanent rate rise: in any
short-term-debt equilibrium with constant `i₀` (any fiscal rule), the weighted sum of surpluses
is `−(π₀ − i₀)/(r + λ₂)`, so it is zero iff `π₀ = i₀` iff `π_t = i₀` for all `t ≥ 0`. -/
theorem ct_zero_weighted_sum_iff_fisherian {r σ κ ρ θsπ θsx α i0 : ℝ} {us x π v s : ℝ → ℝ}
    (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ)
    (h : IsRulesEq r σ κ ρ θsπ θsx α (fun _ => i0) us x π v s)
    (hS : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0)) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ = -(π 0 - i0) / (r + lam2 ρ κ σ) ∧
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ = 0 ↔ π 0 = i0) ∧
        (π 0 = i0 ↔ ∀ t, 0 ≤ t → π t = i0) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hfam := fun t (ht : 0 ≤ t) => (ct_step_family hκ hσ h.1 t ht).1
  have hid := ct_rules_identity (M := |i0|) hr continuousOn_const (fun _ _ => le_refl _) h hS
  obtain ⟨-, hval⟩ := integral_exp_two (c := (0 : ℝ)) (D := -(π 0 - i0)) hr h2
  simp only [zero_div, zero_add] at hval
  have hR : (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * i0) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * π τ = -(π 0 - i0) / (r + lam2 ρ κ σ) := by
    obtain ⟨Kπ, hKπ⟩ := h.1.2.2
    have II := integrableOn_of_contOn_bdd (g := fun _ => i0) (K := |i0|) hr le_rfl
      continuousOn_const (fun _ _ => le_refl _)
    have IP := integrableOn_of_contOn_bdd hr le_rfl h.1.1.2.1 hKπ
    rw [← integral_sub II IP, ← hval]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : (0 : ℝ) < τ) => ?_
    simp only [hfam τ hτ.le]
    ring
  rw [hid, hR]
  have hrl : 0 < r + lam2 ρ κ σ := by linarith
  refine ⟨rfl, ?_, ⟨fun h0 t ht => by rw [hfam t ht, h0]; ring, fun h0 => by
    simpa using h0 0 le_rfl⟩⟩
  rw [div_eq_zero_iff, neg_eq_zero, sub_eq_zero]
  constructor
  · rintro (h0 | h0)
    · exact h0
    · exact absurd h0 hrl.ne'
  · exact fun h0 => Or.inl h0

/-! ## Online Appendix A1 §1.13: the continuous-time matrix method -/

/-- Cochrane (2023), A1 §1.13, p. 583 and survey E25: **a scalar stable mode** `w' = λw + f` with
`λ < 0` and bounded continuous forcing: every solution is bounded on `[0, ∞)` (the initial value
is free). -/
theorem mode_stable_bounded {l M : ℝ} {w f : ℝ → ℝ} (hl : l < 0) (hf : Continuous f)
    (hM : ∀ s, |f s| ≤ M) (hc : ContinuousOn w (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt w (l * w t + f t) t) :
    ∀ t, 0 ≤ t → |w t| ≤ |w 0| + M / (-l) := by
  intro t ht
  have h := (ode_backward (b := -l) (y := w) hf).1
    ⟨hc, fun τ hτ => (hd τ hτ).congr_deriv (by ring)⟩ t ht
  rw [h]
  have he : |Real.exp (-(-l * t)) * w 0| ≤ |w 0| := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    rw [Real.exp_le_one_iff]
    nlinarith
  exact (abs_add_le _ _).trans (add_le_add he
    (bwdInt_abs_le (by linarith) ht fun s _ _ => hM s))

/-- Cochrane (2023), A1 §1.13, p. 583 and survey E25: **a zero eigenvalue is not stable**: for
`w' = 0·w + 1` (bounded forcing) no solution is bounded on `[0, ∞)`; so rows with zero real
part cannot be classed with the stable rows ("real part less than or equal to zero"). -/
theorem mode_zero_unbounded {w : ℝ → ℝ} (hc : ContinuousOn w (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt w (0 * w t + 1) t) : ¬ ∃ K, ∀ t, 0 ≤ t → |w t| ≤ K := by
  rintro ⟨K, hK⟩
  have h := decay_unique (b := 0) (w := fun u => w u - u)
    (hc.sub continuousOn_id) (fun τ hτ => ((hd τ hτ).sub (hasDerivAt_id τ)).congr_deriv (by ring))
  have h1 := h (|K| + |w 0| + 1) (by positivity)
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, sub_zero] at h1
  have := hK (|K| + |w 0| + 1) (by positivity)
  rw [abs_le] at this
  have := neg_abs_le (w 0)
  have := le_abs_self K
  linarith

/-- Cochrane (2023), A1 §1.13, p. 583: **the modes of a diagonalisable system.** If
`A = QΛQ⁻¹` with `Λ = diag(d)` (real eigenvalues) and `z' = Az`, then each mode
`z̃_k = (Q⁻¹z)_k` obeys `z̃_k' = d_k z̃_k`. -/
theorem modes_hasDerivAt {n : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    {z : ℝ → Fin n → ℝ} {t : ℝ} (hA : A = Q * Matrix.diagonal d * Qi) (hQ : Qi * Q = 1)
    (hz : HasDerivAt z (A.mulVec (z t)) t) (k : Fin n) :
    HasDerivAt (fun u => Qi.mulVec (z u) k) (d k * Qi.mulVec (z t) k) t := by
  have hj := fun j => (hasDerivAt_pi.1 hz j).const_mul (Qi k j)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hj j
  have hval : Qi.mulVec (A.mulVec (z t)) = (Matrix.diagonal d).mulVec (Qi.mulVec (z t)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA, ← mul_assoc, ← mul_assoc, hQ, one_mul]
  have hk := congrFun hval k
  rw [Matrix.mulVec_diagonal] at hk
  rw [← hk]
  exact hs

/-- Cochrane (2023), A1 §1.13, pp. 581–583: **the solution of a diagonalisable system**: along
`z' = Az` on `(0, ∞)`, `z` continuous on `[0, ∞)`, `z_t = Q e^{Λt} Q⁻¹ z_0` for `t ≥ 0`. -/
theorem matrix_solution {n : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    {z : ℝ → Fin n → ℝ} (hA : A = Q * Matrix.diagonal d * Qi) (hQ : Qi * Q = 1)
    (hQ' : Q * Qi = 1) (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t) (t : ℝ) (ht : 0 ≤ t) :
    (∀ k, Qi.mulVec (z t) k = Real.exp (d k * t) * Qi.mulVec (z 0) k) ∧
      z t = Q.mulVec fun k => Real.exp (d k * t) * Qi.mulVec (z 0) k := by
  have hw : ∀ k, Qi.mulVec (z t) k = Real.exp (d k * t) * Qi.mulVec (z 0) k := by
    intro k
    have hcont : ContinuousOn (fun u => Qi.mulVec (z u) k) (Set.Ici 0) := by
      simp only [Matrix.mulVec, dotProduct]
      exact continuousOn_finsetSum _ fun j _ =>
        continuousOn_const.mul ((continuous_apply j).comp_continuousOn hc)
    have h := decay_unique (b := -d k) hcont
      (fun τ hτ => (modes_hasDerivAt hA hQ (hd τ hτ) k).congr_deriv (by ring)) t ht
    rw [h]
    ring_nf
  refine ⟨hw, ?_⟩
  have : z t = Q.mulVec (Qi.mulVec (z t)) := by
    rw [Matrix.mulVec_mulVec, hQ', Matrix.one_mulVec]
  rw [this]
  congr 1
  funext k
  exact hw k

/-- Cochrane (2023), A1 §1.13, p. 583: **"to have `E_t z̃_{t+j}` not explode, we must have
`z̃_+ = 0`"** — and conversely. For a diagonalisable `A = QΛQ⁻¹` with real eigenvalues, a solution
of `z' = Az` after the news is bounded on `[0, ∞)` iff every explosive mode (`d_k > 0`) starts at
zero, `(Q⁻¹z_0)_k = 0`. (Zero eigenvalues give bounded constant modes here; see
`mode_zero_unbounded` for why they still do not count as stable, E25.) -/
theorem matrix_bounded_iff {n : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    {z : ℝ → Fin n → ℝ} (hA : A = Q * Matrix.diagonal d * Qi) (hQ : Qi * Q = 1)
    (hQ' : Q * Qi = 1) (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t) :
    (∃ K, ∀ t, 0 ≤ t → ∀ j, |z t j| ≤ K) ↔ ∀ k, 0 < d k → Qi.mulVec (z 0) k = 0 := by
  constructor
  · rintro ⟨K, hK⟩ k hk
    by_contra hne
    set C := ∑ j, |Qi k j| * K
    have hbound : ∀ t, 0 ≤ t → Real.exp (d k * t) * |Qi.mulVec (z 0) k| ≤ C := by
      intro t ht
      have h := (matrix_solution hA hQ hQ' hc hd t ht).1 k
      rw [← abs_of_pos (Real.exp_pos (d k * t)), ← abs_mul, ← h]
      simp only [Matrix.mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hK t ht j) (abs_nonneg _)
    have hw0 : 0 < |Qi.mulVec (z 0) k| := abs_pos.2 hne
    have hC : 0 ≤ C := le_trans (by positivity) (hbound 0 le_rfl)
    set t := C / (|Qi.mulVec (z 0) k| * d k)
    have ht : 0 ≤ t := by positivity
    have h1 := hbound t ht
    have h2 := Real.add_one_le_exp (d k * t)
    have h3 : |Qi.mulVec (z 0) k| * (d k * t) = C := by
      simp only [t]
      field_simp
    nlinarith
  · intro h0
    refine ⟨∑ j, ∑ k, |Q j k| * |Qi.mulVec (z 0) k|, fun t ht j => ?_⟩
    rw [(matrix_solution hA hQ hQ' hc hd t ht).2]
    simp only [Matrix.mulVec, dotProduct]
    have hrow : |∑ k, Q j k * (Real.exp (d k * t) * ∑ x, Qi k x * z 0 x)| ≤
        ∑ k, |Q j k| * |Qi.mulVec (z 0) k| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      by_cases hk : 0 < d k
      · have := h0 k hk
        simp only [Matrix.mulVec, dotProduct] at this
        rw [this, abs_zero, mul_zero]
        exact abs_nonneg _
      · refine mul_le_of_le_one_left (abs_nonneg _) ?_
        rw [Real.exp_le_one_iff]
        push Not at hk
        nlinarith
    refine hrow.trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ k, |Q j k| * |Qi.mulVec (z 0) k|)
      (fun j _ => Finset.sum_nonneg fun k _ => by positivity) (Finset.mem_univ j)

/-- Cochrane (2023), A1 §1.13, p. 583, (1.53): **the expectational errors are found from the
explosive rows.** After a shock `ε` at `0` with expectational errors `δ` (`z_0 = Bε + Cδ`, pre-shock
values zero), the response is bounded iff `(Q⁻¹C δ)_k = −(Q⁻¹B ε)_k` for every explosive `k`. -/
theorem matrix_errors {n m p : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {C : Matrix (Fin n) (Fin p) ℝ} {ε : Fin m → ℝ}
    {δ : Fin p → ℝ} {z : ℝ → Fin n → ℝ} (hA : A = Q * Matrix.diagonal d * Qi)
    (hQ : Qi * Q = 1) (hQ' : Q * Qi = 1) (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t)
    (h0 : z 0 = B.mulVec ε + C.mulVec δ) :
    (∃ K, ∀ t, 0 ≤ t → ∀ j, |z t j| ≤ K) ↔
      ∀ k, 0 < d k → (Qi * C).mulVec δ k = -((Qi * B).mulVec ε k) := by
  rw [matrix_bounded_iff hA hQ hQ' hc hd, h0, Matrix.mulVec_add]
  refine forall_congr' fun k => imp_congr_right fun _ => ?_
  rw [Pi.add_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), A1 §1.13, p. 583: **uniqueness of the expectational errors** "so long as
`Q₊⁻¹C` is invertible": if `η ↦ ((Q⁻¹Cη)_k)_{d_k > 0}` is injective, two bounded responses to the
same shock `ε` have the same expectational errors. -/
theorem matrix_errors_unique {n m p : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {C : Matrix (Fin n) (Fin p) ℝ} {ε : Fin m → ℝ}
    {δ δ' : Fin p → ℝ} {z z' : ℝ → Fin n → ℝ} (hA : A = Q * Matrix.diagonal d * Qi)
    (hQ : Qi * Q = 1) (hQ' : Q * Qi = 1)
    (hinj : ∀ η : Fin p → ℝ, (∀ k, 0 < d k → (Qi * C).mulVec η k = 0) → η = 0)
    (hc : ContinuousOn z (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t)
    (h0 : z 0 = B.mulVec ε + C.mulVec δ) (hb : ∃ K, ∀ t, 0 ≤ t → ∀ j, |z t j| ≤ K)
    (hc' : ContinuousOn z' (Set.Ici 0)) (hd' : ∀ t, 0 < t → HasDerivAt z' (A.mulVec (z' t)) t)
    (h0' : z' 0 = B.mulVec ε + C.mulVec δ') (hb' : ∃ K, ∀ t, 0 ≤ t → ∀ j, |z' t j| ≤ K) :
    δ = δ' := by
  have e := (matrix_errors hA hQ hQ' hc hd h0).1 hb
  have e' := (matrix_errors hA hQ hQ' hc' hd' h0').1 hb'
  have := hinj (δ - δ') fun k hk => by
    rw [Matrix.mulVec_sub, Pi.sub_apply, e k hk, e' k hk, sub_self]
  exact sub_eq_zero.1 this

/-- Cochrane (2023), A1 §1.13, p. 585 (Table 5.2 terms, `∫ e^{(Λ* − rI)τ} dτ = diag(1/(r − λ))`):
for a bounded response of a diagonalisable system and `r > 0`, the discounted integral of each
variable is `∫_0^∞ e^{−rt} z_t dt = Q diag(1/(r − d_k)) Q⁻¹ z_0`. -/
theorem matrix_pv {n : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    {z : ℝ → Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hA : A = Q * Matrix.diagonal d * Qi)
    (hQ : Qi * Q = 1) (hQ' : Q * Qi = 1) (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t)
    (hb : ∃ K, ∀ t, 0 ≤ t → ∀ j, |z t j| ≤ K) (j : Fin n) :
    ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * z t j =
      Q.mulVec (fun k => Qi.mulVec (z 0) k / (r - d k)) j := by
  have h0 := (matrix_bounded_iff hA hQ hQ' hc hd).1 hb
  have hterm : ∀ k, IntegrableOn (fun t => Q j k * (Real.exp (-(r * t)) *
      (Real.exp (d k * t) * Qi.mulVec (z 0) k))) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, Q j k * (Real.exp (-(r * t)) *
        (Real.exp (d k * t) * Qi.mulVec (z 0) k)) = Q j k * (Qi.mulVec (z 0) k / (r - d k)) := by
    intro k
    by_cases hk : 0 < d k
    · simp only [h0 k hk, mul_zero, zero_div]
      exact ⟨integrableOn_zero, integral_zero _ _⟩
    · push Not at hk
      have hrd : 0 < r - d k := by linarith
      have he : ∀ t, Real.exp (-(r * t)) * (Real.exp (d k * t) * Qi.mulVec (z 0) k) =
          Qi.mulVec (z 0) k * Real.exp (-((r - d k) * t)) := fun t => by
        have : Real.exp (-((r - d k) * t)) = Real.exp (-(r * t)) * Real.exp (d k * t) := by
          rw [← Real.exp_add]; ring_nf
        rw [this]
        ring
      simp only [he]
      refine ⟨((integrableOn_exp_Ioi hrd).const_mul _).const_mul _, ?_⟩
      rw [integral_const_mul, integral_const_mul, integral_exp_Ioi hrd]
      ring
  have hfun : Set.EqOn (fun t => Real.exp (-(r * t)) * z t j)
      (fun t => ∑ k, Q j k * (Real.exp (-(r * t)) * (Real.exp (d k * t) * Qi.mulVec (z 0) k)))
      (Set.Ioi 0) := fun t ht => by
    simp only
    rw [(matrix_solution hA hQ hQ' hc hd t (le_of_lt ht)).2]
    change Real.exp (-(r * t)) * ∑ k, Q j k * (Real.exp (d k * t) * Qi.mulVec (z 0) k) = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun,
    integral_finsetSum _ fun k _ => (hterm k).1]
  exact Finset.sum_congr rfl fun k _ => (hterm k).2

end Cochrane.StickyPriceFiscal.CTRules
