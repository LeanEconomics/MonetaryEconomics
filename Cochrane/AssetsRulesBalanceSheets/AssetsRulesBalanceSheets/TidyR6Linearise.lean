/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.SpreadTarget
import AssetsRulesBalanceSheets.MaturityBuffer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# (3.20), (3.21) and (9.22) derived from the nonlinear valuation equation, with remainders

Cochrane (2023), *The Fiscal Theory of the Price Level*, §3.5, eqs. (3.17)–(3.21), pp. 62–65,
Online Appendix §§1.2–1.3, eqs. (1.9)–(1.13) and (1.21)–(1.25), pp. 556–564, and §9.4.1,
eq. (9.22), p. 275.

The module MaturityBuffer takes the linearised identities (3.20)–(3.21) as model equations
(`MaturityBuffer.Identity320`, `MaturityBuffer.Identity321`), and the module SpreadTarget takes
(9.22) as one (`SpreadTarget.Valuation`). Here they are derived from the exact nonlinear
identities, with an explicit second-order bound on the error.

## The linearisation with remainder

* `log_one_add_sub_le`, `exp_sub_one_le`, `log_lin` (**the scalar step**): for `c > 0`,
  `A = c + ȳ > 0`, `|z| ≤ 1` and `u = (c(eᶻ − 1) + (y − ȳ))/A` with `|u| ≤ 1/2`,
  `log(c eᶻ + y) = log A + (c/A) z + (y − ȳ)/A + R` with `|R| ≤ 2u² + (c/A) z²`;
  `log_lin_bound`: `|R| ≤ 2(2ρδ_z + δ_y/A)² + ρδ_z²` when `|z| ≤ δ_z ≤ 1`, `|y − ȳ| ≤ δ_y`.
  `log_lin_hasDerivAt`: the linear coefficients are the exact partial derivatives.

## (3.17) and (3.20)

* The exact flow (1.9) is `v_t + r_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})` (`v` the log
  value of debt to GDP, `r` the log real return, `g` log growth, `sy` the surplus to GDP ratio).
  Around `(v̄, s̄y)`, `s̄y > 0`: `ρ = e^{v̄}/(e^{v̄} + s̄y) ∈ (0, 1)` (`rho_mem`),
  `s̃ = sy/(e^{v̄} + s̄y)` (the book's `ρ sy/e^{v̄}`), and `flow_exact`:
  `v_t + r_{t+1} − g_{t+1} = κ + ρ v_{t+1} + s̃_{t+1} + R_{t+1}` exactly, with the remainder
  `R = remF` bounded by `remF_bound`.
* `unexpected_inflation_identity` (**(3.20) with remainder**): for bounded processes with `v`
  adapted and `r = rⁿ − π`, at every date and state
  `ΔE π_{t+1} − ΔE rⁿ_{t+1} = −∑ ρʲ ΔE s̃_{t+1+j} − ∑ ρʲ ΔE g_{t+1+j} + ∑_{j≥1} ρʲ ΔE r_{t+1+j}
  − ∑ ρʲ ΔE R_{t+1+j}`; `remainder_sum_le`: the last term is at most `2B/(1 − ρ)` when `|R| ≤ B`.
* `identity320_of_flow`: hence `MaturityBuffer.Identity320` holds exactly with the surplus news
  augmented by the remainder news.

## (3.21)

* The exact return on a geometric portfolio (1.22) is `rⁿ_{t+1} = log(1 + ω e^{q_{t+1}}) − q_t`.
  Linearising at `q̄` gives the coefficient `ω̂ = ωQ̄/(1 + ωQ̄)` (`what`), which at the steady-state
  price `Q̄ = 1/(1 + i − ω)` is `ω/(1 + i)` (`what_steady`), not `ω`.
* `bond_return_identity` (**(3.21) with remainder**): `ΔE rⁿ_{t+1} =
  −∑_{j≥1} ω̂ʲ ΔE(r_{t+1+j} + π_{t+1+j}) + ∑ ω̂ʲ ΔE R^q_{t+1+j}`; `identity321_of_return`.
* `identity84_of_nonlinear`: (8.4) with maturity `ω̂` holds with the error
  `∑ ω̂ʲ ΔE R^q − ∑ ρʲ ΔE R`, bounded by `2B_q/(1 − ω̂) + 2B/(1 − ρ)`.

## (9.22)

* `valuation922_of_flow` (**(9.22) with remainder**): with one-period debt, `rⁿ_{t+1} = i_t`
  known at `t`, the valuation equation `SpreadTarget.Valuation` holds with the fiscal shock
  `ε_{t+1} = ∑ ρʲ ΔE(s̃_{t+1+j} + R_{t+1+j})` (no growth), whose remainder part is at most
  `2B/(1 − ρ)`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR6Linearise

open Real Filter Topology

/-! ### The scalar linearisation with an explicit remainder -/

/-- Cochrane (2023), Online Appendix eq. (1.9), p. 558 (Taylor step for the logarithm): for
`|u| ≤ 1/2`, `|log(1 + u) − u| ≤ 2u²`. -/
theorem log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |log (1 + u) - u| ≤ 2 * u ^ 2 := by
  have hx : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, sub_neg_eq_add, abs_neg] at h
  have e : -u + log (1 + u) = log (1 + u) - u := by ring
  rw [e] at h
  refine h.trans ?_
  have h1 : 1 / 2 ≤ 1 - |u| := by linarith
  rw [div_le_iff₀ (by linarith), sq_abs]
  nlinarith [sq_nonneg u]

/-- Cochrane (2023), Online Appendix eq. (1.9), p. 558 (Taylor step for the exponential): for
`|z| ≤ 1`, `|eᶻ − 1| ≤ 2|z|`. -/
theorem exp_sub_one_le {z : ℝ} (hz : |z| ≤ 1) : |exp z - 1| ≤ 2 * |z| := by
  have h := Real.abs_exp_sub_one_sub_id_le hz
  have h2 : z ^ 2 ≤ |z| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg z]
  calc |exp z - 1| = |(exp z - 1 - z) + z| := by ring_nf
    _ ≤ |exp z - 1 - z| + |z| := abs_add_le _ _
    _ ≤ 2 * |z| := by linarith

/-- Cochrane (2023), Online Appendix eqs. (1.9)–(1.11), p. 558 (**the linearisation with
remainder**): for `c > 0`, `A = c + ȳ > 0`, `|z| ≤ 1` and `u = (c(eᶻ − 1) + (y − ȳ))/A` with
`|u| ≤ 1/2`, `log(c eᶻ + y) = log A + (c/A) z + (y − ȳ)/A + R` with `|R| ≤ 2u² + (c/A) z²`. -/
theorem log_lin {c ybar z y : ℝ} (hc : 0 < c) (hA : 0 < c + ybar) (hz : |z| ≤ 1)
    (hu : |(c * (exp z - 1) + (y - ybar)) / (c + ybar)| ≤ 1 / 2) :
    |log (c * exp z + y) - (log (c + ybar) + c / (c + ybar) * z + (y - ybar) / (c + ybar))| ≤
      2 * ((c * (exp z - 1) + (y - ybar)) / (c + ybar)) ^ 2 + c / (c + ybar) * z ^ 2 := by
  set A := c + ybar with hAdef
  set u := (c * (exp z - 1) + (y - ybar)) / A with hudef
  have hu1 : 0 < 1 + u := by
    have := neg_abs_le u
    linarith
  have he : c * exp z + y = A * (1 + u) := by
    rw [hudef]
    field_simp
    ring
  have hlog : log (c * exp z + y) = log A + log (1 + u) := by
    rw [he, Real.log_mul hA.ne' hu1.ne']
  have hdiff : log (c * exp z + y) - (log A + c / A * z + (y - ybar) / A) =
      (log (1 + u) - u) + c / A * (exp z - 1 - z) := by
    rw [hlog, hudef]
    field_simp
    ring
  rw [hdiff]
  have hρ : 0 < c / A := div_pos hc hA
  calc |(log (1 + u) - u) + c / A * (exp z - 1 - z)|
      ≤ |log (1 + u) - u| + |c / A * (exp z - 1 - z)| := abs_add_le _ _
    _ ≤ 2 * u ^ 2 + c / A * z ^ 2 := by
      refine add_le_add (log_one_add_sub_le hu) ?_
      rw [abs_mul, abs_of_pos hρ]
      exact mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_sub_id_le hz) hρ.le

/-- Cochrane (2023), Online Appendix eqs. (1.9)–(1.11), p. 558 (**the explicit second-order
bound**): with `ρ = c/A`, if `|z| ≤ δ_z ≤ 1`, `|y − ȳ| ≤ δ_y` and `η = 2ρδ_z + δ_y/A ≤ 1/2`, the
remainder of `log_lin` is at most `2η² + ρδ_z²`. -/
theorem log_lin_bound {c ybar z y δz δy : ℝ} (hc : 0 < c) (hA : 0 < c + ybar) (hz : |z| ≤ δz)
    (hδz : δz ≤ 1) (hy : |y - ybar| ≤ δy)
    (hη : 2 * (c / (c + ybar)) * δz + δy / (c + ybar) ≤ 1 / 2) :
    |log (c * exp z + y) - (log (c + ybar) + c / (c + ybar) * z + (y - ybar) / (c + ybar))| ≤
      2 * (2 * (c / (c + ybar)) * δz + δy / (c + ybar)) ^ 2 + c / (c + ybar) * δz ^ 2 := by
  set A := c + ybar with hAdef
  have hρ : 0 < c / A := div_pos hc hA
  have hz1 : |z| ≤ 1 := hz.trans hδz
  have hδz0 : 0 ≤ δz := (abs_nonneg z).trans hz
  have hδy0 : 0 ≤ δy := (abs_nonneg _).trans hy
  have hu : |(c * (exp z - 1) + (y - ybar)) / A| ≤ 2 * (c / A) * δz + δy / A := by
    rw [add_div]
    have h1 : |c * (exp z - 1) / A| ≤ 2 * (c / A) * δz := by
      rw [abs_div, abs_of_pos hA, abs_mul, abs_of_pos hc]
      have := exp_sub_one_le hz1
      rw [div_le_iff₀ hA]
      have : c * |exp z - 1| ≤ c * (2 * δz) :=
        mul_le_mul_of_nonneg_left (this.trans (by linarith)) hc.le
      have e : 2 * (c / A) * δz * A = c * (2 * δz) := by field_simp
      linarith
    have h2 : |(y - ybar) / A| ≤ δy / A := by
      rw [abs_div, abs_of_pos hA]
      exact div_le_div_of_nonneg_right hy hA.le
    calc |c * (exp z - 1) / A + (y - ybar) / A| ≤ |c * (exp z - 1) / A| + |(y - ybar) / A| :=
          abs_add_le _ _
      _ ≤ 2 * (c / A) * δz + δy / A := add_le_add h1 h2
      _ = 2 * (c / A) * δz + δy / A := rfl
  have hu' : |(c * (exp z - 1) + (y - ybar)) / A| ≤ 1 / 2 := hu.trans hη
  refine (log_lin hc hA hz1 hu').trans (add_le_add ?_ ?_)
  · have h0 : 0 ≤ |(c * (exp z - 1) + (y - ybar)) / A| := abs_nonneg _
    have := pow_le_pow_left₀ h0 hu 2
    rw [sq_abs] at this
    linarith
  · refine mul_le_mul_of_nonneg_left ?_ hρ.le
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 2

/-- Cochrane (2023), Online Appendix eq. (1.11), p. 558: the linear coefficients are the
exact partial derivatives at the expansion point: `∂/∂z log(c eᶻ + ȳ)|_{z=0} = c/A` and
`∂/∂y log(c + y)|_{y=ȳ} = 1/A`. -/
theorem log_lin_hasDerivAt {c ybar : ℝ} (hA : 0 < c + ybar) :
    HasDerivAt (fun z => log (c * exp z + ybar)) (c / (c + ybar)) 0 ∧
      HasDerivAt (fun y => log (c + y)) (1 / (c + ybar)) ybar := by
  constructor
  · have h1 : HasDerivAt (fun z => c * exp z + ybar) (c * exp 0) 0 :=
      ((hasDerivAt_exp 0).const_mul c).add_const ybar
    have h2 := h1.log (by simpa using hA.ne')
    simpa using h2
  · have h1 : HasDerivAt (fun y => c + y) 1 ybar := (hasDerivAt_id ybar).const_add c
    have h2 := h1.log (by simpa using hA.ne')
    simpa using h2

/-! ### The flow identity (3.17) -/

/-- Cochrane (2023), Online Appendix eq. (1.11), p. 558: `A = e^{v̄} + s̄y`. -/
noncomputable def A0 (vbar sybar : ℝ) : ℝ := exp vbar + sybar

/-- Cochrane (2023), eq. (1.12), p. 558: the linearisation constant
`ρ = e^{v̄}/(e^{v̄} + s̄y)` (`= e^{−(r − g)}` at a steady state). -/
noncomputable def rho (vbar sybar : ℝ) : ℝ := exp vbar / A0 vbar sybar

/-- Cochrane (2023), eq. (1.11), p. 558: the constant of the linearised flow,
`κ = log A − ρ v̄ − s̄y/A`. -/
noncomputable def kap (vbar sybar : ℝ) : ℝ :=
  log (A0 vbar sybar) - rho vbar sybar * vbar - sybar / A0 vbar sybar

/-- Cochrane (2023), eq. (1.13), p. 558: the scaled surplus `s̃ = sy/A = ρ sy/e^{v̄}`. -/
noncomputable def stil {Ω : Type*} (vbar sybar : ℝ) (sy : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  sy t ω / A0 vbar sybar

/-- Cochrane (2023), eqs. (1.9)–(1.13), p. 558: the remainder of the linearised flow,
`R_t = log(sy_t + e^{v_t}) − κ − ρ v_t − s̃_t`. -/
noncomputable def remF {Ω : Type*} (vbar sybar : ℝ) (v sy : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  log (sy t ω + exp (v t ω)) - kap vbar sybar - rho vbar sybar * v t ω - stil vbar sybar sy t ω

/-- Cochrane (2023), eq. (1.12), p. 558: for a positive steady-state surplus `s̄y > 0`,
`0 < ρ < 1` and `A > 0`. -/
theorem rho_mem {vbar sybar : ℝ} (hs : 0 < sybar) :
    0 < A0 vbar sybar ∧ 0 < rho vbar sybar ∧ rho vbar sybar < 1 := by
  have he := exp_pos vbar
  have hA : 0 < A0 vbar sybar := by unfold A0; linarith
  refine ⟨hA, div_pos he hA, ?_⟩
  rw [rho, div_lt_one hA]
  unfold A0
  linarith

/-- Cochrane (2023), eq. (3.17), p. 63, and Online Appendix eq. (1.11), p. 558 (**the linearised
flow, exactly**): if the exact flow (1.9) `v_t + r_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`
holds, then `v_t + r_{t+1} − g_{t+1} = κ + ρ v_{t+1} + s̃_{t+1} + R_{t+1}` with `R = remF`. -/
theorem flow_exact {Ω : Type*} {vbar sybar : ℝ} {v r g sy : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : v t ω + r (t + 1) ω - g (t + 1) ω = log (sy (t + 1) ω + exp (v (t + 1) ω))) :
    v t ω + r (t + 1) ω - g (t + 1) ω = kap vbar sybar + rho vbar sybar * v (t + 1) ω +
      stil vbar sybar sy (t + 1) ω + remF vbar sybar v sy (t + 1) ω := by
  rw [h]
  unfold remF
  ring

/-- Cochrane (2023), Online Appendix eqs. (1.9)–(1.13), p. 558 (**the remainder bound**): if
`|v_t − v̄| ≤ δ_v ≤ 1`, `|sy_t − s̄y| ≤ δ_s` and `η = 2ρδ_v + δ_s/A ≤ 1/2`, then
`|R_t| ≤ 2η² + ρδ_v²`. -/
theorem remF_bound {Ω : Type*} {vbar sybar δv δs : ℝ} (hs : 0 < sybar) {v sy : ℕ → Ω → ℝ}
    {t : ℕ} {ω : Ω} (hv : |v t ω - vbar| ≤ δv) (hδv : δv ≤ 1) (hsy : |sy t ω - sybar| ≤ δs)
    (hη : 2 * rho vbar sybar * δv + δs / A0 vbar sybar ≤ 1 / 2) :
    |remF vbar sybar v sy t ω| ≤
      2 * (2 * rho vbar sybar * δv + δs / A0 vbar sybar) ^ 2 + rho vbar sybar * δv ^ 2 := by
  have hA : 0 < exp vbar + sybar := (rho_mem (vbar := vbar) hs).1
  have h := log_lin_bound (c := exp vbar) (ybar := sybar) (z := v t ω - vbar) (y := sy t ω)
    (exp_pos vbar) hA hv hδv hsy hη
  have e1 : exp vbar * exp (v t ω - vbar) + sy t ω = sy t ω + exp (v t ω) := by
    rw [← exp_add]
    ring_nf
  rw [e1] at h
  have e2 : remF vbar sybar v sy t ω = log (sy t ω + exp (v t ω)) -
      (log (exp vbar + sybar) + exp vbar / (exp vbar + sybar) * (v t ω - vbar) +
        (sy t ω - sybar) / (exp vbar + sybar)) := by
    unfold remF kap stil rho A0
    field_simp
    ring
  rw [e2]
  exact h

/-! ### Innovations -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (3.20), p. 65: the innovation `ΔE_{t+1}` is additive. -/
theorem innov_add (t : ℕ) (x y : Ω → ℝ) :
    SpreadTarget.innov 𝔼 t (x + y) = SpreadTarget.innov 𝔼 t x + SpreadTarget.innov 𝔼 t y := by
  unfold SpreadTarget.innov
  rw [map_add, map_add]
  abel

/-- Cochrane (2023), eq. (3.20), p. 65: the innovation `ΔE_{t+1}` commutes with differences. -/
theorem innov_sub (t : ℕ) (x y : Ω → ℝ) :
    SpreadTarget.innov 𝔼 t (x - y) = SpreadTarget.innov 𝔼 t x - SpreadTarget.innov 𝔼 t y := by
  unfold SpreadTarget.innov
  rw [map_sub, map_sub]
  abel

/-- Cochrane (2023), eq. (3.20), p. 65: the innovation `ΔE_{t+1}` is homogeneous. -/
theorem innov_smul (t : ℕ) (c : ℝ) (x : Ω → ℝ) :
    SpreadTarget.innov 𝔼 t (c • x) = c • SpreadTarget.innov 𝔼 t x := by
  unfold SpreadTarget.innov
  rw [map_smul, map_smul, smul_sub]

/-- Cochrane (2023), eq. (3.20), p. 65: constants carry no news. -/
theorem innov_const (t : ℕ) (c : ℝ) : SpreadTarget.innov 𝔼 t (fun _ => c) = 0 := by
  unfold SpreadTarget.innov
  rw [𝔼.const, 𝔼.const, sub_self]

/-- Cochrane (2023), p. 65 ("since `v_t` is known at time `t`, it usefully disappears from this
innovation accounting"): a variable known at `t` has no date-`t + 1` news. -/
theorem innov_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : SpreadTarget.innov 𝔼 t x = 0 := by
  unfold SpreadTarget.innov
  have h : 𝔼.E (t + 1) x = x := by
    calc 𝔼.E (t + 1) x = 𝔼.E (t + 1) (𝔼.E t x) := by rw [hx]
      _ = 𝔼.E t x := 𝔼.known (Nat.le_succ t) x
      _ = x := hx
  rw [h, hx, sub_self]

/-- Cochrane (2023), eq. (3.20), p. 65: the news in a variable bounded by `K` is at most `2K`. -/
theorem innov_bound {K : ℝ} {x : Ω → ℝ} (hx : ∀ ω, |x ω| ≤ K) (t : ℕ) (ω : Ω) :
    |SpreadTarget.innov 𝔼 t x ω| ≤ 2 * K := by
  unfold SpreadTarget.innov
  simp only [Pi.sub_apply]
  have h1 := 𝔼.abs_E_le hx (t + 1) ω
  have h2 := 𝔼.abs_E_le hx t ω
  calc |𝔼.E (t + 1) x ω - 𝔼.E t x ω| ≤ |𝔼.E (t + 1) x ω| + |𝔼.E t x ω| := abs_sub _ _
    _ ≤ 2 * K := by linarith

/-! ### Forward iteration of news -/

/-- Cochrane (2023), eqs. (3.18)–(3.19), p. 63 (iterating forward): if `a` is bounded,
`0 ≤ ρ < 1` and `a_j = ρ a_{j+1} + w_{j+1}` with `w` bounded, then `∑ ρʲ w_{j+1} = a_0`. -/
theorem forward_sum {ρ K Kw : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {a w : ℕ → ℝ}
    (ha : ∀ j, |a j| ≤ K) (hw : ∀ j, |w j| ≤ Kw) (hrec : ∀ j, a j = ρ * a (j + 1) + w (j + 1)) :
    HasSum (fun j => ρ ^ j * w (j + 1)) (a 0) := by
  have hpart : ∀ n, a 0 = ∑ j ∈ Finset.range n, ρ ^ j * w (j + 1) + ρ ^ n * a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hrec n]
      ring
  have hsum : Summable (fun j => ρ ^ j * w (j + 1)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Kw) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
      exact mul_le_mul_of_nonneg_left (hw _) (pow_nonneg hρ0 j)
  have hlim : Tendsto (fun n => ρ ^ n * a n) atTop (𝓝 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
    rw [zero_mul] at hg
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (ha n) (pow_nonneg hρ0 n)
  rw [hsum.hasSum_iff_tendsto_nat]
  have h2 : Tendsto (fun n => a 0 - ρ ^ n * a n) atTop (𝓝 (a 0 - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero] at h2
  exact h2.congr fun n => by rw [hpart n]; ring

/-- Cochrane (2023), eq. (3.20), p. 65 (supporting lemma): for `0 ≤ ρ < 1` a bounded sequence
`|x_j| ≤ K` has a summable discounted sum, `|∑ ρʲ x_j| ≤ K/(1 − ρ)`. -/
theorem discounted_le {ρ K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {x : ℕ → ℝ} (hx : ∀ j, |x j| ≤ K) :
    Summable (fun j => ρ ^ j * x j) ∧ |∑' j, ρ ^ j * x j| ≤ K / (1 - ρ) := by
  have hg := hasSum_geometric_of_lt_one hρ0 hρ1
  have hb : ∀ j, |ρ ^ j * x j| ≤ ρ ^ j * K := fun j => by
    rw [abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (hx j) (pow_nonneg hρ0 j)
  have hs : Summable (fun j => ρ ^ j * x j) :=
    Summable.of_norm_bounded (hg.summable.mul_right K) fun j => by
      rw [Real.norm_eq_abs]; exact hb j
  refine ⟨hs, ?_⟩
  have hK : HasSum (fun j => ρ ^ j * K) (K / (1 - ρ)) := by
    have := hg.mul_right K
    rwa [← div_eq_inv_mul] at this
  rw [abs_le]
  constructor
  · have := hasSum_le (fun j => (neg_le_of_abs_le (hb j))) hK.neg hs.hasSum
    linarith
  · exact hasSum_le (fun j => (le_abs_self _).trans (hb j)) hs.hasSum hK

/-! ### (3.20) with remainder -/

/-- Cochrane (2023), Online Appendix eq. (1.11), p. 558: the flow remainder is bounded when the
model's processes are: from (1.9),
`|R_{t+1}| ≤ K_v + K_r + K_g + |κ| + ρ K_v + K_s/A`. -/
theorem remF_succ_le {vbar sybar Kv Kr Kg Ks : ℝ} (hs : 0 < sybar) {v r g sy : ℕ → Ω → ℝ}
    (hflow : ∀ t ω, v t ω + r (t + 1) ω - g (t + 1) ω = log (sy (t + 1) ω + exp (v (t + 1) ω)))
    (hvK : ∀ t ω, |v t ω| ≤ Kv) (hrK : ∀ t ω, |r t ω| ≤ Kr) (hgK : ∀ t ω, |g t ω| ≤ Kg)
    (hsK : ∀ t ω, |sy t ω| ≤ Ks) (t : ℕ) (ω : Ω) :
    |remF vbar sybar v sy (t + 1) ω| ≤
      Kv + Kr + Kg + |kap vbar sybar| + rho vbar sybar * Kv + Ks / A0 vbar sybar := by
  obtain ⟨hA, hρ0, -⟩ := rho_mem (vbar := vbar) hs
  have e : remF vbar sybar v sy (t + 1) ω = v t ω + r (t + 1) ω - g (t + 1) ω -
      kap vbar sybar - rho vbar sybar * v (t + 1) ω - sy (t + 1) ω / A0 vbar sybar := by
    unfold remF stil
    rw [hflow t ω]
  rw [e]
  have h1 := hvK t ω
  have h2 := hrK (t + 1) ω
  have h3 := hgK (t + 1) ω
  have h4 : |rho vbar sybar * v (t + 1) ω| ≤ rho vbar sybar * Kv := by
    rw [abs_mul, abs_of_pos hρ0]
    exact mul_le_mul_of_nonneg_left (hvK _ _) hρ0.le
  have h5 : |sy (t + 1) ω / A0 vbar sybar| ≤ Ks / A0 vbar sybar := by
    rw [abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right (hsK _ _) hA.le
  have := abs_sub (v t ω + r (t + 1) ω - g (t + 1) ω - kap vbar sybar -
    rho vbar sybar * v (t + 1) ω) (sy (t + 1) ω / A0 vbar sybar)
  have := abs_sub (v t ω + r (t + 1) ω - g (t + 1) ω - kap vbar sybar)
    (rho vbar sybar * v (t + 1) ω)
  have := abs_sub (v t ω + r (t + 1) ω - g (t + 1) ω) (kap vbar sybar)
  have := abs_sub (v t ω + r (t + 1) ω) (g (t + 1) ω)
  have := abs_add_le (v t ω) (r (t + 1) ω)
  linarith

/-- Cochrane (2023), eq. (3.20), p. 65 (**the unexpected-inflation identity derived from the
nonlinear flow, with remainder**): let `v` (log debt to GDP), `r` (log real return), `g` (log
growth), `sy` (surplus to GDP) be bounded, `v` adapted, `r = rⁿ − π`, and let the exact flow (1.9)
hold. Linearise at `(v̄, s̄y)`, `s̄y > 0`. Then at every date and state
`ΔE π_{t+1} − ΔE rⁿ_{t+1} = −∑ ρʲ ΔE s̃_{t+1+j} − ∑ ρʲ ΔE g_{t+1+j} + ∑_{j≥0} ρ^{j+1} ΔE r_{t+2+j}
− ∑ ρʲ ΔE R_{t+1+j}`, all sums converging, with `R = remF` the linearisation remainder. -/
theorem unexpected_inflation_identity {vbar sybar Kv Kr Kg Ks : ℝ} (hs : 0 < sybar)
    {v r g sy infl rn : ℕ → Ω → ℝ}
    (hflow : ∀ t ω, v t ω + r (t + 1) ω - g (t + 1) ω = log (sy (t + 1) ω + exp (v (t + 1) ω)))
    (hva : ∀ t, 𝔼.E t (v t) = v t) (hr : ∀ t, r t = rn t - infl t)
    (hvK : ∀ t ω, |v t ω| ≤ Kv) (hrK : ∀ t ω, |r t ω| ≤ Kr) (hgK : ∀ t ω, |g t ω| ≤ Kg)
    (hsK : ∀ t ω, |sy t ω| ≤ Ks) (t : ℕ) (ω : Ω) :
    SpreadTarget.innov 𝔼 t (infl (t + 1)) ω - SpreadTarget.innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, rho vbar sybar ^ j * SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω) -
        (∑' j, rho vbar sybar ^ j * SpreadTarget.innov 𝔼 t (g (t + 1 + j)) ω) +
        (∑' j, rho vbar sybar ^ (j + 1) * SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω) -
        ∑' j, rho vbar sybar ^ j *
          SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω := by
  obtain ⟨hA, hρ0, hρ1⟩ := rho_mem (vbar := vbar) hs
  set ρ := rho vbar sybar with hρdef
  set KR := Kv + Kr + Kg + |kap vbar sybar| + ρ * Kv + Ks / A0 vbar sybar with hKR
  have hRK := remF_succ_le (vbar := vbar) hs hflow hvK hrK hgK hsK
  have hsK' : ∀ s ω', |stil vbar sybar sy s ω'| ≤ Ks / A0 vbar sybar := fun s ω' => by
    unfold stil
    rw [abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right (hsK _ _) hA.le
  -- the linearised flow as an identity of random variables
  have hfun : ∀ s, v s = (fun _ => kap vbar sybar) + ρ • v (s + 1) + stil vbar sybar sy (s + 1) +
      g (s + 1) - r (s + 1) + remF vbar sybar v sy (s + 1) := fun s => by
    funext ω'
    have h := flow_exact (vbar := vbar) (sybar := sybar) (hflow s ω')
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hinnov : ∀ s, SpreadTarget.innov 𝔼 t (v s) ω =
      ρ * SpreadTarget.innov 𝔼 t (v (s + 1)) ω +
        (SpreadTarget.innov 𝔼 t (stil vbar sybar sy (s + 1)) ω +
          SpreadTarget.innov 𝔼 t (g (s + 1)) ω - SpreadTarget.innov 𝔼 t (r (s + 1)) ω +
          SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (s + 1)) ω) := fun s => by
    rw [hfun s, innov_add, innov_sub, innov_add, innov_add, innov_add, innov_const, innov_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  set a : ℕ → ℝ := fun j => SpreadTarget.innov 𝔼 t (v (t + 1 + j)) ω with ha
  set Ns : ℕ → ℝ := fun j => SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω with hNs
  set Ng : ℕ → ℝ := fun j => SpreadTarget.innov 𝔼 t (g (t + 1 + j)) ω with hNg
  set Nr : ℕ → ℝ := fun j => SpreadTarget.innov 𝔼 t (r (t + 1 + j)) ω with hNr
  set NR : ℕ → ℝ := fun j =>
    SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω with hNR
  set w : ℕ → ℝ := fun j => Ns j + Ng j - Nr j + NR j with hw
  have hbs : ∀ j, |Ns j| ≤ 2 * (Ks / A0 vbar sybar) := fun j => innov_bound 𝔼 (hsK' _) t ω
  have hbg : ∀ j, |Ng j| ≤ 2 * Kg := fun j => innov_bound 𝔼 (hgK _) t ω
  have hbr : ∀ j, |Nr j| ≤ 2 * Kr := fun j => innov_bound 𝔼 (hrK _) t ω
  have hbR : ∀ j, |NR j| ≤ 2 * KR := fun j => innov_bound 𝔼 (fun ω' => by
    have := hRK (t + j) ω'
    rwa [show t + j + 1 = t + 1 + j by omega] at this) t ω
  have hba : ∀ j, |a j| ≤ 2 * Kv := fun j => innov_bound 𝔼 (hvK _) t ω
  have hbw : ∀ j, |w j| ≤ 2 * (Ks / A0 vbar sybar) + 2 * Kg + 2 * Kr + 2 * KR := fun j => by
    have := abs_add_le (Ns j + Ng j - Nr j) (NR j)
    have := abs_sub (Ns j + Ng j) (Nr j)
    have := abs_add_le (Ns j) (Ng j)
    simp only [hw]
    linarith [hbs j, hbg j, hbr j, hbR j]
  have h0 : 0 = ρ * a 0 + w 0 := by
    have := hinnov t
    rw [innov_known 𝔼 (hva t)] at this
    simpa [ha, hw, hNs, hNg, hNr, hNR] using this
  have hrec : ∀ j, a j = ρ * a (j + 1) + w (j + 1) := fun j => hinnov (t + 1 + j)
  have hfw := forward_sum hρ0.le hρ1 hba hbw hrec
  -- `∑ ρʲ w_j = 0`
  have hW : HasSum (fun j => ρ ^ j * w j) 0 := by
    rw [← hasSum_nat_add_iff' 1]
    have := hfw.mul_left ρ
    simp only [Finset.sum_range_one, pow_zero, one_mul]
    rw [show (0 : ℝ) - w 0 = ρ * a 0 by linarith]
    exact this.congr_fun fun j => by ring
  obtain ⟨hsS, -⟩ := discounted_le hρ0.le hρ1 hbs
  obtain ⟨hsG, -⟩ := discounted_le hρ0.le hρ1 hbg
  obtain ⟨hsr, -⟩ := discounted_le hρ0.le hρ1 hbr
  obtain ⟨hsR, -⟩ := discounted_le hρ0.le hρ1 hbR
  have hW2 : HasSum (fun j => ρ ^ j * w j) ((∑' j, ρ ^ j * Ns j) + (∑' j, ρ ^ j * Ng j) -
      (∑' j, ρ ^ j * Nr j) + ∑' j, ρ ^ j * NR j) :=
    (((hsS.hasSum.add hsG.hasSum).sub hsr.hasSum).add hsR.hasSum).congr_fun fun j => by
      simp only [hw]; ring
  have hzero := hW.unique hW2
  have hr0 : Nr 0 = SpreadTarget.innov 𝔼 t (rn (t + 1)) ω -
      SpreadTarget.innov 𝔼 t (infl (t + 1)) ω := by
    simp only [hNr, add_zero, hr (t + 1), innov_sub, Pi.sub_apply]
  have hrsplit : ∑' j, ρ ^ j * Nr j = Nr 0 + ∑' j, ρ ^ (j + 1) * Nr (j + 1) := by
    rw [hsr.tsum_eq_zero_add]
    simp
  rw [hrsplit, hr0] at hzero
  have e1 : (∑' j, ρ ^ (j + 1) * Nr (j + 1)) =
      ∑' j, ρ ^ (j + 1) * SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω := rfl
  linarith

/-- Cochrane (2023), eq. (3.20), p. 65 (**the size of the error**): if the flow remainder is bounded
by `B` at every date from `t + 1` on, its discounted news is at most `2B/(1 − ρ)`. -/
theorem remainder_sum_le {vbar sybar B : ℝ} (hs : 0 < sybar) {v sy : ℕ → Ω → ℝ} (t : ℕ)
    (hB : ∀ s ω, |remF vbar sybar v sy (t + 1 + s) ω| ≤ B) (ω : Ω) :
    |∑' j, rho vbar sybar ^ j * SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω| ≤
      2 * B / (1 - rho vbar sybar) := by
  obtain ⟨-, hρ0, hρ1⟩ := rho_mem (vbar := vbar) hs
  exact (discounted_le hρ0.le hρ1 fun j => innov_bound 𝔼 (hB j) t ω).2

/-- Cochrane (2023), eq. (3.20), p. 65, as used for (8.4), p. 250 (**`MaturityBuffer.Identity320`
derived**): with no growth (`g = 0`), the news `πN j = ΔE π_{t+1+j}`, `rN j = ΔE r_{t+1+j}`,
`rn = ΔE rⁿ_{t+1}` and the surplus news augmented by the remainder news,
`sN j = ΔE s̃_{t+1+j} + ΔE R_{t+1+j}`, satisfy `MaturityBuffer.Identity320` exactly. -/
theorem identity320_of_flow {vbar sybar Kv Kr Ks : ℝ} (hs : 0 < sybar)
    {v r sy infl rn : ℕ → Ω → ℝ}
    (hflow : ∀ t ω, v t ω + r (t + 1) ω - 0 = log (sy (t + 1) ω + exp (v (t + 1) ω)))
    (hva : ∀ t, 𝔼.E t (v t) = v t) (hr : ∀ t, r t = rn t - infl t)
    (hvK : ∀ t ω, |v t ω| ≤ Kv) (hrK : ∀ t ω, |r t ω| ≤ Kr) (hsK : ∀ t ω, |sy t ω| ≤ Ks)
    (t : ℕ) (ω : Ω) :
    MaturityBuffer.Identity320 (rho vbar sybar)
      (fun j => SpreadTarget.innov 𝔼 t (infl (t + 1 + j)) ω)
      (fun j => SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω +
        SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω)
      (fun j => SpreadTarget.innov 𝔼 t (r (t + 1 + j)) ω)
      (SpreadTarget.innov 𝔼 t (rn (t + 1)) ω) := by
  obtain ⟨hA, hρ0, hρ1⟩ := rho_mem (vbar := vbar) hs
  have h := unexpected_inflation_identity 𝔼 (vbar := vbar) (g := fun _ _ => 0) (Kg := 0) hs hflow
    hva hr hvK hrK
    (fun _ _ => by simp) hsK t ω
  have hg0 : (∑' j, rho vbar sybar ^ j *
      SpreadTarget.innov 𝔼 t ((fun _ _ => (0 : ℝ)) (t + 1 + j)) ω) = 0 := by
    simp [innov_const]
  rw [hg0] at h
  have hRK := remF_succ_le (vbar := vbar) (g := fun _ _ => 0) (Kg := 0) hs hflow hvK hrK
    (fun _ _ => by simp) hsK
  have hsK' : ∀ s ω', |stil vbar sybar sy s ω'| ≤ Ks / A0 vbar sybar := fun s ω' => by
    unfold stil
    rw [abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right (hsK _ _) hA.le
  obtain ⟨h1, -⟩ := discounted_le hρ0.le hρ1 fun j => innov_bound 𝔼 (hsK' (t + 1 + j)) t ω
  obtain ⟨h2, -⟩ := discounted_le hρ0.le hρ1 fun j =>
    innov_bound 𝔼 (x := remF vbar sybar v sy (t + 1 + j)) (fun ω' => by
      have := hRK (t + j) ω'
      rwa [show t + j + 1 = t + 1 + j by omega] at this) t ω
  unfold MaturityBuffer.Identity320
  have e : ∑' j, rho vbar sybar ^ j *
      (SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω +
        SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω) =
      (∑' j, rho vbar sybar ^ j * SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω) +
      ∑' j, rho vbar sybar ^ j *
        SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω := by
    rw [← h1.tsum_add h2]
    exact tsum_congr fun j => by ring
  simp only [add_zero]
  rw [e]
  linarith

/-! ### (3.21) with remainder -/

/-- Cochrane (2023), Online Appendix eq. (1.22), p. 563: the exact linear coefficient of the
return on a geometric portfolio, `ω̂ = ωQ̄/(1 + ωQ̄)` with `Q̄ = e^{q̄}`. -/
noncomputable def what (om qbar : ℝ) : ℝ := om * exp qbar / (om * exp qbar + 1)

/-- Cochrane (2023), Online Appendix eq. (1.22), p. 563: the remainder of the linearised return,
`R^q_t = log(1 + ω e^{q_t}) − log(1 + ωQ̄) − ω̂ (q_t − q̄)`. -/
noncomputable def remQ {Ω : Type*} (om qbar : ℝ) (q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  log (1 + om * exp (q t ω)) - log (1 + om * exp qbar) - what om qbar * (q t ω - qbar)

/-- Cochrane (2023), Online Appendix eq. (1.22), p. 563: for `ω > 0`, `0 < ω̂ < 1`. -/
theorem what_mem {om qbar : ℝ} (hom : 0 < om) : 0 < what om qbar ∧ what om qbar < 1 := by
  have h : 0 < om * exp qbar := mul_pos hom (exp_pos qbar)
  unfold what
  exact ⟨div_pos h (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- Cochrane (2023), Online Appendix eqs. (1.23)–(1.24), p. 563 (**the coefficient is
`ω/(1 + i)`**): at the steady-state portfolio price `Q̄ = 1/(1 + i − ω)` (`1 + i − ω > 0`,
`1 + i > 0`), `ω̂ = ω/(1 + i)`; the book's (1.24) and (3.21) further replace it by `ω`. -/
theorem what_steady {om i qbar : ℝ} (h : 0 < 1 + i - om) (hi : 0 < 1 + i)
    (hq : exp qbar = 1 / (1 + i - om)) : what om qbar = om / (1 + i) := by
  have h2 : (1 + i - om) ≠ 0 := h.ne'
  unfold what
  rw [hq]
  have e : om * (1 / (1 + i - om)) + 1 = (1 + i) / (1 + i - om) := by
    have h1 : (1 + i) ≠ 0 := hi.ne'
    field_simp
    ring
  rw [e, mul_one_div, div_div_div_cancel_right₀ h2]

/-- Cochrane (2023), Online Appendix eq. (1.22), p. 563 (**the return remainder bound**): if
`ω > 0`, `|q_t − q̄| ≤ δ ≤ 1` and `2ω̂δ ≤ 1/2`, then `|R^q_t| ≤ 2(2ω̂δ)² + ω̂δ²`. -/
theorem remQ_bound {om qbar δ : ℝ} (hom : 0 < om) {q : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hq : |q t ω - qbar| ≤ δ) (hδ : δ ≤ 1) (hη : 2 * what om qbar * δ ≤ 1 / 2) :
    |remQ om qbar q t ω| ≤ 2 * (2 * what om qbar * δ) ^ 2 + what om qbar * δ ^ 2 := by
  have hc : 0 < om * exp qbar := mul_pos hom (exp_pos qbar)
  have hA : 0 < om * exp qbar + 1 := by linarith
  have h := log_lin_bound (c := om * exp qbar) (ybar := 1) (z := q t ω - qbar) (y := 1)
    (δy := 0) hc hA hq hδ (by simp) (by simpa [what] using hη)
  have e1 : om * exp qbar * exp (q t ω - qbar) + 1 = 1 + om * exp (q t ω) := by
    rw [mul_assoc, ← exp_add]
    ring_nf
  rw [e1] at h
  simp only [sub_self, zero_div, add_zero] at h
  have e2 : remQ om qbar q t ω = log (1 + om * exp (q t ω)) -
      (log (om * exp qbar + 1) + om * exp qbar / (om * exp qbar + 1) * (q t ω - qbar)) := by
    unfold remQ what
    rw [add_comm (om * exp qbar) 1]
    ring
  rw [e2]
  simpa [what] using h

/-- Cochrane (2023), eq. (3.21), p. 65, and Online Appendix eqs. (1.22)–(1.25), pp. 563–564
(**the bond-return identity derived from the exact return, with remainder**): let `q` (the log
price of the geometric portfolio) be adapted and bounded, `rⁿ` bounded, and the exact return
(1.22) `rⁿ_{t+1} = log(1 + ω e^{q_{t+1}}) − q_t` hold with `ω > 0`. Then
`ΔE rⁿ_{t+1} = −∑_{j≥0} ω̂^{j+1} ΔE rⁿ_{t+2+j} + ∑ ω̂ʲ ΔE R^q_{t+1+j}`. -/
theorem bond_return_identity {om qbar Kq Kn : ℝ} (hom : 0 < om) {q rn : ℕ → Ω → ℝ}
    (hret : ∀ t ω, rn (t + 1) ω = log (1 + om * exp (q (t + 1) ω)) - q t ω)
    (hqa : ∀ t, 𝔼.E t (q t) = q t) (hqK : ∀ t ω, |q t ω| ≤ Kq) (hnK : ∀ t ω, |rn t ω| ≤ Kn)
    (t : ℕ) (ω : Ω) :
    SpreadTarget.innov 𝔼 t (rn (t + 1)) ω =
      -(∑' j, what om qbar ^ (j + 1) * SpreadTarget.innov 𝔼 t (rn (t + 1 + (j + 1))) ω) +
        ∑' j, what om qbar ^ j * SpreadTarget.innov 𝔼 t (remQ om qbar q (t + 1 + j)) ω := by
  obtain ⟨hw0, hw1⟩ := what_mem (qbar := qbar) hom
  set ŵ := what om qbar with hŵ
  set c0 := log (1 + om * exp qbar) - ŵ * qbar with hc0
  have hfun : ∀ s, rn (s + 1) = (fun _ => c0) + ŵ • q (s + 1) - q s + remQ om qbar q (s + 1) :=
    fun s => by
      funext ω'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, remQ, hc0, hret s ω']
      ring
  have hinnov : ∀ s, SpreadTarget.innov 𝔼 t (rn (s + 1)) ω =
      ŵ * SpreadTarget.innov 𝔼 t (q (s + 1)) ω - SpreadTarget.innov 𝔼 t (q s) ω +
        SpreadTarget.innov 𝔼 t (remQ om qbar q (s + 1)) ω := fun s => by
    rw [hfun s, innov_add, innov_sub, innov_add, innov_const, innov_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  -- the remainder is bounded
  set KQ := Kn + Kq + |log (1 + om * exp qbar)| + ŵ * (Kq + |qbar|) with hKQ
  have hRQ : ∀ s ω', |remQ om qbar q (s + 1) ω'| ≤ KQ := fun s ω' => by
    have e : remQ om qbar q (s + 1) ω' = rn (s + 1) ω' + q s ω' - log (1 + om * exp qbar) -
        ŵ * (q (s + 1) ω' - qbar) := by
      unfold remQ
      rw [hret s ω']
      ring
    rw [e]
    have h1 : |ŵ * (q (s + 1) ω' - qbar)| ≤ ŵ * (Kq + |qbar|) := by
      rw [abs_mul, abs_of_pos hw0]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hw0.le
      linarith [hqK (s + 1) ω']
    have := abs_sub (rn (s + 1) ω' + q s ω' - log (1 + om * exp qbar))
      (ŵ * (q (s + 1) ω' - qbar))
    have := abs_sub (rn (s + 1) ω' + q s ω') (log (1 + om * exp qbar))
    have := abs_add_le (rn (s + 1) ω') (q s ω')
    linarith [hnK (s + 1) ω', hqK s ω']
  set b : ℕ → ℝ := fun j => SpreadTarget.innov 𝔼 t (q (t + 1 + j)) ω with hb
  set m : ℕ → ℝ := fun j => SpreadTarget.innov 𝔼 t (rn (t + 1 + j)) ω with hm
  set Rq : ℕ → ℝ := fun j => SpreadTarget.innov 𝔼 t (remQ om qbar q (t + 1 + j)) ω with hRq
  have hbb : ∀ j, |b j| ≤ 2 * Kq := fun j => innov_bound 𝔼 (hqK _) t ω
  have hbm : ∀ j, |m j| ≤ 2 * Kn := fun j => innov_bound 𝔼 (hnK _) t ω
  have hbR : ∀ j, |Rq j| ≤ 2 * KQ := fun j => innov_bound 𝔼 (fun ω' => by
    have := hRQ (t + j) ω'
    rwa [show t + j + 1 = t + 1 + j by omega] at this) t ω
  have hm0 : m 0 = ŵ * b 0 + Rq 0 := by
    have := hinnov t
    simp only [innov_known 𝔼 (hqa t), Pi.zero_apply, sub_zero] at this
    exact this
  have hrec : ∀ j, b j = ŵ * b (j + 1) + (Rq (j + 1) - m (j + 1)) := fun j => by
    have := hinnov (t + 1 + j)
    change m (j + 1) = ŵ * b (j + 1) - b j + Rq (j + 1) at this
    linarith
  have hbw : ∀ j, |Rq j - m j| ≤ 2 * KQ + 2 * Kn := fun j => by
    have := abs_sub (Rq j) (m j)
    linarith [hbR j, hbm j]
  have hfw := forward_sum hw0.le hw1 hbb hbw hrec
  obtain ⟨hsR, -⟩ := discounted_le hw0.le hw1 hbR
  obtain ⟨hsm, -⟩ := discounted_le hw0.le hw1 hbm
  have hsR1 : Summable (fun j => ŵ ^ j * Rq (j + 1)) := by
    have := (summable_nat_add_iff 1).2 hsR
    exact (this.div_const ŵ).congr fun j => by rw [pow_succ]; field_simp
  have hsm1 : Summable (fun j => ŵ ^ j * m (j + 1)) := by
    have := (summable_nat_add_iff 1).2 hsm
    exact (this.div_const ŵ).congr fun j => by rw [pow_succ]; field_simp
  have hb0 : b 0 = (∑' j, ŵ ^ j * Rq (j + 1)) - ∑' j, ŵ ^ j * m (j + 1) := by
    rw [← hsR1.tsum_sub hsm1, ← hfw.tsum_eq]
    exact tsum_congr fun j => by ring
  have eR : ∑' j, ŵ ^ j * Rq j = Rq 0 + ŵ * ∑' j, ŵ ^ j * Rq (j + 1) := by
    rw [hsR.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul]
    congr 1
    exact tsum_congr fun j => by ring
  have em : ∑' j, ŵ ^ (j + 1) * m (j + 1) = ŵ * ∑' j, ŵ ^ j * m (j + 1) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have e1 : (∑' j, ŵ ^ (j + 1) * SpreadTarget.innov 𝔼 t (rn (t + 1 + (j + 1))) ω) =
      ∑' j, ŵ ^ (j + 1) * m (j + 1) := rfl
  have e2 : (∑' j, ŵ ^ j * SpreadTarget.innov 𝔼 t (remQ om qbar q (t + 1 + j)) ω) =
      ∑' j, ŵ ^ j * Rq j := rfl
  have e3 : SpreadTarget.innov 𝔼 t (rn (t + 1)) ω = m 0 := rfl
  rw [e1, e2, e3, eR, em, hm0, hb0]
  ring

/-- Cochrane (2023), eq. (3.21), p. 65, as used for (8.4), p. 250 (**`MaturityBuffer.Identity321`
derived**): under the hypotheses of `bond_return_identity` and `rⁿ = r + π`, the news satisfy
`MaturityBuffer.Identity321` with maturity `ω̂ = ωQ̄/(1 + ωQ̄)` and the bond-return news net of the
remainder news, `ΔE rⁿ_{t+1} − ∑ ω̂ʲ ΔE R^q_{t+1+j}`. -/
theorem identity321_of_return {om qbar Kq Kn : ℝ} (hom : 0 < om) {q rn r infl : ℕ → Ω → ℝ}
    (hret : ∀ t ω, rn (t + 1) ω = log (1 + om * exp (q (t + 1) ω)) - q t ω)
    (hqa : ∀ t, 𝔼.E t (q t) = q t) (hqK : ∀ t ω, |q t ω| ≤ Kq) (hnK : ∀ t ω, |rn t ω| ≤ Kn)
    (hrn : ∀ t, rn t = r t + infl t) (t : ℕ) (ω : Ω) :
    MaturityBuffer.Identity321 (what om qbar)
      (fun j => SpreadTarget.innov 𝔼 t (infl (t + 1 + j)) ω)
      (fun j => SpreadTarget.innov 𝔼 t (r (t + 1 + j)) ω)
      (SpreadTarget.innov 𝔼 t (rn (t + 1)) ω -
        ∑' j, what om qbar ^ j * SpreadTarget.innov 𝔼 t (remQ om qbar q (t + 1 + j)) ω) := by
  have h := bond_return_identity 𝔼 (qbar := qbar) hom hret hqa hqK hnK t ω
  unfold MaturityBuffer.Identity321
  have e : ∀ j, SpreadTarget.innov 𝔼 t (rn (t + 1 + (j + 1))) ω =
      SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω +
        SpreadTarget.innov 𝔼 t (infl (t + 1 + (j + 1))) ω := fun j => by
    rw [hrn, innov_add, Pi.add_apply]
  simp only [e] at h
  linarith

/-- Cochrane (2023), eq. (8.4), p. 250, and eq. (3.22), p. 65 (**(8.4) derived from the nonlinear
identities, with the error explicit**): under the hypotheses of `identity320_of_flow` (no growth)
and `bond_return_identity`, with `r = rⁿ − π`, at every date and state
`∑ ω̂ʲ ΔE π_{t+1+j} = −∑ ρʲ ΔE s̃_{t+1+j} + ∑_{j≥0} (ρ^{j+1} − ω̂^{j+1}) ΔE r_{t+2+j} + e`, with
`e = ∑ ω̂ʲ ΔE R^q_{t+1+j} − ∑ ρʲ ΔE R_{t+1+j}`; if `|R| ≤ B` and `|R^q| ≤ B_q` from `t + 1` on,
`|e| ≤ 2B_q/(1 − ω̂) + 2B/(1 − ρ)`. The maturity weight is `ω̂ = ω/(1 + i)` (`what_steady`). -/
theorem identity84_of_nonlinear {vbar sybar Kv Kr Ks om qbar Kq Kn B Bq : ℝ} (hs : 0 < sybar)
    (hom : 0 < om) {v r sy infl rn q : ℕ → Ω → ℝ}
    (hflow : ∀ t ω, v t ω + r (t + 1) ω - 0 = log (sy (t + 1) ω + exp (v (t + 1) ω)))
    (hret : ∀ t ω, rn (t + 1) ω = log (1 + om * exp (q (t + 1) ω)) - q t ω)
    (hva : ∀ t, 𝔼.E t (v t) = v t) (hqa : ∀ t, 𝔼.E t (q t) = q t)
    (hr : ∀ t, r t = rn t - infl t)
    (hvK : ∀ t ω, |v t ω| ≤ Kv) (hrK : ∀ t ω, |r t ω| ≤ Kr) (hsK : ∀ t ω, |sy t ω| ≤ Ks)
    (hqK : ∀ t ω, |q t ω| ≤ Kq) (hnK : ∀ t ω, |rn t ω| ≤ Kn) (t : ℕ) (ω : Ω) :
    ∑' j, what om qbar ^ j * SpreadTarget.innov 𝔼 t (infl (t + 1 + j)) ω =
      -(∑' j, rho vbar sybar ^ j * SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω) +
      (∑' j, (rho vbar sybar ^ (j + 1) - what om qbar ^ (j + 1)) *
        SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω) +
      ((∑' j, what om qbar ^ j * SpreadTarget.innov 𝔼 t (remQ om qbar q (t + 1 + j)) ω) -
        ∑' j, rho vbar sybar ^ j * SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω) ∧
    ((∀ s ω', |remF vbar sybar v sy (t + 1 + s) ω'| ≤ B) →
      (∀ s ω', |remQ om qbar q (t + 1 + s) ω'| ≤ Bq) →
      |(∑' j, what om qbar ^ j * SpreadTarget.innov 𝔼 t (remQ om qbar q (t + 1 + j)) ω) -
        ∑' j, rho vbar sybar ^ j * SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω| ≤
        2 * Bq / (1 - what om qbar) + 2 * B / (1 - rho vbar sybar)) := by
  obtain ⟨hA, hρ0, hρ1⟩ := rho_mem (vbar := vbar) hs
  obtain ⟨hw0, hw1⟩ := what_mem (qbar := qbar) hom
  set ρ := rho vbar sybar with hρdef
  set ŵ := what om qbar with hŵ
  constructor
  · have h320 := identity320_of_flow 𝔼 (vbar := vbar) (sybar := sybar) hs hflow hva hr hvK hrK
      hsK t ω
    unfold MaturityBuffer.Identity320 at h320
    have hrn : ∀ t, rn t = r t + infl t := fun t => by rw [hr t]; abel
    have hbond := bond_return_identity 𝔼 (qbar := qbar) hom hret hqa hqK hnK t ω
    have e : ∀ j, SpreadTarget.innov 𝔼 t (rn (t + 1 + (j + 1))) ω =
        SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω +
          SpreadTarget.innov 𝔼 t (infl (t + 1 + (j + 1))) ω := fun j => by
      rw [hrn, innov_add, Pi.add_apply]
    simp only [e] at hbond
    -- summability
    have hiK : ∀ s ω', |infl s ω'| ≤ Kn + Kr := fun s ω' => by
      have : infl s ω' = rn s ω' - r s ω' := by rw [hr s]; simp
      rw [this]
      exact (abs_sub _ _).trans (add_le_add (hnK s ω') (hrK s ω'))
    obtain ⟨sπ, -⟩ := discounted_le hw0.le hw1 fun j =>
      innov_bound 𝔼 (x := infl (t + 1 + j)) (hiK _) t ω
    obtain ⟨srw, -⟩ := discounted_le hw0.le hw1 fun j =>
      innov_bound 𝔼 (x := r (t + 1 + j)) (hrK _) t ω
    obtain ⟨srρ, -⟩ := discounted_le hρ0.le hρ1 fun j =>
      innov_bound 𝔼 (x := r (t + 1 + j)) (hrK _) t ω
    have sπ1 := (summable_nat_add_iff 1).2 sπ
    have srw1 := (summable_nat_add_iff 1).2 srw
    have srρ1 := (summable_nat_add_iff 1).2 srρ
    have hRK := remF_succ_le (vbar := vbar) (g := fun _ _ => 0) (Kg := 0) hs hflow hvK hrK
      (fun _ _ => by simp) hsK
    have hsK' : ∀ s ω', |stil vbar sybar sy s ω'| ≤ Ks / A0 vbar sybar := fun s ω' => by
      unfold stil
      rw [abs_div, abs_of_pos hA]
      exact div_le_div_of_nonneg_right (hsK _ _) hA.le
    obtain ⟨ss, -⟩ := discounted_le hρ0.le hρ1 fun j =>
      innov_bound 𝔼 (x := stil vbar sybar sy (t + 1 + j)) (hsK' _) t ω
    obtain ⟨sR, -⟩ := discounted_le hρ0.le hρ1 fun j =>
      innov_bound 𝔼 (x := remF vbar sybar v sy (t + 1 + j)) (fun ω' => by
        have := hRK (t + j) ω'
        rwa [show t + j + 1 = t + 1 + j by omega] at this) t ω
    have eS : ∑' j, ρ ^ j * (SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω +
        SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω) =
        (∑' j, ρ ^ j * SpreadTarget.innov 𝔼 t (stil vbar sybar sy (t + 1 + j)) ω) +
        ∑' j, ρ ^ j * SpreadTarget.innov 𝔼 t (remF vbar sybar v sy (t + 1 + j)) ω := by
      rw [← ss.tsum_add sR]
      exact tsum_congr fun j => by ring
    have eM : ∑' j, ŵ ^ (j + 1) * (SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω +
        SpreadTarget.innov 𝔼 t (infl (t + 1 + (j + 1))) ω) =
        (∑' j, ŵ ^ (j + 1) * SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω) +
        ∑' j, ŵ ^ (j + 1) * SpreadTarget.innov 𝔼 t (infl (t + 1 + (j + 1))) ω := by
      rw [← srw1.tsum_add sπ1]
      exact tsum_congr fun j => by ring
    have eD : ∑' j, (ρ ^ (j + 1) - ŵ ^ (j + 1)) *
        SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω =
        (∑' j, ρ ^ (j + 1) * SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω) -
        ∑' j, ŵ ^ (j + 1) * SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω := by
      rw [← srρ1.tsum_sub srw1]
      exact tsum_congr fun j => by ring
    have eP : ∑' j, ŵ ^ j * SpreadTarget.innov 𝔼 t (infl (t + 1 + j)) ω =
        SpreadTarget.innov 𝔼 t (infl (t + 1)) ω +
        ∑' j, ŵ ^ (j + 1) * SpreadTarget.innov 𝔼 t (infl (t + 1 + (j + 1))) ω := by
      rw [sπ.tsum_eq_zero_add]
      simp
    rw [eS] at h320
    rw [eM] at hbond
    rw [eP, eD]
    simp only [add_zero] at h320
    linarith
  · intro hB hBq
    have h1 := (discounted_le hw0.le hw1 fun j =>
      innov_bound 𝔼 (x := remQ om qbar q (t + 1 + j)) (hBq j) t ω).2
    have h2 := (discounted_le hρ0.le hρ1 fun j =>
      innov_bound 𝔼 (x := remF vbar sybar v sy (t + 1 + j)) (hB j) t ω).2
    exact (abs_sub _ _).trans (add_le_add h1 h2)

/-! ### (9.22) with remainder -/

/-- Cochrane (2023), eq. (9.22), p. 275: the fiscal shock of the derived valuation equation,
`ε_{t+1} = ∑ ρʲ ΔE_{t+1}(s̃_{t+1+j} + R_{t+1+j})` — the surplus news plus the linearisation
remainder news (`ε_0` is unused). -/
noncomputable def epsF {Ω : Type*} (𝔼 : ExpectationSystem Ω) (vbar sybar : ℝ)
    (v sy : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑' j, rho vbar sybar ^ j * (SpreadTarget.innov 𝔼 (n - 1) (stil vbar sybar sy (n + j)) ω +
    SpreadTarget.innov 𝔼 (n - 1) (remF vbar sybar v sy (n + j)) ω)

/-- Cochrane (2023), eq. (9.22), p. 275 (**(9.22) derived from the nonlinear flow**): with no
growth, one-period debt (`rⁿ_{t+1} = i_t`, `i` known at `t`), real return `r = rⁿ − π`, bounded
`v`, `r`, `sy` and `v` adapted, the exact flow (1.9) implies the linearised valuation equation
`SpreadTarget.Valuation` with `ρ = e^{v̄}/(e^{v̄} + s̄y)` and fiscal shock `epsF` — the surplus news
plus the remainder news, the latter at most `2B/(1 − ρ)` when `|R| ≤ B`
(`remainder_sum_le`). -/
theorem valuation922_of_flow {vbar sybar Kv Kr Ks : ℝ} (hs : 0 < sybar)
    {v r sy infl rn i : ℕ → Ω → ℝ}
    (hflow : ∀ t ω, v t ω + r (t + 1) ω - 0 = log (sy (t + 1) ω + exp (v (t + 1) ω)))
    (hva : ∀ t, 𝔼.E t (v t) = v t) (hr : ∀ t, r t = rn t - infl t)
    (hrn : ∀ t, rn (t + 1) = i t) (hia : ∀ t, 𝔼.E t (i t) = i t)
    (hvK : ∀ t ω, |v t ω| ≤ Kv) (hrK : ∀ t ω, |r t ω| ≤ Kr) (hsK : ∀ t ω, |sy t ω| ≤ Ks) :
    SpreadTarget.Valuation 𝔼 (rho vbar sybar) infl i (epsF 𝔼 vbar sybar v sy) := by
  obtain ⟨hA, hρ0, hρ1⟩ := rho_mem (vbar := vbar) hs
  intro t
  funext ω
  have h := identity320_of_flow 𝔼 (vbar := vbar) (sybar := sybar) hs hflow hva hr hvK hrK hsK t ω
  unfold MaturityBuffer.Identity320 at h
  have hi0 : SpreadTarget.innov 𝔼 t (rn (t + 1)) ω = 0 := by
    rw [hrn t, innov_known 𝔼 (hia t), Pi.zero_apply]
  rw [hi0, sub_zero] at h
  have e1 : ∀ j, SpreadTarget.innov 𝔼 t (r (t + 1 + (j + 1))) ω =
      SpreadTarget.innov 𝔼 t (i (t + 1 + j) - infl (t + 2 + j)) ω := fun j => by
    rw [hr, show t + 1 + (j + 1) = (t + 1 + j) + 1 by omega, hrn,
      show t + 1 + j + 1 = t + 2 + j by omega]
  simp only [e1] at h
  simp only [Pi.add_apply, Pi.neg_apply]
  rw [h]
  unfold epsF
  simp only [show t + 1 - 1 = t by omega]

end Cochrane.AssetsRulesBalanceSheets.TidyR6Linearise
