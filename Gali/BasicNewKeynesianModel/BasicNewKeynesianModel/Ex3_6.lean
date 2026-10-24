/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Ex3_5
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Exercise 3.6: the Mankiw–Reis model of sticky information

Galí (2015), Chapter 3, Exercise 3.6, pp. 94–95. Each period a fraction `1 − θ`
of firms chooses a whole path of future prices (a price plan); the others keep
their old plans.

* (a) `hasDerivAt_log_priceIndex`: eq. (38), `p_t = (1 − θ) ∑ⱼ θʲ p_{t−j,t}`, as
  the exact first-order term of the CES price index over plan vintages.
* (b) `planObjective_update`, `plan_foc_of_isLocalMax`: the plan problem
  separates across horizons; each plan price satisfies its own first-order
  condition. `plan_rule_iff`: its exact linearisation is (39),
  `p_{t,t+k} = μ + E_t ψ_{t+k}`, with `ψ = w − ½ a` (`log_marginal_cost`).
* (c) `natural_output_levels`, `natural_output`, `mc_eq_gap`: `yⁿ = a − μ` and
  `m̂c = ỹ`.
* (d) `eq40`: eq. (40),
  `π_t = ((1−θ)/θ) ỹ_t + ((1−θ)/θ) ∑_{j≥1} θʲ E_{t−j}(π_t + Δỹ_t)`.
* (e), (f) `sticky_info_closed_form`: under random-walk money and technology the
  price level is `p_t = (1 − θ) ∑ⱼ θʲ z_{t−j}` with `z = m − yⁿ`, and the output
  gap, output, employment and inflation have closed forms; the impulse
  responses to a money innovation are `θ^{j+1}` (gap and output) and
  `(1 − θ)θʲ` (inflation); to a technology innovation the gap responds by
  `−θ^{j+1}`, output by `1 − θ^{j+1}`, employment by `½ − θ^{j+1}`.
  `nkpc_comparison`: under the standard NKPC the unique bounded equilibrium has
  exactly the same form with `θ` replaced by the stable root `λ` of
  `β λ² − (1 + β + κ) λ + 1 = 0`.

Dates are natural numbers. A plan vintage `j` periods old at date `t` was chosen
with information `E_{t−j}`, where `t − j` is truncated subtraction: firms whose
plans predate date `0` all use the date-`0` information (the filtration is
constant before the start of the economy).
-/

namespace Gali.BasicNewKeynesianModel.Ex3_6

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) The price level -/

/-- The CES price index over plan vintages (Galí (2015), Ex. 3.6(a), p. 94): a
share `(1 − θ)θʲ` of firms charges `Q j = P_{t−j,t}`, the date-`t` price of the
plan chosen `j` periods earlier, so
`P_t = (∑ⱼ (1 − θ)θʲ (P_{t−j,t})^{1−ε})^{1/(1−ε)}`. -/
noncomputable def priceIndex (θ ε : ℝ) (Q : ℕ → ℝ) : ℝ :=
  (∑' j, (1 - θ) * θ ^ j * Q j ^ (1 - ε)) ^ (1 / (1 - ε))

/-- A uniform bound on `exp((p̄ + s x̂ⱼ)(1 − ε))` for `|s| ≤ 1` and `|x̂ⱼ| ≤ B`
(Galí (2015), Ex. 3.6(a)). -/
theorem exp_vintage_le {ε pbar B s : ℝ} {xhat : ℕ → ℝ} (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1)
    (j : ℕ) :
    Real.exp ((pbar + s * xhat j) * (1 - ε)) ≤ Real.exp ((|pbar| + B) * |1 - ε|) := by
  rw [Real.exp_le_exp]
  calc (pbar + s * xhat j) * (1 - ε) ≤ |(pbar + s * xhat j) * (1 - ε)| := le_abs_self _
    _ = |pbar + s * xhat j| * |1 - ε| := abs_mul _ _
    _ ≤ (|pbar| + B) * |1 - ε| := by
      gcongr
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := hx j
      nlinarith [abs_nonneg s, abs_nonneg (xhat j)]

/-- The vintage sum converges (Galí (2015), Ex. 3.6(a)). -/
theorem summable_vintage {θ ε pbar B s : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {xhat : ℕ → ℝ}
    (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1) :
    Summable fun j => (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε)) := by
  refine Summable.of_nonneg_of_le (fun j => by have := hθ1; positivity) (fun j => ?_)
    (((summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ)).mul_right
      (Real.exp ((|pbar| + B) * |1 - ε|)))
  exact mul_le_mul_of_nonneg_left (exp_vintage_le hx hs j) (by have := hθ1; positivity)

/-- The vintage sum is positive (Galí (2015), Ex. 3.6(a)). -/
theorem vintage_pos {θ ε pbar B s : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {xhat : ℕ → ℝ}
    (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1) :
    0 < ∑' j, (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε)) :=
  (summable_vintage hθ0 hθ1 hx hs).tsum_pos (fun j => by have := hθ1; positivity) 0
    (by simp only [pow_zero, mul_one]; exact mul_pos (by linarith) (Real.exp_pos _))

/-- The log price index along a path of plan prices `P_{t−j,t} = exp(p̄ + s x̂ⱼ)`
(Galí (2015), Ex. 3.6(a)). -/
theorem log_priceIndex_path {θ ε pbar B s : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {xhat : ℕ → ℝ}
    (hx : ∀ j, |xhat j| ≤ B) (hs : |s| ≤ 1) :
    Real.log (priceIndex θ ε (fun j => Real.exp (pbar + s * xhat j)))
      = 1 / (1 - ε) *
        Real.log (∑' j, (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε))) := by
  unfold priceIndex
  simp_rw [← Real.exp_mul]
  rw [Real.log_rpow (vintage_pos hθ0 hθ1 hx hs)]

/-- The shares `(1 − θ)θʲ` sum to one (Galí (2015), Ex. 3.6(a)). -/
theorem tsum_shares {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (c : ℝ) :
    ∑' j : ℕ, (1 - θ) * θ ^ j * c = c := by
  rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1]
  have : 1 - θ ≠ 0 := by linarith
  field_simp

/-- **Eq. (38)** (Galí (2015), Ex. 3.6(a), p. 94): along any bounded direction
`p_{t−j,t} = p̄ + s x̂ⱼ`, the log price level has derivative `(1 − θ) ∑ⱼ θʲ x̂ⱼ`
at the zero-inflation steady state; that is, `p_t = (1 − θ) ∑ⱼ θʲ p_{t−j,t}` to
first order. -/
theorem hasDerivAt_log_priceIndex {θ ε pbar B : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : ε ≠ 1)
    {xhat : ℕ → ℝ} (hx : ∀ j, |xhat j| ≤ B) :
    HasDerivAt (fun s => Real.log (priceIndex θ ε (fun j => Real.exp (pbar + s * xhat j))))
      ((1 - θ) * ∑' j, θ ^ j * xhat j) 0 := by
  have hε' : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hx 0)
  set C := Real.exp ((|pbar| + B) * |1 - ε|) with hC
  set g : ℕ → ℝ → ℝ := fun j s => (1 - θ) * θ ^ j * Real.exp ((pbar + s * xhat j) * (1 - ε))
    with hg
  set g' : ℕ → ℝ → ℝ := fun j s =>
    (1 - θ) * θ ^ j * (Real.exp ((pbar + s * xhat j) * (1 - ε)) * (xhat j * (1 - ε))) with hg'
  have hderiv : ∀ j s, HasDerivAt (g j) (g' j s) s := by
    intro j s
    have h1 : HasDerivAt (fun s : ℝ => (pbar + s * xhat j) * (1 - ε)) (xhat j * (1 - ε)) s := by
      simpa using (((hasDerivAt_id s).mul_const (xhat j)).const_add pbar).mul_const (1 - ε)
    exact h1.exp.const_mul _
  have hIoo : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, |s| ≤ 1 := fun s hs => abs_le.mpr ⟨hs.1.le, hs.2.le⟩
  have hT := hasDerivAt_tsum_of_isPreconnected (u := fun j => (1 - θ) * θ ^ j * (C * (B * |1 - ε|)))
    (g := g) (g' := g') (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    ((summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ) |>.mul_right _) isOpen_Ioo
    isPreconnected_Ioo (fun j s _ => hderiv j s)
    (fun j s hs => by
      simp only [hg', Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ), abs_of_nonneg (pow_nonneg hθ0 j)]
      refine mul_le_mul_of_nonneg_left ?_ (by have := hθ1; positivity)
      exact mul_le_mul (exp_vintage_le hx (hIoo s hs) j)
        (mul_le_mul_of_nonneg_right (hx j) (abs_nonneg _)) (by positivity) (by positivity))
    ⟨by norm_num, by norm_num⟩ (summable_vintage hθ0 hθ1 hx (by simp)) ⟨by norm_num, by norm_num⟩
  have hval : ∑' j, g j 0 = Real.exp (pbar * (1 - ε)) := by
    simp only [hg, zero_mul, add_zero]
    exact tsum_shares hθ0 hθ1 _
  have hL := (hT.log (by rw [hval]; exact (Real.exp_pos _).ne')).const_mul (1 / (1 - ε))
  have hfun : (fun s => Real.log (priceIndex θ ε (fun j => Real.exp (pbar + s * xhat j))))
      =ᶠ[𝓝 0] fun s => 1 / (1 - ε) * Real.log (∑' j, g j s) := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
      with s hs
    exact log_priceIndex_path hθ0 hθ1 hx (hIoo s hs)
  refine (hL.congr_of_eventuallyEq hfun).congr_deriv ?_
  rw [hval]
  have hs' : ∑' j, g' j 0
      = (1 - θ) * Real.exp (pbar * (1 - ε)) * (1 - ε) * ∑' j, θ ^ j * xhat j := by
    rw [← tsum_mul_left]
    congr 1; funext j
    simp only [hg', zero_mul, add_zero]
    ring
  rw [hs']
  have := (Real.exp_pos (pbar * (1 - ε))).ne'
  field_simp

/-- The price level at the zero-inflation steady state (Galí (2015), Ex. 3.6(a)). -/
theorem log_priceIndex_steady {θ ε pbar : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : ε ≠ 1) :
    Real.log (priceIndex θ ε (fun _ => Real.exp pbar)) = pbar := by
  have h := log_priceIndex_path (ε := ε) (pbar := pbar) (B := 0) (s := 0) hθ0 hθ1
    (xhat := fun _ => 0) (fun _ => by simp) (by simp)
  simp only [mul_zero, add_zero] at h
  rw [h, tsum_shares hθ0 hθ1, Real.log_exp]
  have : 1 - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
  field_simp

/-! ### (b) The price plan -/

/-- With technology `Y = √A N` and wage `W`, nominal marginal cost is `W/√A`,
so `ψ = w − ½ a` (Galí (2015), Ex. 3.6(b), p. 94). -/
theorem log_marginal_cost {W A : ℝ} (hW : 0 < W) (hA : 0 < A) :
    Real.log (W / Real.sqrt A) = Real.log W - Real.log A / 2 := by
  rw [Real.log_div hW.ne' (Real.sqrt_pos.mpr hA).ne', Real.log_sqrt hA.le]

/-- **The price-plan objective** (Galí (2015), Ex. 3.6(b), p. 94): for a plan
`x = (P_{t,t+k})ₖ`,
`∑ₖ θᵏ E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k}(i)(P_{t,t+k} − Ψ_{t+k})]`, with
`Ψ_{t+k} = W_{t+k}/√A_{t+k}` and the demand of Ex. 3.5. -/
noncomputable def planObjective (θ ε : ℝ) (Λ P C Ψ : ℕ → Ω → ℝ) (t : ℕ) (x : ℕ → ℝ)
    (ω : Ω) : ℝ :=
  ∑' k, θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω

/-- **The plan problem separates across horizons** (Galí (2015), Ex. 3.6(b)): if
the objective converges at the plan `x`, then changing the horizon-`k` price to
`z` changes only the horizon-`k` term. -/
theorem planObjective_update {θ ε : ℝ} {Λ P C Ψ : ℕ → Ω → ℝ} {t : ℕ} {x : ℕ → ℝ} {ω : Ω}
    (hs : Summable fun k => θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω)
    (k : ℕ) (z : ℝ) :
    planObjective 𝔼 θ ε Λ P C Ψ t (Function.update x k z) ω
      = θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω
        + ∑' j, if j = k then 0
            else θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω := by
  set f : ℕ → ℝ := fun j => θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω
    with hf
  have hupd : (fun j => θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j)
      (Function.update x k z j)) ω)
      = Function.update f k (θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  unfold planObjective
  rw [hupd, (hs.update k _).tsum_eq_add_tsum_ite k]
  simp only [Function.update_self]
  congr 1
  refine tsum_congr fun j => ?_
  by_cases hj : j = k
  · simp [hj]
  · simp only [hj, ↓reduceIte]
    rw [Function.update_of_ne hj]

/-- **The first-order condition for each plan price** (Galí (2015), Ex. 3.6(b),
p. 94): if the plan `x` is locally optimal in its horizon-`k` price
`x k > 0`, and `θ > 0`, then
`E_t[Λ_{t,t+k}(1/P_{t+k}) Y_{t+k}(i) (P_{t,t+k} − M Ψ_{t+k})] = 0`. -/
theorem plan_foc_of_isLocalMax {θ ε : ℝ} (hθ : 0 < θ) (hε : 1 < ε) {Λ P C Ψ : ℕ → Ω → ℝ}
    (hP : ∀ k ω, 0 < P k ω) {t : ℕ} {x : ℕ → ℝ} {ω : Ω}
    (hs : Summable fun k => θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω)
    {k : ℕ} (hxk : 0 < x k)
    (hmax : IsLocalMax (fun z => planObjective 𝔼 θ ε Λ P C Ψ t (Function.update x k z) ω) (x k)) :
    𝔼.E t (Ex3_5.focTerm ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω = 0 := by
  have hfun : (fun z => planObjective 𝔼 θ ε Λ P C Ψ t (Function.update x k z) ω)
      = fun z => θ ^ k * 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω
        + ∑' j, if j = k then 0
            else θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω :=
    funext fun z => planObjective_update 𝔼 hs k z
  have hd := Ex3_5.hasDerivAt_closedForm hε hxk (𝔼.E t (Ex3_5.wgt ε (Λ k) (P k) (C k)) ω)
    (𝔼.E t (Ex3_5.wgt ε (Λ k) (P k) (C k) * Ψ k) ω)
  have hd' : HasDerivAt (fun z => 𝔼.E t (Ex3_5.profit ε (Λ k) (P k) (C k) (Ψ k) z) ω)
      ((1 - ε) / x k * 𝔼.E t (Ex3_5.focTerm ε (Λ k) (P k) (C k) (Ψ k) (x k)) ω) (x k) := by
    rw [Ex3_5.E_focTerm_eq 𝔼 hxk (hP k)]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hxk] with z hz
    exact Ex3_5.E_profit_eq 𝔼 hz (hP k) t ω
  have hD := (hd'.const_mul (θ ^ k)).add_const
    (∑' j, if j = k then 0
      else θ ^ j * 𝔼.E t (Ex3_5.profit ε (Λ j) (P j) (C j) (Ψ j) (x j)) ω)
  rw [hfun] at hmax
  have h0 := hmax.hasDerivAt_eq_zero hD
  have hc : θ ^ k * ((1 - ε) / x k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero k hθ.ne') (div_ne_zero (by linarith) hxk.ne')
  rw [← mul_assoc] at h0
  exact (mul_eq_zero.mp h0).resolve_left hc

/-- **Exact linearisation of a plan price's first-order condition**
(Galí (2015), Ex. 3.6(b), p. 94): with weight `w = w̄ exp(s ŵ)`, plan price
`exp(p̄ + s x̂)` and marginal cost `exp(p̄ − μ + s ψ̂)`, the derivative at `s = 0`
is `w̄ e^{p̄}(x̂ − E_t ψ̂)`. -/
theorem plan_hasDerivAt_path {ε wbar pbar xhat B : ℝ} (hε : 1 < ε) {what ψhat : Ω → ℝ}
    (hw : ∀ ω, |what ω| ≤ B) (hψ : ∀ ω, |ψhat ω| ≤ B) (hxB : |xhat| ≤ B) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => 𝔼.E t (fun ω' => wbar * Real.exp (s * what ω') *
        (Real.exp (pbar + s * xhat)
          - Ex3_5.markup ε * Real.exp (pbar - Ex3_5.logMarkup ε + s * ψhat ω'))) ω)
      (wbar * Real.exp pbar * (xhat - 𝔼.E t ψhat ω)) 0 := by
  have h := Ex3_5.hasDerivAt_focLHS_path 𝔼 (N := 1) (β := 1) (wbar := wbar) (pbar := pbar)
    hε (what := fun _ => what) (ψhat := fun _ => ψhat) (fun _ => hw) (fun _ => hψ) hxB t ω
  simpa [Ex3_5.focLHS] using h

/-- **The plan rule (39)** (Galí (2015), Ex. 3.6(b), p. 94): the first-order
term vanishes if and only if `p_{t,t+k} = μ + E_t ψ_{t+k}`, where
`p_{t,t+k} = p̄ + x̂` and `ψ_{t+k} = (p̄ − μ) + ψ̂`. -/
theorem plan_rule_iff {ε wbar pbar xhat : ℝ} (hwbar : 0 < wbar) (ψhat : Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    wbar * Real.exp pbar * (xhat - 𝔼.E t ψhat ω) = 0 ↔
      pbar + xhat
        = Ex3_5.logMarkup ε + 𝔼.E t (fun ω' => (pbar - Ex3_5.logMarkup ε) + ψhat ω') ω := by
  have hf : (fun ω' => (pbar - Ex3_5.logMarkup ε) + ψhat ω')
      = (fun _ => pbar - Ex3_5.logMarkup ε) + ψhat := rfl
  rw [hf, map_add, 𝔼.const, Pi.add_apply]
  have hc : wbar * Real.exp pbar ≠ 0 := (mul_pos hwbar (Real.exp_pos _)).ne'
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_left hc
    linarith
  · intro h
    have : xhat - 𝔼.E t ψhat ω = 0 := by linarith
    rw [this, mul_zero]

/-! ### (c) Natural output and marginal cost -/

/-- **Natural output in levels** (Galí (2015), Ex. 3.6(c), p. 94): with flexible
prices `P = M W/√A`, labour supply `W/P = N` (from `U = C − N²/2`), and
`Y = √A N`, output is `Y = A/M`, i.e. `yⁿ = a − μ` exactly. -/
theorem natural_output_levels {ε P W A Y Nl : ℝ} (hε : 1 < ε) (hA : 0 < A)
    (hflex : P = Ex3_5.markup ε * (W / Real.sqrt A)) (hP : 0 < P) (hls : W / P = Nl)
    (hy : Y = Real.sqrt A * Nl) : Real.log Y = Real.log A - Ex3_5.logMarkup ε := by
  have hM := Ex3_5.markup_pos hε
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hWA : 0 < W / Real.sqrt A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hsA
    rwa [div_mul_cancel₀ W hsA.ne'] at this
  have hN : Nl = Real.sqrt A / Ex3_5.markup ε := by
    rw [← hls, hflex]; field_simp
  have hY : Y = A / Ex3_5.markup ε := by
    rw [hy, hN, ← mul_div_assoc, Real.mul_self_sqrt hA.le]
  rw [hY, Real.log_div hA.ne' hM.ne']
  rfl

/-- **Natural output in logs** (Galí (2015), Ex. 3.6(c)(i), p. 94): flexible
prices `p = μ + ψ` with `ψ = w − ½a`, labour supply `w − p = n` and
`y = ½a + n` give `yⁿ = a − μ`. -/
theorem natural_output {μ p w a y n : ℝ} (hflex : p = μ + (w - a / 2)) (hls : w - p = n)
    (hy : y = a / 2 + n) : y = a - μ := by
  rw [hy, ← hls, hflex]; ring

/-- **Real marginal cost equals the output gap** (Galí (2015), Ex. 3.6(c)(ii),
p. 94): `m̂c_t = (ψ_t − p_t) + μ = y_t − yⁿ_t`. -/
theorem mc_eq_gap {μ p w a y n : ℝ} (hls : w - p = n) (hy : y = a / 2 + n) :
    ((w - a / 2) - p) + μ = y - (a - μ) := by
  rw [hy, ← hls]; ring

/-! ### (d) The sticky-information Phillips curve (40) -/

/-- Geometrically weighted expectations of a bounded random variable converge
(Galí (2015), Ex. 3.6(d)). -/
theorem summable_geom_E {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {Y : Ω → ℝ} {M : ℝ}
    (hY : ∀ ω, |Y ω| ≤ M) (f : ℕ → ℕ) (ω : Ω) :
    Summable fun j => θ ^ j * 𝔼.E (f j) Y ω := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ0 hθ1).mul_right M)
    fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hθ0 j)]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le hY _ ω) (pow_nonneg hθ0 j)

/-- The price level as a vintage average of expectations (Galí (2015), Ex. 3.6(d)):
combining (38) and (39) with `ψ = p + ỹ − μ`,
`p_t = (1 − θ) ∑ⱼ θʲ E_{t−j}(p_t + ỹ_t)`. -/
theorem price_level_eq {θ μ : ℝ} {p ytil ψ : ℕ → Ω → ℝ} {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (t : ℕ) (ω : Ω) :
    p t ω = (1 - θ) * ∑' j, θ ^ j * 𝔼.E (t - j) (p t + ytil t) ω := by
  rw [hindex t ω]
  congr 2; funext j
  rw [hplan, hψ, map_sub, 𝔼.const]
  simp

/-- **Eq. (40)** (Galí (2015), Ex. 3.6(d), p. 95). Under (38), (39) and
`ψ = p + ỹ − μ` (part (c)), with `p` and `ỹ` adapted and bounded at each date,
inflation `π_{t+1} = p_{t+1} − p_t` satisfies
`π_{t+1} = ((1−θ)/θ) ỹ_{t+1} + ((1−θ)/θ) ∑_{j≥1} θʲ E_{t+1−j}(π_{t+1} + Δỹ_{t+1})`;
the `j`-th term below is the `(j+1)`-st of the book, with `E_{(t+1)−(j+1)} = E_{t−j}`. -/
theorem eq40 {θ μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {p ytil ψ infl : ℕ → Ω → ℝ}
    {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hpa : 𝔼.Adapted p) (hya : 𝔼.Adapted ytil)
    (hb : ∀ t, ∃ M, ∀ ω, |p t ω + ytil t ω| ≤ M) (t : ℕ) (ω : Ω) :
    infl (t + 1) ω = (1 - θ) / θ * ytil (t + 1) ω + (1 - θ) / θ *
      ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) (infl (t + 1) + (ytil (t + 1) - ytil t)) ω := by
  obtain ⟨M₁, hM₁⟩ := hb (t + 1)
  obtain ⟨M₀, hM₀⟩ := hb t
  set X1 := p (t + 1) + ytil (t + 1) with hX1
  set X0 := p t + ytil t with hX0
  have hX1b : ∀ ω, |X1 ω| ≤ M₁ := hM₁
  have hX0b : ∀ ω, |X0 ω| ≤ M₀ := hM₀
  have hX1a : 𝔼.E (t + 1) X1 = X1 := by rw [hX1, map_add, hpa, hya]
  have hp1 := price_level_eq 𝔼 hindex hplan hψ (t + 1) ω
  have hp0 := price_level_eq 𝔼 hindex hplan hψ t ω
  rw [← hX1] at hp1
  rw [← hX0] at hp0
  have hs1 := summable_geom_E 𝔼 hθ0.le hθ1 hX1b (fun j => t + 1 - j) ω
  rw [hs1.tsum_eq_zero_add] at hp1
  simp only [pow_zero, one_mul, Nat.sub_zero, hX1a, Nat.add_sub_add_right] at hp1
  have hsA : Summable fun j => θ ^ (j + 1) * 𝔼.E (t - j) X1 ω := by
    have := (summable_geom_E 𝔼 hθ0.le hθ1 hX1b (fun j => t - j) ω).mul_left θ
    refine this.congr fun j => ?_
    ring
  have hsB : Summable fun j => θ ^ (j + 1) * 𝔼.E (t - j) X0 ω := by
    have := (summable_geom_E 𝔼 hθ0.le hθ1 hX0b (fun j => t - j) ω).mul_left θ
    refine this.congr fun j => ?_
    ring
  have hB : ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) X0 ω = θ * ∑' j, θ ^ j * 𝔼.E (t - j) X0 ω := by
    rw [← tsum_mul_left]
    congr 1; funext j; ring
  have hdiff : infl (t + 1) + (ytil (t + 1) - ytil t) = X1 - X0 := by
    rw [hinfl, hX1, hX0]; abel
  have hD : ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) (infl (t + 1) + (ytil (t + 1) - ytil t)) ω
      = ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) X1 ω - ∑' j, θ ^ (j + 1) * 𝔼.E (t - j) X0 ω := by
    rw [← hsA.tsum_sub hsB, hdiff]
    congr 1; funext j
    rw [map_sub, Pi.sub_apply]; ring
  rw [hD, hB]
  have hi := congrFun (hinfl t) ω
  simp only [Pi.sub_apply] at hi
  rw [hi, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hθ0.ne']
  have hX1ω : X1 ω = p (t + 1) ω + ytil (t + 1) ω := rfl
  linear_combination hp1 - θ * hp0 + (1 - θ) * hX1ω

/-! ### (e), (f) Random walks: closed forms -/

/-- With money demand `y = m − p`, the vintage average involves only
`z = m − yⁿ`, so with `z` a random walk
`p_t = (1 − θ) ∑ⱼ θʲ z_{t−j}` (Galí (2015), Ex. 3.6(e), p. 95). -/
theorem price_level_randomWalk {θ μ : ℝ} {p ytil ψ z : ℕ → Ω → ℝ} {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (hgap : ∀ t, ytil t = z t - p t)
    (hz : 𝔼.IsAR1 1 z) (t : ℕ) (ω : Ω) :
    p t ω = (1 - θ) * ∑' j, θ ^ j * z (t - j) ω := by
  rw [price_level_eq 𝔼 hindex hplan hψ t ω]
  congr 2; funext j
  have hX : p t + ytil t = z t := by rw [hgap]; abel
  have hk := 𝔼.ar1_iterate hz (t - j) j
  simp only [one_pow, one_smul] at hk
  rw [hX]
  rcases le_or_gt j t with h | h
  · rw [Nat.sub_add_cancel h] at hk
    rw [hk]
  · have h0 : t - j = 0 := by omega
    rw [h0]
    have := 𝔼.ar1_iterate hz 0 t
    simp only [one_pow, one_smul, zero_add] at this
    rw [this]

/-- The lagged sums `∑ⱼ θʲ z_{s−j}` converge: only `z₀, …, z_s` enter
(Galí (2015), Ex. 3.6(e)). -/
theorem summable_lagged {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (z : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    Summable fun j => θ ^ j * z (s - j) ω := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hθ0 hθ1).mul_right
    (∑ k ∈ Finset.range (s + 1), |z k ω|)) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hθ0 j)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 j)
  exact Finset.single_le_sum (f := fun k => |z k ω|) (fun k _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

/-- **The price-level recursion** (Galí (2015), Ex. 3.6(e), p. 95): if
`p_t = (1 − θ) ∑ⱼ θʲ z_{t−j}`, then `p₀ = z₀` and
`p_{t+1} = θ p_t + (1 − θ) z_{t+1}`. -/
theorem price_level_rec {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {p z : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * z (t - j) ω) (ω : Ω) :
    p 0 ω = z 0 ω ∧ ∀ t, p (t + 1) ω = θ * p t ω + (1 - θ) * z (t + 1) ω := by
  constructor
  · rw [hp 0 ω]
    simp only [Nat.zero_sub]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hθ0 hθ1]
    have : 1 - θ ≠ 0 := by linarith
    field_simp
  · intro t
    rw [hp (t + 1) ω, hp t ω, (summable_lagged hθ0 hθ1 z (t + 1) ω).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    have : ∑' j, θ ^ (j + 1) * z (t - j) ω = θ * ∑' j, θ ^ j * z (t - j) ω := by
      rw [← tsum_mul_left]
      congr 1; funext j; ring
    rw [this]
    ring

/-- The cumulated innovations `Hₜ = ∑_{j≤t} θʲ v_{t−j}`, `vᵢ = z_{i+1} − z_i`
(Galí (2015), Ex. 3.6(e)–(f)). -/
noncomputable def cumInnov (θ : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (t + 1), θ ^ j * (z (t - j + 1) ω - z (t - j) ω)

/-- `H_{t+1} = v_{t+1} + θ H_t` (Galí (2015), Ex. 3.6(e)). -/
theorem cumInnov_succ (θ : ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    cumInnov θ z (t + 1) ω = (z (t + 2) ω - z (t + 1) ω) + θ * cumInnov θ z t ω := by
  unfold cumInnov
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_sub_add_right]
  ring

/-- **The sticky-information equilibrium under random walks in closed form**
(Galí (2015), Ex. 3.6(e)–(f), p. 95). With (38), (39), `ψ = p + ỹ − μ`, money
demand `ỹ = z − p` for `z = m − yⁿ` a random walk, and `0 ≤ θ < 1`:
`ỹ_{t+1} = θ H_t`, `π_{t+1} = (1 − θ) H_t` and `p_{t+1} = z_{t+1} − θ H_t`, where
`H_t = ∑_{j≤t} θʲ v_{t−j}` and `ỹ₀ = 0`. A unit innovation `v` raises the gap by
`θ^{j+1}` after `j` periods and inflation by `(1 − θ)θʲ`. The equilibrium is
unique: the price level is pinned down without any boundedness condition. -/
theorem sticky_info_closed_form {θ μ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    {p ytil ψ z infl : ℕ → Ω → ℝ} {pplan : ℕ → ℕ → Ω → ℝ}
    (hindex : ∀ t ω, p t ω = (1 - θ) * ∑' j, θ ^ j * pplan (t - j) t ω)
    (hplan : ∀ s t, pplan s t = (fun _ => μ) + 𝔼.E s (ψ t))
    (hψ : ∀ t, ψ t = p t + ytil t - fun _ => μ) (hgap : ∀ t, ytil t = z t - p t)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (hz : 𝔼.IsAR1 1 z) (ω : Ω) :
    ytil 0 ω = 0 ∧ ∀ t, ytil (t + 1) ω = θ * cumInnov θ z t ω ∧
      infl (t + 1) ω = (1 - θ) * cumInnov θ z t ω ∧
      p (t + 1) ω = z (t + 1) ω - θ * cumInnov θ z t ω := by
  have hp := price_level_randomWalk 𝔼 hindex hplan hψ hgap hz
  obtain ⟨h0, hrec⟩ := price_level_rec hθ0 hθ1 hp ω
  have hy : ∀ t, ytil t ω = z t ω - p t ω := fun t => by rw [hgap t]; rfl
  have hkey : ∀ t, ytil t ω + (z (t + 1) ω - z t ω) = cumInnov θ z t ω := by
    intro t
    induction t with
    | zero =>
      simp [cumInnov, hy, h0]
    | succ t ih =>
      rw [cumInnov_succ, ← ih, hy, hy, hrec t]
      ring
  refine ⟨by rw [hy, h0, sub_self], fun t => ?_⟩
  have h1 : ytil (t + 1) ω = θ * cumInnov θ z t ω := by
    rw [← hkey t, hy, hy, hrec t]; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [hinfl t, Pi.sub_apply, ← hkey t, hy, hrec t]; ring
  · rw [← h1, hy]; ring

/-- **Output, employment and the gap in terms of money and technology
innovations** (Galí (2015), Ex. 3.6(e)–(f), p. 95). With `yⁿ = a − μ`,
`z = m − yⁿ`, output `y = yⁿ + ỹ` and employment `n = y − ½ a`:
`vᵢ = (m_{i+1} − m_i) − (a_{i+1} − a_i)`, so after a money innovation `u` the gap
and output rise by `θ^{j+1} u` and employment too; after a technology
innovation `ε` the gap moves by `−θ^{j+1} ε`, output by `(1 − θ^{j+1}) ε`,
employment by `(½ − θ^{j+1}) ε`, inflation by `−(1 − θ)θʲ ε`. -/
theorem output_employment {μ : ℝ} {m a yn z ytil y n : ℕ → Ω → ℝ}
    (hyn : ∀ t, yn t = a t - fun _ => μ) (hz : ∀ t, z t = m t - yn t)
    (hy : ∀ t, y t = yn t + ytil t) (hn : ∀ t, n t = y t - (1 / 2 : ℝ) • a t) (t : ℕ) (ω : Ω) :
    z (t + 1) ω - z t ω = (m (t + 1) ω - m t ω) - (a (t + 1) ω - a t ω) ∧
      y t ω = a t ω - μ + ytil t ω ∧ n t ω = a t ω / 2 - μ + ytil t ω := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hz, hyn, Pi.sub_apply]; ring
  · simp only [hy, hyn, Pi.add_apply, Pi.sub_apply]
  · simp only [hn, hy, hyn, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-! ### Comparison with the standard New Keynesian Phillips curve -/

/-- The stable root `λ = ((1 + β + κ) − √((1 + β + κ)² − 4β))/(2β)` of
`β λ² − (1 + β + κ) λ + 1 = 0` (Galí (2015), Ex. 3.6(e), p. 95). -/
noncomputable def nkpcRoot (β κ : ℝ) : ℝ :=
  ((1 + β + κ) - Real.sqrt ((1 + β + κ) ^ 2 - 4 * β)) / (2 * β)

/-- `λ` solves `β λ² − (1 + β + κ) λ + 1 = 0` (Galí (2015), Ex. 3.6(e)). -/
theorem nkpcRoot_quadratic {β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) :
    β * nkpcRoot β κ ^ 2 - (1 + β + κ) * nkpcRoot β κ + 1 = 0 := by
  have hD : 0 ≤ (1 + β + κ) ^ 2 - 4 * β := by nlinarith
  have hs := Real.sq_sqrt hD
  unfold nkpcRoot
  generalize Real.sqrt ((1 + β + κ) ^ 2 - 4 * β) = r at hs ⊢
  field_simp
  linear_combination hs

/-- `0 < λ < 1` (Galí (2015), Ex. 3.6(e)). -/
theorem nkpcRoot_mem {β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) :
    0 < nkpcRoot β κ ∧ nkpcRoot β κ < 1 := by
  have hD : 0 ≤ (1 + β + κ) ^ 2 - 4 * β := by nlinarith
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg ((1 + β + κ) ^ 2 - 4 * β)
  unfold nkpcRoot
  constructor
  · apply div_pos _ (by linarith)
    nlinarith
  · rw [div_lt_one (by linarith)]
    nlinarith

/-- **The NKPC comparison** (Galí (2015), Ex. 3.6(e)–(f), p. 95). Replace (40)
by the NKPC `π_{t+1} = β E_{t+1} π_{t+2} + κ ỹ_{t+1}` with `π_{t+1} = p_{t+1} − p_t`,
`ỹ = z − p`, `z` a random walk with bounded innovations, `p` adapted and
`p − z` bounded. Then the equilibrium is unique given `p₀`, and
`ỹ_{t+1} = λ(ỹ_t + v_t)`, `π_{t+1} = (1 − λ)(ỹ_t + v_t)` with the stable root
`λ ∈ (0,1)`: the same dynamics as sticky information,
`ỹ_{t+1} = θ(ỹ_t + v_t)`, `π_{t+1} = (1 − θ)(ỹ_t + v_t)`, with `θ` replaced by `λ`. -/
theorem nkpc_comparison {β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    {p z ytil infl : ℕ → Ω → ℝ} (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hnkpc : ∀ t, infl (t + 1) = β • 𝔼.E (t + 1) (infl (t + 2)) + κ • ytil (t + 1))
    (hgap : ∀ t, ytil t = z t - p t) (hza : 𝔼.Adapted z) (hzrw : ∀ t, 𝔼.E t (z (t + 1)) = z t)
    {K : ℝ} (hK : ∀ t ω, |z (t + 1) ω - z t ω| ≤ K) (hpa : 𝔼.Adapted p)
    (hb : BoundedProc fun t => p t - z t) (t : ℕ) (ω : Ω) :
    ytil (t + 1) ω = nkpcRoot β κ * (ytil t ω + (z (t + 1) ω - z t ω)) ∧
      infl (t + 1) ω = (1 - nkpcRoot β κ) * (ytil t ω + (z (t + 1) ω - z t ω)) := by
  set S := 1 + β + κ with hS
  set lam := nkpcRoot β κ with hlam
  obtain ⟨hl0, hl1⟩ := nkpcRoot_mem hβ hβ1 hκ
  have hq : β * lam ^ 2 - S * lam + 1 = 0 := nkpcRoot_quadratic hβ hβ1 hκ
  have hq' : β * lam ^ 2 - (1 + β + κ) * lam + 1 = 0 := hq
  have hS0 : 0 < S := by positivity
  have hSl : 0 < S - β * lam := by
    have h1 : lam * (S - β * lam) = 1 := by linear_combination -hq
    by_contra h
    push Not at h
    nlinarith
  have hsol : Ex3_5.SolvesPre 𝔼 (1 / S) (β / S) (fun t => -(1 / S) • (z t - z (t - 1)))
      (fun t => p t - z t) := by
    intro t
    have hEq : 𝔼.E (t + 1) (p (t + 2) - z (t + 2)) = 𝔼.E (t + 1) (p (t + 2)) - z (t + 1) := by
      rw [map_sub, hzrw]
    have hEi : 𝔼.E (t + 1) (infl (t + 2)) = 𝔼.E (t + 1) (p (t + 2)) - p (t + 1) := by
      rw [hinfl (t + 1), map_sub, hpa (t + 1)]
    change p (t + 1) - z (t + 1) = (1 / S) • (p t - z t)
      + (β / S) • 𝔼.E (t + 1) (p (t + 2) - z (t + 2)) + -(1 / S) • (z (t + 1) - z (t + 1 - 1))
    rw [hEq, Nat.add_sub_cancel]
    funext ω
    have e1 := congrFun (hnkpc t) ω
    have e2 := congrFun (hinfl t) ω
    have e3 := congrFun hEi ω
    have e4 := congrFun (hgap (t + 1)) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
    field_simp
    linear_combination e1 - e2 + β * e3 + κ * e4
  have hA : 1 / S = lam * (1 - β / S * lam) := by
    field_simp
    linear_combination hq'
  have hd : 1 - β / S * lam ≠ 0 := by
    have : 1 - β / S * lam = (S - β * lam) / S := by field_simp
    rw [this]; positivity
  have hγ : |β / S / (1 - β / S * lam)| < 1 := by
    have : β / S / (1 - β / S * lam) = β * lam := by
      rw [div_eq_iff hd]
      field_simp
      linear_combination hq'
    rw [this, abs_of_pos (by positivity)]
    nlinarith
  have hfa : 𝔼.Adapted (fun t => -(1 / S) • (z t - z (t - 1))) := by
    intro t
    have : 𝔼.E t (z (t - 1)) = z (t - 1) := by
      rw [← hza (t - 1), 𝔼.known (Nat.sub_le t 1)]
    simp only [map_smul, map_sub, hza t, this]
  have hf0 : ∀ t, 𝔼.E t ((fun t => -(1 / S) • (z t - z (t - 1))) (t + 1)) = 0 := by
    intro t
    simp only [Nat.add_sub_cancel, map_smul, map_sub, hzrw t, hza t, sub_self, smul_zero]
  have hq0 : 𝔼.E 0 (p 0 - z 0) = p 0 - z 0 := by rw [map_sub, hpa 0, hza 0]
  have hex := Ex3_5.predetermined_solves 𝔼 hA hd hfa hf0 hq0
  set g : ℕ → Ω → ℝ := fun t => (1 - β / S * lam)⁻¹ • -(1 / S) • (z t - z (t - 1)) with hg
  have hga : 𝔼.Adapted g := fun t => by simp only [hg, map_smul, hfa t]
  obtain ⟨M, hM⟩ := hb
  have hgb : ∀ t ω, |g t ω| ≤ |(1 - β / S * lam)⁻¹ * (1 / S)| * K := by
    intro t ω
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ω)
    cases t with
    | zero =>
      simp only [hg, Nat.zero_sub, sub_self, smul_zero, Pi.zero_apply, abs_zero]
      positivity
    | succ t =>
      simp only [hg, Nat.add_sub_cancel, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [show (1 - β / S * lam)⁻¹ * (-(1 / S) * (z (t + 1) ω - z t ω))
          = -((1 - β / S * lam)⁻¹ * (1 / S)) * (z (t + 1) ω - z t ω) by ring, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg _)
  have hlam1 : |lam| < 1 := by rw [abs_of_pos hl0]; exact hl1
  have huniq := Ex3_5.predetermined_unique 𝔼 hA hd hγ hsol hex
    (fun t => by simp only [map_sub, hpa t, hza t]) (Ex3_5.ar1Path_adapted 𝔼 hga hq0)
    ⟨M, hM⟩ ⟨_, Ex3_5.ar1Path_bounded hlam1 hgb (M0 := M) (hM 0)⟩ rfl
  have hstep : p (t + 1) ω - z (t + 1) ω
      = lam * (p t ω - z t ω) - lam * (z (t + 1) ω - z t ω) := by
    have h1 : p (t + 1) ω - z (t + 1) ω = Ex3_5.ar1Path lam g (p 0 - z 0) (t + 1) ω :=
      congrFun (congrFun huniq (t + 1)) ω
    have h0 : p t ω - z t ω = Ex3_5.ar1Path lam g (p 0 - z 0) t ω :=
      congrFun (congrFun huniq t) ω
    rw [h1, h0]
    have hsc : (1 - β / S * lam)⁻¹ * (1 / S) = lam := by
      field_simp
      linear_combination hq'
    simp only [Ex3_5.ar1Path, hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      Nat.add_sub_cancel]
    rw [show (1 - β / S * lam)⁻¹ * (-(1 / S) * (z (t + 1) ω - z t ω))
        = -((1 - β / S * lam)⁻¹ * (1 / S)) * (z (t + 1) ω - z t ω) by ring, hsc]
    ring
  have hy1 := congrFun (hgap (t + 1)) ω
  have hy0 := congrFun (hgap t) ω
  have hi := congrFun (hinfl t) ω
  simp only [Pi.sub_apply] at hy1 hy0 hi
  constructor
  · rw [hy1, hy0]; linear_combination -hstep
  · rw [hi, hy0]; linear_combination hstep

end Gali.BasicNewKeynesianModel.Ex3_6
