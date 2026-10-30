/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6CalvoReset
import KeynesianStickyPrices.TidyR6RotembergPC

/-!
# The Phillips curve (17.17) from the Calvo price setter

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, eq. (17.17), p. 407, and
Chapter 5, §5.1, p. 118 ("a random probability of being allowed to change price").

Calvo price setters (TidyR6CalvoReset) who are yeoman farmers: CRRA utility of consumption
(`u′(C) = C^{−γ}`), disutility `y^{1+ϕ}/(1 + ϕ)` of producing, consumption equal to output
`Y_t = Ȳe^{x_t}`, survival probability `α`, discount factor `β`, `δ = αβ`, `η = ε(1 + ϕ)`.
A setter resetting at `t` to the relative price `e^{r}` earns at `t + k` the weights
`a_{t,k} = Ȳ^{1−γ}e^{(1−γ)x_{t+k} + (ε−1)(p_{t+k} − p_t)}` (`aW`) and
`b_{t,k} = Ȳ^{1+ϕ}e^{(1+ϕ)x_{t+k} + η(p_{t+k} − p_t)}/(1 + ϕ)` (`bW`).

The parameters are bundled in `CalvoPar`; `CalvoPar.Valid` states `0 < α < 1`, `0 < β < 1`,
`ε > 1`, `ϕ ≥ 0`, `Ȳ > 0` with the steady state `εȲ^{1+ϕ} = (ε − 1)Ȳ^{1−γ}`. Output gap and
inflation are bounded by `L` everywhere, and `δe^{ηL} < 1` (so the discounted sums converge).

## Main results

* `wA_succ`, `wA_bounds`: the discounted sums `W_A`, `W_B` satisfy `W_t = a_{t,0} +
  δe^{(ε−1)π_{t+1}}W_{t+1}` pathwise and lie in explicit positive bounds.
* `fc_rec`: the forecasts `F_t = E_tW_{A,t}`, `K_t = E_tW_{B,t}` satisfy the exact recursions;
  in logs `f_t = log(F_t/F̄)`, `k_t = log(K_t/K̄)`.
* `rF_bounds`: the explicit remainder `R^F` of the log-linearised recursion is second order,
  `−(e^{f_t} − 1)²e^{−f_t} ≤ R^F_t ≤ (1 − δ)expRem((1−γ)x_t) + δE_t expRem((ε−1)π_{t+1} + f_{t+1})`.
* `resetOpt_iff_gap`: resetting optimally at `t` is `(1 − ε + η)r_t = k_t − f_t`.
* `pc_residual`: **exactly**, with the Calvo index `1 = αe^{(ε−1)π_t} + (1 − α)e^{(1−ε)r_t}`,
  `π_t − βE_tπ_{t+1} − κx_t − u_{π,t} = ((1 − α)/(cα))(G_t − δE_tG_{t+1})` with the reset gap
  `G_t = c r_t − (k_t − f_t)`, `c = 1 − ε + η`, `κ = (1 − α)(1 − αβ)(γ + ϕ)/(αc)` and the explicit
  disturbance `u_π = calvoRem`.
* `calvo_iff_PC` (**necessity and sufficiency**): resetting optimally at every date is equivalent
  to (17.17) at every date with that `κ` and `u_π = calvoRem` (the reset gap solves
  `G_t = δE_tG_{t+1}`, whose only bounded solution is zero).
* Finite trees: `Tree.calvo_iff_PC`, the project's `FullModel.PC`.

`TidyR6CalvoBound` gives a single quadratic bound on the remainder and removes `Lr`;
`TidyR6CalvoAE` weakens the everywhere bounds to almost-sure ones.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6CalvoPC

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6CalvoReset TidyR6EulerIS TidyR6RotembergPC

/-- Cochrane (2023), p. 118: the parameters of the Calvo economy. -/
structure CalvoPar where
  /-- The probability that a price survives a period. -/
  α : ℝ
  /-- The discount factor. -/
  β : ℝ
  /-- The elasticity of demand. -/
  ε : ℝ
  /-- The inverse Frisch elasticity of the disutility of production. -/
  ϕ : ℝ
  /-- The CRRA coefficient. -/
  γ : ℝ
  /-- Steady-state output. -/
  Ybar : ℝ

namespace CalvoPar

variable (p : CalvoPar)

/-- Cochrane (2023), p. 118: the parameter restrictions and the steady state. -/
def Valid : Prop :=
  0 < p.α ∧ p.α < 1 ∧ 0 < p.β ∧ p.β < 1 ∧ 1 < p.ε ∧ 0 ≤ p.ϕ ∧ 0 < p.Ybar ∧
    p.ε * p.Ybar ^ (1 + p.ϕ) = (p.ε - 1) * p.Ybar ^ (1 - p.γ)

/-- Cochrane (2023), p. 118: discounting times survival, `δ = αβ`. -/
def δ : ℝ := p.α * p.β

/-- Cochrane (2023), p. 118: `η = ε(1 + ϕ)`. -/
def η : ℝ := p.ε * (1 + p.ϕ)

/-- Cochrane (2023), p. 118: `c = 1 − ε + η = 1 + εϕ`. -/
def c : ℝ := 1 - p.ε + p.η

/-- Cochrane (2023), eq. (17.17), p. 407: the Calvo slope
`κ = (1 − α)(1 − αβ)(γ + ϕ)/(α(1 + εϕ))`. -/
noncomputable def κ : ℝ := (1 - p.α) * (1 - p.δ) * (p.γ + p.ϕ) / (p.α * p.c)

/-- Cochrane (2023), p. 118: steady-state `F̄ = Ȳ^{1−γ}/(1 − δ)`. -/
noncomputable def Fbar : ℝ := p.Ybar ^ (1 - p.γ) / (1 - p.δ)

/-- Cochrane (2023), p. 118: steady-state `K̄ = Ȳ^{1+ϕ}/((1 + ϕ)(1 − δ))`. -/
noncomputable def Kbar : ℝ := p.Ybar ^ (1 + p.ϕ) / ((1 + p.ϕ) * (1 - p.δ))

variable {p}

/-- Cochrane (2023), p. 118: `0 < δ` (the upper bound is `Valid.δ_lt`). -/
theorem Valid.δ_pos (h : p.Valid) : 0 < p.δ := mul_pos h.1 h.2.2.1

/-- Cochrane (2023), p. 118: `δ < 1`. -/
theorem Valid.δ_lt (h : p.Valid) : p.δ < 1 := by
  have := mul_lt_mul'' h.2.1 h.2.2.2.1 h.1.le h.2.2.1.le
  simpa [δ] using this

/-- Cochrane (2023), p. 118: `c > 0`. -/
theorem Valid.c_pos (h : p.Valid) : 0 < p.c := by
  have := h.2.2.2.2.2.1
  have := h.2.2.2.2.1
  simp only [c, η]
  nlinarith

/-- Cochrane (2023), p. 118: `η > ε − 1`. -/
theorem Valid.η_gt (h : p.Valid) : p.ε - 1 < p.η := by
  have := h.c_pos
  simp only [c] at this
  linarith

/-- Cochrane (2023), p. 118: `F̄ > 0`. -/
theorem Valid.Fbar_pos (h : p.Valid) : 0 < p.Fbar :=
  div_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) (by linarith [h.δ_lt])

/-- Cochrane (2023), p. 118: `K̄ > 0`. -/
theorem Valid.Kbar_pos (h : p.Valid) : 0 < p.Kbar :=
  div_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _)
    (mul_pos (by linarith [h.2.2.2.2.2.1]) (by linarith [h.δ_lt]))

/-- Cochrane (2023), p. 118: at the steady state `ηK̄ = (ε − 1)F̄`, so the steady-state reset
price is the aggregate price. -/
theorem Valid.ss (h : p.Valid) : p.η * p.Kbar = (p.ε - 1) * p.Fbar := by
  have h1 : (0 : ℝ) < 1 + p.ϕ := by linarith [h.2.2.2.2.2.1]
  have h2 : (0 : ℝ) < 1 - p.δ := by linarith [h.δ_lt]
  have hss := h.2.2.2.2.2.2.2
  simp only [η, Kbar, Fbar]
  field_simp
  linear_combination hss

end CalvoPar

/-! ### The payoff weights and their discounted sums (pathwise) -/

variable {Ω : Type*}

/-- Cochrane (2023), p. 118: cumulative inflation from `t` to `t + k`, `p_{t+k} − p_t`. -/
def cumπ (π : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.range k, π (t + 1 + j) ω

/-- Cochrane (2023), p. 118: `p_{t+k+1} − p_t = π_{t+1} + (p_{t+1+k} − p_{t+1})`. -/
theorem cumπ_succ (π : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) :
    cumπ π t (k + 1) ω = π (t + 1) ω + cumπ π (t + 1) k ω := by
  simp only [cumπ, Finset.sum_range_succ', add_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  omega

/-- Cochrane (2023), p. 118: `|p_{t+k} − p_t| ≤ kL` when `|π| ≤ L`. -/
theorem abs_cumπ_le {π : ℕ → Ω → ℝ} {L : ℝ} (hπ : ∀ s ω, |π s ω| ≤ L) (t k : ℕ) (ω : Ω) :
    |cumπ π t k ω| ≤ k * L := by
  unfold cumπ
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hπ (t + 1 + j) ω).trans ?_
  simp

/-- Cochrane (2023), p. 118: the revenue weight `a_{t,k} = Ȳ^{1−γ}e^{(1−γ)x_{t+k} +
(ε−1)(p_{t+k} − p_t)}`. -/
noncomputable def aW (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) : ℝ :=
  p.Ybar ^ (1 - p.γ) * Real.exp ((1 - p.γ) * x (t + k) ω + (p.ε - 1) * cumπ π t k ω)

/-- Cochrane (2023), p. 118: the disutility weight `b_{t,k} = Ȳ^{1+ϕ}e^{(1+ϕ)x_{t+k} +
η(p_{t+k} − p_t)}/(1 + ϕ)`. -/
noncomputable def bW (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) : ℝ :=
  p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp ((1 + p.ϕ) * x (t + k) ω + p.η * cumπ π t k ω)

/-- Cochrane (2023), p. 118: `a_{t,k+1} = e^{(ε−1)π_{t+1}}a_{t+1,k}`. -/
theorem aW_succ (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) :
    aW p x π t (k + 1) ω = Real.exp ((p.ε - 1) * π (t + 1) ω) * aW p x π (t + 1) k ω := by
  simp only [aW, cumπ_succ, show t + (k + 1) = t + 1 + k by omega]
  rw [mul_left_comm, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 118: `b_{t,k+1} = e^{ηπ_{t+1}}b_{t+1,k}`. -/
theorem bW_succ (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) :
    bW p x π t (k + 1) ω = Real.exp (p.η * π (t + 1) ω) * bW p x π (t + 1) k ω := by
  simp only [bW, cumπ_succ, show t + (k + 1) = t + 1 + k by omega]
  rw [mul_left_comm, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 118: the discounted revenue weights `W_{A,t} = ∑_k δᵏa_{t,k}`. -/
noncomputable def wA (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑' k, p.δ ^ k * aW p x π t k ω

/-- Cochrane (2023), p. 118: the discounted disutility weights `W_{B,t} = ∑_k δᵏb_{t,k}`. -/
noncomputable def wB (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑' k, p.δ ^ k * bW p x π t k ω

/-- Cochrane (2023), p. 118: a nonnegative sequence dominated by a geometric one is summable,
and its sum lies between its first term and `C/(1 − ρ)`. -/
theorem geom_bounds {g : ℕ → ℝ} (h0 : ∀ k, 0 ≤ g k) {C ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hle : ∀ k, g k ≤ C * ρ ^ k) : Summable g ∧ g 0 ≤ ∑' k, g k ∧ ∑' k, g k ≤ C / (1 - ρ) := by
  have hg := (summable_geometric_of_lt_one hρ0 hρ).mul_left C
  have hs : Summable g := Summable.of_nonneg_of_le h0 hle hg
  refine ⟨hs, hs.le_tsum 0 fun j _ => h0 j, ?_⟩
  calc ∑' k, g k ≤ ∑' k, C * ρ ^ k := hs.tsum_le_tsum hle hg
    _ = C / (1 - ρ) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ, div_eq_mul_inv]

/-- Cochrane (2023), p. 118: output gap and inflation bounded by `L` everywhere. -/
def Bounded (x π : ℕ → Ω → ℝ) (L : ℝ) : Prop := 0 ≤ L ∧ ∀ t ω, |x t ω| ≤ L ∧ |π t ω| ≤ L

namespace CalvoPar

variable {p : CalvoPar}

/-- Cochrane (2023), p. 118: the lower bound `Ȳ^{1−γ}e^{−|1−γ|L}` of `W_A`. -/
noncomputable def loA (p : CalvoPar) (L : ℝ) : ℝ := p.Ybar ^ (1 - p.γ) * Real.exp (-(|1 - p.γ| * L))

/-- Cochrane (2023), p. 118: the upper bound of `W_A`. -/
noncomputable def hiA (p : CalvoPar) (L : ℝ) : ℝ :=
  p.Ybar ^ (1 - p.γ) * Real.exp (|1 - p.γ| * L) / (1 - p.δ * Real.exp ((p.ε - 1) * L))

/-- Cochrane (2023), p. 118: the lower bound of `W_B`. -/
noncomputable def loB (p : CalvoPar) (L : ℝ) : ℝ :=
  p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp (-((1 + p.ϕ) * L))

/-- Cochrane (2023), p. 118: the upper bound of `W_B`. -/
noncomputable def hiB (p : CalvoPar) (L : ℝ) : ℝ :=
  p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp ((1 + p.ϕ) * L) / (1 - p.δ * Real.exp (p.η * L))

/-- Cochrane (2023), p. 118: `δe^{(ε−1)L} ≤ δe^{ηL} < 1`. -/
theorem Valid.ρA_lt (h : p.Valid) {L : ℝ} (hL : 0 ≤ L) (hρ : p.δ * Real.exp (p.η * L) < 1) :
    p.δ * Real.exp ((p.ε - 1) * L) < 1 := by
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h.δ_pos.le) hρ
  exact mul_le_mul_of_nonneg_right h.η_gt.le hL

end CalvoPar

open CalvoPar

/-- Cochrane (2023), p. 118: the discounted revenue weights converge pathwise and lie in
`[loA, hiA]`. -/
theorem wA_bounds {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (t : ℕ) (ω : Ω) :
    Summable (fun k => p.δ ^ k * aW p x π t k ω) ∧ p.loA L ≤ wA p x π t ω ∧
      wA p x π t ω ≤ p.hiA L := by
  have hY := Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 (1 - p.γ)
  have hρA := h.ρA_lt hB.1 hρ
  have hε1 : 0 ≤ p.ε - 1 := by linarith [h.2.2.2.2.1]
  have hle : ∀ k, p.δ ^ k * aW p x π t k ω ≤ (p.Ybar ^ (1 - p.γ) * Real.exp (|1 - p.γ| * L)) *
      (p.δ * Real.exp ((p.ε - 1) * L)) ^ k := fun k => by
    have h1 := (hB.2 (t + k) ω).1
    have h2 := abs_cumπ_le (fun s ω => (hB.2 s ω).2) t k ω
    have he : Real.exp ((1 - p.γ) * x (t + k) ω + (p.ε - 1) * cumπ π t k ω) ≤
        Real.exp (|1 - p.γ| * L) * Real.exp ((p.ε - 1) * L) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 (add_le_add ?_ ?_)
      · calc (1 - p.γ) * x (t + k) ω ≤ |(1 - p.γ) * x (t + k) ω| := le_abs_self _
          _ = |1 - p.γ| * |x (t + k) ω| := abs_mul _ _
          _ ≤ |1 - p.γ| * L := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      · calc (p.ε - 1) * cumπ π t k ω ≤ (p.ε - 1) * (k * L) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hε1
          _ = k * ((p.ε - 1) * L) := by ring
    simp only [aW]
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left he hY.le
    have hd := pow_nonneg h.δ_pos.le k
    nlinarith [mul_le_mul_of_nonneg_left this hd]
  have h0 : ∀ k, 0 ≤ p.δ ^ k * aW p x π t k ω := fun k =>
    mul_nonneg (pow_nonneg h.δ_pos.le k) (mul_nonneg hY.le (Real.exp_pos _).le)
  obtain ⟨hs, hlo, hhi⟩ := geom_bounds h0 (mul_nonneg h.δ_pos.le (Real.exp_pos _).le) hρA hle
  refine ⟨hs, le_trans ?_ hlo, hhi⟩
  simp only [pow_zero, one_mul, aW, add_zero, cumπ, Finset.range_zero, Finset.sum_empty,
    mul_zero, loA]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hY.le
  have h1 := (hB.2 t ω).1
  have : |(1 - p.γ) * x t ω| ≤ |1 - p.γ| * L := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  linarith [neg_abs_le ((1 - p.γ) * x t ω)]

/-- Cochrane (2023), p. 118: the discounted disutility weights converge pathwise and lie in
`[loB, hiB]`. -/
theorem wB_bounds {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (t : ℕ) (ω : Ω) :
    Summable (fun k => p.δ ^ k * bW p x π t k ω) ∧ p.loB L ≤ wB p x π t ω ∧
      wB p x π t ω ≤ p.hiB L := by
  have h1ϕ : (0 : ℝ) < 1 + p.ϕ := by linarith [h.2.2.2.2.2.1]
  have hY : 0 < p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) :=
    div_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) h1ϕ
  have hη0 : 0 ≤ p.η := by have := h.η_gt; linarith [h.2.2.2.2.1]
  have hle : ∀ k, p.δ ^ k * bW p x π t k ω ≤
      (p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp ((1 + p.ϕ) * L)) *
        (p.δ * Real.exp (p.η * L)) ^ k := fun k => by
    have h1 := (hB.2 (t + k) ω).1
    have h2 := abs_cumπ_le (fun s ω => (hB.2 s ω).2) t k ω
    have he : Real.exp ((1 + p.ϕ) * x (t + k) ω + p.η * cumπ π t k ω) ≤
        Real.exp ((1 + p.ϕ) * L) * Real.exp (p.η * L) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) h1ϕ.le
      · calc p.η * cumπ π t k ω ≤ p.η * (k * L) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hη0
          _ = k * (p.η * L) := by ring
    simp only [bW]
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left he hY.le
    have hd := pow_nonneg h.δ_pos.le k
    nlinarith [mul_le_mul_of_nonneg_left this hd]
  have h0 : ∀ k, 0 ≤ p.δ ^ k * bW p x π t k ω := fun k =>
    mul_nonneg (pow_nonneg h.δ_pos.le k) (mul_nonneg hY.le (Real.exp_pos _).le)
  obtain ⟨hs, hlo, hhi⟩ := geom_bounds h0 (mul_nonneg h.δ_pos.le (Real.exp_pos _).le) hρ hle
  refine ⟨hs, le_trans ?_ hlo, hhi⟩
  simp only [pow_zero, one_mul, bW, add_zero, cumπ, Finset.range_zero, Finset.sum_empty,
    mul_zero, loB]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hY.le
  have h1 := (hB.2 t ω).1
  have : |(1 + p.ϕ) * x t ω| ≤ (1 + p.ϕ) * L := by
    rw [abs_mul, abs_of_pos h1ϕ]; exact mul_le_mul_of_nonneg_left h1 h1ϕ.le
  linarith [neg_abs_le ((1 + p.ϕ) * x t ω)]

/-- Cochrane (2023), p. 118: the recursion `W_{A,t} = a_{t,0} + δe^{(ε−1)π_{t+1}}W_{A,t+1}`. -/
theorem wA_succ {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (t : ℕ) (ω : Ω) :
    wA p x π t ω = aW p x π t 0 ω +
      p.δ * (Real.exp ((p.ε - 1) * π (t + 1) ω) * wA p x π (t + 1) ω) := by
  rw [wA, (wA_bounds h hB hρ t ω).1.tsum_eq_zero_add, wA, pow_zero, one_mul,
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [aW_succ, pow_succ]
  ring

/-- Cochrane (2023), p. 118: the recursion `W_{B,t} = b_{t,0} + δe^{ηπ_{t+1}}W_{B,t+1}`. -/
theorem wB_succ {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (t : ℕ) (ω : Ω) :
    wB p x π t ω = bW p x π t 0 ω +
      p.δ * (Real.exp (p.η * π (t + 1) ω) * wB p x π (t + 1) ω) := by
  rw [wB, (wB_bounds h hB hρ t ω).1.tsum_eq_zero_add, wB, pow_zero, one_mul,
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [bW_succ, pow_succ]
  ring

/-! ### Forecasts of the discounted sums -/

variable [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 118 (law of iterated expectations for a forward recursion): if
`W_t = w_t + δm_{t+1}W_{t+1}` pathwise, with `w_t` known at `t` and integrable, `m_{t+1}` known at
`t + 1` and bounded, and `W` integrable, then `E_tW_t = w_t + δE_t[m_{t+1}E_{t+1}W_{t+1}]` almost
surely. -/
theorem E_rec {δ : ℝ} {W w m : ℕ → Ω → ℝ} {t : ℕ}
    (hrec : ∀ ω, W t ω = w t ω + δ * (m (t + 1) ω * W (t + 1) ω))
    (hw : StronglyMeasurable[S.𝓕 t] (w t)) (hwi : Integrable (w t) S.μ)
    (hm : StronglyMeasurable[S.𝓕 (t + 1)] (m (t + 1))) {M : ℝ}
    (hmM : ∀ᵐ ω ∂S.μ, |m (t + 1) ω| ≤ M) (hWi : Integrable (W (t + 1)) S.μ) :
    S.E t (W t) =ᵐ[S.μ] fun ω => w t ω + δ * S.E t (fun ω => m (t + 1) ω *
      S.E (t + 1) (W (t + 1)) ω) ω := by
  have hgi : Integrable (fun ω => m (t + 1) ω * W (t + 1) ω) S.μ :=
    hWi.bdd_mul (hm.mono (S.𝓕.le _)).aestronglyMeasurable
      (hmM.mono fun ω h => by rwa [Real.norm_eq_abs])
  have e : W t = w t + δ • fun ω => m (t + 1) ω * W (t + 1) ω := by
    funext ω
    simp [hrec ω]
  have hpo := S.E_pullOut hm hmM hWi
  have htow := S.E_tower (Nat.le_succ t) (fun ω => m (t + 1) ω * W (t + 1) ω)
  have hc := S.E_congr hpo t
  rw [e]
  filter_upwards [S.E_add hwi (hgi.smul δ) t, S.E_smul δ (fun ω => m (t + 1) ω * W (t + 1) ω) t,
    htow, hc] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, S.E_of_stronglyMeasurable hw hwi, h2, Pi.smul_apply, smul_eq_mul, ← h3]
  congr 2

/-- Cochrane (2023), p. 118: the weights are measurable. -/
theorem aW_meas {p : CalvoPar} {x π : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t k : ℕ) : Measurable (aW p x π t k) := by
  have hc : Measurable (cumπ π t k) :=
    Finset.measurable_fun_sum _ fun j _ => ((hπ (t + 1 + j)).mono (S.𝓕.le _)).measurable
  exact (Real.continuous_exp.measurable.comp ((((hx (t + k)).mono (S.𝓕.le _)).measurable.const_mul
    _).add (hc.const_mul _))).const_mul _

/-- Cochrane (2023), p. 118: the weights are measurable. -/
theorem bW_meas {p : CalvoPar} {x π : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t k : ℕ) : Measurable (bW p x π t k) := by
  have hc : Measurable (cumπ π t k) :=
    Finset.measurable_fun_sum _ fun j _ => ((hπ (t + 1 + j)).mono (S.𝓕.le _)).measurable
  exact (Real.continuous_exp.measurable.comp ((((hx (t + k)).mono (S.𝓕.le _)).measurable.const_mul
    _).add (hc.const_mul _))).const_mul _

/-- Cochrane (2023), p. 118: a pathwise-summable series of measurable functions has a measurable
sum. -/
theorem measurable_tsum' {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (hs : ∀ ω, Summable fun k => g k ω) : Measurable fun ω => ∑' k, g k ω :=
  measurable_of_tendsto_metrizable (f := fun N ω => ∑ k ∈ Finset.range N, g k ω)
    (fun _ => Finset.measurable_fun_sum _ fun k _ => hg k)
    (tendsto_pi_nhds.2 fun ω => (hs ω).hasSum.tendsto_sum_nat)

/-- Cochrane (2023), p. 118: `W_A` is integrable. -/
theorem wA_integrable {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) : Integrable (wA p x π t) S.μ := by
  refine Integrable.of_bound (measurable_tsum' (fun k => (aW_meas hx hπ t k).const_mul _)
    fun ω => (wA_bounds h hB hρ t ω).1).aestronglyMeasurable (max |p.loA L| |p.hiA L|)
    (Eventually.of_forall fun ω => ?_)
  obtain ⟨-, h1, h2⟩ := wA_bounds h hB hρ t ω
  rw [Real.norm_eq_abs]
  exact abs_le_max_abs_abs h1 h2

/-- Cochrane (2023), p. 118: `W_B` is integrable. -/
theorem wB_integrable {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) : Integrable (wB p x π t) S.μ := by
  refine Integrable.of_bound (measurable_tsum' (fun k => (bW_meas hx hπ t k).const_mul _)
    fun ω => (wB_bounds h hB hρ t ω).1).aestronglyMeasurable (max |p.loB L| |p.hiB L|)
    (Eventually.of_forall fun ω => ?_)
  obtain ⟨-, h1, h2⟩ := wB_bounds h hB hρ t ω
  rw [Real.norm_eq_abs]
  exact abs_le_max_abs_abs h1 h2

variable (S) in
/-- Cochrane (2023), p. 118: `F_t = E_tW_{A,t}`. -/
noncomputable def Fc (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := S.E t (wA p x π t)

variable (S) in
/-- Cochrane (2023), p. 118: `K_t = E_tW_{B,t}`. -/
noncomputable def Kc (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := S.E t (wB p x π t)

/-- Cochrane (2023), p. 118: forecasts of a variable in `[lo, hi]` lie in `[lo, hi]`. -/
theorem E_mem {X : Ω → ℝ} (hX : Integrable X S.μ) {lo hi : ℝ} (h : ∀ ω, lo ≤ X ω ∧ X ω ≤ hi)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, lo ≤ S.E t X ω ∧ S.E t X ω ≤ hi := by
  have h1 := S.E_mono (integrable_const lo) hX (Eventually.of_forall fun ω => (h ω).1) t
  have h2 := S.E_mono hX (integrable_const hi) (Eventually.of_forall fun ω => (h ω).2) t
  rw [S.E_const] at h1 h2
  filter_upwards [h1, h2] with ω a b
  exact ⟨a, b⟩

/-- Cochrane (2023), p. 118: the current weights are known at `t`. -/
theorem aW0_sm {p : CalvoPar} {x π : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (aW p x π t 0) := by
  have e : aW p x π t 0 = fun ω => p.Ybar ^ (1 - p.γ) * Real.exp ((1 - p.γ) * x t ω) := by
    funext ω; simp [aW, cumπ]
  rw [e]
  exact ((Real.continuous_exp.measurable.comp ((hx t).measurable.const_mul _)).const_mul
    _).stronglyMeasurable

/-- Cochrane (2023), p. 118: the current weights are known at `t`. -/
theorem bW0_sm {p : CalvoPar} {x π : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (bW p x π t 0) := by
  have e : bW p x π t 0 =
      fun ω => p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp ((1 + p.ϕ) * x t ω) := by
    funext ω; simp [bW, cumπ]
  rw [e]
  exact ((Real.continuous_exp.measurable.comp ((hx t).measurable.const_mul _)).const_mul
    _).stronglyMeasurable

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: `|e^{cπ_t}| ≤ e^{|c|L}`. -/
theorem abs_exp_le {π : ℕ → Ω → ℝ} {L : ℝ} (hπ : ∀ s ω, |π s ω| ≤ L) (c : ℝ) (s : ℕ) (ω : Ω) :
    |Real.exp (c * π s ω)| ≤ Real.exp (|c| * L) := by
  rw [abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hπ s ω) (abs_nonneg _)

/-- Cochrane (2023), p. 118: a bounded measurable function is integrable. -/
theorem integrable_of_bound' {f : Ω → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ ω, |f ω| ≤ M) :
    Integrable f S.μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hM ω)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: `|a_{t,0}| ≤ Ȳ^{1−γ}e^{|1−γ|L}`. -/
theorem aW0_abs_le {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (t : ℕ) (ω : Ω) :
    |aW p x π t 0 ω| ≤ p.Ybar ^ (1 - p.γ) * Real.exp (|1 - p.γ| * L) := by
  have hY := Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 (1 - p.γ)
  simp only [aW, cumπ, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
  rw [abs_of_pos (mul_pos hY (Real.exp_pos _))]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((le_abs_self _).trans ?_)) hY.le
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB.2 t ω).1 (abs_nonneg _)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: `|b_{t,0}| ≤ Ȳ^{1+ϕ}e^{(1+ϕ)L}/(1 + ϕ)`. -/
theorem bW0_abs_le {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (t : ℕ) (ω : Ω) :
    |bW p x π t 0 ω| ≤ p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp ((1 + p.ϕ) * L) := by
  have h1ϕ : (0 : ℝ) < 1 + p.ϕ := by linarith [h.2.2.2.2.2.1]
  have hY : 0 < p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) :=
    div_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) h1ϕ
  simp only [bW, cumπ, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
  rw [abs_of_pos (mul_pos hY (Real.exp_pos _))]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((le_abs_self _).trans ?_)) hY.le
  rw [abs_mul, abs_of_pos h1ϕ]
  exact mul_le_mul_of_nonneg_left (hB.2 t ω).1 h1ϕ.le

/-- Cochrane (2023), p. 118: the exact recursion `F_t = a_{t,0} + δE_t[e^{(ε−1)π_{t+1}}F_{t+1}]`. -/
theorem Fc_rec {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    Fc S p x π t =ᵐ[S.μ] fun ω => aW p x π t 0 ω + p.δ * S.E t (fun ω =>
      Real.exp ((p.ε - 1) * π (t + 1) ω) * Fc S p x π (t + 1) ω) ω :=
  E_rec (W := wA p x π) (w := fun s => aW p x π s 0)
    (m := fun s ω => Real.exp ((p.ε - 1) * π s ω)) (wA_succ h hB hρ t) (aW0_sm hx t)
    (integrable_of_bound' (aW_meas hx hπ t 0) (aW0_abs_le h hB t))
    ((Real.continuous_exp.measurable.comp
      ((hπ (t + 1)).measurable.const_mul _)).stronglyMeasurable)
    (Eventually.of_forall fun ω => abs_exp_le (fun s ω => (hB.2 s ω).2) _ (t + 1) ω)
    (wA_integrable h hB hρ hx hπ (t + 1))

/-- Cochrane (2023), p. 118: the exact recursion `K_t = b_{t,0} + δE_t[e^{ηπ_{t+1}}K_{t+1}]`. -/
theorem Kc_rec {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    Kc S p x π t =ᵐ[S.μ] fun ω => bW p x π t 0 ω + p.δ * S.E t (fun ω =>
      Real.exp (p.η * π (t + 1) ω) * Kc S p x π (t + 1) ω) ω :=
  E_rec (W := wB p x π) (w := fun s => bW p x π s 0)
    (m := fun s ω => Real.exp (p.η * π s ω)) (wB_succ h hB hρ t) (bW0_sm hx t)
    (integrable_of_bound' (bW_meas hx hπ t 0) (bW0_abs_le h hB t))
    ((Real.continuous_exp.measurable.comp
      ((hπ (t + 1)).measurable.const_mul _)).stronglyMeasurable)
    (Eventually.of_forall fun ω => abs_exp_le (fun s ω => (hB.2 s ω).2) _ (t + 1) ω)
    (wB_integrable h hB hρ hx hπ (t + 1))

/-! ### Logs and the explicit remainders of the recursions -/

/-- Cochrane (2023), p. 118: `F_t ∈ [loA, hiA]` almost surely. -/
theorem Fc_mem {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, p.loA L ≤ Fc S p x π t ω ∧ Fc S p x π t ω ≤ p.hiA L :=
  E_mem (wA_integrable h hB hρ hx hπ t) (fun ω => (wA_bounds h hB hρ t ω).2) t

/-- Cochrane (2023), p. 118: `K_t ∈ [loB, hiB]` almost surely. -/
theorem Kc_mem {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, p.loB L ≤ Kc S p x π t ω ∧ Kc S p x π t ω ≤ p.hiB L :=
  E_mem (wB_integrable h hB hρ hx hπ t) (fun ω => (wB_bounds h hB hρ t ω).2) t

/-- Cochrane (2023), p. 118: `loA > 0`. -/
theorem loA_pos {p : CalvoPar} (h : p.Valid) (L : ℝ) : 0 < p.loA L :=
  mul_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) (Real.exp_pos _)

/-- Cochrane (2023), p. 118: `loB > 0`. -/
theorem loB_pos {p : CalvoPar} (h : p.Valid) (L : ℝ) : 0 < p.loB L :=
  mul_pos (div_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) (by linarith [h.2.2.2.2.2.1]))
    (Real.exp_pos _)

variable (S) in
/-- Cochrane (2023), p. 118: `f_t = log(F_t/F̄)`. -/
noncomputable def fc (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.log (Fc S p x π t ω / p.Fbar)

variable (S) in
/-- Cochrane (2023), p. 118: `k_t = log(K_t/K̄)`. -/
noncomputable def kc (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.log (Kc S p x π t ω / p.Kbar)

/-- Cochrane (2023), p. 118: `f_t` is known at `t`. -/
theorem fc_sm (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (fc S p x π t) :=
  ((S.stronglyMeasurable_E t _).measurable.div_const _).log.stronglyMeasurable

/-- Cochrane (2023), p. 118: `k_t` is known at `t`. -/
theorem kc_sm (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (kc S p x π t) :=
  ((S.stronglyMeasurable_E t _).measurable.div_const _).log.stronglyMeasurable

/-- Cochrane (2023), p. 118: `f_t` is essentially bounded, uniformly in `t`. -/
theorem fc_bdd {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |fc S p x π t ω| ≤
      max |Real.log (p.loA L / p.Fbar)| |Real.log (p.hiA L / p.Fbar)| := by
  filter_upwards [Fc_mem h hB hρ hx hπ t] with ω hω
  have hF := h.Fbar_pos
  have h0 : 0 < p.loA L / p.Fbar := div_pos (loA_pos h L) hF
  have h1 : Real.log (p.loA L / p.Fbar) ≤ fc S p x π t ω :=
    Real.log_le_log h0 (div_le_div_of_nonneg_right hω.1 hF.le)
  have h2 : fc S p x π t ω ≤ Real.log (p.hiA L / p.Fbar) :=
    Real.log_le_log (div_pos ((loA_pos h L).trans_le hω.1) hF)
      (div_le_div_of_nonneg_right hω.2 hF.le)
  exact abs_le_max_abs_abs h1 h2

/-- Cochrane (2023), p. 118: `k_t` is essentially bounded, uniformly in `t`. -/
theorem kc_bdd {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |kc S p x π t ω| ≤
      max |Real.log (p.loB L / p.Kbar)| |Real.log (p.hiB L / p.Kbar)| := by
  filter_upwards [Kc_mem h hB hρ hx hπ t] with ω hω
  have hK := h.Kbar_pos
  have h0 : 0 < p.loB L / p.Kbar := div_pos (loB_pos h L) hK
  have h1 : Real.log (p.loB L / p.Kbar) ≤ kc S p x π t ω :=
    Real.log_le_log h0 (div_le_div_of_nonneg_right hω.1 hK.le)
  have h2 : kc S p x π t ω ≤ Real.log (p.hiB L / p.Kbar) :=
    Real.log_le_log (div_pos ((loB_pos h L).trans_le hω.1) hK)
      (div_le_div_of_nonneg_right hω.2 hK.le)
  exact abs_le_max_abs_abs h1 h2

/-- Cochrane (2023), p. 118: `e^{f_t} = F_t/F̄` almost surely. -/
theorem fc_exp {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Real.exp (fc S p x π t ω) = Fc S p x π t ω / p.Fbar := by
  filter_upwards [Fc_mem h hB hρ hx hπ t] with ω hω
  exact Real.exp_log (div_pos ((loA_pos h L).trans_le hω.1) h.Fbar_pos)

/-- Cochrane (2023), p. 118: `e^{k_t} = K_t/K̄` almost surely. -/
theorem kc_exp {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Real.exp (kc S p x π t ω) = Kc S p x π t ω / p.Kbar := by
  filter_upwards [Kc_mem h hB hρ hx hπ t] with ω hω
  exact Real.exp_log (div_pos ((loB_pos h L).trans_le hω.1) h.Kbar_pos)

/-- Cochrane (2023), p. 118: the exact recursion in logs,
`e^{f_t} = (1 − δ)e^{(1−γ)x_t} + δE_t e^{(ε−1)π_{t+1} + f_{t+1}}`. -/
theorem fc_rec {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Real.exp (fc S p x π t ω) = (1 - p.δ) * Real.exp ((1 - p.γ) * x t ω) +
      p.δ * S.E t (fun ω => Real.exp ((p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω)) ω := by
  have hF := h.Fbar_pos
  have hc : (fun ω => Real.exp ((p.ε - 1) * π (t + 1) ω) * Fc S p x π (t + 1) ω) =ᵐ[S.μ]
      p.Fbar • fun ω => Real.exp ((p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω) := by
    filter_upwards [fc_exp h hB hρ hx hπ (t + 1)] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.exp_add, hω]
    field_simp
  have hE := (S.E_congr hc t).trans (S.E_smul _ _ t)
  filter_upwards [Fc_rec h hB hρ hx hπ t, fc_exp h hB hρ hx hπ t, hE] with ω h1 h2 h3
  rw [h2, h1, h3]
  simp only [Pi.smul_apply, smul_eq_mul, aW, cumπ, Finset.range_zero, Finset.sum_empty,
    mul_zero, add_zero, CalvoPar.Fbar]
  have hY := Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 (1 - p.γ)
  have hd : 1 - p.δ ≠ 0 := by linarith [h.δ_lt]
  field_simp

/-- Cochrane (2023), p. 118: the exact recursion in logs,
`e^{k_t} = (1 − δ)e^{(1+ϕ)x_t} + δE_t e^{ηπ_{t+1} + k_{t+1}}`. -/
theorem kc_rec {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Real.exp (kc S p x π t ω) = (1 - p.δ) * Real.exp ((1 + p.ϕ) * x t ω) +
      p.δ * S.E t (fun ω => Real.exp (p.η * π (t + 1) ω + kc S p x π (t + 1) ω)) ω := by
  have hK := h.Kbar_pos
  have hc : (fun ω => Real.exp (p.η * π (t + 1) ω) * Kc S p x π (t + 1) ω) =ᵐ[S.μ]
      p.Kbar • fun ω => Real.exp (p.η * π (t + 1) ω + kc S p x π (t + 1) ω) := by
    filter_upwards [kc_exp h hB hρ hx hπ (t + 1)] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.exp_add, hω]
    field_simp
  have hE := (S.E_congr hc t).trans (S.E_smul _ _ t)
  filter_upwards [Kc_rec h hB hρ hx hπ t, kc_exp h hB hρ hx hπ t, hE] with ω h1 h2 h3
  rw [h2, h1, h3]
  simp only [Pi.smul_apply, smul_eq_mul, bW, cumπ, Finset.range_zero, Finset.sum_empty,
    mul_zero, add_zero, CalvoPar.Kbar]
  have hY := Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 (1 + p.ϕ)
  have hd : 1 - p.δ ≠ 0 := by linarith [h.δ_lt]
  have h1ϕ : 1 + p.ϕ ≠ 0 := by linarith [h.2.2.2.2.2.1]
  field_simp

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the pointwise second-order bounds for a log-linearised recursion. If
`e^f = (1 − δ)e^a + δE`, `E = R + W + 1` with `R ≥ 0` and `0 ≤ δ ≤ 1`, then
`−(e^f − 1)²e^{−f} ≤ f − (1 − δ)a − δW ≤ (1 − δ)expRem(a) + δR`. -/
theorem log_bounds_pt {f a W E R δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hy : Real.exp f = (1 - δ) * Real.exp a + δ * E) (hE : E = R + W + 1) (hR : 0 ≤ R) :
    -(Real.exp f - 1) ^ 2 * Real.exp (-f) ≤ f - (1 - δ) * a - δ * W ∧
      f - (1 - δ) * a - δ * W ≤ (1 - δ) * expRem a + δ * R := by
  have hea : Real.exp a = expRem a + a + 1 := by simp [expRem]
  have hy1 : Real.exp f - 1 = (1 - δ) * (expRem a + a) + δ * (R + W) := by
    rw [hy, hE, hea]; ring
  have hra := expRem_nonneg a
  have hpos := Real.exp_pos f
  constructor
  · have hl : 1 - Real.exp (-f) ≤ f := by
      have := Real.add_one_le_exp (-f)
      linarith
    have hlin : (1 - δ) * a + δ * W ≤ Real.exp f - 1 := by
      rw [hy1]; nlinarith [mul_nonneg (sub_nonneg.2 hδ1) hra, mul_nonneg hδ0 hR]
    have hinv : Real.exp (-f) * Real.exp f = 1 := by rw [← Real.exp_add]; simp
    have key : -(Real.exp f - 1) ^ 2 * Real.exp (-f) =
        (1 - Real.exp (-f)) - (Real.exp f - 1) := by
      linear_combination (-(Real.exp f) + 2) * hinv
    rw [key]
    linarith
  · have hu : f ≤ Real.exp f - 1 := by linarith [Real.add_one_le_exp f]
    rw [hy1] at hu
    linarith

/-- Cochrane (2023), eq. (17.17), p. 407: the explicit remainder of the log-linearised `F`
recursion, `R^F_t = f_t − (1 − δ)(1 − γ)x_t − δE_t[(ε − 1)π_{t+1} + f_{t+1}]`. -/
noncomputable def RF (S : MeasExpectationSystem Ω) (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  fc S p x π t ω - (1 - p.δ) * ((1 - p.γ) * x t ω) -
    p.δ * S.E t (fun ω => (p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω) ω

/-- Cochrane (2023), eq. (17.17), p. 407: the explicit remainder of the log-linearised `K`
recursion, `R^K_t = k_t − (1 − δ)(1 + ϕ)x_t − δE_t[ηπ_{t+1} + k_{t+1}]`. -/
noncomputable def RK (S : MeasExpectationSystem Ω) (p : CalvoPar) (x π : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  kc S p x π t ω - (1 - p.δ) * ((1 + p.ϕ) * x t ω) -
    p.δ * S.E t (fun ω => p.η * π (t + 1) ω + kc S p x π (t + 1) ω) ω

/-- Cochrane (2023), p. 118: integrability of a bounded variable known at some date. -/
theorem integrable_sm {s : ℕ} {f : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 s] f) {M : ℝ}
    (hM : ∀ᵐ ω ∂S.μ, |f ω| ≤ M) : Integrable f S.μ :=
  Integrable.of_bound (hf.mono (S.𝓕.le s)).aestronglyMeasurable M
    (hM.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), p. 118: **the remainder `R^F` is second order**: almost surely
`−(e^{f_t} − 1)²e^{−f_t} ≤ R^F_t ≤ (1 − δ)expRem((1 − γ)x_t) +
δE_t expRem((ε − 1)π_{t+1} + f_{t+1})`. -/
theorem rF_bounds {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, -(Real.exp (fc S p x π t ω) - 1) ^ 2 * Real.exp (-fc S p x π t ω) ≤
        RF S p x π t ω ∧
      RF S p x π t ω ≤ (1 - p.δ) * expRem ((1 - p.γ) * x t ω) +
        p.δ * S.E t (fun ω => expRem ((p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω)) ω := by
  set w : Ω → ℝ := fun ω => (p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω with hw
  have hwm : StronglyMeasurable[S.𝓕 (t + 1)] w :=
    (((hπ (t + 1)).measurable.const_mul _).add (fc_sm p x π (t + 1)).measurable).stronglyMeasurable
  obtain ⟨M, hM⟩ : BddAt S w := by
    have := ((BddAt.const (S := S) (p.ε - 1)).mul (⟨L, Eventually.of_forall fun ω =>
      (hB.2 (t + 1) ω).2⟩ : BddAt S (π (t + 1)))).add
      ⟨_, fc_bdd h hB hρ hx hπ (t + 1)⟩
    simpa [hw] using this
  have hwi : Integrable w S.μ := integrable_sm hwm hM
  obtain ⟨M2, hM2⟩ := BddAt.comp (v := expRem) (by unfold expRem; fun_prop) ⟨M, hM⟩
  have hRi : Integrable (fun ω => expRem (w ω)) S.μ :=
    integrable_sm (s := t + 1) (((by unfold expRem; fun_prop : Continuous expRem).measurable.comp
      hwm.measurable).stronglyMeasurable) hM2
  have hexp : (fun ω => Real.exp (w ω)) = ((fun ω => expRem (w ω)) + w) + fun _ => 1 := by
    funext ω; simp [expRem]
  have hE : S.E t (fun ω => Real.exp (w ω)) =ᵐ[S.μ]
      fun ω => S.E t (fun ω => expRem (w ω)) ω + S.E t w ω + 1 := by
    rw [hexp]
    filter_upwards [S.E_add (hRi.add hwi) (integrable_const 1) t, S.E_add hRi hwi t]
      with ω h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply, S.E_const]
  have hR0 := S.E_mono (integrable_const 0) hRi
    (Eventually.of_forall fun ω => expRem_nonneg (w ω)) t
  rw [S.E_const] at hR0
  filter_upwards [fc_rec h hB hρ hx hπ t, hE, hR0] with ω h1 h2 h3
  exact log_bounds_pt h.δ_pos.le h.δ_lt.le h1 h2 h3

/-- Cochrane (2023), p. 118: **the remainder `R^K` is second order**: almost surely
`−(e^{k_t} − 1)²e^{−k_t} ≤ R^K_t ≤ (1 − δ)expRem((1 + ϕ)x_t) +
δE_t expRem(ηπ_{t+1} + k_{t+1})`. -/
theorem rK_bounds {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, -(Real.exp (kc S p x π t ω) - 1) ^ 2 * Real.exp (-kc S p x π t ω) ≤
        RK S p x π t ω ∧
      RK S p x π t ω ≤ (1 - p.δ) * expRem ((1 + p.ϕ) * x t ω) +
        p.δ * S.E t (fun ω => expRem (p.η * π (t + 1) ω + kc S p x π (t + 1) ω)) ω := by
  set w : Ω → ℝ := fun ω => p.η * π (t + 1) ω + kc S p x π (t + 1) ω with hw
  have hwm : StronglyMeasurable[S.𝓕 (t + 1)] w :=
    (((hπ (t + 1)).measurable.const_mul _).add (kc_sm p x π (t + 1)).measurable).stronglyMeasurable
  obtain ⟨M, hM⟩ : BddAt S w := by
    have := ((BddAt.const (S := S) p.η).mul (⟨L, Eventually.of_forall fun ω =>
      (hB.2 (t + 1) ω).2⟩ : BddAt S (π (t + 1)))).add
      ⟨_, kc_bdd h hB hρ hx hπ (t + 1)⟩
    simpa [hw] using this
  have hwi : Integrable w S.μ := integrable_sm hwm hM
  obtain ⟨M2, hM2⟩ := BddAt.comp (v := expRem) (by unfold expRem; fun_prop) ⟨M, hM⟩
  have hRi : Integrable (fun ω => expRem (w ω)) S.μ :=
    integrable_sm (s := t + 1) (((by unfold expRem; fun_prop : Continuous expRem).measurable.comp
      hwm.measurable).stronglyMeasurable) hM2
  have hexp : (fun ω => Real.exp (w ω)) = ((fun ω => expRem (w ω)) + w) + fun _ => 1 := by
    funext ω; simp [expRem]
  have hE : S.E t (fun ω => Real.exp (w ω)) =ᵐ[S.μ]
      fun ω => S.E t (fun ω => expRem (w ω)) ω + S.E t w ω + 1 := by
    rw [hexp]
    filter_upwards [S.E_add (hRi.add hwi) (integrable_const 1) t, S.E_add hRi hwi t]
      with ω h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply, S.E_const]
  have hR0 := S.E_mono (integrable_const 0) hRi
    (Eventually.of_forall fun ω => expRem_nonneg (w ω)) t
  rw [S.E_const] at hR0
  filter_upwards [kc_rec h hB hρ hx hπ t, hE, hR0] with ω h1 h2 h3
  exact log_bounds_pt h.δ_pos.le h.δ_lt.le h1 h2 h3

/-! ### The reset gap, the index and the Phillips curve -/

/-- Cochrane (2023), p. 421: the Calvo price index in logs at every date,
`αe^{(ε−1)π_t} + (1 − α)e^{(1−ε)r_t} = 1` (`TidyR6CalvoReset.index_eq_of_cohort`). -/
def Index (p : CalvoPar) (π r : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, p.α * Real.exp ((p.ε - 1) * π t ω) + (1 - p.α) * Real.exp ((1 - p.ε) * r t ω) = 1

/-- Cochrane (2023), p. 421: the remainder of the log-linearised index,
`R^I_t = αe^{(ε−1)π_t} + (1 − α)e^{(1−ε)r_t} − 1 − α(ε − 1)π_t − (1 − α)(1 − ε)r_t`. -/
noncomputable def RI (p : CalvoPar) (π r : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  p.α * Real.exp ((p.ε - 1) * π t ω) + (1 - p.α) * Real.exp ((1 - p.ε) * r t ω) - 1 -
    (p.α * ((p.ε - 1) * π t ω) + (1 - p.α) * ((1 - p.ε) * r t ω))

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 421: `R^I = αexpRem((ε − 1)π) + (1 − α)expRem((1 − ε)r)`, second order. -/
theorem RI_eq (p : CalvoPar) (π r : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    RI p π r t ω = p.α * expRem ((p.ε - 1) * π t ω) + (1 - p.α) * expRem ((1 - p.ε) * r t ω) := by
  simp only [RI, expRem]
  ring

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 421: by the index, `(1 − α)(ε − 1)r_t = α(ε − 1)π_t + R^I_t`. -/
theorem r_of_index {p : CalvoPar} {π r : ℕ → Ω → ℝ} (hI : Index p π r) (t : ℕ) (ω : Ω) :
    (1 - p.α) * (p.ε - 1) * r t ω = p.α * (p.ε - 1) * π t ω + RI p π r t ω := by
  have := hI t ω
  simp only [RI]
  linarith

/-- Cochrane (2023), p. 118: the reset gap `G_t = c r_t − (k_t − f_t)`. -/
noncomputable def gap (S : MeasExpectationSystem Ω) (p : CalvoPar) (x π r : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  p.c * r t ω - (kc S p x π t ω - fc S p x π t ω)

/-- Cochrane (2023), eq. (17.17), p. 407: the explicit Calvo disturbance
`u_{π,t} = ((1 − α)/(cα))(R^K_t − R^F_t) + (β/(ε − 1))E_tR^I_{t+1} − R^I_t/(α(ε − 1))`. -/
noncomputable def calvoRem (S : MeasExpectationSystem Ω) (p : CalvoPar) (x π r : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  (1 - p.α) / (p.c * p.α) * (RK S p x π t ω - RF S p x π t ω) +
    p.β / (p.ε - 1) * S.E t (RI p π r (t + 1)) ω - RI p π r t ω / (p.α * (p.ε - 1))

/-- Cochrane (2023), p. 421: the index remainder is integrable. -/
theorem RI_integrable {p : CalvoPar} {π r : ℕ → Ω → ℝ} {L Lr : ℝ} (hπ : StronglyAdapted S.𝓕 π)
    (hr : StronglyAdapted S.𝓕 r) (hπb : ∀ s ω, |π s ω| ≤ L) (hrb : ∀ s ω, |r s ω| ≤ Lr)
    (s : ℕ) : Integrable (RI p π r s) S.μ := by
  have mπ : Measurable (π s) := ((hπ s).mono (S.𝓕.le s)).measurable
  have mr : Measurable (r s) := ((hr s).mono (S.𝓕.le s)).measurable
  have iπ : Integrable (π s) S.μ := integrable_of_bound' mπ (hπb s)
  have ir : Integrable (r s) S.μ := integrable_of_bound' mr (hrb s)
  have i1 : Integrable (fun ω => Real.exp ((p.ε - 1) * π s ω)) S.μ :=
    integrable_of_bound' (Real.continuous_exp.measurable.comp (mπ.const_mul _))
      (abs_exp_le hπb _ s)
  have i2 : Integrable (fun ω => Real.exp ((1 - p.ε) * r s ω)) S.μ :=
    integrable_of_bound' (Real.continuous_exp.measurable.comp (mr.const_mul _))
      (abs_exp_le hrb _ s)
  have := ((((i1.const_mul p.α).add (i2.const_mul (1 - p.α))).sub (integrable_const 1)).sub
    ((iπ.const_mul (p.α * (p.ε - 1))).add (ir.const_mul ((1 - p.α) * (1 - p.ε)))))
  refine this.congr (Eventually.of_forall fun ω => ?_)
  simp only [RI, Pi.add_apply, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (17.17), p. 407, **the exact Calvo identity**: with the index at every
date, almost surely
`π_t − βE_tπ_{t+1} − κx_t − u_{π,t} = ((1 − α)/(cα))(G_t − δE_tG_{t+1})`. -/
theorem pc_residual {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L Lr : ℝ}
    (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (hr : StronglyAdapted S.𝓕 r) (hrb : ∀ s ω, |r s ω| ≤ Lr)
    (hI : Index p π r) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, π t ω - (p.β * S.E t (π (t + 1)) ω + p.κ * x t ω + calvoRem S p x π r t ω) =
      (1 - p.α) / (p.c * p.α) * (gap S p x π r t ω - p.δ * S.E t (gap S p x π r (t + 1)) ω) := by
  have hπb : ∀ s ω, |π s ω| ≤ L := fun s ω => (hB.2 s ω).2
  have iπ : Integrable (π (t + 1)) S.μ :=
    integrable_of_bound' ((hπ (t + 1)).mono (S.𝓕.le _)).measurable (hπb (t + 1))
  have ir : Integrable (r (t + 1)) S.μ :=
    integrable_of_bound' ((hr (t + 1)).mono (S.𝓕.le _)).measurable (hrb (t + 1))
  have ifc : Integrable (fc S p x π (t + 1)) S.μ :=
    integrable_sm (fc_sm p x π (t + 1)) (fc_bdd h hB hρ hx hπ (t + 1))
  have ikc : Integrable (kc S p x π (t + 1)) S.μ :=
    integrable_sm (kc_sm p x π (t + 1)) (kc_bdd h hB hρ hx hπ (t + 1))
  have iRI := RI_integrable (p := p) hπ hr hπb hrb (t + 1)
  have hε1 : p.ε - 1 ≠ 0 := by linarith [h.2.2.2.2.1]
  have hα1 : 1 - p.α ≠ 0 := by linarith [h.2.1]
  have hα0 : p.α ≠ 0 := h.1.ne'
  have hc0 : p.c ≠ 0 := h.c_pos.ne'
  -- the linearity of `E_t`
  have a1 : S.E t (fun ω => (p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω) =ᵐ[S.μ]
      fun ω => (p.ε - 1) * S.E t (π (t + 1)) ω + S.E t (fc S p x π (t + 1)) ω := by
    have e : (fun ω => (p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω) =
        (p.ε - 1) • π (t + 1) + fc S p x π (t + 1) := by funext ω; simp
    rw [e]
    filter_upwards [S.E_add (iπ.smul (p.ε - 1)) ifc t, S.E_smul (p.ε - 1) (π (t + 1)) t]
      with ω h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
  have a2 : S.E t (fun ω => p.η * π (t + 1) ω + kc S p x π (t + 1) ω) =ᵐ[S.μ]
      fun ω => p.η * S.E t (π (t + 1)) ω + S.E t (kc S p x π (t + 1)) ω := by
    have e : (fun ω => p.η * π (t + 1) ω + kc S p x π (t + 1) ω) =
        p.η • π (t + 1) + kc S p x π (t + 1) := by funext ω; simp
    rw [e]
    filter_upwards [S.E_add (iπ.smul p.η) ikc t, S.E_smul p.η (π (t + 1)) t] with ω h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
  have a3 : S.E t (gap S p x π r (t + 1)) =ᵐ[S.μ] fun ω => p.c * S.E t (r (t + 1)) ω -
      (S.E t (kc S p x π (t + 1)) ω - S.E t (fc S p x π (t + 1)) ω) := by
    have e : gap S p x π r (t + 1) =
        p.c • r (t + 1) - (kc S p x π (t + 1) - fc S p x π (t + 1)) := by
      funext ω; simp [gap]
    rw [e]
    filter_upwards [S.E_sub (ir.smul p.c) (ikc.sub ifc) t, S.E_smul p.c (r (t + 1)) t,
      S.E_sub ikc ifc t] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  have a4 : S.E t (r (t + 1)) =ᵐ[S.μ] fun ω => (p.α * (p.ε - 1) * S.E t (π (t + 1)) ω +
      S.E t (RI p π r (t + 1)) ω) / ((1 - p.α) * (p.ε - 1)) := by
    have e : r (t + 1) = ((1 - p.α) * (p.ε - 1))⁻¹ • ((p.α * (p.ε - 1)) • π (t + 1) +
        RI p π r (t + 1)) := by
      funext ω
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      have := r_of_index hI (t + 1) ω
      field_simp
      linarith
    rw [e]
    filter_upwards [S.E_smul ((1 - p.α) * (p.ε - 1))⁻¹ ((p.α * (p.ε - 1)) • π (t + 1) +
      RI p π r (t + 1)) t, S.E_add (iπ.smul (p.α * (p.ε - 1))) iRI t,
      S.E_smul (p.α * (p.ε - 1)) (π (t + 1)) t]
      with ω h1 h2 h3
    rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    field_simp
  filter_upwards [a1, a2, a3, a4] with ω e1 e2 e3 e4
  simp only [calvoRem, RK, RF, gap]
  rw [e1, e2, e3, e4]
  have hrt : r t ω = (p.α * (p.ε - 1) * π t ω + RI p π r t ω) / ((1 - p.α) * (p.ε - 1)) := by
    have := r_of_index hI t ω
    field_simp
    linarith
  rw [hrt]
  simp only [CalvoPar.κ, CalvoPar.δ, CalvoPar.c, CalvoPar.η]
  have hc' : 1 - p.ε + p.ε * (1 + p.ϕ) ≠ 0 := by
    have := h.c_pos; simp only [CalvoPar.c, CalvoPar.η] at this; linarith
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: with `ηK̄ = (ε − 1)F̄` and `F, K > 0`, the optimal reset price
`r*(F, K)` is characterised by `c r* = log(K/K̄) − log(F/F̄)`. -/
theorem rStar_iff {p : CalvoPar} (h : p.Valid) {F K r : ℝ} (hF : 0 < F) (hK : 0 < K) :
    r = rStar p.ε p.η F K ↔ p.c * r - (Real.log (K / p.Kbar) - Real.log (F / p.Fbar)) = 0 := by
  have hc := h.c_pos
  have hFb := h.Fbar_pos
  have hKb := h.Kbar_pos
  have hε1 : 0 < p.ε - 1 := by linarith [h.2.2.2.2.1]
  have hl : Real.log (p.η * K / ((p.ε - 1) * F)) =
      Real.log (K / p.Kbar) - Real.log (F / p.Fbar) := by
    rw [← Real.log_div (div_pos hK hKb).ne' (div_pos hF hFb).ne']
    congr 1
    have hη : 0 < p.η := by linarith [h.η_gt]
    have he : p.ε - 1 = p.η * p.Kbar / p.Fbar := by
      rw [h.ss]; field_simp
    rw [he]
    field_simp
  rw [rStar, show 1 - p.ε + p.η = p.c from rfl, hl]
  constructor
  · intro e
    rw [e]
    field_simp
    ring
  · intro e
    field_simp
    linarith

/-- Cochrane (2023), p. 118: **resetting optimally at `t` is a zero reset gap**,
`c r_t = k_t − f_t` almost surely (for a reset price known at `t` and bounded). -/
theorem resetOpt_iff_gap {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) {t : ℕ} (hrt : StronglyMeasurable[S.𝓕 t] (r t))
    (hrtb : BddAt S (r t)) :
    ResetOpt S t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t) ↔
      gap S p x π r t =ᵐ[S.μ] 0 := by
  have hlo : 0 < min (p.loA L) (p.loB L) := lt_min (loA_pos h L) (loB_pos h L)
  have hA : ∀ᵐ ω ∂S.μ, min (p.loA L) (p.loB L) ≤ Fc S p x π t ω ∧
      Fc S p x π t ω ≤ max (p.hiA L) (p.hiB L) :=
    (Fc_mem h hB hρ hx hπ t).mono fun ω h1 =>
      ⟨(min_le_left _ _).trans h1.1, h1.2.trans (le_max_left _ _)⟩
  have hK : ∀ᵐ ω ∂S.μ, min (p.loA L) (p.loB L) ≤ Kc S p x π t ω ∧
      Kc S p x π t ω ≤ max (p.hiA L) (p.hiB L) :=
    (Kc_mem h hB hρ hx hπ t).mono fun ω h1 =>
      ⟨(min_le_right _ _).trans h1.1, h1.2.trans (le_max_right _ _)⟩
  rw [resetOpt_iff h.2.2.2.2.1 h.η_gt hlo (fun ω => (wA_bounds h hB hρ t ω).1)
    (fun ω => (wB_bounds h hB hρ t ω).1) (wA_integrable h hB hρ hx hπ t)
    (wB_integrable h hB hρ hx hπ t) hA hK]
  constructor
  · rintro ⟨-, -, he⟩
    filter_upwards [he, Fc_mem h hB hρ hx hπ t, Kc_mem h hB hρ hx hπ t] with ω h1 h2 h3
    exact (rStar_iff h ((loA_pos h L).trans_le h2.1) ((loB_pos h L).trans_le h3.1)).1 h1
  · intro hg
    refine ⟨hrt, hrtb, ?_⟩
    filter_upwards [hg, Fc_mem h hB hρ hx hπ t, Kc_mem h hB hρ hx hπ t] with ω h1 h2 h3
    exact (rStar_iff h ((loA_pos h L).trans_le h2.1) ((loB_pos h L).trans_le h3.1)).2 h1

/-- Cochrane (2023), eq. (17.17), p. 407, **the Calvo Phillips curve: necessity and
sufficiency**. With valid parameters, output gap and inflation bounded by `L` with
`δe^{ηL} < 1`, adapted variables, reset prices adapted and bounded, and the Calvo index at every
date, resetting optimally at every date is equivalent to (17.17) at every date with slope
`κ = (1 − α)(1 − αβ)(γ + ϕ)/(α(1 + εϕ))` and the explicit disturbance `calvoRem`. -/
theorem calvo_iff_PC {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L Lr : ℝ}
    (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (hr : StronglyAdapted S.𝓕 r) (hrb : ∀ s ω, |r s ω| ≤ Lr)
    (hI : Index p π r) :
    (∀ t, ResetOpt S t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t)) ↔
      ∀ t, PCM S p.β p.κ (calvoRem S p x π r) x π t := by
  have hrtb : ∀ t, BddAt S (r t) := fun t => ⟨Lr, Eventually.of_forall (hrb t)⟩
  have hk : (1 - p.α) / (p.c * p.α) ≠ 0 :=
    div_ne_zero (by linarith [h.2.1]) (mul_pos h.c_pos h.1).ne'
  have hiff : ∀ t, ResetOpt S t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t) ↔
      gap S p x π r t =ᵐ[S.μ] 0 := fun t =>
    resetOpt_iff_gap h hB hρ hx hπ (hr t) (hrtb t)
  simp only [hiff]
  constructor
  · intro hg t
    have hE : S.E t (gap S p x π r (t + 1)) =ᵐ[S.μ] 0 := by
      have := S.E_congr (hg (t + 1)) t
      rwa [S.E_zero] at this
    filter_upwards [pc_residual h hB hρ hx hπ hr hrb hI t, hg t, hE] with ω h1 h2 h3
    simp only [Pi.zero_apply] at h2 h3
    rw [h2, h3] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro hpc
    -- the reset gap solves `G_t = δE_tG_{t+1}`
    have hsol : S.Solves p.δ 0 (gap S p x π r) := fun t => by
      filter_upwards [pc_residual h hB hρ hx hπ hr hrb hI t, hpc t] with ω h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at h2 ⊢
      rw [h2] at h1
      have : (1 - p.α) / (p.c * p.α) *
          (gap S p x π r t ω - p.δ * S.E t (gap S p x π r (t + 1)) ω) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hk
      · linarith
    have hsol0 : S.Solves p.δ 0 (0 : ℕ → Ω → ℝ) := fun t =>
      Eventually.of_forall fun ω => by simp [S.E_zero]
    have hgm : ∀ t, AEStronglyMeasurable (gap S p x π r t) S.μ := fun t =>
      (((((hr t).measurable.const_mul p.c).sub ((kc_sm p x π t).measurable.sub
        (fc_sm p x π t).measurable))).stronglyMeasurable.mono (S.𝓕.le t)).aestronglyMeasurable
    have hgb : S.BddProc (gap S p x π r) := by
      refine ⟨|p.c| * Lr + (max |Real.log (p.loB L / p.Kbar)| |Real.log (p.hiB L / p.Kbar)| +
        max |Real.log (p.loA L / p.Fbar)| |Real.log (p.hiA L / p.Fbar)|), fun t => ?_⟩
      filter_upwards [fc_bdd h hB hρ hx hπ t, kc_bdd h hB hρ hx hπ t] with ω h1 h2
      simp only [gap]
      calc |p.c * r t ω - (kc S p x π t ω - fc S p x π t ω)|
          ≤ |p.c * r t ω| + (|kc S p x π t ω| + |fc S p x π t ω|) :=
            (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
        _ ≤ _ := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hrb t ω) (abs_nonneg _))
            (add_le_add h2 h1)
    have hδ : |p.δ| < 1 := by rw [abs_of_pos h.δ_pos]; exact h.δ_lt
    exact S.forward_unique hδ hsol hsol0 hgm (fun _ => aestronglyMeasurable_const)
      hgb ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩

/-! ### Finite event trees -/

namespace Tree

open ExpectationsFiniteTree TreeBridge TidyR6HouseholdMeasureTVC.Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), eq. (17.17), p. 407: on a finite tree, the almost-sure Phillips curve with
any disturbance `u` at every date is the project's `FullModel.PC` for the tree's core expectation
system, in every state. -/
theorem PCM_iff_PC_gen (β κ : ℝ) (u x π : ℕ → Ω' → ℝ) :
    (∀ t, PCM (treeSystem T) β κ u x π t) ↔ FullModel.PC T.toExpectationSystem β κ u x π := by
  constructor
  · intro h t
    rw [(treeSystem T).eq_of_ae_eq (treeSystem_fullSupport T) (h t), treeE]
  · intro h t
    refine Eventually.of_forall fun ω => ?_
    rw [h t, treeE]

/-- Cochrane (2023), eq. (17.17), p. 407, **the Calvo Phillips curve on a finite event tree**:
under the hypotheses of `calvo_iff_PC` posed on the tree, resetting optimally at every date is
equivalent to the project's `FullModel.PC`, in every state, with `u_π = calvoRem`. -/
theorem calvo_iff_PC {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω' → ℝ} {L Lr : ℝ}
    (hB : Bounded x π L) (hρ : p.δ * Real.exp (p.η * L) < 1)
    (hx : StronglyAdapted (treeSystem T).𝓕 x) (hπ : StronglyAdapted (treeSystem T).𝓕 π)
    (hr : StronglyAdapted (treeSystem T).𝓕 r) (hrb : ∀ s ω, |r s ω| ≤ Lr)
    (hI : Index p π r) :
    (∀ t, ResetOpt (treeSystem T) t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t)) ↔
      FullModel.PC T.toExpectationSystem p.β p.κ (calvoRem (treeSystem T) p x π r) x π := by
  rw [TidyR6CalvoPC.calvo_iff_PC h hB hρ hx hπ hr hrb hI, PCM_iff_PC_gen]

end Tree

end Cochrane.KeynesianStickyPrices.TidyR6CalvoPC
