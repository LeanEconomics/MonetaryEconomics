/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Exercise 5.3: optimal policy with transaction frictions

Galí (2015), Chapter 5, Exercise 5.3, pp. 160–161 (based on Woodford 2003b). The planner
minimises `∑ βᵗ (π_t² + ϑ y_t² + α_i i_t²)` (the welfare loss up to the factor `1/2`) subject
to `π_t = β π_{t+1} + κ y_t` and `y_t = −σ⁻¹(i_t − π_{t+1} − r^n_t) + y_{t+1}` for `t ≥ 0`.
Following the chapter (§5.2.2 and the survey's advice), the problem is studied in its
deterministic (perfect-foresight) form for an arbitrary bounded natural-rate path `r^n`, over
bounded paths (Galí's convention).

## (a) The optimality conditions
With multipliers `ξ_1` (Phillips curve) and `ξ_2` (IS curve), `ξ_{1,−1} = ξ_{2,−1} = 0`:
`π_t + ξ_{1,t} − ξ_{1,t−1} − ξ_{2,t−1}/(σβ) = 0`, `ϑ y_t − κ ξ_{1,t} + ξ_{2,t} − ξ_{2,t−1}/β = 0`,
`α_i i_t + ξ_{2,t}/σ = 0` (`FOC`).
* `partial_sum_identity`: summation by parts against any homogeneous feasible direction.
* `ex5_3a_sufficient`: a bounded feasible plan satisfying the FOCs is optimal among bounded
  feasible plans, and it is the unique optimum.
* `ex5_3a_necessary`: every optimal bounded feasible plan satisfies the FOCs (with
  `ξ_2 = −σ α_i i`, `ξ_1 = (ϑ y + ξ_2 − ξ_{2,−1}/β)/κ`); the proof uses the feasible
  finitely supported directions `direction` (`dπ = 𝟙_s`).
* `ex5_3a_optimal_iff`: optimal ⟺ FOCs.

## (b) The implementing rule
`ex5_3b_rule_iff`: the FOCs hold for some multipliers iff the plan satisfies
`i_t = (1 + κ/(σβ)) i_{t−1} + β⁻¹ Δi_{t−1} + (κ/(α_i σ)) π_t + (ϑ/(α_i σ)) Δy_t`
at every `t ≥ 0` (with `i_{−1} = i_{−2} = y_{−1} = 0`), a rule that does not involve `r^n`.
`ex5_3b`: a bounded feasible plan is optimal iff it satisfies the rule. Determinacy of the
rule (that, with the constraints, it has a unique bounded solution) is not claimed in the
exercise and is not proved here. The stochastic version (state-contingent plans) is not
formalised; `y` stands for the welfare-relevant gap `ỹ`.
-/

namespace Gali.DiscretionCommitment.Ex5_3

open Filter Topology

/-! ### The problem -/

/-- Galí (2015), §5.2.2, p. 134: the lag with zero initial condition, `x_{−1} = 0`. -/
def lag (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => x t

/-- Galí (2015), Exercise 5.3, p. 161: feasibility, `π_t = β π_{t+1} + κ y_t` and
`y_t = −σ⁻¹(i_t − π_{t+1} − r^n_t) + y_{t+1}` for all `t ≥ 0`. -/
def Feasible (β κ σ : ℝ) (rn p y i : ℕ → ℝ) : Prop :=
  ∀ t, p t = β * p (t + 1) + κ * y t ∧ y t = -(1 / σ) * (i t - p (t + 1) - rn t) + y (t + 1)

/-- Galí (2015), Exercise 5.3: the homogeneous constraints satisfied by the difference of two
feasible plans. -/
def HomFeasible (β κ σ : ℝ) (dp dy di : ℕ → ℝ) : Prop :=
  ∀ t, dp t = β * dp (t + 1) + κ * dy t ∧ dy t = -(1 / σ) * (di t - dp (t + 1)) + dy (t + 1)

/-- Galí (2015), Exercise 5.3: a path is bounded. -/
def Bdd (x : ℕ → ℝ) : Prop := ∃ M, ∀ t, |x t| ≤ M

/-- Galí (2015), Exercise 5.3, p. 160: the date-`t` loss term `βᵗ (π_t² + ϑ y_t² + α_i i_t²)`. -/
def lossTerm (β ϑ αi : ℝ) (p y i : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (p t ^ 2 + ϑ * y t ^ 2 + αi * i t ^ 2)

/-- Galí (2015), Exercise 5.3, p. 160: the loss `∑ βᵗ (π_t² + ϑ y_t² + α_i i_t²)`. -/
noncomputable def loss (β ϑ αi : ℝ) (p y i : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ αi p y i t

/-- Galí (2015), Exercise 5.3(a): the plan is optimal among bounded feasible plans. -/
def Optimal (β κ σ ϑ αi : ℝ) (rn p y i : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn p y i ∧ Bdd p ∧ Bdd y ∧ Bdd i ∧
    ∀ p' y' i', Feasible β κ σ rn p' y' i' → Bdd p' → Bdd y' → Bdd i' →
      loss β ϑ αi p y i ≤ loss β ϑ αi p' y' i'

/-- **Exercise 5.3(a), the optimality conditions** (Galí 2015, p. 161): the first-order
conditions of the Lagrangian with multipliers `ξ_1, ξ_2` and `ξ_{1,−1} = ξ_{2,−1} = 0`. -/
def FOC (β κ σ ϑ αi : ℝ) (p y i ξ1 ξ2 : ℕ → ℝ) : Prop :=
  ∀ t, p t + ξ1 t - lag ξ1 t - lag ξ2 t / (σ * β) = 0 ∧
    ϑ * y t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0 ∧ αi * i t + ξ2 t / σ = 0

/-- Galí (2015), Exercise 5.3: the residual of the inflation FOC. -/
noncomputable def resid (β σ : ℝ) (p ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : ℝ :=
  p t + ξ1 t - lag ξ1 t - lag ξ2 t / (σ * β)

/-- Galí (2015), Exercise 5.3: the cross term `βᵗ(π_t dπ_t + ϑ y_t dy_t + α_i i_t di_t)`. -/
def cross (β ϑ αi : ℝ) (p y i dp dy di : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (p t * dp t + ϑ * y t * dy t + αi * i t * di t)

/-- Galí (2015), Exercise 5.3(a) (**summation by parts**): if the `y`- and `i`-FOCs hold, then
for every homogeneous feasible direction `d`,
`∑_{t ≤ T} βᵗ(π dπ + ϑ y dy + α_i i di) = ∑_{t ≤ T} βᵗ R_t dπ_t
  − β^T (β ξ_{1,T} dπ_{T+1} + ξ_{2,T}(dπ_{T+1}/σ + dy_{T+1}))`, `R` the inflation residual. -/
theorem partial_sum_identity {β κ σ ϑ αi : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    {p y i ξ1 ξ2 dp dy di : ℕ → ℝ}
    (hy : ∀ t, ϑ * y t = κ * ξ1 t - ξ2 t + lag ξ2 t / β) (hi : ∀ t, αi * i t = -(ξ2 t / σ))
    (hd : HomFeasible β κ σ dp dy di) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), cross β ϑ αi p y i dp dy di t =
      ∑ t ∈ Finset.range (T + 1), β ^ t * (resid β σ p ξ1 ξ2 t * dp t) -
        β ^ T * (β * ξ1 T * dp (T + 1) + ξ2 T * (dp (T + 1) / σ + dy (T + 1))) := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, cross, resid, pow_zero, one_mul]
    rw [hy 0, hi 0]
    obtain ⟨h1, h2⟩ := hd 0
    simp only [lag]
    linear_combination (norm := skip) (-ξ1 0) * h1 + (-ξ2 0) * h2
    field_simp
    ring
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => cross β ϑ αi p y i dp dy di t) (T + 1), ih,
      Finset.sum_range_succ (fun t => β ^ t * (resid β σ p ξ1 ξ2 t * dp t)) (T + 1)]
    generalize ∑ t ∈ Finset.range (T + 1), β ^ t * (resid β σ p ξ1 ξ2 t * dp t) = S
    simp only [cross, resid]
    rw [hy (T + 1), hi (T + 1)]
    obtain ⟨h1, h2⟩ := hd (T + 1)
    simp only [lag]
    linear_combination (norm := skip) (-β ^ (T + 1) * ξ1 (T + 1)) * h1 +
      (-β ^ (T + 1) * ξ2 (T + 1)) * h2
    field_simp
    ring

/-! ### Bounded paths -/

/-- Galí (2015), Exercise 5.3: the lag of a bounded path is bounded. -/
theorem bdd_lag {x : ℕ → ℝ} (hx : Bdd x) : Bdd (lag x) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨M, fun t => ?_⟩
  rcases t with _ | t
  · simpa [lag] using (abs_nonneg _).trans (hM 0)
  · exact hM t

/-- Galí (2015), Exercise 5.3: linear combinations of bounded paths are bounded. -/
theorem bdd_lin {x z : ℕ → ℝ} (hx : Bdd x) (hz : Bdd z) (a b : ℝ) :
    Bdd fun t => a * x t + b * z t := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hz
  refine ⟨|a| * M + |b| * N, fun t => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hN t) (abs_nonneg b)

/-- Galí (2015), Exercise 5.3: the lead of a bounded path is bounded. -/
theorem bdd_shift {x : ℕ → ℝ} (hx : Bdd x) : Bdd fun t => x (t + 1) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M, fun t => hM (t + 1)⟩

/-- Galí (2015), Exercise 5.3: the loss series of a bounded plan is summable
(`0 ≤ β < 1`, `ϑ, α_i ≥ 0`). -/
theorem loss_summable {β ϑ αi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ) (hα : 0 ≤ αi)
    {p y i : ℕ → ℝ} (hp : Bdd p) (hy : Bdd y) (hi : Bdd i) :
    Summable (lossTerm β ϑ αi p y i) := by
  obtain ⟨A, hA⟩ := hp
  obtain ⟨B, hB⟩ := hy
  obtain ⟨C, hC⟩ := hi
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2 + αi * C ^ 2))
    (fun t => ?_)
  rw [Real.norm_eq_abs, lossTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have h1 : p t ^ 2 ≤ A ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
  have h2 : y t ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  have h3 : i t ^ 2 ≤ C ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC t) 2
  rw [abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hϑ, mul_le_mul_of_nonneg_left h3 hα]

/-- Galí (2015), Exercise 5.3: the cross series of bounded paths is summable. -/
theorem cross_summable {β ϑ αi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {p y i dp dy di : ℕ → ℝ} (hp : Bdd p) (hy : Bdd y) (hi : Bdd i) (hdp : Bdd dp)
    (hdy : Bdd dy) (hdi : Bdd di) : Summable (cross β ϑ αi p y i dp dy di) := by
  obtain ⟨A, hA⟩ := hp
  obtain ⟨B, hB⟩ := hy
  obtain ⟨C, hC⟩ := hi
  obtain ⟨D, hD⟩ := hdp
  obtain ⟨E, hE⟩ := hdy
  obtain ⟨F, hF⟩ := hdi
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A * D + |ϑ| * B * E + |αi| * C * F))
    (fun t => ?_)
  rw [Real.norm_eq_abs, cross, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul]; exact mul_le_mul (hA t) (hD t) (abs_nonneg _) hA0
  · rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hB t) (hE t) (abs_nonneg _) hB0) (abs_nonneg _)
  · rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hC t) (hF t) (abs_nonneg _) hC0) (abs_nonneg _)

/-- Galí (2015), Exercise 5.3: the difference of two feasible plans is a homogeneous feasible
direction. -/
theorem hom_of_feasible {β κ σ : ℝ} {rn p y i p' y' i' : ℕ → ℝ}
    (h : Feasible β κ σ rn p y i) (h' : Feasible β κ σ rn p' y' i') :
    HomFeasible β κ σ (fun t => p' t - p t) (fun t => y' t - y t) (fun t => i' t - i t) := by
  intro t
  obtain ⟨a1, a2⟩ := h t
  obtain ⟨b1, b2⟩ := h' t
  constructor
  · linear_combination b1 - a1
  · linear_combination b2 - a2

/-- Galí (2015), Exercise 5.3: a feasible plan plus a multiple of a homogeneous feasible
direction is feasible. -/
theorem feasible_add {β κ σ : ℝ} {rn p y i dp dy di : ℕ → ℝ} (h : Feasible β κ σ rn p y i)
    (hd : HomFeasible β κ σ dp dy di) (ε : ℝ) :
    Feasible β κ σ rn (fun t => p t + ε * dp t) (fun t => y t + ε * dy t)
      (fun t => i t + ε * di t) := by
  intro t
  obtain ⟨a1, a2⟩ := h t
  obtain ⟨b1, b2⟩ := hd t
  constructor
  · linear_combination a1 + ε * b1
  · linear_combination a2 + ε * b2

/-- Galí (2015), Exercise 5.3: the loss term of a perturbed plan,
`ℓ'_t = ℓ_t + 2 c_t + βᵗ(dπ² + ϑ dy² + α_i di²)`. -/
theorem lossTerm_add (β ϑ αi : ℝ) (p y i dp dy di : ℕ → ℝ) (t : ℕ) :
    lossTerm β ϑ αi (fun t => p t + dp t) (fun t => y t + dy t) (fun t => i t + di t) t =
      lossTerm β ϑ αi p y i t + 2 * cross β ϑ αi p y i dp dy di t +
        lossTerm β ϑ αi dp dy di t := by
  simp only [lossTerm, cross]
  ring

/-! ### (a) Sufficiency -/

/-- Galí (2015), Exercise 5.3(a): the multipliers of a bounded plan satisfying the `y`- and
`i`-FOCs are bounded. -/
theorem multipliers_bdd {β κ σ ϑ αi : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {p y i ξ1 ξ2 : ℕ → ℝ}
    (hfoc : FOC β κ σ ϑ αi p y i ξ1 ξ2) (hy : Bdd y) (hi : Bdd i) : Bdd ξ1 ∧ Bdd ξ2 := by
  have e2 : ξ2 = fun t => (-σ * αi) * i t + 0 * i t := by
    funext t
    have := (hfoc t).2.2
    field_simp at this
    linear_combination this
  have h2 : Bdd ξ2 := by rw [e2]; exact bdd_lin hi hi _ _
  have e1 : ξ1 = fun t => κ⁻¹ * (ϑ * y t + 1 * ξ2 t) + (-(κ⁻¹ / β)) * lag ξ2 t := by
    funext t
    have := (hfoc t).2.1
    field_simp
    linear_combination -this
  refine ⟨?_, h2⟩
  rw [e1]
  exact bdd_lin (bdd_lin hy h2 ϑ 1) (bdd_lag h2) _ _

/-- **Exercise 5.3(a), sufficiency** (Galí 2015, p. 161): a bounded feasible plan satisfying the
FOCs is optimal among bounded feasible plans, and it is the only optimal one. -/
theorem ex5_3a_sufficient {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hσ : σ ≠ 0) (hϑ : 0 < ϑ) (hα : 0 < αi) {rn p y i ξ1 ξ2 : ℕ → ℝ}
    (hf : Feasible β κ σ rn p y i) (hp : Bdd p) (hy : Bdd y) (hi : Bdd i)
    (hfoc : FOC β κ σ ϑ αi p y i ξ1 ξ2) :
    Optimal β κ σ ϑ αi rn p y i ∧
      ∀ p' y' i', Feasible β κ σ rn p' y' i' → Bdd p' → Bdd y' → Bdd i' →
        loss β ϑ αi p' y' i' ≤ loss β ϑ αi p y i → p' = p ∧ y' = y ∧ i' = i := by
  obtain ⟨hξ1, hξ2⟩ := multipliers_bdd hκ hσ hfoc hy hi
  -- the key fact: for every alternative, loss' = loss + ∑ βᵗ (dπ² + ϑ dy² + α_i di²)
  have key : ∀ p' y' i', Feasible β κ σ rn p' y' i' → Bdd p' → Bdd y' → Bdd i' →
      loss β ϑ αi p' y' i' = loss β ϑ αi p y i +
        loss β ϑ αi (fun t => p' t - p t) (fun t => y' t - y t) (fun t => i' t - i t) := by
    intro p' y' i' hf' hp' hy' hi'
    set dp : ℕ → ℝ := fun t => p' t - p t
    set dy : ℕ → ℝ := fun t => y' t - y t
    set di : ℕ → ℝ := fun t => i' t - i t
    have hd : HomFeasible β κ σ dp dy di := hom_of_feasible hf hf'
    have hbdp : Bdd dp := by
      have := bdd_lin hp' hp 1 (-1); simpa [dp, sub_eq_add_neg] using this
    have hbdy : Bdd dy := by
      have := bdd_lin hy' hy 1 (-1); simpa [dy, sub_eq_add_neg] using this
    have hbdi : Bdd di := by
      have := bdd_lin hi' hi 1 (-1); simpa [di, sub_eq_add_neg] using this
    have hcs := cross_summable (ϑ := ϑ) (αi := αi) hβ0.le hβ1 hp hy hi hbdp hbdy hbdi
    -- partial sums of the cross series are minus the boundary term, which tends to zero
    have hyf : ∀ t, ϑ * y t = κ * ξ1 t - ξ2 t + lag ξ2 t / β := fun t => by
      have := (hfoc t).2.1; linarith
    have hif : ∀ t, αi * i t = -(ξ2 t / σ) := fun t => by
      have := (hfoc t).2.2; linarith
    have hres : ∀ t, resid β σ p ξ1 ξ2 t = 0 := fun t => (hfoc t).1
    have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), cross β ϑ αi p y i dp dy di t =
        -(β ^ T * (β * ξ1 T * dp (T + 1) + ξ2 T * (dp (T + 1) / σ + dy (T + 1)))) := by
      intro T
      rw [partial_sum_identity hβ0.ne' hσ hyf hif hd T]
      simp [hres]
    obtain ⟨A, hA⟩ := hξ1
    obtain ⟨B, hB⟩ := hξ2
    obtain ⟨D, hD⟩ := hbdp
    obtain ⟨E, hE⟩ := hbdy
    have hbound : ∀ T, ‖-(β ^ T * (β * ξ1 T * dp (T + 1) + ξ2 T * (dp (T + 1) / σ +
        dy (T + 1))))‖ ≤ β ^ T * (β * A * D + B * (D / |σ| + E)) := by
      intro T
      have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
      have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le T)
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_of_pos hβ0]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hA T) hβ0.le) (hD (T + 1)) (abs_nonneg _)
          (by positivity)
      · rw [abs_mul]
        refine mul_le_mul (hB T) ((abs_add_le _ _).trans (add_le_add ?_ (hE (T + 1))))
          (abs_nonneg _) hB0
        rw [abs_div]
        exact div_le_div_of_nonneg_right (hD (T + 1)) (abs_nonneg _)
    have hlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), cross β ϑ αi p y i dp dy di t)
        atTop (𝓝 0) := by
      simp only [hpart]
      refine squeeze_zero_norm hbound ?_
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
        (β * A * D + B * (D / |σ| + E))
    have htsum : ∑' t, cross β ϑ αi p y i dp dy di t = 0 :=
      tendsto_nhds_unique ((hcs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)) hlim
    have hl := loss_summable hβ0.le hβ1 hϑ.le hα.le hp hy hi
    have hq := loss_summable hβ0.le hβ1 hϑ.le hα.le ⟨D, hD⟩ ⟨E, hE⟩ hbdi
    have hsplit : lossTerm β ϑ αi p' y' i' = fun t => lossTerm β ϑ αi p y i t +
        2 * cross β ϑ αi p y i dp dy di t + lossTerm β ϑ αi dp dy di t := by
      funext t
      have := lossTerm_add β ϑ αi p y i dp dy di t
      simpa [dp, dy, di] using this
    unfold loss
    rw [hsplit, (hl.add (hcs.mul_left 2)).tsum_add hq, hl.tsum_add (hcs.mul_left 2),
      tsum_mul_left, htsum, mul_zero, add_zero]
  have hqnn : ∀ dp dy di : ℕ → ℝ, ∀ t, 0 ≤ lossTerm β ϑ αi dp dy di t := fun dp dy di t => by
    unfold lossTerm; positivity
  refine ⟨⟨hf, hp, hy, hi, fun p' y' i' hf' hp' hy' hi' => ?_⟩,
    fun p' y' i' hf' hp' hy' hi' hle => ?_⟩
  · rw [key p' y' i' hf' hp' hy' hi']
    exact le_add_of_nonneg_right (tsum_nonneg (hqnn _ _ _))
  · rw [key p' y' i' hf' hp' hy' hi'] at hle
    have h0 : loss β ϑ αi (fun t => p' t - p t) (fun t => y' t - y t)
        (fun t => i' t - i t) ≤ 0 := by linarith
    have hbd : ∀ (x x' : ℕ → ℝ), Bdd x → Bdd x' → Bdd fun t => x' t - x t := by
      intro x x' hx hx'
      have := bdd_lin hx' hx 1 (-1); simpa [sub_eq_add_neg] using this
    have hq := loss_summable hβ0.le hβ1 hϑ.le hα.le (hbd p p' hp hp') (hbd y y' hy hy')
      (hbd i i' hi hi')
    have hz : ∀ t, lossTerm β ϑ αi (fun t => p' t - p t) (fun t => y' t - y t)
        (fun t => i' t - i t) t = 0 := fun t =>
      le_antisymm ((hq.le_tsum t (fun j _ => hqnn _ _ _ j)).trans h0) (hqnn _ _ _ t)
    have hall : ∀ t, p' t - p t = 0 ∧ y' t - y t = 0 ∧ i' t - i t = 0 := by
      intro t
      have h := hz t
      simp only [lossTerm] at h
      have hβt : 0 < β ^ t := pow_pos hβ0 t
      have hin : (p' t - p t) ^ 2 + ϑ * (y' t - y t) ^ 2 + αi * (i' t - i t) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h hβt.ne'
        · exact h
      have a1 := sq_nonneg (p' t - p t)
      have a2 := mul_nonneg hϑ.le (sq_nonneg (y' t - y t))
      have a3 := mul_nonneg hα.le (sq_nonneg (i' t - i t))
      refine ⟨pow_eq_zero_iff two_ne_zero |>.mp (by linarith), ?_, ?_⟩
      · have : (y' t - y t) ^ 2 = 0 := by
          rcases mul_eq_zero.mp (show ϑ * (y' t - y t) ^ 2 = 0 by linarith) with h | h
          · exact absurd h hϑ.ne'
          · exact h
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      · have : (i' t - i t) ^ 2 = 0 := by
          rcases mul_eq_zero.mp (show αi * (i' t - i t) ^ 2 = 0 by linarith) with h | h
          · exact absurd h hα.ne'
          · exact h
        exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact ⟨funext fun t => sub_eq_zero.mp (hall t).1, funext fun t => sub_eq_zero.mp (hall t).2.1,
      funext fun t => sub_eq_zero.mp (hall t).2.2⟩

/-! ### (a) Necessity -/

/-- Galí (2015), Exercise 5.3(a): the test direction `dπ = 𝟙_{t = s}`. -/
def dirP (s : ℕ) : ℕ → ℝ := fun t => if t = s then 1 else 0

/-- Galí (2015), Exercise 5.3(a): the output-gap part of the test direction,
`dy_t = (dπ_t − β dπ_{t+1})/κ`. -/
noncomputable def dirY (β κ : ℝ) (s : ℕ) : ℕ → ℝ :=
  fun t => (dirP s t - β * dirP s (t + 1)) / κ

/-- Galí (2015), Exercise 5.3(a): the interest-rate part of the test direction,
`di_t = dπ_{t+1} + σ(dy_{t+1} − dy_t)`. -/
noncomputable def dirI (β κ σ : ℝ) (s : ℕ) : ℕ → ℝ :=
  fun t => dirP s (t + 1) + σ * (dirY β κ s (t + 1) - dirY β κ s t)

/-- Galí (2015), Exercise 5.3(a): the test direction is homogeneous feasible. -/
theorem dir_hom {β κ σ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) (s : ℕ) :
    HomFeasible β κ σ (dirP s) (dirY β κ s) (dirI β κ σ s) := by
  intro t
  constructor
  · simp only [dirY]
    field_simp
    ring
  · simp only [dirI]
    field_simp
    ring

/-- Galí (2015), Exercise 5.3(a): the test direction is bounded. -/
theorem dir_bdd (β κ σ : ℝ) (s : ℕ) :
    Bdd (dirP s) ∧ Bdd (dirY β κ s) ∧ Bdd (dirI β κ σ s) := by
  have h0 : Bdd (dirP s) := ⟨1, fun t => by simp only [dirP]; split_ifs <;> simp⟩
  have h1 : Bdd (dirY β κ s) := by
    have := bdd_lin h0 (bdd_shift h0) κ⁻¹ (-β / κ)
    refine this.elim fun M hM => ⟨M, fun t => ?_⟩
    have e : dirY β κ s t = κ⁻¹ * dirP s t + -β / κ * dirP s (t + 1) := by
      simp only [dirY]; ring
    rw [e]; exact hM t
  have h2 : Bdd (dirI β κ σ s) := by
    have := bdd_lin (bdd_shift h0) (bdd_lin (bdd_shift h1) h1 σ (-σ)) 1 1
    refine this.elim fun M hM => ⟨M, fun t => ?_⟩
    have e : dirI β κ σ s t = 1 * dirP s (t + 1) +
        1 * (σ * dirY β κ s (t + 1) + -σ * dirY β κ s t) := by
      simp only [dirI]; ring
    rw [e]; exact hM t
  exact ⟨h0, h1, h2⟩

/-- Galí (2015), Exercise 5.3(a): the test direction vanishes after date `s`. -/
theorem dir_zero_after {β κ σ : ℝ} {s t : ℕ} (h : s < t) :
    dirP s t = 0 ∧ dirY β κ s t = 0 ∧ dirI β κ σ s t = 0 := by
  have hp : ∀ u, s < u → dirP s u = 0 := fun u hu => by
    simp only [dirP]
    split_ifs
    · omega
    · rfl
  have hy : ∀ u, s < u → dirY β κ s u = 0 := fun u hu => by
    simp only [dirY]; rw [hp u hu, hp (u + 1) (by omega)]; simp
  refine ⟨hp t h, hy t h, ?_⟩
  simp only [dirI]
  rw [hp (t + 1) (by omega), hy t h, hy (t + 1) (by omega)]
  simp

/-- Galí (2015), Exercise 5.3: two bounded plans that agree from date `k` on have losses
differing by the finite sum of the first `k` terms. -/
theorem loss_eq_of_eq_after {β ϑ αi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    (hα : 0 ≤ αi) {p y i p' y' i' : ℕ → ℝ} (hp : Bdd p) (hy : Bdd y) (hi : Bdd i)
    (hp' : Bdd p') (hy' : Bdd y') (hi' : Bdd i') (k : ℕ)
    (heq : ∀ t, p' (t + k) = p (t + k) ∧ y' (t + k) = y (t + k) ∧ i' (t + k) = i (t + k)) :
    loss β ϑ αi p' y' i' = loss β ϑ αi p y i +
      ∑ t ∈ Finset.range k, (lossTerm β ϑ αi p' y' i' t - lossTerm β ϑ αi p y i t) := by
  unfold loss
  rw [← (loss_summable hβ0 hβ1 hϑ hα hp' hy' hi').sum_add_tsum_nat_add k,
    ← (loss_summable hβ0 hβ1 hϑ hα hp hy hi).sum_add_tsum_nat_add k, Finset.sum_sub_distrib]
  have : ∑' t, lossTerm β ϑ αi p' y' i' (t + k) = ∑' t, lossTerm β ϑ αi p y i (t + k) :=
    tsum_congr fun t => by simp only [lossTerm, (heq t).1, (heq t).2.1, (heq t).2.2]
  rw [this]
  ring

/-- Galí (2015), Exercise 5.3(a): if `2εC + ε²Q ≥ 0` for every `ε` and `Q ≥ 0`, then `C = 0`. -/
theorem eq_zero_of_quadratic {C Q : ℝ} (hQ : 0 ≤ Q) (h : ∀ ε : ℝ, 0 ≤ 2 * ε * C + ε ^ 2 * Q) :
    C = 0 := by
  have hQ1 : 0 < Q + 1 := by linarith
  have e : 2 * (-C / (Q + 1)) * C + (-C / (Q + 1)) ^ 2 * Q =
      -(C ^ 2 * (Q + 2)) / (Q + 1) ^ 2 := by
    field_simp
    ring
  have h1 := h (-C / (Q + 1))
  rw [e] at h1
  have h2 : 0 ≤ -(C ^ 2 * (Q + 2)) := by
    have := mul_nonneg h1 (sq_nonneg (Q + 1))
    rwa [div_mul_cancel₀ _ (pow_ne_zero 2 hQ1.ne')] at this
  have h3 : C ^ 2 = 0 := by nlinarith [sq_nonneg C]
  exact pow_eq_zero_iff two_ne_zero |>.mp h3

/-- Galí (2015), Exercise 5.3(a): the multiplier on the IS curve, `ξ_{2,t} = −σ α_i i_t`
(from the `i`-FOC). -/
def xi2 (σ αi : ℝ) (i : ℕ → ℝ) : ℕ → ℝ := fun t => -σ * αi * i t

/-- Galí (2015), Exercise 5.3(a): the multiplier on the Phillips curve,
`ξ_{1,t} = (ϑ y_t + ξ_{2,t} − ξ_{2,t−1}/β)/κ` (from the `y`-FOC). -/
noncomputable def xi1 (β κ ϑ : ℝ) (y ξ2 : ℕ → ℝ) : ℕ → ℝ :=
  fun t => (ϑ * y t + ξ2 t - lag ξ2 t / β) / κ

/-- **Exercise 5.3(a), necessity** (Galí 2015, p. 161): an optimal bounded feasible plan
satisfies the FOCs with `ξ_2 = −σ α_i i` and `ξ_1 = (ϑ y + ξ_2 − ξ_{2,−1}/β)/κ`. -/
theorem ex5_3a_necessary {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hσ : σ ≠ 0) (hϑ : 0 ≤ ϑ) (hα : 0 ≤ αi) {rn p y i : ℕ → ℝ}
    (hopt : Optimal β κ σ ϑ αi rn p y i) :
    FOC β κ σ ϑ αi p y i (xi1 β κ ϑ y (xi2 σ αi i)) (xi2 σ αi i) := by
  obtain ⟨hf, hp, hy, hi, hmin⟩ := hopt
  set ξ2 := xi2 σ αi i
  set ξ1 := xi1 β κ ϑ y ξ2
  have hyf : ∀ t, ϑ * y t = κ * ξ1 t - ξ2 t + lag ξ2 t / β := fun t => by
    simp only [ξ1, xi1]
    field_simp
    ring
  have hif : ∀ t, αi * i t = -(ξ2 t / σ) := fun t => by
    simp only [ξ2, xi2]
    field_simp
  intro s
  refine ⟨?_, by linarith [hyf s], by linarith [hif s]⟩
  -- test the plan against the direction concentrated at `s`
  obtain ⟨hdP, hdY, hdI⟩ := dir_bdd β κ σ s
  have hd := dir_hom (β := β) hκ hσ s
  set C := ∑ t ∈ Finset.range (s + 1),
    cross β ϑ αi p y i (dirP s) (dirY β κ s) (dirI β κ σ s) t
  set Q := ∑ t ∈ Finset.range (s + 1), lossTerm β ϑ αi (dirP s) (dirY β κ s) (dirI β κ σ s) t
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun t _ => by unfold lossTerm; positivity
  have hquad : ∀ ε : ℝ, 0 ≤ 2 * ε * C + ε ^ 2 * Q := by
    intro ε
    have hb : ∀ x d : ℕ → ℝ, Bdd x → Bdd d → Bdd fun t => x t + ε * d t := fun x d hx hd' => by
      have := bdd_lin hx hd' 1 ε; simpa using this
    have hle := hmin _ _ _ (feasible_add hf hd ε) (hb _ _ hp hdP) (hb _ _ hy hdY)
      (hb _ _ hi hdI)
    rw [loss_eq_of_eq_after hβ0.le hβ1 hϑ hα hp hy hi (hb _ _ hp hdP) (hb _ _ hy hdY)
      (hb _ _ hi hdI) (s + 1) (fun t => by
        obtain ⟨h1, h2, h3⟩ := dir_zero_after (β := β) (κ := κ) (σ := σ) (s := s)
          (t := t + (s + 1)) (by omega)
        simp [h1, h2, h3])] at hle
    have hsum : ∑ t ∈ Finset.range (s + 1),
        (lossTerm β ϑ αi (fun t => p t + ε * dirP s t) (fun t => y t + ε * dirY β κ s t)
          (fun t => i t + ε * dirI β κ σ s t) t - lossTerm β ϑ αi p y i t) =
        2 * ε * C + ε ^ 2 * Q := by
      simp only [C, Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, cross]
      ring
    linarith
  have hC := eq_zero_of_quadratic hQ hquad
  have hid := partial_sum_identity (p := p) hβ0.ne' hσ hyf hif hd s
  obtain ⟨h1, h2, -⟩ := dir_zero_after (β := β) (κ := κ) (σ := σ) (s := s) (t := s + 1)
    (by omega)
  rw [h1, h2] at hid
  have hsingle : ∑ t ∈ Finset.range (s + 1), β ^ t * (resid β σ p ξ1 ξ2 t * dirP s t) =
      β ^ s * resid β σ p ξ1 ξ2 s := by
    rw [Finset.sum_eq_single s (fun t _ hts => by simp [dirP, hts])
      (fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self s)) h)]
    simp [dirP]
  rw [hsingle] at hid
  have : β ^ s * resid β σ p ξ1 ξ2 s = 0 := by
    have hC' : C = 0 := hC
    simp only [C] at hC'
    rw [hC'] at hid
    simp only [mul_zero, zero_div, add_zero, sub_zero] at hid
    linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (pow_ne_zero s hβ0.ne')
  · exact h

/-- **Exercise 5.3(a)** (Galí 2015, p. 161): a bounded feasible plan is optimal among bounded
feasible plans iff it satisfies the FOCs for some multipliers. -/
theorem ex5_3a_optimal_iff {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hσ : σ ≠ 0) (hϑ : 0 < ϑ) (hα : 0 < αi) {rn p y i : ℕ → ℝ}
    (hf : Feasible β κ σ rn p y i) (hp : Bdd p) (hy : Bdd y) (hi : Bdd i) :
    Optimal β κ σ ϑ αi rn p y i ↔ ∃ ξ1 ξ2, FOC β κ σ ϑ αi p y i ξ1 ξ2 :=
  ⟨fun h => ⟨_, _, ex5_3a_necessary hβ0 hβ1 hκ hσ hϑ.le hα.le h⟩,
    fun ⟨_, _, h⟩ => (ex5_3a_sufficient hβ0 hβ1 hκ hσ hϑ hα hf hp hy hi h).1⟩

/-! ### (b) The implementing rule -/

/-- **Exercise 5.3(b), the rule** (Galí 2015, p. 161):
`i_t = (1 + κ/(σβ)) i_{t−1} + β⁻¹ Δi_{t−1} + (κ/(α_i σ)) π_t + (ϑ/(α_i σ)) Δy_t` with
`i_{−1} = i_{−2} = y_{−1} = 0`. -/
noncomputable def Rule (β κ σ ϑ αi : ℝ) (p y i : ℕ → ℝ) : Prop :=
  ∀ t, i t = (1 + κ / (σ * β)) * lag i t + (lag i t - lag (lag i) t) / β +
    κ / (αi * σ) * p t + ϑ / (αi * σ) * (y t - lag y t)

/-- Galí (2015), Exercise 5.3(b): lags commute with scaling. -/
theorem lag_mul {f g : ℕ → ℝ} {c : ℝ} (h : ∀ t, f t = c * g t) (t : ℕ) :
    lag f t = c * lag g t := by
  rcases t with _ | t
  · simp [lag]
  · exact h t

/-- Galí (2015), Exercise 5.3(b): the lagged `y`-FOC (with zero initial conditions). -/
theorem lag_yfoc {β κ ϑ : ℝ} {y ξ1 ξ2 : ℕ → ℝ}
    (h : ∀ t, ϑ * y t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0) (t : ℕ) :
    ϑ * lag y t - κ * lag ξ1 t + lag ξ2 t - lag (lag ξ2) t / β = 0 := by
  rcases t with _ | t
  · simp [lag]
  · exact h t

/-- **Exercise 5.3(b)** (Galí 2015, p. 161): the FOCs hold for some multipliers iff the plan
satisfies the interest-rate rule (which does not involve `r^n`). -/
theorem ex5_3b_rule_iff {β κ σ ϑ αi : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (hα : αi ≠ 0) {p y i : ℕ → ℝ} :
    (∃ ξ1 ξ2, FOC β κ σ ϑ αi p y i ξ1 ξ2) ↔ Rule β κ σ ϑ αi p y i := by
  constructor
  · rintro ⟨ξ1, ξ2, hfoc⟩ t
    have h4 : ∀ t, ξ2 t = (-σ * αi) * i t := fun t => by
      have := (hfoc t).2.2
      field_simp at this
      linear_combination this
    have E1 := (hfoc t).1
    have E2 := (hfoc t).2.1
    have E3 := lag_yfoc (fun t => (hfoc t).2.1) t
    rw [h4 t, lag_mul h4 t] at E2
    rw [lag_mul h4 t] at E1
    rw [lag_mul h4 t, lag_mul (lag_mul h4) t] at E3
    linear_combination (norm := skip) (-1 / (σ * αi)) * (κ * E1 + E2 - E3)
    field_simp
    ring
  · intro hr
    refine ⟨xi1 β κ ϑ y (xi2 σ αi i), xi2 σ αi i, fun t => ⟨?_, ?_, ?_⟩⟩
    · have h5 : ∀ t, xi2 σ αi i t = (-σ * αi) * i t := fun t => rfl
      have hl1 : lag (xi1 β κ ϑ y (xi2 σ αi i)) t =
          (ϑ * lag y t + lag (xi2 σ αi i) t - lag (lag (xi2 σ αi i)) t / β) / κ := by
        rcases t with _ | t
        · simp [lag]
        · rfl
      rw [hl1, lag_mul (lag_mul h5) t, lag_mul h5 t]
      simp only [xi1, xi2]
      rw [lag_mul h5 t]
      linear_combination (norm := skip) (-σ * αi / κ) * hr t
      field_simp
      ring
    · simp only [xi1]
      field_simp
      ring
    · simp only [xi2]
      field_simp
      ring

/-- **Exercise 5.3(b), implementation** (Galí 2015, p. 161): a bounded feasible plan is the
optimal plan iff it satisfies the interest-rate rule. -/
theorem ex5_3b {β κ σ ϑ αi : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (hϑ : 0 < ϑ) (hα : 0 < αi) {rn p y i : ℕ → ℝ} (hf : Feasible β κ σ rn p y i) (hp : Bdd p)
    (hy : Bdd y) (hi : Bdd i) :
    Optimal β κ σ ϑ αi rn p y i ↔ Rule β κ σ ϑ αi p y i :=
  (ex5_3a_optimal_iff hβ0 hβ1 hκ hσ hϑ hα hf hp hy hi).trans
    (ex5_3b_rule_iff hβ0.ne' hκ hσ hα.ne')

end Gali.DiscretionCommitment.Ex5_3
