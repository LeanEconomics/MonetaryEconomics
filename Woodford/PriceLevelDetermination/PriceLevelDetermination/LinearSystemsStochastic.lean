/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LinearSystemsUnit
import PriceLevelDetermination.LocalIFTStochastic

/-!
# Linear rational-expectations systems with predetermined variables under uncertainty

Woodford (2003), *Interest and Prices*, Appendix A.3, eqs. (A.11)–(A.13), pp. 633–635. The
book asserts that under uncertainty the linearised system
`f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = w_t` (`x_t ∈ ℝⁿ`, `x_{−1}` given) has a unique bounded
solution exactly when the perfect-foresight system (A.10) does. This module proves it for an
arbitrary `ExpectationSystem` on any nonempty state space, using only the core axioms
(linearity, constants, monotonicity, tower and known-earlier; no pull-out, no informational
closure).

## Main results

* `SolvesLinS`, `LinDeterminateS`: the stochastic system and its determinacy (a unique bounded
  adapted solution for every bounded adapted forcing and every `x_{−1}`).
* `linDeterminateS_iff_pencil`: the system is the companion pencil of
  `SystemsBKPencil.GeneralBKSingular` under the same expectation system.
* **`linDeterminateS_iff_pf`**: uncertainty does not change determinacy — stochastic determinacy
  holds iff perfect-foresight determinacy (`LinearSystems.LinDeterminate`) holds;
  `linDeterminateS_iff_roots`: iff the exact root condition of
  `LinearSystems.linDeterminate_iff`; `isUnit_sysOp_iff_stoch`.
* The Blanchard–Kahn decision rule (`exists_solvent`, `solvent_stable`, `isUnit_solventD`,
  `solventJ_stable`, `exists_decision_rule`, `fwdV_spec`, `bkSol`, `bkSol_solves_book`,
  `decision_rule`): under the root condition there are matrices `G` (stable, solving
  `f₁ + f₂G + f₃G² = 0`), `D = f₂ + f₃G` (invertible) and `J = −D⁻¹f₃` (stable) such that the
  unique solution is `x_t = G x_{t−1} + ∑_{k ≥ 0} Jᵏ D⁻¹ E_t w_{t+k}`: the stable block is solved
  backward and the unstable block forward with `E_t`, the series commuting with `E_t` by the
  core `ExpectationSystem.E_tsum`. The same formula solves the book form
  `f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = E_t w_t` for forcing that need not be adapted
  (`book_form_iff`).
* Which half fails under uncertainty: `solvesLinS_detP_iff` (deterministic paths),
  `proj_solves` (date-`k` forecasts of a stochastic solution solve (A.10)), `homInjectiveS_iff`,
  `nonuniqueS_iff`, `nonexistS_iff` (non-uniqueness / non-existence under uncertainty are exactly
  non-injectivity / non-surjectivity of the perfect-foresight operator (A.8));
  `stoch_nonexist_of_unit_root` (a root on the unit circle: non-existence for some bounded
  deterministic forcing, any `f₃`); `failure_cases_stoch` (the four-way classification).
* Genuinely random sunspots: `random_sunspot` (on any system carrying a mean-zero variable
  revealed at date 1) and `coin_random_sunspot`, `coin_random_sunspot_of_count_gt` (on the core
  coin-flip tree, whenever more than `n` roots lie inside the unit circle or genericity fails).
* The operator on `ℓ∞(ℕ × Ω, ℝⁿ)`: `opS` (with the adaptedness term `x_t − E_t x_t`),
  `isUnit_opS_iff` (invertible iff stochastic determinacy), `isUnit_opS_iff_roots`.
-/

namespace Woodford.PriceLevelDetermination.LinearSystemsStochastic

open Filter Topology
open LinearSystems SystemsBK.InvariantSplit SystemsBK.GeneralBKForward SystemsBK.GeneralBK
open SystemsBKPencil.GeneralBKPencil SystemsBKPencil.GeneralBKSingular
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The stochastic linear system -/

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: the lagged vector process `x_{t−1}` with the
deterministic initial condition `x_{−1} = xm`. -/
def lagP (xm : ι → ℝ) (x : ℕ → ι → Ω → ℝ) : ℕ → ι → Ω → ℝ :=
  lagV (fun i (_ : Ω) => xm i) x

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: `x_{−1}` is the initial condition. -/
@[simp] theorem lagP_zero (xm : ι → ℝ) (x : ℕ → ι → Ω → ℝ) :
    lagP xm x 0 = fun i (_ : Ω) => xm i := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the lag at `t + 1` is `x_t`. -/
@[simp] theorem lagP_succ (xm : ι → ℝ) (x : ℕ → ι → Ω → ℝ) (t : ℕ) :
    lagP xm x (t + 1) = x t := rfl

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: `x` solves the linearised conditions under
uncertainty, `f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = w_t` for all `t ≥ 0`, with `x_{−1} = xm`. -/
def SolvesLinS (f₁ f₂ f₃ : Matrix ι ι ℝ) (w : ℕ → ι → Ω → ℝ) (xm : ι → ℝ)
    (x : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t, mv f₁ (lagP xm x t) + mv f₂ (x t) + mv f₃ (fun i => 𝔼.E t (x (t + 1) i)) = w t

/-- Woodford (2003), App. A.3, pp. 633–634: **determinacy under uncertainty**: for every bounded
adapted forcing and every initial condition `x_{−1}` there is exactly one bounded adapted
solution of (A.13). -/
def LinDeterminateS (f₁ f₂ f₃ : Matrix ι ι ℝ) : Prop :=
  ∀ w : ℕ → ι → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w → ∀ xm : ι → ℝ,
    ∃! x, BoundedV x ∧ AdaptedV 𝔼 x ∧ SolvesLinS 𝔼 f₁ f₂ f₃ w xm x

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): the lag of a bounded process is bounded. -/
theorem boundedV_lagP [Finite ι] (xm : ι → ℝ) {x : ℕ → ι → Ω → ℝ} (hx : BoundedV x) :
    BoundedV (lagP xm x) := by
  have := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := hx
  refine ⟨max C (∑ i, |xm i|), fun t i ω => ?_⟩
  cases t with
  | zero =>
    exact (Finset.single_le_sum (f := fun i => |xm i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)).trans (le_max_right _ _)
  | succ t => exact (hC t i ω).trans (le_max_left _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): the lag of an adapted process is adapted (the
date-`t` value is known at `t + 1`). -/
theorem adaptedV_lagP (xm : ι → ℝ) {x : ℕ → ι → Ω → ℝ} (hx : AdaptedV 𝔼 x) :
    AdaptedV 𝔼 (lagP xm x) := by
  intro t i
  cases t with
  | zero => exact 𝔼.const 0 (xm i)
  | succ t =>
    change 𝔼.E (t + 1) (x t i) = x t i
    rw [← hx t i, 𝔼.known (Nat.le_succ t)]

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): the lag of the zero process from zero is zero. -/
theorem lagP_zero_zero (t : ℕ) : lagP (0 : ι → ℝ) (0 : ℕ → ι → Ω → ℝ) t = 0 := by
  cases t <;> rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): the lag splits into the lag from zero and the
initial-condition impulse. -/
theorem lagP_split (xm : ι → ℝ) (x : ℕ → ι → Ω → ℝ) (t : ℕ) :
    lagP xm x t = lagP 0 x t + lagP xm 0 t := by
  cases t <;> funext i ω <;> simp [lagP]

/-! ### The companion pencil under uncertainty -/

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634, as a first-order system in
`y_t = (x_t, x_{t−1})`: one step of the companion pencil, state by state, is one period of
(A.13) together with the law of motion of the predetermined block. -/
theorem comp_stepS (f₁ f₂ f₃ : Matrix ι ι ℝ) (Y Y' W : ι ⊕ ι → Ω → ℝ) :
    mv (compA0 f₃) Y' = mv (compA1 f₁ f₂) Y + W ↔
      mv f₁ (fun i => Y (Sum.inr i)) + mv f₂ (fun i => Y (Sum.inl i)) +
          mv f₃ (fun i => Y' (Sum.inl i)) = (fun i => W (Sum.inl i)) ∧
        (fun i => Y' (Sum.inr i)) = (fun i => Y (Sum.inl i)) + fun i => W (Sum.inr i) := by
  have key : ∀ ω, (compA0 f₃ *ᵥ fun k => Y' k ω) =
      compA1 f₁ f₂ *ᵥ (fun k => Y k ω) + (fun k => W k ω) ↔
      f₁ *ᵥ (fun i => Y (Sum.inr i) ω) + f₂ *ᵥ (fun i => Y (Sum.inl i) ω) +
          f₃ *ᵥ (fun i => Y' (Sum.inl i) ω) = (fun i => W (Sum.inl i) ω) ∧
        (fun i => Y' (Sum.inr i) ω) = (fun i => Y (Sum.inl i) ω) + fun i => W (Sum.inr i) ω :=
    fun ω => comp_step f₁ f₂ f₃ _ _ _
  constructor
  · intro h
    have hω : ∀ ω, (compA0 f₃ *ᵥ fun k => Y' k ω) =
        compA1 f₁ f₂ *ᵥ (fun k => Y k ω) + (fun k => W k ω) := fun ω => by
      funext k
      have := congrFun (congrFun h k) ω
      simpa only [Pi.add_apply, mv_apply] using this
    refine ⟨funext fun i => funext fun ω => ?_, funext fun i => funext fun ω => ?_⟩
    · have := congrFun ((key ω).mp (hω ω)).1 i
      simpa only [Pi.add_apply, mv_apply] using this
    · have := congrFun ((key ω).mp (hω ω)).2 i
      simpa only [Pi.add_apply] using this
  · rintro ⟨h1, h2⟩
    have hω : ∀ ω, (compA0 f₃ *ᵥ fun k => Y' k ω) =
        compA1 f₁ f₂ *ᵥ (fun k => Y k ω) + (fun k => W k ω) := fun ω => by
      refine (key ω).mpr ⟨funext fun i => ?_, funext fun i => ?_⟩
      · have := congrFun (congrFun h1 i) ω
        simpa only [Pi.add_apply, mv_apply] using this
      · have := congrFun (congrFun h2 i) ω
        simpa only [Pi.add_apply] using this
    funext k ω
    have := congrFun (hω ω) k
    simpa only [Pi.add_apply, mv_apply] using this

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: a solution `y_t = (z_t, k_t)` of the
companion pencil with forcing `(a_t, b_t)`, predetermined block known one period ahead and
`k_0 = x_{−1}`, has `k_t = z_{t−1} + b_{t−1}`, and `z` solves (A.13) with forcing
`a_t − f₁ b_{t−1}`. -/
theorem lin_of_pencilS {f₁ f₂ f₃ : Matrix ι ι ℝ} {W y : ℕ → ι ⊕ ι → Ω → ℝ} {x0 : ι → ℝ}
    (hy : SolvesPencil 𝔼 (compA0 f₃) (compA1 f₁ f₂) W y)
    (hk : ∀ t j, 𝔼.E t (y (t + 1) (Sum.inr j)) = y (t + 1) (Sum.inr j))
    (h0 : ∀ j, y 0 (Sum.inr j) = fun _ => x0 j) :
    (∀ t, (fun j => y t (Sum.inr j)) =
        lagP x0 (fun s i => y s (Sum.inl i)) t + lagP 0 (fun s j => W s (Sum.inr j)) t) ∧
      SolvesLinS 𝔼 f₁ f₂ f₃
        (fun t => (fun i => W t (Sum.inl i)) - mv f₁ (lagP 0 (fun s j => W s (Sum.inr j)) t))
        x0 (fun s i => y s (Sum.inl i)) := by
  have hstep := fun t => (comp_stepS f₁ f₂ f₃ _ _ _).mp (hy t)
  have hkt : ∀ t, (fun j => y t (Sum.inr j)) =
      lagP x0 (fun s i => y s (Sum.inl i)) t + lagP 0 (fun s j => W s (Sum.inr j)) t := by
    intro t
    cases t with
    | zero =>
      funext j ω
      simp [h0 j]
    | succ t =>
      have e := (hstep t).2
      have e2 : (fun j => y (t + 1) (Sum.inr j)) =
          fun j => 𝔼.E t (y (t + 1) (Sum.inr j)) := funext fun j => (hk t j).symm
      rw [e2, e]
      rfl
  refine ⟨hkt, fun t => ?_⟩
  have e1 := (hstep t).1
  rw [hkt t, mv_add] at e1
  beta_reduce
  rw [← e1]
  abel

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634: conversely, an adapted solution `z` of
(A.13) with forcing `a_t − f₁ b_{t−1}` (`b` adapted) gives the solution
`y_t = (z_t, z_{t−1} + b_{t−1})` of the companion pencil with forcing `(a_t, b_t)`. -/
theorem pencil_of_linS {f₁ f₂ f₃ : Matrix ι ι ℝ} {W : ℕ → ι ⊕ ι → Ω → ℝ} {xm : ι → ℝ}
    {z : ℕ → ι → Ω → ℝ} (hza : AdaptedV 𝔼 z) (hWa : AdaptedV 𝔼 W)
    (h : SolvesLinS 𝔼 f₁ f₂ f₃
      (fun t => (fun i => W t (Sum.inl i)) - mv f₁ (lagP 0 (fun s j => W s (Sum.inr j)) t))
      xm z) :
    SolvesPencil 𝔼 (compA0 f₃) (compA1 f₁ f₂) W
      (fun t => Sum.elim (z t) (lagP xm z t + lagP 0 (fun s j => W s (Sum.inr j)) t)) := by
  intro t
  rw [comp_stepS]
  constructor
  · simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 := h t
    beta_reduce at h1
    rw [eq_sub_iff_add_eq] at h1
    have hl : (fun i => (lagP xm z t + lagP 0 (fun s j => W s (Sum.inr j)) t) i) =
        lagP xm z t + lagP 0 (fun s j => W s (Sum.inr j)) t := rfl
    rw [hl, mv_add, ← h1]
    abel
  · funext i
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, lagP_succ, map_add, hza t i,
      hWa t (Sum.inr i)]

/-- **(A.13) as a Blanchard–Kahn pencil under uncertainty** (Woodford (2003), App. A.3,
pp. 633–634): the stochastic linearised system is determinate iff its companion pencil
`A₀ E_t y_{t+1} = A₁ y_t + w_t`, `y_t = (x_t, x_{t−1})`, is determinate under the same
expectation system. -/
theorem linDeterminateS_iff_pencil (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    LinDeterminateS 𝔼 f₁ f₂ f₃ ↔ DeterminatePencil 𝔼 (compA0 f₃) (compA1 f₁ f₂) := by
  constructor
  · intro hL W hWb hWa x0
    set b : ℕ → ι → Ω → ℝ := fun s j => W s (Sum.inr j) with hb
    have hbb : BoundedV b := by
      obtain ⟨M, hM⟩ := hWb; exact ⟨M, fun t j ω => hM t _ ω⟩
    have hba : AdaptedV 𝔼 b := fun t j => hWa t (Sum.inr j)
    have hab : BoundedV (fun t i => W t (Sum.inl i)) := by
      obtain ⟨M, hM⟩ := hWb; exact ⟨M, fun t j ω => hM t _ ω⟩
    have haa : AdaptedV 𝔼 (fun t i => W t (Sum.inl i)) := fun t i => hWa t (Sum.inl i)
    obtain ⟨x, ⟨hxb, hxa, hx⟩, hxu⟩ := hL (fun t => (fun i => W t (Sum.inl i)) -
      mv f₁ (lagP 0 b t)) (boundedV_sub hab (boundedV_mv f₁ (boundedV_lagP 0 hbb)))
      (adaptedV_sub 𝔼 haa (adaptedV_mv 𝔼 f₁ (adaptedV_lagP 𝔼 0 hba))) x0
    refine ⟨fun t => Sum.elim (x t) (lagP x0 x t + lagP 0 b t),
      ⟨pencil_of_linS 𝔼 hxa hWa hx, ?_, ?_, ?_, ?_⟩, fun y' hy' => ?_⟩
    · intro t k
      rcases k with i | j
      · exact hxa t i
      · exact (adaptedV_add 𝔼 (adaptedV_lagP 𝔼 x0 hxa) (adaptedV_lagP 𝔼 0 hba)) t j
    · intro t j
      change 𝔼.E t (x t j + b t j) = x t j + b t j
      rw [map_add, hxa t j, hba t j]
    · intro j
      funext ω
      simp [b]
    · obtain ⟨M1, hM1⟩ := hxb
      obtain ⟨M2, hM2⟩ := boundedV_add (boundedV_lagP x0 ⟨M1, hM1⟩) (boundedV_lagP 0 hbb)
      refine ⟨max M1 M2, fun t k ω => ?_⟩
      rcases k with i | j
      · exact (hM1 t i ω).trans (le_max_left _ _)
      · exact (hM2 t j ω).trans (le_max_right _ _)
    · obtain ⟨hs, ha, hk, h0, hbd⟩ := hy'
      obtain ⟨hkt, hsol⟩ := lin_of_pencilS 𝔼 hs hk h0
      have hz : (fun s i => y' s (Sum.inl i)) = x := hxu _ ⟨by
        obtain ⟨M, hM⟩ := hbd; exact ⟨M, fun t i ω => hM t _ ω⟩,
        fun t i => ha t (Sum.inl i), hsol⟩
      funext t k
      rcases k with i | j
      · exact congrFun (congrFun hz t) i
      · have := congrFun (hkt t) j
        rw [hz] at this
        exact this
  · intro hD w hwb hwa xm
    set W : ℕ → ι ⊕ ι → Ω → ℝ := fun t => Sum.elim (w t) 0 with hW
    have hWb : BoundedV W := by
      obtain ⟨M, hM⟩ := hwb
      refine ⟨max M 0, fun t k ω => ?_⟩
      rcases k with i | j
      · exact (hM t i ω).trans (le_max_left _ _)
      · simp [hW]
    have hWa : AdaptedV 𝔼 W := by
      intro t k
      rcases k with i | j
      · exact hwa t i
      · change 𝔼.E t 0 = 0
        exact map_zero _
    have hb0 : (fun s j => W s (Sum.inr j)) = (0 : ℕ → ι → Ω → ℝ) := rfl
    have hforce : (fun t => (fun i => W t (Sum.inl i)) -
        mv f₁ (lagP 0 (fun s j => W s (Sum.inr j)) t)) = w := by
      funext t
      rw [hb0, lagP_zero_zero, mv_zero, sub_zero]
      rfl
    obtain ⟨y, ⟨hs, ha, hk, h0, hbd⟩, hyu⟩ := hD W hWb hWa xm
    obtain ⟨-, hsol⟩ := lin_of_pencilS 𝔼 hs hk h0
    rw [hforce] at hsol
    refine ⟨fun s i => y s (Sum.inl i), ⟨by
      obtain ⟨M, hM⟩ := hbd; exact ⟨M, fun t i ω => hM t _ ω⟩,
      fun t i => ha t (Sum.inl i), hsol⟩, fun x' ⟨hx'b, hx'a, hx'⟩ => ?_⟩
    rw [← hforce] at hx'
    have he := hyu _ ⟨pencil_of_linS 𝔼 hx'a hWa hx', ?_, ?_, ?_, ?_⟩
    · funext t i
      rw [← he]
      rfl
    · intro t k
      rcases k with i | j
      · exact hx'a t i
      · rw [hb0]
        exact (adaptedV_add 𝔼 (adaptedV_lagP 𝔼 xm hx'a)
          (adaptedV_lagP 𝔼 0 (fun _ _ => map_zero _))) t j
    · intro t j
      change 𝔼.E t (x' t j + (0 : ℕ → ι → Ω → ℝ) t j) = x' t j + (0 : ℕ → ι → Ω → ℝ) t j
      rw [map_add, hx'a t j]
      simp
    · intro j
      funext ω
      simp
    · obtain ⟨M1, hM1⟩ := hx'b
      obtain ⟨M2, hM2⟩ := boundedV_add (boundedV_lagP xm ⟨M1, hM1⟩)
        (boundedV_lagP 0 (⟨0, fun _ _ _ => by simp⟩ : BoundedV (0 : ℕ → ι → Ω → ℝ)))
      refine ⟨max M1 M2, fun t k ω => ?_⟩
      rcases k with i | j
      · exact (hM1 t i ω).trans (le_max_left _ _)
      · rw [hb0]
        exact (hM2 t j ω).trans (le_max_right _ _)

omit [DecidableEq ι] in
/-- **Uncertainty does not change the determinacy criterion** (Woodford (2003), App. A.3,
pp. 633–634, (A.12)–(A.13)): for every expectation system on a nonempty state space, the
stochastic system `f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = w_t` is determinate iff the
perfect-foresight system (A.10) is. -/
theorem linDeterminateS_iff_pf [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    LinDeterminateS 𝔼 f₁ f₂ f₃ ↔ LinDeterminate f₁ f₂ f₃ := by
  classical
  rw [linDeterminateS_iff_pencil, linDeterminate_iff_pencil, determinatePencil_iff_general,
    determinatePencil_iff_general]

/-- **The exact root condition under uncertainty** (Woodford (2003), App. A.3, eqs. (A.9) and
(A.12)–(A.13), pp. 632–634): for every expectation system on a nonempty state space, (A.13) is
determinate iff `det(f₃λ² + f₂λ + f₁) ≢ 0`, no root lies on the unit circle, exactly `n` roots
lie in the open unit disc, and genericity holds — the same condition as under perfect
foresight. -/
theorem linDeterminateS_iff_roots [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    LinDeterminateS 𝔼 f₁ f₂ f₃ ↔ quadPoly f₁ f₂ f₃ ≠ 0 ∧
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ HomInjective f₁ f₂ f₃ := by
  rw [linDeterminateS_iff_pf, linDeterminate_iff]

/-- Woodford (2003), App. A.3, pp. 632–634: the perfect-foresight operator (A.8) on
`ℓ∞(ℕ, ℝⁿ)` is invertible iff the stochastic system (A.13) is determinate, for any expectation
system on a nonempty state space. -/
theorem isUnit_sysOp_iff_stoch [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    IsUnit (sysOp f₁ f₂ f₃) ↔ LinDeterminateS 𝔼 f₁ f₂ f₃ := by
  rw [isUnit_sysOp_iff, linDeterminateS_iff_pf]

/-! ### Perfect foresight inside uncertainty: deterministic processes and projections -/

/-- Woodford (2003), App. A.3, p. 634: a deterministic sequence of vectors as a vector process
(the same value in every state of the world). -/
def detP (Y : ℕ → ι → ℝ) : ℕ → ι → Ω → ℝ := fun t i _ => Y t i

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: a deterministic process is adapted. -/
theorem adaptedV_detP (Y : ℕ → ι → ℝ) : AdaptedV 𝔼 (detP Y : ℕ → ι → Ω → ℝ) :=
  fun t i => 𝔼.const t (Y t i)

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: a bounded deterministic sequence is a bounded process. -/
theorem boundedV_detP {Y : ℕ → ι → ℝ} (hY : LinearSystems.BoundedSeq Y) :
    BoundedV (detP Y : ℕ → ι → Ω → ℝ) := by
  obtain ⟨C, hC⟩ := hY
  exact ⟨C, fun t i _ => hC t i⟩

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): a matrix acting on a deterministic vector. -/
theorem mv_cst (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    mv M (fun i (_ : Ω) => v i) = fun i _ => (M *ᵥ v) i := by
  funext i ω
  rw [mv_apply]

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: **a deterministic process solves the stochastic system
iff it solves the perfect-foresight system** (expectations of known values are those values). -/
theorem solvesLinS_detP_iff [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) (W Y : ℕ → ι → ℝ)
    (xm : ι → ℝ) :
    SolvesLinS 𝔼 f₁ f₂ f₃ (detP W) xm (detP Y) ↔ SolvesLin f₁ f₂ f₃ W xm Y := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hl : ∀ t, lagP xm (detP Y : ℕ → ι → Ω → ℝ) t = fun i _ => lagV xm Y t i := by
    intro t
    cases t <;> rfl
  have hE : ∀ t, (fun i => 𝔼.E t ((detP Y : ℕ → ι → Ω → ℝ) (t + 1) i)) =
      fun i _ => Y (t + 1) i := fun t => funext fun i => 𝔼.const t _
  refine forall_congr' fun t => ?_
  rw [hl, hE]
  change mv f₁ (fun i (_ : Ω) => lagV xm Y t i) + mv f₂ (fun i (_ : Ω) => Y t i) +
    mv f₃ (fun i (_ : Ω) => Y (t + 1) i) = (fun i _ => W t i) ↔ _
  rw [mv_cst, mv_cst, mv_cst]
  constructor
  · intro h
    funext i
    have := congrFun (congrFun h i) ω₀
    simpa only [Pi.add_apply] using this
  · intro h
    funext i ω
    simp only [Pi.add_apply]
    rw [← h]
    rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: **projection onto date-`k` information**: if `x` is an
adapted solution of the stochastic system, then in every state `ω` the sequence of forecasts
`s ↦ E_k x_{k+s}(ω)` solves the perfect-foresight system with forcing `E_k w_{k+s}(ω)` and initial
condition `x_{k−1}(ω)` (law of iterated expectations). -/
theorem proj_solves {f₁ f₂ f₃ : Matrix ι ι ℝ} {w x : ℕ → ι → Ω → ℝ} {xm : ι → ℝ}
    (hxa : AdaptedV 𝔼 x) (hx : SolvesLinS 𝔼 f₁ f₂ f₃ w xm x) (k : ℕ) (ω : Ω) :
    SolvesLin f₁ f₂ f₃ (fun s i => 𝔼.E k (w (k + s) i) ω) (fun i => lagP xm x k i ω)
      (fun s i => 𝔼.E k (x (k + s) i) ω) := by
  intro s
  funext i
  have h := congrArg (fun a : ι → Ω → ℝ => 𝔼.E k (a i) ω) (hx (k + s))
  simp only [Pi.add_apply, map_add, E_mv 𝔼] at h
  rw [mv_apply, mv_apply, mv_apply] at h
  have h3 : (fun j => 𝔼.E k (𝔼.E (k + s) (x (k + s + 1) j)) ω) =
      fun j => 𝔼.E k (x (k + (s + 1)) j) ω := by
    funext j
    rw [𝔼.tower (Nat.le_add_right k s), add_assoc]
  have h1 : (fun j => 𝔼.E k (lagP xm x (k + s) j) ω) =
      lagV (fun i => lagP xm x k i ω) (fun s i => 𝔼.E k (x (k + s) i) ω) s := by
    funext j
    cases s with
    | zero => exact congrFun (adaptedV_lagP 𝔼 xm hxa k j) ω
    | succ s => rfl
  rw [h3, h1] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): forecasts of a bounded process are bounded. -/
theorem boundedSeq_proj {x : ℕ → ι → Ω → ℝ} (hx : BoundedV x) (k : ℕ) (ω : Ω) :
    LinearSystems.BoundedSeq (fun s i => 𝔼.E k (x (k + s) i) ω) := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨C, fun s i => 𝔼.abs_E_le (hC (k + s) i) k ω⟩

/-- Woodford (2003), App. A.3, pp. 633–634: uniqueness under uncertainty — the homogeneous
system with `x_{−1} = 0` has no nonzero bounded adapted solution. -/
def HomInjectiveS (f₁ f₂ f₃ : Matrix ι ι ℝ) : Prop :=
  ∀ x, BoundedV x → AdaptedV 𝔼 x → SolvesLinS 𝔼 f₁ f₂ f₃ 0 0 x → x = 0

omit [DecidableEq ι] in
/-- **Uniqueness under uncertainty is uniqueness under perfect foresight** (Woodford (2003),
App. A.3, pp. 633–634): for every expectation system on a nonempty state space, the
homogeneous stochastic system has no nonzero bounded adapted solution iff the perfect-foresight
genericity condition `HomInjective` holds. (Necessity: a deterministic solution is adapted;
sufficiency: project a solution on date-`k` information, by induction on `k`.) -/
theorem homInjectiveS_iff [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    HomInjectiveS 𝔼 f₁ f₂ f₃ ↔ HomInjective f₁ f₂ f₃ := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  constructor
  · intro h Y hYb hY
    have hs : SolvesLinS 𝔼 f₁ f₂ f₃ (detP 0) 0 (detP Y) :=
      (solvesLinS_detP_iff 𝔼 _ _ _ _ _ _).mpr hY
    have h0 := h _ (boundedV_detP hYb) (adaptedV_detP 𝔼 Y) hs
    funext t i
    exact congrFun (congrFun (congrFun h0 t) i) ω₀
  · intro h x hxb hxa hx
    have key : ∀ k, (∀ j < k, x j = 0) → x k = 0 := by
      intro k hk
      funext i ω
      have hlag : (fun i => lagP 0 x k i ω) = 0 := by
        funext j
        cases k with
        | zero => rfl
        | succ k => simp [hk k (Nat.lt_succ_self k)]
      have hp := proj_solves 𝔼 hxa hx k ω
      rw [hlag] at hp
      have hw : (fun s i => 𝔼.E k ((0 : ℕ → ι → Ω → ℝ) (k + s) i) ω) = 0 := by
        funext s j
        simp
      rw [hw] at hp
      have := congrFun (congrFun (h _ (boundedSeq_proj 𝔼 hxb k ω) hp) 0) i
      simpa [hxa k i] using this
    funext k
    induction k using Nat.strong_induction_on with
    | _ k ih => exact key k ih

/-- Woodford (2003), App. A.3, pp. 633–634: **non-existence under uncertainty** — some bounded
deterministic forcing admits no bounded (adapted or not) solution with `x_{−1} = 0`. -/
def NonexistS (f₁ f₂ f₃ : Matrix ι ι ℝ) : Prop :=
  ∃ W : ℕ → ι → ℝ, LinearSystems.BoundedSeq W ∧
    ∀ x, BoundedV x → ¬ SolvesLinS 𝔼 f₁ f₂ f₃ (detP W) 0 x

/-- Woodford (2003), App. A.3, pp. 633–634: **non-uniqueness under uncertainty** — the
homogeneous system with `x_{−1} = 0` has a nonzero bounded adapted solution. -/
def NonuniqueS (f₁ f₂ f₃ : Matrix ι ι ℝ) : Prop :=
  ∃ x, BoundedV x ∧ AdaptedV 𝔼 x ∧ SolvesLinS 𝔼 f₁ f₂ f₃ 0 0 x ∧ x ≠ 0

/-- Woodford (2003), App. A.3, pp. 632–634: non-uniqueness under uncertainty is exactly
non-injectivity of the perfect-foresight operator (A.8). -/
theorem nonuniqueS_iff [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    NonuniqueS 𝔼 f₁ f₂ f₃ ↔ ¬ Function.Injective (sysOp f₁ f₂ f₃) := by
  rw [← homInjective_iff_injective, ← homInjectiveS_iff 𝔼]
  constructor
  · rintro ⟨x, hxb, hxa, hx, hx0⟩ h
    exact hx0 (h x hxb hxa hx)
  · intro h
    simp only [HomInjectiveS, not_forall] at h
    obtain ⟨x, hxb, hxa, hx, hx0⟩ := h
    exact ⟨x, hxb, hxa, hx, hx0⟩

/-- Woodford (2003), App. A.3, pp. 632–634: non-existence under uncertainty (for some bounded
deterministic forcing) is exactly non-surjectivity of the perfect-foresight operator (A.8).
(If (A.8) is onto, the deterministic solution solves the stochastic system; if a bounded process
solves the stochastic system with deterministic forcing, its date-`0` forecasts solve (A.10).) -/
theorem nonexistS_iff [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    NonexistS 𝔼 f₁ f₂ f₃ ↔ ¬ Function.Surjective (sysOp f₁ f₂ f₃) := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  constructor
  · rintro ⟨W, hWb, hno⟩ hs
    obtain ⟨Y, hY⟩ := hs (toSeqV W hWb)
    have hYs := (sysOp_eq_iff _ _ _ _ _).mp hY
    exact hno _ (boundedV_detP (boundedSeq_coe Y))
      ((solvesLinS_detP_iff 𝔼 _ _ _ _ _ _).mpr hYs)
  · intro hns
    by_contra hne
    apply hns
    intro y
    have hyb := boundedSeq_coe y
    have hex : ∃ x, BoundedV x ∧ SolvesLinS 𝔼 f₁ f₂ f₃ (detP fun t => y t) 0 x := by
      by_contra hno
      push Not at hno
      exact hne ⟨fun t => y t, hyb, fun x hxb hx => hno x hxb hx⟩
    obtain ⟨x, hxb, hx⟩ := hex
    -- the date-`0` forecasts solve (A.10)
    set z : ℕ → ι → ℝ := fun s i => 𝔼.E 0 (x s i) ω₀ with hz
    have hzs : SolvesLin f₁ f₂ f₃ (fun t => y t) 0 z := by
      intro s
      funext i
      have h := congrArg (fun a : ι → Ω → ℝ => 𝔼.E 0 (a i) ω₀) (hx s)
      have hc : 𝔼.E 0 ((detP (fun t => (y t : ι → ℝ)) : ℕ → ι → Ω → ℝ) s i) =
          fun _ => y s i := 𝔼.const 0 _
      simp only [Pi.add_apply, map_add, E_mv 𝔼] at h
      rw [hc, mv_apply, mv_apply, mv_apply] at h
      have h3 : (fun j => 𝔼.E 0 (𝔼.E s (x (s + 1) j)) ω₀) = z (s + 1) := by
        funext j
        rw [𝔼.tower (Nat.zero_le s)]
      have h1 : (fun j => 𝔼.E 0 (lagP 0 x s j) ω₀) = lagV 0 z s := by
        funext j
        cases s with
        | zero => exact congrFun (𝔼.const 0 0) ω₀
        | succ s => rfl
      rw [h3, h1] at h
      exact h
    exact ⟨toSeqV z (boundedSeq_proj 𝔼 hxb 0 ω₀ |> fun h => by simpa using h),
      (sysOp_eq_iff _ _ _ _ _).mpr hzs⟩

/-- **A root of (A.9) on the unit circle destroys existence under uncertainty, for any `f₃`**
(Woodford (2003), App. A.3, eqs. (A.9), (A.13), pp. 632–634): some bounded deterministic forcing
admits no bounded solution of the stochastic system with `x_{−1} = 0`. -/
theorem stoch_nonexist_of_unit_root [Nonempty Ω] {f₁ f₂ f₃ : Matrix ι ι ℝ} {μ : ℂ}
    (hμ : μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots) (h1 : ‖μ‖ = 1) :
    NonexistS 𝔼 f₁ f₂ f₃ :=
  (nonexistS_iff 𝔼 f₁ f₂ f₃).mpr (LinearSystemsUnit.not_surjective_of_unit_root hμ h1)

/-- **Which half fails under uncertainty** (Woodford (2003), App. A.3, pp. 632–634): if the
stochastic system is not determinate, then (i) a root of (A.9) lies on the unit circle and
existence fails, or (ii) more than `n` roots lie inside and uniqueness fails, or (iii) no root
lies on the circle, fewer than `n` lie inside, and existence fails, or (iv) no root lies on the
circle, exactly `n` lie inside, and uniqueness fails (genericity) — exactly as under perfect
foresight, with deterministic witnesses. -/
theorem failure_cases_stoch [Nonempty Ω] {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (hfail : ¬ LinDeterminateS 𝔼 f₁ f₂ f₃) :
    (∃ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ = 1) ∧
        NonexistS 𝔼 f₁ f₂ f₃ ∨
      Fintype.card ι < Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) ∧ NonuniqueS 𝔼 f₁ f₂ f₃ ∨
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
        Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) < Fintype.card ι ∧ NonexistS 𝔼 f₁ f₂ f₃ ∨
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
        Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ NonuniqueS 𝔼 f₁ f₂ f₃ := by
  rw [linDeterminateS_iff_pf] at hfail
  rw [nonexistS_iff, nonuniqueS_iff]
  exact LinearSystemsUnit.failure_cases_general hfail

/-! ### Genuinely random sunspots -/

/-- Woodford (2003), App. A.3, p. 634: the sunspot process `x_0 = 0`, `x_{t+1} = ξ · Y_t`
built from a deterministic sequence `Y` and a random variable `ξ`. -/
def sunP (ξ : Ω → ℝ) (Y : ℕ → ι → ℝ) : ℕ → ι → Ω → ℝ :=
  lagV 0 (fun s i ω => Y s i * ξ ω)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): a matrix acting on `v · ξ`. -/
theorem mv_mul_xi (M : Matrix ι ι ℝ) (v : ι → ℝ) (ξ : Ω → ℝ) :
    mv M (fun i ω => v i * ξ ω) = fun i ω => (M *ᵥ v) i * ξ ω := by
  funext i ω
  rw [mv_apply_sum, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- **Random sunspot equilibria** (Woodford (2003), App. A.3, p. 634; the stochastic form of
non-uniqueness): if `ξ` is a bounded random variable revealed at date 1 (`E_1 ξ = ξ`) with
`E_0 ξ = 0`, and `Y` is a bounded solution of the homogeneous perfect-foresight system with
`x_{−1} = 0`, then `x_0 = 0`, `x_{t+1} = ξ Y_t` is a bounded adapted solution of the homogeneous
stochastic system with `x_{−1} = 0`. -/
theorem random_sunspot {f₁ f₂ f₃ : Matrix ι ι ℝ} {ξ : Ω → ℝ} {B : ℝ} (hξb : ∀ ω, |ξ ω| ≤ B)
    (hξ0 : 𝔼.E 0 ξ = 0) (hξ1 : 𝔼.E 1 ξ = ξ) {Y : ℕ → ι → ℝ} (hYb : LinearSystems.BoundedSeq Y)
    (hY : SolvesLin f₁ f₂ f₃ 0 0 Y) :
    BoundedV (sunP ξ Y) ∧ AdaptedV 𝔼 (sunP ξ Y) ∧ SolvesLinS 𝔼 f₁ f₂ f₃ 0 0 (sunP ξ Y) := by
  have hξt : ∀ t, 𝔼.E (t + 1) ξ = ξ := fun t => by
    rw [← hξ1, 𝔼.known (by omega : 1 ≤ t + 1)]
  have hEs : ∀ t (v : ι → ℝ), (fun i => 𝔼.E (t + 1) (fun ω => v i * ξ ω)) =
      fun i ω => v i * ξ ω := by
    intro t v
    funext i
    have : (fun ω => v i * ξ ω) = v i • ξ := rfl
    rw [this, map_smul, hξt]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hYb
    refine ⟨max C 0 * max B 0, fun t i ω => ?_⟩
    cases t with
    | zero =>
      change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      positivity
    | succ t =>
      change |Y t i * ξ ω| ≤ _
      rw [abs_mul]
      exact mul_le_mul ((hC t i).trans (le_max_left _ _)) ((hξb ω).trans (le_max_left _ _))
        (abs_nonneg _) (le_max_right _ _)
  · intro t i
    cases t with
    | zero => exact map_zero _
    | succ t => exact congrFun (hEs t (Y t)) i
  · intro t
    cases t with
    | zero =>
      have h1 : (fun i => 𝔼.E 0 (sunP ξ Y (0 + 1) i)) = 0 := by
        funext i
        change 𝔼.E 0 (Y 0 i • ξ) = 0
        rw [map_smul, hξ0, smul_zero]
      rw [h1]
      have h2 : lagP (0 : ι → ℝ) (sunP ξ Y) 0 = 0 := rfl
      have h3 : sunP ξ Y 0 = 0 := rfl
      rw [h2, h3, mv_zero, mv_zero, mv_zero, add_zero, add_zero]
      rfl
    | succ t =>
      have h1 : (fun i => 𝔼.E (t + 1) (sunP ξ Y (t + 1 + 1) i)) =
          fun i ω => Y (t + 1) i * ξ ω := hEs t (Y (t + 1))
      have h2 : lagP (0 : ι → ℝ) (sunP ξ Y) (t + 1) = fun i ω => lagV 0 Y t i * ξ ω := by
        funext i ω
        cases t with
        | zero => simp [sunP, lagP]
        | succ t => rfl
      have h3 : sunP ξ Y (t + 1) = fun i ω => Y t i * ξ ω := rfl
      rw [h1, h2, h3, mv_mul_xi, mv_mul_xi, mv_mul_xi]
      funext i ω
      have := congrFun (hY t) i
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      rw [← add_mul, ← add_mul, this, zero_mul]

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): if genericity fails, the homogeneous
perfect-foresight system with `x_{−1} = 0` has a bounded solution with `x_0 ≠ 0` (drop the
leading zeros of a nonzero solution). -/
theorem exists_homog_head {f₁ f₂ f₃ : Matrix ι ι ℝ} (h : ¬ HomInjective f₁ f₂ f₃) :
    ∃ Y : ℕ → ι → ℝ, LinearSystems.BoundedSeq Y ∧ SolvesLin f₁ f₂ f₃ 0 0 Y ∧ Y 0 ≠ 0 := by
  simp only [HomInjective, not_forall] at h
  obtain ⟨Z, hZb, hZ, hZ0⟩ := h
  have hex : ∃ t, Z t ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hZ0 (funext hne)
  classical
  set s := Nat.find hex with hs
  have hsZ : Z s ≠ 0 := Nat.find_spec hex
  have hmin : ∀ j < s, Z j = 0 := fun j hj => by
    by_contra hne
    exact Nat.find_min hex hj hne
  refine ⟨fun t => Z (s + t), ?_, fun t => ?_, by simpa using hsZ⟩
  · obtain ⟨C, hC⟩ := hZb
    exact ⟨C, fun t i => hC (s + t) i⟩
  · have e := hZ (s + t)
    have hl : lagV 0 (fun t => Z (s + t)) t = lagV 0 Z (s + t) := by
      cases t with
      | zero =>
        cases hs' : s with
        | zero => rfl
        | succ s' =>
          simp only [lagV_zero, Nat.add_zero, lagV_succ]
          exact (hmin s' (by omega)).symm
      | succ t => rfl
    rw [hl]
    beta_reduce
    rw [show s + (t + 1) = s + t + 1 by omega]
    exact e

/-- Woodford (2003), App. A.3, p. 634 (tool): the date-1 coin innovation `±1` is revealed at
date 1 on the core coin-flip tree. -/
theorem coinShock_one_known :
    ExpectationsFiniteTree.coinSystem.E 1 (ExpectationsFiniteTree.coinShock 1) =
      ExpectationsFiniteTree.coinShock 1 := by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
    ExpectationsFiniteTree.coinShock_measurable 1 h

omit [DecidableEq ι] in
/-- **Genuinely random sunspots on the coin-flip tree** (Woodford (2003), App. A.3, p. 634):
if genericity fails (the homogeneous perfect-foresight system has a nonzero bounded solution),
then on the core two-coin tree the homogeneous stochastic system with `x_{−1} = 0` has, for every
scale `c ≠ 0`, a bounded adapted solution with `x_0 = 0` whose date-1 value differs across the
first coin flip (it is not a deterministic path). -/
theorem coin_random_sunspot {f₁ f₂ f₃ : Matrix ι ι ℝ} (h : ¬ HomInjective f₁ f₂ f₃) {c : ℝ}
    (hc : c ≠ 0) :
    ∃ x : ℕ → ι → Bool × Bool → ℝ, BoundedV x ∧
      AdaptedV ExpectationsFiniteTree.coinSystem x ∧
      SolvesLinS ExpectationsFiniteTree.coinSystem f₁ f₂ f₃ 0 0 x ∧ x 0 = 0 ∧
      (fun i => x 1 i (true, true)) ≠ fun i => x 1 i (false, true) := by
  obtain ⟨Y, hYb, hY, hY0⟩ := exists_homog_head h
  have hcY : SolvesLin f₁ f₂ f₃ 0 0 (fun t => c • Y t) := by
    intro t
    have e := hY t
    have hl : lagV 0 (fun t => c • Y t) t = c • lagV 0 Y t := by
      cases t <;> simp
    rw [hl, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, ← smul_add, e]
    simp
  have hcYb : LinearSystems.BoundedSeq (fun t => c • Y t) := by
    obtain ⟨C, hC⟩ := hYb
    exact ⟨|c| * C, fun t i => by
      change |c * Y t i| ≤ _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC t i) (abs_nonneg c)⟩
  have hξb : ∀ ω, |ExpectationsFiniteTree.coinShock 1 ω| ≤ 1 := fun ω => by
    unfold ExpectationsFiniteTree.coinShock
    split_ifs <;> simp
  obtain ⟨hb, ha, hs⟩ := random_sunspot ExpectationsFiniteTree.coinSystem hξb
    (ExpectationsFiniteTree.coinShock_mean_zero 0) coinShock_one_known hcYb hcY
  refine ⟨_, hb, ha, hs, rfl, fun he => hY0 ?_⟩
  funext i
  have e1 : c * Y 0 i * ExpectationsFiniteTree.coinShock 1 (true, true) =
      c * Y 0 i * ExpectationsFiniteTree.coinShock 1 (false, true) := congrFun he i
  have h1 : ExpectationsFiniteTree.coinShock 1 (true, true) = 1 := by
    simp [ExpectationsFiniteTree.coinShock]
  have hm1 : ExpectationsFiniteTree.coinShock 1 (false, true) = -1 := by
    simp [ExpectationsFiniteTree.coinShock]
  rw [h1, hm1] at e1
  have h2 : c * Y 0 i = 0 := by linarith
  simpa [hc] using h2

/-- **Too many stable roots: random sunspots under uncertainty** (Woodford (2003), App. A.3,
pp. 632–634): if more than `n` roots of `det(f₃λ² + f₂λ + f₁)` lie in the open unit disc, the
conclusion of `coin_random_sunspot` holds. -/
theorem coin_random_sunspot_of_count_gt {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (h : Fintype.card ι < Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
      (fun μ => ‖μ‖ < 1))) {c : ℝ} (hc : c ≠ 0) :
    ∃ x : ℕ → ι → Bool × Bool → ℝ, BoundedV x ∧
      AdaptedV ExpectationsFiniteTree.coinSystem x ∧
      SolvesLinS ExpectationsFiniteTree.coinSystem f₁ f₂ f₃ 0 0 x ∧ x 0 = 0 ∧
      (fun i => x 1 i (true, true)) ≠ fun i => x 1 i (false, true) :=
  coin_random_sunspot (fun hh => not_injective_of_count_gt h
    ((homInjective_iff_injective f₁ f₂ f₃).mp hh)) hc

/-! ### The Blanchard–Kahn decision rule -/

/-- Woodford (2003), App. A.3, p. 633: **the stable solvent of (A.10)**. If the
perfect-foresight system is determinate, there is a matrix `G` with bounded powers solving
`f₁ + f₂ G + f₃ G² = 0` such that the unique bounded solution of the homogeneous system with
initial condition `x_{−1} = v` is `x_t = G^{t+1} v`. -/
theorem exists_solvent {f₁ f₂ f₃ : Matrix ι ι ℝ} (hL : LinDeterminate f₁ f₂ f₃) :
    ∃ G : Matrix ι ι ℝ, f₁ + f₂ * G + f₃ * G ^ 2 = 0 ∧ (∃ C, ∀ t i j, |(G ^ t) i j| ≤ C) ∧
      ∀ (v : ι → ℝ) (Y : ℕ → ι → ℝ), LinearSystems.BoundedSeq Y → SolvesLin f₁ f₂ f₃ 0 v Y →
        ∀ t, Y t = G ^ (t + 1) *ᵥ v := by
  have h0b : LinearSystems.BoundedSeq (0 : ℕ → ι → ℝ) := ⟨0, fun _ _ => by simp⟩
  choose X hX using fun j : ι => (hL 0 h0b (Pi.single j 1)).exists
  choose C hC using fun j => (hX j).1
  set Φ : (ι → ℝ) → ℕ → ι → ℝ := fun v t => ∑ j, v j • X j t with hΦ
  have hlag : ∀ v t, lagV v (Φ v) t = ∑ j, v j • lagV (Pi.single j 1) (X j) t := by
    intro v t
    cases t with
    | zero =>
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    | succ t => rfl
  have hΦs : ∀ v, SolvesLin f₁ f₂ f₃ 0 v (Φ v) := by
    intro v t
    have e : f₁ *ᵥ lagV v (Φ v) t + f₂ *ᵥ Φ v t + f₃ *ᵥ Φ v (t + 1) =
        ∑ j, v j • (f₁ *ᵥ lagV (Pi.single j 1) (X j) t + f₂ *ᵥ X j t + f₃ *ᵥ X j (t + 1)) := by
      rw [hlag v t]
      simp only [hΦ, Matrix.mulVec_sum, Matrix.mulVec_smul, smul_add, Finset.sum_add_distrib]
    rw [e]
    simp [(hX _).2 t]
  have hΦb : ∀ v, LinearSystems.BoundedSeq (Φ v) := by
    intro v
    refine ⟨∑ j, |v j| * C j, fun t i => ?_⟩
    simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC j t i) (abs_nonneg _)
  have huniq : ∀ v Y, LinearSystems.BoundedSeq Y → SolvesLin f₁ f₂ f₃ 0 v Y → Y = Φ v :=
    fun v Y hYb hY => (hL 0 h0b v).unique ⟨hYb, hY⟩ ⟨hΦb v, hΦs v⟩
  set G : Matrix ι ι ℝ := Matrix.of fun i j => X j 0 i with hG
  have hG0 : ∀ v, Φ v 0 = G *ᵥ v := by
    intro v
    funext i
    simp [hΦ, hG, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hshift : ∀ v t, Φ v (t + 1) = Φ (G *ᵥ v) t := by
    intro v
    have hs : SolvesLin f₁ f₂ f₃ 0 (G *ᵥ v) (fun t => Φ v (t + 1)) := by
      intro t
      have e := hΦs v (t + 1)
      have hl : lagV (G *ᵥ v) (fun t => Φ v (t + 1)) t = lagV v (Φ v) (t + 1) := by
        cases t with
        | zero => exact (hG0 v).symm
        | succ t => rfl
      rw [hl]
      exact e
    have h := huniq (G *ᵥ v) _ (boundedSeq_succ (hΦb v)) hs
    exact fun t => congrFun h t
  have hpow : ∀ t v, Φ v t = G ^ (t + 1) *ᵥ v := by
    intro t
    induction t with
    | zero => intro v; rw [hG0, zero_add, pow_one]
    | succ t ih => intro v; rw [hshift, ih, Matrix.mulVec_mulVec, ← pow_succ]
  refine ⟨G, ?_, ⟨1 + ∑ j, |C j|, fun t i j => ?_⟩, fun v Y hYb hY t => ?_⟩
  · refine matrix_eq_of_mulVec fun v => ?_
    have e := hΦs v 0
    rw [lagV_zero, hpow, hpow, zero_add, pow_one] at e
    rw [Matrix.zero_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    exact e
  · have hsum : |C j| ≤ ∑ j, |C j| :=
      Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    cases t with
    | zero =>
      rw [pow_zero, Matrix.one_apply]
      have h1 : (0 : ℝ) ≤ ∑ j, |C j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      split_ifs
      · rw [abs_one]; linarith
      · rw [abs_zero]; linarith
    | succ t =>
      have e : (G ^ (t + 1)) i j = X j t i := by
        have h1 := congrFun (hpow t (Pi.single j 1)) i
        simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h1
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte] at h1
        rw [h1]
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [e]
      linarith [hC j t i, le_abs_self (C j)]
  · rw [huniq v Y hYb hY, hpow]

/-- Woodford (2003), eq. (A.9), p. 632 (tool): an eigenvector `c` of a solvent `G`
(`f₁ + f₂G + f₃G² = 0`) with eigenvalue `μ` is a null vector of `μ²f₃ + μf₂ + f₁`. -/
theorem quadMat_mulVec_of_solvent {f₁ f₂ f₃ G : Matrix ι ι ℝ}
    (hsol : f₁ + f₂ * G + f₃ * G ^ 2 = 0) {μ : ℂ} {c : ι → ℂ}
    (hc : G.map Complex.ofReal *ᵥ c = μ • c) :
    LinearSystemsUnit.quadMat f₁ f₂ f₃ μ *ᵥ c = 0 := by
  have hz : (Complex.ofRealHom.mapMatrix (f₁ + f₂ * G + f₃ * G ^ 2)) *ᵥ c = 0 := by
    rw [hsol, map_zero, Matrix.zero_mulVec]
  rw [map_add, map_add, map_mul, map_mul, map_pow] at hz
  change (f₁.map Complex.ofReal + f₂.map Complex.ofReal * G.map Complex.ofReal +
    f₃.map Complex.ofReal * G.map Complex.ofReal ^ 2) *ᵥ c = 0 at hz
  rw [Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    pow_two, ← Matrix.mulVec_mulVec] at hz
  simp only [hc, Matrix.mulVec_smul, smul_smul] at hz
  rw [LinearSystemsUnit.quadMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, ← hz, pow_two]
  abel

/-- Woodford (2003), App. A.3, p. 633: **the solvent is stable**: under determinacy every
eigenvalue of `G` lies in the open unit disc (bounded powers put them in the closed disc, and an
eigenvalue on the circle would be a unit-circle root of (A.9), destroying existence). -/
theorem solvent_stable {f₁ f₂ f₃ G : Matrix ι ι ℝ} (hL : LinDeterminate f₁ f₂ f₃)
    (hsol : f₁ + f₂ * G + f₃ * G ^ 2 = 0) {C : ℝ} (hb : ∀ t i j, |(G ^ t) i j| ≤ C) :
    ∀ μ ∈ eigs G, ‖μ‖ < 1 := by
  intro μ hμ
  rcases (norm_le_one_of_pow_bounded hb μ hμ).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
    have hdet : (LinearSystemsUnit.quadMat f₁ f₂ f₃ μ).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc0, quadMat_mulVec_of_solvent hsol hc⟩
    have hs : Function.Surjective (sysOp f₁ f₂ f₃) :=
      (ContinuousLinearMap.isUnit_iff_bijective.mp ((isUnit_sysOp_iff _ _ _).mpr hL)).2
    exact LinearSystemsUnit.not_surjective_of_unit_det hdet h hs

/-- Woodford (2003), App. A.3, p. 633: under determinacy `D = f₂ + f₃ G` is invertible (the
date-0 impulse response to a forcing `c` at date 0 solves `D x_0 = c`). -/
theorem isUnit_solventD {f₁ f₂ f₃ G : Matrix ι ι ℝ} (hL : LinDeterminate f₁ f₂ f₃)
    (hG : ∀ (v : ι → ℝ) (Y : ℕ → ι → ℝ), LinearSystems.BoundedSeq Y →
      SolvesLin f₁ f₂ f₃ 0 v Y → ∀ t, Y t = G ^ (t + 1) *ᵥ v) :
    IsUnit (f₂ + f₃ * G).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
  intro c
  set w : ℕ → ι → ℝ := fun t => if t = 0 then c else 0 with hw
  have hwb : LinearSystems.BoundedSeq w := ⟨∑ i, |c i|, fun t i => by
    by_cases ht : t = 0
    · simp only [hw, ht, ↓reduceIte]
      exact Finset.single_le_sum (f := fun i => |c i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    · simp only [hw, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _⟩
  obtain ⟨x, ⟨hxb, hx⟩, -⟩ := hL w hwb 0
  have htail : SolvesLin f₁ f₂ f₃ 0 (x 0) (fun t => x (t + 1)) := by
    intro t
    have e := hx (t + 1)
    have hl : lagV (x 0) (fun t => x (t + 1)) t = lagV 0 x (t + 1) := by
      cases t <;> rfl
    rw [hl]
    simpa [hw] using e
  have h1 := hG (x 0) _ (boundedSeq_succ hxb) htail 0
  rw [zero_add, pow_one] at h1
  refine ⟨x 0, ?_⟩
  have e0 := hx 0
  simp only [lagV_zero, Matrix.mulVec_zero, zero_add, hw, ↓reduceIte] at e0
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← h1]
  exact e0

/-- Woodford (2003), App. A.3, p. 633: **the unstable block is stable when solved forward**:
under determinacy every eigenvalue of `J = −D⁻¹f₃` lies in the open unit disc. (An eigenvalue
`μ` with `|μ| ≥ 1` gives the bounded sequence `ẑ_t = Re(μ⁻ᵗ c)` with `ẑ_t = J ẑ_{t+1}`, and
`x_t = G x_{t−1} + ẑ_t` would be a nonzero bounded solution of the homogeneous system with
`x_{−1} = 0`.) -/
theorem solventJ_stable {f₁ f₂ f₃ G : Matrix ι ι ℝ} (hL : LinDeterminate f₁ f₂ f₃)
    (hsol : f₁ + f₂ * G + f₃ * G ^ 2 = 0) (hGs : ∀ μ ∈ eigs G, ‖μ‖ < 1)
    (hD : IsUnit (f₂ + f₃ * G).det) :
    ∀ μ ∈ eigs (-((f₂ + f₃ * G)⁻¹ * f₃)), ‖μ‖ < 1 := by
  set D := f₂ + f₃ * G with hDdef
  set J := -(D⁻¹ * f₃) with hJ
  have hDJ : D * J = -f₃ := by
    rw [hJ, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD, Matrix.one_mul]
  intro μ hμ
  by_contra hge
  push Not at hge
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hge
    linarith
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  obtain ⟨c', ⟨i0, hi0⟩, hc'⟩ : ∃ c' : ι → ℂ, (∃ i, (c' i).re ≠ 0) ∧
      J.map Complex.ofReal *ᵥ c' = μ • c' := by
    by_cases hre : ∃ i, (c i).re ≠ 0
    · exact ⟨c, hre, hc⟩
    · push Not at hre
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hc0 (funext hne)
      refine ⟨(-Complex.I) • c, ⟨i, ?_⟩, ?_⟩
      · intro h0
        apply hi
        apply Complex.ext
        · simpa using hre i
        · simpa using h0
      · rw [Matrix.mulVec_smul, hc, smul_comm]
  set z : ℕ → ι → ℝ := fun t i => ((μ⁻¹) ^ t * c' i).re with hz
  have hzJ : ∀ t, J *ᵥ z (t + 1) = z t := by
    intro t
    funext i
    have e := re_mulVec J ((μ⁻¹) ^ (t + 1) • c') i
    rw [Matrix.mulVec_smul, hc', smul_smul] at e
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [hz]
    simp only
    rw [← e]
    congr 1
    rw [pow_succ, mul_assoc ((μ⁻¹) ^ t) μ⁻¹ μ, inv_mul_cancel₀ hμ0, mul_one]
  have hμinv : ‖μ⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hge
  have hzb : ∀ t i, |z t i| ≤ ∑ j, ‖c' j‖ := by
    intro t i
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow]
    calc ‖μ⁻¹‖ ^ t * ‖c' i‖ ≤ 1 * ‖c' i‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hμinv) (norm_nonneg _)
      _ ≤ ∑ j, ‖c' j‖ := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun j => ‖c' j‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hGp⟩ := pow_entry_bound G hGs
  set x := xrecV G (fun t => z (t + 1)) (z 0) with hx
  have hxrec : ∀ t, x t = G *ᵥ lagV 0 x t + z t := by
    intro t
    cases t with
    | zero => simp [hx, xrecV]
    | succ t => rfl
  have hB0 : 0 ≤ ∑ j, ‖c' j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hxb : LinearSystems.BoundedSeq x :=
    ⟨_, rec_bounded hCb hρ0.le hρ1 hGp (fun t => rfl) hB0 hB0 (fun t j => hzb (t + 1) j)
      (fun j => hzb 0 j)⟩
  have hxs : SolvesLin f₁ f₂ f₃ 0 0 x := by
    intro t
    set L := lagV 0 x t with hL'
    have h1 : x (t + 1) = G *ᵥ x t + z (t + 1) := rfl
    rw [h1, hxrec t, ← hL', ← hzJ t]
    have e : f₁ *ᵥ L + f₂ *ᵥ (G *ᵥ L + J *ᵥ z (t + 1)) +
        f₃ *ᵥ (G *ᵥ (G *ᵥ L + J *ᵥ z (t + 1)) + z (t + 1)) =
        (f₁ + f₂ * G + f₃ * G ^ 2) *ᵥ L + (D * J) *ᵥ z (t + 1) + f₃ *ᵥ z (t + 1) := by
      simp only [hDdef, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, pow_two,
        Matrix.mul_assoc, Matrix.add_mul]
      abel
    rw [e, hsol, hDJ, Matrix.neg_mulVec, Matrix.zero_mulVec]
    simp
  have hinj : HomInjective f₁ f₂ f₃ := ((linDeterminate_iff _ _ _).mp hL).2.2.2
  have hx0 := congrFun (congrFun (hinj x hxb hxs) 0) i0
  have hz0 : x 0 i0 = z 0 i0 := by simp [hx, xrecV]
  rw [hz0] at hx0
  apply hi0
  simpa [hz] using hx0

/-- **The Blanchard–Kahn decision rule** (Woodford (2003), App. A.3, pp. 632–634; Blanchard and
Kahn (1980)): if (A.10) is determinate there are matrices `G`, `D`, `J` with
`f₁ + f₂G + f₃G² = 0`, `D = f₂ + f₃G` invertible, `J = −D⁻¹f₃`, and every eigenvalue of `G` and
of `J` in the open unit disc. -/
theorem exists_decision_rule {f₁ f₂ f₃ : Matrix ι ι ℝ} (hL : LinDeterminate f₁ f₂ f₃) :
    ∃ G D J : Matrix ι ι ℝ, f₁ + f₂ * G + f₃ * G ^ 2 = 0 ∧ D = f₂ + f₃ * G ∧ IsUnit D.det ∧
      J = -(D⁻¹ * f₃) ∧ (∀ μ ∈ eigs G, ‖μ‖ < 1) ∧ ∀ μ ∈ eigs J, ‖μ‖ < 1 := by
  obtain ⟨G, hsol, ⟨C, hb⟩, hG⟩ := exists_solvent hL
  have hGs := solvent_stable hL hsol hb
  have hD := isUnit_solventD hL hG
  exact ⟨G, _, _, hsol, rfl, hD, rfl, hGs, solventJ_stable hL hsol hGs hD⟩

/-! ### The stochastic decision rule: stable block backward, unstable block forward with `E_t` -/

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634 (and (1.37), p. 70): the forward series
`ẑ_t = ∑_{k ≥ 0} Kᵏ E_t f_{t+k}` (the vector version of the core `forwardSeries`). -/
noncomputable def fwdV (K : Matrix ι ι ℝ) (f : ℕ → ι → Ω → ℝ) : ℕ → ι → Ω → ℝ :=
  fun t i ω => ∑' k, mv (K ^ k) (fun j => 𝔼.E t (f (t + k) j)) i ω

/-- Woodford (2003), App. A.3, eq. (A.13), p. 634 (Blanchard–Kahn forward step, restated from
`SystemsBK.GeneralBKForward.fsolves_exists` for an explicit series and forcing that need not be
adapted): if the powers of `K` decay geometrically and `f` is bounded, the forward series solves
`ẑ_t = K E_t ẑ_{t+1} + E_t f_t`, is adapted and is bounded; `E_t` commutes with the series by
`ExpectationSystem.E_tsum`. -/
theorem fwdV_spec {K : Matrix ι ι ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {f : ℕ → ι → Ω → ℝ} {Mw : ℝ}
    (hw : ∀ t i ω, |f t i ω| ≤ Mw) :
    (∀ t, fwdV 𝔼 K f t = mv K (fun j => 𝔼.E t (fwdV 𝔼 K f (t + 1) j)) +
        fun j => 𝔼.E t (f t j)) ∧ AdaptedV 𝔼 (fwdV 𝔼 K f) ∧ BoundedV (fwdV 𝔼 K f) := by
  set Mb : ℝ := Fintype.card ι * Cb * Mw with hMb
  set B : ℕ → ℕ → ι → Ω → ℝ := fun k t => mv (K ^ k) (fun j => 𝔼.E t (f (t + k) j)) with hB
  have hT : ∀ k t t' i ω, |mv (K ^ k) (fun j => 𝔼.E t (f t' j)) i ω| ≤ ρ ^ k * Mb := by
    intro k t t' i ω
    have := abs_mv_le (hK k) (fun j ω => 𝔼.abs_E_le (hw t' j) t ω) i ω
    calc _ ≤ Fintype.card ι * (Cb * ρ ^ k * Mw) := this
      _ = ρ ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ t t' : ℕ → ℕ, ∀ i ω,
      Summable fun k => mv (K ^ k) (fun j => 𝔼.E (t k) (f (t' k) j)) i ω := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ ρ ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  have hs : ∀ t i, fwdV 𝔼 K f t i = fun ω => ∑' k, B k t i ω := fun _ _ => rfl
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      mv (K ^ k) (fun j => 𝔼.E t (f (t + 1 + k) j)) i := by
    intro k t i
    simp only [hB, E_mv 𝔼, 𝔼.tower (Nat.le_succ t)]
  have hEs : ∀ t i ω, 𝔼.E t (fwdV 𝔼 K f (t + 1) i) ω =
      ∑' k, mv (K ^ k) (fun j => 𝔼.E t (f (t + 1 + k) j)) i ω := by
    intro t i ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k (t + 1) i) (fun k ω => hBb k (t + 1) i ω) t ω
    rw [hs, this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨?_, ?_, ?_⟩
  · intro t
    funext i ω
    have hB0 : B 0 t i ω = 𝔼.E t (f t i) ω := by
      simp only [hB, pow_zero, add_zero, mv_one]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, K i l * mv (K ^ k) (fun j => 𝔼.E t (f (t + 1 + k) j)) l ω := by
      intro k
      simp only [hB]
      rw [← mv_apply_sum, mv_mv, ← pow_succ', show t + (k + 1) = t + 1 + k by omega]
    have hR : (mv K (fun j => 𝔼.E t (fwdV 𝔼 K f (t + 1) j)) + fun j => 𝔼.E t (f t j)) i ω =
        (∑' k, B (k + 1) t i ω) + 𝔼.E t (f t i) ω := by
      rw [Pi.add_apply, Pi.add_apply, mv_apply_sum]
      congr 1
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ =>
        (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left (K i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR]
    change ∑' k, B k t i ω = _
    rw [(hsum t i ω).tsum_eq_zero_add, hB0]
    ring
  · intro t i
    funext ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k t i) (fun k ω => hBb k t i ω) t ω
    rw [hs, this]
    refine tsum_congr fun k => ?_
    simp only [hB, E_mv 𝔼, 𝔼.E_E_self]
  · refine ⟨Mb / (1 - ρ), fun t i ω => ?_⟩
    have hg : HasSum (fun k : ℕ => ρ ^ k * Mb) (Mb / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this

/-- Woodford (2003), App. A.3, p. 634: the backward recursion of the stable block,
`x_t = G x_{t−1} + ẑ_t` with `x_{−1}` given. -/
def bkRec (G : Matrix ι ι ℝ) (z : ℕ → ι → Ω → ℝ) (xm : ι → ℝ) : ℕ → ι → Ω → ℝ
  | 0 => mv G (fun i _ => xm i) + z 0
  | t + 1 => mv G (bkRec G z xm t) + z (t + 1)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: `x_t = G x_{t−1} + ẑ_t` at every date. -/
theorem bkRec_eq (G : Matrix ι ι ℝ) (z : ℕ → ι → Ω → ℝ) (xm : ι → ℝ) (t : ℕ) :
    bkRec G z xm t = mv G (lagP xm (bkRec G z xm) t) + z t := by
  cases t <;> rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the backward recursion of an adapted process is
adapted. -/
theorem bkRec_adapted (G : Matrix ι ι ℝ) {z : ℕ → ι → Ω → ℝ} (hz : AdaptedV 𝔼 z)
    (xm : ι → ℝ) : AdaptedV 𝔼 (bkRec G z xm) := by
  intro t
  induction t with
  | zero =>
    intro i
    change 𝔼.E 0 (mv G (fun i _ => xm i) i + z 0 i) = mv G (fun i _ => xm i) i + z 0 i
    rw [map_add, E_mv 𝔼, hz 0 i]
    congr 2
    funext j
    exact 𝔼.const 0 _
  | succ t ih =>
    intro i
    change 𝔼.E (t + 1) (mv G (bkRec G z xm t) i + z (t + 1) i) =
      mv G (bkRec G z xm t) i + z (t + 1) i
    rw [map_add, E_mv 𝔼, hz (t + 1) i]
    congr 2
    funext j
    rw [← ih j, 𝔼.known (Nat.le_succ t)]

/-- Woodford (2003), App. A.3, p. 634: the backward recursion is bounded when the powers of `G`
decay geometrically and `ẑ` is bounded. -/
theorem bkRec_bounded {G : Matrix ι ι ℝ} {Cb ρ : ℝ} (hCb : 0 ≤ Cb) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hG : ∀ k i j, |(G ^ k) i j| ≤ Cb * ρ ^ k) {z : ℕ → ι → Ω → ℝ} (hz : BoundedV z)
    (xm : ι → ℝ) : BoundedV (bkRec G z xm) := by
  obtain ⟨Mz, hMz⟩ := hz
  set X0 : ℝ := ∑ j, |(G *ᵥ xm) j| + max Mz 0 with hX0
  have hX0n : 0 ≤ X0 := add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (le_max_right _ _)
  refine ⟨Fintype.card ι * Cb * (X0 + max Mz 0 / (1 - ρ)), fun t i ω => ?_⟩
  have hrec : ∀ t, (fun j => bkRec G z xm (t + 1) j ω) =
      G *ᵥ (fun j => bkRec G z xm t j ω) + fun j => z (t + 1) j ω := by
    intro t
    funext j
    simp only [bkRec, Pi.add_apply, mv_apply]
  exact rec_bounded (x := fun t j => bkRec G z xm t j ω) (f := fun t j => z (t + 1) j ω) hCb hρ0
    hρ1 hG hrec (le_max_right _ _) hX0n (fun t j => (hMz (t + 1) j ω).trans (le_max_left _ _))
    (fun j => by
      change |mv G (fun i _ => xm i) j ω + z 0 j ω| ≤ X0
      rw [mv_apply]
      refine (abs_add_le _ _).trans (add_le_add ?_ ((hMz 0 j ω).trans (le_max_left _ _)))
      exact Finset.single_le_sum (f := fun j => |(G *ᵥ xm) j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)) t i

/-- Woodford (2003), App. A.3, pp. 633–634: **the stochastic Blanchard–Kahn solution**
`x_t = G x_{t−1} + ∑_{k ≥ 0} Jᵏ D⁻¹ E_t w_{t+k}`, `x_{−1} = xm`. -/
noncomputable def bkSol (G D J : Matrix ι ι ℝ) (w : ℕ → ι → Ω → ℝ) (xm : ι → ℝ) :
    ℕ → ι → Ω → ℝ :=
  bkRec G (fwdV 𝔼 J (fun t => mv D⁻¹ (w t))) xm

/-- **The decision rule solves the book form of (A.13)** (Woodford (2003), App. A.3,
pp. 633–634): if `f₁ + f₂G + f₃G² = 0`, `D = f₂ + f₃G` is invertible, `J = −D⁻¹f₃`, and the
powers of `G` and `J` decay geometrically, then for every bounded forcing `w` — adapted or not —
`bkSol` is a bounded adapted solution of `f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = E_t w_t`. -/
theorem bkSol_solves_book {f₁ f₂ f₃ G D J : Matrix ι ι ℝ} (hsol : f₁ + f₂ * G + f₃ * G ^ 2 = 0)
    (hDd : D = f₂ + f₃ * G) (hD : IsUnit D.det) (hJ : J = -(D⁻¹ * f₃)) {Cg ρg Cj ρj : ℝ}
    (hCg : 0 ≤ Cg) (hρg0 : 0 ≤ ρg) (hρg1 : ρg < 1) (hGp : ∀ k i j, |(G ^ k) i j| ≤ Cg * ρg ^ k)
    (hρj0 : 0 ≤ ρj) (hρj1 : ρj < 1) (hJp : ∀ k i j, |(J ^ k) i j| ≤ Cj * ρj ^ k)
    {w : ℕ → ι → Ω → ℝ} (hwb : BoundedV w) (xm : ι → ℝ) :
    BoundedV (bkSol 𝔼 G D J w xm) ∧ AdaptedV 𝔼 (bkSol 𝔼 G D J w xm) ∧
      SolvesLinS 𝔼 f₁ f₂ f₃ (fun t i => 𝔼.E t (w t i)) xm (bkSol 𝔼 G D J w xm) := by
  obtain ⟨Mf, hMf⟩ := boundedV_mv D⁻¹ hwb
  obtain ⟨hzs, hza, hzb⟩ := fwdV_spec 𝔼 hρj0 hρj1 hJp (f := fun t => mv D⁻¹ (w t)) hMf
  set z := fwdV 𝔼 J (fun t => mv D⁻¹ (w t)) with hzdef
  set x := bkSol 𝔼 G D J w xm with hx
  have hxa : AdaptedV 𝔼 x := bkRec_adapted 𝔼 G hza xm
  refine ⟨bkRec_bounded hCg hρg0 hρg1 hGp hzb xm, hxa, fun t => ?_⟩
  set L := lagP xm x t with hL
  set Ez : ι → Ω → ℝ := fun j => 𝔼.E t (z (t + 1) j) with hEz
  set Ew : ι → Ω → ℝ := fun j => 𝔼.E t (w t j) with hEw
  have hxt : x t = mv G L + z t := bkRec_eq G z xm t
  have hEx : (fun i => 𝔼.E t (x (t + 1) i)) = mv G (x t) + Ez := by
    funext i
    change 𝔼.E t (mv G (x t) i + z (t + 1) i) = _
    rw [map_add, E_mv 𝔼]
    congr 2
    funext j
    exact hxa t j
  have hzt : z t = mv J Ez + mv D⁻¹ Ew := by
    rw [hzs t]
    congr 1
    funext j
    exact E_mv 𝔼 t D⁻¹ (w t) j
  have hDinv : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
  have hDJ : D * J + f₃ = 0 := by
    rw [hJ, Matrix.mul_neg, ← Matrix.mul_assoc, hDinv, Matrix.one_mul, neg_add_cancel]
  have hDG : f₁ + D * G = 0 := by
    rw [hDd, Matrix.add_mul, ← hsol, Matrix.mul_assoc, pow_two]
    abel
  have h1 : mv f₂ (x t) + mv f₃ (mv G (x t)) = mv D (x t) := by
    rw [mv_mv, ← add_mv, hDd]
  have h2 : mv D (x t) = mv (D * G) L + (mv (D * J) Ez + Ew) := by
    rw [hxt, mv_add, mv_mv, hzt, mv_add, mv_mv, mv_mv, hDinv, mv_one]
  change mv f₁ L + mv f₂ (x t) + mv f₃ (fun i => 𝔼.E t (x (t + 1) i)) = Ew
  rw [hEx, mv_add, ← add_assoc, add_assoc (mv f₁ L), h1, h2]
  have e : mv f₁ L + (mv (D * G) L + (mv (D * J) Ez + Ew)) + mv f₃ Ez =
      mv (f₁ + D * G) L + mv (D * J + f₃) Ez + Ew := by
    rw [add_mv, add_mv]
    abel
  rw [e, hDG, hDJ, zero_mv, zero_mv, zero_add, zero_add]

/-- **The decision rule under uncertainty** (Woodford (2003), App. A.3, pp. 632–634;
Blanchard–Kahn): for every expectation system on a nonempty state space, if (A.13) is
determinate (equivalently the exact root condition holds) there are matrices `G`, `D`, `J` —
`f₁ + f₂G + f₃G² = 0`, `D = f₂ + f₃G` invertible, `J = −D⁻¹f₃`, every eigenvalue of `G` and of
`J` in the open unit disc — such that for every bounded forcing `w` (not necessarily adapted) and
every `x_{−1}`, the book form `f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = E_t w_t` has exactly one
bounded adapted solution, namely `x_t = G x_{t−1} + ∑_{k ≥ 0} Jᵏ D⁻¹ E_t w_{t+k}` (`bkSol`). -/
theorem decision_rule [Nonempty Ω] {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (hL : LinDeterminateS 𝔼 f₁ f₂ f₃) :
    ∃ G D J : Matrix ι ι ℝ, f₁ + f₂ * G + f₃ * G ^ 2 = 0 ∧ D = f₂ + f₃ * G ∧ IsUnit D.det ∧
      J = -(D⁻¹ * f₃) ∧ (∀ μ ∈ eigs G, ‖μ‖ < 1) ∧ (∀ μ ∈ eigs J, ‖μ‖ < 1) ∧
      ∀ w : ℕ → ι → Ω → ℝ, BoundedV w → ∀ xm : ι → ℝ,
        BoundedV (bkSol 𝔼 G D J w xm) ∧ AdaptedV 𝔼 (bkSol 𝔼 G D J w xm) ∧
        SolvesLinS 𝔼 f₁ f₂ f₃ (fun t i => 𝔼.E t (w t i)) xm (bkSol 𝔼 G D J w xm) ∧
        ∀ x, BoundedV x → AdaptedV 𝔼 x →
          SolvesLinS 𝔼 f₁ f₂ f₃ (fun t i => 𝔼.E t (w t i)) xm x → x = bkSol 𝔼 G D J w xm := by
  obtain ⟨G, D, J, hsol, hDd, hD, hJ, hGs, hJs⟩ :=
    exists_decision_rule ((linDeterminateS_iff_pf 𝔼 _ _ _).mp hL)
  obtain ⟨Cg, ρg, hCg, hρg0, hρg1, hGp⟩ := pow_entry_bound G hGs
  obtain ⟨Cj, ρj, -, hρj0, hρj1, hJp⟩ := pow_entry_bound J hJs
  refine ⟨G, D, J, hsol, hDd, hD, hJ, hGs, hJs, fun w hwb xm => ?_⟩
  obtain ⟨hb, ha, hs⟩ := bkSol_solves_book 𝔼 hsol hDd hD hJ hCg hρg0.le hρg1 hGp hρj0.le hρj1
    hJp hwb xm
  refine ⟨hb, ha, hs, fun x hxb hxa hx => ?_⟩
  have hEb : BoundedV (fun t i => 𝔼.E t (w t i)) := by
    obtain ⟨M, hM⟩ := hwb
    exact ⟨M, fun t i ω => 𝔼.abs_E_le (hM t i) t ω⟩
  have hEa : AdaptedV 𝔼 (fun t i => 𝔼.E t (w t i)) := fun t i => 𝔼.E_E_self t _
  exact (hL _ hEb hEa xm).unique ⟨hxb, hxa, hx⟩ ⟨hb, ha, hs⟩

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, eq. (A.11), p. 633 (**the book form**): for a bounded forcing
that need not be adapted (date-`t+1` shocks inside `E_t`), the stochastic system
`f₁ x_{t−1} + f₂ x_t + f₃ E_t x_{t+1} = E_t w_t` has exactly one bounded adapted solution for
every bounded `w` and every `x_{−1}` iff the exact root condition holds. -/
theorem book_form_iff [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    (∀ w : ℕ → ι → Ω → ℝ, BoundedV w → ∀ xm : ι → ℝ,
      ∃! x, BoundedV x ∧ AdaptedV 𝔼 x ∧
        SolvesLinS 𝔼 f₁ f₂ f₃ (fun t i => 𝔼.E t (w t i)) xm x) ↔
      LinDeterminateS 𝔼 f₁ f₂ f₃ := by
  classical
  constructor
  · intro h w hwb hwa xm
    have he : (fun t i => 𝔼.E t (w t i)) = w := funext fun t => funext fun i => hwa t i
    have := h w hwb xm
    rwa [he] at this
  · intro hL w hwb xm
    obtain ⟨G, D, J, -, -, -, -, -, -, h⟩ := decision_rule 𝔼 hL
    obtain ⟨hb, ha, hs, hu⟩ := h w hwb xm
    exact ⟨_, ⟨hb, ha, hs⟩, fun x ⟨hxb, hxa, hx⟩ => hu x hxb hxa hx⟩

/-! ### The linearised operator on `ℓ∞(ℕ × Ω, ℝⁿ)` -/

/-- Woodford (2003), App. A.3, p. 634: the Banach space of uniformly bounded vector processes
`x_t(ω) ∈ ℝⁿ` (sup over dates, states and coordinates); adaptedness is not built in. -/
abbrev SProcV (ι Ω : Type*) [Fintype ι] : Type _ := LocalIFTStochastic.BFun (ℕ × Ω) (ι → ℝ)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): each coordinate of a bounded vector process is
bounded by its norm. -/
theorem abs_apply_le (x : SProcV ι Ω) (t : ℕ) (ω : Ω) (i : ι) : |x (t, ω) i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (x (t, ω)) i).trans (LocalIFTStochastic.norm_apply_le x (t, ω))

/-- Woodford (2003), App. A.3, p. 634: an element of `ℓ∞(ℕ × Ω, ℝⁿ)` as a vector process. -/
def toP (x : SProcV ι Ω) : ℕ → ι → Ω → ℝ := fun t i ω => x (t, ω) i

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: elements of `ℓ∞(ℕ × Ω, ℝⁿ)` are bounded processes. -/
theorem boundedV_toP (x : SProcV ι Ω) : BoundedV (toP x) :=
  ⟨‖x‖, fun t i ω => abs_apply_le x t ω i⟩

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): a uniformly bounded vector process has a uniform
bound on its vector norms. -/
theorem exists_norm_boundV {x : ℕ → ι → Ω → ℝ} (hx : BoundedV x) :
    ∃ C, ∀ p : ℕ × Ω, ‖(fun i => x p.1 i p.2 : ι → ℝ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨max C 0, fun p => (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => by
    rw [Real.norm_eq_abs]
    exact (hC p.1 i p.2).trans (le_max_left _ _)⟩

/-- Woodford (2003), App. A.3, p. 634: a bounded vector process as an element of
`ℓ∞(ℕ × Ω, ℝⁿ)`. -/
noncomputable def ofP (x : ℕ → ι → Ω → ℝ) (hx : BoundedV x) : SProcV ι Ω :=
  LocalIFTStochastic.mkB (fun p i => x p.1 i p.2) (exists_norm_boundV hx)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: `toP` inverts `ofP`. -/
@[simp] theorem toP_ofP (x : ℕ → ι → Ω → ℝ) (hx : BoundedV x) : toP (ofP x hx) = x := rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: elements are determined by their processes. -/
theorem toP_injective {x y : SProcV ι Ω} (h : toP x = toP y) : x = y := by
  ext ⟨t, ω⟩ i
  exact congrFun (congrFun (congrFun h t) i) ω

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): processes of sums. -/
@[simp] theorem toP_add (x y : SProcV ι Ω) : toP (x + y) = toP x + toP y := rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): processes of differences. -/
@[simp] theorem toP_sub (x y : SProcV ι Ω) : toP (x - y) = toP x - toP y := rfl

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): the zero element is the zero process. -/
@[simp] theorem toP_zero : toP (0 : SProcV ι Ω) = 0 := rfl

/-- Woodford (2003), App. A.3, p. 634 (tool): a bounded operator on `ℓ∞(ℕ × Ω, ℝⁿ)` defined
pointwise by an additive, homogeneous formula with a linear bound. -/
noncomputable def mkOp (F : SProcV ι Ω → ℕ × Ω → (ι → ℝ)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x p, ‖F x p‖ ≤ C * ‖x‖) (hadd : ∀ x y, F (x + y) = F x + F y)
    (hsmul : ∀ (c : ℝ) x, F (c • x) = c • F x) : SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFTStochastic.mkB (F x) ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => lp.ext (funext fun p => by
        change F (x + y) p = F x p + F y p
        rw [hadd]
        rfl)
      map_smul' := fun c x => lp.ext (funext fun p => by
        change F (c • x) p = c • F x p
        rw [hsmul]
        rfl) }
    C (fun x => LocalIFTStochastic.norm_le_of_forall (by positivity) (hC x))

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): values of `mkOp`. -/
@[simp] theorem mkOp_apply (F : SProcV ι Ω → ℕ × Ω → (ι → ℝ)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x p, ‖F x p‖ ≤ C * ‖x‖) (hadd : ∀ x y, F (x + y) = F x + F y)
    (hsmul : ∀ (c : ℝ) x, F (c • x) = c • F x) (x : SProcV ι Ω) (p : ℕ × Ω) :
    mkOp F hC0 hC hadd hsmul x p = F x p := rfl

/-- Woodford (2003), App. A.3, p. 634: the conditional-expectation operator
`x ↦ (E_t x_t)_t` on vector processes, coordinate by coordinate (norm at most one). -/
noncomputable def condEV : SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  mkOp (fun x p i => 𝔼.E p.1 (fun ω => x (p.1, ω) i) p.2) zero_le_one
    (fun x p => (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs, one_mul]
      exact 𝔼.abs_E_le (fun ω => abs_apply_le x p.1 ω i) p.1 p.2)
    (fun x y => by
      funext p i
      change 𝔼.E p.1 ((fun ω => x (p.1, ω) i) + fun ω => y (p.1, ω) i) p.2 = _
      rw [map_add]
      rfl)
    (fun c x => by
      funext p i
      change 𝔼.E p.1 (c • fun ω => x (p.1, ω) i) p.2 = _
      rw [map_smul]
      rfl)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634: the process of `condEV x` is `E_t x_t`. -/
theorem toP_condEV (x : SProcV ι Ω) (t : ℕ) :
    toP (condEV 𝔼 x) t = fun i => 𝔼.E t (toP x t i) := rfl

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632, state by state: the operator
`x ↦ (f₁ x_{t−1} + f₂ x_t + f₃ x_{t+1})_t` (with `x_{−1} = 0`) applied in every state. -/
noncomputable def linS (f₁ f₂ f₃ : Matrix ι ι ℝ) : SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  mkOp (fun x p => f₁ *ᵥ lagV 0 (fun s => x (s, p.2)) p.1 + f₂ *ᵥ x p + f₃ *ᵥ x (p.1 + 1, p.2))
    (C := ‖mclm f₁‖ + ‖mclm f₂‖ + ‖mclm f₃‖) (by positivity)
    (fun x p => by
      have hl : ‖lagV 0 (fun s => x (s, p.2)) p.1‖ ≤ ‖x‖ := by
        cases p.1 with
        | zero => simp
        | succ t => exact LocalIFTStochastic.norm_apply_le x _
      have e : ∀ (M : Matrix ι ι ℝ) (v : ι → ℝ), ‖M *ᵥ v‖ ≤ ‖mclm M‖ * ‖v‖ := fun M v => by
        rw [← mclm_apply]; exact (mclm M).le_opNorm v
      calc _ ≤ ‖f₁ *ᵥ lagV 0 (fun s => x (s, p.2)) p.1‖ + ‖f₂ *ᵥ x p‖ +
            ‖f₃ *ᵥ x (p.1 + 1, p.2)‖ := norm_add₃_le
        _ ≤ ‖mclm f₁‖ * ‖x‖ + ‖mclm f₂‖ * ‖x‖ + ‖mclm f₃‖ * ‖x‖ := by
          gcongr
          · exact (e f₁ _).trans (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
          · exact (e f₂ _).trans (mul_le_mul_of_nonneg_left
              (LocalIFTStochastic.norm_apply_le x p) (norm_nonneg _))
          · exact (e f₃ _).trans (mul_le_mul_of_nonneg_left
              (LocalIFTStochastic.norm_apply_le x _) (norm_nonneg _))
        _ = _ := by ring)
    (fun x y => by
      funext p
      have hl : lagV 0 (fun s => (x + y) (s, p.2)) p.1 =
          lagV 0 (fun s => x (s, p.2)) p.1 + lagV 0 (fun s => y (s, p.2)) p.1 := by
        cases p.1 <;> simp
      change f₁ *ᵥ lagV 0 (fun s => (x + y) (s, p.2)) p.1 + f₂ *ᵥ (x + y) p +
          f₃ *ᵥ (x + y) (p.1 + 1, p.2) =
        (f₁ *ᵥ lagV 0 (fun s => x (s, p.2)) p.1 + f₂ *ᵥ x p + f₃ *ᵥ x (p.1 + 1, p.2)) +
          (f₁ *ᵥ lagV 0 (fun s => y (s, p.2)) p.1 + f₂ *ᵥ y p + f₃ *ᵥ y (p.1 + 1, p.2))
      rw [hl, lp.coeFn_add]
      simp only [Pi.add_apply, Matrix.mulVec_add]
      abel)
    (fun c x => by
      funext p
      have hl : lagV 0 (fun s => (c • x) (s, p.2)) p.1 =
          c • lagV 0 (fun s => x (s, p.2)) p.1 := by
        cases p.1 <;> simp
      change f₁ *ᵥ lagV 0 (fun s => (c • x) (s, p.2)) p.1 + f₂ *ᵥ (c • x) p +
          f₃ *ᵥ (c • x) (p.1 + 1, p.2) =
        c • (f₁ *ᵥ lagV 0 (fun s => x (s, p.2)) p.1 + f₂ *ᵥ x p + f₃ *ᵥ x (p.1 + 1, p.2))
      rw [hl, lp.coeFn_smul]
      simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_add])

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the process of `linS x`. -/
theorem toP_linS (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SProcV ι Ω) (t : ℕ) :
    toP (linS f₁ f₂ f₃ x) t = mv f₁ (lagP 0 (toP x) t) + mv f₂ (toP x t) +
      mv f₃ (toP x (t + 1)) := by
  funext i ω
  simp only [Pi.add_apply, mv_apply]
  change (f₁ *ᵥ lagV 0 (fun s => x (s, ω)) t + f₂ *ᵥ x (t, ω) + f₃ *ᵥ x (t + 1, ω)) i = _
  have hl : lagV 0 (fun s => x (s, ω)) t = fun j => lagP 0 (toP x) t j ω := by
    cases t <;> rfl
  rw [hl]
  rfl

/-- Woodford (2003), App. A.3, eqs. (A.12)–(A.13), p. 634: **the linearised operator under
uncertainty with predetermined variables**,
`x ↦ (E_t[f₁ x_{t−1} + f₂ x_t + f₃ x_{t+1}] + (x_t − E_t x_t))_t` on `ℓ∞(ℕ × Ω, ℝⁿ)`
(`x_{−1} = 0`). The second term vanishes exactly on adapted processes, so adaptedness is not
built into the space. -/
noncomputable def opS (f₁ f₂ f₃ : Matrix ι ι ℝ) : SProcV ι Ω →L[ℝ] SProcV ι Ω :=
  (condEV 𝔼).comp (linS f₁ f₂ f₃) + (1 - condEV 𝔼)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, eq. (A.12), p. 634 (tool): `E_t` of a matrix times `E_t a` is
the matrix times `E_t a`. -/
theorem EV_mv_EV (t : ℕ) (M : Matrix ι ι ℝ) (a : ι → Ω → ℝ) :
    (fun i => 𝔼.E t (mv M (fun j => 𝔼.E t (a j)) i)) = mv M (fun j => 𝔼.E t (a j)) := by
  funext i
  rw [E_mv 𝔼]
  congr 1
  funext j
  exact 𝔼.E_E_self t _

/-- Woodford (2003), App. A.3, eqs. (A.12)–(A.13), p. 634: the process of `opS x`,
`f₁ E_t x_{t−1} + f₂ E_t x_t + f₃ E_t x_{t+1} + (x_t − E_t x_t)`. -/
theorem toP_opS (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SProcV ι Ω) (t : ℕ) :
    toP (opS 𝔼 f₁ f₂ f₃ x) t =
      mv f₁ (fun i => 𝔼.E t (lagP 0 (toP x) t i)) + mv f₂ (fun i => 𝔼.E t (toP x t i)) +
        mv f₃ (fun i => 𝔼.E t (toP x (t + 1) i)) + (toP x t - fun i => 𝔼.E t (toP x t i)) := by
  have e1 : toP (opS 𝔼 f₁ f₂ f₃ x) t = toP (condEV 𝔼 (linS f₁ f₂ f₃ x)) t +
      (toP x t - toP (condEV 𝔼 x) t) := rfl
  rw [e1, toP_condEV, toP_condEV, toP_linS]
  congr 1
  funext i
  simp only [Pi.add_apply, map_add, E_mv 𝔼]

/-- Woodford (2003), App. A.3, p. 634: `E_t` of `(opS x)_t` drops the adaptedness term. -/
theorem EV_toP_opS (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SProcV ι Ω) (t : ℕ) :
    (fun i => 𝔼.E t (toP (opS 𝔼 f₁ f₂ f₃ x) t i)) =
      mv f₁ (fun i => 𝔼.E t (lagP 0 (toP x) t i)) + mv f₂ (fun i => 𝔼.E t (toP x t i)) +
        mv f₃ (fun i => 𝔼.E t (toP x (t + 1) i)) := by
  rw [toP_opS]
  funext i
  have hA := congrFun (EV_mv_EV 𝔼 t f₁ (lagP 0 (toP x) t)) i
  have hB := congrFun (EV_mv_EV 𝔼 t f₂ (toP x t)) i
  have hC := congrFun (EV_mv_EV 𝔼 t f₃ (toP x (t + 1))) i
  beta_reduce at hA hB hC
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub, 𝔼.E_E_self, sub_self, add_zero]
  rw [hA, hB, hC]

/-- Woodford (2003), App. A.3, p. 634: if `opS x` is adapted, so is `x` (the adaptedness term is
the only non-measurable part). -/
theorem adapted_of_opS (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SProcV ι Ω)
    (h : AdaptedV 𝔼 (toP (opS 𝔼 f₁ f₂ f₃ x))) : AdaptedV 𝔼 (toP x) := by
  intro t i
  have e1 := congrFun (EV_toP_opS 𝔼 f₁ f₂ f₃ x t) i
  have e2 := congrFun (toP_opS 𝔼 f₁ f₂ f₃ x t) i
  rw [h t i] at e1
  rw [e1] at e2
  simp only [Pi.add_apply, Pi.sub_apply] at e2
  have : toP x t i - 𝔼.E t (toP x t i) = 0 := by
    have := congrArg (fun a => a - (mv f₁ (fun i => 𝔼.E t (lagP 0 (toP x) t i)) i +
      mv f₂ (fun i => 𝔼.E t (toP x t i)) i + mv f₃ (fun i => 𝔼.E t (toP x (t + 1) i)) i)) e2
    simp only [add_sub_cancel_left, sub_self] at this
    exact this.symm
  exact (sub_eq_zero.mp this).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): for adapted `x`, `E_t x_{t−1} = x_{t−1}` and
`E_t x_t = x_t`. -/
theorem EV_adapted {x : ℕ → ι → Ω → ℝ} (hx : AdaptedV 𝔼 x) (t : ℕ) :
    (fun i => 𝔼.E t (lagP 0 x t i)) = lagP 0 x t ∧ (fun i => 𝔼.E t (x t i)) = x t :=
  ⟨funext fun i => adaptedV_lagP 𝔼 0 hx t i, funext fun i => hx t i⟩

/-- Woodford (2003), App. A.3, p. 634: on adapted processes `opS` is the left side of (A.13). -/
theorem toP_opS_of_adapted (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SProcV ι Ω)
    (hx : AdaptedV 𝔼 (toP x)) (t : ℕ) :
    toP (opS 𝔼 f₁ f₂ f₃ x) t = mv f₁ (lagP 0 (toP x) t) + mv f₂ (toP x t) +
      mv f₃ (fun i => 𝔼.E t (toP x (t + 1) i)) := by
  rw [toP_opS, (EV_adapted 𝔼 hx t).1, (EV_adapted 𝔼 hx t).2, sub_self, add_zero]

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 633 (tool): the initial condition moves to the forcing,
`f₁ x_{t−1} = f₁ x_{t−1}|_{x_{−1}=0} + f₁ x_{−1} 1_{t=0}`. -/
theorem solvesLinS_shift (f₁ f₂ f₃ : Matrix ι ι ℝ) (w : ℕ → ι → Ω → ℝ) (xm : ι → ℝ)
    (x : ℕ → ι → Ω → ℝ) :
    SolvesLinS 𝔼 f₁ f₂ f₃ w xm x ↔
      SolvesLinS 𝔼 f₁ f₂ f₃ (fun t => w t - mv f₁ (lagP xm 0 t)) 0 x := by
  refine forall_congr' fun t => ?_
  rw [lagP_split xm x t, mv_add, eq_sub_iff_add_eq]
  constructor <;> intro h <;> rw [← h] <;> abel

/-- **The linearised operator (A.12) is invertible iff (A.13) is determinate** (Woodford (2003),
App. A.3, pp. 633–634): on `ℓ∞(ℕ × Ω, ℝⁿ)`, `opS` is invertible iff for every bounded adapted
forcing and every `x_{−1}` there is exactly one bounded adapted solution. (The operator is block
triangular: the adaptedness term is the identity on `ker E`, and on adapted processes it is the
left side of (A.13).) -/
theorem isUnit_opS_iff (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    IsUnit (opS 𝔼 f₁ f₂ f₃) ↔ LinDeterminateS 𝔼 f₁ f₂ f₃ := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · rintro ⟨hinj, hsurj⟩ w hwb hwa xm
    set y := fun t => w t - mv f₁ (lagP xm 0 t) with hy
    have hyb : BoundedV y :=
      boundedV_sub hwb (boundedV_mv f₁ (boundedV_lagP xm ⟨0, fun _ _ _ => by simp⟩))
    have hya : AdaptedV 𝔼 y :=
      adaptedV_sub 𝔼 hwa (adaptedV_mv 𝔼 f₁ (adaptedV_lagP 𝔼 xm (fun _ _ => map_zero _)))
    obtain ⟨x, hx⟩ := hsurj (ofP y hyb)
    have hxp : toP (opS 𝔼 f₁ f₂ f₃ x) = y := by rw [hx]; rfl
    have hxa : AdaptedV 𝔼 (toP x) := adapted_of_opS 𝔼 f₁ f₂ f₃ x (by rw [hxp]; exact hya)
    refine ⟨toP x, ⟨boundedV_toP x, hxa, (solvesLinS_shift 𝔼 _ _ _ _ _ _).mpr fun t => ?_⟩,
      fun x' ⟨hx'b, hx'a, hx'⟩ => ?_⟩
    · rw [← toP_opS_of_adapted 𝔼 f₁ f₂ f₃ x hxa t, hxp]
    · have hd : SolvesLinS 𝔼 f₁ f₂ f₃ 0 0 (fun t => x' t - toP x t) := by
        have h1 := (solvesLinS_shift 𝔼 _ _ _ _ _ _).mp hx'
        intro t
        have e1 := h1 t
        have e2 := toP_opS_of_adapted 𝔼 f₁ f₂ f₃ x hxa t
        rw [hxp] at e2
        have hl : lagP 0 (fun t => x' t - toP x t) t = lagP 0 x' t - lagP 0 (toP x) t := by
          cases t with
          | zero => funext i ω; simp [lagP]
          | succ t => rfl
        have hE : (fun i => 𝔼.E t ((x' (t + 1) - toP x (t + 1)) i)) =
            (fun i => 𝔼.E t (x' (t + 1) i)) - fun i => 𝔼.E t (toP x (t + 1) i) := by
          funext i; simp [map_sub]
        rw [hl]
        beta_reduce
        rw [hE, mv_sub, mv_sub, mv_sub, Pi.zero_apply]
        have : mv f₁ (lagP 0 x' t) + mv f₂ (x' t) + mv f₃ (fun i => 𝔼.E t (x' (t + 1) i)) -
            (mv f₁ (lagP 0 (toP x) t) + mv f₂ (toP x t) +
              mv f₃ (fun i => 𝔼.E t (toP x (t + 1) i))) = 0 := by
          rw [e1, ← e2, sub_self]
        rw [← this]
        abel
      have hdb : BoundedV (fun t => x' t - toP x t) := boundedV_sub hx'b (boundedV_toP x)
      have hda : AdaptedV 𝔼 (fun t => x' t - toP x t) := adaptedV_sub 𝔼 hx'a hxa
      have h0 : opS 𝔼 f₁ f₂ f₃ (ofP _ hdb) = 0 := by
        apply toP_injective
        funext t
        rw [toP_opS_of_adapted 𝔼 f₁ f₂ f₃ (ofP _ hdb) hda t]
        exact hd t
      have := hinj (h0.trans (map_zero _).symm)
      have e := congrArg toP this
      rw [toP_ofP, toP_zero] at e
      funext t i ω
      have := congrFun (congrFun (congrFun e t) i) ω
      simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this
  · intro hL
    constructor
    · intro x x' hxx
      have h0 : opS 𝔼 f₁ f₂ f₃ (x - x') = 0 := by rw [map_sub, hxx, sub_self]
      have hp : toP (opS 𝔼 f₁ f₂ f₃ (x - x')) = 0 := by rw [h0]; rfl
      have ha : AdaptedV 𝔼 (toP (x - x')) :=
        adapted_of_opS 𝔼 f₁ f₂ f₃ _ (by rw [hp]; exact fun _ _ => map_zero _)
      have hs : SolvesLinS 𝔼 f₁ f₂ f₃ 0 0 (toP (x - x')) := fun t => by
        rw [← toP_opS_of_adapted 𝔼 f₁ f₂ f₃ _ ha t, hp]
      have hz : SolvesLinS 𝔼 f₁ f₂ f₃ 0 0 (0 : ℕ → ι → Ω → ℝ) := fun t => by
        have h0 : (fun (_ : ι) => 𝔼.E t (0 : Ω → ℝ)) = 0 :=
          funext fun _ => map_zero _
        simp only [lagP_zero_zero, Pi.zero_apply, mv_zero, zero_add]
        rw [h0, mv_zero]
      have e := (hL 0 ⟨0, fun _ _ _ => by simp⟩ (fun _ _ => map_zero _) 0).unique
        ⟨boundedV_toP _, ha, hs⟩ ⟨⟨0, fun _ _ _ => by simp⟩, fun _ _ => map_zero _, hz⟩
      exact sub_eq_zero.mp (toP_injective e)
    · intro y
      set b : ℕ → ι → Ω → ℝ := fun t => toP y t - fun i => 𝔼.E t (toP y t i) with hb
      have hbb : BoundedV b := by
        obtain ⟨M, hM⟩ := boundedV_toP y
        exact ⟨M + M, fun t i ω => (abs_sub _ _).trans
          (add_le_add (hM t i ω) (𝔼.abs_E_le (hM t i) t ω))⟩
      have hEb : ∀ t i, 𝔼.E t (b t i) = 0 := fun t i => by
        simp [hb, map_sub, 𝔼.E_E_self]
      have hEb1 : ∀ t i, 𝔼.E t (b (t + 1) i) = 0 := fun t i => by
        simp [hb, map_sub, 𝔼.tower (Nat.le_succ t)]
      set w : ℕ → ι → Ω → ℝ := fun t => (fun i => 𝔼.E t (toP y t i)) -
        mv f₁ (fun i => 𝔼.E t (lagP 0 b t i)) with hw
      have hwb : BoundedV w := by
        refine boundedV_sub ?_ (boundedV_mv f₁ ?_)
        · obtain ⟨M, hM⟩ := boundedV_toP y
          exact ⟨M, fun t i ω => 𝔼.abs_E_le (hM t i) t ω⟩
        · obtain ⟨M, hM⟩ := boundedV_lagP 0 hbb
          exact ⟨M, fun t i ω => 𝔼.abs_E_le (hM t i) t ω⟩
      have hwa : AdaptedV 𝔼 w := by
        refine adaptedV_sub 𝔼 (fun t i => 𝔼.E_E_self t _) (adaptedV_mv 𝔼 f₁ ?_)
        exact fun t i => 𝔼.E_E_self t _
      obtain ⟨z, ⟨hzb, hza, hz⟩, -⟩ := hL w hwb hwa 0
      set xp : ℕ → ι → Ω → ℝ := fun t => z t + b t with hxp
      have hxpb : BoundedV xp := boundedV_add hzb hbb
      refine ⟨ofP xp hxpb, toP_injective ?_⟩
      funext t
      rw [toP_opS, toP_ofP]
      have h1 : (fun i => 𝔼.E t (lagP 0 xp t i)) =
          lagP 0 z t + fun i => 𝔼.E t (lagP 0 b t i) := by
        funext i
        have hl : lagP 0 xp t i = lagP 0 z t i + lagP 0 b t i := by
          cases t with
          | zero => funext ω; simp [lagP]
          | succ t => rfl
        rw [hl, map_add, adaptedV_lagP 𝔼 0 hza t i]
        rfl
      have h2 : (fun i => 𝔼.E t (xp t i)) = z t := by
        funext i
        simp only [hxp, Pi.add_apply, map_add, hza t i, hEb t i, add_zero]
      have h3 : (fun i => 𝔼.E t (xp (t + 1) i)) = fun i => 𝔼.E t (z (t + 1) i) := by
        funext i
        simp only [hxp, Pi.add_apply, map_add, hEb1 t i, add_zero]
      rw [h1, h2, h3, mv_add]
      have e' : mv f₁ (lagP 0 z t) + mv f₂ (z t) + mv f₃ (fun i => 𝔼.E t (z (t + 1) i)) =
          w t := hz t
      have hxpt : xp t - z t = b t := by simp [hxp]
      rw [hxpt]
      calc mv f₁ (lagP 0 z t) + mv f₁ (fun i => 𝔼.E t (lagP 0 b t i)) + mv f₂ (z t) +
            mv f₃ (fun i => 𝔼.E t (z (t + 1) i)) + b t
          = (mv f₁ (lagP 0 z t) + mv f₂ (z t) + mv f₃ (fun i => 𝔼.E t (z (t + 1) i))) +
            mv f₁ (fun i => 𝔼.E t (lagP 0 b t i)) + b t := by abel
        _ = toP y t := by
          rw [e', hw, hb]
          simp only
          abel

/-- **Invertibility on `ℓ∞(ℕ × Ω, ℝⁿ)` is the exact root condition** (Woodford (2003),
App. A.3, eqs. (A.9), (A.12), pp. 632–634): for every expectation system on a nonempty state
space, the operator (A.12) is invertible iff `det(f₃λ² + f₂λ + f₁) ≢ 0`, no root lies on the
unit circle, exactly `n` roots lie inside, and genericity holds — the perfect-foresight
condition; uncertainty does not change it. -/
theorem isUnit_opS_iff_roots [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    IsUnit (opS 𝔼 f₁ f₂ f₃) ↔ quadPoly f₁ f₂ f₃ ≠ 0 ∧
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ HomInjective f₁ f₂ f₃ := by
  rw [isUnit_opS_iff, linDeterminateS_iff_roots]

/-- Woodford (2003), App. A.3, pp. 632–634: the stochastic operator (A.12) is invertible iff the
perfect-foresight operator (A.8) is. -/
theorem isUnit_opS_iff_sysOp [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    IsUnit (opS 𝔼 f₁ f₂ f₃) ↔ IsUnit (sysOp f₁ f₂ f₃) := by
  rw [isUnit_opS_iff, isUnit_sysOp_iff_stoch 𝔼]

end Woodford.PriceLevelDetermination.LinearSystemsStochastic
