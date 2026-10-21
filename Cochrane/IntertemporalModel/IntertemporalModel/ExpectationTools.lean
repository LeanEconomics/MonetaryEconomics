/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.ForwardSolution
import IntertemporalModel.ExpectationsFiniteTree

/-!
# Shared expectation tools for Chapter 2

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1 (p. 22), §2.4 (p. 30)
and §2.5 (p. 35): the general facts about the abstract expectation operators `E_t` that the
Chapter 2 modules share. Each fact is stated once here.

## Main results

* The innovation operator `innov` (the book's `ΔE_{t+1} = E_{t+1} − E_t`, p. 30) and its
  algebra: `innov_add`, `innov_sub`, `innov_smul`, `innov_neg`, `innov_const`,
  `innov_of_known`, `E_innov_zero` and `E_innov_zero_of_le` ("you can't expect future unexpected
  shocks"), `innov_known_next`, `innov_E_succ`, `innov_mul_known`, `eq_E_add_innov`.
* Known variables: with the pull-out property, products, reciprocals and quotients of date-`t`
  variables are known at `t` (`E_mul_known`, `E_inv_known`, `E_div_known`, `E_one_add_known`).
  `FunctionsKnown` (functions of known variables are known) and `Closed` (functions of two known
  variables are known, restated from the Woodford Chapter 2 project) are hypotheses, like
  `PullOut`, true for perfect foresight and for every finite event tree; `Closed` implies
  `FunctionsKnown` (`functionsKnown_of_closed`). `known_div` needs no nonvanishing denominator.
* Conditional monotone convergence `MonotoneConvergence` (restated from the Woodford Chapter 2
  project), with its two instances; `const_le_E`, `E_nonneg`, `abs_E_le_E_abs`;
  `summable_E_shift` (discounted forecasts of bounded surpluses are summable).
-/

namespace Cochrane.IntertemporalModel.ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Innovations `ΔE_{t+1} = E_{t+1} − E_t` -/

/-- Cochrane (2023), §2.4, p. 30 (notation `ΔE_{t+1} ≡ E_{t+1} − E_t`): the innovation of `x`
between dates `t` and `t + 1`. -/
def innov (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) x - 𝔼.E t x

/-- Cochrane (2023), p. 30: innovations are additive. -/
theorem innov_add (t : ℕ) (x y : Ω → ℝ) : innov 𝔼 t (x + y) = innov 𝔼 t x + innov 𝔼 t y := by
  unfold innov
  rw [map_add, map_add]
  abel

/-- Cochrane (2023), p. 30: innovations commute with subtraction. -/
theorem innov_sub (t : ℕ) (x y : Ω → ℝ) : innov 𝔼 t (x - y) = innov 𝔼 t x - innov 𝔼 t y := by
  unfold innov
  rw [map_sub, map_sub]
  abel

/-- Cochrane (2023), p. 30: innovations are homogeneous. -/
theorem innov_smul (t : ℕ) (c : ℝ) (x : Ω → ℝ) : innov 𝔼 t (c • x) = c • innov 𝔼 t x := by
  unfold innov
  rw [map_smul, map_smul, smul_sub]

/-- Cochrane (2023), p. 30: the innovation of a negative. -/
theorem innov_neg (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t (-x) = -innov 𝔼 t x := by
  unfold innov
  rw [map_neg, map_neg]
  abel

/-- Cochrane (2023), p. 30: constants have no innovation. -/
theorem innov_const (t : ℕ) (c : ℝ) : innov 𝔼 t (fun _ => c) = 0 := by
  unfold innov
  rw [𝔼.const, 𝔼.const, sub_self]

/-- Cochrane (2023), p. 30: a variable known at date `t` has no date-`t + 1` innovation. -/
theorem innov_of_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : innov 𝔼 t x = 0 := by
  unfold innov
  rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx, hx, sub_self]

/-- Cochrane (2023), p. 30 ("you can't expect future unexpected shocks"):
`E_t(ΔE_{t+1} x) = 0`. -/
theorem E_innov_zero (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (innov 𝔼 t x) = 0 := by
  unfold innov
  rw [map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), p. 30: an earlier expectation of a later innovation is zero,
`E_s(ΔE_{t+1} x) = 0` for `s ≤ t` (no future innovation is forecastable). -/
theorem E_innov_zero_of_le {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : 𝔼.E s (innov 𝔼 t x) = 0 := by
  rw [← 𝔼.tower hst, E_innov_zero, map_zero]

/-- Cochrane (2023), p. 30: the date-`t + 1` innovation is known at date `t + 1`. -/
theorem innov_known_next (t : ℕ) (x : Ω → ℝ) : 𝔼.E (t + 1) (innov 𝔼 t x) = innov 𝔼 t x := by
  unfold innov
  rw [map_sub, 𝔼.E_E_self, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), p. 30: the innovation of `E_{t+1} x` is the innovation of `x`. -/
theorem innov_E_succ (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t (𝔼.E (t + 1) x) = innov 𝔼 t x := by
  unfold innov
  rw [𝔼.E_E_self, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), p. 30 (pull-out, used for (2.13)): a factor known at date `t` comes out of
the innovation, `ΔE_{t+1}(a y) = a ΔE_{t+1} y`. -/
theorem innov_mul_known (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (y : Ω → ℝ) : innov 𝔼 t (a * y) = a * innov 𝔼 t y := by
  unfold innov
  rw [hPO (t + 1) a y (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ha), hPO t a y ha, mul_sub]

/-- Cochrane (2023), p. 30 and p. 35 ("Using `π_{t+1} = E_t π_{t+1} + ΔE_{t+1} π_{t+1}`"): any
random variable known at `t + 1` is its forecast plus its innovation. -/
theorem eq_E_add_innov {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    x = 𝔼.E t x + innov 𝔼 t x := by
  unfold innov
  rw [hx]
  abel

/-! ### Known variables -/

/-- Cochrane (2023), p. 22 (the price level is known at `t`): with the pull-out property,
products of date-`t` variables are known at `t`. -/
theorem E_mul_known (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [hPO t a b ha, hb]

/-- Cochrane (2023), p. 22: with the pull-out property, the reciprocal of a nonvanishing
date-`t` variable is known at `t` (the abstract `ExpectationSystem` axioms alone do not give
this). -/
theorem E_inv_known (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (ha0 : ∀ ω, a ω ≠ 0) : 𝔼.E t a⁻¹ = a⁻¹ := by
  have h1 : a * a⁻¹ = fun _ => (1 : ℝ) := by
    funext ω; simp [ha0 ω]
  have h2 := hPO t a a⁻¹ ha
  rw [h1, 𝔼.const] at h2
  funext ω
  have h3 := congrFun h2 ω
  simp only [Pi.mul_apply] at h3
  simp only [Pi.inv_apply]
  field_simp [ha0 ω]
  linarith

/-- Cochrane (2023), p. 22: with the pull-out property, quotients of date-`t` variables (with
nonvanishing denominator) are known at `t`. -/
theorem E_div_known (hPO : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) (hb0 : ∀ ω, b ω ≠ 0) : 𝔼.E t (a / b) = a / b := by
  rw [div_eq_mul_inv]
  exact E_mul_known 𝔼 hPO ha (E_inv_known 𝔼 hPO hb hb0)

/-- Cochrane (2023), (2.3), p. 22: the gross rate `1 + i` is known when `i` is. -/
theorem E_one_add_known {t : ℕ} {i : Ω → ℝ} (hi : 𝔼.E t i = i) : 𝔼.E t (1 + i) = 1 + i := by
  rw [map_add, hi]
  congr 1
  exact 𝔼.const t 1

/-- Cochrane (2023), p. 22 ("Debt `B_{t−1}` is predetermined at time `t`" and the price level is
a date-`t` variable): every function of a variable known at `t` is known at `t`. True for genuine
conditional expectations and for the two instances (`perfectForesight_functionsKnown`,
`finiteTree_functionsKnown`), but not implied by the `ExpectationSystem` axioms, so it is a
hypothesis where it is used (like `PullOut`). -/
def FunctionsKnown : Prop :=
  ∀ t (x : Ω → ℝ) (f : ℝ → ℝ), 𝔼.E t x = x → 𝔼.E t (fun ω => f (x ω)) = fun ω => f (x ω)

/-- Cochrane (2023), p. 22: under perfect foresight every variable is known. -/
theorem perfectForesight_functionsKnown : FunctionsKnown perfectForesight :=
  fun _ _ _ _ => rfl

/-- Cochrane (2023), p. 22: on a finite event tree a function of a variable that is constant on
date-`t` information cells is again constant on them, hence known at `t`. -/
theorem finiteTree_functionsKnown {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : FunctionsKnown T.toExpectationSystem := by
  intro t x f hx
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hx ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have : x ω' = x ω := by rw [← hx, T.condE_congr x h]
  rw [this]

/-- Cochrane (2023), p. 22: with pull-out and `FunctionsKnown`, the quotient `a/b` of two
variables known at `t` is known at `t` (no nonvanishing hypothesis, unlike `E_div_known`). -/
theorem known_div (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼)
    {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a) (hb : 𝔼.E t b = b) :
    𝔼.E t (fun ω => a ω / b ω) = fun ω => a ω / b ω := by
  have hsplit : (fun ω => a ω / b ω) = a * fun ω => (b ω)⁻¹ := by
    funext ω; simp [div_eq_mul_inv]
  rw [hsplit, hPO t _ _ ha, hFK t b (fun r => r⁻¹) hb]

/-- Woodford (2003), App. A, §A.6, p. 639 (restated from the Woodford Chapter 2 project): a
function of two date-`t` known variables is known at date `t`. Used for Cochrane (2023), p. 33. -/
def Closed : Prop :=
  ∀ t (f : ℝ → ℝ → ℝ) (x y : Ω → ℝ), 𝔼.E t x = x → 𝔼.E t y = y →
    𝔼.E t (fun ω => f (x ω) (y ω)) = fun ω => f (x ω) (y ω)

/-- Woodford (2003), §A.6 (restated from the Woodford Chapter 2 project): perfect foresight has
the closure property. Used for Cochrane (2023), p. 33. -/
theorem perfectForesight_closed : Closed perfectForesight := fun _ _ _ _ _ _ => rfl

/-- Woodford (2003), §A.6 (restated from the Woodford Chapter 2 project): every finite event tree
has the closure property. Used for Cochrane (2023), p. 33. -/
theorem finiteTree_closed {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    Closed T.toExpectationSystem := by
  intro t f x y hx hy
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hx hy ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have hx' : x ω' = x ω := by
    rw [← hx]
    exact T.condE_congr x h
  have hy' : y ω' = y ω := by
    rw [← hy]
    exact T.condE_congr y h
  simp only [hx', hy']

/-- Cochrane (2023), p. 22 and p. 33: the two-variable closure property `Closed` (used for the
Chapter 2 links to Woodford) implies the one-variable `FunctionsKnown` (used for the
equilibrium price level `P_t = B_{t−1}/pv_t`). -/
theorem functionsKnown_of_closed (hC : Closed 𝔼) : FunctionsKnown 𝔼 :=
  fun t x f hx => hC t (fun a _ => f a) x x hx hx

/-! ### Conditional monotone convergence and order facts -/

/-- Cochrane (2023), p. 22 ("we can then iterate (2.5) to (2.7)"): the interchange of `E_t` and
infinite sums, as the conditional monotone convergence theorem for nonnegative summands.
Restated from the Woodford Chapter 2 project (`AssetPricing.MonotoneConvergence`). -/
def MonotoneConvergence : Prop :=
  ∀ t (f : ℕ → Ω → ℝ), (∀ k ω, 0 ≤ f k ω) → (∀ ω, Summable fun k => f k ω) →
    ∀ ω, HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω)

/-- Cochrane (2023), p. 22: perfect foresight satisfies conditional monotone convergence
(restated from the Woodford Chapter 2 project). -/
theorem perfectForesight_monotoneConvergence : MonotoneConvergence perfectForesight :=
  fun _ _ _ hs ω => (hs ω).hasSum

/-- Cochrane (2023), p. 22: every finite event tree satisfies conditional monotone convergence,
so (2.7) is not restricted to perfect foresight (restated from the Woodford Chapter 2
project). -/
theorem finiteTree_monotoneConvergence {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : MonotoneConvergence T.toExpectationSystem := by
  classical
  intro t f _ hs ω
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num]
  refine HasSum.div_const ?_ _
  refine hasSum_sum fun ω' _ => ?_
  split_ifs
  · exact (hs ω').hasSum.mul_left _
  · exact hasSum_zero

/-- Cochrane (2023), pp. 22 and 31: a constant lower bound passes through `E_t`: if `c ≤ x` in
every state then `c ≤ E_t x`. -/
theorem const_le_E {c : ℝ} {x : Ω → ℝ} (hx : ∀ ω, c ≤ x ω) (t : ℕ) (ω : Ω) :
    c ≤ 𝔼.E t x ω := by
  have h := 𝔼.mono t (x := fun _ => c) (y := x) hx ω
  rwa [𝔼.const] at h

/-- Cochrane (2023), p. 22: expectations of nonnegative variables are nonnegative. -/
theorem E_nonneg {t : ℕ} {x : Ω → ℝ} (hx : ∀ ω, 0 ≤ x ω) (ω : Ω) : 0 ≤ 𝔼.E t x ω :=
  const_le_E 𝔼 hx t ω

/-- Cochrane (2023), p. 22 (signed surpluses): `|E_t x| ≤ E_t|x|`. -/
theorem abs_E_le_E_abs (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    |𝔼.E t x ω| ≤ 𝔼.E t (fun ω' => |x ω'|) ω := by
  have h1 := 𝔼.mono t (show x ≤ fun ω' => |x ω'| from fun ω' => le_abs_self _) ω
  have h2 := 𝔼.mono t (show (fun ω' => -|x ω'|) ≤ x from fun ω' => neg_abs_le _) ω
  have h3 : 𝔼.E t (fun ω' => -|x ω'|) = -𝔼.E t (fun ω' => |x ω'|) := by
    rw [← map_neg]
    rfl
  rw [h3] at h2
  exact abs_le.mpr ⟨by simpa using h2, h1⟩

/-- Cochrane (2023), eqs. (2.7) and (2.17), pp. 22, 35: for bounded surpluses and `0 ≤ β < 1`
the discounted forecasts `∑ βᵏ E_n s_{t+k}` are (absolutely) summable, at every forecast date
`n` and starting date `t`. -/
theorem summable_E_shift {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (n t : ℕ) (ω : Ω) :
    Summable (fun k => β ^ k * 𝔼.E n (s (t + k)) ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + k)) n ω) (pow_nonneg h0 k)

end Cochrane.IntertemporalModel.ExpectationTools
