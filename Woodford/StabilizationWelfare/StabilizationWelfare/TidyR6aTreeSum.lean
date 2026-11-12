/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5RamseyWeighted

/-!
# Discounted sums on an event tree

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (welfare `E_0 ∑ βᵗ U_t`, pp. 383–386) and
Chapter 7, §1 (the Lagrangian of the Ramsey problem); Appendix A.3.

On an event tree (`NonlinearNKMarkovRamseyTree.LagTree`) the expected discounted sum
`S f(x) = E_x ∑_t βᵗ f(x_t)` of a bounded function is the forward solution `fwdS β f` of
`g = βMg + f`. This module develops the calculus of `S` needed for second-order sufficiency
of the Ramsey plan in a DISCOUNTED `ℓ²` norm:

* `S_spec`, `S_unique`, `S_lin`: the defining equation, uniqueness, linearity.
* `S_nonneg`, `S_mono`, `S_ge`: positivity (a maximum-principle argument), monotonicity,
  `S f ≥ f` for `f ≥ 0`.
* `M_lag_mul`: the expectation sees the current node in the lag (`M(f · lag g) = g · Mf`),
  from `TidyR5RamseyWeighted.M_le_children`; `M_sq_le` (Jensen: `(Mf)² ≤ M(f²)`).
* **`S_lag`**: regrouping (the law of iterated expectations in discounted sums):
  `S[a · lag h] = a · lag h + βS[(Ma) h]`; at a root `S[lag h] = βS[h]` (`S_lag_root`).
* `S_M`: `S[Mf] = M(Sf)`; `S_M_le`: `S[Mf] ≤ Sf/β` for `f ≥ 0`.
* **`S_forward_bound`**: if `0 ≤ u ≤ v + κMu` with `κ < β`, then `Su ≤ Sv/(1 − κ/β)`;
  **`S_backward_bound`**: if `0 ≤ u ≤ v + κ lag u` with `κβ < 1`, then at every root
  `Su ≤ Sv/(1 − κβ)`.
-/

namespace Woodford.StabilizationWelfare.TidyR6aTreeSum

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamseyTree TidyR5RamseyWeighted

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), §1, p. 383 (**the expected discounted sum on an event tree**):
`S f = fwdS β f`, the bounded solution of `g = βMg + f`. -/
noncomputable def S (β : ℝ) (f : X → ℝ) : X → ℝ := fwdS T β f

/-- A function is bounded. -/
def Bdd (f : X → ℝ) : Prop := ∃ B, ∀ x, |f x| ≤ B

/-- Woodford (2003), §1: the discounted sum solves `S f = βM(S f) + f` and is bounded. -/
theorem S_spec {β : ℝ} (hβ : |β| < 1) {f : X → ℝ} (hf : Bdd f) :
    Bdd (S T β f) ∧ ∀ x, S T β f x = β * T.M (S T β f) x + f x := by
  obtain ⟨B, hB⟩ := hf
  have hB0 : 0 ≤ |B| := abs_nonneg B
  obtain ⟨h1, h2⟩ := fwdS_spec T hβ hB0 (fun x => (hB x).trans (le_abs_self B))
  exact ⟨⟨_, h1⟩, h2⟩

/-- Woodford (2003), App. A.3: a bounded solution of `g = βMg + f` is `S f`. -/
theorem S_unique {β : ℝ} (hβ : |β| < 1) {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g)
    (h : ∀ x, g x = β * T.M g x + f x) : g = S T β f := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  funext x
  exact fwdS_unique T hβ (abs_nonneg A) (fun y => (hA y).trans (le_abs_self A)) hB h x

/-- Bounded functions: linear combinations. -/
theorem Bdd.lin {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) (a b : ℝ) :
    Bdd (fun x => a * f x + b * g x) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨|a| * A + |b| * B, fun x => ?_⟩
  calc _ ≤ |a * f x| + |b * g x| := abs_add_le _ _
    _ = |a| * |f x| + |b| * |g x| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hA x) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg b))

/-- Bounded functions: congruence. -/
theorem Bdd.congr {f g : X → ℝ} (hf : Bdd f) (h : ∀ x, f x = g x) : Bdd g := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun x => (h x) ▸ hA x⟩

/-- Bounded functions: products. -/
theorem Bdd.mul {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd (fun x => f x * g x) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨|A| * |B|, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hA x).trans (le_abs_self A)) ((hB x).trans (le_abs_self B))
    (abs_nonneg _) (abs_nonneg _)

/-- Bounded functions: the expectation. -/
theorem Bdd.M {f : X → ℝ} (hf : Bdd f) : Bdd (T.M f) := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun x => T.markov.2 f A hA x⟩

/-- Bounded functions: the lag. -/
theorem Bdd.lag {f : X → ℝ} (hf : Bdd f) : Bdd (lag0 T f) := by
  obtain ⟨A, hA⟩ := hf
  refine ⟨|A|, fun x => abs_lag0_le T (abs_nonneg A) (fun y => (hA y).trans (le_abs_self A)) x⟩

/-- Woodford (2003), §1: the discounted sum is linear. -/
theorem S_lin {β : ℝ} (hβ : |β| < 1) {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) (a b : ℝ) :
    S T β (fun x => a * f x + b * g x) = fun x => a * S T β f x + b * S T β g x := by
  obtain ⟨hSf, hf'⟩ := S_spec T hβ hf
  obtain ⟨hSg, hg'⟩ := S_spec T hβ hg
  refine (S_unique T hβ (hf.lin hg a b) (hSf.lin hSg a b) fun x => ?_).symm
  have e := congrFun (M_lin T a b (S T β f) (S T β g)) x
  rw [e, hf' x, hg' x]
  ring

/-- Woodford (2003), §1: the discounted sum of `0` is `0`. -/
theorem S_zero {β : ℝ} (hβ : |β| < 1) : S T β (fun _ => 0) = fun _ => 0 :=
  (S_unique T hβ ⟨0, fun _ => by simp⟩ ⟨0, fun _ => by simp⟩ fun x => by
    rw [M_const T]; ring).symm

/-- Woodford (2003), §1 (**positivity**): the discounted sum of a nonnegative bounded function is
nonnegative (a maximum principle: the infimum `m` of `S f` satisfies `m ≥ βm`). -/
theorem S_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : X → ℝ} (hf : Bdd f)
    (h0 : ∀ x, 0 ≤ f x) (x : X) : 0 ≤ S T β f x := by
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  obtain ⟨⟨B, hB⟩, hS⟩ := S_spec T hβ hf
  have : Nonempty X := ⟨x⟩
  have hbdd : BddBelow (Set.range (S T β f)) :=
    ⟨-B, by rintro _ ⟨y, rfl⟩; linarith [neg_abs_le (S T β f y), hB y]⟩
  set m := ⨅ y, S T β f y with hm
  have hmle : ∀ y, m ≤ S T β f y := fun y => ciInf_le hbdd y
  have hMm : ∀ y, m ≤ T.M (S T β f) y := fun y => by
    have h := M_nonneg T (k := fun z => S T β f z - m) (C := B - m) (fun z => by
      linarith [hmle z]) (fun z => by linarith [le_abs_self (S T β f z), hB z]) y
    have e := congrFun (M_lin T 1 (-m) (S T β f) (fun _ => 1)) y
    simp only [one_mul, mul_one, ← sub_eq_add_neg, M_const T] at e
    rw [e] at h
    linarith
  have hge : β * m ≤ m := le_ciInf fun y => by
    rw [hS y]
    nlinarith [hMm y, h0 y]
  have hm0 : 0 ≤ m := by nlinarith
  exact hm0.trans (hmle x)

/-- Woodford (2003), §1: the discounted sum is monotone. -/
theorem S_mono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g)
    (h : ∀ x, f x ≤ g x) (x : X) : S T β f x ≤ S T β g x := by
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have := S_nonneg T hβ0 hβ1 (hg.lin hf 1 (-1)) (fun y => by linarith [h y]) x
  rw [S_lin T hβ hg hf] at this
  linarith

/-- Woodford (2003), §1: `S f ≥ f` for `f ≥ 0`. -/
theorem S_ge {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : X → ℝ} (hf : Bdd f)
    (h0 : ∀ x, 0 ≤ f x) (x : X) : f x ≤ S T β f x := by
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  obtain ⟨⟨B, hB⟩, hS⟩ := S_spec T hβ hf
  rw [hS x]
  have : 0 ≤ T.M (S T β f) x := M_nonneg T (C := B) (fun y => S_nonneg T hβ0 hβ1 hf h0 y)
    (fun y => (le_abs_self _).trans (hB y)) x
  nlinarith

/-! ## The expectation and the lag -/

/-- Woodford (2003), App. A.3 (**the expectation sees the current node in the lag**): for bounded
`f, g`, `M(f · lag g)(x) = g(x) · (Mf)(x)`. -/
theorem M_lag_mul {f g : X → ℝ} (hf : Bdd f) (hg : Bdd g) (x : X) :
    T.M (fun y => f y * lag0 T g y) x = g x * T.M f x := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  have hd : T.M (fun y => f y * lag0 T g y - g x * f y) x = 0 := by
    have h := M_le_children T x (h := fun y => f y * lag0 T g y - g x * f y)
      (C := |A| * |B| + |B| * |A|) (B := 0) (fun y => by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul ((hA y).trans (le_abs_self A)) (abs_lag0_le T (abs_nonneg B)
            (fun z => (hB z).trans (le_abs_self B)) y) (abs_nonneg _) (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul ((hB x).trans (le_abs_self B)) ((hA y).trans (le_abs_self A))
            (abs_nonneg _) (abs_nonneg _)) le_rfl (fun y hy hy0 => by
        simp only [lag0, hy0, hy, ↓reduceIte, mul_comm (f y) (g x), sub_self, abs_zero, le_refl])
    exact abs_nonpos_iff.1 h
  have e := congrFun (M_lin T 1 (-(g x)) (fun y => f y * lag0 T g y) f) x
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at e
  rw [e] at hd
  linarith

/-- Woodford (2003), App. A.3 (**Jensen**): `(Mf)² ≤ M(f²)` for bounded `f`. -/
theorem M_sq_le {f : X → ℝ} (hf : Bdd f) (x : X) : T.M f x ^ 2 ≤ T.M (fun y => f y ^ 2) x := by
  obtain ⟨A, hA⟩ := hf
  set c := T.M f x with hc
  have h := M_nonneg T (k := fun y => (f y - c) ^ 2) (C := (|A| + |c|) ^ 2) (fun y => sq_nonneg _)
    (fun y => by
      have : |f y - c| ≤ |A| + |c| := (abs_sub _ _).trans (add_le_add ((hA y).trans
        (le_abs_self A)) le_rfl)
      calc (f y - c) ^ 2 = |f y - c| ^ 2 := (sq_abs _).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2) x
  have e : (fun y => (f y - c) ^ 2) = fun y => 1 * (f y ^ 2) + (-2 * c) * f y + c ^ 2 * 1 := by
    funext y; ring
  rw [e] at h
  have e1 := congrFun (M_lin T 1 (-2 * c) (fun y => f y ^ 2) f) x
  have e2 := congrFun (M_lin T 1 (c ^ 2) (fun y => 1 * (f y ^ 2) + (-2 * c) * f y)
    (fun _ => 1)) x
  simp only [one_mul] at e1 e2
  simp only [one_mul] at h
  rw [e2, M_const T] at h
  rw [e1] at h
  nlinarith

/-- Woodford (2003), Ch. 7 (**regrouping, the law of iterated expectations in discounted sums**):
for bounded `a, h`, `S[a · lag h] = a · lag h + βS[(Ma) h]`. -/
theorem S_lag {β : ℝ} (hβ : |β| < 1) {a h : X → ℝ} (ha : Bdd a) (hh : Bdd h) :
    S T β (fun y => a y * lag0 T h y) =
      fun y => a y * lag0 T h y + β * S T β (fun z => T.M a z * h z) y := by
  have hMa : Bdd (fun z => T.M a z * h z) := (ha.M T).mul hh
  obtain ⟨hSb, hS⟩ := S_spec T hβ hMa
  have hb : Bdd (fun y => a y * lag0 T h y + β * S T β (fun z => T.M a z * h z) y) :=
    ((ha.mul (hh.lag T)).lin hSb 1 β).congr fun y => by ring
  refine (S_unique T hβ (ha.mul (hh.lag T)) hb fun y => ?_).symm
  have e := congrFun (M_lin T 1 β (fun z => a z * lag0 T h z)
    (S T β (fun z => T.M a z * h z))) y
  simp only [one_mul] at e
  rw [e, M_lag_mul T ha hh y, hS y]
  ring

/-- Woodford (2003), Ch. 7 (**at a root the lag shifts the discounted sum by one period**):
`S[lag h](x₀) = βS[h](x₀)` for a root `x₀`. -/
theorem S_lag_root {β : ℝ} (hβ : |β| < 1) {h : X → ℝ} (hh : Bdd h) {x : X}
    (hx : T.depth x = 0) : S T β (lag0 T h) x = β * S T β h x := by
  have h1 : Bdd (fun _ : X => (1 : ℝ)) := ⟨1, fun _ => by simp⟩
  have e := congrFun (S_lag T hβ h1 hh) x
  have e1 : (fun y => (1 : ℝ) * lag0 T h y) = lag0 T h := by funext y; ring
  have e2 : (fun z => T.M (fun _ => (1 : ℝ)) z * h z) = h := by
    funext z; rw [M_const T]; ring
  rw [e1, e2] at e
  rw [e]
  simp [lag0, hx]

/-- Woodford (2003), §1: the discounted sum commutes with the expectation, `S[Mf] = M(Sf)`. -/
theorem S_M {β : ℝ} (hβ : |β| < 1) {f : X → ℝ} (hf : Bdd f) : S T β (T.M f) = T.M (S T β f) := by
  obtain ⟨hSb, hS⟩ := S_spec T hβ hf
  refine (S_unique T hβ (hf.M T) (hSb.M T) fun x => ?_).symm
  have e : S T β f = fun x => β * T.M (S T β f) x + 1 * f x := by funext y; rw [hS y]; ring
  have := congrFun (congrArg T.M e) x
  rw [M_lin T β 1] at this
  rw [this]
  ring

/-- Woodford (2003), §1: `S[Mf] ≤ Sf/β` for `f ≥ 0` and `β > 0`. -/
theorem S_M_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {f : X → ℝ} (hf : Bdd f) (h0 : ∀ x, 0 ≤ f x)
    (x : X) : S T β (T.M f) x ≤ S T β f x / β := by
  have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  rw [S_M T hβ hf, le_div_iff₀ hβ0]
  have := (S_spec T hβ hf).2 x
  nlinarith [h0 x]

/-- **Woodford (2003), App. A.3 (a forward bound in the discounted `ℓ²` norm).** If
`0 ≤ u ≤ v + κMu` with `u, v` bounded, `0 < β < 1` and `0 ≤ κ < β`, then
`Su ≤ Sv/(1 − κ/β)` at every node. -/
theorem S_forward_bound {β κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ0 : 0 ≤ κ) (hκ : κ < β)
    {u v : X → ℝ} (hu : Bdd u) (hv : Bdd v) (hu0 : ∀ x, 0 ≤ u x)
    (h : ∀ x, u x ≤ v x + κ * T.M u x) (x : X) : S T β u x ≤ S T β v x / (1 - κ / β) := by
  have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have h1 := S_mono T hβ0.le hβ1 hu (hv.lin (hu.M T) 1 κ) (fun y => by linarith [h y]) x
  rw [S_lin T hβ hv (hu.M T)] at h1
  have h2 := S_M_le T hβ0 hβ1 hu hu0 x
  have hpos : 0 < 1 - κ / β := by rw [sub_pos, div_lt_one hβ0]; exact hκ
  rw [le_div_iff₀ hpos]
  have h3 : κ * S T β (T.M u) x ≤ κ * (S T β u x / β) := mul_le_mul_of_nonneg_left h2 hκ0
  have e : κ * (S T β u x / β) = κ / β * S T β u x := by ring
  nlinarith

/-- **Woodford (2003), App. A.3 (a backward bound in the discounted `ℓ²` norm).** If
`u ≤ v + κ lag u` with `u, v` bounded, `0 ≤ β < 1` and `κβ < 1`, then at every
root `x₀`, `Su(x₀) ≤ Sv(x₀)/(1 − κβ)`. -/
theorem S_backward_bound {β κ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : κ * β < 1)
    {u v : X → ℝ} (hu : Bdd u) (hv : Bdd v) (h : ∀ x, u x ≤ v x + κ * lag0 T u x) {x : X}
    (hx : T.depth x = 0) : S T β u x ≤ S T β v x / (1 - κ * β) := by
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have h1 := S_mono T hβ0 hβ1 hu (hv.lin (hu.lag T) 1 κ) (fun y => by linarith [h y]) x
  rw [S_lin T hβ hv (hu.lag T)] at h1
  beta_reduce at h1
  rw [S_lag_root T hβ hu hx] at h1
  have hpos : 0 < 1 - κ * β := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

end Woodford.StabilizationWelfare.TidyR6aTreeSum
