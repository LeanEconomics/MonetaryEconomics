/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyTree

/-!
# Geometric decay: the inverse of the linearised Ramsey operator on weighted spaces

Woodford (2003), *Interest and Prices*, Chapter 6, §3.2, pp. 414–415 ("the deterministic path for
planned inflation should converge asymptotically to zero") and Chapter 7, §1 (the optimal
commitment converges to the timeless plan); Appendix A.3 (the implicit function theorem in
sequence space).

`NonlinearNKMarkovRamseyTree.LinvR_bound` bounds the inverse `L⁻¹` of the linearised Ramsey operator
in the sup norm. Here it is bounded on the WEIGHTED space of processes with
`|v(y)| ≤ C μ^{date(y)}` for any `μ` with `max(α, z₁) < μ ≤ 1` (`α` the Calvo probability, `z₁`
the stable root of the commitment system): forcing that decays geometrically produces a response
that decays geometrically at the same rate. This is the linear ingredient of the convergence of
the date-0 optimal plan to the timeless plan.

## Main results

* Markov operators on event trees are positive (`M_nonneg`) and see only the successors of a
  node (`M_le_children`); the date of an iterated parent (`depth_iterate`).
* The weighted bound `WB` and its calculus: linear combinations (`WB.lin`), the expectation
  (`WB.M`), the lag (`WB.lag`), the backward solution with root `c < μ` (`WB.back`), the forward
  solution with root `|c| < 1` (`WB.fwd`).
* Weighted bounds for every block of the inverse (`wbd_Dv`, …, `wbd_l3v`) and
  **`wLinvR_bound`**: `‖L⁻¹r(y)‖ ≤ K C μ^{date(y)}` whenever `‖r(y)‖ ≤ C μ^{date(y)}`, with `K`
  depending only on the parameters and `μ`, uniformly over event trees.
-/

namespace Woodford.StabilizationWelfare.TidyR5RamseyWeighted

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree

variable {X : Type*} (T : LagTree X)

/-! ## Markov operators on event trees -/

/-- Woodford (2003), App. A.3: a Markov operator is positive: `0 ≤ k ≤ C` gives `0 ≤ Mk`. -/
theorem M_nonneg {k : X → ℝ} {C : ℝ} (h0 : ∀ y, 0 ≤ k y) (hC : ∀ y, k y ≤ C) (x : X) :
    0 ≤ T.M k x := by
  have hb : ∀ y, |2 * k y - C| ≤ C := fun y => abs_le.2 ⟨by linarith [h0 y], by linarith [hC y]⟩
  have h := T.markov.2 (fun y => 2 * k y - C) C hb x
  have e : T.M (fun y => 2 * k y - C) x = 2 * T.M k x - C := by
    have := congrFun (M_lin T 2 (-C) k (fun _ => 1)) x
    simp only [mul_one] at this
    rw [show (fun y => 2 * k y - C) = fun y => 2 * k y + -C by funext y; ring, this,
      M_const T]
    ring
  rw [e] at h
  linarith [(abs_le.1 h).1]

/-- Woodford (2003), App. A.3 (**the expectation sees only the successors**): if `|h| ≤ C`
everywhere and `|h(y)| ≤ B` at every successor `y` of `x` (`par y = x`, `y` not a root), then
`|(Mh)(x)| ≤ B`. -/
theorem M_le_children (x : X) {h : X → ℝ} {C B : ℝ} (hC : ∀ y, |h y| ≤ C) (hB : 0 ≤ B)
    (hch : ∀ y, T.par y = x → T.depth y ≠ 0 → |h y| ≤ B) : |T.M h x| ≤ B := by
  classical
  set χ : X → ℝ := fun y => if T.par y = x ∧ T.depth y ≠ 0 then 1 else 0 with hχ
  have hχx : T.M χ x = 1 := by
    have e1 : T.M χ = T.M (fun y => (fun z => if z = x then (1 : ℝ) else 0) (T.par y)) :=
      T.M_root _ _ (fun y hy => by simp [hχ, hy])
    rw [e1, T.M_par (fun z => if z = x then (1 : ℝ) else 0)]
    simp
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  have hχ01 : ∀ y, χ y = 0 ∨ χ y = 1 := fun y => by
    by_cases hy : T.par y = x ∧ T.depth y ≠ 0 <;> simp [hχ, hy]
  set h1 : X → ℝ := fun y => h y * χ y with hh1
  set h2 : X → ℝ := fun y => h y * (1 - χ y) with hh2
  have hb1 : ∀ y, |h1 y| ≤ B := fun y => by
    by_cases hy : T.par y = x ∧ T.depth y ≠ 0
    · simp only [hh1, hχ, hy, ne_eq, not_false_eq_true, and_self, ↓reduceIte, mul_one]
      exact hch y hy.1 hy.2
    · simp only [hh1, hχ, hy, ↓reduceIte, mul_zero, abs_zero]
      exact hB
  have hM1 := T.markov.2 h1 B hb1 x
  have hpm : ∀ s : ℝ, |s| = 1 → 0 ≤ T.M (fun y => C * (1 - χ y) + s * h2 y) x := by
    intro s hs
    refine M_nonneg T (C := 2 * C) (fun y => ?_) (fun y => ?_) x
    · rcases hχ01 y with h0 | h0 <;> simp only [hh2, h0]
      · have := neg_abs_le (s * h y)
        rw [abs_mul, hs, one_mul] at this
        nlinarith [hC y]
      · simp
    · rcases hχ01 y with h0 | h0 <;> simp only [hh2, h0]
      · have := le_abs_self (s * h y)
        rw [abs_mul, hs, one_mul] at this
        nlinarith [hC y]
      · simp; linarith
  have hlin : ∀ s : ℝ, T.M (fun y => C * (1 - χ y) + s * h2 y) x = s * T.M h2 x := by
    intro s
    have e := congrFun (M_lin T C s (fun y => 1 - χ y) h2) x
    have e2 := congrFun (M_lin T 1 (-1) (fun _ => 1) χ) x
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, M_const T] at e2
    rw [e, e2, hχx]
    ring
  have hz : T.M h2 x = 0 := by
    have a1 := hpm 1 (by simp)
    have a2 := hpm (-1) (by simp)
    rw [hlin] at a1 a2
    linarith
  have hs : T.M h x = T.M h1 x + T.M h2 x := by
    have : h = h1 + h2 := by funext y; simp only [hh1, hh2, Pi.add_apply]; ring
    rw [this, map_add]; rfl
  rw [hs, hz, add_zero]
  exact hM1

/-- Woodford (2003), Ch. 7: the date of the `j`-th ancestor is `date − j` (for `j ≤ date`). -/
theorem depth_iterate : ∀ (j : ℕ) (x : X), j ≤ T.depth x → T.depth (T.par^[j] x) = T.depth x - j
  | 0, x, _ => by simp
  | j + 1, x, hj => by
    have hx : T.depth x ≠ 0 := by omega
    have hp := T.depth_par x hx
    rw [Function.iterate_succ_apply, depth_iterate j (T.par x) (by omega)]
    omega

/-! ## Weighted bounds -/

/-- Woodford (2003), Ch. 7 (**geometric decay in the date**): `|f(y)| ≤ C μ^{date(y)}`. -/
def WB (μ : ℝ) (f : X → ℝ) (C : ℝ) : Prop := ∀ y, |f y| ≤ C * μ ^ T.depth y

variable {T}

/-- Woodford (2003), Ch. 7: weighted bounds of linear combinations. -/
theorem WB.lin {μ : ℝ} {f g : X → ℝ} {cf cg A : ℝ} (hf : WB T μ f (cf * A))
    (hg : WB T μ g (cg * A)) (k1 k2 : ℝ) :
    WB T μ (fun y => k1 * f y + k2 * g y) ((|k1| * cf + |k2| * cg) * A) := fun y => by
  have h1 := mul_le_mul_of_nonneg_left (hf y) (abs_nonneg k1)
  have h2 := mul_le_mul_of_nonneg_left (hg y) (abs_nonneg k2)
  calc _ ≤ |k1 * f y| + |k2 * g y| := abs_add_le _ _
    _ = |k1| * |f y| + |k2| * |g y| := by rw [abs_mul, abs_mul]
    _ ≤ _ := by nlinarith

/-- Woodford (2003), Ch. 7: weighted bounds are monotone in the constant. -/
theorem WB.mono {μ : ℝ} {f : X → ℝ} {C C' : ℝ} (hμ : 0 ≤ μ) (h : C ≤ C') (hf : WB T μ f C) :
    WB T μ f C' := fun y => (hf y).trans (mul_le_mul_of_nonneg_right h (pow_nonneg hμ _))

/-- Woodford (2003), Ch. 7: weighted bounds transfer along pointwise equality. -/
theorem WB.congr {μ : ℝ} {f g : X → ℝ} {C : ℝ} (h : ∀ y, f y = g y) (hg : WB T μ g C) :
    WB T μ f C := fun y => by rw [h]; exact hg y

/-- Woodford (2003), Ch. 7: for `μ ≤ 1` a weighted bound is a sup bound. -/
theorem WB.bdd {μ : ℝ} {f : X → ℝ} {C : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hC : 0 ≤ C)
    (hf : WB T μ f C) (y : X) : |f y| ≤ C :=
  (hf y).trans (by
    have := pow_le_one₀ hμ0 hμ1 (n := T.depth y)
    nlinarith [pow_nonneg hμ0 (T.depth y)])

/-- Woodford (2003), App. A.3: the expectation keeps weighted bounds (`μ ≤ 1`). -/
theorem WB.M {μ : ℝ} {f : X → ℝ} {C : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hC : 0 ≤ C)
    (hf : WB T μ f C) : WB T μ (T.M f) C := fun x => by
  refine M_le_children T x (C := C) (hf.bdd hμ0.le hμ1 hC) (by positivity) fun y hy hy0 => ?_
  have hd := T.depth_par y hy0
  rw [hy] at hd
  refine (hf y).trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [← hd]
  exact pow_le_pow_of_le_one hμ0.le hμ1 (Nat.le_succ _)

/-- Woodford (2003), Ch. 7: the lag of a weighted process, constant divided by `μ`. -/
theorem WB.lag {μ : ℝ} {f : X → ℝ} {C : ℝ} (hμ0 : 0 < μ) (hC : 0 ≤ C) (hf : WB T μ f C) :
    WB T μ (lag0 T f) (C / μ) := fun x => by
  unfold lag0
  split_ifs with h
  · simp only [abs_zero]; positivity
  · have hp := T.depth_par x h
    refine (hf _).trans (le_of_eq ?_)
    rw [← hp, pow_succ]
    field_simp

/-- Woodford (2003), Ch. 7 (**the backward solution decays**): for `0 ≤ c < μ ≤ 1`,
`bwd c f` keeps the weighted bound with the constant `C/(1 − c/μ)`. -/
theorem WB.back {μ c : ℝ} {f : X → ℝ} {C : ℝ} (hc0 : 0 ≤ c) (hcμ : c < μ) (hC : 0 ≤ C)
    (hf : WB T μ f C) : WB T μ (NonlinearNKMarkovRamseyTree.bwd T c f) (C / (1 - c / μ)) :=
    fun x => by
  have hμ0 : 0 < μ := lt_of_le_of_lt hc0 hcμ
  have hq0 : 0 ≤ c / μ := div_nonneg hc0 hμ0.le
  have hq1 : c / μ < 1 := (div_lt_one hμ0).2 hcμ
  set d := T.depth x
  have hterm : ∀ j ∈ Finset.range (d + 1), |c ^ j * f (T.par^[j] x)| ≤
      C * μ ^ d * (c / μ) ^ j := by
    intro j hj
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hdep := depth_iterate T j x hjd
    rw [abs_mul, abs_of_nonneg (pow_nonneg hc0 j)]
    have hb := hf (T.par^[j] x)
    rw [hdep] at hb
    have e : C * μ ^ d * (c / μ) ^ j = c ^ j * (C * μ ^ (d - j)) := by
      rw [div_pow]
      have : μ ^ d = μ ^ (d - j) * μ ^ j := by rw [← pow_add, Nat.sub_add_cancel hjd]
      rw [this]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hb (pow_nonneg hc0 j)
  unfold NonlinearNKMarkovRamseyTree.bwd
  calc _ ≤ ∑ j ∈ Finset.range (d + 1), |c ^ j * f (T.par^[j] x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (d + 1), C * μ ^ d * (c / μ) ^ j := Finset.sum_le_sum hterm
    _ = C * μ ^ d * ∑ j ∈ Finset.range (d + 1), (c / μ) ^ j := by rw [Finset.mul_sum]
    _ ≤ C * μ ^ d * (1 - c / μ)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← tsum_geometric_of_lt_one hq0 hq1]
        exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hq0 j)
          (summable_geometric_of_lt_one hq0 hq1)
    _ = C / (1 - c / μ) * μ ^ d := by rw [div_eq_mul_inv]; ring

/-- Woodford (2003), (A.13) (**the forward solution decays**): for `|c| < 1` and `0 < μ ≤ 1`,
`fwdS c f` keeps the weighted bound with the constant `C/(1 − |c|)`. -/
theorem WB.fwd {μ c : ℝ} {f : X → ℝ} {C : ℝ} (hc : |c| < 1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : 0 ≤ C) (hf : WB T μ f C) :
    WB T μ (NonlinearNKMarkovRamseyTree.fwdS T c f) (C / (1 - |c|)) := by
  obtain ⟨hg, heq⟩ := fwdS_spec T hc hC (hf.bdd hμ0.le hμ1 hC)
  set g := NonlinearNKMarkovRamseyTree.fwdS T c f
  set G := Sg c * C
  have hG0 : 0 ≤ G := mul_nonneg (Sg_nonneg c) hC
  have hq0 := abs_nonneg c
  set a : ℕ → ℝ := fun n => C * ∑ k ∈ Finset.range n, |c| ^ k with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n =>
    mul_nonneg hC (Finset.sum_nonneg fun k _ => pow_nonneg hq0 k)
  have hstep : ∀ n x, |g x| ≤ a n * μ ^ T.depth x + |c| ^ n * G := by
    intro n
    induction n with
    | zero => intro x; simpa [ha] using hg x
    | succ n ih =>
      intro x
      have hM : |T.M g x| ≤ a n * μ ^ (T.depth x + 1) + |c| ^ n * G := by
        refine M_le_children T x (C := G) hg (by positivity) fun y hy hy0 => ?_
        have hd := T.depth_par y hy0
        rw [hy] at hd
        rw [hd]
        exact ih y
      have hpow : μ ^ (T.depth x + 1) ≤ μ ^ T.depth x :=
        pow_le_pow_of_le_one hμ0.le hμ1 (Nat.le_succ _)
      have hsum : a (n + 1) = |c| * a n + C := by
        simp only [ha, Finset.sum_range_succ', pow_succ, pow_zero]
        rw [← Finset.sum_mul]
        ring
      rw [heq x, hsum]
      calc |c * T.M g x + f x| ≤ |c| * |T.M g x| + |f x| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |c| * (a n * μ ^ (T.depth x + 1) + |c| ^ n * G) + C * μ ^ T.depth x :=
            add_le_add (mul_le_mul_of_nonneg_left hM hq0) (hf x)
        _ ≤ (|c| * a n + C) * μ ^ T.depth x + |c| ^ (n + 1) * G := by
            have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hq0 (ha0 n))
            have key : (|c| * a n + C) * μ ^ T.depth x + |c| ^ (n + 1) * G -
                (|c| * (a n * μ ^ (T.depth x + 1) + |c| ^ n * G) + C * μ ^ T.depth x) =
                |c| * a n * μ ^ T.depth x - |c| * a n * μ ^ (T.depth x + 1) := by ring
            linarith
  intro x
  have hs : Tendsto (fun n => ∑ k ∈ Finset.range n, |c| ^ k) atTop (𝓝 (1 - |c|)⁻¹) := by
    rw [← tsum_geometric_of_lt_one hq0 hc]
    exact (summable_geometric_of_lt_one hq0 hc).hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun n => C * (∑ k ∈ Finset.range n, |c| ^ k) * μ ^ T.depth x +
      |c| ^ n * G) atTop (𝓝 (C * (1 - |c|)⁻¹ * μ ^ T.depth x + 0 * G)) :=
    ((hs.const_mul C).mul_const _).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hc).mul_const G)
  rw [zero_mul, add_zero] at hlim
  rw [div_eq_mul_inv]
  exact ge_of_tendsto' hlim fun n => hstep n x

/-! ## Weighted bounds for the blocks of the inverse -/

variable {p : Par} {μ : ℝ}

/-- Woodford (2003), App. A.3: a weighted bound on the dispersion part of the inverse. -/
theorem wbd_Dv (hp : p.Std) (hμα : p.α < μ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ k, WB T μ (fun y => r y k) (1 * A)) →
      WB T μ (Dv T p r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  have hq : 0 < 1 - p.α / μ := by rw [sub_pos, div_lt_one hμ0]; exact hμα
  set k := aE p / (p.θ - 1)
  refine ⟨(|k| * 1 + |1| * 1) / (1 - p.α / μ), div_nonneg (by positivity) hq.le,
    fun T r A hA hr => ?_⟩
  have hin := WB.lin (hr 7) (hr 8) k 1
  have hb := WB.back hp.α_pos.le hμα (by positivity) hin
  refine (hb.congr fun y => ?_).mono hμ0.le (le_of_eq (by ring))
  simp only [Dv, k, one_mul]

/-- Woodford (2003), App. A.3: a weighted bound on the summed-multiplier part of the inverse. -/
theorem wbd_Muv (R : RPar) (hp : p.Std) (hμα : p.α < μ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*}
    (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (Muv T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  have hq : 0 < 1 - p.α / μ := by rw [sub_pos, div_lt_one hμ0]; exact hμα
  set k := ramseyLam p R 0 * p.c0 / (p.θ - 1)
  refine ⟨(|1| * (|1| * 1 + |1| * 1) + |-k| * 1) / (1 - p.α / μ),
    div_nonneg (by positivity) hq.le, fun T r A hA hr => ?_⟩
  have hin := WB.lin (WB.lin (hr 2) (hr 3) 1 1) (hr 7) 1 (-k)
  have hb := WB.back hp.α_pos.le hμα (by positivity) hin
  refine (hb.congr fun y => ?_).mono hμ0.le (le_of_eq (by ring))
  simp only [Muv, k]
  congr 1
  funext x
  ring

/-- Woodford (2003), App. A.3: a weighted bound on the NKPC forcing. -/
theorem wbd_gv (hp : p.Std) (hμα : p.α < μ) (hμ1 : μ ≤ 1) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*}
    (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (gv T p r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  set k1 := (1 - p.α) / (p.c0 * p.α)
  set k2 := 1 / (p.α * (p.θ - 1))
  refine ⟨|k1| * (|1| * 1 + |-1| * 1) + |k2| * (|1| * 1 + |-(p.α * p.β)| * 1), by positivity,
    fun T r A hA hr => ?_⟩
  have h65 := WB.lin (hr 6) (hr 5) 1 (-1)
  have h77 := WB.lin (hr 7) ((hr 7).M hμ0 hμ1 (by positivity)) 1 (-(p.α * p.β))
  refine (WB.lin h65 h77 k1 k2).congr fun y => ?_
  simp only [gv, k1, k2]
  ring

/-- Woodford (2003), App. A.3: a weighted bound on the targeting-rule forcing. -/
theorem wbd_fv (R : RPar) (hp : p.Std) (hμα : p.α < μ) : ∃ c, 0 ≤ c ∧
    ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (fv T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨cD, hcD, hD⟩ := wbd_Dv hp hμα
  obtain ⟨cM, hcM, hM⟩ := wbd_Muv R hp hμα
  set s := (1 - p.α * p.β) * (p.σ + p.ω)
  set k0 := (1 - p.α) * aE p / p.c0
  set k7 := (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1)
  set k1 := (1 - p.α) / (p.α * p.c0)
  set Av := (1 - R.Φ) * R.Au
  set s2 := (1 - p.α * p.β) * (1 + p.ω)
  set c1 := |-k0| * (|1| * (cM / μ) + |ramseyLam p R 3| * (cD / μ)) + |-k7| * 1
  set c2 := |1| * c1 + |1| * (|1| * 1 + |-k1| * 1)
  set c3 := |1| * (|1| * 1 + |-1| * (1 / μ)) + |Av| * (|1| * cD + |-1| * (cD / μ))
  set c4 := |s| * c2 + |-1| * (|1| * c3 + |s2| * (|1| * cM + |-1| * (cM / μ)))
  refine ⟨|1 / (R.Au * Gw p R)| * c4, by positivity, fun {Y} T r A hA hr => ?_⟩
  have lagc : ∀ {f : Y → ℝ} {c : ℝ}, 0 ≤ c → WB T μ f (c * A) → WB T μ (lag0 T f) (c / μ * A) :=
    fun {f} {c} hc hf => (WB.lag hμ0 (by positivity) hf).mono hμ0.le (le_of_eq (by ring))
  have hDA := hD T r A hA hr
  have hMA := hM T r A hA hr
  have hDl := lagc hcD hDA
  have hMl := lagc hcM hMA
  have h0l := lagc zero_le_one (hr 0)
  have e1 := WB.lin (WB.lin hMl hDl 1 (ramseyLam p R 3)) (hr 7) (-k0) (-k7)
  have e2 := WB.lin e1 (WB.lin (hr 2) (hr 1) 1 (-k1)) 1 1
  have e3 := WB.lin (hr 0) h0l 1 (-1)
  have e4 := WB.lin e3 (WB.lin hDA hDl 1 (-1)) 1 Av
  have e5 := WB.lin e4 (WB.lin hMA hMl 1 (-1)) 1 s2
  have e6 := WB.lin e2 e5 s (-1)
  have e7 : WB T μ (Ftv T p R r) (c4 * A) := by
    refine (e6.congr fun y => ?_).mono hμ0.le (le_of_eq (by simp only [c4, c2, c1, c3]; try ring))
    simp only [Ftv, s, k0, k7, k1, Av, s2]
    ring
  have e8 := WB.lin e7 (g := fun _ => (0 : ℝ)) (cg := 0) (fun y => by simp) (1 / (R.Au * Gw p R)) 0
  refine (e8.congr fun y => ?_).mono hμ0.le (le_of_eq (by ring))
  simp only [fv]
  ring

/-- Woodford (2003), App. A.3: a weighted bound on the forcing of the output equation. -/
theorem wbd_hv (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμ1 : μ ≤ 1) : ∃ c, 0 ≤ c ∧
    ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (hv T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨cg, hcg, hg⟩ := wbd_gv hp hμα hμ1
  obtain ⟨cf, hcf, hf⟩ := wbd_fv R hp hμα
  refine ⟨|1| * (|p.θ| * cg + |p.β| * cf) + |-1| * cf, by positivity, fun T r A hA hr => ?_⟩
  have hF := hf T r A hA hr
  refine (WB.lin (WB.lin (hg T r A hA hr) (hF.M hμ0 hμ1 (by positivity)) p.θ p.β) hF 1
    (-1)).congr fun y => ?_
  simp only [hv]
  ring

/-- Woodford (2003), App. A.3: a weighted bound on the forward factor `u`. -/
theorem wbd_uv (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμ1 : μ ≤ 1) : ∃ c, 0 ≤ c ∧
    ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (uv T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨ch, hch, hh⟩ := wbd_hv R hp hμα hμ1
  have hz := abs_inv_z2 hp
  have hq : 0 < 1 - |1 / z2 p| := by linarith
  refine ⟨(|-(1 / (p.β * z2 p))| * ch + |0| * 0) / (1 - |1 / z2 p|), div_nonneg (by positivity)
    hq.le, fun T r A hA hr => ?_⟩
  have hin := WB.lin (hh T r A hA hr) (g := fun _ => (0 : ℝ)) (cg := 0) (fun y => by simp)
    (-(1 / (p.β * z2 p))) 0
  have hfw := WB.fwd hz hμ0 hμ1 (by positivity)
    (hin.congr (f := fun y => -hv T p R r y / (p.β * z2 p)) fun y => by ring)
  refine hfw.mono hμ0.le (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a weighted bound on output, `y = z₁ lag y + u` (`z₁ < μ`). -/
theorem wbd_yv (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (yv T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨cu, hcu, hu⟩ := wbd_uv R hp hμα hμ1
  obtain ⟨hz0, -, -, -, -⟩ := z_props hp
  have hq : 0 < 1 - z1 p / μ := by rw [sub_pos, div_lt_one hμ0]; exact hμz
  refine ⟨cu / (1 - z1 p / μ), div_nonneg hcu hq.le, fun T r A hA hr => ?_⟩
  exact (WB.back hz0.le hμz (by positivity) (hu T r A hA hr)).mono hμ0.le
    (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a weighted bound on inflation. -/
theorem wbd_piv (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (piv T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨cf, hcf, hf⟩ := wbd_fv R hp hμα
  obtain ⟨cy, hcy, hy⟩ := wbd_yv R hp hμα hμz hμ1
  refine ⟨|1 / p.θ| * (|1| * (|1| * cf + |-1| * cy) + |1| * (cy / μ)) + |0| * 0, by positivity,
    fun T r A hA hr => ?_⟩
  have hY := hy T r A hA hr
  have hYl : WB T μ (lag0 T (yv T p R r)) (cy / μ * A) :=
    (WB.lag hμ0 (by positivity) hY).mono hμ0.le (le_of_eq (by ring))
  have e := WB.lin (WB.lin (WB.lin (hf T r A hA hr) hY 1 (-1)) hYl 1 1)
    (g := fun _ => (0 : ℝ)) (cg := 0) (fun y => by simp) (1 / p.θ) 0
  refine e.congr fun y => ?_
  simp only [piv]
  ring

/-- Woodford (2003), App. A.3: a weighted bound on `F̂` (forward with root `αβ`). -/
theorem wbd_Fv (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (Fv T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨cy, hcy, hy⟩ := wbd_yv R hp hμα hμz hμ1
  obtain ⟨cπ, hcπ, hπ⟩ := wbd_piv R hp hμα hμz hμ1
  have hab := abs_ab hp
  have hq : 0 < 1 - |p.α * p.β| := by linarith
  set k1 := (1 - p.α * p.β) * (1 - p.σ)
  set k2 := p.α * p.β * (p.θ - 1)
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨ci / (1 - |p.α * p.β|), div_nonneg (by positivity) hq.le, fun T r A hA hr => ?_⟩
  have hin := WB.lin (WB.lin (hy T r A hA hr) ((hπ T r A hA hr).M hμ0 hμ1 (by positivity)) k1 k2)
    (hr 5) 1 1
  have hfw := WB.fwd hab hμ0 hμ1 (by positivity)
    (hin.congr (f := fun y => k1 * yv T p R r y + k2 * T.M (piv T p R r) y + r y 5) fun y => by
      ring)
  exact hfw.mono hμ0.le (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a weighted bound on `λ̂₄` (forward with root `αβ`). -/
theorem wbd_l4v (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (l4v T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨cy, hcy, hy⟩ := wbd_yv R hp hμα hμz hμ1
  obtain ⟨cπ, hcπ, hπ⟩ := wbd_piv R hp hμα hμz hμ1
  have hab := abs_ab hp
  have hq : 0 < 1 - |p.α * p.β| := by linarith
  set k1 := (1 - R.Φ) * R.Au
  set k2 := p.α * p.β * ramseyLam p R 3 * aE p
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨ci / (1 - |p.α * p.β|), div_nonneg (by positivity) hq.le, fun T r A hA hr => ?_⟩
  have hin := WB.lin (WB.lin (hy T r A hA hr) ((hπ T r A hA hr).M hμ0 hμ1 (by positivity)) k1 k2)
    (hr 4) 1 1
  have hfw := WB.fwd hab hμ0 hμ1 (by positivity)
    (hin.congr (f := fun y => k1 * yv T p R r y + k2 * T.M (piv T p R r) y + r y 4) fun y => by
      ring)
  exact hfw.mono hμ0.le (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a weighted bound on the relative price `x̂`. -/
theorem wbd_xv (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (xv T p R r) (c * A) := by
  obtain ⟨cπ, hcπ, hπ⟩ := wbd_piv R hp hμα hμz hμ1
  set k := 1 / ((1 - p.α) * (p.θ - 1))
  refine ⟨|k * (p.α * (p.θ - 1))| * cπ + |-k| * 1, by positivity, fun T r A hA hr => ?_⟩
  refine (WB.lin (hπ T r A hA hr) (hr 7) (k * (p.α * (p.θ - 1))) (-k)).congr fun y => ?_
  simp only [xv, k]
  ring

/-- Woodford (2003), App. A.3: a weighted bound on `λ̂₁`. -/
theorem wbd_l1v (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (l1v T p R r) (c * A) := by
  obtain ⟨cy, hcy, hy⟩ := wbd_yv R hp hμα hμz hμ1
  obtain ⟨cD, hcD, hD⟩ := wbd_Dv hp hμα
  obtain ⟨cM, hcM, hM⟩ := wbd_Muv R hp hμα
  set k := 1 / ((1 - p.α * p.β) * (p.σ + p.ω))
  set c1 := |k| * 1 + |k * (R.Au * Gw p R)| * cy
  set c2 := |k * ((1 - R.Φ) * R.Au)| * cD + |k * ((1 - p.α * p.β) * (1 + p.ω))| * cM
  refine ⟨|1| * c1 + |1| * c2, by positivity, fun T r A hA hr => ?_⟩
  have e1 := WB.lin (hr 0) (hy T r A hA hr) k (k * (R.Au * Gw p R))
  have e2 := WB.lin (hD T r A hA hr) (hM T r A hA hr) (k * ((1 - R.Φ) * R.Au))
    (k * ((1 - p.α * p.β) * (1 + p.ω)))
  refine (WB.lin e1 e2 1 1).congr fun y => ?_
  simp only [l1v, k]
  ring

/-- Woodford (2003), App. A.3: a weighted bound on `λ̂₃`. -/
theorem wbd_l3v (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ k, WB T μ (fun y => r y k) (1 * A)) → WB T μ (l3v T p R r) (c * A) := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨c1, hc1, h1⟩ := wbd_l1v R hp hμα hμz hμ1
  obtain ⟨cF, hcF, hF⟩ := wbd_Fv R hp hμα hμz hμ1
  obtain ⟨cπ, hcπ, hπ⟩ := wbd_piv R hp hμα hμz hμ1
  obtain ⟨c4, hc4, h4⟩ := wbd_l4v R hp hμα hμz hμ1
  obtain ⟨cx, hcx, hx⟩ := wbd_xv R hp hμα hμz hμ1
  set k := 1 / ((1 - p.α) * ((p.θ - 1) / p.c0))
  set L0 := ramseyLam p R 0
  set ka := (1 - p.α) * (aE p / p.c0)
  set La := ramseyLam p R 3 * aE p
  set Lb := ramseyLam p R 2 * (p.θ - 1)
  set d1 := |1| * 1 + |-1| * (|1| * c1 + |L0| * cF)
  set d2 := |1| * (c1 / μ) + |L0| * (|p.θ - 1| * cπ + |1| * cF)
  set d3 := |1| * c4 + |-La| * cx
  refine ⟨|k| * (|1| * (|1| * d1 + |p.α| * d2) + |ka| * d3) + |Lb| * cx, by positivity,
    fun T r A hA hr => ?_⟩
  have hl1 := h1 T r A hA hr
  have hFF := hF T r A hA hr
  have hl1l : WB T μ (lag0 T (l1v T p R r)) (c1 / μ * A) :=
    (WB.lag hμ0 (by positivity) hl1).mono hμ0.le (le_of_eq (by ring))
  have e1 := WB.lin (hr 2) (WB.lin hl1 hFF 1 L0) 1 (-1)
  have e2 := WB.lin hl1l (WB.lin (hπ T r A hA hr) hFF (p.θ - 1) 1) 1 L0
  have e12 := WB.lin e1 e2 1 p.α
  have e3 := WB.lin (h4 T r A hA hr) (hx T r A hA hr) 1 (-La)
  have e123 := WB.lin e12 e3 1 ka
  refine (WB.lin e123 (hx T r A hA hr) k Lb).congr fun y => ?_
  simp only [l3v, k, L0, ka, La, Lb]
  field_simp
  ring

/-- **Woodford (2003), App. A.3 and Ch. 7 (the inverse of the linearised Ramsey operator on the
weighted space).** For `max(α, z₁) < μ ≤ 1` there is `K ≥ 0`, depending only on the parameters
and `μ`, such that on every event tree, whenever `‖r(y)‖ ≤ A μ^{date(y)}`, the response satisfies
`‖L⁻¹r(y)‖ ≤ K A μ^{date(y)}`: geometrically decaying forcing produces geometrically decaying
responses. -/
theorem wLinvR_bound (R : RPar) (hp : p.Std) (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ K, 0 ≤ K ∧ ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y, ‖r y‖ ≤ A * μ ^ T.depth y) → ∀ y, ‖LinvR T p R r y‖ ≤ K * A * μ ^ T.depth y := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨c0, h0, b0⟩ := wbd_yv R hp hμα hμz hμ1
  obtain ⟨c1, h1, b1⟩ := wbd_piv R hp hμα hμz hμ1
  obtain ⟨c2, h2, b2⟩ := wbd_Fv R hp hμα hμz hμ1
  obtain ⟨cx, hx, bx⟩ := wbd_xv R hp hμα hμz hμ1
  obtain ⟨c4, h4, b4⟩ := wbd_Dv hp hμα
  obtain ⟨c5, h5, b5⟩ := wbd_l1v R hp hμα hμz hμ1
  obtain ⟨cμ, hcμ, bμ⟩ := wbd_Muv R hp hμα
  obtain ⟨c7, h7, b7⟩ := wbd_l3v R hp hμα hμz hμ1
  obtain ⟨c8, h8, b8⟩ := wbd_l4v R hp hμα hμz hμ1
  set K := c0 + c1 + c2 + (|1| * c2 + |p.c0| * cx) + c4 + c5 + (|1| * cμ + |-1| * c5) + c7 + c8
    with hK
  refine ⟨K, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ k, WB T μ (fun y => r y k) (1 * A) := fun k y => by
    have := (norm_le_pi_norm (r y) k).trans (hr y)
    rw [Real.norm_eq_abs] at this
    rw [one_mul]
    exact this
  have hKA : ∀ c, 0 ≤ c → c ≤ K → c * A * μ ^ T.depth y ≤ K * A * μ ^ T.depth y :=
    fun c _ hcK => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcK hA)
      (pow_nonneg hμ0.le _)
  have hpos := fun (z : ℝ) => abs_nonneg z
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i <;> simp only [LinvR, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact (b0 T r A hA hr' y).trans (hKA _ h0 (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · exact (b1 T r A hA hr' y).trans (hKA _ h1 (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · exact (b2 T r A hA hr' y).trans (hKA _ h2 (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · have e := WB.lin (b2 T r A hA hr') (bx T r A hA hr') 1 p.c0 y
    simp only [one_mul] at e
    exact e.trans (hKA _ (by positivity) (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · exact (b4 T r A hA hr' y).trans (hKA _ h4 (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · exact (b5 T r A hA hr' y).trans (hKA _ h5 (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · have e := WB.lin (bμ T r A hA hr') (b5 T r A hA hr') 1 (-1) y
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e
    exact e.trans (hKA _ (by positivity) (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · exact (b7 T r A hA hr' y).trans (hKA _ h7 (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))
  · exact (b8 T r A hA hr' y).trans (hKA _ h8 (by
      rw [hK]; nlinarith [hpos 1, hpos p.c0, hpos (-1)]))

end Woodford.StabilizationWelfare.TidyR5RamseyWeighted
