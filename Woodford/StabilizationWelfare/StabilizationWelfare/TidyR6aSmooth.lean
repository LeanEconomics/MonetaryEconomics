/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aExpand

/-!
# `C¹` dependence of the sequence-space Ramsey solution on the amplitude of the disturbances

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392: the welfare expansion
treats equilibrium variables as smooth functions of the amplitude of the disturbances) and §5,
Chapter 7, §1–2, and Appendix A.3 (the implicit function theorem in sequence space).

For disturbances `εê` and initial lags `ε²dh` (`‖ê‖, ‖dh‖ ≤ 1`), the exact Ramsey conditions
`Φ(ε, z) = 0` on an event tree have, for `|ε| ≤ δ₁`, a locally unique solution `Z(ε)`
(`TidyR6aExpand.ramsey_newton`). Here `ε ↦ Z(ε)` is shown to be `C¹` — indeed `C^{1,1}` — in the
sup norm over the nodes, with constants independent of the event tree:

* `taylor_gen`: for a `C²` map, a uniform second-order remainder, a Lipschitz derivative and a
  bounded derivative on a ball around `0`.
* `fixed_point_ball`: the contraction principle for bounded functions on the nodes.
* `Lin`, `Peps`: the partial derivatives of `Φ` at `(ε, z)` in `z` (a linear operator on node
  functions) and in `ε`; `lin_sub`, `lin_smul`, `lin_split` (linearity, and `Lin = L + Δ` with
  `L` the linearisation at the steady state).
* **`lin_solve`**: near the steady state `Lin(ε, z)` is invertible on bounded node functions,
  with a bound uniform over event trees (a Neumann-series argument around `LinvR`).
* `phi_expand`: `Φ(ε′, z′) − Φ(ε, z) − Lin(ε, z)(z′ − z) − (ε′ − ε)Peps(ε, z)` is quadratic in
  `(ε′ − ε, z′ − z)`.
* **`ramsey_C1`**: there are `δ₁ > 0` and constants such that on every event tree the solution
  family `Z` satisfies `Z(0) = 0`; for every `|ε₀|, |ε| ≤ δ₁`,
  `‖Z(ε) − Z(ε₀) − (ε − ε₀)V(ε₀)‖ ≤ C(ε − ε₀)²` (differentiability, with derivative
  `V(ε₀) = −Lin(ε₀, Z(ε₀))⁻¹Peps(ε₀, Z(ε₀))`), `‖V(ε) − V(ε₀)‖ ≤ C|ε − ε₀|` (the derivative is
  Lipschitz, hence continuous), and `V(0) = z₁ = L⁻¹(−DQe(ê))`.
-/

namespace Woodford.StabilizationWelfare.TidyR6aSmooth

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT TidyR6aShock TidyR6aExpand

/-- Woodford (2003), App. A.3 (**uniform Taylor bounds for a `C²` map**): there are `ρ > 0` and
`L ≥ 0` such that on the closed ball of radius `ρ` the derivative is bounded by `L` and
`L`-Lipschitz, and `‖g(q′) − g(q) − Dg(q)(q′ − q)‖ ≤ L‖q′ − q‖²`. -/
theorem taylor_gen {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : ContDiff ℝ 2 g) :
    ∃ ρ > 0, ∃ L, 0 ≤ L ∧ ∀ q q', ‖q‖ ≤ ρ → ‖q'‖ ≤ ρ →
      ‖fderiv ℝ g q‖ ≤ L ∧ ‖fderiv ℝ g q' - fderiv ℝ g q‖ ≤ L * ‖q' - q‖ ∧
        ‖g q' - g q - fderiv ℝ g q (q' - q)‖ ≤ L * ‖q' - q‖ ^ 2 := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := hg1.contDiffAt.exists_lipschitzOnWith (x := (0 : E))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  set ρ := δ / 2 with hρ
  have hsub : Metric.closedBall (0 : E) ρ ⊆ t := fun x hx => hball (by
    rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith)
  have hlip : ∀ x y : E, ‖x‖ ≤ ρ → ‖y‖ ≤ ρ →
      ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ K * ‖x - y‖ := fun x y hx hy => by
    have := hK.dist_le_mul x (hsub (by simpa using hx)) y (hsub (by simpa using hy))
    simpa [dist_eq_norm] using this
  set L := ‖fderiv ℝ g 0‖ + K * ρ + K with hL
  have hρ0 : 0 < ρ := by positivity
  have hKL : (K : ℝ) ≤ L := by
    rw [hL]; nlinarith [K.coe_nonneg, norm_nonneg (fderiv ℝ g 0)]
  refine ⟨ρ, hρ0, L, by positivity, fun q q' hq hq' => ⟨?_, ?_, ?_⟩⟩
  · calc ‖fderiv ℝ g q‖ ≤ ‖fderiv ℝ g q - fderiv ℝ g 0‖ + ‖fderiv ℝ g 0‖ := by
          have := norm_add_le (fderiv ℝ g q - fderiv ℝ g 0) (fderiv ℝ g 0); simpa using this
      _ ≤ K * ‖q - 0‖ + ‖fderiv ℝ g 0‖ := add_le_add (hlip q 0 hq (by simp [hρ0.le])) le_rfl
      _ ≤ L := by rw [sub_zero, hL]; nlinarith [K.coe_nonneg, norm_nonneg q]
  · exact (hlip q' q hq' hq).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))
  · set B := Metric.closedBall (0 : E) ρ with hB
    have hconv : Convex ℝ B := convex_closedBall 0 ρ
    have hdiff : ∀ x ∈ B, HasFDerivWithinAt (fun x => g x - fderiv ℝ g q x)
        (fderiv ℝ g x - fderiv ℝ g q) B x := fun x _ => by
      have h1 : HasFDerivAt g (fderiv ℝ g x) x := ((hg.differentiable (by norm_num)) x).hasFDerivAt
      exact (h1.sub (fderiv ℝ g q).hasFDerivAt).hasFDerivWithinAt
    -- restrict to the segment, a convex subset
    set S := segment ℝ q q' with hS
    have hSB : S ⊆ B := hconv.segment_subset (by simpa [hB] using hq) (by simpa [hB] using hq')
    have hbd : ∀ x ∈ S, ‖fderiv ℝ g x - fderiv ℝ g q‖ ≤ K * ‖q' - q‖ := fun x hx => by
      have hxB := hSB hx
      refine (hlip x q (by simpa [hB] using hxB) hq).trans
        (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
      have e : a • q + b • q' - q = b • (q' - q) := by
        rw [show a = 1 - b by linarith]; simp only [sub_smul, one_smul, smul_sub]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    have := (convex_segment q q').norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hdiff x (hSB hx)).mono hSB) hbd (left_mem_segment ℝ q q')
      (right_mem_segment ℝ q q')
    have e : g q' - fderiv ℝ g q q' - (g q - fderiv ℝ g q q) =
        g q' - g q - fderiv ℝ g q (q' - q) := by rw [map_sub]; abel
    rw [e] at this
    calc _ ≤ K * ‖q' - q‖ * ‖q' - q‖ := this
      _ = K * ‖q' - q‖ ^ 2 := by ring
      _ ≤ L * ‖q' - q‖ ^ 2 := mul_le_mul_of_nonneg_right hKL (by positivity)

/-- Woodford (2003), App. A.3 (**the contraction principle on bounded node functions**): a map of
the `r`-ball (sup norm over nodes) into itself that halves distances has a unique fixed point in
the ball. -/
theorem fixed_point_ball {Y : Type*} (Tm : (Y → Fin 9 → ℝ) → (Y → Fin 9 → ℝ)) {r : ℝ}
    (hr : 0 ≤ r) (hmap : ∀ z : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ y, ‖Tm z y‖ ≤ r)
    (hcontr : ∀ z z' : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → (∀ y, ‖z' y‖ ≤ r) → ∀ D,
      (∀ y, ‖z y - z' y‖ ≤ D) → ∀ y, ‖Tm z y - Tm z' y‖ ≤ D / 2) :
    ∃ z : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) ∧ Tm z = z ∧
      ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) → Tm z' = z' → z' = z := by
  set zs : ℕ → Y → Fin 9 → ℝ := fun n => Tm^[n] (fun _ => 0) with hzs
  have hzsB : ∀ n x, ‖zs n x‖ ≤ r := by
    intro n
    induction n with
    | zero => intro x; simp [hzs, hr]
    | succ n ih =>
      intro x
      simp only [hzs, Function.iterate_succ_apply']
      exact hmap _ ih x
  have hstep : ∀ n x, ‖zs n x - zs (n + 1) x‖ ≤ 2 * r / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [pow_zero, div_one]
      have := (norm_sub_le (zs 0 x) (zs 1 x)).trans (add_le_add (hzsB 0 x) (hzsB 1 x))
      linarith
    | succ n ih =>
      intro x
      have h := hcontr (zs (n + 1)) (zs n) (hzsB _) (hzsB _) (2 * r / 2 ^ n)
        (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (n + 1 + 1) = Tm (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = Tm (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) x = Tm (zs n) x from congrFun e2 x]
      calc _ ≤ 2 * r / 2 ^ n / 2 := h
        _ = 2 * r / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun n => zs n x := fun x =>
    cauchySeq_of_le_geometric_two (C := 2 * 2 * r) fun n => by
      rw [dist_eq_norm]
      refine (hstep n x).trans (le_of_eq ?_)
      field_simp
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x => le_of_tendsto' ((hz x).norm) fun n => hzsB n x
  have hzdist : ∀ n x, ‖zs n x - z x‖ ≤ 2 * 2 * r / 2 ^ n := fun n x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := 2 * 2 * r) (f := fun n => zs n x)
      (fun n => by
        rw [dist_eq_norm]; refine (hstep n x).trans (le_of_eq ?_); field_simp) (hz x) n
    rw [dist_eq_norm] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  have hgeo : ∀ c : ℝ, Tendsto (fun n : ℕ => c / 2 ^ n) atTop (𝓝 0) := fun c => by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul c
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow]; field_simp
  have hfix : Tm z = z := by
    funext x
    have hlim : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (Tm z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 := (hgeo (2 * 2 * r)).div_const 2
      rw [zero_div] at h0
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
      have e : zs (n + 1) = Tm (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hcontr z (zs n) hzB (hzsB n) _ (fun x => by rw [norm_sub_rev]; exact hzdist n x) x
    exact tendsto_nhds_unique hlim ((hz x).comp (tendsto_add_atTop_nat 1))
  refine ⟨z, hzB, hfix, fun z' hz'B hz' => ?_⟩
  have hD : ∀ n : ℕ, ∀ x, ‖z' x - z x‖ ≤ 2 * r / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      have := (norm_sub_le (z' x) (z x)).trans (add_le_add (hz'B x) (hzB x))
      simp only [pow_zero, div_one]; linarith
    | succ n ih =>
      intro x
      have h := hcontr z' z hz'B hzB _ ih x
      rw [hfix, hz'] at h
      exact h.trans (le_of_eq (by rw [pow_succ]; ring))
  funext x
  have := ge_of_tendsto' (hgeo (2 * r)) fun n => hD n x
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-! ## The partial derivatives of the exact conditions at a general point -/

variable {Y : Type*} (T : LagTree Y)

/-- Woodford (2003), App. A.3: the argument `(εê(x), lag z(x), z(x))` of the current part at node
`x`, with initial lag `ε²dh` at the roots. -/
noncomputable def qpt (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (ε : ℝ) (z : Y → Fin 9 → ℝ)
    (x : Y) : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) :=
  (ε • ê x, lagI T z (fun y => ε ^ 2 • dh y) x, z x)

/-- Woodford (2003), App. A.3 (**the derivative of the exact conditions in the unknowns at a
general point**) `(ε, z)`, applied to `v`. -/
noncomputable def Lin (p : Par) (R : RPar) (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (ε : ℝ)
    (z v : Y → Fin 9 → ℝ) (x : Y) : Fin 9 → ℝ :=
  fderiv ℝ (Qd p R) (qpt T ê dh ε z x) (0, lagv T v x, v x) +
    Mv T.M (fun y => fderiv ℝ (Nd p R) (z y) (v y)) x

/-- Woodford (2003), App. A.3 (**the derivative of the exact conditions in the amplitude**) at
`(ε, z)`. -/
noncomputable def Peps (p : Par) (R : RPar) (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (ε : ℝ)
    (z : Y → Fin 9 → ℝ) (x : Y) : Fin 9 → ℝ :=
  fderiv ℝ (Qd p R) (qpt T ê dh ε z x) (ê x, (2 * ε) • (if T.depth x = 0 then dh x else 0), 0)

/-- The exact conditions in terms of `qpt`. -/
theorem phiR_eq (p : Par) (R : RPar) (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (ε : ℝ)
    (z : Y → Fin 9 → ℝ) (x : Y) :
    PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) z x =
      Qd p R (qpt T ê dh ε z x) + Mv T.M (fun y => Nd p R (z y)) x := rfl

/-- The lag of a difference. -/
theorem lagv_sub (v v' : Y → Fin 9 → ℝ) (x : Y) :
    lagv T (fun y => v y - v' y) x = lagv T v x - lagv T v' x := by
  funext i; simp only [lagv, lag0, Pi.sub_apply]; split_ifs <;> simp

/-- The lag of a multiple. -/
theorem lagv_smul (c : ℝ) (v : Y → Fin 9 → ℝ) (x : Y) :
    lagv T (fun y => c • v y) x = c • lagv T v x := by
  funext i; simp only [lagv, lag0, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

/-- Woodford (2003), App. A.3: `Lin` is additive. -/
theorem lin_sub (p : Par) (R : RPar) (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (ε : ℝ)
    (z v v' : Y → Fin 9 → ℝ) (x : Y) :
    Lin T p R ê dh ε z (fun y => v y - v' y) x =
      Lin T p R ê dh ε z v x - Lin T p R ê dh ε z v' x := by
  simp only [Lin, lagv_sub]
  have e1 : ((0 : Fin 5 → ℝ), lagv T v x - lagv T v' x, v x - v' x) =
      ((0 : Fin 5 → ℝ), lagv T v x, v x) - (0, lagv T v' x, v' x) := by simp
  have e2 : (fun y => fderiv ℝ (Nd p R) (z y) (v y - v' y)) =
      fun y => fderiv ℝ (Nd p R) (z y) (v y) - fderiv ℝ (Nd p R) (z y) (v' y) := by
    funext y; rw [map_sub]
  rw [e1, map_sub, e2, NonlinearNKMarkovLinks.Mv_sub]
  abel_nf

/-- Woodford (2003), App. A.3: `Lin` is homogeneous. -/
theorem lin_smul (p : Par) (R : RPar) (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (ε c : ℝ)
    (z v : Y → Fin 9 → ℝ) (x : Y) :
    Lin T p R ê dh ε z (fun y => c • v y) x = c • Lin T p R ê dh ε z v x := by
  simp only [Lin, lagv_smul]
  have e1 : ((0 : Fin 5 → ℝ), c • lagv T v x, c • v x) =
      c • ((0 : Fin 5 → ℝ), lagv T v x, v x) := by
    simp
  have e2 : (fun y => fderiv ℝ (Nd p R) (z y) (c • v y)) =
      fun y => c • fderiv ℝ (Nd p R) (z y) (v y) := by
    funext y; rw [map_smul]
  rw [e1, map_smul, e2, Mv_smul, smul_add]

/-- Woodford (2003), App. A.3 (**`Lin = L + Δ`**): the derivative at a general point is the
linearisation at the steady state `LR` plus the change of the derivatives. -/
theorem lin_split {p : Par} (R : RPar) (hp : p.Std) (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ)
    (ε : ℝ) (z v : Y → Fin 9 → ℝ) (x : Y) :
    Lin T p R ê dh ε z v x = LR T p R v x +
      ((fderiv ℝ (Qd p R) (qpt T ê dh ε z x) - fderiv ℝ (Qd p R) 0) (0, lagv T v x, v x) +
        Mv T.M (fun y => (fderiv ℝ (Nd p R) (z y) - fderiv ℝ (Nd p R) 0) (v y)) x) := by
  have hN : (fun y => (fderiv ℝ (Nd p R) (z y) - fderiv ℝ (Nd p R) 0) (v y)) =
      fun y => fderiv ℝ (Nd p R) (z y) (v y) - DNr p R (v y) := by
    funext y; rw [sub_apply, fderiv_Nd]
  rw [hN, NonlinearNKMarkovLinks.Mv_sub, sub_apply, fderiv_Qd R hp]
  simp only [Lin, LR]
  rw [← Mv_DNr]
  abel_nf

/-- Woodford (2003), App. A.3: a bounded node function that is `≤ 1/4` of its own bound at every
iteration is zero. -/
theorem zero_of_quarter {v : Y → Fin 9 → ℝ} {B : ℝ} (hB : ∀ y, ‖v y‖ ≤ B)
    (h : ∀ D, (∀ y, ‖v y‖ ≤ D) → ∀ y, ‖v y‖ ≤ D / 4) : v = 0 := by
  have hn : ∀ n : ℕ, ∀ y, ‖v y‖ ≤ B / 4 ^ n := by
    intro n
    induction n with
    | zero => simpa using hB
    | succ n ih => intro y; rw [pow_succ, ← div_div]; exact h _ ih y
  funext y
  have ht : Tendsto (fun n : ℕ => B / 4 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).const_mul B
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow]; field_simp
  have := ge_of_tendsto' ht fun n => hn n y
  simpa using norm_le_zero_iff.1 this

/-- **Woodford (2003), App. A.3 (the derivative at a general point near the steady state is
invertible, uniformly over event trees).** If `A_uG ≠ 0` there are `η > 0` and `K₁ ≥ 0` such
that on every event tree, at every `(ε, z)` with `‖qpt‖, ‖z‖ ≤ η`, for every forcing with
`‖r‖ ≤ A` the equation `Lin(ε, z)v = r` has a solution with `‖v‖ ≤ K₁A`, and it is the only
bounded solution. -/
theorem lin_solve {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ η > 0, ∃ K₁, 0 ≤ K₁ ∧ ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ)
      (dh : Y → Fin 9 → ℝ) (ε : ℝ) (z : Y → Fin 9 → ℝ), (∀ x, ‖qpt T ê dh ε z x‖ ≤ η) →
        (∀ y, ‖z y‖ ≤ η) → ∀ (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y, ‖r y‖ ≤ A) →
          ∃ v : Y → Fin 9 → ℝ, (∀ y, ‖v y‖ ≤ K₁ * A) ∧ (∀ x, Lin T p R ê dh ε z v x = r x) ∧
            ∀ v' : Y → Fin 9 → ℝ, (∃ B, ∀ y, ‖v' y‖ ≤ B) →
              (∀ x, Lin T p R ê dh ε z v' x = r x) → v' = v := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound R hp
  set K' := K + 1 with hK'
  have hK'0 : 0 < K' := by linarith
  obtain ⟨ρQ, hρQ, LQ, hLQ, hQ⟩ := taylor_gen (contDiff_Qd (n := 2) p R)
  obtain ⟨ρN, hρN, LN, hLN, hN⟩ := taylor_gen (contDiff_Nd (n := 2) p R)
  set η := min (min ρQ ρN) (1 / (4 * K' * (LQ + LN + 1))) with hη
  have hη0 : 0 < η := by positivity
  have hηQ : η ≤ ρQ := (min_le_left _ _).trans (min_le_left _ _)
  have hηN : η ≤ ρN := (min_le_left _ _).trans (min_le_right _ _)
  have hηK : (LQ + LN) * η ≤ 1 / (4 * K') := by
    have h1 : η ≤ 1 / (4 * K' * (LQ + LN + 1)) := min_le_right _ _
    have h2 : (LQ + LN) * η ≤ (LQ + LN + 1) * (1 / (4 * K' * (LQ + LN + 1))) :=
      mul_le_mul (by linarith) h1 hη0.le (by positivity)
    refine h2.trans (le_of_eq ?_)
    field_simp
  refine ⟨η, hη0, 2 * K', by positivity, fun {Y} T ê dh ε z hq hz r A hA hr => ?_⟩
  have hKK : ∀ (s : Y → Fin 9 → ℝ) (B : ℝ), 0 ≤ B → (∀ y, ‖s y‖ ≤ B) →
      ∀ y, ‖LinvR T p R s y‖ ≤ K' * B := fun s B hB hs y =>
    (hK T s B hB hs y).trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : (Y → Fin 9 → ℝ) → Y → Fin 9 → ℝ, Δ = fun v x =>
      (fderiv ℝ (Qd p R) (qpt T ê dh ε z x) - fderiv ℝ (Qd p R) 0) (0, lagv T v x, v x) +
        Mv T.M (fun y => (fderiv ℝ (Nd p R) (z y) - fderiv ℝ (Nd p R) 0) (v y)) x := ⟨_, rfl⟩
  have hLin : ∀ v x, Lin T p R ê dh ε z v x = LR T p R v x + Δ v x := fun v x => by
    rw [hΔ]; exact lin_split T R hp ê dh ε z v x
  have hΔb : ∀ (v : Y → Fin 9 → ℝ) (B : ℝ), 0 ≤ B → (∀ y, ‖v y‖ ≤ B) →
      ∀ x, ‖Δ v x‖ ≤ (LQ + LN) * η * B := by
    intro v B hB hv x
    rw [hΔ]
    have h1 : ‖fderiv ℝ (Qd p R) (qpt T ê dh ε z x) - fderiv ℝ (Qd p R) 0‖ ≤ LQ * η := by
      have := (hQ 0 (qpt T ê dh ε z x) (by simp [hρQ.le]) ((hq x).trans hηQ)).2.1
      rw [sub_zero] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hq x) hLQ)
    have h2 : ‖((0 : Fin 5 → ℝ), lagv T v x, v x)‖ ≤ B := by
      rw [Prod.norm_def, Prod.norm_def, norm_zero]
      exact max_le hB (max_le (norm_lagv_le T hB hv x) (hv x))
    have h3 : ∀ y, ‖(fderiv ℝ (Nd p R) (z y) - fderiv ℝ (Nd p R) 0) (v y)‖ ≤ LN * η * B :=
      fun y => by
        have := (hN 0 (z y) (by simp [hρN.le]) ((hz y).trans hηN)).2.1
        rw [sub_zero] at this
        refine ((ContinuousLinearMap.le_opNorm _ _)).trans ?_
        exact mul_le_mul (this.trans (mul_le_mul_of_nonneg_left (hz y) hLN)) (hv y)
          (norm_nonneg _) (by positivity)
    have h4 := Mv_norm_le T.markov (by positivity) h3 x
    calc _ ≤ ‖(fderiv ℝ (Qd p R) (qpt T ê dh ε z x) - fderiv ℝ (Qd p R) 0)
          ((0 : Fin 5 → ℝ), lagv T v x, v x)‖ +
          ‖Mv T.M (fun y => (fderiv ℝ (Nd p R) (z y) - fderiv ℝ (Nd p R) 0) (v y)) x‖ :=
          norm_add_le _ _
      _ ≤ LQ * η * B + LN * η * B := add_le_add
          ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul h1 h2 (norm_nonneg _)
            (by positivity))) h4
      _ = (LQ + LN) * η * B := by ring
  have hΔsub : ∀ v v' x, Δ (fun y => v y - v' y) x = Δ v x - Δ v' x := by
    intro v v' x
    have h1 := hLin (fun y => v y - v' y) x
    rw [lin_sub, hLin v x, hLin v' x, LR_sub] at h1
    have h2 : Δ (fun y => v y - v' y) x = LR T p R v x + Δ v x - (LR T p R v' x + Δ v' x) -
        (LR T p R v x - LR T p R v' x) := by rw [h1]; abel
    rw [h2]; abel
  -- the Neumann map
  set S : (Y → Fin 9 → ℝ) → Y → Fin 9 → ℝ := fun v => LinvR T p R (fun x => r x - Δ v x)
    with hS
  have hsmall : (LQ + LN) * η * (2 * K' * A) ≤ A / 2 := by
    have := mul_le_mul_of_nonneg_right hηK (show 0 ≤ 2 * K' * A by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  obtain ⟨v, hvB, hvfix, -⟩ := fixed_point_ball S (r := 2 * K' * A) (by positivity)
    (fun v hv y => by
      have hb : ∀ x, ‖r x - Δ v x‖ ≤ A + A / 2 := fun x =>
        (norm_sub_le _ _).trans (add_le_add (hr x)
          ((hΔb v _ (by positivity) hv x).trans hsmall))
      refine (hKK _ _ (by positivity) hb y).trans (le_of_eq_of_le rfl ?_)
      nlinarith)
    (fun v v' hv hv' D hD y => by
      have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD y)
      have hb1 : ∀ x, ‖r x - Δ v x‖ ≤ A + A / 2 := fun x =>
        (norm_sub_le _ _).trans (add_le_add (hr x)
          ((hΔb v _ (by positivity) hv x).trans hsmall))
      have hb2 : ∀ x, ‖r x - Δ v' x‖ ≤ A + A / 2 := fun x =>
        (norm_sub_le _ _).trans (add_le_add (hr x)
          ((hΔb v' _ (by positivity) hv' x).trans hsmall))
      have e := LinvR_sub T R hp hG (by positivity) (by positivity) hb1 hb2
      have e' : S v y - S v' y = LinvR T p R (fun x => (r x - Δ v x) - (r x - Δ v' x)) y := by
        rw [e]
      rw [e']
      have hb3 : ∀ x, ‖(r x - Δ v x) - (r x - Δ v' x)‖ ≤ (LQ + LN) * η * D := fun x => by
        rw [sub_sub_sub_cancel_left, norm_sub_rev, ← hΔsub v v' x]
        exact hΔb _ D hD0 hD x
      refine (hKK _ _ (by positivity) hb3 y).trans ?_
      have : K' * ((LQ + LN) * η * D) ≤ K' * (1 / (4 * K') * D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηK hD0) hK'0.le
      have e2 : K' * (1 / (4 * K') * D) = D / 4 := by field_simp
      linarith)
  -- the fixed point solves the equation
  have hsolve : ∀ x, Lin T p R ê dh ε z v x = r x := by
    have hb : ∀ x k, |(fun x => r x - Δ v x) x k| ≤ A + A / 2 := fun x k => by
      have := (norm_le_pi_norm (r x - Δ v x) k).trans ((norm_sub_le _ _).trans (add_le_add (hr x)
        ((hΔb v _ (by positivity) hvB x).trans hsmall)))
      rwa [Real.norm_eq_abs] at this
    have hLR := LR_LinvR T R hp hG (fun x => r x - Δ v x) (A + A / 2) (by positivity) hb
    have hv : LinvR T p R (fun x => r x - Δ v x) = v := hvfix
    rw [hv] at hLR
    intro x
    rw [hLin, congrFun hLR x]
    abel
  refine ⟨v, hvB, hsolve, fun v' ⟨B, hB⟩ hv' => ?_⟩
  -- uniqueness among bounded solutions
  have hB0 : ∀ y, ‖v' y - v y‖ ≤ B + 2 * K' * A := fun y =>
    (norm_sub_le _ _).trans (add_le_add (hB y) (hvB y))
  have hw : ∀ x, LR T p R (fun y => v' y - v y) x = -Δ (fun y => v' y - v y) x := fun x => by
    have h1 := lin_sub T p R ê dh ε z v' v x
    rw [hv' x, hsolve x, sub_self, hLin] at h1
    rw [← sub_eq_zero, sub_neg_eq_add, h1.symm]
  have hz0 := zero_of_quarter (v := fun y => v' y - v y) hB0 (fun D hD y => by
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD y)
    have hLL := LinvR_LR T R hp hG (v := fun y => v' y - v y) (B := D) hD0 hD
    have e : (fun y => v' y - v y) = LinvR T p R (fun x => -Δ (fun y => v' y - v y) x) :=
      calc (fun y => v' y - v y) = LinvR T p R (LR T p R (fun y => v' y - v y)) := hLL.symm
        _ = _ := by congr 1; funext x; exact hw x
    have hb : ∀ x, ‖-Δ (fun y => v' y - v y) x‖ ≤ (LQ + LN) * η * D := fun x => by
      rw [norm_neg]; exact hΔb _ D hD0 hD x
    rw [congrFun e y]
    refine (hKK _ _ (by positivity) hb y).trans ?_
    have : K' * ((LQ + LN) * η * D) ≤ K' * (1 / (4 * K') * D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηK hD0) hK'0.le
    refine this.trans (le_of_eq ?_)
    field_simp)
  funext y
  have := congrFun hz0 y
  simpa [sub_eq_zero] using this

/-- Woodford (2003), App. A.3: the change of the argument of the current part between `(ε, z)` and
`(ε′, z′)`. -/
theorem qpt_sub (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (ε ε' : ℝ) (z z' : Y → Fin 9 → ℝ)
    (x : Y) : qpt T ê dh ε' z' x - qpt T ê dh ε z x =
      ((0 : Fin 5 → ℝ), lagv T (fun y => z' y - z y) x, z' x - z x) +
        ((ε' - ε) • (ê x, (2 * ε) • (if T.depth x = 0 then dh x else 0), (0 : Fin 9 → ℝ)) +
          ((0 : Fin 5 → ℝ), (ε' - ε) ^ 2 • (if T.depth x = 0 then dh x else 0),
            (0 : Fin 9 → ℝ))) := by
  ext i
  · simp [qpt]; ring
  · simp only [qpt, lagI, lagv, lag0, Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.fst_sub,
      Prod.fst_add, Prod.smul_fst, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp; ring
  · simp [qpt]

/-- **Woodford (2003), App. A.3 (the exact conditions are differentiable with a quadratic
remainder).** There are `ρ > 0` and `C₂ ≥ 0` such that on every event tree, for `‖ê‖, ‖d̂‖ ≤ 1`,
`|ε|, |ε′| ≤ 1` and arguments in the `ρ`-ball, with `‖z′ − z‖ ≤ D`,
`‖Φ(ε′, z′) − Φ(ε, z) − Lin(ε, z)(z′ − z) − (ε′ − ε)Peps(ε, z)‖ ≤ C₂(|ε′ − ε| + D)²`. -/
theorem phi_expand (p : Par) (R : RPar) :
    ∃ ρ > 0, ∃ C₂, 0 ≤ C₂ ∧ ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ)
      (dh : Y → Fin 9 → ℝ), (∀ y, ‖ê y‖ ≤ 1) → (∀ y, ‖dh y‖ ≤ 1) → ∀ (ε ε' : ℝ)
        (z z' : Y → Fin 9 → ℝ) (D : ℝ), |ε| ≤ 1 → |ε'| ≤ 1 →
          (∀ x, ‖qpt T ê dh ε z x‖ ≤ ρ) → (∀ x, ‖qpt T ê dh ε' z' x‖ ≤ ρ) →
          (∀ y, ‖z y‖ ≤ ρ) → (∀ y, ‖z' y‖ ≤ ρ) → (∀ y, ‖z' y - z y‖ ≤ D) → ∀ x,
            ‖PhiR T p R (fun y => ε' • ê y) (fun y => ε' ^ 2 • dh y) z' x -
              PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) z x -
              Lin T p R ê dh ε z (fun y => z' y - z y) x -
              (ε' - ε) • Peps T p R ê dh ε z x‖ ≤ C₂ * (|ε' - ε| + D) ^ 2 := by
  obtain ⟨ρQ, hρQ, LQ, hLQ, hQ⟩ := taylor_gen (contDiff_Qd (n := 2) p R)
  obtain ⟨ρN, hρN, LN, hLN, hN⟩ := taylor_gen (contDiff_Nd (n := 2) p R)
  refine ⟨min ρQ ρN, lt_min hρQ hρN, 17 * LQ + LN, by positivity,
    fun {Y} T ê dh hê hd ε ε' z z' D hε hε' hq hq' hz hz' hD x => ?_⟩
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
  set dr : Fin 9 → ℝ := if T.depth x = 0 then dh x else 0 with hdr
  have hdr1 : ‖dr‖ ≤ 1 := by rw [hdr]; split_ifs; exacts [hd x, by simp]
  set q := qpt T ê dh ε z x with hqd
  set q' := qpt T ê dh ε' z' x with hq'd
  set a : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) :=
    (0, lagv T (fun y => z' y - z y) x, z' x - z x) with ha
  set b : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) := (ê x, (2 * ε) • dr, 0) with hb
  set c : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) := (0, (ε' - ε) ^ 2 • dr, 0) with hc
  have hsub : q' - q = a + ((ε' - ε) • b + c) := qpt_sub T ê dh ε ε' z z' x
  set RN : Y → Fin 9 → ℝ := fun y => Nd p R (z' y) - Nd p R (z y) -
    fderiv ℝ (Nd p R) (z y) (z' y - z y) with hRN
  have key : PhiR T p R (fun y => ε' • ê y) (fun y => ε' ^ 2 • dh y) z' x -
      PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) z x -
      Lin T p R ê dh ε z (fun y => z' y - z y) x - (ε' - ε) • Peps T p R ê dh ε z x =
      (Qd p R q' - Qd p R q - fderiv ℝ (Qd p R) q (q' - q)) + fderiv ℝ (Qd p R) q c +
        Mv T.M RN x := by
    have hM : Mv T.M (fun y => Nd p R (z' y)) x - Mv T.M (fun y => Nd p R (z y)) x -
        Mv T.M (fun y => fderiv ℝ (Nd p R) (z y) (z' y - z y)) x = Mv T.M RN x := by
      rw [← congrFun (NonlinearNKMarkovLinks.Mv_sub T.M _ _) x,
        ← congrFun (NonlinearNKMarkovLinks.Mv_sub T.M _ _) x]
    rw [phiR_eq, phiR_eq, ← hM, hsub, map_add, map_add, map_smul]
    simp only [Lin, Peps, ← hqd, ← hdr]
    abel
  rw [key]
  have hqb : ‖q‖ ≤ ρQ := (hq x).trans (min_le_left _ _)
  have hq'b : ‖q'‖ ≤ ρQ := (hq' x).trans (min_le_left _ _)
  have hab : ‖a‖ ≤ D := by
    rw [ha, Prod.norm_def, Prod.norm_def, norm_zero]
    exact max_le hD0 (max_le (norm_lagv_le T hD0 (fun y => hD y) x) (hD x))
  have hbn : ‖b‖ ≤ 2 := by
    rw [hb, Prod.norm_def, Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs]
    have : |2 * ε| ≤ 2 := by rw [abs_mul]; norm_num; exact hε
    refine max_le ((hê x).trans (by norm_num)) (max_le ?_ (by norm_num))
    calc |2 * ε| * ‖dr‖ ≤ 2 * 1 := mul_le_mul this hdr1 (norm_nonneg _) (by norm_num)
      _ = 2 := by ring
  have hcn : ‖c‖ ≤ (ε' - ε) ^ 2 := by
    rw [hc, Prod.norm_def, Prod.norm_def, norm_zero, norm_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    refine max_le (by positivity) (max_le ?_ (by positivity))
    exact mul_le_of_le_one_right (sq_nonneg _) hdr1
  have hΔε : |ε' - ε| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hsq : (ε' - ε) ^ 2 ≤ 2 * |ε' - ε| := by
    rw [← sq_abs]; nlinarith [abs_nonneg (ε' - ε)]
  have hΔq : ‖q' - q‖ ≤ 4 * (|ε' - ε| + D) := by
    rw [hsub]
    calc _ ≤ ‖a‖ + (‖(ε' - ε) • b‖ + ‖c‖) := (norm_add_le _ _).trans
          (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ D + (|ε' - ε| * 2 + 2 * |ε' - ε|) := by
          refine add_le_add hab (add_le_add ?_ (hcn.trans hsq))
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hbn (abs_nonneg _)
      _ ≤ _ := by nlinarith [abs_nonneg (ε' - ε)]
  have b1 := (hQ q q' hqb hq'b).2.2
  have b2 : ‖fderiv ℝ (Qd p R) q c‖ ≤ LQ * (|ε' - ε| + D) ^ 2 := by
    refine ((ContinuousLinearMap.le_opNorm _ _)).trans ?_
    refine mul_le_mul (hQ q q hqb hqb).1 (hcn.trans ?_) (norm_nonneg _) hLQ
    rw [← sq_abs]; nlinarith [abs_nonneg (ε' - ε)]
  have b3 : ∀ y, ‖RN y‖ ≤ LN * (|ε' - ε| + D) ^ 2 := fun y => by
    have h := (hN (z y) (z' y) ((hz y).trans (min_le_right _ _))
      ((hz' y).trans (min_le_right _ _))).2.2
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hLN)
    have := pow_le_pow_left₀ (norm_nonneg _) (hD y) 2
    nlinarith [abs_nonneg (ε' - ε)]
  have b3' := Mv_norm_le T.markov (by positivity) b3 x
  calc _ ≤ ‖Qd p R q' - Qd p R q - fderiv ℝ (Qd p R) q (q' - q)‖ +
        ‖fderiv ℝ (Qd p R) q c‖ + ‖Mv T.M RN x‖ := norm_add₃_le
    _ ≤ LQ * (4 * (|ε' - ε| + D)) ^ 2 + LQ * (|ε' - ε| + D) ^ 2 +
        LN * (|ε' - ε| + D) ^ 2 := by
        refine add_le_add (add_le_add (b1.trans (mul_le_mul_of_nonneg_left ?_ hLQ)) b2) b3'
        exact pow_le_pow_left₀ (norm_nonneg _) hΔq 2
    _ = _ := by ring

/-- Woodford (2003), App. A.3: `‖qpt(ε′, z′) − qpt(ε, z)‖ ≤ 4(|ε′ − ε| + D)` for `|ε|, |ε′| ≤ 1`,
`‖ê‖, ‖d̂‖ ≤ 1`, `‖z′ − z‖ ≤ D`. -/
theorem norm_qpt_sub (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (hê : ∀ y, ‖ê y‖ ≤ 1)
    (hd : ∀ y, ‖dh y‖ ≤ 1) {ε ε' : ℝ} (hε : |ε| ≤ 1) (hε' : |ε'| ≤ 1) {z z' : Y → Fin 9 → ℝ}
    {D : ℝ} (hD : ∀ y, ‖z' y - z y‖ ≤ D) (x : Y) :
    ‖qpt T ê dh ε' z' x - qpt T ê dh ε z x‖ ≤ 4 * (|ε' - ε| + D) := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
  set dr : Fin 9 → ℝ := if T.depth x = 0 then dh x else 0 with hdr
  have hdr1 : ‖dr‖ ≤ 1 := by rw [hdr]; split_ifs; exacts [hd x, by simp]
  rw [qpt_sub, ← hdr]
  have hab : ‖((0 : Fin 5 → ℝ), lagv T (fun y => z' y - z y) x, z' x - z x)‖ ≤ D := by
    rw [Prod.norm_def, Prod.norm_def, norm_zero]
    exact max_le hD0 (max_le (norm_lagv_le T hD0 (fun y => hD y) x) (hD x))
  have hbn : ‖(ê x, (2 * ε) • dr, (0 : Fin 9 → ℝ))‖ ≤ 2 := by
    rw [Prod.norm_def, Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs]
    have : |2 * ε| ≤ 2 := by rw [abs_mul]; norm_num; exact hε
    refine max_le ((hê x).trans (by norm_num)) (max_le ?_ (by norm_num))
    calc |2 * ε| * ‖dr‖ ≤ 2 * 1 := mul_le_mul this hdr1 (norm_nonneg _) (by norm_num)
      _ = 2 := by ring
  have hcn : ‖((0 : Fin 5 → ℝ), (ε' - ε) ^ 2 • dr, (0 : Fin 9 → ℝ))‖ ≤ (ε' - ε) ^ 2 := by
    rw [Prod.norm_def, Prod.norm_def, norm_zero, norm_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    refine max_le (by positivity) (max_le ?_ (by positivity))
    exact mul_le_of_le_one_right (sq_nonneg _) hdr1
  have hsq : (ε' - ε) ^ 2 ≤ 2 * |ε' - ε| := by
    have hΔε : |ε' - ε| ≤ 2 := (abs_sub _ _).trans (by linarith)
    rw [← sq_abs]; nlinarith [abs_nonneg (ε' - ε)]
  have hsm : ‖(ε' - ε) • (ê x, (2 * ε) • dr, (0 : Fin 9 → ℝ))‖ ≤ |ε' - ε| * 2 := by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hbn (abs_nonneg _)
  have h2 := (norm_add_le _ _).trans (add_le_add hsm (hcn.trans hsq))
  have h1 := (norm_add_le _ _).trans (add_le_add hab h2)
  refine h1.trans ?_
  nlinarith [abs_nonneg (ε' - ε)]

/-- Woodford (2003), App. A.3: at `ε = 0`, `z = 0` the argument of the current part is `0`. -/
theorem qpt_zero (ê : Y → Fin 5 → ℝ) (dh : Y → Fin 9 → ℝ) (x : Y) :
    qpt T ê dh 0 (fun _ => 0) x = 0 := by
  simp only [qpt, lagI, zero_smul]
  split_ifs <;> simp [sq]

/-- Woodford (2003), App. A.3: at `(0, 0)` the partial derivatives are the linearisation at the
steady state: `Lin(0, 0) = L` and `Peps(0, 0) = DQe(ê)`. -/
theorem lin_peps_zero {p : Par} (R : RPar) (hp : p.Std) (ê : Y → Fin 5 → ℝ)
    (dh : Y → Fin 9 → ℝ) (v : Y → Fin 9 → ℝ) (x : Y) :
    Lin T p R ê dh 0 (fun _ => 0) v x = LR T p R v x ∧
      Peps T p R ê dh 0 (fun _ => 0) x = DQs p R (ê x) := by
  constructor
  · simp only [Lin, qpt_zero, fderiv_Qd R hp, fderiv_Nd, LR]
    rw [Mv_DNr]
  · simp only [Peps, qpt_zero, mul_zero, zero_smul]
    rw [fderiv_Qd_full R hp]
    have h0 : DQr p R 0 0 = 0 := by funext i; fin_cases i <;> simp [DQr]
    rw [h0, add_zero]

/-- **Woodford (2003), Ch. 6, §1 and §5, Ch. 7, and App. A.3 (`C¹` — indeed `C^{1,1}` —
dependence of the exact Ramsey solution on the amplitude of the disturbances, uniformly over
event trees).** If `A_uG ≠ 0` there are `δ₁, r > 0` and `C ≥ 0` such that on every event tree,
for disturbance patterns `‖ê‖ ≤ 1` and initial-lag patterns `‖d̂‖ ≤ 1`, there are families
`Z, V : ℝ → (nodes → ℝ⁹)` with, for `|ε|, |ε₀| ≤ δ₁`:
* `Z(ε)` is the solution of the exact Ramsey conditions with disturbances `εê` and initial lag
  `ε²d̂` within `r` of the steady state, and the only one there;
* `V(ε)` is bounded and solves `Lin(ε, Z(ε))V = −Peps(ε, Z(ε))` (the implicit-function formula);
* `Z(0) = 0`, `V(0) = z₁ = L⁻¹(−DQe(ê))`;
* `‖Z(ε) − Z(ε₀) − (ε − ε₀)V(ε₀)‖ ≤ C(ε − ε₀)²` at every node (differentiability in the sup norm
  with derivative `V`);
* `‖V(ε) − V(ε₀)‖ ≤ C|ε − ε₀|` at every node (the derivative is Lipschitz, so continuous). -/
theorem ramsey_C1 {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ δ₁ > 0, ∃ r > 0, ∃ C, 0 ≤ C ∧ ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ)
      (dh : Y → Fin 9 → ℝ), (∀ y, ‖ê y‖ ≤ 1) → (∀ y, ‖dh y‖ ≤ 1) →
        ∃ Z V : ℝ → Y → Fin 9 → ℝ,
          (∀ ε, |ε| ≤ δ₁ →
            (PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) (Z ε) = 0 ∧
              (∀ y, ‖Z ε y‖ ≤ r) ∧ ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
                PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) z' = 0 → z' = Z ε) ∧
            (∀ y, ‖V ε y‖ ≤ C) ∧
            ∀ x, Lin T p R ê dh ε (Z ε) (V ε) x = -Peps T p R ê dh ε (Z ε) x) ∧
          Z 0 = 0 ∧ V 0 = LinvR T p R (fun y => -DQs p R (ê y)) ∧
          (∀ ε ε₀, |ε| ≤ δ₁ → |ε₀| ≤ δ₁ → ∀ y,
            ‖Z ε y - Z ε₀ y - (ε - ε₀) • V ε₀ y‖ ≤ C * (ε - ε₀) ^ 2) ∧
          ∀ ε ε₀, |ε| ≤ δ₁ → |ε₀| ≤ δ₁ → ∀ y, ‖V ε y - V ε₀ y‖ ≤ C * |ε - ε₀| := by
  obtain ⟨rN, hrN, δN, hδN, CN, hCN, hNew⟩ := ramsey_newton R hp hG
  obtain ⟨η, hη, K₁, hK₁, hLs⟩ := lin_solve R hp hG
  obtain ⟨ρE, hρE, C₂, hC₂, hExp⟩ := phi_expand p R
  obtain ⟨ρQ, hρQ, LQ, hLQ, hQ⟩ := taylor_gen (contDiff_Qd (n := 2) p R)
  obtain ⟨ρN, hρN, LN, hLN, hN⟩ := taylor_gen (contDiff_Nd (n := 2) p R)
  set ρs := min (min rN η) (min ρE (min ρQ ρN)) with hρs
  have hρs0 : 0 < ρs := by positivity
  have hρs1 : ρs ≤ rN := (min_le_left _ _).trans (min_le_left _ _)
  have hρs2 : ρs ≤ η := (min_le_left _ _).trans (min_le_right _ _)
  have hρs3 : ρs ≤ ρE := (min_le_right _ _).trans (min_le_left _ _)
  have hρs4 : ρs ≤ ρQ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρs5 : ρs ≤ ρN := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set LipQ := LQ * (1 + 2 * ρQ) with hLipQ
  have hLipQ0 : 0 ≤ LipQ := by positivity
  have hQlip : ∀ q q', ‖q‖ ≤ ρQ → ‖q'‖ ≤ ρQ → ‖Qd p R q' - Qd p R q‖ ≤ LipQ * ‖q' - q‖ := by
    intro q q' hq hq'
    obtain ⟨h1, -, h3⟩ := hQ q q' hq hq'
    have hqq : ‖q' - q‖ ≤ 2 * ρQ := (norm_sub_le _ _).trans (by linarith)
    calc ‖Qd p R q' - Qd p R q‖ ≤ ‖Qd p R q' - Qd p R q - fderiv ℝ (Qd p R) q (q' - q)‖ +
          ‖fderiv ℝ (Qd p R) q (q' - q)‖ := by
          have := norm_add_le (Qd p R q' - Qd p R q - fderiv ℝ (Qd p R) q (q' - q))
            (fderiv ℝ (Qd p R) q (q' - q)); simpa using this
      _ ≤ LQ * ‖q' - q‖ ^ 2 + LQ * ‖q' - q‖ :=
          add_le_add h3 ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
      _ ≤ LipQ * ‖q' - q‖ := by
          rw [hLipQ]
          have := mul_le_mul_of_nonneg_left hqq (mul_nonneg hLQ (norm_nonneg (q' - q)))
          nlinarith [norm_nonneg (q' - q)]
  set CZ := CN * (LipQ * 4) with hCZ
  have hCZ0 : 0 ≤ CZ := by positivity
  set δ₁ := min (min 1 δN) (ρs / (4 * (1 + CZ))) with hδ₁
  have hδ₁0 : 0 < δ₁ := by positivity
  set CL := CN * (LipQ * 4) with hCL
  have hCL0 : 0 ≤ CL := by positivity
  set CV := K₁ * (2 * LQ) with hCV
  have hCV0 : 0 ≤ CV := by positivity
  set Cd := K₁ * (C₂ * (1 + CL) ^ 2) with hCd
  set C3 := K₁ * (LQ * 2 + LQ * (4 * (1 + CL)) * 2 + LQ * (4 * (1 + CL)) * CV + LN * CL * CV)
    with hC3
  refine ⟨δ₁, hδ₁0, rN, hrN, max (max CV Cd) C3, by positivity,
    fun {Y} T ê dh hê hd => ?_⟩
  -- the range of amplitudes
  have hr1 : ∀ ε, |ε| ≤ δ₁ → |ε| ≤ 1 := fun ε h => h.trans ((min_le_left _ _).trans
    (min_le_left _ _))
  have hr2 : ∀ ε, |ε| ≤ δ₁ → |ε| ≤ δN := fun ε h => h.trans ((min_le_left _ _).trans
    (min_le_right _ _))
  have hr3 : ∀ ε, |ε| ≤ δ₁ → 4 * (1 + CZ) * |ε| ≤ ρs := fun ε h => by
    have := h.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  have hsq : ∀ ε : ℝ, |ε| ≤ 1 → ε ^ 2 ≤ |ε| := fun ε h => by
    rw [← sq_abs]; nlinarith [abs_nonneg ε]
  have hdata : ∀ ε, |ε| ≤ δ₁ → (∀ y, ‖ε • ê y‖ ≤ δN) ∧ ∀ y, ‖ε ^ 2 • dh y‖ ≤ δN := by
    intro ε h
    refine ⟨fun y => ?_, fun y => ?_⟩
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hê y)).trans (hr2 ε h)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (mul_le_of_le_one_right (sq_nonneg _) (hd y)).trans ((hsq ε (hr1 ε h)).trans
        (hr2 ε h))
  have hex : ∀ ε, |ε| ≤ δ₁ → ∃ z : Y → Fin 9 → ℝ,
      ((∀ y, ‖z y‖ ≤ rN) ∧ PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) z = 0) ∧
      (∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ rN) →
        PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) z' = 0 → z' = z) ∧
      ∀ zt : Y → Fin 9 → ℝ, (∀ y, ‖zt y‖ ≤ rN) → ∀ τ', 0 ≤ τ' →
        (∀ y, ‖PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) zt y‖ ≤ τ') →
          ∀ y, ‖z y - zt y‖ ≤ CN * τ' := fun ε h =>
    hNew T _ _ (hdata ε h).1 (hdata ε h).2
  choose! Z hZ using hex
  -- the size of the solution
  have hZs : ∀ ε, |ε| ≤ δ₁ → ∀ y, ‖Z ε y‖ ≤ CZ * |ε| := by
    intro ε h y
    have hq0 : ∀ x, ‖qpt T ê dh ε (fun _ => 0) x‖ ≤ 4 * |ε| := fun x => by
      have := norm_qpt_sub T ê dh hê hd (ε := 0) (ε' := ε) (by simp) (hr1 ε h)
        (z := fun _ => 0) (z' := fun _ => 0) (D := 0) (fun _ => by simp) x
      simpa [qpt_zero] using this
    have hres : ∀ x, ‖PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) (fun _ => 0) x‖ ≤
        LipQ * 4 * |ε| := fun x => by
      rw [phiR_eq, Mv_const' T]
      have e5 : Qd p R 0 + Nd p R 0 = 0 := Qd_Nd_zero R hp
      have e : Qd p R (qpt T ê dh ε (fun _ => 0) x) + Nd p R 0 =
          Qd p R (qpt T ê dh ε (fun _ => 0) x) - Qd p R 0 := by
        rw [eq_neg_of_add_eq_zero_right e5]; abel
      rw [e]
      have hb : ‖qpt T ê dh ε (fun _ => 0) x‖ ≤ ρQ :=
        (hq0 x).trans (le_trans (by nlinarith [abs_nonneg ε]) ((hr3 ε h).trans hρs4))
      refine (hQlip 0 _ (by simp [hρQ.le]) hb).trans ?_
      rw [sub_zero]
      calc _ ≤ LipQ * (4 * |ε|) := mul_le_mul_of_nonneg_left (hq0 x) hLipQ0
        _ = _ := by ring
    have := (hZ ε h).2.2 (fun _ => 0) (fun _ => by simp [hrN.le]) _ (by positivity) hres y
    rw [sub_zero] at this
    calc _ ≤ CN * (LipQ * 4 * |ε|) := this
      _ = _ := by rw [hCZ]; ring
  have hZr : ∀ ε, |ε| ≤ δ₁ → ∀ y, ‖Z ε y‖ ≤ ρs := fun ε h y =>
    (hZs ε h y).trans (le_trans (by nlinarith [abs_nonneg ε]) (hr3 ε h))
  have hδr : 4 * (1 + CZ) * δ₁ ≤ ρs := by
    have := min_le_right (min 1 δN) (ρs / (4 * (1 + CZ)))
    rw [← hδ₁, le_div_iff₀ (by positivity), mul_comm] at this
    exact this
  have hqs2 : ∀ ε ε₀, |ε| ≤ δ₁ → |ε₀| ≤ δ₁ → ∀ x, ‖qpt T ê dh ε (Z ε₀) x‖ ≤ ρs := by
    intro ε ε₀ h h₀ x
    have := norm_qpt_sub T ê dh hê hd (ε := 0) (ε' := ε) (by simp) (hr1 ε h)
      (z := fun _ => 0) (z' := Z ε₀) (D := CZ * |ε₀|) (fun y => by simpa using hZs ε₀ h₀ y) x
    rw [qpt_zero, sub_zero, sub_zero] at this
    refine this.trans (le_trans ?_ hδr)
    have := mul_le_mul_of_nonneg_left h₀ hCZ0
    nlinarith [abs_nonneg ε]
  have hqs : ∀ ε, |ε| ≤ δ₁ → ∀ x, ‖qpt T ê dh ε (Z ε) x‖ ≤ ρs := fun ε h x =>
    hqs2 ε ε h h x
  -- the derivative in the amplitude is bounded
  have hPb : ∀ ε, |ε| ≤ δ₁ → ∀ x, ‖Peps T p R ê dh ε (Z ε) x‖ ≤ 2 * LQ := fun ε h x => by
    have hb : ‖(ê x, (2 * ε) • (if T.depth x = 0 then dh x else 0), (0 : Fin 9 → ℝ))‖ ≤ 2 := by
      rw [Prod.norm_def, Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs]
      have h2 : |2 * ε| ≤ 2 := by rw [abs_mul]; norm_num; exact hr1 ε h
      have h3 : ‖(if T.depth x = 0 then dh x else 0 : Fin 9 → ℝ)‖ ≤ 1 := by
        split_ifs; exacts [hd x, by simp]
      refine max_le ((hê x).trans (by norm_num)) (max_le ?_ (by norm_num))
      calc _ ≤ 2 * 1 := mul_le_mul h2 h3 (norm_nonneg _) (by norm_num)
        _ = 2 := by ring
    refine ((ContinuousLinearMap.le_opNorm _ _)).trans ?_
    calc _ ≤ LQ * 2 := mul_le_mul (hQ _ _ ((hqs ε h x).trans hρs4)
          ((hqs ε h x).trans hρs4)).1 hb (norm_nonneg _) hLQ
      _ = 2 * LQ := by ring
  -- the derivative `V`
  have hexV : ∀ ε, |ε| ≤ δ₁ → ∃ v : Y → Fin 9 → ℝ, (∀ y, ‖v y‖ ≤ K₁ * (2 * LQ)) ∧
      (∀ x, Lin T p R ê dh ε (Z ε) v x = -Peps T p R ê dh ε (Z ε) x) ∧
      ∀ v' : Y → Fin 9 → ℝ, (∃ B, ∀ y, ‖v' y‖ ≤ B) →
        (∀ x, Lin T p R ê dh ε (Z ε) v' x = -Peps T p R ê dh ε (Z ε) x) → v' = v :=
    fun ε h => hLs T ê dh ε (Z ε) (fun x => (hqs ε h x).trans hρs2)
      (fun y => (hZr ε h y).trans hρs2) (fun x => -Peps T p R ê dh ε (Z ε) x) (2 * LQ)
      (by positivity) (fun y => by rw [norm_neg]; exact hPb ε h y)
  choose! V hV using hexV
  -- uniqueness for the linear equation, as a bound
  have hLbound : ∀ ε, |ε| ≤ δ₁ → ∀ (w : Y → Fin 9 → ℝ) (B A : ℝ), (∀ y, ‖w y‖ ≤ B) → 0 ≤ A →
      (∀ x, ‖Lin T p R ê dh ε (Z ε) w x‖ ≤ A) → ∀ y, ‖w y‖ ≤ K₁ * A := by
    intro ε h w B A hB hA hLw
    obtain ⟨v, hvb, hvs, hvu⟩ := hLs T ê dh ε (Z ε) (fun x => (hqs ε h x).trans hρs2)
      (fun y => (hZr ε h y).trans hρs2) (Lin T p R ê dh ε (Z ε) w) A hA hLw
    have := hvu w ⟨B, hB⟩ (fun x => rfl)
    rw [this]
    exact hvb
  -- Lipschitz dependence of the solution
  have hZL : ∀ ε ε₀, |ε| ≤ δ₁ → |ε₀| ≤ δ₁ → ∀ y, ‖Z ε y - Z ε₀ y‖ ≤ CL * |ε - ε₀| := by
    intro ε ε₀ h h₀ y
    have hres : ∀ x, ‖PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) (Z ε₀) x‖ ≤
        LipQ * 4 * |ε - ε₀| := fun x => by
      have h0 := congrFun (hZ ε₀ h₀).1.2 x
      rw [phiR_eq] at h0 ⊢
      have e : Qd p R (qpt T ê dh ε (Z ε₀) x) + Mv T.M (fun y => Nd p R (Z ε₀ y)) x =
          Qd p R (qpt T ê dh ε (Z ε₀) x) - Qd p R (qpt T ê dh ε₀ (Z ε₀) x) := by
        rw [eq_neg_of_add_eq_zero_right h0]; abel
      rw [e]
      have hd0 := norm_qpt_sub T ê dh hê hd (hr1 ε₀ h₀) (hr1 ε h) (z := Z ε₀) (z' := Z ε₀)
        (D := 0) (fun _ => by simp) x
      rw [add_zero] at hd0
      refine (hQlip _ _ ((hqs ε₀ h₀ x).trans hρs4) ((hqs2 ε ε₀ h h₀ x).trans hρs4)).trans ?_
      calc _ ≤ LipQ * (4 * |ε - ε₀|) := mul_le_mul_of_nonneg_left hd0 hLipQ0
        _ = _ := by ring
    have := (hZ ε h).2.2 (Z ε₀) (fun y => (hZ ε₀ h₀).1.1 y) _ (by positivity) hres y
    calc _ ≤ CN * (LipQ * 4 * |ε - ε₀|) := this
      _ = _ := by rw [hCL]; ring
  have hCmax : CV ≤ max (max CV Cd) C3 := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨Z, V, fun ε h => ⟨⟨(hZ ε h).1.2, (hZ ε h).1.1, (hZ ε h).2.1⟩,
    fun y => ((hV ε h).1 y).trans hCmax, (hV ε h).2.1⟩, ?_, ?_, ?_, ?_⟩
  · -- `Z(0) = 0`
    have h0 : |(0 : ℝ)| ≤ δ₁ := by simp [hδ₁0.le]
    have hphi0 : PhiR T p R (fun y => (0 : ℝ) • ê y) (fun y => (0 : ℝ) ^ 2 • dh y)
        (fun _ => 0) = 0 := by
      funext x
      rw [phiR_eq, qpt_zero, Mv_const' T]
      exact Qd_Nd_zero R hp
    exact ((hZ 0 h0).2.1 (fun _ => 0) (fun _ => by simp [hrN.le]) hphi0).symm
  · -- `V(0) = z₁`
    have h0 : |(0 : ℝ)| ≤ δ₁ := by simp [hδ₁0.le]
    have hphi0 : PhiR T p R (fun y => (0 : ℝ) • ê y) (fun y => (0 : ℝ) ^ 2 • dh y)
        (fun _ => 0) = 0 := by
      funext x
      rw [phiR_eq, qpt_zero, Mv_const' T]
      exact Qd_Nd_zero R hp
    have hZ0 : Z 0 = fun _ => 0 :=
      ((hZ 0 h0).2.1 (fun _ => 0) (fun _ => by simp [hrN.le]) hphi0).symm
    have hL0 : LR T p R (V 0) = fun y => -DQs p R (ê y) := by
      funext x
      have h := (hV 0 h0).2.1 x
      rw [hZ0, (lin_peps_zero T R hp ê dh (V 0) x).1, (lin_peps_zero T R hp ê dh (V 0) x).2] at h
      exact h
    have := LinvR_LR T R hp hG (v := V 0) (B := K₁ * (2 * LQ)) (by positivity) (hV 0 h0).1
    rw [hL0] at this
    exact this.symm
  · -- differentiability with a quadratic remainder
    intro ε ε₀ h h₀ y
    set w : Y → Fin 9 → ℝ := fun y => (Z ε y - Z ε₀ y) - (ε - ε₀) • V ε₀ y with hw
    have hLw : ∀ x, Lin T p R ê dh ε₀ (Z ε₀) w x =
        Lin T p R ê dh ε₀ (Z ε₀) (fun y => Z ε y - Z ε₀ y) x +
          (ε - ε₀) • Peps T p R ê dh ε₀ (Z ε₀) x := fun x => by
      rw [hw, lin_sub, lin_smul, (hV ε₀ h₀).2.1 x, smul_neg, sub_neg_eq_add]
    have hE := hExp T ê dh hê hd ε₀ ε (Z ε₀) (Z ε) (CL * |ε - ε₀|) (hr1 ε₀ h₀) (hr1 ε h)
      (fun x => (hqs ε₀ h₀ x).trans hρs3) (fun x => (hqs ε h x).trans hρs3)
      (fun y => (hZr ε₀ h₀ y).trans hρs3) (fun y => (hZr ε h y).trans hρs3)
      (fun y => hZL ε ε₀ h h₀ y)
    have hA : ∀ x, ‖Lin T p R ê dh ε₀ (Z ε₀) w x‖ ≤ C₂ * (1 + CL) ^ 2 * (ε - ε₀) ^ 2 :=
      fun x => by
        have k := hE x
        rw [(hZ ε h).1.2, (hZ ε₀ h₀).1.2] at k
        simp only [Pi.zero_apply, sub_zero, zero_sub] at k
        rw [hLw x]
        have e : ‖-Lin T p R ê dh ε₀ (Z ε₀) (fun y => Z ε y - Z ε₀ y) x -
            (ε - ε₀) • Peps T p R ê dh ε₀ (Z ε₀) x‖ =
            ‖Lin T p R ê dh ε₀ (Z ε₀) (fun y => Z ε y - Z ε₀ y) x +
              (ε - ε₀) • Peps T p R ê dh ε₀ (Z ε₀) x‖ := by
          rw [← norm_neg]; congr 1; abel
        rw [e] at k
        refine k.trans (le_of_eq ?_)
        have : |ε - ε₀| + CL * |ε - ε₀| = (1 + CL) * |ε - ε₀| := by ring
        rw [this, mul_pow, sq_abs]
        ring
    have hwb : ∀ y, ‖w y‖ ≤ CL * |ε - ε₀| + |ε - ε₀| * (K₁ * (2 * LQ)) := fun y => by
      rw [hw]
      refine (norm_sub_le _ _).trans (add_le_add (hZL ε ε₀ h h₀ y) ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hV ε₀ h₀).1 y) (abs_nonneg _)
    have := hLbound ε₀ h₀ w _ _ hwb (by positivity) hA y
    calc _ ≤ K₁ * (C₂ * (1 + CL) ^ 2 * (ε - ε₀) ^ 2) := this
      _ = Cd * (ε - ε₀) ^ 2 := by rw [hCd]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _))
          (sq_nonneg _)
  · -- the derivative is Lipschitz
    intro ε ε₀ h h₀ y
    set u : Y → Fin 9 → ℝ := fun y => V ε y - V ε₀ y with hu
    set q := fun x => qpt T ê dh ε (Z ε) x with hq
    set q₀ := fun x => qpt T ê dh ε₀ (Z ε₀) x with hq₀
    have hqq : ∀ x, ‖q₀ x - q x‖ ≤ 4 * (1 + CL) * |ε - ε₀| := fun x => by
      have := norm_qpt_sub T ê dh hê hd (hr1 ε h) (hr1 ε₀ h₀) (z := Z ε) (z' := Z ε₀)
        (D := CL * |ε - ε₀|) (fun y => by rw [norm_sub_rev]; exact hZL ε ε₀ h h₀ y) x
      refine this.trans (le_of_eq ?_)
      rw [abs_sub_comm]; ring
    have hdQ : ∀ x, ‖fderiv ℝ (Qd p R) (q₀ x) - fderiv ℝ (Qd p R) (q x)‖ ≤
        LQ * (4 * (1 + CL) * |ε - ε₀|) := fun x =>
      (hQ (q x) (q₀ x) ((hqs ε h x).trans hρs4) ((hqs ε₀ h₀ x).trans hρs4)).2.1.trans
        (mul_le_mul_of_nonneg_left (hqq x) hLQ)
    have hLu : ∀ x, Lin T p R ê dh ε (Z ε) u x =
        (Peps T p R ê dh ε₀ (Z ε₀) x - Peps T p R ê dh ε (Z ε) x) +
          (Lin T p R ê dh ε₀ (Z ε₀) (V ε₀) x - Lin T p R ê dh ε (Z ε) (V ε₀) x) := fun x => by
      rw [hu, lin_sub, (hV ε h).2.1 x, (hV ε₀ h₀).2.1 x]
      abel
    set dr : Y → Fin 9 → ℝ := fun x => if T.depth x = 0 then dh x else 0 with hdr
    have hdr1 : ∀ x, ‖dr x‖ ≤ 1 := fun x => by
      simp only [hdr]; split_ifs; exacts [hd x, by simp]
    have hP : ∀ x, ‖Peps T p R ê dh ε₀ (Z ε₀) x - Peps T p R ê dh ε (Z ε) x‖ ≤
        (LQ * 2 + LQ * (4 * (1 + CL)) * 2) * |ε - ε₀| := fun x => by
      have e : Peps T p R ê dh ε₀ (Z ε₀) x - Peps T p R ê dh ε (Z ε) x =
          fderiv ℝ (Qd p R) (q₀ x) ((0 : Fin 5 → ℝ), (2 * ε₀ - 2 * ε) • dr x, (0 : Fin 9 → ℝ)) +
            (fderiv ℝ (Qd p R) (q₀ x) - fderiv ℝ (Qd p R) (q x))
              (ê x, (2 * ε) • dr x, (0 : Fin 9 → ℝ)) := by
        have hbb : ((0 : Fin 5 → ℝ), (2 * ε₀ - 2 * ε) • dr x, (0 : Fin 9 → ℝ)) =
            (ê x, (2 * ε₀) • dr x, (0 : Fin 9 → ℝ)) - (ê x, (2 * ε) • dr x, (0 : Fin 9 → ℝ)) := by
          simp [sub_smul]
        rw [hbb, map_sub, sub_apply]
        simp only [Peps, hq, hq₀, hdr]
        abel
      rw [e]
      have hb1 : ‖((0 : Fin 5 → ℝ), (2 * ε₀ - 2 * ε) • dr x, (0 : Fin 9 → ℝ))‖ ≤
          2 * |ε - ε₀| := by
        rw [Prod.norm_def, Prod.norm_def, norm_zero, norm_zero, norm_smul, Real.norm_eq_abs]
        refine max_le (by positivity) (max_le ?_ (by positivity))
        calc |2 * ε₀ - 2 * ε| * ‖dr x‖ ≤ |2 * ε₀ - 2 * ε| * 1 :=
              mul_le_mul_of_nonneg_left (hdr1 x) (abs_nonneg _)
          _ = 2 * |ε - ε₀| := by
              rw [mul_one, show 2 * ε₀ - 2 * ε = 2 * (ε₀ - ε) by ring, abs_mul, abs_sub_comm]
              norm_num
      have hb2 : ‖(ê x, (2 * ε) • dr x, (0 : Fin 9 → ℝ))‖ ≤ 2 := by
        rw [Prod.norm_def, Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs]
        have h2 : |2 * ε| ≤ 2 := by rw [abs_mul]; norm_num; exact hr1 ε h
        refine max_le ((hê x).trans (by norm_num)) (max_le ?_ (by norm_num))
        calc _ ≤ 2 * 1 := mul_le_mul h2 (hdr1 x) (norm_nonneg _) (by norm_num)
          _ = 2 := by ring
      calc _ ≤ ‖fderiv ℝ (Qd p R) (q₀ x) ((0 : Fin 5 → ℝ), (2 * ε₀ - 2 * ε) • dr x,
            (0 : Fin 9 → ℝ))‖ + ‖(fderiv ℝ (Qd p R) (q₀ x) - fderiv ℝ (Qd p R) (q x))
              (ê x, (2 * ε) • dr x, (0 : Fin 9 → ℝ))‖ := norm_add_le _ _
        _ ≤ LQ * (2 * |ε - ε₀|) + LQ * (4 * (1 + CL) * |ε - ε₀|) * 2 := by
            refine add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul (hQ _ _ ((hqs ε₀ h₀ x).trans hρs4) ((hqs ε₀ h₀ x).trans hρs4)).1 hb1
                (norm_nonneg _) hLQ)) ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul (hdQ x) hb2 (norm_nonneg _) (by positivity)))
        _ = _ := by ring
    have hLd : ∀ x, ‖Lin T p R ê dh ε₀ (Z ε₀) (V ε₀) x - Lin T p R ê dh ε (Z ε) (V ε₀) x‖ ≤
        (LQ * (4 * (1 + CL)) * CV + LN * CL * CV) * |ε - ε₀| := fun x => by
      have hVb : ∀ y, ‖V ε₀ y‖ ≤ CV := fun y => (hV ε₀ h₀).1 y
      have e : Lin T p R ê dh ε₀ (Z ε₀) (V ε₀) x - Lin T p R ê dh ε (Z ε) (V ε₀) x =
          (fderiv ℝ (Qd p R) (q₀ x) - fderiv ℝ (Qd p R) (q x)) (0, lagv T (V ε₀) x, V ε₀ x) +
            Mv T.M (fun y => (fderiv ℝ (Nd p R) (Z ε₀ y) - fderiv ℝ (Nd p R) (Z ε y))
              (V ε₀ y)) x := by
        have hN' : (fun y => (fderiv ℝ (Nd p R) (Z ε₀ y) - fderiv ℝ (Nd p R) (Z ε y))
            (V ε₀ y)) = fun y => fderiv ℝ (Nd p R) (Z ε₀ y) (V ε₀ y) -
              fderiv ℝ (Nd p R) (Z ε y) (V ε₀ y) := by
          funext y; rw [sub_apply]
        rw [hN', NonlinearNKMarkovLinks.Mv_sub, sub_apply]
        simp only [Lin, hq, hq₀]
        abel
      rw [e]
      have hv0 : ‖((0 : Fin 5 → ℝ), lagv T (V ε₀) x, V ε₀ x)‖ ≤ CV := by
        rw [Prod.norm_def, Prod.norm_def, norm_zero]
        exact max_le hCV0 (max_le (norm_lagv_le T hCV0 hVb x) (hVb x))
      have hNb : ∀ y, ‖(fderiv ℝ (Nd p R) (Z ε₀ y) - fderiv ℝ (Nd p R) (Z ε y)) (V ε₀ y)‖ ≤
          LN * CL * CV * |ε - ε₀| := fun y => by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        have h1 := (hN (Z ε y) (Z ε₀ y) ((hZr ε h y).trans hρs5)
          ((hZr ε₀ h₀ y).trans hρs5)).2.1
        have h2 : ‖Z ε₀ y - Z ε y‖ ≤ CL * |ε - ε₀| := by
          rw [norm_sub_rev]; exact hZL ε ε₀ h h₀ y
        calc _ ≤ LN * (CL * |ε - ε₀|) * CV := mul_le_mul (h1.trans
              (mul_le_mul_of_nonneg_left h2 hLN)) (hVb y) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      calc _ ≤ ‖(fderiv ℝ (Qd p R) (q₀ x) - fderiv ℝ (Qd p R) (q x))
            (0, lagv T (V ε₀) x, V ε₀ x)‖ + ‖Mv T.M (fun y => (fderiv ℝ (Nd p R) (Z ε₀ y) -
              fderiv ℝ (Nd p R) (Z ε y)) (V ε₀ y)) x‖ := norm_add_le _ _
        _ ≤ LQ * (4 * (1 + CL) * |ε - ε₀|) * CV + LN * CL * CV * |ε - ε₀| :=
            add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul (hdQ x) hv0 (norm_nonneg _) (by positivity)))
              (Mv_norm_le T.markov (by positivity) hNb x)
        _ = _ := by ring
    have hub : ∀ y, ‖u y‖ ≤ CV + CV := fun y =>
      (norm_sub_le _ _).trans (add_le_add ((hV ε h).1 y) ((hV ε₀ h₀).1 y))
    have hA : ∀ x, ‖Lin T p R ê dh ε (Z ε) u x‖ ≤
        (LQ * 2 + LQ * (4 * (1 + CL)) * 2 + LQ * (4 * (1 + CL)) * CV + LN * CL * CV) *
          |ε - ε₀| := fun x => by
      rw [hLu x]
      refine (norm_add_le _ _).trans ((add_le_add (hP x) (hLd x)).trans (le_of_eq ?_))
      ring
    have := hLbound ε h u _ _ hub (by positivity) hA y
    calc _ ≤ K₁ * ((LQ * 2 + LQ * (4 * (1 + CL)) * 2 + LQ * (4 * (1 + CL)) * CV +
          LN * CL * CV) * |ε - ε₀|) := this
      _ = C3 * |ε - ε₀| := by rw [hC3]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

/-- Woodford (2003), §1 (a quadratic first-order remainder gives a derivative): if
`|f(ε) − f(ε₀) − (ε − ε₀)g| ≤ C(ε − ε₀)²` for `|ε| ≤ δ` and `|ε₀| < δ`, then `f′(ε₀) = g`. -/
theorem hasDerivAt_of_quad {f : ℝ → ℝ} {g x₀ δ C : ℝ} (hx : |x₀| < δ)
    (h : ∀ ε, |ε| ≤ δ → |f ε - f x₀ - (ε - x₀) * g| ≤ C * (ε - x₀) ^ 2) :
    HasDerivAt f g x₀ := by
  rw [hasDerivAt_iff_isLittleO]
  have hev : ∀ᶠ ε in 𝓝 x₀, |ε| ≤ δ := by
    have : Set.Icc (-δ) δ ∈ 𝓝 x₀ := Icc_mem_nhds (by linarith [neg_abs_le x₀])
      (by linarith [le_abs_self x₀])
    filter_upwards [this] with ε hε
    exact abs_le.2 hε
  have hO : (fun ε => f ε - f x₀ - (ε - x₀) • g) =O[𝓝 x₀] fun ε => (ε - x₀) ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hev] with ε hε
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ε - x₀)), smul_eq_mul]
    exact h ε hε
  refine hO.trans_isLittleO ((Asymptotics.isLittleO_pow_sub_sub x₀
    (by norm_num : 1 < 2)).congr_left fun ε => ?_)
  rw [Real.norm_eq_abs, sq_abs]

/-- **Woodford (2003), App. A.3 (the solution is `C¹` in the amplitude at every node, with the
implicit-function derivative).** With `δ₁` of `ramsey_C1`, on every event tree, for every node
`y`, coordinate `i` and `|ε₀| < δ₁`: `ε ↦ Z(ε)(y)ᵢ` is differentiable at `ε₀` with derivative
`V(ε₀)(y)ᵢ`, and `ε ↦ V(ε)(y)ᵢ` is continuous at `ε₀`; at `ε₀ = 0` the derivative is
`z₁ = L⁻¹(−DQe(ê))`. -/
theorem ramsey_C1_node {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ δ₁ > 0, ∃ r > 0, ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ)
      (dh : Y → Fin 9 → ℝ), (∀ y, ‖ê y‖ ≤ 1) → (∀ y, ‖dh y‖ ≤ 1) →
        ∃ Z V : ℝ → Y → Fin 9 → ℝ,
          (∀ ε, |ε| ≤ δ₁ →
            PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) (Z ε) = 0 ∧
              (∀ y, ‖Z ε y‖ ≤ r) ∧ ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
                PhiR T p R (fun y => ε • ê y) (fun y => ε ^ 2 • dh y) z' = 0 → z' = Z ε) ∧
          V 0 = LinvR T p R (fun y => -DQs p R (ê y)) ∧
          ∀ ε₀, |ε₀| < δ₁ → ∀ y (i : Fin 9),
            HasDerivAt (fun ε => Z ε y i) (V ε₀ y i) ε₀ ∧
              ContinuousAt (fun ε => V ε y i) ε₀ := by
  obtain ⟨δ₁, hδ₁, r, hr, C, hC, H⟩ := ramsey_C1 R hp hG
  refine ⟨δ₁, hδ₁, r, hr, fun {Y} T ê dh hê hd => ?_⟩
  obtain ⟨Z, V, hZV, -, hV0, hD, hL⟩ := H T ê dh hê hd
  refine ⟨Z, V, fun ε h => (hZV ε h).1, hV0, fun ε₀ h₀ y i => ⟨?_, ?_⟩⟩
  · refine hasDerivAt_of_quad (C := C) h₀ fun ε hε => ?_
    have := (norm_le_pi_norm (Z ε y - Z ε₀ y - (ε - ε₀) • V ε₀ y) i).trans
      (hD ε ε₀ hε h₀.le y)
    simpa [Real.norm_eq_abs] using this
  · rw [Metric.continuousAt_iff]
    intro η hη
    refine ⟨min (δ₁ - |ε₀|) (η / (C + 1)), lt_min (by linarith) (by positivity),
      fun {ε} hε => ?_⟩
    rw [Real.dist_eq] at hε ⊢
    have hε1 : |ε| ≤ δ₁ := by
      have := (abs_sub_abs_le_abs_sub ε ε₀).trans (hε.le.trans (min_le_left _ _))
      linarith
    have k := (norm_le_pi_norm (V ε y - V ε₀ y) i).trans (hL ε ε₀ hε1 h₀.le y)
    rw [Real.norm_eq_abs] at k
    simp only [Pi.sub_apply] at k
    calc |V ε y i - V ε₀ y i| ≤ C * |ε - ε₀| := k
      _ ≤ C * (η / (C + 1)) := mul_le_mul_of_nonneg_left
          (hε.le.trans (min_le_right _ _)) hC
      _ < η := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith

end Woodford.StabilizationWelfare.TidyR6aSmooth
