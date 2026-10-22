/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergSmooth

/-!
# Indeterminacy of the exact Rotemberg model when the Taylor principle fails

Woodford (2003), *Interest and Prices*, Chapter 4, §2.2 (Proposition 4.3, p. 254: when the
Taylor principle fails, the equilibrium is indeterminate and self-fulfilling fluctuations are
possible), Chapter 2 (self-fulfilling expectations), Appendix A.3, for the exact nonlinear
Rotemberg model of `NonlinearRotemberg`.

If `κ(φ_π − 1) + (1 − β)φ_y < 0`, the IS–AS matrix `A` has real roots `0 < μ₁ < 1 < μ₂`
(`roots_of_fail`). The linearised operator then has a one-dimensional bounded kernel
`k_t = μ₂^{−t} w₂` in perfect foresight, and once the unstable coordinate `ℓ₂·(ĉ₀, π₀)` is pinned
the operator is invertible (`LinvI`, `LinvI_spec`, `inj_SI`). The abstract implicit function
result `NonlinearRotembergNewton.newton_exist`, applied to the maps shifted by `c·k`, gives:

* **`indeterminacy_continuum`**: for every `ρ > 0` there are `c₀ > 0` and a family `c ↦ z^c`,
  `|c| ≤ c₀`, of DISTINCT bounded perfect-foresight equilibria of the EXACT nonlinear model with
  `‖z^c_t‖ ≤ ρ` at every date (`ℓ₂·(ĉ^c₀, π^c₀) = c`): a continuum of equilibria in every
  neighbourhood of the steady state;
* **`indeterminacy_every_system`**: every member is an equilibrium of every expectation
  system (every finite event tree, every Markov chain);
* **`sunspot_equilibria`**: with any date-`0` sunspot variable `c(ω)` known at date `0` (for a
  finite tree: constant on the date-`0` information cells), `z_t(ω) = z^{c(ω)}_t` is a bounded
  equilibrium; distinct sunspots give distinct equilibria.

Together with `NonlinearRotembergMarkov.markov_equilibrium_general` (local uniqueness when the
principle holds) this proves: **local uniqueness of the bounded equilibrium near the steady
state holds iff the Taylor principle holds**, except at the boundary
`κ(φ_π − 1) + (1 − β)φ_y = 0` (a unit root; see `NonlinearRotembergBoundary` and
`NonlinearRotembergBoundaryPair`).
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergIndet

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov)
open NonlinearRotemberg NonlinearRotembergNewton NonlinearRotembergMarkov NonlinearRotembergSmooth

variable {p : Par}

/-! ## Perfect foresight as a Markov operator on dates -/

/-- Woodford (2003), Ch. 2 (perfect foresight): the forecast operator on dates,
`(Mf)(t) = f(t+1)`. -/
def shiftOp : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun f t := f (t + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The perfect-foresight forecast operator is a Markov operator. -/
theorem shiftOp_isMarkov : IsMarkov shiftOp :=
  ⟨rfl, fun _ _ hC t => hC (t + 1)⟩

/-! ## The roots when the Taylor principle fails -/

/-- Woodford (2003), Proposition 4.3, Rotemberg slope (**two real roots straddling one**): if
`κ(φ_π − 1) + (1 − β)φ_y < 0` then `χ(μ) = μ² − Tμ + D` (`T = tr A`, `D = det A`) has roots
`0 < μ₁ < 1 < μ₂`, `A₁₀ = κσ/dd > 0`. -/
theorem roots_of_fail (hp : p.Basic) (hT : p.κ * (p.φ - 1) + (1 - p.β) * p.φy < 0) :
    ∃ μ1 μ2, 0 < μ1 ∧ μ1 < 1 ∧ 1 < μ2 ∧
      μ1 ^ 2 - tr2 (Arot p) * μ1 + det2 (Arot p) = 0 ∧
      μ2 ^ 2 - tr2 (Arot p) * μ2 + det2 (Arot p) = 0 ∧
      μ1 + μ2 = tr2 (Arot p) ∧ 0 < Arot p 1 0 := by
  have hd := hp.dd_pos
  set T := tr2 (Arot p) with hTdef
  set D := det2 (Arot p) with hDdef
  have hD0 : 0 < D := by rw [hDdef, det2_Arot]; exact div_pos (mul_pos hp.σ_pos hp.β_pos) hd
  have hTD : 1 + D < T := by
    rw [hTdef, hDdef, tr2_Arot, det2_Arot, ← sub_pos]
    have : (p.σ + p.κ + p.β * (p.σ + p.φy)) / p.dd - (1 + p.σ * p.β / p.dd) =
        -(p.κ * (p.φ - 1) + (1 - p.β) * p.φy) / p.dd := by
      field_simp; unfold Par.dd; ring
    rw [this]; exact div_pos (by linarith) hd
  have hT0 : 0 < T := by linarith
  have hdisc : 0 < T ^ 2 - 4 * D := by
    nlinarith [mul_lt_mul'' hTD hTD (by linarith) (by linarith), sq_nonneg (1 - D)]
  set sq := Real.sqrt (T ^ 2 - 4 * D) with hsq
  have hsq2 : sq ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hdisc.le
  have hsq0 : 0 < sq := Real.sqrt_pos.2 hdisc
  refine ⟨(T - sq) / 2, (T + sq) / 2, ?_, ?_, ?_, by nlinarith, by nlinarith, by ring, ?_⟩
  · have : sq ^ 2 < T ^ 2 := by rw [hsq2]; linarith
    nlinarith
  · -- `χ(1) < 0` puts `1` strictly between the roots
    have h1 : ((1 : ℝ) - (T - sq) / 2) * (1 - (T + sq) / 2) < 0 := by nlinarith
    have : (T - sq) / 2 < (T + sq) / 2 := by linarith
    by_contra hc
    push Not at hc
    nlinarith
  · have h1 : ((1 : ℝ) - (T - sq) / 2) * (1 - (T + sq) / 2) < 0 := by nlinarith
    by_contra hc
    push Not at hc
    nlinarith
  · simp only [Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact div_pos (mul_pos hp.κ_pos hp.σ_pos) hd

/-- The left eigenvector `ℓ(μ) = (A₁₀, μ − A₀₀)` of a root: `ℓ·(Ay) = μ ℓ·y`. -/
theorem ell_A {A : Matrix (Fin 2) (Fin 2) ℝ} {μ : ℝ}
    (hμ : μ ^ 2 - tr2 A * μ + det2 A = 0) (y : Fin 2 → ℝ) :
    A 1 0 * (A.mulVec y) 0 + (μ - A 0 0) * (A.mulVec y) 1 =
      μ * (A 1 0 * y 0 + (μ - A 0 0) * y 1) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp only [tr2, det2] at hμ
  linear_combination (-y 1) * hμ

/-! ## The linear problem with the unstable coordinate pinned -/

/-- The coordinate `ℓ(μ)·y = A₁₀ y₀ + (μ − A₀₀) y₁` along the left eigenvector of the root `μ`. -/
def ell (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  A 1 0 * y 0 + (μ - A 0 0) * y 1

/-- The vector with prescribed coordinates `ℓ(μ₁)·y = s₁`, `ℓ(μ₂)·y = s₂`. -/
noncomputable def ginv (A : Matrix (Fin 2) (Fin 2) ℝ) (μ1 μ2 s1 s2 : ℝ) : Fin 2 → ℝ :=
  ![((μ2 - A 0 0) * s1 - (μ1 - A 0 0) * s2) / (A 1 0 * (μ2 - μ1)), (s2 - s1) / (μ2 - μ1)]

/-- `ginv` has the prescribed coordinates. -/
theorem ell_ginv {A : Matrix (Fin 2) (Fin 2) ℝ} {μ1 μ2 : ℝ} (hA : A 1 0 ≠ 0) (hμ : μ1 < μ2)
    (s1 s2 : ℝ) : ell A μ1 (ginv A μ1 μ2 s1 s2) = s1 ∧ ell A μ2 (ginv A μ1 μ2 s1 s2) = s2 := by
  have h : μ2 - μ1 ≠ 0 := by linarith
  constructor <;> simp only [ell, ginv, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    field_simp <;> ring

/-- The two coordinates determine the vector. -/
theorem eq_zero_of_ell {A : Matrix (Fin 2) (Fin 2) ℝ} {μ1 μ2 : ℝ} (hA : A 1 0 ≠ 0)
    (hμ : μ1 < μ2) {y : Fin 2 → ℝ} (h1 : ell A μ1 y = 0) (h2 : ell A μ2 y = 0) : y = 0 := by
  simp only [ell] at h1 h2
  have hy1 : y 1 = 0 := by
    have : (μ2 - μ1) * y 1 = 0 := by linear_combination h2 - h1
    exact (mul_eq_zero.1 this).resolve_left (by linarith)
  have hy0 : y 0 = 0 := by
    rw [hy1, mul_zero, add_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left hA
  funext i; fin_cases i
  · exact hy0
  · exact hy1

/-- `ℓ` is linear in differences. -/
theorem ell_sub (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) (y y' : Fin 2 → ℝ) :
    ell A μ (y - y') = ell A μ y - ell A μ y' := by
  simp only [ell, Pi.sub_apply]; ring

/-- `ℓ` is bounded: `|ℓ(μ)·y| ≤ (|A₁₀| + |μ − A₀₀|)‖y‖`. -/
theorem abs_ell_le (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) (y : Fin 2 → ℝ) :
    |ell A μ y| ≤ (|A 1 0| + |μ - A 0 0|) * ‖y‖ := by
  have h0 : |y 0| ≤ ‖y‖ := by simpa using norm_le_pi_norm y 0
  have h1 : |y 1| ≤ ‖y‖ := by simpa using norm_le_pi_norm y 1
  unfold ell
  calc _ ≤ |A 1 0 * y 0| + |(μ - A 0 0) * y 1| := abs_add_le _ _
    _ = |A 1 0| * |y 0| + |μ - A 0 0| * |y 1| := by rw [abs_mul, abs_mul]
    _ ≤ |A 1 0| * ‖y‖ + |μ - A 0 0| * ‖y‖ :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ = _ := by ring

/-- Woodford (2003), (A.13) (**the forward solution of the stable coordinate**):
`s_t = ∑ₖ μᵏ β_{t+k}`. -/
noncomputable def fwd1 (μ : ℝ) (β : ℕ → ℝ) (t : ℕ) : ℝ := ∑' k, μ ^ k * β (t + k)

/-- The forward solution: summable, bounded by `B/(1 − μ)`, and `s_t = β_t + μ s_{t+1}`. -/
theorem fwd1_spec {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) {β : ℕ → ℝ} {B : ℝ}
    (hβ : ∀ t, |β t| ≤ B) (t : ℕ) :
    |fwd1 μ β t| ≤ B / (1 - μ) ∧ fwd1 μ β t = β t + μ * fwd1 μ β (t + 1) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hβ 0)
  have hg : Summable fun k : ℕ => μ ^ k * B :=
    (summable_geometric_of_lt_one hμ0 hμ1).mul_right B
  have hb : ∀ t k, ‖μ ^ k * β (t + k)‖ ≤ μ ^ k * B := fun t k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hμ0 k)]
    exact mul_le_mul_of_nonneg_left (hβ _) (pow_nonneg hμ0 k)
  have hs : ∀ t, Summable fun k => μ ^ k * β (t + k) := fun t =>
    Summable.of_norm_bounded hg (hb t)
  refine ⟨?_, ?_⟩
  · have := tsum_of_norm_bounded hg.hasSum (hb t)
    rw [← Real.norm_eq_abs]
    refine this.trans (le_of_eq ?_)
    rw [tsum_mul_right, tsum_geometric_of_lt_one hμ0 hμ1]
    field_simp
  · unfold fwd1
    rw [(hs t).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [pow_succ]; ring_nf

/-- Woodford (2003), (A.13) (**the unstable coordinate solved backward from its pinned initial
value `0`**): `s₀ = 0`, `s_{t+1} = (s_t − β_t)/μ`. -/
noncomputable def bwd2 (μ : ℝ) (β : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (bwd2 μ β t - β t) / μ

/-- The backward solution is bounded by `B/(μ − 1)` for `μ > 1`. -/
theorem bwd2_bound {μ : ℝ} (hμ : 1 < μ) {β : ℕ → ℝ} {B : ℝ} (hβ : ∀ t, |β t| ≤ B) (t : ℕ) :
    |bwd2 μ β t| ≤ B / (μ - 1) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hβ 0)
  have hμ1 : 0 < μ - 1 := by linarith
  induction t with
  | zero => simp only [bwd2, abs_zero]; positivity
  | succ t ih =>
    simp only [bwd2]
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < μ), div_le_div_iff₀ (by linarith) hμ1]
    calc |bwd2 μ β t - β t| * (μ - 1) ≤ (B / (μ - 1) + B) * (μ - 1) :=
          mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add ih (hβ t))) hμ1.le
      _ = B * μ := by field_simp; ring

/-- The backward solution satisfies `s_t = μ s_{t+1} + β_t`. -/
theorem bwd2_rec {μ : ℝ} (hμ : μ ≠ 0) (β : ℕ → ℝ) (t : ℕ) :
    bwd2 μ β t = μ * bwd2 μ β (t + 1) + β t := by
  simp only [bwd2]; field_simp; ring

/-- Woodford (2003), (A.13) with the unstable coordinate pinned (**the solution of
`u_t = A u_{t+1} + b_t` with `ℓ(μ₂)·u₀ = 0`**). -/
noncomputable def uI (A : Matrix (Fin 2) (Fin 2) ℝ) (μ1 μ2 : ℝ) (b : ℕ → Fin 2 → ℝ) (t : ℕ) :
    Fin 2 → ℝ :=
  ginv A μ1 μ2 (fwd1 μ1 (fun t => ell A μ1 (b t)) t) (bwd2 μ2 (fun t => ell A μ2 (b t)) t)

/-- The hypotheses on the roots: `0 < μ₁ < 1 < μ₂`, both roots of `χ`, `A₁₀ > 0`. -/
def RootHyp (A : Matrix (Fin 2) (Fin 2) ℝ) (μ1 μ2 : ℝ) : Prop :=
  0 < μ1 ∧ μ1 < 1 ∧ 1 < μ2 ∧ μ1 ^ 2 - tr2 A * μ1 + det2 A = 0 ∧
    μ2 ^ 2 - tr2 A * μ2 + det2 A = 0 ∧ μ1 + μ2 = tr2 A ∧ 0 < A 1 0

/-- The constant of the bound on `uI`. -/
noncomputable def Ku (A : Matrix (Fin 2) (Fin 2) ℝ) (μ1 μ2 : ℝ) : ℝ :=
  (|μ2 - A 0 0| + |μ1 - A 0 0| + A 1 0) / (A 1 0 * (μ2 - μ1)) *
    ((|A 1 0| + |μ1 - A 0 0|) / (1 - μ1) + (|A 1 0| + |μ2 - A 0 0|) / (μ2 - 1))

/-- Woodford (2003), (A.13) (**the pinned solution exists, is bounded, and has `ℓ(μ₂)·u₀ = 0`**). -/
theorem uI_spec {A : Matrix (Fin 2) (Fin 2) ℝ} {μ1 μ2 : ℝ} (h : RootHyp A μ1 μ2)
    {b : ℕ → Fin 2 → ℝ} {B : ℝ} (hb : ∀ t, ‖b t‖ ≤ B) :
    (∀ t, uI A μ1 μ2 b t = A.mulVec (uI A μ1 μ2 b (t + 1)) + b t) ∧
    (∀ t, ‖uI A μ1 μ2 b t‖ ≤ Ku A μ1 μ2 * B) ∧ ell A μ2 (uI A μ1 μ2 b 0) = 0 := by
  obtain ⟨h10, h11, h21, hc1, hc2, -, hA⟩ := h
  have hμ : μ1 < μ2 := by linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb 0)
  set β1 := fun t => ell A μ1 (b t) with hβ1
  set β2 := fun t => ell A μ2 (b t) with hβ2
  have hb1 : ∀ t, |β1 t| ≤ (|A 1 0| + |μ1 - A 0 0|) * B := fun t =>
    (abs_ell_le A μ1 (b t)).trans (mul_le_mul_of_nonneg_left (hb t) (by positivity))
  have hb2 : ∀ t, |β2 t| ≤ (|A 1 0| + |μ2 - A 0 0|) * B := fun t =>
    (abs_ell_le A μ2 (b t)).trans (mul_le_mul_of_nonneg_left (hb t) (by positivity))
  have hcoord : ∀ t, ell A μ1 (uI A μ1 μ2 b t) = fwd1 μ1 β1 t ∧
      ell A μ2 (uI A μ1 μ2 b t) = bwd2 μ2 β2 t := fun t => ell_ginv hA.ne' hμ _ _
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · have hz := eq_zero_of_ell (A := A) (y := uI A μ1 μ2 b t - (A.mulVec (uI A μ1 μ2 b (t + 1)) +
      b t)) hA.ne' hμ ?_ ?_
    · exact sub_eq_zero.1 hz
    · have e1 := ell_sub A μ1 (uI A μ1 μ2 b t) (A.mulVec (uI A μ1 μ2 b (t + 1)) + b t)
      have e2 : ell A μ1 (A.mulVec (uI A μ1 μ2 b (t + 1)) + b t) =
          μ1 * ell A μ1 (uI A μ1 μ2 b (t + 1)) + β1 t := by
        have := ell_A hc1 (uI A μ1 μ2 b (t + 1))
        simp only [ell, Pi.add_apply, hβ1] at this ⊢
        linear_combination this
      rw [e1, e2, (hcoord t).1, (hcoord (t + 1)).1, (fwd1_spec h10.le h11 hb1 t).2]
      ring
    · have e1 := ell_sub A μ2 (uI A μ1 μ2 b t) (A.mulVec (uI A μ1 μ2 b (t + 1)) + b t)
      have e2 : ell A μ2 (A.mulVec (uI A μ1 μ2 b (t + 1)) + b t) =
          μ2 * ell A μ2 (uI A μ1 μ2 b (t + 1)) + β2 t := by
        have := ell_A hc2 (uI A μ1 μ2 b (t + 1))
        simp only [ell, Pi.add_apply, hβ2] at this ⊢
        linear_combination this
      rw [e1, e2, (hcoord t).2, (hcoord (t + 1)).2, bwd2_rec (by linarith) β2 t]
      ring
  · have hs1 := (fwd1_spec h10.le h11 hb1 t).1
    have hs2 := bwd2_bound h21 hb2 t
    set s1 := fwd1 μ1 β1 t
    set s2 := bwd2 μ2 β2 t
    have hd : 0 < A 1 0 * (μ2 - μ1) := mul_pos hA (by linarith)
    set g := (|μ2 - A 0 0| + |μ1 - A 0 0| + A 1 0) / (A 1 0 * (μ2 - μ1)) with hg
    have hg0 : 0 ≤ g := by positivity
    have hS : |s1| + |s2| ≤ ((|A 1 0| + |μ1 - A 0 0|) / (1 - μ1) +
        (|A 1 0| + |μ2 - A 0 0|) / (μ2 - 1)) * B := by
      have e1 : (|A 1 0| + |μ1 - A 0 0|) * B / (1 - μ1) =
          (|A 1 0| + |μ1 - A 0 0|) / (1 - μ1) * B := by ring
      have e2 : (|A 1 0| + |μ2 - A 0 0|) * B / (μ2 - 1) =
          (|A 1 0| + |μ2 - A 0 0|) / (μ2 - 1) * B := by ring
      rw [e1] at hs1; rw [e2] at hs2; linarith
    have hgD : g * (A 1 0 * (μ2 - μ1)) = |μ2 - A 0 0| + |μ1 - A 0 0| + A 1 0 := by
      rw [hg]; exact div_mul_cancel₀ _ hd.ne'
    have hu0 : uI A μ1 μ2 b t 0 =
        ((μ2 - A 0 0) * s1 - (μ1 - A 0 0) * s2) / (A 1 0 * (μ2 - μ1)) := rfl
    have hu1 : uI A μ1 μ2 b t 1 = (s2 - s1) / (μ2 - μ1) := rfl
    have hy : ∀ i, |uI A μ1 μ2 b t i| ≤ g * (|s1| + |s2|) := fun i => by
      fin_cases i
      · simp only [Fin.zero_eta]
        rw [hu0, abs_div, abs_of_pos hd, div_le_iff₀ hd, mul_comm g, mul_assoc, hgD]
        calc |(μ2 - A 0 0) * s1 - (μ1 - A 0 0) * s2| ≤
              |(μ2 - A 0 0) * s1| + |(μ1 - A 0 0) * s2| := abs_sub _ _
          _ = |μ2 - A 0 0| * |s1| + |μ1 - A 0 0| * |s2| := by rw [abs_mul, abs_mul]
          _ ≤ _ := by nlinarith [abs_nonneg s1, abs_nonneg s2, abs_nonneg (μ2 - A 0 0),
              abs_nonneg (μ1 - A 0 0), hA]
      · simp only [Fin.mk_one]
        have hd2 : 0 < μ2 - μ1 := by linarith
        rw [hu1, abs_div, abs_of_pos hd2, div_le_iff₀ hd2]
        have : g * (μ2 - μ1) = (|μ2 - A 0 0| + |μ1 - A 0 0| + A 1 0) / A 1 0 := by
          rw [hg, div_mul_eq_mul_div, mul_comm (A 1 0), ← div_div, mul_div_assoc,
            div_self hd2.ne', mul_one]
        rw [mul_comm g, mul_assoc, this]
        have h1 : 1 ≤ (|μ2 - A 0 0| + |μ1 - A 0 0| + A 1 0) / A 1 0 := by
          rw [le_div_iff₀ hA]; linarith [abs_nonneg (μ2 - A 0 0), abs_nonneg (μ1 - A 0 0)]
        calc |s2 - s1| ≤ |s2| + |s1| := abs_sub _ _
          _ ≤ (|s1| + |s2|) * ((|μ2 - A 0 0| + |μ1 - A 0 0| + A 1 0) / A 1 0) := by
              nlinarith [abs_nonneg s1, abs_nonneg s2]
    have hK : Ku A μ1 μ2 * B = g * (((|A 1 0| + |μ1 - A 0 0|) / (1 - μ1) +
        (|A 1 0| + |μ2 - A 0 0|) / (μ2 - 1)) * B) := by unfold Ku; rw [hg]; ring
    rw [hK]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact (hy i).trans (mul_le_mul_of_nonneg_left hS hg0)
  · rw [(hcoord 0).2]; rfl

/-- The constant `Ku` is nonnegative under the root hypotheses. -/
theorem Ku_nonneg {A : Matrix (Fin 2) (Fin 2) ℝ} {μ1 μ2 : ℝ} (h : RootHyp A μ1 μ2) :
    0 ≤ Ku A μ1 μ2 := by
  obtain ⟨-, h11, h21, -, -, -, hA⟩ := h
  have : 0 < μ2 - μ1 := by linarith
  have : 0 < 1 - μ1 := by linarith
  have : 0 < μ2 - 1 := by linarith
  unfold Ku; positivity

/-! ## The Rotemberg operator with the unstable coordinate pinned (perfect foresight) -/

/-- The class of perfect-foresight paths whose unstable coordinate `ℓ(μ₂)·(ĉ₀, π₀)` vanishes. -/
def SI (p : Par) (μ2 : ℝ) (w : ℕ → Fin 3 → ℝ) : Prop := ell (Arot p) μ2 ![w 0 2, w 0 1] = 0

/-- Woodford (2003), App. A.3 (**the inverse of the linearised operator on the pinned class**):
`(ĉ, π)` from `uI`, `ŷ = ĉ − r₂`. -/
noncomputable def LinvI (p : Par) (μ1 μ2 : ℝ) (r : ℕ → Fin 3 → ℝ) : ℕ → Fin 3 → ℝ :=
  fun t => ![uI (Arot p) μ1 μ2 (bR p r) t 0 - r t 2, uI (Arot p) μ1 μ2 (bR p r) t 1,
    uI (Arot p) μ1 μ2 (bR p r) t 0]

/-- The constant of the pinned inverse. -/
noncomputable def KI (p : Par) (μ1 μ2 : ℝ) : ℝ := Ku (Arot p) μ1 μ2 * cb p + 1

/-- The pinned constant is positive. -/
theorem KI_pos (hp : p.Basic) {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2) : 0 < KI p μ1 μ2 := by
  unfold KI
  have := mul_nonneg (Ku_nonneg h) (cb_nonneg hp)
  linarith

/-- The pinned inverse always lands in the pinned class (`s₀ = 0` by construction). -/
theorem LinvI_SI {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2) (r : ℕ → Fin 3 → ℝ) :
    SI p μ2 (LinvI p μ1 μ2 r) := by
  obtain ⟨-, h11, h21, -, -, -, hA⟩ := h
  have e : (![LinvI p μ1 μ2 r 0 2, LinvI p μ1 μ2 r 0 1] : Fin 2 → ℝ) =
      uI (Arot p) μ1 μ2 (bR p r) 0 := by
    funext i; fin_cases i <;> rfl
  unfold SI; rw [e]
  exact (ell_ginv hA.ne' (by linarith) _ _).2

/-- Woodford (2003), App. A.3 (**the pinned inverse: bounded right inverse into the class**). -/
theorem LinvI_spec (hp : p.Basic) {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2)
    {r : ℕ → Fin 3 → ℝ} {a : ℝ} (ha : 0 ≤ a) (hr : ∀ t, ‖r t‖ ≤ a) :
    (∀ t, ‖LinvI p μ1 μ2 r t‖ ≤ KI p μ1 μ2 * a) ∧ Lop p shiftOp (LinvI p μ1 μ2 r) = r ∧
      SI p μ2 (LinvI p μ1 μ2 r) := by
  obtain ⟨hrec, hub, h0⟩ := uI_spec h (norm_bR_le hp ha hr)
  set u := uI (Arot p) μ1 μ2 (bR p r) with hu
  have hrc : ∀ t i, |r t i| ≤ a := fun t i => by
    have := norm_le_pi_norm (r t) i; rw [Real.norm_eq_abs] at this; exact this.trans (hr t)
  have huc : ∀ t i, |u t i| ≤ Ku (Arot p) μ1 μ2 * (cb p * a) := fun t i => by
    have := norm_le_pi_norm (u t) i; rw [Real.norm_eq_abs] at this
    exact this.trans (hub t)
  refine ⟨fun t => ?_, ?_, ?_⟩
  · have hK : Ku (Arot p) μ1 μ2 * (cb p * a) + a = KI p μ1 μ2 * a := by unfold KI; ring
    have hSa : 0 ≤ Ku (Arot p) μ1 μ2 * (cb p * a) :=
      mul_nonneg (Ku_nonneg h) (mul_nonneg (cb_nonneg hp) ha)
    refine (pi_norm_le_iff_of_nonneg (by rw [← hK]; linarith)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← hK]
    fin_cases i
    · simp only [LinvI, Fin.zero_eta, Matrix.cons_val_zero]
      exact (abs_sub _ _).trans (add_le_add (huc t 0) (hrc t 2))
    · simp only [LinvI, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [huc t 1]
    · simp only [LinvI, Fin.reduceFinMk, Matrix.cons_val]
      linarith [huc t 0]
  · exact Lop_block hp shiftOp r u hrec
  · have e : (![LinvI p μ1 μ2 r 0 2, LinvI p μ1 μ2 r 0 1] : Fin 2 → ℝ) = u 0 := by
      funext i; fin_cases i <;> rfl
    unfold SI; rw [e]; exact h0

/-- The pinned class is a linear subspace: differences. -/
theorem SI_sub {μ2 : ℝ} {v w : ℕ → Fin 3 → ℝ} (hv : SI p μ2 v) (hw : SI p μ2 w) :
    SI p μ2 (fun t => v t - w t) := by
  unfold SI at *
  have : (![(fun t => v t - w t) 0 2, (fun t => v t - w t) 0 1] : Fin 2 → ℝ) =
      ![v 0 2, v 0 1] - ![w 0 2, w 0 1] := by
    funext i; fin_cases i <;> rfl
  rw [this, ell_sub, hv, hw, sub_zero]

/-- Woodford (2003), Proposition 4.3 (**injectivity on the pinned class**): a bounded path in
the class with `L v = 0` vanishes: the stable coordinate is `0` by boundedness, the unstable one by
the pin. -/
theorem inj_SI (hp : p.Basic) {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2) {v : ℕ → Fin 3 → ℝ}
    {V : ℝ} (hv : ∀ t, ‖v t‖ ≤ V) (hS : SI p μ2 v) (h0 : Lop p shiftOp v = 0) : v = 0 := by
  obtain ⟨h10, h11, h21, hc1, hc2, -, hA⟩ := h
  have hhom := homog_block hp shiftOp h0
  set u : ℕ → Fin 2 → ℝ := fun t => ![v t 2, v t 1] with hu
  have hrec : ∀ t, u t = (Arot p).mulVec (u (t + 1)) := fun t => hhom t
  have huB : ∀ t, ‖u t‖ ≤ V := fun t => by
    refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hv t))).2 fun i => ?_
    fin_cases i
    · simpa [hu] using norm_le_pi_norm (v t) 2 |>.trans (hv t)
    · simpa [hu] using norm_le_pi_norm (v t) 1 |>.trans (hv t)
  have hV : 0 ≤ V := (norm_nonneg _).trans (hv 0)
  -- the stable coordinate
  have hs1 : ∀ t, ell (Arot p) μ1 (u t) = μ1 * ell (Arot p) μ1 (u (t + 1)) := fun t => by
    rw [hrec t]; exact ell_A hc1 _
  have hs1n : ∀ n t, ell (Arot p) μ1 (u t) = μ1 ^ n * ell (Arot p) μ1 (u (t + n)) := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [ih t, hs1 (t + n), pow_succ, ← add_assoc]; ring
  have hs10 : ∀ t, ell (Arot p) μ1 (u t) = 0 := fun t => by
    set C := (|Arot p 1 0| + |μ1 - Arot p 0 0|) * V
    have hb : ∀ n, |ell (Arot p) μ1 (u t)| ≤ μ1 ^ n * C := fun n => by
      rw [hs1n n t, abs_mul, abs_of_nonneg (pow_nonneg h10.le n)]
      exact mul_le_mul_of_nonneg_left ((abs_ell_le _ _ _).trans
        (mul_le_mul_of_nonneg_left (huB _) (by positivity))) (pow_nonneg h10.le n)
    have hl : Tendsto (fun n => μ1 ^ n * C) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h10.le h11).mul_const C
    exact abs_nonpos_iff.1 (ge_of_tendsto' hl hb)
  -- the unstable coordinate
  have hs2 : ∀ t, ell (Arot p) μ2 (u t) = 0 := by
    intro t
    induction t with
    | zero => exact hS
    | succ t ih =>
      have this : ell (Arot p) μ2 ((Arot p).mulVec (u (t + 1))) =
          μ2 * ell (Arot p) μ2 (u (t + 1)) := ell_A hc2 (u (t + 1))
      rw [← hrec t, ih] at this
      have hμ2 : μ2 ≠ 0 := by linarith
      exact (mul_eq_zero.1 this.symm).resolve_left hμ2
  have hu0 : ∀ t, u t = 0 := fun t => eq_zero_of_ell hA.ne' (by linarith) (hs10 t) (hs2 t)
  funext t i
  have h2 : v t 2 = 0 := by have := congrFun (hu0 t) 0; simpa [hu] using this
  have h1 : v t 1 = 0 := by have := congrFun (hu0 t) 1; simpa [hu] using this
  have e2 := (lin_nkpc hp shiftOp h0 t).1
  fin_cases i
  · simp only [Fin.zero_eta, Pi.zero_apply]; linarith
  · exact h1
  · exact h2

/-- Woodford (2003), App. A.3: on the pinned class the pinned inverse is a left inverse. -/
theorem LinvI_left (hp : p.Basic) {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2)
    {v : ℕ → Fin 3 → ℝ} (hS : SI p μ2 v) {V : ℝ} (hv : ∀ t, ‖v t‖ ≤ V) :
    LinvI p μ1 μ2 (Lop p shiftOp v) = v := by
  have hV : 0 ≤ V := (norm_nonneg _).trans (hv 0)
  have hb := LG_bounded (Q := Qmap p) (N := Nmap p) shiftOp_isMarkov hV hv
  rw [LG_eq] at hb
  obtain ⟨hB, hL, hS'⟩ := LinvI_spec hp h (by positivity) hb
  have hd : (fun t => LinvI p μ1 μ2 (Lop p shiftOp v) t - v t) = 0 := by
    refine inj_SI hp h (V := KI p μ1 μ2 * ((‖fderiv ℝ (Qmap p) (0, 0)‖ +
      ‖fderiv ℝ (Nmap p) (0, 0)‖) * V) + V)
      (fun t => (norm_sub_le _ _).trans (add_le_add (hB t) (hv t))) (SI_sub hS' hS) ?_
    rw [Lop_sub, hL]; funext t; simp
  funext t
  exact sub_eq_zero.1 (congrFun hd t)

/-- Woodford (2003), App. A.3: the pinned inverse is additive in differences. -/
theorem LinvI_sub (hp : p.Basic) {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2)
    {r r' : ℕ → Fin 3 → ℝ} {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hr : ∀ t, ‖r t‖ ≤ a)
    (hr' : ∀ t, ‖r' t‖ ≤ a') :
    LinvI p μ1 μ2 (fun t => r t - r' t) = fun t => LinvI p μ1 μ2 r t - LinvI p μ1 μ2 r' t := by
  have hd : ∀ t, ‖r t - r' t‖ ≤ a + a' := fun t => (norm_sub_le _ _).trans (add_le_add (hr t)
    (hr' t))
  obtain ⟨hC1, hL1, hS1⟩ := LinvI_spec hp h (add_nonneg ha ha') hd
  obtain ⟨hC2, hL2, hS2⟩ := LinvI_spec hp h ha hr
  obtain ⟨hC3, hL3, hS3⟩ := LinvI_spec hp h ha' hr'
  have h0 : (fun t => LinvI p μ1 μ2 (fun t => r t - r' t) t -
      (LinvI p μ1 μ2 r t - LinvI p μ1 μ2 r' t)) = 0 := by
    refine inj_SI hp h (V := KI p μ1 μ2 * (a + a') + (KI p μ1 μ2 * a + KI p μ1 μ2 * a'))
      (fun t => (norm_sub_le _ _).trans
      (add_le_add (hC1 t) ((norm_sub_le _ _).trans (add_le_add (hC2 t) (hC3 t)))))
      (SI_sub hS1 (SI_sub hS2 hS3)) ?_
    rw [Lop_sub, hL1, Lop_sub, hL2, hL3]; funext t; simp
  funext t
  exact sub_eq_zero.1 (congrFun h0 t)

/-! ## The kernel direction and the shifted maps -/

/-- The right eigenvector of `μ₂`, normalised so that `ℓ(μ₂)·n₂ = 1`. -/
noncomputable def n2 (p : Par) (μ1 μ2 : ℝ) : Fin 2 → ℝ :=
  (1 / (Arot p 1 0 * (μ2 - μ1))) • ![μ2 - Arot p 1 1, Arot p 1 0]

/-- Woodford (2003), Proposition 4.3 (**the self-fulfilling direction**): the bounded kernel
element `k_t = μ₂^{−t}(n₂, ĉ = ŷ)` of the linearised operator in perfect foresight. -/
noncomputable def kI (p : Par) (μ1 μ2 : ℝ) (t : ℕ) : Fin 3 → ℝ :=
  (μ2⁻¹ ^ t) • ![n2 p μ1 μ2 0, n2 p μ1 μ2 1, n2 p μ1 μ2 0]

/-- `A n₂ = μ₂ n₂` and `ℓ(μ₂)·n₂ = 1`. -/
theorem n2_props {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2) :
    (Arot p).mulVec (n2 p μ1 μ2) = μ2 • n2 p μ1 μ2 ∧ ell (Arot p) μ2 (n2 p μ1 μ2) = 1 := by
  obtain ⟨h10, h11, h21, -, hc2, hsum, hA⟩ := h
  have hd' : μ2 - μ1 ≠ 0 := by linarith
  have hA' := hA.ne'
  simp only [tr2, det2] at hc2 hsum
  refine ⟨?_, ?_⟩
  · unfold n2
    rw [Matrix.mulVec_smul, smul_comm]
    congr 1
    funext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.zero_eta,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
      linear_combination -hc2
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
      ring
  · unfold n2 ell
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    linear_combination hsum

/-- Woodford (2003), Proposition 4.3: `k` is in the kernel of the linearised operator. -/
theorem Lop_kI (hp : p.Basic) {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2) :
    Lop p shiftOp (kI p μ1 μ2) = 0 := by
  have hμ2 : μ2 ≠ 0 := by obtain ⟨-, -, h21, -⟩ := h; linarith
  set u : ℕ → Fin 2 → ℝ := fun t => (μ2⁻¹ ^ t) • n2 p μ1 μ2 with hu
  have hrec : ∀ t, u t = (Arot p).mulVec (Mv shiftOp u t) +
      bR p (fun _ : ℕ => (0 : Fin 3 → ℝ)) t := fun t => by
    have hb0 : bR p (fun _ : ℕ => (0 : Fin 3 → ℝ)) t = 0 := by
      funext i; fin_cases i <;> simp [bR, gR0, gR1]
    have hM : Mv shiftOp u t = u (t + 1) := rfl
    rw [hb0, add_zero, hM, hu, Matrix.mulVec_smul, (n2_props h).1, smul_smul, pow_succ,
      mul_assoc, inv_mul_cancel₀ hμ2, mul_one]
  have hL := Lop_block hp shiftOp (fun _ => 0) u hrec
  have e : (fun t => ![u t 0 - (fun _ : ℕ => (0 : Fin 3 → ℝ)) t 2, u t 1, u t 0]) =
      kI p μ1 μ2 := by
    funext t i
    fin_cases i <;> simp [hu, kI]
  rw [← e, hL]; rfl

/-- `‖k_t‖ ≤ ‖k₀‖`. -/
theorem norm_kI_le {μ1 μ2 : ℝ} (h : RootHyp (Arot p) μ1 μ2) (t : ℕ) :
    ‖kI p μ1 μ2 t‖ ≤ ‖kI p μ1 μ2 0‖ := by
  obtain ⟨-, -, h21, -⟩ := h
  have h0 : 0 ≤ μ2⁻¹ := by positivity
  have h1 : μ2⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h21.le
  unfold kI
  rw [norm_smul, norm_smul, pow_zero, norm_one, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg h0 t)]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ h0 h1)

/-- The maps shifted along the kernel direction: `Q̃(e, w) = Q(0, e + w)`. -/
noncomputable def Qs (p : Par) (q : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  Qmap p (0, q.1 + q.2)

/-- The shifted lead part `Ñ(e, w) = N(0, e + w)`. -/
noncomputable def Ns (p : Par) (q : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  Nmap p (0, q.1 + q.2)

/-- The shifted maps are `C^∞`. -/
theorem contDiff_Qs {n : WithTop ℕ∞} : ContDiff ℝ n (Qs p) :=
  contDiff_Qmap.comp (by fun_prop)

/-- The shifted lead part is `C^∞`. -/
theorem contDiff_Ns {n : WithTop ℕ∞} : ContDiff ℝ n (Ns p) :=
  contDiff_Nmap.comp (by fun_prop)

/-- The shifted maps vanish together at the steady state. -/
theorem Qs_Ns_zero : Qs p (0, 0) + Ns p (0, 0) = 0 := by
  simp only [Qs, Ns, add_zero]; exact steadyState_zero

/-- The shifted maps have the same linearisation in the policy. -/
theorem LG_Qs (M : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ)) (v : ℕ → Fin 3 → ℝ) :
    LG (Qs p) (Ns p) M v = Lop p M v := by
  have hq : ∀ w : Fin 3 → ℝ, fderiv ℝ (Qs p) (0, 0) (0, w) = DQ0 p w := fun w => by
    have hd := ((contDiff_Qs (p := p) (n := 1)).differentiable one_ne_zero (0, 0)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 3 → ℝ), t • w)) ((0 : Fin 3 → ℝ), w) 0 := by
      have := (hasDerivAt_const (0 : ℝ) (0 : Fin 3 → ℝ)).prodMk
        ((hasDerivAt_id (0 : ℝ)).smul_const w)
      simpa using this
    have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    refine hc.unique (hasDerivAt_pi.2 fun i => ?_)
    have := hasDerivAt_Qmap_line (p := p) w i
    simpa [Qs, Function.comp_def] using this
  have hn : ∀ w : Fin 3 → ℝ, fderiv ℝ (Ns p) (0, 0) (0, w) = DN0 p w := fun w => by
    have hd := ((contDiff_Ns (p := p) (n := 1)).differentiable one_ne_zero (0, 0)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 3 → ℝ), t • w)) ((0 : Fin 3 → ℝ), w) 0 := by
      have := (hasDerivAt_const (0 : ℝ) (0 : Fin 3 → ℝ)).prodMk
        ((hasDerivAt_id (0 : ℝ)).smul_const w)
      simpa using this
    have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    refine hc.unique (hasDerivAt_pi.2 fun i => ?_)
    have := hasDerivAt_Nmap_line (p := p) w i
    simpa [Ns, Function.comp_def] using this
  funext t
  simp only [LG, Lop, hq, hn]

/-! ## The continuum of equilibria -/

/-- Woodford (2003), Proposition 4.3 and Ch. 2 (self-fulfilling expectations), Rotemberg pricing
(**INDETERMINACY OF THE EXACT NONLINEAR MODEL WHEN THE TAYLOR PRINCIPLE FAILS**). If
`κ(φ_π − 1) + (1 − β)φ_y < 0`, then for every `ρ > 0` there are `c₀ > 0` and a family
`c ↦ z^c` (`|c| ≤ c₀`) of perfect-foresight paths with
* `‖z^c_t‖ ≤ ρ` at every date (bounded, inside the `ρ`-ball around the steady state);
* `Q(0, z^c_t) + N(0, z^c_{t+1}) = 0` at every date (the EXACT equilibrium conditions without
  disturbances);
* `c ↦ z^c` is injective (`ℓ(μ₂)·(ĉ^c₀, π^c₀) = c`): a continuum of distinct equilibria. -/
theorem indeterminacy_continuum (hp : p.Basic)
    (hT : p.κ * (p.φ - 1) + (1 - p.β) * p.φy < 0) :
    ∀ ρ > 0, ∃ c0 > 0, ∃ z : ℝ → ℕ → Fin 3 → ℝ,
      (∀ c, |c| ≤ c0 → (∀ t, ‖z c t‖ ≤ ρ) ∧
        ∀ t, Qmap p (0, z c t) + Nmap p (0, z c (t + 1)) = 0) ∧
      ∀ c c', |c| ≤ c0 → |c'| ≤ c0 → z c = z c' → c = c' := by
  obtain ⟨μ1, μ2, h10, h11, h21, hc1, hc2, hsum, hA⟩ := roots_of_fail hp hT
  have h : RootHyp (Arot p) μ1 μ2 := ⟨h10, h11, h21, hc1, hc2, hsum, hA⟩
  have hK := KI_pos hp h
  obtain ⟨r0, hr0, hex⟩ := newton_exist (contDiff_Qs (p := p) (n := 1))
    (contDiff_Ns (p := p) (n := 1)) Qs_Ns_zero hK
  intro ρ hρ
  set r := min r0 (ρ / 2) with hr
  have hr0' : 0 < r := lt_min hr0 (by linarith)
  obtain ⟨δ, hδ, hex1⟩ := hex r hr0' (min_le_left _ _)
  set kn := ‖kI p μ1 μ2 0‖ with hkn
  set c0 := min δ (ρ / 2) / (kn + 1) with hc0
  have hc00 : 0 < c0 := div_pos (lt_min hδ (by linarith)) (by positivity)
  have hcb : ∀ c, |c| ≤ c0 → |c| * kn ≤ min δ (ρ / 2) := fun c hc => by
    have h1 : |c| * kn ≤ c0 * (kn + 1) :=
      mul_le_mul hc (by linarith) (norm_nonneg _) hc00.le
    rwa [hc0, div_mul_cancel₀ _ (by positivity)] at h1
  have key : ∀ c, |c| ≤ c0 → ∃ w : ℕ → Fin 3 → ℝ, SI p μ2 w ∧ (∀ t, ‖w t‖ ≤ r) ∧
      PhiG (Qs p) (Ns p) shiftOp (fun t => c • kI p μ1 μ2 t) w = 0 := by
    intro c hc
    have he : ∀ t, ‖c • kI p μ1 μ2 t‖ ≤ δ := fun t => by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (norm_kI_le h t) (abs_nonneg c)).trans
        ((hcb c hc).trans (min_le_left _ _))
    refine hex1 ℕ shiftOp shiftOp_isMarkov (LinvI p μ1 μ2)
      (fun ρ a ha hρa => by
        obtain ⟨h1, h2, -⟩ := LinvI_spec hp h ha hρa
        exact ⟨h1, by rw [LG_Qs]; exact h2⟩)
      (fun ρ ρ' a a' ha ha' h1 h2 => LinvI_sub hp h ha ha' h1 h2) (SI p μ2)
      (fun v w hv hw D hD => by
        rw [LG_Qs]
        exact LinvI_left hp h (SI_sub hv hw) hD) _ he ?_ ?_ ?_
    · unfold SI; simp [ell]
    · intro z hz hzr
      exact SI_sub hz (LinvI_SI h _)
    · intro zs z hzs hlim
      unfold SI at *
      have h1 : Tendsto (fun k => ell (Arot p) μ2 ![zs k 0 2, zs k 0 1]) atTop
          (𝓝 (ell (Arot p) μ2 ![z 0 2, z 0 1])) := by
        have h2 := (continuous_apply 2).continuousAt.tendsto.comp (hlim 0)
        have h3 := (continuous_apply 1).continuousAt.tendsto.comp (hlim 0)
        unfold ell
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        exact (h2.const_mul _).add (h3.const_mul _)
      have h0 : (fun k => ell (Arot p) μ2 ![zs k 0 2, zs k 0 1]) = fun _ => 0 :=
        funext hzs
      rw [h0] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
  choose! W hW using key
  have hcoord : ∀ c, |c| ≤ c0 →
      ell (Arot p) μ2 ![(c • kI p μ1 μ2 0 + W c 0) 2, (c • kI p μ1 μ2 0 + W c 0) 1] = c := by
    intro c hc
    have h1 := (n2_props h).2
    have h2 : ell (Arot p) μ2 ![W c 0 2, W c 0 1] = 0 := (hW c hc).1
    simp only [ell, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2 ⊢
    simp only [kI, pow_zero, one_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination c * h1 + h2
  refine ⟨c0, hc00, fun c t => c • kI p μ1 μ2 t + W c t, fun c hc => ⟨fun t => ?_,
    fun t => ?_⟩, fun c c' hc hc' heq => ?_⟩
  · have h1 : ‖c • kI p μ1 μ2 t‖ ≤ ρ / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (norm_kI_le h t) (abs_nonneg c)).trans
        ((hcb c hc).trans (min_le_right _ _))
    have h2 : ‖W c t‖ ≤ ρ / 2 := ((hW c hc).2.1 t).trans (min_le_right _ _)
    calc _ ≤ ‖c • kI p μ1 μ2 t‖ + ‖W c t‖ := norm_add_le _ _
      _ ≤ ρ / 2 + ρ / 2 := add_le_add h1 h2
      _ = ρ := by ring
  · exact congrFun (hW c hc).2.2 t
  · have e1 := hcoord c hc
    have e2 := hcoord c' hc'
    have e3 : (c • kI p μ1 μ2 0 + W c 0) = (c' • kI p μ1 μ2 0 + W c' 0) := congrFun heq 0
    rw [e3] at e1
    rw [← e1, e2]

/-- Woodford (2003), Proposition 4.3 and Ch. 2 (self-fulfilling expectations), Rotemberg pricing
(**SUNSPOT EQUILIBRIA OF THE EXACT MODEL**). If `κ(φ_π − 1) + (1 − β)φ_y < 0`, for every `ρ > 0`
there are `c₀ > 0` and an injective family `c ↦ z^c` of paths within `ρ` of the steady state
such that, on EVERY expectation system, for every sunspot variable `c(ω)` with `|c| ≤ c₀` that is
known at date `0` (`E_0[h(c)] = h(c)` for every `h`), the process `z_t(ω) = z^{c(ω)}_t` solves the
exact stochastic equilibrium conditions without fundamental disturbances. -/
theorem sunspot_equilibria (hp : p.Basic) (hT : p.κ * (p.φ - 1) + (1 - p.β) * p.φy < 0) :
    ∀ ρ > 0, ∃ c0 > 0, ∃ z : ℝ → ℕ → Fin 3 → ℝ,
      (∀ c, |c| ≤ c0 → ∀ t, ‖z c t‖ ≤ ρ) ∧
      (∀ c c', |c| ≤ c0 → |c'| ≤ c0 → z c = z c' → c = c') ∧
      ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (cs : Ω → ℝ), (∀ ω, |cs ω| ≤ c0) →
        (∀ h : ℝ → ℝ, 𝔼.E 0 (fun ω => h (cs ω)) = fun ω => h (cs ω)) →
        SeqEqm p 𝔼 (fun _ _ => 0) (fun t ω => z (cs ω) t) := by
  intro ρ hρ
  obtain ⟨c0, hc0, z, hz, hinj⟩ := indeterminacy_continuum hp hT ρ hρ
  refine ⟨c0, hc0, z, fun c hc => (hz c hc).1, hinj, fun Ω 𝔼 cs hcs hknown t ω => ?_⟩
  have hE : ∀ i : Fin 3, 𝔼.E t (fun ω' => Nmap p (0, z (cs ω') (t + 1)) i) =
      fun ω' => Nmap p (0, z (cs ω') (t + 1)) i := fun i => by
    have h0 := hknown (fun c => Nmap p (0, z c (t + 1)) i)
    rw [← h0, 𝔼.known (Nat.zero_le t)]
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [hE i]
  exact congrFun ((hz (cs ω) (hcs ω)).2 t) i

/-- Woodford (2003), Proposition 4.3 (**indeterminacy on every expectation system**): the
deterministic members of the family (`c` constant) are equilibria of every expectation system,
in particular of every finite event tree and every Markov chain. -/
theorem indeterminacy_every_system (hp : p.Basic)
    (hT : p.κ * (p.φ - 1) + (1 - p.β) * p.φy < 0) :
    ∀ ρ > 0, ∃ c0 > 0, ∃ z : ℝ → ℕ → Fin 3 → ℝ,
      (∀ c, |c| ≤ c0 → ∀ t, ‖z c t‖ ≤ ρ) ∧
      (∀ c c', |c| ≤ c0 → |c'| ≤ c0 → z c = z c' → c = c') ∧
      ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (c : ℝ), |c| ≤ c0 →
        SeqEqm p 𝔼 (fun _ _ => 0) (fun t _ => z c t) := by
  intro ρ hρ
  obtain ⟨c0, hc0, z, hz, hinj, hs⟩ := sunspot_equilibria hp hT ρ hρ
  exact ⟨c0, hc0, z, hz, hinj, fun Ω 𝔼 c hc =>
    hs Ω 𝔼 (fun _ => c) (fun _ => hc) (fun h => 𝔼.const 0 (h c))⟩

/-- Woodford (2003), p. 633: on an informationally closed system (every finite event tree,
`NonlinearNKMarkovAdapted.finiteTree_infoClosed`) a sunspot constant on the date-`0` information
cells is known at date `0` in the sense of `sunspot_equilibria`. -/
theorem known_of_cellConst {Ω : Type*} {𝔼 : ExpectationSystem Ω}
    (hcl : NonlinearNKMarkovAdapted.InfoClosed 𝔼) {cs : Ω → ℝ}
    (hc : NonlinearNKMarkovAdapted.CellConst 𝔼 0 cs) (h : ℝ → ℝ) :
    𝔼.E 0 (fun ω => h (cs ω)) = fun ω => h (cs ω) :=
  hcl 0 _ fun ω ω' hi => by simp only [hc ω ω' hi]

end Woodford.StabilizationWelfare.NonlinearRotembergIndet
