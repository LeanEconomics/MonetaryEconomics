/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR5Lyapunov
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Existence of forward solutions of the E-stability equation (2.20)

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, pp. 264–266: E-stability of an s.c.e.
`θ̄` is defined through the local stability of the rest point `θ̄` of `θ̇ = T(θ) − θ` (2.20).
Instability of a rest point is a statement that some solutions starting close to `θ̄` move away
from it, so it needs solutions to exist. This module supplies the existence theory.

* `IsSolOn`: a solution of (2.20) on a finite interval `[0, t₁]` (continuous there, with right
  derivatives `T(θ(τ)) − θ(τ)` on `[0, t₁)`); `isSolOn_of_isFwdSol`.
* `FwdComplete`: from every initial belief there is a forward solution on `[0, ∞)`.
* `exists_step`: Picard–Lindelöf (Mathlib's `IsPicardLindelof`) for a globally Lipschitz `T`
  gives a solution on `[0, h]` from every initial point with one step length `h = 1/(K + 2)`;
  **`fwdComplete_of_lipschitz`**: concatenating the steps (continuation) gives a forward solution
  on all of `[0, ∞)`.
* `glue`, `isFwdSol_glue`: a solution on `[0, s]` followed by a forward solution started at its
  end point is a forward solution; `isFwdSol_shift`: time shifts of forward solutions.
* `clampBox`, `tMod`: a map Lipschitz on the closed ball `‖θ − θ̄‖ ≤ r` agrees there with the
  globally Lipschitz map `T ∘ clampBox` (coordinatewise clamping onto the ball, which is a box in
  the sup norm); `eventuallyEq_tMod`: the two maps agree near `θ̄`, so they have the same
  derivative at `θ̄`.
* `exists_first_exit`: a continuous path that reaches distance `ε` from `θ̄` has a first time
  of doing so; `isSolOn_of_isFwdSol_tMod`, `isSolOn_tMod_of_isSolOn`: before that time the
  solutions of `T` and of `T ∘ clampBox` coincide.
-/

namespace Woodford.NeoWicksellianFramework.TidyR6ODEExistence

open Filter Topology TidyR5Lyapunov
open scoped NNReal

variable {ι : Type*}

/-! ### Solutions on finite intervals and on `[0, ∞)` -/

/-- Woodford (2003), (2.20) p. 265: `θ` solves `θ̇ = T(θ) − θ` on the finite interval
`[0, t₁]`: continuous there, with right derivative `T(θ(τ)) − θ(τ)` at every `τ ∈ [0, t₁)`. -/
def IsSolOn (T : (ι → ℝ) → ι → ℝ) (θ : ℝ → ι → ℝ) (t₁ : ℝ) : Prop :=
  ContinuousOn θ (Set.Icc 0 t₁) ∧
    ∀ τ ∈ Set.Ico 0 t₁, HasDerivWithinAt θ (T (θ τ) - θ τ) (Set.Ici τ) τ

/-- Woodford (2003), (2.20) p. 265: equation (2.20) is **forward complete**: from every initial
belief there is a forward solution on all of `[0, ∞)`. -/
def FwdComplete (T : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, ∃ θ, IsFwdSol T θ ∧ θ 0 = x

/-- Woodford (2003), (2.20): a forward solution restricted to `[0, t₁]` is a solution there. -/
theorem isSolOn_of_isFwdSol {T : (ι → ℝ) → ι → ℝ} {θ : ℝ → ι → ℝ} (h : IsFwdSol T θ)
    (t₁ : ℝ) : IsSolOn T θ t₁ :=
  ⟨h.1.mono Set.Icc_subset_Ici_self, fun τ hτ => h.2 τ hτ.1⟩

set_option linter.unusedFintypeInType false in
/-- Woodford (2003), (2.20): a time shift `τ ↦ θ(s + τ)`, `s ≥ 0`, of a forward solution is a
forward solution (the equation is autonomous). -/
theorem isFwdSol_shift [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {θ : ℝ → ι → ℝ} (h : IsFwdSol T θ) {s : ℝ}
    (hs : 0 ≤ s) : IsFwdSol T (fun τ => θ (s + τ)) := by
  have hmap : ∀ τ : ℝ, Set.MapsTo (fun u => s + u) (Set.Ici τ) (Set.Ici (s + τ)) :=
    fun τ u hu => by simp only [Set.mem_Ici] at hu ⊢; linarith
  refine ⟨?_, fun τ hτ => ?_⟩
  · exact h.1.comp (continuous_const.add continuous_id).continuousOn
      (fun u hu => by simp only [Set.mem_Ici] at hu ⊢; linarith)
  · have h1 := (h.2 (s + τ) (by linarith)).scomp τ
      ((hasDerivWithinAt_id τ (Set.Ici τ)).const_add s) (hmap τ)
    simpa [Function.comp_def] using h1

/-- Woodford (2003), (2.20): concatenation of a path `θ₁` on `[0, s]` with a path `θ₂` started
at time `s`. -/
noncomputable def glue (θ₁ θ₂ : ℝ → ι → ℝ) (s : ℝ) : ℝ → ι → ℝ :=
  fun t => if t ≤ s then θ₁ t else θ₂ (t - s)

set_option linter.unusedFintypeInType false in
/-- Woodford (2003), (2.20): **concatenation**: a solution on `[0, s]` followed by a forward
solution started at its end point is a forward solution. -/
theorem isFwdSol_glue [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {θ₁ θ₂ : ℝ → ι → ℝ} {s : ℝ}
    (h₁ : IsSolOn T θ₁ s) (h₂ : IsFwdSol T θ₂) (h0 : θ₂ 0 = θ₁ s) :
    IsFwdSol T (glue θ₁ θ₂ s) := by
  have e1 : ∀ t, t ≤ s → glue θ₁ θ₂ s t = θ₁ t := fun t ht => by simp [glue, ht]
  have e2 : ∀ t, s ≤ t → glue θ₁ θ₂ s t = θ₂ (t - s) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · subst h
      simp [glue, h0]
    · simp [glue, not_le.mpr h]
  have hsh : ∀ τ, s ≤ τ → HasDerivWithinAt (fun t => θ₂ (t - s))
      (T (θ₂ (τ - s)) - θ₂ (τ - s)) (Set.Ici τ) τ := by
    intro τ hτ
    have hmap : Set.MapsTo (fun u => u - s) (Set.Ici τ) (Set.Ici (τ - s)) :=
      fun u hu => by simp only [Set.mem_Ici] at hu ⊢; linarith
    have h1 := (h₂.2 (τ - s) (by linarith)).scomp τ
      ((hasDerivWithinAt_id τ (Set.Ici τ)).sub_const s) hmap
    simpa [Function.comp_def] using h1
  refine ⟨?_, fun τ hτ => ?_⟩
  · have hU : Set.Ici (0 : ℝ) ⊆ Set.Icc 0 s ∪ Set.Ici s := by
      intro t ht
      rcases le_total t s with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    refine ContinuousOn.mono (ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Ici) hU
    · exact h₁.1.congr fun t ht => e1 t ht.2
    · refine ContinuousOn.congr ?_ fun t ht => e2 t ht
      exact h₂.1.comp (continuous_id.sub continuous_const).continuousOn
        (fun u hu => by simp only [Set.mem_Ici] at hu ⊢; linarith)
  · rcases lt_or_ge τ s with hlt | hge
    · have hd := h₁.2 τ ⟨hτ, hlt⟩
      rw [← e1 τ hlt.le] at hd
      refine hd.congr_of_eventuallyEq ?_ (e1 τ hlt.le)
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with t ht
      exact e1 t (le_of_lt ht)
    · have hd := hsh τ hge
      rw [← e2 τ hge] at hd
      exact hd.congr (fun t ht => e2 t (le_trans hge ht)) (e2 τ hge)

/-! ### Global existence for a globally Lipschitz `T` -/

/-- Woodford (2003), (2.20): **one Picard–Lindelöf step**: if `T` is globally `K`-Lipschitz,
from every initial point there is a solution of (2.20) on `[0, 1/(K + 2)]`. -/
theorem exists_step [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {K : ℝ≥0} (hT : LipschitzWith K T)
    (x : ι → ℝ) :
    ∃ α : ℝ → ι → ℝ, α 0 = x ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / ((K : ℝ) + 2)),
      HasDerivWithinAt α (T (α t) - α t) (Set.Icc 0 (1 / ((K : ℝ) + 2))) t := by
  set F : (ι → ℝ) → ι → ℝ := fun y => T y - y with hF
  have hFL : LipschitzWith (K + 1) F := hT.sub LipschitzWith.id
  set h : ℝ := 1 / ((K : ℝ) + 2) with hh
  have hh0 : 0 ≤ h := by positivity
  set R : ℝ≥0 := ‖F x‖₊ + 1 with hR
  set L : ℝ≥0 := ‖F x‖₊ + (K + 1) * R with hL
  have hb : ∀ y ∈ Metric.closedBall x (R : ℝ), ‖F y‖ ≤ (L : ℝ) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have h1 : ‖F y - F x‖ ≤ ((K + 1 : ℝ≥0) : ℝ) * ‖y - x‖ := by
      have := hFL.dist_le_mul y x
      rwa [dist_eq_norm, dist_eq_norm] at this
    have h2 : ‖F y‖ ≤ ‖F x‖ + ‖F y - F x‖ := by
      calc ‖F y‖ = ‖F x + (F y - F x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖F x‖ + ‖F y - F x‖ := norm_add_le _ _
    simp only [hL, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, NNReal.coe_one] at h1 ⊢
    have hK0 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hy hK0]
  have hm : (L : ℝ) * max (h - ((⟨0, ⟨le_rfl, hh0⟩⟩ : Set.Icc (0 : ℝ) h) : ℝ))
      (((⟨0, ⟨le_rfl, hh0⟩⟩ : Set.Icc (0 : ℝ) h) : ℝ) - 0) ≤ (R : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    simp only [sub_zero, NNReal.coe_zero]
    rw [max_eq_left (by linarith [hh0])]
    have hK2 : (0 : ℝ) < (K : ℝ) + 2 := by positivity
    rw [hh, mul_one_div, div_le_iff₀ hK2]
    simp only [hL, hR, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, NNReal.coe_one]
    have hn : 0 ≤ ‖F x‖ := norm_nonneg _
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := K.2
    nlinarith
  have hPL : IsPicardLindelof (fun _ => F) (⟨0, ⟨le_rfl, hh0⟩⟩ : Set.Icc (0 : ℝ) h) x R 0 L
      (K + 1) :=
    IsPicardLindelof.of_time_independent hb (hFL.lipschitzOnWith) hm
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht => hα t ht⟩

/-- Woodford (2003), (2.20) p. 265: **global existence (continuation)**: if `T` is globally
Lipschitz, every initial belief has a forward solution of `θ̇ = T(θ) − θ` on `[0, ∞)`. The
Picard–Lindelöf steps of `exists_step` all have the same length `h`, so they can be concatenated:
`θ(t) = α_k(t − k h)` for `k h ≤ t ≤ (k + 1) h`, `α_{k+1}(0) = α_k(h)`. -/
theorem fwdComplete_of_lipschitz [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {K : ℝ≥0}
    (hT : LipschitzWith K T) :
    FwdComplete T := by
  intro x0
  set h : ℝ := 1 / ((K : ℝ) + 2) with hh
  have hh0 : 0 < h := by positivity
  choose sol hsol0 hsold using fun x => exists_step hT x
  set pts : ℕ → ι → ℝ := fun n => Nat.rec x0 (fun _ p => sol p h) n with hpts
  have hpts0 : pts 0 = x0 := rfl
  have hptsS : ∀ n, pts (n + 1) = sol (pts n) h := fun n => rfl
  set θ : ℝ → ι → ℝ := fun t => sol (pts ⌊t / h⌋₊) (t - ⌊t / h⌋₊ * h) with hθ
  set g : ℕ → ℝ → ι → ℝ := fun k t => sol (pts k) (t - k * h) with hg
  -- `θ` agrees with the `k`-th piece on `[k h, (k + 1) h]`
  have heq : ∀ k : ℕ, ∀ t ∈ Set.Icc ((k : ℝ) * h) ((k + 1) * h), θ t = g k t := by
    intro k t ht
    have ht0 : 0 ≤ t / h := div_nonneg (le_trans (by positivity) ht.1) hh0.le
    rcases eq_or_lt_of_le ht.2 with he | hlt
    · have hf : ⌊t / h⌋₊ = k + 1 := by
        rw [Nat.floor_eq_iff ht0, he, mul_div_assoc, div_self hh0.ne', mul_one]
        push_cast
        constructor <;> linarith
      change sol (pts ⌊t / h⌋₊) (t - ⌊t / h⌋₊ * h) = sol (pts k) (t - k * h)
      rw [hf, hptsS]
      push_cast
      rw [he, sub_self, hsol0]
      congr 1
      ring
    · have hf : ⌊t / h⌋₊ = k := by
        rw [Nat.floor_eq_iff ht0]
        constructor
        · rw [le_div_iff₀ hh0]
          exact ht.1
        · rw [div_lt_iff₀ hh0]
          exact hlt
      simp only [hθ, hg, hf]
  -- each piece solves the equation on its interval
  have hgd : ∀ k : ℕ, ∀ t ∈ Set.Icc ((k : ℝ) * h) ((k + 1) * h),
      HasDerivWithinAt (g k) (T (g k t) - g k t) (Set.Icc ((k : ℝ) * h) ((k + 1) * h)) t := by
    intro k t ht
    have hmap : Set.MapsTo (fun u => u - k * h) (Set.Icc ((k : ℝ) * h) ((k + 1) * h))
        (Set.Icc 0 h) := fun u hu => by
      simp only [Set.mem_Icc] at hu ⊢
      constructor <;> nlinarith
    have h1 := (hsold (pts k) (t - k * h) (hmap ht)).scomp t
      ((hasDerivWithinAt_id t _).sub_const ((k : ℝ) * h)) hmap
    simpa [Function.comp_def, hg] using h1
  have hfl : ∀ t : ℝ, 0 ≤ t → t ∈ Set.Icc ((⌊t / h⌋₊ : ℝ) * h) ((⌊t / h⌋₊ + 1) * h) ∧
      t < (⌊t / h⌋₊ + 1) * h := by
    intro t ht
    have ht0 : 0 ≤ t / h := div_nonneg ht hh0.le
    have h1 := Nat.floor_le ht0
    have h2 := Nat.lt_floor_add_one (t / h)
    rw [le_div_iff₀ hh0] at h1
    rw [div_lt_iff₀ hh0] at h2
    exact ⟨⟨h1, h2.le⟩, h2⟩
  refine ⟨θ, ⟨fun t ht => ?_, fun τ hτ => ?_⟩, ?_⟩
  · -- continuity
    have ht : 0 ≤ t := ht
    obtain ⟨hmem, hlt⟩ := hfl t ht
    set k := ⌊t / h⌋₊ with hk
    have hck : ContinuousWithinAt θ (Set.Icc ((k : ℝ) * h) ((k + 1) * h)) t :=
      ((hgd k t hmem).continuousWithinAt).congr (fun u hu => heq k u hu) (heq k t hmem)
    rcases eq_or_lt_of_le hmem.1 with he | hgt
    · -- `t = k h`
      rcases Nat.eq_zero_or_eq_succ_pred k with hk0 | hk1
      · have ht0 : t = 0 := by rw [← he, hk0]; simp
        rw [ht0] at hck ⊢
        refine hck.mono_of_mem_nhdsWithin ?_
        rw [hk0]
        simpa using Icc_mem_nhdsGE hh0
      · set j := k.pred with hj
        have hjk : (j : ℝ) + 1 = k := by rw [hk1]; push_cast; ring
        have hmem' : t ∈ Set.Icc ((j : ℝ) * h) ((j + 1) * h) := by
          rw [hjk, ← he]
          constructor <;> nlinarith
        have hcj : ContinuousWithinAt θ (Set.Icc ((j : ℝ) * h) ((j + 1) * h)) t :=
          ((hgd j t hmem').continuousWithinAt).congr (fun u hu => heq j u hu) (heq j t hmem')
        have hU := hcj.union hck
        refine (hU.continuousAt ?_).continuousWithinAt
        refine mem_of_superset (Icc_mem_nhds (a := (j : ℝ) * h) (b := ((k : ℝ) + 1) * h)
          ?_ ?_) ?_
        · rw [← he, ← hjk]; nlinarith
        · rw [← he]; nlinarith
        · intro u hu
          rcases le_total u t with h1 | h1
          · left
            exact ⟨hu.1, by rw [hjk]; linarith⟩
          · right
            exact ⟨by linarith, hu.2⟩
    · exact (hck.continuousAt (Icc_mem_nhds hgt hlt)).continuousWithinAt
  · -- right derivatives
    have hτ' : 0 ≤ τ := hτ
    obtain ⟨hmem, hlt⟩ := hfl τ hτ'
    set k := ⌊τ / h⌋₊ with hk
    have hsub : Set.Icc τ ((k + 1) * h) ⊆ Set.Icc ((k : ℝ) * h) ((k + 1) * h) :=
      Set.Icc_subset_Icc_left hmem.1
    have hd := ((hgd k τ hmem).mono hsub).congr (fun u hu => heq k u (hsub hu)) (heq k τ hmem)
    rw [← heq k τ hmem] at hd
    exact hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hlt)
  · simp only [hθ, zero_div, Nat.floor_zero, CharP.cast_eq_zero, zero_mul, sub_zero, hpts0]
    exact hsol0 x0

/-! ### Modification outside a ball -/

/-- Woodford (2003), (2.20): coordinatewise clamping onto the box `|θᵢ − θ̄ᵢ| ≤ r`, which is the
closed ball of radius `r` around `θ̄` in the sup norm. -/
def clampBox (θs : ι → ℝ) (r : ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => max (θs i - r) (min (θs i + r) (x i))

/-- Woodford (2003), (2.20): the map `T` modified outside the closed ball `‖θ − θ̄‖ ≤ r`,
`T ∘ clampBox`. -/
def tMod (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) (r : ℝ) (x : ι → ℝ) : ι → ℝ :=
  T (clampBox θs r x)

/-- Woodford (2003), (2.20): clamping lands in the closed ball of radius `r`. -/
theorem norm_clampBox_sub_le [Fintype ι] (θs : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) (x : ι → ℝ) :
    ‖clampBox θs r x - θs‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  simp only [clampBox, Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor
  · linarith [le_max_left (θs i - r) (min (θs i + r) (x i))]
  · have : max (θs i - r) (min (θs i + r) (x i)) ≤ θs i + r :=
      max_le (by linarith) (min_le_left _ _)
    linarith

/-- Woodford (2003), (2.20): clamping does not move points of the closed ball. -/
theorem clampBox_of_le [Fintype ι] (θs : ι → ℝ) {r : ℝ} {x : ι → ℝ} (hx : ‖x - θs‖ ≤ r) :
    clampBox θs r x = x := by
  funext i
  have hi : |x i - θs i| ≤ r := by
    have := norm_le_pi_norm (x - θs) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  rw [abs_le] at hi
  simp only [clampBox]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Woodford (2003), (2.20): clamping is `1`-Lipschitz (sup norm). -/
theorem lipschitzWith_clampBox [Fintype ι] (θs : ι → ℝ) (r : ℝ) :
    LipschitzWith 1 (clampBox θs r) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  simp only [clampBox, Real.dist_eq]
  have h1 := abs_max_sub_max_le_abs (min (θs i + r) (x i)) (min (θs i + r) (y i)) (θs i - r)
  have h2 := abs_min_sub_min_le_max (θs i + r) (x i) (θs i + r) (y i)
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h2
  rw [max_comm (θs i - r), max_comm (θs i - r)]
  exact h1.trans (h2.trans (by rw [← Real.dist_eq]; exact dist_le_pi_dist x y i))

/-- Woodford (2003), (2.20): if `T` is `K`-Lipschitz on the closed ball `‖θ − θ̄‖ ≤ r`, the
modified map `T ∘ clampBox` is globally `K`-Lipschitz. -/
theorem lipschitzWith_tMod [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ} {K : ℝ≥0}
    (hr : 0 ≤ r)
    (hT : LipschitzOnWith K T (Metric.closedBall θs r)) : LipschitzWith K (tMod T θs r) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hmem : ∀ z, clampBox θs r z ∈ Metric.closedBall θs r := fun z => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact norm_clampBox_sub_le θs hr z
  calc dist (tMod T θs r x) (tMod T θs r y)
      ≤ K * dist (clampBox θs r x) (clampBox θs r y) := hT.dist_le_mul _ (hmem x) _ (hmem y)
    _ ≤ K * dist x y := by
        gcongr
        simpa using (lipschitzWith_clampBox θs r).dist_le_mul x y

/-- Woodford (2003), (2.20): the modified map agrees with `T` on the closed ball. -/
theorem tMod_of_le [Fintype ι] (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) {r : ℝ} {x : ι → ℝ}
    (hx : ‖x - θs‖ ≤ r) : tMod T θs r x = T x := by
  simp only [tMod, clampBox_of_le θs hx]

set_option linter.unusedFintypeInType false in
/-- Woodford (2003), (2.20): for `r > 0` the modified map agrees with `T` near `θ̄`; in
particular it has the same rest point and the same derivative there. -/
theorem eventuallyEq_tMod [Fintype ι] (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    tMod T θs r =ᶠ[𝓝 θs] T := by
  filter_upwards [Metric.closedBall_mem_nhds θs hr] with x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  exact tMod_of_le T θs hx

/-- Woodford (2003), (2.20): if `T` is Lipschitz on a closed ball around `θ̄`, the modified
equation is forward complete. -/
theorem fwdComplete_tMod [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ} {K : ℝ≥0}
    (hr : 0 ≤ r) (hT : LipschitzOnWith K T (Metric.closedBall θs r)) :
    FwdComplete (tMod T θs r) :=
  fwdComplete_of_lipschitz (lipschitzWith_tMod hr hT)

/-! ### First exit times -/

/-- Woodford (2003), (2.20): **first exit**: if a path continuous on `[0, τ]` is at distance at
least `ε` from `θ̄` at time `τ`, there is a first time `s ≤ τ` at which it is, and before `s` it
stays at distance less than `ε`. -/
theorem exists_first_exit [Fintype ι] {θ : ℝ → ι → ℝ} {θs : ι → ℝ} {ε τ : ℝ} (hτ : 0 ≤ τ)
    (hc : ContinuousOn θ (Set.Icc 0 τ)) (hex : ε ≤ ‖θ τ - θs‖) :
    ∃ s, 0 ≤ s ∧ s ≤ τ ∧ ε ≤ ‖θ s - θs‖ ∧ ∀ t ∈ Set.Ico 0 s, ‖θ t - θs‖ < ε := by
  set S := Set.Icc 0 τ ∩ θ ⁻¹' {x | ε ≤ ‖x - θs‖} with hS
  have hcl : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hne : S.Nonempty := ⟨τ, ⟨hτ, le_rfl⟩, hex⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have hmem := hcl.csInf_mem hne hbdd
  refine ⟨sInf S, hmem.1.1, hmem.1.2, hmem.2, fun t ht => ?_⟩
  by_contra hcon
  push Not at hcon
  have htS : t ∈ S := ⟨⟨ht.1, le_trans ht.2.le hmem.1.2⟩, hcon⟩
  exact absurd (csInf_le hbdd htS) (not_le.mpr ht.2)

/-- Woodford (2003), (2.20): a forward solution of the modified equation that stays in the
closed ball before time `s` solves the original equation on `[0, s]`. -/
theorem isSolOn_of_isFwdSol_tMod [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r s : ℝ}
    {θ : ℝ → ι → ℝ} (h : IsFwdSol (tMod T θs r) θ) (hin : ∀ t ∈ Set.Ico 0 s, ‖θ t - θs‖ ≤ r) :
    IsSolOn T θ s := by
  refine ⟨h.1.mono Set.Icc_subset_Ici_self, fun τ hτ => ?_⟩
  have hd := h.2 τ hτ.1
  rwa [tMod_of_le T θs (hin τ hτ)] at hd

/-- Woodford (2003), (2.20): a solution of the original equation on `[0, s]` that stays in the
closed ball before time `s` solves the modified equation there. -/
theorem isSolOn_tMod_of_isSolOn [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r s : ℝ}
    {θ : ℝ → ι → ℝ} (h : IsSolOn T θ s) (hin : ∀ t ∈ Set.Ico 0 s, ‖θ t - θs‖ ≤ r) :
    IsSolOn (tMod T θs r) θ s := by
  refine ⟨h.1, fun τ hτ => ?_⟩
  rw [tMod_of_le T θs (hin τ hτ)]
  exact h.2 τ hτ

end Woodford.NeoWicksellianFramework.TidyR6ODEExistence
