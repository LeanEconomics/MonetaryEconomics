/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aExpand
import StabilizationWelfare.TidyR5CommitLQ
import StabilizationWelfare.TidyR5RamseyDate0

/-!
# The isoelastic Ramsey model and the Calvo model of §5; the first-order component is the
# footnote-71 plan

Woodford (2003), *Interest and Prices*, Chapter 6, §5, pp. 455–463 (the exact Calvo model of
Benigno–Woodford, (5.4)–(5.11)), §3.2, pp. 414–415, §4.5, footnote 71, and Chapter 7, §1
(optimal commitment from a timeless perspective).

The Ramsey conditions of NonlinearNKMarkovRamsey live on an event tree (`LagTree`); the Calvo
model of §5 (`LargeDistortions.CalvoModel.CalvoAS`) and the footnote-71 plan
(`TidyR5CommitLQ.fnX`, `fnPi`) are stated for processes on an `ExpectationSystem`. Here:

* `TreePath`: a path representation of an event tree in an expectation system (`nd t ω` the
  date-`t` node of state `ω`, with `E_t f(nd_{t+1}) = (Mf)(nd_t)`); `natPath` (the deterministic
  time line under perfect foresight).
* **`calvoAS_of_ramsey`**: the constraint block of ANY solution of the exact Ramsey conditions is
  EXACTLY the Calvo model of §5 with `s_C = 1`, `G = 0` and the disturbances
  `(ĉ, τ̂, q, μ̂ʷ)`: the bridge between the isoelastic Ramsey model and LargeDistortions.
* **`fn71_unique`**: the footnote-71 plan is the UNIQUE bounded solution of the AS relation and
  the targeting rule `π = −φ(x − x₋)` with given `x_{−1}` (the converse of
  `TidyR5CommitLQ.fn71_AS`).
* **`first_order_is_fn71`**: along any path, the solution `z₁` of the linearised Ramsey system with
  the disturbance forcing has `π₁ = fnPi`, `ŷ₁ − Ŷ*₁ = fnX` with `φ = λ̃/κ = 1/θ`, `x_{−1} = 0`
  and the cost-push term `u = κ(Ŷ* − Ŷⁿ)` (`TidyR6aShock.u1`), for EVERY distortion `Φ`.
* **`timeless_first_order`**: for every `A_u > 0` and `Φ ∈ [0, 1]` the exact timeless Ramsey plan
  with disturbances `εê` and `|Δ_{−1} − 1| ≤ ε²` exists, is locally unique and equals
  `w̄ + εz₁ + O(ε²)` uniformly; **`date0_eq_timeless`**: for `Φ = 0` the date-0 plan is the
  timeless plan.
* **`date0_far`** (the correct statement for `Φ ≠ 0`): the date-0 conditions are violated at
  every root node whose value is within `ρ(Φ) > 0` of the steady state, whatever the
  disturbances and `Δ_{−1}`; so for `Φ > 0` the date-0 plan is NOT `w̄ + O(ε)` and its
  first-order component around the steady state is not defined. The footnote-71 plan is the
  first-order component of the TIMELESS plan (which keeps `W₀` fixed, as Proposition 6.15 and
  `TidyR5RamseySOC.lq_sufficiency615` require).
-/

namespace Woodford.StabilizationWelfare.TidyR6aBridge

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT TidyR6aShock TidyR6aExpand
open TidyR5CommitLQ TidyR5RamseyDate0 Sequences

variable {Ω Y : Type*} (𝔼 : ExpectationSystem Ω) (T : LagTree Y)

/-- Woodford (2003), Ch. 7 and App. A.3 (**a path representation of an event tree**): `nd t ω`
is the date-`t` node in state `ω`; the date of `nd t ω` is `t`, its parent is `nd (t−1) ω`,
values at `nd t` are known at `t`, and the conditional expectation of a function of the next
node is the tree's expectation operator. -/
structure TreePath where
  /-- The date-`t` node in state `ω`. -/
  nd : ℕ → Ω → Y
  /-- The node of date `t` has depth `t`. -/
  depth_nd : ∀ t ω, T.depth (nd t ω) = t
  /-- The parent of the date-`(t+1)` node is the date-`t` node. -/
  par_nd : ∀ t ω, T.par (nd (t + 1) ω) = nd t ω
  /-- Expectations of next-period node values follow the tree. -/
  E_next : ∀ t (f : Y → ℝ), 𝔼.E t (fun ω => f (nd (t + 1) ω)) = fun ω => T.M f (nd t ω)
  /-- Current node values are known. -/
  E_now : ∀ t (f : Y → ℝ), 𝔼.E t (fun ω => f (nd t ω)) = fun ω => f (nd t ω)

/-- Woodford (2003), pp. 414–415: the deterministic time line under perfect foresight is a path
of `TidyR5RamseyDate0.natTree`. -/
def natPath : TreePath perfectForesight natTree where
  nd t _ := t
  depth_nd _ _ := rfl
  par_nd _ _ := rfl
  E_next _ _ := rfl
  E_now _ _ := rfl

variable {𝔼 T}

/-- Woodford (2003), Ch. 7: along a path, the tree lag (zero at the roots) is the process lag
with zero initial value. -/
theorem lag0_nd (P : TreePath 𝔼 T) (g : Y → ℝ) (t : ℕ) (ω : Ω) :
    lag0 T g (P.nd t ω) = lagP (fun _ => 0) (fun s ω' => g (P.nd s ω')) t ω := by
  cases t with
  | zero => simp [lag0, lagP, P.depth_nd]
  | succ t => simp [lag0, lagP, P.depth_nd, P.par_nd]

/-- Woodford (2003), §5: the expectation of a function of the next node, minus a constant. -/
theorem E_next_sub (P : TreePath 𝔼 T) (t : ℕ) (f : Y → ℝ) (c : ℝ) :
    𝔼.E t (fun ω => f (P.nd (t + 1) ω) - c) = fun ω => T.M f (P.nd t ω) - c := by
  have e : (fun ω => f (P.nd (t + 1) ω) - c) = (fun ω => f (P.nd (t + 1) ω)) - fun _ => c := rfl
  rw [e, map_sub, P.E_next, 𝔼.const]
  rfl

/-- **Woodford (2003), §5, pp. 457–458 (the isoelastic Ramsey model IS the Calvo model of §5).**
Along any path of an event tree, every solution of the exact Ramsey conditions (any distortion,
any root lag) gives processes `π_t = w₁`, `x_t = (K̂ − F̂)/(1+ωθ)`, `F̂ = w₂`, `K̂ = w₃`, `Ŷ = w₀`,
`f̂ = (1−σ)Ŷ + σĉ + τ̂`, `k̂ = (1+ω)Ŷ − ωq + μ̂ʷ` that satisfy EXACTLY
`LargeDistortions.CalvoModel.CalvoAS` with `s_C = 1`, `G = 0` and the disturbances
`(ĉ, q, μ̂ʷ, τ̂) = (e₁, e₃, e₄, e₂)`. -/
theorem calvoAS_of_ramsey {p : Par} (hp : p.Std) (P : TreePath 𝔼 T) (R : RPar)
    (e : Y → Fin 5 → ℝ) (lag : Fin 9 → ℝ) (w : Y → Fin 9 → ℝ) (hw : RamseyL T p R e lag w) :
    LargeDistortions.CalvoModel.CalvoAS 𝔼 p.α p.β p.θ p.ω p.σ 1
      (fun t ω => w (P.nd t ω) 1) (fun t ω => (w (P.nd t ω) 3 - w (P.nd t ω) 2) / p.c0)
      (fun t ω => w (P.nd t ω) 2) (fun t ω => w (P.nd t ω) 3)
      (fun t ω => (1 - p.σ) * w (P.nd t ω) 0 + p.σ * e (P.nd t ω) 1 + e (P.nd t ω) 2)
      (fun t ω => (1 + p.ω) * w (P.nd t ω) 0 - p.ω * e (P.nd t ω) 3 + e (P.nd t ω) 4)
      (fun t ω => w (P.nd t ω) 0) (fun _ _ => 0) (fun t ω => e (P.nd t ω) 1)
      (fun t ω => e (P.nd t ω) 3) (fun t ω => e (P.nd t ω) 4) (fun t ω => e (P.nd t ω) 2) where
  priceIndex := by
    intro t ω
    have h := congrFun (hw (P.nd t ω)) 7
    have hM : Mv T.M (fun y => ramseyN p (w y)) (P.nd t ω) 7 = 0 := by
      change T.M (fun y => ramseyN p (w y) 7) (P.nd t ω) = 0
      have e0 : (fun y => ramseyN p (w y) 7) = fun _ => (0 : ℝ) := by
        funext y; simp [ramseyN]
      rw [e0, M_const T]
    simp only [Pi.add_apply, Pi.zero_apply, hM, add_zero, ramseyQ, Matrix.cons_val] at h
    exact h
  resetPrice := by
    intro t ω
    have hc0 := hp.c0_pos.ne'
    change p.c0 * ((w (P.nd t ω) 3 - w (P.nd t ω) 2) / p.c0) = _
    field_simp
  recF := by
    intro t
    rw [E_next_sub P t (fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2)) 1]
    funext ω
    have h := congrFun (hw (P.nd t ω)) 5
    have hM : Mv T.M (fun y => ramseyN p (w y)) (P.nd t ω) 5 =
        -(p.α * p.β) * T.M (fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2)) (P.nd t ω) := by
      change T.M (fun y => ramseyN p (w y) 5) (P.nd t ω) = _
      have e0 : (fun y => ramseyN p (w y) 5) =
          (-(p.α * p.β)) • fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2) := by
        funext y; simp only [ramseyN, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]; ring
      rw [e0, map_smul]; rfl
    simp only [Pi.add_apply, Pi.zero_apply, hM, ramseyQ, Matrix.cons_val] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h
  recK := by
    intro t
    rw [E_next_sub P t (fun y => Real.exp (p.θ * (1 + p.ω) * w y 1 + w y 3)) 1]
    funext ω
    have h := congrFun (hw (P.nd t ω)) 6
    have hM : Mv T.M (fun y => ramseyN p (w y)) (P.nd t ω) 6 =
        -(p.α * p.β) * T.M (fun y => Real.exp (p.θ * (1 + p.ω) * w y 1 + w y 3)) (P.nd t ω) := by
      change T.M (fun y => ramseyN p (w y) 6) (P.nd t ω) = _
      have e0 : (fun y => ramseyN p (w y) 6) =
          (-(p.α * p.β)) • fun y => Real.exp (p.θ * (1 + p.ω) * w y 1 + w y 3) := by
        funext y; simp only [ramseyN, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, aE]; ring
      rw [e0, map_smul]; rfl
    simp only [Pi.add_apply, Pi.zero_apply, hM, ramseyQ, Matrix.cons_val, aE] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h
  costK := fun t ω => by ring
  revF := fun t ω => by
    simp only [LargeDistortions.fhatIso, sub_self, sub_zero, div_one, Real.log_exp]
    ring

/-! ## The footnote-71 plan is the unique solution of the commitment system -/

/-- **Woodford (2003), footnote 71 and Ch. 7, §1 (uniqueness of the commitment plan).** For
`0 < β < 1`, `κ, φ > 0` and a bounded adapted cost-push process `u`, if processes `π, x`
(`x` bounded and adapted) satisfy the AS relation `π_t = κx_t + βE_tπ_{t+1} + u_t` and the
targeting rule `π_t = −φ(x_t − x_{t−1})` with given `x_{−1}`, then `x = fnX` and `π = fnPi`. -/
theorem fn71_unique {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (xm1 : ℝ)
    {π x : ℕ → Ω → ℝ} (hxb : BoundedProc x) (hxa : 𝔼.Adapted x)
    (hAS : NKPCu 𝔼 κ β u π x)
    (hT : ∀ t ω, π t ω = -(φ * (x t ω - lagP (fun _ => xm1) x t ω))) :
    x = fnX 𝔼 β κ φ u xm1 ∧ π = fnPi 𝔼 β κ φ u xm1 := by
  obtain ⟨hz0, hz1, hzq⟩ := zRoot_props hβ0 hβ1 (div_pos hκ hφ)
  set z := zRoot β (κ / φ) with hz
  have hAS' := fn71_AS 𝔼 hβ0 hβ1 hκ hφ hu hua xm1
  obtain ⟨⟨BX, hBX⟩, hXa⟩ := fnX_props 𝔼 hβ0 hβ1 hκ hφ hu hua xm1
  set X := fnX 𝔼 β κ φ u xm1 with hX
  set Pp := fnPi 𝔼 β κ φ u xm1 with hPp
  obtain ⟨Bx, hBx⟩ := hxb
  obtain ⟨d, hd⟩ : ∃ d : ℕ → Ω → ℝ, d = fun t ω => x t ω - X t ω := ⟨_, rfl⟩
  have hdx : ∀ t ω, x t ω = X t ω + d t ω := fun t ω => by rw [hd]; ring
  have hlag : ∀ t ω, lagP (fun _ => xm1) x t ω - lagP (fun _ => xm1) X t ω =
      lagP (fun _ => 0) d t ω := fun t ω => by cases t <;> simp [lagP, hd]
  have hdπ : ∀ t ω, π t ω - Pp t ω = -(φ * (d t ω - lagP (fun _ => 0) d t ω)) := fun t ω => by
    rw [hT t ω, hPp]
    simp only [fnPi]
    rw [← hlag t ω, hdx t ω]
    rw [← hX]
    ring
  have hdE : ∀ t, 𝔼.E t (d t) = d t := fun t => by
    have e : d t = x t - X t := by rw [hd]; rfl
    rw [e, map_sub, hxa t, hXa t]
  -- the homogeneous second-order equation
  have hrec : ∀ t ω, β * 𝔼.E t (d (t + 1)) ω =
      (1 + β + κ / φ) * d t ω - lagP (fun _ => 0) d t ω := by
    intro t ω
    have k1 := congrFun (hAS t) ω
    have k2 := congrFun (hAS' t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at k1 k2
    have hE1 : 𝔼.E t (π (t + 1)) ω - 𝔼.E t (Pp (t + 1)) ω =
        -φ * 𝔼.E t (d (t + 1)) ω + φ * d t ω := by
      have e : π (t + 1) - Pp (t + 1) = (-φ) • d (t + 1) + φ • d t := by
        funext ω'
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hdπ (t + 1) ω']
        simp only [lagP]
        ring
      have := congrFun (congrArg (𝔼.E t) e) ω
      rw [map_sub, map_add, map_smul, map_smul, hdE t] at this
      simpa using this
    have k3 := hdπ t ω
    have hxd := hdx t ω
    have hφ0 := hφ.ne'
    have key : β * φ * 𝔼.E t (d (t + 1)) ω =
        (φ + β * φ + κ) * d t ω - φ * lagP (fun _ => 0) d t ω := by
      linear_combination k1 - k2 - k3 + κ * hxd + β * hE1
    have hinv : φ * φ⁻¹ = 1 := mul_inv_cancel₀ hφ0
    refine mul_left_cancel₀ hφ0 ?_
    rw [div_eq_mul_inv]
    linear_combination key - κ * d t ω * hinv
  -- the forward factor
  obtain ⟨v, hv⟩ : ∃ v : ℕ → Ω → ℝ, v = fun t ω => d t ω - z * lagP (fun _ => 0) d t ω :=
    ⟨_, rfl⟩
  have hvrec : ∀ t, v t = (β * z) • 𝔼.E t (v (t + 1)) +
      (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) t := by
    intro t
    have e : v (t + 1) = d (t + 1) - z • d t := by
      funext ω; simp only [hv, lagP, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    funext ω
    have k := hrec t ω
    have ev : v t ω = d t ω - z * lagP (fun _ => 0) d t ω := by rw [hv]
    rw [ev, e, map_sub, map_smul, hdE t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, add_zero]
    linear_combination (-z) * k + d t ω * hzq
  have hdb : ∀ s ω', |d s ω'| ≤ Bx + |BX| := fun s ω' => by
    rw [hd]
    exact (abs_sub _ _).trans (add_le_add (hBx s ω') ((hBX s ω').trans (le_abs_self _)))
  have hvb : BoundedProc v := by
    refine ⟨(Bx + |BX|) + z * (Bx + |BX|), fun t ω => ?_⟩
    have hB0 : 0 ≤ Bx + |BX| := (abs_nonneg _).trans (hdb 0 ω)
    have hlb : |lagP (fun _ => 0) d t ω| ≤ Bx + |BX| := by
      cases t with
      | zero => simp only [lagP, abs_zero]; exact hB0
      | succ t => exact hdb t ω
    rw [hv]
    calc _ ≤ |d t ω| + |z * lagP (fun _ => 0) d t ω| := abs_sub _ _
      _ = |d t ω| + z * |lagP (fun _ => 0) d t ω| := by rw [abs_mul, abs_of_pos hz0]
      _ ≤ _ := add_le_add (hdb t ω) (mul_le_mul_of_nonneg_left hlb hz0.le)
  have hβz : |β * z| < 1 := by
    rw [abs_of_pos (mul_pos hβ0 hz0)]; nlinarith
  have hv0 := 𝔼.forward_unique hβz hvrec (z₂ := fun _ _ => 0) (fun t => by
    funext ω
    have e : (fun (_ : Ω) => (0 : ℝ)) = 0 := rfl
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e, map_zero, Pi.zero_apply,
      mul_zero, add_zero]) hvb ⟨0, fun _ _ => by simp⟩
  have hd0 : ∀ t ω, d t ω = 0 := by
    intro t
    induction t with
    | zero =>
      intro ω
      have := congrFun (congrFun hv0 0) ω
      rw [hv] at this
      simpa [lagP] using this
    | succ t ih =>
      intro ω
      have := congrFun (congrFun hv0 (t + 1)) ω
      rw [hv] at this
      simp only [lagP, ih ω, mul_zero, sub_zero] at this
      exact this
  have hxX : x = X := by
    funext t ω; rw [hdx t ω, hd0 t ω, add_zero]
  refine ⟨hxX, ?_⟩
  funext t ω
  have := hdπ t ω
  rw [hd0 t ω] at this
  cases t with
  | zero => simp only [lagP, sub_zero, mul_zero, neg_zero, sub_eq_zero] at this; exact this
  | succ t => simp only [lagP, hd0 t ω, sub_zero, mul_zero, neg_zero, sub_eq_zero] at this
              exact this

/-! ## The first-order component of the Ramsey plan is the footnote-71 plan -/

/-- Woodford (2003), (5.8): the target `Ŷ*` and the cost-push term are bounded on bounded
disturbances. -/
theorem Ys1_u1_bdd (p : Par) (R : RPar) :
    ∃ C, ∀ e : Fin 5 → ℝ, ‖e‖ ≤ 1 → |Ys1 p R e| ≤ C ∧ |u1 p R e| ≤ C := by
  have hc1 : Continuous fun e : Fin 5 → ℝ => Ys1 p R e := by
    unfold Ys1 LargeDistortions.YstarA LargeDistortions.YnA; fun_prop
  have hc2 : Continuous fun e : Fin 5 → ℝ => u1 p R e := by
    unfold u1 LargeDistortions.costPush511 LargeDistortions.YstarA LargeDistortions.YnA; fun_prop
  obtain ⟨C1, h1⟩ := (isCompact_closedBall (0 : Fin 5 → ℝ) 1).exists_bound_of_continuousOn
    hc1.continuousOn
  obtain ⟨C2, h2⟩ := (isCompact_closedBall (0 : Fin 5 → ℝ) 1).exists_bound_of_continuousOn
    hc2.continuousOn
  refine ⟨max C1 C2, fun e he => ?_⟩
  have hm : e ∈ Metric.closedBall (0 : Fin 5 → ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact he
  have k1 := h1 e hm
  have k2 := h2 e hm
  rw [Real.norm_eq_abs] at k1 k2
  exact ⟨k1.trans (le_max_left _ _), k2.trans (le_max_right _ _)⟩

/-- **Woodford (2003), §5, (5.6)–(5.11), footnote 71 and Ch. 7, §1 (the first-order component of
the exact Ramsey plan IS the footnote-71 plan, for every distortion).** Let `A_uG ≠ 0`, `P` a
path of the event tree, `ê` a disturbance pattern with `‖ê‖ ≤ 1`, and `v` a bounded solution
of the linearised Ramsey system with the disturbance forcing, `L v = −DQe(ê)` (zero initial
lag; e.g. `v = z₁` of `TidyR6aExpand.first_order_family`). Then along the path the output gap
`ŷ − Ŷ*` is `fnX` and inflation is `fnPi`, with `φ = λ̃/κ = 1/θ`
(`TidyR6aShock.lamTilde_one`), `x_{−1} = 0` and the cost-push term
`u = κ(Ŷ* − Ŷⁿ)` of the disturbances (`LargeDistortions.costPush511`). -/
theorem first_order_is_fn71 {p : Par} (hp : p.Std) (R : RPar) (hG : R.Au * Gw p R ≠ 0)
    (P : TreePath 𝔼 T) (ê : Y → Fin 5 → ℝ) (hê : ∀ y, ‖ê y‖ ≤ 1) (v : Y → Fin 9 → ℝ) (B : ℝ)
    (hvb : ∀ y, ‖v y‖ ≤ B) (hL : LR T p R v = fun y => -DQs p R (ê y)) :
    (fun t ω => v (P.nd t ω) 0 - Ys1 p R (ê (P.nd t ω))) =
        fnX 𝔼 p.β p.κ (1 / p.θ) (fun t ω => u1 p R (ê (P.nd t ω))) 0 ∧
      (fun t ω => v (P.nd t ω) 1) =
        fnPi 𝔼 p.β p.κ (1 / p.θ) (fun t ω => u1 p R (ê (P.nd t ω))) 0 := by
  obtain ⟨-, -, hAS, hTR, -⟩ := first_order_tree T R hp hG ê v hL
  obtain ⟨CY, hCY⟩ := Ys1_u1_bdd p R
  have hθ0 : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hθ := hθ0.ne'
  have hv0 : ∀ y, |v y 0| ≤ B := fun y => by
    have := (norm_le_pi_norm (v y) 0).trans (hvb y); rwa [Real.norm_eq_abs] at this
  refine fn71_unique (M := CY) hp.β_pos hp.β_lt_one hp.κ_pos (by positivity)
    (fun t ω => (hCY _ (hê _)).2) (fun t => P.E_now t (fun y => u1 p R (ê y))) 0
    ⟨B + CY, fun t ω => (abs_sub _ _).trans (add_le_add (hv0 _) (hCY _ (hê _)).1)⟩
    (fun t => P.E_now t (fun y => v y 0 - Ys1 p R (ê y))) (fun t => ?_) (fun t ω => ?_)
  · funext ω
    have h := hAS (P.nd t ω)
    have hE := congrFun (P.E_next t (fun y => v y 1)) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hE, h, costPush_one]
    ring
  · have h := hTR (P.nd t ω)
    rw [lag0_nd P (fun y => v y 0 - Ys1 p R (ê y)) t ω] at h
    field_simp
    linear_combination h

/-- **Woodford (2003), Ch. 6, §5, and Ch. 7, §1 (the exact timeless Ramsey plan and its
first-order component), for every distortion with `A_uG ≠ 0`** (in particular every `A_u > 0`,
`0 ≤ Φ ≤ 1`, `NonlinearNKMarkovRamseyLin.AuGw_pos`). There are `r, δ₀ > 0` and `C ≥ 0` such
that on every event tree, for every disturbance pattern `ê` with `‖ê‖ ≤ 1`, every amplitude
`|ε| ≤ δ₀` and every initial dispersion with `|Δ_{−1} − 1| ≤ ε²`, the timeless Ramsey conditions
(root lag `lagTL`: steady-state multipliers) with disturbances `εê` have a solution `w` within
`r` of the steady state `w̄`, the only one there, and `‖w − w̄ − εz₁‖ ≤ Cε²` at every node,
`z₁ = L⁻¹(−DQe(ê))`. -/
theorem timeless_first_order {p : Par} (hp : p.Std) (R : RPar) (hG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ₀ > 0, ∃ C, 0 ≤ C ∧ ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ)
      (ε Dm1 : ℝ), (∀ y, ‖ê y‖ ≤ 1) → |ε| ≤ δ₀ → |Dm1 - 1| ≤ ε ^ 2 →
        ∃ w : Y → Fin 9 → ℝ, (RamseyL T p R (fun y => ε • ê y) (lagTL p R Dm1) w ∧
          (∀ y, ‖w y - ramseySS p R‖ ≤ r) ∧
          ∀ w', RamseyL T p R (fun y => ε • ê y) (lagTL p R Dm1) w' →
            (∀ y, ‖w' y - ramseySS p R‖ ≤ r) → w' = w) ∧
          ∀ y, ‖w y - ramseySS p R - ε • LinvR T p R (fun y => -DQs p R (ê y)) y‖ ≤
            C * ε ^ 2 := by
  obtain ⟨r, hr, δ₀, hδ₀, C, hC, H⟩ := first_order_family R hp hG
  refine ⟨r, hr, δ₀, hδ₀, C, hC, fun {Y} T ê ε Dm1 hê hε hD => ?_⟩
  have hd : ∀ y : Y, ‖(fun _ => lagTL p R Dm1 - ramseySS p R) y‖ ≤ ε ^ 2 := fun _ => by
    refine (norm_le_of_abs (abs_nonneg (Dm1 - 1)) fun i => ?_).trans hD
    fin_cases i <;> simp [lagTL, ramseySS]
  obtain ⟨z, ⟨hzb, hz⟩, hu, hfo⟩ := H T ê _ ε hê hε hd
  refine ⟨fun y => ramseySS p R + z y, ⟨?_, fun y => ?_, fun w' hw' hw'b => ?_⟩, fun y => ?_⟩
  · rw [ramseyL_iff]; simpa using hz
  · simpa using hzb y
  · have := hu (fun y => w' y - ramseySS p R) hw'b ((ramseyL_iff _ _ _ _ _ _).1 hw')
    funext y; rw [← congrFun this y]; abel
  · simpa using hfo y

/-- Woodford (2003), Ch. 7 (**without distortion the date-0 plan is the timeless plan**): when
`Φ = 0` the steady-state multipliers of the `F`, `K` recursions vanish, so the date-0 and the
timeless conditions coincide. -/
theorem date0_eq_timeless {p : Par} (R : RPar) (hΦ : R.Φ = 0) (e : Y → Fin 5 → ℝ) (Dm1 : ℝ)
    (w : Y → Fin 9 → ℝ) :
    RamseyL T p R e (lagD0 Dm1) w ↔ RamseyL T p R e (lagTL p R Dm1) w :=
  ramseyL_congr_lag T p R e (by simp [lagD0, lagTL]) (by simp [lagD0, lagTL, ramseyLam, hΦ])
    (by simp [lagD0, lagTL, ramseyLam, hΦ]) w

/-- Woodford (2003), p. 414 (**the steady-state multiplier of the `F` recursion is nonzero exactly
when the steady state is distorted**): `λ̄₁ = −ΦA_u/((1−αβ)(ω+σ)) ≠ 0` for `A_u ≠ 0`, `Φ ≠ 0`. -/
theorem lam1_ne {p : Par} (hp : p.Std) (R : RPar) (hA : R.Au ≠ 0) (hΦ : R.Φ ≠ 0) :
    ramseyLam p R 0 ≠ 0 := by
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  simp only [ramseyLam, Matrix.cons_val_zero, ne_eq, neg_eq_zero, div_eq_zero_iff,
    mul_eq_zero, hΦ, hA, hab, hωσ, or_self, not_false_eq_true]

/-- **Woodford (2003), pp. 414–415 and Ch. 7 (the date-0 plan of a distorted economy is NOT near
the steady state).** If `λ̄₁ ≠ 0` (i.e. `A_u ≠ 0`, `Φ ≠ 0`, `lam1_ne`) there is `ρ > 0` such that
for EVERY event tree, disturbance process and initial dispersion, every solution of the date-0
Ramsey conditions is at distance more than `ρ` from the steady state at every root node. So the
date-0 plan has no first-order component around `w̄` (it is not `w̄ + O(ε)`); the
footnote-71 plan is the first-order component of the timeless plan (`timeless_first_order`,
`first_order_is_fn71`), and of the date-0 plan only when `Φ = 0` (`date0_eq_timeless`). -/
theorem date0_far {p : Par} (hp : p.Std) (R : RPar) (hl : ramseyLam p R 0 ≠ 0) :
    ∃ ρ > 0, ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 5 → ℝ) (Dm1 : ℝ)
      (w : Y → Fin 9 → ℝ), RamseyL T p R e (lagD0 Dm1) w → ∀ x, T.depth x = 0 →
        ρ < ‖w x - ramseySS p R‖ := by
  set g : (Fin 9 → ℝ) → ℝ := fun v => ramseyQ p R 0 (lagD0 1) v 2 with hg
  have hgc : Continuous g := by
    simp only [hg, ramseyQ, lagD0, Matrix.cons_val]; fun_prop
  have hss : g (ramseySS p R) = p.α * ramseyLam p R 0 := by
    have h := congrFun (ramsey_steadyState p R hp) 2
    simp only [Pi.add_apply, Pi.zero_apply, ramseyN, Matrix.cons_val, add_zero] at h
    simp only [hg]
    have e : ramseyQ p R 0 (lagD0 1) (ramseySS p R) 2 =
        ramseyQ p R 0 (ramseySS p R) (ramseySS p R) 2 + p.α * ramseyLam p R 0 := by
      simp [ramseyQ, lagD0, ramseySS]
      ring
    rw [e, h, zero_add]
  have hα := hp.α_pos.ne'
  have hpos : 0 < |p.α * ramseyLam p R 0| := abs_pos.2 (mul_ne_zero hα hl)
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.1 hgc.continuousAt _ hpos
  refine ⟨ρ / 2, by positivity, fun {Y} T e Dm1 w hw x hx => ?_⟩
  by_contra hle
  push Not at hle
  have hgx : g (w x) ≠ 0 := by
    intro h0
    have hd : dist (w x) (ramseySS p R) < ρ := by
      rw [dist_eq_norm]; linarith
    have := hball hd
    rw [hss, h0, dist_eq_norm, zero_sub, norm_neg, Real.norm_eq_abs] at this
    exact lt_irrefl _ this
  apply hgx
  have h := congrFun (hw x) 2
  have hM : Mv T.M (fun y => ramseyN p (w y)) x 2 = 0 := by
    change T.M (fun y => ramseyN p (w y) 2) x = 0
    have e0 : (fun y => ramseyN p (w y) 2) = fun _ => (0 : ℝ) := by funext y; simp [ramseyN]
    rw [e0, M_const T]
  simp only [hx, ↓reduceIte, Pi.add_apply, Pi.zero_apply, hM, add_zero] at h
  have e : g (w x) = ramseyQ p R (e x) (lagD0 Dm1) (w x) 2 := by
    simp [hg, ramseyQ, lagD0]
  rw [e, h]

end Woodford.StabilizationWelfare.TidyR6aBridge
