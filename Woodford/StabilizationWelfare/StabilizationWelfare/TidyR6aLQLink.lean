/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aBridge
import StabilizationWelfare.TidyR6aAS
import StabilizationWelfare.TidyR5RamseySOC

/-!
# The LQ sufficiency argument for the actual Ramsey plan

Woodford (2003), *Interest and Prices*, Chapter 6, §5, Proposition 6.15, (5.5)–(5.11),
pp. 458–461, §3.2, pp. 414–415, footnote 71, and Chapter 7, §1.

`TidyR5RamseySOC.lq_sufficiency615` proved that the family whose first-order component is the
footnote-71 plan is optimal up to `O(ε³)` among feasible families with the same `W₀` and
t.i.p., ASSUMING (a) that this family is the actual Ramsey plan and (b) that the competitors'
first-order components satisfy the linear AS relation. Both are now proved:

* `timeless_family`: the exact timeless Ramsey plan along any family of amplitudes `ε → 0`
  (`TidyR6aBridge.timeless_first_order`), with `w = w̄ + εz₁ + O(ε²)` eventually, uniformly;
  `uproc_of_bound`: such a bound is a `BridgeExtensions.UProc` statement.
* **`ramsey_first_order_uproc`** (hypothesis (a)): along any path, the exact Ramsey plan's
  inflation and output satisfy `π − ε fnPi = O(ε²)` and `Ŷ − ε(fnX + Ŷ*) = O(ε²)` uniformly in
  date and state, with `φ = λ̃/κ = 1/θ` and the cost-push term `κ(Ŷ* − Ŷⁿ)`: the footnote-71
  plan IS the first-order component of the Ramsey plan, for every `Φ ∈ [0, 1]` (`A_u > 0`).
* **`ramsey_lq_sufficiency`**: `TidyR5RamseySOC.lq_sufficiency615` for the ACTUAL Ramsey plan,
  with hypothesis (b) derived (`TidyR6aAS.first_order_NKPCu`): for every `Φ ∈ [0, 1)`, every
  feasible family of
  exact Calvo equilibria with the same disturbances, first-order components and (through the
  welfare expansion of Proposition 6.15) the same `W₀` and t.i.p. has welfare
  `W_B ≤ W_A + C|ε|³`, strictly lower for small `ε ≠ 0` if its first-order loss is larger.
-/

namespace Woodford.StabilizationWelfare.TidyR6aLQLink

open Filter Topology Asymptotics
open NonlinearNKMarkov NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree TidyR6aShock TidyR6aBridge TidyR5CommitLQ TidyR5RamseyDate0
open BridgeExtensions

/-- Woodford (2003), §5 and Ch. 7, §1 (**the exact timeless Ramsey plan along a family of
amplitudes**): for `A_uG ≠ 0` there are `r > 0`, `C ≥ 0` such that on every event tree, for
every disturbance pattern `‖ê‖ ≤ 1`, every family of amplitudes `ε → 0` and initial dispersions
with `|Δ_{−1} − 1| ≤ ε²`, there is a family `w` that is eventually THE timeless Ramsey plan
(locally unique within `r`) and satisfies `‖w − w̄ − εz₁‖ ≤ Cε²` at every node. -/
theorem timeless_family {p : Par} (hp : p.Std) (R : RPar) (hG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ C, 0 ≤ C ∧ ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ),
      (∀ y, ‖ê y‖ ≤ 1) → ∀ {A : Type*} {l : Filter A} {e : A → ℝ}, Tendsto e l (𝓝 0) →
        ∀ Dm1 : A → ℝ, (∀ a, |Dm1 a - 1| ≤ e a ^ 2) → ∃ w : A → Y → Fin 9 → ℝ,
          ∀ᶠ a in l, (RamseyL T p R (fun y => e a • ê y) (lagTL p R (Dm1 a)) (w a) ∧
            (∀ y, ‖w a y - ramseySS p R‖ ≤ r) ∧
            ∀ w', RamseyL T p R (fun y => e a • ê y) (lagTL p R (Dm1 a)) w' →
              (∀ y, ‖w' y - ramseySS p R‖ ≤ r) → w' = w a) ∧
            ∀ y, ‖w a y - ramseySS p R - e a • LinvR T p R (fun y => -DQs p R (ê y)) y‖ ≤
              C * e a ^ 2 := by
  obtain ⟨r, hr, δ₀, hδ₀, C, hC, H⟩ := timeless_first_order hp R hG
  refine ⟨r, hr, C, hC, fun {Y} T ê hê {A} {l} {e} he Dm1 hD => ?_⟩
  classical
  refine ⟨fun a => if h : |e a| ≤ δ₀ then Classical.choose (H T ê (e a) (Dm1 a) hê h (hD a))
    else fun _ => 0, ?_⟩
  have hev : ∀ᶠ a in l, |e a| ≤ δ₀ := by
    filter_upwards [he (Metric.closedBall_mem_nhds 0 hδ₀)] with a ha
    simpa [Real.dist_eq] using ha
  filter_upwards [hev] with a ha
  have hs := Classical.choose_spec (H T ê (e a) (Dm1 a) hê ha (hD a))
  simp only [ha, ↓reduceDIte]
  exact hs

variable {Ω Y : Type*} {𝔼 : ExpectationSystem Ω} {T : LagTree Y}
variable {A : Type*} {l : Filter A} {e : A → ℝ}

/-- Woodford (2003), §2, p. 394: an eventual bound `|f| ≤ Cε²`, uniform in date and state, is a
uniform order statement. -/
theorem uproc_of_bound {f : A → ℕ → Ω → ℝ} {C : ℝ}
    (h : ∀ᶠ a in l, ∀ t z, |f a t z| ≤ C * e a ^ 2) : UProc l f fun a => e a ^ 2 := by
  refine IsBigO.of_bound C ?_
  filter_upwards [h.prod_inl (⊤ : Filter (ℕ × Ω))] with q hq
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (e q.1))]
  exact hq q.2.1 q.2.2

/-- **Woodford (2003), §5, footnote 71, pp. 414–415 (hypothesis (a): the footnote-71 plan IS
the first-order component of the exact Ramsey plan).** For `A_u > 0`, `0 ≤ Φ ≤ 1`, along every
path of every event tree, for every disturbance pattern `‖ê‖ ≤ 1` and every family `ε → 0` with
`|Δ_{−1} − 1| ≤ ε²`, the exact timeless Ramsey plan `w` satisfies, uniformly in date and state,
`π − ε fnPi = O(ε²)` and `Ŷ − ε(fnX + Ŷ*) = O(ε²)`, with `φ = 1/θ = λ̃/κ`, `x_{−1} = 0`, the
cost-push term `u = κ(Ŷ* − Ŷⁿ)` and the target `Ŷ*` of Benigno–Woodford. -/
theorem ramsey_first_order_uproc {p : Par} (hp : p.Std) {Au Φ : ℝ} (hA : 0 < Au) (hΦ0 : 0 ≤ Φ)
    (hΦ1 : Φ ≤ 1) (P : TreePath 𝔼 T) (ê : Y → Fin 5 → ℝ) (hê : ∀ y, ‖ê y‖ ≤ 1)
    (he : Tendsto e l (𝓝 0)) (Dm1 : A → ℝ) (hD : ∀ a, |Dm1 a - 1| ≤ e a ^ 2) :
    ∃ w : A → Y → Fin 9 → ℝ,
      (∀ᶠ a in l, RamseyL T p ⟨Au, Φ⟩ (fun y => e a • ê y) (lagTL p ⟨Au, Φ⟩ (Dm1 a)) (w a)) ∧
      UProc l (fun a t z => w a (P.nd t z) 1 - e a *
        fnPi 𝔼 p.β p.κ (1 / p.θ) (fun t z => u1 p ⟨Au, Φ⟩ (ê (P.nd t z))) 0 t z)
        (fun a => e a ^ 2) ∧
      UProc l (fun a t z => w a (P.nd t z) 0 - e a *
        (fnX 𝔼 p.β p.κ (1 / p.θ) (fun t z => u1 p ⟨Au, Φ⟩ (ê (P.nd t z))) 0 t z +
          Ys1 p ⟨Au, Φ⟩ (ê (P.nd t z)))) (fun a => e a ^ 2) := by
  set R : RPar := ⟨Au, Φ⟩ with hR
  have hG : R.Au * Gw p R ≠ 0 := (AuGw_pos R hp hA hΦ0 hΦ1).ne'
  obtain ⟨r, -, C, -, H⟩ := timeless_family hp R hG
  obtain ⟨B1, -, hz1⟩ := TidyR6aExpand.first_order_solves R hp hG
  obtain ⟨hLz1, hz1b⟩ := hz1 T ê hê
  obtain ⟨w, hw⟩ := H T ê hê he Dm1 hD
  obtain ⟨hxfn, hpfn⟩ := first_order_is_fn71 hp R hG P ê hê _ B1 hz1b hLz1
  set z1 := LinvR T p R (fun y => -DQs p R (ê y)) with hz1d
  refine ⟨w, hw.mono fun a ha => ha.1.1, ?_, ?_⟩
  · refine uproc_of_bound (C := C) (hw.mono fun a ha t z => ?_)
    have hb := (norm_le_pi_norm _ 1).trans (ha.2 (P.nd t z))
    rw [Real.norm_eq_abs] at hb
    have e1 : fnPi 𝔼 p.β p.κ (1 / p.θ) (fun t z => u1 p R (ê (P.nd t z))) 0 t z =
        z1 (P.nd t z) 1 := (congrFun (congrFun hpfn t) z).symm
    rw [e1]
    have hc : (w a (P.nd t z) - ramseySS p R - e a • z1 (P.nd t z)) 1 =
        w a (P.nd t z) 1 - e a * z1 (P.nd t z) 1 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ramseySS, Matrix.cons_val_one,
        Matrix.cons_val_zero, sub_zero]
    rw [hc] at hb
    exact hb
  · refine uproc_of_bound (C := C) (hw.mono fun a ha t z => ?_)
    have hb := (norm_le_pi_norm _ 0).trans (ha.2 (P.nd t z))
    rw [Real.norm_eq_abs] at hb
    have e1 : fnX 𝔼 p.β p.κ (1 / p.θ) (fun t z => u1 p R (ê (P.nd t z))) 0 t z +
        Ys1 p R (ê (P.nd t z)) = z1 (P.nd t z) 0 := by
      rw [← congrFun (congrFun hxfn t) z]; ring
    rw [e1]
    have hc : (w a (P.nd t z) - ramseySS p R - e a • z1 (P.nd t z)) 0 =
        w a (P.nd t z) 0 - e a * z1 (P.nd t z) 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ramseySS, Matrix.cons_val_zero,
        sub_zero]
    rw [hc] at hb
    exact hb

/-- **Woodford (2003), Proposition 6.15, footnote 71 and pp. 414–415 (second-order sufficiency of
the ACTUAL Ramsey plan, up to `O(ε³)`, for every `Φ ∈ [0, 1)`).** Let `A_u > 0`, `ω > 0`, `P` a
path of an event tree in an expectation system with the pull-out property, `‖ê‖ ≤ 1`, `ε → 0`
along a non-trivial filter with `ε ≠ 0` eventually and `|Δ_{−1} − 1| ≤ ε²`. Then the exact
timeless Ramsey plan `w` (`ramsey_first_order_uproc`) has first-order component
`(π₁, Ŷ₁) = (z₁₁, z₁₀)` along the path, and for EVERY family `B` of exact Calvo equilibria of the
same economy (`LargeDistortions.CalvoModel.CalvoAS` with `s_C = 1`, the same disturbances `εê`)
whose reset-price variables are `O(ε)` and whose inflation and output have bounded first-order
components `(π_B, Ŷ_B)`: if
both families have the welfare expansion of Proposition 6.15 with the same `W₀` and t.i.p.
(`BridgeExtensions.prop615_first_order`), then `W_B ≤ W_A + C|ε|³` for small `ε`, and
`W_B < W_A` for small `ε ≠ 0` if `B`'s first-order loss is larger. Both hypotheses of
`TidyR5RamseySOC.lq_sufficiency615` are discharged: (a) by `first_order_is_fn71`, (b) by
`TidyR6aAS.first_order_NKPCu`. -/
theorem ramsey_lq_sufficiency (hPO : 𝔼.PullOut) {p : Par} (hp : p.Std) (hω : 0 < p.ω)
    {Au Φ : ℝ} (hA : 0 < Au) (hΦ0 : 0 ≤ Φ) (hΦ1 : Φ < 1) (P : TreePath 𝔼 T)
    (ê : Y → Fin 5 → ℝ) (hê : ∀ y, ‖ê y‖ ≤ 1) {Ybar uc : ℝ} (hY : 0 < Ybar) (huc : 0 < uc)
    [l.NeBot] (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ a in l, e a ≠ 0)
    {infB xrB FB KB fB kB YB : A → ℕ → Ω → ℝ}
    (hMB : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 p.α p.β p.θ p.ω p.σ 1 (infB a) (xrB a)
      (FB a) (KB a) (fB a) (kB a) (YB a) (fun _ _ => 0) (fun t z => e a * ê (P.nd t z) 1)
      (fun t z => e a * ê (P.nd t z) 3) (fun t z => e a * ê (P.nd t z) 4)
      (fun t z => e a * ê (P.nd t z) 2))
    {πB YB1 : ℕ → Ω → ℝ} (hπB : BoundedProc πB) (hYB1 : BoundedProc YB1)
    (hidB : UProc l (fun a t z => infB a t z - e a * πB t z) fun a => e a ^ 2)
    (hYdB : UProc l (fun a t z => YB a t z - e a * YB1 t z) fun a => e a ^ 2)
    (hxrB : UProc l xrB fun a => e a ^ 1) (hFB : UProc l FB fun a => e a ^ 1)
    (hKB : UProc l KB fun a => e a ^ 1) (hfB : UProc l fB fun a => e a ^ 1)
    (hkB : UProc l kB fun a => e a ^ 1) {WA WB W0 Tt : A → ℝ} (w0 : Ω)
    (hWA : (fun a => WA a - (W0 a - e a ^ 2 * (LargeDistortions.OmegaTilde Ybar uc p.α p.β p.θ
      p.ω p.σ Φ * Sequences.dsum 𝔼 p.β (LargeDistortions.loss615 p.α p.β p.θ p.ω p.σ 1 Φ
        (fun t z => LinvR T p ⟨Au, Φ⟩ (fun y => -DQs p ⟨Au, Φ⟩ (ê y)) (P.nd t z) 1)
        (fun t z => LinvR T p ⟨Au, Φ⟩ (fun y => -DQs p ⟨Au, Φ⟩ (ê y)) (P.nd t z) 0)
        (fun _ _ => 0) (fun t z => ê (P.nd t z) 1) (fun t z => ê (P.nd t z) 3)
        (fun t z => ê (P.nd t z) 4) (fun t z => ê (P.nd t z) 2)) w0) + Tt a)) =O[l]
      fun a => e a ^ 3)
    (hWB : (fun a => WB a - (W0 a - e a ^ 2 * (LargeDistortions.OmegaTilde Ybar uc p.α p.β p.θ
      p.ω p.σ Φ * Sequences.dsum 𝔼 p.β (LargeDistortions.loss615 p.α p.β p.θ p.ω p.σ 1 Φ
        πB YB1 (fun _ _ => 0) (fun t z => ê (P.nd t z) 1) (fun t z => ê (P.nd t z) 3)
        (fun t z => ê (P.nd t z) 4) (fun t z => ê (P.nd t z) 2)) w0) + Tt a)) =O[l]
      fun a => e a ^ 3) :
    (∃ C, ∀ᶠ a in l, WB a - WA a ≤ C * |e a| ^ 3) ∧
      (ELoss 𝔼 p.β (p.κ / p.θ) 0
          (fun t z => LinvR T p ⟨Au, Φ⟩ (fun y => -DQs p ⟨Au, Φ⟩ (ê y)) (P.nd t z) 1)
          (fun t z => LinvR T p ⟨Au, Φ⟩ (fun y => -DQs p ⟨Au, Φ⟩ (ê y)) (P.nd t z) 0 -
            Ys1 p ⟨Au, Φ⟩ (ê (P.nd t z))) w0 <
        ELoss 𝔼 p.β (p.κ / p.θ) 0 πB (fun t z => YB1 t z - Ys1 p ⟨Au, Φ⟩ (ê (P.nd t z))) w0 →
        ∀ᶠ a in l, WB a < WA a) := by
  set R : RPar := ⟨Au, Φ⟩ with hR
  have hG : R.Au * Gw p R ≠ 0 := (AuGw_pos R hp hA hΦ0 hΦ1.le).ne'
  obtain ⟨B1, -, hz1⟩ := TidyR6aExpand.first_order_solves R hp hG
  obtain ⟨hLz1, hz1b⟩ := hz1 T ê hê
  obtain ⟨hxfn, hpfn⟩ := first_order_is_fn71 hp R hG P ê hê _ B1 hz1b hLz1
  set z1 := LinvR T p R (fun y => -DQs p R (ê y)) with hz1d
  set u : ℕ → Ω → ℝ := fun t z => u1 p R (ê (P.nd t z)) with hu
  obtain ⟨CY, hCY⟩ := Ys1_u1_bdd p R
  have hθ0 : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hlam := lamTilde_one p R hp
  have hlam0 : 0 < LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 Φ := by
    rw [hlam.1]; exact div_pos hp.κ_pos hθ0
  -- the competitor's first-order components satisfy the AS relation (hypothesis (b))
  have hb1 : ∀ i, BoundedProc (fun t z => ê (P.nd t z) i) := fun i => ⟨1, fun t z => by
    have := (norm_le_pi_norm (ê (P.nd t z)) i).trans (hê _); rwa [Real.norm_eq_abs] at this⟩
  have hzero : ∀ (X : A → ℕ → Ω → ℝ) (X1 : ℕ → Ω → ℝ), (∀ a t z, X a t z = e a * X1 t z) →
      UProc l (fun a t z => X a t z - e a * X1 t z) fun a => e a ^ 2 := fun X X1 h => by
    refine (isBigO_zero _ _).congr_left fun q => ?_
    simp only [h, sub_self]
  have hAS := TidyR6aAS.first_order_NKPCu 𝔼 (Φ := Φ) hp.α_pos hp.α_lt_one
    (by linarith [hp.one_lt_θ]) hp.c0_pos.ne' one_ne_zero
    (by linarith [hp.ω_nonneg, hp.σ_pos]) he hne.frequently hMB hπB hYB1
    (G1 := fun _ _ => 0) ⟨0, fun _ _ => by simp⟩ (hb1 1) (hb1 3) (hb1 4) (hb1 2) hidB hYdB
    (hzero _ _ fun _ _ _ => by ring) (hzero _ _ fun _ _ _ => rfl) (hzero _ _ fun _ _ _ => rfl)
    (hzero _ _ fun _ _ _ => rfl) (hzero _ _ fun _ _ _ => rfl) hxrB hFB hKB hfB hkB
  -- apply the LQ sufficiency theorem
  have hu' : ∀ t z, |u t z| ≤ CY := fun t z => (hCY _ (hê _)).2
  have hua : 𝔼.Adapted u := fun t => P.E_now t (fun y => u1 p R (ê y))
  obtain ⟨BY, hBY⟩ := hYB1
  have hbx' : BoundedProc (fun t z => YB1 t z - Ys1 p R (ê (P.nd t z))) :=
    ⟨BY + CY, fun t z => (abs_sub _ _).trans (add_le_add (hBY t z) (hCY _ (hê _)).1)⟩
  have eπ : (fun t z => z1 (P.nd t z) 1) =
      fnPi 𝔼 p.β p.κ (LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 Φ / p.κ) u 0 := by
    rw [hlam.2]; exact hpfn
  have eY : (fun t z => z1 (P.nd t z) 0) = fun t z =>
      fnX 𝔼 p.β p.κ (LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 Φ / p.κ) u 0 t z +
        Ys1 p R (ê (P.nd t z)) := by
    rw [hlam.2]
    funext t z
    rw [← congrFun (congrFun hxfn t) z]
    ring
  have hL := TidyR5RamseySOC.lq_sufficiency615 𝔼 hPO (sC := 1) (κ := p.κ) (M := CY) hY huc
    hp.α_pos hp.α_lt_one hp.β_pos hp.β_lt_one hθ0 hω hp.σ_pos hΦ0 hΦ1 hp.κ_pos hlam0 hu' hua
    (G1 := fun _ _ => 0) (cb1 := fun t z => ê (P.nd t z) 1) (q1 := fun t z => ê (P.nd t z) 3)
    (muw1 := fun t z => ê (P.nd t z) 4) (tau1 := fun t z => ê (P.nd t z) 2)
    hπB hbx' hAS he hne (WA := WA) (WB := WB) (W0 := W0) (T := Tt) w0
    (hWA.congr_left fun a => by rw [eπ, eY]; rfl)
    (hWB.congr_left fun a => by simp only [Ys1, hR, sub_add_cancel])
  refine ⟨hL.1, fun hlt => hL.2 ?_⟩
  have eX : fnX 𝔼 p.β p.κ (LargeDistortions.lamTilde p.α p.β p.θ p.ω p.σ 1 Φ / p.κ) u 0 =
      fun t z => z1 (P.nd t z) 0 - Ys1 p R (ê (P.nd t z)) := by
    rw [hlam.2]; exact hxfn.symm
  rw [eX, ← eπ, hlam.1]
  exact hlt

end Woodford.StabilizationWelfare.TidyR6aLQLink
