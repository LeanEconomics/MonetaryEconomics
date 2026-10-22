/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR5KappaPosCore
import GainsFromCommitment.NaturalRateCommitment

/-!
# Optimal responses to natural-rate disturbances: `κ > 0`, and uniqueness at `κ = 0`

Woodford (2003), *Interest and Prices*, Chapter 7, §1.2 (the first-order conditions
(1.16)–(1.18), p. 478) and §2.2, pp. 502–507 (the loss (2.24), the IS relation (2.23), the initial
conditions (2.25) and (2.26), Figure 7.6, and the `κ = 0` optimum (2.28)–(2.30)).

## Main results

**The general system with `κ > 0`** (the dynamics behind Figure 7.6). For every admissible
calibration (`0 < β < 1`, `σ, κ, λₓ, λᵢ > 0`), every bounded adapted natural rate `rⁿ` (and
cost-push `u`) and every pair of initial multipliers `(φ_{1,t₀−1}, φ_{2,t₀−1})`:

* the system (2.1), (2.23), (1.16)–(1.18) has **exactly one** bounded adapted solution
  `(π, x, i, φ₁, φ₂)` (`foc_system_existsUnique`), through the one-to-one correspondence with the
  multiplier system (`sys_of_foc`, `foc_of_sys`, `plan_eq_of_foc`);
* with the initial conditions (2.25) it is the **`t₀`-optimal commitment**: it minimises the
  expected discounted loss (2.24) among all bounded plans satisfying (2.1) and (2.23)
  (`t0_optimal`); with any initial multipliers it is optimal given its own `π_{t₀}, x_{t₀}`, i.e.
  **timelessly optimal** in the sense of (2.26) (`timeless_optimal`); with a faithful expectation
  system it is the unique such optimum (`optimum_unique`);
* **history dependence** (pp. 503–505): the multipliers follow the partial-adjustment law
  `Φ_t = XΦ_{t−1} + ψ_t`, where `ψ_t` is the forward solution of `ψ_t = K E_tψ_{t+1} + B⁻¹F_t`
  (current and expected future disturbances only) and the inertia matrix `X` is real, has both
  eigenvalues inside the unit circle and `det X > 0` (so lagged multipliers always matter)
  (`partial_adjustment`). This generalises (2.29) to `κ > 0`.

**The `κ = 0` optimum (2.29).** Uniqueness holds whenever the date-`t₀` expectation is faithful
(`kappa0_unique_faithful`) but **fails for a general expectation system**: on a two-state system
in which the second state is null at `t₀` but revealed at `t₀ + 1`, a different bounded adapted
plan satisfying (2.23) and the timeless constraint (2.26) attains the same expected loss
(`kappa0_not_unique`).
-/

namespace Woodford.GainsFromCommitment.TidyR5NaturalRateKappa

open Filter Topology
open TidyR5KappaPosCore (Calib lag AS IS FOC3 FOC4 FOC5 FOC Feasible Jloss OptimalGiven Sys2
  lagV Fphi piOf xOf iOf PmG A1G A2G rows_real sys_row VAdapted VBounded planOf_bounded
  planOf_adapted sys2_existsUnique exists_real_split solvent_eq schurStable_scale pG_ofReal pR
  plan_optimal unique_optimum Faithful lagV_known Fphi_bounded Fphi_adapted psiOf inv2 FSolves
  rvMul sys2_step_iff)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The multipliers as a vector -/

/-- Woodford (2003), (1.16)–(1.18), p. 478: the multiplier vector `Φ_t = (φ_{1t}, φ_{2t})`. -/
def vecOf (φ1 φ2 : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![φ1 t, φ2 t]

omit 𝔼 in
/-- Woodford (2003), (2.25), p. 503: the initial multipliers `Φ_{t₀−1} = (φ_{1,t₀−1},
φ_{2,t₀−1})`. -/
def vecH (φ1h φ2h : ℝ) : Fin 2 → ℝ := ![φ1h, φ2h]

omit 𝔼 in
/-- Woodford (2003), p. 478 (tool): the lagged first multiplier is the first coordinate of the
lagged vector. -/
theorem lag_vec0 (φ1h φ2h : ℝ) (φ1 φ2 : ℕ → Ω → ℝ) (t : ℕ) :
    lag φ1h φ1 t = lagV (vecH φ1h φ2h) (vecOf φ1 φ2) t 0 := by
  cases t <;> rfl

omit 𝔼 in
/-- Woodford (2003), p. 478 (tool): the lagged second multiplier is the second coordinate. -/
theorem lag_vec1 (φ1h φ2h : ℝ) (φ1 φ2 : ℕ → Ω → ℝ) (t : ℕ) :
    lag φ2h φ2 t = lagV (vecH φ1h φ2h) (vecOf φ1 φ2) t 1 := by
  cases t <;> rfl

omit 𝔼 in
/-- Woodford (2003), p. 478 (tool): the coordinates of a lagged vector are the lags of the
coordinates. -/
theorem lagV_coords (φ1h φ2h : ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) :
    lagV (vecH φ1h φ2h) Φ t 0 = lag φ1h (fun s => Φ s 0) t ∧
      lagV (vecH φ1h φ2h) Φ t 1 = lag φ2h (fun s => Φ s 1) t := by
  cases t <;> exact ⟨rfl, rfl⟩

omit 𝔼 in
/-- Woodford (2003), (1.16)–(1.18), p. 478: given the multipliers, the first-order conditions
determine the plan: `π`, `x`, `i` are `TidyR5KappaPosCore.piOf`, `TidyR5KappaPosCore.xOf`,
`TidyR5KappaPosCore.iOf` of the multipliers. -/
theorem plan_eq_of_foc (c : Calib) (hc : c.Adm) {π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ}
    (hfoc : FOC c π x i φ1 φ2 φ1h φ2h) :
    π = piOf c (vecH φ1h φ2h) (vecOf φ1 φ2) ∧ x = xOf c (vecH φ1h φ2h) (vecOf φ1 φ2) ∧
      i = iOf c (vecOf φ1 φ2) := by
  obtain ⟨-, -, hσ, -, hlx, hli⟩ := hc
  refine ⟨funext fun t => funext fun ω => ?_, funext fun t => funext fun ω => ?_,
    funext fun t => funext fun ω => ?_⟩
  · have h := congrFun (hfoc t).1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [piOf, ← lag_vec0, ← lag_vec1, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    simp only [vecOf, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith
  · have h := congrFun (hfoc t).2.1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [xOf, ← lag_vec0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [vecOf, Matrix.cons_val_one, Matrix.cons_val_zero]
    have e : c.lx * (x t ω - c.xstar) = c.κ * φ2 t ω - φ1 t ω + c.β⁻¹ * lag φ1h φ1 t ω := by
      linarith
    rw [← e]
    field_simp
    ring
  · have h := congrFun (hfoc t).2.2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [iOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [vecOf, Matrix.cons_val_zero]
    have e : c.σ * φ1 t ω = -(c.li * (i t ω - c.istar)) := by linarith
    rw [div_mul_eq_mul_div, e]
    field_simp
    ring

/-- Woodford (2003), (1.16)–(1.18) with (2.1), (2.23), pp. 478, 502–503 (from the plan to the
multiplier system): the multipliers of a feasible plan satisfying the first-order conditions
solve `P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t` with `Φ_{t₀−1}` the initial multipliers. -/
theorem sys_of_foc (c : Calib) (hc : c.Adm) {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ}
    (hf : Feasible 𝔼 c rn u π x i) (hfoc : FOC c π x i φ1 φ2 φ1h φ2h) (hφ1a : 𝔼.Adapted φ1)
    (hφ2a : 𝔼.Adapted φ2) :
    Sys2 𝔼 (PmG c.β c.σ c.κ c.lx) (A1G c.β c.σ c.κ c.lx c.li) (A2G c.β c.σ c.κ c.lx)
      (Fphi c rn u) (vecH φ1h φ2h) (vecOf φ1 φ2) := by
  obtain ⟨hβ0, -, hσ, hκ, hlx, hli⟩ := hc
  intro t
  funext j ω
  have hp : π t ω = c.σ / c.β * lag φ1h φ1 t ω - φ2 t ω + lag φ2h φ2 t ω := by
    have := congrFun (hfoc t).1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linarith
  have hep : 𝔼.E t (π (t + 1)) ω = c.σ / c.β * φ1 t ω - 𝔼.E t (φ2 (t + 1)) ω + φ2 t ω := by
    have h := congrArg (𝔼.E t) (hfoc (t + 1)).1
    rw [map_zero] at h
    have := congrFun h ω
    simp only [lag, map_add, map_sub, map_smul, hφ1a t, hφ2a t, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linarith
  have hx : x t ω = c.xstar + c.lx⁻¹ * (c.κ * φ2 t ω - φ1 t ω + c.β⁻¹ * lag φ1h φ1 t ω) := by
    have := congrFun (hfoc t).2.1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have e : c.lx * (x t ω - c.xstar) = c.κ * φ2 t ω - φ1 t ω + c.β⁻¹ * lag φ1h φ1 t ω := by
      linarith
    rw [← e]
    field_simp
    ring
  have hex : 𝔼.E t (x (t + 1)) ω = c.xstar + c.lx⁻¹ * (c.κ * 𝔼.E t (φ2 (t + 1)) ω
      - 𝔼.E t (φ1 (t + 1)) ω + c.β⁻¹ * φ1 t ω) := by
    have h := congrArg (𝔼.E t) (hfoc (t + 1)).2.1
    rw [map_zero] at h
    have := congrFun h ω
    simp only [lag, map_add, map_sub, map_smul, hφ1a t, 𝔼.const, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have e : c.lx * (𝔼.E t (x (t + 1)) ω - c.xstar) = c.κ * 𝔼.E t (φ2 (t + 1)) ω
        - 𝔼.E t (φ1 (t + 1)) ω + c.β⁻¹ * φ1 t ω := by linarith
    rw [← e]
    field_simp
    ring
  have hi : i t ω = c.istar - c.σ / c.li * φ1 t ω := by
    have := congrFun (hfoc t).2.2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have e : c.σ * φ1 t ω = -(c.li * (i t ω - c.istar)) := by linarith
    rw [div_mul_eq_mul_div, e]
    field_simp
    ring
  have r := rows_real c hβ0.ne' hlx.ne' hli.ne' (u := u t ω) (rn := rn t ω) hp hep hx hex hi
  have hAS : π t ω = c.κ * x t ω + c.β * 𝔼.E t (π (t + 1)) ω + u t ω := by
    have := congrFun (hf t).1 ω
    simpa only [AS, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hIS : x t ω = 𝔼.E t (x (t + 1)) ω - c.σ * (i t ω - 𝔼.E t (π (t + 1)) ω - rn t ω) := by
    have := congrFun (hf t).2 ω
    simpa only [IS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  rw [sys_row, ← lag_vec0, ← lag_vec1]
  fin_cases j
  · have := r.2.mp hIS
    simp only [PmG, A1G, A2G, Fphi, vecOf, Matrix.of_apply, Matrix.cons_val', Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  · have := r.1.mp hAS
    simp only [PmG, A1G, A2G, Fphi, vecOf, Matrix.of_apply, Matrix.cons_val', Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Pi.add_apply]
    linarith


/-- Woodford (2003), (1.16)–(1.18) with (2.1), (2.23), pp. 478, 502–503 (from the multiplier
system to the plan): for an adapted solution `Φ` of the multiplier system, the plan read off the
first-order conditions satisfies (2.1) and (2.23), and `(Φ₁, Φ₂)` are its multipliers. -/
theorem foc_of_sys (c : Calib) (hc : c.Adm) {rn u : ℕ → Ω → ℝ} {φ1h φ2h : ℝ}
    {Φ : ℕ → Fin 2 → Ω → ℝ}
    (hs : Sys2 𝔼 (PmG c.β c.σ c.κ c.lx) (A1G c.β c.σ c.κ c.lx c.li) (A2G c.β c.σ c.κ c.lx)
      (Fphi c rn u) (vecH φ1h φ2h) Φ) (ha : VAdapted 𝔼 Φ) :
    Feasible 𝔼 c rn u (piOf c (vecH φ1h φ2h) Φ) (xOf c (vecH φ1h φ2h) Φ) (iOf c Φ) ∧
      FOC c (piOf c (vecH φ1h φ2h) Φ) (xOf c (vecH φ1h φ2h) Φ) (iOf c Φ) (fun s => Φ s 0)
        (fun s => Φ s 1) φ1h φ2h := by
  obtain ⟨hβ0, -, hσ, hκ, hlx, hli⟩ := hc
  set Φh := vecH φ1h φ2h with hΦh
  refine ⟨fun t => ?_, fun t => ⟨?_, ?_, ?_⟩⟩
  · refine ⟨?_, ?_⟩
    all_goals
      have hrow := congrFun (hs t)
      have hl : lagV Φh Φ (t + 1) = Φ t := rfl
      funext ω
      have r := rows_real c hβ0.ne' hlx.ne' hli.ne' (u := u t ω) (rn := rn t ω)
        (a1 := lagV Φh Φ t 0 ω) (a2 := lagV Φh Φ t 1 ω) (f1 := Φ t 0 ω) (f2 := Φ t 1 ω)
        (e1 := 𝔼.E t (Φ (t + 1) 0) ω) (e2 := 𝔼.E t (Φ (t + 1) 1) ω)
        (p := piOf c Φh Φ t ω) (x := xOf c Φh Φ t ω) (i := iOf c Φ t ω)
        (ep := 𝔼.E t (piOf c Φh Φ (t + 1)) ω) (ex := 𝔼.E t (xOf c Φh Φ (t + 1)) ω)
        (by simp only [piOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
        (by simp only [piOf, hl, map_add, map_sub, map_smul, ha t 0, ha t 1, Pi.add_apply,
              Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
        (by simp only [xOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
        (by simp only [xOf, hl, map_add, map_sub, map_smul, ha t 0, 𝔼.const, Pi.add_apply,
              Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
        (by simp only [iOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
      have h0 := hrow 0
      have h1 := hrow 1
      rw [funext_iff] at h0 h1
      have h0 := h0 ω
      have h1 := h1 ω
      rw [sys_row] at h0 h1
      simp only [PmG, A1G, A2G, Fphi, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
        smul_eq_mul] at h0 h1
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact r.1.mpr (by linarith)
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact r.2.mpr (by linarith)
  · obtain ⟨l0, l1⟩ := lagV_coords φ1h φ2h Φ t
    unfold FOC3
    rw [← l0, ← l1]
    funext ω
    simp only [piOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  · obtain ⟨l0, -⟩ := lagV_coords φ1h φ2h Φ t
    unfold FOC4
    rw [← l0]
    funext ω
    simp only [xOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  · unfold FOC5
    funext ω
    simp only [iOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring

omit 𝔼 in
/-- Woodford (2003), App. G.4, p. 722, for the Chapter 7 problem (§2.2): the multiplier system has
a real solvent `X` (`PX² − A₁X + A₂ = 0`) with both eigenvalues inside the unit circle and
`det X > 0`, `B = PX − A₁` invertible, and `K = −B⁻¹P` with both eigenvalues inside the unit
circle — for every admissible calibration. -/
theorem exists_solvent (c : Calib) (hc : c.Adm) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      PmG c.β c.σ c.κ c.lx * X * X - A1G c.β c.σ c.κ c.lx c.li * X + A2G c.β c.σ c.κ c.lx = 0 ∧
      SchurStable (tr2 X) (det2 X) ∧ 0 < det2 X ∧
      det2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) ≠ 0 ∧
      SchurStable (tr2 (-(inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) *
          PmG c.β c.σ c.κ c.lx)))
        (det2 (-(inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) *
          PmG c.β c.σ c.κ c.lx))) := by
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩ := hc
  obtain ⟨T, D, hTD, hD, hfacC⟩ := exists_real_split hβ0 hβ1 hσ hκ hlx.le hli
  have hfac : ∀ μ : ℝ, pR c.β c.σ c.κ c.lx c.li μ =
      (μ ^ 2 - T * μ + D) * (μ ^ 2 - T / (c.β * D) * μ + 1 / (c.β ^ 2 * D)) := by
    intro μ
    have := hfacC μ
    rw [pG_ofReal] at this
    exact_mod_cast this
  obtain ⟨-, hsolv, htr, hdet, hB, htrK, hdetK⟩ := solvent_eq hβ0 hβ1 hlx hli hTD hD hfac
  have hK := schurStable_scale hβ0 hβ1 hTD
  rw [← htrK, ← hdetK] at hK
  refine ⟨_, hsolv, ?_, ?_, hB, hK⟩
  · rw [htr, hdet]; exact hTD
  · rw [hdet]; exact hD

/-! ### Existence, uniqueness, optimality and history dependence for `κ > 0` -/

/-- **The general system (1.16)–(1.18) under natural-rate (and cost-push) disturbances,
`κ > 0`** (Woodford (2003), pp. 478 and 502–505): for every admissible calibration, every bounded
adapted `rⁿ`, `u` and every pair of initial multipliers, (2.1), (2.23) and the first-order
conditions (1.16)–(1.18) have **exactly one** bounded adapted solution `(π, x, i, φ₁, φ₂)`. -/
theorem foc_system_existsUnique (c : Calib) (hc : c.Adm) {rn u : ℕ → Ω → ℝ}
    (hrb : BoundedProc rn) (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u)
    (φ1h φ2h : ℝ) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Feasible 𝔼 c rn u p.1 p.2.1 p.2.2.1 ∧ FOC c p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 φ1h φ2h ∧
      (𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2.1 ∧ 𝔼.Adapted p.2.2.2.1 ∧
        𝔼.Adapted p.2.2.2.2) ∧
      (BoundedProc p.1 ∧ BoundedProc p.2.1 ∧ BoundedProc p.2.2.1 ∧ BoundedProc p.2.2.2.1 ∧
        BoundedProc p.2.2.2.2) := by
  obtain ⟨X, hsolv, hXs, -, hB, hK⟩ := exists_solvent c hc
  obtain ⟨Φ, ⟨hs, ha, hb⟩, huniq⟩ := sys2_existsUnique 𝔼 hsolv hXs hB hK
    (Fphi_bounded c hrb hub) (Fphi_adapted 𝔼 c hra hua) (vecH φ1h φ2h)
  obtain ⟨hf, hfoc⟩ := foc_of_sys 𝔼 c hc hs ha
  obtain ⟨b1, b2, b3⟩ := planOf_bounded c (vecH φ1h φ2h) hb
  obtain ⟨a1, a2, a3⟩ := planOf_adapted 𝔼 c (vecH φ1h φ2h) ha
  obtain ⟨M, hM⟩ := hb
  refine ⟨(piOf c (vecH φ1h φ2h) Φ, xOf c (vecH φ1h φ2h) Φ, iOf c Φ, fun s => Φ s 0,
    fun s => Φ s 1), ⟨hf, hfoc, ⟨a1, a2, a3, fun t => ha t 0, fun t => ha t 1⟩,
    ⟨b1, b2, b3, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩⟩⟩, ?_⟩
  rintro ⟨π', x', i', φ1', φ2'⟩ ⟨hf', hfoc', ⟨-, -, -, h1a, h2a⟩, ⟨-, -, -, ⟨M1, hM1⟩, ⟨M2, hM2⟩⟩⟩
  have hs' := sys_of_foc 𝔼 c hc hf' hfoc' h1a h2a
  have hva : VAdapted 𝔼 (vecOf φ1' φ2') := by
    intro t j
    fin_cases j
    · exact h1a t
    · exact h2a t
  have hvb : VBounded (vecOf φ1' φ2') := by
    refine ⟨max M1 M2, fun t j ω => ?_⟩
    fin_cases j
    · exact (hM1 t ω).trans (le_max_left _ _)
    · exact (hM2 t ω).trans (le_max_right _ _)
  have hΦ := huniq _ ⟨hs', hva, hvb⟩
  obtain ⟨e1, e2, e3⟩ := plan_eq_of_foc c hc hfoc'
  have e4 : φ1' = fun s => Φ s 0 := funext fun s => by rw [← hΦ]; rfl
  have e5 : φ2' = fun s => Φ s 1 := funext fun s => by rw [← hΦ]; rfl
  simp only at e1 e2 e3
  rw [hΦ] at e1 e2 e3
  simp only [Prod.mk.injEq]
  exact ⟨e1, e2, e3, e4, e5⟩

/-- **The `t₀`-optimal commitment with `κ > 0`** (Woodford (2003), (2.24)–(2.25), p. 503): the
solution of (2.1), (2.23), (1.16)–(1.18) with zero initial multipliers (2.25) and bounded adapted
multipliers minimises the expected discounted loss (2.24) among **all** bounded plans satisfying
(2.1) and (2.23) (pull-out property assumed). -/
theorem t0_optimal (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut) {rn u π x i φ1 φ2 : ℕ → Ω → ℝ}
    (hf : Feasible 𝔼 c rn u π x i) (hfoc : FOC c π x i φ1 φ2 0 0) (hφ1a : 𝔼.Adapted φ1)
    (hφ2a : 𝔼.Adapted φ2) (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    (hφ1b : BoundedProc φ1) (hφ2b : BoundedProc φ2) {π' x' i' : ℕ → Ω → ℝ}
    (hf' : Feasible 𝔼 c rn u π' x' i') (hπb' : BoundedProc π') (hxb' : BoundedProc x')
    (hib' : BoundedProc i') : Jloss 𝔼 c π x i ≤ Jloss 𝔼 c π' x' i' :=
  plan_optimal 𝔼 c hc hpo hf hfoc hφ1a hφ2a hπb hxb hib hφ1b hφ2b hf' hπb' hxb' hib'
    (Or.inl ⟨rfl, rfl⟩)

/-- **Timeless optimality with `κ > 0`** (Woodford (2003), (2.26), p. 503): for any initial
multipliers, the bounded adapted solution of (2.1), (2.23), (1.16)–(1.18) minimises (2.24) among
all bounded adapted plans satisfying (2.1), (2.23) and the initial constraints
`π_{t₀} = π̄_{t₀}`, `x_{t₀} = x̄_{t₀}` with its own values. -/
theorem timeless_optimal (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut)
    {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ} (hf : Feasible 𝔼 c rn u π x i)
    (hfoc : FOC c π x i φ1 φ2 φ1h φ2h) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hia : 𝔼.Adapted i) (hφ1a : 𝔼.Adapted φ1) (hφ2a : 𝔼.Adapted φ2) (hπb : BoundedProc π)
    (hxb : BoundedProc x) (hib : BoundedProc i) (hφ1b : BoundedProc φ1)
    (hφ2b : BoundedProc φ2) : OptimalGiven 𝔼 c rn u (π 0) (x 0) π x i :=
  ⟨hf, ⟨hπa, hxa, hia⟩, ⟨hπb, hxb, hib⟩, rfl, rfl, fun _ _ _ hf' _ ⟨hπb', hxb', hib'⟩ h0 hx0 =>
    plan_optimal 𝔼 c hc hpo hf hfoc hφ1a hφ2a hπb hxb hib hφ1b hφ2b hf' hπb' hxb' hib'
      (Or.inr ⟨h0, hx0⟩)⟩

/-- Woodford (2003), (2.25)–(2.26), p. 503 (uniqueness of the optimum): with a faithful
expectation system and the pull-out property, a bounded feasible plan with the same initial
condition — zero initial multipliers (2.25), or the same `π_{t₀}, x_{t₀}` (2.26) — and the same
expected loss coincides with the solution of the first-order conditions. -/
theorem optimum_unique (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut) (hfa : Faithful 𝔼)
    {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ} (hf : Feasible 𝔼 c rn u π x i)
    (hfoc : FOC c π x i φ1 φ2 φ1h φ2h) (hφ1a : 𝔼.Adapted φ1) (hφ2a : 𝔼.Adapted φ2)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i) (hφ1b : BoundedProc φ1)
    (hφ2b : BoundedProc φ2) {π' x' i' : ℕ → Ω → ℝ} (hf' : Feasible 𝔼 c rn u π' x' i')
    (hπb' : BoundedProc π') (hxb' : BoundedProc x') (hib' : BoundedProc i')
    (hinit : (φ1h = 0 ∧ φ2h = 0) ∨ (π' 0 = π 0 ∧ x' 0 = x 0))
    (hJ : Jloss 𝔼 c π' x' i' = Jloss 𝔼 c π x i) : π' = π ∧ x' = x ∧ i' = i :=
  unique_optimum 𝔼 c hc hpo hfa hf hfoc hφ1a hφ2a hπb hxb hib hφ1b hφ2b hf' hπb' hxb' hib' hinit hJ

/-- **History dependence of the optimal responses** (Woodford (2003), pp. 503–505 and Figure 7.6;
the `κ > 0` counterpart of (2.29)): there is a real inertia matrix `X`, with both eigenvalues
inside the unit circle and `det X > 0`, and a matrix `K` with both eigenvalues inside the unit
circle, such that for every bounded adapted `rⁿ, u` and initial multipliers, the multipliers of
the solution of (2.1), (2.23), (1.16)–(1.18) follow `Φ_t = XΦ_{t−1} + ψ_t`, where `ψ` is bounded,
adapted and solves `ψ_t = K E_tψ_{t+1} + B⁻¹F_t` — so `ψ_t` depends only on current and expected
future disturbances, while the lagged multipliers enter with the invertible weight `X`. -/
theorem partial_adjustment (c : Calib) (hc : c.Adm) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ, SchurStable (tr2 X) (det2 X) ∧ 0 < det2 X ∧
      SchurStable (tr2 (-(inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) *
          PmG c.β c.σ c.κ c.lx)))
        (det2 (-(inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) *
          PmG c.β c.σ c.κ c.lx))) ∧
      ∀ {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ}, Feasible 𝔼 c rn u π x i →
        FOC c π x i φ1 φ2 φ1h φ2h → 𝔼.Adapted φ1 → 𝔼.Adapted φ2 →
        (∀ t, vecOf φ1 φ2 t = rvMul X (lagV (vecH φ1h φ2h) (vecOf φ1 φ2) t) +
          psiOf X (vecH φ1h φ2h) (vecOf φ1 φ2) t) ∧
        FSolves 𝔼 (-(inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) *
          PmG c.β c.σ c.κ c.lx))
          (fun t => rvMul (inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li))
            (Fphi c rn u t)) (psiOf X (vecH φ1h φ2h) (vecOf φ1 φ2)) := by
  obtain ⟨X, hsolv, hXs, hdet, hB, hK⟩ := exists_solvent c hc
  refine ⟨X, hXs, hdet, hK, fun {rn u π x i φ1 φ2 φ1h φ2h} hf hfoc h1a h2a => ⟨fun t => ?_,
    fun t => ?_⟩⟩
  · simp only [psiOf]
    abel
  · have hva : VAdapted 𝔼 (vecOf φ1 φ2) := by
      intro s j
      fin_cases j
      · exact h1a s
      · exact h2a s
    exact (sys2_step_iff 𝔼 hsolv hB hva t).mp (sys_of_foc 𝔼 c hc hf hfoc h1a h2a t)


/-! ### The `κ = 0` optimum (2.29): uniqueness under faithfulness, and a counterexample -/

omit 𝔼 in
/-- Woodford (2003), (2.24), p. 503, with `κ = 0` (so `π ≡ 0`): the realised discounted loss
`∑_k βᵏ[λₓ(x_{t₀+k} − x*)² + λᵢ(i_{t₀+k} − i*)²]` (Lean dates `k + 1`), state by state. -/
noncomputable def kloss (β lamx lami xs is : ℝ) (y z : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑' k, β ^ k * (lamx * (y (k + 1) ω - xs) ^ 2 + lami * (z (k + 1) ω - is) ^ 2)

omit 𝔼 in
/-- Woodford (2003), (2.24), p. 503 (tool): the discounted loss of a bounded plan is summable. -/
theorem summable_kloss {β lamx lami xs is : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {y z : ℕ → Ω → ℝ}
    (hy : BoundedProc y) (hz : BoundedProc z) (ω : Ω) :
    Summable fun k => β ^ k * (lamx * (y (k + 1) ω - xs) ^ 2 + lami * (z (k + 1) ω - is) ^ 2) := by
  obtain ⟨My, hMy⟩ := hy
  obtain ⟨Mz, hMz⟩ := hz
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right
    (|lamx| * (My + |xs|) ^ 2 + |lami| * (Mz + |is|) ^ 2)) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 k)
  have a := (abs_sub (y (k + 1) ω) xs).trans (add_le_add (hMy (k + 1) ω) le_rfl)
  have b := (abs_sub (z (k + 1) ω) is).trans (add_le_add (hMz (k + 1) ω) le_rfl)
  have a2 : (y (k + 1) ω - xs) ^ 2 ≤ (My + |xs|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a 2
  have b2 : (z (k + 1) ω - is) ^ 2 ≤ (Mz + |is|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) b 2
  calc |lamx * (y (k + 1) ω - xs) ^ 2 + lami * (z (k + 1) ω - is) ^ 2|
      ≤ |lamx| * (y (k + 1) ω - xs) ^ 2 + |lami| * (z (k + 1) ω - is) ^ 2 := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (y (k + 1) ω - xs)),
          abs_of_nonneg (sq_nonneg (z (k + 1) ω - is))]
    _ ≤ _ := by gcongr

omit 𝔼 in
/-- Woodford (2003), (2.24), p. 503 (the parallelogram identity behind strict convexity): the
loss of the midpoint of two bounded plans is the average loss minus a quarter of the loss of
their difference. -/
theorem kloss_midpoint {β lamx lami xs is : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {y z y' z' : ℕ → Ω → ℝ} (hy : BoundedProc y) (hz : BoundedProc z) (hy' : BoundedProc y')
    (hz' : BoundedProc z') :
    kloss β lamx lami xs is (fun t => (1 / 2 : ℝ) • (y t + y' t))
        (fun t => (1 / 2 : ℝ) • (z t + z' t)) =
      (1 / 2 : ℝ) • kloss β lamx lami xs is y z + (1 / 2 : ℝ) • kloss β lamx lami xs is y' z' -
        (1 / 4 : ℝ) • kloss β lamx lami 0 0 (fun t => y t - y' t) (fun t => z t - z' t) := by
  have hd1 : BoundedProc (fun t => y t - y' t) := by
    obtain ⟨A, hA⟩ := hy
    obtain ⟨B, hB⟩ := hy'
    exact ⟨A + B, fun t ω => (abs_sub _ _).trans (add_le_add (hA t ω) (hB t ω))⟩
  have hd2 : BoundedProc (fun t => z t - z' t) := by
    obtain ⟨A, hA⟩ := hz
    obtain ⟨B, hB⟩ := hz'
    exact ⟨A + B, fun t ω => (abs_sub _ _).trans (add_le_add (hA t ω) (hB t ω))⟩
  funext ω
  have h := (((summable_kloss (lamx := lamx) (lami := lami) (xs := xs) (is := is) hβ0 hβ1 hy hz
    ω).hasSum.mul_left (1 / 2)).add ((summable_kloss (lamx := lamx) (lami := lami) (xs := xs)
    (is := is) hβ0 hβ1 hy' hz' ω).hasSum.mul_left (1 / 2))).sub
    ((summable_kloss (lamx := lamx) (lami := lami) (xs := 0) (is := 0) hβ0 hβ1 hd1 hd2
    ω).hasSum.mul_left (1 / 4))
  simp only [kloss, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine HasSum.tsum_eq ?_
  convert h using 1
  funext k
  simp only [Pi.sub_apply]
  ring

/-- **Uniqueness of the `κ = 0` optimum (2.29) for a faithful expectation system** (Woodford
(2003), (2.28)–(2.30), p. 506, footnote 26): if `E_{t₀}` is faithful (a nonnegative variable with
zero date-`t₀` expectation is zero), the plan of (2.29) with the first-order-condition output gap
is the **only** bounded plan satisfying (2.23) and the timeless constraint `x_{t₀} = x̄_{t₀}` that
attains the minimal expected loss (pull-out property assumed). -/
theorem kappa0_unique_faithful (hpo : 𝔼.PullOut)
    (hf1 : ∀ y : Ω → ℝ, 0 ≤ y → 𝔼.E 1 y = 0 → y = 0) {β σ lamx lami xs is M B0 : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hlx : 0 < lamx) (hli : 0 < lami)
    {rn : ℕ → Ω → ℝ} (hrn : ∀ t ω, |rn t ω| ≤ M) (hrna : 𝔼.Adapted rn) {i0 : Ω → ℝ}
    (hi0 : 𝔼.E 0 i0 = i0) (hi0b : ∀ ω, |i0 ω| ≤ B0) :
    ∃ ih : ℕ → Ω → ℝ, ih 0 = i0 ∧ 𝔼.Adapted ih ∧ BoundedProc ih ∧
      NaturalRateCommitment.Eq228 𝔼 β (lamx * σ ^ 2 / lami) rn ih ∧
      (∀ t, NaturalRateCommitment.xFromFoc β σ lamx lami xs is ih (t + 1) =
        𝔼.E (t + 1) (NaturalRateCommitment.xFromFoc β σ lamx lami xs is ih (t + 2)) -
          σ • (ih (t + 1) - rn (t + 1))) ∧
      ∀ x i : ℕ → Ω → ℝ, BoundedProc x → BoundedProc i →
        (∀ t, x (t + 1) = 𝔼.E (t + 1) (x (t + 2)) - σ • (i (t + 1) - rn (t + 1))) →
        x 1 = NaturalRateCommitment.xFromFoc β σ lamx lami xs is ih 1 →
        𝔼.E 1 (kloss β lamx lami xs is x i) =
          𝔼.E 1 (kloss β lamx lami xs is (NaturalRateCommitment.xFromFoc β σ lamx lami xs is ih)
            ih) →
        ∀ t, x (t + 1) = NaturalRateCommitment.xFromFoc β σ lamx lami xs is ih (t + 1) ∧
          i (t + 1) = ih (t + 1) := by
  obtain ⟨ih, h0, ha, hb, h228, -, hIS, hopt⟩ :=
    NaturalRateCommitment.optimal_plan_kappa0 𝔼 hpo (xs := xs) (is := is) hβ0 hβ1 hσ hlx hli
      hrn hrna hi0 hi0b
  refine ⟨ih, h0, ha, hb, h228, hIS, fun x i hxb hib hISx hx1 hL t => ?_⟩
  set xh := NaturalRateCommitment.xFromFoc β σ lamx lami xs is ih with hxh
  have hxhb : BoundedProc xh := by
    obtain ⟨Mh, hMh⟩ := hb
    refine ⟨|xs| + |lami / (σ * lamx)| * ((Mh + |is|) + |β⁻¹| * (Mh + |is|)), fun t ω => ?_⟩
    simp only [hxh, NaturalRateCommitment.xFromFoc, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]
    have h1 : |ih t ω - is| ≤ Mh + |is| := (abs_sub _ _).trans (add_le_add (hMh _ _) le_rfl)
    have h2 : |ih (t - 1) ω - is| ≤ Mh + |is| :=
      (abs_sub _ _).trans (add_le_add (hMh _ _) le_rfl)
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (abs_nonneg _)
    rw [abs_mul]
    gcongr
  set xm : ℕ → Ω → ℝ := fun t => (1 / 2 : ℝ) • (x t + xh t) with hxm
  set im : ℕ → Ω → ℝ := fun t => (1 / 2 : ℝ) • (i t + ih t) with him
  have hmb : BoundedProc xm ∧ BoundedProc im := by
    obtain ⟨A, hA⟩ := hxb
    obtain ⟨B, hB⟩ := hxhb
    obtain ⟨C, hC⟩ := hib
    obtain ⟨D, hD⟩ := hb
    refine ⟨⟨(A + B) / 2, fun t ω => ?_⟩, ⟨(C + D) / 2, fun t ω => ?_⟩⟩
    · simp only [hxm, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [(abs_add_le (x t ω) (xh t ω)).trans (add_le_add (hA t ω) (hB t ω))]
    · simp only [him, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [(abs_add_le (i t ω) (ih t ω)).trans (add_le_add (hC t ω) (hD t ω))]
  have hISm : ∀ t, xm (t + 1) = 𝔼.E (t + 1) (xm (t + 2)) - σ • (im (t + 1) - rn (t + 1)) := by
    intro t
    have a := hISx t
    have b := hIS t
    simp only [hxm, him, map_smul, map_add]
    funext ω
    have a' := congrFun a ω
    have b' := congrFun b ω
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at a' b' ⊢
    linear_combination (1 / 2 : ℝ) * a' + (1 / 2 : ℝ) * b'
  have hm1 : xm 1 = xh 1 := by
    simp only [hxm, hx1]
    funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  set D := kloss β lamx lami 0 0 (fun t => x t - xh t) (fun t => i t - ih t) with hD
  have hDnn : 0 ≤ D := fun ω => tsum_nonneg fun k => mul_nonneg (pow_nonneg hβ0.le k)
    (by positivity)
  have hmid := kloss_midpoint (lamx := lamx) (lami := lami) (xs := xs) (is := is) hβ0.le hβ1 hxb
    hib hxhb hb
  have hED : 𝔼.E 1 D = 0 := by
    funext ω
    have hle := hopt xm im hmb.1 hmb.2 hISm hm1 ω
    change 𝔼.E 1 (kloss β lamx lami xs is xh ih) ω ≤ 𝔼.E 1 (kloss β lamx lami xs is xm im) ω
      at hle
    have e : kloss β lamx lami xs is xm im = kloss β lamx lami xs is
        (fun t => (1 / 2 : ℝ) • (x t + xh t)) (fun t => (1 / 2 : ℝ) • (i t + ih t)) := rfl
    rw [e, hmid, map_sub, map_add, map_smul, map_smul, map_smul, hL] at hle
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hle
    have hge : 0 ≤ 𝔼.E 1 D ω := by
      have hm := 𝔼.mono 1 hDnn
      rw [show (0 : Ω → ℝ) = fun _ => (0 : ℝ) from rfl, 𝔼.const] at hm
      exact hm ω
    simp only [Pi.zero_apply]
    linarith
  have hD0 := hf1 D hDnn hED
  have hd1 : BoundedProc (fun t => x t - xh t) := by
    obtain ⟨A, hA⟩ := hxb
    obtain ⟨B, hB⟩ := hxhb
    exact ⟨A + B, fun t ω => (abs_sub _ _).trans (add_le_add (hA t ω) (hB t ω))⟩
  have hd2 : BoundedProc (fun t => i t - ih t) := by
    obtain ⟨A, hA⟩ := hib
    obtain ⟨B, hB⟩ := hb
    exact ⟨A + B, fun t ω => (abs_sub _ _).trans (add_le_add (hA t ω) (hB t ω))⟩
  have hterm : ∀ ω k, β ^ k * (lamx * (x (k + 1) ω - xh (k + 1) ω - 0) ^ 2 +
      lami * (i (k + 1) ω - ih (k + 1) ω - 0) ^ 2) = 0 := by
    intro ω k
    have hs := summable_kloss (lamx := lamx) (lami := lami) (xs := 0) (is := 0) hβ0.le hβ1 hd1
      hd2 ω
    have hz := congrFun hD0 ω
    simp only [hD, kloss, Pi.zero_apply] at hz
    have hnn : ∀ k, 0 ≤ β ^ k * (lamx * (x (k + 1) ω - xh (k + 1) ω - 0) ^ 2 +
        lami * (i (k + 1) ω - ih (k + 1) ω - 0) ^ 2) := fun k =>
      mul_nonneg (pow_nonneg hβ0.le k) (by positivity)
    have := (hasSum_zero_iff_of_nonneg hnn).mp (hz ▸ hs.hasSum)
    exact congrFun this k
  have hp := (pow_pos hβ0 t).ne'
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · have q := (mul_eq_zero.mp (hterm ω t)).resolve_left hp
    have a1 := mul_nonneg hlx.le (sq_nonneg (x (t + 1) ω - xh (t + 1) ω - 0))
    have a2 := mul_nonneg hli.le (sq_nonneg (i (t + 1) ω - ih (t + 1) ω - 0))
    have e : lamx * (x (t + 1) ω - xh (t + 1) ω - 0) ^ 2 = 0 := by linarith
    have e' := pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp e).resolve_left hlx.ne')
    linarith
  · have q := (mul_eq_zero.mp (hterm ω t)).resolve_left hp
    have a1 := mul_nonneg hlx.le (sq_nonneg (x (t + 1) ω - xh (t + 1) ω - 0))
    have a2 := mul_nonneg hli.le (sq_nonneg (i (t + 1) ω - ih (t + 1) ω - 0))
    have e : lami * (i (t + 1) ω - ih (t + 1) ω - 0) ^ 2 = 0 := by linarith
    have e' := pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp e).resolve_left hli.ne')
    linarith


omit 𝔼 in
/-- Woodford (2003), p. 506, fn. 26 (counterexample tool): on two states, the expectation that
puts all weight on the state `true`, `y ↦ (ω ↦ y true)`. -/
def evalTrue : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) where
  toFun y := fun _ => y true
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit 𝔼 in
/-- Woodford (2003), p. 506, fn. 26 (counterexample): an expectation system on two states in which
the state `false` is null at dates `0` and `1` (`E_t y = y(true)`) but revealed from date `2`
(`E_t = id`). It satisfies all the axioms of an `ExpectationSystem`. -/
def lateInfo : ExpectationSystem Bool where
  E t := if t ≤ 1 then evalTrue else LinearMap.id
  const t c := by split_ifs <;> rfl
  mono t x y h := by
    split_ifs
    · intro ω; exact h true
    · exact h
  tower {s t} hst x := by
    by_cases hs : s ≤ 1 <;> by_cases ht : t ≤ 1
    · simp only [hs, ht, ↓reduceIte]; rfl
    · simp only [hs, ht, ↓reduceIte]; rfl
    · omega
    · simp only [hs, ht, ↓reduceIte]; rfl
  known {s t} hst x := by
    by_cases hs : s ≤ 1 <;> by_cases ht : t ≤ 1
    · simp only [hs, ht, ↓reduceIte]; rfl
    · simp only [hs, ht, ↓reduceIte]; rfl
    · omega
    · simp only [hs, ht, ↓reduceIte]; rfl

omit 𝔼 in
/-- Woodford (2003), p. 506 (counterexample tool): `lateInfo` has the pull-out property. -/
theorem lateInfo_pullOut : lateInfo.PullOut := by
  intro t a y ha
  change (if t ≤ 1 then evalTrue else LinearMap.id) (a * y) =
    a * (if t ≤ 1 then evalTrue else LinearMap.id) y
  change (if t ≤ 1 then evalTrue else LinearMap.id) a = a at ha
  by_cases ht : t ≤ 1
  · simp only [ht, ↓reduceIte] at ha ⊢
    funext ω
    have := congrFun ha ω
    simp only [evalTrue, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply] at this ⊢
    rw [this]
  · simp only [ht, ↓reduceIte, LinearMap.id_apply]

omit 𝔼 in
/-- Woodford (2003), p. 506 (counterexample tool): `E_t` of `lateInfo` at dates `t ≤ 1`. -/
theorem lateInfo_E_le {t : ℕ} (ht : t ≤ 1) (y : Bool → ℝ) : lateInfo.E t y = fun _ => y true := by
  change (if t ≤ 1 then evalTrue else LinearMap.id) y = _
  simp only [ht, ↓reduceIte]
  rfl

omit 𝔼 in
/-- Woodford (2003), p. 506 (counterexample tool): `E_t` of `lateInfo` at dates `t ≥ 2`. -/
theorem lateInfo_E_ge {t : ℕ} (ht : 2 ≤ t) (y : Bool → ℝ) : lateInfo.E t y = y := by
  change (if t ≤ 1 then evalTrue else LinearMap.id) y = _
  simp only [show ¬ t ≤ 1 by omega, ↓reduceIte, LinearMap.id_apply]

omit 𝔼 in
/-- Woodford (2003), p. 506 (counterexample tool): the deviation `1` in state `false` from date
`2` on. -/
def devFalse (t : ℕ) (ω : Bool) : ℝ := if 2 ≤ t ∧ ω = false then 1 else 0

omit 𝔼 in
/-- **The `κ = 0` optimum (2.29) is not unique for a general expectation system** (Woodford
(2003), p. 506, fn. 26; the uniqueness of `kappa0_unique_faithful` needs faithfulness). On
`lateInfo` (`β = 1/2`, `σ = λₓ = λᵢ = 1`, `x* = i* = 0`, `rⁿ ≡ 0`, `i_{t₀−1} = 0`), the plan
(2.29) with the first-order-condition gap is optimal, yet the plan with the same interest rate and
output gap raised by `1` in the null state from `t₀ + 1` on is also bounded, adapted, satisfies
(2.23) and the timeless constraint, and has the same expected loss — but is a different plan. -/
theorem kappa0_not_unique :
    ∃ ih : ℕ → Bool → ℝ, ih 0 = 0 ∧ lateInfo.Adapted ih ∧ BoundedProc ih ∧
      NaturalRateCommitment.Eq228 lateInfo (1 / 2) (1 * 1 ^ 2 / 1) 0 ih ∧
      (∀ t, NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih (t + 1) =
        lateInfo.E (t + 1) (NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih (t + 2)) -
          (1 : ℝ) • (ih (t + 1) - (0 : ℕ → Bool → ℝ) (t + 1))) ∧
      (∀ x i : ℕ → Bool → ℝ, BoundedProc x → BoundedProc i →
        (∀ t, x (t + 1) = lateInfo.E (t + 1) (x (t + 2)) -
          (1 : ℝ) • (i (t + 1) - (0 : ℕ → Bool → ℝ) (t + 1))) →
        x 1 = NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih 1 → ∀ ω,
        lateInfo.E 1 (kloss (1 / 2) 1 1 0 0
          (NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih) ih) ω ≤
          lateInfo.E 1 (kloss (1 / 2) 1 1 0 0 x i) ω) ∧
      ∃ x : ℕ → Bool → ℝ, BoundedProc x ∧ lateInfo.Adapted x ∧
        (∀ t, x (t + 1) = lateInfo.E (t + 1) (x (t + 2)) -
          (1 : ℝ) • (ih (t + 1) - (0 : ℕ → Bool → ℝ) (t + 1))) ∧
        x 1 = NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih 1 ∧
        lateInfo.E 1 (kloss (1 / 2) 1 1 0 0 x ih) =
          lateInfo.E 1 (kloss (1 / 2) 1 1 0 0
            (NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih) ih) ∧
        x ≠ NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih := by
  obtain ⟨ih, h0, ha, hb, h228, -, hIS, hopt⟩ :=
    NaturalRateCommitment.optimal_plan_kappa0 lateInfo lateInfo_pullOut (xs := 0) (is := 0)
      (β := 1 / 2) (σ := 1) (lamx := 1) (lami := 1) (M := 0) (B0 := 0) (by norm_num)
      (by norm_num) one_pos one_pos one_pos (rn := 0) (fun _ _ => by simp)
      (fun t => map_zero _) (i0 := 0) (map_zero _) (fun _ => by simp)
  set xh := NaturalRateCommitment.xFromFoc (1 / 2) 1 1 1 0 0 ih with hxh
  refine ⟨ih, h0, ha, hb, h228, hIS, hopt, fun t => xh t + devFalse t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Mh, hMh⟩ := hb
    refine ⟨(Mh + 2 * Mh) + 1, fun t ω => ?_⟩
    simp only [hxh, NaturalRateCommitment.xFromFoc, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, devFalse]
    have h1 := hMh t ω
    have h2 := hMh (t - 1) ω
    have hd : |(if 2 ≤ t ∧ ω = false then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    refine (abs_add_le _ _).trans (add_le_add ?_ hd)
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  · intro t
    have hxa : lateInfo.E t (xh t) = xh t := by
      simp only [hxh, NaturalRateCommitment.xFromFoc, map_add, map_smul, map_sub, lateInfo.const,
        ha t]
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp only [Nat.zero_sub, ha 0]
      · have e : lateInfo.E t (ih (t - 1)) = ih (t - 1) := by
          conv_lhs => rw [← ha (t - 1)]
          rw [lateInfo.known (by omega : t - 1 ≤ t), ha (t - 1)]
        rw [e]
    rw [map_add, hxa]
    congr 1
    by_cases ht : t ≤ 1
    · rw [lateInfo_E_le ht]
      funext ω
      simp only [devFalse]
      simp [show ¬ 2 ≤ t by omega]
    · rw [lateInfo_E_ge (by omega)]
  · intro t
    have h := hIS t
    funext ω
    have hω := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add] at hω ⊢
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [lateInfo_E_le (le_refl 1)] at hω ⊢
      simp only [devFalse]
      norm_num at hω ⊢
      linarith
    · simp only [lateInfo_E_ge (show 2 ≤ t + 1 by omega)] at hω ⊢
      have e1 : 2 ≤ t + 1 := by omega
      have e2 : 2 ≤ t + 1 + 1 := by omega
      simp only [devFalse, e1, e2, true_and]
      linarith
  · funext ω
    change xh 1 ω + devFalse 1 ω = xh 1 ω
    simp [devFalse]
  · rw [lateInfo_E_le (le_refl 1), lateInfo_E_le (le_refl 1)]
    funext ω
    simp only [kloss, Pi.add_apply, devFalse, Bool.true_eq_false, and_false, ↓reduceIte,
      add_zero]
    rfl
  · intro h
    have := congrFun (congrFun h 2) false
    change xh 2 false + devFalse 2 false = xh 2 false at this
    simp only [devFalse] at this
    norm_num at this

end Woodford.GainsFromCommitment.TidyR5NaturalRateKappa
