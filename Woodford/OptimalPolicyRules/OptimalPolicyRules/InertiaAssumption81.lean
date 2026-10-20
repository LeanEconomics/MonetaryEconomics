/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaFOCSystem
import OptimalPolicyRules.InertiaProp8182

/-!
# Assumption 8.1 for the inflation-inertia model

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541) and Proposition 8.2
(p. 555), for the inflation-inertia model of §3.2 (pp. 592–604, `GeneralLinksInertia.inProblem`),
through the general Blanchard–Kahn theorem of Appendix C.1 (`GeneralBKCopy`).

## Main results

* `equil_of_foc`, `foc_of_equil`: solutions of (1.1) + (1.9) from `t₀` with initial conditions
  `Z_{t₀}`, `M_{t₀−1}` are exactly the equilibria of the Blanchard–Kahn system
  `InertiaFOCSystem.Abk` in the state `(w_t, w_{t−1})`, `w = (π, Ξ₂, Ξ₁)`, started at
  `w_{t₀−1} = (Z_{t₀}, M_{t₀−1})` (dates counted from `t₀`, `Prop84General.shiftES`).
* `genericX_Abk`: the genericity condition of Blanchard and Kahn, by strict convexity: a bounded
  deterministic orbit with `w_{−1} = 0` is a first-order plan of the problem with `x* = i* = 0`,
  hence `t₀`-optimal, hence of zero loss (the zero plan is feasible), hence zero.
* `determinate_Abk`: with `InertiaFOCSystem.bk_roots` (no eigenvalue on the unit circle, three in
  the disc) the system is determinate for every expectation system.
* `in_focUnique`: the uniqueness half of Assumption 8.1, for every expectation system, every `t₀`.
* `in_focSolvableMB`, `in_assumption81MB`: **Assumption 8.1 holds for the inflation-inertia model**
  in the corrected form with bounded initial conditions: for every bounded `Z_{t₀}` known at `t₀`
  and every bounded `M_{t₀−1}` known at `t₀ − 1` there is a bounded solution, and it is unique.
* `not_in_focSolvableM`: the boundedness of `Z_{t₀}` cannot be dropped: with an unbounded
  `Z_{t₀} = π_{t₀−1}` there is no bounded plan at all, so `Prop82General.Assumption81M` (which asks
  for every `Z_{t₀}` known at `t₀`) fails on an infinite sample space.
* `in_assumption81M_of_finite`, `in_assumption81_perfectForesight`: on a finite sample space (every
  random variable bounded) the corrected `Assumption81M` holds, and under perfect foresight the
  original `GeneralFOC.LQ.Assumption81`.
* `not_robustlyOptimal`: for the same reason no rule is robustly optimal in the sense of
  `GeneralSetup.RobustlyOptimal` (every initial condition) on an infinite sample space.
* `RobustlyOptimalB`, `prop82M_robustlyOptimalB`: Proposition 8.2 with bounded initial conditions
  (any LQ problem), from `Assumption81MB`; `in_prop82_real_B` and `in_prop82_real_finite`:
  **Proposition 8.2 for the inflation-inertia model in the real case, unconditionally** (the
  hypothesis `Assumption81M` of `InertiaProp8182.in_prop82_real` is discharged).
-/

namespace Woodford.OptimalPolicyRules.InertiaAssumption81

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open IRuleBasic (Calib)
open CubicRoots CubicRoots.Assumptions
open BKInvariantSplit (eigs stableCount NoUnit boundedOrbits GenericX)
open BKForward (mv mv_apply)
open GeneralLinks (piOf xOf iOf piOf_eq xOf_eq)
open GeneralLinksInertia (inSys inProblem in_det_ne Zof Xi1 Xi2 in_foc_at_iff)
open InertiaFOCSystem

variable (c : Calib) (γ : ℝ) {Ω : Type*}

/-! ### From the first-order system to the Blanchard–Kahn equilibrium -/

/-- Woodford (2003), (1.9) at `t₀` (tool): along a solution of (1.1) + (1.9) the initial vector
`w_{t₀−1} = (Z_{t₀}, M_{t₀−1})` is known at `t₀` (from the `x`- and `π`-rows of (1.9) at `t₀`). -/
theorem x0_known_of_foc (hc : c.Adm) (hγ0 : 0 < γ) {𝔼 : ExpectationSystem Ω}
    {cc : ℕ → Ω → Fin 2 → ℝ} {t0 : ℕ} {Z0 : Ω → Unit → ℝ} {M0 : Ω → Fin 2 → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (hs : FOCSystem (inProblem c γ hc hγ0.le) 𝔼 cc t0 Z0 M0 y φ) :
    ∀ k, 𝔼.E t0 (x0Of Z0 M0 k) = x0Of Z0 M0 k := by
  obtain ⟨⟨-, hZ0, -, hya⟩, -, hmφ, hM, hfoc⟩ := hs
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hF := fun ω => (in_foc_at_iff c γ hc hγ0.le 𝔼 y hmφ t0 ω).mp (hfoc t0 le_rfl ω)
  have hka : 𝔼.E t0 (fun ω => φ (t0 + 1) ω (Sum.inr 0)) = fun ω => φ (t0 + 1) ω (Sum.inr 0) :=
    hmφ t0 0
  have hkb : 𝔼.E t0 (fun ω => φ (t0 + 1) ω (Sum.inr 1)) = fun ω => φ (t0 + 1) ω (Sum.inr 1) :=
    hmφ t0 1
  have hkπ : 𝔼.E t0 (piOf y t0) = piOf y t0 := hya t0 (Sum.inl (Sum.inr 0))
  have hkx : 𝔼.E t0 (xOf y t0) = xOf y t0 := hya t0 (Sum.inl (Sum.inr 1))
  have hkZ : 𝔼.E t0 (Zof y t0) = Zof y t0 := hya t0 (Sum.inl (Sum.inl ()))
  have hZ : (fun ω => Z0 ω ()) = Zof y t0 := funext fun ω => (congrFun (hZ0 ω) ()).symm
  -- `M_{t₀−1,1}` from the `x`-row
  have hbm : (fun ω => M0 ω 1) = fun ω => c.β * (-c.κ * φ (t0 + 1) ω (Sum.inr 0) +
      φ (t0 + 1) ω (Sum.inr 1) + c.lx * (xOf y t0 ω - c.xstar)) := by
    funext ω
    have h2 := (hF ω).2.2.1
    simp only [Xi1, Xi2] at h2
    rw [← congrFun (hM ω) 1]
    change φ t0 ω (Sum.inr 1) = _
    field_simp at h2
    linear_combination -h2
  have hkbm : 𝔼.E t0 (fun ω => M0 ω 1) = fun ω => M0 ω 1 := by
    rw [hbm, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add, ExpectationTools.E_fun_add,
      ExpectationTools.E_fun_mul, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_sub, hka,
      hkb, 𝔼.const, hkx]
  -- `M_{t₀−1,0}` from the `π`-row
  have ham : (fun ω => M0 ω 0) = fun ω => 𝔼.E t0 (fun ω' => φ (t0 + 1) ω' (Sum.inl ())) ω +
      (1 + c.β * γ) * φ (t0 + 1) ω (Sum.inr 0) + (piOf y t0 ω - γ * Zof y t0 ω) -
      c.β⁻¹ * c.σ * M0 ω 1 := by
    funext ω
    have h1 := (hF ω).2.1
    simp only [Xi2] at h1
    rw [← congrFun (hM ω) 0, ← congrFun (hM ω) 1]
    change φ t0 ω (Sum.inr 0) = _ + _ + _ - c.β⁻¹ * c.σ * φ t0 ω (Sum.inr 1)
    field_simp at h1 ⊢
    linear_combination -h1
  have hkam : 𝔼.E t0 (fun ω => M0 ω 0) = fun ω => M0 ω 0 := by
    rw [ham, ExpectationTools.E_fun_sub, ExpectationTools.E_fun_add, ExpectationTools.E_fun_add,
      ExpectationTools.E_fun_mul, ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul,
      ExpectationTools.E_fun_mul, 𝔼.E_E_self, hka, hkπ, hkZ, hkbm]
  intro k
  fin_cases k
  · change 𝔼.E t0 (fun ω => Z0 ω ()) = fun ω => Z0 ω ()
    rw [hZ, hkZ]
  · exact hkam
  · exact hkbm

/-- Woodford (2003), §3.2 (tool): `w_{s+1}` of a plan, with the date written `t₀ + s + 1`. -/
theorem wOf_succ (t0 : ℕ) (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ)
    (φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ) (s : ℕ) :
    wOf t0 y φ (s + 1) = ![fun ω => y (s + t0 + 1) ω (Sum.inl (Sum.inr 0)),
      fun ω => φ (s + t0 + 1 + 1) ω (Sum.inr 0), fun ω => φ (s + t0 + 1 + 1) ω (Sum.inr 1)] := by
  simp only [wOf, show s + 1 + t0 = s + t0 + 1 by omega]

/-- **Woodford (2003), (1.1) + (1.9), §3.2, and App. C.1: a solution of the first-order system is
an equilibrium of the Blanchard–Kahn system** in the state `(w_s, w_{s−1})` (dates from `t₀`),
with initial predetermined vector `(Z_{t₀}, M_{t₀−1})`. -/
theorem equil_of_foc (hc : c.Adm) (hγ0 : 0 < γ) {𝔼 : ExpectationSystem Ω}
    {cc : ℕ → Ω → Fin 2 → ℝ} {t0 : ℕ} {Z0 : Ω → Unit → ℝ} {M0 : Ω → Fin 2 → ℝ}
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (hs : FOCSystem (inProblem c γ hc hγ0.le) 𝔼 cc t0 Z0 M0 y φ) :
    GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) (Abk c γ) (forcing c γ cc t0)
      (x0Of Z0 M0) (bkState (x0Of Z0 M0) (wOf t0 y φ)) := by
  have hx0k := x0_known_of_foc c γ hc hγ0 hs
  have hrows := rows_of_foc c γ hc hγ0 hs
  obtain ⟨⟨-, hZ0, hyb, hya⟩, hφb, hmφ, hM, -⟩ := hs
  have hwa : ∀ s k, 𝔼.E (s + t0) (wOf t0 y φ s k) = wOf t0 y φ s k := by
    intro s k
    fin_cases k
    · exact hya (s + t0) (Sum.inl (Sum.inr 0))
    · exact hmφ (s + t0) 0
    · exact hmφ (s + t0) 1
  refine ⟨(solves_bk_iff c γ hc hγ0 _ _ _ _ hwa).mpr fun s ω => ?_, fun s k => ?_,
    fun s j => hwa s j, fun _ => rfl, ?_⟩
  · funext j
    have h := hrows s ω j
    have e1 : (fun k => (Prop84General.shiftES 𝔼 t0).E s (wOf t0 y φ (s + 1) k) ω) =
        ![𝔼.E (s + t0) (fun ω' => y (s + t0 + 1) ω' (Sum.inl (Sum.inr 0))) ω,
          𝔼.E (s + t0) (fun ω' => φ (s + t0 + 1 + 1) ω' (Sum.inr 0)) ω,
          𝔼.E (s + t0) (fun ω' => φ (s + t0 + 1 + 1) ω' (Sum.inr 1)) ω] := by
      rw [wOf_succ]
      funext k
      fin_cases k <;> rfl
    have e2 : (fun k => Fvec c cc t0 s k ω) =
        ![cc (s + t0) ω 0 - c.κ * c.xstar, c.σ * c.istar + cc (s + t0) ω 1, 0] := by
      funext k
      fin_cases k <;> rfl
    rw [e1, e2]
    exact h
  · rcases k with k | k
    · exact hwa s k
    · cases s with
      | zero =>
        change 𝔼.E (0 + t0) (x0Of Z0 M0 k) = x0Of Z0 M0 k
        rw [zero_add]
        exact hx0k k
      | succ s => exact ForwardSolution.E_of_known 𝔼 (by omega) (hwa s k)
  · obtain ⟨My, hMy⟩ := hyb
    obtain ⟨Mφ, hMφ⟩ := hφb
    refine ⟨max My Mφ, fun s k ω => ?_⟩
    have hw : ∀ s k, |wOf t0 y φ s k ω| ≤ max My Mφ := by
      intro s k
      fin_cases k
      · exact (hMy _ ω _).trans (le_max_left _ _)
      · exact (hMφ _ ω _).trans (le_max_right _ _)
      · exact (hMφ _ ω _).trans (le_max_right _ _)
    rcases k with k | k
    · exact hw s k
    · cases s with
      | zero =>
        fin_cases k
        · change |Z0 ω ()| ≤ _
          rw [← congrFun (hZ0 ω) ()]
          exact (hMy _ ω _).trans (le_max_left _ _)
        · change |M0 ω 0| ≤ _
          rw [← congrFun (hM ω) 0]
          exact (hMφ _ ω _).trans (le_max_right _ _)
        · change |M0 ω 1| ≤ _
          rw [← congrFun (hM ω) 1]
          exact (hMφ _ ω _).trans (le_max_right _ _)
      | succ s => exact hw s k

/-- Woodford (2003), App. C.1 (uniqueness by linearity): under determinacy, two equilibria with
the same forcing and the same initial vector coincide (their difference is an equilibrium of the
homogeneous system started at `0`, and so is `0`). The forcing need not be bounded. -/
theorem equil_unique {Z X : Type*} [Fintype Z] [Fintype X]
    {𝔼 : ExpectationSystem Ω} {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hdet : GeneralBKCopy.Determinate 𝔼 A) {w : ℕ → Z ⊕ X → Ω → ℝ} {x0 : X → Ω → ℝ}
    {Y Y' : ℕ → Z ⊕ X → Ω → ℝ} (h : GeneralBKCopy.Equil 𝔼 A w x0 Y)
    (h' : GeneralBKCopy.Equil 𝔼 A w x0 Y') : Y = Y' := by
  obtain ⟨hs, ha, hk, h0, hb⟩ := h
  obtain ⟨hs', ha', hk', h0', hb'⟩ := h'
  have hz : ∃! Y0, GeneralBKCopy.Equil 𝔼 A (fun _ _ => 0) (fun _ => 0) Y0 :=
    hdet _ ⟨0, fun _ _ _ => by simp⟩ (fun t i => 𝔼.const t 0) _ (fun _ => 𝔼.const 0 0)
      ⟨0, fun _ _ => by simp⟩
  have hD : GeneralBKCopy.Equil 𝔼 A (fun _ _ => 0) (fun _ => 0) (fun t => Y t - Y' t) := by
    refine ⟨fun t i => ?_, fun t i => ?_, fun t j => ?_, fun j => ?_, ?_⟩
    · have e1 := hs t i
      have e2 := hs' t i
      change 𝔼.E t (Y (t + 1) i - Y' (t + 1) i) = mv A (fun k => Y t k - Y' t k) i + 0
      rw [map_sub, e1, e2, add_zero, show (fun k => Y t k - Y' t k) = Y t - Y' t from rfl,
        BKForward.mv_sub]
      simp
    · change 𝔼.E t (Y t i - Y' t i) = Y t i - Y' t i
      rw [map_sub, ha t i, ha' t i]
    · change 𝔼.E t (Y (t + 1) (Sum.inr j) - Y' (t + 1) (Sum.inr j)) = _
      rw [map_sub, hk t j, hk' t j]
      rfl
    · change Y 0 (Sum.inr j) - Y' 0 (Sum.inr j) = fun _ => 0
      rw [h0 j, h0' j, sub_self]
      rfl
    · obtain ⟨M1, hM1⟩ := hb
      obtain ⟨M2, hM2⟩ := hb'
      exact ⟨M1 + M2, fun t i ω => (abs_sub _ _).trans (add_le_add (hM1 t i ω) (hM2 t i ω))⟩
  have hZ : GeneralBKCopy.Equil 𝔼 A (fun _ _ => 0) (fun _ => 0) (fun _ => 0) := by
    refine ⟨fun t i => ?_, fun t i => 𝔼.const t 0, fun t j => 𝔼.const t 0, fun j => rfl,
      ⟨0, fun _ _ _ => by simp⟩⟩
    change 𝔼.E t (fun _ => 0) = mv A (fun _ => fun _ => 0) i + 0
    rw [𝔼.const, add_zero]
    funext ω
    simp [BKForward.mv]
  have e := hz.unique hD hZ
  funext t i ω
  have := congrFun (congrFun (congrFun e t) i) ω
  simpa [sub_eq_zero] using this

/-! ### From the Blanchard–Kahn equilibrium to the first-order system -/

/-- Woodford (2003), App. C.1 (tool): in an equilibrium of the Blanchard–Kahn system the lagged
block is the lag of the current block, `y = (w_s, w_{s−1})` with `w_{−1} = x₀`. -/
theorem equil_eq_bkState {𝔼' : ExpectationSystem Ω} {wf : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ}
    {x0 : Fin 3 → Ω → ℝ} {Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil 𝔼' (Abk c γ) wf x0 Y) (hw : ∀ s j, wf s (Sum.inr j) = 0) :
    Y = bkState x0 (fun s k => Y s (Sum.inl k)) := by
  obtain ⟨hs, -, hk, h0, -⟩ := hY
  funext s k
  rcases k with k | k
  · rfl
  · cases s with
    | zero => exact h0 k
    | succ s =>
      change Y (s + 1) (Sum.inr k) = Y s (Sum.inl k)
      rw [← hk s k, hs s (Sum.inr k), hw s k, add_zero]
      have := congrFun (GeneralBKCopy.mv_inr (Abk c γ) (Y s)) k
      rw [this, Abk, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, BKForward.mv_one]
      funext ω
      simp [BKForward.mv]

/-- **Woodford (2003), App. C.1 and (1.1) + (1.9), §3.2: an equilibrium of the Blanchard–Kahn
system gives a solution of the first-order system** (the plan `yC` and multipliers `φC` read off
its current block), when `M_{t₀−1}` is known at `t₀ − 1`. -/
theorem foc_of_equil (hc : c.Adm) (hγ0 : 0 < γ) {𝔼 : ExpectationSystem Ω}
    {cc : ℕ → Ω → Fin 2 → ℝ} {t0 : ℕ} {Z0 : Ω → Unit → ℝ} {M0 : Ω → Fin 2 → ℝ}
    (hM0k : KnownV 𝔼 (t0 - 1) M0) {Y : ℕ → Fin 3 ⊕ Fin 3 → Ω → ℝ}
    (hY : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) (Abk c γ) (forcing c γ cc t0)
      (x0Of Z0 M0) Y) :
    FOCSystem (inProblem c γ hc hγ0.le) 𝔼 cc t0 Z0 M0
      (yC c t0 (x0Of Z0 M0) (fun s k => Y s (Sum.inl k)))
      (φC c γ t0 (x0Of Z0 M0) (fun s k => Y s (Sum.inl k))) := by
  set w : ℕ → Fin 3 → Ω → ℝ := fun s k => Y s (Sum.inl k) with hwdef
  have hYeq := equil_eq_bkState c γ hY (fun _ _ => rfl)
  obtain ⟨hs, ha, -, -, hb⟩ := hY
  have hwa : ∀ s k, 𝔼.E (s + t0) (w s k) = w s k := fun s k => ha s (Sum.inl k)
  rw [hYeq] at hs ha hb
  refine foc_of_rows c γ hc hγ0 hM0k hwa (fun k => ?_) ?_
    ((solves_bk_iff c γ hc hγ0 _ _ w _ hwa).mp hs)
  · have := ha 0 (Sum.inr k)
    change 𝔼.E (0 + t0) (x0Of Z0 M0 k) = x0Of Z0 M0 k at this
    rwa [zero_add] at this
  · obtain ⟨B, hB⟩ := hb
    exact ⟨B, fun s k ω => ⟨hB s (Sum.inl k) ω, hB s (Sum.inr k) ω⟩⟩

/-! ### Genericity, by strict convexity -/

/-- Woodford (2003), §3.2 (tool): the calibration with the targets `x* = i* = 0`. -/
def calib0 : Calib := ⟨c.β, c.σ, c.κ, c.lx, c.li, 0, 0⟩

/-- Woodford (2003), (3.14), p. 592: the targets `τ = T y = (π − γZ, x, i)` of the inertia
problem. -/
theorem T_inProblem (hc : c.Adm) (hγ : 0 ≤ γ) (v : (Unit ⊕ Fin 2) ⊕ Unit → ℝ) :
    (inProblem c γ hc hγ).T *ᵥ v =
      ![-γ * v (Sum.inl (Sum.inl ())) + v (Sum.inl (Sum.inr 0)), v (Sum.inl (Sum.inr 1)),
        v (Sum.inr ())] := by
  funext a
  fin_cases a <;>
    simp [inProblem, GeneralLinksInertia.inTtil, LQProblem.T, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two]

/-- **Woodford (2003), App. C.1, fn. 2 (the genericity condition) for the inflation-inertia
first-order system: the stable subspace of `A` meets `{w_{−1} = 0}` only in `0`.** A bounded
deterministic orbit starting with `w_{−1} = 0` is a solution of (1.1) + (1.9) under perfect
foresight with `Z_{t₀} = 0`, `M_{t₀−1} = 0`, no disturbance and targets `x* = i* = 0`
(`foc_of_equil`), hence `t₀`-optimal (Lagrangian sufficiency); the zero plan is feasible with
zero loss, so by strict convexity (`W ≻ 0`) the orbit has `π − γZ = x = i = 0`, which forces
`w_0 = 0`. -/
theorem genericX_Abk (hc : c.Adm) (hγ0 : 0 < γ) : GenericX (Abk c γ) := by
  intro v hv hx
  obtain ⟨C, hC⟩ := hv
  set c0 := calib0 c with hc0def
  have hc0 : c0.Adm := hc
  set Y : ℕ → Fin 3 ⊕ Fin 3 → Unit → ℝ := fun s k _ => (Abk c γ ^ s *ᵥ v) k with hYdef
  set cc0 : ℕ → Unit → Fin 2 → ℝ := fun _ _ _ => 0 with hcc0
  have hforce : forcing c0 γ cc0 0 = fun _ _ _ => 0 := by
    funext s k ω
    rcases k with k | k
    · simp only [forcing, Sum.elim_inl, mv_apply]
      have : (fun j => Fvec c0 cc0 0 s j ω) = 0 := by
        funext j
        fin_cases j <;> simp [Fvec, hc0def, calib0, hcc0]
      rw [this, mulVec_zero]
      rfl
    · rfl
  have hEq : GeneralBKCopy.Equil (Prop84General.shiftES perfectForesight 0) (Abk c0 γ)
      (forcing c0 γ cc0 0) (x0Of 0 0) Y := by
    refine ⟨fun s k => ?_, fun s k => rfl, fun s j => rfl, fun j => ?_,
      ⟨C, fun s k _ => hC s k⟩⟩
    · rw [hforce]
      funext ω
      change (Abk c γ ^ (s + 1) *ᵥ v) k = mv (Abk c γ) (Y s) k ω + 0
      rw [mv_apply, pow_succ', ← mulVec_mulVec, add_zero]
    · funext ω
      change (Abk c γ ^ 0 *ᵥ v) (Sum.inr j) = x0Of 0 0 j ω
      rw [pow_zero, one_mulVec, hx j]
      fin_cases j <;> rfl
  set w : ℕ → Fin 3 → Unit → ℝ := fun s k => Y s (Sum.inl k) with hwdef
  have hfoc := foc_of_equil c0 γ hc0 hγ0 (𝔼 := perfectForesight) (cc := cc0)
    (t0 := 0) (Z0 := 0) (M0 := 0) (fun _ => rfl) hEq
  set P0 := inProblem c0 γ hc0 hγ0.le with hP0
  set yv := yC c0 0 (x0Of 0 0) w with hyv
  set φv := φC c0 γ 0 (x0Of 0 0) w with hφv
  have hopt := t0Optimal_of_focSystem_perfectForesight P0 hfoc
  -- the zero plan
  set y0 : ℕ → Unit → (Unit ⊕ Fin 2) ⊕ Unit → ℝ := fun _ _ _ => 0 with hy0
  have hz0 : P0.Feasible perfectForesight cc0 0 0 y0 := by
    refine ⟨fun t _ ω => (in_struct_at c0 γ hc0 hγ0.le perfectForesight _ y0 t ω).mpr ?_,
      fun ω => rfl, ⟨0, fun _ _ _ => by simp [hy0]⟩, fun t i => rfl⟩
    simp only [hy0, Zof, piOf, xOf, iOf]
    refine ⟨trivial, ?_, ?_⟩
    · change c0.β * 0 = _
      ring
    · change c0.σ * 0 + 0 = _
      ring
  -- losses
  have hτ : P0.τstar = 0 := by
    funext a
    fin_cases a <;> rfl
  have hJ0 : Jfn perfectForesight P0.β P0.T P0.W P0.τstar 0 y0 () = 0 := by
    change ∑' k, P0.β ^ k * lossFn P0.T P0.W P0.τstar (y0 (0 + k) ()) = 0
    have hl0 : ∀ k, lossFn P0.T P0.W P0.τstar (y0 (0 + k) ()) = 0 := by
      intro k
      rw [show y0 (0 + k) () = 0 from rfl]
      simp [lossFn, quad, hτ]
    rw [show (fun k => P0.β ^ k * lossFn P0.T P0.W P0.τstar (y0 (0 + k) ())) = fun _ => 0 from
      funext fun k => by rw [hl0 k, mul_zero], tsum_zero]
  have hJnn : 0 ≤ Jfn perfectForesight P0.β P0.T P0.W P0.τstar 0 yv () := by
    change 0 ≤ ∑' k, P0.β ^ k * lossFn P0.T P0.W P0.τstar (yv (0 + k) ())
    exact tsum_nonneg fun k => mul_nonneg (pow_nonneg P0.β_pos.le k)
      (quad_nonneg P0.W_posDef.posSemidef _)
  have hJle : Jfn perfectForesight P0.β P0.T P0.W P0.τstar 0 yv () ≤
      Jfn perfectForesight P0.β P0.T P0.W P0.τstar 0 y0 () := hopt.2 y0 hz0 ()
  have hinit : ∀ ω, φv 0 ω ⬝ᵥ (P0.sys.Itil *ᵥ (y0 0 ω - yv 0 ω)) = 0 := by
    intro ω
    have hM := hfoc.2.2.2.1 ω
    have hZ := (yC_at c0 0 (x0Of 0 0) w 0 ω).2.1
    rw [P0.sys.Itil_mulVec, dotProduct, Fintype.sum_sum_type]
    have h1 : ∀ r, φv 0 ω (Sum.inr r) = 0 := fun r => congrFun hM r
    simp only [Sum.elim_inl, Sum.elim_inr, h1, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_eq_zero fun u _ => ?_
    have : Zpart (y0 0 ω - yv 0 ω) u = 0 := by
      change 0 - Zof yv (0 + 0) ω = 0
      rw [hZ]
      simp [lagW, x0Of]
    rw [this, mul_zero]
  have hT := targets_eq_of_J_eq perfectForesight_pullOut
    ExpectationTools.perfectForesight_faithful P0.β_pos P0.β_lt_one P0.W_posDef
    ((structural_iff P0.sys perfectForesight _ 0 y0).mp hz0.1)
    ((structural_iff P0.sys perfectForesight _ 0 yv).mp hfoc.1.1) hz0.2.2.2 hfoc.1.2.2.2
    hz0.2.2.1 hfoc.1.2.2.1 hfoc.2.1 hfoc.2.2.1 hfoc.2.2.2.2 hinit
    (fun ω => le_antisymm (by rw [hJ0]; exact hJnn) (by exact hJle)) 0 le_rfl ()
  rw [T_inProblem, T_inProblem] at hT
  obtain ⟨y1, y2, y3, y4⟩ := yC_at c0 0 (x0Of 0 0) w 0 ()
  simp only [zero_add] at y1 y2 y3 y4
  have e0 := congrFun hT 0
  have e1 := congrFun hT 1
  have e2 := congrFun hT 2
  simp only [hy0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  change -γ * 0 + 0 = -γ * Zof yv 0 () + piOf yv 0 () at e0
  change 0 = xOf yv 0 () at e1
  change 0 = iOf yv 0 () at e2
  rw [y1, y2] at e0
  rw [y3] at e1
  rw [y4] at e2
  have hl : ∀ k, lagW (x0Of 0 0) w 0 k () = 0 := by
    intro k
    fin_cases k <;> rfl
  rw [hl] at e0 e1
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hlx : c.lx ≠ 0 := hc.2.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hκ : c.κ ≠ 0 := hc.2.2.2.1.ne'
  have w0 : w 0 0 () = 0 := by linarith
  have w2 : w 0 2 () = 0 := by
    change 0 = 0 - c.σ / c.li * w 0 2 () at e2
    have : c.σ / c.li * w 0 2 () = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (div_ne_zero hσ hli)
  have w1 : w 0 1 () = 0 := by
    change 0 = 0 + c.lx⁻¹ * (c.κ * w 0 1 () - w 0 2 () + c.β⁻¹ * 0) at e1
    rw [w2] at e1
    have : c.lx⁻¹ * c.κ * w 0 1 () = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (inv_ne_zero hlx) hκ)
  funext k
  rcases k with k | k
  · have hv0 : ∀ k, v (Sum.inl k) = w 0 k () := by
      intro k
      change v (Sum.inl k) = (Abk c γ ^ 0 *ᵥ v) (Sum.inl k)
      rw [pow_zero, one_mulVec]
    rw [hv0]
    fin_cases k
    · exact w0
    · exact w1
    · exact w2
  · exact hx k

/-! ### Determinacy and Assumption 8.1 -/

/-- **Woodford (2003), App. C.1 (Blanchard–Kahn) for the inflation-inertia first-order system:
determinacy for every expectation system.** No eigenvalue of `A` on the unit circle, a stable
subspace of dimension `3` (the predetermined block) and genericity (`GeneralBKCopy.determinate_of`
with `InertiaFOCSystem.bk_roots`, `finrank_Abk`, `genericX_Abk`). -/
theorem determinate_Abk (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼' : ExpectationSystem Ω) :
    GeneralBKCopy.Determinate 𝔼' (Abk c γ) :=
  GeneralBKCopy.determinate_of 𝔼' (bk_roots c γ hc hγ0 hγ1).1 (finrank_Abk c γ hc hγ0 hγ1)
    (genericX_Abk c γ hc hγ0)

/-- **Woodford (2003), Assumption 8.1 (uniqueness), p. 541, for the inflation-inertia model**:
two bounded solutions of (1.1) + (1.9) with the same disturbance and the same initial conditions
`Z_{t₀}`, `M_{t₀−1}` coincide from `t₀` on (any expectation system, any `t₀`, any disturbance). -/
theorem in_focUnique (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : FOCUnique (inProblem c γ hc hγ0.le) 𝔼 t0 := by
  intro cc Z0 M0 y y' φ φ' hs hs'
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hlx : c.lx ≠ 0 := hc.2.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  have hY := equil_unique (determinate_Abk c γ hc hγ0 hγ1 (Prop84General.shiftES 𝔼 t0))
    (equil_of_foc c γ hc hγ0 hs) (equil_of_foc c γ hc hγ0 hs')
  have hw : ∀ s k ω, wOf t0 y φ s k ω = wOf t0 y' φ' s k ω := fun s k ω =>
    congrFun (congrFun (congrFun hY s) (Sum.inl k)) ω
  obtain ⟨⟨hstr, hZ0, -, -⟩, -, hmφ, hM, hfoc⟩ := hs
  obtain ⟨⟨hstr', hZ0', -, -⟩, -, hmφ', hM', hfoc'⟩ := hs'
  -- inflation and the multipliers `M`
  have hπ : ∀ s ω, piOf y (s + t0) ω = piOf y' (s + t0) ω := fun s ω => hw s 0 ω
  have ha : ∀ s ω, φ (s + t0 + 1) ω (Sum.inr 0) = φ' (s + t0 + 1) ω (Sum.inr 0) :=
    fun s ω => hw s 1 ω
  have hb : ∀ s ω, φ (s + t0 + 1) ω (Sum.inr 1) = φ' (s + t0 + 1) ω (Sum.inr 1) :=
    fun s ω => hw s 2 ω
  have hMl : ∀ s ω r, φ (s + t0) ω (Sum.inr r) = φ' (s + t0) ω (Sum.inr r) := by
    intro s ω r
    cases s with
    | zero =>
      rw [zero_add]
      exact (congrFun (hM ω) r).trans (congrFun (hM' ω) r).symm
    | succ s =>
      rw [show s + 1 + t0 = s + t0 + 1 by omega]
      fin_cases r
      · exact ha s ω
      · exact hb s ω
  have hZ : ∀ s ω, Zof y (s + t0) ω = Zof y' (s + t0) ω := by
    intro s ω
    cases s with
    | zero =>
      rw [zero_add]
      exact (congrFun (hZ0 ω) ()).trans (congrFun (hZ0' ω) ()).symm
    | succ s =>
      rw [show s + 1 + t0 = s + t0 + 1 by omega,
        ((in_struct_at c γ hc hγ0.le 𝔼 cc y (s + t0) ω).mp (hstr _ (by omega) ω)).1,
        ((in_struct_at c γ hc hγ0.le 𝔼 cc y' (s + t0) ω).mp (hstr' _ (by omega) ω)).1]
      exact hπ s ω
  intro t ht
  obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
  have F := fun ω => (in_foc_at_iff c γ hc hγ0.le 𝔼 y hmφ (s + t0) ω).mp (hfoc _ ht ω)
  have F' := fun ω => (in_foc_at_iff c γ hc hγ0.le 𝔼 y' hmφ' (s + t0) ω).mp (hfoc' _ ht ω)
  have hx : ∀ ω, xOf y (s + t0) ω = xOf y' (s + t0) ω := by
    intro ω
    have h2 := (F ω).2.2.1
    have h2' := (F' ω).2.2.1
    simp only [Xi1, Xi2] at h2 h2'
    rw [lin_solve hlx (show c.lx * (xOf y (s + t0) ω - c.xstar) = c.κ *
        φ (s + t0 + 1) ω (Sum.inr 0) - φ (s + t0 + 1) ω (Sum.inr 1) +
          c.β⁻¹ * φ (s + t0) ω (Sum.inr 1) by linarith),
      lin_solve hlx (show c.lx * (xOf y' (s + t0) ω - c.xstar) = c.κ *
        φ' (s + t0 + 1) ω (Sum.inr 0) - φ' (s + t0 + 1) ω (Sum.inr 1) +
          c.β⁻¹ * φ' (s + t0) ω (Sum.inr 1) by linarith),
      ha s ω, hb s ω, hMl s ω 1]
  have hi : ∀ ω, iOf y (s + t0) ω = iOf y' (s + t0) ω := by
    intro ω
    have h3 := (F ω).2.2.2
    have h3' := (F' ω).2.2.2
    simp only [Xi1] at h3 h3'
    rw [lin_solve hli (show c.li * (iOf y (s + t0) ω - c.istar) =
        -(c.σ * φ (s + t0 + 1) ω (Sum.inr 1)) by linarith),
      lin_solve hli (show c.li * (iOf y' (s + t0) ω - c.istar) =
        -(c.σ * φ' (s + t0 + 1) ω (Sum.inr 1)) by linarith), hb s ω]
  have hξ : ∀ ω, φ (s + t0) ω (Sum.inl ()) = φ' (s + t0) ω (Sum.inl ()) := by
    intro ω
    have h0 := (F ω).1
    have h0' := (F' ω).1
    simp only [Xi2] at h0 h0'
    rw [ha s ω, hπ s ω, hZ s ω] at h0
    have : c.β⁻¹ * (φ (s + t0) ω (Sum.inl ()) - φ' (s + t0) ω (Sum.inl ())) = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (inv_ne_zero hβ))
  refine ⟨funext fun ω => funext fun i => ?_, funext fun ω => funext fun r => ?_⟩
  · rcases i with (u | j) | u
    · exact hZ s ω
    · fin_cases j
      · exact hπ s ω
      · exact hx ω
    · exact hi ω
  · rcases r with u | r
    · exact hξ ω
    · exact hMl s ω r

/-- Woodford (2003), Assumption 8.1, p. 541 (existence half), **corrected for predetermined
variables**: (1.1) + (1.9) has a bounded solution for every bounded adapted disturbance, every
**bounded** `Z_{t₀}` known at `t₀` and every bounded `M_{t₀−1}` known at `t₀ − 1`. (A bounded
plan has a bounded `Z_{t₀}`, so the boundedness of `Z_{t₀}` cannot be dropped:
`not_in_focSolvableM`.) -/
def FOCSolvableMB {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
    [DecidableEq ιz] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Prop :=
  ∀ (cc : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ), BoundedV cc → AdaptedV 𝔼 cc →
    KnownV 𝔼 t0 Z0 → (∃ K, ∀ ω j, |Z0 ω j| ≤ K) → (∃ K, ∀ ω r, |M0 ω r| ≤ K) →
      KnownV 𝔼 (t0 - 1) M0 → ∃ y φ, FOCSystem P 𝔼 cc t0 Z0 M0 y φ

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), Assumption 8.1, p. 541, **corrected for predetermined variables**: existence
for bounded initial conditions (`FOCSolvableMB`) and uniqueness (`GeneralFOC.LQ.FOCUnique`). -/
structure Assumption81MB (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) where
  solvable : FOCSolvableMB P 𝔼 t0
  unique : FOCUnique P 𝔼 t0

/-- Woodford (2003), Assumption 8.1, p. 541: the corrected `Prop82General.Assumption81M` implies
the bounded-initial-condition form. -/
theorem Assumption81MB.of_assumption81M {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (hA : Prop82General.Assumption81M P 𝔼 t0) : Assumption81MB P 𝔼 t0 :=
  ⟨fun cc Z0 M0 hb ha hZ _ hMb hMk => hA.solvable cc Z0 M0 hb ha hZ hMb hMk, hA.unique⟩

/-- **Woodford (2003), Assumption 8.1 (existence), p. 541, for the inflation-inertia model**: for
every bounded adapted disturbance, every bounded `Z_{t₀}` known at `t₀` and every bounded
`M_{t₀−1}` known at `t₀ − 1`, (1.1) + (1.9) has a bounded solution (any expectation system, any
`t₀`): the equilibrium of the Blanchard–Kahn system (`determinate_Abk`) read back through
`foc_of_equil`. -/
theorem in_focSolvableMB (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : FOCSolvableMB (inProblem c γ hc hγ0.le) 𝔼 t0 := by
  intro cc Z0 M0 hcb hca hZk hZb hMb hMk
  set 𝔼' := Prop84General.shiftES 𝔼 t0 with h𝔼'
  have hFb : BKForward.BoundedV (Fvec c cc t0) := by
    obtain ⟨Mc, hMc⟩ := hcb
    refine ⟨|Mc| + |c.κ * c.xstar| + |c.σ * c.istar|, fun s k ω => ?_⟩
    have h0 := hMc (s + t0) ω 0
    have h1 := hMc (s + t0) ω 1
    have := le_abs_self Mc
    fin_cases k
    · change |cc (s + t0) ω 0 - c.κ * c.xstar| ≤ _
      have := abs_sub (cc (s + t0) ω 0) (c.κ * c.xstar)
      linarith [abs_nonneg (c.σ * c.istar)]
    · change |c.σ * c.istar + cc (s + t0) ω 1| ≤ _
      have := abs_add_le (c.σ * c.istar) (cc (s + t0) ω 1)
      linarith [abs_nonneg (c.κ * c.xstar)]
    · change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      positivity
  have hFa : BKForward.AdaptedV 𝔼' (Fvec c cc t0) := by
    intro s k
    fin_cases k
    · change 𝔼.E (s + t0) (fun ω => cc (s + t0) ω 0 - c.κ * c.xstar) =
        fun ω => cc (s + t0) ω 0 - c.κ * c.xstar
      rw [ExpectationTools.E_fun_sub, hca (s + t0) 0, 𝔼.const]
    · change 𝔼.E (s + t0) (fun ω => c.σ * c.istar + cc (s + t0) ω 1) =
        fun ω => c.σ * c.istar + cc (s + t0) ω 1
      rw [ExpectationTools.E_fun_add, hca (s + t0) 1, 𝔼.const]
    · exact 𝔼.const (s + t0) 0
  have hwb : BKForward.BoundedV (forcing c γ cc t0) := by
    obtain ⟨B, hB⟩ := BKForward.boundedV_mv (Pm c γ)⁻¹ hFb
    refine ⟨max B 0, fun s k ω => ?_⟩
    rcases k with k | k
    · exact (hB s k ω).trans (le_max_left _ _)
    · change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      exact le_max_right _ _
  have hwa : BKForward.AdaptedV 𝔼' (forcing c γ cc t0) := by
    intro s k
    rcases k with k | k
    · exact BKForward.adaptedV_mv 𝔼' (Pm c γ)⁻¹ hFa s k
    · exact 𝔼'.const s 0
  have hx0k : ∀ j, 𝔼'.E 0 (x0Of Z0 M0 j) = x0Of Z0 M0 j := by
    have hM' := KnownV.mono 𝔼 (Nat.sub_le t0 1) hMk
    intro j
    change 𝔼.E (0 + t0) _ = _
    rw [zero_add]
    fin_cases j
    · exact hZk ()
    · exact hM' 0
    · exact hM' 1
  have hx0b : ∃ K, ∀ j ω, |x0Of Z0 M0 j ω| ≤ K := by
    obtain ⟨K1, hK1⟩ := hZb
    obtain ⟨K2, hK2⟩ := hMb
    refine ⟨max K1 K2, fun j ω => ?_⟩
    fin_cases j
    · exact (hK1 ω ()).trans (le_max_left _ _)
    · exact (hK2 ω 0).trans (le_max_right _ _)
    · exact (hK2 ω 1).trans (le_max_right _ _)
  obtain ⟨Y, hY, -⟩ := determinate_Abk c γ hc hγ0 hγ1 𝔼' _ hwb hwa _ hx0k hx0b
  exact ⟨_, _, foc_of_equil c γ hc hγ0 hMk hY⟩

/-- **Woodford (2003), Assumption 8.1, p. 541, holds for the inflation-inertia model** (corrected
for the predetermined variable, `Assumption81MB`): for every expectation system, every `t₀`,
every bounded adapted disturbance and all bounded initial conditions `Z_{t₀}` (known at `t₀`) and
`M_{t₀−1}` (known at `t₀ − 1`), (1.1) + (1.9) has exactly one bounded solution. -/
theorem in_assumption81MB (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : Assumption81MB (inProblem c γ hc hγ0.le) 𝔼 t0 :=
  ⟨in_focSolvableMB c γ hc hγ0 hγ1 𝔼 t0, in_focUnique c γ hc hγ0 hγ1 𝔼 t0⟩

/-- **Woodford (2003), Assumption 8.1, p. 541, for the inflation-inertia model on a finite sample
space** (every random variable is bounded): the corrected `Prop82General.Assumption81M` holds —
in particular on every finite event tree (`ExpectationsFiniteTree`). -/
theorem in_assumption81M_of_finite [Finite Ω] (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Prop82General.Assumption81M (inProblem c γ hc hγ0.le) 𝔼 t0 := by
  have := Fintype.ofFinite Ω
  refine ⟨fun cc Z0 M0 hb ha hZ hMb hMk => in_focSolvableMB c γ hc hγ0 hγ1 𝔼 t0 cc Z0 M0 hb ha hZ
    ⟨∑ ω, |Z0 ω ()|, fun ω u => ?_⟩ hMb hMk, in_focUnique c γ hc hγ0 hγ1 𝔼 t0⟩
  exact Finset.single_le_sum (f := fun ω => |Z0 ω ()|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ ω)

/-- **Woodford (2003), Assumption 8.1, p. 541, for the inflation-inertia model under perfect
foresight**, in the original formalisation `GeneralFOC.LQ.Assumption81` (on the one-point sample
space every initial condition is known and bounded). -/
theorem in_assumption81_perfectForesight (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (t0 : ℕ) :
    Assumption81 (inProblem c γ hc hγ0.le) perfectForesight t0 := by
  have hA := in_assumption81M_of_finite c γ hc hγ0 hγ1 perfectForesight t0
  refine ⟨fun cc Z0 M0 hcb hca hZ0 _ => ?_, hA.unique⟩
  exact hA.solvable cc Z0 M0 hcb hca hZ0
    ⟨|M0 () 0| + |M0 () 1|, fun ω r => by
      rcases ω
      fin_cases r
      · simp
      · simp⟩ (fun _ => rfl)

/-! ### Unbounded initial conditions -/

/-- Woodford (2003), p. 540 (tool): complete information, `E_t x = x` at every date, on any sample
space (perfect foresight is the one-point case). -/
def fullInfo (Ω : Type*) : ExpectationSystem Ω where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- **Woodford (2003), Assumption 8.1, p. 541: the boundedness of `Z_{t₀}` cannot be dropped.**
With complete information on `ℕ` and the unbounded initial condition `Z_{t₀}(n) = n` (known at
`t₀`), no bounded plan satisfies `Z_{t₀} = Z₀`, so `Prop82General.FOCSolvableM` — which asks for
a bounded solution for every `Z_{t₀}` known at `t₀` — fails for the inflation-inertia model (and
for every problem with a predetermined variable). -/
theorem not_in_focSolvableM (hc : c.Adm) (hγ : 0 ≤ γ) (t0 : ℕ) :
    ¬ Prop82General.FOCSolvableM (inProblem c γ hc hγ) (fullInfo ℕ) t0 := by
  intro h
  obtain ⟨y, φ, hs⟩ := h (fun _ _ _ => 0) (fun n _ => (n : ℝ)) (fun _ _ => 0)
    ⟨0, fun _ _ _ => by simp⟩ (fun _ _ => rfl) (fun _ => rfl) ⟨0, fun _ _ => by simp⟩
    (fun _ => rfl)
  obtain ⟨⟨-, hZ0, ⟨M, hM⟩, -⟩, -⟩ := hs
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have h1 := hM t0 n (Sum.inl (Sum.inl ()))
  have h2 := congrFun (hZ0 n) ()
  change y t0 n (Sum.inl (Sum.inl ())) = (n : ℝ) at h2
  rw [h2, abs_of_nonneg (Nat.cast_nonneg n)] at h1
  linarith

/-- Woodford (2003), Assumption 8.1, p. 541: hence the corrected formalisation
`Prop82General.Assumption81M` fails for the inflation-inertia model on an infinite sample space,
and `Assumption81MB` (bounded initial conditions) is the right form. -/
theorem not_in_assumption81M (hc : c.Adm) (hγ : 0 ≤ γ) (t0 : ℕ) :
    ¬ Prop82General.Assumption81M (inProblem c γ hc hγ) (fullInfo ℕ) t0 :=
  fun h => not_in_focSolvableM c γ hc hγ t0 h.solvable

/-- **Woodford (2003), Definition, pp. 549–550, (1.16): robust optimality for every initial
condition is impossible for the inflation-inertia model on an infinite sample space.** With
complete information on `ℕ` and `Z_{t₀}(n) = n`, no rule at all determines a bounded feasible
plan; hence `RobustlyOptimalB` (bounded initial conditions) below. -/
theorem not_robustlyOptimal (hc : c.Adm) (hγ : 0 ≤ γ) (t0 : ℕ) {κ : Type*} [Fintype κ]
    (Rl : (ℕ → ℕ → Fin 2 → ℝ) → (ℕ → ℕ → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → ℕ → Fin 2 → ℝ) → (ℕ → ℕ → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) → ℕ → ℕ → κ → ℝ) :
    ¬ RobustlyOptimal (inProblem c γ hc hγ) (fullInfo ℕ) t0 Rl Xbar := by
  intro h
  obtain ⟨y, ⟨-, hZ0, ⟨M, hM⟩, -⟩, -⟩ := h (fun _ _ _ => 0) (fun n _ => (n : ℝ))
    ⟨0, fun _ _ _ => by simp⟩ (fun _ _ => rfl) (fun _ => rfl)
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have h1 := hM t0 n (Sum.inl (Sum.inl ()))
  have h2 := congrFun (hZ0 n) ()
  change y t0 n (Sum.inl (Sum.inl ())) = (n : ℝ) at h2
  rw [h2, abs_of_nonneg (Nat.cast_nonneg n)] at h1
  linarith

/-! ### Proposition 8.2 with bounded initial conditions -/

/-- Woodford (2003), Definition, pp. 549–550, (1.16), **with bounded initial conditions**: the rule
determines a unique bounded equilibrium, optimal from a timeless perspective, for every bounded
adapted disturbance and every **bounded** initial condition `Z_{t₀}` known at `t₀` (for an
unbounded `Z_{t₀}` there is no bounded plan at all, `not_in_focSolvableM`). -/
def RobustlyOptimalB {κ : Type*} [Fintype κ] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) : Prop :=
  ∀ (cc : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ), BoundedV cc → AdaptedV 𝔼 cc → KnownV 𝔼 t0 Z0 →
    (∃ K, ∀ ω j, |Z0 ω j| ≤ K) →
    ∃ y, P.Feasible 𝔼 cc t0 Z0 y ∧ Rl cc y ∧
      (∀ y', P.Feasible 𝔼 cc t0 Z0 y' → Rl cc y' → ∀ t, t0 ≤ t → y' t = y t) ∧
      ∃ (f0 : ιz → ℝ) (F : Matrix ιz κ ℝ), P.TimelesslyOptimalPlan 𝔼 cc t0 Z0 (Xbar cc y) f0 F y

omit [DecidableEq ιZ] in
/-- Woodford (2003), (1.16): robust optimality for all initial conditions implies it for bounded
ones. -/
theorem RobustlyOptimal.toB {κ : Type*} [Fintype κ] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    {Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop}
    {Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ}
    (h : RobustlyOptimal P 𝔼 t0 Rl Xbar) : RobustlyOptimalB P 𝔼 t0 Rl Xbar :=
  fun cc Z0 hb ha hZ _ => h cc Z0 hb ha hZ

open TargetCriterion.Crit TargetCriterion.Krylov TargetCriterion.Prop82 Adjugate in
/-- **Woodford (2003), Proposition 8.2, p. 555, with bounded initial conditions**: under the
corrected Assumption 8.1 for bounded initial conditions (`Assumption81MB`) and Assumption 8.5,
commitment to the target criterion (1.23) built from the corrected Proposition 8.1 determines,
for every bounded adapted disturbance and every bounded initial `Z_{t₀}`, a unique bounded
equilibrium, optimal from a timeless perspective (the proof of
`Prop82General.Prop82M.prop82M_robustlyOptimal`, with the solvability of `Assumption81MB`). -/
theorem prop82M_robustlyOptimalB {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hpull : 𝔼.PullOut) (hA : Assumption81MB P 𝔼 t0)
    (H : Prop81General.Prop81ConclusionM P 𝔼 t0) (h85 : Assumption85b H.Λ P.sys.B2) {D : ℕ}
    (hD : D + 1 ≤ t0) (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D)
    (hα : (alpha H.Λ).natDegree ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) (hMhb : BoundedV Mh)
    (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh) (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimalB (κ := ιz) P 𝔼 t0 (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  intro cc Z0 hbc hac hZ0 hZb
  have hMb : ∃ K, ∀ ω r, |Mh (t0 - 1) ω r| ≤ K := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, fun ω r => hK (t0 - 1) ω r⟩
  obtain ⟨y, φ, hs⟩ := hA.solvable cc Z0 (Mh (t0 - 1)) hbc hac hZ0 hZb hMb (hMhk (t0 - 1))
  have hy := hs.1
  have hcrit : Prop82General.Prop82M.CriterionM H D qh vh y := by
    obtain ⟨h120', h119'⟩ := Prop82General.Prop82M.histThen_rec H hD hhist hs
    have hc := eq123_of_eq119_eq120 (eq122 H.Λ) hB hα P.sys.B2 h119' h120'
    intro t ht ω
    exact hc t (by omega) ω
  refine ⟨y, hy, hcrit, fun y' hy' hcrit' t ht => ?_, 0, 1, fun t _ ω => by simp, ?_⟩
  · exact (hA.unique cc Z0 (Mh (t0 - 1)) y' y _ _
      (Prop82General.Prop82M.focSystem_of_criterionM H h85 hD hB hα hhist hMhb hMhk hqhb hvhb
        hy' hcrit')
      (Prop82General.Prop82M.focSystem_of_criterionM H h85 hD hB hα hhist hMhb hMhk hqhb hvhb
        hy hcrit) t ht).1
  · have hopt := Prop82General.Prop82M.prop82M_optimal hpull H h85 hD hB hα hhist hMhb hMhk
      hqhb hvhb hy hcrit
    have he : (fun ω => P.sys.Et *ᵥ ((0 : ιz → ℝ) + (1 : Matrix ιz ιz ℝ) *ᵥ zpart (y t0 ω))) =
        fun ω => P.sys.Et *ᵥ zpart (y t0 ω) := by
      funext ω
      simp
    rw [he]
    exact hopt

/-! ### Proposition 8.2 for the inflation-inertia model, real case, unconditionally -/

open PencilSplit InertiaSplit in
/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the real case
(`S² ≥ 4P₂₃`, including the double root), with no Assumption 8.1 hypothesis**: commitment to the
target criterion (1.23) built from the split solving `λ₂ʳ` forward is robustly optimal for every
bounded adapted disturbance and every bounded initial condition, for any expectation system with
pull-out (Assumption 8.1 is `in_assumption81MB`, Assumption 8.5
`InertiaProp8182.in_assumption85`). -/
theorem in_prop82_real_B {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hD : 0 ≤ discQ c.β γ c.κ c.σ) (hpull : 𝔼.PullOut) {D : ℕ}
    (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK
      (Λmat (inProblem c γ hc hγ0.le).sys c.β (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)).J)
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimalB (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  set Dsp := inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD) with hDsp
  have hE : (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)).Et.rank = 2 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
    · simp
    · rw [in_Et_det]
      exact isUnit_iff_ne_zero.mpr hc.1.ne'
  have hrk : (Λmat (inProblem c γ hc hγ0.le).sys c.β Dsp.J).rank ≤ D := by
    rw [Prop81General.rank_Λmat (inProblem c γ hc hγ0.le).sys hc.1.ne' Dsp.K_det]
    change (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)).Et.rank ≤ D
    rw [hE]
    exact hD2
  have h85 : TargetCriterion.Krylov.Assumption85b
      (Λmat (inProblem c γ hc hγ0.le).sys c.β Dsp.J) (inProblem c γ hc hγ0.le).sys.B2 :=
    (InertiaProp8182.in_assumption85 c γ hc hγ0 hγ1 (quadQ_lam2r hD)).2
  exact prop82M_robustlyOptimalB hpull (in_assumption81MB c γ hc hγ0 hγ1 𝔼 t0)
    (Prop81General.prop81 _ Dsp 𝔼 t0) h85 hD1
    (fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk)
    ((Adjugate.natDegree_alpha_le_rank _).trans hrk) hhist hMhb hMhk hqhb hvhb

open PencilSplit InertiaSplit in
/-- **Woodford (2003), Proposition 8.2, p. 555, for the inflation-inertia model in the real case,
on a finite sample space, in the original robust-optimality sense** (every initial condition):
`InertiaProp8182.in_prop82_real` with its Assumption 8.1 hypothesis discharged by
`in_assumption81M_of_finite`. -/
theorem in_prop82_real_finite [Finite Ω] {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hD : 0 ≤ discQ c.β γ c.κ c.σ) (hpull : 𝔼.PullOut) {D : ℕ}
    (hD1 : D + 1 ≤ t0) (hD2 : 2 ≤ D) {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK
      (Λmat (inProblem c γ hc hγ0.le).sys c.β (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)).J)
      (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (quadQ_lam2r hD)) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) :=
  InertiaProp8182.in_prop82_real c γ hc hγ0 hγ1 hD hpull
    (in_assumption81M_of_finite c γ hc hγ0 hγ1 𝔼 t0) hD1 hD2 hhist hMhb hMhk hqhb hvhb

end Woodford.OptimalPolicyRules.InertiaAssumption81
