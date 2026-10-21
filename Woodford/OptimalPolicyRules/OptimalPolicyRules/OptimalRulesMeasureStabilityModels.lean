/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureStability
import OptimalPolicyRules.NKAssumption81
import OptimalPolicyRules.InertiaAssumption81

/-!
# Geometric stability of `H_n` in the book's two models

Woodford (2003), *Interest and Prices*, Chapter 8: the basic neo-Wicksellian model of §3.1
(pp. 582–591, `GeneralLinks.nkProblem`, Assumption 8.1 in `NKAssumption81`) and the
inflation-inertia model of §3.2 (pp. 592–604, `GeneralLinksInertia.inProblem`, Assumption 8.1
in `InertiaAssumption81`). For both, the endogenous state transition `H_n` of the optimal plan is
**geometrically stable**, for every admissible calibration — so the existence theorems
`OptimalRulesMeasureMarkov.m_existsUnique_var` (VAR disturbances) and
`OptimalRulesMeasureGeneral.m_assumption81MB_of_powDecay` (every bounded adapted disturbance)
apply.

The criterion is `OptimalRulesMeasureStability.powDecay_of_tendsto`: `Hᵏ n` is the difference of
the date-`k` states of the zero-forcing perfect-foresight solutions from `n` and from `0`
(`Hgen_pow_mulVec`), and these differences tend to zero:

* **basic model** (`nk_powDecay`): the difference of the multipliers solves the homogeneous
  second-order system of App. G.4 with initial value `Φ_{−1}`, so by uniqueness
  (`NKAssumption81.sys2R_existsUnique`) it is `X^{s+1}Φ_{−1}` with the stable solvent `X`
  (`NKAssumption81.NK.nk_solvent`);
* **inflation-inertia model** (`in_powDecay`): the difference of the Blanchard–Kahn states
  (`InertiaAssumption81.equil_of_foc`) is a bounded orbit of `InertiaFOCSystem.Abk`, which has
  no eigenvalue on the unit circle (`InertiaFOCSystem.bk_roots`), so it tends to zero
  (`BKInvariantSplit.tendsto_of_mem_boundedOrbits`).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureStabilityModels

open Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open OptimalRulesMeasureKernel OptimalRulesMeasureGeneral OptimalRulesMeasureStability

/-! ### Powers of `H` are differences of homogeneous solutions -/

/-- Woodford (2003), p. 539: `Hᵏ n` is the difference between the date-`k` states
`(Z_k, M_{k−1})` of the zero-forcing perfect-foresight solutions from `n` and from `0`. -/
theorem Hgen_pow_mulVec {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ]
    [DecidableEq ιZ] [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ}
    (hA81 : Assumption81 P perfectForesight 0) (k : ℕ) (n : ιZ ⊕ ιz → ℝ) :
    Hgen hA81 ^ k *ᵥ n = Sum.elim (Zpart (solY hA81 n 0 k)) (Mpart (solΦ hA81 n 0 k)) -
      Sum.elim (Zpart (solY hA81 0 0 k)) (Mpart (solΦ hA81 0 0 k)) := by
  set f : (ιZ ⊕ ιz → ℝ) → ιZ ⊕ ιz → ℝ := fun m => nextS hA81 m 0 with hf
  have hdiff : ∀ k n, f^[k] n - f^[k] 0 = Hgen hA81 ^ k *ᵥ n := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [hf]
      rw [hgen_spec, hgen_spec]
      have := ih n
      rw [pow_succ', ← mulVec_mulVec, ← this, mulVec_sub]
      abel
  have hst : ∀ m, f^[k] m = Sum.elim (Zpart (solY hA81 m 0 k)) (Mpart (solΦ hA81 m 0 k)) :=
    fun m => by
      rw [state_of_sol hA81 (f^[k] m) (bddSeq_zero (ι := ιz)), ← (iter_sol hA81 k m).1,
        ← (iter_sol hA81 k m).2]
  rw [← hdiff, hst, hst]

/-! ### The basic model -/

namespace NK

open NKAssumption81 NKAssumption81.NK GeneralLinks
open IRuleBasic (Calib PmG A1G A2G rvMul rvMul_sub VBounded VAdapted)

/-- Woodford (2003), App. G.4 (linearity): the difference of two solutions of the second-order
system with the same forcing solves the homogeneous system with the difference of the initial
values. -/
theorem sys2R_sub' {Ω : Type*} {𝔼 : ExpectationSystem Ω} {P A1 A2 : Matrix (Fin 2) (Fin 2) ℝ}
    {F : ℕ → Fin 2 → Ω → ℝ} {Φm Φm' : Fin 2 → Ω → ℝ} {Φ Φ' : ℕ → Fin 2 → Ω → ℝ}
    (h : Sys2R 𝔼 P A1 A2 F Φm Φ) (h' : Sys2R 𝔼 P A1 A2 F Φm' Φ') :
    Sys2R 𝔼 P A1 A2 (fun _ => 0) (Φm - Φm') (fun s => Φ s - Φ' s) := by
  intro s
  have e1 : (fun j => 𝔼.E s ((fun s => Φ s - Φ' s) (s + 1) j)) =
      (fun j => 𝔼.E s (Φ (s + 1) j)) - (fun j => 𝔼.E s (Φ' (s + 1) j)) := by
    funext j
    simp [map_sub]
  have e2 : lagR (Φm - Φm') (fun s => Φ s - Φ' s) s = lagR Φm Φ s - lagR Φm' Φ' s := by
    cases s with
    | zero => rfl
    | succ s => rfl
  rw [e1, e2, rvMul_sub, rvMul_sub, rvMul_sub]
  have hs := h s
  have hs' := h' s
  change _ = (0 : Fin 2 → Ω → ℝ)
  calc _ = (rvMul P (fun j => 𝔼.E s (Φ (s + 1) j)) - rvMul A1 (Φ s) + rvMul A2 (lagR Φm Φ s)) -
      (rvMul P (fun j => 𝔼.E s (Φ' (s + 1) j)) - rvMul A1 (Φ' s) +
        rvMul A2 (lagR Φm' Φ' s)) := by abel
    _ = 0 := by rw [hs, hs', sub_self]

variable (c : Calib) (hc : c.Adm)

/-- Woodford (2003), App. G.4: the zero-forcing perfect-foresight solution of the basic model
from the state `n = M_{−1}`: its multipliers solve the second-order system with
`Φ_{−1} = (M_{−1,1}, M_{−1,0})`. -/
theorem nk_sys2R (n : Empty ⊕ Fin 2 → ℝ) :
    Sys2R (Prop84General.shiftES perfectForesight 0) (PmG c.β c.σ c.κ c.lx)
      (A1G c.β c.σ c.κ c.lx c.li) (A2G c.β c.σ c.κ c.lx)
      (Fnk c (fun k (_ : Unit) => (0 : ℕ → Fin 2 → ℝ) k) 0)
      (PhiM (fun (_ : Unit) r => n (Sum.inr r)))
      (PhiOf 0 (fun k (_ : Unit) => solΦ (nk_assumption81_perfectForesight c hc 0) n 0 k)) := by
  have hs := sol_spec (nk_assumption81_perfectForesight c hc 0) n (bddSeq_zero (ι := Fin 2))
  exact (struct_iff_sys c hc perfectForesight _ 0 _ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2).mp hs.1.1

/-- Woodford (2003), §3.1 and App. G.4: **for the basic model `H_n` is geometrically stable**
(every admissible calibration): the homogeneous multiplier paths are `X^{s+1}Φ_{−1}` with the
stable solvent `X`. -/
theorem nk_powDecay :
    PencilSplit.PowDecay (Hgen (nk_assumption81_perfectForesight c hc 0)) := by
  set hA81 := nk_assumption81_perfectForesight c hc 0 with hA81def
  obtain ⟨X, hX, hXs, hB, hK⟩ := nk_solvent c hc
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hXp⟩ := IRuleBasic.pow_bound_of_schurStable hXs
  set 𝔼' := Prop84General.shiftES perfectForesight 0 with h𝔼'
  refine powDecay_of_tendsto fun n => ?_
  set Φn := PhiOf 0 (fun k (_ : Unit) => solΦ hA81 n 0 k) with hΦn
  set Φ0 := PhiOf 0 (fun k (_ : Unit) => solΦ hA81 0 0 k) with hΦ0
  set Φm := PhiM (fun (_ : Unit) r => n (Sum.inr r)) -
    PhiM (fun (_ : Unit) r => (0 : Empty ⊕ Fin 2 → ℝ) (Sum.inr r)) with hΦm
  have hD : Sys2R 𝔼' (PmG c.β c.σ c.κ c.lx) (A1G c.β c.σ c.κ c.lx c.li) (A2G c.β c.σ c.κ c.lx)
      (fun _ => 0) Φm (fun s => Φn s - Φ0 s) := sys2R_sub' (nk_sys2R c hc n) (nk_sys2R c hc 0)
  have hm : ∀ j, 𝔼'.E 0 (Φm j) = Φm j := fun j => rfl
  set KΦ := |Φm 0 ()| + |Φm 1 ()| with hKΦ
  have hmb : ∀ j ω, |Φm j ω| ≤ KΦ := by
    intro j ω
    rcases ω
    fin_cases j
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
  obtain ⟨Φu, -, hu⟩ := sys2R_existsUnique 𝔼' hX hXs hB hK (F := fun _ => 0)
    ⟨0, fun _ _ _ => by simp⟩ (fun _ _ => rfl) hm ⟨KΦ, hmb⟩
  obtain ⟨Mn, hMn⟩ := sol_bdd hA81 n (bddSeq_zero (ι := Fin 2))
  obtain ⟨M0, hM0⟩ := sol_bdd hA81 0 (bddSeq_zero (ι := Fin 2))
  have hDb : VBounded (fun s => Φn s - Φ0 s) := ⟨Mn + M0, fun s j ω => by
    rcases ω
    fin_cases j
    · exact (abs_sub _ _).trans (add_le_add ((hMn _).2 _) ((hM0 _).2 _))
    · exact (abs_sub _ _).trans (add_le_add ((hMn _).2 _) ((hM0 _).2 _))⟩
  have hhat : ∀ s j ω, |hatΦ X Φm s j ω| ≤ 2 * (Cb * ρ ^ (s + 1) * KΦ) := fun s j ω =>
    IRuleBasic.abs_rvMul_pow_le hXp (s + 1) hmb j ω
  have hρk : ∀ s, ρ ^ (s + 1) ≤ 1 := fun s => pow_le_one₀ hρ0.le hρ1.le
  have hKΦ0 : 0 ≤ KΦ := by positivity
  have hhb : VBounded (hatΦ X Φm) := ⟨2 * (Cb * KΦ), fun s j ω => by
    refine (hhat s j ω).trans ?_
    have := mul_le_mul_of_nonneg_left (hρk s) hCb
    nlinarith⟩
  have h1 : (fun s => Φn s - Φ0 s) = Φu := hu _ ⟨hD, fun _ _ => rfl, hDb⟩
  have h2 : hatΦ X Φm = Φu := hu _ ⟨hat_sys 𝔼' hX hm, fun _ _ => rfl, hhb⟩
  have hconv : ∀ j, Tendsto (fun s => (Φn s - Φ0 s) j ()) atTop (𝓝 0) := by
    intro j
    have e : ∀ s, (Φn s - Φ0 s) j () = hatΦ X Φm s j () := fun s => by
      have := congrFun h1 s
      rw [this, ← h2]
    refine squeeze_zero_norm (a := fun s => 2 * (Cb * ρ ^ (s + 1) * KΦ)) (fun s => ?_) ?_
    · rw [Real.norm_eq_abs, e]
      exact hhat s j ()
    · have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp
        (tendsto_add_atTop_nat 1)).const_mul (2 * Cb) |>.mul_const KΦ
      simp only [Function.comp_def, mul_zero, zero_mul] at this
      refine this.congr fun s => ?_
      ring
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_pi_nhds]
  intro a
  rcases a with e | r
  · exact e.elim
  simp only [Hgen_pow_mulVec, Pi.sub_apply, Sum.elim_inr, Mpart, Pi.zero_apply]
  fin_cases r
  · exact hconv 1
  · exact hconv 0

/-- Woodford (2003), §3.1: `H_n` of `OptimalRulesMeasureMarkov` (for any VAR) is geometrically
stable in the basic model, so `OptimalRulesMeasureMarkov.m_existsUnique_var` applies. -/
theorem nk_powDecay_Hn {ιs : Type*} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
    (C2 : Matrix (Fin 2) ιs ℝ) (hA : OptimalRulesMeasureMarkov.PowBdd A) :
    PencilSplit.PowDecay (OptimalRulesMeasureMarkov.Hn (nkProblem c hc) A C2
      (nk_assumption81_perfectForesight c hc 0) hA) := by
  rw [Hn_eq_Hgen]
  exact nk_powDecay c hc

/-- Woodford (2003), **Assumption 8.1 for the basic model on every filtered probability space**,
p. 541: for every bounded adapted disturbance, every bounded `Z_{t₀}` known at `t₀` and every
bounded `M_{t₀−1}` known at `t₀ − 1`, (1.1) + (1.9) has an a.s. unique bounded solution with
Mathlib's conditional expectation (`OptimalRulesMeasureGeneral.m_assumption81MB_of_powDecay`). -/
theorem nk_m_assumption81MB {Ω : Type*} [MeasurableSpace Ω]
    (S : ExpectationsMeasure.MeasExpectationSystem Ω) (t0 : ℕ) :
    OptimalRulesMeasure.MAssumption81MB S (nkProblem c hc) t0 :=
  m_assumption81MB_of_powDecay _ S t0 (nk_powDecay c hc)

end NK

/-! ### The inflation-inertia model -/

namespace Inertia

open InertiaAssumption81 InertiaFOCSystem GeneralLinksInertia
open IRuleBasic (Calib)

variable (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)

/-- Woodford (2003), §3.2 and App. C.1: the zero-forcing perfect-foresight solution of the
inflation-inertia model from the state `n = (Z, M_{−1})` is an equilibrium of the
Blanchard–Kahn system (`InertiaAssumption81.equil_of_foc`). -/
theorem in_equil (n : Unit ⊕ Fin 2 → ℝ) :
    GeneralBKCopy.Equil (Prop84General.shiftES perfectForesight 0) (Abk c γ)
      (forcing c γ (fun k (_ : Unit) => (0 : ℕ → Fin 2 → ℝ) k) 0)
      (x0Of (fun (_ : Unit) j => n (Sum.inl j)) (fun (_ : Unit) r => n (Sum.inr r)))
      (bkState (x0Of (fun (_ : Unit) j => n (Sum.inl j)) (fun (_ : Unit) r => n (Sum.inr r)))
        (wOf 0 (fun k (_ : Unit) => solY (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) n 0 k)
          (fun k (_ : Unit) => solΦ (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) n 0 k))) :=
  equil_of_foc c γ hc hγ0
    (sol_spec (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) n (bddSeq_zero (ι := Fin 2)))

/-- Woodford (2003), §3.2 (`Z_t = π_{t−1}`): along a solution the next predetermined variable is
current inflation. -/
theorem in_Z_next (n : Unit ⊕ Fin 2 → ℝ) (t : ℕ) :
    solY (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) n 0 (t + 1) (Sum.inl (Sum.inl ())) =
      solY (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) n 0 t (Sum.inl (Sum.inr 0)) := by
  have hrow := ((sol_spec (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) n
    (bddSeq_zero (ι := Fin 2))).1.1 t (Nat.zero_le t) ()).1
  have := congrFun hrow ()
  simpa [inProblem, inSys, mulVec, dotProduct, Fin.sum_univ_two, Zpart, zpart] using this

/-- Woodford (2003), §3.2 and App. C.1: **for the inflation-inertia model `H_n` is geometrically
stable** (every admissible calibration, `0 < γ ≤ 1`): the homogeneous Blanchard–Kahn state paths
are bounded orbits of `InertiaFOCSystem.Abk`, which has no eigenvalue on the unit circle, so
they tend to zero. -/
theorem in_powDecay :
    PencilSplit.PowDecay (Hgen (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0)) := by
  set hA81 := in_assumption81_perfectForesight c γ hc hγ0 hγ1 0 with hA81def
  refine powDecay_of_tendsto fun n => ?_
  obtain ⟨hs1, -, -, -, ⟨B1, hB1⟩⟩ := in_equil c γ hc hγ0 hγ1 n
  obtain ⟨hs0, -, -, -, ⟨B0, hB0⟩⟩ := in_equil c γ hc hγ0 hγ1 0
  set Y1 := bkState (x0Of (fun (_ : Unit) j => n (Sum.inl j)) (fun (_ : Unit) r => n (Sum.inr r)))
    (wOf 0 (fun k (_ : Unit) => solY hA81 n 0 k) (fun k (_ : Unit) => solΦ hA81 n 0 k)) with hY1
  set Y0 := bkState (x0Of (fun (_ : Unit) j => (0 : Unit ⊕ Fin 2 → ℝ) (Sum.inl j))
    (fun (_ : Unit) r => (0 : Unit ⊕ Fin 2 → ℝ) (Sum.inr r)))
    (wOf 0 (fun k (_ : Unit) => solY hA81 0 0 k) (fun k (_ : Unit) => solΦ hA81 0 0 k)) with hY0
  set D : ℕ → Fin 3 ⊕ Fin 3 → ℝ := fun t k => Y1 t k () - Y0 t k () with hD
  have hrec : ∀ t, D (t + 1) = Abk c γ *ᵥ D t := by
    intro t
    funext k
    have e1 := congrFun (hs1 t k) ()
    have e0 := congrFun (hs0 t k) ()
    change Y1 (t + 1) k () = BKForward.mv (Abk c γ) (Y1 t) k () + _ at e1
    change Y0 (t + 1) k () = BKForward.mv (Abk c γ) (Y0 t) k () + _ at e0
    rw [BKForward.mv_apply_sum] at e1 e0
    simp only [hD, e1, e0, mulVec, dotProduct]
    rw [← sub_eq_zero]
    simp only [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, mul_sub, sub_self]
  have hDb : ∀ t i, |D t i| ≤ B1 + B0 := fun t i =>
    (abs_sub _ _).trans (add_le_add (hB1 t i ()) (hB0 t i ()))
  have hmem := BKInvariantSplit.mem_boundedOrbits_of_orbit hrec hDb
  have hT := BKInvariantSplit.tendsto_of_mem_boundedOrbits (bk_roots c γ hc hγ0 hγ1).1 hmem
  have hpow : ∀ t, Abk c γ ^ t *ᵥ D 0 = D t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', ← mulVec_mulVec, ih, hrec]
  simp only [hpow] at hT
  have hx : ∀ j, Tendsto (fun t => D (t + 1) (Sum.inr j)) atTop (𝓝 0) := fun j => by
    have := ((continuous_apply (Sum.inr j)).tendsto 0).comp
      ((tendsto_add_atTop_iff_nat 1).mpr hT)
    exact this
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_pi_nhds]
  intro a
  rcases a with u | r
  · rcases u
    refine (hx 0).congr fun t => ?_
    simp only [Hgen_pow_mulVec, Pi.sub_apply, Sum.elim_inl, Zpart]
    rw [in_Z_next c γ hc hγ0 hγ1 n t, in_Z_next c γ hc hγ0 hγ1 0 t]
    rfl
  · fin_cases r
    · refine (hx 1).congr fun t => ?_
      simp only [Hgen_pow_mulVec, Pi.sub_apply, Sum.elim_inr, Mpart]
      rfl
    · refine (hx 2).congr fun t => ?_
      simp only [Hgen_pow_mulVec, Pi.sub_apply, Sum.elim_inr, Mpart]
      rfl

/-- Woodford (2003), §3.2: `H_n` of `OptimalRulesMeasureMarkov` (for any VAR) is geometrically
stable in the inflation-inertia model, so `OptimalRulesMeasureMarkov.m_existsUnique_var`
applies. -/
theorem in_powDecay_Hn {ιs : Type*} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
    (C2 : Matrix (Fin 2) ιs ℝ) (hA : OptimalRulesMeasureMarkov.PowBdd A) :
    PencilSplit.PowDecay (OptimalRulesMeasureMarkov.Hn (inProblem c γ hc hγ0.le) A C2
      (in_assumption81_perfectForesight c γ hc hγ0 hγ1 0) hA) := by
  rw [Hn_eq_Hgen]
  exact in_powDecay c γ hc hγ0 hγ1

include hγ1 in
/-- Woodford (2003), **Assumption 8.1 for the inflation-inertia model on every filtered
probability space**, p. 541: for every bounded adapted disturbance and bounded initial conditions
(1.1) + (1.9) has an a.s. unique bounded solution with Mathlib's conditional expectation. -/
theorem in_m_assumption81MB {Ω : Type*} [MeasurableSpace Ω]
    (S : ExpectationsMeasure.MeasExpectationSystem Ω) (t0 : ℕ) :
    OptimalRulesMeasure.MAssumption81MB S (inProblem c γ hc hγ0.le) t0 :=
  m_assumption81MB_of_powDecay _ S t0 (in_powDecay c γ hc hγ0 hγ1)

end Inertia

end Woodford.OptimalPolicyRules.OptimalRulesMeasureStabilityModels
