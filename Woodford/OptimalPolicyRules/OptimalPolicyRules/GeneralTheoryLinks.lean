/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaProp8182
import OptimalPolicyRules.PencilRepeated
import OptimalPolicyRules.Circle81
import OptimalPolicyRules.NKAssumption81

/-!
# Links between the general theory of Props 8.1–8.4 and the rest of the chapter

Woodford (2003), *Interest and Prices*, Chapter 8, §1.4–1.5 (pp. 552–559) and Appendix G.1–G.2
(pp. 716–719), with the inflation-inertia model of §3.2 (pp. 592–604) and the basic model of
§3.1 (pp. 582–591).

## Main results

* **The bounded-orbit subspace does not depend on the representation.**
  `orbitBdd_eq_of_homEquiv`: any two matrices `Λ, Λ'` that represent the bounded solutions of the
  homogeneous (1.18) as Proposition 8.1 requires (`Prop83.HomEquiv`) have the same subspace of
  initial multipliers with bounded orbits. With `card_le_zerosInside_add_finrank` and
  `zerosInside_add_one_le_of_root` this gives Proposition 8.3's count for *every*
  representation from one explicit representation, with no distinct-root assumption.
* **The inflation-inertia model at the double root `S² = 4P₂₃`.** There Assumption 8.3 fails
  (`in_double_not_assumption83`), and no selection satisfying Assumption 8.2 takes whole root
  classes (`in_double_not_selWhole`), so neither `PencilAssumptions.prop81_of_assumptions` nor
  `PencilRepeated.prop81_of_assumptions_general` applies. Proposition 8.1 still holds there from
  the explicit split (`InertiaProp8182.in_prop81_real`, all real cases), and so does Proposition
  8.3 for every representation (`in_prop83_real`). With `InertiaSplit.in_prop83` (`S² ≠ 4P₂₃`)
  this gives Proposition 8.3 for the model at **every** admissible calibration (`in_prop83_all`),
  and with `InertiaProp8182.in_prop81_all` (complex roots through case (ii) of Assumption 8.2)
  Propositions 8.1 and 8.3 together at every calibration (`in_props_81_83_all`).
* **The old conditional results of `TargetCriterion`.** `conclusionM_of_conclusion`: the original
  hypothesis structure `Prop81Conclusion` (whenever `R(L⁻¹)` is adapted, e.g. under perfect
  foresight, `conclusionM_perfectForesight`) is an instance of the corrected
  `Prop81ConclusionM`, with the same criterion (`criterion_iff`); so the conclusions of
  `prop82_optimal`, `prop82_unique` hold **without** their hypothesis `MultStable`, under
  Assumption 8.5 instead (`prop82_optimal_of_assumption85`, `prop82_unique_of_assumption85`;
  `MultStable` fails in the book's applications, `PencilAssumptions.not_multStable_of_unselected`).
  `prop84_conditional_discharged`: every hypothesis of `TargetCriterion.prop84_conditional` is
  supplied by Propositions 8.3–8.4 (`Prop84General`) for every corrected representation, so its
  equivalence holds unconditionally. `prop83Claim_perfectForesight`: the statement
  `TargetCriterion.Prop83Claim` is non-vacuous and true under Assumptions 8.2 (i)–8.4.
* **The basic model as a worked instance.** `nk_assumption82`, `nk_assumption84`,
  `nk_assumption85` check Assumptions 8.2, 8.4 and 8.5 for `GeneralLinks.nkProblem`
  (Assumption 8.3 is `GeneralLinks.nk_assumption83`, Assumption 8.1 (corrected) is
  `NKAssumption81.NK.nk_assumption81M`); `nk_Λmat`: the general `Λ = β⁻¹K⁻¹Ẽ'` is the
  hand-computed `GeneralLinks.nkΛ`; `nk_prop81_prop83`: Propositions 8.1 and 8.3 for the basic
  model from the general theorems; `nk_prop82`: Proposition 8.2 for it, for every expectation
  system with pull-out (no further hypothesis).
* `circSys_half`: the scalar system of `Circle81` at `β = 1/2` is `Prop81General.coinSys`.
-/

namespace Woodford.OptimalPolicyRules.GeneralTheoryLinks

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ Adjugate
open TargetCriterion (zerosInside)
open TargetCriterion.Prop81
open Prop83 (cmat HomEquiv orbitBdd zerosOnCircle)
open Prop81General (Prop81ConclusionM)

variable {Ω : Type*}

/-! ### The bounded-orbit subspace is representation-independent -/

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-- Woodford (2003), p. 553 (the paragraph after Proposition 8.1) and p. 557: if `Λ, Υ` and
`Λ', Υ'` both represent the bounded solutions of the homogeneous (1.18) (`HomEquiv`), every
initial multiplier `M` with a bounded orbit under `Λ` has a bounded orbit under `Λ'`: the bounded
solution `(Υ Λᵗ M, Λᵗ M)` of (1.18) obeys (1.20) for `Λ'` too, so its `M`-block is `Λ'ᵗ M`. -/
theorem orbitBdd_le_of_homEquiv {S : LinearRESystem ιZ ιz} {β : ℝ} {Λ Λ' : Matrix ιz ιz ℝ}
    {Υ Υ' : Matrix ιZ ιz ℝ} (hE : HomEquiv S β Λ Υ) (hE' : HomEquiv S β Λ' Υ') :
    orbitBdd (cmat Λ) ≤ orbitBdd (cmat Λ') := by
  intro v hv
  obtain ⟨C, hC⟩ := hv
  set h : ℕ → ιZ ⊕ ιz → ℂ := fun t => Prop83.Gmap (cmat Υ) ((cmat Λ ^ t) *ᵥ v) with hh
  have hrep : Prop83.RepSolC Λ Υ h := by
    intro t
    refine ⟨funext fun r => ?_, funext fun r => ?_⟩
    · change ((cmat Λ ^ (t + 1)) *ᵥ v) r = (cmat Λ *ᵥ ((cmat Λ ^ t) *ᵥ v)) r
      rw [pow_succ', mulVec_mulVec]
    · rfl
  have hb : Prop83.BddSeq h := by
    refine ⟨(∑ i', ∑ j, ‖cmat Υ i' j‖) * max C 0 + max C 0, fun t i => ?_⟩
    exact Prop83.norm_Gmap_le (cmat Υ) (le_max_right C 0)
      (fun j => (hC t j).trans (le_max_left _ _)) i
  have hrep' := Prop83.repSolC_of_homSolC hE' hb (Prop83.homSolC_of_repSolC hE hb hrep)
  have hM : ∀ t, (fun r => h t (Sum.inr r)) = (cmat Λ' ^ t) *ᵥ v := by
    intro t
    induction t with
    | zero =>
      funext r
      change ((cmat Λ ^ 0) *ᵥ v) r = ((cmat Λ' ^ 0) *ᵥ v) r
      simp
    | succ t ih => rw [(hrep' t).1, ih, pow_succ', mulVec_mulVec]
  obtain ⟨K, hK⟩ := hb
  refine ⟨K, fun k i => ?_⟩
  have := hK k (Sum.inr i)
  rwa [show h k (Sum.inr i) = ((cmat Λ' ^ k) *ᵥ v) i from congrFun (hM k) i] at this

/-- Woodford (2003), pp. 553, 557: **the bounded-orbit subspace is the same for every
representation** of the bounded homogeneous solutions of (1.18). -/
theorem orbitBdd_eq_of_homEquiv {S : LinearRESystem ιZ ιz} {β : ℝ} {Λ Λ' : Matrix ιz ιz ℝ}
    {Υ Υ' : Matrix ιZ ιz ℝ} (hE : HomEquiv S β Λ Υ) (hE' : HomEquiv S β Λ' Υ') :
    orbitBdd (cmat Λ) = orbitBdd (cmat Λ') :=
  le_antisymm (orbitBdd_le_of_homEquiv hE hE') (orbitBdd_le_of_homEquiv hE' hE)

/-- Woodford (2003), p. 557 (tool): an eigenvector for an eigenvalue `|μ| > 1` has an unbounded
orbit. -/
theorem not_mem_orbitBdd {M : Matrix ιz ιz ℂ} {z : ιz → ℂ} {μ : ℂ} (hz0 : z ≠ 0)
    (hz : M *ᵥ z = μ • z) (hμ : 1 < ‖μ‖) : z ∉ orbitBdd M := by
  rintro ⟨C, hC⟩
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hz0 (funext hn)
  have hpow : ∀ k, (M ^ k) *ᵥ z = μ ^ k • z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hz, smul_smul, pow_succ]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / ‖z i‖) hμ
  have h1 := hC k i
  rw [hpow, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow] at h1
  have hzi : 0 < ‖z i‖ := norm_pos_iff.mpr hi
  rw [div_lt_iff₀ hzi] at hk
  linarith

/-- Woodford (2003), p. 557 (tool): a matrix with an eigenvalue `|μ| > 1` has a bounded-orbit
subspace of dimension `< n`. -/
theorem finrank_orbitBdd_lt {M : Matrix ιz ιz ℂ} {μ : ℂ} (hroot : M.charpoly.eval μ = 0)
    (hμ : 1 < ‖μ‖) : Module.finrank ℂ (orbitBdd M) < Fintype.card ιz := by
  rw [eval_charpoly] at hroot
  obtain ⟨z, hz0, hz⟩ := PencilEigen.exists_eigvec hroot
  have hne : orbitBdd M ≠ ⊤ := fun h => not_mem_orbitBdd hz0 hz hμ (h ▸ Submodule.mem_top)
  have := Submodule.finrank_lt hne
  rwa [Module.finrank_fintype_fun_eq_card] at this

variable {S : LinearRESystem ιZ ιz} {β : ℝ} {Λ : Matrix ιz ιz ℝ} {Υ : Matrix ιZ ιz ℝ}

/-- Woodford (2003), Proposition 8.3, pp. 556–557, **lower half without Assumption 8.3**: if no
root of (1.15) lies on `|λ| = β⁻¹`, then `n_z ≤ zerosInside α + dim(bounded orbits of Λ)`. -/
theorem card_le_zerosInside_add_finrank (hE : HomEquiv S β Λ Υ) (hβ : 0 < β)
    (hreg : S.pencilPoly ≠ 0) (hcirc : ∀ l ∈ S.pencilPoly.roots, ‖l‖ ≠ β⁻¹) :
    Fintype.card ιz ≤ zerosInside (alpha Λ) + Module.finrank ℂ (orbitBdd (cmat Λ)) := by
  have h0 := Prop83.zerosOnCircle_eq_zero hE hβ hreg hcirc
  rw [Prop83.zerosOnCircle_alpha] at h0
  rw [Prop83.zerosInside_alpha]
  have hin := Prop83.card_inside_le_finrank (cmat Λ)
  have hR : Multiset.card (cmat Λ).charpoly.roots = Fintype.card ιz :=
    Prop83.card_charpoly_roots _
  set R := (cmat Λ).charpoly.roots
  have hp1 := congrArg Multiset.card (Multiset.filter_add_not (fun μ : ℂ => ‖μ‖ < 1) R)
  have hp2 := congrArg Multiset.card (Multiset.filter_add_not (fun μ : ℂ => 1 < ‖μ‖)
    (R.filter (fun μ => ¬ ‖μ‖ < 1)))
  rw [Multiset.card_add] at hp1 hp2
  have e1 : (R.filter (fun μ => ¬ ‖μ‖ < 1)).filter (fun μ => 1 < ‖μ‖) =
      R.filter (fun μ => 1 < ‖μ‖) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun μ _ => ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
  have e2 : (R.filter (fun μ => ¬ ‖μ‖ < 1)).filter (fun μ => ¬ 1 < ‖μ‖) =
      R.filter (fun μ => ‖μ‖ = 1) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun μ _ => ⟨fun h => ?_, fun h => ⟨?_, ?_⟩⟩
    · exact le_antisymm (not_lt.mp h.1) (not_lt.mp h.2)
    · rw [h]
      exact lt_irrefl 1
    · rw [h]
      exact lt_irrefl 1
  rw [e1, e2] at hp2
  omega

/-- Woodford (2003), Proposition 8.3, pp. 556–557, **upper half without Assumption 8.3**: a
nonzero root `λ` of (1.15) with `|λ| ≥ β⁻¹` makes `(βλ)⁻¹` an eigenvalue of `Λ` in the closed
unit disc (`Prop83.charpoly_root_of_pencil_root`), so `zerosInside α ≤ n_z − 1`. -/
theorem zerosInside_add_one_le_of_root (hE : HomEquiv S β Λ Υ) (hβ : 0 < β)
    (hreg : S.pencilPoly ≠ 0) {l : ℂ} (hl : l ∈ S.pencilPoly.roots) (hl0 : l ≠ 0)
    (hln : β⁻¹ ≤ ‖l‖) : zerosInside (alpha Λ) + 1 ≤ Fintype.card ιz := by
  have hdet : (cmat S.Ahat - l • cmat S.Ihat).det = 0 := by
    rw [← PencilSplit.pencilPoly_eval]
    exact (mem_roots hreg).mp hl
  have hroot := Prop83.charpoly_root_of_pencil_root hE hβ hl0 hdet hln
  have hx : ‖((β : ℂ) * l)⁻¹‖ ≤ 1 := by
    have h1 : 1 ≤ β * ‖l‖ := by
      have := mul_le_mul_of_nonneg_left hln hβ.le
      rwa [mul_inv_cancel₀ hβ.ne'] at this
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ.le]
    exact inv_le_one_of_one_le₀ h1
  have hxR : ((β : ℂ) * l)⁻¹ ∈ (cmat Λ).charpoly.roots :=
    (mem_roots (charpoly_monic _).ne_zero).mpr hroot
  rw [Prop83.zerosInside_alpha]
  have hR : Multiset.card (cmat Λ).charpoly.roots = Fintype.card ιz :=
    Prop83.card_charpoly_roots _
  set R := (cmat Λ).charpoly.roots
  have hp := congrArg Multiset.card (Multiset.filter_add_not (fun μ : ℂ => 1 < ‖μ‖) R)
  rw [Multiset.card_add] at hp
  have hpos : 0 < Multiset.card (R.filter (fun μ : ℂ => ¬ 1 < ‖μ‖)) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨_, Multiset.mem_filter.mpr ⟨hxR, not_lt.mpr hx⟩⟩
  omega

/-! ### The inflation-inertia model, including the double root `S² = 4P₂₃` -/

namespace Inertia

open InertiaSplit CubicRoots GeneralLinksInertia
open IRuleBasic (Calib)

variable (c : Calib) (γ : ℝ)

/-- Woodford (2003), (1.15), App. G.6, p. 725, for the inertia model: the characteristic
polynomial is a nonzero polynomial (it is `−β(μ − μ₁)(μ − μ₂)(μ − μ₃)`). -/
theorem in_pencil_ne_zero (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) : (inSys c γ hσ hd).pencilPoly ≠ 0 := by
  rw [in_pencilPoly c γ h]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr
    (neg_ne_zero.mpr (by exact_mod_cast h.beta_pos.ne'))) (X_sub_C_ne_zero _))
    (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)

/-- Woodford (2003), App. G.1 and G.6, p. 725: the nonzero roots of (1.15) for the inertia
model are `μ₁, μ₂, μ₃` (`μⱼ = (βλⱼ)⁻¹`), with multiplicity. -/
theorem in_nonzeroRoots (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) :
    PencilEigen.nonzeroRoots (inSys c γ hσ hd) = {muj c (lam1 c.β γ c.κ c.σ),
      muj c (lam2 c.β γ c.κ c.σ), muj c (lam3 c.β γ c.κ c.σ)} := by
  have z1 := muj_ne_zero c γ h (by exact_mod_cast (lam1_spec h).1.ne' :
    (lam1 c.β γ c.κ c.σ : ℂ) ≠ 0)
  have z2 := muj_ne_zero c γ h (lam2_ne_zero h)
  have z3 := muj_ne_zero c γ h (lam3_ne_zero h)
  rw [PencilEigen.nonzeroRoots, in_roots c γ h, Multiset.filter_eq_self]
  intro a ha
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  exacts [z1, z2, z3]

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716, **fails at the double root**: when
`S² = 4P₂₃` the roots `μ₂ = μ₃` of (1.15) coincide, so (1.15) has no three distinct nonzero
roots. -/
theorem in_double_not_assumption83 (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) (hD0 : discQ c.β γ c.κ c.σ = 0) :
    ¬ PencilEigen.Assumption83 (inSys c γ hσ hd) := by
  intro h83
  have hnd := h83.nodup
  rw [in_nonzeroRoots c γ h hσ hd, lam2_eq_lam3_iff.mpr hD0] at hnd
  simp at hnd

/-- Woodford (2003), Assumption 8.2, p. 552, at the double root `S² = 4P₂₃`: every selection of
`n_Z = 1` root with `|μ| < β⁻¹` takes one copy of the double root `μ₂ = μ₃`, so it never takes
whole root classes (`PencilRepeated.SelWhole`). Hence
`PencilRepeated.prop81_of_assumptions_general` does not apply there (its selection must be
whole), and Proposition 8.1 at the double root comes from the explicit split instead
(`InertiaProp8182.in_prop81_real`). -/
theorem in_double_not_selWhole (h : Assumptions.Standing c.β γ c.κ c.σ) (hσ : c.σ ≠ 0)
    (hd : 1 + c.β * γ ≠ 0) (hD0 : discQ c.β γ c.κ c.σ = 0)
    (h82 : PencilEigen.Assumption82 (inSys c γ hσ hd) c.β) :
    ¬ PencilRepeated.SelWhole (inSys c γ hσ hd) h82.sel := by
  intro hw
  obtain ⟨n1, -, -⟩ := in_root_norms c γ h
  have h23 := lam2_eq_lam3_iff.mpr hD0
  have hcard : Multiset.card h82.sel = 1 := by
    have := h82.sel_card
    rw [InertiaProp8182.in_rank_Ahat c γ h hσ hd] at this
    simpa using this
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  have hmem : a ∈ h82.sel := by
    rw [ha]
    exact Multiset.mem_singleton_self a
  have hfl := Multiset.mem_of_le h82.sel_le hmem
  rw [Multiset.mem_filter, in_roots c γ h] at hfl
  have ha3 : a = muj c (lam3 c.β γ c.κ c.σ) := by
    obtain ⟨hr, -, hlt⟩ := hfl
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact absurd hlt (not_lt.mpr n1.le)
    · rw [h23]
    · rfl
  have hne : muj c (lam1 c.β γ c.κ c.σ) ≠ muj c (lam3 c.β γ c.κ c.σ) := fun e => by
    obtain ⟨-, -, n3⟩ := in_root_norms c γ h
    rw [e] at n1
    linarith
  have hc := hw a hmem
  rw [ha, ha3, in_roots c γ h, h23] at hc
  simp [hne.symm] at hc

/-- Woodford (2003), Proposition 8.1, p. 553, for the inertia model: every representation of the
corrected Proposition 8.1 represents the bounded deterministic solutions of the homogeneous
(1.18) (`HomEquiv`); the base point is the constant plan of `InertiaSplit.in_xvec_base`, so
Assumption 8.1 is not needed. -/
theorem in_homEquiv [Nonempty Ω] (hc : c.Adm) (hγ : 0 ≤ γ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (H : Prop81ConclusionM (inProblem c γ hc hγ) 𝔼 t0) :
    HomEquiv (inProblem c γ hc hγ).sys c.β H.Λ H.Υ := by
  obtain ⟨hyb, hya, hφb, hφm, h118⟩ :=
    Prop83Links.const_base _ 𝔼 t0 _ (in_xvec_base c γ hc hγ)
  exact Prop83.homEquiv_of_perturbation h118 (Prop83Links.hequiv_of_prop81M H hyb hya hφb hφm)

/-- **Woodford (2003), Proposition 8.3, pp. 556–557, for the inflation-inertia model in the real
case `S² ≥ 4P₂₃`, including the double root, for every representation of Proposition 8.1**
(any expectation system, nonempty sample space): `α(L) = det(I − ΛL)` has exactly one zero
inside the unit circle and none on it. Assumption 8.3 is not used (it fails at the double root):
the upper bound comes from the root `μ₁` (`zerosInside_add_one_le_of_root`), the lower bound
from comparing the bounded-orbit subspace with that of the explicit split solving `λ₂ʳ` forward,
whose `Λ` has the eigenvalue `λ₃ʳ > 1` (`orbitBdd_eq_of_homEquiv`). -/
theorem in_prop83_real [Nonempty Ω] (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : 0 ≤ discQ c.β γ c.κ c.σ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (H : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) :
    zerosInside (alpha H.Λ) = 1 ∧ zerosOnCircle (alpha H.Λ) = 0 := by
  have h := standing_of c γ hc hγ0 hγ1
  have hβ := hc.1
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hd := in_det_ne c γ hc hγ0.le
  have hE := in_homEquiv c γ hc hγ0.le 𝔼 t0 H
  have hreg : (inProblem c γ hc hγ0.le).sys.pencilPoly ≠ 0 := in_pencil_ne_zero c γ h hσ hd
  have hcirc : ∀ l ∈ (inProblem c γ hc hγ0.le).sys.pencilPoly.roots, ‖l‖ ≠ c.β⁻¹ :=
    in_no_circle c γ h hσ hd
  -- the reference representation: the split solving `λ₂ʳ` forward (perfect foresight)
  have hq : quadQ c.β γ c.κ c.σ (lam2r c.β γ c.κ c.σ) = 0 := quadQ_lam2r hD
  have hEs := in_homEquiv c γ hc hγ0.le perfectForesight 0
    (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) perfectForesight 0)
  obtain ⟨hp, h1, h0, -, -⟩ := mu_facts c γ h hq
  have hl2 := one_lt_lam2r h
  have hls0 : lam2r c.β γ c.κ c.σ ≠ 0 := by linarith
  have htr := in_Λ_trace c γ hσ hd hβ.ne' h.gamma_pos.ne' hp h1 h0
  have hdt := in_Λ_det c γ hσ hd hβ.ne' h.gamma_pos.ne' hp h1 h0
  rw [tr_eq c γ h hls0 hp] at htr
  rw [det_eq c γ h hls0 hq] at hdt
  have hb : sumS c.β γ c.κ c.σ - lam2r c.β γ c.κ c.σ = lam3r c.β γ c.κ c.σ := by
    linarith [lam2r_add_lam3r c.β γ c.κ c.σ]
  rw [hb] at htr hdt
  set Λs := PencilSplit.Λmat (inSys c γ hσ hd) c.β (inJ c (c.β * lam2r c.β γ c.κ c.σ)⁻¹) with hΛs
  have hroot : (cmat Λs).charpoly.eval (lam3r c.β γ c.κ c.σ : ℂ) = 0 := by
    have htrC : (cmat Λs).trace = (Λs.trace : ℂ) := by simp [trace_fin_two, Prop83.cmat]
    have hdetC : (cmat Λs).det = (Λs.det : ℂ) := by simp [det_fin_two, Prop83.cmat]
    rw [charpoly_fin_two, htrC, hdetC, htr, hdt]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    push_cast
    ring
  have hfr := finrank_orbitBdd_lt hroot (by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [one_lt_lam3r h])]
    exact one_lt_lam3r h)
  rw [Fintype.card_fin] at hfr
  have heq := orbitBdd_eq_of_homEquiv hE hEs
  have hfr' : Module.finrank ℂ (orbitBdd (cmat H.Λ)) ≤ 1 := by
    rw [heq]
    change Module.finrank ℂ (orbitBdd (cmat Λs)) ≤ 1
    omega
  have hlow := card_le_zerosInside_add_finrank hE hβ hreg hcirc
  obtain ⟨n1, -, -⟩ := in_root_norms c γ h
  have hl1 : muj c (lam1 c.β γ c.κ c.σ) ∈ (inProblem c γ hc hγ0.le).sys.pencilPoly.roots := by
    change muj c (lam1 c.β γ c.κ c.σ) ∈ (inSys c γ hσ hd).pencilPoly.roots
    rw [in_roots c γ h]
    simp
  have hl0 : muj c (lam1 c.β γ c.κ c.σ) ≠ 0 :=
    muj_ne_zero c γ h (by exact_mod_cast (lam1_spec h).1.ne' : (lam1 c.β γ c.κ c.σ : ℂ) ≠ 0)
  have hup := zerosInside_add_one_le_of_root hE hβ hreg hl1 hl0 n1.le
  rw [Fintype.card_fin] at hlow hup
  exact ⟨by omega, Prop83.zerosOnCircle_eq_zero hE hβ hreg hcirc⟩

/-- **Woodford (2003), Proposition 8.3, pp. 556–557, for the inflation-inertia model at every
admissible calibration** (`0 < γ ≤ 1`, real or complex roots, with or without the double root
`S² = 4P₂₃`), for every representation of the corrected Proposition 8.1: `α(L) = det(I − ΛL)`
has exactly one zero inside the unit circle and none on it. -/
theorem in_prop83_all [Nonempty Ω] (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (H : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) :
    zerosInside (alpha H.Λ) = 1 ∧ zerosOnCircle (alpha H.Λ) = 0 := by
  rcases le_or_gt 0 (discQ c.β γ c.κ c.σ) with hD | hD
  · exact in_prop83_real c γ hc hγ0 hγ1 hD 𝔼 t0 H
  · exact in_prop83 c γ hc hγ0 hγ1 hD.ne 𝔼 t0 H

/-- **Woodford (2003), Propositions 8.1 and 8.3 for the inflation-inertia model at every
admissible calibration** (`0 < γ ≤ 1`; real roots, the double root `S² = 4P₂₃`, or a complex
pair; any expectation system, nonempty sample space): the corrected Proposition 8.1 holds
(`InertiaProp8182.in_prop81_all`, through case (ii) of Assumption 8.2 when the roots are
complex), and every representation has `α(L)` with exactly one zero inside the unit circle and
none on it (`in_prop83_all`). -/
theorem in_props_81_83_all [Nonempty Ω] (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) ∧
      ∀ H : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0,
        zerosInside (alpha H.Λ) = 1 ∧ zerosOnCircle (alpha H.Λ) = 0 :=
  ⟨InertiaProp8182.in_prop81_all c γ hc hγ0 hγ1 𝔼 t0, fun H => in_prop83_all c γ hc hγ0 hγ1 𝔼 t0 H⟩

/-- **Woodford (2003), Propositions 8.1 and 8.3 at the double root `S² = 4P₂₃` of the
inflation-inertia model** (pp. 553–557, 594–596): Assumption 8.3 fails there, yet the corrected
Proposition 8.1 holds (any expectation system) and every representation it delivers has
`α(L)` with exactly one zero inside the unit circle and none on it. -/
theorem in_double_props_81_83 [Nonempty Ω] (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD0 : discQ c.β γ c.κ c.σ = 0) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ¬ PencilEigen.Assumption83 (inProblem c γ hc hγ0.le).sys ∧
      Nonempty (Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) ∧
      ∀ H : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0,
        zerosInside (alpha H.Λ) = 1 ∧ zerosOnCircle (alpha H.Λ) = 0 :=
  ⟨in_double_not_assumption83 c γ (standing_of c γ hc hγ0 hγ1) hc.2.2.1.ne'
      (in_det_ne c γ hc hγ0.le) hD0,
    InertiaProp8182.in_prop81_real c γ hc hγ0 hγ1 hD0.ge 𝔼 t0,
    fun H => in_prop83_real c γ hc hγ0 hγ1 hD0.ge 𝔼 t0 H⟩

end Inertia

/-! ### The basic model: a fully worked instance of the general theory -/

namespace NK

open GeneralLinks
open IRuleBasic (Calib)

variable (c : Calib)

/-- Woodford (2003), (1.15), p. 546, for the basic model:
`det(A − μÎ) = βμ² − (1 + β + κσ)μ + 1`. -/
theorem nk_pencil_eval (hσ : c.σ ≠ 0) (z : ℂ) :
    (nkSys c hσ).pencilPoly.eval z = c.β * z ^ 2 - (1 + c.β + c.κ * c.σ) * z + 1 := by
  rw [PencilSplit.pencilPoly_eval, Prop83.det_empty_sum, det_fin_two]
  simp [toBlocks₂₂, LinearRESystem.Ahat, LinearRESystem.Ihat, nkSys]
  ring

/-- Woodford (2003), (1.15) at `μ = 0`: `A` is invertible for the basic model
(`det A = det A₂₂ = 1`), so `rank A = 2`. -/
theorem nk_rank_Ahat (hσ : c.σ ≠ 0) : (nkSys c hσ).Ahat.rank = 2 := by
  rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
  · simp
  · rw [Prop83.det_empty_sum]
    exact (nkSys c hσ).A22_isUnit

/-- **Woodford (2003), Assumption 8.2, p. 552, for the basic model**: `n_Z = 0`, the zero root
does not occur (`rank A = n`), and the empty selection is admissible (case (i)). -/
noncomputable def nk_assumption82 (hσ : c.σ ≠ 0) : PencilEigen.Assumption82 (nkSys c hσ) c.β where
  count := by
    unfold LinearRESystem.Assumption82Count
    simp
  sel := 0
  sel_le := Multiset.zero_le _
  sel_card := by
    rw [nk_rank_Ahat c hσ]
    simp
  cases := Or.inl (by simp [GeneralFOC.Selection.ConjClosed])

/-- Woodford (2003), App. G.1, (G.6), p. 718, for the basic model: with `Γ = (0; I)`,
`W = Ẽ A₂₂⁻¹ = [β βκ; σ σκ + 1]` gives `W Γ'A = Γ'Î`. -/
theorem nk_G6 (hσ : c.σ ≠ 0) :
    !![c.β, c.β * c.κ; c.σ, c.σ * c.κ + 1] * (Matrix.fromRows 0 1 :
      Matrix (Empty ⊕ Fin 2) (Fin 2) ℝ)ᵀ * (nkSys c hσ).Ahat =
      (Matrix.fromRows 0 1 : Matrix (Empty ⊕ Fin 2) (Fin 2) ℝ)ᵀ * (nkSys c hσ).Ihat := by
  ext i j
  rcases j with e | j
  · exact e.elim
  · fin_cases i <;> fin_cases j <;>
      simp [nkSys, LinearRESystem.Ahat, LinearRESystem.Ihat, Matrix.mul_apply,
        Fin.sum_univ_two, Fintype.sum_sum_type, Matrix.one_apply, vecMul, dotProduct]

/-- **Woodford (2003), Assumption 8.4, App. G.1, p. 718, for the basic model** (with the empty
selection): `Γ = (0; I)`, `W = Ẽ A₂₂⁻¹`, whose eigenvalues are the reciprocals `λ₁⁻¹, λ₂⁻¹` of
the (unselected) roots of (1.15); `A'Γ` has rank 2 and `Γ₂ = I`. -/
noncomputable def nk_assumption84 (hσ : c.σ ≠ 0) :
    PencilAssumptions.Assumption84 (nkSys c hσ) 0 where
  Γ := Matrix.fromRows 0 1
  W := !![c.β, c.β * c.κ; c.σ, c.σ * c.κ + 1]
  G6 := nk_G6 c hσ
  W_eig := by
    intro θ hθ
    have hdet : θ ^ 2 - (1 + c.β + c.κ * c.σ) * θ + c.β = 0 := by
      rw [det_fin_two] at hθ
      simp [Matrix.scalar_apply] at hθ
      linear_combination hθ
    by_cases h0 : θ = 0
    · exact Or.inl h0
    · refine Or.inr ⟨θ⁻¹, ?_, inv_ne_zero h0, by simp, (inv_inv θ).symm⟩
      rw [nk_pencil_eval c hσ]
      field_simp
      linear_combination hdet
  full_rank := by
    refine le_antisymm (rank_le_card_width _) ?_
    have hsub : ((nkSys c hσ).Ahatᵀ * (Matrix.fromRows 0 1 :
        Matrix (Empty ⊕ Fin 2) (Fin 2) ℝ)).submatrix Sum.inr id = (nkSys c hσ).A22ᵀ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [LinearRESystem.Ahat, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    have hr : (nkSys c hσ).A22ᵀ.rank = 2 := by
      rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
      · simp
      · rw [det_transpose]
        exact (nkSys c hσ).A22_isUnit
    have := rank_submatrix_le ((nkSys c hσ).Ahatᵀ * (Matrix.fromRows 0 1 :
        Matrix (Empty ⊕ Fin 2) (Fin 2) ℝ)) Sum.inr id
    rw [hsub, hr] at this
    simpa using this
  det_Γ2 := by
    have e : (Matrix.fromRows 0 1 : Matrix (Empty ⊕ Fin 2) (Fin 2) ℝ).submatrix Sum.inr id =
        1 := by
      ext i j
      simp
    rw [e, det_one]
    exact one_ne_zero

/-- Woodford (2003), (1.20), p. 553, for the basic model: the general `Λ = β⁻¹K⁻¹Ẽ'` of
Proposition 8.1 (`PencilSplit.Λmat`, any `J`: with `n_Z = 0`, `K = A₂₂'`) is the hand-computed
`GeneralLinks.nkΛ = [1 σ/β; κ (1 + κσ)/β]`. -/
theorem nk_Λmat (hσ : c.σ ≠ 0) (hβ : c.β ≠ 0) (J : Matrix (Empty ⊕ Fin 2) Empty ℝ) :
    PencilSplit.Λmat (nkSys c hσ) c.β J = nkΛ c := by
  have hK : PencilSplit.Kmat (nkSys c hσ) J = !![1, 0; -c.κ, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PencilSplit.Kmat, nkSys]
  have hKi : (PencilSplit.Kmat (nkSys c hσ) J)⁻¹ = !![1, 0; c.κ, 1] := by
    rw [hK]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [PencilSplit.Λmat, hKi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nkΛ, nkSys, Fin.sum_univ_two, vecMul, dotProduct]
  all_goals field_simp
  all_goals ring

/-- Woodford (2003), (1.20), p. 553: `det Λ = β⁻¹` for the basic model. -/
theorem nk_det_Λ (hβ : c.β ≠ 0) : (nkΛ c).det = c.β⁻¹ := by
  rw [det_fin_two]
  simp [nkΛ]
  field_simp
  ring

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, for the basic model**: with `B₂ = (0, σ)`
and `k = rank Λ = 2`, `B₂', B₂'Λ` are linearly independent, and so are `B₂'Λ, B₂'Λ²`
(`InertiaProp8182.assumption85_two`: `det Λ = β⁻¹ ≠ 0`, `Λ₁₀ = κ ≠ 0`). -/
theorem nk_assumption85 (hc : c.Adm) :
    PencilAssumptions.Assumption85 (nkΛ c) (nkSys c hc.2.2.1.ne').B2 :=
  InertiaProp8182.assumption85_two hc.2.2.1.ne' (by simpa [nkΛ] using hc.2.2.2.1.ne')
    (by rw [nk_det_Λ c hc.1.ne']; exact inv_ne_zero hc.1.ne')

/-- **Woodford (2003), Propositions 8.1 and 8.3 for the basic model, from the general
theorems** (pp. 553–557, 582–586; any expectation system, nonempty sample space). Assumptions
8.2 (case (i), empty selection), 8.3 and 8.4 hold (`nk_assumption82`,
`GeneralLinks.nk_assumption83`, `nk_assumption84`), so `PencilAssumptions.prop81_of_assumptions`
gives the corrected Proposition 8.1, whose `Λ` is `GeneralLinks.nkΛ`; and for **every**
representation `α(L) = det(I − ΛL)` has exactly one zero inside the unit circle and none on it
(`Prop83Links.prop83M_const`, `m = 1`, no root on `|μ| = β⁻¹`): Proposition 8.5's
superinertia. Assumption 8.1 is not needed. -/
theorem nk_prop81_prop83 [Nonempty Ω] (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    (∃ H : Prop81ConclusionM (nkProblem c hc) 𝔼 t0, H.Λ = nkΛ c) ∧
      ∀ H : Prop81ConclusionM (nkProblem c hc) 𝔼 t0,
        zerosInside (alpha H.Λ) = 1 ∧ zerosOnCircle (alpha H.Λ) = 0 := by
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hi : GeneralFOC.Selection.ConjClosed (nk_assumption82 c hσ).sel := by
    simp [GeneralFOC.Selection.ConjClosed, nk_assumption82]
  refine ⟨⟨Prop81General.prop81 _ (PencilAssumptions.splitOf (nkProblem c hc)
    (nk_assumption82 c hσ) hi (nk_assumption83 c hc) (nk_assumption84 c hσ)) 𝔼 t0,
    nk_Λmat c hσ hc.1.ne' _⟩, fun H => ?_⟩
  have hv0 : (nkProblem c hc).Ttilᵀ *ᵥ ((nkProblem c hc).W *ᵥ ((nkProblem c hc).T *ᵥ
      Sum.elim (Sum.elim (fun e => e.elim) ![0, c.xstar]) (fun _ => 0) -
        (nkProblem c hc).τstar)) = 0 := by
    rw [nk_xvec]
    funext r
    rcases r with e | j
    · exact e.elim
    · fin_cases j <;> simp
  exact Prop83Links.prop83M_const H _ hv0 (nk_assumption83 c hc) (nk_stableCount c hc)
    (nk_no_circle c hc)

/-- **Woodford (2003), Proposition 8.2 for the basic model, from the general theorem**
(p. 555), for every expectation system with pull-out: Assumptions 8.1 (corrected,
`NKAssumption81.NK.nk_assumption81M`), 8.2–8.5 (`nk_assumption82`,
`GeneralLinks.nk_assumption83`, `nk_assumption84`, `nk_assumption85`) hold, so
`PencilAssumptions.prop82_of_assumptions` applies: commitment to the target criterion (1.23)
built from the representation with `Λ = nkΛ` is robustly optimal (a window of `D ≥ 2` lags,
any consistent bounded history). -/
theorem nk_prop82 {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hc : c.Adm) (hpull : 𝔼.PullOut)
    {D : ℕ} (hD : D + 1 ≤ t0) (hD2 : 2 ≤ D)
    {Mh qh : ℕ → Ω → Fin 2 → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (nkΛ c) (nkSys c hc.2.2.1.ne').B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    ∃ H : Prop81ConclusionM (nkProblem c hc) 𝔼 t0, H.Λ = nkΛ c ∧
      RobustlyOptimal (κ := Fin 2) (nkProblem c hc) 𝔼 t0
        (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
        (fun _ y t ω => zpart (y t ω)) := by
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hi : GeneralFOC.Selection.ConjClosed (nk_assumption82 c hσ).sel := by
    simp [GeneralFOC.Selection.ConjClosed, nk_assumption82]
  have hΛ := nk_Λmat c hσ hc.1.ne' (PencilAssumptions.splitOf (nkProblem c hc)
    (nk_assumption82 c hσ) hi (nk_assumption83 c hc) (nk_assumption84 c hσ)).J
  have hE : (nkSys c hσ).Et.rank = 2 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)]
    · simp
    · simp [nkSys, det_fin_two, hc.1.ne']
  refine ⟨_, hΛ, PencilAssumptions.prop82_of_assumptions hpull
    (NKAssumption81.NK.nk_assumption81M c hc 𝔼 t0) (nk_assumption82 c hσ) hi
    (nk_assumption83 c hc) (nk_assumption84 c hσ) ?_ hD ?_ ?_ hMhb hMhk hqhb hvhb⟩
  · convert nk_assumption85 c hc using 2
    · exact hΛ
    · rfl
  · change (nkSys c hσ).Et.rank ≤ D
    rw [hE]
    exact hD2
  · convert hhist using 2
    · exact hΛ
    · rfl

end NK

/-! ### The old conditional results of `TargetCriterion` -/

namespace Old

variable {ιτ : Type*} [Fintype ιτ] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}

/-- Woodford (2003), Proposition 8.1, p. 553: the original hypothesis structure
`TargetCriterion.Prop81.Prop81Conclusion` (the equivalence for all bounded multipliers) yields
the corrected `Prop81General.Prop81ConclusionM` (the equivalence restricted to adapted plans and
multipliers known at `t`), whenever its `R(L⁻¹)` is adapted. -/
def conclusionM_of_conclusion (H : Prop81Conclusion P 𝔼 t0)
    (hR : ∀ x, BoundedV x → AdaptedV 𝔼 (H.Rop x)) : Prop81ConclusionM P 𝔼 t0 where
  Λ := H.Λ
  Υ := H.Υ
  Qop := H.Qop
  Rop := H.Rop
  equiv := fun y φ hy _ hφ _ => H.equiv y φ hy hφ
  Qbounded := H.Qbounded
  Rbounded := H.Rbounded
  Qadapted := H.Qadapted
  Radapted := hR

/-- Woodford (2003), Proposition 8.1, p. 553, under perfect foresight: every inhabitant of the
original structure is one of the corrected structure (everything is adapted). -/
def conclusionM_perfectForesight (H : Prop81Conclusion P perfectForesight t0) :
    Prop81ConclusionM P perfectForesight t0 :=
  conclusionM_of_conclusion H fun _ _ _ _ => rfl

/-- Woodford (2003), eq. (1.23), p. 554: the target criterion of the old conditional
Proposition 8.2 (`TargetCriterion.Prop82.Criterion`) is that of the unconditional one
(`Prop82General.Prop82M.CriterionM`) for the converted representation. -/
theorem criterion_iff (H : Prop81Conclusion P 𝔼 t0)
    (hR : ∀ x, BoundedV x → AdaptedV 𝔼 (H.Rop x)) (D : ℕ) (qh : ℕ → Ω → ιz → ℝ)
    (vh : ℕ → Ω → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    TargetCriterion.Prop82.Criterion H D qh vh y ↔
      Prop82General.Prop82M.CriterionM (conclusionM_of_conclusion H hR) D qh vh y :=
  Iff.rfl

/-- **Woodford (2003), Proposition 8.2 (second part), p. 555: `TargetCriterion.prop82_optimal`
without its hypothesis `MultStable`.** For the old representation (with `R(L⁻¹)` adapted, e.g.
under perfect foresight), Assumption 8.5 and a bounded history replace `MultStable` (which fails
in the book's applications, `PencilAssumptions.not_multStable_of_unselected`); the conclusion is
the same. -/
theorem prop82_optimal_of_assumption85 (hpull : 𝔼.PullOut) (H : Prop81Conclusion P 𝔼 t0)
    (hR : ∀ x, BoundedV x → AdaptedV 𝔼 (H.Rop x))
    (h85 : TargetCriterion.Krylov.Assumption85b H.Λ P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D) (hα : (alpha H.Λ).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.Feasible 𝔼 c t0 Z0 y)
    (hcrit : TargetCriterion.Prop82.Criterion H D qh vh y) :
    P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y :=
  Prop82General.Prop82M.prop82M_optimal hpull (conclusionM_of_conclusion H hR) h85 hD hB hα
    hhist hMhb hMhk hqhb hvhb hy hcrit

/-- **Woodford (2003), Proposition 8.2 (uniqueness), p. 555: `TargetCriterion.prop82_unique`
without its hypothesis `MultStable`**, under Assumption 8.5 and a bounded history instead (and
the corrected Assumption 8.1, `Prop82General.Assumption81M`, implied by the original). -/
theorem prop82_unique_of_assumption85 (hA : Prop82General.Assumption81M P 𝔼 t0)
    (H : Prop81Conclusion P 𝔼 t0)
    (hR : ∀ x, BoundedV x → AdaptedV 𝔼 (H.Rop x))
    (h85 : TargetCriterion.Krylov.Assumption85b H.Λ P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D) (hα : (alpha H.Λ).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.Feasible 𝔼 c t0 Z0 y)
    (hy' : P.Feasible 𝔼 c t0 Z0 y') (hcrit : TargetCriterion.Prop82.Criterion H D qh vh y)
    (hcrit' : TargetCriterion.Prop82.Criterion H D qh vh y') : ∀ t, t0 ≤ t → y t = y' t :=
  Prop82General.Prop82M.prop82M_unique hA (conclusionM_of_conclusion H hR) h85 hD hB hα hhist
    hMhb hMhk hqhb hvhb hy hy' hcrit hcrit'

/-- **Woodford (2003), Proposition 8.4, p. 558: the hypotheses of
`TargetCriterion.prop84_conditional` are discharged** for every representation of the corrected
Proposition 8.1, under Assumptions 8.1, 8.3, 8.7 and no root of (1.15) on `|λ| = β⁻¹`
(`Prop83Links.prop84M`): `α = α₁α₂` with `deg α₁ = m`, `α₁ ≠ 0`, every root of `α̃₁` outside the
unit circle, and for every bounded adapted `w` a bounded adapted `g` with `E_t α̃₁(L⁻¹) g_t = w_t`;
so the conditional equivalence (1.28) ⟺ (1.32) at all dates holds outright. -/
theorem prop84_conditional_discharged [Nonempty Ω] (H : Prop81ConclusionM P 𝔼 t0)
    (hA : Assumption81 P 𝔼 t0) (h83 : PencilEigen.Assumption83 P.sys) {m : ℕ}
    (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    ∃ α1 α2 : ℝ[X], alpha H.Λ = α1 * α2 ∧ α1.natDegree = m ∧ α1 ≠ 0 ∧
      (∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖) ∧
      ∀ (lam istar : ℝ) (i w : ℕ → Ω → ℝ), BoundedProc i → 𝔼.Adapted i → BoundedProc w →
        𝔼.Adapted w → ∃ g, BoundedProc g ∧ 𝔼.Adapted g ∧
          (aeval (TargetCriterion.fwdOp 𝔼) α1.reverse) g = w ∧
          (lam • (aeval (TargetCriterion.lagOp (Ω := Ω)) (alpha H.Λ))
              (fun t ω => i t ω - istar) + w = 0 ↔
            g + lam • ((TargetCriterion.lagOp (Ω := Ω)) ^ m)
              ((aeval (TargetCriterion.lagOp (Ω := Ω)) α2) (fun t ω => i t ω - istar)) = 0) := by
  obtain ⟨α1, α2, hfac, hdeg, hin, -, hrest⟩ := Prop83Links.prop84M H hA h83 h87 hcirc
  have hα1 : α1 ≠ 0 := fun h0 => alpha_ne_zero H.Λ (by rw [hfac, h0, zero_mul])
  have hrev : ∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖ := by
    rw [TargetCriterion.map_reverse_ofReal]
    exact TargetCriterion.roots_reverse_outside hin
  refine ⟨α1, α2, hfac, hdeg, hα1, hrev, fun lam istar i w hib hia hwb hwa => ?_⟩
  obtain ⟨g, ⟨hgb, hga, hg⟩, -⟩ := (hrest lam istar i w hib hia hwb hwa).1
  refine ⟨g, hgb, hga, hg, ?_⟩
  rw [hfac]
  exact TargetCriterion.prop84_conditional hdeg hα1 hrev hib hia hgb hg

/-- **Woodford (2003), Proposition 8.3, pp. 556–557: the statement `TargetCriterion.Prop83Claim`
is non-vacuous and true** under perfect foresight, Assumptions 8.1, 8.2 (case (i)), 8.3, 8.4 and
no root of (1.15) on `|λ| = β⁻¹`: the original hypothesis structure is inhabited
(`PencilAssumptions.prop81_of_assumptions_perfectForesight`) and every inhabitant satisfies the
claim (`Prop83.prop83Claim_holds`). -/
theorem prop83Claim_perfectForesight (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (hA : Assumption81 P perfectForesight t0) (h82 : PencilEigen.Assumption82 P.sys P.β)
    (hi : GeneralFOC.Selection.ConjClosed h82.sel) (h83 : PencilEigen.Assumption83 P.sys)
    (h84 : PencilAssumptions.Assumption84 P.sys h82.sel)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    Nonempty (Prop81Conclusion P perfectForesight t0) ∧
      ∀ H : Prop81Conclusion P perfectForesight t0,
        TargetCriterion.Prop83Claim P perfectForesight t0 H :=
  ⟨PencilAssumptions.prop81_of_assumptions_perfectForesight P h82 hi h83 h84 t0,
    fun H => Prop83.prop83Claim_holds H hA h83 hcirc⟩

end Old

/-! ### The scalar circle system -/

/-- Woodford (2003), (1.1) (the scalar systems of the counterexamples): `Circle81.circSys` at
`β = 1/2`, `E_t z_{t+1} = 2z_t + i_t + c_t`, is the system `Prop81General.coinSys` of the
counterexamples to the uncorrected Proposition 8.1 and to the remark on p. 553. -/
theorem circSys_half :
    Circle81.circSys (1 / 2) (by norm_num) = Prop81General.coinSys := by
  unfold Circle81.circSys Prop81General.coinSys
  congr 1
  ext i j
  norm_num

end Woodford.OptimalPolicyRules.GeneralTheoryLinks
